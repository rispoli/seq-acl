#include <argtable2.h>
#include <errno.h>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include "message.h"
#include <sstream>
#include <stdlib.h>
#include <string>
#include <string.h>
#include <sys/types.h>
#include <utility>
#include <vector>
using namespace std;

#if defined (WIN32) && !defined (__CYGWIN32__) // It's not Unix, really. See? Capital letters.

#define __WINDOWS

#define _WIN32_WINNT 0x501 // To get getaddrinfo && freeaddrinfo working with MinGW.
#include <windows.h>
#include <winsock2.h>
#include <ws2tcpip.h>

#define close(fd) closesocket(fd)
#define SCAST const char
#define RCAST char

#else

#include <arpa/inet.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/socket.h>

#define SCAST void
#define RCAST void

#endif

void close_and_cleanup(int sock_fd) {
	close(sock_fd);
#ifdef __WINDOWS
	WSACleanup();
#endif
}

vector<string> * split(string s) {
	vector<string> *v = new vector<string>;
	size_t p = 0;
	for(size_t i = 0; i < s.size(); i++)
		if(s[i] == ',') { v->push_back(s.substr(p, i - p)); p = i + (i + 1 < s.size() && s[i + 1] == ' ' ? 2 : 1); }
	v->push_back(s.substr(p, s.size() - p));
	return v;
}

vector< vector<string > * > split_multiple(string s) {
	vector< vector<string> * > outer;
	size_t p = 0;
	for(size_t i = 0; i < s.size(); i++) {
		if(s[i] == '[') p = i + 1;
		else if(s[i] == ']') { outer.push_back(split(s.substr(p, i - p))); p = i + 1; }
	}
	return outer;
}

string join(vector<string> v) {
	stringstream ss;
	for(size_t i = 0; i < v.size(); i++)
		ss << v[i] << ", ";
	return ss.str().substr(0, ss.str().size() - 2);
}

bool already_granted(vector<string> v, size_t b, map<pair<string, size_t>, bool> h) {
	for(size_t i = 0; i < v.size(); i++)
		for(size_t j = 0; j < b; j++) {
			map<pair<string, size_t>, bool>::iterator it = h.find(make_pair(v[i], j));
			if(it != h.end() && it->second)
				return true;
		}
	return false;
}

int process_query(string whoami, string iporhostname, string credentials, string query, map<string, string> addresses, bool interactive, map<pair<string, size_t>, bool> history) {
	int sock_fd = -1;
	size_t rv;
	string port("3333");

	if((rv = iporhostname.find(":")) != string::npos) {
		port = iporhostname.substr(rv + 1, iporhostname.length() - rv);
		iporhostname = iporhostname.substr(0, rv);
	}

#ifdef __WINDOWS
	WSADATA wsaData;

	if(WSAStartup(MAKEWORD(2, 2), &wsaData) != 0) {
		cerr << "Could not find Winsock dll" << endl;
		return FAILURE;
	}

	if(LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2) {
		cerr << "Wrong Winsock version" << endl;
		WSACleanup();
		return FAILURE;
	}
#endif

	struct addrinfo hints, *serv_info, *p;
	memset(&hints, 0, sizeof(hints));
	hints.ai_family = AF_UNSPEC;
	hints.ai_socktype = SOCK_STREAM;

	if(getaddrinfo(iporhostname.c_str(), port.c_str(), &hints, &serv_info) != 0) {
		cerr << "Could not resolve host (" << errno << ")" << endl;
#ifdef __WINDOWS
		WSACleanup();
#endif
		return FAILURE;
	}

	for(p = serv_info; p != NULL; p = p->ai_next) {
		if((sock_fd = socket(p->ai_family, p->ai_socktype, p->ai_protocol)) == -1) {
			cerr << "Could not open socket (" << errno << ")" << endl;
#ifdef __WINDOWS
			WSACleanup();
#endif
			continue;
		}

		if(connect(sock_fd, p->ai_addr, p->ai_addrlen) == -1) {
			cerr << "Could not connect (" << errno << ")" << endl;
			close_and_cleanup(sock_fd);
			continue;
		}

		break;
	}

	if(p == NULL) {
		cerr << "Failed to connect" << endl;
		close_and_cleanup(sock_fd);
		freeaddrinfo(serv_info);
		return FAILURE;
	}

	freeaddrinfo(serv_info);

	c2s_t query_metadata;
	query_metadata.principal_size = whoami.size();
	query_metadata.credentials_size = credentials.size();
	query_metadata.request_size = query.size();

	if(send(sock_fd, (SCAST *)&query_metadata, sizeof(query_metadata), 0) == -1) {
		cerr << "Could not send query (" << errno << ")" << endl;
		close_and_cleanup(sock_fd);
		return FAILURE;
	}

	if(send(sock_fd, (SCAST *)whoami.c_str(), whoami.size(), 0) == -1) {
		cerr << "Could not send principal (" << errno << ")" << endl;
		close_and_cleanup(sock_fd);
		return FAILURE;
	}
	if(credentials != "")
		if(send(sock_fd, (SCAST *)credentials.c_str(), credentials.size(), 0) == -1) {
			cerr << "Could not send credentials (" << errno << ")" << endl;
			close_and_cleanup(sock_fd);
			return FAILURE;
		}
	if(send(sock_fd, (SCAST *)query.c_str(), query.size(), 0) == -1) {
		cerr << "Could not send query (" << errno << ")" << endl;
		close_and_cleanup(sock_fd);
		return FAILURE;
	}

	answer_t answer_metadata;
	if(recv(sock_fd, (RCAST *)&answer_metadata, sizeof(answer_metadata), 0) == -1) {
		cerr << "Could not receive result (" << errno << ")" << endl;
		close_and_cleanup(sock_fd);
		return FAILURE;
	}

	char *answer = NULL;
	if(answer_metadata.status != SUCCESS) {
		answer = (char *)malloc(answer_metadata.size + 1);
		memset(answer, 0, answer_metadata.size + 1);
		if(recv(sock_fd, (RCAST *)answer, answer_metadata.size, 0) == -1) {
			cerr << "Could not receive data (" << errno << ")" << endl;
			close_and_cleanup(sock_fd);
			if(answer != NULL) free(answer);
			return FAILURE;
		}
	}

	close_and_cleanup(sock_fd);

	if(answer_metadata.status == FAILURE) {
		cerr << iporhostname << ":" << port << " says: " << string(answer) << endl;
		free(answer);
		return FAILURE;
	} else if(answer_metadata.status == SUCCESS)
		// Move this output to main so intermediate results do not get shown?
		cout << iporhostname << ":" << port << " says: '" << query << "' granted." << endl;
	else if(answer_metadata.status == COUNTERMODELS) {
		if(!strncmp(answer, "[]", sizeof(answer_metadata.size + 1))) {
			cerr << iporhostname << ":" << port << " says: '" << query << "' not satisfiable." << endl;
			free(answer);
			return FAILURE;
		}

		vector< vector<string> * > vm = split_multiple(answer);
		stringstream new_credentials; new_credentials << "(" << credentials << ")";
		size_t i = 0, successes = 0;
		while(i < vm.size() && i == successes) {
			vector<string> *v = vm[i];
			if(!already_granted(*v, i, history)) {
				int return_value = FAILURE;
				if(interactive) {
					unsigned int choices = 0;
					do {
						stringstream choice_banner;
						choice_banner << iporhostname << ":" << port << " says: choose one among these additional credentials:" << endl;
						choices = 0;
						for(size_t j = 0; j < v->size(); j++)
							if(history.find(make_pair((*v)[j], i)) == history.end() && (*v)[j] != "") {
								choice_banner << j << ". " << (*v)[j] << endl;
								choices++;
							}
						if(choices) {
							cout << choice_banner.str();
							int c = -1;
							do {
								cout << "> ";
								while(!(cin >> c)) {
									cin.clear();
									cin.ignore(numeric_limits<streamsize>::max(), '\n');
									cout << "> ";
								}
							} while(c < 0 || c >= (int)v->size() || history.find(make_pair((*v)[c], i)) != history.end());
							size_t p = (*v)[c].find("says");
							if(p != string::npos) {
								if(addresses.find((*v)[c].substr(0, p - 1)) == addresses.end())
									cerr << "Address for '" << (*v)[c].substr(0, p - 1) << "' not found." << endl;
								else {
									history[make_pair((*v)[c], i)] = false;
									return_value = process_query(whoami, addresses[(*v)[c].substr(0, p - 1)], whoami + " says " + (*v)[c], (*v)[c], addresses, interactive, history);
									history[make_pair((*v)[c], i)] = return_value == SUCCESS;
								}
							}
							if(return_value == SUCCESS) {
								new_credentials << " and (" << (*v)[c] << ")";
								successes++;
							}
						}
					} while(return_value != SUCCESS && choices);
				} else {
					size_t j = 0;
					if((*v)[0] != "") {
						cout << iporhostname << ":" << port << " says: additional credentials '" << join(*v) << "'." << endl;
						while(j < v->size() && return_value != SUCCESS) {
							if(history.find(make_pair((*v)[j], i)) == history.end()) {
								size_t p = (*v)[j].find("says");
								if(p != string::npos) {
									if(addresses.find((*v)[j].substr(0, p - 1)) == addresses.end())
										cerr << "Address for '" << (*v)[j].substr(0, p - 1) << "' not found." << endl;
									else {
										history[make_pair((*v)[j], i)] = false;
										return_value = process_query(whoami, addresses[(*v)[j].substr(0, p - 1)], whoami + " says " + (*v)[j], (*v)[j], addresses, interactive, history);
										history[make_pair((*v)[j], i)] = return_value == SUCCESS;
									}
								}
							}
							j++;
						}
					}
					if(return_value == SUCCESS) {
						new_credentials << " and (" << (*v)[j - 1] << ")";
						successes++;
					}
				}
			} else successes++;
			i++;
		}
		if(vm.size() == successes)
			answer_metadata.status = process_query(whoami, iporhostname + ":" + port, new_credentials.str(), query, addresses, interactive, history);
		else
			cout << iporhostname << ":" << port << " says: '" << query << "' cannot be granted." << endl;

		free(answer);
		for(size_t i = 0; i < vm.size(); i++) delete vm[i];
	}

	return answer_metadata.status;
}

map<string, string> process_addresses(const char *fn) {
	ifstream f(fn);
	if(!f.is_open()) {
		cerr << "Could not open addresses file" << endl;
		exit(EXIT_FAILURE);
	}
	string line;
	size_t p;
	map<string, string> a;
	while(f.good()) {
		getline(f, line);
		if((p = line.find(",")) != string::npos) {
			a[line.substr(0, p)] = line.substr(p + 1, line.size() - p);
		} else if(line != "") {
			cerr << "Malformed addresses file" << endl;
			exit(EXIT_FAILURE);
		}
	}
	f.close();
	return a;
}

string process_credentials(const char *fn) {
	ifstream f(fn);
	if(!f.is_open()) {
		cerr << "Could not open credentials file" << endl;
		exit(EXIT_FAILURE);
	}
	string line, credentials = "";
	while(f.good()) {
		getline(f, line);
		if(line != "")
			credentials += line + " and ";
		else
			credentials.erase(credentials.size() - 5, 5);
	}
	f.close();
	return credentials;
}

void process_requests(string whoami, const char *fn, string credentials, map<string, string> addresses, bool interactive, map<pair<string, size_t>, bool> history) {
	ifstream f(fn);
	if(!f.is_open()) {
		cerr << "Could not open request file" << endl;
		exit(EXIT_FAILURE);
	}
	string line;
	size_t p;
	while(f.good()) {
		getline(f, line);
		if((p = line.find("@")) != string::npos) {
			process_query(whoami, line.substr(line.find_first_not_of(" \t", p + 1), line.find_last_not_of(" \t") - line.find_first_not_of(" \t", p + 1) + 1), credentials, line.substr(0, p), addresses, interactive, history);
		} else if(line != "") {
			cerr << "Malformed request file" << endl;
			exit(EXIT_FAILURE);
		}
	}
	f.close();
}

int main(int argc, char *argv[]) {
	struct arg_lit *help = arg_lit0("h", "help", "print this help and exit");
	struct arg_str *whoami = arg_str1("w", "whoami", NULL, "name of the principal issuing the requests");
	struct arg_file *credentials = arg_file0("c", "credentials", NULL, "credentials path (default: credentials)");
	struct arg_file *request = arg_file0("r", "request", NULL, "request path (default: request)");
	struct arg_file *addresses = arg_file0("a", "addresses", NULL, "addresses path (default: addresses)");
	struct arg_lit *interactive = arg_lit0("i", "interactive", "interactively choose which additional credential to request");
	struct arg_end *end = arg_end(23);
	void *argtable[] = {help, whoami, credentials, request, addresses, interactive, end};

	if(arg_nullcheck(argtable) != 0) {
		cerr << "Could not allocate enough memory for command line arguments" << endl;
		arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));
		return 1;
	}

	credentials->filename[0] = "credentials";
	request->filename[0] = "request";
	addresses->filename[0] =  "addresses";

	int nerrors = arg_parse(argc, argv, argtable);

	if(help->count > 0) {
		cout << "Usage: " << argv[0];
		arg_print_syntaxv(stdout, argtable, "\n");
		arg_print_glossary(stdout, argtable, "  %-30s %s\n");
		arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));
		return 0;
	}

	if(nerrors > 0) {
		arg_print_errors(stdout, end, argv[0]);
		arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));
		return 1;
	}

	map<pair<string, size_t>, bool> history;
	if(credentials->count > 0)
		process_requests(whoami->sval[0], request->filename[0], process_credentials(credentials->filename[0]), process_addresses(addresses->filename[0]), interactive->count > 0, history);
	else
		process_requests(whoami->sval[0], request->filename[0], "", process_addresses(addresses->filename[0]), interactive->count > 0, history);

	arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));

	return 0;
}
