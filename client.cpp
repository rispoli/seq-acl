#include <argtable2.h>
#include <errno.h>
#include <fstream>
#include <iostream>
#include <map>
#include "message.h"
#include <sstream>
#include <stdlib.h>
#include <string>
#include <string.h>
#include <sys/types.h>
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

vector< vector<string> * > split(string s) {
	vector< vector<string> * > outer;
	vector<string> *inner = NULL;
	size_t p = 0, sb = 0;
	for(size_t i = 0; i < s.size(); i++) {
		if(s[i] == '[') { inner = new vector<string>(); p = i + 1; sb++; }
		else if(s[i] == ']') { inner->push_back(s.substr(p, i - p)); outer.push_back(inner); p = i + 1; sb--; }
		else if(s[i] == ',' && sb) { inner->push_back(s.substr(p, i - p)); p = i + 1; }
	}
	return outer;
}

int process_query(string whoami, string iporhostname, string credentials, string query, map<string, string> addresses) {
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
	query_metadata.credentials_size = credentials.size();
	query_metadata.request_size = query.size();

	if(send(sock_fd, (SCAST *)&query_metadata, sizeof(query_metadata), 0) == -1) {
		cerr << "Could not send query (" << errno << ")" << endl;
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

		string c_sets_of_sets(answer, 1, answer_metadata.size - 2);
		cout << iporhostname << ":" << port << " says: find these additional credentials '" << c_sets_of_sets << "'." << endl;

		vector< vector<string> * > v = split(c_sets_of_sets);

		int positive_results = 0;
		stringstream new_credentials; new_credentials << "(" << credentials << ")";
		for(size_t i = 0; i < v.size(); i++) {
			size_t j = 0;
			int return_value = FAILURE;
			while(j < v[i]->size() && return_value != SUCCESS) {
				size_t p = (*v[i])[j].find("says");
				if(p != string::npos) {
					if(addresses.find((*v[i])[j].substr(0, p - 1)) == addresses.end())
						cerr << "Address for '" << (*v[i])[j].substr(0, p - 1) << "' not found." << endl;
					else
						return_value = process_query(whoami, addresses[(*v[i])[j].substr(0, p - 1)], whoami + " says " + (*v[i])[j] , (*v[i])[j] , addresses);
				}
				j++;
			}
			if(return_value == SUCCESS) {
				new_credentials << " and (" << (*v[i])[j - 1] << ")";
				positive_results++;
			} else break;
		}

		if(positive_results == (int)v.size())
			answer_metadata.status = process_query(whoami, iporhostname + ":" + port, new_credentials.str(), query, addresses);

		free(answer);
		for(size_t i = 0; i < v.size(); i++) delete v[i];
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
			cerr << "Malformed request file" << endl;
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

void process_requests(string whoami, const char *fn, string credentials, map<string, string> addresses) {
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
			process_query(whoami, line.substr(line.find_first_not_of(" \t", p + 1), line.find_last_not_of(" \t") - line.find_first_not_of(" \t", p + 1) + 1), credentials, line.substr(0, p), addresses);
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
	struct arg_end *end = arg_end(23);
	void *argtable[] = {help, whoami, credentials, request, addresses, end};

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

	if(credentials->count > 0)
		process_requests(whoami->sval[0], request->filename[0], process_credentials(credentials->filename[0]), process_addresses(addresses->filename[0]));
	else
		process_requests(whoami->sval[0], request->filename[0], "", process_addresses(addresses->filename[0]));

	arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));

	return 0;
}
