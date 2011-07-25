#include <argtable2.h>
#include <errno.h>
#include <fstream>
#include <iostream>
#include "message.h"
#include <signal.h>
#include <sstream>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
using namespace std;

#if defined (WIN32) && !defined (__CYGWIN32__) // It's not Unix, really. See? Capital letters.

#define __WINDOWS

#define _WIN32_WINNT 0x501 // To get getaddrinfo && freeaddrinfo working with MinGW.
#include <windows.h>
#include <winsock2.h>
#include <ws2tcpip.h>

#define SCAST const char
#define RCAST char

string executable_path;
string options;
string policy_fn;
string log_fn;
int log_level;
struct in_addr sin_addr;

#else

#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>

#define SCAST void
#define RCAST void
#define closesocket(fd) close(fd)

#endif

#ifdef __WINDOWS
void log_message(string filename, string message);
BOOL CtrlHandler(DWORD) {
	if(log_level > 0)
		log_message(log_fn, "server stopped");

	WSACleanup();

	return 0;
}
#else
int termination_pipe[2];

void sig_handler(int) {
	FILE *p = fdopen(termination_pipe[1], "w");
	fprintf(p, "1");
	fclose(p);
	close(termination_pipe[1]);
}
#endif

void log_message(string filename, string message) {
	FILE *logfile = fopen(filename.c_str(), "a");
	if(!logfile) {
		cerr << "Could not write to log file: " << filename << endl;
		return;
	}
	stringstream ss_time;
	time_t now = time(NULL);
	ss_time << ctime(&now);
	fprintf(logfile, "%s\n", ("[" + ss_time.str().substr(0, ss_time.str().length() - 1) + "] " + message).c_str());
	fclose(logfile);
}

#ifdef __WINDOWS
DWORD WINAPI handle_query(void *lp) {
	int &sock_fd = *(int *)lp;
#else
int handle_query(string executable_path, string options, int sock_fd, string policy_fn, string log_fn, int log_level, struct in_addr sin_addr) {
	signal(SIGCHLD, SIG_DFL);
#endif

	c2s_t query_metadata;
	if(recv(sock_fd, (RCAST *)&query_metadata, sizeof(query_metadata), 0) == -1) {
		cerr << "Could not receive data (" << errno << ")" << endl;
		closesocket(sock_fd);
		return 1;
	}

	char *principal = (char *)malloc(query_metadata.principal_size + 1);
	memset(principal, 0, query_metadata.principal_size + 1);
	if(recv(sock_fd, (RCAST *)principal, query_metadata.principal_size, 0) == -1) {
		cerr << "Could not receive data (" << errno << ")" << endl;
		closesocket(sock_fd);
		free(principal);
		return 1;
	}
	char *credentials = NULL;
	if(query_metadata.credentials_size > 0) {
		credentials = (char *)malloc(query_metadata.credentials_size + 1);
		memset(credentials, 0, query_metadata.credentials_size + 1);
		if(recv(sock_fd, (RCAST *)credentials, query_metadata.credentials_size, 0) == -1) {
			cerr << "Could not receive data (" << errno << ")" << endl;
			closesocket(sock_fd);
			free(credentials);
			return 1;
		}
	}
	char *query = (char *)malloc(query_metadata.request_size + 1);
	memset(query, 0, query_metadata.request_size + 1);
	if(recv(sock_fd, (RCAST *)query, query_metadata.request_size, 0) == -1) {
		cerr << "Could not receive data (" << errno << ")" << endl;
		closesocket(sock_fd);
		free(query);
		if(credentials != NULL) free(credentials);
		return 1;
	}

	stringstream command;
	if(credentials != NULL)
		command << executable_path << options << " 'prove_c(" << policy_fn << ", " << string(principal) << ", " << string(credentials) << ", " << string(query) << ")' 2>&1";
	else
		command << executable_path << options << " 'prove_c(" << policy_fn << ", " << string(principal) << ", " << string(query) << ")' 2>&1";
cout << command.str() << endl;

	FILE *fpipe;
	char buffer_p[256];
	memset(buffer_p, 0, sizeof(buffer_p));

	if(!(fpipe = popen(command.str().c_str(), "r"))) {
		cerr << "Could not execute command: " << command.str() << " (" << errno << ")" << endl;
		closesocket(sock_fd);
		free(query);
		if(credentials != NULL) free(credentials);
		return 1;
	}

	stringstream c_output;
	while(fgets(buffer_p, sizeof(buffer_p), fpipe))
		c_output << buffer_p;
	int exit_status = pclose(fpipe);

	struct answer_t answer;

	string result = c_output.str();
	if(WEXITSTATUS(exit_status)) {
		answer.status = FAILURE;
		answer.size = result.size();
	} else {
		if(result == "granted") {
			answer.status = SUCCESS;
			answer.size = 0;
		} else {
			answer.status = COUNTERMODELS;
			answer.size = result.size();
		}
	}

    if(send(sock_fd, (SCAST *)&answer, sizeof(answer), 0) == -1) {
		cerr << "Could not send answer (" << errno << ")" << endl;
		closesocket(sock_fd);
		free(query);
		if(credentials != NULL) free(credentials);
		return 1;
	}
	if(answer.status != SUCCESS)
		if(send(sock_fd, (SCAST *)result.c_str(), result.size(), 0) == -1) {
			cerr << "Could not send answer (" << errno << ")" << endl;
			closesocket(sock_fd);
			free(query);
			if(credentials != NULL) free(credentials);
			return 1;
		}

	if(log_level > 0) {
		stringstream message;
		message << "received message from: " << inet_ntoa(sin_addr);
		if(log_level > 1) {
			message << ", query: '" << string(query);
			if(credentials != NULL) message << "', credentials: '" << string(credentials);
			message << "', result: " << result;
		}
		log_message(log_fn, message.str());
	}

	closesocket(sock_fd);
	free(query);
	if(credentials != NULL) free(credentials);

	return 0;
}

void closesocket_and_cleanup(int sock_fd) {
	closesocket(sock_fd);
#ifdef __WINDOWS
	WSACleanup();
#endif
}

int main(int argc, char *argv[]) {

#ifdef __WINDOWS
	SetConsoleCtrlHandler((PHANDLER_ROUTINE)CtrlHandler, TRUE);
#else
	signal(SIGINT, sig_handler);
	signal(SIGTERM, sig_handler);
#endif

	struct arg_lit *help = arg_lit0("h", "help", "print this help and exit");
#ifndef __WINDOWS
	struct arg_lit *daemon = arg_lit0("d", "daemon", "run in background");
#endif
	struct arg_file *executable = arg_file0("e", "executable", NULL, "Prolog executable path (default: swipl)");
	struct arg_file *policy = arg_file0("o", "policy", NULL, "policy path (default: policy)");
	struct arg_int *port_number = arg_int0("p", "port-number", NULL, "port number to listen on (default: 3333)");
	struct arg_file *log_file = arg_file0("L", "log-file", NULL, "log-file path (default: queries.log)");
	struct arg_int *log_l = arg_int0("l", "log-level", NULL, "0 - off, 1 - default, 2 - verbose");
	struct arg_end *end = arg_end(23);
#ifdef __WINDOWS
	void *argtable[] = {help, executable, policy, port_number, log_file, log_l, end};
#else
	void *argtable[] = {help, daemon, executable, policy, port_number, log_file, log_l, end};
#endif

	if(arg_nullcheck(argtable) != 0) {
		cerr << "Could not allocate enough memory for command line arguments" << endl;
		arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));
		return 1;
	}

	executable->filename[0] = "swipl";
	policy->filename[0] = "policy";
	port_number->ival[0] = 3333;
	log_file->filename[0] =  "queries.log";
	log_l->ival[0] = 1;

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

#ifndef __WINDOWS
	if(daemon->count > 0) {
		int pid = fork();
		if(pid < 0) {
			cerr << "Could not run in background" << endl;
			return 1;
		} else if(pid > 0) return 0;
		setsid();
	}
#endif

#ifdef __WINDOWS
	executable_path = executable->filename[0];
	options = " -q -t halt -f credentials.pl -g";
	policy_fn = policy->filename[0];
	int port_no = port_number->ival[0];
	log_fn = log_file->filename[0];
	log_level = log_l->ival[0];
#else
	string executable_path = executable->filename[0];
	string options = " -q -t halt -f credentials.pl -g";
	string policy_fn = policy->filename[0];
	int port_no = port_number->ival[0];
	string log_fn = log_file->filename[0];
	int log_level = log_l->ival[0];
#endif

	arg_freetable(argtable, sizeof(argtable) / sizeof(argtable[0]));

#ifndef __WINDOWS
	if(pipe(termination_pipe) == -1) {
		cerr << "Could not create pipe (" << errno << ")" << endl;
		return 1;
	}
#endif

#ifdef __WINDOWS
	WSADATA wsaData;

	if(WSAStartup(MAKEWORD(2, 2), &wsaData) != 0) {
		cerr << "Could not find Winsock dll" << endl;
		return DLV_ERROR;
	}

	if(LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2) {
		cerr << "Wrong Winsock version" << endl;
		WSACleanup();
		return DLV_ERROR;
	}
#endif

	int sock_fd = socket(AF_INET, SOCK_STREAM, 0);
	if(sock_fd == -1) {
		cerr << "Could not open socket (" << errno << ")" << endl;
		return 1;
	}
	int on = 1;
	int rc = setsockopt(sock_fd, SOL_SOCKET, SO_REUSEADDR, (char *)&on, sizeof(on));
	if(rc == -1) {
		cerr << "Could not set socket options (" << errno << ")" << endl;
		closesocket_and_cleanup(sock_fd);
		return 1;
	}

	struct sockaddr_in serv_addr, cli_addr;
	memset(&serv_addr, 0, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	serv_addr.sin_addr.s_addr = INADDR_ANY;
	serv_addr.sin_port = htons(port_no);
	if(bind(sock_fd, (struct sockaddr *)&serv_addr, sizeof(serv_addr)) == -1) {
		cerr << "Could not bind port: " << port_no << endl;
		closesocket_and_cleanup(sock_fd);
		return 1;
	}
	listen(sock_fd, SOMAXCONN);
	stringstream startup; startup << "server started (pid: " << getpid() << "), listening on port: " << port_no << ", policy: " << policy_fn;
	if(log_level > 0)
		log_message(log_fn, startup.str());
#ifndef __WINDOWS
	signal(SIGCHLD, SIG_IGN);
	fd_set fd_set_s;
#endif
	int new_sock_fd, cli_len = sizeof(cli_addr);
	while(1) {
#ifndef __WINDOWS
		do {
			FD_ZERO(&fd_set_s);
			FD_SET(sock_fd, &fd_set_s);
			FD_SET(termination_pipe[0], &fd_set_s);
			rc = select((sock_fd >= termination_pipe[0] ? sock_fd : termination_pipe[0]) + 1, &fd_set_s, NULL, NULL, NULL);
		} while((rc == -1) && (errno == EINTR));

		if(rc == -1) {
			cerr << "Could not select (" << errno << ")" << endl;
			close(sock_fd);
			close(termination_pipe[0]);
			close(termination_pipe[1]);
			return 1;
		}

		if(FD_ISSET(termination_pipe[0], &fd_set_s)) {
			close(sock_fd);
			FD_CLR(sock_fd, &fd_set_s);
			close(termination_pipe[0]);
			FD_CLR(termination_pipe[0], &fd_set_s);
			break;
		}
#endif

		if((new_sock_fd = accept(sock_fd, (struct sockaddr *)&cli_addr, (socklen_t *)&cli_len)) != -1) {
#ifdef __WINDOWS
			sin_addr = cli_addr.sin_addr;
			CreateThread(0, 0, &handle_query, (void *)&new_sock_fd , 0, 0);
#else
			int pid;
			struct sockaddr_in serv_addr_;
			socklen_t serv_addr_size = sizeof(struct sockaddr);
			switch(pid = fork()) {
				case -1:
					cerr << "Could not fork child (" << errno << ")" << endl;
					break;
				case 0:
					close(sock_fd);
					close(termination_pipe[0]);
					close(termination_pipe[1]);
					getsockname(new_sock_fd, (struct sockaddr *)&serv_addr_, &serv_addr_size);
					return handle_query(executable_path, options, new_sock_fd, policy_fn, log_fn, log_level, cli_addr.sin_addr);
				default:
					close(new_sock_fd);
			}
#endif
		} else {
			cerr << "Could not accept connection (" << errno << ")" << endl;
			closesocket_and_cleanup(sock_fd);
			return 1;
		}
	}

	closesocket_and_cleanup(sock_fd);

	if(log_level > 0)
		log_message(log_fn, "server stopped");
	return 0;
}
