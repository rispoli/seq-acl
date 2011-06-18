struct c2s_t {
	size_t credentials_size;
	size_t request_size;
};

#define SUCCESS 1
#define COUNTERMODELS 2
#define FAILURE -1

struct answer_t {
	size_t size;
	int status;
};
