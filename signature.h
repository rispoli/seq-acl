/*

   Copyright 2012 Daniele Rispoli, Valerio Genovese, Deepak Garg

   This file is part of smart-rsync.

   smart-rsync is free software: you can redistribute it and/or modify
   it under the terms of the GNU Affero General Public License as
   published by the Free Software Foundation, either version 3 of the
   License, or (at your option) any later version.

   smart-rsync is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Affero General Public License for more details.

   You should have received a copy of the GNU Affero General Public
   License along with smart-rsync.  If not, see <http://www.gnu.org/licenses/>.

*/

#include <iostream>
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/pem.h>
#include <stdio.h>
#include <string>
#include <string.h>
using namespace std;

#define CLEANUP(err_func) \
		cerr << err_func << ": failed (" << ERR_get_error() << ")" << endl; \
		EVP_PKEY_free(pkey); \
		EVP_MD_CTX_cleanup(&ctx); \
		ERR_remove_state(0); \
		CRYPTO_cleanup_all_ex_data();

unsigned char * sign(const char *private_key_fn, string message, unsigned int *siglen) {
	FILE *pkey_fp = NULL;
	if((pkey_fp = fopen(private_key_fn, "r")) == NULL) {
		cerr << "Could not open RSA Private Key file (" << errno << ")" << endl;
		return NULL;
	}

	EVP_PKEY *pkey = NULL;
	if((pkey = PEM_read_PrivateKey(pkey_fp, NULL, NULL, NULL)) == NULL) {
		cerr << "Could not load RSA Private Key (" << ERR_get_error() << ")" << endl;
		fclose(pkey_fp);
		ERR_remove_state(0);
		CRYPTO_cleanup_all_ex_data();
		return NULL;
	}
	fclose(pkey_fp);

	EVP_MD_CTX ctx;
	EVP_MD_CTX_init(&ctx);

	if(!EVP_SignInit(&ctx, EVP_sha1())) {
		CLEANUP("EVP_SignInit")
		return NULL;
	}

	if(!EVP_SignUpdate(&ctx, message.c_str(), message.size())) {
		CLEANUP("EVP_SignUpdate")
		return NULL;
	}

	unsigned char *signature = (unsigned char *)malloc(EVP_PKEY_size(pkey));
	memset(signature, 0, EVP_PKEY_size(pkey));
	if(!EVP_SignFinal(&ctx, signature, siglen, pkey)) {
		CLEANUP("EVP_SignFinal")
		return NULL;
	}

	EVP_PKEY_free(pkey);
	EVP_MD_CTX_cleanup(&ctx);

	ERR_remove_state(0);
	CRYPTO_cleanup_all_ex_data();

	return signature;
}

int verify(const char *public_key_fn, string message, unsigned char *signature, unsigned int siglen) {
	FILE *pkey_fp = NULL;
	if((pkey_fp = fopen(public_key_fn, "r")) == NULL) {
		cerr << "Could not open RSA Public Key file (" << errno << ")" << endl;
		return FAILURE;
	}

	EVP_PKEY *pkey = NULL;
	if((pkey = PEM_read_PUBKEY(pkey_fp, NULL, NULL, NULL)) == NULL) {
		cerr << "Could not load RSA Public Key (" << ERR_get_error() << ")" << endl;
		fclose(pkey_fp);
		ERR_remove_state(0);
		CRYPTO_cleanup_all_ex_data();
		return FAILURE;
	}
	fclose(pkey_fp);

	EVP_MD_CTX ctx;
	EVP_MD_CTX_init(&ctx);

	if(!EVP_VerifyInit(&ctx, EVP_sha1())) {
		CLEANUP("EVP_VerifyInit")
		return FAILURE;
	}

	if(!EVP_VerifyUpdate(&ctx, message.c_str(), message.size())) {
		CLEANUP("EVP_VerifyUpdate")
		return FAILURE;
	}

	if(!EVP_VerifyFinal(&ctx, signature, siglen, pkey)) {
		CLEANUP("EVP_VerifyFinal")
		return FAILURE;
	}

	EVP_PKEY_free(pkey);
	EVP_MD_CTX_cleanup(&ctx);

	ERR_remove_state(0);
	CRYPTO_cleanup_all_ex_data();

	return SUCCESS;
}

string fetch_public_key(string principal, string public_keys_rn) {
	return public_keys_rn + "/" + principal + "_public.pem";
}
