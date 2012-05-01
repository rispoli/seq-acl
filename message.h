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

struct c2s_t {
	size_t principal_size;
	size_t credentials_size;
	size_t request_size;
	size_t signature_size;
};

#define SUCCESS 1
#define COUNTERMODELS 2
#define FAILURE -1

struct answer_t {
	size_t size;
	size_t signature_size;
	int status;
};
