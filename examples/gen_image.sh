#!/bin/sh

if [ "$#" -ne 1 ] ; then
	echo "usage: $0 <tex-file>"
	exit 1
fi

perl tex2png.pl -dpi 300 -white -file $1
