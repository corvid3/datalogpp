#!/bin/bash

g++ -std=c++23 -Wall -Wextra -O2 src/datalogpp.cc -c -o datalogpp.o
ar rcs libdatalogpp.a datalogpp.o

sudo cp include/datalogpp.hh /usr/local/include/
sudo cp libdatalogpp.a /usr/local/lib/
