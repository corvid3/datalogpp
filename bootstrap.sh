#!/bin/bash

if [ ! -d $HOME/.hewg/bootstrap/crow.datalogpp ]; then
  mkdir -p $HOME/.hewg/bootstrap/crow.datalogpp
fi


g++ -std=c++23 -Wall -Wextra -O2 src/datalogpp.cc -c -o datalogpp.o
ar rcs libdatalogpp.a datalogpp.o

cp include/datalogpp.hh $HOME/.hewg/bootstrap/crow.datalogpp/
cp libdatalogpp.a $HOME/.hewg/bootstrap/
