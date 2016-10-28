#!/usr/bin/env bash

set -e

make cleaner

git pull

pushd ../StructTact/ \
  && make clean \
  && git pull \
  && ./configure \
  && make
popd

pushd ../PrettyParsing/ \
  && make clean \
  && git pull \
  && ./configure \
  && make
popd

make compcert

./configure

make plugin

# first make will fail
make \
  || make sanitize && make

make test
