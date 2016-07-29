


cd compcert

./configure ia32-linux
make proof -j8
make driver/Version.ml
make -f Makefile.extr cparser/pre_parser_messages.ml
cd ..

./configure
make -j8

bash build.sh

