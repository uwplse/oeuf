


cd compcert

./configure ia32-linux
make proof -j8
make driver/Version.ml
cd ..

./configure
make -j8

bash build.sh

