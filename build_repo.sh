

cd compcert

./configure ia32-linux
make proof -j8
cd ..

./configure
make -j8
