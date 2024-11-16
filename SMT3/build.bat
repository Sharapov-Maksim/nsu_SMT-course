
mkdir build-dir
cd build-dir

cmake ..
cmake --build . --config Release

Release\SMT3.exe ..\..\Benchmark\2sat_test5.cnf

