
mkdir build-dir
cd build-dir

cmake ..
cmake --build . --config Release

Release\SMT2.exe ..\..\Benchmark\formula1.cnf

