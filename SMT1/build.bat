
mkdir build-dir
cd build-dir

cmake ..
cmake --build . --config Release

Release\SMT1.exe ..\..\Benchmark1\formula1.cnf

