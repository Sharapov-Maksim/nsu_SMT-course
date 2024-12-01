
mkdir build-dir
cd build-dir

cmake ..
cmake --build . --config Release

Release\SMT4.exe ..\..\Benchmark\6cnf20_28000_28000_2.shuffled.cnf

