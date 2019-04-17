cmake_minimum_required(VERSION 3.12)
project(AlphaTank)

set(CMAKE_CXX_STANDARD 17)

add_executable(MCTS mcts.cpp)
add_executable(Coperate cooperate.cpp)
add_executable(AlphaTank alphatank.cpp)