cmake_minimum_required(VERSION 3.10)

project(deltaDB)

# use C++17 standard
set(CMAKE_CXX_STANDARD 17)

if(TARGET SCIP::SCIP)
  # find package by SCIP PATH
  find_package(SCIP CONFIG PATHS ${SCIP_BINARY_DIR} REQUIRED)
else()
  find_package(SCIP REQUIRED)
endif()

message("found SCIP_INCLUDE_DIRS=${SCIP_INCLUDE_DIRS}")
include_directories(${SCIP_INCLUDE_DIRS})

find_path(GMP_INCLUDE_DIRS
    NAMES gmp.h gmpxx.h
    HINTS ${GMP_DIR}
    PATH_SUFFIXES include)
message("GMP_INCLUDE_DIRS=${GMP_INCLUDE_DIRS}")
include_directories(${GMP_INCLUDE_DIRS})

add_executable(deltaDB main.cpp)

# link specific object files we need
target_link_libraries(deltaDB ${SCIP_LIBRARIES} ${GMP_LIBRARIES})
