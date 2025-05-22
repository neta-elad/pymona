cmake_minimum_required(VERSION 3.26)

project(pymona LANGUAGES C CXX)

# Set C++ standard
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
add_compile_options(-Werror)

if (DEFINED ENV{FORCE_DEBUG})
    message(WARNING "Forcing DEBUG build with debug symbols")
    set(CMAKE_BUILD_TYPE Debug)
    add_compile_options(-g)
    set(CMAKE_STRIP "")
endif()


add_subdirectory(vendor)

if (NOT SKBUILD)
    message(WARNING "\
    This CMake file is meant to be executed using 'scikit-build'. Running
    it directly will almost certainly not produce the desired result. If
    you are a user trying to install this package, please use the command
    below, which will install all necessary build dependencies, compile
    the package in an isolated environment, and then install it.
    =====================================================================
     $ pip install .
    =====================================================================
    If you are a software developer, and this is your own package, then
    it is usually much more efficient to install the build dependencies
    in your environment once and use the following command that avoids
    a costly creation of a new virtual environment at every compilation:
    =====================================================================
     $ pip install nanobind scikit-build-core[pyproject]
     $ pip install --no-build-isolation -ve .
    =====================================================================
    You may optionally add -Ceditable.rebuild=true to auto-rebuild when
    the package is imported. Otherwise, you need to re-run the above
    after editing C++ files.")
    set(nanobind_DIR ".venv/lib/python3.12/site-packages/nanobind/cmake")
endif()

# Try to import all Python components potentially needed by nanobind
find_package(Python 3.12
        REQUIRED COMPONENTS Interpreter Development.Module
        OPTIONAL_COMPONENTS Development.SABIModule)

# Import nanobind through CMake's find_package mechanism
find_package(nanobind CONFIG REQUIRED)

# We are now ready to compile the actual extension module
nanobind_add_module(
        # Name of the extension
        _pymona

        # Target the stable ABI for Python 3.12+, which reduces
        # the number of binary wheels that must be built. This
        # does nothing on older Python versions
        STABLE_ABI

        # Build libnanobind statically and merge it into the
        # extension (which itself remains a shared library)
        #
        # If your project builds multiple extensions, you can
        # replace this flag by NB_SHARED to conserve space by
        # reusing a shared libnanobind across libraries
        NB_STATIC

        # Source code goes here
        src/pymona.cpp
)
target_link_libraries(_pymona PRIVATE mona)

if (DEFINED ENV{FORCE_DEBUG})
    set_target_properties(_pymona PROPERTIES
            COMPILE_FLAGS "-g"
            LINK_FLAGS "-g"
    )
endif()

nanobind_add_stub(
        _pymona_stub
        MODULE _pymona
        OUTPUT _pymona.pyi
        PYTHON_PATH $<TARGET_FILE_DIR:_pymona>
        DEPENDS _pymona
        MARKER_FILE py.typed
)

# Install directive for scikit-build-core
install(TARGETS _pymona LIBRARY DESTINATION pymona)
install(FILES "${CMAKE_BINARY_DIR}/py.typed" "${CMAKE_BINARY_DIR}/_pymona.pyi" DESTINATION pymona)