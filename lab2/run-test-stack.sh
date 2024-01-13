#!/bin/sh

# Programming Language Technology (Chalmers DAT151 / GU DIT231)
# (C) 2022-23 Andreas Abel
# All rights reserved.

# Run PLT lab 2 testsuite on directory src/

root="$PWD"
cd testsuite
stack run -- "$root/src"
