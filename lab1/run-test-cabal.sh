#!/bin/sh

# Programming Language Technology (Chalmers DAT151 / GU DIT231)
# (C) 2022-23 Andreas Abel
# All rights reserved.

# Run PLT lab 1 testsuite on grammar file CC.cf

root="$PWD"
cd testsuite
cabal run plt-test-lab1 -- "$root/CC.cf"
