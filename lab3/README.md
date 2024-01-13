Lab 3: Code Generator for C--
=============================

# Summary

The objective of this assignment is to write a code generator from a fragment C-- of the C/C++ programming language to JVM, the Java Virtual Machine.
The code generator should produce Java class files, which can be run in the Java bytecode interpreter so that they correctly perform all their input and output actions.

The code generator is partially characterized by compilation schemes in Chapter 6 of the PLT book.
More JVM instructions are given in Appendix B of the book.
These explanations follow Jasmin assembler; the code generator may emit Jasmin assembly code into text files, which are then processed further by [Jasmin](#jasmin-tips) to create class files.

The recommended implementation is via a BNF grammar processed by the BNF Converter (BNFC) tool.
The syntax tree created by the parser is first type checked by using the type checker created in Lab 2.
The code generator should then make a pass over the type-annotated syntax produced by the type checker.

The approximate size of the grammar is 50 rules, and the code generator should be around 300-700 lines, depending on the programming language used.
All BNFC supported languages can be used, but guidance is guaranteed only for Haskell and Java.

Before the work can be submitted, the program has to pass the [test suite](testsuite/).

# Method

The recommended procedure for the compiler is two passes:

1. build a symbol table that for every function gives its type in a form usable for JVM code generation;
2. compile the program by generating a class file containing every source code function as a method.

You can start by copying your `TypeChecker` from Lab 2 to the `src/` directory.
Make sure that the type-annotated syntax indicates where a conversion from int to double occurs, such that the conversion instruction `i2d` can be placed by the code generator.

# Language specification

The language is the same as in Lab 2, except the handling of uninitialized variables, and you can reuse the parser and type checker.

Programs using uninitialized variables fall under undefined behavior in this lab, meaning that any semantics for such programs is allowed.

There are four built-in functions:
* `void printInt(int x)` prints an integer and a newline in standard output.
* `void printDouble(double x)` prints a double and a newline in standard output.
* `int readInt()` reads an integer from standard input.
* `double readDouble()` reads a double from standard input.

These functions can be defined in a separate **runtime** class, which can be obtained e.g. from writing these functions in Java and compiling to a class file.
**A ready-made Java file is [`Runtime.java`](Runtime.java)**.

## Bytecode verification

When running your compiled programs, the Java bytecode you have generated will be automatically sanity-checked by a Java bytecode verifier (which is part of the JVM you are using).
The verifier will e.g. check that there are no operand stack overflows or underflows and that all local variable uses and stores are valid.
If your code does not pass the verifier, a `java.lang.VerifyError` exception will be thrown (with an often useful error message).

## Class structure

Boilerplate code, see the PLT book, Chapter 6, or the example below.

## Functions

Methods in the class, `main` special, see Chapter 6, or example below.

Note that all returns must be explicit in Java bytecode, including returns from functions returning `void`.
(The bytecode verifier will complain if it thinks that a function may end without returning.)

For non-`void`-returning functions you are allowed to assume that returns are always properly placed by the programmer who wrote the input source code.
However, for `void`-returning functions you must consider the possibility that no explicit return statement was included in the program source code.

## Statements and expressions

The semantics is the same as in Lab 2 (again, except for programs using uninitialized variables).
In other words, running the generated classes in `java` produces the same behavior as running the source code in the `lab2` interpreter.

## Example

File [good03.cc](good03.cc)
```cpp
int main ()
{
  int arg = readInt() ;
  int ret = 1 ;

  int i = 1 ;

  while (i < arg + 1) {
    ret = i * ret ;
    ++i ;
  }

  printInt(ret) ;
  return 0 ;
}
```
could compile to [good03.j](good03.j) as follows:
```scheme
;; Boilerplate: a wrapping class for cc code

.class public good03
.super java/lang/Object

.method public <init>()V
  .limit locals 1
  .limit stack 1

  aload_0
  invokespecial java/lang/Object/<init>()V
  return

.end method

;; The java-style main method calls the cc main

.method public static main([Ljava/lang/String;)V
  .limit locals 1
  .limit stack 1

  invokestatic good03/main()I
  pop
  return

.end method

;; Program

.method public static main()I
  .limit locals 3
  .limit stack 3

  ;; int arg = readInt();

  invokestatic Runtime/readInt()I
  istore_0

  ;; int ret = 1;

  iconst_1
  istore_1

  ;; int i = 1;

  iconst_1
  istore_2

  ;; while (i < arg + 1)

  L0:            ;; // beginning of loop, check condition
  iload_2        ;; i
  iload_0
  iconst_1
  iadd           ;; arg + 1
  if_icmplt L2   ;; i < arg + 1 ?
  iconst_0
  goto L3
  L2:            ;; i < arg + 1 is true
  iconst_1
  L3:            ;; i < arg + 1 is false
  iconst_0
  if_icmpeq L1   ;; if last comparison was false, exit while loop

  ;; ret = i * ret

  iload_2
  iload_1
  imul
  istore_1
  iload_1
  pop

  ;; ++i

  iload_2
  iconst_1
  iadd
  istore_2  ;; // i = i + 1
  iload_2
  pop

  ;; // continue loop
  goto L0

  ;; printInt(ret)

  L1:
  iload_1
  invokestatic Runtime/printInt(I)V
  nop

  ;; return 0

  iconst_0
  ireturn

.end method
```
(The comments are only for seeing the connection between .cc and .j).

A smarter compiler might generate the following better code for the `while` loop:
```scheme
    ;; while (i < arg + 1)

    goto    L1
L0:

    ;; ret = i * ret;

    iload_2
    iload_1
    imul
    istore_1

    ;; ++ i;

    iinc    2 1
L1:
    iload_2
    iload_0
    iconst_1
    iadd
    if_icmplt   L0
```
This code has only 11 instructions instead of the 23 above.

# Solution format

## Solution templates

For Haskell and Java there are stubs that can be extended to the full solution.
Just link one of these subdirectory to `src/`:

- [`src-haskell/`](src-haskell/): Haskell template
- [`src-java/`](src-java/): Java template

These directories contain the grammar, stubs for type checker and compiler, code to invoke Jasmin, [jasmin.jar](jasmin.jar), and suitable makefiles.

The stubs match the requirements for the solution format as detailed in the following:

## Input and output

The code generator must be a program called `lab3`, which is executed by the command
```console
$ lab3 <SourceFile>
```
and produces a class (`.class`) file.
It may do this by first generating Jasmin assembly code (a `.j` file) and then calling Jasmin on this code.
For help with building the Jasmin file, refer to the [Jasmin instructions](http://jasmin.sourceforge.net/instructions.html) and [Java bytecode instruction listings](https://ben.wikipedia.org/wiki/Java_bytecode_instruction_listings).
Jasmin can be called by
```console
$ java -jar jasmin.jar <File>.j
```
or
```console
$ jasmin <File>.j
```
if you have installed Jasmin as a stand-alone program.

The generated class file should have the same name and be **in the same directory** as the original source file:
```console
$ lab3 ../a/b/c.cc
```
This should produce a class file `../a/b/c.class`.
To instruct Jasmin to place the file `c.class` in the correct directory, use Jasmin's  option `-d`, for instance, `jasmin -d ../a/b ../a/b/c.j`.
(Note: to _run_ a class file in a subdirectory, that directory needs to be in the `CLASSPATH`, e.g., `java -cp ../a/b:path/to/runtime c` can be used to run `../a/b/c.class` without changing to its directory, assuming that `Runtime.class` is located in `path/to/runtime`.)

The output at failure is a code generator error, or `TYPE ERROR` or `SYNTAX ERROR` as in Lab 2.

The input can be read not only from user typing on the terminal, but also from standard input redirected from a file or by `echo`.
For instance:
```console
$ echo 20 | java good03
$ java good03 <<< 20
$ java good03 < input.txt
```
(where `input.txt` might contain `20`).

## Example of success

Source file:
```cpp
// file good.cc
int main ()
{
  int i = readInt() ; // e.g. 5

  printInt(i) ;       // e.g. 5
  printInt(i++) ;     // e.g. 5
  printInt(i) ;       // e.g. 6
  printInt(++i) ;     // e.g. 7
  printInt(i) ;       // e.g. 7

  return 0 ;
}
```
Running the compiler:
```console
$ tree
.
├── Runtime.class
└── test
    └── good.cc

$ lab3 test/good.cc
$ tree
.
├── Runtime.class
└── test
    ├── good.cc
    └── good.class

$ echo 5 | java -cp test:. good
5
5
6
7
7
```

## Compiling the code generator

The compiler is submitted as source files that can be compiled by typing `make`.

# Test programs

We also provide a [test suite](testsuite/) for Lab 3 (with the same test cases as for Lab 2).
Passing all these tests is **required** for passing this lab.

There are pre-configured testsuite runner scripts in the repository root.
(These scripts only differ in the way they invoke the testsuite runner which is written in Haskell.)
- [`run-test-ghc.sh`](run-test-ghc.sh): Run testsuite with `runghc`.
- [`run-test-cabal.sh`](run-test-cabal.sh): Run testsuite with `cabal run`.
- [`run-test-stack.sh`](run-test-stack.sh): Run testsuite with `stack run`.

The scripts assume your sources in `src/` (see section [Submission](#submission)).

## Jasmin tips

Jasmin is available on [Sourceforge](http://jasmin.sourceforge.net/).
Note that version 2.4 is included in the [stubs](#solution-templates)
and that there are also versions on e.g. Ubuntu (`apt install jasmin-sable`) and macOS (`brew install jasmin`).

Make sure your class names in Jasmin have simple names without slashes or dots.
If the first line of your Jasmin file is
```
.class public x/y/z.cc
```
then Jasmin will compile it to a file
```
x/y/z/cc.class
```
regardless of what the name of the `.j` file is.
The easiest option, and also what the test suite expects, is that your class name is just a string without any slashes or dots (in this example, just "z").

Also note that it seems that each statement in your Jasmin file needs to be **terminated** by a newline, in particular the last `.end method` directive.

**Important:**
Make sure that your compiler waits for the Jasmin conversion to finish before exiting.
In other words, it shouldn't exit before the `.class` file has been written.
For example when using Haskell, you can do the following:
```haskell
p <- runCommand <call jasmin here>
waitForProcess p
```
or with at least version 1.2.0.0 (December 2013) of library [process](https://hackage.haskell.org/package/process) installed, simply:
```haskell
callCommand <call jasmin here>
```

# Success criteria

Your program must be compatible with the [test suite](testsuite/) and meet the specification in this document in all respects.

The code you generate must pass the Java bytecode verification.
Note: Passing the verifier check means no additional work beyond generating correct code (such as not popping empty stacks etc.).

The solution must be written in an easily readable and maintainable way.
In particular, tailoring it for the programs in the test suite is not maintainable!

# Submission

1. Do not submit your solution before it passes the [test suite](testsuite/) if you want proper grading.

2. Make sure your solution has the following structure:
   - Subdirectory `src/` contains the sources of your solution plus a `Makefile`.
   - After `make` is invoked in `src/`, there should be a runnable program `src/lab3`.
   - This program takes a filepath as command-line parameter and type-checks and compiles this file.

   See the example solution stubs `src-haskell/` and `src-java/`.
   If you solve this lab in Haskell or Java, you can symlink `src/` to one of `src-haskell/` or `src-java/` and work there.
   For another programming language, create `src/` and place a suitable `Makefile` there.

3. Make sure all your source files are pushed to your lab repository on `git.chalmers.se`.
   Do not submit generated files, only submit source files.

   Run the testsuite _on the server_ by pushing a `test` tag (e.g. `test0`, `test1` etc.).

4. Test that your submission builds in a fresh clone:
   ```console
   TMPDIR=`mktemp -d`
   git clone YOUR_LAB_REPO $TMPDIR
   cd $TMPDIR/src
   make
   ./lab3
   ```
    On Windows, the tools used here (`bash`, `mktemp`, `make`) are provided by both WSL and [MSYS2](https://www.msys2.org/).

5. Finalize your submission by adding a `submission` tag (e.g. `submission0`, `submission1`).
   The last submission before the deadline counts.
