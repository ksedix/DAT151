-- Programming Language Technology (Chalmers DAT 151, GU DIT 231)
-- (C) Andreas Abel, 2023
-- All rights reserved.

module Compiler where

open import Library
open import TypedSyntax

-- Entry point: compiler program to jasmin text.

compileProgram : (prg : Program) → List String
compileProgram prg = "COMPILER ERROR: not yet implemented" ∷ "" ∷ header
  where
  header
    = ".class public CLASSNAME"
    ∷ ".super java/lang/Object"
    ∷ ""
    ∷ ".method public <init>()V"
    ∷ ".limit stack 1"
    ∷ ""
    ∷ "    aload_0"
    ∷ "    invokespecial java/lang/Object/<init>()V"
    ∷ "    return"
    ∷ ""
    ∷ ".end method"
    ∷ ""
    ∷ ".method public static main([Ljava/lang/String;)V"
    ∷ ".limit stack 1"
    ∷ ""
    ∷ "    invokestatic CLASSNAME/main()I"
    ∷ "    pop"
    ∷ "    return"
    ∷ ""
    ∷ ".end method"
    ∷ []
