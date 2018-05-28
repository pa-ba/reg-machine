# Calculating compilers for register machines

This repository contains mechanised compiler calculations for register
machines. The calculations use a partial order on the memory instead
of equality for calculation.

## File Structure

Below we list the relevant Coq files for the calculations:

 - [Arith.v](Arith.v): arithmetic expressions 
 - [Exceptions.v](Exceptions.v): arithmetic expressions + exceptions
 - [StateGlobal.v](StateGlobal.v): global state
 - [StateLocal.v](StateLocal.v): local state
 - [LambdaBad.v](LambdaBad.v): call-by-value lambda calculus without a
   stack which yields an unsatisfactory compiler and machine
 - [LambdaStack.v](LambdaStack.v): call-by-value lambda calculus with
   a stack which yields a much more realistic compiler and machine
 - [LambdaTruncate.v](LambdaTruncate.v): variant of
   [LambdaStack.v](LambdaStack.v) is more realistic as it only copies
   a bounded set of registers to the stack (via truncation)
 - [LambdaException.v](LambdaException.v): lambda calculus +
   exceptions, based on [LambdaTruncate.v](LambdaTruncate.v)

The remaining files are used to define the Coq tactics to support
reasoning in calculation style and to provide auxiliary concepts:
 - [Tactics.v](Tactics.v): tactics for calculation style proofs
 - [Machine.v](Machine.v): auxiliary definitions and tactics for
    virtual machines 
 - [Memory.v](Memory.v): the (axiomatic) memory model
 - [LinearMemory.v](LinearMemory.v): instantiation of the memory model
 - [ListIndex.v](ListIndex.v): definitions to index elements in a list

