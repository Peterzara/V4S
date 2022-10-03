**HW 1: Due May 10, 2022, 23:59**

README
=======

In this assignment, you will implement a verifier based on the weakest-precondition/VCGen methodology.
We will work with programs that are written in a subset ECMAScript and translate them into our imperative language Nano.

Requirements
------------
Install Microsoft's Z3 SMT solver

- Linux: https://www.howtoinstall.me/ubuntu/18-04/z3/
- MacOs: https://formulae.brew.sh/formula/z3
- Binaries: https://github.com/Z3Prover/z3/releases

Install Haskell/GHC and stack

- Follow the installation instructions on https://docs.haskellstack.org/en/stable/README/

Install 
-------

Make sure your machine has the above **requirements**.

After that, just clone the directory using 

    git clone https://github.com/gleissen/hw1.git

and you're good to go!

Run
---

You can build and run the verifier with

    $ stack run -- tests/pos/skip.js

Here, `tests/pos/skip.js` specifies the file we want to verify. If all went well
you should see something like:

    horn
    hornConfig {files = ["tests/pos/skip.js"]}

    Checking the file : "tests/pos/skip.js"
    horn: TODO: Please Implement!
    CallStack (from HasCallStack):

After filling in the right code you
should see something like:

    horn
    hornConfig {files = ["tests/pos/skip.js"]}

    Checking the file : "tests/pos/skip.js"
    Verification: passed


Running All Tests
-----------------

You can provide any number of files to the verifier. To run a specifc test, write:

    $ stack run -- path/to/file.js

All tests can be found within the `tests` directory.

To run all the positive tests you can write:

    $ stack run -- tests/pos/*

To run all negative tests, you can write:

    $ stack run -- tests/neg/*

Positive tests should give you `Verification: passed`; negative tests should show `Verification: failed`.

Writing Specifications
----------------------

Horn takes specifications in the form of loop invariants, for an example, see `tests/pos/while5.js`

Assignment
----------

You need to do three things to complete the assignment.

## Part A: Verification Condition Generation

Fill in the implementation of VC generation by
completing the relevant implementations in:

    - hw1/horn/Logic/Clauses.hs
    - hw1/horn/Horn/Nano/Nano.hs
    - hw1/horn/Horn/VCGen/VCGen.hs

in particular, wherever it says:

    error "TODO: FILL THIS IN"

In **Clauses.hs** you have to complete functions

    - subst
    - subst_exp

which implement substitution, as defined in class; These functions will be useful for implementing the VCGen rule for assignements.

In **Nano.hs**, you have to complete functions

    - toNanoBexp
    - toNanoExp
    - toNanoStmt

These functions translate programs written in ECMAScript (that is, our examples in tests/pos, tests/neg) into Nano, as defined in this file. The programs are already parsed and in the data-format defined in [this documentation](https://hackage.haskell.org/package/language-ecmascript-0.17.0.1/docs/Language-ECMAScript3-Syntax.html).

To transform While-loops, you can use function **getInvariant s** which extracts invariants specified in the loop body.

You also have to complete functions

    - expToBase
    - bexpToBase

which translate program expressions into logic, as define in file `Logic/Clauses.hs`.

File **VCGen.hs** implements verification condition generation based on weakest preconditions, as discussed in class.

You have to fill in function **generateStmtVC**. **generateStmtVC** returns the
weakest precondition for the given statement, however, it keeps as additional
state a list of vcs `VCState`, which contains verification conditions on
invariants. You can use functions **getVCs** and **addVCs** to access this
state.

**TIP:** If you don't know what a function in the existing code does, you can
look it up on Hoogle: (https://hoogle.haskell.org/). Hoogle will give you its
type and a link to the documentation.

**NOTE:**  You can **only** modify/extend the code in 
the functions mentioned above; there is no need to 
change any code elsewhere.

## Part B: Verifying A Small Suite of NanoJS Programs

Next, use your implementation to **verify** the suite of programs in

    tests/pos/*.js

To do this, you will have to understand the code in order to determine
suitable loop-invariants that you will then put into the .js file.

You can find an example loop invariant in `tests/pos/while5.js`.

Instead of Hoare-triples, Nano contains statements `assume` and `assert`.
`assume(F)` encodes an assumption that formula F holds. `assert(F)` encodes an
obligation to show that formula F holds. In particular a Hoare triple {P} s {Q}
can be translated into 

    assume(P); s; assert(Q)

As we did not discuss these concepts in class yet, the implementation for these statements is provided.

**Tip** Instead of writing 

    invariant(P && Q && R);

you can write 

    invariant(P);
    invariant(Q);
    invariant(R);

To make sure that your implementation is correct, you also need to make sure that 

    tests/neg/*.js

do *not* pass verification.

**NOTE:** You can **only** write specification annotations of the form 

    invariant(p)

That is, you **cannot** add, remove or modify **any** other lines. 
(Of course, when **debugging** your specifications, you can make 
whatever modifications you like; we just require that the **final** 
versions adhere to the above requirement.) 

## Part C: Add New Test-cases

Your final assignment is to add 3 new positive test-cases to the folder `tests/pos-new`.
The new test-cases should require non-trivial invariants and pass verification.
