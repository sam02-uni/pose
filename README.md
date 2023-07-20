# POSE: Path-optimal symbolic execution prototype

This repository contains the prototype implementation of path-optimal symbolic execution. To compile and run it you need Coq, OCaml (that usually comes with Coq), make and Z3. Build the Coq files and extract the OCaml implementation by running

    $ make

You can find some examples in the Examples.v file. Process it row by row in your favorite Coq environment (I use Proof General since CoqIDE does not play well with mathematical symbols). To compile the OCaml program just issue the commands:

    $ ocamlopt pose.mli
    $ ocamlopt -o run pose.ml run.ml

You will find a run executable, with a sketchy help that you can read by issuing the command

    $ ./run -h


A possible execution is:

    $ ./run -p -z3 /usr/bin/z3 dll.txt 100

It will run the dll.txt example up to depth 100, by pruning the infeasible states using Z3 (option -p), where the Z3 executable is installed at /usr/bin.

Note that this prototype is underoptimized, and consequently slow and memory-consuming. If execution crashes with a stack overflow error try and crank up the stack memory with the command ulimit -s. Expect in any case execution times to suddenly explode when states start to become big, which usually happen at high depts. I optimized to have decent time with the experiments in this repo, but on other programs your mileage may vary.

Some notes on the small programming language in which you must write the programs you want this prototype to symbolically execute: It comes with some limitations, that you can in some ways overcome.

* All fields must have different names even if they belong to different classes. Do not reuse field names across classes or you will confuse the tool.
* There is no sequential composition: Use let-binding, perhaps by assigning to foo variables.
* There are ifs, but there are no loops (for, while): Use method recursion instead.
* All methods have exactly one parameter. Use a suitable object if you want more (or less) than one parameter.

The grammar of the language is reported in Parse.v, that implements a LL parser based on parser combinators. Alas, due to the need of keeping the grammar LL there are lots of silly parentheses, and you are not free to add the parentheses where you want. Refer the grammar or the examples (the treemap.txt example is quite comprehensive). Another limitation of the parser is that it does not do any semantic error checking, especially typing (the language itself is terribly dynamic). If you do a typing error this is detected at runtime, and the typical effect is that the state that has the error is killed. When a state has not a successor it is one of two: Either the state is final, or the state was killed because of some semantic error. So if your symbolic execution has less traces than you think, maybe is because there is some bug in the program you are analyzing. My advice is: Run your algorithm with some concrete inputs (i.e., tests) and see if the end state is exactly one, and the one you expect. When you are pretty sure that your program is correct execute it symbolically.

For what concerns the examples the maximum depths are:

* dll: 143
* treemap: 336

