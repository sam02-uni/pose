# POSE: Path-optimal symbolic execution prototype

This repository contains the prototype implementation of path-optimal symbolic execution. To compile and run it you need Coq + OCaml + make. Build the Coq files and extract the OCaml implementation by running

    $ make

You can find some examples in the Examples.v file. Process it row by row in your favorite Coq environment (I use Proof General since CoqIDE does not play well with mathematical symbols). To compile the OCaml program just

    $ ocamlopt pose.mli
    $ ocamlopt -o pose pose.ml

Of course you have to add to pose.ml the code that parses your program to analyze, symbolically executes it and prints the results, otherwise pose.ml will silently terminate. In the repo you can find some OCaml example files that exactly do that. For instance, if you want to link the dll.ml example, that runs the doubly linked list example, you need to issue the commands:

    $ ocamlopt pose.mli
    $ ocamlopt -o dll pose.ml dll.ml
    $ ./dll

Note that this prototype is underoptimized, and consequently slow and memory-consuming. If execution crashes with a stack overflow error try and crank up the stack memory with the command ulimit -s. Expect in any case execution times to suddenly explode when converting to string big states: Producing states scales sufficiently well, but stringification does not. I optimized to have decent time with the experiments in this repo, but on other programs your mileage may vary.

Some notes on the small programming language in which you must write the programs you want this prototype to symbolically execute: It comes with some limitations, that you can in some ways overcome.

* All fields must have different names even if they belong to different classes. Do not reuse field names across classes or you will confuse the tool.
* There is no sequential composition: Use let-binding, perhaps by assigning to foo variables.
* There are ifs, but there are no loops (for, while): Use method recursion instead.
* All methods have exactly one parameter. Use a suitable object if you want more (or less) than one parameter.

The grammar of the language is reported in Parse.v, where a LL parser based on parser combinators is reported. Alas, due to the need of keeping the grammar LL there are lots of silly parentheses, and you are not free to add the parentheses where you want. Refer the grammar or the examples (the dll.txt example is quite comprehensive). As a further issue the parser does not recognize all the whitespaces, so you have to put your program in a big string without line breaks, as in dll.ml (the program in dll.txt is formatted for your convenience, but it is not readable by the parser as is). Another limitation of the parser is that it does not do any semantic error checking, especially of typing. If you do a typing error this is usually detected at runtime, and the effect is usually that the state that has the error is killed. When a state has not a successor it is one of two: Either the state is final, or the state has some semantic error and it was killed. So if your symbolic execution has less traces than you think, maybe is because there is some bug in the program you are analyzing.

