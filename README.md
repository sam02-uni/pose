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

Note that this prototype is underoptimized, and consequently slow and memory-consuming. If execution crashes with a stack overflow error try and crank up the stack memory with the command ulimit -s. Expect in any case execution times to suddenly explode around an execution depth of about 110 steps.
