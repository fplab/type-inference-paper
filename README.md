# type-inference-paper

This branch develops support for a topological sort to resolve unify substitutions to their final forms.

If in code file, the Makefile present can be used to do the following:
- make test will run the test.ml file
- make clean will remove any accumulated files from compilation, debugging, or bytecode
- make bytecode will compile a bytecode executable that can be (theoretically) used for the OCaml earlybird vscode debugger
- make debug will run test.ml and initiate an ocamldebug instance (not in the vscode ide but in terminal). 
  - type r and enter to run the program to termination or a breakpoint
  - type b to step backwards once from termination
  - type s to step forwards once
  - type n to step forwards to the next event
  - can set breakpoints or run a specific number of steps, etc with more detailed commands. 
    - See https://ocaml.org/manual/debugger.html or https://ocaml.org/learn/tutorials/debug.html#The-OCaml-debugger
