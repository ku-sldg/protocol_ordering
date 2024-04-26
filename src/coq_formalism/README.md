# Overview 

This folder contains code relating to attestation protocol ordering. We design an ordering scheme such that one protocol is better than another if it is more difficult for an adversary to attack.   

We divide this research into the following files. 

`attack_graph.v` 
- contains data structure for attack trees 

`graph_normalization.v`
- attack tree normalization code 

`graph_equiv.v`
- equivalence relation over individual attack trees

`graph_strict_partial_order.v` 
- strict partial order over individual attack trees

`graph_partial_order.v`
- partial order over individual attack trees

`set_equiv.v`
- equivalence relation over sets of attack trees

`set_order.v`
- partial order over sets of attack trees

`parameterized_*.v`
- ordering relations parameterized over an arbitrary adversary event ordering

`example.v`
- ordering relationships between example Copland protocols

# Building this folder

Before compiling this Coq specification, ensure you have an up-to-date version of Coq. We specifically compiled with version 8.18.0. 

To compile code, run `make` from within the `coq_formalism` folder. You may need to run `coq_makefile -f _CoqProject -o Makefile` first if you are running a different version of Coq.

# Questions 

This research was conducted by Anna Fritz (a987f052@ku.edu), Sarah Johnson (sarahjohnson@ku.edu), and Perry Alexander. Please feel free to reach out with questions. 