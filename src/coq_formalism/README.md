# Overview 

This folder contains code related to protocol orderings in the context of an adversary. We prove one protocol is better than another if it is more difficult for an adversary to attack. We assume comparable protocols have the same final measurement events. The analysis is agnostic to the identity and purpose of the measured components.   

To compare protocols, we define four mutually exclusive relationship: 

1. Less than "<"
2. Greater than ">"
3. Equals "="
4. Incomparable 

To reason about comparisons, we divide this research into the following files. 

`attack_graph.v` 
- contains data structure for attack graph 

`graph_normalization.v`
- graph normalization code 

`equiv.v`
- equivalence operator for comparing two graphs (isomorphism)

`graph_strict_partial_order.v` 
- defining and proving strict partial order between two graphs 

`set_order.v`
- proving properties of supports as motivated by Rowe's paper "On Orderings in Security Models"

`example.v`
- examples related to graph analysis

# Building this folder

Before compiling this Coq code, ensure you have an up to date version of Coq. We specifically compiled with version 8.18.0. 

To run code, type `make` inside the `Coq_Formalism` folder. This should make all the dependencies and so you can walk through code in any file.  

# Questions 

This research was conducted by Anna Fritz (a987f052@ku.edu), Sarah Johnson, and Perry Alexander. Please feel free to reach out with questions. 