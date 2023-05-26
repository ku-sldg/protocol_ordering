# Virus checking analysis

In this folder lives some examples related to virus checking measurements motivated by Paul Rowe's "Confining the Adversary" paper.

# To run 

1. Download most recent (as of 4.12.23) version of copland collection 
2. cd into any folder to run that test case 
3. To run chase analysis on some phrase in `filename.cop` type `make filename_chase.xhtml` to generate xhtml output of the chase analysis

# Measurements 

## sys1 

This measurement is one remote call to the virus checker to take a measurement of the system. 

Protocol: `*target: @p4 (vc p4 sys)`

## vc-sys 

This measurement is two ASP calls. One to measure the virus checker and one to use the virus checker to measure the system. Chase analysis is performed on the measurements in series and in parallel.  

Protocol (seq) : `*target: @p3 [a1 p4 vc +<+ @p4 vc p4 sys]`
Protocol (par) : `*target: @p3 [(a1 p4 vc) +~+ @p4 (vc p4 sys)]`

## a-vc-sys

This measurement is three ASP calls. First, from the root of trust (TPM) take a measurement of a. Then, from a measure the virus checker. Finally, use the virus checker to measure the system. Chase analysis is performed on the measurements in series and in parallel.  





