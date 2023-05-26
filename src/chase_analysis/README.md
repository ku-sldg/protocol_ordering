# Virus checking analysis

This folder contains examples related to virus checking measurements presented in Paul Rowe's "Confining the Adversary" paper. With these protocols, we seek to use the CHASE model finder to determine protocol vulnerabilities in the context of an adversary. Ultimately, we aim to distinguish protocols that may be less advantageous to an adversary therefore "better" for a relying party/target. 

# To run 

1. Download most recent (as of 4.12.23) version of copland collection
2. Follow directions written inside copland-collection README.md for installation
3. Once installation is complete, cd into any folder to run that test case 
4. To run chase analysis on the Copland phrases written in `filename.cop` type `make filename_chase.xhtml` to generate xhtml output of the chase analysis

* Alternatively, once all tools are downloaded, cd into any folder and type `./run.sh` to use the premade script to run the analysis on all phrases present in the folder. 

# Measurements 

The files are names according to the measurement targets in the copland phrase. For example, `sys1` takes a measurement of the system. `vc-sys` takes a measurement of the virus checker and the system. 

## sys1 

This measurement is one remote call to the virus checker to take a measurement of the system. 

Protocol: `*target: @p4 (vc p4 sys)`

## vc-sys 

These Copland phrases include a1 measuring the virus checker and the virus checker measuring the system. Chase analysis is performed on the measurements in series and in parallel.  

Protocol (seq) : `*target: @p3 [a1 p4 vc +<+ @p4 vc p4 sys]`

Protocol (par) : `*target: @p3 [(a1 p4 vc) +~+ @p4 (vc p4 sys)]`

## a1-vc-sys

This measurement is three ASP calls including: call root of trust (rtm) to measure a1, use a1 measure the virus checker, and use the virus checker to measure the system. Chase analysis is performed on the measurements in series and in parallel.  

Protocol (seq) : `*target: @p1 [(rtm p3 a1) +<+ @p3 [(a1 p4 vc) +<+ @p4 (vc p4 sys)]]`

Protocol (par) : `*target: @p1 [(rtm p3 a1) +~+ @p3 [(a1 p4 vc) +~+ @p4 (vc p4 sys)]]`

## a2-ker-sys

This protocol includes three measurement operations: it uses the root of trust to measure a2, a2 to measure the kernel, and the virus checker to measure the system. 

Protocol (seq): `*target: @p1 [rtm p3 a2 +<+ @p3 [a2 p4 ker +<+ @p4 (vc p4 sys)]]`

Protocol (par): `*target: @p1 [(rtm p3 a2) +~+ @p3 [(a2 p4 ker) +~+ @p4 (vc p4 sys)]]`

## a1-a2-vc-ker-sys 

This protocol combines the measurement operations in a1-vc-sys and a2-ker-sys. 

Protocol: `*target: @p1 ( rtm p3 a1 +~+ rtm p3 a2)  +<+ @p3 ( a1 p4 vc +~+ a2 p4 ker ) +<+ @p4 ((ker p4 vc) +<+ (vc p4 sys1 ))`

## ker_vc-sys

This protocol calls the kernel to measure the virus checker and the virus checker to measure the system. This is different from the "Confining" paper where the virus checker was previously measured by a1. Here it is measured by the kernel.  

Protocol (seq): `*target: @p4 [ker p4 vc +<+ @p4 vc p4 sys]`

Protocol (par): `*target: @p4 [(ker p4 vc) +~+ @p4 (vc p4 sys)]`

## rtm_ker-sys

This protocol calls the root of trust (rtm) to measure the kernel and the virus checker to measure the system.

Protocol (seq): `*target: @p1 [rtm p4 ker +<+ @p4 vc p4 sys]`

Protocol (par): `*target: @p1 [rtm p4 ker +~+ @p4 vc p4 sys]`

## rtm_ker-vc-sys

The protocol uses the rtm to measure the kernel. The kernel to measurement the virus checker. And the virus checker to measure the system. 

Protocol (seq): `*target: @p1 [(rtm p4 ker) +<+ @p4 [(ker p4 vc) +<+ @p4 (vc p4 sys)]]` 

Protocol (par): `*target: @p1 [(rtm p4 ker) +~+ @p4 [(ker p4 vc) +~+ @p4 (vc p4 sys)]]`

# Specifications 

In all models, we assume the adversary goes undetected at the main measurement event. This is written as follows:

`l(V) = msp(p4, M, p4, sys, X) => corrupt_at(p4, sys, V).`

For dependencies, this analysis assumes the system and virus checker depend on the kernel. We assume the root of trust (rtm) has no dependencies. This appears as follows:

    % Assume sys and vc depend on kernel 
    depends(p4, C, p4, sys) => C = ker.
    depends(p4, C, p4, vc) => C = ker.
    % rtm has no dependencies 
    depends(p1, C, p1, rtm) => false.

If we want to assume recently measured components cannot be corrupted, we would write the following line. We do not make this assumption.  

`prec(V, V1) & l(V1) = cor(P,C) & ms_evt(V) => false.`

We assume the root of trust, at place `p1` cannot be corrupted. This would be a deep corruption. We prevent this by writing the following line. 

`l(V) = cor(p1, M) => false.`