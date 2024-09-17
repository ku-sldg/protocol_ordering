# Virus checking example analysis

This folder contains examples related to virus checking measurements presented in Paul Rowe's "Confining the Adversary" paper. With these protocols, we seek to use the Chase model finder to discover protocol vulnerabilities in the context of an active adversary. Ultimately, we aim to distinguish protocols that may be more difficult to attack and therefore "better" for the relying party. 

# To run 

1. Download the latest version of the Copland Collection at https://ku-sldg.github.io/copland//blog/2023/12/22/Copland-Collection-Updated.html.
2. Follow directions within the Copland Collection `README.md` for installation instructions.
3. Once installation is complete, navigate into any `protocol_ordering/src/chase_analysis` subdirectory.
4. To run Chase on the Copland phrases written in `filename.cop`, type `make filename_chase.xhtml`. Alternatively, type `./run.sh` to use the premade script to run Chase on all Copland phrases present in the subdirectory.

# Examples from An Ordering over Attestation Protocols

The examples from "An Ordering over Attestation Protocols" can be found in:

`ker-vc-sys`

`rtm-ker-vc-sys`

`ker-hv-vc-sys`

# Target infrastructure 

The target's system and virus checker depend on the kernel. The root of trust has no dependencies. This is written as follows in `filename.gln`:

    % sys and vc depend on kernel
    depends(p4, C, p4, sys) => C = ker.
    depends(p4, C, p4, vc) => C = ker.
    
    % rtm has no dependencies 
    depends(p1, C, p1, rtm) => false.

The root of trust at place `p1` cannot be corrupted. This is written as follows in `filename.gln`:

`l(V) = cor(p1, M) => false.`

We assume the adversary goes undetected at the final measurement event. This is written as follows in `filename.gln`:

`l(V) = msp(p4, M, p4, sys, X) => corrupt_at(p4, sys, V).`

# Copland phrases 

The directories are names according to the measurements present in the Copland phrase.

## vc-sys

This Copland phrase includes one remote call to the virus checker to take a measurement of the system. 

Protocol: `*target: @p4 (vc p4 sys)`

## a1-vc-sys 

These Copland phrases include a1 measuring the virus checker and the virus checker measuring the system. 

Protocol (seq) : `*target: @p3 [a1 p4 vc +<+ @p4 vc p4 sys]`

Protocol (par) : `*target: @p3 [(a1 p4 vc) +~+ @p4 (vc p4 sys)]`

## rtm-a1-vc-sys

These Copland phrases include the root of trust measuring a1, a1 measuring the virus checker, and the virus checker measuring the system.

Protocol (seq) : `*target: @p1 [(rtm p3 a1) +<+ @p3 [(a1 p4 vc) +<+ @p4 (vc p4 sys)]]`

Protocol (par) : `*target: @p1 [(rtm p3 a1) +~+ @p3 [(a1 p4 vc) +~+ @p4 (vc p4 sys)]]`

## rtm-a2-ker-sys

These Copland phrases include the root of trust measuring a2, a2 measuring the kernel, and the virus checker measuring the system.

Protocol (seq): `*target: @p1 [rtm p3 a2 +<+ @p3 [a2 p4 ker +<+ @p4 (vc p4 sys)]]`

Protocol (par): `*target: @p1 [(rtm p3 a2) +~+ @p3 [(a2 p4 ker) +~+ @p4 (vc p4 sys)]]`

## rtm-a1-a2-vc-ker-sys 

This Copland phrase combines the measurement operations in rtm-a1-vc-sys and rtm-a2-ker-sys. 

Protocol: `*target: @p1 ( rtm p3 a1 +~+ rtm p3 a2)  +<+ @p3 ( a1 p4 vc +~+ a2 p4 ker ) +<+ @p4 ((ker p4 vc) +<+ (vc p4 sys1 ))`

## ker-vc-sys

These Copland phrases include the kernel measuring the virus checker and the virus checker measuring the system. This is different from the "Confining" paper where the virus checker was previously measured by a1. Here it is measured by the kernel.  

Protocol (seq): `*target: @p4 [ker p4 vc +<+ @p4 vc p4 sys]`

Protocol (par): `*target: @p4 [(ker p4 vc) +~+ @p4 (vc p4 sys)]`

## rtm-ker-vc-sys

These Copland phrases include the root of trust measuring the kernel, the kernel measuring the virus checker, and the virus checker measuring the system. 

Protocol (seq): `*target: @p1 [(rtm p4 ker) +<+ @p4 [(ker p4 vc) +<+ @p4 (vc p4 sys)]]` 

Protocol (par): `*target: @p1 [(rtm p4 ker) +~+ @p4 [(ker p4 vc) +~+ @p4 (vc p4 sys)]]`

## ker-hv-vc-sys

This Copland phrase includes the kernel measuring the hypervisor, the kernel measuring the virus checker, and the virus checker measuring the system. 

Protocol: `*target: @p4 [(ker p4 hv) +<+ @p4 [(ker p4 vc) +<+ @p4 (vc p4 sys)]]` 


