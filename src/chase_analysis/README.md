# Virus checking analysis

In this folder lives some examples related to virus checking measurements.

# To run 

1. Download most recent (as of 4.12.23) version of copland collection 
2. cd into any folder to run that test case 
3. Add `Makefile` and `thy.gli` to the folder (I wasn't sure if I should share) 
4. Follow directions in Makefile to run chase theory

# Measurements 

## sys 

This measurement is one remote call to the virus checker to take a measurement of the system. 

## vc-sys 

This measurement is two ASP calls. One to measure the virus checker and one to use the virus checker to measure the system. Chase analysis is performed on the measurements in series and in parallel.  

## a-vc-sys

This measurement is three ASP calls. First, from the root of trust (TPM) take a measurement of a. Then, from a measure the virus checker. Finally, use the virus checker to measure the system. Chase analysis is performed on the measurements in series and in parallel.  





