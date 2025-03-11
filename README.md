# Rust-code-jubjub
This repository contains Rust implementation of the Jubjub elliptic curve group and its associated fields.

This implementation is based on the implementation of the repository GitHub [zkcrypto jubjub](https://github.com/zkcrypto/jubjub). 

This implementation has the **PMNS** algorithmic implemented to be used on the JubJub curve. It is only used as a test for comparison between the Classical algorithmic and the PMNS algorithmic.

## Prerequisites

Before you begin, ensure you have met the following requirement:

- You have a compilater (Cargo) for the RUST language.

## Build and test

To test the program you can use the Makefile in the main directory.
There are four tests possible:
* Execution time for the Full Scalar Multiplication : 
```
make tests_time
```
* Execution time for the Modular Multiplication :
```
make tests_arithm_time
```
* Clock cycle number for Full Scalar Multiplication :
```
make tests_cycle
```
* Clock cycle number for Modular Multiplication :
```
make tests_arithm_cycle
```
