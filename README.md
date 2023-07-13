# OCL2MSFOL: A mapping from OCL constraints to Many-sorted First-order Logic

OCL2MSFOL is a _pure_ Java application that generates a Many-Sorted First-Order Logic (MSFOL) theory from an Object Constraint Language (OCL) constraint with an underlying contextual model. The mapping is _strictly_ based on [the work](https://software.imdea.org/~dania/papers/models2016.pdf) of Carolina Dania et. al. at IMDEA Research Institute, Madrid, Spain. The detail of the mapping definition can be reviewed [here](https://software.imdea.org/~dania/tools/definitions.pdf).

OCL works with a four-value logic: _true_, _false_, _null_ and _invalid_. While the first two values are understood universally, 
the last two represent undefinedness: _null_ represents unknown or undefined value whereas _invalid_ represents an error or exception.
Given an OCL constraint (represented as a string) and its contextual model (represented as a JSON file), OCL2MSFOL generates a complete FOL theory in [SMT-LIB2](https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) language as a text file.

## Supported language and features:

There are four modes that can be chosen from: **TRUE**, **FALSE**, **NULL** and **INVALID**.
Each model corresponds to a different theory which can be interpreted differently. 
For example, given an OCL expression e, using the application with mode **TRUE** generates a MSFOL 
theory that defines scenarios in which evaluating e returns _true_.

Please be aware that neither the mapping definition nor the implementation is complete. 
The following items highlight the supported subset of OCL:

  - literal: Boolean, Integer, String.
    - Boolean: `true`, `false`.
    - Integer: ..., `-1`, `0`, `1`, ...
    - String: `"a string"`, ...
  - predefined variables of permitted types.
    - `caller`, `self`, `user`, ...
  - datamodel's attributes and association-ends.
    - `user.age`, `user.accounts`, ... 
  - datamodel classes's `allInstances()`.
    - `class.allInstances()`
  - logical operations: `not`, `and`, `or`, `implies`.
  - comparison operations `=`, `<`, `<=`, `>`, `>=`, `<>`.
  - collection's operations: `isEmpty()`, `notEmpty()`, `isUnique()`, `forAll()`, `exists()`, `collect()`, `select()`.
  - undefinedness opeartions: `oclIsUndefined()`, `oclIsInvalid()`.

## How to use

### Requirements:
- (required) `Maven 3` and `Java 1.8` (or higher).

### Quick guideline:
Users can either clone this repository directly or pull it as package from the Maven Central.
```
<dependency>
  <groupId>io.github.modelsvgu</groupId>
  <artifactId>OCL2MSFOL</artifactId>
  <version>1.0.1</version>
</dependency>
```

### For usage
Have a quick look at the `Runner.java` [class](https://github.com/MoDELSVGU/OCL2MSFOL/blob/Clean/src/main/java/modeling/ocl/fol/config/Runner.java) for a quick guideline.

You can invoke it as a standalone application by the following command:

```bash
java -jar ocl2msfol-1.0.1.jar
  -out <output_theory_url>
  -in <input_datamodel_url>
  -ctx [<var>:<type>]*
  -inv [<ocl_expr>]*
  -ocl <ocl_exp>
```
