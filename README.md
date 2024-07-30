# Fun Language Compiler targeting LLVM-IR

## Overview

The compiler I created in Scala can lex and parse Fun-programs (where Fun is its own programming language) and generate corresponding code for the LLVM-IR. The compiler specifically targets the LLVM-IR, a fully typed intermediate representation language used by the LLVM compiler framework.

You can find information about the LLVM-IR mappings at:
 - https://bit.ly/3rheZYr
 - https://llvm.org/docs/LangRef.html

## Components

### Compiler

The compiler for the Fun language utilising both the tokenizer and parser is in `compiler.sc`

### Tokenizer

The tokenizer for the Fun language is implemented in `fun_tokens.sc`.

### Parser

The parser for the Fun language is implemented in `fun_parser.sc`.

## Requirements

To run the compiler and obtain the `.ll` files for the LLVM-IR, you need the following:

- **Ammonite Repl 2.5.9**
- **Scala 3.2.2**

To generate an executable from the `.ll` files, you need the following:

- **Clang 17.0.1**

## Usage

### Running the Compiler

1. **Setup Ammonite REPL:**
   Ensure you have Ammonite REPL 2.5.9 installed. You can download it from [Ammonite](https://ammonite.io).

2. **Setup Clang:**
   Ensure you have Clang 17.0.1 installed. You can download it from [Clang](https://releases.llvm.org/download.html)

3. **Execute the Compiler:**
   Use the Ammonite REPL to run the compiler scripts. In your terminal, navigate to the directory containing the `compiler.sc` file, and with the Ammonite REPL:
   ```bash
   ./amm compiler.sc [Fun program]
   ```
   The Fun program can be either 'fact', 'hanoi', 'mand', 'mand2', or 'sqr'

4. **Creating the `.ll` files:**
   Copy and paste the output for each of the Fun programs into their own respective `.ll` files.

5. **Generate an executable from the `.ll` files:**
   Use clang to run the `.ll` files. In your terminal, navigate to the directory containing the `.ll` files, and with Clang:
   ```bash
   clang [program].ll -o [program].exe
   ```

6. **Run the executable:**
   In your terminal, run the [program].exe file
   ```bash
   [program].exe
   ```
