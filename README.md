# Nazm (نَظْم)

**Nazm** is a new programming language designed to provide flexible and efficient tools for building robust and advanced applications, using **Arabic** syntax.

The name **Nazm** reflects the core goal of the language: Organization and Arrangement.

## Features

- **Strong Syntax**: Designed for readability and organized code structure.
- **Type Safety**: Strong static typing to ensure data is used correctly and consistently.
- **Low-level Control**: Provides low-level access to system resources and hardware.
- **FFI**: Supports Foreign Function Interface (FFI) for calling external functions.

## Project Structure

The project is organized as a Rust workspace with multiple crates, each handling a specific part of the compilation process:

- **`src`**: The main driver and CLI for the compiler.
- **`nazmc_ast`**: Defines the Abstract Syntax Tree (AST) nodes.
- **`nazmc_lexer`**: Handles lexical analysis (tokenizing the source code).
- **`nazmc_parser`**: Parses tokens into the AST.
- **`nazmc_resolve`**: Handles name resolution and scope analysis.
- **`nazmc_semantics`**: Performs semantic analysis and type checking.
- **`nazmc_nir`**: Defines the Nazm Intermediate Representation (NIR).
- **`nazmc_nir_interpreter`**: An interpreter for the NIR (useful for compile-time evaluation).
- **`nazmc_codegen_llvm`**: The backend that generates LLVM IR and compiles it to machine code.
- **`nazmc_codegen_qbe`**: An alternative backend using QBE (currently experimental/inactive).
- **`nazmc_diagnostics`**: Centralized error reporting and diagnostics.
- **`nazmc_data_pool`**: Utilities for efficient data storage (interning strings, etc.).

## Prerequisites

To build and run Nazm, you need:

1.  **Rust**: Install via [rustup](https://rustup.rs/).
2.  **LLVM 17**: The LLVM backend requires LLVM 17.
    - On Linux (Ubuntu/Debian): `sudo apt install llvm-17-dev libpolly-17-dev`
    - On macOS: `brew install llvm@17`

## Getting Started

### 1. Clone the Repository

```bash
git clone https://github.com/sherif-ibn-nasser/nazm-lang.git
cd nazm-lang
```

### 2. Build the Project

```bash
cargo build --release
```
