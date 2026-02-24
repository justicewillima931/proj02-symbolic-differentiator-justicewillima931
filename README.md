# Project 2: Symbolic Differentiator

**CSC3301 Programming Language Paradigms**
**Weight:** 5.5% | **Language:** Scheme (Racket)

## Overview

Implement a symbolic differentiation system in Scheme that computes derivatives of mathematical expressions symbolically (not numerically) and simplifies the results.

## Environment Setup

### Installing Racket

#### macOS
```bash
brew install --cask racket
```

#### Ubuntu/Debian
```bash
sudo apt install racket
```

#### Windows
Download the installer from [racket-lang.org](https://download.racket-lang.org/) and follow the installation wizard.

### Verify Installation

```bash
racket --version
```

You should see output like: `Welcome to Racket v8.x.x`

### Running Tests

Run all tests in the `tests/visible/` directory:
```bash
raco test tests/visible/test_differentiator.rkt
```

Or run tests for the entire `src/` directory:
```bash
raco test src/
```

### Interactive Development

Start the Racket REPL:
```bash
racket
```

Or use DrRacket (the integrated IDE) for a graphical environment:
```bash
drracket
```

### Testing Framework

This project uses **rackunit**, a unit testing framework that comes built-in with Racket. No additional installation is needed. Tests are automatically discovered and executed with `raco test`.

## Variant System

This assignment uses a **variant-based system** to generate unique requirements for each student. When your repository is created via GitHub Classroom, a GitHub Action automatically generates:

1. **`.variant_config.json`** - Your unique configuration file containing:
   - Required trigonometric functions (subset of sin, cos, tan, sec, csc, cot)
   - Test expression parameters
   - Polynomial coefficients for testing

2. **`ASSIGNMENT.md`** - Your personalized assignment document with specific requirements

### How It Works

- Your variant is deterministically generated from your GitHub username
- Each student gets 3-4 trigonometric functions to implement
- Test expressions are customized based on your variant
- Hidden tests will verify your specific trigonometric implementations

### Checking Your Variant

After cloning your repository, check your requirements:

```bash
cat .variant_config.json
cat ASSIGNMENT.md
```

## Requirements

### Core Functionality

1. **Differentiate polynomials, sums, products, quotients**
2. **Handle exponentials (e^x) and logarithms**
3. **Differentiate trigonometric functions from your variant**
4. **Apply chain rule for composite functions**
5. **Simplify results**

### Milestones

| Milestone | Description | Weight |
|-----------|-------------|--------|
| M1 | Basic derivatives (constants, variables, sum, product) | 25% |
| M2 | Advanced functions + chain rule | 35% |
| M3 | Simplification | 25% |
| Final | Complete with tests | 15% |

## Expression Representation

```scheme
'(+ x 3)           ; x + 3
'(* 2 x)           ; 2 * x
'(** x 3)          ; x^3
'(sin (* 2 x))     ; sin(2x)
```

## Example

```scheme
(deriv '(** x 3) 'x)  ; Returns '(* 3 (** x 2))
```

## Running Tests

### Run All Tests

```bash
raco test src/
raco test tests/visible/
```

### Run Specific Test File

```bash
racket tests/visible/test_differentiator.rkt
```

**Note:** Testing is local-only. There is no automatic feedback on push — you must run tests yourself before submitting. Hidden tests will run after the deadline to verify your trigonometric implementations.

## Project Structure

```
.
├── .github/
│   └── workflows/
│       └── generate-variant.yml # Generates student variant
├── src/
│   └── differentiator.rkt       # Your implementation
├── tests/
│   └── visible/
│       └── test_differentiator.rkt
├── scripts/
│   ├── variant_generator.py     # Generates variant config
│   └── generate_assignment.py   # Generates ASSIGNMENT.md
├── .variant_config.json         # Your variant (auto-generated)
├── ASSIGNMENT.md                # Your personalized assignment (auto-generated)
├── ASSIGNMENT_TEMPLATE.md       # Template for assignment generation
└── README.md
```

## Submission

1. Complete `src/differentiator.rkt`
2. Ensure all visible tests pass locally
3. Push your code before the deadline
4. Hidden tests will run after the deadline to verify your trigonometric implementations

## Academic Integrity

Each student receives a unique variant with different required functions. Sharing solutions or copying from others will be detected through variant mismatches and code similarity analysis.
