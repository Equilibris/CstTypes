# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 project implementing System F (polymorphic lambda calculus) with De Bruijn indices. The codebase provides both types and expressions with complete substitution machinery, syntax sugar, and correctness proofs.

## Build Commands

- `lake build` - Build the entire project
- `lake exe cache get` - Get mathlib cache (if available)
- `#check <theorem_name>` - Check a specific theorem in Lean REPL

## Architecture

The project is organized into two main hierarchies under `Types/`:

### Type System (`Types/Ty/`)
- **`Stx.lean`**: Core `Ty` inductive type and syntax sugar
  - `Ty.fn` (function types), `Ty.id` (type variables), `Ty.fa` (universal quantification)
  - Syntax: `[t| 0 → 1]`, `[t| Λ. 0]` for De Bruijn indexed types
- **`RefSet.lean`**: Reference tracking predicate for types
- **`Repl.lean`**: Variable shifting and substitution operations
- **`ReplCorrect.lean`**: Correctness proofs for substitution

### Expression System (`Types/Expr/`)
- **`Stx.lean`**: Core `Expr` inductive type and syntax sugar
  - `Expr.id` (variables), `Expr.app` (application), `Expr.lam` (lambda), `Expr.tapp` (type application), `Expr.tlam` (type lambda)
  - Syntax: `[e| λ : T . e]` (term lambda), `[e| Λ. e]` (type lambda), `[e| f [T]]` (type application)
- **`RefSet.lean`**: Reference tracking predicate for expressions
- **`Repl.lean`**: Variable shifting and substitution operations
- **`ReplCorrect.lean`**: Correctness proofs for substitution

## Key Design Patterns

### De Bruijn Indices
Both types and expressions use De Bruijn indices with extrinsic validity predicates:
- `Ty.Valid : Ty → Nat → Prop` - ensures type variables are within bounds
- `Expr.RefSet : Expr → Nat → Prop` - tracks which variables are referenced

### Syntax Sugar
Custom syntax categories with macro expansion:
- Type syntax: `[t| ...]` expands to `Ty` constructors
- Expression syntax: `[e| ...]` expands to `Expr` constructors
- Both support named variables that get converted to De Bruijn indices

### Substitution Operations
Each namespace provides:
- `bvarShift` / `bvarUnShift` - variable index manipulation
- `replace` - substitution with proper index handling
- `β` - beta reduction (substitution at index 0)
- Correctness theorems proving operations preserve validity

## Module Dependencies

- `Types/Ty/Stx.lean` defines core type syntax
- `Types/Expr/Stx.lean` imports and builds on the type system
- `RefSet` modules define reference tracking
- `Repl` modules implement substitution
- `ReplCorrect` modules prove correctness properties

The architecture supports both intrinsic typing (with dependent types) and extrinsic typing (with validity predicates), though the current implementation uses extrinsic typing for simplicity.