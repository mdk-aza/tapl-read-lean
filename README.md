# Type Systems in Lean 4

![Lean](https://img.shields.io/badge/Lean-4-blue) 
![Status](https://img.shields.io/badge/status-in_progress-yellow)

🇯🇵 Japanese Versionn → [README.ja.md](README.ja.md)

This repository is a research-oriented Lean 4 project for formalizing **type systems**, **operational semantics**, and related foundations in programming language theory.

It begins with systematic reconstructions inspired by:

> Benjamin C. Pierce, *Types and Programming Languages* (TaPL), MIT Press

and extends toward more advanced developments such as bidirectional typing, subtyping, and polymorphism.

---

## 🎯 Purpose

The goals of this project are:

- **Formalization**  
  To mechanize core concepts from programming language theory in Lean 4

- **Understanding through reconstruction**  
  To deepen understanding of type systems and semantics by rebuilding them from first principles

- **Verification**  
  To prove key meta-theoretical properties such as:
    - preservation
    - progress
    - determinism
    - soundness

- **Research foundation**  
  To build a reusable and extensible basis for research in type systems, formal methods, and mechanized metatheory

---

## 📚 Scope

This repository is organized as a collection of related formalization projects.

### Current and planned areas include:

- **Mathematical preliminaries**
    - relations
    - orders
    - closures
    - inductive definitions

- **Core language formalizations**
    - untyped arithmetic expressions
    - operational semantics
    - Simply Typed Lambda Calculus (STLC)

- **Advanced type system developments**
    - bidirectional typing
    - subtyping
    - System F
    - dependent types
    - effect systems

This project is a **reconstruction**, not a translation, of textbook and research ideas into Lean 4.

---

## 🏗️ Project Structure

    TypeSystemsInLean/
    ├── Common/          # Shared foundations and reusable definitions
    ├── TaPL/            # Formalizations inspired by Types and Programming Languages
    ├── Bidirectional/   # Bidirectional typing developments
    ├── Subtyping/       # Planned extensions
    ├── SystemF/         # Planned extensions
    └── lakefile.lean

### Directory Roles

- **Common/**  
  Shared infrastructure used across multiple developments, such as:
    - relations
    - multi-step closures
    - generic helper lemmas
    - reusable context utilities

- **TaPL/**  
  Formalizations inspired by *Types and Programming Languages*, including foundational chapters and core calculi

- **Bidirectional/**  
  Formalizations of bidirectional type systems built on top of the core foundations

- **Future directories**  
  Extensions toward richer type systems and research topics

---

## 🔬 Research Context

This repository is part of a broader effort to study and mechanize:

- programming language metatheory
- type soundness proofs
- algorithmic typing
- formal verification of language designs
- connections between theory and practical type systems

In particular, the project is motivated by an interest in:

- type systems
- formal methods
- mechanized proofs in Lean 4
- research directions connecting textbook foundations to modern PL work

---

## 🧠 Design Principles

### 1. Reconstruction over transcription
The goal is not to copy textbook presentations directly, but to reconstruct them in a form suitable for mechanized reasoning in Lean 4.

### 2. Layered formalization
The repository is structured so that foundational material can be reused across multiple developments.

### 3. Extensibility
Definitions and proofs are organized to support later extensions, rather than only isolated one-off formalizations.

### 4. Research orientation
This repository is intended not only as a learning project, but also as a foundation for future research work.

---

## 🚀 Status

- [ ] Mathematical preliminaries
- [ ] Untyped arithmetic expressions
- [ ] Operational semantics
- [ ] STLC formalization
- [ ] Preservation and progress proofs
- [ ] Bidirectional typing
- [ ] Subtyping
- [ ] System F

---

## ⚠️ Copyright & Attribution

This repository does **not** reproduce the original text of *Types and Programming Languages*.

All definitions, proofs, and formal developments are original implementations in Lean 4, inspired by textbook and research literature.

Primary inspiration includes:

- Benjamin C. Pierce, *Types and Programming Languages*
- Research literature on bidirectional typing and mechanized metatheory

---

## 📄 License

This project is licensed under the MIT License.  
See the LICENSE file for details.

---

## ⚠️ AI Training and Usage Restriction

The contents of this repository are provided for educational and research purposes.

Use of this repository for training machine learning models (including LLMs) is not permitted without explicit prior written consent.

---

## ⚙️ Environment Setup

### Setup

    lake update && lake exe cache get

### Build

    lake build

### Recommended Editor

A VS Code–based editor (VS Code or Cursor) is recommended.

With the Lean 4 extension, you can:

- check proofs interactively
- inspect goals and contexts
- navigate definitions and theorems
- get real-time feedback while developing proofs