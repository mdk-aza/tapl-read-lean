# Bidirectional Typing in Lean 4

This directory provides a formalization of **Bidirectional Type Systems** in Lean 4, as part of the broader project:

> **Type Systems in Lean 4**

It builds on foundational material inspired by *Types and Programming Languages (TaPL)* and extends it toward modern type system research.

---

## 🎯 Purpose

- **Mechanization**: Implement a sound and deterministic bidirectional type-checking algorithm in Lean 4.
- **Verification**: Prove key meta-theoretical properties such as:
    - **Soundness** (the algorithm respects typing rules)
    - **Uniqueness** (type synthesis is deterministic)
- **Research**: Explore design principles of bidirectional typing from modern PL literature.
- **Extensibility**: Serve as a foundation for more advanced systems (e.g., Subtyping, System F, Dependent Types).

---

## 📚 Scope

This directory currently formalizes a **Simply Typed Lambda Calculus (STLC)** with type annotations:

- **Checking Mode ($\Leftarrow$)**  
  Handles introduction forms (e.g., unit, lambda abstractions)

- **Synthesis Mode ($\Rightarrow$)**  
  Handles elimination forms (e.g., variables, applications, annotations)

- **Mode Interaction**  
  Includes implicit subsumption from synthesis to checking

---

## 🔬 Research Context

This formalization is informed by:

- **Jana Dunfield and Neel Krishnaswami (2020)**  
  *Bidirectional Typing* (arXiv:1908.05839)

- **Benjamin C. Pierce (2002)**  
  *Types and Programming Languages (TaPL)*

---

### Core Design Principles

- **Mode Correctness**  
  Inputs and outputs are consistent within each judgment

- **Completeness**  
  All typable terms (with annotations) are handled

- **Pfenning Recipe**
    - Introduction → Checking
    - Elimination → Synthesis

---

## 🧠 Technical Highlights (Lean 4)

- **Termination Proof**  
  Using a lexicographic measure: $(sizeOf(e), mode)$

- **Proof as Program (Curry–Howard)**  
  Determinism (uniqueness) is implemented via structural recursion

- **Reuse of Formal Foundations**  
  Builds upon core definitions and lemmas from `Common/` and the TaPL formalization (e.g., syntax, typing relations, and operational semantics)

---

## 🔗 Relation to Other Directories

- `TaPL/`  
  Provides foundational formalizations (relations, STLC, etc.)

- `Common/`  
  Shared utilities (relations, closures, helper lemmas)

- `Bidirectional/` (this directory)  
  Extends STLC toward algorithmic typing

---

## 🚀 Future Work

- [ ] Subtyping ($A <: B$)
- [ ] System F (polymorphism)
- [ ] Dependent types
- [ ] Effect systems

---

## 📄 License

This project is licensed under the MIT License.

---

## ⚠️ AI Training and Usage Restriction

Use of this directory for training machine learning models is **not permitted** without explicit prior consent.

---

## ⚙️ Setup

From the repository root:

```bash
lake update && lake exe cache get
lake build