# TaPL Formalization in Lean 4

🇯🇵 日本語版 → [README.ja.md](README.ja.md)

---

This directory contains formalizations inspired by:

> Benjamin C. Pierce, *Types and Programming Languages* (TaPL)

as part of the broader **TypeSystemsInLean** project.

---

## 🎯 Purpose

- To systematically reconstruct the theoretical development of *TaPL* in Lean 4
- To deepen understanding of programming language theory through mechanization
- To provide a solid foundation for further developments in type systems

---

## 📚 Scope

This directory covers:

- Mathematical preliminaries (relations, orders)
- Untyped arithmetic expressions
- Operational semantics
- Simply Typed Lambda Calculus (STLC)

Each chapter is reconstructed in Lean rather than translated directly.

---

## 🔬 Role in the Project

This directory serves as the **foundation layer** of the repository.

It provides:

- core syntactic definitions
- typing relations
- operational semantics
- basic metatheory

These are reused and extended by other directories such as:

- `Bidirectional/`
- future extensions (Subtyping, System F, etc.)

---

## 🧠 Design Principles

- Reconstruction over transcription
- Clarity of definitions and proofs
- Alignment with mechanized reasoning in Lean 4
- Extensibility toward research-level developments

---

## 🚀 Status

- [ ] Chapter 2–3 (preliminaries)
- [ ] Arithmetic expressions
- [ ] Operational semantics
- [ ] STLC
- [ ] Type soundness (preservation & progress)