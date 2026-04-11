# Bidirectional Typing in Lean 4

🇯🇵 日本語版 → [README.ja.md](README.ja.md)

---

This directory contains formalizations of **bidirectional type systems** in Lean 4, developed as part of the **TypeSystemsInLean** project.

---

## 🎯 Purpose

- To implement a deterministic bidirectional type-checking algorithm
- To verify properties such as:
    - soundness
    - uniqueness (determinism of synthesis)
- To bridge declarative type systems and algorithmic typing

---

## 📚 Scope

This directory currently focuses on:

- STLC with type annotations
- Bidirectional typing rules:
    - checking mode (⇐)
    - synthesis mode (⇒)
- Interaction between modes (subsumption)

---

## 🔬 Relation to Other Directories

- `TaPL/`  
  Provides foundational definitions and typing systems

- `Common/`  
  Provides shared infrastructure (relations, closures, utilities)

This directory builds on those components and extends them toward algorithmic typing.

---

## 🧠 Design Principles

- Separation of checking and synthesis
- Mode correctness
- Alignment with modern bidirectional typing literature
- Extensibility toward richer type systems

---

## 🚀 Future Work

- Subtyping
- System F
- Dependent types
- Effect systems