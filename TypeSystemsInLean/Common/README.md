# Common Infrastructure (Lean 4)

🇯🇵 日本語版 → [README.ja.md](README.ja.md)

---

This directory contains **shared foundations and reusable components** used across the TypeSystemsInLean project.

It provides general-purpose definitions and lemmas that are independent of any specific language or type system.

---

## 🎯 Purpose

- To centralize reusable definitions and proofs
- To avoid duplication across different formalizations
- To provide a stable foundation for extensions

---

## 📚 Scope

This directory includes:

- **Relations**
    - reflexive, transitive, symmetric
    - determinism
    - equivalence relations

- **Closures**
    - reflexive-transitive closure
    - multi-step reduction

- **Utilities**
    - helper lemmas
    - reusable proof patterns

- **(Optional) Context utilities**
    - generic lookup
    - environment manipulation (if shared)

---

## 🔬 Role in the Project

This directory acts as the **infrastructure layer**.

It is used by:

- `TaPL/` for foundational formalizations
- `Bidirectional/` for algorithmic typing
- future extensions (Subtyping, System F, etc.)

---

## 🧠 Design Principles

### 1. Language-independent
Definitions should not depend on a specific syntax or type system.

### 2. Minimal abstraction
Only abstract when there is clear reuse across multiple components.

### 3. Stability
Avoid frequent changes to ensure downstream modules remain stable.

### 4. Reusability
Each definition should be usable in at least two different contexts.

---

## 🚫 What NOT to include

- Syntax definitions (e.g., `Term`, `Type`)
- Typing relations
- Substitution (usually syntax-dependent)
- Language-specific proofs (e.g., preservation, progress)

---

## 🏗️ Example Structure

    Common/
    ├── Relation.lean
    ├── MultiStep.lean
    ├── Context.lean
    └── Util.lean