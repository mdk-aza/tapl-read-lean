# TaPL Formalization in Lean 4

This repository contains a systematic formalization of concepts from:

> Benjamin C. Pierce, *Types and Programming Languages*, MIT Press.

using the Lean 4 proof assistant.

---

## 🎯 Purpose

The goals of this project are:

* To reconstruct the full theoretical development of *TaPL* in Lean 4
* To deepen understanding of programming language theory through formalization
* To mechanize definitions, semantics, and proofs (e.g., preservation and progress)
* To build a research-oriented foundation in type systems and formal methods

---

## 📚 Scope

This project aims to cover:

* **Chapter 2–3**: Mathematical preliminaries (relations, orders)
* **Chapter 4–7**: Untyped arithmetic expressions and operational semantics
* **Chapter 8–12**: Simply Typed Lambda Calculus (STLC)
* **Later chapters** (planned):

    * Subtyping
    * System F
    * Recursive types
    * Advanced type systems

Each chapter is reconstructed in Lean, not translated.

---

## ⚠️ Copyright & Attribution

* This repository **does NOT reproduce the original text**
* All definitions and proofs are **original implementations**
* The work is **inspired by**:

Benjamin C. Pierce,
*Types and Programming Languages*, MIT Press.

No copyrighted material from the book is included.

---

## 🔬 Research Context

This project is part of a broader research direction including:

* Formal verification of programming languages
* Type soundness proofs (preservation & progress)
* Mechanization of type systems
* Connections to real-world languages such as TypeScript

Future research directions include:

* Formalization of structural typing systems (e.g., MiniTS-Core)
* Subtyping and advanced type relations
* Integration with effect systems and modern FP techniques

---

## 🏗️ Project Structure

```text
tapl-lean/
├── Chapter02/   # Relations, orders
├── Chapter03/   # Additional mathematical structures
├── Chapter04/   # Arithmetic expressions
├── Chapter05/   # Operational semantics
├── Chapter06/
├── Chapter07/
├── Chapter08/   # STLC begins
├── ...
├── Common/      # Shared definitions
└── lakefile.lean
```

---

## 🚀 Status

* [x] Chapter 2 (in progress)
* [ ] Chapter 3
* [ ] Chapter 4–7
* [ ] STLC formalization
* [ ] Type soundness proofs

---

## 🧠 Notes

* This is a **reconstruction project**, not a translation
* Emphasis is placed on:

    * clarity of definitions
    * proof structure
    * extensibility toward research topics

---

## 📄 License

This project is licensed under the MIT License.
See the LICENSE file for details.

---

## 📌 Disclaimer

This repository is an independent educational and research project.
It is not affiliated with or endorsed by the original author or publisher.


## ⚙️ Environment Setup

### Installing Lean

Please follow the official installation guide:

https://aconite-ac.github.io/how_to_install_lean/how-to-install.html

---

### Setup

After installing Lean, run the following command to download dependencies:

```bash
lake update && lake exe cache get
```

---

### Recommended Editor

Using a VSCode-based editor (including Cursor) is highly recommended.

With the Lean 4 extension, you can:

* Check whether proofs are valid in real time
* Inspect goals and context interactively
* Improve productivity when developing formal proofs

Setup instructions can be found here:

https://github.com/leanprover/vscode-lean4/blob/master/vscode-lean4/manual/manual.md

---

### Docker (Optional)

If you prefer using Docker, the following guide may be helpful:

https://zenn.dev/chantakan/articles/9166197c6acaf9

## 🚀 Quick Start

Clone the repository and set up the environment:

```bash
git clone https://github.com/mdk-aza/tapl-read-lean.git
cd tapl-lean
lake update && lake exe cache get
```

---

### Build the project

```bash
lake build
```

---

### Open in VSCode

Open the project folder in VSCode (or Cursor) with the Lean 4 extension installed.

You will be able to:

* See proof states interactively
* Navigate definitions and theorems
* Get real-time feedback on errors

---

### Run Lean files

You can type-check individual files:

```bash
lake env lean Chapter02/YourFile.lean
```

Or simply open files in VSCode and interact with them directly.

---

### Example workflow

1. Open a `.lean` file
2. Write or modify definitions / proofs
3. Check the goal state in the editor
4. Iterate until the proof is complete

---

### Notes

* Make sure Lean and Lake are properly installed
* VSCode + Lean extension is strongly recommended
* Use `lake build` if dependencies are updated

