# 双方向型付け（Lean 4）

🇺🇸 English → [README.md](README.md)

---

このディレクトリでは、Lean 4 を用いて**双方向型付け（Bidirectional Typing）**を形式化します。

本リポジトリ **TypeSystemsInLean** の発展的な部分にあたります。

---

## 🎯 目的

- 決定的な型検査アルゴリズムの実装
- 以下の性質の検証：
    - soundness（健全性）
    - 一意性（synthesisの決定性）
- 宣言的型システムとアルゴリズム的型付けの橋渡し

---

## 📚 スコープ

現在の対象：

- 型注釈付きSTLC
- 双方向型付け：
    - checking mode（⇐）
    - synthesis mode（⇒）
- モード間の変換（subsumption）

---

## 🔬 他ディレクトリとの関係

- `TaPL/`  
  基本的な型システム・意味論を提供

- `Common/`  
  共通基盤（関係・補題など）

これらの上に構築し、アルゴリズム的型付けへ拡張します。

---

## 🧠 設計方針

- checking / synthesis の分離
- モードの整合性
- 現代的な双方向型付け理論との整合
- 拡張可能な設計

---

## 🚀 今後の拡張

- 部分型
- System F
- 依存型
- 効果システム