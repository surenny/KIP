# Blueprint Review Notes

> Collected during review of the current blueprint version.
> Mathematical issues will be re-checked after the ongoing major refactor is complete.

---

## Definition 0.56 (Tensor-Triangulated Category Axioms)

### 1. Item 2: Tensor-Cofiber Exchange — Blueprint vs Lean Mismatch

**Status:** Pending correction

Definition 0.56 第 2 条（tensor-cofiber exchange）的 Blueprint 描述与 Lean 代码不一致，需根据 Lean 代码修正 Blueprint。

**TODO:** 比对 Lean 代码中的实际定义，将 Blueprint 中 item 2 的陈述修正为与形式化一致的版本。

---

### 2. Item 1: Missing Compatibility Axiom for `smashSuspIso`

**Status:** Pending — need to write

王老师指出：Lean 代码中 `smashSuspIso` 的 compatibility 公理缺失。

Blueprint `prerequisites.tex:582` item 1 写道：
> $e_{X,Y}: \Sigma X \wedge Y \xrightarrow{\sim} \Sigma(X \wedge Y)$, **compatible with the unit and associativity isomorphisms**.

Lean 代码 `KIP/StableHomotopy/TensorTriangulatedCategory.lean:83-86` 中 `smashSuspIso` 只声明了该同构的存在，但没有写出与 unit / associativity isomorphisms 兼容的公理。

**TODO:** 在 Lean 代码的 `ClosedSymmetricTensorTriangulated` class 中为 `smashSuspIso` 补写 compatibility 公理（与 unit isomorphism 和 associativity isomorphism 的交换图），并在 Blueprint 中确认描述一致。

---

### 3. Homotopy Pushout / Pullback: 无法在当前体系下叙述

**Status:** Pending — need to redefine

原文提到"Homotopy pullback squares and homotopy pushout squares in S coincide"，但在目前的体系下无法叙述这件事。

**决定：**
- **Pushout：** 改为单独的定义——定义 pushout 为 $X \to Y \vee Z$ 的 cofiber。
- **Pullback：** 不定义。

**TODO:** 在 Blueprint 中删除原来关于 homotopy pullback/pushout squares coincide 的叙述，替换为 pushout 的新定义（作为 cofiber）。

---

## Axiom 0.71 (HF2-Adams Spectral Sequence)

### 4. 删除 "converging"

**Status:** Pending correction

王老师指出：Axiom 0.71 中描述 Adams spectral sequence 时，"converging bigraded spectral sequences" 中的 **"converging" 一词应删除**，只保留 "bigraded spectral sequences"。

原文片段：
> ...the category of **converging** bigraded spectral sequences...

改为：
> ...the category of bigraded spectral sequences...

**TODO:** 在 Blueprint 中找到 Axiom 0.71 对应位置，删除 "converging" 一词。

---

## §0.3 前最后一个 Axiom（$H_*(X; \mathbb{Q}) = 0$ 条件）

### 5. 将 $H_i(X; \mathbb{Q}) = 0$ for some $i$ 条件移入 item 1，item 2 不加此条件

**Status:** Pending correction

该 axiom 中条件 "$H_i(X; \mathbb{Q}) = 0$ for some $i$" 目前的位置/归属不对。

**决定：**
- 将此条件**塞进 item 1** 中作为假设。
- **Item 2 不要这个条件。**

**TODO:** 在 Blueprint 中调整该 axiom 的 item 1 和 item 2，把 $H_i(X; \mathbb{Q}) = 0$ 条件仅放在 item 1 中。
