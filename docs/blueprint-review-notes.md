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

---

## Synthetic Adams Spectral Sequence 叙述修正

### 6. 函子的定义域应为 Syn，后一句需假设 X 有限

**Status:** Pending correction

原文：
> The synthetic Adams spectral sequence is a functor from S to the category of 3-graded converging spectral sequences.

两处修正：
1. **定义域应为 Syn（synthetic spectra），而非 S（stable homotopy category）。**
2. **后一句（关于具体谱序列的性质）需要假设 $X$ 有限（finite spectrum）。**

**TODO:** 在 Blueprint 中将该函子的定义域从 $\mathcal{S}$ 改为 $\mathrm{Syn}$；在后续描述具体谱序列性质时加上 "$X$ finite" 假设。

---

## Axiom 0.108

### 7. 加上 finite spectra 条件

**Status:** Pending correction

Axiom 0.108 需要加上 **finite spectra** 的假设条件。

**TODO:** 在 Blueprint 中 Axiom 0.108 的陈述中补充 finite spectra 假设。

---

## Synthetic Rigidity 一节

### 8. 全节加上 finite spectra 条件

**Status:** Pending correction

Synthetic rigidity 一节的结果均需要加上 **finite spectra** 的条件。

**TODO:** 在 Blueprint 中 synthetic rigidity 一节的所有相关陈述中补充 finite spectra 假设。

---

## Synthetic Lift 补充公理

### 9. 新增 $\lambda g = f$ 公理，并用于证明 0.114、0.115 及 0.106 最后一句

**Status:** Pending — need to write

**公理陈述：**
设 $X, Y$ 为 finite spectra，$f: X \to Y$ 在 homology 上诱导零映射。设
$$W \to X \to Y \to \Sigma W$$
为 functorial distinguished triangle。则有 distinguished triangle
$$\nu(\Sigma^{-1} Y) \to \nu W \to \nu X$$
记其 boundary map 为 $g$。

**Axiom:** $\lambda g = f$。

**用途：** 用此公理证明：
- **Proposition 0.114**
- **Proposition 0.115**
- **Proposition 0.106 的最后一句**

**TODO:** 在 Blueprint 的 synthetic lift 一节中补写此公理；在 0.114、0.115 的证明以及 0.106 最后一句中引用此公理。

---

## 第四章开头段落删除

### 10. 删除 extension spectral sequence 推广段落

**Status:** Pending deletion

第四章开头关于 extension spectral sequence 推广到 $H\mathbb{F}_2$-synthetic spectra 的段落（"The extension spectral sequence introduced in Section ?? can be generalized for $H\mathbb{F}_2$-synthetic spectra. Consider a map $f: X \to Y$ between two bounded below finite $H\mathbb{F}_2$-synthetic spectra filtering..."）应删除。

**原因：** 与我们的逻辑链条不相容。

**TODO:** 在 Blueprint 第四章开头删除该段落。

---

### 11. 删除 "finite $m$ implies $m = \infty$" 段落

**Status:** Pending deletion

第四章中关于 "Many arguments for finite $m$ implies the corresponding statement when $m = \infty$ because of $vX = \lim vX/X_m$..." 以及后续 "We also note that our grading for the triangulation transla..." 的段落应删除。

**原因：** $m = \infty$ 的情形对机器来说单独证更简单，不需要从有限 $m$ 取极限。

**TODO:** 在 Blueprint 第四章中删除该段落。
