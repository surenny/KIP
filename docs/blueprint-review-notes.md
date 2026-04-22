# Blueprint Review Notes

> Collected during review of the current blueprint version.

---

## Definition 0.56 (Tensor-Triangulated Category Axioms)

### Item 1: Missing Compatibility Axiom for `smashSuspIso`

**Status:** Pending — need to write

王老师指出：Lean 代码中 `smashSuspIso` 的 compatibility 公理缺失。

Blueprint `prerequisites.tex` item 1 写道：
> $e_{X,Y}: \Sigma X \wedge Y \xrightarrow{\sim} \Sigma(X \wedge Y)$, **compatible with the unit and associativity isomorphisms**.

Lean 代码 `KIP/StableHomotopy/TensorTriangulatedCategory.lean:83-86` 中 `smashSuspIso` 只声明了该同构的存在，但没有写出与 unit / associativity isomorphisms 兼容的公理。

需要补写的两个 compatibility 条件：
1. **(unit)**: $e_{\mathbb{S},X} \circ (\Sigma\lambda_{\mathbb{S}} \wedge \mathrm{id}_X) = \lambda_{\Sigma X}$
2. **(associativity)**: $e_{X \wedge Y, Z} \circ \alpha^{-1}_{\Sigma X,Y,Z} = (e_{X,Y} \wedge \mathrm{id}_Z) \circ \alpha^{-1}_{X,Y,Z}$

**TODO:** 在 Lean 代码的 `ClosedSymmetricTensorTriangulated` class 中为 `smashSuspIso` 补写 compatibility 公理，并在 Blueprint 中补写对应的 remark 或 axiom。
