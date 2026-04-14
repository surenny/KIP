# 论文作者标注 Blueprint 的操作指南

这份指南是给论文作者用的。

你们**不需要懂 Lean**，也**不需要懂 leanblueprint 的内部实现**。
你们需要做的事情只有一件：

把论文里的 theorem / lemma / corollary / proposition 按照论文本身的证明结构，补上适合生成依赖图的标注。

## 0. 为什么要做这件事

我们引入 `blueprint`，不是为了把论文换一种排版，而是为了把论文里的数学内容变成一个可以管理的形式化项目结构。

对形式化项目来说，真正重要的不是 theorem 的总数，而是尽早弄清楚下面这些问题：

- 哪些结果已经足够稳定，可以直接开始形式化
- 哪些结果依赖哪些前置结论
- 哪些任务彼此独立，可以并行推进
- 哪些地方其实卡在同一个瓶颈上，不应该重复投入

`blueprint` 的作用，就是把论文中的 theorem / lemma / corollary / proposition 组织成一张依赖图。

这张图最重要的价值不是展示，而是调度：

- 它帮助我们尽早发现已经 ready 的形式化对象
- 它帮助我们把大证明拆成若干可以独立处理的小任务
- 它帮助我们判断哪些人可以并行工作，哪些人必须等待上游结果
- 它帮助我们避免所有人都盯着主定理，而忽略大量已经可以先做的中间结果

这里说一个结果 “ready”，通常不是指它已经有 Lean 代码，而是指：

- 它的陈述已经稳定
- 它的标签和位置明确
- 它依赖的前置结果大致清楚
- 它不需要先解决更上游的不确定问题
- 它可以被单独分配给一个形式化工作者

所以，这项标注工作的目标不是立刻 formalize 全文，而是先把论文转换成一种更适合项目管理的结构。

一旦这件事做好，我们就能更清楚地回答这些实际问题：

- 现在有哪些结果已经可以交给不同人分别 formalize？
- 哪些任务可以并行？
- 哪些结果是公共瓶颈，应该优先处理？
- 主定理还缺哪些上游节点？

从这个角度看，`blueprint` 本质上是形式化项目的任务分解和并行调度工具。
它把论文从线性叙述变成依赖网络，从而让形式化工作尽可能并行展开。

## 1. 这项工作到底在做什么

我们希望把论文改造成一个可以生成“结果依赖图”的 blueprint。

这个依赖图回答的问题是：

- 主定理依赖哪些中间结果？
- 某个 lemma 是为了证明哪个 proposition？
- 哪些 corollary 只是前一个 theorem 的直接推论？

这件事和 Lean formalization 有关系，但不是一回事。

你们现在要做的是：

- 先把论文中的数学依赖关系标清楚。

你们现在**不需要**做的是：

- 不需要写 Lean 代码
- 不需要会 `lake`
- 不需要理解 `leanpkg.tex`
- 不需要给每个结果都找 Lean 名字

## 2. 你们应该编辑哪个文件

请只编辑下面这个文件：

- `formal/leanworkspace/blueprint/src/content.tex`

不要改原始论文源码：

- `data/sources/arxiv/2412.10879/tex/main.tex`

原论文会保持不动。
`blueprint/src/content.tex` 是专门拿来做 blueprint 标注的副本。

## 3. 你们只需要学会 4 个东西

### 3.1 `\label{...}`

每个 theorem / lemma / corollary / proposition 都应该有一个稳定的 label。

例如：

```tex
\begin{theorem}\label{thm:main}
  ...
\end{theorem}
```

如果一个结果还没有 label，请补一个。

推荐前缀：

- theorem: `thm:...`
- lemma: `lem:...`
- corollary: `cor:...`
- proposition: `prop:...`

### 3.2 `\uses{...}`

这是最重要的标注。

它表示：

- “这个结果的证明真正用到了哪些前面的结果”

写法：

```tex
\begin{theorem}\label{thm:main}
  \uses{thm:browder,thm:h62}
  ...
\end{theorem}
```

多个依赖用逗号分开。

### 3.3 `\lean{...}`

只有当你**已经知道**某个结果对应哪条 Lean 声明时，才需要加。

例如：

```tex
\lean{FormalMathProject.Spectra.proposition_3_1}
```

如果不知道，就**先不要加**。

### 3.4 `\leanok`

只有当对应的 Lean 定理已经存在并且可以认为“已经 formalize”时才加：

```tex
\leanok
```

如果不确定，就不要加。

## 4. 你们平时到底怎么标

对每个 theorem / lemma / corollary / proposition，按下面顺序处理。

### 第一步：确认它有 `label`

如果没有，就加一个。

### 第二步：补 `\uses{...}`

思考这个问题：

- “如果我要向别人解释这个结果是怎么证明的，我会先叫他去看哪几个前面的结果？”

这些“真正被证明用到的前面的结果”，就是 `\uses{...}` 应该写的内容。

### 第三步：如果你知道 Lean 对应名，再补 `\lean{...}`

不知道就跳过。

## 5. `\uses{...}` 应该怎么判断

这是最容易出错的部分。

请用下面的规则。

### 应该写进 `\uses{...}` 的情况

- proof 里明确引用了某个 theorem / lemma / proposition / corollary
- 这个结果是“由前一个结果立刻推出”的
- 证明虽然没逐字写 “By Theorem X”，但实质上明显依赖 X

### 不应该写进 `\uses{...}` 的情况

- introduction 里提到的背景文献
- “为了读者方便回顾”的综述性提及
- 只是 statement 里提到某个名词，但证明没有用到
- 外部参考文献，除非你们决定把它也当作 blueprint 节点维护

### 一个简单判断法

问自己：

- 如果把这个前置结果删掉，这个 proof 还成立吗？

如果“不成立”，大概率应该写进 `\uses{...}`。

## 6. 最常见的 3 种标法

### 6.1 主定理依赖两个前置结果

```tex
\begin{theorem}\label{thm:main}
  \uses{thm:browder,thm:h62}
  ...
\end{theorem}
```

### 6.2 corollary 是 theorem 的直接推论

```tex
\begin{corollary}\label{cor:my-cor}
  \uses{thm:main}
  ...
\end{corollary}
```

### 6.3 lemma 只依赖一个前面 lemma

```tex
\begin{lemma}\label{lem:step2}
  \uses{lem:step1}
  ...
\end{lemma}
```

## 7. 不要做的事情

### 7.1 不要制造循环依赖

下面这种通常是错的：

- `prop:A` 的 `\uses{prop:B}`
- 同时 `prop:B` 的 `\uses{prop:A}`

依赖图必须是有方向、无环的。

如果两个结果只是“表述相关”，但不是 proof 上谁推出谁，就不要互相 `\uses`。

### 7.2 不要为了“图更丰富”而乱加边

` \uses ` 宁可少一点，也不要加错。

错边比漏边更麻烦，因为它会误导后续 formalization。

### 7.3 不要碰原始论文文件

请只改 blueprint 副本。

## 8. 一个推荐工作流

不要一口气标完整篇。

推荐按 section 分轮做：

1. 先处理本节所有 theorem / lemma / corollary / proposition 的 `label`
2. 再补本节内部最明显的 `\uses`
3. 再补本节与前面章节之间的 `\uses`
4. 编译看依赖图
5. 人工检查有没有明显错边

## 9. 如何编译查看效果

在仓库根目录执行：

```bash
cd formal/leanworkspace/blueprint
bash build.sh
```

成功后会得到：

- PDF: `formal/leanworkspace/blueprint/print/print.pdf`
- Web: `formal/leanworkspace/blueprint/web/index.html`
- 依赖图: `formal/leanworkspace/blueprint/web/dep_graph_document.html`

如果只是想本地打开网页，可以在仓库根目录运行：

```bash
python3 -m http.server 8765 --directory formal/leanworkspace/blueprint/web
```

然后访问：

- `http://127.0.0.1:8765/index.html`
- `http://127.0.0.1:8765/dep_graph_document.html`

## 10. 你们在这一阶段的最低要求

如果时间有限，只做到下面这些也已经很有价值：

- 每个 theorem / lemma / corollary / proposition 都有 `label`
- 主定理相关链条都有 `\uses`
- 每个 corollary 都至少指向它直接依赖的前一个结果
- 不随便写 `\lean{...}`

## 11. 你们在这一阶段可以完全忽略的东西

下面这些可以先不管：

- `lean_decls/`
- `leanpkg.tex`
- Lean 文件里的声明名
- `\leanok`
- 依赖图是否“覆盖全论文”

先把数学上的 proof spine 标清楚，比什么都重要。

## 12. 一个建议的验收标准

当你们完成某一节时，可以自查：

- 这一节的每个 theorem-like 环境都有 label 吗？
- 每个主结果的 proof 能不能从 `\uses` 看出主要前置结果？
- 有没有明显把“背景提及”误写成依赖？
- 有没有循环依赖？

如果这四条都通过，这一节就已经是合格的 blueprint 标注。

## 13. 遇到不确定时怎么办

如果某条边不确定，请遵循下面原则：

- 不确定是否依赖：先不写
- 确定 proof 用到了：再写
- 不确定 Lean 名：不要加 `\lean{...}`
- 不确定是否已 formalize：不要加 `\leanok`

一句话总结：

- 先把“论文自己的证明结构”标清楚，再谈 Lean。
