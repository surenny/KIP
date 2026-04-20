# Blueprint-Native Workflow — 设计草稿

## 0. 设计动机

原版 Archon 的工作流是：`init → autoformalize → prover → polish`，以 **文件** 为调度单位。在 blueprint-driven 的论文形式化项目中暴露出三个不足：

1. **粒度不匹配**：Archon 以 `.lean` 文件为单位分配任务，但 blueprint 的最小单位是 **节点**（一条数学声明）。一个文件里可能有 20 个节点处于不同的生命周期阶段。
2. **缺少人机交互门控**：Archon 的流程是全自动循环，没有"人类审核自然语言"和"人类确认 NL↔Lean 对齐"两个关键卡点。
3. **没有利用依赖图**：Archon 按文件并行，不知道节点之间的依赖关系。blueprint 的依赖图天然告诉我们哪些节点已经 ready，哪些被上游阻塞。

> **核心思想：以 blueprint 节点为逻辑调度单位，以 Lean 文件为物理执行单位，以 `status.yaml` + `dep_graph.json` 为状态源，以依赖图拓扑序决定优先级，在 AI 自动化步骤之间插入人类门控。**

---

## 1. 工作流全景

```
Paper (LaTeX) ──→ [Extract AI] ──→ 节点 + 依赖图 (Draft)
                                        │
                                        ▼
                               [Human Gate: NL Review]
                                Draft → Reviewed
                                        │
                                        ▼
                               [Formalize AI]
                                Reviewed → Bound (所有证明留 sorry)
                                        │
                                        ▼
                               [Human Gate: Alignment]
                                Bound → Aligned
                                        │
                                        ▼
                               [Prove AI]
                                Aligned → Proved (填充 sorry)
                                        │
                                        ▼
                               [Polish AI] (optional)
```

---

## 2. Agent 与门控

系统由 **4 个 AI Agent + 1 个编排器 + 2 个人类门控** 组成。人类不是 agent——人类是流水线上的质检站。

```
AI Agents (4):              Human Gates (2):          Infrastructure (1):
  Extract                     NL Review                 Orchestrator
  Formalize                   Alignment
  Prove
  Polish
  + Plan (规划子模块)
  + Review (审阅子模块)
```

---

## 3. 核心设计问题：节点 vs 文件的阻抗失配

### 3.1 矛盾的本质

blueprint 中的最小逻辑单元是 **节点**（一条数学声明），但 Lean 项目中 agent 操作的最小物理单元是 **文件**。这产生三个层面的张力：

| 层面 | 节点视角 | 文件视角 | 张力 |
|------|---------|---------|------|
| **调度** | "节点 A 已 aligned，可以 prove" | "Adams.lean 里有 3 个 sorry，有的 aligned 有的没有" | 一个文件里的节点状态不一致 |
| **定位** | "节点 prereq:thm:adams-weak-convergence" | "Adams.lean 第 156 行" | 行号是脆弱的——编辑文件后就变了 |
| **分配** | "这批 ready 节点分散在 5 个文件里" | "一个 agent 一个文件" | 有的文件只有 1 个 ready 节点，启动一个 agent 浪费；有的文件有 10 个 |

### 3.2 行号定位为什么不可行

当前 Archon 用 `line 156` 定位 sorry。问题：

```
# 初始状态：sorry 在第 156 行
theorem weakConvergence : ... := by
  sorry  -- line 156

# Agent A 在第 100 行添加了一个辅助 lemma（+15 行）
# 现在 sorry 在第 171 行了，但 PROGRESS.md 还写着 "line 156"
```

在 blueprint-native 工作流中更严重——Formalize Agent 一次性往文件里加几十个声明，所有行号都会大面积偏移。

### 3.3 正确的定位方式：用声明的全限定名

Lean 的声明有全局唯一的全限定名（Fully Qualified Name, FQN），例如 `KIP.StableHomotopy.Adams.weakConvergence`。这个名字：

- **不随文件内编辑变化**（只要声明本身不被重命名）
- **可以被 grep 精确定位到文件和行号**
- **已经存在于 `\lean{...}` 绑定中**
- **是 Lean LSP 工具的原生查询 key**

所以：**节点的 Lean 标识应该是声明 FQN，不是文件+行号。**

### 3.4 提出的解决方案：三层模型

```
┌─────────────────────────────────────────────────────────┐
│  Layer 1: 逻辑层 (Logical)                               │
│  单位: 节点 (node)                                        │
│  标识: LaTeX label (prereq:thm:adams-weak-convergence)   │
│  状态: status.yaml                                       │
│  关系: dep_graph.json (依赖图)                            │
│  职责: 调度决策 — 哪些节点 ready，什么优先级              │
└──────────────────────────┬──────────────────────────────┘
                           │
                    节点 → 声明 映射
                    (lean_decl in status.yaml)
                           │
┌──────────────────────────▼──────────────────────────────┐
│  Layer 2: 符号层 (Symbolic)                              │
│  单位: Lean 声明 (declaration)                           │
│  标识: FQN (KIP.StableHomotopy.Adams.weakConvergence)    │
│  定位: 用 FQN grep 或 LSP 查找物理位置                    │
│  职责: 精确定位 — 在代码中找到"这个声明在哪"             │
└──────────────────────────┬──────────────────────────────┘
                           │
                    声明 → 文件 映射
                    (grep / LSP / lean_decls)
                           │
┌──────────────────────────▼──────────────────────────────┐
│  Layer 3: 物理层 (Physical)                              │
│  单位: .lean 文件                                        │
│  标识: 相对路径 (KIP/StableHomotopy/Adams.lean)          │
│  执行: 一个 prover agent 拥有一个文件                     │
│  职责: 实际编辑 — agent 在这个文件里工作                  │
└─────────────────────────────────────────────────────────┘
```

**核心原则：**
- **调度按节点**（编排器在逻辑层工作）
- **定位按声明名**（不用行号，用 FQN）
- **执行按文件**（agent 仍然"拥有一个文件"，与 Archon 兼容）
- 编排器负责从节点聚合到文件，生成 **文件级任务清单**（file manifest）

### 3.5 File Manifest：桥接节点和文件的关键数据结构

编排器的输出不是"一堆节点 ID"，而是 **按文件分组的任务清单**：

```yaml
# .archon/manifests/KIP_StableHomotopy_Adams.lean.yaml
# 这个文件是编排器生成的，给 agent 的指令

file: KIP/StableHomotopy/Adams.lean
tasks:
  - node_id: prereq:thm:adams-weak-convergence
    action: prove            # formalize | prove
    lean_decl: KIP.StableHomotopy.Adams.weakConvergence
    kind: theorem
    nl_text: |
      The Adams spectral sequence for bounded below spectra
      of finite type weakly converges.
    informal_proof: |
      By the standard convergence theorem...
    dependencies_proved:
      - KIP.StableHomotopy.IsBoundedBelow    # 已 proved/aligned
      - KIP.StableHomotopy.FiniteType        # 已 proved/aligned
    prior_attempts:
      - approach: "Direct application of converges lemma"
        result: FAILED
        dead_end: true

  - node_id: prereq:thm:adams-separated
    action: prove
    lean_decl: KIP.StableHomotopy.Adams.separated
    kind: theorem
    nl_text: |
      The Adams spectral sequence for bounded below spectra
      of finite type is separated.
    informal_proof: |
      Follows from the filtration degree bound...
    dependencies_proved:
      - KIP.StableHomotopy.Adams.weakConvergence  # 同文件，注意依赖顺序！
```

**Agent 看到的是这个 manifest，不是裸的 PROGRESS.md 自由文本。** Agent 的流程变成：

1. 读 manifest → 知道"我的文件里有哪些节点需要工作"
2. 用 FQN grep 定位每个声明的实际位置 → 不依赖行号
3. 按 manifest 中的依赖顺序处理（同一文件内也有先后）
4. 每完成一个节点，写 task_results，编排器更新 status.yaml

### 3.6 为什么保留文件级 agent（不做纯节点级 agent）

考虑过但否决的方案：为每个节点启动一个独立 agent。问题：

1. **agent 启动开销**：每个 `claude -p` 调用有几十秒的冷启动 + 上下文加载时间。一个文件里 10 个节点就是 10 次冷启动。
2. **上下文割裂**：同一文件中的声明往往共享 `import`、`namespace`、辅助 lemma。拆成独立 agent 后每个 agent 都要重新理解文件上下文。
3. **编辑冲突**：两个 agent 同时编辑同一文件 = 灾难。Archon 的"一个 agent 一个文件"的隔离模型是对的。
4. **自然分组**：Lean 项目的文件组织本身反映了数学结构。`Adams.lean` 里的声明之间天然关联紧密。

所以：**保持 Archon 的文件级 agent 隔离，但给 agent 一个节点级的任务清单（manifest）。**

### 3.7 节点分散到不同文件时怎么办

一批 ready 节点分散在 5 个文件里，每个文件 1-3 个节点：

| 方案 | 做法 | 优劣 |
|------|------|------|
| **A: 每个文件一个 agent** | 5 个并行 agent，各自的 manifest 只含 1-3 个节点 | 简单但浪费——agent 大部分时间在读文件上下文 |
| **B: 合并到少数 agent** | 相关文件分成 2 组，每组 agent 处理 2-3 个文件 | 省资源但破坏"一 agent 一文件"隔离 |
| **C: 批量等待后再派发** | 等积累够多 ready 节点后再批量派发，每文件至少 N 个节点 | 减少浪费但增加延迟 |
| **D: 混合策略** | 如果文件只有 1 个 ready 节点 → 暂缓，如果有 ≥3 个 → 立即派发 | 平衡浪费和延迟 |

**建议：方案 D（混合策略）**，阈值可调。编排器内部设一个 `min_tasks_per_agent` 参数（默认 2），只有当某个文件的 ready 节点数 ≥ 这个阈值时才派发 agent。低于阈值的文件积累到下一批次，除非该节点是关键路径上的瓶颈（blocking 很多下游节点）。

---

## 4. 改进的 `status.yaml` 组织形式

### 4.1 当前 schema 的问题

```yaml
# 当前：平面结构，节点属性为主，缺少定位信息
nodes:
  prereq:thm:adams-weak-convergence:
    lean_decl: KIP.StableHomotopy.Adams.weakConvergence  # 只有声明名
    nl_reviewed: true
    bound: true
    aligned: true
    proved: false
    kind: theorem
    nl_hash: a1b2c3d4
```

问题：
- `lean_decl` 是字符串，不知道在哪个文件——agent 要 grep 整个项目
- 没有 `lean_file`——缺少物理定位
- 没有 `assigned_to`——不知道哪个 agent 在处理
- `lean_decl` 是单值，但一个节点可能对应多个声明

### 4.2 提议的 schema

```yaml
nodes:
  prereq:thm:adams-weak-convergence:
    # --- 逻辑层（来自 LaTeX） ---
    kind: theorem
    chapter: prerequisites
    nl_hash: a1b2c3d4e5f6g7h8

    # --- 符号层（来自 \lean{...} 绑定） ---
    lean_decls:                                    # 改为 list
      - KIP.StableHomotopy.Adams.weakConvergence
    lean_file: KIP/StableHomotopy/Adams.lean       # 新增：物理文件位置（构建时自动填充）

    # --- 生命周期状态 ---
    nl_reviewed: true
    nl_reviewer: surenny
    nl_reviewed_at: '2026-04-19'
    bound: true
    aligned: true
    align_reviewer: web-reviewer
    aligned_at: '2026-04-19'
    proved: false
    proved_at: null
    proved_by: null          # 新增：由哪个 session 证明的

    # --- 任务追踪（编排器管理） ---
    assigned_to: null        # 新增：当前分配给哪个 agent session
    assigned_at: null
    attempt_count: 0         # 新增：总尝试次数
    last_attempt_result: null  # 新增：RESOLVED / FAILED / IN_PROGRESS

    # --- 审核记录 ---
    comments:
      - topic: align
        text: SSData字段顺序和NL不一致
        by: surenny
        at: '2026-04-19'
```

### 4.3 `lean_file` 字段的自动填充

在 `make_lean_data()` 中，`_extract_lean_source()` 已经在搜索 `.lean` 文件。只需在找到匹配时记录文件路径：

```python
def _extract_lean_source(lean_root, decl_name, max_lines=40):
    short_name = decl_name.rsplit('.', 1)[-1]
    for lean_file in sorted(lean_root.rglob('*.lean')):
        # ... 匹配逻辑 ...
        if match:
            rel_path = lean_file.relative_to(lean_root)
            return '\n'.join(block), str(rel_path)  # 返回 (source, file_path)
    return '', ''
```

然后在 `make_lean_data()` 中：
```python
src, file_path = _extract_lean_source(lean_root, decl)
if file_path:
    st['lean_file'] = file_path
```

这样每次 `leanblueprint web` 后，`status.yaml` 中每个 bound 节点都自动有物理文件定位。

### 4.4 编排器使用 `lean_file` 做文件级分组

```python
def group_by_file(ready_nodes, status):
    """将 ready 节点按 lean_file 分组，生成文件级 manifest"""
    groups = defaultdict(list)
    for node_id in ready_nodes:
        st = status[node_id]
        lean_file = st.get('lean_file')
        if lean_file:
            groups[lean_file].append(node_id)
        else:
            # 未 bound 的节点（formalize 阶段），按 chapter 估算目标文件
            groups[estimate_target_file(st)].append(node_id)
    return groups
```

---

## 5. `status.yaml` 的产生机制与局限性

### 5.1 产生机制

`status.yaml` 由 `leanblueprint web`（plasTeX 构建）的后解析回调 `make_lean_data()` 自动生成和更新：

```
LaTeX (.tex) ─── plasTeX 解析 ──→ make_lean_data() ──→ status.yaml
                                        ↑
Lean (.lean) ───── _extract_lean_source() 搜索声明 ──┘
```

**每次 `leanblueprint web` 时：**
1. 加载已有 `status.yaml`
2. 遍历依赖图每个节点：
   - `st['bound'] = bool(leandecls)` — 有 `\lean{...}` 就为 true
   - `st['kind'] = item_kind(node)` — 从 LaTeX 环境类型推导
   - NL 哈希变更检测 → 自动重置 `nl_reviewed`, `aligned`
   - `bound → nl_reviewed` 单调提升
   - `proved` 来自 `\leanok` 标记
3. 写回 status.yaml

**关键事实：status.yaml 是构建副产品，不是主动管理的数据库。**

### 5.2 绑定机制

绑定是 LaTeX 侧声明式的：`\lean{KIP.SpectralSequence.SSData}\leanok`

Lean 源码搜索（`_extract_lean_source`）用正则短名匹配，不是符号表查询。局限：
- 同名声明取第一个匹配
- 搜索时间与 .lean 文件数线性
- 不处理 namespace 上下文

### 5.3 七个关键局限

1. **不含依赖图** — `status.yaml` 只存节点属性，不存 `\uses` 关系。需要额外导出 `dep_graph.json`。
2. **节点 ID 脆弱** — 基于 `\label{}`，label 重命名 = 审核历史归零。
3. **无物理定位** — 缺少 `lean_file` 字段，agent 不知道声明在哪个文件。
4. **无图感知查询** — 无法直接问"哪些节点 ready"。
5. **并发写入不安全** — 整体覆写，无文件锁。
6. **`proved` 靠手动标记** — 应由 Lean 编译器判定（无 sorry + 编译通过）。
7. **无任务分配追踪** — 缺 `assigned_to` 字段。

---

## 6. 状态查询 API 层

### 6.1 `blueprint-status.py` — 编排器的查询引擎

```
数据源：
  status.yaml     + dep_graph.json
  (节点属性)         (依赖关系)
```

#### 命令列表

```bash
# 全局汇总
blueprint-status.py summary

# 列出就绪节点，按文件分组
blueprint-status.py ready --stage formalize
blueprint-status.py ready --stage prove --group-by-file --json

# 列出阻塞节点及原因
blueprint-status.py blocked

# 单节点详情 + 上下游依赖
blueprint-status.py node prereq:thm:adams-weak-convergence

# 从目标节点到根的关键路径
blueprint-status.py path proof:thm:main-theorem

# 两次快照的差异
blueprint-status.py diff status.yaml.bak status.yaml

# 标记节点被分配（编排器用）
blueprint-status.py assign prereq:thm:adams-weak-convergence --agent session-42

# 生成文件级 manifest（给 agent 用）
blueprint-status.py manifest --stage prove --output .archon/manifests/
```

#### `manifest` 命令详解

这是编排器到 agent 的接口：

```bash
$ blueprint-status.py manifest --stage prove --output .archon/manifests/

Generated manifests:
  .archon/manifests/KIP_StableHomotopy_Adams.lean.yaml  (2 tasks)
  .archon/manifests/KIP_SyntheticSpectra_Basic.lean.yaml  (4 tasks)
  Skipped: KIP_SpectralSequence_Convergence.lean (1 task < threshold 2, not on critical path)
```

每个 manifest 是前面 3.5 节描述的格式——agent 直接读取它工作，不需要自己解析 status.yaml + 依赖图。

### 6.2 核心查询引擎（Python 库）

```python
class BlueprintQuery:
    """纯逻辑查询，无 I/O"""
    def __init__(self, status: dict, dep_graph: dict):
        self.status = status['nodes']
        self.graph = dep_graph
        self._build_adjacency()

    def ready(self, stage: str) -> list[str]:
        """返回可以进入指定阶段的节点 ID 列表"""

    def blocked(self) -> list[dict]:
        """返回被阻塞的节点及其阻塞原因"""

    def critical_path(self, target: str) -> list[dict]:
        """从目标节点回溯，找到最长未完成链"""

    def group_by_file(self, node_ids: list[str]) -> dict[str, list[str]]:
        """按 lean_file 分组"""

    def generate_manifest(self, file: str, node_ids: list[str]) -> dict:
        """为一个文件生成 agent manifest"""

    def summary(self) -> dict:
        """全局统计"""

    def diff(self, old_status: dict) -> list[dict]:
        """两次状态的差异"""
```

### 6.3 `dep_graph.json` 导出

在 `leanblueprint web` 时自动导出：

```json
{
  "generated_at": "2026-04-20T15:30:00Z",
  "nodes": {
    "prereq:def:ss-data": { "kind": "definition", "chapter": "Prerequisites" },
    "prereq:thm:adams-weak-convergence": { "kind": "theorem", "chapter": "Prerequisites" }
  },
  "edges": [
    { "from": "prereq:def:bounded-below", "to": "prereq:thm:adams-weak-convergence", "type": "uses" }
  ]
}
```

---

## 7. 完整的调度算法

### 7.1 编排器的一次迭代

```python
def orchestrate_iteration():
    # 1. 加载数据
    status = load_yaml('blueprint/status.yaml')
    graph = load_json('blueprint/dep_graph.json')
    query = BlueprintQuery(status, graph)

    # 2. 计算 ready 节点
    ready_formalize = query.ready('formalize')  # reviewed + deps bound
    ready_prove = query.ready('prove')          # aligned + theorem + deps proved

    # 3. 按文件分组
    formalize_by_file = query.group_by_file(ready_formalize)
    prove_by_file = query.group_by_file(ready_prove)

    # 4. 过滤：至少 N 个任务才派发（除非在关键路径上）
    critical = set(query.critical_path('proof:thm:main-theorem'))
    min_tasks = config.get('min_tasks_per_agent', 2)

    for file, nodes in list(prove_by_file.items()):
        if len(nodes) < min_tasks and not any(n in critical for n in nodes):
            del prove_by_file[file]  # 暂缓，积累到下一批

    # 5. 生成 manifest 文件
    for file, nodes in prove_by_file.items():
        manifest = query.generate_manifest(file, nodes)
        save_yaml(f'.archon/manifests/{slugify(file)}.yaml', manifest)

    # 6. 运行 Plan Agent（准备 informal content）
    run_plan_agent(formalize_by_file, prove_by_file)

    # 7. 并行派发 agent
    for file in prove_by_file:
        launch_agent('prove', file, manifest=f'.archon/manifests/{slugify(file)}.yaml')

    # 8. 等待完成 → Review → 更新 status.yaml
    wait_all_agents()
    run_review()
    run_leanblueprint_web()  # 更新 status.yaml 中的 bound/proved 等自动字段
```

### 7.2 Agent 的工作流程（带 manifest）

```
Agent 启动
    │
    ▼
读取 manifest YAML
    │ 获得：文件路径、节点列表、每个节点的 FQN + NL + informal proof + 依赖
    │
    ▼
用 FQN grep 定位每个声明的实际位置
    │ 例如：grep -n "theorem weakConvergence" KIP/StableHomotopy/Adams.lean
    │ 结果：第 171 行（不是 manifest 里的静态行号！）
    │
    ▼
按 manifest 中的依赖顺序处理节点
    │ 如果 A 依赖 B 且两个都在同一文件，先做 B
    │
    ▼
每完成一个节点的 sorry 填充：
    │ - 编译验证 (lake env lean <file>)
    │ - 写 task_results/<file>.md（按节点分段，标注 node_id）
    │
    ▼
Agent 结束
```

---

## 8. 数据流详图

```
                    ┌─────────────────────────────────┐
                    │  status.yaml + dep_graph.json   │
                    │  (Single Source of Truth)         │
                    └──────┬──────────────┬────────────┘
                           │              │
              ┌────────────▼──┐    ┌──────▼────────────┐
              │ Orchestrator  │    │ GitHub Pages UI    │
              │               │    │ (human review)     │
              │ blueprint-    │    │                    │
              │ status.py     │    │ Writes:            │
              │ query engine  │    │  nl_reviewed       │
              │               │    │  aligned           │
              │ Generates:    │    │  comments          │
              │  manifests/   │    └────────────────────┘
              └──┬─────┬──┬──┘
                 │     │  │
       ┌─────────▼┐ ┌─▼──▼────────┐  ┌───────────────┐
       │ Formalize│ │   Prove      │  │    Review      │
       │ Agent    │ │   Agent      │  │    (子模块)     │
       │          │ │              │  │                │
       │ Reads:   │ │ Reads:       │  │ Reads:         │
       │  manifest│ │  manifest    │  │  task_results/ │
       │          │ │              │  │                │
       │ Writes:  │ │ Writes:      │  │ Writes:        │
       │  .lean   │ │  .lean       │  │  proof-journal/│
       │  .tex    │ │  task_results│  │  PROJECT_STATUS│
       └──────────┘ └──────────────┘  └───────────────┘
```

---

## 9. 与原版 Archon 的关系

### 保留

- 文件级 agent 隔离（一个 agent 一个文件）
- prover-prover.md / prover-polish.md / review.md 核心 prompt
- lean4 skill agents (proof-repair, golfer, sorry-filler)
- LSP/MCP 工具链
- informal agent

### 新增

| 组件 | 用途 |
|------|------|
| `blueprint-orchestrator.py` | Python 编排器，替代 `archon-loop.sh` |
| `blueprint-status.py` | 状态查询 CLI + 库 |
| `dep_graph.json` | 持久化依赖图 |
| `.archon/manifests/*.yaml` | 文件级任务清单 |
| `prompts/formalize.md` | Formalize Agent prompt |
| `prompts/plan-blueprint.md` | Blueprint-aware Plan prompt |

### 替代

| 原版 | 新版 | 原因 |
|------|------|------|
| 行号定位 | FQN 定位 | 行号脆弱 |
| PROGRESS.md 自由文本 | manifest YAML | 结构化、可解析 |
| 文件级全量处理 | 节点级选择性处理 | 避免动未 aligned 的声明 |
| sorry_analyzer 全局扫描 | 按节点判定 proved | 精确到单个声明 |

---

## 10. 外部参考：Matlas 的依赖图模型及启示

### 10.1 Matlas 是什么

北大 AI4Math 团队的工作。从 43.5 万篇论文 + 1900 本教材中提取 807 万条数学陈述，构建依赖图，然后在图上做拓扑展开使每条陈述 self-contained，最后做向量检索。

### 10.2 他们的依赖图数据模型

**节点：** 每条数学陈述，包含三个字段：
- `type` — 陈述类型（definition / theorem / lemma / ...）
- `content` — 文本内容
- `local dependency links` — 指向同文档内其他节点的依赖

**边：** 有向边 A → B 表示"B 的成立依赖 A"

**作用域：** 每个文档（paper/book）一张独立的有向依赖图，**没有跨文档依赖**。

**提取方式：** 两阶段 pipeline：
1. Locator：LLM 生成文档专用的正则表达式，定位陈述候选段
2. Structurer：DeepSeek-V3.2 对候选段（batch size=5, context window=4000 chars）生成结构化输出（type + content + dependency links）

### 10.3 关键创新：拓扑展开（Unfolding）

他们不把依赖图直接用于调度，而是做了一个**展开操作**使每条陈述变成 self-contained：

```
Layer 0: 无依赖的节点（定义、公理）
Layer 1: 只依赖 Layer 0 的节点
Layer 2: 只依赖 Layer 0-1 的节点
...
```

对每个节点，按拓扑序递归地把上游依赖的内容**内联展开**到自身文本中。最终每条陈述包含了理解它所需的所有前置知识。

### 10.4 对我们 blueprint 工作流的启示

#### 启示 1：展开后的 NL 是更好的 formalize 输入

当前 Formalize Agent 拿到的是一条孤立的 NL 陈述 + 一个依赖列表。Agent 需要自己去读每个依赖的 NL 内容来理解上下文。

Matlas 的做法提示我们：**可以在生成 manifest 时，为每个节点预计算一个"展开后的 NL"**，把所有被依赖的定义/定理的文本内联进来。这样 agent 拿到的是一个 self-contained 的数学陈述，不需要反复跳转读依赖。

```yaml
# manifest 中的 expanded_nl 字段
- node_id: prereq:thm:adams-weak-convergence
  nl_text: |
    The Adams spectral sequence for bounded below spectra
    of finite type weakly converges.
  expanded_nl: |
    [Definition: Bounded Below] A spectrum X is bounded below if...
    [Definition: Finite Type] A spectrum is of finite type if...
    [Theorem: Adams Spectral Sequence] For any spectrum X, there is a spectral sequence...

    The Adams spectral sequence for bounded below spectra
    of finite type weakly converges.
```

这对 AI agent 的效果应该显著——减少上下文跳转，减少误解依赖的风险。

#### 启示 2：分层调度更好理解优先级

Matlas 的分层（layer 0, 1, 2, ...）本质上就是我们依赖图的拓扑层级。但他们用层级来组织展开顺序，我们可以用层级来组织**调度优先级**：

```
Layer 0 (叶节点/定义): 最先 formalize，无依赖
Layer 1: 只依赖 Layer 0 的定理
Layer 2: 依赖 Layer 0-1 的定理
...
```

这比当前草稿中的"按依赖深度浅的优先"更精确——直接用拓扑分层编号。

#### 启示 3：他们没有做跨文档依赖——我们也不必跨项目

Matlas 的一个有意义的设计选择：每个文档的依赖图是独立的，不试图建立跨文档的引用关系。类似地，我们的 blueprint 依赖图也应该保持在**单个项目内闭合**。对外部数学结果用 `axiom` 节点封装边界，而不是试图建立到 Mathlib 或其他项目的依赖链。

#### 启示 4：他们的 SearchResult 数据模型非常扁平

Matlas 的 API 返回：
```json
{
  "type": "paper",
  "entity_name": "Theorem 3.1",
  "doi": "...",
  "title": "...",
  "authors": "...",
  "statement": "The expanded, self-contained statement text",
  "candidate_id": "unique-id"
}
```

注意：**没有依赖图结构、没有层级信息、没有生命周期状态**。这是一个纯检索接口——所有图结构都在构建时消化掉了（展开成 self-contained 文本），检索时只需要扁平的文本匹配。

这和我们的需求不同——我们需要依赖图在运行时持续存在（用于调度）。但他们的"构建时展开、查询时扁平"的思路可以用在 agent 交互上：**agent 看到的是展开后的扁平 manifest，编排器在后台维护完整的图结构。**

#### 启示 5：Matlas 作为工具可以辅助我们的 Extract Agent

Matlas 有 807 万条数学陈述的检索库。我们的 Extract Agent 在分析论文依赖时，可以用 Matlas API 检索论文引用的外部结果（如 "by Hiblot 1975"），获取该结果的 self-contained 陈述，作为 axiom 节点的 NL 内容。

```python
# Extract Agent 遇到未定义的引用时
result = matlas_search("Hiblot 1975 finite type spectrum")
axiom_nl = result[0]['statement']  # self-contained 展开文本
# → 生成 axiom 节点，NL 内容来自 Matlas
```

---

## 11. 待讨论/决策点

1. **编排器语言**：鉴于需要图遍历和 YAML 解析，建议 Python。
2. **Formalize Agent 粒度**：一次处理一个文件中的所有待 formalize 节点（减少启动开销）。
3. **NL 变更回退传播**：definition 的 NL 变更是否回退所有依赖它的节点的 alignment？当前只回退自身。
4. **并行度限制**：同时运行多少个 `claude -p`？受 API rate limit 约束。
5. **最小任务阈值**：`min_tasks_per_agent` 默认值？太高延迟大，太低浪费多。
6. **Prove 失败的回退**：多轮失败是否通知人类重审 alignment（可能签名有误）？
7. **`dep_graph.json` 生成时机**：每次 `leanblueprint web` 自动生成。
8. **`proved` 权威判定**：从 LaTeX `\leanok` 切换到编译器检查的过渡方案。
9. **manifest 是否存到 status.yaml**：`assigned_to` 和 `attempt_count` 等字段是否污染了 status.yaml 的"blueprint 状态"语义？是否应该分成 `status.yaml`（纯数学状态）+ `assignments.yaml`（任务追踪）？
