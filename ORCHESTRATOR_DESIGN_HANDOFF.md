# Orchestrator 设计 Handoff

**最后更新:2026-05-07**

把 Archon (`/inspire/hdd/project/qproject-fundationmodel/czxs25250150/Archon`) 的 plan-prover-review 循环引入 KIP,作为推进 blueprint 节点生命周期 **后半程**(formalize 与 prove,即 `nl_reviewed → bound → aligned → proved`)的引擎。前半程(extract → reviewed)继续靠现有 `agents/blueprint-absorber/`。

本文档是 living design doc。每次设计会议后更新,下次开会请从 `## 7. 当前停在哪里` 接续。

---

## 0. 状态总览

- **Phase 0(目录命名 cleanup)**:✅ 已 land(PR #23 / AUT-52,2026-05-07)
- **Phase A(vendoring)**:🟡 待启动
- **Phase B(builder + writer)**:🟡 待启动 —— 当前讨论焦点
- 设计层未决项见 §6,集中在 builder 实现细节(4 件事)

---

## 1. 背景与核心张力

- **KIP 调度单位是 blueprint 节点**(`status.yaml` 里的 `prereq:def:ss-data` 这种 ID,带 `lean_decl: KIP.X.Y.Z`)
- **Archon 调度单位是 .lean 文件**(`PROGRESS.md` 里 `**file.lean**` 这种)
- 这是 `BLUEPRINT_WORKFLOW_DRAFT.md` 早就识别出的"阻抗失配"
- 整个 orchestrator 设计都在解决:**逻辑层(节点)↔ 物理层(文件)** 的桥接

KIP 已经有的基础设施(不要重写):
- `blueprint/status.yaml` —— 单源真相(SoT),节点状态
- `blueprint/src/chapters/*.tex` —— informal NL,带 `\lean{}` `\uses{}` `\label{}` 标记
- `blueprint/lean_decls` —— FQN 清单,`leanblueprint checkdecls` 校验
- `tools/kip-state/` —— 把 status.yaml 索引进 SQLite(`.dashboard/state.db`)
- `ui/server` + `ui/client` —— 节点中心 dashboard
- `agents/blueprint-absorber/` —— 已存在的 LLM agent,吸收 draft-hint 进 TeX

---

## 2. 已锁定的决策

按设计讨论顺序列出。粗体是今日(2026-05-07)新增/修订。

| # | 决策 | 备注 |
|---|---|---|
| 1 | **目标**:plan-prover-review 循环驱动 formalize / prove 阶段 | 不动 absorber,不动 NL review 人工门控 |
| 2 | **comments 处理**:暂作 USER_HINTS,只 plan 读 | 不做 topic 枚举/curator 层(可能是未来工作) |
| 3 | **cluster 概念**:删除,统一叫 `FileJob` | 1 file ↔ 1 job,文件不相交不变式 |
| 4 | **stage purity 不要求** | 同 file 可混 formalize 和 prove tasks |
| 5 | **同 FileJob 内部跑两次 prover**(顺序) | phase-1 autoformalize → `lake build` 门 → phase-2 prove,共享 worktree |
| 6 | **scheduler 的 `max_tasks_per_job` 删除** | 任务大小由 plan / builder 决定 |
| 7 | **跨轮 task 不持久化** | 上轮没干完的下轮重决,不 carry-forward |
| 8 | **wave 调度**:每轮只跑 wave 1 | 外部依赖未满足的 task 推迟到下轮 |
| 9 | **snapshot 用 cp**(沿用 Archon),**不**用 git-tag、**不**用 worktree | cp baseline → `.orchestrator/cycles/{N}/jobs/{slug}/baseline/{file}.lean` |
| 10 | **回滚** = `cp baseline → checkout` | 在 review 否决时触发 |
| 11 | **scheduler 不是 agent 也不是单独模块** | 是 `build_jobs()` 函数,放 `cycle.py` |
| 12 | **plan 的输出 orchestrator 不解析** | 任务结构化数据从 canonical 源(status.yaml + TeX + audit + lean_decls)来,plan 不重出 |
| 13 | ~~plan 输入 = `list[PlannedTask]`~~ → **plan 输入 = `list[FileJob]`(嵌套带 PlannedTask)** | 升级到 file 级,plan 才能做跨文件协调 |
| 14 | **LLM 阶段只剩 plan / prover / review**(absorber 在 cycle 之外) | plan 角色见决策 17 |
| 15 | **隔离机制**:文件不相交不变式 + sandbox 路径白名单 | 不用 worktree |
| **16** | **builder 角色窄化** | builder 只做"file 聚类 + comment 消费",不"代 plan 决定任务组织"。plan 升格为 cycle 协调者 |
| **17** | **plan 每轮跑、看全部 task** | 同时承担 (a) pre-flight routing(看 informal proof 设计 Lean 路线)+ (b) adaptive recovery(看 past_attempts 失败时换路子)。retry-only 切片不走 |
| **18** | **`informal_proof` 字段** | prove 阶段带,formalize 不带。多 proof 块全部拼接(用 `--- alternative proof ---` 分隔)。plan 也看 informal_proof |
| **19** | **`section_header` 字段** | 从 status.yaml `chapter`+`subsection` 拼,作为 nl_brief 前置上下文 |
| **20** | **nl_brief 走 `chapters/*.tex`(不走 web HTML)** | 切 `\begin{kind}\label{}...\end{kind}`,strip `\lean{}` `\leanok` `\uses{...}`(这三个信息已在其他字段) |
| **21** | **comment 消费标记** | 写回 `status.yaml` 节点 `comments[].consumed_at_cycle: N`,由 builder 写。打破"只 writer 动 status.yaml"默契——这是 read-only 元数据,不影响 transition |
| **22** | **plan 能力边界** | 只能 (i) per-FileJob 写 strategy notes、(ii) 排优先级。**禁止**改 FileJob 结构(拆/合/跨 file 移 task)。跨 FileJob 依赖标注留作未来 |
| **23** | **目录命名**:`.dashboard/` + `.orchestrator/` | 已 land(PR #23 / AUT-52)。`.kip/` 是项目缩写,不该作工具运行时目录名 |

---

## 3. 当前架构图

```
canonical sources                    .orchestrator/audit/
  ├─ blueprint/status.yaml           ├─ transitions.jsonl
  ├─ blueprint/src/chapters/*.tex    └─ comment_consumption.jsonl
  ├─ blueprint/lean_decls
  └─ status.yaml.comments[]
                  │
                  ▼
        build_objectives()    [纯 Python,无 LLM]
        - 选 ready 节点(确定性规则,见 §6.1)
        - 切 nl_brief(走 .tex,strip \lean/\leanok/\uses)
        - 切 informal_proof(prove 阶段)
        - 抽 upstream signatures(见 §6.2)
        - 抽 past_attempts(见 §6.3)
        - 拼 section_header
        - 标记 comments[].consumed_at_cycle
                  │
                  ▼ list[PlannedTask]
                  │
        build_jobs()          [Python]
        - 按 file 聚类,1 file ↔ 1 job
        - tasks 排序(formalize 在 prove 之前)
                  │
                  ▼ list[FileJob]
                  │
        plan(list[FileJob])   [LLM]
        - pre-flight routing:per-task 设计 Lean 路线
        - adaptive recovery:看 past_attempts 换路子
        - 排优先级
        - 输出:cycle_plan.md(单文件,含全部 task 策略)
                  │
                  ▼ list[FileJob with plan_notes]
                  │
        parallel per FileJob:  [LLM]
          ├─ snapshot (cp baseline)
          ├─ phase-1 prover (autoformalize)  ← 读 plan_notes 相关段
          ├─ lake build gate
          ├─ phase-2 prover (prove)
          └─ aggregate → JobResult
                  │
                  ▼ list[JobResult]
                  │
        review                [LLM]
                  │
                  ▼ milestones.jsonl
                  │
        writer                [Python]
        - 校验 milestone vs status.yaml 一致性
        - 接受 → 更新 status.yaml + audit append
        - 拒绝 → cp baseline → checkout(回滚)
```

---

## 4. 目录布局(目标态)

```
KIP/
├── agents/
│   ├── blueprint-absorber/        (existing)
│   ├── orchestrator/              (NEW)
│   │   ├── SYSTEM.md              # cycle 设计说明
│   │   ├── cycle.py               # vendored & 改造的 Archon loop.py
│   │   ├── jobs/
│   │   │   ├── builder.py         # build_objectives + build_jobs
│   │   │   ├── runner.py          # run_file_job (phase-1 / phase-2)
│   │   │   └── snapshot.py        # cp baseline / rollback
│   │   ├── schemas/               # pydantic 模型
│   │   ├── validators/
│   │   ├── settings.json          # sandbox 权限
│   │   ├── restrict-paths.sh
│   │   └── run.sh
│   └── prompts/                   (vendored from Archon)
│       ├── plan.md                # 改:看 list[FileJob],per-task 写 strategy
│       ├── prover-autoformalize.md
│       ├── prover-prover.md
│       ├── prover-polish.md       # 暂不接入,polish 阶段未启用
│       └── review.md              # 改:输出 milestones.jsonl
├── tools/
│   ├── lean-lsp-mcp/              (vendored from Archon)
│   ├── archon-lean4-skills/       (vendored,deep agents 在这里)
│   ├── leanblueprint/             (existing)
│   ├── plastexdepgraph/           (existing)
│   └── kip-state/                 (existing,扩展 audit 表)
├── .dashboard/
│   └── state.db                   (existing,UI 索引)
├── .orchestrator/                 # NEW
│   ├── cycles/
│   │   └── cycle_{N}/
│   │       ├── objectives.json    # builder dump,审计用
│   │       ├── cycle_plan.md      # plan 输出,prover 各取所需段
│   │       ├── jobs/
│   │       │   └── {slug}/
│   │       │       ├── job.json
│   │       │       ├── baseline/{file}.lean
│   │       │       ├── prover-phase1.jsonl
│   │       │       ├── prover-phase2.jsonl
│   │       │       └── result.json
│   │       └── milestones.jsonl
│   └── audit/
│       ├── transitions.jsonl      # append-only 跨轮日志
│       └── comment_consumption.jsonl  # plan 消费 comment 的标记
└── ui/                            (existing,加 Cycles tab)
```

---

## 5. Schema 契约

五个核心 dataclass(用 pydantic v2 实现),数据流:

```
list[PlannedTask]   (build_objectives 写)
  → list[FileJob]   (build_jobs 写,plan & runner 读)
  → cycle_plan.md   (plan 写自由文本,prover 读)
  → list[TaskOutcome]  (runner 聚合 prover JSONL)
  → list[Milestone] (review 写,writer 读)
  → status.yaml + AuditEntry  (writer 写)
```

关键字段:

```python
@dataclass(frozen=True)
class PlannedTask:
    node_id: str
    fqn: str
    stage: Literal["formalize", "prove", "polish"]
    file: Path
    section_header: str             # "Chapter > Subsection",从 status.yaml 拼
    nl_brief: str                   # builder 从 chapters/*.tex 切,strip \lean/\leanok/\uses
    informal_proof: str | None      # prove 阶段非空,多 proof 块全拼;formalize 阶段 None
    upstream_signatures: list[str]  # 见 §6.2 抽法待定
    past_attempts: list[str]        # 见 §6.3,首版可能为空
    user_hints: str                 # status.yaml 节点 comments[] 全文(未消费部分)

@dataclass(frozen=True)
class FileJob:
    file: Path
    tasks: list[PlannedTask]        # formalize 排在 prove 之前
    job_dir: Path
    baseline_path: Path
    plan_notes: str | None          # plan 写完后填充,per-FileJob 自由文本

@dataclass
class Milestone:
    cycle: int
    node_id: str
    fqn: str
    transition: Literal[
        "proved", "bound", "polished",
        "stuck", "no-change",
        "rejected-by-scheduler", "rejected-by-review",
        "blocked-by-formalize-failure", "scope-violation",
    ]
    evidence: MilestoneEvidence
    accepted: bool
    rollback_required: bool
    follow_up: str
```

**Wire format**:JSON 文件 + JSONL,LLM 用 Write 工具产出,Python 端 `model_validate_json`。

**Plan agent 输出例外**:plan 不写结构化文件,只写 `cycle_plan.md` 自由文本,**orchestrator 永远不解析它**。runner 读时把整文件作为上下文交给 prover,prover 自己挑相关段。

**Comment 消费标记**:builder 在生成 `user_hints` 时,把所选 comment 在 `status.yaml` 写入 `comments[i].consumed_at_cycle: N`,同时 append 到 `.orchestrator/audit/comment_consumption.jsonl`。下一轮 builder 跳过已消费 comment(除非节点又出新 comment)。

---

## 6. 未决问题(builder 实现层)

§6.1–6.4 是当前讨论焦点。§6.5 是更远期的次要 open。

### 6.1 ready 节点选取规则

builder 读 status.yaml flags 推 stage:

| flags | 推断 | 处理 |
|---|---|---|
| `nl_reviewed=true, bound=false` | formalize 待做 | 进 cycle |
| `bound=true, aligned=false` | 待人工 align review | **跳过**(非 cycle 任务) |
| `aligned=true, proved=false` | prove 待做 | 进 cycle |
| `proved=true` | polish | 待定(决策 §6.5) |

**未决**:有未满足 prereq 的节点(`\uses{}` 指向的上游节点尚未到 ready 状态)如何处理?决策 8 说"推到下一轮"——具体实现是 builder 在 build_objectives 阶段就过滤,还是 build_jobs 阶段过滤?我倾向 build_objectives 阶段直接 skip(数据干净),并把 skip 原因记到 `.orchestrator/cycles/{N}/objectives.json` 审计。

### 6.2 upstream_signatures 抽法

三个选项:

| 方案 | 说明 | 准度 | 复杂度 |
|---|---|---|---|
| (a) Lean LSP query | 起 daemon,query symbol → signatureHelp | 高 | 高(需起 LSP daemon) |
| (b) grep .lean 文件 | 直接读源文件,正则切 `def FQN ... :=` 之前 | 中(implicit/typeclass 处理粗) | 低 |
| (c) 不抽,推给 prover | builder 只给 FQN,prover 自己 LSP 查 | (在 prover 那边解决) | 极低 |

倾向 **(b) 起步,(a) 升级路径**。能跑就行,粗糙 signature 也能给 prover 类型参考。

### 6.3 `past_attempts` 数据源

`.orchestrator/audit/transitions.jsonl` 还没建。这是 builder 的依赖。

选项:
- (i) 第一版返回空 list,等 audit 跑过几轮再有数据(不阻塞 builder 落地)
- (ii) 先实现 writer 的 audit append,builder 配套读

倾向 **(i)**,writer 同步在 Phase B 做。

**窗口**(决策 17 拍板 plan 看 past_attempts):
- 倾向 **last 1 轮**:再往前的失败上一轮 plan 已经处理过、变成新策略,老失败重复喂 plan 是冗余
- 折中方案:last 1 完整 + 更早的摘要(增加 builder 复杂度,先不做)

### 6.4 `USER_HINTS` 字段

直接拿 status.yaml 节点 `comments[]` 全文(未消费部分),不做关键词匹配——决策 2 说 plan 自己读。

未决细节:
- comment 拼接格式(JSON dump?markdown 列表?)
- 长度上限?(防止历史 comment 堆积成几千 token)

倾向 markdown 列表,不设硬上限,observe 后再说。

### 6.5 其他次要 open

- `tools/leanblueprint` 是否要扩展 `dep_graph.json` 输出(供 builder 直接吃,不靠解析 web/*.html)
- absorber 与 cycle 的边界:cycle 跑期间 absorber 改 TeX(改 `nl_hash`)如何处理?目前 schema 里有 `nl_hash` 锚定,但流程没具体写
- `polish` 阶段是否独立 cycle 还是混入主循环
- `MAX_JOBS_PER_CYCLE` 的具体数值(进程并发上限),需要根据机器实测定
- `MAX_TASKS_PER_CYCLE` 软上限(plan 信息量收口),决策 17 后这个回归为可选 —— 看实际 ready 节点数才能判断要不要

---

## 7. 当前停在哪里

**最近一次会议(2026-05-07)成果**:
- §6.1 全部回答(plan 每轮跑、看全部 task,§2 决策 17)
- §2 新增决策 16-23(builder 窄化、plan 升格、informal_proof、section_header、nl_brief 走 .tex、comment 消费、plan 能力边界、目录命名)
- §3 架构图重画
- §5 schema 更新
- 目录命名 cleanup(PR #23)已 land

**下次开会从这里接续**:聊完 §6.1–6.4 这 4 件事(builder 实现细节)后,可以进 Phase B 写代码。

具体路线两条:

**Path 1 —— 把 §6.1–6.4 4 件事拍完**(推荐)
- ready 选取:确认 prereq 不满足在 build_objectives 阶段过滤
- upstream_signatures:确认 (b) grep 起步
- past_attempts:确认第一版返空 list,window=last 1
- USER_HINTS:确认 markdown 列表 + 不设上限
- 然后开 Phase A(vendoring)→ Phase B(builder + writer)

**Path 2 —— 跳过细节,直接草稿 builder.py**
- 用我"倾向"的默认值起 outline
- 在 PR review 时再讨论 4 件事
- 适合用户精力有限时

---

## 8. 落地 phases

| Phase | 内容 | 状态 | PR/Linear |
|---|---|---|---|
| **0** | **Cleanup**:`.kip/` → `.dashboard/` + `.orchestrator/` | ✅ 2026-05-07 land | PR #23 / AUT-52 |
| A | Vendoring: `tools/lean-lsp-mcp/`, `tools/archon-lean4-skills/`, `agents/orchestrator/runner.py` from Archon | 🟡 待 | 1 PR + 1 AUT issue |
| B | `build_objectives()` + `build_jobs()` + `writer.py`(status.yaml 增量更新 + audit append) + 单元测试用 status.yaml.bak fixture | 🟡 待(当前讨论) | 1 PR |
| C | 单节点 e2e:`--max-iterations 1`,跑通 `aligned → proved` 一个简单 case | 🟡 待 | 1 PR |
| D | 并行 FileJob + plan agent 接入 + deep escalation | 🟡 待 | 1 PR |
| E | UI Cycles tab + polish 阶段 | 🟡 待 | 1 PR |

每个 Phase 对应一个 Linear AUT issue,符合 `CLAUDE.md` 的 PR 规约。

---

## 9. 关键文件路径速查

**Archon 侧**:
- 主循环:`/inspire/hdd/project/qproject-fundationmodel/czxs25250150/Archon/src/archon/commands/loop.py` (~720 行)
- 状态解析:`Archon/src/archon/state.py` (~243 行)
- Subprocess 包装:`Archon/src/archon/runner.py`
- Prompts:`Archon/src/archon/.archon-src/prompts/{plan,prover-autoformalize,prover-prover,prover-polish,review,init}.md`
- Lean LSP MCP:`Archon/src/archon/.archon-src/tools/lean-lsp-mcp/`
- Skills(deep agents):`Archon/src/archon/.archon-src/skills/lean4/`(包含 `lean4-proof-repair`、`lean4-axiom-eliminator`、`lean4-sorry-filler-deep`、`lean4-proof-golfer`)
- Settings 模板:`Archon/src/archon/.archon-src/settings.local.json`

**KIP 侧**:
- 节点状态:`KIP/blueprint/status.yaml`(已存在)
- TeX 章节:`KIP/blueprint/src/chapters/*.tex`
- FQN 清单:`KIP/blueprint/lean_decls`
- Lean 源:`KIP/KIP/{SpectralSequence,StableHomotopy,Synthetic}/*.lean`
- 现有 absorber:`KIP/agents/blueprint-absorber/{SYSTEM.md,run.sh,restrict-paths.sh,settings.json}`
- UI 抽屉抽块逻辑(参考用,builder 不复用):`KIP/ui/server/src/routes/nodes.ts:46-152`
- 工作流草稿:`KIP/BLUEPRINT_WORKFLOW_DRAFT.md`(2026-04-20)

**关键 Archon 行号(loop.py)**:
- 主循环结构:line 562–693
- 进程池调度:line 339, 451
- Snapshot 创建:line 156–162, 310–311, 347
- Stage 推进检查:line 553, 565, 612

---

## 10. 用户偏好(讨论暴露)

记录给下次帮助校准:
- 偏好简化、反对 over-engineering、反对 premature flexibility
- 多次砍掉我提议的复杂层(comment curator、worktree、cluster 抽象、scheduler 模块、plan 为决策者、retry-only 切片)
- 倾向"先简后繁",MVP 先跑通再谈优化
- Push back 我用过度抽象的命名("scheduler"、"cluster"、`.kip/` 当工具目录)
- 容忍冷静的反复批判,期待我直接改方案而不是辩护
- 决策时常常先听我的备选,然后**只回一个字**或一句话拍板("好的"、"B"、"都需要"、"走方案2")—— 这种回应是命令,不是疑问

---

## 附:对话锚点

按时间顺序的关键 turning points,方便回溯:

**2026-05-06 会议**:
1. "把它当做之前 archon 里的 human hint" → comment curator 取消
2. "如何 cluster?如何避免两个 agent 编辑同一个文件" → worktree 讨论起点
3. "这个要求是很苛刻的" → stage purity 取消
4. "cluster 现在和 file 有啥区别" → cluster 改 FileJob
5. "plan 后面加一个 scheduler 是干什么的" → scheduler 改 build_jobs 函数
6. "保留 archon 的 cp 做法吧" → snapshot 选 cp
7. "现在 plan agent 的输出是什么,也是 python class 吗" → 暴露 LLM/Python 边界设计模糊
8. "我觉得我们没必要从 plan 的输出里解析这些东西" → builder 成结构化源头
9. "你知道哪些节点相关的任务被喂给 plan,自然就知道要检查什么了" → 信息折返消除
10. "我觉得现在的设计 plan agent 要处理的信息有些多啊" → 我提议砍 plan
11. "plan agent 的价值在于协调任务... 你看下 archon 的 plan.md" → 用户纠正,plan 留下

**2026-05-07 会议**(本次):
12. "从 tex 块抽 informal 描述这件事情没有做成吗" → 暴露 UI 抽屉走的是 plastex 编译产物 HTML,不是 .tex;builder 决定独立走 .tex 路径(决策 20)
13. "prove 阶段带 informal proof 就可以,formalize 阶段不带,而且 proof 应该要带给 plan agent 进行路线设计" → 决策 18 + 间接拍板 plan 角色
14. "都需要" → 决策 17(plan 同时承担 routing + recovery)
15. "不是要先做 builder 吗你不是说" → 我跑题被纠正,回归 builder 主线
16. "我觉得 builder 这一步主要承担把节点的任务聚类到文件级别..." → 决策 16(builder 窄化)+ 决策 13 修订(plan 输入升 file 级)
17. ".kip 用的不对啊,这是数学问题的缩写" → 决策 23 + Phase 0 cleanup
18. "走方案 2" → 一并清理 `.kip/state.db`(虽然是既有技术债)
19. "好的" → 授权执行 cleanup PR(AUT-52,PR #23 land)
