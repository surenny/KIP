# Blueprint Absorber Agent

将 `draft-hint/` 里的数学家提示文件吸收进 `blueprint/src/chapters/*.tex`。

## 前置条件

```bash
pip install -e tools/plastexdepgraph
pip install -e tools/leanblueprint
```

## 本地运行

```bash
# 处理单个文件
./agents/blueprint-absorber/run.sh draft-hint/foo.md

# 处理所有待吸收文件
./agents/blueprint-absorber/run.sh

# 指定模型
./agents/blueprint-absorber/run.sh --model opus draft-hint/foo.md

# 试运行（只显示会处理哪些文件，不实际调用 claude）
./agents/blueprint-absorber/run.sh --dry-run
```

运行日志保存在 `agents/blueprint-absorber/logs/run-<timestamp>/absorber.jsonl`。

## 远程监控（多机协作）

如果需要在本机跑 agent、同时让部署在服务器上的 dashboard 实时看到运行进度，
设置以下两个环境变量即可：

```bash
export KIP_INGEST_URL=https://kip.opensii.ai/dashboard/api/ingest
export KIP_INGEST_TOKEN=<token>   # 与服务器 KIP_INGEST_TOKEN 一致，未配置 token 时可不设
```

设置后正常跑 agent，每条日志 event 会自动上报到服务器，在 dashboard 的
**Logs** tab 实时可见。未设置 `KIP_INGEST_URL` 时行为与纯本地模式完全一致。

### 验证网络是否通

```bash
curl -s -w "\nHTTP %{http_code}" -X POST "$KIP_INGEST_URL" -H "Content-Type: application/json" -d '{"agent":"blueprint-absorber","runId":"run-test","hintFile":"test","row":{"ts":"2026-01-01T00:00:00Z","event":"text","content":"ping"}}'
```

返回 `HTTP 204` 即表示连接正常。

## 状态追踪

`agents/blueprint-absorber/STATUS.md` 记录哪些 hint 文件已吸收（Absorbed）、哪些待处理（Pending）。
成功吸收后 agent 自动更新此文件。
