# Blueprint Workspace

`leanblueprint` 源码布局。约定：

- `src/content.tex` 是从原稿抽取出的正文。
- `src/macros/common.tex` 保留原 preamble，并加载 `blueprint` 包。
- `src/web.tex` 和 `src/print.tex` 是 leanblueprint 的两个入口。

接入 Lean 声明时，在 `src/content.tex` 中加入：

- `\lean{...}`
- `\leanok`
- `\uses{...}`

## 构建

构建脚本在 Lean 工程根目录（与 `lakefile.toml` 同级）执行：

```bash
bash blueprint/build.sh
```

它会：

1. `lake build` 整个 Lean 工程
2. `lake build KIP:docs` 生成 doc-gen4 API 文档（设 `SKIP_DOCS=1` 跳过）
3. `leanblueprint pdf` 生成 PDF 到 `blueprint/print/print.pdf`
4. `leanblueprint web` 生成 HTML 到 `blueprint/web/`
5. `leanblueprint checkdecls` 校验 Lean 引用
6. 把 `blueprint/web/` 同步到 `docs/blueprint/`（用于本地预览或手动发布）

如果本机尚未安装 `leanblueprint`：

```bash
python -m pip install leanblueprint
```

说明：web 构建为了绕过 `plasTeX` 对 `enumitem`、复杂图形缩放和大表格的兼容问题，
会把部分 `figure` / `table` 在 web 版里替换成占位提示；PDF 版保持完整。
