# Blueprint Workspace

这个目录是从
`data/sources/arxiv/2412.10879/tex/main.tex`
复制并改造成 `leanblueprint` 期望的源码布局。

如果这套 blueprint 需要交给论文作者本人继续补标注，请先看：

- `AUTHOR_GUIDE.zh.md`

约定如下：

- 原始论文源码保持不变。
- `src/content.tex` 是从原稿自动抽取出的正文。
- `src/macros/common.tex` 保留原有 preamble，并额外加载 `blueprint` 包。
- `src/web.tex` 和 `src/print.tex` 是 leanblueprint 的两个入口。

后续接入 Lean 声明时，优先在 `src/content.tex` 中逐步加入：

- `\lean{...}`
- `\leanok`
- `\uses{...}`

如果本机尚未安装 `leanblueprint`，可以在 Lean 工程目录下安装并使用：

```bash
python -m pip install leanblueprint
leanblueprint pdf
leanblueprint web
```

是否需要额外生成 `leanpkg.tex` 取决于你后续是否要把定理和
`FormalMathProject` 中的 Lean 声明建立链接。

当前这个仓库里，Lean 工程位于 `formal/leanworkspace/`，但 git 仓库根目录更外层。
`leanblueprint` 官方 CLI 会把 git 根目录当成项目根，因此这里直接运行
`leanblueprint pdf` / `leanblueprint web` 会认错 `lakefile.lean` 位置。

已经验证可用的本地构建方式是：

```bash
cd formal/leanworkspace/blueprint
bash build.sh
```

它会做三件事：

- 生成 PDF 到 `blueprint/print/print.pdf`
- 预处理 web 专用源码 `src/web_content.tex` 和 `src/web_112.tex`
- 生成 HTML 到 `blueprint/web/index.html`

说明：

- web 构建为了绕过 `plasTeX` 对 `enumitem`、复杂图形缩放和大表格的兼容问题，
  会把部分 `figure` / `table` 在 web 版里替换成占位提示；PDF 版保持完整。
