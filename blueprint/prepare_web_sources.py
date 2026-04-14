from __future__ import annotations

from pathlib import Path


SRC = Path(__file__).resolve().parent / "src"

import re


def expand_inputs(text: str, base_dir: Path) -> str:
    """Recursively expand \\input{...} directives in *text*."""
    pattern = re.compile(r"^\\input\{([^}]+)\}\s*$", re.MULTILINE)
    def _replace(m: re.Match) -> str:
        rel = m.group(1)
        path = base_dir / (rel if rel.endswith(".tex") else rel + ".tex")
        if path.is_file():
            return expand_inputs(path.read_text(), path.parent)
        return m.group(0)  # leave unchanged if file not found
    return pattern.sub(_replace, text)


def read_group(text: str, start: int) -> tuple[str, int]:
    if start >= len(text) or text[start] != "{":
        raise ValueError(f"expected '{{' at offset {start}")
    depth = 0
    i = start
    while i < len(text):
        ch = text[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "%":
            newline = text.find("\n", i)
            if newline == -1:
                return text[start + 1 : i], len(text)
            i = newline + 1
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : i], i + 1
        i += 1
    raise ValueError("unterminated brace group")


def strip_macro(text: str, macro: str, arity: int, keep_index: int) -> str:
    needle = f"\\{macro}"
    out: list[str] = []
    i = 0
    while True:
        j = text.find(needle, i)
        if j == -1:
            out.append(text[i:])
            return "".join(out)
        line_start = text.rfind("\n", 0, j) + 1
        comment = text.find("%", line_start, j)
        if comment != -1:
            out.append(text[i : j + len(needle)])
            i = j + len(needle)
            continue
        out.append(text[i:j])
        k = j + len(needle)
        args: list[str] = []
        for _ in range(arity):
            while k < len(text) and text[k].isspace():
                k += 1
            group, k = read_group(text, k)
            args.append(group)
        out.append(args[keep_index])
        i = k


def strip_environment(text: str, env: str, replacement: str) -> str:
    begin = f"\\begin{{{env}}}"
    end = f"\\end{{{env}}}"
    out: list[str] = []
    i = 0
    while True:
        j = text.find(begin, i)
        if j == -1:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:j])
        k = text.find(end, j)
        if k == -1:
            raise ValueError(f"unterminated environment {env}")
        out.append(replacement)
        i = k + len(end)


def prepare_web_file(src_name: str, dst_name: str) -> None:
    text = (SRC / src_name).read_text()
    text = expand_inputs(text, SRC)
    text = strip_macro(text, "scalebox", 2, 1)
    text = strip_macro(text, "resizebox", 3, 2)
    text = strip_environment(
        text,
        "figure",
        "\n\\begin{center}\\textit{Figure omitted in web build; see PDF version.}\\end{center}\n",
    )
    if src_name == "content.tex":
        text = strip_environment(
            text,
            "table",
            "\n\\begin{center}\\textit{Table omitted in web build; see PDF version.}\\end{center}\n",
        )
    if src_name == "content.tex":
        text = text.replace("\\include{112}", "\\include{web_112}")
    (SRC / dst_name).write_text(text)


def main() -> None:
    prepare_web_file("content.tex", "web_content.tex")
    prepare_web_file("112.tex", "web_112.tex")


if __name__ == "__main__":
    main()
