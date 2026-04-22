"""
plasTeX package for tikzpicture environments in web builds.

Captures tikzpicture content verbatim (preventing plasTeX from garbling
tikz commands like \\fill), then pre-compiles each diagram to SVG using
the system's pdflatex + dvisvgm during a post-parse callback.
"""
import hashlib
import os
import subprocess
import tempfile
from pathlib import Path

from plasTeX import Command, Environment, VerbatimEnvironment
from plasTeX.Logging import getLogger

log = getLogger()

# Tikz preamble for standalone compilation — must match what the PDF build uses.
_TIKZ_PREAMBLE = r"""
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,mathtools}
\usepackage{tikz}
\usetikzlibrary{arrows.meta}
\usetikzlibrary{calc}

\definecolor{lightgray}{RGB}{200,200,200}
\definecolor{llgray}{RGB}{235,235,235}

\newcommand{\tikzgrid}[4]{\foreach \x in {#1,...,#2} {
        \draw[black!20] (\x-0.5, #3-0.5) -- (\x-0.5, #4-0.5);
    }
    \foreach \y in {#3,...,#4} {
        \draw[black!20] (#1-0.5, \y-0.5) -- (#2-0.5, \y-0.5);
    }
}

\newcommand{\drawarrow}{\draw[-{Stealth[length=1.5mm]}, shorten >=(0.08cm)]}

\newcommand{\AF}{\mathrm{AF}}
\newcommand{\Sus}{\Sigma}
\newcommand{\sma}{\wedge}
\newcommand{\bF}{\mathbb{F}}
\newcommand{\HF}{\mathrm{H}\bF_2}

% Macros from 112.tex (large spectral sequence charts)
\newcommand{\labelar}[1]{\overset{\uparrow}{#1}}
\newdimen\widthA
\newcommand{\resizelabel}[2]{\settowidth{\widthA}{#2}\pgfmathsetmacro{\ratio}{min((1cm)/max(\widthA, 1cm), #1)}\scalebox{\ratio}{#2}}
"""


def _compile_tikz_to_svg(tikz_source: str) -> str:
    """Compile a tikzpicture to SVG. Returns SVG string, or '' on failure."""
    doc = (
        r'\documentclass[crop,tikz]{standalone}'
        '\n'
        + _TIKZ_PREAMBLE
        + r'\begin{document}'
        '\n'
        + r'\begin{tikzpicture}' + tikz_source + '\n'
        + r'\end{tikzpicture}'
        '\n'
        + r'\end{document}'
        '\n'
    )
    with tempfile.TemporaryDirectory() as tmpdir:
        tex_path = os.path.join(tmpdir, 'tikz.tex')
        with open(tex_path, 'w') as f:
            f.write(doc)
        try:
            result = subprocess.run(
                ['latex', '-interaction=nonstopmode', '-halt-on-error', 'tikz.tex'],
                cwd=tmpdir,
                capture_output=True,
                timeout=120,
            )
            dvi_path = os.path.join(tmpdir, 'tikz.dvi')
            svg_path = os.path.join(tmpdir, 'tikz.svg')
            if not os.path.exists(dvi_path):
                stdout = result.stdout.decode(errors='replace')
                errors = [l for l in stdout.split('\n') if l.startswith('!')]
                log.warning('tikzpicture: latex produced no DVI. Errors: %s',
                            '; '.join(errors[:5]) or '(none found)')
                return ''
            result = subprocess.run(
                ['dvisvgm', '--no-fonts', '--exact-bbox', '-o', svg_path, dvi_path],
                cwd=tmpdir,
                capture_output=True,
                timeout=120,
            )
            if os.path.exists(svg_path):
                return Path(svg_path).read_text()
            log.warning('tikzpicture: dvisvgm produced no SVG: %s', result.stderr.decode())
            return ''
        except subprocess.TimeoutExpired:
            log.warning('tikzpicture: compilation timed out')
            return ''
        except Exception as exc:
            log.warning('tikzpicture: compilation failed: %s', exc)
            return ''


class usetikzlibrary(Command):
    args = 'libraries:str'
    def invoke(self, tex):
        Command.invoke(self, tex)
        return []


class tikzpicture(VerbatimEnvironment):
    blockType = True

    def invoke(self, tex):
        tokens = VerbatimEnvironment.invoke(self, tex)
        if tokens and tokens[0] is self:
            self._verbatim = ''.join(str(t) for t in tokens[1:])
            return [self]
        return tokens


def ProcessOptions(options, document):
    """Register a post-parse callback to compile tikzpictures to SVG."""
    svg_cache = {}

    def compile_tikzpictures():
        from plasTeX import Node
        tikz_nodes = []

        def walk(node):
            if hasattr(node, '_verbatim') and node.nodeName == 'tikzpicture':
                tikz_nodes.append(node)
            for child in node.childNodes:
                if isinstance(child, Node):
                    walk(child)
        walk(document)

        outdir = Path(document.userdata.get('working-dir', '.')).parent / 'web' / 'images'
        outdir.mkdir(parents=True, exist_ok=True)

        for i, node in enumerate(tikz_nodes):
            content = node._verbatim
            cache_key = hashlib.md5(content.encode()).hexdigest()[:12]

            if cache_key in svg_cache:
                node.userdata['tikz_svg_file'] = svg_cache[cache_key]
                continue

            log.info(f'Compiling tikzpicture {i+1}/{len(tikz_nodes)} ...')
            svg = _compile_tikz_to_svg(content)
            if svg:
                svg_filename = f'tikz-{cache_key}.svg'
                svg_path = outdir / svg_filename
                svg_path.write_text(svg)
                node.userdata['tikz_svg_file'] = f'images/{svg_filename}'
                svg_cache[cache_key] = f'images/{svg_filename}'
                log.info(f'  -> {svg_filename}')
            else:
                node.userdata['tikz_svg_file'] = ''
                log.warning(f'  -> FAILED (tikzpicture #{i+1})')

    document.addPostParseCallbacks(200, compile_tikzpictures)
