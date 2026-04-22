import re

from plasTeX import Environment
from plasTeX.Base.LaTeX.Math import MathEnvironment
from plasTeX.PackageResource import PackageProcessFilecontents


MATHJAX_MACROS = {
    'prescript': '["{}^{#1}_{#2}{#3}", 3]',
    'Sus': '"\\\\Sigma"',
    'sma': '"\\\\wedge"',
}

_MATHJAX_BLOCK = re.compile(
    r'<script>\s*MathJax\s*=\s*\{.*?\}\s*\}\s*</script>',
    re.DOTALL,
)

_MATHJAX_V2_BLOCK = re.compile(
    r'<script type="text/x-mathjax-config">\s*'
    r'MathJax\.Hub\.Config\(\{.*?\}\);\s*'
    r'</script>',
    re.DOTALL,
)


def _fix_mathjax_config(document, s):
    """Fix the MathJax config block in rendered HTML:
    1. Add missing comma after inlineMath array
    2. Replace lowercased macro names with correct casing
    3. Handle both MathJax v3 config and v2-style Hub.Config
    """
    macro_lines = ',\n          '.join(
        f'{k}: {v}' for k, v in MATHJAX_MACROS.items()
    )
    v3_block = (
        '<script>\n'
        '  MathJax = {\n'
        '    tex: {\n'
        "      inlineMath: [['\\\\(','\\\\)']],\n"
        '      macros: {\n'
        f'          {macro_lines}\n'
        '      }\n'
        '    }\n'
        '  }\n'
        '</script>'
    )
    if _MATHJAX_BLOCK.search(s):
        s = _MATHJAX_BLOCK.sub(lambda m: v3_block, s, count=1)
    elif _MATHJAX_V2_BLOCK.search(s):
        s = _MATHJAX_V2_BLOCK.sub(lambda m: v3_block, s, count=1)
    return s


def ProcessOptions(options, document):
    document.addPackageResource(
        PackageProcessFilecontents(data=_fix_mathjax_config)
    )


class CD(MathEnvironment):
    mathMode = True
    blockType = False

    def invoke(self, tex):
        if self.macroMode == Environment.MODE_END:
            return

        escape = self.ownerDocument.context.categories[0][0]
        bgroup = self.ownerDocument.context.categories[1][0]
        egroup = self.ownerDocument.context.categories[2][0]
        self.ownerDocument.context.push(self)
        self.parse(tex)
        self.ownerDocument.context.setVerbatimCatcodes()

        name = self.nodeName
        if self.macroMode != Environment.MODE_NONE:
            if self.ownerDocument.context.currenvir is not None:
                name = self.ownerDocument.context.currenvir

        endpattern = list(r'%send%s%s%s' % (escape, bgroup, name, egroup))
        endlength = len(endpattern)
        collected = []

        for tok in tex:
            collected.append(tok)
            if len(collected) >= endlength:
                if collected[-endlength:] == endpattern:
                    collected = collected[:-endlength]
                    self.ownerDocument.context.pop(self)
                    end = self.ownerDocument.createElement(name)
                    end.parentNode = self.parentNode
                    end.macroMode = Environment.MODE_END
                    res = end.invoke(tex)
                    if res is None:
                        res = [end]
                    tex.pushTokens(res)
                    break

        self._verbatim = ''.join(str(t) for t in collected)
        return [self]

    @property
    def source(self):
        body = getattr(self, '_verbatim', '')
        # HTML-entity-encode < and > so mathjax_lt_gt doesn't convert them
        # to {\lt}/{\gt} LaTeX commands (which break amscd arrow syntax).
        # The browser decodes &lt;/&gt; back to </> for MathJax.
        body = body.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')
        return r'\begin{CD}' + body + r'\end{CD}'
