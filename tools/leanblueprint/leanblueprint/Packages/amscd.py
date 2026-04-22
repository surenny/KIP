from plasTeX import Environment
from plasTeX.Base.LaTeX.Math import MathEnvironment


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
