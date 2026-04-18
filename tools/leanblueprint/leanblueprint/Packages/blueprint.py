"""
Package Lean blueprint

This depends on the depgraph plugin. This plugin has to be installed but then it is
used automatically.

Options:
* project: lean project path

* showmore: enable buttons showing or hiding proofs (this requires the showmore plugin).

You can also add options that will be passed to the dependency graph package.
"""
import string
from datetime import datetime
from pathlib import Path

import yaml
from jinja2 import Template
from plasTeX import Command
from plasTeX.Logging import getLogger
from plasTeX.PackageResource import PackageCss, PackageTemplateDir
from plastexdepgraph.Packages.depgraph import item_kind

log = getLogger()

PKG_DIR = Path(__file__).parent
STATIC_DIR = Path(__file__).parent.parent/'static'


class home(Command):
    r"""\home{url}"""
    args = 'url:url'

    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['project_home'] = self.attributes['url']
        return []


class github(Command):
    r"""\github{url}"""
    args = 'url:url'

    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['project_github'] = self.attributes['url'].textContent.rstrip(
            '/')
        return []


class dochome(Command):
    r"""\dochome{url}"""
    args = 'url:url'

    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['project_dochome'] = self.attributes['url'].textContent
        return []


class graphcolor(Command):
    r"""\graphcolor{node_type}{color}{color_descr}"""
    args = 'node_type:str color:str color_descr:str'

    def digest(self, tokens):
        Command.digest(self, tokens)
        attrs = self.attributes
        colors = self.ownerDocument.userdata['dep_graph']['colors']
        node_type = attrs['node_type']
        if node_type not in colors:
            log.warning(f'Unknown node type {node_type}')
        colors[node_type] = (attrs['color'].strip(), attrs['color_descr'].strip())


class leanok(Command):
    r"""\leanok"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.userdata['leanok'] = True


class notready(Command):
    r"""\notready"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.userdata['notready'] = True


class mathlibok(Command):
    r"""\mathlibok"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.userdata['leanok'] = True
        self.parentNode.userdata['mathlibok'] = True


class lean(Command):
    r"""\lean{decl list} """
    args = 'decls:list:nox'

    def digest(self, tokens):
        Command.digest(self, tokens)
        decls = [dec.strip() for dec in self.attributes['decls']]
        self.parentNode.setUserData('leandecls', decls)
        all_decls = self.ownerDocument.userdata.setdefault('lean_decls', [])
        all_decls.extend(decls)


class discussion(Command):
    r"""\discussion{issue_number} """
    args = 'issue:str'

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.setUserData(
            'issue', self.attributes['issue'].lstrip('#').strip())


CHECKMARK_TPL = Template("""
    {% if obj.userdata.leanok and ('proved_by' not in obj.userdata or obj.userdata.proved_by.userdata.leanok ) %}
    ✓
    {% endif %}
""")

LEAN_DECLS_TPL = Template("""
    {% if obj.userdata.leandecls %}
    <button class="modal lean">L∃∀N</button>
    {% call modal('Lean declarations') %}
        <ul class="uses">
          {% for lean, url in obj.userdata.lean_urls %}
          <li><a href="{{ url }}" class="lean_decl">{{ lean }}</a></li>
          {% endfor %}
        </ul>
    {% endcall %}
    {% endif %}
""")

GITHUB_ISSUE_TPL = Template("""
    {% if obj.userdata.issue %}
    <a class="github_link" href="{{ obj.ownerDocument.userdata.project_github }}/issues/{{ obj.userdata.issue }}">Discussion</a>
    {% endif %}
""")

LEAN_LINKS_TPL = Template("""
  {% if thm.userdata['lean_urls'] -%}
    {%- if thm.userdata['lean_urls']|length > 1 -%}
  <div class="tooltip">
      <span class="lean_link">Lean</span>
      <ul class="tooltip_list">
        {% for name, url in thm.userdata['lean_urls'] %}
           <li><a href="{{ url }}" class="lean_decl">{{ name }}</a></li>
        {% endfor %}
      </ul>
  </div>
    {%- else -%}
    <a class="lean_link lean_decl" href="{{ thm.userdata['lean_urls'][0][1] }}">Lean</a>
    {%- endif -%}
    {%- endif -%}
""")

GITHUB_LINK_TPL = Template("""
  {% if thm.userdata['issue'] -%}
  <a class="issue_link" href="{{ document.userdata['project_github'] }}/issues/{{ thm.userdata['issue'] }}">Discussion</a>
  {%- endif -%}
""")

STATUS_BADGES_TPL = Template("""
  {% if thm.userdata.get('ext_status') -%}
  {% set st = thm.userdata['ext_status'] -%}
  <div class="ext-status-badges" style="margin-top:6px;display:flex;flex-wrap:wrap;gap:4px;">
    {%- if st.get('verified') -%}
    <span class="badge" style="background:#1CAC78;color:#fff;padding:2px 6px;border-radius:3px;font-size:0.8em;">Verified{% if st.get('verify_reviewer') %} by {{ st['verify_reviewer'] }}{% endif %}</span>
    {%- elif st.get('proved') -%}
    <span class="badge" style="background:#9CEC8B;color:#333;padding:2px 6px;border-radius:3px;font-size:0.8em;">Proved</span>
    <span class="badge needs-review" style="background:#eee;color:#666;padding:2px 6px;border-radius:3px;font-size:0.8em;">Needs verification</span>
    {%- elif st.get('aligned') -%}
    <span class="badge" style="background:#D4EFDF;color:#333;padding:2px 6px;border-radius:3px;font-size:0.8em;">Aligned{% if st.get('align_reviewer') %} by {{ st['align_reviewer'] }}{% endif %}</span>
    <span class="badge needs-review" style="background:#eee;color:#666;padding:2px 6px;border-radius:3px;font-size:0.8em;">Needs proof</span>
    {%- elif st.get('bound') -%}
    <span class="badge" style="background:#0072B2;color:#fff;padding:2px 6px;border-radius:3px;font-size:0.8em;">Bound</span>
    <span class="badge needs-review" style="background:#eee;color:#666;padding:2px 6px;border-radius:3px;font-size:0.8em;">Needs alignment review</span>
    {%- elif st.get('nl_reviewed') -%}
    <span class="badge" style="background:#E69F00;color:#fff;padding:2px 6px;border-radius:3px;font-size:0.8em;">NL Reviewed{% if st.get('nl_reviewer') %} by {{ st['nl_reviewer'] }}{% endif %}</span>
    {%- else -%}
    <span class="badge" style="background:#999;color:#fff;padding:2px 6px;border-radius:3px;font-size:0.8em;">Draft</span>
    <span class="badge needs-review" style="background:#eee;color:#666;padding:2px 6px;border-radius:3px;font-size:0.8em;">Needs NL review</span>
    {%- endif -%}
    {%- if st.get('reclassify') -%}
    <span class="badge" style="background:#CC79A7;color:#fff;padding:2px 6px;border-radius:3px;font-size:0.8em;">⚠ Reclassify → {{ st['reclassify'] }}{% if st.get('reclassify_by') %} ({{ st['reclassify_by'] }}){% endif %}</span>
    {%- endif -%}
  </div>
  {%- if st.get('nl_review_comment') -%}
  <div class="ext-review-comment" style="margin-top:4px;padding:4px 8px;background:#FFF8E1;border-left:3px solid #E69F00;font-size:0.85em;">
    💬 {{ st['nl_review_comment'] }}
    {%- if st.get('nl_review_comment_by') %} <span style="color:#999;">— {{ st['nl_review_comment_by'] }}{% if st.get('nl_review_comment_at') %}, {{ st['nl_review_comment_at'] }}{% endif %}</span>{% endif -%}
  </div>
  {%- endif -%}
  {%- endif -%}
""")


def ProcessOptions(options, document):
    """This is called when the package is loaded."""

    # We want to ensure the depgraph and showmore packages are loaded.
    # We first need to make sure the corresponding plugins are used.
    # This is a bit hacky but needed for backward compatibility with
    # project who used the blueprint package before the depgraph one was
    # split.
    plugins = document.config['general'].data['plugins'].value
    if 'plastexdepgraph' not in plugins:
        plugins.append('plastexdepgraph')
    # And now load the package.
    document.context.loadPythonPackage(document, 'depgraph', options)
    if 'showmore' in options:
        if 'plastexshowmore' not in plugins:
            plugins.append('plastexshowmore')
        # And now load the package.
        document.context.loadPythonPackage(document, 'showmore', {})

    templatedir = PackageTemplateDir(path=PKG_DIR/'renderer_templates')
    document.addPackageResource(templatedir)

    jobname = document.userdata['jobname']
    outdir = document.config['files']['directory']
    outdir = string.Template(outdir).substitute({'jobname': jobname})

    def _load_status_yaml() -> dict:
        """Load blueprint/status.yaml, returning the 'nodes' dict (or empty)."""
        working_dir = Path(document.userdata['working-dir'])
        status_path = working_dir.parent / "status.yaml"
        if not status_path.exists():
            return {}
        try:
            with status_path.open() as f:
                data = yaml.safe_load(f) or {}
            return data.get('nodes', {})
        except Exception as exc:
            log.warning(f'Could not load status.yaml: {exc}')
            return {}

    def _save_status_yaml(status_nodes: dict) -> None:
        """Write back auto-derived fields to status.yaml."""
        working_dir = Path(document.userdata['working-dir'])
        status_path = working_dir.parent / "status.yaml"
        try:
            with status_path.open() as f:
                data = yaml.safe_load(f) or {}
        except Exception:
            data = {}
        data.setdefault('nodes', {}).update(status_nodes)
        with status_path.open('w') as f:
            yaml.dump(data, f, default_flow_style=False, sort_keys=False, allow_unicode=True)

    def make_lean_data() -> None:
        """
        Build url and formalization status for nodes in the dependency graphs.
        Loads status.yaml for the 6-state lifecycle, auto-derives bound/proved,
        and writes back updated auto-derived fields.
        Also create the file lean_decls of all Lean names referred to in the blueprint.
        """
        project_dochome = document.userdata.get('project_dochome',
                                                'https://leanprover-community.github.io/mathlib4_docs')

        status_nodes = _load_status_yaml()
        use_extended_states = bool(status_nodes)

        for graph in document.userdata['dep_graph']['graphs'].values():
            nodes = graph.nodes
            for node in nodes:
                leandecls = node.userdata.get('leandecls', [])
                lean_urls = []
                for leandecl in leandecls:
                    lean_urls.append(
                        (leandecl,
                         f'{project_dochome}/find/#doc/{leandecl}'))

                node.userdata['lean_urls'] = lean_urls

                used = node.userdata.get('uses', [])
                node.userdata['can_state'] = all(thm.userdata.get('leanok')
                                                 for thm in used) and not node.userdata.get('notready', False)
                proof = node.userdata.get('proved_by')
                if proof:
                    used.extend(proof.userdata.get('uses', []))
                    node.userdata['can_prove'] = all(thm.userdata.get('leanok')
                                                     for thm in used)
                    node.userdata['proved'] = proof.userdata.get(
                        'leanok', False)
                else:
                    node.userdata['can_prove'] = False
                    node.userdata['proved'] = False

                if use_extended_states:
                    node_id = node.id
                    st = status_nodes.get(node_id, {})
                    has_lean_binding = bool(leandecls)
                    st['bound'] = has_lean_binding
                    is_proved = node.userdata.get('proved', False)
                    if is_proved:
                        st['proved'] = True
                    # Enforce monotonic cumulative: proved → aligned → bound → reviewed
                    if st.get('proved'):
                        st['aligned'] = True
                    if st.get('aligned'):
                        st['bound'] = True
                    if st.get('bound'):
                        st['nl_reviewed'] = True
                    node.userdata['ext_status'] = st
                    status_nodes[node_id] = st

            for node in nodes:
                node.userdata['fully_proved'] = all(n.userdata.get('proved', False) or item_kind(
                    n) == 'definition' for n in graph.ancestors(node).union({node}))

        if use_extended_states:
            _save_status_yaml(status_nodes)

        lean_decls_path = Path(document.userdata['working-dir']).parent/"lean_decls"
        lean_decls_path.write_text("\n".join(document.userdata.get("lean_decls", [])))

    document.addPostParseCallbacks(150, make_lean_data)

    document.addPackageResource([PackageCss(path=STATIC_DIR/'blueprint.css')])

    colors = document.userdata['dep_graph']['colors'] = {
        'draft':       ('#999999', 'Gray'),
        'reviewed':    ('#E69F00', 'Orange'),
        'bound':       ('#0072B2', 'Blue'),
        'aligned':     ('#009E73', 'Green'),
        'proved':      ('#9CEC8B', 'Light green'),
        'verified':    ('#1CAC78', 'Dark green'),
        'aligned_fill': ('#D4EFDF', 'Light green'),
        # Legacy keys kept for backward compat with \graphcolor
        'mathlib':     ('darkgreen', 'Dark green'),
        'stated':      ('green', 'Green'),
        'can_state':   ('blue', 'Blue'),
        'not_ready':   ('#FFAA33', 'Orange'),
        'can_prove':   ('#A3D6FF', 'Blue'),
        'defined':     ('#B0ECA3', 'Light green'),
        'fully_proved': ('#1CAC78', 'Dark green')
    }

    document.userdata['dep_graph']['shapes'] = {
        'definition': 'box',
        'axiom': 'diamond',
    }

    def _has_status_yaml() -> bool:
        working_dir = Path(document.userdata.get('working-dir', '.'))
        return (working_dir.parent / "status.yaml").exists()

    def colorizer(node) -> str:
        data = node.userdata
        ext = data.get('ext_status')

        if ext:
            if ext.get('verified'):
                return colors['aligned'][0]
            if ext.get('proved') or data.get('proved'):
                return colors['aligned'][0]
            if ext.get('aligned'):
                return colors['aligned'][0]
            if ext.get('bound') or data.get('leandecls'):
                return colors['bound'][0]
            if ext.get('nl_reviewed'):
                return colors['reviewed'][0]
            return colors['draft'][0]

        # Fallback: original leanblueprint logic
        color = ''
        if data.get('mathlibok'):
            color = colors['mathlib'][0]
        elif data.get('leanok'):
            color = colors['stated'][0]
        elif data.get('can_state'):
            color = colors['can_state'][0]
        elif data.get('notready'):
            color = colors['not_ready'][0]
        return color

    def fillcolorizer(node) -> str:
        data = node.userdata
        ext = data.get('ext_status')

        if ext:
            if ext.get('verified'):
                return colors['verified'][0]
            if ext.get('proved') or data.get('proved'):
                return colors['proved'][0]
            if ext.get('aligned'):
                return colors['aligned_fill'][0]
            return ''

        # Fallback: original leanblueprint logic
        stated = data.get('leanok')
        can_state = data.get('can_state')
        can_prove = data.get('can_prove')
        proved = data.get('proved')
        fully_proved = data.get('fully_proved')

        fillcolor = ''
        if proved:
            fillcolor = colors['proved'][0]
        elif can_prove and (can_state or stated):
            fillcolor = colors['can_prove'][0]
        if item_kind(node) == 'definition':
            if stated:
                fillcolor = colors['defined'][0]
            elif can_state:
                fillcolor = colors['can_prove'][0]
        elif fully_proved:
            fillcolor = colors['fully_proved'][0]
        return fillcolor

    document.userdata['dep_graph']['colorizer'] = colorizer
    document.userdata['dep_graph']['fillcolorizer'] = fillcolorizer

    def make_legend() -> None:
        """
        Extend the dependency graph legend defined by the depgraph plugin
        by adding information specific to Lean blueprints. This is registered
        as a post-parse callback to allow users to redefine colors and their
        descriptions.
        """
        legend = document.userdata['dep_graph']['legend']
        # Replace default shape legend with 3-shape version
        legend.clear()
        legend.extend([
            ('Boxes (□)', 'definitions'),
            ('Ellipses (○)', 'theorems and lemmas'),
            ('Diamonds (◇)', 'axioms — unformalized external results'),
        ])
        if _has_status_yaml():
            legend.extend([
                (f"<span style='color:{colors['draft'][0]}'>■</span> {colors['draft'][1]} border",
                 "AI-generated, unreviewed"),
                (f"<span style='color:{colors['reviewed'][0]}'>■</span> {colors['reviewed'][1]} border",
                 "human confirmed NL content"),
                (f"<span style='color:{colors['bound'][0]}'>■</span> {colors['bound'][1]} border",
                 "has <code>\\lean{{}}</code> binding"),
                (f"<span style='color:{colors['aligned'][0]}'>■</span> {colors['aligned'][1]} border",
                 "human confirmed NL↔Lean match"),
                (f"<span style='color:{colors['aligned_fill'][0]}; background:{colors['aligned_fill'][0]}'>■</span> {colors['aligned_fill'][1]} background",
                 "aligned — NL↔Lean binding confirmed"),
                (f"<span style='color:{colors['proved'][0]}; background:{colors['proved'][0]}'>■</span> {colors['proved'][1]} background",
                 "Lean proof exists"),
                (f"<span style='color:{colors['verified'][0]}; background:{colors['verified'][0]}'>■</span> {colors['verified'][1]} background",
                 "human reviewed proof quality"),
            ])
        else:
            legend.extend([
                (f"{colors['can_state'][1]} border",
                 "the <em>statement</em> of this result is ready to be formalized; all prerequisites are done"),
                (f"{colors['not_ready'][1]} border",
                    "the <em>statement</em> of this result is not ready to be formalized; the blueprint needs more work"),
                (f"{colors['can_state'][1]} background",
                    "the <em>proof</em> of this result is ready to be formalized; all prerequisites are done"),
                (f"{colors['proved'][1]} border",
                    "the <em>statement</em> of this result is formalized"),
                (f"{colors['proved'][1]} background",
                    "the <em>proof</em> of this result is formalized"),
                (f"{colors['fully_proved'][1]} background",
                    "the <em>proof</em> of this result and all its ancestors are formalized"),
                (f"{colors['mathlib'][1]} border",
                    "this is in Mathlib"),
            ])

    document.addPostParseCallbacks(150, make_legend)

    document.userdata.setdefault(
        'thm_header_extras_tpl', []).extend([CHECKMARK_TPL])
    document.userdata.setdefault('thm_header_hidden_extras_tpl', []).extend([LEAN_DECLS_TPL,
                                                                             GITHUB_ISSUE_TPL])
    document.userdata['dep_graph'].setdefault('extra_modal_links_tpl', []).extend([
        LEAN_LINKS_TPL, GITHUB_LINK_TPL, STATUS_BADGES_TPL])
