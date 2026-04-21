"""
Package Lean blueprint

This depends on the depgraph plugin. This plugin has to be installed but then it is
used automatically.

Options:
* project: lean project path

* showmore: enable buttons showing or hiding proofs (this requires the showmore plugin).

You can also add options that will be passed to the dependency graph package.
"""
import hashlib
import json
import re
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


# Lean declaration keywords that start a top-level declaration
_LEAN_DECL_KW = re.compile(
    r'^(noncomputable\s+)?(protected\s+)?(private\s+)?'
    r'(def|theorem|lemma|axiom|abbrev|structure|class|instance|inductive)\s+'
)


def _extract_lean_source(lean_root: Path, decl_name: str, max_lines: int = 40) -> str:
    """
    Search .lean files under lean_root for a declaration matching decl_name.
    Returns the source text of the declaration block, or '' if not found.
    """
    # The short name is the last component: KIP.SpectralSequence.SSData → SSData
    short_name = decl_name.rsplit('.', 1)[-1]
    for lean_file in sorted(lean_root.rglob('*.lean')):
        try:
            lines = lean_file.read_text(encoding='utf-8').splitlines()
        except Exception:
            continue
        for i, line in enumerate(lines):
            # Check if this line declares our target
            stripped = line.lstrip()
            if not _LEAN_DECL_KW.match(stripped):
                continue
            # Check if short_name appears right after the keyword
            if short_name not in stripped:
                continue
            # More precise: after the keyword, the name should match
            m = _LEAN_DECL_KW.match(stripped)
            rest = stripped[m.end():]
            declared = rest.split()[0].split('(')[0].split('{')[0].split(':')[0].split('[')[0].rstrip()
            # Match: exact short_name, or declared is a suffix of the full decl_name
            # e.g. decl_name="KIP.SS.SSData.eInfty", declared="SSData.eInfty" → match
            #      decl_name="KIP.SS.SSData", declared="SSData" → match
            declared_short = declared.rsplit('.', 1)[-1]
            if declared != short_name and declared_short != short_name and \
               not decl_name.endswith('.' + declared) and declared != decl_name:
                continue
            # Found it — extract the block
            block = [lines[i]]
            indent = len(line) - len(line.lstrip())
            for j in range(i + 1, min(i + max_lines, len(lines))):
                l = lines[j]
                if l.strip() == '':
                    block.append(l)
                    continue
                cur_indent = len(l) - len(l.lstrip())
                # Stop at next top-level declaration or dedent
                if cur_indent <= indent and l.strip() and _LEAN_DECL_KW.match(l.strip()):
                    break
                # Stop at blank line followed by top-level code
                if cur_indent <= indent and l.strip() and not l.strip().startswith('--'):
                    # Check if it looks like continuation (e.g. `where`, `|`, `:=`)
                    if not any(l.strip().startswith(kw) for kw in ('where', '|', ':=', '·', '⟨', '⟩', 'with')):
                        break
                block.append(l)
            # Trim trailing blank lines
            while block and not block[-1].strip():
                block.pop()
            return '\n'.join(block)
    return ''


def _truncate_proof(source: str) -> str:
    """
    For theorems/lemmas, replace the tactic proof body after `by` with `...`.
    Keeps the full type signature (statement) but hides proof tactics.
    Handles: `:= by\\n  tactics`, `:= by tactic`, and term-mode `:= expr`.
    """
    lines = source.splitlines()
    result = []
    for i, line in enumerate(lines):
        stripped = line.rstrip()
        # Pattern 1: line ends with `:= by` (proof starts on next line)
        if re.search(r':=\s+by\s*$', stripped):
            result.append(stripped)
            pad = '  ' * (1 + (len(line) - len(line.lstrip())) // 2)
            result.append(pad + '...')
            return '\n'.join(result)
        # Pattern 2: `:= by <tactic>` on the same line
        m = re.search(r':=\s+by\s+\S', stripped)
        if m:
            result.append(stripped[:m.start()] + ':= by ...')
            return '\n'.join(result)
        # Pattern 3: standalone `by` on its own line (after type signature)
        if stripped.strip() == 'by':
            result.append(stripped)
            pad = '  ' * (1 + (len(line) - len(line.lstrip())) // 2)
            result.append(pad + '...')
            return '\n'.join(result)
        result.append(line)
    return source

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
  {% set kind = st.get('kind', '') -%}
  {% set is_thm = kind not in ('definition', 'axiom') -%}
  {#- Determine current stage index -#}
  {%- if st.get('proved') and is_thm -%}{% set cur = 4 -%}
  {%- elif st.get('aligned') -%}{% set cur = 3 -%}
  {%- elif st.get('bound') -%}{% set cur = 2 -%}
  {%- elif st.get('nl_reviewed') -%}{% set cur = 1 -%}
  {%- else -%}{% set cur = 0 -%}{%- endif -%}
  {#- Build stage list depending on node kind -#}
  {%- if is_thm -%}
    {%- set stages = [
      (0, 'draft',    'Draft',    '#999'),
      (1, 'reviewed', 'Reviewed', '#E69F00'),
      (2, 'bound',    'Bound',    '#0072B2'),
      (3, 'aligned',  'Aligned',  '#009E73'),
      (4, 'proved',   'Proved',   '#1CAC78')
    ] -%}
  {%- else -%}
    {%- set stages = [
      (0, 'draft',    'Draft',    '#999'),
      (1, 'reviewed', 'Reviewed', '#E69F00'),
      (2, 'bound',    'Bound',    '#0072B2'),
      (3, 'aligned',  'Aligned',  '#009E73')
    ] -%}
  {%- endif -%}
  <div class="ext-status-badges" data-node-id="{{ thm.id }}" style="margin-top:6px;display:flex;flex-wrap:wrap;gap:0;align-items:center;font-size:0.8em;">
    {%- for idx, key, label, color in stages -%}
      {%- if idx > 0 -%}<span style="color:#bbb;margin:0 3px;">&rarr;</span>{%- endif -%}
      {%- if idx == cur -%}
      <span class="badge badge-{{ key }}" style="background:{{ color }};color:{% if color in ('#9CEC8B','#D4EFDF') %}#333{% else %}#fff{% endif %};padding:2px 6px;border-radius:3px;">{{ label }}</span>
      {%- elif idx < cur -%}
      <span style="color:#333;font-weight:500;">{{ label }}</span>
      {%- else -%}
      <span style="color:#ccc;">{{ label }}</span>
      {%- endif -%}
    {%- endfor -%}
    {%- if st.get('reclassify') -%}
    {%- set rc = st['reclassify'] -%}
    {%- if rc == 'definition' -%}{%- set rc_label = '&#9633; definition' -%}
    {%- elif rc == 'theorem' -%}{%- set rc_label = '&#9675; theorem' -%}
    {%- elif rc == 'axiom' -%}{%- set rc_label = '&#9671; axiom' -%}
    {%- else -%}{%- set rc_label = rc -%}{%- endif -%}
    <span style="color:#bbb;margin:0 3px;">|</span>
    <span class="badge badge-reclassify" style="background:#CC79A7;color:#fff;padding:2px 6px;border-radius:3px;">Reclassify &rarr; {{ rc_label }}{% if st.get('reclassify_by') %} ({{ st['reclassify_by'] }}){% endif %}</span>
    {%- endif -%}
  </div>
  {%- if st.get('comments') -%}
  <div class="ext-review-comments" style="margin-top:4px;">
    {%- for c in st['comments'] -%}
    {%- set topic_colors = {'review':'#E69F00','align':'#009E73','verify':'#1CAC78','general':'#666'} -%}
    {%- set tc = topic_colors.get(c.get('topic','general'), '#666') -%}
    <div style="padding:3px 8px;background:#FAFAFA;border-left:3px solid {{ tc }};font-size:0.82em;margin-bottom:2px;">
      <span style="color:{{ tc }};font-weight:bold;font-size:0.85em;">{{ c.get('topic','general')|e }}</span>
      {{ c['text']|e }}
      <span style="color:#999;font-size:0.9em;"> — {{ c.get('by','?')|e }}{% if c.get('at') %}, {{ c['at']|e }}{% endif %}</span>
    </div>
    {%- endfor -%}
  </div>
  {%- endif -%}
  {%- if st.get('nl_review_comment') -%}
  <div class="ext-review-comment" style="margin-top:4px;padding:4px 8px;background:#FFF8E1;border-left:3px solid #E69F00;font-size:0.85em;">
    {{ st['nl_review_comment']|e }}
    {%- if st.get('nl_review_comment_by') %} <span style="color:#999;">-- {{ st['nl_review_comment_by']|e }}{% if st.get('nl_review_comment_at') %}, {{ st['nl_review_comment_at']|e }}{% endif %}</span>{% endif -%}
  </div>
  {%- endif -%}
  <div class="review-panel" data-node-id="{{ thm.id }}" style="margin-top:8px;padding:8px;background:#f8f9fa;border:1px solid #dee2e6;border-radius:4px;font-size:0.85em;">
    <div style="display:flex;flex-wrap:wrap;gap:4px;margin-bottom:6px;">
      {%- if not st.get('nl_reviewed') -%}
      <button class="review-btn" data-action="review" style="background:#E69F00;color:#fff;border:none;padding:3px 8px;border-radius:3px;cursor:pointer;font-size:0.85em;">Approve NL</button>
      {%- endif -%}
      {%- if st.get('bound') and not st.get('aligned') -%}
      <button class="review-btn" data-action="align" style="background:#009E73;color:#fff;border:none;padding:3px 8px;border-radius:3px;cursor:pointer;font-size:0.85em;">Confirm Alignment</button>
      {%- endif -%}
      {%- if st.get('kind') == 'definition' and st.get('aligned') -%}
      <span style="color:#009E73;font-size:0.8em;font-weight:bold;">Complete (definition)</span>
      {%- elif st.get('kind') == 'axiom' and st.get('aligned') -%}
      <span style="color:#CC79A7;font-size:0.8em;font-weight:bold;">Complete (axiom — no proof needed)</span>
      {%- elif st.get('kind') not in ('definition', 'axiom') and st.get('proved') -%}
      <span style="color:#1CAC78;font-size:0.8em;font-weight:bold;">Complete (proved)</span>
      {%- endif -%}
    </div>
    <div style="display:flex;gap:4px;align-items:stretch;">
      <select class="review-comment-topic" style="padding:3px 4px;border:1px solid #ccc;border-radius:3px;font-size:0.85em;">
        <option value="general">general</option>
        <option value="review">NL review</option>
        <option value="align">alignment</option>
      </select>
      <input type="text" class="review-comment-input" placeholder="Comment or suggestion..." style="flex:1;padding:3px 6px;border:1px solid #ccc;border-radius:3px;font-size:0.85em;" />
      <button class="review-btn" data-action="comment" style="background:#666;color:#fff;border:none;padding:3px 8px;border-radius:3px;cursor:pointer;font-size:0.85em;">Send</button>
    </div>
    <div style="margin-top:4px;display:flex;gap:4px;align-items:center;">
      {%- set kind = st.get('kind', 'unknown') -%}
      {%- if kind in ('theorem', 'lemma', 'proposition', 'corollary') -%}
        {%- set kind_label = 'theorem &#9675;' -%}
      {%- elif kind == 'definition' -%}
        {%- set kind_label = 'definition &#9633;' -%}
      {%- elif kind == 'axiom' -%}
        {%- set kind_label = 'axiom &#9671;' -%}
      {%- else -%}
        {%- set kind_label = kind -%}
      {%- endif -%}
      <span style="font-size:0.8em;color:#555;">Type: <b>{{ kind_label }}</b></span>
      <select class="review-reclassify-select" style="padding:2px 4px;border:1px solid #ccc;border-radius:3px;font-size:0.85em;">
        <option value="">Reclassify to...</option>
        <option value="definition" {% if kind == 'definition' %}disabled{% endif %}>&#9633; definition</option>
        <option value="theorem" {% if kind in ('theorem', 'lemma', 'proposition', 'corollary') %}disabled{% endif %}>&#9675; theorem</option>
        <option value="axiom" {% if kind == 'axiom' %}disabled{% endif %}>&#9671; axiom</option>
      </select>
      <button class="review-btn" data-action="reclassify" style="background:#CC79A7;color:#fff;border:none;padding:3px 8px;border-radius:3px;cursor:pointer;font-size:0.85em;">Suggest</button>
    </div>
    <div style="margin-top:4px;">
      <label style="font-size:0.8em;color:#666;">Reviewer:
        <input type="text" class="review-reviewer-input" placeholder="your name" style="padding:2px 4px;border:1px solid #ccc;border-radius:3px;font-size:0.85em;width:120px;" />
      </label>
    </div>
    <div class="review-feedback" style="margin-top:4px;font-size:0.8em;color:#666;"></div>
  </div>
  {%- endif -%}
""")

LEAN_SOURCE_TPL = Template("""
  {%- if thm.userdata.get('lean_source') -%}
  <div class="lean-source-panel" style="margin-top:6px;">
    <button class="lean-source-toggle" style="background:none;border:1px solid #999;padding:2px 8px;border-radius:3px;cursor:pointer;font-size:0.8em;color:#555;">
      Lean ▸
    </button>
    <pre class="lean-source-code" style="display:none;margin-top:4px;padding:10px 12px;background:#1e1e2e;color:#cdd6f4;border-radius:6px;font-size:0.82em;overflow-x:auto;line-height:1.5;tab-size:2;"><code class="language-lean4">{{ thm.userdata['lean_source'] }}</code></pre>
  </div>
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
        MATHLIB_DOCHOME = 'https://leanprover-community.github.io/mathlib4_docs'
        project_dochome = document.userdata.get('project_dochome', MATHLIB_DOCHOME)

        status_nodes = _load_status_yaml()
        use_extended_states = bool(status_nodes)

        # Locate Lean project root for source extraction
        working_dir = Path(document.userdata['working-dir']).resolve()
        lean_root = working_dir.parent.parent  # blueprint/src → blueprint → project root

        # Detect project-local Lean library names from lean_lib sections in lakefile
        _project_prefixes = set()
        for lakefile_name in ('lakefile.toml', 'lakefile.lean'):
            lakefile = lean_root / lakefile_name
            if lakefile.exists():
                try:
                    text = lakefile.read_text(encoding='utf-8')
                    if lakefile_name.endswith('.toml'):
                        for m in re.finditer(r'\[\[lean_lib\]\]\s*\n\s*name\s*=\s*"([^"]+)"', text):
                            _project_prefixes.add(m.group(1))
                    else:
                        for m in re.finditer(r'lean_lib\s+(\S+)', text):
                            _project_prefixes.add(m.group(1))
                except Exception:
                    pass
        if not _project_prefixes:
            _project_prefixes = set()

        def _lean_decl_url(decl: str) -> str:
            """Return the doc URL for a Lean declaration, using the mathlib
            doc host for declarations outside the project's own libraries."""
            if project_dochome != MATHLIB_DOCHOME and _project_prefixes and \
               not any(decl == p or decl.startswith(p + '.') for p in _project_prefixes):
                return f'{MATHLIB_DOCHOME}/find/#doc/{decl}'
            return f'{project_dochome}/find/#doc/{decl}'

        # Cache: avoid re-searching the same declaration
        _lean_source_cache = {}

        for graph in document.userdata['dep_graph']['graphs'].values():
            nodes = graph.nodes
            for node in nodes:
                leandecls = node.userdata.get('leandecls', [])
                lean_urls = []
                for leandecl in leandecls:
                    lean_urls.append((leandecl, _lean_decl_url(leandecl)))

                node.userdata['lean_urls'] = lean_urls

                # Extract Lean source for inline display
                if leandecls:
                    kind = item_kind(node)
                    truncate = kind in ('theorem', 'lemma', 'proposition', 'corollary')
                    sources = []
                    for decl in leandecls:
                        cache_key = (decl, truncate)
                        if cache_key not in _lean_source_cache:
                            src = _extract_lean_source(lean_root, decl)
                            if src and truncate:
                                src = _truncate_proof(src)
                            _lean_source_cache[cache_key] = src
                        src = _lean_source_cache[cache_key]
                        if src:
                            sources.append(src)
                    node.userdata['lean_source'] = '\n\n'.join(sources) if sources else ''

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
                    kind = item_kind(node)
                    st['kind'] = kind
                    has_lean_binding = bool(leandecls)
                    st['bound'] = has_lean_binding

                    # NL content change detection: hash textContent,
                    # reset human review gates if content changed.
                    # Skip anonymous nodes (plasTeX auto-ids like a0000000001)
                    # whose textContent is not stable across builds.
                    is_anonymous = node_id.startswith('a') and node_id[1:].isdigit()
                    if not is_anonymous:
                        nl_text = node.textContent.strip()
                        nl_hash = hashlib.sha256(nl_text.encode()).hexdigest()[:16]
                        old_hash = st.get('nl_hash')
                        if old_hash is not None and old_hash != nl_hash:
                            st['nl_reviewed'] = False
                            st['aligned'] = False
                            st.pop('nl_reviewed_by', None)
                            st.pop('nl_reviewed_at', None)
                            st.pop('aligned_by', None)
                            st.pop('aligned_at', None)
                            log.info(f'NL content changed for {node_id}, resetting review status')
                        st['nl_hash'] = nl_hash

                    if kind == 'definition':
                        st['proved'] = False
                    elif kind == 'axiom':
                        st['proved'] = False
                    else:
                        is_proved = node.userdata.get('proved', False)
                        if is_proved:
                            st['proved'] = True
                    # Monotonic auto-derive (only for machine-derivable gates):
                    #   bound → nl_reviewed  (having Lean binding implies NL was seen)
                    # aligned is NEVER auto-promoted — it requires human confirmation
                    # proved → aligned is NOT automatic
                    if st.get('bound'):
                        st['nl_reviewed'] = True
                    node.userdata['ext_status'] = st
                    status_nodes[node_id] = st

            for node in nodes:
                node.userdata['fully_proved'] = all(n.userdata.get('proved', False) or item_kind(
                    n) == 'definition' for n in graph.ancestors(node).union({node}))

        if use_extended_states:
            _save_status_yaml(status_nodes)
            document.userdata['dep_graph']['status_nodes_json'] = json.dumps(
                status_nodes, ensure_ascii=False, default=str)

        lean_decls_path = Path(document.userdata['working-dir']).parent/"lean_decls"
        lean_decls_path.write_text("\n".join(document.userdata.get("lean_decls", [])))

    document.addPostParseCallbacks(150, make_lean_data)

    document.addPackageResource([PackageCss(path=STATIC_DIR/'blueprint.css')])

    colors = document.userdata['dep_graph']['colors'] = {
        'draft':       ('#999999', 'Gray'),
        'reviewed':    ('#E69F00', 'Orange'),
        'bound':       ('#0072B2', 'Blue'),
        'aligned':     ('#009E73', 'Green'),
        'proved':      ('#1CAC78', 'Dark green'),
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
            if ext.get('proved'):
                return colors['proved'][0]
            if ext.get('aligned'):
                return colors['aligned'][0]
            if ext.get('bound'):
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
            if ext.get('proved'):
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
                (f"<span style='color:{colors['draft'][0]}'>■</span> Draft",
                 "AI-generated, not yet reviewed"),
                (f"<span style='color:{colors['reviewed'][0]}'>■</span> Reviewed",
                 "human confirmed NL content"),
                (f"<span style='color:{colors['bound'][0]}'>■</span> Bound",
                 "has <code>\\lean{{}}</code> binding to Lean declaration"),
                (f"<span style='display:inline-block;width:12px;height:12px;border:2px solid {colors['aligned'][0]};background:{colors['aligned_fill'][0]}'></span> Aligned",
                 "human confirmed NL↔Lean semantic match"),
                (f"<span style='display:inline-block;width:12px;height:12px;border:2px solid {colors['proved'][0]};background:{colors['proved'][0]}'></span> Proved",
                 "Lean proof compiled (theorems only)"),
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
        LEAN_LINKS_TPL, LEAN_SOURCE_TPL, GITHUB_LINK_TPL, STATUS_BADGES_TPL])
