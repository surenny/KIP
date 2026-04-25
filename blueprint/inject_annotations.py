#!/usr/bin/env python3
"""Inject exported browser annotations into LaTeX source as margin notes.

Usage:
    python3 inject_annotations.py [annotations.json] [--output-dir DIR]

Reads a JSON file exported from the blueprint annotation system and injects
\\marginpar notes after the corresponding \\label{} commands in the .tex
source files under blueprint/src/chapters/.

Only annotations whose element-id matches a LaTeX label are injected;
paragraph-level annotations (containing '--p') are skipped since they have
no stable LaTeX anchor.
"""

import json
import sys
import os
import re
import glob
import shutil
from datetime import datetime

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
CHAPTERS_DIR = os.path.join(SCRIPT_DIR, 'src', 'chapters')
BACKUP_SUFFIX = '.bak-annotations'


def load_annotations(path):
    with open(path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    return data.get('annotations', {})


def format_comment_latex(comments):
    """Format a list of comments as a LaTeX marginnote."""
    parts = []
    for c in comments:
        author = c.get('author', 'Anonymous')
        text = c.get('text', '')
        resolved = c.get('resolved', False)
        prefix = '[Resolved] ' if resolved else ''
        safe_text = text.replace('\\', '\\textbackslash{}')
        safe_text = safe_text.replace('{', '\\{').replace('}', '\\}')
        safe_text = safe_text.replace('#', '\\#').replace('&', '\\&')
        safe_text = safe_text.replace('%', '\\%').replace('$', '\\$')
        safe_text = safe_text.replace('_', '\\_')
        safe_author = author.replace('_', '\\_')
        parts.append(
            f'\\textbf{{{safe_author}}}: {prefix}{safe_text}'
        )
    joined = ' \\\\[2pt] '.join(parts)
    return (
        f'\\marginpar{{\\footnotesize\\raggedright '
        f'\\textcolor{{orange}}{{\\textbf{{Comment}}}} \\\\ {joined}}}'
    )


def inject_into_file(tex_path, annotations):
    """Inject annotations into a single .tex file. Returns number injected."""
    with open(tex_path, 'r', encoding='utf-8') as f:
        content = f.read()

    injected = 0
    for el_id, comments in annotations.items():
        if '--p' in el_id:
            continue
        label_pattern = r'(\\label\{' + re.escape(el_id) + r'\})'
        match = re.search(label_pattern, content)
        if not match:
            continue
        note = format_comment_latex(comments)
        insertion = match.group(0) + '\n' + note
        content = content[:match.start()] + insertion + content[match.end():]
        injected += 1

    if injected > 0:
        backup = tex_path + BACKUP_SUFFIX
        if not os.path.exists(backup):
            shutil.copy2(tex_path, backup)
        with open(tex_path, 'w', encoding='utf-8') as f:
            f.write(content)

    return injected


def restore_backups():
    """Remove injected annotations by restoring .bak files."""
    for bak in glob.glob(os.path.join(CHAPTERS_DIR, '*' + BACKUP_SUFFIX)):
        original = bak[:-len(BACKUP_SUFFIX)]
        shutil.move(bak, original)
        print(f'  Restored {os.path.basename(original)}')


def main():
    if len(sys.argv) < 2:
        json_path = os.path.join(SCRIPT_DIR, 'annotations-export.json')
    else:
        if sys.argv[1] == '--restore':
            print('Restoring backups...')
            restore_backups()
            return
        json_path = sys.argv[1]

    if not os.path.exists(json_path):
        print(f'No annotation file found at {json_path}, skipping injection.')
        return

    annotations = load_annotations(json_path)
    if not annotations:
        print('No annotations to inject.')
        return

    print(f'Loaded {sum(len(v) for v in annotations.values())} comment(s) '
          f'for {len(annotations)} element(s)')

    tex_files = glob.glob(os.path.join(CHAPTERS_DIR, '*.tex'))
    total = 0
    for tf in tex_files:
        n = inject_into_file(tf, annotations)
        if n > 0:
            print(f'  Injected {n} annotation(s) into {os.path.basename(tf)}')
            total += n

    print(f'Total: {total} annotation(s) injected.')
    if total > 0:
        print('Run "python3 inject_annotations.py --restore" to undo.')


if __name__ == '__main__':
    main()
