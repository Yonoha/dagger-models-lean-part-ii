"""Generate the catalogue TeX sections and exact selected-root Lean axiom audit."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
folder = root / 'docs/formalization-companion'
catalogue = json.loads((folder / 'results.json').read_text())
groups = catalogue['groups']
assert len({g['id'] for g in groups}) == len(groups)
def escape(text):
    return ''.join({'&':r'\&', '%':r'\%', '_':r'\_', '#':r'\#',
        '{':r'\{', '}':r'\}', '$':r'\$', '≤':r'\ensuremath{\leq}'}.get(c, c) for c in text)
def mixed_escape(text):
    return ''.join(part if part.startswith('$') and part.endswith('$') else
        escape(part.replace('`', '')) for part in re.split(r'(\$[^$]*\$)', text))
def lines(text):
    return re.sub(r'(?<=[.;:]) +', '\n', text.strip())
def module_path(module):
    path = root / 'lean' / Path(*module.split('.')).with_suffix('.lean')
    if not path.is_file():
        path = root / 'lean/TheoremCStages' / (module + '.lean')
    assert path.is_file(), module
    return path.relative_to(root).as_posix()
declarations = {}
for group in groups:
    assert group['kind'] in {'theorem', 'proposition'}
    assert not re.search(r'\\(?:bigl|bigr|longrightarrow|longmapsto)\b', group['summary_tex'])
    for d in group['declarations']:
        path = module_path(d['module'])
        assert d['name'].split('.')[-1] in (root / path).read_text(), d
        assert declarations.get(d['name'], d['module']) == d['module']
        declarations[d['name']] = d['module']
for section in catalogue['sections']:
    body = [r'\section{' + escape(section['title']) + '}', '', section['intro_tex'], '']
    selected = [g for g in groups if g['section'] == section['id']]
    for group in selected:
        body += [r'\begin{resultblock}',
            r'\begin{' + group['kind'] + '}[' + escape(group['title']) + ']',
            r'\label{catalogue:' + group['id'] + '}', lines(group['summary_tex']),
            r'\end{' + group['kind'] + '}', '']
        names = ';\n'.join(d['name'] for d in group['declarations'])
        paths = ';\n'.join(dict.fromkeys(module_path(d['module']) for d in group['declarations']))
        body += [r'\Source{' + names + '}{' + paths + '}',
            r'\CatalogueNote{Scope}{' + escape(group['universe']) + '}',
            r'\CatalogueNote{Manuscript context}{' +
                escape(', '.join(group['manuscript_labels'])) + '}',
            r'\CatalogueNote{Construction and reuse}{' + mixed_escape(group['provenance']) + '}',
            r'\end{resultblock}', '']
    (folder / (section['id'] + '-results.tex')).write_text('\n'.join(body).rstrip() + '\n')
(folder / 'catalogue-version.tex').write_text(
    r'\newcommand{\CompanionTag}{' + catalogue['release_tag'] + '}\n' +
    r'\newcommand{\CatalogueCount}{' + str(len(groups)) + '}\n' +
    r'\newcommand{\CatalogueDeclarationCount}{' + str(len(declarations)) + '}\n')
audit = root / 'verification/catalogue-20261125/CheckCatalogueAxioms.lean'
audit.parent.mkdir(parents=True, exist_ok=True)
imports = sorted(set(declarations.values()) | {'MainTheoremsPartII'})
body = ['import ' + module for module in imports]
body += ['', '/-! Exact advertised declaration roots. Not an independent Challenge. -/', '',
    'set_option autoImplicit false', 'set_option warningAsError true', '']
body += ['#print axioms ' + name for name in sorted(declarations)]
audit.write_text('\n'.join(body) + '\n')
print(json.dumps(dict(grouped_results=len(groups), selected_declarations=len(declarations),
    owner_modules=len(set(declarations.values())), main_theorems=sum(g['kind']=='theorem' for g in groups))))
