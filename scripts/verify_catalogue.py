"""Verify the exact catalogue roots and their saved or freshly supplied axiom log."""
from pathlib import Path
import argparse
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--axioms', type=Path, help='Validate a newly produced Lean log.')
args = parser.parse_args()
catalogue_path = root / 'docs/formalization-companion/results.json'
catalogue = json.loads(catalogue_path.read_text())
expected = {d['name'] for g in catalogue['groups'] for d in g['declarations']}
record = json.loads((root / 'verification/catalogue-20261125/catalogue-audit.json').read_text())
assert record['actual_exit'] == 0 and record['artifact_valid']
assert record['catalogue_sha256'] == sha(catalogue_path)
assert record['selected_declarations'] == len(expected)
assert record['grouped_results'] == len(catalogue['groups'])
for path, expected_hash in record['source_hashes'].items():
    assert sha(root / path) == expected_hash, path
assert sha(root / record['audit_source']) == record['audit_source_sha256']
if args.axioms:
    text = args.axioms.read_text()
else:
    log = root / record['log']
    assert sha(log) == record['log_sha256']
    text = log.read_text()
assert not re.search(r'\b(error|warning):|sorryAx', text)
reports = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
    assert name not in reports, ('duplicate report', name)
    reports[name] = [a.strip() for a in axioms.split(',') if a.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    assert name not in reports, ('duplicate report', name)
    reports[name] = []
assert set(reports) == expected, ('wrong declaration coverage', expected - set(reports))
assert all(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
    for axioms in reports.values()), 'nonstandard axiom'
if not args.axioms:
    assert reports == record['transitive_axioms']
print(json.dumps(dict(grouped_results=len(catalogue['groups']),
    main_theorems=sum(g['kind'] == 'theorem' for g in catalogue['groups']),
    selected_declarations=len(reports), standard_transitive_axioms_only=True,
    source_and_catalogue_hashes_match=True, fresh_lean_compilation=False), indent=2))
