"""Check the published source inventory and saved Lean evidence without building."""
from pathlib import Path
import argparse
import hashlib
import json
import re

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--part-i-root', type=Path,
    help='Also check the imported Part I source bytes in a local pinned checkout.')
args = parser.parse_args()
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text())
sources = manifest['sources']
actual = {p.relative_to(root).as_posix() for p in (root / 'lean').rglob('*.lean')}
assert actual == set(sources), 'Lean source inventory differs from the saved manifest'
for path, expected in sources.items():
    assert sha(root / path) == expected, ('source hash mismatch', path)
evidence = root / 'verification/theorem-c-20261125'
summary = json.loads((evidence / 'summary.json').read_text())
assert summary['original_C_proved'] and not summary['original_source_completeness_assumed']
gate = json.loads((evidence / 'project-source-gate.json').read_text())
assert gate['actual_exit'] == 0 and gate['gate_valid']
stages = gate['stage_modules']
reports = 0
for module in stages:
    receipt = json.loads((evidence / 'stages' / (module + '.json')).read_text())
    assert receipt['actual_exit'] == 0 and receipt['artifact_valid'], module
    assert receipt['source_unchanged'] and receipt['imports_unchanged_during_build'], module
    assert sha(root / receipt['source']) == receipt['source_sha256'], module
    log = root / receipt['log']
    assert sha(log) == receipt['log_sha256'], ('log hash mismatch', module)
    text = log.read_text()
    assert not re.search(r'\b(error|warning):|sorryAx', text), module
    for axioms in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S):
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
            'propext', 'Classical.choice', 'Quot.sound'}, module
        reports += 1
for name, data in gate['project_sources'].items():
    if data['repository'] == 'part-ii':
        assert sha(root / data['source']) == data['source_sha256'], name
    elif args.part_i_root:
        assert sha(args.part_i_root / data['source']) == data['source_sha256'], name
assert reports == summary['used_stage_printed_axiom_reports']
assert len(stages) == summary['used_named_stages']
required = {
    'TheoremCOriginalCompletionProof': [
        'rawChosenFiberMapAtP_weak', 'originalRawOrderedUnitWeak', 'original_statement'],
    'TheoremCOriginalFourLinksAudit': [
        'partI', 'constantVertex', 'reversalIdentity', 'indexChange'],
}
for module, names in required.items():
    text = (evidence / 'stages' / (module + '.log')).read_text()
    for name in names:
        assert module + '.' + name + "' depends on axioms:" in text, name
for path, expected in manifest.get('evidence_files', {}).items():
    assert sha(root / path) == expected, ('evidence hash mismatch', path)
print(json.dumps(dict(lean_sources=len(sources), used_named_stages=len(stages),
    recorded_standard_axiom_reports=reports, source_hashes_match=True,
    original_four_link_target_checked=True, recorded_builds_exit_zero=True,
    part_i_source_bytes_checked=bool(args.part_i_root),
    fresh_lean_compilation=False), indent=2))
