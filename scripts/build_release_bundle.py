"""Build a deterministic, exact-commit source archive and release hash records."""
from pathlib import Path
import gzip
import hashlib
import io
import json
import subprocess
import tarfile

root = Path(__file__).resolve().parents[1]
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=root), 'Commit first.'
subprocess.run(['python3', 'scripts/verify_snapshot.py'], cwd=root, check=True)
commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
version = 'v0.1.0-rc1'
prefix = 'dagger-models-lean-part-ii-' + version + '/'
output = root / 'build/release'
output.mkdir(parents=True, exist_ok=True)
tar_bytes = subprocess.check_output(['git', 'archive', '--format=tar', '--prefix=' + prefix,
    commit], cwd=root)
sources = {}
with tarfile.open(fileobj=io.BytesIO(tar_bytes)) as archive:
    for member in archive:
        assert member.name.startswith(prefix) and '..' not in Path(member.name).parts
        if member.isdir():
            continue
        assert member.isfile(), ('unexpected archive member', member.name)
        relative = member.name[len(prefix):]
        data = archive.extractfile(member).read()
        assert data == (root / relative).read_bytes(), ('committed byte mismatch', relative)
        sources[relative] = dict(size=len(data), sha256=hashlib.sha256(data).hexdigest())
archive_path = output / ('dagger-models-lean-part-ii-' + version + '-source.tar.gz')
archive_path.write_bytes(gzip.compress(tar_bytes, mtime=0))
(output / 'source-archive-manifest.json').write_text(json.dumps(dict(
    source_commit=commit, prefix=prefix, files=sources), indent=2) + '\n')
for source, name in [
    ('docs/formalization-companion/part2-theorem-c-companion-en.pdf',
        'part2-theorem-c-companion-en.pdf'),
    ('verification/theorem-c-20261125/summary.json', 'verification-summary.json'),
    ('verification/theorem-c-20261125/publication-checks.json', 'publication-checks.json')]:
    (output / name).write_bytes((root / source).read_bytes())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
names = [archive_path.name, 'source-archive-manifest.json',
    'part2-theorem-c-companion-en.pdf', 'verification-summary.json', 'publication-checks.json']
record = dict(repository='https://github.com/Yonoha/dagger-models-lean-part-ii',
    release_tag=version, source_commit=commit, tracked_files=len(sources),
    lean_library_sources=sum(p.startswith('lean/') and p.endswith('.lean') for p in sources),
    part_i_commit='9ee62295a79ef61269259e27216afc0292458931',
    original_C_target='DaggerModels.PartII.TheoremCStatement.statement',
    verification_scope='Local original kernel evidence and separate-layout final module checks; '
        'no cold full build, hosted Linux CI, Comparator or human certification',
    artifacts={name: dict(sha256=sha(output / name), size=(output / name).stat().st_size)
        for name in names})
(output / 'release-record.json').write_text(json.dumps(record, indent=2) + '\n')
names.append('release-record.json')
(output / 'SHA256SUMS').write_text(''.join(sha(output / name) + '  ' + name + '\n'
    for name in names))
print(json.dumps(dict(source_commit=commit, tracked_files=len(sources),
    archive_sha256=sha(archive_path), archive_bytes=archive_path.stat().st_size,
    output='build/release'), indent=2))
