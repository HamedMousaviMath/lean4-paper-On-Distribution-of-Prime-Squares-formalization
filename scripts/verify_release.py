#!/usr/bin/env python3
"""Check publication correspondence; this does not replace a Lean kernel build."""
from pathlib import Path
import json,re,hashlib,collections,sys
from check_source import code_only
R=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
hashes=json.loads((R/'verification/checkpoint1265-lean-source-hashes.json').read_text())
for name,h in hashes.items():assert sha(R/name)==h,'Changed checked proof source: '+name
nodes=json.loads((R/'blueprint/nodes.json').read_text());byid={n['id']:n for n in nodes};assert len(byid)==len(nodes)==52
visited=set();active=set()
def visit(i):
 assert i not in active,'Dependency cycle: '+i
 if i in visited:return
 active.add(i)
 for d in byid[i]['deps']:assert d in byid;visit(d)
 active.remove(i);visited.add(i)
for i in byid:visit(i)
labels=[l for n in nodes for l in n['labels']];assert len(labels)==len(set(labels))==58
mp=json.loads((R/'docs/PAPER_MAP.json').read_text());assert set(labels)=={x['label'] for x in mp['claims']}
assert sha(R/'paper/PrimeSquares.tex')==mp['current_manuscript_sha256']
text=(R/'blueprint/src/content.tex').read_text()
for n in nodes:
 assert text.count('\\label{'+n['id']+'}')==1
 assert text.count('\\proves{'+n['id']+'}')==1
 assert '\\uses{'+','.join(n['deps'])+'}' in text
 # Do not mark external assumptions as proved.
 if 'external_ids' in n:
  begin=text.index('\\label{'+n['id']+'}')
  end=text.index('\\end{proof}',begin)
  assert '\\leanok' not in text[begin:end]
decls=collections.defaultdict(list);theorems=set()
for f in (R/'PrimeSquares').glob('*.lean'):
 s=code_only(f.read_text())
 for k,name in re.findall(r'^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure|class)\s+(\w+(?:\.\w+)*)',s,re.M):
  decls[name].append(str(f.relative_to(R)))
  if k in ['theorem','lemma']:theorems.add('PrimeSquares.'+name)
targets={a for n in nodes for a in n['anchors']}
for a in targets:assert len(decls[a])==1,a
checks=set(re.findall(r'^#check PrimeSquares\.(\w+)',(R/'scripts/CheckBlueprint.lean').read_text(),re.M));assert checks==targets
printed=re.findall(r'^#print axioms (\S+)',(R/'scripts/CheckAxioms.lean').read_text(),re.M);assert len(printed)==len(set(printed))==4517 and set(printed)==theorems
log=(R/'verification/axioms-current.log').read_text();allowed={'propext','Classical.choice','Quot.sound'}
for name in printed:
 match=re.search("'"+re.escape(name)+r"' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",log,re.S)
 assert match,name
 assert {s.strip() for s in (match[1] or '').split(',') if s.strip()}<=allowed,name
review=json.loads((R/'verification/manuscript-review1266.json').read_text())
for name in ['PrimeSquares.tex','PrimeSquares.pdf','BibPrimeSquares.bib']:assert sha(R/'paper'/name)==review[name+'_sha256']
# Match all current statement bodies, ignoring only comments and whitespace.
def uncomment(s):return '\n'.join(re.split(r'(?<!\\)%',line,1)[0] for line in s.splitlines())
pat=r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(.*?)\\end\{\1\}'
canon=lambda s:re.sub(r'\s+','',s)
current=collections.Counter((k,canon(s)) for k,s in re.findall(pat,uncomment((R/'paper/PrimeSquares.tex').read_text()),re.S))
saved=collections.Counter((x['kind'],canon(x['statement_latex'])) for x in mp['claims']);assert current==saved
# The full original blueprint archive is immutable, independently of current titles.
manifest=json.loads((R/'blueprint/full_unedited_manifest.json').read_text())
for row in manifest['files']:
 p=R/'blueprint/full_unedited'/row['path']
 assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
submitted=(R/'paper/archive/PrimeSquares_Submitted_2026_10_28.tex').read_text()
assert submitted.replace('On Equidistribution of Prime Squares','On the Distribution of Prime Squares')==(R/'paper/PrimeSquares.tex').read_text()
result={'publication_release':1266,'proof_checkpoint':1265,'checked_Lean_files_unchanged':len(hashes),'blueprint_nodes':len(nodes),'mathematical_groups':39,'independent_input_groups':13,'paper_claims_and_definitions':58,'DAG_acyclic':True,'displayed_Lean_targets_resolve_in_unchanged_sources':len(targets),'archived_theorem_axiom_results_revalidated':len(printed),'fresh_Lean_build_this_release':False,'full_unedited_original_files_preserved':len(manifest['files']),'manuscript_source_edit_is_title_only':True,'scope':'Source identities, exact statement correspondence, graph, source declarations and archived audits; no new kernel execution.'}
(R/'verification/publication-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
