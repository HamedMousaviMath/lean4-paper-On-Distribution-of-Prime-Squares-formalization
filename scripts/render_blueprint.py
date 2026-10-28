#!/usr/bin/env python3
"""Render the curated 52-node blueprint; no Lean source is generated or modified."""
from pathlib import Path
import json,re,collections
ROOT=Path(__file__).resolve().parents[1];S=ROOT/'blueprint/src'
nodes=json.loads((ROOT/'blueprint/nodes.json').read_text());mp=json.loads((ROOT/'docs/PAPER_MAP.json').read_text());rows={x['label']:x for x in mp['claims']};nums=json.loads((ROOT/'blueprint/paper_labels.json').read_text())
sections=['IndependentInputs','Arithmetic','Improving','PrimeOperators','Stopping','Orlicz','Badness','Ergodic','GoldbachArithmetic','GoldbachCircle','GoldbachSieve']
titles={'IndependentInputs':'Independent inputs and their exact scope','Arithmetic':'Arithmetic: quadratic sums and conductors','Improving':'Improving: optimization and the main estimate','PrimeOperators':'Prime operators: approximation, low and high terms','Stopping':'Stopping: local estimates and sparse domination','Orlicz':'Orlicz: quantitative IW and the three-family maximum','Badness':'Badness: arithmetic blocks and the persistent criterion','Ergodic':'Ergodic: transference and the two endpoint conclusions','GoldbachArithmetic':'Goldbach arithmetic: reductions and the exceptional set','GoldbachCircle':'Goldbach circle method: minor arcs, major arcs and completion','GoldbachSieve':'Goldbach sieve: local densities, presieving and comparison'}
def esc(s):return s.replace('&',r'\&').replace('_',r'\_').replace('%',r'\%').replace('#',r'\#')
def statement(s):
 s=re.sub(r'^\s*\[[^\]]*\]','',s)
 s=re.sub(r'\\label\{[^}]+\}','',s)
 def ref(m):
  num=nums.get(m[2]);assert num is not None,m[2]
  return r'\textup{('+num+r')}' if m[1]=='eqref' else r'\textup{'+num+'}'
 s=re.sub(r'\\(eqref|ref)\{([^}]+)\}',ref,s)
 s=re.sub(r'\\cite(?:\[([^\]]*)\])?\{([^}]+)\}',lambda m:r'\textnormal{[paper bibliography: '+esc(m[2])+(('; '+esc(m[1])) if m[1] else '')+']}',s)
 s=re.sub(r'\\begin\{enumerate\}\[[^\n]*?\]',r'\\begin{enumerate}',s)
 return re.sub(r'\n[ \t]*\n+', '\n', s).strip()
intro=r'''\section*{Purpose and verification boundary}
This is the compact public blueprint for Hamed Mousavi's
\emph{On the Distribution of Prime Squares and Its Applications}.
It is a companion to the supplied manuscript, not a new statement of the
independent analytic theorems. All 54 numbered claims and four definitions
are accounted for in 52 graph nodes: 39 mathematical groups and 13 independent
input groups. Closely related identities and immediate consequences share a
node. No node is devoted only to simplification, linear arithmetic or routine
algebra.

The Lean implementation is unchanged from proof checkpoint 1265.
Its recorded fresh build covered 1,382 project modules, 4,517 named theorem
axiom audits and 973 evidence declaration signatures. Release 1266 is a
source reconciliation and exposition release, not a new proof checkpoint.
The numbered ledger has 22 proved results under their source hypotheses,
31 complete conditional implications and one quoted external theorem;
all four definitions are formalized.

\textbf{Conditional means conditional.}
The theorem statements below are read under the independent inputs linked
in their dependency nodes. These inputs are explicit Lean hypotheses, not
new mathematical axioms. Kernel axiom audits therefore do not establish
their truth. The exact published-to-interface bridges, including some
normalizations, globalization and full-domain formulations, remain external.
The separate input catalogue gives the complete boundary; a group here is
not a claim that it is one single published theorem.

\textbf{Reading the graph.}
Milestones depend on technical nodes, which depend on essential definitions
and external inputs. An edge is a curated mathematical dependency, not an
exhaustive traversal of a Lean proof term. The web graph is a DAG with shared
lemmas, rather than a tree with duplicate copies. Every node has an explicit
\texttt{\string\uses} list and a following explanation carrying
\texttt{\string\proves}. External nodes deliberately have no proof-completion
marker. For conditional nodes, completion refers to the implication under
those hypotheses. Full statement-to-declaration evidence is in
\texttt{docs/PAPER\_MAP.json}.

\textbf{Notation and references.}
Use the conventions and surrounding hypotheses of the supplied manuscript.
In particular $e(t)=e^{2\pi it}$, $\mathbb A_q=(\mathbb Z/q\mathbb Z)^\times$,
and $\Lambda$ is the von Mangoldt function. Formula and section references
inside the reproduced statements refer to the paper's current numbering;
blueprint node numbers have their own counter. Source statements are retained
verbatim apart from labels, cross-reference rendering and enumeration style.
Groups may contain several statements with different external requirements;
the statement map retains their individual status. No source label or
existing Lean declaration has been renamed.

\textbf{Main routes.}
Theorem 1.1 follows from the arithmetic estimates, fixed-scale prime
approximation and abstract improving theorem, together with the ordinary-square
input. Theorem 1.3 additionally needs the high maximum and stopping recursion.
The quantitative IW route yields Theorem 7.2, its corollaries and Theorem 1.5(ii).
The arithmetic badness route yields Theorem 1.5(i), without the optional full
Granville--Kurlberg spacing theorem. The Goldbach route combines the circle
method, two-range sieve and strict positivity comparison.

\textbf{Implementation policy.}
Retain the small Lean lemmas used by automation, but keep them out of the
public graph. The existing namespace is \texttt{PrimeSquares}; section titles
are subject areas, not claims that new Lean subnamespaces have been created.
The module index lists the actual source modules for every displayed target.
'''
content=[intro]
for sec in sections:
 content.append('\\section{'+titles[sec]+'}\n')
 for x in [n for n in nodes if n['section']==sec]:
  isext='external_ids' in x;kind='lemma' if isext else ('definition' if x['id'][0].isupper() else ('theorem' if any(l.startswith('t:') for l in x['labels']) else 'lemma'))
  deps=','.join(x['deps'])
  content += ['\\begin{'+kind+'}['+esc(x['title'])+']',r'\label{'+x['id']+'}',r'\uses{'+deps+'}',r'\lean{'+','.join('PrimeSquares.'+a for a in x['anchors'])+'}']
  if not isext:content.append(r'\leanok')
  if isext:content += [r'\textbf{External input; no proof claimed.} '+x['text']]
  for label in x['labels']:
   row=rows[label];num=nums.get(label);name=(row['kind'].capitalize()+' '+num) if num else row['title']
   status={'proved':'proved under source hypotheses','conditional':'complete conditional implication','formalized':'definition formalized','external_candidate':'quoted external theorem'}[row['status']]
   content += [r'\par\medskip\noindent\textbf{Paper '+esc(name)+'.} '+r'\textit{'+status+r'.}\par',statement(row['statement_latex'])]
  content += ['\\end{'+kind+'}',r'\begin{proof}['+('Boundary and application' if isext else 'Proof architecture')+']',r'\proves{'+x['id']+'}',r'\uses{'+deps+'}']
  if isext:content += [r'This node records an unproved interface, not a proof. See the exact predicates in the displayed Lean declarations and the full input catalogue. '+(r'The unit-square application uses the correlation node, while the general spacing theorem remains external.' if x['id']=='input_gk' else r'The downstream nodes verify the paper-specific applicability and deductions.')]
  else:content += [r'\leanok',x['proof']]
  content += [r'\end{proof}','']
(S/'content.tex').write_text('\n'.join(content)+'\n')
(S/'content_web.tex').write_text((S/'content.tex').read_text().replace(r'\uses{}', r'% \uses{} -- explicitly empty leaf; plasTeX 3.1 compatibility').replace(r'\string\uses', 'uses').replace(r'\string\proves', 'proves'))
for row in mp['claims']: row['current_reference_number'] = nums.get(row['label'], 'unnumbered')
(ROOT/'docs/PAPER_MAP.json').write_text(json.dumps(mp,indent=2)+'\n')
# Complete coverage table, not extra mathematical graph nodes.
maplines=['# Paper-to-Lean map','','Numbers come from the newly compiled current manuscript. Nodes group related results; exact statements and all supporting anchors are in PAPER_MAP.json.','','| Paper | Statement | Blueprint node | Status | Selected Lean targets |','| --- | --- | --- | --- | --- |']
modulelines=['# Module index','','The existing namespace is `PrimeSquares`. Subject groups below are editorial navigation; proof sources are unchanged.','','| Node | Actual Lean modules |','| --- | --- |']
for x in nodes:
 for l in x['labels']:
  row=rows[l];maplines.append('| '+row['kind'].capitalize()+' '+nums.get(l,'(unnumbered)')+' | '+row['title']+' | `'+x['id']+'` | '+row['status']+' | '+', '.join('`PrimeSquares.'+n+'`' for n in x['anchors'])+' |')
 modules=[]
 for a in x['anchors']:
  matches=[f for f in (ROOT/'PrimeSquares').glob('*.lean') if re.search(r'^(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|def|abbrev|structure|class)\s+'+re.escape(a)+r'\b',f.read_text(),re.M)]
  assert len(matches)==1,(a,matches)
  modules.append(str(matches[0].relative_to(ROOT)))
 x['modules']=sorted(set(modules));modulelines.append('| `'+x['id']+'` | '+', '.join('`'+m+'`' for m in x['modules'])+' |')
(ROOT/'docs/PAPER_MAP.md').write_text('\n'.join(maplines)+'\n');(ROOT/'docs/MODULE_INDEX.md').write_text('\n'.join(modulelines)+'\n')
(ROOT/'blueprint/nodes.json').write_text(json.dumps(nodes,indent=2)+'\n')
# Every target gets a kernel #check after a local Lean build; no optional checkdecls dependency.
(ROOT/'scripts/CheckBlueprint.lean').write_text('import PrimeSquares\n\n'+''.join('#check PrimeSquares.'+a+'\n' for a in sorted({a for n in nodes for a in n['anchors']})))
print('Rendered',len(nodes),'nodes')
