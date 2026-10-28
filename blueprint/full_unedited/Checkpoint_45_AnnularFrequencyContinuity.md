# Checkpoint 45: Continuity in frequency of the genuine annular oscillatory integral

The genuine normalized annular oscillatory integral is continuous as a function of the real frequency, for every positive natural arithmetic length N and every real exponent beta. This proves regularity of the actual integral; it is not an extra hypothesis on a model function.

The proof first establishes joint continuity of the quadratic phase in frequency and integration variable. To apply compact parametric integration for arbitrary beta, the power density is continuously extended by replacing t with max(t,N/2). This extension is strictly positive and equals the original density throughout the integration annulus. The compact-interval integral is then identified with the original half-open integral, whose endpoint difference has measure zero, and the exact factor 1/N is preserved. This regularity will support continuous circle multipliers after periodization. It does not supply any prime-distribution estimate.


## Checked declarations

| Module | Named supporting theorems |
| --- | ---: |
| AnnularFrequencyContinuity.lean | 2 |

- `quadraticOscillation_joint_continuous`
- `annularOscillatoryModel_continuous`

<!-- checkpoint-verification -->

## Verification

All 112 project modules are covered by the authenticated compilation history, beginning with a fresh full build. This checkpoint passes a 3631-job dependency-aware build with remote project artifact reuse disabled. Unchanged earlier proof sources and compiled Lean artifacts are SHA256 checked before reuse; new/changed modules and the root are compiled. All 853 named theorems pass a fresh complete transitive axiom audit, allowing only propext, Classical.choice and Quot.sound; all 114 Lean files pass the source scan. No placeholders, added mathematical axioms or unchecked evaluation are used. Build receipts record exactly which modules were compiled at every step.

The ten completed numbered results remain 3.1, 3.11, 3.12, accepted revised 3.14 and Corollary 3.16, original 3.20, 3.24, 3.27, Theorem 4.1 and Corollary 4.15. The abstract results retain their source hypotheses. Full Lemma 6.5, Proposition 4.19 and headline applications remain open. Lemma 3.21 retains two earlier explicit PNT limits; its external bridge is not integrated or used here. The already displayed raw progression-prefix estimate is consumed as a theorem hypothesis; it remains unproved. No new external analytic estimate or own-paper lemma is assumed.
