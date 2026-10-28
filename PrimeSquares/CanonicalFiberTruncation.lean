import PrimeSquares.UnitFiberReindexing

open Finset
namespace PrimeSquares

theorem canonicalDenominatorFiber_zero : canonicalDenominatorFiber 0=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  have h := (mem_canonicalDenominatorFiber 0 r).mp hr
  have hp := r.den_pos
  omega

theorem canonicalCenters_denominator_filter {q M : ℕ} (hq : q ≤ M) :
    (canonicalRationalCenters M).filter (fun r => r.den=q)=canonicalDenominatorFiber q := by
  classical
  ext r
  simp only [mem_filter,mem_canonicalRationalCenters,mem_canonicalDenominatorFiber]
  constructor
  · rintro ⟨⟨hc,_⟩,hd⟩
    exact ⟨hc,hd⟩
  · rintro ⟨hc,hd⟩
    exact ⟨⟨hc,hd.le.trans hq⟩,hd⟩

end PrimeSquares
