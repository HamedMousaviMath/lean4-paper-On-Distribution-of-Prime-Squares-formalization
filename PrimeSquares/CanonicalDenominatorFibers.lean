import PrimeSquares.RationalUnitRecovery

open Finset
namespace PrimeSquares

noncomputable def canonicalDenominatorFiber (q : ℕ) : Finset ℚ :=
  (canonicalRationalCenters q).filter (fun r => r.den=q)

theorem mem_canonicalDenominatorFiber (q : ℕ) (r : ℚ) :
    r ∈ canonicalDenominatorFiber q ↔ r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den=q := by
  classical
  simp only [canonicalDenominatorFiber,mem_filter,mem_canonicalRationalCenters]
  constructor
  · rintro ⟨⟨hc,_⟩,hd⟩
    exact ⟨hc,hd⟩
  · rintro ⟨hc,hd⟩
    exact ⟨⟨hc,hd.le⟩,hd⟩

theorem unitRational_mem_fiber (q : ℕ) [NeZero q] (u : (ZMod q)ˣ) :
    unitRational q u ∈ canonicalDenominatorFiber q := by
  rw [mem_canonicalDenominatorFiber]
  exact ⟨unitRational_canonical q u,unitRational_den q u⟩

end PrimeSquares
