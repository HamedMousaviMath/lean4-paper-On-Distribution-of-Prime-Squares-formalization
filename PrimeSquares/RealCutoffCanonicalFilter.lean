import PrimeSquares.RealCutoffFloorBudget

open Finset
namespace PrimeSquares

theorem canonicalCenters_real_filter {M : ℕ} {Q : ℝ} (hQ : 0 ≤ Q) (hM : ⌊Q⌋₊ ≤ M) :
    (canonicalRationalCenters M).filter (fun r => (r.den : ℝ) ≤ Q)=canonicalRationalCenters ⌊Q⌋₊ := by
  classical
  ext r
  simp only [mem_filter,mem_canonicalRationalCenters]
  constructor
  · rintro ⟨⟨hc,_⟩,hd⟩
    exact ⟨hc,Nat.le_floor hd⟩
  · rintro ⟨hc,hd⟩
    exact ⟨⟨hc,hd.trans hM⟩,real_cutoff_denominator_bound hQ hd⟩

theorem sourceCenters_real_filter {Q R : ℝ} (hQ : 0 ≤ Q) (hQR : Q ≤ R) :
    (sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ Q)=canonicalRationalCenters ⌊Q⌋₊ :=
  canonicalCenters_real_filter hQ (Nat.floor_mono hQR)

end PrimeSquares
