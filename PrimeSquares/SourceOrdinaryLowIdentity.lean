import PrimeSquares.OrdinaryOnlySourceCircle
import PrimeSquares.RealCutoffCanonicalFilter
import PrimeSquares.RealOrdinaryCircleTerm
import PrimeSquares.DenominatorLowSourceInterface

open Finset
namespace PrimeSquares

theorem sourceLowModel_no_exception {N : ℕ} (hN : 1 ≤ N) {Q R : ℝ}
    (hQ : 1 ≤ Q) (hQR : Q ≤ R) (hb : 2*R^4 ≤ (N : ℝ)^2) (q₀ : ℕ) (B₀ : ℝ)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleLowModel (sourceRationalCenters R) N hN q₀ Q B₀ χ (fun _ => 0) β=
      realOrdinaryLowModel N hN Q (by linarith) (source_low_width_budget hQ hQR hb) := by
  classical
  have hQp : 0 < Q := by linarith
  have hR : 0 ≤ R := by linarith
  have hw := source_low_width_budget hQ hQR hb
  unfold circleLowModel realOrdinaryLowModel
  calc
    _ = ∑ r ∈ sourceRationalCenters R,
        if (r.den : ℝ) ≤ Q then ordinaryRationalCircleLow N hN Q hQp hw r else 0 := by
      apply sum_congr rfl
      intro r hr
      exact circleLowTerm_no_exception hN r hQp hQR ((mem_sourceRationalCenters hR r).mp hr).2 hb hw q₀ B₀ χ β
    _ = ∑ r ∈ canonicalRationalCenters ⌊Q⌋₊,ordinaryRationalCircleLow N hN Q hQp hw r := by
      rw [←sum_filter,sourceCenters_real_filter (by linarith : 0 ≤ Q) hQR]
    _ = _ := by
      rw [canonicalCenters_sum_units]
      apply sum_congr rfl
      intro q _
      exact denominatorUnitSum_ordinary N hN hQp hw q

end PrimeSquares
