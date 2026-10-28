import PrimeSquares.ClippedSourceConductorCenters
open Finset
namespace PrimeSquares
theorem clipped_source_collar_identity (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hR : 0 ≤ R)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    circleExceptionalHighModel ((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀))
      N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β=
    rationalCollarBlock (conductorCollarCenters Q q₀) N hN (effectiveCollarCutoff Q q₀) (fun _ => β)
      (fun r => if (r.den : ℝ) ≤ R then sourceExceptionalSelector q₀ active r*rationalTwistedGauss r (χ r) else 0) := by
  classical
  have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ hq₀)
  have he := circleExceptionalHighModel_collar
    ((sourceRationalCenters R).filter (fun r => (r.den : ℝ) ≤ effectiveCollarCutoff Q q₀))
    N hN hq₀ hQ hB χ (sourceExceptionalSelector q₀ active) β (fun r hr => (mem_filter.mp hr).2)
  rw [he]
  change rationalCollarBlock _ N hN (effectiveCollarCutoff Q q₀) _ _=_
  rw [rationalCollarBlock_exceptional_prune,clipped_source_conductor_centers hQ hq₀ hR,rationalCollarBlock_filter]
end PrimeSquares
