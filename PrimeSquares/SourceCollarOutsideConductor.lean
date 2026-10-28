import PrimeSquares.SourceCollarInactiveIdentity
open Finset
namespace PrimeSquares
theorem sourceCollarDifference_outside_conductor (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hq₀ : 0 < q₀) (hR : 0 ≤ R) (hout : R < (q₀ : ℝ))
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) :
    sourceCollarDifference N hN Q R q₀ active χ β=
      rationalCollarBlock (canonicalRationalCenters ⌊Q⌋₊) N hN Q (fun _ => 1) rationalPrincipalGauss := by
  classical
  rw [sourceCollarDifference,clipped_source_collar_identity N hN hQ hq₀ hR]
  have hz : rationalCollarBlock (conductorCollarCenters Q q₀) N hN (effectiveCollarCutoff Q q₀) (fun _ => β)
      (fun r => if (r.den : ℝ) ≤ R then sourceExceptionalSelector q₀ active r*rationalTwistedGauss r (χ r) else 0)=0 := by
    ext θ
    simp only [rationalCollarBlock,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,ContinuousMap.zero_apply]
    apply sum_eq_zero
    intro r hr
    have hl := conductor_divides_den_lower r (mem_conductorCollarCenters.mp hr).2.2
    have hn : ¬(r.den : ℝ) ≤ R := by linarith
    simp only [ite_eq_right hn,zero_mul]
  rw [hz,sub_zero]
end PrimeSquares
