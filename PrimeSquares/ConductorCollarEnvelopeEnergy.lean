import PrimeSquares.EffectiveCutoffUniformPower
open Finset
namespace PrimeSquares
theorem conductorCollar_envelope_energy {M : ℕ} (hM : 2 ≤ M) {Q C η ε : ℝ}
    (hC : 0 < C) (hη0 : 0 ≤ η) (hη1 : η < 1) {q₀ : ℕ} (hq₀ : 0 < q₀)
    (hW : 1 ≤ effectiveCollarCutoff Q q₀)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ conductorCollarCenters Q q₀,0 ≤ β j r)
    (hβ1 : ∀ j,∀ r ∈ conductorCollarCenters Q q₀,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ conductorCollarCenters Q q₀,
      ‖c j r‖ ≤ (C*(q₀ : ℝ)^(-ε))*(r.den : ℝ)^(-η)) (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖rationalCollarBlock (conductorCollarCenters Q q₀) ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) (effectiveCollarCutoff Q q₀) (β j) (c j) θ‖^2) ≤
      (collarPowerConstant C η*(q₀ : ℝ)^(-ε)*(effectiveCollarCutoff Q q₀)^(-η))^2 := by
  rw [←collarPowerConstant_mul]
  apply completeRationalCollar_finite_energy hM _ (fun r hr => (mem_conductorCollarCenters.mp hr).1)
    hW (by positivity) hη0 hη1 (fun r hr => (mem_conductorCollarCenters.mp hr).2.1) β hβ0 hβ1 c hc J θ
end PrimeSquares
