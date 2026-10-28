import PrimeSquares.ConductorPowerSeparation
namespace PrimeSquares
theorem conductorGauss_envelope {η ε : ℝ} (hε : 0 ≤ ε) (hhalf : η+ε < 1/2) :
    ∃ C : ℝ,0 < C ∧ ∀ (q₀ : ℕ),0 < q₀ → ∀ r : ℚ,q₀ ∣ r.den →
      ∀ χ : DirichletCharacter ℂ r.den,‖rationalTwistedGauss r χ‖ ≤
        (C*(q₀ : ℝ)^(-ε))*(r.den : ℝ)^(-η) := by
  obtain ⟨C,hC,hG⟩ := rationalGauss_uniform_decay hhalf
  refine ⟨C,hC,?_⟩
  intro q₀ hq₀ r hdiv χ
  calc
    _ ≤ C*(r.den : ℝ)^(-(η+ε)) := (hG r).2 χ
    _ ≤ C*((q₀ : ℝ)^(-ε)*(r.den : ℝ)^(-η)) := mul_le_mul_of_nonneg_left
      (conductor_power_separation (by exact_mod_cast hq₀) (conductor_divides_den_lower r hdiv) hε) hC.le
    _ = _ := by ring
end PrimeSquares
