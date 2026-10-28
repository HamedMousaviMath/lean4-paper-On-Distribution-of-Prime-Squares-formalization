import PrimeSquares.ConductorEstimates
import PrimeSquares.ConductorDecay

/-!
# Complete conductor-sensitive refinement (Lemma 3.27)

Source label: `l:exceptionalarithmetic`; equations `e:exceptionalarithmetic`
and `e:sqfreeconds`. All three estimates, the logarithmic consequence and
the support condition are combined below, with one admissible B₀ depending
only on q₀. The result is stronger than the source: no primitivity assumption
is needed. The character is required to be real, expressed by conjugation.
No additional mathematical hypotheses are used.
-/

namespace PrimeSquares

theorem conductor_sensitive_refinement :
    ∃ C : ℝ, 0 < C ∧ ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),
      (∀ r, star (χ₀ r) = χ₀ r) →
      1 ≤ conductorMajorant q₀ ∧
      (∀ (d : ℕ) [NeZero d] (x : ZMod (q₀ * d)),
        ‖twistedSquareCorrelation (q₀ * d)
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) x‖ ≤
          conductorMajorant q₀ * conductorCorrelationProduct d) ∧
      (∀ (d : ℕ) [NeZero d] (a : ZMod (q₀ * d)), IsUnit a →
        ‖twistedSquareSum (q₀ * d)
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) a‖ ≤
          32 * conductorSigma q₀ χ₀ * (d : ℝ) ^ (-(1 / 2 : ℝ)) * conductorRho d) ∧
      conductorSigma q₀ χ₀ * Real.sqrt (conductorMajorant q₀) ≤
        C * (q₀ : ℝ) ^ (-(1 / 25 : ℝ)) ∧
      (1 + Real.log q₀) * conductorSigma q₀ χ₀ * Real.sqrt (conductorMajorant q₀) ≤ C ∧
      (∀ (d : ℕ) [NeZero d],
        (∃ a : (ZMod (q₀ * d))ˣ, twistedSquareSum (q₀ * d)
          (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) a ≠ 0) →
        ∃ ν d₁ : ℕ, ν ≤ 5 ∧ 0 < d₁ ∧ Squarefree d₁ ∧
          d₁.Coprime (2 * q₀) ∧ d = 2 ^ ν * d₁) := by
  obtain ⟨D, hD, hd⟩ := conductorSigma_majorant_decay
  obtain ⟨L, hL, hl⟩ := conductorSigma_majorant_log_bound
  refine ⟨D + L, add_pos hD hL, ?_⟩
  intro q₀ inst χ₀ hreal
  have hχ₀ := (dirichletCharacter_quadratic_iff_real q₀ χ₀).mpr hreal
  refine ⟨conductorMajorant_one_le q₀ (NeZero.pos q₀), ?_, ?_, ?_, ?_, ?_⟩
  · intro d inst x
    exact induced_twistedCorrelation_conductor_bound q₀ d χ₀ hχ₀ x
  · intro d inst a ha
    rw [Real.rpow_neg (Nat.cast_nonneg d), ← Real.sqrt_eq_rpow]
    simpa only [div_eq_mul_inv] using induced_twistedSquareSum_conductor_bound q₀ d χ₀ hχ₀ a ha
  · exact (hd q₀ χ₀).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact (hl q₀ χ₀).trans (by linarith)
  · intro d inst h
    obtain ⟨a, ha⟩ := h
    exact induced_real_twistedSquareSum_support q₀ d χ₀ hreal a a.isUnit ha

end PrimeSquares
