import PrimeSquares.CircleApproximationData
import PrimeSquares.RestrictedL2

open Finset
open scoped lp
namespace PrimeSquares

theorem operator_finite_indicator_pairing_bound
    (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) {b : ℝ} (hT : ‖T‖ ≤ b) (F G : Finset ℤ) :
    ‖∑ x ∈ G, T (finiteIndicatorLp F 2) x‖ ≤ b*Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ) := by
  have hn := T.le_of_opNorm_le hT (finiteIndicatorLp F 2)
  rw [finiteIndicatorLp_two_norm] at hn
  exact (norm_finite_sum_le_lp_two G (T (finiteIndicatorLp F 2))).trans
    (mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _))

theorem operator_finite_indicator_pairing_normalized
    (T : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) {b L : ℝ} (hT : ‖T‖ ≤ b) (hL : 0 < L)
    (F G : Finset ℤ) :
    ‖∑ x ∈ G, T (finiteIndicatorLp F 2) x‖/L ≤ b*(finiteSetDensity L F G)^(1/2 : ℝ) := by
  calc
    _ ≤ (b*Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ))/L :=
      div_le_div_of_nonneg_right (operator_finite_indicator_pairing_bound T hT F G) hL.le
    _ = _ := by rw [finiteSetDensity_half_rpow hL F G];ring

theorem globalCircleError_restricted_bound {P C B d c A : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hd : 0 ≤ d) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1/8)*Real.sqrt (Real.log N) →
    ∀ (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ),
      CircleAnalyticInputs N Q χ κ β P C B d c → ∀ hN : 1 ≤ N, ∀ F G : Finset ℤ,
    ‖∑ x ∈ G, circleMajorArcErrorOperator (sourceRationalCenters (sourceMajorArcScale N Q))
      N hN χ κ β (finiteIndicatorLp F 2) x‖ ≤
      (2*((2 : ℝ)^A*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-A)))*
        Real.sqrt (F.card : ℝ)*Real.sqrt (G.card : ℝ) := by
  obtain ⟨N₀,hN₀,h⟩ := globalCircleApproximation_l2_operator hP hC hB hd hc hA
  refine ⟨N₀,hN₀,?_⟩
  intro N hn Q hQ hQl χ κ β hi hN F G
  exact operator_finite_indicator_pairing_bound _ (h N hn Q hQ hQl χ κ β hi hN) F G

end PrimeSquares
