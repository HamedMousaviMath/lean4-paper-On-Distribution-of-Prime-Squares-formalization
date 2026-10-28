import PrimeSquares.FullSquareApproximationRate
import PrimeSquares.DecayingMaximalTail
import PrimeSquares.DyadicLogarithmicBudget

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

noncomputable def fullSquareCircleErrorOperator (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) :
    ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  integerMultiplier (fullSquareCircleError (sourceRationalCenters (sourceMajorArcScale N Q)) N hN)

theorem fullSquareCircleErrorOperator_eq (N : ℕ) (hN : 1 ≤ N) (Q : ℝ) :
    fullSquareCircleErrorOperator N hN Q =
      annularWeightedSquareAverage (P := 2) (by norm_num) N (fun _ => 1)-
      integerMultiplier (varyingIndexAnnularBlock (sourceRationalCenters (sourceMajorArcScale N Q))
        N hN 1 rationalFullSquareGauss) := by
  unfold fullSquareCircleErrorOperator fullSquareCircleError
  rw [integerMultiplier_sub, ←annularWeightedSquareAverage_l2_multiplier]

theorem fullSquareCircleErrorOperator_uniform {E : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (1/8 : ℝ)*Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
      ‖fullSquareCircleErrorOperator N hN Q‖ ≤ 4*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-(2 : ℝ)) := by
  obtain ⟨N₀, hN₀, hbound⟩ := fullSquareCircleError_uniform hE HE
  refine ⟨N₀, hN₀, ?_⟩
  intro N hn hEven Q hQ hcut hN
  apply (integerMultiplier_opNorm_le _).trans
  exact (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 4*Q^(-(1/2 : ℝ))*(1+Real.log N)^(-(2 : ℝ)))).mpr
    (hbound N hn hEven Q hQ hcut hN)

noncomputable def fullSquareErrorMaximalConstant : ℝ := 8*(Real.log 2)^(-(2 : ℝ))

theorem fullSquareErrorMaximalConstant_pos : 0 < fullSquareErrorMaximalConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold fullSquareErrorMaximalConstant
  positivity

theorem full_square_approximation_maximum {E : ℝ} (hE : 0 ≤ E)
    (HE : RawQuadraticWeylApproximationInput E) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ (M : ℕ), N₀ ≤ M → ∀ hM : 2 ≤ M, Even M →
      ∀ Q : ℝ, 1 ≤ Q → Real.log Q ≤ (1/8 : ℝ)*Real.sqrt (Real.log M) →
      ∀ f : ℓ²(ℤ,ℂ), ∃ g : lp (fun _ : ℤ => ℝ) 2, (∀ x, 0 ≤ g x) ∧
        (∀ j x, ‖fullSquareCircleErrorOperator ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j; omega) Q f x‖ ≤ g x) ∧
        ‖g‖ ≤ fullSquareErrorMaximalConstant*Q^(-(1/2 : ℝ))*‖f‖ := by
  obtain ⟨N₀, hN₀, hbound⟩ := fullSquareCircleErrorOperator_uniform hE HE
  refine ⟨N₀, hN₀, ?_⟩
  intro M hm hM hEven Q hQ hcut f
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hMp : (0 : ℝ) < M := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let T := fun j => fullSquareCircleErrorOperator ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j; omega) Q
  let B := 4*Q^(-(1/2 : ℝ))*(Real.log 2)^(-(2 : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdecay (j : ℕ) : ‖T j‖ ≤ B*((j : ℝ)+1)^(-(2 : ℝ)) := by
    have hp : (1 : ℕ) ≤ 2^j := one_le_pow₀ (by norm_num)
    have hMNnat : M ≤ (2 : ℕ)^j*M := by simpa only [one_mul] using Nat.mul_le_mul_right M hp
    have hMN : (M : ℝ) ≤ (((2 : ℕ)^j*M : ℕ) : ℝ) := by exact_mod_cast hMNnat
    have hroot := Real.sqrt_le_sqrt (Real.log_le_log hMp hMN)
    have hcutN := hcut.trans (mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 1/8))
    have h := hbound ((2 : ℕ)^j*M) (hm.trans hMNnat) (hEven.mul_left _) Q hQ hcutN
      (by have h := dyadic_annular_scale_lower hM j; omega)
    have hNmono : (((2 : ℕ)^j : ℕ) : ℝ) ≤ (((2 : ℕ)^j*M : ℕ) : ℝ) := by
      exact_mod_cast (show (2 : ℕ)^j ≤ (2 : ℕ)^j*M by
        simpa only [mul_one] using Nat.mul_le_mul_left ((2 : ℕ)^j) (show 1 ≤ M by omega))
    have hlog : 1+Real.log (((2 : ℕ)^j : ℕ) : ℝ) ≤ 1+Real.log (((2 : ℕ)^j*M : ℕ) : ℝ) := by
      have hl := Real.log_le_log (by positivity : (0 : ℝ) < (((2 : ℕ)^j : ℕ) : ℝ)) hNmono
      linarith
    have hpos : 0 < 1+Real.log (((2 : ℕ)^j : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ (((2 : ℕ)^j : ℕ) : ℝ) := by exact_mod_cast hp
      linarith [Real.log_nonneg h1]
    have hb := (Real.rpow_le_rpow_of_nonpos hpos hlog (by norm_num : -(2 : ℝ) ≤ 0)).trans
      (dyadic_log_inverse_power (by norm_num : (0 : ℝ) ≤ 2) j)
    exact h.trans (by
      dsimp [B]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*Q^(-(1/2 : ℝ)) by positivity))
  obtain ⟨g, hg, ht, hn⟩ := decaying_operator_maximal_tail_majorant hB (by norm_num : (2 : ℝ) ≤ 2)
    0 T (by simpa only [zero_add] using hdecay) f
  refine ⟨g, hg, by simpa only [zero_add] using ht, ?_⟩
  exact hn.trans_eq (by
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    dsimp [B, fullSquareErrorMaximalConstant]
    ring)

end PrimeSquares
