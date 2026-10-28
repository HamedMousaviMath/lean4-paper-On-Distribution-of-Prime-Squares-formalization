import PrimeSquares.PrimeSquareAnnularEndpoint
import PrimeSquares.EndpointFiniteScaleBounds

namespace PrimeSquares

theorem orliczWeight_half_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    orliczWeight (1/2) x ≤ orliczWeight (1/2) y := by
  have hy : 2 ≤ y := hx.trans hxy
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := by linarith
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hb : 0 < Real.sqrt y := Real.sqrt_pos.mpr hyp
  have hab : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne',Real.log_sqrt hyp.le,Real.log_sqrt hxp.le] at hl
  have hm : (Real.log y/2-Real.log x/2+1)*Real.sqrt x ≤ Real.sqrt y :=
    (le_div_iff₀ ha).mp (by linarith)
  have hnon := mul_nonneg (sub_nonneg.mpr hab) hlx
  dsimp [orliczWeight]
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow]
  apply (div_le_div_iff₀ (by linarith : 0 < 2+Real.log x) (by linarith : 0 < 2+Real.log y)).mpr
  nlinarith

theorem paperPhi_half_antitone {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (hab : a ≤ b) (hb : b ≤ 1) : paperPhi c (1/2) b ≤ paperPhi c (1/2) a := by
  have hbp : 0 < b := ha.trans_le hab
  have hpl : paperLog b ≤ paperLog a := by
    rw [paperLog_of_le_one hbp hb,paperLog_of_le_one ha (hab.trans hb)]
    linarith [Real.log_le_log ha hab]
  rw [paperPhi_eq_exp_weight,paperPhi_eq_exp_weight]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (orliczWeight_half_mono (paperLog_two_le b) hpl) hc)

theorem primeSquare_annular_endpoint_dyadic (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ A : ℝ,0 < A ∧ ∀ k : ℕ,∀ F G : Finset ℤ,
      (F.card : ℝ)*(G.card : ℝ) ≤ (((2^k : ℕ) : ℝ)^2)^2 →
        ‖restrictedKernelPairing (annularWeightedSquareAverageKernel (2^k)
          ArithmeticFunction.vonMangoldt) F G‖/(((2^k : ℕ) : ℝ)^2) ≤
          A*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
            paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G) := by
  obtain ⟨N₀,hN₀,A,hA,h⟩ := primeSquare_annular_endpoint_large HP D hCS HS hstar
  have hc : 0 ≤ cstar := (by positivity : (0 : ℝ) ≤ 4*Real.sqrt 3/9).trans hstar.le
  refine ⟨A+(N₀ : ℝ)^2,by positivity,?_⟩
  intro k F G hFG
  have hδ : 0 ≤ finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hp : 0 ≤ (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
      paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G) :=
    mul_nonneg (Real.rpow_nonneg hδ _) (paperPhi_pos _ _ _).le
  by_cases hk : N₀ ≤ 2^k
  · exact (h k hk F G hFG).trans (by
      have hm := mul_le_mul_of_nonneg_right (show A ≤ A+(N₀ : ℝ)^2 by nlinarith [sq_nonneg (N₀ : ℝ)]) hp
      simpa only [mul_assoc] using hm)
  · have hb := annular_endpoint_finite_scale (by positivity : 0 < (2 : ℕ)^k)
      (le_of_not_ge hk) hc F G hFG
    exact hb.trans (by
      have hm := mul_le_mul_of_nonneg_right (show (N₀ : ℝ)^2 ≤ A+(N₀ : ℝ)^2 by linarith) hp
      simpa only [mul_assoc] using hm)

end PrimeSquares
