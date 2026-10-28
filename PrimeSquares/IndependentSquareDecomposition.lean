import PrimeSquares.DyadicSquareReconstruction

open scoped lp
namespace PrimeSquares

/-- Explicit external input for the independent unweighted-square problem.
The Fourier construction in Han--Lacey--Yang, arXiv:1907.05734v2,
Lemma 2.2, Lemma 3.2, Proposition 3.3 and Lemmas 3.4/4.2 motivates this
GLOBAL norm interface. The displayed Lemma 2.2 itself is local. Its
globalization and the cited
independent analytic estimates are retained as an unformalized input here;
this predicate is not an imported Mathlib theorem or a prime-square claim.
Reflection from x+n^2 to x-n^2 with identical constants is proved separately
in SquareDecompositionReflection; it is no longer an unformalized passage.
All full-to-annular deductions below are proved. -/
def FullSquareDecompositionInput (C : ℝ) : Prop :=
  ∀ (N : ℕ),0 < N → ∀ j : ℕ,2 ≤ (2 : ℝ)^j →
    OperatorHighLowBound (weightedSquareAverageKernel N (fun _ => 1))
      ((N : ℝ)^2) ((2 : ℝ)^j) 1 (1/2) 2 1 C

theorem annular_indicator_two_mul (M : ℕ) (w : ℕ → ℝ) (F : Finset ℤ) (x : ℤ) :
    indicatorConvolution (annularWeightedSquareAverageKernel (2*M) w) F x=
      indicatorConvolution (weightedSquareAverageKernel (2*M) w) F x-
        (1/2 : ℂ)*indicatorConvolution (weightedSquareAverageKernel M w) F x := by
  have hs := congrArg (fun T : ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) => T (finiteIndicatorLp F 2) x)
    (annularWeightedSquareAverage_two_mul (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) M w)
  have ha := annularWeightedSquareAverage_finiteInput
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (2*M) w F (fun _ => 1) x
  have hn := weightedSquareAverage_finiteInput
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (2*M) w F (fun _ => 1) x
  have hm := weightedSquareAverage_finiteInput
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) M w F (fun _ => 1) x
  simp only [finiteConvolution_indicator,finiteInputLp_one] at ha hn hm
  rw [ha,hn,hm]
  exact hs

theorem fullSquare_decomposition_annular_two_mul {C : ℝ} (hC : 0 ≤ C)
    (H : FullSquareDecompositionInput C) (M : ℕ) (hM : 0 < M) (j : ℕ)
    (hj : 2 ≤ (2 : ℝ)^j) :
    OperatorHighLowBound (annularWeightedSquareAverageKernel (2*M) (fun _ => 1))
      (((2*M : ℕ) : ℝ)^2) ((2 : ℝ)^j) 1 (1/2) 2 1 (3*C) := by
  obtain ⟨Ln,Hn,hen,hln,hhn⟩ := H (2*M) (by omega) j hj
  obtain ⟨Lm,Hm,hem,hlm,hhm⟩ := H M hM j hj
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hhalf : ‖(1/2 : ℂ)‖=(1/2 : ℝ) := by norm_num
  refine ⟨(fun f => Ln f-(1/2 : ℂ) • Lm f),(fun f => Hn f-(1/2 : ℂ) • Hm f),?_,?_,?_⟩
  · intro F x
    rw [annular_indicator_two_mul,hen,hem]
    change _=(_-(1/2 : ℂ)*_)+(_-(1/2 : ℂ)*_)
    ring
  · intro f
    calc
      _ ≤ ‖Ln f‖+‖(1/2 : ℂ) • Lm f‖ := norm_sub_le _ _
      _ = ‖Ln f‖+(1/2 : ℝ)*‖Lm f‖ := by rw [norm_smul,hhalf]
      _ ≤ (C/(((2*M : ℕ) : ℝ)^2)*((2 : ℝ)^j)^1*(Real.log ((2 : ℝ)^j))^2*‖f‖)+
          (1/2 : ℝ)*(C/(M : ℝ)^2*((2 : ℝ)^j)^1*(Real.log ((2 : ℝ)^j))^2*‖f‖) :=
        add_le_add (hln f) (mul_le_mul_of_nonneg_left (hlm f) (by norm_num))
      _ = _ := by push_cast;field_simp;ring
  · intro f
    have hX : 0 ≤ ((2 : ℝ)^j)^(-(1/2 : ℝ))*(Real.log ((2 : ℝ)^j))^1*‖f‖ := by
      have hl : 0 ≤ Real.log ((2 : ℝ)^j) := Real.log_nonneg (by linarith)
      positivity
    calc
      _ ≤ ‖Hn f‖+‖(1/2 : ℂ) • Hm f‖ := norm_sub_le _ _
      _ = ‖Hn f‖+(1/2 : ℝ)*‖Hm f‖ := by rw [norm_smul,hhalf]
      _ ≤ (C*((2 : ℝ)^j)^(-(1/2 : ℝ))*(Real.log ((2 : ℝ)^j))^1*‖f‖)+
          (1/2 : ℝ)*(C*((2 : ℝ)^j)^(-(1/2 : ℝ))*(Real.log ((2 : ℝ)^j))^1*‖f‖) :=
        add_le_add (hhn f) (mul_le_mul_of_nonneg_left (hhm f) (by norm_num))
      _ = (C+(1/2 : ℝ)*C)*(((2 : ℝ)^j)^(-(1/2 : ℝ))*(Real.log ((2 : ℝ)^j))^1*‖f‖) := by simp only [Real.rpow_one,pow_one];ring
      _ ≤ (3*C)*(((2 : ℝ)^j)^(-(1/2 : ℝ))*(Real.log ((2 : ℝ)^j))^1*‖f‖) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
      _ = _ := by simp only [Real.rpow_one,pow_one];ring

end PrimeSquares
