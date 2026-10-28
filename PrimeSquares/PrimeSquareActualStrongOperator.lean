import PrimeSquares.PrimeSquareStrongImproving
import PrimeSquares.PrimeSquareSourceInterval

open scoped lp
namespace PrimeSquares

/-- The genuine finite weighted sum, viewed as an lp-to-lq map by inclusion. -/
noncomputable def primeSquareImprovingOperator {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hp : 0 < P.toReal) (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) (N : ℕ) :
    lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) Q :=
  (lpInclusion hPQ hQ).comp (weightedSquareAverage hp N ArithmeticFunction.vonMangoldt)

theorem primeSquareImprovingOperator_apply {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hp : 0 < P.toReal) (hPQ : P ≤ Q) (hQ : Q ≠ ⊤) (N : ℕ)
    (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    primeSquareImprovingOperator hp hPQ hQ N f x=
      Complex.ofReal ((N : ℝ)⁻¹)*∑ n ∈ Finset.Ioc 0 N,
        (ArithmeticFunction.vonMangoldt n : ℂ)*f (x-(n : ℤ)^2) := by
  exact weightedSquareAverage_apply hp N ArithmeticFunction.vonMangoldt f x

theorem primeSquare_actual_strong_uniform (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS)
    {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (hconj : Q.toReal=holderConjugate P.toReal) (hp : 3/2 < P.toReal) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N →
      ‖primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N‖ ≤
        A*((N : ℝ)^2)^(1-2/P.toReal) := by
  obtain ⟨A,hA,h⟩ := primeSquare_strong_kernel_uniform HP D hCS HS hP2 h2Q hQ hconj hp
  refine ⟨A,hA,?_⟩
  intro N hN
  obtain ⟨T,hT,hnT⟩ := h N hN
  let U := primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N
  have hU (F : Finset ℤ) (x : ℤ) :
      indicatorConvolution (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x=
        U (finiteIndicatorLp F P) x := by
    change indicatorConvolution (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x=
      lpInclusion (hP2.trans h2Q) hQ
        (weightedSquareAverage (by linarith : 0 < P.toReal) N ArithmeticFunction.vonMangoldt (finiteIndicatorLp F P)) x
    rw [lpInclusion_apply]
    have he := weightedSquareAverage_finiteInput (by linarith : 0 < P.toReal) N
      ArithmeticFunction.vonMangoldt F (fun _ => 1) x
    simpa only [finiteConvolution_indicator,finiteInputLp_one] using he
  have heq := kernelLp_realization_unique (ne_top_of_le_ne_top (by norm_num) hP2) T U hT hU
  simpa only [heq] using hnT

theorem improving_scale_comparison {S T p : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (hTS : T ≤ 4*S) (hp : 0 < p) (hp2 : p ≤ 2) :
    S^(1-2/p) ≤ (4 : ℝ)^(-(1-2/p))*T^(1-2/p) := by
  have hT : 0 < T := hS.trans_le hST
  have he : 1-2/p ≤ 0 := by
    have h := (one_le_div hp).mpr hp2
    linarith
  have hb : T/4 ≤ S := by linarith
  have h := Real.rpow_le_rpow_of_nonpos (div_pos hT (by norm_num)) hb he
  rw [Real.div_rpow hT.le (by norm_num : (0 : ℝ) ≤ 4)] at h
  exact h.trans_eq (by rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)];ring)

/-- The strong conclusion of source Theorem 1.1, with the exact source
interval normalization. The estimate holds for all lp inputs, hence also
for the inputs supported in the source interval. -/
theorem theorem_1_1_strong (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS)
    {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (hconj : Q.toReal=holderConjugate P.toReal) (hp : 3/2 < P.toReal) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ f : lp (fun _ : ℤ => ℂ) P,
      ‖primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N f‖/
        ((primeSquareSourceInterval N).card : ℝ)^(1/Q.toReal) ≤
      A*‖f‖/((primeSquareSourceInterval N).card : ℝ)^(1/P.toReal) := by
  obtain ⟨A,hA,h⟩ := primeSquare_actual_strong_uniform HP D hCS HS hP2 h2Q hQ hconj hp
  have hp0 : 0 < P.toReal := by linarith
  have hp1 : 1 < P.toReal := by linarith
  have hp2 : P.toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ENNReal) ≠ ⊤) hP2
  let C : ℝ := (4 : ℝ)^(-(1-2/P.toReal))
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨A*C,mul_pos hA hC,?_⟩
  intro N hN f
  obtain ⟨hSlo,hShi⟩ := primeSquareSourceInterval_card_bounds hN
  have hS : (0 : ℝ) < (N : ℝ)^2 := by positivity
  have hI : (0 : ℝ) < (primeSquareSourceInterval N).card := hS.trans_le hSlo
  have hb := (primeSquareImprovingOperator (by linarith : 0 < P.toReal) (hP2.trans h2Q) hQ N).le_opNorm f
  have hn := (h N hN).trans (mul_le_mul_of_nonneg_left
    (improving_scale_comparison hS hSlo hShi hp0 hp2) hA.le)
  have hout := hb.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hid : ((primeSquareSourceInterval N).card : ℝ)^(1-2/P.toReal)/
      ((primeSquareSourceInterval N).card : ℝ)^(1/Q.toReal)=
        ((primeSquareSourceInterval N).card : ℝ)^(-(1/P.toReal)) := by
    rw [←Real.rpow_sub hI,hconj,holderConjugate_reciprocal hp1]
    congr 1
    ring
  calc
    _ ≤ (A*(C*((primeSquareSourceInterval N).card : ℝ)^(1-2/P.toReal))*‖f‖)/
        ((primeSquareSourceInterval N).card : ℝ)^(1/Q.toReal) :=
      div_le_div_of_nonneg_right hout (Real.rpow_nonneg hI.le _)
    _ = (A*C)*‖f‖*(((primeSquareSourceInterval N).card : ℝ)^(1-2/P.toReal)/
        ((primeSquareSourceInterval N).card : ℝ)^(1/Q.toReal)) := by ring
    _ = _ := by rw [hid,Real.rpow_neg hI.le];ring

end PrimeSquares
