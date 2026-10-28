import PrimeSquares.PrimeSquareFullEndpoint
import PrimeSquares.StrongImproving

open scoped lp
namespace PrimeSquares

theorem primeSquare_fixed_coefficient : 4*Real.sqrt (3 : ℝ)/9 < 2 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hs : Real.sqrt (3 : ℝ) < 3 := by nlinarith
  linarith

theorem primeSquare_restricted_power_uniform (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS q : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hq : 3/2 < q) (hq2 : q ≤ 2) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ F G : Finset ℤ,
      ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖ ≤
        A*((N : ℝ)^2)^(1-2/q)*(F.card : ℝ)^(1/q)*(G.card : ℝ)^(1/q) := by
  obtain ⟨A,hA,hendpoint⟩ := primeSquare_full_endpoint HP D hCS HS primeSquare_fixed_coefficient
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hgap : (1 : ℝ)/q < 2/3 := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3/2) hq
    norm_num only [show (1 : ℝ)/(3/2)=2/3 by norm_num] at h
    exact h
  obtain ⟨B,hB,hloss⟩ := density_power_phi_loss_nonneg
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 2) (div_pos (by norm_num) hq0) hgap
  let C : ℝ := A*B+primeSquareChebyshevConstant
  have hC : 0 < C := add_pos (mul_pos hA hB) primeSquareChebyshevConstant_pos
  refine ⟨C,hC,?_⟩
  intro N hN F G
  have hS : (0 : ℝ) < (N : ℝ)^2 := by positivity
  have hsmall : ∀ F G : Finset ℤ,(F.card : ℝ)*(G.card : ℝ) ≤ ((N : ℝ)^2)^2 →
      ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/(N : ℝ)^2 ≤
        (A*B)*(finiteSetDensity ((N : ℝ)^2) F G)^(1/q) := by
    intro F G hFG
    have hδ : 0 ≤ finiteSetDensity ((N : ℝ)^2) F G :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
    have hδ1 : finiteSetDensity ((N : ℝ)^2) F G ≤ 1 := (div_le_one (sq_pos_of_pos hS)).mpr hFG
    exact (hendpoint N hN F G hFG).trans (by
      have hm := mul_le_mul_of_nonneg_left (hloss _ hδ hδ1) hA.le
      simpa only [mul_assoc] using hm)
  have hall := restricted_pairing_globalization hS hq0 hq2 (mul_pos hA hB).le
    primeSquareChebyshevConstant_pos.le (mangoldtSquareKernel_l2_bound hN).1 hsmall F G
  have hdn := density_denormalize_bound hS hq1 F G hall
  simpa only [holderConjugate_scaling hq1,C] using hdn

theorem primeSquare_strong_kernel_uniform (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS)
    {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hP2 : P ≤ 2) (h2Q : 2 ≤ Q) (hQ : Q ≠ ⊤)
    (hconj : Q.toReal=holderConjugate P.toReal) (hp : 3/2 < P.toReal) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N →
      KernelLpBound (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) P Q
        (A*((N : ℝ)^2)^(1-2/P.toReal)) := by
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hP2
  have hp2 : P.toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ENNReal) ≠ ⊤) hP2
  by_cases he : P.toReal=2
  · have hPe : P=2 := by rw [←ENNReal.ofReal_toReal hP,he];norm_num
    have hQe : Q=2 := by rw [←ENNReal.ofReal_toReal hQ,hconj,he,holderConjugate_two];norm_num
    subst P Q
    refine ⟨primeSquareChebyshevConstant,primeSquareChebyshevConstant_pos,?_⟩
    intro N hN
    simpa only [ENNReal.toReal_ofNat,show (1 : ℝ)-2/2=0 by norm_num,Real.rpow_zero,mul_one] using
      (kernelLpBound_of_l2 (mangoldtSquareKernel_l2_bound hN).1 (by norm_num : (2 : ENNReal) ≤ 2)
        (by norm_num : (2 : ENNReal) ≤ 2) (by norm_num : (2 : ENNReal) ≠ ⊤))
  · have hp2' : P.toReal < 2 := lt_of_le_of_ne hp2 he
    let q : ℝ := (3/2+P.toReal)/2
    have hq : 3/2 < q := by dsimp [q];linarith
    have hqp : q < P.toReal := by dsimp [q];linarith
    have hq0 : 0 < q := by linarith
    obtain ⟨A,hA,hrest⟩ := primeSquare_restricted_power_uniform HP D hCS HS hq (by linarith)
    let C : ℝ := interpolationWeightConstant A primeSquareChebyshevConstant
      (1/q-1/P.toReal) (1/P.toReal-1/2)*(3 : ℝ)^(2/P.toReal)
    obtain ⟨ha,hb⟩ := interpolation_gaps_pos hq0 hqp hp2'
    have hC : 0 ≤ C := mul_nonneg
      (interpolationWeightConstant_nonneg hA.le primeSquareChebyshevConstant_pos.le ha hb) (by positivity)
    refine ⟨1+C,by positivity,?_⟩
    intro N hN
    have hk := restricted_l2_strong_improving hP2 h2Q hQ hconj (by linarith)
      (by positivity : (0 : ℝ) < (N : ℝ)^2) hq0 hqp hp2' hA.le primeSquareChebyshevConstant_pos.le
      (finiteSquareKernel_nonnegative _ (by positivity) _ (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg))
      (mangoldtSquareKernel_l2_bound hN).1 (hrest N hN)
    obtain ⟨T,hT,hnT⟩ := hk
    refine ⟨T,hT,hnT.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith : C ≤ 1+C) (by positivity)

end PrimeSquares
