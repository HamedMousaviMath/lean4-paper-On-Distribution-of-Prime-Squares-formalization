import PrimeSquares.PrimeSquareFullDyadicEndpoint
import PrimeSquares.PrimeSquareCutoffComparison
import PrimeSquares.OrliczScaleComparison

namespace PrimeSquares

theorem square_density_bounded_ratio {N M K : ℝ} (hN : 0 < N) (hNM : N ≤ M)
    (_hK : 0 ≤ K) (hMN : M ≤ K*N) (F G : Finset ℤ) :
    finiteSetDensity (N^2) F G ≤ K^4*finiteSetDensity (M^2) F G := by
  have hM : 0 < M := hN.trans_le hNM
  rw [square_density_ratio hN hM F G]
  have hr : M/N ≤ K := (div_le_iff₀ hN).mpr hMN
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (div_nonneg hM.le hN.le) hr 4)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))

theorem primeSquare_full_endpoint (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ F G : Finset ℤ,
      (F.card : ℝ)*(G.card : ℝ) ≤ ((N : ℝ)^2)^2 →
      ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/
        ((N : ℝ)^2) ≤ A*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ)*
          paperPhi cstar (1/2) (finiteSetDensity ((N : ℝ)^2) F G) := by
  obtain ⟨A,hA,h⟩ := primeSquare_full_endpoint_dyadic HP D hCS HS hstar
  have hc : 0 ≤ cstar := (by positivity : (0 : ℝ) ≤ 4*Real.sqrt 3/9).trans hstar.le
  let C : ℝ := Real.exp (cstar*Real.sqrt (Real.log 16)/2)
  have hC : 0 < C := Real.exp_pos _
  refine ⟨8*A*C,by positivity,?_⟩
  intro N hN F G hFG
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨k,hNM,hMN⟩ := exists_dyadic_upper_nat N hN
  have hMr : (0 : ℝ) < ((2^k : ℕ) : ℝ) := by positivity
  have hNMr : (N : ℝ) ≤ ((2^k : ℕ) : ℝ) := by exact_mod_cast hNM
  have hMNr : ((2^k : ℕ) : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hMN
  have hSS := pow_le_pow_left₀ hNr.le hNMr 2
  have hδ0 : 0 ≤ finiteSetDensity ((N : ℝ)^2) F G :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hδM0 : 0 ≤ finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hδMN := finiteSetDensity_scale_antitone (sq_pos_of_pos hNr) hSS F G
  have hδ1 : finiteSetDensity ((N : ℝ)^2) F G ≤ 1 := (div_le_one (by positivity)).mpr hFG
  have hδ16 : finiteSetDensity ((N : ℝ)^2) F G ≤ 16*finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G := by
    simpa only [show (2 : ℝ)^4=16 by norm_num] using
      square_density_bounded_ratio hNr hNMr (by norm_num : (0 : ℝ) ≤ 2) hMNr F G
  by_cases hδz : finiteSetDensity ((N : ℝ)^2) F G=0
  · have hp : (F.card : ℝ)*(G.card : ℝ)=0 := (div_eq_zero_iff.mp hδz).resolve_right (by positivity)
    rcases mul_eq_zero.mp hp with hf|hg
    · have he : F=∅ := Finset.card_eq_zero.mp (by exact_mod_cast hf)
      subst F
      simp only [restrictedKernelPairing_empty_left,norm_zero,zero_div,finiteSetDensity,Finset.card_empty,Nat.cast_zero,zero_mul,
        Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0),mul_zero,zero_mul,zero_div,le_refl]
    · have he : G=∅ := Finset.card_eq_zero.mp (by exact_mod_cast hg)
      subst G
      simp only [restrictedKernelPairing_empty_right,norm_zero,zero_div,finiteSetDensity,Finset.card_empty,Nat.cast_zero,mul_zero,
        Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0),mul_zero,zero_mul,zero_div,le_refl]
  have hδ : 0 < finiteSetDensity ((N : ℝ)^2) F G := lt_of_le_of_ne hδ0 (Ne.symm hδz)
  have hδM : 0 < finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G := by nlinarith
  have hΦ : paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G) ≤
      C*paperPhi cstar (1/2) (finiteSetDensity ((N : ℝ)^2) F G) :=
    paperPhi_half_fixed_rescale hc hδM hδ1 (by norm_num) hδMN hδ16
  have hFGr : (F.card : ℝ)*(G.card : ℝ) ≤ (((2^k : ℕ) : ℝ)^2)^2 :=
    hFG.trans (pow_le_pow_left₀ (sq_nonneg _) hSS 2)
  have hb := h k F G hFGr
  have hpair := mangoldtSquarePairing_cutoff_bound hN hNM F G
  have hpow : (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ) ≤
      (finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ) :=
    Real.rpow_le_rpow hδM0 hδMN (by norm_num)
  have henv : A*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
      paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G) ≤
      A*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ)*
        (C*paperPhi cstar (1/2) (finiteSetDensity ((N : ℝ)^2) F G)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) hΦ (paperPhi_pos _ _ _).le (by positivity)
  have hratio : ((2^k : ℕ) : ℝ)/(N : ℝ) ≤ 2 := (div_le_iff₀ hNr).mpr hMNr
  have hRnon : 0 ≤ ((2^k : ℕ) : ℝ)/(N : ℝ) := div_nonneg hMr.le hNr.le
  have hRcube : (((2^k : ℕ) : ℝ)/(N : ℝ))^3 ≤ 8 := by
    simpa only [show (2 : ℝ)^3=8 by norm_num] using pow_le_pow_left₀ hRnon hratio 3
  calc
    _ ≤ (((2^k : ℕ) : ℝ)/(N : ℝ))*‖restrictedKernelPairing
        (weightedSquareAverageKernel (2^k) ArithmeticFunction.vonMangoldt) F G‖/(N : ℝ)^2 :=
      div_le_div_of_nonneg_right hpair (sq_nonneg _)
    _ = (((2^k : ℕ) : ℝ)/(N : ℝ))^3*(‖restrictedKernelPairing
        (weightedSquareAverageKernel (2^k) ArithmeticFunction.vonMangoldt) F G‖/
          (((2^k : ℕ) : ℝ)^2)) := by field_simp [hNr.ne',hMr.ne']
    _ ≤ 8*(A*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ)*
        (C*paperPhi cstar (1/2) (finiteSetDensity ((N : ℝ)^2) F G))) :=
      mul_le_mul hRcube (hb.trans henv) (div_nonneg (norm_nonneg _) (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

end PrimeSquares
