import PrimeSquares.DyadicEndpointReconstruction

open Finset
namespace PrimeSquares

theorem finiteSetDensity_scale_antitone {S T : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (F G : Finset ℤ) : finiteSetDensity T F G ≤ finiteSetDensity S F G := by
  exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sq_pos_of_pos hS) (pow_le_pow_left₀ hS.le hST 2)

theorem primeSquare_annular_comparison (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ A : ℝ,0 < A ∧ ∀ k : ℕ,∀ F G : Finset ℤ,∀ δ : ℝ,0 < δ → δ ≤ 1 →
      δ ≤ finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G →
      ‖restrictedKernelPairing (annularWeightedSquareAverageKernel (2^k)
        ArithmeticFunction.vonMangoldt) F G‖/(((2^k : ℕ) : ℝ)^2) ≤
        A*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*paperPhi cstar (1/2) δ := by
  obtain ⟨A,hA,h⟩ := primeSquare_annular_endpoint_dyadic HP D hCS HS hstar
  have hc : 0 ≤ cstar := (by positivity : (0 : ℝ) ≤ 4*Real.sqrt 3/9).trans hstar.le
  have hB := primeSquareChebyshevConstant_pos
  refine ⟨A+primeSquareChebyshevConstant,add_pos hA hB,?_⟩
  intro k F G δ hδ hδ1 hδd
  have hS : (0 : ℝ) < (((2^k : ℕ) : ℝ)^2) := by positivity
  have hd : 0 < finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G := hδ.trans_le hδd
  by_cases hd1 : finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G ≤ 1
  · have hb := h k F G ((div_le_one (sq_pos_of_pos hS)).mp hd1)
    have hΦ := paperPhi_half_antitone hc hδ hδd hd1
    exact hb.trans (by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (show A ≤ A+primeSquareChebyshevConstant by linarith)
          (Real.rpow_nonneg hd.le (2/3 : ℝ))
      · exact hΦ
      · exact (paperPhi_pos _ _ _).le
      · positivity)
  · have hb := restrictedKernelPairing_l2_normalized
      (mangoldtSquareKernel_l2_bound (by positivity : 0 < (2 : ℕ)^k)).2 hS F G
    have hpow : (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(1/2 : ℝ) ≤
        (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hd1) (by norm_num)
    exact hb.trans (by
      calc
        _ ≤ primeSquareChebyshevConstant*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow hB.le
        _ ≤ (A+primeSquareChebyshevConstant)*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le _)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (paperPhi_one_le hc _ _))

theorem dyadic_descending_ratio (k j : ℕ) (hj : j ≤ k) :
    (((2^(k-j) : ℕ) : ℝ)/((2^k : ℕ) : ℝ))=((2 : ℝ)^j)⁻¹ := by
  push_cast
  have hprod : (2 : ℝ)^(k-j)*(2 : ℝ)^j=(2 : ℝ)^k := by
    rw [←pow_add,Nat.sub_add_cancel hj]
  field_simp
  exact hprod

theorem primeSquare_full_endpoint_dyadic (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ A : ℝ,0 < A ∧ ∀ k : ℕ,∀ F G : Finset ℤ,
      (F.card : ℝ)*(G.card : ℝ) ≤ (((2^k : ℕ) : ℝ)^2)^2 →
      ‖restrictedKernelPairing (weightedSquareAverageKernel (2^k)
        ArithmeticFunction.vonMangoldt) F G‖/(((2^k : ℕ) : ℝ)^2) ≤
        A*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
          paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G) := by
  obtain ⟨A,hA,h⟩ := primeSquare_annular_comparison HP D hCS HS hstar
  obtain ⟨hr0,hr1⟩ := dyadic_decay_ratio (by norm_num : (0 : ℝ) < 1/3)
  let R : ℝ := (2 : ℝ)^(-(1/3 : ℝ))
  have hden : 0 < 1-R := sub_pos.mpr hr1
  refine ⟨A/(1-R),div_pos hA hden,?_⟩
  intro k F G hFG
  have hN : (0 : ℝ) < ((2^k : ℕ) : ℝ) := by positivity
  have hδ0 : 0 ≤ finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  by_cases hδz : finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G=0
  · have hprod : (F.card : ℝ)*(G.card : ℝ)=0 := (div_eq_zero_iff.mp hδz).resolve_right (by positivity)
    rcases mul_eq_zero.mp hprod with hf|hg
    · have hf0 : F=∅ := card_eq_zero.mp (by exact_mod_cast hf)
      subst F
      simp only [restrictedKernelPairing_empty_left,norm_zero,zero_div,finiteSetDensity,card_empty,Nat.cast_zero,zero_mul,
        Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0),mul_zero,zero_div,zero_mul,le_refl]
    · have hg0 : G=∅ := card_eq_zero.mp (by exact_mod_cast hg)
      subst G
      simp only [restrictedKernelPairing_empty_right,norm_zero,zero_div,finiteSetDensity,card_empty,Nat.cast_zero,mul_zero,
        Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0),zero_mul,mul_zero,zero_div,le_refl]
  have hδ : 0 < finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G := lt_of_le_of_ne hδ0 (Ne.symm hδz)
  have hδ1 : finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G ≤ 1 :=
    (div_le_one (by positivity)).mpr hFG
  let T : ℝ := A*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
    paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)
  have hT : 0 ≤ T := by dsimp [T];exact mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hδ.le _)) (paperPhi_pos _ _ _).le
  have hterm (j : ℕ) (hj : j ∈ range k) :
      ‖((2 : ℂ)^j)⁻¹*restrictedKernelPairing (annularWeightedSquareAverageKernel (2^(k-j))
        ArithmeticFunction.vonMangoldt) F G‖/(((2^k : ℕ) : ℝ)^2) ≤ T*R^j := by
    have hjk : j ≤ k := (mem_range.mp hj).le
    have hM : (0 : ℝ) < ((2^(k-j) : ℕ) : ℝ) := by positivity
    have hMN : (((2^(k-j) : ℕ) : ℝ)^2) ≤ (((2^k : ℕ) : ℝ)^2) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.sub_le k j)) 2
    have hb := h (k-j) F G _ hδ hδ1 (finiteSetDensity_scale_antitone (by positivity) hMN F G)
    have hc := (div_le_iff₀ (by positivity : (0 : ℝ) < (((2^(k-j) : ℕ) : ℝ)^2))).mp hb
    have hratio := dyadic_descending_ratio k j hjk
    have hprof : ((((2^(k-j) : ℕ) : ℝ)/((2^k : ℕ) : ℝ)))^(1/3 : ℝ)=R^j := by
      rw [hratio,Real.inv_rpow (by positivity),dyadic_pow_rpow,←inv_pow,
        ←Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [norm_mul,norm_inv,norm_pow,show ‖(2 : ℂ)‖=(2 : ℝ) by norm_num]
    calc
      _ ≤ (((2 : ℝ)^j)⁻¹)*(A*(finiteSetDensity (((2^(k-j) : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
          paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)*(((2^(k-j) : ℕ) : ℝ)^2))/
          (((2^k : ℕ) : ℝ)^2) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) (sq_nonneg _)
      _ = T*R^j := by
        rw [square_density_ratio hM hN F G,←hratio]
        have he := square_endpoint_rescale hM hN hδ.le
        rw [hprof] at he
        dsimp [T]
        convert congrArg (fun t : ℝ => A*paperPhi cstar (1/2)
          (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)*t) he using 1 <;> ring

  rw [mangoldtPairing_dyadic_reconstruction]
  calc
    _ ≤ (∑ j ∈ range k,‖((2 : ℂ)^j)⁻¹*restrictedKernelPairing
        (annularWeightedSquareAverageKernel (2^(k-j)) ArithmeticFunction.vonMangoldt) F G‖)/
        (((2^k : ℕ) : ℝ)^2) := div_le_div_of_nonneg_right (norm_sum_le _ _) (sq_nonneg _)
    _ = ∑ j ∈ range k,‖((2 : ℂ)^j)⁻¹*restrictedKernelPairing
        (annularWeightedSquareAverageKernel (2^(k-j)) ArithmeticFunction.vonMangoldt) F G‖/
        (((2^k : ℕ) : ℝ)^2) := sum_div _ _ _
    _ ≤ ∑ j ∈ range k,T*R^j := sum_le_sum hterm
    _ = T*∑ j ∈ range k,R^j := (mul_sum _ _ _).symm
    _ ≤ T*(1-R)⁻¹ := mul_le_mul_of_nonneg_left
      ((summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum (range k) (fun n _ => pow_nonneg hr0.le n) |>.trans_eq
        (tsum_geometric_of_lt_one hr0.le hr1)) hT
    _ = _ := by dsimp [T];ring

end PrimeSquares
