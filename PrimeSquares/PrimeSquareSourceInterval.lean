import PrimeSquares.PrimeSquareFullEndpoint

open Finset
namespace PrimeSquares

noncomputable def primeSquareSourceInterval (N : ℕ) : Finset ℤ :=
  Icc (-((N : ℤ)^2)) (2*(N : ℤ)^2)

theorem primeSquareSourceInterval_card (N : ℕ) :
    (primeSquareSourceInterval N).card=3*N^2+1 := by
  have he : 2*(N : ℤ)^2+1-(-((N : ℤ)^2))=((3*N^2+1 : ℕ) : ℤ) := by push_cast;ring
  rw [primeSquareSourceInterval,Int.card_Icc,he,Int.toNat_natCast]

theorem primeSquareSourceInterval_card_bounds {N : ℕ} (hN : 0 < N) :
    (N : ℝ)^2 ≤ ((primeSquareSourceInterval N).card : ℝ) ∧
      ((primeSquareSourceInterval N).card : ℝ) ≤ 4*(N : ℝ)^2 := by
  rw [primeSquareSourceInterval_card]
  push_cast
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  constructor <;> nlinarith [sq_nonneg (N : ℝ)]

theorem finiteSetDensity_scale_ratio {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (F G : Finset ℤ) :
    finiteSetDensity S F G=(T/S)^2*finiteSetDensity T F G := by
  dsimp [finiteSetDensity]
  field_simp [hS.ne',hT.ne']

theorem primeSquare_full_comparison (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ F G : Finset ℤ,∀ δ : ℝ,0 < δ → δ ≤ 1 →
      δ ≤ finiteSetDensity ((N : ℝ)^2) F G →
      ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/
        ((N : ℝ)^2) ≤ A*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ)*paperPhi cstar (1/2) δ := by
  obtain ⟨A,hA,h⟩ := primeSquare_full_endpoint HP D hCS HS hstar
  have hc : 0 ≤ cstar := (by positivity : (0 : ℝ) ≤ 4*Real.sqrt 3/9).trans hstar.le
  have hB := primeSquareChebyshevConstant_pos
  refine ⟨A+primeSquareChebyshevConstant,add_pos hA hB,?_⟩
  intro N hN F G δ hδ hδ1 hδd
  have hS : (0 : ℝ) < (N : ℝ)^2 := by positivity
  have hd : 0 < finiteSetDensity ((N : ℝ)^2) F G := hδ.trans_le hδd
  by_cases hd1 : finiteSetDensity ((N : ℝ)^2) F G ≤ 1
  · have hb := h N hN F G ((div_le_one (sq_pos_of_pos hS)).mp hd1)
    exact hb.trans (by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (show A ≤ A+primeSquareChebyshevConstant by linarith)
          (Real.rpow_nonneg hd.le (2/3 : ℝ))
      · exact paperPhi_half_antitone hc hδ hδd hd1
      · exact (paperPhi_pos _ _ _).le
      · positivity)
  · have hb := restrictedKernelPairing_l2_normalized (mangoldtSquareKernel_l2_bound hN).1 hS F G
    have hpow : (finiteSetDensity ((N : ℝ)^2) F G)^(1/2 : ℝ) ≤
        (finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hd1) (by norm_num)
    exact hb.trans (by
      calc
        _ ≤ primeSquareChebyshevConstant*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow hB.le
        _ ≤ (A+primeSquareChebyshevConstant)*(finiteSetDensity ((N : ℝ)^2) F G)^(2/3 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le _)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (paperPhi_one_le hc _ _))

/-- The first conclusion of source Theorem 1.1, with its exact interval,
normalization, density, operator, and every coefficient above 4 sqrt(3)/9.
All independent deep inputs remain visible parameters. -/
theorem theorem_1_1_restricted (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ A : ℝ,0 < A ∧ ∀ N : ℕ,0 < N → ∀ F G : Finset ℤ,
      F ⊆ primeSquareSourceInterval N → G ⊆ primeSquareSourceInterval N →
      ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/
        ((primeSquareSourceInterval N).card : ℝ) ≤
      A*(finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G)^(2/3 : ℝ)*
        paperPhi cstar (1/2) (finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G) := by
  obtain ⟨A,hA,h⟩ := primeSquare_full_comparison HP D hCS HS hstar
  refine ⟨A*(16 : ℝ)^(2/3 : ℝ),by positivity,?_⟩
  intro N hN F G hF hG
  obtain ⟨hSlo,hShi⟩ := primeSquareSourceInterval_card_bounds hN
  have hS : (0 : ℝ) < (N : ℝ)^2 := by positivity
  have hI : (0 : ℝ) < (primeSquareSourceInterval N).card := hS.trans_le hSlo
  have hFG : (F.card : ℝ)*(G.card : ℝ) ≤ ((primeSquareSourceInterval N).card : ℝ)^2 := by
    have hf : (F.card : ℝ) ≤ (primeSquareSourceInterval N).card := by exact_mod_cast card_le_card hF
    have hg : (G.card : ℝ) ≤ (primeSquareSourceInterval N).card := by exact_mod_cast card_le_card hG
    simpa only [pow_two] using mul_le_mul hf hg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hδ0 : 0 ≤ finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
  have hδ1 : finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G ≤ 1 := (div_le_one (sq_pos_of_pos hI)).mpr hFG
  by_cases hδz : finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G=0
  · have hp : (F.card : ℝ)*(G.card : ℝ)=0 := (div_eq_zero_iff.mp hδz).resolve_right (by positivity)
    rcases mul_eq_zero.mp hp with hf|hg
    · have he : F=∅ := card_eq_zero.mp (by exact_mod_cast hf)
      subst F
      simp only [restrictedKernelPairing_empty_left,norm_zero,zero_div,finiteSetDensity,card_empty,Nat.cast_zero,zero_mul,
        Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0),mul_zero,zero_div,zero_mul,le_refl]
    · have he : G=∅ := card_eq_zero.mp (by exact_mod_cast hg)
      subst G
      simp only [restrictedKernelPairing_empty_right,norm_zero,zero_div,finiteSetDensity,card_empty,Nat.cast_zero,mul_zero,
        Real.zero_rpow (by norm_num : (2/3 : ℝ) ≠ 0),zero_mul,mul_zero,zero_div,le_refl]
  have hδ : 0 < finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G := lt_of_le_of_ne hδ0 (Ne.symm hδz)
  have hb := h N hN F G _ hδ hδ1 (finiteSetDensity_scale_antitone hS hSlo F G)
  have hd : finiteSetDensity ((N : ℝ)^2) F G ≤
      16*finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G := by
    rw [finiteSetDensity_scale_ratio hS hI F G]
    have hr : ((primeSquareSourceInterval N).card : ℝ)/(N : ℝ)^2 ≤ 4 := (div_le_iff₀ hS).mpr hShi
    have hp := pow_le_pow_left₀ (div_nonneg hI.le hS.le) hr 2
    norm_num only [show (4 : ℝ)^2=16 by norm_num] at hp
    exact mul_le_mul_of_nonneg_right hp hδ0
  have hp := Real.rpow_le_rpow (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)) hd
    (by norm_num : (0 : ℝ) ≤ 2/3)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hδ0] at hp
  calc
    _ ≤ ‖restrictedKernelPairing (weightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F G‖/(N : ℝ)^2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) hS hSlo
    _ ≤ _ := hb
    _ ≤ A*((16 : ℝ)^(2/3 : ℝ)*(finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G)^(2/3 : ℝ))*
        paperPhi cstar (1/2) (finiteSetDensity ((primeSquareSourceInterval N).card : ℝ) F G) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA.le) (paperPhi_pos _ _ _).le
    _ = _ := by ring

end PrimeSquares
