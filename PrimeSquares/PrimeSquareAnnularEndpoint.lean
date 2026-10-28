import PrimeSquares.PrimeSquareDistributionInputs
import PrimeSquares.IndependentSquareDecomposition
import PrimeSquares.HighLowTheorem

namespace PrimeSquares

theorem primeSquare_leading_coefficient (c₁ : ℝ) :
    orliczLeadingCoefficient 1 (1/2) c₁ (1/2)=c₁*(2*Real.sqrt 3/9) := by
  have hs3 : (Real.sqrt (3 : ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have he : (2 : ℝ)^(1/2 : ℝ)*(3/2 : ℝ)^(3/2 : ℝ)=(3/2 : ℝ)*Real.sqrt 3 := by
    have hr := Real.rpow_add (by norm_num : (0 : ℝ) < 3/2) (1/2 : ℝ) 1
    norm_num only [show (1/2 : ℝ)+1=3/2 by norm_num,Real.rpow_one] at hr
    rw [hr,←mul_assoc]
    rw [←Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 3/2)]
    norm_num only [show (2 : ℝ)*(3/2)=3 by norm_num]
    rw [←Real.sqrt_eq_rpow]
    ring
  dsimp [orliczLeadingCoefficient]
  norm_num only [one_mul,show (1 : ℝ)+1/2=3/2 by norm_num,show (1/2 : ℝ)+1=3/2 by norm_num]
  rw [he]
  field_simp
  nlinarith [congrArg (fun x : ℝ => c₁*x) hs3]

theorem exists_primeSquare_high_coefficient {cstar : ℝ}
    (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ c₁ : ℝ,2 < c₁ ∧ orliczLeadingCoefficient 1 (1/2) c₁ (1/2) < cstar := by
  have ha : 0 < 2*Real.sqrt (3 : ℝ)/9 := by positivity
  have h2 : (2 : ℝ) < cstar/(2*Real.sqrt 3/9) := (lt_div_iff₀ ha).mpr (by nlinarith)
  obtain ⟨c₁,hc₁,hc₁'⟩ := exists_between h2
  refine ⟨c₁,hc₁,?_⟩
  rw [primeSquare_leading_coefficient]
  exact (lt_div_iff₀ ha).mp hc₁'

theorem primeSquare_annular_endpoint_large (HP : PrimeAsymptoticInputs)
    (D : PrimeSquareDistributionInputs) {CS cstar : ℝ} (hCS : 1 ≤ CS)
    (HS : FullSquareDecompositionInput CS) (hstar : 4*Real.sqrt 3/9 < cstar) :
    ∃ N₀ : ℕ,4 ≤ N₀ ∧ ∃ A : ℝ,0 < A ∧ ∀ k : ℕ,N₀ ≤ 2^k →
      ∀ F G : Finset ℤ,(F.card : ℝ)*(G.card : ℝ) ≤ (((2^k : ℕ) : ℝ)^2)^2 →
        ‖restrictedKernelPairing (annularWeightedSquareAverageKernel (2^k)
          ArithmeticFunction.vonMangoldt) F G‖/(((2^k : ℕ) : ℝ)^2) ≤
          A*(finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G)^(2/3 : ℝ)*
            paperPhi cstar (1/2) (finiteSetDensity (((2^k : ℕ) : ℝ)^2) F G) := by
  obtain ⟨c₁,hc₁,hcoeff⟩ := exists_primeSquare_high_coefficient hstar
  obtain ⟨N₀,hN₀,c₀,hc₀,CHi,hCHi,hdec⟩ := primeSquare_orlicz_decomposition_large HP D hc₁
  obtain ⟨_,_,A,hA,hendpoint⟩ := highLow_AB_endpoint
    (v := 1/2) (s := 1) (r := 1/2) (γ := 2) (β := 1) (CB := 3*CS)
    (a := 1) (α := 1) (c₀ := c₀) (c₁ := c₁) (c := 1/2) (κ := 1/2)
    (M := 0) (CLo := 4*lowSpatialConstant) (CHi := CHi) (CErr := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) hc₀ (by linarith) (by norm_num) (by norm_num) (by norm_num) hcoeff
  refine ⟨N₀,hN₀,A,hA,?_⟩
  intro k hk F G hFG
  have hpos : 0 < (2 : ℕ)^k := by positivity
  have hSr : (0 : ℝ) < (((2^k : ℕ) : ℝ)^2) := by positivity
  have he := annular_square_elementary_inputs hpos
  have hk0 : k ≠ 0 := by intro hz;rw [hz,pow_zero] at hk;omega
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hpow : 2^(l+1)=2*(2^l) := by rw [pow_succ,Nat.mul_comm]
  have H : HighLowEndpointInputs
      (annularWeightedSquareAverageKernel (2^(l+1)) ArithmeticFunction.vonMangoldt)
      (annularWeightedSquareAverageKernel (2^(l+1)) (fun _ => 1))
      (squareAverageWindow (2^(l+1)))
      (((2^(l+1) : ℕ) : ℝ)^2) (1/2) 1 (1/2) 2 1 (3*CS) 1 1 c₀ c₁ (1/2) (1/2) 0
      (4*lowSpatialConstant) CHi 8 := by
    refine ⟨he.square_nonnegative,?_,?_,?_,?_⟩
    · intro F x
      simpa only [Real.rpow_one] using he.domination F x
    · intro F x
      have hx : 0 ≤ ((((2^(l+1) : ℕ) : ℝ)^2)^(-(1/2 : ℝ)))*
          ‖finiteIndicatorLp (F ∩ squareAverageWindow (2^(l+1)) x) 1‖ := by positivity
      have hm := le_mul_of_one_le_left hx (by linarith : 1 ≤ 3*CS)
      simpa only [mul_assoc] using (he.local_bound F x).trans hm
    · intro j hj _
      rw [hpow]
      exact fullSquare_decomposition_annular_two_mul (by linarith : 0 ≤ CS) HS (2^l) (by positivity) j hj
    · intro j hj hcut
      exact hdec _ hk j hj hcut
  have h := (hendpoint _ _ _ _ hSr H F G hFG).2
  norm_num only [show (1 : ℝ)-1/(2*(1+1/2))=2/3 by norm_num] at h
  exact h

end PrimeSquares
