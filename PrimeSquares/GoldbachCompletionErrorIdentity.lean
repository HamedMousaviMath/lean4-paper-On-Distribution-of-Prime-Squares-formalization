import PrimeSquares.GoldbachCompletionArithmetic

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap
namespace PrimeSquares

noncomputable def goldbachCompletedMainTerm (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R U W : ℝ) (n : ℤ) : ℂ :=
  ∑ i∈I,(d i*goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W)/((i.1:ℂ)*(i.2.totient:ℂ))*
    goldbachArithmeticFactor R i.2 (i.1:ℤ) (a i:ℤ) n

noncomputable def goldbachSmallCompletionError (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R U W : ℝ) (n : ℤ) : ℂ :=
  ∑ i∈I,(d i*(goldbachHardSingularIntegral N i.1 R (n:ℝ) U W-goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W))/
    ((i.1:ℂ)*(i.2.totient:ℂ))*(∑ q∈Icc 1 ⌊R⌋₊,generalCoefficient q i.2 (i.1:ℤ) (a i:ℤ) n)

noncomputable def goldbachAddedCompletionError (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R Y U W : ℝ) (n : ℤ) : ℂ :=
  ∑ r∈goldbachAddedCompletionCenters R Y,realFourierPhase (-(n:ℝ)*(r:ℝ))*
    (∫ γ : ℝ,goldbachSmoothMajorFamilyIntegrand ψ N R I (fun i=>(a i:ℤ)) d U W r γ*realFourierPhase (-(n:ℝ)*γ))

noncomputable def goldbachFarCompletionError (ψ : 𝓢(ℝ,ℝ)) (N : ℕ) (I : Finset (ℕ×ℕ))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (R Y U W : ℝ) (n : ℤ) : ℂ :=
  ∑ i∈I,(d i*goldbachSingularIntegral ψ N i.1 R (n:ℝ) U W)/((i.1:ℂ)*(i.2.totient:ℂ))*
    (∑ q∈(goldbachCompletionDivisors R).filter (fun q : ℕ=>Y<(q:ℝ)),generalCoefficient q i.2 (i.1:ℤ) (a i:ℤ) n)

theorem goldbach_completion_error_identity (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (N : ℕ) (hN : 1≤N) (hlog : 1≤Real.log N) (L B : ℝ) (V : ℕ→ℝ)
    (hB : 0≤B) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ →(ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B))
    (a : ℕ×ℕ→ℕ) (ha : ∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (a i:ℤ))
    (d : ℕ×ℕ→ℂ) (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1)
    {R Y U W : ℝ} (hR : 2≤R) (hRY : R≤Y) (hsep : 2*R^3<(N:ℝ)^2) (hc : R/(N:ℝ)^2<1/2)
    (hU : 2≤U) (hUN : U≤N) (hW : 2≤W) (n : ℤ) :
    goldbachMajorModelCoefficient N (goldbachCoefficientIndices L V) a d R U W n-
      goldbachCompletedMainTerm ψ N (goldbachCoefficientIndices L V) a d R U W n=
      goldbachSmallCompletionError ψ N (goldbachCoefficientIndices L V) a d R U W n-
        goldbachAddedCompletionError ψ N (goldbachCoefficientIndices L V) a d R Y U W n-
        goldbachFarCompletionError ψ N (goldbachCoefficientIndices L V) a d R Y U W n := by
  classical
  let I := goldbachCoefficientIndices L V
  have hI : ∀ i∈I,0 < i.1 := fun i hi=>((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
  have hModel := goldbach_actual_major_model_identity N hN hlog L B V hB hL hV a ha d hd
    (by linarith : 1≤R) hsep hc hU hUN hW n
  have hAdded := goldbach_added_completion_identity ψ hψ N (by omega) I hI (fun i=>(a i:ℤ)) d
    hU hUN hW (by linarith : 0≤Y) R n
  rw [hModel]
  unfold goldbachCompletedMainTerm goldbachSmallCompletionError goldbachAddedCompletionError goldbachFarCompletionError
  rw [hAdded]
  dsimp only [I]
  simp only [←sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  have hk := ((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).2.2.1
  let : NeZero i.2 := ⟨hk.ne'⟩
  rw [goldbach_completion_arithmetic_split hR hRY i.2 (i.1:ℤ) (a i:ℤ) n (ha i hi)]
  ring

end PrimeSquares
