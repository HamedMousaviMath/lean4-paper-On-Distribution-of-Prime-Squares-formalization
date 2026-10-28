import PrimeSquares.GenericKernelTesting

set_option autoImplicit false
open Finset
open scoped NNReal
namespace PrimeSquares

noncomputable def genericFullDyadicMaximum {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (F : Finset ℤ) (x : ℤ) : ℝ := ⨆ j : ℕ,‖positiveDyadicValue T j F x‖

theorem genericFullDyadicMaximum_bdd {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K) (F : Finset ℤ) (x : ℤ) :
    BddAbove (Set.range (fun j : ℕ => ‖positiveDyadicValue T j F x‖)) := by
  refine ⟨K*Ψ (2*(m:ℝ)+1) 1,?_⟩
  rintro _ ⟨j,rfl⟩
  exact genericLocalHypothesis_uniform_indicator_bound T m hC Ψ hlocal j F x

theorem genericFullDyadicMaximum_nonneg {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K) (F : Finset ℤ) (x : ℤ) :
    0 ≤ genericFullDyadicMaximum T F x :=
  (norm_nonneg _).trans (le_ciSup (genericFullDyadicMaximum_bdd T m hC Ψ hlocal F x) 0)

theorem genericFullDyadicMaximum_half_attained {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K) (F : Finset ℤ) (x : ℤ) :
    ∃ j : ℕ,genericFullDyadicMaximum T F x ≤ 2*‖positiveDyadicValue T j F x‖ := by
  have h0 := genericFullDyadicMaximum_nonneg T m hC Ψ hlocal F x
  by_cases hz : genericFullDyadicMaximum T F x=0
  · refine ⟨0,?_⟩
    rw [hz]
    positivity
  · have hp : 0 < genericFullDyadicMaximum T F x := lt_of_le_of_ne h0 (Ne.symm hz)
    have hex : ∃ j : ℕ,genericFullDyadicMaximum T F x/2 < ‖positiveDyadicValue T j F x‖ := by
      by_contra! h
      have hh : genericFullDyadicMaximum T F x ≤ genericFullDyadicMaximum T F x/2 := ciSup_le h
      linarith
    obtain ⟨j,hj⟩ := hex
    exact ⟨j,by linarith⟩

theorem genericFullDyadicMaximum_finite_test {C K : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (m : ℕ) (hC : C ≤ (m:ℝ)) (Ψ : ℝ → ℝ → ℝ)
    (hlocal : GenericRestrictedLocalEstimate T m Ψ K) (F G : Finset ℤ) :
    ∃ J : Finset ℕ,(∑ x ∈ G,genericFullDyadicMaximum T F x) ≤
      2*∑ x ∈ G,(genericDyadicMaximum T J F x:ℝ) := by
  classical
  choose j hj using genericFullDyadicMaximum_half_attained T m hC Ψ hlocal F
  let J := G.image j
  refine ⟨J,?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  have hmajor : ‖positiveDyadicValue T (j x) F x‖ ≤ (genericDyadicMaximum T J F x:ℝ) := by
    exact_mod_cast (Finset.le_sup (f:=fun i => ‖positiveDyadicValue T i F x‖₊)
      (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
  exact (hj x).trans (mul_le_mul_of_nonneg_left hmajor (by norm_num))

end PrimeSquares
