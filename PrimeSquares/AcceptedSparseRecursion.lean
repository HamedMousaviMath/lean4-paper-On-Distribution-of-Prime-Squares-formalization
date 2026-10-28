import PrimeSquares.GenericSourceSparse

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- The accepted definition chooses its admissibility coefficient after the
fixed radius. This supplies one threshold valid for every subsequent test. -/
theorem accepted_sparse_admissibility_threshold (C : ℝ) :
    ∃ A₀ : ℝ, 1 < A₀ ∧ 320 * max 1 C ≤ A₀ := by
  refine ⟨320 * max 1 C, ?_, le_rfl⟩
  have hm : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  linarith

theorem accepted_general_dyadic_sparse_recursion {C : ℝ}
    (T : PositiveDyadicConvolutionFamily C) (m : ℕ) (hC : C ≤ (m : ℝ))
    (Ψ : ℝ → ℝ → ℝ) :
    ∃ A₀ : ℝ, 1 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∀ K : ℝ, 0 < K → SourceDyadicLocalEstimate T m Ψ K A →
      ∃ Kout : ℝ, 0 < Kout ∧ ∀ F G : Finset ℤ,
        ∃ S : Finset SparseIntegerInterval, IntegerSparseFamily (1/4) S ∧
          |genericFullDyadicPairing T F G| ≤
            Kout * ∑ I ∈ S, genericDensitySparseCost m Ψ I F G := by
  obtain ⟨A₀, hA₀, hA⟩ := accepted_sparse_admissibility_threshold C
  refine ⟨A₀, hA₀, ?_⟩
  intro A hAA K hK hlocal
  exact source_dyadic_sparse_recursion_full_domain T m hC Ψ hK (hA.trans hAA) hlocal

end PrimeSquares
