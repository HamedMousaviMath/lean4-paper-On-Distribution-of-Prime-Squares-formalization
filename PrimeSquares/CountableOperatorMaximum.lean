import PrimeSquares.CountableEnvelopeDomination

open scoped lp
namespace PrimeSquares

noncomputable def operatorMaximalValue
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) : ℝ :=
  ⨆ j : ℕ, ‖T j f x‖

theorem operatorNormValues_bddAbove
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    BddAbove (Set.range (fun j : ℕ => ‖T j f x‖)) := by
  refine ⟨countableOperatorEnvelope T f x,?_⟩
  rintro y ⟨j,rfl⟩
  exact countableOperatorEnvelope_dominates T hT f j x

theorem operatorMaximalValue_dominates
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (j : ℕ) (x : ℤ) :
    ‖T j f x‖ ≤ operatorMaximalValue T f x :=
  le_ciSup (operatorNormValues_bddAbove T hT f x) j

theorem operatorMaximalValue_nonneg
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    0 ≤ operatorMaximalValue T f x :=
  (norm_nonneg _).trans (operatorMaximalValue_dominates T hT f 0 x)

theorem operatorMaximalValue_le_envelope
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    operatorMaximalValue T f x ≤ countableOperatorEnvelope T f x :=
  ciSup_le (fun j => countableOperatorEnvelope_dominates T hT f j x)

end PrimeSquares
