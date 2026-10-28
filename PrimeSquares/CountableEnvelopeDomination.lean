import PrimeSquares.CountableEnvelopeCoordinates

open Finset
open scoped lp
namespace PrimeSquares

theorem countableOperatorEnvelope_nonneg
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    0 ≤ countableOperatorEnvelope T f x := by
  rw [countableOperatorEnvelope_coordinate T hT f x]
  exact tsum_nonneg (fun j => norm_nonneg _)

theorem countableOperatorEnvelope_dominates
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (j : ℕ) (x : ℤ) :
    ‖T j f x‖ ≤ countableOperatorEnvelope T f x := by
  rw [countableOperatorEnvelope_coordinate T hT f x]
  exact (operator_coordinate_norm_summable T hT f x).le_tsum j (fun k _ => norm_nonneg _)

theorem finiteOperatorEnvelope_le_countable (S : Finset ℕ)
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    finiteOperatorEnvelope S T f x ≤ countableOperatorEnvelope T f x := by
  change (∑ j ∈ S, magnitudeL2 (T j f)) x ≤ _
  rw [lp.coeFn_sum,Finset.sum_apply,countableOperatorEnvelope_coordinate T hT f x]
  exact (operator_coordinate_norm_summable T hT f x).sum_le_tsum S (fun j _ => norm_nonneg _)

end PrimeSquares
