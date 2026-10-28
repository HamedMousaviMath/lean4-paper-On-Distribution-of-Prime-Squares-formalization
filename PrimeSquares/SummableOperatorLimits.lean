import PrimeSquares.CountableEnvelopeCoordinates

open Filter
open scoped lp Topology
namespace PrimeSquares

theorem operator_outputs_summable
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Summable (fun j : ℕ => T j f) :=
  (hT.mul_right ‖f‖).of_norm_bounded (fun j => (T j).le_opNorm f)

theorem operator_outputs_tendsto_zero_l2
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) :
    Tendsto (fun j : ℕ => T j f) atTop (𝓝 0) :=
  (operator_outputs_summable T hT f).tendsto_atTop_zero

theorem operator_outputs_tendsto_zero_pointwise
    (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖)) (f : ℓ²(ℤ, ℂ)) (x : ℤ) :
    Tendsto (fun j : ℕ => T j f x) atTop (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (operator_coordinate_norm_summable T hT f x).tendsto_atTop_zero

end PrimeSquares
