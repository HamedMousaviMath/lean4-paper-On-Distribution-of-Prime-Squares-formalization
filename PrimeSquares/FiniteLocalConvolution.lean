import PrimeSquares.PolynomialLocalMassBound
import PrimeSquares.FiniteDecayConvolution

namespace PrimeSquares

theorem finiteConvolution_local_mass (K : ℤ → ℂ) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H)
    (hK : ∀ z : ℤ, ‖K z‖ ≤ A/H*decayProfile H 10 z)
    (F : Finset ℤ) (f : ℤ → ℂ) (x : ℤ) :
    ‖finiteConvolution K F f x‖ ≤ 4*A*dyadicLocalMass H F (fun y => ‖f y‖) x := by
  calc
    _ ≤ A/H*∑ y ∈ F,decayProfile H 10 ((x-y : ℤ) : ℝ)*‖f y‖ :=
      finiteConvolution_profile_bound K hH 10 hK F f x
    _ ≤ A/H*(4*H*dyadicLocalMass H F (fun y => ‖f y‖) x) :=
      mul_le_mul_of_nonneg_left (polynomial_profile_local_mass hH F _ (fun y _ => norm_nonneg _) x) (div_nonneg hA hH.le)
    _ = _ := by field_simp

end PrimeSquares
