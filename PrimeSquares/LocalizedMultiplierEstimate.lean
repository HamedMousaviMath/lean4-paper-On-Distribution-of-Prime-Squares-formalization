import PrimeSquares.UniformDisjointRealMaximum
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem integerMultiplier_localized (m p : C(PrimeCircle,ℂ)) (hm : m=m*p) (f : ℓ²(ℤ,ℂ)) :
    integerMultiplier m f=integerMultiplier m (integerMultiplier p f) := by
  rw [integerMultiplier_comp_apply,←hm]
theorem integerMultiplier_localized_norm (m p : C(PrimeCircle,ℂ)) (hm : m=m*p) (f : ℓ²(ℤ,ℂ)) :
    ‖integerMultiplier m f‖ ≤ ‖m‖*‖integerMultiplier p f‖ := by
  rw [integerMultiplier_localized m p hm f]
  exact integerMultiplier_norm_le m _
end PrimeSquares
