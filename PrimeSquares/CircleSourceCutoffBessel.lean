import PrimeSquares.FiniteDisjointMultiplierBessel
import PrimeSquares.CircleSourceCutoffDisjoint
import PrimeSquares.CircleSourceCutoffPointwiseBound
open Finset
open scoped lp
namespace PrimeSquares
theorem circleSourceCutoff_bessel {s : ℕ} (hs : 2 ≤ s) (S : Finset ℚ)
    (hc : ∀ r ∈ S,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ S,(r.den : ℝ) ≤ (2 : ℝ)^(s+1)) (f : ℓ²(ℤ,ℂ)) :
    (∑ r ∈ S,‖integerMultiplier (circleSourceCutoff s r) f‖^2) ≤ ‖f‖^2 := by
  simpa only [one_pow,one_mul] using finite_disjoint_multiplier_bessel S (circleSourceCutoff s)
    (fun r hr t ht hrt => circleSourceCutoff_disjoint hs (hc r hr) (hc t ht) hrt (hd r hr) (hd t ht))
    (by norm_num : (0 : ℝ) ≤ 1) (fun r _ => circleSourceCutoff_pointwise_norm (by omega) r) f
end PrimeSquares
