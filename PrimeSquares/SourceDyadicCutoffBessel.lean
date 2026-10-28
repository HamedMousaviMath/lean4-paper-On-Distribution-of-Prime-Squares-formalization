import PrimeSquares.SourceDyadicDenominatorBounds
import PrimeSquares.CircleSourceCutoffBessel
open Finset
open scoped lp
namespace PrimeSquares
theorem sourceDyadic_cutoff_bessel {s : ℕ} (hs : 2 ≤ s) (f : ℓ²(ℤ,ℂ)) :
    (∑ r ∈ sourceDyadicRationalCenters s,‖integerMultiplier (circleSourceCutoff s r) f‖^2) ≤ ‖f‖^2 :=
  circleSourceCutoff_bessel hs _ (fun r hr => ((mem_sourceDyadicRationalCenters s r).mp hr).1)
    (fun _ hr => (sourceDyadicRationalCenters_den_bounds hr).2.le) f
end PrimeSquares
