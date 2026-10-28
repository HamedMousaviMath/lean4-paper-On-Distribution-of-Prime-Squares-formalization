import PrimeSquares.SourceDyadicDenominatorBounds
import PrimeSquares.CircleSourceCutoffDisjoint
namespace PrimeSquares
theorem sourceDyadic_circleCutoff_disjoint {s : ℕ} (hs : 2 ≤ s) {r t : ℚ}
    (hr : r ∈ sourceDyadicRationalCenters s) (ht : t ∈ sourceDyadicRationalCenters s)
    (hrt : r ≠ t) (θ : PrimeCircle) :
    circleSourceCutoff s r θ=0 ∨ circleSourceCutoff s t θ=0 :=
  circleSourceCutoff_disjoint hs ((mem_sourceDyadicRationalCenters s r).mp hr).1
    ((mem_sourceDyadicRationalCenters s t).mp ht).1 hrt
    (sourceDyadicRationalCenters_den_bounds hr).2.le (sourceDyadicRationalCenters_den_bounds ht).2.le θ
end PrimeSquares
