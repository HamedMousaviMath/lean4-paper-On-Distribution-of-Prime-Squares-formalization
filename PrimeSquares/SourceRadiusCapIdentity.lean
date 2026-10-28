import PrimeSquares.SourceExceptionalLargeBand
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceRadius_filter_cap {R : ℝ} (hR : 0 ≤ R) (M : ℕ) (hRM : R ≤ M) :
    (sourceRationalCenters R).filter (fun r => r.den ≤ M)=sourceRationalCenters R := by
  apply filter_eq_self.mpr
  intro r hr
  have hd := (mem_sourceRationalCenters hR r).mp hr
  exact_mod_cast (hd.2.trans hRM)
end PrimeSquares
