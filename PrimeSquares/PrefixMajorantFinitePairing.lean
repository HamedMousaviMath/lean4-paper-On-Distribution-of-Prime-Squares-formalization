import PrimeSquares.OrthogonalRademacherMenshov
open Finset
open scoped lp
namespace PrimeSquares
theorem prefix_majorant_finite_pairing (h a : ℕ) (F : ℕ → ℓ²(ℤ,ℂ)) (G : Finset ℤ) :
    (∑ x ∈ G,prefixL2Majorant h a F x) ≤
      Real.sqrt (h+1 : ℝ)*Real.sqrt (binaryTreeL2Energy h a F)*Real.sqrt G.card := by
  simpa only [prefixL2Majorant_norm] using real_l2_finite_sum_bound G (prefixL2Majorant h a F)
    (fun x _ => prefixL2Majorant_nonneg h a F x)
end PrimeSquares
