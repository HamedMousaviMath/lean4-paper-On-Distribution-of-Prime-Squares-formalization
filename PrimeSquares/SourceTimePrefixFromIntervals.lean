import PrimeSquares.SourceRadiusCapIdentity
import PrimeSquares.TimePrefixRademacherMenshov
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem source_time_prefix_from_intervals (M h : ℕ) (hM : M+1 ≤ 2^h)
    (F : ℕ → ℚ → C(PrimeCircle,ℂ)) (f : ℓ²(ℤ,ℂ))
    (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) (w : ℕ → ℝ) (hw : ∀ i,0 ≤ w i)
    {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t k b x,‖integerMultiplier (intervalCircleSymbol b (2^k)
      (rationalCircleDenominatorBlock (canonicalRationalCenters M) (F t))) f x‖ ≤ G k b x)
    (hI : ∀ k b,‖G k b‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t R,0 ≤ R → ∀ x,‖integerMultiplier
        (∑ r ∈ (sourceRationalCenters R).filter (fun r => r.den ≤ M),F t r) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*Real.sqrt (intervalRealBudget 0 (2^h) w) := by
  obtain ⟨g,hg,ht,hn⟩ := time_prefix_rademacherMenshov h 0
    (fun t i x => integerMultiplier (rationalCircleDenominatorBlock (canonicalRationalCenters M) (F t) i) f x)
    G w hw hB (fun t k b x => by
      rw [←intervalL2Sum_apply,←integerMultiplier_interval]
      exact hG t k b x) hI
  refine ⟨g,hg,?_,hn⟩
  intro t R hR x
  rw [sourceCircle_symbol_prefix M hR,realTruncatedCircleSymbol_prefix (M+1) hR,
    integerMultiplier_interval,intervalL2Sum_apply]
  exact ht t _ ((min_le_left _ _).trans hM) x
end PrimeSquares
