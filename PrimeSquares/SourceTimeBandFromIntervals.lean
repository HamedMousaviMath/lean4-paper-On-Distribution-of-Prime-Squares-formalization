import PrimeSquares.SourceTimePrefixFromIntervals
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem source_time_band_from_intervals (M h : ℕ) (hM : M+1 ≤ 2^h)
    (F : ℕ → ℚ → C(PrimeCircle,ℂ)) (f : ℓ²(ℤ,ℂ))
    (G : ℕ → ℕ → lp (fun _ : ℤ => ℝ) 2) (w : ℕ → ℝ) (hw : ∀ i,0 ≤ w i)
    {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t k b x,‖integerMultiplier (intervalCircleSymbol b (2^k)
      (rationalCircleDenominatorBlock (canonicalRationalCenters M) (F t))) f x‖ ≤ G k b x)
    (hI : ∀ k b,‖G k b‖^2 ≤ B^2*intervalRealBudget b (2^k) w) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t Q R,0 ≤ Q → 0 ≤ R → ∀ x,‖integerMultiplier
        (∑ r ∈ (canonicalRationalCenters M).filter
          (fun r => (r.den : ℝ) ≤ R ∧ Q < (r.den : ℝ)),F t r) f x‖ ≤ g x) ∧
      ‖g‖ ≤ 2*((h+1 : ℝ)*B*Real.sqrt (intervalRealBudget 0 (2^h) w)) := by
  obtain ⟨g,hg,ht,hn⟩ := source_time_prefix_from_intervals M h hM F f G w hw hB hG hI
  refine ⟨(2 : ℝ) • g,fun x => mul_nonneg (by norm_num) (hg x),?_,?_⟩
  · intro t Q R hQ hR x
    have hp (S : ℝ) (hS : 0 ≤ S) :
        ‖integerMultiplier (realTruncatedCircleSymbol (M+1) S
          (rationalCircleDenominatorBlock (canonicalRationalCenters M) (F t))) f x‖ ≤ g x := by
      simpa only [sourceCircle_symbol_prefix M hS] using ht t S hS x
    rw [rationalCircle_real_band _ M
      (fun r hr => ((mem_canonicalRationalCenters M r).mp hr).2) hQ hR,
      integerMultiplier_sub,_root_.sub_apply,lp.coeFn_sub,Pi.sub_apply]
    change ‖_ - _‖ ≤ 2*g x
    exact (norm_sub_le _ _).trans (by linarith [hp R hR,hp (min Q R) (le_min hQ hR)])
  · simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2)] using
      mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2)
end PrimeSquares
