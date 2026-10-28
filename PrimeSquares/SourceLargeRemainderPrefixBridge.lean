import PrimeSquares.SourceHighIntervalBridge
import PrimeSquares.SourceLargeHighRemainder
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceLargeRemainder_prefix_bridge (M N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0 < Q) (hR : 0 ≤ R) (hRM : R ≤ M) (hq₀ : 0 < q₀)
    (active : Bool) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ)
    (f : ℓ²(ℤ,ℂ)) (go ge : lp (fun _ : ℤ => ℝ) 2)
    (ho : ∀ S,0 ≤ S → ∀ x,‖integerMultiplier (realTruncatedCircleSymbol (M+1) S
      (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleRationalModelTerm N hN χ (fun _ => 0) β))) f x‖ ≤ go x)
    (he : ∀ S,0 ≤ S → ∀ x,‖integerMultiplier (realTruncatedCircleSymbol (M+1) S
      (rationalCircleDenominatorBlock (canonicalRationalCenters M)
        (circleExceptionalHigh N hN q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β))) f x‖ ≤ ge x) :
    ∀ x,‖integerMultiplier (sourceLargeHighRemainder N hN Q R q₀ active χ β) f x‖ ≤ 2*(go x+ge x) := by
  intro x
  have hcap := sourceRadius_filter_cap hR M hRM
  have hw := (effectiveCollarCutoff_pos hQ hq₀).le
  have hOrd := sourceOrdinary_large_band M N hN hQ.le hR χ β
  have hExc := sourceExceptional_large_band M N hN hw hR q₀ Q (conductorMajorant q₀) χ (sourceExceptionalSelector q₀ active) β
  rw [hcap] at hOrd hExc
  unfold sourceLargeHighRemainder
  rw [hOrd,hExc,integerMultiplier_sub,integerMultiplier_sub,integerMultiplier_sub,
    _root_.sub_apply,_root_.sub_apply,_root_.sub_apply,lp.coeFn_sub,lp.coeFn_sub,lp.coeFn_sub]
  simp only [Pi.sub_apply]
  have htri (a b c d : ℂ) : ‖(a-b)-(c-d)‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    have h1 := norm_sub_le (a-b) (c-d)
    have h2 := norm_sub_le a b
    have h3 := norm_sub_le c d
    linarith
  have h1 := ho R hR x
  have h2 := ho (min Q R) (le_min hQ.le hR) x
  have h3 := he R hR x
  have h4 := he (min (effectiveCollarCutoff Q q₀) R) (le_min hw hR) x
  exact (htri _ _ _ _).trans (by linarith only [h1,h2,h3,h4])
end PrimeSquares
