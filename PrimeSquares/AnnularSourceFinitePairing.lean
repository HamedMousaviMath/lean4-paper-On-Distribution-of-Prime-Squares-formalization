import PrimeSquares.SourceHighFromLargeMajorant
import PrimeSquares.SourcePointwiseConvolutionBound
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem annularSource_finite_pairing (N : ℕ) (hN : 1 ≤ N) {Q R : ℝ} {q₀ : ℕ}
    (hQ : 0<Q) (hq₀ : 0<q₀) (hQR : Q ≤ R) (active : Bool)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (β : ℝ) (F S : Finset ℤ) (f : ℤ → ℂ)
    (gc gl ge : lp (fun _ : ℤ => ℝ) 2) (hgc : ∀ x,0 ≤ gc x)
    (hgl : ∀ x,0 ≤ gl x) (hge : ∀ x,0 ≤ ge x) (L : ℝ)
    (hlow : ∀ x ∈ S,‖circleLowOperator (sourceRationalCenters R) N hN q₀ Q (conductorMajorant q₀)
      χ (sourceExceptionalSelector q₀ active) β (finiteInputLp F f 1) x‖ ≤ L)
    (hc : ∀ x ∈ S,‖integerMultiplier (sourceCollarDifference N hN Q R q₀ active χ β) (finiteInputLp F f 2) x‖ ≤ gc x)
    (hl : ∀ x ∈ S,‖integerMultiplier (sourceLargeHighRemainder N hN Q R q₀ active χ β) (finiteInputLp F f 2) x‖ ≤ gl x)
    (he : ∀ x ∈ S,‖circleMajorArcErrorOperator (sourceRationalCenters R) N hN χ
      (sourceExceptionalSelector q₀ active) β (finiteInputLp F f 2) x‖ ≤ ge x) :
    (∑ x ∈ S,‖finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x‖) ≤
      (S.card : ℝ)*L+(‖gc‖+‖gl‖+‖ge‖)*Real.sqrt S.card := by
  have hs : (∑ x ∈ S,‖finiteConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F f x‖) ≤
      ∑ x ∈ S,(L+gc x+gl x+ge x) := by
    apply sum_le_sum
    intro x hx
    exact (annularConvolution_source_triangle N hN hQ hq₀ hQR active χ β F f x).trans
      (by linarith [hlow x hx,hc x hx,hl x hx,he x hx])
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul] at hs
  have h1 := real_l2_finite_sum_bound S gc (fun x _ => hgc x)
  have h2 := real_l2_finite_sum_bound S gl (fun x _ => hgl x)
  have h3 := real_l2_finite_sum_bound S ge (fun x _ => hge x)
  nlinarith
end PrimeSquares
