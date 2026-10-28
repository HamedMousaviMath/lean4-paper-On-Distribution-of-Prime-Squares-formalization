import PrimeSquares.CircleHighLowNormInputs
import PrimeSquares.HighLowOperators

open scoped lp
namespace PrimeSquares

/-- An explicit assembly theorem, not a proof of the two remaining analytic estimates.
The spatial scale is the square of the arithmetic length N. -/
theorem circleModel_operatorHighLowBound (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (q₀ : ℕ) (Q B₀ : ℝ) (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ)
    (β J s r γ δ C : ℝ)
    (hlo : ∀ x, ‖circleLowKernel Γ N hN q₀ Q B₀ χ κ β x‖ ≤
      C/(N : ℝ)^2*J^s*(Real.log J)^γ)
    (hhi : ∀ θ, ‖circleHighModel Γ N hN q₀ Q B₀ χ κ β θ +
      circleMajorArcError Γ N hN χ κ β θ‖ ≤ C*J^(-r)*(Real.log J)^δ) :
    OperatorHighLowBound (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt)
      ((N : ℝ)^2) J s r γ δ C := by
  let Lo := circleLowOperator Γ N hN q₀ Q B₀ χ κ β
  let Hm := circleHighModel Γ N hN q₀ Q B₀ χ κ β + circleMajorArcError Γ N hN χ κ β
  let Hi := integerMultiplier Hm
  have hL : ‖Lo‖ ≤ C/(N : ℝ)^2*J^s*(Real.log J)^γ :=
    circleLowOperator_kernel_bound Γ N hN q₀ Q B₀ χ κ β hlo
  have hB : 0 ≤ C*J^(-r)*(Real.log J)^δ := (norm_nonneg _).trans (hhi 0)
  have hH : ‖Hi‖ ≤ C*J^(-r)*(Real.log J)^δ := integerMultiplier_opNorm_le_of_bound Hm hB hhi
  refine ⟨Lo,Hi,?_,?_,?_⟩
  · intro F x
    have hd := annularKernel_finite_low_high_error Γ N hN q₀ Q B₀ χ κ β F (fun _ => 1) x
    simp only [finiteConvolution_indicator,finiteInputLp_one] at hd
    change indicatorConvolution _ F x = Lo (finiteIndicatorLp F 1) x + Hi (finiteIndicatorLp F 2) x
    dsimp [Lo,Hi,Hm]
    rw [integerMultiplier_add]
    simpa only [circleHighOperator,circleMajorArcErrorOperator,
      _root_.add_apply,lp.coeFn_add,Pi.add_apply,add_assoc] using hd
  · intro f
    exact (Lo.le_opNorm f).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · intro f
    exact (Hi.le_opNorm f).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))

end PrimeSquares
