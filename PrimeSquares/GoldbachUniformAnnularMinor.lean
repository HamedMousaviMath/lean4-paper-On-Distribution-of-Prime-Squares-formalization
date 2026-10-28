import PrimeSquares.GoldbachMinorArcGeometry

set_option autoImplicit false
namespace PrimeSquares

noncomputable def goldbachPrimeExponentialConstant (D : UniformRenGhoshInputs) : ℝ :=
  renSourceConstant D.renConstant+ghoshSourceConstant D.ghoshConstant

theorem goldbachPrimeExponentialConstant_nonneg (D : UniformRenGhoshInputs) :
    0≤goldbachPrimeExponentialConstant D :=
  add_nonneg (renSourceConstant_nonneg D.ren_nonneg) (ghoshSourceConstant_nonneg D.ghosh_nonneg)

/-- The common annular bound is derived from the already recorded independent
raw Ren/Ghosh input; no Goldbach pointwise estimate is an assumption. -/
theorem goldbach_common_annular_minor (D : UniformRenGhoshInputs)
    (N : ℕ) (hN : 1≤N) (ξ : ℝ) {H R : ℝ}
    (hH4 : 4≤H) (hstart : (D.startingScale:ℝ)≤H) (hExp : Real.exp 1≤H)
    (hR : 1≤R) (hmin : 1≤R*(H/(N:ℝ))^2) (hpower : R^4≤H/2)
    (hout : (ξ:PrimeCircle)∈GoldbachMinorArcs N R) :
    ∀ m : ℕ,m≤N → H<(m:ℝ) →
      ‖annularWeightedSquareAverageSymbol m ArithmeticFunction.vonMangoldt (ξ:PrimeCircle)‖≤
        goldbachPrimeExponentialConstant D*(Real.log N)^D.logarithmicPower*
          (R*(H/(N:ℝ))^2)^(-(1/4:ℝ)) := by
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hH : 0≤H := by linarith
  intro m hm hml
  have hm4 : 4≤m := by exact_mod_cast hH4.trans hml.le
  have hms : D.startingScale≤m := by exact_mod_cast hstart.trans hml.le
  have hmR : (0:ℝ)<m := hH.trans_lt hml
  have hlM : 1≤Real.log m := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hExp.trans hml.le)
  have hrH : H/(N:ℝ)≤(m:ℝ)/(N:ℝ) := div_le_div_of_nonneg_right hml.le hnR.le
  have hminS : R*(H/(N:ℝ))^2≤R*((m:ℝ)/(N:ℝ))^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrH 2) (by linarith)
  have hS1 : 1≤R*((m:ℝ)/(N:ℝ))^2 := hmin.trans hminS
  have hratio : (m:ℝ)/(N:ℝ)≤1 := (div_le_one hnR).mpr (by exact_mod_cast hm)
  have hratio2 : ((m:ℝ)/(N:ℝ))^2≤1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by positivity) hratio 2
  have hSR : R*((m:ℝ)/(N:ℝ))^2≤R := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio2 (by linarith : 0≤R)
  have hS4 : (R*((m:ℝ)/(N:ℝ))^2)^4≤(m:ℝ)/2 :=
    (pow_le_pow_left₀ (by positivity) hSR 4).trans
      (hpower.trans (div_le_div_of_nonneg_right hml.le (by norm_num : (0:ℝ)≤2)))
  have hOutM := goldbach_minor_arcs_rescale N m (by omega) hm (by linarith : 0≤R) hout
  have ha := annularMangoldt_outside_major_quarter_bound hm4 D.ren_nonneg D.ghosh_nonneg
    D.power_nonneg hS1 hS4 hlM hOutM (D.ren m hms ξ) (D.ghosh m hms ξ)
  have hlogMN : Real.log m≤Real.log N := Real.log_le_log hmR (by exact_mod_cast hm)
  have hLP : (Real.log m)^D.logarithmicPower≤(Real.log N)^D.logarithmicPower :=
    Real.rpow_le_rpow (by linarith) hlogMN D.power_nonneg
  have hRP := Real.rpow_le_rpow_of_nonpos (by linarith : 0<R*(H/(N:ℝ))^2)
    hminS (by norm_num : (-(1/4:ℝ))≤0)
  calc
    _≤goldbachPrimeExponentialConstant D*(Real.log m)^D.logarithmicPower*
      (R*((m:ℝ)/(N:ℝ))^2)^(-(1/4:ℝ)) := ha
    _≤_ := mul_le_mul
      (mul_le_mul_of_nonneg_left hLP (goldbachPrimeExponentialConstant_nonneg D)) hRP
      (by positivity) (mul_nonneg (goldbachPrimeExponentialConstant_nonneg D)
        (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN)) _))

theorem goldbach_prime_minor_from_numeric_parameters (D : UniformRenGhoshInputs)
    (N : ℕ) (hN : 1≤N) (ξ : ℝ) {H R : ℝ}
    (hH4 : 4≤H) (hstart : (D.startingScale:ℝ)≤H) (hExp : Real.exp 1≤H)
    (hR : 1≤R) (hmin : 1≤R*(H/(N:ℝ))^2) (hpower : R^4≤H/2)
    (hout : (ξ:PrimeCircle)∈GoldbachMinorArcs N R)
    (U : ℝ) (hU : 0≤U) (hUN : U≤N) :
    ‖goldbachPrimeSquarePolynomial U (ξ:PrimeCircle)‖≤
      (2*(goldbachPrimeExponentialConstant D*(Real.log N)^D.logarithmicPower*
        (R*(H/(N:ℝ))^2)^(-(1/4:ℝ)))*(N:ℝ)+H*Real.log N)/Real.log 2+
          (2/Real.log 2)*Real.sqrt N*Real.log N := by
  have hH : 0≤H := by linarith
  have hbudget : 0≤goldbachPrimeExponentialConstant D*(Real.log N)^D.logarithmicPower*
      (R*(H/(N:ℝ))^2)^(-(1/4:ℝ)) := by
    have hp := goldbachPrimeExponentialConstant_nonneg D
    have hl : 0≤Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    positivity
  have hparts := goldbach_mangoldt_partials_from_annular N hN ξ hH hbudget
    (goldbach_common_annular_minor D N hN ξ hH4 hstart hExp hR hmin hpower hout)
  apply goldbach_prime_from_mangoldt_partials N hN (ξ:PrimeCircle) _ hparts U hU hUN
  have hl : 0≤Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  positivity

end PrimeSquares
