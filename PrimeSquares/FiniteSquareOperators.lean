import PrimeSquares.FiniteComplexInputs

/-!
# Actual finite weighted square-translation operators

Integer translations preserve every genuine finite-exponent lp norm.
Finite weighted averages are continuous complex-linear maps, with their
usual total-mass bound. No multiplier estimate or PNT input is assumed.
-/

open Finset
open scoped lp

namespace PrimeSquares

noncomputable def integerTranslateValue {P : ENNReal} (hp : 0 < P.toReal)
    (d : ℤ) (f : lp (fun _ : ℤ => ℂ) P) : lp (fun _ : ℤ => ℂ) P :=
  ⟨fun x => f (x-d), memℓp_gen
    ((Equiv.subRight d).summable_iff.mpr ((lp.memℓp f).summable hp))⟩

theorem integerTranslateValue_apply {P : ENNReal} (hp : 0 < P.toReal)
    (d : ℤ) (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    integerTranslateValue hp d f x = f (x-d) := rfl

theorem integerTranslateValue_norm {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (d : ℤ) (f : lp (fun _ : ℤ => ℂ) P) : ‖integerTranslateValue hp d f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  exact congrArg (fun t : ℝ => t ^ (1 / P.toReal))
    ((Equiv.subRight d).tsum_eq (fun x : ℤ => ‖f x‖ ^ P.toReal))

noncomputable def integerTranslate {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (d : ℤ) :
    lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) P :=
  LinearMap.mkContinuous
    { toFun := integerTranslateValue hp d
      map_add' := by intro f g; apply lp.ext; funext x; rfl
      map_smul' := by intro c f; apply lp.ext; funext x; rfl }
    1 (fun f => by
      change ‖integerTranslateValue hp d f‖ ≤ 1 * ‖f‖
      rw [integerTranslateValue_norm hp d f, one_mul])

theorem integerTranslate_apply {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (d : ℤ) (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    integerTranslate hp d f x = f (x-d) := rfl

theorem integerTranslate_norm {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (d : ℤ) (f : lp (fun _ : ℤ => ℂ) P) : ‖integerTranslate hp d f‖ = ‖f‖ :=
  integerTranslateValue_norm hp d f

theorem integerTranslate_opNorm_le {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (d : ℤ) : ‖integerTranslate hp d‖ ≤ 1 :=
  (integerTranslate hp d).opNorm_le_bound (by norm_num)
    (fun f => by rw [integerTranslate_norm hp d f, one_mul])

noncomputable def finiteSquareOperator {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 0 < P.toReal) (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    lp (fun _ : ℤ => ℂ) P →L[ℂ] lp (fun _ : ℤ => ℂ) P :=
  (c : ℂ) • ∑ n ∈ S, (w n : ℂ) • integerTranslate hp ((n : ℤ)^2)

theorem finiteSquareOperator_apply {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) (f : lp (fun _ : ℤ => ℂ) P) (x : ℤ) :
    finiteSquareOperator hp S c w f x = (c : ℂ) * ∑ n ∈ S, (w n : ℂ) * f (x-(n : ℤ)^2) := by
  simp only [finiteSquareOperator, _root_.smul_apply, _root_.sum_apply,
    lp.coeFn_smul, lp.coeFn_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    integerTranslate_apply]

theorem finiteSquareOperator_norm_le {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (S : Finset ℕ) (c : ℝ) (w : ℕ → ℝ) :
    ‖finiteSquareOperator hp S c w‖ ≤ |c| * ∑ n ∈ S, |w n| := by
  rw [finiteSquareOperator, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc
    _ ≤ ∑ n ∈ S, ‖(w n : ℂ) • integerTranslate hp ((n : ℤ)^2)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro n _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (integerTranslate_opNorm_le hp _)

theorem finiteSquareOperator_norm_le_mass {P : ENNReal} [Fact (1 ≤ P)] (hp : 0 < P.toReal)
    (S : Finset ℕ) {c : ℝ} (hc : 0 ≤ c) (w : ℕ → ℝ) (hw : ∀ n ∈ S, 0 ≤ w n) :
    ‖finiteSquareOperator hp S c w‖ ≤ c * ∑ n ∈ S, w n := by
  have h := finiteSquareOperator_norm_le hp S c w
  rwa [abs_of_nonneg hc, sum_congr rfl (fun n hn => abs_of_nonneg (hw n hn))] at h

end PrimeSquares
