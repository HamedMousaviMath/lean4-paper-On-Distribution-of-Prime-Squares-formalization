import PrimeSquares.TwistedQuadratic

/-! Finite orthogonality bounds for the genuine twisted quadratic sum. -/

open Finset

namespace PrimeSquares

theorem twistedGauss_energy_complex (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ((∑ b : ZMod q, ‖twistedUnitQuadraticGaussSum q χ b‖ ^ 2 : ℝ) : ℂ) =
      (q : ℂ) * ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        if (u : ZMod q) ^ 2 = (v : ZMod q) ^ 2 then
          χ u * (starRingEnd ℂ) (χ v) else 0 := by
  classical
  have hn (b : ZMod q) : ((‖twistedUnitQuadraticGaussSum q χ b‖ ^ 2 : ℝ) : ℂ) =
      twistedUnitQuadraticGaussSum q χ b * (starRingEnd ℂ) (twistedUnitQuadraticGaussSum q χ b) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_sum, hn]
  unfold twistedUnitQuadraticGaussSum
  simp_rw [map_sum, sum_mul_sum, map_mul, conj_stdAddChar]
  have term (b : ZMod q) (u v : (ZMod q)ˣ) :
      (χ u * ZMod.stdAddChar (b * (u : ZMod q) ^ 2)) *
        ((starRingEnd ℂ) (χ v) * ZMod.stdAddChar (-(b * (v : ZMod q) ^ 2))) =
      (χ u * (starRingEnd ℂ) (χ v)) *
        ZMod.stdAddChar (((u : ZMod q) ^ 2 - (v : ZMod q) ^ 2) * b) := by
    calc
      _ = (χ u * (starRingEnd ℂ) (χ v)) *
          (ZMod.stdAddChar (b * (u : ZMod q) ^ 2) *
            ZMod.stdAddChar (-(b * (v : ZMod q) ^ 2))) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        congr 1
        ring
  simp_rw [term]
  calc
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, ∑ b : ZMod q,
        (χ u * (starRingEnd ℂ) (χ v)) *
          ZMod.stdAddChar (((u : ZMod q) ^ 2 - (v : ZMod q) ^ 2) * b) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro u _
      rw [sum_comm]
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        (χ u * (starRingEnd ℂ) (χ v)) *
          (if (u : ZMod q) ^ 2 = (v : ZMod q) ^ 2 then (q : ℂ) else 0) := by
      simp_rw [← mul_sum, sum_stdAddChar_mul, sub_eq_zero]
    _ = _ := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      split_ifs <;> ring

theorem twistedGauss_energy_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ b : ZMod q, ‖twistedUnitQuadraticGaussSum q χ b‖ ^ 2) ≤
      (q : ℝ) * q.totient * unitSquareRootCount q := by
  classical
  have he := congrArg Complex.re (twistedGauss_energy_complex q χ)
  simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, apply_ite, Complex.zero_re] at he
  rw [he]
  calc
    _ ≤ (q : ℝ) * ∑ u : (ZMod q)ˣ, (unitSquareRootCount q : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      apply sum_le_sum
      intro u _
      calc
        _ ≤ ∑ v : (ZMod q)ˣ, if (u : ZMod q) ^ 2 = (v : ZMod q) ^ 2 then (1 : ℝ) else 0 := by
          apply sum_le_sum
          intro v _
          split_ifs
          · have hn : ‖χ u * (starRingEnd ℂ) (χ v)‖ = 1 := by
              simp only [norm_mul, χ.unit_norm_eq_one, RCLike.norm_conj, mul_one]
            exact (Complex.re_le_norm _).trans_eq hn
          · exact le_rfl
        _ = ((univ.filter (fun v : (ZMod q)ˣ => (v : ZMod q) ^ 2 = (u : ZMod q) ^ 2)).card : ℝ) := by
          simp only [eq_comm, sum_boole]
        _ ≤ _ := by
          have hc : (univ.filter (fun v : (ZMod q)ˣ =>
              (v : ZMod q) ^ 2 = (u : ZMod q) ^ 2)).card ≤ unitSquareRootCount q := by
            simpa only [one_mul] using unitSquareFiber_card_le q 1 ((u : ZMod q) ^ 2) isUnit_one
          exact Nat.cast_le.mpr hc
    _ = _ := by simp [ZMod.card_units_eq_totient]; ring

theorem sum_comp_le_fiber_bound {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (g : X → Y) (f : Y → ℝ) (K : ℕ) (hf : ∀ y, 0 ≤ f y)
    (hK : ∀ y, (univ.filter (fun x => g x = y)).card ≤ K) :
    (∑ x, f (g x)) ≤ (K : ℝ) * ∑ y, f y := by
  classical
  rw [← sum_fiberwise univ g (fun x => f (g x)), mul_sum]
  apply sum_le_sum
  intro y _
  calc
    _ = ((univ.filter (fun x => g x = y)).card : ℝ) * f y := by
      calc
        _ = ∑ x ∈ univ.filter (fun x => g x = y), f y := by
          apply sum_congr rfl
          intro x hx
          rw [(mem_filter.mp hx).2]
        _ = _ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hK y) (hf y)

theorem norm_twistedUnitQuadraticGaussSum_le_roots (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a : ZMod q) (ha : IsUnit a) :
    ‖twistedUnitQuadraticGaussSum q χ a‖ ≤ (unitSquareRootCount q : ℝ) * Real.sqrt q := by
  classical
  have horbit := sum_comp_le_fiber_bound
    (fun u : (ZMod q)ˣ => a * (u : ZMod q) ^ 2)
    (fun b => ‖twistedUnitQuadraticGaussSum q χ b‖ ^ 2)
    (unitSquareRootCount q) (fun _ => sq_nonneg _)
    (fun b => unitSquareFiber_card_le q a b ha)
  simp only [norm_twistedUnitQuadraticGaussSum_mul_unit_sq, sum_const, card_univ,
    ZMod.card_units_eq_totient, nsmul_eq_mul] at horbit
  have he := twistedGauss_energy_le q χ
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hk : (0 : ℝ) ≤ unitSquareRootCount q := Nat.cast_nonneg _
  have hs := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg q)
  have hsq : ‖twistedUnitQuadraticGaussSum q χ a‖ ^ 2 ≤
      (unitSquareRootCount q : ℝ) ^ 2 * q := by
    have h := horbit.trans (mul_le_mul_of_nonneg_left he hk)
    nlinarith [h]
  have hnn := norm_nonneg (twistedUnitQuadraticGaussSum q χ a)
  have hscale : ((unitSquareRootCount q : ℝ) * Real.sqrt q) ^ 2 =
      (unitSquareRootCount q : ℝ) ^ 2 * q := by rw [mul_pow, hs2]
  rw [← hscale] at hsq
  exact (sq_le_sq₀ hnn (mul_nonneg hk hs)).mp hsq

end PrimeSquares
