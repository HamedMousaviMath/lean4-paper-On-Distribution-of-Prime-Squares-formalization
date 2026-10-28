import PrimeSquares.CyclicFullSquareMeasures

set_option autoImplicit false
open Finset
namespace PrimeSquares

def differenceSecondEquiv (q : ℕ) : (ZMod q × ZMod q) ≃ (ZMod q × ZMod q) where
  toFun uv := (uv.1-uv.2, uv.2)
  invFun hy := (hy.1+hy.2, hy.2)
  left_inv uv := by ext <;> simp
  right_inv hy := by ext <;> simp

theorem zmod_two_kernel_card_le_two (q : ℕ) [NeZero q] :
    ((univ : Finset (ZMod q)).filter (fun h => 2*h = 0)).card ≤ 2 := by
  classical
  have hq := NeZero.pos q
  have hsub : ((univ : Finset (ZMod q)).filter (fun h => 2*h = 0)) ⊆
      {0, ((q/2 : ℕ) : ZMod q)} := by
    intro h hh
    have hh0 : (2 : ZMod q)*h = 0 := (mem_filter.mp hh).2
    have hd : q ∣ 2*h.val := (ZMod.natCast_eq_zero_iff _ q).mp (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using hh0)
    have hquot : 2*h.val/q < 2 := (Nat.div_lt_iff_lt_mul hq).mpr (by
      have hv := h.val_lt
      omega)
    have hdecomp := Nat.mod_add_div (2*h.val) q
    rw [Nat.mod_eq_zero_of_dvd hd, zero_add] at hdecomp
    have hcases : 2*h.val/q = 0 ∨ 2*h.val/q = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hquot)
    simp only [mem_insert, mem_singleton]
    rcases hcases with he | he
    · left
      rw [he, mul_zero] at hdecomp
      have hv : h.val = 0 := by omega
      calc
        h = (h.val : ZMod q) := (ZMod.natCast_zmod_val h).symm
        _ = 0 := by rw [hv, Nat.cast_zero]
    · right
      rw [he, mul_one] at hdecomp
      have hv : h.val = q/2 := by omega
      calc
        h = (h.val : ZMod q) := (ZMod.natCast_zmod_val h).symm
        _ = _ := by rw [hv]
  exact (card_le_card hsub).trans Finset.card_le_two

theorem completeQuadraticGaussSum_autocorrelation (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    completeQuadraticGaussSum q a*(starRingEnd ℂ) (completeQuadraticGaussSum q a) =
      ∑ h ∈ (univ : Finset (ZMod q)).filter (fun h => 2*h = 0),
        (q : ℂ)*ZMod.stdAddChar (a*h^2) := by
  classical
  unfold completeQuadraticGaussSum
  rw [map_sum, sum_mul_sum]
  simp_rw [conj_stdAddChar, ←AddChar.map_add_eq_mul]
  calc
    _ = ∑ hy : ZMod q × ZMod q, ZMod.stdAddChar (a*(hy.1+hy.2)^2-a*hy.2^2) := by
      rw [←Fintype.sum_prod_type (fun uv : ZMod q × ZMod q =>
        ZMod.stdAddChar (a*uv.1^2+ -(a*uv.2^2)))]
      apply Fintype.sum_equiv (differenceSecondEquiv q)
      intro uv
      congr 1
      dsimp [differenceSecondEquiv]
      ring
    _ = ∑ h : ZMod q, ZMod.stdAddChar (a*h^2)*
        ∑ y : ZMod q, ZMod.stdAddChar ((2*a*h)*y) := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro h _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      rw [←AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ h : ZMod q, if 2*h = 0 then (q : ℂ)*ZMod.stdAddChar (a*h^2) else 0 := by
      apply sum_congr rfl
      intro h _
      rw [sum_stdAddChar_mul]
      have he : 2*a*h = 0 ↔ 2*h = 0 := by
        rw [show 2*a*h = a*(2*h) by ring]
        exact ha.mul_right_eq_zero
      simp only [he]
      split_ifs <;> ring
    _ = _ := by rw [Finset.sum_filter]

theorem completeQuadraticGaussSum_norm_sq_le (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖completeQuadraticGaussSum q a‖^2 ≤ 2*(q : ℝ) := by
  let S := (univ : Finset (ZMod q)).filter (fun h => 2*h = 0)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hcard : (S.card : ℝ) ≤ 2 := by exact_mod_cast zmod_two_kernel_card_le_two q
  calc
    _ = ‖∑ h ∈ S, (q : ℂ)*ZMod.stdAddChar (a*h^2)‖ := by
      rw [←completeQuadraticGaussSum_autocorrelation q a ha, norm_mul, Complex.norm_conj]
      ring
    _ ≤ ∑ h ∈ S, ‖(q : ℂ)*ZMod.stdAddChar (a*h^2)‖ := norm_sum_le _ _
    _ = (S.card : ℝ)*(q : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hq

theorem completeQuadraticGaussSum_norm_le (q : ℕ) [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    ‖completeQuadraticGaussSum q a‖ ≤ 2*Real.sqrt (q : ℝ) := by
  have h := completeQuadraticGaussSum_norm_sq_le q a ha
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hg := norm_nonneg (completeQuadraticGaussSum q a)
  nlinarith

end PrimeSquares
