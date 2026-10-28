import PrimeSquares.PrimeCountingNormalization

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem prime_sum_le_mangoldt_partial_bound {N : ℕ} (hN : 2 ≤ N)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ m : ℕ, (∑ n ∈ Ioc 0 m, ArithmeticFunction.vonMangoldt n*u n) ≤ (m : ℝ)*B) :
    (∑ p ∈ Nat.primesLE N, u p) ≤ (6*(N : ℝ)/Real.log (N : ℝ))*B := by
  classical
  let m := ⌊Real.sqrt (N : ℝ)⌋₊
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hm : (m : ℝ) ≤ Real.sqrt (N : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hs2 := Real.sq_sqrt hNp.le
  have hmlog : (m : ℝ)*Real.log (N : ℝ) ≤ 2*(N : ℝ) := by
    have h := mul_le_mul hm (real_log_le_two_sqrt hNp) (by linarith : 0 ≤ Real.log (N : ℝ)) hs0
    nlinarith
  have hmdiv : (m : ℝ) ≤ 2*(N : ℝ)/Real.log (N : ℝ) := (le_div_iff₀ hlog).mpr hmlog
  have hweight (n : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt n*u n :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hu n)
  have hmajor (p : ℕ) (hp : p ∈ Nat.primesLE N) :
      u p ≤ (2/Real.log (N : ℝ))*(ArithmeticFunction.vonMangoldt p*u p)+
        (if p ≤ m then 2*(ArithmeticFunction.vonMangoldt p*u p) else 0) := by
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    have hpLog : (1/2 : ℝ) ≤ Real.log (p : ℝ) :=
      real_log_two_half_le.trans (Real.log_le_log (by norm_num) hp2)
    by_cases hpm : p ≤ m
    · rw [ite_eq_left hpm, ArithmeticFunction.vonMangoldt_apply_prime hprime]
      have h := mul_le_mul_of_nonneg_right hpLog (hu p)
      have hpos : 0 ≤ (2/Real.log (N : ℝ))*(Real.log (p : ℝ)*u p) :=
        mul_nonneg (by positivity) (mul_nonneg (by linarith) (hu p))
      nlinarith
    · rw [ite_eq_right hpm, add_zero, ArithmeticFunction.vonMangoldt_apply_prime hprime]
      have hroot : Real.sqrt (N : ℝ) < (p : ℝ) :=
        (Nat.floor_lt (Real.sqrt_nonneg _)).mp (show m < p by omega)
      have hlogp := Real.log_le_log (Real.sqrt_pos.mpr hNp) hroot.le
      rw [Real.log_sqrt hNp.le] at hlogp
      rw [show (2/Real.log (N : ℝ))*(Real.log (p : ℝ)*u p) =
        (2*Real.log (p : ℝ)*u p)/Real.log (N : ℝ) by ring]
      apply (le_div_iff₀ hlog).mpr
      have h := mul_le_mul_of_nonneg_right hlogp (hu p)
      nlinarith
  have hsubN : Nat.primesLE N ⊆ Ioc 0 N := by
    intro p hp
    exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
  have hsubm : (Nat.primesLE N).filter (fun p => p ≤ m) ⊆ Ioc 0 m := by
    intro p hp
    obtain ⟨hp, hpm⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, hpm⟩
  have hsumN := sum_le_sum_of_subset_of_nonneg hsubN (fun n _ _ => hweight n)
  have hsumm := sum_le_sum_of_subset_of_nonneg hsubm (fun n _ _ => hweight n)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, ((2/Real.log (N : ℝ))*(ArithmeticFunction.vonMangoldt p*u p)+
        (if p ≤ m then 2*(ArithmeticFunction.vonMangoldt p*u p) else 0)) := sum_le_sum hmajor
    _ = (2/Real.log (N : ℝ))*(∑ p ∈ Nat.primesLE N, ArithmeticFunction.vonMangoldt p*u p)+
        2*(∑ p ∈ (Nat.primesLE N).filter (fun p => p ≤ m), ArithmeticFunction.vonMangoldt p*u p) := by
      rw [sum_add_distrib, ←sum_filter]
      simp only [←mul_sum]
    _ ≤ (2/Real.log (N : ℝ))*((N : ℝ)*B)+2*((m : ℝ)*B) :=
      add_le_add (mul_le_mul_of_nonneg_left (hsumN.trans (hpartial N)) (by positivity))
        (mul_le_mul_of_nonneg_left (hsumm.trans (hpartial m)) (by norm_num : (0 : ℝ) ≤ 2))
    _ ≤ (2/Real.log (N : ℝ))*((N : ℝ)*B)+2*((2*(N : ℝ)/Real.log (N : ℝ))*B) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmdiv hB) (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

theorem normalized_prime_sum_le_mangoldt_bound {N : ℕ} (hN : 2 ≤ N)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ m : ℕ, (∑ n ∈ Ioc 0 m, ArithmeticFunction.vonMangoldt n*u n) ≤ (m : ℝ)*B) :
    (Nat.primeCounting N : ℝ)⁻¹*(∑ p ∈ Nat.primesLE N, u p) ≤ 3072*B := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ (512*Real.log (N : ℝ)/(N : ℝ))*((6*(N : ℝ)/Real.log (N : ℝ))*B) :=
      mul_le_mul (primeCounting_inverse_bound hN) (prime_sum_le_mangoldt_partial_bound hN u hu hB hpartial)
        (sum_nonneg (fun p _ => hu p)) (by positivity)
    _ = _ := by field_simp; ring

end PrimeSquares
