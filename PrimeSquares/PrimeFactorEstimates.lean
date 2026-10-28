import PrimeSquares.ElementaryPrimeProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Elementary estimates for a set of prime divisors

No prime number theorem is used in this file. The threshold inequality retains
the Chebyshev correction instead of assuming an extremizing prime set.
-/

open Finset Filter

namespace PrimeSquares

noncomputable def primeTheta (y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log (p : ℝ)

noncomputable def primeInvSqrtSum (y : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊y⌋₊, (Real.sqrt (p : ℝ))⁻¹

theorem primeFactors_log_budget (q : ℕ) (hq : 0 < q) :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log q := by
  have hp : 0 < ∏ p ∈ q.primeFactors, p :=
    prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  calc
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) :=
      (Real.log_prod fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero).symm
    _ = Real.log (∏ p ∈ q.primeFactors, p : ℕ) := by rw [Nat.cast_prod]
    _ ≤ Real.log q := Real.log_le_log (by exact_mod_cast hp)
      (by exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))

theorem finite_threshold_bound (S T : Finset ℕ) (f g : ℕ → ℝ) (c L : ℝ)
    (hc : 0 ≤ c) (hbudget : ∑ p ∈ S, g p ≤ L)
    (hsmall : ∀ p ∈ T, 0 ≤ f p - c * g p)
    (hlarge : ∀ p ∈ S, p ∉ T → f p - c * g p ≤ 0) :
    (∑ p ∈ S, f p) ≤ (∑ p ∈ T, f p) + c * (L - ∑ p ∈ T, g p) := by
  classical
  have hres : (∑ p ∈ S, (f p - c * g p)) ≤ ∑ p ∈ T, (f p - c * g p) := by
    calc
      _ ≤ ∑ p ∈ S, if p ∈ T then f p - c * g p else 0 := by
        apply sum_le_sum
        intro p hp
        split_ifs with h
        · exact le_rfl
        · exact hlarge p hp h
      _ = ∑ p ∈ S.filter (fun p => p ∈ T), (f p - c * g p) := by rw [sum_filter]
      _ ≤ ∑ p ∈ T, (f p - c * g p) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp; exact (mem_filter.mp hp).2
        · intro p hp _; exact hsmall p hp
  simp only [sum_sub_distrib, ← mul_sum] at hres
  nlinarith [mul_le_mul_of_nonneg_left hbudget hc]

theorem sqrt_mul_log_mono {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    Real.sqrt x * Real.log x ≤ Real.sqrt y * Real.log y := by
  exact mul_le_mul (Real.sqrt_le_sqrt hxy)
    (Real.log_le_log (by linarith) hxy) (Real.log_nonneg hx) (Real.sqrt_nonneg y)

theorem primeFactors_inv_sqrt_threshold (q : ℕ) (hq : 0 < q)
    (y : ℝ) (hy : 2 ≤ y) :
    (∑ p ∈ q.primeFactors, (Real.sqrt (p : ℝ))⁻¹) ≤
      primeInvSqrtSum y + (Real.log q - primeTheta y) / (Real.sqrt y * Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  have hd : 0 < Real.sqrt y * Real.log y := mul_pos (Real.sqrt_pos.mpr hy0) hl
  let T := Nat.primesLE ⌊y⌋₊
  have hmem (p : ℕ) (hp : p.Prime) : p ∈ T ↔ (p : ℝ) ≤ y := by
    simp only [T, Nat.mem_primesLE, hp, and_true]
    exact Nat.le_floor_iff hy0.le
  have hs : ∀ p ∈ T, 0 ≤ (Real.sqrt (p : ℝ))⁻¹ -
      (Real.sqrt y * Real.log y)⁻¹ * Real.log (p : ℝ) := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
    have hr : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hprime.pos)
    have hm := mul_le_mul_of_nonneg_left
      (sqrt_mul_log_mono hp1 ((hmem p hprime).mp hp)) (inv_nonneg.mpr hd.le)
    rw [inv_mul_cancel₀ hd.ne'] at hm
    have : (Real.sqrt y * Real.log y)⁻¹ * Real.log (p : ℝ) ≤
        1 / Real.sqrt (p : ℝ) := (le_div_iff₀ hr).mpr (by nlinarith [hm])
    simpa only [one_div] using sub_nonneg.mpr this
  have hb : ∀ p ∈ q.primeFactors, p ∉ T →
      (Real.sqrt (p : ℝ))⁻¹ -
        (Real.sqrt y * Real.log y)⁻¹ * Real.log (p : ℝ) ≤ 0 := by
    intro p hp hpt
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpY : y ≤ (p : ℝ) := le_of_lt (lt_of_not_ge (fun h => hpt ((hmem p hprime).mpr h)))
    have hr : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hprime.pos)
    have hm := mul_le_mul_of_nonneg_left (sqrt_mul_log_mono (by linarith) hpY)
      (inv_nonneg.mpr hd.le)
    rw [inv_mul_cancel₀ hd.ne'] at hm
    have : 1 / Real.sqrt (p : ℝ) ≤
        (Real.sqrt y * Real.log y)⁻¹ * Real.log (p : ℝ) :=
      (div_le_iff₀ hr).mpr (by nlinarith [hm])
    simpa only [one_div] using sub_nonpos.mpr this
  simpa only [primeInvSqrtSum, primeTheta, T, div_eq_mul_inv, mul_comm]
    using finite_threshold_bound q.primeFactors T
      (fun p => (Real.sqrt (p : ℝ))⁻¹) (fun p => Real.log (p : ℝ))
      (Real.sqrt y * Real.log y)⁻¹ (Real.log q) (inv_nonneg.mpr hd.le)
      (primeFactors_log_budget q hq) hs hb

theorem primeFactors_reciprocal_bound (q : ℕ) (hq : 0 < q)
    (hL : 2 ≤ Real.log q) :
    (∑ p ∈ q.primeFactors, (p : ℝ)⁻¹) ≤
      1 + Real.log (Real.log q) + (Real.log 2)⁻¹ := by
  classical
  let L : ℝ := Real.log q
  have hL0 : 0 < L := by dsimp [L]; linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let S := q.primeFactors
  let A : Finset ℕ := S.filter (fun p : ℕ => (p : ℝ) ≤ L)
  let B : Finset ℕ := S.filter (fun p : ℕ => ¬ (p : ℝ) ≤ L)
  have hA : (∑ p ∈ A, (p : ℝ)⁻¹) ≤ 1 + Real.log L := by
    calc
      _ ≤ ∑ p ∈ Icc 1 ⌊L⌋₊, (p : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpS, hpL⟩ := mem_filter.mp hp
          exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hpS).one_le,
            (Nat.le_floor_iff hL0.le).mpr hpL⟩
        · intro p hp _; positivity
      _ = (harmonic ⌊L⌋₊ : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ ≤ _ := harmonic_floor_le_one_add_log L (by dsimp [L]; linarith)
  have hB : (∑ p ∈ B, (p : ℝ)⁻¹) ≤ (Real.log 2)⁻¹ := by
    calc
      _ ≤ ∑ p ∈ B, L⁻¹ * (Real.log 2)⁻¹ * Real.log (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpS, hpL⟩ := mem_filter.mp hp
        have hprime := Nat.prime_of_mem_primeFactors hpS
        have hlp : Real.log 2 ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
        have hinv : (p : ℝ)⁻¹ ≤ L⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hL0 (le_of_lt (lt_of_not_ge hpL))
        have hrat : 1 ≤ (Real.log 2)⁻¹ * Real.log (p : ℝ) := by
          have hdiv : 1 ≤ Real.log (p : ℝ) / Real.log 2 :=
            (le_div_iff₀ h2).mpr (by simpa only [one_mul] using hlp)
          simpa only [div_eq_mul_inv, mul_comm] using hdiv
        nlinarith [mul_le_mul_of_nonneg_left hrat (inv_nonneg.mpr hL0.le)]
      _ ≤ ∑ p ∈ S, L⁻¹ * (Real.log 2)⁻¹ * Real.log (p : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p hp _
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hL0.le) (inv_nonneg.mpr h2.le))
          (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
      _ = L⁻¹ * (Real.log 2)⁻¹ * ∑ p ∈ S, Real.log (p : ℝ) := by rw [mul_sum]
      _ ≤ L⁻¹ * (Real.log 2)⁻¹ * L :=
        mul_le_mul_of_nonneg_left (primeFactors_log_budget q hq)
          (mul_nonneg (inv_nonneg.mpr hL0.le) (inv_nonneg.mpr h2.le))
      _ = _ := by field_simp
  have hsplit := sum_filter_add_sum_filter_not S (fun p => (p : ℝ) ≤ L) (fun p => (p : ℝ)⁻¹)
  change (∑ p ∈ S, (p : ℝ)⁻¹) ≤ 1 + Real.log L + (Real.log 2)⁻¹
  rw [← hsplit]
  exact add_le_add hA hB

end PrimeSquares
