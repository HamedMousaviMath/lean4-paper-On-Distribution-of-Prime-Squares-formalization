import PrimeSquares.GeneralSmoothEuler

/-!
# Solution-count local factors for Corollary 3.16

The counts below are cardinalities of the actual pairs of units in the source.
The factor at two retains precisely the finite Ramanujan sum e:generalT2.
-/

open Finset

namespace PrimeSquares

noncomputable def primeSolutionCount (p k : ℕ) (ell b n : ℤ) : ℕ :=
  if h : p = 0 then 0 else
    letI : NeZero p := ⟨h⟩
    (univ.filter fun uv : (ZMod p)ˣ × (ZMod p)ˣ =>
      ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (uv.2 : ZMod p) =
          (b : ZMod (p.gcd k)) ∧
        (uv.1 : ZMod p) ^ 2 + (ell : ZMod p) * (uv.2 : ZMod p) = (n : ZMod p)).card

theorem primeSolutionCount_eq (p k : ℕ) [NeZero p] (ell b n : ℤ) :
    primeSolutionCount p k ell b n =
    (univ.filter fun uv : (ZMod p)ˣ × (ZMod p)ˣ =>
      ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (uv.2 : ZMod p) =
          (b : ZMod (p.gcd k)) ∧
        (uv.1 : ZMod p) ^ 2 + (ell : ZMod p) * (uv.2 : ZMod p) = (n : ZMod p)).card := by
  simp [primeSolutionCount, NeZero.ne p]

/-- A finite pair count is exactly its double sum of indicators. -/
theorem unit_pair_count_cast (q : ℕ) [NeZero q]
    (P : (ZMod q)ˣ × (ZMod q)ˣ → Prop) [DecidablePred P] :
    ((univ.filter P).card : ℂ) =
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, if P (u, v) then (1 : ℂ) else 0 := by
  calc
    _ = ∑ uv : (ZMod q)ˣ × (ZMod q)ˣ, if P uv then (1 : ℂ) else 0 := by simp
    _ = _ := Fintype.sum_prod_type _

/-- The exact prime Ramanujan pair sum, before evaluating its total mass. -/
theorem generalPairRamanujanSum_prime (p k : ℕ) [Fact p.Prime] (ell b n : ℤ) :
    generalPairRamanujanSum p k ell b n =
      (p : ℂ) * (primeSolutionCount p k ell b n : ℂ) -
        ∑ _u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
          if ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (v : ZMod p) =
              (b : ZMod (p.gcd k)) then (1 : ℂ) else 0 := by
  classical
  rw [primeSolutionCount_eq, unit_pair_count_cast]
  unfold generalPairRamanujanSum
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro u _
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  rw [ramanujanSum_prime]
  have he : (n : ZMod p) - (u : ZMod p) ^ 2 - (ell : ZMod p) * (v : ZMod p) = 0 ↔
      (u : ZMod p) ^ 2 + (ell : ZMod p) * (v : ZMod p) = (n : ZMod p) := by
    rw [sub_sub, sub_eq_zero, eq_comm]
  simp only [he]
  by_cases hP : ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (v : ZMod p) =
      (b : ZMod (p.gcd k)) <;>
    by_cases hS : (u : ZMod p) ^ 2 + (ell : ZMod p) * (v : ZMod p) = (n : ZMod p) <;>
    simp only [hP, hS, and_self, and_false, false_and, ite_true, ite_false] <;> ring

/-- Reduction to a unit class modulo a divisor equal to q fixes one unit. -/
theorem unit_reduction_eq_iff (q k : ℕ) [NeZero q] (hd : q ∣ k) (b : ℤ)
    (hb : IsUnit (b : ZMod q)) (v : (ZMod q)ˣ) :
    ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (v : ZMod q) =
        (b : ZMod (q.gcd k)) ↔ v = hb.unit := by
  have hg : q.gcd k = q := Nat.gcd_eq_left_iff_dvd.mpr hd
  have he (z : ZMod q) :
      ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) z =
        (b : ZMod (q.gcd k)) ↔ z = (b : ZMod q) := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    simp only [map_intCast]
    rw [hg]
  rw [he]
  constructor
  · intro h
    apply Units.ext
    exact h.trans hb.unit_spec.symm
  · rintro rfl
    exact hb.unit_spec

/-- Count the progression units at a prime, with the exact gcd normalization. -/
theorem prime_progression_unit_mass (p k : ℕ) [Fact p.Prime] (b : ℤ)
    (hb : IsCoprime (k : ℤ) b) :
    ((p.gcd k).totient : ℂ) *
      (∑ v : (ZMod p)ˣ,
        if ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (v : ZMod p) =
            (b : ZMod (p.gcd k)) then (1 : ℂ) else 0) = (p.totient : ℂ) := by
  classical
  have hp : p.Prime := Fact.out
  rcases Nat.coprime_or_dvd_of_prime hp k with hc | hd
  · have : Subsingleton (ZMod (p.gcd k)) := by rw [hc.gcd_eq_one]; infer_instance
    have he (v : (ZMod p)ˣ) :
        ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (v : ZMod p) =
          (b : ZMod (p.gcd k)) := Subsingleton.elim _ _
    have hs : (∑ v : (ZMod p)ˣ,
        if ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (v : ZMod p) =
            (b : ZMod (p.gcd k)) then (1 : ℂ) else 0) = ∑ _ : (ZMod p)ˣ, (1 : ℂ) := by
      apply sum_congr rfl
      intro v _
      exact ite_eq_left (he v)
    rw [hs]
    simp [hc.gcd_eq_one, ZMod.card_units_eq_totient]
  · have hbu : IsUnit (b : ZMod p) :=
      (ZMod.coe_int_isUnit_iff_isCoprime b p).mpr (integer_coprime_of_nat_dvd p k b hb hd)
    simp_rw [unit_reduction_eq_iff p k hd b hbu]
    simp [Nat.gcd_eq_left_iff_dvd.mpr hd]

/-- Exact mass of pairs satisfying just the progression restriction. -/
theorem prime_progression_pair_mass (p k : ℕ) [Fact p.Prime] (b : ℤ)
    (hb : IsCoprime (k : ℤ) b) :
    ((p.gcd k).totient : ℂ) *
      (∑ _u : (ZMod p)ˣ, ∑ v : (ZMod p)ˣ,
        if ZMod.castHom (Nat.gcd_dvd_left p k) (ZMod (p.gcd k)) (v : ZMod p) =
            (b : ZMod (p.gcd k)) then (1 : ℂ) else 0) = (p.totient : ℂ) ^ 2 := by
  rw [sum_const, card_univ, nsmul_eq_mul, ZMod.card_units_eq_totient]
  rw [← mul_assoc, mul_comm ((p.gcd k).totient : ℂ), mul_assoc,
    prime_progression_unit_mass p k b hb]
  ring

/-- The source pair sum with the equivalent gcd normalization. -/
theorem generalCoefficient_normalized_pairs (q k : ℕ) [NeZero q] [NeZero k]
    (ell b n : ℤ) : generalCoefficient q k ell b n =
      ((q.gcd k).totient : ℂ) / (q.totient : ℂ) ^ 2 *
        generalPairRamanujanSum q k ell b n := by
  rw [generalCoefficient_as_quadratic, generalPairRamanujanSum_as_quadratic]

/-- The actual prime coefficient becomes precisely the source's solution count. -/
theorem generalCoefficient_prime_euler_factor (p k : ℕ) [Fact p.Prime] [NeZero k]
    (ell b n : ℤ) (hb : IsCoprime (k : ℤ) b) :
    1 + generalCoefficient p k ell b n =
      (p : ℂ) * ((p.gcd k).totient : ℂ) / ((p : ℂ) - 1) ^ 2 *
        (primeSolutionCount p k ell b n : ℂ) := by
  have hp : p.Prime := Fact.out
  have hφ : (p.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  have hm := prime_progression_pair_mass p k b hb
  have he : 1 + generalCoefficient p k ell b n =
      (p : ℂ) * ((p.gcd k).totient : ℂ) / (p.totient : ℂ) ^ 2 *
        (primeSolutionCount p k ell b n : ℂ) := by
    rw [generalCoefficient_normalized_pairs, generalPairRamanujanSum_prime]
    field_simp
    linear_combination -hm
  simpa only [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one] using he

/-- The exact finite factor e:generalT2, with exponents one through three. -/
noncomputable def generalTwoEulerFactor (k : ℕ) (ell b n : ℤ) : ℂ :=
  1 + ∑ j ∈ range 3,
    (k.totient : ℂ) /
      (((2 ^ (j + 1)).totient : ℂ) * ((k.lcm (2 ^ (j + 1))).totient : ℂ)) *
        generalPairRamanujanSum (2 ^ (j + 1)) k ell b n

theorem generalCoefficient_two_euler_factor (k : ℕ) (ell b n : ℤ) :
    1 + generalCoefficient 2 k ell b n + generalCoefficient 4 k ell b n +
      generalCoefficient 8 k ell b n = generalTwoEulerFactor k ell b n := by
  simp only [generalTwoEulerFactor, sum_range_succ, sum_range_zero, zero_add,
    show 2 ^ (0 + 1) = 2 by norm_num, show 2 ^ (1 + 1) = 4 by norm_num,
    show 2 ^ (2 + 1) = 8 by norm_num, generalCoefficient_fixed_modulus]
  ring

/-- At ell=1, the general 2-adic factor agrees with the previous closed formula. -/
theorem generalTwoEulerFactor_one_multiplier (k : ℕ) [NeZero k] (b n : ℤ)
    (hb : IsCoprime (k : ℤ) b) : generalTwoEulerFactor k 1 b n =
      twoProgressionEulerFactor (k.factorization 2) b n := by
  rw [← generalCoefficient_two_euler_factor]
  simp only [generalCoefficient_one_multiplier]
  exact progressionCoefficient_two_euler_factor k b n hb

/-- Complete Corollary 3.16 for every integer cutoff Q>=3 and positive k. -/
theorem general_progression_euler_product (Q k : ℕ) [NeZero k] (hQ : 3 ≤ Q)
    (ell b n : ℤ) (hb : IsCoprime (k : ℤ) b) : smoothGeneralSeries Q k ell b n =
      generalTwoEulerFactor k ell b n *
        ∏ p ∈ oddPrimesBelow Q,
          (p : ℂ) * ((p.gcd k).totient : ℂ) / ((p : ℂ) - 1) ^ 2 *
            (primeSolutionCount p k ell b n : ℂ) := by
  rw [smoothGeneralSeries_euler_product Q k ell b n hQ,
    generalCoefficient_two_euler_factor]
  congr 1
  apply prod_congr rfl
  intro p hp
  have : Fact p.Prime := ⟨(mem_filter.mp hp).2.1⟩
  exact generalCoefficient_prime_euler_factor p k ell b n hb

/-- The same source identity for every real cutoff Q>2. -/
theorem general_progression_euler_product_real (Q : ℝ) (k : ℕ) [NeZero k] (hQ : 2 < Q)
    (ell b n : ℤ) (hb : IsCoprime (k : ℤ) b) :
    (∑' q : ℕ, if ∀ p ∈ q.primeFactors, (p : ℝ) < Q
      then generalCoefficient q k ell b n else 0) =
      generalTwoEulerFactor k ell b n *
        ∏ p ∈ oddPrimesBelow (Nat.ceil Q),
          (p : ℂ) * ((p.gcd k).totient : ℂ) / ((p : ℂ) - 1) ^ 2 *
            (primeSolutionCount p k ell b n : ℂ) := by
  have hc : 3 ≤ Nat.ceil Q := by
    have h : 2 < Nat.ceil Q := Nat.lt_ceil.mpr hQ
    omega
  have he := general_progression_euler_product (Nat.ceil Q) k hc ell b n hb
  simpa only [smoothGeneralSeries, Nat.lt_ceil] using he

end PrimeSquares
