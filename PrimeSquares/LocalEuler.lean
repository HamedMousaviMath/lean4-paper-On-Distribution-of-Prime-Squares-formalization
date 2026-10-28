import PrimeSquares.SmoothEuler

/-!
# Explicit local factors in the progression Euler product

Source: Draft5, Lemma 3.14. Every formula below evaluates the actual
coefficient, using the proved identities rather than a surrogate local model.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeSquares

/-- Coprimality passes from a positive modulus to every divisor. -/
theorem integer_coprime_of_nat_dvd (q k : ℕ) (b : ℤ)
    (hb : IsCoprime (k : ℤ) b) (hd : q ∣ k) : IsCoprime (q : ℤ) b :=
  hb.of_isCoprime_of_dvd_left (Int.natCast_dvd_natCast.mpr hd)

/-- Fixing a unit class modulo all of q leaves just that one residue. -/
theorem progressionCoefficient_of_dvd (q k : ℕ) [NeZero q] [NeZero k]
    (hd : q ∣ k) (b x : ℤ) (hb : IsUnit (b : ZMod q)) :
    progressionCoefficient q k b x = cohenCorrelation q (x - b) / (q.totient : ℂ) := by
  classical
  have hg : q.gcd k = q := Nat.gcd_eq_left_iff_dvd.mpr hd
  have hP (r : (ZMod q)ˣ) :
      ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (r : ZMod q) =
        (b : ZMod (q.gcd k)) ↔ r = hb.unit := by
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
  rw [progressionCoefficient_as_quadratic]
  have he : (∑ r : (ZMod q)ˣ,
      if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (r : ZMod q) =
          (b : ZMod (q.gcd k))
      then quadraticRamanujanSum q ((x : ZMod q) - (r : ZMod q)) else 0) =
      quadraticRamanujanSum q ((x : ZMod q) - (b : ZMod q)) := by
    simp_rw [hP]
    rw [sum_ite_eq', ite_eq_left (mem_univ _), hb.unit_spec]
  rw [he, hg, cohenCorrelation_eq, Int.cast_sub]
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

/-- Convolving C_q with all units has the same linear Cohen eigenvalue mu(q). -/
theorem linear_quadratic_cohen_identity (q : ℕ) [NeZero q] (x : ZMod q) :
    (∑ r : (ZMod q)ˣ, quadraticRamanujanSum q (x - r)) =
      (μ q : ℂ) * quadraticRamanujanSum q x := by
  classical
  simp only [quadraticRamanujanSum, sum_unit_filter_eq_sum_units]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro u _
  have he (r : (ZMod q)ˣ) : x - (r : ZMod q) - (u : ZMod q) ^ 2 =
      (x - (u : ZMod q) ^ 2) - (r : ZMod q) := by ring
  simp_rw [he]
  exact linear_cohen_identity q _

/-- If q is coprime to k the progression restriction modulo gcd(q,k)=1 disappears. -/
theorem progressionCoefficient_of_coprime (q k : ℕ) [NeZero q] [NeZero k]
    (hc : q.Coprime k) (b x : ℤ) :
    progressionCoefficient q k b x = (μ q : ℂ) * cohenCorrelation q x / (q.totient : ℂ) ^ 2 := by
  classical
  have : Subsingleton (ZMod (q.gcd k)) := by rw [hc.gcd_eq_one]; infer_instance
  have he (r : (ZMod q)ˣ) :
      ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (r : ZMod q) =
        (b : ZMod (q.gcd k)) := Subsingleton.elim _ _
  rw [progressionCoefficient_as_quadratic]
  have hs : (∑ r : (ZMod q)ˣ,
      if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (r : ZMod q) =
          (b : ZMod (q.gcd k))
      then quadraticRamanujanSum q ((x : ZMod q) - (r : ZMod q)) else 0) =
      ∑ r : (ZMod q)ˣ, quadraticRamanujanSum q ((x : ZMod q) - r) := by
    apply sum_congr rfl
    intro r _
    exact ite_eq_left (he r)
  rw [hs, linear_quadratic_cohen_identity, hc.gcd_eq_one, Nat.totient_one, Nat.cast_one,
    cohenCorrelation_eq]
  ring

/-- Partial prime-power overlap kills the coefficient, with the normalizer nonzero. -/
theorem progressionCoefficient_non_coprime_complement (q k : ℕ) [NeZero q] [NeZero k]
    (b x : ℤ) (hb : IsCoprime (k : ℤ) b)
    (hc : ¬(q.gcd k).Coprime (q / q.gcd k)) : progressionCoefficient q k b x = 0 := by
  have he := sum_upsilon_square_identity q k b x
    (integer_coprime_of_nat_dvd _ _ b hb (Nat.gcd_dvd_right q k))
  dsimp only at he
  rw [← progressionCoefficient_eq] at he
  simp only [ite_eq_right hc, mul_zero, zero_mul] at he
  have hq : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hk : (k.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos k)).ne'
  have hl : ((k.lcm q).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos (NeZero.pos k) (NeZero.pos q))).ne'
  exact (mul_eq_zero.mp he).resolve_left (div_ne_zero (mul_ne_zero hq hl) hk)

/-- At exponent at least two, a prime power contributes only if it divides k in full. -/
theorem progressionCoefficient_prime_pow_not_dvd (p a k : ℕ) [Fact p.Prime] [NeZero k]
    (ha : 2 ≤ a) (hd : ¬p ^ a ∣ k) (b x : ℤ) (hb : IsCoprime (k : ℤ) b) :
    progressionCoefficient (p ^ a) k b x = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ a) k)
  by_cases hj0 : j = 0
  · have hc : (p ^ a).Coprime k := by simpa only [hj0, pow_zero] using hg
    rw [progressionCoefficient_of_coprime _ k hc b x,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show a ≠ 1 by omega]
  · have hja : j < a := by
      by_contra! hn
      have hje : j = a := by omega
      apply hd
      simpa only [hje, hg] using Nat.gcd_dvd_right (p ^ a) k
    have hh : p ^ a / (p ^ a).gcd k = p ^ (a - j) := by rw [hg, Nat.pow_div hj hp.pos]
    apply progressionCoefficient_non_coprime_complement _ k b x hb
    rw [hh, hg]
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt
      (dvd_pow_self p hj0) (dvd_pow_self p (by omega : a - j ≠ 0))

/-- Odd-prime local coefficient, with the Legendre factors in the source. -/
theorem progressionCoefficient_odd_prime (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hp2 : p ≠ 2) (b x : ℤ) (hb : IsCoprime (k : ℤ) b) :
    progressionCoefficient p k b x =
      if p ∣ k then oddCohenFactor p (x - b) / (p - 1 : ℂ)
      else -oddCohenFactor p x / (p - 1 : ℂ) ^ 2 := by
  classical
  have hp : p.Prime := Fact.out
  have hcast : (p.totient : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub (by have := hp.two_le; omega), Nat.cast_one]
  have hC (n : ℤ) : cohenCorrelation p n = oddCohenFactor p n := by
    simpa only [pow_one, ite_true, one_mul] using cohenCorrelation_odd_prime_pow p hp2 1 (by decide) n
  by_cases hd : p ∣ k
  · rw [ite_eq_left hd, progressionCoefficient_of_dvd p k hd b x
      ((ZMod.coe_int_isUnit_iff_isCoprime b p).mpr (integer_coprime_of_nat_dvd p k b hb hd)), hcast, hC]
  · rw [ite_eq_right hd, progressionCoefficient_of_coprime p k (hp.coprime_iff_not_dvd.mpr hd) b x,
      ArithmeticFunction.moebius_apply_prime hp, hcast, hC]
    simp

/-- The full-divisibility or zero dichotomy for higher prime powers. -/
theorem progressionCoefficient_prime_pow_ge_two (p a k : ℕ) [Fact p.Prime] [NeZero k]
    (ha : 2 ≤ a) (b x : ℤ) (hb : IsCoprime (k : ℤ) b) :
    progressionCoefficient (p ^ a) k b x =
      if p ^ a ∣ k then cohenCorrelation (p ^ a) (x - b) / ((p ^ a).totient : ℂ) else 0 := by
  classical
  by_cases hd : p ^ a ∣ k
  · rw [ite_eq_left hd]
    exact progressionCoefficient_of_dvd _ k hd b x
      ((ZMod.coe_int_isUnit_iff_isCoprime b (p ^ a)).mpr
        (integer_coprime_of_nat_dvd _ k b hb hd))
  · rw [ite_eq_right hd]
    exact progressionCoefficient_prime_pow_not_dvd p a k ha hd b x hb

/-- The two possible coefficients at modulus two. -/
theorem progressionCoefficient_two (k : ℕ) [NeZero k] (b x : ℤ) (hb : IsCoprime (k : ℤ) b) :
    progressionCoefficient 2 k b x =
      if 2 ∣ k then cohenCorrelation 2 (x - b) else -cohenCorrelation 2 x := by
  classical
  by_cases hd : 2 ∣ k
  · rw [ite_eq_left hd, progressionCoefficient_of_dvd 2 k hd b x
      ((ZMod.coe_int_isUnit_iff_isCoprime b 2).mpr (integer_coprime_of_nat_dvd 2 k b hb hd))]
    norm_num
  · rw [ite_eq_right hd,
      progressionCoefficient_of_coprime 2 k (Nat.prime_two.coprime_iff_not_dvd.mpr hd) b x,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num

/-- The source's odd-prime Euler factor; nonprime inputs are unused. -/
noncomputable def oddProgressionEulerFactor (p k : ℕ) (b x : ℤ) : ℂ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    if p ∣ k then
      if legendreSym p (x - b) = 1 then 1 + ((p : ℂ) + 1) / ((p : ℂ) - 1) else 0
    else
      if legendreSym p x = 1 then 1 - ((p : ℂ) + 1) / ((p : ℂ) - 1) ^ 2
      else 1 + 1 / ((p : ℂ) - 1)
  else 0

/-- Adding the unit term gives exactly the four odd-prime cases in e:corupss. -/
theorem progressionCoefficient_odd_euler_factor (p k : ℕ) [Fact p.Prime] [NeZero k]
    (hp2 : p ≠ 2) (b x : ℤ) (hb : IsCoprime (k : ℤ) b) :
    1 + progressionCoefficient p k b x = oddProgressionEulerFactor p k b x := by
  classical
  have hp : p.Prime := Fact.out
  have hden : (p : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [progressionCoefficient_odd_prime p k hp2 b x hb]
  simp only [oddProgressionEulerFactor, oddCohenFactor, dite_eq_left hp]
  split_ifs <;> field_simp <;> ring

/-- The exact 2-adic factor in e:T2factor. -/
noncomputable def twoProgressionEulerFactor (h : ℕ) (b x : ℤ) : ℂ :=
  if h = 0 then 1 + (-1 : ℂ) ^ x
  else ((2 ^ min h 3 : ℕ) : ℂ) *
    (if ((x - b : ℤ) : ZMod (2 ^ min h 3)) = 1 then 1 else 0)

/-- The small 2-adic partial sum at exponent two. -/
theorem two_local_partial_four (n : ℤ) :
    1 + cohenCorrelation 2 n + cohenCorrelation 4 n / 2 =
      4 * (if (n : ZMod 4) = 1 then (1 : ℂ) else 0) := by
  have h2 : (n : ZMod 2) = ZMod.castHom (show 2 ∣ 4 from ⟨2, rfl⟩) (ZMod 2) (n : ZMod 4) := by
    rw [map_intCast]
  have hC2 : cohenCorrelation 2 n = if (n : ZMod 2) = 1 then 1 else -1 := by
    simpa [twoAdicCohenFactor] using cohenCorrelation_two_pow 1 n
  have hC4 : cohenCorrelation 4 n = if (n : ZMod 4) = 1 then 4
      else if (n : ZMod 4) = 3 then -4 else 0 := by
    simpa [twoAdicCohenFactor] using cohenCorrelation_two_pow 2 n
  have hρ : (n : ZMod 2) = 1 ↔ (n : ZMod 4) = 1 ∨ (n : ZMod 4) = 3 := by
    rw [h2]
    exact (by decide : ∀ z : ZMod 4,
      ZMod.castHom (show 2 ∣ 4 from ⟨2, rfl⟩) (ZMod 2) z = 1 ↔ z = 1 ∨ z = 3) _
  rw [hC2, hC4]
  by_cases h1 : (n : ZMod 4) = 1
  · rw [ite_eq_left (hρ.mpr (Or.inl h1)), ite_eq_left h1]
    norm_num; exact h1
  · by_cases h3 : (n : ZMod 4) = 3
    · rw [ite_eq_left (hρ.mpr (Or.inr h3)), ite_eq_right h1, ite_eq_left h3]
      norm_num; exact h1
    · have hno : (n : ZMod 2) ≠ 1 := fun h => (hρ.mp h).elim h1 h3
      rw [ite_eq_right hno, ite_eq_right h1, ite_eq_right h3]
      norm_num; exact h1

/-- The small 2-adic partial sum at exponent three. -/
theorem two_local_partial_eight (n : ℤ) :
    1 + cohenCorrelation 2 n + cohenCorrelation 4 n / 2 + cohenCorrelation 8 n / 4 =
      8 * (if (n : ZMod 8) = 1 then (1 : ℂ) else 0) := by
  rw [two_local_partial_four]
  have h4 : (n : ZMod 4) = ZMod.castHom (show 4 ∣ 8 from ⟨2, rfl⟩) (ZMod 4) (n : ZMod 8) := by
    rw [map_intCast]
  have hρ : (n : ZMod 4) = 1 ↔ (n : ZMod 8) = 1 ∨ (n : ZMod 8) = 5 := by
    rw [h4]
    exact (by decide : ∀ z : ZMod 8,
      ZMod.castHom (show 4 ∣ 8 from ⟨2, rfl⟩) (ZMod 4) z = 1 ↔ z = 1 ∨ z = 5) _
  have hC8 : cohenCorrelation 8 n = if (n : ZMod 8) = 1 then 16
      else if (n : ZMod 8) = 5 then -16 else 0 := by
    simpa [twoAdicCohenFactor] using cohenCorrelation_two_pow 3 n
  rw [hC8]
  by_cases h1 : (n : ZMod 8) = 1
  · rw [ite_eq_left (hρ.mpr (Or.inl h1)), ite_eq_left h1]
    norm_num; exact h1
  · by_cases h5 : (n : ZMod 8) = 5
    · rw [ite_eq_left (hρ.mpr (Or.inr h5)), ite_eq_right h1, ite_eq_left h5]
      norm_num; exact h1
    · have hno : (n : ZMod 4) ≠ 1 := fun h => (hρ.mp h).elim h1 h5
      rw [ite_eq_right hno, ite_eq_right h1, ite_eq_right h5]
      norm_num; exact h1

/-- The complete explicit 2-adic factor, including every valuation of k. -/
theorem progressionCoefficient_two_euler_factor (k : ℕ) [NeZero k] (b x : ℤ)
    (hb : IsCoprime (k : ℤ) b) :
    1 + progressionCoefficient 2 k b x + progressionCoefficient 4 k b x +
      progressionCoefficient 8 k b x = twoProgressionEulerFactor (k.factorization 2) b x := by
  classical
  have h4 := progressionCoefficient_prime_pow_ge_two 2 2 k (by decide) b x hb
  have h8 := progressionCoefficient_prime_pow_ge_two 2 3 k (by decide) b x hb
  norm_num at h4 h8
  simp only [show Nat.totient 4 = 2 from by decide, show Nat.totient 8 = 4 from by decide,
    Nat.cast_ofNat] at h4 h8
  rw [progressionCoefficient_two k b x hb, h4, h8]
  generalize hv : k.factorization 2 = v
  have hd2 : 2 ∣ k ↔ 1 ≤ v := by
    simpa only [hv, pow_one] using
      Nat.prime_two.pow_dvd_iff_le_factorization (k := 1) (NeZero.ne k)
  have hd4 : 4 ∣ k ↔ 2 ≤ v := by
    simpa only [hv, show (2 : ℕ) ^ 2 = 4 from by decide] using Nat.prime_two.pow_dvd_iff_le_factorization (k := 2) (NeZero.ne k)
  have hd8 : 8 ∣ k ↔ 3 ≤ v := by
    simpa only [hv, show (2 : ℕ) ^ 3 = 8 from by decide] using Nat.prime_two.pow_dvd_iff_le_factorization (k := 3) (NeZero.ne k)
  rcases v with _ | (_ | (_ | t))
  · have hn2 : ¬2 ∣ k := fun h => by have := hd2.mp h; omega
    have hn4 : ¬4 ∣ k := fun h => by have := hd4.mp h; omega
    have hn8 : ¬8 ∣ k := fun h => by have := hd8.mp h; omega
    rw [ite_eq_right hn2, ite_eq_right hn4, ite_eq_right hn8]
    have hC2 : cohenCorrelation 2 x = (-1 : ℂ) ^ (x + 1) := by
      rw [← twoAdicCohenFactor_one]
      exact cohenCorrelation_two_pow 1 x
    rw [hC2, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    simp [twoProgressionEulerFactor]
  · have h2 : 2 ∣ k := hd2.mpr (by omega)
    have hn4 : ¬4 ∣ k := fun h => by have := hd4.mp h; omega
    have hn8 : ¬8 ∣ k := fun h => by have := hd8.mp h; omega
    rw [ite_eq_left h2, ite_eq_right hn4, ite_eq_right hn8]
    have hC2 : cohenCorrelation 2 (x - b) = if ((x - b : ℤ) : ZMod 2) = 1 then 1 else -1 := by
      simpa [twoAdicCohenFactor] using cohenCorrelation_two_pow 1 (x - b)
    rw [hC2]
    norm_num [twoProgressionEulerFactor]
    split_ifs <;> norm_num
  · have h2 : 2 ∣ k := hd2.mpr (by omega)
    have h4 : 4 ∣ k := hd4.mpr (by omega)
    have hn8 : ¬8 ∣ k := fun h => by have := hd8.mp h; omega
    rw [ite_eq_left h2, ite_eq_left h4, ite_eq_right hn8, add_zero]
    simpa [twoProgressionEulerFactor] using two_local_partial_four (x - b)
  · have h2 : 2 ∣ k := hd2.mpr (by omega)
    have h4 : 4 ∣ k := hd4.mpr (by omega)
    have h8 : 8 ∣ k := hd8.mpr (by omega)
    rw [ite_eq_left h2, ite_eq_left h4, ite_eq_left h8]
    have he (m : ℕ) (hm : m = 3) :
        1 + cohenCorrelation 2 (x - b) + cohenCorrelation 4 (x - b) / 2 +
          cohenCorrelation 8 (x - b) / 4 = ((2 ^ m : ℕ) : ℂ) *
            (if ((x - b : ℤ) : ZMod (2 ^ m)) = 1 then 1 else 0) := by
      subst m
      simpa using two_local_partial_eight (x - b)
    simp only [twoProgressionEulerFactor, ite_eq_right (show t + 1 + 1 + 1 ≠ 0 by omega)]
    exact he _ (Nat.min_eq_right (by omega))

/-- Lemma 3.14 with its necessary explicit range Q>=3 and positive modulus k.
The case product is exactly the four odd-prime products in e:corupss. -/
theorem progression_euler_product (Q k : ℕ) [NeZero k] (hQ : 3 ≤ Q)
    (b x : ℤ) (hb : IsCoprime (k : ℤ) b) : smoothProgressionSeries Q k b x =
      twoProgressionEulerFactor (k.factorization 2) b x *
        ∏ p ∈ oddPrimesBelow Q, oddProgressionEulerFactor p k b x := by
  rw [smoothProgressionSeries_euler_product Q k b x hQ,
    progressionCoefficient_two_euler_factor k b x hb]
  congr 1
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hp', hp2⟩ := mem_filter.mp hp
  have : Fact p.Prime := ⟨hp'⟩
  exact progressionCoefficient_odd_euler_factor p k (ne_of_gt hp2) b x hb

/-- The corrected vanishing assertion: the obstructing prime must be below Q. -/
theorem progression_euler_product_eq_zero_of_obstruction (Q k p : ℕ)
    [NeZero k] [Fact p.Prime] (hQ : 3 ≤ Q) (hp2 : 2 < p) (hpQ : p < Q)
    (hd : p ∣ k) (b x : ℤ) (hb : IsCoprime (k : ℤ) b)
    (hleg : legendreSym p (x - b) ≠ 1) : smoothProgressionSeries Q k b x = 0 := by
  classical
  have hp : p.Prime := Fact.out
  rw [progression_euler_product Q k hQ b x hb]
  have hm : p ∈ oddPrimesBelow Q := mem_filter.mpr ⟨mem_range.mpr hpQ, hp, hp2⟩
  have hz : oddProgressionEulerFactor p k b x = 0 := by
    simp only [oddProgressionEulerFactor, dite_eq_left hp, ite_eq_left hd, ite_eq_right hleg]
  rw [prod_eq_zero hm hz, mul_zero]

/-- The same corrected identity for every real cutoff Q>2, using its exact ceiling.
For integer primes, p < ceil(Q) if and only if (p : Real) < Q. -/
theorem progression_euler_product_real (Q : ℝ) (k : ℕ) [NeZero k] (hQ : 2 < Q)
    (b x : ℤ) (hb : IsCoprime (k : ℤ) b) :
    (∑' q : ℕ, if ∀ p ∈ q.primeFactors, (p : ℝ) < Q
      then progressionCoefficient q k b x else 0) =
      twoProgressionEulerFactor (k.factorization 2) b x *
        ∏ p ∈ oddPrimesBelow (Nat.ceil Q), oddProgressionEulerFactor p k b x := by
  have hc : 3 ≤ Nat.ceil Q := by
    have h : 2 < Nat.ceil Q := Nat.lt_ceil.mpr hQ
    omega
  have he := progression_euler_product (Nat.ceil Q) k hc b x hb
  simpa only [smoothProgressionSeries, Nat.lt_ceil] using he

/-- At Q=2 only the modulus one is allowed by the strict prime cutoff. -/
theorem smoothProgressionSeries_cutoff_two (k : ℕ) [NeZero k] (b x : ℤ) :
    smoothProgressionSeries 2 k b x = 1 := by
  classical
  unfold smoothProgressionSeries
  rw [tsum_eq_single 1]
  · simp [progressionCoefficient_one]
  · intro q hq1
    by_cases hq0 : q = 0
    · simp [hq0, progressionCoefficient]
    by_cases hs : ∀ p ∈ q.primeFactors, p < 2
    · obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd hq1
      have hl := hs p (Nat.mem_primeFactors.mpr ⟨hp, hd, hq0⟩)
      have := hp.two_le
      omega
    · exact ite_eq_right hs

/-- A kernel-checked counterexample to omitting Q>2 from the displayed formula. -/
theorem cutoff_two_counterexample :
    smoothProgressionSeries 2 1 0 0 = 1 ∧
      twoProgressionEulerFactor (Nat.factorization 1 2) 0 0 = 2 := by
  constructor
  · exact smoothProgressionSeries_cutoff_two 1 0 0
  · norm_num [Nat.factorization_one, twoProgressionEulerFactor]

/-- The unqualified final vanishing sentence fails at a prime above the cutoff.
Here Q=3, k=5, b=1, x=4, while x-b=3 is a nonsquare modulo five. -/
theorem obstructing_prime_above_cutoff_counterexample :
    smoothProgressionSeries 3 5 1 4 = 2 ∧ ¬IsSquare (3 : ZMod 5) := by
  constructor
  · rw [progression_euler_product 3 5 (by decide) 1 4 isCoprime_one_right]
    have hs : oddPrimesBelow 3 = ∅ := by decide
    have hv : Nat.factorization 5 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 5)
    rw [hs, prod_empty, mul_one, hv]
    norm_num [twoProgressionEulerFactor]
  · change ¬∃ r : ZMod 5, (3 : ZMod 5) = r * r
    decide

end PrimeSquares
