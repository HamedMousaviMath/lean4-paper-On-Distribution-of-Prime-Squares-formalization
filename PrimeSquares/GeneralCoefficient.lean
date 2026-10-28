import PrimeSquares.LocalEuler

/-!
# The coefficient with an arbitrary integer multiplier

Source: Corollary 3.16, `c:generalmajorprimesquareprog` and
`e:fixedqcoefficient`. The definition uses the actual Upsilon(a*ell),
principal square sum and additive character. No condition on ell is imposed.
-/

open Finset

namespace PrimeSquares

noncomputable def generalCoefficient (q k : ℕ) (ell b n : ℤ) : ℂ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ∑ a : (ZMod q)ˣ, upsilon q k b ((a : ZMod q) * (ell : ZMod q)) *
      principalSquareSum q a * ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))

theorem generalCoefficient_eq (q k : ℕ) [NeZero q] (ell b n : ℤ) :
    generalCoefficient q k ell b n =
      ∑ a : (ZMod q)ˣ, upsilon q k b ((a : ZMod q) * (ell : ZMod q)) *
        principalSquareSum q a * ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) := by
  simp [generalCoefficient, NeZero.ne q]

/-- The new coefficient specializes to the previously checked Lemma 3.14. -/
theorem generalCoefficient_one_multiplier (q k : ℕ) (b n : ℤ) :
    generalCoefficient q k 1 b n = progressionCoefficient q k b n := by
  by_cases hq : q = 0
  · simp [hq, generalCoefficient, progressionCoefficient]
  · have : NeZero q := ⟨hq⟩
    simp only [generalCoefficient_eq, progressionCoefficient_eq, Int.cast_one, mul_one]

/-- The pair sum in equations e:fixedqcoefficient and e:generalT2. -/
noncomputable def generalPairRamanujanSum (q k : ℕ) [NeZero q] (ell b n : ℤ) : ℂ :=
  ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
    if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (v : ZMod q) =
        (b : ZMod (q.gcd k))
    then ramanujanSum q ((n : ZMod q) - (u : ZMod q) ^ 2 - (ell : ZMod q) * (v : ZMod q))
    else 0

/-- Opening the characters proves the finite expansion, including ell=0. -/
theorem general_correlation_expansion (q g : ℕ) [NeZero q] [NeZero g]
    (hg : g ∣ q) (b : ZMod g) (ell n : ZMod q) :
    (∑ a : (ZMod q)ˣ, progressionExponentialSum q g hg b ((a : ZMod q) * ell) *
      (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q) * (u : ZMod q) ^ 2))) *
      ZMod.stdAddChar ((a : ZMod q) * n)) =
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        if ZMod.castHom hg (ZMod g) (v : ZMod q) = b then
          ramanujanSum q (n - (u : ZMod q) ^ 2 - ell * (v : ZMod q)) else 0 := by
  classical
  have he (a : (ZMod q)ˣ) :
      progressionExponentialSum q g hg b ((a : ZMod q) * ell) *
        (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q) * (u : ZMod q) ^ 2))) *
        ZMod.stdAddChar ((a : ZMod q) * n) =
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        if ZMod.castHom hg (ZMod g) (v : ZMod q) = b then
          ZMod.stdAddChar ((n - (u : ZMod q) ^ 2 - ell * (v : ZMod q)) * (a : ZMod q)) else 0 := by
    unfold progressionExponentialSum
    simp_rw [sum_mul, mul_sum]
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    split_ifs
    · rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    · simp
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_ite_irrel]
  split_ifs
  · rw [ramanujanSum, sum_unit_filter_eq_sum_units]
  · simp

/-- The paper's exact fixed-q formula, with its original totient normalization. -/
theorem generalCoefficient_fixed_modulus (q k : ℕ) [NeZero q] (ell b n : ℤ) :
    generalCoefficient q k ell b n =
      (k.totient : ℂ) / ((q.totient : ℂ) * ((k.lcm q).totient : ℂ)) *
        generalPairRamanujanSum q k ell b n := by
  rw [generalCoefficient_eq]
  have he := general_correlation_expansion q (q.gcd k) (Nat.gcd_dvd_left q k)
    (b : ZMod (q.gcd k)) (ell : ZMod q) (n : ZMod q)
  change _ = generalPairRamanujanSum q k ell b n at he
  rw [← he]
  simp only [upsilon, principalSquareSum]
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

/-- Switch summation order to expose C_q(n-ell*v). -/
theorem generalPairRamanujanSum_as_quadratic (q k : ℕ) [NeZero q] (ell b n : ℤ) :
    generalPairRamanujanSum q k ell b n =
      ∑ v : (ZMod q)ˣ,
        if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (v : ZMod q) =
            (b : ZMod (q.gcd k))
        then quadraticRamanujanSum q ((n : ZMod q) - (ell : ZMod q) * (v : ZMod q)) else 0 := by
  classical
  unfold generalPairRamanujanSum
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_ite_irrel]
  split_ifs
  · simp only [quadraticRamanujanSum, sum_unit_filter_eq_sum_units]
    apply sum_congr rfl
    intro u _
    congr 1
    ring
  · simp

/-- Exact gcd normalization for the actual coefficient, at every positive modulus. -/
theorem generalCoefficient_as_quadratic (q k : ℕ) [NeZero q] [NeZero k] (ell b n : ℤ) :
    generalCoefficient q k ell b n =
      ((q.gcd k).totient : ℂ) / (q.totient : ℂ) ^ 2 *
        ∑ v : (ZMod q)ˣ,
          if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (v : ZMod q) =
              (b : ZMod (q.gcd k))
          then quadraticRamanujanSum q ((n : ZMod q) - (ell : ZMod q) * (v : ZMod q)) else 0 := by
  have hq : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hl : ((k.lcm q).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos (NeZero.pos k) (NeZero.pos q))).ne'
  have ht : ((k.lcm q).totient : ℂ) * ((q.gcd k).totient : ℂ) =
      (q.totient : ℂ) * (k.totient : ℂ) := by
    exact_mod_cast (by simpa only [Nat.lcm_comm k q] using totient_lcm_mul_totient_gcd q k)
  rw [generalCoefficient_fixed_modulus, generalPairRamanujanSum_as_quadratic]
  congr 1
  field_simp
  linear_combination -ht

/-- Pointwise C_q vanishing transfers to the actual progression coefficient. -/
theorem generalCoefficient_eq_zero_of_cohen_zero (q k : ℕ) [NeZero q] [NeZero k]
    (ell b x : ℤ) (hc : ∀ z : ℤ, cohenCorrelation q z = 0) :
    generalCoefficient q k ell b x = 0 := by
  classical
  rw [generalCoefficient_as_quadratic]
  have hz (z : ZMod q) : quadraticRamanujanSum q z = 0 := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    rw [← cohenCorrelation_eq]
    exact hc n
  simp only [hz, ite_self, sum_const_zero, mul_zero]

theorem generalCoefficient_odd_prime_sq (q k p : ℕ) [NeZero q] [NeZero k]
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q) (ell b x : ℤ) :
    generalCoefficient q k ell b x = 0 := by
  exact generalCoefficient_eq_zero_of_cohen_zero q k ell b x
    (cohenCorrelation_eq_zero_of_odd_prime_sq q p (NeZero.ne q) hp2 hd)

theorem generalCoefficient_sixteen_dvd (q k : ℕ) [NeZero q] [NeZero k]
    (hd : 16 ∣ q) (ell b x : ℤ) : generalCoefficient q k ell b x = 0 := by
  exact generalCoefficient_eq_zero_of_cohen_zero q k ell b x
    (cohenCorrelation_eq_zero_of_sixteen_dvd q (NeZero.ne q) hd)

/-- CRT separates any pair of coordinate restrictions in the C_q correlation. -/
theorem scaled_quadratic_filtered_crt (m n : ℕ) [NeZero m] [NeZero n] (hc : m.Coprime n)
    (P : ZMod (m * n) → Prop) (Pm : ZMod m → Prop) (Pn : ZMod n → Prop)
    [DecidablePred P] [DecidablePred Pm] [DecidablePred Pn]
    (hP : ∀ r, P r ↔ Pm (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) r) ∧
      Pn (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) r)) (ell : ℤ) (x : ZMod (m * n)) :
    (∑ r : (ZMod (m * n))ˣ, if P r then quadraticRamanujanSum (m * n) (x - (ell : ZMod (m * n)) * (r : ZMod (m * n))) else 0) =
      (∑ r : (ZMod m)ˣ, if Pm r then quadraticRamanujanSum m
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x - (ell : ZMod m) * (r : ZMod m)) else 0) *
      (∑ r : (ZMod n)ˣ, if Pn r then quadraticRamanujanSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x - (ell : ZMod n) * (r : ZMod n)) else 0) := by
  classical
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        (if Pm ab.1 then quadraticRamanujanSum m
          (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x - (ell : ZMod m) * (ab.1 : ZMod m)) else 0) *
        (if Pn ab.2 then quadraticRamanujanSum n
          (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x - (ell : ZMod n) * (ab.2 : ZMod n)) else 0) := by
      rw [← Equiv.sum_comp (crtUnitsEquiv hc).symm.toEquiv]
      apply sum_congr rfl
      intro ab _
      let r : (ZMod (m * n))ˣ := (crtUnitsEquiv hc).symm ab
      change (if P (r : ZMod (m * n)) then
        quadraticRamanujanSum (m * n) (x - (ell : ZMod (m * n)) * (r : ZMod (m * n))) else 0) = _
      have ht := crtUnitsEquiv_cast hc r
      dsimp only [r] at ht
      simp only [MulEquiv.apply_symm_apply] at ht
      change (ab.1 : ZMod m) = ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) r ∧
        (ab.2 : ZMod n) = ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) r at ht
      simp only [hP, quadraticRamanujanSum_coprime_mul m n hc, map_sub, map_mul, map_intCast, ← ht.1, ← ht.2]
      by_cases hm : Pm (ab.1 : ZMod m) <;> by_cases hn : Pn (ab.2 : ZMod n) <;>
        simp only [hm, hn, and_self, and_false, false_and, ite_true, ite_false, zero_mul, mul_zero]
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

/-- The coefficient is multiplicative in the actual modulus, not just in a local model. -/
theorem generalCoefficient_mul (m n k : ℕ) [NeZero k] (hc : m.Coprime n) (ell b x : ℤ) :
    generalCoefficient (m * n) k ell b x =
      generalCoefficient m k ell b x * generalCoefficient n k ell b x := by
  classical
  by_cases hm : m = 0
  · simp [hm, generalCoefficient]
  by_cases hn : n = 0
  · simp [hn, generalCoefficient]
  have : NeZero m := ⟨hm⟩
  have : NeZero n := ⟨hn⟩
  have hg : (m * n).gcd k = m.gcd k * n.gcd k := by
    simpa only [Nat.gcd_comm] using hc.gcd_mul k
  have hcg : (m.gcd k).Coprime (n.gcd k) :=
    (hc.of_dvd_left (Nat.gcd_dvd_left m k)).of_dvd_right (Nat.gcd_dvd_left n k)
  have hφ : ((m * n).gcd k).totient = (m.gcd k).totient * (n.gcd k).totient := by
    rw [hg, Nat.totient_mul hcg]
  have hP (r : ZMod (m * n)) :
      ZMod.castHom (Nat.gcd_dvd_left (m * n) k) (ZMod ((m * n).gcd k)) r =
        (b : ZMod ((m * n).gcd k)) ↔
      ZMod.castHom (Nat.gcd_dvd_left m k) (ZMod (m.gcd k))
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) r) = (b : ZMod (m.gcd k)) ∧
      ZMod.castHom (Nat.gcd_dvd_left n k) (ZMod (n.gcd k))
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) r) = (b : ZMod (n.gcd k)) := by
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
    have he := reduction_product_eq_iff (m * n) (m.gcd k) (n.gcd k)
      ((Nat.gcd_dvd_left m k).trans (Nat.dvd_mul_right m n))
      ((Nat.gcd_dvd_left n k).trans (Nat.dvd_mul_left n m)) hcg
      (Nat.mul_dvd_mul (Nat.gcd_dvd_left m k) (Nat.gcd_dvd_left n k)) b (z : ZMod (m * n))
    simp only [map_intCast]
    rw [hg]
    simpa only [map_intCast] using he
  rw [generalCoefficient_as_quadratic, generalCoefficient_as_quadratic,
    generalCoefficient_as_quadratic]
  have hsplit := scaled_quadratic_filtered_crt m n hc
    (fun r => ZMod.castHom (Nat.gcd_dvd_left (m * n) k) (ZMod ((m * n).gcd k)) r =
      (b : ZMod ((m * n).gcd k)))
    (fun r => ZMod.castHom (Nat.gcd_dvd_left m k) (ZMod (m.gcd k)) r = (b : ZMod (m.gcd k)))
    (fun r => ZMod.castHom (Nat.gcd_dvd_left n k) (ZMod (n.gcd k)) r = (b : ZMod (n.gcd k)))
    hP ell (x : ZMod (m * n))
  rw [hsplit]
  simp only [hφ, Nat.totient_mul hc, Nat.cast_mul, map_intCast, mul_pow, mul_div_mul_comm]
  ring

/-- At modulus one the actual coefficient equals one. -/
theorem generalCoefficient_one (k : ℕ) [NeZero k] (ell b x : ℤ) :
    generalCoefficient 1 k ell b x = 1 := by
  classical
  rw [generalCoefficient_as_quadratic]
  have : Subsingleton (ZMod (Nat.gcd 1 k)) := by
    rw [Nat.gcd_one_left]
    infer_instance
  have he (r : (ZMod 1)ˣ) :
      ZMod.castHom (Nat.gcd_dvd_left 1 k) (ZMod (Nat.gcd 1 k)) (r : ZMod 1) =
        (b : ZMod (Nat.gcd 1 k)) := Subsingleton.elim _ _
  simp only [quadraticRamanujanSum_one, Nat.gcd_one_left,
    Nat.totient_one, Nat.cast_one, one_pow, div_one, one_mul]
  calc
    _ = ∑ _ : (ZMod 1)ˣ, (1 : ℂ) := by
      apply sum_congr rfl
      intro r _
      exact ite_eq_left (he r)
    _ = 1 := by simp

end PrimeSquares
