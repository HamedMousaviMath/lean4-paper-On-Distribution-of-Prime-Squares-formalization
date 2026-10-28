import PrimeSquares.ProgressionCorrelation

/-!
# The actual fixed-modulus coefficient for the smooth Euler product

Source: Draft5, Lemma 3.14 (`l:motamakemajorprimesquareprog`). The coefficient
is the actual sum of Upsilon times the principal square sum, extended by zero
at modulus zero. Opening it in the other summation order exposes C_q(x-r),
so the checked quadratic Cohen factors give uniform vanishing at bad moduli.
-/

open Finset

namespace PrimeSquares

noncomputable def progressionCoefficient (q k : ℕ) (b x : ℤ) : ℂ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ∑ a : (ZMod q)ˣ, upsilon q k b a * principalSquareSum q a *
      ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q))

theorem progressionCoefficient_eq (q k : ℕ) [NeZero q] (b x : ℤ) :
    progressionCoefficient q k b x =
      ∑ a : (ZMod q)ˣ, upsilon q k b a * principalSquareSum q a *
        ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q)) := by
  simp [progressionCoefficient, NeZero.ne q]

/-- Multiplicativity of the totient implies its exact gcd/lcm identity. -/
theorem totient_lcm_mul_totient_gcd (q k : ℕ) :
    (q.lcm k).totient * (q.gcd k).totient = q.totient * k.totient := by
  let f : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩
  have hf : f.IsMultiplicative := ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  exact hf.lcm_apply_mul_gcd_apply

/-- Reordering the finite correlation exposes the already proved C_q factor. -/
theorem progression_correlation_as_quadratic (q g : ℕ) [NeZero q] [NeZero g]
    (hg : g ∣ q) (b : ZMod g) (x : ZMod q) :
    (∑ u : (ZMod q)ˣ, progressionRamanujanSum q g hg b (x - (u : ZMod q) ^ 2)) =
      ∑ r : (ZMod q)ˣ, if ZMod.castHom hg (ZMod g) (r : ZMod q) = b
        then quadraticRamanujanSum q (x - (r : ZMod q)) else 0 := by
  classical
  unfold progressionRamanujanSum
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [sum_ite_irrel]
  split_ifs
  · simp only [quadraticRamanujanSum, sum_unit_filter_eq_sum_units]
    apply sum_congr rfl
    intro u _
    congr 1
    ring
  · simp

/-- The exact weight is phi(gcd(q,k))/phi(q)^2. No distribution estimate is used. -/
theorem progressionCoefficient_as_quadratic (q k : ℕ) [NeZero q] [NeZero k] (b x : ℤ) :
    progressionCoefficient q k b x =
      ((q.gcd k).totient : ℂ) / (q.totient : ℂ) ^ 2 *
        ∑ r : (ZMod q)ˣ,
          if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (r : ZMod q) =
              (b : ZMod (q.gcd k))
          then quadraticRamanujanSum q ((x : ZMod q) - (r : ZMod q)) else 0 := by
  have hq : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hk : (k.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos k)).ne'
  have hl : ((k.lcm q).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos (NeZero.pos k) (NeZero.pos q))).ne'
  have ht : ((k.lcm q).totient : ℂ) * ((q.gcd k).totient : ℂ) =
      (q.totient : ℂ) * (k.totient : ℂ) := by
    exact_mod_cast (by simpa only [Nat.lcm_comm k q] using totient_lcm_mul_totient_gcd q k)
  have he := normalized_upsilon_correlation_expansion q k b x
  rw [← progressionCoefficient_eq, progression_correlation_as_quadratic] at he
  have hs : ((q.gcd k).totient : ℂ) / (q.totient : ℂ) ^ 2 =
      ((Nat.totient q : ℂ) * (Nat.totient (k.lcm q) : ℂ) / (Nat.totient k : ℂ))⁻¹ := by
    field_simp
    linear_combination ht
  rw [hs, ← he]
  field_simp

/-- A prime square dividing q forces C_q to vanish at every input. -/
theorem cohenCorrelation_eq_zero_of_odd_prime_sq (q p : ℕ) (hq : q ≠ 0)
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q) (x : ℤ) :
    cohenCorrelation q x = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have he : 2 ≤ q.factorization p := (hp.pow_dvd_iff_le_factorization hq).mp hd
  have hm : p ∈ q.primeFactors := by
    change p ∈ q.factorization.support
    exact Finsupp.mem_support_iff.mpr (by omega)
  rw [cohenCorrelation_factorization q hq]
  apply prod_eq_zero hm
  rw [cohenCorrelation_odd_prime_pow p hp2 _ (by omega)]
  simp only [ite_eq_right (show q.factorization p ≠ 1 by omega), zero_mul]

/-- The factor at sixteen kills C_q for every multiple of sixteen. -/
theorem cohenCorrelation_eq_zero_of_sixteen_dvd (q : ℕ) (hq : q ≠ 0)
    (hd : 16 ∣ q) (x : ℤ) : cohenCorrelation q x = 0 := by
  classical
  have he : 4 ≤ q.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hq).mp hd
  have hm : 2 ∈ q.primeFactors := by
    change 2 ∈ q.factorization.support
    exact Finsupp.mem_support_iff.mpr (by omega)
  rw [cohenCorrelation_factorization q hq]
  apply prod_eq_zero hm
  rw [cohenCorrelation_two_pow]
  simp [twoAdicCohenFactor, show q.factorization 2 ≠ 0 by omega,
    show q.factorization 2 ≠ 1 by omega, show q.factorization 2 ≠ 2 by omega,
    show q.factorization 2 ≠ 3 by omega]

/-- Pointwise C_q vanishing transfers to the actual progression coefficient. -/
theorem progressionCoefficient_eq_zero_of_cohen_zero (q k : ℕ) [NeZero q] [NeZero k]
    (b x : ℤ) (hc : ∀ z : ℤ, cohenCorrelation q z = 0) :
    progressionCoefficient q k b x = 0 := by
  classical
  rw [progressionCoefficient_as_quadratic]
  have hz (z : ZMod q) : quadraticRamanujanSum q z = 0 := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective z
    rw [← cohenCorrelation_eq]
    exact hc n
  simp only [hz, ite_self, sum_const_zero, mul_zero]

theorem progressionCoefficient_odd_prime_sq (q k p : ℕ) [NeZero q] [NeZero k]
    [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ^ 2 ∣ q) (b x : ℤ) :
    progressionCoefficient q k b x = 0 := by
  exact progressionCoefficient_eq_zero_of_cohen_zero q k b x
    (cohenCorrelation_eq_zero_of_odd_prime_sq q p (NeZero.ne q) hp2 hd)

theorem progressionCoefficient_sixteen_dvd (q k : ℕ) [NeZero q] [NeZero k]
    (hd : 16 ∣ q) (b x : ℤ) : progressionCoefficient q k b x = 0 := by
  exact progressionCoefficient_eq_zero_of_cohen_zero q k b x
    (cohenCorrelation_eq_zero_of_sixteen_dvd q (NeZero.ne q) hd)

/-- Congruence modulo a coprime product is exactly the pair of congruences. -/
theorem reduction_product_eq_iff (q g h : ℕ) (hg : g ∣ q) (hh : h ∣ q)
    (hc : g.Coprime h) (hgh : g * h ∣ q) (b : ℤ) (r : ZMod q) :
    ZMod.castHom hgh (ZMod (g * h)) r = (b : ZMod (g * h)) ↔
      ZMod.castHom hg (ZMod g) r = (b : ZMod g) ∧
      ZMod.castHom hh (ZMod h) r = (b : ZMod h) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
  simp only [map_intCast]
  constructor
  · intro he
    constructor
    · simpa only [map_intCast] using
        congrArg (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g)) he
    · simpa only [map_intCast] using
        congrArg (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h)) he
  · rintro ⟨hg', hh'⟩
    apply (ZMod.chineseRemainder hc).injective
    simp only [map_intCast]
    exact Prod.ext hg' hh'

/-- CRT separates any pair of coordinate restrictions in the C_q correlation. -/
theorem quadratic_filtered_crt (m n : ℕ) [NeZero m] [NeZero n] (hc : m.Coprime n)
    (P : ZMod (m * n) → Prop) (Pm : ZMod m → Prop) (Pn : ZMod n → Prop)
    [DecidablePred P] [DecidablePred Pm] [DecidablePred Pn]
    (hP : ∀ r, P r ↔ Pm (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) r) ∧
      Pn (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) r)) (x : ZMod (m * n)) :
    (∑ r : (ZMod (m * n))ˣ, if P r then quadraticRamanujanSum (m * n) (x - r) else 0) =
      (∑ r : (ZMod m)ˣ, if Pm r then quadraticRamanujanSum m
        (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x - r) else 0) *
      (∑ r : (ZMod n)ˣ, if Pn r then quadraticRamanujanSum n
        (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x - r) else 0) := by
  classical
  calc
    _ = ∑ ab : (ZMod m)ˣ × (ZMod n)ˣ,
        (if Pm ab.1 then quadraticRamanujanSum m
          (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) x - ab.1) else 0) *
        (if Pn ab.2 then quadraticRamanujanSum n
          (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) x - ab.2) else 0) := by
      rw [← Equiv.sum_comp (crtUnitsEquiv hc).symm.toEquiv]
      apply sum_congr rfl
      intro ab _
      let r : (ZMod (m * n))ˣ := (crtUnitsEquiv hc).symm ab
      change (if P (r : ZMod (m * n)) then
        quadraticRamanujanSum (m * n) (x - (r : ZMod (m * n))) else 0) = _
      have ht := crtUnitsEquiv_cast hc r
      dsimp only [r] at ht
      simp only [MulEquiv.apply_symm_apply] at ht
      change (ab.1 : ZMod m) = ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) r ∧
        (ab.2 : ZMod n) = ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) r at ht
      simp only [hP, quadraticRamanujanSum_coprime_mul m n hc, map_sub, ← ht.1, ← ht.2]
      by_cases hm : Pm (ab.1 : ZMod m) <;> by_cases hn : Pn (ab.2 : ZMod n) <;>
        simp only [hm, hn, and_self, and_false, false_and, ite_true, ite_false, zero_mul, mul_zero]
    _ = _ := by rw [Fintype.sum_prod_type, sum_mul_sum]

/-- The coefficient is multiplicative in the actual modulus, not just in a local model. -/
theorem progressionCoefficient_mul (m n k : ℕ) [NeZero k] (hc : m.Coprime n) (b x : ℤ) :
    progressionCoefficient (m * n) k b x =
      progressionCoefficient m k b x * progressionCoefficient n k b x := by
  classical
  by_cases hm : m = 0
  · simp [hm, progressionCoefficient]
  by_cases hn : n = 0
  · simp [hn, progressionCoefficient]
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
  rw [progressionCoefficient_as_quadratic, progressionCoefficient_as_quadratic,
    progressionCoefficient_as_quadratic]
  have hsplit := quadratic_filtered_crt m n hc
    (fun r => ZMod.castHom (Nat.gcd_dvd_left (m * n) k) (ZMod ((m * n).gcd k)) r =
      (b : ZMod ((m * n).gcd k)))
    (fun r => ZMod.castHom (Nat.gcd_dvd_left m k) (ZMod (m.gcd k)) r = (b : ZMod (m.gcd k)))
    (fun r => ZMod.castHom (Nat.gcd_dvd_left n k) (ZMod (n.gcd k)) r = (b : ZMod (n.gcd k)))
    hP (x : ZMod (m * n))
  rw [hsplit]
  simp only [hφ, Nat.totient_mul hc, Nat.cast_mul, map_intCast, mul_pow, mul_div_mul_comm]
  ring

/-- At modulus one the actual coefficient equals one. -/
theorem progressionCoefficient_one (k : ℕ) [NeZero k] (b x : ℤ) :
    progressionCoefficient 1 k b x = 1 := by
  classical
  rw [progressionCoefficient_as_quadratic]
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
