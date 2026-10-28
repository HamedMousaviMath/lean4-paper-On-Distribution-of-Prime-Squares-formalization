import PrimeSquares.ProgressionCohen

/-!
# Correlation of the progression and square exponential sums

Source: Draft5, Lemma 3.12 (`l:sumoverramanujan`). The definitions retain
both minus signs and the exact totient normalizations of `e:upsilondef` and
`e:mathfraks`. The finite expansion is proved first, then Lemma 3.11 is used.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace PrimeSquares

/-- A divisor of a positive modulus is positive, specialized to the gcd. -/
instance gcdNeZeroLeft (q y : ℕ) [NeZero q] : NeZero (q.gcd y) :=
  ⟨(Nat.gcd_pos_of_pos_left y (Nat.pos_of_ne_zero (NeZero.ne q))).ne'⟩

/-- The complementary modulus in Lemma 3.12 is also positive. -/
instance gcdQuotientNeZero (q y : ℕ) [NeZero q] : NeZero (q / q.gcd y) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.gcd_dvd_left q y))
    (Nat.pos_of_ne_zero (NeZero.ne (q.gcd y)))).ne'⟩

/-- The unnormalized progression exponential sum. -/
noncomputable def progressionExponentialSum (q g : ℕ) [NeZero q]
    (hg : g ∣ q) (b : ZMod g) (a : ZMod q) : ℂ :=
  ∑ r : (ZMod q)ˣ, if ZMod.castHom hg (ZMod g) (r : ZMod q) = b
    then ZMod.stdAddChar (-(a * (r : ZMod q))) else 0

/-- The principal-character square sum, with exactly the paper's normalization. -/
noncomputable def principalSquareSum (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-(a * (u : ZMod q) ^ 2))

/-- Upsilon from `e:upsilondef`, including its gcd and lcm. -/
noncomputable def upsilon (q y : ℕ) [NeZero q] (b : ℤ) (a : ZMod q) : ℂ :=
  ((Nat.totient y : ℂ) / (Nat.totient (y.lcm q) : ℂ)) *
    progressionExponentialSum q (q.gcd y) (Nat.gcd_dvd_left q y) (b : ZMod (q.gcd y)) a

/-- Opening the two sums gives the genuine Ramanujan correlation, with no analytic input. -/
theorem progression_correlation_expansion (q g : ℕ) [NeZero q] [NeZero g]
    (hg : g ∣ q) (b : ZMod g) (x : ZMod q) :
    (∑ a : (ZMod q)ˣ, progressionExponentialSum q g hg b a *
      (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q) * (u : ZMod q) ^ 2))) *
      ZMod.stdAddChar ((a : ZMod q) * x)) =
      ∑ u : (ZMod q)ˣ, progressionRamanujanSum q g hg b (x - (u : ZMod q) ^ 2) := by
  classical
  have he (a : (ZMod q)ˣ) :
      progressionExponentialSum q g hg b a *
        (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q) * (u : ZMod q) ^ 2))) *
        ZMod.stdAddChar ((a : ZMod q) * x) =
      ∑ u : (ZMod q)ˣ, ∑ r : (ZMod q)ˣ,
        if ZMod.castHom hg (ZMod g) (r : ZMod q) = b then
          ZMod.stdAddChar ((x - (u : ZMod q) ^ 2 - (r : ZMod q)) * (a : ZMod q)) else 0 := by
    unfold progressionExponentialSum
    simp_rw [sum_mul, mul_sum]
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro r _
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
  unfold progressionRamanujanSum
  apply sum_congr rfl
  intro r _
  rw [sum_ite_irrel]
  split_ifs
  · rw [ramanujanSum, sum_unit_filter_eq_sum_units]
  · simp

/-- Normalize the actual paper sums; positivity justifies every cancelled denominator. -/
theorem normalized_upsilon_correlation_expansion (q y : ℕ) [NeZero q] [NeZero y]
    [NeZero (q.gcd y)] (b x : ℤ) :
    ((Nat.totient q : ℂ) * (Nat.totient (y.lcm q) : ℂ) / (Nat.totient y : ℂ)) *
      (∑ a : (ZMod q)ˣ, upsilon q y b a * principalSquareSum q a *
        ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q))) =
      ∑ u : (ZMod q)ˣ, progressionRamanujanSum q (q.gcd y) (Nat.gcd_dvd_left q y)
        (b : ZMod (q.gcd y)) ((x : ZMod q) - (u : ZMod q) ^ 2) := by
  have hq : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  have hy : (Nat.totient y : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne y))).ne'
  have hl : (Nat.totient (y.lcm q) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.lcm_pos
      (Nat.pos_of_ne_zero (NeZero.ne y)) (Nat.pos_of_ne_zero (NeZero.ne q)))).ne'
  rw [mul_sum]
  calc
    _ = ∑ a : (ZMod q)ˣ,
        progressionExponentialSum q (q.gcd y) (Nat.gcd_dvd_left q y)
          (b : ZMod (q.gcd y)) a *
        (∑ u : (ZMod q)ˣ, ZMod.stdAddChar (-((a : ZMod q) * (u : ZMod q) ^ 2))) *
        ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q)) := by
      apply sum_congr rfl
      intro a _
      unfold upsilon principalSquareSum
      field_simp
    _ = _ := progression_correlation_expansion q (q.gcd y) _ _ _

/-- Equation `e:eqjustforLHS`, including the exact normalizations and both branches. -/
theorem sum_upsilon_square_identity (q y : ℕ) [NeZero q] [NeZero y]
    (b x : ℤ) (hb : IsCoprime (q.gcd y : ℤ) b) :
    let g := q.gcd y
    let h := q / g
    ((Nat.totient q : ℂ) * (Nat.totient (y.lcm q) : ℂ) / (Nat.totient y : ℂ)) *
      (∑ a : (ZMod q)ˣ, upsilon q y b a * principalSquareSum q a *
        ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q))) =
      (μ h : ℂ) * (if g.Coprime h then (1 : ℂ) else 0) *
        ∑ u : (ZMod q)ˣ,
          ramanujanSum h (ZMod.castHom (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q y)) (ZMod h)
            ((x : ZMod q) - (u : ZMod q) ^ 2)) *
          ramanujanSum g (ZMod.castHom (Nat.gcd_dvd_left q y) (ZMod g)
            ((x : ZMod q) - (u : ZMod q) ^ 2) - (b : ZMod g)) := by
  classical
  dsimp only
  rw [normalized_upsilon_correlation_expansion]
  simp_rw [progression_cohen_identity_residue q (q.gcd y) (Nat.gcd_dvd_left q y)
    (b : ZMod (q.gcd y)) ((ZMod.coe_int_isUnit_iff_isCoprime b (q.gcd y)).mpr hb)]
  by_cases hc : (q.gcd y).Coprime (q / q.gcd y)
  · simp only [ite_eq_left hc, mul_one]
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    ring
  · simp only [ite_eq_right hc, mul_zero, sum_const_zero, zero_mul]

/-- The vanishing assertion in Lemma 3.12 follows from the checked Möbius factor. -/
theorem sum_upsilon_square_eq_zero_of_not_squarefree (q y : ℕ) [NeZero q] [NeZero y]
    (b x : ℤ) (hb : IsCoprime (q.gcd y : ℤ) b) (hs : ¬Squarefree (q / q.gcd y)) :
    ((Nat.totient q : ℂ) * (Nat.totient (y.lcm q) : ℂ) / (Nat.totient y : ℂ)) *
      (∑ a : (ZMod q)ˣ, upsilon q y b a * principalSquareSum q a *
        ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q))) = 0 := by
  rw [sum_upsilon_square_identity q y b x hb,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  simp

/-- Under coprimality, the two differently shifted quadratic factors split by CRT. -/
theorem progression_quadratic_correlation_coprime (g h : ℕ) [NeZero g] [NeZero h]
    (hc : g.Coprime h) (b : ZMod g) (x : ZMod (g * h)) :
    (∑ u : (ZMod (g * h))ˣ,
      ramanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h)
        (x - (u : ZMod (g * h)) ^ 2)) *
      ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g)
        (x - (u : ZMod (g * h)) ^ 2) - b)) =
      quadraticRamanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) x - b) *
      quadraticRamanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h) x) := by
  classical
  calc
    _ = ∑ ab : (ZMod g)ˣ × (ZMod h)ˣ,
        ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g) x - b -
          (ab.1 : ZMod g) ^ 2) *
        ramanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h) x -
          (ab.2 : ZMod h) ^ 2) := by
      rw [← Equiv.sum_comp (crtUnitsEquiv hc).symm.toEquiv]
      apply sum_congr rfl
      intro ab _
      have ht := crtUnitsEquiv_cast hc ((crtUnitsEquiv hc).symm ab)
      simp only [MulEquiv.apply_symm_apply] at ht
      change ramanujanSum h (ZMod.castHom (Nat.dvd_mul_left h g) (ZMod h)
          (x - (((crtUnitsEquiv hc).symm ab : (ZMod (g * h))ˣ) : ZMod (g * h)) ^ 2)) *
        ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g)
          (x - (((crtUnitsEquiv hc).symm ab : (ZMod (g * h))ˣ) : ZMod (g * h)) ^ 2) - b) = _
      simp only [map_sub, map_pow, ← ht.1, ← ht.2]
      rw [mul_comm]
      congr 2
      ring
    _ = _ := by
      simp only [quadraticRamanujanSum, sum_unit_filter_eq_sum_units]
      rw [Fintype.sum_prod_type, sum_mul_sum]

/-- Divisor/quotient form of the CRT splitting, for the paper's integer inputs. -/
theorem progression_quadratic_correlation_factorization (q g : ℕ) [NeZero q] [NeZero g]
    [hdiv : NeZero (q / g)] (hg : g ∣ q) (hc : g.Coprime (q / g)) (b x : ℤ) :
    (∑ u : (ZMod q)ˣ,
      ramanujanSum (q / g) (ZMod.castHom (Nat.div_dvd_of_dvd hg) (ZMod (q / g))
        ((x : ZMod q) - (u : ZMod q) ^ 2)) *
      ramanujanSum g (ZMod.castHom hg (ZMod g)
        ((x : ZMod q) - (u : ZMod q) ^ 2) - (b : ZMod g))) =
      cohenCorrelation g (x - b) * cohenCorrelation (q / g) x := by
  obtain ⟨h, rfl⟩ := hg
  have : NeZero h := ⟨fun hz => NeZero.ne (g * h) (by rw [hz, mul_zero])⟩
  have hd : g * h / g = h := Nat.mul_div_right h (Nat.pos_of_ne_zero (NeZero.ne g))
  have hc' : g.Coprime h := by simpa only [hd] using hc
  have hf (d : ℕ) [NeZero d] (hdvd : d ∣ g * h) (he : d = h) :
      (∑ u : (ZMod (g * h))ˣ,
        ramanujanSum d (ZMod.castHom hdvd (ZMod d)
          ((x : ZMod (g * h)) - (u : ZMod (g * h)) ^ 2)) *
        ramanujanSum g (ZMod.castHom (Nat.dvd_mul_right g h) (ZMod g)
          ((x : ZMod (g * h)) - (u : ZMod (g * h)) ^ 2) - (b : ZMod g))) =
        cohenCorrelation g (x - b) * cohenCorrelation d x := by
    subst d
    simpa only [cohenCorrelation_eq, map_intCast, Int.cast_sub] using
      progression_quadratic_correlation_coprime g h hc' (b : ZMod g) (x : ZMod (g * h))
  exact hf (g * h / g) (Nat.div_dvd_of_dvd (Nat.dvd_mul_right g h)) hd

/-- The final assertion of Lemma 3.12, as an explicit product over the prime powers.
Coprimality makes the prime supports of g and h disjoint, with q=g*h. -/
theorem sum_upsilon_square_prime_factorization (q y : ℕ) [NeZero q] [NeZero y]
    (b x : ℤ) (hb : IsCoprime (q.gcd y : ℤ) b)
    (hc : (q.gcd y).Coprime (q / q.gcd y)) :
    let g := q.gcd y
    let h := q / g
    ((Nat.totient q : ℂ) * (Nat.totient (y.lcm q) : ℂ) / (Nat.totient y : ℂ)) *
      (∑ a : (ZMod q)ˣ, upsilon q y b a * principalSquareSum q a *
        ZMod.stdAddChar ((a : ZMod q) * (x : ZMod q))) =
      (∏ p ∈ g.primeFactors, cohenCorrelation (p ^ g.factorization p) (x - b)) *
        (∏ p ∈ h.primeFactors,
          (μ (p ^ h.factorization p) : ℂ) * cohenCorrelation (p ^ h.factorization p) x) := by
  classical
  dsimp only
  rw [sum_upsilon_square_identity q y b x hb]
  simp only [ite_eq_left hc, mul_one]
  rw [progression_quadratic_correlation_factorization q (q.gcd y)
    (Nat.gcd_dvd_left q y) hc b x,
    cohenCorrelation_factorization (q.gcd y) (NeZero.ne _) (x - b),
    cohenCorrelation_factorization (q / q.gcd y) (NeZero.ne _) x]
  have hm : (μ (q / q.gcd y) : ℂ) =
      ∏ p ∈ (q / q.gcd y).primeFactors, (μ (p ^ (q / q.gcd y).factorization p) : ℂ) := by
    exact Nat.multiplicative_factorization (fun n => (μ n : ℂ))
      (fun a b hab => by
        rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab, Int.cast_mul])
      (by simp) (NeZero.ne _)
  rw [prod_mul_distrib, ← hm]
  ring

end PrimeSquares
