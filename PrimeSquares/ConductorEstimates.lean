import PrimeSquares.ConductorFactors

/-!
# The two conductor-sensitive sum estimates

An admissible explicit majorant is `conductorMajorant`. Constants in this
module are absolute. The original source definition of the induced character
and both normalized exponential sums are retained throughout.
-/

open Finset

namespace PrimeSquares

theorem norm_principalCorrelation_odd_squarefree (n : ℕ) [NeZero n]
    (hodd : ¬2 ∣ n) (hsf : Squarefree n) (x : ZMod n) :
    ‖twistedSquareCorrelation n 1 x‖ ≤ conductorCorrelationProduct n := by
  classical
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  have hφnat : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_prod_factorization (NeZero.ne n)]
    apply prod_congr rfl
    intro p hp
    rw [Nat.factorization_eq_one_of_squarefree hsf (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)]
    simp
  have hφ : (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [hφnat, Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  have hC : ‖cohenCorrelation n z‖ ≤ ∏ p ∈ n.primeFactors, ((p : ℝ) + 1) := by
    rw [cohenCorrelation_odd_modulus n (NeZero.ne n) hodd,
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsf, Int.cast_one, one_mul, norm_prod]
    exact prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => norm_oddCohenFactor_le p z)
  calc
    _ = ‖cohenCorrelation n z‖ / (n.totient : ℝ) := by
      rw [twistedSquareCorrelation_principal, ← cohenCorrelation_eq, norm_mul, norm_inv,
        norm_natCast]
      ring
    _ ≤ (∏ p ∈ n.primeFactors, ((p : ℝ) + 1)) / (n.totient : ℝ) :=
      div_le_div_of_nonneg_right hC (Nat.cast_nonneg _)
    _ = _ := by rw [hφ, conductorCorrelationProduct, prod_div_distrib]

theorem dyadic_primeFactors_card_le (q₀ j : ℕ) (hq₀ : q₀ ≠ 0) :
    (q₀ * 2 ^ j).primeFactors.card ≤ q₀.primeFactors.card + 1 := by
  have h2 : (2 ^ j).primeFactors.card ≤ 1 := by
    cases j with
    | zero => simp
    | succ j => simp [Nat.primeFactors_pow_succ, Nat.prime_two.primeFactors]
  rw [Nat.primeFactors_mul hq₀ (by positivity)]
  exact (card_union_le _ _).trans (Nat.add_le_add_left h2 _)

theorem dyadic_sqrt_le (m j : ℕ) (hj : j ≤ 5) :
    Real.sqrt (m * 2 ^ j : ℕ) ≤ 8 * Real.sqrt m := by
  have h2 : 2 ^ j ≤ (64 : ℕ) := (Nat.pow_le_pow_right (by decide) hj).trans (by norm_num)
  have hm : (m * 2 ^ j : ℕ) ≤ 64 * m := by
    simpa only [mul_comm m 64] using Nat.mul_le_mul_left m h2
  calc
    _ ≤ Real.sqrt ((64 : ℝ) * m) := Real.sqrt_le_sqrt (by exact_mod_cast hm)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num), show (64 : ℝ) = 8 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]

theorem norm_dyadicTwistedCorrelation_le_majorant (q₀ j : ℕ) [NeZero q₀]
    (hj : j ≤ 5) (χ : DirichletCharacter ℂ (q₀ * 2 ^ j)) (x : ZMod (q₀ * 2 ^ j)) :
    ‖twistedSquareCorrelation (q₀ * 2 ^ j) χ x‖ ≤ conductorMajorant q₀ := by
  have hp : (8 : ℝ) ^ (q₀ * 2 ^ j).primeFactors.card ≤ 8 * (8 : ℝ) ^ q₀.primeFactors.card := by
    calc
      _ ≤ (8 : ℝ) ^ (q₀.primeFactors.card + 1) :=
        pow_le_pow_right₀ (by norm_num) (dyadic_primeFactors_card_le q₀ j (NeZero.ne q₀))
      _ = _ := by rw [pow_succ, mul_comm]
  have hs := dyadic_sqrt_le q₀ j hj
  calc
    _ ≤ (8 : ℝ) ^ (q₀ * 2 ^ j).primeFactors.card * Real.sqrt (q₀ * 2 ^ j : ℕ) :=
      norm_twistedCorrelation_finite_bound _ χ x
    _ ≤ (8 * (8 : ℝ) ^ q₀.primeFactors.card) * (8 * Real.sqrt q₀) :=
      mul_le_mul hp hs (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by dsimp only [conductorMajorant]; ring

/-- The source character at a double multiple is the iterated induced character. -/
theorem induced_character_mul_trans (q₀ k n : ℕ) (χ₀ : DirichletCharacter ℂ q₀) :
    DirichletCharacter.changeLevel
      ((Nat.dvd_mul_right q₀ k).trans (Nat.dvd_mul_right (q₀ * k) n)) χ₀ =
    DirichletCharacter.changeLevel (Nat.dvd_mul_right (q₀ * k) n)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ k) χ₀) :=
  DirichletCharacter.changeLevel_trans χ₀ _ _

theorem twistedCorrelation_zero_of_all_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (h : ∀ a : (ZMod q)ˣ, twistedSquareSum q χ a = 0)
    (x : ZMod q) : twistedSquareCorrelation q χ x = 0 := by
  simp only [twistedSquareCorrelation, h, zero_mul, sum_const_zero]

/-- The first estimate of e:exceptionalarithmetic, with implied constant one. -/
theorem induced_twistedCorrelation_conductor_bound (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ₀ : χ₀.IsQuadratic) (x : ZMod (q₀ * d)) :
    ‖twistedSquareCorrelation (q₀ * d)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) x‖ ≤
      conductorMajorant q₀ * conductorCorrelationProduct d := by
  classical
  let χ := DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀
  by_cases hz : ∀ a : (ZMod (q₀ * d))ˣ, twistedSquareSum (q₀ * d) χ a = 0
  · rw [twistedCorrelation_zero_of_all_zero (q₀ * d) χ hz, norm_zero]
    exact mul_nonneg (le_trans (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀)))
      (le_trans (by norm_num) (conductorCorrelationProduct_one_le d))
  · push Not at hz
    obtain ⟨a, ha⟩ := hz
    obtain ⟨ν, d₁, hν, hd₁, hsf, hcop, he⟩ := twistedSquareSum_conductor_support q₀ d χ
      (quadratic_character_changeLevel _ χ₀ hχ₀) a a.isUnit ha
    have : NeZero d₁ := ⟨hd₁.ne'⟩
    have hc₂ : d₁.Coprime 2 := hcop.of_dvd_right (Nat.dvd_mul_right 2 q₀)
    have hc₀ : d₁.Coprime q₀ := hcop.of_dvd_right (Nat.dvd_mul_left q₀ 2)
    have hc : (q₀ * 2 ^ ν).Coprime d₁ := hc₀.symm.mul_left (hc₂.symm.pow_left ν)
    have hodd : ¬2 ∣ d₁ := Nat.prime_two.coprime_iff_not_dvd.mp hc₂.symm
    have H (r : ℕ) [NeZero r] (hr : r = (q₀ * 2 ^ ν) * d₁) (hdiv : q₀ ∣ r)
        (x : ZMod r) :
        ‖twistedSquareCorrelation r (DirichletCharacter.changeLevel hdiv χ₀) x‖ ≤
          conductorMajorant q₀ * conductorCorrelationProduct d₁ := by
      subst r
      rw [induced_character_mul_trans q₀ (2 ^ ν) d₁,
        induced_twistedCorrelation_coprime_mul (q₀ * 2 ^ ν) d₁ hc, norm_mul]
      exact mul_le_mul (norm_dyadicTwistedCorrelation_le_majorant q₀ ν hν _ _)
        (norm_principalCorrelation_odd_squarefree d₁ hodd hsf _)
        (norm_nonneg _) (by have := conductorMajorant_one_le q₀ (NeZero.pos q₀); linarith)
    calc
      _ ≤ conductorMajorant q₀ * conductorCorrelationProduct d₁ :=
        H (q₀ * d) (by rw [he, Nat.mul_assoc]) (Nat.dvd_mul_right q₀ d) x
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (conductorCorrelationProduct_mono (by rw [he]; exact Nat.dvd_mul_left d₁ (2 ^ ν))
          (NeZero.ne d))
        (by have := conductorMajorant_one_le q₀ (NeZero.pos q₀); linarith)

theorem induced_twistedSquareSum_split_bound (q₀ ν d₁ : ℕ) [NeZero q₀] [NeZero d₁]
    (χ₀ : DirichletCharacter ℂ q₀) (hν : ν ≤ 5) (hc : (q₀ * 2 ^ ν).Coprime d₁)
    (a : ZMod ((q₀ * 2 ^ ν) * d₁)) (ha : IsUnit a) :
    ‖twistedSquareSum ((q₀ * 2 ^ ν) * d₁)
      (DirichletCharacter.changeLevel
        ((Nat.dvd_mul_right q₀ (2 ^ ν)).trans (Nat.dvd_mul_right (q₀ * 2 ^ ν) d₁)) χ₀) a‖ ≤
      conductorSigma q₀ χ₀ * ((4 / Real.sqrt d₁) * conductorRho d₁) := by
  let a₀ : ZMod (q₀ * 2 ^ ν) :=
    ZMod.castHom (Nat.dvd_mul_right (q₀ * 2 ^ ν) d₁) (ZMod (q₀ * 2 ^ ν)) a *
      (((ZMod.unitOfCoprime d₁ hc.symm)⁻¹ : (ZMod (q₀ * 2 ^ ν))ˣ) : ZMod (q₀ * 2 ^ ν))
  let a₁ : ZMod d₁ :=
    ZMod.castHom (Nat.dvd_mul_left d₁ (q₀ * 2 ^ ν)) (ZMod d₁) a *
      (((ZMod.unitOfCoprime (q₀ * 2 ^ ν) hc)⁻¹ : (ZMod d₁)ˣ) : ZMod d₁)
  have ha₀ : IsUnit a₀ := (ha.map
    (ZMod.castHom (Nat.dvd_mul_right (q₀ * 2 ^ ν) d₁) (ZMod (q₀ * 2 ^ ν)))).mul
      ((ZMod.unitOfCoprime d₁ hc.symm)⁻¹).isUnit
  have ha₁ : IsUnit a₁ := (ha.map
    (ZMod.castHom (Nat.dvd_mul_left d₁ (q₀ * 2 ^ ν)) (ZMod d₁))).mul
      ((ZMod.unitOfCoprime (q₀ * 2 ^ ν) hc)⁻¹).isUnit
  have hσ : ‖twistedSquareSum (q₀ * 2 ^ ν)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ ν)) χ₀) a₀‖ ≤
      conductorSigma q₀ χ₀ := by
    simpa only [IsUnit.unit_spec] using norm_inducedSquareSum_le_sigma q₀ ν χ₀ hν ha₀.unit
  rw [induced_character_mul_trans q₀ (2 ^ ν) d₁,
    induced_twistedSquareSum_coprime_mul (q₀ * 2 ^ ν) d₁ hc, norm_mul]
  change ‖twistedSquareSum (q₀ * 2 ^ ν)
    (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ (2 ^ ν)) χ₀) a₀‖ *
    ‖principalSquareSum d₁ a₁‖ ≤ _
  apply mul_le_mul hσ _ (norm_nonneg _) (conductorSigma_nonneg _ _)
  exact (principalSquareSum_finite_product_bound d₁ a₁ ha₁).trans
    (mul_le_mul_of_nonneg_left (gaussOddProduct_le_conductorRho d₁) (by positivity))

/-- The second estimate of e:exceptionalarithmetic, with absolute constant 32. -/
theorem induced_twistedSquareSum_conductor_bound (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ₀ : χ₀.IsQuadratic)
    (a : ZMod (q₀ * d)) (ha : IsUnit a) :
    ‖twistedSquareSum (q₀ * d)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) a‖ ≤
      (32 * conductorSigma q₀ χ₀ / Real.sqrt d) * conductorRho d := by
  let χ := DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀
  by_cases hz : twistedSquareSum (q₀ * d) χ a = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (conductorSigma_nonneg _ _))
      (Real.sqrt_nonneg _)) (le_trans (by norm_num) (conductorRho_one_le d))
  · obtain ⟨ν, d₁, hν, hd₁, _hsf, hcop, he⟩ := twistedSquareSum_conductor_support q₀ d χ
      (quadratic_character_changeLevel _ χ₀ hχ₀) a ha hz
    have : NeZero d₁ := ⟨hd₁.ne'⟩
    have hc₂ : d₁.Coprime 2 := hcop.of_dvd_right (Nat.dvd_mul_right 2 q₀)
    have hc₀ : d₁.Coprime q₀ := hcop.of_dvd_right (Nat.dvd_mul_left q₀ 2)
    have hc : (q₀ * 2 ^ ν).Coprime d₁ := hc₀.symm.mul_left (hc₂.symm.pow_left ν)
    have H (r : ℕ) [NeZero r] (hr : r = (q₀ * 2 ^ ν) * d₁) (hdiv : q₀ ∣ r)
        (a : ZMod r) (ha : IsUnit a) :
        ‖twistedSquareSum r (DirichletCharacter.changeLevel hdiv χ₀) a‖ ≤
          conductorSigma q₀ χ₀ * ((4 / Real.sqrt d₁) * conductorRho d₁) := by
      subst r
      exact induced_twistedSquareSum_split_bound q₀ ν d₁ χ₀ hν hc a ha
    have hs₁ : 0 < Real.sqrt (d₁ : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd₁)
    have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos d)
    have hscale : (4 : ℝ) / Real.sqrt d₁ ≤ 32 / Real.sqrt d := by
      have hs : Real.sqrt (d : ℝ) ≤ 8 * Real.sqrt d₁ := by
        simpa only [he, mul_comm (2 ^ ν) d₁] using dyadic_sqrt_le d₁ ν hν
      exact (div_le_div_iff₀ hs₁ hsd).mpr (by nlinarith)
    have hρ : conductorRho d₁ ≤ conductorRho d :=
      conductorRho_mono (by rw [he]; exact Nat.dvd_mul_left d₁ (2 ^ ν)) (NeZero.ne d)
    calc
      _ ≤ conductorSigma q₀ χ₀ * ((4 / Real.sqrt d₁) * conductorRho d₁) :=
        H (q₀ * d) (by rw [he, Nat.mul_assoc]) (Nat.dvd_mul_right q₀ d) a ha
      _ ≤ conductorSigma q₀ χ₀ * ((32 / Real.sqrt d) * conductorRho d) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hscale hρ (le_trans (by norm_num) (conductorRho_one_le d₁)) (by positivity))
          (conductorSigma_nonneg _ _)
      _ = _ := by ring

end PrimeSquares
