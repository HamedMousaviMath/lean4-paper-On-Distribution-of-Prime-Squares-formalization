import PrimeSquares.ConductorFactors

/-!
# Conductor decay for an admissible B₀

The source allows any B₀ depending only on q₀. We use
64 * 8^omega(q₀) * sqrt(q₀), for which the preceding uniform Gauss bound
proves the requested decay for every complex character, with an absolute
constant. Primitive-character classification is therefore unnecessary.
-/

namespace PrimeSquares

theorem sqrt_conductorMajorant_le (q₀ : ℕ) (hq₀ : 0 < q₀) :
    Real.sqrt (conductorMajorant q₀) ≤
      8 * (8 : ℝ) ^ q₀.primeFactors.card * (q₀ : ℝ) ^ (1 / 4 : ℝ) := by
  have hq : (0 : ℝ) ≤ q₀ := Nat.cast_nonneg _
  have hy : ((q₀ : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt q₀ := by
    rw [← Real.rpow_mul_natCast hq]
    simp only [Nat.cast_ofNat]
    rw [show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
  have hD : (1 : ℝ) ≤ 8 ^ q₀.primeFactors.card := one_le_pow₀ (by norm_num)
  have hDD : (8 : ℝ) ^ q₀.primeFactors.card ≤ ((8 : ℝ) ^ q₀.primeFactors.card) ^ 2 := by
    nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  dsimp only [conductorMajorant]
  calc
    _ ≤ 64 * ((8 : ℝ) ^ q₀.primeFactors.card) ^ 2 * Real.sqrt q₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDD (by norm_num))
        (Real.sqrt_nonneg _)
    _ = _ := by rw [mul_pow, mul_pow, hy]; ring

/-- The last estimate of e:exceptionalarithmetic, uniform even over complex characters. -/
theorem conductorSigma_majorant_decay : ∃ C : ℝ, 0 < C ∧
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),
      conductorSigma q₀ χ₀ * Real.sqrt (conductorMajorant q₀) ≤
        C * (q₀ : ℝ) ^ (-(1 / 25 : ℝ)) := by
  obtain ⟨S, hS, hs⟩ := conductorSigma_uniform_bound (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨A, hA, ha⟩ := primeFactor_pow_le_rpow 8 (by norm_num) (1 / 16) (by norm_num)
  refine ⟨8 * S * A, by positivity, ?_⟩
  intro q₀ inst χ₀
  have hq : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  have hq1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast NeZero.pos q₀
  have hs' : conductorSigma q₀ χ₀ ≤ S * (q₀ : ℝ) ^ (-(3 / 8 : ℝ)) := by
    convert hs q₀ χ₀ using 1
    norm_num
  calc
    _ ≤ (S * (q₀ : ℝ) ^ (-(3 / 8 : ℝ))) *
        (8 * (8 : ℝ) ^ q₀.primeFactors.card * (q₀ : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul hs' (sqrt_conductorMajorant_le q₀ (NeZero.pos q₀))
        (Real.sqrt_nonneg _) (by positivity)
    _ ≤ (S * (q₀ : ℝ) ^ (-(3 / 8 : ℝ))) *
        (8 * (A * (q₀ : ℝ) ^ (1 / 16 : ℝ)) * (q₀ : ℝ) ^ (1 / 4 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ha q₀ (NeZero.pos q₀)) (by norm_num)) (by positivity))
        (by positivity)
    _ = (8 * S * A) * (q₀ : ℝ) ^ (-(1 / 16 : ℝ)) := by
      have he : (q₀ : ℝ) ^ (-(3 / 8 : ℝ)) * (q₀ : ℝ) ^ (1 / 16 : ℝ) *
          (q₀ : ℝ) ^ (1 / 4 : ℝ) = (q₀ : ℝ) ^ (-(1 / 16 : ℝ)) := by
        rw [← Real.rpow_add hq, ← Real.rpow_add hq]
        norm_num
      calc
        _ = (8 * S * A) * ((q₀ : ℝ) ^ (-(3 / 8 : ℝ)) *
            (q₀ : ℝ) ^ (1 / 16 : ℝ) * (q₀ : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)) (by positivity)

/-- The logarithmic consequence in Lemma 3.27, with a uniform absolute constant. -/
theorem conductorSigma_majorant_log_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀),
      (1 + Real.log q₀) * conductorSigma q₀ χ₀ * Real.sqrt (conductorMajorant q₀) ≤ C := by
  obtain ⟨C, hC, hc⟩ := conductorSigma_majorant_decay
  refine ⟨26 * C, by positivity, ?_⟩
  intro q₀ inst χ₀
  have hq : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
  have hq1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast NeZero.pos q₀
  have hlog : 1 + Real.log q₀ ≤ 26 * (q₀ : ℝ) ^ (1 / 25 : ℝ) := by
    have hl := Real.log_natCast_le_rpow_div q₀ (show (0 : ℝ) < 1 / 25 by norm_num)
    have hp : (1 : ℝ) ≤ (q₀ : ℝ) ^ (1 / 25 : ℝ) :=
      Real.one_le_rpow hq1 (by norm_num)
    linarith
  have hn : 0 ≤ conductorSigma q₀ χ₀ * Real.sqrt (conductorMajorant q₀) :=
    mul_nonneg (conductorSigma_nonneg _ _) (Real.sqrt_nonneg _)
  calc
    _ = (1 + Real.log q₀) * (conductorSigma q₀ χ₀ * Real.sqrt (conductorMajorant q₀)) := by ring
    _ ≤ (26 * (q₀ : ℝ) ^ (1 / 25 : ℝ)) * (C * (q₀ : ℝ) ^ (-(1 / 25 : ℝ))) :=
      mul_le_mul hlog (hc q₀ χ₀) hn (by positivity)
    _ = _ := by
      have he : (q₀ : ℝ) ^ (1 / 25 : ℝ) * (q₀ : ℝ) ^ (-(1 / 25 : ℝ)) = 1 := by
        rw [← Real.rpow_add hq, add_neg_cancel, Real.rpow_zero]
      calc
        _ = 26 * C * ((q₀ : ℝ) ^ (1 / 25 : ℝ) * (q₀ : ℝ) ^ (-(1 / 25 : ℝ))) := by ring
        _ = _ := by rw [he, mul_one]

end PrimeSquares
