import PrimeSquares.CohenSeries
import PrimeSquares.ElementaryPrimeProduct

/-!
# Lemma 3.20: the uniform logarithmic bound

The absolute constant below is explicit but not optimized. Its proof uses
only the checked Cohen factors and the elementary finite prime-product bound;
no Mertens theorem or deep analytic input is assumed.
-/

open Finset

namespace PrimeSquares

noncomputable def cohenLogConstant : ℝ := 5 * Real.exp 2 * (12 + 2 / Real.log 3)

theorem cohenLogConstant_pos : 0 < cohenLogConstant := by
  have h3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  unfold cohenLogConstant
  positivity

/-- Integer cutoffs satisfy a slightly stronger explicit-constant estimate. -/
theorem low_ramanujan_bound_integer (Q : ℕ) (hQ : 3 ≤ Q) (n : ℤ) :
    smoothCohenSeries Q n ≤ (cohenLogConstant / 2) * Real.log Q := by
  have hs : ∀ p ∈ oddPrimesBelow Q, p.Prime ∧ p ≤ Q := by
    intro p hp
    obtain ⟨hpQ, hp', _⟩ := mem_filter.mp hp
    exact ⟨hp', (mem_range.mp hpQ).le⟩
  calc
    _ ≤ (5 / 2 : ℝ) * ∏ p ∈ oddPrimesBelow Q,
        (1 + ((p : ℝ) + 1) / ((p : ℝ) * ((p : ℝ) - 1))) :=
      smoothCohenSeries_le_prime_product Q n hQ
    _ ≤ (5 / 2 : ℝ) * (Real.exp 2 * (12 + 2 / Real.log 3) * Real.log Q) :=
      mul_le_mul_of_nonneg_left (cohen_prime_product_le_log _ Q hQ hs) (by norm_num)
    _ = _ := by unfold cohenLogConstant; ring

/-- Lemma 3.20 for every real Q>=3, every integer n and the exact strict cutoff. -/
theorem low_ramanujan_bound (Q : ℝ) (hQ : 3 ≤ Q) (n : ℤ) :
    (∑' q : ℕ, if ∀ p ∈ q.primeFactors, (p : ℝ) < Q then cohenWeight q n else 0) ≤
      cohenLogConstant * Real.log Q := by
  have hc : 3 ≤ Nat.ceil Q := by
    exact_mod_cast hQ.trans (Nat.le_ceil Q)
  have hceil : (Nat.ceil Q : ℝ) ≤ Q ^ 2 := by
    have he := Nat.ceil_lt_add_one (by linarith : 0 ≤ Q)
    nlinarith
  have hlog : Real.log (Nat.ceil Q : ℝ) ≤ 2 * Real.log Q := by
    calc
      _ ≤ Real.log (Q ^ 2) :=
        Real.log_le_log (by exact_mod_cast (show 0 < Nat.ceil Q by omega)) hceil
      _ = _ := by rw [Real.log_pow]; norm_num
  calc
    _ = smoothCohenSeries (Nat.ceil Q) n := by
      simp only [smoothCohenSeries, Nat.lt_ceil]
    _ ≤ (cohenLogConstant / 2) * Real.log (Nat.ceil Q) :=
      low_ramanujan_bound_integer _ hc n
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_left hlog
        (div_nonneg cohenLogConstant_pos.le (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith

/-- The implied constant is absolute and simultaneous for all n and Q. -/
theorem low_ramanujan_uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ n : ℤ,
    (∑' q : ℕ, if ∀ p ∈ q.primeFactors, (p : ℝ) < Q then cohenWeight q n else 0) ≤
      C * Real.log Q := by
  exact ⟨cohenLogConstant, cohenLogConstant_pos, fun Q hQ n => low_ramanujan_bound Q hQ n⟩

end PrimeSquares
