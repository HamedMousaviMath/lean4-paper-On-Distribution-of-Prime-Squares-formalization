import PrimeSquares.DenominatorActivation
namespace PrimeSquares
theorem individual_denominator_tail (R : ℕ → ℝ) (hR : Monotone R) (q : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hi : denominatorActivation (R i) q=1) : denominatorActivation (R j) q=1 := by
  have hq : (q : ℝ) ≤ R i := by
    by_contra hn
    simp only [denominatorActivation,ite_eq_right hn] at hi
    norm_num at hi
  exact ite_eq_left (hq.trans (hR hij))
end PrimeSquares
