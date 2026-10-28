import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Elementary arithmetic supporting the local progression and Lemma 11.2. -/

namespace PrimeSquares

theorem square_mod24 (n : ℕ) (h₂ : n % 2 = 1) (h₃ : n % 3 ≠ 0) :
    n ^ 2 % 24 = 1 := by
  have hsmall : n % 24 < 24 := Nat.mod_lt n (by decide)
  have h₂' : (n % 24) % 2 = 1 := by omega
  have h₃' : (n % 24) % 3 ≠ 0 := by omega
  rw [Nat.pow_mod]
  interval_cases h : n % 24 <;> simp_all

theorem prime_square_mod24 (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    p ^ 2 % 24 = 1 := by
  have h₂ : p % 2 ≠ 0 := by
    intro h
    have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  have h₃ : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  apply square_mod24 p _ h₃
  omega

/-- The representation in the abstract and the shifted representation in
Theorem 1.6 are exactly equivalent. Natural subtraction is avoided. -/
theorem shifted_representation (m a b p : ℕ) :
    m = a ^ 2 + b ^ 2 + p ^ 2 ↔
      m + 1 = a ^ 2 + b ^ 2 + p ^ 2 + 1 := by omega

theorem shifted_progression (m : ℕ) :
    m % 24 = 11 ↔ (m + 1) % 24 = 12 := by omega

theorem prime_square_sum_progression (r p : ℕ)
    (hr : r % 24 = 11) (hp : p.Prime) (hp3 : 3 < p) :
    (r + p ^ 2) % 24 = 12 := by
  have hs := prime_square_mod24 p hp hp3
  omega

/-- The key finite observation behind the exceptional terms in Lemma 11.2:
if the same prime divides n and r, and n = m²+r with m prime, then m is that prime. -/
theorem shared_prime_forces_square_prime (p m n r : ℕ)
    (hp : p.Prime) (hm : m.Prime)
    (heq : n = m ^ 2 + r) (hpn : p ∣ n) (hpr : p ∣ r) :
    m = p := by
  have hsum : p ∣ m ^ 2 + r := by simpa [heq] using hpn
  have hsq : p ∣ m ^ 2 := (Nat.dvd_add_iff_left hpr).mpr hsum
  have hpm : p ∣ m := hp.dvd_of_dvd_pow hsq
  rcases (Nat.dvd_prime hm).mp hpm with h | h
  · have := hp.two_le
    omega
  · exact h.symm

end PrimeSquares
