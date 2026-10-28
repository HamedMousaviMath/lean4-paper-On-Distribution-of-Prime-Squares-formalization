import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Nth

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem primeCounting_nth_prime (k : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime k) = k+1 :=
  Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime k

theorem primeCutoff_count_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Nat.primeCounting N := by
  by_contra h
  have he : Nat.primeCounting N = 0 := by omega
  have hn := Nat.primeCounting_eq_zero_iff.mp he
  omega

theorem primesLE_image_nth (N : ℕ) :
    Nat.primesLE N = (Finset.range (Nat.primeCounting N)).image (Nat.nth Nat.Prime) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpN, hprime⟩ := Nat.mem_primesLE.mp hp
    apply Finset.mem_image.mpr
    refine ⟨Nat.count Nat.Prime p, Finset.mem_range.mpr ?_, Nat.nth_count hprime⟩
    exact Nat.count_strict_mono hprime (by omega : p < N+1)
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hlt := Nat.nth_lt_of_lt_count (Finset.mem_range.mp hk)
    exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_nth_prime k⟩

theorem sum_primesLE_nth {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → E) :
    (∑ p ∈ Nat.primesLE N, f p) = ∑ k ∈ Finset.range (Nat.primeCounting N), f (Nat.nth Nat.Prime k) := by
  rw [primesLE_image_nth]
  exact Finset.sum_image (fun i _ j _ hij => (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hij)

end PrimeSquares
