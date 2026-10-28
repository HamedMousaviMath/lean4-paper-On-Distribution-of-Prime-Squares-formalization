import PrimeSquares.PrimeCutoffEnumeration
import PrimeSquares.ErgodicSquareAverages

set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
namespace PrimeSquares

noncomputable def enumeratedPrimeSquareAverage {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (m : ℕ) (f : X → ℂ) (x : X) : ℂ :=
  (((m : ℝ)⁻¹) : ℂ)*∑ k ∈ Finset.range m, f (T^[(Nat.nth Nat.Prime k)^2] x)

noncomputable def enumeratedPrimeMaximalENorm {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ k : ℕ, ‖enumeratedPrimeSquareAverage T (k+1) f x‖ₑ

noncomputable def enumeratedPrimeMaximalValue {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (f : X → ℂ) (x : X) : ℝ := (enumeratedPrimeMaximalENorm T f x).toReal

theorem ergodic_prime_cutoff_enumerated {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (n : ℕ) (f : X → ℂ) (x : X) :
    ergodicPositiveAverage primePositiveFamily T n f x =
      enumeratedPrimeSquareAverage T (Nat.primeCounting (n+2)) f x := by
  rw [ergodicPositiveAverage_square primePositiveFamily (Or.inr (Or.inr rfl))]
  simp only [primePositiveFamily, enumeratedPrimeSquareAverage, Complex.ofReal_inv]
  rw [←Finset.mul_sum, sum_primesLE_nth]

theorem enumeratedPrimeSquareAverage_cutoff {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (k : ℕ) (f : X → ℂ) (x : X) :
    enumeratedPrimeSquareAverage T (k+1) f x =
      ergodicPositiveAverage primePositiveFamily T (Nat.nth Nat.Prime k-2) f x := by
  have hN : 2 ≤ Nat.nth Nat.Prime k := by have h := Nat.add_two_le_nth_prime k; omega
  have h := ergodic_prime_cutoff_enumerated T (Nat.nth Nat.Prime k-2) f x
  rw [Nat.sub_add_cancel hN, primeCounting_nth_prime] at h
  exact h.symm

theorem enumeratedPrimeMaximalENorm_eq {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (f : X → ℂ) (x : X) :
    enumeratedPrimeMaximalENorm T f x = ergodicMaximalENorm primePositiveFamily T f x := by
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [enumeratedPrimeSquareAverage_cutoff]
    exact ergodicMaximalENorm_dominates primePositiveFamily T f _ x
  · apply iSup_le
    intro n
    rw [ergodic_prime_cutoff_enumerated]
    have hcount := primeCutoff_count_pos (by omega : 2 ≤ n+2)
    have he : Nat.primeCounting (n+2)-1+1 = Nat.primeCounting (n+2) := by omega
    have h := le_iSup (fun k : ℕ => ‖enumeratedPrimeSquareAverage T (k+1) f x‖ₑ)
      (Nat.primeCounting (n+2)-1)
    simpa only [he, enumeratedPrimeMaximalENorm] using h

theorem enumeratedPrimeMaximalValue_eq {X : Type*} [MeasurableSpace X]
    (T : X ≃ᵐ X) (f : X → ℂ) :
    enumeratedPrimeMaximalValue T f = ergodicMaximalValue primePositiveFamily T f := by
  funext x
  simp only [enumeratedPrimeMaximalValue, ergodicMaximalValue, enumeratedPrimeMaximalENorm_eq]

end PrimeSquares
