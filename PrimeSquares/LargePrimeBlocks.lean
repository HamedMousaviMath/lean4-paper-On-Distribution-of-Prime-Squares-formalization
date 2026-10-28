import PrimeSquares.UnitSquareDensityProducts
import Mathlib.Data.Nat.Pairing

set_option autoImplicit false
open Finset
namespace PrimeSquares

def badnessPrimeThreshold (n : ℕ) : ℕ := (64*(n+1)*3^(n+1))^2

def badnessPrimeIndex (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n+1), (badnessPrimeThreshold k+1)

noncomputable def badnessAuxPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (badnessPrimeIndex n)

theorem badnessPrimeIndex_strictMono : StrictMono badnessPrimeIndex := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold badnessPrimeIndex
  rw [Finset.sum_range_succ (fun k => badnessPrimeThreshold k+1) (n+1)]
  omega

theorem badnessPrimeIndex_dominates {j n : ℕ} (hj : j ≤ n) :
    badnessPrimeThreshold j+1 ≤ badnessPrimeIndex n := by
  apply Finset.single_le_sum (f:=fun k => badnessPrimeThreshold k+1)
    (fun _ _ => Nat.zero_le _)
  exact Finset.mem_range.mpr (by omega)

theorem badnessAuxPrime_prime (n : ℕ) : (badnessAuxPrime n).Prime :=
  Nat.prime_nth_prime (badnessPrimeIndex n)

theorem badnessAuxPrime_strictMono : StrictMono badnessAuxPrime :=
  (Nat.nth_strictMono Nat.infinite_setOfPred_prime).comp badnessPrimeIndex_strictMono

theorem badnessAuxPrime_threshold {j n : ℕ} (hj : j ≤ n) :
    badnessPrimeThreshold j < badnessAuxPrime n := by
  have hindex := badnessPrimeIndex_dominates hj
  have hprime := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le (badnessPrimeIndex n)
  change badnessPrimeThreshold j < Nat.nth Nat.Prime (badnessPrimeIndex n)
  exact (Nat.lt_of_succ_le hindex).trans_le hprime

theorem badnessAuxPrime_gt_two (n : ℕ) : 2 < badnessAuxPrime n := by
  have h := badnessAuxPrime_threshold (j:=0) (n:=n) (Nat.zero_le n)
  norm_num [badnessPrimeThreshold] at h
  omega

theorem badnessAuxPrime_odd (n : ℕ) : Odd (badnessAuxPrime n) :=
  (badnessAuxPrime_prime n).odd_of_ne_two (by have := badnessAuxPrime_gt_two n; omega)

noncomputable def badnessAuxU (j : ℕ) : ℕ := badnessAuxPrime (2*j)

noncomputable def badnessPrimeBlock (j : ℕ) : Finset ℕ :=
  (Finset.range (j+1)).image (fun k => badnessAuxPrime (2*Nat.pair j k+1))

noncomputable def badnessBlockModulus (j : ℕ) : ℕ := ∏ p ∈ badnessPrimeBlock j, p

theorem badnessPrimeBlock_card (j : ℕ) : (badnessPrimeBlock j).card=j+1 := by
  unfold badnessPrimeBlock
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro k l h
  have hi := badnessAuxPrime_strictMono.injective h
  have hp : Nat.pair j k=Nat.pair j l := by omega
  have he : (j,k)=(j,l) := Nat.pairEquiv.injective hp
  exact congrArg Prod.snd he

theorem badnessPrimeBlock_prime (j : ℕ) (p : ℕ) (hp : p ∈ badnessPrimeBlock j) :
    p.Prime ∧ p ≠ 2 := by
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
  exact ⟨badnessAuxPrime_prime _, by have := badnessAuxPrime_gt_two (2*Nat.pair j k+1); omega⟩

theorem badnessPrimeBlock_threshold (j : ℕ) (p : ℕ) (hp : p ∈ badnessPrimeBlock j) :
    badnessPrimeThreshold j < p := by
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
  apply badnessAuxPrime_threshold
  have := Nat.left_le_pair j k
  omega

theorem badnessBlockModulus_pos (j : ℕ) : 0 < badnessBlockModulus j :=
  Finset.prod_pos (fun p hp => (badnessPrimeBlock_prime j p hp).1.pos)

end PrimeSquares
