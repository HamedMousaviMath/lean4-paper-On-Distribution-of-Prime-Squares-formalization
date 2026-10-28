import PrimeSquares.PrimeLargeStoppingPairing

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def physicalAnnularPrimeValue (N : ℕ) (F : Finset ℤ) (x : ℤ) : ℂ :=
  indicatorConvolution (annularWeightedSquareAverageKernel N ArithmeticFunction.vonMangoldt) F x

theorem physicalAnnularPrimeValue_one (F : Finset ℤ) (x : ℤ) :
    physicalAnnularPrimeValue 1 F x=0 := by
  have h := annularMangoldt_indicator_domination 1 F x
  simp only [Nat.cast_one,Real.log_one,zero_mul] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem physicalAnnularPrimeValue_empty (N : ℕ) (x : ℤ) :
    physicalAnnularPrimeValue N ∅ x=0 := indicatorConvolution_empty _ x

theorem physicalDyadic_above_one {N : ℕ} (hN : 2 ≤ N) (hd : ∃ j : ℕ,N=2^j) :
    (2:ℕ)^(Nat.log2 N-1)*2=N := by
  obtain ⟨j,rfl⟩ := hd
  have hj : 1 ≤ j := by
    by_contra hh
    have hj0 : j=0 := by omega
    simp only [hj0,pow_zero] at hN
    omega
  rw [Nat.log2_two_pow,←pow_succ,Nat.sub_add_cancel hj]

theorem physicalDyadic_prime_pairing (F G : Finset ℤ) (τ : ℤ → ℕ)
    (hτ : ∀ x ∈ G,∃ j : ℕ,τ x=2^j) :
    (∑ x ∈ G,physicalAnnularPrimeValue (τ x) F x)=
      ∑ x ∈ G.filter (fun x => 2 ≤ τ x),annularDyadicValue (Nat.log2 (τ x)-1) F x := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with hh
  · unfold physicalAnnularPrimeValue annularDyadicValue
    rw [physicalDyadic_above_one hh (hτ x hx)]
  · have hN1 : τ x=1 := by
      obtain ⟨j,hj⟩ := hτ x hx
      have hp : 1 ≤ τ x := hj ▸ one_le_pow₀ (by norm_num : 1≤(2:ℕ))
      omega
    rw [hN1,physicalAnnularPrimeValue_one]

end PrimeSquares
