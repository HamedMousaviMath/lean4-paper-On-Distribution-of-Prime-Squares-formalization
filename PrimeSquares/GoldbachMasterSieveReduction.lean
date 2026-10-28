import PrimeSquares.GoldbachUpperSieveInclusion

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachUpperSieveSum (n N : ℕ) (z : ℝ) : ℕ :=
  ∑ ℓ∈goldbachClosedLn n N z,(goldbachUpperSifted n N ℓ).card

theorem goldbach_upper_reduction_exact {N n : ℕ} (hN : 2≤N) (hn : 12<n)
    (hsize : n<N^2) (hres : n%24=12) {α : ℝ} (hα1 : 1<α) (hα2 : α<2) :
    (goldbachTruncatedBadValues n ((N:ℝ)^(1/α))).card≤
      goldbachUpperSieveSum n N ((N:ℝ)^(1/α))+(n-1).primeFactors.card := by
  classical
  rw [goldbachTruncatedBadValues_card]
  have hh := card_le_card (goldbach_upper_sifted_inclusion hN hn hsize hres hα1 hα2)
  exact hh.trans ((card_union_le _ _).trans
    (add_le_add card_biUnion_le (goldbachDivisorExceptions_card n)))

theorem goldbach_upper_reduction {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N → 12<n → n%24=12 → n<N^2 →
      ∀ α : ℝ,1<α → α<2 →
        ((goldbachTruncatedBadValues n ((N:ℝ)^(1/α))).card:ℝ)≤
          (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)+K*(N:ℝ)^ε := by
  obtain ⟨K,hK,herr⟩ := goldbach_prime_divisor_power_error hε
  refine ⟨K,hK,?_⟩
  intro N n hN hn hres hsize α hα1 hα2
  have hcard : ((goldbachTruncatedBadValues n ((N:ℝ)^(1/α))).card:ℝ)≤
      (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)+((n-1).primeFactors.card:ℝ) := by
    exact_mod_cast goldbach_upper_reduction_exact hN hn hsize hres hα1 hα2
  exact hcard.trans (add_le_add le_rfl (herr N n (by omega) (by omega) (by omega)))

theorem goldbach_master_sieve_exact (H : PrimitiveTwoSquaresCriterion)
    {N n : ℕ} (hN : 2≤N) (hn : 12<n) (hsize : n<N^2) (hres : n%24=12)
    {α : ℝ} (hα1 : 1<α) (hα2 : α<2) :
    (goldbachSiftedValues n ((N:ℝ)^(1/α))).card≤
      (goldbachGoodRepresentations n).card+goldbachUpperSieveSum n N ((N:ℝ)^(1/α))+
        2*(n-1).primeFactors.card := by
  obtain ⟨hz,hlarge⟩ := goldbach_truncation_scale hN hα1 hα2
  obtain ⟨e,he,hcount⟩ := goldbach_truncation_exact_error H hn hres (Nat.le_of_lt hsize) hz hlarge
  have hu := goldbach_upper_reduction_exact hN hn hsize hres hα1 hα2
  omega

/-- Complete master reduction for the proposed closed-cutoff source convention. -/
theorem goldbach_master_sieve_reduction (H : PrimitiveTwoSquaresCriterion) {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N → 12<n → n%24=12 → n<N^2 →
      ∀ α : ℝ,1<α → α<2 →
        ((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ)-
          (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)-K*(N:ℝ)^ε≤
            ((goldbachGoodRepresentations n).card:ℝ) := by
  obtain ⟨K,hK,herr⟩ := goldbach_prime_divisor_power_error hε
  refine ⟨2*K,by positivity,?_⟩
  intro N n hN hn hres hsize α hα1 hα2
  have hcard : ((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ)≤
      ((goldbachGoodRepresentations n).card:ℝ)+(goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)+
        2*((n-1).primeFactors.card:ℝ) := by
    exact_mod_cast goldbach_master_sieve_exact H hN hn hsize hres hα1 hα2
  have he := herr N n (by omega) (by omega) (by omega)
  nlinarith only [hcard,he]

end PrimeSquares
