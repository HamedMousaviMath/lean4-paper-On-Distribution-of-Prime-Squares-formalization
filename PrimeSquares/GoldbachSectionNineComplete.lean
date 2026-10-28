import PrimeSquares.GoldbachPrimitiveCriterion
import PrimeSquares.GoldbachFixedSmoothSeed
import PrimeSquares.GoldbachGeneralWeightedIntegral
import PrimeSquares.GoldbachHeadlineTheorem

set_option autoImplicit false
open Finset Filter
namespace PrimeSquares

/-- Section9's first source lemma without the former arithmetic hypothesis. -/
theorem goldbach_from_sifted_to_primes_complete {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,1≤N→2≤n→n≤N^2→
      ((goldbachSiftedValues n ((N:ℝ)^2)).card:ℝ)-K*(N:ℝ)^ε≤
        ((goldbachGoodRepresentations n).card:ℝ) :=
  goldbach_from_full_sifted goldbach_primitive_two_squares_criterion hε

/-- The full truncation identity, including repeated bad prime factors. -/
theorem goldbach_truncation_complete {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N→12<n→n%24=12→n≤N^2→
      ∀ α : ℝ,1<α→α<2→∃ e : ℕ,(e:ℝ)≤K*(N:ℝ)^ε ∧
        (goldbachSiftedValues n ((N:ℝ)^(1/α))).card=
          (goldbachGoodRepresentations n).card+
          (goldbachTruncatedBadValues n ((N:ℝ)^(1/α))).card+e :=
  goldbach_truncationT goldbach_primitive_two_squares_criterion hε

theorem goldbach_section9_master_exact {N n : ℕ} (hN : 2≤N) (hn : 12<n)
    (hsize : n<N^2) (hres : n%24=12) {α : ℝ} (hα1 : 1<α) (hα2 : α<2) :
    (goldbachSiftedValues n ((N:ℝ)^(1/α))).card≤
      (goldbachGoodRepresentations n).card+goldbachUpperSieveSum n N ((N:ℝ)^(1/α))+
        2*(n-1).primeFactors.card :=
  goldbach_master_sieve_exact goldbach_primitive_two_squares_criterion hN hn hsize hres hα1 hα2

theorem goldbach_master_sieve_complete {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ N n : ℕ,2≤N→12<n→n%24=12→n<N^2→
      ∀ α : ℝ,1<α→α<2→
        ((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ)-
          (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)-K*(N:ℝ)^ε≤
            ((goldbachGoodRepresentations n).card:ℝ) :=
  goldbach_master_sieve_reduction goldbach_primitive_two_squares_criterion hε

/-- The headline bound now needs neither a primitive-two-square assumption
nor a supplied test function. Only the explicit independent analytic inputs remain. -/
theorem goldbach_section9_headline_complete (H : GoldbachSection11Inputs) (A : ℝ) (hA : 0<A) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ X : ℝ in atTop,
      ((goldbachSourceExceptionalSet X).card:ℝ)≤D*X*(Real.log X)^(-A) := by
  exact goldbach_headline_theorem H goldbach_primitive_two_squares_criterion
    goldbachFixedSmoothSeed goldbach_fixed_smooth_seed_nonzero goldbach_fixed_smooth_seed_support A hA

theorem goldbach_section9_exceptional_density_zero (H : GoldbachSection11Inputs) :
    Tendsto (fun X : ℝ=>((goldbachSourceExceptionalSet X).card:ℝ)/X) atTop (nhds 0) := by
  obtain ⟨D,_,hBound⟩ := goldbach_section9_headline_complete H 1 (by norm_num)
  have hlim : Tendsto (fun X : ℝ=>D/Real.log X) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (2:ℝ)] with X hX
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  · filter_upwards [hBound,eventually_gt_atTop (2:ℝ)] with X hB hX
    have hX0 : 0<X := by linarith
    calc
      _≤(D*X*(Real.log X)^(-(1:ℝ)))/X := div_le_div_of_nonneg_right hB hX0.le
      _=D/Real.log X := by rw [Real.rpow_neg_one];field_simp

end PrimeSquares
