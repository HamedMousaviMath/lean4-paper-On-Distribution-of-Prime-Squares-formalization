import PrimeSquares.GoldbachMasterSieveReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachExceptionalSet (F : Finset ℕ) : Finset ℕ := by
  classical
  exact F.filter (fun n => (goldbachGoodRepresentations n).card=0)

/-- A reduction from the paper's still-unproved internal sieve/main-term estimates,
not an assertion that those estimates are independent external facts. -/
theorem goldbach_exceptional_square_sum (H : PrimitiveTwoSquaresCriterion)
    {N : ℕ} (hN : 2≤N) {α : ℝ} (hα1 : 1<α) (hα2 : α<2)
    (F : Finset ℕ) (hF : ∀ n∈F,12<n ∧ n%24=12 ∧ n<N^2)
    (M a b E₁ E₂ : ℕ→ℝ) {t : ℝ} (ht : 0<t)
    (hlower : ∀ n∈F,a n*M n+E₁ n≤((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ))
    (hupper : ∀ n∈F,(goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)≤b n*M n+E₂ n)
    (hgap : ∀ n∈F,2*t≤(a n-b n)*M n)
    (hsmall : ∀ n∈F,2*((n-1).primeFactors.card:ℝ)≤t) :
    ((goldbachExceptionalSet F).card:ℝ)*t^2≤2*(∑ n∈F,(E₁ n)^2+∑ n∈F,(E₂ n)^2) := by
  classical
  have hpoint (n : ℕ) (hn : n∈goldbachExceptionalSet F) : t^2≤2*((E₁ n)^2+(E₂ n)^2) := by
    obtain ⟨hnF,hzero⟩ := mem_filter.mp hn
    obtain ⟨hnlarge,hnres,hnsize⟩ := hF n hnF
    have hm := goldbach_master_sieve_exact H hN hnlarge hnsize hnres hα1 hα2
    rw [hzero,zero_add] at hm
    have hmR : ((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ)≤
        (goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)+2*((n-1).primeFactors.card:ℝ) := by exact_mod_cast hm
    have hl := hlower n hnF
    have hu := hupper n hnF
    have hg := hgap n hnF
    have hs := hsmall n hnF
    have hd : t≤E₂ n-E₁ n := by nlinarith only [hmR,hl,hu,hg,hs]
    have hsq := pow_le_pow_left₀ ht.le hd 2
    nlinarith only [hsq,sq_nonneg (E₂ n+E₁ n)]
  calc
    _=∑ _n∈goldbachExceptionalSet F,t^2 := by rw [sum_const,nsmul_eq_mul]
    _≤∑ n∈goldbachExceptionalSet F,2*((E₁ n)^2+(E₂ n)^2) := sum_le_sum hpoint
    _≤∑ n∈F,2*((E₁ n)^2+(E₂ n)^2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _=_ := by rw [←mul_sum,sum_add_distrib]

theorem goldbach_exceptional_count (H : PrimitiveTwoSquaresCriterion)
    {N : ℕ} (hN : 2≤N) {α : ℝ} (hα1 : 1<α) (hα2 : α<2)
    (F : Finset ℕ) (hF : ∀ n∈F,12<n ∧ n%24=12 ∧ n<N^2)
    (M a b E₁ E₂ : ℕ→ℝ) {t : ℝ} (ht : 0<t)
    (hlower : ∀ n∈F,a n*M n+E₁ n≤((goldbachSiftedValues n ((N:ℝ)^(1/α))).card:ℝ))
    (hupper : ∀ n∈F,(goldbachUpperSieveSum n N ((N:ℝ)^(1/α)):ℝ)≤b n*M n+E₂ n)
    (hgap : ∀ n∈F,2*t≤(a n-b n)*M n)
    (hsmall : ∀ n∈F,2*((n-1).primeFactors.card:ℝ)≤t) :
    ((goldbachExceptionalSet F).card:ℝ)≤2*(∑ n∈F,(E₁ n)^2+∑ n∈F,(E₂ n)^2)/t^2 := by
  exact (le_div_iff₀ (sq_pos_of_pos ht)).mpr
    (goldbach_exceptional_square_sum H hN hα1 hα2 F hF M a b E₁ E₂ ht hlower hupper hgap hsmall)

end PrimeSquares
