import PrimeSquares.InitialPositiveDistribution

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- The source Chebyshev/union deduction, with the actual full maximum.
The large-scale envelope hypotheses are internal premises of this reusable
lemma. No source-specific high-low existence theorem is an external input. -/
theorem highLow_restricted_distribution (A : PositiveAverageFamily) (F : Finset ℤ) (J : ℕ)
    (g h : ℤ → ℝ) (hg : ∀ x,0≤g x) (hh : ∀ x,0≤h x)
    {p Blo Bhi : ℝ} (hp : 0<p) (hlo : FinitePowerBudget g p Blo)
    (hhi : FinitePowerBudget h 2 Bhi)
    (hlarge : ∀ n : ℕ,J≤n → ∀ x,‖positiveAverage A n (finiteIndicator F) x‖≤g x+h x)
    {t : ℝ} (ht : 0<t) :
    TestedDistributionBound (positiveMaximal A (finiteIndicator F)) (1/t)
      (t*(J : ℝ)*A.mass*F.card+(2*t)^p*Blo+4*t^2*Bhi) := by
  classical
  intro D
  have hsplit : finiteDistribution D (positiveMaximal A (finiteIndicator F)) (1/t)≤
      finiteDistribution D (initialPositiveSum A J F) (1/t)+
        finiteDistribution D g (1/(2*t))+finiteDistribution D h (1/(2*t)) := by
    have hsub : D.filter (fun x => 1/t<positiveMaximal A (finiteIndicator F) x) ⊆
        (D.filter (fun x => 1/t< initialPositiveSum A J F x)) ∪
        (D.filter (fun x => 1/(2*t)<g x)) ∪ (D.filter (fun x => 1/(2*t)<h x)) := by
      intro x hx
      obtain ⟨hx,htop⟩ := mem_filter.mp hx
      have hn : ∃ n : ℕ,1/t<‖positiveAverage A n (finiteIndicator F) x‖ := by
        by_contra hn
        push Not at hn
        have hs : positiveMaximal A (finiteIndicator F) x≤1/t := ciSup_le hn
        exact (not_lt_of_ge hs) htop
      obtain ⟨n,hn⟩ := hn
      by_cases hnJ : n<J
      · exact mem_union_left _ (mem_union_left _
          (mem_filter.mpr ⟨hx,hn.trans_le (initialPositiveSum_dominates A hnJ F x)⟩))
      · have hnJ' : J≤n := Nat.le_of_not_gt hnJ
        by_cases hgl : 1/(2*t)<g x
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx,hgl⟩))
        · apply mem_union_right
          apply mem_filter.mpr
          refine ⟨hx,?_⟩
          have he : 1/(2*t)+1/(2*t)=1/t := by ring
          have hl := hlarge n hnJ' x
          nlinarith
    have hc := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    unfold finiteDistribution
    exact_mod_cast hc
  have hsmall := initialPositiveSum_distribution A J F D ht
  have hlo' := finiteDistribution_real_power hg (show 0<1/(2*t) by positivity) hp hlo D
  have hhi' := finiteDistribution_real_power hh (show 0<1/(2*t) by positivity)
    (by norm_num : (0 : ℝ)<2) hhi D
  have heq : Blo/(1/(2*t))^p=(2*t)^p*Blo := by
    rw [one_div,Real.inv_rpow (show 0≤2*t by positivity),div_inv_eq_mul,mul_comm]
  rw [heq] at hlo'
  have heq2 : Bhi/(1/(2*t))^(2 : ℝ)=4*t^2*Bhi := by
    rw [Real.rpow_two]
    field_simp
    norm_num
  rw [heq2] at hhi'
  linarith

theorem highLow_restricted_levelset_finite (A : PositiveAverageFamily) (F : Finset ℤ) (J : ℕ)
    (g h : ℤ → ℝ) (hg : ∀ x,0≤g x) (hh : ∀ x,0≤h x)
    {p Blo Bhi : ℝ} (hp : 0<p) (hlo : FinitePowerBudget g p Blo)
    (hhi : FinitePowerBudget h 2 Bhi)
    (hlarge : ∀ n : ℕ,J≤n → ∀ x,‖positiveAverage A n (finiteIndicator F) x‖≤g x+h x)
    {t : ℝ} (ht : 0<t) :
    {x | 1/t<positiveMaximal A (finiteIndicator F) x}.Finite :=
  testedDistribution_finite (highLow_restricted_distribution A F J g h hg hh hp hlo hhi hlarge ht)

end PrimeSquares
