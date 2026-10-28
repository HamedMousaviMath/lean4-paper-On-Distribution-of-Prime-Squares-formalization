import PrimeSquares.HighLowOperators
import Mathlib.Data.Set.Card
import Mathlib.Tactic.GCongr

open Finset
open scoped lp
namespace PrimeSquares

noncomputable def finiteDistribution (D : Finset ℤ) (g : ℤ → ℝ) (a : ℝ) : ℝ :=
  ((D.filter (fun x => a<g x)).card : ℝ)

/-- Finite testing is equivalent to the actual level-set cardinal bound;
in particular it does not silently assign cardinality zero to infinite sets. -/
def TestedDistributionBound (g : ℤ → ℝ) (a B : ℝ) : Prop :=
  ∀ D : Finset ℤ, finiteDistribution D g a ≤ B

theorem finiteDistribution_nonneg (D : Finset ℤ) (g : ℤ → ℝ) (a : ℝ) :
    0≤finiteDistribution D g a := Nat.cast_nonneg _

theorem testedDistribution_finite {g : ℤ → ℝ} {a B : ℝ} (h : TestedDistributionBound g a B) :
    {x | a<g x}.Finite := by
  classical
  by_contra hn
  obtain ⟨k,hk⟩ := exists_nat_gt B
  obtain ⟨S,hS,hfin,hcard⟩ := Set.Infinite.exists_subset_ncard_eq hn k
  have he : hfin.toFinset.filter (fun x => a<g x)=hfin.toFinset := by
    ext x
    simp only [mem_filter,Set.Finite.mem_toFinset,and_iff_left_iff_imp]
    exact fun hx => hS hx
  have ht := h hfin.toFinset
  rw [finiteDistribution,he,←Set.ncard_eq_toFinset_card S hfin,hcard] at ht
  linarith

theorem testedDistribution_ncard {g : ℤ → ℝ} {a B : ℝ} (h : TestedDistributionBound g a B) :
    ({x | a<g x}.ncard : ℝ)≤B := by
  classical
  have hs := testedDistribution_finite h
  have he : hs.toFinset.filter (fun x => a<g x)=hs.toFinset := by ext x;simp
  have ht := h hs.toFinset
  simpa only [finiteDistribution,he,←Set.ncard_eq_toFinset_card _ hs] using ht

theorem testedDistribution_iff {g : ℤ → ℝ} {a B : ℝ} :
    TestedDistributionBound g a B ↔ {x | a<g x}.Finite ∧ ({x | a<g x}.ncard : ℝ)≤B := by
  classical
  constructor
  · exact fun h => ⟨testedDistribution_finite h,testedDistribution_ncard h⟩
  · rintro ⟨hs,hc⟩ D
    have hsub : D.filter (fun x => a<g x) ⊆ hs.toFinset := by
      intro x hx
      rw [Set.Finite.mem_toFinset]
      exact (mem_filter.mp hx).2
    exact (show finiteDistribution D g a ≤ (hs.toFinset.card : ℝ) by
      unfold finiteDistribution
      exact_mod_cast card_le_card hsub).trans
      (by simpa only [←Set.ncard_eq_toFinset_card _ hs] using hc)

theorem finiteDistribution_chebyshev (D : Finset ℤ) (f : ℤ → ℂ) {a p : ℝ}
    (ha : 0<a) (hp : 0<p) :
    a^p*finiteDistribution D (fun x => ‖f x‖) a ≤ ∑ x ∈ D,‖f x‖^p := by
  classical
  calc
    _ = ∑ _x ∈ D.filter (fun x => a<‖f x‖),a^p := by
      rw [sum_const,nsmul_eq_mul]
      unfold finiteDistribution
      ring
    _ ≤ ∑ x ∈ D.filter (fun x => a<‖f x‖),‖f x‖^p := by
      apply sum_le_sum
      intro x hx
      exact Real.rpow_le_rpow ha.le (mem_filter.mp hx).2.le hp.le
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun x _ _ => Real.rpow_nonneg (norm_nonneg _) p)

theorem finiteDistribution_lp {P : ENNReal} (hp : 0<P.toReal)
    (f : lp (fun _ : ℤ => ℂ) P) {a : ℝ} (ha : 0<a) (D : Finset ℤ) :
    finiteDistribution D (fun x => ‖f x‖) a ≤ ‖f‖^P.toReal/a^P.toReal := by
  have h := (finiteDistribution_chebyshev D f ha hp).trans (lp.sum_rpow_le_norm_rpow hp f D)
  exact (le_div_iff₀ (Real.rpow_pos_of_pos ha _)).mpr (by simpa only [mul_comm] using h)

theorem finiteDistribution_mono (D : Finset ℤ) {f g : ℤ → ℝ} {a b : ℝ}
    (hfg : ∀ x∈D,f x≤g x) (hab : b≤a) :
    finiteDistribution D f a ≤ finiteDistribution D g b := by
  classical
  apply Nat.cast_le.mpr
  apply card_le_card
  intro x hx
  obtain ⟨hx,h⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hx,hab.trans_lt (h.trans_le (hfg x hx))⟩

theorem finiteDistribution_two (D : Finset ℤ) {f g h : ℤ → ℝ} {a b : ℝ}
    (hfg : ∀ x∈D,f x≤g x+h x) :
    finiteDistribution D f (a+b) ≤ finiteDistribution D g a+finiteDistribution D h b := by
  classical
  have hsub : D.filter (fun x => a+b<f x) ⊆
      (D.filter (fun x => a<g x)) ∪ (D.filter (fun x => b<h x)) := by
    intro x hx
    obtain ⟨hx,ht⟩ := mem_filter.mp hx
    by_cases hg : a<g x
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hg⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,by have := hfg x hx;nlinarith⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  unfold finiteDistribution
  exact_mod_cast hc

theorem finiteDistribution_finite_sum (D : Finset ℤ) (I : Finset ℕ)
    (g : ℕ → ℤ → ℝ) (a : ℕ → ℝ) :
    finiteDistribution D (fun x => ∑ j ∈ I,g j x) (∑ j ∈ I,a j) ≤
      ∑ j ∈ I,finiteDistribution D (g j) (a j) := by
  induction I using Finset.induction_on with
  | empty => simp [finiteDistribution]
  | @insert j I hj ih =>
    simp only [sum_insert hj]
    exact (finiteDistribution_two D (fun _ _ => le_rfl)).trans (by linarith)

end PrimeSquares
