import PrimeSquares.CanonicalRationalCenters
import PrimeSquares.QuantitativeIWParameters
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- Exact rational representatives of the union of torsion subgroups
formed from products of at most k members of S. -/
noncomputable def iwFrequencySet (S : Finset ℕ) (k : ℕ) : Finset ℚ := by
  classical
  exact (canonicalRationalCenters (∏ s∈S,s)).filter (fun r =>
    ∃ A : Finset ℕ,A⊆S ∧ A.card≤k ∧ r.den∣∏ s∈A,s)

theorem iwFrequencySet_mem {S : Finset ℕ} (hS : ∀ s∈S,0<s) {k : ℕ} (r : ℚ) :
    r∈iwFrequencySet S k ↔ r∈Set.Ico (0 : ℚ) 1 ∧
      ∃ A : Finset ℕ,A⊆S ∧ A.card≤k ∧ r.den∣∏ s∈A,s := by
  classical
  simp only [iwFrequencySet,mem_filter,mem_canonicalRationalCenters]
  constructor
  · rintro ⟨⟨hr,_⟩,hA⟩
    exact ⟨hr,hA⟩
  · rintro ⟨hr,A,hAS,hcard,hden⟩
    have hdvd : r.den∣∏ s∈S,s := hden.trans (Finset.prod_dvd_prod_of_subset _ _ _ hAS)
    exact ⟨⟨hr,Nat.le_of_dvd (prod_pos hS) hdvd⟩,A,hAS,hcard,hden⟩

theorem iwFrequencySet_denominator_bound {S : Finset ℕ} (hS : ∀ s∈S,0<s)
    {k : ℕ} {T : ℝ} (hT : 1≤T) (hcap : ∀ s∈S,(s : ℝ)≤T) {r : ℚ}
    (hr : r∈iwFrequencySet S k) : (r.den : ℝ)≤T^k := by
  classical
  obtain ⟨_,A,hAS,hcard,hden⟩ := (iwFrequencySet_mem hS r).mp hr
  have hprod : (r.den : ℝ)≤((∏ s∈A,s : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (prod_pos (fun s hs => hS s (hAS hs))) hden
  calc
    _ ≤ ((∏ s∈A,s : ℕ) : ℝ) := hprod
    _ = ∏ s∈A,(s : ℝ) := by rw [Nat.cast_prod]
    _ ≤ ∏ _s∈A,T := prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun s hs => hcap s (hAS hs))
    _ = T^A.card := prod_const _
    _ ≤ T^k := pow_le_pow_right₀ hT hcard

/-- Raw independent construction data from Tao (2021), Lemma 5.1.
No multiplier, maximal estimate or current-paper low/high conclusion is a field.
The represented frequency set is defined above, rather than an uninterpreted label. -/
structure TaoArcConstructionData (C ρ : ℝ) (k Q : ℕ) where
  S : Finset ℕ
  positive : ∀ s∈S,0<s
  coprime : (S : Set ℕ).Pairwise Nat.Coprime
  period : ℕ
  period_pos : 0<period
  period_bound : period≤3^Q
  covered : canonicalRationalCenters Q⊆iwFrequencySet S k
  periodic : ∀ r∈iwFrequencySet S k,r.den∣period
  component_bound : ∀ s∈S,(s : ℝ)≤C^((k : ℝ)*(Q : ℝ)^(ρ/2))

/-- The existence of the cited deep construction remains an explicit hypothesis.
This predicate is not a Lean axiom or a formalized Mathlib theorem. -/
def RawTaoArcConstructionInput (C : ℝ) : Prop :=
  ∀ ρ : ℝ,0<ρ → ρ<1 → ∀ Q : ℕ,2^(⌊2/ρ⌋₊+1)≤Q →
    Nonempty (TaoArcConstructionData C ρ (⌊2/ρ⌋₊+1) Q)

theorem taoArc_denominator_bound {C : ℝ} (hC : 2≤C) {k Q : ℕ}
    (d : TaoArcConstructionData C (iwRho k) k Q) (hk : 4≤k)
    {r : ℚ} (hr : r∈iwFrequencySet d.S k) :
    (r.den : ℝ)≤ iwDenominatorBound C k Q := by
  let T := C^((k : ℝ)*(Q : ℝ)^(iwRho k/2))
  have hC0 : 0≤C := by linarith
  have hT : 1≤T := Real.one_le_rpow (by linarith : 1≤C) (by positivity)
  have h := iwFrequencySet_denominator_bound d.positive hT d.component_bound hr
  have he : T^k=iwDenominatorBound C k Q := by
    dsimp [T,iwDenominatorBound]
    rw [←Real.rpow_natCast,←Real.rpow_mul hC0,iwRho_half hk]
    congr 1
    ring
  exact h.trans_eq he

theorem quantitative_iw_frequency_geometry {C : ℝ} (hC : 2≤C)
    (HT : RawTaoArcConstructionInput C) {r k Q : ℕ} (hr : 2≤r) (hk : 4≤k) (hQ : 2^k≤Q) :
    ∃ d : TaoArcConstructionData C (iwRho k) k Q,
      (∀ a∈iwFrequencySet d.S k,(a.den : ℝ)≤ iwDenominatorBound C k Q) ∧
        0< iwWidth C r k Q ∧ 4*iwWidth C r k Q*(iwDenominatorBound C k Q)^2<1 := by
  have hraw : Nonempty (TaoArcConstructionData C (iwRho k) k Q) := by
    have h := HT (iwRho k) (iwRho_bounds hk).1 (iwRho_bounds hk).2 Q
      (by simpa only [iwRho_rank hk] using hQ)
    simpa only [iwRho_rank hk] using h
  obtain ⟨d⟩ := hraw
  exact ⟨d,fun _ ha => taoArc_denominator_bound hC d hk ha,
    iwWidth_pos hC hr k Q,iwWidth_denominator_separation hC hr k Q⟩

end PrimeSquares
