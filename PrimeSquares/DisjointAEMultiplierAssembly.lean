import PrimeSquares.AEBoundedCircleMultipliers
import PrimeSquares.FiniteDisjointSymbolBound

set_option autoImplicit false
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares

theorem finiteAEMultiplier_sum_measurable (Γ : Finset ℚ) (μ : ℚ→AEBoundedCircleSymbol 1) :
    AEStronglyMeasurable (fun θ => ∑ r ∈ Γ,(μ r).value θ) AddCircle.haarAddCircle := by
  classical
  induction Γ using Finset.induction_on with
  | empty => simpa only [sum_empty] using (aestronglyMeasurable_const (b := (0:ℂ)))
  | @insert r Γ hr ih =>
    convert (μ r).measurable.add ih using 1
    ext θ
    simp only [sum_insert hr,Pi.add_apply]

theorem disjointAEMultiplier_sum_bound (Γ : Finset ℚ) (μ : ℚ→AEBoundedCircleSymbol 1)
    (P : ℚ→C(PrimeCircle,ℂ))
    (hP : ∀ r ∈ Γ,∀ t ∈ Γ,r≠t → ∀ θ,P r θ=0 ∨ P t θ=0)
    (hs : ∀ r ∈ Γ,∀ᵐ θ ∂AddCircle.haarAddCircle,P r θ=0 → (μ r).value θ=0) :
    ∀ᵐ θ ∂AddCircle.haarAddCircle,‖∑ r ∈ Γ,(μ r).value θ‖≤1 := by
  classical
  have hs' : ∀ᵐ θ ∂AddCircle.haarAddCircle,∀ r,r∈Γ → P r θ=0 → (μ r).value θ=0 :=
    ae_all_iff.mpr (fun r => by
      by_cases hr : r∈Γ
      · exact (hs r hr).mono (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (hr h).elim))
  filter_upwards [hs',ae_all_iff.mpr (fun r => (μ r).norm_bound)] with θ hsupport hbound
  by_cases hz : ∀ r ∈ Γ,(μ r).value θ=0
  · rw [sum_eq_zero hz,norm_zero]
    norm_num
  · push Not at hz
    obtain ⟨r,hr,hr0⟩ := hz
    have hrP : P r θ≠0 := fun h => hr0 (hsupport r hr h)
    have he : (∑ t ∈ Γ,(μ t).value θ)=(μ r).value θ := by
      apply sum_eq_single r
      · intro t ht htr
        exact hsupport t ht ((hP t ht r hr htr θ).resolve_right hrP)
      · exact fun h => (h hr).elim
    rw [he]
    exact hbound r

noncomputable def disjointAEMultiplierSymbol (Γ : Finset ℚ) (μ : ℚ→AEBoundedCircleSymbol 1)
    (P : ℚ→C(PrimeCircle,ℂ))
    (hP : ∀ r ∈ Γ,∀ t ∈ Γ,r≠t → ∀ θ,P r θ=0 ∨ P t θ=0)
    (hs : ∀ r ∈ Γ,∀ᵐ θ ∂AddCircle.haarAddCircle,P r θ=0 → (μ r).value θ=0) :
    AEBoundedCircleSymbol 1 where
  value θ := ∑ r ∈ Γ,(μ r).value θ
  measurable := finiteAEMultiplier_sum_measurable Γ μ
  norm_bound := disjointAEMultiplier_sum_bound Γ μ P hP hs

theorem disjointAEMultiplierSymbol_local_comp (Γ : Finset ℚ) (μ : ℚ→AEBoundedCircleSymbol 1)
    (P : ℚ→C(PrimeCircle,ℂ))
    (hP : ∀ r ∈ Γ,∀ t ∈ Γ,r≠t → ∀ θ,P r θ=0 ∨ P t θ=0)
    (hs : ∀ r ∈ Γ,∀ᵐ θ ∂AddCircle.haarAddCircle,P r θ=0 → (μ r).value θ=0)
    {r : ℚ} (hr : r∈Γ) (a : C(PrimeCircle,ℂ)) (ha : ∀ θ,P r θ=0 → a θ=0) :
    (integerMultiplier a).comp (aeIntegerMultiplier (μ r))=
      (integerMultiplier a).comp (aeIntegerMultiplier (disjointAEMultiplierSymbol Γ μ P hP hs)) := by
  classical
  apply aeIntegerMultiplier_localized_comp
  have hs' : ∀ᵐ θ ∂AddCircle.haarAddCircle,∀ t,t∈Γ → P t θ=0 → (μ t).value θ=0 :=
    ae_all_iff.mpr (fun t => by
      by_cases ht : t∈Γ
      · exact (hs t ht).mono (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (ht h).elim))
  filter_upwards [hs'] with θ hsupport
  by_cases hz : P r θ=0
  · rw [ha θ hz,zero_mul,zero_mul]
  · have he : (∑ t ∈ Γ,(μ t).value θ)=(μ r).value θ := by
      apply sum_eq_single r
      · intro t ht htr
        exact hsupport t ht ((hP t ht r hr htr θ).resolve_right hz)
      · exact fun h => (h hr).elim
    change a θ*(μ r).value θ=a θ*(∑ t ∈ Γ,(μ t).value θ)
    rw [he]

end PrimeSquares
