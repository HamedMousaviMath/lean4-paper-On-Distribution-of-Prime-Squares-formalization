import PrimeSquares.LocalizedTimePrefixMajorant
import PrimeSquares.RationalCircleRealPrefix
import PrimeSquares.DisjointMultiplierBessel
import PrimeSquares.FiniteDisjointSymbolBound

open Finset
open scoped lp
namespace PrimeSquares

theorem rationalCircle_interval_grouping (Γ : Finset ℚ) (a K : ℕ)
    (F : ℚ → C(PrimeCircle,ℂ)) :
    intervalCircleSymbol a K (rationalCircleDenominatorBlock Γ F)=
      ∑ r ∈ Γ.filter (fun r => a ≤ r.den ∧ r.den<a+K),F r := by
  classical
  simp only [intervalCircleSymbol,rationalCircleDenominatorBlock,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  by_cases hr : a ≤ r.den ∧ r.den<a+K
  · rw [ite_eq_left hr,sum_eq_single (r.den-a)]
    · rw [ite_eq_left (by omega : r.den=a+(r.den-a))]
    · intro j _ hj
      rw [ite_eq_right (by omega)]
    · intro hj
      exact (hj (mem_range.mpr (by omega))).elim
  · rw [ite_eq_right hr]
    apply sum_eq_zero
    intro j hj
    rw [ite_eq_right (by have hj' := mem_range.mp hj;omega)]

theorem finite_localized_symbol_sum (Γ Δ : Finset ℚ) (hΔ : Δ ⊆ Γ)
    (F P : ℚ → C(PrimeCircle,ℂ)) (hF : ∀ r ∈ Γ,F r=F r*P r)
    (hP : ∀ r ∈ Γ,∀ t ∈ Γ,r ≠ t → ∀ θ,P r θ=0 ∨ P t θ=0) :
    (∑ r ∈ Δ,F r)=(∑ r ∈ Δ,F r)*(∑ r ∈ Δ,P r) := by
  classical
  symm
  rw [sum_mul]
  apply sum_congr rfl
  intro r hr
  rw [mul_sum]
  calc
    _=F r*P r := by
      apply sum_eq_single r
      · intro t ht htr
        ext θ
        change F r θ*P t θ=0
        rcases hP r (hΔ hr) t (hΔ ht) (Ne.symm htr) θ with hz|hz
        · have he := congrArg (fun z : C(PrimeCircle,ℂ) => z θ) (hF r (hΔ hr))
          change F r θ=F r θ*P r θ at he
          rw [hz,mul_zero] at he
          rw [he,zero_mul]
        · rw [hz,mul_zero]
      · exact fun h => (h hr).elim
    _=F r := (hF r (hΔ hr)).symm

theorem rationalCircle_grouped_disjoint (Γ : Finset ℚ) (P : ℚ → C(PrimeCircle,ℂ))
    (hP : ∀ r ∈ Γ,∀ t ∈ Γ,r ≠ t → ∀ θ,P r θ=0 ∨ P t θ=0) :
    ∀ i j,i ≠ j → ∀ θ,rationalCircleDenominatorBlock Γ P i θ=0 ∨
      rationalCircleDenominatorBlock Γ P j θ=0 := by
  classical
  intro i j hij θ
  by_cases hz : ∀ r ∈ Γ,r.den=i → P r θ=0
  · left
    simp only [rationalCircleDenominatorBlock,ContinuousMap.sum_apply]
    exact sum_eq_zero (fun r hr => hz r (mem_filter.mp hr).1 (mem_filter.mp hr).2)
  push Not at hz
  obtain ⟨r,hr,hri,hrz⟩ := hz
  right
  simp only [rationalCircleDenominatorBlock,ContinuousMap.sum_apply]
  apply sum_eq_zero
  intro t ht
  obtain ⟨ht,hjt⟩ := mem_filter.mp ht
  exact (hP r hr t ht (by intro h;subst t;exact hij (hri.symm.trans hjt)) θ).resolve_left hrz

theorem rationalCircle_grouped_norm (Γ : Finset ℚ) (P : ℚ → C(PrimeCircle,ℂ))
    (hP : ∀ r ∈ Γ,∀ t ∈ Γ,r ≠ t → ∀ θ,P r θ=0 ∨ P t θ=0)
    (hb : ∀ r ∈ Γ,∀ θ,‖P r θ‖ ≤ 1) (i : ℕ) (θ : PrimeCircle) :
    ‖rationalCircleDenominatorBlock Γ P i θ‖ ≤ 1 := by
  apply finite_disjoint_symbol_bound (Γ.filter (fun r => r.den=i)) P
  · intro r hr t ht hne
    exact hP r (mem_filter.mp hr).1 t (mem_filter.mp ht).1 hne
  · norm_num
  · intro r hr
    exact hb r (mem_filter.mp hr).1

theorem finiteFrequency_denominator_maximum (Γ : Finset ℚ) (M h : ℕ)
    (hM : ∀ r ∈ Γ,r.den ≤ M) (hh : M+1 ≤ 2^h)
    (F : ℕ → ℚ → C(PrimeCircle,ℂ)) (P : ℚ → C(PrimeCircle,ℂ))
    (hF : ∀ t,∀ r ∈ Γ,F t r=F t r*P r)
    (hP : ∀ r ∈ Γ,∀ u ∈ Γ,r ≠ u → ∀ θ,P r θ=0 ∨ P u θ=0)
    (hp : ∀ r ∈ Γ,∀ θ,‖P r θ‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hMax : ∀ Δ : Finset ℚ,Δ ⊆ Γ → ∀ v : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
        (∀ t x,‖integerMultiplier (∑ r ∈ Δ,F t r) v x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖v‖)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t R,0 ≤ R → ∀ x,‖integerMultiplier
        (∑ r ∈ Γ.filter (fun r => (r.den : ℝ) ≤ R),F t r) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (h+1 : ℝ)*B*‖f‖ := by
  classical
  let p := rationalCircleDenominatorBlock Γ P
  let m := fun t => rationalCircleDenominatorBlock Γ (F t)
  have hpg := rationalCircle_grouped_disjoint Γ P hP
  have hlocal (t a K : ℕ) : intervalCircleSymbol a K (m t)=
      intervalCircleSymbol a K (m t)*intervalCircleSymbol a K p := by
    dsimp [m,p]
    rw [rationalCircle_interval_grouping,rationalCircle_interval_grouping]
    exact finite_localized_symbol_sum Γ _ (filter_subset _ _) (F t) P (hF t) hP
  have hex (k b : ℕ) : ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ t x,‖integerMultiplier (intervalCircleSymbol b (2^k) (m t)) f x‖ ≤ g x) ∧
      ‖g‖ ≤ B*‖integerMultiplier (intervalCircleSymbol b (2^k) p) f‖ := by
    obtain ⟨g,hg,ht,hn⟩ := hMax (Γ.filter (fun r => b ≤ r.den ∧ r.den<b+2^k))
      (filter_subset _ _) (integerMultiplier (intervalCircleSymbol b (2^k) p) f)
    refine ⟨g,hg,?_,hn⟩
    intro t x
    rw [integerMultiplier_localized _ _ (hlocal t b (2^k)) f]
    simpa only [m,rationalCircle_interval_grouping] using ht t x
  choose G hG0 hGt hGn using hex
  obtain ⟨g,hg,ht,hn⟩ := localized_time_prefix_majorant h 0 m p hpg f G hB
    (fun t k b x => hGt k b t x)
    (fun k b => (pow_le_pow_left₀ (norm_nonneg _) (hGn k b) 2).trans_eq (mul_pow _ _ _))
  have henergy : intervalRealBudget 0 (2^h) (fun i => ‖integerMultiplier (p i) f‖^2) ≤ ‖f‖^2 := by
    simpa only [intervalRealBudget,Nat.zero_add,one_pow,one_mul] using
      disjointMultiplier_bessel (range (2^h)) p hpg (by norm_num : (0 : ℝ) ≤ 1)
        (fun i _ => rationalCircle_grouped_norm Γ P hP hp i) f
  refine ⟨g,hg,?_,hn.trans ?_⟩
  · intro t R hR x
    rw [rationalCircle_real_prefix Γ M hM hR,realTruncatedCircleSymbol_prefix _ hR]
    exact ht t _ ((min_le_left _ _).trans hh) x
  · exact mul_le_mul_of_nonneg_left
      ((Real.sqrt_le_sqrt henergy).trans_eq (Real.sqrt_sq (norm_nonneg f))) (by positivity)

end PrimeSquares
