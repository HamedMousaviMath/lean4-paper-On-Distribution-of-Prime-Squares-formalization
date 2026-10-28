import PrimeSquares.AnnularBlockLogarithmicBudget
import PrimeSquares.NestedSourceLocalization
import PrimeSquares.FiniteFrequencyTruncationMaximum
import PrimeSquares.CircleSourceCutoffPointwiseBound

open Finset
open scoped lp
namespace PrimeSquares

theorem weightedAnnular_truncation_maximum {C : ℝ} (hC : 0 ≤ C)
    (hB : SmoothCircleBourgainInput C) {M s : ℕ} (hM : 2 ≤ M) (hs : 4 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j R,0 ≤ R → ∀ x,‖integerMultiplier
        (weightedAnnularSourceBlock (Γ.filter (fun r => (r.den : ℝ) ≤ R)) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (annularTruncationConstant C*A*((s : ℝ)+1)^3)*‖f‖ := by
  have hE := annularProjectionErrorL2Constant_pos
  have hlog0 := circleFrequencyLogFactor_nonneg Γ
  obtain ⟨ht,hst,hw⟩ := predecessorSourceCutoff_geometry hs
  let F := fun j r => c r • circleAnnularSource ((2 : ℕ)^j*M)
    (by have h := dyadic_annular_scale_lower hM j;omega) (β j) s r
  let P := circleSourceCutoff (s-1)
  let B := A*((3/2 : ℝ)*(2*(s : ℝ)+3)+(1/2)*C*circleFrequencyLogFactor Γ+
    annularProjectionErrorL2Constant)
  have hlocal : ∀ j,∀ r ∈ Γ,F j r=F j r*P r := by
    intro j r _
    dsimp [F,P]
    calc
      _=c r • (circleAnnularSource ((2 : ℕ)^j*M) _ (β j) s r*circleSourceCutoff (s-1) r) :=
        congrArg (fun z => c r • z) (circleAnnularSource_localized _ (by omega) ht hst (β j) r)
      _=_ := (smul_mul_assoc _ _ _).symm
  have hP : ∀ r ∈ Γ,∀ u ∈ Γ,r ≠ u → ∀ θ,P r θ=0 ∨ P u θ=0 := by
    intro r hr u hu hne θ
    exact circleSourceCutoff_general_disjoint (hc r hr) (hc u hu) hne (hd r hr) (hd u hu) hw θ
  have hMax : ∀ Δ : Finset ℚ,Δ ⊆ Γ → ∀ v : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
        (∀ j x,‖integerMultiplier (∑ r ∈ Δ,F j r) v x‖ ≤ g x) ∧ ‖g‖ ≤ B*‖v‖ := by
    intro Δ hΔ v
    obtain ⟨g,hg,htg,hng⟩ := weightedAnnular_allStartingScales hC hB hM (by omega) Δ
      (fun r hr => hc r (hΔ hr)) (fun r hr => hd r (hΔ hr)) β hβ0 hβ1 c hA
      (fun r hr => hb r (hΔ hr)) v
    refine ⟨g,hg,htg,hng.trans ?_⟩
    have hlog := circleFrequencyLogFactor_mono hΔ
    dsimp [B]
    gcongr
  have hh : (2 : ℕ)^(s+1)+1 ≤ (2 : ℕ)^(s+2) := by
    have hp : (1 : ℕ) ≤ (2 : ℕ)^(s+1) := Nat.one_le_pow _ _ (by norm_num)
    rw [show s+2=(s+1)+1 by omega,pow_succ]
    omega
  obtain ⟨g,hg,htg,hng⟩ := finiteFrequency_denominator_maximum Γ ((2 : ℕ)^(s+1)) (s+2)
    (fun r hr => by exact_mod_cast hd r hr) hh F P hlocal hP
    (fun r _ θ => circleSourceCutoff_pointwise_norm ht r θ)
    (show 0 ≤ B by dsimp [B];positivity) hMax f
  refine ⟨g,hg,htg,hng.trans ?_⟩
  have hb' := annular_allStarting_budget Γ s hc hd hC hA
  dsimp [B]
  push_cast
  convert mul_le_mul_of_nonneg_right hb' (norm_nonneg f) using 1;ring

end PrimeSquares
