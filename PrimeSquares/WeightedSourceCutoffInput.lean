import PrimeSquares.CircleSourceCutoffDisjoint
import PrimeSquares.CircleSourceCutoffPointwiseBound
import PrimeSquares.FiniteDisjointSymbolBound
import PrimeSquares.CircleMultipliers
open Finset
open scoped lp
namespace PrimeSquares
noncomputable def weightedSourceCutoff (Γ : Finset ℚ) (s : ℕ) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,c r • circleSourceCutoff s r
theorem weightedSourceCutoff_norm {s : ℕ} (hs : 2 ≤ s) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A) :
    ‖weightedSourceCutoff Γ s c‖ ≤ A := by
  apply (ContinuousMap.norm_le _ hA).mpr
  change ∀ θ,‖(∑ r ∈ Γ,c r • circleSourceCutoff s r) θ‖ ≤ A
  refine finite_disjoint_symbol_bound Γ (fun r => c r • circleSourceCutoff s r) ?_ hA ?_
  · intro r hr t ht hne θ
    rcases circleSourceCutoff_disjoint hs (hc r hr) (hc t ht) hne (hd r hr) (hd t ht) θ with h|h
    · left; simp only [ContinuousMap.smul_apply,h,smul_zero]
    · right; simp only [ContinuousMap.smul_apply,h,smul_zero]
  · intro r hr θ
    simp only [ContinuousMap.smul_apply,norm_smul]
    exact (mul_le_mul_of_nonneg_left (circleSourceCutoff_pointwise_norm (by omega) r θ)
      (norm_nonneg _)).trans (by simpa only [mul_one] using hb r hr)
theorem weightedSourceCutoff_input_norm {s : ℕ} (hs : 2 ≤ s) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A) (f : ℓ²(ℤ,ℂ)) :
    ‖integerMultiplier (weightedSourceCutoff Γ s c) f‖ ≤ A*‖f‖ :=
  (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    ((integerMultiplier_opNorm_le _).trans (weightedSourceCutoff_norm hs Γ hc hd c hA hb)) (norm_nonneg _))
end PrimeSquares
