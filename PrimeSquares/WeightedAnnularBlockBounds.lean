import PrimeSquares.WeightedAnnularLargeStartMaximum
import PrimeSquares.CircleSourceCutoffSupport
import PrimeSquares.FiniteDisjointSymbolBound

open Finset
namespace PrimeSquares

theorem circleAnnularSource_norm_bound {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : β ≤ 1)
    (s : ℕ) (r : ℚ) (θ : PrimeCircle) :
    ‖circleAnnularSource N (by omega) β s r θ‖ ≤ 3/2 := by
  have hb (x : ℝ) : ‖localizedAnnularSource N (by omega) β s x‖ ≤ 1/2 := by
    change ‖annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoffScale s x)‖ ≤ 1/2
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,sourceArcCutoffScale,
      abs_of_nonneg (sourceArcCutoff_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans
      (by simpa only [mul_one] using annularOscillatoryModel_norm_half hN hβ x)
  have h := compactCircleLift_norm_bound (localizedAnnularSource N (by omega) β s)
    (localizedAnnularSource_support N (by omega) β s) hb
    (θ-((r : ℝ) : PrimeCircle))
  norm_num only [show (3 : ℝ)*(1/2)=3/2 by norm_num] at h
  exact h

theorem circleAnnularSource_zero_of_cutoff (N : ℕ) (hN : 1 ≤ N) (β : ℝ)
    {s : ℕ} (hs : 1 ≤ s) (r : ℚ) (θ : PrimeCircle)
    (hz : circleSourceCutoff s r θ=0) : circleAnnularSource N hN β s r θ=0 := by
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he] at hz ⊢
  have hb (k : ℤ) : sourceArcCutoffScale s (ξ-(r : ℝ)+k)=0 := by
    by_contra hk
    exact circleSourceCutoff_ne_zero_of_lift hs r ξ k hk hz
  rw [circleAnnularSource_real]
  simp only [hb,Complex.ofReal_zero,mul_zero,tsum_zero]

theorem weightedAnnularSourceBlock_norm_bound {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    {β A : ℝ} (hβ : β ≤ 1) (c : ℚ → ℂ) (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A) :
    ‖weightedAnnularSourceBlock Γ N (by omega) s β c‖ ≤ (3/2 : ℝ)*A := by
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ (3/2)*A)).mpr
  apply finite_disjoint_symbol_bound Γ (fun r => c r • circleAnnularSource N (by omega) β s r)
  · intro r hr t ht hne θ
    rcases circleSourceCutoff_disjoint hs (hc r hr) (hc t ht) hne (hd r hr) (hd t ht) θ with h|h
    · left
      simp only [ContinuousMap.smul_apply,circleAnnularSource_zero_of_cutoff N (by omega) β (by omega) r θ h,smul_zero]
    · right
      simp only [ContinuousMap.smul_apply,circleAnnularSource_zero_of_cutoff N (by omega) β (by omega) t θ h,smul_zero]
  · positivity
  · intro r hr θ
    simp only [ContinuousMap.smul_apply,norm_smul]
    exact (mul_le_mul (hb r hr) (circleAnnularSource_norm_bound hN hβ s r θ)
      (norm_nonneg _) hA).trans_eq (by ring)

theorem weightedAnnularSourceBlock_operator_bound {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s)
    (Γ : Finset ℚ) (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    {β A : ℝ} (hβ : β ≤ 1) (c : ℚ → ℂ) (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A) :
    ‖integerMultiplier (weightedAnnularSourceBlock Γ N (by omega) s β c)‖ ≤ (3/2 : ℝ)*A :=
  (integerMultiplier_opNorm_le _).trans (weightedAnnularSourceBlock_norm_bound hN hs Γ hc hd hβ c hA hb)

end PrimeSquares
