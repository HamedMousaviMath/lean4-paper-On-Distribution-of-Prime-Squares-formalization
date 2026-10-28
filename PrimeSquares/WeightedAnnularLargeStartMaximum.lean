import PrimeSquares.BourgainWeightedSourceProjection
import PrimeSquares.ScalarMultiplierMajorants
import PrimeSquares.CircleAnnularSourceDecomposition
import PrimeSquares.RationalProjectionErrorMaximum
import PrimeSquares.AnnularModelSize

open Finset
open scoped lp

namespace PrimeSquares

/-- Actual weighted bare annular source block, before the two Gauss families
are combined. The rational centers and coefficients are fixed. -/
noncomputable def weightedAnnularSourceBlock (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (s : ℕ) (β : ℝ) (c : ℚ → ℂ) : C(PrimeCircle,ℂ) :=
  ∑ r ∈ Γ,c r • circleAnnularSource N hN β s r

theorem weightedAnnularSourceBlock_decomposition (Γ : Finset ℚ) (N : ℕ) (hN : 1 ≤ N)
    (s : ℕ) (β : ℝ) (c : ℚ → ℂ) :
    weightedAnnularSourceBlock Γ N hN s β c=
      annularOscillatoryModel N β 0 •
        (∑ r ∈ Γ,c r • circleAnnularSmoothProjection N s r)+
      rationalProjectionErrorBlock Γ N hN s (fun _ => β) c := by
  unfold weightedAnnularSourceBlock rationalProjectionErrorBlock
  rw [smul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  rw [circleAnnularSource_decomposition]
  ext θ
  simp only [ContinuousMap.smul_apply,ContinuousMap.add_apply,smul_eq_mul]
  ring

theorem largeStart_weightedAnnular_maximum {C : ℝ} (hC : 0 ≤ C)
    (hB : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2 ≤ M) (hs : 2 ≤ s) (Γ : Finset ℚ)
    (hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1)
    (hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1))
    (hwide : (16 : ℝ)^s ≤ (M : ℝ)^2)
    (hsepScale : 16*((2 : ℝ)^(s+1))^2 ≤ (M : ℝ)^2)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1)
    (c : ℚ → ℂ) {A : ℝ} (hA : 0 ≤ A) (hb : ∀ r ∈ Γ,‖c r‖ ≤ A)
    (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖integerMultiplier
        (weightedAnnularSourceBlock Γ ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) s (β j) c) f x‖ ≤ g x) ∧
      ‖g‖ ≤ (A*((1/2)*C*circleFrequencyLogFactor Γ+annularProjectionErrorL2Constant))*‖f‖ := by
  let m := fun j => ∑ r ∈ Γ,c r • circleAnnularSmoothProjection ((2 : ℕ)^j*M) s r
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := bourgain_weightedSource_projection hC hB hM hs Γ hc hd
    hwide hsepScale c hA hb f
  obtain ⟨u,hu,htU,hnU⟩ := scalar_multiplier_majorant m
    (fun j => annularOscillatoryModel ((2 : ℕ)^j*M) (β j) 0)
    (by norm_num : (0 : ℝ) ≤ 1/2)
    (fun j => annularOscillatoryModel_norm_half (dyadic_annular_scale_lower hM j) (hβ1 j) 0)
    f g₀ hg₀ ht₀ hn₀
  obtain ⟨g₁,hg₁,ht₁,hn₁⟩ := rationalProjectionErrorBlock_maximum hM hs Γ hc hd
    (fun j _ => β j) (fun j _ _ => hβ0 j) (fun j _ _ => hβ1 j)
    (fun _ => c) hA (fun _ => hb) f
  refine ⟨u+g₁,fun x => add_nonneg (hu x) (hg₁ x),?_,?_⟩
  · intro j x
    rw [weightedAnnularSourceBlock_decomposition,integerMultiplier_add]
    change ‖integerMultiplier (_ • m j) f x+integerMultiplier _ f x‖ ≤ u x+g₁ x
    exact (norm_add_le _ _).trans (add_le_add (htU j x) (ht₁ j x))
  · exact (norm_add_le _ _).trans ((add_le_add hnU hn₁).trans_eq (by ring))

end PrimeSquares
