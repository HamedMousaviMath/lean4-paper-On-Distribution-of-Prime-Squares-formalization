import PrimeSquares.BourgainWeightedSourceProjection
import PrimeSquares.SmoothMainCommonAmplitudes
import PrimeSquares.ScalarMultiplierMajorants
import PrimeSquares.AnnularModelSize
open Finset
open scoped lp
namespace PrimeSquares
theorem largeStart_smoothMain_maximum {C : ℝ} (hC : 0≤C) (hB : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2≤M) (hs : 2≤s) (Γ : Finset ℚ)
    (hc : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hd : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1))
    (hwide : (16 : ℝ)^s≤(M : ℝ)^2)
    (hsepScale : 16*((2 : ℝ)^(s+1))^2≤(M : ℝ)^2)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ→ℂ)
    (β : ℕ→ℝ) (hβ1 : ∀ j,β j≤1)
    {A₀ A₁ : ℝ} (hA₀ : 0≤A₀) (hA₁ : 0≤A₁)
    (hp : ∀ r∈Γ,‖rationalPrincipalGauss r‖≤A₀)
    (he : ∀ r∈Γ,‖rationalExceptionalCoefficient χ κ r‖≤A₁) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ=>ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s χ κ (β j)) f x‖≤g x) ∧
      ‖g‖≤((1/2)*C*circleFrequencyLogFactor Γ*(A₀+A₁))*‖f‖ := by
  let m₀ := fun j=>∑ r∈Γ,rationalPrincipalGauss r • circleAnnularSmoothProjection ((2 : ℕ)^j*M) s r
  let m₁ := fun j=>∑ r∈Γ,rationalExceptionalCoefficient χ κ r • circleAnnularSmoothProjection ((2 : ℕ)^j*M) s r
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := bourgain_weightedSource_projection hC hB hM hs Γ hc hd hwide hsepScale
    rationalPrincipalGauss hA₀ hp f
  obtain ⟨g₁,hg₁,ht₁,hn₁⟩ := bourgain_weightedSource_projection hC hB hM hs Γ hc hd hwide hsepScale
    (rationalExceptionalCoefficient χ κ) hA₁ he f
  obtain ⟨u₀,hu₀,htU₀,hnU₀⟩ := scalar_multiplier_majorant m₀
    (fun j=>annularOscillatoryModel ((2 : ℕ)^j*M) 1 0) (by norm_num : (0 : ℝ)≤1/2)
    (fun j=>annularOscillatoryModel_norm_half (dyadic_annular_scale_lower hM j) (by norm_num) 0)
    f g₀ hg₀ ht₀ hn₀
  obtain ⟨u₁,hu₁,htU₁,hnU₁⟩ := scalar_multiplier_majorant m₁
    (fun j=>annularOscillatoryModel ((2 : ℕ)^j*M) (β j) 0) (by norm_num : (0 : ℝ)≤1/2)
    (fun j=>annularOscillatoryModel_norm_half (dyadic_annular_scale_lower hM j) (hβ1 j) 0)
    f g₁ hg₁ ht₁ hn₁
  refine ⟨u₀+u₁,fun x=>add_nonneg (hu₀ x) (hu₁ x),?_,?_⟩
  · intro j x
    rw [rationalGaussSmoothMain_common_amplitudes,integerMultiplier_sub]
    change ‖integerMultiplier (_ • m₀ j) f x-integerMultiplier (_ • m₁ j) f x‖≤u₀ x+u₁ x
    exact (norm_sub_le _ _).trans (add_le_add (htU₀ j x) (htU₁ j x))
  · exact (norm_add_le _ _).trans ((add_le_add hnU₀ hnU₁).trans_eq (by ring))
end PrimeSquares
