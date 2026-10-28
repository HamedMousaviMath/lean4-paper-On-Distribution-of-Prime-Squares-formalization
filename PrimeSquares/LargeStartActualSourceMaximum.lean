import PrimeSquares.LargeStartSmoothMainMaximum
import PrimeSquares.ActualGaussProjectionErrorMaximum
open scoped lp
namespace PrimeSquares
theorem largeStart_actualSource_maximum {C : ℝ} (hC : 0≤C) (hB : SmoothCircleBourgainInput C)
    {M s : ℕ} (hM : 2≤M) (hs : 2≤s) (Γ : Finset ℚ)
    (hc : ∀ r∈Γ,r∈Set.Ico (0 : ℚ) 1)
    (hd : ∀ r∈Γ,(r.den : ℝ)≤(2 : ℝ)^(s+1)) (hl : ∀ r∈Γ,Nat.log2 r.den=s)
    (hwide : (16 : ℝ)^s≤(M : ℝ)^2)
    (hsepScale : 16*((2 : ℝ)^(s+1))^2≤(M : ℝ)^2)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ→ℂ)
    (β : ℕ→ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    {A₀ A₁ : ℝ} (hA₀ : 0≤A₀) (hA₁ : 0≤A₁)
    (hp : ∀ r∈Γ,‖rationalPrincipalGauss r‖≤A₀)
    (he : ∀ r∈Γ,‖rationalExceptionalCoefficient χ κ r‖≤A₁) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ=>ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier (circleMajorArcModel Γ ((2 : ℕ)^j*M)
        (by have h:=dyadic_annular_scale_lower hM j;omega) χ κ (β j)) f x‖≤g x) ∧
      ‖g‖≤((A₀+A₁)*((1/2)*C*circleFrequencyLogFactor Γ+annularProjectionErrorL2Constant))*‖f‖ := by
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := largeStart_smoothMain_maximum hC hB hM hs Γ hc hd hwide hsepScale
    χ κ β hβ1 hA₀ hA₁ hp he f
  obtain ⟨g₁,hg₁,ht₁,hn₁⟩ := actualGaussProjectionError_maximum hM hs Γ hc hd hl
    (fun _=>χ) (fun _=>κ) β hβ0 hβ1 hA₀ hA₁ hp (fun _=>he) f
  refine ⟨g₀+g₁,fun x=>add_nonneg (hg₀ x) (hg₁ x),?_,?_⟩
  · intro j x
    have heq : integerMultiplier (circleMajorArcModel Γ ((2 : ℕ)^j*M)
        (by have h:=dyadic_annular_scale_lower hM j;omega) χ κ (β j)) f=
        integerMultiplier (rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s χ κ (β j)) f+
        integerMultiplier (circleMajorArcModel Γ ((2 : ℕ)^j*M)
          (by have h:=dyadic_annular_scale_lower hM j;omega) χ κ (β j)-
          rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s χ κ (β j)) f := by
      rw [integerMultiplier_sub]
      simp only [_root_.sub_apply]
      abel
    rw [heq]
    change ‖integerMultiplier _ f x+integerMultiplier _ f x‖≤g₀ x+g₁ x
    exact (norm_add_le _ _).trans (add_le_add (ht₀ j x) (ht₁ j x))
  · exact (norm_add_le _ _).trans ((add_le_add hn₀ hn₁).trans_eq (by ring))
end PrimeSquares
