import PrimeSquares.PowerDecayingAnnularMaximum
import PrimeSquares.RationalGaussCoefficientBounds

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem iw_denominator_tail_power {Q q : ℝ} (hQ : 0<Q) (hQq : Q≤q) :
    q^(-(3/8 : ℝ))≤Q^(-(1/4 : ℝ))*q^(-(1/8 : ℝ)) := by
  have hq : 0<q := hQ.trans_le hQq
  calc
    _ = q^(-(1/4 : ℝ))*q^(-(1/8 : ℝ)) := by
      rw [←Real.rpow_add hq]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hQ hQq (by norm_num)) (Real.rpow_nonneg hq.le _)

/-- An actual countable dyadic maximum of the original denominator-dependent
cutoff symbols. This permits variable beta and a variable upper denominator
limit. Only the already recorded general smooth multifrequency input is used. -/
theorem iw_annular_denominator_tail {C A Q : ℝ} (hC : 0≤C)
    (HB : SmoothCircleBourgainInput C) (hA : 0≤A) (hQ : 0<Q)
    {M : ℕ} (hM : 2≤M) (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ → ℂ) (hc : ∀ r,r∈Set.Ico (0 : ℚ) 1 →
      ‖c r‖≤A*(r.den : ℝ)^(-(3/8 : ℝ)))
    (R : ℕ → ℝ) (hR : ∀ j,0≤R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier
        (varyingIndexAnnularBlock ((sourceRationalCenters (R j)).filter
          (fun r => Q<(r.den : ℝ))) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c) f x‖≤g x) ∧
      ‖g‖≤(annularPowerConstant C (1/8)*A*Q^(-(1/4 : ℝ)))*‖f‖ := by
  classical
  obtain ⟨g,hg,ht,hn⟩ := powerAnnular_countable_maximum hC HB (by norm_num : (0 : ℝ)<1/8)
    hM (fun r => Q<(r.den : ℝ)) β hβ0 hβ1 c
    (show 0≤A*Q^(-(1/4 : ℝ)) by positivity)
    (fun r hr hq => (hc r hr).trans
      ((mul_le_mul_of_nonneg_left (iw_denominator_tail_power hQ hq.le) hA).trans_eq (by ring)))
    R hR f
  refine ⟨g,hg,ht,?_⟩
  convert hn using 1; ring

theorem iw_gauss_annular_denominator_tails {C : ℝ} (hC : 0≤C)
    (HB : SmoothCircleBourgainInput C) :
    ∃ K : ℝ,0<K ∧ ∀ Q : ℝ,0<Q → ∀ (M : ℕ) (hM : 2≤M),
      ∀ (β : ℕ → ℝ),(∀ j,0≤β j) → (∀ j,β j≤1) →
      ∀ (χ : (r : ℚ) → DirichletCharacter ℂ r.den) (R : ℕ → ℝ),(∀ j,0≤R j) →
      ∀ f : ℓ²(ℤ,ℂ),∃ g₀ gχ : lp (fun _ : ℤ => ℝ) 2,
        (∀ x,0≤g₀ x ∧ 0≤gχ x) ∧
        (∀ j x,‖integerMultiplier
          (varyingIndexAnnularBlock ((sourceRationalCenters (R j)).filter
            (fun r => Q<(r.den : ℝ))) ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) 1 rationalPrincipalGauss) f x‖≤g₀ x) ∧
        (∀ j x,‖integerMultiplier
          (varyingIndexAnnularBlock ((sourceRationalCenters (R j)).filter
            (fun r => Q<(r.den : ℝ))) ((2 : ℕ)^j*M)
            (by have h := dyadic_annular_scale_lower hM j;omega) (β j)
            (fun r => rationalTwistedGauss r (χ r))) f x‖≤gχ x) ∧
        ‖g₀‖≤K*Q^(-(1/4 : ℝ))*‖f‖ ∧ ‖gχ‖≤K*Q^(-(1/4 : ℝ))*‖f‖ := by
  obtain ⟨A,hA,hGauss⟩ := rationalGauss_uniform_decay (by norm_num : (3/8 : ℝ)<1/2)
  refine ⟨annularPowerConstant C (1/8)*A,mul_pos (annularPowerConstant_pos hC _) hA,?_⟩
  intro Q hQ M hM β hβ0 hβ1 χ R hR f
  obtain ⟨g₀,hg₀,ht₀,hn₀⟩ := iw_annular_denominator_tail hC HB hA.le hQ hM
    (fun _ => 1) (fun _ => by norm_num) (fun _ => le_rfl) rationalPrincipalGauss
    (fun r _ => (hGauss r).1) R hR f
  obtain ⟨gχ,hgχ,htχ,hnχ⟩ := iw_annular_denominator_tail hC HB hA.le hQ hM β hβ0 hβ1
    (fun r => rationalTwistedGauss r (χ r)) (fun r _ => (hGauss r).2 (χ r)) R hR f
  exact ⟨g₀,gχ,fun x => ⟨hg₀ x,hgχ x⟩,ht₀,htχ,hn₀,hnχ⟩

end PrimeSquares
