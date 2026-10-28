import PrimeSquares.ActualGaussProjectionErrorMaximum
import PrimeSquares.SourceDyadicGaussCoefficientEnvelope
open scoped lp
namespace PrimeSquares
theorem sourceDyadicProjectionError_power_maximum {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (s : ℕ),2 ≤ s →
      ∀ (Γ : Finset ℚ),Γ ⊆ sourceDyadicRationalCenters s →
      ∀ (χ : ℕ → ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ),
        (∀ j,∀ r ∈ Γ,‖κ j r‖ ≤ 1) → ∀ (β : ℕ → ℝ),(∀ j,0 ≤ β j) → (∀ j,β j ≤ 1) →
      ∀ f : ℓ²(ℤ,ℂ),∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
        (∀ j x,‖integerMultiplier
          (circleMajorArcModel Γ ((2 : ℕ)^j*M) (by have h := dyadic_annular_scale_lower hM j;omega)
            (χ j) (κ j) (β j)-rationalGaussSmoothMainBlock Γ ((2 : ℕ)^j*M) s (χ j) (κ j) (β j)) f x‖ ≤ g x) ∧
        ‖g‖ ≤ H*((2 : ℝ)^s)^(-δ)*‖f‖ := by
  obtain ⟨C,hC,h⟩ := sourceDyadicGaussCoefficient_envelope hδ0 hδ1
  refine ⟨2*C*annularProjectionErrorL2Constant,mul_pos (mul_pos (by norm_num) hC)
    annularProjectionErrorL2Constant_pos,?_⟩
  intro M hM s hs Γ hΓ χ κ hκ β hβ0 hβ1 f
  have hc : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 :=
    fun r hr => ((mem_sourceDyadicRationalCenters s r).mp (hΓ hr)).1
  have hd : ∀ r ∈ Γ,(r.den : ℝ) ≤ (2 : ℝ)^(s+1) :=
    fun _ hr => (sourceDyadicRationalCenters_den_bounds (hΓ hr)).2.le
  have hl : ∀ r ∈ Γ,Nat.log2 r.den=s :=
    fun r hr => ((mem_sourceDyadicRationalCenters s r).mp (hΓ hr)).2
  have hp : ∀ r ∈ Γ,‖rationalPrincipalGauss r‖ ≤ C*((2 : ℝ)^s)^(-δ) :=
    fun r hr => (h s r (hΓ hr) (χ 0) (κ 0) (hκ 0 r hr)).1
  have he : ∀ j,∀ r ∈ Γ,‖rationalExceptionalCoefficient (χ j) (κ j) r‖ ≤ C*((2 : ℝ)^s)^(-δ) :=
    fun j r hr => (h s r (hΓ hr) (χ j) (κ j) (hκ j r hr)).2
  have hA : 0 ≤ C*((2 : ℝ)^s)^(-δ) := by positivity
  obtain ⟨g,hg,ht,hn⟩ := actualGaussProjectionError_maximum hM hs Γ hc hd hl χ κ β hβ0 hβ1 hA hA hp he f
  exact ⟨g,hg,ht,hn.trans_eq (by ring)⟩
end PrimeSquares
