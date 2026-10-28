import PrimeSquares.CircleHighFiniteWindow
import PrimeSquares.ConductorRatioBound

open Finset
namespace PrimeSquares

noncomputable def highPowerConstant (C T δ η : ℝ) : ℝ :=
  12*(2*C*highMaskConstant*(1+T))/(1-(2 : ℝ)^(-(δ-η)))

theorem circleHighModel_power_bound {N : ℕ} (hN : 2 ≤ N) (Γ : Finset ℚ) (M q₀ : ℕ) [NeZero q₀]
    {Q C T δ η : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C) (hT : 0 ≤ T) (hδη : η < δ)
    (hratio : conductorMajorant q₀/(q₀ : ℝ) ≤ T) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hG : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q),IsUnit a →
      ‖principalSquareSum q a‖ ≤ C*(q : ℝ)^(-δ) ∧ ‖twistedSquareSum q χ a‖ ≤ C*(q : ℝ)^(-δ))
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hk : ∀ r ∈ Γ,‖κ r‖ ≤ 1) :
    ∀ θ,‖circleHighModel Γ N (by omega) q₀ Q (conductorMajorant q₀) χ κ β θ‖ ≤ highPowerConstant C T δ η*Q^(-η) := by
  have hK : 0 < highMaskConstant := (by norm_num : (0 : ℝ) < 1).trans_le highMaskConstant_one_le
  have hA : 0 ≤ (2*C*highMaskConstant*(1+T))*Q^(-η) := by positivity
  have hsum : ∀ ξ : ℝ,‖∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀) χ κ β r (ξ-(r : ℝ))‖ ≤
      4*((2*C*highMaskConstant*(1+T))*Q^(-η))/(1-(2 : ℝ)^(-(δ-η))) := by
    intro ξ
    apply rational_high_weighted_sum Γ M ξ _ hA (sub_pos.mpr hδη) hΓ
    · intro r _ hz
      exact centeredHighSymbol_zero_of_broad N (by omega) q₀ Q (conductorMajorant q₀) χ κ β r _ hz
    · intro r hr
      exact centeredHighSymbol_power_bound hN q₀ hQ hC hT hratio hη0 hη1 hG χ κ hβ0 hβ1 r (hk r hr) _
  apply circleBound_from_fundamental_interval
  intro ξ hξ
  rw [circleHighModel_finite_window Γ N (by omega) q₀ Q (conductorMajorant q₀) χ κ β (fun r hr => (hΓ r hr).1) hξ]
  have h1 := hsum (ξ-1)
  have h2 := hsum ξ
  have h3 := hsum (ξ+1)
  calc
    _ ≤ (‖∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀) χ κ β r (ξ-1-(r : ℝ))‖+
        ‖∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀) χ κ β r (ξ-(r : ℝ))‖)+
        ‖∑ r ∈ Γ,centeredHighSymbol N (by omega) q₀ Q (conductorMajorant q₀) χ κ β r (ξ+1-(r : ℝ))‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3*(4*((2*C*highMaskConstant*(1+T))*Q^(-η))/(1-(2 : ℝ)^(-(δ-η)))) := by linarith
    _ = _ := by unfold highPowerConstant;ring

end PrimeSquares
