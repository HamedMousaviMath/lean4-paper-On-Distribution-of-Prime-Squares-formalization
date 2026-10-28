import PrimeSquares.TwistedCollarUniformMaximum
import PrimeSquares.CenteredHighMaskFormula

namespace PrimeSquares

theorem centeredHighSymbol_ordinary_collar (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (β : ℝ) (r : ℚ) (hr : (r.den : ℝ) ≤ Q) :
    centeredHighSymbol N hN q₀ Q B χ (fun _ => 0) β r=
      rationalPrincipalGauss r • annularCollarSymbol N hN 1 (r.den : ℝ) Q (Nat.log2 r.den) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  ext θ
  rw [centeredHighSymbol_mask_formula N hN q₀ hq₀ hQ hB χ (fun _ => 0) β r θ]
  simp only [zero_mul,mul_zero,sub_zero,annularHighFactor_eq_collar hr,ContinuousMap.smul_apply,smul_eq_mul]
  change principalSquareSum r.den (r.num : ZMod r.den)*annularCollarFactor N 1 (r.den : ℝ) Q θ*
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ)=
    principalSquareSum r.den (r.num : ZMod r.den)*(annularCollarFactor N 1 (r.den : ℝ) Q θ*
      Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ))
  ring

end PrimeSquares
