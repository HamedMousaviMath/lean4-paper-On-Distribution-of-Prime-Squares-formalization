import PrimeSquares.ExceptionalEffectiveCutoff
import PrimeSquares.CenteredHighSymbol

namespace PrimeSquares

theorem centeredHighSymbol_mask_formula (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) (hq₀ : 0 < q₀)
    {Q B : ℝ} (hQ : 0 < Q) (hB : 0 < B) (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den)
    (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (θ : ℝ) :
    letI : NeZero r.den := ⟨r.den_pos.ne'⟩
    centeredHighSymbol N hN q₀ Q B χ κ β r θ=
      (principalSquareSum r.den (r.num : ZMod r.den)*annularHighFactor N 1 (r.den : ℝ) Q θ-
        twistedSquareSum r.den (χ r) (r.num : ZMod r.den)*
          (κ r*annularHighFactor N β (r.den : ℝ) (Q*(q₀ : ℝ)/B) θ))*
        Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ) := by
  have hq₀r : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  change localizedAnnularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den) (Nat.log2 r.den) θ-
    (rationalLowModelTerm N q₀ Q B χ κ β r (θ+(r : ℝ))*Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) θ))=_
  dsimp only [localizedAnnularGaussModel,annularGaussModel,
    rationalLowModelTerm,rationalOrdinaryModelTerm,rationalExceptionalModelTerm,
    ordinaryNarrowCutoff,exceptionalNarrowCutoff,annularHighFactor,annularHighMask]
  simp only [add_sub_cancel_right]
  simp only [exceptional_effective_cutoff hq₀r,exceptional_effective_width hq₀r hQ hB]
  split_ifs <;> push_cast <;> ring

end PrimeSquares
