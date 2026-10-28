import PrimeSquares.CenteredRationalSymbol
import PrimeSquares.LocalizedAnnularSource
import PrimeSquares.RationalGaussCoefficientBounds
namespace PrimeSquares
noncomputable def rationalExceptionalCoefficient
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (r : ℚ) : ℂ :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  twistedSquareSum r.den (χ r) (r.num : ZMod r.den)*κ r
theorem centeredRationalSymbol_annular_decomposition (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) :
    centeredRationalSymbol N hN χ κ β r=
      rationalPrincipalGauss r • localizedAnnularSource N hN 1 (Nat.log2 r.den)-
        rationalExceptionalCoefficient χ κ r • localizedAnnularSource N hN β (Nat.log2 r.den) := by
  ext x
  simp only [centeredRationalSymbol,ContinuousMap.coe_mk,localizedAnnularGaussModel,
    annularGaussModel,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,
    rationalPrincipalGauss,rationalExceptionalCoefficient,localizedAnnularSource,annularCutoffSymbol,
    sourceArcCutoffScale]
  ring
end PrimeSquares
