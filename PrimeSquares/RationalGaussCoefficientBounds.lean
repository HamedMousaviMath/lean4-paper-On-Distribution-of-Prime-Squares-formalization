import PrimeSquares.CompleteRationalCollarMaximum
import PrimeSquares.GeneralGaussDecay

namespace PrimeSquares

noncomputable def rationalPrincipalGauss (r : ℚ) : ℂ :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  principalSquareSum r.den (r.num : ZMod r.den)

noncomputable def rationalTwistedGauss (r : ℚ) (χ : DirichletCharacter ℂ r.den) : ℂ :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  twistedSquareSum r.den χ (r.num : ZMod r.den)

theorem rationalGauss_uniform_decay {δ : ℝ} (hδ : δ < 1/2) :
    ∃ C : ℝ,0 < C ∧ ∀ r : ℚ,‖rationalPrincipalGauss r‖ ≤ C*(r.den : ℝ)^(-δ) ∧
      ∀ χ : DirichletCharacter ℂ r.den,‖rationalTwistedGauss r χ‖ ≤ C*(r.den : ℝ)^(-δ) := by
  obtain ⟨C,hC,h⟩ := gauss_pair_arbitrary_decay hδ
  refine ⟨C,hC,?_⟩
  intro r
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  exact ⟨(h r.den 1 (r.num : ZMod r.den) ha).1,fun χ => (h r.den χ (r.num : ZMod r.den) ha).2⟩

theorem rationalTwistedGauss_principal (r : ℚ) : rationalTwistedGauss r 1=rationalPrincipalGauss r := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  exact twistedSquareSum_principal r.den (r.num : ZMod r.den)

end PrimeSquares
