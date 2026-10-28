import PrimeSquares.LocalizedModelContinuity
import PrimeSquares.MajorArcModelError

namespace PrimeSquares

noncomputable def centeredRationalSymbol (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) : C(ℝ, ℂ) := by
  let : NeZero r.den := ⟨r.den_pos.ne'⟩
  exact ⟨localizedAnnularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den)
    (Nat.log2 r.den), localizedAnnularGaussModel_continuous hN _ _ _ _ _ _⟩

theorem centeredRationalSymbol_translate (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    centeredRationalSymbol N hN χ κ β r (ξ-(r : ℝ)) = rationalMajorArcTerm N χ κ β r ξ := by
  rw [rationalMajorArcTerm_eq_localized]
  rfl

theorem centeredRationalSymbol_support (N : ℕ) (hN : 1 ≤ N)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ)
    (x : ℝ) (hx : 1 ≤ |x|) : centeredRationalSymbol N hN χ κ β r x = 0 := by
  have hp : (1 : ℝ) ≤ (16 : ℝ)^(Nat.log2 r.den) := one_le_pow₀ (by norm_num)
  have hb : 1/(16 : ℝ)^(Nat.log2 r.den) ≤ 1 := (div_le_one (by positivity)).mpr hp
  have hz : sourceArcCutoffScale (Nat.log2 r.den) x = 0 := by
    by_contra h
    have hr := sourceArcCutoffScale_radius _ h
    linarith
  simp only [centeredRationalSymbol, ContinuousMap.coe_mk, localizedAnnularGaussModel,
    hz, Complex.ofReal_zero, mul_zero]

end PrimeSquares
