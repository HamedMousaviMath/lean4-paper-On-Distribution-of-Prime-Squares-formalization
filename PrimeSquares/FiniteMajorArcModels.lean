import PrimeSquares.AnnularGaussModelBounds

/-!
# Finite source model symbols and their exact high-low split

One beta and one family of character/coefficient data are shared by all
centers. For the source application kappa is the exceptional-conductor
indicator and the characters are its induced characters. No existence of
exceptional data or progression estimate is asserted here.
-/

open Finset

namespace PrimeSquares

noncomputable def rationalOrdinaryModelTerm (N : ℕ) (r : ℚ) (ξ : ℝ) : ℂ :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  principalSquareSum r.den (r.num : ZMod r.den) *
    annularOscillatoryModel N 1 (ξ-(r : ℝ))

noncomputable def rationalExceptionalModelTerm (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) : ℂ :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  (-(twistedSquareSum r.den (χ r) (r.num : ZMod r.den) *
    (κ r * annularOscillatoryModel N β (ξ-(r : ℝ)))))

noncomputable def rationalMajorArcTerm (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) : ℂ :=
  (rationalOrdinaryModelTerm N r ξ + rationalExceptionalModelTerm N χ κ β r ξ) *
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)))

noncomputable def finiteMajorArcModel (Γ : Finset ℚ) (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (ξ : ℝ) : ℂ :=
  ∑ r ∈ Γ, rationalMajorArcTerm N χ κ β r ξ

noncomputable def ordinaryNarrowCutoff (N : ℕ) (Q : ℝ) (r : ℚ) (ξ : ℝ) : ℂ :=
  Complex.ofReal (sourceArcCutoff (((r.den : ℝ)*(N : ℝ)^2/Q)*(ξ-(r : ℝ))))

noncomputable def exceptionalNarrowCutoff (N q₀ : ℕ) (Q B₀ : ℝ) (r : ℚ) (ξ : ℝ) : ℂ :=
  Complex.ofReal (sourceArcCutoff ((B₀*((r.den : ℝ)/q₀)*(N : ℝ)^2/Q)*(ξ-(r : ℝ))))

noncomputable def rationalLowModelTerm (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) : ℂ :=
  (if (r.den : ℝ) ≤ Q then
    rationalOrdinaryModelTerm N r ξ * ordinaryNarrowCutoff N Q r ξ else 0) +
  (if (r.den : ℝ)/q₀ ≤ Q/B₀ then
    rationalExceptionalModelTerm N χ κ β r ξ * exceptionalNarrowCutoff N q₀ Q B₀ r ξ else 0)

noncomputable def rationalHighModelTerm (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) : ℂ :=
  (if (r.den : ℝ) ≤ Q then
    rationalOrdinaryModelTerm N r ξ *
      (Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))) -
        ordinaryNarrowCutoff N Q r ξ)
  else rationalOrdinaryModelTerm N r ξ *
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)))) +
  (if (r.den : ℝ)/q₀ ≤ Q/B₀ then
    rationalExceptionalModelTerm N χ κ β r ξ *
      (Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))) -
        exceptionalNarrowCutoff N q₀ Q B₀ r ξ)
  else rationalExceptionalModelTerm N χ κ β r ξ *
    Complex.ofReal (sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ))))

noncomputable def finiteLowModel (Γ : Finset ℚ) (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (ξ : ℝ) : ℂ :=
  ∑ r ∈ Γ, rationalLowModelTerm N q₀ Q B₀ χ κ β r ξ

noncomputable def finiteHighModel (Γ : Finset ℚ) (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (ξ : ℝ) : ℂ :=
  ∑ r ∈ Γ, rationalHighModelTerm N q₀ Q B₀ χ κ β r ξ

noncomputable def finiteMajorArcError (Γ : Finset ℚ) (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (ξ : ℝ) : ℂ :=
  annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) -
    finiteMajorArcModel Γ N χ κ β ξ

theorem rationalMajorArcTerm_eq_localized (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    letI : NeZero r.den := ⟨r.den_pos.ne'⟩
    rationalMajorArcTerm N χ κ β r ξ =
      localizedAnnularGaussModel N r.den (χ r) (κ r) β (r.num : ZMod r.den)
        (Nat.log2 r.den) (ξ-(r : ℝ)) := by
  dsimp [rationalMajorArcTerm, rationalOrdinaryModelTerm, rationalExceptionalModelTerm,
    localizedAnnularGaussModel, annularGaussModel]
  ring

theorem rationalMajorArcTerm_core (N : ℕ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ)
    (hcore : sourceArcCutoffScale (Nat.log2 r.den) (ξ-(r : ℝ)) = 1) :
    rationalMajorArcTerm N χ κ β r ξ =
      rationalOrdinaryModelTerm N r ξ + rationalExceptionalModelTerm N χ κ β r ξ := by
  simp only [rationalMajorArcTerm, hcore, Complex.ofReal_one, mul_one]

theorem rationalModel_low_add_high (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (r : ℚ) (ξ : ℝ) :
    rationalLowModelTerm N q₀ Q B₀ χ κ β r ξ +
      rationalHighModelTerm N q₀ Q B₀ χ κ β r ξ =
      rationalMajorArcTerm N χ κ β r ξ := by
  classical
  unfold rationalLowModelTerm rationalHighModelTerm rationalMajorArcTerm
  split_ifs <;> ring

theorem finiteModel_low_add_high (Γ : Finset ℚ) (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (ξ : ℝ) :
    finiteLowModel Γ N q₀ Q B₀ χ κ β ξ +
      finiteHighModel Γ N q₀ Q B₀ χ κ β ξ = finiteMajorArcModel Γ N χ κ β ξ := by
  simp only [finiteLowModel, finiteHighModel, finiteMajorArcModel, ← sum_add_distrib,
    rationalModel_low_add_high]

theorem annularSymbol_finite_low_high_error (Γ : Finset ℚ) (N q₀ : ℕ) (Q B₀ : ℝ)
    (χ : ∀ r : ℚ, DirichletCharacter ℂ r.den) (κ : ℚ → ℂ) (β : ℝ) (ξ : ℝ) :
    annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle) =
      finiteLowModel Γ N q₀ Q B₀ χ κ β ξ +
      finiteHighModel Γ N q₀ Q B₀ χ κ β ξ +
      finiteMajorArcError Γ N χ κ β ξ := by
  rw [finiteModel_low_add_high, finiteMajorArcError]
  ring

end PrimeSquares
