import PrimeSquares.ConductorEstimates

namespace PrimeSquares

noncomputable def inducedIntegerCorrelation (q₀ : ℕ) [NeZero q₀] (χ₀ : DirichletCharacter ℂ q₀)
    (d : ℕ) (x : ℤ) : ℂ :=
  if hd : d=0 then 0 else
    letI : NeZero d := ⟨hd⟩
    twistedSquareCorrelation (q₀*d) (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) (x : ZMod (q₀*d))

theorem inducedIntegerCorrelation_eq (q₀ d : ℕ) [NeZero q₀] [NeZero d]
    (χ₀ : DirichletCharacter ℂ q₀) (x : ℤ) :
    inducedIntegerCorrelation q₀ χ₀ d x=
      twistedSquareCorrelation (q₀*d) (DirichletCharacter.changeLevel (Nat.dvd_mul_right q₀ d) χ₀) (x : ZMod (q₀*d)) := by
  simp only [inducedIntegerCorrelation,dite_eq_right (NeZero.ne d)]

theorem inducedIntegerCorrelation_bound (q₀ d : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) (hχ : χ₀.IsQuadratic) (x : ℤ) :
    ‖inducedIntegerCorrelation q₀ χ₀ d x‖ ≤ conductorMajorant q₀*conductorCorrelationProduct d := by
  by_cases hd : d=0
  · subst d
    have he : inducedIntegerCorrelation q₀ χ₀ 0 x=0 := by simp [inducedIntegerCorrelation]
    rw [he,norm_zero]
    exact mul_nonneg (le_trans (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀)))
      (le_trans (by norm_num) (conductorCorrelationProduct_one_le 0))
  · have : NeZero d := ⟨hd⟩
    rw [inducedIntegerCorrelation_eq]
    exact induced_twistedCorrelation_conductor_bound q₀ d χ₀ hχ _

end PrimeSquares
