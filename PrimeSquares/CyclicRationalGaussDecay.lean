import PrimeSquares.IWMultiplierInterface
import PrimeSquares.RationalGaussCoefficientBounds

set_option autoImplicit false
namespace PrimeSquares

theorem cyclicRationalCoefficient_eq_reduced {P : ℕ} [NeZero P]
    (ν : ZMod P → ℂ) (r : ℚ) [NeZero r.den] (hd : r.den∣P) :
    cyclicRationalCoefficient P ν r=cyclicReducedFourier hd ν (r.num : ZMod r.den) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  simpa only [cyclicRationalCoefficient,Rat.cast_def] using cyclicRationalFourier_eq_reduced hd ν r.num

theorem cyclicRationalCoefficient_principal {P : ℕ} [NeZero P]
    (r : ℚ) (hd : r.den∣P) :
    cyclicRationalCoefficient P (cyclicSquareMeasure P 1) r=rationalPrincipalGauss r := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  rw [cyclicRationalCoefficient_eq_reduced _ r hd,cyclicReducedPrincipalSquare]
  rfl

theorem cyclicRationalCoefficient_changeLevel {P : ℕ} [NeZero P]
    (r : ℚ) (hd : r.den∣P) (χ : DirichletCharacter ℂ r.den) :
    cyclicRationalCoefficient P (cyclicSquareMeasure P (DirichletCharacter.changeLevel hd χ)) r=
      rationalTwistedGauss r χ := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  rw [cyclicRationalCoefficient_eq_reduced _ r hd,cyclicReducedSquare_changeLevel]
  rfl

theorem cyclicRationalCoefficient_conductor_zero {P : ℕ} [NeZero P]
    (χ : DirichletCharacter ℂ P) (r : ℚ) (hd : r.den∣P) (hc : ¬χ.conductor∣r.den) :
    cyclicRationalCoefficient P (cyclicSquareMeasure P χ) r=0 := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  rw [cyclicRationalCoefficient_eq_reduced _ r hd,cyclicReducedSquare_conductor_zero hd χ hc]

theorem cyclicRationalSquare_uniform_decay {δ : ℝ} (hδ : δ<1/2) :
    ∃ A : ℝ,0<A ∧ ∀ (P : ℕ) [NeZero P] (χ : DirichletCharacter ℂ P) (r : ℚ),r.den∣P →
      ‖cyclicRationalCoefficient P (cyclicSquareMeasure P χ) r‖≤A*(r.den : ℝ)^(-δ) := by
  classical
  obtain ⟨A,hA,hGauss⟩ := rationalGauss_uniform_decay hδ
  refine ⟨A,hA,?_⟩
  intro P inst χ r hd
  by_cases hc : χ.conductor∣r.den
  · obtain ⟨_,χq,he⟩ := (χ.mem_conductorSet_iff_conductor_dvd hd).mpr hc
    rw [he,cyclicRationalCoefficient_changeLevel]
    exact (hGauss r).2 χq
  · rw [cyclicRationalCoefficient_conductor_zero χ r hd hc,norm_zero]
    positivity

end PrimeSquares
