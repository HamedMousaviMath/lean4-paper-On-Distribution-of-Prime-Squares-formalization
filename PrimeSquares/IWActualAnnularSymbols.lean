import PrimeSquares.IWCommonCutoffTails
import PrimeSquares.WeightedAnnularBlockBounds

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem annularCutoffSymbol_norm_half {N : ℕ} (hN : 2≤N) {β : ℝ} (hβ : β≤1)
    (a x : ℝ) : ‖annularCutoffSymbol N (by omega) β a x‖≤1/2 := by
  change ‖annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoff (a*x))‖≤1/2
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sourceArcCutoff_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (sourceArcCutoff_le_one _) (norm_nonneg _)).trans
    (by simpa only [mul_one] using annularOscillatoryModel_norm_half hN hβ x)

noncomputable def annularBoundedSymbol (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : β≤1)
    (a : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (annularCutoffSymbol N (by omega) β a)
    (annularCutoffSymbol N (by omega) β a).continuous (1/2) (annularCutoffSymbol_norm_half hN hβ a)

theorem annularBoundedSymbol_apply (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : β≤1) (a x : ℝ) :
    annularBoundedSymbol N hN β hβ a x=
      annularOscillatoryModel N β x*Complex.ofReal (sourceArcCutoff (a*x)) := rfl

theorem annularBoundedSymbol_support (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : β≤1)
    {a : ℝ} (ha : 2≤a) (x : ℝ) (hx : 1≤|x|) : annularBoundedSymbol N hN β hβ a x=0 :=
  annularCutoffSymbol_support N (by omega) β ha x hx

theorem iwCyclicSymbol_annular (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P → ℂ) (N : ℕ) (hN : 2≤N) (β : ℝ) (hβ : β≤1)
    (a : ℝ) (ha : 2≤a) :
    iwCyclicSymbol S k P ν (annularBoundedSymbol N hN β hβ a)
      (annularBoundedSymbol_support N hN β hβ ha)=
      weightedWidthAnnularBlock (iwFrequencySet S k) N (by omega) β a ha
        (cyclicRationalCoefficient P ν) := rfl

noncomputable def rationalInducedSquareCoefficient (q : ℕ) (χ : DirichletCharacter ℂ q)
    (r : ℚ) : ℂ :=
  if q∣r.den then rationalTwistedGauss r (sourceInducedCharacter q χ r) else 0

theorem cyclicRationalCoefficient_primitive_induced {q P : ℕ} [NeZero P]
    (hqP : q∣P) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (r : ℚ) (hr : r.den∣P) :
    cyclicRationalCoefficient P (cyclicSquareMeasure P (DirichletCharacter.changeLevel hqP χ)) r=
      rationalInducedSquareCoefficient q χ r := by
  classical
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  by_cases hd : q∣r.den
  · have he : DirichletCharacter.changeLevel hqP χ=
        DirichletCharacter.changeLevel hr (sourceInducedCharacter q χ r) := by
      rw [sourceInducedCharacter_of_dvd q χ r hd]
      exact χ.changeLevel_trans hd hr
    rw [he,cyclicRationalCoefficient_changeLevel]
    simp only [rationalInducedSquareCoefficient,ite_eq_left hd]
  · have hcond : (DirichletCharacter.changeLevel hqP χ).conductor=q :=
      (χ.conductor_changeLevel hqP).trans hχ
    rw [cyclicRationalCoefficient_conductor_zero _ r hr (by simpa only [hcond] using hd)]
    simp only [rationalInducedSquareCoefficient,ite_eq_right hd]

theorem iw_principal_width_symbol {C ρ : ℝ} {k Q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (N : ℕ) (hN : 1≤N) (β a : ℝ) (ha : 2≤a) :
    weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β a ha
      (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period 1))=
      weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β a ha rationalPrincipalGauss := by
  unfold weightedWidthAnnularBlock
  apply sum_congr rfl
  intro r hr
  rw [cyclicRationalCoefficient_principal r (d.periodic r hr)]

theorem iw_induced_width_symbol {C ρ : ℝ} {k Q q : ℕ}
    (d : TaoArcConstructionData C ρ k Q) [NeZero d.period]
    (hqP : q∣d.period) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (N : ℕ) (hN : 1≤N) (β a : ℝ) (ha : 2≤a) :
    weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β a ha
      (cyclicRationalCoefficient d.period (cyclicSquareMeasure d.period (DirichletCharacter.changeLevel hqP χ)))=
      weightedWidthAnnularBlock (iwFrequencySet d.S k) N hN β a ha
        (rationalInducedSquareCoefficient q χ) := by
  unfold weightedWidthAnnularBlock
  apply sum_congr rfl
  intro r hr
  rw [cyclicRationalCoefficient_primitive_induced hqP χ hχ r (d.periodic r hr)]

end PrimeSquares
