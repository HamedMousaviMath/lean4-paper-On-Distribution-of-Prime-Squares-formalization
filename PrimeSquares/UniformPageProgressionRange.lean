import PrimeSquares.PageDistributionInputs
import PrimeSquares.SourceRangeMajorArc

set_option autoImplicit false
namespace PrimeSquares

noncomputable def pageModulusCharacter (E : Option PageZeroDatum) (q : ℕ) :
    DirichletCharacter ℂ q :=
  if h : optionPageConductor 1 E ∣ q then
    DirichletCharacter.changeLevel h (optionPageCharacter 1 E) else 1

noncomputable def pageModulusSelector (E : Option PageZeroDatum) (q : ℕ) : ℂ :=
  if E.isSome = true ∧ optionPageConductor 1 E ∣ q then 1 else 0

/-- A general uniform prime-progression theorem at one fixed Page level for
each N. The same optional genuine primitive zero is used for every modulus
and every real endpoint in [N/2,N]. This independent input contains no
quadratic phase, major-arc conclusion, decomposition or maximal estimate.
Its existence, including the fixed-level analytic bridge, is unproved. -/
structure UniformPageProgressionInputs (pageConstant : ℝ) where
  prefixConstant : ℝ
  modulusConstant : ℝ
  decayConstant : ℝ
  prefix_nonneg : 0 ≤ prefixConstant
  modulus_pos : 0 < modulusConstant
  decay_pos : 0 < decayConstant
  startingScale : ℕ
  raw_data : ∀ N : ℕ, startingScale ≤ N → ∃ E : Option PageZeroDatum,
    (∀ F, E = some F →
      (F.conductor : ℝ) ≤ Real.exp (modulusConstant * Real.sqrt (Real.log N)) ∧
      1-pageConstant/Real.log (Real.exp (modulusConstant * Real.sqrt (Real.log N))) < F.beta) ∧
    ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ Real.exp (modulusConstant * Real.sqrt (Real.log N)) →
      ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t -
        progressionPowerModel q
          (pageModulusSelector E q * pageModulusCharacter E q u) (optionPageBeta E) t‖ ≤
        (N : ℝ)*(prefixConstant*Real.exp (-decayConstant*Real.sqrt (Real.log N)))

theorem optionPageBeta_pos (E : Option PageZeroDatum) : 0 < optionPageBeta E := by
  cases E with
  | none => norm_num [optionPageBeta]
  | some F => exact F.beta_pos

theorem pageModulusCharacter_rational (E : Option PageZeroDatum) (r : ℚ) :
    pageModulusCharacter E r.den =
      sourceInducedCharacter (optionPageConductor 1 E) (optionPageCharacter 1 E) r := rfl

theorem pageModulusSelector_rational (E : Option PageZeroDatum) (r : ℚ) :
    pageModulusSelector E r.den =
      sourceExceptionalSelector (optionPageConductor 1 E) E.isSome r := rfl

theorem extended_major_denominator_in_Page_range {R η c L : ℝ}
    (hR : 0 < R) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hcη : c ≤ η) (hlog : 7*Real.log R ≤ c*L) :
    R^(11/10 : ℝ) ≤ Real.exp (η*L) := by
  rw [Real.rpow_def_of_pos hR, Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_right hcη hL
  have hηL : 0 ≤ η*L := mul_nonneg hη hL
  nlinarith

/-- The optional Page datum is chosen before Q, the modulus and the phase. -/
theorem uniformPage_extended_major_arc {pc : ℝ} (D : UniformPageProgressionInputs pc) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ E : Option PageZeroDatum,
      ∀ Q : ℝ, 1 ≤ Q →
        Real.log Q ≤ (min ((min D.decayConstant D.modulusConstant)/7) 1/8)*
          Real.sqrt (Real.log N) →
      ∀ (q : ℕ) [NeZero q] (a : ℤ) (θ : ℝ),
        (q : ℝ) ≤ (sourceMajorArcScale N Q)^(11/10 : ℝ) →
        |θ| ≤ sourceMajorArcScale N Q/((q : ℝ)*(N : ℝ)^2) →
      ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
          ((((a : ℝ)/q : ℝ) : PrimeCircle)+(θ : PrimeCircle))-
        (principalSquareSum q (a : ZMod q)*annularOscillatoryModel N 1 θ-
          twistedSquareSum q (pageModulusCharacter E q) (a : ZMod q)*
            (pageModulusSelector E q*annularOscillatoryModel N (optionPageBeta E) θ))‖ ≤
        (4+(2+4*Real.pi)*D.prefixConstant)/(sourceMajorArcScale N Q)^5 := by
  let c := min D.decayConstant D.modulusConstant
  have hc : 0 < c := lt_min D.decay_pos D.modulus_pos
  obtain ⟨N₁,hN₁,hparam⟩ := sourceMajorArc_parameter_threshold hc
  refine ⟨max D.startingScale N₁,?_⟩
  intro N hN
  obtain ⟨E,_,hprefix⟩ := D.raw_data N ((le_max_left _ _).trans hN)
  refine ⟨E,?_⟩
  intro Q hQ hQl q inst a θ hq hθ
  obtain ⟨hR,hlog,hbudget,hdecay⟩ := hparam N ((le_max_right _ _).trans hN) Q hQ hQl
  have hden := extended_major_denominator_in_Page_range
    (sourceMajorArcScale_pos N Q) (Real.sqrt_nonneg _) D.modulus_pos.le
    (min_le_right D.decayConstant D.modulusConstant) hdecay
  have hdecay' : 7*Real.log (sourceMajorArcScale N Q) ≤
      D.decayConstant*Real.sqrt (Real.log N) :=
    hdecay.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  exact annularMangoldt_majorArc_inverse_fifth
    (hN₁.trans ((le_max_right _ _).trans hN)) (pageModulusCharacter E q)
    (pageModulusSelector E q) (optionPageBeta_pos E) a θ hR D.prefix_nonneg hq hθ
    hlog hbudget hdecay' (hprefix q (hq.trans hden))

end PrimeSquares
