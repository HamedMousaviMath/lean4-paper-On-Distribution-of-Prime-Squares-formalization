import PrimeSquares.UniformPageProgressionRange
import PrimeSquares.CorrectedMinorArcInput
import PrimeSquares.SourceScaleFourthPower

set_option autoImplicit false
open Filter
namespace PrimeSquares

/-- The separate, independent Ren and Ghosh quadratic prime-sum estimates.
Only their raw brackets and rational-approximation hypotheses occur here. -/
structure UniformRenGhoshInputs where
  renConstant : ℝ
  ghoshConstant : ℝ
  logarithmicPower : ℝ
  ren_nonneg : 0 ≤ renConstant
  ghosh_nonneg : 0 ≤ ghoshConstant
  power_nonneg : 0 ≤ logarithmicPower
  startingScale : ℕ
  ren : ∀ N : ℕ, startingScale ≤ N → ∀ ξ : ℝ,
    RenBalancedInput N ξ renConstant logarithmicPower
  ghosh : ∀ N : ℕ, startingScale ≤ N → ∀ ξ : ℝ,
    GhoshBalancedInput N ξ ghoshConstant

/-- The two literal conclusions of the corrected source lemma, for one datum.
The minor predicate ranges over every real rational lift, so its forbidden
arcs include every integer translate of every reduced rational center. -/
def CorrectedPrimeSquareInputConclusion (N : ℕ) (Q P C B d : ℝ)
    (E : Option PageZeroDatum) : Prop :=
  (∀ (q : ℕ) [NeZero q] (a : ℤ) (θ : ℝ),
    (q : ℝ) ≤ (sourceMajorArcScale N Q)^(11/10 : ℝ) →
    |θ| ≤ sourceMajorArcScale N Q/((q : ℝ)*(N : ℝ)^2) →
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
        ((((a : ℝ)/q : ℝ) : PrimeCircle)+(θ : PrimeCircle))-
      (principalSquareSum q (a : ZMod q)*annularOscillatoryModel N 1 θ-
        twistedSquareSum q (pageModulusCharacter E q) (a : ZMod q)*
          (pageModulusSelector E q*annularOscillatoryModel N (optionPageBeta E) θ))‖ ≤
      (4+(2+4*Real.pi)*P)/(sourceMajorArcScale N Q)^5) ∧
  (∀ ξ : ℝ, OutsideSourceMajorArcs N (sourceMajorArcScale N Q) ξ →
    ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt (ξ : PrimeCircle)‖ ≤
      (renSourceConstant C+ghoshSourceConstant B)*(Real.log N)^d*
        (sourceMajorArcScale N Q)^(-(1/4 : ℝ)))

theorem pageModulusSelector_none (q : ℕ) : pageModulusSelector none q = 0 := by
  simp [pageModulusSelector]

theorem pageModulusSelector_some (F : PageZeroDatum) (q : ℕ) :
    pageModulusSelector (some F) q = if F.conductor ∣ q then 1 else 0 := by
  simp only [pageModulusSelector, Option.isSome_some, true_and, optionPageConductor]

/-- The full corrected prime-square input, with one datum per N before Q.
All range, partial-summation, effective-denominator and minor-arc deductions
are proved. Only the explicitly named independent progression and
exponential-sum inputs remain hypotheses. -/
theorem source_corrected_prime_square_input {pc : ℝ}
    (D : UniformPageProgressionInputs pc) (H : UniformRenGhoshInputs) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∃ E : Option PageZeroDatum,
      (∀ F, E = some F →
        (F.conductor : ℝ) ≤ Real.exp (D.modulusConstant*Real.sqrt (Real.log N)) ∧
        1-pc/Real.log (Real.exp (D.modulusConstant*Real.sqrt (Real.log N))) < F.beta) ∧
      0 < optionPageBeta E ∧ optionPageBeta E ≤ 1 ∧
      ∀ Q : ℝ, 1 ≤ Q →
        Real.log Q ≤ (min ((min D.decayConstant D.modulusConstant)/7) 1/8)*
          Real.sqrt (Real.log N) →
        CorrectedPrimeSquareInputConclusion N Q D.prefixConstant
          H.renConstant H.ghoshConstant H.logarithmicPower E := by
  let c := min D.decayConstant D.modulusConstant
  have hc : 0 < c := lt_min D.decay_pos D.modulus_pos
  obtain ⟨N₁,hN₁,hparam⟩ := sourceMajorArc_parameter_threshold hc
  obtain ⟨N₂,hN₂,hfourth⟩ := sourceMajorArcScale_uniform_fourth_power hc
  have he := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp he
  let N₀ := max (max D.startingScale H.startingScale) (max N₁ (max N₂ N₃))
  have hnD : D.startingScale ≤ N₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hnH : H.startingScale ≤ N₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hn1 : N₁ ≤ N₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hn2 : N₂ ≤ N₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hn3 : N₃ ≤ N₀ := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨N₀,hN₂.trans hn2,?_⟩
  intro N hN
  obtain ⟨E,hPage,hprefix⟩ := D.raw_data N (hnD.trans hN)
  refine ⟨E,hPage,optionPageBeta_pos E,optionPageBeta_le_one E,?_⟩
  intro Q hQ hQl
  obtain ⟨hR,hlog,hbudget,hdecay⟩ := hparam N (hn1.trans hN) Q hQ hQl
  constructor
  · intro q inst a θ hq hθ
    have hden := extended_major_denominator_in_Page_range
      (sourceMajorArcScale_pos N Q) (Real.sqrt_nonneg _) D.modulus_pos.le
      (min_le_right D.decayConstant D.modulusConstant) hdecay
    have hdecay' : 7*Real.log (sourceMajorArcScale N Q) ≤
        D.decayConstant*Real.sqrt (Real.log N) :=
      hdecay.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    exact annularMangoldt_majorArc_inverse_fifth
      (hN₁.trans (hn1.trans hN)) (pageModulusCharacter E q) (pageModulusSelector E q)
      (optionPageBeta_pos E) a θ hR D.prefix_nonneg hq hθ hlog hbudget hdecay'
      (hprefix q (hq.trans hden))
  · intro ξ hout
    exact annularMangoldt_outside_major_quarter_bound (hN₂.trans (hn2.trans hN))
      H.ren_nonneg H.ghosh_nonneg H.power_nonneg hR (hfourth N (hn2.trans hN) Q hQ hQl)
      (hN₃ N (hn3.trans hN)) hout (H.ren N (hnH.trans hN) ξ)
      (H.ghosh N (hnH.trans hN) ξ)

end PrimeSquares
