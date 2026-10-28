import PrimeSquares.ExponentialMajorArcBudget
import PrimeSquares.MajorArcParameters

open Filter

namespace PrimeSquares

theorem sourceMajorArc_parameter_threshold {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8) * Real.sqrt (Real.log N) →
      1 ≤ sourceMajorArcScale N Q ∧
      Real.log (sourceMajorArcScale N Q) ≤ Real.log N ∧
      (sourceMajorArcScale N Q)^5 * Real.log N ≤ Real.sqrt N ∧
      7 * Real.log (sourceMajorArcScale N Q) ≤ c * Real.sqrt (Real.log N) := by
  have hp := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually (eventually_sourceMajorArc_conditions hc)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hp
  refine ⟨max N₀ 1, le_max_right _ _, ?_⟩
  intro N hN
  exact hN₀ N ((le_max_left N₀ 1).trans hN)

theorem sourceMajorArc_uniform_inverse_fifth {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8) * Real.sqrt (Real.log N) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (κ : ℂ)
        (β : ℝ), 0 < β → ∀ (a : ℤ) (θ C : ℝ), 0 ≤ C →
      (q : ℝ) ≤ (sourceMajorArcScale N Q)^(11/10 : ℝ) →
      |θ| ≤ sourceMajorArcScale N Q / ((q : ℝ) * (N : ℝ)^2) →
      (∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
        ‖progressionMangoldtPrefix q u t - progressionPowerModel q (κ * χ u) β t‖ ≤
          (N : ℝ) * (C * Real.exp (-c * Real.sqrt (Real.log N)))) →
      ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
          ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
        (principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ -
          twistedSquareSum q χ (a : ZMod q) * (κ * annularOscillatoryModel N β θ))‖ ≤
        (4 + (2 + 4 * Real.pi) * C) / (sourceMajorArcScale N Q)^5 := by
  obtain ⟨N₀, hN₀, hp⟩ := sourceMajorArc_parameter_threshold hc
  refine ⟨N₀, ?_⟩
  intro N hN Q hQ hQlog q inst χ κ β hβ a θ C hC hq hθ hprefix
  obtain ⟨hR, hlog, hbudget, hexp⟩ := hp N hN Q hQ hQlog
  exact annularMangoldt_majorArc_inverse_fifth (hN₀.trans hN) χ κ hβ a θ hR hC
    hq hθ hlog hbudget hexp hprefix

theorem sourceMajorArc_uniform_ordinary {c : ℝ} (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℝ, 1 ≤ Q →
      Real.log Q ≤ (min (c/7) 1 / 8) * Real.sqrt (Real.log N) →
      ∀ (q : ℕ) [NeZero q] (a : ℤ) (θ C : ℝ), 0 ≤ C →
      (q : ℝ) ≤ (sourceMajorArcScale N Q)^(11/10 : ℝ) →
      |θ| ≤ sourceMajorArcScale N Q / ((q : ℝ) * (N : ℝ)^2) →
      (∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
        ‖progressionMangoldtPrefix q u t - (q.totient : ℂ)⁻¹ * (t : ℂ)‖ ≤
          (N : ℝ) * (C * Real.exp (-c * Real.sqrt (Real.log N)))) →
      ‖annularWeightedSquareAverageSymbol N ArithmeticFunction.vonMangoldt
          ((((a : ℝ)/q : ℝ) : PrimeCircle) + (θ : PrimeCircle)) -
          principalSquareSum q (a : ZMod q) * annularOscillatoryModel N 1 θ‖ ≤
        (4 + (2 + 4 * Real.pi) * C) / (sourceMajorArcScale N Q)^5 := by
  obtain ⟨N₀, hp⟩ := sourceMajorArc_uniform_inverse_fifth hc
  refine ⟨N₀, ?_⟩
  intro N hN Q hQ hQlog q inst a θ C hC hq hθ hprefix
  have he : ∀ u : (ZMod q)ˣ, ∀ t ∈ Set.Icc ((N : ℝ)/2) N,
      ‖progressionMangoldtPrefix q u t -
        progressionPowerModel q (0 * (1 : DirichletCharacter ℂ q) u) 1 t‖ ≤
        (N : ℝ) * (C * Real.exp (-c * Real.sqrt (Real.log N))) := by
    intro u t ht
    simpa only [zero_mul, progressionPowerModel_zero] using hprefix u t ht
  have h := hp N hN Q hQ hQlog q (1 : DirichletCharacter ℂ q) 0 1 (by norm_num)
    a θ C hC hq hθ he
  simpa only [zero_mul, mul_zero, sub_zero] using h

end PrimeSquares
