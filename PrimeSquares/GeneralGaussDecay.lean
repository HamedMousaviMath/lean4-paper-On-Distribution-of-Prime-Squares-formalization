import PrimeSquares.TwistedGaussBound
import PrimeSquares.RationalNumeratorUnits

namespace PrimeSquares

theorem gauss_pair_arbitrary_decay {δ : ℝ} (hδ : δ < 1/2) :
    ∃ C : ℝ,0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q),
      IsUnit a → ‖principalSquareSum q a‖ ≤ C*(q : ℝ)^(-δ) ∧
        ‖twistedSquareSum q χ a‖ ≤ C*(q : ℝ)^(-δ) := by
  obtain ⟨C,hC,h⟩ := twistedSquareSum_uniform_bound (1/2-δ) (sub_pos.mpr hδ)
  refine ⟨C,hC,?_⟩
  intro q inst χ a ha
  have he : -(1/2 : ℝ)+(1/2-δ)=-δ := by ring
  exact ⟨by simpa only [twistedSquareSum_principal,he] using h q 1 a ha,
    by simpa only [he] using h q χ a ha⟩

end PrimeSquares
