import PrimeSquares.PureAnnularCollar

namespace PrimeSquares

theorem annularCollar_first_scale (M : ℕ) (q Q θ : ℝ)
    (h : ∃ j : ℕ,annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ ≠ 0) :
    ∃ i : ℕ,annularCollarMask ((((2 : ℕ)^i*M : ℕ) : ℝ)) q Q θ ≠ 0 ∧
      ∀ j : ℕ,j < i → annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ=0 := by
  classical
  refine ⟨Nat.find h,Nat.find_spec h,?_⟩
  intro j hj
  exact not_not.mp (Nat.find_min h hj)

theorem annularCollar_no_onset (M : ℕ) (q Q θ : ℝ)
    (h : ¬∃ j : ℕ,annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ ≠ 0) :
    ∀ j : ℕ,annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ=0 := by
  simpa only [not_exists,not_not] using h

end PrimeSquares
