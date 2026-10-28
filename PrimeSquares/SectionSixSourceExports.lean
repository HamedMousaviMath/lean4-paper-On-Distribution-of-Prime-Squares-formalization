import PrimeSquares.SelectedPrimeLowBounds
import PrimeSquares.SelectedPrimeErrorBounds
import PrimeSquares.SelectedPrimeHighBounds

set_option autoImplicit false
open scoped lp
namespace PrimeSquares

theorem source_approximation_all_exponents {c : ℝ} (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
        Real.log Q ≤ δ*Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
          ‖selectedPrimeError D N hN Q‖ ≤
            K*Q^(-(1/2:ℝ))*(1+Real.log N)^(-A) := by
  obtain ⟨δE,hδE,hError⟩ := selectedPrimeError_all_exponents D
  obtain ⟨δR,hδR,hRaw⟩ := selectedPage_raw_source_range D
  refine ⟨min δE δR,lt_min hδE hδR,?_⟩
  intro A hA
  obtain ⟨K,hK,herr⟩ := hError A hA.le
  refine ⟨K,hK,?_⟩
  intro N hn Q hQ hcut hN
  have he : Real.log Q ≤ δE*Real.sqrt (Real.log N) :=
    hcut.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  have hr : Real.log Q ≤ δR*Real.sqrt (Real.log N) :=
    hcut.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
  exact herr N hn Q hQ he (hRaw Q N hQ (by exact_mod_cast hn) hr N le_rfl) hN

theorem source_approximation_function_bound {c : ℝ} (D : PagePrimeSquareDistributionInputs c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 < K ∧
      ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
        Real.log Q ≤ δ*Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
          ∀ f : ℓ²(ℤ,ℂ), ‖selectedPrimeError D N hN Q f‖ ≤
            K*Q^(-(1/2:ℝ))*(1+Real.log N)^(-A)*‖f‖ := by
  obtain ⟨δ,hδ,hAll⟩ := source_approximation_all_exponents D
  refine ⟨δ,hδ,?_⟩
  intro A hA
  obtain ⟨K,hK,hBound⟩ := hAll A hA
  refine ⟨K,hK,?_⟩
  intro N hn Q hQ hcut hN f
  exact ((selectedPrimeError D N hN Q).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (hBound N hn Q hQ hcut hN) (norm_nonneg f))

theorem source_low_local_and_norm :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ {c : ℝ} (D : PagePrimeSquareDistributionInputs c),
        ∀ N : ℕ, 2 ≤ N → ∀ Q : ℝ, 2 ≤ Q →
          Real.log Q ≤ δ*Real.sqrt (Real.log N) → ∀ hN : 1 ≤ N,
            (∀ (f : ℓ¹(ℤ,ℂ)) (x : ℤ), ‖selectedPrimeLow D N hN Q f x‖ ≤
              K*Q*Real.log (2*Q)*sourceLocalMass N f x) ∧
            (∀ f : ℓ¹(ℤ,ℂ), ‖selectedPrimeLow D N hN Q f‖ ≤
              K*((N:ℝ)^2)⁻¹*Q*Real.log (2*Q)*‖f‖) := by
  obtain ⟨δ,hδ,hLow⟩ := selectedPrimeLow_source_bounds
  let K : ℝ := 8*lowSpatialConstant+1
  have hL := lowSpatialConstant_nonneg
  have hK : 0 < K := by dsimp [K];linarith
  have hK8 : 8*lowSpatialConstant ≤ K := by dsimp [K];linarith
  have hK2 : 2*lowSpatialConstant ≤ K := by dsimp [K];linarith
  refine ⟨δ,K,hδ,hK,?_⟩
  intro c D N hn Q hQ hcut hN
  have hb := hLow D N hn Q hQ hcut hN
  have hQ0 : 0 ≤ Q := by linarith
  have hlog : 0 ≤ Real.log (2*Q) := Real.log_nonneg (by linarith)
  constructor
  · intro f x
    apply (hb.2 f x).trans
    gcongr
    exact sourceLocalMass_nonneg hN f x
  · intro f
    apply ((selectedPrimeLow D N hN Q).le_opNorm f).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    apply hb.1.trans
    gcongr

end PrimeSquares
