import PrimeSquares.SeparatedSmoothCircleSupports
import PrimeSquares.FiniteDisjointSymbolBound
namespace PrimeSquares
theorem separatedSmoothCircleFamily_norm (Γ : Finset ℚ) {δ a : ℝ} (ha : 4 ≤ a)
    (hsep : PeriodicFrequencySeparated Γ δ) (hw : 2*(1/a)<δ) (j : ℕ) :
    ‖unweightedSmoothCircleFamily Γ a ha j‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  refine finite_disjoint_symbol_bound Γ
    (fun r => circleSmoothCutoff (smoothCircleScale a j) (smoothCircleScale_one ha j) r) ?_
    (by norm_num) ?_
  · intro r hr t ht hne θ
    apply separatedSmoothCircle_disjoint Γ (smoothCircleScale_one ha j) hsep _ hr ht hne θ
    have hi : 1/smoothCircleScale a j ≤ 1/a :=
      one_div_le_one_div_of_le (by linarith) (smoothCircleScale_ge (by linarith) j)
    linarith
  · intro r hr θ
    exact circleSmoothCutoff_pointwise_norm (smoothCircleScale_one ha j) (smoothCircleScale_four ha j) r θ
end PrimeSquares
