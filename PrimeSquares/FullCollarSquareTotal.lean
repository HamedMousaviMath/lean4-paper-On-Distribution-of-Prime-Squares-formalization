import PrimeSquares.FullCollarSquareSummability

namespace PrimeSquares

theorem collarFactor_square_total {M : ℕ} (hM : 2 ≤ M) (β : ℕ → ℝ)
    (hβ0 : ∀ j,0 ≤ β j) (hβ1 : ∀ j,β j ≤ 1) {q Q : ℝ} (hq : 0 < q) (hQ : 0 < Q) (θ : ℝ) :
    (∑' j : ℕ,‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2) ≤
      (16/15 : ℝ)*(4*q/(Real.pi*Q))^2 := by
  classical
  have hs := collarFactor_square_summable hM β hβ0 hβ1 hq hQ θ
  by_cases h : ∃ j : ℕ,annularCollarMask ((((2 : ℕ)^j*M : ℕ) : ℝ)) q Q θ ≠ 0
  · obtain ⟨i,hi,hpre⟩ := annularCollar_first_scale M q Q θ h
    have hp : (∑ j ∈ Finset.range i,‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2)=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [annularCollarFactor_zero_of_mask _ _ _ _ _ (hpre j (Finset.mem_range.mp hj)),norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    rw [←hs.sum_add_tsum_nat_add i,hp,zero_add]
    simpa only [Nat.add_comm] using collarFactor_tail_square_total hM β hβ0 hβ1 hq hQ i hi
  · have hz := annularCollar_no_onset M q Q θ h
    have he : (fun j : ℕ => ‖annularCollarFactor ((2 : ℕ)^j*M) (β j) q Q θ‖^2)=fun _ => 0 := by
      funext j
      rw [annularCollarFactor_zero_of_mask _ _ _ _ _ (hz j),norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    rw [he,tsum_zero]
    positivity

end PrimeSquares
