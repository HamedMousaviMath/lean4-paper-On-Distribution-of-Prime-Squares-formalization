import PrimeSquares.RealExceptionalLowModel

namespace PrimeSquares

theorem exceptionalUnitSum_filter (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (q : ℕ) [NeZero q] :
    denominatorUnitSum q (fun r => if (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
      then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r else 0)=
      if (q : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
        then realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β q else 0 := by
  classical
  unfold realExceptionalCircleTerm
  rw [denominatorUnitSum_pos,denominatorUnitSum_pos]
  simp only [unitRational_den]
  by_cases hp : (q : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
  · simp only [ite_eq_left hp]
  · simp only [ite_eq_right hp,Finset.sum_const_zero]

theorem exceptionalUnitSum_divisor_filter (N : ℕ) (hN : 1 ≤ N) (q₀ : ℕ) [NeZero q₀]
    (χ₀ : DirichletCharacter ℂ q₀) {Q : ℝ} (hQ : 0 < Q) (hb : 2*Q ≤ (N : ℝ)^2)
    (β : ℝ) (q : ℕ) [NeZero q] :
    denominatorUnitSum q (fun r => if (r.den : ℝ)/(q₀ : ℝ) ≤ Q/conductorMajorant q₀
      then exceptionalRationalCircleLow N hN q₀ χ₀ Q hQ hb β r else 0)=
      if q₀ ∣ q ∧ conductorMajorant q₀*((q/q₀ : ℕ) : ℝ) ≤ Q
        then realExceptionalCircleTerm N hN q₀ χ₀ Q hQ hb β q else 0 := by
  classical
  rw [exceptionalUnitSum_filter]
  by_cases hd : q₀ ∣ q
  · have hB : 0 < conductorMajorant q₀ := lt_of_lt_of_le (by norm_num) (conductorMajorant_one_le q₀ (NeZero.pos q₀))
    simp only [hd,true_and,conductor_quotient_cutoff (NeZero.pos q₀) hd hB]
  · rw [realExceptionalCircleTerm_not_dvd N hN q₀ χ₀ hQ hb β q hd]
    simp only [ite_self,hd,false_and]

end PrimeSquares
