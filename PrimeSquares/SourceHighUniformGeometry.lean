import PrimeSquares.SourceScaleFourthPower
import PrimeSquares.SourceLowRangeBudget

namespace PrimeSquares

theorem sourceHigh_uniform_geometry : ∃ c₀ : ℝ,0<c₀ ∧ ∀ Q N₀ : ℝ,2 ≤ Q → 2 ≤ N₀ →
    Real.log Q ≤ c₀*Real.sqrt (Real.log N₀) → ∀ N : ℕ,N₀ ≤ (N : ℝ) →
    2*(sourceMajorArcScale (N : ℝ) Q)^8 ≤ (N : ℝ)^2 := by
  obtain ⟨Nb,hNb,hBudget⟩ := sourceMajorArcScale_uniform_fourth_power (c := 7) (by norm_num)
  have hNbp : (0 : ℝ)<Nb := by exact_mod_cast (by omega : 0<Nb)
  have hLogNb : 0 ≤ Real.log (Nb : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Nb))
  let L := Real.log (Nb : ℝ)+1
  have hL : 0<L := by dsimp [L];linarith
  have hsL : 0<Real.sqrt L := Real.sqrt_pos.mpr hL
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  let c₀ : ℝ := min (1/8) (Real.log 2/(2*Real.sqrt L))
  have hc₀ : 0<c₀ := lt_min (by norm_num) (div_pos hlog2 (by positivity))
  refine ⟨c₀,hc₀,?_⟩
  intro Q N₀ hQ hN₀ hcut N hN
  have hN₀p : 0<N₀ := by linarith
  have hLog₀ : 0 ≤ Real.log N₀ := Real.log_nonneg (by linarith)
  have hbase : Real.log 2 ≤ c₀*Real.sqrt (Real.log N₀) :=
    (Real.log_le_log (by norm_num : (0 : ℝ)<2) hQ).trans hcut
  have hcoef : c₀ ≤ Real.log 2/(2*Real.sqrt L) := min_le_right _ _
  have hbound := hbase.trans (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right hbound (show 0 ≤ 2*Real.sqrt L by positivity)
  have hclear : (Real.log 2/(2*Real.sqrt L))*Real.sqrt (Real.log N₀)*(2*Real.sqrt L)=
      Real.log 2*Real.sqrt (Real.log N₀) := by field_simp
  rw [hclear] at hmul
  have hs : 2*Real.sqrt L ≤ Real.sqrt (Real.log N₀) := le_of_mul_le_mul_left hmul hlog2
  have hs2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2*Real.sqrt L) hs 2
  have hlogForce : Real.log (Nb : ℝ) ≤ Real.log N₀ := by
    have hLval : L=Real.log (Nb : ℝ)+1 := rfl
    nlinarith [Real.sq_sqrt hL.le,Real.sq_sqrt hLog₀]
  have hNb₀ : (Nb : ℝ) ≤ N₀ := (Real.log_le_log_iff hNbp hN₀p).mp hlogForce
  have hNbN : Nb ≤ N := by exact_mod_cast hNb₀.trans hN
  have hlogMono : Real.log N₀ ≤ Real.log (N : ℝ) := Real.log_le_log hN₀p hN
  have hcutN : Real.log Q ≤ (1/8 : ℝ)*Real.sqrt (Real.log (N : ℝ)) :=
    hcut.trans (mul_le_mul (min_le_left _ _) (Real.sqrt_le_sqrt hlogMono) (Real.sqrt_nonneg _) (by norm_num))
  have hb4 := hBudget N hNbN Q (by linarith : 1 ≤ Q)
    (by simpa only [show (min ((7 : ℝ)/7) 1)/8=1/8 by norm_num] using hcutN)
  exact source_fourth_budget_to_eighth hb4

end PrimeSquares
