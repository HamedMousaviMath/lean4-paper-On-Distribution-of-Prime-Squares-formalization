import PrimeSquares.GoldbachWeightedHarmonic

set_option autoImplicit false
open MeasureTheory
namespace PrimeSquares

theorem goldbach_weighted_thin_window_width (n T : ℝ) (hn : 4≤n)
    (hT : 0≤T) (hTn : T≤n/4) :
    Real.sqrt (n-1)-Real.sqrt (n-1-T)≤2*T/Real.sqrt n := by
  have hn0 : 0≤n := by linarith
  have ha0 : 0≤n-1-T := by linarith
  have hb0 : 0≤n-1 := by linarith
  have ha := Real.sq_sqrt ha0
  have hb := Real.sq_sqrt hb0
  have hs := Real.sq_sqrt hn0
  have hapos := Real.sqrt_nonneg (n-1-T)
  have hbpos := Real.sqrt_nonneg (n-1)
  have hspos := Real.sqrt_pos.mpr (show 0<n by linarith)
  have hba : Real.sqrt (n-1-T)≤Real.sqrt (n-1) := Real.sqrt_le_sqrt (by linarith)
  have hslow : Real.sqrt n≤2*Real.sqrt (n-1-T) := by nlinarith only [ha,hs,hapos,hspos,hn,hTn]
  apply (le_div_iff₀ hspos).mpr
  have hh := mul_nonneg (sub_nonneg.mpr hba)
    (show 0≤2*(Real.sqrt (n-1)+Real.sqrt (n-1-T))-Real.sqrt n by linarith)
  nlinarith only [hh,ha,hb]

theorem goldbach_weighted_thin_window_subset (n T : ℝ) (hn : 4≤n)
    (_hT : 0≤T) (hTn : T≤n/4) :
    {u : ℝ | 2≤u ∧ 0<n-1-u^2 ∧ n-1-u^2<T}⊆
      Set.Ioo (Real.sqrt (n-1-T)) (Real.sqrt (n-1)) := by
  intro u hu
  have hu0 : 0≤u := by linarith [hu.1]
  have hl0 : 0≤n-1-T := by linarith
  constructor
  · apply (Real.sqrt_lt hl0 hu0).mpr
    linarith [hu.2.2]
  · apply Real.lt_sqrt_of_sq_lt
    linarith [hu.2.1]

theorem goldbach_weighted_thin_window_measure (n T : ℝ) (hn : 4≤n)
    (hT : 0≤T) (hTn : T≤n/4) :
    volume.real {u : ℝ | 2≤u ∧ 0<n-1-u^2 ∧ n-1-u^2<T}≤2*T/Real.sqrt n := by
  have hs := goldbach_weighted_thin_window_subset n T hn hT hTn
  have hfin : volume (Set.Ioo (Real.sqrt (n-1-T)) (Real.sqrt (n-1)))≠⊤ :=
    (lt_of_le_of_lt (measure_mono Set.Ioo_subset_Icc_self) isCompact_Icc.measure_lt_top).ne
  have hm := measureReal_mono (μ:=volume) hs hfin
  have hba : Real.sqrt (n-1-T)≤Real.sqrt (n-1) := Real.sqrt_le_sqrt (by linarith)
  rw [Real.volume_real_Ioo,max_eq_left (sub_nonneg.mpr hba)] at hm
  exact hm.trans (goldbach_weighted_thin_window_width n T hn hT hTn)

end PrimeSquares
