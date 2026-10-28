import PrimeSquares.IWSamplingSpaces
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace PrimeSquares

theorem cyclicRealLpSize_mono_bound {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : ℕ) [NeZero P] (p : ℝ≥0∞) {U : ZMod P → ℝ → E} {V : ZMod P → ℝ → F}
    (hV : ∀ y, MemLp (V y) p volume) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ y, eLpNorm (U y) p volume ≤ ENNReal.ofReal K * eLpNorm (V y) p volume) :
    cyclicRealLpSize P p U ≤ ENNReal.ofReal K * cyclicRealLpSize P p V := by
  have hpoint (y : ZMod P) : (eLpNorm (U y) p volume).toReal ≤
      K*(eLpNorm (V y) p volume).toReal := by
    have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hV y).eLpNorm_ne_top) (h y)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK] using h'
  unfold cyclicRealLpSize
  have he : eLpNorm (fun y : ZMod P => (eLpNorm (U y) p volume).toReal) p Measure.count ≤
      ENNReal.ofReal K * eLpNorm (fun y : ZMod P => (eLpNorm (V y) p volume).toReal) p Measure.count := by
    calc
      _ ≤ eLpNorm (fun y : ZMod P => K*(eLpNorm (V y) p volume).toReal) p Measure.count := by
        apply eLpNorm_mono (by exact AEStronglyMeasurable.of_discrete)
        intro y
        simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          abs_of_nonneg (mul_nonneg hK ENNReal.toReal_nonneg)] using hpoint y
      _ = _ := by
        rw [show (fun y : ZMod P => K*(eLpNorm (V y) p volume).toReal) =
          K • (fun y : ZMod P => (eLpNorm (V y) p volume).toReal) by rfl,
          eLpNorm_const_smul, Real.enorm_eq_ofReal hK]
  exact (mul_le_mul_right he _).trans_eq (by ring)

theorem eLpNorm_count_equiv {A : Type*} [Fintype A] [MeasurableSpace A] [DiscreteMeasurableSpace A]
    (e : A ≃ A) (f : A → ℝ) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ∞) :
    eLpNorm (fun y => f (e y)) p Measure.count = eLpNorm f p Measure.count := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT AEStronglyMeasurable.of_discrete,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT AEStronglyMeasurable.of_discrete,
    lintegral_count, lintegral_count]
  congr 1
  exact e.tsum_eq (fun y => ‖f y‖ₑ^p.toReal)

theorem cyclicRealLpSize_translate {E : Type*} [NormedAddCommGroup E]
    (P : ℕ) [NeZero P] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpT : p ≠ ∞)
    (U : ZMod P → ℝ → E) (z : ZMod P) :
    cyclicRealLpSize P p (fun y => U (y-z)) = cyclicRealLpSize P p U := by
  unfold cyclicRealLpSize
  congr 1
  have he := eLpNorm_count_equiv (Equiv.subRight z)
    (fun y : ZMod P => (eLpNorm (U y) p volume).toReal) hp0 hpT
  exact he

theorem cyclicRealLpSize_add {E : Type*} [NormedAddCommGroup E]
    (P : ℕ) [NeZero P] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (U V : ZMod P → ℝ → E) (hU : ∀ y, MemLp (U y) p volume)
    (hV : ∀ y, MemLp (V y) p volume) :
    cyclicRealLpSize P p (fun y x => U y x + V y x) ≤
      cyclicRealLpSize P p U + cyclicRealLpSize P p V := by
  let u : ZMod P → ℝ := fun y => (eLpNorm (U y) p volume).toReal
  let v : ZMod P → ℝ := fun y => (eLpNorm (V y) p volume).toReal
  have hpoint (y : ZMod P) : (eLpNorm (fun x => U y x+V y x) p volume).toReal ≤ u y+v y := by
    have h' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨(hU y).eLpNorm_ne_top, (hV y).eLpNorm_ne_top⟩)
      (eLpNorm_add_le hp (f := U y) (g := V y) (μ := volume))
    simpa only [Pi.add_def, ENNReal.toReal_add (hU y).eLpNorm_ne_top (hV y).eLpNorm_ne_top] using h'
  have hnorm : eLpNorm (fun y : ZMod P => (eLpNorm (fun x => U y x+V y x) p volume).toReal) p Measure.count ≤
      eLpNorm u p Measure.count + eLpNorm v p Measure.count := by
    calc
      _ ≤ eLpNorm (u+v) p Measure.count := by
        apply eLpNorm_mono (by exact AEStronglyMeasurable.of_discrete)
        intro y
        change ‖(eLpNorm (fun x => U y x+V y x) p volume).toReal‖ ≤ ‖u y+v y‖
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ENNReal.toReal_nonneg,
          abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
        exact hpoint y
      _ ≤ _ := eLpNorm_add_le hp
  unfold cyclicRealLpSize
  exact (mul_le_mul_right hnorm _).trans_eq (by rw [mul_add])

theorem cyclicRealLpSize_smul (P : ℕ) [NeZero P] (p : ℝ≥0∞)
    (c : ℂ) (U : ZMod P → ℝ → ℂ) :
    cyclicRealLpSize P p (fun y x => c*U y x) = ‖c‖ₑ * cyclicRealLpSize P p U := by
  have hinner (y : ZMod P) : eLpNorm (fun x => c*U y x) p volume = ‖c‖ₑ*eLpNorm (U y) p volume := by
    exact eLpNorm_const_smul c (U y) p volume
  unfold cyclicRealLpSize
  simp_rw [hinner, ENNReal.toReal_mul, toReal_enorm]
  have he : (fun y : ZMod P => ‖c‖*(eLpNorm (U y) p volume).toReal) =
      ‖c‖ • (fun y : ZMod P => (eLpNorm (U y) p volume).toReal) := rfl
  rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal (norm_nonneg c), ofReal_norm]
  ring

theorem cyclicRealLpSize_zero (P : ℕ) (p : ℝ≥0∞) :
    cyclicRealLpSize P p (fun _ : ZMod P => (0 : ℝ → ℂ)) = 0 := by
  unfold cyclicRealLpSize
  simp only [eLpNorm_zero, ENNReal.toReal_zero]
  change _ * eLpNorm (0 : ZMod P → ℝ) p Measure.count = 0
  rw [eLpNorm_zero, mul_zero]

theorem cyclicRealLpSize_finsetSum {ι : Type*} (I : Finset ι)
    (P : ℕ) [NeZero P] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (W : ι → ZMod P → ℝ → ℂ) (hW : ∀ i ∈ I, ∀ y, MemLp (W i y) p volume) :
    cyclicRealLpSize P p (fun y x => ∑ i ∈ I, W i y x) ≤
      ∑ i ∈ I, cyclicRealLpSize P p (W i) := by
  classical
  revert hW
  induction I using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    exact (cyclicRealLpSize_zero P p).le
  | @insert i I hi ih =>
    intro hW
    have hrest : ∀ y, MemLp (fun x => ∑ j ∈ I, W j y x) p volume :=
      fun y => memLp_finsetSum I (fun j hj => hW j (Finset.mem_insert_of_mem hj) y)
    simp only [Finset.sum_insert hi]
    exact (cyclicRealLpSize_add P hp (W i) _ (hW i (Finset.mem_insert_self i I)) hrest).trans
      (add_le_add le_rfl (ih (fun j hj => hW j (Finset.mem_insert_of_mem hj))))

noncomputable def cyclicConvolutionSchwartz (P : ℕ) [NeZero P] (ν : ZMod P → ℂ)
    (F : ZMod P → SchwartzMap ℝ ℂ) (y : ZMod P) : SchwartzMap ℝ ℂ :=
  ∑ z : ZMod P, ν z • F (y-z)

theorem cyclicConvolutionSchwartz_apply (P : ℕ) [NeZero P] (ν : ZMod P → ℂ)
    (F : ZMod P → SchwartzMap ℝ ℂ) (y : ZMod P) (x : ℝ) :
    cyclicConvolutionSchwartz P ν F y x = ∑ z : ZMod P, ν z * F (y-z) x := by
  simp only [cyclicConvolutionSchwartz, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]

theorem cyclicConvolutionSchwartz_Lp (P : ℕ) [NeZero P]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpT : p ≠ ∞) (ν : ZMod P → ℂ)
    (F : ZMod P → SchwartzMap ℝ ℂ) :
    cyclicRealLpSize P p (fun y x => cyclicConvolutionSchwartz P ν F y x) ≤
      ENNReal.ofReal (cyclicVariation P ν) * cyclicRealLpSize P p (fun y x => F y x) := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hW : ∀ z ∈ (Finset.univ : Finset (ZMod P)), ∀ y,
      MemLp (fun x => ν z*F (y-z) x) p volume :=
    fun z _ y => (F (y-z)).memLp p |>.const_smul (ν z)
  simp_rw [cyclicConvolutionSchwartz_apply]
  calc
    _ ≤ ∑ z : ZMod P, cyclicRealLpSize P p (fun y x => ν z*F (y-z) x) :=
      cyclicRealLpSize_finsetSum Finset.univ P hp _ hW
    _ = ∑ z : ZMod P, ‖ν z‖ₑ * cyclicRealLpSize P p (fun y x => F y x) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [cyclicRealLpSize_smul]
      exact congrArg (fun t : ℝ≥0∞ => ‖ν z‖ₑ*t)
        (cyclicRealLpSize_translate P hp0 hpT (fun y => (F y : ℝ → ℂ)) z)
    _ = (∑ z : ZMod P, ENNReal.ofReal ‖ν z‖) * cyclicRealLpSize P p (fun y x => F y x) := by
      simp only [ofReal_norm, Finset.sum_mul]
    _ = _ := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun z _ => norm_nonneg (ν z))]
      rfl

end PrimeSquares
