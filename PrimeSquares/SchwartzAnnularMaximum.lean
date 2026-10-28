import PrimeSquares.SchwartzConvolutionIdentity

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform ContDiff ENNReal
namespace PrimeSquares

noncomputable def cutoffSchwartzOutput (a : ℝ) (ha : 2 ≤ a)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  compactSmoothMultiplier (continuousCutoffSymbol a)
    (continuousCutoffSymbol_boundary (by linarith) (by linarith : 1 ≤ a*1))
    (continuousCutoffSymbol_smooth a) f

noncomputable def annularSchwartzOutput (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (a : ℝ) (ha : 2 ≤ a)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  compactSmoothMultiplier (allAnnularBoundedSymbol N hN β hβ0 hβ1 a)
    (allAnnularBoundedSymbol_boundary N hN β hβ0 hβ1 (by linarith) (by linarith : 1 ≤ a*1))
    (allAnnularBoundedSymbol_smooth N hN β hβ0 hβ1 a) f

theorem annularSchwartzOutput_convolution (N : ℕ) (hN : 1 ≤ N)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (a : ℝ) (ha : 2 ≤ a)
    (f : SchwartzMap ℝ ℂ) :
    (annularSchwartzOutput N hN β hβ0 hβ1 a ha f : ℝ → ℂ) =
      continuousAnnularConvolution N β (cutoffSchwartzOutput a ha f : ℝ → ℂ) :=
  compactSmoothMultiplier_annular_convolution N hN hβ0 hβ1 ha f

theorem cutoffSchwartzOutput_Lp (HY : RawYoungMultiplierInput)
    {a : ℝ} (ha : 2 ≤ a) {p : ℝ} (hp : 1 ≤ p) (f : SchwartzMap ℝ ℂ) :
    eLpNorm (cutoffSchwartzOutput a ha f : ℝ → ℂ) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal cutoffL1Constant * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume :=
  compactSmoothMultiplier_Lp (continuousCutoffSymbol a) _ _
    (continuousCutoffMultiplier_Lp HY (by linarith : 0 < a) hp) f

theorem annularSchwartzOutput_maximum_Lp {C : ℝ} (hC : 0 ≤ C)
    (HHL : RawOneSidedHLInput C) (HY : RawYoungMultiplierInput)
    {p β a : ℝ} (hp0 : 1 < p) (hp1 : p ≤ 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ha : 2 ≤ a)
    (I : Finset ℕ) (N : ℕ → ℕ) (hN : ∀ i, 2 ≤ N i) (f : SchwartzMap ℝ ℂ) :
    MemLp (finiteCoordinateMaximum I (fun i x =>
      annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 a ha f x))
      (ENNReal.ofReal p) volume ∧
    eLpNorm (finiteCoordinateMaximum I (fun i x =>
      annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 a ha f x))
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((C/(p-1))*cutoffL1Constant) * eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume := by
  let u : ℕ → ℝ → ℂ := fun i x =>
    annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 a ha f x
  obtain ⟨H, hHm, hH0, hHnorm, hHdom⟩ := continuousAnnular_maximal_majorant HHL hp0 hp1 hβ1
    ((cutoffSchwartzOutput a ha f).memLp 2) ((cutoffSchwartzOutput a ha f).memLp (ENNReal.ofReal p))
  have hmeas : AEStronglyMeasurable (finiteCoordinateMaximum I u) volume :=
    (finiteCoordinateMaximum_continuous I u
      (fun i _ => (annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 a ha f).continuous)).aestronglyMeasurable
  have hdom : ∀ᵐ x ∂volume, ‖finiteCoordinateMaximum I u x‖ ≤ H x := by
    filter_upwards [hHdom] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (finiteCoordinateMaximum_nonneg I u x)]
    apply finiteCoordinateMaximum_le I u x (hH0 x)
    intro i _
    change ‖annularSchwartzOutput (N i) _ β hβ0 hβ1 a ha f x‖ ≤ _
    rw [annularSchwartzOutput_convolution]
    exact hx (N i) (hN i)
  refine ⟨hHm.mono' hmeas hdom, ?_⟩
  calc
    _ ≤ eLpNorm H (ENNReal.ofReal p) volume :=
      eLpNorm_mono_ae hmeas (hdom.mono (fun x hx => hx.trans (le_abs_self (H x))))
    _ ≤ ENNReal.ofReal (C/(p-1))*eLpNorm (cutoffSchwartzOutput a ha f : ℝ → ℂ) (ENNReal.ofReal p) volume := hHnorm
    _ ≤ ENNReal.ofReal (C/(p-1))*(ENNReal.ofReal cutoffL1Constant*eLpNorm (f : ℝ → ℂ) (ENNReal.ofReal p) volume) :=
      mul_le_mul_right (cutoffSchwartzOutput_Lp HY ha hp0.le f) _
    _ = _ := by rw [←mul_assoc, ←ENNReal.ofReal_mul (div_nonneg hC (by linarith : 0 ≤ p-1))]

theorem cyclic_annularSchwartzOutput_maximum {C : ℝ} (hC : 0 ≤ C)
    (HHL : RawOneSidedHLInput C) (HY : RawYoungMultiplierInput)
    (P : ℕ) [NeZero P] {p β a : ℝ} (hp0 : 1 < p) (hp1 : p ≤ 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ha : 2 ≤ a)
    (I : Finset ℕ) (N : ℕ → ℕ) (hN : ∀ i, 2 ≤ N i)
    (f : ZMod P → SchwartzMap ℝ ℂ) :
    cyclicRealLpSize P (ENNReal.ofReal p) (fun y x => finiteCoordinateMaximum I (fun i x =>
      annularSchwartzOutput (N i) (by have h := hN i; omega) β hβ0 hβ1 a ha (f y) x) x) ≤
      ENNReal.ofReal ((C/(p-1))*cutoffL1Constant) *
        cyclicRealLpSize P (ENNReal.ofReal p) (fun y x => f y x) := by
  exact cyclicRealLpSize_mono_bound P _ (fun y => (f y).memLp _) (by
    exact mul_nonneg (div_nonneg hC (by linarith)) cutoffL1Constant_nonneg)
    (fun y => (annularSchwartzOutput_maximum_Lp hC HHL HY hp0 hp1 hβ0 hβ1 ha I N hN (f y)).2)

end PrimeSquares
