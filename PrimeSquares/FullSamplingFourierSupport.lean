import PrimeSquares.CyclicProductLpOperators
import PrimeSquares.FiniteComplexInputs
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.PoissonSummation

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform SchwartzMap ENNReal lp
namespace PrimeSquares

/-- Fourier support on the full real Lp space, including p=infinity, is
expressed using the native Fourier transform of its tempered distribution.
No integrable or L2 representative is required. -/
def RealLpSpectrumIn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp V p (volume : Measure ℝ))
    (Ω : Set ℝ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ, tsupport φ ⊆ Ωᶜ →
    (𝓕 (Lp.toTemperedDistribution f)) φ = 0

theorem realLpSpectrumIn_mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Lp V p (volume : Measure ℝ)}
    {Ω Ψ : Set ℝ} (h : RealLpSpectrumIn f Ω) (hΩ : Ω ⊆ Ψ) :
    RealLpSpectrumIn f Ψ := by
  intro φ hφ
  exact h φ (hφ.trans (Set.compl_subset_compl.mpr hΩ))

theorem realLpSpectrumIn_interval_mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : Lp V p (volume : Measure ℝ)}
    {δ ε : ℝ} (hδε : δ ≤ ε) (h : RealLpSpectrumIn f (Set.Icc (-δ) δ)) :
    RealLpSpectrumIn f (Set.Icc (-ε) ε) :=
  realLpSpectrumIn_mono h (Set.Icc_subset_Icc (neg_le_neg hδε) hδε)

/-- All integer translates are included, giving the full lift of the torus
major arcs rather than one chosen real representative. -/
def liftedRationalArcs (Γ : Finset ℚ) (ε : ℝ) : Set ℝ :=
  {θ | ∃ α ∈ Γ, ∃ j : ℤ, |θ-(α : ℝ)-(j : ℝ)| ≤ ε}

/-- Distributional Fourier support of an arbitrary integer Lp sequence.
The Fourier series is tested against Schwartz functions supported off the
periodic lifted frequency set. Its absolute convergence is proved below. -/
def IntegerLpSpectrumIn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {p : ℝ≥0∞} (f : lp (fun _ : ℤ => V) p) (Ω : Set ℝ) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ, tsupport φ ⊆ Ωᶜ →
    ∑' n : ℤ, (𝓕 φ) (n : ℝ) • f n = 0

theorem schwartz_integer_test_summable {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : lp (fun _ : ℤ => V) p) (φ : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => (𝓕 φ) (n : ℝ) • f n) := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  have hs : Summable (fun n : ℤ => (𝓕 φ) (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
      (((𝓕 φ).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  apply (hs.norm.mul_right ‖f‖).of_norm_bounded
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm hp0 f n) (norm_nonneg _)

theorem integerLpSpectrumIn_mono {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {p : ℝ≥0∞} {f : lp (fun _ : ℤ => V) p} {Ω Ψ : Set ℝ}
    (h : IntegerLpSpectrumIn f Ω) (hΩ : Ω ⊆ Ψ) : IntegerLpSpectrumIn f Ψ := by
  intro φ hφ
  exact h φ (hφ.trans (Set.compl_subset_compl.mpr hΩ))

noncomputable def cyclicFunctionLp {V : Type*} [NormedAddCommGroup V]
    {p : ℝ≥0∞} (P : ℕ) (G : ZMod P → C(ℝ,V))
    (hG : ∀ y, MemLp (G y : ℝ → V) p volume) (y : ZMod P) :
    Lp V p (volume : Measure ℝ) := (hG y).toLp (G y : ℝ → V)

noncomputable def cyclicFourierLpComponent {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (P : ℕ) [NeZero P]
    (F : ZMod P → Lp V p (volume : Measure ℝ)) (α : ℚ) : Lp V p (volume : Measure ℝ) :=
  (P : ℂ)⁻¹ • ∑ y : ZMod P,
    negativeFourierCharacter (y.val : ℤ) ((α : ℝ) : PrimeCircle) • F y

/-- The finite cyclic Fourier basis consists of P-torsion rational points,
not all rational points whose denominator is at most P. -/
noncomputable def cyclicTorsionRationals (P : ℕ) : Finset ℚ := by
  classical
  exact (canonicalRationalCenters P).filter (fun α => α.den ∣ P)

/-- The actual full bandlimited real/cyclic class. Continuous representatives
are retained because sampling evaluates functions at points; Lp membership
and Fourier support impose no Schwartz or L2 condition. -/
structure CyclicBandlimitedLp (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : ℕ) [NeZero P] (Γ : Finset ℚ) (ε : ℝ) where
  value : ZMod P → C(ℝ,V)
  memLp : ∀ y, MemLp (value y : ℝ → V) p volume
  spectral : ∀ α ∈ cyclicTorsionRationals P,
    if α ∈ Γ then RealLpSpectrumIn
      (cyclicFourierLpComponent P (cyclicFunctionLp P value memLp) α) (Set.Icc (-ε) ε)
    else cyclicFourierLpComponent P (cyclicFunctionLp P value memLp) α = 0

noncomputable def cyclicBandlimitedDiagonal {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {P : ℕ} [NeZero P] {Γ : Finset ℚ} {ε : ℝ}
    (G : CyclicBandlimitedLp V p P Γ ε) (n : ℤ) : V := G.value (n : ZMod P) (n : ℝ)

theorem cyclicFunctionLp_size {V : Type*} [NormedAddCommGroup V]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (P : ℕ) [NeZero P]
    (G : ZMod P → C(ℝ,V)) (hG : ∀ y, MemLp (G y : ℝ → V) p volume) :
    cyclicFamilyLpSize P p (cyclicFunctionLp P G hG) =
      cyclicRealLpSize P p (fun y x => G y x) := by
  unfold cyclicFamilyLpSize cyclicRealLpSize
  congr 1
  rw [←eLpNorm_norm _ AEStronglyMeasurable.of_discrete]
  congr 1
  funext y
  exact Lp.norm_toLp (G y : ℝ → V) (hG y)

end PrimeSquares
