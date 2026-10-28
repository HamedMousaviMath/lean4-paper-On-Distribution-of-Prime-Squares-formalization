import PrimeSquares.FullSamplingFourierSupport
import PrimeSquares.RealIWConstruction
import PrimeSquares.IWFiniteMaximumCost

set_option autoImplicit false
open MeasureTheory Finset
open scoped FourierTransform SchwartzMap ENNReal lp
namespace PrimeSquares

noncomputable def bandlimitedLpSize {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)] {P : ℕ} [NeZero P]
    {Γ : Finset ℚ} {ε : ℝ} (G : CyclicBandlimitedLp V p P Γ ε) : ℝ≥0∞ :=
  cyclicFamilyLpSize P p (cyclicFunctionLp P G.value G.memLp)

/-- The full two-direction sampling assertion on the actual bandlimited
classes, together with the unique interpolation operator on every lp input
whose distributional Fourier support is in the projected arcs. -/
def FullMajorArcSamplingProperty (C : ℝ) (r k : ℕ) (S : Finset ℕ)
    (P : ℕ) [NeZero P] (ε p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] : Prop :=
  (∀ G : CyclicBandlimitedLp ℂ (ENNReal.ofReal p) P (iwFrequencySet S k) ε,
    MemLp (cyclicBandlimitedDiagonal G) (ENNReal.ofReal p) Measure.count ∧
    eLpNorm (cyclicBandlimitedDiagonal G) (ENNReal.ofReal p) Measure.count ≤
      ENNReal.ofReal (iwMultiplierConstant C r k)*bandlimitedLpSize G ∧
    bandlimitedLpSize G ≤ ENNReal.ofReal (iwMultiplierConstant C r k)*
      eLpNorm (cyclicBandlimitedDiagonal G) (ENNReal.ofReal p) Measure.count) ∧
  (∀ f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p),
    IntegerLpSpectrumIn f (liftedRationalArcs (iwFrequencySet S k) ε) →
    ∃! G : CyclicBandlimitedLp ℂ (ENNReal.ofReal p) P (iwFrequencySet S k) ε,
      ∀ n : ℤ, cyclicBandlimitedDiagonal G n = f n)

/-- The independent Tao major-arc sampling theorem, Theorem1.6, in the
finite arithmetic quotient. It applies to every good coprime data set and
the whole source lp classes; it contains no Q, constructed period, annular
kernel, current-paper low/high or maximal conclusion. The published/full-
distributional-class and quotient realization bridges remain unproved. -/
def RawFullMajorArcSamplingInput (C : ℝ) : Prop :=
  ∀ (r k : ℕ), 2 ≤ r → 1 ≤ k → ∀ S : Finset ℕ,
    (∀ s ∈ S, 0 < s) → (S : Set ℕ).Pairwise Nat.Coprime →
    ∀ (P : ℕ) [NeZero P], (∀ α ∈ iwFrequencySet S k, α.den ∣ P) →
    ∀ ε : ℝ, IWGood r k S ε → ∀ p : ℝ,
    iwNearOneExponent r ≤ p → p ≤ 2*(r : ℝ) →
    ∀ [Fact (1 ≤ ENNReal.ofReal p)], FullMajorArcSamplingProperty C r k S P ε p

theorem quantitative_real_iw_full_sampling {C Q : ℝ} (hC : 2 ≤ C) (hQ : 0 ≤ Q)
    (HS : RawFullMajorArcSamplingInput C) {r k : ℕ} (hr : 2 ≤ r) (hk : 4 ≤ k)
    (d : TaoArcConstructionData C (iwRho k) k ⌊Q⌋₊) [NeZero d.period]
    {p : ℝ} (hp0 : iwNearOneExponent r ≤ p) (hp1 : p ≤ 2*(r : ℝ))
    [Fact (1 ≤ ENNReal.ofReal p)] :
    FullMajorArcSamplingProperty C r k d.S d.period (realIWWidth C r k Q) p :=
  HS r k hr (by omega) d.S d.positive d.coprime d.period d.periodic
    (realIWWidth C r k Q) (real_iw_goodness_from_floor hC hQ hr hk d) p hp0 hp1

noncomputable def fullIWInterpolation {C : ℝ} {r k : ℕ} {S : Finset ℕ}
    {P : ℕ} [NeZero P] {ε p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : FullMajorArcSamplingProperty C r k S P ε p)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (hf : IntegerLpSpectrumIn f (liftedRationalArcs (iwFrequencySet S k) ε)) :
    CyclicBandlimitedLp ℂ (ENNReal.ofReal p) P (iwFrequencySet S k) ε :=
  Classical.choose (H.2 f hf).exists

theorem fullIWInterpolation_diagonal {C : ℝ} {r k : ℕ} {S : Finset ℕ}
    {P : ℕ} [NeZero P] {ε p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : FullMajorArcSamplingProperty C r k S P ε p)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (hf : IntegerLpSpectrumIn f (liftedRationalArcs (iwFrequencySet S k) ε)) :
    (cyclicBandlimitedDiagonal (fullIWInterpolation H f hf) : ℤ → ℂ) = (f : ℤ → ℂ) := by
  funext n
  exact Classical.choose_spec (H.2 f hf).exists n

theorem fullIWInterpolation_unique {C : ℝ} {r k : ℕ} {S : Finset ℕ}
    {P : ℕ} [NeZero P] {ε p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : FullMajorArcSamplingProperty C r k S P ε p)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (hf : IntegerLpSpectrumIn f (liftedRationalArcs (iwFrequencySet S k) ε))
    (G : CyclicBandlimitedLp ℂ (ENNReal.ofReal p) P (iwFrequencySet S k) ε)
    (hG : ∀ n : ℤ, cyclicBandlimitedDiagonal G n = f n) :
    G = fullIWInterpolation H f hf :=
  (H.2 f hf).unique hG (Classical.choose_spec (H.2 f hf).exists)

theorem fullIWInterpolation_source_bounds {C : ℝ} (hC : 2 ≤ C) {r k : ℕ} (hr : 2 ≤ r)
    {S : Finset ℕ} {P : ℕ} [NeZero P] {ε p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : FullMajorArcSamplingProperty C r k S P ε p)
    (f : lp (fun _ : ℤ => ℂ) (ENNReal.ofReal p))
    (hf : IntegerLpSpectrumIn f (liftedRationalArcs (iwFrequencySet S k) ε)) :
    (ENNReal.ofReal (iwMultiplierConstant C r k))⁻¹*
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count ≤
      bandlimitedLpSize (fullIWInterpolation H f hf) ∧
    bandlimitedLpSize (fullIWInterpolation H f hf) ≤
      ENNReal.ofReal (iwMultiplierConstant C r k)*
        eLpNorm (f : ℤ → ℂ) (ENNReal.ofReal p) Measure.count := by
  obtain ⟨_,h₁,h₂⟩ := H.1 (fullIWInterpolation H f hf)
  rw [fullIWInterpolation_diagonal] at h₁ h₂
  have hK : 0 < iwMultiplierConstant C r k :=
    lt_of_lt_of_le (by norm_num) (iwMultiplierConstant_one_le hC hr k)
  have hK0 : ENNReal.ofReal (iwMultiplierConstant C r k) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hK).ne'
  refine ⟨?_,h₂⟩
  calc
    _ ≤ (ENNReal.ofReal (iwMultiplierConstant C r k))⁻¹*
        (ENNReal.ofReal (iwMultiplierConstant C r k)*
          bandlimitedLpSize (fullIWInterpolation H f hf)) := mul_le_mul_right h₁ _
    _ = _ := by rw [←mul_assoc,ENNReal.inv_mul_cancel hK0 ENNReal.ofReal_ne_top,one_mul]

/-- Independent quantitative Shannon sampling at c=1/100, Tao Proposition1.5,
for every finite-dimensional normed complex target and the complete Lp
scale, including p=1 and infinity. It has no current-paper parameters. -/
def RawFullShannonInput (C : ℝ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (P : ℕ) [NeZero P], ∀ p : ℝ≥0∞, 1 ≤ p → ∀ [Fact (1 ≤ p)],
    ∀ G : ZMod P → C(ℝ,V), ∀ hG : ∀ y, MemLp (G y : ℝ → V) p volume,
      (∀ y, RealLpSpectrumIn (cyclicFunctionLp P G hG y)
        (Set.Icc (-(1/(100*(P : ℝ)))) (1/(100*(P : ℝ))))) →
    MemLp (fun n : ℤ => G (n : ZMod P) (n : ℝ)) p Measure.count ∧
    eLpNorm (fun n : ℤ => G (n : ZMod P) (n : ℝ)) p Measure.count ≤
      ENNReal.ofReal C*cyclicRealLpSize P p (fun y x => G y x) ∧
    cyclicRealLpSize P p (fun y x => G y x) ≤ ENNReal.ofReal C*
      eLpNorm (fun n : ℤ => G (n : ZMod P) (n : ℝ)) p Measure.count

theorem quantitative_full_shannon_diagonal {C : ℝ} (HS : RawFullShannonInput C)
    (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (P : ℕ) [NeZero P] (p : ℝ≥0∞) (hp : 1 ≤ p) [Fact (1 ≤ p)]
    {δ : ℝ} (hδ : δ ≤ 1/(100*(P : ℝ)))
    (G : ZMod P → C(ℝ,V)) (hG : ∀ y, MemLp (G y : ℝ → V) p volume)
    (hband : ∀ y, RealLpSpectrumIn (cyclicFunctionLp P G hG y) (Set.Icc (-δ) δ)) :
    MemLp (fun n : ℤ => G (n : ZMod P) (n : ℝ)) p Measure.count ∧
    eLpNorm (fun n : ℤ => G (n : ZMod P) (n : ℝ)) p Measure.count ≤
      ENNReal.ofReal C*cyclicRealLpSize P p (fun y x => G y x) ∧
    cyclicRealLpSize P p (fun y x => G y x) ≤ ENNReal.ofReal C*
      eLpNorm (fun n : ℤ => G (n : ZMod P) (n : ℝ)) p Measure.count :=
  HS V P p hp G hG (fun y => realLpSpectrumIn_interval_mono hδ (hband y))

end PrimeSquares
