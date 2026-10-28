import PrimeSquares.ContinuousAnnularSignedFourier

set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

/-- Independent scalar Hormander singular-integral theorem on the real line,
with its quantitative near-one consequence from weak (1,1), interpolation and
L2 boundedness. It is quantified over arbitrary integrable kernels and their
actual Fourier symbols. No annular, IW, low/high, maximal or paper conclusion
is a field. This predicate asserts no existence and adds no Lean axiom. -/
def RawScalarHormanderInput (C : ℝ) : Prop :=
  ∀ K : ℝ→ℂ,Integrable K volume →
    ∀ m : BoundedContinuousFunction ℝ ℂ,(∀ θ,𝓕 K θ=m θ) →
    ∀ A H : ℝ,0≤A → 0≤H → (∀ θ,‖m θ‖≤A) → KernelHormanderBound K H →
    ∀ p : ℝ,1<p → p≤2 →
      RealLpMultiplierBound (ENNReal.ofReal p) m (C*(A+H)/(p-1))

theorem scalar_hormander_multiplier {C : ℝ} (HCZ : RawScalarHormanderInput C)
    (K : ℝ→ℂ) (hK : Integrable K volume)
    (m : BoundedContinuousFunction ℝ ℂ) (hF : ∀ θ,𝓕 K θ=m θ)
    {A H p : ℝ} (hA : 0≤A) (hH : 0≤H) (hm : ∀ θ,‖m θ‖≤A)
    (hreg : KernelHormanderBound K H) (hp0 : 1<p) (hp1 : p≤2) :
    RealLpMultiplierBound (ENNReal.ofReal p) m (C*(A+H)/(p-1)) :=
  HCZ K hK m hF A H hA hH hm hreg p hp0 hp1

/-- The complete actual uncut signed-increment estimate, conditional only on
the general scalar singular-integral theorem just stated. Every kernel and L2
hypothesis for this particular family has already been proved. -/
theorem continuousAnnularSignedMultiplier_Lp {C : ℝ} (HCZ : RawScalarHormanderInput C)
    {β : ℝ} (hβ0 : 0<β) (hβ1 : β≤1) (J : ℕ) (σ : ℕ→ℂ)
    (hσ : ∀ j∈Finset.range J,‖σ j‖≤1) {p : ℝ} (hp0 : 1<p) (hp1 : p≤2) :
    RealLpMultiplierBound (ENNReal.ofReal p)
      (continuousAnnularSignedSymbol β hβ0.le hβ1 0 J σ)
      (C*(continuousAnnularIncrementConstant+2+50)/(p-1)) := by
  apply scalar_hormander_multiplier HCZ (continuousAnnularSignedKernel β J σ)
    (continuousAnnularSignedKernel_integrable β J σ) _
    (continuousAnnularSignedKernel_fourier hβ0.le hβ1 J σ)
    (by have h := continuousAnnularIncrementConstant_pos;linarith) (by norm_num)
    (continuousAnnularSignedSymbol_norm hβ0 hβ1 0 J σ hσ)
    (continuousAnnularSignedKernel_hormander hβ0 hβ1 J σ hσ) hp0 hp1

end PrimeSquares
