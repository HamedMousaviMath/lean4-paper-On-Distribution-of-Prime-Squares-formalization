import PrimeSquares.RealAnnularMaximal
import PrimeSquares.RealAnnularFourierIdentity
import PrimeSquares.ScalarHormanderInterface

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal FourierTransform
namespace PrimeSquares

def FullLpConvolutionBound (p : ℝ≥0∞) (K : ℝ → ℂ) (B : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, MemLp f p volume →
    MemLp (convolution K f (ContinuousLinearMap.mul ℂ ℂ) volume) p volume ∧
      eLpNorm (convolution K f (ContinuousLinearMap.mul ℂ ℂ) volume) p volume ≤
        ENNReal.ofReal B*eLpNorm f p volume

/-- The general scalar Hormander theorem on the full Lp domain. The kernel,
actual Fourier symbol, L2 bound and Hormander condition are all hypotheses.
No annular, signed-increment or current-paper conclusion is a field. -/
def RawFullScalarHormanderInput (C : ℝ) : Prop :=
  ∀ K : ℝ → ℂ, Integrable K volume →
    ∀ m : BoundedContinuousFunction ℝ ℂ, (∀ θ,𝓕 K θ=m θ) →
    ∀ A H : ℝ, 0 ≤ A → 0 ≤ H → (∀ θ,‖m θ‖ ≤ A) → KernelHormanderBound K H →
    ∀ p : ℝ, 1 < p → p ≤ 2 →
      FullLpConvolutionBound (ENNReal.ofReal p) K (C*(A+H)/(p-1))

theorem fullLpConvolutionBound_mono {p : ℝ≥0∞} {K : ℝ → ℂ} {A B : ℝ}
    (HA : FullLpConvolutionBound p K A) (hAB : A ≤ B) : FullLpConvolutionBound p K B := by
  intro f hf
  obtain ⟨hmem,hn⟩ := HA f hf
  exact ⟨hmem,hn.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hAB) _)⟩

theorem continuousAnnularSigned_full_Lp {C : ℝ} (HCZ : RawFullScalarHormanderInput C)
    {β p : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hp : 1 < p) (hp2 : p ≤ 2)
    (J : ℕ) (σ : ℕ → ℂ) (hσ : ∀ j ∈ Finset.range J, ‖σ j‖ ≤ 1) :
    FullLpConvolutionBound (ENNReal.ofReal p) (continuousAnnularSignedKernel β J σ)
      (C*(continuousAnnularIncrementConstant+52)/(p-1)) := by
  have hA : 0 ≤ continuousAnnularIncrementConstant+2 := by
    have h := continuousAnnularIncrementConstant_pos
    linarith
  have h := HCZ (continuousAnnularSignedKernel β J σ)
    (continuousAnnularSignedKernel_integrable β J σ)
    (continuousAnnularSignedSymbol β hβ0.le hβ1 0 J σ)
    (continuousAnnularSignedKernel_fourier hβ0.le hβ1 J σ)
    (continuousAnnularIncrementConstant+2) 50 hA (by norm_num)
    (continuousAnnularSignedSymbol_norm hβ0 hβ1 0 J σ hσ)
    (continuousAnnularSignedKernel_hormander hβ0 hβ1 J σ hσ) p hp hp2
  convert h using 1; ring

theorem source_continuous_annular_estimates {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (HCZ : RawFullScalarHormanderInput C) (HHL : RawFullOneSidedHLInput H) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ p : ℝ, 1 < p → p ≤ 2 →
      (∀ (J : ℕ) (σ : ℕ → ℂ), (∀ j ∈ Finset.range J, ‖σ j‖ ≤ 1) →
        FullLpConvolutionBound (ENNReal.ofReal p) (continuousAnnularSignedKernel β J σ)
          (K/(p-1))) ∧
      (∀ f : ℝ → ℂ, MemLp f (ENNReal.ofReal p) volume →
        (∀ᵐ x ∂volume, realContinuousAnnularMaxENorm β f x < ∞) ∧
        MemLp (realContinuousAnnularMaxValue β f) (ENNReal.ofReal p) volume ∧
        eLpNorm (realContinuousAnnularMaxValue β f) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (K/(p-1))*eLpNorm f (ENNReal.ofReal p) volume) := by
  let A := C*(continuousAnnularIncrementConstant+52)
  have hA : 0 ≤ A := by
    have h := continuousAnnularIncrementConstant_pos
    dsimp [A]
    positivity
  let K := A+2*H+1
  have hK : 0 < K := by dsimp [K];linarith
  have hAK : A ≤ K := by dsimp [K];linarith
  have hHK : 2*H ≤ K := by dsimp [K];linarith
  refine ⟨K,hK,?_⟩
  intro β hβ0 hβ1 p hp hp2
  have hpp : 0 < p-1 := by linarith
  constructor
  · intro J σ hσ
    exact fullLpConvolutionBound_mono (continuousAnnularSigned_full_Lp HCZ hβ0 hβ1 hp hp2 J σ hσ)
      (div_le_div_of_nonneg_right hAK hpp.le)
  · intro f hf
    obtain ⟨hfin,hmem,hn⟩ := realContinuousAnnular_maximal_Lp HHL hp hp2 hβ1 hf
    exact ⟨hfin,hmem,hn.trans (mul_le_mul_left
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hHK hpp.le)) _)⟩

end PrimeSquares
