import PrimeSquares.ContinuousAnnularHormander
import PrimeSquares.RealFourierIntegralLinearity

set_option autoImplicit false
open Finset MeasureTheory
open scoped FourierTransform
namespace PrimeSquares

theorem continuousAnnularSignedKernel_fourier {β : ℝ}
    (hβ0 : 0≤β) (hβ1 : β≤1) (J : ℕ) (σ : ℕ→ℂ) (θ : ℝ) :
    𝓕 (continuousAnnularSignedKernel β J σ) θ=
      continuousAnnularSignedSymbol β hβ0 hβ1 0 J σ θ := by
  have hp (j : ℕ) := continuousAnnularKernel_complex_integrable (N := (2 : ℕ)^(j+1))
    (one_le_pow₀ (by norm_num)) β
  have hm (j : ℕ) := continuousAnnularKernel_complex_integrable (N := (2 : ℕ)^j)
    (one_le_pow₀ (by norm_num)) β
  have hs (j : ℕ) (_hj : j∈range J) :
      Integrable (fun x => σ j*(Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x)-
        Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x))) volume := by
    have hd : Integrable (fun x => Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^(j+1)) β x)-
        Complex.ofReal (continuousAnnularKernel ((2 : ℕ)^j) β x)) volume :=
      ((hp j).sub (hm j)).congr (Filter.Eventually.of_forall (fun _ => rfl))
    exact hd.const_mul (σ j)
  rw [continuousAnnularSignedSymbol_untruncated]
  unfold continuousAnnularSignedKernel
  rw [realFourier_finsetSum (range J) _ hs]
  apply sum_congr rfl
  intro j _
  rw [realFourier_smul,realFourier_sub (hp j) (hm j),
    continuousAnnularKernel_fourier (one_le_pow₀ (by norm_num)) β θ,
    continuousAnnularKernel_fourier (one_le_pow₀ (by norm_num)) β θ]

end PrimeSquares
