import PrimeSquares.QuadraticOscillation
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

namespace PrimeSquares

noncomputable def realFourierPhase (u : ℝ) : ℂ :=
  Complex.exp (Complex.ofReal (2*Real.pi*u)*Complex.I)

theorem realFourierPhase_norm (u : ℝ) : ‖realFourierPhase u‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem realFourierPhase_continuous : Continuous realFourierPhase := by
  unfold realFourierPhase
  fun_prop

theorem realFourierPhase_add (u v : ℝ) : realFourierPhase (u+v)=realFourierPhase u*realFourierPhase v := by
  unfold realFourierPhase
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realFourierPhase_quadratic (θ t : ℝ) : quadraticOscillation θ t=realFourierPhase (-θ*t^2) := by
  unfold quadraticOscillation realFourierPhase
  congr 1
  push_cast
  ring

end PrimeSquares
