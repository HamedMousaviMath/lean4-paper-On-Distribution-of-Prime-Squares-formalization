import PrimeSquares.SourceArcCutoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open scoped ContDiff
namespace PrimeSquares

theorem sourceArcCutoff_compact : HasCompactSupport sourceArcCutoff :=
  sourceArcBump.hasCompactSupport

theorem complexSourceCutoff_compact : HasCompactSupport (fun x : ℝ => Complex.ofReal (sourceArcCutoff x)) :=
  sourceArcCutoff_compact.comp_left Complex.ofReal_zero

theorem complexSourceCutoff_smooth : ContDiff ℝ ∞ (fun x : ℝ => Complex.ofReal (sourceArcCutoff x)) :=
  Complex.ofRealCLM.contDiff.comp sourceArcCutoff_contDiff

noncomputable def sourceCutoffSchwartz : SchwartzMap ℝ ℂ :=
  complexSourceCutoff_compact.toSchwartzMap complexSourceCutoff_smooth

theorem sourceCutoffSchwartz_apply (x : ℝ) : sourceCutoffSchwartz x = Complex.ofReal (sourceArcCutoff x) := rfl

end PrimeSquares
