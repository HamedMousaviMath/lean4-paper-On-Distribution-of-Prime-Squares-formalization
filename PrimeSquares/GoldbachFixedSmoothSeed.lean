import PrimeSquares.GoldbachPositiveSingularComplete
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
namespace PrimeSquares

noncomputable def goldbachTestBump : ContDiffBump (0:ℝ) where
  rIn := 1/32
  rOut := 1/16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def goldbachFixedSmoothSeed : SchwartzMap ℝ ℝ :=
  goldbachTestBump.hasCompactSupport.toSchwartzMap goldbachTestBump.contDiff

theorem goldbach_fixed_smooth_seed_at_zero : goldbachFixedSmoothSeed 0=1 := by
  change goldbachTestBump 0=1
  apply goldbachTestBump.one_of_mem_closedBall
  norm_num [Metric.mem_closedBall,goldbachTestBump]

theorem goldbach_fixed_smooth_seed_nonzero : goldbachFixedSmoothSeed≠0 := by
  intro h
  have hh := congrArg (fun f : SchwartzMap ℝ ℝ=>f 0) h
  rw [goldbach_fixed_smooth_seed_at_zero] at hh
  norm_num at hh

theorem goldbach_fixed_smooth_seed_support (x : ℝ) (hx : (1/8:ℝ)≤|x|) :
    goldbachFixedSmoothSeed x=0 := by
  change goldbachTestBump x=0
  apply goldbachTestBump.zero_of_le_dist
  change (1/16:ℝ)≤dist x 0
  rw [Real.dist_eq,sub_zero]
  linarith

theorem goldbach_fixed_smooth_seed_compact_support :
    HasCompactSupport (goldbachFixedSmoothSeed : ℝ→ℝ) := by
  change HasCompactSupport (goldbachTestBump : ℝ→ℝ)
  exact goldbachTestBump.hasCompactSupport

theorem goldbach_fixed_smooth_seed_tsupport_subset :
    tsupport (goldbachFixedSmoothSeed : ℝ→ℝ)⊆Set.Ioo (-(1/8:ℝ)) (1/8:ℝ) := by
  change tsupport (goldbachTestBump : ℝ→ℝ)⊆_
  rw [goldbachTestBump.tsupport_eq]
  intro x hx
  have hh := Metric.mem_closedBall.mp hx
  change dist x 0≤(1/16:ℝ) at hh
  rw [Real.dist_eq,sub_zero] at hh
  obtain ⟨hl,hu⟩ := abs_le.mp hh
  exact ⟨by linarith,by linarith⟩

theorem goldbach_smooth_seed_exists :
    ∃ ψ : SchwartzMap ℝ ℝ,ψ≠0 ∧ ∀ x : ℝ,(1/8:ℝ)≤|x|→ψ x=0 :=
  ⟨goldbachFixedSmoothSeed,goldbach_fixed_smooth_seed_nonzero,goldbach_fixed_smooth_seed_support⟩

end PrimeSquares
