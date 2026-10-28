import PrimeSquares.LinearLocalRadiusComparison
import PrimeSquares.SourceLocalMass

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem sourceBallMass_eq_linear (f : ℓ¹(ℤ,ℂ)) (x : ℤ) (M : ℝ) :
    sourceBallMass f x M=linearSourceBallMass 1 f x (M^2) := by
  simp only [sourceBallMass,linearSourceBallMass,one_mul]

theorem sourceLocalMass_eq_linear_square {N : ℕ} (hN : 1 ≤ N)
    (f : ℓ¹(ℤ,ℂ)) (x : ℤ) :
    sourceLocalMass N f x=linearSourceLocalMass 1 (N^2) f x := by
  have hN2 : 1 ≤ N^2 := one_le_pow₀ hN
  have hNr : (0:ℝ)≤N := Nat.cast_nonneg _
  apply le_antisymm
  · apply ciSup_le
    intro M
    rw [sourceBallMass_eq_linear]
    apply linearSourceBallMass_le_local hN2
    have hM0 : (0:ℝ)≤M := hNr.trans M.property
    simpa only [Nat.cast_pow] using (sq_le_sq₀ hNr hM0).2 M.property
  · apply ciSup_le
    intro R
    have hR0 : (0:ℝ)≤R := (Nat.cast_nonneg (N^2)).trans R.property
    have hM : (N:ℝ)≤Real.sqrt (R:ℝ) := by
      calc
        _ = Real.sqrt ((N:ℝ)^2) := (Real.sqrt_sq hNr).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by simpa only [Set.mem_Ici,Nat.cast_pow] using R.property)
    have h := sourceBallMass_le_local hN f x (Real.sqrt R) hM
    rw [sourceBallMass_eq_linear,Real.sq_sqrt hR0] at h
    exact h

theorem sourceLocalMass_from_quadratic_radius {N : ℕ} (hN : 1 ≤ N)
    {C B : ℝ} (hC : 0 < C) (F : Finset ℤ) (x : ℤ)
    (hadm : ∀ M : ℝ,(N:ℝ) ≤ M →
      (linearWindowCount C (M^2) F x:ℝ)/M^2 ≤ B) :
    sourceLocalMass N (finiteIndicatorLp F 1) x ≤ max 1 (1/C)*B := by
  have hN2 : 1 ≤ N^2 := one_le_pow₀ hN
  have hlocal : linearSourceLocalMass C (N^2) (finiteIndicatorLp F 1) x ≤ B := by
    apply (linearSourceLocalMass_le_iff hN2 C _ x _).mpr
    intro R hR
    have hR0 : 0 ≤ R := (Nat.cast_nonneg (N^2)).trans hR
    have hM : (N:ℝ)≤Real.sqrt R := by
      calc
        _ = Real.sqrt ((N:ℝ)^2) := (Real.sqrt_sq (Nat.cast_nonneg _)).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by simpa only [Nat.cast_pow] using hR)
    have h := hadm (Real.sqrt R) hM
    rw [Real.sq_sqrt hR0] at h
    simpa only [linearSourceBallMass_indicator] using h
  rw [sourceLocalMass_eq_linear_square hN]
  exact (linearSourceLocalMass_change_radius (C:=1) hN2 hC _ x).trans
    (mul_le_mul_of_nonneg_left hlocal (by have h:=le_max_left (1:ℝ) (1/C); linarith))

end PrimeSquares
