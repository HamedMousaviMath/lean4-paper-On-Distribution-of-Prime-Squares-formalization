import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def absoluteDyadicPotential (x : ℝ) : ℝ := 1/(1+x)

theorem absoluteDyadicPotential_range {x : ℝ} (hx : 0≤x) :
    0≤absoluteDyadicPotential x ∧ absoluteDyadicPotential x≤1 := by
  unfold absoluteDyadicPotential
  exact ⟨by positivity,(div_le_one (by positivity)).mpr (by linarith)⟩

theorem absoluteDyadicPotential_difference {x : ℝ} (hx : 0≤x) :
    absoluteDyadicPotential x-absoluteDyadicPotential (4*x)=3*x/((1+x)*(1+4*x)) := by
  unfold absoluteDyadicPotential
  have h1 : 1+x≠0 := ne_of_gt (by positivity)
  have h2 : 1+4*x≠0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem absoluteDyadicPotential_near {x : ℝ} (hx : 0≤x) (h1 : x≤1) :
    x≤(10/3 : ℝ)*(absoluteDyadicPotential x-absoluteDyadicPotential (4*x)) := by
  have hx2 : x^2≤x := by nlinarith
  have hd : (1+x)*(1+4*x)≤10 := by nlinarith
  rw [absoluteDyadicPotential_difference hx]
  calc
    _ ≤ 10*x/((1+x)*(1+4*x)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hd hx]
    _ = _ := by ring

theorem absoluteDyadicPotential_far {x : ℝ} (h1 : 1≤x) :
    x⁻¹≤(10/3 : ℝ)*(absoluteDyadicPotential x-absoluteDyadicPotential (4*x)) := by
  have hx : 0<x := by linarith
  have hx2 : x≤x^2 := by nlinarith
  have hd : (1+x)*(1+4*x)≤10*x^2 := by nlinarith
  rw [absoluteDyadicPotential_difference hx.le]
  calc
    _ = 1/x := (one_div _).symm
    _ ≤ 10*x/((1+x)*(1+4*x)) := by
      apply (div_le_div_iff₀ hx (by positivity)).mpr
      nlinarith
    _ = _ := by ring

theorem absoluteDyadicProfile_bound {x : ℝ} (hx : 0≤x) :
    min x x⁻¹≤(10/3 : ℝ)*(absoluteDyadicPotential x-absoluteDyadicPotential (4*x)) := by
  by_cases h : x≤1
  · exact (min_le_left _ _).trans (absoluteDyadicPotential_near hx h)
  · exact (min_le_right _ _).trans (absoluteDyadicPotential_far (le_of_lt (lt_of_not_ge h)))

theorem two_sided_absolute_profile {C y z : ℝ} (hy : 0≤y)
    (hnear : z≤C*y) (hfar : y*z≤C) : z≤C*min y y⁻¹ := by
  by_cases h : y≤y⁻¹
  · rw [min_eq_left h]
    exact hnear
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    have hp : 0<y := by
      by_contra hn
      have he : y=0 := le_antisymm (le_of_not_gt hn) hy
      simp only [he,inv_zero,le_refl,not_true_eq_false] at h
    have hb : z≤C/y := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hfar)
    simpa only [div_eq_mul_inv] using hb

theorem absoluteDyadicPotential_telescoping (x : ℝ) (J : ℕ) :
    (∑ j∈range J,(absoluteDyadicPotential ((4 : ℝ)^j*x)-
      absoluteDyadicPotential ((4 : ℝ)^(j+1)*x)))=
      absoluteDyadicPotential x-absoluteDyadicPotential ((4 : ℝ)^J*x) := by
  induction J with
  | zero => simp
  | succ J ih => rw [sum_range_succ,ih];ring

theorem dyadic_absolute_profile_sum {x : ℝ} (hx : 0≤x) (J : ℕ) :
    (∑ j∈range J,min ((4 : ℝ)^j*x) (((4 : ℝ)^j*x)⁻¹))≤10/3 := by
  calc
    _ ≤ ∑ j∈range J,(10/3 : ℝ)*(absoluteDyadicPotential ((4 : ℝ)^j*x)-
        absoluteDyadicPotential ((4 : ℝ)^(j+1)*x)) := by
      apply sum_le_sum
      intro j _
      have h := absoluteDyadicProfile_bound (mul_nonneg (by positivity : (0 : ℝ)≤4^j) hx)
      simpa only [pow_succ,show (4 : ℝ)^j*4*x=4*((4 : ℝ)^j*x) by ring] using h
    _ = (10/3 : ℝ)*(absoluteDyadicPotential x-absoluteDyadicPotential ((4 : ℝ)^J*x)) := by
      rw [←mul_sum,absoluteDyadicPotential_telescoping]
    _ ≤ _ := by
      have h0 := (absoluteDyadicPotential_range (mul_nonneg (by positivity : (0 : ℝ)≤4^J) hx)).1
      have h1 := (absoluteDyadicPotential_range hx).2
      linarith

end PrimeSquares
