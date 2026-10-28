import PrimeSquares.FiniteComplexInputs
import PrimeSquares.RestrictedPowers

/-!
# Finite-output complex norm duality

Finite tests recover the genuine output lp norm. The phase of the test
matches the output; the pairing conjugates the test. Zero coordinates,
empty output sets and a zero bound are included.
-/

open Finset
open scoped lp

namespace PrimeSquares

theorem holderConjugate_sub_mul {p : ℝ} (hp : 1 < p) :
    (holderConjugate p - 1) * p = holderConjugate p := by
  unfold holderConjugate
  field_simp [ne_of_gt (show 0 < p - 1 by linarith)]
  ring

theorem holderConjugate_two_le {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    2 ≤ holderConjugate p := by
  unfold holderConjugate
  apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
  linarith

noncomputable def finiteDualTest (r : ℝ) (z : ℂ) : ℂ :=
  ((‖z‖ ^ (r - 2) : ℝ) : ℂ) * z

theorem finiteDualTest_norm {r : ℝ} (hr : 2 ≤ r) (z : ℂ) :
    ‖finiteDualTest r z‖ = ‖z‖ ^ (r - 1) := by
  by_cases hz : z = 0
  · subst z
    simp [finiteDualTest, Real.zero_rpow (by linarith : r - 1 ≠ 0)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [finiteDualTest, norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
  calc
    _ = ‖z‖ ^ (r - 2) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem finiteDualTest_pairing {r : ℝ} (hr : 2 ≤ r) (z : ℂ) :
    z * star (finiteDualTest r z) = ((‖z‖ ^ r : ℝ) : ℂ) := by
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow (by linarith : r ≠ 0)]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : ‖z‖ ^ (r - 2) * ‖z‖ ^ 2 = ‖z‖ ^ r := by
    rw [← Real.rpow_two, ← Real.rpow_add hn]
    congr 1
    ring
  simp only [finiteDualTest, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((‖z‖ ^ (r - 2) : ℝ) : ℂ) * (z * (starRingEnd ℂ) z) := by ring
    _ = ((‖z‖ ^ (r - 2) : ℝ) : ℂ) * (‖z‖ : ℂ) ^ 2 := by rw [Complex.mul_conj']
    _ = ((‖z‖ ^ (r - 2) * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    _ = _ := by rw [he]

theorem finiteDualTest_norm_rpow {p r : ℝ} (hr : 2 ≤ r)
    (hconj : (r - 1) * p = r) (z : ℂ) :
    ‖finiteDualTest r z‖ ^ p = ‖z‖ ^ r := by
  rw [finiteDualTest_norm hr, ← Real.rpow_mul (norm_nonneg _), hconj]

theorem duality_power_cancel {S M p r : ℝ} (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hr : 0 < r) (hrecip : 1 / r = 1 - 1 / p)
    (h : S ≤ M * S ^ (1 / p)) : S ≤ M ^ r := by
  by_cases hz : S = 0
  · subst S
    exact Real.rpow_nonneg hM _
  have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
  have hsum : 1 / r + 1 / p = 1 := by linarith
  have hprod : S ^ (1 / r) * S ^ (1 / p) = S := by
    rw [← Real.rpow_add hpos, hsum, Real.rpow_one]
  have hroot : S ^ (1 / r) ≤ M :=
    (mul_le_mul_iff_of_pos_right (Real.rpow_pos_of_pos hpos (1 / p))).mp
      (by rw [hprod]; exact h)
  calc
    S = (S ^ (1 / r)) ^ r := by
      rw [← Real.rpow_mul hS, one_div_mul_cancel hr.ne', Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hS _) hroot hr.le

theorem finite_output_power_bound {P : ENNReal} [Fact (1 ≤ P)]
    (hp : 1 < P.toReal) (hp2 : P.toReal ≤ 2) {M : ℝ} (hM : 0 ≤ M)
    (u : ℤ → ℂ)
    (hpair : ∀ (G : Finset ℤ) (g : ℤ → ℂ),
      ‖∑ x ∈ G, u x * star (g x)‖ ≤ M * ‖finiteInputLp G g P‖)
    (G : Finset ℤ) :
    ∑ x ∈ G, ‖u x‖ ^ holderConjugate P.toReal ≤ M ^ holderConjugate P.toReal := by
  let r := holderConjugate P.toReal
  have hr : 2 ≤ r := holderConjugate_two_le hp hp2
  have hS : 0 ≤ ∑ x ∈ G, ‖u x‖ ^ r := sum_nonneg fun x _ => by positivity
  have htest : ‖finiteInputLp G (fun x => finiteDualTest r (u x)) P‖ =
      (∑ x ∈ G, ‖u x‖ ^ r) ^ (1 / P.toReal) := by
    rw [finiteInputLp_norm G _ P (by linarith)]
    simp_rw [finiteDualTest_norm_rpow hr (holderConjugate_sub_mul hp)]
  have hidentity : (∑ x ∈ G, u x * star (finiteDualTest r (u x))) =
      ((∑ x ∈ G, ‖u x‖ ^ r : ℝ) : ℂ) := by
    simp_rw [finiteDualTest_pairing hr]
    push_cast
    rfl
  have hh := hpair G (fun x => finiteDualTest r (u x))
  rw [hidentity, Complex.norm_of_nonneg hS, htest] at hh
  exact duality_power_cancel hS hM (holderConjugate_pos hp)
    (holderConjugate_reciprocal hp) hh

theorem lp_norm_le_of_finite_pairing {P Q : ENNReal} [Fact (1 ≤ P)] [Fact (1 ≤ Q)]
    (hp : 1 < P.toReal) (hp2 : P.toReal ≤ 2)
    (hQ : Q.toReal = holderConjugate P.toReal) {M : ℝ} (hM : 0 ≤ M)
    (u : lp (fun _ : ℤ => ℂ) Q)
    (hpair : ∀ (G : Finset ℤ) (g : ℤ → ℂ),
      ‖∑ x ∈ G, u x * star (g x)‖ ≤ M * ‖finiteInputLp G g P‖) : ‖u‖ ≤ M := by
  apply lp.norm_le_of_forall_sum_le (by rw [hQ]; exact holderConjugate_pos hp) hM
  intro G
  rw [hQ]
  exact finite_output_power_bound hp hp2 hM u hpair G

end PrimeSquares
