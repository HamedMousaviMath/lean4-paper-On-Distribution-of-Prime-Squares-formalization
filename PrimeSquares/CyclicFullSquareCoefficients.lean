import PrimeSquares.CompleteQuadraticGaussBound
import PrimeSquares.CyclicRationalGaussDecay

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem finite_add_group_pullback_average {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (φ : G →+ H) (hφ : Function.Surjective φ) (F : H → ℂ) :
    (Fintype.card G : ℂ)⁻¹*∑ g : G, F (φ g) =
      (Fintype.card H : ℂ)⁻¹*∑ h : H, F h := by
  classical
  have hs (h : H) : ∑ g : G, F (φ g+h) = ∑ g : G, F (φ g) := by
    obtain ⟨v, rfl⟩ := hφ h
    simp_rw [←map_add]
    exact Equiv.sum_comp (Equiv.addRight v) (fun g : G => F (φ g))
  have ht (g : G) : ∑ h : H, F (φ g+h) = ∑ h : H, F h :=
    Equiv.sum_comp (Equiv.addLeft (φ g)) F
  have he : (Fintype.card H : ℂ)*(∑ g : G, F (φ g)) =
      (Fintype.card G : ℂ)*(∑ h : H, F h) := by
    calc
      _ = ∑ h : H, ∑ g : G, F (φ g) := by simp
      _ = ∑ h : H, ∑ g : G, F (φ g+h) := sum_congr rfl (fun h _ => (hs h).symm)
      _ = ∑ g : G, ∑ h : H, F (φ g+h) := sum_comm
      _ = _ := by simp_rw [ht]; simp
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination he

noncomputable def normalizedCompleteGauss (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (q : ℂ)⁻¹*completeQuadraticGaussSum q a

noncomputable def rationalFullSquareGauss (r : ℚ) : ℂ :=
  letI : NeZero r.den := ⟨r.den_pos.ne'⟩
  normalizedCompleteGauss r.den (-(r.num : ZMod r.den))

theorem normalizedCompleteGauss_norm_one (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖normalizedCompleteGauss q a‖ ≤ 1 := by
  have h := cyclicFullSquareMeasure_fourier_norm_le_one q (-a)
  rw [cyclicFullSquareMeasure_fourier, neg_neg] at h
  exact h

theorem normalizedCompleteGauss_decay (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    ‖normalizedCompleteGauss q a‖ ≤ 2*(q : ℝ)^(-(1/2 : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hs : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq
  have hs2 := Real.sq_sqrt hq.le
  have hg := completeQuadraticGaussSum_norm_le q a ha
  have he : (q : ℝ)^(-(1/2 : ℝ)) = (Real.sqrt (q : ℝ))⁻¹ := by
    rw [Real.rpow_neg hq.le, ←Real.sqrt_eq_rpow]
  rw [normalizedCompleteGauss, norm_mul, norm_inv, norm_natCast, he]
  calc
    _ ≤ (q : ℝ)⁻¹*(2*Real.sqrt (q : ℝ)) := mul_le_mul_of_nonneg_left hg (inv_pos.mpr hq).le
    _ = _ := by field_simp; nlinarith

theorem rationalFullSquareGauss_norm_one (r : ℚ) : ‖rationalFullSquareGauss r‖ ≤ 1 := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  exact normalizedCompleteGauss_norm_one r.den _

theorem rationalFullSquareGauss_decay (r : ℚ) :
    ‖rationalFullSquareGauss r‖ ≤ 2*(r.den : ℝ)^(-(3/8 : ℝ)) := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  have ha : IsUnit (r.num : ZMod r.den) :=
    (ZMod.coe_int_isUnit_iff_isCoprime r.num r.den).mpr r.isCoprime_num_den.symm
  exact (normalizedCompleteGauss_decay r.den _ ha.neg).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast r.den_pos : (1 : ℝ) ≤ r.den) (by norm_num : -(1/2 : ℝ) ≤ -(3/8 : ℝ))) (by norm_num))

theorem cyclicReducedFullSquare {q P : ℕ} [NeZero q] [NeZero P]
    (hd : q ∣ P) (a : ZMod q) :
    cyclicReducedFourier hd (cyclicFullSquareMeasure P) a = normalizedCompleteGauss q (-a) := by
  rw [cyclicReducedFourier, cyclicFullSquareMeasure_test]
  let φ : ZMod P →+ ZMod q :=
    { toFun := ZMod.castHom hd (ZMod q)
      map_zero' := map_zero _
      map_add' := map_add _ }
  have he := finite_add_group_pullback_average φ (ZMod.castHom_surjective hd)
    (fun u : ZMod q => ZMod.stdAddChar (-a*u^2))
  simpa [φ, normalizedCompleteGauss, completeQuadraticGaussSum, neg_mul, ZMod.cast_pow hd] using he

theorem cyclicRationalCoefficient_fullSquare {P : ℕ} [NeZero P] (r : ℚ) (hd : r.den ∣ P) :
    cyclicRationalCoefficient P (cyclicFullSquareMeasure P) r = rationalFullSquareGauss r := by
  have : NeZero r.den := ⟨r.den_pos.ne'⟩
  rw [cyclicRationalCoefficient_eq_reduced _ r hd, cyclicReducedFullSquare]
  rfl

end PrimeSquares
