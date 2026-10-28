import PrimeSquares.QuadraticCharacterExpansion

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def quadraticSoftCorrelation (p : ℕ) [Fact p.Prime]
    (S : Finset (ZMod p)) : ℝ := ∑ t : ZMod p, ∏ h ∈ S, quadraticSoftIndicator p (t+h)

theorem quadraticCorrelation_as_product (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) :
    quadraticCorrelation p S = ∑ t : ZMod p, ∏ h ∈ S, unitSquareIndicator p (t+h) := by
  classical
  simp only [unitSquareIndicator, Finset.prod_boole]
  unfold quadraticCorrelation
  rw [show ((Finset.univ.filter (fun t : ZMod p => ∀ h ∈ S,
    t+h ∈ unitSquareResidues p)).card : ℝ) =
      ∑ t ∈ Finset.univ.filter (fun t : ZMod p => ∀ h ∈ S,
        t+h ∈ unitSquareResidues p), (1 : ℝ) by simp]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : ∀ h ∈ S, t+h ∈ unitSquareResidues p
  · simp only [ite_eq_left ht]
  · simp only [ite_eq_right ht]

theorem quadraticSoft_product_nonneg (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p))
    (t : ZMod p) : 0 ≤ ∏ h ∈ S, quadraticSoftIndicator p (t+h) :=
  Finset.prod_nonneg (fun _ _ => (quadraticSoftIndicator_bounds p _).1)

theorem quadraticSoft_product_le_one (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p))
    (t : ZMod p) : (∏ h ∈ S, quadraticSoftIndicator p (t+h)) ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => (quadraticSoftIndicator_bounds p _).1)
    (fun _ _ => (quadraticSoftIndicator_bounds p _).2)

theorem quadraticSoft_product_correction (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p))
    (t : ZMod p) :
    0 ≤ (∏ h ∈ S, quadraticSoftIndicator p (t+h))-
        (∏ h ∈ S, unitSquareIndicator p (t+h)) ∧
      (∏ h ∈ S, quadraticSoftIndicator p (t+h))-
        (∏ h ∈ S, unitSquareIndicator p (t+h)) ≤
          ∑ h ∈ S, (if t+h=0 then (1 : ℝ) else 0) := by
  classical
  have hI : 0 ≤ ∏ h ∈ S, unitSquareIndicator p (t+h) :=
    Finset.prod_nonneg (fun _ _ => (unitSquareIndicator_bounds p _).1)
  have hle : (∏ h ∈ S, unitSquareIndicator p (t+h)) ≤
      ∏ h ∈ S, quadraticSoftIndicator p (t+h) := by
    apply Finset.prod_le_prod₀ (fun _ _ => (unitSquareIndicator_bounds p _).1)
    intro h _
    rw [quadraticSoftIndicator_eq]
    split_ifs <;> linarith
  refine ⟨sub_nonneg.mpr hle, ?_⟩
  by_cases he : ∃ h ∈ S, t+h=0
  · obtain ⟨h, hh, hz⟩ := he
    have hsum : (1 : ℝ) ≤ ∑ h ∈ S, (if t+h=0 then 1 else 0) := by
      have hs := Finset.single_le_sum (f:=fun h => if t+h=0 then (1 : ℝ) else 0)
        (fun _ _ => by positivity) hh
      simpa only [ite_eq_left hz] using hs
    have hJ := quadraticSoft_product_le_one p S t
    linarith
  · have hzero : ∀ h ∈ S, t+h ≠ 0 := by simpa only [not_exists, not_and] using he
    have heq : (∏ h ∈ S, quadraticSoftIndicator p (t+h)) =
        ∏ h ∈ S, unitSquareIndicator p (t+h) := by
      apply Finset.prod_congr rfl
      intro h hh
      simp only [quadraticSoftIndicator_eq, ite_eq_right (hzero h hh), zero_div, add_zero]
    rw [heq, sub_self]
    exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem quadraticSoftCorrelation_error (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) :
    0 ≤ quadraticSoftCorrelation p S-quadraticCorrelation p S ∧
      quadraticSoftCorrelation p S-quadraticCorrelation p S ≤ S.card := by
  classical
  rw [quadraticSoftCorrelation, quadraticCorrelation_as_product, ←Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun t _ => (quadraticSoft_product_correction p S t).1), ?_⟩
  calc
    _ ≤ ∑ t : ZMod p, ∑ h ∈ S, (if t+h=0 then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun t _ => (quadraticSoft_product_correction p S t).2)
    _ = S.card := by rw [Finset.sum_comm]; simp [add_eq_zero_iff_eq_neg]

end PrimeSquares
