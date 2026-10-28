import PrimeSquares.GoldbachSieveResidues

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- Finite Abel summation with nonnegative decreasing real weights. Its only
sum hypothesis is the displayed bound on the actual partial sums. -/
theorem goldbach_finite_abel_bound (a : ℕ→ℝ) (z : ℕ→ℂ) (n : ℕ) {B : ℝ}
    (hB : 0≤B) (ha : ∀ i,0≤a i) (hanti : Antitone a)
    (hG : ∀ k : ℕ,k≤n → ‖∑ j∈range k,z j‖≤B) :
    ‖∑ i∈range n,a i • z i‖≤B*a 0 := by
  by_cases hn : n=0
  · simp only [hn,range_zero,sum_empty,norm_zero]
    exact mul_nonneg hB (ha 0)
  rw [sum_range_by_parts]
  have hlast : ‖a (n-1) • ∑ i∈range n,z i‖≤a (n-1)*B := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ha (n-1))]
    exact mul_le_mul_of_nonneg_left (hG n le_rfl) (ha (n-1))
  have hdiff (i : ℕ) (hi : i∈range (n-1)) :
      ‖(a (i+1)-a i) • ∑ j∈range (i+1),z j‖≤(a i-a (i+1))*B := by
    have hd : a (i+1)≤a i := hanti (Nat.le_succ i)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hd),neg_sub]
    exact mul_le_mul_of_nonneg_left (hG (i+1) (by have := mem_range.mp hi; omega))
      (sub_nonneg.mpr hd)
  calc
    _≤‖a (n-1) • ∑ i∈range n,z i‖+
      ‖∑ i∈range (n-1),(a (i+1)-a i) • ∑ j∈range (i+1),z j‖ := norm_sub_le _ _
    _≤a (n-1)*B+∑ i∈range (n-1),(a i-a (i+1))*B :=
      add_le_add hlast ((norm_sum_le _ _).trans (sum_le_sum hdiff))
    _=_ := by rw [←sum_mul,sum_range_sub']; ring

/-- Clipping only at 2 makes the logarithmic weight monotone even at 0 and1.
The von-Mangoldt coefficients at those two indices vanish. -/
noncomputable def goldbachLogRemovalWeight (n : ℕ) : ℝ :=
  1/Real.log (max 2 (n:ℝ))

theorem goldbachLogRemovalWeight_nonneg (n : ℕ) : 0≤goldbachLogRemovalWeight n := by
  unfold goldbachLogRemovalWeight
  exact one_div_nonneg.mpr (Real.log_nonneg ((by norm_num : (1:ℝ)≤2).trans (le_max_left _ _)))

theorem goldbachLogRemovalWeight_antitone : Antitone goldbachLogRemovalWeight := by
  intro m n hmn
  unfold goldbachLogRemovalWeight
  apply one_div_le_one_div_of_le
  · exact Real.log_pos ((by norm_num : (1:ℝ)<2).trans_le (le_max_left _ _))
  · apply Real.log_le_log (by positivity)
    exact max_le_max_left 2 (by exact_mod_cast hmn)

theorem goldbachLogRemovalWeight_zero : goldbachLogRemovalWeight 0=1/Real.log 2 := by
  simp [goldbachLogRemovalWeight]

theorem goldbachLogRemovalWeight_of_two_le {n : ℕ} (hn : 2≤n) :
    goldbachLogRemovalWeight n=1/Real.log n := by
  unfold goldbachLogRemovalWeight
  rw [max_eq_right (by exact_mod_cast hn : (2:ℝ)≤n)]

end PrimeSquares
