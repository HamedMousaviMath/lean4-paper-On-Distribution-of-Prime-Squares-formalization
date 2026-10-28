import PrimeSquares.ActualSourceLowRemainderBounds
import PrimeSquares.OperatorMaximalNorm

open scoped lp
namespace PrimeSquares

theorem dyadic_cutoff_inverse_power_summable {Q η : ℝ} (hQ : 0 < Q) (hη : 0 < η) :
    Summable (fun j : ℕ => ((2 : ℝ)^j*Q)^(-η)) := by
  have hr0 : 0 ≤ (2 : ℝ)^(-η) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ)^(-η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hη)
  have hs := (hasSum_geometric_of_norm_lt_one (ξ := (2 : ℝ)^(-η)) (by simpa only [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)).summable.mul_right (Q^(-η))
  convert hs using 1
  ext j
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2^j) hQ.le]
  congr 1
  calc
    _ = (2 : ℝ)^((j : ℝ)*(-η)) := (Real.rpow_natCast_mul (by norm_num) j (-η)).symm
    _ = (2 : ℝ)^((-η)*(j : ℝ)) := congrArg (fun z : ℝ => (2 : ℝ)^z) (mul_comm (j : ℝ) (-η))
    _ = _ := Real.rpow_mul_natCast (by norm_num) (-η) j

theorem actualHigh_summable_cutoff_maximum {η : ℝ} (hη0 : 0 < η) (hηhalf : η < 1/2) :
    ∃ H : ℝ,0 < H ∧ ∀ (N : ℕ → ℕ) (hN : ∀ j,2 ≤ N j) (Q : ℕ → ℝ),
      (∀ j,0 < Q j) → Summable (fun j => (Q j)^(-η)) →
    ∀ (q₀ : ℕ → ℕ) [∀ j,NeZero (q₀ j)] (M : ℕ → ℕ) (Γ : ℕ → Finset ℚ),
      (∀ j,∀ r ∈ Γ j,r ∈ Set.Ico (0 : ℚ) 1 ∧ r.den ≤ M j) →
    ∀ (χ : ∀ _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den) (κ : ℕ → ℚ → ℂ) (β : ℕ → ℝ),
      (∀ j,0 ≤ β j) → (∀ j,β j ≤ 1) → (∀ j,∀ r ∈ Γ j,‖κ j r‖ ≤ 1) → ∀ f : ℓ²(ℤ,ℂ),
      ∃ g : lp (fun _ : ℤ => ℝ) 2,
        (∀ x,g x=⨆ j : ℕ,‖circleHighOperator (Γ j) (N j) (by have hh := hN j;omega) (q₀ j) (Q j)
          (conductorMajorant (q₀ j)) (χ j) (κ j) (β j) f x‖) ∧
        ‖g‖ ≤ H*(∑' j : ℕ,(Q j)^(-η))*‖f‖ := by
  obtain ⟨H,hH,hh⟩ := sourceHigh_power_uniform hη0 hηhalf
  refine ⟨H,hH,?_⟩
  intro N hN Q hQ hsum q₀ inst M Γ hΓ χ κ β hβ0 hβ1 hk f
  let T (j : ℕ) := circleHighOperator (Γ j) (N j) (by have hn := hN j;omega) (q₀ j) (Q j)
    (conductorMajorant (q₀ j)) (χ j) (κ j) (β j)
  have hb : ∀ j,‖T j‖ ≤ H*(Q j)^(-η) := fun j =>
    (hh (N j) (hN j) (Q j) (hQ j) (q₀ j) (M j) (Γ j) (hΓ j) (χ j) (κ j) (β j) (hβ0 j) (hβ1 j) (hk j)).2
  have hs : Summable (fun j => ‖T j‖) := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb (hsum.mul_left H)
  refine ⟨operatorMaximalL2 T hs f,fun _ => rfl,?_⟩
  have ht : (∑' j : ℕ,‖T j‖) ≤ H*(∑' j : ℕ,(Q j)^(-η)) := by
    simpa only [tsum_mul_left] using hs.tsum_le_tsum hb (hsum.mul_left H)
  exact (operatorMaximalL2_norm_bound T hs f).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))

end PrimeSquares
