import PrimeSquares.RationalCollarDyadicPartition

open Finset
namespace PrimeSquares

theorem completeRationalCollar_finite_energy {M : ℕ} (hM : 2 ≤ M) (Γ : Finset ℚ)
    (hΓ : ∀ r ∈ Γ,r ∈ Set.Ico (0 : ℚ) 1) {Q C δ : ℝ}
    (hQ : 1 ≤ Q) (hC : 0 < C) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hden : ∀ r ∈ Γ,r.den ≤ ⌊Q⌋₊)
    (β : ℕ → ℚ → ℝ) (hβ0 : ∀ j,∀ r ∈ Γ,0 ≤ β j r) (hβ1 : ∀ j,∀ r ∈ Γ,β j r ≤ 1)
    (c : ℕ → ℚ → ℂ) (hc : ∀ j,∀ r ∈ Γ,‖c j r‖ ≤ C*(r.den : ℝ)^(-δ))
    (J : Finset ℕ) (θ : PrimeCircle) :
    (∑ j ∈ J,‖rationalCollarBlock Γ ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j) θ‖^2) ≤
      (collarPowerConstant C δ*Q^(-δ))^2 := by
  classical
  let S := range (Nat.log2 ⌊Q⌋₊+1)
  let B (s : ℕ) := (192*C/(Real.pi*Q))*((2 : ℝ)^(1-δ))^s
  let m (j s : ℕ) := rationalCollarBlock (Γ.filter (fun r => Nat.log2 r.den=s)) ((2 : ℕ)^j*M)
    (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j)
  have hQp : 0 < Q := by linarith
  have hB : ∀ s ∈ S,0 < B s := fun s _ => by dsimp [B];have hp := Real.pi_pos;positivity
  have hE : ∀ s ∈ S,∀ I : Finset ℕ,∀ t : PrimeCircle,(∑ j ∈ I,‖m j s t‖^2) ≤ (B s)^2 := by
    intro s _ I t
    apply rationalCollarBlock_power_energy hM _ s
    · intro r hr
      exact hΓ r (mem_filter.mp hr).1
    · intro r hr
      exact (mem_filter.mp hr).2
    · exact hQp
    · exact hC.le
    · exact hδ0
    · intro j r hr
      exact hβ0 j r (mem_filter.mp hr).1
    · intro j r hr
      exact hβ1 j r (mem_filter.mp hr).1
    · intro j r hr
      exact hc j r (mem_filter.mp hr).1
  have he (j : ℕ) : rationalCollarBlock Γ ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) Q (β j) (c j)=∑ s ∈ S,m j s :=
    rationalCollarBlock_dyadic_partition Γ _ _ _ hden Q (β j) (c j)
  calc
    _ = ∑ j ∈ J,‖(∑ s ∈ S,m j s) θ‖^2 := sum_congr rfl (fun j _ => by rw [he j])
    _ ≤ (∑ s ∈ S,B s)^2 := finite_circle_energy_assemble S m B hB hE J θ
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg (fun s hs => (hB s hs).le)) (collar_block_constant_sum hQ hC.le hδ1) 2

end PrimeSquares
