import PrimeSquares.SourceLargeRemainderPrefixBridge
import PrimeSquares.SourceCollarSubhalfMaximum
open Finset MeasureTheory
open scoped lp
namespace PrimeSquares
theorem sourceHigh_from_large_majorant {η : ℝ} (hη : 0 ≤ η) (hηhalf : η<1/2) :
    ∃ K : ℝ,0<K ∧ ∀ (M : ℕ) (hM : 2 ≤ M) (Q : ℝ),1 ≤ Q →
    ∀ (q₀ : ℕ → ℕ),(∀ i,2^i ≤ q₀ i) → ∀ (R : ℕ → ℝ),(∀ j,Q ≤ R j) →
    ∀ (active : ℕ → ℕ → Bool) (χ : ∀ _i _j : ℕ,∀ r : ℚ,DirichletCharacter ℂ r.den)
      (β : ℕ → ℕ → ℝ),(∀ i j,0 ≤ β i j) → (∀ i j,β i j ≤ 1) →
    ∀ (σ : ℕ → ℕ) (f : ℓ²(ℤ,ℂ)) (gl : lp (fun _ : ℤ => ℝ) 2),
    (∀ x,0 ≤ gl x) →
    (∀ j x,‖integerMultiplier (sourceLargeHighRemainder ((2 : ℕ)^j*M)
      (by have hh := dyadic_annular_scale_lower hM j;omega) Q (R j) (q₀ (σ j))
      (active (σ j) j) (χ (σ j) j) (β (σ j) j)) f x‖ ≤ gl x) →
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0 ≤ g x) ∧
      (∀ j x,‖circleHighOperator (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
        (by have hh := dyadic_annular_scale_lower hM j;omega) (q₀ (σ j)) Q
        (conductorMajorant (q₀ (σ j))) (χ (σ j) j)
        (sourceExceptionalSelector (q₀ (σ j)) (active (σ j) j)) (β (σ j) j) f x‖ ≤ g x) ∧
      ‖g‖ ≤ K*Q^(-η)*‖f‖+‖gl‖ := by
  obtain ⟨K,hK,hC⟩ := sourceCollar_subhalf_maximum hη hηhalf
  refine ⟨K,hK,?_⟩
  intro M hM Q hQ q₀ hclass R hQR active χ β hβ0 hβ1 σ f gl hgl hlarge
  obtain ⟨gc,_,hgc,hc,hn⟩ := hC M hM Q hQ q₀ hclass R hQR active χ β hβ0 hβ1 σ f
  refine ⟨gc+gl,fun x => add_nonneg (hgc x) (hgl x),?_,(norm_add_le gc gl).trans (by linarith)⟩
  intro j x
  have hq : 0<q₀ (σ j) := lt_of_lt_of_le (pow_pos (by norm_num) _) (hclass (σ j))
  rw [circleHighOperator_collar_remainder _ _ (by linarith : 0<Q) hq (hQR j),
    _root_.add_apply,lp.coeFn_add,Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (hc j x) (hlarge j x))
end PrimeSquares
