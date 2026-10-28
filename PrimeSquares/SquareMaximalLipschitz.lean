import PrimeSquares.SummableOperatorSquares

open scoped lp
namespace PrimeSquares

theorem squareOperatorMax_add (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖^2)) (f g : ℓ²(ℤ, ℂ)) (x : ℤ) :
    squareMaximumValue (fun j => T j (f+g)) x ≤
      squareMaximumValue (fun j => T j f) x+squareMaximumValue (fun j => T j g) x := by
  apply ciSup_le
  intro j
  have hf := le_ciSup (squareMaximumValue_bddAbove _ (operator_output_square_summable T hT f) x) j
  have hg := le_ciSup (squareMaximumValue_bddAbove _ (operator_output_square_summable T hT g) x) j
  change ‖T j (f+g) x‖ ≤ _
  rw [map_add,lp.coeFn_add,Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add hf hg)

theorem squareOperatorMax_difference (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖^2)) (f g : ℓ²(ℤ, ℂ)) (x : ℤ) :
    |squareMaximumValue (fun j => T j f) x-squareMaximumValue (fun j => T j g) x| ≤
      squareMaximumValue (fun j => T j (f-g)) x := by
  have h₁ := squareOperatorMax_add T hT (f-g) g x
  rw [sub_add_cancel] at h₁
  have h₂ := squareOperatorMax_add T hT (g-f) f x
  rw [sub_add_cancel] at h₂
  have he : squareMaximumValue (fun j => T j (g-f)) x=squareMaximumValue (fun j => T j (f-g)) x := by
    unfold squareMaximumValue
    apply iSup_congr
    intro j
    change ‖T j (g-f) x‖=‖T j (f-g) x‖
    rw [show g-f=-(f-g) by abel]
    have hn := congrArg (fun v : ℓ²(ℤ, ℂ) => ‖v x‖) ((T j).map_neg (f-g))
    simpa only [lp.coeFn_neg,Pi.neg_apply,norm_neg] using hn
  rw [he] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem squareOperatorMax_L2_difference (T : ℕ → ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hT : Summable (fun j : ℕ => ‖T j‖^2)) (f g : ℓ²(ℤ, ℂ)) :
    ‖squareMaximumL2 (fun j => T j f) (operator_output_square_summable T hT f)-
      squareMaximumL2 (fun j => T j g) (operator_output_square_summable T hT g)‖ ≤
        Real.sqrt (∑' j : ℕ,‖T j‖^2)*‖f-g‖ := by
  apply le_trans _ (operator_squares_countable_maximal T hT (f-g))
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro x
  change ‖squareMaximumValue (fun j => T j f) x-squareMaximumValue (fun j => T j g) x‖ ≤
    ‖squareMaximumValue (fun j => T j (f-g)) x‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg
    (squareMaximumValue_nonneg _ (operator_output_square_summable T hT (f-g)) x)]
  exact squareOperatorMax_difference T hT f g x

end PrimeSquares
