import PrimeSquares.UniformPageHighMaximum

open scoped lp
namespace PrimeSquares

/-- The harmless bounded-Q convention: this agrees with sqrt(log Q)/log log Q
as soon as log Q >= 2. It avoids the singular unregularized expression in a
range where the source explicitly absorbs bounded Q into the constant. -/
noncomputable def regularizedHighExponentWeight (Q : ℝ) : ℝ :=
  sharpHighExponentWeight (max 2 (Real.log Q))

theorem regularizedHighExponentWeight_pos (Q : ℝ) : 0<regularizedHighExponentWeight Q :=
  sharpHighExponentWeight_pos (le_max_left _ _)

theorem regularizedHighExponentWeight_eq {Q : ℝ} (hQ : 2 ≤ Real.log Q) :
    regularizedHighExponentWeight Q=Real.sqrt (Real.log Q)/Real.log (Real.log Q) := by
  rw [regularizedHighExponentWeight,max_eq_right hQ,sharpHighExponentWeight]

/-- Proposition6.21, with both conclusions, in precise epsilon form. The
entire bounded-Q range is included. The constant is uniform in the starting
threshold and in every compatible choice of the source exceptional data.
Only the stated general prime-asymptotic, smooth multifrequency and Page
inputs remain unproved. No maximal statement of this paper is a hypothesis. -/
theorem proposition621 (HP : PrimeAsymptoticInputs)
    {C c : ℝ} (hC : 0 ≤ C) (hBourgain : SmoothCircleBourgainInput C)
    (hc : 0<c) (hPage : RawPageUniquenessInput c) {ε : ℝ} (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ Q : ℝ,2 ≤ Q → ∀ N₀ : ℝ,2 ≤ N₀ →
    ∀ E : ℕ → Option PageZeroDatum,
      (∀ j F,N₀ ≤ (((2 : ℕ)^j*2 : ℕ) : ℝ) → E j=some F →
        (F.conductor : ℝ) ≤ sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q ∧
        1-(c/2)/Real.log (sourceMajorArcScale (((2 : ℕ)^j*2 : ℕ) : ℝ) Q)<F.beta) →
    ∀ f : ℓ²(ℤ,ℂ),∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,G x=⨆ j : ℕ,‖sourcePageDyadicTailOperator N₀ Q E j f x‖) ∧
      (∀ x,0 ≤ G x) ∧ (∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ G x) ∧
      ‖G‖ ≤ (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*regularizedHighExponentWeight Q))*‖f‖ ∧
      (∀ j,‖sourcePageDyadicTailOperator N₀ Q E j f‖ ≤
        (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*regularizedHighExponentWeight Q))*‖f‖) := by
  classical
  obtain ⟨Q₀,Ka,hQ₀,hKa,hlarge⟩ := proposition621_maximal_asymptotic HP hC hBourgain hc hPage hε
  obtain ⟨Kb,hKb,hbounded⟩ := sourcePageDyadicTail_uniform hC hBourgain hc hPage
  have hQ₀p : 0<Q₀ := by linarith
  let K := Ka+Kb*Q₀^(1/2 : ℝ)
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨K,hK,?_⟩
  intro Q hQ N₀ hN₀ E hE f
  have hQp : 0<Q := by linarith
  have hex : ∃ G : lp (fun _ : ℤ => ℝ) 2,
      (∀ x,G x=⨆ j : ℕ,‖sourcePageDyadicTailOperator N₀ Q E j f x‖) ∧
      (∀ x,0 ≤ G x) ∧ (∀ j x,‖sourcePageDyadicTailOperator N₀ Q E j f x‖ ≤ G x) ∧
      ‖G‖ ≤ (K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*regularizedHighExponentWeight Q))*‖f‖ := by
    by_cases hlargeQ : Q₀ ≤ Q
    · obtain ⟨G,heq,h0,ht,hn,_⟩ := hlarge Q hlargeQ N₀ hN₀ E hE f
      have hlog16 : (2 : ℝ) ≤ Real.log 16 := by
        rw [show (16 : ℝ)=4^2 by norm_num,Real.log_pow]
        norm_num only [Nat.cast_ofNat]
        linarith [log_four_one_le]
      have hlogQ : 2 ≤ Real.log Q := hlog16.trans
        (Real.log_le_log (by norm_num : (0 : ℝ)<16) (hQ₀.trans hlargeQ))
      have he : regularizedHighExponentWeight Q=sharpHighExponentWeight (Real.log Q) := by
        unfold regularizedHighExponentWeight
        rw [max_eq_right hlogQ]
      have hKaK : Ka ≤ K := by dsimp [K];exact le_add_of_nonneg_right (by positivity)
      refine ⟨G,heq,h0,ht,hn.trans ?_⟩
      rw [he]
      gcongr
    · obtain ⟨G,heq,h0,ht,hn⟩ := hbounded Q hQ N₀ hN₀ E hE f
      have hpow : Q^(1/2 : ℝ) ≤ Q₀^(1/2 : ℝ) :=
        Real.rpow_le_rpow hQp.le (lt_of_not_ge hlargeQ).le (by norm_num)
      have hfactor : (1 : ℝ) ≤ Q₀^(1/2 : ℝ)*Q^(-(1/2 : ℝ)) := by
        rw [Real.rpow_neg hQp.le,←div_eq_mul_inv]
        exact (one_le_div (Real.rpow_pos_of_pos hQp (1/2 : ℝ))).mpr hpow
      have hExp : 1 ≤ Real.exp ((2+ε)*regularizedHighExponentWeight Q) :=
        Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) (regularizedHighExponentWeight_pos Q).le)
      have hKbK : Kb*Q₀^(1/2 : ℝ) ≤ K := by dsimp [K];linarith
      have hscalar : Kb ≤ K*Q^(-(1/2 : ℝ))*Real.exp ((2+ε)*regularizedHighExponentWeight Q) := by
        calc
          _ ≤ Kb*(Q₀^(1/2 : ℝ)*Q^(-(1/2 : ℝ))) := le_mul_of_one_le_right hKb.le hfactor
          _ = (Kb*Q₀^(1/2 : ℝ))*Q^(-(1/2 : ℝ)) := by ring
          _ ≤ K*Q^(-(1/2 : ℝ)) := mul_le_mul_of_nonneg_right hKbK (by positivity)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
      exact ⟨G,heq,h0,ht,hn.trans (mul_le_mul_of_nonneg_right hscalar (norm_nonneg f))⟩
  obtain ⟨G,heq,h0,ht,hn⟩ := hex
  exact ⟨G,heq,h0,ht,hn,fun j => (norm_le_nonnegative_majorant _ G h0 (ht j)).trans hn⟩

end PrimeSquares
