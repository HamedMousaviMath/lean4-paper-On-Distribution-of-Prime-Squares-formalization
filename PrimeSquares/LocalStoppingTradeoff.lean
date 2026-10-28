import PrimeSquares.LocalStoppingHypotheses

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def localStoppingLowConstant {C v s r γ β A : ℝ}
    (P : LocalStoppingFamily C v s r γ β A) (D : ℝ) : ℝ :=
  P.constant*D*(1+(10:ℝ)^s*(Real.log 2)^(-γ))

noncomputable def localStoppingHighConstant {C v s r γ β A : ℝ}
    (P : LocalStoppingFamily C v s r γ β A) : ℝ :=
  P.constant*(1+dyadicLogSquareConstant A)

theorem localStopping_low_pointwise {C v s r γ β A D L J : ℝ}
    (P : LocalStoppingFamily C v s r γ β A) (hv : v < 1) (hγ : 0 ≤ γ)
    (hD : 0 ≤ D) (hL : 0 < L) (hJ : 2 ≤ J) (j : ℕ) (F : Finset ℤ) (x : ℤ)
    (hadm : linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) :
    ‖(if localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ)
      then P.Lo J j (finiteIndicatorLp F 2) x else P.B j (finiteIndicatorLp F 2) x)‖ ≤
      localStoppingLowConstant P D*((F.card:ℝ)/L)*J^s*(Real.log J)^γ := by
  have hPc := P.constant_pos.le
  have hlog : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hfac : 0 ≤ (10:ℝ)^s*(Real.log 2)^(-γ) := by positivity
  split_ifs with hlarge
  · have hh := (P.low J hJ j (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hlarge) F x).trans
      (mul_le_mul_of_nonneg_left hadm (by positivity))
    calc
      _ ≤ P.constant*J^s*(Real.log J)^γ*(D*((F.card:ℝ)/L)) := hh
      _ ≤ localStoppingLowConstant P D*((F.card:ℝ)/L)*J^s*(Real.log J)^γ := by
        unfold localStoppingLowConstant
        have hm : P.constant*D ≤ P.constant*D*(1+(10:ℝ)^s*(Real.log 2)^(-γ)) := by
          nlinarith [mul_nonneg (mul_nonneg hPc hD) hfac]
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (F.card:ℝ)/L))
            (by positivity : 0 ≤ J^s)) (by positivity : 0 ≤ (Real.log J)^γ)
        convert this using 1; ring
  · have hh := localStopping_small_pointwise P hv hγ hJ j F x (lt_of_not_ge hlarge) hadm
    apply hh.trans
    unfold localStoppingLowConstant
    have hm : P.constant*D*(10:ℝ)^s*(Real.log 2)^(-γ) ≤
        P.constant*D*(1+(10:ℝ)^s*(Real.log 2)^(-γ)) := by
      nlinarith [mul_nonneg hPc hD]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by positivity))
      (by positivity)

theorem localStopping_finite_tradeoff {C v s r γ β A D L J : ℝ}
    (P : LocalStoppingFamily C v s r γ β A) (hv : v < 1) (hγ : 0 ≤ γ)
    (hA : 1/2 < A) (hD : 0 ≤ D) (hL : 0 < L) (hJ : 2 ≤ J)
    (F G : Finset ℤ) (τ : ℤ → ℕ)
    (hadm : ∀ x ∈ G,
      linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) :
    ‖∑ x ∈ G,P.B (τ x) (finiteIndicatorLp F 2) x‖ ≤
      (G.card:ℝ)*(localStoppingLowConstant P D*((F.card:ℝ)/L)*J^s*(Real.log J)^γ)+
        (localStoppingHighConstant P*J^(-r)*(Real.log J)^β*Real.sqrt (F.card:ℝ))*Real.sqrt (G.card:ℝ) := by
  have hPc := P.constant_pos.le
  have hlog : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
  obtain ⟨H,hH0,hHpoint,hHnorm⟩ := P.high J hJ (finiteIndicatorLp F 2)
  obtain ⟨E,hE0,hEpoint,hEnorm⟩ := localError_square_majorant hA
    (by positivity : 0 ≤ P.constant*J^(-r)*(Real.log J)^β) (P.Er J) (P.error J hJ)
      (finiteIndicatorLp F 2)
  let large := fun x : ℤ => localSplittingThreshold v s J ≤ (((2:ℕ)^(τ x):ℕ):ℝ)
  let lo := fun x : ℤ => if large x then P.Lo J (τ x) (finiteIndicatorLp F 2) x
    else P.B (τ x) (finiteIndicatorLp F 2) x
  let hi := fun x : ℤ => if large x then P.Hi J (τ x) (finiteIndicatorLp F 2) x else 0
  let er := fun x : ℤ => if large x then P.Er J (τ x) (finiteIndicatorLp F 2) x else 0
  have heq (x : ℤ) (_hx : x ∈ G) : P.B (τ x) (finiteIndicatorLp F 2) x=lo x+hi x+er x := by
    dsimp [lo,hi,er]
    split_ifs with hh
    · exact P.decomposition J hJ (τ x) (by simpa only [large,Nat.cast_pow,Nat.cast_ofNat] using hh) F x
    · simp
  have hlo (x : ℤ) (hx : x ∈ G) : ‖lo x‖ ≤
      localStoppingLowConstant P D*((F.card:ℝ)/L)*J^s*(Real.log J)^γ :=
    localStopping_low_pointwise P hv hγ hD hL hJ (τ x) F x (hadm x hx)
  have hhi (x : ℤ) (_hx : x ∈ G) : ‖hi x‖ ≤ H x := by
    dsimp [hi]
    split_ifs with hh
    · exact hHpoint _ (by simpa only [large,Nat.cast_pow,Nat.cast_ofNat] using hh) x
    · simpa only [norm_zero] using hH0 x
  have her (x : ℤ) (_hx : x ∈ G) : ‖er x‖ ≤ E x := by
    dsimp [er]
    split_ifs
    · exact hEpoint _ x
    · simpa only [norm_zero] using hE0 x
  have hnorm : ‖H‖+‖E‖ ≤ localStoppingHighConstant P*J^(-r)*(Real.log J)^β*Real.sqrt (F.card:ℝ) := by
    have hh := add_le_add hHnorm hEnorm
    simp only [finiteIndicatorLp_two_norm] at hh
    apply hh.trans_eq
    unfold localStoppingHighConstant
    ring
  exact (finite_threePiece_majorant_bound G _ lo hi er H E _ heq hlo hhi her).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _)))

end PrimeSquares
