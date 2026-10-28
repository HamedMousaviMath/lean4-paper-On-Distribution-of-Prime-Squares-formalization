import PrimeSquares.LocalStoppingHypotheses

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

/-- The low and local hypotheses are required only for the current indicator
and testing set. K is a parameter shared by all estimates, so final constants
can be uniform over F,G and families satisfying these bounds. -/
structure LocalizedStoppingFamily (F G : Finset ℤ) (C v s r γ β A K : ℝ) where
  B : ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  Lo : ℝ → ℕ → ℓ²(ℤ,ℂ) → ℤ → ℂ
  Hi : ℝ → ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  Er : ℝ → ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  local_bound : ∀ j : ℕ,∀ x ∈ G,
    ‖B j (finiteIndicatorLp F 2) x‖ ≤
      K*((2:ℝ)^j)^(1-v)*linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℕ)^j)
  decomposition : ∀ J : ℝ,2 ≤ J → ∀ j : ℕ,
    localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ) → ∀ x ∈ G,
      B j (finiteIndicatorLp F 2) x=Lo J j (finiteIndicatorLp F 2) x+
        Hi J j (finiteIndicatorLp F 2) x+Er J j (finiteIndicatorLp F 2) x
  low : ∀ J : ℝ,2 ≤ J → ∀ j : ℕ,
    localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ) → ∀ x ∈ G,
      ‖Lo J j (finiteIndicatorLp F 2) x‖ ≤
        K*J^s*(Real.log J)^γ*linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x
  high : ∀ J : ℝ,2 ≤ J → ∀ f : ℓ²(ℤ,ℂ),∃ H : ℓ²(ℤ,ℝ),
    (∀ x,0 ≤ H x) ∧
      (∀ j : ℕ,localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ) → ∀ x,‖Hi J j f x‖ ≤ H x) ∧
      ‖H‖ ≤ K*J^(-r)*(Real.log J)^β*‖f‖
  error : ∀ J : ℝ,2 ≤ J → ∀ j : ℕ,
    ‖Er J j‖ ≤ K*J^(-r)*(Real.log J)^β*(1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A)

noncomputable def localizedLowConstant (K D s γ : ℝ) : ℝ :=
  K*D*(1+(10:ℝ)^s*(Real.log 2)^(-γ))

noncomputable def localizedHighConstant (K A : ℝ) : ℝ :=
  K*(1+dyadicLogSquareConstant A)

theorem localizedStopping_low_pointwise {C v s r γ β A K D L J : ℝ}
    {F G : Finset ℤ} (P : LocalizedStoppingFamily F G C v s r γ β A K) (hK : 0 ≤ K) (hv : v < 1) (hγ : 0 ≤ γ)
    (hD : 0 ≤ D) (hL : 0 < L) (hJ : 2 ≤ J) (j : ℕ) (x : ℤ) (hx : x ∈ G)
    (hadm : linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) :
    ‖(if localSplittingThreshold v s J ≤ (((2:ℕ)^j:ℕ):ℝ)
      then P.Lo J j (finiteIndicatorLp F 2) x else P.B j (finiteIndicatorLp F 2) x)‖ ≤
      localizedLowConstant K D s γ*((F.card:ℝ)/L)*J^s*(Real.log J)^γ := by
  have hPc := hK
  have hlog : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
  have hlog2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have hfac : 0 ≤ (10:ℝ)^s*(Real.log 2)^(-γ) := by positivity
  split_ifs with hlarge
  · have hh := (P.low J hJ j hlarge x hx).trans
      (mul_le_mul_of_nonneg_left hadm (by positivity))
    calc
      _ ≤ K*J^s*(Real.log J)^γ*(D*((F.card:ℝ)/L)) := hh
      _ ≤ localizedLowConstant K D s γ*((F.card:ℝ)/L)*J^s*(Real.log J)^γ := by
        unfold localizedLowConstant
        have hm : K*D ≤ K*D*(1+(10:ℝ)^s*(Real.log 2)^(-γ)) := by
          nlinarith [mul_nonneg (mul_nonneg hPc hD) hfac]
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (F.card:ℝ)/L))
            (by positivity : 0 ≤ J^s)) (by positivity : 0 ≤ (Real.log J)^γ)
        convert this using 1; ring
  · have hN : 1 ≤ (2:ℕ)^j := one_le_pow₀ (by norm_num)
    have hball := (linearSourceBallMass_le_local hN C (finiteIndicatorLp F 1) x _ le_rfl).trans hadm
    have hscale := (small_local_scale_growth (M:=(((2:ℕ)^j:ℕ):ℝ)) (s:=s) hv
      (by linarith : 0 < J) (by positivity) (lt_of_not_ge hlarge)).trans
        (local_small_scale_log_absorption hγ hJ)
    have hscale' : ((2:ℝ)^j)^(1-v) ≤ ((10:ℝ)^s*(Real.log 2)^(-γ))*J^s*(Real.log J)^γ := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hscale
    have hball' : linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℝ)^j) ≤ D*((F.card:ℝ)/L) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hball
    have hbase := P.local_bound j x hx
    simp only [Nat.cast_ofNat] at hbase
    have hh : ‖P.B j (finiteIndicatorLp F 2) x‖ ≤
        (K*D*(10:ℝ)^s*(Real.log 2)^(-γ))*((F.card:ℝ)/L)*J^s*(Real.log J)^γ := by
      calc
        _ ≤ K*((2:ℝ)^j)^(1-v)*linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℝ)^j) := hbase
        _ ≤ K*(((10:ℝ)^s*(Real.log 2)^(-γ))*J^s*(Real.log J)^γ)*(D*((F.card:ℝ)/L)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hscale' hK) hball'
            (linearSourceBallMass_nonneg C _ x _ (by positivity)) (by positivity)
        _ = _ := by ring
    apply hh.trans
    unfold localizedLowConstant
    have hm : K*D*(10:ℝ)^s*(Real.log 2)^(-γ) ≤
        K*D*(1+(10:ℝ)^s*(Real.log 2)^(-γ)) := by
      nlinarith [mul_nonneg hPc hD]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm (by positivity)) (by positivity))
      (by positivity)

theorem localizedStopping_finite_tradeoff {C v s r γ β A K D L J : ℝ}
    (F G : Finset ℤ) (P : LocalizedStoppingFamily F G C v s r γ β A K) (hK : 0 ≤ K) (hv : v < 1) (hγ : 0 ≤ γ)
    (hA : 1/2 < A) (hD : 0 ≤ D) (hL : 0 < L) (hJ : 2 ≤ J)
    (τ : ℤ → ℕ)
    (hadm : ∀ x ∈ G,
      linearSourceLocalMass C ((2:ℕ)^(τ x)) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) :
    ‖∑ x ∈ G,P.B (τ x) (finiteIndicatorLp F 2) x‖ ≤
      (G.card:ℝ)*(localizedLowConstant K D s γ*((F.card:ℝ)/L)*J^s*(Real.log J)^γ)+
        (localizedHighConstant K A*J^(-r)*(Real.log J)^β*Real.sqrt (F.card:ℝ))*Real.sqrt (G.card:ℝ) := by
  have hPc := hK
  have hlog : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
  obtain ⟨H,hH0,hHpoint,hHnorm⟩ := P.high J hJ (finiteIndicatorLp F 2)
  obtain ⟨E,hE0,hEpoint,hEnorm⟩ := localError_square_majorant hA
    (by positivity : 0 ≤ K*J^(-r)*(Real.log J)^β) (P.Er J) (P.error J hJ)
      (finiteIndicatorLp F 2)
  let large := fun x : ℤ => localSplittingThreshold v s J ≤ (((2:ℕ)^(τ x):ℕ):ℝ)
  let lo := fun x : ℤ => if large x then P.Lo J (τ x) (finiteIndicatorLp F 2) x
    else P.B (τ x) (finiteIndicatorLp F 2) x
  let hi := fun x : ℤ => if large x then P.Hi J (τ x) (finiteIndicatorLp F 2) x else 0
  let er := fun x : ℤ => if large x then P.Er J (τ x) (finiteIndicatorLp F 2) x else 0
  have heq (x : ℤ) (hx : x ∈ G) : P.B (τ x) (finiteIndicatorLp F 2) x=lo x+hi x+er x := by
    dsimp [lo,hi,er]
    split_ifs with hh
    · exact P.decomposition J hJ (τ x) hh x hx
    · simp
  have hlo (x : ℤ) (hx : x ∈ G) : ‖lo x‖ ≤
      localizedLowConstant K D s γ*((F.card:ℝ)/L)*J^s*(Real.log J)^γ :=
    localizedStopping_low_pointwise P hK hv hγ hD hL hJ (τ x) x hx (hadm x hx)
  have hhi (x : ℤ) (_hx : x ∈ G) : ‖hi x‖ ≤ H x := by
    dsimp [hi]
    split_ifs with hh
    · exact hHpoint _ hh x
    · simpa only [norm_zero] using hH0 x
  have her (x : ℤ) (_hx : x ∈ G) : ‖er x‖ ≤ E x := by
    dsimp [er]
    split_ifs
    · exact hEpoint _ x
    · simpa only [norm_zero] using hE0 x
  have hnorm : ‖H‖+‖E‖ ≤ localizedHighConstant K A*J^(-r)*(Real.log J)^β*Real.sqrt (F.card:ℝ) := by
    have hh := add_le_add hHnorm hEnorm
    simp only [finiteIndicatorLp_two_norm] at hh
    apply hh.trans_eq
    unfold localizedHighConstant
    ring
  exact (finite_threePiece_majorant_bound G _ lo hi er H E _ heq hlo hhi her).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hnorm (Real.sqrt_nonneg _)))

end PrimeSquares
