import PrimeSquares.LinearLocalMass
import PrimeSquares.LocalErrorSquareMaximum
import PrimeSquares.HighLowCappedBalance
import PrimeSquares.StoppingPairingMajorants

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def localSplittingThreshold (v s J : ℝ) : ℝ := (10*J)^(s/(1-v))

/-- The functional norm form of the printed abstract local hypotheses.
The family is indexed by j with physical scale2^j. No local pairing or
endpoint conclusion is a field. Positivity of B is unnecessary after its
printed absolute local bound has been supplied. -/
structure LocalStoppingFamily (C v s r γ β A : ℝ) where
  B : ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  Lo : ℝ → ℕ → ℓ²(ℤ,ℂ) → ℤ → ℂ
  Hi : ℝ → ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  Er : ℝ → ℕ → ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ)
  constant : ℝ
  constant_pos : 0 < constant
  local_bound : ∀ (j : ℕ) (F : Finset ℤ) (x : ℤ),
    ‖B j (finiteIndicatorLp F 2) x‖ ≤
      constant*((2:ℝ)^j)^(1-v)*linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℕ)^j)
  decomposition : ∀ J : ℝ, 2 ≤ J → ∀ j : ℕ,
    localSplittingThreshold v s J ≤ (2:ℕ)^j → ∀ (F : Finset ℤ) (x : ℤ),
      B j (finiteIndicatorLp F 2) x=
        Lo J j (finiteIndicatorLp F 2) x+Hi J j (finiteIndicatorLp F 2) x+
          Er J j (finiteIndicatorLp F 2) x
  low : ∀ J : ℝ, 2 ≤ J → ∀ j : ℕ,
    localSplittingThreshold v s J ≤ (2:ℕ)^j → ∀ (F : Finset ℤ) (x : ℤ),
      ‖Lo J j (finiteIndicatorLp F 2) x‖ ≤
        constant*J^s*(Real.log J)^γ*linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x
  high : ∀ J : ℝ, 2 ≤ J → ∀ f : ℓ²(ℤ,ℂ), ∃ H : ℓ²(ℤ,ℝ),
    (∀ x,0 ≤ H x) ∧
      (∀ j : ℕ,localSplittingThreshold v s J ≤ (2:ℕ)^j → ∀ x,‖Hi J j f x‖ ≤ H x) ∧
      ‖H‖ ≤ constant*J^(-r)*(Real.log J)^β*‖f‖
  error : ∀ J : ℝ, 2 ≤ J → ∀ j : ℕ,
    ‖Er J j‖ ≤ constant*J^(-r)*(Real.log J)^β*(1+Real.log (((2:ℕ)^j:ℕ):ℝ))^(-A)

theorem localSplittingThreshold_power {v s J : ℝ} (hv : v < 1) (hJ : 0 < J) :
    (localSplittingThreshold v s J)^(1-v)=(10*J)^s := by
  have hd : 1-v ≠ 0 := by linarith
  unfold localSplittingThreshold
  rw [←Real.rpow_mul (by positivity : (0:ℝ) ≤ 10*J)]
  congr 1
  field_simp

theorem small_local_scale_growth {v s J M : ℝ} (hv : v < 1) (hJ : 0 < J)
    (hM : 0 ≤ M) (hsmall : M < localSplittingThreshold v s J) :
    M^(1-v) ≤ (10*J)^s := by
  rw [←localSplittingThreshold_power hv hJ]
  exact Real.rpow_le_rpow hM hsmall.le (by linarith)

theorem local_small_scale_log_absorption {s γ J : ℝ} (hγ : 0 ≤ γ) (hJ : 2 ≤ J) :
    (10*J)^s ≤ ((10:ℝ)^s*(Real.log 2)^(-γ))*J^s*(Real.log J)^γ := by
  have hJp : 0 < J := by linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogJ : Real.log 2 ≤ Real.log J := Real.log_le_log (by norm_num) hJ
  have hcan : (Real.log 2)^(-γ)*(Real.log 2)^γ=1 := by
    rw [←Real.rpow_add hlog2]
    simp
  have hge : 1 ≤ (Real.log 2)^(-γ)*(Real.log J)^γ := by
    rw [←hcan]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hlog2.le hlogJ hγ) (by positivity)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) hJp.le]
  calc
    _ ≤ ((10:ℝ)^s*J^s)*((Real.log 2)^(-γ)*(Real.log J)^γ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hge (by positivity : 0 ≤ (10:ℝ)^s*J^s)
    _ = _ := by ring

theorem localStopping_small_pointwise {C v s r γ β A D L J : ℝ}
    (P : LocalStoppingFamily C v s r γ β A) (hv : v < 1) (hγ : 0 ≤ γ)
    (hJ : 2 ≤ J) (j : ℕ) (F : Finset ℤ) (x : ℤ)
    (hsmall : (((2:ℕ)^j:ℕ):ℝ) < localSplittingThreshold v s J)
    (hadm : linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x ≤ D*((F.card:ℝ)/L)) :
    ‖P.B j (finiteIndicatorLp F 2) x‖ ≤
      (P.constant*D*(10:ℝ)^s*(Real.log 2)^(-γ))*((F.card:ℝ)/L)*J^s*(Real.log J)^γ := by
  have hN : 1 ≤ (2:ℕ)^j := one_le_pow₀ (by norm_num)
  have hBall := (linearSourceBallMass_le_local hN C (finiteIndicatorLp F 1) x _ le_rfl).trans hadm
  have hBall' : linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℝ)^j) ≤ D*((F.card:ℝ)/L) := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hBall
  have hbase := P.local_bound j F x
  simp only [Nat.cast_ofNat] at hbase
  have hPc := P.constant_pos.le
  have hlogJ0 : 0 ≤ Real.log J := Real.log_nonneg (by linarith : 1 ≤ J)
  have hScale := (small_local_scale_growth (M := (((2:ℕ)^j:ℕ):ℝ)) (s := s) hv
    (by linarith : 0 < J) (by positivity) hsmall).trans (local_small_scale_log_absorption hγ hJ)
  have hScale' : ((2:ℝ)^j)^(1-v) ≤ ((10:ℝ)^s*(Real.log 2)^(-γ))*J^s*(Real.log J)^γ := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hScale
  calc
    _ ≤ P.constant*((2:ℝ)^j)^(1-v)*linearSourceBallMass C (finiteIndicatorLp F 1) x ((2:ℝ)^j) := hbase
    _ ≤ P.constant*(((10:ℝ)^s*(Real.log 2)^(-γ))*J^s*(Real.log J)^γ)*(D*((F.card:ℝ)/L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hScale' hPc) hBall'
        (linearSourceBallMass_nonneg C _ x _ (by positivity)) (by positivity)
    _ = _ := by ring

end PrimeSquares
