import PrimeSquares.PrimeStoppingGeometry
import PrimeSquares.LinearLocalRadiusComparison
import PrimeSquares.LinearOneSidedAdmissibility

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem linearOneSided_bounds_of_symmetric {N : ℕ} (hN : 1 ≤ N)
    (C : ℝ) (F : Finset ℤ) (x : ℤ) (B : ℝ)
    (hB : linearSourceLocalMass C N (finiteIndicatorLp F 1) x ≤ B) :
    ∀ M : ℝ,(N:ℝ) ≤ M →
      (leftLinearWindowCount C M F x:ℝ)/M ≤ B ∧
        (rightLinearWindowCount C M F x:ℝ)/M ≤ B := by
  intro M hM
  have hM0 : 0 ≤ M := (Nat.cast_nonneg N).trans hM
  have hb := (linearSourceBallMass_le_local hN C (finiteIndicatorLp F 1) x M hM).trans hB
  rw [linearSourceBallMass_indicator] at hb
  obtain ⟨hl,hr,_⟩ := linearWindowCount_oneSided_compare C M F x
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hl) hM0).trans hb
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hr) hM0).trans hb

theorem linearSymmetric_bound_of_both_oneSided {N : ℕ} (hN : 1 ≤ N)
    (C : ℝ) (F : Finset ℤ) (x : ℤ) (B : ℝ)
    (hB : ∀ M : ℝ,(N:ℝ) ≤ M →
      (leftLinearWindowCount C M F x:ℝ)/M ≤ B ∧
        (rightLinearWindowCount C M F x:ℝ)/M ≤ B) :
    linearSourceLocalMass C N (finiteIndicatorLp F 1) x ≤ 2*B := by
  simpa only [two_mul] using linearSourceLocalMass_of_both_oneSided hN C F x B B
    (fun M hM => (hB M hM).1) (fun M hM => (hB M hM).2)

theorem linearBallMass_le_interval_count (F : Finset ℤ) (x : ℤ) {M : ℝ} (hM : 0 ≤ M)
    (J : SparseIntegerInterval)
    (hJ : ∀ y ∈ F,|((x-y:ℤ):ℝ)| ≤ M → y ∈ J.points) :
    linearSourceBallMass 1 (finiteIndicatorLp F 1) x M ≤ ((F ∩ J.points).card:ℝ)/M := by
  rw [linearSourceBallMass_indicator]
  apply div_le_div_of_nonneg_right _ hM
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro y hy
  have hh := Finset.mem_filter.mp hy
  exact Finset.mem_inter.mpr ⟨hh.1,hJ y hh.1 (by simpa only [one_mul] using hh.2)⟩

theorem goodPoint_linearSourceLocalMass (R : SparseIntegerInterval) (F : Finset ℤ) {t : ℝ}
    (ht : (F.card:ℝ)/R.length ≤ t) {N : ℕ} (hN : 1 ≤ N) {x z : ℤ}
    (hx : x ∈ R.points) (hclose : |((x-z:ℤ):ℝ)| ≤ (N:ℝ))
    (hgood : ∀ J : SparseIntegerInterval,J.points ⊆ R.five.points → z ∈ J.points →
      ((F ∩ J.points).card:ℝ) ≤ t*(J.length:ℝ)) :
    linearSourceLocalMass 1 N (finiteIndicatorLp F 1) x ≤ 5*t := by
  have hR : (0:ℝ)<R.length := by exact_mod_cast R.length_pos
  have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hR.le).trans ht
  apply ciSup_le
  intro M
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hM : (1:ℝ)≤M.val := hNr.trans M.property
  have hMpos : 0 < M.val := by linarith
  by_cases hlarge : (R.length:ℝ) ≤ M.val
  · have hh := linearSourceBallMass_uniform (Nat.succ_le_iff.mpr R.length_pos)
      M.val hlarge 1 (finiteIndicatorLp F 1) x
    rw [finiteIndicatorLp_one_norm] at hh
    calc
      _ ≤ (R.length:ℝ)⁻¹*(F.card:ℝ) := hh
      _ = (F.card:ℝ)/R.length := by ring
      _ ≤ t := ht
      _ ≤ 5*t := by linarith
  · let r := Nat.ceil M.val
    have hr : M.val ≤ (r:ℝ) := Nat.le_ceil _
    have hrR : r ≤ R.length := Nat.ceil_le.mpr (le_of_not_ge hlarge)
    let J := integerCenteredBall x r
    have hJsub : J.points ⊆ R.five.points := integerCenteredBall_subset_five R hx hrR
    have hzJ : z ∈ J.points := by
      rw [integerCenteredBall_mem]
      exact_mod_cast (hclose.trans M.property).trans hr
    have hcount := linearBallMass_le_interval_count F x hMpos.le J (fun y _ hy => by
      rw [integerCenteredBall_mem]
      exact_mod_cast hy.trans hr)
    have hsize : (J.length:ℝ) ≤ 5*M.val := by
      have hrup : (r:ℝ)<M.val+1 := Nat.ceil_lt_add_one hMpos.le
      change ((2*r+1:ℕ):ℝ) ≤ _
      push_cast
      linarith
    have hd : ((F ∩ J.points).card:ℝ) ≤ 5*t*M.val :=
      (hgood J hJsub hzJ).trans (by nlinarith [mul_le_mul_of_nonneg_left hsize ht0])
    calc
      _ ≤ ((F ∩ J.points).card:ℝ)/M.val := hcount
      _ ≤ (5*t*M.val)/M.val := div_le_div_of_nonneg_right hd hMpos.le
      _ = _ := by field_simp

theorem linearStopping_remaining_localMass (R : SparseIntegerInterval) (F : Finset ℤ)
    {N : ℕ} (hN : 1 ≤ N) {x : ℤ} (hx : x ∈ R.points)
    (hrem : ∀ I ∈ primeStoppingChildren R F,x ∈ I.points → I.length < N) :
    linearSourceLocalMass 1 N (finiteIndicatorLp F 1) x ≤ 320*((F.card:ℝ)/R.length) := by
  have hR : (0:ℝ)<R.length := by exact_mod_cast R.length_pos
  have hclose : ∃ z ∈ R.points,z ∉ primeStoppingBadSet R F ∧ |((x-z:ℤ):ℝ)| ≤ (N:ℝ) := by
    by_cases hbad : x ∈ primeStoppingBadSet R F
    · have hcov : x ∈ (primeStoppingChildren R F).biUnion SparseIntegerInterval.points := by
        rw [primeStoppingChildren_cover]
        exact hbad
      obtain ⟨I,hI,hxI⟩ := Finset.mem_biUnion.mp hcov
      obtain ⟨z,hzR,hzB,hdist⟩ := integerComponent_near_good hI hxI
        (integer_good_point_of_quarter_packing R _ (primeStoppingBadSet_packing R F))
      refine ⟨z,hzR,hzB,?_⟩
      have hd : |((x-z:ℤ):ℝ)| ≤ (I.length:ℝ) := by exact_mod_cast hdist
      exact hd.trans (by exact_mod_cast (hrem I hI hxI).le)
    · exact ⟨x,hx,hbad,by simp⟩
  obtain ⟨z,hzR,hzB,hdist⟩ := hclose
  have ht : (F.card:ℝ)/R.length ≤ primeStoppingThreshold R F := by
    have hp : 0 ≤ (F.card:ℝ)/R.length := div_nonneg (Nat.cast_nonneg _) hR.le
    dsimp [primeStoppingThreshold]
    rw [mul_div_assoc]
    nlinarith
  have h := goodPoint_linearSourceLocalMass R F ht hN hx hdist
    (fun J hJ hzJ => primeStopping_good_density hzR hzB J hJ hzJ)
  exact h.trans_eq (by dsimp [primeStoppingThreshold]; ring)

theorem linearStopping_remaining_radius (R : SparseIntegerInterval) (F : Finset ℤ)
    (C : ℝ) {N : ℕ} (hN : 1 ≤ N) {x : ℤ} (hx : x ∈ R.points)
    (hrem : ∀ I ∈ primeStoppingChildren R F,x ∈ I.points → I.length < N) :
    linearSourceLocalMass C N (finiteIndicatorLp F 1) x ≤
      (320*max 1 C)*((F.card:ℝ)/R.length) := by
  have hcomp := linearSourceLocalMass_change_radius (C:=C) hN (by norm_num : (0:ℝ)<1)
    (finiteIndicatorLp F 1) x
  simp only [div_one] at hcomp
  have hm : 0 ≤ max 1 C := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  exact (hcomp.trans (mul_le_mul_of_nonneg_left (linearStopping_remaining_localMass R F hN hx hrem) hm)).trans_eq
    (by ring)

end PrimeSquares
