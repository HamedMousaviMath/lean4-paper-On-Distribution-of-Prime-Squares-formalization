import PrimeSquares.GenericFiniteSparse

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem positiveDyadicValue_translate {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (j : ℕ) (F : Finset ℤ) (x z : ℤ) :
    positiveDyadicValue T j (F.image (fun y => y-x+z)) z=positiveDyadicValue T j F x := by
  classical
  unfold positiveDyadicValue indicatorConvolution
  rw [Finset.sum_image (fun a _ b _ h => by omega)]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  omega

theorem positiveDyadicValue_le_interval_test {C : ℝ} (T : PositiveDyadicConvolutionFamily C)
    (I : SparseIntegerInterval) (m j : ℕ) (hC : C ≤ (m:ℝ))
    (hN : (2:ℕ)^j ≤ I.length) (F : Finset ℤ) (x : ℤ) {z : ℤ} (hz : z ∈ I.points) :
    ‖positiveDyadicValue T j F x‖ ≤ ‖positiveDyadicValue T j (I.oddDilate m).points z‖ := by
  let H := F.image (fun y => y-x+z)
  calc
    _ = ‖positiveDyadicValue T j H z‖ := congrArg norm (positiveDyadicValue_translate T j F x z).symm
    _ = ‖positiveDyadicValue T j (H ∩ (I.oddDilate m).points) z‖ := by
      rw [positiveDyadicValue_localize T I m j hC hN H hz]
    _ ≤ _ := nonnegativeKernel_indicator_norm_mono (T.nonnegative j) Finset.inter_subset_right z

theorem genericConstantStop_admissible (I : SparseIntegerInterval) (F : Finset ℤ)
    (C : ℝ) (j : ℕ) (hI : I.length=(2:ℕ)^j) (x : ℤ) :
    linearSourceLocalMass C ((2:ℕ)^j) (finiteIndicatorLp F 1) x ≤
      (320*max 1 C)*((F.card:ℝ)/I.length) := by
  have hN : 1 ≤ (2:ℕ)^j := one_le_pow₀ (by norm_num)
  have hL : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have hD : (1:ℝ)≤320*max 1 C := by have h:=le_max_left (1:ℝ) C; linarith
  have hb := linearSourceLocalMass_uniform hN C (finiteIndicatorLp F 1) x
  rw [finiteIndicatorLp_one_norm] at hb
  calc
    _ ≤ (((2:ℕ)^j:ℕ):ℝ)⁻¹*(F.card:ℝ) := hb
    _ = (F.card:ℝ)/I.length := by rw [hI]; ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (div_nonneg (Nat.cast_nonneg _) hL.le)

theorem genericLocalHypothesis_uniform_indicator_bound {C K : ℝ}
    (T : PositiveDyadicConvolutionFamily C) (m : ℕ) (hC : C ≤ (m:ℝ))
    (Ψ : ℝ → ℝ → ℝ) (hlocal : GenericRestrictedLocalEstimate T m Ψ K) :
    ∀ (j : ℕ) (F : Finset ℤ) (x : ℤ),
      ‖positiveDyadicValue T j F x‖ ≤ K*Ψ (2*(m:ℝ)+1) 1 := by
  intro j F x
  let I : SparseIntegerInterval := ⟨0,(2:ℕ)^j,by positivity⟩
  let E := (I.oddDilate m).points
  have hL : (0:ℝ)<I.length := by exact_mod_cast I.length_pos
  have htest := hlocal I E I.points (fun _ => j) Subset.rfl Subset.rfl
    (fun _ _ => le_rfl) (fun y _ => genericConstantStop_admissible I E C j rfl y)
  have hdf : (E.card:ℝ)/I.length=2*(m:ℝ)+1 := by
    rw [integerInterval_card_points]
    dsimp [SparseIntegerInterval.oddDilate]
    push_cast
    field_simp
  have hdg : (I.points.card:ℝ)/I.length=1 := by
    rw [integerInterval_card_points]
    exact div_self hL.ne'
  rw [hdf,hdg] at htest
  have hsum : (I.length:ℝ)*‖positiveDyadicValue T j F x‖ ≤
      ‖∑ z ∈ I.points,positiveDyadicValue T j E z‖ := by
    rw [finite_positive_pairing_norm I.points _ (fun z _ => positiveDyadicValue_positive T j E z)]
    have hh := Finset.sum_le_sum (fun z hz => positiveDyadicValue_le_interval_test T I m j hC le_rfl F x hz)
    simpa only [Finset.sum_const,nsmul_eq_mul,integerInterval_card_points] using hh
  have hh : (I.length:ℝ)*‖positiveDyadicValue T j F x‖ ≤
      (I.length:ℝ)*(K*Ψ (2*(m:ℝ)+1) 1) := (hsum.trans htest).trans_eq (by ring)
  exact (mul_le_mul_iff_of_pos_left hL).mp hh

end PrimeSquares
