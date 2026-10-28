import PrimeSquares.DyadicLocalMassBounds
import PrimeSquares.SparseIntegerIntervals
import PrimeSquares.AllInputFourierConvolution



set_option autoImplicit false
open Finset
open scoped lp

namespace PrimeSquares

theorem linearSourceBall_summable (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) (M : ℝ) :
    Summable (fun y : ℤ => if |((x-y : ℤ) : ℝ)| ≤ C*M then ‖f y‖ else 0) := by
  have hf : Summable (fun y : ℤ => ‖f y‖) := by simpa using f.2.summable
  exact hf.of_norm_bounded (fun y => by split_ifs <;> simp)

noncomputable def linearSourceBallMass (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) (M : ℝ) : ℝ :=
  M⁻¹ * ∑' y : ℤ, if |((x-y : ℤ) : ℝ)| ≤ C*M then ‖f y‖ else 0

theorem linearSourceBallMass_nonneg (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ linearSourceBallMass C f x M := by
  unfold linearSourceBallMass
  exact mul_nonneg (by positivity) (tsum_nonneg (fun y => by split_ifs <;> positivity))

theorem linearSourceBallMass_uniform {N : ℕ} (hN : 1 ≤ N) (M : ℝ) (hM : (N : ℝ) ≤ M)
    (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    linearSourceBallMass C f x M ≤ (N : ℝ)⁻¹ * ‖f‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hf : Summable (fun y : ℤ => ‖f y‖) := by simpa using f.2.summable
  have ht : (∑' y : ℤ, if |((x-y : ℤ) : ℝ)| ≤ C*M then ‖f y‖ else 0) ≤ ‖f‖ := by
    calc
      _ ≤ ∑' y : ℤ, ‖f y‖ := Summable.tsum_le_tsum
        (fun y => by split_ifs <;> simp) (linearSourceBall_summable C f x M) hf
      _ = ‖f‖ := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp
  exact mul_le_mul (inv_anti₀ hNr hM) ht
    (tsum_nonneg (fun y => by split_ifs <;> positivity)) (by positivity)

noncomputable def linearSourceLocalMass (C : ℝ) (N : ℕ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) : ℝ :=
  ⨆ M : Set.Ici (N : ℝ), linearSourceBallMass C f x M

theorem linearSourceLocalMass_bddAbove {N : ℕ} (hN : 1 ≤ N) (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    BddAbove (Set.range (fun M : Set.Ici (N : ℝ) => linearSourceBallMass C f x M)) := by
  refine ⟨(N : ℝ)⁻¹ * ‖f‖, ?_⟩
  rintro _ ⟨M, rfl⟩
  exact linearSourceBallMass_uniform hN M M.property C f x

theorem linearSourceBallMass_le_local {N : ℕ} (hN : 1 ≤ N) (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ)
    (M : ℝ) (hM : (N : ℝ) ≤ M) : linearSourceBallMass C f x M ≤ linearSourceLocalMass C N f x :=
  le_ciSup (linearSourceLocalMass_bddAbove hN C f x) ⟨M, hM⟩

theorem linearSourceLocalMass_nonneg {N : ℕ} (hN : 1 ≤ N) (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    0 ≤ linearSourceLocalMass C N f x :=
  (linearSourceBallMass_nonneg C f x N (Nat.cast_nonneg _)).trans (linearSourceBallMass_le_local hN C f x N le_rfl)

theorem linearSourceLocalMass_uniform {N : ℕ} (hN : 1 ≤ N) (C : ℝ) (f : ℓ¹(ℤ, ℂ)) (x : ℤ) :
    linearSourceLocalMass C N f x ≤ (N : ℝ)⁻¹ * ‖f‖ :=
  ciSup_le (fun M => linearSourceBallMass_uniform hN M M.property C f x)

theorem linearSourceLocalMass_le_iff {N : ℕ} (hN : 1 ≤ N) (C : ℝ)
    (f : ℓ¹(ℤ,ℂ)) (x : ℤ) (B : ℝ) :
    linearSourceLocalMass C N f x ≤ B ↔
      ∀ M : ℝ, (N:ℝ) ≤ M → linearSourceBallMass C f x M ≤ B := by
  constructor
  · intro h M hM
    exact (linearSourceBallMass_le_local hN C f x M hM).trans h
  · intro h
    exact ciSup_le (fun M => h M M.property)

noncomputable def linearWindowCount (C M : ℝ) (F : Finset ℤ) (x : ℤ) : ℕ :=
  (F.filter (fun y => |((x-y:ℤ):ℝ)| ≤ C*M)).card

theorem linearSourceBallMass_indicator (C M : ℝ) (F : Finset ℤ) (x : ℤ) :
    linearSourceBallMass C (finiteIndicatorLp F 1) x M=(linearWindowCount C M F x:ℝ)/M := by
  classical
  unfold linearSourceBallMass
  rw [tsum_eq_sum (s:=F) (fun y hy => by
    simp only [finiteIndicatorLp,finiteIndicator,ite_eq_right hy,norm_zero,ite_self])]
  have he : (∑ y ∈ F,if |((x-y:ℤ):ℝ)| ≤ C*M then ‖finiteIndicatorLp F 1 y‖ else 0)=
      ∑ y ∈ F,if |((x-y:ℤ):ℝ)| ≤ C*M then (1:ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro y hy
    simp only [finiteIndicatorLp,finiteIndicator,ite_eq_left hy,norm_one]
  rw [he,Finset.sum_boole]
  simp only [linearWindowCount,div_eq_mul_inv,mul_comm]

def SourceLinearAdmissible (I : SparseIntegerInterval) (F : Finset ℤ) (C : ℝ)
    (τ : ℤ → ℕ) : Prop :=
  (∀ x ∈ I.points, ∃ j : ℕ, τ x=2^j ∧ τ x ≤ I.length) ∧
    ∀ x ∈ I.points, linearSourceLocalMass C (τ x) (finiteIndicatorLp F 1) x ≤
      C*((F.card:ℝ)/I.length)

theorem sourceLinearAdmissible_iff_display (I : SparseIntegerInterval) (F : Finset ℤ)
    (C : ℝ) (τ : ℤ → ℕ) : SourceLinearAdmissible I F C τ ↔
      (∀ x ∈ I.points, ∃ j : ℕ, τ x=2^j ∧ τ x ≤ I.length) ∧
      ∀ x ∈ I.points, ∀ M : ℝ, (τ x:ℝ) ≤ M →
        (linearWindowCount C M F x:ℝ)/M ≤ C*((F.card:ℝ)/I.length) := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro x hx M hM
    have hτ : 1 ≤ τ x := by
      obtain ⟨j,hj,_⟩ := h.1 x hx
      rw [hj]
      exact one_le_pow₀ (by decide : 1 ≤ (2:ℕ))
    rw [←linearSourceBallMass_indicator]
    exact ((linearSourceLocalMass_le_iff hτ C _ x _).mp (h.2 x hx)) M hM
  · rintro ⟨hτ,h⟩
    refine ⟨hτ,?_⟩
    intro x hx
    have hpos : 1 ≤ τ x := by
      obtain ⟨j,hj,_⟩ := hτ x hx
      rw [hj]
      exact one_le_pow₀ (by decide : 1 ≤ (2:ℕ))
    apply (linearSourceLocalMass_le_iff hpos C _ x _).mpr
    intro M hM
    rw [linearSourceBallMass_indicator]
    exact h x hx M hM

end PrimeSquares
