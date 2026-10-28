import PrimeSquares.LinearLocalRadiusComparison

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

noncomputable def leftLinearWindowCount (C M : ℝ) (F : Finset ℤ) (x : ℤ) : ℕ :=
  (F.filter (fun y => y ≤ x ∧ |((x-y:ℤ):ℝ)| ≤ C*M)).card

noncomputable def rightLinearWindowCount (C M : ℝ) (F : Finset ℤ) (x : ℤ) : ℕ :=
  (F.filter (fun y => x ≤ y ∧ |((x-y:ℤ):ℝ)| ≤ C*M)).card

theorem linearWindowCount_oneSided_compare (C M : ℝ) (F : Finset ℤ) (x : ℤ) :
    leftLinearWindowCount C M F x ≤ linearWindowCount C M F x ∧
      rightLinearWindowCount C M F x ≤ linearWindowCount C M F x ∧
      linearWindowCount C M F x ≤ leftLinearWindowCount C M F x+rightLinearWindowCount C M F x := by
  classical
  constructor
  · apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1,hy.2.2⟩
  constructor
  · apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1,hy.2.2⟩
  · have hsub : F.filter (fun y => |((x-y:ℤ):ℝ)| ≤ C*M) ⊆
        F.filter (fun y => y ≤ x ∧ |((x-y:ℤ):ℝ)| ≤ C*M) ∪
          F.filter (fun y => x ≤ y ∧ |((x-y:ℤ):ℝ)| ≤ C*M) := by
      intro y hy
      simp only [Finset.mem_filter] at hy
      rcases le_total y x with hh|hh
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy.1,hh,hy.2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy.1,hh,hy.2⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem linearSourceLocalMass_of_both_oneSided {N : ℕ} (hN : 1 ≤ N)
    (C : ℝ) (F : Finset ℤ) (x : ℤ) (L R : ℝ)
    (hleft : ∀ M : ℝ,(N:ℝ) ≤ M → (leftLinearWindowCount C M F x:ℝ)/M ≤ L)
    (hright : ∀ M : ℝ,(N:ℝ) ≤ M → (rightLinearWindowCount C M F x:ℝ)/M ≤ R) :
    linearSourceLocalMass C N (finiteIndicatorLp F 1) x ≤ L+R := by
  apply (linearSourceLocalMass_le_iff hN C _ x _).mpr
  intro M hM
  rw [linearSourceBallMass_indicator]
  have hM0 : 0 ≤ M := (Nat.cast_nonneg N).trans hM
  have hc : (linearWindowCount C M F x:ℝ) ≤
      (leftLinearWindowCount C M F x:ℝ)+(rightLinearWindowCount C M F x:ℝ) := by
    exact_mod_cast (linearWindowCount_oneSided_compare C M F x).2.2
  calc
    _ ≤ ((leftLinearWindowCount C M F x:ℝ)+(rightLinearWindowCount C M F x:ℝ))/M :=
      div_le_div_of_nonneg_right hc hM0
    _ = _ := add_div _ _ _
    _ ≤ _ := add_le_add (hleft M hM) (hright M hM)

theorem rightLinearWindowCount_negative_singleton (C M : ℝ) :
    rightLinearWindowCount C M {-1} 0=0 := by
  simp [rightLinearWindowCount]

theorem symmetricLocalMass_negative_singleton :
    1 ≤ linearSourceLocalMass 10 1 (finiteIndicatorLp {-1} 1) 0 := by
  have h := linearSourceBallMass_le_local (by norm_num : 1≤(1:ℕ)) 10
    (finiteIndicatorLp {-1} 1) 0 1 (by norm_num)
  rw [linearSourceBallMass_indicator] at h
  have hc : linearWindowCount 10 1 {-1} 0=1 := by
    unfold linearWindowCount
    have hf : ({-1}:Finset ℤ).filter (fun y => |((0-y:ℤ):ℝ)| ≤ 10*1)={-1} := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      have hy' : y=(-1:ℤ) := Finset.mem_singleton.mp hy
      rw [hy']
      norm_num
    rw [hf]
    simp
  simpa only [hc,Nat.cast_one,div_one] using h

theorem single_direction_does_not_control_symmetric (K : ℝ) :
    (∀ M : ℝ,1 ≤ M → (rightLinearWindowCount 10 M {-1} 0:ℝ)/M=0) ∧
      ¬linearSourceLocalMass 10 1 (finiteIndicatorLp {-1} 1) 0 ≤ K*0 := by
  constructor
  · intro M _
    rw [rightLinearWindowCount_negative_singleton]
    simp
  · have h := symmetricLocalMass_negative_singleton
    simp only [mul_zero]
    linarith

end PrimeSquares
