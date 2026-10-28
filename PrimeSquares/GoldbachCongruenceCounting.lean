import PrimeSquares.GoldbachReciprocalLCM

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- A finite set in one residue class contains at most T/q+1 points in an
interval of length T. No compatibility or existence of a residue is assumed. -/
theorem goldbach_congruence_interval_card (F : Finset ℕ) (A T q : ℕ)
    (hF : F⊆Ico A (A+T))
    (hmod : ∀ x∈F,∀ y∈F,Nat.ModEq q x y) :
    F.card≤T/q+1 := by
  classical
  by_cases hne : F.Nonempty
  · let b := F.min' hne
    have hb : b∈F := F.min'_mem hne
    have hbt (t : ℕ) (ht : t∈F) : b≤t := F.min'_le t ht
    have hrec (t : ℕ) (ht : t∈F) : b+q*((t-b)/q)=t := by
      have hsub : Nat.ModEq q (t-b) 0 := by
        simpa only [Nat.sub_self] using (hmod t ht b hb).sub (hbt t ht) le_rfl (Nat.ModEq.refl b)
      rw [Nat.mul_div_cancel' (Nat.modEq_zero_iff_dvd.mp hsub)]
      exact Nat.add_sub_of_le (hbt t ht)
    have hc := card_le_card_of_injOn (fun t : ℕ => (t-b)/q)
      (t:=range (T/q+1)) (s:=F)
      (fun t ht => by
        have hba := (mem_Ico.mp (hF hb)).1
        have htt := (mem_Ico.mp (hF ht)).2
        exact mem_range.mpr (Nat.lt_succ_iff.mpr
          (Nat.div_le_div_right (show t-b≤T by omega))))
      (fun x hx y hy he => by
        have hrx := hrec x hx
        have hry := hrec y hy
        dsimp only at he
        rw [he] at hrx
        exact hrx.symm.trans hry)
    simpa only [card_range] using hc
  · rw [not_nonempty_iff_eq_empty.mp hne,card_empty]
    exact Nat.zero_le _

theorem goldbach_congruence_interval_card_real (F : Finset ℕ) (A T q : ℕ)
    (hF : F⊆Ico A (A+T))
    (hmod : ∀ x∈F,∀ y∈F,Nat.ModEq q x y) :
    (F.card:ℝ)≤(T:ℝ)/(q:ℝ)+1 := by
  have hc : (F.card:ℝ)≤((T/q:ℕ):ℝ)+1 := by
    exact_mod_cast goldbach_congruence_interval_card F A T q hF hmod
  exact hc.trans (add_le_add (Nat.cast_div_le (α:=ℝ) (m:=T) (n:=q)) le_rfl)

noncomputable def goldbachSimultaneousCongruences (A T k₁ k₂ a₁ a₂ : ℕ) : Finset ℕ :=
  (Ico A (A+T)).filter (fun t => t%k₁=a₁%k₁ ∧ t%k₂=a₂%k₂)

theorem goldbach_simultaneous_congruence_count (A T k₁ k₂ a₁ a₂ : ℕ) :
    (goldbachSimultaneousCongruences A T k₁ k₂ a₁ a₂).card≤T/(k₁.lcm k₂)+1 := by
  apply goldbach_congruence_interval_card _ A T (k₁.lcm k₂) (filter_subset _ _)
  intro x hx y hy
  obtain ⟨_,hx₁,hx₂⟩ := mem_filter.mp hx
  obtain ⟨_,hy₁,hy₂⟩ := mem_filter.mp hy
  exact Nat.mod_lcm (hx₁.trans hy₁.symm) (hx₂.trans hy₂.symm)

theorem goldbach_simultaneous_congruence_count_real (A T k₁ k₂ a₁ a₂ : ℕ) :
    ((goldbachSimultaneousCongruences A T k₁ k₂ a₁ a₂).card:ℝ)≤
      (T:ℝ)/(k₁.lcm k₂:ℕ)+1 := by
  have hc : ((goldbachSimultaneousCongruences A T k₁ k₂ a₁ a₂).card:ℝ)≤
      ((T/(k₁.lcm k₂):ℕ):ℝ)+1 := by
    exact_mod_cast goldbach_simultaneous_congruence_count A T k₁ k₂ a₁ a₂
  exact hc.trans (add_le_add (Nat.cast_div_le (α:=ℝ) (m:=T) (n:=k₁.lcm k₂)) le_rfl)

end PrimeSquares
