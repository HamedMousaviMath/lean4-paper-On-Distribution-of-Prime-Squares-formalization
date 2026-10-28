import PrimeSquares.GoldbachPresieveClassicalInputs

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- The current manuscript's level chain already implies the previously
explicit strict inequality between the preliminary and total levels. -/
theorem goldbach_current_presieve_strict_level (N C D z : ℝ) (hN : 1<N)
    (hz : (Real.log N)^C+1≤z)
    (hlevel : z≤D/Real.exp ((Real.log (Real.log N))^3)) :
    Real.exp ((Real.log (Real.log N))^3)<D := by
  have hR : 0<(Real.log N)^C := Real.rpow_pos_of_pos (Real.log_pos hN) C
  have hz1 : 1<z := by linarith
  have hratio := hz1.trans_le hlevel
  simpa only [one_mul] using
    (lt_div_iff₀ (Real.exp_pos ((Real.log (Real.log N))^3))).mp hratio

/-- Inline preliminary-prime conditions in the current statement give
exactly the finite set in the existing presieving formalization. -/
theorem goldbach_current_presieve_preliminary_filter (P : Finset ℕ) (R w y : ℝ) :
    (P.filter (fun p : ℕ => (p:ℝ)≤R)).filter
      (fun p : ℕ => w≤(p:ℝ) ∧ (p:ℝ)<y)=
      P.filter (fun p : ℕ => w≤(p:ℝ) ∧ (p:ℝ)<y ∧ (p:ℝ)≤R) := by
  classical
  ext p
  simp only [mem_filter]
  tauto

/-- Because y<=z, the outer prime set's p<z condition is redundant
inside the current statement's interval product. -/
theorem goldbach_current_presieve_outer_filter (P : Finset ℕ) (R z w y : ℝ)
    (hy : y≤z) :
    (P.filter (fun p : ℕ => R<(p:ℝ) ∧ (p:ℝ)<z)).filter
      (fun p : ℕ => w≤(p:ℝ) ∧ (p:ℝ)<y)=
      P.filter (fun p : ℕ => w≤(p:ℝ) ∧ (p:ℝ)<y ∧ R<(p:ℝ)) := by
  classical
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hp,hR,_⟩,hw,hpy⟩
    exact ⟨hp,hw,hpy,hR⟩
  · rintro ⟨hp,hw,hpy,hR⟩
    exact ⟨⟨hp,hR,hpy.trans_le hy⟩,hw,hpy⟩

end PrimeSquares
