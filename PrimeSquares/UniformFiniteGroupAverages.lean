import PrimeSquares.TwistedQuadratic

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem finite_group_pullback_average {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (φ : G →* H) (hφ : Function.Surjective φ) (F : H → ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G,F (φ g) =
      (Fintype.card H : ℂ)⁻¹ * ∑ h : H,F h := by
  classical
  have hs (h : H) : ∑ g : G,F (φ g*h)=∑ g : G,F (φ g) := by
    obtain ⟨v,rfl⟩ := hφ h
    simp_rw [←map_mul]
    exact Equiv.sum_comp (Equiv.mulRight v) (fun g : G => F (φ g))
  have ht (g : G) : ∑ h : H,F (φ g*h)=∑ h : H,F h :=
    Equiv.sum_comp (Equiv.mulLeft (φ g)) F
  have he : (Fintype.card H : ℂ)*(∑ g : G,F (φ g))=
      (Fintype.card G : ℂ)*(∑ h : H,F h) := by
    calc
      _ = ∑ h : H,∑ g : G,F (φ g) := by simp
      _ = ∑ h : H,∑ g : G,F (φ g*h) := sum_congr rfl (fun h _ => (hs h).symm)
      _ = ∑ g : G,∑ h : H,F (φ g*h) := sum_comm
      _ = _ := by simp_rw [ht]; simp
  have hG : (Fintype.card G : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hH : (Fintype.card H : ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination he

/-- Cancellation over an entire finite group. The character and test function
are arbitrary, and the only obstruction is a nontrivial kernel value. -/
theorem finite_group_twisted_pullback_zero {G H : Type*} [Group G] [Group H]
    [Fintype G] (φ : G →* H) (χ : G →* ℂ) (F : H → ℂ)
    (v : G) (hv : φ v=1) (hχ : χ v≠1) :
    ∑ g : G,χ g*F (φ g)=0 := by
  classical
  have he : χ v*(∑ g : G,χ g*F (φ g))=∑ g : G,χ g*F (φ g) := by
    rw [mul_sum]
    calc
      _ = ∑ g : G,χ (v*g)*F (φ (v*g)) := by
        apply sum_congr rfl
        intro g _
        rw [map_mul,map_mul,hv,one_mul]
        ring
      _ = _ := Equiv.sum_comp (Equiv.mulLeft v) (fun g => χ g*F (φ g))
  have hz : (χ v-1)*(∑ g : G,χ g*F (φ g))=0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχ)

end PrimeSquares
