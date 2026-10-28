import PrimeSquares.GoldbachArithmeticFamily
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_normalized_group_sum_pullback {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (F : G→*H) (hF : Function.Surjective F) (f : H→ℂ) :
    (Fintype.card G:ℂ)⁻¹*(∑ g : G,f (F g))=
      (Fintype.card H:ℂ)⁻¹*(∑ h : H,f h) := by
  classical
  let C := ((univ : Finset G).filter (fun g => F g=1)).card
  have hc (h : H) : ((univ : Finset G).filter (fun g => F g=h)).card=C :=
    MonoidHom.card_fiber_eq_of_mem_range F (hF h) (hF 1)
  have hs (f : H→ℂ) : (∑ g : G,f (F g))=(C:ℂ)*(∑ h : H,f h) := by
    rw [←sum_fiberwise_of_maps_to (fun g (_ : g∈(univ:Finset G)) => mem_univ (F g)) (fun g => f (F g)),mul_sum]
    apply sum_congr rfl
    intro h _
    calc
      _=∑ _g∈(univ:Finset G).filter (fun g => F g=h),f h := by
        apply sum_congr rfl
        intro g hg
        rw [(mem_filter.mp hg).2]
      _=_ := by rw [sum_const,nsmul_eq_mul,hc]
  have hC : C≠0 := by
    apply Nat.ne_of_gt
    apply card_pos.mpr
    exact ⟨1,mem_filter.mpr ⟨mem_univ _,map_one F⟩⟩
  have hcard : (Fintype.card G:ℂ)=(C:ℂ)*(Fintype.card H:ℂ) := by
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using hs (fun _ => 1)
  have hC' : (C:ℂ)≠0 := Nat.cast_ne_zero.mpr hC
  have hH : (Fintype.card H:ℂ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hs,hcard]
  field_simp

theorem goldbach_normalized_units_sum_pullback (m n : ℕ) [NeZero m] [NeZero n]
    (hd : n∣m) (f : (ZMod n)ˣ→ℂ) :
    (m.totient:ℂ)⁻¹*(∑ u : (ZMod m)ˣ,f (ZMod.unitsMap hd u))=
      (n.totient:ℂ)⁻¹*(∑ u : (ZMod n)ˣ,f u) := by
  simpa only [ZMod.card_units_eq_totient] using
    goldbach_normalized_group_sum_pullback (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd) f

end PrimeSquares
