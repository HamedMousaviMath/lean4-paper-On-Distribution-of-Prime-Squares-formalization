import PrimeSquares.UnitSquareCRTCardinality

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def unitSquareRoots (q : ℕ) [NeZero q] (a : ZMod q) : Finset (ZMod q)ˣ :=
  Finset.univ.filter (fun u => (u:ZMod q)^2=a)

theorem mem_unitSquareRoots (q : ℕ) [NeZero q] (a : ZMod q) (u : (ZMod q)ˣ) :
    u ∈ unitSquareRoots q a ↔ (u:ZMod q)^2=a := by
  classical
  simp [unitSquareRoots]

theorem unitSquareRoots_nonempty (q : ℕ) [NeZero q] (a : ZMod q) :
    (unitSquareRoots q a).Nonempty ↔ a ∈ unitSquareResidues q := by
  constructor
  · rintro ⟨u,hu⟩
    exact (mem_unitSquareResidues a).mpr ⟨u,(mem_unitSquareRoots q a u).mp hu⟩
  · intro ha
    obtain ⟨u,hu⟩ := (mem_unitSquareResidues a).mp ha
    exact ⟨u,(mem_unitSquareRoots q a u).mpr hu⟩

theorem unitSquareRoots_card_eq_kernel (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : a ∈ unitSquareResidues q) :
    (unitSquareRoots q a).card=(unitSquareRoots q 1).card := by
  classical
  obtain ⟨u,hu⟩ := (mem_unitSquareResidues a).mp ha
  have haunit : IsUnit a := by rw [←hu]; exact u.isUnit.pow 2
  symm
  unfold unitSquareRoots
  apply Finset.card_bijective (Equiv.mulLeft u) (Equiv.mulLeft u).bijective
  intro v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (v:ZMod q)^2=1 ↔ ((u*v : (ZMod q)ˣ):ZMod q)^2=a
  rw [Units.val_mul, mul_pow, hu]
  constructor
  · intro hv
    rw [hv,mul_one]
  · intro hv
    have hz : a*((v:ZMod q)^2-1)=0 := by rw [mul_sub,mul_one,hv,sub_self]
    exact sub_eq_zero.mp ((haunit.mul_right_eq_zero).mp hz)

theorem unitSquareRoots_sum (q : ℕ) [NeZero q] :
    ∑ a ∈ unitSquareResidues q, (unitSquareRoots q a).card=q.totient := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise (s:=(Finset.univ : Finset (ZMod q)ˣ))
    (t:=unitSquareResidues q) (f:=fun u : (ZMod q)ˣ => (u:ZMod q)^2)
    (fun u _ => (mem_unitSquareResidues ((u:ZMod q)^2)).mpr ⟨u,rfl⟩)
  rw [Finset.card_univ, ZMod.card_units_eq_totient] at hc
  exact hc.symm

theorem unitSquareRoots_kernel_factor (q : ℕ) [NeZero q] :
    (unitSquareRoots q 1).card*(unitSquareResidues q).card=q.totient := by
  classical
  calc
    _ = ∑ _a ∈ unitSquareResidues q, (unitSquareRoots q 1).card := by simp [mul_comm]
    _ = ∑ a ∈ unitSquareResidues q, (unitSquareRoots q a).card :=
      Finset.sum_congr rfl (fun a ha => (unitSquareRoots_card_eq_kernel q a ha).symm)
    _ = q.totient := unitSquareRoots_sum q

theorem unitSquareRoots_normalized (q : ℕ) [NeZero q] (a : ZMod q)
    (ha : a ∈ unitSquareResidues q) :
    ((unitSquareRoots q a).card:ℝ)/q.totient=1/((unitSquareResidues q).card:ℝ) := by
  rw [unitSquareRoots_card_eq_kernel q a ha]
  have hphi : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hm : (0:ℝ)<(unitSquareResidues q).card := by
    exact_mod_cast Finset.card_pos.mpr (unitSquareResidues_nonempty q)
  apply (div_eq_div_iff hphi.ne' hm.ne').mpr
  have hcast : ((unitSquareRoots q 1).card:ℝ)*
      ((unitSquareResidues q).card:ℝ)=(q.totient:ℝ) := by
    exact_mod_cast unitSquareRoots_kernel_factor q
  simpa only [one_mul] using hcast

end PrimeSquares
