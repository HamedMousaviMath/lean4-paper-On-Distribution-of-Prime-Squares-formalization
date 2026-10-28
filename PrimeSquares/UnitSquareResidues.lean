import PrimeSquares.PrimeCutoffEnumeration
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option autoImplicit false
open Finset
namespace PrimeSquares

def IsUnitSquare {R : Type*} [CommRing R] (x : R) : Prop :=
  ∃ u : Rˣ, (u : R)^2=x

noncomputable def unitSquareResidues (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.image (fun u : (ZMod q)ˣ => (u : ZMod q)^2)

theorem mem_unitSquareResidues {q : ℕ} [NeZero q] (a : ZMod q) :
    a ∈ unitSquareResidues q ↔ IsUnitSquare a := by
  classical
  simp [unitSquareResidues, IsUnitSquare]

theorem isUnitSquare_iff {R : Type*} [CommRing R] (a : R) :
    IsUnitSquare a ↔ IsUnit a ∧ IsSquare a := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.isUnit.pow 2, ⟨(u : R), by rw [pow_two]⟩⟩
  · rintro ⟨hu, b, hb⟩
    have hbunit : IsUnit b := isUnit_of_mul_isUnit_left (hb ▸ hu)
    refine ⟨hbunit.unit, ?_⟩
    rw [hbunit.unit_spec, pow_two]
    exact hb.symm

theorem isUnitSquare_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : IsUnitSquare (e a) ↔ IsUnitSquare a := by
  simp only [isUnitSquare_iff]
  constructor
  · intro h
    exact ⟨by simpa using h.1.map e.symm, by simpa using h.2.map e.symm⟩
  · intro h
    exact ⟨h.1.map e, h.2.map e⟩

theorem isUnitSquare_prod {R S : Type*} [CommRing R] [CommRing S] (a : R) (b : S) :
    IsUnitSquare (a,b) ↔ IsUnitSquare a ∧ IsUnitSquare b := by
  simp only [isUnitSquare_iff, Prod.isUnit_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, ⟨⟨x,y⟩, hxy⟩⟩
    exact ⟨⟨ha, ⟨x, congrArg Prod.fst hxy⟩⟩, ⟨hb, ⟨y, congrArg Prod.snd hxy⟩⟩⟩
  · rintro ⟨⟨ha, x, hx⟩, ⟨hb, y, hy⟩⟩
    exact ⟨⟨ha, hb⟩, ⟨(x,y), Prod.ext hx hy⟩⟩

theorem unitSquareResidues_crt {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (a : ZMod (q*r)) :
    a ∈ unitSquareResidues (q*r) ↔
      (ZMod.chineseRemainder h a).1 ∈ unitSquareResidues q ∧
      (ZMod.chineseRemainder h a).2 ∈ unitSquareResidues r := by
  simp only [mem_unitSquareResidues]
  rw [← isUnitSquare_ringEquiv (ZMod.chineseRemainder h) a]
  exact isUnitSquare_prod _ _

theorem unitSquareResidues_nonempty (q : ℕ) [NeZero q] :
    (unitSquareResidues q).Nonempty := by
  refine ⟨1, (mem_unitSquareResidues 1).mpr ⟨1, ?_⟩⟩
  simp

theorem unitSquareResidues_prime_represented {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : a ∈ unitSquareResidues q) :
    ∃ k : ℕ, ((Nat.nth Nat.Prime k : ℕ) : ZMod q)^2=a := by
  obtain ⟨u, hu⟩ := (mem_unitSquareResidues a).mp ha
  obtain ⟨p, _, hp, heq⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit 0
  refine ⟨Nat.count Nat.Prime p, ?_⟩
  rw [Nat.nth_count hp, heq]
  exact hu

end PrimeSquares
