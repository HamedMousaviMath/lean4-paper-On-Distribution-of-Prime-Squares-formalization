import PrimeSquares.FiniteAdditiveResidueCounts

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem unitSquarePairCount_crt {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (t : ZMod (q*r)) :
    additivePairCount (unitSquareResidues (q*r)) t =
      additivePairCount (unitSquareResidues q) (ZMod.chineseRemainder h t).1*
      additivePairCount (unitSquareResidues r) (ZMod.chineseRemainder h t).2 := by
  rw [additivePairCount_equiv (ZMod.chineseRemainder h).toAddEquiv]
  simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv]
  rw [unitSquareResidues_crt_image]
  exact additivePairCount_product _ _ _ _

theorem unitSquareTripleCount_crt {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r)
    (t : ZMod (q*r)) :
    additiveTripleCount (unitSquareResidues (q*r)) t =
      additiveTripleCount (unitSquareResidues q) (ZMod.chineseRemainder h t).1*
      additiveTripleCount (unitSquareResidues r) (ZMod.chineseRemainder h t).2 := by
  rw [additiveTripleCount_equiv (ZMod.chineseRemainder h).toAddEquiv]
  simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv]
  rw [unitSquareResidues_crt_image]
  exact additiveTripleCount_product _ _ _ _

noncomputable def unitSquarePairCount (q : ℕ) (t : ℤ) : ℕ :=
  if h : q=0 then 0 else
    letI : NeZero q := ⟨h⟩
    additivePairCount (unitSquareResidues q) (t : ZMod q)

noncomputable def unitSquareTripleCount (q : ℕ) (t : ℤ) : ℕ :=
  if h : q=0 then 0 else
    letI : NeZero q := ⟨h⟩
    additiveTripleCount (unitSquareResidues q) (t : ZMod q)

theorem unitSquarePairCount_eq (q : ℕ) [NeZero q] (t : ℤ) :
    unitSquarePairCount q t=additivePairCount (unitSquareResidues q) (t : ZMod q) := by
  simp only [unitSquarePairCount, dite_eq_right (NeZero.ne q)]

theorem unitSquareTripleCount_eq (q : ℕ) [NeZero q] (t : ℤ) :
    unitSquareTripleCount q t=additiveTripleCount (unitSquareResidues q) (t : ZMod q) := by
  simp only [unitSquareTripleCount, dite_eq_right (NeZero.ne q)]

theorem unitSquarePairCount_mul {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (t : ℤ) :
    unitSquarePairCount (q*r) t=unitSquarePairCount q t*unitSquarePairCount r t := by
  rw [unitSquarePairCount_eq, unitSquarePairCount_eq, unitSquarePairCount_eq,
    unitSquarePairCount_crt h]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]

theorem unitSquareTripleCount_mul {q r : ℕ} [NeZero q] [NeZero r]
    (h : q.Coprime r) (t : ℤ) :
    unitSquareTripleCount (q*r) t=unitSquareTripleCount q t*unitSquareTripleCount r t := by
  rw [unitSquareTripleCount_eq, unitSquareTripleCount_eq, unitSquareTripleCount_eq,
    unitSquareTripleCount_crt h]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast]

theorem unitSquarePairCount_one (t : ℤ) : unitSquarePairCount 1 t=1 := by
  rw [unitSquarePairCount_eq]
  have ht : (t : ZMod 1)=0 := Subsingleton.elim _ _
  rw [ht, additivePairCount_zero, unitSquareResidues_one_card]

theorem unitSquareTripleCount_one (t : ℤ) : unitSquareTripleCount 1 t=1 := by
  rw [unitSquareTripleCount_eq]
  unfold additiveTripleCount
  have hS : (1:ZMod 1) ∈ unitSquareResidues 1 :=
    (mem_unitSquareResidues 1).mpr ⟨1, by simp⟩
  have hmem : ∀ uv ∈ unitSquareResidues 1 ×ˢ unitSquareResidues 1,
      uv.1-uv.2-(t:ZMod 1) ∈ unitSquareResidues 1 := by
    intro uv _
    simpa only [Subsingleton.elim (uv.1-uv.2-(t:ZMod 1)) 1] using hS
  rw [Finset.filter_eq_self.mpr hmem, Finset.card_product, unitSquareResidues_one_card]

theorem multiplicative_prime_product (f : ℕ → ℕ) (h1 : f 1=1)
    (hmul : ∀ q r : ℕ, 0 < q → 0 < r → q.Coprime r → f (q*r)=f q*f r)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : f (∏ p ∈ S, p)=∏ p ∈ S, f p := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using h1
  | @insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    have hST : ∀ r ∈ S, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
    have hprod : 0 < ∏ r ∈ S, r := Finset.prod_pos (fun r hr => (hST r hr).pos)
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS,
      hmul p _ hp.pos hprod (prime_coprime_product hp hpS hST), ih hST]

theorem unitSquarePairCount_primeProduct (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (t : ℤ) :
    unitSquarePairCount (∏ p ∈ S, p) t=∏ p ∈ S, unitSquarePairCount p t := by
  apply multiplicative_prime_product (fun q => unitSquarePairCount q t) (unitSquarePairCount_one t) ?_ S hS
  intro q r hq hr hcop
  have : NeZero q := ⟨hq.ne'⟩
  have : NeZero r := ⟨hr.ne'⟩
  exact unitSquarePairCount_mul hcop t

theorem unitSquareTripleCount_primeProduct (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (t : ℤ) :
    unitSquareTripleCount (∏ p ∈ S, p) t=∏ p ∈ S, unitSquareTripleCount p t := by
  apply multiplicative_prime_product (fun q => unitSquareTripleCount q t) (unitSquareTripleCount_one t) ?_ S hS
  intro q r hq hr hcop
  have : NeZero q := ⟨hq.ne'⟩
  have : NeZero r := ⟨hr.ne'⟩
  exact unitSquareTripleCount_mul hcop t

end PrimeSquares
