import PrimeSquares.UnitSquareCRTCardinality

set_option autoImplicit false
open Finset
namespace PrimeSquares

def additivePairCount {G : Type*} [AddGroup G] [DecidableEq G] (S : Finset G) (t : G) : ℕ :=
  (S.filter (fun a => a+t ∈ S)).card

def additiveTripleCount {G : Type*} [AddGroup G] [DecidableEq G] (S : Finset G) (t : G) : ℕ :=
  ((S ×ˢ S).filter (fun uv => uv.1-uv.2-t ∈ S)).card

theorem mem_image_addEquiv {G H : Type*} [AddGroup G] [AddGroup H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (S : Finset G) (a : G) :
    e a ∈ S.image e ↔ a ∈ S := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    exact e.injective he ▸ hb
  · exact Finset.mem_image_of_mem e

theorem additivePairCount_equiv {G H : Type*} [AddGroup G] [AddGroup H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (S : Finset G) (t : G) :
    additivePairCount S t=additivePairCount (S.image e) (e t) := by
  unfold additivePairCount
  apply Finset.card_bijective e e.bijective
  intro a
  simp only [Finset.mem_filter, ←e.map_add, mem_image_addEquiv]

theorem additiveTripleCount_equiv {G H : Type*} [AddGroup G] [AddGroup H]
    [DecidableEq G] [DecidableEq H] (e : G ≃+ H) (S : Finset G) (t : G) :
    additiveTripleCount S t=additiveTripleCount (S.image e) (e t) := by
  unfold additiveTripleCount
  apply Finset.card_bijective (e.prodCongr e) (e.prodCongr e).bijective
  rintro ⟨a,b⟩
  simp only [Finset.mem_filter]
  change ((a,b) ∈ S ×ˢ S ∧ a-b-t ∈ S) ↔
    ((e a,e b) ∈ S.image e ×ˢ S.image e ∧ e a-e b-e t ∈ S.image e)
  simp only [Finset.mem_product, ←e.map_sub, mem_image_addEquiv]

theorem additivePairCount_product {G H : Type*} [AddGroup G] [AddGroup H]
    [DecidableEq G] [DecidableEq H] (S : Finset G) (R : Finset H) (a : G) (b : H) :
    additivePairCount (S ×ˢ R) (a,b)=additivePairCount S a*additivePairCount R b := by
  have heq : (S ×ˢ R).filter (fun uv => uv+(a,b) ∈ S ×ˢ R) =
      (S.filter (fun u => u+a ∈ S)) ×ˢ (R.filter (fun v => v+b ∈ R)) := by
    ext ⟨u,v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Prod.fst_add, Prod.snd_add]
    tauto
  rw [additivePairCount, heq, Finset.card_product]
  rfl

theorem additiveTripleCount_product {G H : Type*} [AddGroup G] [AddGroup H]
    [DecidableEq G] [DecidableEq H] (S : Finset G) (R : Finset H) (a : G) (b : H) :
    additiveTripleCount (S ×ˢ R) (a,b)=additiveTripleCount S a*additiveTripleCount R b := by
  unfold additiveTripleCount
  rw [←Finset.card_product]
  apply Finset.card_bijective (Equiv.prodProdProdComm G H G H)
    (Equiv.prodProdProdComm G H G H).bijective
  rintro ⟨⟨u,v⟩,⟨w,z⟩⟩
  simp only [Equiv.prodProdProdComm, Equiv.coe_fn_mk, Finset.mem_filter,
    Finset.mem_product, Prod.fst_sub, Prod.snd_sub]
  tauto

theorem additiveTripleCount_sum_pairs {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (t : G) :
    additiveTripleCount S t = ∑ v ∈ S, additivePairCount S (-v-t) := by
  simp only [additiveTripleCount, additivePairCount, Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  congr 1
  abel

theorem additivePairCount_le_card {G : Type*} [AddGroup G] [DecidableEq G]
    (S : Finset G) (t : G) : additivePairCount S t ≤ S.card := Finset.card_filter_le _ _

theorem additivePairCount_zero {G : Type*} [AddGroup G] [DecidableEq G]
    (S : Finset G) : additivePairCount S 0=S.card := by simp [additivePairCount]

end PrimeSquares
