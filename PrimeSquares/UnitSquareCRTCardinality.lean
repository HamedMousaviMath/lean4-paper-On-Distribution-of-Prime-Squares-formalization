import PrimeSquares.QuadraticResidueIndicator
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem unitSquareResidues_crt_image {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r) :
    (unitSquareResidues (q*r)).image (ZMod.chineseRemainder h) =
      (unitSquareResidues q) ×ˢ (unitSquareResidues r) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_product.mpr ((unitSquareResidues_crt h x).mp hx)
  · intro ha
    refine Finset.mem_image.mpr ⟨(ZMod.chineseRemainder h).symm a, ?_, ?_⟩
    · apply (unitSquareResidues_crt h _).mpr
      simpa using Finset.mem_product.mp ha
    · exact (ZMod.chineseRemainder h).apply_symm_apply a

theorem unitSquareResidues_mul_card {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r) :
    (unitSquareResidues (q*r)).card=(unitSquareResidues q).card*(unitSquareResidues r).card := by
  have hc := congrArg Finset.card (unitSquareResidues_crt_image h)
  rw [Finset.card_image_of_injective _ (ZMod.chineseRemainder h).injective,
    Finset.card_product] at hc
  exact hc

theorem unitSquareResidues_one_card : (unitSquareResidues 1).card=1 := by
  classical
  have hs : unitSquareResidues 1 = {1} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨(mem_unitSquareResidues 1).mpr ⟨1, by simp⟩,
      fun _ _ => Subsingleton.elim _ _⟩
  rw [hs, Finset.card_singleton]

theorem prime_coprime_product {s : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hps : p ∉ s) (hs : ∀ r ∈ s, r.Prime) : p.Coprime (∏ r ∈ s, r) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro r hr
  apply (Nat.coprime_primes hp (hs r hr)).mpr
  intro heq
  exact hps (heq ▸ hr)

noncomputable def unitSquareCard (q : ℕ) : ℕ :=
  if h : q=0 then 0 else
    letI : NeZero q := ⟨h⟩
    (unitSquareResidues q).card

theorem unitSquareCard_eq (q : ℕ) [NeZero q] :
    unitSquareCard q=(unitSquareResidues q).card := by
  simp only [unitSquareCard, dite_eq_right (NeZero.ne q)]

theorem unitSquareResidues_primeProduct_card (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2) :
    unitSquareCard (∏ p ∈ s, p) = ∏ p ∈ s, (p-1)/2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, unitSquareCard_eq] using unitSquareResidues_one_card
  | @insert p s hps ih =>
    have hp := hs p (Finset.mem_insert_self p s)
    have hst : ∀ r ∈ s, r.Prime ∧ r ≠ 2 := fun r hr => hs r (Finset.mem_insert_of_mem hr)
    have : NeZero p := ⟨hp.1.ne_zero⟩
    have : NeZero (∏ r ∈ s, r) := ⟨Finset.prod_ne_zero_iff.mpr (fun r hr => (hst r hr).1.ne_zero)⟩
    have : Fact p.Prime := ⟨hp.1⟩
    have hcard : (unitSquareResidues p).card=(p-1)/2 := by
      have := unitSquareResidues_prime_card p hp.2
      omega
    rw [Finset.prod_insert hps, Finset.prod_insert hps, unitSquareCard_eq,
      unitSquareResidues_mul_card (prime_coprime_product hp.1 hps (fun r hr => (hst r hr).1)),
      hcard, ←unitSquareCard_eq, ih hst]

end PrimeSquares
