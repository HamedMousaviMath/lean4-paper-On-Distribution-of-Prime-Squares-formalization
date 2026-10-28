import PrimeSquares.LargePrimeBlocks

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem badnessAuxU_prime (j : ℕ) : (badnessAuxU j).Prime := badnessAuxPrime_prime _

theorem badnessAuxU_odd (j : ℕ) : Odd (badnessAuxU j) := badnessAuxPrime_odd _

theorem badnessAuxU_not_mem_block (i j : ℕ) : badnessAuxU i ∉ badnessPrimeBlock j := by
  intro h
  obtain ⟨k,_,heq⟩ := Finset.mem_image.mp h
  have hi := badnessAuxPrime_strictMono.injective heq
  change 2*Nat.pair j k+1=2*i at hi
  omega

theorem badnessPrimeBlocks_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (badnessPrimeBlock i) (badnessPrimeBlock j) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨k,_,hi⟩ := Finset.mem_image.mp hpi
  obtain ⟨l,_,hj⟩ := Finset.mem_image.mp hpj
  have he := badnessAuxPrime_strictMono.injective (hi.trans hj.symm)
  have hpair : Nat.pair i k=Nat.pair j l := by omega
  have hpairs : (i,k)=(j,l) := Nat.pairEquiv.injective hpair
  exact hij (congrArg Prod.fst hpairs)

theorem badnessAuxU_pairwise_coprime : Pairwise (fun i j => (badnessAuxU i).Coprime (badnessAuxU j)) := by
  intro i j hij
  apply (Nat.coprime_primes (badnessAuxU_prime i) (badnessAuxU_prime j)).mpr
  intro heq
  have h := badnessAuxPrime_strictMono.injective heq
  change 2*i=2*j at h
  exact hij (by omega)

theorem badnessAuxU_block_coprime (i j : ℕ) :
    (badnessAuxU i).Coprime (badnessBlockModulus j) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply (Nat.coprime_primes (badnessAuxU_prime i) (badnessPrimeBlock_prime j p hp).1).mpr
  intro heq
  subst p
  exact badnessAuxU_not_mem_block i j hp

theorem badnessBlockModuli_pairwise_coprime :
    Pairwise (fun i j => (badnessBlockModulus i).Coprime (badnessBlockModulus j)) := by
  intro i j hij
  apply Nat.coprime_prod_left_iff.mpr
  intro p hpi
  apply Nat.coprime_prod_right_iff.mpr
  intro r hrj
  apply (Nat.coprime_primes (badnessPrimeBlock_prime i p hpi).1
    (badnessPrimeBlock_prime j r hrj).1).mpr
  intro heq
  subst r
  exact Finset.disjoint_left.mp (badnessPrimeBlocks_disjoint hij) hpi hrj

theorem badness_combined_moduli_pairwise_coprime :
    Pairwise (fun a b : ℕ ⊕ ℕ => (Sum.elim badnessAuxU badnessBlockModulus a).Coprime
      (Sum.elim badnessAuxU badnessBlockModulus b)) := by
  intro a b hab
  rcases a with i|i <;> rcases b with j|j
  · exact badnessAuxU_pairwise_coprime (by intro h; subst j; exact hab rfl)
  · exact badnessAuxU_block_coprime i j
  · exact (badnessAuxU_block_coprime j i).symm
  · exact badnessBlockModuli_pairwise_coprime (by intro h; subst j; exact hab rfl)

theorem badnessBlockModulus_odd (j : ℕ) : Odd (badnessBlockModulus j) := by
  unfold badnessBlockModulus
  apply Finset.prod_induction (fun p : ℕ => p) Odd
    (fun _ _ ha hb => ha.mul hb) (by decide)
  intro p hp
  exact (badnessPrimeBlock_prime j p hp).1.odd_of_ne_two (badnessPrimeBlock_prime j p hp).2

theorem badnessBlockModulus_gt_one (j : ℕ) : 1 < badnessBlockModulus j := by
  have hnon : (badnessPrimeBlock j).Nonempty := Finset.card_pos.mp (by rw [badnessPrimeBlock_card]; omega)
  obtain ⟨p,hp⟩ := hnon
  have hle : p ≤ badnessBlockModulus j := by
    exact Finset.single_le_prod (fun r hr => (badnessPrimeBlock_prime j r hr).1.one_le) hp
  exact (badnessPrimeBlock_prime j p hp).1.one_lt.trans_le hle

instance badnessAuxU_fact (j : ℕ) : Fact (badnessAuxU j).Prime := ⟨badnessAuxU_prime j⟩

instance badnessBlockModulus_neZero (j : ℕ) : NeZero (badnessBlockModulus j) :=
  ⟨(badnessBlockModulus_pos j).ne'⟩

end PrimeSquares
