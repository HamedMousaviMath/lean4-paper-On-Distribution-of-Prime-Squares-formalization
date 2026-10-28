import PrimeSquares.GoldbachMajorLCMQFibres

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachMajorResidues (k q a : ℕ) : Finset ℕ :=
  (range (k.lcm q)).filter (fun b => b%k=a%k ∧ b.Coprime (k.lcm q))

theorem mem_goldbachMajorResidues (k q a b : ℕ) :
    b∈goldbachMajorResidues k q a ↔ b<k.lcm q ∧ b%k=a%k ∧ b.Coprime (k.lcm q) := by
  simp only [goldbachMajorResidues,mem_filter,mem_range]

theorem goldbach_major_residues_modq_injective (k q a : ℕ) :
    Set.InjOn (fun b => b%q) (↑(goldbachMajorResidues k q a):Set ℕ) := by
  intro b hb c hc heq
  obtain ⟨hbh,hbk,_⟩ := (mem_goldbachMajorResidues k q a b).mp hb
  obtain ⟨hch,hck,_⟩ := (mem_goldbachMajorResidues k q a c).mp hc
  have hk : Nat.ModEq k b c := hbk.trans hck.symm
  have hq : Nat.ModEq q b c := heq
  exact (Nat.mod_lcm hk hq).eq_of_lt_of_lt hbh hch

theorem goldbach_major_residues_card (k q a : ℕ) :
    (goldbachMajorResidues k q a).card≤q := by
  classical
  by_cases hq : q=0
  · simp only [hq,goldbachMajorResidues,Nat.lcm_zero_right,range_zero,filter_empty,card_empty,le_refl]
  · have hs : (goldbachMajorResidues k q a).image (fun b => b%q)⊆range q := by
      intro r hr
      obtain ⟨b,_,rfl⟩ := mem_image.mp hr
      exact mem_range.mpr (Nat.mod_lt b (Nat.pos_of_ne_zero hq))
    calc
      _=((goldbachMajorResidues k q a).image (fun b => b%q)).card :=
        (card_image_iff.mpr (goldbach_major_residues_modq_injective k q a)).symm
      _≤(range q).card := card_le_card hs
      _=q := card_range q

theorem goldbach_major_compatible_lift (k q a r : ℕ) (hk : k≠0) (hq : q≠0)
    (ha : a.Coprime k) (hr : r.Coprime q) (hcompat : Nat.ModEq (k.gcd q) a r) :
    ∃ b∈goldbachMajorResidues k q a,Nat.ModEq q b r := by
  let b := (Nat.chineseRemainder' hcompat).val
  have hbK : Nat.ModEq k b a := (Nat.chineseRemainder' hcompat).prop.1
  have hbQ : Nat.ModEq q b r := (Nat.chineseRemainder' hcompat).prop.2
  have hbCk : b.Coprime k := by
    change b.gcd k=1
    exact hbK.gcd_eq.trans ha
  have hbCq : b.Coprime q := by
    change b.gcd q=1
    exact hbQ.gcd_eq.trans hr
  have hbCh : b.Coprime (k.lcm q) :=
    Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul k q) (hbCk.mul_right hbCq)
  refine ⟨b,(mem_goldbachMajorResidues k q a b).mpr ⟨?_,hbK,hbCh⟩,hbQ⟩
  exact Nat.chineseRemainder'_lt_lcm hcompat hk hq

theorem goldbach_major_residue_compatible (k q a b : ℕ)
    (hb : b∈goldbachMajorResidues k q a) :
    b.Coprime q ∧ Nat.ModEq (k.gcd q) a b := by
  obtain ⟨_,hbK,hbC⟩ := (mem_goldbachMajorResidues k q a b).mp hb
  exact ⟨Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right k q) hbC,
    (Nat.ModEq.of_dvd (Nat.gcd_dvd_left k q) hbK).symm⟩

end PrimeSquares
