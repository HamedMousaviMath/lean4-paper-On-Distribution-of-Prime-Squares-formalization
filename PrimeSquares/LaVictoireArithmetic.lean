import PrimeSquares.PrimeSquareFrequency
import PrimeSquares.BadnessThickeningLittleO
import Mathlib.Data.PNat.Basic

set_option autoImplicit false
open Finset Filter Asymptotics
open scoped Topology
namespace PrimeSquares

abbrev CyclicResidueFamily := (q : ℕ+) → Finset (ZMod (q:ℕ))

noncomputable def cyclicFamilyDensity (Λ : CyclicResidueFamily) (q : ℕ+) : ℝ :=
  ((Λ q).card:ℝ)/(q:ℕ)

structure LaVictoireArithmetic (n : ℕ → ℕ) where
  residues : CyclicResidueFamily
  u : ℕ → ℕ+
  q : ℕ → ℕ+
  increasing : StrictMono n
  represented : ∀ (r : ℕ+) (a : ZMod (r:ℕ)), a ∈ residues r →
    ∃ k : ℕ, (n k : ZMod (r:ℕ))=a
  crt : ∀ (r s : ℕ+) (h : (r:ℕ).Coprime (s:ℕ))
    (a : ZMod ((r:ℕ)*(s:ℕ))), a ∈ residues (r*s) ↔
    (ZMod.chineseRemainder h a).1 ∈ residues r ∧
    (ZMod.chineseRemainder h a).2 ∈ residues s
  odd_u : ∀ j, Odd (u j:ℕ)
  odd_q : ∀ j, Odd (q j:ℕ)
  coprime : Pairwise (fun a b : ℕ ⊕ ℕ =>
    ((Sum.elim u q a : ℕ+):ℕ).Coprime ((Sum.elim u q b : ℕ+):ℕ))
  density_zero : Tendsto (fun j => cyclicFamilyDensity residues (q j)) atTop (𝓝 0)
  density_positive : 0 < ⨅ j, cyclicFamilyDensity residues (u j)
  thickening : (fun γ : ℝ => γ-liminf (fun j =>
    cyclicThickeningDensity (q j:ℕ) (residues (q j)) γ) atTop)
      =o[𝓝[>] (0:ℝ)] (fun γ : ℝ => γ)
  differences : ∃ α : ℝ, 0 < α ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧
    ∀ γ : ℝ, 0 < γ → γ < γ₀ → 5*α < liminf (fun j =>
      cyclicFarPairFraction (q j:ℕ) (residues (q j)) γ) atTop
  frequencies : ∃ β : ℝ, 0 < β ∧ ∀ S : Finset (ℕ ⊕ ℕ),
    ∀ a : ZMod ((∏ i ∈ S, Sum.elim u q i : ℕ+):ℕ),
      a ∈ residues (∏ i ∈ S, Sum.elim u q i) →
      β/((residues (∏ i ∈ S, Sum.elim u q i)).card:ℝ)<
        liminf (sequenceResidueFrequency n _ a) atTop

noncomputable def unitSquareFamily : CyclicResidueFamily := fun q => unitSquareResidues (q:ℕ)
noncomputable def badnessUPos (j : ℕ) : ℕ+ := ⟨badnessAuxU j,(badnessAuxU_prime j).pos⟩
noncomputable def badnessQPos (j : ℕ) : ℕ+ := ⟨badnessBlockModulus j,badnessBlockModulus_pos j⟩

theorem unitSquareFamily_density (q : ℕ+) :
    cyclicFamilyDensity unitSquareFamily q=unitSquareDensity (q:ℕ) := by
  simp only [cyclicFamilyDensity, unitSquareFamily, unitSquareDensity, unitSquareCard_eq]

theorem badness_aux_density_iInf_positive :
    0 < ⨅ j, cyclicFamilyDensity unitSquareFamily (badnessUPos j) := by
  have h : (1/3:ℝ) ≤ ⨅ j, cyclicFamilyDensity unitSquareFamily (badnessUPos j) := by
    apply le_ciInf
    intro j
    rw [unitSquareFamily_density]
    exact badnessAuxU_density_lower j
  exact (by norm_num : (0:ℝ)<1/3).trans_le h

theorem primeSquare_lavictoire_arithmetic (HW : RawSplitQuadraticWeilInput)
    (HP : RawFixedPrimeProgressionFrequencyInput) :
    Nonempty (LaVictoireArithmetic primeSquareSequence) := by
  refine ⟨{
    residues := unitSquareFamily
    u := badnessUPos
    q := badnessQPos
    increasing := primeSquareSequence_strictMono
    represented := ?_
    crt := ?_
    odd_u := ?_
    odd_q := badnessBlockModulus_odd
    coprime := ?_
    density_zero := ?_
    density_positive := badness_aux_density_iInf_positive
    thickening := badness_thickening_little_o HW
    differences := ?_
    frequencies := ?_ }⟩
  · intro r a ha
    obtain ⟨k,hk⟩ := unitSquareResidues_prime_represented ha
    exact ⟨k,by simpa only [primeSquareSequence, Nat.cast_pow] using hk⟩
  · intro r s h a
    exact unitSquareResidues_crt h a
  · intro j
    exact (badnessAuxU_prime j).odd_of_ne_two (ne_of_gt (badnessAuxPrime_gt_two _))
  · intro a b hab
    have h := badness_combined_moduli_pairwise_coprime hab
    cases a <;> cases b <;> simpa only [Sum.elim_inl, Sum.elim_inr, badnessUPos,
      badnessQPos, PNat.mk_coe] using h
  · have heq : (fun j => cyclicFamilyDensity unitSquareFamily (badnessQPos j))=
        (fun j => unitSquareDensity (badnessBlockModulus j)) := by
      funext j
      exact unitSquareFamily_density (badnessQPos j)
    rw [heq]
    exact badnessBlockDensity_tendsto_zero
  · refine ⟨1/160,by norm_num,1/16,by norm_num,?_⟩
    intro γ hγ hγ16
    exact badness_difference_condition HW γ hγ hγ16
  · refine ⟨1/2,by norm_num,?_⟩
    intro S a ha
    exact primeSquareFrequency_strict_liminf HP _ a ha

end PrimeSquares
