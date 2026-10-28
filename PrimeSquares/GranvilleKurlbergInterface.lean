import PrimeSquares.CyclicPoissonSpacings
import PrimeSquares.QuadraticGKCorrelation

set_option autoImplicit false
open Finset Filter
open scoped Topology
namespace PrimeSquares

def ResidueFamilyCRT (Λ : CyclicResidueFamily) : Prop :=
  ∀ (r s : ℕ+) (h : (r:ℕ).Coprime (s:ℕ))
    (a : ZMod ((r:ℕ)*(s:ℕ))), a ∈ Λ (r*s) ↔
    (ZMod.chineseRemainder h a).1 ∈ Λ r ∧ (ZMod.chineseRemainder h a).2 ∈ Λ s

noncomputable def cyclicFamilyCorrelation (Λ : CyclicResidueFamily) (q : ℕ+)
    (S : Finset (ZMod (q:ℕ))) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun t => ∀ h ∈ S, t+h ∈ Λ q)).card:ℝ)

def GKLocalHypotheses (Λ : CyclicResidueFamily) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
    0 < cyclicFamilyDensity Λ ⟨p,(Fact.out : p.Prime).pos⟩) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ S : Finset (ZMod p), S.card=k →
      let r := cyclicFamilyDensity Λ ⟨p,(Fact.out : p.Prime).pos⟩
      |cyclicFamilyCorrelation Λ ⟨p,(Fact.out : p.Prime).pos⟩ S/(r^k*(p:ℝ))-1| ≤
        K*(1-r)*(p:ℝ)^(-c)) ∧
  (∀ ε : ℝ, 0 < ε → ∃ P : ℕ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → P ≤ p →
    (cyclicFamilyDensity Λ ⟨p,(Fact.out : p.Prime).pos⟩)⁻¹ ≤ (p:ℝ)^ε)

def RawGranvilleKurlbergInput : Prop :=
  ∀ Λ : CyclicResidueFamily, ResidueFamilyCRT Λ → GKLocalHypotheses Λ →
    ∀ q : ℕ → ℕ+, (∀ j, Odd (q j:ℕ)) → (∀ j, Squarefree (q j:ℕ)) →
      Tendsto (fun j => ((q j:ℕ):ℝ)/(Λ (q j)).card) atTop atTop →
      CyclicPoissonSpacings Λ q

theorem unitSquareFamily_crt : ResidueFamilyCRT unitSquareFamily := by
  intro r s h a
  exact unitSquareResidues_crt h a

theorem unitSquareFamily_prime_density (p : ℕ) [Fact p.Prime] :
    cyclicFamilyDensity unitSquareFamily ⟨p,(Fact.out : p.Prime).pos⟩=primeResidueDensity p := by
  change ((unitSquareResidues p).card:ℝ)/(p:ℝ)=primeResidueDensity p
  rfl

theorem unitSquareFamily_gk_local (HW : RawSplitQuadraticWeilInput) :
    GKLocalHypotheses unitSquareFamily := by
  refine ⟨?_,⟨1/3,by norm_num,?_⟩,?_⟩
  · intro p _ hp
    rw [unitSquareFamily_prime_density]
    exact (by norm_num : (0:ℝ)<1/3).trans_le (primeResidueDensity_bounds p hp).1
  · intro k _
    obtain ⟨K,hK,hcorr⟩ := quadratic_GK_uniform_correlation HW k
    refine ⟨K,hK,?_⟩
    intro p _ hp S hS
    dsimp only
    rw [unitSquareFamily_prime_density]
    exact hcorr p hp S hS
  · intro ε hε
    obtain ⟨P,hP⟩ := primeResidueDensity_subpower ε hε
    refine ⟨P,?_⟩
    intro p _ hp hpP
    rw [unitSquareFamily_prime_density]
    exact hP p hp hpP

theorem badnessBlockModulus_squarefree (j : ℕ) : Squarefree (badnessBlockModulus j) := by
  unfold badnessBlockModulus
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hpr
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (badnessPrimeBlock_prime j p hp).1
      (badnessPrimeBlock_prime j r hr).1).mpr hpr)
  · intro p hp
    exact (badnessPrimeBlock_prime j p hp).1.squarefree

theorem unitSquareBlock_poisson (HW : RawSplitQuadraticWeilInput)
    (HG : RawGranvilleKurlbergInput) : CyclicPoissonSpacings unitSquareFamily badnessQPos := by
  apply HG unitSquareFamily unitSquareFamily_crt (unitSquareFamily_gk_local HW) badnessQPos
    badnessBlockModulus_odd badnessBlockModulus_squarefree
  have heq : (fun j => ((badnessQPos j:ℕ):ℝ)/(unitSquareFamily (badnessQPos j)).card)=
      (fun j => unitSquareSpacing (badnessBlockModulus j)) := by
    funext j
    simp only [badnessQPos,unitSquareFamily,unitSquareSpacing,unitSquareCard_eq,PNat.mk_coe]
  rw [heq]
  exact badnessBlockSpacing_tendsto_atTop

theorem unitSquareBlock_gap_tail (HW : RawSplitQuadraticWeilInput)
    (HG : RawGranvilleKurlbergInput) (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun j => cyclicGapTail (badnessBlockModulus j)
      (unitSquareResidues (badnessBlockModulus j)) θ) atTop (𝓝 (Real.exp (-θ))) :=
  poisson_single_gap_tail unitSquareFamily badnessQPos (unitSquareBlock_poisson HW HG) θ hθ.le

end PrimeSquares
