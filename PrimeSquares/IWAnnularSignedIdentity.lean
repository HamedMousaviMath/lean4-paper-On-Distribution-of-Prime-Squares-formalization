import PrimeSquares.IWSymbolLinearity
import PrimeSquares.IWSignedAnnularBounds
import PrimeSquares.IntervalIntegerMultiplier

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem iwCyclicSymbol_all_annular (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (N : ℕ) (hN : 1≤N) (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (ha : 2≤a)
    (hs : ∀ x : ℝ,1≤|x| → allAnnularBoundedSymbol N hN β hβ0 hβ1 a x=0) :
    iwCyclicSymbol S k P ν (allAnnularBoundedSymbol N hN β hβ0 hβ1 a) hs=
      weightedWidthAnnularBlock (iwFrequencySet S k) N hN β a ha (cyclicRationalCoefficient P ν) := rfl

noncomputable def iwAnnularLowOperator (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (N : ℕ) (hN : 1≤N) (β a : ℝ) (ha : 2≤a) :
    ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  integerMultiplier (weightedWidthAnnularBlock (iwFrequencySet S k) N hN β a ha
    (cyclicRationalCoefficient P ν))

noncomputable def iwAnnularSignedOperator (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (β a : ℝ) (ha : 2≤a) (J : ℕ) (σ : ℕ→ℂ) :
    ℓ²(ℤ,ℂ) →L[ℂ] ℓ²(ℤ,ℂ) :=
  ∑ j∈range J,σ j •
    (iwAnnularLowOperator S k P ν ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β a ha-
      iwAnnularLowOperator S k P ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β a ha)

theorem iwCyclicSymbol_signed_annular (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (ha : 2≤a) (J : ℕ) (σ : ℕ→ℂ)
    (hs : ∀ x : ℝ,1≤|x| → continuousAnnularSignedSymbol β hβ0 hβ1 a J σ x=0) :
    iwCyclicSymbol S k P ν (continuousAnnularSignedSymbol β hβ0 hβ1 a J σ) hs=
      ∑ j∈range J,σ j •
        (weightedWidthAnnularBlock (iwFrequencySet S k) ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num))
          β a ha (cyclicRationalCoefficient P ν)-
        weightedWidthAnnularBlock (iwFrequencySet S k) ((2 : ℕ)^j) (one_le_pow₀ (by norm_num))
          β a ha (cyclicRationalCoefficient P ν)) := by
  have hap : 0≤a := by linarith
  have haw : 1≤a*1 := by linarith
  let f : ℕ→BoundedContinuousFunction ℝ ℂ := fun j =>
    allAnnularBoundedSymbol ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β hβ0 hβ1 a-
    allAnnularBoundedSymbol ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β hβ0 hβ1 a
  have hp (j : ℕ) := allAnnularBoundedSymbol_boundary ((2 : ℕ)^(j+1))
    (one_le_pow₀ (by norm_num)) β hβ0 hβ1 hap haw
  have hm (j : ℕ) := allAnnularBoundedSymbol_boundary ((2 : ℕ)^j)
    (one_le_pow₀ (by norm_num)) β hβ0 hβ1 hap haw
  have hf : ∀ j x,1≤|x| → f j x=0 := by
    intro j x hx
    change _-_ = (0 : ℂ)
    rw [hp j x hx,hm j x hx,sub_self]
  have he (x : ℝ) : continuousAnnularSignedSymbol β hβ0 hβ1 a J σ x=
      ∑ j∈range J,σ j*f j x := by
    simp only [continuousAnnularSignedSymbol,BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.smul_apply,BoundedContinuousFunction.sub_apply,smul_eq_mul,f]
  rw [iwCyclicSymbol_combination (range J) σ S k P ν f _ hf hs he]
  apply sum_congr rfl
  intro j _
  change σ j • iwCyclicSymbol S k P ν (_-_) (hf j)=_
  rw [iwCyclicSymbol_sub _ _ _ _ _ _ (hp j) (hm j) (hf j),
    iwCyclicSymbol_all_annular S k P ν _ _ β hβ0 hβ1 a ha,
    iwCyclicSymbol_all_annular S k P ν _ _ β hβ0 hβ1 a ha]

theorem iw_signed_annular_operator_identity (S : Finset ℕ) (k P : ℕ) [NeZero P]
    (ν : ZMod P→ℂ) (β : ℝ) (hβ0 : 0≤β) (hβ1 : β≤1)
    (a : ℝ) (ha : 2≤a) (J : ℕ) (σ : ℕ→ℂ)
    (hs : ∀ x : ℝ,1≤|x| → continuousAnnularSignedSymbol β hβ0 hβ1 a J σ x=0) :
    integerMultiplier (iwCyclicSymbol S k P ν (continuousAnnularSignedSymbol β hβ0 hβ1 a J σ) hs)=
      ∑ j∈range J,σ j •
        (iwAnnularLowOperator S k P ν ((2 : ℕ)^(j+1)) (one_le_pow₀ (by norm_num)) β a ha-
          iwAnnularLowOperator S k P ν ((2 : ℕ)^j) (one_le_pow₀ (by norm_num)) β a ha) := by
  rw [iwCyclicSymbol_signed_annular S k P ν β hβ0 hβ1 a ha J σ hs,integerMultiplier_finset_sum]
  apply sum_congr rfl
  intro j _
  rw [integerMultiplier_smul,integerMultiplier_sub]
  rfl

end PrimeSquares
