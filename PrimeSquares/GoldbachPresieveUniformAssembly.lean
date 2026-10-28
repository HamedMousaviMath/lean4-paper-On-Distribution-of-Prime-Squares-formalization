import PrimeSquares.GoldbachPresieveEulerMass

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachSieveProduct (P : Finset ℕ) (g : ℕ→ℝ) : ℝ :=
  ∏ p∈P,(1-g p)

structure GoldbachSingleStageWeights (P : Finset ℕ) (level : ℝ) where
  divisors : Finset ℕ
  lower : ℕ→ℝ
  upper : ℕ→ℝ
  level_bound : ∀ d∈divisors,0 < d ∧ (d:ℝ) < level
  squarefree : ∀ d∈divisors,Squarefree d
  prime_support : ∀ d∈divisors,∀ p : ℕ,p.Prime→p∣d→p∈P
  lower_norm : ∀ d∈divisors,|lower d|≤1
  upper_norm : ∀ d∈divisors,|upper d|≤1
  sift_lower : ∀ a : ℕ,(∑ d∈divisors,lower d*goldbachDivIndicator d a)≤goldbachSiftIndicator P a
  sift_upper : ∀ a : ℕ,goldbachSiftIndicator P a≤∑ d∈divisors,upper d*goldbachDivIndicator d a

structure GoldbachPresieveDensityData (P Q : Finset ℕ) (D₀ D₁ : ℝ)
    (W₀ : GoldbachSingleStageWeights P D₀) (W₁ : GoldbachSingleStageWeights Q D₁)
    (g : ℕ→ℝ) (ε₀ ε₁ L f F : ℝ) : Prop where
  one : g 1=1
  mul : ∀ d e : ℕ,Squarefree d→Squarefree e→d.Coprime e→
    d.primeFactors⊆P∪Q→e.primeFactors⊆P∪Q→g (d*e)=g d*g e
  prime_range : ∀ p∈P∪Q,0≤g p ∧ g p < 1
  inverse_bound : (goldbachSieveProduct Q g)⁻¹≤L
  prelim_lower : |(∑ e∈W₀.divisors,W₀.lower e*g e)-goldbachSieveProduct P g|≤ε₀*goldbachSieveProduct P g
  prelim_upper : |(∑ e∈W₀.divisors,W₀.upper e*g e)-goldbachSieveProduct P g|≤ε₀*goldbachSieveProduct P g
  outer_lower : goldbachSieveProduct Q g*(f-ε₁)≤∑ d∈W₁.divisors,W₁.lower d*g d
  outer_upper : (∑ d∈W₁.divisors,W₁.upper d*g d)≤goldbachSieveProduct Q g*(F+ε₁)

def GoldbachPresieveBounds {ι : Type*} (A : Finset ι) (a : ι→ℕ) (P Q : Finset ℕ)
    (level X f F ε : ℝ) (g r cm cp : ℕ→ℝ) : Prop :=
  X*goldbachSieveProduct P g*goldbachSieveProduct Q g*(f-ε)+
      (∑ m∈range (Nat.ceil level),cm m*r m)≤goldbachSequenceSiftedCount A a (P∪Q) ∧
  goldbachSequenceSiftedCount A a (P∪Q)≤
    X*goldbachSieveProduct P g*goldbachSieveProduct Q g*(F+ε)+
      ∑ m∈range (Nat.ceil level),cp m*r m

theorem goldbach_presieve_uniform_assembly (P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (D₀ D₁ : ℝ) (W₀ : GoldbachSingleStageWeights P D₀) (W₁ : GoldbachSingleStageWeights Q D₁)
    (ε₀ ε₁ L f F : ℝ) (hε₀ : 0≤ε₀) :
    ∃ cm cp : ℕ→ℝ,
      (∀ m : ℕ,|cm m|≤1 ∧ |cp m|≤1) ∧
      (∀ m : ℕ,D₀*D₁≤m→cm m=0 ∧ cp m=0) ∧
      ∀ g : ℕ→ℝ,GoldbachPresieveDensityData P Q D₀ D₁ W₀ W₁ g ε₀ ε₁ L f F→
        ∀ (ι : Type*) (A : Finset ι) (a : ι→ℕ) (X : ℝ),0≤X→∀ r : ℕ→ℝ,
          (∀ i∈W₀.divisors×ˢW₁.divisors,
            goldbachSequenceDivisorCount A a (i.1*i.2)=X*g (i.1*i.2)+r (i.1*i.2))→
          GoldbachPresieveBounds A a P Q (D₀*D₁) X f F (ε₁+ε₀*L^2) g r cm cp := by
  classical
  let E := W₀.divisors
  let D := W₁.divisors
  have hc : ∀ e∈E,∀ d∈D,e.Coprime d :=
    goldbach_presieve_disjoint_support_coprime E D P Q hPQ W₀.prime_support W₁.prime_support
  let cm := goldbachPresievePushforward (E×ˢD) (goldbachPresievePair W₁.lower W₀.lower W₀.upper)
  let cp := goldbachPresievePushforward (E×ˢD) (goldbachPresievePair W₁.upper W₀.upper W₀.lower)
  have hcm := goldbach_presieve_coefficient_properties E D D₀ D₁ W₀.level_bound W₁.level_bound hc
    W₁.lower W₀.lower W₀.upper W₁.lower_norm W₀.lower_norm W₀.upper_norm
  have hcp := goldbach_presieve_coefficient_properties E D D₀ D₁ W₀.level_bound W₁.level_bound hc
    W₁.upper W₀.upper W₀.lower W₁.upper_norm W₀.upper_norm W₀.lower_norm
  refine ⟨cm,cp,fun m=>⟨hcm.1 m,hcp.1 m⟩,fun m hm=>⟨hcm.2 m hm,hcp.2 m hm⟩,?_⟩
  intro g hg ι A a X hX r hA
  let V₀ := goldbachSieveProduct P g
  let V₁ := goldbachSieveProduct Q g
  have hPsupp : ∀ e∈E,e.primeFactors⊆P := by
    intro e he p hp
    exact W₀.prime_support e he p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hQsupp : ∀ d∈D,d.primeFactors⊆Q := by
    intro d hd p hp
    exact W₁.prime_support d hd p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hPrange : ∀ p∈P,0≤g p ∧ g p < 1 := fun p hp=>hg.prime_range p (mem_union_left Q hp)
  have hQrange : ∀ p∈Q,0≤g p ∧ g p < 1 := fun p hp=>hg.prime_range p (mem_union_right P hp)
  have hV₀ : 0 < V₀ := (goldbach_presieve_outer_product P g hPrange).1
  have hV₁ : 0 < V₁ := (goldbach_presieve_outer_product Q g hQrange).1
  have heval : ∀ d∈D,g d=∏ p∈d.primeFactors,g p := by
    intro d hd
    exact goldbach_presieve_density_prime_product (P∪Q) g hg.one hg.mul d
      (W₁.squarefree d hd) (fun p hp=>mem_union_right P (hQsupp d hd hp))
  have hgnonneg : ∀ d∈D,0≤g d := by
    intro d hd
    rw [heval d hd]
    exact prod_nonneg (fun p hp=>(hQrange p (hQsupp d hd hp)).1)
  have hmul : ∀ e∈E,∀ d∈D,g (e*d)=g e*g d := by
    intro e he d hd
    exact hg.mul e d (W₀.squarefree e he) (W₁.squarefree d hd) (hc e he d hd)
      (fun p hp=>mem_union_left Q (hPsupp e he hp)) (fun p hp=>mem_union_right P (hQsupp d hd hp))
  have hmass (u : ℕ→ℝ) (hu : ∀ d∈D,|u d|≤1) : (∑ d∈D,|u d| * g d)≤V₁*L^2 := by
    have hr := goldbach_presieve_outer_mass_ratio D Q u g W₁.squarefree hQsupp hu hQrange heval
    have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hV₁.le) hg.inverse_bound 2
    have h := (div_le_iff₀ hV₁).mp (hr.trans hpow)
    simpa only [mul_comm (L^2) V₁] using h
  have hrem (u lo hi : ℕ→ℝ) :
      (∑ m∈range (Nat.ceil (D₀*D₁)),goldbachPresievePushforward (E×ˢD) (goldbachPresievePair u lo hi) m*r m)=
      ∑ m∈(E×ˢD).image (fun i=>i.1*i.2),goldbachPresievePushforward (E×ˢD) (goldbachPresievePair u lo hi) m*r m := by
    rw [goldbach_presieve_remainder_level E D D₀ D₁ W₀.level_bound W₁.level_bound,
      goldbach_presieve_pushforward_reindex]
  constructor
  · have hraw := goldbach_presieve_quantitative_lower A a E D P Q hc W₀.lower W₀.upper W₁.lower g r
      X V₀ V₁ ε₀ ε₁ f hX hV₀.le W₀.sift_lower W₀.sift_upper W₁.sift_lower hA hmul hgnonneg
      hg.prelim_lower hg.prelim_upper hg.outer_lower
    have hloss := mul_le_mul_of_nonneg_left (hmass W₁.lower W₁.lower_norm) (mul_nonneg hε₀ hV₀.le)
    have hnorm : X*V₀*V₁*(f-(ε₁+ε₀*L^2))≤
        X*(V₀*V₁*(f-ε₁)-ε₀*V₀*(∑ d∈D,|W₁.lower d| * g d)) := by
      have hinside : V₀*V₁*(f-(ε₁+ε₀*L^2))≤V₀*V₁*(f-ε₁)-ε₀*V₀*(∑ d∈D,|W₁.lower d| * g d) := by
        nlinarith only [hloss]
      nlinarith only [mul_le_mul_of_nonneg_left hinside hX]
    change X*V₀*V₁*(f-(ε₁+ε₀*L^2))+(∑ m∈range (Nat.ceil (D₀*D₁)),cm m*r m)≤_
    rw [hrem]
    exact (add_le_add hnorm le_rfl).trans hraw
  · have hraw := goldbach_presieve_quantitative_upper A a E D P Q hc W₀.lower W₀.upper W₁.upper g r
      X V₀ V₁ ε₀ ε₁ F hX hV₀.le W₀.sift_lower W₀.sift_upper W₁.sift_upper hA hmul hgnonneg
      hg.prelim_lower hg.prelim_upper hg.outer_upper
    have hloss := mul_le_mul_of_nonneg_left (hmass W₁.upper W₁.upper_norm) (mul_nonneg hε₀ hV₀.le)
    have hnorm : X*(V₀*V₁*(F+ε₁)+ε₀*V₀*(∑ d∈D,|W₁.upper d| * g d))≤
        X*V₀*V₁*(F+(ε₁+ε₀*L^2)) := by
      have hinside : V₀*V₁*(F+ε₁)+ε₀*V₀*(∑ d∈D,|W₁.upper d| * g d)≤V₀*V₁*(F+(ε₁+ε₀*L^2)) := by
        nlinarith only [hloss]
      nlinarith only [mul_le_mul_of_nonneg_left hinside hX]
    change _≤X*V₀*V₁*(F+(ε₁+ε₀*L^2))+(∑ m∈range (Nat.ceil (D₀*D₁)),cp m*r m)
    rw [hrem]
    exact hraw.trans (add_le_add hnorm le_rfl)

end PrimeSquares
