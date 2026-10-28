import PrimeSquares.GoldbachPresieveUniformAssembly

set_option autoImplicit false
open Finset
namespace PrimeSquares

def GoldbachMultiplicativeDensityOn (P : Finset ℕ) (g : ℕ→ℝ) : Prop :=
  g 1=1 ∧
    (∀ d e : ℕ,Squarefree d→Squarefree e→d.Coprime e→
      d.primeFactors⊆P→e.primeFactors⊆P→g (d*e)=g d*g e) ∧
    ∀ p∈P,0≤g p ∧ g p < 1

def GoldbachRefinedSieveDimension (P : Finset ℕ) (z κ K : ℝ) (g : ℕ→ℝ) : Prop :=
  ∀ w y : ℝ,2≤w→w<y→y≤z→
    (∏ p∈P.filter (fun p : ℕ=>w≤(p:ℝ) ∧ (p:ℝ) < y),(1-g p)⁻¹)≤
      (1+K/Real.log w)*(Real.log y/Real.log w)^κ

def GoldbachClassicalFundamentalInput (κ K Kerror c sstar : ℝ) : Prop :=
  ∀ (P : Finset ℕ) (D z : ℝ),2≤z→z≤D→sstar≤Real.log D/Real.log z→
    (∀ p∈P,p.Prime ∧ (p:ℝ) < z)→
    ∃ W : GoldbachSingleStageWeights P D,
      ∀ g : ℕ→ℝ,GoldbachMultiplicativeDensityOn P g→GoldbachRefinedSieveDimension P z κ K g→
        |(∑ d∈W.divisors,W.lower d*g d)-goldbachSieveProduct P g|≤
          (Kerror*Real.exp (-c*(Real.log D/Real.log z)))*goldbachSieveProduct P g ∧
        |(∑ d∈W.divisors,W.upper d*g d)-goldbachSieveProduct P g|≤
          (Kerror*Real.exp (-c*(Real.log D/Real.log z)))*goldbachSieveProduct P g

def GoldbachClassicalCoefficientInput (κ K Kerror δ : ℝ) (f F : ℝ→ℝ) : Prop :=
  ∀ (P : Finset ℕ) (D z : ℝ),2≤z→z≤D→(∀ p∈P,p.Prime ∧ (p:ℝ) < z)→
    ∃ W : GoldbachSingleStageWeights P D,
      ∀ g : ℕ→ℝ,GoldbachMultiplicativeDensityOn P g→GoldbachRefinedSieveDimension P z κ K g→
        goldbachSieveProduct P g*(f (Real.log D/Real.log z)-Kerror*(Real.log D)^(-δ))≤
          (∑ d∈W.divisors,W.lower d*g d) ∧
        (∑ d∈W.divisors,W.upper d*g d)≤
          goldbachSieveProduct P g*(F (Real.log D/Real.log z)+Kerror*(Real.log D)^(-δ))

theorem goldbach_density_restrict {P Q : Finset ℕ} (hPQ : P⊆Q) (g : ℕ→ℝ)
    (hg : GoldbachMultiplicativeDensityOn Q g) : GoldbachMultiplicativeDensityOn P g := by
  refine ⟨hg.1,?_,?_⟩
  · intro d e hd he hc hds hes
    exact hg.2.1 d e hd he hc (hds.trans hPQ) (hes.trans hPQ)
  · intro p hp
    exact hg.2.2 p (hPQ hp)

theorem goldbach_refined_dimension_restrict (P : Finset ℕ) (z Z κ K : ℝ) (g : ℕ→ℝ)
    (hzZ : z≤Z) (hdim : GoldbachRefinedSieveDimension P Z κ K g) :
    GoldbachRefinedSieveDimension P z κ K g := by
  intro w y hw hwy hy
  exact hdim w y hw hwy (hy.trans hzZ)

theorem goldbach_refined_dimension_total (P : Finset ℕ) (z κ K : ℝ) (g : ℕ→ℝ)
    (hz : 2 < z) (hP : ∀ p∈P,p.Prime ∧ (p:ℝ) < z)
    (hdim : GoldbachRefinedSieveDimension P z κ K g) :
    (goldbachSieveProduct P g)⁻¹≤(1+K/Real.log 2)*(Real.log z/Real.log 2)^κ := by
  classical
  have hf : P.filter (fun p : ℕ=>2≤(p:ℝ) ∧ (p:ℝ) < z)=P := by
    apply filter_eq_self.mpr
    intro p hp
    exact ⟨by exact_mod_cast (hP p hp).1.two_le,(hP p hp).2⟩
  have h := hdim 2 z le_rfl hz le_rfl
  rw [hf] at h
  simpa only [prod_inv_distrib,goldbachSieveProduct] using h

def GoldbachCorrectedPresieveAt
    (N C A κ₀ κ K K₀ c K₁ δ z D₁ : ℝ) (P Q : Finset ℕ) (f F : ℝ→ℝ) : Prop :=
    let D₀ := Real.exp ((Real.log (Real.log N))^3)
    let R₀ := Real.exp (C*Real.log (Real.log N))+1
    let K₂ := (1+K/Real.log 2)*(A/Real.log 2)^κ
    let ε := K₁*(Real.log D₁)^(-δ)+
      (K₀*Real.exp (-c*goldbachPresievePreliminaryS C N))*(K₂*(Real.log N)^κ)^2
    ∃ cm cp : ℕ→ℝ,
      (∀ m : ℕ,|cm m|≤1 ∧ |cp m|≤1) ∧
      (∀ m : ℕ,D₀*D₁≤m→cm m=0 ∧ cp m=0) ∧
      ∀ g : ℕ→ℝ,GoldbachMultiplicativeDensityOn (P∪Q) g→
        GoldbachRefinedSieveDimension P R₀ κ₀ K g→GoldbachRefinedSieveDimension Q z κ K g→
        ∀ (ι : Type*) (B : Finset ι) (a : ι→ℕ) (X : ℝ),0≤X→∀ r : ℕ→ℝ,
          (∀ m : ℕ,Squarefree m→m.primeFactors⊆P∪Q→(m:ℝ) < D₀*D₁→
            goldbachSequenceDivisorCount B a m=X*g m+r m)→
          GoldbachPresieveBounds B a P Q (D₀*D₁) X (f (Real.log D₁/Real.log z))
            (F (Real.log D₁/Real.log z)) ε g r cm cp

theorem goldbach_presieving_from_classical_coefficients
    (N C A κ₀ κ K K₀ c sstar K₁ δ z D₁ : ℝ) (P Q : Finset ℕ) (f F : ℝ→ℝ)
    (hC : 0 < C) (hA : 0≤A) (hκ : 0≤κ) (hK : 0≤K) (hK₀ : 0≤K₀)
    (hN : 1 < N) (ht : 1≤Real.log (Real.log N)) (hPQ : Disjoint P Q)
    (hpre : GoldbachClassicalFundamentalInput κ₀ K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput κ K K₁ δ f F)
    (hD₀ : Real.exp (C*Real.log (Real.log N))+1≤Real.exp ((Real.log (Real.log N))^3))
    (hs : sstar≤goldbachPresievePreliminaryS C N)
    (hz : Real.exp (C*Real.log (Real.log N))+1≤z) (hD₁ : z≤D₁)
    (hlogz : Real.log z≤A*Real.log N)
    (hP : ∀ p∈P,p.Prime ∧ (p:ℝ) < Real.exp (C*Real.log (Real.log N))+1)
    (hQ : ∀ p∈Q,p.Prime ∧ (p:ℝ) < z) :
    GoldbachCorrectedPresieveAt N C A κ₀ κ K K₀ c K₁ δ z D₁ P Q f F := by
  classical
  let t := Real.log (Real.log N)
  let D₀ := Real.exp (t^3)
  let R₀ := Real.exp (C*t)+1
  let K₂ := (1+K/Real.log 2)*(A/Real.log 2)^κ
  let ε₀ := K₀*Real.exp (-c*goldbachPresievePreliminaryS C N)
  let ε₁ := K₁*(Real.log D₁)^(-δ)
  let L := K₂*(Real.log N)^κ
  have he : 1 < Real.exp (C*t) := Real.one_lt_exp_iff.mpr (mul_pos hC (by dsimp [t];linarith))
  have hR : 2≤R₀ := by dsimp only [R₀];linarith
  have hz2 : 2 < z := (show 2 < R₀ by dsimp only [R₀];linarith).trans_le hz
  have hs' : sstar≤Real.log D₀/Real.log R₀ := by
    simpa only [D₀,R₀,t,Real.log_exp,goldbachPresievePreliminaryS] using hs
  obtain ⟨W₀,hW₀⟩ := hpre P D₀ R₀ hR hD₀ hs' hP
  obtain ⟨W₁,hW₁⟩ := houter Q D₁ z hz2.le hD₁ hQ
  obtain ⟨cm,cp,hnorm,hlevel,hbound⟩ := goldbach_presieve_uniform_assembly P Q hPQ D₀ D₁ W₀ W₁
    ε₀ ε₁ L (f (Real.log D₁/Real.log z)) (F (Real.log D₁/Real.log z))
    (mul_nonneg hK₀ (Real.exp_pos _).le)
  refine ⟨cm,cp,hnorm,hlevel,?_⟩
  intro g hg hdimP hdimQ ι B a X hX r hB
  obtain ⟨hpl,hpu⟩ := hW₀ g (goldbach_density_restrict subset_union_left g hg) hdimP
  obtain ⟨hol,hou⟩ := hW₁ g (goldbach_density_restrict subset_union_right g hg) hdimQ
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK' : 0≤1+K/Real.log 2 := by positivity
  have hinv := goldbach_presieve_inverse_polylog (goldbachSieveProduct Q g) N z A (1+K/Real.log 2) κ
    hN hz2.le hA hK' hκ hlogz (goldbach_refined_dimension_total Q z κ K g hz2 hQ hdimQ)
  have hgdata : GoldbachPresieveDensityData P Q D₀ D₁ W₀ W₁ g ε₀ ε₁ L
      (f (Real.log D₁/Real.log z)) (F (Real.log D₁/Real.log z)) := by
    refine ⟨hg.1,hg.2.1,hg.2.2,hinv,?_,?_,hol,hou⟩
    · simpa only [D₀,R₀,t,ε₀,Real.log_exp,goldbachPresievePreliminaryS] using hpl
    · simpa only [D₀,R₀,t,ε₀,Real.log_exp,goldbachPresievePreliminaryS] using hpu
  apply hbound g hgdata ι B a X hX r
  intro i hi
  obtain ⟨he,hd⟩ := mem_product.mp hi
  have hc := goldbach_presieve_disjoint_support_coprime W₀.divisors W₁.divisors P Q hPQ
    W₀.prime_support W₁.prime_support i.1 he i.2 hd
  have hsf := (Nat.squarefree_mul hc).mpr ⟨W₀.squarefree i.1 he,W₁.squarefree i.2 hd⟩
  have hsupp : (i.1*i.2).primeFactors⊆P∪Q := by
    rw [Nat.primeFactors_mul (W₀.level_bound i.1 he).1.ne' (W₁.level_bound i.2 hd).1.ne']
    intro p hp
    rcases mem_union.mp hp with hp|hp
    · exact mem_union_left Q (W₀.prime_support i.1 he p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
    · exact mem_union_right P (W₁.prime_support i.2 hd p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  have hlev : ((i.1*i.2:ℕ):ℝ) < D₀*D₁ := Nat.lt_ceil.mp (mem_range.mp
    (goldbach_presieve_product_range W₀.divisors W₁.divisors D₀ D₁ W₀.level_bound W₁.level_bound
      (mem_image.mpr ⟨i,hi,rfl⟩)))
  exact hB (i.1*i.2) hsf hsupp hlev

theorem goldbach_presieve_source_R (N C : ℝ) (hN : 1 < N) :
    (Real.log N)^C=Real.exp (C*Real.log (Real.log N)) := by
  rw [Real.rpow_def_of_pos (Real.log_pos hN),mul_comm]

theorem goldbach_corrected_presieving
    (C A κ₀ κ K K₀ c sstar K₁ δ : ℝ) (z D₁ : ℝ→ℝ)
    (P Q : ℝ→Finset ℕ) (f F : ℝ→ℝ)
    (hC : 0 < C) (hA : 0≤A) (hκ : 0≤κ) (hK : 0≤K) (hK₀ : 0≤K₀)
    (hc : 0 < c) (hδ : 0 < δ)
    (hpre : GoldbachClassicalFundamentalInput κ₀ K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput κ K K₁ δ f F)
    (hlarge : ∀ᶠ N : ℝ in Filter.atTop,
      1 < N ∧ Disjoint (P N) (Q N) ∧ Real.exp (C*Real.log (Real.log N))+1≤z N ∧
        z N≤D₁ N ∧ D₁ N≤N^A ∧
        (∀ p∈P N,p.Prime ∧ (p:ℝ) < Real.exp (C*Real.log (Real.log N))+1) ∧
        (∀ p∈Q N,p.Prime ∧ (p:ℝ) < z N)) :
    let K₂ := (1+K/Real.log 2)*(A/Real.log 2)^κ
    Filter.Tendsto (fun N : ℝ=>K₁*(Real.log (D₁ N))^(-δ)+
      (K₀*Real.exp (-c*goldbachPresievePreliminaryS C N))*(K₂*(Real.log N)^κ)^2)
      Filter.atTop (nhds 0) ∧
    ∀ᶠ N : ℝ in Filter.atTop,
      GoldbachCorrectedPresieveAt N C A κ₀ κ K K₀ c K₁ δ (z N) (D₁ N) (P N) (Q N) f F := by
  have hD : ∀ᶠ N : ℝ in Filter.atTop,Real.exp (C*Real.log (Real.log N))+1≤D₁ N := by
    filter_upwards [hlarge] with N hN
    exact hN.2.2.1.trans hN.2.2.2.1
  refine ⟨goldbach_presieve_uniform_error_tendsto C c K₀ K₁ _ δ κ hC hc hK₀ hδ D₁ hD,?_⟩
  have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hlarge,ht.eventually_ge_atTop 1,
    goldbach_presieve_preliminary_level_eventually C hC,
    (goldbach_presieve_preliminary_s_tendsto C hC).eventually_ge_atTop sstar]
    with N hN htN hD₀ hs
  obtain ⟨hN,hPQ,hz,hD₁,hUpper,hP,hQ⟩ := hN
  have hzpos : 0 < z N := (show 0 < Real.exp (C*Real.log (Real.log N))+1 by positivity).trans_le hz
  have hlogz : Real.log (z N)≤A*Real.log N := by
    apply (Real.log_le_log hzpos (hD₁.trans hUpper)).trans_eq
    exact Real.log_rpow (by linarith) A
  exact goldbach_presieving_from_classical_coefficients N C A κ₀ κ K K₀ c sstar K₁ δ
    (z N) (D₁ N) (P N) (Q N) f F hC hA hκ hK hK₀ hN htN hPQ hpre houter hD₀ hs hz hD₁ hlogz hP hQ

theorem goldbach_integer_sequence_divisor_count {ι : Type*} (B : Finset ι) (a : ι→ℤ) (d : ℕ) :
    goldbachSequenceDivisorCount B (fun i=>(a i).natAbs) d=
      ((B.filter (fun i=>(d:ℤ)∣a i)).card:ℝ) := by
  simp only [goldbachSequenceDivisorCount,Int.natCast_dvd]

theorem goldbach_integer_sequence_sifted_count {ι : Type*} (B : Finset ι) (a : ι→ℤ) (P : Finset ℕ) :
    goldbachSequenceSiftedCount B (fun i=>(a i).natAbs) P=
      ((B.filter (fun i=>∀ p∈P,¬(p:ℤ)∣a i)).card:ℝ) := by
  classical
  simp only [goldbachSequenceSiftedCount,Int.natCast_dvd]

end PrimeSquares
