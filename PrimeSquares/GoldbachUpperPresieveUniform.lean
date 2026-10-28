import PrimeSquares.GoldbachUpperSieveDensity
import PrimeSquares.GoldbachUpperSieveParameters

set_option autoImplicit false
open Filter
namespace PrimeSquares

theorem goldbach_eventually_uniform_of_paths {α β : Type*} (l : Filter α)
    (P Q : α→β→Prop) (b₀ : β) (hP : ∀ᶠ a in l,P a b₀)
    (H : ∀ b : α→β,(∀ᶠ a in l,P a (b a))→∀ᶠ a in l,Q a (b a)) :
    ∀ᶠ a in l,∀ b : β,P a b→Q a b := by
  classical
  let b := fun a=>if h : ∃ v,P a v ∧ ¬Q a v then Classical.choose h else b₀
  have hb : ∀ᶠ a in l,P a (b a) := by
    filter_upwards [hP] with a ha
    by_cases h : ∃ v,P a v ∧ ¬Q a v
    · simpa only [b,dite_eq_left h] using (Classical.choose_spec h).1
    · simpa only [b,dite_eq_right h] using ha
  filter_upwards [H b hb] with a ha v hv
  by_contra hnv
  have h : ∃ v,P a v ∧ ¬Q a v := ⟨v,hv,hnv⟩
  have hbad := (Classical.choose_spec h).2
  apply hbad
  simpa only [b,dite_eq_left h] using ha

noncomputable def goldbachUpperSieveError (B C K K₀ c K₁ δ N : ℝ) (ℓ : ℕ) : ℝ :=
  K₁*(Real.log (goldbachUpperOuterLevel B N ℓ))^(-δ)+
    (K₀*Real.exp (-c*goldbachPresievePreliminaryS C N))*
      (((1+K/Real.log 2)*(2/Real.log 2)^((1:ℝ)))*(Real.log N)^((1:ℝ)))^2

theorem goldbach_upper_presieving_uniform
    (B C K K₀ c sstar K₁ δ : ℝ) (f F : ℝ→ℝ)
    (hB : 0≤B) (hC : 0<C) (hK : 0≤K) (hK₀ : 0≤K₀) (hc : 0<c) (hδ : 0<δ)
    (hpre : GoldbachClassicalFundamentalInput 2 K K₀ c sstar)
    (houter : GoldbachClassicalCoefficientInput 1 K K₁ δ f F)
    (hF : ContinuousAt F 2) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℝ in atTop,∀ ℓ : ℕ,1≤ℓ→(ℓ:ℝ)≤N^(10/9:ℝ)→
      GoldbachCorrectedPresieveAt.{0} N C 2 2 1 K K₀ c K₁ δ
        (goldbachUpperSieveLimit N ℓ) (goldbachUpperOuterLevel B N ℓ)
        (goldbachUpperPreliminaryPrimes ℓ ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ))
        (goldbachUpperOuterPrimes ℓ ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ)) f F ∧
      F (Real.log (goldbachUpperOuterLevel B N ℓ)/Real.log (goldbachUpperSieveLimit N ℓ))+
        goldbachUpperSieveError B C K K₀ c K₁ δ N ℓ≤F 2+ε := by
  classical
  let P := fun N : ℝ=>fun ℓ : ℕ=>1<N ∧ 1≤ℓ ∧ (ℓ:ℝ)≤N^(10/9:ℝ)
  let Q := fun N : ℝ=>fun ℓ : ℕ=>
    GoldbachCorrectedPresieveAt.{0} N C 2 2 1 K K₀ c K₁ δ
      (goldbachUpperSieveLimit N ℓ) (goldbachUpperOuterLevel B N ℓ)
      (goldbachUpperPreliminaryPrimes ℓ ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ))
      (goldbachUpperOuterPrimes ℓ ((Real.log N)^C) (goldbachUpperSieveLimit N ℓ)) f F ∧
    F (Real.log (goldbachUpperOuterLevel B N ℓ)/Real.log (goldbachUpperSieveLimit N ℓ))+
      goldbachUpperSieveError B C K K₀ c K₁ δ N ℓ≤F 2+ε
  have hp : ∀ᶠ N : ℝ in atTop,P N 1 := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with N hN
    exact ⟨hN,by decide,by simpa using (Real.one_le_rpow hN.le (by norm_num : (0:ℝ)≤10/9))⟩
  have huni : ∀ᶠ N : ℝ in atTop,∀ ℓ : ℕ,P N ℓ→Q N ℓ := by
    apply goldbach_eventually_uniform_of_paths atTop P Q 1 hp
    intro ℓ hℓ
    let z := fun N : ℝ=>goldbachUpperSieveLimit N (ℓ N)
    let D₁ := fun N : ℝ=>goldbachUpperOuterLevel B N (ℓ N)
    let P₀ := fun N : ℝ=>goldbachUpperPreliminaryPrimes (ℓ N) ((Real.log N)^C) (z N)
    let Q₁ := fun N : ℝ=>goldbachUpperOuterPrimes (ℓ N) ((Real.log N)^C) (z N)
    have hlarge : ∀ᶠ N : ℝ in atTop,1<N ∧ Disjoint (P₀ N) (Q₁ N) ∧
        Real.exp (C*Real.log (Real.log N))+1≤z N ∧ z N≤D₁ N ∧ D₁ N≤N^(2:ℝ) ∧
        (∀ p∈P₀ N,p.Prime ∧ (p:ℝ)<Real.exp (C*Real.log (Real.log N))+1) ∧
        (∀ p∈Q₁ N,p.Prime ∧ (p:ℝ)<z N) := by
      filter_upwards [hℓ,goldbach_upper_sieve_levels_uniform B C hB] with N hℓ hlev
      obtain ⟨hN,hpos,hbound⟩ := hℓ
      obtain ⟨hR,hD,hU⟩ := hlev.2 (ℓ N) hpos hbound
      have he := goldbach_presieve_source_R N C hN
      refine ⟨hN,(goldbach_upper_prime_split (ℓ N) _ _).1,?_,hD,hU,?_,?_⟩
      · simpa only [←he] using hR
      · intro p hp
        obtain ⟨hp,hpR⟩ := Finset.mem_filter.mp hp
        refine ⟨((mem_goldbach_upper_sieve_primes (ℓ N) (z N) p).mp hp).1.1,?_⟩
        rw [←he];linarith
      · intro p hp
        have hh := (mem_goldbach_upper_sieve_primes (ℓ N) (z N) p).mp (Finset.mem_filter.mp hp).1
        exact ⟨hh.1.1,hh.2⟩
    obtain ⟨herror,hAt⟩ := goldbach_corrected_presieving.{0} C 2 2 1 K K₀ c sstar K₁ δ
      z D₁ P₀ Q₁ f F hC (by norm_num) (by norm_num) hK hK₀ hc hδ hpre houter hlarge
    have hs := goldbach_upper_parameter_along B ℓ hℓ
    have hsum : Tendsto (fun N : ℝ=>F (Real.log (D₁ N)/Real.log (z N))+
        goldbachUpperSieveError B C K K₀ c K₁ δ N (ℓ N)) atTop (nhds (F 2)) := by
      simpa only [goldbachUpperSieveError,D₁,z,Function.comp_def,add_zero] using
        (hF.tendsto.comp hs).add herror
    filter_upwards [hAt,hsum.eventually (gt_mem_nhds (by linarith : F 2<F 2+ε))] with N hAt hsum
    exact ⟨hAt,hsum.le⟩
  filter_upwards [huni,eventually_gt_atTop (1:ℝ)] with N hN hN1
  intro ℓ hpos hbound
  exact hN ℓ ⟨hN1,hpos,hbound⟩

end PrimeSquares
