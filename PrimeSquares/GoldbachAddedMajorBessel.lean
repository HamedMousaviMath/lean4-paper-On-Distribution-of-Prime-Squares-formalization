import PrimeSquares.GoldbachDenominatorEnergy

set_option autoImplicit false
open Finset MeasureTheory
open scoped SchwartzMap ENNReal
namespace PrimeSquares

theorem goldbach_smooth_added_major_bessel (ψ : 𝓢(ℝ,ℝ)) (hψ : ψ≠0)
    (hsψ : ∀ x : ℝ,(1/8:ℝ)≤|x| →ψ x=0) :
    ∃ K : ℝ,0<K ∧ ∀ N : ℕ,1≤N →1≤Real.log N →∀ L B : ℝ,∀ V : ℕ→ℝ,
      0≤B →L≤(N:ℝ)^2 →
      (∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)*(Real.log N)^(-B)) →
      ∀ b : ℕ×ℕ→ℤ,(∀ i∈goldbachCoefficientIndices L V,IsCoprime (i.2:ℤ) (b i)) →
      ∀ d : ℕ×ℕ→ℂ,(∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) →
      ∀ U W R Y : ℝ,2≤U →U≤N →2≤W →2≤R →1≤Y →
      R/(4*(N:ℝ)^2)<1/2 →2*(R/(4*(N:ℝ)^2))<1/Y^2 →
      ∀ S : Finset ℚ,S⊆(sourceRationalCenters Y).filter (fun r=>R<(r.den:ℝ)) →∀ T : Finset ℤ,
      (∑ n∈T,‖∑ r∈S,realFourierPhase (-(n:ℝ)*(r:ℝ))*
        (∫ γ : ℝ,goldbachSmoothMajorFamilyIntegrand ψ N R (goldbachCoefficientIndices L V) b d U W r γ*
          realFourierPhase (-(n:ℝ)*γ))‖^2)≤K*(N:ℝ)^4*(Real.log N)^4/Real.sqrt R := by
  classical
  obtain ⟨KD,hKD,hDen⟩ := goldbach_added_denominator_energy_budget
  let E := goldbachEuclideanL1Constant/(Real.log 2)^2
  let K := KD*E
  have hE : 0<E := by dsimp [E];have := goldbachEuclideanL1Constant_pos;have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity
  refine ⟨K,by dsimp [K];positivity,?_⟩
  intro N hN hlog L B V hB hL hV b hb d hd U W R Y hU hUN hW hR hY hhalf hsep S hS T
  have hNpos : 0<N := by omega
  have hRpos : 0<R := by linarith
  let I := goldbachCoefficientIndices L V
  let f := goldbachSmoothMajorFamilyIntegrand ψ N R I b d U W
  have hI : ∀ i∈I,0 < i.1 := by
    intro i hi
    exact ((mem_goldbachCoefficientIndices L V i.1 i.2).mp hi).1
  have hfm (r : ℚ) : StronglyMeasurable (f r) :=
    goldbach_smooth_major_family_measurable ψ N R I hI b d U W r
  have hfn (r : ℚ) (γ : ℝ) : ‖f r γ‖≤goldbachMajorArithmeticPrefactor N r.den*goldbachMajorEnvelope N γ :=
    (goldbach_smooth_major_family_norm ψ hψ N R I b d U W r γ).trans
      (goldbach_major_family_integrand_bound N hN hlog L B V hB hL hV b hb d hd hU hUN hW r γ)
  have hsupp (r : ℚ) {γ : ℝ} (hγ : R/(4*(N:ℝ)^2)≤|γ|) : f r γ=0 :=
    goldbach_smooth_major_family_support ψ hsψ N hNpos hRpos I b d U W r hγ
  have hhalf' : ∀ r∈S,∀ γ : ℝ,(1/2:ℝ)≤|γ| →f r γ=0 := by
    intro r _ γ hγ
    exact hsupp r (hhalf.le.trans hγ)
  have hLp : ∀ r∈S,MemLp (goldbachArcLift r (f r)) 2 AddCircle.haarAddCircle := by
    intro r _
    exact goldbach_arc_lift_memLp r (f r) (hfm r) (fun γ=>(hfn r γ).trans
      (mul_le_mul_of_nonneg_left (goldbach_major_envelope_bound N γ)
        (goldbach_major_arithmetic_prefactor_nonnegative N r.den))) 2
  have hdisj : ∀ r∈S,∀ s∈S,r≠s →∀ θ : PrimeCircle,
      goldbachArcLift r (f r) θ=0 ∨ goldbachArcLift s (f s) θ=0 := by
    intro r hr s hs hrs θ
    apply goldbach_arc_lifts_disjoint hY hsep (mem_filter.mp (hS hr)).1 (mem_filter.mp (hS hs)).1 hrs (f r) (f s) _ _ θ
    · intro γ hγ
      by_contra hh
      exact hγ (hsupp r (le_of_lt (lt_of_not_ge hh)))
    · intro γ hγ
      by_contra hh
      exact hγ (hsupp s (le_of_lt (lt_of_not_ge hh)))
  have hbessel := goldbach_disjoint_arc_bessel S T f hhalf' hLp hdisj
  have henergy (r : ℚ) : (∫ γ : ℝ,‖f r γ‖^2)≤
      (goldbachMajorArithmeticPrefactor N r.den)^2*E*(N:ℝ)^4 :=
    (goldbach_major_envelope_dominated_energy N hNpos (f r) (hfm r)
      (goldbach_major_arithmetic_prefactor_nonnegative N r.den) (hfn r)).2
  have hdenS : (∑ r∈S,(goldbachMajorArithmeticPrefactor N r.den)^2)≤
      KD*(Real.log N)^4/Real.sqrt R :=
    (sum_le_sum_of_subset_of_nonneg hS (fun r _ _=>sq_nonneg (goldbachMajorArithmeticPrefactor N r.den))).trans
      (hDen N R hR Y)
  apply hbessel.trans
  calc
    _≤∑ r∈S,(goldbachMajorArithmeticPrefactor N r.den)^2*E*(N:ℝ)^4 :=
      sum_le_sum (fun r _=>henergy r)
    _=(E*(N:ℝ)^4)*(∑ r∈S,(goldbachMajorArithmeticPrefactor N r.den)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    _≤(E*(N:ℝ)^4)*(KD*(Real.log N)^4/Real.sqrt R) :=
      mul_le_mul_of_nonneg_left hdenS (by positivity)
    _=_ := by dsimp [K];ring

end PrimeSquares
