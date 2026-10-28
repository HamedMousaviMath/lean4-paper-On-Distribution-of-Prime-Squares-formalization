import PrimeSquares.GoldbachMinorEventualCutoffs

set_option autoImplicit false
namespace PrimeSquares

theorem goldbachMinorRadiusThreshold_pos (D : UniformRenGhoshInputs) {t : ℝ} (ht : 0<t) :
    0<goldbachMinorRadiusThreshold D t := by
  have hd := D.power_nonneg
  unfold goldbachMinorRadiusThreshold
  linarith

/-- Uniform bound for the actual unweighted prime-square sum. The only
independent analytic hypothesis is the already recorded raw Ren/Ghosh input. -/
theorem goldbach_prime_minor_uniform (D : UniformRenGhoshInputs) {t : ℝ} (ht : 0<t)
    (C : ℝ) (hC : goldbachMinorRadiusThreshold D t≤C) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      1≤Real.log N ∧ ∀ U : ℝ,0≤U → U≤N → ∀ θ : PrimeCircle,
        θ∈GoldbachMinorArcs N ((Real.log N)^C) →
        ‖goldbachPrimeSquarePolynomial U θ‖≤
          goldbachMinorPrimeConstant D*(N:ℝ)*(Real.log N)^(-t) := by
  obtain ⟨N₀,hN₀,hparams⟩ := goldbach_minor_eventual_numeric_parameters D t C
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  obtain ⟨hl,h4,hs,he,hp,hq⟩ := hparams N hN
  refine ⟨hl,?_⟩
  intro U hU hUN θ hout
  obtain ⟨ξ,rfl⟩ := Quotient.exists_rep θ
  exact goldbach_prime_minor_log_parameters D N (by omega) ht hC hl h4 hs he hp hq
    ξ U hU hUN hout

theorem goldbach_prime_minor_source_cutoff_algebra {N U s : ℝ}
    (hN : 1≤Real.log N) (hU : 2≤U) (hUN : U≤N)
    (hlarge : N*(Real.log N)^(-2*s)≤U) :
    N*(Real.log N)^(-(3*s+1))≤(U/Real.log U)*(Real.log N)^(-s) := by
  have hu0 : 0<U := by linarith
  have hlU : 0<Real.log U := Real.log_pos (by linarith)
  have hlN : 0<Real.log N := by linarith
  have hlUN : Real.log U≤Real.log N := Real.log_le_log hu0 hUN
  have hprod : (Real.log N)^(-2*s)*(Real.log N)^(-s)*(Real.log N)^(-1:ℝ)=
      (Real.log N)^(-(3*s+1)) := by
    rw [←Real.rpow_add hlN,←Real.rpow_add hlN]
    congr 1
    ring
  calc
    _=(N*(Real.log N)^(-2*s))*(Real.log N)^(-s)/Real.log N := by
      rw [←hprod,Real.rpow_neg_one]
      ring
    _≤U*(Real.log N)^(-s)/Real.log N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hlN.le _)) hlN.le
    _≤U*(Real.log N)^(-s)/Real.log U :=
      div_le_div_of_nonneg_left (mul_nonneg hu0.le (Real.rpow_nonneg hlN.le _)) hlU hlUN
    _=(U/Real.log U)*(Real.log N)^(-s) := by ring

/-- The stronger large-cutoff estimate printed before the hybrid lemma also
follows from the proved actual prime bound. -/
theorem goldbach_prime_minor_source_high_range (D : UniformRenGhoshInputs)
    {s : ℝ} (hs : 0<s) (C : ℝ)
    (hC : goldbachMinorRadiusThreshold D (3*s+1)≤C) :
    ∃ N₀ : ℕ,4≤N₀ ∧ ∀ N : ℕ,N₀≤N →
      ∀ U : ℝ,2≤U → U≤N → (N:ℝ)*(Real.log N)^(-2*s)≤U →
      ∀ θ : PrimeCircle,θ∈GoldbachMinorArcs N ((Real.log N)^C) →
      ‖goldbachPrimeSquarePolynomial U θ‖≤
        goldbachMinorPrimeConstant D*(U/Real.log U)*(Real.log N)^(-s) := by
  obtain ⟨N₀,hN₀,hbound⟩ := goldbach_prime_minor_uniform D (by linarith : 0<3*s+1) C hC
  refine ⟨N₀,hN₀,?_⟩
  intro N hN U hU hUN hlarge θ hout
  obtain ⟨hl,hp⟩ := hbound N hN
  have hb := hp U (by linarith) hUN θ hout
  have ha := mul_le_mul_of_nonneg_left
    (goldbach_prime_minor_source_cutoff_algebra hl hU hUN hlarge)
    (goldbachMinorPrimeConstant_pos D).le
  exact hb.trans (by simpa only [mul_assoc] using ha)

end PrimeSquares
