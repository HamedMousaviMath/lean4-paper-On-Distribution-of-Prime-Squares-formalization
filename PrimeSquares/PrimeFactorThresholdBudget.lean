import PrimeSquares.GaussAsymptotic
import PrimeSquares.ConductorFactors

open Finset Filter Topology
namespace PrimeSquares

theorem primeFactors_reciprocal_threshold (q : ℕ) (hq : 0 < q)
    (y : ℝ) (hy : 2 ≤ y) :
    (∑ p ∈ q.primeFactors,(p : ℝ)⁻¹) ≤
      1+Real.log y+y⁻¹*(Real.log 2)⁻¹*Real.log q := by
  classical
  have hy0 : 0 < y := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let S := q.primeFactors
  let A : Finset ℕ := S.filter (fun p : ℕ => (p : ℝ) ≤ y)
  let B : Finset ℕ := S.filter (fun p : ℕ => ¬(p : ℝ) ≤ y)
  have hA : (∑ p ∈ A,(p : ℝ)⁻¹) ≤ 1+Real.log y := by
    calc
      _ ≤ ∑ p ∈ Icc 1 ⌊y⌋₊,(p : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpS,hpy⟩ := mem_filter.mp hp
          exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hpS).one_le,
            (Nat.le_floor_iff hy0.le).mpr hpy⟩
        · intro p hp hn;positivity
      _ = (harmonic ⌊y⌋₊ : ℝ) := by
        simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      _ ≤ _ := harmonic_floor_le_one_add_log y (by linarith)
  have hB : (∑ p ∈ B,(p : ℝ)⁻¹) ≤ y⁻¹*(Real.log 2)⁻¹*Real.log q := by
    calc
      _ ≤ ∑ p ∈ B,y⁻¹*(Real.log 2)⁻¹*Real.log (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpS,hpy⟩ := mem_filter.mp hp
        have hprime := Nat.prime_of_mem_primeFactors hpS
        have hlp : Real.log 2 ≤ Real.log (p : ℝ) :=
          Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
        have hinv : (p : ℝ)⁻¹ ≤ y⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hy0 (le_of_lt (lt_of_not_ge hpy))
        have hrat : 1 ≤ (Real.log 2)⁻¹*Real.log (p : ℝ) := by
          have hdiv : 1 ≤ Real.log (p : ℝ)/Real.log 2 :=
            (le_div_iff₀ h2).mpr (by simpa only [one_mul] using hlp)
          simpa only [div_eq_mul_inv,mul_comm] using hdiv
        nlinarith [mul_le_mul_of_nonneg_left hrat (inv_nonneg.mpr hy0.le)]
      _ ≤ ∑ p ∈ S,y⁻¹*(Real.log 2)⁻¹*Real.log (p : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p hp hn
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hy0.le) (inv_nonneg.mpr h2.le))
          (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le))
      _ = y⁻¹*(Real.log 2)⁻¹*∑ p ∈ S,Real.log (p : ℝ) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (primeFactors_log_budget q hq)
        (mul_nonneg (inv_nonneg.mpr hy0.le) (inv_nonneg.mpr h2.le))
  have hsplit := sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ y) (fun p => (p : ℝ)⁻¹)
  rw [←hsplit]
  exact add_le_add hA hB

noncomputable def gaussThresholdSlope (y : ℝ) : ℝ :=
  (Real.sqrt y*Real.log y)⁻¹+4*(y⁻¹*(Real.log 2)⁻¹)

theorem gaussThresholdSlope_nonneg {y : ℝ} (hy : 2 ≤ y) : 0 ≤ gaussThresholdSlope y := by
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gaussThresholdSlope
  positivity

theorem log_conductorRho_le (q : ℕ) :
    Real.log (conductorRho q) ≤ (∑ p ∈ q.primeFactors,(Real.sqrt (p : ℝ))⁻¹)+
      4*∑ p ∈ q.primeFactors,(p : ℝ)⁻¹ := by
  rw [conductorRho,Real.log_prod]
  · calc
      _ ≤ ∑ p ∈ q.primeFactors,((Real.sqrt (p : ℝ))⁻¹+4*(p : ℝ)⁻¹) :=
        sum_le_sum (fun p hp => log_gaussOddPrimeFactor_le p (Nat.prime_of_mem_primeFactors hp).two_le)
      _ = _ := by rw [sum_add_distrib,←mul_sum]
  · intro p hp
    exact (gaussOddPrimeFactor_pos p (Nat.prime_of_mem_primeFactors hp).two_le).ne'

theorem conductorRho_log_threshold (q : ℕ) (hq : 0 < q) {y : ℝ} (hy : 2 ≤ y) :
    Real.log (conductorRho q) ≤ gaussAnalyticMajorant y-Real.log 4+
      gaussThresholdSlope y*(Real.log q-y) := by
  have h1 := log_conductorRho_le q
  have h2 := primeFactors_inv_sqrt_threshold q hq y hy
  have h3 := primeFactors_reciprocal_threshold q hq y hy
  have he : gaussAnalyticMajorant y-Real.log 4+gaussThresholdSlope y*(Real.log q-y)=
      primeInvSqrtSum y+(Real.log q-primeTheta y)/(Real.sqrt y*Real.log y)+
        4*(1+Real.log y+y⁻¹*(Real.log 2)⁻¹*Real.log q) := by
    have hy0 : y ≠ 0 := by linarith
    unfold gaussAnalyticMajorant gaussLogCorrection gaussThresholdSlope
    field_simp
    ring
  rw [he]
  linarith

theorem conductorRho_exp_threshold (q : ℕ) (hq : 0 < q) {y : ℝ} (hy : 2 ≤ y) :
    conductorRho q ≤ Real.exp (gaussAnalyticMajorant y)*
      Real.exp (gaussThresholdSlope y*(Real.log q-y)) := by
  have hp : 0 < conductorRho q := (by norm_num : (0 : ℝ)<1).trans_le (conductorRho_one_le q)
  have h := Real.exp_le_exp.mpr (conductorRho_log_threshold q hq hy)
  rw [Real.exp_log hp] at h
  rw [←Real.exp_add]
  exact h.trans (Real.exp_le_exp.mpr (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]))

end PrimeSquares
