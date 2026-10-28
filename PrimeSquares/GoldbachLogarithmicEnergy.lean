import PrimeSquares.GoldbachProgressionRows

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_harmonic_nonneg (M : ℕ) : (0:ℝ)≤harmonic M := by
  rw [harmonic_eq_sum_Icc,Rat.cast_sum]
  exact sum_nonneg (fun i _ => by simp only [Rat.cast_inv,Rat.cast_natCast]; positivity)

theorem goldbach_total_row_square_bound (X M : ℕ) (L : Finset ℕ)
    (K : ℕ→Finset ℕ) (a : ℕ→ℕ→ℕ)
    (hL : L⊆Icc 1 X) (hK : ∀ ℓ∈L,K ℓ⊆Icc 1 M)
    (hc : ∀ ℓ∈L,((K ℓ).card:ℝ)^2≤(X:ℝ)/(ℓ:ℝ)) :
    (∑ ℓ∈L,∑ t∈Icc 1 (X/ℓ),(goldbachCongruenceMultiplicity (K ℓ) (a ℓ) t:ℝ)^2)≤
      (X:ℝ)*((harmonic M:ℝ)^3+1)*(harmonic X:ℝ) := by
  have hH := goldbach_harmonic_nonneg M
  have hrow (ℓ : ℕ) (hℓ : ℓ∈L) :
      (∑ t∈Icc 1 (X/ℓ),(goldbachCongruenceMultiplicity (K ℓ) (a ℓ) t:ℝ)^2)≤
        (X:ℝ)/(ℓ:ℝ)*((harmonic M:ℝ)^3+1) := by
    have hinterval : Ico 1 (1+X/ℓ)=Icc 1 (X/ℓ) := by
      ext t
      simp only [mem_Ico,mem_Icc]
      omega
    have hh := goldbach_congruence_square_harmonic_bound (K ℓ) (a ℓ) 1 (X/ℓ) M (hK ℓ hℓ)
    rw [hinterval] at hh
    calc
      _≤((X/ℓ:ℕ):ℝ)*(harmonic M:ℝ)^3+((K ℓ).card:ℝ)^2 := hh
      _≤((X:ℝ)/(ℓ:ℝ))*(harmonic M:ℝ)^3+(X:ℝ)/(ℓ:ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right Nat.cast_div_le (pow_nonneg hH 3)) (hc ℓ hℓ)
      _=_ := by ring
  have hrec : (∑ ℓ∈L,(ℓ:ℝ)⁻¹)≤(harmonic X:ℝ) := by
    calc
      _≤∑ ℓ∈Icc 1 X,(ℓ:ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hL (fun ℓ _ _ => by positivity)
      _=_ := by simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  calc
    _≤∑ ℓ∈L,(X:ℝ)/(ℓ:ℝ)*((harmonic M:ℝ)^3+1) := sum_le_sum hrow
    _=((X:ℝ)*((harmonic M:ℝ)^3+1))*(∑ ℓ∈L,(ℓ:ℝ)⁻¹) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro ℓ _
      simp only [div_eq_mul_inv]
      ring
    _≤_ := mul_le_mul_of_nonneg_left hrec (by positivity)

theorem goldbach_progression_energy_harmonic (N : ℕ) (hN : 1≤N) (M : ℕ)
    (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ)
    (hI : ∀ i ∈ I, 0 < (i.1 : ℕ) ∧ i.1≤N^2)
    (hK : ∀ ℓ∈I.image Prod.fst,goldbachModuliAt I ℓ⊆Icc 1 M)
    (hc : ∀ ℓ∈I.image Prod.fst,((goldbachModuliAt I ℓ).card:ℝ)^2≤(N:ℝ)^2/(ℓ:ℝ))
    (hd : ∀ i∈I,‖d i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N I a d W θ‖^2
      ∂AddCircle.haarAddCircle)≤
      (Real.log (N^2:ℕ)/Real.log 2)*
        ((N:ℝ)^2*((harmonic M:ℝ)^3+1)*(harmonic (N^2):ℝ)) := by
  have hL : I.image Prod.fst⊆Icc 1 (N^2) := by
    intro ℓ hℓ
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hℓ
    exact mem_Icc.mpr (hI i hi)
  have hr := goldbach_total_row_square_bound (N^2) M (I.image Prod.fst)
    (goldbachModuliAt I) (fun ℓ k => a (ℓ,k)) hL hK (by simpa only [Nat.cast_pow] using hc)
  have hR : 0≤Real.log (N^2:ℕ)/Real.log 2 := div_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1≤N^2 by nlinarith)))
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  have he := goldbach_progression_energy_by_row_squares N hN I a d W
    (fun i hi => (hI i hi).1) hd
  exact he.trans (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_pow] using hr) hR)

/-- A slightly stronger bound than the source's logarithmic sixth power. The
local cardinality condition is discharged from the source cutoffs separately. -/
theorem goldbach_progression_energy_log_five (N : ℕ) (hN : 1≤N)
    (I : Finset (ℕ×ℕ)) (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ)
    (hI : ∀ i ∈ I, 0 < (i.1 : ℕ) ∧ i.1≤N^2)
    (hK : ∀ ℓ∈I.image Prod.fst,goldbachModuliAt I ℓ⊆Icc 1 N)
    (hc : ∀ ℓ∈I.image Prod.fst,((goldbachModuliAt I ℓ).card:ℝ)^2≤(N:ℝ)^2/(ℓ:ℝ))
    (hd : ∀ i∈I,‖d i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N I a d W θ‖^2
      ∂AddCircle.haarAddCircle)≤
        (8/Real.log 2)*(N:ℝ)^2*(1+Real.log N)^5 := by
  let L : ℝ := 1+Real.log N
  have hl : 0≤Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hL : 1≤L := by dsimp only [L]; linarith
  have hH := goldbach_harmonic_nonneg N
  have hHX := goldbach_harmonic_nonneg (N^2)
  have hlogX : Real.log (N^2:ℕ)=2*Real.log N := by
    rw [Nat.cast_pow,Real.log_pow]
    norm_num
  have hcub : (harmonic N:ℝ)^3+1≤2*L^3 := by
    have hh := pow_le_pow_left₀ hH (harmonic_le_one_add_log N) 3
    have h1 : (1:ℝ)≤L^3 := by
      simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hL 3
    dsimp only [L] at h1
    dsimp only [L]
    linarith
  have hhX : (harmonic (N^2):ℝ)≤2*L := by
    have hh := harmonic_le_one_add_log (N^2)
    rw [hlogX] at hh
    dsimp only [L]
    linarith
  have hR : Real.log (N^2:ℕ)/Real.log 2≤2*L/Real.log 2 := by
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
    rw [hlogX]
    dsimp only [L]
    linarith
  have he := goldbach_progression_energy_harmonic N hN N I a d W hI hK hc hd
  calc
    _≤(Real.log (N^2:ℕ)/Real.log 2)*
      ((N:ℝ)^2*((harmonic N:ℝ)^3+1)*(harmonic (N^2):ℝ)) := he
    _≤(2*L/Real.log 2)*((N:ℝ)^2*(2*L^3)*(2*L)) := by
      gcongr
    _=_ := by dsimp only [L]; ring

end PrimeSquares
