import PrimeSquares.GoldbachBVSourceParameters

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_source_row_subset (N : ℕ) (L : ℝ) (V : ℕ→ℝ) (hL : L≤(N:ℝ)^2) :
    (goldbachCoefficientIndices L V).image Prod.fst⊆Icc 1 (N^2) := by
  intro ℓ hℓ
  obtain ⟨hp,hl,_⟩ := goldbach_source_row_cutoffs L V ℓ hℓ
  exact mem_Icc.mpr ⟨hp,by exact_mod_cast hl.le.trans hL⟩

theorem goldbach_source_row_reciprocal (N : ℕ) (L : ℝ) (V : ℕ→ℝ) (hL : L≤(N:ℝ)^2) :
    (∑ ℓ∈(goldbachCoefficientIndices L V).image Prod.fst,(ℓ:ℝ)⁻¹)≤(harmonic (N^2):ℝ) := by
  have he : (∑ ℓ∈Icc 1 (N^2),(ℓ:ℝ)⁻¹)=(harmonic (N^2):ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [←he]
  exact sum_le_sum_of_subset_of_nonneg (goldbach_source_row_subset N L V hL)
    (fun ℓ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem goldbach_source_row_scale_sum (N : ℕ) (hlog : 1≤Real.log N)
    (L : ℝ) (V : ℕ→ℝ) (hL : L≤(N:ℝ)^2) :
    (∑ ℓ∈(goldbachCoefficientIndices L V).image Prod.fst,(N:ℝ)^2/ℓ)≤
      3*(N:ℝ)^2*Real.log N := by
  have hH : (harmonic (N^2):ℝ)≤3*Real.log N := by
    have h := harmonic_le_one_add_log (N^2)
    have he : Real.log (N^2:ℕ)=2*Real.log N := by
      rw [Nat.cast_pow,Real.log_pow]
      norm_num
    rw [he] at h
    linarith
  calc
    _=(N:ℝ)^2*(∑ ℓ∈(goldbachCoefficientIndices L V).image Prod.fst,(ℓ:ℝ)⁻¹) := by
      simp only [div_eq_mul_inv,mul_sum]
    _≤(N:ℝ)^2*(harmonic (N^2):ℝ) :=
      mul_le_mul_of_nonneg_left (goldbach_source_row_reciprocal N L V hL) (sq_nonneg _)
    _≤(N:ℝ)^2*(3*Real.log N) := mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _=3*(N:ℝ)^2*Real.log N := by ring

theorem goldbach_source_row_card (L : ℝ) (V : ℕ→ℝ) :
    (((goldbachCoefficientIndices L V).image Prod.fst).card:ℝ)≤max L 0 := by
  have hs : (goldbachCoefficientIndices L V).image Prod.fst⊆Icc 1 ⌊max L 0⌋₊ := by
    intro ℓ hℓ
    obtain ⟨hp,hl,_⟩ := goldbach_source_row_cutoffs L V ℓ hℓ
    exact mem_Icc.mpr ⟨hp,Nat.le_floor (hl.le.trans (le_max_left _ _))⟩
  have hcard := card_le_card hs
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hcard
  exact (show (((goldbachCoefficientIndices L V).image Prod.fst).card:ℝ)≤⌊max L 0⌋₊ by
    exact_mod_cast hcard).trans (Nat.floor_le (le_max_right _ _))

theorem goldbach_source_index_card_square (N : ℕ) (hlog : 1≤Real.log N)
    (L : ℝ) (V : ℕ→ℝ) (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L → V ℓ≤Real.sqrt ((N:ℝ)^2/ℓ)) :
    ((goldbachCoefficientIndices L V).card:ℝ)^2≤3*(N:ℝ)^2*max L 0*Real.log N := by
  let I := goldbachCoefficientIndices L V
  have hc : (I.card:ℝ)=∑ ℓ∈I.image Prod.fst,((goldbachModuliAt I ℓ).card:ℝ) := by
    have h := goldbach_index_row_sum I (fun _ => (1:ℝ))
    simpa only [sum_const,nsmul_eq_mul,mul_one] using h
  have hrow := (goldbach_source_energy_numerical_ranges N L V hL hV).2.2
  have hs := sum_mul_sq_le_sq_mul_sq (I.image Prod.fst)
    (fun ℓ => ((goldbachModuliAt I ℓ).card:ℝ)) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,sum_const,nsmul_eq_mul] at hs
  have hsq : (∑ ℓ∈I.image Prod.fst,((goldbachModuliAt I ℓ).card:ℝ)^2)≤
      3*(N:ℝ)^2*Real.log N :=
    (sum_le_sum hrow).trans (goldbach_source_row_scale_sum N hlog L V hL)
  have hrows : ((I.image Prod.fst).card:ℝ)≤max L 0 := goldbach_source_row_card L V
  rw [hc]
  calc
    _≤(∑ ℓ∈I.image Prod.fst,((goldbachModuliAt I ℓ).card:ℝ)^2)*((I.image Prod.fst).card:ℝ) := hs
    _≤(3*(N:ℝ)^2*Real.log N)*max L 0 := mul_le_mul hsq hrows
      (Nat.cast_nonneg _) (by positivity)
    _=3*(N:ℝ)^2*max L 0*Real.log N := by ring

end PrimeSquares
