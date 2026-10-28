import PrimeSquares.GoldbachLogarithmicEnergy

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_source_row_cutoffs (L : ℝ) (V : ℕ→ℝ) (ℓ : ℕ)
    (hℓ : ℓ∈(goldbachCoefficientIndices L V).image Prod.fst) :
    0<ℓ ∧ (ℓ:ℝ)<L ∧ 1<V ℓ := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hℓ
  obtain ⟨hlpos,hl,hkpos,hk⟩ := (mem_goldbachCoefficientIndices L V i.1 i.2).mp hi
  have hk1 : (1:ℝ) ≤ i.2 := by exact_mod_cast hkpos
  exact ⟨hlpos,hl,hk1.trans_lt hk⟩

theorem goldbach_source_energy_numerical_ranges (N : ℕ) (L : ℝ) (V : ℕ→ℝ)
    (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L → V ℓ≤Real.sqrt ((N:ℝ)^2/(ℓ:ℝ))) :
    (∀ i ∈ goldbachCoefficientIndices L V, 0 < (i.1 : ℕ) ∧ i.1≤N^2) ∧
    (∀ ℓ∈(goldbachCoefficientIndices L V).image Prod.fst,
      goldbachModuliAt (goldbachCoefficientIndices L V) ℓ⊆Icc 1 N) ∧
    (∀ ℓ∈(goldbachCoefficientIndices L V).image Prod.fst,
      ((goldbachModuliAt (goldbachCoefficientIndices L V) ℓ).card:ℝ)^2≤(N:ℝ)^2/(ℓ:ℝ)) := by
  classical
  let I := goldbachCoefficientIndices L V
  have hrow (ℓ : ℕ) (hℓ : ℓ∈I.image Prod.fst) :
      0<ℓ ∧ 0≤V ℓ ∧ (V ℓ)^2≤(N:ℝ)^2/(ℓ:ℝ) := by
    obtain ⟨hℓpos,hℓL,hℓV⟩ := goldbach_source_row_cutoffs L V ℓ hℓ
    have hVpos : 0≤V ℓ := by linarith
    have hh := pow_le_pow_left₀ hVpos (hV ℓ hℓpos hℓL) 2
    rw [Real.sq_sqrt (by positivity)] at hh
    exact ⟨hℓpos,hVpos,hh⟩
  refine ⟨?_,?_,?_⟩
  · intro i hi
    obtain ⟨hlpos,hl,_,_⟩ := (mem_goldbachCoefficientIndices L V i.1 i.2).mp hi
    exact ⟨hlpos,by exact_mod_cast hl.le.trans hL⟩
  · intro ℓ hℓ k hk
    have hi := (mem_goldbachModuliAt I ℓ k).mp hk
    obtain ⟨_,_,hkpos,hkV⟩ := (mem_goldbachCoefficientIndices L V ℓ k).mp hi
    obtain ⟨hℓpos,_,hV2⟩ := hrow ℓ hℓ
    have hk2 := (pow_le_pow_left₀ (Nat.cast_nonneg k) hkV.le 2).trans hV2
    have hℓR : (0:ℝ)<ℓ := by exact_mod_cast hℓpos
    have hℓ1 : (1:ℝ)≤ℓ := by exact_mod_cast hℓpos
    have hq : (N:ℝ)^2/(ℓ:ℝ)≤(N:ℝ)^2 :=
      (div_le_iff₀ hℓR).mpr (by nlinarith [sq_nonneg (N:ℝ)])
    have hkN : (k:ℝ)≤N := by
      nlinarith [hk2.trans hq,(show (0:ℝ)≤N from Nat.cast_nonneg N)]
    exact mem_Icc.mpr ⟨hkpos,by exact_mod_cast hkN⟩
  · intro ℓ hℓ
    obtain ⟨_,hVpos,hV2⟩ := hrow ℓ hℓ
    have hsub : goldbachModuliAt I ℓ⊆Icc 1 ⌊V ℓ⌋₊ := by
      intro k hk
      have hi := (mem_goldbachModuliAt I ℓ k).mp hk
      obtain ⟨_,_,hkpos,hkV⟩ := (mem_goldbachCoefficientIndices L V ℓ k).mp hi
      exact mem_Icc.mpr ⟨hkpos,(Nat.le_floor_iff hVpos).mpr hkV.le⟩
    have hcard := (card_le_card hsub).trans_eq (show (Icc 1 ⌊V ℓ⌋₊).card=⌊V ℓ⌋₊ by simp)
    have hcardR : ((goldbachModuliAt I ℓ).card:ℝ)≤V ℓ :=
      (show ((goldbachModuliAt I ℓ).card:ℝ)≤(⌊V ℓ⌋₊:ℝ) by exact_mod_cast hcard).trans
        (Nat.floor_le hVpos)
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcardR 2).trans hV2

/-- The source's complete progression-energy estimate, with explicit constant.
Neither a mean-square theorem nor an own-paper endpoint is assumed. -/
theorem goldbach_source_progression_energy (N : ℕ) (hN : 1≤N)
    (hlog : 1≤Real.log N) (L B : ℝ) (V : ℕ→ℝ) (hB : 0≤B)
    (hL : L≤(N:ℝ)^2)
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
      V ℓ≤Real.sqrt ((N:ℝ)^2/(ℓ:ℝ))*(Real.log N)^(-B))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ)
    (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N
      (goldbachCoefficientIndices L V) a d W θ‖^2 ∂AddCircle.haarAddCircle)≤
        (256/Real.log 2)*(N:ℝ)^2*(Real.log N)^6 := by
  have hpow : (Real.log N)^(-B)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)
  have hVplain (ℓ : ℕ) (hℓ : 0<ℓ) (hℓL : (ℓ:ℝ)<L) :
      V ℓ≤Real.sqrt ((N:ℝ)^2/(ℓ:ℝ)) :=
    (hV ℓ hℓ hℓL).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
        (Real.sqrt_nonneg ((N:ℝ)^2/(ℓ:ℝ))))
  obtain ⟨hI,hK,hc⟩ := goldbach_source_energy_numerical_ranges N L V hL hVplain
  have he := goldbach_progression_energy_log_five N hN _ a d W hI hK hc hd
  have hp5 : (1+Real.log N)^5≤(2*Real.log N)^5 :=
    pow_le_pow_left₀ (by linarith : 0≤1+Real.log N) (by linarith) 5
  have hp6 : (Real.log N)^5≤(Real.log N)^6 := pow_le_pow_right₀ hlog (by decide)
  have hp : (1+Real.log N)^5≤32*(Real.log N)^6 := by
    have hh : (2*Real.log N)^5=32*(Real.log N)^5 := by ring
    exact (hp5.trans_eq hh).trans (mul_le_mul_of_nonneg_left hp6 (by norm_num : (0:ℝ)≤32))
  calc
    _≤(8/Real.log 2)*(N:ℝ)^2*(1+Real.log N)^5 := he
    _≤(8/Real.log 2)*(N:ℝ)^2*(32*(Real.log N)^6) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _=_ := by ring

theorem goldbach_source_progression_energy_printed_range (N : ℕ) (hN : 1≤N)
    (hlog : 1≤Real.log N) (L B δ : ℝ) (V : ℕ→ℝ) (hB : 0≤B) (hδ : 0<δ)
    (hL : L<(N:ℝ)^(2-δ))
    (hV : ∀ ℓ : ℕ,0<ℓ → (ℓ:ℝ)<L →
      V ℓ≤Real.sqrt ((N:ℝ)^2/(ℓ:ℝ))*(Real.log N)^(-B))
    (a : ℕ×ℕ→ℕ) (d : ℕ×ℕ→ℂ) (W : ℝ)
    (hd : ∀ i∈goldbachCoefficientIndices L V,‖d i‖≤1) :
    (∫ θ : PrimeCircle,‖goldbachWeightedProgressionPolynomial N
      (goldbachCoefficientIndices L V) a d W θ‖^2 ∂AddCircle.haarAddCircle)≤
        (256/Real.log 2)*(N:ℝ)^2*(Real.log N)^6 := by
  have hpow : (N:ℝ)^(2-δ)≤(N:ℝ)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN : (1:ℝ)≤N) (show 2-δ≤(2:ℝ) by linarith)
  exact goldbach_source_progression_energy N hN hlog L B V hB (hL.le.trans hpow) hV a d W hd

end PrimeSquares
