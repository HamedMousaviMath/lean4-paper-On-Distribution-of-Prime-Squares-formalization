import PrimeSquares.GoldbachHybridMinorComplete

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachPrimeProgressionCutoff (k a : ℕ) (W : ℝ) : Finset ℕ :=
  (goldbachPrimeCutoff W).filter (fun t => t%k=a%k)

theorem mem_goldbachPrimeProgressionCutoff {k a t : ℕ} {W : ℝ} (hW : 0≤W) :
    t∈goldbachPrimeProgressionCutoff k a W ↔ t.Prime ∧ (t:ℝ)≤W ∧ t%k=a%k := by
  simp only [goldbachPrimeProgressionCutoff,mem_filter,mem_goldbachPrimeCutoff hW]
  exact and_assoc

theorem goldbach_progression_strict_endpoint (N ℓ k a : ℕ) (hℓ : 0<ℓ)
    {W : ℝ} (hW : 0≤W) (hWX : W≤(N:ℝ)^2/ℓ) :
    goldbachProgressionCutoff N ℓ k a W=
      (goldbachPrimeProgressionCutoff k a W).filter (fun t => ℓ*t≠N^2) := by
  classical
  have hlR : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  ext t
  rw [mem_goldbachProgressionCutoff hW,mem_filter,mem_goldbachPrimeProgressionCutoff hW]
  have htbound : (t:ℝ)≤W → ℓ*t≤N^2 := by
    intro ht
    have hm := mul_le_mul_of_nonneg_left (ht.trans hWX) hlR.le
    have he : (ℓ:ℝ)*((N:ℝ)^2/ℓ)=(N:ℝ)^2 := by field_simp
    rw [he] at hm
    exact_mod_cast hm
  constructor
  · rintro ⟨hp,ht,hlt,ha⟩
    exact ⟨⟨hp,ht,ha⟩,by omega⟩
  · rintro ⟨⟨hp,ht,ha⟩,hne⟩
    exact ⟨hp,ht,by have hb:=htbound ht;omega,ha⟩

theorem goldbach_progression_endpoint_card (N ℓ k a : ℕ) (hℓ : 0<ℓ) (W : ℝ) :
    ((goldbachPrimeProgressionCutoff k a W).filter (fun t => ℓ*t=N^2)).card≤1 := by
  classical
  apply card_le_one.mpr
  intro s hs t ht
  have hs' := (mem_filter.mp hs).2
  have ht' := (mem_filter.mp ht).2
  exact Nat.eq_of_mul_eq_mul_left hℓ (hs'.trans ht'.symm)

theorem goldbach_progression_endpoint_error (N ℓ k a : ℕ) (hℓ : 0<ℓ)
    {W : ℝ} (hW : 0≤W) (hWX : W≤(N:ℝ)^2/ℓ) (θ : PrimeCircle) :
    ‖(∑ t∈goldbachPrimeProgressionCutoff k a W,fourier ((ℓ*t:ℕ):ℤ) θ)-
      goldbachProgressionPolynomial N ℓ k a W θ‖≤1 := by
  classical
  have hs : (∑ t∈goldbachPrimeProgressionCutoff k a W,fourier ((ℓ*t:ℕ):ℤ) θ)=
      (∑ t∈(goldbachPrimeProgressionCutoff k a W).filter (fun t => ℓ*t=N^2),
        fourier ((ℓ*t:ℕ):ℤ) θ)+goldbachProgressionPolynomial N ℓ k a W θ := by
    rw [←sum_filter_add_sum_filter_not (goldbachPrimeProgressionCutoff k a W)
      (fun t => ℓ*t=N^2) (fun t => fourier ((ℓ*t:ℕ):ℤ) θ)]
    rw [goldbachProgressionPolynomial,goldbach_progression_strict_endpoint N ℓ k a hℓ hW hWX]
    simp only [ContinuousMap.sum_apply]
  rw [hs,add_sub_cancel_right]
  calc
    _≤∑ t∈(goldbachPrimeProgressionCutoff k a W).filter (fun t => ℓ*t=N^2),
      ‖fourier ((ℓ*t:ℕ):ℤ) θ‖ := norm_sum_le _ _
    _=(((goldbachPrimeProgressionCutoff k a W).filter (fun t => ℓ*t=N^2)).card:ℝ) := by
      simp only [fourier_apply,Circle.norm_coe,sum_const,nsmul_eq_mul,mul_one]
    _≤1 := by exact_mod_cast goldbach_progression_endpoint_card N ℓ k a hℓ W

theorem goldbach_progression_cutoff_min (N ℓ k a : ℕ) (hℓ : 0<ℓ)
    {W : ℝ} (hW : 0≤W) :
    goldbachProgressionCutoff N ℓ k a (min W ((N:ℝ)^2/ℓ))=
      goldbachProgressionCutoff N ℓ k a W := by
  classical
  have hX : 0≤(N:ℝ)^2/ℓ := by positivity
  have hlR : (0:ℝ)<ℓ := by exact_mod_cast hℓ
  ext t
  rw [mem_goldbachProgressionCutoff (le_min hW hX),mem_goldbachProgressionCutoff hW]
  constructor
  · rintro ⟨hp,ht,hlt,ha⟩
    exact ⟨hp,ht.trans (min_le_left _ _),hlt,ha⟩
  · rintro ⟨hp,ht,hlt,ha⟩
    refine ⟨hp,le_min ht ?_,hlt,ha⟩
    apply (le_div_iff₀ hlR).mpr
    have hh : (ℓ:ℝ)*(t:ℝ)<(N:ℝ)^2 := by exact_mod_cast hlt
    nlinarith

end PrimeSquares
