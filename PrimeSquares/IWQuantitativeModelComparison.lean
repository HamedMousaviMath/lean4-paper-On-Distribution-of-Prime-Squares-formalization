import PrimeSquares.IWFiniteModelComparison
import PrimeSquares.IWSmallDenominatorDifference

set_option autoImplicit false
open Finset
open scoped lp
namespace PrimeSquares

theorem iw_small_difference_absorption {a : ℝ} (ha : 0≤a) {Q M : ℕ}
    (hQ : 4≤Q) (hM : 2≤M)
    (hbudget : ((Q : ℝ)+1)^2*a*(Q : ℝ)≤(M : ℝ)^2) :
    24*((canonicalRationalCenters Q).card : ℝ)*a/(Real.pi*(M : ℝ)^2)≤
      (24/Real.pi)*(Q : ℝ)^(-(1/4 : ℝ)) := by
  have hQ0 : (0 : ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hM0 : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hcard : ((canonicalRationalCenters Q).card : ℝ)≤((Q : ℝ)+1)^2 := by
    exact_mod_cast canonicalRationalCenters_card Q
  have hb : ((canonicalRationalCenters Q).card : ℝ)*a*(Q : ℝ)≤(M : ℝ)^2 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard ha) hQ0.le).trans hbudget
  have hr : ((canonicalRationalCenters Q).card : ℝ)*a/(M : ℝ)^2≤1/(Q : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hM0) hQ0).mpr
    simpa only [one_mul] using hb
  have hpow : 1/(Q : ℝ)≤(Q : ℝ)^(-(1/4 : ℝ)) := by
    rw [one_div,←Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤Q by omega)) (by norm_num)
  calc
    _ = (24/Real.pi)*(((canonicalRationalCenters Q).card : ℝ)*a/(M : ℝ)^2) := by ring
    _ ≤ (24/Real.pi)*(1/(Q : ℝ)) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The actual original-cutoff circle model and its actual common-cutoff IW
model differ by an operator with a uniform Q^(-1/4) countable maximum.
The coefficient bounds are internal premises and are proved for the concrete
principal and character coefficients separately. -/
theorem iw_quantitative_model_comparison {C Cb A : ℝ} (hC : 2≤C) (hCb : 0≤Cb)
    (HB : SmoothCircleBourgainInput Cb) (hA : 0≤A)
    {r k Q M : ℕ} (hr : 2≤r) (hk : 4≤k) (hQ : 2^k≤Q) (hM : 2≤M)
    (d : TaoArcConstructionData C (iwRho k) k Q)
    (hbudget : ((Q : ℝ)+1)^2*iwCutoffScale C r k Q*(Q : ℝ)≤(M : ℝ)^2)
    (β : ℕ → ℝ) (hβ0 : ∀ j,0≤β j) (hβ1 : ∀ j,β j≤1)
    (c : ℚ → ℂ) (hc : ∀ t,t∈Set.Ico (0 : ℚ) 1 → ‖c t‖≤A*(t.den : ℝ)^(-(3/8 : ℝ)))
    (hsmall : ∀ t∈canonicalRationalCenters Q,‖c t‖≤1)
    (R : ℕ → ℝ) (hR : ∀ j,(Q : ℝ)≤R j) (f : ℓ²(ℤ,ℂ)) :
    ∃ g : lp (fun _ : ℤ => ℝ) 2,(∀ x,0≤g x) ∧
      (∀ j x,‖integerMultiplier
        (varyingIndexAnnularBlock (sourceRationalCenters (R j)) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (β j) c-
        weightedWidthAnnularBlock (iwFrequencySet d.S k) ((2 : ℕ)^j*M)
          (by have h := dyadic_annular_scale_lower hM j;omega) (β j) (iwCutoffScale C r k Q)
          (by have h := iwCutoffScale_four_le hC hr k Q;linarith) c) f x‖≤g x) ∧
      ‖g‖≤((2*annularPowerConstant Cb (1/8)*A+24/Real.pi)*(Q : ℝ)^(-(1/4 : ℝ)))*‖f‖ := by
  classical
  have h16 : 16≤2^k := by
    calc
      16 = 2^4 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hQ4 : 4≤Q := by omega
  have hQ0 : (0 : ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hR0 : ∀ j,0≤R j := fun j => hQ0.le.trans (hR j)
  let a := iwCutoffScale C r k Q
  have ha : 4≤a := iwCutoffScale_four_le hC hr k Q
  let Γ := iwFrequencySet d.S k
  have hcan : ∀ t∈Γ,t∈Set.Ico (0 : ℚ) 1 := fun t ht => ((iwFrequencySet_mem d.positive t).mp ht).1
  have hwide : ∀ t∈Γ,2*(16 : ℝ)^(Nat.log2 t.den)≤a :=
    fun t ht => iwCutoffScale_band_core hC hr hk d ht
  have hscale : ∀ t∈canonicalRationalCenters Q,(16 : ℝ)^(Nat.log2 t.den)≤a := by
    intro t ht
    have hw := hwide t (d.covered ht)
    have hp : 0<(16 : ℝ)^(Nat.log2 t.den) := by positivity
    linarith
  obtain ⟨go,hgo,hto,hno⟩ := iw_annular_denominator_tail hCb HB hA hQ0 hM β hβ0 hβ1 c hc R hR0 f
  obtain ⟨gl,hgl,htl,hnl⟩ := common_cutoff_denominator_tail hCb HB hA ha
    (by exact_mod_cast hQ4 : (4 : ℝ)≤Q) hM Γ hcan
    (fun t ht => Finset.le_sup (f := Rat.den) ht) hwide β hβ0 hβ1 c (fun t ht => hc t (hcan t ht)) f
  obtain ⟨gd,hgd,htd,hnd⟩ := common_source_difference_maximum hM (canonicalRationalCenters Q)
    (by linarith : 2≤a) (by norm_num : (0 : ℝ)≤1) hscale β hβ0 hβ1 c hsmall f
  have hset (T : Finset ℚ) : T.filter (fun t => (Q : ℝ)<(t.den : ℝ))=T.filter (fun t => Q<t.den) := by
    ext t
    simp only [mem_filter,Nat.cast_lt]
  simp only [hset] at hto htl
  have hnd' : ‖gd‖≤((24/Real.pi)*(Q : ℝ)^(-(1/4 : ℝ)))*‖f‖ := by
    exact hnd.trans (mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using iw_small_difference_absorption (by linarith : 0≤a) hQ4 hM hbudget)
      (norm_nonneg _))
  refine ⟨go+gl+gd,fun x => add_nonneg (add_nonneg (hgo x) (hgl x)) (hgd x),?_,?_⟩
  · intro j x
    rw [iw_original_common_comparison d (hR j),integerMultiplier_add,integerMultiplier_sub,
      _root_.add_apply,_root_.sub_apply,lp.coeFn_add,lp.coeFn_sub,Pi.add_apply,Pi.sub_apply]
    change _≤go x+gl x+gd x
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (hto j x) (htl j x))) (htd j x))
  · have hn := (norm_add_le (go+gl) gd).trans
      (add_le_add ((norm_add_le go gl).trans (add_le_add hno hnl)) hnd')
    exact hn.trans_eq (by ring)

end PrimeSquares
