import PrimeSquares.GoldbachWeightedPairs
import PrimeSquares.GoldbachWeightedNormalization

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_finite_variable_interval {ι : Type*} (I : Finset ι) (a U : ℝ)
    (b : ι→ℝ) (f : ι→ℝ→ℝ) (hb : ∀ i∈I,b i≤U)
    (hi : ∀ i∈I,IntegrableOn (f i) (Set.Icc a U)) :
    (∑ i∈I,∫ t in Set.Icc a (b i),f i t)=
      ∫ t in Set.Icc a U,∑ i∈I.filter (fun i=>t≤b i),f i t := by
  classical
  simp_rw [sum_filter]
  have hint (i : ι) (hiI : i∈I) :
      IntegrableOn (fun t : ℝ=>if t≤b i then f i t else 0) (Set.Icc a U) := by
    exact (hi i hiI).indicator measurableSet_Iic
  rw [integral_finsetSum I hint]
  apply sum_congr rfl
  intro i hiI
  have hfun : (fun t : ℝ=>if t≤b i then f i t else 0)=(Set.Iic (b i)).indicator (f i) := rfl
  rw [hfun,setIntegral_indicator measurableSet_Iic]
  have hs : Set.Icc a U∩Set.Iic (b i)=Set.Icc a (b i) := by
    ext t
    simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Iic]
    exact ⟨fun h=>⟨h.1.1,h.2⟩,fun h=>⟨⟨h.1,h.2.trans (hb i hiI)⟩,h.2⟩⟩
  rw [hs]

theorem goldbach_weighted_outer_product_le_one (R z : ℝ) (a : ℕ) :
    goldbachWeightedOuterProduct R z a≤1 := by
  classical
  change (∏ p∈goldbachWeightedOuterPrimes R z a,(1-1/((p:ℝ)-1)))≤1
  suffices (∏ p∈goldbachWeightedOuterPrimes R z a,(1-1/((p:ℝ)-1)))≤
      ∏ _p∈goldbachWeightedOuterPrimes R z a,(1:ℝ) by simpa only [prod_const_one] using this
  apply prod_le_prod₀
  · intro p hp
    have hs := (mem_goldbach_weighted_outer_primes R z a p).mp hp
    have hpR : (3:ℝ)<p := by exact_mod_cast hs.2.1
    have hi : 1/((p:ℝ)-1)<1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  · intro p hp
    have hs := (mem_goldbach_weighted_outer_primes R z a p).mp hp
    have hpR : (3:ℝ)<p := by exact_mod_cast hs.2.1
    have hi : 0≤1/((p:ℝ)-1) := div_nonneg (by norm_num) (by linarith)
    linarith

theorem goldbach_finite_smoothing_upper {ι : Type*} (I : Finset ι) (w : ι→ℝ)
    (F G : ι→ℂ) (E : ℝ) (hw : ∀ i∈I,0≤w i) (hE : ∀ i∈I,‖F i-G i‖≤E) :
    (∑ i∈I,w i*(F i).re)≤(∑ i∈I,w i*(G i).re)+E*∑ i∈I,w i := by
  have hp : ∀ i∈I,(F i).re≤(G i).re+E := by
    intro i hi
    have hh := (Complex.abs_re_le_norm (F i-G i)).trans (hE i hi)
    have hl := le_abs_self (F i-G i).re
    simp only [Complex.sub_re] at hh hl
    linarith
  calc
    _≤∑ i∈I,w i*((G i).re+E) :=
      sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_left (hp i hi) (hw i hi))
    _=_ := by simp_rw [mul_add];rw [sum_add_distrib,←sum_mul];ring

theorem goldbach_finite_smoothing_outer_upper {ι : Type*} (I : Finset ι)
    (w V : ι→ℝ) (F G : ι→ℂ) (E : ℝ)
    (hw : ∀ i∈I,0≤w i) (hV : ∀ i∈I,0≤V i ∧ V i≤1)
    (hE0 : 0≤E) (hE : ∀ i∈I,‖F i-G i‖≤E) :
    (∑ i∈I,w i*V i*(F i).re)≤
      (∑ i∈I,w i*V i*(G i).re)+E*∑ i∈I,w i := by
  have hs := goldbach_finite_smoothing_upper I (fun i=>w i*V i) F G E
    (fun i hi=>mul_nonneg (hw i hi) (hV i hi).1) hE
  have hmass : (∑ i∈I,w i*V i)≤∑ i∈I,w i :=
    sum_le_sum (fun i hi=>mul_le_of_le_one_right (hw i hi) (hV i hi).2)
  have hh := mul_le_mul_of_nonneg_left hmass hE0
  linarith only [hs,hh]

end PrimeSquares
