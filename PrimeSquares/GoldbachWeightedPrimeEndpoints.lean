import PrimeSquares.GoldbachWeightedPrimeBalance

set_option autoImplicit false
open Finset MeasureTheory
namespace PrimeSquares

theorem goldbach_finite_real_endpoint (P : Finset ℕ) (z E : ℝ) (hE : 0≤E)
    (F : ℕ→ℝ) (hF : ∀ p∈P,(p:ℝ)=z→F p≤E) :
    (∑ p∈P.filter (fun p : ℕ=>(p:ℝ)=z),F p)≤E := by
  classical
  let S := P.filter (fun p : ℕ=>(p:ℝ)=z)
  have hs : S⊆{⌊z⌋₊} := by
    intro p hp
    have he := (mem_filter.mp hp).2
    simp only [mem_singleton]
    rw [←he,Nat.floor_natCast]
  have hc : S.card≤1 := by simpa only [card_singleton] using card_le_card hs
  have hcR : (S.card:ℝ)≤1 := by exact_mod_cast hc
  calc
    _≤∑ _p∈S,E := sum_le_sum (fun p hp=>hF p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
    _=(S.card:ℝ)*E := by simp only [sum_const,nsmul_eq_mul]
    _≤E := by nlinarith only [mul_le_mul_of_nonneg_right hcR hE]

theorem goldbach_weighted_prime_finite_upper (K M c z b : ℝ)
    (hK : 0≤K) (hM : ClassicalPrimeLogMertens K) (hz : 2≤z) (hzb : z≤b)
    (hL : ∀ t∈Set.Icc z b,0<M-Real.log c-Real.log t ∧
      M-Real.log c-Real.log t≤2*Real.log t)
    (hLz : Real.log z≤M-Real.log c-Real.log z)
    (hLb : Real.log z≤M-Real.log c-Real.log b)
    (P : Finset ℕ) (hP : ∀ p∈P,p.Prime ∧ p%4=3 ∧ z≤(p:ℝ) ∧ (p:ℝ)≤b) :
    (∑ p∈P,1/((p:ℝ)*(M-Real.log c-Real.log p)^2))≤
      (1/2:ℝ)*(∫ t in Set.Ioc z b,1/(t*Real.log t*(M-Real.log c-Real.log t)^2))+
        2*(2*K+1)/(Real.log z)^3+1/(z*(Real.log z)^2) := by
  classical
  let F := fun p : ℕ=>1/((p:ℝ)*(M-Real.log c-Real.log p)^2)
  let Q := (Ioc ⌊z⌋₊ ⌊b⌋₊).filter (fun p : ℕ=>p.Prime ∧ p%4=3)
  have hz0 : 0<z := by linarith
  have hlogz : 0<Real.log z := Real.log_pos (by linarith)
  have hlogb : Real.log z≤Real.log b := Real.log_le_log hz0 hzb
  have hLz0 : 0<M-Real.log c-Real.log z := hlogz.trans_le hLz
  have hLb0 : 0<M-Real.log c-Real.log b := hlogz.trans_le hLb
  have hsub : P.filter (fun p : ℕ=>¬(p:ℝ)=z)⊆Q := by
    intro p hp
    obtain ⟨hpP,hpne⟩ := mem_filter.mp hp
    obtain ⟨hp,hp4,hpz,hpb⟩ := hP p hpP
    exact mem_filter.mpr ⟨mem_Ioc.mpr
      ⟨(Nat.floor_lt hz0.le).mpr (lt_of_le_of_ne hpz (Ne.symm hpne)),
        (Nat.le_floor_iff (by linarith : (0:ℝ)≤b)).mpr hpb⟩,hp,hp4⟩
  have hrest : (∑ p∈P.filter (fun p : ℕ=>¬(p:ℝ)=z),F p)≤∑ p∈Q,F p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p _ _=>by
      dsimp only [F]
      exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  have hend : (∑ p∈P.filter (fun p : ℕ=>(p:ℝ)=z),F p)≤1/(z*(Real.log z)^2) := by
    apply goldbach_finite_real_endpoint P z _ (by positivity) F
    intro p hp he
    dsimp only [F]
    rw [he]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogz.le hLz 2) hz0.le)
  have hkernel : goldbachWeightedPrimeKernel M c b≤1/(Real.log z)^3 := by
    dsimp only [goldbachWeightedPrimeKernel]
    have hm := mul_le_mul hlogb (pow_le_pow_left₀ hlogz.le hLb 2)
      (sq_nonneg _) (by linarith : 0≤Real.log b)
    have hd : (Real.log z)^3≤Real.log b*(M-Real.log c-Real.log b)^2 := by
      nlinarith only [hm]
    exact one_div_le_one_div_of_le (by positivity) hd
  have ha := goldbach_weighted_prime_abel K M c z b hK hM hz hzb hL
  have hcoef : 0≤2*(2*K+1) := by positivity
  have he : (∑ p∈P.filter (fun p : ℕ=>(p:ℝ)=z),F p)+
      (∑ p∈P.filter (fun p : ℕ=>¬(p:ℝ)=z),F p)=∑ p∈P,F p :=
    sum_filter_add_sum_filter_not P _ F
  have hh := mul_le_mul_of_nonneg_left hkernel hcoef
  simp only [mul_one_div] at hh
  dsimp only [Q,F] at hrest
  dsimp only [F] at he hend
  linarith only [he,hend,hrest,ha,hh]

end PrimeSquares
