import PrimeSquares.GoldbachWeightedLocalFactors

set_option autoImplicit false
namespace PrimeSquares

theorem goldbach_weighted_factor_geometry (t u p : ℝ) (ht : 1<t) (hu : 0<u)
    (huB : u<t^2/2) (_hp : 0<p) (hpB : 2*u*p^2<t^18) :
    2*u*p<t^10 := by
  have h₁ : (2*u*p)^2<2*u*t^18 := by
    have hh := mul_lt_mul_of_pos_left hpB (show 0<2*u by positivity)
    nlinarith only [hh]
  have h₂ : 2*u*t^18<t^20 := by
    have hh := mul_lt_mul_of_pos_right huB (show 0<t^18 by positivity)
    nlinarith only [hh]
  have hten : 0<t^10 := by positivity
  have hsq : (2*u*p)^2<(t^10)^2 := by
    calc
      _<t^20 := h₁.trans h₂
      _=(t^10)^2 := by ring
  nlinarith only [hsq,hten,show 0≤2*u*p by positivity]

theorem goldbach_weighted_level_geometry (t u p : ℝ) (ht : 1<t) (hu : 1≤u)
    (huB : u<t^2/2) (hp : t^8≤p) (hpB : 2*u*p^2<t^18) :
    u<(t^18/(2*u*p))^(1/4:ℝ) ∧
      t^2<(t^18/(2*u*p))^(1/4:ℝ) ∧
      (t^18/(2*u*p))^(1/4:ℝ)<t^8 ∧
      (t^18/(2*u*p))^(1/4:ℝ)<p := by
  have ht0 : 0<t := by linarith
  have hu0 : 0<u := by linarith
  have hp0 : 0<p := (by positivity : 0<t^8).trans_le hp
  have hℓ0 : 0<2*u*p := by positivity
  have hℓ := goldbach_weighted_factor_geometry t u p ht hu0 huB hp0 hpB
  have hquot : 0<t^18/(2*u*p) := div_pos (by positivity) hℓ0
  have hr4 : ((t^18/(2*u*p))^(1/4:ℝ))^4=t^18/(2*u*p) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hquot.le]
    norm_num
  have hr0 : 0<(t^18/(2*u*p))^(1/4:ℝ) := Real.rpow_pos_of_pos hquot _
  have hlow : (t^2)^4<t^18/(2*u*p) := by
    apply (lt_div_iff₀ hℓ0).mpr
    have hh := mul_lt_mul_of_pos_left hℓ (show 0<t^8 by positivity)
    convert hh using 1 <;> ring
  have hlow' : t^2<(t^18/(2*u*p))^(1/4:ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 4 hr0.le
    rwa [hr4]
  have hu2 : 0<2*u := by positivity
  have hup : (t^18/(2*u*p))^(1/4:ℝ)<t^8 := by
    apply lt_of_pow_lt_pow_left₀ 4 (show 0≤t^8 by positivity)
    rw [hr4]
    apply (div_lt_iff₀ hℓ0).mpr
    have hpow : t^18<t^40 := pow_lt_pow_right₀ ht (by decide : 18<40)
    have hh := mul_le_mul_of_nonneg_left hp (show 0≤(t^8)^4*(2*u) by positivity)
    have hh' : t^40≤(t^8)^4*(2*u)*t^8 := by
      have hbig : 1≤2*u := by linarith
      have hmul := mul_le_mul_of_nonneg_left hbig (show 0≤t^40 by positivity)
      convert hmul using 1 <;> ring
    have hlast : t^18<(t^8)^4*(2*u*p) := by nlinarith only [hpow,hh,hh']
    exact hlast
  exact ⟨lt_trans (by nlinarith only [huB,show 0<t^2 by positivity]) hlow',hlow',hup,hup.trans_le hp⟩

theorem goldbach_weighted_multiplier_geometry {N ℓ : ℕ} (hN : 2≤N)
    (hℓ : ℓ∈goldbachClosedLSet N ((N:ℝ)^(8/9:ℝ))) :
    ∃ u p : ℕ,0<u ∧ ℓ=2*u*p ∧ p.Prime ∧ p%4=3 ∧
      (∀ q : ℕ,q.Prime→q∣u→q%4=1) ∧
      (ℓ:ℝ)<(N:ℝ)^(10/9:ℝ) ∧
      (u:ℝ)<goldbachUpperSieveLevel N ℓ ∧
      (N:ℝ)^(2/9:ℝ)<goldbachUpperSieveLevel N ℓ ∧
      goldbachUpperSieveLevel N ℓ<(N:ℝ)^(8/9:ℝ) ∧
      goldbachUpperSieveLevel N ℓ<(p:ℝ) := by
  obtain ⟨u,p,hu,he,huB,hp,hp4,hpz,hpB,hU⟩ := mem_goldbachClosedLSet.mp hℓ
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  let t := (N:ℝ)^(1/9:ℝ)
  have ht : 1<t := Real.one_lt_rpow hN1 (by norm_num)
  have ht0 : 0<t := by linarith
  have htpow (k : ℕ) : t^k=(N:ℝ)^((k:ℝ)/9) := by
    dsimp only [t]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN0.le]
    congr 1
    ring
  have ht18 : t^18=(N:ℝ)^2 := by
    simpa only [show ((18:ℕ):ℝ)/9=2 by norm_num,Real.rpow_two] using htpow 18
  have ht8 : t^8=(N:ℝ)^(8/9:ℝ) := by simpa only [Nat.cast_ofNat] using htpow 8
  have ht2 : t^2=(N:ℝ)^(2/9:ℝ) := by simpa only [Nat.cast_ofNat] using htpow 2
  have ht10 : t^10=(N:ℝ)^(10/9:ℝ) := by simpa only [Nat.cast_ofNat] using htpow 10
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hu1 : (1:ℝ)≤u := by exact_mod_cast hu
  have hquot : (N:ℝ)^2/(2*((N:ℝ)^(8/9:ℝ))^2)=t^2/2 := by
    rw [←ht18,←ht8]
    field_simp
  rw [hquot] at huB
  rw [←ht8] at hpz
  have hpR : (0:ℝ)≤p := by positivity
  have hs := (Real.lt_sqrt hpR).mp hpB
  have hs' : 2*(u:ℝ)*(p:ℝ)^2<t^18 := by
    rw [←ht18] at hs
    have hh := (lt_div_iff₀ (show 0<2*(u:ℝ) by positivity)).mp hs
    nlinarith only [hh]
  have hh := goldbach_weighted_factor_geometry t (u:ℝ) (p:ℝ) ht huR huB
    (by exact_mod_cast hp.pos) hs'
  have hg := goldbach_weighted_level_geometry t (u:ℝ) (p:ℝ) ht hu1 huB hpz hs'
  have hlevel : goldbachUpperSieveLevel N ℓ=(t^18/(2*(u:ℝ)*(p:ℝ)))^(1/4:ℝ) := by
    simp only [goldbachUpperSieveLevel,he,Nat.cast_mul,Nat.cast_ofNat,ht18]
  refine ⟨u,p,hu,he,hp,hp4,hU,?_,?_,?_,?_,?_⟩
  · simp only [he,Nat.cast_mul,Nat.cast_ofNat]
    rw [←ht10]
    exact hh
  · rw [hlevel]
    exact hg.1
  · rw [hlevel,←ht2]
    exact hg.2.1
  · rw [hlevel,←ht8]
    exact hg.2.2.1
  · rw [hlevel]
    exact hg.2.2.2

end PrimeSquares
