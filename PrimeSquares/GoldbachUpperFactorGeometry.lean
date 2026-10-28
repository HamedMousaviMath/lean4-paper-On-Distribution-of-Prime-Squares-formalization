import PrimeSquares.GoldbachTruncationReduction

set_option autoImplicit false
open Finset
namespace PrimeSquares

def GoldbachClosedL (N : ℕ) (z : ℝ) (ℓ : ℕ) : Prop :=
  ∃ u p : ℕ,0<u ∧ ℓ=2*u*p ∧ (u:ℝ)<(N:ℝ)^2/(2*z^2) ∧
    p.Prime ∧ p%4=3 ∧ z≤(p:ℝ) ∧ (p:ℝ)<Real.sqrt ((N:ℝ)^2/(2*(u:ℝ))) ∧
    ∀ s : ℕ,s.Prime → s∣u → s%4=1

noncomputable def goldbachClosedLSet (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (range (N^2)).filter (GoldbachClosedL N z)

noncomputable def goldbachClosedLn (n N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (goldbachClosedLSet N z).filter (fun ℓ => ℓ.Coprime (n-1))

noncomputable def goldbachUpperM (n N ℓ : ℕ) : Finset ℕ := by
  classical
  exact (range (N^2)).filter (fun r => ∃ p q : ℕ,
    p.Prime ∧ p%4=3 ∧ q.Prime ∧ 3<q ∧ r=ℓ*p+1 ∧ r+q^2=n)

def GoldbachUpperSievePrime (n ℓ p : ℕ) : Prop := p.Prime ∧ ¬p∣12*ℓ*n

noncomputable def goldbachUpperSieveLevel (N ℓ : ℕ) : ℝ :=
  ((N:ℝ)^2/(ℓ:ℝ))^(1/4:ℝ)

noncomputable def goldbachUpperSifted (n N ℓ : ℕ) : Finset ℕ := by
  classical
  exact (goldbachUpperM n N ℓ).filter (fun r => ∀ p : ℕ,
    GoldbachUpperSievePrime n ℓ p → (p:ℝ)<goldbachUpperSieveLevel N ℓ → ¬p∣r)

theorem goldbachClosedL_bound {N ℓ : ℕ} {z : ℝ} (h : GoldbachClosedL N z ℓ) : ℓ<N^2 := by
  obtain ⟨u,p,hu,he,_,hp,_,_,hps,_⟩ := h
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hpR : (1:ℝ)≤p := by exact_mod_cast hp.one_le
  have hsq := (Real.lt_sqrt (show (0:ℝ)≤p by positivity)).mp hps
  have hh := (lt_div_iff₀ (show 0<2*(u:ℝ) by positivity)).mp hsq
  have hpp : (p:ℝ)≤(p:ℝ)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hpp (show 0≤2*(u:ℝ) by positivity)
  have hreal : (ℓ:ℝ)<(N:ℝ)^2 := by
    have he' : (ℓ:ℝ)=2*(u:ℝ)*p := by exact_mod_cast he
    nlinarith only [he',hmul,hh]
  exact_mod_cast hreal

theorem mem_goldbachClosedLSet {N ℓ : ℕ} {z : ℝ} :
    ℓ∈goldbachClosedLSet N z ↔ GoldbachClosedL N z ℓ := by
  classical
  simp only [goldbachClosedLSet,mem_filter,mem_range]
  exact ⟨And.right,fun h => ⟨goldbachClosedL_bound h,h⟩⟩

theorem goldbach_upper_factor_geometry {N u p₁ p₂ : ℕ} (hu : 0<u)
    (hp₂ : p₂.Prime) (horder : p₂≤p₁) {z : ℝ} (hz : 0<z) (hpz : z≤(p₂:ℝ))
    (hsize : 2*u*p₁*p₂<N^2) :
    (u:ℝ)<(N:ℝ)^2/(2*z^2) ∧ (p₂:ℝ)<Real.sqrt ((N:ℝ)^2/(2*(u:ℝ))) := by
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hpR : (0:ℝ)<p₂ := by exact_mod_cast hp₂.pos
  have ho : (p₂:ℝ)≤p₁ := by exact_mod_cast horder
  have hs : 2*(u:ℝ)*p₁*p₂<(N:ℝ)^2 := by exact_mod_cast hsize
  have hp2 : (p₂:ℝ)^2≤(p₁:ℝ)*p₂ := by nlinarith
  have hz2 : z^2≤(p₂:ℝ)^2 := pow_le_pow_left₀ hz.le hpz 2
  have hh := mul_le_mul_of_nonneg_left (hz2.trans hp2) (show 0≤2*(u:ℝ) by positivity)
  have hh' := mul_le_mul_of_nonneg_left hp2 (show 0≤2*(u:ℝ) by positivity)
  constructor
  · apply (lt_div_iff₀ (show 0<2*z^2 by positivity)).mpr
    nlinarith only [hh,hs]
  · apply Real.lt_sqrt_of_sq_lt
    apply (lt_div_iff₀ (show 0<2*(u:ℝ) by positivity)).mpr
    nlinarith only [hh',hs]

theorem goldbach_upper_level_le_sqrt {N ℓ : ℕ} (hℓ : 1≤ℓ) :
    goldbachUpperSieveLevel N ℓ≤(N:ℝ)^(1/2:ℝ) := by
  have hℓR : (1:ℝ)≤ℓ := by exact_mod_cast hℓ
  have hd : (N:ℝ)^2/(ℓ:ℝ)≤(N:ℝ)^2 := div_le_self (sq_nonneg _) hℓR
  have hh := Real.rpow_le_rpow (by positivity : 0≤(N:ℝ)^2/(ℓ:ℝ)) hd (by norm_num : (0:ℝ)≤1/4)
  have he : ((N:ℝ)^2)^(1/4:ℝ)=(N:ℝ)^(1/2:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    norm_num
  exact hh.trans_eq he

theorem goldbach_sqrt_lt_truncation {N : ℕ} (hN : 2≤N) {α : ℝ} (hα1 : 1<α) (hα2 : α<2) :
    (N:ℝ)^(1/2:ℝ)<(N:ℝ)^(1/α) := by
  have hN1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  apply Real.rpow_lt_rpow_of_exponent_lt hN1
  exact (lt_div_iff₀ (by linarith : 0<α)).mpr (by linarith)

theorem prime_survives_smaller_sieve {r : ℕ} (hr : r.Prime) {z : ℝ} (hz : z≤r)
    {p : ℕ} (hp : p.Prime) (hpz : (p:ℝ)<z) : ¬p∣r := by
  intro hd
  have he := (Nat.prime_dvd_prime_iff_eq hp hr).mp hd
  rw [he] at hpz
  linarith

end PrimeSquares
