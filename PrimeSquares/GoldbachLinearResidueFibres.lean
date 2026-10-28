import PrimeSquares.GoldbachSquareMajorSW

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachGoodLinearCutoff (k q a : ℕ) (W : ℝ) : Finset ℕ :=
  (goldbachPrimeProgressionCutoff k a W).filter (fun n => n.Coprime (k.lcm q))

theorem goldbach_good_linear_maps_to (k q a : ℕ) [NeZero k] [NeZero q] (W : ℝ)
    (n : ℕ) (hn : n∈goldbachGoodLinearCutoff k q a W) :
    n%(k.lcm q)∈goldbachMajorResidues k q a := by
  have hpos : 0<k.lcm q := Nat.lcm_pos (NeZero.pos k) (NeZero.pos q)
  have hka : n%k=a%k := (mem_filter.mp (mem_filter.mp hn).1).2
  apply (mem_goldbachMajorResidues k q a (n%(k.lcm q))).mpr
  refine ⟨Nat.mod_lt n hpos,?_,?_⟩
  · rw [Nat.mod_mod_of_dvd n (Nat.dvd_lcm_left k q)]
    exact hka
  · change (n%(k.lcm q)).gcd (k.lcm q)=1
    exact (Nat.mod_modEq n (k.lcm q)).gcd_eq.trans (mem_filter.mp hn).2

theorem goldbach_good_linear_fibre (k q a b : ℕ) {W : ℝ} (hW : 0≤W)
    (hb : b∈goldbachMajorResidues k q a) :
    (goldbachGoodLinearCutoff k q a W).filter (fun n => n%(k.lcm q)=b)=
      goldbachPrimeProgressionCutoff (k.lcm q) b W := by
  classical
  obtain ⟨hbh,hbk,hbC⟩ := (mem_goldbachMajorResidues k q a b).mp hb
  have hbmod : b%(k.lcm q)=b := Nat.mod_eq_of_lt hbh
  ext n
  simp only [goldbachGoodLinearCutoff,mem_filter,mem_goldbachPrimeProgressionCutoff hW]
  constructor
  · rintro ⟨⟨⟨hp,ht,_⟩,_⟩,hnmod⟩
    exact ⟨hp,ht,hnmod.trans hbmod.symm⟩
  · rintro ⟨hp,ht,hnmod⟩
    have hnH : Nat.ModEq (k.lcm q) n b := hnmod
    have hnK : Nat.ModEq k n b := hnH.of_dvd (Nat.dvd_lcm_left k q)
    have hnC : n.Coprime (k.lcm q) := by
      change n.gcd (k.lcm q)=1
      exact hnH.gcd_eq.trans hbC
    exact ⟨⟨⟨hp,ht,hnK.trans hbk⟩,hnC⟩,hnmod.trans hbmod⟩

theorem goldbach_positive_linear_character (n : ℕ) (x : ℝ) :
    fourier (n:ℤ) (x:PrimeCircle)=realFourierPhase (x*n) := by
  rw [fourier_coe_apply,realFourierPhase]
  congr 1
  push_cast
  ring

theorem goldbach_linear_rational_phase (q : ℕ) [NeZero q] (A : ℤ) (ℓ n : ℕ) (γ : ℝ) :
    realFourierPhase (((A:ℝ)/q+γ)*((ℓ*n:ℕ):ℝ))=
      ZMod.stdAddChar ((A:ZMod q)*(ℓ:ZMod q)*(n:ZMod q))*
        realFourierPhase (((ℓ:ℝ)*γ)*(n:ℝ)) := by
  have he : ((A*((ℓ*n:ℕ):ℤ):ℤ):ZMod q)=(A:ZMod q)*(ℓ:ZMod q)*(n:ZMod q) := by
    push_cast
    ring
  rw [←he,ZMod.stdAddChar_coe,realFourierPhase,realFourierPhase,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem goldbach_good_linear_residue_grouping (k q a ℓ : ℕ) [NeZero k] [NeZero q]
    {W : ℝ} (hW : 0≤W) (A : ℤ) (γ : ℝ) :
    (∑ n∈goldbachGoodLinearCutoff k q a W,
      realFourierPhase (((A:ℝ)/q+γ)*((ℓ*n:ℕ):ℝ)))=
      ∑ b∈goldbachMajorResidues k q a,ZMod.stdAddChar ((A:ZMod q)*(ℓ:ZMod q)*(b:ZMod q))*
        (∑ n∈goldbachPrimeProgressionCutoff (k.lcm q) b W,
          realFourierPhase (((ℓ:ℝ)*γ)*(n:ℝ))) := by
  classical
  rw [←sum_fiberwise_of_maps_to (goldbach_good_linear_maps_to k q a W)]
  apply sum_congr rfl
  intro b hb
  rw [goldbach_good_linear_fibre k q a b hW hb,mul_sum]
  apply sum_congr rfl
  intro n hn
  have hnH : Nat.ModEq (k.lcm q) n b :=
    ((mem_goldbachPrimeProgressionCutoff hW).mp hn).2.2
  have hc : (n:ZMod q)=(b:ZMod q) := (ZMod.natCast_eq_natCast_iff n b q).mpr
    (hnH.of_dvd (Nat.dvd_lcm_right k q))
  rw [goldbach_linear_rational_phase,hc]

end PrimeSquares
