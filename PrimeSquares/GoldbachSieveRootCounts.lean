import PrimeSquares.GeneralLocalEuler

set_option autoImplicit false
open Finset
namespace PrimeSquares

noncomputable def goldbachRho (p : ℕ) (n : ℤ) : ℕ :=
  if h : p=0 then 0 else
    letI : NeZero p := ⟨h⟩
    (univ.filter (fun u : (ZMod p)ˣ=>(u:ZMod p)^2=(n:ZMod p))).card

theorem goldbach_rho_eq (p : ℕ) [NeZero p] (n : ℤ) :
    goldbachRho p n=(univ.filter (fun u : (ZMod p)ˣ=>(u:ZMod p)^2=(n:ZMod p))).card := by
  simp only [goldbachRho,dite_eq_right (NeZero.ne p)]

theorem goldbach_rho_congr (p : ℕ) [NeZero p] {n m : ℤ} (h : (n:ZMod p)=(m:ZMod p)) :
    goldbachRho p n=goldbachRho p m := by rw [goldbach_rho_eq,goldbach_rho_eq,h]

theorem goldbach_cohen_rho (p : ℕ) [Fact p.Prime] (n : ℤ) :
    cohenCorrelation p n=(p:ℂ)*(goldbachRho p n:ℂ)-((p:ℂ)-1) := by
  classical
  have hp : p.Prime := Fact.out
  have hterm (u : (ZMod p)ˣ) : ramanujanSum p ((n:ZMod p)-(u:ZMod p)^2)=
      (p:ℂ)*(if (u:ZMod p)^2=(n:ZMod p) then 1 else 0)-1 := by
    rw [ramanujanSum_prime]
    by_cases h : (u:ZMod p)^2=(n:ZMod p)
    · simp only [h,sub_self,ite_true,mul_one]
    · have hh : (n:ZMod p)-(u:ZMod p)^2≠0 := sub_ne_zero.mpr (Ne.symm h)
      simp only [h,hh,ite_false,mul_zero,zero_sub]
  rw [cohenCorrelation_eq,quadraticRamanujanSum,sum_unit_filter_eq_sum_units]
  simp_rw [hterm]
  rw [sum_sub_distrib,←mul_sum]
  have hs : (∑ u : (ZMod p)ˣ,if (u:ZMod p)^2=(n:ZMod p) then (1:ℂ) else 0)=(goldbachRho p n:ℂ) := by
    rw [goldbach_rho_eq]
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hs]
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient,
    Nat.totient_prime hp,Nat.cast_sub hp.one_le,Nat.cast_one]

theorem goldbach_rho_legendre (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (n : ℤ) :
    goldbachRho p n=if legendreSym p n=1 then 2 else 0 := by
  have hp : p.Prime := Fact.out
  have hpn : (p:ℂ)≠0 := by exact_mod_cast hp.ne_zero
  have h := goldbach_cohen_rho p n
  rw [cohenCorrelation_eq,quadraticRamanujanSum_odd_prime p hp2] at h
  by_cases hχ : legendreSym p n=1
  · rw [ite_eq_left hχ] at h ⊢
    have hm : (p:ℂ)*((goldbachRho p n:ℂ)-2)=0 := by linear_combination -h
    have hh : (goldbachRho p n:ℂ)=2 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hpn)
    exact_mod_cast hh
  · rw [ite_eq_right hχ] at h ⊢
    have hm : (p:ℂ)*(goldbachRho p n:ℂ)=0 := by linear_combination -h
    have hh : (goldbachRho p n:ℂ)=0 := (mul_eq_zero.mp hm).resolve_left hpn
    exact_mod_cast hh

theorem goldbach_rho_le_two (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (n : ℤ) :
    goldbachRho p n≤2 := by
  rw [goldbach_rho_legendre p hp2]
  split_ifs <;> omega

theorem goldbach_rho_of_zero (p : ℕ) [Fact p.Prime] (hp2 : p≠2) {n : ℤ} (hn : (n:ZMod p)=0) :
    goldbachRho p n=0 := by
  rw [goldbach_rho_legendre p hp2, (legendreSym.eq_zero_iff p n).mpr hn]
  norm_num

theorem goldbach_rho_five_consecutive (n : ℤ) :
    goldbachRho 5 n=0 ∨goldbachRho 5 n=2 ∧ goldbachRho 5 (n-1)=0 := by
  have h : ∀ x : ZMod 5,
      (univ.filter (fun u : (ZMod 5)ˣ=>(u:ZMod 5)^2=x)).card=0 ∨
        (univ.filter (fun u : (ZMod 5)ˣ=>(u:ZMod 5)^2=x)).card=2 ∧
          (univ.filter (fun u : (ZMod 5)ˣ=>(u:ZMod 5)^2=x-1)).card=0 := by decide
  simpa only [goldbach_rho_eq,Int.cast_sub,Int.cast_one] using h (n:ZMod 5)

theorem goldbach_prime_restricted_count (p k : ℕ) [Fact p.Prime]
    (hpk : p∣k) (ℓ b n : ℤ) (hb : IsUnit (b:ZMod p)) :
    primeSolutionCount p k ℓ b n=goldbachRho p (n-ℓ*b) := by
  classical
  have h : (primeSolutionCount p k ℓ b n:ℂ)=(goldbachRho p (n-ℓ*b):ℂ) := by
    rw [primeSolutionCount_eq,unit_pair_count_cast]
    simp_rw [unit_reduction_eq_iff p k hpk b hb]
    have he (u v : (ZMod p)ˣ) :
        (if v=hb.unit ∧ (u:ZMod p)^2+(ℓ:ZMod p)*(v:ZMod p)=(n:ZMod p) then (1:ℂ) else 0)=
        if v=hb.unit then (if (u:ZMod p)^2=(n:ZMod p)-(ℓ:ZMod p)*(b:ZMod p) then 1 else 0) else 0 := by
      by_cases hv : v=hb.unit
      · subst v
        rw [hb.unit_spec]
        simp only [true_and,ite_true,eq_sub_iff_add_eq]
      · simp only [hv,false_and,ite_false]
    simp_rw [he]
    simp only [sum_ite_eq',mem_univ,ite_true]
    rw [goldbach_rho_eq]
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Int.cast_sub,Int.cast_mul]
  exact_mod_cast h

end PrimeSquares
