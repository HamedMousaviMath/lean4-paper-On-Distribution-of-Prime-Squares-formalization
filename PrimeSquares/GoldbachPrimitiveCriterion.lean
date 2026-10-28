import PrimeSquares.GoldbachPrimitiveProducts

set_option autoImplicit false
namespace PrimeSquares

theorem goldbach_primitive_one_mod_four_support (n : ℕ) (hn : 0<n)
    (hs : ∀ p : ℕ,p.Prime→p∣n→p%4=1) : PrimitiveTwoSquares n := by
  induction n using induction_on_primes with
  | zero => omega
  | one => exact ⟨1,0,by norm_num,by norm_num⟩
  | prime_mul p n hp ih =>
    have hn0 : 0<n := by
      have hnne : n≠0 := by
        intro he
        rw [he,Nat.mul_zero] at hn
        omega
      exact Nat.pos_of_ne_zero hnne
    have hs' : ∀ q : ℕ,q.Prime→q∣n→q%4=1 := fun q hq hqn=>hs q hq (hqn.mul_left p)
    have hpp : p%4=1 := hs p hp (dvd_mul_right p n)
    simpa only [Nat.mul_comm] using goldbach_primitive_multiply_one_mod_four_prime n p (ih hn0 hs') hp hpp

theorem goldbach_primitive_double_of_odd (n : ℕ) (hn : n%2=1)
    (hprim : PrimitiveTwoSquares n) : PrimitiveTwoSquares (2*n) := by
  obtain ⟨x,y,hNorm,hCop⟩ := hprim
  have hnval : (n:ZMod 2)=1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff n 1 2).mpr (by
      change n%2=1%2
      simpa using hn)
  have hNormMod : (n:ZMod 2)=(x:ZMod 2)^2+(y:ZMod 2)^2 := by
    have hh := congrArg (fun z : ℕ=>(z:ZMod 2)) hNorm
    simpa only [Nat.cast_add,Nat.cast_pow] using hh
  have havoid : ¬((((x:ℤ)*1-(y:ℤ)*1):ZMod 2)=0 ∧
      (((x:ℤ)*1+(y:ℤ)*1):ZMod 2)=0) := by
    rintro ⟨_,hd⟩
    have hd' : (x:ZMod 2)+(y:ZMod 2)=0 := by simpa using hd
    have hid : ∀ X Y : ZMod 2,X^2+Y^2=(X+Y)^2 := by decide
    have hh : (n:ZMod 2)=0 := by rw [hNormMod,hid,hd'];norm_num
    exact one_ne_zero (hnval.symm.trans hh)
  have hnew := goldbach_primitive_prime_matrix 2 x y (by decide) hCop 1 1 (by norm_num) havoid
  apply goldbach_primitive_pair_from_integer_norm (2*n) ((x:ℤ)-(y:ℤ)) ((x:ℤ)+(y:ℤ))
  · have hNormInt : (n:ℤ)=(x:ℤ)^2+(y:ℤ)^2 := by exact_mod_cast hNorm
    push_cast
    rw [hNormInt]
    ring
  · simpa only [mul_one] using hnew

theorem goldbach_primitive_two_squares_criterion : PrimitiveTwoSquaresCriterion := by
  intro n hn4
  have hn : 0<n := by omega
  constructor
  · rintro ⟨x,y,hNorm,hCop⟩ p hp hp4 hpd
    have hsq := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime hNorm hCop
    exact (Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
      (hp.mem_primeFactors hpd hn.ne') hsq) hp4
  · intro hno
    have hfac : n=2*(n/2) := by omega
    have hodd : (n/2)%2=1 := by omega
    have hpos : 0<n/2 := by omega
    have hs : ∀ p : ℕ,p.Prime→p∣n/2→p%4=1 := by
      intro p hp hpd
      have hpn : p∣n := by rw [hfac];exact hpd.mul_left 2
      have hp3 : p%4≠3 := fun h=>hno p hp h hpn
      rcases hp.eq_two_or_odd with he|he
      · subst p
        have hh := Nat.mod_eq_zero_of_dvd hpd
        omega
      · omega
    rw [hfac]
    exact goldbach_primitive_double_of_odd (n/2) hodd (goldbach_primitive_one_mod_four_support (n/2) hpos hs)

end PrimeSquares
