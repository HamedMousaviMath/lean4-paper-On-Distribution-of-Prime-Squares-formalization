import PrimeSquares.GoldbachFullSiftedReduction
import Mathlib.NumberTheory.SumTwoSquares

set_option autoImplicit false
namespace PrimeSquares

theorem goldbach_coprime_zmod_not_both_zero (q x y : ℕ) (hq : q.Prime)
    (hxy : x.Coprime y) : ¬((x:ZMod q)=0 ∧ (y:ZMod q)=0) := by
  rintro ⟨hx,hy⟩
  have hd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff x q).mp hx)
    ((ZMod.natCast_eq_zero_iff y q).mp hy)
  rw [hxy.gcd_eq_one] at hd
  exact hq.not_dvd_one hd

theorem goldbach_prime_norm_coprime (p a b : ℕ) (hp : p.Prime)
    (hab : a^2+b^2=p) : a.Coprime b := by
  apply Nat.coprime_of_dvd
  intro q hq hqa hqb
  have hdiv : q*q∣a^2+b^2 := dvd_add
    (by simpa only [pow_two] using mul_dvd_mul hqa hqa)
    (by simpa only [pow_two] using mul_dvd_mul hqb hqb)
  rw [hab] at hdiv
  exact (Nat.squarefree_iff_prime_squarefree.mp hp.squarefree q hq) hdiv

theorem goldbach_square_matrix_kernel {F : Type*} [CommRing F] (x y a b : F)
    (hc : x*a-y*b=0) (hd : x*b+y*a=0) :
    (a^2+b^2)*x=0 ∧ (a^2+b^2)*y=0 := by
  constructor
  · linear_combination a*hc+b*hd
  · linear_combination -b*hc+a*hd

theorem goldbach_conjugate_kernel_separation {F : Type*} [CommRing F] [NoZeroDivisors F]
    (x y a b : F) (h2 : (2:F)≠0) (hxy : ¬(x=0 ∧ y=0)) (hab : ¬(a=0 ∧ b=0)) :
    ¬((x*a-y*b=0 ∧ x*b+y*a=0) ∧ (x*a+y*b=0 ∧ -x*b+y*a=0)) := by
  rintro ⟨⟨hc,hd⟩,⟨hc',hd'⟩⟩
  have hax : (2*a)*x=0 := by linear_combination hc+hc'
  have hay : (2*a)*y=0 := by linear_combination hd+hd'
  have hbx : (2*b)*x=0 := by linear_combination hd-hd'
  have hby : (2*b)*y=0 := by linear_combination hc'-hc
  apply hxy
  by_cases ha : a=0
  · have hb : b≠0 := fun hb=>hab ⟨ha,hb⟩
    exact ⟨(mul_eq_zero.mp hbx).resolve_left (mul_ne_zero h2 hb),
      (mul_eq_zero.mp hby).resolve_left (mul_ne_zero h2 hb)⟩
  · exact ⟨(mul_eq_zero.mp hax).resolve_left (mul_ne_zero h2 ha),
      (mul_eq_zero.mp hay).resolve_left (mul_ne_zero h2 ha)⟩

theorem goldbach_primitive_pair_from_integer_norm (m : ℕ) (c d : ℤ)
    (hnorm : (m:ℤ)=c^2+d^2) (hcop : c.natAbs.Coprime d.natAbs) : PrimitiveTwoSquares m := by
  refine ⟨c.natAbs,d.natAbs,?_,hcop⟩
  have hh : (m:ℤ)=(c.natAbs:ℤ)^2+(d.natAbs:ℤ)^2 := by
    simpa only [Int.natCast_natAbs,sq_abs] using hnorm
  exact_mod_cast hh

/-- The determinant is the prime p, so an additional common prime divisor
of the two new coordinates can only be p itself. -/
theorem goldbach_primitive_prime_matrix (p x y : ℕ) (hp : p.Prime)
    (hxy : x.Coprime y) (a b : ℤ) (hab : a^2+b^2=(p:ℤ))
    (havoid : ¬((((x:ℤ)*a-(y:ℤ)*b):ZMod p)=0 ∧
      (((x:ℤ)*b+(y:ℤ)*a):ZMod p)=0)) :
    (((x:ℤ)*a-(y:ℤ)*b).natAbs).Coprime (((x:ℤ)*b+(y:ℤ)*a).natAbs) := by
  apply Nat.coprime_of_dvd
  intro q hq hqc hqd
  have : Fact q.Prime := ⟨hq⟩
  have hc : (((x:ℤ)*a-(y:ℤ)*b):ZMod q)=0 := by
    simpa only [Int.cast_sub,Int.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (Int.natCast_dvd.mpr hqc)
  have hd : (((x:ℤ)*b+(y:ℤ)*a):ZMod q)=0 := by
    simpa only [Int.cast_add,Int.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (Int.natCast_dvd.mpr hqd)
  by_cases he : q=p
  · subst q
    exact havoid ⟨hc,hd⟩
  · have hpq : (p:ZMod q)≠0 := by
      intro h
      have hh := (Nat.prime_dvd_prime_iff_eq hq hp).mp ((ZMod.natCast_eq_zero_iff p q).mp h)
      exact he hh
    have hnorm : (a:ZMod q)^2+(b:ZMod q)^2=(p:ZMod q) := by
      have hh := congrArg (fun z : ℤ=>(z:ZMod q)) hab
      simpa only [Int.cast_add,Int.cast_pow,Int.cast_natCast] using hh
    have hkernel := goldbach_square_matrix_kernel (x:ZMod q) (y:ZMod q) (a:ZMod q) (b:ZMod q)
      (by simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using hc)
      (by simpa only [Int.cast_add,Int.cast_mul,Int.cast_natCast] using hd)
    rw [hnorm] at hkernel
    exact goldbach_coprime_zmod_not_both_zero q x y hq hxy
      ⟨(mul_eq_zero.mp hkernel.1).resolve_left hpq,(mul_eq_zero.mp hkernel.2).resolve_left hpq⟩

theorem goldbach_primitive_multiply_one_mod_four_prime (m p : ℕ) (hm : PrimitiveTwoSquares m)
    (hp : p.Prime) (hp4 : p%4=1) : PrimitiveTwoSquares (m*p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,y,hxyNorm,hxy⟩ := hm
  obtain ⟨a,b,hab⟩ := Nat.Prime.sq_add_sq (by omega : p%4≠3)
  have habcop := goldbach_prime_norm_coprime p a b hp hab
  have h2 : (2:ZMod p)≠0 := by
    intro h
    have hpd : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa only [Nat.cast_ofNat] using h)
    have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hpd
    omega
  have hsep := goldbach_conjugate_kernel_separation (x:ZMod p) (y:ZMod p) (a:ZMod p) (b:ZMod p)
    h2 (goldbach_coprime_zmod_not_both_zero p x y hp hxy)
      (goldbach_coprime_zmod_not_both_zero p a b hp habcop)
  have hnormOld : (m:ℤ)=(x:ℤ)^2+(y:ℤ)^2 := by exact_mod_cast hxyNorm
  have hnormPrime : (a:ℤ)^2+(b:ℤ)^2=(p:ℤ) := by exact_mod_cast hab
  have hbuild (b' : ℤ) (hb' : (a:ℤ)^2+b'^2=(p:ℤ))
      (havoid : ¬((((x:ℤ)*(a:ℤ)-(y:ℤ)*b'):ZMod p)=0 ∧
        (((x:ℤ)*b'+(y:ℤ)*(a:ℤ)):ZMod p)=0)) : PrimitiveTwoSquares (m*p) := by
    apply goldbach_primitive_pair_from_integer_norm (m*p)
      ((x:ℤ)*(a:ℤ)-(y:ℤ)*b') ((x:ℤ)*b'+(y:ℤ)*(a:ℤ))
    · push_cast
      rw [hnormOld,←hb']
      ring
    · exact goldbach_primitive_prime_matrix p x y hp hxy (a:ℤ) b' hb' havoid
  by_cases hplus : (x:ZMod p)*(a:ZMod p)-(y:ZMod p)*(b:ZMod p)=0 ∧
      (x:ZMod p)*(b:ZMod p)+(y:ZMod p)*(a:ZMod p)=0
  · apply hbuild (-(b:ℤ)) (by simpa only [neg_sq] using hnormPrime)
    intro hminus
    apply hsep ⟨hplus,?_⟩
    simpa only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast,Int.cast_neg,
      mul_neg,sub_neg_eq_add,neg_mul] using hminus
  · apply hbuild (b:ℤ) hnormPrime
    simpa only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hplus

end PrimeSquares
