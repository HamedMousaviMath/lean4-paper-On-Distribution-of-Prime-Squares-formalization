import PrimeSquares.QuadraticPairMoment

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem finite_one_exception_sum {I : Type*} [DecidableEq I] (S : Finset I) (a : I)
    (A : I → ℝ) (B M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ v ∈ S, A v ≤ B+(if v=a then M else 0)) :
    ∑ v ∈ S, A v ≤ (S.card:ℝ)*B+M := by
  classical
  calc
    _ ≤ ∑ v ∈ S, (B+(if v=a then M else 0)) := Finset.sum_le_sum hA
    _ = (S.card:ℝ)*B+(if a∈S then M else 0) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := by split_ifs <;> linarith

theorem large_density_exception {p m : ℝ} (hp : 1 ≤ p) (hm : p/3 ≤ m) :
    m ≤ (9/Real.sqrt p)*(m^3/p) := by
  have hp0 : 0 < p := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hsqrt : Real.sqrt p ≤ p := (Real.sqrt_le_iff).mpr ⟨hp0.le, by nlinarith⟩
  have hmsq : p^2 ≤ 9*m^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 3*m-p) (by linarith : 0 ≤ 3*m+p)]
  have h1 : m*Real.sqrt p*p ≤ m*p*p :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hm0) hp0.le
  have h2 := mul_le_mul_of_nonneg_left hmsq hm0
  calc
    m ≤ 9*m^3/(Real.sqrt p*p) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by ring

theorem quadratic_triple_moment (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (t : ZMod p) :
    (additiveTripleCount (unitSquareResidues p) t : ℝ) ≤
      (1+63/Real.sqrt p)*(((unitSquareResidues p).card : ℝ)^3/p) := by
  classical
  let S := unitSquareResidues p
  let m : ℝ := S.card
  let B : ℝ := (1+54/Real.sqrt p)*(m^2/p)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have heach (v : ZMod p) (hvS : v ∈ S) :
      (additivePairCount S (-v-t) : ℝ) ≤ B+(if v=-t then m else 0) := by
    by_cases hv : v=-t
    · rw [ite_eq_left hv]
      have hcard : (additivePairCount S (-v-t) : ℝ) ≤ m := by
        change (additivePairCount S (-v-t) : ℝ) ≤ (S.card:ℝ)
        exact_mod_cast additivePairCount_le_card S (-v-t)
      linarith
    · rw [ite_eq_right hv, add_zero]
      have hshift : -v-t ≠ 0 := by
        intro he
        exact hv (neg_eq_iff_eq_neg.mp (sub_eq_zero.mp he))
      exact quadratic_pair_moment HW p hp (-v-t) hshift
  have htotal : (additiveTripleCount S t : ℝ) ≤ m*B+m := by
    rw [additiveTripleCount_sum_pairs, Nat.cast_sum]
    exact finite_one_exception_sum S (-t) (fun v => (additivePairCount S (-v-t) : ℝ)) B m hm0 heach
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hmlower : (p:ℝ)/3 ≤ m := by
    have hb := (unitSquareResidues_prime_density p hp).1
    have hc := (le_div_iff₀ hp0).mp hb
    dsimp [m,S]
    linarith
  have hexc := large_density_exception hp1 hmlower
  calc
    _ ≤ m*B+m := htotal
    _ ≤ m*B+(9/Real.sqrt p)*(m^3/p) := add_le_add le_rfl hexc
    _ = _ := by dsimp [B,m,S]; ring

theorem quadratic_pair_moment_common (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (t : ZMod p) (ht : t ≠ 0) :
    (additivePairCount (unitSquareResidues p) t : ℝ) ≤
      (1+64/Real.sqrt p)*(((unitSquareResidues p).card : ℝ)^2/p) := by
  calc
    _ ≤ (1+54/Real.sqrt p)*(((unitSquareResidues p).card : ℝ)^2/p) :=
      quadratic_pair_moment HW p hp t ht
    _ ≤ _ := by gcongr; norm_num

theorem quadratic_triple_moment_common (HW : RawSplitQuadraticWeilInput)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (t : ZMod p) :
    (additiveTripleCount (unitSquareResidues p) t : ℝ) ≤
      (1+64/Real.sqrt p)*(((unitSquareResidues p).card : ℝ)^3/p) := by
  calc
    _ ≤ (1+63/Real.sqrt p)*(((unitSquareResidues p).card : ℝ)^3/p) :=
      quadratic_triple_moment HW p hp t
    _ ≤ _ := by gcongr; norm_num

end PrimeSquares
