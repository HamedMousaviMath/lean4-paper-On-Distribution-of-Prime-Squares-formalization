import PrimeSquares.CyclicCharacters

/-!
# Exact small 2-adic factors of the quadratic Cohen identity

Source: Draft5, Lemma l:cohenquadratic, equation e:Ta.
Complete additive-character orthogonality minus the even residues evaluates
c_4 and c_8 from the genuine exponential definition. Kernel-checked finite
unit sets supply the residue decomposition. The final theorems give every
signed and zero case of C_4 and C_8.
-/

open Finset

namespace PrimeSquares

theorem sum_unit_four (f : ZMod 4 → ℂ) :
    (∑ r : ZMod 4, if IsUnit r then f r else 0) =
      (∑ r : ZMod 4, f r) - (f 0 + f 2) := by
  classical
  have hu : (univ.filter fun r : ZMod 4 => IsUnit r) = {1, 3} := by decide
  have hall : (univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [← sum_filter, hu, hall]
  simp (disch := decide) only [sum_insert, sum_singleton]
  ring

theorem sum_unit_eight (f : ZMod 8 → ℂ) :
    (∑ r : ZMod 8, if IsUnit r then f r else 0) =
      (∑ r : ZMod 8, f r) - (f 0 + f 2 + f 4 + f 6) := by
  classical
  have hu : (univ.filter fun r : ZMod 8 => IsUnit r) = {1, 3, 5, 7} := by decide
  have hall : (univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
  rw [← sum_filter, hu, hall]
  simp (disch := decide) only [sum_insert, sum_singleton]
  ring

theorem ramanujanSum_four (m : ZMod 4) :
    ramanujanSum 4 m = if m = 0 then 2 else if m = 2 then -2 else 0 := by
  classical
  let ρ : ZMod 4 →+* ZMod 2 := ZMod.castHom (Nat.dvd_mul_right 2 2) (ZMod 2)
  have hscale (j : ℕ) : ZMod.stdAddChar (m * (2 * (j : ZMod 4))) =
      ZMod.stdAddChar (ρ m * (j : ZMod 2)) := by
    calc
      _ = ZMod.stdAddChar (2 * (m * (j : ZMod 4))) := by congr 1; ring
      _ = _ := by
        simpa only [Nat.cast_ofNat, map_mul, map_natCast] using
          stdAddChar_scale 2 2 (m * (j : ZMod 4))
  have heven : ZMod.stdAddChar (m * 0) + ZMod.stdAddChar (m * 2) =
      if ρ m = 0 then (2 : ℂ) else 0 := by
    calc
      _ = ∑ r : ZMod 2, ZMod.stdAddChar (ρ m * r) := by
        rw [show (univ : Finset (ZMod 2)) = {0, 1} by decide]
        simp (disch := decide) only [sum_insert, sum_singleton]
        have hs : ZMod.stdAddChar (m * 2) = ZMod.stdAddChar (ρ m) := by
          simpa only [Nat.cast_one, mul_one] using hscale 1
        simp only [mul_zero, mul_one, AddChar.map_zero_eq_one, hs]
      _ = _ := sum_stdAddChar_mul 2 (ρ m)
  rw [ramanujanSum, sum_unit_four, sum_stdAddChar_mul, heven]
  have hρ : ρ m = 0 ↔ m = 0 ∨ m = 2 := by
    exact (by decide : ∀ x : ZMod 4,
      ZMod.castHom (Nat.dvd_mul_right 2 2) (ZMod 2) x = 0 ↔ x = 0 ∨ x = 2) m
  simp only [hρ]
  by_cases h0 : m = 0
  · simp only [h0, true_or, ↓reduceIte]
    norm_num
  · simp only [h0, false_or, ↓reduceIte]
    split_ifs <;> norm_num

theorem ramanujanSum_eight (m : ZMod 8) :
    ramanujanSum 8 m = if m = 0 then 4 else if m = 4 then -4 else 0 := by
  classical
  let ρ : ZMod 8 →+* ZMod 4 := ZMod.castHom (Nat.dvd_mul_right 4 2) (ZMod 4)
  have hscale (j : ℕ) : ZMod.stdAddChar (m * (2 * (j : ZMod 8))) =
      ZMod.stdAddChar (ρ m * (j : ZMod 4)) := by
    calc
      _ = ZMod.stdAddChar (2 * (m * (j : ZMod 8))) := by congr 1; ring
      _ = _ := by
        simpa only [Nat.cast_ofNat, map_mul, map_natCast] using
          stdAddChar_scale 4 2 (m * (j : ZMod 8))
  have heven : ZMod.stdAddChar (m * 0) + ZMod.stdAddChar (m * 2) +
      ZMod.stdAddChar (m * 4) + ZMod.stdAddChar (m * 6) =
      if ρ m = 0 then (4 : ℂ) else 0 := by
    calc
      _ = ∑ r : ZMod 4, ZMod.stdAddChar (ρ m * r) := by
        rw [show (univ : Finset (ZMod 4)) = {0, 1, 2, 3} by decide]
        simp (disch := decide) only [sum_insert, sum_singleton]
        have hs1 : ZMod.stdAddChar (m * 2) = ZMod.stdAddChar (ρ m) := by
          simpa only [Nat.cast_one, mul_one] using hscale 1
        have hs2 : ZMod.stdAddChar (m * 4) = ZMod.stdAddChar (ρ m * 2) := by
          convert hscale 2 using 1; norm_num
        have hs3 : ZMod.stdAddChar (m * 6) = ZMod.stdAddChar (ρ m * 3) := by
          convert hscale 3 using 1; norm_num
        simp only [mul_zero, mul_one, AddChar.map_zero_eq_one, hs1, hs2, hs3]
        ring
      _ = _ := sum_stdAddChar_mul 4 (ρ m)
  rw [ramanujanSum, sum_unit_eight, sum_stdAddChar_mul, heven]
  have hρ : ρ m = 0 ↔ m = 0 ∨ m = 4 := by
    exact (by decide : ∀ x : ZMod 8,
      ZMod.castHom (Nat.dvd_mul_right 4 2) (ZMod 4) x = 0 ↔ x = 0 ∨ x = 4) m
  simp only [hρ]
  by_cases h0 : m = 0
  · simp only [h0, true_or, ↓reduceIte]
    norm_num
  · simp only [h0, false_or, ↓reduceIte]
    split_ifs <;> norm_num

theorem quadraticRamanujanSum_four_explicit (n : ZMod 4) :
    quadraticRamanujanSum 4 n = if n = 1 then 4 else if n = 3 then -4 else 0 := by
  rw [quadraticRamanujanSum_four, ramanujanSum_four]
  have h3 : n - 1 = 2 ↔ n = 3 := by
    exact (by decide : ∀ x : ZMod 4, x - 1 = 2 ↔ x = 3) n
  simp only [sub_eq_zero, h3]
  split_ifs <;> norm_num

theorem quadraticRamanujanSum_eight_explicit (n : ZMod 8) :
    quadraticRamanujanSum 8 n = if n = 1 then 16 else if n = 5 then -16 else 0 := by
  rw [quadraticRamanujanSum_eight, ramanujanSum_eight]
  have h5 : n - 1 = 4 ↔ n = 5 := by
    exact (by decide : ∀ x : ZMod 8, x - 1 = 4 ↔ x = 5) n
  simp only [sub_eq_zero, h5]
  split_ifs <;> norm_num

end PrimeSquares
