import PrimeSquares.ElementaryPrimeProduct

open Finset
namespace PrimeSquares

theorem reciprocal_multiples_bound (m D : ℕ) (hm : 0 < m) :
    (∑ n ∈ (Icc 1 D).filter (fun n => m ∣ n),(n : ℝ)⁻¹) ≤ (m : ℝ)⁻¹*(harmonic D : ℝ) := by
  classical
  rw [harmonic_eq_sum_Icc,Rat.cast_sum]
  simp only [Rat.cast_inv,Rat.cast_natCast,mul_sum]
  apply sum_le_sum_of_injOn (fun n => n/m)
  · intro n hn n' hn' he
    dsimp only at he
    have hd := (mem_filter.mp hn).2
    have hd' := (mem_filter.mp hn').2
    calc
      n = m*(n/m) := (Nat.mul_div_cancel' hd).symm
      _ = m*(n'/m) := by rw [he]
      _ = n' := Nat.mul_div_cancel' hd'
  · intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    obtain ⟨hn,hd⟩ := mem_filter.mp hn
    obtain ⟨hnp,hnD⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hd) hm,(Nat.div_le_self n m).trans hnD⟩
  · intro n hn
    have hd := (mem_filter.mp hn).2
    have he : (n : ℝ)=(m : ℝ)*(n/m : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hd).symm
    rw [he,mul_inv_rev,mul_comm]
  · intro n _ _
    positivity

end PrimeSquares
