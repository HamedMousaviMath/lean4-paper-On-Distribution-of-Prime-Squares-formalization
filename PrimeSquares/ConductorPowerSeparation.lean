import PrimeSquares.SubunitConductorCollars
namespace PrimeSquares
theorem conductor_power_separation {q₀ q η ε : ℝ} (hq₀ : 0 < q₀) (hle : q₀ ≤ q) (hε : 0 ≤ ε) :
    q^(-(η+ε)) ≤ q₀^(-ε)*q^(-η) := by
  have hq := hq₀.trans_le hle
  calc
    q^(-(η+ε))=q^(-ε)*q^(-η) := by rw [←Real.rpow_add hq];congr 1;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hq₀ hle (neg_nonpos.mpr hε)) (Real.rpow_pos_of_pos hq _).le
theorem conductor_divides_den_lower {q₀ : ℕ} (r : ℚ) (hdiv : q₀ ∣ r.den) : (q₀ : ℝ) ≤ r.den := by
  exact_mod_cast Nat.le_of_dvd r.den_pos hdiv
end PrimeSquares
