import PrimeSquares.GoldbachUpperFactorGeometry

set_option autoImplicit false
open Finset
namespace PrimeSquares

/-- A full set inclusion into actual upper sifted sets for the corrected closed L. -/
theorem goldbach_upper_sifted_inclusion {N n : ℕ} (hN : 2≤N) (hn : 12<n)
    (hsize : n<N^2) (hresn : n%24=12) {α : ℝ} (hα1 : 1<α) (hα2 : α<2) :
    goldbachTruncatedBad n ((N:ℝ)^(1/α))⊆
      (goldbachClosedLn n N ((N:ℝ)^(1/α))).biUnion (goldbachUpperSifted n N)∪
        goldbachDivisorExceptions n := by
  classical
  let z := (N:ℝ)^(1/α)
  intro r hr
  by_cases hE : r∈goldbachDivisorExceptions n
  · exact mem_union_right _ hE
  · obtain ⟨hra,u,p₁,p₂,hu,hfac,hp₂z,horder,hp₁,hp₂,hugood⟩ := mem_filter.mp hr
    obtain ⟨hrr,hrres⟩ := mem_filter.mp hra
    obtain ⟨hrp,q,hq,heq⟩ := mem_goldbachRepresentations.mp hrr
    have hr2 := hrp.two_le
    let ℓ := 2*u*p₂
    have hℓpos : 0<ℓ := Nat.mul_pos (Nat.mul_pos (by norm_num) hu) hp₂.1.pos
    have hℓfac : r-1=ℓ*p₁ := by dsimp [ℓ]; nlinarith only [hfac]
    have hℓdiv : ℓ∣r-1 := ⟨p₁,hℓfac⟩
    have hc : ℓ.Coprime (n-1) := goldbach_factor_coprime_of_not_exception (by omega) hrp.one_le hq heq hℓdiv hE
    have hz : 0<z := Real.rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _
    have hb : 2*u*p₁*p₂<N^2 := by omega
    obtain ⟨huSize,hp₂Size⟩ := goldbach_upper_factor_geometry hu hp₂.1 horder hz hp₂z hb
    have hℓL : GoldbachClosedL N z ℓ :=
      ⟨u,p₂,hu,rfl,huSize,hp₂.1,hp₂.2.1,hp₂z,hp₂Size,hugood⟩
    have hLn : ℓ∈goldbachClosedLn n N z := mem_filter.mpr ⟨mem_goldbachClosedLSet.mpr hℓL,hc⟩
    have hq3 := goldbach_square_prime_large hn hresn hrp hq heq
    have hrN : r<N^2 := by omega
    have hM : r∈goldbachUpperM n N ℓ :=
      mem_filter.mpr ⟨mem_range.mpr hrN,p₁,q,hp₁.1,hp₁.2.1,hq,hq3,by omega,heq⟩
    have hlevel : goldbachUpperSieveLevel N ℓ≤r := by
      have h₁ := goldbach_upper_level_le_sqrt (N:=N) (by omega : 1≤ℓ)
      have h₂ := goldbach_sqrt_lt_truncation hN hα1 hα2
      have horderR : (p₂:ℝ)≤p₁ := by exact_mod_cast horder
      have hp₁div : p₁∣r-1 := ⟨ℓ,by rw [hℓfac]; ring⟩
      have hp₁r : (p₁:ℝ)≤r := by exact_mod_cast
        (Nat.le_of_dvd (by have hh := hrp.two_le; omega : 0<r-1) hp₁div).trans (Nat.sub_le r 1)
      exact h₁.trans ((h₂.le.trans (hp₂z.trans horderR)).trans hp₁r)
    have hS : r∈goldbachUpperSifted n N ℓ := mem_filter.mpr ⟨hM,
      fun p hp hpz => prime_survives_smaller_sieve hrp hlevel hp.1 hpz⟩
    exact mem_union_left _ (mem_biUnion.mpr ⟨ℓ,hLn,hS⟩)

end PrimeSquares
