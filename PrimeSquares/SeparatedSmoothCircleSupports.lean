import PrimeSquares.CircleSmoothSupportWitness
import PrimeSquares.GeometricSmoothCircleFamily
namespace PrimeSquares
def PeriodicFrequencySeparated (Γ : Finset ℚ) (δ : ℝ) : Prop :=
  ∀ r ∈ Γ,∀ t ∈ Γ,r ≠ t → ∀ k : ℤ,δ ≤ |(r : ℝ)-(t : ℝ)-(k : ℝ)|
theorem separatedSmoothCircle_disjoint (Γ : Finset ℚ) {δ a : ℝ} (ha : 1 ≤ a)
    (hsep : PeriodicFrequencySeparated Γ δ) (hw : 2*(1/a)<δ)
    {r t : ℚ} (hr : r ∈ Γ) (ht : t ∈ Γ) (hne : r ≠ t) (θ : PrimeCircle) :
    circleSmoothCutoff a ha r θ=0 ∨ circleSmoothCutoff a ha t θ=0 := by
  by_contra hn
  push Not at hn
  let ξ := (AddCircle.equivIco 1 (-(1/2) : ℝ) θ : ℝ)
  have he : (ξ : PrimeCircle)=θ := AddCircle.coe_equivIco
  rw [←he] at hn
  obtain ⟨k,hk⟩ := circleSmoothCutoff_nonzero_lift ha r ξ hn.1
  obtain ⟨l,hl⟩ := circleSmoothCutoff_nonzero_lift ha t ξ hn.2
  have hp : 0 < a := by linarith
  have hkr := scaledSmoothCutoff_radius hp hk
  have hlr := scaledSmoothCutoff_radius hp hl
  have hb := hsep r hr t ht hne (k-l)
  have heq : (r : ℝ)-(t : ℝ)-((k-l : ℤ) : ℝ)=
      (ξ-(t : ℝ)+(l : ℝ))-(ξ-(r : ℝ)+(k : ℝ)) := by push_cast;ring
  rw [heq] at hb
  have hd := abs_sub (ξ-(t : ℝ)+(l : ℝ)) (ξ-(r : ℝ)+(k : ℝ))
  linarith
end PrimeSquares
