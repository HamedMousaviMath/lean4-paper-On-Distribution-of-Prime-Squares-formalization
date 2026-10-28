import PrimeSquares.PrimeStoppingLocalEndpoint
import PrimeSquares.SparseTriangleGeometry
import PrimeSquares.RestrictedGeometricInterpolation

/-! # The actual local bound at every point in the full open sparse triangle -/

open Finset
namespace PrimeSquares

theorem primeStopping_open_endpoint {c δ CS a b : ℝ}
    (D : PagePrimeSquareDistributionInputs c) (H419 : Proposition419Bounds D δ) (hδ : 0 < δ)
    (hCS : 1 ≤ CS) (HS : OrdinarySquareStoppingInput CS) (HM : IndependentPrimeMaximalInput)
    (htri : SourceSparseTriangle a b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (I : SparseIntegerInterval) (F G H : Finset ℤ) (τ : ℤ → ℕ),
      F ⊆ I.five.points → H ⊆ I.five.points → G ⊆ I.points → G ⊆ H →
      F.Nonempty → H.Nonempty →
      (∀ x ∈ G, ((2 : ℕ)^(τ x)*2)^2 ≤ I.length) →
      (∀ x ∈ G, sourceLocalMass ((2 : ℕ)^(τ x)*2) (finiteIndicatorLp F 1) x ≤
        320*((F.card : ℝ)/I.length)) →
      ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖/(5*(I.length : ℝ)) ≤
        K*((F.card : ℝ)/(5*(I.length : ℝ)))^a*((H.card : ℝ)/(5*(I.length : ℝ)))^b := by
  obtain ⟨q, t, α, hq0, hq, ht, ht1, hα, hα1, ha, hb⟩ := sourceSparseTriangle_interpolation htri
  let cstar := 4*Real.sqrt 3/9+1
  have hstar : 4*Real.sqrt 3/9 < cstar := by dsimp [cstar]; linarith
  have hcstar : 0 ≤ cstar := by dsimp [cstar]; positivity
  obtain ⟨KE, hKE, hEndpoint⟩ := primeStopping_local_endpoint D H419 hδ hCS HS hstar
  obtain ⟨CP, hCP, hMaximal⟩ := independentPrimeMaximal_restrict_tests HM hα hα1
  obtain ⟨D₀, hD₀, hAbsorb⟩ := density_rpow_mul_paperPhi_le
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) hcstar
    (by linarith : 0 < (2/3 : ℝ)-q) (2/3)
  let K := (KE*D₀)^t*CP^(1-t)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (mul_pos hKE hD₀) _)
    (Real.rpow_pos_of_pos hCP _)
  refine ⟨K, hK, ?_⟩
  intro I F G H τ hF hH hG hGH hFn hHn hscale hadm
  let L := 5*(I.length : ℝ)
  let f := (F.card : ℝ)/L
  let g := (H.card : ℝ)/L
  let R := ‖∑ x ∈ G, annularDyadicValue (τ x) F x‖/L
  let d := finiteSetDensity L F H
  have hI : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hF0 : (0 : ℝ) < F.card := by exact_mod_cast card_pos.mpr hFn
  have hH0 : (0 : ℝ) < H.card := by exact_mod_cast card_pos.mpr hHn
  have hf : 0 < f := div_pos hF0 hL
  have hg : 0 < g := div_pos hH0 hL
  have hd := finiteSetDensity_five_bounds I F H hF hH hFn hHn
  have hdfg : d=f*g := by dsimp [d, f, g, finiteSetDensity]; ring
  have hEp := hEndpoint I F G H τ hF hH hG hGH hFn hHn hscale hadm
  have hA : d^(2/3 : ℝ)*paperPhi cstar (1/2) d ≤ D₀*d^q := by
    simpa only [show (2/3 : ℝ)-(2/3-q)=q by ring] using hAbsorb d hd.1 hd.2
  have hE : R ≤ (KE*D₀)*f^q*g^q := by
    calc
      _ ≤ KE*d^(2/3 : ℝ)*paperPhi cstar (1/2) d := hEp
      _ ≤ KE*(D₀*d^q) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hA hKE.le
      _ = _ := by rw [hdfg, Real.mul_rpow hf.le hg.le]; ring
  have hPraw := hMaximal F G H τ hGH
  have hP : R ≤ CP*f^α*g^(1-α) := by
    calc
      _ ≤ (CP*(F.card : ℝ)^α*(H.card : ℝ)^(1-α))/L :=
        div_le_div_of_nonneg_right hPraw hL.le
      _ = CP*((F.card : ℝ)^α*(H.card : ℝ)^(1-α)/L) := by ring
      _ = CP*(((F.card : ℝ)/L)^α*((H.card : ℝ)/L)^(1-α)) :=
        congrArg (CP*·) (complementary_count_normalization hL (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      _ = _ := by dsimp [f, g]; ring
  exact restricted_geometric_interpolation (div_nonneg (norm_nonneg _) hL.le)
    (mul_pos hKE hD₀) hCP hf hg ht ht1 ha hb hE hP

end PrimeSquares
