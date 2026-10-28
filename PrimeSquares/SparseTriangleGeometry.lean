import PrimeSquares.OrliczGrowth

/-!
# Exact geometry of the open sparse triangle

The three strict inequalities are equivalent to positive barycentric
coordinates at (2/3,2/3), (1,0), (0,1). Every such point is interpolated
using a diagonal exponent strictly below 2/3 and a point strictly inside
the complementary-exponent segment.
-/

namespace PrimeSquares

def SourceSparseTriangle (a b : ℝ) : Prop := 1 < a+b ∧ 2*a+b < 2 ∧ a+2*b < 2

theorem sourceSparseTriangle_iff_barycentric (a b : ℝ) : SourceSparseTriangle a b ↔
    ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u+v+w=1 ∧
      a=(2/3 : ℝ)*u+v ∧ b=(2/3 : ℝ)*u+w := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨3*(a+b-1), 2-a-2*b, 2-2*a-b, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩ <;> ring
  · rintro ⟨u, v, w, hu, hv, hw, he, ha, hb⟩
    dsimp [SourceSparseTriangle]
    constructor
    · linarith
    · constructor <;> linarith

theorem sourceSparseTriangle_interpolation {a b : ℝ} (h : SourceSparseTriangle a b) :
    ∃ q t α : ℝ, 1/2 < q ∧ q < 2/3 ∧ 0 < t ∧ t < 1 ∧ 0 < α ∧ α < 1 ∧
      a=t*q+(1-t)*α ∧ b=t*q+(1-t)*(1-α) := by
  obtain ⟨h1, h2, h3⟩ := h
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hdA : 0 < 1+a-b := by linarith
  have hdB : 0 < 1-a+b := by linarith
  have hrA : a/(1+a-b) < (2/3 : ℝ) := (div_lt_iff₀ hdA).mpr (by nlinarith)
  have hrB : b/(1-a+b) < (2/3 : ℝ) := (div_lt_iff₀ hdB).mpr (by nlinarith)
  let m₁ := max (1/2 : ℝ) ((a+b)/2)
  let m₂ := max (a/(1+a-b)) (b/(1-a+b))
  have hm : max m₁ m₂ < (2/3 : ℝ) := by
    exact max_lt_iff.mpr ⟨max_lt_iff.mpr ⟨by norm_num, by linarith⟩,
      max_lt_iff.mpr ⟨hrA, hrB⟩⟩
  obtain ⟨q, hmq, hq⟩ := exists_between hm
  have hqhalf : (1/2 : ℝ) < q :=
    ((le_max_left (1/2 : ℝ) ((a+b)/2)).trans (le_max_left m₁ m₂)).trans_lt hmq
  have hqsum : (a+b)/2 < q :=
    ((le_max_right (1/2 : ℝ) ((a+b)/2)).trans (le_max_left m₁ m₂)).trans_lt hmq
  have hqA : a < q*(1+a-b) := (div_lt_iff₀ hdA).mp
    (((le_max_left (a/(1+a-b)) (b/(1-a+b))).trans (le_max_right m₁ m₂)).trans_lt hmq)
  have hqB : b < q*(1-a+b) := (div_lt_iff₀ hdB).mp
    (((le_max_right (a/(1+a-b)) (b/(1-a+b))).trans (le_max_right m₁ m₂)).trans_lt hmq)
  have hd : 0 < 2*q-1 := by linarith
  let t := (a+b-1)/(2*q-1)
  have ht : 0 < t := div_pos (by linarith) hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  have hteq : t*(2*q-1)=a+b-1 := by dsimp [t]; field_simp
  have hqeq := congrArg (fun z : ℝ => q*z) hteq
  have hnumA : 0 < a-q*t := by
    have hs : 0 < (a-q*t)*(2*q-1) := by nlinarith only [hqA, hqeq]
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd.le
    linarith
  have hnumB : 0 < b-q*t := by
    have hs : 0 < (b-q*t)*(2*q-1) := by nlinarith only [hqB, hqeq]
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd.le
    linarith
  let α := (a-q*t)/(1-t)
  have hα : 0 < α := div_pos hnumA (by linarith)
  have hα1 : α < 1 := (div_lt_one (by linarith : 0 < 1-t)).mpr (by nlinarith only [hnumB, hteq])
  have hαeq : (1-t)*α=a-q*t := by
    dsimp [α]
    field_simp [show (1-t) ≠ 0 by linarith]
  refine ⟨q, t, α, hqhalf, hq, ht, ht1, hα, hα1, ?_, ?_⟩ <;> nlinarith only [hαeq, hteq]

end PrimeSquares
