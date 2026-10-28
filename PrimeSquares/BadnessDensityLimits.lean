import PrimeSquares.BadnessBlockBudgets
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
open Filter
open scoped Topology
namespace PrimeSquares

theorem badnessBlockDensity_tendsto_zero :
    Tendsto (fun j : ℕ => unitSquareDensity (badnessBlockModulus j)) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsucc : Tendsto (fun j : ℕ => (1/2:ℝ)^(j+1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using hhalf.mul_const (1/2:ℝ)
  exact squeeze_zero (fun j => (unitSquareDensity_pos (badnessBlockModulus j)).le)
    (fun j => (badnessBlockDensity_bounds j).2) hsucc

theorem badnessBlockSpacing_tendsto_atTop :
    Tendsto (fun j : ℕ => unitSquareSpacing (badnessBlockModulus j)) atTop atTop := by
  have hlinear (j : ℕ) : (j:ℝ) ≤ unitSquareSpacing (badnessBlockModulus j) := by
    have hnat : j ≤ 2^(j+1) := by
      have h : j+1 < 2^(j+1) := Nat.lt_two_pow_self
      omega
    have hreal : (j:ℝ) ≤ (2:ℝ)^(j+1) := by exact_mod_cast hnat
    exact hreal.trans (badnessBlockSpacing_bounds j).1
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N,hN⟩ := exists_nat_ge b
  filter_upwards [eventually_ge_atTop N] with j hj
  exact hN.trans ((by exact_mod_cast hj : (N:ℝ) ≤ j).trans (hlinear j))

theorem badnessAuxU_density_lower (j : ℕ) : (1/3:ℝ) ≤ unitSquareDensity (badnessAuxU j) := by
  rw [unitSquareDensity_prime]
  have hne : badnessAuxU j ≠ 2 := by
    unfold badnessAuxU
    exact ne_of_gt (badnessAuxPrime_gt_two _)
  exact (primeResidueDensity_bounds (badnessAuxU j) hne).1

theorem liminf_lower_from_vanishing_error {f e : ℕ → ℝ} {L U : ℝ}
    (h0 : ∀ j, 0 ≤ f j) (hU : ∀ j, f j ≤ U)
    (he : Tendsto e atTop (𝓝 0)) (hlower : ∀ j, L-e j ≤ f j) :
    L ≤ liminf f atTop := by
  have hbounded : IsBoundedUnder (fun x y : ℝ => y ≤ x) atTop f :=
    isBoundedUnder_of ⟨0,h0⟩
  have hcobounded : IsCoboundedUnder (fun x y : ℝ => y ≤ x) atTop f :=
    IsCoboundedUnder.of_frequently_le (Eventually.of_forall hU).frequently
  have ht : Tendsto (fun j => L-e j) atTop (𝓝 L) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub he)
  apply (le_liminf_iff hcobounded hbounded).mpr
  intro a ha
  have hnear : ∀ᶠ j in atTop, a < L-e j := ht.eventually (Ioi_mem_nhds ha)
  exact hnear.mono (fun j hj => hj.trans_le (hlower j))

theorem liminf_le_uniform_upper {f : ℕ → ℝ} {U : ℝ}
    (h0 : ∀ j, 0 ≤ f j) (hU : ∀ j, f j ≤ U) : liminf f atTop ≤ U := by
  have hbounded : IsBoundedUnder (fun x y : ℝ => y ≤ x) atTop f :=
    isBoundedUnder_of ⟨0,h0⟩
  apply liminf_le_of_le hbounded
  intro b hb
  obtain ⟨j,hj⟩ := hb.exists
  exact hj.trans (hU j)

end PrimeSquares
