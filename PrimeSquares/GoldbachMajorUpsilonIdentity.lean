import PrimeSquares.GoldbachMajorCompatibleResidues

set_option autoImplicit false
open Finset
namespace PrimeSquares

theorem goldbach_reduction_val {h m : ℕ} [NeZero h] (hd : m∣h) (b : ZMod h) :
    (b.val:ZMod m)=ZMod.castHom hd (ZMod m) b := by
  have hh := congrArg (ZMod.castHom hd (ZMod m)) (ZMod.natCast_zmod_val b)
  simpa only [map_natCast] using hh

noncomputable def goldbachMajorQResidues (k q a : ℕ) [NeZero q] : Finset (ZMod q) :=
  univ.filter (fun r => IsUnit r ∧ Nat.ModEq (k.gcd q) a r.val)

theorem goldbach_major_residue_image (k q a : ℕ) [NeZero k] [NeZero q]
    (ha : a.Coprime k) :
    (goldbachMajorResidues k q a).image (fun b : ℕ => (b:ZMod q))=goldbachMajorQResidues k q a := by
  classical
  ext r
  simp only [mem_image,goldbachMajorQResidues,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨hbq,hcomp⟩ := goldbach_major_residue_compatible k q a b hb
    refine ⟨(ZMod.isUnit_iff_coprime b q).mpr hbq,?_⟩
    rw [ZMod.val_natCast]
    exact hcomp.trans ((Nat.mod_modEq b q).symm.of_dvd (Nat.gcd_dvd_right k q))
  · rintro ⟨hr,hcompat⟩
    have hrC : r.val.Coprime q := by
      apply (ZMod.isUnit_iff_coprime r.val q).mp
      simpa only [ZMod.natCast_zmod_val] using hr
    obtain ⟨b,hb,hbq⟩ := goldbach_major_compatible_lift k q a r.val
      (NeZero.ne k) (NeZero.ne q) ha hrC hcompat
    refine ⟨b,hb,?_⟩
    have hc := (ZMod.natCast_eq_natCast_iff b r.val q).mpr hbq
    simpa only [ZMod.natCast_zmod_val] using hc

theorem goldbach_major_castq_injective (k q a : ℕ) [NeZero q] :
    Set.InjOn (fun b : ℕ => (b:ZMod q)) (↑(goldbachMajorResidues k q a):Set ℕ) := by
  intro b hb c hc heq
  exact goldbach_major_residues_modq_injective k q a hb hc
    ((ZMod.natCast_eq_natCast_iff b c q).mp heq)

theorem goldbach_major_residue_sum (k q a : ℕ) [NeZero k] [NeZero q]
    (ha : a.Coprime k) (f : ZMod q→ℂ) :
    (∑ b∈goldbachMajorResidues k q a,f (b:ZMod q))=
      ∑ u : (ZMod q)ˣ,if Nat.ModEq (k.gcd q) a (u:ZMod q).val then f u else 0 := by
  classical
  rw [←sum_image (goldbach_major_castq_injective k q a),goldbach_major_residue_image k q a ha]
  unfold goldbachMajorQResidues
  simp only [sum_filter]
  have he : (∑ r : ZMod q,if IsUnit r ∧ Nat.ModEq (k.gcd q) a r.val then f r else 0)=
      ∑ r : ZMod q,if IsUnit r then (if Nat.ModEq (k.gcd q) a r.val then f r else 0) else 0 := by
    apply sum_congr rfl
    intro r _
    by_cases hu : IsUnit r <;> by_cases hc : Nat.ModEq (k.gcd q) a r.val <;> simp [hu,hc]
  rw [he,sum_unit_filter_eq_sum_units]

theorem goldbach_major_compatibility_character (k q a : ℕ) [NeZero q] (r : ZMod q) :
    Nat.ModEq (k.gcd q) a r.val ↔
      ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) r=(a:ZMod (q.gcd k)) := by
  rw [←goldbach_reduction_val (Nat.gcd_dvd_left q k) r]
  rw [ZMod.natCast_eq_natCast_iff]
  rw [Nat.gcd_comm k q]
  exact ⟨Nat.ModEq.symm,Nat.ModEq.symm⟩

/-- Exact source Upsilon normalization for the compatible lcm residues. -/
theorem goldbach_major_upsilon_identity (k q a : ℕ) [NeZero k] [NeZero q]
    (ha : a.Coprime k) (α : ZMod q) :
    ((k.lcm q).totient:ℂ)⁻¹*
      (∑ b∈goldbachMajorResidues k q a,ZMod.stdAddChar (α*(b:ZMod q)))=
      upsilon q k (a:ℤ) (-α)/(k.totient:ℂ) := by
  rw [goldbach_major_residue_sum k q a ha (fun r => ZMod.stdAddChar (α*r))]
  unfold upsilon progressionExponentialSum
  have hk : (k.totient:ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos k)).ne'
  have hs : (∑ u : (ZMod q)ˣ,if Nat.ModEq (k.gcd q) a (u:ZMod q).val then
      ZMod.stdAddChar (α*(u:ZMod q)) else 0)=
      ∑ u : (ZMod q)ˣ,if ZMod.castHom (Nat.gcd_dvd_left q k) (ZMod (q.gcd k)) (u:ZMod q)=
        ((a:ℤ):ZMod (q.gcd k)) then ZMod.stdAddChar (-(-α*(u:ZMod q))) else 0 := by
    apply sum_congr rfl
    intro u _
    simp only [goldbach_major_compatibility_character,Int.cast_natCast,neg_mul,neg_neg]
  rw [hs]
  field_simp [hk]

end PrimeSquares
