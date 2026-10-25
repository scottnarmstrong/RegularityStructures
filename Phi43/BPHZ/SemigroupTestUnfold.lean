/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgePeriodise
public import RegularityStructures.Torus.HeatKernelFacts
public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Unfolding of nonnegative integrals onto the torus

For a measurable `H : ℝ³ → [0, ∞]`,
`∫⁻_{ℝ³} H = ∫⁻_{T³} ∑_{k ∈ ℤ³} H (torusRep u + k) du`
(`lintegral_eq_lintegral_torus_tsum`), and, for `H : ℝ × ℝ³ → [0, ∞]`, the same identity on
`ℝ × T³` with the time variable carried along (`lintegral_eq_lintegral_spaceTime_tsum`).

This is the `[0, ∞]`-valued companion of `integral_eq_integral_torus_tsum`; unlike the real
version it needs no integrability and yields the integrability of the periodised sum.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

private def unfoldUnitCell : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1)

private def unfoldIntCell (k : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (k i : ℝ) ((k i : ℝ) + 1))

private theorem unfoldIntCell_measurable (k : Fin 3 → ℤ) : MeasurableSet (unfoldIntCell k) :=
  (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => measurableSet_Ioc)

private theorem unfoldIntCell_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint unfoldIntCell) := by
  intro k l hkl
  change Disjoint (unfoldIntCell k) (unfoldIntCell l)
  rw [Set.disjoint_left]
  intro x hxk hxl
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, k i ≠ l i := by
    by_contra h
    apply hkl
    funext i
    by_contra hi'
    exact h ⟨i, hi'⟩
  have hki : x i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1) := hxk i (Set.mem_univ i)
  have hli : x i ∈ Set.Ioc (l i : ℝ) ((l i : ℝ) + 1) := hxl i (Set.mem_univ i)
  rcases lt_or_gt_of_ne hi with hkl' | hlk'
  · have hcast : (k i : ℝ) + 1 ≤ (l i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hkl')
    linarith [hki.2, hli.1]
  · have hcast : (l i : ℝ) + 1 ≤ (k i : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hlk')
    linarith [hki.1, hli.2]

private theorem unfoldIntCell_cover : ⋃ k : Fin 3 → ℤ, unfoldIntCell k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  choose k hk using fun i : Fin 3 => by
    have hi : x i ∈ ⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1) := by
      rw [iUnion_Ioc_intCast]
      trivial
    exact Set.mem_iUnion.mp hi
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_pi.mpr (fun i _ => by simpa [unfoldIntCell] using hk i)⟩

/-- The cell change of variables, on the level of `[0, ∞]`-valued integrals. -/
private theorem unfold_cell_change {H : (Fin 3 → ℝ) → ℝ≥0∞} (hH : Measurable H)
    (k : Fin 3 → ℤ) :
    ∫⁻ x in unfoldUnitCell, H (x + fun i => (k i : ℝ)) = ∫⁻ x in unfoldIntCell k, H x := by
  let kR : Fin 3 → ℝ := fun i => (k i : ℝ)
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.addRight kR
  have he : MeasurePreserving (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) volume volume :=
    measurePreserving_add_right volume kR
  have hpre : e ⁻¹' unfoldIntCell k = unfoldUnitCell := by
    ext x
    constructor
    · intro hx
      refine Set.mem_pi.mpr (fun i _ => ?_)
      have hi := hx i (Set.mem_univ i)
      change x i + kR i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1) at hi
      dsimp [kR] at hi
      change x i ∈ Set.Ioc (0 : ℝ) 1
      constructor <;> linarith [hi.1, hi.2]
    · intro hx
      refine Set.mem_pi.mpr (fun i _ => ?_)
      have hi := hx i (Set.mem_univ i)
      change x i + kR i ∈ Set.Ioc (k i : ℝ) ((k i : ℝ) + 1)
      dsimp [kR]
      constructor <;> linarith [hi.1, hi.2]
  have hchange := he.setLIntegral_comp_preimage (unfoldIntCell_measurable k) hH
  rw [hpre] at hchange
  exact hchange

private theorem unfold_torusRep_torusProj (x : Fin 3 → ℝ) :
    ∃ m : Fin 3 → ℤ, torusRep (torusProj x) = x + fun i => (m i : ℝ) := by
  have h : ∀ i, ∃ n : ℤ, torusRep (torusProj x) i = x i + n := by
    intro i
    have h1 : ((torusRep (torusProj x) i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle) := by
      have := congrFun (show torusProj (torusRep (torusProj x)) = torusProj x by
        funext j; simp [torusProj, torusRep]) i
      simpa [torusProj] using this
    have h2 : ((torusRep (torusProj x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h2
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  choose m hm using h
  exact ⟨m, funext fun i => hm i⟩

/-- Re-indexing of the lattice sum, for `[0, ∞]`-valued summands. -/
theorem tsum_comp_torusRep_torusProj_ennreal (H : (Fin 3 → ℝ) → ℝ≥0∞) (x : Fin 3 → ℝ) :
    ∑' k : Fin 3 → ℤ, H (torusRep (torusProj x) + fun i => (k i : ℝ)) =
      ∑' k : Fin 3 → ℤ, H (x + fun i => (k i : ℝ)) := by
  obtain ⟨m, hm⟩ := unfold_torusRep_torusProj x
  rw [hm]
  have hk : ∀ k : Fin 3 → ℤ, (x + fun i => (m i : ℝ)) + (fun i => (k i : ℝ)) =
      x + fun i => (((m + k) i : ℤ) : ℝ) := by
    intro k
    funext i
    simp [add_assoc]
  simp_rw [hk]
  exact (Equiv.addLeft m).tsum_eq (fun k : Fin 3 → ℤ => H (x + fun i => (k i : ℝ)))

private theorem unfold_lintegral_torus_eq_cell (G : Torus3 → ℝ≥0∞) :
    ∫⁻ u : Torus3, G u = ∫⁻ x in unfoldUnitCell, G (torusProj x) := by
  have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have htorus : (volume : Measure Torus3) =
      Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle) := by
    change Measure.pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle)) = _
    rw [hcircle]
  have hpre := UnitAddTorus.lintegral_preimage G (0 : Fin 3 → ℝ)
  have hD : {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc
      ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)} = unfoldUnitCell := by
    ext x
    simp [unfoldUnitCell]
  rw [hD] at hpre
  rw [htorus]
  simp only [MeasureSpace.volume]
    at hpre ⊢
  exact hpre

/-- **Unfolding of `[0, ∞]`-valued integrals onto the torus.** -/
theorem lintegral_eq_lintegral_torus_tsum {H : (Fin 3 → ℝ) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H x = ∫⁻ u : Torus3, ∑' k : Fin 3 → ℤ, H (torusRep u + fun i => (k i : ℝ)) := by
  rw [unfold_lintegral_torus_eq_cell]
  have hshift : ∀ k : Fin 3 → ℤ, Measurable (fun x : Fin 3 → ℝ => H (x + fun i => (k i : ℝ))) :=
    fun k => hH.comp (measurable_id.add_const _)
  calc ∫⁻ x, H x = ∫⁻ x in ⋃ k : Fin 3 → ℤ, unfoldIntCell k, H x := by
        rw [unfoldIntCell_cover, Measure.restrict_univ]
    _ = ∑' k : Fin 3 → ℤ, ∫⁻ x in unfoldIntCell k, H x :=
        lintegral_iUnion unfoldIntCell_measurable unfoldIntCell_pairwise_disjoint H
    _ = ∑' k : Fin 3 → ℤ, ∫⁻ x in unfoldUnitCell, H (x + fun i => (k i : ℝ)) :=
        tsum_congr fun k => (unfold_cell_change hH k).symm
    _ = ∫⁻ x in unfoldUnitCell, ∑' k : Fin 3 → ℤ, H (x + fun i => (k i : ℝ)) :=
        (lintegral_tsum fun k => (hshift k).aemeasurable).symm
    _ = _ := by
        refine setLIntegral_congr_fun ?_ fun x _ => ?_
        · exact (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => measurableSet_Ioc)
        · exact (tsum_comp_torusRep_torusProj_ennreal H x).symm

/-- **Unfolding on space-time.** For measurable `H : ℝ × ℝ³ → [0, ∞]`,
`∫⁻_{ℝ⁴} H = ∫⁻_{ℝ × T³} ∑_k H (t, torusRep u + k)`. -/
theorem lintegral_eq_lintegral_spaceTime_tsum {H : ParabolicSpace → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ y : ParabolicSpace, H y =
      ∫⁻ q : SpaceTime, ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ)) := by
  have hF : Measurable (fun q : SpaceTime =>
      ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
    Measurable.tsum fun k => hH.comp
      (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))
  calc ∫⁻ y : ParabolicSpace, H y = ∫⁻ t : ℝ, ∫⁻ z : Fin 3 → ℝ, H (t, z) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod _ hH.aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ u : Torus3, ∑' k : Fin 3 → ℤ, H (t, torusRep u + fun i => (k i : ℝ)) :=
        lintegral_congr fun t => lintegral_eq_lintegral_torus_tsum (hH.comp measurable_prodMk_left)
    _ = _ := by
        rw [Measure.volume_eq_prod]
        exact (lintegral_prod _ hF.aemeasurable).symm

end RegularityStructures.Phi43

end
