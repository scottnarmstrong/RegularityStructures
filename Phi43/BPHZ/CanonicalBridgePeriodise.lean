/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Unfolding an integral over `ℝ³` onto the torus

For an integrable `H : ℝ³ → ℝ`, summing over integer translates and integrating over the torus
recovers the integral over `ℝ³`:
`∫_{ℝ³} H = ∫_{T³} ∑_{k ∈ ℤ³} H (torusRep u + k) du`.
This is the one-slice form of the periodisation identity used in `CanonicalBridgeConvolution`.
The proof splits `ℝ³` into the unit cubes `(k, k+1]` and uses the fundamental-domain formula
`UnitAddTorus.integral_preimage`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

open RegularityStructures

private def bridgeUnitCell : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun _ : Fin 3 => Set.Ioc (0 : ℝ) 1)

private def bridgeIntCell (k : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (k i : ℝ) ((k i : ℝ) + 1))

private theorem bridgeUnitCell_measurable : MeasurableSet bridgeUnitCell :=
  (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => measurableSet_Ioc)

private theorem bridgeIntCell_measurable (k : Fin 3 → ℤ) : MeasurableSet (bridgeIntCell k) :=
  (measurableSet_pi Set.countable_univ).2 (Or.inl fun _ _ => measurableSet_Ioc)

private theorem bridgeIntCell_pairwise_disjoint :
    Pairwise (Function.onFun Disjoint bridgeIntCell) := by
  intro k l hkl
  change Disjoint (bridgeIntCell k) (bridgeIntCell l)
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

private theorem bridgeIntCell_cover : ⋃ k : Fin 3 → ℤ, bridgeIntCell k = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  choose k hk using fun i : Fin 3 => by
    have hi : x i ∈ ⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1) := by
      rw [iUnion_Ioc_intCast]
      trivial
    exact Set.mem_iUnion.mp hi
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_pi.mpr (fun i _ => by simpa [bridgeIntCell] using hk i)⟩

private theorem bridge_cell_change (H : (Fin 3 → ℝ) → ℝ) (k : Fin 3 → ℤ) :
    ∫ x in bridgeUnitCell, H (x + fun i => (k i : ℝ)) = ∫ x in bridgeIntCell k, H x := by
  let kR : Fin 3 → ℝ := fun i => (k i : ℝ)
  let e : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) := MeasurableEquiv.addRight kR
  have he : MeasurePreserving (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) volume volume :=
    measurePreserving_add_right volume kR
  have hpre : e ⁻¹' bridgeIntCell k = bridgeUnitCell := by
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
  have hchange := (he.restrict_preimage (bridgeIntCell_measurable k)).integral_comp' H
  rw [hpre] at hchange
  exact hchange

private theorem bridge_torusRep_torusProj (x : Fin 3 → ℝ) :
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

/-- Re-indexing the lattice sum: the representative in `[0,1)³` changes the sum by an integer shift. -/
theorem tsum_comp_torusRep_torusProj (H : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    ∑' k : Fin 3 → ℤ, H (torusRep (torusProj x) + fun i => (k i : ℝ)) =
      ∑' k : Fin 3 → ℤ, H (x + fun i => (k i : ℝ)) := by
  obtain ⟨m, hm⟩ := bridge_torusRep_torusProj x
  rw [hm]
  have hk : ∀ k : Fin 3 → ℤ, (x + fun i => (m i : ℝ)) + (fun i => (k i : ℝ)) =
      x + fun i => (((m + k) i : ℤ) : ℝ) := by
    intro k
    funext i
    simp [add_assoc]
  simp_rw [hk]
  exact (Equiv.addLeft m).tsum_eq (fun k : Fin 3 → ℤ => H (x + fun i => (k i : ℝ)))

private theorem bridge_integral_torus_eq_cell (G : Torus3 → ℝ) :
    ∫ u : Torus3, G u = ∫ x in bridgeUnitCell, G (torusProj x) := by
  have hcircle : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have htorus : (volume : Measure Torus3) =
      Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle) := by
    change Measure.pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle)) = _
    rw [hcircle]
  have hpre := UnitAddTorus.integral_preimage G (0 : Fin 3 → ℝ)
  have hD : {x : Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc
      ((0 : Fin 3 → ℝ) i) ((0 : Fin 3 → ℝ) i + 1)} = bridgeUnitCell := by
    ext x
    simp [bridgeUnitCell]
  rw [hD] at hpre
  rw [htorus]
  simp only [MeasureSpace.volume]
    at hpre ⊢
  exact hpre

/-- **Unfolding onto the torus.**  For integrable `H : ℝ³ → ℝ`,
`∫_{ℝ³} H = ∫_{T³} ∑_{k ∈ ℤ³} H (torusRep u + k) du`. -/
theorem integral_eq_integral_torus_tsum {H : (Fin 3 → ℝ) → ℝ} (hH : Integrable H) :
    ∫ x, H x = ∫ u : Torus3, ∑' k : Fin 3 → ℤ, H (torusRep u + fun i => (k i : ℝ)) := by
  have hshift : ∀ k : Fin 3 → ℤ, Integrable (fun x => H (x + fun i => (k i : ℝ))) :=
    fun k => (measurePreserving_add_right (volume : Measure (Fin 3 → ℝ))
      (fun i => (k i : ℝ))).integrable_comp_of_integrable hH
  have hsum_norm : Summable (fun k : Fin 3 → ℤ =>
      ∫ x in bridgeUnitCell, ‖H (x + fun i => (k i : ℝ))‖) := by
    have hsum_cell : HasSum (fun k : Fin 3 → ℤ => ∫ x in bridgeIntCell k, |H x|)
        (∫ x, |H x|) := by
      have hi := hasSum_integral_iUnion (f := fun x : Fin 3 → ℝ => |H x|)
        (fun k => bridgeIntCell_measurable k) bridgeIntCell_pairwise_disjoint
        hH.norm.integrableOn
      rw [bridgeIntCell_cover, Measure.restrict_univ] at hi
      exact hi
    have hcell_eq : ∀ k : Fin 3 → ℤ, ∫ x in bridgeUnitCell, ‖H (x + fun i => (k i : ℝ))‖ =
        ∫ x in bridgeIntCell k, |H x| := fun k =>
      bridge_cell_change (fun z => |H z|) k
    rw [show (fun k : Fin 3 → ℤ => ∫ x in bridgeUnitCell, ‖H (x + fun i => (k i : ℝ))‖) =
        (fun k => ∫ x in bridgeIntCell k, |H x|) by funext k; exact hcell_eq k]
    exact hsum_cell.summable
  have hsum : HasSum (fun k : Fin 3 → ℤ => ∫ x in bridgeUnitCell, H (x + fun i => (k i : ℝ)))
      (∫ x, H x) := by
    have hi := hasSum_integral_iUnion (f := H) (fun k => bridgeIntCell_measurable k)
      bridgeIntCell_pairwise_disjoint hH.integrableOn
    rw [bridgeIntCell_cover, Measure.restrict_univ] at hi
    exact hi.congr_fun (fun k => bridge_cell_change H k)
  have hmeas : ∀ k : Fin 3 → ℤ, AEStronglyMeasurable
      (fun x : Fin 3 → ℝ => H (x + fun i => (k i : ℝ))) (volume.restrict bridgeUnitCell) :=
    fun k => (hshift k).aestronglyMeasurable.restrict
  have hterm : ∀ k : Fin 3 → ℤ,
      ∫⁻ x in bridgeUnitCell, ‖H (x + fun i => (k i : ℝ))‖ₑ =
        ‖∫ x in bridgeUnitCell, ‖H (x + fun i => (k i : ℝ))‖‖ₑ := by
    intro k
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hshift k).integrableOn.norm]
    simp only [ENNReal.coe_nnreal_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))]
  have hnorm : (∑' k : Fin 3 → ℤ, ∫⁻ x in bridgeUnitCell,
      ‖H (x + fun i => (k i : ℝ))‖ₑ) ≠ (⊤ : ENNReal) := by
    rw [funext hterm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hsum_norm.abs
  have htsum := integral_tsum hmeas hnorm
  rw [bridge_integral_torus_eq_cell]
  calc
    ∫ x, H x = ∑' k : Fin 3 → ℤ, ∫ x in bridgeUnitCell, H (x + fun i => (k i : ℝ)) :=
      hsum.tsum_eq.symm
    _ = ∫ x in bridgeUnitCell, ∑' k : Fin 3 → ℤ, H (x + fun i => (k i : ℝ)) := htsum.symm
    _ = _ := by
      refine setIntegral_congr_fun bridgeUnitCell_measurable fun x _ => ?_
      exact (tsum_comp_torusRep_torusProj H x).symm

end RegularityStructures.Phi43

end
