/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.FrechetHeatBridge
public import GlobalPhi43.Local.SmallScaleLocalData
public import GlobalPhi43.MW20.BarrierRegularity

/-! The actual augmented native PDE rows from local data. The
smooth representative uses only the original local solution neighbourhood. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Filter Topology
open scoped ContDiff

 theorem localData_augmented_sourceHeat
    {u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ} {C₁ C₂ : ℝ}
    (hd : IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂) :
    ∃ (v : ParabolicSpace → ℝ) (W : Set ParabolicSpace),
      ContDiff ℝ ∞ v ∧ IsOpen W ∧ closure mwCylinder ⊆ W ∧
      EqOn v (fun z => u z - J z) W ∧
      ∀ z ∈ mwCylinder,
        sourceHeat v z = -v z ^ 3 - 3 * v z ^ 2 * J z -
          3 * v z * (J z ^ 2 - C₁) - (J z ^ 3 - 3 * C₁ * J z) -
          9 * C₂ * (v z + J z) - e₁ z ∧
        sourceHeat Y z = (J z ^ 2 - C₁) + e₂ z ∧
        sourceHeat Z z = (J z ^ 3 - 3 * C₁ * J z) + e₃ z := by
  rcases hd with ⟨⟨O, hO, hKO, hu⟩, _, hJ, hY, hZ, _, _, _, huPDE, hTrees⟩
  obtain ⟨u', W, hu', hW, hKW, _, he, _, _⟩ :=
    exists_smooth_representative isCompact_closure_mwCylinder hO hKO u hu
  let v := fun z => u' z - J z
  have hv : ContDiff ℝ ∞ v := hu'.sub hJ
  refine ⟨v, W, hv, hW, hKW, fun z hz => ?_, ?_⟩
  · dsimp [v]
    rw [he hz]
  · intro z hz
    have hnear : u' =ᶠ[𝓝 z] u := by
      filter_upwards [hW.mem_nhds (hKW (subset_closure hz))] with w hw
      exact he hw
    have hval : u z = v z + J z := by
      dsimp [v]
      rw [hnear.self_of_nhds]
      ring
    have hzplus : z ∈ parabolicClosedNbhd mwCylinder 1 :=
      ⟨z, hz, by simp [parabolicDist]⟩
    have ht := hTrees z hzplus
    refine ⟨?_, ?_, ?_⟩
    · change sourceHeat (fun z => u' z - J z) z = _
      rw [sourceHeat_sub_of_contDiffAt z (hu'.contDiffAt.of_le (by norm_num))
        (hJ.contDiffAt.of_le (by norm_num)), sourceHeat_eq_heatOperator hu',
        sourceHeat_eq_heatOperator hJ, heatOperator_eq_of_eventuallyEq hnear,
        huPDE z hz, ht.1, hval]
      ring
    · rw [sourceHeat_eq_heatOperator hY]
      exact ht.2.1
    · rw [sourceHeat_eq_heatOperator hZ]
      exact ht.2.2

 theorem sourceSup_remainder_representative {u J v : ParabolicSpace → ℝ}
    {W : Set ParabolicSpace} (hKW : closure mwCylinder ⊆ W)
    (heq : EqOn v (fun z => u z - J z) W) {r : ℝ} (hr : 0 ≤ r) :
    sourceSup v r = sourceSup (fun z => u z - J z) r := by
  unfold sourceSup
  congr 1
  apply Set.image_congr
  intro z hz
  have hzP : z ∈ mwCylinder := by
    rw [mwCylinder_eq_sourceCylinder]
    exact sourceCylinder_antitone (by norm_num : (0 : ℝ) ≤ 0) hr hz
  exact congrArg abs (heq (hKW (subset_closure hzP)))

end GlobalPhi43.Local
