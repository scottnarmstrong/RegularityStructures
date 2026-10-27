/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SourceSectionHeat
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.Local.ClosedPastSampling
public import GlobalPhi43.Local.LocalHeatSupremum
public import GlobalPhi43.MW20.PastBallNormDomains

/-! The forcing supremum in the heat-affine estimate is exactly the
smoothed source-heat supremum in the original one-point hypothesis. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff

 theorem source_section_heat_supremum_eq (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (U : GermPoint → ℝ) {r d L T : ℝ} (hr : 0 ≤ r)
    (hT : 0 < T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hLT : L + T ≤ d)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d) :
    localScalarSup (sourceHeat (fun z => ∫ w, U (x, z + w)
        ∂infiniteKernelMeasure Φ hΦ T hT)) (pastBall x L) =
      localScalarSup (fun y => ∫ w, sourceHeat (fun z => U (x, z)) (y + w)
        ∂infiniteKernelMeasure Φ hΦ T hT) (pastBall x L) := by
  unfold localScalarSup
  apply iSup_congr
  intro y
  apply iSup_congr
  intro hy
  rw [(source_section_heat_smoothing Φ hΦ U hr hT hT₁ hL hLT hU hx hy).1]

 theorem source_section_heat_supremum_ne_top
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (U : GermPoint → ℝ) {r d L T : ℝ} (hr : 0 ≤ r)
    (hT : 0 < T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hLT : L + T ≤ d)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d) :
    localScalarSup (sourceHeat (fun z => ∫ w, U (x, z + w)
      ∂infiniteKernelMeasure Φ hΦ T hT)) (pastBall x L) ≠ ⊤ := by
  obtain ⟨O, hO, hboxO, hsmooth⟩ := exists_source_smoothing_closed_past_neighbourhood
    Φ hΦ U hr hT hT₁ hL hLT hU hx
  have hcbox : IsClosed {y : ParabolicSpace | pdist x y ≤ L ∧ y.1 ≤ x.1} := by
    apply IsClosed.inter
    · exact isClosed_le (show Continuous (fun y : ParabolicSpace => pdist x y) by unfold pdist; fun_prop) continuous_const
    · exact isClosed_le continuous_fst continuous_const
  have hclosure : closure (pastBall x L) ⊆ {y | pdist x y ≤ L ∧ y.1 ≤ x.1} :=
    closure_minimal (fun _ hy => ⟨hy.1.le, hy.2.le⟩) hcbox
  have hcompact : IsCompact (closure (pastBall x L)) :=
    (isCompact_closedBall (0 : ParabolicSpace) (‖x‖ + max (L ^ 2) L)).of_isClosed_subset
      isClosed_closure (closure_minimal (pastBall_subset_compact_ball x hL) Metric.isClosed_closedBall)
  exact local_heat_supremum_ne_top hcompact hO (hclosure.trans hboxO) hsmooth subset_closure

end GlobalPhi43.Local
