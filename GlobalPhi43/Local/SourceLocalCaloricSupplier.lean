/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CaloricAffineEstimate
public import GlobalPhi43.Local.SourceHeatSupremum
public import GlobalPhi43.MW20.SourceCaloricStep

/-! The caloric estimate on original local smooth source data;
all open neighbourhoods and finite heat suprema are derived. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set MeasureTheory
open scoped ContDiff ENNReal

 theorem exists_source_local_caloric_supplier : ∃ C > 0,
    ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
      (U : GermPoint → ℝ) (r d η L : ℝ) (hη : 0 < η) (hL : 0 < L),
      0 ≤ r → η ≤ 1 → η ^ 2 * L ≤ 1 → L + η ^ 2 * L ≤ d →
      (∃ O : Set GermPoint, IsOpen O ∧
        closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) →
      ∀ x ∈ cylinderInterior r d, sourceCaloricStep Φ hΦ U C η L hη hL x := by
  obtain ⟨C, hC, hb⟩ := exists_caloric_affine_estimate
  refine ⟨C, hC, ?_⟩
  intro Φ hΦ U r d η L hη hL hr hηone hT hLT hU x hx
  have hTp : 0 < η ^ 2 * L := mul_pos (sq_pos_of_pos hη) hL
  let μ := infiniteKernelMeasure Φ hΦ (η ^ 2 * L) hTp
  let g := pastSmooth μ (fun y => U (x, y))
  obtain ⟨O, hO, hboxO, hsmooth⟩ := exists_source_smoothing_closed_past_neighbourhood
    Φ hΦ U hr hTp hT hL.le hLT hU hx
  have hcbox : IsClosed {y : ParabolicSpace | pdist x y ≤ L ∧ y.1 ≤ x.1} :=
    (isClosed_le (show Continuous (fun y : ParabolicSpace => pdist x y) by unfold pdist; fun_prop)
      continuous_const).inter (isClosed_le continuous_fst continuous_const)
  have hclbox : closure (pastBall x L) ⊆ {y | pdist x y ≤ L ∧ y.1 ≤ x.1} :=
    closure_minimal (fun _ hy => ⟨hy.1.le, hy.2.le⟩) hcbox
  have hclosure : closure (pastBall x L) ⊆ O := hclbox.trans hboxO
  have hQ : localScalarSup (sourceHeat g) (pastBall x L) ≠ ⊤ :=
    source_section_heat_supremum_ne_top Φ hΦ U hr hTp hT hL.le hLT hU hx
  have hout := hb g x L (η * L) hL (mul_pos hη hL).le
    (mul_le_of_le_one_left hL.le hηone) O hO hclosure hsmooth
  have hreal : ENNReal.ofReal (C * L ^ 2) * localScalarSup (sourceHeat g) (pastBall x L) =
      ENNReal.ofReal (C * L ^ 2 * (localScalarSup (sourceHeat g) (pastBall x L)).toReal) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hC.le (sq_nonneg L)), ENNReal.ofReal_toReal hQ]
  rw [hreal] at hout
  exact hout

end GlobalPhi43.Local
