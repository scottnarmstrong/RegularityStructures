/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitCaloricSupremum
public import GlobalPhi43.Local.UnitPastClosure
public import GlobalPhi43.Local.CaloricScaling

/-! The ordinary-heat affine estimate on actual source past balls, from
the proved analytic unit estimate and exact amplitude-one transport. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff ENNReal

 theorem exists_caloric_affine_estimate : ∃ C > 0,
    ∀ (h : ParabolicSpace → ℝ) (x : ParabolicSpace) (L R : ℝ), 0 < L →
      0 ≤ R → R ≤ L → ∀ O : Set ParabolicSpace, IsOpen O →
      closure (pastBall x L) ⊆ O → ContDiffOn ℝ ∞ h O →
      pastAffineError h x R ≤
        ENNReal.ofReal (C * (R / L) ^ 2) * pastAffineError h x L +
          ENNReal.ofReal (C * L ^ 2) * localScalarSup (sourceHeat h) (pastBall x L) := by
  obtain ⟨C, hC, hb⟩ := exists_unit_caloric_supremum
  refine ⟨C, hC, ?_⟩
  intro h x L R hL hR hRL O hO hKO hh
  have hz : parabolicMap x L 0 = x := by simp [parabolicMap, parabolicDilate]
  have hcarrier : parabolicMap x L '' unitHeatPastCarrier = closure (pastBall x L) := by
    rw [unitHeatPastCarrier_eq_closure, parabolicMap_image_closure_pastBall x hL, hz, mul_one]
  have hpre : unitHeatPastCarrier ⊆ parabolicMap x L ⁻¹' O := by
    intro z hz'
    apply hKO
    rw [← hcarrier]
    exact ⟨z, hz', rfl⟩
  have hopen : IsOpen (parabolicMap x L ⁻¹' O) :=
    (parabolicTransport x L hL.ne').continuous.isOpen_preimage _ hO
  have hsmooth : ContDiffOn ℝ ∞ (fun z => h (parabolicMap x L z))
      (parabolicMap x L ⁻¹' O) := by
    simpa only [parabolicPullback_one] using parabolicPullback_contDiffOn 1 h x L hh
  have heL := pastAffineError_comp_parabolicMap h x hL 0 1
  rw [hz, mul_one] at heL
  have heR := pastAffineError_comp_parabolicMap h x hL 0 (R / L)
  rw [hz, show L * (R / L) = R by field_simp] at heR
  have hQ := localScalarSup_sourceHeat_parabolicPullback 1 h x hL 0 1
  simp only [parabolicPullback_one, hz, mul_one, one_mul, abs_of_nonneg (sq_nonneg L)] at hQ
  have hout := hb (fun z => h (parabolicMap x L z)) _ hopen hpre hsmooth (R / L)
    (div_nonneg hR hL.le) ((div_le_one hL).mpr hRL)
  rw [heR, heL, hQ, ← mul_assoc, ← ENNReal.ofReal_mul hC.le] at hout
  exact hout

end GlobalPhi43.Local
