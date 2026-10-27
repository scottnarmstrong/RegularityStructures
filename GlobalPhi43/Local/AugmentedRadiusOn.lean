/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedRadius
public import GlobalPhi43.Local.CompactCylinderSup

/-! Augmented iteration on the local compact-cylinder carrier. Global
continuity is not assumed. The analytic interior row is still an input. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20

/-- Actual-cylinder augmented iteration, with the stopping alternative proved.
No assumed finite sequence, terminal halving or positive mass profile is used. -/
theorem augmented_radius_estimate_on {I : Type*} [Fintype I] [Nonempty I]
    (v : ParabolicSpace → ℝ) (hv : ContinuousOn v sourceClosedCylinder) (B p : I → ℝ)
    {C c E₁ E₂ E₃ : ℝ} (hC : 1 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1)
    (hB : ∀ i, 0 ≤ B i) (hp : ∀ i, 0 < p i)
    (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) (h₃ : 0 ≤ E₃)
    (hmax : ∀ r ∈ Icc (0 : ℝ) (1 / 2),
      AugmentedSmall B p c (sourceSup v r) E₁ E₂ E₃ → 0 < sourceSup v r →
      ∀ R, 2 / sourceSup v r ≤ R → r + R < 1 / 2 →
        sourceSup v (r + R) ≤ max (C / (R - 1 / sourceSup v r)) (sourceSup v r / 2)) :
    ∀ R ∈ Ioc (0 : ℝ) (1 / 2), sourceSup v R ≤
      max (8 * C / R) (max (treeRadiusMajorant B p c) ((2 / c) * defectScale E₁ E₂ E₃)) := by
  refine source_radius_estimate_on v hv
    (fun r => AugmentedSmall B p c (sourceSup v r) E₁ E₂ E₃) hC ?_ hmax ?_
  · exact le_max_of_le_left (treeRadiusMajorant_nonneg B p hc hB)
  · intro r hr hfail
    exact augmented_stopping_bound B p hc hc₁ (sourceSup_nonneg_on hv hr)
      hB hp h₁ h₂ h₃ hfail

/-- The iteration constant is chosen before every field, tree norm and defect.
Its only parameters are C,c and the finite positive exponent family. -/
theorem augmented_radius_uniform_on {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) {C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1)
    (hp : ∀ i, 0 < p i) :
    ∃ K > 0, ∀ (v : ParabolicSpace → ℝ), ContinuousOn v sourceClosedCylinder → ∀ (B : I → ℝ),
      (∀ i, 0 ≤ B i) → ∀ E₁ E₂ E₃, 0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ →
      (∀ r ∈ Icc (0 : ℝ) (1 / 2),
        AugmentedSmall B p c (sourceSup v r) E₁ E₂ E₃ → 0 < sourceSup v r →
        ∀ R, 2 / sourceSup v r ≤ R → r + R < 1 / 2 →
          sourceSup v (r + R) ≤ max (C / (R - 1 / sourceSup v r)) (sourceSup v r / 2)) →
      ∀ R ∈ Ioc (0 : ℝ) (1 / 2), sourceSup v R ≤
        K * max (1 / R) (max (treeRadiusMajorant B p 1) (defectScale E₁ E₂ E₃)) := by
  let D := max (treeRadiusMajorant (fun _ : I => 1) p c) (2 / c)
  let K := max (8 * C) D
  have hK : 0 < K := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro v hv B hB E₁ E₂ E₃ h₁ h₂ h₃ hmax R hR
  have hb := augmented_radius_estimate_on v hv B p hC hc hc₁ hB hp h₁ h₂ h₃ hmax R hR
  have hB0 := treeRadiusMajorant_nonneg B p (by norm_num : (0 : ℝ) < 1) hB
  have hE0 := defectScale_nonneg (E₂ := E₂) (E₃ := E₃) h₁
  have hD : treeRadiusMajorant (fun _ : I => 1) p c ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hcK : 2 / c ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hdata : max (treeRadiusMajorant B p c) ((2 / c) * defectScale E₁ E₂ E₃) ≤
      K * max (treeRadiusMajorant B p 1) (defectScale E₁ E₂ E₃) := by
    apply max_le
    · exact (treeRadiusMajorant_scale B p hc hB).trans
        ((mul_le_mul_of_nonneg_right hD hB0).trans
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hK.le))
    · exact (mul_le_mul_of_nonneg_right hcK hE0).trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hK.le)
  apply hb.trans
  apply max_le
  · have ht := mul_le_mul_of_nonneg_right (le_max_left (8 * C) D) (one_div_pos.mpr hR.1).le
    have hbnd : 8 * C / R ≤ K * (1 / R) := by
      simpa only [div_eq_mul_inv, one_mul] using ht
    exact hbnd.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hK.le)
  · exact hdata.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hK.le)

end GlobalPhi43.Local
