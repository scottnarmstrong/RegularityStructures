/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedRadiusOn
public import GlobalPhi43.Local.AugmentedIteration
public import GlobalPhi43.Local.CylinderClosure

/-! The augmented iteration on the local smooth-data domain, conditional
on the interior estimate. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20
open scoped ContDiff

/-- The interior estimate used by the radius iteration, with the original
common c and the actual cylinder mass. -/
@[expose] def RadiusInteriorRow {I : Type*} (v : ParabolicSpace → ℝ)
    (B p : I → ℝ) (C c E₁ E₂ E₃ : ℝ) : Prop :=
  ∀ r ∈ Icc (0 : ℝ) (1 / 2),
    AugmentedSmall B p c (sourceSup v r) E₁ E₂ E₃ → 0 < sourceSup v r →
    ∀ R, 2 / sourceSup v r ≤ R → r + R < 1 / 2 →
      sourceSup v (r + R) ≤ max (C / (R - 1 / sourceSup v r)) (sourceSup v r / 2)

/-- The full-radius uniform estimate from compact-cylinder continuity only. -/
theorem augmented_radius_on_all {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) {C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1)
    (hp : ∀ i, 0 < p i) :
    ∃ K > 0, ∀ (v : ParabolicSpace → ℝ), ContinuousOn v sourceClosedCylinder →
      ∀ (B : I → ℝ), (∀ i, 0 ≤ B i) → ∀ E₁ E₂ E₃,
      0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ → RadiusInteriorRow v B p C c E₁ E₂ E₃ →
      ∀ R ∈ Ioo (0 : ℝ) 1, ∀ z ∈ sourceCylinder R, |v z| ≤
        K * max (1 / R) (max (treeRadiusMajorant B p 1) (defectScale E₁ E₂ E₃)) := by
  obtain ⟨K, hK, hb⟩ := augmented_radius_uniform_on p hC hc hc₁ hp
  refine ⟨2 * K, by positivity, ?_⟩
  intro v hv B hB E₁ E₂ E₃ h₁ h₂ h₃ hmax
  apply extend_radius_bound v hK.le
    (le_max_of_le_left (treeRadiusMajorant_nonneg B p (by norm_num) hB))
  intro R hR z hz
  exact (abs_le_sourceSup_on hv hR.1.le hz).trans
    (hb v hv B hB E₁ E₂ E₃ h₁ h₂ h₃ hmax R hR)

/-- The iteration on v=u-J, using exactly local smoothness of u near P-bar
and global smoothness of J. No extension or global regularity of u is required.
The estimate constant precedes u,J and all the numerical norms. -/
theorem local_remainder_radius_iteration {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) {C c : ℝ} (hC : 1 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1)
    (hp : ∀ i, 0 < p i) :
    ∃ K > 0, ∀ (u J : ParabolicSpace → ℝ),
      (∃ O : Set ParabolicSpace, IsOpen O ∧ closure (sourceCylinder 0) ⊆ O ∧
        ContDiffOn ℝ ∞ u O) → ContDiff ℝ ∞ J →
      ∀ (B : I → ℝ), (∀ i, 0 ≤ B i) → ∀ E₁ E₂ E₃,
      0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ →
      RadiusInteriorRow (fun z => u z - J z) B p C c E₁ E₂ E₃ →
      ∀ R ∈ Ioo (0 : ℝ) 1, ∀ z ∈ sourceCylinder R, |u z - J z| ≤
        K * max (1 / R) (max (treeRadiusMajorant B p 1) (defectScale E₁ E₂ E₃)) := by
  obtain ⟨K, hK, hb⟩ := augmented_radius_on_all p hC hc hc₁ hp
  refine ⟨K, hK, ?_⟩
  intro u J hu hJ
  exact hb (fun z => u z - J z)
    (remainder_continuousOn_closed u J hu hJ.continuous.continuousOn)

end GlobalPhi43.Local
