/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LocalAffineCoefficient
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.Local.FutureRemainder

/-! The actual weighted radius-local norm in the radius-local Schauder estimate. Empty
suprema are zero; infinite values are retained by the extended supremum. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

/-- The exact left side of the radius-compatible Schauder adapter. -/
@[expose] def weightedRadiusAffineSeminorm
    (U : ParabolicSpace × ParabolicSpace → ℝ) (r d₀ γ : ℝ) : ℝ≥0∞ :=
  ⨆ d ∈ Ioc (0 : ℝ) d₀,
    ENNReal.ofReal (d ^ γ) * radiusAffineSeminorm U (cylinderInterior r d) γ d

/-- Any one coefficient field bounds the actual truncated sup-inf-sup norm.
No attainment or finite-infimum hypothesis is needed for this upper bound. -/
theorem radiusAffineSeminorm_le_of_remainder
    (U : ParabolicSpace × ParabolicSpace → ℝ) (D : Set ParabolicSpace)
    (ν : ParabolicSpace → Fin 3 → ℝ) {γ L C : ℝ}
    (hbound : ∀ x ∈ D, ∀ y ∈ D, y ≠ x → pdist x y ≤ L →
      |U (x, y) - spatialLinear (ν x) (y - x)| ≤ C * pdist x y ^ γ) :
    radiusAffineSeminorm U D γ L ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply (iInf_le _ (ν x)).trans
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply iSup_le
  intro hne
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) _)).2
  simpa only [spatialLinear, Prod.snd_sub, Pi.sub_apply] using
    hbound x hx y hy.1 hne hy.2

/-- A normalized pointwise remainder gives the literal weighted conclusion,
with the identical finite allowance on all depths and both time orders. -/
theorem weightedRadiusAffineSeminorm_le
    (U : ParabolicSpace × ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d₀ γ C : ℝ}
    (hbound : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ y ∈ cylinderInterior r d, y ≠ x → pdist x y ≤ d →
      |U (x, y) - spatialLinear (ν x) (y - x)| ≤ C * (pdist x y / d) ^ γ) :
    weightedRadiusAffineSeminorm U r d₀ γ ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  have hp : 0 < d ^ γ := Real.rpow_pos_of_pos hd.1 _
  have hn : radiusAffineSeminorm U (cylinderInterior r d) γ d ≤
      ENNReal.ofReal (C / d ^ γ) := by
    apply radiusAffineSeminorm_le_of_remainder U _ ν
    intro x hx y hy hne hxy
    have hb := hbound d hd x hx y hy hne hxy
    rw [Real.div_rpow (pdist_nonneg x y) hd.1.le] at hb
    convert hb using 1; ring
  calc
    _ ≤ ENNReal.ofReal (d ^ γ) * ENNReal.ofReal (C / d ^ γ) :=
      mul_le_mul le_rfl hn (by positivity) (by positivity)
    _ = ENNReal.ofReal (d ^ γ * (C / d ^ γ)) := by rw [ENNReal.ofReal_mul hp.le]
    _ = ENNReal.ofReal C := by congr 1; field_simp

end GlobalPhi43.Local
