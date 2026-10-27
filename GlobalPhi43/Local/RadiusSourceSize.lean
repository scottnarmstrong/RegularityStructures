/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSectionBounds
public import GlobalPhi43.Local.TimeFreeGeometry
public import GlobalPhi43.MW20.SourceConeEstimate

/-! The exact B_U of the radius-local Schauder estimate, as an extended nonnegative supremum over
radius-truncated source pairs. Its finite allowance is derived locally. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal ContDiff

def radiusSourceUSup (U : GermPoint → ℝ) (r d₀ : ℝ) : ℝ≥0∞ :=
  ⨆ d ∈ Ioc (0 : ℝ) d₀, localTwoPointSup U (cylinderInterior r d) d

theorem radiusSourceUSup_le (U : GermPoint → ℝ) {r d₀ B : ℝ}
    (hbound : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ y ∈ cylinderInterior r d, pdist x y ≤ d → |U (x, y)| ≤ B) :
    radiusSourceUSup U r d₀ ≤ ENNReal.ofReal B := by
  simp only [radiusSourceUSup, localTwoPointSup, iSup_le_iff]
  intro d hd x hx y hy hxy
  exact ENNReal.ofReal_le_ofReal (hbound d hd x hx y hy hxy)

theorem radiusSourceUSup_bound (U : GermPoint → ℝ) {r d₀ d : ℝ}
    (hfinite : radiusSourceUSup U r d₀ ≠ ⊤) (hd : d ∈ Ioc (0 : ℝ) d₀)
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ cylinderInterior r d)
    (hxy : pdist x y ≤ d) : |U (x, y)| ≤ (radiusSourceUSup U r d₀).toReal := by
  have hall : ∀ d ∈ Ioc (0 : ℝ) d₀, localTwoPointSup U (cylinderInterior r d) d ≤
      radiusSourceUSup U r d₀ := by
    simpa only [radiusSourceUSup, iSup_le_iff] using
      (le_rfl : radiusSourceUSup U r d₀ ≤ radiusSourceUSup U r d₀)
  have hn : radiusSourceUSup U r d₀ ≤ ENNReal.ofReal (radiusSourceUSup U r d₀).toReal := by
    rw [ENNReal.ofReal_toReal hfinite]
  exact localTwoPointSup_bound U _ d ENNReal.toReal_nonneg ((hall d hd).trans hn) hx hy hxy

/-- B_U is finite by compactness and local smoothness on closure(D)^2. -/
theorem radiusSourceUSup_ne_top (U : GermPoint → ℝ) {r d₀ : ℝ} (hr : 0 ≤ r)
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) :
    radiusSourceUSup U r d₀ ≠ ⊤ := by
  obtain ⟨O, hO, hKO, hs⟩ := hU
  have hc := (isCompact_closure_sourceCylinder hr).prod (isCompact_closure_sourceCylinder hr)
  have hu : ContinuousOn U (closure (sourceCylinder r) ×ˢ closure (sourceCylinder r)) :=
    hs.continuousOn.mono hKO
  obtain ⟨b, hb⟩ := (hc.image_of_continuousOn hu.abs).bddAbove
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  apply radiusSourceUSup_le U (B := max 0 b)
  intro d hd x hx y hy _
  have hxD := cylinderInterior_mem_domain hd.1.le hx
  have hyD := cylinderInterior_mem_domain hd.1.le hy
  exact (hb ⟨(x, y), ⟨subset_closure hxD, subset_closure hyD⟩, rfl⟩).trans (le_max_right 0 b)

end GlobalPhi43.Local
