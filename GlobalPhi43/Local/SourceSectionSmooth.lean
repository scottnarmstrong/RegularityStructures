/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SourceSectionHeat
public import GlobalPhi43.Local.SmoothLocalAverage

/-! Infinity-smoothness of the actual smoothed source section, derived
from the original source smoothness and the existing compact testing tube. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff

 theorem source_section_contDiffAt_infty (U : GermPoint → ℝ) {r : ℝ}
    (hU : ∃ O : Set GermPoint, IsOpen O ∧
      closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O)
    {x y : ParabolicSpace} (hx : x ∈ closure (sourceCylinder r))
    (hy : y ∈ closure (sourceCylinder r)) : ContDiffAt ℝ ∞ (fun z => U (x, z)) y := by
  obtain ⟨O, hO, hKO, hs⟩ := hU
  exact (hs.contDiffAt (hO.mem_nhds (hKO ⟨hx, hy⟩))).comp y
    (contDiffAt_const.prodMk contDiffAt_id)

end GlobalPhi43.Local
