/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactSmoothExtension
public import GlobalPhi43.Local.HeatOperatorRegularity
public import GlobalPhi43.MW20.ScalarSupNorm

/-! Finiteness of the actual heat supremum is a consequence of source
smoothness near a compact carrier, rather than a source-input certificate. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff

 theorem local_heat_supremum_ne_top {h : ParabolicSpace → ℝ}
    {K O D : Set ParabolicSpace} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hh : ContDiffOn ℝ ∞ h O) (hDK : D ⊆ K) :
    localScalarSup (sourceHeat h) D ≠ ⊤ := by
  obtain ⟨g, hg, _, he⟩ := exists_compact_smooth_extension hK hO hKO hh
  have heq : localScalarSup (sourceHeat h) D = localScalarSup (sourceHeat g) D := by
    unfold localScalarSup
    apply iSup_congr
    intro p
    apply iSup_congr
    intro hp
    rw [sourceHeat_eq_of_eventuallyEq (he p (hDK hp))]
  rw [heq]
  exact localScalarSup_ne_top _ (sourceHeat_contDiff hg).continuous D K hDK hK

end GlobalPhi43.Local
