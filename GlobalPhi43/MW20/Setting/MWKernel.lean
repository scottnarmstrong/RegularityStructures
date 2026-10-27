/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.MWKernelSeq
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Defs.Filter

/-!
# `GlobalPhi43.mwKernel`

The MW20 kernel `Ψ_T`. Source: MW20 §2.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The MW20 test kernel `Ψ_T = lim_{n→∞} Ψ_{T,n}`, the pointwise limit (MW20 §2.1). The
limit exists for every admissible `Φ` and `T > 0`: the paired characterisation theorem is
`GlobalPhi43.tendsto_mwKernelSeq_mwKernel` (`GlobalPhi43.MW20.Setting.Characterisations`). -/
def mwKernel (Φ : ParabolicSpace → ℝ) (T : ℝ) (z : ParabolicSpace) : ℝ :=
  Filter.limUnder Filter.atTop fun n => mwKernelSeq Φ T n z

end GlobalPhi43

end
