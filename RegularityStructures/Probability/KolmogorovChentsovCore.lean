/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Deterministic ingredients for a Kolmogorov–Chentsov construction

This module records the complete-space and Hölder bookkeeping used by the
probabilistic Kolmogorov–Chentsov argument.  The stochastic input is kept in
ENNReal form: no Bochner integrability is hidden in these lemmas.

The Hölder conventions are those of Mathlib: `HolderOnWith C r f s` means
`edist (f x) (f y) ≤ C * edist x y ^ r` on `s`, and `eHolderNorm` is the
corresponding extended-real seminorm.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {T E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]

/-! ### Complete-space limits -/

theorem holderOnWith_subtype {r C : ℝ≥0} {f : T → E} {s : Set T}
    (h : HolderOnWith C r f s) :
    HolderWith C r (fun x : s => f x) := by
  exact holderOnWith_univ.1 (fun x _ y _ => h x x.property y y.property)

end RegularityStructures

end
