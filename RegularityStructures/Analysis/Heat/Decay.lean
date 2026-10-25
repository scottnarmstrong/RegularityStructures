/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decay.Poly
public import RegularityStructures.Analysis.Heat.Decay.KernelDeriv
public import RegularityStructures.Analysis.Heat.Decay.Estimate
public import RegularityStructures.Analysis.Heat.Decay.Nonpos
public import RegularityStructures.Analysis.Heat.Decay.Kernel
public import RegularityStructures.Analysis.Heat.Decay.Remainder

/-!
# Spatial decay of derivatives of the heat kernel and its smooth remainders (facade)

On bounded time windows `t ≤ T₀`, every derivative `D^k` of

* `heatKernelR4` is `O(|x|^{-2m})` for `|x| ≥ 1` (`exists_abs_lineIter_heatKernelR4_le`),
* `heatRemainder` is `O((1 + |x|²)^{-m})` globally (`exists_abs_lineIter_heatRemainder_le`),
* `annRemainderC N` is `O((1 + |x|²)^{-m})` globally (`exists_abs_lineIter_annRemainderC_le`)

for every `m`.  The causal remainder vanishes with all derivatives for `t ≤ 0`
(`lineIter_multiDirs_annRemainderC_eq_zero`).
-/
