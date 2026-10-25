/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Realising.Measurable

/-!
# Realising models for abstract integration maps

Aggregator for `RegularityStructures.Abstract.Integration.Realising`: the germ `realGerm`
`= ∑_n ⟨Π_x e_i, K^{deg i}_{n;xy}⟩` with its bound (`Germ`), measurability (`Measurable`), the
`Q`-distribution `realReg` (`Reg`), the predicates `RealisesKernel`, `IsPolyCompatible`,
`IsRealising` (`Def`) and the consistency bound at degree `deg i + 2` (`Consistency`).
Reference: [Hai14, Definition 5.9, Remark 5.10], arXiv:1303.5113v4.
-/
