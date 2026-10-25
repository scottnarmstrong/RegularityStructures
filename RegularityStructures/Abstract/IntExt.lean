/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.IntExt.Measurable

/-!
# Generic model extension by abstract integration

Aggregator for `RegularityStructures.Abstract.IntExt`: the model `M'` on a regularity structure `𝒯'`
containing, for each symbol `d` of a finite set `D` not integrated by `I`, a planted symbol
`new d = 𝓘 d` of degree `deg d + 2` [Hai14, Theorem 5.14, Lemma 5.16, Remark 5.10, (5.17)].

* `Basic`: `IntegrationExtension` (interface), `liftOld`, `restrictOld`, `intExt`, normal form `mkVec`;
* `Gamma`, `Cocycle`: the extended group maps `Γ'` and their algebra (`gammaExt_self`,
  `gammaExt_comp`);
* `Hyp`, `Sector`: the standing hypotheses `IntExtHyp` and the enlarged sector `V ⊔ span D`;
* `Germ`, `Identity`: the planted germs `realRegP M h x d` and `Π_x (I + J(x)) a + ∑ a_d R_x d = Q K ∗ Π_x a`;
* `Pi`, `GammaModel`, `PiGamma`, `Model`: `Π'`, `Γ'`, `Π'_x Γ'_{xy} = Π'_y`, `IntExtHyp.intExtend`;
* `OldSymbols`: old/planted symbol lemmas, polynomial compatibility, `isRealisingP_intExtend`;
* `Bounds`: inherited bounds below the level of the planted symbols;
* `Control`: the bounds of `M'` at level `γ' + 2` from Ext514;
* `Measurable`: `IntExtMeas` (joint measurability of the planted regularisations) from
  `Model.IsJointMeasurable` (`intExtMeas_of_isJointMeasurable`, `intExtendOfJoint`).
-/
