/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureAutomaticDuality
public import RegularityStructures.Probability.MalliavinClosureTestAdjoint
public import RegularityStructures.Probability.MalliavinClosureGraphDuality
public import RegularityStructures.Probability.MalliavinClosureClosable
public import RegularityStructures.Probability.MalliavinClosureAutomaticClosable
public import RegularityStructures.Probability.MalliavinClosureBoundedCore
public import RegularityStructures.Probability.MalliavinClosureExtension

/-!
# Closability of the white-noise Malliavin derivative

This aggregator exports the augmented Gaussian duality, smooth finite-rank adjoints, the cylindrical
graph pairing, and closability of the cylindrical derivative: a sequence of cylindrical graph points
converging to `(0, G)` has `G = 0` (`malliavin_derivative_closable`, [HS23, Definition 2.20 and
Remark 2.22]). It also exports the transport of the chain and product rules to the closure.
-/

@[expose] public section

end
