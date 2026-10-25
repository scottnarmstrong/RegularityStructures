/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCore
public import RegularityStructures.Probability.MalliavinClosureGaussianIBP
public import RegularityStructures.Probability.MalliavinClosureSpectralGap
public import RegularityStructures.Probability.MalliavinClosureClosability
public import RegularityStructures.Probability.MalliavinClosureDuality
public import RegularityStructures.Probability.MalliavinClosureCalculus
public import RegularityStructures.Probability.MalliavinClosureLinearity
public import RegularityStructures.Probability.MalliavinClosureSupport
public import RegularityStructures.Probability.MalliavinClosureConcatenation
public import RegularityStructures.Probability.MalliavinClosureLaw
public import RegularityStructures.Probability.MalliavinClosureD1
public import RegularityStructures.Probability.MalliavinClosureRelativeClosability
public import RegularityStructures.Probability.MalliavinClosureDivergenceAlgebra
public import RegularityStructures.Probability.MalliavinClosureDivergence
public import RegularityStructures.Probability.MalliavinClosureGaussianDivergence
public import RegularityStructures.Probability.MalliavinClosureLpCalculus
public import RegularityStructures.Probability.MalliavinClosureNemytskii

/-!
# White-noise Malliavin closure

This aggregator exposes the cylindrical graph, its closed spectral-gap sublevel set, the
finite-dimensional Gaussian duality, the dense-duality closability criterion, and the cylindrical
chain and product rules, including transport across concatenated coordinate lists, and the
standard representation of centred Gaussian vectors, as well as the finite-dimensional
random-test divergence identity.  The
unconditional white-noise test-density instantiation required to
identify every graph-closure point as a single-valued Malliavin derivative is recorded in the
status log and is deliberately not hidden behind a proposition-valued contract.
-/

@[expose] public section

end
