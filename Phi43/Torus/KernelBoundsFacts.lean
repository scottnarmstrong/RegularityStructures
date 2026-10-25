/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsBasic
public import Phi43.Torus.KernelBoundsConvolution
public import Phi43.Torus.KernelBoundsCovariance
public import RegularityStructures.Torus.KernelBoundsDerivative
public import RegularityStructures.Torus.KernelBoundsGaussian
public import RegularityStructures.Torus.KernelBoundsGeometry
public import RegularityStructures.Torus.KernelBoundsLargeTime
public import Phi43.Torus.KernelBoundsK3
public import Phi43.Torus.KernelBoundsL1
public import Phi43.Torus.KernelBoundsLocal
public import Phi43.Torus.KernelBoundsMollified
public import Phi43.Torus.KernelBoundsMollifier
public import Phi43.Torus.KernelBoundsPeriodiseL1
public import Phi43.Torus.KernelBoundsShifted
public import RegularityStructures.Torus.KernelBoundsSpatialDerivative
public import RegularityStructures.Torus.KernelBoundsSpatialPeriodisation
public import RegularityStructures.Torus.KernelBoundsSpatialSingularDerivative
public import RegularityStructures.Torus.KernelBoundsParabolicDerivative
public import Phi43.Torus.KernelBoundsSupport
public import Phi43.Torus.KernelBoundsWeighted

/-!
# Torus kernel-bound façade

This module collects the torus parabolic geometry, heat-kernel bounds, mollifier scaling facts, and
the singular estimates for the massive kernel and its covariance.  The short-scale kernel bound is
a bound for the kernels (2.1)--(2.2) of the statement; the covariance
estimate is the bound required for the logarithmically divergent constant `C₂^ε` of Definition 2.5
of the statement.
-/

public section

end
