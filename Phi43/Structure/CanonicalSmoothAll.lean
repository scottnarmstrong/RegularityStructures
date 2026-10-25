/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothPolynomial
public import Phi43.Structure.CanonicalSmoothRealisingNoise
public import Phi43.Structure.CanonicalTaylorIntegrationSources
public import Phi43.Structure.CanonicalSmoothTaylorBounds
public import Phi43.Structure.CanonicalSmoothIntegratedBounds
public import Phi43.Structure.CanonicalGlobalDerivativeGrowth

/-!
# Smooth canonical-model results

This module collects the analytic results on the canonical model of a smooth
periodic noise [Hai14, Section 8.2, Proposition 8.27]:

* polynomial admissibility of the smooth canonical model, which is an exact
  identity [Hai14, Definition 5.9];
* the causal realising identity on the noise: the first integrated symbol is
  the convolution of the noise with the kernel;
* the causal Taylor shell identities on every retained integration source
  [Hai14, (8.18)–(8.20)], which use only smoothness and spatial periodicity of
  the noise;
* local parabolic Taylor bounds for smooth functions and the local bound for
  the integrated symbol `I(Ψ)`, ingredients of the compact Gamma bounds;
* derivative growth of all unbased retained trees under an explicit polynomial
  growth bound on the first four iterated derivatives of the noise, the growth
  hypothesis of the weighted framework [Hos25, Definition 2.1].

The growth hypothesis is stronger than the local smoothness hypothesis of
[Hai14, Proposition 8.27]; the compact-test bounds do not use it. The
renormalised model is collected separately in `RenormalisedExtensionAll`.
-/

public section

end
