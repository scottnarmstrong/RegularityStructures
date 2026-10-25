/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.CoordinateDecay
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Periodicity of derivatives

Fourier integration by parts on the spatial circle uses the elementary fact that every derivative
of a smooth periodic lift has the same period.
-/

@[expose] public section

open scoped ContDiff Topology

namespace RegularityStructures.Phi43

theorem periodic_iteratedDeriv_one {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f 1) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) 1 := by
  induction n with
  | zero => simpa using hper
  | succ n ih =>
      intro x
      have hderiv : ∀ y : ℝ,
          HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f y) y := by
        intro y
        have h := (hf.differentiable_iteratedDeriv n
          (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n))).differentiableAt
            (x := y) |>.hasDerivAt
        simpa [iteratedDeriv_succ] using h
      have hshift : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
        simpa using (hasDerivAt_id x).add_const (1 : ℝ)
      have houter : HasDerivAt (iteratedDeriv n f)
          (iteratedDeriv (n + 1) f ((fun y : ℝ => y + 1) x))
          ((fun y : ℝ => y + 1) x) := by
        simpa using hderiv (x + 1)
      have hleft : HasDerivAt
          (iteratedDeriv n f ∘ fun y : ℝ => y + 1)
          ((1 : ℝ) • iteratedDeriv (n + 1) f (x + 1)) x :=
        houter.scomp x hshift
      have hfun : (fun y : ℝ => iteratedDeriv n f (y + 1)) =ᶠ[𝓝 x]
          iteratedDeriv n f := by
        filter_upwards [] with y
        exact ih y
      have hleft' := hleft.congr_of_eventuallyEq hfun.symm
      have hright := hderiv x
      have heq := hleft'.unique hright
      simpa using heq

end RegularityStructures.Phi43

end
