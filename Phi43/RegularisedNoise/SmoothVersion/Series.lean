/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Deterministic
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth series on space-time

This module isolates the deterministic series step in the smooth-modification argument.  The
probabilistic argument uses it after supplying a countable Fourier expansion and uniform bounds
for all iterated derivatives.  The statement is deliberately independent of the periodisation of
the mollifier.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures.Phi43

theorem isSmoothOnSpaceTime_tsum_of_derivative_bounds {ι : Type*} [Countable ι]
    {f : ι → SpaceTime → ℝ} {v : ℕ → ι → ℝ}
    (hf : ∀ i, IsSmoothOnSpaceTime (f i))
    (hv : ∀ k, Summable (v k))
    (hbound : ∀ (k : ℕ) (i : ι) (p : ℝ × (Fin 3 → ℝ)),
      ‖iteratedFDeriv ℝ k (fun q => f i (q.1, torusProj q.2)) p‖ ≤ v k i) :
    IsSmoothOnSpaceTime (fun z => ∑' i, f i z) := by
  unfold IsSmoothOnSpaceTime at hf ⊢
  let F : ι → (ℝ × (Fin 3 → ℝ)) → ℝ :=
    fun i p => f i (p.1, torusProj p.2)
  have hF : ∀ i, ContDiff ℝ ∞ (F i) := by
    intro i
    simpa [F] using hf i
  have hFbound : ∀ (k : ℕ) (i : ι) (p : ℝ × (Fin 3 → ℝ)),
      ‖iteratedFDeriv ℝ k (F i) p‖ ≤ v k i := by
    intro k i p
    exact hbound k i p
  have hsum : ContDiff ℝ ∞ (fun p => ∑' i, F i p) := by
    apply contDiff_tsum hF (fun k _ => hv k)
    intro k i p hk
    exact hFbound k i p
  simpa [F] using hsum

end RegularityStructures.Phi43

end
