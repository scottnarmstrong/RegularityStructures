/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.MW20.LocalAverageRegularity

/-! All finite orders, and hence infinity-smoothness, of local averages
from smooth germs on the actual compact testing tube. -/
public section

namespace GlobalPhi43.Local

open MeasureTheory Filter Topology Set MW20
open scoped ContDiff

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 theorem contDiffAt_average_on_open_nat (n : ℕ)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContDiffAt ℝ n f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) : ContDiffAt ℝ n (fun z => ∫ y, f (z + y) ∂μ) x := by
  induction n generalizing F with
  | zero =>
    apply contDiffAt_zero.mpr
    refine ⟨U, hU.mem_nhds hx, ?_⟩
    intro z hz
    exact (continuousAt_average_on_open μ f hK hU
      (fun w hw => (hf w hw).continuousAt) htest hz).continuousWithinAt
  | succ n ih =>
    apply (contDiffAt_succ_iff_hasFDerivAt (n := n)).mpr
    refine ⟨fun z => ∫ y, fderiv ℝ f (z + y) ∂μ, ⟨U, hU.mem_nhds hx, ?_⟩, ?_⟩
    · intro z hz
      exact hasFDerivAt_average_on_open μ f hK hU
        (fun w hw => (hf w hw).of_le (by exact_mod_cast Nat.succ_pos n)) htest hz
    · exact ih (fderiv ℝ f)
        (fun w hw => (hf w hw).fderiv_right (m := n) (by simp))

 theorem contDiffAt_average_on_open_infty
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContDiffAt ℝ ∞ f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) : ContDiffAt ℝ ∞ (fun z => ∫ y, f (z + y) ∂μ) x := by
  apply contDiffAt_infty.mpr
  intro n
  exact contDiffAt_average_on_open_nat n μ f hK hU
    (fun w hw => (hf w hw).of_le (by simp)) htest hx

end GlobalPhi43.Local
