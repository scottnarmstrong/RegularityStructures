/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.PathLimit
public import Phi43.TheoremA.StoppedLimitMeasurable

/-!
# Bounds on compact limits inherited from stopped limits

On an active compact window, the pointwise stopped limit and the continuous-map limit are two
limits of the same approximating sequence.  Uniqueness of limits therefore transfers any bound on
the stopped path to the compact limit used by the continuation argument.
-/

public section

open Filter Topology
open Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyStoppedLimit_windowLimit_bound
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (τ : Ω → ℝ≥0∞)
    (hCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => x n ω t))
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hwindow : ∀ ω T, 0 ≤ T → ENNReal.ofReal T < τ ω →
      CauchySeq (fun n =>
        ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hcont n ω).mono Icc_subset_Ici_self))))
    {ω : Ω} {s : ℝ} (hs : 0 ≤ s)
    (hτ : ENNReal.ofReal s < τ ω)
    {L : ℝ}
    (hv : ∀ t ∈ Icc (0 : ℝ) s,
      ‖assemblyStoppedLimit x τ hCauchy ω t‖ ≤ L) :
    ∀ t : Icc (0 : ℝ) s,
      ‖assembly_path_limit (fun n => x n ω)
        (fun n => hcont n ω)
        (hwindow ω s hs hτ) t‖ ≤ L := by
  intro t
  have htτ : ENNReal.ofReal t.1 < τ ω :=
    (ENNReal.ofReal_mono t.2.2).trans_lt hτ
  have hstop : Tendsto (fun n => x n ω t.1) atTop
      (𝓝 (assemblyStoppedLimit x τ hCauchy ω t.1)) := by
    have hvalue : assemblyStoppedLimit x τ hCauchy ω t.1 =
        Classical.choose (cauchySeq_tendsto_of_complete
          (hCauchy ω t.1 t.2.1 htτ)) := by
      dsimp [assemblyStoppedLimit]
      split
      · rfl
      · rename_i h
        exact False.elim (h ⟨t.2.1, htτ⟩)
    rw [hvalue]
    exact Classical.choose_spec
      (cauchySeq_tendsto_of_complete (hCauchy ω t.1 t.2.1 htτ))
  have hpath := assembly_path_limit_pointwise
    (fun n => x n ω) (fun n => hcont n ω) (hwindow ω s hs hτ) t
  have heq : assemblyStoppedLimit x τ hCauchy ω t.1 =
      assembly_path_limit (fun n => x n ω)
        (fun n => hcont n ω) (hwindow ω s hs hτ) t :=
    tendsto_nhds_unique hstop hpath
  rw [← heq]
  exact hv t.1 t.2

end RegularityStructures.Phi43

end
