/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Continuous-map limits of solution paths

The Holder--Besov completion is complete, hence so is the continuous-map space on a
compact time interval.  This module packages the resulting limit choice for a
Cauchy family of classical paths.
-/

public section

open Set Filter Topology

namespace RegularityStructures.Phi43

noncomputable def assembly_path_limit
    {η : NegExponent} {T : ℝ}
    (x : ℕ → ℝ → HolderBesov η)
    (hcont : ∀ n, ContinuousOn (x n) (Ici (0 : ℝ)))
    (hCauchy : CauchySeq (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n).mono Icc_subset_Ici_self)))) :
    C(Icc (0 : ℝ) T, HolderBesov η) :=
  Classical.choose (cauchySeq_tendsto_of_complete hCauchy)

theorem assembly_path_limit_spec
    {η : NegExponent} {T : ℝ}
    (x : ℕ → ℝ → HolderBesov η)
    (hcont : ∀ n, ContinuousOn (x n) (Ici (0 : ℝ)))
    (hCauchy : CauchySeq (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n).mono Icc_subset_Ici_self)))) :
    Tendsto (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n).mono Icc_subset_Ici_self))) atTop
      (𝓝 (assembly_path_limit x hcont hCauchy)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete hCauchy)

theorem assembly_path_limit_pointwise
    {η : NegExponent} {T : ℝ}
    (x : ℕ → ℝ → HolderBesov η)
    (hcont : ∀ n, ContinuousOn (x n) (Ici (0 : ℝ)))
    (hCauchy : CauchySeq (fun n =>
      ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((hcont n).mono Icc_subset_Ici_self))))
    (t : Icc (0 : ℝ) T) :
    Tendsto (fun n => x n t.1) atTop
      (𝓝 (assembly_path_limit x hcont hCauchy t)) := by
  exact (continuous_eval_const t).continuousAt.tendsto.comp
    (assembly_path_limit_spec x hcont hCauchy)

end RegularityStructures.Phi43

end
