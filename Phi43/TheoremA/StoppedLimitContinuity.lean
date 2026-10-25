/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.PathLimit
public import Phi43.TheoremA.StoppedLimitMeasurable
public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuity of the stopped limit

The pointwise stopped limit is continuous before its lifetime whenever the approximating paths
are locally Cauchy as continuous maps on every compact interval contained in that lifetime.
The compact-map limit is identified with the pointwise choice in `assemblyStoppedLimit` by
uniqueness of limits.
-/

public section

open Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyStoppedLimit_continuousOn
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
            ((hcont n ω).mono Icc_subset_Ici_self)))) :
    ∀ ω, ContinuousOn (assemblyStoppedLimit x τ hCauchy ω)
      {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω} := by
  intro ω t ht
  obtain ⟨T, htT, hTτ⟩ : ∃ T : ℝ, t < T ∧ ENNReal.ofReal T < τ ω := by
    rcases eq_top_or_lt_top (τ ω) with htop | hfinite
    · exact ⟨t + 1, by linarith, by simp [htop]
        ⟩
    · have ht' : t < (τ ω).toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal ht.1 hfinite.ne).mp ht.2
      obtain ⟨T, htT, hTτ'⟩ := exists_between ht'
      have hT0' : 0 ≤ T := ht.1.trans htT.le
      exact ⟨T, htT, (ENNReal.ofReal_lt_iff_lt_toReal hT0' hfinite.ne).mpr hTτ'⟩
  have hT0 : (0 : ℝ) ≤ T := ht.1.trans htT.le
  have hwindowT := hwindow ω T hT0 hTτ
  let y : C(Icc (0 : ℝ) T, HolderBesov η) :=
    assembly_path_limit (fun n => x n ω) (fun n => hcont n ω) hwindowT
  let z : ℝ → HolderBesov η := fun s => y (Set.projIcc 0 T hT0 s)
  have hz : Continuous z := y.continuous.comp (continuous_projIcc)
  have hEq : ∀ s ∈ Icc (0 : ℝ) T,
      assemblyStoppedLimit x τ hCauchy ω s = z s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsτ : ENNReal.ofReal s < τ ω := by
      exact (ENNReal.ofReal_mono hs.2).trans_lt hTτ
    have hv : Tendsto (fun n => x n ω s) atTop
        (𝓝 (assemblyStoppedLimit x τ hCauchy ω s)) := by
      have hvalue : assemblyStoppedLimit x τ hCauchy ω s =
          Classical.choose (cauchySeq_tendsto_of_complete (hCauchy ω s hs0 hsτ)) := by
        dsimp [assemblyStoppedLimit]
        split
        · rfl
        · rename_i h
          exact False.elim (h ⟨hs0, hsτ⟩)
      rw [hvalue]
      exact Classical.choose_spec
        (cauchySeq_tendsto_of_complete (hCauchy ω s hs0 hsτ))
    have hy : Tendsto (fun n => x n ω s) atTop
        (𝓝 (y ⟨s, hs⟩)) := by
      simpa only [y] using
        (assembly_path_limit_pointwise (fun n => x n ω) (fun n => hcont n ω)
          hwindowT ⟨s, hs⟩)
    have hvy : assemblyStoppedLimit x τ hCauchy ω s = y ⟨s, hs⟩ :=
      tendsto_nhds_unique hv hy
    change assemblyStoppedLimit x τ hCauchy ω s =
      y (Set.projIcc 0 T hT0 s)
    rw [show Set.projIcc 0 T hT0 s = ⟨s, hs⟩ by
      exact Set.projIcc_of_mem hT0 hs]
    exact hvy
  have hIcc : Icc (0 : ℝ) T ∈
      𝓝[{s | 0 ≤ s ∧ ENNReal.ofReal s < τ ω}] t := by
    apply mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds htT))
    intro s hs
    exact ⟨hs.1.1, hs.2.le⟩
  have heq : (fun s => assemblyStoppedLimit x τ hCauchy ω s) =ᶠ[
      𝓝[{s | 0 ≤ s ∧ ENNReal.ofReal s < τ ω}] t] z := by
    filter_upwards [hIcc] with s hs
    exact hEq s hs
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htT.le⟩
  exact hz.continuousAt.continuousWithinAt.congr_of_eventuallyEq heq (hEq t htIcc)

end RegularityStructures.Phi43

end
