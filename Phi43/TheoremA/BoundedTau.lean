/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The lifetime defined from boundedness alone

The lifetime is defined from boundedness at countably many rational times alone, so that it is
measurable. The Cauchy property is supplied separately on the full-measure good set by the stopped
continuity of classical solutions and the convergence of the G-models, so it does not enter the
definition of the lifetime.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

local instance assemblyBoundedTauPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def assemblyRationalBoundedPathEvent (q : ℚ) (L : ℕ)
    {Ω : Type*} {η : NegExponent} (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) : Prop :=
  let _ := hcont
  0 < (q : ℝ) ∧ ∀ n : ℕ, ∀ r : ℚ, r ∈ Icc (0 : ℚ) q →
    ‖x n ω (r : ℝ)‖ ≤ (L : ℝ)

def assemblyBoundedTau {Ω : Type*} {η : NegExponent} (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) : ℝ≥0∞ :=
  if ∃ q : ℚ, ∃ L : ℕ, assemblyRationalBoundedPathEvent q L x hcont ω then
    ⨆ q : ℚ, ⨆ L : ℕ,
      if assemblyRationalBoundedPathEvent q L x hcont ω then
        ENNReal.ofReal (q : ℝ) else 0
  else ⊤

end RegularityStructures.Phi43

end

end

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyRationalBoundedPathEvent_measurableSet
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent} (q : ℚ) (L : ℕ)
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) :
    MeasurableSet {ω | assemblyRationalBoundedPathEvent q L x hcont ω} := by
  by_cases hq : 0 < (q : ℝ)
  · simp only [assemblyRationalBoundedPathEvent, hq, true_and]
    rw [show {ω | ∀ n : ℕ, ∀ r : ℚ, r ∈ Icc (0 : ℚ) q →
        ‖x n ω (r : ℝ)‖ ≤ (L : ℝ)} =
      ⋂ n : ℕ, ⋂ r : ℚ,
        {ω | r ∈ Icc (0 : ℚ) q → ‖x n ω (r : ℝ)‖ ≤ (L : ℝ)} by
      ext ω
      simp]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun r => ?_
    by_cases hr : r ∈ Icc (0 : ℚ) q
    · have hr0 : 0 ≤ (r : ℝ) := by exact_mod_cast hr.1
      simpa [hr] using measurableSet_le
        ((continuous_norm.measurable.comp (hmeas n (r : ℝ) hr0))) measurable_const
    · simp [hr]
  · simp only [assemblyRationalBoundedPathEvent, hq, false_and]
    exact MeasurableSet.empty

theorem assemblyBoundedTau_measurable
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) :
    Measurable (assemblyBoundedTau x hcont) := by
  classical
  have hA (q : ℚ) (L : ℕ) : MeasurableSet
      {ω | assemblyRationalBoundedPathEvent q L x hcont ω} :=
    assemblyRationalBoundedPathEvent_measurableSet q L x hcont hmeas
  have hpiece (q : ℚ) (L : ℕ) : Measurable (fun ω =>
      if assemblyRationalBoundedPathEvent q L x hcont ω then
        ENNReal.ofReal (q : ℝ) else 0) :=
    Measurable.ite (hA q L) measurable_const measurable_const
  have hraw : Measurable (fun ω =>
      ⨆ q : ℚ, ⨆ L : ℕ,
        if assemblyRationalBoundedPathEvent q L x hcont ω then
          ENNReal.ofReal (q : ℝ) else 0) := by
    exact Measurable.iSup fun q => Measurable.iSup fun L => hpiece q L
  have hexists : MeasurableSet
      {ω | ∃ q : ℚ, ∃ L : ℕ, assemblyRationalBoundedPathEvent q L x hcont ω} := by
    rw [show {ω | ∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω} =
      ⋃ q : ℚ, ⋃ L : ℕ,
        {ω | assemblyRationalBoundedPathEvent q L x hcont ω} by
      ext ω
      simp]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun L => hA q L
  rw [show assemblyBoundedTau x hcont = fun ω =>
      if ∃ q : ℚ, ∃ L : ℕ, assemblyRationalBoundedPathEvent q L x hcont ω then
        ⨆ q : ℚ, ⨆ L : ℕ,
          if assemblyRationalBoundedPathEvent q L x hcont ω then
            ENNReal.ofReal (q : ℝ) else 0
      else ⊤ by
    funext ω
    simp only [assemblyBoundedTau]]
  exact Measurable.ite hexists hraw measurable_const

theorem assemblyBoundedTau_pos
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) :
    0 < assemblyBoundedTau x hcont ω := by
  classical
  by_cases h : ∃ q : ℚ, ∃ L : ℕ,
      assemblyRationalBoundedPathEvent q L x hcont ω
  · obtain ⟨q, L, hq⟩ := h
    have h_exists : ∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω := ⟨q, L, hq⟩
    have hle : ENNReal.ofReal (q : ℝ) ≤ assemblyBoundedTau x hcont ω := by
      rw [show assemblyBoundedTau x hcont ω =
          ⨆ q : ℚ, ⨆ L : ℕ,
            if assemblyRationalBoundedPathEvent q L x hcont ω then
              ENNReal.ofReal (q : ℝ) else 0 by
        simp [assemblyBoundedTau, h_exists]]
      exact le_iSup_of_le q (le_iSup_of_le L (by simp [hq]))
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hq.1) hle
  · simp [assemblyBoundedTau, h]

theorem assemblyRationalBoundedPathEvent_bound
    {Ω : Type*} {η : NegExponent} (q : ℚ) (L : ℕ)
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    (hE : assemblyRationalBoundedPathEvent q L x hcont ω) :
    ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (q : ℝ), ‖x n ω t‖ ≤ (L : ℝ) := by
  intro n t ht
  let f : ℝ → ℝ := fun s => ‖x n ω s‖
  have hf : ContinuousWithinAt f (Ici (0 : ℝ)) t := by
    exact continuous_norm.continuousAt.comp_continuousWithinAt
      (hcont n ω t ht.1)
  have hrat : ∀ r : ℚ, r ∈ Icc (0 : ℚ) q → f (r : ℝ) ≤ (L : ℝ) := by
    intro r hr
    exact hE.2 n r hr
  by_contra hnot
  have hLt : (L : ℝ) < f t := lt_of_not_ge hnot
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousWithinAt_iff.1 hf)
    (f t - (L : ℝ)) (sub_pos.mpr hLt)
  by_cases ht0 : t = 0
  · subst t
    have hzero := hrat 0 (by
      constructor
      · norm_num
      · exact_mod_cast hE.1.le)
    exact (not_lt_of_ge hzero) (by simpa using hLt)
  by_cases htq : t = (q : ℝ)
  · subst t
    have hqrat := hrat q (by
      constructor
      · exact_mod_cast hE.1.le
      · rfl)
    exact (not_lt_of_ge hqrat) hLt
  have ht0' : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htq' : t < (q : ℝ) := lt_of_le_of_ne ht.2 htq
  let d : ℝ := min (t / 2) (min (((q : ℝ) - t) / 2) (δ / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (div_pos ht0' (by norm_num))
      (lt_min (div_pos (sub_pos.mpr htq') (by norm_num))
        (div_pos hδ (by norm_num)))
  obtain ⟨r, hrl, hrr⟩ := exists_rat_btwn (show t - d < t + d by linarith)
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by
    have htd : 0 < t - d := by
      have hd' : d ≤ t / 2 := min_le_left _ _
      linarith
    linarith
  have hrq : (r : ℝ) ≤ (q : ℝ) := by
    have hd' : d ≤ ((q : ℝ) - t) / 2 :=
      (min_le_right (t / 2) _).trans (min_le_left _ _)
    linarith
  have hrδ : dist (r : ℝ) t < δ := by
    rw [Real.dist_eq]
    apply (abs_lt).2
    have hdδ : d ≤ δ / 2 :=
      (min_le_right (t / 2) _).trans (min_le_right _ _)
    constructor <;> linarith
  have hfr := hclose (show (r : ℝ) ∈ Ici (0 : ℝ) from hr0) hrδ
  have hfr' : |f (r : ℝ) - f t| < f t - (L : ℝ) := by
    simpa only [Real.dist_eq] using hfr
  have hfrL : (L : ℝ) < f (r : ℝ) := by
    have hlow := (abs_lt.mp hfr').1
    linarith
  have hr0q : (0 : ℚ) ≤ r := by exact_mod_cast hr0
  have hrqq : r ≤ q := by exact_mod_cast hrq
  exact (not_lt_of_ge (hrat r ⟨hr0q, hrqq⟩)) hfrL

end RegularityStructures.Phi43

end
