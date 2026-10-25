/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Instances.AddCircle.Real
public import Phi43.Stochastic.StochasticHeatConvergencePathSpace

/-!
# Measurable compact-time path events

The proof of Theorem A uses only the measurable point evaluations supplied by the second half of
item (W5) of Lemma 4.1 of the statement.  On a compact time interval these evaluations assemble
into a measurable continuous-map valued path, so uniform boundedness and the Cauchy condition are
measurable.  This makes the construction of the maximal path measurable.
-/

public section

open MeasureTheory Set Topology

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

private theorem assembly_torus_secondCountable :
    SecondCountableTopology (Torus3) := by
  let hcircle : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
    change IsOpenQuotientMap (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
    exact QuotientAddGroup.isOpenQuotientMap_mk
  let _ : SecondCountableTopology UnitAddCircle := hcircle.secondCountableTopology
  infer_instance

/-- The Holder--Besov path restricted to a compact rational time interval. -/
@[expose] def assemblyPathRestriction (q : ℚ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (n : ℕ) (ω : Ω) :
    C(Icc (0 : ℝ) (q : ℝ), HolderBesov η) :=
  ContinuousMap.mk (fun t => x n ω t.1)
    (continuousOn_iff_continuous_domRestrict.mp
      ((hcont n ω).mono Icc_subset_Ici_self))

omit [MeasurableSpace Ω] in
theorem assemblyPathRestriction_eval (q : ℚ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (n : ℕ) (ω : Ω)
    (t : Icc (0 : ℝ) (q : ℝ)) :
    assemblyPathRestriction q x hcont n ω t = x n ω t.1 :=
  by
    change (ContinuousMap.mk (fun s => x n ω s.1) _) t = x n ω t.1
    rfl

theorem assemblyPathRestriction_measurable (q : ℚ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) (n : ℕ) :
    Measurable (fun ω => assemblyPathRestriction q x hcont n ω) := by
  let _ : SecondCountableTopology (Torus3) := assembly_torus_secondCountable
  let _ : SecondCountableTopology (HolderBesov η) :=
    UniformSpace.secondCountable_of_separable _
  apply ContinuousMap.measurable_iff_eval.2
  intro t
  simpa only [assemblyPathRestriction_eval] using hmeas n t.1 t.2.1

private theorem assembly_cauchy_iff_rational_bounds
    {X : Type*} [PseudoMetricSpace X] {a : ℕ → X} :
    CauchySeq a ↔
      ∀ k : ℕ, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        dist (a n) (a m) < (1 : ℝ) / (k + 1) := by
  constructor
  · intro h k
    rcases Metric.cauchySeq_iff.1 h ((1 : ℝ) / (k + 1)) (by positivity) with ⟨N, hN⟩
    exact ⟨N, fun n m hn hm => hN n hn m hm⟩
  · intro h
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    have hsmall : (1 : ℝ) / (k + 1) < ε := by
      have hk' : (1 : ℝ) / ε < (k : ℝ) := by exact_mod_cast hk
      have hrecip : (1 : ℝ) / (k + 1) < (1 : ℝ) / (1 / ε) := by
        exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
      simpa [one_div_div] using hrecip
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun n m hn hm => ?_⟩
    exact (hN n hn m hm).trans hsmall

theorem assemblyPathUniformBound_measurableSet (q : ℚ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) (L : ℝ) :
    MeasurableSet {ω | ∀ n, ‖assemblyPathRestriction q x hcont n ω‖ ≤ L} := by
  rw [show {ω | ∀ n, ‖assemblyPathRestriction q x hcont n ω‖ ≤ L} =
      ⋂ n : ℕ, {ω | ‖assemblyPathRestriction q x hcont n ω‖ ≤ L} by
    ext ω
    simp]
  refine MeasurableSet.iInter fun n => ?_
  have hm := assemblyPathRestriction_measurable q x hcont hmeas n
  exact measurableSet_le (continuous_norm.measurable.comp hm) measurable_const

theorem assemblyPathCauchy_measurableSet (q : ℚ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) :
    MeasurableSet {ω | CauchySeq (fun n => assemblyPathRestriction q x hcont n ω)} := by
  let _ : SecondCountableTopology (Torus3) := assembly_torus_secondCountable
  let _ : SecondCountableTopology (HolderBesov η) :=
    UniformSpace.secondCountable_of_separable _
  let X : ℕ → Ω → C(Icc (0 : ℝ) (q : ℝ), HolderBesov η) :=
    fun n ω => assemblyPathRestriction q x hcont n ω
  have hX : ∀ n, Measurable (X n) := fun n => by
    simpa [X] using assemblyPathRestriction_measurable q x hcont hmeas n
  have hdist (n m : ℕ) : Measurable (fun ω => dist (X n ω) (X m ω)) :=
    (hX n).dist (hX m)
  have hmeas_kN (k N : ℕ) : MeasurableSet
      {ω | ∀ n m, N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} := by
    rw [show {ω | ∀ n m, N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} =
      ⋂ n : ℕ, ⋂ m : ℕ, {ω | N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} by
      ext ω
      simp]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun m => ?_
    by_cases hn : N ≤ n
    · by_cases hm : N ≤ m
      · simpa [hn, hm] using measurableSet_lt (hdist n m) measurable_const
      · simp [hm]
    · simp [hn]
  have hrat : MeasurableSet {ω | ∀ k : ℕ, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} := by
    rw [show {ω | ∀ k : ℕ, ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} =
      ⋂ k : ℕ, ⋃ N : ℕ, {ω | ∀ n m, N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} by
      ext ω
      simp]
    exact MeasurableSet.iInter fun k => MeasurableSet.iUnion fun N => hmeas_kN k N
  rw [show {ω | CauchySeq (fun n => X n ω)} =
      {ω | ∀ k : ℕ, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
        dist (X n ω) (X m ω) < (1 : ℝ) / (k + 1)} by
    ext ω
    exact assembly_cauchy_iff_rational_bounds]
  exact hrat

end RegularityStructures.Phi43

end
