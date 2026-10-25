/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Measurable compact-path tails

This module contains the countable selection used in the proof of Theorem A.  A tail event
records pairwise uniform closeness of a continuous-map family and a common norm bound.  The
selection lemma is deliberately stated for arbitrary measurable path families, so it does not
encode any stochastic or model-specific information.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures.Phi43

@[expose] def assemblyConvergencePathTail
    {Ω K X : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [LocallyCompactSpace K]
    [NormedAddCommGroup X] [SecondCountableTopology X]
    (p : ℕ → Ω → C(K, X)) (n : ℕ) (r L : ℝ) : Set Ω :=
  {ω | (∀ m, n ≤ m → ∀ k, n ≤ k → dist (p m ω) (p k ω) ≤ r) ∧
    ∀ m, n ≤ m → ‖p m ω‖ ≤ L}

theorem assemblyConvergencePathTail_measurableSet
    {Ω K X : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [LocallyCompactSpace K]
    [NormedAddCommGroup X] [SecondCountableTopology X]
    (p : ℕ → Ω → C(K, X)) (hp : ∀ n, Measurable (p n))
    (n : ℕ) (r L : ℝ) :
    MeasurableSet (assemblyConvergencePathTail p n r L) := by
  have hdist (m k : ℕ) : Measurable (fun ω => dist (p m ω) (p k ω)) :=
    (hp m).dist (hp k)
  have hnorm (m : ℕ) : Measurable (fun ω => ‖p m ω‖) :=
    continuous_norm.measurable.comp (hp m)
  have hpair : MeasurableSet {ω |
      ∀ m, n ≤ m → ∀ k, n ≤ k → dist (p m ω) (p k ω) ≤ r} := by
    rw [show {ω | ∀ m, n ≤ m → ∀ k, n ≤ k → dist (p m ω) (p k ω) ≤ r} =
        ⋂ m : ℕ, ⋂ k : ℕ,
          {ω | n ≤ m → n ≤ k → dist (p m ω) (p k ω) ≤ r} by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro h i j hi hj
        exact h i hi j hj
      · intro h i hi j hj
        exact h i j hi hj]
    refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun k => ?_
    by_cases hm : n ≤ m
    · by_cases hk : n ≤ k
      · simpa [hm, hk] using measurableSet_le (hdist m k) measurable_const
      · simp [hk]
    · simp [hm]
  have hnorm' : MeasurableSet {ω | ∀ m, n ≤ m → ‖p m ω‖ ≤ L} := by
    rw [show {ω | ∀ m, n ≤ m → ‖p m ω‖ ≤ L} =
        ⋂ m : ℕ, {ω | n ≤ m → ‖p m ω‖ ≤ L} by
      ext ω
      simp]
    refine MeasurableSet.iInter fun m => ?_
    by_cases hm : n ≤ m
    · simpa [hm] using measurableSet_le (hnorm m) measurable_const
    · simp [hm]
  exact (hpair.inter hnorm')

theorem assemblyConvergencePathTail_mono_index
    {Ω K X : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [LocallyCompactSpace K]
    [NormedAddCommGroup X] [SecondCountableTopology X]
    (p : ℕ → Ω → C(K, X)) {n m : ℕ} (hnm : n ≤ m) (r L : ℝ) :
    assemblyConvergencePathTail p n r L ⊆
      assemblyConvergencePathTail p m r L := by
  intro ω hω
  change (∀ k, n ≤ k → ∀ l, n ≤ l → dist (p k ω) (p l ω) ≤ r) ∧
    (∀ k, n ≤ k → ‖p k ω‖ ≤ L) at hω
  change (∀ k, m ≤ k → ∀ l, m ≤ l → dist (p k ω) (p l ω) ≤ r) ∧
    (∀ k, m ≤ k → ‖p k ω‖ ≤ L)
  refine ⟨?_, ?_⟩
  · intro k hk l hl
    exact hω.1 k (hnm.trans hk) l (hnm.trans hl)
  · intro k hk
    exact hω.2 k (hnm.trans hk)

theorem assemblyConvergencePathTail_mono_bound
    {Ω K X : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [LocallyCompactSpace K]
    [NormedAddCommGroup X] [SecondCountableTopology X]
    (p : ℕ → Ω → C(K, X)) (n : ℕ) {L L' r : ℝ} (hLL' : L ≤ L') :
    assemblyConvergencePathTail p n r L ⊆
      assemblyConvergencePathTail p n r L' := by
  intro ω hω
  exact ⟨hω.1, fun m hm => (hω.2 m hm).trans hLL'⟩

theorem assemblyConvergencePathTail_exists_index
    {Ω K X : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [CompactSpace K]
    [SecondCountableTopology K] [LocallyCompactSpace K]
    [NormedAddCommGroup X] [SecondCountableTopology X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (p : ℕ → Ω → C(K, X)) (hp : ∀ n, Measurable (p n))
    (r : ℝ) (_hr : 0 < r) (M : ℕ) (α : ℝ) (hα : 0 < α)
    (hcover : A ⊆ ⋃ L : ℕ, ⋃ k : ℕ,
      assemblyConvergencePathTail p (M + k) r (L : ℝ)) :
    ∃ n : ℕ, M ≤ n ∧ ∃ L : ℕ,
      P (A \ assemblyConvergencePathTail p n r (L : ℝ)) < ENNReal.ofReal α := by
  let C : ℕ → Set Ω := fun L => ⋃ k : ℕ,
    assemblyConvergencePathTail p (M + k) r (L : ℝ)
  let D : ℕ → Set Ω := fun L => A \ C L
  have hCmeas : ∀ L, MeasurableSet (C L) := by
    intro L
    exact MeasurableSet.iUnion fun k =>
      assemblyConvergencePathTail_measurableSet p hp (M + k) r (L : ℝ)
  have hDmeas : ∀ L, MeasurableSet (D L) := fun L => hA.diff (hCmeas L)
  have hDanti : Antitone D := by
    intro L L' hLL' ω hω
    change ω ∈ A ∧ ω ∉ C L' at hω
    change ω ∈ A ∧ ω ∉ C L
    refine ⟨hω.1, ?_⟩
    intro hω'
    apply hω.2
    dsimp [C] at hω'
    rcases Set.mem_iUnion.mp hω' with ⟨k, hk⟩
    dsimp [C]
    have hLLr : (L : ℝ) ≤ (L' : ℝ) := by exact_mod_cast hLL'
    exact Set.mem_iUnion.mpr ⟨k, (assemblyConvergencePathTail_mono_bound p (M + k)
      (L := (L : ℝ)) (L' := (L' : ℝ)) (r := r) hLLr) hk⟩
  have hDinter : ⋂ L : ℕ, D L = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    have hωD : ω ∈ D 0 := Set.mem_iInter.mp hω 0
    have hωA : ω ∈ A := hωD.1
    rcases Set.mem_iUnion.mp (hcover hωA) with ⟨L, hL⟩
    rcases Set.mem_iUnion.mp hL with ⟨k, hk⟩
    have hωDL : ω ∈ D L := Set.mem_iInter.mp hω L
    apply hωDL.2
    dsimp [C]
    exact Set.mem_iUnion.mpr ⟨k, hk⟩
  have hDlim : Tendsto (fun L => P (D L)) atTop (𝓝 0) := by
    simpa [Function.comp_def, hDinter] using
      (tendsto_measure_iInter_atTop (fun L => (hDmeas L).nullMeasurableSet)
        hDanti ⟨0, (measure_lt_top P (D 0)).ne⟩)
  have hhalf : 0 < α / 2 := by linarith
  obtain ⟨L, hL⟩ := ((tendsto_order.1 hDlim).2 (ENNReal.ofReal (α / 2))
    (ENNReal.ofReal_pos.mpr hhalf)).exists
  have hDL : P (D L) < ENNReal.ofReal (α / 2) := by
    exact hL
  let C₀ := C L
  let E : ℕ → Set Ω := fun k => C₀ \ assemblyConvergencePathTail p (M + k) r (L : ℝ)
  have hEmeas : ∀ k, MeasurableSet (E k) := by
    intro k
    exact (hCmeas L).diff
      (assemblyConvergencePathTail_measurableSet p hp (M + k) r (L : ℝ))
  have hEanti : Antitone E := by
    intro k k' hkk' ω hω
    change ω ∈ C₀ ∧ ω ∉ assemblyConvergencePathTail p (M + k') r (L : ℝ) at hω
    change ω ∈ C₀ ∧ ω ∉ assemblyConvergencePathTail p (M + k) r (L : ℝ)
    refine ⟨hω.1, ?_⟩
    intro htail
    apply hω.2
    have hkm : M + k ≤ M + k' := Nat.add_le_add_left hkk' M
    exact (assemblyConvergencePathTail_mono_index p (n := M + k)
      (m := M + k') hkm r (L : ℝ)) htail
  have hEinter : ⋂ k : ℕ, E k = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    have hωE : ω ∈ E 0 := Set.mem_iInter.mp hω 0
    have hCmem : ω ∈ C L := hωE.1
    dsimp [C] at hCmem
    rcases Set.mem_iUnion.mp hCmem with ⟨j, hj⟩
    exact (Set.mem_iInter.mp hω j).2 hj
  have hElim : Tendsto (fun k => P (E k)) atTop (𝓝 0) := by
    simpa [Function.comp_def, hEinter] using
      (tendsto_measure_iInter_atTop (fun k => (hEmeas k).nullMeasurableSet)
        hEanti ⟨0, (measure_lt_top P (E 0)).ne⟩)
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hElim).2 (ENNReal.ofReal (α / 2))
    (ENNReal.ofReal_pos.mpr hhalf)).exists
  have hEk : P (E k) < ENNReal.ofReal (α / 2) := by
    simpa [hEinter] using hk
  refine ⟨M + k, Nat.le_add_right M k, L, ?_⟩
  have hsub : A \ assemblyConvergencePathTail p (M + k) r (L : ℝ) ⊆
      D L ∪ E k := by
    intro ω hω
    by_cases hCω : ω ∈ C₀
    · exact Or.inr ⟨hCω, hω.2⟩
    · exact Or.inl ⟨hω.1, hCω⟩
  have hadd : ENNReal.ofReal (α / 2) + ENNReal.ofReal (α / 2) =
      ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_add (le_of_lt hhalf) (le_of_lt hhalf)]
    congr 1
    ring
  calc
    P (A \ assemblyConvergencePathTail p (M + k) r (L : ℝ)) ≤
        P (D L ∪ E k) := measure_mono hsub
    _ ≤ P (D L) + P (E k) := measure_union_le _ _
    _ < ENNReal.ofReal (α / 2) + ENNReal.ofReal (α / 2) :=
      ENNReal.add_lt_add hDL hEk
    _ = ENNReal.ofReal α := hadd

end RegularityStructures.Phi43

end
