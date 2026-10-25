/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovCore
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Complete-space extension of a Hölder path

The dyadic construction of a Kolmogorov–Chentsov modification first produces a
uniformly Hölder map on a dense countable set.  This module supplies the exact
completion step: a Hölder map into a complete metric space has a uniformly
continuous extension, and the extension agrees with the original map on the
dense set.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {T E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]

theorem dense_holder_extension_tendsto [CompleteSpace E] [T3Space E]
    {s : Set T} (hs : Dense s) {f : s → E} {C r : ℝ≥0}
    (hf : HolderWith C r f) (hr : 0 < r) (x : T) :
    Tendsto f (comap (↑) (𝓝 x)) (𝓝 (hs.extend f x)) := by
  exact hs.extend_spec (hf.uniformContinuous hr) x

theorem dense_holderWith_extend {T' E' : Type*} [PseudoEMetricSpace T']
    [EMetricSpace E'] [CompleteSpace E'] {s : Set T'} (hs : Dense s)
    {f : s → E'} {C r : ℝ≥0} (hf : HolderWith C r f) (hr : 0 < r) :
    HolderWith C r (hs.extend f) := by
  have huc : UniformContinuous (hs.extend f) :=
    hs.uniformContinuous_extend (hf.uniformContinuous hr)
  have hclosed : IsClosed {p : T' × T' |
      edist (hs.extend f p.1) (hs.extend f p.2) ≤
        (C : ℝ≥0∞) * edist p.1 p.2 ^ (r : ℝ)} := by
    apply isClosed_le
    · exact continuous_edist.comp
        ((huc.continuous.comp continuous_fst).prodMk (huc.continuous.comp continuous_snd))
    · exact (ENNReal.continuous_const_mul (by simp)).comp
        (ENNReal.continuous_rpow_const.comp continuous_edist)
  have hdense : Dense {p : T' × T' |
      edist (hs.extend f p.1) (hs.extend f p.2) ≤
        (C : ℝ≥0∞) * edist p.1 p.2 ^ (r : ℝ)} := by
    apply (hs.prod hs).mono
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hxe : hs.extend f x = f ⟨x, hx⟩ := hs.extend_eq (hf.continuous hr) ⟨x, hx⟩
    have hye : hs.extend f y = f ⟨y, hy⟩ := hs.extend_eq (hf.continuous hr) ⟨y, hy⟩
    change edist (hs.extend f x) (hs.extend f y) ≤
      (C : ℝ≥0∞) * edist x y ^ (r : ℝ)
    rw [hxe, hye]
    simpa using hf ⟨x, hx⟩ ⟨y, hy⟩
  intro x y
  change (x, y) ∈ {p : T' × T' |
    edist (hs.extend f p.1) (hs.extend f p.2) ≤
      (C : ℝ≥0∞) * edist p.1 p.2 ^ (r : ℝ)}
  apply hclosed.closure_subset
  rw [hdense.closure_eq]
  exact mem_univ (x, y)

end RegularityStructures

end
