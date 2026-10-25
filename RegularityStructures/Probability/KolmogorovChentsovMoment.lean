/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovFinite
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# ENNReal moments of finite dyadic close-pair suprema

The supremum over the bounded-offset neighbours is controlled by a finite
sum.  The proof is deliberately stated with `lintegral`, so no Bochner
integrability is implicit in the Kolmogorov estimate.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
  {P : Measure Ω}

noncomputable def dyadicCloseSup (X : UnitInterval → Ω → E) (n : ℕ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨆ i : Fin (2 ^ n + 1), ⨆ d : Fin 5,
    edist (X (dyadicGridPoint n i) ω)
      (X (dyadicGridPoint n (dyadicNeighbor n i d)) ω)

theorem dyadicCloseSup_lintegral_pow_le {p : ℕ} {q : ℝ} {M : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 0 ≤ q) (X : UnitInterval → Ω → E)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (hpair : ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤
      M * edist s t ^ q) (n : ℕ) :
    ∫⁻ ω, (dyadicCloseSup X n ω) ^ p ∂P ≤
      ((2 ^ n + 1 : ℕ) : ℝ≥0∞) * 5 *
        (M * (ENNReal.ofReal (4 / (2 : ℝ) ^ n)) ^ q) := by
  have hp0 : p ≠ 0 := by omega
  have hpoint : ∀ ω, (dyadicCloseSup X n ω) ^ p ≤
      ∑' z : Fin (2 ^ n + 1) × Fin 5,
        edist (X (dyadicGridPoint n z.1) ω)
          (X (dyadicGridPoint n (dyadicNeighbor n z.1 z.2)) ω) ^ p := by
    intro ω
    rw [dyadicCloseSup, ENNReal.iSup_pow_of_ne_zero hp0]
    refine iSup_le fun i => ?_
    rw [ENNReal.iSup_pow_of_ne_zero hp0]
    exact iSup_le fun d =>
      ENNReal.le_tsum (f := fun z : Fin (2 ^ n + 1) × Fin 5 =>
        edist (X (dyadicGridPoint n z.1) ω)
          (X (dyadicGridPoint n (dyadicNeighbor n z.1 z.2)) ω) ^ p) (i, d)
  calc
    ∫⁻ ω, (dyadicCloseSup X n ω) ^ p ∂P ≤
        ∫⁻ ω, ∑' z : Fin (2 ^ n + 1) × Fin 5,
          edist (X (dyadicGridPoint n z.1) ω)
            (X (dyadicGridPoint n (dyadicNeighbor n z.1 z.2)) ω) ^ p ∂P :=
      lintegral_mono hpoint
    _ = ∑' z : Fin (2 ^ n + 1) × Fin 5, ∫⁻ ω,
        edist (X (dyadicGridPoint n z.1) ω)
          (X (dyadicGridPoint n (dyadicNeighbor n z.1 z.2)) ω) ^ p ∂P := by
      rw [lintegral_tsum]
      intro z
      exact (hmeas _ _).pow_const p
    _ ≤ ∑' z : Fin (2 ^ n + 1) × Fin 5,
        M * (ENNReal.ofReal (4 / (2 : ℝ) ^ n)) ^ q := by
      exact ENNReal.tsum_le_tsum fun z =>
        (hpair _ _).trans <| by
          gcongr
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal
            (dist_dyadicGridPoint_neighbor_le n z.1 z.2)
    _ = ((2 ^ n + 1 : ℕ) : ℝ≥0∞) * 5 *
        (M * (ENNReal.ofReal (4 / (2 : ℝ) ^ n)) ^ q) := by
      simp [mul_assoc, mul_left_comm]

end RegularityStructures

end
