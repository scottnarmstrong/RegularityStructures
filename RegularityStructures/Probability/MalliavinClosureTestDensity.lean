/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureGrowth
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

set_option linter.style.haveILetI false

/-!
# Pulling smooth finite-dimensional tests back to white-noise coordinates

The compactly supported smooth functions are dense in finite-dimensional Gaussian `L²`.  This
file records the corresponding pullback approximation through an arbitrary AEMeasurable
coordinate map, with the approximation measured in the probability-space `L²` metric.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace RegularityStructures

theorem malliavin_compact_smooth_pullback_approx
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Ω → (Fin n → ℝ)} (hX : AEMeasurable X P)
    {U : (Fin n → ℝ) → ℝ} (hU : MemLp U 2 (P.map X))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : (Fin n → ℝ) → ℝ,
      HasCompactSupport u ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
        MemLp (fun ω => u (X ω)) 2 P ∧
        eLpNorm (fun ω => U (X ω) - u (X ω)) 2 P < ENNReal.ofReal ε := by
  let μ : Measure (Fin n → ℝ) := P.map X
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  have hdense : Dense {f : Lp ℝ (2 : ENNReal) μ | ∃ g : (Fin n → ℝ) → ℝ,
      f =ᵐ[μ] g ∧ HasCompactSupport g ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (μ := μ) (p := (2 : ENNReal)) (by norm_num)
  obtain ⟨v, hv, hvdist⟩ := hdense.exists_dist_lt (hU.toLp U) hε
  rcases hv with ⟨u, hu_ae, hsupport, hcont⟩
  let huμ : MemLp u 2 μ := hcont.continuous.memLp_of_hasCompactSupport hsupport
  have hv_eq : v = huμ.toLp u := by
    apply Lp.ext
    exact hu_ae.trans huμ.coeFn_toLp.symm
  have hsource : dist (hU.toLp U) (huμ.toLp u) < ε := by
    rw [← hv_eq]
    exact hvdist
  have hUP : MemLp (fun ω => U (X ω)) 2 P := hU.comp_of_map hX
  have huP : MemLp (fun ω => u (X ω)) 2 P := huμ.comp_of_map hX
  have hsource_dist :
      (eLpNorm (⇑(hU.toLp U) - ⇑(huμ.toLp u)) 2 μ).toReal < ε := by
    simpa [Lp.dist_def, μ] using hsource
  have heq_source :
      eLpNorm (⇑(hU.toLp U) - ⇑(huμ.toLp u)) 2 μ =
        eLpNorm (fun x => U x - u x) 2 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hU.coeFn_toLp, huμ.coeFn_toLp] with x hx hy
    simp [hx, hy]
  have hmap : eLpNorm (fun x => U x - u x) 2 μ =
      eLpNorm (fun ω => U (X ω) - u (X ω)) 2 P := by
    simpa [μ, Function.comp_def] using
      (eLpNorm_map_measure
        (g := fun x => U x - u x)
        (hU.aestronglyMeasurable.sub huμ.aestronglyMeasurable) hX)
  have heq_pullback :
      eLpNorm (⇑(hUP.toLp (fun ω => U (X ω))) -
        ⇑(huP.toLp (fun ω => u (X ω)))) 2 P =
        eLpNorm (fun ω => U (X ω) - u (X ω)) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [hUP.coeFn_toLp, huP.coeFn_toLp] with ω hx hy
    simp [hx, hy]
  refine ⟨u, hsupport, hcont, huP, ?_⟩
  rw [← hmap, ← heq_source]
  have hclass :
      eLpNorm (⇑(hU.toLp U - huμ.toLp u)) 2 μ =
        eLpNorm (⇑(hU.toLp U) - ⇑(huμ.toLp u)) 2 μ := by
    apply eLpNorm_congr_ae
    exact Lp.coeFn_sub (hU.toLp U) (huμ.toLp u)
  have hne :
      eLpNorm (⇑(hU.toLp U) - ⇑(huμ.toLp u)) 2 μ ≠ ⊤ := by
    rw [← hclass]
    exact Lp.eLpNorm_ne_top _
  exact (ENNReal.lt_ofReal_iff_toReal_lt hne).2 hsource_dist

end RegularityStructures

end
