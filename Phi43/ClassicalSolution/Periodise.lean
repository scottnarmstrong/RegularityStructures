/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import RegularityStructures.Torus.HeatKernelFacts

/-!
# Elementary support facts for the periodised mollifier

The compact support in the time coordinate survives parabolic rescaling and spatial
periodisation. These are the support facts about the periodised mollifier `ρ_ε^♯` of Definition 2.3; smoothness and
boundedness of the infinite spatial sum require the corresponding locally finite-series argument.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem measurable_periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} :
    Measurable (periodise ρ ε) := by
  have hρm : Measurable ρ := hρ.contDiff.continuous.measurable
  have hrescale : Measurable (rescale ρ ε) := by
    unfold rescale
    apply measurable_const.mul
    apply hρm.comp
    exact (measurable_const.mul measurable_fst).prodMk
      (measurable_snd.const_smul ε⁻¹)
  unfold periodise
  apply Measurable.tsum
  intro k
  convert hrescale.comp
      (measurable_fst.prodMk
        ((RegularityStructures.measurable_torusRep.comp measurable_snd).add measurable_const))
    using 1 <;> rfl

theorem periodise_eq_zero_outside_time_interval
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℝ, ∀ z : SpaceTime, z.1 < a ∨ b < z.1 → periodise ρ ε z = 0 := by
  have hK : IsCompact (tsupport ρ) := hρ.hasCompactSupport
  have hupper : BddAbove ((fun q : ℝ × (Fin 3 → ℝ) => q.1) '' tsupport ρ) :=
    (hK.image continuous_fst).bddAbove
  have hlower : BddBelow ((fun q : ℝ × (Fin 3 → ℝ) => q.1) '' tsupport ρ) :=
    (hK.image continuous_fst).bddBelow
  rcases hupper with ⟨A, hA⟩
  rcases hlower with ⟨B, hB⟩
  let scale : ℝ := ε ^ (-2 : ℤ)
  have hscale : 0 < scale := zpow_pos hε _
  refine ⟨B / scale, A / scale, ?_⟩
  intro z hz
  have hzero : ∀ k : Fin 3 → ℤ,
      rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ)) = 0 := by
    intro k
    unfold rescale
    have hq :
        (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • (torusRep z.2 + fun i => (k i : ℝ))) ∉
          tsupport ρ := by
      intro hq
      have htime : ε ^ (-2 : ℤ) * z.1 ∈
          ((fun q : ℝ × (Fin 3 → ℝ) => q.1) '' tsupport ρ) :=
        ⟨(ε ^ (-2 : ℤ) * z.1, ε⁻¹ • (torusRep z.2 + fun i => (k i : ℝ))), hq, rfl⟩
      have hscale_eq : ε ^ (-2 : ℤ) = scale := rfl
      rcases hz with hz | hz
      · have htime_lt : ε ^ (-2 : ℤ) * z.1 < B := by
          rw [hscale_eq]
          calc
            scale * z.1 < scale * (B / scale) := mul_lt_mul_of_pos_left hz hscale
            _ = B := by field_simp
        exact (not_lt_of_ge (hB htime)) htime_lt
      · have htime_lt : A < ε ^ (-2 : ℤ) * z.1 := by
          rw [hscale_eq]
          calc
            A = scale * (A / scale) := by field_simp
            _ < scale * z.1 := mul_lt_mul_of_pos_left hz hscale
        exact (not_lt_of_ge (hA htime)) htime_lt
    rw [image_eq_zero_of_notMem_tsupport hq, mul_zero]
  simp [periodise, hzero]

end RegularityStructures.Phi43

end
