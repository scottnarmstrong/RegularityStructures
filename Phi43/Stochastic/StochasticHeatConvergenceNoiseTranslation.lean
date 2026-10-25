/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoise
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Phi43.Mollifier

/-!
# Time translations of the pinned white-noise family

Haar translation preserves every covariance and hence the literal white-noise
predicate. Translating a smooth regularised noise translates its indexing
family in the opposite direction. These identities allow one fixed Fourier
window to be reused at every integer time in the growth proof for
the convergence of the noise potentials (`phi43Noise_cauchy`) [Hai14, Proposition 9.5].
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem isWhiteNoise_shift_time {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) (a : ℝ) :
    IsWhiteNoise P (fun h => W (fun w => h (w - (a, 0)))) := by
  have hmp : MeasurePreserving (fun w : SpaceTime => w - (a, 0)) volume volume := by
    simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure SpaceTime) (-(a, 0)))
  refine ⟨fun h hh => hW.1 _ (hh.comp_measurePreserving hmp), ?_⟩
  intro n h hh
  have hg := hW.2 n (fun i w => h i (w - (a, 0)))
    (fun i => (hh i).comp_measurePreserving hmp)
  refine ⟨hg.1, hg.2.1, hg.2.2.1, fun i j => ?_⟩
  exact (hg.2.2.2 i j).trans (by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self (fun w : SpaceTime => h i w * h j w) (-(a, 0))))

theorem isRegularisedNoise_shift_time {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    {ρ : (ℝ × (Fin 3 → ℝ)) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ ε ξ) (a : ℝ) :
    IsRegularisedNoise P (fun h => W (fun w => h (w - (a, 0)))) ρ ε
      (fun ω z => ξ ω (z + (a, 0))) := by
  refine ⟨fun ω => ?_, fun z => ⟨(hξ.2 (z + (a, 0))).1, ?_⟩⟩
  · have hsm := hξ.1 ω
    unfold IsSmoothOnSpaceTime at hsm ⊢
    have heq : (fun w : ℝ × (Fin 3 → ℝ) =>
        ξ ω ((w.1, torusProj w.2) + (a, 0))) =
        (fun w : ℝ × (Fin 3 → ℝ) => ξ ω (w.1, torusProj w.2)) ∘
          (fun w => w + (a, 0)) := by
      funext w
      simp only [Function.comp_apply, Prod.fst_add, Prod.snd_add, add_zero]
      change ξ ω (w.1 + a, torusProj w.2 + 0) = ξ ω (w.1 + a, torusProj w.2)
      rw [add_zero]
    rw [heq]
    exact hsm.comp (contDiff_id.add contDiff_const)
  · have heq : (fun w : SpaceTime => mollifierAt ρ ε z (w - (a, 0))) =
        mollifierAt ρ ε (z + (a, 0)) := by
      funext w
      unfold mollifierAt
      congr 1
      abel
    simpa only [heq] using (hξ.2 (z + (a, 0))).2

end RegularityStructures.Phi43

end
