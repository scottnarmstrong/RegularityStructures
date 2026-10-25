/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondProfile
public import Phi43.BPHZ.ProductIPsiPsiSecondPeriodise
import Mathlib.Tactic

/-!
# From `ℝ⁴ × ℝ⁴` to the profile double integrals

For `h = ipsiWeightedKernel t x` with periodisation `g(u) = ∑_k h(lift_k u)`, a nonneg measurable
`Θ` on `(ℝ × T³)²` for which `|g| |g'| Θ` is integrable on `(ℝ × T³)²`,
`∫_{ℝ⁴ × ℝ⁴} h(y) h(y') Θ(proj y, proj y') = ∫_{(ℝ × T³)²} |g(u)| |g(v)| Θ(u, v)`, with
integrable left-hand integrand (`ipsiWeighted_integral_comp_proj`).
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

/-- The periodisation of the weighted kernel. -/
def ipsiWeightedPeriodised (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, ipsiWeightedKernel t x (u.1, torusRep u.2 + fun i => (k i : ℝ))

end RegularityStructures

end

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem measurable_ipsiWeightedPeriodised (t : ℝ) (x : ParabolicSpace) :
    Measurable (ipsiWeightedPeriodised t x) :=
  Measurable.tsum fun _ => (measurable_ipsiWeightedKernel t x).comp
    (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))

theorem ipsiWeightedPeriodised_nonneg (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) :
    0 ≤ ipsiWeightedPeriodised t x u :=
  tsum_nonneg fun _ => ipsiWeightedKernel_nonneg _ _ _

theorem ofReal_ipsiWeightedPeriodised {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ParabolicSpace)
    (u : SpaceTime) :
    ENNReal.ofReal (ipsiWeightedPeriodised t x u) =
      periodiseENN (fun y => ENNReal.ofReal (ipsiWeightedKernel t x y)) u := by
  obtain ⟨B, hB0, hB⟩ := exists_ipsiWeightedKernel_lattice_sum_le
  have hs := (hB ht ht1 x u).1
  have hs' : Summable (fun k : Fin 3 → ℤ =>
      ipsiWeightedKernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ))) := by
    refine hs.congr fun k => ?_
    exact abs_of_nonneg (ipsiWeightedKernel_nonneg _ _ _)
  unfold ipsiWeightedPeriodised periodiseENN
  exact ENNReal.ofReal_tsum_of_nonneg (fun k => ipsiWeightedKernel_nonneg _ _ _) hs'

/-- **Transfer of a periodised double integral.** -/
theorem ipsiWeighted_integral_comp_proj {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ParabolicSpace)
    {Θ : SpaceTime → SpaceTime → ℝ} (hΘm : Measurable (fun w : SpaceTime × SpaceTime => Θ w.1 w.2))
    (hΘ0 : ∀ u v, 0 ≤ Θ u v)
    (hI : Integrable (fun w : SpaceTime × SpaceTime =>
      ipsiWeightedPeriodised t x w.1 * ipsiWeightedPeriodised t x w.2 * Θ w.1 w.2)) :
    Integrable (fun q : ParabolicSpace × ParabolicSpace => ipsiWeightedKernel t x q.1 *
      ipsiWeightedKernel t x q.2 * Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) ∧
    ∫ q : ParabolicSpace × ParabolicSpace, ipsiWeightedKernel t x q.1 *
      ipsiWeightedKernel t x q.2 * Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2) =
    ∫ w : SpaceTime × SpaceTime,
      ipsiWeightedPeriodised t x w.1 * ipsiWeightedPeriodised t x w.2 * Θ w.1 w.2 := by
  set h := ipsiWeightedKernel t x with hh
  have hφ : Measurable (fun y => ENNReal.ofReal (h y)) :=
    (measurable_ipsiWeightedKernel t x).ennreal_ofReal
  have hΨ : Measurable (fun w : SpaceTime × SpaceTime => ENNReal.ofReal (Θ w.1 w.2)) :=
    hΘm.ennreal_ofReal
  have key := lintegral_prod_comp_proj_periodise hφ (Ψ := fun u v => ENNReal.ofReal (Θ u v)) hΨ
  have hn := ipsiWeightedKernel_nonneg t x
  have hg0 := ipsiWeightedPeriodised_nonneg t x
  have eL : ∀ q : ParabolicSpace × ParabolicSpace,
      ENNReal.ofReal (h q.1) * ENNReal.ofReal (h q.2) *
        ENNReal.ofReal (Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) =
      ENNReal.ofReal (h q.1 * h q.2 *
        Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) := fun q => by
    rw [ENNReal.ofReal_mul (mul_nonneg (hn _) (hn _)), ENNReal.ofReal_mul (hn _)]
  have eR : ∀ w : SpaceTime × SpaceTime,
      periodiseENN (fun y => ENNReal.ofReal (h y)) w.1 *
        periodiseENN (fun y => ENNReal.ofReal (h y)) w.2 * ENNReal.ofReal (Θ w.1 w.2) =
      ENNReal.ofReal (ipsiWeightedPeriodised t x w.1 * ipsiWeightedPeriodised t x w.2 *
        Θ w.1 w.2) := fun w => by
    rw [← ofReal_ipsiWeightedPeriodised ht ht1, ← ofReal_ipsiWeightedPeriodised ht ht1,
      ENNReal.ofReal_mul (mul_nonneg (hg0 _) (hg0 _)), ENNReal.ofReal_mul (hg0 _)]
  simp_rw [eL, eR] at key
  have hRnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 * Θ w.1 w.2 := fun w =>
    mul_nonneg (mul_nonneg (hg0 _) (hg0 _)) (hΘ0 _ _)
  have hLnn : ∀ q : ParabolicSpace × ParabolicSpace, 0 ≤ h q.1 * h q.2 *
      Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2) := fun q =>
    mul_nonneg (mul_nonneg (hn _) (hn _)) (hΘ0 _ _)
  have hLm : Measurable (fun q : ParabolicSpace × ParabolicSpace => h q.1 * h q.2 *
      Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) := by
    have hp : Measurable (fun q : ParabolicSpace × ParabolicSpace =>
        (Phi43.spaceTimeProj q.1, Phi43.spaceTimeProj q.2)) :=
      (Phi43.continuous_spaceTimeProj.measurable.comp measurable_fst).prodMk
        (Phi43.continuous_spaceTimeProj.measurable.comp measurable_snd)
    have h1 : Measurable (fun q : ParabolicSpace × ParabolicSpace => h q.1 * h q.2) :=
      ((measurable_ipsiWeightedKernel t x).comp measurable_fst).mul
        ((measurable_ipsiWeightedKernel t x).comp measurable_snd)
    exact h1.mul (Measurable.comp (g := fun w : SpaceTime × SpaceTime => Θ w.1 w.2)
      (f := fun q : ParabolicSpace × ParabolicSpace =>
        (Phi43.spaceTimeProj q.1, Phi43.spaceTimeProj q.2)) hΘm hp)
  have hRfin : ∫⁻ w : SpaceTime × SpaceTime, ENNReal.ofReal (ipsiWeightedPeriodised t x w.1 *
      ipsiWeightedPeriodised t x w.2 * Θ w.1 w.2) =
      ENNReal.ofReal (∫ w : SpaceTime × SpaceTime, ipsiWeightedPeriodised t x w.1 *
        ipsiWeightedPeriodised t x w.2 * Θ w.1 w.2) :=
    (ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall hRnn)).symm
  have hLi : Integrable (fun q : ParabolicSpace × ParabolicSpace => h q.1 * h q.2 *
      Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) := by
    refine ⟨hLm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hLnn)).2 ?_⟩
    have : ∫⁻ q : ParabolicSpace × ParabolicSpace, ENNReal.ofReal (h q.1 * h q.2 *
        Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) < ⊤ := by
      rw [key, hRfin]; exact ENNReal.ofReal_lt_top
    exact this
  refine ⟨hLi, ?_⟩
  have h1 : ENNReal.ofReal (∫ q : ParabolicSpace × ParabolicSpace, h q.1 * h q.2 *
      Θ (Phi43.spaceTimeProj q.1) (Phi43.spaceTimeProj q.2)) =
      ENNReal.ofReal (∫ w : SpaceTime × SpaceTime, ipsiWeightedPeriodised t x w.1 *
        ipsiWeightedPeriodised t x w.2 * Θ w.1 w.2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hLi (Filter.Eventually.of_forall hLnn), key, hRfin]
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hLnn)
    (integral_nonneg hRnn)).1 h1

end RegularityStructures

end
