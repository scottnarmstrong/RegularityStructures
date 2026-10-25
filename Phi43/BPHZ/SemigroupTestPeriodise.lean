/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestUnfold
public import Phi43.BPHZ.CanonicalBridgeConvolution
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Periodisation of the semigroup test function

Let `Q_t = parabolicSemigroup.kernel t` on `ℝ⁴`.  For a point `x ∈ ℝ⁴` the *periodised* kernel
`q^♯_t(x, ·) : ℝ × T³ → ℝ` is
`q^♯_t(x, u) = ∑_{k ∈ ℤ³} Q_t(x, (u₀, torusRep u' + k))`.
For a spatially `1`-periodic function `g(y) = G(proj y)` on `ℝ⁴`, with `proj y = (y₀, y' mod ℤ³)`,
`∫_{ℝ⁴} Q_t(x, y) g(y) dy = ∫_{ℝ × T³} q^♯_t(x, u) G(u) du`
(`integral_semigroup_kernel_mul_comp_proj`), with integrability of the right-hand integrand.

The proof unfolds the `ℝ³` integral over the torus slice by slice (`integral_eq_integral_torus_tsum`)
and gets the integrability of the periodised integrand from the `[0, ∞]`-valued unfolding
`lintegral_eq_lintegral_spaceTime_tsum`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The periodised semigroup kernel `q^♯_t(x, u) = ∑_{k ∈ ℤ³} Q_t(x, (u₀, torusRep u' + k))`. -/
def semigroupPeriodised (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, parabolicSemigroup.kernel t x (u.1, torusRep u.2 + fun i => (k i : ℝ))

end RegularityStructures

end

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem spaceTimeProj_semigroup_lift (t : ℝ) (u : Torus3) (k : Fin 3 → ℤ) :
    Phi43.spaceTimeProj (t, torusRep u + fun i => (k i : ℝ)) = (t, u) := by
  refine Prod.ext rfl ?_
  funext i
  have h := congrFun (show torusProj (torusRep u) = u by
    funext j; simp [torusProj, torusRep]) i
  simpa [Phi43.spaceTimeProj, torusProj] using h

/-- The kernel of the parabolic semigroup is the translate `q_t(x - y)` of the parabolic kernel. -/
theorem parabolicSemigroup_kernel_eq (t : ℝ) (x y : ParabolicSpace) :
    parabolicSemigroup.kernel t x y = parabolicKernel t (x - y) := rfl

theorem measurable_parabolicSemigroup_kernel (t : ℝ) (x : ParabolicSpace) :
    Measurable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y) := by
  simp only [parabolicSemigroup_kernel_eq]
  exact (measurable_parabolicKernel t).comp (measurable_const.sub measurable_id)

theorem measurable_semigroupPeriodised (t : ℝ) (x : ParabolicSpace) :
    Measurable (semigroupPeriodised t x) := by
  unfold semigroupPeriodised
  refine Measurable.tsum fun k => ?_
  exact (measurable_parabolicSemigroup_kernel t x).comp
    (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))

/-- **Periodisation of the semigroup test.**  For measurable `G` on `ℝ × T³` such that
`Q_t(x, ·) (G ∘ proj)` is integrable on `ℝ⁴`,
`∫_{ℝ⁴} Q_t(x, y) G(proj y) dy = ∫_{ℝ × T³} q^♯_t(x, u) G(u) du`, and the right-hand integrand is
integrable. -/
theorem integral_semigroup_kernel_mul_comp_proj (t : ℝ) (x : ParabolicSpace) {G : SpaceTime → ℝ}
    (hG : Measurable G)
    (hint : Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * G (Phi43.spaceTimeProj y))) :
    Integrable (fun u : SpaceTime => semigroupPeriodised t x u * G u) ∧
      ∫ y : ParabolicSpace, parabolicSemigroup.kernel t x y * G (Phi43.spaceTimeProj y) =
        ∫ u : SpaceTime, semigroupPeriodised t x u * G u := by
  set H : ParabolicSpace → ℝ := fun y =>
    parabolicSemigroup.kernel t x y * G (Phi43.spaceTimeProj y) with hH
  have hHm : Measurable H :=
    (measurable_parabolicSemigroup_kernel t x).mul
      (hG.comp Phi43.continuous_spaceTimeProj.measurable)
  have hlift : ∀ q : SpaceTime, ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ)) =
      semigroupPeriodised t x q * G q := by
    intro q
    unfold semigroupPeriodised
    rw [← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [hH, spaceTimeProj_semigroup_lift]
  have hHt : Measurable (fun q : SpaceTime =>
      ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
    Measurable.tsum fun k => hHm.comp
      (measurable_fst.prodMk ((measurable_torusRep.comp measurable_snd).add measurable_const))
  have hfin : ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ <
      ⊤ := by
    calc ∫⁻ q : SpaceTime, ‖∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ
        ≤ ∫⁻ q : SpaceTime, ∑' k : Fin 3 → ℤ,
            ‖H (q.1, torusRep q.2 + fun i => (k i : ℝ))‖ₑ :=
          lintegral_mono fun q => enorm_tsum_le_tsum_enorm
      _ = ∫⁻ y : ParabolicSpace, ‖H y‖ₑ :=
          (Phi43.lintegral_eq_lintegral_spaceTime_tsum hHm.enorm).symm
      _ < ⊤ := hint.2
  have hIntT : Integrable (fun u : SpaceTime => semigroupPeriodised t x u * G u) := by
    have h1 : Integrable (fun q : SpaceTime =>
        ∑' k : Fin 3 → ℤ, H (q.1, torusRep q.2 + fun i => (k i : ℝ))) :=
      ⟨hHt.aestronglyMeasurable, hfin⟩
    exact h1.congr (Filter.Eventually.of_forall hlift)
  refine ⟨hIntT, ?_⟩
  have hint' : Integrable H (volume.prod volume : Measure (ℝ × (Fin 3 → ℝ))) := by
    rwa [← Measure.volume_eq_prod]
  have hIntT' : Integrable (fun q : SpaceTime => semigroupPeriodised t x q * G q)
      (volume.prod volume : Measure (ℝ × Torus3)) := by
    rwa [← Measure.volume_eq_prod]
  rw [show (∫ y : ParabolicSpace, H y) = ∫ t' : ℝ, ∫ z : Fin 3 → ℝ, H (t', z) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hint',
    show (∫ u : SpaceTime, semigroupPeriodised t x u * G u) =
      ∫ t' : ℝ, ∫ u : Torus3, semigroupPeriodised t x (t', u) * G (t', u) by
      rw [Measure.volume_eq_prod]; exact integral_prod _ hIntT']
  refine integral_congr_ae ?_
  filter_upwards [hint'.prod_right_ae] with t' ht'
  rw [Phi43.integral_eq_integral_torus_tsum (H := fun z => H (t', z)) ht']
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => hlift (t', u))

end RegularityStructures

end
