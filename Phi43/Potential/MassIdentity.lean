/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.ConvIntegrable
public import Phi43.Potential.Term3

/-!
# The massive part of `K ∗ ζ` as a Duhamel integral of the slices

For `ζ = f ∘ proj` periodic and `z = (s, xt)`,

  `(ζ ⋆ potMass)(s, xt) = ∫_{s - 1/4}^{s} χ(s - r) e^{-(s-r)} (P_{s-r} f_r)(x) dr`,  `x = proj xt`,

i.e. the evaluation at `x` of the `C(T³)`-valued integral `∫ χ(s - r) • potF s r dr`
(`potConv_potMass_eq`).  Fubini on `ℝ × ℝ³`, then `∫ gauss(τ, y) f_r(x - proj y) dy = P_τ f_r (x)`.
-/

public section

open MeasureTheory Set Filter

namespace RegularityStructures.Potential

open RegularityStructures

theorem potMass_apply {τ : ℝ} (hτ : 0 < τ) (x : Fin 3 → ℝ) :
    potMass (τ, x) = potCutoff τ * Real.exp (-τ) * gaussKernel τ x := by
  simp [potMass, heatKernelR4_of_pos (z := (τ, x)) hτ]

theorem inner_potMass_eq {f : SpaceTime → ℝ} (hf : Continuous f) {ζ : ParabolicSpace → ℝ}
    (hζf : ∀ z : ParabolicSpace, ζ z = f (z.1, torusProj z.2)) (s r : ℝ) (xt : Fin 3 → ℝ) :
    ∫ y₂ : Fin 3 → ℝ, ζ (r, y₂) * potMass (s - r, xt - y₂) =
      if r < s then potCutoff (s - r) * (potF hf s r (torusProj xt)) else 0 := by
  by_cases hr : r < s
  · have hτ : 0 < s - r := by linarith
    simp only [hr, ite_true]
    simp only [potMass_apply hτ]
    have e1 : ∫ y₂ : Fin 3 → ℝ, ζ (r, y₂) * (potCutoff (s - r) * Real.exp (-(s - r)) *
        gaussKernel (s - r) (xt - y₂)) =
        ∫ y : Fin 3 → ℝ, ζ (r, xt - y) * (potCutoff (s - r) * Real.exp (-(s - r)) *
          gaussKernel (s - r) y) := by
      rw [← integral_sub_left_eq_self (μ := (volume : Measure (Fin 3 → ℝ)))
        (fun y₂ : Fin 3 → ℝ => ζ (r, y₂) * (potCutoff (s - r) * Real.exp (-(s - r)) *
          gaussKernel (s - r) (xt - y₂))) xt]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp
    rw [e1]
    have e2 : ∀ y : Fin 3 → ℝ, ζ (r, xt - y) = potSlice hf r (torusProj xt - torusProj y) := by
      intro y
      rw [hζf, potSlice_apply]
      rw [PDE.torusProj_sub]
    simp only [e2]
    simp only [potF, ContinuousMap.smul_apply, smul_eq_mul]
    rw [PDE.heatOp_eq_heatSemigroup hτ, heatSemigroup]
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  · simp only [hr, ite_false]
    have : ∀ y₂ : Fin 3 → ℝ, potMass (s - r, xt - y₂) = 0 := fun y₂ =>
      potMass_eq_zero (Or.inl (by simp; linarith [not_lt.1 hr]))
    simp [this]

/-- **The massive part of `K ∗ ζ` is the Duhamel integral of the slices.** -/
theorem potConv_potMass_eq {f : SpaceTime → ℝ} (hf : Continuous f) {ζ : ParabolicSpace → ℝ}
    (hζf : ∀ z : ParabolicSpace, ζ z = f (z.1, torusProj z.2)) (hζ : Continuous ζ) {Bζ : ℝ}
    (s : ℝ) (hb : ∀ y : ParabolicSpace, s - 1 / 4 ≤ y.1 → y.1 ≤ s → |ζ y| ≤ Bζ)
    (xt : Fin 3 → ℝ) :
    potConv ζ potMass (s, xt) =
      (∫ r in Ioc (s - 1 / 4) s, potCutoff (s - r) • potF hf s r) (torusProj xt) := by
  have hint : Integrable fun y => ζ y * potMass (((s, xt) : ParabolicSpace) - y) :=
    integrable_conv_kernel integrable_potMass (a := 1 / 4)
      (fun w hw => by
        refine ⟨?_, ?_⟩
        · by_contra h; exact hw (potMass_eq_zero (Or.inl (not_le.1 h).le))
        · by_contra h; exact hw (potMass_eq_zero (Or.inr (by linarith [not_le.1 h]))))
      hζ (s, xt) (fun y h1 h2 => hb y (by simpa using h1) (by simpa using h2))
  unfold potConv
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  simp only [Prod.mk_sub_mk]
  simp only [inner_potMass_eq hf hζf]
  have hI : IntegrableOn (fun r : ℝ => potCutoff (s - r) • potF hf s r) (Ioc (s - 1 / 4) s) :=
    (((contDiff_potCutoff_sub s).continuous).smul (continuous_potF hf s)).integrableOn_Ioc
  have h2 := (ContinuousMap.evalCLM ℝ (torusProj xt)).integral_comp_comm hI
  have h3 : (∫ r in Ioc (s - 1 / 4) s, potCutoff (s - r) • potF hf s r) (torusProj xt) =
      ∫ r in Ioc (s - 1 / 4) s, potCutoff (s - r) * potF hf s r (torusProj xt) := by
    have := h2.symm
    simpa using this
  rw [h3, ← integral_indicator measurableSet_Ioc]
  have hae : ∀ᵐ r : ℝ, r ≠ s := compl_mem_ae_iff.2 (measure_singleton s)
  refine integral_congr_ae ?_
  filter_upwards [hae] with r hr
  by_cases h1 : r < s
  · by_cases h2' : s - 1 / 4 < r
    · rw [indicator_of_mem (show r ∈ Ioc (s - 1 / 4) s from ⟨h2', h1.le⟩)]
      simp [h1]
    · rw [indicator_of_notMem (show r ∉ Ioc (s - 1 / 4) s from fun h => h2' h.1)]
      simp [h1, potCutoff_eq_zero (show 1 / 4 ≤ s - r by linarith [not_lt.1 h2'])]
  · have h1' : s < r := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hr)
    rw [indicator_of_notMem (show r ∉ Ioc (s - 1 / 4) s from fun h => by linarith [h.2])]
    simp [h1]

end RegularityStructures.Potential

end
