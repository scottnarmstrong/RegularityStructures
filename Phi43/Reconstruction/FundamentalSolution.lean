/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.DuhamelPrinciple
public import Phi43.Reconstruction.HeatPotential
public import Phi43.Potential.HeatEq

/-!
# The heat kernel is a fundamental solution (periodic test functions)

For a smooth space-periodic `ψ` vanishing for `|t| > b` and `L^*ψ = -∂_t ψ - Δ ψ`,
`∫_{ℝ⁴} G(w) (L^*ψ)(w) dw = ψ(0)`, `G = heatKernelR4` (`fundamentalSolution_periodic`).
Proof: `a(s, y) = ψ(T - s, -y)` satisfies `(∂_s - Δ) a = (L^*ψ)(T - s, -y)`, so by the Duhamel
principle `a(T, 0) = ∫₀ᵀ P_{T-s}(L^*ψ)(T - s, -·)(0) ds`, which is the integral above
(`heatPotential_eq_duhamel`).
-/

public section

open Set MeasureTheory RegularityStructures.PDE RegularityStructures.Inhomogeneity
open scoped ContDiff

namespace RegularityStructures.Phi43

/-- The formal adjoint `L^* = -∂_t - Δ` of the heat operator. -/
@[expose] noncomputable def lstar (ψ : ParabolicSpace → ℝ) : ParabolicSpace → ℝ :=
  fun w => -ddv 0 ψ w - ∑ j : Fin 3, ddv j.succ (ddv j.succ ψ) w

theorem perSmooth_lstar {ψ : ParabolicSpace → ℝ} (hψ : PerSmooth ψ) : PerSmooth (lstar ψ) where
  smooth := by
    unfold lstar
    refine (hψ.ddv 0).smooth.neg.sub (ContDiff.sum fun j _ => ?_)
    exact ((hψ.ddv j.succ).ddv j.succ).smooth
  periodic z c hc := by
    unfold lstar
    simp only [(hψ.ddv 0).periodic z c hc, ((hψ.ddv _).ddv _).periodic z c hc]

theorem ddv_reflect {F : ParabolicSpace → ℝ} (hF : Differentiable ℝ F) (τ : ParabolicSpace) (j : Fin 4)
    (z : ParabolicSpace) : ddv j (fun w => F (τ - w)) z = -ddv j F (τ - z) := by
  have h1 : HasFDerivAt (fun w : ParabolicSpace => τ - w) (-(ContinuousLinearMap.id ℝ ParabolicSpace)) z :=
    (hasFDerivAt_id z).const_sub τ
  have h2 := (hF (τ - z)).hasFDerivAt.comp z h1
  simp only [ddv]
  rw [show fderiv ℝ (fun w => F (τ - w)) z =
    (fderiv ℝ F (τ - z)).comp (-ContinuousLinearMap.id ℝ ParabolicSpace) from h2.fderiv]
  simp

theorem ddv_neg {F : ParabolicSpace → ℝ} (j : Fin 4) (z : ParabolicSpace) :
    ddv j (fun w => -F w) z = -ddv j F z := by
  simp [ddv, fderiv_fun_neg]

/-- The reflection `a(z) = ψ(τ - z)` turns `L^*` into `L`: `(∂_t - Δ) a = (L^*ψ)(τ - ·)`. -/
theorem ddv_lstar_reflect {ψ : ParabolicSpace → ℝ} (hψ : ContDiff ℝ ∞ ψ) (τ : ParabolicSpace)
    (z : ParabolicSpace) :
    ddv 0 (fun w => ψ (τ - w)) z - ∑ j : Fin 3, ddv j.succ (ddv j.succ (fun w => ψ (τ - w))) z =
      lstar ψ (τ - z) := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have e1 : ∀ j : Fin 4, ddv j (fun w => ψ (τ - w)) = fun w => -ddv j ψ (τ - w) := by
    intro j; funext w; exact ddv_reflect hd τ j w
  have hdd : ∀ j : Fin 4, Differentiable ℝ (ddv j ψ) := fun j =>
    ((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have e2 : ∀ j : Fin 3, ddv j.succ (ddv j.succ (fun w => ψ (τ - w))) z =
      ddv j.succ (ddv j.succ ψ) (τ - z) := by
    intro j
    rw [e1 j.succ]
    have : ddv j.succ (fun w => -ddv j.succ ψ (τ - w)) z =
        -ddv j.succ (fun w => ddv j.succ ψ (τ - w)) z := ddv_neg (F := fun w => ddv j.succ ψ (τ - w)) _ _
    rw [this, ddv_reflect (hdd j.succ) τ j.succ z]
    simp
  rw [e1 0]
  simp only [e2, lstar]

theorem perSmooth_reflect {F : ParabolicSpace → ℝ} (hF : PerSmooth F) (T : ℝ) :
    PerSmooth (fun z : ParabolicSpace => F (((T, 0) : ParabolicSpace) - z)) where
  smooth := hF.smooth.comp (contDiff_const.sub contDiff_id)
  periodic z c hc := by
    have e : ((T, 0) : ParabolicSpace) - (z.1, z.2 + c) =
        ((((T, 0) : ParabolicSpace) - z).1, (((T, 0) : ParabolicSpace) - z).2 + (-c)) := by
      ext <;> simp [sub_eq_add_neg, add_comm]
    have hc' : torusProj (-c) = 0 := by rw [torusProj_neg, hc, neg_zero]
    show F (((T, 0) : ParabolicSpace) - (z.1, z.2 + c)) = F (((T, 0) : ParabolicSpace) - z)
    rw [e]
    exact hF.periodic _ (-c) hc'

private theorem lstar_eq_zero {ψ : ParabolicSpace → ℝ} {b : ℝ}
    (hs : ∀ w : ParabolicSpace, b < w.1 → ψ w = 0) {w : ParabolicSpace} (hw : b < w.1) :
    lstar ψ w = 0 := by
  have hopen : IsOpen {w : ParabolicSpace | b < w.1} := isOpen_lt continuous_const continuous_fst
  have h1 : ∀ F : ParabolicSpace → ℝ, (∀ w : ParabolicSpace, b < w.1 → F w = 0) →
      ∀ j : Fin 4, ∀ w : ParabolicSpace, b < w.1 → ddv j F w = 0 := by
    intro F hF j w hw
    have : F =ᶠ[nhds w] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hopen.mem_nhds hw) fun w' hw' => hF w' hw'
    simp only [ddv, this.fderiv_eq]
    simp
  unfold lstar
  rw [h1 ψ hs 0 w hw]
  simp only [neg_zero, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact h1 _ (h1 ψ hs j.succ) j.succ w hw

/-- **The heat kernel is a fundamental solution** (space-periodic test functions). -/
theorem fundamentalSolution_periodic {ψ : ParabolicSpace → ℝ} (hψ : PerSmooth ψ) {b : ℝ}
    (hb : 0 ≤ b) (hs : ∀ w : ParabolicSpace, b < |w.1| → ψ w = 0) :
    ∫ w, heatKernelR4 w * lstar ψ w = ψ 0 := by
  set T := b + 1 with hT
  have hT0 : 0 < T := by linarith
  set τ : ParabolicSpace := (T, 0) with hτ
  have hs' : ∀ w : ParabolicSpace, b < w.1 → ψ w = 0 := fun w hw =>
    hs w (by rw [abs_of_pos (by linarith)]; exact hw)
  have ha := perSmooth_reflect hψ T
  have hg := perSmooth_reflect (perSmooth_lstar hψ) T
  set a : ParabolicSpace → ℝ := fun z => ψ (τ - z) with hadef
  set g : ParabolicSpace → ℝ := fun z => lstar ψ (τ - z) with hgdef
  have hag : ∀ z, ddv 0 a z - ∑ j : Fin 3, ddv j.succ (ddv j.succ a) z = g z :=
    fun z => ddv_lstar_reflect hψ.smooth τ z
  have hP := duhamel_principle ha hg hag hT0.le
  have ha0 : forcePath ha 0 = 0 := by
    ext x
    obtain ⟨y, rfl⟩ := torusProj_surjective x
    rw [forcePath_apply]
    simp only [hadef, ContinuousMap.zero_apply]
    refine hs' _ ?_
    simp [hτ, hT]
  have h1 := congrArg (fun F : C(Torus3, ℝ) => F (torusProj 0)) hP
  simp only [ha0, heatOp_zero_right, zero_add] at h1
  rw [forcePath_apply] at h1
  have hτ0 : a (T, 0) = ψ 0 := by
    simp only [hadef, hτ, sub_self]
  rw [hτ0] at h1
  have hB3 := heatPotential_eq_duhamel (forcePath hg) (continuous_forcePath hg) hT0 le_rfl g
    (fun r _ y => (forcePath_apply hg r y).symm) 0
  rw [← h1] at hB3
  rw [← hB3]
  -- the change of variables `u = τ - z`
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]
    refine ⟨?_⟩
    have h := Measure.map_prod_map (volume : Measure ℝ) (volume : Measure (Fin 3 → ℝ))
      (measurable_neg (G := ℝ)) (measurable_neg (G := Fin 3 → ℝ))
    rw [Measure.map_neg_eq_self, Measure.map_neg_eq_self] at h
    exact h.symm
  have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [← integral_sub_left_eq_self (fun u : ParabolicSpace => heatKernelR4 u * lstar ψ u)
    (volume : Measure ParabolicSpace) τ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show heatKernelR4 (τ - z) * lstar ψ (τ - z) = heatKernelR4 ((T, 0) - z) * (timeSlab T).indicator g z
  by_cases hz : z ∈ timeSlab T
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz]
    by_cases h0 : 0 < z.1
    · have hz1 : T < z.1 := by
        by_contra hle
        exact hz ⟨h0, not_lt.1 hle⟩
      rw [heatKernelR4_of_nonpos (by simp [hτ]; linarith)]
      simp
    · rw [lstar_eq_zero hs' (by simp [hτ, hT]; linarith)]

end RegularityStructures.Phi43

end
