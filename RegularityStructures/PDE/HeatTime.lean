/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.PDE.GaussDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# The time derivative of the heat operator

For `g ∈ C(T³, E)` with continuous first and second derivatives `Dg`, `D²g` on the lift, and
`t > 0`, `∂_t P_t g(x) = P_t(Δg)(x)`, where `Δg = Σᵢ D²g(eᵢ, eᵢ)`.

With `P_t g(x) = ∫ γ₁(z) g(x - √t z) dz`, differentiation in `t` gives
`-(2√t)⁻¹ ∫ γ₁(z) Dg(x - √t z) z dz`, and the Gaussian integration by parts
`∫ zᵢ γ₁(z) φ(z) dz = 2 ∫ γ₁(z) ∂ᵢ φ(z) dz` turns this into `∫ γ₁(z) Δg(x - √t z) dz`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Laplacian `Σᵢ D2g(·)ᵢᵢ` of a function with second partial derivatives `D2g`. -/
def torusLap (D2g : C(Torus3, Fin 3 → Fin 3 → E)) : C(Torus3, E) :=
  ⟨fun x => ∑ i : Fin 3, D2g x i i, by fun_prop⟩

end RegularityStructures.PDE

end

public section

open MeasureTheory Real Filter Topology Set

namespace RegularityStructures.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem torusLap_apply (D2g : C(Torus3, Fin 3 → Fin 3 → E)) (x : Torus3) :
    torusLap D2g x = ∑ i : Fin 3, D2g x i i := rfl

/-- **Gaussian integration by parts**: `∫ zᵢ γ₁(z) φ(z) dz = 2 ∫ γ₁(z) ∂ᵢ φ(z) dz` for bounded
`C¹` functions `φ` with bounded derivative. -/
theorem integral_coord_mul_gaussKernel_smul {φ : (Fin 3 → ℝ) → E}
    {φ' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] E} (hφ : ∀ z, HasFDerivAt φ (φ' z) z)
    (hφ'c : Continuous φ') {C C' : ℝ} (hC : ∀ z, ‖φ z‖ ≤ C) (hC' : ∀ z, ‖φ' z‖ ≤ C')
    (i : Fin 3) :
    ∫ z, (z i * gaussKernel 1 z) • φ z = (2 : ℝ) • ∫ z, gaussKernel 1 z • φ' z (Pi.single i 1) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun z => (hφ z).continuousAt
  have hfd : ∀ z, fderiv ℝ φ z = φ' z := fun z => (hφ z).fderiv
  have hγ := differentiable_gaussKernel_one
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := gaussKernel 1) (g := φ) (v := Pi.single i 1) ?_ ?_ ?_
    (fun z _ => hγ z) (fun z _ => (hφ z).differentiableAt)
  · simp_rw [hfd, fderiv_gaussKernel_one_single] at hibp
    have h2 : ∫ z, (z i * gaussKernel 1 z) • φ z =
        (-2 : ℝ) • ∫ z, (-(z i / 2) * gaussKernel 1 z) • φ z := by
      rw [← integral_smul]
      congr 1
      funext z
      rw [smul_smul]
      congr 1
      ring
    rw [h2, hibp, smul_neg, ← neg_smul]
  · -- `∂ᵢγ₁ • φ` is integrable
    simp_rw [fderiv_gaussKernel_one_single]
    refine ((integrable_abs_mul_gaussKernel_one i).mul_const (C / 2)).mono'
      ((((continuous_apply i).div_const 2).neg.mul continuous_gaussKernel_one).smul
        hφc).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_div, abs_two,
      abs_of_nonneg (gaussKernel_one_nonneg z)]
    have := hC z
    have h0 : 0 ≤ |z i| * gaussKernel 1 z := mul_nonneg (abs_nonneg _) (gaussKernel_one_nonneg z)
    calc |z i| / 2 * gaussKernel 1 z * ‖φ z‖ = |z i| * gaussKernel 1 z * ‖φ z‖ / 2 := by ring
      _ ≤ |z i| * gaussKernel 1 z * C / 2 := by gcongr
      _ = |z i| * gaussKernel 1 z * (C / 2) := by ring
  · -- `γ₁ • ∂ᵢφ` is integrable
    simp_rw [hfd]
    refine (integrable_gaussKernel_one.mul_const (C' * ‖(Pi.single i 1 : Fin 3 → ℝ)‖)).mono'
      (continuous_gaussKernel_one.smul (hφ'c.clm_apply continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
    refine mul_le_mul_of_nonneg_left (((φ' z).le_opNorm _).trans ?_) (gaussKernel_one_nonneg z)
    exact mul_le_mul_of_nonneg_right (hC' z) (norm_nonneg _)
  · -- `γ₁ • φ` is integrable
    refine (integrable_gaussKernel_one.mul_const C).mono'
      (continuous_gaussKernel_one.smul hφc).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
    exact mul_le_mul_of_nonneg_left (hC z) (gaussKernel_one_nonneg z)

theorem clm_apply_eq_sum (L : (Fin 3 → ℝ) →L[ℝ] E) (z : Fin 3 → ℝ) :
    L z = ∑ i, z i • L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  congr 1
  funext i
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

/-- The integration-by-parts identity behind `∂_t P_t g = P_t Δg`:
`∫ γ₁(z) ψ(y - √t z)(-(2√t)⁻¹ z) dz = ∫ γ₁(z) Σᵢ ψ'(y - √t z)(eᵢ, eᵢ) dz` when `ψ = Dg` has the
bounded continuous derivative `ψ'`. -/
theorem integral_gaussKernel_smul_deriv_eq {ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] E}
    {ψ' : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E}
    (hψ : ∀ w, HasFDerivAt ψ (ψ' w) w) (hψ'c : Continuous ψ') {C C' : ℝ}
    (hC : ∀ w, ‖ψ w‖ ≤ C) (hC' : ∀ w, ‖ψ' w‖ ≤ C') (y : Fin 3 → ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ z, gaussKernel 1 z • ψ (y - √t • z) (-(2 * √t)⁻¹ • z) =
      ∫ z, gaussKernel 1 z • ∑ i : Fin 3, ψ' (y - √t • z) (Pi.single i 1) (Pi.single i 1) := by
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun z => (hψ z).continuousAt
  have haff : ∀ z : Fin 3 → ℝ, HasFDerivAt (fun z : Fin 3 → ℝ => y - √t • z)
      (-(√t • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))) z := fun z =>
    ((hasFDerivAt_id z).const_smul (√t)).const_sub y
  have hcaff : Continuous fun z : Fin 3 → ℝ => y - √t • z := by fun_prop
  -- the coordinate functions `φᵢ(z) = ψ(y - √t z) eᵢ` and their derivatives
  have hIBP : ∀ i : Fin 3, ∫ z, (z i * gaussKernel 1 z) • ψ (y - √t • z) (Pi.single i 1) =
      (-(2 * √t)) • ∫ z, gaussKernel 1 z • ψ' (y - √t • z) (Pi.single i 1) (Pi.single i 1) := by
    intro i
    set L := ContinuousLinearMap.apply ℝ E (Pi.single i 1 : Fin 3 → ℝ)
    have hφ : ∀ z, HasFDerivAt (fun z => ψ (y - √t • z) (Pi.single i 1))
        (L.comp ((ψ' (y - √t • z)).comp (-(√t • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))))) z :=
      fun z => L.hasFDerivAt.comp z ((hψ _).comp z (haff z))
    have h := integral_coord_mul_gaussKernel_smul hφ
      (by fun_prop) (C := C * ‖(Pi.single i 1 : Fin 3 → ℝ)‖)
      (C' := ‖L‖ * (C' * ‖-(√t • ContinuousLinearMap.id ℝ (Fin 3 → ℝ))‖))
      (fun z => ((ψ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
      (fun z => (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
        (((ψ' _).opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right (hC' _) (norm_nonneg _)))
        (norm_nonneg _))) i
    rw [h]
    have hval : ∀ z, (L.comp ((ψ' (y - √t • z)).comp (-(√t • ContinuousLinearMap.id ℝ
        (Fin 3 → ℝ))))) (Pi.single i 1) =
        -(√t • ψ' (y - √t • z) (Pi.single i 1) (Pi.single i 1)) := by
      intro z
      simp [L]
    simp_rw [hval, smul_neg, smul_comm (gaussKernel 1 _) (√t)]
    rw [integral_neg, integral_smul]
    module
  have hexp : ∀ z, gaussKernel 1 z • ψ (y - √t • z) (-(2 * √t)⁻¹ • z) =
      (-(2 * √t)⁻¹) • ∑ i : Fin 3, (z i * gaussKernel 1 z) • ψ (y - √t • z) (Pi.single i 1) := by
    intro z
    rw [map_smul, clm_apply_eq_sum (ψ (y - √t • z)) z, Finset.smul_sum, Finset.smul_sum,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hint1 : ∀ i : Fin 3, Integrable fun z : Fin 3 → ℝ =>
      (z i * gaussKernel 1 z) • ψ (y - √t • z) (Pi.single i 1) := by
    intro i
    refine ((integrable_abs_mul_gaussKernel_one i).mul_const
      (C * ‖(Pi.single i 1 : Fin 3 → ℝ)‖)).mono' (by fun_prop : Continuous _).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussKernel_one_nonneg z)]
    exact mul_le_mul_of_nonneg_left (((ψ _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
      (mul_nonneg (abs_nonneg _) (gaussKernel_one_nonneg z))
  have hint2 : ∀ i : Fin 3, Integrable fun z : Fin 3 → ℝ =>
      gaussKernel 1 z • ψ' (y - √t • z) (Pi.single i 1) (Pi.single i 1) := by
    intro i
    refine (integrable_gaussKernel_one.mul_const
      (C' * ‖(Pi.single i 1 : Fin 3 → ℝ)‖ * ‖(Pi.single i 1 : Fin 3 → ℝ)‖)).mono'
      (by fun_prop : Continuous _).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [norm_smul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
    refine mul_le_mul_of_nonneg_left ?_ (gaussKernel_one_nonneg z)
    refine ((ψ' _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact ((ψ' _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC' _) (norm_nonneg _))
  simp_rw [hexp]
  rw [integral_smul, integral_finsetSum _ fun i _ => hint1 i]
  simp_rw [hIBP, Finset.smul_sum, smul_smul]
  have hc : (-(2 * √t)⁻¹) * (-(2 * √t)) = 1 := by field_simp
  simp_rw [hc, one_smul]
  rw [integral_finsetSum _ fun i _ => hint2 i]

/-- **The heat equation for `P_t`.** If `g` has continuous partial derivatives `Dg` and `Dg` has
continuous partial derivatives `D2g`, then `∂_t P_t g(x) = P_t(Δg)(x)` for `t > 0`, where
`Δg = Σᵢ D2g(·)ᵢᵢ` (`torusLap`). -/
theorem hasDerivAt_heatOp_apply {g : C(Torus3, E)} {Dg : C(Torus3, Fin 3 → E)}
    {D2g : C(Torus3, Fin 3 → Fin 3 → E)} (hg : HasTorusDeriv g Dg)
    (hDg : HasTorusDeriv (E := Fin 3 → E) Dg D2g) {t : ℝ} (ht : 0 < t) (x : Torus3) :
    HasDerivAt (fun s => heatOp s g x) (heatOp t (torusLap D2g) x) t := by
  obtain ⟨y, rfl⟩ := torusProj_surjective x
  simp_rw [heatOp_torusProj]
  set P : (Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] E := ofPartials with hP
  set F' : ℝ → (Fin 3 → ℝ) → E := fun s z =>
    gaussKernel 1 z • P (Dg (torusProj (y - √s • z))) (-(2 * √s)⁻¹ • z) with hF'
  have hdiff : ∀ z, ∀ s, 0 < s →
      HasDerivAt (fun s => gaussKernel 1 z • g (torusProj (y - √s • z))) (F' s z) s := by
    intro z s hs
    have h1 : HasDerivAt (fun s => y - √s • z) (-(2 * √s)⁻¹ • z) s := by
      have := ((Real.hasDerivAt_sqrt hs.ne').smul_const z).const_sub y
      simpa [one_div, neg_smul] using this
    exact ((hg (y - √s • z)).comp_hasDerivAt s h1).const_smul (gaussKernel 1 z)
  have ht2 : 0 < t / 2 := half_pos ht
  set c : ℝ := ‖P‖ * ‖Dg‖ * (2 * √(t / 2))⁻¹ with hc
  have hbound : ∀ z, ∀ s ∈ Metric.ball t (t / 2), ‖F' s z‖ ≤ c * (‖z‖ * gaussKernel 1 z) := by
    intro z s hs
    have hs' : t / 2 < s := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      linarith
    have hsq : √(t / 2) ≤ √s := Real.sqrt_le_sqrt hs'.le
    have hsq0 : 0 < √(t / 2) := Real.sqrt_pos.2 ht2
    have hPD : ‖P (Dg (torusProj (y - √s • z)))‖ ≤ ‖P‖ * ‖Dg‖ :=
      (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (Dg.norm_coe_le_norm _) (norm_nonneg _))
    rw [hF', norm_smul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
    calc gaussKernel 1 z * ‖P (Dg (torusProj (y - √s • z))) (-(2 * √s)⁻¹ • z)‖
        ≤ gaussKernel 1 z * ((‖P‖ * ‖Dg‖) * ((2 * √s)⁻¹ * ‖z‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (gaussKernel_one_nonneg z)
          refine ((P _).le_opNorm _).trans (mul_le_mul hPD ?_ (norm_nonneg _)
            (mul_nonneg (ContinuousLinearMap.opNorm_nonneg P) (norm_nonneg Dg)))
          rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
      _ ≤ gaussKernel 1 z * ((‖P‖ * ‖Dg‖) * ((2 * √(t / 2))⁻¹ * ‖z‖)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by linarith))
              (norm_nonneg _)) (mul_nonneg (ContinuousLinearMap.opNorm_nonneg P) (norm_nonneg Dg)))
            (gaussKernel_one_nonneg z)
      _ = c * (‖z‖ * gaussKernel 1 z) := by rw [hc]; ring
  have hcontF' : Continuous (F' t) := by
    rw [hF']
    have : Continuous fun z : Fin 3 → ℝ => P (Dg (torusProj (y - √t • z))) :=
      P.continuous.comp (Dg.continuous.comp (continuous_torusProj.comp (by fun_prop)))
    fun_prop
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s z => gaussKernel 1 z • g (torusProj (y - √s • z))) (F' := F')
    (bound := fun z => c * (‖z‖ * gaussKernel 1 z)) (Metric.ball_mem_nhds t ht2)
    (Eventually.of_forall fun s => by
      simpa [torusProj_sub] using
        (continuous_heatOp_integrand_right g s (torusProj y)).aestronglyMeasurable)
    (by simpa [torusProj_sub] using integrable_heatOp_integrand g t (torusProj y))
    hcontF'.aestronglyMeasurable (Eventually.of_forall fun z s hs => hbound z s hs)
    (integrable_norm_mul_gaussKernel_one.const_mul c)
    (Eventually.of_forall fun z s hs => hdiff z s (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      linarith))
  convert hD using 1
  -- identify the derivative by Gaussian integration by parts
  set P2 : (Fin 3 → Fin 3 → E) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] Fin 3 → E := ofPartials with hP2
  have hψ : ∀ w : Fin 3 → ℝ, HasFDerivAt (fun w => P (Dg (torusProj w)))
      (P.comp (P2 (D2g (torusProj w)))) w := fun w => P.hasFDerivAt.comp w (hDg w)
  have hψ'c : Continuous fun w : Fin 3 → ℝ => P.comp (P2 (D2g (torusProj w))) :=
    (continuous_const.clm_comp (P2.continuous.comp (D2g.continuous.comp continuous_torusProj)))
  have hC : ∀ w, ‖P (Dg (torusProj w))‖ ≤ ‖P‖ * ‖Dg‖ := fun w =>
    (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (Dg.norm_coe_le_norm _) (norm_nonneg _))
  have hC' : ∀ w, ‖P.comp (P2 (D2g (torusProj w)))‖ ≤ ‖P‖ * (‖P2‖ * ‖D2g‖) := fun w =>
    (P.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ((P2.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (D2g.norm_coe_le_norm _) (norm_nonneg _))) (norm_nonneg _))
  rw [hF', integral_gaussKernel_smul_deriv_eq hψ hψ'c hC hC' y ht]
  congr 1
  funext z
  congr 1
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hP, hP2, ofPartials_single,
    torusLap_apply, torusProj_sub]

end RegularityStructures.PDE

end
