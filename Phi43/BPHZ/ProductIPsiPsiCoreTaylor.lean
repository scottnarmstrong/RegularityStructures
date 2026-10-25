/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGradKernel
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements
import Mathlib.Tactic

/-!
# The Taylor kernel in `ℝ⁴` coordinates: measurability, `L¹` size, time support

For `x y : ℝ⁴` write `hairerTaylorKernelAt N x y w = hairerTaylorKernel N (proj x) (y₀ - x₀) (y' - x') w`,
so that `v₁(x, y) = hairerIPsiRecentred N ξ ω x y = ∫ hairerTaylorKernelAt N x y w Ψ(w) dw`.
It is jointly measurable in `(y, w)`, has `L¹` norm at most `L (1 + ‖y - x‖_𝔰)`, and vanishes unless
`w₀` is within `1` of `x₀` or of `y₀`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The Taylor kernel of `v₁(x, y)` in `ℝ⁴` coordinates. -/
def hairerTaylorKernelAt (N : ℕ) (x y : ParabolicSpace) (w : SpaceTime) : ℝ :=
  hairerTaylorKernel N (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) w

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `v₁(x, y)` is the pairing of `Ψ` with the Taylor kernel. -/
theorem hairerIPsiRecentred_eq_integral_taylorKernelAt {Ω : Type*} {ξ : Ω → SpaceTime → ℝ}
    {ω : Ω} (N : ℕ) (hξ : IsSmoothOnSpaceTime (ξ ω)) (x y : ParabolicSpace) :
    hairerIPsiRecentred N ξ ω x y =
      ∫ w, hairerTaylorKernelAt N x y w * hairerPsiField N ξ ω w := by
  rw [hairerIPsiRecentred_eq_gammaPsiTaylor N hξ]
  rfl

/-- The Taylor kernel is jointly measurable in `(y, w)`. -/
theorem measurable_uncurry_hairerTaylorKernelAt (N : ℕ) (x : ParabolicSpace) :
    Measurable (fun p : ParabolicSpace × SpaceTime => hairerTaylorKernelAt N x p.1 p.2) := by
  unfold hairerTaylorKernelAt hairerTaylorKernel
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hproj : Measurable fun p : ParabolicSpace × SpaceTime =>
      spaceTimeProj x + ((p.1.1 - x.1), torusProj (p.1.2 - x.2)) - p.2 := by
    refine (measurable_const.add (Measurable.prodMk ?_ ?_)).sub measurable_snd
    · exact (measurable_fst.comp measurable_fst).sub measurable_const
    · have hpr : Measurable (torusProj : (Fin 3 → ℝ) → Torus3) :=
        (continuous_pi fun i =>
          (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)).measurable
      exact hpr.comp ((measurable_snd.comp measurable_fst).sub measurable_const)
  refine ((hK.comp hproj).sub (hK.comp (measurable_const.sub measurable_snd))).sub ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  refine ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_snd)).mul ?_
  exact ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).sub measurable_const

/-- The `L¹` norm of the Taylor kernel grows at most linearly. -/
theorem integral_abs_hairerTaylorKernel_le (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ),
      ∫ w, |hairerTaylorKernel N x t a w| ≤ L * (1 + ∑ i, |a i|) := by
  set CK : ℝ := ∫ w, |hairerKernelTorus N w| with hCK
  set CG : Fin 3 → ℝ := fun i => ∫ w, |hairerKernelTorusGrad N i w| with hCG
  have hCK0 : 0 ≤ CK := integral_nonneg fun _ => abs_nonneg _
  have hCG0 : ∀ i, 0 ≤ CG i := fun i => integral_nonneg fun _ => abs_nonneg _
  have hS0 : 0 ≤ ∑ i, CG i := Finset.sum_nonneg fun i _ => hCG0 i
  refine ⟨2 * CK + ∑ i, CG i, by positivity, fun x t a => ?_⟩
  have h1 : Integrable (fun w => |hairerKernelTorus N (x + (t, torusProj a) - w)|) :=
    (integrable_hairerKernelTorus_sub N _).abs
  have h2 : Integrable (fun w => |hairerKernelTorus N (x - w)|) :=
    (integrable_hairerKernelTorus_sub N _).abs
  have h3 : ∀ i, Integrable (fun w => |hairerKernelTorusGrad N i (x - w)| * |a i|) := fun i =>
    ((integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i) x).abs).mul_const _
  have h4 : Integrable (fun w => ∑ i, |hairerKernelTorusGrad N i (x - w)| * |a i|) :=
    integrable_finsetSum _ fun i _ => h3 i
  have hmaj : Integrable (fun w => |hairerKernelTorus N (x + (t, torusProj a) - w)| +
      |hairerKernelTorus N (x - w)| + ∑ i, |hairerKernelTorusGrad N i (x - w)| * |a i|) :=
    (h1.add h2).add h4
  have hpt : ∀ w, |hairerTaylorKernel N x t a w| ≤
      |hairerKernelTorus N (x + (t, torusProj a) - w)| + |hairerKernelTorus N (x - w)| +
        ∑ i, |hairerKernelTorusGrad N i (x - w)| * |a i| := by
    intro w
    unfold hairerTaylorKernel
    calc _ ≤ |hairerKernelTorus N (x + (t, torusProj a) - w) - hairerKernelTorus N (x - w)| +
          |∑ i, hairerKernelTorusGrad N i (x - w) * a i| := abs_sub _ _
      _ ≤ (|hairerKernelTorus N (x + (t, torusProj a) - w)| + |hairerKernelTorus N (x - w)|) +
          ∑ i, |hairerKernelTorusGrad N i (x - w) * a i| :=
        add_le_add (abs_sub _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ = _ := by simp only [abs_mul]
  have hint : ∫ w, (|hairerKernelTorus N (x + (t, torusProj a) - w)| +
      |hairerKernelTorus N (x - w)| + ∑ i, |hairerKernelTorusGrad N i (x - w)| * |a i|) =
      CK + CK + ∑ i, CG i * |a i| := by
    rw [integral_add (f := fun w => |hairerKernelTorus N (x + (t, torusProj a) - w)| +
      |hairerKernelTorus N (x - w)|) (g := fun w => ∑ i, |hairerKernelTorusGrad N i (x - w)| * |a i|)
      (h1.add h2) h4, integral_add h1 h2,
      integral_comp_sub_left_spaceTime (fun w => |hairerKernelTorus N w|),
      integral_comp_sub_left_spaceTime (fun w => |hairerKernelTorus N w|)]
    rw [integral_finsetSum _ fun i _ => h3 i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const,
      integral_comp_sub_left_spaceTime (fun w => |hairerKernelTorusGrad N i w|)]
  calc ∫ w, |hairerTaylorKernel N x t a w|
      ≤ ∫ w, (|hairerKernelTorus N (x + (t, torusProj a) - w)| +
          |hairerKernelTorus N (x - w)| + ∑ i, |hairerKernelTorusGrad N i (x - w)| * |a i|) :=
        integral_mono (integrable_hairerTaylorKernel N x t a).abs hmaj hpt
    _ = CK + CK + ∑ i, CG i * |a i| := hint
    _ ≤ (2 * CK + ∑ i, CG i) * (1 + ∑ i, |a i|) := by
        have hs : 0 ≤ ∑ i, |a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
        have hle : ∑ i, CG i * |a i| ≤ (∑ i, CG i) * ∑ i, |a i| := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_le_sum fun i _ => ?_
          have : CG i * |a i| ≤ ∑ j, CG i * |a j| :=
            Finset.single_le_sum (f := fun j => CG i * |a j|)
              (fun j _ => mul_nonneg (hCG0 i) (abs_nonneg _)) (Finset.mem_univ i)
          exact this.trans (le_of_eq rfl)
        nlinarith [mul_nonneg hCK0 hs]

/-- The Taylor kernel vanishes unless `w₀` is within `1` of `x₀ + t` or of `x₀`. -/
theorem hairerTaylorKernel_ne_zero_time (N : ℕ) {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ}
    {w : SpaceTime} (h : hairerTaylorKernel N x t a w ≠ 0) :
    |x.1 + t - w.1| ≤ 1 ∨ |x.1 - w.1| ≤ 1 := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  apply h
  have h1 : 1 < |(x + (t, torusProj a) - w).1| := by simpa using hcon.1
  have h2 : 1 < |(x - w).1| := by simpa using hcon.2
  unfold hairerTaylorKernel
  rw [hairerKernelTorus_eq_zero_of_one_lt_time N h1, hairerKernelTorus_eq_zero_of_one_lt_time N h2]
  simp [hairerKernelTorusGrad_eq_zero_of_one_lt_time _ _ h2]

end RegularityStructures.Phi43

end
