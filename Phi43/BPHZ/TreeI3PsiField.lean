/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickSquare
public import Phi43.BPHZ.PsiGaussianVectorContinuous

/-!
# The field `I₃Ψ`: definition, measurability and integrability

With the Wick cube `:Ψ³: = Ψ³ - 3 C₁ Ψ` (`C₁ = hairerWickConstant`) we set, for a base point `x`,
`I₃Ψ(y) = (∫ (K(y - w) - K(x - w)) :Ψ³:(w) dw) Ψ(y)`
(the pathwise field behind the tree `I(Ψ³) Ψ` of [Hai14, §10]).

Because `ξ ω` is smooth, `Ψ(ω, ·)` is continuous, and the kernel `K` is integrable and vanishes
for time displacement larger than `1`; hence the inner integral converges for every `ω`.  The
field `(ω, y) ↦ I₃Ψ` is jointly measurable.

The Wick cube here is named `hairerPsiWickCubeField` (a parallel development may use
`hairerPsiWickCube`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The Wick cube `Ψ(z)³ - 3 C₁ Ψ(z)` of the tree `Ψ`, `C₁ = hairerWickConstant`. -/
def hairerPsiWickCubeField {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (ω : Ω) (z : SpaceTime) : ℝ :=
  hairerPsiField N ξ ω z ^ 3 - 3 * hairerWickConstant N ρ ε * hairerPsiField N ξ ω z

/-- The field `I₃Ψ(y) = (∫ (K(y - w) - K(x - w)) :Ψ³:(w) dw) Ψ(y)` with base point `x`. -/
def hairerI3PsiField {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (x : SpaceTime) (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, (hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)) *
      hairerPsiWickCubeField N ρ ε ξ ω w) * hairerPsiField N ξ ω y

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The kernel `K(y - ·)` times a continuous function is integrable. -/
theorem integrable_hairerKernelTorus_sub_mul_continuous (N : ℕ) (y : SpaceTime)
    {h : SpaceTime → ℝ} (hh : Continuous h) :
    Integrable (fun w => hairerKernelTorus N (y - w) * h w) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := y.1 - 1) (b := y.1 + 1)).prod
    (isCompact_univ (X := Torus3)) |>.exists_bound_of_continuousOn hh.continuousOn
  have hK := integrable_hairerKernelTorus_sub N y
  refine (hK.abs.mul_const C).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id) |>.mul hh.measurable).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hw : 1 < |(y - w).1|
    · rw [hairerKernelTorus_eq_zero_of_one_lt_time N hw]
      simp
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hmem : w ∈ Set.Icc (y.1 - 1) (y.1 + 1) ×ˢ (Set.univ : Set Torus3) := by
        refine ⟨?_, Set.mem_univ _⟩
        have h2 := abs_le.1 (not_lt.1 hw)
        simp only [Set.mem_Icc, Prod.fst_sub] at h2 ⊢
        constructor <;> linarith [h2.1, h2.2]
      simpa using hC _ hmem

/-- The Wick cube of `Ψ` is jointly measurable. -/
theorem measurable_hairerPsiWickCubeField_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable (fun q : Ω × SpaceTime => hairerPsiWickCubeField N ρ ε ξ q.1 q.2) := by
  have h := measurable_hairerPsiField_uncurry N hξ
  unfold hairerPsiWickCubeField
  exact (h.pow_const 3).sub (h.const_mul _)

/-- The integrand of the inner integral of `I₃Ψ` is jointly measurable. -/
theorem measurable_hairerI3PsiField_integrand (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : SpaceTime) :
    Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      (hairerKernelTorus N (r.1.2 - r.2) - hairerKernelTorus N (x - r.2)) *
        hairerPsiWickCubeField N ρ ε ξ r.1.1 r.2) := by
  have hK := measurable_constantsComparison_hairerKernelTorus N
  have hC := measurable_hairerPsiWickCubeField_uncurry N hξ
  have h1 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerKernelTorus N (r.1.2 - r.2)) :=
    hK.comp ((measurable_snd.comp measurable_fst).sub measurable_snd)
  have h2 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime => hairerKernelTorus N (x - r.2)) :=
    hK.comp (measurable_const.sub measurable_snd)
  have h3 : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
      hairerPsiWickCubeField N ρ ε ξ r.1.1 r.2) :=
    Measurable.comp (g := fun q : Ω × SpaceTime => hairerPsiWickCubeField N ρ ε ξ q.1 q.2)
      (f := fun r : (Ω × SpaceTime) × SpaceTime => (r.1.1, r.2)) hC
      (measurable_fst.fst.prodMk measurable_snd)
  exact (h1.sub h2).mul h3

/-- **Joint measurability of `I₃Ψ`.** -/
theorem measurable_hairerI3PsiField_uncurry (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x : SpaceTime) :
    Measurable (fun q : Ω × SpaceTime => hairerI3PsiField N ρ ε ξ x q.1 q.2) := by
  have hint := measurable_hairerI3PsiField_integrand N hξ x
  have hI : Measurable (fun q : Ω × SpaceTime => ∫ w,
      (hairerKernelTorus N (q.2 - w) - hairerKernelTorus N (x - w)) *
        hairerPsiWickCubeField N ρ ε ξ q.1 w) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  exact hI.mul (measurable_hairerPsiField_uncurry N hξ)

/-- `hairerCovariance` is even. -/
private theorem hairerCovariance_neg (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (x : SpaceTime) :
    hairerCovariance N ρ ε (-x) = hairerCovariance N ρ ε x := by
  unfold hairerCovariance
  have h := integral_comp_add_left_spaceTime
    (fun v => hairerMollifiedKernel N ρ ε (-x + v) * hairerMollifiedKernel N ρ ε v) x
  simp only [neg_add_cancel_left] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => mul_comm _ _)

/-- `hairerCovariance` is even, in subtraction form. -/
theorem hairerCovariance_sub_comm (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (a b : SpaceTime) :
    hairerCovariance N ρ ε (a - b) = hairerCovariance N ρ ε (b - a) := by
  rw [← neg_sub, hairerCovariance_neg]

end RegularityStructures.Phi43

end
