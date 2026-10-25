/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2Field
public import Phi43.BPHZ.TreeWickSquareFour
public import Phi43.BPHZ.TreeWickDifferenceTested
public import RegularityStructures.Probability.RandomFieldFubini

/-!
# The tree `I(Ψ²) Ψ²`: the mean

[Hai14, (10.39)-(10.42)].  For a kernel `g ∈ L¹` and `Y = :Ψ²:`,
`E[(∫ g Y) Y(y)] = ∫ g(w) 2 Q_ε(w - y)² dw` (stochastic Fubini, the chaos-`0` part).  For the
increment kernel `g = K(y - ·) - K(x - ·)` this gives the mean of the field `(10.39)`:
`E[(Π̂^ε_x τ)(y)] = -2 ∫ K(x - w) Q_ε(w - y)² dw`, using that `Q_ε` is even and that
`C₂ = 2 ∫ K Q_ε²` (the definition of `hairerSunsetConstant`) in the form
`∫ K(y - w) Q_ε(w - y)² dw = ∫ K Q_ε² = C₂ / 2`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- The covariance `Q_ε` is even (torus translation invariance). -/
theorem hairerCovariance_neg (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) :
    hairerCovariance N ρ ε (-z) = hairerCovariance N ρ ε z := by
  unfold hairerCovariance
  rw [← integral_add_right_eq_self (fun w => hairerMollifiedKernel N ρ ε (-z + w) *
    hairerMollifiedKernel N ρ ε w) z]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show hairerMollifiedKernel N ρ ε (-z + (u + z)) * hairerMollifiedKernel N ρ ε (u + z) = _
  rw [show -z + (u + z) = u by abel, add_comm u z, mul_comm]

/-- `|Q_ε(x)| ≤ c_ε`. -/
theorem abs_hairerCovariance_le_wickConstant (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x : SpaceTime) :
    |hairerCovariance N ρ ε x| ≤ hairerWickConstant N ρ ε := by
  have h := abs_hairerCrossCovariance_le N hρ hε hε hW hξ hξ x
  rw [hairerCrossCovariance_self] at h
  linarith

/-- The covariance `Q_ε` is measurable. -/
theorem measurable_hairerCovariance (N : ℕ) (hρ : IsMollifier ρ) (ε : ℝ) :
    Measurable (hairerCovariance N ρ ε) :=
  measurable_hairerCrossCovariance N hρ ε ε

/-- `K(z - ·) Q_ε(· - y)²` is integrable. -/
theorem integrable_hairerKernelTorus_sub_mul_sq (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (z y : SpaceTime) :
    Integrable (fun w => hairerKernelTorus N (z - w) * hairerCovariance N ρ ε (w - y) ^ 2) := by
  have hm : Measurable (fun w => hairerCovariance N ρ ε (w - y) ^ 2) :=
    ((measurable_hairerCovariance N hρ ε).comp (measurable_id.sub measurable_const)).pow_const 2
  have hb := abs_hairerCovariance_le_wickConstant N hρ hε hW hξ
  refine (integrable_hairerKernelTorus_sub N z).mul_bdd (c := hairerWickConstant N ρ ε ^ 2)
    hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb _) 2

/-- **Fubini for the Wick square against a kernel** (chaos `0`):
`E[(∫ g Y) Y(y)] = ∫ g(w) 2 Q_ε(w - y)² dw`, and `(∫ g Y) Y(y)` is integrable. -/
theorem integral_integral_mul_hairerPsiWickSquare (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) {g : SpaceTime → ℝ}
    (hg : Integrable g) (y : SpaceTime) :
    Integrable (fun ω => (∫ w, g w * hairerPsiWickSquare N ρ ε ξ ω w) *
      hairerPsiWickSquare N ρ ε ξ ω y) P ∧
    ∫ ω, (∫ w, g w * hairerPsiWickSquare N ρ ε ξ ω w) *
      hairerPsiWickSquare N ρ ε ξ ω y ∂P =
        ∫ w, g w * (2 * hairerCovariance N ρ ε (w - y) ^ 2) := by
  have := hW.isProbabilityMeasure
  set Y := hairerPsiWickSquare N ρ ε ξ with hYdef
  have hYm : Measurable (fun q : Ω × SpaceTime => Y q.1 q.2) :=
    measurable_hairerPsiWickSquare_uncurry N hξ
  have hY' : AEStronglyMeasurable (Function.uncurry fun ω w => Y ω w * Y ω y) (P.prod volume) :=
    (hYm.mul (hYm.comp (measurable_fst.prodMk measurable_const))).aestronglyMeasurable
  have hL2 := fun u => hairerPsiWickSquare_memLp N hρ hε hW hξ u
  have hYi : ∀ w, Integrable (fun ω => Y ω w * Y ω y) P :=
    fun w => (hL2 w).integrable_mul (hL2 y)
  have hcov := hairerPsiWickSquare_integral_mul N hρ hε hW hξ
  have hM : ∀ w, ∫ ω, |Y ω w * Y ω y| ∂P ≤ 2 * hairerCovariance N ρ ε 0 ^ 2 := by
    intro w
    have hx : Integrable (fun ω => Y ω w * Y ω w) P := (hL2 w).integrable_mul (hL2 w)
    have hy : Integrable (fun ω => Y ω y * Y ω y) P := (hL2 y).integrable_mul (hL2 y)
    calc ∫ ω, |Y ω w * Y ω y| ∂P
        ≤ ∫ ω, (Y ω w * Y ω w + Y ω y * Y ω y) / 2 ∂P := by
          refine integral_mono (hYi w).abs ((hx.add hy).div_const 2) fun ω => ?_
          rw [abs_mul]
          nlinarith [sq_nonneg (|Y ω w| - |Y ω y|), abs_mul_abs_self (Y ω w),
            abs_mul_abs_self (Y ω y)]
      _ = 2 * hairerCovariance N ρ ε 0 ^ 2 := by
          rw [integral_div, integral_add hx hy, hcov w w, hcov y y]
          simp only [sub_self]
          ring
  have hG := integrable_uncurry_mul_of_bound (P := P) (μ := (volume : Measure SpaceTime)) hg hY'
    hYi hM
  have hpt : ∀ ω, (∫ w, g w * Y ω w) * Y ω y = ∫ w, g w * (Y ω w * Y ω y) := by
    intro ω
    rw [← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only; ring)
  refine ⟨?_, ?_⟩
  · refine (hG.integral_prod_left).congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (hpt ω).symm
  · simp_rw [hpt]
    rw [integral_integral_mul_swap hg hY' hYi hM]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [hcov w y]

/-- **`C₂` is twice the integral `∫ K(y - w) Q_ε(w - y)² dw`**
(evenness of `Q_ε` and torus translation invariance). -/
theorem integral_hairerKernelTorus_sub_mul_sq (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (y : SpaceTime) :
    2 * ∫ w, hairerKernelTorus N (y - w) * hairerCovariance N ρ ε (w - y) ^ 2 =
      hairerSunsetConstant N ρ ε := by
  have h := integral_comp_sub_left_spaceTime
    (fun v => hairerKernelTorus N v * hairerCovariance N ρ ε v ^ 2) y
  unfold hairerSunsetConstant
  rw [← h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [← hairerCovariance_neg N ρ ε (y - w), neg_sub]

/-- **The mean of the tree `I(Ψ²) Ψ²`** [Hai14, (10.41)-(10.42)]:
`E[(Π̂^ε_x τ)(y)] = -2 ∫ K(x - w) Q_ε(w - y)² dw`, and the field is integrable. -/
theorem integral_hairerI2Psi2Field (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : SpaceTime) :
    Integrable (fun ω => hairerI2Psi2Field N ρ ε ξ x ω y) P ∧
      ∫ ω, hairerI2Psi2Field N ρ ε ξ x ω y ∂P =
        -2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2 := by
  have := hW.isProbabilityMeasure
  obtain ⟨hi, he⟩ := integral_integral_mul_hairerPsiWickSquare N hρ hε hW hξ
    (integrable_hairerI2Psi2Kernel N x y) y
  have h1 := integrable_hairerKernelTorus_sub_mul_sq N hρ hε hW hξ y y
  have h2 := integrable_hairerKernelTorus_sub_mul_sq N hρ hε hW hξ x y
  have hC := integral_hairerKernelTorus_sub_mul_sq N ρ ε y
  refine ⟨hi.sub (integrable_const _), ?_⟩
  unfold hairerI2Psi2Field
  rw [integral_sub hi (integrable_const _), he]
  simp only [integral_const, probReal_univ, one_smul]
  have hsplit : ∀ w, hairerI2Psi2Kernel N x y w * (2 * hairerCovariance N ρ ε (w - y) ^ 2) =
      2 * (hairerKernelTorus N (y - w) * hairerCovariance N ρ ε (w - y) ^ 2) -
        2 * (hairerKernelTorus N (x - w) * hairerCovariance N ρ ε (w - y) ^ 2) := fun w => by
    unfold hairerI2Psi2Kernel
    ring
  simp_rw [hsplit]
  rw [integral_sub (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul,
    hC]
  ring

end RegularityStructures.Phi43

end
