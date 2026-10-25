/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierKernel
public import Phi43.BPHZ.TreeWickPairing
public import Phi43.BPHZ.PsiGaussianVector
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound

/-!
# Cross covariances of two mollifiers

For mollifiers `ρ`, `ρ'` and scales `ε`, `ε'` write `K = K_{ρ,ε}`, `K' = K_{ρ',ε'}` for the
mollified Hairer kernels and `Q(κ, κ')(x) = ∫ κ(x + w) κ'(w) dw`
(`hairerCrossCovarianceTwo N ρ ε ρ' ε'`).  With
`a = Q(K, K)`, `b = Q(K, K')`, `c = Q(K', K)`, `d = Q(K', K')` the combination
`∫ (K + s K')(x + w) (K + t K')(w) dw = a + t b + s c + s t d` satisfies
* `|a + t b + s c + s t d| ≲ s(x)⁻¹` for `|s|, |t| ≤ 1`,
* `|a + t b - c - t d|, |a - b + s c - s d| ≲ (max ε ε')^θ s(x)^(-1-θ)`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The cross covariance `Q(x) = ∫ K_{ρ,ε}(x + w) K_{ρ',ε'}(w) dw` of two mollified Hairer kernels
with possibly different mollifiers. -/
def hairerCrossCovarianceTwo (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε' : ℝ) (x : SpaceTime) : ℝ :=
  ∫ w, hairerMollifiedKernel N ρ ε (x + w) * hairerMollifiedKernel N ρ' ε' w

/-- The kernel combination `K_{ρ,ε} + s K_{ρ',ε'}`. -/
def hairerKernelCombTwo (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ε' s : ℝ) (v : SpaceTime) : ℝ :=
  hairerMollifiedKernel N ρ ε v + s * hairerMollifiedKernel N ρ' ε' v

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `hairerCrossCovarianceTwo` with equal mollifiers is `hairerCrossCovariance`. -/
theorem hairerCrossCovarianceTwo_self (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε ε' : ℝ) :
    hairerCrossCovarianceTwo N ρ ε ρ ε' = hairerCrossCovariance N ρ ε ε' := rfl

/-- Integrability and a uniform bound for the mollified kernel at a fixed scale. -/
private theorem cmc_integrable_bdd (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (hairerMollifiedKernel N ρ ε) ∧
      ∃ B : ℝ, ∀ v, |hairerMollifiedKernel N ρ ε v| ≤ B := by
  refine ⟨?_, ?_⟩
  · rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
    exact (integrable_periodise ρ hρ hε).integrable_convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) (integrable_constantsComparison_hairerKernelTorus N)
  · obtain ⟨C0, hC0, hK⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
    refine ⟨C0 * ε ^ (-(3 : ℝ)), fun v => (hK hε hε1 v).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε
      (le_add_of_nonneg_left (torusParabolicSize_nonneg v)) (by norm_num)) hC0

private theorem cmc_integrable_shift_mul {F G : SpaceTime → ℝ} (hF : Integrable F)
    (hG : Integrable G) {B : ℝ} (hB : ∀ v, |G v| ≤ B) (x : SpaceTime) :
    Integrable (fun w => F (x + w) * G w) :=
  ((measurePreserving_add_left volume x).integrable_comp_of_integrable hF).mul_bdd
    hG.aestronglyMeasurable (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]; exact hB v)

/-- Bilinear expansion for general integrable bounded `F`, `G`. -/
private theorem cmc_expand {F G : SpaceTime → ℝ} (hF : Integrable F) (hG : Integrable G)
    {B B' : ℝ} (hB : ∀ v, |F v| ≤ B) (hB' : ∀ v, |G v| ≤ B') (s t : ℝ) (x : SpaceTime) :
    ∫ w, (F (x + w) + s * G (x + w)) * (F w + t * G w) =
      (∫ w, F (x + w) * F w) + t * (∫ w, F (x + w) * G w) + s * (∫ w, G (x + w) * F w) +
        s * t * (∫ w, G (x + w) * G w) := by
  have i1 := cmc_integrable_shift_mul hF hF hB x
  have i2 := cmc_integrable_shift_mul hF hG hB' x
  have i3 := cmc_integrable_shift_mul hG hF hB x
  have i4 := cmc_integrable_shift_mul hG hG hB' x
  have j12 : Integrable (fun w => F (x + w) * F w + t * (F (x + w) * G w)) :=
    i1.add (i2.const_mul t)
  have j123 : Integrable (fun w => F (x + w) * F w + t * (F (x + w) * G w) +
      s * (G (x + w) * F w)) := j12.add (i3.const_mul s)
  calc ∫ w, (F (x + w) + s * G (x + w)) * (F w + t * G w)
      = ∫ w, (F (x + w) * F w + t * (F (x + w) * G w) + s * (G (x + w) * F w)) +
          (s * t) * (G (x + w) * G w) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        ring
    _ = _ := by
        rw [integral_add j123 (i4.const_mul (s * t)), integral_add j12 (i3.const_mul s),
          integral_add i1 (i2.const_mul t), integral_const_mul, integral_const_mul,
          integral_const_mul]

/-- **Bilinear expansion** of the pairing of two kernel combinations in the four cross
covariances of the 2×2 table `(ρ, ε), (ρ', ε')`. -/
theorem integral_hairerKernelCombTwo_shift_mul (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {ε ε' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (s t : ℝ) (x : SpaceTime) :
    ∫ w, hairerKernelCombTwo N ρ ε ρ' ε' s (x + w) * hairerKernelCombTwo N ρ ε ρ' ε' t w =
      hairerCrossCovarianceTwo N ρ ε ρ ε x + t * hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
        s * hairerCrossCovarianceTwo N ρ' ε' ρ ε x +
        s * t * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x := by
  obtain ⟨hKi, B, hB⟩ := cmc_integrable_bdd N ρ hρ hε hε1
  obtain ⟨hKi', B', hB'⟩ := cmc_integrable_bdd N ρ' hρ' hε' hε'1
  exact cmc_expand hKi hKi' hB hB' s t x

/-- Singular bound for the kernel combination: `|K_{ρ,ε} + s K_{ρ',ε'}| ≲ s⁻³` for `|s| ≤ 1`. -/
private theorem cmc_comb_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ {ε ε' s : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → |s| ≤ 1 →
      ∀ v : SpaceTime, 0 < torusParabolicSize v →
        |hairerKernelCombTwo N ρ ε ρ' ε' s v| ≤ C0 * torusParabolicSize v ^ (-(3 : ℝ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  obtain ⟨C1, hC1, hK'⟩ := hairerMollifiedKernel_singular_bound ρ' hρ' N
  refine ⟨C0 + C1, by positivity, ?_⟩
  intro ε ε' s hε hε1 hε' hε'1 hs v hv
  have h1 : |hairerMollifiedKernel N ρ ε v| ≤ C0 * torusParabolicSize v ^ (-(3 : ℝ)) :=
    (hK hε hε1 v).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hv (by linarith) (by norm_num)) hC0)
  have h2 : |hairerMollifiedKernel N ρ' ε' v| ≤ C1 * torusParabolicSize v ^ (-(3 : ℝ)) :=
    (hK' hε' hε'1 v).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hv (by linarith) (by norm_num)) hC1)
  have hp : 0 ≤ torusParabolicSize v ^ (-(3 : ℝ)) := Real.rpow_nonneg hv.le _
  calc |hairerKernelCombTwo N ρ ε ρ' ε' s v|
      ≤ |hairerMollifiedKernel N ρ ε v| + |s| * |hairerMollifiedKernel N ρ' ε' v| := by
        rw [hairerKernelCombTwo, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ C0 * torusParabolicSize v ^ (-(3 : ℝ)) + 1 * (C1 * torusParabolicSize v ^ (-(3 : ℝ))) :=
        add_le_add h1 (mul_le_mul hs h2 (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- `|a + t b + s c + s t d| ≲ s(x)⁻¹` for `|s|, |t| ≤ 1` (cross-mollifier table). -/
theorem hairerCrossTwo_comb_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' s t : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → |s| ≤ 1 → |t| ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerCrossCovarianceTwo N ρ ε ρ ε x + t * hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
          s * hairerCrossCovarianceTwo N ρ' ε' ρ ε x +
          s * t * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x| ≤
          C * torusParabolicSize x ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, hK⟩ := cmc_comb_abs_le N ρ ρ' hρ hρ'
  obtain ⟨Cp, hCp, hP⟩ := abs_integral_shift_mul_singular_le (a := 3) (b := 3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cp * C0 * C0, by positivity, ?_⟩
  intro ε ε' s t hε hε1 hε' hε'1 hs ht x hx
  have := hP hC0 hC0 (hK hε hε1 hε' hε'1 hs) (hK hε hε1 hε' hε'1 ht) x hx
  rw [integral_hairerKernelCombTwo_shift_mul N ρ ρ' hρ hρ' hε hε1 hε' hε'1 s t x] at this
  refine this.trans (le_of_eq ?_)
  rw [show (5 : ℝ) - 3 - 3 = -1 by norm_num]

/-- The kernel difference of the two mollified kernels is the combination with `s = -1`. -/
private theorem cmc_diff_bound (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ v, 0 < torusParabolicSize v → |hairerKernelCombTwo N ρ ε ρ' ε' (-1) v| ≤
        (C1 * (max ε ε') ^ θ) * torusParabolicSize v ^ (-(3 + θ)) := by
  obtain ⟨C1, hC1, hD⟩ := hairerMollifiedKernel_sub_abs_le_cross_of_pos N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨C1, hC1, fun hε hε1 hε' hε'1 v hv => ?_⟩
  have := hD hε hε1 hε' hε'1 v hv
  simpa only [hairerKernelCombTwo, neg_mul, one_mul, ← sub_eq_add_neg, mul_assoc] using this

/-- A difference on the left: `a + t b - c - t d` is `≲ (max ε ε')^θ s(x)^(-1-θ)` for `|t| ≤ 1`
(`s = -1`). -/
theorem hairerCrossTwo_diff_left_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' t : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → |t| ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerCrossCovarianceTwo N ρ ε ρ ε x + t * hairerCrossCovarianceTwo N ρ ε ρ' ε' x -
          hairerCrossCovarianceTwo N ρ' ε' ρ ε x - t * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x| ≤
          C * (max ε ε') ^ θ * torusParabolicSize x ^ (-1 - θ) := by
  obtain ⟨C0, hC0, hK⟩ := cmc_comb_abs_le N ρ ρ' hρ hρ'
  obtain ⟨C1, hC1, hDb⟩ := cmc_diff_bound N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨Cp, hCp, hP⟩ := abs_integral_shift_mul_singular_le (a := 3 + θ) (b := 3)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by linarith)
  refine ⟨Cp * C1 * C0, by positivity, ?_⟩
  intro ε ε' t hε hε1 hε' hε'1 ht x hx
  have hM0 : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.le) _
  have := hP (mul_nonneg hC1 hM0) hC0 (hDb hε hε1 hε' hε'1) (hK hε hε1 hε' hε'1 ht) x hx
  rw [integral_hairerKernelCombTwo_shift_mul N ρ ρ' hρ hρ' hε hε1 hε' hε'1 (-1) t x] at this
  have e : (5 : ℝ) - (3 + θ) - 3 = -1 - θ := by ring
  rw [e] at this
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · congr 1
    ring
  · ring

/-- A difference on the right: `a - b + s c - s d` is `≲ (max ε ε')^θ s(x)^(-1-θ)` for `|s| ≤ 1`
(`t = -1`). -/
theorem hairerCrossTwo_diff_right_abs_le (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' s : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → |s| ≤ 1 →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |hairerCrossCovarianceTwo N ρ ε ρ ε x - hairerCrossCovarianceTwo N ρ ε ρ' ε' x +
          s * hairerCrossCovarianceTwo N ρ' ε' ρ ε x - s * hairerCrossCovarianceTwo N ρ' ε' ρ' ε' x| ≤
          C * (max ε ε') ^ θ * torusParabolicSize x ^ (-1 - θ) := by
  obtain ⟨C0, hC0, hK⟩ := cmc_comb_abs_le N ρ ρ' hρ hρ'
  obtain ⟨C1, hC1, hDb⟩ := cmc_diff_bound N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨Cp, hCp, hP⟩ := abs_integral_shift_mul_singular_le (a := 3) (b := 3 + θ)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨Cp * C0 * C1, by positivity, ?_⟩
  intro ε ε' s hε hε1 hε' hε'1 hs x hx
  have hM0 : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.le) _
  have := hP hC0 (mul_nonneg hC1 hM0) (hK hε hε1 hε' hε'1 hs) (hDb hε hε1 hε' hε'1) x hx
  rw [integral_hairerKernelCombTwo_shift_mul N ρ ρ' hρ hρ' hε hε1 hε' hε'1 s (-1) x] at this
  have e : (5 : ℝ) - 3 - (3 + θ) = -1 - θ := by ring
  rw [e] at this
  refine le_trans (le_of_eq ?_) (this.trans (le_of_eq ?_))
  · congr 1
    ring
  · ring

end RegularityStructures.Phi43

end
