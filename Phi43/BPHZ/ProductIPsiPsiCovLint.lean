/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovMajorant
public import Phi43.BPHZ.ProductIPsiPsiCovField
public import Phi43.BPHZ.SemigroupTestTreesSlabAt
public import Phi43.BPHZ.TreeI3PsiLeaves
public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.Stochastic.ConstantsComparisonC2Bounds
import Mathlib.Tactic

/-!
# The pairing `∫ T(w) Q(w - g) dw` of the Taylor remainder kernel with the covariance, small `r`

For `r = ‖(t, a)‖_𝔰 ≤ 1/2`, `0 < γ < 1`, `0 < θ < 1`, uniformly in `ε ∈ (0, 1]`, `x`, `g` with
`g ≠ x`:
`|∫ T(w) Q(w - g) dw| ≤ C r^γ (1 + s(x - g)^(-θ))`
(`hairerTaylorKernel_pairing_le_small`).  The proof uses the refined majorant of
`hairerTaylorKernel_refined_majorant`, `|Q(z)| ≲ s(z)^(-1)`, and the convolution estimates
`singularIntLe_mul_two` (`(4+θ) + 1 > 5`) and `singularIntLe_slabAt_mul_two` (`(3+γ) + 1 < 5`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ipsi_size_swap (a b : SpaceTime) : torusParabolicSize (a - b) = torusParabolicSize (b - a) := by
  refine le_antisymm ?_ ?_
  · have := torusParabolicSize_neg_le_self (b - a)
    rwa [neg_sub] at this
  · have := torusParabolicSize_neg_le_self (a - b)
    rwa [neg_sub] at this

theorem ipsi_slab_mul_eq_indicator (τ : ℝ) (f : SpaceTime → ℝ) (w : SpaceTime) :
    i2Psi2Slab τ w * f w = Set.indicator {w : SpaceTime | |w.1 - τ| ≤ 2} f w := by
  unfold i2Psi2Slab
  by_cases h : |w.1 - τ| ≤ 2
  · simp [h]
  · simp [h]

/-- `|Q(w - g)| ≤ C s(g - w)^(-1)`. -/
theorem ipsi_cov_abs_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ g w : SpaceTime,
      0 < torusParabolicSize (g - w) →
        |hairerCovariance N ρ ε (w - g)| ≤ C * singularPow 1 g w := by
  obtain ⟨C, hC, h⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨C, hC, fun {ε} hε hε1 g w hgw => ?_⟩
  have hsz : torusParabolicSize (w - g) = torusParabolicSize (g - w) := ipsi_size_swap _ _
  have := h hε hε1 (w - g) (by rw [hsz]; exact hgw)
  simpa [singularPow, hsz] using this

/-- **Small-`r` pairing bound.** -/
theorem hairerTaylorKernel_pairing_le_small (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {θ γ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ}
      {g : SpaceTime}, parabolicNorm (t, a) ≤ 1 / 2 → 0 < torusParabolicSize (x - g) →
        Integrable (fun w => hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)) ∧
        |∫ w, hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)| ≤
          C * parabolicNorm (t, a) ^ γ * (1 + torusParabolicSize (x - g) ^ (-θ)) := by
  obtain ⟨M, hM, hMaj⟩ := hairerTaylorKernel_refined_majorant N (θ := θ) (γ := γ) hθ.le hθ1.le
    hγ.le (by linarith)
  obtain ⟨C₂, hC₂, hQ⟩ := ipsi_cov_abs_le N hρ
  obtain ⟨Ca, hCa, hA⟩ := singularIntLe_mul_two (a := 4 + θ) (b := 1) (η := θ) (by linarith)
    (by linarith) (by norm_num) (by norm_num) hθ (by ring)
  set Kb : ℝ := 2 * (80 / (5 - ((3 + γ) + 1)) + 2 * 2) with hKb
  have hKb0 : 0 ≤ Kb := by
    have : 0 ≤ 80 / (5 - ((3 + γ) + 1)) := div_nonneg (by norm_num) (by linarith)
    rw [hKb]; positivity
  refine ⟨C₂ * M * (Ca + 2 * Kb), by positivity, ?_⟩
  intro ε hε hε1 x t a g hr hxg
  have hQm : Measurable (hairerCovariance N ρ ε) :=
    constantsComparison_hairerCovariance_measurable N ρ hε hρ hε1
  set r := parabolicNorm (t, a) with hrdef
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hai : ∀ i, |a i| ≤ 1 / 2 := fun i => by
    refine le_trans ?_ hr
    refine (Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)).trans ?_
    simp only [hrdef, parabolicNorm]
    linarith [Real.sqrt_nonneg |t|]
  have ht : |t| ≤ 1 := by
    have h1 : √|t| ≤ 1 / 2 := by
      refine le_trans ?_ hr
      simp only [hrdef, parabolicNorm]
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (a i)]
    have h2 : |t| ≤ (1 / 2) ^ 2 := by
      rw [← Real.sqrt_le_left (by norm_num)]; exact h1
    linarith
  set v : SpaceTime := x + (t, torusProj a) with hv
  have hTm : Measurable (hairerTaylorKernel N x t a) := measurable_hairerTaylorKernel N x t a
  have hGm : Measurable (fun w => hairerCovariance N ρ ε (w - g)) :=
    hQm.comp (measurable_id.sub_const g)
  -- the integrable majorants
  have S1 := (hA x g hxg).const_mul (c := r ^ (1 + θ)) (Real.rpow_nonneg hr0 _)
  have S2 := (singularIntLe_slabAt_mul_two (a := 3 + γ) (b := 1) (T := 2) x.1 (by linarith)
    (by norm_num) (by linarith) (by norm_num) v g)
  have S3 := (singularIntLe_slabAt_mul_two (a := 3 + γ) (b := 1) (T := 2) x.1 (by linarith)
    (by norm_num) (by linarith) (by norm_num) x g)
  have S23 := (S2.add S3).const_mul (c := r ^ γ) (Real.rpow_nonneg hr0 _)
  have S := (S1.add S23).const_mul (c := C₂ * M) (by positivity)
  have hfin : SingularIntLe (fun w => |hairerTaylorKernel N x t a w *
      hairerCovariance N ρ ε (w - g)|)
      (C₂ * M * (r ^ (1 + θ) * (Ca * torusParabolicSize (x - g) ^ (-θ)) +
        r ^ γ * (Kb + Kb))) := by
    refine S.of_le (F := fun w => |hairerTaylorKernel N x t a w *
      hairerCovariance N ρ ε (w - g)|) (hTm.mul hGm).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => abs_nonneg _) ?_
    filter_upwards [ae_torusParabolicSize_sub_pos x, ae_torusParabolicSize_sub_pos v,
      ae_torusParabolicSize_sub_pos g] with w hx hv' hg
    have hT := hMaj hai ht w hx hv'
    have hG := hQ hε hε1 g w hg
    have hsl0 := i2Psi2Slab_nonneg x.1 w
    have hsl1 := i2Psi2Slab_le_one x.1 w
    have e2 := ipsi_slab_mul_eq_indicator x.1
      (fun w => singularPow (3 + γ) v w * singularPow 1 g w) w
    have e3 := ipsi_slab_mul_eq_indicator x.1
      (fun w => singularPow (3 + γ) x w * singularPow 1 g w) w
    have nA := singularPow_nonneg (4 + θ) x w
    have nB := singularPow_nonneg (3 + γ) v w
    have nC := singularPow_nonneg (3 + γ) x w
    have nG := singularPow_nonneg 1 g w
    have hP1 : 0 ≤ r ^ (1 + θ) := Real.rpow_nonneg hr0 _
    have hPg : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
    rw [abs_mul]
    have hmain : |hairerTaylorKernel N x t a w| * |hairerCovariance N ρ ε (w - g)| ≤
        (i2Psi2Slab x.1 w * (M * (r ^ (1 + θ) * singularPow (4 + θ) x w +
          r ^ γ * (singularPow (3 + γ) v w + singularPow (3 + γ) x w)))) *
          (C₂ * singularPow 1 g w) :=
      mul_le_mul hT hG (abs_nonneg _) (by positivity)
    refine hmain.trans ?_
    simp only [singularPow] at e2 e3 nA nB nC nG ⊢
    have key : i2Psi2Slab x.1 w * (M * (r ^ (1 + θ) * torusParabolicSize (x - w) ^ (-(4 + θ)) +
          r ^ γ * (torusParabolicSize (v - w) ^ (-(3 + γ)) +
            torusParabolicSize (x - w) ^ (-(3 + γ))))) *
        (C₂ * torusParabolicSize (g - w) ^ (-(1 : ℝ))) =
        C₂ * M * (r ^ (1 + θ) * (i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
            torusParabolicSize (g - w) ^ (-(1 : ℝ)))) +
          r ^ γ * (i2Psi2Slab x.1 w * (torusParabolicSize (v - w) ^ (-(3 + γ)) *
            torusParabolicSize (g - w) ^ (-(1 : ℝ))) +
            i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(3 + γ)) *
            torusParabolicSize (g - w) ^ (-(1 : ℝ))))) := by ring
    rw [key, e2, e3]
    have : i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
        torusParabolicSize (g - w) ^ (-(1 : ℝ))) ≤
        torusParabolicSize (x - w) ^ (-(4 + θ)) * torusParabolicSize (g - w) ^ (-(1 : ℝ)) :=
      mul_le_of_le_one_left (mul_nonneg nA nG) hsl1
    have h4 : r ^ (1 + θ) * (i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
        torusParabolicSize (g - w) ^ (-(1 : ℝ)))) ≤
        r ^ (1 + θ) * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
        torusParabolicSize (g - w) ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_left this hP1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hint : Integrable (fun w => hairerTaylorKernel N x t a w *
      hairerCovariance N ρ ε (w - g)) := by
    have := hfin.1
    exact (integrable_norm_iff (hTm.mul hGm).aestronglyMeasurable).1 (by simpa using this)
  refine ⟨hint, ?_⟩
  have h1 : |∫ w, hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)| ≤
      ∫ w, |hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)| := by
    simpa using norm_integral_le_integral_norm
      (fun w => hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g))
  refine h1.trans (hfin.2.trans ?_)
  have hrg : r ^ (1 + θ) ≤ r ^ γ :=
    Real.rpow_le_rpow_of_exponent_ge' hr0 (by linarith) hγ.le (by linarith)
  have hE : 0 ≤ torusParabolicSize (x - g) ^ (-θ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hPg : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
  have hP1 : 0 ≤ r ^ (1 + θ) := Real.rpow_nonneg hr0 _
  have hCM : 0 ≤ C₂ * M := by positivity
  calc C₂ * M * (r ^ (1 + θ) * (Ca * torusParabolicSize (x - g) ^ (-θ)) + r ^ γ * (Kb + Kb))
      ≤ C₂ * M * (r ^ γ * (Ca * torusParabolicSize (x - g) ^ (-θ)) + r ^ γ * (Kb + Kb)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCM
        have := mul_le_mul_of_nonneg_right hrg (mul_nonneg hCa hE)
        linarith
    _ ≤ C₂ * M * (Ca + 2 * Kb) * r ^ γ * (1 + torusParabolicSize (x - g) ^ (-θ)) := by
        have : 0 ≤ r ^ γ * (Ca * torusParabolicSize (x - g) ^ (-θ)) := by positivity
        have h2 : r ^ γ * (Ca * torusParabolicSize (x - g) ^ (-θ)) + r ^ γ * (Kb + Kb) ≤
            (Ca + 2 * Kb) * r ^ γ * (1 + torusParabolicSize (x - g) ^ (-θ)) := by
          have h3 : 0 ≤ r ^ γ * Kb := mul_nonneg hPg hKb0
          have h4 : 0 ≤ r ^ γ * (Kb * torusParabolicSize (x - g) ^ (-θ)) := by positivity
          nlinarith
        calc _ ≤ C₂ * M * ((Ca + 2 * Kb) * r ^ γ * (1 + torusParabolicSize (x - g) ^ (-θ))) :=
              mul_le_mul_of_nonneg_left h2 hCM
          _ = _ := by ring

/-- `|∂ᵢK(z)| ≲ s(z)^(-(4+θ))` for all `z` (the kernel vanishes for `s(z) > 1`). -/
theorem hairerKernelTorusGrad_abs_le_rpow (N : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) {z : SpaceTime}, 0 < torusParabolicSize z →
      |hairerKernelTorusGrad N i z| ≤ C * torusParabolicSize z ^ (-(4 + θ)) := by
  obtain ⟨C, hC, h⟩ := hairerKernelTorusGrad_abs_le N
  refine ⟨C, hC, fun i z hz => ?_⟩
  by_cases h1 : torusParabolicSize z ≤ 1
  · refine (h i hz).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.rpow_le_rpow_of_exponent_ge hz h1 (by linarith)
  · rw [hairerKernelTorusGrad_eq_zero_of_one_lt N i (lt_of_not_ge h1)]
    simp only [abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

/-- `|K(z)| ≤ B s(z)^(-3) 1[|z₀| ≤ 1]`, in the form of a bound by a slab indicator. -/
theorem hairerKernelTorus_abs_le_indicator (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c w : SpaceTime), 0 < torusParabolicSize (c - w) →
      |hairerKernelTorus N (c - w)| ≤
        B * Set.indicator {w : SpaceTime | |w.1 - c.1| ≤ 2} (singularPow 3 c) w := by
  obtain ⟨B3, hB3, -, -, -, hKb, -⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  refine ⟨B3, hB3, fun c w hz => ?_⟩
  by_cases hw : |w.1 - c.1| ≤ 2
  · rw [Set.indicator_of_mem (show w ∈ {w : SpaceTime | |w.1 - c.1| ≤ 2} from hw)]
    simpa [singularPow] using hKb _ hz
  · have h1 : 1 < |(c - w).1| := by
      simp only [Prod.fst_sub]
      rw [abs_sub_comm]
      linarith [not_le.1 hw]
    rw [hairerKernelTorus_eq_zero_of_one_lt_time N h1,
      Set.indicator_of_notMem (show w ∉ {w : SpaceTime | |w.1 - c.1| ≤ 2} from hw)]
    simp

/-- **Crude pairing bound, all `r`.** -/
theorem hairerTaylorKernel_pairing_le_crude (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ}
      {g : SpaceTime}, 0 < torusParabolicSize (x - g) →
        Integrable (fun w => hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)) ∧
        |∫ w, hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)| ≤
          C * (1 + parabolicNorm (t, a)) * (1 + torusParabolicSize (x - g) ^ (-θ)) := by
  obtain ⟨C₂, hC₂, hQ⟩ := ipsi_cov_abs_le N hρ
  obtain ⟨Ca, hCa, hA⟩ := singularIntLe_mul_two (a := 4 + θ) (b := 1) (η := θ) (by linarith)
    (by linarith) (by norm_num) (by norm_num) hθ (by ring)
  obtain ⟨B3, hB3, hK⟩ := hairerKernelTorus_abs_le_indicator N
  obtain ⟨C1, hC1, hG⟩ := hairerKernelTorusGrad_abs_le_rpow N hθ.le
  set Kb : ℝ := 2 * (80 / (5 - (3 + 1)) + 2 * 2) with hKb
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  refine ⟨C₂ * (2 * B3 * Kb + 3 * C1 * Ca), by positivity, ?_⟩
  intro ε hε hε1 x t a g hxg
  have hQm : Measurable (hairerCovariance N ρ ε) :=
    constantsComparison_hairerCovariance_measurable N ρ hε hρ hε1
  set r := parabolicNorm (t, a) with hrdef
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hai : ∀ i, |a i| ≤ r := fun i => by
    refine (Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)).trans ?_
    simp only [hrdef, parabolicNorm]
    linarith [Real.sqrt_nonneg |t|]
  set v : SpaceTime := x + (t, torusProj a) with hv
  have hTm : Measurable (hairerTaylorKernel N x t a) := measurable_hairerTaylorKernel N x t a
  have hGm : Measurable (fun w => hairerCovariance N ρ ε (w - g)) :=
    hQm.comp (measurable_id.sub_const g)
  have S1 := singularIntLe_slabAt_mul_two (a := 3) (b := 1) (T := 2) v.1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) v g
  have S2 := singularIntLe_slabAt_mul_two (a := 3) (b := 1) (T := 2) x.1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) x g
  have S3 := (hA x g hxg).const_mul (c := 3 * C1 * r) (by positivity)
  have S := ((S1.const_mul hB3).add (S2.const_mul hB3)).add S3
  have hfin : SingularIntLe (fun w => |hairerTaylorKernel N x t a w *
      hairerCovariance N ρ ε (w - g)|) (C₂ * ((B3 * Kb + B3 * Kb) +
        3 * C1 * r * (Ca * torusParabolicSize (x - g) ^ (-θ)))) := by
    refine (S.const_mul hC₂).of_le (F := fun w => |hairerTaylorKernel N x t a w *
      hairerCovariance N ρ ε (w - g)|) (hTm.mul hGm).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => abs_nonneg _) ?_
    filter_upwards [ae_torusParabolicSize_sub_pos x, ae_torusParabolicSize_sub_pos v,
      ae_torusParabolicSize_sub_pos g] with w hx hv' hg
    have hG' := hQ hε hε1 g w hg
    have k1 := hK v w hv'
    have k2 := hK x w hx
    have g1 : ∀ i : Fin 3, |hairerKernelTorusGrad N i (x - w)| ≤
        C1 * singularPow (4 + θ) x w := fun i => by simpa [singularPow] using hG i hx
    have hT : |hairerTaylorKernel N x t a w| ≤
        B3 * Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2} (singularPow 3 v) w +
        B3 * Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2} (singularPow 3 x) w +
        3 * C1 * r * singularPow (4 + θ) x w := by
      have hsum : |∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i| ≤
          3 * C1 * r * singularPow (4 + θ) x w := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hterm : ∀ i : Fin 3, |hairerKernelTorusGrad N i (x - w) * a i| ≤
            C1 * r * singularPow (4 + θ) x w := fun i => by
          rw [abs_mul]
          calc _ ≤ (C1 * singularPow (4 + θ) x w) * r :=
                mul_le_mul (g1 i) (hai i) (abs_nonneg _)
                  (mul_nonneg hC1 (singularPow_nonneg _ _ _))
            _ = _ := by ring
        calc _ ≤ ∑ _i : Fin 3, C1 * r * singularPow (4 + θ) x w :=
              Finset.sum_le_sum fun i _ => hterm i
          _ = _ := by simp; ring
      unfold hairerTaylorKernel
      have e1 := abs_sub (hairerKernelTorus N (x + (t, torusProj a) - w) -
        hairerKernelTorus N (x - w)) (∑ i : Fin 3, hairerKernelTorusGrad N i (x - w) * a i)
      have e2 := abs_sub (hairerKernelTorus N (x + (t, torusProj a) - w))
        (hairerKernelTorus N (x - w))
      linarith
    have nI1 : 0 ≤ Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2} (singularPow 3 v) w :=
      Set.indicator_nonneg (fun w _ => singularPow_nonneg _ _ _) w
    have nI2 : 0 ≤ Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2} (singularPow 3 x) w :=
      Set.indicator_nonneg (fun w _ => singularPow_nonneg _ _ _) w
    have nG := singularPow_nonneg 1 g w
    rw [abs_mul]
    have n3 : 0 ≤ 3 * C1 * r * singularPow (4 + θ) x w :=
      mul_nonneg (by positivity) (singularPow_nonneg _ _ _)
    refine (mul_le_mul hT hG' (abs_nonneg _)
      (add_nonneg (add_nonneg (mul_nonneg hB3 nI1) (mul_nonneg hB3 nI2)) n3)).trans ?_
    have e1 : Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2}
        (fun w => singularPow 3 v w * singularPow 1 g w) w =
        Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2} (singularPow 3 v) w * singularPow 1 g w := by
      by_cases h : |w.1 - v.1| ≤ 2 <;> simp [h]
    have e2 : Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2}
        (fun w => singularPow 3 x w * singularPow 1 g w) w =
        Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2} (singularPow 3 x) w * singularPow 1 g w := by
      by_cases h : |w.1 - x.1| ≤ 2 <;> simp [h]
    show _ ≤ C₂ * (B3 * Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2}
        (fun w => singularPow 3 v w * singularPow 1 g w) w +
      B3 * Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2}
        (fun w => singularPow 3 x w * singularPow 1 g w) w +
      3 * C1 * r * (singularPow (4 + θ) x w * singularPow 1 g w))
    rw [e1, e2]
    linarith [mul_nonneg nI1 nG, mul_nonneg nI2 nG]
  have hint : Integrable (fun w => hairerTaylorKernel N x t a w *
      hairerCovariance N ρ ε (w - g)) :=
    (integrable_norm_iff (hTm.mul hGm).aestronglyMeasurable).1 (by simpa using hfin.1)
  refine ⟨hint, ?_⟩
  have h1 : |∫ w, hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)| ≤
      ∫ w, |hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g)| := by
    simpa using norm_integral_le_integral_norm
      (fun w => hairerTaylorKernel N x t a w * hairerCovariance N ρ ε (w - g))
  refine h1.trans (hfin.2.trans ?_)
  have hE : 0 ≤ torusParabolicSize (x - g) ^ (-θ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have h0 : 0 ≤ C₂ * (B3 * Kb) := by positivity
  have h2 : 0 ≤ C₂ * (C1 * Ca) := by positivity
  have h3 : 0 ≤ C₂ * (C1 * Ca) * (r * torusParabolicSize (x - g) ^ (-θ)) := by positivity
  have h4 : 0 ≤ C₂ * (B3 * Kb) * (r + torusParabolicSize (x - g) ^ (-θ) +
      r * torusParabolicSize (x - g) ^ (-θ)) := by positivity
  have h5 : 0 ≤ C₂ * (C1 * Ca) * (1 + r + torusParabolicSize (x - g) ^ (-θ)) := by positivity
  linarith [h0, h2, h3, h4, h5]

/-- **Key pairing bound.**  For `g ≠ proj x`, uniformly in `ε ∈ (0, 1]`, `x`, `y`:
`|∫ T_{x,y}(w) Q(w - g) dw| ≤ C r^γ (1 + r) (1 + s(proj x - g)^(-θ))`, `r = ‖y - x‖_𝔰`. -/
theorem ipsiTaylorKernel_pairing_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {θ γ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hγ1 : γ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ (x y : ParabolicSpace) {g : SpaceTime},
      0 < torusParabolicSize (spaceTimeProj x - g) →
        Integrable (fun w => ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - g)) ∧
        |∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - g)| ≤
          C * (parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
            (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by
  obtain ⟨Cs, hCs, hs⟩ := hairerTaylorKernel_pairing_le_small N hρ hθ hθ1 hγ hγ1
  obtain ⟨Cc, hCc, hc⟩ := hairerTaylorKernel_pairing_le_crude N hρ hθ hθ1
  refine ⟨Cs + 2 * Cc, by positivity, ?_⟩
  intro ε hε hε1 x y g hxg
  have hn : parabolicNorm (y - x) = parabolicNorm (y.1 - x.1, y.2 - x.2) := rfl
  rw [hn]
  set r := parabolicNorm (y.1 - x.1, y.2 - x.2) with hr
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hE : 0 ≤ torusParabolicSize (spaceTimeProj x - g) ^ (-θ) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hPg : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
  unfold ipsiTaylorKernel
  by_cases hsm : r ≤ 1 / 2
  · obtain ⟨hi, hb⟩ := hs hε hε1 (x := spaceTimeProj x) (t := y.1 - x.1) (a := y.2 - x.2)
      (g := g) hsm hxg
    refine ⟨hi, hb.trans ?_⟩
    have h1 : r ^ γ * 1 ≤ r ^ γ * (1 + r) := mul_le_mul_of_nonneg_left (by linarith) hPg
    have h2 : 0 ≤ (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by linarith
    have h3 : r ^ γ ≤ r ^ γ * (1 + r) := by linarith
    calc _ ≤ Cs * (r ^ γ * (1 + r)) * (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by
          have := mul_le_mul_of_nonneg_left h3 hCs
          have := mul_le_mul_of_nonneg_right this h2
          linarith
      _ ≤ _ := by
          have : 0 ≤ r ^ γ * (1 + r) * (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by
            positivity
          linarith [mul_nonneg hCc this]
  · have hbig : 1 / 2 < r := lt_of_not_ge hsm
    obtain ⟨hi, hb⟩ := hc hε hε1 (x := spaceTimeProj x) (t := y.1 - x.1) (a := y.2 - x.2)
      (g := g) hxg
    refine ⟨hi, hb.trans ?_⟩
    have hrg : 1 / 2 ≤ r ^ γ := by
      have : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ γ :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hγ1.le
      have h2 : (1 / 2 : ℝ) ^ γ ≤ r ^ γ := Real.rpow_le_rpow (by norm_num) hbig.le hγ.le
      simpa using this.trans h2
    have h2 : 0 ≤ (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by linarith
    have hh : (1 + r) ≤ 2 * (r ^ γ * (1 + r)) := by nlinarith
    calc Cc * (1 + r) * (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ))
        ≤ Cc * (2 * (r ^ γ * (1 + r))) * (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by
          have := mul_le_mul_of_nonneg_left hh hCc
          exact mul_le_mul_of_nonneg_right this h2
      _ ≤ _ := by
          have : 0 ≤ r ^ γ * (1 + r) * (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-θ)) := by
            positivity
          linarith [mul_nonneg hCs this]

end RegularityStructures.Phi43

end
