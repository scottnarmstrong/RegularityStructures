/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovLint
public import Phi43.BPHZ.ProductIPsiPsiDiffKernel
import Mathlib.Tactic

/-!
# Pairing of the Taylor kernel with a kernel `Φ(z) ≲ s(z)^(-b)`

Generalisation of `ProductIPsiPsiCovLint` from `Φ = Q` (`b = 1`) to an arbitrary measurable kernel
with `|Φ z| ≤ K s(z)^(-b)`, `1 ≤ b < 2`: for `g ≠ proj x`
`|∫ T(w) Φ(w - g) dw| ≤ C K r^γ (1 + r) (1 + s(proj x - g)^(-(θ + b - 1)))`
(`ipsiTaylorKernel_pairing_gen`).  The exponent `θ + b - 1` of the singularity at `g` records the
convolution of `s^(-(4+θ))` with `s^(-b)`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Small-`r` pairing bound.** -/
theorem hairerTaylorKernel_pairing_gen_small (N : ℕ)     {θ γ b : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hγ : 0 < γ) (hγ1 : γ < 1) (hb1 : 1 ≤ b)
    (hbγ : γ + b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Φ : SpaceTime → ℝ} {K : ℝ}, Measurable Φ → 0 ≤ K →
      (∀ z, 0 < torusParabolicSize z → |Φ z| ≤ K * torusParabolicSize z ^ (-b)) → ∀ {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ}
      {g : SpaceTime}, parabolicNorm (t, a) ≤ 1 / 2 → 0 < torusParabolicSize (x - g) →
        Integrable (fun w => hairerTaylorKernel N x t a w * Φ (w - g)) ∧
        |∫ w, hairerTaylorKernel N x t a w * Φ (w - g)| ≤
          C * K * parabolicNorm (t, a) ^ γ * (1 + torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by
  obtain ⟨M, hM, hMaj⟩ := hairerTaylorKernel_refined_majorant N (θ := θ) (γ := γ) hθ.le hθ1.le
    hγ.le (by linarith)
  obtain ⟨Ca, hCa, hA⟩ := singularIntLe_mul_two (a := 4 + θ) (b := b) (η := θ + b - 1)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  set Kb : ℝ := 2 * (80 / (5 - ((3 + γ) + b)) + 2 * 2) with hKb
  have hKb0 : 0 ≤ Kb := by
    have : 0 ≤ 80 / (5 - ((3 + γ) + b)) := div_nonneg (by norm_num) (by linarith)
    rw [hKb]; positivity
  refine ⟨M * (Ca + 2 * Kb), by positivity, ?_⟩
  intro Φ K hΦm hK0 hΦb x t a g hr hxg
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
  have hGm : Measurable (fun w => Φ (w - g)) :=
    hΦm.comp (measurable_id.sub_const g)
  -- the integrable majorants
  have S1 := (hA x g hxg).const_mul (c := r ^ (1 + θ)) (Real.rpow_nonneg hr0 _)
  have S2 := (singularIntLe_slabAt_mul_two (a := 3 + γ) (b := b) (T := 2) x.1 (by linarith)
    (by linarith) (by linarith) (by norm_num) v g)
  have S3 := (singularIntLe_slabAt_mul_two (a := 3 + γ) (b := b) (T := 2) x.1 (by linarith)
    (by linarith) (by linarith) (by norm_num) x g)
  have S23 := (S2.add S3).const_mul (c := r ^ γ) (Real.rpow_nonneg hr0 _)
  have S := (S1.add S23).const_mul (c := K * M) (by positivity)
  have hfin : SingularIntLe (fun w => |hairerTaylorKernel N x t a w *
      Φ (w - g)|)
      (K * M * (r ^ (1 + θ) * (Ca * torusParabolicSize (x - g) ^ (-(θ + b - 1))) +
        r ^ γ * (Kb + Kb))) := by
    refine S.of_le (F := fun w => |hairerTaylorKernel N x t a w *
      Φ (w - g)|) (hTm.mul hGm).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => abs_nonneg _) ?_
    filter_upwards [ae_torusParabolicSize_sub_pos x, ae_torusParabolicSize_sub_pos v,
      ae_torusParabolicSize_sub_pos g] with w hx hv' hg
    have hT := hMaj hai ht w hx hv'
    have hG : |Φ (w - g)| ≤ K * singularPow b g w := by
      have hsz : torusParabolicSize (w - g) = torusParabolicSize (g - w) := ipsi_size_swap _ _
      have := hΦb (w - g) (by rw [hsz]; exact hg)
      simpa [singularPow, hsz] using this
    have hsl0 := i2Psi2Slab_nonneg x.1 w
    have hsl1 := i2Psi2Slab_le_one x.1 w
    have e2 := ipsi_slab_mul_eq_indicator x.1
      (fun w => singularPow (3 + γ) v w * singularPow b g w) w
    have e3 := ipsi_slab_mul_eq_indicator x.1
      (fun w => singularPow (3 + γ) x w * singularPow b g w) w
    have nA := singularPow_nonneg (4 + θ) x w
    have nB := singularPow_nonneg (3 + γ) v w
    have nC := singularPow_nonneg (3 + γ) x w
    have nG := singularPow_nonneg b g w
    have hP1 : 0 ≤ r ^ (1 + θ) := Real.rpow_nonneg hr0 _
    have hPg : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
    rw [abs_mul]
    have hmain : |hairerTaylorKernel N x t a w| * |Φ (w - g)| ≤
        (i2Psi2Slab x.1 w * (M * (r ^ (1 + θ) * singularPow (4 + θ) x w +
          r ^ γ * (singularPow (3 + γ) v w + singularPow (3 + γ) x w)))) *
          (K * singularPow b g w) :=
      mul_le_mul hT hG (abs_nonneg _) (by positivity)
    refine hmain.trans ?_
    simp only [singularPow] at e2 e3 nA nB nC nG ⊢
    have key : i2Psi2Slab x.1 w * (M * (r ^ (1 + θ) * torusParabolicSize (x - w) ^ (-(4 + θ)) +
          r ^ γ * (torusParabolicSize (v - w) ^ (-(3 + γ)) +
            torusParabolicSize (x - w) ^ (-(3 + γ))))) *
        (K * torusParabolicSize (g - w) ^ (-b)) =
        K * M * (r ^ (1 + θ) * (i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
            torusParabolicSize (g - w) ^ (-b))) +
          r ^ γ * (i2Psi2Slab x.1 w * (torusParabolicSize (v - w) ^ (-(3 + γ)) *
            torusParabolicSize (g - w) ^ (-b)) +
            i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(3 + γ)) *
            torusParabolicSize (g - w) ^ (-b)))) := by ring
    rw [key, e2, e3]
    have : i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
        torusParabolicSize (g - w) ^ (-b)) ≤
        torusParabolicSize (x - w) ^ (-(4 + θ)) * torusParabolicSize (g - w) ^ (-b) :=
      mul_le_of_le_one_left (mul_nonneg nA nG) hsl1
    have h4 : r ^ (1 + θ) * (i2Psi2Slab x.1 w * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
        torusParabolicSize (g - w) ^ (-b))) ≤
        r ^ (1 + θ) * (torusParabolicSize (x - w) ^ (-(4 + θ)) *
        torusParabolicSize (g - w) ^ (-b)) := mul_le_mul_of_nonneg_left this hP1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hint : Integrable (fun w => hairerTaylorKernel N x t a w *
      Φ (w - g)) := by
    have := hfin.1
    exact (integrable_norm_iff (hTm.mul hGm).aestronglyMeasurable).1 (by simpa using this)
  refine ⟨hint, ?_⟩
  have h1 : |∫ w, hairerTaylorKernel N x t a w * Φ (w - g)| ≤
      ∫ w, |hairerTaylorKernel N x t a w * Φ (w - g)| := by
    simpa using norm_integral_le_integral_norm
      (fun w => hairerTaylorKernel N x t a w * Φ (w - g))
  refine h1.trans (hfin.2.trans ?_)
  have hrg : r ^ (1 + θ) ≤ r ^ γ :=
    Real.rpow_le_rpow_of_exponent_ge' hr0 (by linarith) hγ.le (by linarith)
  have hE : 0 ≤ torusParabolicSize (x - g) ^ (-(θ + b - 1)) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hPg : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
  have hP1 : 0 ≤ r ^ (1 + θ) := Real.rpow_nonneg hr0 _
  have hCM : 0 ≤ K * M := by positivity
  calc K * M * (r ^ (1 + θ) * (Ca * torusParabolicSize (x - g) ^ (-(θ + b - 1))) + r ^ γ * (Kb + Kb))
      ≤ K * M * (r ^ γ * (Ca * torusParabolicSize (x - g) ^ (-(θ + b - 1))) + r ^ γ * (Kb + Kb)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCM
        have := mul_le_mul_of_nonneg_right hrg (mul_nonneg hCa hE)
        linarith
    _ ≤ M * (Ca + 2 * Kb) * K * r ^ γ * (1 + torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by
        have : 0 ≤ r ^ γ * (Ca * torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by positivity
        have h2 : r ^ γ * (Ca * torusParabolicSize (x - g) ^ (-(θ + b - 1))) + r ^ γ * (Kb + Kb) ≤
            (Ca + 2 * Kb) * r ^ γ * (1 + torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by
          have h3 : 0 ≤ r ^ γ * Kb := mul_nonneg hPg hKb0
          have h4 : 0 ≤ r ^ γ * (Kb * torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by positivity
          nlinarith
        calc _ ≤ K * M * ((Ca + 2 * Kb) * r ^ γ * (1 + torusParabolicSize (x - g) ^ (-(θ + b - 1)))) :=
              mul_le_mul_of_nonneg_left h2 hCM
          _ = _ := by ring


/-- **Crude pairing bound, all `r`.** -/
theorem hairerTaylorKernel_pairing_gen_crude (N : ℕ) {θ b : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hb1 : 1 ≤ b) (hb2 : b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Φ : SpaceTime → ℝ} {K : ℝ}, Measurable Φ → 0 ≤ K →
      (∀ z, 0 < torusParabolicSize z → |Φ z| ≤ K * torusParabolicSize z ^ (-b)) →
      ∀ {x : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ} {g : SpaceTime}, 0 < torusParabolicSize (x - g) →
        Integrable (fun w => hairerTaylorKernel N x t a w * Φ (w - g)) ∧
        |∫ w, hairerTaylorKernel N x t a w * Φ (w - g)| ≤
          C * K * (1 + parabolicNorm (t, a)) * (1 + torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by
  obtain ⟨Ca, hCa, hA⟩ := singularIntLe_mul_two (a := 4 + θ) (b := b) (η := θ + b - 1)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by ring)
  obtain ⟨B3, hB3, hK⟩ := hairerKernelTorus_abs_le_indicator N
  obtain ⟨C1, hC1, hG⟩ := hairerKernelTorusGrad_abs_le_rpow N hθ.le
  set Kb : ℝ := 2 * (80 / (5 - (3 + b)) + 2 * 2) with hKb
  have hKb0 : 0 ≤ Kb := by
    have : 0 ≤ 80 / (5 - (3 + b)) := div_nonneg (by norm_num) (by linarith)
    rw [hKb]; positivity
  refine ⟨2 * B3 * Kb + 3 * C1 * Ca, by positivity, ?_⟩
  intro Φ K hΦm hK0 hΦb x t a g hxg
  set r := parabolicNorm (t, a) with hrdef
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hai : ∀ i, |a i| ≤ r := fun i => by
    refine (Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)).trans ?_
    simp only [hrdef, parabolicNorm]
    linarith [Real.sqrt_nonneg |t|]
  set v : SpaceTime := x + (t, torusProj a) with hv
  have hTm : Measurable (hairerTaylorKernel N x t a) := measurable_hairerTaylorKernel N x t a
  have hGm : Measurable (fun w => Φ (w - g)) :=
    hΦm.comp (measurable_id.sub_const g)
  have S1 := singularIntLe_slabAt_mul_two (a := 3) (b := b) (T := 2) v.1 (by norm_num)
    (by linarith) (by linarith) (by norm_num) v g
  have S2 := singularIntLe_slabAt_mul_two (a := 3) (b := b) (T := 2) x.1 (by norm_num)
    (by linarith) (by linarith) (by norm_num) x g
  have S3 := (hA x g hxg).const_mul (c := 3 * C1 * r) (by positivity)
  have S := ((S1.const_mul hB3).add (S2.const_mul hB3)).add S3
  have hfin : SingularIntLe (fun w => |hairerTaylorKernel N x t a w *
      Φ (w - g)|) (K * ((B3 * Kb + B3 * Kb) +
        3 * C1 * r * (Ca * torusParabolicSize (x - g) ^ (-(θ + b - 1))))) := by
    refine (S.const_mul hK0).of_le (F := fun w => |hairerTaylorKernel N x t a w *
      Φ (w - g)|) (hTm.mul hGm).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => abs_nonneg _) ?_
    filter_upwards [ae_torusParabolicSize_sub_pos x, ae_torusParabolicSize_sub_pos v,
      ae_torusParabolicSize_sub_pos g] with w hx hv' hg
    have hG' : |Φ (w - g)| ≤ K * singularPow b g w := by
      have hsz : torusParabolicSize (w - g) = torusParabolicSize (g - w) := ipsi_size_swap _ _
      have := hΦb (w - g) (by rw [hsz]; exact hg)
      simpa [singularPow, hsz] using this
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
    have nG := singularPow_nonneg b g w
    rw [abs_mul]
    have n3 : 0 ≤ 3 * C1 * r * singularPow (4 + θ) x w :=
      mul_nonneg (by positivity) (singularPow_nonneg _ _ _)
    refine (mul_le_mul hT hG' (abs_nonneg _)
      (add_nonneg (add_nonneg (mul_nonneg hB3 nI1) (mul_nonneg hB3 nI2)) n3)).trans ?_
    have e1 : Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2}
        (fun w => singularPow 3 v w * singularPow b g w) w =
        Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2} (singularPow 3 v) w * singularPow b g w := by
      by_cases h : |w.1 - v.1| ≤ 2 <;> simp [h]
    have e2 : Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2}
        (fun w => singularPow 3 x w * singularPow b g w) w =
        Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2} (singularPow 3 x) w * singularPow b g w := by
      by_cases h : |w.1 - x.1| ≤ 2 <;> simp [h]
    show _ ≤ K * (B3 * Set.indicator {w : SpaceTime | |w.1 - v.1| ≤ 2}
        (fun w => singularPow 3 v w * singularPow b g w) w +
      B3 * Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ 2}
        (fun w => singularPow 3 x w * singularPow b g w) w +
      3 * C1 * r * (singularPow (4 + θ) x w * singularPow b g w))
    rw [e1, e2]
    linarith [mul_nonneg nI1 nG, mul_nonneg nI2 nG]
  have hint : Integrable (fun w => hairerTaylorKernel N x t a w *
      Φ (w - g)) :=
    (integrable_norm_iff (hTm.mul hGm).aestronglyMeasurable).1 (by simpa using hfin.1)
  refine ⟨hint, ?_⟩
  have h1 : |∫ w, hairerTaylorKernel N x t a w * Φ (w - g)| ≤
      ∫ w, |hairerTaylorKernel N x t a w * Φ (w - g)| := by
    simpa using norm_integral_le_integral_norm
      (fun w => hairerTaylorKernel N x t a w * Φ (w - g))
  refine h1.trans (hfin.2.trans ?_)
  have hE : 0 ≤ torusParabolicSize (x - g) ^ (-(θ + b - 1)) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have h0 : 0 ≤ K * (B3 * Kb) := by positivity
  have h2 : 0 ≤ K * (C1 * Ca) := by positivity
  have h3 : 0 ≤ K * (C1 * Ca) * (r * torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by positivity
  have h4 : 0 ≤ K * (B3 * Kb) * (r + torusParabolicSize (x - g) ^ (-(θ + b - 1)) +
      r * torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by positivity
  have h5 : 0 ≤ K * (C1 * Ca) * (1 + r + torusParabolicSize (x - g) ^ (-(θ + b - 1))) := by positivity
  linarith [h0, h2, h3, h4, h5]


/-- **General key pairing bound.**  For `g ≠ proj x`, any measurable `Φ` with
`|Φ z| ≤ K s(z)^(-b)`: `|∫ T_{x,y}(w) Φ(w - g) dw| ≤
C K r^γ (1 + r) (1 + s(proj x - g)^(-(θ + b - 1)))`, `r = ‖y - x‖_𝔰`. -/
theorem ipsiTaylorKernel_pairing_gen (N : ℕ) {θ γ b : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hb1 : 1 ≤ b) (hbγ : γ + b < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Φ : SpaceTime → ℝ} {K : ℝ}, Measurable Φ → 0 ≤ K →
      (∀ z, 0 < torusParabolicSize z → |Φ z| ≤ K * torusParabolicSize z ^ (-b)) →
      ∀ (x y : ParabolicSpace) {g : SpaceTime},
      0 < torusParabolicSize (spaceTimeProj x - g) →
        Integrable (fun w => ipsiTaylorKernel N x y w * Φ (w - g)) ∧
        |∫ w, ipsiTaylorKernel N x y w * Φ (w - g)| ≤
          C * K * (parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
            (1 + torusParabolicSize (spaceTimeProj x - g) ^ (-(θ + b - 1))) := by
  obtain ⟨Cs, hCs, hs⟩ := hairerTaylorKernel_pairing_gen_small N hθ hθ1 hγ hγ1 hb1 hbγ
  obtain ⟨Cc, hCc, hc⟩ := hairerTaylorKernel_pairing_gen_crude N hθ hθ1 hb1 (by linarith)
  refine ⟨Cs + 2 * Cc, by positivity, ?_⟩
  intro Φ K hΦm hK0 hΦb x y g hxg
  have hn : parabolicNorm (y - x) = parabolicNorm (y.1 - x.1, y.2 - x.2) := rfl
  rw [hn]
  set r := parabolicNorm (y.1 - x.1, y.2 - x.2) with hr
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  set E := 1 + torusParabolicSize (spaceTimeProj x - g) ^ (-(θ + b - 1)) with hEdef
  have hE0 : 0 ≤ E := by
    have := Real.rpow_nonneg (torusParabolicSize_nonneg (spaceTimeProj x - g)) (-(θ + b - 1))
    rw [hEdef]; linarith
  have hPg : 0 ≤ r ^ γ := Real.rpow_nonneg hr0 _
  have hB : 0 ≤ r ^ γ * (1 + r) := mul_nonneg hPg (by linarith)
  have hKE : 0 ≤ K * E := mul_nonneg hK0 hE0
  unfold ipsiTaylorKernel
  by_cases hsm : r ≤ 1 / 2
  · obtain ⟨hi, hb⟩ := hs hΦm hK0 hΦb (x := spaceTimeProj x) (t := y.1 - x.1) (a := y.2 - x.2)
      (g := g) hsm hxg
    refine ⟨hi, hb.trans ?_⟩
    have hAB : r ^ γ ≤ r ^ γ * (1 + r) := by nlinarith
    have k1 := mul_nonneg (mul_nonneg hCs hKE) (sub_nonneg.2 hAB)
    have k2 := mul_nonneg (mul_nonneg hCc hKE) hB
    linarith [k1, k2]
  · have hbig : 1 / 2 < r := lt_of_not_ge hsm
    obtain ⟨hi, hb⟩ := hc hΦm hK0 hΦb (x := spaceTimeProj x) (t := y.1 - x.1) (a := y.2 - x.2)
      (g := g) hxg
    refine ⟨hi, hb.trans ?_⟩
    have hrg : 1 / 2 ≤ r ^ γ := by
      have : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ γ :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hγ1.le
      have h2 : (1 / 2 : ℝ) ^ γ ≤ r ^ γ := Real.rpow_le_rpow (by norm_num) hbig.le hγ.le
      simpa using this.trans h2
    have hh : (1 + r) ≤ 2 * (r ^ γ * (1 + r)) := by nlinarith
    have k1 := mul_nonneg (mul_nonneg hCc hKE) (sub_nonneg.2 hh)
    have k2 := mul_nonneg (mul_nonneg hCs hKE) hB
    linarith [k1, k2]

end RegularityStructures.Phi43

end
