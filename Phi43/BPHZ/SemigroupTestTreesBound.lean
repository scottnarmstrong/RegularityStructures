/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestKernel
public import Phi43.BPHZ.TreeI3Psi2TestedSize

/-!
# A calculus of double-integral bounds against a semigroup test profile

`SemigroupDoubleBound g F I` records that `(u, v) ↦ |g u| |g v| F u v` is integrable on
`SpaceTime × SpaceTime` with integral at most `I`.  It is stable under sums, nonnegative multiples
and domination, and the basic weights `s(u - x)^ζ s(u - v)^e`, `s(v - x)^ζ s(u - v)^e` and
`s(u - x)^a s(v - x)^b` are bounded by `SemigroupTestProfile.integral_double_le` and
`SemigroupTestProfile.integral_rpow_le`.

A covariance function is bounded through a local majorant (valid when
`s(u - x), s(v - x) ≤ 1`) and a global majorant (valid otherwise).
`SemigroupTestProfile.doubleBound_global` bounds the global majorant
`(s(u - x)^n + s(v - x)^n) (s(u - v)^(-e) + s(u - x)^(-a) + s(v - x)^(-a) + 1)` by a constant for
`lam ≤ 1`: the polynomial growth is absorbed by the moments of the profile.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- `(u, v) ↦ |g u| |g v| F u v` is integrable with integral at most `I`. -/
def SemigroupDoubleBound (g : SpaceTime → ℝ) (F : SpaceTime → SpaceTime → ℝ) (I : ℝ) : Prop :=
  Integrable (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| * F w.1 w.2) ∧
    ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| * F w.1 w.2 ≤ I

/-- The constant of `SemigroupTestProfile.doubleBound_global`. -/
def semigroupTestGlobalConst (B : ℝ) (Mom : ℝ → ℝ) (n e a : ℝ) : ℝ :=
  semigroupTestDoubleConst B Mom n (-e) + semigroupTestDoubleConst B Mom n (-e) +
    semigroupTestDoubleConst B Mom (n - a) 0 + semigroupTestDoubleConst B Mom (n - a) 0 +
    semigroupTestMomConst B Mom (-a) * semigroupTestMomConst B Mom n +
    semigroupTestMomConst B Mom n * semigroupTestMomConst B Mom (-a) +
    semigroupTestDoubleConst B Mom n 0 + semigroupTestDoubleConst B Mom n 0

/-- The global majorant `(s(u - x)^n + s(v - x)^n)
(s(u - v)^(-e) + s(u - x)^(-a) + s(v - x)^(-a) + 1)`, written as a sum of eight monomials. -/
def semigroupTestGlobalMajorant (x : SpaceTime) (n e a : ℝ) (u v : SpaceTime) : ℝ :=
  torusParabolicSize (u - x) ^ n * torusParabolicSize (u - v) ^ (-e) +
    torusParabolicSize (v - x) ^ n * torusParabolicSize (u - v) ^ (-e) +
    torusParabolicSize (u - x) ^ (n - a) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ (n - a) * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (u - x) ^ (-a) * torusParabolicSize (v - x) ^ n +
    torusParabolicSize (u - x) ^ n * torusParabolicSize (v - x) ^ (-a) +
    torusParabolicSize (u - x) ^ n * torusParabolicSize (u - v) ^ (0 : ℝ) +
    torusParabolicSize (v - x) ^ n * torusParabolicSize (u - v) ^ (0 : ℝ)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

namespace SemigroupDoubleBound

variable {g : SpaceTime → ℝ} {F G : SpaceTime → SpaceTime → ℝ} {I J : ℝ}

theorem add (hF : SemigroupDoubleBound g F I) (hG : SemigroupDoubleBound g G J) :
    SemigroupDoubleBound g (fun u v => F u v + G u v) (I + J) := by
  refine ⟨(hF.1.add hG.1).congr (Filter.Eventually.of_forall fun w => ?_), ?_⟩
  · simp only [Pi.add_apply]
    ring
  · have e : ∀ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| * (F w.1 w.2 + G w.1 w.2) =
        |g w.1| * |g w.2| * F w.1 w.2 + |g w.1| * |g w.2| * G w.1 w.2 := fun w => by ring
    simp only [e]
    rw [integral_add hF.1 hG.1]
    exact add_le_add hF.2 hG.2

theorem const_mul (hF : SemigroupDoubleBound g F I) {c : ℝ} (hc : 0 ≤ c) :
    SemigroupDoubleBound g (fun u v => c * F u v) (c * I) := by
  refine ⟨(hF.1.const_mul c).congr (Filter.Eventually.of_forall fun w => ?_), ?_⟩
  · simp only
    ring
  · have e : ∀ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| * (c * F w.1 w.2) =
        c * (|g w.1| * |g w.2| * F w.1 w.2) := fun w => by ring
    simp only [e]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hF.2 hc

theorem mono_right (hF : SemigroupDoubleBound g F I) (hIJ : I ≤ J) :
    SemigroupDoubleBound g F J :=
  ⟨hF.1, hF.2.trans hIJ⟩

theorem congr_ae (hF : SemigroupDoubleBound g F I)
    (h : ∀ᵐ w : SpaceTime × SpaceTime ∂volume, F w.1 w.2 = G w.1 w.2) :
    SemigroupDoubleBound g G I := by
  have e : (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| * F w.1 w.2) =ᵐ[volume]
      fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| * G w.1 w.2 := by
    filter_upwards [h] with w hw
    rw [hw]
  exact ⟨hF.1.congr e, by rw [← integral_congr_ae e]; exact hF.2⟩

/-- Domination: an almost everywhere bound `|F| ≤ G` by a bounded integrand transfers the bound. -/
theorem of_abs_le (hg : Measurable g) (hG : SemigroupDoubleBound g G I)
    (hF : AEStronglyMeasurable (fun w : SpaceTime × SpaceTime => F w.1 w.2) volume)
    (hle : ∀ᵐ w : SpaceTime × SpaceTime ∂volume, |F w.1 w.2| ≤ G w.1 w.2) :
    SemigroupDoubleBound g (fun u v => |F u v|) I := by
  have hgg : ∀ w : SpaceTime × SpaceTime, 0 ≤ |g w.1| * |g w.2| := fun w =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (fun w : SpaceTime × SpaceTime =>
      |g w.1| * |g w.2| * |F w.1 w.2|) volume :=
    (((continuous_abs.measurable.comp hg).comp measurable_fst).mul
      ((continuous_abs.measurable.comp hg).comp measurable_snd)).aestronglyMeasurable.mul
      (continuous_abs.comp_aestronglyMeasurable hF)
  have hle' : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      |g w.1| * |g w.2| * |F w.1 w.2| ≤ |g w.1| * |g w.2| * G w.1 w.2 := by
    filter_upwards [hle] with w hw
    exact mul_le_mul_of_nonneg_left hw (hgg w)
  refine ⟨hG.1.mono' hmeas ?_, ?_⟩
  · filter_upwards [hle'] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hgg w) (abs_nonneg _))]
    exact hw
  · exact (integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
      mul_nonneg (hgg w) (abs_nonneg _)) hG.1 hle').trans hG.2

end SemigroupDoubleBound

namespace SemigroupTestProfile

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

theorem semigroupTestMomConst_nonneg (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    {a : ℝ} (ha : -5 < a) : 0 ≤ semigroupTestMomConst B Mom a := by
  unfold semigroupTestMomConst
  split_ifs with ha0
  · exact h.mom_nonneg hlam ha0
  · have hB := h.const_nonneg hlam
    have h0 := h.mom_zero_nonneg
    have : 0 ≤ 80 / (5 + a) := div_nonneg (by norm_num) (by linarith)
    positivity

theorem semigroupTestDoubleConst_nonneg (h : SemigroupTestProfile x lam B Mom g) (hlam : 0 < lam)
    {ζ e : ℝ} (hζ : -5 < ζ) (he : -5 < e) (hζe : -5 < ζ + e) :
    0 ≤ semigroupTestDoubleConst B Mom ζ e := by
  unfold semigroupTestDoubleConst
  have hB := h.const_nonneg hlam
  have h0 := h.mom_zero_nonneg
  have c1 := h.semigroupTestMomConst_nonneg hlam hζ
  split_ifs with he0
  · have : 0 ≤ 80 / (5 + e) := div_nonneg (by norm_num) (by linarith)
    positivity
  · have he' : 0 ≤ e := not_lt.1 he0
    have c2 := h.semigroupTestMomConst_nonneg hlam hζe
    have m1 := h.mom_nonneg hlam he'
    positivity

/-- `∫∫ |g u| |g v| s(u - x)^ζ s(u - v)^e`. -/
theorem doubleBound_fst (h : SemigroupTestProfile x lam B Mom g) {ζ e : ℝ} (hζ : -5 < ζ)
    (he : -5 < e) (hlam : 0 < lam) :
    SemigroupDoubleBound g (fun u v => torusParabolicSize (u - x) ^ ζ *
      torusParabolicSize (u - v) ^ e) (semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e)) :=
  h.integral_double_le hζ he hlam

/-- `∫∫ |g u| |g v| s(v - x)^ζ s(u - v)^e`, by the symmetry `u ↔ v`. -/
theorem doubleBound_snd (h : SemigroupTestProfile x lam B Mom g) {ζ e : ℝ} (hζ : -5 < ζ)
    (he : -5 < e) (hlam : 0 < lam) :
    SemigroupDoubleBound g (fun u v => torusParabolicSize (v - x) ^ ζ *
      torusParabolicSize (u - v) ^ e) (semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e)) := by
  obtain ⟨hi, hb⟩ := h.integral_double_le hζ he hlam
  have hsw : ∀ a b : SpaceTime, torusParabolicSize (b - a) = torusParabolicSize (a - b) := by
    intro a b
    refine le_antisymm ?_ ?_
    · have := torusParabolicSize_neg_le_self (a - b)
      rwa [neg_sub] at this
    · have := torusParabolicSize_neg_le_self (b - a)
      rwa [neg_sub] at this
  have e1 : (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
      (torusParabolicSize (w.2 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e)) =
      (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e)) ∘ Prod.swap := by
    funext w
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, hsw w.1 w.2]
    ring
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact hi.swap
  · rw [e1]
    have := integral_prod_swap (μ := (volume : Measure SpaceTime)) (ν := (volume : Measure SpaceTime))
      (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e))
    rw [Measure.volume_eq_prod]
    simp only [Function.comp_def] at this ⊢
    rw [this]
    exact hb

/-- `∫∫ |g u| |g v| s(u - x)^a s(v - x)^b`. -/
theorem doubleBound_mul (h : SemigroupTestProfile x lam B Mom g) {a b : ℝ} (ha : -5 < a)
    (hb : -5 < b) (hlam : 0 < lam) :
    SemigroupDoubleBound g (fun u v => torusParabolicSize (u - x) ^ a *
      torusParabolicSize (v - x) ^ b)
      (semigroupTestMomConst B Mom a * semigroupTestMomConst B Mom b * lam ^ (a + b)) := by
  obtain ⟨ia, ba⟩ := h.integral_rpow_le ha hlam
  obtain ⟨ib, bb⟩ := h.integral_rpow_le hb hlam
  have e : ∀ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
      (torusParabolicSize (w.1 - x) ^ a * torusParabolicSize (w.2 - x) ^ b) =
      (|g w.1| * torusParabolicSize (w.1 - x) ^ a) *
        (|g w.2| * torusParabolicSize (w.2 - x) ^ b) := fun w => by ring
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact ia.mul_prod ib
  · simp only [e]
    rw [show (∫ w : SpaceTime × SpaceTime, (|g w.1| * torusParabolicSize (w.1 - x) ^ a) *
        (|g w.2| * torusParabolicSize (w.2 - x) ^ b)) =
        (∫ u, |g u| * torusParabolicSize (u - x) ^ a) *
          ∫ v, |g v| * torusParabolicSize (v - x) ^ b from
      integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
        (fun u => |g u| * torusParabolicSize (u - x) ^ a)
        (fun v => |g v| * torusParabolicSize (v - x) ^ b)]
    have n1 : 0 ≤ ∫ u, |g u| * torusParabolicSize (u - x) ^ a :=
      integral_nonneg fun u => mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
    have c1 := h.semigroupTestMomConst_nonneg hlam ha
    have l1 := Real.rpow_nonneg hlam.le a
    calc _ ≤ (semigroupTestMomConst B Mom a * lam ^ a) *
          (semigroupTestMomConst B Mom b * lam ^ b) :=
          mul_le_mul ba bb (integral_nonneg fun v => mul_nonneg (abs_nonneg _)
            (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)) (mul_nonneg c1 l1)
      _ = _ := by rw [Real.rpow_add hlam]; ring

end SemigroupTestProfile

end RegularityStructures

end
