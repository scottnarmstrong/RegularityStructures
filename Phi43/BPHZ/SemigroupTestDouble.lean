/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestProfile
public import Phi43.BPHZ.ChaosReductionIntegralWeights
public import Phi43.BPHZ.KernelCalculusBasic

/-!
# The chaos-reduction double integral for a semigroup test profile

For a semigroup test profile `g` at scale `lam` and base point `x` (see `SemigroupTestProfile`) and
real exponents `ζ, e > -5`,
`∫∫ |g u| |g v| s(u - x)^ζ s(u - v)^e ≤ C lam^(ζ+e)`
(`SemigroupTestProfile.integral_double_le`).  This is the analogue of
`chaosReduction_integral_left` with the compactly supported test function replaced by a profile
with unbounded support, for which only a sup bound and moment bounds are available.

* For `e < 0` the inner integral over `v` is bounded uniformly in `u` by
  `SemigroupTestProfile.integral_mul_rpow_sub_le`.
* For `e ≥ 0` we use `s(u - v)^e ≤ 16^e (s(u - x)^e + s(v - x)^e)` and the moment bounds.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The constant of `SemigroupTestProfile.integral_double_le`. -/
def semigroupTestDoubleConst (B : ℝ) (Mom : ℝ → ℝ) (ζ e : ℝ) : ℝ :=
  if e < 0 then (B * (80 / (5 + e)) + Mom 0) * semigroupTestMomConst B Mom ζ
  else 16 ^ e * (Mom 0 * semigroupTestMomConst B Mom (ζ + e) +
    Mom e * semigroupTestMomConst B Mom ζ)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

/-- The reflected parabolic size is positive almost everywhere. -/
theorem ae_pos_torusParabolicSize_sub_right (x : SpaceTime) :
    ∀ᵐ u : SpaceTime ∂volume, 0 < torusParabolicSize (u - x) := by
  filter_upwards [treePsi_ae_pos_size_sub x] with u hu
  have := chaosSize_flip x u
  linarith

/-- `s(u - v)^e ≤ 16^e (s(u - x)^e + s(v - x)^e)` for `e ≥ 0`. -/
theorem torusParabolicSize_sub_rpow_le {e : ℝ} (he : 0 ≤ e) (u v x : SpaceTime) :
    torusParabolicSize (u - v) ^ e ≤
      16 ^ e * (torusParabolicSize (u - x) ^ e + torusParabolicSize (v - x) ^ e) := by
  have h8 := torusParabolicSize_sub_le_eight_mul (u - x) (v - x)
  rw [sub_sub_sub_cancel_right] at h8
  set a := torusParabolicSize (u - x) with ha
  set b := torusParabolicSize (v - x) with hb
  have ha0 : 0 ≤ a := torusParabolicSize_nonneg _
  have hb0 : 0 ≤ b := torusParabolicSize_nonneg _
  have hsum : a + b ≤ 2 * max a b := by
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have hmax : max a b ^ e ≤ a ^ e + b ^ e := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg ha0 _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hb0 _)
  have hle : torusParabolicSize (u - v) ≤ 16 * max a b := by
    have := le_max_left a b
    linarith
  calc torusParabolicSize (u - v) ^ e ≤ (16 * max a b) ^ e :=
        Real.rpow_le_rpow (torusParabolicSize_nonneg _) hle he
    _ = 16 ^ e * max a b ^ e := Real.mul_rpow (by norm_num) (le_max_of_le_left ha0)
    _ ≤ 16 ^ e * (a ^ e + b ^ e) :=
        mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by norm_num) _)

/-- Fubini for a product `A(u) T(u, v)` whose inner integral is bounded by `K(u)`. -/
theorem integrable_integral_prod_mul_le {A K : SpaceTime → ℝ} {T : SpaceTime → SpaceTime → ℝ}
    (hA : Measurable A) (hA0 : ∀ u, 0 ≤ A u) (hT : Measurable fun w : SpaceTime × SpaceTime =>
      T w.1 w.2) (hT0 : ∀ u v, 0 ≤ T u v)
    (hinner : ∀ u, Integrable (T u) ∧ ∫ v, T u v ≤ K u)
    (hAK : Integrable (fun u => A u * K u)) :
    Integrable (fun w : SpaceTime × SpaceTime => A w.1 * T w.1 w.2) ∧
      ∫ w : SpaceTime × SpaceTime, A w.1 * T w.1 w.2 ≤ ∫ u, A u * K u := by
  have hFm : Measurable (fun w : SpaceTime × SpaceTime => A w.1 * T w.1 w.2) :=
    (hA.comp measurable_fst).mul hT
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ A w.1 * T w.1 w.2 := fun w =>
    mul_nonneg (hA0 _) (hT0 _ _)
  have hinn : ∀ u, ∫ v, ‖A u * T u v‖ = A u * ∫ v, T u v := by
    intro u
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    exact Real.norm_of_nonneg (mul_nonneg (hA0 u) (hT0 u v))
  have hint : Integrable (fun w : SpaceTime × SpaceTime => A w.1 * T w.1 w.2) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun u => (hinner u).1.const_mul (A u)
    · have hmeas : AEStronglyMeasurable (fun u => ∫ v, ‖A u * T u v‖) volume :=
        hFm.norm.aestronglyMeasurable.integral_prod_right'
      refine Integrable.mono' hAK hmeas (Filter.Eventually.of_forall fun u => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun v => norm_nonneg _), hinn u]
      exact mul_le_mul_of_nonneg_left (hinner u).2 (hA0 u)
  refine ⟨hint, ?_⟩
  calc ∫ w : SpaceTime × SpaceTime, A w.1 * T w.1 w.2
      = ∫ u, ∫ v, A u * T u v := integral_prod _ hint
    _ ≤ ∫ u, A u * K u := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun u => integral_nonneg fun v => mul_nonneg (hA0 u)
            (hT0 u v)) hAK (Filter.Eventually.of_forall fun u => ?_)
        beta_reduce
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hinner u).2 (hA0 u)

/-- Combination of two powers of the same size, almost everywhere in the argument. -/
theorem ae_rpow_mul_rpow_eq (x : SpaceTime) (ζ e : ℝ) :
    ∀ᵐ u : SpaceTime ∂volume, torusParabolicSize (u - x) ^ ζ * torusParabolicSize (u - x) ^ e =
      torusParabolicSize (u - x) ^ (ζ + e) := by
  filter_upwards [ae_pos_torusParabolicSize_sub_right x] with u hu
  rw [Real.rpow_add hu]

namespace SemigroupTestProfile

variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

/-- Reassociation of the integrand. -/
private theorem double_integrand_eq (g : SpaceTime → ℝ) (x : SpaceTime) (ζ e : ℝ)
    (w : SpaceTime × SpaceTime) :
    |g w.1| * |g w.2| * (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e) =
      (|g w.1| * torusParabolicSize (w.1 - x) ^ ζ) *
        (|g w.2| * torusParabolicSize (w.1 - w.2) ^ e) := by ring

private theorem measurable_double_T (h : SemigroupTestProfile x lam B Mom g) (e : ℝ) :
    Measurable (fun w : SpaceTime × SpaceTime =>
      |g w.2| * torusParabolicSize (w.1 - w.2) ^ e) :=
  (h.measurable_abs.comp measurable_snd).mul
    ((Phi43.measurable_torusParabolicSize.comp (measurable_fst.sub measurable_snd)).pow_const _)

private theorem measurable_double_A (h : SemigroupTestProfile x lam B Mom g) (ζ : ℝ) :
    Measurable (fun u => |g u| * torusParabolicSize (u - x) ^ ζ) :=
  h.measurable_abs.mul
    ((Phi43.measurable_torusParabolicSize.comp (measurable_id.sub measurable_const)).pow_const _)

private theorem nonneg_double_A (g : SpaceTime → ℝ) (x : SpaceTime) (ζ : ℝ) (u : SpaceTime) :
    0 ≤ |g u| * torusParabolicSize (u - x) ^ ζ :=
  mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

private theorem nonneg_double_T (g : SpaceTime → ℝ) (e : ℝ) (u v : SpaceTime) :
    0 ≤ |g v| * torusParabolicSize (u - v) ^ e :=
  mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)

/-- Case `e < 0` of the double integral. -/
private theorem integral_double_le_neg (h : SemigroupTestProfile x lam B Mom g) {ζ e : ℝ}
    (hζ : -5 < ζ) (he : -5 < e) (he0 : e < 0) (hlam : 0 < lam) :
    Integrable (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e)) ∧
      ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e) ≤
      semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
  have hq := fun u => h.integral_mul_rpow_sub_le (q := -e) (by linarith) (by linarith) hlam u
  simp only [neg_neg] at hq
  set Kc : ℝ := (B * (80 / (5 - -e)) + Mom 0) * lam ^ e with hKc
  have hAint := (h.integral_rpow_le hζ hlam)
  have key := integrable_integral_prod_mul_le (A := fun u => |g u| * torusParabolicSize (u - x) ^ ζ)
    (K := fun _ => Kc) (T := fun u v => |g v| * torusParabolicSize (u - v) ^ e)
    (h.measurable_double_A ζ) (nonneg_double_A g x ζ) (h.measurable_double_T e)
    (nonneg_double_T g e) hq (hAint.1.mul_const Kc)
  simp only [double_integrand_eq]
  refine ⟨key.1, key.2.trans ?_⟩
  rw [integral_mul_const]
  have hKc0 : 0 ≤ Kc := by
    have := h.const_nonneg hlam
    have := h.mom_zero_nonneg
    have : 0 < 5 - -e := by linarith
    positivity
  calc (∫ u, |g u| * torusParabolicSize (u - x) ^ ζ) * Kc
      ≤ (semigroupTestMomConst B Mom ζ * lam ^ ζ) * Kc :=
        mul_le_mul_of_nonneg_right hAint.2 hKc0
    _ = semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
        simp only [semigroupTestDoubleConst, he0, ↓reduceIte]
        rw [hKc, Real.rpow_add hlam]
        have : (5 : ℝ) - -e = 5 + e := by ring
        rw [this]
        ring

/-- Case `e ≥ 0` of the double integral. -/
private theorem integral_double_le_nonneg (h : SemigroupTestProfile x lam B Mom g) {ζ e : ℝ}
    (hζ : -5 < ζ) (he0 : 0 ≤ e) (hlam : 0 < lam) :
    Integrable (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e)) ∧
      ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e) ≤
      semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
  have hζe : -5 < ζ + e := by linarith
  have h16 : (0 : ℝ) ≤ 16 ^ e := Real.rpow_nonneg (by norm_num) _
  have hAint := (h.integral_rpow_le hζ hlam)
  have hBint := (h.integral_rpow_le hζe hlam)
  -- the inner bound
  have hinner : ∀ u, Integrable (fun v => |g v| * torusParabolicSize (u - v) ^ e) ∧
      ∫ v, |g v| * torusParabolicSize (u - v) ^ e ≤
        16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e) := by
    intro u
    have hdom : Integrable (fun v => 16 ^ e * torusParabolicSize (u - x) ^ e * |g v| +
        16 ^ e * (|g v| * torusParabolicSize (v - x) ^ e)) :=
      (h.integrable_abs.const_mul _).add ((h.integrable_moment e he0).const_mul _)
    have hpt : ∀ v, |g v| * torusParabolicSize (u - v) ^ e ≤
        16 ^ e * torusParabolicSize (u - x) ^ e * |g v| +
          16 ^ e * (|g v| * torusParabolicSize (v - x) ^ e) := by
      intro v
      have := mul_le_mul_of_nonneg_left (torusParabolicSize_sub_rpow_le he0 u v x)
        (abs_nonneg (g v))
      linarith
    have hm : Measurable (fun v => |g v| * torusParabolicSize (u - v) ^ e) :=
      h.measurable_abs.mul ((Phi43.measurable_torusParabolicSize.comp
        (measurable_const.sub measurable_id)).pow_const _)
    refine ⟨hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_), ?_⟩
    · rw [Real.norm_of_nonneg (nonneg_double_T g e u v)]
      exact hpt v
    · calc ∫ v, |g v| * torusParabolicSize (u - v) ^ e
          ≤ ∫ v, (16 ^ e * torusParabolicSize (u - x) ^ e * |g v| +
              16 ^ e * (|g v| * torusParabolicSize (v - x) ^ e)) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall (nonneg_double_T g e u)) hdom
              (Filter.Eventually.of_forall hpt)
        _ = (16 ^ e * torusParabolicSize (u - x) ^ e * ∫ v, |g v|) +
              16 ^ e * ∫ v, |g v| * torusParabolicSize (v - x) ^ e := by
            rw [integral_add ((h.integrable_abs.const_mul _))
              ((h.integrable_moment e he0).const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ 16 ^ e * torusParabolicSize (u - x) ^ e * Mom 0 + 16 ^ e * (Mom e * lam ^ e) := by
            have hc : 0 ≤ 16 ^ e * torusParabolicSize (u - x) ^ e :=
              mul_nonneg h16 (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
            exact add_le_add (mul_le_mul_of_nonneg_left h.integral_abs_le hc)
              (mul_le_mul_of_nonneg_left (h.integral_moment_le e he0) h16)
        _ = 16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e) := by ring
  -- integrability of `A K`
  have hAK_eq : ∀ᵐ u : SpaceTime ∂volume,
      (|g u| * torusParabolicSize (u - x) ^ ζ) *
        (16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e)) =
      (16 ^ e * Mom 0) * (|g u| * torusParabolicSize (u - x) ^ (ζ + e)) +
        (16 ^ e * Mom e * lam ^ e) * (|g u| * torusParabolicSize (u - x) ^ ζ) := by
    filter_upwards [ae_rpow_mul_rpow_eq x ζ e] with u hu
    rw [← hu]
    ring
  have hAK : Integrable (fun u => (|g u| * torusParabolicSize (u - x) ^ ζ) *
      (16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e))) :=
    ((hBint.1.const_mul _).add (hAint.1.const_mul _)).congr (hAK_eq.mono fun u hu => hu.symm)
  have key := integrable_integral_prod_mul_le
    (A := fun u => |g u| * torusParabolicSize (u - x) ^ ζ)
    (K := fun u => 16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e))
    (T := fun u v => |g v| * torusParabolicSize (u - v) ^ e)
    (h.measurable_double_A ζ) (nonneg_double_A g x ζ) (h.measurable_double_T e)
    (nonneg_double_T g e) hinner hAK
  simp only [double_integrand_eq]
  refine ⟨key.1, key.2.trans ?_⟩
  rw [integral_congr_ae hAK_eq, integral_add (hBint.1.const_mul _) (hAint.1.const_mul _),
    integral_const_mul, integral_const_mul]
  have hm0 := h.mom_zero_nonneg
  have hMe : 0 ≤ Mom e := h.mom_nonneg hlam he0
  calc (16 ^ e * Mom 0 * ∫ u, |g u| * torusParabolicSize (u - x) ^ (ζ + e)) +
        16 ^ e * Mom e * lam ^ e * ∫ u, |g u| * torusParabolicSize (u - x) ^ ζ
      ≤ 16 ^ e * Mom 0 * (semigroupTestMomConst B Mom (ζ + e) * lam ^ (ζ + e)) +
        16 ^ e * Mom e * lam ^ e * (semigroupTestMomConst B Mom ζ * lam ^ ζ) :=
        add_le_add (mul_le_mul_of_nonneg_left hBint.2 (mul_nonneg h16 hm0))
          (mul_le_mul_of_nonneg_left hAint.2 (mul_nonneg (mul_nonneg h16 hMe)
            (Real.rpow_nonneg hlam.le _)))
    _ = semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
        simp only [semigroupTestDoubleConst, not_lt.2 he0, ↓reduceIte]
        rw [Real.rpow_add hlam]
        ring

/-- **Chaos-reduction double integral for a semigroup test profile.**  For `ζ, e > -5`,
`∫∫ |g u| |g v| s(u - x)^ζ s(u - v)^e ≤ C lam^(ζ+e)`, with `C` an explicit function of the profile
constants `B`, `Mom` and of `ζ, e`. -/
theorem integral_double_le (h : SemigroupTestProfile x lam B Mom g) {ζ e : ℝ} (hζ : -5 < ζ)
    (he : -5 < e) (hlam : 0 < lam) :
    Integrable (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e)) ∧
      ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e) ≤
      semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
  rcases lt_or_ge e 0 with he0 | he0
  · exact integral_double_le_neg h hζ he he0 hlam
  · exact integral_double_le_nonneg h hζ he0 hlam

end SemigroupTestProfile

end RegularityStructures

end
