/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestCoord
import Mathlib.Tactic

/-!
# The periodisation of `|Q_t(x, y)| (1 + ‖y - x‖/lam)²` is a semigroup test profile

With `lam = t^(1/4)` and `W(y) = (1 + ‖y - x‖_𝔰 / lam)²`, the periodisation of
`ipsiWeightedKernel t x y = |Q_t(x, y)| W(y)` is a `SemigroupTestProfile` at scale `lam`, base
point `proj x`, with moment function `ipsiMom r = M_r + 2 M_{r+1} + M_{r+2}`
(`exists_semigroupTestProfile_ipsiWeighted`).  Polynomial weights `‖y - x‖^a (1 + ‖y - x‖)^c`,
`a + c ≤ 2`, are dominated by `lam^a` times this kernel, which is how the covariance layer of
`I(Ψ)Ψ` reduces the `ℝ⁴ × ℝ⁴` integrals to the profile double bounds.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The weighted kernel `|Q_t(x, y)| (1 + ‖y - x‖/t^(1/4))²`. -/
def ipsiWeightedKernel (t : ℝ) (x y : ParabolicSpace) : ℝ :=
  |parabolicSemigroup.kernel t x y| * (1 + parabolicNorm (y - x) / t ^ (1 / 4 : ℝ)) ^ 2

/-- The moment function of the weighted profile. -/
def ipsiMom (r : ℝ) : ℝ :=
  parabolicMomentConst r + 2 * parabolicMomentConst (r + 1) + parabolicMomentConst (r + 2)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem measurable_ipsiWeightedKernel (t : ℝ) (x : ParabolicSpace) :
    Measurable (ipsiWeightedKernel t x) := by
  unfold ipsiWeightedKernel
  refine (continuous_abs.measurable.comp (measurable_parabolicSemigroup_kernel t x)).mul ?_
  refine (measurable_const.add ?_).pow_const 2
  exact (continuous_parabolicNorm.measurable.comp
    (measurable_id.sub measurable_const)).div_const _

theorem ipsiWeightedKernel_nonneg (t : ℝ) (x y : ParabolicSpace) :
    0 ≤ ipsiWeightedKernel t x y :=
  mul_nonneg (abs_nonneg _) (sq_nonneg _)

theorem ipsiWeightedKernel_expand {t : ℝ} (ht : 0 < t) (x y : ParabolicSpace) {r : ℝ} (hr : 0 ≤ r) :
    ipsiWeightedKernel t x y * parabolicNorm (y - x) ^ r =
      |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ r +
        2 * (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
          t ^ (1 / 4 : ℝ) +
        (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 2)) /
          (t ^ (1 / 4 : ℝ)) ^ 2 := by
  have hl : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have h0 := parabolicNorm_nonneg (y - x)
  unfold ipsiWeightedKernel
  rw [Real.rpow_add' h0 (by linarith), Real.rpow_add' h0 (by linarith), Real.rpow_one]
  have : parabolicNorm (y - x) ^ (2 : ℝ) = parabolicNorm (y - x) ^ 2 := by
    rw [← Real.rpow_natCast]; norm_num
  rw [this]
  field_simp
  ring

/-- **Lattice sums of the weighted kernel.** -/
theorem exists_ipsiWeightedKernel_lattice_sum_le :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ (x : ParabolicSpace) (u : SpaceTime),
      Summable (fun k : Fin 3 → ℤ =>
        |ipsiWeightedKernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ))|) ∧
      ∑' k : Fin 3 → ℤ, |ipsiWeightedKernel t x (u.1, torusRep u.2 + fun j => (k j : ℝ))| ≤
        B * ((t ^ (1 / 4 : ℝ)) ^ 5)⁻¹ := by
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_parabolicKernel_mul_norm_le 0
  obtain ⟨C2, hC20, hC2⟩ := exists_abs_parabolicKernel_mul_norm_le 2
  obtain ⟨L, hL0, hL⟩ := tsum_abs_periodise_le
  refine ⟨(2 * (C0 + C2)) * L, by positivity, fun {t} ht ht1 x u => ?_⟩
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hdec : ∀ y : ParabolicSpace, |ipsiWeightedKernel t x y| ≤
      ((2 * (C0 + C2)) * t ^ (-(5 / 4 : ℝ))) * ∏ j : Fin 3, ((1 + |x.2 j - y.2 j|) ^ 2)⁻¹ := by
    intro y
    rw [abs_of_nonneg (ipsiWeightedKernel_nonneg t x y)]
    have h0 := hC0 ht ht1 (x - y)
    have h2 := hC2 ht ht1 (x - y)
    simp only [pow_zero, mul_one] at h0
    rw [parabolicNorm_sub_comm] at h2
    simp only [Prod.snd_sub, Pi.sub_apply] at h0 h2
    have hu : 0 ≤ parabolicNorm (y - x) / t ^ (1 / 4 : ℝ) := by
      have := parabolicNorm_nonneg (y - x); positivity
    have e : ipsiWeightedKernel t x y ≤ 2 * |parabolicKernel t (x - y)| +
        2 * (|parabolicKernel t (x - y)| * (parabolicNorm (y - x) / t ^ (1 / 4 : ℝ)) ^ 2) := by
      unfold ipsiWeightedKernel
      rw [parabolicSemigroup_kernel_eq]
      nlinarith [mul_nonneg (abs_nonneg (parabolicKernel t (x - y))) (sq_nonneg
        (1 - parabolicNorm (y - x) / t ^ (1 / 4 : ℝ)))]
    refine e.trans ?_
    have hP : 0 ≤ t ^ (-(5 / 4 : ℝ)) * ∏ j : Fin 3, ((1 + |x.2 j - y.2 j|) ^ 2)⁻¹ := by positivity
    nlinarith
  obtain ⟨hs, hb⟩ := hL (h := ipsiWeightedKernel t x)
    (C := (2 * (C0 + C2)) * t ^ (-(5 / 4 : ℝ))) (a0 := x.2)
    (mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)) hdec u
  refine ⟨hs, hb.trans (le_of_eq ?_)⟩
  rw [rpow_quarter_pow_five_inv ht]
  ring

/-- **The weighted periodised kernel is a test profile.** -/
theorem exists_semigroupTestProfile_ipsiWeighted :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupTestProfile (Phi43.spaceTimeProj x) (t ^ (1 / 4 : ℝ)) B ipsiMom
        (fun u : SpaceTime => ∑' k : Fin 3 → ℤ,
          ipsiWeightedKernel t x (u.1, torusRep u.2 + fun i => (k i : ℝ))) := by
  obtain ⟨B, hB0, hB⟩ := exists_ipsiWeightedKernel_lattice_sum_le
  refine ⟨B, hB0, fun {t} ht ht1 x => ?_⟩
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hsup := hB ht ht1 x
  have hI : ∀ s : ℝ, 0 ≤ s → Integrable (fun y => |parabolicSemigroup.kernel t x y| *
      parabolicNorm (y - x) ^ s) := fun s hs => parabolicSemigroup.integrable_moment ht hs x
  have hint : ∀ r : ℝ, 0 ≤ r → Integrable (fun y => |ipsiWeightedKernel t x y| *
      parabolicNorm (y - x) ^ r) := by
    intro r hr
    have hsum := ((hI r hr).add (((hI (r + 1) (by linarith)).const_mul 2).div_const
      (t ^ (1 / 4 : ℝ)))).add ((hI (r + 2) (by linarith)).div_const ((t ^ (1 / 4 : ℝ)) ^ 2))
    refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    rw [abs_of_nonneg (ipsiWeightedKernel_nonneg t x y), ipsiWeightedKernel_expand ht x y hr]
  refine semigroupTestProfile_periodise (measurable_ipsiWeightedKernel t x) hsup hint ?_
  intro r hr
  have h1 : ∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ r ≤
      parabolicMomentConst r * t ^ (r / 4) := parabolicSemigroup.moment_le ht hr x
  have h2 : ∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1) ≤
      parabolicMomentConst (r + 1) * t ^ ((r + 1) / 4) :=
    parabolicSemigroup.moment_le ht (show 0 ≤ r + 1 by linarith) x
  have h3 : ∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 2) ≤
      parabolicMomentConst (r + 2) * t ^ ((r + 2) / 4) :=
    parabolicSemigroup.moment_le ht (show 0 ≤ r + 2 by linarith) x
  have hl := hlam
  have e : ∀ s : ℝ, t ^ (s / 4) = (t ^ (1 / 4 : ℝ)) ^ s := fun s => (rpow_quarter_rpow ht s).symm
  have hint' := hint r hr
  have hsum := ((hI r hr).add (((hI (r + 1) (by linarith)).const_mul 2).div_const
      (t ^ (1 / 4 : ℝ)))).add ((hI (r + 2) (by linarith)).div_const ((t ^ (1 / 4 : ℝ)) ^ 2))
  have hle : ∫ y, |ipsiWeightedKernel t x y| * parabolicNorm (y - x) ^ r =
      (∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ r) +
        2 * (∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
          t ^ (1 / 4 : ℝ) +
        (∫ y, |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 2)) /
          (t ^ (1 / 4 : ℝ)) ^ 2 := by
    have : (fun y => |ipsiWeightedKernel t x y| * parabolicNorm (y - x) ^ r) =
        fun y => (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ r +
          2 * (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
            t ^ (1 / 4 : ℝ)) +
          (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 2)) /
            (t ^ (1 / 4 : ℝ)) ^ 2 := by
      funext y
      rw [abs_of_nonneg (ipsiWeightedKernel_nonneg t x y), ipsiWeightedKernel_expand ht x y hr]
    have i1 := hI r hr
    have i2 : Integrable (fun y => 2 * (|parabolicSemigroup.kernel t x y| *
        parabolicNorm (y - x) ^ (r + 1)) / t ^ (1 / 4 : ℝ)) :=
      ((hI (r + 1) (by linarith)).const_mul 2).div_const _
    have i3 : Integrable (fun y => (|parabolicSemigroup.kernel t x y| *
        parabolicNorm (y - x) ^ (r + 2)) / (t ^ (1 / 4 : ℝ)) ^ 2) :=
      (hI (r + 2) (by linarith)).div_const _
    have i12 : Integrable (fun y => |parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ r +
        2 * (|parabolicSemigroup.kernel t x y| * parabolicNorm (y - x) ^ (r + 1)) /
          t ^ (1 / 4 : ℝ)) := i1.add i2
    rw [this, integral_add i12 i3, integral_add i1 i2, integral_div, integral_const_mul,
      integral_div]
  rw [hle]
  have p1 : parabolicMomentConst r * t ^ (r / 4) = parabolicMomentConst r * (t ^ (1 / 4 : ℝ)) ^ r := by
    rw [e]
  have q1 : 2 * (parabolicMomentConst (r + 1) * (t ^ (1 / 4 : ℝ)) ^ (r + 1)) / t ^ (1 / 4 : ℝ) =
      2 * parabolicMomentConst (r + 1) * (t ^ (1 / 4 : ℝ)) ^ r := by
    rw [Real.rpow_add hlam, Real.rpow_one]; field_simp
  have q2 : (parabolicMomentConst (r + 2) * (t ^ (1 / 4 : ℝ)) ^ (r + 2)) / (t ^ (1 / 4 : ℝ)) ^ 2 =
      parabolicMomentConst (r + 2) * (t ^ (1 / 4 : ℝ)) ^ r := by
    rw [Real.rpow_add hlam]
    have : (t ^ (1 / 4 : ℝ)) ^ (2 : ℝ) = (t ^ (1 / 4 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast]; norm_num
    rw [this]; field_simp
  rw [e] at h1 h2 h3
  have hp := Real.rpow_nonneg hlam.le r
  calc _ ≤ parabolicMomentConst r * (t ^ (1 / 4 : ℝ)) ^ r +
        2 * (parabolicMomentConst (r + 1) * (t ^ (1 / 4 : ℝ)) ^ (r + 1)) / t ^ (1 / 4 : ℝ) +
        (parabolicMomentConst (r + 2) * (t ^ (1 / 4 : ℝ)) ^ (r + 2)) / (t ^ (1 / 4 : ℝ)) ^ 2 := by
        gcongr
    _ = ipsiMom r * (t ^ (1 / 4 : ℝ)) ^ r := by
        rw [q1, q2]; unfold ipsiMom; ring

end RegularityStructures

end
