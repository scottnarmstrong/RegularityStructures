/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCoreTaylor
public import Phi43.BPHZ.ProductIPsiPsiLatticeUnfold
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
import Mathlib.Tactic

/-!
# The lattice-summed Taylor kernel and its weight

Fix `N`, `t > 0` and `x ∈ ℝ⁴`, and write `Q_n(u) = Q_t(x, lift_n u)`, `c_n(u) = 1 + ‖lift_n u - x‖_𝔰`,
`T_n(u, w) = hairerTaylorKernelAt N x (lift_n u) w`.  On `ℝ × T³` put

* `latticeG u = ∑_n |Q_n(u)| c_n(u)` (as the real part of an extended sum),
* `latticeNum u w = ∑_n Q_n(u) T_n(u, w)`, `latticeK u w = latticeNum u w / latticeG u`.

Then `latticeG` is measurable, integrable and almost everywhere equal to a convergent sum, and
`latticeK` is jointly measurable, with `∫ |latticeK u w| dw ≤ L` for all `u`, supported (in `w`) in a
compact set uniformly for `u₀` in a bounded interval.  These are the data of the generic
chaos-moment engine for the field `∫_{ℝ⁴} Q_t(x, y) v₁(x, y) Φ(y) dy`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures
open scoped ENNReal

/-- The `n`-th term `|Q_t(x, lift_n u)| (1 + ‖lift_n u - x‖_𝔰)` of the weight sum. -/
def latticeWeightTerm (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) (n : Fin 3 → ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (|parabolicSemigroup.kernel t x (latticeLift u n)| *
    (1 + parabolicNorm (latticeLift u n - x)))

/-- The extended weight sum `∑_n |Q_t(x, lift_n u)| (1 + ‖lift_n u - x‖_𝔰)`. -/
def latticeWeightSum (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) : ℝ≥0∞ :=
  ∑' n : Fin 3 → ℤ, latticeWeightTerm t x u n

/-- The real weight `g`. -/
def latticeG (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) : ℝ :=
  (latticeWeightSum t x u).toReal

/-- The numerator `∑_n Q_t(x, lift_n u) T_n(u, w)`. -/
def latticeNum (N : ℕ) (t : ℝ) (x : ParabolicSpace) (u w : SpaceTime) : ℝ :=
  ∑' n : Fin 3 → ℤ, parabolicSemigroup.kernel t x (latticeLift u n) *
    hairerTaylorKernelAt N x (latticeLift u n) w

/-- The normalised kernel `k(u, w) = latticeNum u w / g(u)`. -/
def latticeK (N : ℕ) (t : ℝ) (x : ParabolicSpace) (u w : SpaceTime) : ℝ :=
  latticeNum N t x u w / latticeG t x u

end RegularityStructures.Phi43

end

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem measurable_latticeWeightSum (t : ℝ) (x : ParabolicSpace) :
    Measurable (latticeWeightSum t x) := by
  refine Measurable.tsum fun n => ?_
  unfold latticeWeightTerm
  refine ENNReal.measurable_ofReal.comp ?_
  refine (continuous_abs.measurable.comp
    ((measurable_parabolicSemigroup_kernel t x).comp (measurable_latticeLift_left n))).mul ?_
  exact measurable_const.add (continuous_parabolicNorm.measurable.comp
    ((measurable_latticeLift_left n).sub measurable_const))

theorem measurable_latticeG (t : ℝ) (x : ParabolicSpace) : Measurable (latticeG t x) :=
  (measurable_latticeWeightSum t x).ennreal_toReal

theorem latticeG_nonneg (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) : 0 ≤ latticeG t x u :=
  ENNReal.toReal_nonneg

theorem lintegral_latticeWeightSum_ne_top {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    ∫⁻ u, latticeWeightSum t x u ≠ ⊤ := by
  set φ : ParabolicSpace → ℝ := fun y =>
    |parabolicSemigroup.kernel t x y| * (1 + parabolicNorm (y - x)) with hφ
  have hφi : Integrable φ := by
    have h0 := parabolicSemigroup.integrable_moment ht (r := 0) le_rfl x
    have h1 := parabolicSemigroup.integrable_moment ht (r := 1) zero_le_one x
    refine (h0.add h1).congr (Filter.Eventually.of_forall fun y => ?_)
    have e : parabolicSemigroup.scaleDist y x = parabolicNorm (y - x) := rfl
    simp only [hφ, e, Real.rpow_zero, Real.rpow_one, Pi.add_apply]
    ring
  have hm : Measurable fun y => ENNReal.ofReal (φ y) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (continuous_abs.measurable.comp (measurable_parabolicSemigroup_kernel t x)).mul
      (measurable_const.add (continuous_parabolicNorm.measurable.comp
        (measurable_id.sub measurable_const)))
  have h := lintegral_eq_lintegral_spaceTime_tsum (H := fun y => ENNReal.ofReal (φ y)) hm
  have e : ∫⁻ u, latticeWeightSum t x u = ∫⁻ y, ENNReal.ofReal (φ y) := h.symm
  rw [e]
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun y => ?_) hφi.2)
  exact Real.ofReal_le_enorm _

theorem ae_latticeWeightSum_lt_top {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    ∀ᵐ u : SpaceTime, latticeWeightSum t x u < ⊤ :=
  ae_lt_top (measurable_latticeWeightSum t x) (lintegral_latticeWeightSum_ne_top ht x)

theorem integrable_latticeG {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    Integrable (latticeG t x) :=
  integrable_toReal_of_lintegral_ne_top (measurable_latticeWeightSum t x).aemeasurable
    (lintegral_latticeWeightSum_ne_top ht x)

theorem latticeWeight_nonneg (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) (n : Fin 3 → ℤ) :
    0 ≤ |parabolicSemigroup.kernel t x (latticeLift u n)| *
      (1 + parabolicNorm (latticeLift u n - x)) :=
  mul_nonneg (abs_nonneg _) (by linarith [parabolicNorm_nonneg (latticeLift u n - x)])

/-- On the set where the weight sum is finite, it is the sum of a convergent real series. -/
theorem summable_latticeWeight {t : ℝ} {x : ParabolicSpace} {u : SpaceTime}
    (hu : latticeWeightSum t x u < ⊤) :
    Summable (fun n : Fin 3 → ℤ => |parabolicSemigroup.kernel t x (latticeLift u n)| *
      (1 + parabolicNorm (latticeLift u n - x))) ∧
    latticeG t x u = ∑' n : Fin 3 → ℤ, |parabolicSemigroup.kernel t x (latticeLift u n)| *
      (1 + parabolicNorm (latticeLift u n - x)) := by
  have hterm : ∀ n, (latticeWeightTerm t x u n).toReal =
      |parabolicSemigroup.kernel t x (latticeLift u n)| *
        (1 + parabolicNorm (latticeLift u n - x)) := fun n =>
    ENNReal.toReal_ofReal (latticeWeight_nonneg t x u n)
  have hs := ENNReal.summable_toReal hu.ne
  simp only [hterm] at hs
  refine ⟨?_, ?_⟩
  · simpa only [hterm] using hs
  · unfold latticeG latticeWeightSum
    rw [ENNReal.tsum_toReal_eq (f := latticeWeightTerm t x u) fun n => ENNReal.ofReal_ne_top]
    exact tsum_congr hterm

theorem sum_abs_le_parabolicNorm (z : ParabolicSpace) : ∑ i, |z.2 i| ≤ parabolicNorm z := by
  unfold parabolicNorm
  linarith [Real.sqrt_nonneg |z.1|]

theorem measurable_uncurry_latticeNum (N : ℕ) (t : ℝ) (x : ParabolicSpace) :
    Measurable (fun p : SpaceTime × SpaceTime => latticeNum N t x p.1 p.2) := by
  unfold latticeNum
  refine Measurable.tsum fun n => ?_
  have hlat : Measurable fun p : SpaceTime × SpaceTime => latticeLift p.1 n :=
    (measurable_latticeLift_left n).comp measurable_fst
  have hQ : Measurable fun p : SpaceTime × SpaceTime =>
      parabolicSemigroup.kernel t x (latticeLift p.1 n) :=
    (measurable_parabolicSemigroup_kernel t x).comp hlat
  have hT : Measurable fun p : SpaceTime × SpaceTime =>
      hairerTaylorKernelAt N x (latticeLift p.1 n) p.2 :=
    (measurable_uncurry_hairerTaylorKernelAt N x).comp
      (f := fun p : SpaceTime × SpaceTime => (latticeLift p.1 n, p.2)) (hlat.prodMk measurable_snd)
  exact hQ.mul hT

theorem measurable_latticeNum (N : ℕ) (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) :
    Measurable (latticeNum N t x u) :=
  (measurable_uncurry_latticeNum N t x).comp (f := fun w : SpaceTime => (u, w))
    (measurable_const.prodMk measurable_id)

theorem measurable_uncurry_latticeK (N : ℕ) (t : ℝ) (x : ParabolicSpace) :
    Measurable (Function.uncurry (latticeK N t x)) :=
  (measurable_uncurry_latticeNum N t x).div ((measurable_latticeG t x).comp measurable_fst)

/-- The `L¹(dw)` norm of the numerator is at most `L` times the weight sum. -/
theorem lintegral_enorm_latticeNum_le {N : ℕ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ (x' : SpaceTime) (t' : ℝ) (a : Fin 3 → ℝ),
      ∫ w, |hairerTaylorKernel N x' t' a w| ≤ L * (1 + ∑ i, |a i|))
    (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) :
    ∫⁻ w, ‖latticeNum N t x u w‖ₑ ≤ ENNReal.ofReal L * latticeWeightSum t x u := by
  unfold latticeNum
  have hmeas : ∀ n : Fin 3 → ℤ, Measurable fun w => parabolicSemigroup.kernel t x
      (latticeLift u n) * hairerTaylorKernelAt N x (latticeLift u n) w := fun n =>
    measurable_const.mul ((measurable_uncurry_hairerTaylorKernelAt N x).comp
      (f := fun w : SpaceTime => (latticeLift u n, w)) (measurable_const.prodMk measurable_id))
  calc ∫⁻ w, ‖∑' n : Fin 3 → ℤ, parabolicSemigroup.kernel t x (latticeLift u n) *
          hairerTaylorKernelAt N x (latticeLift u n) w‖ₑ
      ≤ ∫⁻ w, ∑' n : Fin 3 → ℤ, ‖parabolicSemigroup.kernel t x (latticeLift u n) *
          hairerTaylorKernelAt N x (latticeLift u n) w‖ₑ :=
        lintegral_mono fun w => enorm_tsum_le_tsum_enorm
    _ = ∑' n : Fin 3 → ℤ, ∫⁻ w, ‖parabolicSemigroup.kernel t x (latticeLift u n) *
          hairerTaylorKernelAt N x (latticeLift u n) w‖ₑ :=
        lintegral_tsum fun n => (hmeas n).enorm.aemeasurable
    _ ≤ ∑' n : Fin 3 → ℤ, ENNReal.ofReal L * latticeWeightTerm t x u n := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        set y := latticeLift u n with hy
        set Qn := parabolicSemigroup.kernel t x y with hQn
        have hT : Integrable (hairerTaylorKernelAt N x y) :=
          integrable_hairerTaylorKernel N _ _ _
        have h1 : ∫⁻ w, ‖Qn * hairerTaylorKernelAt N x y w‖ₑ =
            ENNReal.ofReal |Qn| * ENNReal.ofReal (∫ w, |hairerTaylorKernelAt N x y w|) := by
          simp_rw [enorm_mul]
          rw [lintegral_const_mul' _ _ (by simp), Real.enorm_eq_ofReal_abs]
          congr 1
          have := ofReal_integral_norm_eq_lintegral_enorm hT
          simpa only [Real.norm_eq_abs] using this.symm
        have h2 : ∫ w, |hairerTaylorKernelAt N x y w| ≤ L * (1 + parabolicNorm (y - x)) := by
          refine (hL _ _ _).trans ?_
          have hs := sum_abs_le_parabolicNorm (y - x)
          simp only [Prod.snd_sub] at hs
          exact mul_le_mul_of_nonneg_left (by linarith) hL0
        rw [h1]
        calc ENNReal.ofReal |Qn| * ENNReal.ofReal (∫ w, |hairerTaylorKernelAt N x y w|)
            ≤ ENNReal.ofReal |Qn| * ENNReal.ofReal (L * (1 + parabolicNorm (y - x))) :=
              mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal h2)
          _ = ENNReal.ofReal L * latticeWeightTerm t x u n := by
              rw [← ENNReal.ofReal_mul (abs_nonneg _), latticeWeightTerm, ← ENNReal.ofReal_mul hL0]
              congr 1
              ring
    _ = ENNReal.ofReal L * latticeWeightSum t x u := ENNReal.tsum_mul_left

/-- When the weight sum vanishes, so does the numerator. -/
theorem latticeNum_eq_zero_of_latticeG_eq_zero {N : ℕ} {t : ℝ} {x : ParabolicSpace} {u : SpaceTime}
    (hu : latticeWeightSum t x u < ⊤) (hG : latticeG t x u = 0) (w : SpaceTime) :
    latticeNum N t x u w = 0 := by
  have h0 : latticeWeightSum t x u = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hG with h | h
    · exact h
    · exact absurd h hu.ne
  have hn : ∀ n, parabolicSemigroup.kernel t x (latticeLift u n) = 0 := by
    intro n
    have h1 : latticeWeightTerm t x u n = 0 := (ENNReal.tsum_eq_zero.1 h0) n
    have h2 := (ENNReal.ofReal_eq_zero.1 h1)
    have h3 : 0 < 1 + parabolicNorm (latticeLift u n - x) := by
      linarith [parabolicNorm_nonneg (latticeLift u n - x)]
    have h4 : |parabolicSemigroup.kernel t x (latticeLift u n)| ≤ 0 := by
      by_contra hc
      exact absurd h2 (not_le.2 (mul_pos (not_le.1 hc) h3))
    exact abs_nonpos_iff.1 h4
  unfold latticeNum
  simp [hn]

/-- The normalised kernel is integrable with `L¹` norm at most `L`, for every `u`. -/
theorem integrable_latticeK_and_integral_abs_le {N : ℕ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ (x' : SpaceTime) (t' : ℝ) (a : Fin 3 → ℝ),
      ∫ w, |hairerTaylorKernel N x' t' a w| ≤ L * (1 + ∑ i, |a i|))
    (t : ℝ) (x : ParabolicSpace) (u : SpaceTime) :
    Integrable (latticeK N t x u) ∧ ∫ w, |latticeK N t x u w| ≤ L := by
  by_cases hG : latticeG t x u = 0
  · have hk : latticeK N t x u = fun _ => 0 := by
      funext w
      simp [latticeK, hG]
    rw [hk]
    exact ⟨integrable_zero _ _ _, by simpa using hL0⟩
  · have hGpos : 0 < latticeG t x u := lt_of_le_of_ne (latticeG_nonneg t x u) (Ne.symm hG)
    have hS : latticeWeightSum t x u ≠ ⊤ := fun h => hG (by simp [latticeG, h])
    have hle := lintegral_enorm_latticeNum_le hL0 hL t x u
    have hlt : ∫⁻ w, ‖latticeNum N t x u w‖ₑ < ⊤ :=
      lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS.lt_top)
    have hnum : Integrable (latticeNum N t x u) :=
      ⟨(measurable_latticeNum N t x u).aestronglyMeasurable, hlt⟩
    refine ⟨hnum.div_const _, ?_⟩
    have e : ∀ w, |latticeK N t x u w| = |latticeNum N t x u w| / latticeG t x u := fun w => by
      rw [latticeK, abs_div, abs_of_pos hGpos]
    simp_rw [e]
    rw [integral_div, div_le_iff₀ hGpos]
    have h1 : ∫ w, |latticeNum N t x u w| = (∫⁻ w, ‖latticeNum N t x u w‖ₑ).toReal := by
      rw [← integral_norm_eq_lintegral_enorm (measurable_latticeNum N t x u).aestronglyMeasurable]
      simp only [Real.norm_eq_abs]
    rw [h1]
    calc (∫⁻ w, ‖latticeNum N t x u w‖ₑ).toReal
        ≤ (ENNReal.ofReal L * latticeWeightSum t x u).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) hle
      _ = L * latticeG t x u := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL0]
          rfl

/-- Uniform compact time support of the normalised kernel on bounded time intervals. -/
theorem latticeK_support (N : ℕ) (t : ℝ) (x : ParabolicSpace) (c R : ℝ) :
    ∃ S : Set SpaceTime, IsCompact S ∧ ∀ u : SpaceTime, |u.1 - c| ≤ R →
      ∀ w, latticeK N t x u w ≠ 0 → w ∈ S := by
  set T : ℝ := |c| + R + |x.1| + 1 with hT
  refine ⟨Set.Icc (-T) T ×ˢ Set.univ, isCompact_Icc.prod isCompact_univ, fun u hu w hw => ?_⟩
  refine ⟨?_, Set.mem_univ _⟩
  have hnum : latticeNum N t x u w ≠ 0 := fun h => hw (by simp [latticeK, h])
  have hex : ∃ n : Fin 3 → ℤ, parabolicSemigroup.kernel t x (latticeLift u n) *
      hairerTaylorKernelAt N x (latticeLift u n) w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnum (by unfold latticeNum; simp [hcon])
  obtain ⟨n, hn⟩ := hex
  have hT0 : hairerTaylorKernelAt N x (latticeLift u n) w ≠ 0 := right_ne_zero_of_mul hn
  have htime := hairerTaylorKernel_ne_zero_time N hT0
  have hu' := abs_le.1 hu
  have hc1 := le_abs_self c
  have hc2 := neg_abs_le c
  have hx0 := abs_nonneg x.1
  have hR : 0 ≤ R := (abs_nonneg _).trans hu
  have hw1 : |u.1 - w.1| ≤ 1 ∨ |x.1 - w.1| ≤ 1 := by
    rcases htime with h | h
    · left
      have e : (spaceTimeProj x).1 + ((latticeLift u n).1 - x.1) - w.1 = u.1 - w.1 := by
        simp [spaceTimeProj, latticeLift]
      rw [e] at h
      exact h
    · right
      exact h
  have hxl := le_abs_self x.1
  have hxl2 := neg_abs_le x.1
  rcases hw1 with h | h
  · have h' := abs_le.1 h
    constructor <;> linarith
  · have h' := abs_le.1 h
    constructor <;> linarith

end RegularityStructures.Phi43

end
