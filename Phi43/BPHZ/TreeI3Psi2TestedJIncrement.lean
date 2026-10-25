/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2TestedJNear
public import Phi43.BPHZ.HairerKernelIncrementTorus

/-!
# Uniform increment bound for the mollified Hairer kernel

`hairerMollifiedKernel_increment_uniform`: there is `C` with
`|J_ε(u + h) - J_ε(u)| ≤ C s(h) s(u)⁻⁴` for all `ε ∈ (0, 1]`, `s(u) > 0`, `s(h) ≤ s(u)/2`.
Three regimes: (i) `s(h) > s(u)/4`: the singular bound `|J_ε| ≤ C s⁻³` for both terms and
`s(u + h) ≥ s(u)/2`; (ii) `s(h) ≤ s(u)/4` and `s(u) ≥ 2 B ε`: the increment bound of `K` against
the mollifier; (iii) `s(h) ≤ s(u)/4` and `s(u) < 2 B ε`: the Lipschitz bound of the mollifier
(`hairerMollifiedKernel_increment_near`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_neg_four_half_le {x y : ℝ} (hy : 0 < y) (h : y / 2 ≤ x) :
    x ^ (-(4 : ℝ)) ≤ 16 * y ^ (-(4 : ℝ)) := by
  have hy2 : 0 < y / 2 := by positivity
  refine (Real.rpow_le_rpow_of_nonpos hy2 h (by norm_num)).trans (le_of_eq ?_)
  rw [Real.div_rpow hy.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  ring

private theorem rpow_neg_three_half_le {x y : ℝ} (hy : 0 < y) (h : y / 2 ≤ x) :
    x ^ (-(3 : ℝ)) ≤ 8 * y ^ (-(3 : ℝ)) := by
  have hy2 : 0 < y / 2 := by positivity
  refine (Real.rpow_le_rpow_of_nonpos hy2 h (by norm_num)).trans (le_of_eq ?_)
  rw [Real.div_rpow hy.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num
  ring

/-- **Increment of `J_ε` away from the singularity** (`s(u) ≥ 2 B ε`, `s(h) ≤ s(u)/4`). -/
theorem hairerMollifiedKernel_increment_far (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {B : ℝ}
    (hsupp : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ w : SpaceTime,
      periodise ρ ε w ≠ 0 → torusParabolicSize w ≤ B * ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {u h : SpaceTime},
      0 < torusParabolicSize u → 2 * B * ε ≤ torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 4 →
        |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
          C * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := by
  obtain ⟨Ci, hCi, hinc⟩ := hairerKernelTorus_sub_abs_le N
  set mass : ℝ := ∫ y, |ρ y| with hmassdef
  have hmass : 0 ≤ mass := integral_nonneg fun y => abs_nonneg _
  refine ⟨16 * Ci * mass, by positivity, ?_⟩
  intro ε hε hε1 u h hu huε hh
  obtain ⟨D, hD⟩ := bounded_periodise ρ hρ hε
  have hPi : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hPm : Measurable (periodise ρ ε) := measurable_periodise ρ hρ
  have hKi : ∀ v : SpaceTime, Integrable (fun w : SpaceTime => hairerKernelTorus N (v - w) *
      periodise ρ ε w) := fun v =>
    (integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N)
      v).mul_bdd (c := D) hPm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hD _)
  have hdiff : hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u =
      ∫ w, (hairerKernelTorus N (u + h - w) - hairerKernelTorus N (u - w)) * periodise ρ ε w := by
    unfold hairerMollifiedKernel
    rw [← integral_sub (hKi (u + h)) (hKi u)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by simp only; ring)
  set G : ℝ := 16 * Ci * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) with hG
  have hs0 := torusParabolicSize_nonneg h
  have hG0 : 0 ≤ G := by
    have := Real.rpow_nonneg hu.le (-(4 : ℝ))
    positivity
  have hmaj : Integrable (fun w : SpaceTime => G * |periodise ρ ε w|) := hPi.norm.const_mul G
  have hpt : ∀ w : SpaceTime, ‖(hairerKernelTorus N (u + h - w) - hairerKernelTorus N (u - w)) *
      periodise ρ ε w‖ ≤ G * |periodise ρ ε w| := by
    intro w
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hp : periodise ρ ε w = 0
    · simp [hp]
    · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have hw := hsupp hε hε1 w hp
      have hlow : torusParabolicSize u / 2 ≤ torusParabolicSize (u - w) := by
        have := torusParabolicSize_sub_le_sub u w
        nlinarith
      have hpos : 0 < torusParabolicSize (u - w) := by linarith
      have h2 := hinc (z := u - w) (h := h) hpos (by linarith)
      rw [show u - w + h = u + h - w by abel] at h2
      refine h2.trans ?_
      have h3 := rpow_neg_four_half_le hu hlow
      calc Ci * torusParabolicSize h * torusParabolicSize (u - w) ^ (-(4 : ℝ))
          ≤ Ci * torusParabolicSize h * (16 * torusParabolicSize u ^ (-(4 : ℝ))) :=
            mul_le_mul_of_nonneg_left h3 (mul_nonneg hCi hs0)
        _ = G := by rw [hG]; ring
  have hPint : ∫ w : SpaceTime, |periodise ρ ε w| ≤ mass := by
    calc _ ≤ ∫ y, |rescale ρ ε y| := integral_abs_periodise_le ρ hρ hε hε1
      _ = mass := integral_abs_rescale_eq ρ hε
  rw [hdiff]
  calc ‖∫ w, (hairerKernelTorus N (u + h - w) - hairerKernelTorus N (u - w)) *
        periodise ρ ε w‖ ≤ ∫ w, G * |periodise ρ ε w| :=
        norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)
    _ = G * ∫ w, |periodise ρ ε w| := integral_const_mul G _
    _ ≤ G * mass := mul_le_mul_of_nonneg_left hPint hG0
    _ = 16 * Ci * mass * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := by
        rw [hG]; ring

/-- **Increment of `J_ε` for `s(u)/4 < s(h) ≤ s(u)/2`**, from the singular bound alone. -/
theorem hairerMollifiedKernel_increment_crude (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {u h : SpaceTime},
      0 < torusParabolicSize u → torusParabolicSize u / 4 < torusParabolicSize h →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
          C * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := by
  obtain ⟨CJ, hCJ, hJ⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  refine ⟨36 * CJ, by positivity, ?_⟩
  intro ε hε hε1 u h hu hh1 hh2
  have hlow : torusParabolicSize u / 2 ≤ torusParabolicSize (u + h) := by
    have := torusParabolicSize_sub_le_add u h
    linarith
  have hpos : 0 < torusParabolicSize (u + h) := by linarith
  have hJ' : ∀ z : SpaceTime, 0 < torusParabolicSize z →
      |hairerMollifiedKernel N ρ ε z| ≤ CJ * torusParabolicSize z ^ (-(3 : ℝ)) := by
    intro z hz
    refine (hJ hε hε1 z).trans (mul_le_mul_of_nonneg_left ?_ hCJ)
    exact Real.rpow_le_rpow_of_nonpos hz (by linarith) (by norm_num)
  have b0 := hJ' u hu
  have b1 := hJ' (u + h) hpos
  have h3 := rpow_neg_three_half_le hu hlow
  have e : torusParabolicSize u ^ (-(3 : ℝ)) =
      torusParabolicSize u * torusParabolicSize u ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_one_add' hu.le (by norm_num)]
    norm_num
  have hq0 := Real.rpow_nonneg hu.le (-(4 : ℝ))
  have hq : torusParabolicSize u ^ (-(3 : ℝ)) ≤
      4 * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := by
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) hq0
  have hsum : |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
      CJ * (8 * torusParabolicSize u ^ (-(3 : ℝ))) + CJ * torusParabolicSize u ^ (-(3 : ℝ)) :=
    (abs_sub _ _).trans (add_le_add (b1.trans (mul_le_mul_of_nonneg_left h3 hCJ)) b0)
  refine hsum.trans ?_
  have := mul_le_mul_of_nonneg_left hq hCJ
  nlinarith

/-- **Uniform increment bound for the mollified Hairer kernel**: for `ε ∈ (0, 1]`,
`|J_ε(u + h) - J_ε(u)| ≤ C s(h) s(u)⁻⁴` whenever `s(u) > 0` and `s(h) ≤ s(u)/2`. -/
theorem hairerMollifiedKernel_increment_uniform (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ (u h : SpaceTime),
      0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
          C * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := by
  obtain ⟨B, hB, hsupp⟩ := periodise_support_parabolic_bound ρ hρ
  obtain ⟨C1, hC1, h1⟩ := hairerMollifiedKernel_increment_near N hρ hB hsupp
  obtain ⟨C2, hC2, h2⟩ := hairerMollifiedKernel_increment_far N hρ hsupp
  obtain ⟨C3, hC3, h3⟩ := hairerMollifiedKernel_increment_crude N hρ
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro ε hε hε1 u h hu hh
  have hq0 := Real.rpow_nonneg hu.le (-(4 : ℝ))
  have hs0 := torusParabolicSize_nonneg h
  have hmono : ∀ {C : ℝ}, C ≤ C1 + C2 + C3 → 0 ≤ C → C * torusParabolicSize h *
      torusParabolicSize u ^ (-(4 : ℝ)) ≤ (C1 + C2 + C3) * torusParabolicSize h *
        torusParabolicSize u ^ (-(4 : ℝ)) := fun hC _ => by gcongr
  by_cases hsmall : torusParabolicSize h ≤ torusParabolicSize u / 4
  · by_cases hfar : 2 * B * ε ≤ torusParabolicSize u
    · exact (h2 hε hε1 hu hfar hsmall).trans (hmono (by linarith) hC2)
    · exact (h1 hε hε1 hu (le_of_not_ge hfar) hsmall).trans (hmono (by linarith) hC1)
  · exact (h3 hε hε1 hu (lt_of_not_ge hsmall) hh).trans (hmono (by linarith) hC3)

end RegularityStructures.Phi43

end

