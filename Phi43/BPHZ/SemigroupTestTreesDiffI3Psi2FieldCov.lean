/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2CovPair
public import Phi43.BPHZ.TreeI3Psi2DifferenceFieldCov
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Field

/-!
# The global covariance bound for the difference of the fields of `I(Ψ³)Ψ²`

`hairerI3Psi2Field_sub_cov_bound_cross_global`: for mollifiers `ρ`, `ρ'`, `θ ∈ (0, 1/16]`, scales
`ε, ε' ∈ (0, 1]` and noises `ξ`, `ξ'` of the same white noise regularised at `(ρ, ε)`, `(ρ', ε')`,
and all `x, y, y'` with `y, y' ≠ x`, `y ≠ y'` (no smallness),
`|E[(F - F')(y) (F - F')(y')]| ≤ C (max ε ε')^(2θ) (1 + s(y - x)² + s(y' - x)²)³
(s(y - y')^(-5/2) + s(y - x)^(-5/2) + s(y' - x)^(-5/2) + 1)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Covariance bound for the difference of the fields of `I(Ψ³)Ψ²`, two mollifiers.** -/
theorem hairerI3Psi2Field_sub_cov_bound_cross_global (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
          |∫ ω, (hairerI3Psi2Field N ρ ε ξ x ω y - hairerI3Psi2Field N ρ' ε' ξ' x ω y) *
              (hairerI3Psi2Field N ρ ε ξ x ω y' - hairerI3Psi2Field N ρ' ε' ξ' x ω y') ∂P| ≤
            C * (max ε ε') ^ (2 * θ) *
              (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3 *
              (torusParabolicSize (y - y') ^ (-(5 / 2 : ℝ)) +
                torusParabolicSize (y - x) ^ (-(5 / 2 : ℝ)) +
                torusParabolicSize (y' - x) ^ (-(5 / 2 : ℝ)) + 1) := by
  have hθ1' : θ ≤ 1 := by linarith
  obtain ⟨BK, hBK, hKm, hKs, hK, -⟩ := hairerKernelTorus_diagram_data N
  obtain ⟨CJ, hCJ, hJ⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  obtain ⟨CJ', hCJ', hJ'⟩ := hairerMollifiedKernel_singular_bound ρ' hρ' N
  obtain ⟨CI, hCI, hJi⟩ := hairerMollifiedKernel_increment_uniform N hρ
  obtain ⟨CI', hCI', hJi'⟩ := hairerMollifiedKernel_increment_uniform N hρ'
  obtain ⟨CD, hCD, hD⟩ := hairerMollifiedKernel_sub_abs_le_cross_of_pos N ρ ρ' hρ hρ' hθ hθ1'
  obtain ⟨CD1, hCD1, hD1⟩ := hairerMollifiedKernel_sub_abs_le_cross_of_pos N ρ ρ' hρ hρ' one_pos
    le_rfl
  obtain ⟨A, hA, hTab⟩ := hairerCrossTwo_tables_bd N ρ ρ' hρ hρ' hθ hθ1'
  set B : ℝ := 17 * (BK + CJ + CJ' + CI + CI' + CD + CD1) with hBdef
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  obtain ⟨C0, hC0, hmain⟩ := i3Psi2CovPair_second_diff_bound_global (B := B) (A := A) (δ := 1 / 8)
    hB hA (by norm_num) le_rfl hθ hθ1
  refine ⟨125 * C0, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hz hz' hzz
  obtain ⟨hε0, hε1⟩ := hε
  obtain ⟨hε'0, hε'1⟩ := hε'
  have hmax0 : 0 < max ε ε' := lt_max_of_lt_left hε0
  have hmax : (0 : ℝ) ≤ max ε ε' := hmax0.le
  set μ : ℝ := (max ε ε') ^ θ with hμdef
  have hμ : 0 ≤ μ := Real.rpow_nonneg hmax _
  have hsum : BK ≤ B ∧ CJ ≤ B ∧ CJ' ≤ B ∧ CI ≤ B ∧ CI' ≤ B ∧ CD ≤ B ∧ 17 * (CI + CI' + CD1) ≤ B := by
    rw [hBdef]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hsum
  have rn : ∀ (z : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize z ^ e := fun z e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hKi : Integrable (hairerKernelTorus N) := integrable_K hBK hKm hKs hK
  have hK' : ∀ z, 0 < torusParabolicSize z →
      |hairerKernelTorus N z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz =>
    (hK z hz).trans (mul_le_mul_of_nonneg_right hs1 (rn z _))
  have hJa : ∀ z, 0 < torusParabolicSize z →
      |hairerMollifiedKernel N ρ ε z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz => by
    refine (hJ hε0 hε1 z).trans ?_
    refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz (by linarith) (by norm_num))
      hCJ).trans ?_
    exact mul_le_mul_of_nonneg_right hs2 (rn z _)
  have hJb : ∀ z, 0 < torusParabolicSize z →
      |hairerMollifiedKernel N ρ' ε' z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ)) := fun z hz => by
    refine (hJ' hε'0 hε'1 z).trans ?_
    refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hz (by linarith) (by norm_num))
      hCJ').trans ?_
    exact mul_le_mul_of_nonneg_right hs3 (rn z _)
  have hJainc : ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
        B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := fun u h hu hh =>
    (hJi hε0 hε1 u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs4 (torusParabolicSize_nonneg _)) (rn u _))
  have hJbinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |hairerMollifiedKernel N ρ' ε' (u + h) - hairerMollifiedKernel N ρ' ε' u| ≤
        (CI + CI' + CD1) * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := fun u h hu hh =>
    (hJi' hε'0 hε'1 u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _)) (rn u _))
  have hJainc0 : ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ ε u| ≤
        (CI + CI' + CD1) * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)) := fun u h hu hh =>
    (hJi hε0 hε1 u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _)) (rn u _))
  have hΔJ : ∀ z, 0 < torusParabolicSize z →
      |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
        B * μ * torusParabolicSize z ^ (-(3 + θ)) := fun z hz =>
    (hD hε0 hε1 hε'0 hε'1 z hz).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hs6 hμ) (rn z _))
  have hΔ1 : ∀ z, 0 < torusParabolicSize z →
      |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
        (CI + CI' + CD1) * max ε ε' * torusParabolicSize z ^ (-(4 : ℝ)) := fun z hz => by
    have := hD1 hε0 hε1 hε'0 hε'1 z hz
    rw [Real.rpow_one] at this
    have e : (-(3 + 1) : ℝ) = -(4 : ℝ) := by norm_num
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hmax) (rn z _)
  have hΔJinc := holder_increment_sub_of_bounds (θ := θ) (B := CI + CI' + CD1) (m := max ε ε')
    (by positivity) hmax hθ hθ1' hJainc0 hJbinc hΔ1
  have hΔJinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
      |(hairerMollifiedKernel N ρ ε (u + h) - hairerMollifiedKernel N ρ' ε' (u + h)) -
          (hairerMollifiedKernel N ρ ε u - hairerMollifiedKernel N ρ' ε' u)| ≤
        B * μ * torusParabolicSize h ^ (1 - θ) * torusParabolicSize u ^ (-(3 + θ) - (1 - θ)) :=
    fun u h hu hh => (hΔJinc u h hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs7 hμ) (rn h _)) (rn u _))
  have hMa : ∀ z, |hairerMollifiedKernel N ρ ε z| ≤ CJ * ε ^ (-(3 : ℝ)) := fun z =>
    (hJ hε0 hε1 z).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε0
      (by linarith [torusParabolicSize_nonneg z]) (by norm_num)) hCJ)
  have hMb : ∀ z, |hairerMollifiedKernel N ρ' ε' z| ≤ CJ' * ε' ^ (-(3 : ℝ)) := fun z =>
    (hJ' hε'0 hε'1 z).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε'0
      (by linarith [torusParabolicSize_nonneg z]) (by norm_num)) hCJ')
  set t : ℝ := |(y - x).1| with ht
  set t' : ℝ := |(y' - x).1| with ht'
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht0' : 0 ≤ t' := abs_nonneg _
  have hDD : ∀ a b : SpaceTime, |a.1| ≤ t + t' + 2 → |b.1| ≤ t + t' + 2 →
      torusParabolicSize (a - b) ≤ √(2 * (t + t' + 2)) + 1 := by
    intro a b ha hb
    refine torusParabolicSize_le_sqrt_add_one ?_
    have : (a - b).1 = a.1 - b.1 := rfl
    rw [this]
    have := abs_sub a.1 b.1
    linarith
  have hmain' := hmain (K := hairerKernelTorus N) (Ja := hairerMollifiedKernel N ρ ε)
    (Jb := hairerMollifiedKernel N ρ' ε') (Q₁₁ := hairerCrossCovarianceTwo N ρ ε ρ ε)
    (Q₁₂ := hairerCrossCovarianceTwo N ρ ε ρ' ε') (Q₂₁ := hairerCrossCovarianceTwo N ρ' ε' ρ ε)
    (Q₂₂ := hairerCrossCovarianceTwo N ρ' ε' ρ' ε') (μ := μ)
    (D := √(2 * (t + t' + 2)) + 1) hμ (by positivity) hKs hKi hKm hK'
    (measurable_hairerMollifiedKernel N hρ ε) (measurable_hairerMollifiedKernel N hρ' ε') hMa hMb
    (integrable_hairerMollifiedKernel N ρ hρ hε0) (integrable_hairerMollifiedKernel N ρ' hρ' hε'0)
    hJa hJainc hΔJ hΔJinc' (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl
    (hTab hε0 hε1 hε'0 hε'1) (y - x) (y' - x) hDD hz hz' (by rwa [sub_sub_sub_cancel_right])
  rw [(hairerI3Psi2Field_sub_integral_mulTwo N hρ hρ' hε0 hε'0 hW hξ hξ' x y y').2]
  simp only [hairerI3Psi2CovTwo_eq_i3Psi2CovPair]
  have e2 : μ ^ 2 = (max ε ε') ^ (2 * θ) := by
    rw [hμdef, ← Real.rpow_natCast, ← Real.rpow_mul hmax]
    congr 1
    push_cast; ring
  rw [e2] at hmain'
  refine hmain'.trans ?_
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have e1' := abs_fst_le_sq_torusParabolicSize (y' - x)
  have hpoly := poly_prefactor_le ht0 ht0' (a := torusParabolicSize (y - x) ^ 2)
    (b := torusParabolicSize (y' - x) ^ 2) e1 e1'
  have hT : treeTheta (y - x) (y' - x) = torusParabolicSize (y - y') ^ (-(5 / 2 : ℝ)) +
      torusParabolicSize (y - x) ^ (-(5 / 2 : ℝ)) + torusParabolicSize (y' - x) ^ (-(5 / 2 : ℝ)) +
        1 := by
    unfold treeTheta
    rw [sub_sub_sub_cancel_right]
  have hT0 : 0 ≤ treeTheta (y - x) (y' - x) := treeTheta_nonneg _ _
  rw [hT] at hT0 ⊢
  have hm0 : 0 ≤ C0 * (max ε ε') ^ (2 * θ) := mul_nonneg hC0 (Real.rpow_nonneg hmax _)
  calc C0 * (max ε ε') ^ (2 * θ) * ((1 + (√(2 * (t + t' + 2)) + 1)) ^ 2 * (1 + t + t')) * _
      ≤ C0 * (max ε ε') ^ (2 * θ) * (125 * (1 + torusParabolicSize (y - x) ^ 2 +
        torusParabolicSize (y' - x) ^ 2) ^ 3) * _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hm0) hT0
    _ = _ := by ring


end RegularityStructures.Phi43

end
