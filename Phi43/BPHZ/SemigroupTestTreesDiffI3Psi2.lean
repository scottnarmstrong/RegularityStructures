/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Local
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2FieldCov
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2
public import Phi43.BPHZ.TreeI3Psi2DifferenceFieldCov
public import Phi43.BPHZ.TreeI3Psi2DifferenceMoment

/-!
# The difference bound for `I(Ψ³)Ψ²` against the periodised semigroup kernel

For mollifiers `ρ`, `ρ'`, `θ ∈ (0, 1/16]`, `δ ∈ (0, 1/8]`, `ε, ε' ∈ (0, 1]`, `t ∈ (0, 1]` and a base
point `x ∈ ℝ⁴`,
`E|∫ (F_{ρ,ε} - F_{ρ',ε'})(proj x)(w) q^♯_t(x, w) dw|² ≤ C (max ε ε')^(2θ) lam^(-(1 + 2δ + 2θ))`,
`lam = t^(1/4)` (`hairerI3Psi2Field_sub_semigroupPeriodised_second_moment_le_delta`), from the
local cross bound on `{s(u - x), s(v - x) ≤ 1}` and the global bound on the complement.  With
`δ = min (1/8) (7κ/2)` and `θ ≤ κ ≤ 1/16` the exponent is at most `1 + 9κ`
(`hairerI3Psi2Field_sub_semigroupPeriodised_second_moment_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of the tested difference of `I(Ψ³)Ψ²`, semigroup test, with loss `δ`.** -/
theorem hairerI3Psi2Field_sub_semigroupPeriodised_second_moment_le_delta (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 16) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω w -
            hairerI3Psi2Field N ρ' ε' ξ' (spaceTimeProj x) ω w) * semigroupPeriodised t x w| ^ 2
          ∂P ≤ C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ)) := by
  obtain ⟨Cc, hCc, hloc⟩ := hairerI3Psi2Field_sub_cov_bound_cross.{u} N hρ hρ' hθ hθ1 hδ hδ1
  obtain ⟨Cg, hCg, hglob⟩ := hairerI3Psi2Field_sub_cov_bound_cross_global.{u} N hρ hρ' hθ hθ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨Cc * |i3Psi2DiffLocalConst B parabolicMomentConst δ θ| +
    32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)|,
    by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  set μ : ℝ := (max ε ε') ^ (2 * θ) with hμdef
  have hμ : 0 ≤ μ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hL1 : 1 ≤ (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hYm := measurable_hairerI3Psi2Field_sub_uncurry N hξ hξ' x'
  have hL2 := fun w => hairerI3Psi2Field_sub_memLp N hρ hρ' hε.1 hε'.1 hW hξ hξ' x' w
  obtain ⟨M, hM'⟩ := hairerI3Psi2Field_sub_pair_integrable_bound N hρ hρ' hε.1 hε'.1 hW hξ hξ' x'
  have hM : ∀ w : SpaceTime, ∫ ω, (hairerI3Psi2Field N ρ ε ξ x' ω w -
      hairerI3Psi2Field N ρ' ε' ξ' x' ω w) * (hairerI3Psi2Field N ρ ε ξ x' ω w -
      hairerI3Psi2Field N ρ' ε' ξ' x' ω w) ∂P ≤ M := by
    intro w
    obtain ⟨hi, hb⟩ := hM' w w
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω w => hairerI3Psi2Field N ρ ε ξ x' ω w - hairerI3Psi2Field N ρ' ε' ξ' x' ω w) hYm
  have hMl := (h.doubleBound_i3Psi2DiffLocal hlam hlam1 hδ hδ1 hθ hθ1).const_mul
    (mul_nonneg hμ hCc)
  have hMg := (h.doubleBound_global hlam hlam1 (n := 6) (e := 5 / 2) (a := 5 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).const_mul
    (mul_nonneg hμ (by positivity : (0 : ℝ) ≤ 32 * Cg))
  have hbound := semigroupDoubleBound_of_majorants (x := x') (Φ := fun w w' => ∫ ω,
      (hairerI3Psi2Field N ρ ε ξ x' ω w - hairerI3Psi2Field N ρ' ε' ξ' x' ω w) *
        (hairerI3Psi2Field N ρ ε ξ x' ω w' - hairerI3Psi2Field N ρ' ε' ξ' x' ω w') ∂P)
    h.measurable hΦ hMl hMg
    (fun w w' => mul_nonneg (mul_nonneg hμ hCc) (i3Psi2DiffLocalMajorant_nonneg x' δ θ w w'))
    (fun w w' => mul_nonneg (mul_nonneg hμ (by positivity))
      (semigroupTestGlobalMajorant_nonneg x' 6 (5 / 2) (5 / 2) w w'))
    (by
      filter_upwards [ae_pos_triple x'] with w hw h1 h2
      have hc := hloc hW hε hε' hξ hξ' x' w.1 w.2 hw.1 hw.2.1 hw.2.2 h1 h2
      refine hc.trans (le_of_eq ?_)
      rw [i3Psi2DiffLocalMajorant_eq]
      ring)
    (by
      filter_upwards [ae_pos_triple x'] with w hw hnb
      have hc := hglob hW hε hε' hξ hξ' x' w.1 w.2 hw.1 hw.2.1 hw.2.2
      refine hc.trans ?_
      rw [semigroupTestGlobalMajorant_eq (n := 6) (e := 5 / 2) (a := 5 / 2) hw.1 hw.2.1]
      have hu6 : torusParabolicSize (w.1 - x') ^ (6 : ℝ) = torusParabolicSize (w.1 - x') ^ 6 := by
        exact_mod_cast Real.rpow_natCast (torusParabolicSize (w.1 - x')) 6
      have hv6 : torusParabolicSize (w.2 - x') ^ (6 : ℝ) = torusParabolicSize (w.2 - x') ^ 6 := by
        exact_mod_cast Real.rpow_natCast (torusParabolicSize (w.2 - x')) 6
      rw [hu6, hv6]
      have hs := sextic_region_le (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) hnb
      have hΘ : 0 ≤ torusParabolicSize (w.1 - w.2) ^ (-(5 / 2 : ℝ)) +
          torusParabolicSize (w.1 - x') ^ (-(5 / 2 : ℝ)) +
          torusParabolicSize (w.2 - x') ^ (-(5 / 2 : ℝ)) + 1 := by
        have := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - w.2)) (-(5 / 2 : ℝ))
        have := Real.rpow_nonneg (torusParabolicSize_nonneg (w.1 - x')) (-(5 / 2 : ℝ))
        have := Real.rpow_nonneg (torusParabolicSize_nonneg (w.2 - x')) (-(5 / 2 : ℝ))
        linarith
      have hCm : 0 ≤ Cg * μ := mul_nonneg hCg hμ
      calc _ ≤ Cg * μ * (32 * (torusParabolicSize (w.1 - x') ^ 6 +
            torusParabolicSize (w.2 - x') ^ 6)) *
            (torusParabolicSize (w.1 - w.2) ^ (-(5 / 2 : ℝ)) +
              torusParabolicSize (w.1 - x') ^ (-(5 / 2 : ℝ)) +
              torusParabolicSize (w.2 - x') ^ (-(5 / 2 : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hCm) hΘ
        _ = _ := by ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : μ * Cc * (i3Psi2DiffLocalConst B parabolicMomentConst δ θ *
      (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ))) ≤
      Cc * |i3Psi2DiffLocalConst B parabolicMomentConst δ θ| * μ *
        (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ)) := by
    have : i3Psi2DiffLocalConst B parabolicMomentConst δ θ ≤
        |i3Psi2DiffLocalConst B parabolicMomentConst δ θ| := le_abs_self _
    have hp : 0 ≤ (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ)) := Real.rpow_nonneg hlam.le _
    calc _ = (μ * Cc) * (i3Psi2DiffLocalConst B parabolicMomentConst δ θ *
          (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ))) := by ring
      _ ≤ (μ * Cc) * (|i3Psi2DiffLocalConst B parabolicMomentConst δ θ| *
          (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hp) (mul_nonneg hμ hCc)
      _ = _ := by ring
  have e2 : μ * (32 * Cg) * semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2) ≤
      32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| * μ *
        (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ + 2 * θ)) := by
    have h0 : 0 ≤ 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| *
        μ := by positivity
    calc μ * (32 * Cg) * semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)
        ≤ μ * (32 * Cg) * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hμ (by positivity))
      _ = 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| * μ * 1 := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 h0
  nlinarith [e1, e2]

end RegularityStructures.Phi43

end
