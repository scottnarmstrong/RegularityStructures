/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Local
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2Field
public import Phi43.BPHZ.SemigroupTestTreesAssembly
public import Phi43.BPHZ.TreeI3Psi2TestedMoment

/-!
# The a-priori bound (10.2) for `I(Ψ³)Ψ²` against the periodised semigroup kernel

For `t ∈ (0, 1]`, `lam = t^(1/4)` and a base point `x ∈ ℝ⁴`,
`E|∫ F_{proj x}(w) q^♯_t(x, w) dw|² ≤ C lam^(-(1 + 2δ))` for `δ ∈ (0, 1/4]`, uniformly in
`ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x` (`hairerI3Psi2Field_semigroupPeriodised_second_moment_le_delta`);
with `δ' = 2δ` this is `lam^(-(1 + δ'))` for `δ' ∈ (0, 1/2]`
(`..._le_one_add`), and with `δ' = min (1/2, 9κ)` the bound `C lam^(-1 - 9κ)`
(`hairerI3Psi2Field_semigroupPeriodised_second_moment_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem sextic_region_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hnb : ¬(p ≤ 1 ∧ q ≤ 1)) :
    (1 + p ^ 2 + q ^ 2) ^ 3 ≤ 32 * (p ^ 6 + q ^ 6) := by
  have hR : 1 ≤ p ^ 2 + q ^ 2 := by
    by_contra hlt
    have := not_le.1 hlt
    apply hnb
    constructor <;> nlinarith [sq_nonneg p, sq_nonneg q]
  have a1 : 1 + p ^ 2 + q ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by linarith
  have a2 : (1 + p ^ 2 + q ^ 2) ^ 3 ≤ (2 * (p ^ 2 + q ^ 2)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) a1 3
  have a3 : (p ^ 2 + q ^ 2) ^ 3 ≤ 4 * (p ^ 6 + q ^ 6) := by
    nlinarith [sq_nonneg (p ^ 2 - q ^ 2), mul_nonneg (sq_nonneg p) (sq_nonneg q),
      sq_nonneg (p ^ 2), sq_nonneg (q ^ 2), mul_nonneg (mul_nonneg (sq_nonneg p) (sq_nonneg q))
        (add_nonneg (sq_nonneg p) (sq_nonneg q))]
  calc (1 + p ^ 2 + q ^ 2) ^ 3 ≤ (2 * (p ^ 2 + q ^ 2)) ^ 3 := a2
    _ = 8 * (p ^ 2 + q ^ 2) ^ 3 := by ring
    _ ≤ 8 * (4 * (p ^ 6 + q ^ 6)) := by linarith
    _ = 32 * (p ^ 6 + q ^ 6) := by ring

/-- **Second moment of the tested tree `I(Ψ³)Ψ²`, semigroup test, with loss `δ`.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x ∈ ℝ⁴`. -/
theorem hairerI3Psi2Field_semigroupPeriodised_second_moment_le_delta (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤ C * (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ)) := by
  obtain ⟨Cc, hCc, hloc⟩ := hairerI3Psi2Field_cov_bound.{u} N hρ hδ hδ1
  obtain ⟨Cg, hCg, hglob⟩ := hairerI3Psi2Field_cov_bound_global.{u} N hρ
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  refine ⟨Cc * |i3Psi2LocalConst B parabolicMomentConst δ| +
    32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)|,
    by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hL1 : 1 ≤ (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hYm := measurable_hairerI3Psi2Field_uncurry N hξ x'
  have hL2 := fun u => hairerI3Psi2Field_memLp N hρ hε.1 hW hξ x' u
  obtain ⟨M, hM'⟩ := exists_hairerI3Psi2Field_pair_integral_abs_le N hρ hε.1 hW hξ x'
  have hM : ∀ u : SpaceTime, ∫ ω, hairerI3Psi2Field N ρ ε ξ x' ω u *
      hairerI3Psi2Field N ρ ε ξ x' ω u ∂P ≤ M := by
    intro u
    obtain ⟨hi, hb⟩ := hM' u u
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => hairerI3Psi2Field N ρ ε ξ x' ω u) hYm
  have hMl := (h.doubleBound_i3Psi2Local hlam hlam1 hδ hδ1).const_mul hCc
  have hMg := (h.doubleBound_global hlam hlam1 (n := 6) (e := 5 / 2) (a := 5 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).const_mul
    (by positivity : (0 : ℝ) ≤ 32 * Cg)
  have hbound := semigroupDoubleBound_of_majorants (x := x') (Φ := fun u v => ∫ ω,
      hairerI3Psi2Field N ρ ε ξ x' ω u * hairerI3Psi2Field N ρ ε ξ x' ω v ∂P) h.measurable hΦ
    hMl hMg
    (fun u v => mul_nonneg hCc (i3Psi2LocalMajorant_nonneg x' δ u v))
    (fun u v => mul_nonneg (by positivity) (semigroupTestGlobalMajorant_nonneg x' 6 (5 / 2)
      (5 / 2) u v))
    (by
      filter_upwards [ae_pos_triple x'] with w hw h1 h2
      have hc := hloc hW hε hξ x' w.1 w.2 hw.1 hw.2.1 hw.2.2 h1 h2
      refine hc.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCc
      unfold i3Psi2Target
      rw [sub_sub_sub_cancel_right]
      simp only [i3Psi2LocalMajorant, Real.rpow_zero, mul_one, one_mul]
      linarith)
    (by
      filter_upwards [ae_pos_triple x'] with w hw hnb
      have hc := hglob hW hε hξ x' w.1 w.2 hw.1 hw.2.1 hw.2.2
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
      calc _ ≤ Cg * (32 * (torusParabolicSize (w.1 - x') ^ 6 + torusParabolicSize (w.2 - x') ^ 6)) *
            (torusParabolicSize (w.1 - w.2) ^ (-(5 / 2 : ℝ)) +
              torusParabolicSize (w.1 - x') ^ (-(5 / 2 : ℝ)) +
              torusParabolicSize (w.2 - x') ^ (-(5 / 2 : ℝ)) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hCg) hΘ
        _ = _ := by ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : Cc * (i3Psi2LocalConst B parabolicMomentConst δ *
      (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ))) ≤
      Cc * |i3Psi2LocalConst B parabolicMomentConst δ| * (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hCc)
      (Real.rpow_nonneg hlam.le _)
  have e2 : 32 * Cg * semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2) ≤
      32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| *
        (t ^ (1 / 4 : ℝ)) ^ (-(1 + 2 * δ)) := by
    have h0 : 0 ≤ 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| := by
      positivity
    calc 32 * Cg * semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)
        ≤ 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ = 32 * Cg * |semigroupTestGlobalConst B parabolicMomentConst 6 (5 / 2) (5 / 2)| * 1 := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL1 h0
  linarith

/-- **Second moment of the tested tree `I(Ψ³)Ψ²`, semigroup test, with loss `1 + δ'`.** -/
theorem hairerI3Psi2Field_semigroupPeriodised_second_moment_le_one_add (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {δ' : ℝ} (hδ : 0 < δ') (hδ1 : δ' ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤ C * (t ^ (1 / 4 : ℝ)) ^ (-(1 + δ')) := by
  obtain ⟨C, hC, h⟩ := hairerI3Psi2Field_semigroupPeriodised_second_moment_le_delta.{u} N hρ
    (δ := δ' / 2) (by linarith) (by linarith)
  refine ⟨C, hC, fun {Ω _ P W ε ξ} hW hε hξ {t} ht ht1 x => ?_⟩
  have e : -(1 + 2 * (δ' / 2)) = -(1 + δ') := by ring
  rw [e] at h
  exact h hW hε hξ ht ht1 x

/-- **The a-priori bound (10.2) for `I(Ψ³)Ψ²`, semigroup test** [Hai14, (10.2) for `I(Ψ³)Ψ²`]:
`E|∫ F_{proj x} q^♯_t(x, ·)|² ≤ C lam^(-1 - 9κ)`, uniformly in `ε ∈ (0, 1]`, `t ∈ (0, 1]`
and `x`, `lam = t^(1/4)`. -/
theorem hairerI3Psi2Field_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (-1 - 9 * κ) := by
  have hδ : 0 < min (1 / 2 : ℝ) (9 * κ) := lt_min (by norm_num) (by linarith)
  obtain ⟨C, hC, h⟩ := hairerI3Psi2Field_semigroupPeriodised_second_moment_le_one_add.{u} N hρ hδ
    (min_le_left _ _)
  refine ⟨C, hC, fun {Ω _ P W ε ξ} hW hε hξ {t} ht ht1 x => ?_⟩
  refine (h hW hε hξ ht ht1 x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) ?_
  have := min_le_right (1 / 2 : ℝ) (9 * κ)
  linarith

end RegularityStructures.Phi43

end
