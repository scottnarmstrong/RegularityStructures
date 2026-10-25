/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiCov
public import Phi43.BPHZ.ProductPiDouble
public import Phi43.BPHZ.SemigroupTestTreesAssembly

/-!
# The second moment of `I(Ψ²)Ψ` against the periodised semigroup kernel

For `δ ∈ (0, 1/2]`, `t ∈ (0, 1]`, `lam = t^(1/4)` and a base point `x`,
`E|∫ I₂Ψ_{proj x}(w) q^♯_t(x, w) dw|² ≤ C lam^(1 - δ)`, uniformly in `ε ∈ (0, 1]`, `t`, `x`
(`productISqPsiField_semigroupPeriodised_second_moment_le`).  The covariance bound of
`productISqPsiField_cov_bound` with `θ = 1 - δ/2`, `η = (1 - δ)/2` is dominated by two polynomially
weighted majorants, each with double bound `lam^(1 - δ)` (`doubleBound_productPoly`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_mul_rpow_le_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (θ : ℝ) :
    a ^ θ * b ^ θ ≤ (a ^ (2 * θ) + b ^ (2 * θ)) / 2 := by
  have e : ∀ c : ℝ, 0 ≤ c → c ^ (2 * θ) = (c ^ θ) ^ 2 := by
    intro c hc
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
    norm_num [mul_comm]
  rw [e a ha, e b hb]
  linarith [sq_nonneg (a ^ θ - b ^ θ)]

/-- **Second moment of `I(Ψ²)Ψ` against the periodised semigroup kernel** (loss `δ`). -/
theorem productISqPsiField_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, productISqPsiField N ρ ε ξ (spaceTimeProj x) ω w *
            semigroupPeriodised t x w| ^ 2 ∂P ≤ C * (t ^ (1 / 4 : ℝ)) ^ (1 - δ) := by
  have hθ0 : 0 < 1 - δ / 2 := by linarith
  have hθ1 : 1 - δ / 2 < 1 := by linarith
  have hη0 : 0 < (1 - δ) / 2 := by linarith
  have hη1 : (1 - δ) / 2 < 1 / 2 := by linarith
  obtain ⟨Cc, hCc, hcov⟩ := productISqPsiField_cov_bound N hρ hθ0 hθ1 hη0 hη1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  set K1 : ℝ := |productPolyConst B parabolicMomentConst (2 * (1 - δ / 2)) 1| with hK1
  set K2 : ℝ := |productPolyConst B parabolicMomentConst (2 * ((1 - δ) / 2)) 0| with hK2
  refine ⟨Cc / 2 * (K1 + K2), by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hYm := measurable_productISqPsiField_uncurry N hξ x'
  have hL2 := fun u => productISqPsiField_memLp N hρ hε.1 hW hξ x' u
  have hM : ∀ u : SpaceTime, ∫ ω, productISqPsiField N ρ ε ξ x' ω u *
      productISqPsiField N ρ ε ξ x' ω u ∂P ≤
      10 * hairerWickConstant N ρ ε ^ 3 * ((2 * ∫ w, |hairerKernelTorus N w|) *
        (2 * ∫ w, |hairerKernelTorus N w|)) := by
    intro u
    obtain ⟨hi, hb⟩ := productISqPsiField_pair_integrable_bound N hρ hε.1 hW hξ x' u u
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => productISqPsiField N ρ ε ξ x' ω u) hYm
  have hd1 := h.doubleBound_productPoly hlam hlam1 (p := 2 * (1 - δ / 2)) (e := 1)
    (by linarith) (by norm_num)
  have hd2 := h.doubleBound_productPoly hlam hlam1 (p := 2 * ((1 - δ) / 2)) (e := 0)
    (by linarith) (by norm_num)
  have hMaj := (hd1.add hd2).const_mul (c := Cc / 2) (by positivity)
  have hbound := SemigroupDoubleBound.of_abs_le h.measurable hMaj
    (F := fun u v => ∫ ω, productISqPsiField N ρ ε ξ x' ω u *
      productISqPsiField N ρ ε ξ x' ω v ∂P) hΦ (by
      filter_upwards [ae_pos_triple x'] with w hw
      have hc := hcov hW hε hξ x' w.1 w.2 hw.2.2
      refine hc.trans ?_
      have a1 := rpow_mul_rpow_le_half (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) (1 - δ / 2)
      have a2 := rpow_mul_rpow_le_half (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) ((1 - δ) / 2)
      have p0 : 0 ≤ 1 + torusParabolicSize (w.1 - x') ^ 2 := by positivity
      have d0 : 0 ≤ torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) :=
        Real.rpow_nonneg (torusParabolicSize_nonneg _) _
      have r0 := fun (u : SpaceTime) (e : ℝ) =>
        Real.rpow_nonneg (torusParabolicSize_nonneg u) e
      simp only [productPolyMajorant, Real.rpow_zero, neg_zero]
      have b1 := mul_le_mul_of_nonneg_left a1 (mul_nonneg p0 d0)
      have b2 := mul_le_mul_of_nonneg_left a2 p0
      have key : (1 + torusParabolicSize (w.1 - x') ^ 2) *
          (torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) *
            (torusParabolicSize (w.1 - x') ^ (1 - δ / 2) *
              torusParabolicSize (w.2 - x') ^ (1 - δ / 2))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ ((1 - δ) / 2) *
              torusParabolicSize (w.2 - x') ^ ((1 - δ) / 2)) ≤
          ((1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * (1 - δ / 2)) +
              torusParabolicSize (w.2 - x') ^ (2 * (1 - δ / 2))) *
            torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * ((1 - δ) / 2)) +
              torusParabolicSize (w.2 - x') ^ (2 * ((1 - δ) / 2))) * 1) / 2 := by
        linarith [b1, b2]
      calc Cc * (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) *
              (torusParabolicSize (w.1 - x') ^ (1 - δ / 2) *
                torusParabolicSize (w.2 - x') ^ (1 - δ / 2)) +
              torusParabolicSize (w.1 - x') ^ ((1 - δ) / 2) *
                torusParabolicSize (w.2 - x') ^ ((1 - δ) / 2))
          = Cc * ((1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) *
              (torusParabolicSize (w.1 - x') ^ (1 - δ / 2) *
                torusParabolicSize (w.2 - x') ^ (1 - δ / 2))) +
            (1 + torusParabolicSize (w.1 - x') ^ 2) *
              (torusParabolicSize (w.1 - x') ^ ((1 - δ) / 2) *
                torusParabolicSize (w.2 - x') ^ ((1 - δ) / 2))) := by ring
        _ ≤ Cc * (((1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * (1 - δ / 2)) +
              torusParabolicSize (w.2 - x') ^ (2 * (1 - δ / 2))) *
            torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * ((1 - δ) / 2)) +
              torusParabolicSize (w.2 - x') ^ (2 * ((1 - δ) / 2))) * 1) / 2) :=
            mul_le_mul_of_nonneg_left key hCc
        _ = _ := by ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : (2 * (1 - δ / 2) - 1 : ℝ) = 1 - δ := by ring
  have e2 : (2 * ((1 - δ) / 2) - 0 : ℝ) = 1 - δ := by ring
  rw [e1, e2]
  have l0 := Real.rpow_nonneg hlam.le (1 - δ)
  have k1 : productPolyConst B parabolicMomentConst (2 * (1 - δ / 2)) 1 ≤ K1 := le_abs_self _
  have k2 : productPolyConst B parabolicMomentConst (2 * ((1 - δ) / 2)) 0 ≤ K2 := le_abs_self _
  nlinarith [mul_le_mul_of_nonneg_right k1 l0, mul_le_mul_of_nonneg_right k2 l0]

end RegularityStructures.Phi43

end
