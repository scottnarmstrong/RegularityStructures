/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiDiffCov
public import Phi43.BPHZ.ProductPiDouble
public import Phi43.BPHZ.SemigroupTestTreesAssembly

/-!
# The second moment of the difference of `I(Ψ²)Ψ` at two mollifiers

For `θ > 0`, `δ > 0` with `2θ + δ < 1`, `t ∈ (0, 1]`, `lam = t^(1/4)`:
`E|∫ (I₂Ψ_{ρ,ε} - I₂Ψ_{ρ',ε'})_{proj x} q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(1 - δ - 2θ)`
(`productISqPsiField_sub_semigroupPeriodised_second_moment_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_mul_rpow_le_half' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (θ : ℝ) :
    a ^ θ * b ^ θ ≤ (a ^ (2 * θ) + b ^ (2 * θ)) / 2 := by
  have e : ∀ c : ℝ, 0 ≤ c → c ^ (2 * θ) = (c ^ θ) ^ 2 := by
    intro c hc
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
    norm_num [mul_comm]
  rw [e a ha, e b hb]
  linarith [sq_nonneg (a ^ θ - b ^ θ)]

/-- **Second moment of the tested two-mollifier difference of `I(Ψ²)Ψ`.** -/
theorem productISqPsiField_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 < δ) (hθδ : 2 * θ + δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (productISqPsiField N ρ ε ξ (spaceTimeProj x) ω w -
            productISqPsiField N ρ' ε' ξ' (spaceTimeProj x) ω w) * semigroupPeriodised t x w| ^ 2
          ∂P ≤ C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (1 - δ - 2 * θ) := by
  obtain ⟨Cc, hCc, hcov⟩ := productISqPsiField_sub_cov_bound.{u} N hρ hρ' hθ hθ1 hδ hθδ
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  set K1 : ℝ := |productPolyConst B parabolicMomentConst (2 * (1 - δ / 2 - θ)) 1| with hK1
  set K2 : ℝ := |productPolyConst B parabolicMomentConst (2 * (1 - δ / 2)) (1 + 2 * θ)| with hK2
  set K3 : ℝ := |productPolyConst B parabolicMomentConst (2 * ((1 - δ) / 2 - θ)) 0| with hK3
  refine ⟨Cc / 2 * (K1 + K2 + K3), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  set x' : SpaceTime := spaceTimeProj x with hx'
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hmax : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hμ : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hmax.le _
  have hYm : Measurable (fun q : Ω × SpaceTime => productISqPsiField N ρ ε ξ x' q.1 q.2 -
      productISqPsiField N ρ' ε' ξ' x' q.1 q.2) :=
    (measurable_productISqPsiField_uncurry N hξ x').sub
      (measurable_productISqPsiField_uncurry N hξ' x')
  have hL2 := fun u => productISqPsiField_sub_memLp_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x' u
  obtain ⟨M, hMb⟩ := productISqPsiField_sub_pair_integrable_bound_cross N hρ hρ' hε.1 hε'.1 hW hξ
    hξ' x'
  have hM : ∀ u : SpaceTime, ∫ ω, (productISqPsiField N ρ ε ξ x' ω u -
      productISqPsiField N ρ' ε' ξ' x' ω u) * (productISqPsiField N ρ ε ξ x' ω u -
      productISqPsiField N ρ' ε' ξ' x' ω u) ∂P ≤ M := by
    intro u
    obtain ⟨hi, hb⟩ := hMb u u
    exact (integral_mono hi hi.abs fun ω => le_abs_self _).trans hb
  have hΦ := aestronglyMeasurable_cov (P := P)
    (Y := fun ω u => productISqPsiField N ρ ε ξ x' ω u - productISqPsiField N ρ' ε' ξ' x' ω u)
    hYm
  have d1 := h.doubleBound_productPoly hlam hlam1 (p := 2 * (1 - δ / 2 - θ)) (e := 1)
    (by linarith) (by norm_num)
  have d2 := h.doubleBound_productPoly hlam hlam1 (p := 2 * (1 - δ / 2)) (e := 1 + 2 * θ)
    (by linarith) (by linarith)
  have d3 := h.doubleBound_productPoly hlam hlam1 (p := 2 * ((1 - δ) / 2 - θ)) (e := 0)
    (by linarith) (by norm_num)
  have hMaj := ((d1.add d2).add d3).const_mul (c := Cc * (max ε ε') ^ (2 * θ) / 2)
    (by positivity)
  have hbound := SemigroupDoubleBound.of_abs_le h.measurable hMaj
    (F := fun u v => ∫ ω, (productISqPsiField N ρ ε ξ x' ω u -
      productISqPsiField N ρ' ε' ξ' x' ω u) * (productISqPsiField N ρ ε ξ x' ω v -
      productISqPsiField N ρ' ε' ξ' x' ω v) ∂P) hΦ (by
      filter_upwards [ae_pos_triple x'] with w hw
      have hc := hcov hW hε hε' hξ hξ' x' w.1 w.2 hw.2.2
      refine hc.trans ?_
      have r0 := fun (u : SpaceTime) (e : ℝ) =>
        Real.rpow_nonneg (torusParabolicSize_nonneg u) e
      have a1 := rpow_mul_rpow_le_half' (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) (1 - δ / 2 - θ)
      have a2 := rpow_mul_rpow_le_half' (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) (1 - δ / 2)
      have a3 := rpow_mul_rpow_le_half' (torusParabolicSize_nonneg (w.1 - x'))
        (torusParabolicSize_nonneg (w.2 - x')) ((1 - δ) / 2 - θ)
      have p0 : 0 ≤ 1 + torusParabolicSize (w.1 - x') ^ 2 := by positivity
      simp only [productPolyMajorant, Real.rpow_zero, neg_zero]
      have b1 := mul_le_mul_of_nonneg_left a1
        (mul_nonneg p0 (r0 (w.1 - w.2) (-(1 : ℝ))))
      have b2 := mul_le_mul_of_nonneg_left a2
        (mul_nonneg p0 (r0 (w.1 - w.2) (-(1 + 2 * θ))))
      have b3 := mul_le_mul_of_nonneg_left a3 p0
      have key : (1 + torusParabolicSize (w.1 - x') ^ 2) *
          (torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) *
            (torusParabolicSize (w.1 - x') ^ (1 - δ / 2 - θ) *
              torusParabolicSize (w.2 - x') ^ (1 - δ / 2 - θ))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - w.2) ^ (-(1 + 2 * θ)) *
              (torusParabolicSize (w.1 - x') ^ (1 - δ / 2) *
                torusParabolicSize (w.2 - x') ^ (1 - δ / 2))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ ((1 - δ) / 2 - θ) *
              torusParabolicSize (w.2 - x') ^ ((1 - δ) / 2 - θ)) ≤
          (((1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * (1 - δ / 2 - θ)) +
              torusParabolicSize (w.2 - x') ^ (2 * (1 - δ / 2 - θ))) *
            torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * (1 - δ / 2)) +
              torusParabolicSize (w.2 - x') ^ (2 * (1 - δ / 2))) *
            torusParabolicSize (w.1 - w.2) ^ (-(1 + 2 * θ))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * ((1 - δ) / 2 - θ)) +
              torusParabolicSize (w.2 - x') ^ (2 * ((1 - δ) / 2 - θ))) * 1) / 2 := by
        linarith [b1, b2, b3]
      have hCm : 0 ≤ Cc * (max ε ε') ^ (2 * θ) := mul_nonneg hCc hμ
      calc _ = (Cc * (max ε ε') ^ (2 * θ)) * (
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
          (torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) *
            (torusParabolicSize (w.1 - x') ^ (1 - δ / 2 - θ) *
              torusParabolicSize (w.2 - x') ^ (1 - δ / 2 - θ))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - w.2) ^ (-(1 + 2 * θ)) *
              (torusParabolicSize (w.1 - x') ^ (1 - δ / 2) *
                torusParabolicSize (w.2 - x') ^ (1 - δ / 2))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ ((1 - δ) / 2 - θ) *
              torusParabolicSize (w.2 - x') ^ ((1 - δ) / 2 - θ))) := by ring
        _ ≤ (Cc * (max ε ε') ^ (2 * θ)) * ((((1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * (1 - δ / 2 - θ)) +
              torusParabolicSize (w.2 - x') ^ (2 * (1 - δ / 2 - θ))) *
            torusParabolicSize (w.1 - w.2) ^ (-(1 : ℝ)) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * (1 - δ / 2)) +
              torusParabolicSize (w.2 - x') ^ (2 * (1 - δ / 2))) *
            torusParabolicSize (w.1 - w.2) ^ (-(1 + 2 * θ))) +
          (1 + torusParabolicSize (w.1 - x') ^ 2) *
            (torusParabolicSize (w.1 - x') ^ (2 * ((1 - δ) / 2 - θ)) +
              torusParabolicSize (w.2 - x') ^ (2 * ((1 - δ) / 2 - θ))) * 1) / 2) :=
            mul_le_mul_of_nonneg_left key hCm
        _ = _ := by ring)
  have hmain := secondMoment_le_of_semigroupDoubleBound hYm hL2 hM h hbound
  refine hmain.trans ?_
  have e1 : (2 * (1 - δ / 2 - θ) - 1 : ℝ) = 1 - δ - 2 * θ := by ring
  have e2 : (2 * (1 - δ / 2) - (1 + 2 * θ) : ℝ) = 1 - δ - 2 * θ := by ring
  have e3 : (2 * ((1 - δ) / 2 - θ) - 0 : ℝ) = 1 - δ - 2 * θ := by ring
  rw [e1, e2, e3]
  have l0 := Real.rpow_nonneg hlam.le (1 - δ - 2 * θ)
  have k1 : productPolyConst B parabolicMomentConst (2 * (1 - δ / 2 - θ)) 1 ≤ K1 := le_abs_self _
  have k2 : productPolyConst B parabolicMomentConst (2 * (1 - δ / 2)) (1 + 2 * θ) ≤ K2 :=
    le_abs_self _
  have k3 : productPolyConst B parabolicMomentConst (2 * ((1 - δ) / 2 - θ)) 0 ≤ K3 :=
    le_abs_self _
  have hCm : 0 ≤ Cc * (max ε ε') ^ (2 * θ) / 2 := by positivity
  have s1 := mul_le_mul_of_nonneg_right k1 l0
  have s2 := mul_le_mul_of_nonneg_right k2 l0
  have s3 := mul_le_mul_of_nonneg_right k3 l0
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add s1 s2) s3) hCm
  calc _ ≤ _ := this
    _ = _ := by ring

end RegularityStructures.Phi43

end
