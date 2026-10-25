/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.TreeI2Psi2DiagramLint
public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Convolution of two singular weights, as lower-integral bounds

For `p, q ∈ ℝ × T³` and exponents `0 < a, b < 5` with `a + b > 5`,
`∫ s(p - w)^(-a) s(q - w)^(-b) dw ≤ C s(p - q)^(5-a-b)`, in the form
`i2Psi2LintBound` (no integrability hypothesis is needed, and none is hidden:
the bound is on the lower integral).  This is [Hai14, Lemma 10.14, (10.10)] with `|s| = 5`;
we reprove it in lower-integral form because the chain of estimates for the tree `I(Ψ²) Ψ²`
needs to integrate the result once more.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Change of variables `w ↦ z - w` for lower-integral bounds. -/
theorem i2Psi2LintBound.comp_sub_left {f : SpaceTime → ℝ} {M : ℝ} (hf : Measurable f)
    (h : i2Psi2LintBound volume f M) (z : SpaceTime) :
    i2Psi2LintBound volume (fun w => f (z - w)) M := by
  unfold i2Psi2LintBound at *
  rw [(measurePreserving_sub_left_spaceTime z).lintegral_comp
    (f := fun w => ENNReal.ofReal (f w)) hf.ennreal_ofReal]
  exact h

theorem i2Psi2LintBound_singularLocalWeight {p a : ℝ} (hp : 0 < p) (hp5 : p < 5) (ha : 0 < a) :
    i2Psi2LintBound volume (singularLocalWeight p a) (80 / (5 - p) * a ^ (5 - p)) :=
  lintegral_singularLocalWeight_le hp hp5 ha

theorem i2Psi2LintBound_singularTailWeight {p e : ℝ} (hp : 5 < p) (he : 0 < e) :
    i2Psi2LintBound volume (singularTailWeight p e) (16 * p / (p - 5) * e ^ (5 - p)) :=
  lintegral_singularTailWeight_le hp he

private theorem split_aux {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
    {w w' : SpaceTime} (hw : 0 < torusParabolicSize w) (hw' : 0 < torusParabolicSize w')
    (hsum : 2 * δ ≤ torusParabolicSize w + torusParabolicSize w') :
    torusParabolicSize w' ^ (-a) * torusParabolicSize w ^ (-b) ≤
      δ ^ (-a) * singularLocalWeight b δ w + δ ^ (-b) * singularLocalWeight a δ w' +
        singularTailWeight (a + b) δ w + singularTailWeight (a + b) δ w' := by
  have n1 := singularLocalWeight_nonneg b δ w
  have n2 := singularLocalWeight_nonneg a δ w'
  have n3 := singularTailWeight_nonneg (a + b) δ w
  have n4 := singularTailWeight_nonneg (a + b) δ w'
  have hd1 : 0 ≤ δ ^ (-a) := Real.rpow_nonneg hδ.le _
  have hd2 : 0 ≤ δ ^ (-b) := Real.rpow_nonneg hδ.le _
  by_cases hx : torusParabolicSize w ≤ δ
  · have hy : δ ≤ torusParabolicSize w' := by linarith
    have hL : singularLocalWeight b δ w = torusParabolicSize w ^ (-b) := by
      simp [singularLocalWeight, hw, hx]
    have h1 : torusParabolicSize w' ^ (-a) ≤ δ ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hδ hy (neg_nonpos.2 ha)
    calc
      _ ≤ δ ^ (-a) * torusParabolicSize w ^ (-b) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hw.le _)
      _ = δ ^ (-a) * singularLocalWeight b δ w := by rw [hL]
      _ ≤ _ := by
        have := mul_nonneg hd2 n2
        linarith
  · by_cases hy : torusParabolicSize w' ≤ δ
    · have hx' : δ ≤ torusParabolicSize w := by linarith
      have hL : singularLocalWeight a δ w' = torusParabolicSize w' ^ (-a) := by
        simp [singularLocalWeight, hw', hy]
      have h1 : torusParabolicSize w ^ (-b) ≤ δ ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hδ hx' (neg_nonpos.2 hb)
      calc
        _ ≤ torusParabolicSize w' ^ (-a) * δ ^ (-b) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hw'.le _)
        _ = δ ^ (-b) * singularLocalWeight a δ w' := by rw [hL]; ring
        _ ≤ _ := by
          have := mul_nonneg hd1 n1
          linarith
    · have hTx : singularTailWeight (a + b) δ w = torusParabolicSize w ^ (-(a + b)) := by
        simp [singularTailWeight, lt_of_not_ge hx]
      have hTy : singularTailWeight (a + b) δ w' = torusParabolicSize w' ^ (-(a + b)) := by
        simp [singularTailWeight, lt_of_not_ge hy]
      have h := torusParabolicSize_rpow_neg_mul_le ha hb hw' hw
      rw [← hTx, ← hTy] at h
      have := mul_nonneg hd1 n1
      have := mul_nonneg hd2 n2
      linarith

/-- **Convolution of two singular weights** [Hai14, Lemma 10.14, (10.10)], `a + b > 5`:
`∫ s(p - w)^(-a) s(q - w)^(-b) dw ≤ C s(p - q)^(5-a-b)`. -/
theorem i2Psi2LintBound_rpow_mul_rpow_of_gt {a b : ℝ} (ha : 0 < a) (ha5 : a < 5) (hb : 0 < b)
    (hb5 : b < 5) (hab : 5 < a + b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : SpaceTime, 0 < torusParabolicSize (p - q) →
      i2Psi2LintBound volume (fun w => torusParabolicSize (p - w) ^ (-a) *
        torusParabolicSize (q - w) ^ (-b)) (C * torusParabolicSize (p - q) ^ (5 - a - b)) := by
  have hpa : 0 < a + b := by linarith
  have hab0 : 0 < a + b - 5 := by linarith
  have h5a : 0 < 5 - a := by linarith
  have h5b : 0 < 5 - b := by linarith
  have hK : 0 ≤ 80 / (5 - b) + 80 / (5 - a) + 2 * (16 * (a + b) / (a + b - 5)) := by
    have h1 : 0 ≤ 80 / (5 - b) := div_nonneg (by norm_num) h5b.le
    have h2 : 0 ≤ 80 / (5 - a) := div_nonneg (by norm_num) h5a.le
    have h3 : 0 ≤ 16 * (a + b) / (a + b - 5) := div_nonneg (by linarith) hab0.le
    linarith
  refine ⟨(80 / (5 - b) + 80 / (5 - a) + 2 * (16 * (a + b) / (a + b - 5))) /
    (16 : ℝ) ^ (5 - (a + b)), div_nonneg hK (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro p q hpq
  set r := torusParabolicSize (p - q) with hr
  have hδ : 0 < r / 16 := by linarith
  set δ := r / 16 with hδdef
  have hd1 : 0 ≤ δ ^ (-a) := Real.rpow_nonneg hδ.le _
  have hd2 : 0 ≤ δ ^ (-b) := Real.rpow_nonneg hδ.le _
  have mLb := (measurable_singularLocalWeight b δ).comp
    (measurable_const.sub measurable_id : Measurable fun w : SpaceTime => q - w)
  have mLa := (measurable_singularLocalWeight a δ).comp
    (measurable_const.sub measurable_id : Measurable fun w : SpaceTime => p - w)
  have mTb := (measurable_singularTailWeight (a + b) δ).comp
    (measurable_const.sub measurable_id : Measurable fun w : SpaceTime => q - w)
  have mTa := (measurable_singularTailWeight (a + b) δ).comp
    (measurable_const.sub measurable_id : Measurable fun w : SpaceTime => p - w)
  have bLb := (i2Psi2LintBound_singularLocalWeight hb hb5 hδ).comp_sub_left
    (measurable_singularLocalWeight b δ) q
  have bLa := (i2Psi2LintBound_singularLocalWeight ha ha5 hδ).comp_sub_left
    (measurable_singularLocalWeight a δ) p
  have bTb := (i2Psi2LintBound_singularTailWeight hab hδ).comp_sub_left
    (measurable_singularTailWeight (a + b) δ) q
  have bTa := (i2Psi2LintBound_singularTailWeight hab hδ).comp_sub_left
    (measurable_singularTailWeight (a + b) δ) p
  have c1 := bLb.const_mul hd1
  have c2 := bLa.const_mul hd2
  have nLb : ∀ w, 0 ≤ singularLocalWeight b δ (q - w) := fun w =>
    singularLocalWeight_nonneg _ _ _
  have nLa : ∀ w, 0 ≤ singularLocalWeight a δ (p - w) := fun w =>
    singularLocalWeight_nonneg _ _ _
  have nTb : ∀ w, 0 ≤ singularTailWeight (a + b) δ (q - w) := fun w =>
    singularTailWeight_nonneg _ _ _
  have nTa : ∀ w, 0 ≤ singularTailWeight (a + b) δ (p - w) := fun w =>
    singularTailWeight_nonneg _ _ _
  have hMb : 0 ≤ δ ^ (-a) * (80 / (5 - b) * δ ^ (5 - b)) :=
    mul_nonneg hd1 (mul_nonneg (div_nonneg (by norm_num) h5b.le) (Real.rpow_nonneg hδ.le _))
  have hMa : 0 ≤ δ ^ (-b) * (80 / (5 - a) * δ ^ (5 - a)) :=
    mul_nonneg hd2 (mul_nonneg (div_nonneg (by norm_num) h5a.le) (Real.rpow_nonneg hδ.le _))
  have hMT : 0 ≤ 16 * (a + b) / (a + b - 5) * δ ^ (5 - (a + b)) :=
    mul_nonneg (div_nonneg (by linarith) hab0.le) (Real.rpow_nonneg hδ.le _)
  have s1 := c1.add (g := fun w => δ ^ (-b) * singularLocalWeight a δ (p - w))
    (mLb.const_mul _).aemeasurable (fun w => mul_nonneg hd1 (nLb w))
    (fun w => mul_nonneg hd2 (nLa w)) hMb hMa c2
  have mA : Measurable fun w : SpaceTime => δ ^ (-a) * singularLocalWeight b δ (q - w) +
      δ ^ (-b) * singularLocalWeight a δ (p - w) :=
    (mLb.const_mul _).add (mLa.const_mul _)
  have s2 := s1.add (g := fun w => singularTailWeight (a + b) δ (q - w)) mA.aemeasurable
    (fun w => add_nonneg (mul_nonneg hd1 (nLb w)) (mul_nonneg hd2 (nLa w))) nTb
    (add_nonneg hMb hMa) hMT bTb
  have mB : Measurable fun w : SpaceTime => δ ^ (-a) * singularLocalWeight b δ (q - w) +
      δ ^ (-b) * singularLocalWeight a δ (p - w) + singularTailWeight (a + b) δ (q - w) :=
    mA.add mTb
  have s3 := s2.add (g := fun w => singularTailWeight (a + b) δ (p - w)) mB.aemeasurable
    (fun w => add_nonneg (add_nonneg (mul_nonneg hd1 (nLb w)) (mul_nonneg hd2 (nLa w))) (nTb w))
    nTa (add_nonneg (add_nonneg hMb hMa) hMT) hMT bTa
  refine s3.mono_ae ?_ ?_
  · filter_upwards [ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos q]
      with w hp' hq'
    have htri := torusParabolicSize_sub_le_eight_mul (p - w) (q - w)
    have e : p - w - (q - w) = p - q := by abel
    rw [e] at htri
    exact split_aux (a := a) (b := b) ha.le hb.le hδ hq' hp' (by rw [hδdef]; linarith)
  · have e1 : δ ^ (-a) * δ ^ (5 - b) = δ ^ (5 - (a + b)) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    have e2 : δ ^ (-b) * δ ^ (5 - a) = δ ^ (5 - (a + b)) := by
      rw [← Real.rpow_add hδ]; congr 1; ring
    have hX : δ ^ (5 - (a + b)) = r ^ (5 - a - b) / (16 : ℝ) ^ (5 - (a + b)) := by
      rw [hδdef, Real.div_rpow hpq.le (by norm_num)]
      congr 2; ring
    refine le_of_eq ?_
    calc _ = 80 / (5 - b) * (δ ^ (-a) * δ ^ (5 - b)) + 80 / (5 - a) * (δ ^ (-b) * δ ^ (5 - a)) +
          2 * (16 * (a + b) / (a + b - 5)) * δ ^ (5 - (a + b)) := by ring
      _ = (80 / (5 - b) + 80 / (5 - a) + 2 * (16 * (a + b) / (a + b - 5))) *
          δ ^ (5 - (a + b)) := by rw [e1, e2]; ring
      _ = _ := by rw [hX]; ring

end RegularityStructures

end
