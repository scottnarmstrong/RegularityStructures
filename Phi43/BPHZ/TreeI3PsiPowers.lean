/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Integrals of products of two centred parabolic powers

For a centre `c` and exponent `a`, `singularPow a c w = s(c - w)^(-a)`.  If `0 < a, b < 5` and
`a + b > 5`, the product `singularPow a p * singularPow b q` is integrable and its integral is
at most `C * s(p - q)^(5 - a - b)` (the whole-space convolution estimate of [Hai14, Lemma 10.14],
in the form with two arbitrary centres, together with integrability of the integrand).

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.37a).
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

/-- The parabolic power weight `s(c - w)^(-a)` centred at `c`. -/
def singularPow (a : ℝ) (c w : SpaceTime) : ℝ := torusParabolicSize (c - w) ^ (-a)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem singularPow_nonneg (a : ℝ) (c w : SpaceTime) : 0 ≤ singularPow a c w :=
  Real.rpow_nonneg (torusParabolicSize_nonneg _) _

theorem measurable_singularPow (a : ℝ) (c : SpaceTime) : Measurable (singularPow a c) :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _

/-- [Hai14, (10.37a)] for centred powers. -/
theorem singularPow_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {p q w : SpaceTime}
    (hp : 0 < torusParabolicSize (p - w)) (hq : 0 < torusParabolicSize (q - w)) :
    singularPow a p w * singularPow b q w ≤
      singularPow (a + b) p w + singularPow (a + b) q w :=
  torusParabolicSize_rpow_neg_mul_le ha hb hp hq

private theorem pointwise_split {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
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
      have h := torusParabolicSize_rpow_neg_mul_le (a := b) (b := a) hb ha hw hw'
      rw [mul_comm] at h
      have h2 : -(b + a) = -(a + b) := by ring
      rw [h2] at h
      rw [← hTx, ← hTy] at h
      have := mul_nonneg hd1 n1
      have := mul_nonneg hd2 n2
      linarith

/-- Quasi-triangle inequality for two centres. -/
theorem torusParabolicSize_sub_le_eight_mul_centres (p q w : SpaceTime) :
    torusParabolicSize (p - q) ≤
      8 * (torusParabolicSize (p - w) + torusParabolicSize (q - w)) := by
  have h1 := torusParabolicSize_sub_le (p - q) (p - w)
  have h2 := torusParabolicSize_neg_le_two_mul (q - w)
  have h3 : p - q - (p - w) = -(q - w) := by abel
  rw [h3] at h1
  have := torusParabolicSize_nonneg (p - w)
  have := torusParabolicSize_nonneg (q - w)
  linarith

/-- The convolution of two centred singular powers of total order `> 5` is integrable and of
order `s(p - q)^(5 - a - b)`. -/
theorem integrable_and_integral_singularPow_mul_le {a b : ℝ} (ha : 0 < a) (ha5 : a < 5)
    (hb : 0 < b) (hb5 : b < 5) (hab : 5 < a + b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : SpaceTime, 0 < torusParabolicSize (p - q) →
      Integrable (fun w => singularPow a p w * singularPow b q w) ∧
        ∫ w, singularPow a p w * singularPow b q w ≤
          C * torusParabolicSize (p - q) ^ (5 - a - b) := by
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
  have iLb := integrable_singularLocalWeight hb hb5 hδ
  have iLa := integrable_singularLocalWeight ha ha5 hδ
  have iT := integrable_singularTailWeight (p := a + b) hab hδ
  have iLb' := integrable_comp_sub_left_spaceTime iLb q
  have iLa' := integrable_comp_sub_left_spaceTime iLa p
  have iT' := integrable_comp_sub_left_spaceTime iT p
  have iT'' := integrable_comp_sub_left_spaceTime iT q
  let H : SpaceTime → ℝ := fun w => δ ^ (-a) * singularLocalWeight b δ (q - w) +
    δ ^ (-b) * singularLocalWeight a δ (p - w) + singularTailWeight (a + b) δ (q - w) +
      singularTailWeight (a + b) δ (p - w)
  have hA : Integrable (fun w => δ ^ (-a) * singularLocalWeight b δ (q - w)) :=
    iLb'.const_mul _
  have hB : Integrable (fun w => δ ^ (-b) * singularLocalWeight a δ (p - w)) :=
    iLa'.const_mul _
  have hAB : Integrable (fun w => δ ^ (-a) * singularLocalWeight b δ (q - w) +
      δ ^ (-b) * singularLocalWeight a δ (p - w)) := hA.add hB
  have hABC : Integrable (fun w => δ ^ (-a) * singularLocalWeight b δ (q - w) +
      δ ^ (-b) * singularLocalWeight a δ (p - w) + singularTailWeight (a + b) δ (q - w)) :=
    hAB.add iT''
  have hH : Integrable H := hABC.add iT'
  have hle : ∀ᵐ w : SpaceTime ∂volume, singularPow a p w * singularPow b q w ≤ H w := by
    filter_upwards [ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos q]
      with w hw hw'
    have htri := torusParabolicSize_sub_le_eight_mul_centres p q w
    exact pointwise_split (a := a) (b := b) ha.le hb.le hδ hw' hw (by rw [hδdef]; linarith)
  have hnn : ∀ w, 0 ≤ singularPow a p w * singularPow b q w := fun w =>
    mul_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)
  have hmeas : Measurable (fun w => singularPow a p w * singularPow b q w) :=
    (measurable_singularPow a p).mul (measurable_singularPow b q)
  refine ⟨Integrable.mono' hH hmeas.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]
    exact hw
  have hI : ∫ w, H w = (δ ^ (-a) * ∫ w, singularLocalWeight b δ w) +
      (δ ^ (-b) * ∫ w, singularLocalWeight a δ w) + (∫ w, singularTailWeight (a + b) δ w) +
        ∫ w, singularTailWeight (a + b) δ w := by
    simp only [H]
    rw [integral_add hABC iT', integral_add hAB iT'', integral_add hA hB,
      integral_const_mul, integral_const_mul,
      integral_comp_sub_left_spaceTime (singularLocalWeight b δ) q,
      integral_comp_sub_left_spaceTime (singularLocalWeight a δ) p,
      integral_comp_sub_left_spaceTime (singularTailWeight (a + b) δ) q,
      integral_comp_sub_left_spaceTime (singularTailWeight (a + b) δ) p]
  have hd1 : 0 ≤ δ ^ (-a) := Real.rpow_nonneg hδ.le _
  have hd2 : 0 ≤ δ ^ (-b) := Real.rpow_nonneg hδ.le _
  have e1 : δ ^ (-a) * δ ^ (5 - b) = δ ^ (5 - (a + b)) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have e2 : δ ^ (-b) * δ ^ (5 - a) = δ ^ (5 - (a + b)) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have bLb := integral_singularLocalWeight_le hb hb5 hδ
  have bLa := integral_singularLocalWeight_le ha ha5 hδ
  have bT := integral_singularTailWeight_le hab hδ
  have hX : δ ^ (5 - (a + b)) = r ^ (5 - a - b) / (16 : ℝ) ^ (5 - (a + b)) := by
    rw [hδdef, Real.div_rpow hpq.le (by norm_num)]
    congr 2; ring
  calc
    ∫ w, singularPow a p w * singularPow b q w ≤ ∫ w, H w :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hH hle
    _ = _ := hI
    _ ≤ δ ^ (-a) * (80 / (5 - b) * δ ^ (5 - b)) +
          δ ^ (-b) * (80 / (5 - a) * δ ^ (5 - a)) +
          16 * (a + b) / (a + b - 5) * δ ^ (5 - (a + b)) +
          16 * (a + b) / (a + b - 5) * δ ^ (5 - (a + b)) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left bLb hd1)
        (mul_le_mul_of_nonneg_left bLa hd2)) bT) bT
    _ = (80 / (5 - b) + 80 / (5 - a) + 2 * (16 * (a + b) / (a + b - 5))) *
          δ ^ (5 - (a + b)) := by
      have e3 : δ ^ (-a) * (80 / (5 - b) * δ ^ (5 - b)) +
          δ ^ (-b) * (80 / (5 - a) * δ ^ (5 - a)) =
          80 / (5 - b) * (δ ^ (-a) * δ ^ (5 - b)) +
            80 / (5 - a) * (δ ^ (-b) * δ ^ (5 - a)) := by ring
      rw [e3, e1, e2]; ring
    _ = _ := by
      rw [hX]
      ring

end RegularityStructures

end
