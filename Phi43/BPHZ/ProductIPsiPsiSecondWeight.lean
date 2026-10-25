/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondDouble
import Mathlib.Tactic

/-!
# Weights and null sets for the second moment of `I(Ψ)Ψ`

* `ipsi_rpow_le_weight`, `ipsi_weightW_le`: `r^a ≤ lam^a (1 + r/lam)²` and
  `r^γ (1 + r) ≤ lam^γ (1 + r/lam)²` for `lam ∈ (0, 1]`;
* `ipsi_ae_time_ne`: for almost every `(y, y') ∈ ℝ⁴ × ℝ⁴` the times `y₀, y'₀, x₀` are distinct;
* positivity of the sizes in terms of times.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ipsi_rpow_le_weight {l r a : ℝ} (hl : 0 < l) (hr : 0 ≤ r) (ha0 : 0 ≤ a)
    (ha2 : a ≤ 2) : r ^ a ≤ l ^ a * (1 + r / l) ^ 2 := by
  set u := r / l with hu
  have hu0 : 0 ≤ u := div_nonneg hr hl.le
  have hru : r = l * u := by rw [hu]; field_simp
  have h1 : r ^ a = l ^ a * u ^ a := by rw [hru, Real.mul_rpow hl.le hu0]
  have h2 : u ^ a ≤ (1 + u) ^ a := Real.rpow_le_rpow hu0 (by linarith) ha0
  have h3 : (1 + u) ^ a ≤ (1 + u) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) ha2
  have h4 : (1 + u) ^ (2 : ℝ) = (1 + u) ^ 2 := by
    rw [← Real.rpow_natCast]; norm_num
  rw [h1]
  exact mul_le_mul_of_nonneg_left (h2.trans (h3.trans (le_of_eq h4))) (Real.rpow_nonneg hl.le _)

theorem ipsi_weightW_le {l r γ : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) (hr : 0 ≤ r) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) : r ^ γ * (1 + r) ≤ l ^ γ * (1 + r / l) ^ 2 := by
  set u := r / l with hu
  have hu0 : 0 ≤ u := div_nonneg hr hl.le
  have hru : r = l * u := by rw [hu]; field_simp
  have h1 : r ^ γ = l ^ γ * u ^ γ := by rw [hru, Real.mul_rpow hl.le hu0]
  have h2 : u ^ γ ≤ (1 + u) ^ γ := Real.rpow_le_rpow hu0 (by linarith) hγ0
  have h3 : (1 + u) ^ γ ≤ (1 + u) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hγ1
  rw [Real.rpow_one] at h3
  have h5 : 1 + r ≤ 1 + u := by
    have : r ≤ u := by
      rw [hu, le_div_iff₀ hl]; nlinarith
    linarith
  have h6 : r ^ γ ≤ l ^ γ * (1 + u) := by
    rw [h1]; exact mul_le_mul_of_nonneg_left (h2.trans h3) (Real.rpow_nonneg hl.le _)
  calc r ^ γ * (1 + r) ≤ (l ^ γ * (1 + u)) * (1 + u) :=
        mul_le_mul h6 h5 (by linarith) (by have := Real.rpow_nonneg hl.le γ; positivity)
    _ = _ := by ring

theorem ipsi_ae_ne_time (c : ℝ) : ∀ᵐ y : ParabolicSpace ∂volume, y.1 ≠ c := by
  rw [Measure.volume_eq_prod]
  have hm : MeasurableSet {y : ParabolicSpace | y.1 ≠ c} :=
    (measurableSet_singleton c).compl.preimage measurable_fst
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 3 → ℝ))) (s := {y : ParabolicSpace | y.1 ≠ c}) hm).2 ?_
  have h : ∀ᵐ s : ℝ ∂volume, s ≠ c := by
    have := (Set.countable_singleton c).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with s hs
    simpa using hs
  filter_upwards [h] with s hs
  exact Filter.Eventually.of_forall fun z => hs

theorem ipsi_ae_time_ne (x : ParabolicSpace) :
    ∀ᵐ q : ParabolicSpace × ParabolicSpace ∂volume,
      q.1.1 ≠ x.1 ∧ q.2.1 ≠ x.1 ∧ q.1.1 ≠ q.2.1 := by
  have hm : MeasurableSet {q : ParabolicSpace × ParabolicSpace |
      q.1.1 ≠ x.1 ∧ q.2.1 ≠ x.1 ∧ q.1.1 ≠ q.2.1} := by
    refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
    · exact (measurableSet_singleton x.1).compl.preimage (measurable_fst.comp measurable_fst)
    · exact (measurableSet_singleton x.1).compl.preimage (measurable_fst.comp measurable_snd)
    · exact (measurableSet_eq_fun (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd)).compl
  rw [Measure.volume_eq_prod]
  refine (Measure.ae_prod_mem_iff_ae_ae_mem (μ := (volume : Measure ParabolicSpace))
    (ν := (volume : Measure ParabolicSpace)) hm).2 ?_
  filter_upwards [ipsi_ae_ne_time x.1] with y hy
  filter_upwards [ipsi_ae_ne_time x.1, ipsi_ae_ne_time y.1] with y' hy' hyy
  exact ⟨hy, hy', fun h => hyy h.symm⟩

theorem torusParabolicSize_pos_of_time_ne {z : SpaceTime} (h : z.1 ≠ 0) :
    0 < torusParabolicSize z := by
  unfold torusParabolicSize
  have : 0 < √|z.1| := Real.sqrt_pos.2 (abs_pos.2 h)
  linarith [torusSpatialNorm_nonneg z.2]

theorem parabolicNorm_pos_of_time_ne {z : ParabolicSpace} (h : z.1 ≠ 0) : 0 < parabolicNorm z := by
  unfold parabolicNorm
  have : 0 < √|z.1| := Real.sqrt_pos.2 (abs_pos.2 h)
  have : 0 ≤ ∑ i, |z.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  linarith

end RegularityStructures.Phi43

end
