/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DTaylorLinear
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorKernelBound
public import RegularityStructures.Analysis.Heat.Schauder.TaylorSplit

/-!
# Limits of Taylor sums of the derivative shells

Integrability against compactly supported functions and the limits of the Taylor sums used for the
derivative kernels (`tendsto_integral_sub_sum_right`, `tendsto_integral_sub_sum_left`,
`tendsto_dShell_centre`).

Source: [Hai14, proof of Lemma 5.19].
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

theorem integrable_mul_of_hasCompactSupport {Λ : ℝ → ParabolicSpace → ℝ}
    {x₀ : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ}
    (hLD : parabolicSemigroup.LocalData Λ x₀ γ A C) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    {φ : ParabolicSpace → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable fun z => Λ s z * φ z := by
  have hbdd : BddAbove ((fun z => parabolicNorm (z - x₀)) '' tsupport φ) :=
    (hc.isCompact.image (continuous_parabolicNorm.comp (continuous_id.sub continuous_const))).bddAbove
  obtain ⟨R, hR⟩ := hbdd
  refine hLD.integrable_mul hs (lam := R) ⟨hφ.measurable, hφ.integrable_of_hasCompactSupport hc,
    fun z hz => ?_⟩
  by_contra hne
  have : z ∈ tsupport φ := subset_tsupport φ hne
  have := hR ⟨z, this, rfl⟩
  have hz' : R < parabolicNorm (z - x₀) := hz
  linarith

theorem tendsto_integral_sub_sum_right {Λ : ℝ → ParabolicSpace → ℝ} {ι : Type*} {F : Finset ι}
    {φ₀ : ParabolicSpace → ℝ} {φ : ι → ParabolicSpace → ℝ} (c : ι → ℝ) {p₀ : ℝ} {p : ι → ℝ}
    (h0 : Tendsto (fun s => ∫ w, Λ s w * φ₀ w) (nhdsWithin 0 (Ioi 0)) (nhds p₀))
    (h : ∀ i ∈ F, Tendsto (fun s => ∫ w, Λ s w * φ i w) (nhdsWithin 0 (Ioi 0)) (nhds (p i)))
    (i0 : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun w => Λ s w * φ₀ w)
    (ih : ∀ i ∈ F, ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun w => Λ s w * φ i w) :
    Tendsto (fun s => ∫ w, Λ s w * (φ₀ w - ∑ i ∈ F, c i * φ i w)) (nhdsWithin 0 (Ioi 0))
      (nhds (p₀ - ∑ i ∈ F, c i * p i)) := by
  refine (h0.sub (tendsto_finsetSum _ fun i hi => (h i hi).const_mul (c i))).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs'
  have hs2 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs'.1, hs'.2.le⟩
  have hI : ∀ i ∈ F, Integrable fun w => c i * (Λ s w * φ i w) := fun i hi =>
    (ih i hi s hs2).const_mul (c i)
  have e1 : (fun w => Λ s w * (φ₀ w - ∑ i ∈ F, c i * φ i w)) =
      fun w => Λ s w * φ₀ w - ∑ i ∈ F, c i * (Λ s w * φ i w) := by
    funext w; rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, integral_sub (i0 s hs2) (integrable_finsetSum _ hI), integral_finsetSum _ hI]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _ |>.symm

theorem tendsto_integral_sub_sum_left {Λ₀ : ℝ → ParabolicSpace → ℝ} {ι : Type*} {F : Finset ι}
    {Λ : ι → ℝ → ParabolicSpace → ℝ} (c : ι → ℝ) {φ : ParabolicSpace → ℝ} {p₀ : ℝ} {p : ι → ℝ}
    (h0 : Tendsto (fun s => ∫ w, Λ₀ s w * φ w) (nhdsWithin 0 (Ioi 0)) (nhds p₀))
    (h : ∀ i ∈ F, Tendsto (fun s => ∫ w, Λ i s w * φ w) (nhdsWithin 0 (Ioi 0)) (nhds (p i)))
    (i0 : ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun w => Λ₀ s w * φ w)
    (ih : ∀ i ∈ F, ∀ s ∈ Ioc (0 : ℝ) 1, Integrable fun w => Λ i s w * φ w) :
    Tendsto (fun s => ∫ w, (Λ₀ s w - ∑ i ∈ F, c i * Λ i s w) * φ w) (nhdsWithin 0 (Ioi 0))
      (nhds (p₀ - ∑ i ∈ F, c i * p i)) := by
  refine (h0.sub (tendsto_finsetSum _ fun i hi => (h i hi).const_mul (c i))).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with s hs'
  have hs2 : s ∈ Ioc (0 : ℝ) 1 := ⟨hs'.1, hs'.2.le⟩
  have hI : ∀ i ∈ F, Integrable fun w => c i * (Λ i s w * φ w) := fun i hi =>
    (ih i hi s hs2).const_mul (c i)
  have e1 : (fun w => (Λ₀ s w - ∑ i ∈ F, c i * Λ i s w) * φ w) =
      fun w => Λ₀ s w * φ w - ∑ i ∈ F, c i * (Λ i s w * φ w) := by
    funext w; rw [sub_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, integral_sub (i0 s hs2) (integrable_finsetSum _ hI), integral_finsetSum _ hI]
  congr 1
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _ |>.symm

theorem tendsto_dShell_centre {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : Λ ∈ parabolicSemigroup.distributions) (hΛm : ∀ u, 0 < u → Measurable (Λ u))
    {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (hs : ∀ z, 1 < parabolicNorm z → h z = 0)
    {x y : ParabolicSpace} {γ C : ℝ} {A : Finset ℝ} (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) (hC : 0 ≤ C)
    (hloc : parabolicSemigroup.IsLocalOrder Λ x γ A C) (k : Fin 4 →₀ ℕ) (n : ℕ) :
    Tendsto (fun s => ∫ z, Λ s z * lineIter (multiDirs k) (scaledShell h n) (y - z))
      (nhdsWithin 0 (Ioi 0))
      (nhds (parabolicSemigroup.pairing Λ
        (fun z => lineIter (multiDirs k) (scaledShell h n) (y - z)))) := by
  have hh' : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter h0 _
  have hs' : ∀ z, 1 < parabolicNorm z → lineIter (multiDirs k) h z = 0 := fun z hz =>
    lineIter_eq_zero_of_lt hs _ hz
  obtain ⟨T, -⟩ := tendsto_and_abs_pairing_scaledShell_centre_le hΛ hΛm hh' hs' hA hC hloc n
    (y := y)
  have hT : Tendsto (fun s => ∫ z, Λ s z * lineIter (multiDirs k) (scaledShell h n) (y - z))
      (nhdsWithin 0 (Ioi 0))
      (nhds (((2 : ℝ) ^ n) ^ multiDeg k * parabolicSemigroup.pairing Λ
        (fun z => scaledShell (lineIter (multiDirs k) h) n (y - z)))) := by
    refine (T.const_mul (((2 : ℝ) ^ n) ^ multiDeg k)).congr fun s => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [lineIter_multiDirs_scaledShell h0]
    ring
  convert hT using 2
  have e : (fun z => lineIter (multiDirs k) (scaledShell h n) (y - z)) =
      fun z => ((2 : ℝ) ^ n) ^ multiDeg k * scaledShell (lineIter (multiDirs k) h) n (y - z) := by
    funext z; rw [lineIter_multiDirs_scaledShell h0]
  rw [parabolicSemigroup.pairing_eq_of_tendsto hT]

end RegularityStructures

end
