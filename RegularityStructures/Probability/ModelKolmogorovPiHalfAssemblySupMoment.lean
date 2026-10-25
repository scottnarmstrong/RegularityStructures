/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyCells
public import Mathlib.Order.CompletePartialOrder

/-!
# Moment of the supremum over levels and cells

`lintegral_piHalfRandomSup_pow_le`: `E (piHalfRandomSup)^q ≤ 2 |ι| A (K C)^q` under the cell-count,
decay and `q κ ≥ 12` hypotheses.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem aemeasurable_piHalfRandomSup {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (𝒯 : RegularityStructure ι) (γ : ℝ) (Dπ : Set ι) (n : ℕ → ℕ)
    (R : ℕ → ι → ℕ → Ω → ℝ≥0∞) (hmeas : ∀ j i c, AEMeasurable (R j i c) P) :
    AEMeasurable (piHalfRandomSup 𝒯 γ Dπ n R) P := by
  classical
  unfold piHalfRandomSup
  refine AEMeasurable.iSup fun x => ?_
  by_cases h : x.2.1 ∉ Dπ ∧ 𝒯.deg x.2.1 < γ
  · simp only [h]; exact (hmeas _ _ _).mul_const _
  · simp only [h]; exact aemeasurable_const

theorem le_piHalfRandomSup {Ω : Type*} (𝒯 : RegularityStructure ι) (γ : ℝ) (Dπ : Set ι)
    (n : ℕ → ℕ) (R : ℕ → ι → ℕ → Ω → ℝ≥0∞) (ω : Ω) {j : ℕ} {i : ι} {c : ℕ}
    (hi : i ∉ Dπ) (hγ : 𝒯.deg i < γ) (hc : c < n j) :
    R j i c ω * ENNReal.ofReal (piHalfScale j ^ (-(𝒯.deg i / parabolicSemigroup.order))) ≤
      piHalfRandomSup 𝒯 γ Dπ n R ω := by
  classical
  unfold piHalfRandomSup
  refine le_trans (le_of_eq ?_) (le_iSup _ (⟨j, i, ⟨c, hc⟩⟩ : Σ j : ℕ, ι × Fin (n j)))
  simp [hi, hγ]

theorem lintegral_piHalfRandomSup_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (𝒯 : RegularityStructure ι) (γ κ : ℝ) (Dπ : Set ι) (n : ℕ → ℕ)
    (R : ℕ → ι → ℕ → Ω → ℝ≥0∞) (q : ℕ) (hq : q ≠ 0) {A K C : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hqκ : 12 ≤ (q : ℝ) * κ)
    (hn : ∀ j, (n j : ℝ) ≤ A * (2 : ℝ) ^ (5 * (j / 4)))
    (hmeas : ∀ j i c, AEMeasurable (R j i c) P)
    (hR : ∀ j i, i ∉ Dπ → 𝒯.deg i < γ → ∀ c < n j,
      ∫⁻ ω, R j i c ω ^ q ∂P ≤
        ENNReal.ofReal (K * C * piHalfScale j ^ ((𝒯.deg i + κ) / parabolicSemigroup.order)) ^ q) :
    ∫⁻ ω, piHalfRandomSup 𝒯 γ Dπ n R ω ^ q ∂P ≤
      ENNReal.ofReal (2 * (Fintype.card ι : ℝ) * A * (K * C) ^ q) := by
  classical
  have hord : parabolicSemigroup.order = 4 := rfl
  set f : (Σ j : ℕ, ι × Fin (n j)) → Ω → ℝ≥0∞ := fun x ω =>
    if x.2.1 ∉ Dπ ∧ 𝒯.deg x.2.1 < γ then
      R x.1 x.2.1 x.2.2 ω *
        ENNReal.ofReal (piHalfScale x.1 ^ (-(𝒯.deg x.2.1 / parabolicSemigroup.order)))
    else 0 with hf
  have hfm : ∀ x, AEMeasurable (f x) P := fun x => by
    by_cases h : x.2.1 ∉ Dπ ∧ 𝒯.deg x.2.1 < γ
    · simp only [hf, h]; exact (hmeas _ _ _).mul_const _
    · simp only [hf, h, ↓reduceIte]; exact aemeasurable_const
  have hsup : ∫⁻ ω, piHalfRandomSup 𝒯 γ Dπ n R ω ^ q ∂P ≤ ∑' x, ∫⁻ ω, f x ω ^ q ∂P :=
    lintegral_iSup_pow_le_tsum hfm hq
  set T : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal ((K * C) ^ q *
    piHalfScale j ^ (parabolicSemigroup.order⁻¹ * κ * q)) with hT
  have hterm : ∀ x, ∫⁻ ω, f x ω ^ q ∂P ≤ T x.1 := fun x => by
    by_cases h : x.2.1 ∉ Dπ ∧ 𝒯.deg x.2.1 < γ
    · simp only [hf, h]
      have := lintegral_rescaled_pow_le (P := P) (R := R x.1 x.2.1 x.2.2)
        (piHalfScale_pos x.1) hK hC q (e := 𝒯.deg x.2.1 / parabolicSemigroup.order)
        (κ' := κ / parabolicSemigroup.order) (by
          rw [← add_div]; exact hR x.1 x.2.1 h.1 h.2 x.2.2 x.2.2.2)
      refine this.trans (le_of_eq ?_)
      simp only [hT]
      congr 3
      rw [div_eq_inv_mul]
    · simp only [hf, h, ↓reduceIte]
      simp [hq]
  have hsum : ∑' x : (Σ j : ℕ, ι × Fin (n j)), T x.1 = ∑' j, ((Fintype.card ι : ℝ≥0∞) * n j) * T j := by
    rw [ENNReal.tsum_sigma']
    refine tsum_congr fun j => ?_
    rw [tsum_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; rfl
  have hcell : ∀ j, ((Fintype.card ι : ℝ≥0∞) * n j) * T j ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * A * (K * C) ^ q * (1 / 2 : ℝ) ^ j) := fun j => by
    have hx : (3 : ℝ) ≤ parabolicSemigroup.order⁻¹ * κ * q := by
      rw [hord]; linarith
    have h1 := cell_count_mul_scale_le j (n j) hA (hn j) hx
    simp only [hT]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : (Fintype.card ι : ℝ) * (n j : ℝ) * ((K * C) ^ q *
        piHalfScale j ^ (parabolicSemigroup.order⁻¹ * κ * q)) =
        (Fintype.card ι : ℝ) * (K * C) ^ q * ((n j : ℝ) *
        piHalfScale j ^ (parabolicSemigroup.order⁻¹ * κ * q)) := by ring
    rw [this]
    calc _ ≤ (Fintype.card ι : ℝ) * (K * C) ^ q * (A * (1 / 2 : ℝ) ^ j) := by gcongr
      _ = _ := by ring
  have hgeo : ∑' j : ℕ, ENNReal.ofReal ((Fintype.card ι : ℝ) * A * (K * C) ^ q * (1 / 2 : ℝ) ^ j) =
      ENNReal.ofReal (2 * (Fintype.card ι : ℝ) * A * (K * C) ^ q) := by
    have hnn : 0 ≤ (Fintype.card ι : ℝ) * A * (K * C) ^ q := by positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      ((summable_geometric_two).mul_left _), tsum_mul_left, tsum_geometric_two]
    congr 1; ring
  calc ∫⁻ ω, piHalfRandomSup 𝒯 γ Dπ n R ω ^ q ∂P ≤ ∑' x, ∫⁻ ω, f x ω ^ q ∂P := hsup
    _ ≤ ∑' x : (Σ j : ℕ, ι × Fin (n j)), T x.1 := ENNReal.tsum_le_tsum hterm
    _ = _ := hsum
    _ ≤ _ := ENNReal.tsum_le_tsum hcell
    _ = _ := hgeo

end RegularityStructures

end
