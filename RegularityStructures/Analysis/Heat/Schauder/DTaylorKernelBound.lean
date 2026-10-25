/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.DTaylorEstimate

/-!
# The derivative Taylor kernel bound

`exists_abs_pairing_dTaylorKernel_le`: the pairing of a distribution of local order `γ` with the
Taylor remainder of a derivative of the shell kernel.

Source: [Hai14, proof of Lemma 5.19].
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem exists_abs_pairing_dTaylorKernel_le {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (k : Fin 4 →₀ ℕ) {γ : ℝ} (σ : ℝ) {A : Finset ℝ}
    (hA : ∀ a ∈ A, -4 < a ∧ a ≤ γ) :
    ∃ (𝔈 : List (List (Fin 4))) (κ : List (Fin 4) → ℝ), (∀ ℓ, 0 ≤ κ ℓ) ∧
      (∀ ℓ ∈ 𝔈, σ ≤ (indexWeight ℓ : ℝ) ∧
        ((∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) ≠ σ) → σ < (indexWeight ℓ : ℝ))) ∧
      ∀ {Λ : ℝ → ParabolicSpace → ℝ} {C : ℝ} {x y : ParabolicSpace},
        Λ ∈ parabolicSemigroup.distributions → (∀ u, 0 < u → Measurable (Λ u)) → 0 ≤ C →
        parabolicSemigroup.IsLocalOrder Λ x γ A C → ∀ n : ℕ,
        parabolicNorm (y - x) ≤ (2 : ℝ)⁻¹ ^ n →
        |parabolicSemigroup.pairing Λ (dTaylorKernel h k n σ x y)| ≤
          C * (𝔈.map fun ℓ => κ ℓ * (parabolicNorm (y - x) ^ indexWeight ℓ *
            (2 : ℝ) ^ (((indexWeight ℓ : ℝ) + multiDeg k - γ - 2) * n))).sum := by
  have hh' : ContDiff ℝ ∞ (lineIter (multiDirs k) h) := contDiff_lineIter h0 _
  have hs' : ∀ z, 1 < parabolicNorm z → lineIter (multiDirs k) h z = 0 := fun z hz =>
    lineIter_eq_zero_of_lt hs _ hz
  obtain ⟨𝔈, κ, hκ, hdeg, hb⟩ := exists_abs_pairing_taylorKernel_le_sigma hh' hs' σ hA
  refine ⟨𝔈, κ, hκ, hdeg, fun {Λ C x y} hΛ hΛm hC hloc n hn => ?_⟩
  obtain ⟨T, B⟩ := hb hΛ hΛm hC hloc n hn
  have hN : (0 : ℝ) < ((2 : ℝ) ^ n) ^ multiDeg k := by positivity
  rw [dTaylorKernel_eq h0]
  have hT : Filter.Tendsto (fun s => ∫ w, Λ s w * (((2 : ℝ) ^ n) ^ multiDeg k *
      taylorKernel (lineIter (multiDirs k) h) n σ x y w)) (nhdsWithin 0 (Ioi 0))
      (nhds (((2 : ℝ) ^ n) ^ multiDeg k * parabolicSemigroup.pairing Λ
        (taylorKernel (lineIter (multiDirs k) h) n σ x y))) := by
    refine (T.const_mul (((2 : ℝ) ^ n) ^ multiDeg k)).congr fun s => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only; ring
  rw [parabolicSemigroup.pairing_eq_of_tendsto hT, abs_mul, abs_of_pos hN]
  refine (mul_le_mul_of_nonneg_left B hN.le).trans (le_of_eq ?_)
  rw [mul_left_comm, ← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun ℓ _ => ?_
  have : ((indexWeight ℓ : ℝ) + multiDeg k - γ - 2) * n =
      (multiDeg k : ℝ) * n + ((indexWeight ℓ : ℝ) - γ - 2) * n := by ring
  rw [this, Real.rpow_add (by norm_num), two_rpow_natCast_mul]
  ring

end RegularityStructures

end
