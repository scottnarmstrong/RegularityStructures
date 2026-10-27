module

public import GlobalPhi43.Attachment.TestPartition
public import RegularityStructures.Analysis.Parabolic.ScaledTest
import Mathlib.Tactic.Linarith

/-! Uniform support and C4 bounds for the recentered partition profiles. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures

open scoped ContDiff in
/-- Multiplying by a fixed cutoff and recentering at radius r <= 1 gives a unit-supported
profile with the uniform derivative allowance 16 A B. -/
theorem partition_profile_bounds {φ χ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    {A B : ℝ} (hA : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k φ z‖ ≤ A)
    (hB : ∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k χ z‖ ≤ B)
    {w : ParabolicSpace} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : tsupport χ ⊆ {z | parabolicNorm (z - w) < r}) :
    let p := fun z => φ (w + parabolicDilate r z) * χ (w + parabolicDilate r z)
    ContDiff ℝ ∞ p ∧ (∀ z, 1 < parabolicNorm z → p z = 0) ∧
      (∀ k ≤ 4, ∀ z, ‖iteratedFDeriv ℝ k p z‖ ≤ 16 * A * B) := by
  have hprod : ContDiff ℝ ∞ (φ * χ) := hφ.mul hχ
  have hmap : ContDiff ℝ ∞ (fun z : ParabolicSpace => w + parabolicDilate r z) :=
    contDiff_const.add (parabolicDilateCLM r).contDiff
  have hsm : ContDiff ℝ ∞ (fun z => φ (w + parabolicDilate r z) * χ (w + parabolicDilate r z)) :=
    (hφ.comp hmap).mul (hχ.comp hmap)
  refine ⟨hsm, ?_, ?_⟩
  · intro z hz
    have hzero : χ (w + parabolicDilate r z) = 0 := by
      by_contra hn
      have hmem : w + parabolicDilate r z ∈ tsupport χ := subset_closure hn
      have hsmall := hs hmem
      change parabolicNorm (w + parabolicDilate r z - w) < r at hsmall
      rw [add_sub_cancel_left, parabolicNorm_parabolicDilate hr.le] at hsmall
      nlinarith
    change φ (w + parabolicDilate r z) * χ (w + parabolicDilate r z) = 0
    rw [hzero, mul_zero]
  · intro k hk z
    have hprodB : ∀ j ≤ 4, ∀ y, ‖iteratedFDeriv ℝ j (φ * χ) y‖ ≤ 16 * A * B := by
      intro j hj y
      simpa only [show (2 : ℝ) ^ 4 = 16 by norm_num] using
        norm_iteratedFDeriv_mul_le_of_le hφ hχ hA hB hj y
    exact norm_iteratedFDeriv_comp_parabolicDilate_le hprod hprodB hr.le hr1 w hk z

end GlobalPhi43.Attachment
