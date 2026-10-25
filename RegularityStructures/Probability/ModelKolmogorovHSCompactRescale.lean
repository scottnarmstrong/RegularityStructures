/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.TestFunction
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Normalizing a compact parabolic index set

Hairer--Steele, arXiv:2301.10081v3, Proposition B.3. A compact set lies
in a bounded product ball. A translated parabolic dilation sends it into
the unit box. Both directions of the exact distance scaling are recorded
so that stochastic increment assumptions transfer only along the image
of the original set, without enlargement.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- Center of the unit space-time box. -/
def hsParabolicBoxCenter : ParabolicSpace := (1 / 2, fun _ => 1 / 2)

/-- Normalize parabolic lengths by `L` and translate to the unit-box center. -/
def hsParabolicBoxHomeomorph {L : ℝ} (hL : L ≠ 0) : ParabolicSpace ≃ₜ ParabolicSpace where
  toFun x := hsParabolicBoxCenter + parabolicDilate L⁻¹ x
  invFun y := parabolicDilate L (y - hsParabolicBoxCenter)
  left_inv x := by
    change parabolicDilate L ((hsParabolicBoxCenter + parabolicDilate L⁻¹ x) - hsParabolicBoxCenter) = x
    rw [add_sub_cancel_left, parabolicDilate_parabolicDilate_inv hL]
  right_inv y := by
    change hsParabolicBoxCenter + parabolicDilate L⁻¹ (parabolicDilate L (y - hsParabolicBoxCenter)) = y
    rw [parabolicDilate_inv_parabolicDilate hL, add_sub_cancel]
  continuous_toFun := by
    have h : Continuous (parabolicDilate L⁻¹) := by
      rw [show parabolicDilate L⁻¹ = (parabolicDilateCLM L⁻¹ : ParabolicSpace → ParabolicSpace) from
        funext fun x => (parabolicDilateCLM_apply L⁻¹ x).symm]
      exact (parabolicDilateCLM L⁻¹).continuous
    exact continuous_const.add h
  continuous_invFun := by
    have h : Continuous (parabolicDilate L) := by
      rw [show parabolicDilate L = (parabolicDilateCLM L : ParabolicSpace → ParabolicSpace) from
        funext fun x => (parabolicDilateCLM_apply L x).symm]
      exact (parabolicDilateCLM L).continuous
    exact h.comp (continuous_id.sub continuous_const)

end RegularityStructures

end

public section

namespace RegularityStructures

private theorem hs_affine_interval {a d R : ℝ} (hd : 0 < d) (ha : |a| ≤ R)
    (hR : 2 * R ≤ d) : 1 / 2 + a / d ∈ Set.Icc (0 : ℝ) 1 := by
  have h : |a / d| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hd]
    exact (div_le_iff₀ hd).2 (by linarith)
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- A sufficiently large parabolic normalization sends a bounded product ball into the unit box. -/
theorem hsParabolicBoxHomeomorph_mem_unitBox {L : ℝ} (hL : 2 ≤ L)
    {x : ParabolicSpace} (hx : ‖x‖ ≤ L / 2) :
    ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)) x).1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ j, ((hsParabolicBoxHomeomorph (by linarith : L ≠ 0)) x).2 j ∈ Set.Icc (0 : ℝ) 1 := by
  have hL0 : 0 < L := by linarith
  have ht : |x.1| ≤ L / 2 := (le_max_left ‖x.1‖ ‖x.2‖).trans hx
  have hs (j : Fin 3) : |x.2 j| ≤ L / 2 :=
    (norm_le_pi_norm x.2 j).trans ((le_max_right ‖x.1‖ ‖x.2‖).trans hx)
  change 1 / 2 + (L⁻¹) ^ 2 * x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ j, 1 / 2 + L⁻¹ * x.2 j ∈ Set.Icc (0 : ℝ) 1
  constructor
  · have hsq : 2 * (L / 2) ≤ L ^ 2 := by nlinarith
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
      hs_affine_interval (sq_pos_of_pos hL0) ht hsq
  · intro j
    simpa only [div_eq_mul_inv, mul_comm] using
      hs_affine_interval hL0 (hs j) (by linarith : 2 * (L / 2) ≤ L)

/-- Exact parabolic distance scaling for the normalization. -/
theorem parabolicNorm_sub_hsParabolicBoxHomeomorph {L : ℝ} (hL : 0 < L)
    (x y : ParabolicSpace) :
    parabolicNorm (hsParabolicBoxHomeomorph hL.ne' x - hsParabolicBoxHomeomorph hL.ne' y) =
      L⁻¹ * parabolicNorm (x - y) := by
  have he : hsParabolicBoxHomeomorph hL.ne' x - hsParabolicBoxHomeomorph hL.ne' y =
      parabolicDilate L⁻¹ (x - y) := by
    change (hsParabolicBoxCenter + parabolicDilate L⁻¹ x) -
      (hsParabolicBoxCenter + parabolicDilate L⁻¹ y) = _
    rw [parabolicDilate_sub]
    abel
  rw [he, parabolicNorm_parabolicDilate (inv_nonneg.2 hL.le)]

/-- Exact parabolic distance scaling for the inverse normalization. -/
theorem parabolicNorm_sub_hsParabolicBoxHomeomorph_symm {L : ℝ} (hL : 0 < L)
    (x y : ParabolicSpace) :
    parabolicNorm ((hsParabolicBoxHomeomorph hL.ne').symm x -
      (hsParabolicBoxHomeomorph hL.ne').symm y) = L * parabolicNorm (x - y) := by
  have he : (hsParabolicBoxHomeomorph hL.ne').symm x -
      (hsParabolicBoxHomeomorph hL.ne').symm y = parabolicDilate L (x - y) := by
    change parabolicDilate L (x - hsParabolicBoxCenter) -
      parabolicDilate L (y - hsParabolicBoxCenter) = _
    rw [← parabolicDilate_sub]
    congr 1
    abel
  rw [he, parabolicNorm_parabolicDilate hL.le]

end RegularityStructures

end
