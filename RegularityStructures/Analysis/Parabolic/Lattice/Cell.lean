/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Lattice.Bump
public import RegularityStructures.Analysis.Parabolic.TestFunction

/-!
# Causal lattice cells on parabolic space

`latticePoint n k = S^{2^{-n}} k` is the `k`-th point of the parabolic lattice at scale `2^{-n}`, and
`latticeCell n k` is the rescaled bump `latticeBump4 (S^{2^n} · - k)`. Its support lies in the
causal box `latticePoint n k + (0, 2·2^{-n}]^4`-type region (`latticeCell_ne_zero`), and has
parabolic radius at most `8 · 2^{-n}` around `latticePoint n k`
(`parabolicNorm_sub_latticePoint_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The lattice point `S^{2^{-n}} k` at scale `2^{-n}`. -/
def latticePoint (n : ℕ) (k : LatticeIndex) : ParabolicSpace :=
  parabolicDilate ((2 : ℝ) ^ n)⁻¹ (latticeCoe k)

/-- The lattice cell `w ↦ latticeBump4 (S^{2^n} w - k)`. -/
def latticeCell (n : ℕ) (k : LatticeIndex) (w : ParabolicSpace) : ℝ :=
  latticeBump4 (parabolicDilate ((2 : ℝ) ^ n) w - latticeCoe k)

end RegularityStructures

end

public section

namespace RegularityStructures

@[simp]
theorem latticePoint_fst (n : ℕ) (k : LatticeIndex) :
    (latticePoint n k).1 = (((2 : ℝ) ^ n)⁻¹) ^ 2 * k.1 := by
  simp [latticePoint, parabolicDilate, latticeCoe]

@[simp]
theorem latticePoint_snd (n : ℕ) (k : LatticeIndex) (i : Fin 3) :
    (latticePoint n k).2 i = ((2 : ℝ) ^ n)⁻¹ * k.2 i := by
  simp [latticePoint, parabolicDilate, latticeCoe]

private theorem parabolicDilate_add_aux (c : ℝ) (z w : ParabolicSpace) :
    parabolicDilate c (z + w) = parabolicDilate c z + parabolicDilate c w := by
  ext <;> simp [parabolicDilate, mul_add]

private theorem two_pow_ne_zero (n : ℕ) : ((2 : ℝ) ^ n) ≠ 0 := by positivity

open scoped ContDiff in
theorem contDiff_latticeCell (n : ℕ) (k : LatticeIndex) : ContDiff ℝ ∞ (latticeCell n k) := by
  have h : ContDiff ℝ ∞ fun w : ParabolicSpace =>
      parabolicDilateCLM ((2 : ℝ) ^ n) w - latticeCoe k :=
    (parabolicDilateCLM ((2 : ℝ) ^ n)).contDiff.sub contDiff_const
  have := contDiff_latticeBump4.comp h
  have e : latticeCell n k = latticeBump4 ∘ fun w : ParabolicSpace =>
      parabolicDilateCLM ((2 : ℝ) ^ n) w - latticeCoe k := by
    funext w
    simp only [latticeCell, Function.comp_apply, parabolicDilateCLM_apply]
  rw [e]
  exact this

theorem latticeCell_nonneg (n : ℕ) (k : LatticeIndex) (w : ParabolicSpace) :
    0 ≤ latticeCell n k w :=
  latticeBump4_nonneg _

theorem latticeCell_add_parabolicDilate (m : ℕ) (l : LatticeIndex) (a : ParabolicSpace) (c : ℝ)
    (v : ParabolicSpace) :
    latticeCell m l (a + parabolicDilate c v) =
      latticeBump4 (parabolicDilate ((2 : ℝ) ^ m * c) v +
        (parabolicDilate ((2 : ℝ) ^ m) a - latticeCoe l)) := by
  unfold latticeCell
  rw [parabolicDilate_add_aux, parabolicDilate_mul]
  congr 1
  abel

theorem latticeCell_latticePoint_add (n : ℕ) (k : LatticeIndex) (v : ParabolicSpace) :
    latticeCell n k (latticePoint n k + parabolicDilate ((2 : ℝ) ^ n)⁻¹ v) = latticeBump4 v := by
  rw [latticeCell_add_parabolicDilate, mul_inv_cancel₀ (two_pow_ne_zero n), parabolicDilate_one]
  unfold latticePoint
  rw [parabolicDilate_parabolicDilate_inv (two_pow_ne_zero n)]
  simp

theorem latticeCell_ne_zero {n : ℕ} {k : LatticeIndex} {w : ParabolicSpace}
    (h : latticeCell n k w ≠ 0) :
    (0 < w.1 - (latticePoint n k).1 ∧
        w.1 - (latticePoint n k).1 < 2 * (((2 : ℝ) ^ n)⁻¹) ^ 2) ∧
      ∀ i, 0 < w.2 i - (latticePoint n k).2 i ∧
        w.2 i - (latticePoint n k).2 i < 2 * ((2 : ℝ) ^ n)⁻¹ := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := latticeBump4_ne_zero h
  simp only [parabolicDilate, latticeCoe, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul] at h1 h2 h3
  have hD : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have e1 : w.1 - (latticePoint n k).1 =
      (((2 : ℝ) ^ n)⁻¹) ^ 2 * (((2 : ℝ) ^ n) ^ 2 * w.1 - k.1) := by
    simp only [latticePoint_fst]
    field_simp
  refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
  · rw [e1]; exact mul_pos (by positivity) h1
  · rw [e1, mul_comm 2]; exact mul_lt_mul_of_pos_left h2 (by positivity)
  · have e2 : w.2 i - (latticePoint n k).2 i =
        ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ n) * w.2 i - k.2 i) := by
      simp only [latticePoint_snd]
      field_simp
    obtain ⟨g1, g2⟩ := h3 i
    refine ⟨?_, ?_⟩
    · rw [e2]; exact mul_pos hD g1
    · rw [e2, mul_comm 2]; exact mul_lt_mul_of_pos_left g2 hD

theorem parabolicNorm_sub_latticePoint_le {n : ℕ} {k : LatticeIndex} {w : ParabolicSpace}
    (h : latticeCell n k w ≠ 0) :
    parabolicNorm (w - latticePoint n k) ≤ 8 * ((2 : ℝ) ^ n)⁻¹ := by
  have e : w - latticePoint n k =
      parabolicDilate ((2 : ℝ) ^ n)⁻¹ (parabolicDilate ((2 : ℝ) ^ n) w - latticeCoe k) := by
    rw [parabolicDilate_sub, parabolicDilate_inv_parabolicDilate (two_pow_ne_zero n)]
    rfl
  rw [e, parabolicNorm_parabolicDilate (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (parabolicNorm_le_of_latticeBump4_ne_zero h) (by positivity)

end RegularityStructures

end
