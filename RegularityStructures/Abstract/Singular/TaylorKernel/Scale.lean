/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.DTaylorDeriv
public import RegularityStructures.Analysis.Heat.Schauder.TaylorEstimate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorRegime

/-!
# Scaled form of the Taylor-remainder kernel `D^k K_n`

With `S = S^{2^n}` the parabolic dilation and `G = D^k h`,

  `dTaylorKernel h k n σ x y w = (2^n)^{3 + |k|_𝔰} · taylorProfile G σ (S (y - x)) (S (x - w))`

(`dTaylorKernel_eq_profile`), and it vanishes for `‖w - x‖_𝔰 > 2 · 2^{-n}` when
`‖y - x‖_𝔰 ≤ 2^{-n}` (`dTaylorKernel_eq_zero`).

Source: [Hai14] = arXiv:1303.5113v4, (5.14), proof of Lemma 5.18.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem coeffT_parabolicDilate (c : ℝ) (z : ParabolicSpace) (k : Fin 4 →₀ ℕ) :
    coeffT (parabolicCoords (parabolicDilate c z)) k = c ^ multiDeg k * coeffT (parabolicCoords z) k := by
  unfold coeffT
  have h : ∀ i, (parabolicCoords (parabolicDilate c z) i) ^ k i /
      ((Nat.factorial (k i) : ℕ) : ℝ) = c ^ (parabolicWeight i * k i) *
        (parabolicCoords z i ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ)) := fun i => by
    rw [parabolicCoords_parabolicDilate, mul_pow, ← pow_mul]; ring
  simp only [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← multiDeg_eq_sum]

theorem taylorProfile_scaledShell {G : ParabolicSpace → ℝ} (hG : ContDiff ℝ ∞ G) (n : ℕ) (σ : ℝ)
    (z u : ParabolicSpace) :
    taylorProfile (scaledShell G n) σ z u = ((2 : ℝ) ^ n) ^ 3 *
      taylorProfile G σ (parabolicDilate (2 ^ n) z) (parabolicDilate (2 ^ n) u) := by
  unfold taylorProfile
  have hadd : parabolicDilate ((2 : ℝ) ^ n) (u + z) =
      parabolicDilate (2 ^ n) u + parabolicDilate (2 ^ n) z := by
    simpa using (parabolicDilateCLM ((2 : ℝ) ^ n)).map_add u z
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · simp only [scaledShell, hadd]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [evalParabolic_monomial_div, evalParabolic_monomial_div, multiDirs_eq_map,
      lineIter_coordDir_scaledShell hG, indexWeight_toList, coeffT_parabolicDilate, ← multiDirs_eq_map]
    ring

theorem dTaylorKernel_eq_profile {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h) (k : Fin 4 →₀ ℕ)
    (n : ℕ) (σ : ℝ) (x y w : ParabolicSpace) :
    dTaylorKernel h k n σ x y w = ((2 : ℝ) ^ n) ^ (3 + multiDeg k) *
      taylorProfile (lineIter (multiDirs k) h) σ (parabolicDilate (2 ^ n) (y - x))
        (parabolicDilate (2 ^ n) (x - w)) := by
  rw [dTaylorKernel_eq h0]
  simp only
  rw [taylorKernel_eq_profile, taylorProfile_scaledShell (contDiff_lineIter h0 _)]
  ring

theorem dTaylorKernel_eq_zero {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (k : Fin 4 →₀ ℕ) (n : ℕ) (σ : ℝ)
    {x y w : ParabolicSpace} (hy : parabolicNorm (y - x) ≤ ((2 : ℝ) ^ n)⁻¹)
    (hw : 2 * ((2 : ℝ) ^ n)⁻¹ < parabolicNorm (w - x)) : dTaylorKernel h k n σ x y w = 0 := by
  have hs' : ∀ z, 1 < parabolicNorm z → lineIter (multiDirs k) h z = 0 := fun z hz =>
    lineIter_eq_zero_of_lt hs _ hz
  rw [dTaylorKernel_eq h0]
  simp only
  rw [taylorKernel_eq_profile, taylorProfile_eq_zero hs' n σ, mul_zero]
  have e : ((2 : ℝ)⁻¹) ^ n = ((2 : ℝ) ^ n)⁻¹ := inv_pow _ _
  have c := parabolicNorm_sub_comm x w
  linarith

end RegularityStructures

end
