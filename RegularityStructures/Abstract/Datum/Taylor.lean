/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# One-coordinate Taylor remainders

`taylorRem i n h G z = G (z + h e_i) - ∑_{a < n} h^a / a! · ∂_i^a G (z)` is the Taylor remainder of
`G` in the `i`-th coordinate direction. If `|∂_i^n G| ≤ M` on the segment `[z, z + h e_i]` (which
lies in `{t > 0}`), then `|taylorRem i n h G z| ≤ M |h|^n` (`abs_taylorRem_le`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The Taylor remainder of order `n` of `G` at `z` in the direction `e_i` with step `h`. -/
def taylorRem (i : Fin 4) (n : ℕ) (h : ℝ) (G : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  G (z + h • stBasis i) - ∑ a ∈ Finset.range n, h ^ a / (a.factorial : ℝ) * pdIter i a G z

end RegularityStructures.Datum

end

public section

open scoped ContDiff
open Set

namespace RegularityStructures.Datum

theorem hasDerivAt_taylorPoly (c : ℕ → ℝ) (h s : ℝ) (n : ℕ) :
    HasDerivAt (fun s : ℝ => ∑ a ∈ Finset.range (n + 1), (s * h) ^ a / (a.factorial : ℝ) * c a)
      (h * ∑ a ∈ Finset.range n, (s * h) ^ a / (a.factorial : ℝ) * c (a + 1)) s := by
  induction n with
  | zero => simpa using hasDerivAt_const s (c 0)
  | succ n ih =>
    have h1 : HasDerivAt (fun s : ℝ => (s * h) ^ (n + 1) / ((n + 1).factorial : ℝ) * c (n + 1))
        (h * ((s * h) ^ n / (n.factorial : ℝ) * c (n + 1))) s := by
      have h0 : HasDerivAt (fun s : ℝ => s * h) h s := by
        simpa using (hasDerivAt_id s).mul_const h
      have := ((h0.pow (n + 1)).div_const ((n + 1).factorial : ℝ)).mul_const (c (n + 1))
      convert this using 1
      rw [Nat.factorial_succ]
      push_cast
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
    rw [show (fun s : ℝ => ∑ a ∈ Finset.range (n + 1 + 1), (s * h) ^ a / (a.factorial : ℝ) * c a) =
      fun s : ℝ => (∑ a ∈ Finset.range (n + 1), (s * h) ^ a / (a.factorial : ℝ) * c a) +
        (s * h) ^ (n + 1) / ((n + 1).factorial : ℝ) * c (n + 1) from by
      funext s
      exact Finset.sum_range_succ _ _]
    rw [Finset.sum_range_succ _ n, mul_add]
    exact ih.add h1

theorem abs_taylorRem_le (i : Fin 4) (n : ℕ) :
    ∀ {G : ParabolicSpace → ℝ}, SmoothPos G → ∀ (z : ParabolicSpace) (h M : ℝ),
      (∀ s ∈ Icc (0 : ℝ) 1, 0 < (z + (s * h) • stBasis i).1) →
      (∀ s ∈ Icc (0 : ℝ) 1, |pdIter i n G (z + (s * h) • stBasis i)| ≤ M) →
      |taylorRem i n h G z| ≤ M * |h| ^ n := by
  induction n with
  | zero =>
    intro G _ z h M _ hM
    have := hM 1 ⟨zero_le_one, le_rfl⟩
    simpa [taylorRem, pdIter_zero] using this
  | succ n ih =>
    intro G hG z h M hseg hM
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
    -- the function `ψ(s) = G (z + s h e) - ∑_{a ≤ n} (s h)^a / a! ∂^a G (z)`
    set ψ : ℝ → ℝ := fun s => G (z + (s * h) • stBasis i) -
      ∑ a ∈ Finset.range (n + 1), (s * h) ^ a / (a.factorial : ℝ) * pdIter i a G z with hψ
    have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + (s * h) • stBasis i) (h • stBasis i) s := by
      intro s
      have h0 : HasDerivAt (fun s : ℝ => s * h) h s := by
        simpa using (hasDerivAt_id s).mul_const h
      simpa using h0.smul_const (stBasis i)
    have hder : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt ψ
        (h * taylorRem i n (s * h) (pd i G) z) s := by
      intro s hs
      have hpt := hseg s hs
      have hGd : HasDerivAt (fun s : ℝ => G (z + (s * h) • stBasis i))
          (h * pd i G (z + (s * h) • stBasis i)) s := by
        have h2 := (hG.differentiableAt hpt).hasFDerivAt.comp_hasDerivAt s (hline s)
        rw [map_smul, smul_eq_mul] at h2
        have e : h * pd i G (z + (s * h) • stBasis i) =
            h * (fderiv ℝ G (z + (s * h) • stBasis i)) (stBasis i) := by
          show h * pdv (stBasis i) G _ = _
          rw [pdv_of_pos hpt]
        rw [e]
        exact h2
      have hP := hasDerivAt_taylorPoly (fun a => pdIter i a G z) h s n
      have e : taylorRem i n (s * h) (pd i G) z = pd i G (z + (s * h) • stBasis i) -
          ∑ a ∈ Finset.range n, (s * h) ^ a / (a.factorial : ℝ) * pdIter i (a + 1) G z := by
        simp only [taylorRem, pdIter_succ]
      convert hGd.sub hP using 1
      rw [e, mul_sub, Finset.mul_sum]
    have hbd : ∀ s ∈ Icc (0 : ℝ) 1, |h * taylorRem i n (s * h) (pd i G) z| ≤ M * |h| ^ (n + 1) := by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      have hs1 : s ≤ 1 := hs.2
      have := ih (hG.pd i) z (s * h) M
        (fun s' hs' => by
          have := hseg (s' * s) ⟨mul_nonneg hs'.1 hs0, by nlinarith [hs'.2]⟩
          simpa [mul_assoc] using this)
        (fun s' hs' => by
          have := hM (s' * s) ⟨mul_nonneg hs'.1 hs0, by nlinarith [hs'.2]⟩
          simpa [← pdIter_succ, mul_assoc] using this)
      rw [abs_mul]
      calc |h| * |taylorRem i n (s * h) (pd i G) z| ≤ |h| * (M * |s * h| ^ n) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ ≤ |h| * (M * |h| ^ n) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hM0) (abs_nonneg _)
            refine pow_le_pow_left₀ (abs_nonneg _) ?_ n
            rw [abs_mul, abs_of_nonneg hs0]
            exact mul_le_of_le_one_left (abs_nonneg _) hs1
        _ = M * |h| ^ (n + 1) := by ring
    have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ)
      (f' := fun s => h * taylorRem i n (s * h) (pd i G) z) (C := M * |h| ^ (n + 1))
      (fun s hs => (hder s hs).hasDerivWithinAt) (fun s hs => by
        simpa [Real.norm_eq_abs] using hbd s ⟨hs.1, hs.2.le⟩)
    have h0 : ψ 0 = 0 := by simp [hψ, Finset.sum_range_succ', pdIter_zero]
    have h1 : ψ 1 = taylorRem i (n + 1) h G z := by simp [hψ, taylorRem]
    rw [h0, h1, sub_zero, Real.norm_eq_abs] at key
    exact key

end RegularityStructures.Datum

end
