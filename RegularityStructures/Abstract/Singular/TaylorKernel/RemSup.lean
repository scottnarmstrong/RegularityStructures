/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorBox

/-!
# Pointwise (sup) bound for the box Taylor remainder

The pointwise analogue of `exists_integral_abs_remJ_le`: if `|s_j| ≤ d^{w_j}` and
`|D^ℓ φ| ≤ B ℓ` for every coordinate word `ℓ`, then

  `|remJ s m J φ w| ≤ ∑_{ℓ ∈ E} d^{|ℓ|_𝔰} B ℓ`

for a finite list `E` of words (depending only on `m`, `J`), each containing at least `m_j + 1`
letters `j` for some `j ∈ J`.

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.18.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem abs_remOp_le_of_sup {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace)
    (s : ℝ) (m : ℕ) (B : ℝ) (hB : ∀ u, |(dirDeriv e)^[m + 1] φ u| ≤ B) (w : ParabolicSpace) :
    |remOp e s m φ w| ≤ |s| ^ (m + 1) * B := by
  refine (abs_remOp_le hφ e s m w).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => |(dirDeriv e)^[m + 1] φ (w + (t * s) • e)|) (C := B)
    (fun t _ => by rw [Real.norm_eq_abs, abs_abs]; exact hB _)
  simp only [sub_zero, abs_one, mul_one] at h
  exact (le_abs_self _).trans (by simpa using h)

theorem exists_abs_remJ_le_sup (m : Fin 4 → ℕ) : ∀ (J : List (Fin 4)),
    ∃ E : List (List (Fin 4)), (∀ ℓ ∈ E, ∃ j ∈ J, m j + 1 ≤ ℓ.count j) ∧
      ∀ (s : Fin 4 → ℝ) (d : ℝ), 0 ≤ d → (∀ j, |s j| ≤ d ^ parabolicWeight j) →
        ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → ∀ B : List (Fin 4) → ℝ,
          (∀ ℓ u, |lineIter (ℓ.map coordDir) φ u| ≤ B ℓ) → ∀ w,
          |remJ s m J φ w| ≤ (E.map fun ℓ => d ^ indexWeight ℓ * B ℓ).sum
  | [] => ⟨[], by simp, fun s d _ _ φ _ B _ w => by simp [remJ, tyOp, disp]⟩
  | j :: J => by
    obtain ⟨E', hE'p, hE'⟩ := exists_abs_remJ_le_sup m J
    obtain ⟨W, hW⟩ := exists_abs_tyOp_le m J
    refine ⟨E' ++ W.map fun K => List.replicate (m j + 1) j ++ K, ?_, ?_⟩
    · intro ℓ hℓ
      rcases List.mem_append.1 hℓ with h | h
      · obtain ⟨j', hj', hc⟩ := hE'p ℓ h
        exact ⟨j', List.mem_cons_of_mem _ hj', hc⟩
      · obtain ⟨K, _, rfl⟩ := List.mem_map.1 h
        refine ⟨j, List.mem_cons_self .., ?_⟩
        rw [List.count_append, List.count_replicate_self]
        omega
    intro s d hd hs φ hφ B hB w
    set a : ParabolicSpace := s j • coordDir j with ha
    have hSφ : ContDiff ℝ ∞ fun u => φ (u + a) := hφ.comp (contDiff_id.add contDiff_const)
    have hrem := contDiff_remOp hφ (coordDir j) (s j) (m j)
    rw [remJ_cons s m j J hφ]
    simp only
    have h1 : |remJ s m J (fun u => φ (u + a)) w +
        tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w| ≤
        |remJ s m J (fun u => φ (u + a)) w| +
          |tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w| := abs_add_le _ _
    refine h1.trans ?_
    rw [List.map_append, List.sum_append]
    refine add_le_add ?_ ?_
    · refine (hE' s d hd hs hSφ B (fun ℓ u => ?_) w)
      rw [lineIter_shift]
      exact hB ℓ _
    · set ψ := remOp (coordDir j) (s j) (m j) φ with hψ
      refine (hW s d hd hs hrem w).trans ?_
      rw [List.map_map]
      refine List.sum_le_sum fun K _ => ?_
      simp only [Function.comp]
      have e1 : lineIter (K.map coordDir) ψ = remOp (coordDir j) (s j) (m j)
          (lineIter (K.map coordDir) φ) := lineIter_remOp hφ _ _ _ _
      have e2 : (dirDeriv (coordDir j))^[m j + 1] (lineIter (K.map coordDir) φ) =
          lineIter ((List.replicate (m j + 1) j ++ K).map coordDir) φ := by
        rw [List.map_append, List.map_replicate, lineIter_append, lineIter_replicate]
      have h3 := abs_remOp_le_of_sup (contDiff_lineIter hφ (K.map coordDir)) (coordDir j) (s j)
        (m j) (B (List.replicate (m j + 1) j ++ K)) (fun u => by rw [e2]; exact hB _ u) w
      rw [e1]
      have h4 : |s j| ^ (m j + 1) ≤ d ^ ((m j + 1) * parabolicWeight j) := by
        rw [mul_comm, pow_mul]
        exact pow_le_pow_left₀ (abs_nonneg _) (hs j) _
      have h5 : 0 ≤ B (List.replicate (m j + 1) j ++ K) := (abs_nonneg _).trans (hB _ 0)
      have h6 := h3.trans (mul_le_mul_of_nonneg_right h4 h5)
      have h7 := mul_le_mul_of_nonneg_left h6 (pow_nonneg hd (indexWeight K))
      rw [indexWeight_append, indexWeight_replicate, pow_add]
      calc _ ≤ _ := h7
        _ = _ := by ring

end RegularityStructures

end
