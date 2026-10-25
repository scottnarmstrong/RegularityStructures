/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorBox
public import RegularityStructures.Analysis.Heat.Schauder.TaylorBound
public import RegularityStructures.Analysis.Heat.Schauder.TaylorTySupport

/-!
# `L¹` bound on the Taylor remainder of a shell

Support and smoothness of the Taylor remainder `remJ`, and the `L¹` bound
`exists_integral_abs_remJ_le`.

Source: [Hai14, proof of Lemma 5.19].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem hasCompactSupport_shift {φ : ParabolicSpace → ℝ} (hφ : HasCompactSupport φ)
    (a : ParabolicSpace) : HasCompactSupport fun w => φ (w + a) :=
  hφ.comp_homeomorph (Homeomorph.addRight a)

theorem contDiff_remJ (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) (J : List (Fin 4))
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (remJ s m J φ) := by
  have : remJ s m J φ = fun w => φ (w + disp s J) - tyOp s m J φ w := rfl
  rw [this]
  exact (hφ.comp (contDiff_id.add contDiff_const)).sub (contDiff_tyOp s m J hφ)

theorem hasCompactSupport_remJ (s : Fin 4 → ℝ) (m : Fin 4 → ℕ) (J : List (Fin 4))
    {φ : ParabolicSpace → ℝ} (hc : HasCompactSupport φ) : HasCompactSupport (remJ s m J φ) := by
  have : remJ s m J φ = (fun w => φ (w + disp s J)) - tyOp s m J φ := rfl
  rw [this]
  exact (hasCompactSupport_shift hc _).sub (hasCompactSupport_tyOp s m J hc)

theorem hasCompactSupport_remOp {φ : ParabolicSpace → ℝ} (hc : HasCompactSupport φ)
    (e : ParabolicSpace) (s : ℝ) (m : ℕ) : HasCompactSupport (remOp e s m φ) := by
  have : remOp e s m φ = (fun w => φ (w + s • e)) - tayOp e s m φ := rfl
  rw [this]
  exact (hasCompactSupport_shift hc _).sub (hasCompactSupport_tayOp hc e s m)

theorem integrable_list_sum {α : Type*} (l : List α) (f : α → ParabolicSpace → ℝ)
    (hf : ∀ a ∈ l, Integrable (f a)) : Integrable fun w => (l.map fun a => f a w).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a (List.mem_cons_self ..)).add (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

theorem integral_list_sum {α : Type*} (l : List α) (f : α → ParabolicSpace → ℝ)
    (hf : ∀ a ∈ l, Integrable (f a)) :
    ∫ w, (l.map fun a => f a w).sum = (l.map fun a => ∫ w, f a w).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf a (List.mem_cons_self ..))
      (integrable_list_sum l f fun b hb => hf b (List.mem_cons_of_mem _ hb)),
      ih fun b hb => hf b (List.mem_cons_of_mem _ hb)]

theorem integral_abs_lineIter_shift {φ : ParabolicSpace → ℝ} (K : List ParabolicSpace)
    (a : ParabolicSpace) :
    ∫ w, |lineIter K (fun u => φ (u + a)) w| = ∫ w, |lineIter K φ w| := by
  have : (volume : Measure ParabolicSpace).IsAddRightInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [lineIter_shift]
  exact integral_add_right_eq_self (fun w => |lineIter K φ w|) a

theorem exists_integral_abs_remJ_le (m : Fin 4 → ℕ) : ∀ (J : List (Fin 4)),
    ∃ E : List (List (Fin 4)), (∀ ℓ ∈ E, ∃ j ∈ J, m j + 1 ≤ ℓ.count j) ∧
      ∀ (s : Fin 4 → ℝ) (d : ℝ), 0 ≤ d → (∀ j, |s j| ≤ d ^ parabolicWeight j) →
        ∀ {φ : ParabolicSpace → ℝ}, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          ∫ w, |remJ s m J φ w| ≤
            (E.map fun ℓ => d ^ indexWeight ℓ * ∫ w, |lineIter (ℓ.map coordDir) φ w|).sum
  | [] => ⟨[], by simp, fun s d _ _ φ _ _ => by simp [remJ, tyOp, disp]⟩
  | j :: J => by
    obtain ⟨E', hE'p, hE'⟩ := exists_integral_abs_remJ_le m J
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
    intro s d hd hs φ hφ hc
    set a : ParabolicSpace := s j • coordDir j with ha
    have hSφ : ContDiff ℝ ∞ fun u => φ (u + a) := hφ.comp (contDiff_id.add contDiff_const)
    have hSc : HasCompactSupport fun u => φ (u + a) := hasCompactSupport_shift hc a
    have hrem := contDiff_remOp hφ (coordDir j) (s j) (m j)
    have hremc := hasCompactSupport_remOp hc (coordDir j) (s j) (m j)
    have hAs := contDiff_remJ s m J hSφ
    have hAc := hasCompactSupport_remJ s m J hSc
    have hBs := contDiff_tyOp s m J hrem
    have hBc := hasCompactSupport_tyOp s m J hremc
    have hAi : Integrable (remJ s m J fun u => φ (u + a)) :=
      hAs.continuous.integrable_of_hasCompactSupport hAc
    have hBi : Integrable (tyOp s m J (remOp (coordDir j) (s j) (m j) φ)) :=
      hBs.continuous.integrable_of_hasCompactSupport hBc
    rw [remJ_cons s m j J hφ]
    simp only
    -- split
    have h1 : ∫ w, |remJ s m J (fun u => φ (u + a)) w +
        tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w| ≤
        (∫ w, |remJ s m J (fun u => φ (u + a)) w|) +
          ∫ w, |tyOp s m J (remOp (coordDir j) (s j) (m j) φ) w| := by
      rw [← integral_add hAi.abs hBi.abs]
      exact integral_mono ((hAi.add hBi).abs) (hAi.abs.add hBi.abs)
        fun w => abs_add_le _ _
    refine h1.trans ?_
    rw [List.map_append, List.sum_append]
    refine add_le_add ?_ ?_
    · refine (hE' s d hd hs hSφ hSc).trans (le_of_eq ?_)
      congr 1
      refine List.map_congr_left fun ℓ _ => ?_
      rw [integral_abs_lineIter_shift]
    · set ψ := remOp (coordDir j) (s j) (m j) φ with hψ
      have hterm : ∀ K ∈ W, Integrable fun w => d ^ indexWeight K *
          |lineIter (K.map coordDir) ψ w| := fun K _ => by
        have hcont := ((contDiff_lineIter hrem (K.map coordDir)).continuous.abs.const_mul
          (d ^ indexWeight K))
        refine hcont.integrable_of_hasCompactSupport ?_
        exact (hasCompactSupport_lineIter hremc _).abs.mul_left
      have step1 : ∫ w, |tyOp s m J ψ w| ≤
          ∫ w, (W.map fun K => d ^ indexWeight K * |lineIter (K.map coordDir) ψ w|).sum :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          (integrable_list_sum W _ hterm) (Filter.Eventually.of_forall fun w =>
            hW s d hd hs hrem w)
      refine step1.trans ?_
      rw [integral_list_sum W _ hterm, List.map_map]
      refine List.sum_le_sum fun K _ => ?_
      · simp only [Function.comp]
        rw [integral_const_mul]
        have hφ' := contDiff_lineIter hφ (K.map coordDir)
        have hc' := hasCompactSupport_lineIter hc (K.map coordDir)
        have e1 : lineIter (K.map coordDir) ψ = remOp (coordDir j) (s j) (m j)
            (lineIter (K.map coordDir) φ) := lineIter_remOp hφ _ _ _ _
        have e2 : (dirDeriv (coordDir j))^[m j + 1] (lineIter (K.map coordDir) φ) =
            lineIter ((List.replicate (m j + 1) j ++ K).map coordDir) φ := by
          rw [List.map_append, List.map_replicate, lineIter_append, lineIter_replicate]
        have h3 := integral_abs_remOp_le hφ' hc' (coordDir j) (s j) (m j)
        rw [e2] at h3
        rw [e1]
        have h4 : |s j| ^ (m j + 1) ≤ d ^ ((m j + 1) * parabolicWeight j) := by
          rw [mul_comm, pow_mul]
          exact pow_le_pow_left₀ (abs_nonneg _) (hs j) _
        have h5 : 0 ≤ ∫ w, |lineIter ((List.replicate (m j + 1) j ++ K).map coordDir) φ w| :=
          integral_nonneg fun _ => abs_nonneg _
        have h6 := h3.trans (mul_le_mul_of_nonneg_right h4 h5)
        have h7 := mul_le_mul_of_nonneg_left h6 (pow_nonneg hd (indexWeight K))
        rw [indexWeight_append, indexWeight_replicate, pow_add]
        calc _ ≤ _ := h7
          _ = _ := by ring

end RegularityStructures

end
