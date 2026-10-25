/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorGen
public import RegularityStructures.Analysis.Heat.Schauder.TaylorDeriv
public import RegularityStructures.Analysis.Heat.Annihilating.ScaledDeriv
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeReflect
public import RegularityStructures.Analysis.Heat.Schauder.ShellIntegral

/-!
# The parabolic generator on shifts and sums

Commutation of the parabolic generator with shifts, differences and finite sums.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem parabolicGenerator_shift {f : ParabolicSpace → ℝ} (a : ParabolicSpace) :
    parabolicGenerator (fun w => f (w + a)) = fun w => parabolicGenerator f (w + a) := by
  funext w
  unfold parabolicGenerator
  rw [iteratedFDeriv_comp_add_right, iteratedFDeriv_comp_add_right]

theorem parabolicGenerator_sub' {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    parabolicGenerator (fun w => f w - g w) =
      fun w => parabolicGenerator f w - parabolicGenerator g w := by
  have hk : ∀ k : ℕ, ContDiff ℝ k f := fun k => hf.of_le (by exact_mod_cast le_top)
  have hk' : ∀ k : ℕ, ContDiff ℝ k g := fun k => hg.of_le (by exact_mod_cast le_top)
  funext w
  have E : ∀ (k : ℕ) (v : ParabolicSpace),
      iteratedFDeriv ℝ k (fun w => f w - g w) w (fun _ => v) =
        iteratedFDeriv ℝ k f w (fun _ => v) - iteratedFDeriv ℝ k g w (fun _ => v) := by
    intro k v
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := w) (i := k) (f := f) (g := g)
      (hk k).contDiffAt (hk' k).contDiffAt
    have h2 : (fun w => f w - g w) = f - g := rfl
    rw [h2, this]
    rfl
  unfold parabolicGenerator
  simp only [E, Finset.sum_sub_distrib]
  ring

theorem parabolicGenerator_add' {f g : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) :
    parabolicGenerator (fun w => f w + g w) =
      fun w => parabolicGenerator f w + parabolicGenerator g w := by
  have hk : ∀ k : ℕ, ContDiff ℝ k f := fun k => hf.of_le (by exact_mod_cast le_top)
  have hk' : ∀ k : ℕ, ContDiff ℝ k g := fun k => hg.of_le (by exact_mod_cast le_top)
  funext w
  have E : ∀ (k : ℕ) (v : ParabolicSpace),
      iteratedFDeriv ℝ k (fun w => f w + g w) w (fun _ => v) =
        iteratedFDeriv ℝ k f w (fun _ => v) + iteratedFDeriv ℝ k g w (fun _ => v) := by
    intro k v
    have := iteratedFDeriv_add_apply (𝕜 := ℝ) (x := w) (i := k) (f := f) (g := g)
      (hk k).contDiffAt (hk' k).contDiffAt
    have h2 : (fun w => f w + g w) = f + g := rfl
    rw [h2, this]
    rfl
  unfold parabolicGenerator
  simp only [E, Finset.sum_add_distrib]
  ring

theorem parabolicGenerator_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ParabolicSpace → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    parabolicGenerator (fun w => ∑ i ∈ s, f i w) =
      fun w => ∑ i ∈ s, parabolicGenerator (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext w
    unfold parabolicGenerator
    simp [iteratedFDeriv_fun_zero]
  | insert a s ha ih =>
    have hs : ContDiff ℝ ∞ fun w => ∑ i ∈ s, f i w :=
      ContDiff.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : (fun w => ∑ i ∈ insert a s, f i w) =
        fun w => f a w + ∑ i ∈ s, f i w := by
      funext w; rw [Finset.sum_insert ha]
    rw [hsum, parabolicGenerator_add' (hf a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]
    funext w
    rw [Finset.sum_insert ha]

end RegularityStructures

end
