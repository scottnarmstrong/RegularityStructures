/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelCalc
public import RegularityStructures.Abstract.Datum.Lift

/-!
# Derivative bounds of the Duhamel field from derivative bounds of the forcing

[Hai14, Section 9.4]. For `g` smooth and spatially periodic with `|ddA l g| ≤ B` on
`[0, 1] × ℝ³` for all words `l` of length `≤ L` (`DerivHyp g B L`), every mixed derivative
`∂_t^a ∂_x^w θ` of the Duhamel field `θ = duhamelField g` with `2a + |w| ≤ L` is bounded on
`(0, 1] × ℝ³` by `duhCst a * B` (`abs_pdIter_pdWord_duhamelField_le`), where
`duhCst 0 = 1`, `duhCst (a+1) = 1 + 3 duhCst a`: the time derivative is traded for the Laplacian and
the forcing by `∂_t θ = g⁺ + Δθ`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

/-- Bound of all derivatives of `g` along words of length `≤ L` on `[0, 1] × ℝ³`. -/
def DerivHyp (g : ParabolicSpace → ℝ) (B : ℝ) (L : ℕ) : Prop :=
  ∀ l : List (Fin 4), l.length ≤ L → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y : Fin 3 → ℝ,
    |ddA l g (s, y)| ≤ B

/-- The constants of the derivative bounds of the Duhamel field. -/
def duhCst : ℕ → ℝ
  | 0 => 1
  | a + 1 => 1 + 3 * duhCst a

end RegularityStructures.Inhomogeneity

end

public section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE Set Filter Topology

variable {g : ParabolicSpace → ℝ}

theorem duhCst_nonneg (a : ℕ) : 0 ≤ duhCst a := by
  induction a with
  | zero => simp [duhCst]
  | succ a ih => simp only [duhCst]; linarith

theorem DerivHyp.nonneg {B : ℝ} {L : ℕ} (h : DerivHyp g B L) : 0 ≤ B :=
  (abs_nonneg _).trans (h [] (Nat.zero_le _) 0 ⟨le_rfl, zero_le_one⟩ 0)

theorem abs_posPart_ddA_le {B : ℝ} {L : ℕ} (h : DerivHyp g B L) {l : List (Fin 4)}
    (hl : l.length ≤ L) {z : ParabolicSpace} (hz : z ∈ Ioc (0 : ℝ) 1 ×ˢ (univ : Set (Fin 3 → ℝ))) :
    |posPart (ddA l g) z| ≤ B := by
  rw [posPart_of_pos _ hz.1.1]
  exact h l hl z.1 ⟨hz.1.1.le, hz.1.2⟩ z.2

theorem abs_pdWord_duhamelField_le (hg : PerSmooth g) {B : ℝ} {L : ℕ} (h : DerivHyp g B L)
    (w : List (Fin 3)) (hw : w.length ≤ L) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (y : Fin 3 → ℝ) : |Datum.pdWord w (duhamelField hg) (t, y)| ≤ B := by
  rw [pdWord_duhamelField hg w ht]
  have hM : ∀ s ∈ Icc (0 : ℝ) t, ∀ y, |Inhomogeneity.ddWord w g (s, y)| ≤ B := by
    intro s hs y'
    rw [ddWord_eq_ddA]
    exact h _ (by simpa using hw) s ⟨hs.1, hs.2.trans ht1⟩ y'
  have := abs_duhamelField_le (hg.ddWord w) hM ht y
  exact this.trans (by nlinarith [h.nonneg])

/-- **Derivative bounds of the Duhamel field**: if `|ddA l g| ≤ B` on `[0,1] × ℝ³` for all words of
length `≤ L`, then `|∂_t^a ∂_x^w θ| ≤ duhCst a * B` on `(0,1] × ℝ³` when `2a + |w| ≤ L`. -/
theorem abs_pdIter_pdWord_duhamelField_le (hg : PerSmooth g) (a : ℕ) :
    ∀ {B : ℝ} {L : ℕ}, DerivHyp g B L → ∀ (w : List (Fin 3)), 2 * a + w.length ≤ L →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ y : Fin 3 → ℝ,
        |Datum.pdIter 0 a (Datum.pdWord w (duhamelField hg)) (t, y)| ≤ duhCst a * B := by
  induction a with
  | zero =>
    intro B L h w hw t ht ht1 y
    have := abs_pdWord_duhamelField_le hg h w (by simpa using hw) ht ht1 y
    simpa [duhCst, Datum.pdIter_zero] using this
  | succ a ih =>
    intro B L h w hw t ht ht1 y
    have hθ := smoothPos_duhamelField hg
    have hsm1 : Datum.SmoothPos (Datum.pdIter 0 a (Datum.pdWord w (posPart g))) :=
      (hg.smoothPos_posPart.pdWord w).pdIter 0 a
    have hsm2 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), Datum.SmoothPos
        (Datum.pdWord (w ++ [j, j]) (duhamelField hg)) := fun j _ => hθ.pdWord _
    have e : Datum.pdIter 0 (a + 1) (Datum.pdWord w (duhamelField hg)) =
        Datum.pdIter 0 a (Datum.pdWord w (posPart g)) +
          ∑ j : Fin 3, Datum.pdIter 0 a (Datum.pdWord (w ++ [j, j]) (duhamelField hg)) := by
      rw [Datum.pdIter_succ, pd_pdWord_comm hθ, pd_zero_duhamelField_fun hg,
        pdWord_add hg.smoothPos_posPart
          (Datum.SmoothPos.sum fun j _ => (hθ.pd _).pd _) w,
        pdWord_sum _ (fun j _ => (hθ.pd _).pd _) w,
        Datum.pdIter_add_fun 0 a (hg.smoothPos_posPart.pdWord w)
          (Datum.SmoothPos.sum fun j _ => ((hθ.pd _).pd _).pdWord w),
        Datum.pdIter_sum 0 a _ (fun j _ => ((hθ.pd _).pd _).pdWord w)]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Datum.pdWord_append]
      rfl
    rw [e, Pi.add_apply, Finset.sum_apply]
    have h1 : |Datum.pdIter 0 a (Datum.pdWord w (posPart g)) (t, y)| ≤ B := by
      rw [pdWord_posPart, pdIter_posPart, ← ddA_append]
      refine abs_posPart_ddA_le h ?_ (z := (t, y)) ⟨⟨ht, ht1⟩, mem_univ _⟩
      simp only [List.length_append, List.length_replicate, List.length_map]
      omega
    have h2 : ∀ j : Fin 3, |Datum.pdIter 0 a (Datum.pdWord (w ++ [j, j]) (duhamelField hg))
        (t, y)| ≤ duhCst a * B := fun j =>
      ih h (w ++ [j, j]) (by simp; omega) ht ht1 y
    calc _ ≤ |Datum.pdIter 0 a (Datum.pdWord w (posPart g)) (t, y)| +
          |∑ j : Fin 3, Datum.pdIter 0 a (Datum.pdWord (w ++ [j, j]) (duhamelField hg)) (t, y)| :=
          abs_add_le _ _
      _ ≤ B + ∑ j : Fin 3, duhCst a * B := add_le_add h1
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => h2 j))
      _ = duhCst (a + 1) * B := by simp [duhCst]; ring

end RegularityStructures.Inhomogeneity

end
