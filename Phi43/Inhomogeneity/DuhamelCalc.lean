/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Inhomogeneity.DuhamelTime

/-!
# Calculus lemmas for the derivative bounds of the Duhamel field

* global iterated derivatives `ddA l g` of a function along a word `l` of coordinate directions of
  space-time, and their compatibility with the truncation `posPart` and with `Datum.pd`;
* additivity of `Datum.pdWord` and commutation of `∂_t` with spatial words;
* the heat equation with forcing as an identity of functions on all of space-time
  (`pd_zero_duhamelField_fun`): `∂_t θ = g⁺ + ∑ⱼ ∂ⱼ∂ⱼ θ`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Inhomogeneity

/-- The iterated global derivative of `g` along a word of space-time directions. -/
def ddA : List (Fin 4) → (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  | [], g => g
  | j :: l, g => ddv j (ddA l g)

end RegularityStructures.Inhomogeneity

end

public section

namespace RegularityStructures.Inhomogeneity

open RegularityStructures.PDE Set Filter Topology

variable {g : ParabolicSpace → ℝ}

theorem ddA_append (l₁ l₂ : List (Fin 4)) (g : ParabolicSpace → ℝ) :
    ddA (l₁ ++ l₂) g = ddA l₁ (ddA l₂ g) := by
  induction l₁ with
  | nil => rfl
  | cons j l ih => simp only [List.cons_append, ddA, ih]

theorem ddWord_eq_ddA (w : List (Fin 3)) (g : ParabolicSpace → ℝ) :
    Inhomogeneity.ddWord w g = ddA (w.map Fin.succ) g := by
  induction w with
  | nil => rfl
  | cons j w ih => simp only [Inhomogeneity.ddWord, List.map_cons, ddA, ih]

theorem pd_posPart (g : ParabolicSpace → ℝ) (i : Fin 4) :
    Datum.pd i (posPart g) = posPart (ddv i g) := by
  funext z
  by_cases hz : 0 < z.1
  · rw [Datum.pd, Datum.pdv_of_pos hz, posPart_of_pos _ hz]
    have : posPart g =ᶠ[𝓝 z] g :=
      Filter.eventually_of_mem (Datum.isOpen_posTime.mem_nhds hz) fun w hw => posPart_of_pos g hw
    rw [this.fderiv_eq]
    rfl
  · rw [Datum.pd, Datum.pdv_of_nonpos (not_lt.1 hz), posPart_of_nonpos _ (not_lt.1 hz)]

theorem pdIter_posPart (g : ParabolicSpace → ℝ) (i : Fin 4) (n : ℕ) :
    Datum.pdIter i n (posPart g) = posPart (ddA (List.replicate n i) g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Datum.pdIter_succ', ih, pd_posPart _, List.replicate_succ]
    rfl

theorem pdWord_posPart (g : ParabolicSpace → ℝ) (w : List (Fin 3)) :
    Datum.pdWord w (posPart g) = posPart (ddA (w.map Fin.succ) g) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Datum.pd j.succ (Datum.pdWord w (posPart g)) = _
    rw [ih, pd_posPart _]
    rfl

theorem pdWord_add {F G : ParabolicSpace → ℝ} (hF : Datum.SmoothPos F) (hG : Datum.SmoothPos G)
    (w : List (Fin 3)) : Datum.pdWord w (F + G) = Datum.pdWord w F + Datum.pdWord w G := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Datum.pd j.succ (Datum.pdWord w (F + G)) = Datum.pd j.succ (Datum.pdWord w F) +
      Datum.pd j.succ (Datum.pdWord w G)
    rw [ih]
    exact Datum.pdv_add (hF.pdWord w) (hG.pdWord w)

theorem pdWord_sum {ι : Type*} (s : Finset ι) {F : ι → ParabolicSpace → ℝ}
    (hF : ∀ a ∈ s, Datum.SmoothPos (F a)) (w : List (Fin 3)) :
    Datum.pdWord w (∑ a ∈ s, F a) = ∑ a ∈ s, Datum.pdWord w (F a) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Datum.pd j.succ (Datum.pdWord w (∑ a ∈ s, F a)) = ∑ a ∈ s, Datum.pd j.succ (Datum.pdWord w (F a))
    rw [ih]
    exact Datum.pdv_sum s fun a ha => (hF a ha).pdWord w

theorem pd_pdWord_comm {F : ParabolicSpace → ℝ} (hF : Datum.SmoothPos F) (i : Fin 4)
    (w : List (Fin 3)) : Datum.pd i (Datum.pdWord w F) = Datum.pdWord w (Datum.pd i F) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Datum.pd i (Datum.pd j.succ (Datum.pdWord w F)) =
      Datum.pd j.succ (Datum.pdWord w (Datum.pd i F))
    rw [← ih]
    exact Datum.pd_comm (hF.pdWord w) i j.succ

/-- **The heat equation with forcing**, as an identity of functions on space-time. -/
theorem pd_zero_duhamelField_fun (hg : PerSmooth g) :
    Datum.pd 0 (duhamelField hg) = posPart g +
      ∑ j : Fin 3, Datum.pd j.succ (Datum.pd j.succ (duhamelField hg)) := by
  funext z
  by_cases hz : 0 < z.1
  · rw [pd_zero_duhamelField hg hz, Pi.add_apply, Finset.sum_apply, posPart_of_pos _ hz]
  · have hz' := not_lt.1 hz
    rw [Datum.pd, Datum.pdv_of_nonpos hz', Pi.add_apply, Finset.sum_apply, posPart_of_nonpos _ hz']
    simp [Datum.pd, Datum.pdv_of_nonpos hz']

end RegularityStructures.Inhomogeneity

end
