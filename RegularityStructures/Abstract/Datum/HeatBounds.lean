/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Deriv

/-!
# Derivative bounds from spatial bounds and the heat equation

`HeatLike η A F` packages the properties of a solution `F(t, x) = P_t a(x)` of the heat equation
with `a ∈ 𝒞^η` that are used for the Taylor estimates: `F` is `C^∞` on `{t > 0}`, solves
`∂_t F = ΔF` there, and every spatial derivative of order `m` is bounded by
`K_m A t^{(η - m)/2}` for `0 < t ≤ 1` (`SpatialBound`). The heat equation turns time derivatives
into pairs of spatial ones, so `∂_t^{k₀} ∂_x^β F` is bounded by `K A t^{(η - 2 k₀ - |β|)/2}`
(`HeatLike.bound_D`).
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The spatial derivative along a word in `{1, 2, 3}` (the coordinate `j : Fin 3` is the
direction `j + 1` of space-time). -/
def pdWord : List (Fin 3) → (ParabolicSpace → ℝ) → ParabolicSpace → ℝ
  | [], F => F
  | j :: w, F => pd j.succ (pdWord w F)

/-- The heat equation `∂_t F = ΔF`. -/
def HeatEq (F : ParabolicSpace → ℝ) : Prop :=
  pd 0 F = ∑ j : Fin 3, pd j.succ (pd j.succ F)

/-- Every spatial derivative of order `m` of every `F i` is `O(A i · t^{(η - m)/2})` for
`0 < t ≤ 1`, with a constant independent of `i`. -/
def SpatialBound {κ : Type*} (η : ℝ) (A : κ → ℝ) (F : κ → ParabolicSpace → ℝ) : Prop :=
  ∀ m : ℕ, ∃ K : ℝ, ∀ (i : κ) (w : List (Fin 3)), w.length = m → ∀ z : ParabolicSpace,
    0 < z.1 → z.1 ≤ 1 → |pdWord w (F i) z| ≤ K * A i * z.1 ^ ((η - m) / 2)

/-- A family of smooth solutions of the heat equation with the spatial bounds of `P_t a`,
`a ∈ 𝒞^η`, `‖a‖_η ≤ A i`, uniformly in the family. -/
structure HeatLike {κ : Type*} (η : ℝ) (A : κ → ℝ) (F : κ → ParabolicSpace → ℝ) : Prop where
  smooth : ∀ i, SmoothPos (F i)
  heat : ∀ i, HeatEq (F i)
  spatial : SpatialBound η A F

end RegularityStructures.Datum

end

public section

open scoped ContDiff

namespace RegularityStructures.Datum

theorem pdWord_nil (F : ParabolicSpace → ℝ) : pdWord [] F = F := rfl

theorem pdWord_append (w₁ w₂ : List (Fin 3)) (F : ParabolicSpace → ℝ) :
    pdWord (w₁ ++ w₂) F = pdWord w₁ (pdWord w₂ F) := by
  induction w₁ with
  | nil => rfl
  | cons j w ih => simp only [List.cons_append, pdWord, ih]

theorem pdWord_replicate (j : Fin 3) (b : ℕ) (F : ParabolicSpace → ℝ) :
    pdWord (List.replicate b j) F = pdIter j.succ b F := by
  induction b with
  | zero => rfl
  | succ b ih => rw [List.replicate_succ, pdWord, ih, pdIter_succ']

theorem SmoothPos.pdWord {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (w : List (Fin 3)) :
    SmoothPos (RegularityStructures.Datum.pdWord w F) := by
  induction w with
  | nil => exact hF
  | cons j w ih => exact ih.pd _

/-- The heat equation for the derivative `∂_i F`. -/
theorem heatEq_pd {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (h : HeatEq F) (i : Fin 4) :
    HeatEq (pd i F) := by
  unfold HeatEq at h ⊢
  rw [pd_comm hF 0 i, h]
  have h2 : ∀ j : Fin 3, SmoothPos (pd j.succ (pd j.succ F)) := fun j => (hF.pd _).pd _
  rw [show pd i (∑ j : Fin 3, pd j.succ (pd j.succ F)) =
    ∑ j : Fin 3, pd i (pd j.succ (pd j.succ F)) from pdv_sum _ fun j _ => h2 j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pd_comm (hF.pd _) i, pd_comm hF i]

theorem pdIter_sum (i : Fin 4) (n : ℕ) {ι : Type*} (s : Finset ι) {F : ι → ParabolicSpace → ℝ}
    (hF : ∀ a ∈ s, SmoothPos (F a)) :
    pdIter i n (∑ a ∈ s, F a) = ∑ a ∈ s, pdIter i n (F a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdIter_succ', ih]
    rw [show pd i (∑ a ∈ s, pdIter i n (F a)) = ∑ a ∈ s, pd i (pdIter i n (F a)) from
      pdv_sum _ fun a ha => (hF a ha).pdIter i n]
    exact Finset.sum_congr rfl fun a _ => (pdIter_succ' i n (F a)).symm

variable {κ : Type*}

theorem spatialBound_pd {η : ℝ} {A : κ → ℝ} {F : κ → ParabolicSpace → ℝ}
    (h : SpatialBound η A F) (j : Fin 3) : SpatialBound (η - 1) A (fun i => pd j.succ (F i)) := by
  intro m
  obtain ⟨K, hK⟩ := h (m + 1)
  refine ⟨K, fun i w hw z hz hz1 => ?_⟩
  have e : pdWord w (pd j.succ (F i)) = pdWord (w ++ [j]) (F i) := by
    rw [pdWord_append]; rfl
  rw [e]
  have := hK i (w ++ [j]) (by simp [hw]) z hz hz1
  convert this using 3
  push_cast
  ring

theorem heatLike_pd {η : ℝ} {A : κ → ℝ} {F : κ → ParabolicSpace → ℝ} (h : HeatLike η A F)
    (j : Fin 3) : HeatLike (η - 1) A (fun i => pd j.succ (F i)) :=
  ⟨fun i => (h.smooth i).pd _, fun i => heatEq_pd (h.smooth i) (h.heat i) _,
    spatialBound_pd h.spatial j⟩

theorem heatLike_pdIter {η : ℝ} {A : κ → ℝ} {F : κ → ParabolicSpace → ℝ} (h : HeatLike η A F)
    (j : Fin 3) (b : ℕ) : HeatLike (η - b) A (fun i => pdIter j.succ b (F i)) := by
  induction b with
  | zero =>
    rw [Nat.cast_zero, sub_zero]
    exact h
  | succ b ih =>
    have := heatLike_pd ih j
    have e : η - ((b + 1 : ℕ) : ℝ) = η - b - 1 := by push_cast; ring
    rw [e]
    simp only [pdIter_succ']
    exact this

theorem heatLike_bound_pdIter_zero {A : κ → ℝ} (a : ℕ) :
    ∀ {η : ℝ} {F : κ → ParabolicSpace → ℝ}, HeatLike η A F →
      ∃ K : ℝ, ∀ (i : κ) (z : ParabolicSpace), 0 < z.1 → z.1 ≤ 1 →
        |pdIter 0 a (F i) z| ≤ K * A i * z.1 ^ ((η - 2 * a) / 2) := by
  induction a with
  | zero =>
    intro η F h
    obtain ⟨K, hK⟩ := h.spatial 0
    refine ⟨K, fun i z hz hz1 => ?_⟩
    have := hK i [] rfl z hz hz1
    simpa [pdWord_nil, pdIter_zero] using this
  | succ a ih =>
    intro η F h
    have hj : ∀ j : Fin 3, ∃ K : ℝ, ∀ (i : κ) (z : ParabolicSpace), 0 < z.1 → z.1 ≤ 1 →
        |pdIter 0 a (pd j.succ (pd j.succ (F i))) z| ≤
          K * A i * z.1 ^ ((η - 1 - 1 - 2 * a) / 2) :=
      fun j => ih (F := fun i => pd j.succ (pd j.succ (F i)))
        (heatLike_pd (heatLike_pd h j) j)
    choose K hK using hj
    refine ⟨∑ j, K j, fun i z hz hz1 => ?_⟩
    have hsm : ∀ j ∈ (Finset.univ : Finset (Fin 3)), SmoothPos (pd j.succ (pd j.succ (F i))) :=
      fun j _ => ((h.smooth i).pd _).pd _
    have e : pdIter 0 (a + 1) (F i) =
        ∑ j : Fin 3, pdIter 0 a (pd j.succ (pd j.succ (F i))) := by
      rw [pdIter_succ, h.heat i, pdIter_sum 0 a _ hsm]
    rw [e, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    convert hK j i z hz hz1 using 3
    push_cast
    ring

theorem heatLike_bound_D {η : ℝ} {A : κ → ℝ} {F : κ → ParabolicSpace → ℝ}
    (h : HeatLike η A F) (k : Fin 4 → ℕ) :
    ∃ K : ℝ, ∀ (i : κ) (z : ParabolicSpace), 0 < z.1 → z.1 ≤ 1 →
      |D k (F i) z| ≤ K * A i * z.1 ^ ((η - ((2 * k 0 + k 1 + k 2 + k 3 : ℕ) : ℝ)) / 2) := by
  have h3 := heatLike_pdIter h 2 (k 3)
  have h2 := heatLike_pdIter h3 1 (k 2)
  have h1 := heatLike_pdIter h2 0 (k 1)
  obtain ⟨K, hK⟩ := heatLike_bound_pdIter_zero (A := A) (k 0) h1
  refine ⟨K, fun i z hz hz1 => ?_⟩
  have e : (η - ((2 * k 0 + k 1 + k 2 + k 3 : ℕ) : ℝ)) / 2 =
      (η - ↑(k 3) - ↑(k 2) - ↑(k 1) - 2 * ↑(k 0)) / 2 := by
    push_cast
    ring
  rw [e]
  exact hK i z hz hz1

end RegularityStructures.Datum

end
