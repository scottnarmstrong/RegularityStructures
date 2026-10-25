/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.HeatDeriv1

/-!
# `P_s g` is smooth with derivative bounds, for continuous `g`

For `g ∈ C(T³)` and `s > 0`, the lift `φ = P_s g ∘ torusProj` is `C^∞` on `ℝ³`
(`contDiff_lift_heatOp`), and every spatial derivative of order `m` is again of the form
`P_{s/2^m} g''` with `‖g''‖ ≤ K_m s^{-m/2} ‖g‖` (`exists_sdWord_heatOp`). The mechanism is
`∂ᵢ P_s g = P_{s/2} (∂ᵢ P_{s/2} g)` (`exists_sdLift_heatOp`), where `∂ᵢ P_{s/2} g` is a continuous
function bounded by `c₁ (s/2)^{-1/2} ‖g‖`.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- The periodic lift of a function on `T³`. -/
def liftFn (g : C(Torus3, ℝ)) : (Fin 3 → ℝ) → ℝ := fun y => g (torusProj y)

/-- The `i`-th partial derivative of a function on `ℝ³`. -/
def sdLift (i : Fin 3) (φ : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ φ y (Pi.single i 1)

/-- The iterated partial derivative along a word. -/
def sdWord : List (Fin 3) → ((Fin 3 → ℝ) → ℝ) → (Fin 3 → ℝ) → ℝ
  | [], φ => φ
  | i :: w, φ => sdLift i (sdWord w φ)

end RegularityStructures.Datum

end

public section

open MeasureTheory Filter Topology Real
open scoped ContDiff

namespace RegularityStructures.Datum

open RegularityStructures.PDE

/-- `∂ᵢ P_s g = P_{s/2} g'` with `g' = ∂ᵢ P_{s/2} g`, and `‖g'‖ ≤ c₁ (s/2)^{-1/2} ‖g‖`. -/
theorem exists_sdLift_heatOp (g : C(Torus3, ℝ)) {s : ℝ} (hs : 0 < s) (i : Fin 3) :
    ∃ g' : C(Torus3, ℝ), sdLift i (liftFn (heatOp s g)) = liftFn (heatOp (s / 2) g') ∧
      ‖g'‖ ≤ derivConst * (√(s / 2))⁻¹ * ‖g‖ := by
  have hs2 : 0 < s / 2 := half_pos hs
  obtain ⟨V, hV, hbV⟩ := exists_hasTorusDeriv_heatOp g hs2
  have h2 := hasTorusDeriv_heatOp hV (s / 2)
  have hsg : heatOp (s / 2) (heatOp (s / 2) g) = heatOp s g := by
    rw [heatOp_heatOp hs2.le hs2.le, add_halves]
  rw [hsg] at h2
  set g' : C(Torus3, ℝ) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i
    ).compLeftContinuous ℝ Torus3 V with hg'
  refine ⟨g', ?_, ?_⟩
  · funext y
    have hf := (h2 y).fderiv
    show fderiv ℝ (fun y => heatOp s g (torusProj y)) y (Pi.single i 1) =
      heatOp (s / 2) g' (torusProj y)
    rw [hf, ofPartials_single]
    have h3 := DFunLike.congr_fun (heatOp_compLeftContinuous (s / 2)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) V) (torusProj y)
    simpa [hg'] using h3.symm
  · refine (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg derivConst_nonneg (by positivity))
      (norm_nonneg _))).2 fun x => ?_
    rw [Real.norm_eq_abs]
    exact hbV x i

theorem sdLift_congr {φ ψ : (Fin 3 → ℝ) → ℝ} (h : φ = ψ) (i : Fin 3) :
    sdLift i φ = sdLift i ψ := by rw [h]

/-- Iterating: `∂_w P_s g = P_{s/2^m} g''` with `‖g''‖ ≤ K s^{-m/2} ‖g‖`. -/
theorem exists_sdWord_heatOp (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : List (Fin 3), w.length = m → ∀ (g : C(Torus3, ℝ)) {s : ℝ}, 0 < s →
      ∃ g'' : C(Torus3, ℝ), sdWord w (liftFn (heatOp s g)) = liftFn (heatOp (s / 2 ^ m) g'') ∧
        ‖g''‖ ≤ K * ((√s)⁻¹) ^ m * ‖g‖ := by
  induction m with
  | zero =>
    refine ⟨1, zero_le_one, fun w hw g s hs => ⟨g, ?_, by simp⟩⟩
    rw [List.length_eq_zero_iff] at hw
    subst hw
    simp [sdWord]
  | succ m ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    refine ⟨K * derivConst * 2 ^ (m + 1), by
      have := derivConst_nonneg
      positivity, fun w hw g s hs => ?_⟩
    obtain ⟨i, w, rfl⟩ : ∃ i w', w = i :: w' := by
      cases w with
      | nil => simp at hw
      | cons i w' => exact ⟨i, w', rfl⟩
    have hw' : w.length = m := by simpa using hw
    obtain ⟨g'', hg'', hn''⟩ := hK w hw' g hs
    have hs' : 0 < s / 2 ^ m := by positivity
    obtain ⟨g''', hg''', hn'''⟩ := exists_sdLift_heatOp g'' hs' i
    refine ⟨g''', ?_, ?_⟩
    · simp only [sdWord]
      rw [sdLift_congr hg'' i, hg''']
      rw [div_div, ← pow_succ]
    · refine hn'''.trans ?_
      have hsq : 0 < √s := Real.sqrt_pos.2 hs
      have h1 : (√(s / 2 ^ m / 2))⁻¹ ≤ (√s)⁻¹ * 2 ^ (m + 1) := by
        have e : s / 2 ^ m / 2 = s / 2 ^ (m + 1) := by rw [div_div, ← pow_succ]
        have h2 : √(2 ^ (m + 1)) ≤ 2 ^ (m + 1) := by
          refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
          calc (2 : ℝ) ^ (m + 1) = 2 ^ (m + 1) * 1 := (mul_one _).symm
            _ ≤ 2 ^ (m + 1) * 2 ^ (m + 1) :=
                mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) (by positivity)
            _ = (2 ^ (m + 1)) ^ 2 := by ring
        have h3 : √s / 2 ^ (m + 1) ≤ √(s / 2 ^ (m + 1)) := by
          rw [Real.sqrt_div hs.le]
          exact div_le_div_of_nonneg_left hsq.le (Real.sqrt_pos.2 (by positivity)) h2
        rw [e]
        calc (√(s / 2 ^ (m + 1)))⁻¹ ≤ (√s / 2 ^ (m + 1))⁻¹ := inv_anti₀ (by positivity) h3
          _ = (√s)⁻¹ * 2 ^ (m + 1) := by
              rw [inv_div]
              field_simp
      have hc := derivConst_nonneg
      calc derivConst * (√(s / 2 ^ m / 2))⁻¹ * ‖g''‖
          ≤ derivConst * ((√s)⁻¹ * 2 ^ (m + 1)) * (K * (√s)⁻¹ ^ m * ‖g‖) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) hn'' (norm_nonneg _) (by positivity)
        _ = K * derivConst * 2 ^ (m + 1) * (√s)⁻¹ ^ (m + 1) * ‖g‖ := by ring

theorem differentiable_lift_heatOp (g : C(Torus3, ℝ)) {s : ℝ} (hs : 0 < s) :
    Differentiable ℝ (liftFn (heatOp s g)) := by
  intro y
  obtain ⟨V, hV, -⟩ := exists_hasTorusDeriv_heatOp g hs
  exact (hV y).differentiableAt

theorem fderiv_eq_sum_sdLift (φ : (Fin 3 → ℝ) → ℝ) :
    fderiv ℝ φ = fun y => ∑ i : Fin 3, sdLift i φ y •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) := by
  funext y
  refine ContinuousLinearMap.ext fun z => ?_
  rw [clm_apply_eq_sum]
  simp [sdLift, mul_comm]

/-- **`P_s g` is smooth** for continuous `g` and `s > 0`. -/
theorem contDiff_lift_heatOp (n : ℕ) :
    ∀ (g : C(Torus3, ℝ)) {s : ℝ}, 0 < s → ContDiff ℝ n (liftFn (heatOp s g)) := by
  induction n with
  | zero =>
    intro g s hs
    exact contDiff_zero.2 ((heatOp s g).continuous.comp continuous_torusProj)
  | succ n ih =>
    intro g s hs
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hcast, contDiff_succ_iff_fderiv]
    refine ⟨differentiable_lift_heatOp g hs, fun h => absurd h (by simp), ?_⟩
    rw [fderiv_eq_sum_sdLift]
    refine ContDiff.sum fun i _ => ?_
    obtain ⟨g', hg', -⟩ := exists_sdLift_heatOp g hs i
    rw [hg']
    exact (ih g' (half_pos hs)).smul contDiff_const

theorem contDiff_lift_heatOp_infty (g : C(Torus3, ℝ)) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (liftFn (heatOp s g)) :=
  contDiff_infty.2 fun n => contDiff_lift_heatOp n g hs

end RegularityStructures.Datum

end
