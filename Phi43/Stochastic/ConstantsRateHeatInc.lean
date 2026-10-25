/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateHeatDerivLarge
public import Phi43.Stochastic.ConstantsRateLift

/-!
# Spatial increments of the lifted heat kernel

Mean-value estimates along the three coordinate directions, from the derivative bounds of
`ConstantsRateHeatDeriv` and `ConstantsRateHeatDerivLarge`.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

theorem heatLift_line_increment {F : (Fin 3 → ℝ) → ℝ} {M : ℝ} (y : Fin 3 → ℝ) (i : Fin 3)
    (a : ℝ)
    (hd : ∀ s ∈ uIcc (y i) (y i + a), ∃ d : ℝ,
      HasDerivAt (fun s' => F (Function.update y i s')) d s ∧ |d| ≤ M) :
    |F (Function.update y i (y i + a)) - F y| ≤ M * |a| := by
  classical
  let f' : ℝ → ℝ := fun s => if h : s ∈ uIcc (y i) (y i + a) then Classical.choose (hd s h) else 0
  have hf' : ∀ s ∈ uIcc (y i) (y i + a),
      HasDerivAt (fun s' => F (Function.update y i s')) (f' s) s ∧ |f' s| ≤ M := by
    intro s hs
    have := Classical.choose_spec (hd s hs)
    simpa [f', hs] using this
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s' => F (Function.update y i s')) (f' := f') (s := uIcc (y i) (y i + a))
    (C := M) (fun s hs => (hf' s hs).1.hasDerivWithinAt) (fun s hs => by
      simpa [Real.norm_eq_abs] using (hf' s hs).2) (convex_uIcc _ _)
    (left_mem_uIcc) (right_mem_uIcc)
  simpa [Real.norm_eq_abs, Function.update_eq_self] using hmain

theorem sum_abs_update_sub_le (y u : Fin 3 → ℝ) (i : Fin 3) (s : ℝ) :
    ∑ j, |Function.update u i s j - y j| ≤ ∑ j, |u j - y j| + |s - u i| := by
  fin_cases i
  · simp only [Fin.sum_univ_three, Fin.zero_eta]
    simp [Function.update]
    have := abs_sub_le (s) (u 0) (y 0)
    linarith [abs_nonneg (u 1 - y 1), abs_nonneg (u 2 - y 2), abs_nonneg (u 0 - y 0), abs_nonneg (s - u 0)]
  · simp only [Fin.sum_univ_three, Fin.mk_one]
    simp [Function.update]
    have := abs_sub_le (s) (u 1) (y 1)
    linarith [abs_nonneg (u 0 - y 0), abs_nonneg (u 2 - y 2), abs_nonneg (u 1 - y 1), abs_nonneg (s - u 1)]
  · simp only [Fin.sum_univ_three, Fin.reduceFinMk]
    simp [Function.update]
    have := abs_sub_le (s) (u 2) (y 2)
    linarith [abs_nonneg (u 0 - y 0), abs_nonneg (u 1 - y 1), abs_nonneg (u 2 - y 2), abs_nonneg (s - u 2)]

theorem heatLift_step_increment {F : (Fin 3 → ℝ) → ℝ} {M A : ℝ} (y u : Fin 3 → ℝ) (i : Fin 3)
    (ai : ℝ)
    (hd : ∀ v : Fin 3 → ℝ, ∀ j : Fin 3, ∑ l, |v l - y l| ≤ A → ∃ d : ℝ,
      HasDerivAt (fun s => F (Function.update v j s)) d (v j) ∧ |d| ≤ M)
    (hu : ∑ j, |u j - y j| + |ai| ≤ A) :
    |F (Function.update u i (u i + ai)) - F u| ≤ M * |ai| := by
  apply heatLift_line_increment
  intro s hs
  have hsd : |s - u i| ≤ |ai| := by
    rw [mem_uIcc] at hs
    rw [abs_le]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor <;> cases abs_cases ai <;> linarith
    · constructor <;> cases abs_cases ai <;> linarith
  have hsum := sum_abs_update_sub_le y u i s
  obtain ⟨d, hd1, hd2⟩ := hd (Function.update u i s) i (by linarith)
  refine ⟨d, ?_, hd2⟩
  have hfun : (fun s' => F (Function.update (Function.update u i s) i s')) =
      fun s' => F (Function.update u i s') := by
    funext s'
    rw [Function.update_idem]
  rw [hfun] at hd1
  simpa using hd1

theorem heatLift_vec_increment {F : (Fin 3 → ℝ) → ℝ} {M A : ℝ} (y a : Fin 3 → ℝ)
    (hA : ∑ j, |a j| ≤ A)
    (hd : ∀ v : Fin 3 → ℝ, ∀ j : Fin 3, ∑ l, |v l - y l| ≤ A → ∃ d : ℝ,
      HasDerivAt (fun s => F (Function.update v j s)) d (v j) ∧ |d| ≤ M) :
    |F (y + a) - F y| ≤ M * ∑ j, |a j| := by
  set u1 : Fin 3 → ℝ := Function.update y 0 (y 0 + a 0) with hu1
  set u2 : Fin 3 → ℝ := Function.update u1 1 (u1 1 + a 1) with hu2
  set u3 : Fin 3 → ℝ := Function.update u2 2 (u2 2 + a 2) with hu3
  have h3 : u3 = y + a := by
    funext j
    fin_cases j <;> simp [hu3, hu2, hu1, Function.update]
  have hsa : ∑ j, |a j| = |a 0| + |a 1| + |a 2| := by simp [Fin.sum_univ_three]
  have hn0 := abs_nonneg (a 0)
  have hn1 := abs_nonneg (a 1)
  have hn2 := abs_nonneg (a 2)
  have s0 : |F u1 - F y| ≤ M * |a 0| := by
    apply heatLift_step_increment (A := A) y y 0 (a 0) hd
    simp only [sub_self, abs_zero, Finset.sum_const_zero, zero_add]
    linarith
  have s1 : |F u2 - F u1| ≤ M * |a 1| := by
    apply heatLift_step_increment (A := A) y u1 1 (a 1) hd
    have : ∑ j, |u1 j - y j| = |a 0| := by
      simp [Fin.sum_univ_three, hu1, Function.update]
    rw [this]
    linarith
  have s2 : |F u3 - F u2| ≤ M * |a 2| := by
    apply heatLift_step_increment (A := A) y u2 2 (a 2) hd
    have : ∑ j, |u2 j - y j| = |a 0| + |a 1| := by
      simp [Fin.sum_univ_three, hu2, hu1, Function.update]
    rw [this]
    linarith
  rw [← h3, hsa]
  calc
    |F u3 - F y| = |(F u3 - F u2) + (F u2 - F u1) + (F u1 - F y)| := by ring_nf
    _ ≤ |F u3 - F u2| + |F u2 - F u1| + |F u1 - F y| := by
      refine (abs_add_le _ _).trans ?_
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ M * |a 2| + M * |a 1| + M * |a 0| := by linarith
    _ = M * (|a 0| + |a 1| + |a 2|) := by ring

theorem heatLiftNu_le_sum_abs (b : Fin 3 → ℝ) : heatLiftNu b ≤ ∑ i, |b i| := by
  obtain ⟨n, hn⟩ := exists_int_lift_centered b
  have := Phi43.constantsRate_spatialNorm_le_lift (torusProj b) n
  have h2 : ∑ i, |torusCenteredRep (torusProj b) i + (n i : ℝ)| = ∑ i, |b i| := by
    apply Finset.sum_congr rfl
    intro i _
    have := congrFun hn i
    simp only [Pi.add_apply] at this
    rw [← this]
  rw [h2] at this
  exact this

theorem heatLiftNu_lower (y v : Fin 3 → ℝ) :
    heatLiftNu y ≤ 2 * (heatLiftNu v + ∑ l, |v l - y l|) := by
  have h := torusSpatialNorm_sub_le (torusProj v) (torusProj (v - y))
  have hsub : torusProj v - torusProj (v - y) = torusProj y := by
    rw [← RegularityStructures.PDE.torusProj_sub]
    congr 1
    ring
  rw [hsub] at h
  have h2 := heatLiftNu_le_sum_abs (v - y)
  unfold heatLiftNu at h2 ⊢
  simp only [Pi.sub_apply] at h2
  linarith

theorem heatLift_increment_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ y a : Fin 3 → ℝ,
      ∑ j, |a j| ≤ (√τ + heatLiftNu y) / 8 →
      |heatKernelLift τ (y + a) - heatKernelLift τ y| ≤
        C * (∑ j, |a j|) * (√τ + heatLiftNu y) ^ (-(4 : ℝ)) := by
  obtain ⟨C₁, hC₁, hder⟩ := heatLift_space_hasDerivAt_small
  refine ⟨C₁ * (8 / 3) ^ 4, by positivity, ?_⟩
  intro τ hτ hτ1 y a hA
  have hq : 0 < √τ + heatLiftNu y := by
    have := heatLiftNu_nonneg y
    have : 0 < √τ := Real.sqrt_pos.mpr hτ
    linarith
  apply (heatLift_vec_increment (F := heatKernelLift τ) (M := C₁ * (8 / 3) ^ 4 *
    (√τ + heatLiftNu y) ^ (-(4 : ℝ))) (A := (√τ + heatLiftNu y) / 8) y a hA ?_).trans_eq
    (by ring)
  intro v j hv
  obtain ⟨d, hd1, hd2⟩ := hder τ hτ hτ1 v j
  refine ⟨d, hd1, hd2.trans ?_⟩
  have hlow := heatLiftNu_lower y v
  have hqv : (3 / 8) * (√τ + heatLiftNu y) ≤ √τ + heatLiftNu v := by
    have := Real.sqrt_nonneg τ
    linarith
  have hqv0 : 0 < (3 / 8) * (√τ + heatLiftNu y) := by positivity
  have hpow : (√τ + heatLiftNu v) ^ (-(4 : ℝ)) ≤ ((3 / 8) * (√τ + heatLiftNu y)) ^ (-(4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hqv0 hqv (by norm_num)
  have hmul : ((3 / 8) * (√τ + heatLiftNu y)) ^ (-(4 : ℝ)) =
      (8 / 3) ^ 4 * (√τ + heatLiftNu y) ^ (-(4 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hq.le]
    rw [Real.rpow_neg (by norm_num), show ((3 / 8 : ℝ) ^ (4 : ℝ)) = (3 / 8 : ℝ) ^ (4 : ℕ) by
      exact_mod_cast Real.rpow_natCast (3 / 8 : ℝ) 4]
    norm_num
  calc
    C₁ * (√τ + heatLiftNu v) ^ (-(4 : ℝ)) ≤ C₁ * (((3 / 8) * (√τ + heatLiftNu y)) ^ (-(4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow hC₁
    _ = C₁ * (8 / 3) ^ 4 * (√τ + heatLiftNu y) ^ (-(4 : ℝ)) := by rw [hmul]; ring

theorem heatLift_increment_large :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 1 / 2 ≤ τ → ∀ y a : Fin 3 → ℝ,
      |heatKernelLift τ (y + a) - heatKernelLift τ y| ≤ C * ∑ j, |a j| := by
  obtain ⟨C₁, hC₁, hder⟩ := heatLift_space_hasDerivAt_large
  refine ⟨C₁, hC₁, ?_⟩
  intro τ hτ y a
  exact heatLift_vec_increment (F := heatKernelLift τ) (M := C₁) (A := ∑ j, |a j|) y a le_rfl
    (fun v j _ => hder τ hτ v j)

theorem real_increment_of_hasDerivAt {f : ℝ → ℝ} {M : ℝ} (x z : ℝ)
    (hd : ∀ s ∈ uIcc x z, ∃ d : ℝ, HasDerivAt f d s ∧ |d| ≤ M) :
    |f z - f x| ≤ M * |z - x| := by
  classical
  let f' : ℝ → ℝ := fun s => if h : s ∈ uIcc x z then Classical.choose (hd s h) else 0
  have hf' : ∀ s ∈ uIcc x z, HasDerivAt f (f' s) s ∧ |f' s| ≤ M := by
    intro s hs
    have := Classical.choose_spec (hd s hs)
    simpa [f', hs] using this
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := uIcc x z) (C := M) (fun s hs => (hf' s hs).1.hasDerivWithinAt)
    (fun s hs => by simpa [Real.norm_eq_abs] using (hf' s hs).2) (convex_uIcc _ _)
    (left_mem_uIcc) (right_mem_uIcc)
  simpa [Real.norm_eq_abs] using hmain

theorem heatLift_time_increment_small :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ η Q : ℝ) (y : Fin 3 → ℝ), 0 < Q →
      (∀ σ ∈ uIcc τ (τ + η), 0 < σ ∧ σ ≤ 1 ∧ Q ≤ √σ + heatLiftNu y) →
      |heatKernelLift (τ + η) y - heatKernelLift τ y| ≤ C * |η| * Q ^ (-(5 : ℝ)) := by
  obtain ⟨C₁, hC₁, hder⟩ := heatLift_time_hasDerivAt_small
  refine ⟨C₁, hC₁, ?_⟩
  intro τ η Q y hQ hσ
  have h := real_increment_of_hasDerivAt (f := fun σ => heatKernelLift σ y)
    (M := C₁ * Q ^ (-(5 : ℝ))) τ (τ + η) (by
      intro s hs
      obtain ⟨h0, h1, h2⟩ := hσ s hs
      obtain ⟨d, hd1, hd2⟩ := hder s h0 h1 y
      refine ⟨d, hd1, hd2.trans ?_⟩
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hQ h2 (by norm_num)) hC₁)
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

theorem heatLift_time_increment_large :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ η : ℝ) (y : Fin 3 → ℝ),
      (∀ σ ∈ uIcc τ (τ + η), 1 / 2 ≤ σ) →
      |heatKernelLift (τ + η) y - heatKernelLift τ y| ≤ C * |η| := by
  obtain ⟨C₁, hC₁, hder⟩ := heatLift_time_hasDerivAt_large
  refine ⟨C₁, hC₁, ?_⟩
  intro τ η y hσ
  have h := real_increment_of_hasDerivAt (f := fun σ => heatKernelLift σ y)
    (M := C₁) τ (τ + η) (fun s hs => hder s (hσ s hs) y)
  simpa using h

end RegularityStructures

end
