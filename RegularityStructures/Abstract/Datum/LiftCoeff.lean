/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Lift

/-!
# The translated Taylor polynomial

`Γ_h` acts on the coefficients of the Taylor polynomial of `F` at `x` by the translation
`polyTranslate h`. Its `l`-th coefficient is the Taylor polynomial, of parabolic degree
`< γ₀ - |l|_𝔰`, of `D^l F` at `x` evaluated at `h`, divided by `l!`
(`polyTranslate_liftCoeff`). Together with the Taylor expansion of `D^l F`, this identifies the
increment `f(y) - Γ_{yx} f(x)` of the lift with a Taylor remainder.
-/

public section

open scoped ContDiff

namespace RegularityStructures.Datum

variable {N : ℕ}

theorem prod_choose_div_multiFactorial (l m : Fin 4 → ℕ) :
    (∏ i, (((l i + m i).choose (l i) : ℕ) : ℝ)) / multiFactorial (l + m) =
      1 / (multiFactorial l * multiFactorial m) := by
  unfold multiFactorial
  rw [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib, one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, ← one_div]
  exact choose_div_factorial (l i) (m i)

theorem polyTranslate_liftCoeff {F : ParabolicSpace → ℝ} (hF : SmoothPos F) {γ₀ : ℝ}
    (hγ : γ₀ ≤ N) (h : Fin 4 → ℝ) (x : ParabolicSpace) (l : PolyIndex N) :
    polyTranslate h (liftCoeff N γ₀ F x) l =
      ∑ m ∈ taylorIdx N (γ₀ - (wt ⇑l.1 : ℝ)),
        D m (D ⇑l.1 F) x * (∏ i, h i ^ m i) / (multiFactorial m * multiFactorial ⇑l.1) := by
  set g : (Fin 4 → ℕ) → ℝ := fun a =>
    (if (wt a : ℝ) < γ₀ then D a F x / multiFactorial a else 0) *
      (if ∀ i, l.1 i ≤ a i then ∏ i, h i ^ (a i - l.1 i) * (((a i).choose (l.1 i) : ℕ) : ℝ)
        else 0) with hg
  have step1 : polyTranslate h (liftCoeff N γ₀ F x) l = ∑ k : PolyIndex N, g ⇑k.1 := by
    have hσ : liftCoeff N γ₀ F x =
        ∑ k, liftCoeff N γ₀ F x k • (Pi.single k 1 : PolyIndex N → ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hσ]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      polyTranslate_single_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, liftCoeff, polyDeg_eq_wt, Finsupp.le_def]
  rw [step1, sum_polyIndex g]
  -- reindex `a = l + m`
  have hinj : Function.Injective fun m : Fin 4 → ℕ => (⇑l.1 : Fin 4 → ℕ) + m :=
    fun a b hab => add_left_cancel hab
  have step2 : ∑ m ∈ taylorIdx N (γ₀ - (wt ⇑l.1 : ℝ)),
        D m (D ⇑l.1 F) x * (∏ i, h i ^ m i) / (multiFactorial m * multiFactorial ⇑l.1) =
      ∑ m ∈ taylorIdx N (γ₀ - (wt ⇑l.1 : ℝ)), g (⇑l.1 + m) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [mem_taylorIdx] at hm
    have hw : ((wt (⇑l.1 + m) : ℕ) : ℝ) < γ₀ := by
      rw [wt_add]
      push_cast
      linarith [hm.2]
    have hle : ∀ i, l.1 i ≤ l.1 i + m i := fun i => Nat.le_add_right _ _
    simp only [hg, Pi.add_apply, hw, hle, implies_true, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [← D_add hF m ⇑l.1, add_comm m ⇑l.1, Finset.prod_mul_distrib]
    have hc := prod_choose_div_multiFactorial ⇑l.1 m
    have hl : multiFactorial ⇑l.1 ≠ 0 := (multiFactorial_pos _).ne'
    have hm0 : multiFactorial m ≠ 0 := (multiFactorial_pos _).ne'
    rw [show D (⇑l.1 + m) F x / multiFactorial (⇑l.1 + m) *
        ((∏ i, h i ^ m i) * ∏ i, (((l.1 i + m i).choose (l.1 i) : ℕ) : ℝ)) =
      D (⇑l.1 + m) F x * (∏ i, h i ^ m i) *
        ((∏ i, (((l.1 i + m i).choose (l.1 i) : ℕ) : ℝ)) / multiFactorial (⇑l.1 + m)) by ring,
      hc]
    field_simp
  rw [step2, ← Finset.sum_image (f := g) (fun a _ b _ h => hinj h)]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨m, hm, rfl⟩ := ha
    rw [mem_taylorIdx] at hm ⊢
    have hw : ((wt (⇑l.1 + m) : ℕ) : ℝ) < γ₀ := by
      rw [wt_add]
      push_cast
      linarith [hm.2]
    refine ⟨fun i => ?_, ?_⟩
    · have h1 := coord_le_wt (⇑l.1 + m) i
      have : ((wt (⇑l.1 + m) : ℕ) : ℝ) < N := lt_of_lt_of_le hw hγ
      have h2 : wt (⇑l.1 + m) < N := by exact_mod_cast this
      omega
    · exact lt_of_lt_of_le hw hγ
  · intro a ha hna
    rw [mem_taylorIdx] at ha
    by_cases hle : ∀ i, l.1 i ≤ a i
    · by_cases hw : (wt a : ℝ) < γ₀
      · exfalso
        apply hna
        rw [Finset.mem_image]
        refine ⟨fun i => a i - l.1 i, ?_, ?_⟩
        · rw [mem_taylorIdx]
          refine ⟨fun i => lt_of_le_of_lt (Nat.sub_le _ _) (ha.1 i), ?_⟩
          have : wt a = wt ⇑l.1 + wt (fun i => a i - l.1 i) := by
            unfold wt
            have h0 := hle 0
            have h1 := hle 1
            have h2 := hle 2
            have h3 := hle 3
            simp only
            omega
          rw [this] at hw
          push_cast at hw
          linarith
        · funext i
          simp [Nat.add_sub_cancel' (hle i)]
      · simp [hg, hw]
    · simp [hg, hle]

end RegularityStructures.Datum

end
