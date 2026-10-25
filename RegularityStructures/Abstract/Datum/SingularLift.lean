/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Bound
public import RegularityStructures.Abstract.WeightedSingularDefs
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Abstract.Model

/-!
# The Taylor lift as a singular modelled distribution

For `F` with the derivative bounds `DerivBound η A Kc F` and a polynomial-compatible model `M`
(`M.IsPolyCompatible P`), the Taylor lift `liftOf P γ₀ F` satisfies
`M.SingularBoundOn timeZeroDist γ₀ η (liftConst N Kc * A) (timeSlab T) (liftOf P γ₀ F)` for
`T ≤ 1`, `η < 0 < γ₀ ≤ N` (`singularBoundOn_liftOf`). The constant depends only on `N` and `Kc`.
This is [Hai14, Lemma 7.5] for the lift of the free heat evolution of an initial datum.
-/

public section

open scoped ContDiff

namespace RegularityStructures.Datum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

theorem timeZeroDist_eq_sqrt {z : ParabolicSpace} (hz : 0 < z.1) :
    timeZeroDist z = Real.sqrt z.1 := by
  simp [timeZeroDist, abs_of_pos hz]

theorem singularWeight_timeZeroDist {z : ParabolicSpace} (hz : 0 < z.1) (hz1 : z.1 ≤ 1) :
    singularWeight timeZeroDist z = Real.sqrt z.1 := by
  rw [singularWeight, timeZeroDist_eq_sqrt hz]
  exact min_eq_right (Real.sqrt_le_one.2 hz1)

theorem sqrt_rpow_eq {t : ℝ} (ht : 0 ≤ t) (e : ℝ) : Real.sqrt t ^ e = t ^ (e / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]
  congr 1
  ring

theorem le_liftConst {Kc : (Fin 4 → ℕ) → ℝ} (hKc : ∀ k, 0 ≤ Kc k) (hN : 1 ≤ N) {k : Fin 4 → ℕ}
    (hk : ∀ i, k i < 2 * N) : Kc k ≤ liftConst N Kc := by
  have hmem : k ∈ box (2 * N) := mem_box.2 hk
  have h1 : Kc k ≤ ∑ k ∈ box (2 * N), Kc k :=
    Finset.single_le_sum (f := Kc) (fun k _ => hKc k) hmem
  have h0 : 0 ≤ ∑ k ∈ box (2 * N), Kc k := Finset.sum_nonneg fun k _ => hKc k
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfac : (1 : ℝ) ≤ (N : ℝ) ^ 4 + (N : ℝ) ^ 3 + (N : ℝ) ^ 2 + N + 1 := by
    have : (0 : ℝ) ≤ (N : ℝ) ^ 4 + (N : ℝ) ^ 3 + (N : ℝ) ^ 2 + N := by positivity
    linarith
  unfold liftConst
  nlinarith

theorem liftConst_nonneg {Kc : (Fin 4 → ℕ) → ℝ} (hKc : ∀ k, 0 ≤ Kc k) : 0 ≤ liftConst N Kc := by
  unfold liftConst
  have : 0 ≤ ∑ k ∈ box (2 * N), Kc k := Finset.sum_nonneg fun k _ => hKc k
  positivity

/-- **The Taylor lift is a singular modelled distribution** on the time slab (the bounds of
[Hai14, Definition 6.2] with `ρ = |t|^{1/2}`). -/
theorem singularBoundOn_liftOf {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N}
    (hM : M.IsPolyCompatible P) {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F : ParabolicSpace → ℝ}
    (hF : DerivBound η A Kc F) (hη : η < 0) (hA : 0 ≤ A) (hKc : ∀ k, 0 ≤ Kc k) {γ₀ : ℝ}
    (hγ₀ : 0 < γ₀) (hγN : γ₀ ≤ N) {T : ℝ} (hT : T ≤ 1) :
    M.SingularBoundOn timeZeroDist γ₀ η (liftConst N Kc * A) (timeSlab T) (liftOf P γ₀ F) := by
  have hN : 1 ≤ N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le hγ₀ hγN
    exact_mod_cast this
  have hC : 0 ≤ liftConst N Kc * A := mul_nonneg (liftConst_nonneg hKc) hA
  constructor
  · -- the sup bounds
    intro x hx hρ i hi
    have hx0 : 0 < x.1 := hx.1
    have hx1 : x.1 ≤ 1 := hx.2.trans hT
    rw [singularWeight_timeZeroDist hx0 hx1]
    by_cases hmem : i ∈ Set.range P.emb
    · obtain ⟨k, rfl⟩ := hmem
      rw [P.deg_emb] at hi ⊢
      rw [liftOf_apply_emb]
      have hk : polyDeg N k < γ₀ := hi
      have hco : liftCoeff N γ₀ F x k = D ⇑k.1 F x / multiFactorial ⇑k.1 := by
        simp [liftCoeff, hk]
      have hneg : η - polyDeg N k ≤ 0 := by
        have : (0 : ℝ) ≤ polyDeg N k := by rw [polyDeg_eq_wt]; exact Nat.cast_nonneg _
        linarith
      rw [min_eq_left hneg, sqrt_rpow_eq hx0.le, hco, polyDeg_eq_wt]
      have hmf := one_le_multiFactorial ⇑k.1
      have hmfpos := multiFactorial_pos ⇑k.1
      have hkb := hF.bound ⇑k.1 x hx0 hx1
      have hkN : ∀ i, (⇑k.1 : Fin 4 → ℕ) i < 2 * N := fun i => by
        have := coord_lt_of_weight_lt k.2 i
        omega
      have hKk := le_liftConst hKc hN hkN
      have hpow : 0 ≤ x.1 ^ ((η - (wt ⇑k.1 : ℝ)) / 2) := Real.rpow_nonneg hx0.le _
      calc |D ⇑k.1 F x / multiFactorial ⇑k.1| ≤ |D ⇑k.1 F x| := by
            rw [abs_div, abs_of_pos hmfpos]
            exact div_le_self (abs_nonneg _) hmf
        _ ≤ Kc ⇑k.1 * A * x.1 ^ ((η - (wt ⇑k.1 : ℝ)) / 2) := hkb
        _ ≤ liftConst N Kc * A * x.1 ^ ((η - (wt ⇑k.1 : ℝ)) / 2) := by
            gcongr
    · rw [liftOf_apply_of_notMem P γ₀ F x hmem, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  · intro x hx y hy hρx hρy hd j hj
    have hx0 : 0 < x.1 := hx.1
    have hx1 : x.1 ≤ 1 := hx.2.trans hT
    have hy0 : 0 < y.1 := hy.1
    have hy1 : y.1 ≤ 1 := hy.2.trans hT
    rw [singularWeight_timeZeroDist hx0 hx1, singularWeight_timeZeroDist hy0 hy1] at hd ⊢
    set ρ₀ : ℝ := min (Real.sqrt x.1) (Real.sqrt y.1) with hρ₀
    have hρ₀pos : 0 < ρ₀ := lt_min (Real.sqrt_pos.2 hx0) (Real.sqrt_pos.2 hy0)
    have hρx : ρ₀ ^ 2 ≤ x.1 := by
      calc ρ₀ ^ 2 ≤ Real.sqrt x.1 ^ 2 :=
            pow_le_pow_left₀ hρ₀pos.le (min_le_left _ _) 2
        _ = x.1 := Real.sq_sqrt hx0.le
    have hρy : ρ₀ ^ 2 ≤ y.1 := by
      calc ρ₀ ^ 2 ≤ Real.sqrt y.1 ^ 2 :=
            pow_le_pow_left₀ hρ₀pos.le (min_le_right _ _) 2
        _ = y.1 := Real.sq_sqrt hy0.le
    have hd' : parabolicNorm (y - x) ≤ ρ₀ := hd
    by_cases hmem : j ∈ Set.range P.emb
    · obtain ⟨l, rfl⟩ := hmem
      rw [P.deg_emb] at hj ⊢
      have hΓ : M.gammaMap y x (liftOf P γ₀ F x) =
          P.polyEmbed (polyTranslate (parabolicCoords (y - x)) (liftCoeff N γ₀ F x)) :=
        gammaMap_polyEmbed hM y x _
      have hval : (liftOf P γ₀ F y - M.gammaMap y x (liftOf P γ₀ F x)) (P.emb l) =
          liftCoeff N γ₀ F y l -
            polyTranslate (parabolicCoords (y - x)) (liftCoeff N γ₀ F x) l := by
        rw [hΓ, Pi.sub_apply]
        unfold liftOf
        rw [P.polyEmbed_apply_emb, P.polyEmbed_apply_emb]
      rw [hval]
      have h := coeff_increment_le hF hη hA hKc hγN hρ₀pos hρx hρy hx1 hy1 hd' l hj
      have hsd : (parabolicSemigroup.scaleDist y x) = parabolicNorm (y - x) := rfl
      rw [hsd]
      calc _ ≤ liftConst N Kc * A * ρ₀ ^ (η - γ₀) * parabolicNorm (y - x) ^ (γ₀ - polyDeg N l) := h
        _ = _ := by ring
    · have h0 : (liftOf P γ₀ F y - M.gammaMap y x (liftOf P γ₀ F x)) j = 0 := by
        have hmemΓ : M.gammaMap y x (liftOf P γ₀ F x) ∈ P.subspace := by
          unfold liftOf
          rw [gammaMap_polyEmbed hM y x _]
          exact P.polyEmbed_mem _
        rw [Pi.sub_apply, liftOf_apply_of_notMem P γ₀ F y hmem, hmemΓ j hmem]
        simp
      rw [h0, abs_zero]
      refine mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (parabolicNorm_nonneg _) _))
        (Real.rpow_nonneg hρ₀pos.le _)

end RegularityStructures.Datum

end
