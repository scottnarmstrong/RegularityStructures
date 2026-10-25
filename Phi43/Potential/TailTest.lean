/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.TailTheta
public import RegularityStructures.Abstract.Singular.Remainder.Decay
public import RegularityStructures.Abstract.Singular.ModelPairing.Single

/-!
# The pieces of a spatially decaying kernel as scaled test functions

`IsTailKernel Φ B`: `Φ` is smooth, vanishes for lags outside `(0, 1/4)`, and its derivatives of
order `≤ 4` decay like `B (1 + |x|²)^{-3}` (`RemDecay`-type bound).  Multiplying `Φ(z - ·)` by the cell
`bump3 (8 y₂ - k)` of the spatial partition of unity gives a test function scaled at
`z_k = (z₀, (k+1)/8)` with radius `1` and constant `tailConst B z k = 432 B M_θ latRem z₂ k`
(`isScaledTest_tail`); these constants are summable in `k`.
-/

open scoped ContDiff

public section

open Set

namespace RegularityStructures.Potential

/-- A smooth kernel of lag in `(0, 1/4)` with decaying derivatives. -/
structure IsTailKernel (Φ : ParabolicSpace → ℝ) (B : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ Φ
  pos : 0 < B
  lag : ∀ w : ParabolicSpace, w.1 ≤ 0 ∨ 1 / 4 ≤ w.1 → Φ w = 0
  decay : ∀ i ≤ 4, ∀ w : ParabolicSpace, w.1 ≤ 1 / 4 →
    ‖iteratedFDeriv ℝ i Φ w‖ ≤ B * remWt w.2

/-- The base point `z_k = (z₀, (k + 1)/8)` of the `k`-th cell. -/
@[expose] noncomputable def tailBase (z : ParabolicSpace) (k : Fin 3 → ℤ) : ParabolicSpace :=
  (z.1, fun i => ((k i : ℝ) + 1) / 8)

/-- The constant of the `k`-th piece. -/
@[expose] noncomputable def tailConst (B : ℝ) (z : ParabolicSpace) (k : Fin 3 → ℤ) : ℝ :=
  432 * B * potThetaConst * latRem z.2 k

theorem lat1_pos (a : ℝ) (m : ℤ) : 0 < lat1 a m := by unfold lat1; positivity

theorem latRem_pos (a : Fin 3 → ℝ) (k : Fin 3 → ℤ) : 0 < latRem a k :=
  Finset.prod_pos fun _ _ => lat1_pos _ _

theorem tailConst_pos {B : ℝ} (hB : 0 < B) (z : ParabolicSpace) (k : Fin 3 → ℤ) :
    0 < tailConst B z k := by
  unfold tailConst
  have := potThetaConst_pos
  have := latRem_pos z.2 k
  positivity

theorem remWt_le_latRem (a : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    remWt (fun i => a i - ((k i : ℝ) + 1) / 8) ≤ latRem a k := by
  unfold remWt latRem lat1
  exact inv_one_add_sqNorm3_pow_le _

/-- Peetre's inequality for the weight `remWt`, for shifts in the cube of radius `1/8`. -/
theorem remWt_sub_le (a v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ 1 / 8) :
    remWt (a - v) ≤ 27 * remWt a := by
  have h1 : sqNorm3 a ≤ 2 * sqNorm3 (a - v) + 2 * sqNorm3 v := by
    unfold sqNorm3
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (a i - v i + v i), sq_nonneg (a i - 2 * v i)]
  have h2 : sqNorm3 v ≤ 3 / 64 := by
    unfold sqNorm3
    calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin 3, (1 / 8 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have := sq_le_sq' (abs_le.1 (hv i)).1 (abs_le.1 (hv i)).2
            simpa using this
      _ = 3 / 64 := by simp; norm_num
  have h3 : 1 + sqNorm3 a ≤ 3 * (1 + sqNorm3 (a - v)) := by
    have := sqNorm3_nonneg (a - v)
    nlinarith
  unfold remWt
  have h4 : (1 + sqNorm3 (a - v))⁻¹ ≤ 3 * (1 + sqNorm3 a)⁻¹ := by
    have hp : 0 < 1 + sqNorm3 a := by have := sqNorm3_nonneg a; linarith
    have hq : 0 < 1 + sqNorm3 (a - v) := by have := sqNorm3_nonneg (a - v); linarith
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ hq hp]
    nlinarith
  have hq0 : 0 ≤ (1 + sqNorm3 (a - v))⁻¹ :=
    inv_nonneg.2 (by have := sqNorm3_nonneg (a - v); linarith)
  calc (1 + sqNorm3 (a - v))⁻¹ ^ 3 ≤ (3 * (1 + sqNorm3 a)⁻¹) ^ 3 :=
        pow_le_pow_left₀ hq0 h4 3
    _ = 27 * (1 + sqNorm3 a)⁻¹ ^ 3 := by ring

theorem IsTailKernel.norm_iteratedFDeriv_le {Φ : ParabolicSpace → ℝ} {B : ℝ}
    (hΦ : IsTailKernel Φ B) {i : ℕ} (hi : i ≤ 4) (w : ParabolicSpace) :
    ‖iteratedFDeriv ℝ i Φ w‖ ≤ B * remWt w.2 := by
  by_cases hw : w.1 ≤ 1 / 4
  · exact hΦ.decay i hi w hw
  · have hs : tsupport Φ ⊆ {w : ParabolicSpace | w.1 ≤ 1 / 4} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_fst continuous_const)
      by_contra hc
      exact hx (hΦ.lag x (Or.inr (not_le.1 hc).le))
    have : iteratedFDeriv ℝ i Φ w = 0 := by
      by_contra hne
      exact hw (hs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := i) hne))
    rw [this, norm_zero]
    have := remWt_nonneg w.2
    have := hΦ.pos
    positivity

theorem norm_iteratedFDeriv_reflect_le {Φ : ParabolicSpace → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (a : ParabolicSpace) (j : ℕ) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ j (fun v => Φ (a - v)) v‖ ≤ ‖iteratedFDeriv ℝ j Φ (a - v)‖ := by
  have hf : ContDiff ℝ ∞ (fun u => Φ (a + u)) := hΦ.comp (contDiff_const.add contDiff_id)
  have e : (fun v => Φ (a - v)) =
      (fun u => Φ (a + u)) ∘ (-(ContinuousLinearMap.id ℝ ParabolicSpace)) := by
    funext v; simp [sub_eq_add_neg]
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right (n := j)
    (-(ContinuousLinearMap.id ℝ ParabolicSpace)) (hf.of_le (by exact_mod_cast le_top)) v
    (by exact_mod_cast le_refl j)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖(-(ContinuousLinearMap.id ℝ ParabolicSpace))‖ ≤ 1 := by
    rw [norm_neg]; exact ContinuousLinearMap.norm_id_le
  have hp : ∏ _i : Fin j, ‖(-(ContinuousLinearMap.id ℝ ParabolicSpace))‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hL
  have hd : iteratedFDeriv ℝ j (fun u => Φ (a + u)) ((-(ContinuousLinearMap.id ℝ ParabolicSpace)) v)
      = iteratedFDeriv ℝ j Φ (a - v) := by
    rw [iteratedFDeriv_comp_add_left]
    simp [sub_eq_add_neg]
  rw [hd] at *
  calc _ ≤ ‖iteratedFDeriv ℝ j Φ (a - v)‖ * 1 := by gcongr
    _ = _ := mul_one _

/-- The `k`-th piece `Φ(z - y) · bump3 (8 y₂ - k)`. -/
@[expose] noncomputable def tailPiece (Φ : ParabolicSpace → ℝ) (z : ParabolicSpace)
    (k : Fin 3 → ℤ) (y : ParabolicSpace) : ℝ :=
  Φ (z - y) * bump3 (fun i => 8 * y.2 i - k i)

theorem tailPiece_scaled (Φ : ParabolicSpace → ℝ) (z : ParabolicSpace) (k : Fin 3 → ℤ) :
    (fun v => tailPiece Φ z k (tailBase z k + parabolicDilate 1 v)) =
      fun v => Φ ((z - tailBase z k) - v) * potTheta v := by
  funext v
  have e1 : z - (tailBase z k + parabolicDilate 1 v) = (z - tailBase z k) - v := by
    simp [parabolicDilate]; abel
  have e2 : (fun i => 8 * (tailBase z k + parabolicDilate 1 v).2 i - k i) =
      fun i => 8 * v.2 i + 1 := by
    funext i
    simp [tailBase, parabolicDilate]
    ring
  simp only [tailPiece, e1, e2, potTheta]

theorem tailPiece_eq_zero {Φ : ParabolicSpace → ℝ} {B : ℝ} (hΦ : IsTailKernel Φ B)
    (z : ParabolicSpace) (k : Fin 3 → ℤ) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm (w - tailBase z k)) : tailPiece Φ z k w = 0 := by
  by_contra hne
  rw [tailPiece] at hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
  have hlag : 0 < z.1 - w.1 ∧ z.1 - w.1 < 1 / 4 := by
    by_contra hc
    apply h1
    refine hΦ.lag _ ?_
    simp only [Prod.fst_sub]
    by_cases h : 0 < z.1 - w.1
    · right; exact (not_and.1 hc h) |> not_lt.1
    · left; exact not_lt.1 h
  have hb := bump3_ne_zero h2
  have hsp : ∀ i, |w.2 i - ((k i : ℝ) + 1) / 8| < 1 / 8 := fun i => by
    obtain ⟨a1, a2⟩ := hb i
    rw [abs_lt]; constructor <;> linarith
  have ht : Real.sqrt |w.1 - z.1| < 1 / 2 := by
    have : |w.1 - z.1| < 1 / 4 := by
      rw [abs_sub_comm, abs_of_pos hlag.1]; exact hlag.2
    calc Real.sqrt |w.1 - z.1| < Real.sqrt (1 / 4) := Real.sqrt_lt_sqrt (abs_nonneg _) this
      _ = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
  have hs : ∑ i, |(w - tailBase z k).2 i| ≤ 3 / 8 := by
    calc ∑ i, |(w - tailBase z k).2 i| ≤ ∑ _i : Fin 3, (1 / 8 : ℝ) :=
          Finset.sum_le_sum fun i _ => by
            simp only [Prod.snd_sub, Pi.sub_apply, tailBase]
            exact (hsp i).le
      _ = 3 / 8 := by simp; norm_num
  unfold parabolicNorm at hw
  simp only [Prod.fst_sub, tailBase] at hw ht hs
  linarith

theorem isScaledTest_tail {Φ : ParabolicSpace → ℝ} {B : ℝ} (hΦ : IsTailKernel Φ B)
    (z : ParabolicSpace) (k : Fin 3 → ℤ) :
    IsScaledTest (tailPiece Φ z k) (tailBase z k) 1 (tailConst B z k) where
  contDiff := ((hΦ.smooth.comp (contDiff_const.sub contDiff_id)).mul
    (contDiff_bump3.comp (contDiff_pi.2 fun i =>
      (contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp contDiff_snd)).sub contDiff_const))).of_le
    (by exact_mod_cast le_top)
  radius_pos := one_pos
  radius_le_one := le_rfl
  const_pos := tailConst_pos hΦ.pos z k
  supp w hw := tailPiece_eq_zero hΦ z k hw
  deriv j hj v := by
    rw [tailPiece_scaled]
    set a : ParabolicSpace := z - tailBase z k with ha
    have hf : ContDiff ℝ ∞ (fun v : ParabolicSpace => Φ (a - v)) :=
      hΦ.smooth.comp (contDiff_const.sub contDiff_id)
    refine (_root_.norm_iteratedFDeriv_mul_le (N := j) (hf.of_le (by exact_mod_cast le_top))
      (contDiff_potTheta.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl j)).trans ?_
    have hA : 0 ≤ tailConst B z k := (tailConst_pos hΦ.pos z k).le
    by_cases hv : ∀ i : Fin 3, |v.2 i| ≤ 1 / 8
    · have hrem : remWt (a.2 - v.2) ≤ 27 * latRem z.2 k := by
        refine (remWt_sub_le a.2 v.2 hv).trans ?_
        have : remWt a.2 ≤ latRem z.2 k := by
          have h5 := remWt_le_latRem z.2 k
          have e : a.2 = fun i => z.2 i - ((k i : ℝ) + 1) / 8 := by
            funext i; simp [ha, tailBase]
          rwa [e]
        linarith
      have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun v : ParabolicSpace => Φ (a - v)) v‖ *
          ‖iteratedFDeriv ℝ (j - i) potTheta v‖ ≤
          j.choose i * (B * (27 * latRem z.2 k) * potThetaConst) := by
        intro i hi
        have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 : ‖iteratedFDeriv ℝ i (fun v : ParabolicSpace => Φ (a - v)) v‖ ≤
            B * (27 * latRem z.2 k) :=
          (norm_iteratedFDeriv_reflect_le hΦ.smooth a i v).trans
            ((hΦ.norm_iteratedFDeriv_le (hi'.trans hj) (a - v)).trans
              (mul_le_mul_of_nonneg_left (by simpa using hrem) hΦ.pos.le))
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul h1
          (norm_iteratedFDeriv_potTheta_le (by omega) v) (norm_nonneg _) ?_) (Nat.cast_nonneg _)
        have := latRem_pos z.2 k
        have := hΦ.pos
        positivity
      refine (Finset.sum_le_sum hb).trans ?_
      rw [← Finset.sum_mul]
      have h2 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [h2]
      have h3 : (2 : ℝ) ^ j ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hj
      have hp : 0 ≤ B * (27 * latRem z.2 k) * potThetaConst := by
        have := latRem_pos z.2 k
        have := hΦ.pos
        have := potThetaConst_pos
        positivity
      unfold tailConst
      nlinarith
    · push Not at hv
      obtain ⟨i₀, hi₀⟩ := hv
      have : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun v : ParabolicSpace => Φ (a - v)) v‖ *
          ‖iteratedFDeriv ℝ (j - i) potTheta v‖ = 0 := by
        intro i _
        rw [iteratedFDeriv_potTheta_eq_zero _ hi₀]; simp
      rw [Finset.sum_eq_zero this]
      exact hA

end RegularityStructures.Potential

end
