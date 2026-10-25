/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.ModelNearAlgebra
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Chaining: from near-`1` to near-`R` `Γ`-bounds

If `Γ` satisfies the bound `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{deg i − deg j}` for pairs at parabolic
distance at most `1` of a segment-closed set `S` (`SegmentClosed`), then it satisfies the same bound
with the constant `gammaChainConst |ι| C m = max C ((|ι| max(1, C))^m)` for pairs at distance at
most `R`, where `m` is any number of chain steps with `R² ≤ m` (`GammaBoundNearOn.of_one`).  Proof:
`Γ_{yx} = Γ_{y z_{m-1}} ⋯ Γ_{z_1 x}` along the equally spaced points `z_k = x + (k/m)(y - x)`
(`gamma_mul`), each step has parabolic length `≤ √(1/m) R ≤ 1`, the entries of a product of `m`
graded unipotent maps with entries `≤ B` are `≤ (|ι| B)^m` (`GammaEntryBound.comp`), and
`d ≥ 1` for the long pairs.  The numbers of steps `m ≥ R²` cannot be improved in general to a
polynomial dependence of the constant on `C` of degree below `m`.

`SegmentClosed` holds for `hairerTimeWindow` and for `timeSlab T`.
-/

@[expose] public section

namespace RegularityStructures

/-- A subset of space-time containing the straight segment between any two of its points. -/
def SegmentClosed (S : Set ParabolicSpace) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → x + s • (y - x) ∈ S

/-- The constant of the chained near-`R` bound after `m` steps. -/
def gammaChainConst (N : ℕ) (C : ℝ) (m : ℕ) : ℝ := max C ((N * max 1 C) ^ m)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem fst_add_smul_sub (x y : ParabolicSpace) (s : ℝ) :
    (x + s • (y - x)).1 = (1 - s) * x.1 + s * y.1 := by
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  ring

theorem segmentClosed_hairerTimeWindow : SegmentClosed hairerTimeWindow := by
  intro x hx y hy s hs0 hs1
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  refine ⟨?_, ?_⟩ <;> rw [fst_add_smul_sub] <;> nlinarith

theorem segmentClosed_timeSlab (T : ℝ) : SegmentClosed (timeSlab T) := by
  intro x hx y hy s hs0 hs1
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : (1 - s) * min x.1 y.1 ≤ (1 - s) * x.1 :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
  have h2 : s * min x.1 y.1 ≤ s * y.1 := mul_le_mul_of_nonneg_left (min_le_right _ _) hs0
  have h3 : 0 < min x.1 y.1 := lt_min hx0 hy0
  refine ⟨?_, ?_⟩ <;> rw [fst_add_smul_sub] <;> nlinarith

theorem parabolicNorm_smul_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (w : ParabolicSpace) :
    parabolicNorm (s • w) ≤ Real.sqrt s * parabolicNorm w := by
  have hr0 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg _
  have hr1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 h1
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt h0
  have hs : s ≤ Real.sqrt s := by nlinarith
  unfold parabolicNorm
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg h0]
  rw [Real.sqrt_mul h0, ← Finset.mul_sum, mul_add]
  have : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable (M : Model 𝒯 parabolicSemigroup) {γ C : ℝ} {S : Set ParabolicSpace}

/-- A single step of near distance has entries bounded by `max 1 C`. -/
theorem gammaEntryBound_of_near (h : M.GammaBoundNearOn γ C 1 S) {x y : ParabolicSpace}
    (hx : x ∈ S) (hy : y ∈ S) (hd : parabolicSemigroup.scaleDist y x ≤ 1) :
    GammaEntryBound 𝒯 γ (max 1 C) (M.gammaMap y x) := by
  intro i j hi
  have hU := M.isGradedUnipotent_gammaMap y x
  by_cases hji : j = i
  · subst hji
    rw [hU.apply_single_self, abs_one]
    exact le_max_left _ _
  by_cases hlt : 𝒯.deg j < 𝒯.deg i
  · have hd0 : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg _ _
    have hp0 : 0 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
      Real.rpow_nonneg hd0 _
    have hp1 : parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) ≤ 1 :=
      Real.rpow_le_one hd0 hd (by linarith)
    refine (h i j hi hlt x hx y hy hd).trans ?_
    rcases le_total 0 C with hC | hC
    · calc C * _ ≤ C * 1 := mul_le_mul_of_nonneg_left hp1 hC
        _ ≤ max 1 C := by rw [mul_one]; exact le_max_right _ _
    · calc C * _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC hp0
        _ ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  · rw [hU.apply_single_of_le hji (not_lt.1 hlt), abs_zero]
    exact zero_le_one.trans (le_max_left _ _)

theorem gammaEntryBound_chain (hS : SegmentClosed S) (h : M.GammaBoundNearOn γ C 1 S)
    {x y : ParabolicSpace} (hx : x ∈ S) (hy : y ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (hstep : parabolicNorm ((1 / (m : ℝ)) • (y - x)) ≤ 1) :
    GammaEntryBound 𝒯 γ (((Fintype.card ι : ℝ) * max 1 C) ^ m) (M.gammaMap y x) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set z : ℕ → ParabolicSpace := fun k => x + ((k : ℝ) / m) • (y - x) with hz
  have hzmem : ∀ k : ℕ, k ≤ m → z k ∈ S := fun k hk =>
    hS x hx y hy _ (by positivity) ((div_le_one hm0).2 (by exact_mod_cast hk))
  have hB0 : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  have key : ∀ k : ℕ, k ≤ m →
      GammaEntryBound 𝒯 γ (((Fintype.card ι : ℝ) * max 1 C) ^ k) (M.gammaMap (z k) x) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : z 0 = x := by simp [hz]
      rw [this, M.gammaMap_self, pow_zero]
      exact GammaEntryBound.id
    | succ k ih =>
      intro hk
      have ih' := ih (Nat.le_of_succ_le hk)
      have hdiff : z (k + 1) - z k = (1 / (m : ℝ)) • (y - x) := by
        simp only [hz]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        push_cast
        ring
      have hstepb := M.gammaEntryBound_of_near h (hzmem k (Nat.le_of_succ_le hk))
        (hzmem (k + 1) hk) (by
          change parabolicNorm (z (k + 1) - z k) ≤ 1
          rw [hdiff]
          exact hstep)
      have hcomp : M.gammaMap (z (k + 1)) x =
          M.gammaMap (z (k + 1)) (z k) ∘ₗ M.gammaMap (z k) x :=
        (M.gammaMap_comp (z (k + 1)) (z k) x).symm
      have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      have hb0 : 0 ≤ ((Fintype.card ι : ℝ) * max 1 C) ^ k := pow_nonneg (mul_nonneg hN0 hB0) _
      have := GammaEntryBound.comp (M.isGradedUnipotent_gammaMap (z k) x) hB0 hb0 hstepb ih'
      rw [hcomp]
      have e : (Fintype.card ι : ℝ) * (((Fintype.card ι : ℝ) * max 1 C) ^ k * max 1 C) =
          ((Fintype.card ι : ℝ) * max 1 C) ^ (k + 1) := by ring
      rwa [e] at this
  have hzm : z m = y := by
    simp only [hz]
    rw [div_self hm0.ne', one_smul, add_sub_cancel]
  have := key m le_rfl
  rwa [hzm] at this

/-- **Chaining**: near-`1` bounds on a segment-closed set give near-`R` bounds, `R² ≤ m`, with the
constant `gammaChainConst |ι| C m`. -/
theorem GammaBoundNearOn.of_one (hS : SegmentClosed S) (h : M.GammaBoundNearOn γ C 1 S)
    {R : ℝ} {m : ℕ} (hm : 1 ≤ m) (hRm : R ^ 2 ≤ m) :
    M.GammaBoundNearOn γ (gammaChainConst (Fintype.card ι) C m) R S := by
  intro i j hi hj x hx y hy hd
  have hd0 : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg _ _
  have hp0 : 0 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
    Real.rpow_nonneg hd0 _
  by_cases hle : parabolicSemigroup.scaleDist y x ≤ 1
  · exact (h i j hi hj x hx y hy hle).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hp0)
  · push Not at hle
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hR : R ≤ Real.sqrt m := (le_abs_self R).trans (Real.abs_le_sqrt hRm)
    have hstep : parabolicNorm ((1 / (m : ℝ)) • (y - x)) ≤ 1 := by
      have h1 : (1 / (m : ℝ)) ≤ 1 := by
        rw [div_le_one hm0]
        exact_mod_cast hm
      refine (parabolicNorm_smul_le (by positivity) h1 _).trans ?_
      have hsq : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
      have e : Real.sqrt (1 / (m : ℝ)) = (Real.sqrt m)⁻¹ := by
        rw [one_div, Real.sqrt_inv]
      rw [e]
      have : parabolicNorm (y - x) ≤ Real.sqrt m := hd.trans hR
      calc (Real.sqrt m)⁻¹ * parabolicNorm (y - x) ≤ (Real.sqrt m)⁻¹ * Real.sqrt m :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hsq.le)
        _ = 1 := inv_mul_cancel₀ hsq.ne'
    have hchain := (M.gammaEntryBound_chain hS h hx hy hm hstep) i j hi
    have hN0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have hB0 : 0 ≤ ((Fintype.card ι : ℝ) * max 1 C) ^ m :=
      pow_nonneg (mul_nonneg hN0 (zero_le_one.trans (le_max_left _ _))) _
    have hone : 1 ≤ parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
      Real.one_le_rpow hle.le (by linarith)
    calc |M.gammaMap y x (Pi.single i 1) j| ≤ ((Fintype.card ι : ℝ) * max 1 C) ^ m := hchain
      _ ≤ ((Fintype.card ι : ℝ) * max 1 C) ^ m *
          parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) := le_mul_of_one_le_right hB0 hone
      _ ≤ gammaChainConst (Fintype.card ι) C m *
          parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hp0

/-- The near-`gammaNearRadius` bound (`16` chain steps) from the near-`1` bound. -/
theorem GammaBoundNearOn.toGammaNearOn (hS : SegmentClosed S) (h : M.GammaBoundNearOn γ C 1 S) :
    M.GammaNearOn γ (gammaChainConst (Fintype.card ι) C 16) S :=
  h.of_one M hS (m := 16) (by norm_num) (by unfold gammaNearRadius; norm_num)

end Model

end RegularityStructures

end
