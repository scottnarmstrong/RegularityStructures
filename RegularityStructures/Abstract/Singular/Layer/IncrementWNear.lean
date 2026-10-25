/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.PairWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.LatticeApprox.TelescopeW
public import RegularityStructures.Abstract.Singular.Layer.BoxSums
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Increment bound for the layer approximations, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, for `φ^λ_x` vanishing after time `T` and
`32 · 2^{-n} ≤ λ`, the lattice approximations of `f` against `φ^λ_x` at levels `n + 1` and `n`
differ by at most `C K₀ C_f (λ^{-(γ'−η)⁺} 2^{-nγ'} + λ^{-2} 2^{-n(2+α∧η)})`, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

open scoped ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_abs_layerApprox_succ_sub_le_win_near (𝒯 : RegularityStructure ι) (γ γ' η : ℝ)
    (hγ' : γ' ≤ γ) (hγ'η : γ' < η + 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
      {α Cf CPi CGam T : ℝ}, LayerSettingWNear M f γ η α Cf CPi CGam T →
      ∀ {φ : ParabolicSpace → ℝ}, φ ∈ testFunctionClass 4 → ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 →
      ∀ {x : ParabolicSpace},
      (∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ lam x w = 0) → ∀ {n : ℕ},
      32 * ((2 : ℝ) ^ n)⁻¹ ≤ lam →
      |M.latticeApprox f (rescaledTestFunction φ lam x) (n + 1) -
          M.latticeApprox f (rescaledTestFunction φ lam x) n| ≤
        C * (max 1 CGam * CPi) * Cf *
          (lam ^ (-(max (-(η - γ')) 0)) * (((2 : ℝ) ^ n)⁻¹) ^ γ' +
            lam ^ (-2 : ℝ) * (((2 : ℝ) ^ n)⁻¹) ^ (2 + min α η)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hpair⟩ := Layer.exists_abs_pairing_pair_le_win_near 𝒯 γ γ' hγ'
  set θ : ℝ := max (-(η - γ')) 0 with hθ_def
  have hθ0 : 0 ≤ θ := le_max_right _ _
  have hθ2 : θ < 2 := max_lt (by linarith) two_pos
  set κ : ℝ := 11 * (2 : ℝ) ^ θ * (1 + (2 : ℝ) ^ θ / (1 - θ / 2)) with hκ_def
  have hκ : 0 ≤ κ := by
    have : 0 < 1 - θ / 2 := by linarith
    positivity
  refine ⟨5097040 * (125 * κ * C₁ + 1730 * 125 * C₂), by positivity, ?_⟩
  intro M f α Cf CPi CGam T S φ hφ lam hlam hlam1 x hφT n hn
  set r : ℝ := ((2 : ℝ) ^ n)⁻¹ with hr_def
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr : 0 < r := by positivity
  have hΛ : 32 ≤ lam * 2 ^ n := by
    have : 32 * r * 2 ^ n ≤ lam * 2 ^ n := mul_le_mul_of_nonneg_right hn h2.le
    have e : 32 * r * 2  ^ n = 32 := by rw [hr_def]; field_simp
    linarith
  have hr32 : r ≤ 1 / 32 := by linarith
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    have h2' : (2 : ℝ) ^ n ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (1 : ℝ) / 4 ≤ r := by
      rw [hr_def, one_div]; exact inv_anti₀ (by positivity) (by linarith)
    linarith
  have hψ0 : ∀ w, lam < parabolicNorm (w - x) → rescaledTestFunction φ lam x w = 0 :=
    fun w hw => rescaledTestFunction_eq_zero hφ.2.1 hlam hw
  have hψ : ContDiff ℝ ∞ (rescaledTestFunction φ lam x) := contDiff_rescaledTestFunction hφ.1 lam x
  have tele := M.latticeApprox_succ_sub_eq_win hψ S.hfT S.hgrowth S.hdeg hn3
    (s' := latticeBox (n + 1) x ((lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)
      (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹))
    (s := latticeBox n x ((lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2) (lam + 8 * ((2 : ℝ) ^ n)⁻¹))
    (fun k w h => Layer.mem_latticeBox_of_support hψ0 (n + 1) k w h)
    (fun k w h => Layer.mem_latticeBox_of_support hψ0 n k w h)
  rw [tele]
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hCf := S.hCf
  have hlam5 : 0 ≤ (lam ^ 5)⁻¹ := by positivity
  set c₁ : ℝ := C₁ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * r ^ (5 + γ') with hc₁
  set c₂ : ℝ := C₂ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * r ^ (5 + min α η) with hc₂
  have hc₁0 : 0 ≤ c₁ := by
    have := Real.rpow_nonneg hr.le (5 + γ'); positivity
  have hc₂0 : 0 ≤ c₂ := by
    have := Real.rpow_nonneg hr.le (5 + min α η); positivity
  set s' := latticeBox (n + 1) x ((lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)
    (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) with hs'_def
  set s := latticeBox n x ((lam + 8 * ((2 : ℝ) ^ n)⁻¹) ^ 2) (lam + 8 * ((2 : ℝ) ^ n)⁻¹) with hs_def
  set NB : Finset LatticeIndex := latticeBox (n + 1) ((72 * r ^ 2, x.2) : ParabolicSpace)
    (216 * r ^ 2) (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) with hNB_def
  set Lb : LatticeIndex → Finset LatticeIndex := fun k =>
    latticeBox n (latticePoint (n + 1) k) (144 * r ^ 2) (12 * r) with hLb_def
  set A1 : LatticeIndex → ℝ := fun k =>
    if 0 < (latticePoint (n + 1) k).1 then c₁ * Layer.weightBound θ (n + 1) k.1 else 0 with hA1_def
  set A2 : LatticeIndex → ℝ := fun k => if k ∈ NB then c₂ else 0 with hA2_def
  have hA1 : ∀ k, 0 ≤ A1 k := fun k => by
    rw [hA1_def]; dsimp only; split_ifs
    · exact mul_nonneg hc₁0 (Layer.weightBound_nonneg _ _ _)
    · exact le_rfl
  have hA2 : ∀ k, 0 ≤ A2 k := fun k => by
    rw [hA2_def]; dsimp only; split_ifs
    · exact hc₂0
    · exact le_rfl
  have hpairs : ∀ k l, |parabolicSemigroup.pairing (M.regPi (latticePoint (n + 1) k)
        (f (latticePoint (n + 1) k) - M.gammaMap (latticePoint (n + 1) k) (latticePoint n l)
          (f (latticePoint n l))))
        (fun w => rescaledTestFunction φ lam x w * latticeCell (n + 1) k w *
          latticeCell n l w)| ≤ if l ∈ Lb k then A1 k + A2 k else 0 :=
    fun k l => hpair S hφ hlam hlam1 hφT hn k l
  have hL : ∀ k, ((Lb k).card : ℝ) ≤ 5097040 := fun k => Layer.card_latticeBox_pair_le n _
  have hsum1 : ∑ k ∈ s', A1 k ≤ 125 * (lam * 2 ^ n) ^ 3 *
      (c₁ * (κ * (lam * 2 ^ n) ^ 2 * lam ^ (-θ))) :=
    Layer.sum_regular_le hθ0 hθ2 hlam hlam1 hΛ x hc₁0
  have hsum2 : ∑ k ∈ s', A2 k ≤ 1730 * (125 * (lam * 2 ^ n) ^ 3) * c₂ := by
    refine (Layer.sum_ite_mem_le s' NB hc₂0).trans ?_
    exact mul_le_mul_of_nonneg_right (Layer.card_latticeBox_near_succ_le hlam hΛ _) hc₂0
  have hmain : |∑ k ∈ s', ∑ l ∈ s, parabolicSemigroup.pairing
        (M.regPi (latticePoint (n + 1) k) (f (latticePoint (n + 1) k) -
          M.gammaMap (latticePoint (n + 1) k) (latticePoint n l) (f (latticePoint n l))))
        (fun w => rescaledTestFunction φ lam x w * latticeCell (n + 1) k w *
          latticeCell n l w)| ≤ 5097040 * (∑ k ∈ s', A1 k + ∑ k ∈ s', A2 k) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpairs k l).trans ?_
    rw [← Finset.sum_add_distrib]
    exact Layer.sum_sum_ite_le Lb (fun k => A1 k + A2 k) (fun k => add_nonneg (hA1 k) (hA2 k)) hL
  refine hmain.trans ?_
  have e1 : 125 * (lam * 2 ^ n) ^ 3 * (c₁ * (κ * (lam * 2 ^ n) ^ 2 * lam ^ (-θ))) =
      125 * κ * C₁ * (max 1 CGam * CPi) * Cf * (lam ^ (-θ) * r ^ γ') := by
    have := Layer.alg_regular (n := n) hlam γ'
    calc _ = 125 * κ * C₁ * (max 1 CGam * CPi) * Cf * lam ^ (-θ) *
          ((lam ^ 5)⁻¹ * r ^ (5 + γ') * (lam * 2 ^ n) ^ 5) := by rw [hc₁]; ring
      _ = _ := by rw [this]; ring
  have e2 : 1730 * (125 * (lam * 2 ^ n) ^ 3) * c₂ =
      1730 * 125 * C₂ * (max 1 CGam * CPi) * Cf * (lam ^ (-2 : ℝ) * r ^ (2 + min α η)) := by
    have := Layer.alg_near (n := n) hlam (min α η)
    calc _ = 1730 * 125 * C₂ * (max 1 CGam * CPi) * Cf *
          ((lam ^ 5)⁻¹ * r ^ (5 + min α η) * (lam * 2 ^ n) ^ 3) := by rw [hc₂]; ring
      _ = _ := by rw [this]
  calc 5097040 * (∑ k ∈ s', A1 k + ∑ k ∈ s', A2 k)
      ≤ 5097040 * (125 * κ * C₁ * (max 1 CGam * CPi) * Cf * (lam ^ (-θ) * r ^ γ') +
        1730 * 125 * C₂ * (max 1 CGam * CPi) * Cf * (lam ^ (-2 : ℝ) * r ^ (2 + min α η))) := by
        rw [← e1, ← e2]; gcongr
    _ ≤ _ := by
        have hT1 : 0 ≤ lam ^ (-θ) * r ^ γ' :=
          mul_nonneg (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg hr.le _)
        have hT2 : 0 ≤ lam ^ (-2 : ℝ) * r ^ (2 + min α η) :=
          mul_nonneg (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg hr.le _)
        have hP : 0 ≤ (max 1 CGam * CPi) * Cf := mul_nonneg hK0 hCf
        have ha : 0 ≤ 125 * κ * C₁ := by positivity
        have hb : 0 ≤ 1730 * 125 * C₂ := by positivity
        have h1 := mul_nonneg (mul_nonneg ha hP) hT2
        have h2 := mul_nonneg (mul_nonneg hb hP) hT1
        linarith [h1, h2]

end RegularityStructures

end
