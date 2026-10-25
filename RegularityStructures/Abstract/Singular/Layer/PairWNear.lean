/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.NearWNear
public import RegularityStructures.Abstract.Singular.Layer.RegularWNear
public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Layer.SupBoundWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Layer.Pair
public import RegularityStructures.Abstract.Singular.Layer.Setting
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Cell-pair bound for the layer increments, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, a bound on the pairing of
`Π_{x_k}(f(x_k) − Γ_{x_k x_l} f(x_l))`, for a lattice point `x_k` of level `n + 1` and a
neighbouring lattice point `x_l` of level `n`, with `φ^λ_x` cut off by the two lattice cells, for
`32 · 2^{-n} ≤ λ` and `φ^λ_x` vanishing after time `T`: a weighted regular term of order
`λ^{-5} 2^{-n(5+γ')}` plus a term of order `λ^{-5} 2^{-n(5+α∧η)}` near time zero, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures.Layer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_abs_pairing_pair_le_win_near (𝒯 : RegularityStructure ι) (γ γ' : ℝ) (hγ' : γ' ≤ γ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {M : Model 𝒯 parabolicSemigroup}
      {f : ParabolicSpace → ι → ℝ} {η α Cf CPi CGam T : ℝ},
      LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {φ : ParabolicSpace → ℝ},
      φ ∈ testFunctionClass 4 → ∀ {lam : ℝ}, 0 < lam → lam ≤ 1 → ∀ {x : ParabolicSpace},
      (∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ lam x w = 0) → ∀ {n : ℕ},
      32 * ((2 : ℝ) ^ n)⁻¹ ≤ lam → ∀ k l : LatticeIndex,
      |parabolicSemigroup.pairing (M.regPi (latticePoint (n + 1) k)
        (f (latticePoint (n + 1) k) - M.gammaMap (latticePoint (n + 1) k) (latticePoint n l)
          (f (latticePoint n l))))
        (fun w => rescaledTestFunction φ lam x w * latticeCell (n + 1) k w *
          latticeCell n l w)| ≤
        if l ∈ latticeBox n (latticePoint (n + 1) k) (144 * (((2 : ℝ) ^ n)⁻¹) ^ 2)
            (12 * ((2 : ℝ) ^ n)⁻¹) then
          (if 0 < (latticePoint (n + 1) k).1 then
            C₁ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * (((2 : ℝ) ^ n)⁻¹) ^ (5 + γ') *
              weightBound (max (-(η - γ')) 0) (n + 1) k.1 else 0) +
          (if k ∈ latticeBox (n + 1) ((72 * (((2 : ℝ) ^ n)⁻¹) ^ 2, x.2) : ParabolicSpace)
              (216 * (((2 : ℝ) ^ n)⁻¹) ^ 2) (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) then
            C₂ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * (((2 : ℝ) ^ n)⁻¹) ^ (5 + min α η)
          else 0)
        else 0 := by
  obtain ⟨C₀, hC₀, hnear⟩ := exists_abs_pairing_near_le_win_near 𝒯 γ
  obtain ⟨Cr, hCr, hreg⟩ := exists_abs_pairing_regular_le_win_near 𝒯 γ γ' hγ'
  obtain ⟨C₃, hC₃, h3b⟩ := exists_isScaledTest_rescaledTestFunction_mul_latticeCell_mul
  refine ⟨Cr * C₃, C₀ * C₃, by positivity, by positivity, ?_⟩
  intro M f η α Cf CPi CGam T S φ hφ lam hlam hlam1 x hφT n hn k l
  set r : ℝ := ((2 : ℝ) ^ n)⁻¹ with hr_def
  have hr : 0 < r := by positivity
  have hr32 : r ≤ 1 / 32 := by linarith
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  have hCf := S.hCf
  have hn8 : 8 * r ≤ lam := by linarith
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (1 : ℝ) / 4 ≤ r := by
      rw [hr_def, one_div]; exact inv_anti₀ (by positivity) (by linarith)
    linarith
  set z' := latticePoint (n + 1) k with hz'_def
  set z := latticePoint n l with hz_def
  set wb := weightBound (max (-(η - γ')) 0) (n + 1) k.1 with hwb_def
  have hwb : 0 ≤ wb := weightBound_nonneg _ _ _
  set A1 : ℝ := if 0 < z'.1 then Cr * C₃ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * r ^ (5 + γ') * wb else 0
    with hA1_def
  set A2 : ℝ := if k ∈ latticeBox (n + 1) ((72 * r ^ 2, x.2) : ParabolicSpace) (216 * r ^ 2)
      (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) then
    C₀ * C₃ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * r ^ (5 + min α η) else 0 with hA2_def
  have hL : 0 ≤ (lam ^ 5)⁻¹ := inv_nonneg.2 (pow_nonneg hlam.le 5)
  have hA1 : 0 ≤ A1 := by
    rw [hA1_def]; split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCr hC₃.le)
        hK0) hCf) hL) (Real.rpow_nonneg hr.le _)) hwb
    · exact le_rfl
  have hA2 : 0 ≤ A2 := by
    rw [hA2_def]; split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀ hC₃.le) hK0) hCf) hL)
        (Real.rpow_nonneg hr.le _)
    · exact le_rfl
  have hg3 := h3b hφ hlam hlam1 x n hn8 k l
  set g : ParabolicSpace → ℝ := fun w => rescaledTestFunction φ lam x w * latticeCell (n + 1) k w *
    latticeCell n l w with hg_def
  by_cases hex : ∃ w, g w ≠ 0
  swap
  · push Not at hex
    have : g = fun _ => 0 := funext hex
    rw [this, pairing_zero_test, abs_zero]
    split_ifs
    · exact add_nonneg hA1 hA2
    · exact le_rfl
  obtain ⟨w, hw⟩ := hex
  obtain ⟨h12, h3⟩ := mul_ne_zero_iff.1 hw
  obtain ⟨hψ, h1⟩ := mul_ne_zero_iff.1 h12
  have hwx : parabolicNorm (w - x) ≤ lam := by
    by_contra hc
    exact hψ (rescaledTestFunction_eq_zero hφ.2.1 hlam (not_le.1 hc))
  have hwT : w.1 ≤ T := by
    by_contra hc
    exact hψ (hφT w (not_le.1 hc))
  obtain ⟨g1, g2, g3, g4, g5⟩ := pair_geometry h1 h3
  have hLbox : l ∈ latticeBox n z' (144 * r ^ 2) (12 * r) := by
    refine mem_latticeBox ?_ fun i => ?_
    · have := abs_fst_sub_le_sq z' z
      rw [abs_sub_comm]
      have h0 := parabolicNorm_nonneg (z' - z)
      refine this.trans ?_
      nlinarith
    · rw [abs_sub_comm]
      exact (abs_snd_sub_le z' z i).trans g5
  rw [ite_eq_left hLbox]
  suffices h : |parabolicSemigroup.pairing (M.regPi z' (f z' - M.gammaMap z' z (f z))) g| ≤
      A1 + A2 from h
  have hz'T : z'.1 ≤ T := (g3.trans_le hwT).le
  have hzT : z.1 ≤ T := (g4.trans_le hwT).le
  by_cases hReg : 0 < z'.1 ∧ 0 < z.1 ∧ parabolicNorm (z' - z) ≤
      min (singularWeight timeZeroDist z') (singularWeight timeZeroDist z)
  · obtain ⟨ha, hb, hd⟩ := hReg
    have hz'm : z' ∈ timeSlab T := ⟨ha, hz'T⟩
    have hzm : z ∈ timeSlab T := ⟨hb, hzT⟩
    have hmain := hreg S hg3 hz'm hzm hd g5
    set W := min (singularWeight timeZeroDist z') (singularWeight timeZeroDist z) with hW_def
    have hu : 0 < Real.sqrt |z'.1| := Real.sqrt_pos.2 (abs_pos.2 ha.ne')
    have hWle : W ≤ min 1 (Real.sqrt |z'.1|) := min_le_left _ _
    have hWge : min 1 (Real.sqrt |z'.1|) / 2 ≤ W := half_singularWeight_le_min hd
    have hWp := rpow_le_of_half_le (η - γ') hu hWge hWle
    rw [sqrt_latticePoint_fst ha] at hWp
    have hWb : W ^ (η - γ') ≤ wb := hWp
    have hA1' : A1 = Cr * C₃ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ * r ^ (5 + γ') * wb := ite_eq_left ha
    rw [hA1']
    refine (hmain.trans ?_).trans (le_add_of_nonneg_right hA2)
    have hcoef : 0 ≤ Cr * (max 1 CGam * CPi) * Cf * (C₃ * (lam ^ 5)⁻¹) * r ^ (5 + γ') :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCr hK0) hCf) (mul_nonneg hC₃.le hL))
        (Real.rpow_nonneg hr.le _)
    calc Cr * (max 1 CGam * CPi) * Cf * (C₃ * (lam ^ 5)⁻¹) * r ^ (5 + γ') * W ^ (η - γ')
        ≤ Cr * (max 1 CGam * CPi) * Cf * (C₃ * (lam ^ 5)⁻¹) * r ^ (5 + γ') * wb :=
          mul_le_mul_of_nonneg_left hWb hcoef
      _ = _ := by ring
  · by_cases hf0 : f z' = 0 ∧ f z = 0
    · have : M.regPi z' (f z' - M.gammaMap z' z (f z)) = M.regPi z' 0 := by
        rw [hf0.1, hf0.2, map_zero, sub_zero]
      rw [this, pairing_regPi_zero_eq, abs_zero]
      exact add_nonneg hA1 hA2
    · have hpos : 0 < z'.1 ∨ 0 < z.1 := by
        by_contra hc
        push Not at hc
        exact hf0 ⟨S.hf0 z' fun hm => absurd hm.1 (not_lt.2 hc.1),
          S.hf0 z fun hm => absurd hm.1 (not_lt.2 hc.2)⟩
      obtain ⟨t1, t2⟩ := near_time_bounds hr.le hr32 g5 hReg hpos
      have e : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ = 4 * r := by rw [hr_def, pow_succ, mul_inv]; ring
      have hNB : k ∈ latticeBox (n + 1) ((72 * r ^ 2, x.2) : ParabolicSpace) (216 * r ^ 2)
          (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) := by
        refine mem_latticeBox ?_ fun i => ?_
        · show |z'.1 - 72 * r ^ 2| ≤ 216 * r ^ 2
          rw [abs_le]; constructor <;> linarith
        · show |z'.2 i - x.2 i| ≤ _
          refine (abs_snd_sub_le z' x i).trans ?_
          have : z' - x = (z' - w) + (w - x) := by abel
          rw [this]
          refine (parabolicNorm_add_le _ _).trans ?_
          rw [parabolicNorm_sub_comm z' w]
          linarith
      have hA2' : A2 = C₀ * C₃ * (max 1 CGam * CPi) * Cf * (lam ^ 5)⁻¹ *
          r ^ (5 + min α η) := ite_eq_left hNB
      rw [hA2']
      refine le_trans ?_ (le_add_of_nonneg_left hA1)
      have hn := hnear S hn3 hg3 fun w' hw' => right_ne_zero_of_mul hw'
      refine hn.trans (le_of_eq ?_)
      ring

end RegularityStructures.Layer

end
