/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Singular.Layer.Geometry
public import RegularityStructures.Abstract.Singular.ModelPairing.Single
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Regular-pair bound for the layer increments, near-pair `Γ`-bounds

In the window layer setting `LayerSettingWNear`, for a lattice point `x_k` of level `n + 1` and a
lattice point `x_l` of level `n` in the slab, at distance at most `12 · 2^{-n}` and at most the
smaller weight `w = min(w_{x_k}, w_{x_l})`, and `g` scaled at `x_k` with constant `A`:
`|⟨Π_{x_k}(f(x_k) − Γ_{x_k x_l} f(x_l)), g⟩| ≤ C K₀ C_f A 2^{-n(5+γ')} w^{η−γ'}`, for models whose
`Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

theorem exists_abs_pairing_regular_le_win_near (𝒯 : RegularityStructure ι) (γ γ' : ℝ) (hγ' : γ' ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Model 𝒯 parabolicSemigroup} {f : ParabolicSpace → ι → ℝ}
      {η α Cf CPi CGam T : ℝ}, LayerSettingWNear M f γ η α Cf CPi CGam T → ∀ {n : ℕ}
      {k l : LatticeIndex} {g : ParabolicSpace → ℝ} {A : ℝ},
      IsScaledTest g (latticePoint (n + 1) k) (8 * ((2 : ℝ) ^ (n + 1))⁻¹) A →
      latticePoint (n + 1) k ∈ timeSlab T → latticePoint n l ∈ timeSlab T →
      parabolicNorm (latticePoint (n + 1) k - latticePoint n l) ≤
        min (singularWeight timeZeroDist (latticePoint (n + 1) k))
          (singularWeight timeZeroDist (latticePoint n l)) →
      parabolicNorm (latticePoint (n + 1) k - latticePoint n l) ≤ 12 * ((2 : ℝ) ^ n)⁻¹ →
      |parabolicSemigroup.pairing (M.regPi (latticePoint (n + 1) k)
        (f (latticePoint (n + 1) k) - M.gammaMap (latticePoint (n + 1) k) (latticePoint n l)
          (f (latticePoint n l)))) g| ≤
        C * (max 1 CGam * CPi) * Cf * A * (((2 : ℝ) ^ n)⁻¹) ^ (5 + γ') *
          (min (singularWeight timeZeroDist (latticePoint (n + 1) k))
            (singularWeight timeZeroDist (latticePoint n l))) ^ (η - γ') := by
  set D12 : ℝ := ∑ i, (12 : ℝ) ^ (γ - 𝒯.deg i) * (4 : ℝ) ^ 𝒯.deg i with hD12
  refine ⟨|r4ModelConst 𝒯 γ| * 4 ^ 5 * (2 : ℝ) ^ (γ - γ') * D12, by positivity,
    fun {M f η α Cf CPi CGam T} S n k l g A hg hz' hz hd hd12 => ?_⟩
  set r : ℝ := ((2 : ℝ) ^ n)⁻¹ with hr_def
  have hr : 0 < r := by positivity
  set z' := latticePoint (n + 1) k with hz'_def
  set z := latticePoint n l with hz_def
  set W := min (singularWeight timeZeroDist z') (singularWeight timeZeroDist z) with hW_def
  set d := parabolicNorm (z' - z) with hd_def
  have hR : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ = 4 * r := by
    rw [hr_def, pow_succ, mul_inv]; ring
  rw [hR] at hg
  have hw1 : r / 2 ≤ singularWeight timeZeroDist z' := by
    have := Layer.inv_two_pow_le_singularWeight (n := n + 1) (k := k) hz'.1
    rw [pow_succ, mul_inv] at this
    have e : r / 2 = ((2 : ℝ) ^ n)⁻¹ * 2⁻¹ := by rw [hr_def]; ring
    rwa [e]
  have hw2 : r / 2 ≤ singularWeight timeZeroDist z :=
    (div_le_self hr.le (by norm_num)).trans (Layer.inv_two_pow_le_singularWeight hz.1)
  have hWr : r / 2 ≤ W := le_min hw1 hw2
  have hWpos : 0 < W := lt_of_lt_of_le (by positivity) hWr
  have hρ' : 0 < timeZeroDist z' := timeZeroDist_pos_of_mem_timeSlab hz'
  have hρ : 0 < timeZeroDist z := timeZeroDist_pos_of_mem_timeSlab hz
  have hτ : f z' - M.gammaMap z' z (f z) ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (S.hfT _) ((M.isGradedUnipotent_gammaMap _ _).map_lowerSubspace (S.hfT _))
  have hmain := S.abs_pairing_le hτ hg hz'
  refine hmain.trans ?_
  have hK0 : 0 ≤ max 1 CGam * CPi := S.hK0
  -- bound on each coordinate of the increment
  have hterm : ∀ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f z' - M.gammaMap z' z (f z)) i| * (4 * r) ^ 𝒯.deg i ≤
        Cf * (2 : ℝ) ^ (γ - γ') * (12 ^ (γ - 𝒯.deg i) * 4 ^ 𝒯.deg i) *
          (r ^ γ' * W ^ (η - γ')) := by
    intro i hi
    have hi' := (Finset.mem_filter.1 hi).2
    have h1 := S.hf.2 z hz z' hz' hρ hρ' (by rw [min_comm]; exact hd) i hi'
    rw [min_comm (singularWeight timeZeroDist z) (singularWeight timeZeroDist z')] at h1
    have hγi : 0 ≤ γ - 𝒯.deg i := by linarith
    have h2 : d ^ (γ - 𝒯.deg i) ≤ (12 * r) ^ (γ - 𝒯.deg i) :=
      Real.rpow_le_rpow (parabolicNorm_nonneg _) hd12 hγi
    have h3 : |(f z' - M.gammaMap z' z (f z)) i| ≤
        Cf * (12 * r) ^ (γ - 𝒯.deg i) * W ^ (η - γ) :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 S.hCf)
        (Real.rpow_nonneg hWpos.le _))
    have hexp : r ^ (γ - 𝒯.deg i) * r ^ 𝒯.deg i = r ^ γ := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have hWg : W ^ (η - γ) * r ^ γ ≤ (2 : ℝ) ^ (γ - γ') * (r ^ γ' * W ^ (η - γ')) := by
      have e1 : W ^ (η - γ) = W ^ (η - γ') * W ^ (γ' - γ) := by
        rw [← Real.rpow_add hWpos]; congr 1; ring
      have e2 : W ^ (γ' - γ) ≤ (r / 2) ^ (γ' - γ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hWr (by linarith)
      have e3 : (r / 2) ^ (γ' - γ) = r ^ (γ' - γ) * (2 : ℝ) ^ (γ - γ') := by
        rw [Real.div_rpow hr.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
        congr 2; ring
      have e4 : r ^ γ * r ^ (γ' - γ) = r ^ γ' := by
        rw [← Real.rpow_add hr]; congr 1; ring
      have hWp := Real.rpow_nonneg hWpos.le (η - γ')
      calc W ^ (η - γ) * r ^ γ = W ^ (η - γ') * W ^ (γ' - γ) * r ^ γ := by rw [e1]
        _ ≤ W ^ (η - γ') * ((r ^ (γ' - γ) * (2 : ℝ) ^ (γ - γ'))) * r ^ γ := by
            rw [← e3]; gcongr
        _ = (2 : ℝ) ^ (γ - γ') * (r ^ γ' * W ^ (η - γ')) := by
            rw [← e4]; ring
    calc |(f z' - M.gammaMap z' z (f z)) i| * (4 * r) ^ 𝒯.deg i
        ≤ (Cf * (12 * r) ^ (γ - 𝒯.deg i) * W ^ (η - γ)) * (4 * r) ^ 𝒯.deg i := by gcongr
      _ = Cf * (12 ^ (γ - 𝒯.deg i) * 4 ^ 𝒯.deg i) * (r ^ (γ - 𝒯.deg i) * r ^ 𝒯.deg i *
            W ^ (η - γ)) := by
          rw [Real.mul_rpow (by norm_num) hr.le, Real.mul_rpow (by norm_num) hr.le]; ring
      _ = Cf * (12 ^ (γ - 𝒯.deg i) * 4 ^ 𝒯.deg i) * (W ^ (η - γ) * r ^ γ) := by
          rw [hexp]; ring
      _ ≤ Cf * (12 ^ (γ - 𝒯.deg i) * 4 ^ 𝒯.deg i) *
            ((2 : ℝ) ^ (γ - γ') * (r ^ γ' * W ^ (η - γ'))) := by
          have := S.hCf
          gcongr
      _ = _ := by ring
  have hsum : ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f z' - M.gammaMap z' z (f z)) i| * (4 * r) ^ 𝒯.deg i ≤
        Cf * (2 : ℝ) ^ (γ - γ') * D12 * (r ^ γ' * W ^ (η - γ')) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (by have := S.hCf; positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => by positivity
  have hr5 : (4 * r) ^ 5 = 4 ^ 5 * r ^ (5 : ℝ) := by
    rw [mul_pow, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpow : r ^ (5 + γ') = r ^ (5 : ℝ) * r ^ γ' := Real.rpow_add hr _ _
  have hc : r4ModelConst 𝒯 γ ≤ |r4ModelConst 𝒯 γ| := le_abs_self _
  have hA := hg.const_pos
  have hp5 : 0 ≤ r ^ (5 : ℝ) := Real.rpow_nonneg hr.le _
  have h0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      |(f z' - M.gammaMap z' z (f z)) i| * (4 * r) ^ 𝒯.deg i :=
    Finset.sum_nonneg fun i _ => by positivity
  have h5 : 0 ≤ A * (4 * r) ^ 5 := by positivity
  calc r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A * (4 * r) ^ 5) *
        ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
          |(f z' - M.gammaMap z' z (f z)) i| * (4 * r) ^ 𝒯.deg i
      ≤ |r4ModelConst 𝒯 γ| * (max 1 CGam * CPi) * (A * (4 * r) ^ 5) *
        (Cf * (2 : ℝ) ^ (γ - γ') * D12 * (r ^ γ' * W ^ (η - γ'))) := by
        calc _ ≤ |r4ModelConst 𝒯 γ| * (max 1 CGam * CPi) * (A * (4 * r) ^ 5) *
              ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
                |(f z' - M.gammaMap z' z (f z)) i| * (4 * r) ^ 𝒯.deg i := by gcongr
          _ ≤ _ := by gcongr
    _ = _ := by rw [hr5, hpow]; ring

end RegularityStructures

end
