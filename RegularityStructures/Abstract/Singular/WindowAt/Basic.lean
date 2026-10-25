/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.SectorLocal
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Pointwise qualitative growth

`Model.HasQualitativeGrowthAt M γ x` is the qualitative polynomial growth of `Q_t Π_x e_i`
(`deg i < γ`, `0 < t ≤ 1`) at the single base point `x`, with constants allowed to depend on `x`.

The uniform-in-`x` version `Model.HasQualitativeGrowth` of
`RegularityStructures.Abstract.Singular.Window.Basic` cannot be derived from a `Model.GrowthModel`
(its constants carry the unbounded weights `ρP(x) ρG(x)`); the pointwise version can
(`GrowthModel.hasQualitativeGrowthAt`). The window entry lemmas only ever use the growth at the base
point, so they are re-proved in `WindowAt/*` with the pointwise hypothesis; the quantitative
constants are unchanged.
-/

@[expose] public section

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- Qualitative polynomial growth of `Q_t Π_x e_i`, `deg i < γ`, `0 < t ≤ 1`, at the base point
`x` (constants may depend on `x`). -/
def HasQualitativeGrowthAt (M : Model 𝒯 parabolicSemigroup) (γ : ℝ) (x : ParabolicSpace) :
    Prop :=
  ∃ C' β q : ℝ, ∀ i : ι, 𝒯.deg i < γ → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
    ∀ y : ParabolicSpace, |M.regPi x (Pi.single i 1) t y| ≤
      C' * t ^ (β / 4) * (1 + parabolicNorm (y - x)) ^ q

end Model

end RegularityStructures

end

public section

open Set

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ : ℝ} {x : ParabolicSpace}

/-- Normalised form of the pointwise qualitative growth: nonnegative constant and exponent. -/
theorem HasQualitativeGrowthAt.exists_crude (h : M.HasQualitativeGrowthAt γ x) :
    ∃ C' β q : ℝ, 0 ≤ C' ∧ 0 ≤ q ∧ ∀ i : ι, 𝒯.deg i < γ →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ y : ParabolicSpace, |M.regPi x (Pi.single i 1) t y| ≤
        C' * t ^ (β / 4) * (1 + parabolicNorm (y - x)) ^ q := by
  obtain ⟨C', β, q, h⟩ := h
  refine ⟨max C' 0, β, max q 0, le_max_right _ _, le_max_right _ _, fun i hi t ht y => ?_⟩
  refine (h i hi t ht y).trans ?_
  have hd : 1 ≤ 1 + parabolicNorm (y - x) := by linarith [parabolicNorm_nonneg (y - x)]
  have h1 : (1 + parabolicNorm (y - x)) ^ q ≤ (1 + parabolicNorm (y - x)) ^ (max q 0) :=
    Real.rpow_le_rpow_of_exponent_le hd (le_max_left _ _)
  have h2 : 0 ≤ t ^ (β / 4) := Real.rpow_nonneg ht.1.le _
  have h3 : 0 ≤ (1 + parabolicNorm (y - x)) ^ q := Real.rpow_nonneg (by linarith) _
  have h4 : 0 ≤ (1 + parabolicNorm (y - x)) ^ (max q 0) := Real.rpow_nonneg (by linarith) _
  calc C' * t ^ (β / 4) * (1 + parabolicNorm (y - x)) ^ q
      ≤ max C' 0 * t ^ (β / 4) * (1 + parabolicNorm (y - x)) ^ q := by
        gcongr; exact le_max_left _ _
    _ ≤ _ := by gcongr

/-- A growth model has qualitative growth at every base point (the constants depend on the
weights at the base point). -/
theorem GrowthModel.hasQualitativeGrowthAt {CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG) (x : ParabolicSpace) :
    M.HasQualitativeGrowthAt γ x := by
  set S : ℝ := ∑ j, |𝒯.deg j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSj : ∀ j, |𝒯.deg j| ≤ S := fun j =>
    Finset.single_le_sum (f := fun j => |𝒯.deg j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  set c : ℝ := max CGam 1 * CPi * Fintype.card ι * (ρP x * ρG x) with hc
  have hc0 : 0 ≤ c :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _))
      G.piBound_nonneg) (Nat.cast_nonneg _))
      (mul_nonneg (G.moderateP.pos x).le (G.moderateG.pos x).le)
  have hpq : 0 ≤ p + qG := add_nonneg G.moderateP.nonneg_exp G.nonnegG
  refine ⟨c * Fintype.card ι, -S, p + qG + 2 * S, fun i hi u hu y => ?_⟩
  have h1 := G.isLocalOrderGrowth_regPi_single_top hi x u hu y
  have hsd : parabolicSemigroup.scaleDist y x = parabolicNorm (y - x) := rfl
  have hord : parabolicSemigroup.order = 4 := rfl
  rw [hsd, hord] at h1
  set d := parabolicNorm (y - x) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have h1d : 1 ≤ 1 + d := by linarith
  have hterm : ∀ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i),
      u ^ (a / (4 : ℝ)) * d ^ (𝒯.deg i - a) ≤ u ^ (-S / 4) * (1 + d) ^ (2 * S) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    obtain ⟨j, -, -, rfl⟩ := (𝒯.mem_degreesBelowIn _).1 ha1
    have hja := abs_le.1 (hSj j)
    have hji := abs_le.1 (hSj i)
    have e1 : u ^ (𝒯.deg j / (4 : ℝ)) ≤ u ^ (-S / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2 (by linarith)
    have e2 : d ^ (𝒯.deg i - 𝒯.deg j) ≤ (1 + d) ^ (2 * S) :=
      (Real.rpow_le_rpow hd0 (by linarith) (by linarith)).trans
        (Real.rpow_le_rpow_of_exponent_le h1d (by linarith))
    exact mul_le_mul e1 e2 (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hu.1.le _)
  have hsum : ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i),
      u ^ (a / (4 : ℝ)) * d ^ (𝒯.deg i - a) ≤
        Fintype.card ι * (u ^ (-S / 4) * (1 + d) ^ (2 * S)) := by
    refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.rpow_nonneg hu.1.le _)
      (Real.rpow_nonneg (by linarith) _))
    exact_mod_cast (Finset.card_filter_le _ _).trans
      (Finset.card_image_le.trans (Finset.card_le_univ _))
  have hpos : 0 < 1 + d := by linarith
  have hpow : (1 + d) ^ (p + qG + 2 * S) = (1 + d) ^ (p + qG) * (1 + d) ^ (2 * S) :=
    Real.rpow_add hpos _ _
  refine h1.trans ?_
  have hA : 0 ≤ c * (1 + d) ^ (p + qG) := mul_nonneg hc0 (Real.rpow_nonneg hpos.le _)
  calc c * (1 + d) ^ (p + qG) * ∑ a ∈ 𝒯.degreesBelowLeIn ⊤ γ (𝒯.deg i),
        u ^ (a / (4 : ℝ)) * d ^ (𝒯.deg i - a)
      ≤ c * (1 + d) ^ (p + qG) * (Fintype.card ι * (u ^ (-S / 4) * (1 + d) ^ (2 * S))) :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = _ := by rw [hpow]; ring

/-- Pointwise qualitative growth from the mere existence of a growth model (arbitrary constants,
weights and exponents). -/
theorem hasQualitativeGrowthAt_of_exists (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}
    (h : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q) (x : ParabolicSpace) :
    M.HasQualitativeGrowthAt γ x := by
  obtain ⟨_, _, _, _, _, _, G⟩ := h
  exact G.hasQualitativeGrowthAt x

end Model

end RegularityStructures

end
