/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Integration.SectorLocalOrder
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Basic
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Local order with growth of `Π_x e_i`, sector version

Weighted version of `Model.isLocalOrder_regPi_single_in` ([Hos25, Remark 3.4, (3.1)],
[Hai14, (2.15)]). With `|(Q_t Π_y e_j)(y)| ≤ C_Π ρΠ(y) t^{deg j/ℓ}`,
`|(Γ_{yx} e_i)_j| ≤ C_Γ ρΓ(x) (1 + d)^{q} d^{deg i − deg j}` and `ρΠ(y) ≤ ρΠ(x) (1 + d)^p`,
for `e_i ∈ V` the distribution `Π_x e_i` is of local order `deg i` at `x` with exponents from the
sector `V` and growth `p + q`:

  `|(Q_u Π_x e_i)(y)| ≤ max(C_Γ, 1) C_Π |ι| ρΠ(x) ρΓ(x) (1 + d(y, x))^{p+q}
      ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}`

(`Model.isLocalOrderGrowth_regPi_single_in`).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)
  {V : Submodule ℝ (ι → ℝ)}

/-- `Π_x e_i` is of local order `deg i` at `x` with growth `p + q` and exponents from the sector
`V` (weighted version of `isLocalOrder_regPi_single_in`). -/
theorem isLocalOrderGrowth_regPi_single_in (hV : 𝒯.IsSector V)
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    {γ CPi CGam p q : ℝ} {ρP ρG : E → ℝ} (hρP : K.IsModerateWeight ρP p)
    (hρG : ∀ x, 1 ≤ ρG x) (hq : 0 ≤ q) (hPi : M.PiBoundGrowth γ CPi ρP)
    (hGam : M.GammaBoundGrowth γ CGam ρG q) (hCPi : 0 ≤ CPi) {i : ι}
    (hVi : (Pi.single i 1 : ι → ℝ) ∈ V) (hi : 𝒯.deg i < γ) (x : E) :
    K.IsLocalOrderGrowth (fun t y => M.regPi x (Pi.single i 1) t y) x (𝒯.deg i)
      (𝒯.degreesBelowLeIn V γ (𝒯.deg i))
      (max CGam 1 * CPi * Fintype.card ι * (ρP x * ρG x)) (p + q) := by
  intro u hu y
  have hU := M.isGradedUnipotent_gammaMap y x
  have hτ : M.gammaMap y x (Pi.single i 1) ∈ lowerSubspace 𝒯.deg γ :=
    hU.map_lowerSubspace (single_mem_lowerSubspace hi 1)
  have hτV : M.gammaMap y x (Pi.single i 1) ∈ V := hV.invariant _ (M.gamma y x).2 _ hVi
  have hC1 : 0 ≤ max CGam 1 := le_trans zero_le_one (le_max_right _ _)
  have hC11 : 1 ≤ max CGam 1 := le_max_right _ _
  set d := K.scaleDist y x with hd
  have hd0 : 0 ≤ d := K.scaleDist_nonneg _ _
  have hb0 : 0 ≤ 1 + d := by linarith
  have hbq : 1 ≤ (1 + d) ^ q := Real.one_le_rpow (by linarith) hq
  have hbp : 0 ≤ (1 + d) ^ p := Real.rpow_nonneg hb0 _
  have hsplit : (1 + d) ^ (p + q) = (1 + d) ^ p * (1 + d) ^ q := Real.rpow_add (by linarith) _ _
  have hρx : 0 < ρP x := hρP.pos x
  have hρGx : 1 ≤ ρG x := hρG x
  have hmod : ρP y ≤ ρP x * (1 + d) ^ p := hρP.le x y
  set W : ℝ := max CGam 1 * CPi * (ρP x * ρG x) * (1 + d) ^ (p + q) with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1 hCPi) (mul_nonneg hρx.le (zero_le_one.trans hρGx)))
      (Real.rpow_nonneg hb0 _)
  set h : ℝ → ℝ := fun a => if a ≤ 𝒯.deg i then
      W * (u ^ (a / K.order) * d ^ (𝒯.deg i - a)) else 0 with hh
  have hh0 : ∀ a ∈ 𝒯.degreesBelowIn V γ, 0 ≤ h a := fun a _ => by
    simp only [hh]
    split_ifs
    · exact mul_nonneg hW0
        (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg hd0 _))
    · exact le_rfl
  have hterm : ∀ j ∈ 𝒯.sectorBelow V γ,
      |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| ≤ h (𝒯.deg j) := by
    intro j hj0
    have hj : 𝒯.deg j < γ := ((𝒯.mem_sectorBelow V).1 hj0).2
    have hPij := hPi j hj u hu y
    have hPij' : |M.regPi y (Pi.single j 1) u y| ≤
        CPi * (ρP x * (1 + d) ^ p) * u ^ (𝒯.deg j / K.order) :=
      hPij.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmod hCPi)
        (Real.rpow_nonneg hu.1.le _))
    have hR0 : 0 ≤ CPi * (ρP x * (1 + d) ^ p) * u ^ (𝒯.deg j / K.order) :=
      (abs_nonneg _).trans hPij'
    rw [abs_mul]
    by_cases hji : j = i
    · subst hji
      rw [hU.apply_single_self, abs_one, one_mul]
      simp only [hh, le_refl, ite_true, sub_self, Real.rpow_zero, mul_one]
      refine hPij'.trans ?_
      rw [hW, hsplit]
      have e : CPi * (ρP x * (1 + d) ^ p) * u ^ (𝒯.deg j / K.order) =
          (CPi * ρP x * (1 + d) ^ p * u ^ (𝒯.deg j / K.order)) * 1 := by ring
      have hbase : 0 ≤ CPi * ρP x * (1 + d) ^ p * u ^ (𝒯.deg j / K.order) :=
        mul_nonneg (mul_nonneg (mul_nonneg hCPi hρx.le) hbp) (Real.rpow_nonneg hu.1.le _)
      have hf : (1 : ℝ) ≤ max CGam 1 * ρG x * (1 + d) ^ q :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC11 hρGx) hbq
      calc CPi * (ρP x * (1 + d) ^ p) * u ^ (𝒯.deg j / K.order)
          = (CPi * ρP x * (1 + d) ^ p * u ^ (𝒯.deg j / K.order)) * 1 := e
        _ ≤ (CPi * ρP x * (1 + d) ^ p * u ^ (𝒯.deg j / K.order)) *
              (max CGam 1 * ρG x * (1 + d) ^ q) := mul_le_mul_of_nonneg_left hf hbase
        _ = _ := by ring
    · by_cases hlt : 𝒯.deg j < 𝒯.deg i
      · have hG := hGam i j hi hlt x y
        simp only [hh, hlt.le, ite_true]
        have hG' : |M.gammaMap y x (Pi.single i 1) j| ≤
            max CGam 1 * ρG x * (1 + d) ^ q * d ^ (𝒯.deg i - 𝒯.deg j) :=
          hG.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hρGx))
            (Real.rpow_nonneg hb0 _)) (Real.rpow_nonneg hd0 _))
        calc |M.gammaMap y x (Pi.single i 1) j| * |M.regPi y (Pi.single j 1) u y|
            ≤ (max CGam 1 * ρG x * (1 + d) ^ q * d ^ (𝒯.deg i - 𝒯.deg j)) *
                (CPi * (ρP x * (1 + d) ^ p) * u ^ (𝒯.deg j / K.order)) :=
              mul_le_mul hG' hPij' (abs_nonneg _) ((abs_nonneg _).trans hG')
          _ = _ := by rw [hW, hsplit]; ring
      · rw [hU.apply_single_of_le hji (not_lt.1 hlt), abs_zero, zero_mul]
        exact hh0 _ (Finset.mem_image_of_mem _ hj0)
  have hsum : ∑ a ∈ 𝒯.degreesBelowIn V γ, h a =
      W * ∑ a ∈ 𝒯.degreesBelowLeIn V γ (𝒯.deg i),
        u ^ (a / K.order) * d ^ (𝒯.deg i - a) := by
    rw [RegularityStructure.degreesBelowLeIn, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh]
    split_ifs <;> simp
  calc |M.regPi x (Pi.single i 1) u y|
      = |M.regPi y (M.gammaMap y x (Pi.single i 1)) u y| := by rw [M.regPi_gammaMap]
    _ = |∑ j ∈ 𝒯.sectorBelow V γ,
          M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| := by
        rw [M.regPi_eq_sum_sectorBelow hVb hτV hτ]
    _ ≤ ∑ j ∈ 𝒯.sectorBelow V γ, h (𝒯.deg j) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ Fintype.card ι * ∑ a ∈ 𝒯.degreesBelowIn V γ, h a :=
        sum_sectorBelow_le_card_mul 𝒯 V γ hh0
    _ = _ := by rw [hsum, hW]; ring

end Model

end RegularityStructures

end
