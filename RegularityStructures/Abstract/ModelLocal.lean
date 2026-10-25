/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Germ
public import RegularityStructures.Abstract.GermCoherence
public import RegularityStructures.Analysis.Semigroup.Pairing
public import RegularityStructures.Analysis.Semigroup.Pairing.Limit

/-!
# Local order of `Π_x e_i` away from the base point

The model bound controls `(Q_t Π_x e_i)` only at the base point `x`. With the `Γ` bound and
`Π_x = Π_y Γ_{yx}` one gets, for every `y` ([Hos25, Remark 3.4, (3.1)], [Hai14, (2.15)]),

  `|(Q_u Π_x e_i)(y)| ≤ max(C_Γ, 1) C_Π |ι| ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}`,

i.e. `Π_x e_i` is of local order `deg i` at `x` (`RegularisingSemigroup.IsLocalOrder`). This is
what is needed to pair `Π_x e_i` with test functions near `x` (e.g. with derivatives of the
kernel `K_n(x, ·)` in Hairer's map `J(x)`, [Hai14, (5.11)]).

Source: [Hos25, Remark 3.4], [Hai14, Section 2.3, (5.11)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degrees `a ≤ α` among those below `γ`. -/
def RegularityStructure.degreesBelowLe (𝒯 : RegularityStructure ι) (γ α : ℝ) : Finset ℝ :=
  (𝒯.degreesBelow γ).filter (· ≤ α)

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- `Π_x e_i` is of local order `deg i` at `x`. -/
theorem isLocalOrder_regPi_single {γ CPi CGam : ℝ} (hPi : M.PiBoundOn γ CPi univ)
    (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi) {i : ι} (hi : 𝒯.deg i < γ)
    (x : E) :
    K.IsLocalOrder (fun t y => M.regPi x (Pi.single i 1) t y) x (𝒯.deg i)
      (𝒯.degreesBelowLe γ (𝒯.deg i)) (max CGam 1 * CPi * Fintype.card ι) := by
  intro u hu y
  have hU := M.isGradedUnipotent_gammaMap y x
  have hτ : M.gammaMap y x (Pi.single i 1) ∈ lowerSubspace 𝒯.deg γ :=
    hU.map_lowerSubspace (single_mem_lowerSubspace hi 1)
  have hC1 : 0 ≤ max CGam 1 := le_trans zero_le_one (le_max_right _ _)
  set h : ℝ → ℝ := fun a => if a ≤ 𝒯.deg i then
      max CGam 1 * CPi * (u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a)) else 0 with hh
  have hh0 : ∀ a ∈ 𝒯.degreesBelow γ, 0 ≤ h a := fun a _ => by
    simp only [hh]
    split_ifs
    · exact mul_nonneg (mul_nonneg hC1 hCPi)
        (mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
    · exact le_rfl
  have hterm : ∀ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
      |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| ≤ h (𝒯.deg j) := by
    intro j hj
    have hj : 𝒯.deg j < γ := (Finset.mem_filter.1 hj).2
    have hPij := hPi j hj u hu y (mem_univ y)
    rw [abs_mul]
    by_cases hji : j = i
    · subst hji
      rw [hU.apply_single_self, abs_one, one_mul]
      simp only [hh, le_refl, ite_true, sub_self, Real.rpow_zero, mul_one]
      calc |M.regPi y (Pi.single j 1) u y| ≤ CPi * u ^ (𝒯.deg j / K.order) := hPij
        _ = 1 * CPi * u ^ (𝒯.deg j / K.order) := by ring
        _ ≤ max CGam 1 * CPi * u ^ (𝒯.deg j / K.order) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hCPi)
            (Real.rpow_nonneg hu.1.le _)
    · by_cases hlt : 𝒯.deg j < 𝒯.deg i
      · have hG := hGam i j hi hlt x (mem_univ x) y (mem_univ y)
        simp only [hh, hlt.le, ite_true]
        calc |M.gammaMap y x (Pi.single i 1) j| * |M.regPi y (Pi.single j 1) u y|
            ≤ (CGam * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) *
                (CPi * u ^ (𝒯.deg j / K.order)) :=
              mul_le_mul hG hPij (abs_nonneg _) ((abs_nonneg _).trans hG)
          _ ≤ (max CGam 1 * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) *
                (CPi * u ^ (𝒯.deg j / K.order)) := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)) ?_
              exact mul_nonneg hCPi (Real.rpow_nonneg hu.1.le _)
          _ = _ := by ring
      · rw [hU.apply_single_of_le hji (not_lt.1 hlt), abs_zero, zero_mul]
        exact hh0 _ ((𝒯.mem_degreesBelow).2 ⟨j, hj, rfl⟩)
  have hsum : ∑ a ∈ 𝒯.degreesBelow γ, h a =
      max CGam 1 * CPi * ∑ a ∈ 𝒯.degreesBelowLe γ (𝒯.deg i),
        u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a) := by
    rw [RegularityStructure.degreesBelowLe, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh]
    split_ifs <;> simp
  calc |M.regPi x (Pi.single i 1) u y|
      = |M.regPi y (M.gammaMap y x (Pi.single i 1)) u y| := by rw [M.regPi_gammaMap]
    _ = |∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
          M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| := by
        rw [M.regPi_eq_sum_filter hτ]
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), h (𝒯.deg j) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ ≤ Fintype.card ι * ∑ a ∈ 𝒯.degreesBelow γ, h a := sum_filter_deg_le_card_mul 𝒯 γ hh0
    _ = _ := by rw [hsum]; ring

end Model

end RegularityStructures

end
