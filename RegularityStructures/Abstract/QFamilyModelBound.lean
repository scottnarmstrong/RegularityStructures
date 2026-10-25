/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Germ
public import RegularityStructures.Analysis.Semigroup.Pairing
public import RegularityStructures.Abstract.Model

/-!
# From the `Q`-form model bound to the test-function bound [Hai14, (2.15)]

The model bounds of this layer are in `Q`-form: `|(Q_t Π_x e_i)(x)| ≤ C_Π t^{deg i/ℓ}`
(`Model.PiBoundOn`) and `|(Γ_{yx} e_i)_j| ≤ C_Γ d(y, x)^{deg i − deg j}` (`Model.GammaBoundOn`).
Hairer's bound (2.15) is in test-function form: `|⟨Π_x e_i, φ^λ_x⟩| ≲ λ^{deg i}`.

* `Model.gammaMap_single_apply_self`, `Model.gammaMap_single_apply_of_le`: the coordinates of
  `Γ e_i` of degree `≥ deg i` are those of `e_i` (graded unipotence);
* `Model.isLocalOrder_regPi_single_degreesAtMost`: `Π_x e_i` is of local order `deg i` at `x`,
  `|(Q_u Π_x e_i)(y)| ≤ |ι| max(1, C_Γ) C_Π ∑_{a ≤ deg i} u^{a/ℓ} d(y, x)^{deg i − a}` (the
  model bound at the base point is transported to `y` by `Π_x = Π_y Γ_{yx}`);
* `Model.abs_pairing_regPi_single_le`: hence, if all homogeneities below `γ` exceed `-ℓ`, the
  pairing `⟨Π_x e_i, φ⟩` with a test function `φ` adapted to scale `λ ≤ 1` at `x` (with
  generator image `ψ`) exists and is at most
  `|ι| max(1, C_Γ) C_Π pairingConst (B₀ + B₁) λ^{deg i}`.

The `ℝ⁴` form with `φ^λ_x`, `φ ∈ B^4`, is `Model.abs_pairing_regPi_rescaledTestFunction_le` in
`RegularityStructures.Abstract.QFamilyR4ModelBound`.

Sources: [Hai14] = arXiv:1303.5113v4, Definition 2.17, (2.15); [Hos25] = arXiv:2310.07396v2,
Definition 3.2.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degrees `deg j ≤ b`. -/
def RegularityStructure.degreesAtMost (𝒯 : RegularityStructure ι) (b : ℝ) : Finset ℝ :=
  (Finset.univ.filter (fun j => 𝒯.deg j ≤ b)).image 𝒯.deg

end RegularityStructures

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

theorem RegularityStructure.mem_degreesAtMost (𝒯 : RegularityStructure ι) {b a : ℝ} :
    a ∈ 𝒯.degreesAtMost b ↔ ∃ j, 𝒯.deg j ≤ b ∧ 𝒯.deg j = a := by
  simp [RegularityStructure.degreesAtMost]

theorem RegularityStructure.degreesAtMost_subset_degreesBelow (𝒯 : RegularityStructure ι)
    {b γ : ℝ} (hb : b < γ) : 𝒯.degreesAtMost b ⊆ 𝒯.degreesBelow γ := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := (𝒯.mem_degreesAtMost).1 ha
  exact (𝒯.mem_degreesBelow).2 ⟨j, hj.trans_lt hb, rfl⟩

/-- A sum over a set of basis vectors of a function of the degree is at most `|ι|` times the sum
over the set of degrees. -/
theorem sum_le_card_mul_sum_image (𝒯 : RegularityStructure ι) (S : Finset ι) {h : ℝ → ℝ}
    (hh : ∀ a ∈ S.image 𝒯.deg, 0 ≤ h a) :
    ∑ j ∈ S, h (𝒯.deg j) ≤ Fintype.card ι * ∑ a ∈ S.image 𝒯.deg, h a := by
  have hS : 0 ≤ ∑ a ∈ S.image 𝒯.deg, h a := Finset.sum_nonneg hh
  calc ∑ j ∈ S, h (𝒯.deg j) ≤ ∑ _j ∈ S, ∑ a ∈ S.image 𝒯.deg, h a :=
        Finset.sum_le_sum fun j hj => Finset.single_le_sum hh (Finset.mem_image_of_mem _ hj)
    _ = S.card * ∑ a ∈ S.image 𝒯.deg, h a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * ∑ a ∈ S.image 𝒯.deg, h a :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) hS

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- `(Γ_{yx} e_i)_i = 1`. -/
theorem gammaMap_single_apply_self (x y : E) (i : ι) :
    M.gammaMap y x (Pi.single i 1) i = 1 := by
  have h := (mem_lowerSubspace.1 (M.isGradedUnipotent_gammaMap y x i)) i le_rfl
  rwa [Pi.sub_apply, Pi.single_eq_same, sub_eq_zero] at h

/-- `(Γ_{yx} e_i)_j = 0` for `j ≠ i` with `deg i ≤ deg j`. -/
theorem gammaMap_single_apply_of_le (x y : E) {i j : ι} (hji : j ≠ i)
    (hle : 𝒯.deg i ≤ 𝒯.deg j) : M.gammaMap y x (Pi.single i 1) j = 0 := by
  have h := (mem_lowerSubspace.1 (M.isGradedUnipotent_gammaMap y x i)) j hle
  rwa [Pi.sub_apply, Pi.single_eq_of_ne hji, sub_zero] at h

end Model

end RegularityStructures

end
