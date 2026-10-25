/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedProductF
public import Phi43.Structure.EnlargedAbstractF
public import Phi43.Structure.EnlargedIntegrationF
public import RegularityStructures.Abstract.ProductDefs
import Mathlib.Tactic.Linarith

/-!
# Basic calculus of the enlarged product

* `phi43EF τ = e_{old τ}`, the old basis vectors in the enlarged coordinate space;
* `phi43ProductLinearF_apply_coord`: the coordinates of the product;
* `phi43ProductLinearF_eF`: the product of two old basis vectors;
* `Phi43SuppGe κ α v`: `v` has no coordinate of degree `< α`, and `phi43ProductLinearF_suppGe`: the product of
  vectors supported in degrees `≥ α`, `≥ β` is supported in degrees `≥ α + β`.

Source: [Hai14, Definition 4.1, (8.3)–(8.4)].
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- The old basis vector `e_{old τ}` of the enlarged coordinate space. -/
noncomputable def phi43EF (τ : Symbol) : SymbolF → ℝ := Pi.single (.old τ) 1

/-- `v` has no coordinate of degree `< α`. -/
def Phi43SuppGe (κ : Kappa) (α : ℝ) (v : SymbolF → ℝ) : Prop :=
  ∀ τ, phi43DegreeF κ τ < α → v τ = 0

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43EF_eq (τ : Symbol) : phi43EF τ = phi43OldEmbF (Pi.single τ 1) :=
  (phi43OldEmbF_single τ).symm

theorem phi43ProductLinearF_apply_coord (a b : SymbolF → ℝ) (υ : SymbolF) :
    phi43ProductLinearF a b υ =
      ∑ τ : SymbolF, ∑ σ : SymbolF, (a τ * b σ) * phi43ProductBasisF τ σ υ := by
  change (∑ τ : SymbolF, ∑ σ : SymbolF, (a τ * b σ) • phi43ProductBasisF τ σ) υ = _
  simp [Finset.sum_apply]

theorem phi43ProductBasisF_apply_ne_zero {τ σ υ : SymbolF}
    (h : phi43ProductBasisF τ σ υ ≠ 0) : phi43ProductSymbolF τ σ = some υ := by
  unfold phi43ProductBasisF at h
  cases hs : phi43ProductSymbolF τ σ with
  | none => simp [hs] at h
  | some υ' =>
    rw [hs] at h
    have : υ' = υ := by
      by_contra hne
      exact h (Pi.single_eq_of_ne (Ne.symm hne) _)
    rw [this]

/-- Products of vectors supported in degrees `≥ α` and `≥ β` are supported in degrees `≥ α + β`. -/
theorem phi43ProductLinearF_suppGe (κ : Kappa) {α β : ℝ} {a b : SymbolF → ℝ}
    (ha : Phi43SuppGe κ α a) (hb : Phi43SuppGe κ β b) :
    Phi43SuppGe κ (α + β) (phi43ProductLinearF a b) := by
  intro υ hυ
  rw [phi43ProductLinearF_apply_coord]
  refine Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun σ _ => ?_
  by_cases h : phi43ProductBasisF τ σ υ = 0
  · rw [h, mul_zero]
  · have hs := phi43ProductBasisF_apply_ne_zero h
    have hd := phi43ProductSymbolF_degree κ hs
    by_cases hτ : phi43DegreeF κ τ < α
    · rw [ha τ hτ, zero_mul, zero_mul]
    · have hσ : phi43DegreeF κ σ < β := by linarith
      rw [hb σ hσ, mul_zero, zero_mul]

theorem phi43SuppGe_mono (κ : Kappa) {α β : ℝ} (h : α ≤ β) {v : SymbolF → ℝ}
    (hv : Phi43SuppGe κ β v) : Phi43SuppGe κ α v :=
  fun τ hτ => hv τ (lt_of_lt_of_le hτ h)

theorem phi43SuppGe_add (κ : Kappa) {α : ℝ} {a b : SymbolF → ℝ} (ha : Phi43SuppGe κ α a)
    (hb : Phi43SuppGe κ α b) : Phi43SuppGe κ α (a + b) := by
  intro τ hτ
  simp [ha τ hτ, hb τ hτ]

theorem phi43SuppGe_smul (κ : Kappa) {α : ℝ} (c : ℝ) {a : SymbolF → ℝ}
    (ha : Phi43SuppGe κ α a) : Phi43SuppGe κ α (c • a) := by
  intro τ hτ
  simp [ha τ hτ]

theorem phi43SuppGe_zero (κ : Kappa) (α : ℝ) : Phi43SuppGe κ α 0 := fun _ _ => rfl

theorem phi43SuppGe_single (κ : Kappa) {α : ℝ} {τ : SymbolF} (h : α ≤ phi43DegreeF κ τ) :
    Phi43SuppGe κ α (Pi.single τ 1 : SymbolF → ℝ) := by
  intro σ hσ
  have : σ ≠ τ := by
    rintro rfl
    linarith
  simp [Pi.single_eq_of_ne this]

/-- A vector supported in degrees `≥ κ` is killed by `Q_{<κ}`. -/
theorem lowerProj_eq_zero_of_suppGe (κ : Kappa) {γ : ℝ} {v : SymbolF → ℝ}
    (hv : Phi43SuppGe κ γ v) :
    RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg γ v = 0 := by
  funext τ
  rw [RegularityStructures.lowerProj_apply]
  split_ifs with h
  · exact hv τ h
  · rfl

theorem phi43ProductLinearF_single (τ σ : SymbolF) :
    phi43ProductLinearF (Pi.single τ 1) (Pi.single σ 1) = phi43ProductBasisF τ σ := by
  change (∑ τ' : SymbolF, ∑ σ' : SymbolF, ((Pi.single τ 1 : SymbolF → ℝ) τ' *
    (Pi.single σ 1 : SymbolF → ℝ) σ') • phi43ProductBasisF τ' σ') = _
  rw [Finset.sum_eq_single τ]
  · rw [Finset.sum_eq_single σ]
    · simp
    · intro σ' _ h
      simp [Pi.single_eq_of_ne h]
    · simp
  · intro τ' _ h
    simp [Pi.single_eq_of_ne h]
  · simp

theorem phi43ProductLinearF_eF (τ σ : Symbol) :
    phi43ProductLinearF (phi43EF τ) (phi43EF σ) =
      match productSymbol τ σ with
      | some υ => phi43EF υ
      | none => 0 := by
  unfold phi43EF
  rw [phi43ProductLinearF_single]
  simp only [phi43ProductBasisF, phi43ProductSymbolF]
  cases h : productSymbol τ σ <;> simp

end RegularityStructures.Phi43

end
