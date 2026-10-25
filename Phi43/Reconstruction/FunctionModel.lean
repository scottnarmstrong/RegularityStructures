/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.FunctionModel
public import Phi43.Restart.Compat
public import Phi43.Structure.CanonicalModelExistence
public import RegularityStructures.Abstract.Translate.Model
public import RegularityStructures.Abstract.Translate.Realising
public import Phi43.LiftBounds.Translate

/-!
# The enlarged restarted model is a smooth function model below `κ`

Let `M'` be a model of the enlarged structure which is compatible (`EnlargedCompat`) with the time
translate by `a` of the renormalised canonical model `Z` of `noise`.  Then
`M'.IsSmoothFunctionModelBelow (phi43EnlargedBase N κ noise C a) κ`, where
`phi43EnlargedBase x (old τ) y = Π^M_{x + a} τ (y + a)` (the base functions of `Z`, translated) and
the planted symbols are given the function `0` (they have degree `≥ κ`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures.Phi43.Restart

/-- The function representatives of `Π'_x e_i`, `deg i < κ`, of the translated enlarged model. -/
@[expose] noncomputable def phi43EnlargedBase (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (a : ParabolicSpace) :
    ParabolicSpace → SymbolF → ParabolicSpace → ℝ := fun x i y =>
  match i with
  | .old τ => phi43BaseFunctions N κ noise C (x + a) τ (y + a)
  | .planted _ => 0

theorem isSmoothFunctionModelBelow_phi43EnlargedBase (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (a : ParabolicSpace)
    {M' : Model (phi43RegularityStructureF κ) parabolicSemigroup}
    (hC : EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate a) M') :
    M'.IsSmoothFunctionModelBelow (phi43EnlargedBase N κ noise C a) κ.1 := by
  have hk : 0 < κ.1 := κ.2.1
  have hZ := isSmoothFunctionModelBelow_phi43BaseFunctions N κ noise C hg
    (canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C)
  have hold : ∀ i : SymbolF, (phi43RegularityStructureF κ).deg i < κ.1 → ∃ τ : Symbol,
      i = .old τ ∧ homogeneity κ τ < κ.1 := by
    intro i hi
    cases i with
    | planted p =>
        have := phi43DegreeF_planted_ge κ p
        exfalso
        have h2 : (phi43RegularityStructureF κ).deg (.planted p) = phi43DegreeF κ (.planted p) := rfl
        linarith [κ.2.2]
    | old τ => exact ⟨τ, rfl, hi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x i hi t ht y
    obtain ⟨τ, rfl, hτ⟩ := hold i hi
    rw [hC.regPi_single, Model.regPi_translate, hZ.regPi_eq (x + a) τ hτ t ht (y + a),
      ← parabolicSemigroup_apply_translate]
    rfl
  · intro i hi
    obtain ⟨τ, rfl, hτ⟩ := hold i hi
    have h1 : Continuous fun p : ParabolicSpace × ParabolicSpace => (p.1 + a, p.2 + a) :=
      (continuous_fst.add continuous_const).prodMk (continuous_snd.add continuous_const)
    have e : (fun p : ParabolicSpace × ParabolicSpace =>
        phi43EnlargedBase N κ noise C a p.1 (.old τ) p.2) = fun p =>
        phi43BaseFunctions N κ noise C (p.1 + a) τ (p.2 + a) := rfl
    rw [e]
    have hc := hZ.continuous τ hτ
    exact Continuous.comp (g := fun p : ParabolicSpace × ParabolicSpace =>
      phi43BaseFunctions N κ noise C p.1 τ p.2) (f := fun p : ParabolicSpace × ParabolicSpace =>
      (p.1 + a, p.2 + a)) hc h1
  · intro x i hi
    obtain ⟨τ, rfl, hτ⟩ := hold i hi
    obtain ⟨B, n, hB⟩ := hZ.growth (x + a) τ hτ
    have hB0 : 0 ≤ B := by
      have := (abs_nonneg _).trans (hB 0)
      rw [parabolicNorm_zero] at this; simpa using this
    refine ⟨B * (1 + parabolicNorm a) ^ n, n, fun u => ?_⟩
    have h1 := one_add_parabolicNorm_le (u + a) a
    rw [add_sub_cancel_right] at h1
    have h2 : (1 + parabolicNorm (u + a)) ^ n ≤ ((1 + parabolicNorm a) * (1 + parabolicNorm u)) ^ n :=
      pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg (u + a)]) h1 n
    calc |phi43EnlargedBase N κ noise C a x (.old τ) u| ≤ B * (1 + parabolicNorm (u + a)) ^ n :=
          hB (u + a)
      _ ≤ B * ((1 + parabolicNorm a) * (1 + parabolicNorm u)) ^ n :=
          mul_le_mul_of_nonneg_left h2 hB0
      _ = _ := by rw [mul_pow]; ring
  · obtain ⟨B, n, hB⟩ := hZ.diag_growth
    have hB0 : 0 ≤ B := by
      have := (abs_nonneg _).trans (hB 0 .one (by simp [phi43RegularityStructure, homogeneity, hk]))
      rw [parabolicNorm_zero] at this; simpa using this
    refine ⟨B * (1 + parabolicNorm a) ^ n, n, fun y i hi => ?_⟩
    obtain ⟨τ, rfl, hτ⟩ := hold i hi
    have h1 := one_add_parabolicNorm_le (y + a) a
    rw [add_sub_cancel_right] at h1
    have h2 : (1 + parabolicNorm (y + a)) ^ n ≤ ((1 + parabolicNorm a) * (1 + parabolicNorm y)) ^ n :=
      pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg (y + a)]) h1 n
    calc |phi43EnlargedBase N κ noise C a y (.old τ) y| ≤ B * (1 + parabolicNorm (y + a)) ^ n :=
          hB (y + a) τ hτ
      _ ≤ B * ((1 + parabolicNorm a) * (1 + parabolicNorm y)) ^ n :=
          mul_le_mul_of_nonneg_left h2 hB0
      _ = _ := by rw [mul_pow]; ring

end RegularityStructures.Phi43

end
