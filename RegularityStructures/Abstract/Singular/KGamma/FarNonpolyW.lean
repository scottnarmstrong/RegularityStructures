/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.DecompW
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Singular Schauder: non-polynomial components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)`, window models

Window (`_win`) version of the far-pair bound on the non-polynomial components.
For `f ∈ D^{γ,η}_P` on the time slab and `x, y` in the slab with `d(y, x) ≤ ‖x, y‖_P`, the
non-polynomial components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` equal `(I τ)_j`, `τ = f(y) − Γ_{yx} f(x)`,
and satisfy `≤ |ι| C_I C_f d^{γ+2−deg j} ‖x, y‖_P^{α∧η − γ}` ([Hai14, Prop. 6.16]).  The bound
uses no model bound (only the singular bound on `f`); the identity uses the
qualitative Lemma 5.16 (`DecompW`).
-/

public section

open Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

/-- The non-polynomial components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` are those of
`I (f(y) − Γ_{yx} f(x))`. -/
theorem kGammaS_sub_gamma_apply_of_notMem_range_win {M : Model 𝒯 parabolicSemigroup}
    {h : ParabolicSpace → ℝ} {N : ℕ} {γ : ℝ}
    {P : PolynomialSector 𝒯 N'}
    {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hh : ShellProfile h N) (hreal : M.IsRealisingP h γ P I V) (hI : IsAbstractIntegration P V I 2)
    (hV : 𝒯.IsSector V) (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hdeg : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hgrowth : ∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ),
      M.GrowthModel γ C' C'' ρP ρG p q)
    (hN' : ∀ j, (Pi.single j 1 : ι → ℝ) ∈ V → 𝒯.deg j < γ → ∀ k : Fin 4 →₀ ℕ,
      (multiDeg k : ℝ) < 𝒯.deg j + 2 → multiDeg k < N')
    {f : ParabolicSpace → ι → ℝ} (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (hfV : ∀ x, f x ∈ V)
    {j : ι} (hj : j ∉ Set.range P.emb) (x y : ParabolicSpace) :
    (kGammaS M h P I γ f y - M.gammaMap y x (kGammaS M h P I γ f x)) j =
      I (f y - M.gammaMap y x (f x)) j := by
  rw [kGammaS_sub_gamma_eq_win hh hreal hI hV hVb hdeg hgrowth hN' hf hfV x y]
  have hpoly : ∀ v ∈ P.subspace, v j = 0 := fun v hv => hv j hj
  have hJ := hpoly _ (jMapP_mem_subspace M h P y (f y - M.gammaMap y x (f x)))
  have hN1 := hpoly _ (nVecS_mem_subspace M h P γ f y)
  have hN2 : M.gammaMap y x (nVecS M h P γ f x) j = 0 :=
    hpoly _ (P.invariant _ (M.gamma y x).2 _ (nVecS_mem_subspace M h P γ f x))
  simp only [Pi.add_apply, Pi.sub_apply] at hJ hN1 hN2 ⊢
  rw [hJ, hN1, hN2]; ring

end Model

end RegularityStructures

end
