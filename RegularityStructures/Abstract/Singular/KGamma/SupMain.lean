/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.KGamma.Emb

/-!
# Sup bounds for `𝒦_γ f`, the singular case with the lattice reconstruction

For `f ∈ D^{γ,η}_P` on the time slab `(0, T] × ℝ³` with values in a sector of regularity `α`,
`α ∧ η > −2`, a causal shell profile `h`, and an abstract integration map `I` raising degrees by `2`
(with `ηK = α ∧ η + 2`), `x` in the slab, `w = ‖x‖_P`:

* `exists_abs_kGammaS_apply_emb_le`: `|(𝒦_γ f(x))_{X^k}| ≤ C K₀ C_f w^{ηK − |k|}` for `|k| < γ + 2`
  (assuming `|k| ≠ deg i + 2` for the relevant `i`);
* `abs_kGammaS_apply_le_of_notMem_range`: `|(𝒦_γ f(x))_j| ≤ |ι| C_I C_f w^{ηK − deg j}`
  for the non-polynomial components `j`;
* `kGammaS_mem_lowerSubspace`: `𝒦_γ f(x) ∈ T_{<γ+2}`;
* `summable_singShellPairing`: the series `nCoeffS` converges absolutely.

Source: [Hai14] = arXiv:1303.5113v4, (5.15)–(5.16), Prop. 6.16 (sup part), Thm. 7.1.
-/

public section

open Set Filter

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {N : ℕ} {h : ParabolicSpace → ℝ}

theorem nVecS_apply_of_notMem_range (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (P : PolynomialSector 𝒯 N') (γ : ℝ) (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace)
    {j : ι} (hj : j ∉ Set.range P.emb) : M.nVecS h P γ f x j = 0 := by
  classical
  unfold nVecS
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul]
    have : (Pi.single (P.emb k) 1 : ι → ℝ) j = 0 := by
      have hne : j ≠ P.emb k := fun e => hj ⟨k, e.symm⟩
      simp [hne]
    rw [this, mul_zero]
  · rfl

theorem kGammaS_apply_of_notMem_range (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (P : PolynomialSector 𝒯 N') (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (γ : ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) {j : ι} (hj : j ∉ Set.range P.emb) :
    M.kGammaS h P I γ f x j = I (f x) j := by
  have h1 := jMapP_mem_subspace M h P x (f x) j hj
  have h2 := nVecS_apply_of_notMem_range M h P γ f x hj
  simp only [kGammaS, Pi.add_apply, h1, h2, add_zero]

/-- `𝒦_γ f(x) ∈ T_{<γ+2}`. -/
theorem kGammaS_mem_lowerSubspace {γ : ℝ} {M : Model 𝒯 parabolicSemigroup}
    {f : ParabolicSpace → ι → ℝ} (h : ParabolicSpace → ℝ) (P : PolynomialSector 𝒯 N')
    (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (V : Submodule ℝ (ι → ℝ))
    (hVb : ∀ a ∈ V, ∀ j, a j ≠ 0 → (Pi.single j 1 : ι → ℝ) ∈ V)
    (hInt : IsAbstractIntegration P V I 2) (hIp : ∀ a ∈ V, ∀ kk : PolyIndex N', I a (P.emb kk) = 0)
    {x : ParabolicSpace} (hfV : f x ∈ V) (hfx : f x ∈ lowerSubspace 𝒯.deg γ) :
    M.kGammaS h P I γ f x ∈ lowerSubspace 𝒯.deg (γ + 2) := by
  rw [mem_lowerSubspace]
  intro j hj
  by_cases hjr : j ∈ Set.range P.emb
  · obtain ⟨kk, rfl⟩ := hjr
    have hdk : γ + 2 ≤ polyDeg N' kk := by rw [← P.deg_emb]; exact hj
    have hI0 : I (f x) (P.emb kk) = 0 := hIp _ hfV kk
    have hJ : ∑ i, f x i * (if polyDeg N' kk < 𝒯.deg i + 2 then
        jCoeffP M h x i kk.1 / multiFactorial kk.1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hfi : f x i = 0
      · rw [hfi, zero_mul]
      · have hi : 𝒯.deg i < γ := by
          by_contra hge
          exact hfi ((mem_lowerSubspace).1 hfx i (not_lt.1 hge))
        have : ¬ polyDeg N' kk < 𝒯.deg i + 2 := by linarith
        simp [this]
    have hk2 : ¬ polyDeg N' kk < γ + 2 := not_lt.2 hdk
    simp only [kGammaS, Pi.add_apply, hI0, jMapP_apply_emb, nVecS_apply_emb, hk2, ↓reduceIte, hJ,
      add_zero]
  · rw [kGammaS_apply_of_notMem_range M h P I γ _ x hjr, linearMap_apply_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hfi : f x i = 0
    · rw [hfi, zero_mul]
    · have hi : 𝒯.deg i < γ := by
        by_contra hge
        exact hfi ((mem_lowerSubspace).1 hfx i (not_lt.1 hge))
      have hIi : I (Pi.single i 1) ∈ homogeneousSubspace 𝒯.deg (𝒯.deg i + 2) :=
        hInt.map_homogeneous _ _ (hVb _ hfV i hfi) (single_mem_homogeneousSubspace i 1)
      have hne : ¬ 𝒯.deg j = 𝒯.deg i + 2 := by
        intro h'; linarith
      rw [hIi j hne, mul_zero]

end Model

end RegularityStructures

end
