/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.Inject
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Model

/-!
# Polynomial-compatible models: injectivity on `T̄` and `Γ` on polynomials

For `M.IsPolyCompatible P` (`Π_x X^k = (· - x)^k`, [Hai14, Definition 5.9]):

* `regPi_polyEmbed`: `Q_t Π_x (∑ σ_k e_{emb k}) = Q_t (· - x)^σ`;
* `eq_zero_of_regPi_eq_zero`: `Π_x` is injective on `P.subspace` (in the `Q`-family sense);
* `gammaMap_single_emb`: `Γ_{xy} X^k` is the image under `emb` of the translated polynomial.

These are the inputs for [Hai14, Lemma 5.16].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace PolynomialSector

/-- The image `∑_k σ_k e_{emb k}` of a coefficient vector `σ` in `T̄`. -/
def polyEmbed (P : PolynomialSector 𝒯 N') (σ : PolyIndex N' → ℝ) : ι → ℝ :=
  ∑ k, σ k • (Pi.single (P.emb k) 1 : ι → ℝ)

end PolynomialSector

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace PolynomialSector

theorem polyEmbed_apply_emb (P : PolynomialSector 𝒯 N') (σ : PolyIndex N' → ℝ) (k : PolyIndex N') :
    P.polyEmbed σ (P.emb k) = σ k := by
  simp only [polyEmbed, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [P.emb_injective.ne hl.symm]
  · simp

theorem polyEmbed_apply_of_notMem (P : PolynomialSector 𝒯 N') (σ : PolyIndex N' → ℝ) {i : ι}
    (hi : i ∉ Set.range P.emb) : P.polyEmbed σ i = 0 := by
  simp only [polyEmbed, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun l _ => ?_
  have : i ≠ P.emb l := fun h => hi ⟨l, h.symm⟩
  simp [this]

theorem polyEmbed_mem (P : PolynomialSector 𝒯 N') (σ : PolyIndex N' → ℝ) :
    P.polyEmbed σ ∈ P.subspace := fun _ hi => P.polyEmbed_apply_of_notMem σ hi

theorem eq_polyEmbed_of_mem (P : PolynomialSector 𝒯 N') {τ : ι → ℝ} (hτ : τ ∈ P.subspace) :
    τ = P.polyEmbed (fun k => τ (P.emb k)) := by
  funext i
  by_cases hi : i ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hi
    rw [P.polyEmbed_apply_emb]
  · rw [P.polyEmbed_apply_of_notMem _ hi, hτ i hi]

end PolynomialSector

namespace Model

variable {M : Model 𝒯 parabolicSemigroup}

/-- For a polynomial-compatible model, `Q_t Π_x (∑ σ_k e_{emb k}) = Q_t (· - x)^σ`. -/
theorem regPi_polyEmbed {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P)
    (x : ParabolicSpace) (σ : PolyIndex N' → ℝ) (t : ℝ) (z : ParabolicSpace) :
    M.regPi x (P.polyEmbed σ) t z = polyReg x σ t z := by
  rw [M.regPi_eq_sum, polyReg_eq_sum]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.emb)) ?_,
    Finset.sum_image (fun a _ b _ h => P.emb_injective h)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [P.polyEmbed_apply_emb, hM x k t z]
  · intro i _ hi
    have : i ∉ Set.range P.emb := fun ⟨k, hk⟩ => hi (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩)
    rw [P.polyEmbed_apply_of_notMem σ this, zero_mul]

/-- Target 2: for a polynomial-compatible model, `τ ↦ (Q_t Π_x τ)_{t>0}` is injective on `T̄`. -/
theorem eq_zero_of_regPi_eq_zero {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P)
    (x : ParabolicSpace) {τ : ι → ℝ} (hτ : τ ∈ P.subspace)
    (h : ∀ t : ℝ, 0 < t → ∀ z, M.regPi x τ t z = 0) : τ = 0 := by
  have hσ : (fun k => τ (P.emb k)) = 0 := by
    refine polyReg_injective x fun t ht z => ?_
    rw [← regPi_polyEmbed hM, ← P.eq_polyEmbed_of_mem hτ]
    exact h t ht z
  rw [P.eq_polyEmbed_of_mem hτ, hσ]
  funext i
  by_cases hi : i ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hi
    rw [P.polyEmbed_apply_emb]; rfl
  · rw [P.polyEmbed_apply_of_notMem _ hi]; rfl

/-- Target 3: `Γ_{xy} X^k` is the image under `emb` of the translated polynomial. -/
theorem gammaMap_single_emb {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P)
    (x y : ParabolicSpace) (k : PolyIndex N') :
    M.gammaMap x y (Pi.single (P.emb k) 1) =
      ∑ l, polyTranslate (parabolicCoords (x - y)) (Pi.single k 1) l •
        (Pi.single (P.emb l) 1 : ι → ℝ) := by
  change _ = P.polyEmbed _
  have hmem : M.gammaMap x y (Pi.single (P.emb k) 1) ∈ P.subspace := by
    intro i hi
    refine P.invariant (M.gamma x y).1 (M.gamma x y).2 _ (fun j hj => ?_) i hi
    simp [show j ≠ P.emb k from fun h => hj ⟨k, h.symm⟩]
  have hd : M.gammaMap x y (Pi.single (P.emb k) 1) -
      P.polyEmbed (polyTranslate (parabolicCoords (x - y)) (Pi.single k 1)) = 0 := by
    refine eq_zero_of_regPi_eq_zero hM x (Submodule.sub_mem _ hmem (P.polyEmbed_mem _))
      fun t ht z => ?_
    rw [M.regPi_sub, M.regPi_gammaMap, regPi_polyEmbed hM, hM y k t z,
      polyReg_of_pos _ _ ht, polyReg_of_pos _ _ ht, sub_eq_zero]
    congr 1
    funext w
    exact (polyEval_polyTranslate x y _ w).symm
  exact sub_eq_zero.1 hd

end Model

end RegularityStructures

end
