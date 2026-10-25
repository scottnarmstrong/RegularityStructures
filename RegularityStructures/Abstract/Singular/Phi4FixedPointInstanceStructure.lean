/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Bounds
public import RegularityStructures.Abstract.Polynomial.Model.Unit
public import RegularityStructures.Abstract.Integration

/-!
# A structure on which the `Φ⁴₃` fixed-point hypotheses are satisfiable: the structure

`Phi4Inst.structure N'` is the regularity structure on `PolyIndex N' ⊕ Fin 2` with the polynomials
`X^k` (`inl k`, degree `|k|_𝔰`), a symbol `τ = inr 0` of degree `-1/2` and a symbol `σ = inr 1`
(playing `Iτ`) of degree `3/2`.  The structure group consists of the polynomial translations `Γ_h`
acting as the identity on `τ` and `σ`.  The polynomial sector is `inl`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi4Inst

/-- The index set: polynomials and two extra symbols. -/
abbrev Idx (N' : ℕ) : Type := PolyIndex N' ⊕ Fin 2

variable {N' : ℕ}

/-- The index of `τ`. -/
def tauIdx (N' : ℕ) : Idx N' := Sum.inr 0

/-- The index of `σ = Iτ`. -/
def sigmaIdx (N' : ℕ) : Idx N' := Sum.inr 1

/-- The degrees of the two extra symbols: `|τ| = -1/2`, `|σ| = 3/2`. -/
def extDeg (e : Fin 2) : ℝ := if e = 0 then -1 / 2 else 3 / 2

/-- The degrees: `|X^k|_𝔰`, `|τ| = -1/2`, `|σ| = 3/2`. -/
def deg (N' : ℕ) : Idx N' → ℝ := Sum.elim (polyDeg N') extDeg

/-- `A ⊕ id` on `Idx N' → ℝ`. -/
def extLin (A : (PolyIndex N' → ℝ) →ₗ[ℝ] (PolyIndex N' → ℝ)) :
    (Idx N' → ℝ) →ₗ[ℝ] (Idx N' → ℝ) where
  toFun τ i := Sum.elim (fun k => A (fun k' => τ (Sum.inl k')) k) (fun e => τ (Sum.inr e)) i
  map_add' τ σ := by
    funext i
    cases i with
    | inr e => rfl
    | inl k =>
      show A (fun k' => (τ + σ) (Sum.inl k')) k = _
      have : (fun k' => (τ + σ) (Sum.inl k')) =
          (fun k' => τ (Sum.inl k')) + (fun k' => σ (Sum.inl k')) := rfl
      rw [this, map_add]; rfl
  map_smul' c τ := by
    funext i
    cases i with
    | inr e => rfl
    | inl k =>
      show A (fun k' => (c • τ) (Sum.inl k')) k = _
      have : (fun k' => (c • τ) (Sum.inl k')) = c • (fun k' => τ (Sum.inl k')) := rfl
      rw [this, map_smul]; rfl

/-- The restriction to the polynomial coordinates. -/
def restrictLin : (Idx N' → ℝ) →ₗ[ℝ] (PolyIndex N' → ℝ) :=
  LinearMap.funLeft ℝ ℝ Sum.inl

theorem restrictLin_apply (τ : Idx N' → ℝ) (k : PolyIndex N') : restrictLin τ k = τ (Sum.inl k) :=
  rfl

theorem extLin_apply_inr (A : (PolyIndex N' → ℝ) →ₗ[ℝ] (PolyIndex N' → ℝ)) (τ : Idx N' → ℝ)
    (e : Fin 2) : extLin A τ (Sum.inr e) = τ (Sum.inr e) := rfl

theorem extLin_apply_inl (A : (PolyIndex N' → ℝ) →ₗ[ℝ] (PolyIndex N' → ℝ)) (τ : Idx N' → ℝ)
    (k : PolyIndex N') : extLin A τ (Sum.inl k) = A (restrictLin τ) k := rfl

/-- `A ↦ A ⊕ id` as a monoid homomorphism. -/
def extHom (N' : ℕ) : Module.End ℝ (PolyIndex N' → ℝ) →* Module.End ℝ (Idx N' → ℝ) where
  toFun := extLin
  map_one' := by
    refine LinearMap.ext fun τ => funext fun o => ?_
    cases o <;> rfl
  map_mul' A B := by
    refine LinearMap.ext fun τ => funext fun o => ?_
    cases o <;> rfl

theorem restrictLin_single_inl (k : PolyIndex N') :
    restrictLin (Pi.single (Sum.inl k) 1 : Idx N' → ℝ) = Pi.single k 1 := by
  funext k'
  simp [restrictLin_apply, Pi.single_apply]

theorem restrictLin_single_inr (e : Fin 2) :
    restrictLin (Pi.single (Sum.inr e) 1 : Idx N' → ℝ) = 0 := by
  funext k'
  simp [restrictLin_apply]

theorem extLin_single_inr (A : (PolyIndex N' → ℝ) →ₗ[ℝ] (PolyIndex N' → ℝ)) (e : Fin 2) :
    extLin A (Pi.single (Sum.inr e) 1 : Idx N' → ℝ) = Pi.single (Sum.inr e) 1 := by
  funext o
  cases o with
  | inr e' => rfl
  | inl k => rw [extLin_apply_inl, restrictLin_single_inr]; simp

/-- The regularity structure `{X^k} ∪ {τ, σ}` with translations acting trivially on `τ, σ`. -/
def «structure» (N' : ℕ) : RegularityStructure (Idx N') where
  deg := deg N'
  group := (polyGroup N').map (Units.map (extHom N'))
  isGradedUnipotent := by
    rintro g ⟨u, hu, rfl⟩
    have hU := (polynomialStructure N').isGradedUnipotent u hu
    intro i
    change extLin (u : Module.End ℝ (PolyIndex N' → ℝ)) (Pi.single i 1) - Pi.single i 1 ∈
      lowerSubspace (deg N') (deg N' i)
    cases i with
    | inr e =>
      rw [extLin_single_inr, sub_self]
      exact Submodule.zero_mem _
    | inl k =>
      intro o ho
      cases o with
      | inr e => simp [extLin_apply_inr]
      | inl j =>
        have h' : polyDeg N' k ≤ polyDeg N' j := by simpa [deg] using ho
        have := hU k j h'
        simp only [Pi.sub_apply, extLin_apply_inl, restrictLin_single_inl] at this ⊢
        simpa [Pi.single_apply] using this

theorem structure_deg_tau : («structure» N').deg (tauIdx N') = -1 / 2 := by
  simp [«structure», deg, tauIdx, extDeg]

theorem structure_deg_sigma : («structure» N').deg (sigmaIdx N') = 3 / 2 := by
  simp [«structure», deg, sigmaIdx, extDeg]

/-- The polynomial sector `inl`. -/
def polySector (N' : ℕ) : PolynomialSector («structure» N') N' where
  emb := Sum.inl
  emb_injective := Sum.inl_injective
  deg_emb _ := rfl
  invariant := by
    rintro g ⟨u, hu, rfl⟩ τ hτ i hi
    cases i with
    | inl k => exact absurd ⟨k, rfl⟩ hi
    | inr e =>
      show extLin (u : Module.End ℝ (PolyIndex N' → ℝ)) τ (Sum.inr e) = 0
      rw [extLin_apply_inr]
      exact hτ _ hi

end RegularityStructures.Phi4Inst

end
