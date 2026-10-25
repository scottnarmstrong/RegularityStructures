/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.Compat

/-!
# The difference model: block vectors and the polynomial facts

For a polynomial sector `P` of `𝒯` let `ι₀ = NonPoly P` be the non-polynomial symbols and
`ι⊕ = ι₀ ⊕ ι`, with degrees `degSum P`. A vector of `ι⊕ → ℝ` is a pair `(a, b)` with
`a : ι₀ → ℝ`, `b : ι → ℝ` (`leftPart`, `rightPart`, `pairVec`). `restrictNP` is the restriction
`Q : (ι → ℝ) → (ι₀ → ℝ)` and `extendNP` the zero extension `E₀`. `blockMap F G H` is the
block-triangular map `(a, b) ↦ (F a, G a + H b)`.

For polynomial-compatible models `M₁, M₂` the maps `Γ¹_{xy}`, `Γ²_{xy}` agree on `P.subspace`
(`gammaMap_eq_of_mem_subspace`) and `Π¹_x - Π²_x` vanishes there (`regPi_sub_eq_zero`); these
are the inputs for the difference model, which reduces the two-model half of Hairer
[Hai14, Theorem 7.1] to the single-model one.
-/

@[expose] public noncomputable section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

/-- The non-polynomial symbols `ι₀ = {i : ι // i ∉ range P.emb}`. -/
abbrev NonPoly (P : PolynomialSector 𝒯 N') : Type _ := {i : ι // i ∉ Set.range P.emb}

instance (P : PolynomialSector 𝒯 N') : Fintype (NonPoly P) := Fintype.ofFinite _

/-- The degrees on `ι⊕ = ι₀ ⊕ ι`: `deg⊕ (inl i) = deg i`, `deg⊕ (inr j) = deg j`. -/
def degSum (P : PolynomialSector 𝒯 N') : NonPoly P ⊕ ι → ℝ :=
  Sum.elim (fun i => 𝒯.deg i.1) 𝒯.deg

/-- The restriction `Q : (ι → ℝ) → (ι₀ → ℝ)` to the non-polynomial coordinates. -/
def restrictNP (P : PolynomialSector 𝒯 N') : (ι → ℝ) →ₗ[ℝ] (NonPoly P → ℝ) where
  toFun w i := w i.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
/-- The zero extension `E₀ : (ι₀ → ℝ) → (ι → ℝ)`. -/
def extendNP (P : PolynomialSector 𝒯 N') : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a i := if h : i ∈ Set.range P.emb then 0 else a ⟨i, h⟩
  map_add' a b := by
    funext i
    by_cases h : i ∈ Set.range P.emb
    · simp only [Pi.add_apply, h, ↓reduceDIte, add_zero]
    · simp only [Pi.add_apply, h, ↓reduceDIte]
  map_smul' c a := by
    funext i
    by_cases h : i ∈ Set.range P.emb
    · simp only [Pi.smul_apply, h, ↓reduceDIte, smul_zero, RingHom.id_apply]
    · simp only [Pi.smul_apply, h, ↓reduceDIte, RingHom.id_apply]

/-- The left part `a` of a vector `(a, b)` of `ι⊕ → ℝ`. -/
def leftPart (P : PolynomialSector 𝒯 N') : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P → ℝ) where
  toFun v i := v (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The right part `b` of a vector `(a, b)` of `ι⊕ → ℝ`. -/
def rightPart (P : PolynomialSector 𝒯 N') : (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v j := v (Sum.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The vector `(a, b)` of `ι⊕ → ℝ`. -/
def pairVec (P : PolynomialSector 𝒯 N') (a : NonPoly P → ℝ) (b : ι → ℝ) : NonPoly P ⊕ ι → ℝ :=
  Sum.elim a b

/-- The block-triangular map `(a, b) ↦ (F a, G a + H b)`. -/
def blockMap (P : PolynomialSector 𝒯 N') (F : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ))
    (G : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (H : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    (NonPoly P ⊕ ι → ℝ) →ₗ[ℝ] (NonPoly P ⊕ ι → ℝ) where
  toFun v := pairVec P (F (leftPart P v)) (G (leftPart P v) + H (rightPart P v))
  map_add' v w := by
    funext s
    rcases s with i | j
    · simp only [pairVec, Sum.elim_inl, map_add, Pi.add_apply]
    · simp only [pairVec, Sum.elim_inr, map_add, Pi.add_apply]
      abel
  map_smul' c v := by
    funext s
    rcases s with i | j
    · simp only [pairVec, Sum.elim_inl, map_smul, Pi.smul_apply, RingHom.id_apply]
    · simp only [pairVec, Sum.elim_inr, map_smul, Pi.smul_apply, RingHom.id_apply,
        Pi.add_apply, smul_eq_mul, mul_add]

end TwoModel

end RegularityStructures

end

public section

namespace RegularityStructures

namespace TwoModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  (P : PolynomialSector 𝒯 N')

@[simp] theorem degSum_inl (i : NonPoly P) : degSum P (Sum.inl i) = 𝒯.deg i.1 := rfl

@[simp] theorem degSum_inr (j : ι) : degSum P (Sum.inr j) = 𝒯.deg j := rfl

@[simp] theorem restrictNP_apply (w : ι → ℝ) (i : NonPoly P) : restrictNP P w i = w i.1 := rfl

theorem extendNP_apply_of_notMem (a : NonPoly P → ℝ) {i : ι} (hi : i ∉ Set.range P.emb) :
    extendNP P a i = a ⟨i, hi⟩ := by
  simp [extendNP, hi]

theorem extendNP_apply_of_mem (a : NonPoly P → ℝ) {i : ι} (hi : i ∈ Set.range P.emb) :
    extendNP P a i = 0 := by
  simp [extendNP, hi]

@[simp] theorem extendNP_apply_val (a : NonPoly P → ℝ) (i : NonPoly P) :
    extendNP P a i.1 = a i :=
  extendNP_apply_of_notMem P a i.2

@[simp] theorem restrictNP_extendNP (a : NonPoly P → ℝ) : restrictNP P (extendNP P a) = a := by
  funext i
  simp

@[simp] theorem leftPart_apply (v : NonPoly P ⊕ ι → ℝ) (i : NonPoly P) :
    leftPart P v i = v (Sum.inl i) := rfl

@[simp] theorem rightPart_apply (v : NonPoly P ⊕ ι → ℝ) (j : ι) :
    rightPart P v j = v (Sum.inr j) := rfl

@[simp] theorem pairVec_inl (a : NonPoly P → ℝ) (b : ι → ℝ) (i : NonPoly P) :
    pairVec P a b (Sum.inl i) = a i := rfl

@[simp] theorem pairVec_inr (a : NonPoly P → ℝ) (b : ι → ℝ) (j : ι) :
    pairVec P a b (Sum.inr j) = b j := rfl

@[simp] theorem leftPart_pairVec (a : NonPoly P → ℝ) (b : ι → ℝ) :
    leftPart P (pairVec P a b) = a := rfl

@[simp] theorem rightPart_pairVec (a : NonPoly P → ℝ) (b : ι → ℝ) :
    rightPart P (pairVec P a b) = b := rfl

theorem pairVec_leftPart_rightPart (v : NonPoly P ⊕ ι → ℝ) :
    pairVec P (leftPart P v) (rightPart P v) = v := by
  funext s
  rcases s with i | j <;> rfl

theorem pairVec_sub (a a' : NonPoly P → ℝ) (b b' : ι → ℝ) :
    pairVec P (a - a') (b - b') = pairVec P a b - pairVec P a' b' := by
  funext s
  rcases s with i | j <;> rfl

@[simp] theorem blockMap_apply_inl (F : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ))
    (G : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (H : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : NonPoly P ⊕ ι → ℝ)
    (i : NonPoly P) :
    blockMap P F G H v (Sum.inl i) = F (leftPart P v) i := rfl

@[simp] theorem blockMap_apply_inr (F : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ))
    (G : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (H : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : NonPoly P ⊕ ι → ℝ)
    (j : ι) :
    blockMap P F G H v (Sum.inr j) = G (leftPart P v) j + H (rightPart P v) j := rfl

@[simp] theorem leftPart_blockMap (F : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ))
    (G : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (H : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : NonPoly P ⊕ ι → ℝ) :
    leftPart P (blockMap P F G H v) = F (leftPart P v) := rfl

@[simp] theorem rightPart_blockMap (F : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ))
    (G : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (H : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : NonPoly P ⊕ ι → ℝ) :
    rightPart P (blockMap P F G H v) = G (leftPart P v) + H (rightPart P v) := rfl

theorem blockMap_comp (F F' : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ))
    (G G' : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)) (H H' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    blockMap P F G H ∘ₗ blockMap P F' G' H' =
      blockMap P (F ∘ₗ F') (G ∘ₗ F' + H ∘ₗ G') (H ∘ₗ H') := by
  refine LinearMap.ext fun v => ?_
  funext s
  rcases s with i | j <;> simp [add_assoc]

theorem blockMap_ext {F F' : (NonPoly P → ℝ) →ₗ[ℝ] (NonPoly P → ℝ)}
    {G G' : (NonPoly P → ℝ) →ₗ[ℝ] (ι → ℝ)} {H H' : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)}
    (hF : F = F') (hG : G = G') (hH : H = H') : blockMap P F G H = blockMap P F' G' H' := by
  subst hF hG hH; rfl

theorem blockMap_id : blockMap P LinearMap.id 0 LinearMap.id = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  funext s
  rcases s with i | j <;> simp

/-- A vector `w` differs from `E₀ Q w` by a polynomial vector. -/
theorem sub_extendNP_restrictNP_mem (w : ι → ℝ) :
    w - extendNP P (restrictNP P w) ∈ P.subspace := by
  intro i hi
  have := extendNP_apply_of_notMem P (restrictNP P w) hi
  simp [this]

theorem restrictNP_eq_zero_of_mem_subspace {p : ι → ℝ} (hp : p ∈ P.subspace) :
    restrictNP P p = 0 := by
  funext i
  exact hp i.1 i.2

end TwoModel

end RegularityStructures

end
