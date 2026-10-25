/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Profile.Realising
public import RegularityStructures.Abstract.Integration.Sector.Commute
public import RegularityStructures.Abstract.Integration.PolyCompat.Compat
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.JMap
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# The germ of the realised integral as `K ∗ Π_x e_i` minus a Taylor polynomial

The germ identity of [Hai14, Remark 5.10] for a general kernel profile `h`. When all homogeneities
below `γ` (or those of the basis vectors in the sector `V`) exceed `-2`, `Π_x e_i` is `KRegular` at
`x`, so `K ∗ Π_x e_i = kConvP h (Π_x e_i)` is a function, and the germ `realGermP M h x i` of
[Hai14, Remark 5.10] is this function minus the Taylor polynomial of `K ∗ Π_x e_i` at `x` of order
`deg i + 2`, with the coefficients of `J(x)` (`jCoeffP`) [Hai14, (5.11), (5.14)]:
  `realGermP M h x i z = kConvP h (Π_x e_i) z - ∑_{|k|_𝔰 < deg i + 2} (z - x)^k / k! · jCoeffP M h x i k`
(`realGerm_eqP`, `realGerm_eq_inP`).  `polyEval_jPolyCoeffP` identifies this Taylor sum with a
polynomial of the abstract polynomial sector.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

/-- The coefficient vector of `J(x) e_i` in the abstract polynomials. -/
def jPolyCoeffP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (i : ι) : PolyIndex N' → ℝ := fun k =>
  if polyDeg N' k < 𝒯.deg i + 2 then jCoeffP M h x i k.1 / multiFactorial k.1 else 0

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}
  {h : ParabolicSpace → ℝ} {N : ℕ} {V : Submodule ℝ (ι → ℝ)}

theorem jVec_eq_polyEmbedP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ) (P : PolynomialSector 𝒯 N')
    (x : ParabolicSpace) (i : ι) : jVecP M h P x i = P.polyEmbed (jPolyCoeffP (N' := N') M h x i) := by
  classical
  unfold jVecP PolynomialSector.polyEmbed jPolyCoeffP
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- `∑_{k : PolyIndex N'} σ_k (z - x)^k` is the Taylor sum over `taylorIdx (deg i + 2)`. -/
theorem polyEval_jPolyCoeffP (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (i : ι)
    (hN' : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg i + 2 → multiDeg k < N') (z : ParabolicSpace) :
    polyEval x (jPolyCoeffP (N' := N') M h x i) z = ∑ k ∈ taylorIdx (𝒯.deg i + 2),
      (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) * jCoeffP M h x i k := by
  classical
  rw [polyEval_eq_sum]
  set F : (Fin 4 →₀ ℕ) → ℝ := fun l =>
    if (multiDeg l : ℝ) < 𝒯.deg i + 2 then
      (evalParabolic (MvPolynomial.monomial l 1) (z - x) / multiFact l) * jCoeffP M h x i l
    else 0 with hF
  have h1 : ∀ k : PolyIndex N', jPolyCoeffP (N' := N') M h x i k *
      evalParabolic (MvPolynomial.monomial k.1 1) (z - x) = F k.1 := by
    intro k
    unfold jPolyCoeffP
    have hd : polyDeg N' k = (multiDeg k.1 : ℝ) := rfl
    have hm : (multiFactorial k.1 : ℝ) = multiFact k.1 := by
      unfold multiFactorial multiFact; push_cast; rfl
    rw [hd, hF]
    dsimp only
    split_ifs
    · rw [hm]; ring
    · simp
  simp only [h1]
  have h2 : ∑ k : PolyIndex N', F k.1 = ∑ l ∈ Finset.univ.image (Subtype.val : PolyIndex N' → _),
      F l := (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
  rw [h2, ← Finset.sum_subset (s₁ := taylorIdx (𝒯.deg i + 2))]
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [hF]
    simp [(mem_taylorIdx_iff l).1 hl]
  · intro l hl
    refine Finset.mem_image.2 ⟨⟨l, ?_⟩, Finset.mem_univ _, rfl⟩
    exact hN' l ((mem_taylorIdx_iff l).1 hl)
  · intro l _ hl
    rw [hF]
    simp [(mem_taylorIdx_iff l).not.1 hl]

end RegularityStructures

end
