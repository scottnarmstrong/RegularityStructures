/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Commute.Reg
public import RegularityStructures.Abstract.Integration.Commute.Germ
public import RegularityStructures.Abstract.Integration.JMapDef
public import RegularityStructures.Abstract.Integration.Realising.RealisesKernel
public import RegularityStructures.Analysis.Semigroup.ConsistencyLimit

/-!
# `Q_t Π_x (I + J(x)) e_i = Q_t (K ∗ Π_x e_i)`

For a realising, polynomially compatible model and a basis vector `e_i ∈ V` with `deg i < γ`,

  `(Q_t Π_x (I e_i + J(x) e_i))(z) = Q_t (kConv N (Π_x e_i)) (z)`  for `t > 0`

(`regPi_integral_add_jMap`; [Hai14, proof of Lemma 5.16]). Indeed `Q_t Π_x I e_i = Q_t g_{x,i}`
(`RealisesKernel`) and `Π_x J(x) e_i` is the polynomial `∑_k jCoeff/k! (· - x)^k`
(`IsPolyCompatible`), and `g_{x,i} + ∑_k jCoeff/k! (· - x)^k = kConv N (Π_x e_i)` by the germ identity
`realGerm_eq`. The hypothesis `hN'` says that `jVec` uses exactly the multi-indices
`taylorIdx (deg i + 2)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

/-- The coefficient vector of `J(x) e_i` in the abstract polynomials. -/
noncomputable def jPolyCoeff (M : Model 𝒯 parabolicSemigroup) (N : ℕ)
    (x : ParabolicSpace) (i : ι) : PolyIndex N' → ℝ := fun k =>
  if polyDeg N' k < 𝒯.deg i + 2 then jCoeff M N x i k.1 / multiFactorial k.1 else 0

theorem jVec_eq_polyEmbed (M : Model 𝒯 parabolicSemigroup) (N : ℕ) (P : PolynomialSector 𝒯 N')
    (x : ParabolicSpace) (i : ι) : jVec M N P x i = P.polyEmbed (jPolyCoeff (N' := N') M N x i) := by
  classical
  unfold jVec PolynomialSector.polyEmbed jPolyCoeff
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- `∑_{k : PolyIndex N'} σ_k (z - x)^k` is the Taylor sum over `taylorIdx (deg i + 2)`. -/
theorem polyEval_jPolyCoeff (M : Model 𝒯 parabolicSemigroup) (N : ℕ)
    (x : ParabolicSpace) (i : ι)
    (hN' : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg i + 2 → multiDeg k < N') (z : ParabolicSpace) :
    polyEval x (jPolyCoeff (N' := N') M N x i) z = ∑ k ∈ taylorIdx (𝒯.deg i + 2),
      (evalParabolic (MvPolynomial.monomial k 1) (z - x) / multiFact k) * jCoeff M N x i k := by
  classical
  rw [polyEval_eq_sum]
  set F : (Fin 4 →₀ ℕ) → ℝ := fun l =>
    if (multiDeg l : ℝ) < 𝒯.deg i + 2 then
      (evalParabolic (MvPolynomial.monomial l 1) (z - x) / multiFact l) * jCoeff M N x i l
    else 0 with hF
  have h1 : ∀ k : PolyIndex N', jPolyCoeff (N' := N') M N x i k *
      evalParabolic (MvPolynomial.monomial k.1 1) (z - x) = F k.1 := by
    intro k
    unfold jPolyCoeff
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

namespace Model

/-- **Target 3** [Hai14, proof of Lemma 5.16]: for a realising, polynomially compatible model and
`e_i ∈ V`, `Q_t Π_x (I e_i + J(x) e_i) = Q_t (K ∗ Π_x e_i)` for `t > 0`. -/
theorem regPi_integral_add_jMap {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam : ℝ}
    {P : PolynomialSector 𝒯 N'} {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}
    (hreal : M.IsRealising N γ P I V) (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    {i : ι} (hi : 𝒯.deg i < γ) (hV : (Pi.single i 1 : ι → ℝ) ∈ V)
    (hN' : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < 𝒯.deg i + 2 → multiDeg k < N')
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    M.regPi x (I (Pi.single i 1) + jMap M N P x (Pi.single i 1)) t z =
      parabolicSemigroup.apply t (kConv N (fun t w => M.regPi x (Pi.single i 1) t w)) z := by
  have hR := M.kRegular_regPi_single hdeg hPi hGam hCPi hi x
  have hK := hR.polyBounded_kConv N
  have hσ := polyBounded_polyEval x (jPolyCoeff (N' := N') M N x i)
  have hG : PolyBounded (realGerm M N x i) := by
    have e : realGerm M N x i = fun w => kConv N (fun t w => M.regPi x (Pi.single i 1) t w) w -
        polyEval x (jPolyCoeff (N' := N') M N x i) w := by
      funext w
      rw [realGerm_eq M N hdeg hPi hGam hCPi hi x w, polyEval_jPolyCoeff M N x i hN' w]
    rw [e]
    exact hK.sub hσ
  rw [M.regPi_add, hreal.realises x i hi hV t ht z, realReg_of_pos M N x i ht,
    jMap_single, jVec_eq_polyEmbed, regPi_polyEmbed hreal.poly, polyReg_of_pos _ _ ht,
    ← hG.apply_add hσ ht z]
  congr 1
  funext w
  rw [realGerm_eq M N hdeg hPi hGam hCPi hi x w, polyEval_jPolyCoeff M N x i hN' w]
  ring

end Model

end RegularityStructures

end
