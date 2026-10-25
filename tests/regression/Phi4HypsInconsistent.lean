/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Phi4FixedPointInstanceHyps

/-!
# The unrestricted non-integrality hypothesis is inconsistent

If the non-integrality hypothesis `hni` of the `Φ⁴₃` fixed point and of [Hai14, Theorem 7.1]
ranges over all indices, then together with `hγpos` and `hNγ` it contradicts `ζ ≤ 0`, for every
structure with a polynomial sector (`Regression.phi4_hyps_allIndices_inconsistent`): it then
quantifies also over `X⁰` (degree `0`) and `k = X₀` (`|k|_𝔰 = 2`).

The corresponding statement for `hni` restricted to the non-polynomial indices
(`i ∉ Set.range Ppoly.emb`), the form used by `Model.exists_unique_phi4_fixedPoint_causal_win_near`,
is false: the restricted hypothesis holds on the instance `Phi4Inst.«structure» 4` with
`ζ = -1/2` (`Regression.hni_nonPolynomial_on_instance`).
-/

open RegularityStructures

/-- The unrestricted `hni` is false when `ζ ≤ 0 < γ̄` and the structure has a polynomial sector
with `0 < N'`. -/
theorem Regression.hni_allIndices_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} {N' : ℕ} (Ppoly : PolynomialSector 𝒯 N') (hN' : 0 < N') {ζ γb : ℝ} (hζ : ζ ≤ 0)
    (hγ : 0 < γb) :
    ¬ (∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γb + 2 →
      ∀ i, ζ ≤ 𝒯.deg i → 𝒯.deg i < γb → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) := by
  intro h
  have hk : (multiDeg (Finsupp.single (0 : Fin 4) 1) : ℝ) = 2 := by
    simp [multiDeg, parabolicWeight, Finsupp.weight_single]
  have hdeg : 𝒯.deg (Ppoly.emb (polyZero hN')) = 0 := by
    rw [Ppoly.deg_emb, polyDeg_polyZero]
  exact h (Finsupp.single (0 : Fin 4) 1) (by rw [hk]; linarith) (Ppoly.emb (polyZero hN'))
    (by rw [hdeg]; exact hζ) (by rw [hdeg]; exact hγ) (by rw [hk, hdeg]; norm_num)

/-- `hNγ` at `l = 0` forces `0 < N'`. -/
theorem Regression.polyOrder_pos_of_hNγ {N' : ℕ} {γb : ℝ} (hγ : 0 < γb)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γb + 2 → multiDeg l < N') : 0 < N' := by
  have := hNγ 0 (by simp [multiDeg]; linarith)
  simpa [multiDeg] using this

/-- **With the unrestricted `hni`, the hypotheses of the `Φ⁴₃` fixed point are inconsistent for
`ζ ≤ 0`**: from `hγpos`, `hNγ`, the unrestricted `hni` and `ζ ≤ 0`, derive `False`. -/
theorem Regression.phi4_hyps_allIndices_inconsistent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} {N' : ℕ} (Ppoly : PolynomialSector 𝒯 N') {ζ γ₀ α : ℝ}
    (hζ : ζ ≤ 0) (hγpos : 0 < γ₀ + α + α)
    (hNγ : ∀ l : Fin 4 →₀ ℕ, (multiDeg l : ℝ) < γ₀ + α + α + 2 → multiDeg l < N')
    (hni : ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < γ₀ + α + α + 2 →
      ∀ i, ζ ≤ 𝒯.deg i → 𝒯.deg i < γ₀ + α + α → (multiDeg k : ℝ) ≠ 𝒯.deg i + 2) :
    False :=
  Regression.hni_allIndices_false Ppoly (Regression.polyOrder_pos_of_hNγ hγpos hNγ) hζ hγpos hni

/-- On the instance (`ζ = -1/2`, `γ̄ = 5/4`) the unrestricted `hni` is false
(by `Regression.hni_allIndices_false`). -/
theorem Regression.hni_allIndices_false_on_instance :
    ¬ (∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < Phi4Inst.gam₀ + Phi4Inst.alpha + Phi4Inst.alpha + 2 →
      ∀ i, Phi4Inst.zeta ≤ (Phi4Inst.«structure» 4).deg i →
        (Phi4Inst.«structure» 4).deg i < Phi4Inst.gam₀ + Phi4Inst.alpha + Phi4Inst.alpha →
          (multiDeg k : ℝ) ≠ (Phi4Inst.«structure» 4).deg i + 2) :=
  Regression.hni_allIndices_false (Phi4Inst.polySector 4) (by norm_num)
    (by norm_num [Phi4Inst.zeta])
    (by norm_num [Phi4Inst.gam₀, Phi4Inst.alpha])

/-- The restricted `hni` (non-polynomial indices only) holds on the instance with the same
parameters. Hence the restricted `hni` is consistent with `ζ ≤ 0 < γ̄`. -/
theorem Regression.hni_nonPolynomial_on_instance :
    ∀ k : Fin 4 →₀ ℕ, (multiDeg k : ℝ) < Phi4Inst.gam₀ + Phi4Inst.alpha + Phi4Inst.alpha + 2 →
      ∀ i, i ∉ Set.range (Phi4Inst.polySector 4).emb → Phi4Inst.zeta ≤ (Phi4Inst.«structure» 4).deg i →
        (Phi4Inst.«structure» 4).deg i < Phi4Inst.gam₀ + Phi4Inst.alpha + Phi4Inst.alpha →
          (multiDeg k : ℝ) ≠ (Phi4Inst.«structure» 4).deg i + 2 :=
  Phi4Inst.hyp_hni
