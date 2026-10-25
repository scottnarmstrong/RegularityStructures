/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.Combinatorics
public import RegularityStructures.Abstract.Datum.Deriv
public import RegularityStructures.Abstract.Integration.PolyCompat.Compat
public import RegularityStructures.Abstract.Model

/-!
# The Taylor lift of a smooth function into the polynomial sector

For `F` smooth on `{t > 0}` and a polynomial sector `P` of `𝒯`, `liftOf P γ₀ F x` is the Taylor
polynomial `∑_{|k|_𝔰 < γ₀} D^k F(x) / k! · e_{P.emb k}` of `F` at `x`. It is linear in `F`.
For a polynomial-compatible model, `Γ_{xy}` acts on `T̄` through the translation
`polyTranslate (x - y)` (`gammaMap_polyEmbed`).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-- The coefficients `D^k F(x) / k!`, `|k|_𝔰 < γ₀`, of the Taylor polynomial of `F` at `x`. -/
def liftCoeff (N : ℕ) (γ₀ : ℝ) (F : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    PolyIndex N → ℝ :=
  fun k => if polyDeg N k < γ₀ then D ⇑k.1 F x / multiFactorial ⇑k.1 else 0

/-- The Taylor polynomial of `F` at `x`, as an element of `T̄ ⊂ T`. -/
def liftOf (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) (F : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    ι → ℝ :=
  P.polyEmbed (liftCoeff N γ₀ F x)

end RegularityStructures.Datum

end

public section

open scoped ContDiff

namespace RegularityStructures.Datum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

/-! ### Linearity of the derivatives -/

theorem pdIter_add_fun (i : Fin 4) (n : ℕ) {F G : ParabolicSpace → ℝ} (hF : SmoothPos F)
    (hG : SmoothPos G) : pdIter i n (F + G) = pdIter i n F + pdIter i n G := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdIter_succ', pdIter_succ', pdIter_succ', ih]
    exact pdv_add (hF.pdIter i n) (hG.pdIter i n)

theorem pdIter_smul_fun (i : Fin 4) (n : ℕ) {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (c : ℝ) :
    pdIter i n (c • F) = c • pdIter i n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pdIter_succ', pdIter_succ', ih]
    exact pdv_smul (hF.pdIter i n) c

theorem D_add_fun (k : Fin 4 → ℕ) {F G : ParabolicSpace → ℝ} (hF : SmoothPos F)
    (hG : SmoothPos G) : D k (F + G) = D k F + D k G := by
  unfold D
  rw [pdIter_add_fun 3 _ hF hG, pdIter_add_fun 2 _ (hF.pdIter 3 _) (hG.pdIter 3 _),
    pdIter_add_fun 1 _ ((hF.pdIter 3 _).pdIter 2 _) ((hG.pdIter 3 _).pdIter 2 _),
    pdIter_add_fun 0 _ (((hF.pdIter 3 _).pdIter 2 _).pdIter 1 _)
      (((hG.pdIter 3 _).pdIter 2 _).pdIter 1 _)]

theorem D_smul_fun (k : Fin 4 → ℕ) {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (c : ℝ) :
    D k (c • F) = c • D k F := by
  unfold D
  rw [pdIter_smul_fun 3 _ hF, pdIter_smul_fun 2 _ (hF.pdIter 3 _),
    pdIter_smul_fun 1 _ ((hF.pdIter 3 _).pdIter 2 _),
    pdIter_smul_fun 0 _ (((hF.pdIter 3 _).pdIter 2 _).pdIter 1 _)]

theorem liftCoeff_add (γ₀ : ℝ) {F G : ParabolicSpace → ℝ} (hF : SmoothPos F) (hG : SmoothPos G)
    (x : ParabolicSpace) :
    liftCoeff N γ₀ (F + G) x = liftCoeff N γ₀ F x + liftCoeff N γ₀ G x := by
  funext k
  simp only [liftCoeff, Pi.add_apply]
  split_ifs
  · rw [D_add_fun _ hF hG, Pi.add_apply, add_div]
  · simp

theorem liftCoeff_smul (γ₀ : ℝ) {F : ParabolicSpace → ℝ} (hF : SmoothPos F) (c : ℝ)
    (x : ParabolicSpace) :
    liftCoeff N γ₀ (c • F) x = c • liftCoeff N γ₀ F x := by
  funext k
  simp only [liftCoeff, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [D_smul_fun _ hF, Pi.smul_apply, smul_eq_mul, mul_div_assoc]
  · simp

theorem polyEmbed_add (P : PolynomialSector 𝒯 N) (σ τ : PolyIndex N → ℝ) :
    P.polyEmbed (σ + τ) = P.polyEmbed σ + P.polyEmbed τ := by
  simp [PolynomialSector.polyEmbed, add_smul, Finset.sum_add_distrib]

theorem polyEmbed_smul (P : PolynomialSector 𝒯 N) (c : ℝ) (σ : PolyIndex N → ℝ) :
    P.polyEmbed (c • σ) = c • P.polyEmbed σ := by
  simp [PolynomialSector.polyEmbed, Finset.smul_sum, smul_smul]

theorem liftOf_add (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) {F G : ParabolicSpace → ℝ}
    (hF : SmoothPos F) (hG : SmoothPos G) (x : ParabolicSpace) :
    liftOf P γ₀ (F + G) x = liftOf P γ₀ F x + liftOf P γ₀ G x := by
  unfold liftOf
  rw [liftCoeff_add γ₀ hF hG, polyEmbed_add]

theorem liftOf_smul (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) {F : ParabolicSpace → ℝ}
    (hF : SmoothPos F) (c : ℝ) (x : ParabolicSpace) :
    liftOf P γ₀ (c • F) x = c • liftOf P γ₀ F x := by
  unfold liftOf
  rw [liftCoeff_smul γ₀ hF, polyEmbed_smul]

/-! ### Values -/

theorem liftOf_mem_subspace (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) (F : ParabolicSpace → ℝ)
    (x : ParabolicSpace) : liftOf P γ₀ F x ∈ P.subspace := P.polyEmbed_mem _

theorem liftOf_apply_emb (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) (F : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (k : PolyIndex N) :
    liftOf P γ₀ F x (P.emb k) = liftCoeff N γ₀ F x k :=
  P.polyEmbed_apply_emb _ _

theorem liftOf_apply_of_notMem (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) (F : ParabolicSpace → ℝ)
    (x : ParabolicSpace) {i : ι} (hi : i ∉ Set.range P.emb) : liftOf P γ₀ F x i = 0 :=
  P.polyEmbed_apply_of_notMem _ hi

theorem liftOf_mem_lowerSubspace (P : PolynomialSector 𝒯 N) (γ₀ : ℝ) (F : ParabolicSpace → ℝ)
    (x : ParabolicSpace) : liftOf P γ₀ F x ∈ lowerSubspace 𝒯.deg γ₀ := by
  intro i hi
  by_cases hmem : i ∈ Set.range P.emb
  · obtain ⟨k, rfl⟩ := hmem
    rw [liftOf_apply_emb]
    rw [P.deg_emb] at hi
    simp [liftCoeff, not_lt.2 hi]
  · exact liftOf_apply_of_notMem P γ₀ F x hmem

/-! ### The action of `Γ` on the Taylor polynomial -/

theorem gammaMap_polyEmbed {M : Model 𝒯 parabolicSemigroup} {P : PolynomialSector 𝒯 N}
    (hM : M.IsPolyCompatible P) (x y : ParabolicSpace) (σ : PolyIndex N → ℝ) :
    M.gammaMap x y (P.polyEmbed σ) =
      P.polyEmbed (polyTranslate (parabolicCoords (x - y)) σ) := by
  have hσ : σ = ∑ k, σ k • (Pi.single k 1 : PolyIndex N → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hσ]
  simp only [PolynomialSector.polyEmbed, map_sum, map_smul, Model.gammaMap_single_emb hM,
    Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]
  rw [Finset.sum_comm]

end RegularityStructures.Datum

end
