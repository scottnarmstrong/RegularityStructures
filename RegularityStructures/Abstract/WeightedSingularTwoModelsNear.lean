/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularTwoModels
public import RegularityStructures.Abstract.ProductTwoModelsBoundsNear
public import RegularityStructures.Abstract.WeightedSingularProductNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.WeightedSingularTwoModels`

The statements of `RegularityStructures.Abstract.WeightedSingularTwoModels` that involve `Γ`-bounds,
for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

variable (M₁ M₂ : Model 𝒯 K) (P : 𝒯.GradedProduct)

/-- The weighted version of `abs_mul_gammaMap_sub_mul_gammaMap_apply_le_near`: the difference of the
terms `Γ Q_m f₁ ⋆ Γ Q_n f₂` and `Γ̄ Q_m g₁ ⋆ Γ̄ Q_n g₂` with `m + n ≥ γ`, for coordinates bounded
by powers `w^{(ηᵢ − deg) ∧ 0}` of the weight. -/
theorem abs_mul_gammaMap_sub_mul_gammaMap_apply_le_weighted_near
    {γ₁ γ₂ α₁ α₂ η₁ η₂ γ η δΓ CΓ C₁ C₂ δ₁ δ₂ w : ℝ} {S : Set E}
    (hΓd₁ : M₁.GammaDiffNearOn M₂ γ₁ δΓ S) (hΓd₂ : M₁.GammaDiffNearOn M₂ γ₂ δΓ S)
    (hΓ₁ : M₁.GammaNearOn γ₂ CΓ S) (hΓ₂ : M₂.GammaNearOn γ₁ CΓ S)
    (hΓ₂' : M₂.GammaNearOn γ₂ CΓ S) (hδΓ : 0 ≤ δΓ) (hCΓ : 0 ≤ CΓ) {x y : E} (hx : x ∈ S)
    (hy : y ∈ S) (hdw : K.scaleDist y x ≤ w) (hw0 : 0 < w) (hw1 : w ≤ 1)
    {a₁ a₂ b₁ b₂ : ι → ℝ} (ha₁T : a₁ ∈ lowerSubspace 𝒯.deg γ₁)
    (hb₁T : b₁ ∈ lowerSubspace 𝒯.deg γ₁) (ha₂T : a₂ ∈ lowerSubspace 𝒯.deg γ₂)
    (hb₂T : b₂ ∈ lowerSubspace 𝒯.deg γ₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hδ₁ : 0 ≤ δ₁)
    (hδ₂ : 0 ≤ δ₂) (ha₁ : ∀ i, |a₁ i| ≤ C₁ * w ^ min (η₁ - 𝒯.deg i) 0)
    (hb₁ : ∀ i, |b₁ i| ≤ C₁ * w ^ min (η₁ - 𝒯.deg i) 0)
    (ha₂ : ∀ j, |a₂ j| ≤ C₂ * w ^ min (η₂ - 𝒯.deg j) 0)
    (hab₁ : ∀ i, |a₁ i - b₁ i| ≤ δ₁ * w ^ min (η₁ - 𝒯.deg i) 0)
    (hab₂ : ∀ j, |a₂ j - b₂ j| ≤ δ₂ * w ^ min (η₂ - 𝒯.deg j) 0)
    (ha₁α : ∀ i, 𝒯.deg i < α₁ → a₁ i = 0) (hb₁α : ∀ i, 𝒯.deg i < α₁ → b₁ i = 0)
    (ha₂α : ∀ j, 𝒯.deg j < α₂ → a₂ j = 0) (hb₂α : ∀ j, 𝒯.deg j < α₂ → b₂ j = 0)
    (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁) (hη₁₂ : η ≤ η₁ + η₂) (hηγ : η ≤ γ) {m n : ℝ}
    (hmn : γ ≤ m + n) {k : ι} (hk : 𝒯.deg k < γ) :
    |P.mul (M₁.gammaMap y x (homogeneousProj 𝒯.deg m a₁))
          (M₁.gammaMap y x (homogeneousProj 𝒯.deg n a₂)) k -
        P.mul (M₂.gammaMap y x (homogeneousProj 𝒯.deg m b₁))
          (M₂.gammaMap y x (homogeneousProj 𝒯.deg n b₂)) k| ≤
      P.const * ((Fintype.card ι : ℝ) ^ 2 *
        ((C₁ * δΓ + δ₁ * (1 + CΓ)) * (C₂ * (1 + CΓ)) +
          C₁ * (1 + CΓ) * (C₂ * δΓ + δ₂ * (1 + CΓ))) *
        (K.scaleDist y x ^ (γ - 𝒯.deg k) * w ^ (η - γ))) := by
  have hd0 := K.scaleDist_nonneg y x
  set B : ℝ := (C₁ * δΓ + δ₁ * (1 + CΓ)) * (C₂ * (1 + CΓ)) +
    C₁ * (1 + CΓ) * (C₂ * δΓ + δ₂ * (1 + CΓ)) with hB_def
  have hB : 0 ≤ B := by positivity
  have hX : 0 ≤ P.const * ((Fintype.card ι : ℝ) ^ 2 * B *
      (K.scaleDist y x ^ (γ - 𝒯.deg k) * w ^ (η - γ))) :=
    mul_nonneg P.const_nonneg (mul_nonneg (mul_nonneg (by positivity) hB)
      (mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hw0.le _)))
  have hzero : ∀ {c : ℝ} {v : ι → ℝ} {α : ℝ}, c < α → (∀ i, 𝒯.deg i < α → v i = 0) →
      homogeneousProj 𝒯.deg c v = 0 := by
    intro c v α hc hv
    funext i
    rw [homogeneousProj_apply, Pi.zero_apply]
    split_ifs with h
    · exact hv i (h ▸ hc)
    · rfl
  by_cases hm : m < α₁
  · simp only [hzero hm ha₁α, hzero hm hb₁α, map_zero, LinearMap.zero_apply, Pi.zero_apply,
      sub_self, abs_zero]
    exact hX
  by_cases hn : n < α₂
  · simp only [hzero hn ha₂α, hzero hn hb₂α, map_zero, Pi.zero_apply, sub_self, abs_zero]
    exact hX
  set p₁ : ℝ := min (η₁ - m) 0 with hp₁
  set p₂ : ℝ := min (η₂ - n) 0 with hp₂
  have hw₁ : 0 ≤ w ^ p₁ := Real.rpow_nonneg hw0.le _
  have hw₂ : 0 ≤ w ^ p₂ := Real.rpow_nonneg hw0.le _
  -- bounds on the homogeneous parts
  have hQ : ∀ {c : ℝ} {v : ι → ℝ} {C ηv : ℝ}, 0 ≤ C →
      (∀ i, |v i| ≤ C * w ^ min (ηv - 𝒯.deg i) 0) →
      ∀ i, |homogeneousProj 𝒯.deg c v i| ≤ C * w ^ min (ηv - c) 0 := by
    intro c v C ηv hC hv i
    rw [homogeneousProj_apply]
    split_ifs with h
    · rw [← h]
      exact hv i
    · rw [abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg hw0.le _)
  have hQd : ∀ {c : ℝ} {u v : ι → ℝ} {C ηv : ℝ}, 0 ≤ C →
      (∀ i, |u i - v i| ≤ C * w ^ min (ηv - 𝒯.deg i) 0) →
      ∀ i, |homogeneousProj 𝒯.deg c u i - homogeneousProj 𝒯.deg c v i| ≤
        C * w ^ min (ηv - c) 0 := by
    intro c u v C ηv hC huv i
    rw [homogeneousProj_apply, homogeneousProj_apply]
    split_ifs with h
    · rw [← h]
      exact huv i
    · rw [sub_self, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg hw0.le _)
  have hQT : ∀ {c γ' : ℝ} {v : ι → ℝ}, v ∈ lowerSubspace 𝒯.deg γ' →
      homogeneousProj 𝒯.deg c v ∈ lowerSubspace 𝒯.deg γ' := fun hv i hi => by
    rw [homogeneousProj_apply, hv i hi, ite_self]
  have h := abs_mul_gammaMap_sub_mul_gammaMap_apply_le_near M₁ M₂ P hΓd₁ hΓd₂ hΓ₁ hΓ₂ hΓ₂' hδΓ hCΓ
    hx hy (le_gammaNearRadius_of_le_one (hdw.trans hw1)) (hQT (c := m) ha₁T) (hQT (c := m) hb₁T) (hQT (c := n) ha₂T) (hQT (c := n) hb₂T)
    (hQ (c := m) hC₁ ha₁) (hQ (c := m) hC₁ hb₁) (hQ (c := n) hC₂ ha₂) (hQd (c := m) hδ₁ hab₁)
    (hQd (c := n) hδ₂ hab₂) m n k
  rw [homogeneousProj_eq_self (homogeneousProj_mem _ _ _),
    homogeneousProj_eq_self (homogeneousProj_mem _ _ _),
    homogeneousProj_eq_self (homogeneousProj_mem _ _ _),
    homogeneousProj_eq_self (homogeneousProj_mem _ _ _)] at h
  refine h.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (rpow_mul_rpow_le_rpow_mul_rpow (a := m + n - 𝒯.deg k) (b := p₁ + p₂) hd0 hdw hw0 hw1
      (by linarith) (by linarith) ?_) (mul_nonneg (by positivity) hB)) P.const_nonneg))
  · rw [Real.rpow_add hw0, hB_def]
    ring
  · have hm' := not_lt.1 hm
    have hn' := not_lt.1 hn
    rw [hp₁, hp₂]
    rcases min_cases (η₁ - m) 0 with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases min_cases (η₂ - n) 0 with ⟨e2, _⟩ | ⟨e2, _⟩ <;> rw [e1, e2] <;> linarith

/-- The increment comparison for an admissible pair of points [Hai14, proof of
Proposition 6.12, second part]. -/
theorem abs_truncMul_diffIncrement_le_singular_near {V W : Submodule ℝ (ι → ℝ)}
    (hV : 𝒯.IsSector V) (hW : 𝒯.IsSector W) {α₁ α₂ γ₁ γ₂ γ η₁ η₂ η : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α₁)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W α₂) (hγ₁ : γ ≤ γ₁ + α₂)
    (hγ₂ : γ ≤ γ₂ + α₁) (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁) (hη₁₂ : η ≤ η₁ + η₂)
    (hηγ : η ≤ γ) (hreg : P.IsRegularPair V W γ) {ρ : E → ℝ} {S : Set E}
    {f₁ f₂ g₁ g₂ : E → ι → ℝ} {C₁ C₂ δ₁ δ₂ CΓ δΓ : ℝ}
    (hf₁V : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ V) (hg₁V : ∀ x ∈ S, 0 < ρ x → g₁ x ∈ V)
    (hf₂W : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ W) (hg₂W : ∀ x ∈ S, 0 < ρ x → g₂ x ∈ W)
    (hf₁T : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ lowerSubspace 𝒯.deg γ₁)
    (hg₁T : ∀ x ∈ S, 0 < ρ x → g₁ x ∈ lowerSubspace 𝒯.deg γ₁)
    (hf₂T : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ lowerSubspace 𝒯.deg γ₂)
    (hg₂T : ∀ x ∈ S, 0 < ρ x → g₂ x ∈ lowerSubspace 𝒯.deg γ₂)
    (hf₁ : M₁.SingularBoundOn ρ γ₁ η₁ C₁ S f₁) (hg₁ : M₂.SingularBoundOn ρ γ₁ η₁ C₁ S g₁)
    (hf₂ : M₁.SingularBoundOn ρ γ₂ η₂ C₂ S f₂)
    (hδ₁ : M₁.SingularDiffBoundOn M₂ ρ γ₁ η₁ δ₁ S f₁ g₁)
    (hδ₂ : M₁.SingularDiffBoundOn M₂ ρ γ₂ η₂ δ₂ S f₂ g₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂) (hΓ₁₂ : M₁.GammaNearOn γ₂ CΓ S)
    (hΓ₂₁ : M₂.GammaNearOn γ₁ CΓ S) (hΓ₂₂ : M₂.GammaNearOn γ₂ CΓ S)
    (hΓd₁ : M₁.GammaDiffNearOn M₂ γ₁ δΓ S) (hΓd₂ : M₁.GammaDiffNearOn M₂ γ₂ δΓ S)
    (hCΓ : 0 ≤ CΓ) (hδΓ : 0 ≤ δΓ) {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hρx : 0 < ρ x)
    (hρy : 0 < ρ y) (hd : K.scaleDist y x ≤ min (singularWeight ρ x) (singularWeight ρ y))
    {k : ι} (hk : 𝒯.deg k < γ) :
    |(P.truncMul γ f₁ f₂ y - M₁.gammaMap y x (P.truncMul γ f₁ f₂ x)) k -
        (P.truncMul γ g₁ g₂ y - M₂.gammaMap y x (P.truncMul γ g₁ g₂ x)) k| ≤
      P.truncMulConst * (δ₁ * C₂ + C₁ * δ₂ + 2 * C₁ * C₂ * δΓ) * (1 + CΓ) ^ 2 *
        K.scaleDist y x ^ (γ - 𝒯.deg k) *
          min (singularWeight ρ x) (singularWeight ρ y) ^ (η - γ) := by
  set w := min (singularWeight ρ x) (singularWeight ρ y) with hw_def
  have hw0 : 0 < w := lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
  have hw1 : w ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one ρ x)
  have hd0 := K.scaleDist_nonneg y x
  have hF : (P.truncMul γ f₁ f₂ y - M₁.gammaMap y x (P.truncMul γ f₁ f₂ x)) k =
      P.mul (f₁ y) (f₂ y - M₁.gammaMap y x (f₂ x)) k +
        P.mul (f₁ y - M₁.gammaMap y x (f₁ x)) (f₂ y) k -
        P.mul (f₁ y - M₁.gammaMap y x (f₁ x)) (f₂ y - M₁.gammaMap y x (f₂ x)) k +
        (P.mul (M₁.gammaMap y x (f₁ x)) (M₁.gammaMap y x (f₂ x)) -
          M₁.gammaMap y x (P.truncMul γ f₁ f₂ x)) k :=
    P.lowerProj_mul_sub_map_apply_eq (M₁.gammaMap y x) (f₁ x) (f₂ x) (f₁ y) (f₂ y) hk
  have hG : (P.truncMul γ g₁ g₂ y - M₂.gammaMap y x (P.truncMul γ g₁ g₂ x)) k =
      P.mul (g₁ y) (g₂ y - M₂.gammaMap y x (g₂ x)) k +
        P.mul (g₁ y - M₂.gammaMap y x (g₁ x)) (g₂ y) k -
        P.mul (g₁ y - M₂.gammaMap y x (g₁ x)) (g₂ y - M₂.gammaMap y x (g₂ x)) k +
        (P.mul (M₂.gammaMap y x (g₁ x)) (M₂.gammaMap y x (g₂ x)) -
          M₂.gammaMap y x (P.truncMul γ g₁ g₂ x)) k :=
    P.lowerProj_mul_sub_map_apply_eq (M₂.gammaMap y x) (g₁ x) (g₂ x) (g₁ y) (g₂ y) hk
  have hdec : (P.truncMul γ f₁ f₂ y - M₁.gammaMap y x (P.truncMul γ f₁ f₂ x)) k -
      (P.truncMul γ g₁ g₂ y - M₂.gammaMap y x (P.truncMul γ g₁ g₂ x)) k =
      P.mul (f₁ y - g₁ y) (f₂ y - M₁.gammaMap y x (f₂ x)) k +
        P.mul (g₁ y) ((f₂ y - M₁.gammaMap y x (f₂ x)) - (g₂ y - M₂.gammaMap y x (g₂ x))) k +
        P.mul ((f₁ y - M₁.gammaMap y x (f₁ x)) - (g₁ y - M₂.gammaMap y x (g₁ x))) (f₂ y) k +
        P.mul (g₁ y - M₂.gammaMap y x (g₁ x)) (f₂ y - g₂ y) k -
        P.mul ((f₁ y - M₁.gammaMap y x (f₁ x)) - (g₁ y - M₂.gammaMap y x (g₁ x)))
          (f₂ y - M₁.gammaMap y x (f₂ x)) k -
        P.mul (g₁ y - M₂.gammaMap y x (g₁ x))
          ((f₂ y - M₁.gammaMap y x (f₂ x)) - (g₂ y - M₂.gammaMap y x (g₂ x))) k +
        ((P.mul (M₁.gammaMap y x (f₁ x)) (M₁.gammaMap y x (f₂ x)) -
          M₁.gammaMap y x (P.truncMul γ f₁ f₂ x)) k -
        (P.mul (M₂.gammaMap y x (g₁ x)) (M₂.gammaMap y x (g₂ x)) -
          M₂.gammaMap y x (P.truncMul γ g₁ g₂ x)) k) := by
    rw [hF, hG]
    simp only [map_sub, LinearMap.sub_apply, Pi.sub_apply]
    ring
  -- coordinate facts at `y`
  have hfg₁y : ∀ i, |(f₁ y - g₁ y) i| ≤ δ₁ * w ^ min (η₁ - 𝒯.deg i) 0 :=
    hδ₁.abs_sub_apply_le_weight hδ₁0 (hf₁T y hy hρy) (hg₁T y hy hρy) hy hρy hw0
      (min_le_right _ _)
  have hfg₂y : ∀ j, |(f₂ y - g₂ y) j| ≤ δ₂ * w ^ min (η₂ - 𝒯.deg j) 0 :=
    hδ₂.abs_sub_apply_le_weight hδ₂0 (hf₂T y hy hρy) (hg₂T y hy hρy) hy hρy hw0
      (min_le_right _ _)
  have hg₁y : ∀ i, |g₁ y i| ≤ C₁ * w ^ min (η₁ - 𝒯.deg i) 0 :=
    hg₁.abs_apply_le_weight M₂ hC₁ (hg₁T y hy hρy) hy hρy hw0 (min_le_right _ _)
  have hf₂y : ∀ j, |f₂ y j| ≤ C₂ * w ^ min (η₂ - 𝒯.deg j) 0 :=
    hf₂.abs_apply_le_weight M₁ hC₂ (hf₂T y hy hρy) hy hρy hw0 (min_le_right _ _)
  have hVy : ∀ i, 𝒯.deg i < α₁ → (f₁ y - g₁ y) i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
      (V.sub_mem (hf₁V y hy hρy) (hg₁V y hy hρy)) hi
  have hWy : ∀ j, 𝒯.deg j < α₂ → (f₂ y - g₂ y) j = 0 := fun j hj =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα
      (W.sub_mem (hf₂W y hy hρy) (hg₂W y hy hρy)) hj
  have hg₁α : ∀ i, 𝒯.deg i < α₁ → g₁ y i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα (hg₁V y hy hρy) hi
  have hf₂α : ∀ j, 𝒯.deg j < α₂ → f₂ y j = 0 := fun j hj =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα (hf₂W y hy hρy) hj
  -- the increments
  have hDE₁ : ∀ i, 𝒯.deg i < γ₁ → |((f₁ y - M₁.gammaMap y x (f₁ x)) -
      (g₁ y - M₂.gammaMap y x (g₁ x))) i| ≤
        δ₁ * K.scaleDist y x ^ (γ₁ - 𝒯.deg i) * w ^ (η₁ - γ₁) :=
    fun i hi => by rw [Pi.sub_apply]; exact hδ₁.2 x hx y hy hρx hρy hd i hi
  have hDE₂ : ∀ j, 𝒯.deg j < γ₂ → |((f₂ y - M₁.gammaMap y x (f₂ x)) -
      (g₂ y - M₂.gammaMap y x (g₂ x))) j| ≤
        δ₂ * K.scaleDist y x ^ (γ₂ - 𝒯.deg j) * w ^ (η₂ - γ₂) :=
    fun j hj => by rw [Pi.sub_apply]; exact hδ₂.2 x hx y hy hρx hρy hd j hj
  have hDE₁T : ∀ i, γ₁ ≤ 𝒯.deg i → ((f₁ y - M₁.gammaMap y x (f₁ x)) -
      (g₁ y - M₂.gammaMap y x (g₁ x))) i = 0 := fun i hi => by
    rw [Pi.sub_apply, M₁.increment_apply_eq_zero_of_mem (hf₁T x hx hρx) (hf₁T y hy hρy) hi,
      M₂.increment_apply_eq_zero_of_mem (hg₁T x hx hρx) (hg₁T y hy hρy) hi, sub_zero]
  have hDE₂T : ∀ j, γ₂ ≤ 𝒯.deg j → ((f₂ y - M₁.gammaMap y x (f₂ x)) -
      (g₂ y - M₂.gammaMap y x (g₂ x))) j = 0 := fun j hj => by
    rw [Pi.sub_apply, M₁.increment_apply_eq_zero_of_mem (hf₂T x hx hρx) (hf₂T y hy hρy) hj,
      M₂.increment_apply_eq_zero_of_mem (hg₂T x hx hρx) (hg₂T y hy hρy) hj, sub_zero]
  have hDE₁α : ∀ i, 𝒯.deg i < α₁ → ((f₁ y - M₁.gammaMap y x (f₁ x)) -
      (g₁ y - M₂.gammaMap y x (g₁ x))) i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
      (V.sub_mem (M₁.increment_mem_of_mem hV (hf₁V x hx hρx) (hf₁V y hy hρy))
        (M₂.increment_mem_of_mem hV (hg₁V x hx hρx) (hg₁V y hy hρy))) hi
  have hE₁α : ∀ i, 𝒯.deg i < α₁ → (g₁ y - M₂.gammaMap y x (g₁ x)) i = 0 := fun i hi =>
    RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
      (M₂.increment_mem_of_mem hV (hg₁V x hx hρx) (hg₁V y hy hρy)) hi
  have hE₁ : ∀ i, 𝒯.deg i < γ₁ → |(g₁ y - M₂.gammaMap y x (g₁ x)) i| ≤
      C₁ * K.scaleDist y x ^ (γ₁ - 𝒯.deg i) * w ^ (η₁ - γ₁) := fun i hi =>
    hg₁.2 x hx y hy hρx hρy hd i hi
  have hD₂ : ∀ j, 𝒯.deg j < γ₂ → |(f₂ y - M₁.gammaMap y x (f₂ x)) j| ≤
      C₂ * K.scaleDist y x ^ (γ₂ - 𝒯.deg j) * w ^ (η₂ - γ₂) := fun j hj =>
    hf₂.2 x hx y hy hρx hρy hd j hj
  have hE₁T : ∀ i, γ₁ ≤ 𝒯.deg i → (g₁ y - M₂.gammaMap y x (g₁ x)) i = 0 := fun i hi =>
    M₂.increment_apply_eq_zero_of_mem (hg₁T x hx hρx) (hg₁T y hy hρy) hi
  have hD₂T : ∀ j, γ₂ ≤ 𝒯.deg j → (f₂ y - M₁.gammaMap y x (f₂ x)) j = 0 := fun j hj =>
    M₁.increment_apply_eq_zero_of_mem (hf₂T x hx hρx) (hf₂T y hy hρy) hj
  -- the six terms
  have hT1 := P.abs_mul_apply_le_of_right_increment_weighted (a := f₁ y - g₁ y) hd0 hd hw0 hw1
    hk hγ₂ hη₁₂ (by linarith) hδ₁0 hC₂ hfg₁y hVy hD₂ hD₂T
  have hT2 := P.abs_mul_apply_le_of_right_increment_weighted hd0 hd hw0 hw1 hk hγ₂ hη₁₂
    (by linarith) hC₁ hδ₂0 hg₁y hg₁α hDE₂ hDE₂T
  have hT3 := P.abs_mul_apply_le_of_left_increment_weighted hd0 hd hw0 hw1 hk hγ₁ hη₁₂ hη₁
    hδ₁0 hC₂ hDE₁ hDE₁T hf₂y hf₂α
  have hT4 := P.abs_mul_apply_le_of_left_increment_weighted (b := f₂ y - g₂ y) hd0 hd hw0 hw1
    hk hγ₁ hη₁₂ hη₁ hC₁ hδ₂0 hE₁ hE₁T hfg₂y hWy
  have hT5 := P.abs_mul_apply_le_of_increments_weighted hd0 hd hw0 hw1 hk hγ₂ hη₁₂ hδ₁0 hC₂
    hDE₁ hDE₁T hDE₁α hD₂ hD₂T
  have hT6 := P.abs_mul_apply_le_of_increments_weighted hd0 hd hw0 hw1 hk hγ₂ hη₁₂ hC₁ hδ₂0
    hE₁ hE₁T hE₁α hDE₂ hDE₂T
  -- the remainder terms
  set N : ℝ := (Fintype.card ι : ℝ) with hN_def
  set V₀ : ℝ := K.scaleDist y x ^ (γ - 𝒯.deg k) * w ^ (η - γ) with hV₀_def
  have hV₀ : 0 ≤ V₀ := mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hw0.le _)
  set B : ℝ := (C₁ * δΓ + δ₁ * (1 + CΓ)) * (C₂ * (1 + CΓ)) +
    C₁ * (1 + CΓ) * (C₂ * δΓ + δ₂ * (1 + CΓ)) with hB_def
  have hB : 0 ≤ B := by positivity
  set X : ℝ := P.const * (N ^ 2 * B * V₀) with hX_def
  have hX : 0 ≤ X := mul_nonneg P.const_nonneg (mul_nonneg (mul_nonneg (by positivity) hB) hV₀)
  have hR : |(P.mul (M₁.gammaMap y x (f₁ x)) (M₁.gammaMap y x (f₂ x)) -
        M₁.gammaMap y x (P.truncMul γ f₁ f₂ x)) k -
      (P.mul (M₂.gammaMap y x (g₁ x)) (M₂.gammaMap y x (g₂ x)) -
        M₂.gammaMap y x (P.truncMul γ g₁ g₂ x)) k| ≤ N * (N * X) := by
    rw [M₁.mul_gammaMap_sub_gammaMap_truncMul_eq P hV hW hreg (hf₁V x hx hρx) (hf₂W x hx hρx) y,
      M₂.mul_gammaMap_sub_gammaMap_truncMul_eq P hV hW hreg (hg₁V x hx hρx) (hg₂W x hx hρx) y,
      ← Pi.sub_apply, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    refine abs_sum_sum_image_apply_le 𝒯.deg _ k hX fun m _ n _ => ?_
    split_ifs with hmn
    · rw [sub_self, Pi.zero_apply, abs_zero]
      exact hX
    · rw [Pi.sub_apply]
      exact abs_mul_gammaMap_sub_mul_gammaMap_apply_le_weighted_near M₁ M₂ P hΓd₁ hΓd₂ hΓ₁₂ hΓ₂₁
        hΓ₂₂ hδΓ hCΓ hx hy hd hw0 hw1 (hf₁T x hx hρx) (hg₁T x hx hρx) (hf₂T x hx hρx)
        (hg₂T x hx hρx) hC₁ hC₂ hδ₁0 hδ₂0
        (hf₁.abs_apply_le_weight M₁ hC₁ (hf₁T x hx hρx) hx hρx hw0 (min_le_left _ _))
        (hg₁.abs_apply_le_weight M₂ hC₁ (hg₁T x hx hρx) hx hρx hw0 (min_le_left _ _))
        (hf₂.abs_apply_le_weight M₁ hC₂ (hf₂T x hx hρx) hx hρx hw0 (min_le_left _ _))
        (hδ₁.abs_sub_apply_le_weight hδ₁0 (hf₁T x hx hρx) (hg₁T x hx hρx) hx hρx hw0
          (min_le_left _ _))
        (hδ₂.abs_sub_apply_le_weight hδ₂0 (hf₂T x hx hρx) (hg₂T x hx hρx) hx hρx hw0
          (min_le_left _ _))
        (fun i hi => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
          (hf₁V x hx hρx) hi)
        (fun i hi => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
          (hg₁V x hx hρx) hi)
        (fun j hj => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα
          (hf₂W x hx hρx) hj)
        (fun j hj => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα
          (hg₂W x hx hρx) hj) hη₁ hη₂ hη₁₂ hηγ (not_lt.1 hmn) hk
  -- assembly
  set Y : ℝ := δ₁ * C₂ + C₁ * δ₂ + 2 * C₁ * C₂ * δΓ with hY_def
  have hGG : 1 ≤ (1 + CΓ) ^ 2 := one_le_pow₀ (by linarith)
  have hcd : 0 ≤ P.const * V₀ := mul_nonneg P.const_nonneg hV₀
  have hZT : P.const * ((δ₁ * C₂ + C₁ * δ₂) * V₀) ≤ P.const * (Y * (1 + CΓ) ^ 2) * V₀ := by
    have h1 : δ₁ * C₂ + C₁ * δ₂ ≤ Y := by
      rw [hY_def]
      have : 0 ≤ 2 * C₁ * C₂ * δΓ := by positivity
      linarith
    have h2 : Y ≤ Y * (1 + CΓ) ^ 2 := le_mul_of_one_le_right (by positivity) hGG
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hcd
    calc _ = (P.const * V₀) * (δ₁ * C₂ + C₁ * δ₂) := by ring
      _ ≤ (P.const * V₀) * (Y * (1 + CΓ) ^ 2) := h3
      _ = _ := by ring
  have hWT : P.const * B * V₀ ≤ P.const * (Y * (1 + CΓ) ^ 2) * V₀ := by
    have h3 := mul_le_mul_of_nonneg_left
      (twoModels_const_le (δ₁ := δ₁) (δ₂ := δ₂) hC₁ hC₂ hCΓ hδΓ) hcd
    calc _ = (P.const * V₀) * B := by ring
      _ ≤ _ := h3
      _ = _ := by ring
  have hNX : N * (N * X) = N ^ 4 * (P.const * B * V₀) := by
    rw [hX_def]
    ring
  rw [hdec]
  refine (abs_add_add_add_sub_sub_add_le _ _ _ _ _ _ _).trans ?_
  calc _ ≤ P.const * ((δ₁ * C₂ + C₁ * δ₂) * V₀) + P.const * ((δ₁ * C₂ + C₁ * δ₂) * V₀) +
        P.const * ((δ₁ * C₂ + C₁ * δ₂) * V₀) + N ^ 4 * (P.const * B * V₀) := by
        rw [← hNX]
        have e1 : P.const * ((δ₁ * C₂ + C₁ * δ₂) * V₀) =
            P.const * (δ₁ * C₂ * V₀) + P.const * (C₁ * δ₂ * V₀) := by ring
        rw [e1]
        linarith
    _ ≤ (3 + N ^ 4) * (P.const * (Y * (1 + CΓ) ^ 2) * V₀) :=
        three_add_card_pow_le_of_le hZT hWT
    _ = _ := by
        rw [hV₀_def, RegularityStructure.GradedProduct.truncMulConst]
        ring

/-- **Products of singular modelled distributions for two models** [Hai14, Proposition 6.12,
second part], explicit form on a set `S`, under the (necessary) hypothesis `η ≤ γ`:
`|||f₁ ⋆_γ f₂; g₁ ⋆_γ g₂|||_{γ,η;S} ≤ c (δ₁ C₂ + C₁ δ₂ + 2 C₁ C₂ δ_Γ) (1 + C_Γ)²`, where `C₁` bounds
`|||f₁|||_{γ₁,η₁}` and `|||g₁|||_{γ₁,η₁}`, `C₂` bounds `|||f₂|||_{γ₂,η₂}`, `C_Γ` bounds `‖Γ‖` and
`‖Γ̄‖`, `δ₁ = |||f₁; g₁|||_{γ₁,η₁}`, `δ₂ = |||f₂; g₂|||_{γ₂,η₂}` and `δ_Γ = ‖Γ − Γ̄‖`. -/
theorem singularDiffBoundOn_truncMul_near {V W : Submodule ℝ (ι → ℝ)} (hV : 𝒯.IsSector V)
    (hW : 𝒯.IsSector W) {α₁ α₂ γ₁ γ₂ γ η₁ η₂ η : ℝ}
    (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α₁)
    (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W α₂) (hγ₁ : γ ≤ γ₁ + α₂)
    (hγ₂ : γ ≤ γ₂ + α₁) (hη₁ : η ≤ η₁ + α₂) (hη₂ : η ≤ η₂ + α₁) (hη₁₂ : η ≤ η₁ + η₂)
    (hηγ : η ≤ γ) (hreg : P.IsRegularPair V W γ) {ρ : E → ℝ} {S : Set E}
    {f₁ f₂ g₁ g₂ : E → ι → ℝ} {C₁ C₂ δ₁ δ₂ CΓ δΓ : ℝ}
    (hf₁V : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ V) (hg₁V : ∀ x ∈ S, 0 < ρ x → g₁ x ∈ V)
    (hf₂W : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ W) (hg₂W : ∀ x ∈ S, 0 < ρ x → g₂ x ∈ W)
    (hf₁T : ∀ x ∈ S, 0 < ρ x → f₁ x ∈ lowerSubspace 𝒯.deg γ₁)
    (hg₁T : ∀ x ∈ S, 0 < ρ x → g₁ x ∈ lowerSubspace 𝒯.deg γ₁)
    (hf₂T : ∀ x ∈ S, 0 < ρ x → f₂ x ∈ lowerSubspace 𝒯.deg γ₂)
    (hg₂T : ∀ x ∈ S, 0 < ρ x → g₂ x ∈ lowerSubspace 𝒯.deg γ₂)
    (hf₁ : M₁.SingularBoundOn ρ γ₁ η₁ C₁ S f₁) (hg₁ : M₂.SingularBoundOn ρ γ₁ η₁ C₁ S g₁)
    (hf₂ : M₁.SingularBoundOn ρ γ₂ η₂ C₂ S f₂)
    (hδ₁ : M₁.SingularDiffBoundOn M₂ ρ γ₁ η₁ δ₁ S f₁ g₁)
    (hδ₂ : M₁.SingularDiffBoundOn M₂ ρ γ₂ η₂ δ₂ S f₂ g₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hδ₁0 : 0 ≤ δ₁) (hδ₂0 : 0 ≤ δ₂) (hΓ₁₂ : M₁.GammaNearOn γ₂ CΓ S)
    (hΓ₂₁ : M₂.GammaNearOn γ₁ CΓ S) (hΓ₂₂ : M₂.GammaNearOn γ₂ CΓ S)
    (hΓd₁ : M₁.GammaDiffNearOn M₂ γ₁ δΓ S) (hΓd₂ : M₁.GammaDiffNearOn M₂ γ₂ δΓ S)
    (hCΓ : 0 ≤ CΓ) (hδΓ : 0 ≤ δΓ) :
    M₁.SingularDiffBoundOn M₂ ρ γ η
      (P.truncMulConst * (δ₁ * C₂ + C₁ * δ₂ + 2 * C₁ * C₂ * δΓ) * (1 + CΓ) ^ 2) S
      (P.truncMul γ f₁ f₂) (P.truncMul γ g₁ g₂) := by
  refine ⟨fun x hx hρ k _ => ?_, fun x hx y hy hρx hρy hd k hk => ?_⟩
  · have hw0 := singularWeight_pos hρ
    have hw1 := singularWeight_le_one ρ x
    have hsplit : P.truncMul γ f₁ f₂ x k - P.truncMul γ g₁ g₂ x k =
        lowerProj 𝒯.deg γ (P.mul (f₁ x - g₁ x) (f₂ x)) k +
          lowerProj 𝒯.deg γ (P.mul (g₁ x) (f₂ x - g₂ x)) k := by
      simp only [RegularityStructure.GradedProduct.truncMul, map_sub, LinearMap.sub_apply,
        Pi.sub_apply]
      ring
    have h1 := P.abs_mul_apply_le_weighted_sup (a := f₁ x - g₁ x) (k := k) hw0 hw1 hδ₁0 hC₂
      (hδ₁.abs_sub_apply_le_weight hδ₁0 (hf₁T x hx hρ) (hg₁T x hx hρ) hx hρ hw0 le_rfl)
      (fun i hi => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
        (V.sub_mem (hf₁V x hx hρ) (hg₁V x hx hρ)) hi)
      (hf₂.abs_apply_le_weight M₁ hC₂ (hf₂T x hx hρ) hx hρ hw0 le_rfl)
      (fun j hj => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα
        (hf₂W x hx hρ) hj) hη₁ hη₂ hη₁₂
    have h2 := P.abs_mul_apply_le_weighted_sup (b := f₂ x - g₂ x) (k := k) hw0 hw1 hC₁ hδ₂0
      (hg₁.abs_apply_le_weight M₂ hC₁ (hg₁T x hx hρ) hx hρ hw0 le_rfl)
      (fun i hi => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hVα
        (hg₁V x hx hρ) hi)
      (hδ₂.abs_sub_apply_le_weight hδ₂0 (hf₂T x hx hρ) (hg₂T x hx hρ) hx hρ hw0 le_rfl)
      (fun j hj => RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity hWα
        (W.sub_mem (hf₂W x hx hρ) (hg₂W x hx hρ)) hj) hη₁ hη₂ hη₁₂
    rw [hsplit]
    refine (abs_add_le _ _).trans ((add_le_add ((abs_lowerProj_apply_le _ _).trans h1)
      ((abs_lowerProj_apply_le _ _).trans h2)).trans ?_)
    have hG : 1 ≤ (1 + CΓ) ^ 2 := one_le_pow₀ (by linarith)
    have hp : 0 ≤ singularWeight ρ x ^ min (η - 𝒯.deg k) 0 := Real.rpow_nonneg hw0.le _
    have hY : δ₁ * C₂ + C₁ * δ₂ ≤ (δ₁ * C₂ + C₁ * δ₂ + 2 * C₁ * C₂ * δΓ) * (1 + CΓ) ^ 2 := by
      have : 0 ≤ 2 * C₁ * C₂ * δΓ := by positivity
      exact (le_add_of_nonneg_right this).trans (le_mul_of_one_le_right (by positivity) hG)
    calc P.const * (δ₁ * C₂ * singularWeight ρ x ^ min (η - 𝒯.deg k) 0) +
          P.const * (C₁ * δ₂ * singularWeight ρ x ^ min (η - 𝒯.deg k) 0)
        = P.const * (δ₁ * C₂ + C₁ * δ₂) * singularWeight ρ x ^ min (η - 𝒯.deg k) 0 := by ring
      _ ≤ P.truncMulConst * ((δ₁ * C₂ + C₁ * δ₂ + 2 * C₁ * C₂ * δΓ) * (1 + CΓ) ^ 2) *
          singularWeight ρ x ^ min (η - 𝒯.deg k) 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul P.const_le_truncMulConst hY (by positivity)
            P.truncMulConst_nonneg) hp
      _ = _ := by ring
  · exact M₁.abs_truncMul_diffIncrement_le_singular_near M₂ P hV hW hVα hWα hγ₁ hγ₂ hη₁ hη₂ hη₁₂
      hηγ hreg hf₁V hg₁V hf₂W hg₂W hf₁T hg₁T hf₂T hg₂T hf₁ hg₁ hf₂ hδ₁ hδ₂ hC₁ hC₂ hδ₁0 hδ₂0
      hΓ₁₂ hΓ₂₁ hΓ₂₂ hΓd₁ hΓd₂ hCΓ hδΓ hx hy hρx hρy hd hk

end Model

end RegularityStructures

end
