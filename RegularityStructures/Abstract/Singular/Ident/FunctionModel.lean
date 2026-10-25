/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
public import RegularityStructures.Abstract.Integration.Theorem512.Helpers
public import RegularityStructures.Abstract.QFamilyContinuousModel
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Abstract.Integration.Commute.Reg

/-!
# Models realised by smooth functions of polynomial growth

[Hai14, Remark 3.15] for models whose components are continuous functions of polynomial growth
(rather than bounded functions).  `Model.IsSmoothFunctionModelBelow M g γ` says that for
`deg i < γ` the distribution `Π_x e_i` is the `Q`-family of the continuous function `g x i`, jointly
continuous in `(x, y)`, with polynomial growth in `y` (for each `x`) and along the diagonal.

For `τ ∈ T_{<γ}` put `fnComb g γ x τ y = ∑_{deg i < γ} τ_i g_{x,i}(y)`.  Then

* `Model.regPi_eq_apply_fnComb`: `Q_t Π_x τ = Q_t (fnComb g γ x τ)`;
* `Model.pairing_regPi_eq_integral`: `⟨Π_x τ, φ⟩ = ∫ fnComb g γ x τ · φ` for continuous compactly
  supported `φ`;
* `Model.fnComb_eq_fnComb_gammaMap`: `Π_x τ (y) = (Π_y Γ_{yx} τ)(y)` pointwise;
* `Model.diag_eq_zero_of_isSmooth`: `g_{y,i}(y) = 0` for `0 < deg i < γ` if the `Π`-bound holds at `y`.

Source: [Hai14] = arXiv:1303.5113v4, Remark 3.15.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- The model is realised in degrees `< γ` by continuous functions of polynomial growth:
`Q_t Π_x e_i = Q_t g_{x,i}` for `t > 0`. -/
structure IsSmoothFunctionModelBelow (M : Model 𝒯 parabolicSemigroup)
    (g : ParabolicSpace → ι → ParabolicSpace → ℝ) (γ : ℝ) : Prop where
  regPi_eq : ∀ x i, 𝒯.deg i < γ → ∀ t : ℝ, 0 < t → ∀ y,
    M.regPi x (Pi.single i 1) t y = parabolicSemigroup.apply t (g x i) y
  continuous : ∀ i, 𝒯.deg i < γ →
    Continuous (fun p : ParabolicSpace × ParabolicSpace => g p.1 i p.2)
  growth : ∀ x i, 𝒯.deg i < γ →
    ∃ (B : ℝ) (n : ℕ), ∀ u, |g x i u| ≤ B * (1 + parabolicNorm u) ^ n
  diag_growth : ∃ (B : ℝ) (n : ℕ), ∀ y i, 𝒯.deg i < γ →
    |g y i y| ≤ B * (1 + parabolicNorm y) ^ n

/-- `∑_{deg i < γ} τ_i g_{x,i}(y)`, the function representing `Π_x τ` for `τ ∈ T_{<γ}`. -/
def fnComb (𝒯 : RegularityStructure ι) (g : ParabolicSpace → ι → ParabolicSpace → ℝ) (γ : ℝ)
    (x : ParabolicSpace) (τ : ι → ℝ) (y : ParabolicSpace) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ), τ i * g x i y

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ} {γ : ℝ}

namespace IsSmoothFunctionModelBelow

variable (hg : M.IsSmoothFunctionModelBelow g γ)
include hg

theorem continuous_apply {i : ι} (hi : 𝒯.deg i < γ) (x : ParabolicSpace) :
    Continuous (g x i) :=
  (hg.continuous i hi).comp (continuous_const.prodMk continuous_id)

theorem polyBounded {i : ι} (hi : 𝒯.deg i < γ) (x : ParabolicSpace) : PolyBounded (g x i) := by
  obtain ⟨B, n, hB⟩ := hg.growth x i hi
  exact ⟨(hg.continuous_apply hi x).measurable, B, n, hB⟩

theorem continuous_fnComb (x : ParabolicSpace) (τ : ι → ℝ) :
    Continuous (fnComb 𝒯 g γ x τ) := by
  unfold fnComb
  exact continuous_finsetSum _ fun i hi =>
    continuous_const.mul (hg.continuous_apply (Finset.mem_filter.1 hi).2 x)

theorem polyBounded_fnComb (x : ParabolicSpace) (τ : ι → ℝ) :
    PolyBounded (fnComb 𝒯 g γ x τ) :=
  PolyBounded.finsetSum _ τ (fun i => g x i) fun _ hi =>
    hg.polyBounded (Finset.mem_filter.1 hi).2 x

theorem diag_continuous {i : ι} (hi : 𝒯.deg i < γ) : Continuous (fun y => g y i y) :=
  (hg.continuous i hi).comp (continuous_id.prodMk continuous_id)

end IsSmoothFunctionModelBelow

variable (hg : M.IsSmoothFunctionModelBelow g γ)
include hg

/-- `Q_t Π_x τ = Q_t (fnComb g γ x τ)` for `τ ∈ T_{<γ}`, `t > 0`. -/
theorem regPi_eq_apply_fnComb {x : ParabolicSpace} {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) {t : ℝ} (ht : 0 < t) (y : ParabolicSpace) :
    M.regPi x τ t y = parabolicSemigroup.apply t (fnComb 𝒯 g γ x τ) y := by
  unfold fnComb
  rw [PolyBounded.apply_finsetSum _ τ (fun i => g x i)
    (fun i hi => hg.polyBounded (Finset.mem_filter.1 hi).2 x) ht, M.regPi_eq_sum x τ t y,
    ← Finset.sum_filter_of_ne (p := fun i => 𝒯.deg i < γ)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [hg.regPi_eq x i (Finset.mem_filter.1 hi).2 t ht y]
  · intro i _ hne
    by_contra hlt
    exact hne (by rw [(mem_lowerSubspace).1 hτ i (not_lt.1 hlt), zero_mul])

/-- The approximate identity at the base point: `(Q_t Π_x τ)(y) → ∑_i τ_i g_{x,i}(y)`. -/
theorem tendsto_regPi_lower {x : ParabolicSpace} {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (y : ParabolicSpace) :
    Tendsto (fun t => M.regPi x τ t y) (𝓝[>] 0) (𝓝 (fnComb 𝒯 g γ x τ y)) := by
  refine ((hg.polyBounded_fnComb x τ).tendsto_apply_nhdsGT (hg.continuous_fnComb x τ) y).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (regPi_eq_apply_fnComb hg hτ ht y).symm

/-- `⟨Π_x τ, φ⟩ = ∫ fnComb g γ x τ · φ` for continuous compactly supported `φ`. -/
theorem pairing_regPi_eq_integral {x : ParabolicSpace} {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) {φ : ParabolicSpace → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    parabolicSemigroup.pairing (M.regPi x τ) φ = ∫ y, fnComb 𝒯 g γ x τ y * φ y := by
  obtain ⟨_, B, n, hB⟩ := hg.polyBounded_fnComb x τ
  exact pairing_eq_integral_of_bound (hg.continuous_fnComb x τ) hB hφ hφc fun s hs =>
    funext fun y => regPi_eq_apply_fnComb hg hτ hs y

/-- `Π_x τ (y) = (Π_y Γ_{yx} τ)(y)` pointwise. -/
theorem fnComb_eq_fnComb_gammaMap {x : ParabolicSpace} {τ : ι → ℝ}
    (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (y : ParabolicSpace) :
    fnComb 𝒯 g γ x τ y = fnComb 𝒯 g γ y (M.gammaMap y x τ) y := by
  have hτ' : M.gammaMap y x τ ∈ lowerSubspace 𝒯.deg γ :=
    (M.isGradedUnipotent_gammaMap y x).map_lowerSubspace hτ
  have h1 := tendsto_regPi_lower (x := x) hg hτ y
  have h2 := tendsto_regPi_lower (x := y) hg hτ' y
  simp only [M.regPi_gammaMap y x τ] at h2
  exact tendsto_nhds_unique h1 h2

/-- `g_{y,i}(y) = 0` for `0 < deg i < γ` when the `Π`-bound holds at `y`. -/
theorem diag_eq_zero_of_isSmooth {CPi : ℝ} {S : Set ParabolicSpace} (hPi : M.PiBoundOn γ CPi S)
    {i : ι} (hi0 : 0 < 𝒯.deg i) (hiγ : 𝒯.deg i < γ) {y : ParabolicSpace} (hy : y ∈ S) :
    g y i y = 0 := by
  have hmem : (Pi.single i 1 : ι → ℝ) ∈ lowerSubspace 𝒯.deg γ := by
    refine (mem_lowerSubspace).2 fun j hj => ?_
    by_cases hji : j = i
    · subst hji; exact absurd hiγ (not_lt.2 hj)
    · simp [hji]
  have h1 : Tendsto (fun t => M.regPi y (Pi.single i 1) t y) (𝓝[>] 0) (𝓝 (g y i y)) := by
    have := tendsto_regPi_lower (x := y) hg hmem y
    simpa [fnComb, Finset.sum_filter, Pi.single_apply, hiγ] using this
  have hp : 0 < 𝒯.deg i / parabolicSemigroup.order := div_pos hi0 parabolicSemigroup.order_pos
  have h2 : Tendsto (fun t : ℝ => CPi * t ^ (𝒯.deg i / parabolicSemigroup.order)) (𝓝[>] 0)
      (𝓝 0) := by
    have := ((Real.continuous_rpow_const hp.le).const_mul CPi).tendsto 0
    rw [Real.zero_rpow hp.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : |g y i y| ≤ 0 := le_of_tendsto_of_tendsto h1.abs h2
    (Filter.mem_of_superset (Ioc_mem_nhdsGT one_pos) fun t ht => hPi i hiγ t ht y hy)
  exact abs_nonpos_iff.1 hle

omit hg in
/-- `pointwiseReconstruct g f y = ∑_{deg i < γ} f(y)_i g_{y,i}(y)` when `f y ∈ T_{<γ}`. -/
theorem pointwiseReconstruct_eq_fnComb {f : ParabolicSpace → ι → ℝ} (y : ParabolicSpace)
    (hfy : f y ∈ lowerSubspace 𝒯.deg γ) :
    pointwiseReconstruct g f y = fnComb 𝒯 g γ y (f y) y := by
  unfold pointwiseReconstruct fnComb
  rw [Finset.sum_filter_of_ne]
  intro i _ hne
  by_contra hlt
  exact hne (by rw [(mem_lowerSubspace).1 hfy i (not_lt.1 hlt), zero_mul])

end Model

end RegularityStructures

end
