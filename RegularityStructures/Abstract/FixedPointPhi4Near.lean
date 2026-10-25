/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointPhi4
public import RegularityStructures.Abstract.WeightedSingularCubeNear
public import RegularityStructures.Abstract.WeightedSingularCubeTwoModelsNear
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.FixedPointPhi4`

The statements of `RegularityStructures.Abstract.FixedPointPhi4` that involve `Γ`-bounds, for models
whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct) {E : Type*}

end RegularityStructure.GradedProduct

end RegularityStructures

end

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {V : Submodule ℝ (ι → ℝ)} {γ η : ℝ} {S : Set E}

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} {M : Model 𝒯 K}
  {ρ : E → ℝ} {S : Set E} (P : 𝒯.GradedProduct) {V W : Submodule ℝ (ι → ℝ)}
  {α γ₀ η₀ η' η'' CΓ : ℝ} (hV : 𝒯.IsSector V) (hW : 𝒯.IsSector W)
  (hVα : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
  (hWα : RegularityStructure.IsSector.OfRegularity 𝒯 W (α + α))
  (hVVW : ∀ a ∈ V, ∀ b ∈ V, P.mul a b ∈ W) (hreg₁ : P.IsRegularPair V V (γ₀ + α))
  (hreg₂ : P.IsRegularPair V W (γ₀ + α + α)) (hη'₁ : η' ≤ η₀ + α) (hη'₂ : η' ≤ η₀ + η₀)
  (hη'γ : η' ≤ γ₀ + α) (hη''₁ : η'' ≤ η₀ + (α + α)) (hη''₂ : η'' ≤ η' + α)
  (hη''₃ : η'' ≤ η₀ + η') (hη''γ : η'' ≤ γ₀ + α + α)

include hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ

/-- The cube of an element of `D^{γ₀,η₀}_P(V)` on the slab lies in `D^{γ₀+2α,η''}_P` on the slab,
with `|||U³||| ≤ c² |||U|||³ (1 + C_Γ)⁴` ([Hai14, Lemma 9.7]). -/
theorem SlabSpace.truncCube_mem_near (u : M.SlabSpace ρ V γ₀ η₀ S) (hΓ₀ : M.GammaNearOn γ₀ CΓ S)
    (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) :
    P.truncCube (γ₀ + α + α) u.val ∈ M.slabModelledDistributions ρ ⊤ (γ₀ + α + α) η'' S ∧
      M.SingularBoundOn ρ (γ₀ + α + α) η''
        (P.truncMulConst ^ 2 * ‖u‖ ^ 3 * (1 + CΓ) ^ 4) S (P.truncCube (γ₀ + α + α) u.val) := by
  have hb := M.singularBoundOn_truncCube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁
    hη''₂ hη''₃ hη''γ (fun x hx hρ => (Submodule.mem_inf.1 (u.mem_inf hx hρ)).1)
    (fun x hx hρ => (Submodule.mem_inf.1 (u.mem_inf hx hρ)).2) u.singularBoundOn_norm
    (norm_nonneg u) hΓ₀ hΓ₁ hCΓ
  refine ⟨⟨P.measurable_truncCube _ u.measurable, fun x _ _ => Submodule.mem_inf.2
    ⟨Submodule.mem_top, lowerProj_mem _⟩, fun x hx => P.truncCube_apply_eq_zero _
    (u.apply_eq_zero hx), _, hb⟩, hb⟩

theorem SlabSpace.val_cube_near (u : M.SlabSpace ρ V γ₀ η₀ S) (hΓ₀ : M.GammaNearOn γ₀ CΓ S)
    (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) :
    (SlabSpace.cube P (γ₀ + α + α) η'' u).val = P.truncCube (γ₀ + α + α) u.val := by
  rw [SlabSpace.cube, dite_eq_left (SlabSpace.truncCube_mem_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂
    hη'γ hη''₁ hη''₂ hη''₃ hη''γ u hΓ₀ hΓ₁ hCΓ).1, SlabSpace.val_mk]

theorem SlabSpace.norm_cube_le_near (u : M.SlabSpace ρ V γ₀ η₀ S) (hΓ₀ : M.GammaNearOn γ₀ CΓ S)
    (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) :
    ‖SlabSpace.cube P (γ₀ + α + α) η'' u‖ ≤ P.truncMulConst ^ 2 * ‖u‖ ^ 3 * (1 + CΓ) ^ 4 := by
  refine SlabSpace.norm_le _ (by positivity) ?_
  rw [SlabSpace.val_cube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ u
    hΓ₀ hΓ₁ hCΓ]
  exact (SlabSpace.truncCube_mem_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃
    hη''γ u hΓ₀ hΓ₁ hCΓ).2

/-- **Local Lipschitz bound for the cube** ([Hai14, Lemma 9.7]), with a constant polynomial in
the radius: `|||U³ − U'³||| ≤ 3 c² (1 + C_Γ)⁴ (1 + R)² |||U − U'|||` for `|||U|||, |||U'||| ≤ R`. -/
theorem SlabSpace.norm_cube_sub_cube_le_near (hΓ₀ : M.GammaNearOn γ₀ CΓ S)
    (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S) (hCΓ : 0 ≤ CΓ) (R : ℝ)
    (u u' : M.SlabSpace ρ V γ₀ η₀ S) (hu : ‖u‖ ≤ R) (hu' : ‖u'‖ ≤ R) :
    ‖SlabSpace.cube P (γ₀ + α + α) η'' u - SlabSpace.cube P (γ₀ + α + α) η'' u'‖ ≤
      3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * (1 + R) ^ 2 * ‖u - u'‖ := by
  have hc := P.truncMulConst_nonneg
  have hR : 0 ≤ R := (norm_nonneg u).trans hu
  have hb := M.singularBoundOn_truncCube_sub_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ (fun x hx hρ => (Submodule.mem_inf.1 (u.mem_inf hx hρ)).1)
    (fun x hx hρ => (Submodule.mem_inf.1 (u'.mem_inf hx hρ)).1)
    (fun x hx hρ => (Submodule.mem_inf.1 (u.mem_inf hx hρ)).2)
    (fun x hx hρ => (Submodule.mem_inf.1 (u'.mem_inf hx hρ)).2) u.singularBoundOn_norm
    u'.singularBoundOn_norm (by simpa using (u - u').singularBoundOn_norm) (norm_nonneg u)
    (norm_nonneg u') (norm_nonneg _) hΓ₀ hΓ₁ hCΓ
  have hpoly : ‖u‖ ^ 2 + ‖u'‖ * ‖u‖ + ‖u'‖ ^ 2 ≤ 3 * (1 + R) ^ 2 := by
    have h1 := norm_nonneg u
    have h2 := norm_nonneg u'
    nlinarith
  refine SlabSpace.norm_le _ (by positivity) ?_
  rw [SlabSpace.val_sub, SlabSpace.val_cube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁
    hη''₂ hη''₃ hη''γ u hΓ₀ hΓ₁ hCΓ, SlabSpace.val_cube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂
    hη'γ hη''₁ hη''₂ hη''₃ hη''γ u' hΓ₀ hΓ₁ hCΓ]
  refine hb.mono M ?_
  have hn := norm_nonneg (u - u')
  calc P.truncMulConst ^ 2 * ‖u - u'‖ * (‖u‖ ^ 2 + ‖u'‖ * ‖u‖ + ‖u'‖ ^ 2) * (1 + CΓ) ^ 4
      = (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * ‖u - u'‖) *
        (‖u‖ ^ 2 + ‖u'‖ * ‖u‖ + ‖u'‖ ^ 2) := by ring
    _ ≤ (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * ‖u - u'‖) * (3 * (1 + R) ^ 2) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = 3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * (1 + R) ^ 2 * ‖u - u'‖ := by ring

theorem SlabSpace.cube_zero_near (hΓ₀ : M.GammaNearOn γ₀ CΓ S) (hΓ₁ : M.GammaNearOn (γ₀ + α) CΓ S)
    (hCΓ : 0 ≤ CΓ) :
    SlabSpace.cube P (γ₀ + α + α) η'' (0 : M.SlabSpace ρ V γ₀ η₀ S) = 0 := by
  have h := SlabSpace.norm_cube_le_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂
    hη''₃ hη''γ (0 : M.SlabSpace ρ V γ₀ η₀ S) hΓ₀ hΓ₁ hCΓ
  rw [norm_zero, zero_pow (by norm_num), mul_zero, zero_mul] at h
  exact norm_le_zero_iff.1 h

/-- **[Hai14, Proposition 9.8], continuity in the model.** For two models `M₁, M₂` with
`‖Γⁱ‖ ≤ C_Γ` and `‖Γ¹ − Γ²‖ ≤ δ_Γ` on the slab, integration operators `𝒦₁, 𝒦₂` with the
two-model bound `|||𝒦₁ g; 𝒦₂ ḡ||| ≤ C T^θ |||g; ḡ||| + ε_𝒦` (for `|||g|||, |||ḡ||| ≤ B`,
`B = c² (R₀ + 1)³ (1 + C_Γ)⁴`), data with `|||v₁; v₂||| ≤ δ_v`, and
`0 < T ≤ fixedPointTime C θ (3 c² (1 + C_Γ)⁴) 0 R₀ 2`, the solutions of `Uᵢ = −𝒦ᵢ(Uᵢ³) + vᵢ` with
`|||Uᵢ||| ≤ R₀ + 1` satisfy
`|||U₁; U₂|||_{γ₀,η₀;T} ≤ 2 (δ_v + C T^θ · 4 c² (R₀ + 1)³ (1 + C_Γ)⁴ δ_Γ + ε_𝒦)`. -/
theorem singularDiffBoundOn_phi4_slab_fixedPoint_near {M₁ M₂ : Model 𝒯 K} {δΓ : ℝ}
    (hΓ₁₀ : M₁.GammaNearOn γ₀ CΓ S) (hΓ₁₁ : M₁.GammaNearOn (γ₀ + α) CΓ S)
    (hΓ₂₀ : M₂.GammaNearOn γ₀ CΓ S) (hΓ₂₁ : M₂.GammaNearOn (γ₀ + α) CΓ S)
    (hΓd₀ : M₁.GammaDiffNearOn M₂ γ₀ δΓ S) (hΓd₁ : M₁.GammaDiffNearOn M₂ (γ₀ + α) δΓ S)
    (hCΓ : 0 ≤ CΓ) (hδΓ : 0 ≤ δΓ) {C θ R₀ T ε𝒦 δv : ℝ} (hC : 0 ≤ C) (hθ : 0 < θ)
    (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime C θ (3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) 0 R₀ 2)
    (hε𝒦 : 0 ≤ ε𝒦) (hδv : 0 ≤ δv)
    (𝒦₁ : M₁.SlabSpace ρ ⊤ (γ₀ + α + α) η'' S →ₗ[ℝ] M₁.SlabSpace ρ V γ₀ η₀ S)
    (𝒦₂ : M₂.SlabSpace ρ ⊤ (γ₀ + α + α) η'' S →ₗ[ℝ] M₂.SlabSpace ρ V γ₀ η₀ S)
    (h𝒦 : ∀ g₁ g₂ b, ‖g₁‖ ≤ P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 →
      ‖g₂‖ ≤ P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 → 0 ≤ b →
      M₁.SingularDiffBoundOn M₂ ρ (γ₀ + α + α) η'' b S g₁.val g₂.val →
      M₁.SingularDiffBoundOn M₂ ρ γ₀ η₀ (C * T ^ θ * b + ε𝒦) S (𝒦₁ g₁).val (𝒦₂ g₂).val)
    {v₁ U₁ : M₁.SlabSpace ρ V γ₀ η₀ S} {v₂ U₂ : M₂.SlabSpace ρ V γ₀ η₀ S}
    (hv : M₁.SingularDiffBoundOn M₂ ρ γ₀ η₀ δv S v₁.val v₂.val) (hU₁ : ‖U₁‖ ≤ R₀ + 1)
    (hU₂ : ‖U₂‖ ≤ R₀ + 1) (hfix₁ : U₁ = -𝒦₁ (SlabSpace.cube P (γ₀ + α + α) η'' U₁) + v₁)
    (hfix₂ : U₂ = -𝒦₂ (SlabSpace.cube P (γ₀ + α + α) η'' U₂) + v₂) :
    M₁.SingularDiffBoundOn M₂ ρ γ₀ η₀
      (2 * (δv + C * T ^ θ * (4 * P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 * δΓ) +
        ε𝒦)) S U₁.val U₂.val := by
  have hc := P.truncMulConst_nonneg
  set B := P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 with hB
  have hFB : ∀ (M' : Model 𝒯 K), M'.GammaNearOn γ₀ CΓ S → M'.GammaNearOn (γ₀ + α) CΓ S →
      ∀ u : M'.SlabSpace ρ V γ₀ η₀ S, ‖u‖ ≤ R₀ + 1 →
        ‖-SlabSpace.cube P (γ₀ + α + α) η'' u‖ ≤ B := by
    intro M' h₀ h₁ u hu
    rw [norm_neg]
    refine (SlabSpace.norm_cube_le_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂
      hη''₃ hη''γ u h₀ h₁ hCΓ).trans ?_
    have := norm_nonneg u
    rw [hB]
    gcongr
  refine singularDiffBoundOn_slab_fixedPoint_of_le_fixedPointTime (A := 0) (B := B) hC hθ
    (by positivity) le_rfl hR₀ hT hTT₀ (by positivity) hε𝒦 hδv 𝒦₁ 𝒦₂ h𝒦
    (fun u => -SlabSpace.cube P (γ₀ + α + α) η'' u)
    (fun u => -SlabSpace.cube P (γ₀ + α + α) η'' u) ?_ (hFB M₁ hΓ₁₀ hΓ₁₁) (hFB M₂ hΓ₂₀ hΓ₂₁) hv
    hU₁ hU₂ (by rw [map_neg]; exact hfix₁) (by rw [map_neg]; exact hfix₂)
  intro u₁ u₂ a hu₁ hu₂ ha hδ
  have hR1 : 0 ≤ R₀ + 1 := by linarith
  have hd := M₁.singularDiffBoundOn_truncCube_near M₂ P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ
    hη''₁ hη''₂ hη''₃ hη''γ (fun x hx hρ => (Submodule.mem_inf.1 (u₁.mem_inf hx hρ)).1)
    (fun x hx hρ => (Submodule.mem_inf.1 (u₂.mem_inf hx hρ)).1)
    (fun x hx hρ => (Submodule.mem_inf.1 (u₁.mem_inf hx hρ)).2)
    (fun x hx hρ => (Submodule.mem_inf.1 (u₂.mem_inf hx hρ)).2)
    (u₁.singularBoundOn_norm.mono M₁ hu₁) (u₂.singularBoundOn_norm.mono M₂ hu₂) hδ hR1 ha
    hΓ₁₀ hΓ₁₁ hΓ₂₀ hΓ₂₁ hΓd₀ hΓd₁ hCΓ hδΓ
  rw [← SlabSpace.val_cube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁ hη''₂ hη''₃ hη''γ
    u₁ hΓ₁₀ hΓ₁₁ hCΓ, ← SlabSpace.val_cube_near P hV hW hVα hWα hVVW hreg₁ hreg₂ hη'₁ hη'₂ hη'γ hη''₁
    hη''₂ hη''₃ hη''γ u₂ hΓ₂₀ hΓ₂₁ hCΓ] at hd
  have hd' := hd.neg
  rw [← SlabSpace.val_neg, ← SlabSpace.val_neg] at hd'
  refine hd'.mono ?_
  have hR2 : (R₀ + 1) ^ 2 ≤ (2 + R₀) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h4 : 0 ≤ P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 := by positivity
  calc P.truncMulConst ^ 2 * (3 * (R₀ + 1) ^ 2 * a + 4 * (R₀ + 1) ^ 3 * δΓ) * (1 + CΓ) ^ 4
      = 3 * (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * (R₀ + 1) ^ 2 * a +
        4 * P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 * δΓ := by ring
    _ ≤ 3 * (P.truncMulConst ^ 2 * (1 + CΓ) ^ 4) * (2 + R₀) ^ 2 * a +
        4 * P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 * δΓ := by gcongr
    _ = 3 * P.truncMulConst ^ 2 * (1 + CΓ) ^ 4 * (2 + R₀) ^ 2 * a +
        4 * P.truncMulConst ^ 2 * (R₀ + 1) ^ 3 * (1 + CΓ) ^ 4 * δΓ := by ring

end Model

end RegularityStructures

end
