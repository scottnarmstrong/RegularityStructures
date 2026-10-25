/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointTruncation
public import RegularityStructures.Abstract.ModelNear

/-!
# Near-pair `Γ` version of `RegularityStructures.Abstract.FixedPointTruncation`

The statements of `RegularityStructures.Abstract.FixedPointTruncation` that involve `Γ`-bounds, for
models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- **Truncation on `D^{γ',η'}_P`**: for `γ ≤ γ'`,
`|||Q_{<γ} f|||_{γ, η' ∧ γ; S} ≤ (1 + |ι| C_Γ) |||f|||_{γ',η';S}`. -/
theorem SingularBoundOn.lowerProj_near {ρ : E → ℝ} {γ γ' η' C CΓ : ℝ} {S : Set E} {f : E → ι → ℝ}
    (hf : M.SingularBoundOn ρ γ' η' C S f)
    (hfT : ∀ x ∈ S, 0 < ρ x → f x ∈ lowerSubspace 𝒯.deg γ') (hγ : γ ≤ γ')
    (hΓ : M.GammaNearOn γ' CΓ S) (hC : 0 ≤ C) (hCΓ : 0 ≤ CΓ) :
    M.SingularBoundOn ρ γ (min η' γ) (C * (1 + Fintype.card ι * CΓ)) S
      (fun x => RegularityStructures.lowerProj 𝒯.deg γ (f x)) := by
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hC1 : C ≤ C * (1 + Fintype.card ι * CΓ) := by nlinarith [mul_nonneg hN hCΓ]
  refine ⟨fun x hx hρ i hi => ?_, fun x hx y hy hρx hρy hd j hj => ?_⟩
  · have hw0 := singularWeight_pos hρ
    show |RegularityStructures.lowerProj 𝒯.deg γ (f x) i| ≤ _
    rw [lowerProj_apply_of_lt hi]
    refine (hf.1 x hx hρ i (hi.trans_le hγ)).trans (mul_le_mul hC1 ?_
      (Real.rpow_nonneg hw0.le _) (by positivity))
    exact Real.rpow_le_rpow_of_exponent_ge hw0 (singularWeight_le_one ρ x)
      (min_le_min (by linarith [min_le_left η' γ]) le_rfl)
  · set w := min (singularWeight ρ x) (singularWeight ρ y) with hw_def
    set d := K.scaleDist y x with hd_def
    have hw0 : 0 < w := lt_min (singularWeight_pos hρx) (singularWeight_pos hρy)
    have hw1 : w ≤ 1 := (min_le_left _ _).trans (singularWeight_le_one ρ x)
    have hd0 : 0 ≤ d := K.scaleDist_nonneg y x
    have hj' : 𝒯.deg j < γ' := hj.trans_le hγ
    set X : ℝ := d ^ (γ - 𝒯.deg j) * w ^ (min η' γ - γ) with hX
    have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hw0.le _)
    -- the high part `r = f x − Q_{<γ} f x`
    set r : ι → ℝ := f x - RegularityStructures.lowerProj 𝒯.deg γ (f x) with hr
    have hdec : (RegularityStructures.lowerProj 𝒯.deg γ (f y) -
        M.gammaMap y x (RegularityStructures.lowerProj 𝒯.deg γ (f x))) j =
        (f y - M.gammaMap y x (f x)) j + M.gammaMap y x r j := by
      simp only [hr, map_sub, Pi.sub_apply, lowerProj_apply_of_lt hj]
      ring
    -- first term
    have h1 : |(f y - M.gammaMap y x (f x)) j| ≤ C * X := by
      refine (hf.2 x hx y hy hρx hρy hd j hj').trans ?_
      rw [mul_assoc, hX]
      exact mul_le_mul_of_nonneg_left (rpow_mul_rpow_le_rpow_mul_rpow hd0 hd hw0 hw1
        (by linarith) (by linarith) (by linarith [min_le_left η' γ])) hC
    -- second term
    have hterm : ∀ i, |r i * M.gammaMap y x (Pi.single i 1) j| ≤ C * CΓ * X := by
      intro i
      by_cases hiγ : 𝒯.deg i < γ
      · rw [hr, Pi.sub_apply, lowerProj_apply_of_lt hiγ, sub_self, zero_mul, abs_zero]
        positivity
      by_cases hiγ' : 𝒯.deg i < γ'
      · have hri : r i = f x i := by
          rw [hr, Pi.sub_apply, lowerProj_apply_of_le (not_lt.1 hiγ), sub_zero]
        have hji : 𝒯.deg j < 𝒯.deg i := hj.trans_le (not_lt.1 hiγ)
        have hfx := hf.abs_apply_le_weight M hC (hfT x hx hρx) hx hρx hw0 (min_le_left _ _) i
        have hΓij := hΓ i j hiγ' hji x hx y hy (le_gammaNearRadius_of_le_one (hd.trans hw1))
        rw [hri, abs_mul]
        calc |f x i| * |M.gammaMap y x (Pi.single i 1) j|
            ≤ (C * w ^ min (η' - 𝒯.deg i) 0) * (CΓ * d ^ (𝒯.deg i - 𝒯.deg j)) := by
              refine mul_le_mul hfx ?_ (abs_nonneg _) (by positivity)
              simpa [hd_def, K.scaleDist_nonneg] using hΓij
          _ = C * CΓ * (d ^ (𝒯.deg i - 𝒯.deg j) * w ^ min (η' - 𝒯.deg i) 0) := by ring
          _ ≤ C * CΓ * X := by
              refine mul_le_mul_of_nonneg_left (rpow_mul_rpow_le_rpow_mul_rpow hd0 hd hw0 hw1
                (by linarith) (by linarith [not_lt.1 hiγ]) ?_) (mul_nonneg hC hCΓ)
              rcases min_cases (η' - 𝒯.deg i) 0 with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;>
                linarith [min_le_left η' γ, min_le_right η' γ, not_lt.1 hiγ]
      · have hri : r i = 0 := by
          rw [hr, Pi.sub_apply, lowerProj_apply_of_le (not_lt.1 hiγ),
            hfT x hx hρx i (not_lt.1 hiγ'), sub_zero]
        rw [hri, zero_mul, abs_zero]
        positivity
    have h2 : |M.gammaMap y x r j| ≤ Fintype.card ι * (C * CΓ * X) := by
      rw [M.gammaMap_apply_eq_sum x y r j]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
      simp
    rw [hdec]
    calc |(f y - M.gammaMap y x (f x)) j + M.gammaMap y x r j|
        ≤ C * X + Fintype.card ι * (C * CΓ * X) := (abs_add_le _ _).trans (add_le_add h1 h2)
      _ = C * (1 + Fintype.card ι * CΓ) * d ^ (γ - 𝒯.deg j) * w ^ (min η' γ - γ) := by
        rw [hX]
        ring

variable {M} {ρ : E → ℝ} {V V' : Submodule ℝ (ι → ℝ)} {γ η γ' η' : ℝ} {S : Set E}

/-- **Theorems 7.1 and 7.8 with Hairer's exponent conditions.** Let `𝒦 = Q_{<γ} 𝒦₀` on the slab,
where for every `g`, `𝒦₀ g` takes values in `T_{<γ_K}`, satisfies the bound of `D^{γ_K,η_K}_P`
on the slab with constant `C |||g|||` and the vanishing bound
`|(𝒦₀ g)(x)_i| ≤ C |||g||| ‖x‖_P^{η_K − deg i}` (the conclusions of the proof of
[Hai14, Theorem 7.1], `C` independent of `T`). If `γ ≤ γ_K` (Hairer: `γ < γ̄ + 2q`),
`η < η_K` (Hairer: `η < (η̄ ∧ ζ̄) + 2q`), `η < γ`, `‖Γ‖ ≤ C_Γ` and `ρ ≤ T^{1/𝔰₀}` on the slab, then
for `0 < T ≤ fixedPointTime (C (1 + |ι| C_Γ)) (((η_K ∧ γ) − η)/𝔰₀) L₀ A R₀ p` the equation
`U = 𝒦 (F U) + v` has a unique solution with `|||U|||_{γ,η;T} ≤ R₀ + 1`. -/
theorem exists_unique_slab_fixedPoint_of_integration_near {γK ηK C CΓ s L₀ A R₀ T : ℝ} {p : ℕ}
    (hγK : γ ≤ γK) (hηK : η < ηK) (hηγ : η < γ) (hC : 0 ≤ C) (hCΓ : 0 ≤ CΓ) (hs : 0 < s)
    (hL₀ : 0 ≤ L₀) (hA : 0 ≤ A) (hR₀ : 0 ≤ R₀) (hT : 0 < T)
    (hTT₀ : T ≤ fixedPointTime (C * (1 + Fintype.card ι * CΓ)) ((min ηK γ - η) / s) L₀ A R₀ p)
    (hS : ∀ x ∈ S, 0 < ρ x → ρ x ≤ T ^ s⁻¹) (hΓ : M.GammaNearOn γK CΓ S)
    (𝒦₀ : M.SlabSpace ρ V' γ' η' S → E → ι → ℝ)
    (h𝒦₀T : ∀ g, ∀ x ∈ S, 0 < ρ x → 𝒦₀ g x ∈ lowerSubspace 𝒯.deg γK)
    (h𝒦₀ : ∀ g, M.SingularBoundOn ρ γK ηK (C * ‖g‖) S (𝒦₀ g))
    (h𝒦₀sup : ∀ g, ∀ x ∈ S, 0 < ρ x → ∀ i, 𝒯.deg i < γK →
      |𝒦₀ g x i| ≤ C * ‖g‖ * singularWeight ρ x ^ (ηK - 𝒯.deg i))
    (𝒦 : M.SlabSpace ρ V' γ' η' S →ₗ[ℝ] M.SlabSpace ρ V γ η S)
    (h𝒦 : ∀ g, ∀ x ∈ S, 0 < ρ x →
      (𝒦 g).val x = RegularityStructures.lowerProj 𝒯.deg γ (𝒦₀ g x))
    (F : M.SlabSpace ρ V γ η S → M.SlabSpace ρ V' γ' η' S)
    (hF : ∀ R u u', ‖u‖ ≤ R → ‖u'‖ ≤ R → ‖F u - F u'‖ ≤ L₀ * (1 + R) ^ p * ‖u - u'‖)
    (hF0 : ‖F 0‖ ≤ A) (v : M.SlabSpace ρ V γ η S) (hv : ‖v‖ ≤ R₀) :
    ∃! U : M.SlabSpace ρ V γ η S, ‖U‖ ≤ R₀ + 1 ∧ U = 𝒦 (F U) + v := by
  set κ := min ηK γ - η with hκ_def
  have hκ : 0 < κ := by
    rw [hκ_def]
    exact sub_pos.2 (lt_min hηK hηγ)
  have hηκ : η + κ = min ηK γ := by rw [hκ_def]; ring
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hC1 : C ≤ C * (1 + Fintype.card ι * CΓ) := by nlinarith [mul_nonneg hN hCΓ]
  refine exists_unique_slab_fixedPoint_of_vanishing M (by positivity) hκ hs hL₀ hA hR₀ hT hTT₀
    hS 𝒦 (fun g x hx hρ i hi => ?_) (fun g => ?_) F hF hF0 v hv
  · have hw0 := singularWeight_pos hρ
    rw [h𝒦 g x hx hρ, lowerProj_apply_of_lt hi]
    refine (h𝒦₀sup g x hx hρ i (hi.trans_le hγK)).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hC1 (norm_nonneg g)) ?_ (Real.rpow_nonneg hw0.le _)
      (by positivity))
    refine Real.rpow_le_rpow_of_exponent_ge hw0 (singularWeight_le_one ρ x) ?_
    rw [hηκ]
    linarith [min_le_left ηK γ]
  · have ht := (h𝒦₀ g).lowerProj_near M (h𝒦₀T g) hγK hΓ (mul_nonneg hC (norm_nonneg g)) hCΓ
    rw [hηκ]
    refine (ht.congr M fun x hx hρ => (h𝒦 g x hx hρ).symm).mono M (le_of_eq ?_)
    ring

end Model

end RegularityStructures

end
