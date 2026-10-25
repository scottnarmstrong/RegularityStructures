/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.LatticeLimit
public import RegularityStructures.Abstract.Singular.Ident.DomIntegrable

/-!
# Lattice reconstruction as an integral, near-pair `Γ`-bounds

Singular lattice form of [Hai14, Remark 3.15]: in the window layer setting `LayerSettingWNear`, the
lattice approximations of `f` against a test function are integrals of a continuous finite sum, and
the lattice reconstruction of `f` paired with a continuous compactly supported test function `ψ` is
`∫ R̃f ψ`, for models whose `Γ`-bounds hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}

/-- `S_n f ψ = ∫ latticeAvg n · ψ`, with a continuous finite-sum integrand. -/
theorem exists_continuous_eq_latticeApprox_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (n : ℕ) :
    ∃ F : ParabolicSpace → ℝ, Continuous F ∧ (∀ y, F y = latticeAvg 𝒯 g γ f n y * ψ y) ∧
      M.latticeApprox f ψ n = ∫ y, F y := by
  classical
  obtain ⟨R, hR⟩ := hψc.isCompact.exists_bound_of_continuousOn
    continuous_parabolicNorm.continuousOn
  have hsupp : ∀ w, R < parabolicNorm (w - 0) → ψ w = 0 := by
    intro w hw
    by_contra hne
    have := hR w (subset_tsupport _ hne)
    rw [Real.norm_eq_abs, abs_of_nonneg (parabolicNorm_nonneg _)] at this
    rw [sub_zero] at hw
    linarith
  obtain ⟨s, hs⟩ := exists_finset_support_mul_latticeCell hsupp n
  have hcont : ∀ k, Continuous (fun w => ψ w * latticeCell n k w) := fun k =>
    hψ.mul (contDiff_latticeCell n k).continuous
  have hcs : ∀ k, HasCompactSupport (fun w => ψ w * latticeCell n k w) := fun k =>
    hψc.mul_right
  have hG : ∀ k, Continuous (fun y => fnComb 𝒯 g γ (latticePoint n k) (f (latticePoint n k)) y) :=
    fun k => hg.continuous_fnComb _ _
  have hint : ∀ k, Integrable (fun y => fnComb 𝒯 g γ (latticePoint n k)
      (f (latticePoint n k)) y * (ψ y * latticeCell n k y)) := fun k =>
    ((hG k).mul (hcont k)).integrable_of_hasCompactSupport (hcs k).mul_left
  refine ⟨fun y => ∑ k ∈ s, fnComb 𝒯 g γ (latticePoint n k) (f (latticePoint n k)) y *
    (ψ y * latticeCell n k y), continuous_finsetSum _ fun k _ => (hG k).mul (hcont k),
    fun y => ?_, ?_⟩
  · by_cases hy : ψ y = 0
    · simp [hy]
    · unfold latticeAvg
      have hsub : ∀ k, latticeCell n k y * fnComb 𝒯 g γ (latticePoint n k)
          (f (latticePoint n k)) y ≠ 0 → k ∈ s := fun k hk =>
        hs k y (mul_ne_zero hy (left_ne_zero_of_mul hk))
      rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
  · rw [M.latticeApprox_eq_sum hs, integral_finsetSum _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact pairing_regPi_eq_integral hg (S.hfT _) (hcont k) (hcs k)

/-- **Remark 3.15, singular lattice form**: the lattice reconstruction of `f` paired with a
continuous compactly supported test function is `∫ R̃f ψ`. -/
theorem latticeRecon_eq_integral_wnear (hg : M.IsSmoothFunctionModelBelow g γ)
    (S : LayerSettingWNear M f γ η α Cf CPi CGam T) {ψ : ParabolicSpace → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    M.latticeRecon f ψ = ∫ y, pointwiseReconstruct g f y * ψ y := by
  choose F hFc hFe hFi using fun n => exists_continuous_eq_latticeApprox_wnear hg S hψ hψc n
  have hη : -2 < min η 0 :=
    lt_min (lt_of_lt_of_le S.hαη (min_le_right _ _)) (by norm_num)
  have hdom := integrable_abs_mul_identDom (M := M) (g := g) (γ := γ) (η := η) (Cf := Cf)
    (CGam := CGam) hg hη S.hCf hψ hψc
  have hlim : Tendsto (fun n => ∫ y, F (n + 1) y) atTop (𝓝 (∫ y, pointwiseReconstruct g f y * ψ y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => |ψ y| * identDom 𝒯 g γ η Cf CGam y)
      (fun n => (hFc (n + 1)).aestronglyMeasurable) hdom (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_)
    · rw [hFe, Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (abs_latticeAvg_le_wnear hg S (Nat.le_add_left 1 n) y) (abs_nonneg _)
    · simp only [hFe]
      exact ((tendsto_latticeAvg_wnear hg S y).comp (tendsto_add_atTop_nat 1)).mul_const _
  have hlim' : Tendsto (fun n => M.latticeApprox f ψ n) atTop
      (𝓝 (∫ y, pointwiseReconstruct g f y * ψ y)) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa [hFi] using hlim
  exact hlim'.limUnder_eq

end Model

end RegularityStructures
