/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Local.ReconWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.LatticeApprox.Defs
public import RegularityStructures.Abstract.Singular.Local.Main
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Local bound for the reconstruction, near-pair `Γ`-bounds

[Hai14, Prop. 7.2 and (6.6)]: for `x` in the slab with `64 λ ≤ w_x`, the lattice approximations of
`f` against `φ^λ_x` converge to `⟨R f, φ^λ_x⟩`, and
`|⟨R f − Π_x f(x), φ^λ_x⟩| ≤ C K₀ C_f λ^γ w_x^{η−γ}`, for models whose `Γ`-bounds hold only for near
pairs: `GammaNearOn`/`GammaDiffNearOn` (`RegularityStructures.Abstract.ModelNear`) in place of
`GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

open scoped Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ : ℝ}

/-- Hairer (arXiv:1303.5113v4), Prop. 7.2 and (6.6): the local bound for `⟨R f, ψ⟩` and the
convergence of the lattice approximations. -/
theorem exists_tendsto_and_abs_latticeRecon_sub_pairing_le_win_near (𝒯 : RegularityStructure ι) {γ : ℝ}
    (η : ℝ) (hγ : 0 < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ} {T : ℝ} {φ : ParabolicSpace → ℝ} {lam : ℝ}
      {x : ParabolicSpace},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi → M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 →
      (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f →
      φ ∈ testFunctionClass 4 → 0 < lam → lam ≤ 1 → x ∈ timeSlab T →
      64 * lam ≤ singularWeight timeZeroDist x →
      (∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ lam x w = 0) →
      Tendsto (M.latticeApprox f (rescaledTestFunction φ lam x)) atTop
        (𝓝 (M.latticeRecon f (rescaledTestFunction φ lam x))) ∧
      |M.latticeRecon f (rescaledTestFunction φ lam x) -
          parabolicSemigroup.pairing (M.regPi x (f x)) (rescaledTestFunction φ lam x)| ≤
        C * (max 1 CGam * CPi) * Cf * lam ^ γ * singularWeight timeZeroDist x ^ (η - γ) := by
  by_cases hex : ∃ i, 𝒯.deg i < γ
  · obtain ⟨C, hC0, hC⟩ :=
      exists_tendsto_and_abs_latticeRecon_sub_pairing_le_of_nonneg_win_near 𝒯 η hγ hdeg
    obtain ⟨i, hi⟩ := hex
    exact ⟨C, hC0, fun M CPi CGam Cf f T φ lam x hPi hCPi hGam hgrowth hT1 hfT hf hφ hlam hl1 hx hxw hφT =>
      hC M hPi hCPi hGam hgrowth hT1 hfT hf (Model.SingularBoundOn.nonneg M hf hx (timeZeroDist_pos_of_mem_timeSlab hx) hi) hφ hlam
        hl1 hx hxw hφT⟩
  · refine ⟨0, le_rfl, fun M CPi CGam Cf f T φ lam x hPi hCPi hGam hgrowth hT1 hfT hf hφ hlam hl1 hx hxw hφT => ⟨?_, ?_⟩⟩
    · rw [latticeRecon_eq_zero_of_no_index M hex hfT,
        show M.latticeApprox f (rescaledTestFunction φ lam x) = fun _ => 0 from
          funext (latticeApprox_eq_zero_of_no_index M hex hfT _)]
      exact tendsto_const_nhds
    · rw [latticeRecon_eq_zero_of_no_index M hex hfT, eq_zero_of_no_index hex hfT x,
        pairing_regPi_zero]
      simp

end RegularityStructures.Model

end
