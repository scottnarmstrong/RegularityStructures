/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.LatticeApprox.Pieces
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Linearity of the lattice reconstruction in the test function (weighted model)

Weighted version: only convergence of the model pairings is used, so the
global bounds are replaced by a `Model.GrowthModel`.

For smooth test functions vanishing outside parabolic balls, `ψ ↦ S_n f ψ` is additive and
homogeneous for `n ≥ 3`; hence so is `ψ ↦ ⟨R f, ψ⟩` whenever the lattice approximations converge.
-/

public section

open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- Additivity of the lattice approximation over a finite family of smooth test functions, each
vanishing outside some parabolic ball. -/
theorem latticeApprox_finset_sum_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {κ : Type*} (S : Finset κ)
    (ψ : κ → ParabolicSpace → ℝ) (x : κ → ParabolicSpace) (R : κ → ℝ)
    (hψ : ∀ j ∈ S, ContDiff ℝ ∞ (ψ j))
    (hsupp : ∀ j ∈ S, ∀ w, R j < parabolicNorm (w - x j) → ψ j w = 0) {n : ℕ} (hn : 3 ≤ n) :
    M.latticeApprox f (∑ j ∈ S, ψ j) n = ∑ j ∈ S, M.latticeApprox f (ψ j) n := by
  classical
  have hs : ∀ j, ∃ s : Finset LatticeIndex, j ∈ S →
      ∀ k w, ψ j w * latticeCell n k w ≠ 0 → k ∈ s := fun j => by
    by_cases hj : j ∈ S
    · obtain ⟨s, hs⟩ := exists_finset_support_mul_latticeCell (hsupp j hj) n
      exact ⟨s, fun _ => hs⟩
    · exact ⟨∅, fun h => absurd h hj⟩
  choose s hs using hs
  set T : Finset LatticeIndex := S.biUnion s with hT
  have hT' : ∀ j ∈ S, ∀ k w, ψ j w * latticeCell n k w ≠ 0 → k ∈ T := fun j hj k w h =>
    Finset.mem_biUnion.2 ⟨j, hj, hs j hj k w h⟩
  have hTsum : ∀ k w, (∑ j ∈ S, ψ j) w * latticeCell n k w ≠ 0 → k ∈ T := fun k w h => by
    rw [Finset.sum_apply] at h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    exact hT' j hj k w (mul_ne_zero hne h2)
  rw [M.latticeApprox_eq_sum hTsum, Finset.sum_congr rfl fun j hj =>
    M.latticeApprox_eq_sum (hT' j hj), Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hA : ∀ j, ∃ A, j ∈ S → IsScaledTest (fun w => ψ j w * latticeCell n k w)
      (latticePoint n k) (8 * ((2 : ℝ) ^ n)⁻¹) A := fun j => by
    by_cases hj : j ∈ S
    · obtain ⟨A, hA⟩ := exists_isScaledTest_of_latticeCell
        ((hψ j hj).mul (contDiff_latticeCell n k)) hn fun w h => right_ne_zero_of_mul h
      exact ⟨A, fun _ => hA⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose A hA using hA
  have e : (fun w => (∑ j ∈ S, ψ j) w * latticeCell n k w) =
      ∑ j ∈ S, fun w => ψ j w * latticeCell n k w := by
    funext w
    simp only [Finset.sum_apply, Finset.sum_mul]
  rw [e]
  exact M.pairing_regPi_finset_sum_of_scaled_growth G hdeg (hf _)
    (fun j w => ψ j w * latticeCell n k w) S (fun _ => 8 * ((2 : ℝ) ^ n)⁻¹) A hA

/-- Additivity of the lattice approximation (two smooth test functions, each vanishing outside a
parabolic ball). -/
theorem latticeApprox_add_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ₁ ψ₂ : ParabolicSpace → ℝ}
    {x₁ x₂ : ParabolicSpace} {R₁ R₂ : ℝ} (h₁ : ContDiff ℝ ∞ ψ₁) (h₂ : ContDiff ℝ ∞ ψ₂)
    (s₁ : ∀ w, R₁ < parabolicNorm (w - x₁) → ψ₁ w = 0)
    (s₂ : ∀ w, R₂ < parabolicNorm (w - x₂) → ψ₂ w = 0) {n : ℕ} (hn : 3 ≤ n) :
    M.latticeApprox f (ψ₁ + ψ₂) n = M.latticeApprox f ψ₁ n + M.latticeApprox f ψ₂ n := by
  have := M.latticeApprox_finset_sum_growth hf G hdeg (Finset.univ : Finset Bool)
    (fun b => bif b then ψ₁ else ψ₂) (fun b => bif b then x₁ else x₂)
    (fun b => bif b then R₁ else R₂)
    (fun b _ => by cases b <;> assumption) (fun b _ => by cases b <;> assumption) hn
  simpa [Fintype.sum_bool, add_comm] using this

/-- Homogeneity of the lattice approximation. -/
theorem latticeApprox_smul_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (c : ℝ) {n : ℕ} (hn : 3 ≤ n) :
    M.latticeApprox f (c • ψ) n = c * M.latticeApprox f ψ n := by
  obtain ⟨s, hs'⟩ := exists_finset_support_mul_latticeCell hs n
  have hs'' : ∀ k w, (c • ψ) w * latticeCell n k w ≠ 0 → k ∈ s := fun k w h =>
    hs' k w (by
      intro h0
      apply h
      have e : (c • ψ) w * latticeCell n k w = c * (ψ w * latticeCell n k w) := by
        simp [mul_assoc]
      rw [e, h0, mul_zero])
  rw [M.latticeApprox_eq_sum hs'', M.latticeApprox_eq_sum hs', Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨A, hA⟩ := exists_isScaledTest_of_latticeCell
    (hψ.mul (contDiff_latticeCell n k)) hn fun w h => right_ne_zero_of_mul h
  have e : (fun w => (c • ψ) w * latticeCell n k w) =
      c • fun w => ψ w * latticeCell n k w := by
    funext w; simp [mul_assoc]
  have ht := M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg (hf (latticePoint n k)) hA
  rw [e]
  refine parabolicSemigroup.pairing_eq_of_tendsto ((ht.const_mul c).congr fun t => ?_)
    |>.trans ?_
  · rw [← integral_const_mul]
    congr 1; funext y
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rw [parabolicSemigroup.pairing_eq_of_tendsto ht]

/-- Convergence is preserved by finite sums. -/
theorem tendsto_latticeApprox_finset_sum_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {κ : Type*} (S : Finset κ)
    (ψ : κ → ParabolicSpace → ℝ) (x : κ → ParabolicSpace) (R : κ → ℝ)
    (hψ : ∀ j ∈ S, ContDiff ℝ ∞ (ψ j))
    (hsupp : ∀ j ∈ S, ∀ w, R j < parabolicNorm (w - x j) → ψ j w = 0) (L : κ → ℝ)
    (hL : ∀ j ∈ S, Tendsto (M.latticeApprox f (ψ j)) atTop (𝓝 (L j))) :
    Tendsto (M.latticeApprox f (∑ j ∈ S, ψ j)) atTop (𝓝 (∑ j ∈ S, L j)) := by
  refine (tendsto_finsetSum S hL).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (M.latticeApprox_finset_sum_growth hf G hdeg S ψ x R hψ hsupp hn).symm

/-- `⟨R f, ∑ ψ_j⟩ = ∑ ⟨R f, ψ_j⟩`. -/
theorem latticeRecon_finset_sum_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {κ : Type*} (S : Finset κ)
    (ψ : κ → ParabolicSpace → ℝ) (x : κ → ParabolicSpace) (R : κ → ℝ)
    (hψ : ∀ j ∈ S, ContDiff ℝ ∞ (ψ j))
    (hsupp : ∀ j ∈ S, ∀ w, R j < parabolicNorm (w - x j) → ψ j w = 0) (L : κ → ℝ)
    (hL : ∀ j ∈ S, Tendsto (M.latticeApprox f (ψ j)) atTop (𝓝 (L j))) :
    M.latticeRecon f (∑ j ∈ S, ψ j) = ∑ j ∈ S, M.latticeRecon f (ψ j) := by
  unfold latticeRecon
  rw [Finset.sum_congr rfl fun j hj => (hL j hj).limUnder_eq]
  exact (M.tendsto_latticeApprox_finset_sum_growth hf G hdeg S ψ x R hψ hsupp L hL).limUnder_eq

/-- Additivity of the reconstruction. -/
theorem tendsto_latticeApprox_add_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ₁ ψ₂ : ParabolicSpace → ℝ}
    {x₁ x₂ : ParabolicSpace} {R₁ R₂ L₁ L₂ : ℝ} (h₁ : ContDiff ℝ ∞ ψ₁) (h₂ : ContDiff ℝ ∞ ψ₂)
    (s₁ : ∀ w, R₁ < parabolicNorm (w - x₁) → ψ₁ w = 0)
    (s₂ : ∀ w, R₂ < parabolicNorm (w - x₂) → ψ₂ w = 0)
    (t₁ : Tendsto (M.latticeApprox f ψ₁) atTop (𝓝 L₁))
    (t₂ : Tendsto (M.latticeApprox f ψ₂) atTop (𝓝 L₂)) :
    Tendsto (M.latticeApprox f (ψ₁ + ψ₂)) atTop (𝓝 (L₁ + L₂)) := by
  refine (t₁.add t₂).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (M.latticeApprox_add_growth hf G hdeg h₁ h₂ s₁ s₂ hn).symm

theorem latticeRecon_add_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ₁ ψ₂ : ParabolicSpace → ℝ}
    {x₁ x₂ : ParabolicSpace} {R₁ R₂ L₁ L₂ : ℝ} (h₁ : ContDiff ℝ ∞ ψ₁) (h₂ : ContDiff ℝ ∞ ψ₂)
    (s₁ : ∀ w, R₁ < parabolicNorm (w - x₁) → ψ₁ w = 0)
    (s₂ : ∀ w, R₂ < parabolicNorm (w - x₂) → ψ₂ w = 0)
    (t₁ : Tendsto (M.latticeApprox f ψ₁) atTop (𝓝 L₁))
    (t₂ : Tendsto (M.latticeApprox f ψ₂) atTop (𝓝 L₂)) :
    M.latticeRecon f (ψ₁ + ψ₂) = M.latticeRecon f ψ₁ + M.latticeRecon f ψ₂ := by
  unfold latticeRecon
  rw [t₁.limUnder_eq, t₂.limUnder_eq]
  exact (M.tendsto_latticeApprox_add_growth hf G hdeg h₁ h₂ s₁ s₂ t₁ t₂).limUnder_eq

theorem tendsto_latticeApprox_smul_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R L : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (c : ℝ)
    (t : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L)) :
    Tendsto (M.latticeApprox f (c • ψ)) atTop (𝓝 (c * L)) := by
  refine (t.const_mul c).congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (M.latticeApprox_smul_growth hf G hdeg hψ hs c hn).symm

theorem latticeRecon_smul_growth {f : ParabolicSpace → ι → ℝ}
    (hf : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ)
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {ψ : ParabolicSpace → ℝ}
    {x : ParabolicSpace} {R L : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ w, R < parabolicNorm (w - x) → ψ w = 0) (c : ℝ)
    (t : Tendsto (M.latticeApprox f ψ) atTop (𝓝 L)) :
    M.latticeRecon f (c • ψ) = c * M.latticeRecon f ψ := by
  unfold latticeRecon
  rw [t.limUnder_eq]
  exact (M.tendsto_latticeApprox_smul_growth hf G hdeg hψ hs c t).limUnder_eq

end RegularityStructures.Model

end
