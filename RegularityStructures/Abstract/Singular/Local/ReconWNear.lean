/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.SettingWNear
public import RegularityStructures.Abstract.Singular.Local.FirstLevelWNear
public import RegularityStructures.Abstract.Singular.Local.IncrementWNear
public import RegularityStructures.Abstract.ModelNear
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Singular.LatticeApprox.Defs
public import RegularityStructures.Abstract.Singular.Local.Series
public import RegularityStructures.Abstract.Singular.Window.Basic
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Convergence of the lattice approximations and the local bound, near-pair `Γ`-bounds

For `ψ = φ^λ_x` with `x` in the time slab, `64 λ ≤ w(x)` and `ψ` vanishing after time `T ≤ 1`, the
lattice approximations `S_n f ψ` converge and
`|⟨R f, ψ⟩ - ⟨Π_x f(x), ψ⟩| ≤ C (max 1 CGam * CPi) C_f λ^γ w(x)^{η-γ}`
(`exists_tendsto_and_abs_latticeRecon_sub_pairing_le_of_nonneg_win_near`). The model bounds are
assumed on `hairerTimeWindow`, together with a qualitative growth model, for models whose `Γ`-bounds
hold only for near pairs: `GammaNearOn`/`GammaDiffNearOn`
(`RegularityStructures.Abstract.ModelNear`) in place of `GammaBoundOn`/`GammaDiffBoundOn`.
-/

public section

open Set Filter

open scoped Topology

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Convergence and the local bound, assuming `0 ≤ C_f`. -/
theorem exists_tendsto_and_abs_latticeRecon_sub_pairing_le_of_nonneg_win_near
    (𝒯 : RegularityStructure ι) {γ : ℝ} (η : ℝ) (hγ : 0 < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Model 𝒯 parabolicSemigroup) {CPi CGam Cf : ℝ}
      {f : ParabolicSpace → ι → ℝ} {T : ℝ} {φ : ParabolicSpace → ℝ} {lam : ℝ}
      {x : ParabolicSpace},
      M.PiBoundOn γ CPi hairerTimeWindow → 0 ≤ CPi → M.GammaNearOn γ CGam hairerTimeWindow →
      (∃ (C' C'' : ℝ) (ρP ρG : ParabolicSpace → ℝ) (p q : ℝ), M.GrowthModel γ C' C'' ρP ρG p q) →
      T ≤ 1 →
      (∀ z, f z ∈ lowerSubspace 𝒯.deg γ) →
      M.SingularBoundOn timeZeroDist γ η Cf (timeSlab T) f → 0 ≤ Cf →
      φ ∈ testFunctionClass 4 → 0 < lam → lam ≤ 1 → x ∈ timeSlab T →
      64 * lam ≤ singularWeight timeZeroDist x →
      (∀ w : ParabolicSpace, T < w.1 → rescaledTestFunction φ lam x w = 0) →
      Tendsto (M.latticeApprox f (rescaledTestFunction φ lam x)) atTop
        (𝓝 (M.latticeRecon f (rescaledTestFunction φ lam x))) ∧
      |M.latticeRecon f (rescaledTestFunction φ lam x) -
          parabolicSemigroup.pairing (M.regPi x (f x)) (rescaledTestFunction φ lam x)| ≤
        C * (max 1 CGam * CPi) * Cf * lam ^ γ * singularWeight timeZeroDist x ^ (η - γ) := by
  obtain ⟨C0, hC00, hC0⟩ := exists_abs_latticeApprox_sub_pairing_le_of_nonneg_win_near 𝒯 η hdeg
  obtain ⟨C1, hC10, hC1⟩ := exists_abs_latticeApprox_succ_sub_le_of_nonneg_win_near 𝒯 η hdeg
  set r : ℝ := ((2 : ℝ)⁻¹) ^ γ with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hγ
  refine ⟨C0 + C1 / (1 - r), ?_, fun M CPi CGam Cf f T φ lam x hPi hCPi hGam hgrowth hT1 hfT hf hCf hφ hlam hl1
    hx hxw hφT => ?_⟩
  · have : 0 < 1 - r := by linarith
    positivity
  obtain ⟨n0, hn0, hn016⟩ := exists_level_eight_mul_inv_le hlam hl1
  set ψ := rescaledTestFunction φ lam x with hψ_def
  set w := singularWeight timeZeroDist x with hw_def
  set K0 := max 1 CGam * CPi with hK0
  have hK : 0 ≤ K0 := by positivity
  have hwx : 0 < w := by linarith
  have hq : 0 < ((2 : ℝ) ^ n0)⁻¹ := by positivity
  -- increments
  have hinc : ∀ j : ℕ, |M.latticeApprox f ψ (n0 + j + 1) - M.latticeApprox f ψ (n0 + j)| ≤
      (C1 * K0 * Cf * ((2 : ℝ) ^ n0)⁻¹ ^ γ * w ^ (η - γ)) * r ^ j := by
    intro j
    have hm : 8 * ((2 : ℝ) ^ (n0 + j))⁻¹ ≤ lam := by
      refine le_trans ?_ hn0
      have : ((2 : ℝ) ^ (n0 + j))⁻¹ ≤ ((2 : ℝ) ^ n0)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
      linarith
    refine (hC1 M hPi hCPi hGam hgrowth hT1 hfT hf hCf hφ hlam hl1 hx hxw hφT hm).trans (le_of_eq ?_)
    have e2 : ((2 : ℝ) ^ j)⁻¹ ^ γ = r ^ j := by
      rw [← inv_pow, hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    have e : ((2 : ℝ) ^ (n0 + j))⁻¹ ^ γ = ((2 : ℝ) ^ n0)⁻¹ ^ γ * r ^ j := by
      rw [pow_add, mul_inv, Real.mul_rpow (by positivity) (by positivity), e2]
    rw [e]; ring
  obtain ⟨L, hL, hLb⟩ := exists_tendsto_of_geometric_increments (M.latticeApprox f ψ) n0 hr0.le
    hr1 hinc
  have hrec : M.latticeRecon f ψ = L := hL.limUnder_eq
  refine ⟨hrec ▸ hL, ?_⟩
  rw [hrec]
  have hfirst := hC0 M hPi hCPi hGam hgrowth hT1 hfT hf hCf hφ hlam hl1 hx hxw hφT hn0 hn016
  have hq' : ((2 : ℝ) ^ n0)⁻¹ ^ γ ≤ lam ^ γ :=
    Real.rpow_le_rpow hq.le (by linarith) hγ.le
  have hwp : 0 ≤ w ^ (η - γ) := Real.rpow_nonneg hwx.le _
  have h1r : 0 < 1 - r := by linarith
  have hD : C1 * K0 * Cf * ((2 : ℝ) ^ n0)⁻¹ ^ γ * w ^ (η - γ) / (1 - r) ≤
      C1 / (1 - r) * K0 * Cf * lam ^ γ * w ^ (η - γ) := by
    rw [div_le_iff₀ h1r]
    have : C1 / (1 - r) * K0 * Cf * lam ^ γ * w ^ (η - γ) * (1 - r) =
        C1 * K0 * Cf * lam ^ γ * w ^ (η - γ) := by field_simp
    rw [this]
    have h0 : 0 ≤ C1 * K0 * Cf := by positivity
    calc C1 * K0 * Cf * ((2 : ℝ) ^ n0)⁻¹ ^ γ * w ^ (η - γ) =
          (C1 * K0 * Cf) * (((2 : ℝ) ^ n0)⁻¹ ^ γ * w ^ (η - γ)) := by ring
      _ ≤ (C1 * K0 * Cf) * (lam ^ γ * w ^ (η - γ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq' hwp) h0
      _ = _ := by ring
  have htri : |L - parabolicSemigroup.pairing (M.regPi x (f x)) ψ| ≤
      |L - M.latticeApprox f ψ n0| +
        |M.latticeApprox f ψ n0 - parabolicSemigroup.pairing (M.regPi x (f x)) ψ| := by
    have := abs_add_le (L - M.latticeApprox f ψ n0)
      (M.latticeApprox f ψ n0 - parabolicSemigroup.pairing (M.regPi x (f x)) ψ)
    simpa using this
  calc _ ≤ _ := htri
    _ ≤ (C1 * K0 * Cf * ((2 : ℝ) ^ n0)⁻¹ ^ γ * w ^ (η - γ)) / (1 - r) +
        C0 * K0 * Cf * lam ^ γ * w ^ (η - γ) := add_le_add hLb hfirst
    _ ≤ C1 / (1 - r) * K0 * Cf * lam ^ γ * w ^ (η - γ) +
        C0 * K0 * Cf * lam ^ γ * w ^ (η - γ) := by gcongr
    _ = _ := by ring

end RegularityStructures.Model

end
