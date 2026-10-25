/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.WrapG
public import RegularityStructures.Abstract.Singular.KGamma.WrapShell
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model

/-!
# The shell derivatives `D^k K_n(x - ·)` against the lattice reconstruction, weighted models

Weighted (`_growth`) versions of `RegularityStructures.Abstract.Singular.KGamma.WrapShell`, for a
`Model.GrowthModel` whose weights are bounded by `Rw` on `timeWindow8`; the constant
`max 1 CGam * CPi` becomes `max 1 CGam * CPi * Rw ^ 2`. Base points lie in the time slab `(0, T]`,
`T ≤ 8`, or (for the single-vector pairing bound) in `timeWindow8`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N : ℕ}

namespace Model

variable (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- `⟨Π_z τ, g⟩ = ∑_{deg i < γ} τ_i ⟨Π_z e_i, g⟩` for `g` scaled at `z` and `τ ∈ T_{<γ}`
(weighted models). -/
theorem pairing_regPi_eq_sum_of_scaled_growth (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) {g : ParabolicSpace → ℝ} {z : ParabolicSpace}
    {R A : ℝ} (hg : IsScaledTest g z R A) :
    parabolicSemigroup.pairing (M.regPi z τ) g = ∑ i ∈ Finset.univ.filter (fun i => 𝒯.deg i < γ),
      τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g := by
  set F := Finset.univ.filter (fun i => 𝒯.deg i < γ) with hF
  have h := tendsto_finsetSum (f := fun i s => τ i * ∫ y, M.regPi z (Pi.single i 1) s y * g y)
    (a := fun i => τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)
    F fun i hi =>
    (M.tendsto_abs_pairing_regPi_single_of_scaled_growth G hdeg
      (Finset.mem_filter.1 hi).2 hg).1.const_mul (τ i)
  have h' : Tendsto (fun s => ∫ y, M.regPi z τ s y * g y) (𝓝[>] 0)
      (𝓝 (∑ i ∈ F, τ i * parabolicSemigroup.pairing (M.regPi z (Pi.single i 1)) g)) := by
    refine h.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with s hs
    have e : (fun y => M.regPi z τ s y * g y) = fun y => ∑ i ∈ F,
        τ i * (M.regPi z (Pi.single i 1) s y * g y) := by
      funext y
      rw [M.regPi_eq_sum_filter hτ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum _ fun i hi =>
      (M.integrable_regPi_single_mul_of_scaled_growth G (Finset.mem_filter.1 hi).2 hg
        hs.1 hs.2).const_mul _]
    exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  exact tendsto_nhds_unique
    (M.tendsto_integral_regPi_mul_of_scaled_growth G hdeg hτ hg) h'

variable {h : ParabolicSpace → ℝ} (hh : ShellProfile h N)
  (hc : ∀ z : ParabolicSpace, z.1 ≤ 0 → h z = 0) (k : Fin 4 →₀ ℕ)

include hh hc in
/-- If the lattice approximations of the time-Taylor remainder `rem` converge, then
`⟨R f, D^k K_n(x − ·)⟩ = ⟨R f, rem⟩`: the subtracted terms are supported in `{y₀ < 0}`, where the
germ `f` vanishes, so their reconstruction is zero. -/
theorem latticeRecon_shell_eq_rem_growth (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam p qG : ℝ} {ρP ρG : ParabolicSpace → ℝ}
    (G : M.GrowthModel γ CPi CGam ρP ρG p qG)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {f : ParabolicSpace → ι → ℝ}
    (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) (hf0 : ∀ z : ParabolicSpace, z.1 ≤ 0 → f z = 0)
    (m n : ℕ) {x : ParabolicSpace} {R₁ L₁ : ℝ}
    (hs : ∀ w, R₁ < parabolicNorm (w - x) → shellTimeTaylorRem h k m n x w = 0)
    (t : Tendsto (M.latticeApprox f (shellTimeTaylorRem h k m n x)) atTop (𝓝 L₁)) :
    M.latticeRecon f (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) =
      M.latticeRecon f (shellTimeTaylorRem h k m n x) := by
  set Sx : ParabolicSpace → ℝ := fun y => ∑ j ∈ Finset.range m, (x.1 ^ j / (Nat.factorial j : ℝ)) *
    lineIter (multiDirs (k + Finsupp.single 0 j)) (scaledShell h n) ((0, x.2) - y) with hSx
  have hSxc : ∀ w : ParabolicSpace, 0 ≤ w.1 → Sx w = 0 := fun w hw =>
    Finset.sum_eq_zero fun j _ => by
      rw [lineIter_multiDirs_scaledShell_projection_eq_zero hh.contDiff hc _ n x.2 hw, mul_zero]
  have hSxcd : ContDiff ℝ ∞ Sx := by
    have h1 : ContDiff ℝ ∞ (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) :=
      (contDiff_lineIter (contDiff_scaledShell hh.contDiff n) _).comp
        (contDiff_const.sub contDiff_id)
    have h2 : ContDiff ℝ ∞ (shellTimeTaylorRem h k m n x) :=
      contDiff_shellTimeTaylorRem hh.contDiff k m n x
    have : Sx = fun y => lineIter (multiDirs k) (scaledShell h n) (x - y) -
        shellTimeTaylorRem h k m n x y := by
      funext y; simp [shellTimeTaylorRem, hSx]
    rw [this]; exact h1.sub h2
  have hSxs : ∀ w, ((2 : ℝ) ^ n)⁻¹ < parabolicNorm (w - ((0 : ℝ), x.2)) → Sx w = 0 := by
    intro w hw
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [lineIter_multiDirs_scaledShell_eq_zero_of_lt hh _ n (by rwa [parabolicNorm_sub_comm]),
      mul_zero]
  have ht2 : Tendsto (M.latticeApprox f Sx) atTop (𝓝 0) := by
    rw [show M.latticeApprox f Sx = fun _ => 0 from
      funext (M.latticeApprox_eq_zero_of_causal hSxc hf0)]
    exact tendsto_const_nhds
  have hsum := M.latticeRecon_add_growth hfT G hdeg
    (contDiff_shellTimeTaylorRem hh.contDiff k m n x) hSxcd hs hSxs t ht2
  have hGeq : (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y)) =
      shellTimeTaylorRem h k m n x + Sx := by
    funext y; simp [shellTimeTaylorRem, hSx]
  have hS0 : M.latticeRecon f Sx = 0 := M.latticeRecon_eq_zero_of_causal hSxc hf0
  rw [hGeq, hsum, hS0, add_zero]

end Model

end RegularityStructures

end
