/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.IdentNear.Coeff
public import RegularityStructures.Abstract.Singular.IdentNear.RemPairing
public import RegularityStructures.Abstract.Singular.IdentNear.ShellSum
public import RegularityStructures.Abstract.Integration.Realising.Def
public import RegularityStructures.Abstract.Singular.Theorem71.KernelPairG

/-!
# `𝒦_γ + R_γ` as convolution with the kernel, near-pair `Γ`-bounds

For a kernel pair `(h, r)`, a model realised by smooth functions, `f` a singular modelled
distribution and `x` a point of the time slab, the coefficient of the unit `X^0` of
`(𝒦_γ f + R_γ f)(x)` is the convolution `∫ H(x − y) R̃f(y) dy` of the kernel `H = ∑_n K_n + r` with
the pointwise reconstruction `R̃f(y) = (Π_y f(y))(y)`
(`kGammaRemG_apply_emb_zero_eq_integral_wnear`). The kernel identity `H = ∑_n K_n + r` away from `0`
is a hypothesis.

The statements are in the window layer setting `LayerSettingWNear`, whose `Γ`-bound `GammaNearOn`
(`RegularityStructures.Abstract.ModelNear`) holds only for near pairs, in place of `GammaBoundOn`.
-/

public section

open MeasureTheory Set Filter Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {g : ParabolicSpace → ι → ParabolicSpace → ℝ}
  {γ η α Cf CPi CGam T : ℝ} {f : ParabolicSpace → ι → ℝ}
  {h r : ParabolicSpace → ℝ} {N N' : ℕ}

/-- **Identification with the mild form**: the unit coefficient of `𝒦_γ f + R_γ f` at `x` is
`∫ H(x − y) R̃f(y) dy`, `H = ∑_n K_n + r`. -/
theorem kGammaRemG_apply_emb_zero_eq_integral_wnear (hK : KernelPair h r N) (hN : N' ≤ N)
    {P : PolynomialSector 𝒯 N'} (hM : M.IsPolyCompatible P) (I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hg : M.IsSmoothFunctionModelBelow g γ) (S : LayerSettingWNear M f γ η α Cf CPi CGam T)
    {x : ParabolicSpace} (hx : x ∈ timeSlab T) (kk : PolyIndex N') (hkk : kk.1 = 0)
    (hI0 : I (f x) (P.emb kk) = 0) {H : ParabolicSpace → ℝ}
    (hH : ∀ z, z ≠ 0 → H z = ∑' n, scaledShell h n z + r z) :
    M.kGammaRemG h r P I γ f x (P.emb kk) =
      ∫ y, H (x - y) * pointwiseReconstruct g f y := by
  classical
  rw [kGammaRemG_apply_emb_zero_wnear hK.shell hN hK.causal hM I S hx kk hkk hI0]
  set Φ : ParabolicSpace → ℝ := pointwiseReconstruct g f with hΦ
  have hψc : ∀ n, HasCompactSupport (fun y => scaledShell h n (x - y)) := fun n =>
    (hasCompactSupport_scaledShell hK.shell.eq_zero n).comp_homeomorph (Homeomorph.subLeft x)
  have hψ : ∀ n, Continuous (fun y => scaledShell h n (x - y)) := fun n =>
    (contDiff_scaledShell hK.shell.contDiff n).continuous.comp (continuous_const.sub continuous_id)
  have hrc : Continuous (fun y => r (x - y)) :=
    hK.rem.contDiff.continuous.comp (continuous_const.sub continuous_id)
  -- the family of integrands
  let F : ℕ → ParabolicSpace → ℝ := fun i y => match i with
    | 0 => Φ y * r (x - y)
    | n + 1 => Φ y * scaledShell h n (x - y)
  have hFint : ∀ i, Integrable (F i) := by
    intro i
    cases i with
    | zero => exact integrable_pointwiseReconstruct_mul_rem_wnear hg S hK.rem x
    | succ n => exact integrable_pointwiseReconstruct_mul_wnear hg S (hψ n) (hψc n)
  have hFsum : Summable fun i => ∫ y, ‖F i y‖ :=
    (summable_nat_add_iff 1).1
      (summable_integral_norm_pointwiseReconstruct_mul_shell_wnear hg S hK.shell hx.1)
  have hHS := hasSum_integral_of_summable_integral_norm hFint hFsum
  have h1 : ∑' i, ∫ y, F i y = ∫ y, ∑' i, F i y := hHS.tsum_eq
  have h2 : ∑' i, ∫ y, F i y = (∫ y, F 0 y) + ∑' n, ∫ y, F (n + 1) y :=
    hHS.summable.tsum_eq_zero_add
  have hlr : ∀ n, M.latticeRecon f (fun y => scaledShell h n (x - y)) = ∫ y, F (n + 1) y :=
    fun n => latticeRecon_eq_integral_wnear hg S (hψ n) (hψc n)
  have hrem : M.remPairing f (fun y => r (x - y)) = ∫ y, F 0 y :=
    remPairing_eq_integral_wnear hg S hrc (integrable_pointwiseReconstruct_mul_rem_wnear hg S hK.rem x)
  have hpt : ∀ y, y ≠ x → ∑' i, F i y = H (x - y) * Φ y := by
    intro y hyx
    have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyx)
    have hsy : Summable (fun n => scaledShell h n (x - y)) :=
      summable_scaledShell_of_causal hK.shell.eq_zero hK.causal (x - y)
    have hs : Summable (fun i => F i y) :=
      (summable_nat_add_iff 1).1 (hsy.mul_left (Φ y))
    rw [hs.tsum_eq_zero_add]
    show Φ y * r (x - y) + ∑' n, Φ y * scaledShell h n (x - y) = _
    rw [tsum_mul_left, hH (x - y) hz]
    ring
  rw [tsum_congr hlr, hrem, add_comm, ← h2, h1]
  have hna : NullSingletonClass (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]; infer_instance
  exact integral_congr_ae ((Set.countable_singleton x).ae_notMem _ |>.mono fun y hy =>
    hpt y (by simpa using hy))

end Model

end RegularityStructures
