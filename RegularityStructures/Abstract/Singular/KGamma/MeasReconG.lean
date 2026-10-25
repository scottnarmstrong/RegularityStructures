/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.MeasPairing
public import RegularityStructures.Abstract.Singular.Kernel.LinearG
public import RegularityStructures.Abstract.Singular.ModelPairingGrowth
public import RegularityStructures.Abstract.Singular.Kernel.Shell
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model

/-!
# Measurability of `x ↦ ⟨R f, D^k K_n(x − ·)⟩` on the time slab, weighted models

Weighted (`_growth`) version: the convergence of the lattice approximations
uses the weighted layer bound (`exists_tendsto_latticeApprox_abs_latticeRecon_le_growth`).

For a smooth `G` vanishing outside a ball, `x ↦ S_m f (G(x − ·))` is measurable for `m ≥ 3`
(`measurable_latticeApprox_translate_growth`): it is a locally finite sum over lattice cells of pairings
`⟨Π_{z_{m,k}} f(z_{m,k}), G(x − ·) χ_{m,k}⟩`, each a limit along `s = 1/(j+1)` of integrals which
are measurable in `x` by Fubini. On `{x₀ ≤ T}` the lattice approximations of the shell derivatives
converge to `latticeRecon` (layer bound, `exists_tendsto_latticeApprox_abs_latticeRecon_le_growth`, plus
causality), so `x ↦ latticeRecon f (D^k K_n(x − ·))` is measurable on any measurable subset of
`{x₀ ≤ T}` (`measurable_indicator_latticeRecon_lineIter_growth`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam p qG Rw : ℝ} {ρP ρG : ParabolicSpace → ℝ}

/-- Each cell pairing `x ↦ ⟨Π_z τ, G(x − ·) χ_{m,k}⟩` is measurable (`m ≥ 3`). -/
theorem measurable_pairing_translate_mul_latticeCell_growth (Gm : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ)
    {G : ParabolicSpace → ℝ} (hG : ContDiff ℝ ∞ G) {m : ℕ} (hm : 3 ≤ m)
    (k : LatticeIndex) :
    Measurable fun x => parabolicSemigroup.pairing (M.regPi (latticePoint m k) τ)
      (fun w => G (x - w) * latticeCell m k w) := by
  have hF : ∀ j : ℕ, Measurable fun x => ∫ y, M.regPi (latticePoint m k) τ (1 / ((j : ℝ) + 1)) y *
      (G (x - y) * latticeCell m k y) := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hm' : Measurable fun p : ParabolicSpace × ParabolicSpace =>
        M.regPi (latticePoint m k) τ (1 / ((j : ℝ) + 1)) p.2 * (G (p.1 - p.2) * latticeCell m k p.2) :=
      ((M.measurable_regPi (latticePoint m k) τ hpos).comp measurable_snd).mul
        ((hG.continuous.comp (continuous_fst.sub continuous_snd)).mul
          ((contDiff_latticeCell m k).continuous.comp continuous_snd)).measurable
    exact (hm'.stronglyMeasurable.integral_prod_right (ν := volume)).measurable
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun x => ?_)
  obtain ⟨A, hA⟩ := exists_isScaledTest_of_latticeCell
    (g := fun w => G (x - w) * latticeCell m k w)
    ((hG.comp (contDiff_const.sub contDiff_id)).mul (contDiff_latticeCell m k)) hm
    fun w h => right_ne_zero_of_mul h
  have key := M.tendsto_integral_regPi_mul_of_scaled_growth Gm hdeg hτ hA
  have hseq : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun j => by
        show (0 : ℝ) < 1 / ((j : ℝ) + 1)
        positivity⟩
  exact key.comp hseq

/-- `x ↦ S_m f (G(x − ·))` is measurable for `m ≥ 3`, `G` smooth vanishing outside `B(0, R)`. -/
theorem measurable_latticeApprox_translate_growth (Gm : M.GrowthModel γ CPi CGam ρP ρG p qG) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {f : ParabolicSpace → ι → ℝ}
    (hfT : ∀ z, f z ∈ lowerSubspace 𝒯.deg γ) {G : ParabolicSpace → ℝ} (hG : ContDiff ℝ ∞ G)
    {R : ℝ} (hGR : ∀ v, R < parabolicNorm v → G v = 0) {m : ℕ} (hm : 3 ≤ m) :
    Measurable fun x => M.latticeApprox f (fun y => G (x - y)) m := by
  classical
  set T : LatticeIndex → ParabolicSpace → ℝ := fun k x => parabolicSemigroup.pairing
    (M.regPi (latticePoint m k) (f (latticePoint m k))) (fun w => G (x - w) * latticeCell m k w)
    with hT
  have hTm : ∀ k, Measurable (T k) := fun k =>
    M.measurable_pairing_translate_mul_latticeCell_growth Gm hdeg (hfT _) hG hm k
  have hfin : ∀ x, (Function.support fun k => T k x).Finite := fun x => by
    obtain ⟨s, hs⟩ := exists_finset_support_mul_latticeCell (ψ := fun y => G (x - y)) (x := x)
      (R := R) (fun w hw => hGR _ (by rwa [parabolicNorm_sub_comm] at hw)) m
    refine s.finite_toSet.subset fun k hk => ?_
    by_contra hks
    refine hk ?_
    have : (fun w => G (x - w) * latticeCell m k w) = fun _ => 0 := by
      funext w
      by_contra h
      exact hks (hs k w h)
    simp only [hT, this]
    exact pairing_zero_test _ _
  obtain ⟨e⟩ := nonempty_denumerable LatticeIndex
  have hval : ∀ x, M.latticeApprox f (fun y => G (x - y)) m = ∑' j : ℕ, T (e.eqv.symm j) x :=
    fun x => by
      rw [Equiv.tsum_eq e.eqv.symm (fun k => T k x), tsum_eq_finsum (hfin x)]
      rfl
  have e' : (fun x => M.latticeApprox f (fun y => G (x - y)) m) = fun x =>
      ∑' j : ℕ, T (e.eqv.symm j) x := funext hval
  rw [e']
  exact measurable_tsum_of_summable (fun j => hTm _) fun x =>
    (e.eqv.symm.summable_iff (f := fun k => T k x)).2 (summable_of_hasFiniteSupport (hfin x))

end Model

end RegularityStructures

end
