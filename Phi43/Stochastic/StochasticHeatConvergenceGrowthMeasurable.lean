/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.Properties
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import Phi43.Stochastic.StochasticHeatConvergenceGrowth
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import RegularityStructures.PDE.TorusLift
import Mathlib.Topology.Algebra.Order.Field

/-!
# Measurability of derivative growth for smooth random sections

The measurable-event part of the convergence of the noise potentials (`phi43Noise_cauchy`) is
obtained from joint measurability of the forcing and smoothness of every sample section.  The
derivative evaluations are measurable limits of secant quotients.  The final growth event is then a
countable intersection over derivative order and a countable dense set of lifted space-time points.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ContDiff

namespace RegularityStructures.Phi43

private theorem measurableSet_forall_le_continuous
    {Ω A : Type*} [MeasurableSpace Ω] [TopologicalSpace A] [SeparableSpace A]
    {f : Ω → A → ℝ} {g : A → ℝ}
    (hm : ∀ a, Measurable (fun w => f w a))
    (hf : ∀ w, Continuous (f w)) (hg : Continuous g) :
    MeasurableSet {w | ∀ a, f w a ≤ g a} := by
  have hm' : Measurable (fun w => ⨆ a, ENNReal.ofReal (f w a - g a)) := by
    have h : Measurable (⨆ a, fun w => ENNReal.ofReal (f w a - g a)) :=
      measurable_iSup_of_lowerSemicontinuous
        (f := fun a w => ENNReal.ofReal (f w a - g a))
        (fun a => ((hm a).sub measurable_const).ennreal_ofReal)
        (fun w => (ENNReal.continuous_ofReal.comp ((hf w).sub hg)).lowerSemicontinuous)
    have he : (⨆ a, fun w => ENNReal.ofReal (f w a - g a)) =
        (fun w => ⨆ a, ENNReal.ofReal (f w a - g a)) := by
      funext w
      exact iSup_apply
    exact he ▸ h
  have he : {w | ∀ a, f w a ≤ g a} =
      {w | (⨆ a, ENNReal.ofReal (f w a - g a)) ≤ 0} := by
    ext w
    change (∀ a, f w a ≤ g a) ↔ (⨆ a, ENNReal.ofReal (f w a - g a)) ≤ 0
    rw [iSup_le_iff]
    simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, sub_nonpos]
  rw [he]
  exact measurableSet_le hm' measurable_const

private theorem measurable_fderiv_apply_of_joint
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableAdd₂ E]
    {f : Ω → E → ℝ}
    (hm : Measurable (fun p : Ω × E => f p.1 p.2))
    (hs : ∀ w : Ω, ContDiff ℝ ∞ (f w)) (v : E) :
    Measurable (fun p : Ω × E => fderiv ℝ (f p.1) p.2 v) := by
  let secant (n : ℕ) (p : Ω × E) : ℝ :=
    slope (fun t : ℝ => f p.1 (p.2 + t • v)) 0 ((n : ℝ) + 1)⁻¹
  have hpoint : Measurable (fun p : Ω × E => f p.1 p.2) := hm
  have hshift (n : ℕ) : Measurable (fun p : Ω × E =>
      f p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • v)) := by
    have hmap : Measurable (fun p : Ω × E =>
        (p.1, p.2 + ((n : ℝ) + 1)⁻¹ • v)) := by
      exact measurable_fst.prodMk
        (measurable_snd.add (measurable_const.smul measurable_const))
    have hcomp := hm.comp hmap
    change Measurable (fun p : Ω × E =>
      f p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • v)) at hcomp
    exact hcomp
  have hsec (n : ℕ) : Measurable (secant n) := by
    have hmul := (hshift n).sub hpoint |>.mul
      (measurable_const : Measurable (fun _ : Ω × E => (n : ℝ) + 1))
    change Measurable (fun p : Ω × E =>
      (f p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • v) - f p.1 p.2) *
        ((n : ℝ) + 1)) at hmul
    simpa [secant, slope_def_field, div_eq_mul_inv] using hmul
  apply measurable_of_tendsto_metrizable (fun n => hsec n)
  apply tendsto_pi_nhds.mpr
  intro p
  have hline : HasDerivAt (fun t : ℝ => f p.1 (p.2 + t • v))
      (fderiv ℝ (f p.1) p.2 v) 0 := by
    have hpath : HasDerivAt (fun t : ℝ => p.2 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.2
    have hcomp :=
      ((hs p.1).contDiffAt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
        0 hpath
    simpa only [Function.comp_def, zero_smul, add_zero] using hcomp
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_inv_atTop_nhdsGT_zero.comp
    exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hne : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) := by
    apply nhdsWithin_mono
    intro x hx
    exact ne_of_gt hx
  have hslope := hline.tendsto_slope.mono_left hne
  change Tendsto (fun n : ℕ =>
    slope (fun t : ℝ => f p.1 (p.2 + t • v)) 0 ((n : ℝ) + 1)⁻¹)
      atTop (𝓝 ((fderiv ℝ (f p.1) p.2) v))
  simpa only [Function.comp_def] using hslope.comp ht

private theorem measurable_iteratedFDeriv_apply_of_joint
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableAdd₂ E]
    {f : Ω → E → ℝ}
    (hm : Measurable (fun p : Ω × E => f p.1 p.2))
    (hs : ∀ w : Ω, ContDiff ℝ ∞ (f w))
    (k : ℕ) (v : Fin k → E) :
    Measurable (fun p : Ω × E =>
      iteratedFDeriv ℝ k (f p.1) p.2 v) := by
  induction k with
  | zero =>
      simpa only [iteratedFDeriv_zero_apply] using hm
  | succ k ih =>
      let vtail : Fin k → E := Fin.tail v
      let g : Ω → E → ℝ := fun w y =>
        iteratedFDeriv ℝ k (f w) y (vtail)
      have hgm : Measurable (fun p : Ω × E => g p.1 p.2) := by
        simpa only [g, vtail] using ih (v := vtail)
      have hgs : ∀ w : Ω, ContDiff ℝ ∞ (g w) := by
        intro w
        have hc : ContDiff ℝ ∞ (iteratedFDeriv ℝ k (f w)) :=
          (hs w).iteratedFDeriv_right'
        exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ vtail).contDiff.comp hc
      have hd := measurable_fderiv_apply_of_joint hgm hgs (v 0)
      have heq : (fun p : Ω × E => fderiv ℝ (g p.1) p.2 (v 0)) =
          (fun p : Ω × E => iteratedFDeriv ℝ (k + 1) (f p.1) p.2 v) := by
        funext p
        rw [iteratedFDeriv_succ_apply_left]
        symm
        have hc : ContDiff ℝ ∞ (iteratedFDeriv ℝ k (f p.1)) :=
          (hs p.1).iteratedFDeriv_right'
        have hdiff : DifferentiableAt ℝ
            (iteratedFDeriv ℝ k (f p.1)) p.2 :=
          (hs p.1).contDiffAt.differentiableAt_iteratedFDeriv (by
            have hlt : (k : ℕ∞ω) < (k.succ : ℕ∞ω) := Nat.cast_lt.2 k.lt_succ_self
            have hle : (k.succ : ℕ∞ω) ≤ ∞ :=
              WithTop.coe_le_coe.mpr le_top
            exact hlt.trans_le hle)
        simpa only [g, vtail] using
          (fderiv_continuousMultilinear_apply_const_apply hdiff vtail (v 0)).symm
      rw [← heq]
      exact hd

theorem regularisedNoise_hasPhi43NoiseGrowth_measurable_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) 1)
    (ξ : Ω → SpaceTime → ℝ)
    (hξ : IsRegularisedNoise P W ρ ε ξ) :
    MeasurableSet {w | Statements.HasPhi43NoiseGrowth (ξ w)} ∧
      ∀ᵐ w ∂P, Statements.HasPhi43NoiseGrowth (ξ w) := by
  let f : Ω → ParabolicSpace → ℝ := fun w z => ξ w (z.1, torusProj z.2)
  have hjoint : Measurable (fun p : Ω × ParabolicSpace => f p.1 p.2) := by
    have hmap : Measurable (fun p : Ω × ParabolicSpace =>
        (p.1, (p.2.1, torusProj p.2.2))) := by
      exact measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          ((PDE.continuous_torusProj : Continuous torusProj).measurable.comp
            (measurable_snd.comp measurable_snd)))
    have hξjoint := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
    have hcomp := hξjoint.comp hmap
    change Measurable (fun p : Ω × ParabolicSpace => f p.1 p.2) at hcomp
    exact hcomp
  have hsmooth : ∀ w, ContDiff ℝ ∞ (f w) := by
    intro w
    exact hξ.1 w
  have hscalar (k : ℕ) (v : Fin k → ParabolicSpace) (z : ParabolicSpace) :
      Measurable (fun w : Ω =>
        ‖iteratedFDeriv ℝ k (f w) z v‖) := by
    have h := measurable_iteratedFDeriv_apply_of_joint hjoint hsmooth k v
    have hmap : Measurable (fun w : Ω => (w, z)) :=
      measurable_id.prodMk measurable_const
    have h' := h.comp hmap
    exact measurable_norm.comp h'
  have hcontinuous (k : ℕ) (w : Ω) :
      Continuous (fun a : ParabolicSpace × (Fin k → ParabolicSpace) =>
        ‖iteratedFDeriv ℝ k (f w) a.1 a.2‖) := by
    have hderiv : Continuous (fun z : ParabolicSpace =>
        iteratedFDeriv ℝ k (f w) z) :=
      (hsmooth w).continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have heval : Continuous (fun p :
        (ContinuousMultilinearMap ℝ (fun _ : Fin k => ParabolicSpace) ℝ) ×
          (Fin k → ParabolicSpace) => p.1 p.2) := continuous_eval
    have happly : Continuous (fun a : ParabolicSpace × (Fin k → ParabolicSpace) =>
        iteratedFDeriv ℝ k (f w) a.1 a.2) := by
      exact heval.comp (hderiv.comp continuous_fst |>.prodMk continuous_snd)
    exact continuous_norm.comp happly
  have hineq (n q : ℕ) (k : Fin 5) : MeasurableSet
      {w | ∀ a : ParabolicSpace × (Fin k → ParabolicSpace),
        ‖iteratedFDeriv ℝ k.1 (f w) a.1 a.2‖ ≤
          (n : ℝ) * (1 + parabolicNorm a.1) ^ q * ∏ i, ‖a.2 i‖} := by
    let A := ParabolicSpace × (Fin k.1 → ParabolicSpace)
    have hm : ∀ a : A, Measurable (fun w : Ω =>
        ‖iteratedFDeriv ℝ k.1 (f w) a.1 a.2‖) := by
      intro a
      exact hscalar k.1 a.2 a.1
    have hf : ∀ w, Continuous (fun a : A =>
        ‖iteratedFDeriv ℝ k.1 (f w) a.1 a.2‖) := by
      intro w
      exact hcontinuous k.1 w
    have hg : Continuous (fun a : A =>
        (n : ℝ) * (1 + parabolicNorm a.1) ^ q * ∏ i, ‖a.2 i‖) := by
      have hp : Continuous (fun a : A => parabolicNorm a.1) :=
        continuous_parabolicNorm.comp continuous_fst
      have hprod : Continuous (fun a : A => ∏ i, ‖a.2 i‖) := by
        exact continuous_finsetProd Finset.univ (fun i _ =>
          continuous_norm.comp (continuous_apply i |>.comp continuous_snd))
      exact continuous_const.mul ((continuous_const.add hp).pow q) |>.mul hprod
    exact measurableSet_forall_le_continuous hm hf hg
  let E : Set Ω := ⋃ n : ℕ, ⋃ q : ℕ, ⋂ k : Fin 5,
    {w | ∀ a : ParabolicSpace × (Fin k.1 → ParabolicSpace),
      ‖iteratedFDeriv ℝ k.1 (f w) a.1 a.2‖ ≤
        (n : ℝ) * (1 + parabolicNorm a.1) ^ q * ∏ i, ‖a.2 i‖}
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun q =>
      MeasurableSet.iInter fun k => hineq n q k
  have hEeq : E = {w | Statements.HasPhi43NoiseGrowth (ξ w)} := by
    ext w
    constructor
    · intro hw
      rcases mem_iUnion.mp hw with ⟨n, hw⟩
      rcases mem_iUnion.mp hw with ⟨q, hw⟩
      refine ⟨n, q, ?_⟩
      intro j hj z
      let k : Fin 5 := ⟨j, by omega⟩
      have hC : 0 ≤ (n : ℝ) * (1 + parabolicNorm z) ^ q := by
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
          (by linarith [parabolicNorm_nonneg z]) _)
      apply (ContinuousMultilinearMap.opNorm_le_iff hC).2
      intro m
      have hw' : ∀ k : Fin 5, w ∈
          {w | ∀ a : ParabolicSpace × (Fin k.1 → ParabolicSpace),
            ‖iteratedFDeriv ℝ k.1 (f w) a.1 a.2‖ ≤
              (n : ℝ) * (1 + parabolicNorm a.1) ^ q * ∏ i, ‖a.2 i‖} := by
        simpa only [mem_iInter] using hw
      exact hw' k (z, m)
    · rintro ⟨Cg, q, hCg⟩
      obtain ⟨n, hn⟩ := exists_nat_ge Cg
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨q, ?_⟩⟩
      simp only [mem_iInter, mem_ofPred_eq]
      intro k a
      have hbound := hCg k.1 (by omega) a.1
      have heval :=
        (ContinuousMultilinearMap.le_of_opNorm_le hbound a.2)
      have hw : 0 ≤ (1 + parabolicNorm a.1) ^ q := by
        exact pow_nonneg (by linarith [parabolicNorm_nonneg a.1]) _
      have hp : 0 ≤ ∏ i, ‖a.2 i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
      calc
        ‖iteratedFDeriv ℝ k.1 (f w) a.1 a.2‖ ≤
            Cg * (1 + parabolicNorm a.1) ^ q * ∏ i, ‖a.2 i‖ := heval
        _ ≤ (n : ℝ) * (1 + parabolicNorm a.1) ^ q * ∏ i, ‖a.2 i‖ := by
          gcongr
  refine ⟨hEeq ▸ hEmeas, ?_⟩
  exact regularisedNoise_ae_hasPhi43NoiseGrowth P W hW ρ hρ hε ξ hξ

end RegularityStructures.Phi43

end
