/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.Parameters
public import Phi43.TheoremA.SelectedLiftsWithGrowth
public import Phi43.TheoremA.DyadicPaths
public import Phi43.TheoremA.LimitPackage
public import Phi43.TheoremA.BoundedTauClosure
public import Phi43.TheoremA.ExplosionFromPersistence
public import Phi43.TheoremA.StoppedLimitWindowBound
public import Phi43.TheoremA.BoundedTauRelations
public import Phi43.TheoremA.BoundedTauWitnessExtension
public import Phi43.TheoremA.FirstThreshold
public import Phi43.TheoremA.ConvergenceSelection
public import Phi43.TheoremA.InitialWindow
public import Phi43.TheoremA.StepLifts
public import Phi43.TheoremA.CrossLimitUniqueness
public import Phi43.ClassicalSolution.PathContinuity
public import Phi43.ClassicalSolution.Measurable
public import Phi43.Limit
public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.ClassicalSolution
public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import RegularityStructures.Statements.Defs.IsMassivePotential
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.IsModerateRenormalisedCanonicalModel
public import Phi43Statements.Defs.Phi43Dist
public import Phi43Statements.Defs.Phi43Size
public import RegularityStructures.Probability.WhiteNoise
public import Mathlib.Order.CompletePartialOrder
public import Phi43.TheoremA.MaximalPathWindow
public import Phi43.TheoremA.PathCauchyWindow

/-!
# Theorem A from its main analytic and probabilistic inputs

`theoremA_of_steps` derives the conclusion of Theorem A from four inputs, taken as hypotheses:

* `hG1`, the existence and uniqueness of the renormalised canonical model of a smooth noise
  (`Statements.renormalisedCanonicalModel_existsUnique`);
* `hG4`, the persistence and stopped continuity of classical solutions
  (`Statements.phi43ClassicalSolution_stoppedContinuity`);
* `hG7`, the convergence of the massive potentials of the noise (`Statements.phi43Noise_cauchy`);
* `hG10`, the convergence of the G-models (`Statements.phi43GModels_convergence`).

Each hypothesis is the corresponding statement in `Phi43Statements.Steps`, except that the
sample-space universes are tied to the single universe `u` of the conclusion.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

universe u

private theorem assembly_boundedTauClosureEvent_of_gModels
    {Ω : Type u} [MeasurableSpace Ω] {η : NegExponent}
    {κ : Kappa} {N : ℕ}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (u : ℕ → Ω → ℝ → C(Torus3, ℝ))
    (hident : ∀ n ω t, x n ω t = toHolderBesov η (u n ω t))
    {u₀ : C(Torus3, ℝ)} {f : ℕ → SpaceTime → ℝ}
    {C : ℕ → RenormalisationConstants}
    {Z : ℕ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup}
    {ψ : ℕ → Ω → ℝ → C(Torus3, ℝ)}
    (ω : Ω)
    (hG10good : ∀ T : ℕ, 1 ≤ T →
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        Statements.phi43Dist κ η T (Z n ω) (Z m ω) (ψ n ω) (ψ m ω) ≤
          ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ,
        Statements.phi43Size κ η T (Z n ω) (ψ n ω) ≤ ENNReal.ofReal B)
    (hPersistence : ∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
        (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ))
        (u : ℝ → C(Torus3, ℝ)) (T : ℝ),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Icc (0 : ℝ) T,
          holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Icc s (s + t₀),
            holderBesovENorm η (u t) ≤ ENNReal.ofReal R)
    (hStopped : ∀ T L B ϵ : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (f g : SpaceTime → ℝ)
        (C C' : RenormalisationConstants)
        (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
        (ψ ψ' : ℝ → C(Torus3, ℝ)) (u₀ : C(Torus3, ℝ))
        (u v : ℝ → C(Torus3, ℝ)),
        Statements.IsModeratePhi43Lift N κ f C Z ψ →
        Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
        ∀ t ∈ Icc (0 : ℝ) T,
          (∀ s ∈ Icc (0 : ℝ) t,
            holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
            holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
          holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ)
    (hLift : ∀ n, Statements.IsModeratePhi43Lift N κ (f n)
      (C n) (Z n ω) (ψ n ω))
    (hclass : ∀ n, IsClassicalSolution
      (3 * (C n).1 - 9 * (C n).2) (f n) u₀ (u n ω))
    (hinitial_bound : holderBesovENorm η u₀ ≤ ENNReal.ofReal
      (max 1 (holderBesovENorm η u₀).toReal)) :
    assemblyBoundedTauClosureEvent x hcont ω := by
  let L₀ : ℝ := max 1 (holderBesovENorm η u₀).toReal
  have hL₀ : 1 ≤ L₀ := by
    dsimp [L₀]
    exact le_max_left _ _
  have hB₁data := hG10good 1 (by norm_num)
  obtain ⟨B, hB⟩ := hB₁data.2
  let B₁ : ℝ := max B 1
  have hB₁ : 1 ≤ B₁ := by
    dsimp [B₁]
    exact le_max_right _ _
  have hsize₁ : ∀ n, Statements.phi43Size κ η 1 (Z n ω) (ψ n ω) ≤
      ENNReal.ofReal B₁ := by
    intro n
    dsimp [B₁]
    convert (hB n).trans (ENNReal.ofReal_mono (le_max_left B 1)) using 1
    all_goals norm_num
  obtain ⟨t₀, R, ht₀, ht₀1, hwindow⟩ := assembly_initial_window_of_steps
    hPersistence hL₀ hB₁ hLift hclass hsize₁
    (fun n => (hclass n).initial) hinitial_bound
  let R₀ : ℝ := max R 0
  have hR₀ : 0 ≤ R₀ := by
    dsimp [R₀]
    exact le_max_right _ _
  have hnorm_window : ∀ n, ∀ t ∈ Icc (0 : ℝ) t₀,
      ‖x n ω t‖ ≤ R₀ := by
    intro n t ht
    have hh : holderBesovENorm η (u n ω t) ≤ ENNReal.ofReal R₀ :=
      (hwindow n t ht).trans (ENNReal.ofReal_mono (le_max_left _ _))
    rw [hident n ω t, norm_toHolderBesov]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq
      (ENNReal.toReal_ofReal hR₀)
  obtain ⟨q₀, K₀, hq₀, hinitial_event⟩ :=
    assemblyBoundedTau_event_of_uniformBound x hcont ω ht₀ hnorm_window
  refine ⟨⟨q₀, K₀, hq₀, hinitial_event⟩, ?_⟩
  intro q L hq
  obtain ⟨K, hK⟩ := exists_nat_ge (q : ℝ)
  let H : ℕ := max 1 K
  have hH : 1 ≤ H := by
    dsimp [H]
    exact le_max_left _ _
  have hqH : (q : ℝ) ≤ (H : ℝ) := by
    dsimp [H]
    exact hK.trans (by exact_mod_cast le_max_right 1 K)
  obtain ⟨hmodel, ⟨B, hsize_raw⟩⟩ := hG10good H hH
  let B' : ℝ := max B 1
  have hB' : 1 ≤ B' := by
    dsimp [B']
    exact le_max_right _ _
  have hsize : ∀ n, Statements.phi43Size κ η (H : ℝ) (Z n ω) (ψ n ω) ≤
      ENNReal.ofReal B' := by
    intro n
    exact (hsize_raw n).trans (ENNReal.ofReal_mono (le_max_left _ _))
  let L' : ℝ := max (L : ℝ) 1
  have hL' : 1 ≤ L' := by
    dsimp [L']
    exact le_max_right _ _
  have hbound : ∀ n, ∀ t ∈ Icc (0 : ℝ) (q : ℝ),
      holderBesovENorm η (u n ω t) ≤ ENNReal.ofReal L' := by
    intro n t ht
    have hx := assemblyRationalBoundedPathEvent_bound q L x hcont ω hq n t ht
    have hnorm : ‖toHolderBesov η (u n ω t)‖ ≤ (L : ℝ) := by
      rw [← hident n ω t]
      exact hx
    have hreal : (holderBesovENorm η (u n ω t)).toReal ≤ (L : ℝ) := by
      rw [← norm_toHolderBesov]
      exact hnorm
    have htop : holderBesovENorm η (u n ω t) < ⊤ :=
      holderBesovENorm_lt_top η.2.le (u n ω t)
    have hh : holderBesovENorm η (u n ω t) ≤ ENNReal.ofReal (L : ℝ) :=
      (ENNReal.le_ofReal_iff_toReal_le
        (a := holderBesovENorm η (u n ω t))
        htop.ne (Nat.cast_nonneg L)).2 hreal
    exact hh.trans (ENNReal.ofReal_mono (le_max_left _ _))
  let d : ℕ → ℕ → ℝ≥0∞ := fun n m =>
    Statements.phi43Dist κ η (H : ℝ) (Z n ω) (Z m ω) (ψ n ω) (ψ m ω)
  have hmetric : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n m : ℕ,
      N₀ ≤ n → N₀ ≤ m → d n m ≤ ENNReal.ofReal δ := by
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := hmodel δ hδ
    exact ⟨N₀, fun n m hn hm => hN₀ n hn m hm⟩
  have hdist : ∀ n m : ℕ,
      Statements.phi43Dist κ η (H : ℝ) (Z n ω) (Z m ω) (ψ n ω) (ψ m ω) ≤ d n m := by
    intro n m
    rfl
  have hpath := assembly_path_cauchy_from_stopped_window
    (show 0 ≤ (q : ℝ) by exact_mod_cast hq.1.le)
    (show (1 : ℝ) ≤ (H : ℝ) by exact_mod_cast hH) hqH
    hStopped hL' hB' hLift hclass hsize d hmetric hdist hbound
  have hpath' : CauchySeq (fun n => assemblyPathRestriction q x hcont n ω) := by
    convert hpath using 1
    funext n
    apply ContinuousMap.ext
    intro t
    change x n ω t.1 = toHolderBesov η (u n ω t.1)
    exact hident n ω t.1
  have hnorm : ∀ n, ‖assemblyPathRestriction q x hcont n ω‖ ≤ (L : ℝ) := by
    intro n
    apply (ContinuousMap.norm_le _ (by exact_mod_cast (Nat.zero_le L))).2
    intro t
    rw [assemblyPathRestriction_eval]
    exact assemblyRationalBoundedPathEvent_bound q L x hcont ω hq n t.1 t.property
  exact ⟨hq.1, hnorm, hpath'⟩

private theorem assembly_boundedTauClosurePath_window
    {Ω : Type u} [MeasurableSpace Ω] {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (x₀ : HolderBesov η) (ω : Ω) {T : ℝ} (hT : 0 ≤ T)
    (hτ : ENNReal.ofReal T <
      assemblyBoundedTau (assemblyBoundedTauClosurePath x hcont x₀)
        (assemblyBoundedTauClosurePath_continuousOn x hcont x₀) ω) :
    CauchySeq (fun n =>
      ContinuousMap.mk
        (fun t : Icc (0 : ℝ) T =>
          assemblyBoundedTauClosurePath x hcont x₀ n ω t.1)
        (continuousOn_iff_continuous_domRestrict.mp
          ((assemblyBoundedTauClosurePath_continuousOn x hcont x₀ n ω).mono
            Icc_subset_Ici_self))) := by
  classical
  let xb := assemblyBoundedTauClosurePath x hcont x₀
  let hxb := assemblyBoundedTauClosurePath_continuousOn x hcont x₀
  let τb := assemblyBoundedTau xb hxb
  change CauchySeq (fun n =>
    ContinuousMap.mk (fun t : Icc (0 : ℝ) T => xb n ω t.1)
      (continuousOn_iff_continuous_domRestrict.mp
        ((hxb n ω).mono Icc_subset_Ici_self)))
  by_cases hE : assemblyBoundedTauClosureEvent x hcont ω
  · have hExists : ∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L xb hxb ω := by
      obtain ⟨q, L, hq⟩ :=
        (show assemblyBoundedTauClosureEvent x hcont ω from hE).1
      rcases hq with ⟨hqpos, hqbound⟩
      refine ⟨q, L, hqpos, ?_⟩
      intro n r hr
      simpa [xb, hxb, assemblyBoundedTauClosurePath, hE] using hqbound n r hr
    have hτ' : ENNReal.ofReal T < τb ω := by
      simpa [τb, xb, hxb] using hτ
    obtain ⟨q, L, hqT, hq⟩ :=
      (assemblyBoundedTau_lt_iff xb hxb ω hExists hT).mp hτ'
    have hqX : assemblyRationalBoundedPathEvent q L x hcont ω := by
      rcases hq with ⟨hqpos, hqbound⟩
      refine ⟨hqpos, ?_⟩
      intro n r hr
      simpa [xb, hxb, assemblyBoundedTauClosurePath, hE] using hqbound n r hr
    have hE' : (∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω) ∧
        ∀ q : ℚ, ∀ L : ℕ,
          assemblyRationalBoundedPathEvent q L x hcont ω →
            assemblyPathEvent q L x hcont ω := by
      simpa only [assemblyBoundedTauClosureEvent] using hE
    have hpathEvent : assemblyPathEvent q L x hcont ω := hE'.2 q L hqX
    have hpathWindow := assemblyTau_window x hcont ω
      ⟨q, L, hpathEvent⟩ hT
      ((assemblyTau_lt_iff_of_exists x hcont ω ⟨q, L, hpathEvent⟩ hT).2
        ⟨q, L, hqT, hpathEvent⟩)
    have heq : (fun n =>
        ContinuousMap.mk (fun t : Icc (0 : ℝ) T => xb n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hxb n ω).mono Icc_subset_Ici_self))) =
        (fun n =>
          ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n ω t.1)
            (continuousOn_iff_continuous_domRestrict.mp
              ((hcont n ω).mono Icc_subset_Ici_self))) := by
      funext n
      apply ContinuousMap.ext
      intro t
      change xb n ω t.1 = x n ω t.1
      simp [xb, assemblyBoundedTauClosurePath, hE]
    rw [heq]
    exact hpathWindow
  · rw [Metric.cauchySeq_iff']
    intro ε hε
    refine ⟨0, fun n _ => ?_⟩
    let _ : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
    refine lt_of_le_of_lt ?_ hε
    apply (ContinuousMap.dist_le_iff_of_nonempty (C := 0)).mpr
    intro t
    change dist (xb n ω t.1) (xb 0 ω t.1) ≤ 0
    simp [xb, assemblyBoundedTauClosurePath, hE]

private theorem assembly_boundedTau_congr_at
    {Ω : Type u} {η : NegExponent} [MeasurableSpace Ω]
    (x y : ℕ → Ω → ℝ → HolderBesov η)
    (hx : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hy : ∀ n ω, ContinuousOn (y n ω) (Ici (0 : ℝ)))
    (ω : Ω) (hxy : ∀ n t, x n ω t = y n ω t) :
    assemblyBoundedTau x hx ω = assemblyBoundedTau y hy ω := by
  classical
  have hev (q : ℚ) (L : ℕ) :
      assemblyRationalBoundedPathEvent q L x hx ω ↔
        assemblyRationalBoundedPathEvent q L y hy ω := by
    constructor
    · intro h
      rcases h with ⟨hq, hbound⟩
      refine ⟨hq, ?_⟩
      intro n r hr
      simpa [hxy n (r : ℝ)] using hbound n r hr
    · intro h
      rcases h with ⟨hq, hbound⟩
      refine ⟨hq, ?_⟩
      intro n r hr
      simpa [hxy n (r : ℝ)] using hbound n r hr
  have hex :
      (∃ q : ℚ, ∃ L : ℕ, assemblyRationalBoundedPathEvent q L x hx ω) ↔
        ∃ q : ℚ, ∃ L : ℕ, assemblyRationalBoundedPathEvent q L y hy ω := by
    constructor
    · rintro ⟨q, L, hq⟩
      exact ⟨q, L, (hev q L).mp hq⟩
    · rintro ⟨q, L, hq⟩
      exact ⟨q, L, (hev q L).mpr hq⟩
  unfold assemblyBoundedTau
  by_cases h : ∃ q : ℚ, ∃ L : ℕ, assemblyRationalBoundedPathEvent q L x hx ω
  · have h' := hex.mp h
    simp only [h, h', ↓reduceIte]
    congr 2
    funext q
    congr 1
    funext L
    simp [hev q L]
  · have h' : ¬∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L y hy ω := by
      intro h'
      exact h (hex.mpr h')
    simp only [h, h', ↓reduceIte]

theorem theoremA_of_steps
    (hG1 :
      ∀ (N : ℕ) (κ : Kappa)
        (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
        (_hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
          ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤
            Cg * (1 + parabolicNorm z) ^ q)
        (C : RenormalisationConstants),
        (∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
          Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z) ∧
        ∀ Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup,
          Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z →
          Statements.IsModerateRenormalisedCanonicalModel N κ noise C Z' →
            Z.diffNormOn Z' (gamma κ) Set.univ = 0)
    (hG4 :
      ∀ (κ : Kappa)
        (_hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ)
        (_hN : 5 ≤ N) (η : NegExponent)
        (_hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
        (_hκη : κ.1 < -(1 / 2 : ℝ) - η),
        (∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
          ∀ (f : SpaceTime → ℝ)
            (C : RenormalisationConstants)
            (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
            (ψ : ℝ → C(Torus3, ℝ))
            (u₀ : C(Torus3, ℝ))
            (u : ℝ → C(Torus3, ℝ)) (T : ℝ),
            Statements.IsModeratePhi43Lift N κ f C Z ψ →
            IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
            1 ≤ T →
            Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
            ∀ s ∈ Set.Icc (0 : ℝ) T,
              holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
              ∀ t ∈ Set.Icc s (s + t₀),
                holderBesovENorm η (u t) ≤ ENNReal.ofReal R) ∧
        ∀ T L B ϵ : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ, 0 < δ ∧
          ∀ (f g : SpaceTime → ℝ)
            (C C' : RenormalisationConstants)
            (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
            (ψ ψ' : ℝ → C(Torus3, ℝ))
            (u₀ : C(Torus3, ℝ))
            (u v : ℝ → C(Torus3, ℝ)),
            Statements.IsModeratePhi43Lift N κ f C Z ψ →
            Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
            IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
            IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
            Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
            Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
            Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
            ∀ t ∈ Set.Icc (0 : ℝ) T,
              (∀ s ∈ Set.Icc (0 : ℝ) t,
                holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
                holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
              holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ)
    (hG7 :
      ∀ (η : NegExponent),
        (η : ℝ) < -(1 / 2 : ℝ) →
        (∀ f : SpaceTime → ℝ,
          IsSmoothOnSpaceTime f →
          Statements.HasPhi43NoiseGrowth f →
          ∃ ψ : ℝ → C(Torus3, ℝ),
            RegularityStructures.IsMassivePotential f ψ ∧
            IsSmoothOnSpaceTime (fun z : SpaceTime => ψ z.1 z.2) ∧
            Continuous ψ) ∧
        (∀ ρ : ParabolicSpace → ℝ,
          IsMollifier ρ →
          ∀ {Ω : Type u} [MeasurableSpace Ω]
            (P : Measure Ω) [IsProbabilityMeasure P]
            (W : (SpaceTime → ℝ) → Ω → ℝ),
            IsWhiteNoise P W →
            ∀ ξ : ℝ → Ω → SpaceTime → ℝ,
              (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
                IsRegularisedNoise P W ρ ε (ξ ε)) →
              ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
                MeasurableSet {ω | Statements.HasPhi43NoiseGrowth (ξ ε ω)} ∧
                ∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ε ω)) ∧
        ∃ β₀ : ℝ, 0 < β₀ ∧
        ∀ ρ ρ' : ParabolicSpace → ℝ,
          IsMollifier ρ → IsMollifier ρ' →
          ∀ T : ℝ, 1 ≤ T → ∀ p : ℕ, 1 ≤ p →
          ∃ C : ℝ, 0 ≤ C ∧
          ∀ {Ω : Type u} [MeasurableSpace Ω]
            (P : Measure Ω) [IsProbabilityMeasure P]
            (W : (SpaceTime → ℝ) → Ω → ℝ),
            IsWhiteNoise P W →
            ∀ (ξ ξ' : ℝ → Ω → SpaceTime → ℝ),
              (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
                IsRegularisedNoise P W ρ ε (ξ ε)) →
              (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
                IsRegularisedNoise P W ρ' ε (ξ' ε)) →
              ∀ (ψ ψ' : ℝ → Ω → ℝ → C(Torus3, ℝ)),
                (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
                  RegularityStructures.IsMassivePotential (ξ ε ω) (ψ ε ω)) →
                (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
                  RegularityStructures.IsMassivePotential (ξ' ε ω) (ψ' ε ω)) →
                ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ε' ∈ Set.Ioc (0 : ℝ) 1,
                  AEMeasurable
                      (fun ω => Statements.phi43NoiseSize η T (ψ ε ω)) P ∧
                  AEMeasurable
                      (fun ω => Statements.phi43NoiseDist η T
                        (ψ ε ω) (ψ' ε' ω)) P ∧
                  ∫⁻ ω, Statements.phi43NoiseSize η T (ψ ε ω) ^ p ∂P ≤
                    ENNReal.ofReal C ∧
                  ∫⁻ ω, Statements.phi43NoiseDist η T
                      (ψ ε ω) (ψ' ε' ω) ^ p ∂P ≤
                    ENNReal.ofReal (C * max ε ε' ^ (β₀ * p)))
    (hG10 :
      ∀ (κ : Kappa)
        (_hκE : κ.1 ∉ Statements.excludedKappa) (N : ℕ)
        (_hN : 5 ≤ N) (η : NegExponent)
        (_hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
        (_hκη : κ.1 < -(1 / 2 : ℝ) - η)
        (ρ ρ' : ParabolicSpace → ℝ)
        (_hρ : IsMollifier ρ) (_hρ' : IsMollifier ρ')
        (c : RenormalisationConstants),
        ∀ {Ω : Type u} [MeasurableSpace Ω]
          (P : Measure Ω) [IsProbabilityMeasure P]
          (W : (SpaceTime → ℝ) → Ω → ℝ),
          IsWhiteNoise P W →
          ∀ (ξ ξ' : ℝ → Ω → SpaceTime → ℝ),
            (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
              IsRegularisedNoise P W ρ ε (ξ ε)) →
            (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
              IsRegularisedNoise P W ρ' ε (ξ' ε)) →
            ∀ (Z Z' : ℝ → Ω → Model (phi43RegularityStructure κ)
                parabolicSemigroup)
              (ψ ψ' : ℝ → Ω → ℝ → C(Torus3, ℝ)),
              (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
                Statements.IsModeratePhi43Lift N κ (ξ ε ω)
                  (wickConstant ρ ε + c.1, sunsetConstant ρ ε + c.2)
                  (Z ε ω) (ψ ε ω)) →
              (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
                Statements.IsModeratePhi43Lift N κ (ξ' ε ω)
                  (wickConstant ρ' ε + c.1, sunsetConstant ρ' ε + c.2)
                  (Z' ε ω) (ψ' ε ω)) →
              (∀ T : ℝ, 1 ≤ T → ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ,
                ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
                  P {ω | ENNReal.ofReal B <
                    Statements.phi43Size κ η T (Z ε ω) (ψ ε ω)} ≤
                    ENNReal.ofReal ϑ) ∧
              (∀ T : ℝ, 1 ≤ T → ∀ δ : ℝ, 0 < δ →
                Tendsto (fun e : ℝ × ℝ =>
                    P {ω | ENNReal.ofReal δ <
                      Statements.phi43Dist κ η T (Z e.1 ω) (Z' e.2 ω)
                        (ψ e.1 ω) (ψ' e.2 ω)})
                  ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 0)) ∧
              ∀ᵐ ω ∂P, ∀ T : ℕ, 1 ≤ T →
                (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
                  Statements.phi43Dist κ η T
                    (Z ((2 : ℝ) ^ n)⁻¹ ω) (Z ((2 : ℝ) ^ m)⁻¹ ω)
                    (ψ ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ m)⁻¹ ω) ≤
                    ENNReal.ofReal δ) ∧
                ∃ B : ℝ, ∀ n : ℕ,
                  Statements.phi43Size κ η T
                    (Z ((2 : ℝ) ^ n)⁻¹ ω) (ψ ((2 : ℝ) ^ n)⁻¹ ω) ≤
                    ENNReal.ofReal B)
    : ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (SpaceTime → ℝ) → Ω → ℝ)
      (_hW : IsWhiteNoise P W) (a : ℝ)
      (u₀ : C(Torus3, ℝ)) (_hu₀ : IsSmoothOnTorus u₀)
      (η : NegExponent)
      (_hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
      (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ)
      (ξ : ℝ → Ω → SpaceTime → ℝ)
      (_hξ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        IsRegularisedNoise P W ρ ε (ξ ε))
      (u : ℝ → Ω → ℝ → C(Torus3, ℝ))
      (_hu : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
        IsClassicalSolution
          (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε)
          (ξ ε ω) u₀ (u ε ω)),
      ∃ (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η),
        IsPhi43Limit P η u₀ u τ v ∧
        ∀ (ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
          (ξ' : ℝ → Ω → SpaceTime → ℝ)
          (u' : ℝ → Ω → ℝ → C(Torus3, ℝ))
          (τ' : Ω → ℝ≥0∞) (v' : Ω → ℝ → HolderBesov η),
          IsMollifier ρ' →
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            IsRegularisedNoise P W ρ' ε (ξ' ε)) →
          (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
            IsClassicalSolution
              (a + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε)
              (ξ' ε ω) u₀ (u' ε ω)) →
          IsPhi43Limit P η u₀ u' τ' v' →
          τ' =ᵐ[P] τ ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
            ENNReal.ofReal t < τ ω → v' ω t = v ω t := by
  intro Ω instΩ P instP W hW a u₀ hu₀ η hη ρ hρ ξ hξ u hu
  classical
  obtain ⟨κ, hκE, hκη⟩ := assembly_exists_kappa (η : ℝ) hη.2
  obtain ⟨hG7potential, hG7growth, hG7mom⟩ := hG7 η hη.2
  let C : ℝ → RenormalisationConstants :=
    fun ε => (wickConstant ρ ε + a / 3, sunsetConstant ρ ε + 0)
  have hclass : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
      IsClassicalSolution (3 * (C ε).1 - 9 * (C ε).2)
        (ξ ε ω) u₀ (u ε ω) := by
    intro ε hε ω
    rw [show 3 * (C ε).1 - 9 * (C ε).2 =
      a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε by
        dsimp [C]
        ring]
    exact hu ε hε ω
  have hpotential : ∀ f : SpaceTime → ℝ, IsSmoothOnSpaceTime f →
      Statements.HasPhi43NoiseGrowth f →
      ∃ ψ : ℝ → C(Torus3, ℝ), RegularityStructures.IsMassivePotential f ψ := by
    intro f hf hg
    obtain ⟨ψ, hψ, -, -⟩ := hG7potential f hf hg
    exact ⟨ψ, hψ⟩
  have hξsmooth : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
      IsSmoothOnSpaceTime (ξ ε ω) := by
    intro ε hε ω
    exact (hξ ε hε).1 ω
  obtain ⟨Z, ψ, hZgrowth⟩ := assembly_selected_lifts_with_growth
    (N := 5) (κ := κ) hG1 hξsmooth hpotential (C := C)
  have hZ : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift 5 κ (ξ ε ω) (C ε) (Z ε ω) (ψ ε ω) := by
    intro ε hε
    filter_upwards [(hG7growth ρ hρ P W hW ξ hξ ε hε).2] with ω hg
    exact hZgrowth ε hε ω hg
  let e : ℕ → ℝ := fun n => ((2 : ℝ) ^ n)⁻¹
  have he : ∀ n : ℕ, e n ∈ Set.Ioc (0 : ℝ) 1 := by
    intro n
    dsimp [e]
    have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    constructor
    · positivity
    · exact inv_le_one_of_one_le₀ hpow
  have hclassd : ∀ n ω,
      IsClassicalSolution (3 * (C (e n)).1 - 9 * (C (e n)).2)
        (ξ (e n) ω) u₀ (u (e n) ω) := by
    intro n ω
    exact hclass (e n) (he n) ω
  have hpaths := assembly_dyadic_holder_paths_of_steps (η := η) P W hW ρ hρ hξ hu₀
    (C := C) (u := fun n ω => u (e n) ω) hclassd
  let x : ℕ → Ω → ℝ → HolderBesov η :=
    fun n ω t => toHolderBesov η (u (e n) ω t)
  have hxcont : ∀ n ω, ContinuousOn (x n ω) (Set.Ici (0 : ℝ)) := by
    intro n ω
    exact hpaths.1 n ω
  have hxmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t) := by
    intro n t ht
    exact hpaths.2 n t ht
  have hxident : ∀ n ω t, x n ω t = toHolderBesov η (u (e n) ω t) := by
    intro n ω t
    rfl
  let Zd : ℕ → Ω → Model (phi43RegularityStructure κ) parabolicSemigroup :=
    fun n ω => Z (e n) ω
  let ψd : ℕ → Ω → ℝ → C(Torus3, ℝ) :=
    fun n ω => ψ (e n) ω
  have hZd : ∀ n, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift 5 κ (ξ (e n) ω) (C (e n))
        (Zd n ω) (ψd n ω) := by
    intro n
    filter_upwards [hZ (e n) (he n)] with ω hω
    exact hω
  have hZ' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift 5 κ (ξ ε ω)
        (wickConstant ρ ε + (a / 3), sunsetConstant ρ ε + 0)
        (Z ε ω) (ψ ε ω) := by
    intro ε hε
    simpa [C] using hZ ε hε
  obtain ⟨hG10tight, hG10cross, hG10good⟩ :=
    hG10 κ hκE 5 (by norm_num) η hη hκη ρ ρ hρ hρ
      (a / 3, 0)
      P W hW ξ ξ hξ hξ Z Z ψ ψ hZ' hZ'
  have hG10good' : ∀ᵐ ω ∂P, ∀ T : ℕ, 1 ≤ T →
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
        Statements.phi43Dist κ η T (Zd n ω) (Zd m ω) (ψd n ω) (ψd m ω) ≤
          ENNReal.ofReal δ) ∧
      ∃ B : ℝ, ∀ n : ℕ,
        Statements.phi43Size κ η T (Zd n ω) (ψd n ω) ≤ ENNReal.ofReal B := by
    simpa [Zd, ψd, e] using hG10good
  have hgrowth : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.HasPhi43NoiseGrowth (ξ ε ω) := by
    intro ε hε
    exact (hG7growth ρ hρ P W hW ξ hξ ε hε).2
  have hgrowthd : ∀ᵐ ω ∂P, ∀ n,
      Statements.HasPhi43NoiseGrowth (ξ (e n) ω) :=
    ae_all_iff.2 (fun n => hgrowth (e n) (he n))
  let Good : Set Ω := {ω |
    (∀ n, Statements.HasPhi43NoiseGrowth (ξ (e n) ω)) ∧
      (∀ T : ℕ, 1 ≤ T →
        (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ m ≥ n₀,
          Statements.phi43Dist κ η T (Zd n ω) (Zd m ω) (ψd n ω) (ψd m ω) ≤
            ENNReal.ofReal δ) ∧
        ∃ B : ℝ, ∀ n : ℕ,
          Statements.phi43Size κ η T (Zd n ω) (ψd n ω) ≤ ENNReal.ofReal B)}
  have hGoodAE : ∀ᵐ ω ∂P, ω ∈ Good := by
    filter_upwards [hgrowthd, hG10good'] with ω hg hg10
    exact ⟨hg, hg10⟩
  have hGoodNM : NullMeasurableSet Good P := by
    apply NullMeasurableSet.of_compl
    apply NullMeasurableSet.of_null
    exact (mem_ae_iff.mp hGoodAE)
  obtain ⟨E, hEsub, hEmeas, hEae⟩ := hGoodNM.exists_measurable_subset_ae_eq
  have hu₀bound : holderBesovENorm η u₀ ≤ ENNReal.ofReal
      (max 1 (holderBesovENorm η u₀).toReal) := by
    have htop : holderBesovENorm η u₀ < ⊤ :=
      holderBesovENorm_lt_top η.2.le u₀
    calc
      holderBesovENorm η u₀ = ENNReal.ofReal (holderBesovENorm η u₀).toReal :=
        (ENNReal.ofReal_toReal htop.ne).symm
      _ ≤ ENNReal.ofReal (max 1 (holderBesovENorm η u₀).toReal) :=
        ENNReal.ofReal_mono (le_max_right _ _)
  have hclosure : ∀ᵐ ω ∂P,
      assemblyBoundedTauClosureEvent x hxcont ω := by
    filter_upwards [hG10good', hgrowthd] with ω hG10ω hgrowthω
    have hLiftω : ∀ n, Statements.IsModeratePhi43Lift 5 κ (ξ (e n) ω) (C (e n))
        (Zd n ω) (ψd n ω) := by
      intro n
      exact hZgrowth (e n) (he n) ω (hgrowthω n)
    apply assembly_boundedTauClosureEvent_of_gModels x hxcont
      (fun n ω t => u (e n) ω t) hxident ω hG10ω
      (hG4 κ hκE 5 (by norm_num) η hη hκη).1
      (hG4 κ hκE 5 (by norm_num) η hη hκη).2 hLiftω
      (fun n => hclassd n ω) hu₀bound
  let x₀ : HolderBesov η := toHolderBesov η u₀
  let xcl : ℕ → Ω → ℝ → HolderBesov η :=
    assemblyBoundedTauClosurePath x hxcont x₀
  let hclcont : ∀ n ω, ContinuousOn (xcl n ω) (Set.Ici (0 : ℝ)) :=
    assemblyBoundedTauClosurePath_continuousOn x hxcont x₀
  let τcl : Ω → ℝ≥0∞ := assemblyBoundedTau xcl hclcont
  have hclmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => xcl n ω t) :=
    assemblyBoundedTauClosurePath_measurable x hxcont x₀ hxmeas
  have hrawWindow : ∀ ω T, 0 ≤ T → ENNReal.ofReal T < τcl ω →
      CauchySeq (fun n =>
        ContinuousMap.mk (fun t : Set.Icc (0 : ℝ) T => xcl n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hclcont n ω).mono Icc_subset_Ici_self))) := by
    intro ω T hT hτ
    exact assembly_boundedTauClosurePath_window x hxcont x₀ ω hT hτ
  have hrawCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τcl ω →
      CauchySeq (fun n => xcl n ω t) := by
    intro ω t ht hτ
    exact assembly_pointwiseCauchy_of_pathWindow xcl τcl hclcont hrawWindow ht hτ
  let uRaw : ℕ → Ω → ℝ → C(Torus3, ℝ) := fun n ω t =>
    if assemblyBoundedTauClosureEvent x hxcont ω then u (e n) ω t else u₀
  have hrawIdent : ∀ n ω t, xcl n ω t = toHolderBesov η (uRaw n ω t) := by
    intro n ω t
    by_cases hE : assemblyBoundedTauClosureEvent x hxcont ω
    · simp [xcl, uRaw, assemblyBoundedTauClosurePath, hE, x]
    · simp [xcl, uRaw, assemblyBoundedTauClosurePath, hE, x₀]
  have hrawInitial : ∀ n ω, xcl n ω 0 = x₀ := by
    intro n ω
    by_cases hE : assemblyBoundedTauClosureEvent x hxcont ω
    · simp [xcl, assemblyBoundedTauClosurePath, hE, x, x₀,
        (hclassd n ω).initial]
    · simp [xcl, assemblyBoundedTauClosurePath, hE]
  let xbar : ℕ → Ω → ℝ → HolderBesov η := fun n ω t =>
    if ω ∈ E then xcl n ω t else x₀
  have hbarcont : ∀ n ω, ContinuousOn (xbar n ω) (Set.Ici (0 : ℝ)) := by
    intro n ω
    by_cases hω : ω ∈ E
    · change ContinuousOn (fun t => if ω ∈ E then xcl n ω t else x₀)
        (Set.Ici (0 : ℝ))
      simp only [hω, ↓reduceIte]
      exact hclcont n ω
    · change ContinuousOn (fun t => if ω ∈ E then xcl n ω t else x₀)
        (Set.Ici (0 : ℝ))
      simp only [hω, ↓reduceIte]
      exact continuousOn_const
  have hbarmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => xbar n ω t) := by
    intro n t ht
    exact Measurable.ite hEmeas (hclmeas n t ht) measurable_const
  let τ : Ω → ℝ≥0∞ := assemblyBoundedTau xbar hbarcont
  have hτmeas : Measurable τ := assemblyBoundedTau_measurable xbar hbarcont hbarmeas
  have hτpos : ∀ ω, 0 < τ ω := fun ω => assemblyBoundedTau_pos xbar hbarcont ω
  have hbarWindow : ∀ ω T, 0 ≤ T → ENNReal.ofReal T < τ ω →
      CauchySeq (fun n =>
        ContinuousMap.mk (fun t : Set.Icc (0 : ℝ) T => xbar n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hbarcont n ω).mono Icc_subset_Ici_self))) := by
    intro ω T hT hτω
    by_cases hω : ω ∈ E
    · have hfun : (fun n t => xbar n ω t) = (fun n t => xcl n ω t) := by
        funext n t
        simp [xbar, hω]
      have hτeq : τ ω = τcl ω := by
        exact assembly_boundedTau_congr_at xbar xcl hbarcont hclcont ω
          (fun n t => congrFun (congrFun hfun n) t)
      have hτcl : ENNReal.ofReal T < τcl ω := by
        rw [← hτeq]
        exact hτω
      simpa only [xbar, hω, ↓reduceIte] using hrawWindow ω T hT hτcl
    · rw [Metric.cauchySeq_iff']
      intro ε hε
      refine ⟨0, fun n _ => ?_⟩
      let _ : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
      refine lt_of_le_of_lt ?_ hε
      apply (ContinuousMap.dist_le_iff_of_nonempty (C := 0)).mpr
      intro t
      change dist (if ω ∈ E then xcl n ω t.1 else x₀)
        (if ω ∈ E then xcl 0 ω t.1 else x₀) ≤ 0
      simp only [hω, ↓reduceIte, dist_self]
      exact le_rfl
  have hbarCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => xbar n ω t) := by
    intro ω t ht hτ'
    exact assembly_pointwiseCauchy_of_pathWindow xbar τ hbarcont hbarWindow ht hτ'
  have hbarInitial : ∀ n ω, xbar n ω 0 = x₀ := by
    intro n ω
    by_cases hω : ω ∈ E
    · change (if ω ∈ E then xcl n ω 0 else x₀) = x₀
      simp only [hω, ↓reduceIte]
      exact hrawInitial n ω
    · change (if ω ∈ E then xcl n ω 0 else x₀) = x₀
      simp only [hω, ↓reduceIte]
  have hclosureOnE : ∀ ω, ω ∈ E →
      assemblyBoundedTauClosureEvent x hxcont ω := by
    intro ω hω
    have hGoodω := hEsub hω
    have hLiftω : ∀ n, Statements.IsModeratePhi43Lift 5 κ (ξ (e n) ω) (C (e n))
        (Zd n ω) (ψd n ω) := by
      intro n
      exact hZgrowth (e n) (he n) ω (hGoodω.1 n)
    exact assembly_boundedTauClosureEvent_of_gModels x hxcont
      (fun n ω t => u (e n) ω t) hxident ω hGoodω.2
      (hG4 κ hκE 5 (by norm_num) η hη hκη).1
      (hG4 κ hκE 5 (by norm_num) η hη hκη).2 hLiftω
      (fun n => hclassd n ω) hu₀bound
  let ubar : ℕ → Ω → ℝ → C(Torus3, ℝ) := fun n ω t =>
    if ω ∈ E then u (e n) ω t else u₀
  have hbarIdent : ∀ n ω t, xbar n ω t = toHolderBesov η (ubar n ω t) := by
    intro n ω t
    by_cases hω : ω ∈ E
    · have hcl := hclosureOnE ω hω
      simp [xbar, ubar, xcl, assemblyBoundedTauClosurePath, hcl, x, hω]
    · simp [xbar, ubar, x₀, hω]
  let v : Ω → ℝ → HolderBesov η :=
    assemblyStoppedLimit xbar τ hbarCauchy
  have hlimit : IsPhi43Limit P η u₀ u τ v := by
    apply assembly_isPhi43Limit_of_stoppedData P u₀ xbar u τ
      hbarCauchy hbarcont hbarmeas hbarWindow hτmeas hτpos hbarInitial
    · intro ω hfinite hbounded
      by_cases hω : ω ∈ E
      · have hGoodω := hEsub hω
        have hLiftω : ∀ n, Statements.IsModeratePhi43Lift 5 κ (ξ (e n) ω) (C (e n))
            (Zd n ω) (ψd n ω) := by
          intro n
          exact hZgrowth (e n) (he n) ω (hGoodω.1 n)
        obtain ⟨H, hH⟩ := exists_nat_ge (max 1 (τ ω).toReal)
        have hH1 : (1 : ℝ) ≤ (H : ℝ) := by
          exact (le_max_left _ _).trans (by exact_mod_cast hH)
        have hτH : (τ ω).toReal ≤ (H : ℝ) := by
          exact (le_max_right _ _).trans (by exact_mod_cast hH)
        obtain ⟨B, hB⟩ := (hGoodω.2 H (by exact_mod_cast hH1)).2
        let B' : ℝ := max B 1
        have hB' : 1 ≤ B' := by
          dsimp [B']
          exact le_max_right _ _
        have hsize : ∀ n, Statements.phi43Size κ η (H : ℝ)
            (Zd n ω) (ψd n ω) ≤ ENNReal.ofReal B' := by
          intro n
          exact (hB n).trans (ENNReal.ofReal_mono (le_max_left _ _))
        have hclassω : ∀ n,
            IsClassicalSolution (3 * (C (e n)).1 - 9 * (C (e n)).2)
              (ξ (e n) ω) u₀ (ubar n ω) := by
          intro n
          simp only [ubar, hω, ↓reduceIte]
          exact hclassd n ω
        exact (assembly_explosion_of_persistence_eventual xbar ubar hbarIdent τ
          hbarCauchy hbarcont hbarWindow (by rfl) (hτpos ω)
          (fun A B hA hB => by
            obtain ⟨t₀, R, ht₀, ht₀1, hR⟩ :=
              (hG4 κ hκE 5 (by norm_num) η hη hκη).1 A B hA hB
            exact ⟨t₀, R, ht₀, hR⟩) hB' hH1 hτH
          hLiftω hclassω hsize hbounded) hfinite
      · have hτtop : τ ω = ⊤ := by
          apply ENNReal.eq_top_of_forall_nnreal_le
          intro r
          obtain ⟨L, hL⟩ := exists_nat_ge ‖x₀‖
          obtain ⟨K, hK⟩ := exists_nat_ge r
          let q : ℚ := K + 1
          have hqr : (r : ℝ) ≤ (q : ℝ) := by
            have hKr : (r : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
            dsimp [q]
            norm_num
            linarith
          have hev : assemblyRationalBoundedPathEvent q L xbar hbarcont ω := by
            refine ⟨?_, ?_⟩
            · dsimp [q]
              positivity
            · intro n s hs
              simp only [xbar, hω, ↓reduceIte]
              exact hL
          have hExists : ∃ q : ℚ, ∃ L : ℕ,
              assemblyRationalBoundedPathEvent q L xbar hbarcont ω :=
            ⟨q, L, hev⟩
          have hleq : ENNReal.ofReal (q : ℝ) ≤ τ ω := by
            have hleq' : ENNReal.ofReal (q : ℝ) ≤
                assemblyBoundedTau xbar hbarcont ω := by
              rw [show assemblyBoundedTau xbar hbarcont ω =
                  ⨆ q : ℚ, ⨆ L : ℕ,
                    if assemblyRationalBoundedPathEvent q L xbar hbarcont ω then
                      ENNReal.ofReal (q : ℝ) else 0 by
                simp [assemblyBoundedTau, hExists]]
              exact le_iSup_of_le q (le_iSup_of_le L (by simp [hev]))
            simpa only [τ] using hleq'
          calc
            (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := by simp
            _ ≤ ENNReal.ofReal (q : ℝ) := ENNReal.ofReal_mono hqr
            _ ≤ τ ω := hleq
        have : (⊤ : ℝ≥0∞) < ⊤ := by simp [hτtop] at hfinite
        exact (lt_irrefl _ this)
    · intro T hT δ hδ
      refine tendsto_order.2 ?_
      refine ⟨?_, ?_⟩
      · intro b hb
        exact Filter.Eventually.of_forall (fun _ => hb.trans_le bot_le)
      · intro b hb
        by_cases hbtop : b = ⊤
        · simp [hbtop]
        · have hbtr : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbtop
          let α : ℝ := min 1 (b.toReal / 2)
          have hα : 0 < α := by
            dsimp [α]
            exact lt_min one_pos (by positivity)
          have hαb : ENNReal.ofReal α < b := by
            apply (ENNReal.ofReal_lt_iff_lt_toReal hα.le hbtop).2
            dsimp [α]
            exact (min_le_right _ _).trans_lt (by linarith)
          let q : ℝ := α / 10
          have hq : 0 < q := by
            dsimp [q]
            linarith
          obtain ⟨K, hK⟩ := exists_nat_ge T
          let H : ℕ := max 1 K
          have hH1 : (1 : ℝ) ≤ H := by
            dsimp [H]
            exact_mod_cast le_max_left 1 K
          have hTH : T ≤ (H : ℝ) := by
            exact hK.trans (by
              dsimp [H]
              exact_mod_cast le_max_right 1 K)
          let A : Set Ω := E ∩ {ω | ENNReal.ofReal T < τ ω}
          have hA : MeasurableSet A := by
            exact hEmeas.inter (measurableSet_lt measurable_const hτmeas)
          let p : ℕ → Ω → C(Icc (0 : ℝ) T, HolderBesov η) := fun n ω =>
            ContinuousMap.mk (fun t : Icc (0 : ℝ) T => xbar n ω t.1)
              (continuousOn_iff_continuous_domRestrict.mp
                ((hbarcont n ω).mono Icc_subset_Ici_self))
          have hp : ∀ n, Measurable (p n) := by
            intro n
            apply ContinuousMap.measurable_iff_eval.2
            intro t
            dsimp [p]
            exact hbarmeas n t.1 t.2.1
          have hpCauchy : ∀ ω, ω ∈ A → CauchySeq (fun n => p n ω) := by
            intro ω hω
            dsimp [p]
            exact hbarWindow ω T hT.le hω.2
          let r : ℝ := min (1 / 4 : ℝ) (δ / 4)
          have hr : 0 < r := by
            dsimp [r]
            exact lt_min (by norm_num) (by linarith)
          have hcover : ∀ M : ℕ, A ⊆ ⋃ L : ℕ, ⋃ k : ℕ,
              assemblyConvergencePathTail p (M + k) r (L : ℝ) := by
            intro M ω hω
            have hr2 : 0 < r / 2 := by linarith
            obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.1 (hpCauchy ω hω)) (r / 2) hr2
            let n : ℕ := M + N
            obtain ⟨L, hL⟩ := exists_nat_ge (‖p N ω‖ + r)
            refine Set.mem_iUnion.mpr ⟨L, Set.mem_iUnion.mpr ⟨N, ?_⟩⟩
            dsimp [assemblyConvergencePathTail]
            change (∀ m, M + N ≤ m → ∀ k, M + N ≤ k →
                dist (p m ω) (p k ω) ≤ r) ∧
              ∀ m, M + N ≤ m → ‖p m ω‖ ≤ (L : ℝ)
            refine ⟨?_, ?_⟩
            · intro m hm k hk
              have hmn := hN m (le_trans (Nat.le_add_left N M) hm)
              have hkn := hN k (le_trans (Nat.le_add_left N M) hk)
              have hmk : dist (p m ω) (p k ω) ≤
                  dist (p m ω) (p N ω) + dist (p N ω) (p k ω) :=
                dist_triangle _ _ _
              exact hmk.trans ((add_le_add hmn.le (by
                have : dist (p N ω) (p k ω) < r / 2 := by
                  simpa [dist_comm] using hkn
                exact this.le)).trans (by linarith))
            · intro m hm
              have hmN : N ≤ m := le_trans (Nat.le_add_left N M) hm
              have hmn : ‖p m ω - p N ω‖ ≤ r := by
                rw [← dist_eq_norm]
                exact (hN m hmN).le.trans (by linarith)
              calc
                ‖p m ω‖ = ‖(p m ω - p N ω) + p N ω‖ := by rw [sub_add_cancel]
                _ ≤ ‖p m ω - p N ω‖ + ‖p N ω‖ := norm_add_le _ _
                _ ≤ r + ‖p N ω‖ := add_le_add hmn le_rfl
                _ = ‖p N ω‖ + r := add_comm _ _
                _ ≤ (L : ℝ) := hL
          obtain ⟨n₀, hn₀, L, hpath₀⟩ :=
            assemblyConvergencePathTail_exists_index P A hA p hp r hr 0 q hq
              (hcover 0)
          obtain ⟨B, hB⟩ := hG10tight H hH1 q hq
          let B₀ : ℝ := max B 1
          have hB₀ : 1 ≤ B₀ := by
            dsimp [B₀]
            exact le_max_right _ _
          let A₀ : ℝ := max (L : ℝ) ‖x₀‖ + 1
          have hA₀ : 1 ≤ A₀ := by
            dsimp [A₀]
            have : 0 ≤ max (L : ℝ) ‖x₀‖ := le_max_of_le_left (by positivity)
            linarith
          have hLA₀ : (L : ℝ) ≤ A₀ := by
            dsimp [A₀]
            exact (le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num))
          have hx₀A₀ : ‖x₀‖ < A₀ := by
            dsimp [A₀]
            exact lt_add_of_le_of_pos (le_max_right _ _) (by norm_num)
          obtain ⟨d, hd, hδspec⟩ := (hG4 κ hκE 5 (by norm_num) η hη hκη).2
            (H : ℝ) A₀ B₀ r hH1 hA₀ hB₀ hr
          have hcross := hG10cross H hH1 d hd
          have hcross_ev : {z : ℝ × ℝ |
              P {ω | ENNReal.ofReal d <
              Statements.phi43Dist κ η H (Z z.1 ω) (Z z.2 ω)
                (ψ z.1 ω) (ψ z.2 ω)} < ENNReal.ofReal q} ∈
              (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)) := by
            exact (tendsto_order.1 hcross).2 (ENNReal.ofReal q)
              (ENNReal.ofReal_pos.mpr hq)
          obtain ⟨U, hU, V, hV, hUV⟩ := Filter.eventually_prod_iff.mp hcross_ev
          have heT : Tendsto e atTop (𝓝[>] (0 : ℝ)) := by
            have heT0 : Tendsto e atTop (𝓝 (0 : ℝ)) := by
              change Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 (0 : ℝ))
              exact tendsto_inv_atTop_zero.comp
                (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
            refine tendsto_nhdsWithin_iff.2 ⟨heT0, ?_⟩
            exact Eventually.of_forall (fun n => (he n).1)
          obtain ⟨M, hM⟩ := (eventually_atTop.1 (heT.eventually hV))
          let n : ℕ := max n₀ M
          have hnM : M ≤ n := le_max_right _ _
          have hnn₀ : n₀ ≤ n := le_max_left _ _
          have hpath : P (A \ assemblyConvergencePathTail p n r (L : ℝ)) <
              ENNReal.ofReal q := by
            apply (measure_mono ?_).trans_lt hpath₀
            intro ω hω
            refine ⟨hω.1, ?_⟩
            intro htail
            apply hω.2
            exact assemblyConvergencePathTail_mono_index p hnn₀ r (L : ℝ) htail
          have hεevent : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
              ε ∈ Set.Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT one_pos
          have hEAE : ∀ᵐ ω ∂P, ω ∈ E := by
            filter_upwards [hEae, hGoodAE] with ω hEq hGood
            exact hEq.mpr hGood
          have hEzero : P Eᶜ = 0 := by
            change P {ω | ω ∉ E} = 0
            exact ae_iff.mp hEAE
          have hholder_of_norm : ∀ (g : C(Torus3, ℝ)) (R : ℝ), 0 ≤ R →
              ‖toHolderBesov η g‖ ≤ R →
              holderBesovENorm η g ≤ ENNReal.ofReal R := by
            intro g R hR hnorm
            have htop : holderBesovENorm η g < ⊤ :=
              holderBesovENorm_lt_top η.2.le g
            rw [norm_toHolderBesov] at hnorm
            calc
              holderBesovENorm η g = ENNReal.ofReal
                  (holderBesovENorm η g).toReal :=
                (ENNReal.ofReal_toReal htop.ne).symm
              _ ≤ ENNReal.ofReal R := ENNReal.ofReal_le_ofReal hnorm
          have hFcont : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
              ContinuousOn (fun s => ‖toHolderBesov η (u ε ω s)‖)
                (Set.Icc (0 : ℝ) T) := by
            intro ε hε ω
            exact (classicalSolution_continuousOn η (hclass ε hε ω)).norm.mono
              (Icc_subset_Ici_self)
          let hEfail : Set Ω := Eᶜ
          let hLiftFail : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
              Set Ω := fun ε _ => {ω |
                ¬ Statements.IsModeratePhi43Lift 5 κ (ξ ε ω) (C ε) (Z ε ω) (ψ ε ω)}
          let hLiftFailD : ∀ n : ℕ, Set Ω := fun n =>
            {ω | ¬ Statements.IsModeratePhi43Lift 5 κ (ξ (e n) ω) (C (e n))
              (Zd n ω) (ψd n ω)}
          have hLiftFailZero : ∀ ε (hε : ε ∈ Set.Ioc (0 : ℝ) 1),
              P (hLiftFail ε hε) = 0 := by
            intro ε hε
            simpa only [hLiftFail] using (ae_iff.mp (hZ ε hε))
          have hLiftFailDZero : ∀ n : ℕ, P (hLiftFailD n) = 0 := by
            intro n
            simpa only [hLiftFailD] using (ae_iff.mp (hZd n))
          have hSε : ∀ ε (hε : ε ∈ Set.Ioc (0 : ℝ) 1),
              P {ω | ENNReal.ofReal B₀ <
                Statements.phi43Size κ η H (Z ε ω) (ψ ε ω)} ≤ ENNReal.ofReal q := by
            intro ε hε
            apply (measure_mono ?_).trans (hB ε hε)
            intro ω hω
            exact (ENNReal.ofReal_mono (le_max_left B 1)).trans_lt hω
          have hSd : P {ω | ENNReal.ofReal B₀ <
              Statements.phi43Size κ η H (Zd n ω) (ψd n ω)} ≤ ENNReal.ofReal q := by
            apply (measure_mono ?_).trans (hB (e n) (he n))
            intro ω hω
            exact (ENNReal.ofReal_mono (le_max_left B 1)).trans_lt hω
          have hMε : ∀ (ε : ℝ), U ε → V (e n) → P {ω |
              ENNReal.ofReal d < Statements.phi43Dist κ η H (Z ε ω) (Zd n ω)
                (ψ ε ω) (ψd n ω)} < ENNReal.ofReal q := by
            intro ε hεU hnV
            exact hUV hεU hnV
          have hRbad : P (A \ assemblyConvergencePathTail p n r (L : ℝ)) <
              ENNReal.ofReal q := hpath
          have hεsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), U ε := hU
          filter_upwards [hεsmall, hεevent] with ε hεU hε
          let Bad : Set Ω := {ω |
            ENNReal.ofReal T < τ ω ∧ ∃ t ∈ Set.Icc (0 : ℝ) T,
              δ < ‖toHolderBesov η (u ε ω t) - v ω t‖}
          let Sε : Set Ω := {ω |
            ENNReal.ofReal B₀ < Statements.phi43Size κ η H (Z ε ω) (ψ ε ω)}
          let Sd : Set Ω := {ω |
            ENNReal.ofReal B₀ < Statements.phi43Size κ η H (Zd n ω) (ψd n ω)}
          let Mε : Set Ω := {ω |
            ENNReal.ofReal d < Statements.phi43Dist κ η H (Z ε ω) (Zd n ω)
              (ψ ε ω) (ψd n ω)}
          let Rbad : Set Ω := A \ assemblyConvergencePathTail p n r (L : ℝ)
          have hMε' : P Mε < ENNReal.ofReal q := by
            dsimp [Mε]
            exact hMε ε hεU (hM n hnM)
          have hSε' : P Sε ≤ ENNReal.ofReal q := by
            dsimp [Sε]
            exact hSε ε hε
          have hSd' : P Sd ≤ ENNReal.ofReal q := by
            dsimp [Sd]
            exact hSd
          have hLiftεzero : P (hLiftFail ε hε) = 0 := hLiftFailZero ε hε
          have hBadSub : Bad ⊆
              Sε ∪ Sd ∪ Mε ∪ Rbad ∪ hEfail ∪ hLiftFail ε hε ∪
                hLiftFailD n := by
            intro ω hω
            by_cases hωE : ω ∈ E
            · by_cases hωR : ω ∈ Rbad
              · simp [hωR]
              · have hωA : ω ∈ A := by
                    simpa [A] using (show ω ∈ E ∧ ENNReal.ofReal T < τ ω from
                      ⟨hωE, hω.1⟩)
                have hωtail : ω ∈ assemblyConvergencePathTail p n r (L : ℝ) := by
                  by_contra hnot
                  exact hωR ⟨hωA, hnot⟩
                by_cases hωS : ω ∈ Sε
                · simp [hωS]
                · by_cases hωSd : ω ∈ Sd
                  · simp [hωSd]
                  · by_cases hωM : ω ∈ Mε
                    · simp [hωM]
                    · by_cases hωL : ω ∈ hLiftFail ε hε
                      · simp [hωL]
                      · by_cases hωLd : ω ∈ hLiftFailD n
                        · simp [hωLd]
                        · have hLiftε : Statements.IsModeratePhi43Lift 5 κ
                            (ξ ε ω) (C ε) (Z ε ω) (ψ ε ω) := by
                            exact not_not.mp (by simpa [hLiftFail] using hωL)
                          have hLiftD : Statements.IsModeratePhi43Lift 5 κ
                              (ξ (e n) ω) (C (e n)) (Zd n ω) (ψd n ω) := by
                            exact not_not.mp (by simpa [hLiftFailD] using hωLd)
                          have hsizeε : Statements.phi43Size κ η H (Z ε ω)
                              (ψ ε ω) ≤ ENNReal.ofReal B₀ := by
                            exact le_of_not_gt (by simpa [Sε] using hωS)
                          have hsizeD : Statements.phi43Size κ η H (Zd n ω)
                              (ψd n ω) ≤ ENNReal.ofReal B₀ := by
                            exact le_of_not_gt (by simpa [Sd] using hωSd)
                          have hdist : Statements.phi43Dist κ η H (Z ε ω) (Zd n ω)
                              (ψ ε ω) (ψd n ω) ≤ ENNReal.ofReal d := by
                            exact le_of_not_gt (by simpa [Mε] using hωM)
                          have hF0 : ‖toHolderBesov η (u ε ω 0)‖ < A₀ := by
                            rw [(hclass ε hε ω).initial]
                            exact hx₀A₀
                          have hboundε : ∀ s ∈ Set.Icc (0 : ℝ) T,
                              holderBesovENorm η (u ε ω s) ≤ ENNReal.ofReal A₀ := by
                            intro s hs
                            by_contra hnot
                            have hFbad : ∃ s ∈ Set.Icc (0 : ℝ) T, A₀ ≤
                                ‖toHolderBesov η (u ε ω s)‖ := by
                              refine ⟨s, hs, ?_⟩
                              have hlt : ENNReal.ofReal A₀ <
                                  holderBesovENorm η (u ε ω s) := lt_of_not_ge hnot
                              have htop : holderBesovENorm η (u ε ω s) < ⊤ :=
                                holderBesovENorm_lt_top η.2.le (u ε ω s)
                              have hreal :=
                                (ENNReal.ofReal_lt_iff_lt_toReal
                                  (zero_le_one.trans hA₀) htop.ne).mp hlt
                              simpa [norm_toHolderBesov] using hreal.le
                            obtain ⟨s, hs, hFs, hbefore⟩ :=
                              assembly_exists_first_threshold
                                (hFcont ε hε ω) hF0 hFbad
                            have hnorms : ‖toHolderBesov η (u ε ω s)‖ = A₀ := hFs
                            have hnormD : ‖toHolderBesov η (u (e n) ω s)‖ ≤
                                (L : ℝ) := by
                              have hpt := ContinuousMap.norm_coe_le_norm (p n ω)
                                (⟨s, hs.1, hs.2⟩ : Icc (0 : ℝ) T)
                              have hpt' : ‖xbar n ω s‖ ≤ (L : ℝ) := by
                                have hpt0 : ‖xbar n ω s‖ ≤ ‖p n ω‖ := by
                                  change ‖xbar n ω s‖ ≤ ‖p n ω‖ at hpt
                                  exact hpt
                                exact hpt0.trans (hωtail.2 n le_rfl)
                              simpa [hbarIdent n ω s, ubar, hωE] using hpt'
                            have hδs := hδspec (ξ ε ω) (ξ (e n) ω) (C ε)
                              (C (e n)) (Z ε ω) (Zd n ω) (ψ ε ω) (ψd n ω)
                              u₀ (u ε ω) (u (e n) ω) hLiftε hLiftD
                              (hclass ε hε ω) (hclassd n ω) hsizeε hsizeD hdist s
                              ⟨hs.1, hs.2.trans hTH⟩
                              (fun z hz => ⟨hholder_of_norm _ _ (zero_le_one.trans hA₀)
                                (hbefore z hz),
                                hholder_of_norm _ _ (zero_le_one.trans hA₀) (by
                                  have hpt := ContinuousMap.norm_coe_le_norm (p n ω)
                                    (⟨z, hz.1, hz.2.trans hs.2⟩ : Icc (0 : ℝ) T)
                                  change ‖xbar n ω z‖ ≤ ‖p n ω‖ at hpt
                                  have hpt' := hpt.trans (hωtail.2 n le_rfl)
                                  simpa [hbarIdent n ω z, ubar, hωE] using
                                    hpt'.trans hLA₀)⟩)
                            have hds : dist (toHolderBesov η (u ε ω s))
                                (toHolderBesov η (u (e n) ω s)) ≤ r := by
                              rw [dist_eq_norm, ← toHolderBesov_sub η]
                              rw [norm_toHolderBesov]
                              exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hδs).trans_eq
                                (ENNReal.toReal_ofReal hr.le)
                            have htri : ‖toHolderBesov η (u ε ω s)‖ ≤
                                dist (toHolderBesov η (u ε ω s))
                                  (toHolderBesov η (u (e n) ω s)) +
                                  ‖toHolderBesov η (u (e n) ω s)‖ := by
                              rw [dist_eq_norm] at hds ⊢
                              calc
                                ‖toHolderBesov η (u ε ω s)‖ =
                                    ‖(toHolderBesov η (u ε ω s) -
                                      toHolderBesov η (u (e n) ω s)) +
                                      toHolderBesov η (u (e n) ω s)‖ := by
                                        rw [sub_add_cancel]
                                _ ≤ _ := norm_add_le _ _
                            have hA0L1 : (L : ℝ) + 1 ≤ A₀ := by
                              dsimp [A₀]
                              have hmax : (L : ℝ) ≤ max (L : ℝ) ‖x₀‖ :=
                                le_max_left _ _
                              linarith
                            linarith [htri, hds, hnormD, hA0L1,
                              min_le_left (1 / 4 : ℝ) (δ / 4)]
                          have hboundD : ∀ s ∈ Set.Icc (0 : ℝ) T,
                              holderBesovENorm η (u (e n) ω s) ≤ ENNReal.ofReal A₀ := by
                            intro s hs
                            have hpt := ContinuousMap.norm_coe_le_norm (p n ω)
                              (⟨s, hs.1, hs.2⟩ : Icc (0 : ℝ) T)
                            have hpt' : ‖xbar n ω s‖ ≤ (L : ℝ) := by
                              have hpt0 : ‖xbar n ω s‖ ≤ ‖p n ω‖ := by
                                change ‖xbar n ω s‖ ≤ ‖p n ω‖ at hpt
                                exact hpt
                              exact hpt0.trans (hωtail.2 n le_rfl)
                            have hnorm : ‖toHolderBesov η (u (e n) ω s)‖ ≤ (L : ℝ) := by
                              simpa [hbarIdent n ω s, ubar, hωE] using hpt'
                            exact hholder_of_norm _ _ (zero_le_one.trans hA₀)
                              (hnorm.trans hLA₀)
                          obtain ⟨t, ht, hbad⟩ := hω.2
                          have hδt := hδspec (ξ ε ω) (ξ (e n) ω) (C ε)
                            (C (e n)) (Z ε ω) (Zd n ω) (ψ ε ω) (ψd n ω)
                            u₀ (u ε ω) (u (e n) ω) hLiftε hLiftD
                            (hclass ε hε ω) (hclassd n ω) hsizeε hsizeD hdist t
                            ⟨ht.1, ht.2.trans hTH⟩
                            (fun s hs => ⟨hboundε s ⟨hs.1, hs.2.trans ht.2⟩,
                              hboundD s ⟨hs.1, hs.2.trans ht.2⟩⟩)
                          have hdt : dist (toHolderBesov η (u ε ω t))
                              (toHolderBesov η (u (e n) ω t)) ≤ r := by
                            rw [dist_eq_norm, ← toHolderBesov_sub η, norm_toHolderBesov]
                            exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hδt).trans_eq
                              (ENNReal.toReal_ofReal hr.le)
                          have hstop : Tendsto (fun m => xbar m ω t) atTop
                              (𝓝 (v ω t)) := by
                            have hvalue : v ω t = Classical.choose
                                (cauchySeq_tendsto_of_complete
                                  (hbarCauchy ω t ht.1
                                    ((ENNReal.ofReal_mono ht.2).trans_lt hω.1))) := by
                              dsimp [v, assemblyStoppedLimit]
                              simp [ht.1, (ENNReal.ofReal_mono ht.2).trans_lt hω.1]
                            rw [hvalue]
                            exact Classical.choose_spec
                              (cauchySeq_tendsto_of_complete
                                (hbarCauchy ω t ht.1
                                  ((ENNReal.ofReal_mono ht.2).trans_lt hω.1)))
                          have hnv : dist (xbar n ω t) (v ω t) ≤ r := by
                            apply le_of_tendsto ((tendsto_const_nhds.dist hstop))
                            filter_upwards [eventually_ge_atTop n] with m hm
                            exact (ContinuousMap.dist_le (C := r) hr.le).mp
                              (hωtail.1 n le_rfl m hm)
                              (⟨t, ht.1, ht.2⟩ : Icc (0 : ℝ) T)
                          have hnv' : dist (toHolderBesov η (u (e n) ω t))
                              (v ω t) ≤ r := by
                            simpa [hbarIdent n ω t, ubar, hωE] using hnv
                          have htri : ‖toHolderBesov η (u ε ω t) - v ω t‖ ≤
                              dist (toHolderBesov η (u ε ω t))
                                (toHolderBesov η (u (e n) ω t)) +
                              dist (toHolderBesov η (u (e n) ω t)) (v ω t) := by
                            calc
                              ‖toHolderBesov η (u ε ω t) - v ω t‖ =
                                  ‖(toHolderBesov η (u ε ω t) -
                                    toHolderBesov η (u (e n) ω t)) +
                                    (toHolderBesov η (u (e n) ω t) - v ω t)‖ := by
                                      congr 1
                                      abel
                              _ ≤ ‖toHolderBesov η (u ε ω t) -
                                    toHolderBesov η (u (e n) ω t)‖ +
                                  ‖toHolderBesov η (u (e n) ω t) - v ω t‖ :=
                                norm_add_le _ _
                              _ = _ := by rw [dist_eq_norm, dist_eq_norm]
                          exfalso
                          linarith [hbad, htri, hdt, hnv',
                            min_le_right (1 / 4 : ℝ) (δ / 4)]
            · have hEfailω : ω ∈ hEfail := by
                simpa [hEfail] using hωE
              simp only [Set.mem_union]
              exact Or.inl (Or.inl (Or.inr hEfailω))
          let BadCover : Set Ω := Sε ∪ Sd ∪ Mε ∪ Rbad ∪ hEfail ∪
            hLiftFail ε hε ∪ hLiftFailD n
          have hBadSub' : Bad ⊆ BadCover := by
            simpa [BadCover] using hBadSub
          have hcover_measure : P BadCover ≤
              P Sε + P Sd + P Mε + P Rbad + P hEfail +
                P (hLiftFail ε hε) + P (hLiftFailD n) := by
            calc
              P BadCover ≤ P (Sε ∪ Sd ∪ Mε ∪ Rbad ∪ hEfail ∪
                hLiftFail ε hε) + P (hLiftFailD n) := by
                  simpa [BadCover, Set.union_assoc] using
                    (measure_union_le
                      (Sε ∪ Sd ∪ Mε ∪ Rbad ∪ hEfail ∪ hLiftFail ε hε)
                      (hLiftFailD n))
              _ ≤ (P (Sε ∪ Sd ∪ Mε ∪ Rbad ∪ hEfail) +
                    P (hLiftFail ε hε)) + P (hLiftFailD n) := by
                gcongr
                exact measure_union_le _ _
              _ ≤ ((P (Sε ∪ Sd ∪ Mε ∪ Rbad) + P hEfail) +
                    P (hLiftFail ε hε)) + P (hLiftFailD n) := by
                gcongr
                exact measure_union_le _ _
              _ ≤ (((P (Sε ∪ Sd ∪ Mε) + P Rbad) + P hEfail) +
                    P (hLiftFail ε hε)) + P (hLiftFailD n) := by
                gcongr
                exact measure_union_le _ _
              _ ≤ ((((P (Sε ∪ Sd) + P Mε) + P Rbad) + P hEfail) +
                    P (hLiftFail ε hε)) + P (hLiftFailD n) := by
                gcongr
                exact measure_union_le _ _
              _ ≤ (((((P Sε + P Sd) + P Mε) + P Rbad) + P hEfail) +
                    P (hLiftFail ε hε)) + P (hLiftFailD n) := by
                gcongr
                exact measure_union_le _ _
          have hmeasure : P Bad ≤ ENNReal.ofReal (4 * q) := by
            have hfirst : P Sε + P Sd + P Mε + P Rbad ≤
                ENNReal.ofReal q + ENNReal.ofReal q + ENNReal.ofReal q +
                  ENNReal.ofReal q := by
              exact add_le_add (add_le_add (add_le_add hSε' hSd') hMε'.le)
                hRbad.le
            have hEfailzero : P hEfail = 0 := by
              simpa [hEfail] using hEzero
            have hrest : P hEfail + P (hLiftFail ε hε) + P (hLiftFailD n) ≤
                0 + 0 + 0 := by
              simp [hEfailzero, hLiftεzero, hLiftFailDZero n]
            have hfull : P Sε + P Sd + P Mε + P Rbad + P hEfail +
                  P (hLiftFail ε hε) + P (hLiftFailD n) ≤
                ENNReal.ofReal q + ENNReal.ofReal q + ENNReal.ofReal q +
                  ENNReal.ofReal q + 0 + 0 + 0 := by
              simpa [add_assoc] using add_le_add hfirst hrest
            calc
              P Bad ≤ P BadCover := measure_mono hBadSub'
              _ ≤ P Sε + P Sd + P Mε + P Rbad + P hEfail +
                    P (hLiftFail ε hε) + P (hLiftFailD n) := hcover_measure
              _ ≤ _ := hfull
              _ = ENNReal.ofReal (4 * q) := by
                simp only [add_zero]
                rw [← ENNReal.ofReal_add hq.le hq.le,
                  ← ENNReal.ofReal_add (add_nonneg hq.le hq.le) hq.le,
                  ← ENNReal.ofReal_add
                    (add_nonneg (add_nonneg hq.le hq.le) hq.le) hq.le]
                congr 1
                ring
          have h4qα : 4 * q < α := by
            dsimp [q]
            linarith
          exact hmeasure.trans_lt
            ((ENNReal.ofReal_mono h4qα.le).trans_lt hαb)
  refine ⟨τ, v, hlimit, ?_⟩
  intro ρ' ξ' u' τ' v' hρ' hξ' hu' hlimit'
  let C' : ℝ → RenormalisationConstants :=
    fun ε => (wickConstant ρ' ε + a / 3, sunsetConstant ρ' ε + 0)
  have hclass' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
      IsClassicalSolution (3 * (C' ε).1 - 9 * (C' ε).2)
        (ξ' ε ω) u₀ (u' ε ω) := by
    intro ε hε ω
    rw [show 3 * (C' ε).1 - 9 * (C' ε).2 =
      a + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε by
        dsimp [C']
        ring]
    exact hu' ε hε ω
  have hξsmooth' : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ ω,
      IsSmoothOnSpaceTime (ξ' ε ω) := by
    intro ε hε ω
    exact (hξ' ε hε).1 ω
  obtain ⟨Z', ψ', hZgrowth'⟩ := assembly_selected_lifts_with_growth
    (N := 5) (κ := κ) hG1 hξsmooth' hpotential (C := C')
  have hZsecond : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Statements.IsModeratePhi43Lift 5 κ (ξ' ε ω) (C' ε) (Z' ε ω) (ψ' ε ω) := by
    intro ε hε
    filter_upwards [(hG7growth ρ' hρ' P W hW ξ' hξ' ε hε).2] with ω hg
    exact hZgrowth' ε hε ω hg
  obtain ⟨hG10tight', hG10cross', hG10good'⟩ :=
    hG10 κ hκE 5 (by norm_num) η hη hκη ρ' ρ' hρ' hρ'
      (a / 3, 0)
      P W hW ξ' ξ' hξ' hξ' Z' Z' ψ' ψ' hZsecond hZsecond
  obtain ⟨-, hG10cross12, -⟩ :=
    hG10 κ hκE 5 (by norm_num) η hη hκη ρ ρ' hρ hρ'
      (a / 3, 0)
      P W hW ξ ξ' hξ hξ' Z Z' ψ ψ' hZ' hZsecond
  exact assembly_cross_limit_unique
    (η := η) (κ := κ) (N := 5) (P := P) (u₀ := u₀)
    (u := u) (u' := u') (τ := τ) (τ' := τ') (v := v) (v' := v')
    (ξ := ξ) (ξ' := ξ') (C := C) (C' := C')
    (Z := Z) (Z' := Z') (ψ := ψ) (ψ' := ψ')
    (hStopped := (hG4 κ hκE 5 (by norm_num) η hη hκη).2)
    (hsize := hG10tight) (hsize' := hG10tight')
    (hcross := hG10cross12) (hLift := hZ') (hLift' := hZsecond)
    (hclass := hclass) (hclass' := hclass') hlimit hlimit'

end RegularityStructures.Phi43

end
