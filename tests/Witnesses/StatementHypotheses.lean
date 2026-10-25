/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Steps.KolmogorovModelNorm
public import Phi43Statements.Steps.NoiseCauchy
public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsPhi43Lift
public import Phi43Statements.WhiteNoiseExists
public import Phi43Statements.RegularisedNoiseExistsUnique
public import Phi43Statements.ClassicalWellPosed
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Satisfiability of the hypotheses of Theorem A and its steps

Term-level witnesses that the hypotheses of Theorem A and of the intermediate statements
`Statements.*` are jointly satisfiable, so that none of them holds vacuously.

* **Section A** uses only the definitions and the preliminary statements (W1), (W2) of Lemma 4.1
  of the statement.
* **Section B** applies the Kolmogorov bound for the model norms, `Statements.kolmogorov_modelNorm`,
  to the zero model.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace RegularityStructures.Phi43.Witnesses

/-! ## A. Parameters, noises and mollifiers -/

/-- The exclusion set `E` is countable. -/
theorem excludedKappa_countable :
    Set.Countable RegularityStructures.Phi43.Statements.excludedKappa := by
  refine (Set.countable_range
    (fun p : ℕ × ℕ × ℤ => ((p.2.2 : ℝ) / 2 - (p.2.1 : ℝ)) / (p.1 : ℝ))).mono ?_
  rintro q ⟨⟨b, -, n, -, m, rfl⟩, -⟩
  exact ⟨(b, n, m), rfl⟩

/-- **Admissible parameters.** For every `η < -1/2` there is `κ : Kappa` with `κ ∉ E` and
`κ < -1/2 - η`, as required by `Statements.phi43ClassicalSolution_stoppedContinuity`,
`Statements.bphzModels_cauchy` and `Statements.phi43GModels_convergence`. -/
theorem exists_kappa (η : ℝ) (hη : η < -(1 / 2 : ℝ)) :
    ∃ κ : RegularityStructures.Phi43.Kappa,
      κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa ∧ κ.1 < -(1 / 2 : ℝ) - η := by
  have hlt : (0 : ℝ) < min (1 / 16) (-(1 / 2 : ℝ) - η) := lt_min (by norm_num) (by linarith)
  obtain ⟨k, hk, hk0, hk1⟩ :=
    (excludedKappa_countable.dense_compl ℝ).exists_between hlt
  exact ⟨⟨k, hk0, lt_of_lt_of_le hk1 (min_le_left _ _)⟩, hk,
    lt_of_lt_of_le hk1 (min_le_right _ _)⟩

/-- The zero noise as a `CanonicalNoise`. -/
def zeroNoise : RegularityStructures.Phi43.CanonicalNoise where
  zeta _ := 0
  smooth := contDiff_const
  periodic _ _ := rfl

/-- The zero noise satisfies the growth premise `hg` of
`Statements.renormalisedCanonicalModel_existsUnique` (with `Cg = 0`, `q = 0`). -/
theorem zeroNoise_growth : ∀ k : ℕ, k ≤ 4 → ∀ z : RegularityStructures.ParabolicSpace,
    ‖iteratedFDeriv ℝ k zeroNoise.zeta z‖ ≤ 0 * (1 + RegularityStructures.parabolicNorm z) ^ 0 := by
  intro k _ z
  simp [zeroNoise, iteratedFDeriv_fun_zero]

/-- The hypothesis `η < 0` of `Statements.closureNorm_equiv_littlewoodPaley` is satisfiable
(nondegeneracy, for example at `f = 1`, is a property of the norms, not of the hypotheses). -/
theorem closureNorm_hypotheses : ∃ η : ℝ, η < 0 := ⟨-1, by norm_num⟩

/-- The zero noise is smooth. -/
theorem isSmoothOnSpaceTime_zero :
    RegularityStructures.IsSmoothOnSpaceTime (fun _ => 0) := by
  unfold RegularityStructures.IsSmoothOnSpaceTime
  exact contDiff_const

/-- The growth predicate holds for the zero noise. -/
theorem hasPhi43NoiseGrowth_zero : RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth (fun _ => 0) :=
  ⟨0, 0, fun k _ z => by simp⟩

/-- The potential predicate is consistent: `ψ = 0` is the potential of `f = 0`. -/
theorem isMassivePotential_zero :
    RegularityStructures.IsMassivePotential (fun _ => 0) (fun _ => 0) :=
  ⟨fun t x => by simp, fun t x => by simp⟩

/-- The conclusion of the first part of `Statements.phi43Noise_cauchy` is satisfiable: the zero potential is smooth and continuous. -/
theorem zeroPotential_smooth_continuous :
    RegularityStructures.IsSmoothOnSpaceTime
        (fun z : RegularityStructures.SpaceTime =>
          (fun _ : ℝ => (0 : C(RegularityStructures.Torus3, ℝ))) z.1 z.2) ∧
      Continuous (fun _ : ℝ => (0 : C(RegularityStructures.Torus3, ℝ))) :=
  ⟨by simpa using isSmoothOnSpaceTime_zero, continuous_const⟩

/-- **No junk potentials.** If the massive heat integral diverges at some point, no `ψ` (in
particular not `ψ = 0`) is a potential of `f`. -/
theorem not_isMassivePotential_of_not_integrable (f : RegularityStructures.SpaceTime → ℝ)
    (t : ℝ) (x : RegularityStructures.Torus3)
    (h : ¬ Integrable (fun w : RegularityStructures.SpaceTime =>
      RegularityStructures.massiveHeatKernel ((t, x) - w) * f w))
    (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) :
    ¬ RegularityStructures.IsMassivePotential f ψ :=
  fun hψ => h (hψ.1 t x)

/-- The mollifier hypotheses are satisfiable: a normalised smooth bump is a mollifier. -/
theorem exists_mollifier :
    ∃ ρ : RegularityStructures.ParabolicSpace → ℝ, RegularityStructures.Phi43.IsMollifier ρ := by
  let f : ContDiffBump (0 : ℝ × (Fin 3 → ℝ)) := ⟨1, 2, by norm_num, by norm_num⟩
  exact ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed, f.integral_normed⟩⟩

/-- The noise hypotheses are satisfiable: a white noise and, for every mollifier, a family of
regularised noises indexed by `ε ∈ (0, 1]` exist (Lemma 4.1 (W1), (W2)). -/
theorem exists_regularisedNoise_family :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (W : (RegularityStructures.SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ RegularityStructures.IsWhiteNoise P W ∧
      ∀ ρ : RegularityStructures.ParabolicSpace → ℝ, RegularityStructures.Phi43.IsMollifier ρ →
        ∃ ξ : ℝ → Ω → RegularityStructures.SpaceTime → ℝ,
          ∀ ε ∈ Set.Ioc (0 : ℝ) 1, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε (ξ ε) := by
  classical
  obtain ⟨Ω, mΩ, P, W, hP, hW⟩ := RegularityStructures.Phi43.Statements.exists_whiteNoise
  refine ⟨Ω, mΩ, P, W, hP, hW, fun ρ hρ => ?_⟩
  have h : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∃ ξ, RegularityStructures.Phi43.IsRegularisedNoise P W ρ ε ξ :=
    fun ε hε => (RegularityStructures.Phi43.Statements.regularisedNoise_exists_unique P W hW ρ hρ hε).1
  exact ⟨fun ε => if hε : ε ∈ Set.Ioc (0 : ℝ) 1 then (h ε hε).choose else fun _ _ => 0,
    fun ε hε => by simpa only [hε, ↓reduceDIte] using (h ε hε).choose_spec⟩

/-- Theorem A's counterterm is the counterterm `3 C₁ - 9 C₂` of
`Statements.phi43ClassicalSolution_stoppedContinuity` for the constants `(C₁^ε + a/3, C₂^ε)` that
`Statements.phi43GModels_convergence` uses with `c = (a/3, 0)`. -/
theorem counterterm_eq (a w s : ℝ) :
    a + 3 * w - 9 * s =
      3 * ((w + a / 3, s + 0) : ℝ × ℝ).1 - 9 * ((w + a / 3, s + 0) : ℝ × ℝ).2 := by
  simp only
  ring

/-! ## B. The Kolmogorov bound for the model norms on the zero model -/

def unitStructure : RegularityStructures.RegularityStructure Unit where
  deg _ := 0
  group := ⊥
  isGradedUnipotent g hg := by
    rw [Subgroup.mem_bot] at hg
    subst hg
    exact fun _ => by simp

/-- The zero model `Π = 0`, `Γ = 1`. -/
def zeroModel : RegularityStructures.Model unitStructure RegularityStructures.parabolicSemigroup where
  pi _ := 0
  gamma _ _ := 1
  pi_gamma _ _ _ := rfl
  gamma_self _ := rfl
  gamma_mul _ _ _ := mul_one 1
  measurable_diag _ _ _ := by simp
  measurable_pi _ _ _ _ := by simpa using (measurable_zero : Measurable (0 :
    RegularityStructures.ParabolicSpace → ℝ))

/-- The hypotheses of `Statements.kolmogorov_modelNorm` can be discharged for every moment order
`q` it chooses: it applies to the deterministic pair `Z₁ = Z₂ = 0` with no pathwise exemption
(`Dπ = DΓ = ∅`), so the moment hypotheses (at all base points) are the ones exercised. -/
theorem kolmogorov_modelNorm_applies_zeroModel (S : Set RegularityStructures.ParabolicSpace) (hS : IsCompact S) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∫⁻ _ : Unit, zeroModel.normOn 1 S ^ 1 ∂(Measure.dirac ()) ≤ ENNReal.ofReal (K * 1 ^ 1) := by
  obtain ⟨q, -, hq⟩ := RegularityStructures.Phi43.Statements.kolmogorov_modelNorm unitStructure 1 1 0
    one_pos le_rfl ∅ ∅ S hS 1 le_rfl
  obtain ⟨K, hK, h⟩ := hq 1
  have hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn
      (fun _ : Unit => zeroModel) S :=
    ⟨⟨fun _ _ _ _ => measurable_const, fun _ _ _ _ => measurable_const,
      fun _ _ => continuousOn_const, fun _ _ _ => continuousOn_const⟩,
      fun _ _ _ => continuousOn_const⟩
  have hpi : ∀ (x : RegularityStructures.ParabolicSpace) (τ : Unit → ℝ) (t : ℝ)
      (z : RegularityStructures.ParabolicSpace), zeroModel.regPi x τ t z = 0 :=
    fun _ _ _ _ => rfl
  have h0 : ∀ a : ℝ≥0∞, (0 : ℝ≥0∞) ^ q ≤ a ^ q := fun _ => pow_le_pow_left₀ le_rfl zero_le q
  have key := h (Measure.dirac ()) (fun _ => zeroModel) (fun _ => zeroModel) 1 0
    zero_le_one le_rfl le_rfl hZ hZ
  obtain ⟨hpair, -⟩ := key (by simp) (by simp) (by simp) (by simp)
    (by
      intro Z hZm i _ _ t _ x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at hZm
      subst hZm
      simp only [hpi, enorm_zero, MeasureTheory.lintegral_dirac]
      exact h0 _)
    (by
      intro i _ _ t _ x
      simp only [hpi, sub_self, enorm_zero, MeasureTheory.lintegral_dirac]
      exact h0 _)
    (by
      intro Z _ i j _ _ hij
      exact absurd hij (lt_irrefl _))
    (by
      intro i j _ _ hij
      exact absurd hij (lt_irrefl _))
  exact ⟨K, hK, (hpair _ (Set.mem_insert _ _)).2⟩


end RegularityStructures.Phi43.Witnesses

end
