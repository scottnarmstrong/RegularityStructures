/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.IsMWTestKernel
public import GlobalPhi43.MW20.Setting.IsMWLocalData
public import GlobalPhi43.MW20.Setting.ParabolicClosedNbhd
public import GlobalPhi43Statements.Defs.ExtNorm
public import Phi43Statements.Defs.IsModeratePhi43ModelOf
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import GlobalPhi43.MW20.Setting.MWInnerCylinder
public import Phi43.Steps.RenormalisedCanonicalModel
public import Phi43.BPHZ.RandomCanonicalModification
public import Phi43.BPHZ.TreeFormulas
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Non-vacuity of the hypotheses of the MW20 estimates

The hypotheses of the local estimates `GlobalPhi43.mw20DefectBound`, `GlobalPhi43.modelTestBound`,
`GlobalPhi43.translationInterface` and `GlobalPhi43.compactSublevel` are jointly satisfiable:

* `mw20DefectBound_hypotheses`: an admissible MW20 test kernel, the product of two normalised
  bumps in `t` and in `x` (`exists_isMWTestKernel`), a local data set (the zero data) and a radius.
* `modelTestBound_hypotheses`: a model of the moderate canonical predicate (Theorem A's canonical model of
  the zero noise), a compact set and base point, a scale, a test, and a negative symbol (the noise `Ξ`)
  whose realisation is a continuous function of polynomial growth.
* `translationInterface_hypotheses`: the predicate of clauses (ii)–(iii) is satisfiable (clause (i) has no
  hypotheses beyond its carriers).
* `compactSublevel_hypotheses`: exponents `η ≤ β < η'' < 0`.

Non-degenerate instances, so that no hypothesis is satisfied only by zero data:
* `mw20DefectBound_nondegenerate`: the admissible kernel with the local data `u = 1, ζ = 1, J = t, Y = Z = 0,
  e₁ = 0, e₂ = −t², e₃ = −t³, C₁ = C₂ = 0`, for which `u − J ≠ 0` on `P_{1/2}`.
* `modelTestBound_nondegenerate` (and the predicate of `translationInterface`): a bump test `φ` with `φ 0 = 1`, the constant-one
  noise with its canonical model and noise growth, and the symbol `Ξ` realised by `f = 1`.

No `sorry`: every declaration here uses only the standard axioms.
-/

public section

open MeasureTheory Set Metric
open scoped ContDiff
open RegularityStructures RegularityStructures.Phi43

namespace GlobalPhi43.NonVacuity

/-- An admissible MW20 test kernel exists: `Φ(t, x) = a(t) b(x)` with normalised bumps `a` on `ℝ` (centre `-1/2`,
radii `1/4, 1/3`) and `b` on `ℝ³` (centre `0`, radii `4/5, 9/10`). -/
theorem exists_isMWTestKernel : ∃ Φ : ParabolicSpace → ℝ, IsMWTestKernel Φ := by
  let a : ContDiffBump (-(1 / 2) : ℝ) := ⟨1 / 4, 1 / 3, by norm_num, by norm_num⟩
  let b : ContDiffBump (0 : Fin 3 → ℝ) := ⟨4 / 5, 9 / 10, by norm_num, by norm_num⟩
  let A := a.normed volume
  let B := b.normed volume
  have hA : ∀ t, A t ≤ 2 := fun t => by
    have h := a.normed_le_div_measure_closedBall_rIn volume t
    rw [Measure.real, Real.volume_closedBall] at h
    have : ENNReal.toReal (ENNReal.ofReal (2 * (1 / 4 : ℝ))) = 1 / 2 := by norm_num
    simp only [a] at h
    rw [this] at h
    linarith
  have hB : ∀ x, B x ≤ 1 / 4 := fun x => by
    have h := b.normed_le_div_measure_closedBall_rIn volume x
    rw [Measure.real, Real.volume_pi_closedBall _ (by norm_num : (0 : ℝ) ≤ 4 / 5)] at h
    simp only [Fintype.card_fin, b] at h
    rw [ENNReal.toReal_ofReal (by norm_num)] at h
    have : (1 : ℝ) / (2 * (4 / 5)) ^ 3 ≤ 1 / 4 := by norm_num
    linarith
  refine ⟨fun z => A z.1 * B z.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((a.contDiff_normed (μ := volume) (n := ⊤)).comp contDiff_fst).mul
      ((b.contDiff_normed (μ := volume) (n := ⊤)).comp contDiff_snd)
  · intro z hz
    have hz' : z ∈ tsupport A ×ˢ tsupport B := by
      have hsub : Function.support (fun z : ParabolicSpace => A z.1 * B z.2) ⊆
          Function.support A ×ˢ Function.support B := by
        intro w hw
        simp only [Function.mem_support, ne_eq] at hw ⊢
        exact ⟨fun h => hw (by simp [h]), fun h => hw (by simp [h])⟩
      have := closure_mono hsub hz
      rw [closure_prod_eq] at this
      exact this
    rw [a.tsupport_normed_eq, b.tsupport_normed_eq] at hz'
    obtain ⟨h1, h2⟩ := hz'
    simp only [mem_closedBall, Real.dist_eq, dist_zero_right] at h1 h2
    simp only [a, b] at h1 h2
    have ht1 : z.1 < 0 := by linarith [(abs_le.1 h1).2]
    have ht2 : -1 < z.1 := by linarith [(abs_le.1 h1).1]
    refine ⟨?_, by simpa using ht1⟩
    simp only [parabolicDist, zero_sub, Prod.fst_zero, Prod.snd_zero, norm_neg]
    refine max_lt ?_ (by linarith)
    rw [abs_neg, abs_of_neg ht1]
    calc √(-z.1) < √1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
      _ = 1 := Real.sqrt_one
  · intro z
    refine ⟨mul_nonneg (a.nonneg_normed _) (b.nonneg_normed _), ?_⟩
    calc A z.1 * B z.2 ≤ 2 * (1 / 4) :=
          mul_le_mul (hA _) (hB _) (b.nonneg_normed _) (by norm_num)
      _ ≤ 1 := by norm_num
  · have h := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin 3 → ℝ))) A B
    rw [a.integral_normed, b.integral_normed, mul_one] at h
    rw [← h]
    rfl
  · intro z
    change A z.1 * b.normed volume (-z.2) = A z.1 * b.normed volume z.2
    rw [b.normed_neg]

/-- The zero data form an MW20-D local data set. -/
theorem isMWLocalData_zero : IsMWLocalData 0 0 0 0 0 0 0 0 0 0 := by
  have hL : ∀ z, heatOperator (0 : ParabolicSpace → ℝ) z = 0 := fun z => by
    simp [heatOperator]
  refine ⟨⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩, contDiff_const, contDiff_const,
    contDiff_const, contDiff_const, contDiff_const, contDiff_const, contDiff_const, ?_, ?_⟩
  · intro z _; simp [hL]
  · intro z _; simp [hL]

/-- `mw20DefectBound`: its hypotheses are satisfiable. -/
theorem mw20DefectBound_hypotheses :
    ∃ Φ : ParabolicSpace → ℝ, IsMWTestKernel Φ ∧
      ∃ (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ),
        IsMWLocalData u ζ J Y Z e₁ e₂ e₃ C₁ C₂ ∧ (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_isMWTestKernel
  exact ⟨Φ, hΦ, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, isMWLocalData_zero, by norm_num, by norm_num⟩

/-- Theorem A's canonical model of the zero noise satisfies the moderate canonical predicate for `f₀ = 0`. -/
theorem exists_isModeratePhi43ModelOf_zero (N : ℕ) (κ : Kappa) (C : RenormalisationConstants) :
    ∃ Z : Model (phi43RegularityStructure κ) parabolicSemigroup,
      RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ 0 C Z ∧
      RegularityStructures.Phi43.Statements.IsModerateRenormalisedCanonicalModel N κ zeroCanonicalNoise C Z := by
  obtain ⟨⟨Z, hZ⟩, -⟩ := renormalisedCanonicalModel_existsUnique N κ zeroCanonicalNoise 0 0
    (fun k _ z => by simp [zeroCanonicalNoise]) C
  exact ⟨Z, ⟨zeroCanonicalNoise, fun _ => rfl, hZ⟩, hZ⟩

/-- `modelTestBound`: its hypotheses are satisfiable, with `τ = Ξ` (degree `-5/2 - κ < 0`) and its
realisation `f = 0`. -/
theorem modelTestBound_hypotheses (N : ℕ) (κ : Kappa) :
    ∃ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ f₀ C Z ∧
      RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f₀ ∧
      ∃ (S : Set ParabolicSpace) (x : ParabolicSpace) (T : ℝ) (φ : ParabolicSpace → ℝ) (τ : Symbol)
        (f : ParabolicSpace → ℝ),
        IsCompact S ∧ x ∈ S ∧ T ∈ Ioc (0 : ℝ) 1 ∧ ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        tsupport φ ⊆ parabolicClosedNbhd {0} 1 ∧ (phi43RegularityStructure κ).deg τ < 0 ∧
        Continuous f ∧ (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) ∧
        ∀ r : ℝ, 0 < r → ∀ y, Z.regPi x (Pi.single τ 1) r y = parabolicSemigroup.apply r f y := by
  obtain ⟨Z, hZ, hZ'⟩ := exists_isModeratePhi43ModelOf_zero N κ (0, 0)
  refine ⟨0, (0, 0), Z, hZ, ⟨0, 0, fun k _ z => by simp⟩, {0}, 0, 1, 0, .noise, 0, isCompact_singleton, rfl, ⟨by norm_num, le_rfl⟩,
    contDiff_const, HasCompactSupport.zero, by simp, ?_, continuous_const, ⟨0, 0, fun z => by simp⟩, ?_⟩
  · change -5 / 2 - κ.1 < 0
    linarith [κ.2.1]
  · intro r hr y
    rw [hZ'.2.1 .noise ((mem_fMinus_iff_isFMinus _).2 trivial) 0 r hr y, CanonicalData.renormalisedPi_basis_noise_eq]
    rfl

/-- `translationInterface`: the predicate assumed in clauses (ii) and (iii) is satisfiable. -/
theorem translationInterface_hypotheses (N : ℕ) (κ : Kappa) :
    ∃ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ f C Z := by
  obtain ⟨Z, hZ, -⟩ := exists_isModeratePhi43ModelOf_zero N κ (0, 0)
  exact ⟨0, (0, 0), Z, hZ⟩

/-- `compactSublevel`: admissible exponents `η ≤ β < η'' < 0` exist. -/
theorem compactSublevel_hypotheses :
    ∃ η β η'' : NegExponent, (η : ℝ) ≤ β ∧ (β : ℝ) < η'' :=
  ⟨⟨-(3 / 5), by norm_num⟩, ⟨-(4 / 7), by norm_num⟩, ⟨-(5 / 9), by norm_num⟩, by norm_num, by norm_num⟩

/-- The heat operator of a constant is zero. -/
theorem heatOperator_const (c : ℝ) (z : ParabolicSpace) : heatOperator (fun _ => c) z = 0 := by
  simp [heatOperator]

/-- The heat operator of the time coordinate is one. -/
theorem heatOperator_fst (z : ParabolicSpace) : heatOperator (fun w : ParabolicSpace => w.1) z = 1 := by
  have h : ∀ w : ParabolicSpace, fderiv ℝ (fun w : ParabolicSpace => w.1) w = ContinuousLinearMap.fst ℝ ℝ _ :=
    fun w => fderiv_fst
  simp [heatOperator, h]

/-- A non-zero MW20-D local data set: `u = 1, ζ = 1, J = t, Y = Z = 0, e₁ = 0, e₂ = −t², e₃ = −t³`. -/
theorem isMWLocalData_nonzero :
    IsMWLocalData (fun _ => 1) (fun _ => 1) (fun w => w.1) 0 0 0 (fun w => -w.1 ^ 2) (fun w => -w.1 ^ 3) 0 0 := by
  have h0 : ∀ z, heatOperator (0 : ParabolicSpace → ℝ) z = 0 := fun z => heatOperator_const 0 z
  refine ⟨⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩, contDiff_const, contDiff_fst, contDiff_const,
    contDiff_const, contDiff_const, contDiff_fst.pow 2 |>.neg, contDiff_fst.pow 3 |>.neg, ?_, ?_⟩
  · intro z _
    rw [heatOperator_const]; norm_num
  · intro z _
    refine ⟨?_, ?_, ?_⟩
    · rw [heatOperator_fst]; simp
    · rw [h0]; simp
    · rw [h0]; simp

/-- `mw20DefectBound`, non-degenerate: an admissible kernel and the non-zero local data, with `u − J ≠ 0` on `P_{1/2}`. -/
theorem mw20DefectBound_nondegenerate :
    ∃ Φ : ParabolicSpace → ℝ, IsMWTestKernel Φ ∧
      IsMWLocalData (fun _ => 1) (fun _ => 1) (fun w => w.1) 0 0 0 (fun w => -w.1 ^ 2) (fun w => -w.1 ^ 3) 0 0 ∧
      ∃ z ∈ mwInnerCylinder (1 / 2), (fun _ => (1 : ℝ)) z - z.1 ≠ 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_isMWTestKernel
  refine ⟨Φ, hΦ, isMWLocalData_nonzero, ((1 / 2 : ℝ), 0), ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩, by norm_num⟩

/-- The constant-one noise. -/
def oneCanonicalNoise : CanonicalNoise where
  zeta := fun _ => 1
  smooth := contDiff_const
  periodic := fun _ _ => rfl

/-- The constant-one noise has polynomial growth (its derivatives of order `1, …, 4` vanish). -/
theorem one_growth : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k (fun _ : ParabolicSpace => (1 : ℝ)) z‖ ≤ 1 * (1 + parabolicNorm z) ^ 0 := by
  intro k _ z
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hk.ne']; simp

/-- `modelTestBound`, non-degenerate (and the predicate of `translationInterface`): the constant-one noise with its canonical model and noise
growth, a bump test `φ` with `φ 0 = 1`, and `Ξ` realised by `f = 1 ≠ 0`. -/
theorem modelTestBound_nondegenerate (N : ℕ) (κ : Kappa) :
    ∃ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      RegularityStructures.Phi43.Statements.IsModeratePhi43ModelOf N κ f₀ C Z ∧
      RegularityStructures.Phi43.Statements.HasPhi43NoiseGrowth f₀ ∧
      ∃ (φ : ParabolicSpace → ℝ) (f : ParabolicSpace → ℝ),
        ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ parabolicClosedNbhd {0} 1 ∧ φ 0 = 1 ∧
        (phi43RegularityStructure κ).deg Symbol.noise < 0 ∧
        Continuous f ∧ (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) ∧ f 0 = 1 ∧
        ∀ x : ParabolicSpace, ∀ r : ℝ, 0 < r → ∀ y,
          Z.regPi x (Pi.single Symbol.noise 1) r y = parabolicSemigroup.apply r f y := by
  obtain ⟨⟨Z, hZ⟩, -⟩ := renormalisedCanonicalModel_existsUnique N κ oneCanonicalNoise 1 0
    (fun k hk z => one_growth k hk z) (0, 0)
  let b : ContDiffBump (0 : ParabolicSpace) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨fun _ => 1, (0, 0), Z, ⟨oneCanonicalNoise, fun _ => rfl, hZ⟩, ⟨1, 0, fun k hk z => one_growth k hk z⟩,
    b, fun _ => 1, b.contDiff, b.hasCompactSupport, ?_, b.one_of_mem_closedBall (by simp [b]), ?_,
    continuous_const, ⟨1, 0, fun z => by simp⟩, rfl, ?_⟩
  · rw [b.tsupport_eq]
    intro w hw
    refine ⟨0, rfl, ?_⟩
    simp only [mem_closedBall, dist_zero_right, b] at hw
    have h1 : |w.1| ≤ 1 := (norm_fst_le w).trans hw
    have h2 : ‖w.2‖ ≤ 1 := (norm_snd_le w).trans hw
    simp only [parabolicDist, Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg, norm_neg]
    refine max_le ?_ h2
    calc √|w.1| ≤ √1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  · change -5 / 2 - κ.1 < 0
    linarith [κ.2.1]
  · intro x r hr y
    rw [hZ.2.1 .noise ((mem_fMinus_iff_isFMinus _).2 trivial) x r hr y,
      CanonicalData.renormalisedPi_basis_noise_eq]
    rfl

end GlobalPhi43.NonVacuity

end
