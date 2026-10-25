/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

/-!
# Gaussian coefficient sequences

The product of standard centred Gaussian laws supplies independent coordinates.  The finite
linear-combination facts in this file are the concrete input for the isonormal construction in
`RegularityStructures.Probability.Isonormal`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace RegularityStructures

abbrev GaussianSequenceSpace (ι : Type*) := ι → ℝ

noncomputable def standardGaussianReal : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (1 : ℝ≥0)

instance instIsProbabilityMeasure_standardGaussianReal :
    IsProbabilityMeasure standardGaussianReal := by
  rw [standardGaussianReal]
  infer_instance

noncomputable def gaussianSequenceMeasure (ι : Type*) :
    Measure (GaussianSequenceSpace ι) :=
  Measure.infinitePi fun _ : ι => standardGaussianReal

instance instIsProbabilityMeasure_gaussianSequenceMeasure (ι : Type*) :
    IsProbabilityMeasure (gaussianSequenceMeasure ι) := by
  rw [gaussianSequenceMeasure]
  infer_instance

def gaussianCoordinate {ι : Type*} (i : ι) : GaussianSequenceSpace ι → ℝ :=
  fun ω => ω i

@[fun_prop]
theorem measurable_gaussianCoordinate {ι : Type*} (i : ι) :
    Measurable (gaussianCoordinate i) := by
  change Measurable (fun ω : GaussianSequenceSpace ι => ω i)
  exact measurable_pi_apply i

theorem aemeasurable_gaussianCoordinate {ι : Type*} (i : ι) :
    AEMeasurable (gaussianCoordinate i) (gaussianSequenceMeasure ι) :=
  (measurable_gaussianCoordinate i).aemeasurable

theorem gaussianCoordinate_hasLaw {ι : Type*} (i : ι) :
    HasLaw (gaussianCoordinate i) standardGaussianReal (gaussianSequenceMeasure ι) := by
  exact MeasurePreserving.hasLaw
    (measurePreserving_eval_infinitePi (fun _ : ι => standardGaussianReal) i)

theorem identDistrib_gaussianCoordinate_id {ι : Type*} (i : ι) :
    IdentDistrib (gaussianCoordinate i) id (gaussianSequenceMeasure ι) standardGaussianReal where
  aemeasurable_fst := aemeasurable_gaussianCoordinate i
  aemeasurable_snd := aemeasurable_id'
  map_eq := by
    rw [(gaussianCoordinate_hasLaw i).map_eq]
    exact Measure.map_id.symm

theorem memLp_gaussianCoordinate {ι : Type*} (i : ι) :
    MemLp (gaussianCoordinate i) 2 (gaussianSequenceMeasure ι) := by
  have hdist := identDistrib_gaussianCoordinate_id (ι := ι) i
  exact hdist.symm.memLp_snd
    (ProbabilityTheory.memLp_id_gaussianReal' (μ := 0) (v := (1 : ℝ≥0)) 2 (by norm_num))

theorem integral_gaussianCoordinate {ι : Type*} (i : ι) :
    ∫ ω, gaussianCoordinate i ω ∂gaussianSequenceMeasure ι = 0 := by
  calc
    ∫ ω, gaussianCoordinate i ω ∂gaussianSequenceMeasure ι =
        ∫ x, x ∂standardGaussianReal := (gaussianCoordinate_hasLaw i).integral_eq
    _ = 0 := by
      rw [standardGaussianReal]
      simp

theorem variance_gaussianCoordinate {ι : Type*} (i : ι) :
    Var[gaussianCoordinate i; gaussianSequenceMeasure ι] = 1 := by
  calc
    Var[gaussianCoordinate i; gaussianSequenceMeasure ι] =
        Var[id; standardGaussianReal] := (gaussianCoordinate_hasLaw i).variance_eq
    _ = 1 := by
      rw [standardGaussianReal]
      simp

theorem map_const_mul_gaussianCoordinate {ι : Type*} (i : ι) (c : ℝ) :
    Measure.map (fun ω => c * gaussianCoordinate i ω) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal (c ^ (2 : Nat))) := by
  change Measure.map ((fun x : ℝ => c * x) ∘ gaussianCoordinate i)
      (gaussianSequenceMeasure ι) =
    ProbabilityTheory.gaussianReal 0 (Real.toNNReal (c ^ (2 : Nat)))
  have hmul_meas :
      AEMeasurable (fun x : ℝ => c * x)
        (Measure.map (gaussianCoordinate i) (gaussianSequenceMeasure ι)) := by
    rw [(gaussianCoordinate_hasLaw i).map_eq]
    fun_prop
  rw [← AEMeasurable.map_map_of_aemeasurable
    hmul_meas (aemeasurable_gaussianCoordinate i)]
  rw [(gaussianCoordinate_hasLaw i).map_eq, standardGaussianReal,
    ProbabilityTheory.gaussianReal_map_const_mul]
  congr
  · ring
  · apply NNReal.coe_injective
    simp [Real.coe_toNNReal _ (sq_nonneg c)]

theorem iIndepFun_gaussianCoordinate {ι : Type*} :
    iIndepFun (fun i : ι => gaussianCoordinate i) (gaussianSequenceMeasure ι) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    exact measurable_gaussianCoordinate i)]
  change Measure.map id (gaussianSequenceMeasure ι) =
    Measure.infinitePi fun i : ι => Measure.map (gaussianCoordinate i) (gaussianSequenceMeasure ι)
  rw [Measure.map_id, gaussianSequenceMeasure]
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi (fun _ : ι => standardGaussianReal) i).map_eq).symm

theorem indepFun_gaussianCoordinate {ι : Type*} {i j : ι} (hij : i ≠ j) :
    gaussianCoordinate i ⟂ᵢ[gaussianSequenceMeasure ι] gaussianCoordinate j :=
  iIndepFun_gaussianCoordinate.indepFun hij

theorem covariance_gaussianCoordinate_eq_zero {ι : Type*} {i j : ι} (hij : i ≠ j) :
    cov[gaussianCoordinate i, gaussianCoordinate j; gaussianSequenceMeasure ι] = 0 :=
  (indepFun_gaussianCoordinate hij).covariance_eq_zero
    (memLp_gaussianCoordinate i) (memLp_gaussianCoordinate j)

theorem covariance_gaussianCoordinate_self {ι : Type*} (i : ι) :
    cov[gaussianCoordinate i, gaussianCoordinate i; gaussianSequenceMeasure ι] = 1 := by
  rw [covariance_self (aemeasurable_gaussianCoordinate i), variance_gaussianCoordinate i]

theorem covariance_gaussianCoordinate {ι : Type*} [DecidableEq ι] (i j : ι) :
    cov[gaussianCoordinate i, gaussianCoordinate j; gaussianSequenceMeasure ι] =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [covariance_gaussianCoordinate_self]
  · simp [hij, covariance_gaussianCoordinate_eq_zero hij]

noncomputable def gaussianLinearCombination {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    GaussianSequenceSpace ι → ℝ :=
  fun ω => ∑ i ∈ s, a i * gaussianCoordinate i ω

@[fun_prop]
theorem measurable_gaussianLinearCombination {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    Measurable (gaussianLinearCombination s a) := by
  unfold gaussianLinearCombination
  fun_prop

theorem aemeasurable_gaussianLinearCombination {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    AEMeasurable (gaussianLinearCombination s a) (gaussianSequenceMeasure ι) :=
  (measurable_gaussianLinearCombination s a).aemeasurable

theorem indepFun_gaussianCoordinate_gaussianLinearCombination {ι : Type*} [DecidableEq ι]
    {i : ι} {s : Finset ι} (his : i ∉ s) (a : ι → ℝ) :
    gaussianCoordinate i ⟂ᵢ[gaussianSequenceMeasure ι] gaussianLinearCombination s a := by
  let S : Finset ι := {i}
  have hdisjoint : Disjoint S s := by
    rw [Finset.disjoint_left]
    intro j hj hjs
    have hji : j = i := by simpa [S] using hj
    exact his (hji ▸ hjs)
  have htuple :
      (fun ω (j : S) => gaussianCoordinate (j : ι) ω)
        ⟂ᵢ[gaussianSequenceMeasure ι]
      (fun ω (j : s) => gaussianCoordinate (j : ι) ω) :=
    iIndepFun_gaussianCoordinate.indepFun_finset S s hdisjoint
      (fun j => measurable_gaussianCoordinate j)
  let φ : ((j : S) → ℝ) → ℝ := fun x => x ⟨i, by simp [S]⟩
  let ψ : ((j : s) → ℝ) → ℝ := fun x => ∑ j : s, a j * x j
  have hφ : Measurable φ := by
    change Measurable (fun x : (j : S) → ℝ => x ⟨i, by simp [S]⟩)
    exact measurable_pi_apply _
  have hψ : Measurable ψ := by
    change Measurable (fun x : (j : s) → ℝ => ∑ j : s, a j * x j)
    fun_prop
  have hcomp := htuple.comp hφ hψ
  convert hcomp using 1 <;> ext ω
  · rfl
  · change (∑ x ∈ s, a x * ω x) = ∑ j : s, a (j : ι) * ω (j : ι)
    rw [← Finset.sum_attach s (fun x => a x * ω x)]
    simp

noncomputable def gaussianLinearCombinationVariance {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ℝ≥0 :=
  ∑ i ∈ s, Real.toNNReal ((a i) ^ (2 : Nat))

theorem gaussianLinearCombinationVariance_insert {ι : Type*} [DecidableEq ι]
    {i : ι} {s : Finset ι} (his : i ∉ s) (a : ι → ℝ) :
    gaussianLinearCombinationVariance (insert i s) a =
      Real.toNNReal ((a i) ^ (2 : Nat)) + gaussianLinearCombinationVariance s a := by
  simp [gaussianLinearCombinationVariance, Finset.sum_insert, his]

theorem map_gaussianLinearCombination_eq_gaussianReal {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) :
    Measure.map (gaussianLinearCombination s a) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0 (gaussianLinearCombinationVariance s a) := by
  induction s using Finset.induction with
  | empty =>
      change Measure.map (fun _ : GaussianSequenceSpace ι => 0) (gaussianSequenceMeasure ι) =
        ProbabilityTheory.gaussianReal 0 0
      rw [ProbabilityTheory.gaussianReal_zero_var, Measure.map_const]
      simp
  | insert i s his ih =>
      have hsum_fun :
          gaussianLinearCombination (insert i s) a =
            (fun ω => a i * gaussianCoordinate i ω) + gaussianLinearCombination s a := by
        funext ω
        simp [gaussianLinearCombination, Finset.sum_insert, his]
      have hindep :
          (fun ω => a i * gaussianCoordinate i ω)
            ⟂ᵢ[gaussianSequenceMeasure ι]
          gaussianLinearCombination s a := by
        have h := (indepFun_gaussianCoordinate_gaussianLinearCombination his a).comp
          (by fun_prop : Measurable (fun x : ℝ => a i * x)) measurable_id
        simpa [Function.comp_def] using h
      have hscaled :
          Measure.map (fun ω => a i * gaussianCoordinate i ω)
              (gaussianSequenceMeasure ι) =
            ProbabilityTheory.gaussianReal 0 (Real.toNNReal ((a i) ^ (2 : Nat))) :=
        map_const_mul_gaussianCoordinate i (a i)
      have hscaledLaw :
          HasLaw (fun ω => a i * gaussianCoordinate i ω)
            (ProbabilityTheory.gaussianReal 0
              (Real.toNNReal ((a i) ^ (2 : Nat)))) (gaussianSequenceMeasure ι) :=
        { aemeasurable := (aemeasurable_gaussianCoordinate i).const_mul (a i)
          map_eq := hscaled }
      have hsumLaw :
          HasLaw (gaussianLinearCombination s a)
            (ProbabilityTheory.gaussianReal 0
              (gaussianLinearCombinationVariance s a)) (gaussianSequenceMeasure ι) :=
        { aemeasurable := aemeasurable_gaussianLinearCombination s a
          map_eq := ih }
      have hsum :=
        ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
          hindep hscaledLaw hsumLaw
      rw [hsum_fun]
      simpa [gaussianLinearCombinationVariance_insert his a] using hsum

theorem coe_gaussianLinearCombinationVariance {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (gaussianLinearCombinationVariance s a : ℝ) =
      ∑ i ∈ s, (a i) ^ (2 : Nat) := by
  simp [gaussianLinearCombinationVariance, Real.coe_toNNReal _ (sq_nonneg _)]

end RegularityStructures

end
