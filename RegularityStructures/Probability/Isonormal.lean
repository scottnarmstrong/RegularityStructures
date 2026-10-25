/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianSequence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Isonormal Gaussian series

This module turns independent standard Gaussian coordinates into an isonormal Gaussian map on a
separable real Hilbert space.  The law of the infinite series is obtained from the finite partial
sums by convergence in distribution and characteristic functions.

The construction is the standard countable-basis proof of the existence part of white noise; see
Definition 2.2 and item (W1) of Lemma 4.1 of the statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace NNReal ProbabilityTheory lp
open scoped Topology
open Filter

namespace RegularityStructures

instance instFact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) :=
  ⟨ENNReal.ofNat_ne_top⟩

theorem inner_toLp_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ ω, f ω * g ω ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp [hfω, hgω, mul_comm]

section GaussianL2

variable {ι : Type*}

noncomputable def gaussianCoordinateLp (i : ι) :
    Lp ℝ 2 (gaussianSequenceMeasure ι) :=
  (memLp_gaussianCoordinate i).toLp (gaussianCoordinate i)

theorem inner_gaussianCoordinateLp [DecidableEq ι] (i j : ι) :
    ⟪gaussianCoordinateLp i, gaussianCoordinateLp j⟫_ℝ =
      if i = j then 1 else 0 := by
  rw [gaussianCoordinateLp, gaussianCoordinateLp, inner_toLp_real]
  have hcov := covariance_gaussianCoordinate (ι := ι) i j
  rw [covariance_eq_sub (memLp_gaussianCoordinate i) (memLp_gaussianCoordinate j)] at hcov
  simpa [integral_gaussianCoordinate] using hcov

theorem orthonormal_gaussianCoordinateLp [DecidableEq ι] :
    Orthonormal ℝ (fun i : ι => gaussianCoordinateLp i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  exact inner_gaussianCoordinateLp i j

noncomputable def gaussianL2Isometry [DecidableEq ι] :
    ℓ²(ι, ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianSequenceMeasure ι) :=
  (orthonormal_gaussianCoordinateLp (ι := ι)).orthogonalFamily.linearIsometry

noncomputable def gaussianIndexTruncation (ι : Type*) [Encodable ι] [DecidableEq ι]
    (n : ℕ) : Finset ι :=
  (Finset.range n).preimage (Encodable.encode : ι → ℕ) (by
    intro i _ j _ hij
    exact Encodable.encode_injective hij)

theorem tendsto_gaussianIndexTruncation (ι : Type*) [Encodable ι] [DecidableEq ι] :
    Tendsto (gaussianIndexTruncation ι) atTop (atTop : Filter (Finset ι)) := by
  exact (Filter.tendsto_finset_preimage_atTop_atTop
    (f := (Encodable.encode : ι → ℕ)) Encodable.encode_injective).comp
      Filter.tendsto_finset_range

noncomputable def gaussianL2CoefficientPartialSum [DecidableEq ι] (s : Finset ι)
    (c : ℓ²(ι, ℝ)) : ℓ²(ι, ℝ) :=
  ∑ i ∈ s, lp.single (E := fun _ : ι => ℝ) 2 i (c i)

theorem norm_gaussianL2CoefficientPartialSum_sq [DecidableEq ι] (s : Finset ι)
    (c : ℓ²(ι, ℝ)) :
    ‖gaussianL2CoefficientPartialSum s c‖ ^ (2 : Nat) =
      ∑ i ∈ s, (c i) ^ (2 : Nat) := by
  have h := lp.norm_sum_single (E := fun _ : ι => ℝ) (p := (2 : ℝ≥0∞))
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (fun i => c i) s
  norm_num at h
  simpa [gaussianL2CoefficientPartialSum, Real.norm_eq_abs, sq_abs] using h

theorem hasSum_gaussianL2CoefficientPartialSum [DecidableEq ι] (c : ℓ²(ι, ℝ)) :
    HasSum (fun i : ι => lp.single (E := fun _ : ι => ℝ) 2 i (c i)) c := by
  simpa using
    (lp.hasSum_single (E := fun _ : ι => ℝ) (p := (2 : ℝ≥0∞))
      ENNReal.ofNat_ne_top c)

theorem tendsto_gaussianL2CoefficientPartialSum [DecidableEq ι] (c : ℓ²(ι, ℝ)) :
    Tendsto (fun s : Finset ι => gaussianL2CoefficientPartialSum s c) atTop (𝓝 c) := by
  simpa [HasSum, gaussianL2CoefficientPartialSum] using
    (hasSum_gaussianL2CoefficientPartialSum c)

theorem tendsto_gaussianL2CoefficientPartialSum_truncation [Encodable ι] [DecidableEq ι]
    (c : ℓ²(ι, ℝ)) :
    Tendsto (fun n : ℕ => gaussianL2CoefficientPartialSum (gaussianIndexTruncation ι n) c)
      atTop (𝓝 c) :=
  (tendsto_gaussianL2CoefficientPartialSum c).comp (tendsto_gaussianIndexTruncation ι)

theorem tendsto_gaussianLinearCombinationVariance_indexTruncation [Encodable ι]
    [DecidableEq ι] (c : ℓ²(ι, ℝ)) :
    Tendsto
      (fun n : ℕ =>
        (gaussianLinearCombinationVariance (gaussianIndexTruncation ι n) fun i => c i : ℝ))
      atTop (𝓝 (‖c‖ ^ (2 : Nat))) := by
  have hnorm := ((continuous_norm.tendsto _).comp
    (tendsto_gaussianL2CoefficientPartialSum_truncation c)).pow 2
  convert hnorm using 1
  ext n
  rw [coe_gaussianLinearCombinationVariance]
  simp only [Function.comp_apply]
  rw [norm_gaussianL2CoefficientPartialSum_sq]

noncomputable def gaussianPartialSumLp [DecidableEq ι] (s : Finset ι)
    (c : ℓ²(ι, ℝ)) : Lp ℝ 2 (gaussianSequenceMeasure ι) :=
  ∑ i ∈ s, c i • gaussianCoordinateLp i

theorem gaussianPartialSumLp_coeFn [DecidableEq ι] (s : Finset ι)
    (c : ℓ²(ι, ℝ)) :
    ⇑(gaussianPartialSumLp s c) =ᵐ[gaussianSequenceMeasure ι]
      gaussianLinearCombination s (fun i => c i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      change (fun ω => (0 : Lp ℝ 2 (gaussianSequenceMeasure ι)) ω) =ᵐ[
        gaussianSequenceMeasure ι] gaussianLinearCombination ∅ (fun i => c i)
      filter_upwards with ω
      simp [gaussianLinearCombination]
  | insert i s hi ih =>
      have hsum :
          gaussianPartialSumLp (insert i s) c =
            c i • gaussianCoordinateLp i + gaussianPartialSumLp s c := by
        simp [gaussianPartialSumLp, Finset.sum_insert, hi]
      rw [hsum]
      filter_upwards [Lp.coeFn_add (c i • gaussianCoordinateLp i)
          (gaussianPartialSumLp s c),
        Lp.coeFn_smul (c i) (gaussianCoordinateLp i),
        (memLp_gaussianCoordinate i).coeFn_toLp,
        ih] with ω hadd hsmul hcoord hih
      rw [hadd]
      change ((c i • gaussianCoordinateLp i : Lp ℝ 2 (gaussianSequenceMeasure ι)) ω +
          (gaussianPartialSumLp s c) ω) =
        gaussianLinearCombination (insert i s) (fun i => c i) ω
      rw [hsmul, hih]
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold gaussianCoordinateLp
      rw [hcoord]
      simp [gaussianLinearCombination, Finset.sum_insert, hi]

theorem hasSum_gaussianPartialSumLp [DecidableEq ι] (c : ℓ²(ι, ℝ)) :
    HasSum (fun i : ι => c i • gaussianCoordinateLp i)
      (gaussianL2Isometry (ι := ι) c) := by
  rw [gaussianL2Isometry]
  simpa using
    (orthonormal_gaussianCoordinateLp (ι := ι)).orthogonalFamily.hasSum_linearIsometry c

theorem tendsto_gaussianPartialSumLp [DecidableEq ι] (c : ℓ²(ι, ℝ)) :
    Tendsto (fun s : Finset ι => gaussianPartialSumLp s c) atTop
      (𝓝 (gaussianL2Isometry (ι := ι) c)) := by
  simpa [HasSum, gaussianPartialSumLp] using
    (hasSum_gaussianPartialSumLp c)

theorem map_gaussianPartialSumLp_eq_gaussianReal [DecidableEq ι] (s : Finset ι)
    (c : ℓ²(ι, ℝ)) :
    Measure.map (gaussianPartialSumLp s c) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0
        (gaussianLinearCombinationVariance s fun i => c i) := by
  calc
    Measure.map (gaussianPartialSumLp s c) (gaussianSequenceMeasure ι) =
        Measure.map (gaussianLinearCombination s fun i => c i)
          (gaussianSequenceMeasure ι) := by
          exact Measure.map_congr (gaussianPartialSumLp_coeFn s c)
    _ = ProbabilityTheory.gaussianReal 0
        (gaussianLinearCombinationVariance s fun i => c i) :=
          map_gaussianLinearCombination_eq_gaussianReal s fun i => c i

theorem charFun_map_gaussianL2Isometry [Encodable ι] [DecidableEq ι]
    (c : ℓ²(ι, ℝ)) (t : ℝ) :
    charFun (Measure.map (gaussianL2Isometry (ι := ι) c) (gaussianSequenceMeasure ι)) t =
      charFun (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖c‖ ^ (2 : Nat)))) t := by
  let μ : Measure (GaussianSequenceSpace ι) := gaussianSequenceMeasure ι
  let X : Lp ℝ 2 μ := gaussianL2Isometry (ι := ι) c
  let Xn : ℕ → Lp ℝ 2 μ := fun n =>
    gaussianPartialSumLp (gaussianIndexTruncation ι n) c
  have hLp : Tendsto Xn atTop (𝓝 X) := by
    exact (tendsto_gaussianPartialSumLp c).comp (tendsto_gaussianIndexTruncation ι)
  have hInMeasure : TendstoInMeasure μ (fun n => ⇑(Xn n)) atTop X :=
    tendstoInMeasure_of_tendsto_Lp (p := (2 : ℝ≥0∞)) hLp
  have hDist :
      TendstoInDistribution (fun n => ⇑(Xn n)) atTop (⇑X) (fun _ : ℕ => μ) μ :=
    TendstoInMeasure.tendstoInDistribution hInMeasure fun n =>
      (Lp.aestronglyMeasurable (Xn n)).aemeasurable
  have hWeak :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto (Ω := ℝ) ℂ).mp
      hDist.tendsto
  have hCharLimit :
      Tendsto
        (fun n : ℕ => charFun (Measure.map (Xn n) μ) t)
        atTop (𝓝 (charFun (Measure.map X μ) t)) := by
    simpa [charFun_eq_integral_innerProbChar] using
      hWeak (BoundedContinuousFunction.innerProbChar (t : ℝ))
  have hVarianceLimit :
      Tendsto
        (fun n : ℕ =>
          (gaussianLinearCombinationVariance (gaussianIndexTruncation ι n)
            fun i => c i : ℝ))
        atTop (𝓝 (‖c‖ ^ (2 : Nat))) :=
    tendsto_gaussianLinearCombinationVariance_indexTruncation c
  have hGaussianLimit :
      Tendsto
        (fun n : ℕ =>
          charFun
            (ProbabilityTheory.gaussianReal 0
              (gaussianLinearCombinationVariance (gaussianIndexTruncation ι n) fun i => c i))
            t)
        atTop (𝓝 (charFun
          (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖c‖ ^ (2 : Nat)))) t)) := by
    have hVarianceLimitComplex :=
      (Complex.continuous_ofReal.tendsto _).comp hVarianceLimit
    have hArgumentLimit :
        Tendsto
          (fun n : ℕ =>
            (t : ℂ) * (0 : ℂ) * Complex.I -
              (((gaussianLinearCombinationVariance (gaussianIndexTruncation ι n)
                fun i => c i : ℝ)) : ℂ) * (t : ℂ) ^ (2 : Nat) / 2)
          atTop
          (𝓝 ((t : ℂ) * (0 : ℂ) * Complex.I -
            (((‖c‖ ^ (2 : Nat) : ℝ)) : ℂ) * (t : ℂ) ^ (2 : Nat) / 2)) := by
      exact (tendsto_const_nhds.sub
        ((hVarianceLimitComplex.mul tendsto_const_nhds).div tendsto_const_nhds
          (by norm_num : (2 : ℂ) ≠ 0)))
    have hExp := (Complex.continuous_exp.tendsto _).comp hArgumentLimit
    simpa [Function.comp_def, ProbabilityTheory.charFun_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg ‖c‖)] using hExp
  have hFiniteChar :
      Tendsto
        (fun n : ℕ => charFun (Measure.map (Xn n) μ) t)
        atTop (𝓝 (charFun
          (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖c‖ ^ (2 : Nat)))) t)) := by
    simpa [Xn, μ, map_gaussianPartialSumLp_eq_gaussianReal] using hGaussianLimit
  exact tendsto_nhds_unique hCharLimit hFiniteChar

theorem map_gaussianL2Isometry_eq_gaussianReal [Encodable ι] [DecidableEq ι]
    (c : ℓ²(ι, ℝ)) :
    Measure.map (gaussianL2Isometry (ι := ι) c) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖c‖ ^ (2 : Nat))) := by
  refine Measure.ext_of_charFun ?_
  ext t
  exact charFun_map_gaussianL2Isometry c t

end GaussianL2

theorem countable_of_orthonormal_of_separable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [TopologicalSpace.SeparableSpace H]
    {ι : Type*} {v : ι → H} (hv : Orthonormal ℝ v) : Countable ι := by
  classical
  let r : ℝ := 1 / 3
  refine Pairwise.countable_of_isOpen_disjoint
    (s := fun i : ι => Metric.ball (v i) r) ?hd ?ho ?hne
  · intro i j hij
    rw [Function.onFun]
    refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    have hxi' : dist (v i) x < r := by
      simpa [Metric.mem_ball, dist_comm] using hxi
    have hxj' : dist x (v j) < r := by
      simpa [Metric.mem_ball] using hxj
    have hdist_lt : dist (v i) (v j) < 1 := by
      calc
        dist (v i) (v j) ≤ dist (v i) x + dist x (v j) := dist_triangle _ _ _
        _ < r + r := add_lt_add hxi' hxj'
        _ < 1 := by norm_num [r]
    have hinner := orthonormal_iff_ite.mp hv
    have hii : ⟪v i, v i⟫_ℝ = 1 := by simpa using hinner i i
    have hjj : ⟪v j, v j⟫_ℝ = 1 := by simpa using hinner j j
    have hij0 : ⟪v i, v j⟫_ℝ = 0 := by simpa [hij] using hinner i j
    have hnorm_sq : ‖v i - v j‖ ^ (2 : Nat) = 2 := by
      rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self, hii, hjj, hij0]
      norm_num
    have hdist_gt : 1 < dist (v i) (v j) := by
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (v i - v j), hnorm_sq]
    linarith
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨v i, by simp [r]⟩

end RegularityStructures

end
