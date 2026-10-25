/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.Isonormal
public import RegularityStructures.Probability.WhiteNoise
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Existence of space-time white noise

The product-Gaussian isonormal construction is instantiated on the Hilbert space
`L²(ℝ × T³, volume)`. The resulting family has the exact finite-dimensional definition of space-time
white noise used in `RegularityStructures.Probability.WhiteNoise` and in item (W1) of Lemma 4.1 of
the statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace NNReal ProbabilityTheory lp

namespace RegularityStructures

section IsonormalProcess

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (b : HilbertBasis ι ℝ H) [Encodable ι] [DecidableEq ι]

noncomputable def isonormalL2 : H →ₗᵢ[ℝ] Lp ℝ 2 (gaussianSequenceMeasure ι) :=
  (gaussianL2Isometry (ι := ι)).comp b.repr.toLinearIsometry

noncomputable def isonormalValue (h : H) : GaussianSequenceSpace ι → ℝ :=
  fun ω => isonormalL2 b h ω

omit [Encodable ι] in
theorem measurable_isonormalValue (h : H) :
    Measurable (isonormalValue b h) := by
  change Measurable (isonormalL2 b h).1
  exact AEEqFun.measurable (isonormalL2 b h).1

theorem map_isonormalValue_eq_gaussianReal (h : H) :
    Measure.map (isonormalValue b h) (gaussianSequenceMeasure ι) =
      ProbabilityTheory.gaussianReal 0
        (Real.toNNReal (‖h‖ ^ (2 : Nat))) := by
  change Measure.map (gaussianL2Isometry (ι := ι) (b.repr h))
      (gaussianSequenceMeasure ι) = _
  rw [map_gaussianL2Isometry_eq_gaussianReal]
  simp

theorem hasLaw_isonormalValue (h : H) :
    HasLaw (isonormalValue b h)
      (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖h‖ ^ (2 : Nat))))
      (gaussianSequenceMeasure ι) where
  aemeasurable := (Lp.aestronglyMeasurable (isonormalL2 b h)).aemeasurable
  map_eq := map_isonormalValue_eq_gaussianReal b h

omit [Encodable ι] in
theorem isonormalValue_finset_linearCombination_ae {κ : Type*} (s : Finset κ)
    (a : κ → ℝ) (f : κ → H) :
    (fun ω => ∑ i ∈ s, a i * isonormalValue b (f i) ω) =ᵐ[
      gaussianSequenceMeasure ι]
      fun ω => isonormalValue b (∑ i ∈ s, a i • f i) ω := by
  have hLp :
      (∑ i ∈ s, a i • isonormalL2 b (f i)) =
        isonormalL2 b (∑ i ∈ s, a i • f i) := by
    simp [isonormalL2, map_sum]
  change (fun ω => ∑ i ∈ s, a i * isonormalValue b (f i) ω) =ᵐ[
      gaussianSequenceMeasure ι]
      fun ω => isonormalL2 b (∑ i ∈ s, a i • f i) ω
  rw [← hLp]
  have hcoe :
      (fun ω => (∑ i ∈ s, a i • isonormalL2 b (f i)) ω) =ᵐ[
        gaussianSequenceMeasure ι]
      fun ω => ∑ i ∈ s, a i * isonormalValue b (f i) ω := by
    refine (Lp.coeFn_fun_finsetSum s (fun i => a i • isonormalL2 b (f i))).trans ?_
    filter_upwards [eventuallyEq_sum fun i _ =>
      Lp.coeFn_smul (a i) (isonormalL2 b (f i))] with ω hω
    simpa [isonormalValue] using hω
  exact hcoe.symm

theorem isGaussian_isonormalVector {n : ℕ} (f : Fin n → H) :
    ProbabilityTheory.IsGaussian
      ((gaussianSequenceMeasure ι).map (fun ω i => isonormalValue b (f i) ω)) := by
  apply ProbabilityTheory.isGaussian_of_map_eq_gaussianReal
  intro L
  let a : Fin n → ℝ := fun i => (L.comp (.single ℝ (fun _ : Fin n => ℝ) i)) 1
  have hL :
      L ∘ (fun ω i => isonormalValue b (f i) ω) =
        fun ω => ∑ i, a i * isonormalValue b (f i) ω := by
    ext ω
    change L (fun i => isonormalValue b (f i) ω) = _
    calc
      L (fun i => isonormalValue b (f i) ω) =
          ∑ i, (L.comp (.single ℝ (fun _ : Fin n => ℝ) i))
            (isonormalValue b (f i) ω) := by
        rw [← L.sum_comp_single]
      _ = ∑ i, a i * isonormalValue b (f i) ω := by
        apply Finset.sum_congr rfl
        intro i hi
        change (L.comp (.single ℝ (fun _ : Fin n => ℝ) i))
            (isonormalValue b (f i) ω) =
          (L.comp (.single ℝ (fun _ : Fin n => ℝ) i)) 1 *
            isonormalValue b (f i) ω
        conv_lhs =>
          rw [show isonormalValue b (f i) ω =
            isonormalValue b (f i) ω • (1 : ℝ) by simp]
        rw [(L.comp (.single ℝ (fun _ : Fin n => ℝ) i)).map_smul]
        simp [smul_eq_mul, mul_comm]
  have hX :
      AEMeasurable (fun ω i => isonormalValue b (f i) ω)
        (gaussianSequenceMeasure ι) :=
    aemeasurable_pi_iff.2 fun i =>
      (Lp.aestronglyMeasurable (isonormalL2 b (f i))).aemeasurable
  have hae := isonormalValue_finset_linearCombination_ae b
    (Finset.univ : Finset (Fin n)) a f
  have hmap :
      Measure.map L
          ((gaussianSequenceMeasure ι).map (fun ω i => isonormalValue b (f i) ω)) =
        ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (‖∑ i, a i • f i‖ ^ (2 : Nat))) := by
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hX, hL]
    calc
      Measure.map (fun ω => ∑ i, a i * isonormalValue b (f i) ω)
          (gaussianSequenceMeasure ι) =
          Measure.map (isonormalValue b (∑ i, a i • f i))
            (gaussianSequenceMeasure ι) := by
        apply Measure.map_congr
        simpa using hae
      _ = _ := map_isonormalValue_eq_gaussianReal b _
  exact ⟨0, Real.toNNReal (‖∑ i, a i • f i‖ ^ (2 : Nat)), hmap⟩

theorem integral_isonormalValue (h : H) :
    ∫ ω, isonormalValue b h ω ∂gaussianSequenceMeasure ι = 0 := by
  calc
    ∫ ω, isonormalValue b h ω ∂gaussianSequenceMeasure ι =
        ∫ x, x ∂ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (‖h‖ ^ (2 : Nat))) := (hasLaw_isonormalValue b h).integral_eq
    _ = 0 := by simp

omit [Encodable ι] in
theorem integral_mul_isonormalValue (f g : H) :
    ∫ ω, isonormalValue b f ω * isonormalValue b g ω
        ∂gaussianSequenceMeasure ι = ⟪f, g⟫_ℝ := by
  calc
    ∫ ω, isonormalValue b f ω * isonormalValue b g ω
        ∂gaussianSequenceMeasure ι =
        ⟪isonormalL2 b f, isonormalL2 b g⟫_ℝ := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with ω
      simp [isonormalValue, mul_comm]
    _ = ⟪f, g⟫_ℝ := (isonormalL2 b).inner_map_map f g

end IsonormalProcess

section WhiteNoise

abbrev spaceTimeHilbert : Type :=
  Lp ℝ 2 (volume : Measure SpaceTime)

theorem isCentredGaussianVector_isonormal {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ι ℝ H) [Encodable ι] [DecidableEq ι] {n : ℕ}
    (f : Fin n → H) :
    IsCentredGaussianVector (gaussianSequenceMeasure ι)
      (fun ω i => isonormalValue b (f i) ω)
      (fun i j => ⟪f i, f j⟫_ℝ) := by
  have haemeas :
      AEMeasurable (fun ω i => isonormalValue b (f i) ω)
        (gaussianSequenceMeasure ι) :=
    aemeasurable_pi_iff.2 fun i =>
      (Lp.aestronglyMeasurable (isonormalL2 b (f i))).aemeasurable
  have hgauss := isGaussian_isonormalVector b f
  refine ⟨haemeas, hgauss, ?_, ?_⟩
  · intro i
    exact integral_isonormalValue b (f i)
  · intro i j
    exact integral_mul_isonormalValue b (f i) (f j)

noncomputable def spaceTimeBasisData :
    Σ w : Set (spaceTimeHilbert), HilbertBasis w ℝ (spaceTimeHilbert) := by
  classical
  let h : ∃ (w : Set spaceTimeHilbert) (b : HilbertBasis w ℝ (spaceTimeHilbert)),
      ⇑b = ((↑) : w → spaceTimeHilbert) :=
    exists_hilbertBasis ℝ (spaceTimeHilbert)
  let w : Set spaceTimeHilbert := Classical.choose h
  let b : HilbertBasis w ℝ (spaceTimeHilbert) :=
    Classical.choose (Classical.choose_spec h)
  exact ⟨w, b⟩

noncomputable def spaceTimeBasis :
    HilbertBasis spaceTimeBasisData.1 ℝ (spaceTimeHilbert) :=
  spaceTimeBasisData.2

noncomputable instance spaceTimeBasisData_countable : Countable spaceTimeBasisData.1 :=
  countable_of_orthonormal_of_separable spaceTimeBasis.orthonormal

noncomputable instance spaceTimeBasisData_encodable : Encodable spaceTimeBasisData.1 :=
  Encodable.ofCountable _

noncomputable instance spaceTimeBasisData_decidableEq : DecidableEq spaceTimeBasisData.1 :=
  Classical.decEq _

theorem isCentredGaussianVector_spaceTime {n : ℕ} (h : Fin n → SpaceTime → ℝ)
    (hh : ∀ i, MemLp (h i) 2 (volume : Measure SpaceTime)) :
    IsCentredGaussianVector (gaussianSequenceMeasure spaceTimeBasisData.1)
      (fun ω i => isonormalValue spaceTimeBasis ((hh i).toLp (h i)) ω)
      (fun i j => ∫ z, h i z * h j z) := by
  have hcent := isCentredGaussianVector_isonormal spaceTimeBasis
    (fun i => (hh i).toLp (h i))
  refine ⟨hcent.1, hcent.2.1, hcent.2.2.1, ?_⟩
  intro i j
  calc
    ∫ ω, isonormalValue spaceTimeBasis ((hh i).toLp (h i)) ω *
        isonormalValue spaceTimeBasis ((hh j).toLp (h j)) ω
        ∂gaussianSequenceMeasure spaceTimeBasisData.1 =
      ⟪(hh i).toLp (h i), (hh j).toLp (h j)⟫_ℝ := hcent.2.2.2 i j
    _ = ∫ z, h i z * h j z := inner_toLp_real (hh i) (hh j)

end WhiteNoise

end RegularityStructures

namespace RegularityStructures

open MeasureTheory

noncomputable def spaceTimeWhiteNoise (h : SpaceTime → ℝ) :
    GaussianSequenceSpace spaceTimeBasisData.1 → ℝ := by
  classical
  exact if hh : MemLp h 2 (volume : Measure SpaceTime) then
    isonormalValue spaceTimeBasis (hh.toLp h) else fun _ => 0

/-- **(W1)** Some probability space carries a space-time white noise; this is item (W1) of
Lemma 4.1 of the statement, using its Definition 2.2 of finite-dimensional Gaussian white noise. -/
theorem exists_whiteNoise :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ IsWhiteNoise P W := by
  let Ω := GaussianSequenceSpace spaceTimeBasisData.1
  let W : (SpaceTime → ℝ) → Ω → ℝ := spaceTimeWhiteNoise
  refine ⟨Ω, inferInstance, gaussianSequenceMeasure spaceTimeBasisData.1, W,
    inferInstance, ?_⟩
  constructor
  · intro h hh
    simpa [W, spaceTimeWhiteNoise, Ω, hh] using
      measurable_isonormalValue spaceTimeBasis (hh.toLp h)
  · intro n h hh
    have hcent := isCentredGaussianVector_spaceTime h hh
    simpa [W, spaceTimeWhiteNoise, Ω, hh] using hcent

end RegularityStructures

end
