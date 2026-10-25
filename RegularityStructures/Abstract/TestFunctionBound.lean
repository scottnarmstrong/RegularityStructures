/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Pairing
public import RegularityStructures.Analysis.Semigroup.Pairing.Limit

/-!
# The reconstruction bound tested against test functions

The reconstruction theorem in [Hai14, Theorem 3.10, (3.3)] is stated with test functions:
`|⟨Rf − Π_x f(x), φ^λ_x⟩| ≲ λ^γ`. Here the distribution `Λ = Rf − Π_{x₀} f(x₀)` is of local
order `γ` at `x₀` (`Model.abs_reconstruct_sub_regPi_le`), so the abstract bridge
`RegularisingSemigroup.abs_pairing_le` applies to every test function `φ` supported in
`{d(·, x₀) ≤ λ}` whose generator image `ψ = Lφ` is supported there too, with
`∫|φ| ≤ B₀` and `∫|ψ| ≤ B₁ λ^{-ℓ}`. On `ℝ⁴` these hypotheses hold for `φ = φ^λ_{x₀}`,
`φ ∈ B^4` (`Model.abs_pairing_rescaledTestFunction_le`), giving Hairer's form of the bound.

This requires all homogeneities below `γ` to exceed `-ℓ` (for the regularising semigroup on
`ℝ⁴`, `ℓ = 4`; in the Φ⁴₃ structure the lowest homogeneity is `-5/2 - κ`).

Source: [Hai14, Theorem 3.10], [Hos25, Section 4].
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The distribution `Rf − Π_{x₀} f(x₀)`, through its regularisations. -/
def reconstructSubAt (M : Model 𝒯 K) (f : E → ι → ℝ) (x₀ : E) (t : ℝ) (y : E) : ℝ :=
  M.reconstruct f t y - M.regPi x₀ (f x₀) t y

end Model

/-- The constant of the test-function form of the reconstruction bound. -/
def testReconstructionConst (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ)
    (γ : ℝ) : ℝ :=
  (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * K.pairingConst (insert γ (𝒯.degreesBelow γ))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

section Single

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} [SFinite μ]
  (M : Model 𝒯 K) {γ CPi Cf : ℝ} (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi)
  {f : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
  (hCf : 0 ≤ Cf)

include hγ hPi hCPi hf hfb hCf

theorem reconstructSubAt_mem (x₀ : E) : M.reconstructSubAt f x₀ ∈ K.distributions :=
  K.distributions.sub_mem (M.reconstruct_mem hγ hPi hCPi hf hfb hCf) (M.regPi_mem x₀ (f x₀))

theorem measurable_reconstructSubAt (x₀ : E) {u : ℝ} (hu : 0 < u) :
    Measurable (M.reconstructSubAt f x₀ u) :=
  (K.measurable_reconstruct (M.isGerm_germ hPi hf) hγ
    (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hCf hCPi)) (M.isCoherent_germ hPi hCPi hf hfb hCf) hu).sub
    (M.measurable_regPi x₀ (f x₀) hu)

theorem isLocalOrder_reconstructSubAt (x₀ : E) :
    K.IsLocalOrder (M.reconstructSubAt f x₀) x₀ γ (insert γ (𝒯.degreesBelow γ))
      ((modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf) :=
  fun _ hu y => M.abs_reconstruct_sub_regPi_le hγ hPi hCPi hf hfb hCf hu x₀ y

/-- **Reconstruction bound against test functions** ([Hai14, Theorem 3.10, (3.3)]), abstract
form: if all homogeneities below `γ` exceed `-ℓ`, then for every test function `φ` supported in
`{d(·, x₀) ≤ λ}`, `0 < λ ≤ 1`, with generator image `ψ` supported there,
`∫|φ| ≤ B₀`, `∫|ψ| ≤ B₁ λ^{-ℓ}`, the pairing `⟨Rf − Π_{x₀} f(x₀), φ⟩` exists and
`|⟨Rf − Π_{x₀} f(x₀), φ⟩| ≤ c C_Π C_f (B₀ + B₁) λ^γ`, `c = testReconstructionConst 𝒯 K γ`. -/
theorem abs_pairing_reconstructSubAt_le (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) (hdeg : ∀ i, 𝒯.deg i < γ → -K.order < 𝒯.deg i) (x₀ : E)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hφm : Measurable φ) (hψm : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    Filter.Tendsto (fun s => ∫ y, M.reconstructSubAt f x₀ s y * φ y ∂μ)
        (nhdsWithin 0 (Ioi 0)) (nhds (K.pairing (M.reconstructSubAt f x₀) φ)) ∧
      |K.pairing (M.reconstructSubAt f x₀) φ| ≤
        testReconstructionConst 𝒯 K γ * CPi * Cf * (B₀ + B₁) * lam ^ γ := by
  have hA : ∀ a ∈ insert γ (𝒯.degreesBelow γ), -K.order < a ∧ a ≤ γ := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨by linarith [K.order_pos], le_rfl⟩
    · obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
      exact ⟨hdeg i hi, hi.le⟩
  have hC : 0 ≤ (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf :=
    mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 K hγ.le)
      (Nat.cast_nonneg _)) hCPi) hCf
  have hmem := M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x₀
  have hmeas := fun u (hu : 0 < u) => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x₀ hu
  have hloc := M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x₀
  refine ⟨K.tendsto_integral_pairing hK hd hJ hmem hmeas hA hC hloc hlam hlam1 hφm hψm hφi hψi
    hφs hψs hφ1 hψ1 hgen, ?_⟩
  have h := K.abs_pairing_le hK hd hJ hmem hmeas hA hC hloc hlam hlam1 hφm hψm hφi hψi
    hφs hψs hφ1 hψ1 hgen
  calc |K.pairing (M.reconstructSubAt f x₀) φ|
      ≤ (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf *
          K.pairingConst (insert γ (𝒯.degreesBelow γ)) * (B₀ + B₁) * lam ^ γ := h
    _ = testReconstructionConst 𝒯 K γ * CPi * Cf * (B₀ + B₁) * lam ^ γ := by
        rw [testReconstructionConst]
        ring


end Single

section Lipschitz

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} [SFinite μ]

/-- Local order at `x₀` of the difference `(R¹f¹ − Π¹_{x₀} f¹(x₀)) − (R²f² − Π²_{x₀} f²(x₀))`
for two models, with constant `(c + |ι|)(C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||)`. -/
theorem isLocalOrder_reconstructSubAt_sub (M₁ M₂ : Model 𝒯 K) {γ : ℝ} (hγ : 0 < γ)
    {CPi₁ CPi₂ CdPi Cf₁ Cf₂ Cdf : ℝ}
    (hPi₁ : M₁.PiBoundOn γ CPi₁ univ) (hPi₂ : M₂.PiBoundOn γ CPi₂ univ)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi univ) (hCPi₁ : 0 ≤ CPi₁) (hCPi₂ : 0 ≤ CPi₂)
    (hCdPi : 0 ≤ CdPi) {f₁ f₂ : E → ι → ℝ} (hf₁ : f₁ ∈ M₁.modelledDistributions γ)
    (hf₂ : f₂ ∈ M₂.modelledDistributions γ) (hfb₁ : M₁.ModelledBoundOn γ Cf₁ univ f₁)
    (hfb₂ : M₂.ModelledBoundOn γ Cf₂ univ f₂) (hdf : M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂)
    (hCf₁ : 0 ≤ Cf₁) (hCf₂ : 0 ≤ Cf₂) (hCdf : 0 ≤ Cdf) (x₀ : E) :
    K.IsLocalOrder (fun t y => M₁.reconstructSubAt f₁ x₀ t y - M₂.reconstructSubAt f₂ x₀ t y)
      x₀ γ (insert γ (𝒯.degreesBelow γ))
      ((modelReconstructionConst 𝒯 K γ + Fintype.card ι) * (Cf₁ * CdPi + Cdf * CPi₂)) := by
  intro u hu y
  have hγA : γ ∉ 𝒯.degreesBelow γ := fun h => lt_irrefl γ (𝒯.lt_of_mem_degreesBelow h)
  set D := Cf₁ * CdPi + Cdf * CPi₂ with hD
  have hD0 : 0 ≤ D := add_nonneg (mul_nonneg hCf₁ hCdPi) (mul_nonneg hCdf hCPi₂)
  have h1 := abs_reconstruct_sub_reconstruct_le M₁ M₂ hγ hPi₁ hPi₂ hdPi hCPi₁ hCPi₂ hCdPi hf₁ hf₂
    hfb₁ hfb₂ hdf hCf₁ hCf₂ hCdf hu y
  have h2 := isCoherent_germ_sub M₁ M₂ hPi₂ hdPi hf₁ hf₂ hfb₁ hdf hCf₁ hCdf hCdPi hCPi₂ hu x₀ y
  simp only [Pi.sub_apply] at h2
  set S := ∑ a ∈ 𝒯.degreesBelow γ, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ =>
    mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
  have hu' : 0 ≤ u ^ (γ / K.order) := Real.rpow_nonneg hu.1.le _
  have hc := modelReconstructionConst_nonneg 𝒯 K hγ.le
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [Finset.sum_insert hγA, sub_self, Real.rpow_zero, mul_one]
  beta_reduce
  have hid : M₁.reconstructSubAt f₁ x₀ u y - M₂.reconstructSubAt f₂ x₀ u y =
      ((M₁.reconstruct f₁ u y - M₂.reconstruct f₂ u y) -
        (M₁.regPi y (f₁ y) u y - M₂.regPi y (f₂ y) u y)) -
      ((M₁.germ f₁ x₀ u y - M₂.germ f₂ x₀ u y) - (M₁.germ f₁ y u y - M₂.germ f₂ y u y)) := by
    simp only [reconstructSubAt, germ]
    ring
  rw [hid]
  have e1 : modelReconstructionConst 𝒯 K γ * D * u ^ (γ / K.order) ≤
      (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * D * u ^ (γ / K.order) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hcard) hD0)
      hu'
  have e2 : Fintype.card ι * D * S ≤ (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * D * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc) hD0) hS
  calc _ ≤ |(M₁.reconstruct f₁ u y - M₂.reconstruct f₂ u y) -
          (M₁.regPi y (f₁ y) u y - M₂.regPi y (f₂ y) u y)| +
        |(M₁.germ f₁ x₀ u y - M₂.germ f₂ x₀ u y) - (M₁.germ f₁ y u y - M₂.germ f₂ y u y)| :=
        abs_sub _ _
    _ ≤ modelReconstructionConst 𝒯 K γ * D * u ^ (γ / K.order) + Fintype.card ι * D * S :=
        add_le_add h1 h2
    _ ≤ (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * D * u ^ (γ / K.order) +
          (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * D * S := add_le_add e1 e2
    _ = _ := by ring


/-- **Continuity in the model, test-function form** ([Hai14, Theorem 3.10, (3.4)]): for two models
and `fⁱ ∈ D^γ(Mⁱ)`, with `(φ, ψ)` as in `abs_pairing_reconstructSubAt_le`,
`|⟨R¹f¹ − Π¹_{x₀} f¹(x₀) − R²f² + Π²_{x₀} f²(x₀), φ⟩|
  ≤ c (C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||) (B₀ + B₁) λ^γ`. -/
theorem abs_pairing_reconstructSubAt_sub_le (hK : K.IsSymmetric) (hd : K.IsMetricScale)
    (hJ : K.IsJointMeasurable) (M₁ M₂ : Model 𝒯 K) {γ : ℝ} (hγ : 0 < γ)
    (hdeg : ∀ i, 𝒯.deg i < γ → -K.order < 𝒯.deg i) {CPi₁ CPi₂ CdPi Cf₁ Cf₂ Cdf : ℝ}
    (hPi₁ : M₁.PiBoundOn γ CPi₁ univ) (hPi₂ : M₂.PiBoundOn γ CPi₂ univ)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi univ) (hCPi₁ : 0 ≤ CPi₁) (hCPi₂ : 0 ≤ CPi₂)
    (hCdPi : 0 ≤ CdPi) {f₁ f₂ : E → ι → ℝ} (hf₁ : f₁ ∈ M₁.modelledDistributions γ)
    (hf₂ : f₂ ∈ M₂.modelledDistributions γ) (hfb₁ : M₁.ModelledBoundOn γ Cf₁ univ f₁)
    (hfb₂ : M₂.ModelledBoundOn γ Cf₂ univ f₂) (hdf : M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂)
    (hCf₁ : 0 ≤ Cf₁) (hCf₂ : 0 ≤ Cf₂) (hCdf : 0 ≤ Cdf) (x₀ : E)
    {φ ψ : E → ℝ} {lam B₀ B₁ : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hφm : Measurable φ) (hψm : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ μ)
    (hφs : ∀ y, lam < K.scaleDist y x₀ → φ y = 0) (hψs : ∀ y, lam < K.scaleDist y x₀ → ψ y = 0)
    (hφ1 : ∫ y, |φ y| ∂μ ≤ B₀) (hψ1 : ∫ y, |ψ y| ∂μ ≤ B₁ * lam ^ (-K.order))
    (hgen : K.IsGeneratorPair φ ψ) :
    |K.pairing (fun t y => M₁.reconstructSubAt f₁ x₀ t y - M₂.reconstructSubAt f₂ x₀ t y) φ| ≤
      testReconstructionConst 𝒯 K γ * (Cf₁ * CdPi + Cdf * CPi₂) * (B₀ + B₁) * lam ^ γ := by
  have hA : ∀ a ∈ insert γ (𝒯.degreesBelow γ), -K.order < a ∧ a ≤ γ := by
    intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨by linarith [K.order_pos], le_rfl⟩
    · obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
      exact ⟨hdeg i hi, hi.le⟩
  have hC : 0 ≤ (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * (Cf₁ * CdPi + Cdf * CPi₂) :=
    mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 K hγ.le) (Nat.cast_nonneg _))
      (add_nonneg (mul_nonneg hCf₁ hCdPi) (mul_nonneg hCdf hCPi₂))
  have hmem : (fun t y => M₁.reconstructSubAt f₁ x₀ t y - M₂.reconstructSubAt f₂ x₀ t y) ∈
      K.distributions :=
    K.distributions.sub_mem (M₁.reconstructSubAt_mem hγ hPi₁ hCPi₁ hf₁ hfb₁ hCf₁ x₀)
      (M₂.reconstructSubAt_mem hγ hPi₂ hCPi₂ hf₂ hfb₂ hCf₂ x₀)
  have hmeas : ∀ u, 0 < u → Measurable
      ((fun t y => M₁.reconstructSubAt f₁ x₀ t y - M₂.reconstructSubAt f₂ x₀ t y) u) :=
    fun u hu => (M₁.measurable_reconstructSubAt hγ hPi₁ hCPi₁ hf₁ hfb₁ hCf₁ x₀ hu).sub
      (M₂.measurable_reconstructSubAt hγ hPi₂ hCPi₂ hf₂ hfb₂ hCf₂ x₀ hu)
  have hloc := isLocalOrder_reconstructSubAt_sub M₁ M₂ hγ hPi₁ hPi₂ hdPi hCPi₁ hCPi₂ hCdPi hf₁ hf₂
    hfb₁ hfb₂ hdf hCf₁ hCf₂ hCdf x₀
  have h := K.abs_pairing_le hK hd hJ hmem hmeas hA hC hloc hlam hlam1 hφm hψm hφi hψi
    hφs hψs hφ1 hψ1 hgen
  refine h.trans (le_of_eq ?_)
  rw [testReconstructionConst]
  ring

end Lipschitz

end Model

end RegularityStructures

end
