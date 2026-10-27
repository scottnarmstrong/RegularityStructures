/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusSchauderSmallP2
public import GlobalPhi43.Local.P2BoundedPerturbation

/-! Receiving composition for localized formal source pricing and the
separately proved original-data bounded defect forcing. This internal
application does not assume that a localized producer has been constructed. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 theorem exists_augmented_schauder_application {I J : Type*}
    (A : Finset I) (α : I → ℝ) (B : Finset J) (β : J → ℝ) (hA : A.Nonempty)
    {γ : ℝ} (hγ : 1 < γ) (hγ₂ : γ < 2)
    (hαγ : ∀ i ∈ A, α i ≤ γ) (hβ : ∀ j ∈ B, 0 ≤ β j) (hβγ : ∀ j ∈ B, β j ≤ γ) :
    ∃ K > 0, ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (U : GermPoint → ℝ)
      (G : (T : ℝ) → 0 < T → ParabolicSpace → ParabolicSpace → ℝ)
      (r d₀ M₁ M₂ F : ℝ), 0 ≤ r → 0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ F →
      (∃ O : Set GermPoint, IsOpen O ∧
        closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) →
      (∀ x ∈ sourceCylinder r, U (x, x) = 0) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
        d ^ γ * |U (x, z) - U (x, b) - U (b, z)| ≤
          M₂ * ∑ j ∈ B, pdist x b ^ β j * pdist b z ^ (γ - β j)) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
        ∀ y ∈ pastBall x L,
        |sourceHeat (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun z => U (x, z))) y -
          G T hT x y| ≤ F) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
        ∀ y ∈ pastBall x L, d ^ γ * T ^ 2 * |G T hT x y| ≤
          M₁ * ∑ i ∈ A, T ^ α i * L ^ (γ - α i)) →
      weightedRadiusAffineSeminorm U r d₀ γ ≤
        ENNReal.ofReal (K * ((radiusSourceUSup U r d₀).toReal + M₁ + M₂ + d₀ ^ 2 * F)) := by
  obtain ⟨K, hK, hb⟩ := exists_radius_schauder_small_P2 A α B β hγ hγ₂ hβ hβγ
  refine ⟨K, hK, ?_⟩
  intro Φ hΦ U G r d₀ M₁ M₂ F hr hM₁ hM₂ hF hU hdiag hthree herror hbase
  have hp : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
      d ^ γ * T ^ 2 * (localScalarSup (fun y => ∫ w,
        sourceHeat (fun z => U (x, z)) (y + w) ∂infiniteKernelMeasure Φ hΦ T hT)
          (pastBall x L)).toReal ≤
        (M₁ + d₀ ^ 2 * F) * ∑ i ∈ A, T ^ α i * L ^ (γ - α i) := by
    intro d hd x hx L hL hLd T hT hTL
    have hd1 : d < 1 := by nlinarith [hd.1, hx.1, hx.2.1, sq_nonneg r]
    have hT1 : T ≤ 1 := by linarith
    have hLT : L + T ≤ d := by linarith
    have heq := source_section_heat_supremum_eq Φ hΦ U hr hT hT1 hL.le hLT hU hx
    rw [← heq]
    have hh := perturbed_one_point_allowance A α hA hαγ hγ₂.le
      (sourceHeat (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun z => U (x, z))))
      (G T hT x) (pastBall x L) hd.1 hd.2 hT hTL (by linarith) hM₁ hF
      (herror d hd x hx L hL hLd T hT hTL) (hbase d hd x hx L hL hLd T hT hTL)
    simpa only [pastSmooth] using! hh
  have hout := hb Φ hΦ U r d₀ (M₁ + d₀ ^ 2 * F) M₂ hr (by positivity) hM₂ hU hdiag hthree hp
  convert hout using 1
  congr 1
  ring

end GlobalPhi43.Local
