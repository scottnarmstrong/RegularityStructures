/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.SecondReconstructionTest
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Smooth compact-test attachment for the second MW20 product germ

The auxiliary germ uses the counterterm sign compatible with the product identity.
Smooth source fields and a continuous compactly supported test supply every
integrability premise of the second-germ coherence bound. Quantitative
coefficient bounds are expressed through the source seminorms. These are
reconstruction estimates for Lemma 2.10; the product estimate is [MW20, (2.33)].
-/

public section

open MeasureTheory
open scoped ContDiff

namespace GlobalPhi43.MW20


/-- Source-scale form of the second tested coherence bound. In spatial
 dimension three the final cardinal coefficient is exactly three. -/
theorem secondReconstructionGerm_coherence_scales {E ι : Type*}
    [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (K v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ) (x z : E)
    (hA : Integrable (fun y => K y * ((Y y - Y z) * V y - C₂)) μ)
    (hV : Integrable (fun y => K y * V y) μ)
    (hX : ∀ i, Integrable (fun y => K y * ((X y i - X z i) * V y)) μ)
    {κ d t Hᵥ HU Hν NA NV NX : ℝ}
    (hv : |v x - v z| ≤ Hᵥ * d ^ (1 / 2 - 3 * κ))
    (hU : |Local.expansion v Y Z x z - ∑ i, ν x i * (X z i - X x i)| ≤
      HU * d ^ (3 / 2 - 5 * κ))
    (hν : ∀ i, |ν x i - ν z i| ≤ Hν * d ^ (1 / 2 - 5 * κ))
    (ha : |∫ y, K y * ((Y y - Y z) * V y - C₂) ∂μ| ≤ NA * t ^ (-4 * κ))
    (hb : |∫ y, K y * V y ∂μ| ≤ NV * t ^ (-1 - 2 * κ))
    (hc : ∀ i, |∫ y, K y * ((X y i - X z i) * V y) ∂μ| ≤ NX * t ^ (-2 * κ)) :
    |∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y -
      secondReconstructionGerm v Y Z V ν X C₂ z y) ∂μ| ≤
      3 * Hᵥ * NA * d ^ (1 / 2 - 3 * κ) * t ^ (-4 * κ) +
      HU * NV * d ^ (3 / 2 - 5 * κ) * t ^ (-1 - 2 * κ) +
      (Fintype.card ι : ℝ) * Hν * NX * d ^ (1 / 2 - 5 * κ) * t ^ (-2 * κ) := by
  convert secondReconstructionGerm_tested_increment_bound μ K v Y Z V ν X C₂ x z
    hA hV hX hv hU hν ha hb hc using 1
  ring

end GlobalPhi43.MW20

end
