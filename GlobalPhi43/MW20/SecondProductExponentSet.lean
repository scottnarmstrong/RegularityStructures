module

public import GlobalPhi43.MW20.SecondProductSmooth

/-! The actual three-element exponent set for the second product in MW20
section 5.2.3. All three reconstruction exponents are exactly 1/2-7κ. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory

/-- Source-scale second-germ coherence indexed by the literal finite set of
A, V and XV testing exponents, retaining the three distinct tree coefficients. -/
theorem secondReconstructionGerm_coherence_exponent_set {E ι : Type*}
    [MeasurableSpace E] [Fintype ι]
    (μ : Measure E) (K v Y Z V : E → ℝ) (ν X : E → ι → ℝ) (C₂ : ℝ) (x z : E)
    (hA : Integrable (fun y => K y * ((Y y - Y z) * V y - C₂)) μ)
    (hV : Integrable (fun y => K y * V y) μ)
    (hX : ∀ i, Integrable (fun y => K y * ((X y i - X z i) * V y)) μ)
    {κ d t Hᵥ HU Hν NA NV NX : ℝ} (hκ : 0 < κ) (hsmall : κ < 1 / 14)
    (hv : |v x - v z| ≤ Hᵥ * d ^ (1 / 2 - 3 * κ))
    (hU : |Local.expansion v Y Z x z - ∑ i, ν x i * (X z i - X x i)| ≤
      HU * d ^ (3 / 2 - 5 * κ))
    (hν : ∀ i, |ν x i - ν z i| ≤ Hν * d ^ (1 / 2 - 5 * κ))
    (ha : |∫ y, K y * ((Y y - Y z) * V y - C₂) ∂μ| ≤ NA * t ^ (-4 * κ))
    (hb : |∫ y, K y * V y ∂μ| ≤ NV * t ^ (-1 - 2 * κ))
    (hc : ∀ i, |∫ y, K y * ((X y i - X z i) * V y) ∂μ| ≤ NX * t ^ (-2 * κ)) :
    |∫ y, K y * (secondReconstructionGerm v Y Z V ν X C₂ x y -
      secondReconstructionGerm v Y Z V ν X C₂ z y) ∂μ| ≤
      ∑ β ∈ ({-4 * κ, -1 - 2 * κ, -2 * κ} : Finset ℝ),
        (if β = -4 * κ then 3 * Hᵥ * NA
          else if β = -1 - 2 * κ then HU * NV else (Fintype.card ι : ℝ) * Hν * NX) *
          d ^ ((1 / 2 - 7 * κ) - β) * t ^ β := by
  classical
  have hAV : -4 * κ ≠ -1 - 2 * κ := by intro he; linarith
  have hAX : -4 * κ ≠ -2 * κ := by intro he; linarith
  have hVX : -1 - 2 * κ ≠ -2 * κ := by intro he; linarith
  have hnot : -4 * κ ∉ ({-1 - 2 * κ, -2 * κ} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hAV, hAX⟩
  have heA : (1 / 2 - 7 * κ) - -4 * κ = 1 / 2 - 3 * κ := by ring
  have heV : (1 / 2 - 7 * κ) - (-1 - 2 * κ) = 3 / 2 - 5 * κ := by ring
  have heX : (1 / 2 - 7 * κ) - -2 * κ = 1 / 2 - 5 * κ := by ring
  simpa only [Finset.sum_insert hnot, Finset.sum_pair hVX, eq_self, ite_true,
    Ne.symm hAV, Ne.symm hAX, Ne.symm hVX, ite_false, heA, heV, heX, add_assoc] using
    secondReconstructionGerm_coherence_scales μ K v Y Z V ν X C₂ x z hA hV hX hv hU hν ha hb hc

/-- The three distinct testing exponents satisfy the source reconstruction
hypotheses, including the non-strict individual regularity endpoint. -/
theorem secondProduct_exponents_admissible {κ : ℝ} (_hκ : 0 < κ) (hsmall : κ < 1 / 14) :
    0 < (1 / 2 : ℝ) - 7 * κ ∧
      ∀ β ∈ ({-4 * κ, -1 - 2 * κ, -2 * κ} : Finset ℝ), β ≤ 1 / 2 - 7 * κ := by
  constructor
  · linarith
  · intro β hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with h | h | h <;> rw [h] <;> linarith

end GlobalPhi43.MW20
