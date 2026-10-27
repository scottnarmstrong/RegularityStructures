/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Probability.NoiseExteriorGeometry

/-! Increasing exterior fields exhaust the completed complement of the native
half-open time window. This is derived from actual cutoff tests. -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set RegularityStructures

namespace GlobalPhi43.Probability

theorem supportedNoiseSigma_exterior_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) (s t : ℝ) :
    supportedNoiseSigma (mΩ := mΩ) P W (Ioc s t ×ˢ (univ : Set Torus3))ᶜ ≤
      ⨆ n, supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth n)) := by
  let m := ⨆ n, supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth n))
  have hm : m ≤ mΩ := iSup_le fun n =>
    supportedNoiseSigma_le (mΩ := mΩ) P hW (exteriorStrip s t (germWidth n))
  have hn : MeasurableSpace.generateFrom {A | MeasurableSet[mΩ] A ∧ P A = 0} ≤ m :=
    (null_le_supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth 0))).trans
      (le_iSup (fun n => supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth n))) 0)
  apply sup_le hn
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  have hf (n : ℕ) := hh.1.indicator (exteriorStrip_measurable s t (germWidth n))
  have hfm (n : ℕ) : Measurable[m] (W ((exteriorStrip s t (germWidth n)).indicator h)) :=
    (measurable_supported_pairing (mΩ := mΩ) P W (hf n)
      (support_indicator_subset _ h)).mono
      (le_iSup (fun j => supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth j))) n) le_rfl
  exact (measurable_whiteNoise_of_Lp_limit (mΩ := mΩ) P hW hm hn hf hh.1 hfm
    (exterior_toLp_tendsto hh.1 s t hh.2)).comap_le

theorem iSup_exteriorNoiseSigma {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W) (s t : ℝ) :
    (⨆ n, supportedNoiseSigma (mΩ := mΩ) P W (exteriorStrip s t (germWidth n))) =
      supportedNoiseSigma (mΩ := mΩ) P W (Ioc s t ×ˢ (univ : Set Torus3))ᶜ := by
  apply le_antisymm
  · exact iSup_le fun n => supportedNoiseSigma_mono P W (exteriorStrip_subset_compl_Ioc_prod s t n)
  · exact supportedNoiseSigma_exterior_le P hW s t

end GlobalPhi43.Probability
