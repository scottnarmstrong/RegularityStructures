/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.LocalPatching

/-!
# Patching smooth series supplied one finite window at a time

The finite-window Fourier construction has a countable mode family and a smooth coefficient family
for each window.  This wrapper feeds those window-dependent data into the countable dense patcher.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem exists_smoothVersion_of_windowed_series_certificate
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {X : ℕ → ι → Ω → ℝ} {f : ℕ → ι → SpaceTime → ℝ}
    {Y : SpaceTime → Ω → ℝ} {U : ℕ → Set SpaceTime} {G : Set Ω}
    (hG : MeasurableSet G)
    (hGae : ∀ᵐ w ∂P, w ∈ G)
    (hX : ∀ n i, Measurable (X n i))
    (hSmooth : ∀ n w, w ∈ G →
      IsSmoothOnSpaceTime (fun z => ∑' i, X n i w * f n i z))
    (hEq : ∀ n z, z ∈ U n →
      (fun w => ∑' i, X n i w * f n i z) =ᵐ[P] Y z) :
    ∃ xi : ℕ → Ω → SpaceTime → ℝ,
      (∀ n w, IsSmoothOnSpaceTime (xi n w)) ∧
        (∀ n z, z ∈ U n →
          Measurable (fun w => xi n w z) ∧
            (fun w => xi n w z) =ᵐ[P] Y z) := by
  classical
  have hlocal : ∀ n, ∃ xi : Ω → SpaceTime → ℝ,
      (∀ w, IsSmoothOnSpaceTime (xi w)) ∧
        ∀ z ∈ U n, Measurable (fun w => xi w z) ∧
          (fun w => xi w z) =ᵐ[P] Y z := by
    intro n
    exact exists_smooth_series_version_on hG hGae
      (fun i => hX n i) (hSmooth n) (fun z hz => hEq n z hz)
  choose xi hxi_smooth hxi_eq using hlocal
  exact ⟨xi, hxi_smooth, hxi_eq⟩

theorem exists_smoothVersion_of_windowed_series_certificate_patched
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {X : ℕ → ι → Ω → ℝ} {f : ℕ → ι → SpaceTime → ℝ}
    {Y : SpaceTime → Ω → ℝ} {U : ℕ → Set SpaceTime} {G : Set Ω}
    (hU_open : ∀ n, IsOpen (U n))
    (hU_cover : ⋃ n, U n = Set.univ)
    (hG : MeasurableSet G)
    (hGae : ∀ᵐ w ∂P, w ∈ G)
    (hX : ∀ n i, Measurable (X n i))
    (hSmooth : ∀ n w, w ∈ G →
      IsSmoothOnSpaceTime (fun z => ∑' i, X n i w * f n i z))
    (hEq : ∀ n z, z ∈ U n →
      (fun w => ∑' i, X n i w * f n i z) =ᵐ[P] Y z) :
    ∃ ξ : Ω → SpaceTime → ℝ,
      (∀ w, IsSmoothOnSpaceTime (ξ w)) ∧
        ∀ z, Measurable (fun w => ξ w z) ∧
          (fun w => ξ w z) =ᵐ[P] Y z := by
  classical
  choose xi hxi_smooth hxi_eq using
    exists_smoothVersion_of_windowed_series_certificate
      hG hGae hX hSmooth hEq
  apply smoothVersion_patch_of_countable_dense hG hGae hU_open hU_cover
  · intro n w
    exact hxi_smooth n w
  · intro n z hz
    exact (hxi_eq n z hz).1
  · intro n z hz
    exact (hxi_eq n z hz).2
  · intro n m z hzn hzm
    filter_upwards [(hxi_eq n z hzn).2, (hxi_eq m z hzm).2] with w hn hm
    exact hn.trans hm.symm

end RegularityStructures.Phi43

end
