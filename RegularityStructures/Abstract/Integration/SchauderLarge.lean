/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.SchauderBracket

/-!
# Multilevel Schauder: the large-scale form of the series

`polyU_eq_large`: for every `n`,
`polyU n = ⟨Rf − Π_x f(x), K^{k,γ}_{n;xy}⟩ − ∑_{i : |k| ≥ deg i + 2} τ_i ⟨Π_y e_i, D^k K_n(y−·)⟩`
([Hai14, (5.48)]), from `Rf − Π_y f(y) = (Rf − Π_x f(x)) − Π_y τ`.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {γ CPi CGam Cf : ℝ}

theorem reconstructSubAt_eq_sub (f : ParabolicSpace → ι → ℝ) (x y : ParabolicSpace) (t : ℝ)
    (z : ParabolicSpace) :
    M.reconstructSubAt f y t z = M.reconstructSubAt f x t z -
      M.regPi y (f y - M.gammaMap y x (f x)) t z := by
  unfold reconstructSubAt
  rw [M.regPi_sub, M.regPi_gammaMap]
  ring

theorem polyU_eq_large (hγ : 0 < γ) (hdeg : ∀ j, 𝒯.deg j < γ → -2 < 𝒯.deg j)
    (hPi : M.PiBoundOn γ CPi univ) (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi)
    {f : ParabolicSpace → ι → ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) (N : ℕ) (x y : ParabolicSpace)
    (k : Fin 4 →₀ ℕ) (n : ℕ) :
    polyU M N γ f x y k n =
      parabolicSemigroup.pairing (M.reconstructSubAt f x)
        (dTaylorKernel (annKernel0 N) k n (γ + 2 - multiDeg k) x y) -
      ∑ i ∈ Finset.univ.filter (fun i => ¬ (multiDeg k : ℝ) < 𝒯.deg i + 2),
        (f y - M.gammaMap y x (f x)) i *
          derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n := by
  classical
  have hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [hdeg j hj]
  set τ := f y - M.gammaMap y x (f x) with hτ
  have hτl : τ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ (hf.2.1 y) ((M.isGradedUnipotent_gammaMap y x).map_lowerSubspace
      (hf.2.1 x))
  set g := scaledShell (annKernel0 N) n with hg
  set φ : ParabolicSpace → ℝ := fun z => lineIter (multiDirs k) g (y - z) with hφ
  set F : Finset ι := Finset.univ.filter (fun i => τ i ≠ 0) with hF
  have hFlt : ∀ i ∈ F, 𝒯.deg i < γ := by
    intro i hi
    by_contra hge
    exact (Finset.mem_filter.1 hi).2 (hτl i (not_lt.1 hge))
  -- local orders
  have hlocx := M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x
  have hAx := exponents_reconstructSubAt hγ hdeg4
  have hCx : 0 ≤ (modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf :=
    mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
      (Nat.cast_nonneg _)) hCPi) hCf
  have hCw : 0 ≤ max CGam 1 * CPi * Fintype.card ι :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _)
  have hh0 := contDiff_annKernel0 N
  have hhs : ∀ z, 1 < parabolicNorm z → annKernel0 N z = 0 := fun _ hz => annKernel0_eq_zero N hz
  have hcont : Continuous φ ∧ HasCompactSupport φ :=
    ⟨(contDiff_lineIter (contDiff_scaledShell hh0 n) _).continuous.comp
        (continuous_const.sub continuous_id),
      hasCompactSupport_reflect (hasCompactSupport_lineIter
        (hasCompactSupport_scaledShell hhs n) _) y⟩
  have hLDx : parabolicSemigroup.LocalData (M.reconstructSubAt f x) x γ
      (insert γ (𝒯.degreesBelow γ)) _ := ⟨M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x,
    fun _ hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu, hCx,
    fun a ha => (hAx a ha).2, hlocx⟩
  have hLDi : ∀ i ∈ F, parabolicSemigroup.LocalData (fun t z => M.regPi y (Pi.single i 1) t z) y
      (𝒯.deg i) (𝒯.degreesBelowLe γ (𝒯.deg i)) (max CGam 1 * CPi * Fintype.card ι) := by
    intro i hi
    exact ⟨M.regPi_mem y _, fun _ hu => M.measurable_regPi y _ hu, hCw,
      fun a ha => (degreesBelowLe_bounds 𝒯 hdeg4 i a ha).2,
      M.isLocalOrder_regPi_single hPi hGam hCPi (hFlt i hi) y⟩
  -- the limit for `Λ_y`
  have hlim := tendsto_integral_sub_sum_left (F := F)
    (Λ₀ := M.reconstructSubAt f x) (Λ := fun i t z => M.regPi y (Pi.single i 1) t z)
    (fun i => τ i) (φ := φ)
    (tendsto_dShell_centre (M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x)
      (fun _ hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu) hh0 hhs
      hAx hCx hlocx k n)
    (fun i hi => (tendsto_and_abs_pairing_word_scaledShell_le (M.regPi_mem y _)
      (fun _ hu => M.measurable_regPi y _ hu) hh0 hhs
      (degreesBelowLe_bounds 𝒯 hdeg4 i) hCw
      (M.isLocalOrder_regPi_single hPi hGam hCPi (hFlt i hi) y)
      ((Finsupp.toMultiset k).toList) n).1)
    (fun s hs' => integrable_mul_of_hasCompactSupport hLDx hs' hcont.1 hcont.2)
    (fun i hi s hs' => integrable_mul_of_hasCompactSupport (hLDi i hi) hs' hcont.1 hcont.2)
  have hΛy : ∀ t z, M.reconstructSubAt f y t z = M.reconstructSubAt f x t z -
      ∑ i ∈ F, τ i * M.regPi y (Pi.single i 1) t z := by
    intro t z
    rw [reconstructSubAt_eq_sub f x y t z, M.regPi_eq_sum, ← hτ]
    congr 1
    rw [hF, Finset.sum_filter_of_ne]
    intro i _ hne h0
    exact hne (by rw [h0, zero_mul])
  have hb : parabolicSemigroup.pairing (M.reconstructSubAt f y) φ =
      parabolicSemigroup.pairing (M.reconstructSubAt f x) φ -
        ∑ i ∈ F, τ i * parabolicSemigroup.pairing
          (fun t z => M.regPi y (Pi.single i 1) t z) φ := by
    refine parabolicSemigroup.pairing_eq_of_tendsto ?_
    refine hlim.congr fun s => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hΛy]
  have hP := pairing_dTaylorKernel_eq (M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x)
    (fun _ hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu) hh0 hhs
    (x := x) (y := y) hAx hCx hlocx k n (γ + 2 - multiDeg k)
  rw [hP]
  unfold polyU
  have hF1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι)
    (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2)
    (fun i => τ i * derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z)
      (annKernel0 N) k y n)
  have hFF : ∑ i ∈ F, τ i * derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z)
      (annKernel0 N) k y n = ∑ i, τ i * derivShellPairing
        (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n := by
    rw [hF, Finset.sum_filter_of_ne]
    intro i _ hne h0
    exact hne (by rw [h0, zero_mul])
  have hb' : derivShellPairing (M.reconstructSubAt f y) (annKernel0 N) k y n =
      parabolicSemigroup.pairing (M.reconstructSubAt f x) φ - ∑ i ∈ F, τ i *
        derivShellPairing (fun t z => M.regPi y (Pi.single i 1) t z) (annKernel0 N) k y n := hb
  rw [hb', hFF, ← hF1]
  have hsub : ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
      parabolicSemigroup.pairing (M.reconstructSubAt f x)
        (fun z => lineIter (multiDirs (k + l)) (scaledShell (annKernel0 N) n) (x - z)) =
      ∑ l ∈ taylorIdx (γ + 2 - multiDeg k), coeffT (parabolicCoords (y - x)) l *
        derivShellPairing (M.reconstructSubAt f x) (annKernel0 N) (k + l) x n := rfl
  rw [hsub]
  have : parabolicSemigroup.pairing (M.reconstructSubAt f x) φ =
      parabolicSemigroup.pairing (M.reconstructSubAt f x)
        (fun z => lineIter (multiDirs k) (scaledShell (annKernel0 N) n) (y - z)) := rfl
  rw [this]
  ring

end Model

end RegularityStructures

end
