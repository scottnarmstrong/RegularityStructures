/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.MeasKGamma
public import RegularityStructures.Abstract.Integration.Theorem512.MeasPairing
public import RegularityStructures.Abstract.Integration.Theorem512.MeasurableShellPairing

/-!
# Measurability of `𝒦_γ f`

Under joint measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)`, the coefficients of `J(x)` and `N_γ`, and
`x ↦ 𝒦_γ f(x)`, are measurable (`Model.measurable_kGamma`).

Source: [Hai14, Theorem 5.12].
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup} {N : ℕ} {γ CPi CGam CI : ℝ} {P : PolynomialSector 𝒯 N'}
  {I : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)} {V : Submodule ℝ (ι → ℝ)}

theorem measurable_jCoeff (hJ : M.IsJointMeasurable) (hPi : M.PiBoundOn γ CPi univ)
    (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi) {i : ι} (hi : 𝒯.deg i < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) {k : Fin 4 →₀ ℕ}
    (hk : (multiDeg k : ℝ) < 𝒯.deg i + 2) :
    Measurable fun x => jCoeff M N x i k := by
  have hC : 0 ≤ max CGam 1 * CPi * Fintype.card ι :=
    mul_nonneg (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hCPi) (Nat.cast_nonneg _)
  have hterm : ∀ n : ℕ, Measurable fun x => derivShellPairing
      (fun t y => M.regPi x (Pi.single i 1) t y) (annKernel0 N) k x n := fun n =>
    measurable_derivShellPairing (fun x => regPi_single_mem_distributions M x i)
      (fun s hs => hJ i s hs) (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz)
      (degreesBelowLe_bounds 𝒯 hdeg i) hC
      (fun x => M.isLocalOrder_regPi_single hPi hGam hCPi hi x) k n
  exact measurable_tsum_of_summable hterm fun x =>
    summable_jCoeff_terms M N x i k hPi hGam hCPi hi hdeg hk

theorem measurable_nCoeff (hJ : M.IsJointMeasurable) {γ CPi Cf : ℝ} (hγ : 0 < γ)
    (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi) {f : ParabolicSpace → ι → ℝ}
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
    (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) {k : Fin 4 →₀ ℕ} (hk : (multiDeg k : ℝ) < γ + 2) :
    Measurable fun x => nCoeff M N f x k := by
  have hrec : ∀ s : ℝ, 0 < s → Measurable (M.reconstruct f s) := fun s hs => by
    have h : M.reconstruct f s = fun z => M.reconstructSubAt f 0 s z + M.regPi 0 (f 0) s z := by
      funext z; simp [Model.reconstructSubAt]
    rw [h]
    exact (M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf 0 hs).add
      (M.measurable_regPi 0 (f 0) hs)
  have hjoint : ∀ s : ℝ, 0 < s → Measurable fun p : ParabolicSpace × ParabolicSpace =>
      M.reconstructSubAt f p.1 s p.2 := fun s hs => by
    have h : (fun p : ParabolicSpace × ParabolicSpace => M.reconstructSubAt f p.1 s p.2) =
        fun p => M.reconstruct f s p.2 - ∑ i, f p.1 i * M.regPi p.1 (Pi.single i 1) s p.2 := by
      funext p; rw [Model.reconstructSubAt, M.regPi_eq_sum p.1 (f p.1) s p.2]
    rw [h]
    exact ((hrec s hs).comp measurable_snd).sub (Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp hf.1).comp measurable_fst).mul (hJ i s hs))
  have hterm : ∀ n : ℕ, Measurable fun x => derivShellPairing (M.reconstructSubAt f x)
      (annKernel0 N) k x n := fun n =>
    measurable_derivShellPairing (fun x => M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x)
      hjoint (contDiff_annKernel0 N) (fun _ hz => annKernel0_eq_zero N hz)
      (exponents_reconstructSubAt hγ hdeg)
      (mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
        (Nat.cast_nonneg _)) hCPi) hCf)
      (fun x => M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x) k n
  exact measurable_tsum_of_summable hterm fun x =>
    summable_nCoeff_terms M hγ hPi hCPi hf hfb hCf hdeg N x hk

theorem measurable_jVec (hJ : M.IsJointMeasurable) (hPi : M.PiBoundOn γ CPi univ)
    (hGam : M.GammaBoundOn γ CGam univ) (hCPi : 0 ≤ CPi) {i : ι} (hi : 𝒯.deg i < γ)
    (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j) :
    Measurable fun x => jVec M N P x i := by
  unfold jVec
  refine Finset.measurable_sum _ fun k _ => ?_
  split_ifs with hc
  · exact ((measurable_jCoeff hJ hPi hGam hCPi hi hdeg hc).div_const _).smul_const _
  · exact measurable_const

theorem measurable_nVec (hJ : M.IsJointMeasurable) (hγ : 0 < γ) {Cf : ℝ}
    (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi) {f : ParabolicSpace → ι → ℝ}
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
    (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) :
    Measurable fun x => nVec M N P γ f x := by
  unfold nVec
  refine Finset.measurable_sum _ fun k _ => ?_
  split_ifs with hc
  · exact ((measurable_nCoeff hJ hγ hPi hCPi hf hfb hCf hdeg hc).div_const _).smul_const _
  · exact measurable_const

/-- **Measurability of `𝒦_γ f`** (under joint measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)`). -/
theorem measurable_kGamma (hJ : M.IsJointMeasurable)
    (S : SchauderSetting M N γ P I V CPi CGam CI) {f : ParabolicSpace → ι → ℝ} {Cf : ℝ}
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) :
    Measurable fun x => kGamma M N P I γ f x := by
  have hdeg4 : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j := fun j hj => by linarith [S.deg_gt j hj]
  have hI : Measurable fun x => I (f x) :=
    (LinearMap.continuous_of_finiteDimensional I).measurable.comp hf.1
  have hj : Measurable fun x => jMap M N P x (f x) := by
    have h : (fun x => jMap M N P x (f x)) = fun x => ∑ i, f x i • jVec M N P x i := rfl
    rw [h]
    refine Finset.measurable_sum _ fun i _ => ?_
    by_cases hi : 𝒯.deg i < γ
    · exact ((measurable_pi_apply i).comp hf.1).smul
        (measurable_jVec hJ S.piBound S.gammaBound S.piBound_nonneg hi hdeg4)
    · have h0 : (fun x => f x i • jVec M N P x i) = fun _ => 0 :=
        funext fun x => by rw [hf.2.1 x i (not_lt.1 hi), zero_smul]
      rw [h0]
      exact measurable_const
  exact (hI.add hj).add (measurable_nVec hJ S.pos S.piBound S.piBound_nonneg hf hfb hCf hdeg4)

end Model

end RegularityStructures

end
