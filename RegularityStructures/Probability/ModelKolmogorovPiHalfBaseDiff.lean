/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfBase
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.BlockEnvelope.Envelope
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellDiffBlock
public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeight

/-!
# Base-point cell weights, difference version
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

/-- The base difference weight `∫ E^n_s(x₀ - w) ‖(Q_s (Π_{x₀} - Π'_{x₀}) e_k)(w)‖ dw`. -/
def piHalfBaseDiffWeight (M M' : Model 𝒯 parabolicSemigroup) (n : ℕ) (s : ℝ)
    (x₀ : ParabolicSpace) (k : ι) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
    ‖M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w‖ₑ

end RegularityStructures

end

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- Chen at the base point for the difference of regularised fields. -/
theorem enorm_regPi_single_sub_le_base (M M' : Model 𝒯 parabolicSemigroup)
    (x₀ x w : ParabolicSpace) (i : ι) (s : ℝ) :
    ‖M.regPi x (Pi.single i 1) s w - M'.regPi x (Pi.single i 1) s w‖ₑ ≤
      ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
        (‖M.gammaMap x₀ x (Pi.single i 1) k‖ₑ *
            ‖M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w‖ₑ +
          ‖M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k‖ₑ *
            ‖M'.regPi x₀ (Pi.single k 1) s w‖ₑ) := by
  rw [← M.regPi_gammaMap x₀ x (Pi.single i 1) s w, ← M'.regPi_gammaMap x₀ x (Pi.single i 1) s w,
    M.regPi_eq_sum, M'.regPi_eq_sum, ← Finset.sum_sub_distrib]
  have hrew : ∑ k, (M.gammaMap x₀ x (Pi.single i 1) k * M.regPi x₀ (Pi.single k 1) s w -
      M'.gammaMap x₀ x (Pi.single i 1) k * M'.regPi x₀ (Pi.single k 1) s w) =
      ∑ k, (M.gammaMap x₀ x (Pi.single i 1) k *
          (M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w) +
        (M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k) *
          M'.regPi x₀ (Pi.single k 1) s w) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hrew]
  have hres : ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      (M.gammaMap x₀ x (Pi.single i 1) k *
          (M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w) +
        (M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k) *
          M'.regPi x₀ (Pi.single k 1) s w) =
      ∑ k, (M.gammaMap x₀ x (Pi.single i 1) k *
          (M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w) +
        (M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k) *
          M'.regPi x₀ (Pi.single k 1) s w) := by
    refine Finset.sum_filter_of_ne fun k _ hk => ?_
    by_contra hlt
    have h1 := M.gammaMap_single_apply_eq_zero_of_lt x₀ x (not_le.1 hlt) (k := i)
    have h2 := M'.gammaMap_single_apply_eq_zero_of_lt x₀ x (not_le.1 hlt) (k := i)
    exact hk (by rw [h1, h2]; ring)
  rw [← hres]
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (enorm_add_le _ _).trans ?_
  rw [enorm_mul, enorm_mul]

end Model

theorem exists_piHalfBase_block_bound_diff (n : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (M M' : Model 𝒯 parabolicSemigroup) (γ : ℝ) (i : ι), 𝒯.deg i < γ →
        ∀ {s u : ℝ}, 0 < s → u ∈ Set.Icc (2 * s) (4 * s) →
          ∀ (S : Set ParabolicSpace) (G Gd : ℝ), 0 ≤ G → 0 ≤ Gd → M.GammaBoundOn γ G S →
            Model.GammaDiffBoundOn M M' γ Gd S →
            ∀ x x₀ : ParabolicSpace, x ∈ S → x₀ ∈ S →
              parabolicNorm (x - x₀) ≤ s ^ (1 / 4 : ℝ) →
              (∀ k, Measurable (fun w => M.regPi x₀ (Pi.single k 1) s w)) →
              (∀ k, Measurable (fun w => M'.regPi x₀ (Pi.single k 1) s w)) →
                ‖M.regPi x (Pi.single i 1) u x - M'.regPi x (Pi.single i 1) u x‖ₑ ≤
                  ENNReal.ofReal C₀ *
                    ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
                      ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
                        (ENNReal.ofReal (1 + G) * piHalfBaseDiffWeight M M' n s x₀ k +
                          ENNReal.ofReal Gd * piHalfBaseWeight M' n s x₀ k) := by
  obtain ⟨C, hC, hb⟩ := exists_enorm_apply_le_blockEnvelope_lintegral n
  refine ⟨C * 2 ^ (4 * n), by positivity, ?_⟩
  intro M M' γ i hi s u hs hu S G Gd hG hGd hΓ hΓd x x₀ hx hx₀ hd hm hm'
  have hshift : ∀ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (4 * n)) *
        ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) := fun w => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (kernelBlockEnvelope_shift_le n hs hd)
  have hcoef : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ‖M.gammaMap x₀ x (Pi.single i 1) k‖ₑ ≤
        ENNReal.ofReal (1 + G) * ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4)) :=
    fun k hk => enorm_gammaMap_coeff_le M hG hΓ hi (Finset.mem_filter.1 hk).2 hs hx hx₀ hd
  have hcoefd : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      ‖M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k‖ₑ ≤
        ENNReal.ofReal Gd * ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4)) :=
    fun k hk => Model.enorm_gammaMap_sub_coeff_le M M' hGd hΓd hi (Finset.mem_filter.1 hk).2
      hs hx hx₀ hd
  have hE : Measurable (fun w : ParabolicSpace =>
      ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w))) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_kernelBlockEnvelope n s).comp (measurable_const.sub measurable_id))
  have hgD : ∀ k, AEMeasurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
      ‖M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w‖ₑ) volume := fun k =>
    hE.aemeasurable.mul ((hm k).sub (hm' k)).enorm.aemeasurable
  have hg' : ∀ k, AEMeasurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
      ‖M'.regPi x₀ (Pi.single k 1) s w‖ₑ) volume := fun k =>
    hE.aemeasurable.mul (hm' k).enorm.aemeasurable
  have hmeas : ∀ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
      AEMeasurable (fun w =>
        ‖M.gammaMap x₀ x (Pi.single i 1) k‖ₑ * (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
          ‖M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w‖ₑ) +
        ‖M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k‖ₑ *
          (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
            ‖M'.regPi x₀ (Pi.single k 1) s w‖ₑ)) volume := fun k _ =>
    ((hgD k).const_mul _).add ((hg' k).const_mul _)
  calc ‖M.regPi x (Pi.single i 1) u x - M'.regPi x (Pi.single i 1) u x‖ₑ
      ≤ ENNReal.ofReal C * ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
          ‖M.regPi x (Pi.single i 1) s w - M'.regPi x (Pi.single i 1) s w‖ₑ :=
        hb (parabolicSemigroup.distributions.sub_mem (M.regPi_mem x (Pi.single i 1))
          (M'.regPi_mem x (Pi.single i 1))) s hs u hu x
    _ ≤ ENNReal.ofReal C * ∫⁻ w, ENNReal.ofReal ((2 : ℝ) ^ (4 * n)) *
          ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
            (‖M.gammaMap x₀ x (Pi.single i 1) k‖ₑ *
                (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
                  ‖M.regPi x₀ (Pi.single k 1) s w - M'.regPi x₀ (Pi.single k 1) s w‖ₑ) +
              ‖M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k‖ₑ *
                (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
                  ‖M'.regPi x₀ (Pi.single k 1) s w‖ₑ)) := by
        refine mul_le_mul_right (lintegral_mono fun w => ?_) _
        calc _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ (4 * n)) *
              ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w))) * _ :=
              mul_le_mul' (hshift w) (M.enorm_regPi_single_sub_le_base M' x₀ x w i s)
          _ = _ := by
              rw [mul_assoc]
              congr 1
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun k _ => by ring
    _ = ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ (4 * n)) *
          ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
            (‖M.gammaMap x₀ x (Pi.single i 1) k‖ₑ * piHalfBaseDiffWeight M M' n s x₀ k +
              ‖M.gammaMap x₀ x (Pi.single i 1) k - M'.gammaMap x₀ x (Pi.single i 1) k‖ₑ *
                piHalfBaseWeight M' n s x₀ k)) := by
        congr 1
        rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ hmeas),
          lintegral_finsetSum' _ hmeas]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_mul_add_mul_of_aemeasurable _ _ (hgD k) (hg' k)
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal ((2 : ℝ) ^ (4 * n)) *
          ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i),
            ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4)) *
              (ENNReal.ofReal (1 + G) * piHalfBaseDiffWeight M M' n s x₀ k +
                ENNReal.ofReal Gd * piHalfBaseWeight M' n s x₀ k)) := by
        refine mul_le_mul' le_rfl (mul_le_mul' le_rfl (Finset.sum_le_sum fun k hk => ?_))
        calc _ ≤ (ENNReal.ofReal (1 + G) * ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4))) *
                piHalfBaseDiffWeight M M' n s x₀ k +
              (ENNReal.ofReal Gd * ENNReal.ofReal (s ^ ((𝒯.deg i - 𝒯.deg k) / 4))) *
                piHalfBaseWeight M' n s x₀ k :=
              add_le_add (mul_le_mul' (hcoef k hk) le_rfl) (mul_le_mul' (hcoefd k hk) le_rfl)
          _ = _ := by ring
    _ = _ := by
        rw [ENNReal.ofReal_mul hC]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

end RegularityStructures

end
