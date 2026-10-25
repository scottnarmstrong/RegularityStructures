/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateYoung
public import Phi43.Stochastic.ConstantsRateMemLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Correlations of `Lᵖ` functions on `ℝ × T³`

`corr u v (z) = ∫ u(z + w) v(w) dw`.  For conjugate exponents the integrand is integrable for
every `z` and `‖corr u v z‖ ≤ ‖u‖ₚ ‖v‖_q`; for `u, v ∈ L^{3/2}` Young's inequality gives
`corr u v ∈ L³`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

/-- The correlation `z ↦ ∫ u(z + w) v(w) dw`. -/
def constantsRateCorr (u v : SpaceTime → ℝ) (z : SpaceTime) : ℝ := ∫ w, u (z + w) * v w

theorem constantsRate_memLp_shift {u : SpaceTime → ℝ} {p : ENNReal} (hu : MemLp u p)
    (z : SpaceTime) : MemLp (fun w => u (z + w)) p ∧
      eLpNorm (fun w => u (z + w)) p = eLpNorm u p := by
  have hmp : MeasurePreserving (fun w : SpaceTime => z + w) volume volume :=
    measurePreserving_add_left volume z
  have h' : eLpNorm (fun w => u (z + w)) p = eLpNorm u p :=
    eLpNorm_comp_measurePreserving (p := p) hu.aestronglyMeasurable hmp
  exact ⟨by rw [memLp_iff, h']; exact hu, h'⟩

theorem constantsRate_corr_bound {u v : SpaceTime → ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hu : MemLp u (ENNReal.ofReal p)) (hv : MemLp v (ENNReal.ofReal q)) (z : SpaceTime) :
    Integrable (fun w => u (z + w) * v w) ∧
      ‖∫ w, u (z + w) * v w‖ₑ ≤ eLpNorm u (ENNReal.ofReal p) * eLpNorm v (ENNReal.ofReal q) := by
  have hH : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 := hpq.ennrealOfReal
  obtain ⟨huz, hnorm⟩ := constantsRate_memLp_shift hu z
  have hint : Integrable ((fun w => u (z + w)) * v) :=
    huz.integrable_mul hv
  refine ⟨hint, ?_⟩
  calc
    ‖∫ w, u (z + w) * v w‖ₑ ≤ ∫⁻ w, ‖u (z + w) * v w‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun w => u (z + w) * v w) 1 volume :=
      (eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable).symm
    _ ≤ eLpNorm (fun w => u (z + w)) (ENNReal.ofReal p) volume *
          eLpNorm v (ENNReal.ofReal q) volume :=
      eLpNorm_smul_le_mul_eLpNorm huz.aestronglyMeasurable hv.aestronglyMeasurable
    _ = _ := by rw [hnorm]

theorem constantsRate_eLpNorm_eq {f : SpaceTime → ℝ} (hf : AEStronglyMeasurable f volume)
    {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) volume = (∫⁻ z, ‖f z‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le]

theorem constantsRate_lintegral_ne_top {f : SpaceTime → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p)) : ∫⁻ z, ‖f z‖ₑ ^ p ≠ ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf
  rw [ENNReal.toReal_ofReal hp.le] at h
  exact h.ne

theorem constantsRate_corr_young {u v : SpaceTime → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu' : MemLp u (ENNReal.ofReal (3 / 2))) (hv' : MemLp v (ENNReal.ofReal (3 / 2))) :
    (∀ᵐ z : SpaceTime ∂volume, Integrable (fun w => u (z + w) * v w)) ∧
      MemLp (constantsRateCorr u v) (ENNReal.ofReal 3) ∧
      eLpNorm (constantsRateCorr u v) (ENNReal.ofReal 3) ≤
        eLpNorm u (ENNReal.ofReal (3 / 2)) * eLpNorm v (ENNReal.ofReal (3 / 2)) := by
  have hFu := constantsRate_lintegral_ne_top (by norm_num : (0 : ℝ) < 3 / 2) hu'
  have hFv := constantsRate_lintegral_ne_top (by norm_num : (0 : ℝ) < 3 / 2) hv'
  have hY := constantsRate_young_lintegral hu hv hFu hFv
  set Θ : SpaceTime → ℝ≥0∞ := fun z => ∫⁻ w, ‖u (z + w)‖ₑ * ‖v w‖ₑ with hΘ
  have hmeas2 : Measurable (fun x : SpaceTime × SpaceTime => ‖u (x.1 + x.2)‖ₑ * ‖v x.2‖ₑ) :=
    ((hu.comp (measurable_fst.add measurable_snd)).enorm).mul ((hv.comp measurable_snd).enorm)
  have hΘm : Measurable Θ := hmeas2.lintegral_prod_right'
  have hfin : ∫⁻ z, Θ z ^ (3 : ℝ) < ⊤ := by
    refine hY.trans_lt ?_
    exact ENNReal.pow_lt_top (ENNReal.mul_lt_top hFu.lt_top hFv.lt_top)
  have hΘ3 : ∀ᵐ z : SpaceTime ∂volume, Θ z ^ (3 : ℝ) < ⊤ :=
    ae_lt_top' (hΘm.pow_const _).aemeasurable hfin.ne
  have hΘlt : ∀ᵐ z : SpaceTime ∂volume, Θ z < ⊤ := by
    filter_upwards [hΘ3] with z hz
    by_contra h
    have : Θ z = ⊤ := not_lt_top_iff.mp h
    rw [this] at hz
    simp at hz
  refine ⟨?_, ?_⟩
  · filter_upwards [hΘlt] with z hz
    refine ⟨((hu.comp (measurable_const.add measurable_id)).mul hv).aestronglyMeasurable, ?_⟩
    simpa [HasFiniteIntegral, enorm_mul, hΘ] using hz
  have hcm : AEStronglyMeasurable (constantsRateCorr u v) volume := by
    have h1 : StronglyMeasurable (fun x : SpaceTime × SpaceTime => u (x.1 + x.2) * v x.2) :=
      ((hu.comp (measurable_fst.add measurable_snd)).mul (hv.comp measurable_snd)).stronglyMeasurable
    exact (h1.integral_prod_right').aestronglyMeasurable
  have hbd : ∫⁻ z, ‖constantsRateCorr u v z‖ₑ ^ (3 : ℝ) ≤ ∫⁻ z, Θ z ^ (3 : ℝ) := by
    apply lintegral_mono
    intro z
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    calc
      ‖constantsRateCorr u v z‖ₑ ≤ ∫⁻ w, ‖u (z + w) * v w‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = Θ z := by simp [hΘ, enorm_mul]
  have hnorm : eLpNorm (constantsRateCorr u v) (ENNReal.ofReal 3) ≤
      eLpNorm u (ENNReal.ofReal (3 / 2)) * eLpNorm v (ENNReal.ofReal (3 / 2)) := by
    rw [constantsRate_eLpNorm_eq hcm (by norm_num), constantsRate_eLpNorm_eq hu'.aestronglyMeasurable
      (by norm_num), constantsRate_eLpNorm_eq hv'.aestronglyMeasurable (by norm_num)]
    calc
      (∫⁻ z, ‖constantsRateCorr u v z‖ₑ ^ (3 : ℝ)) ^ (1 / 3 : ℝ) ≤
          (((∫⁻ z, ‖u z‖ₑ ^ (3 / 2 : ℝ)) * ∫⁻ z, ‖v z‖ₑ ^ (3 / 2 : ℝ)) ^ (2 : ℕ)) ^
            (1 / 3 : ℝ) :=
        ENNReal.rpow_le_rpow (hbd.trans hY) (by norm_num)
      _ = (∫⁻ z, ‖u z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) *
          (∫⁻ z, ‖v z‖ₑ ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  refine ⟨?_, hnorm⟩
  rw [memLp_iff]
  refine hnorm.trans_lt ?_
  exact ENNReal.mul_lt_top hu' hv'

end RegularityStructures.Phi43

end
