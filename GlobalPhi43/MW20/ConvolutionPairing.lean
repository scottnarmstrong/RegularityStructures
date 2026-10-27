module

public import GlobalPhi43.MW20.ConvolutionComposition
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import RegularityStructures.Analysis.Parabolic.TestFunction

/-!
# Reflected smoothing and density convolution
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- Pairing the averaged density with a bounded continuous field moves the
same probability average onto that field. The plus sign is the project's
past-looking convention. -/
theorem integral_probabilityConvolution_mul (ν : Measure ParabolicSpace)
    [IsProbabilityMeasure ν] (k g : ParabolicSpace →ᵇ ℝ) (hk : Integrable k) :
    (∫ x, probabilityConvolution ν k x * g x) =
      ∫ y, (∫ x, k x * g (x + y)) ∂ν := by
  have : Measure.IsAddHaarMeasure (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hc : Continuous (fun p : ParabolicSpace × ParabolicSpace => k (p.1 - p.2) * g p.1) :=
    (k.continuous.comp (continuous_fst.sub continuous_snd)).mul
      (g.continuous.comp continuous_fst)
  have hs : ∀ y : ParabolicSpace, Integrable (fun x => k (x - y) * g x) := by
    intro y
    exact (hk.comp_sub_right y).mul_bdd g.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => g.norm_coe_le_norm x)
  have hprod : Integrable (fun p : ParabolicSpace × ParabolicSpace =>
      k (p.1 - p.2) * g p.1) (volume.prod ν) := by
    apply (integrable_prod_iff' hc.stronglyMeasurable.aestronglyMeasurable).2
    refine ⟨ae_of_all _ hs, ?_⟩
    apply (integrable_const (‖g‖ * ∫ x, ‖k x‖) : Integrable (fun _ : ParabolicSpace => _) ν).mono'
      hc.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    apply ae_of_all
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc
      _ ≤ ∫ x, ‖g‖ * ‖k (x - y)‖ := by
        apply integral_mono_ae (hs y).norm ((hk.comp_sub_right y).norm.const_mul ‖g‖)
        exact ae_of_all _ fun x => by
          change ‖k (x - y) * g x‖ ≤ ‖g‖ * ‖k (x - y)‖
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun x : ParabolicSpace => ‖k x‖) y
  calc
    _ = ∫ x, ∫ y, k (x - y) * g x ∂ν := by
      simp only [probabilityConvolution_apply, integral_mul_const]
    _ = ∫ y, (∫ x, k (x - y) * g x) ∂ν := integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      simpa only [add_sub_cancel_right] using!
        (integral_add_right_eq_self (μ := volume) (fun x => k (x - y) * g x) y).symm

end GlobalPhi43.MW20
