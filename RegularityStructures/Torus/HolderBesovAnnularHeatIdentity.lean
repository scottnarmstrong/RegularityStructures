/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovMultiplierAction
public import RegularityStructures.Torus.HolderBesovAnnulusTensor
public import RegularityStructures.Torus.HolderBesovHeatDerivativeProfiles
public import RegularityStructures.Torus.HolderBesovHeatReconstruction

/-!
# Exact composition identity for annular heat regularisation

On the literal dyadic polynomial, convolution with each Green kernel followed by its
coordinate-weighted heat kernel reproduces the heat operator, up to the explicit inverse frequency
power. This identity supplies the operator composition step in the equivalence of the heat norm
(2.3) of the statement with the Littlewood--Paley norm.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus

namespace RegularityStructures

/-- The existing weighted heat kernel bundled as a continuous torus function. -/
def torusWeightedHeatKernelMap (M : ℕ) (i : Fin 3) (s : ℝ) (hs : 0 < s) : C(Torus3, ℂ) :=
  ⟨torusWeightedHeatKernel M i (Real.sqrt s)⁻¹,
    continuous_torusWeightedHeatKernel M i (inv_pos.mpr (Real.sqrt_pos.mpr hs))⟩

/-- One of the three Green/weighted-heat composition terms for a dyadic block. -/
def torusAnnularHeatTerm (M : ℕ) (i : Fin 3) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (f : C(Torus3, ℝ)) : C(Torus3, ℂ) :=
  torusMultiplierAction (torusWeightedHeatKernelMap M i s hs)
    (torusMultiplierAction (torusLPAnnulusGreenKernel M i n) (torusLittlewoodPaleyBlock (n + 1) f))

theorem torusLPAnnulusGreenKernel_fourierCoeff (M : ℕ) (i : Fin 3) (n : ℕ) (k : Fin 3 → ℤ) :
    mFourierCoeff (torusLPAnnulusGreenKernel M i n) k =
      ∏ j : Fin 3, torusLPAnnulusFactor M i j ((k j : ℝ) / (2 : ℝ) ^ (n + 2)) := by
  have he : (torusLPAnnulusGreenKernel M i n : Torus3 → ℂ) = fun x =>
      ∏ j : Fin 3, ∑' l : ℤ,
        torusLPAnnulusFactor M i j ((l : ℝ) / (2 : ℝ) ^ (n + 2)) * fourier l (x j) := by
    funext x
    exact torusTensorFiniteKernel_apply (torusLPAnnulusFactor M i)
      (fun j _ hu => torusLPAnnulusFactor_eq_zero M i j hu) (n + 2) x
  rw [he]
  exact mFourierCoeff_schwartz_tensor_multiplier _ (pow_pos (by norm_num) _) k

private theorem heatOp_complex_smul (s : ℝ) (c : ℂ) (g : C(Torus3, ℂ)) :
    PDE.heatOp s (c • g) = c • PDE.heatOp s g := by
  ext x
  simp only [PDE.heatOp_apply, ContinuousMap.smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm _ _ _

private theorem heatOp_sum {ι : Type*} (s : ℝ) (S : Finset ι) (g : ι → C(Torus3, ℂ)) :
    PDE.heatOp s (∑ j ∈ S, g j) = ∑ j ∈ S, PDE.heatOp s (g j) :=
  map_sum (PDE.heatOpCLM (E := ℂ) s) g S

private theorem annular_coeff_algebra (p : ℕ) (A d c E : ℂ) (B q : Fin 3 → ℂ)
    (hr : (∑ i : Fin 3, B i * (q i / A) ^ p) * d = d) :
    (d * c) * E = (A⁻¹) ^ p * ∑ i : Fin 3, ((d * c) * B i) * (q i ^ p * E) := by
  have hsum : (∑ i : Fin 3, B i * (q i / A) ^ p) =
      (A⁻¹) ^ p * ∑ i : Fin 3, B i * q i ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_eq_mul_inv, mul_pow]
    ring
  have hsum' : (∑ i : Fin 3, ((d * c) * B i) * (q i ^ p * E)) =
      (∑ i : Fin 3, B i * q i ^ p) * (d * c * E) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hr
  calc
    _ = (((A⁻¹) ^ p * ∑ i : Fin 3, B i * q i ^ p) * d) * c * E := by rw [hr]
    _ = _ := by rw [hsum']; ring

private theorem annular_term_fourier (M : ℕ) (i : Fin 3) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (f : C(Torus3, ℝ)) :
    torusAnnularHeatTerm M i n s hs f = ∑ k ∈ torusLPFrequencyBox (n + 1),
      (((torusDyadicFrequencySymbol (n + 1) k : ℂ) *
        mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k) *
        (∏ j : Fin 3, torusLPAnnulusFactor M i j ((k j : ℝ) / (2 : ℝ) ^ (n + 2))) *
        ((k i : ℂ) ^ (2 * M) *
          ∏ j : Fin 3, Complex.exp ((-4 * Real.pi ^ 2 * s * (k j : ℝ) ^ 2 : ℝ) : ℂ))) •
        mFourier k := by
  unfold torusAnnularHeatTerm torusLittlewoodPaleyBlock
  rw [torusMultiplierAction_fourierSum, torusMultiplierAction_fourierSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [torusLPAnnulusGreenKernel_fourierCoeff]
  simp only [torusWeightedHeatKernelMap, ContinuousMap.coe_mk]
  rw [mFourierCoeff_torusWeightedHeatKernel_time M i hs k]
  simp only [Complex.ofReal_exp]

theorem heatOp_torusLittlewoodPaleyBlock_succ_eq_annular (M n : ℕ) (s : ℝ) (hs : 0 < s)
    (f : C(Torus3, ℝ)) :
    PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f) =
      ((((2 : ℝ) ^ (n + 2))⁻¹ : ℝ) : ℂ) ^ (2 * M) •
        ∑ i : Fin 3, torusAnnularHeatTerm M i n s hs f := by
  conv_lhs => unfold torusLittlewoodPaleyBlock
  rw [heatOp_sum]
  simp_rw [heatOp_complex_smul, heatOp_mFourier hs, smul_smul, annular_term_fourier]
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul, smul_smul]
  congr 1
  have hr : (∑ i : Fin 3,
      (∏ j : Fin 3, torusLPAnnulusFactor M i j ((k j : ℝ) / (2 : ℝ) ^ (n + 2))) *
        ((k i : ℂ) / (((2 : ℝ) ^ (n + 2) : ℝ) : ℂ)) ^ (2 * M)) *
      (torusDyadicFrequencySymbol (n + 1) k : ℂ) =
        (torusDyadicFrequencySymbol (n + 1) k : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_intCast] using
      torusLPAnnulusGreen_symbol_identity M n k
  simpa only [Complex.ofReal_inv] using annular_coeff_algebra (2 * M)
    (((2 : ℝ) ^ (n + 2) : ℝ) : ℂ) (torusDyadicFrequencySymbol (n + 1) k : ℂ)
    (mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k)
    (∏ j : Fin 3, Complex.exp ((-4 * Real.pi ^ 2 * s * (k j : ℝ) ^ 2 : ℝ) : ℂ))
    (fun i => ∏ j : Fin 3, torusLPAnnulusFactor M i j ((k j : ℝ) / (2 : ℝ) ^ (n + 2)))
    (fun i => (k i : ℂ)) hr

end RegularityStructures

end
