/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCalculus
public import RegularityStructures.Probability.GaussianVector

/-!
# Linear consequences of the white-noise axioms

The definition of `IsWhiteNoise` gives the finite-dimensional centred Gaussian laws and their
covariances, but does not assert pointwise linearity of the indexed family.  The following
theorems record the needed `L²` linearity consequences.  They are used when two cylindrical
representations are put over a common list of test functions.  See [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem ae_eq_zero_of_integral_sq_zero {P : Measure Ω} {u : Ω → ℝ}
    (hu : Integrable (fun ω => u ω ^ 2) P)
    (hzero : ∫ ω, u ω ^ 2 ∂P = 0) : u =ᵐ[P] 0 := by
  have hnonneg : 0 ≤ᵐ[P] (fun ω => u ω ^ 2) := Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  have hsq : (fun ω => u ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hu).mp hzero
  filter_upwards [hsq] with ω hω
  exact (sq_eq_zero_iff.mp hω)

theorem whiteNoise_zero_ae {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) : W (0 : SpaceTime → ℝ) =ᵐ[P] 0 := by
  have hX := hW.2 1 (fun _ : Fin 1 => (0 : SpaceTime → ℝ)) (fun _ => MemLp.zero)
  have hmem : MemLp (fun ω => W (0 : SpaceTime → ℝ) ω) 2 P := by
    simpa using hX.memLp_two_apply (0 : Fin 1)
  have hzero : ∫ ω, (W (0 : SpaceTime → ℝ) ω) ^ 2 ∂P = 0 := by
    simpa [pow_two] using hX.integral_mul (0 : Fin 1) (0 : Fin 1)
  exact ae_eq_zero_of_integral_sq_zero hmem.integrable_sq hzero

theorem whiteNoise_add_ae {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {h k : SpaceTime → ℝ}
    (hh : MemLp h 2) (hk : MemLp k 2) :
    W (h + k) =ᵐ[P] W h + W k := by
  let hv : Fin 3 → SpaceTime → ℝ := ![h + k, h, k]
  let a : Fin 3 → ℝ := ![1, -1, -1]
  have hmem : ∀ i, MemLp (hv i) 2 := by
    intro i
    fin_cases i
    · simpa [hv] using hh.add hk
    · simpa [hv] using hh
    · simpa [hv] using hk
  have hX := hW.2 3 hv hmem
  have hlin := hX.integral_linear_sq (σ := id) a
  have henergy := cylindrical_energy_eq_integral_sq (a := a) hmem
  have hsumcov :
      (∑ m, ∑ m', a m * a m' * (∫ z, hv (id m) z * hv (id m') z)) =
        covarianceEnergy (fun i j => ∫ z, hv i z * hv j z) a := by
    simp only [id_eq]
    unfold covarianceEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hright :
      (∑ m, ∑ m', a m * a m' * (∫ z, hv (id m) z * hv (id m') z)) =
        ∫ z, (∑ m, a m * hv (id m) z) ^ 2 := by
    calc
      _ = covarianceEnergy (fun i j => ∫ z, hv i z * hv j z) a := hsumcov
      _ = ∫ z, (∑ i, a i * hv i z) ^ 2 := henergy.symm
      _ = ∫ z, (∑ m, a m * hv (id m) z) ^ 2 := by simp only [id_eq]
  have hzero : ∫ ω, (∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) ^ 2 ∂P = 0 := by
    calc
      ∫ ω, (∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) ^ 2 ∂P =
          ∑ m, ∑ m', a m * a m' * (∫ z, hv (id m) z * hv (id m') z) := by
        simpa using hlin
      _ = ∫ z, (∑ m, a m * hv (id m) z) ^ 2 := hright
      _ = 0 := by
        have hzero_fun : (fun z => (∑ m, a m * hv (id m) z) ^ 2) =ᵐ[
            (volume : Measure SpaceTime)] 0 := by
          filter_upwards [] with z
          have hz : ∑ m, a m * hv (id m) z = 0 := by
            simp [Fin.sum_univ_succ, hv, a, id]
            ring
          rw [hz]
          norm_num
        exact integral_eq_zero_of_ae hzero_fun
  have hu : MemLp
      (fun ω => ∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) 2 P := by
    apply memLp_finsetSum
    intro m hm
    exact (hX.memLp_two_apply (id m)).const_mul _
  have hae := ae_eq_zero_of_integral_sq_zero hu.integrable_sq hzero
  filter_upwards [hae] with ω hω
  change (∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) = 0 at hω
  have hsum : ∑ m, a m * (fun ω k => W (hv k) ω) ω (id m) =
      W (h + k) ω - W h ω - W k ω := by
    simp [Fin.sum_univ_succ, hv, a, id]
    ring
  rw [hsum] at hω
  change W (h + k) ω = W h ω + W k ω
  linarith

theorem whiteNoise_smul_ae {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {c : ℝ} {h : SpaceTime → ℝ}
    (hh : MemLp h 2) :
    W (c • h) =ᵐ[P] c • W h := by
  let hv : Fin 2 → SpaceTime → ℝ := ![c • h, h]
  let a : Fin 2 → ℝ := ![1, -c]
  have hmem : ∀ i, MemLp (hv i) 2 := by
    intro i
    fin_cases i
    · simpa [hv] using hh.const_smul c
    · simpa [hv] using hh
  have hX := hW.2 2 hv hmem
  have hlin := hX.integral_linear_sq (σ := id) a
  have henergy := cylindrical_energy_eq_integral_sq (a := a) hmem
  have hsumcov :
      (∑ m, ∑ m', a m * a m' * (∫ z, hv (id m) z * hv (id m') z)) =
        covarianceEnergy (fun i j => ∫ z, hv i z * hv j z) a := by
    simp only [id_eq]
    unfold covarianceEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hright :
      (∑ m, ∑ m', a m * a m' * (∫ z, hv (id m) z * hv (id m') z)) =
        ∫ z, (∑ m, a m * hv (id m) z) ^ 2 := by
    calc
      _ = covarianceEnergy (fun i j => ∫ z, hv i z * hv j z) a := hsumcov
      _ = ∫ z, (∑ i, a i * hv i z) ^ 2 := henergy.symm
      _ = ∫ z, (∑ m, a m * hv (id m) z) ^ 2 := by simp only [id_eq]
  have hzero : ∫ ω, (∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) ^ 2 ∂P = 0 := by
    calc
      ∫ ω, (∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) ^ 2 ∂P =
          ∑ m, ∑ m', a m * a m' * (∫ z, hv (id m) z * hv (id m') z) := by
        simpa using hlin
      _ = ∫ z, (∑ m, a m * hv (id m) z) ^ 2 := hright
      _ = 0 := by
        have hzero_fun : (fun z => (∑ m, a m * hv (id m) z) ^ 2) =ᵐ[
            (volume : Measure SpaceTime)] 0 := by
          filter_upwards [] with z
          have hz : ∑ m, a m * hv (id m) z = 0 := by
            simp [Fin.sum_univ_succ, hv, a, id]
          rw [hz]
          norm_num
        exact integral_eq_zero_of_ae hzero_fun
  have hu : MemLp
      (fun ω => ∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) 2 P := by
    apply memLp_finsetSum
    intro m hm
    exact (hX.memLp_two_apply (id m)).const_mul _
  have hae := ae_eq_zero_of_integral_sq_zero hu.integrable_sq hzero
  filter_upwards [hae] with ω hω
  change (∑ m, a m * (fun ω k => W (hv k) ω) ω (id m)) = 0 at hω
  have hsum : ∑ m, a m * (fun ω k => W (hv k) ω) ω (id m) =
      W (c • h) ω - c * W h ω := by
    simp [Fin.sum_univ_succ, hv, a, id]
    ring
  rw [hsum] at hω
  change W (c • h) ω = c * W h ω
  linarith

end RegularityStructures

end
