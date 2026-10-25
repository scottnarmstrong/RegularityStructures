/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.AnnealedNoiseTorus

/-!
# Almost-sure linearity of a Gaussian white-noise family

The definition of `IsWhiteNoise` specifies the joint centred Gaussian law and covariance of every
finite family of pairings.  Those finite-dimensional laws force the family to be linear almost
everywhere: the variance of `W (h + g) - W h - W g` and of `W (a • h) - a * W h` is zero.  These
identities are the probabilistic bridge needed when a spatial heat convolution is rewritten as a
single white-noise pairing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

private theorem ae_eq_of_integral_sq_eq_zero {f : Ω → ℝ}
    (_hf : Measurable f) (hfi : Integrable (fun ω => f ω ^ 2) P)
    (hzero : ∫ ω, f ω ^ 2 ∂P = 0) : f =ᵐ[P] 0 := by
  have hsq : (fun ω => f ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (f ω)) hfi).mp hzero
  filter_upwards [hsq] with ω hω
  exact sq_eq_zero_iff.mp (by simpa using hω)

private theorem integral_linear_sq_eq_covariance_sum {ι : Type*} [Fintype ι]
    {f : ι → SpaceTime → ℝ} (hf : ∀ i, MemLp (f i) 2) (a : ι → ℝ) :
    ∫ z, (∑ i, a i * f i z) ^ 2 =
      ∑ i, ∑ j, a i * a j * ∫ z, f i z * f j z := by
  have hpt : ∀ z, (∑ i, a i * f i z) ^ 2 =
      ∑ i, ∑ j, a i * a j * (f i z * f j z) := by
    intro z
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hpt]
  change ∫ z, ∑ i, ∑ j, a i * a j * ((f i * f j) z) = _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hf i).integrable_mul (hf j)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hf i).integrable_mul (hf j)).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  simp only [Pi.mul_apply]

theorem whiteNoise_add_ae_fun (hW : IsWhiteNoise P W)
    {h g : SpaceTime → ℝ} (hh : MemLp h 2) (hg : MemLp g 2) :
    W (h + g) =ᵐ[P] fun ω => W h ω + W g ω := by
  have hsum : MemLp (h + g) 2 := hh.add hg
  have hvec := hW.2 3 ![h + g, h, g] (by
    intro i
    fin_cases i
    · simpa using hsum
    · simpa using hh
    · simpa using hg)
  have hsq := hvec.integral_linear_sq ![0, 1, 2] ![1, -1, -1]
  have hdet := integral_linear_sq_eq_covariance_sum
    (f := ![h + g, h, g]) (by
      intro i
      fin_cases i
      · simpa using hsum
      · simpa using hh
      · simpa using hg) ![1, -1, -1]
  have hsq_zero : ∫ ω, (W (h + g) ω - W h ω - W g ω) ^ 2 ∂P = 0 := by
    calc
      _ = ∫ ω, (∑ m, ![1, -1, -1] m *
          W (![h + g, h, g] (![0, 1, 2] m)) ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        norm_num [Fin.sum_univ_succ]
        ring
      _ = _ := hsq
      _ = ∫ z, (∑ m, ![1, -1, -1] m * ![h + g, h, g] m z) ^ 2 := hdet.symm
      _ = 0 := integral_eq_zero_of_ae <| Filter.Eventually.of_forall fun z => by
        norm_num [Fin.sum_univ_succ]
        ring
  have hfi : Integrable (fun ω => (W (h + g) ω - W h ω - W g ω) ^ 2) P := by
    convert hvec.integrable_linear_pow ![0, 1, 2] ![1, -1, -1] 2 using 1
    funext ω
    norm_num [Fin.sum_univ_succ]
    ring
  have hfi' : Integrable (fun ω =>
      (W (h + g) - (W h + W g)) ω ^ 2) P := by
    convert hfi using 1
    funext ω
    change (W (h + g) ω - (W h ω + W g ω)) ^ 2 = _
    ring
  have hsq_zero' : ∫ ω, (W (h + g) - (W h + W g)) ω ^ 2 ∂P = 0 := by
    calc
      _ = ∫ ω, (W (h + g) ω - W h ω - W g ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change (W (h + g) ω - (W h ω + W g ω)) ^ 2 = _
        ring
      _ = 0 := hsq_zero
  have hz := ae_eq_of_integral_sq_eq_zero
    ((hW.1 (h + g) hsum).sub ((hW.1 h hh).add (hW.1 g hg))) hfi' hsq_zero'
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp (by simpa using hω)

end RegularityStructures

end
