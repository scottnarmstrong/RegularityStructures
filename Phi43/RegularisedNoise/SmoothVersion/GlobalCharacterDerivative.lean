/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.CharacterDerivativeBound
public import Phi43.RegularisedNoise.SmoothVersion.TranslationCoefficient
public import Phi43.RegularisedNoise.SmoothVersion.CoefficientDecay
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Derivatives of translated Fourier characters

The global finite-window character is the exponential of a real linear phase.  The resulting
frequency-polynomial derivative bound is the deterministic estimate used in the Fourier series
construction of a smooth regularised noise (Definition 2.4 and the existence part of item (W2) of
Lemma 4.1 of the statement).
-/

@[expose] public noncomputable section

open scoped BigOperators ContDiff

namespace RegularityStructures.Phi43

private noncomputable def smoothVersionCharacterPhase (L : ℝ) (k : Fin 4 → ℤ) :
    (ℝ × (Fin 3 → ℝ)) →L[ℝ] ℝ :=
  (2 * Real.pi * (k 0 : ℝ) * L⁻¹) •
      ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ) +
    ∑ i : Fin 3, (2 * Real.pi * (k i.succ : ℝ)) •
      (ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))

private theorem globalWindowFourierMode_eq_exp_smoothVersionCharacterPhase
    (L : ℝ) (k : Fin 4 → ℤ) (p : ℝ × (Fin 3 → ℝ)) :
    globalWindowFourierMode L k (p.1, torusProj p.2) =
      Complex.exp (smoothVersionCharacterPhase L k p * Complex.I) := by
  unfold globalWindowFourierMode smoothVersionCharacterPhase
  simp only [torusProj, fourier_coe_apply]
  rw [← Complex.exp_sum]
  rw [← Complex.exp_add]
  congr 1
  simp [add_apply, smul_apply, ContinuousLinearMap.comp_apply]
  field_simp
  rw [mul_add]
  rw [Finset.mul_sum (s := Finset.univ)]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

private theorem norm_smoothVersionCharacterPhase_le
    {L : ℝ} (hL : 1 ≤ L) (k : Fin 4 → ℤ) :
    ‖smoothVersionCharacterPhase L k‖ ≤
      8 * Real.pi * smoothVersionFrequencyNormSq k := by
  let S : ℝ := smoothVersionFrequencyNormSq k
  have hS : 1 ≤ S := by
    dsimp [S, smoothVersionFrequencyNormSq]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hki : ∀ i : Fin 4, |(k i : ℝ)| ≤ S := by
    intro i
    have hsq : ((k i : ℝ)) ^ 2 ≤ ∑ j : Fin 4, ((k j : ℝ)) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ((k j : ℝ))) (Finset.mem_univ i)
    have hsq' : ((k i : ℝ)) ^ 2 ≤ S := by
      dsimp [S, smoothVersionFrequencyNormSq]
      linarith
    have hnonneg : 0 ≤ S := le_trans (by norm_num) hS
    have habs : |(k i : ℝ)| ^ 2 ≤ S := by simpa [sq_abs] using hsq'
    have hle : |(k i : ℝ)| ≤ S := by
      nlinarith [sq_nonneg (|(k i : ℝ)| - 1), sq_nonneg (|(k i : ℝ)|)]
    exact hle
  have hLinv : |L⁻¹| ≤ 1 := by
    rw [abs_inv, abs_of_nonneg (by linarith : 0 ≤ L)]
    exact (inv_le_one₀ (by linarith)).2 hL
  have hproj (i : Fin 3) :
      ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa using norm_le_pi_norm x i
  have hsnd : ‖ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.norm_snd_le ℝ ℝ (Fin 3 → ℝ)
  have hprojcomp (i : Fin 3) :
      ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))‖ ≤ 1 := by
    calc
      ‖(ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))‖ ≤
          ‖(ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)‖ *
            ‖ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (hproj i) hsnd (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  unfold smoothVersionCharacterPhase
  calc
    ‖((2 * Real.pi * (k 0 : ℝ) * L⁻¹) •
          ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) p +
        (∑ i : Fin 3, (2 * Real.pi * (k i.succ : ℝ)) •
          ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p)‖ ≤
      ‖((2 * Real.pi * (k 0 : ℝ) * L⁻¹) •
          ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) p‖ +
        ∑ i : Fin 3, ‖((2 * Real.pi * (k i.succ : ℝ)) •
          ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p)‖ := by
      have hs := norm_sum_le (Finset.univ : Finset (Fin 3))
        (fun i => (2 * Real.pi * (k i.succ : ℝ)) •
          ((ContinuousLinearMap.proj i).comp
            (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p)
      calc
        _ ≤ ‖((2 * Real.pi * (k 0 : ℝ) * L⁻¹) •
            ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) p‖ +
              ‖∑ i : Fin 3, (2 * Real.pi * (k i.succ : ℝ)) •
                ((ContinuousLinearMap.proj i).comp
                  (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p‖ := norm_add_le _ _
        _ = ‖∑ i : Fin 3, (2 * Real.pi * (k i.succ : ℝ)) •
                ((ContinuousLinearMap.proj i).comp
                  (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p‖ +
            ‖((2 * Real.pi * (k 0 : ℝ) * L⁻¹) •
              ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) p‖ := add_comm _ _
        _ ≤ _ := add_le_add_left hs _
        _ = _ := add_comm _ _
    _ ≤ 8 * Real.pi * S * ‖p‖ := by
      simp only [smul_apply]
      simp only [norm_smul]
      have hpi : 0 ≤ Real.pi := Real.pi_pos.le
      calc
        |2 * Real.pi * (k 0 : ℝ) * L⁻¹| *
              ‖ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ) p‖ +
            ∑ i : Fin 3, |2 * Real.pi * (k i.succ : ℝ)| *
              ‖((ContinuousLinearMap.proj i).comp
                (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p‖ ≤
          8 * Real.pi * S * ‖p‖ := by
            have htime : |2 * Real.pi * (k 0 : ℝ) * L⁻¹| *
                  ‖ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ) p‖ ≤
                2 * Real.pi * S * ‖p‖ := by
              calc
                _ ≤ 2 * Real.pi * |(k 0 : ℝ)| * |L⁻¹| * ‖p‖ := by
                  rw [abs_mul, abs_mul, abs_mul,
                    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                    abs_of_nonneg Real.pi_pos.le]
                  exact mul_le_mul_of_nonneg_left (norm_fst_le p) (by positivity)
                _ ≤ 2 * Real.pi * S * ‖p‖ := by
                  have htime' : |(k 0 : ℝ)| * |L⁻¹| * ‖p‖ ≤ S * ‖p‖ := by
                    calc
                      _ ≤ |(k 0 : ℝ)| * 1 * ‖p‖ := by
                        gcongr
                      _ ≤ S * ‖p‖ := by
                        gcongr
                        simpa using hki 0
                  have hconst : 0 ≤ 2 * Real.pi := by positivity
                  calc
                    2 * Real.pi * |(k 0 : ℝ)| * |L⁻¹| * ‖p‖ =
                        (2 * Real.pi) *
                          (|(k 0 : ℝ)| * |L⁻¹| * ‖p‖) := by ring
                    _ ≤ (2 * Real.pi) * (S * ‖p‖) :=
                      mul_le_mul_of_nonneg_left htime' hconst
                    _ = 2 * Real.pi * S * ‖p‖ := by ring
            have hsp : ∀ i : Fin 3,
                |2 * Real.pi * (k i.succ : ℝ)| *
                    ‖((ContinuousLinearMap.proj i).comp
                      (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p‖ ≤
                  2 * Real.pi * S * ‖p‖ := by
              intro i
              calc
                _ ≤ 2 * Real.pi * |(k i.succ : ℝ)| * ‖p‖ := by
                  rw [abs_mul, abs_mul,
                    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                    abs_of_nonneg Real.pi_pos.le]
                  have hcomp :
                      ‖((ContinuousLinearMap.proj i).comp
                        (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))) p‖ ≤ ‖p‖ := by
                    calc
                      _ ≤ ‖((ContinuousLinearMap.proj i).comp
                          (ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ)))‖ * ‖p‖ :=
                        ContinuousLinearMap.le_opNorm _ _
                      _ ≤ 1 * ‖p‖ :=
                        mul_le_mul_of_nonneg_right (hprojcomp i) (norm_nonneg _)
                      _ = ‖p‖ := by ring
                  exact mul_le_mul_of_nonneg_left hcomp (by positivity)
                _ ≤ 2 * Real.pi * S * ‖p‖ := by
                  have hk := mul_le_mul_of_nonneg_right (hki i.succ) (norm_nonneg p)
                  have hc := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ 2 * Real.pi)
                  convert hc using 1 <;> ring
            calc
              _ ≤ 2 * Real.pi * S * ‖p‖ +
                    ∑ i : Fin 3, 2 * Real.pi * S * ‖p‖ :=
                add_le_add htime (Finset.sum_le_sum fun i hi => hsp i)
              _ = 8 * Real.pi * S * ‖p‖ := by
                norm_num [Fin.sum_univ_succ]
                ring

theorem norm_iteratedFDeriv_globalWindowFourierMode_le
    {L : ℝ} (hL : 1 ≤ L) (k : Fin 4 → ℤ) (n : ℕ)
    (p : ℝ × (Fin 3 → ℝ)) :
    ‖iteratedFDeriv ℝ n
        (fun q => globalWindowFourierMode L k (q.1, torusProj q.2)) p‖ ≤
      n.factorial * 2 * (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ n := by
  have hphase := norm_iteratedFDeriv_exp_mul_I_comp_linear_le
    (smoothVersionCharacterPhase L k) n p
  have hnorm := norm_smoothVersionCharacterPhase_le hL k
  have hpow : ‖smoothVersionCharacterPhase L k‖ ^ n ≤
      (8 * Real.pi * smoothVersionFrequencyNormSq k) ^ n := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm n
  rw [show (fun q : ℝ × (Fin 3 → ℝ) =>
      globalWindowFourierMode L k (q.1, torusProj q.2)) =
      (fun q => Complex.exp (smoothVersionCharacterPhase L k q * Complex.I)) by
    funext q
    exact globalWindowFourierMode_eq_exp_smoothVersionCharacterPhase L k q]
  exact (hphase.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))

end RegularityStructures.Phi43

end
