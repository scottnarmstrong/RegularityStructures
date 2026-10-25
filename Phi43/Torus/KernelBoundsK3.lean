/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsShifted

/-!
# The covariance singular bound

This is the singular estimate for the covariance `Q_ε` of Definition 2.5 of the statement.  The
proof splits the covariance convolution into the two regions where one factor is close to the
origin, and a complementary region controlled by the sixth-power majorant.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

private theorem product_bound_of_two_singular {C x y L u v : ℝ}
    (hC : 0 ≤ C) (hx : 0 < x) (hy : 0 < y) (hL : 0 < L) (hxy : y ≤ L * x)
    (hu : |u| ≤ C * x ^ (-(3 : ℝ)))
    (hv : |v| ≤ C * y ^ (-(3 : ℝ))) :
    |u * v| ≤ C ^ 2 * L ^ (3 : ℝ) * y ^ (-(6 : ℝ)) := by
  have hpow := rpow_neg_three_le_mul x y L hx hy hL hxy
  have hpow' : x ^ (-(3 : ℝ)) * y ^ (-(3 : ℝ)) ≤
      L ^ (3 : ℝ) * y ^ (-(6 : ℝ)) := by
    calc
      x ^ (-(3 : ℝ)) * y ^ (-(3 : ℝ)) ≤
          (L ^ (3 : ℝ) * y ^ (-(3 : ℝ))) * y ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hy.le _)
      _ = L ^ (3 : ℝ) * (y ^ (-(3 : ℝ)) * y ^ (-(3 : ℝ))) := by ring
      _ = L ^ (3 : ℝ) * y ^ (-(6 : ℝ)) := by
        rw [← Real.rpow_add hy]
        norm_num
  calc
    |u * v| = |u| * |v| := abs_mul u v
    _ ≤ (C * x ^ (-(3 : ℝ))) * (C * y ^ (-(3 : ℝ))) := by
      exact mul_le_mul hu hv (by positivity) (by positivity)
    _ = C ^ 2 * (x ^ (-(3 : ℝ)) * y ^ (-(3 : ℝ))) := by ring
    _ ≤ C ^ 2 * (L ^ (3 : ℝ) * y ^ (-(6 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow' (sq_nonneg C)
    _ = C ^ 2 * L ^ (3 : ℝ) * y ^ (-(6 : ℝ)) := by ring

private theorem torusParabolicSize_neg_le (w : SpaceTime) :
    torusParabolicSize (-w) ≤ 2 * torusParabolicSize w := by
  unfold torusParabolicSize
  change √|(-w.1)| + torusSpatialNorm (-w.2) ≤
    2 * (√|w.1| + torusSpatialNorm w.2)
  rw [abs_neg]
  calc
    √|w.1| + torusSpatialNorm (-w.2) ≤
        √|w.1| + 2 * torusSpatialNorm w.2 :=
      by linarith [torusSpatialNorm_neg_le w.2]
    _ ≤ 2 * (√|w.1| + torusSpatialNorm w.2) := by
      linarith [Real.sqrt_nonneg |w.1|, torusSpatialNorm_nonneg w.2]

theorem covariance_singular_bound (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      |covariance ρ ε z| ≤
        C * (torusParabolicSize z + ε) ^ (-(1 : ℝ)) := by
  obtain ⟨C₀, hC₀, hM⟩ := mollifiedKernel_singular_bound ρ hρ
  let C : ℝ := 400000 * C₀ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1 z
  let r : ℝ := torusParabolicSize z + ε
  have hr : 0 < r := by
    dsimp [r]
    exact add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg z) hε
  have hcov_int : Integrable (fun w : SpaceTime =>
      mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) :=
    (covariance_facts ρ hρ hε).1 z
  by_cases hnear : torusParabolicSize z < ε
  · have hmajor : Integrable (fun w : SpaceTime =>
        729 * C₀ ^ 2 * shiftedParabolicSix ε w) :=
      (integrable_shiftedParabolicSix hε).const_mul _
    have hpoint : ∀ w : SpaceTime,
        |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
          729 * C₀ ^ 2 * shiftedParabolicSix ε w := by
      intro w
      let x : ℝ := torusParabolicSize (z + w) + ε
      let y : ℝ := torusParabolicSize w + ε
      have hx : 0 < x := by
        dsimp [x]
        exact add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε
      have hy : 0 < y := by
        dsimp [y]
        exact add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε
      have hxy : y ≤ 9 * x := by
        dsimp [x, y] at ⊢
        have hsw := torusParabolicSize_nonneg w
        have hsz := torusParabolicSize_nonneg z
        have htriW := torusParabolicSize_sub_le w (-z)
        have hnegZ := torusParabolicSize_neg_le z
        simp only [sub_neg_eq_add, add_comm] at htriW
        linarith [hnear, torusParabolicSize_nonneg (z + w)]
      have hp := product_bound_of_two_singular (C := C₀) (x := x) (y := y) (L := 9)
        (u := mollifiedKernel ρ ε (z + w)) (v := mollifiedKernel ρ ε w)
        hC₀ hx hy (by norm_num) hxy
        (by simpa [x] using hM hε hε1 (z + w))
        (by simpa [y] using hM hε hε1 w)
      calc
        |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
            C₀ ^ 2 * 9 ^ (3 : ℝ) * y ^ (-(6 : ℝ)) := hp
        _ = 729 * C₀ ^ 2 * shiftedParabolicSix ε w := by
          rw [show (9 : ℝ) ^ (3 : ℝ) = 729 by norm_num]
          change C₀ ^ 2 * 729 * (torusParabolicSize w + ε) ^ (-(6 : ℝ)) =
            729 * C₀ ^ 2 * (torusParabolicSize w + ε) ^ (-(6 : ℝ))
          ring
    have hnorm := norm_integral_le_of_norm_le
      (f := fun w : SpaceTime =>
        mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) hmajor
      (Filter.Eventually.of_forall (fun w => by
        simpa only [Real.norm_eq_abs] using hpoint w))
    have hbound : 729 * C₀ ^ 2 * (112 / ε) ≤ C * r ^ (-(1 : ℝ)) := by
      dsimp [C]
      have hεr : r < 2 * ε := by
        dsimp [r]
        linarith [torusParabolicSize_nonneg z]
      have hrecip : ε⁻¹ ≤ 2 * r⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        apply (div_le_iff₀ hε).2
        rw [show 2 * (1 / r) * ε = (2 * ε) / r by ring]
        apply (le_div_iff₀ hr).2
        linarith [hεr]
      rw [Real.rpow_neg_one]
      calc
        729 * C₀ ^ 2 * (112 / ε) ≤
            729 * C₀ ^ 2 * (112 * (2 * r⁻¹)) := by
          rw [div_eq_mul_inv]
          have h112 : 112 * ε⁻¹ ≤ 112 * (2 * r⁻¹) :=
            mul_le_mul_of_nonneg_left hrecip (by norm_num)
          exact mul_le_mul_of_nonneg_left h112 (by positivity)
        _ ≤ 400000 * C₀ ^ 2 * r⁻¹ := by
          nlinarith [sq_nonneg C₀, inv_nonneg.mpr hr.le]
    change |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤ _
    rw [Real.norm_eq_abs] at hnorm
    calc
      |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
          ∫ w, 729 * C₀ ^ 2 * shiftedParabolicSix ε w := hnorm
      _ = 729 * C₀ ^ 2 * ∫ w, shiftedParabolicSix ε w := integral_const_mul _ _
      _ ≤ 729 * C₀ ^ 2 * (112 / ε) := by
        gcongr
        exact integral_shiftedParabolicSix_le hε
      _ ≤ C * r ^ (-(1 : ℝ)) := hbound
  · have hfar : ε ≤ torusParabolicSize z := le_of_not_gt hnear
    let a : ℝ := r / 32
    have ha : 0 < a := by
      dsimp [a]
      positivity
    let fA : SpaceTime → ℝ :=
      ({w : SpaceTime | torusParabolicSize w ≤ a}).indicator (shiftedParabolicCube ε)
    let fB : SpaceTime → ℝ := fun w => fA (z + w)
    have hAint : Integrable fA := by
      dsimp [fA]
      exact integrable_shiftedParabolicCube_on hε ha
    have hpres : MeasurePreserving (fun w : SpaceTime => z + w) volume volume :=
      measurePreserving_add_left volume z
    have hBint : Integrable fB := by
      dsimp [fB]
      exact hpres.integrable_comp_of_integrable hAint
    let Acoef : ℝ := 4096 * C₀ ^ 2 * r ^ (-(3 : ℝ))
    have hAcoef : 0 ≤ Acoef := by
      dsimp [Acoef]
      positivity
    have hAmaj : Integrable (fun w => Acoef * fA w) := hAint.const_mul _
    have hBmaj : Integrable (fun w => Acoef * fB w) := hBint.const_mul _
    have hAint_bound : ∫ w, fA w ≤ 56 * a ^ 2 := by
      dsimp [fA]
      exact integral_shiftedParabolicCube_on_le hε ha
    have hBint_bound : ∫ w, fB w ≤ 56 * a ^ 2 := by
      dsimp [fB]
      rw [integral_comp_add_left_spaceTime]
      exact hAint_bound
    have hA_bound : ∫ w, Acoef * fA w ≤ 1000 * C₀ ^ 2 * r⁻¹ := by
      calc
        ∫ w, Acoef * fA w = Acoef * ∫ w, fA w := integral_const_mul _ _
        _ ≤ Acoef * (56 * a ^ 2) :=
          mul_le_mul_of_nonneg_left hAint_bound hAcoef
        _ ≤ 1000 * C₀ ^ 2 * r⁻¹ := by
          dsimp [Acoef, a]
          norm_num [Real.rpow_neg]
          field_simp
          linarith [sq_nonneg C₀, hr]
    have hB_bound : ∫ w, Acoef * fB w ≤ 1000 * C₀ ^ 2 * r⁻¹ := by
      calc
        ∫ w, Acoef * fB w = Acoef * ∫ w, fB w := integral_const_mul _ _
        _ ≤ Acoef * (56 * a ^ 2) :=
          mul_le_mul_of_nonneg_left hBint_bound hAcoef
        _ ≤ 1000 * C₀ ^ 2 * r⁻¹ := by
          dsimp [Acoef, a]
          norm_num [Real.rpow_neg]
          field_simp
          linarith [sq_nonneg C₀, hr]
    have hfA_nonneg : ∀ w, 0 ≤ fA w := by
      intro w
      dsimp [fA]
      by_cases hw : torusParabolicSize w ≤ a
      · change 0 ≤ if torusParabolicSize w ≤ a then
          shiftedParabolicCube ε w else 0
        simp [hw, shiftedParabolicCube_nonneg hε w]
      · change 0 ≤ if torusParabolicSize w ≤ a then
          shiftedParabolicCube ε w else 0
        simp [hw]
    have hfB_nonneg : ∀ w, 0 ≤ fB w := by
      intro w
      dsimp [fB]
      exact hfA_nonneg (z + w)
    by_cases hlarge : r / 64 < ε
    · let fC : SpaceTime → ℝ := fun w => C₀ ^ 2 *
          (shiftedParabolicSix ε w + shiftedParabolicSix ε (z + w))
      have hSix := integrable_shiftedParabolicSix hε
      have hSixB : Integrable (fun w => shiftedParabolicSix ε (z + w)) := by
        exact hpres.integrable_comp_of_integrable hSix
      have hCint : Integrable fC := by
        dsimp [fC]
        have h := (hSix.const_mul (C₀ ^ 2)).add (hSixB.const_mul (C₀ ^ 2))
        refine h.congr (Filter.Eventually.of_forall ?_)
        intro w
        simp only [Pi.add_apply]
        ring
      have hC_bound : ∫ w, fC w ≤ 15000 * C₀ ^ 2 * r⁻¹ := by
        have hrecip : ε⁻¹ ≤ 64 * r⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          apply (div_le_iff₀ hε).2
          rw [show 64 * (1 / r) * ε = (64 * ε) / r by ring]
          apply (le_div_iff₀ hr).2
          linarith
        dsimp [fC]
        rw [integral_const_mul]
        have htrans : ∫ w, shiftedParabolicSix ε (z + w) =
            ∫ w, shiftedParabolicSix ε w := integral_comp_add_left_spaceTime _ _
        have hsum : (∫ w, shiftedParabolicSix ε w) +
            ∫ w, shiftedParabolicSix ε (z + w) ≤ 224 / ε := by
          rw [htrans]
          calc
            (∫ w, shiftedParabolicSix ε w) + ∫ w, shiftedParabolicSix ε w ≤
                (112 / ε) + (112 / ε) := add_le_add
                  (integral_shiftedParabolicSix_le hε)
                  (integral_shiftedParabolicSix_le hε)
            _ = 224 / ε := by ring
        have hadd : (∫ x, shiftedParabolicSix ε x +
            shiftedParabolicSix ε (z + x)) =
            (∫ x, shiftedParabolicSix ε x) +
              ∫ x, shiftedParabolicSix ε (z + x) := by
          simpa only [Pi.add_apply] using (integral_add hSix hSixB)
        rw [hadd]
        calc
          C₀ ^ 2 * ((∫ x, shiftedParabolicSix ε x) +
              ∫ x, shiftedParabolicSix ε (z + x)) ≤
              C₀ ^ 2 * (224 / ε) := mul_le_mul_of_nonneg_left hsum (sq_nonneg C₀)
          _ ≤ 15000 * C₀ ^ 2 * r⁻¹ := by
            rw [div_eq_mul_inv]
            have h224 : 224 * ε⁻¹ ≤ 224 * (64 * r⁻¹) :=
              mul_le_mul_of_nonneg_left hrecip (by norm_num)
            calc
              C₀ ^ 2 * (224 * ε⁻¹) ≤ C₀ ^ 2 * (224 * (64 * r⁻¹)) :=
                mul_le_mul_of_nonneg_left h224 (sq_nonneg C₀)
              _ ≤ 15000 * C₀ ^ 2 * r⁻¹ := by
                nlinarith [sq_nonneg C₀, inv_nonneg.mpr hr.le]
      have hpoint : ∀ w : SpaceTime,
          |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
            Acoef * fA w + Acoef * fB w + fC w := by
        intro w
        by_cases hAw : torusParabolicSize w ≤ a
        · have hAw' : w ∈ {w : SpaceTime | torusParabolicSize w ≤ a} := hAw
          have htri := torusParabolicSize_sub_le z (-w)
          have hneg := torusParabolicSize_neg_le w
          have hden : r ≤ 16 * (torusParabolicSize (z + w) + ε) := by
            simp only [sub_neg_eq_add] at htri
            dsimp [a, r] at hAw ⊢
            linarith [htri, hneg, hfar, torusParabolicSize_nonneg (z + w)]
          have hpow := rpow_neg_three_le_mul
            (torusParabolicSize (z + w) + ε) r 16
            (add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε)
              hr (by norm_num) hden
          have hpow' : (torusParabolicSize (z + w) + ε) ^ (-(3 : ℝ)) ≤
              4096 * r ^ (-(3 : ℝ)) := by
            convert hpow using 1; norm_num
          have hprod : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
              Acoef * shiftedParabolicCube ε w := by
            calc
              |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| =
                  |mollifiedKernel ρ ε (z + w)| * |mollifiedKernel ρ ε w| := abs_mul _ _
              _ ≤ (C₀ * (4096 * r ^ (-(3 : ℝ)))) *
                    (C₀ * shiftedParabolicCube ε w) := by
                apply mul_le_mul
                · exact (hM hε hε1 (z + w)).trans (mul_le_mul_of_nonneg_left hpow' hC₀)
                · simpa [shiftedParabolicCube] using hM hε hε1 w
                · positivity
                · positivity
              _ = Acoef * shiftedParabolicCube ε w := by ring
          have hrest : 0 ≤ Acoef * fB w + fC w := by
            exact add_nonneg (mul_nonneg hAcoef (hfB_nonneg w)) (by
              dsimp [fC]
              exact mul_nonneg (sq_nonneg C₀)
                (add_nonneg (shiftedParabolicSix_nonneg hε w)
                  (shiftedParabolicSix_nonneg hε (z + w))))
          simpa [fA, hAw', add_assoc] using le_add_of_le_of_nonneg hprod hrest
        · by_cases hBw : torusParabolicSize (z + w) ≤ a
          · have hBw' : z + w ∈ {v : SpaceTime | torusParabolicSize v ≤ a} := hBw
            have htri := torusParabolicSize_sub_le z (z + w)
            have hneg := torusParabolicSize_neg_le w
            have htri' : torusParabolicSize z ≤ 4 *
                (torusParabolicSize (-w) + torusParabolicSize (z + w)) := by
              have heq : z - (z + w) = -w := by abel
              simpa [heq] using htri
            have hden : r ≤ 16 * (torusParabolicSize w + ε) := by
              have hsbound : torusParabolicSize z ≤ 8 * torusParabolicSize w +
                  4 * torusParabolicSize (z + w) := by
                linarith [htri', hneg]
              have hsv : torusParabolicSize (z + w) ≤ r / 32 := by
                simpa [a] using hBw
              have hsr : torusParabolicSize z ≤ 8 * torusParabolicSize w + r / 8 := by
                linarith [hsbound, hsv]
              dsimp [r] at hsr ⊢
              have hlarge' : (torusParabolicSize z + ε) / 64 < ε := by
                simpa [r] using hlarge
              linarith [hsr, hε.le]
            have hpow := rpow_neg_three_le_mul
              (torusParabolicSize w + ε) r 16
              (add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε)
                hr (by norm_num) hden
            have hpow' : (torusParabolicSize w + ε) ^ (-(3 : ℝ)) ≤
                4096 * r ^ (-(3 : ℝ)) := by
              convert hpow using 1; norm_num
            have hprod : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
                Acoef * shiftedParabolicCube ε (z + w) := by
              calc
                |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| =
                    |mollifiedKernel ρ ε (z + w)| * |mollifiedKernel ρ ε w| := abs_mul _ _
                _ ≤ (C₀ * shiftedParabolicCube ε (z + w)) *
                      (C₀ * (4096 * r ^ (-(3 : ℝ)))) := by
                  apply mul_le_mul
                  · simpa [shiftedParabolicCube] using hM hε hε1 (z + w)
                  · exact (hM hε hε1 w).trans (mul_le_mul_of_nonneg_left hpow' hC₀)
                  · exact abs_nonneg _
                  · exact mul_nonneg hC₀ (shiftedParabolicCube_nonneg hε (z + w))
                _ = Acoef * shiftedParabolicCube ε (z + w) := by ring
            have hrest : 0 ≤ Acoef * fA w + fC w := by
              exact add_nonneg (mul_nonneg hAcoef (hfA_nonneg w)) (by
                dsimp [fC]
                exact mul_nonneg (sq_nonneg C₀)
                  (add_nonneg (shiftedParabolicSix_nonneg hε w)
                    (shiftedParabolicSix_nonneg hε (z + w))))
            have htmp := le_add_of_le_of_nonneg hprod hrest
            calc
              _ ≤ Acoef * shiftedParabolicCube ε (z + w) +
                  (Acoef * fA w + fC w) := htmp
              _ = Acoef * fA w + (Acoef * shiftedParabolicCube ε (z + w) + fC w) := by ring
              _ = Acoef * fA w + (Acoef * fB w + fC w) := by
                have hfB : fB w = shiftedParabolicCube ε (z + w) := by
                  dsimp [fB, fA]
                  simp [Set.indicator, hBw]
                rw [hfB]
              _ = Acoef * fA w + Acoef * fB w + fC w := by ring
          · have hAw' : ¬torusParabolicSize w ≤ a := hAw
            have hBw' : ¬torusParabolicSize (z + w) ≤ a := hBw
            have hp : 0 < torusParabolicSize (z + w) + ε :=
              add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε
            have hq : 0 < torusParabolicSize w + ε :=
              add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε
            by_cases hpq : torusParabolicSize (z + w) + ε ≤
                torusParabolicSize w + ε
            · have hprod := product_bound_of_two_singular
                (C := C₀) (x := torusParabolicSize w + ε)
                (y := torusParabolicSize (z + w) + ε) (L := 1)
                (u := mollifiedKernel ρ ε w) (v := mollifiedKernel ρ ε (z + w))
                hC₀ hq hp (by norm_num) (by simpa using hpq)
                (by simpa [show torusParabolicSize w + ε = torusParabolicSize w + ε by rfl]
                  using hM hε hε1 w)
                (by simpa using hM hε hε1 (z + w))
              have hprod' : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
                  C₀ ^ 2 * shiftedParabolicSix ε (z + w) := by
                simpa [shiftedParabolicSix, mul_comm] using hprod
              have hcf : C₀ ^ 2 * shiftedParabolicSix ε (z + w) ≤ fC w := by
                dsimp [fC]
                calc
                  C₀ ^ 2 * shiftedParabolicSix ε (z + w) ≤
                      C₀ ^ 2 * shiftedParabolicSix ε w +
                        C₀ ^ 2 * shiftedParabolicSix ε (z + w) :=
                    le_add_of_nonneg_left
                      (mul_nonneg (sq_nonneg C₀) (shiftedParabolicSix_nonneg hε w))
                  _ = C₀ ^ 2 * (shiftedParabolicSix ε w +
                      shiftedParabolicSix ε (z + w)) := by ring
              have hprodC := hprod'.trans hcf
              have hab : 0 ≤ Acoef * fA w + Acoef * fB w := by
                exact add_nonneg (mul_nonneg hAcoef (hfA_nonneg w))
                  (mul_nonneg hAcoef (hfB_nonneg w))
              have htmp := le_add_of_le_of_nonneg hprodC hab
              calc
                _ ≤ fC w + (Acoef * fA w + Acoef * fB w) := htmp
                _ = Acoef * fA w + (Acoef * fB w + fC w) := by ring
                _ = Acoef * fA w + Acoef * fB w + fC w := by ring
            · have hqp : torusParabolicSize w + ε ≤
                  torusParabolicSize (z + w) + ε := le_of_not_ge hpq
              have hprod := product_bound_of_two_singular
                (C := C₀) (x := torusParabolicSize (z + w) + ε)
                (y := torusParabolicSize w + ε) (L := 1)
                (u := mollifiedKernel ρ ε (z + w)) (v := mollifiedKernel ρ ε w)
                hC₀ hp hq (by norm_num) (by simpa using hqp)
                (by simpa using hM hε hε1 (z + w))
                (by simpa using hM hε hε1 w)
              have hprod' : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
                  C₀ ^ 2 * shiftedParabolicSix ε w := by
                simpa [shiftedParabolicSix] using hprod
              have hcf : C₀ ^ 2 * shiftedParabolicSix ε w ≤ fC w := by
                dsimp [fC]
                calc
                  C₀ ^ 2 * shiftedParabolicSix ε w ≤
                      C₀ ^ 2 * shiftedParabolicSix ε w +
                        C₀ ^ 2 * shiftedParabolicSix ε (z + w) :=
                    le_add_of_nonneg_right
                      (mul_nonneg (sq_nonneg C₀)
                        (shiftedParabolicSix_nonneg hε (z + w)))
                  _ = C₀ ^ 2 * (shiftedParabolicSix ε w +
                      shiftedParabolicSix ε (z + w)) := by ring
              have hprodC := hprod'.trans hcf
              have hab : 0 ≤ Acoef * fA w + Acoef * fB w := by
                exact add_nonneg (mul_nonneg hAcoef (hfA_nonneg w))
                  (mul_nonneg hAcoef (hfB_nonneg w))
              have htmp := le_add_of_le_of_nonneg hprodC hab
              calc
                _ ≤ fC w + (Acoef * fA w + Acoef * fB w) := htmp
                _ = Acoef * fA w + (Acoef * fB w + fC w) := by ring
                _ = Acoef * fA w + Acoef * fB w + fC w := by ring
      let g : SpaceTime → ℝ := fun w => Acoef * fA w +
        (Acoef * fB w + fC w)
      have hg : Integrable g := by
        dsimp [g]
        exact hAmaj.add (hBmaj.add hCint)
      have hnorm := norm_integral_le_of_norm_le
        (f := fun w : SpaceTime =>
          mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) (g := g) hg
        (Filter.Eventually.of_forall (fun w => by
          simpa only [Real.norm_eq_abs, Pi.add_apply, g, add_assoc] using hpoint w))
      have htotal : ∫ w, Acoef * fA w + (Acoef * fB w + fC w) ≤
          C * r⁻¹ := by
        have hsplitB : (∫ w, Acoef * fB w + fC w) =
            (∫ w, Acoef * fB w) + ∫ w, fC w := by
          simpa only [Pi.add_apply] using (integral_add hBmaj hCint)
        have hsplit : (∫ w, Acoef * fA w + (Acoef * fB w + fC w)) =
            (∫ w, Acoef * fA w) + (∫ w, Acoef * fB w + fC w) := by
          simpa only [Pi.add_apply] using
            (integral_add hAmaj (hBmaj.add hCint))
        rw [hsplit, hsplitB]
        dsimp [C]
        calc
          (∫ w, Acoef * fA w) +
              ((∫ w, Acoef * fB w) + ∫ w, fC w) ≤
              1000 * C₀ ^ 2 * r⁻¹ +
                (1000 * C₀ ^ 2 * r⁻¹ + 15000 * C₀ ^ 2 * r⁻¹) :=
            add_le_add hA_bound (add_le_add hB_bound hC_bound)
          _ ≤ 400000 * C₀ ^ 2 * r⁻¹ := by
            nlinarith [sq_nonneg C₀, inv_nonneg.mpr hr.le]
      change |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤ _
      rw [Real.norm_eq_abs] at hnorm
      calc
        |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
            ∫ w, Acoef * fA w + (Acoef * fB w + fC w) := hnorm
        _ ≤ C * r⁻¹ := htotal
        _ = C * r ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]
    · have hsmall : ε ≤ r / 64 := le_of_not_gt hlarge
      let q : ℝ := r / 64
      have hq : 0 < q := by
        dsimp [q]
        positivity
      let fC : SpaceTime → ℝ := fun w => C₀ ^ 2 *
          (truncatedParabolicWeight q w + truncatedParabolicWeight q (z + w))
      have hTr := integrable_truncatedParabolicWeight hq
      have hTrB : Integrable (fun w => truncatedParabolicWeight q (z + w)) := by
        exact hpres.integrable_comp_of_integrable hTr
      have hCint : Integrable fC := by
        dsimp [fC]
        have h := (hTr.const_mul (C₀ ^ 2)).add (hTrB.const_mul (C₀ ^ 2))
        refine h.congr (Filter.Eventually.of_forall ?_)
        intro w
        simp only [Pi.add_apply]
        ring
      have hC_bound : ∫ w, fC w ≤ 13000 * C₀ ^ 2 * r⁻¹ := by
        dsimp [fC]
        rw [integral_const_mul]
        have htrans : ∫ w, truncatedParabolicWeight q (z + w) =
            ∫ w, truncatedParabolicWeight q w :=
          integral_comp_add_left_spaceTime _ _
        have hsum : (∫ w, truncatedParabolicWeight q w) +
            ∫ w, truncatedParabolicWeight q (z + w) ≤ 192 / q := by
          rw [htrans]
          calc
            (∫ w, truncatedParabolicWeight q w) +
                ∫ w, truncatedParabolicWeight q w ≤ (96 / q) + (96 / q) :=
              add_le_add (integral_truncatedParabolicWeight_le hq)
                (integral_truncatedParabolicWeight_le hq)
            _ = 192 / q := by ring
        have hadd : (∫ x, truncatedParabolicWeight q x +
            truncatedParabolicWeight q (z + x)) =
            (∫ x, truncatedParabolicWeight q x) +
              ∫ x, truncatedParabolicWeight q (z + x) := by
          simpa only [Pi.add_apply] using (integral_add hTr hTrB)
        rw [hadd]
        calc
          C₀ ^ 2 * ((∫ x, truncatedParabolicWeight q x) +
              ∫ x, truncatedParabolicWeight q (z + x)) ≤
              C₀ ^ 2 * (192 / q) :=
            mul_le_mul_of_nonneg_left hsum (sq_nonneg C₀)
          _ ≤ 13000 * C₀ ^ 2 * r⁻¹ := by
            dsimp [q]
            have hr0 : r ≠ 0 := ne_of_gt hr
            have hqinv : (r / 64)⁻¹ = 64 * r⁻¹ := by
              field_simp [hr0]
            rw [div_eq_mul_inv, hqinv]
            nlinarith [sq_nonneg C₀, inv_nonneg.mpr hr.le]
      have hpoint : ∀ w : SpaceTime,
          |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
            Acoef * fA w + Acoef * fB w + fC w := by
        intro w
        by_cases hAw : torusParabolicSize w ≤ a
        · have hAw' : w ∈ {w : SpaceTime | torusParabolicSize w ≤ a} := hAw
          have htri := torusParabolicSize_sub_le z (-w)
          have hneg := torusParabolicSize_neg_le w
          have hden : r ≤ 16 * (torusParabolicSize (z + w) + ε) := by
            simp only [sub_neg_eq_add] at htri
            dsimp [a, r] at hAw ⊢
            linarith [htri, hneg, hfar, torusParabolicSize_nonneg (z + w)]
          have hpow := rpow_neg_three_le_mul
            (torusParabolicSize (z + w) + ε) r 16
            (add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε)
              hr (by norm_num) hden
          have hpow' : (torusParabolicSize (z + w) + ε) ^ (-(3 : ℝ)) ≤
              4096 * r ^ (-(3 : ℝ)) := by
            convert hpow using 1; norm_num
          have hprod : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
              Acoef * shiftedParabolicCube ε w := by
            calc
              |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| =
                  |mollifiedKernel ρ ε (z + w)| * |mollifiedKernel ρ ε w| := abs_mul _ _
              _ ≤ (C₀ * (4096 * r ^ (-(3 : ℝ)))) *
                    (C₀ * shiftedParabolicCube ε w) := by
                apply mul_le_mul
                · exact (hM hε hε1 (z + w)).trans
                    (mul_le_mul_of_nonneg_left hpow' hC₀)
                · simpa [shiftedParabolicCube] using hM hε hε1 w
                · positivity
                · positivity
              _ = Acoef * shiftedParabolicCube ε w := by ring
          have hrest : 0 ≤ Acoef * fB w + fC w := by
            exact add_nonneg (mul_nonneg hAcoef (hfB_nonneg w)) (by
              dsimp [fC]
              exact mul_nonneg (sq_nonneg C₀)
                (add_nonneg (truncatedParabolicWeight_nonneg (r := q) w)
                  (truncatedParabolicWeight_nonneg (r := q) (z + w))))
          simpa [fA, hAw', add_assoc] using le_add_of_le_of_nonneg hprod hrest
        · by_cases hBw : torusParabolicSize (z + w) ≤ a
          · have hBw' : z + w ∈ {v : SpaceTime | torusParabolicSize v ≤ a} := hBw
            have htri := torusParabolicSize_sub_le z (z + w)
            have hneg := torusParabolicSize_neg_le w
            have htri' : torusParabolicSize z ≤ 4 *
                (torusParabolicSize (-w) + torusParabolicSize (z + w)) := by
              have heq : z - (z + w) = -w := by abel
              simpa [heq] using htri
            have hden : r ≤ 16 * (torusParabolicSize w + ε) := by
              have hsbound : torusParabolicSize z ≤ 8 * torusParabolicSize w +
                  4 * torusParabolicSize (z + w) := by
                linarith [htri', hneg]
              have hsv : torusParabolicSize (z + w) ≤ r / 32 := by
                simpa [a] using hBw
              have hsr : torusParabolicSize z ≤ 8 * torusParabolicSize w + r / 8 := by
                linarith [hsbound, hsv]
              dsimp [r] at hsr ⊢
              linarith [hsr, hε.le]
            have hpow := rpow_neg_three_le_mul
              (torusParabolicSize w + ε) r 16
              (add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε)
                hr (by norm_num) hden
            have hpow' : (torusParabolicSize w + ε) ^ (-(3 : ℝ)) ≤
                4096 * r ^ (-(3 : ℝ)) := by
              convert hpow using 1; norm_num
            have hprod : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
                Acoef * shiftedParabolicCube ε (z + w) := by
              calc
                |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| =
                    |mollifiedKernel ρ ε (z + w)| * |mollifiedKernel ρ ε w| := abs_mul _ _
                _ ≤ (C₀ * shiftedParabolicCube ε (z + w)) *
                      (C₀ * (4096 * r ^ (-(3 : ℝ)))) := by
                  apply mul_le_mul
                  · simpa [shiftedParabolicCube] using hM hε hε1 (z + w)
                  · exact (hM hε hε1 w).trans
                      (mul_le_mul_of_nonneg_left hpow' hC₀)
                  · exact abs_nonneg _
                  · exact mul_nonneg hC₀ (shiftedParabolicCube_nonneg hε (z + w))
                _ = Acoef * shiftedParabolicCube ε (z + w) := by ring
            have hrest : 0 ≤ Acoef * fA w + fC w := by
              exact add_nonneg (mul_nonneg hAcoef (hfA_nonneg w)) (by
                dsimp [fC]
                exact mul_nonneg (sq_nonneg C₀)
                  (add_nonneg (truncatedParabolicWeight_nonneg (r := q) w)
                    (truncatedParabolicWeight_nonneg (r := q) (z + w))))
            have htmp := le_add_of_le_of_nonneg hprod hrest
            calc
              _ ≤ Acoef * shiftedParabolicCube ε (z + w) +
                  (Acoef * fA w + fC w) := htmp
              _ = Acoef * fA w +
                    (Acoef * shiftedParabolicCube ε (z + w) + fC w) := by ring
              _ = Acoef * fA w + (Acoef * fB w + fC w) := by
                have hfB : fB w = shiftedParabolicCube ε (z + w) := by
                  dsimp [fB, fA]
                  simp [Set.indicator, hBw]
                rw [hfB]
              _ = Acoef * fA w + Acoef * fB w + fC w := by ring
          · have hAw' : ¬torusParabolicSize w ≤ a := hAw
            have hBw' : ¬torusParabolicSize (z + w) ≤ a := hBw
            have hcutW : q < torusParabolicSize w := by
              dsimp [q, a] at ⊢ hAw
              exact lt_of_le_of_lt (by linarith [hr]) (lt_of_not_ge hAw)
            have hcutZ : q < torusParabolicSize (z + w) := by
              dsimp [q, a] at ⊢ hBw
              exact lt_of_le_of_lt (by linarith [hr]) (lt_of_not_ge hBw)
            have hdomW : shiftedParabolicSix ε w ≤
                truncatedParabolicWeight q w := by
              have hanti := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
                (r := -(6 : ℝ)) (by norm_num)
              have hswpos : 0 < torusParabolicSize w := lt_trans hq hcutW
              have h := hanti (show torusParabolicSize w ∈ Set.Ioi (0 : ℝ) from hswpos)
                (show torusParabolicSize w + ε ∈ Set.Ioi (0 : ℝ) from
                  add_pos_of_pos_of_nonneg hswpos hε.le)
                (le_add_of_nonneg_right hε.le)
              simpa [truncatedParabolicWeight, shiftedParabolicSix, hcutW] using h
            have hdomZ : shiftedParabolicSix ε (z + w) ≤
                truncatedParabolicWeight q (z + w) := by
              have hanti := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
                (r := -(6 : ℝ)) (by norm_num)
              have hszpos : 0 < torusParabolicSize (z + w) := lt_trans hq hcutZ
              have h := hanti
                (show torusParabolicSize (z + w) ∈ Set.Ioi (0 : ℝ) from hszpos)
                (show torusParabolicSize (z + w) + ε ∈ Set.Ioi (0 : ℝ) from
                  add_pos_of_pos_of_nonneg hszpos hε.le)
                (le_add_of_nonneg_right hε.le)
              simpa [truncatedParabolicWeight, shiftedParabolicSix, hcutZ] using h
            have hp : 0 < torusParabolicSize (z + w) + ε :=
              add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε
            have hq' : 0 < torusParabolicSize w + ε :=
              add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg _) hε
            by_cases hpq : torusParabolicSize (z + w) + ε ≤
                torusParabolicSize w + ε
            · have hprod := product_bound_of_two_singular
                (C := C₀) (x := torusParabolicSize w + ε)
                (y := torusParabolicSize (z + w) + ε) (L := 1)
                (u := mollifiedKernel ρ ε w) (v := mollifiedKernel ρ ε (z + w))
                hC₀ hq' hp (by norm_num) (by simpa using hpq)
                (by simpa using hM hε hε1 w)
                (by simpa using hM hε hε1 (z + w))
              have hprod' : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
                  C₀ ^ 2 * shiftedParabolicSix ε (z + w) := by
                simpa [shiftedParabolicSix, mul_comm] using hprod
              have hcf : C₀ ^ 2 * shiftedParabolicSix ε (z + w) ≤ fC w := by
                dsimp [fC]
                calc
                  C₀ ^ 2 * shiftedParabolicSix ε (z + w) ≤
                      C₀ ^ 2 * truncatedParabolicWeight q (z + w) :=
                    mul_le_mul_of_nonneg_left hdomZ (sq_nonneg C₀)
                  _ ≤ C₀ ^ 2 * truncatedParabolicWeight q w +
                      C₀ ^ 2 * truncatedParabolicWeight q (z + w) :=
                    le_add_of_nonneg_left
                      (mul_nonneg (sq_nonneg C₀)
                        (truncatedParabolicWeight_nonneg (r := q) w))
                  _ = C₀ ^ 2 * (truncatedParabolicWeight q w +
                      truncatedParabolicWeight q (z + w)) := by ring
              have hprodC := hprod'.trans hcf
              have hab : 0 ≤ Acoef * fA w + Acoef * fB w := by
                exact add_nonneg (mul_nonneg hAcoef (hfA_nonneg w))
                  (mul_nonneg hAcoef (hfB_nonneg w))
              have htmp := le_add_of_le_of_nonneg hprodC hab
              calc
                _ ≤ fC w + (Acoef * fA w + Acoef * fB w) := htmp
                _ = Acoef * fA w + (Acoef * fB w + fC w) := by ring
                _ = Acoef * fA w + Acoef * fB w + fC w := by ring
            · have hqp : torusParabolicSize w + ε ≤
                  torusParabolicSize (z + w) + ε := le_of_not_ge hpq
              have hprod := product_bound_of_two_singular
                (C := C₀) (x := torusParabolicSize (z + w) + ε)
                (y := torusParabolicSize w + ε) (L := 1)
                (u := mollifiedKernel ρ ε (z + w)) (v := mollifiedKernel ρ ε w)
                hC₀ hp hq' (by norm_num) (by simpa using hqp)
                (by simpa using hM hε hε1 (z + w))
                (by simpa using hM hε hε1 w)
              have hprod' : |mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
                  C₀ ^ 2 * shiftedParabolicSix ε w := by
                simpa [shiftedParabolicSix] using hprod
              have hcf : C₀ ^ 2 * shiftedParabolicSix ε w ≤ fC w := by
                dsimp [fC]
                calc
                  C₀ ^ 2 * shiftedParabolicSix ε w ≤
                      C₀ ^ 2 * truncatedParabolicWeight q w :=
                    mul_le_mul_of_nonneg_left hdomW (sq_nonneg C₀)
                  _ ≤ C₀ ^ 2 * truncatedParabolicWeight q w +
                      C₀ ^ 2 * truncatedParabolicWeight q (z + w) :=
                    le_add_of_nonneg_right
                      (mul_nonneg (sq_nonneg C₀)
                        (truncatedParabolicWeight_nonneg (r := q) (z + w)))
                  _ = C₀ ^ 2 * (truncatedParabolicWeight q w +
                      truncatedParabolicWeight q (z + w)) := by ring
              have hprodC := hprod'.trans hcf
              have hab : 0 ≤ Acoef * fA w + Acoef * fB w := by
                exact add_nonneg (mul_nonneg hAcoef (hfA_nonneg w))
                  (mul_nonneg hAcoef (hfB_nonneg w))
              have htmp := le_add_of_le_of_nonneg hprodC hab
              calc
                _ ≤ fC w + (Acoef * fA w + Acoef * fB w) := htmp
                _ = Acoef * fA w + (Acoef * fB w + fC w) := by ring
                _ = Acoef * fA w + Acoef * fB w + fC w := by ring
      let g : SpaceTime → ℝ := fun w => Acoef * fA w +
        (Acoef * fB w + fC w)
      have hg : Integrable g := by
        dsimp [g]
        exact hAmaj.add (hBmaj.add hCint)
      have hnorm := norm_integral_le_of_norm_le
        (f := fun w : SpaceTime =>
          mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) (g := g) hg
        (Filter.Eventually.of_forall (fun w => by
          simpa only [Real.norm_eq_abs, Pi.add_apply, g, add_assoc] using hpoint w))
      have htotal : ∫ w, Acoef * fA w + (Acoef * fB w + fC w) ≤
          C * r⁻¹ := by
        have hsplitB : (∫ w, Acoef * fB w + fC w) =
            (∫ w, Acoef * fB w) + ∫ w, fC w := by
          simpa only [Pi.add_apply] using (integral_add hBmaj hCint)
        have hsplit : (∫ w, Acoef * fA w + (Acoef * fB w + fC w)) =
            (∫ w, Acoef * fA w) + (∫ w, Acoef * fB w + fC w) := by
          simpa only [Pi.add_apply] using
            (integral_add hAmaj (hBmaj.add hCint))
        rw [hsplit, hsplitB]
        dsimp [C]
        calc
          (∫ w, Acoef * fA w) +
              ((∫ w, Acoef * fB w) + ∫ w, fC w) ≤
              1000 * C₀ ^ 2 * r⁻¹ +
                (1000 * C₀ ^ 2 * r⁻¹ + 13000 * C₀ ^ 2 * r⁻¹) :=
            add_le_add hA_bound (add_le_add hB_bound hC_bound)
          _ ≤ 400000 * C₀ ^ 2 * r⁻¹ := by
            nlinarith [sq_nonneg C₀, inv_nonneg.mpr hr.le]
      change |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤ _
      rw [Real.norm_eq_abs] at hnorm
      calc
        |∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w| ≤
            ∫ w, Acoef * fA w + (Acoef * fB w + fC w) := by
              simpa [g] using hnorm
        _ ≤ C * r⁻¹ := htotal
        _ = C * r ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one]

end Phi43

end RegularityStructures

end
