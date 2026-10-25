/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerKernelTaylor
public import Phi43.Stochastic.ConstantsComparisonDefinitions
public import RegularityStructures.Torus.KernelBoundsGeometry
import RegularityStructures.PDE.SmoothDense
import Mathlib.Algebra.Order.Chebyshev

/-!
# Second-order bounds for the periodised Hairer kernel

`hairerKernelTorusGrad N i = ∑ₖ ∂ᵢK_N (z.1, torusRep z.2 + k)` is the spatial gradient of
`K♯_N = hairerKernelTorus N`.  As in `HairerKernelIncrementTorus` both periodisations are finite
sums over the lifts `(z.1, c + k)` of `z`, `c` the centred representative.  The increment of the
torus point is `(t, proj a)` for a *lift* `a` of its spatial part with `|aᵢ| ≤ 1/2`; the statements
are in terms of the parabolic size `‖(t, a)‖` of the lift.

* `hairerKernelTorusGrad_abs_le`: `|∂ᵢK♯ z| ≲ s(z)⁻⁴`;
* `hairerKernelTorusGrad_sub_abs_le`: `|∂ᵢK♯ (z + h) - ∂ᵢK♯ z| ≲ ‖h‖ s(z)⁻⁵`;
* `hairerKernelTorus_taylor_abs_le`:
  `|K♯ (z + h) - K♯ z - ∑ᵢ ∂ᵢK♯ z aᵢ| ≲ ‖(t, a)‖^(1+θ) s(z)^(-(4+θ))`, `θ ∈ [0, 1]`.
-/

@[expose] public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The spatial gradient of the periodised Hairer kernel. -/
noncomputable def hairerKernelTorusGrad (N : ℕ) (i : Fin 3) (z : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, hairerKernelGrad N i (z.1, torusRep z.2 + fun j => (k j : ℝ))

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

open RegularityStructures

private noncomputable def kttBox : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-2 : ℤ) 2

/-- The gradient of the kernel vanishes outside the unit ball. -/
theorem hairerKernelGrad_eq_zero_of_one_lt (N : ℕ) (i : Fin 3) {z : ParabolicSpace}
    (hz : 1 < parabolicNorm z) : hairerKernelGrad N i z = 0 := by
  unfold hairerKernelGrad
  have hzero : ∀ n, lineIter [spaceDir i] (annShellC N n) z = 0 := fun n =>
    lineIter_spaceDir_annShellC_eq_zero N n i
      (lt_of_le_of_lt (pow_le_one₀ (by positivity) (by norm_num)) hz)
  rw [tsum_eq_sum (s := (∅ : Finset ℕ)) (fun n _ => hzero n)]
  simp

private theorem ktt_kernel_eq_zero (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    hairerKernel N z = 0 := by
  unfold hairerKernel
  have hzero : ∀ n, annShellC N n z = 0 := fun n =>
    annShellC_eq_zero (lt_of_le_of_lt (pow_le_one₀ (by positivity) (by norm_num)) hz)
  rw [tsum_eq_sum (s := (∅ : Finset ℕ)) (fun n _ => hzero n)]
  simp

/-- A lift `y` of `z.2` with coordinates in `[-1, 1]` computes the periodisation as a finite sum. -/
private theorem ktt_tsum_eq_sum (F : ParabolicSpace → ℝ)
    (hF : ∀ w, 1 < parabolicNorm w → F w = 0) (z : SpaceTime) {y : Fin 3 → ℝ}
    (hy : RegularityStructures.torusProj y = z.2) (hy1 : ∀ i, |y i| ≤ 1) :
    ∑' k : Fin 3 → ℤ, F (z.1, torusRep z.2 + fun i => (k i : ℝ)) =
      ∑ k ∈ kttBox, F (z.1, y + fun i => (k i : ℝ)) := by
  have hab : RegularityStructures.torusProj (torusRep z.2) = RegularityStructures.torusProj y := by
    rw [hy]; exact RegularityStructures.PDE.torusProj_torusRep z.2
  choose m hm using fun i => RegularityStructures.PDE.exists_int_of_torusProj_eq hab i
  let g : (Fin 3 → ℤ) → ℝ := fun k => F (z.1, y + fun i => (k i : ℝ))
  have hshift : ∑' k : Fin 3 → ℤ, F (z.1, torusRep z.2 + fun i => (k i : ℝ)) = ∑' k, g k := by
    rw [← (Equiv.subRight m).tsum_eq g]
    refine tsum_congr fun k => ?_
    simp only [g, Equiv.subRight_apply]
    congr 2
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_sub, hm i]
    ring
  rw [hshift]
  refine tsum_eq_sum fun k hk => ?_
  by_contra hne
  apply hk
  have hnorm : parabolicNorm (z.1, y + fun i => (k i : ℝ)) ≤ 1 := by
    by_contra h
    exact hne (hF _ (lt_of_not_ge h))
  unfold kttBox
  rw [Fintype.mem_piFinset]
  intro i
  have hi : |y i + (k i : ℝ)| ≤ 1 := by
    have h1 : |y i + (k i : ℝ)| ≤ ∑ j, |y j + (k j : ℝ)| :=
      Finset.single_le_sum (f := fun j => |y j + (k j : ℝ)|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    unfold parabolicNorm at hnorm
    simp only [Pi.add_apply] at hnorm
    linarith [Real.sqrt_nonneg |z.1|]
  have hlo := (abs_le.1 hi).1
  have hhi := (abs_le.1 hi).2
  have hyi := abs_le.1 (hy1 i)
  rw [Finset.mem_Icc]
  constructor
  · have : (-2 : ℝ) ≤ k i := by linarith
    exact_mod_cast this
  · have : (k i : ℝ) ≤ 2 := by linarith
    exact_mod_cast this

/-- The centred representative is the shortest lift. -/
private theorem ktt_spatialNorm_le_l1 (x : Torus3) {y : Fin 3 → ℝ}
    (hy : ∀ i, ∃ n : ℤ, y i = torusCenteredRep x i + n) :
    torusSpatialNorm x ≤ ∑ i, |y i| := by
  have hc : ∀ i, |torusCenteredRep x i| ≤ |y i| := by
    intro i
    obtain ⟨n, hn⟩ := hy i
    have := sq_centered_add_int_ge (torusCenteredRep_mem_Icc x i) n
    rw [← hn] at this
    exact sq_le_sq.1 this
  have hsum0 : 0 ≤ ∑ i, |y i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold torusSpatialNorm
  rw [Real.sqrt_le_left hsum0]
  unfold sqNorm3
  calc ∑ i, torusCenteredRep x i ^ 2 = ∑ i, |torusCenteredRep x i| ^ 2 := by simp only [sq_abs]
    _ ≤ (∑ i, |torusCenteredRep x i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ ≤ (∑ i, |y i|) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _)
          (Finset.sum_le_sum fun i _ => hc i) 2

/-- Every lift `(z.1, c + k)` is at least as large as `z`. -/
private theorem ktt_lift_ge (z : SpaceTime) (k : Fin 3 → ℤ) :
    torusParabolicSize z ≤ parabolicNorm (z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) := by
  unfold torusParabolicSize parabolicNorm
  have := ktt_spatialNorm_le_l1 z.2 (y := torusCenteredRep z.2 + fun i => (k i : ℝ))
    (fun i => ⟨k i, by simp⟩)
  simp only [Pi.add_apply] at this ⊢
  linarith

private theorem ktt_centred_abs_le (z : SpaceTime) (i : Fin 3) :
    |torusCenteredRep z.2 i| ≤ 1 / 2 :=
  abs_le.2 ⟨(torusCenteredRep_mem_Icc z.2 i).1, (torusCenteredRep_mem_Icc z.2 i).2⟩

private theorem ktt_sum_c (F : ParabolicSpace → ℝ) (hF : ∀ w, 1 < parabolicNorm w → F w = 0)
    (z : SpaceTime) :
    ∑' k : Fin 3 → ℤ, F (z.1, torusRep z.2 + fun i => (k i : ℝ)) =
      ∑ k ∈ kttBox, F (z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) :=
  ktt_tsum_eq_sum F hF z (RegularityStructures.torusProj_torusCenteredRep z.2) fun i =>
    (ktt_centred_abs_le z i).trans (by norm_num)

private theorem ktt_sum_shift (F : ParabolicSpace → ℝ) (hF : ∀ w, 1 < parabolicNorm w → F w = 0)
    (z : SpaceTime) (t : ℝ) {a : Fin 3 → ℝ} (ha : ∀ i, |a i| ≤ 1 / 2) :
    ∑' k : Fin 3 → ℤ, F ((z + (t, RegularityStructures.torusProj a)).1,
        torusRep (z + (t, RegularityStructures.torusProj a)).2 + fun i => (k i : ℝ)) =
      ∑ k ∈ kttBox, F ((z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) + (t, a)) := by
  rw [ktt_tsum_eq_sum F hF (z + (t, RegularityStructures.torusProj a))
    (y := torusCenteredRep z.2 + a)
    (by rw [Prod.snd_add, RegularityStructures.PDE.torusProj_add,
      RegularityStructures.torusProj_torusCenteredRep]) fun i => by
        have := ktt_centred_abs_le z i
        simp only [Pi.add_apply]
        exact (abs_add_le _ _).trans (by linarith [ha i])]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine Prod.ext rfl ?_
  funext i
  simp only [Prod.snd_add, Pi.add_apply]
  ring

private theorem ktt_lift_pos {z : SpaceTime} (hz : 0 < torusParabolicSize z) (k : Fin 3 → ℤ) :
    0 < parabolicNorm (z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) :=
  lt_of_lt_of_le hz (ktt_lift_ge z k)

private theorem ktt_rpow_le {z : SpaceTime} (hz : 0 < torusParabolicSize z) (k : Fin 3 → ℤ)
    (e : ℝ) (he : e ≤ 0) :
    parabolicNorm (z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) ^ e ≤
      torusParabolicSize z ^ e :=
  Real.rpow_le_rpow_of_nonpos hz (ktt_lift_ge z k) he

private theorem ktt_ratio {z : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ}
    (hh : parabolicNorm (t, a) ≤ torusParabolicSize z / 2) (k : Fin 3 → ℤ) :
    parabolicNorm (t, a) ≤
      9 / 10 * parabolicNorm (z.1, torusCenteredRep z.2 + fun i => (k i : ℝ)) := by
  have := ktt_lift_ge z k
  have h0 := torusParabolicSize_nonneg z
  linarith

/-- **Bound of the spatial gradient of the periodised Hairer kernel**. -/
theorem hairerKernelTorusGrad_abs_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) {z : SpaceTime}, 0 < torusParabolicSize z →
      |hairerKernelTorusGrad N i z| ≤ C * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerKernelGrad_abs_le N
  refine ⟨kttBox.card * C0, by positivity, fun i z hz => ?_⟩
  have e : hairerKernelTorusGrad N i z =
      ∑ k ∈ kttBox, hairerKernelGrad N i (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) :=
    ktt_sum_c (hairerKernelGrad N i) (fun _ hw => hairerKernelGrad_eq_zero_of_one_lt N i hw) z
  rw [e]
  calc _ ≤ ∑ k ∈ kttBox, |hairerKernelGrad N i
          (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ kttBox, C0 * torusParabolicSize z ^ (-(4 : ℝ)) :=
        Finset.sum_le_sum fun k _ =>
          (hK i (ktt_lift_pos hz k)).trans
            (mul_le_mul_of_nonneg_left (ktt_rpow_le hz k _ (by norm_num)) hC0)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Increment of the spatial gradient of the periodised Hairer kernel**. -/
theorem hairerKernelTorusGrad_sub_abs_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) {z : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ},
      0 < torusParabolicSize z → (∀ j, |a j| ≤ 1 / 2) →
      parabolicNorm (t, a) ≤ torusParabolicSize z / 2 →
        |hairerKernelTorusGrad N i (z + (t, RegularityStructures.torusProj a)) -
            hairerKernelTorusGrad N i z| ≤
          C * parabolicNorm (t, a) * torusParabolicSize z ^ (-(5 : ℝ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerKernelGrad_sub_abs_le_of_le N
  refine ⟨kttBox.card * C0, by positivity, fun i z t a hz ha hh => ?_⟩
  have hF : ∀ w, 1 < parabolicNorm w → hairerKernelGrad N i w = 0 := fun w hw =>
    hairerKernelGrad_eq_zero_of_one_lt N i hw
  have e1 : hairerKernelTorusGrad N i (z + (t, RegularityStructures.torusProj a)) =
      ∑ k ∈ kttBox, hairerKernelGrad N i
        ((z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) + (t, a)) :=
    ktt_sum_shift (hairerKernelGrad N i) hF z t ha
  have e0 : hairerKernelTorusGrad N i z =
      ∑ k ∈ kttBox, hairerKernelGrad N i (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) :=
    ktt_sum_c (hairerKernelGrad N i) hF z
  rw [e1, e0, ← Finset.sum_sub_distrib]
  have hs0 := parabolicNorm_nonneg (t, a)
  calc _ ≤ ∑ k ∈ kttBox, |hairerKernelGrad N i
          ((z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) + (t, a)) -
        hairerKernelGrad N i (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ kttBox, C0 * parabolicNorm (t, a) * torusParabolicSize z ^ (-(5 : ℝ)) :=
        Finset.sum_le_sum fun k _ =>
          (hK i (ktt_lift_pos hz k) (ktt_ratio hh k)).trans
            (mul_le_mul_of_nonneg_left (ktt_rpow_le hz k _ (by norm_num))
              (mul_nonneg hC0 hs0))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Taylor remainder of the periodised Hairer kernel**, spatial gradient only. -/
theorem hairerKernelTorus_taylor_abs_le (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → ∀ {z : SpaceTime} {t : ℝ} {a : Fin 3 → ℝ},
      0 < torusParabolicSize z → (∀ j, |a j| ≤ 1 / 2) →
      parabolicNorm (t, a) ≤ torusParabolicSize z / 2 →
        |hairerKernelTorus N (z + (t, RegularityStructures.torusProj a)) - hairerKernelTorus N z -
            ∑ i : Fin 3, hairerKernelTorusGrad N i z * a i| ≤
          C * parabolicNorm (t, a) ^ (1 + θ) * torusParabolicSize z ^ (-(4 + θ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerKernel_taylor_abs_le_of_le N
  refine ⟨kttBox.card * C0, by positivity, fun {θ} hθ0 hθ1 z t a hz ha hh => ?_⟩
  have hF : ∀ w, 1 < parabolicNorm w → hairerKernel N w = 0 := fun w hw =>
    ktt_kernel_eq_zero N hw
  have e1 : hairerKernelTorus N (z + (t, RegularityStructures.torusProj a)) =
      ∑ k ∈ kttBox, hairerKernel N
        ((z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) + (t, a)) :=
    ktt_sum_shift (hairerKernel N) hF z t ha
  have e0 : hairerKernelTorus N z =
      ∑ k ∈ kttBox, hairerKernel N (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) :=
    ktt_sum_c (hairerKernel N) hF z
  have e2 : ∀ i : Fin 3, hairerKernelTorusGrad N i z =
      ∑ k ∈ kttBox, hairerKernelGrad N i (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) :=
    fun i => ktt_sum_c (hairerKernelGrad N i)
      (fun _ hw => hairerKernelGrad_eq_zero_of_one_lt N i hw) z
  have hdiff : hairerKernelTorus N (z + (t, RegularityStructures.torusProj a)) -
      hairerKernelTorus N z - ∑ i : Fin 3, hairerKernelTorusGrad N i z * a i =
      ∑ k ∈ kttBox, (hairerKernel N
          ((z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) + (t, a)) -
        hairerKernel N (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) -
        ∑ i : Fin 3, hairerKernelGrad N i
          (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) * a i) := by
    simp only [e1, e0, e2, Finset.sum_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hdiff]
  have hs0 := Real.rpow_nonneg (parabolicNorm_nonneg (t, a)) (1 + θ)
  calc _ ≤ ∑ k ∈ kttBox, |hairerKernel N
          ((z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) + (t, a)) -
        hairerKernel N (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) -
        ∑ i : Fin 3, hairerKernelGrad N i
          (z.1, torusCenteredRep z.2 + fun j => (k j : ℝ)) * a i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ kttBox, C0 * parabolicNorm (t, a) ^ (1 + θ) *
          torusParabolicSize z ^ (-(4 + θ)) :=
        Finset.sum_le_sum fun k _ =>
          (hK hθ0 hθ1 (ktt_lift_pos hz k) (ktt_ratio hh k)).trans
            (mul_le_mul_of_nonneg_left (ktt_rpow_le hz k _ (by linarith))
              (mul_nonneg hC0 hs0))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end RegularityStructures.Phi43

end
