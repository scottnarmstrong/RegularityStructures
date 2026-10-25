/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerKernelIncrementTorus
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Phi43.Stochastic.ConstantsComparisonPeriodise

/-!
# Difference of mollified Hairer kernels for two mollifiers

For mollifiers `ρ`, `ρ'` and scales `ε`, `ε'` in `(0, 1]` we prove, for `θ ∈ (0, 1]`,
`|K_{ρ,ε} z - K_{ρ',ε'} z| ≲ (max ε ε')^θ (s(z) + min ε ε')^(-3-θ)`, where
`K_{ρ,ε} = hairerMollifiedKernel N ρ ε`, and the consequence
`|K_{ρ,ε} z - K_{ρ',ε'} z| ≲ (max ε ε')^θ s(z)^(-3-θ)` for `s z > 0`.
Both kernels are compared with the periodised Hairer kernel away from the origin, so the bound
does not depend on `ρ`, `ρ'` beyond the constant (this is the form needed to compare the models of
two different mollifiers).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem cmk_size_neg_le (w : SpaceTime) :
    torusParabolicSize (-w) ≤ 2 * torusParabolicSize w := by
  unfold torusParabolicSize
  change √|(-w.1)| + torusSpatialNorm (-w.2) ≤ 2 * (√|w.1| + torusSpatialNorm w.2)
  rw [abs_neg]
  have := torusSpatialNorm_neg_le w.2
  have := Real.sqrt_nonneg |w.1|
  have := torusSpatialNorm_nonneg w.2
  linarith

/-- `x ≥ y / L` gives `x ^ (-a) ≤ L ^ a * y ^ (-a)`. -/
private theorem cmk_rpow_neg_le {a x y L : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hL : 0 < L)
    (h : y ≤ L * x) : x ^ (-a) ≤ L ^ a * y ^ (-a) := by
  have hx : 0 < x := by
    by_contra hx
    nlinarith
  have h1 : y / L ≤ x := by rw [div_le_iff₀ hL]; linarith
  have h2 : x ^ (-a) ≤ (y / L) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  have h3 : (y / L) ^ (-a) = L ^ a * y ^ (-a) := by
    rw [Real.div_rpow hy.le hL.le, Real.rpow_neg hy.le, Real.rpow_neg hL.le,
      div_inv_eq_mul]
    ring
  exact h2.trans h3.le

/-- `M s⁻⁴ ≤ M^θ s^(-3-θ)` for `M ≤ s` and `θ ≤ 1`. -/
private theorem cmk_alg {M s θ : ℝ} (hM : 0 < M) (hMs : M ≤ s) (hθ1 : θ ≤ 1) :
    M * s ^ (-(4 : ℝ)) ≤ M ^ θ * s ^ (-(3 + θ)) := by
  have hs : 0 < s := lt_of_lt_of_le hM hMs
  have h1 : M = M ^ θ * M ^ (1 - θ) := by
    rw [← Real.rpow_add hM]; simp
  have h2 : M ^ (1 - θ) ≤ s ^ (1 - θ) := Real.rpow_le_rpow hM.le hMs (by linarith)
  have h3 : s ^ (1 - θ) * s ^ (-(4 : ℝ)) = s ^ (-(3 + θ)) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h4 : 0 ≤ M ^ θ := Real.rpow_nonneg hM.le _
  have h5 : 0 ≤ s ^ (-(4 : ℝ)) := Real.rpow_nonneg hs.le _
  calc M * s ^ (-(4 : ℝ)) = M ^ θ * M ^ (1 - θ) * s ^ (-(4 : ℝ)) := by rw [← h1]
    _ ≤ M ^ θ * s ^ (1 - θ) * s ^ (-(4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h4) h5
    _ = M ^ θ * s ^ (-(3 + θ)) := by rw [mul_assoc, h3]

/-- Away from the origin, `K_ε` is within `ε s⁻⁴` of the periodised Hairer kernel. -/
private theorem cmk_far_bound (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {B : ℝ} (hB : 0 < B) (hsupp : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ w : SpaceTime,
      periodise ρ ε w ≠ 0 → torusParabolicSize w ≤ B * ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {z : SpaceTime},
      8 * B * ε ≤ torusParabolicSize z → 0 < torusParabolicSize z →
        |hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z| ≤
          C * ε * torusParabolicSize z ^ (-(4 : ℝ)) := by
  obtain ⟨C2, hC2, hinc⟩ := hairerKernelTorus_sub_abs_le N
  let mass : ℝ := ∫ y, |ρ y|
  have hmass : 0 ≤ mass :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
  refine ⟨C2 * 2 * B * mass, by positivity, ?_⟩
  intro ε hε hε1 z hzε hz
  obtain ⟨D, hD⟩ := bounded_periodise ρ hρ hε
  have hPi : Integrable (periodise ρ ε) := integrable_periodise ρ hρ hε
  have hKi : Integrable (fun w : SpaceTime => hairerKernelTorus N (z - w)) :=
    integrable_comp_sub_left_spaceTime (integrable_constantsComparison_hairerKernelTorus N) z
  have hf : Integrable (fun w : SpaceTime => hairerKernelTorus N (z - w) * periodise ρ ε w) :=
    hKi.mul_bdd hPi.aestronglyMeasurable (c := D)
      (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hD w)
  have hg : Integrable (fun w : SpaceTime => hairerKernelTorus N z * periodise ρ ε w) :=
    hPi.const_mul _
  have hdiff : hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z =
      ∫ w, (hairerKernelTorus N (z - w) - hairerKernelTorus N z) * periodise ρ ε w := by
    have e : ∀ w : SpaceTime, (hairerKernelTorus N (z - w) - hairerKernelTorus N z) *
        periodise ρ ε w = hairerKernelTorus N (z - w) * periodise ρ ε w -
          hairerKernelTorus N z * periodise ρ ε w := fun w => by ring
    simp only [e]
    rw [integral_sub hf hg, integral_const_mul, integral_periodise_eq_one ρ hρ hε]
    unfold hairerMollifiedKernel
    ring
  set G : ℝ := C2 * (2 * (B * ε)) * torusParabolicSize z ^ (-(4 : ℝ)) with hG
  have hmaj : Integrable (fun w : SpaceTime => G * |periodise ρ ε w|) := hPi.norm.const_mul G
  have hpt : ∀ w : SpaceTime, ‖(hairerKernelTorus N (z - w) - hairerKernelTorus N z) *
      periodise ρ ε w‖ ≤ G * |periodise ρ ε w| := by
    intro w
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hp : periodise ρ ε w = 0
    · simp [hp]
    · have hw := hsupp hε hε1 w hp
      have hneg := cmk_size_neg_le w
      have h1 : torusParabolicSize (-w) ≤ torusParabolicSize z / 2 := by
        linarith
      have h2 := hinc (z := z) (h := -w) hz h1
      rw [← sub_eq_add_neg] at h2
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine h2.trans ?_
      have h3 : 0 ≤ torusParabolicSize z ^ (-(4 : ℝ)) := Real.rpow_nonneg hz.le _
      rw [hG]
      refine mul_le_mul_of_nonneg_right ?_ h3
      exact mul_le_mul_of_nonneg_left (by linarith) hC2
  have hfi : Integrable (fun w : SpaceTime =>
      (hairerKernelTorus N (z - w) - hairerKernelTorus N z) * periodise ρ ε w) := by
    have e : ∀ w : SpaceTime, (hairerKernelTorus N (z - w) - hairerKernelTorus N z) *
        periodise ρ ε w = hairerKernelTorus N (z - w) * periodise ρ ε w -
          hairerKernelTorus N z * periodise ρ ε w := fun w => by ring
    simp only [e]
    exact hf.sub hg
  have hBe : 0 ≤ G := by
    rw [hG]
    positivity
  have hPint : ∫ w : SpaceTime, |periodise ρ ε w| ≤ mass := by
    calc _ ≤ ∫ y, |rescale ρ ε y| := integral_abs_periodise_le ρ hρ hε hε1
      _ = mass := integral_abs_rescale_eq ρ hε
  rw [hdiff]
  calc |∫ w, (hairerKernelTorus N (z - w) - hairerKernelTorus N z) * periodise ρ ε w|
      = ‖∫ w, (hairerKernelTorus N (z - w) - hairerKernelTorus N z) * periodise ρ ε w‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ w, G * |periodise ρ ε w| := norm_integral_le_of_norm_le hmaj
        (Filter.Eventually.of_forall hpt)
    _ = G * ∫ w, |periodise ρ ε w| := integral_const_mul G _
    _ ≤ G * mass := mul_le_mul_of_nonneg_left hPint hBe
    _ = C2 * 2 * B * mass * ε * torusParabolicSize z ^ (-(4 : ℝ)) := by
      rw [hG]; ring

/-- **Cross-mollifier difference of the mollified Hairer kernel** (the weight uses `min ε ε'`). -/
theorem hairerMollifiedKernel_sub_abs_le_cross (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → ∀ z : SpaceTime,
      |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
        C * (max ε ε') ^ θ * (torusParabolicSize z + min ε ε') ^ (-(3 + θ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  obtain ⟨C0', hC0', hK'⟩ := hairerMollifiedKernel_singular_bound ρ' hρ' N
  obtain ⟨B0, hB0, hsupp0⟩ := periodise_support_parabolic_bound ρ hρ
  obtain ⟨B0', hB0', hsupp0'⟩ := periodise_support_parabolic_bound ρ' hρ'
  set B : ℝ := max (max B0 B0') 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB : 0 < B := by linarith
  have hsupp : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ w : SpaceTime,
      periodise ρ ε w ≠ 0 → torusParabolicSize w ≤ B * ε := fun hε hε1 w hw =>
    (hsupp0 hε hε1 w hw).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) hε.le)
  have hsupp' : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ w : SpaceTime,
      periodise ρ' ε w ≠ 0 → torusParabolicSize w ≤ B * ε := fun hε hε1 w hw =>
    (hsupp0' hε hε1 w hw).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) hε.le)
  obtain ⟨Cf, hCf, hfar⟩ := cmk_far_bound N ρ hρ hB hsupp
  obtain ⟨Cf', hCf', hfar'⟩ := cmk_far_bound N ρ' hρ' hB hsupp'
  set L : ℝ := 1 + (8 * B)⁻¹ with hL
  have hL0 : 0 < L := by positivity
  refine ⟨(C0 + C0') * (8 * B + 1) + (Cf + Cf') * L ^ (3 + θ), by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z
  set M : ℝ := max ε ε' with hM
  set m : ℝ := min ε ε' with hm
  have hM0 : 0 < M := lt_max_of_lt_left hε
  have hm0 : 0 < m := lt_min hε hε'
  have hεM : ε ≤ M := le_max_left _ _
  have hε'M : ε' ≤ M := le_max_right _ _
  have hmε : m ≤ ε := min_le_left _ _
  have hmε' : m ≤ ε' := min_le_right _ _
  have hs0 := torusParabolicSize_nonneg z
  set s := torusParabolicSize z with hs
  have hMθ : 0 ≤ M ^ θ := Real.rpow_nonneg hM0.le _
  have hW : 0 ≤ (s + m) ^ (-(3 + θ)) := Real.rpow_nonneg (by positivity) _
  have hX : 0 ≤ M ^ θ * (s + m) ^ (-(3 + θ)) := mul_nonneg hMθ hW
  have hCC : 0 ≤ (C0 + C0') * (8 * B + 1) := by positivity
  have hCF : 0 ≤ (Cf + Cf') * L ^ (3 + θ) := by positivity
  by_cases hnear : s < 8 * B * M
  · have h1 : |hairerMollifiedKernel N ρ ε z| ≤ C0 * (s + m) ^ (-(3 : ℝ)) :=
      (hK hε hε1 z).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)) hC0)
    have h2 : |hairerMollifiedKernel N ρ' ε' z| ≤ C0' * (s + m) ^ (-(3 : ℝ)) :=
      (hK' hε' hε'1 z).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)) hC0')
    have h3 : (s + m) ^ (-(3 : ℝ)) = (s + m) ^ θ * (s + m) ^ (-(3 + θ)) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; ring
    have h4 : (s + m) ^ θ ≤ (8 * B + 1) * M ^ θ := by
      have h5 : s + m ≤ (8 * B + 1) * M := by linarith [min_le_left ε ε', le_max_left ε ε']
      calc (s + m) ^ θ ≤ ((8 * B + 1) * M) ^ θ := Real.rpow_le_rpow (by positivity) h5 hθ.le
        _ = (8 * B + 1) ^ θ * M ^ θ := Real.mul_rpow (by positivity) hM0.le
        _ ≤ (8 * B + 1) * M ^ θ := by
          refine mul_le_mul_of_nonneg_right ?_ hMθ
          calc (8 * B + 1) ^ θ ≤ (8 * B + 1) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hθ1
            _ = 8 * B + 1 := Real.rpow_one _
    have h6 : |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
        (C0 + C0') * (8 * B + 1) * (M ^ θ * (s + m) ^ (-(3 + θ))) := by
      calc _ ≤ |hairerMollifiedKernel N ρ ε z| + |hairerMollifiedKernel N ρ' ε' z| := abs_sub _ _
        _ ≤ (C0 + C0') * (s + m) ^ (-(3 : ℝ)) := by linarith
        _ = (C0 + C0') * ((s + m) ^ θ * (s + m) ^ (-(3 + θ))) := by rw [h3]
        _ ≤ (C0 + C0') * (((8 * B + 1) * M ^ θ) * (s + m) ^ (-(3 + θ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hW) (by positivity)
        _ = _ := by ring
    have h7 : (C0 + C0') * (8 * B + 1) * (M ^ θ * (s + m) ^ (-(3 + θ))) ≤
        ((C0 + C0') * (8 * B + 1) + (Cf + Cf') * L ^ (3 + θ)) *
          (M ^ θ * (s + m) ^ (-(3 + θ))) :=
      mul_le_mul_of_nonneg_right (by linarith) hX
    calc _ ≤ _ := h6.trans h7
      _ = _ := by ring
  · have hfarc : 8 * B * M ≤ s := not_lt.1 hnear
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hfarc
    have hMs : M ≤ s := by nlinarith
    have hKe := hfar hε hε1 (z := z) (by nlinarith) hspos
    have hKe' := hfar' hε' hε'1 (z := z) (by nlinarith) hspos
    have h1 : |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
        (Cf + Cf') * (M * s ^ (-(4 : ℝ))) := by
      have h0 : 0 ≤ s ^ (-(4 : ℝ)) := Real.rpow_nonneg hspos.le _
      calc _ ≤ |hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z| +
            |hairerMollifiedKernel N ρ' ε' z - hairerKernelTorus N z| := by
            rw [← abs_neg (hairerMollifiedKernel N ρ' ε' z - hairerKernelTorus N z)]
            refine (abs_add_le _ _).trans' (le_of_eq ?_)
            congr 1; ring
        _ ≤ Cf * ε * s ^ (-(4 : ℝ)) + Cf' * ε' * s ^ (-(4 : ℝ)) := add_le_add hKe hKe'
        _ ≤ Cf * M * s ^ (-(4 : ℝ)) + Cf' * M * s ^ (-(4 : ℝ)) := by
          gcongr
        _ = _ := by ring
    have h2 := cmk_alg hM0 hMs hθ1
    have h3 : s ^ (-(3 + θ)) ≤ L ^ (3 + θ) * (s + m) ^ (-(3 + θ)) := by
      refine cmk_rpow_neg_le (by linarith) (by positivity) hL0 ?_
      have : M ≤ s / (8 * B) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h4 : s + m ≤ s + s / (8 * B) := by
        have : m ≤ M := (min_le_left _ _).trans (le_max_left _ _)
        linarith
      calc s + m ≤ s + s / (8 * B) := h4
        _ = L * s := by rw [hL]; field_simp
    have h5 : |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
        (Cf + Cf') * L ^ (3 + θ) * (M ^ θ * (s + m) ^ (-(3 + θ))) := by
      calc _ ≤ (Cf + Cf') * (M ^ θ * s ^ (-(3 + θ))) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ ≤ (Cf + Cf') * (M ^ θ * (L ^ (3 + θ) * (s + m) ^ (-(3 + θ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hMθ) (by positivity)
        _ = _ := by ring
    have h7 : (Cf + Cf') * L ^ (3 + θ) * (M ^ θ * (s + m) ^ (-(3 + θ))) ≤
        ((C0 + C0') * (8 * B + 1) + (Cf + Cf') * L ^ (3 + θ)) *
          (M ^ θ * (s + m) ^ (-(3 + θ))) :=
      mul_le_mul_of_nonneg_right (by linarith) hX
    calc _ ≤ _ := h5.trans h7
      _ = _ := by ring

/-- Away from the origin, the cross-mollifier difference is `≲ (max ε ε')^θ s(z)^(-3-θ)`. -/
theorem hairerMollifiedKernel_sub_abs_le_cross_of_pos (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 → ∀ z : SpaceTime,
      0 < torusParabolicSize z →
        |hairerMollifiedKernel N ρ ε z - hairerMollifiedKernel N ρ' ε' z| ≤
          C * (max ε ε') ^ θ * torusParabolicSize z ^ (-(3 + θ)) := by
  obtain ⟨C, hC, h⟩ := hairerMollifiedKernel_sub_abs_le_cross N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨C, hC, fun {ε ε'} hε hε1 hε' hε'1 z hz => ?_⟩
  refine (h hε hε1 hε' hε'1 z).trans ?_
  have hM : (0 : ℝ) ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.le) _
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hM)
  exact Real.rpow_le_rpow_of_nonpos hz (by linarith [lt_min hε hε']) (by linarith)

end RegularityStructures.Phi43

end
