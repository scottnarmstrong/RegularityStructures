/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateModuliKernel
public import Phi43.Stochastic.ConstantsComparisonRemainderBound
public import Phi43.Stochastic.ConstantsComparisonDefinitions

/-!
# The `L³` translation modulus of the remainder `R = G - K^♯`

The remainder has the order-one bound `|R| ≲ size⁻¹`, and its increments satisfy
`|ΔR| ≤ |ΔG| + |ΔK| ≲ size(h) size⁻⁴`.  Interpolating the two with exponent `1/4` gives
`|ΔR| ≲ size(h)^{1/4} size⁻^{7/4}`, hence a power modulus in `L³`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_min_le_rpow_mul {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) : min x y ≤ x ^ θ * y ^ (1 - θ) := by
  have hnn : 0 ≤ x ^ θ * y ^ (1 - θ) :=
    mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)
  rcases hx.eq_or_lt with hx0 | hxp
  · have : min x y = 0 := by rw [← hx0]; exact min_eq_left hy
    rw [this]
    exact hnn
  rcases hy.eq_or_lt with hy0 | hyp
  · have : min x y = 0 := by rw [← hy0]; exact min_eq_right hx
    rw [this]
    exact hnn
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy]
    calc
      x = x ^ θ * x ^ (1 - θ) := by
        rw [← Real.rpow_add hxp]; simp
      _ ≤ x ^ θ * y ^ (1 - θ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx _)
        exact Real.rpow_le_rpow hx hxy (by linarith)
  · rw [min_eq_right hyx]
    calc
      y = y ^ θ * y ^ (1 - θ) := by
        rw [← Real.rpow_add hyp]; simp
      _ ≤ x ^ θ * y ^ (1 - θ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy _)
        exact Real.rpow_le_rpow hy hyx hθ0

theorem constantsRate_R_bound (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ z : SpaceTime ∂volume, 0 < torusParabolicSize z →
      |constantsComparisonR N z| ≤ A * torusParabolicSize z ^ (-(1 : ℝ)) := by
  obtain ⟨C₁, hC₁, h1⟩ := constantsComparisonR_orderOne_ae N
  obtain ⟨CG, hCG, hG⟩ := massiveHeatKernel_global_singular_bound
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  refine ⟨C₁ + CG + CK, by positivity, ?_⟩
  filter_upwards [h1] with z hz hσ
  by_cases hs : torusParabolicSize z ≤ 1
  · have := hz hσ hs
    have hn : 0 ≤ torusParabolicSize z ^ (-(1 : ℝ)) := Real.rpow_nonneg hσ.le _
    nlinarith [mul_nonneg hCG hn, mul_nonneg hCK hn]
  · have hs1 : 1 ≤ torusParabolicSize z := (not_le.mp hs).le
    have hpow : torusParabolicSize z ^ (-(3 : ℝ)) ≤ torusParabolicSize z ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
    have hn : 0 ≤ torusParabolicSize z ^ (-(1 : ℝ)) := Real.rpow_nonneg hσ.le _
    have hGz := hG z hσ
    have hKz := hK hσ
    rw [constantsComparisonR_def]
    calc
      |massiveHeatKernel z - hairerKernelTorus N z| ≤
          |massiveHeatKernel z| + |hairerKernelTorus N z| := abs_sub _ _
      _ ≤ CG * torusParabolicSize z ^ (-(3 : ℝ)) + CK * torusParabolicSize z ^ (-(3 : ℝ)) := by
        rw [abs_of_nonneg (massiveHeatKernel_nonneg z)]
        exact add_le_add hGz hKz
      _ ≤ CG * torusParabolicSize z ^ (-(1 : ℝ)) + CK * torusParabolicSize z ^ (-(1 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hCG) (mul_le_mul_of_nonneg_left hpow hCK)
      _ ≤ _ := by nlinarith [mul_nonneg hC₁ hn]

theorem constantsRate_R_memLp (N : ℕ) :
    MemLp (constantsComparisonR N) (ENNReal.ofReal 3) := by
  obtain ⟨A, hA, hR⟩ := constantsRate_R_bound N
  exact constantsRate_memLp_of_bound
    (measurable_massiveHeatKernel.sub (measurable_constantsComparison_hairerKernelTorus N))
    (q := 3) (a := 1) (A := A) (by norm_num) hA (by norm_num) (by norm_num) hR

theorem constantsRate_R_increment (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : SpaceTime, torusParabolicSize h ≤ 1 / 16 →
      ∀ᵐ z : SpaceTime ∂volume, 64 * torusParabolicSize h ≤ torusParabolicSize z →
        |constantsComparisonR N (z - h) - constantsComparisonR N z| ≤
          B * torusParabolicSize h ^ (1 / 4 : ℝ) * torusParabolicSize z ^ (-(7 / 4 : ℝ)) := by
  obtain ⟨A, hA, hR⟩ := constantsRate_R_bound N
  obtain ⟨BG, hBG, hG⟩ := constantsRate_massive_increment
  obtain ⟨BK, hBK, hK⟩ := constantsRate_hairerKernelTorus_increment N
  refine ⟨(BG + BK) ^ (1 / 4 : ℝ) * ((79 / 15) * A) ^ (3 / 4 : ℝ), by positivity, ?_⟩
  intro h hh
  have hRshift : ∀ᵐ z : SpaceTime ∂volume, 0 < torusParabolicSize (z - h) →
      |constantsComparisonR N (z - h)| ≤ A * torusParabolicSize (z - h) ^ (-(1 : ℝ)) :=
    (measurePreserving_sub_right (volume : Measure SpaceTime) h).quasiMeasurePreserving.ae hR
  filter_upwards [constantsRate_ae_size_pos, hR, hRshift] with z hz hRz hRzh hzh
  set r : ℝ := torusParabolicSize h with hr
  set σ : ℝ := torusParabolicSize z with hσ
  have hr0 : 0 ≤ r := torusParabolicSize_nonneg h
  have hsub := torusParabolicSize_sub_le z h
  have hlow : (15 / 64) * σ ≤ torusParabolicSize (z - h) := by linarith
  have hpos : 0 < (15 / 64) * σ := by positivity
  have hpos' : 0 < torusParabolicSize (z - h) := lt_of_lt_of_le hpos hlow
  have hRzh' : |constantsComparisonR N (z - h)| ≤ (64 / 15) * A * σ ^ (-(1 : ℝ)) := by
    have h1 := hRzh hpos'
    have h2 : torusParabolicSize (z - h) ^ (-(1 : ℝ)) ≤ ((15 / 64) * σ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
    have h3 : ((15 / 64) * σ) ^ (-(1 : ℝ)) = (64 / 15) * σ ^ (-(1 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num) hz.le, Real.rpow_neg_one, Real.rpow_neg_one]
      norm_num
    calc
      _ ≤ A * torusParabolicSize (z - h) ^ (-(1 : ℝ)) := h1
      _ ≤ A * (((15 / 64) * σ) ^ (-(1 : ℝ))) := mul_le_mul_of_nonneg_left h2 hA
      _ = (64 / 15) * A * σ ^ (-(1 : ℝ)) := by rw [h3]; ring
  have hRz' := hRz hz
  have hn1 : 0 ≤ σ ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have hn4 : 0 ≤ σ ^ (-(4 : ℝ)) := Real.rpow_nonneg hz.le _
  set X : ℝ := (BG + BK) * r * σ ^ (-(4 : ℝ)) with hX
  set Y : ℝ := (79 / 15) * A * σ ^ (-(1 : ℝ)) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hΔX : |constantsComparisonR N (z - h) - constantsComparisonR N z| ≤ X := by
    have e1 := hG z h hz hzh hh
    have e2 := hK z h hz (by linarith)
    rw [constantsComparisonR_def, constantsComparisonR_def]
    calc
      _ = |(massiveHeatKernel (z - h) - massiveHeatKernel z) -
          (hairerKernelTorus N (z - h) - hairerKernelTorus N z)| := by ring_nf
      _ ≤ |massiveHeatKernel (z - h) - massiveHeatKernel z| +
          |hairerKernelTorus N (z - h) - hairerKernelTorus N z| := abs_sub _ _
      _ ≤ BG * r * σ ^ (-(4 : ℝ)) + BK * r * σ ^ (-(4 : ℝ)) := add_le_add e1 e2
      _ = X := by rw [hX]; ring
  have hΔY : |constantsComparisonR N (z - h) - constantsComparisonR N z| ≤ Y := by
    calc
      _ ≤ |constantsComparisonR N (z - h)| + |constantsComparisonR N z| := abs_sub _ _
      _ ≤ (64 / 15) * A * σ ^ (-(1 : ℝ)) + A * σ ^ (-(1 : ℝ)) := add_le_add hRzh' hRz'
      _ = Y := by rw [hY]; ring
  have hmin := constantsRate_min_le_rpow_mul hX0 hY0 (θ := 1 / 4) (by norm_num) (by norm_num)
  have hle : |constantsComparisonR N (z - h) - constantsComparisonR N z| ≤ min X Y :=
    le_min hΔX hΔY
  refine hle.trans (hmin.trans (le_of_eq ?_))
  have hE : 0 ≤ BG + BK := by positivity
  have hA' : 0 ≤ (79 / 15) * A := by positivity
  have hXr : X ^ (1 / 4 : ℝ) = (BG + BK) ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) * σ ^ (-(1 : ℝ)) := by
    rw [hX, Real.mul_rpow (by positivity) hn4, Real.mul_rpow hE hr0, ← Real.rpow_mul hz.le]
    norm_num
  have hYr : Y ^ (1 - 1 / 4 : ℝ) = ((79 / 15) * A) ^ (3 / 4 : ℝ) * σ ^ (-(3 / 4 : ℝ)) := by
    rw [hY, Real.mul_rpow hA' hn1, ← Real.rpow_mul hz.le]
    norm_num
  rw [hXr, hYr]
  have hsig : σ ^ (-(1 : ℝ)) * σ ^ (-(3 / 4 : ℝ)) = σ ^ (-(7 / 4 : ℝ)) := by
    rw [← Real.rpow_add hz]
    norm_num
  calc
    (BG + BK) ^ (1 / 4 : ℝ) * r ^ (1 / 4 : ℝ) * σ ^ (-(1 : ℝ)) *
        (((79 / 15) * A) ^ (3 / 4 : ℝ) * σ ^ (-(3 / 4 : ℝ))) =
        (BG + BK) ^ (1 / 4 : ℝ) * ((79 / 15) * A) ^ (3 / 4 : ℝ) * r ^ (1 / 4 : ℝ) *
          (σ ^ (-(1 : ℝ)) * σ ^ (-(3 / 4 : ℝ))) := by ring
    _ = _ := by rw [hsig]

theorem constantsRate_R_modulus (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : SpaceTime, 0 < torusParabolicSize h →
      ∫⁻ z, ‖constantsComparisonR N (z - h) - constantsComparisonR N z‖ₑ ^ (3 : ℝ) ≤
        ENNReal.ofReal (C * torusParabolicSize h ^ (1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hR⟩ := constantsRate_R_bound N
  obtain ⟨B, hB, hinc⟩ := constantsRate_R_increment N
  have hRm : Measurable (constantsComparisonR N) :=
    measurable_massiveHeatKernel.sub (measurable_constantsComparison_hairerKernelTorus N)
  have hmod := constantsRate_translation_modulus (f := constantsComparisonR N) hRm
    (q := 3) (a := 1) (A := A) (c := 7 / 4) (B := B) (θ := 1 / 4) (κ := 64) (r₀ := 1 / 16)
    (by norm_num) (by norm_num) (by norm_num) hA (by norm_num) hB (by norm_num) (by norm_num)
    hR hinc
  obtain ⟨C, hC, hC'⟩ := hmod
  have hmem := constantsRate_R_memLp N
  have hall := constantsRate_modulus_all (f := constantsComparisonR N) hRm
    (q := 3) (by norm_num) hmem (C := C)
    (γ := min (5 - 1 * 3) (1 / 4 * 3 + 5 - 7 / 4 * 3))
    (r₀ := 1 / 16) hC (by norm_num) (by norm_num) hC'
  obtain ⟨C', hC'0, hC''⟩ := hall
  refine ⟨C', hC'0, fun h hh => ?_⟩
  have := hC'' h hh
  have hγ : min (5 - 1 * 3 : ℝ) (1 / 4 * 3 + 5 - 7 / 4 * 3) = 1 / 2 := by norm_num
  rwa [hγ] at this

end RegularityStructures.Phi43

end
