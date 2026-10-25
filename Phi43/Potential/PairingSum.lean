/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Potential.NearPairing
public import Phi43.Potential.PairingGeneric
public import RegularityStructures.Abstract.Singular.WindowAt.Basic

/-!
# Pairing of the noise coordinate with a sum of scaled test functions

If `K = ∑_j g_j` pointwise, where `g_j` is a test function scaled at the base point `z_j`
(`0 ≤ z_j.1 ≤ 1`) with radius `R_j ≤ 1` and constant `A_j`, then (near-pair `Γ` hypothesis)

  `|∫ ξ K| ≤ ∑_j r4ModelConst · max(1, C_Γ) C_Π · (A_j R_j⁵) R_j^{deg o}`

provided `∑_j A_j R_j⁵ < ∞` and `ξ` is bounded on the strip `-1 ≤ t ≤ 2` (`abs_integral_family_le`).
Each term is the model pairing bound; the interchange of sum and integral is justified by
`hasSum_integral_of_summable_integral_norm`, with `∫ |g_j| ≤ 16 A_j R_j⁵`.
-/

public section

open MeasureTheory Filter Topology Set

namespace RegularityStructures.Potential

theorem abs_le_of_isScaledTest {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}
    (hg : IsScaledTest g z R A) (w : ParabolicSpace) : |g w| ≤ A := by
  have h := hg.deriv 0 (by norm_num) (parabolicDilate R⁻¹ (w - z))
  rw [norm_iteratedFDeriv_zero] at h
  have e : z + parabolicDilate R (parabolicDilate R⁻¹ (w - z)) = w := by
    rw [parabolicDilate_parabolicDilate_inv hg.radius_pos.ne']
    abel
  rw [e] at h
  simpa using h

theorem potAbsSubLe (z w : ParabolicSpace) (i : Fin 3) :
    |w.2 i - z.2 i| ≤ parabolicNorm (w - z) := by
  have h := Finset.single_le_sum (f := fun j => |(w - z).2 j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ i)
  unfold parabolicNorm
  have := Real.sqrt_nonneg |(w - z).1|
  simp only [Prod.snd_sub, Pi.sub_apply] at h ⊢
  linarith

theorem parabolicBall_subset_box (z : ParabolicSpace) {R : ℝ} :
    {w : ParabolicSpace | parabolicNorm (w - z) ≤ R} ⊆
      Icc (z.1 - R ^ 2) (z.1 + R ^ 2) ×ˢ Set.pi univ (fun i => Icc (z.2 i - R) (z.2 i + R)) := by
  intro w hw
  have h1 : Real.sqrt |w.1 - z.1| ≤ R := by
    have : Real.sqrt |(w - z).1| ≤ parabolicNorm (w - z) := by
      unfold parabolicNorm
      have := Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
        abs_nonneg ((w - z).2 i)
      linarith
    exact this.trans hw
  have hR : 0 ≤ R := (Real.sqrt_nonneg _).trans h1
  refine ⟨?_, fun i _ => ?_⟩
  · have := abs_time_sub_le_of_parabolicNorm_le (r := R) hw
    simp only [Prod.fst_sub] at this
    constructor <;> linarith [abs_le.1 this]
  · have := potAbsSubLe z w i
    have h2 := this.trans hw
    constructor <;> linarith [abs_le.1 h2]

theorem volume_parabolicBall_le (z : ParabolicSpace) {R : ℝ} (hR : 0 ≤ R) :
    volume {w : ParabolicSpace | parabolicNorm (w - z) ≤ R} ≤ ENNReal.ofReal (16 * R ^ 5) := by
  refine (measure_mono (parabolicBall_subset_box z)).trans (le_of_eq ?_)
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc]
  have e : ∀ x : Fin 3, z.2 x + R - (z.2 x - R) = 2 * R := fun x => by ring
  simp only [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
  congr 1
  ring

theorem integral_abs_le_of_isScaledTest {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}
    (hg : IsScaledTest g z R A) : ∫ w, |g w| ≤ 16 * A * R ^ 5 := by
  have hA : 0 ≤ A := hg.const_pos.le
  have hR := hg.radius_pos
  set S := {w : ParabolicSpace | parabolicNorm (w - z) ≤ R} with hS
  have hSm : MeasurableSet S := (isClosed_le (continuous_parabolicNorm.comp
    (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hle : ∀ w, |g w| ≤ S.indicator (fun _ => A) w := by
    intro w
    by_cases hw : w ∈ S
    · rw [indicator_of_mem hw]; exact abs_le_of_isScaledTest hg w
    · rw [indicator_of_notMem hw]
      have : R < parabolicNorm (w - z) := not_le.1 hw
      simp [hg.supp w this]
  have hvol : volume S < ⊤ := (volume_parabolicBall_le z hR.le).trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (S.indicator fun _ => A) :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hvol.ne)
  calc ∫ w, |g w| ≤ ∫ w, S.indicator (fun _ => A) w :=
        integral_mono hg.integrable.abs hint hle
    _ = A * (volume S).toReal := by
        rw [integral_indicator hSm, setIntegral_const]; simp [Measure.real, mul_comm]
    _ ≤ A * (16 * R ^ 5) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_parabolicBall_le z hR.le)
        rwa [ENNReal.toReal_ofReal (by positivity)] at this
    _ = _ := by ring

theorem hasCompactSupport_of_isScaledTest {g : ParabolicSpace → ℝ} {z : ParabolicSpace} {R A : ℝ}
    (hg : IsScaledTest g z R A) : HasCompactSupport g := by
  refine HasCompactSupport.intro
    (isCompact_Icc.prod (isCompact_univ_pi fun i => isCompact_Icc) :
      IsCompact (Icc (z.1 - R ^ 2) (z.1 + R ^ 2) ×ˢ
        Set.pi univ (fun i => Icc (z.2 i - R) (z.2 i + R)))) fun w hw => ?_
  by_contra hne
  exact hw (parabolicBall_subset_box z (R := R) (show parabolicNorm (w - z) ≤ R from by
    by_contra h; exact hne (hg.supp w (not_le.1 h))))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ}

/-- **Pairing with a sum of scaled test functions** (near-pair `Γ`). -/
theorem abs_integral_family_le (hPi : M.PiBoundOn γ CPi hairerTimeWindow) (hCPi : 0 ≤ CPi)
    (hGam : M.GammaNearOn γ CGam hairerTimeWindow) (hdeg : ∀ j, 𝒯.deg j < γ → -4 < 𝒯.deg j)
    {o : ι} (ho : 𝒯.deg o < γ) {ξ : ParabolicSpace → ℝ} (hξ : Continuous ξ) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |ξ u| ≤ B * (1 + parabolicNorm u) ^ n)
    (hreg : ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ y,
      M.regPi x (Pi.single o 1) t y = parabolicSemigroup.apply t ξ y)
    (hgrowth : ∀ z : ParabolicSpace, 0 ≤ z.1 → z.1 ≤ 1 → M.HasQualitativeGrowthAt γ z)
    {Bξ : ℝ} (hξb : ∀ y : ParabolicSpace, -1 ≤ y.1 → y.1 ≤ 2 → |ξ y| ≤ Bξ)
    {J : Type*} [Countable J] (zj : J → ParabolicSpace) (hzj : ∀ j, 0 ≤ (zj j).1 ∧ (zj j).1 ≤ 1)
    (g : J → ParabolicSpace → ℝ) (R A : J → ℝ) (hg : ∀ j, IsScaledTest (g j) (zj j) (R j) (A j))
    (K : ParabolicSpace → ℝ) (hK : ∀ y, HasSum (fun j => g j y) (K y))
    (hs1 : Summable fun j => A j * R j ^ 5)
    (hs2 : Summable fun j => r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A j * R j ^ 5) *
      R j ^ 𝒯.deg o) :
    |∫ y, ξ y * K y| ≤ ∑' j, r4ModelConst 𝒯 γ * (max 1 CGam * CPi) * (A j * R j ^ 5) *
      R j ^ 𝒯.deg o := by
  have hBξ : 0 ≤ Bξ := (abs_nonneg _).trans (hξb 0 (by simp) (by simp))
  have hwin : ∀ j y, g j y ≠ 0 → -1 ≤ y.1 ∧ y.1 ≤ 2 := by
    intro j y hy
    have hle : parabolicNorm (y - zj j) ≤ R j := by
      by_contra h; exact hy ((hg j).supp y (not_le.1 h))
    have := ball_subset_hairerTimeWindow (hzj j).1 (hzj j).2
      (hle.trans (hg j).radius_le_one)
    exact this
  have hF : ∀ j, Integrable fun y => ξ y * g j y := by
    intro j
    refine ((hg j).integrable.norm.const_mul Bξ).mono'
      ((hξ.mul (hg j).continuous).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    by_cases hy : g j y = 0
    · simp [hy]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hξb y (hwin j y hy).1 (hwin j y hy).2) (abs_nonneg _)
  have hnorm : Summable fun j => ∫ y, ‖ξ y * g j y‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun y => norm_nonneg _)
      (fun j => ?_) (hs1.mul_left (16 * Bξ))
    calc ∫ y, ‖ξ y * g j y‖ ≤ ∫ y, Bξ * |g j y| := by
          refine integral_mono (hF j).norm ((hg j).integrable.abs.const_mul Bξ) fun y => ?_
          by_cases hy : g j y = 0
          · simp [hy]
          · rw [norm_mul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hξb y (hwin j y hy).1 (hwin j y hy).2)
              (abs_nonneg _)
      _ = Bξ * ∫ y, |g j y| := integral_const_mul _ _
      _ ≤ Bξ * (16 * A j * R j ^ 5) :=
          mul_le_mul_of_nonneg_left (integral_abs_le_of_isScaledTest (hg j)) hBξ
      _ = 16 * Bξ * (A j * R j ^ 5) := by ring
  have hsum := hasSum_integral_of_summable_integral_norm hF hnorm
  have hpt : ∀ y, ∑' j, ξ y * g j y = ξ y * K y := fun y => ((hK y).mul_left (ξ y)).tsum_eq
  simp only [hpt] at hsum
  have hbd : ∀ j, |∫ y, ξ y * g j y| ≤ r4ModelConst 𝒯 γ * (max 1 CGam * CPi) *
      (A j * R j ^ 5) * R j ^ 𝒯.deg o := by
    intro j
    have hpair := pairing_eq_integral_of_bound hξ hB (hg j).continuous
      (hasCompactSupport_of_isScaledTest (hg j))
      (Λ := M.regPi (zj j) (Pi.single o 1)) (fun s hs => funext fun y => hreg (zj j) s hs y)
    rw [← hpair]
    exact (M.tendsto_abs_pairing_regPi_single_of_scaled_onWindowAt_near hPi hCPi hGam
      (hgrowth (zj j) (hzj j).1 (hzj j).2) hdeg ho
      (fun y hy => ball_subset_hairerTimeWindow (hzj j).1 (hzj j).2 hy) (hg j)).2
  rw [← hsum.tsum_eq]
  have hs3 : Summable fun j => |∫ y, ξ y * g j y| :=
    Summable.of_nonneg_of_le (fun j => abs_nonneg _) hbd hs2
  have h4 := norm_tsum_le_tsum_norm (f := fun j => ∫ y, ξ y * g j y) hs3
  simp only [Real.norm_eq_abs] at h4
  exact h4.trans (hs3.tsum_le_tsum hbd hs2)

end RegularityStructures.Potential

end
