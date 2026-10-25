/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.Deterministic
public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientIdentity
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Phi43.RegularisedNoise.SmoothVersion.TranslationCoefficient

/-!
# Translation of a finite-window Fourier coefficient

The translated kernel has a coefficient which is a fixed scalar times a character in the
translation variable.  This is the algebraic reason that the random Fourier series has smooth
coefficient functions, while the cut-off test modes themselves need only be square-integrable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate

namespace RegularityStructures.Phi43

private theorem norm_globalWindowFourierMode (L : ℝ) (k : Fin 4 → ℤ) (z : SpaceTime) :
    ‖globalWindowFourierMode L k z‖ = 1 := by
  unfold globalWindowFourierMode
  simp only [norm_mul, fourier_apply, Circle.norm_coe, norm_prod]
  simp

theorem mFourierCoeff_windowKernel_eq_character
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) (k : WindowFrequency)
    (hgp : Integrable
      (fun x : ℝ × (Fin 3 → ℝ) =>
        windowWeightedIntegrand (fun w => (Phi (z - w) : ℂ)) a b k
          (a + (b - a) * x.1, torusProj x.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1))))) :
    UnitAddTorus.mFourierCoeff
        (fun y : UnitAddTorus (Fin 4) => (Phi (z - windowPoint a b y) : ℂ)) k =
      (b - a)⁻¹ •
        (globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0) *
          (conj (globalWindowFourierMode (b - a) k z) *
            ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u)) := by
  have hN : 0 < N := lt_of_le_of_lt (abs_nonneg z.1) hz
  have hab : a < b := by
    rw [ha, hb]
    linarith
  have hPhiInt : Integrable Phi (volume : Measure SpaceTime) :=
    (Continuous.continuous_of_isSmoothOnSpaceTime hPhi).integrable_of_hasCompactSupport
      (hasCompactSupport_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR)
  have htrans : Integrable
      (fun w => (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w))
      (volume : Measure SpaceTime) := by
    have hcomp : Integrable (fun w : SpaceTime => (Phi (z - w) : ℂ))
        (volume : Measure SpaceTime) := by
      exact integrable_comp_sub_left_spaceTime (E := ℂ) hPhiInt.ofReal z
    apply hcomp.mul_bdd
    · exact (Complex.continuous_conj.measurable.comp
        (measurable_windowFourierModeShift a b k)).aestronglyMeasurable
    · filter_upwards [] with w
      rw [Complex.norm_conj, norm_windowFourierModeShift]
  have hzero : ∀ w : SpaceTime, w ∉ windowInterval a b → Phi (z - w) = 0 := by
    intro w hw
    have htime : w.1 ≤ a ∨ b < w.1 := by
      by_cases hle : w.1 ≤ a
      · exact Or.inl hle
      · right
        exact lt_of_not_ge fun hwb => hw ⟨⟨lt_of_not_ge hle, hwb⟩, mem_univ _⟩
    rcases htime with hleft | hright
    · apply hR
      by_cases hR0' : 0 ≤ R
      · have hzlow : -N < z.1 := (abs_lt.mp hz).1
        have hpos : 0 < z.1 - w.1 := by
          rw [ha] at hleft
          linarith
        change R < |z.1 - w.1|
        rw [abs_of_pos hpos]
        rw [ha] at hleft
        linarith
      · exact lt_of_lt_of_le (lt_of_not_ge hR0') (abs_nonneg _)
    · apply hR
      by_cases hR0' : 0 ≤ R
      · have hzupper : z.1 < N := (abs_lt.mp hz).2
        have hneg : z.1 - w.1 < 0 := by
          rw [hb] at hright
          linarith
        change R < |z.1 - w.1|
        rw [abs_of_neg hneg]
        rw [hb] at hright
        linarith
      · exact lt_of_lt_of_le (lt_of_not_ge hR0') (abs_nonneg _)
  have hset :
      (∫ w in windowInterval a b,
          (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w)) =
        ∫ w, (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w) := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun w : SpaceTime =>
        (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w))
      (s := windowInterval a b)
      (fun w hw => by
        have hw0 := congrArg (fun r : ℝ => (r : ℂ)) (hzero w hw)
        rw [hw0]
        simp)
  have hglobal_integral :
      (∫ w, (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w)) =
        globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0) *
          (conj (globalWindowFourierMode (b - a) k z) *
            ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u) := by
    let c := globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0)
    have htranslate :
        (∫ w, (Phi (z - w) : ℂ) *
            conj (globalWindowFourierMode (b - a) k w)) =
          conj (globalWindowFourierMode (b - a) k z) *
            ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u := by
      let g : SpaceTime → ℂ := fun u =>
        (Phi u : ℂ) * conj (globalWindowFourierMode (b - a) k (z - u))
      have hg : Integrable g (volume : Measure SpaceTime) := by
        apply hPhiInt.ofReal.mul_bdd
        · unfold globalWindowFourierMode
          fun_prop
        · filter_upwards [] with u
          rw [Complex.norm_conj, norm_globalWindowFourierMode]
      have hchange : (∫ w, g (z - w)) = ∫ u, g u :=
        integral_comp_sub_left_spaceTime g z
      have hleft : (fun w => g (z - w)) =
          (fun w => (Phi (z - w) : ℂ) *
            conj (globalWindowFourierMode (b - a) k w)) := by
        funext w
        dsimp [g]
        rw [sub_sub_cancel]
      have hchar : ∀ u : SpaceTime,
          conj (globalWindowFourierMode (b - a) k (z - u)) =
            conj (globalWindowFourierMode (b - a) k z) *
              globalWindowFourierMode (b - a) k u := by
        intro u
        rw [globalWindowFourierMode_sub]
        simp only [map_mul, Complex.conj_conj]
      calc
        (∫ w, (Phi (z - w) : ℂ) *
            conj (globalWindowFourierMode (b - a) k w)) =
            ∫ w, g (z - w) := by rw [hleft]
        _ = ∫ u, g u := hchange
        _ = ∫ u, conj (globalWindowFourierMode (b - a) k z) *
              ((Phi u : ℂ) * globalWindowFourierMode (b - a) k u) := by
          apply integral_congr_ae
          filter_upwards [] with u
          dsimp [g]
          rw [hchar]
          ring
        _ = conj (globalWindowFourierMode (b - a) k z) *
              ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u := by
          rw [integral_const_mul]
    calc
      (∫ w, (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w)) =
          ∫ w, c * ((Phi (z - w) : ℂ) *
            conj (globalWindowFourierMode (b - a) k w)) := by
        apply integral_congr_ae
        filter_upwards [] with w
        dsimp [c]
        rw [windowFourierModeShift_eq_globalWindowFourierMode_mul hab k w]
        simp only [map_mul, Complex.conj_conj]
        ring
      _ = c * ∫ w, (Phi (z - w) : ℂ) *
            conj (globalWindowFourierMode (b - a) k w) := by
        rw [integral_const_mul]
      _ = c * (conj (globalWindowFourierMode (b - a) k z) *
            ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u) := by
        rw [htranslate]
  calc
    UnitAddTorus.mFourierCoeff
        (fun y : UnitAddTorus (Fin 4) => (Phi (z - windowPoint a b y) : ℂ)) k =
        (b - a)⁻¹ • ∫ w in windowInterval a b,
          windowWeightedIntegrand (fun q => (Phi (z - q) : ℂ)) a b k w :=
      mFourierCoeff_windowPoint_eq_windowIntegral hab
        (integrable_comp_sub_left_spaceTime (E := ℂ) hPhiInt.ofReal z) k hgp
    _ = (b - a)⁻¹ • ∫ w in windowInterval a b,
          (Phi (z - w) : ℂ) * conj (windowFourierModeShift a b k w) := by rfl
    _ = (b - a)⁻¹ • ∫ w, (Phi (z - w) : ℂ) *
          conj (windowFourierModeShift a b k w) := by rw [hset]
    _ = (b - a)⁻¹ •
        (globalWindowFourierMode (b - a) k (a, fun _ : Fin 3 => 0) *
          (conj (globalWindowFourierMode (b - a) k z) *
            ∫ u, (Phi u : ℂ) * globalWindowFourierMode (b - a) k u)) := by
      rw [hglobal_integral]

theorem integrable_windowKernel_pullback
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (_hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (_hR0 : 0 ≤ R) {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) (k : WindowFrequency) :
    Integrable
      (fun x : ℝ × (Fin 3 → ℝ) =>
        windowWeightedIntegrand (fun w => (Phi (z - w) : ℂ)) a b k
          (a + (b - a) * x.1, torusProj x.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1)))) := by
  let μ : Measure (ℝ × (Fin 3 → ℝ)) :=
    (volume.restrict (Ioc (0 : ℝ) 1)).prod
      (Measure.pi (fun _ : Fin 3 => volume.restrict (Ioc (0 : ℝ) 1)))
  let F : ℝ × (Fin 3 → ℝ) → ℂ := fun x =>
    windowWeightedIntegrand (fun w => (Phi (z - w) : ℂ)) a b k
      (a + (b - a) * x.1, torusProj x.2)
  have htorus : Measurable (torusProj : (Fin 3 → ℝ) → Torus3) := by
    apply measurable_pi_iff.2
    intro i
    change Measurable (fun x : Fin 3 → ℝ => ((x i : ℝ) : UnitAddCircle))
    exact AddCircle.measurable_mk'.comp (measurable_pi_apply i)
  have hmap : Measurable
      (fun x : ℝ × (Fin 3 → ℝ) =>
        (a + (b - a) * x.1, torusProj x.2)) := by
    exact (measurable_const.add
      ((measurable_const.sub measurable_const).mul measurable_fst)).prodMk
      (htorus.comp measurable_snd)
  have hmeas : Measurable F := by
    unfold F windowWeightedIntegrand
    apply Measurable.mul
    · apply Complex.continuous_ofReal.measurable.comp
      apply (Continuous.continuous_of_isSmoothOnSpaceTime hPhi).measurable.comp
      exact measurable_const.sub hmap
    · apply Complex.continuous_conj.measurable.comp
      exact (measurable_windowFourierModeShift a b k).comp hmap
  have hμtop : μ Set.univ < ⊤ := by
    finiteness
  let _ : IsFiniteMeasure μ := ⟨hμtop⟩
  have hN : 0 < N := lt_of_le_of_lt (abs_nonneg z.1) hz
  have hab : a < b := by
    rw [ha, hb]
    linarith
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_univ (X := Torus3))).exists_bound_of_continuousOn
      (Continuous.continuous_of_isSmoothOnSpaceTime hPhi).continuousOn
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  have hfirst : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), t ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hpair : ∀ᵐ x ∂μ, x.1 ∈ Ioc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_preimage measurable_fst measurableSet_Ioc)).2
    filter_upwards [hfirst] with t ht
    exact ae_of_all _ (fun _ => ht)
  have hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖(B : ℂ)‖ := by
    filter_upwards [hpair] with x hx
    have hL : 0 < b - a := sub_pos.mpr hab
    have htime : z.1 - (a + (b - a) * x.1) ∈ Icc (z.1 - b) (z.1 - a) := by
      constructor
      · have hx' : x.1 ≤ 1 := hx.2
        have hmul : (b - a) * x.1 ≤ b - a :=
          mul_le_of_le_one_right (le_of_lt hL) hx'
        linarith
      · have hx' : 0 ≤ x.1 := le_of_lt hx.1
        have hmul : 0 ≤ (b - a) * x.1 := mul_nonneg hL.le hx'
        linarith
    have hq : (z - (a + (b - a) * x.1, torusProj x.2)) ∈
        Icc (z.1 - b) (z.1 - a) ×ˢ (Set.univ : Set Torus3) := by
      exact ⟨htime, mem_univ _⟩
    have hval : |Phi (z - (a + (b - a) * x.1, torusProj x.2))| ≤ B :=
      (hC _ hq).trans (le_max_left _ _)
    dsimp [F, windowWeightedIntegrand]
    rw [norm_mul, Complex.norm_conj, norm_windowFourierModeShift]
    simpa [Real.norm_eq_abs, abs_of_nonneg hB] using hval
  have hconst : Integrable (fun _ : ℝ × (Fin 3 → ℝ) => (B : ℂ)) μ := by
    exact integrable_const (c := (B : ℂ))
  have hres : Integrable F μ :=
    hconst.mono hmeas.aestronglyMeasurable hbound
  change Integrable F μ
  exact hres

end RegularityStructures.Phi43

end
