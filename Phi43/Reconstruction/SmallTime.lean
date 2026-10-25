/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.UnitIdentity
public import Phi43.Reconstruction.HeatPotentialBound
public import RegularityStructures.Abstract.Singular.Ident.LatticeAvg

/-!
# The behaviour of the reconstruction as `t → 0`

Part of the derivation of the mild equation (continuity at `t = s` with value `w_s`). The unit
coordinate satisfies the singular bound `|U(t, x)_1| ≤ ‖U‖ t^{η/2}` (`abs_unit_le`), hence
`w = ⟨1, U⟩ + K ∗ ζ` and `w³ - c w` are bounded by `C t^{η/2}`, `C t^{3η/2}`, and the heat potential
term of the unit identity is at most `C t^{1 + 3η/2} → 0` (`3η/2 > -1`): `w(t) → u(s)` uniformly
(`phi43_small_time`).
-/

public section

open Set MeasureTheory Filter Topology RegularityStructures.PDE

namespace RegularityStructures.Phi43

open Inhomogeneity

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

theorem abs_unit_le (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T)
    {noise : CanonicalNoise} {s : ℝ} (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : Fin 3 → ℝ) :
    |S.U.val (t, x) (.old .one)| ≤ ‖S.U‖ * t ^ ((η : ℝ) / 2) := by
  have hy : ((t, x) : ParabolicSpace) ∈ timeSlab T := ⟨ht.1, ht.2⟩
  have hρ : 0 < timeZeroDist ((t, x) : ParabolicSpace) :=
    Inhomogeneity.timeZeroDist_pos_of_mem_timeSlab hy
  have hk : 0 < κ.1 := κ.2.1
  have hdeg : (phi43RegularityStructureF κ).deg (.old .one) < gamma κ := by
    change homogeneity κ .one < gamma κ
    simp only [homogeneity, gamma]
    linarith
  have h := S.U.singularBoundOn_norm.1 _ hy hρ (.old .one) hdeg
  have hd0 : (phi43RegularityStructureF κ).deg (.old .one) = 0 := rfl
  rw [hd0, sub_zero, min_eq_left η.2.le,
    Model.singularWeight_timeZeroDist_eq hy hyp.hT1] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.1.le]
  congr 1
  ring

/-- The potential `K ∗ ζ` as a continuous path in `C(T³)`. -/
@[expose] noncomputable def psiPath (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) : ℝ → C(Torus3, ℝ) :=
  forcePath (perSmooth_phi43PsiAt N κ noise C)

theorem psiPath_apply (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants)
    (r : ℝ) (y : Fin 3 → ℝ) : psiPath N κ noise C r (torusProj y) = phi43PsiAt N κ noise C (r, y) :=
  forcePath_apply _ r y

theorem continuous_psiPath (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) : Continuous (psiPath N κ noise C) :=
  continuous_forcePath _

theorem abs_phi43PsiAt_le (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (s T : ℝ) :
    ∃ Mψ : ℝ, 0 ≤ Mψ ∧ ∀ t ∈ Icc 0 T, ∀ x : Fin 3 → ℝ,
      |phi43PsiAt N κ noise C (t + s, x)| ≤ Mψ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    ((continuous_psiPath N κ noise C).comp (continuous_id.add continuous_const)).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t ht x => ?_⟩
  have := hM t ht
  rw [← psiPath_apply N κ noise C (t + s) x]
  exact ((psiPath N κ noise C (t + s)).norm_coe_le_norm _).trans (this.trans (le_max_left _ _))

theorem one_le_rpow_neg {t e : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (he : e ≤ 0) : 1 ≤ t ^ e :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 he

/-- `|w| ≤ A t^{η/2}` for `w = ⟨1, U⟩ + K ∗ ζ` (`0 < t ≤ T`). -/
theorem abs_W_le (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T)
    {noise : CanonicalNoise} {s : ℝ} (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    (C : RenormalisationConstants) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      |S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x)| ≤ A * t ^ ((η : ℝ) / 2) := by
  obtain ⟨Mψ, hMψ0, hMψ⟩ := abs_phi43PsiAt_le N κ noise C s T
  refine ⟨‖S.U‖ + Mψ, add_nonneg (norm_nonneg _) hMψ0, fun t ht x => ?_⟩
  have h1 := abs_unit_le hyp S ht x
  have h2 := hMψ t ⟨ht.1.le, ht.2⟩ x
  have h3 : 1 ≤ t ^ ((η : ℝ) / 2) := one_le_rpow_neg ⟨ht.1, ht.2.trans hyp.hT1⟩ (by
    have := η.2; linarith)
  calc |S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x)|
      ≤ |S.U.val (t, x) (.old .one)| + |phi43PsiAt N κ noise C (t + s, x)| := abs_add_le _ _
    _ ≤ ‖S.U‖ * t ^ ((η : ℝ) / 2) + Mψ * t ^ ((η : ℝ) / 2) :=
        add_le_add h1 (h2.trans (le_mul_of_one_le_right hMψ0 h3))
    _ = _ := by ring

/-- `|w³ - c w| ≤ D t^{3η/2}` (`0 < t ≤ T`). -/
theorem abs_cubic_le (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T)
    {noise : CanonicalNoise} {s : ℝ} (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s)
    (C : RenormalisationConstants) (c : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      |(S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x)) ^ 3 -
        c * (S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x))| ≤
        D * t ^ (3 * (η : ℝ) / 2) := by
  obtain ⟨A, hA0, hA⟩ := abs_W_le hyp S C
  refine ⟨A ^ 3 + |c| * A, by positivity, fun t ht x => ?_⟩
  have ht1 : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hyp.hT1⟩
  have hw := hA t ht x
  set w := S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x)
  have hη0 : (η : ℝ) < 0 := η.2
  have hp1 : 1 ≤ t ^ ((η : ℝ) / 2) := one_le_rpow_neg ht1 (by linarith)
  have hp0 : 0 ≤ t ^ ((η : ℝ) / 2) := Real.rpow_nonneg ht.1.le _
  have hcube : (t ^ ((η : ℝ) / 2)) ^ 3 = t ^ (3 * (η : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    congr 1
    push_cast
    ring
  have hle : t ^ ((η : ℝ) / 2) ≤ t ^ (3 * (η : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht1.2 (by linarith)
  have hw3 : |w| ^ 3 ≤ A ^ 3 * t ^ (3 * (η : ℝ) / 2) := by
    calc |w| ^ 3 ≤ (A * t ^ ((η : ℝ) / 2)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hw 3
      _ = A ^ 3 * t ^ (3 * (η : ℝ) / 2) := by rw [mul_pow, hcube]
  calc |w ^ 3 - c * w| ≤ |w ^ 3| + |c * w| := abs_sub _ _
    _ = |w| ^ 3 + |c| * |w| := by rw [abs_pow, abs_mul]
    _ ≤ A ^ 3 * t ^ (3 * (η : ℝ) / 2) + |c| * (A * t ^ (3 * (η : ℝ) / 2)) := by
        refine add_le_add hw3 (mul_le_mul_of_nonneg_left (hw.trans ?_) (abs_nonneg _))
        exact mul_le_mul_of_nonneg_left hle hA0
    _ = _ := by ring

/-- **Behaviour as `t → 0`**: `w(t, ·) → u(s)` uniformly. -/
theorem phi43_small_time (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - (η : ℝ))
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ}
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s) (us : C(Torus3, ℝ))
    (hws : ∀ x : Fin 3 → ℝ, S.ws (torusProj x) = us (torusProj x) - phi43PsiAt N κ noise C (s, x)) :
    ∃ E : ℝ → ℝ, Tendsto E (𝓝[>] 0) (𝓝 0) ∧ ∀ t ∈ Ioc 0 T, ∀ x : Fin 3 → ℝ,
      |S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x) - us (torusProj x)| ≤ E t := by
  have hη0 : (η : ℝ) < 0 := η.2
  have hη3 : -1 < 3 * (η : ℝ) / 2 := by linarith
  obtain ⟨D, hD0, hD⟩ := abs_cubic_le hyp S C (3 * C₁ C - 9 * C₂ C)
  -- the forcing
  obtain ⟨Mζ, hMζ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (continuous_forcePath (Potential.perSmooth_zeta_restart noise N s)).continuousOn
  set E : ℝ → ℝ := fun t => ‖heatOp t S.ws - S.ws‖ + max Mζ 0 * t +
    ‖psiPath N κ noise C (t + s) - psiPath N κ noise C s‖ +
      D * (t ^ (3 * (η : ℝ) / 2 + 1) / (3 * (η : ℝ) / 2 + 1)) with hE
  refine ⟨E, ?_, fun t ht x => ?_⟩
  · -- the limit
    have h1 : Tendsto (fun t => ‖heatOp t S.ws - S.ws‖) (𝓝[>] 0) (𝓝 0) := by
      have := (continuous_heatOp_left S.ws).tendsto 0
      rw [heatOp_zero_left] at this
      have h := (tendsto_iff_norm_sub_tendsto_zero.1 this).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi 0))
      exact h
    have h2 : Tendsto (fun t : ℝ => max Mζ 0 * t) (𝓝[>] 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (max Mζ 0)
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun t => ‖psiPath N κ noise C (t + s) - psiPath N κ noise C s‖)
        (𝓝[>] 0) (𝓝 0) := by
      have hc : Tendsto (fun t : ℝ => psiPath N κ noise C (t + s)) (𝓝 0)
          (𝓝 (psiPath N κ noise C s)) := by
        have hcc : Continuous fun t : ℝ => psiPath N κ noise C (t + s) :=
          (continuous_psiPath N κ noise C).comp (continuous_id.add continuous_const)
        have := hcc.tendsto 0
        simpa only [zero_add] using this
      exact (tendsto_iff_norm_sub_tendsto_zero.1 hc).mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun t : ℝ => D * (t ^ (3 * (η : ℝ) / 2 + 1) / (3 * (η : ℝ) / 2 + 1)))
        (𝓝[>] 0) (𝓝 0) := by
      have hpos : 0 < 3 * (η : ℝ) / 2 + 1 := by linarith
      have := ((Real.continuous_rpow_const hpos.le).tendsto 0)
      rw [Real.zero_rpow hpos.ne'] at this
      have h := (this.div_const (3 * (η : ℝ) / 2 + 1)).const_mul D
      simpa using h.mono_left nhdsWithin_le_nhds
    have := ((h1.add h2).add h3).add h4
    simpa [hE] using this
  · -- the pointwise estimate
    have hid := phi43_unit_identity hyp hN hη₁ hκη noise Cg q hg C hC S ht x
    set I := ∫ y, heatKernelR4 (((t, x) : ParabolicSpace) - y) * (timeSlab T).indicator (fun y =>
        (phi43PsiAt N κ noise C (y + LiftBounds.restartPoint s) + S.U.val y (.old .one)) ^ 3 -
          (3 * C₁ C - 9 * C₂ C) * (phi43PsiAt N κ noise C (y + LiftBounds.restartPoint s) +
            S.U.val y (.old .one))) y with hI
    have hus := hws x
    have hts : 0 < ((t, x) : ParabolicSpace).1 := ht.1
    have b1 : |heatOp t S.ws (torusProj x) - S.ws (torusProj x)| ≤ ‖heatOp t S.ws - S.ws‖ := by
      have := (heatOp t S.ws - S.ws).norm_coe_le_norm (torusProj x)
      simpa using this
    have b2 : |duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x)| ≤ max Mζ 0 * t := by
      rw [duhamelField_of_pos _ hts]
      have := norm_duhamel_le_mul (continuous_forcePath (Potential.perSmooth_zeta_restart noise N s))
        ht.1.le (M := max Mζ 0) (fun r hr => (hMζ r ⟨hr.1, hr.2.trans ht.2⟩).trans (le_max_left _ _))
      exact ((Real.norm_eq_abs _ ▸ (duhamel _ t).norm_coe_le_norm (torusProj x))).trans this
    have b3 : |phi43PsiAt N κ noise C (t + s, x) - phi43PsiAt N κ noise C (s, x)| ≤
        ‖psiPath N κ noise C (t + s) - psiPath N κ noise C s‖ := by
      have := (psiPath N κ noise C (t + s) - psiPath N κ noise C s).norm_coe_le_norm (torusProj x)
      simpa [psiPath_apply] using this
    have b4 : |I| ≤ D * (t ^ (3 * (η : ℝ) / 2 + 1) / (3 * (η : ℝ) / 2 + 1)) := by
      have hgm : Measurable fun r : ℝ => D * |r| ^ (3 * (η : ℝ) / 2) := by fun_prop
      have hg0 : ∀ r : ℝ, 0 ≤ D * |r| ^ (3 * (η : ℝ) / 2) := fun r =>
        mul_nonneg hD0 (Real.rpow_nonneg (abs_nonneg _) _)
      have hint : IntervalIntegrable (fun r : ℝ => D * |r| ^ (3 * (η : ℝ) / 2)) volume 0 t := by
        refine IntervalIntegrable.congr (fun r hr => ?_)
          ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hη3).const_mul D)
        have hr0 : 0 ≤ r := by
          rw [uIoc_of_le ht.1.le] at hr
          exact hr.1.le
        simp only [abs_of_nonneg hr0]
      have hb := abs_heatPotential_le hg0 hgm ht.1 ht.2 hint (fun y => (phi43PsiAt N κ noise C
        (y + LiftBounds.restartPoint s) + S.U.val y (.old .one)) ^ 3 - (3 * C₁ C - 9 * C₂ C) *
          (phi43PsiAt N κ noise C (y + LiftBounds.restartPoint s) + S.U.val y (.old .one)))
        (fun r hr y => by
          have h := hD r ⟨hr.1, hr.2.trans ht.2⟩ y
          rw [restartPoint_add, add_comm]
          rw [abs_of_pos hr.1]
          exact h) x
      refine hb.trans (le_of_eq ?_)
      have hpos : 0 < 3 * (η : ℝ) / 2 + 1 := by linarith
      have e1 : ∫ r in (0 : ℝ)..t, D * |r| ^ (3 * (η : ℝ) / 2) =
          ∫ r in (0 : ℝ)..t, D * r ^ (3 * (η : ℝ) / 2) := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le ht.1.le] at hr
        simp only [abs_of_nonneg hr.1]
      rw [e1, intervalIntegral.integral_const_mul, integral_rpow (Or.inl hη3),
        Real.zero_rpow hpos.ne', sub_zero]
    have hexpr : S.U.val (t, x) (.old .one) + phi43PsiAt N κ noise C (t + s, x) - us (torusProj x) =
        (heatOp t S.ws (torusProj x) - S.ws (torusProj x)) +
          duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x) +
          (phi43PsiAt N κ noise C (t + s, x) - phi43PsiAt N κ noise C (s, x)) - I := by
      rw [hid]
      have : us (torusProj x) = S.ws (torusProj x) + phi43PsiAt N κ noise C (s, x) := by
        rw [hus]; ring
      rw [this]
      ring
    rw [hexpr]
    calc _ ≤ |heatOp t S.ws (torusProj x) - S.ws (torusProj x)| +
          |duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x)| +
          |phi43PsiAt N κ noise C (t + s, x) - phi43PsiAt N κ noise C (s, x)| + |I| := by
            refine (abs_sub _ _).trans ?_
            refine add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl
      _ ≤ _ := by simp only [hE]; linarith

end RegularityStructures.Phi43

end
