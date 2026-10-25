/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.SmallTime
public import Phi43.Reconstruction.ScalarUniqueness

/-!
# Spatial periodicity of the unit coordinate of the fixed point

The unit identity (`phi43_unit_identity`) is a closed integral equation for `U_1`: the data
`P_t w_s`, `θ_s`, `K ∗ ζ` are periodic in space and the nonlinearity depends on `U_1` only.  For a
lattice vector `c` the difference `d(t, x) = U_1(t, x + c) - U_1(t, x)` therefore satisfies
`|d(t, x)| ≤ ∫₀ᵗ (3A² r^η + |c₀|) sup_y |d(r, y)| dr` and `|d| ≤ 2‖U‖ t^{η/2}`, hence `d = 0` by the
weighted Gronwall lemma `scalar_uniqueness` (`phi43_unit_periodic`).
-/

public section

open Set MeasureTheory RegularityStructures.PDE

namespace RegularityStructures.Phi43

open Inhomogeneity

theorem abs_cubic_sub_le {w₁ w₂ m c : ℝ} (h₁ : |w₁| ≤ m) (h₂ : |w₂| ≤ m) :
    |(w₂ ^ 3 - c * w₂) - (w₁ ^ 3 - c * w₁)| ≤ (3 * m ^ 2 + |c|) * |w₂ - w₁| := by
  have e : (w₂ ^ 3 - c * w₂) - (w₁ ^ 3 - c * w₁) = (w₂ - w₁) * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2 - c) := by
    ring
  rw [e, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hm : 0 ≤ m := (abs_nonneg _).trans h₁
  have h3 : |w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2| ≤ 3 * m ^ 2 := by
    calc |w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2| ≤ |w₂ ^ 2 + w₂ * w₁| + |w₁ ^ 2| := abs_add_le _ _
      _ ≤ |w₂ ^ 2| + |w₂ * w₁| + |w₁ ^ 2| := by gcongr; exact abs_add_le _ _
      _ = |w₂| ^ 2 + |w₂| * |w₁| + |w₁| ^ 2 := by rw [abs_pow, abs_mul, abs_pow]
      _ ≤ m ^ 2 + m * m + m ^ 2 := by gcongr
      _ = 3 * m ^ 2 := by ring
  calc |w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2 - c| ≤ |w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2| + |c| := abs_sub _ _
    _ ≤ 3 * m ^ 2 + |c| := by linarith

variable {κ : Kappa} {N : ℕ} {η : NegExponent}
  {M : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {CPi CGam CΓ CGam₁ CΓ₁ T : ℝ}

/-- **Spatial periodicity of the unit coordinate of the fixed point.** -/
theorem phi43_unit_periodic (hyp : Phi43NearHyp κ N M CPi CGam CΓ CGam₁ CΓ₁ T) (hN : 3 ≤ N)
    (hη₁ : -2 / 3 < (η : ℝ)) (hκη : κ.1 < -1 / 2 - (η : ℝ))
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) {s : ℝ}
    (hC : Restart.EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate
      (LiftBounds.restartPoint s)) M)
    (S : Phi43RestartSolution N η hyp.real.poly hyp.hT1 noise s) :
    ∀ t ∈ Ioc 0 T, ∀ (x c : Fin 3 → ℝ), torusProj c = 0 →
      S.U.val (t, x + c) (.old .one) = S.U.val (t, x) (.old .one) := by
  intro t₀ ht₀ x₀ c hc
  have hη0 : (η : ℝ) < 0 := η.2
  set ĉ := 3 * C₁ C - 9 * C₂ C with hĉ
  have hψ := perSmooth_phi43PsiAt N κ noise C
  have hψc : Continuous (phi43PsiAt N κ noise C) := hψ.smooth.continuous
  obtain ⟨A, hA0, hA⟩ := abs_W_le hyp S C
  set τ : ParabolicSpace := ((0 : ℝ), c) with hτ
  set a := LiftBounds.restartPoint s with ha
  -- the integrand
  set Gf : ParabolicSpace → ℝ := fun y => (phi43PsiAt N κ noise C (y + a) + S.U.val y (.old .one)) ^ 3 -
    ĉ * (phi43PsiAt N κ noise C (y + a) + S.U.val y (.old .one)) with hGf
  have hUm : Measurable fun y : ParabolicSpace => S.U.val y (.old .one) :=
    (measurable_pi_apply (SymbolF.old Symbol.one)).comp S.U.measurable
  have hGm : Measurable Gf := by
    have : Measurable fun y : ParabolicSpace => phi43PsiAt N κ noise C (y + a) :=
      hψc.measurable.comp (measurable_id.add_const a)
    simp only [hGf]
    exact ((this.add hUm).pow_const 3).sub (measurable_const.mul (this.add hUm))
  have hGτ : ∀ y : ParabolicSpace, Gf (y + τ) = (phi43PsiAt N κ noise C (y + a) +
      S.U.val (y + τ) (.old .one)) ^ 3 - ĉ * (phi43PsiAt N κ noise C (y + a) +
        S.U.val (y + τ) (.old .one)) := by
    intro y
    have e : phi43PsiAt N κ noise C (y + τ + a) = phi43PsiAt N κ noise C (y + a) := by
      have := hψ.periodic (y + a) c hc
      have e2 : y + τ + a = ((y + a).1, (y + a).2 + c) := by
        refine Prod.ext (by simp [hτ, ha, LiftBounds.restartPoint]) ?_
        funext i
        simp only [hτ, ha, LiftBounds.restartPoint, Prod.snd_add, Pi.add_apply, Pi.zero_apply]
        ring
      rw [e2, this]
    simp only [hGf, e]
  have e0 : ∀ (r : ℝ) (y : Fin 3 → ℝ), phi43PsiAt N κ noise C (((r, y) : ParabolicSpace) + a) =
      phi43PsiAt N κ noise C (r + s, y) := fun r y => by rw [ha, restartPoint_add]
  set d : ℝ → (Fin 3 → ℝ) → ℝ := fun t x => S.U.val (t, x + c) (.old .one) -
    S.U.val (t, x) (.old .one) with hd
  refine sub_eq_zero.1 (scalar_uniqueness (η := (η : ℝ)) (d := d) (a₀ := 3 * A ^ 2) (b₀ := |ĉ|) (T := T)
    (B := 2 * ‖S.U‖) hη₁ hη0 (by positivity) (abs_nonneg _) (by positivity) ?_ ?_ t₀ ht₀ x₀)
  · intro t ht x
    have h1 := abs_unit_le hyp S ht (x + c)
    have h2 := abs_unit_le hyp S ht x
    simp only [hd]
    calc |S.U.val (t, x + c) (.old .one) - S.U.val (t, x) (.old .one)| ≤
        |S.U.val (t, x + c) (.old .one)| + |S.U.val (t, x) (.old .one)| := abs_sub _ _
      _ ≤ _ := by linarith
  · refine fun t ht x g hg0 hgm hgi hgb => ?_
    obtain ⟨D, hD0, hD⟩ := abs_cubic_le hyp S C ĉ
    -- the bound for `Gf`
    have hGb : ∀ r ∈ Ioc 0 T, ∀ y : Fin 3 → ℝ, |Gf (r, y)| ≤ D * r ^ (3 * (η : ℝ) / 2) := by
      intro r hr y
      have h := hD r hr y
      have e : Gf (r, y) = (S.U.val (r, y) (.old .one) + phi43PsiAt N κ noise C (r + s, y)) ^ 3 -
          ĉ * (S.U.val (r, y) (.old .one) + phi43PsiAt N κ noise C (r + s, y)) := by
        simp only [hGf, e0]
        ring
      rw [e]
      exact h
    set g₁ : ℝ → ℝ := fun r => D * |r| ^ (3 * (η : ℝ) / 2) with hg₁
    have hg₁0 : ∀ r, 0 ≤ g₁ r := fun r => mul_nonneg hD0 (Real.rpow_nonneg (abs_nonneg _) _)
    have hg₁m : Measurable g₁ := by simp only [hg₁]; fun_prop
    have hη3 : -1 < 3 * (η : ℝ) / 2 := by linarith
    have hg₁i : IntervalIntegrable g₁ volume 0 t := by
      refine IntervalIntegrable.congr (fun r hr => ?_)
        ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) hη3).const_mul D)
      have hr0 : 0 ≤ r := by
        rw [uIoc_of_le ht.1.le] at hr
        exact hr.1.le
      simp only [hg₁, abs_of_nonneg hr0]
    set G' : ParabolicSpace → ℝ := fun y => Gf (y + τ) with hG'
    have hG'm : Measurable G' := hGm.comp (measurable_id.add_const τ)
    have hG'b : ∀ r ∈ Ioc 0 t, ∀ y : Fin 3 → ℝ, |G' (r, y)| ≤ g₁ r := by
      intro r hr y
      have e : ((r, y) : ParabolicSpace) + τ = (r, y + c) := by
        ext <;> simp [hτ]
      have := hGb r ⟨hr.1, hr.2.trans ht.2⟩ (y + c)
      simp only [hG', e, hg₁, abs_of_pos hr.1]
      exact this
    have hGb' : ∀ r ∈ Ioc 0 t, ∀ y : Fin 3 → ℝ, |Gf (r, y)| ≤ g₁ r := by
      intro r hr y
      have := hGb r ⟨hr.1, hr.2.trans ht.2⟩ y
      simp only [hg₁, abs_of_pos hr.1]
      exact this
    have hI₁ := integrable_heatPotential hg₁0 hg₁m ht.2 hg₁i Gf hGm hGb' x
    have hI₂ := integrable_heatPotential hg₁0 hg₁m ht.2 hg₁i G' hG'm hG'b x
    -- the unit identities
    have hid₁ := phi43_unit_identity hyp hN hη₁ hκη noise Cg q hg C hC S ht x
    have hid₂ := phi43_unit_identity hyp hN hη₁ hκη noise Cg q hg C hC S ht (x + c)
    have hprojc : torusProj (x + c) = torusProj x := by
      rw [torusProj_add, hc, add_zero]
    have hθ : duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x + c) =
        duhamelField (Potential.perSmooth_zeta_restart noise N s) (t, x) := by
      rw [duhamelField_of_pos _ ht.1, duhamelField_of_pos _ ht.1]
      simp only [hprojc]
    -- the translation of the integral
    have hshift : (∫ y, heatKernelR4 (((t, x + c) : ParabolicSpace) - y) *
        (timeSlab T).indicator Gf y) = ∫ y, heatKernelR4 (((t, x) : ParabolicSpace) - y) *
        (timeSlab T).indicator G' y := by
      have h := integral_add_right_eq_self (μ := (volume : Measure ParabolicSpace))
        (fun y : ParabolicSpace => heatKernelR4 (((t, x + c) : ParabolicSpace) - y) *
          (timeSlab T).indicator Gf y) τ
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have e : ((t, x + c) : ParabolicSpace) - (y + τ) = (t, x) - y := by
        ext <;> simp [hτ]
      have hmem : y + τ ∈ timeSlab T ↔ y ∈ timeSlab T := by
        simp [timeSlab, hτ]
      simp only [e]
      congr 1
      by_cases hy : y ∈ timeSlab T
      · rw [indicator_of_mem (hmem.2 hy), indicator_of_mem hy]
      · rw [indicator_of_notMem (fun h => hy (hmem.1 h)), indicator_of_notMem hy]
    have hdexpr : d t x = (∫ y, heatKernelR4 (((t, x) : ParabolicSpace) - y) *
          (timeSlab T).indicator Gf y) - ∫ y, heatKernelR4 (((t, x) : ParabolicSpace) - y) *
          (timeSlab T).indicator G' y := by
      simp only [hd]
      rw [hid₂, hid₁, hprojc, hθ, hshift]
      ring
    rw [hdexpr, ← integral_sub hI₁ hI₂]
    have hsub : (fun y : ParabolicSpace => heatKernelR4 (((t, x) : ParabolicSpace) - y) *
          (timeSlab T).indicator Gf y - heatKernelR4 (((t, x) : ParabolicSpace) - y) *
          (timeSlab T).indicator G' y) = fun y => heatKernelR4 (((t, x) : ParabolicSpace) - y) *
          (timeSlab T).indicator (fun y => Gf y - G' y) y := by
      funext y
      by_cases hy : y ∈ timeSlab T
      · simp only [indicator_of_mem hy]; ring
      · simp only [indicator_of_notMem hy]; ring
    rw [hsub]
    -- the pointwise estimate of the difference
    have hdiffb : ∀ r ∈ Ioc 0 t, ∀ y : Fin 3 → ℝ, |Gf (r, y) - G' (r, y)| ≤ g r := by
      intro r hr y
      have hrT : r ∈ Ioc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
      have e : ((r, y) : ParabolicSpace) + τ = (r, y + c) := by
        ext <;> simp [hτ]
      have hpsi : phi43PsiAt N κ noise C (r + s, y + c) = phi43PsiAt N κ noise C (r + s, y) :=
        hψ.periodic (r + s, y) c hc
      set w₁ := S.U.val (r, y) (.old .one) + phi43PsiAt N κ noise C (r + s, y) with hw₁
      set w₂ := S.U.val (r, y + c) (.old .one) + phi43PsiAt N κ noise C (r + s, y) with hw₂
      have hA₁ : |w₁| ≤ A * r ^ ((η : ℝ) / 2) := hA r hrT y
      have hA₂ : |w₂| ≤ A * r ^ ((η : ℝ) / 2) := by
        have := hA r hrT (y + c)
        rwa [hpsi] at this
      have hGe₁ : Gf (r, y) = w₁ ^ 3 - ĉ * w₁ := by
        simp only [hGf, e0, hw₁]
        ring
      have hGe₂ : G' (r, y) = w₂ ^ 3 - ĉ * w₂ := by
        simp only [hG', e, hGf, e0, hw₂, hpsi]
        ring
      have hm := abs_cubic_sub_le (c := ĉ) hA₁ hA₂
      have hsq : (A * r ^ ((η : ℝ) / 2)) ^ 2 = A ^ 2 * r ^ (η : ℝ) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast (r ^ ((η : ℝ) / 2)) 2, ← Real.rpow_mul hr.1.le]
        congr 1; push_cast; ring
      have hdw : w₂ - w₁ = d r y := by simp only [hd, hw₁, hw₂]; ring
      have h3 := hgb r hr y
      rw [hGe₁, hGe₂, abs_sub_comm]
      calc |(w₂ ^ 3 - ĉ * w₂) - (w₁ ^ 3 - ĉ * w₁)| ≤
          (3 * (A * r ^ ((η : ℝ) / 2)) ^ 2 + |ĉ|) * |w₂ - w₁| := hm
        _ = (3 * A ^ 2 * r ^ (η : ℝ) + |ĉ|) * |d r y| := by rw [hsq, hdw]; ring
        _ ≤ g r := h3
    exact abs_heatPotential_le hg0 hgm ht.1 ht.2 hgi (fun y => Gf y - G' y) hdiffb x

end RegularityStructures.Phi43

end
