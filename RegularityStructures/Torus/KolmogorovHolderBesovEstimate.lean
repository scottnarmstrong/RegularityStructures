/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovAnnealed
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Endpoint estimates for the dyadic Kolmogorov argument

The endpoint estimate makes the two analytic inputs explicit: the heat `Lᵖ` smoothing bound and
the annealed pointwise heat estimate.  The conversion between Bochner integrals and lintegrals is
kept in this module so that the final random-field theorem does not conceal an integrability
assumption.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

open PDE

private theorem dyadicScale_add (m n : ℕ) :
    dyadicScale (m + n) = dyadicScale m * dyadicScale n := by
  unfold dyadicScale
  rw [pow_add]
  field_simp

private theorem dyadicScale_eq_rpow_neg (n : ℕ) :
    dyadicScale n = (2 : ℝ) ^ (-(n : ℝ)) := by
  unfold dyadicScale
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp [one_div]

theorem dyadicHeatPower_eq_geometric {p : ℕ} {α η : ℝ} (n : ℕ) :
    (dyadicScale n) ^ (-η * p / 2) *
        (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          (dyadicScale (n + 2)) ^ (α * p / 2)) =
      heatKernelScaleConstant * (dyadicScale 2) ^ ((α * p - 3) / 2) *
        ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by
  have hn : 0 < dyadicScale n := dyadicScale_pos n
  have h2 : 0 < dyadicScale 2 := dyadicScale_pos 2
  have hscale : dyadicScale (n + 2) = dyadicScale n * dyadicScale 2 :=
    dyadicScale_add n 2
  have hncombine :
      (dyadicScale n) ^ (-η * ↑p / 2) *
          (dyadicScale n) ^ (-(3 : ℝ) / 2) *
          (dyadicScale n) ^ (α * ↑p / 2) =
        (dyadicScale n) ^ (-η * ↑p / 2 + (-(3 : ℝ) / 2) + α * ↑p / 2) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
  have h2combine :
      (dyadicScale 2) ^ (-(3 : ℝ) / 2) *
          (dyadicScale 2) ^ (α * ↑p / 2) =
        (dyadicScale 2) ^ (-(3 : ℝ) / 2 + α * ↑p / 2) := by
    rw [← Real.rpow_add h2]
  have hgeom :
      (dyadicScale n) ^ ((p * (α - η) - 3) / 2) =
        ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by
    rw [dyadicScale_eq_rpow_neg]
    rw [← Real.rpow_natCast]
    have hpow := Real.rpow_mul (x := (2 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 2)
      (-(p * (α - η) - 3) / 2) (n : ℝ)
    calc
      ((2 : ℝ) ^ (-(n : ℝ))) ^ ((p * (α - η) - 3) / 2) =
          (2 : ℝ) ^ (-(n : ℝ) * ((p * (α - η) - 3) / 2)) := by
        exact (Real.rpow_mul (x := (2 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 2) (-(n : ℝ))
          ((p * (α - η) - 3) / 2)).symm
      _ =
          (2 : ℝ) ^ (-(p * (α - η) - 3) / 2 * (n : ℝ)) := by
        congr 1
        ring
      _ = ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ (n : ℝ) := hpow
  rw [hscale, Real.mul_rpow hn.le h2.le, Real.mul_rpow hn.le h2.le]
  calc
    (dyadicScale n) ^ (-η * ↑p / 2) *
        (heatKernelScaleConstant *
          ((dyadicScale n) ^ (-(3 : ℝ) / 2) * (dyadicScale 2) ^ (-(3 : ℝ) / 2)) *
          ((dyadicScale n) ^ (α * ↑p / 2) * (dyadicScale 2) ^ (α * ↑p / 2))) =
        heatKernelScaleConstant *
          (((dyadicScale n) ^ (-η * ↑p / 2) *
            (dyadicScale n) ^ (-(3 : ℝ) / 2)) *
            (dyadicScale n) ^ (α * ↑p / 2)) *
          ((dyadicScale 2) ^ (-(3 : ℝ) / 2) *
            (dyadicScale 2) ^ (α * ↑p / 2)) := by ring
    _ = heatKernelScaleConstant *
          (dyadicScale n) ^ (-η * ↑p / 2 + (-(3 : ℝ) / 2) + α * ↑p / 2) *
          (dyadicScale 2) ^ (-(3 : ℝ) / 2 + α * ↑p / 2) := by
      rw [← hncombine, ← h2combine]
    _ = heatKernelScaleConstant * (dyadicScale 2) ^ ((α * ↑p - 3) / 2) *
          (dyadicScale n) ^ ((p * (α - η) - 3) / 2) := by
      have he : -η * ↑p / 2 + (-(3 : ℝ) / 2) + α * ↑p / 2 =
          (p * (α - η) - 3) / 2 := by ring
      have hf : -(3 : ℝ) / 2 + α * ↑p / 2 = (α * ↑p - 3) / 2 := by ring
      rw [he, hf]
      ring
    _ = heatKernelScaleConstant * (dyadicScale 2) ^ ((α * ↑p - 3) / 2) *
          ((2 : ℝ) ^ (-(p * (α - η) - 3) / 2)) ^ n := by
      rw [hgeom]

/- The geometric constant is written with the actual heat-kernel constant, so its dependence on
the exponent and the regularity gap is visible in the final moment theorem. -/
noncomputable def kolmogorovHolderBesovConstant (p : ℕ) (α η : ℝ) : ℝ :=
  heatKernelScaleConstant * (dyadicScale 2) ^ ((α * p - 3) / 2) *
    (1 - (2 : ℝ) ^ (-(p * (α - η) - 3) / 2))⁻¹

theorem kolmogorovHolderBesovConstant_nonneg {p : ℕ} {α η : ℝ}
    (hdecay : 3 < p * (α - η)) :
    0 ≤ kolmogorovHolderBesovConstant p α η := by
  have hδ : 0 < (p : ℝ) * (α - η) - 3 := by linarith
  have hq : 0 ≤ (2 : ℝ) ^ (-(p * (α - η) - 3) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hq_lt : (2 : ℝ) ^ (-(p * (α - η) - 3) / 2) < 1 := by
    apply (Real.rpow_lt_one_iff (by norm_num : (0 : ℝ) ≤ 2)).2
    exact Or.inr (Or.inl ⟨by norm_num, by linarith⟩)
  unfold kolmogorovHolderBesovConstant
  exact mul_nonneg
    (mul_nonneg heatKernelScaleConstant_nonneg
      (Real.rpow_nonneg (dyadicScale_pos 2).le _))
    (inv_nonneg.mpr (sub_nonneg.mpr hq_lt.le))

private theorem heatSemigroup_abs_natPow_integrable {r : ℝ} (hr : 0 < r)
    (g : C(Torus3, ℝ)) (p : ℕ) :
    Integrable (fun y : Torus3 => |heatSemigroup r g y| ^ p) := by
  have hc : Continuous (fun y : Torus3 => |heatSemigroup r g y| ^ p) := by
    rw [show (fun y : Torus3 => |heatSemigroup r g y| ^ p) =
        (fun y : Torus3 => |heatOp r g y| ^ p) by
      funext y
      rw [heatOp_eq_heatSemigroup hr]]
    exact ((heatOp r g).continuous.abs.pow p)
  exact (integrableOn_univ).mp
    (hc.continuousOn.integrableOn_compact isCompact_univ)

private theorem heatSemigroup_enorm_natPow_eq_ofReal_integral {r : ℝ} (hr : 0 < r)
    (g : C(Torus3, ℝ)) (p : ℕ) :
    ∫⁻ y : Torus3, ‖heatSemigroup r g y‖ₑ ^ p =
      ENNReal.ofReal (∫ y : Torus3, |heatSemigroup r g y| ^ p) := by
  calc
    ∫⁻ y : Torus3, ‖heatSemigroup r g y‖ₑ ^ p =
        ∫⁻ y : Torus3, ENNReal.ofReal (|heatSemigroup r g y| ^ p) := by
      apply lintegral_congr_ae
      filter_upwards [] with y
      rw [ENNReal.ofReal_pow (abs_nonneg _) p, ← ofReal_norm]
      rfl
    _ = ENNReal.ofReal (∫ y : Torus3, |heatSemigroup r g y| ^ p) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal
        (heatSemigroup_abs_natPow_integrable hr g p)
        (Filter.Eventually.of_forall fun y => by positivity)

private theorem dyadicHolderBesovTerm_pow_le {η : ℝ} {p : ℕ} {q : ℝ}
    (hpq : (p : ℝ).HolderConjugate q) (n : ℕ)
    (g : C(Torus3, ℝ)) :
    (dyadicHolderBesovTerm η n g) ^ p ≤
      ENNReal.ofReal ((dyadicScale n) ^ (-η * p / 2) *
        (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          ∫ y : Torus3, |heatSemigroup (dyadicScale (n + 2)) g y| ^ (p : ℝ))) := by
  have hnpos : 0 < dyadicScale n := dyadicScale_pos n
  have hrpos : 0 < dyadicScale (n + 1) := dyadicScale_pos (n + 1)
  have hrle : dyadicScale (n + 1) ≤ 1 := dyadicScale_le_one _
  have hrhalf : dyadicScale (n + 1) / 2 = dyadicScale (n + 2) := by
    simpa [Nat.add_assoc] using (dyadicScale_succ (n + 1)).symm
  have hsup :
      (⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) g x‖ₑ) =
        ‖heatOp (dyadicScale (n + 1)) g‖ₑ := by
    calc
      (⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) g x‖ₑ) =
          ⨆ x : Torus3, ‖heatOp (dyadicScale (n + 1)) g x‖ₑ := by
        apply iSup_congr
        intro x
        rw [heatOp_eq_heatSemigroup hrpos]
      _ = ‖heatOp (dyadicScale (n + 1)) g‖ₑ :=
        (ContinuousMap.enorm_eq_iSup_enorm _).symm
  have hnorm := heatSemigroup_norm_pow_le hpq hrpos hrle
    (g := g)
  have hnorm' :
      ‖heatOp (dyadicScale (n + 1)) g‖ ^ p ≤
        heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          ∫ y : Torus3,
            |heatSemigroup (dyadicScale (n + 2)) g y| ^ (p : ℝ) := by
    rw [hrhalf] at hnorm
    exact hnorm
  have hweight : 0 ≤ (dyadicScale n) ^ (-η / 2) := by
    exact Real.rpow_nonneg hnpos.le _
  have hweight_pow :
      ((dyadicScale n) ^ (-η / 2)) ^ p = (dyadicScale n) ^ (-η * p / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    ring
  have henorm :
      ‖heatOp (dyadicScale (n + 1)) g‖ₑ ^ p =
        ENNReal.ofReal (‖heatOp (dyadicScale (n + 1)) g‖ ^ p) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _) p, ofReal_norm]
  rw [dyadicHolderBesovTerm, mul_pow, ← ENNReal.ofReal_pow hweight p, hsup, henorm]
  rw [← ENNReal.ofReal_mul (pow_nonneg hweight p)]
  apply ENNReal.ofReal_le_ofReal
  rw [hweight_pow]
  exact mul_le_mul_of_nonneg_left hnorm'
    (Real.rpow_nonneg hnpos.le _)

theorem dyadicHolderBesovTerm_lintegral_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {X : Ω → C(Torus3, ℝ)} {η α A q : ℝ} {p : ℕ}
    (hpq : (p : ℝ).HolderConjugate q)
    (hjoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 →
      AEMeasurable
        (fun z : Ω × Torus3 =>
          ‖heatSemigroup r (X z.1) z.2‖ₑ ^ p) (P.prod volume))
    (hpoint : ∀ {r : ℝ}, 0 < r → r ≤ 1 → ∀ y : Torus3,
      ∫⁻ ω, ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2))) (n : ℕ) :
    ∫⁻ ω, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P ≤
      ENNReal.ofReal ((dyadicScale n) ^ (-η * p / 2) *
        (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2)))) := by
  let r : ℝ := dyadicScale (n + 2)
  let K : ℝ := (dyadicScale n) ^ (-η * p / 2) *
    (heatKernelScaleConstant * r ^ (-(3 : ℝ) / 2))
  let I : Ω → ℝ := fun ω =>
    ∫ y : Torus3, |heatSemigroup r (X ω) y| ^ (p : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    exact dyadicScale_pos _
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact dyadicScale_le_one _
  have hglobal :
      ∫⁻ ω, ∫⁻ y : Torus3,
          ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂volume ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) :=
    heatMoment_lintegral_swap_le (P := P) (X := X) (p := p) (r := r)
      (α := α) (A := A) (hjoint hr hr1) (hpoint hr hr1)
  have hglobal_real :
      ∫⁻ ω, ENNReal.ofReal (I ω) ∂P ≤
        ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (I ω) ∂P =
          ∫⁻ ω, ∫⁻ y : Torus3,
            ‖heatSemigroup r (X ω) y‖ₑ ^ p ∂volume ∂P := by
        apply lintegral_congr
        intro ω
        simpa [I] using
          (heatSemigroup_enorm_natPow_eq_ofReal_integral hr (X ω) p).symm
      _ ≤ ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) := hglobal
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (Real.rpow_nonneg (dyadicScale_pos n).le _)
      (mul_nonneg heatKernelScaleConstant_nonneg
        (Real.rpow_nonneg hr.le _))
  have hterm : ∀ ω : Ω,
      (dyadicHolderBesovTerm η n (X ω)) ^ p ≤ ENNReal.ofReal (K * I ω) := by
    intro ω
    simpa [I, K, r, mul_assoc] using
      (dyadicHolderBesovTerm_pow_le (η := η) hpq n (X ω))
  calc
    ∫⁻ ω, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P ≤
        ∫⁻ ω, ENNReal.ofReal (K * I ω) ∂P := lintegral_mono hterm
    _ = ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (I ω) ∂P := by
      apply lintegral_congr
      intro ω
      rw [ENNReal.ofReal_mul hK]
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (I ω) ∂P := by
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (A ^ p * r ^ (α * p / 2)) := by
      gcongr
    _ = ENNReal.ofReal (K * (A ^ p * r ^ (α * p / 2))) := by
      rw [ENNReal.ofReal_mul hK]
    _ = ENNReal.ofReal ((dyadicScale n) ^ (-η * p / 2) *
        (heatKernelScaleConstant * (dyadicScale (n + 2)) ^ (-(3 : ℝ) / 2) *
          (A ^ p * (dyadicScale (n + 2)) ^ (α * p / 2)))) := by
      congr 1
      dsimp [K, r]
      ring

end RegularityStructures

end
