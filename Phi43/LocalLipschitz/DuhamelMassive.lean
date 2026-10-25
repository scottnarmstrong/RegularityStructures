/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.LocalLipschitz.DuhamelTriangle
public import RegularityStructures.PDE.Duhamel
public import RegularityStructures.PDE.Semigroup
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Duhamel integral versus the massive Duhamel integral

For a continuous path `F`, put `Dm(r) = ∫₀ʳ e^{-(r-q)} P_{r-q} F(q) dq`.  Then
`∫₀ᵗ P_{t-q} F(q) dq = Dm(t) + ∫₀ᵗ P_{t-r} Dm(r) dr`
(`duhamel_eq_massiveDuhamel_add`).  The proof is the semigroup property and Fubini on the triangle.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43.LocalLipschitz

open RegularityStructures

/-- The massive Duhamel integral `∫₀ʳ e^{-(r-q)} P_{r-q} F(q) dq`. -/
@[expose] noncomputable def massiveDuhamel (F : ℝ → C(Torus3, ℝ)) (r : ℝ) : C(Torus3, ℝ) :=
  ∫ q in (0 : ℝ)..r, Real.exp (-(r - q)) • PDE.heatOp (r - q) (F q)

theorem continuous_massiveDuhamel_integrand {F : ℝ → C(Torus3, ℝ)} (hF : Continuous F) :
    Continuous fun p : ℝ × ℝ => Real.exp (-(p.1 - p.2)) • PDE.heatOp (p.1 - p.2) (F p.2) :=
  (Real.continuous_exp.comp (continuous_fst.sub continuous_snd).neg).smul
    (PDE.continuous_duhamel_integrand hF)

theorem continuous_massiveDuhamel {F : ℝ → C(Torus3, ℝ)} (hF : Continuous F) :
    Continuous (massiveDuhamel F) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun r q => Real.exp (-(r - q)) • PDE.heatOp (r - q) (F q))
    (continuous_massiveDuhamel_integrand hF) continuous_id

private theorem integral_exp_neg_sub (q t : ℝ) :
    ∫ r in q..t, Real.exp (-(r - q)) = 1 - Real.exp (-(t - q)) := by
  have : ∀ r ∈ uIcc q t, HasDerivAt (fun r : ℝ => -Real.exp (-(r - q))) (Real.exp (-(r - q))) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -(r - q)) (-1) r :=
      ((hasDerivAt_id r).sub_const q).neg
    exact (h1.exp.neg).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    (by exact (Real.continuous_exp.comp (continuous_id.sub continuous_const).neg).intervalIntegrable _ _)]
  simp
  ring

/-- **Duhamel = massive Duhamel + Duhamel of the massive Duhamel.** -/
theorem duhamel_eq_massiveDuhamel_add {F : ℝ → C(Torus3, ℝ)} (hF : Continuous F) {t : ℝ}
    (ht : 0 ≤ t) :
    PDE.duhamel F t = massiveDuhamel F t + PDE.duhamel (massiveDuhamel F) t := by
  set X : ℝ → C(Torus3, ℝ) := fun q => PDE.heatOp (t - q) (F q) with hX
  have hXc : Continuous X := PDE.intervalIntegrable_duhamel_integrand hF t 0 0 |> fun _ =>
    (continuous_const.sub continuous_id).heatOp hF
  have hG := continuous_massiveDuhamel_integrand hF
  -- inner identity
  have hinner : ∀ r ∈ Icc (0 : ℝ) t, PDE.heatOp (t - r) (massiveDuhamel F r) =
      ∫ q in (0 : ℝ)..r, Real.exp (-(r - q)) • X q := by
    intro r hr
    have hint : IntervalIntegrable (fun q => Real.exp (-(r - q)) • PDE.heatOp (r - q) (F q))
        MeasureTheory.volume 0 r :=
      (hG.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable 0 r
    have := (PDE.heatOpCLM (E := ℝ) (t - r)).intervalIntegral_comp_comm hint
    simp only [PDE.heatOpCLM_apply] at this
    unfold massiveDuhamel
    rw [← this]
    refine intervalIntegral.integral_congr fun q hq => ?_
    rw [uIcc_of_le hr.1] at hq
    simp only [hX]
    rw [PDE.heatOp_smul, PDE.heatOp_heatOp (sub_nonneg.2 hq.2) (sub_nonneg.2 hr.2)]
    rw [show r - q + (t - r) = t - q by ring]
  have hK : Continuous (Function.uncurry fun r q : ℝ => Real.exp (-(r - q)) • X q) :=
    (Real.continuous_exp.comp (continuous_fst.sub continuous_snd).neg).smul (hXc.comp continuous_snd)
  have hswap := intervalIntegral_triangle_swap hK ht
  have h2 : PDE.duhamel (massiveDuhamel F) t =
      ∫ q in (0 : ℝ)..t, (1 - Real.exp (-(t - q))) • X q := by
    unfold PDE.duhamel
    rw [intervalIntegral.integral_congr (g := fun r => ∫ q in (0 : ℝ)..r,
      Real.exp (-(r - q)) • X q) (fun r hr => by
        rw [uIcc_of_le ht] at hr; exact hinner r hr), hswap]
    refine intervalIntegral.integral_congr fun q _ => ?_
    rw [intervalIntegral.integral_smul_const, integral_exp_neg_sub]
  have hE : Continuous fun q : ℝ => Real.exp (-(t - q)) • X q :=
    (Real.continuous_exp.comp (continuous_const.sub continuous_id).neg).smul hXc
  have h3 : ∫ q in (0 : ℝ)..t, (1 - Real.exp (-(t - q))) • X q =
      (∫ q in (0 : ℝ)..t, X q) - ∫ q in (0 : ℝ)..t, Real.exp (-(t - q)) • X q := by
    simp_rw [sub_smul, one_smul]
    exact intervalIntegral.integral_sub (hXc.intervalIntegrable 0 t) (hE.intervalIntegrable 0 t)
  have e1 : PDE.duhamel F t = ∫ q in (0 : ℝ)..t, X q := rfl
  have e2 : massiveDuhamel F t = ∫ q in (0 : ℝ)..t, Real.exp (-(t - q)) • X q := rfl
  rw [h2, h3, e1, e2]
  abel

end RegularityStructures.Phi43.LocalLipschitz

end
