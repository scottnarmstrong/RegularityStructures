/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.ChaosLimitMomentsRiemann
public import RegularityStructures.BPHZ.ChaosLimitMomentsField
public import RegularityStructures.BPHZ.ChaosLimitMomentsCauchySchwarz

/-!
# Uniform second moment of the sampled tested fields

For finitely-valued measurable sampling maps `π`, `E (chaosIntegral … π)²` is bounded by a constant
independent of `π` (`exists_integral_chaosIntegral_sq_le`). The proof applies the weighted
Cauchy-Schwarz bound `integral_sq_integral_mul_le` to the inner integral and then to the outer
integral, with the uniform moment bounds of `ChaosLimitMomentsField`.
-/

public section

open MeasureTheory

namespace RegularityStructures

universe u

private lemma exists_abs_comp_le {π : SpaceTime → SpaceTime} (hfin : (Set.range π).Finite)
    (f : SpaceTime → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f (π x)| ≤ C := by
  obtain ⟨C, hC⟩ := (hfin.image fun b => |f b|).bddAbove
  exact ⟨max C 0, le_max_right _ _, fun x =>
    (hC ⟨π x, ⟨x, rfl⟩, rfl⟩).trans (le_max_left _ _)⟩

/-- The inner integral is bounded by `L C` when the sampled polynomial values are bounded by `C`. -/
theorem abs_chaosInner_le {Ω : Type*} {ψ : Ω → SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ}
    {L : ℝ} (hki : ∀ y, Integrable (k y)) (hL : ∀ y, ∫ w, |k y w| ≤ L) {Q : Polynomial ℝ}
    {π : SpaceTime → SpaceTime} {ω : Ω} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w, |Q.eval (ψ ω (π w))| ≤ C) (y : SpaceTime) :
    |chaosInner ψ k Q π ω y| ≤ L * C := by
  have h1 : ‖chaosInner ψ k Q π ω y‖ ≤ ∫ w, |k y w| * C := by
    refine norm_integral_le_of_norm_le ((hki y).abs.mul_const C)
      (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC w) (abs_nonneg _)
  rw [integral_mul_const] at h1
  exact (Real.norm_eq_abs _ ▸ h1).trans (mul_le_mul_of_nonneg_right (hL y) hC0)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ψ : Ω → SpaceTime → ℝ}

/-- **Second moments of the sampled tested fields, uniform in the sampling map.** -/
theorem exists_integral_chaosIntegral_sq_le (hW : IsWhiteNoise P W)
    (hψW : ∀ y, ∃ h : SpaceTime → ℝ, MemLp h 2 ∧ (fun ω => ψ ω y) =ᵐ[P] W h) {V : ℝ}
    (hV : ∀ y, ∫ ω, ψ ω y ^ 2 ∂P ≤ V) (hψm : ∀ y, Measurable fun ω => ψ ω y)
    (hψj : Measurable fun q : Ω × SpaceTime => ψ q.1 q.2)
    {g : SpaceTime → ℝ} {k : SpaceTime → SpaceTime → ℝ} {L : ℝ} (hgm : Measurable g)
    (hgi : Integrable g) (hkm : Measurable (Function.uncurry k)) (hki : ∀ y, Integrable (k y))
    (hL : ∀ y, ∫ w, |k y w| ≤ L) (P₁ P₂ P₃ : Polynomial ℝ) :
    ∃ B : ℝ, ∀ {π : SpaceTime → SpaceTime}, Measurable π → (Set.range π).Finite →
      ∫ ω, chaosIntegral ψ k P₁ P₂ P₃ g π ω ^ 2 ∂P ≤ B := by
  have := hW.isProbabilityMeasure
  obtain ⟨M₁₂, hM₁₂0, hM₁₂⟩ := exists_integral_polyField_sq_mul_sq_le hW hψW hV hψm P₁ P₂
  obtain ⟨M₃, hM₃0, hM₃'⟩ :=
    exists_integral_polyField_sq_mul_sq_le hW hψW hV hψm P₃ (Polynomial.C 1)
  have hM₃ : ∀ v, Integrable (fun ω => (P₃.eval (ψ ω v)) ^ 2) P ∧
      ∫ ω, (P₃.eval (ψ ω v)) ^ 2 ∂P ≤ M₃ := fun v => by simpa using hM₃' v v
  have hL0 : 0 ≤ L := (integral_nonneg fun w => abs_nonneg _).trans (hL 0)
  set MH : ℝ := 2 * (L * (L * M₁₂) + M₃) with hMH
  have hMH0 : 0 ≤ MH := by positivity
  refine ⟨(∫ y, |g y|) * ((∫ y, |g y|) * MH), fun {π} hπ hfin => ?_⟩
  set T := hfin.toFinset with hTdef
  have hT : ∀ x, π x ∈ T := fun x => hfin.mem_toFinset.2 ⟨x, rfl⟩
  have hk_y : ∀ y, Measurable (k y) := fun y => hkm.comp (measurable_const.prodMk measurable_id)
  have hjoint : ∀ Q : Polynomial ℝ,
      Measurable (fun r : Ω × SpaceTime => Q.eval (ψ r.1 (π r.2))) := fun Q =>
    Q.continuous.measurable.comp (hψj.comp (measurable_fst.prodMk (hπ.comp measurable_snd)))
  have hfix : ∀ (Q : Polynomial ℝ) (v : SpaceTime),
      Measurable (fun r : Ω × SpaceTime => Q.eval (ψ r.1 v)) := fun Q v =>
    Q.continuous.measurable.comp ((hψm v).comp measurable_fst)
  have hA : ∀ y, Integrable (fun ω => (chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y))) ^ 2) P ∧
      ∫ ω, (chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y))) ^ 2 ∂P ≤ L * (L * M₁₂) := by
    intro y
    have key := integral_sq_integral_mul_le (P := P) (ν := volume) (k := k y) (hk_y y) (hki y)
      (hL y) hM₁₂0 (H := fun ω w => P₁.eval (ψ ω (π w)) * P₂.eval (ψ ω (π y)))
      ((hjoint P₁).mul (hfix P₂ (π y)))
      (fun ω => integrable_mul_comp hπ T hT (hki y).abs
        (fun u => (P₁.eval (ψ ω u) * P₂.eval (ψ ω (π y))) ^ 2))
      (fun w => by simpa only [mul_pow] using (hM₁₂ (π w) (π y)).1)
      (fun w => by simpa only [mul_pow] using (hM₁₂ (π w) (π y)).2)
    have e : ∀ ω, ∫ w, k y w * (P₁.eval (ψ ω (π w)) * P₂.eval (ψ ω (π y))) =
        chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y)) := fun ω => by
      unfold chaosInner
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
    simp only [e] at key
    exact key
  set Hn : Ω → SpaceTime → ℝ := fun ω y =>
    chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y)) + P₃.eval (ψ ω (π y)) with hHn
  have hinner_m : Measurable (fun r : Ω × SpaceTime => chaosInner ψ k P₁ π r.1 r.2) := by
    have hf : Measurable (fun r : (Ω × SpaceTime) × SpaceTime =>
        k r.1.2 r.2 * P₁.eval (ψ r.1.1 (π r.2))) :=
      (hkm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (P₁.continuous.measurable.comp (hψj.comp (measurable_fst.fst.prodMk
          (hπ.comp measurable_snd))))
    exact hf.stronglyMeasurable.integral_prod_right'.measurable
  have hHn_m : Measurable (Function.uncurry Hn) :=
    (hinner_m.mul (hjoint P₂)).add (hjoint P₃)
  have hHb : ∀ ω, Integrable (fun y => |g y| * Hn ω y ^ 2) := by
    intro ω
    obtain ⟨C₁, hC₁0, hC₁⟩ := exists_abs_comp_le hfin (fun u => P₁.eval (ψ ω u))
    obtain ⟨C₂, hC₂0, hC₂⟩ := exists_abs_comp_le hfin (fun u => P₂.eval (ψ ω u))
    obtain ⟨C₃, hC₃0, hC₃⟩ := exists_abs_comp_le hfin (fun u => P₃.eval (ψ ω u))
    have hbd : ∀ y, |Hn ω y| ≤ L * C₁ * C₂ + C₃ := fun y => by
      refine (abs_add_le _ _).trans (add_le_add ?_ (hC₃ y))
      rw [abs_mul]
      exact mul_le_mul (abs_chaosInner_le hki hL hC₁0 hC₁ y) (hC₂ y) (abs_nonneg _)
        (by positivity)
    refine Integrable.mono' (hgi.abs.mul_const ((L * C₁ * C₂ + C₃) ^ 2)) ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_abs.measurable.comp hgm).mul
        ((hHn_m.comp (measurable_const.prodMk measurable_id)).pow_const 2)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := pow_le_pow_left₀ (abs_nonneg _) (hbd y) 2
      rwa [sq_abs] at this
  have hsq : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have hHi : ∀ y, Integrable (fun ω => Hn ω y ^ 2) P := fun y =>
    Integrable.mono' (((hA y).1.const_mul 2).add ((hM₃ (π y)).1.const_mul 2))
      ((hHn_m.comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsq _ _)
  have hM : ∀ y, ∫ ω, Hn ω y ^ 2 ∂P ≤ MH := fun y => by
    calc ∫ ω, Hn ω y ^ 2 ∂P ≤ ∫ ω, (2 * (chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y))) ^ 2 +
          2 * (P₃.eval (ψ ω (π y))) ^ 2) ∂P :=
        integral_mono (hHi y) (((hA y).1.const_mul 2).add ((hM₃ (π y)).1.const_mul 2))
          fun ω => hsq _ _
      _ = 2 * ∫ ω, (chaosInner ψ k P₁ π ω y * P₂.eval (ψ ω (π y))) ^ 2 ∂P +
          2 * ∫ ω, (P₃.eval (ψ ω (π y))) ^ 2 ∂P := by
        rw [integral_add ((hA y).1.const_mul 2) ((hM₃ (π y)).1.const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ MH := by
        have := (hA y).2
        have := (hM₃ (π y)).2
        rw [hMH]
        linarith
  have key := integral_sq_integral_mul_le (P := P) (ν := volume) (k := g) hgm hgi
    (le_refl (∫ y, |g y|)) hMH0 (H := Hn) hHn_m hHb hHi hM
  have e : ∀ ω, chaosIntegral ψ k P₁ P₂ P₃ g π ω = ∫ y, g y * Hn ω y := fun ω => by
    unfold chaosIntegral chaosIntegrand
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  simp_rw [e]
  exact key.2

end RegularityStructures

end
