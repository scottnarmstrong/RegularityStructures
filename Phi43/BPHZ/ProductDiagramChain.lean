/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductDiagramSum
public import Phi43.BPHZ.TreeI3PsiPowers

/-!
# The two-variable chain integral with a singular link

`productChain_bound`: let `F(w, v)` be dominated by
`Λ 1_{|w₁ - τ| ≤ T}(w) (∑ᵢ wᵢ s(cᵢ - w)^(-α)) (∑ⱼ w'ⱼ s(dⱼ - v)^(-β)) s(w - v)^(-γ)` with
`β + γ > 5` and `α + (β + γ - 5) < 5`.  Then `F` is integrable on `SpaceTime × SpaceTime` and
`|∫∫ F| ≤ C Λ (total weights) (1 + T)` with `C` depending only on `α, β, γ` (not on the centres).
The inner `v`-integral is the convolution estimate `integrable_and_integral_singularPow_mul_le`;
the outer integral is a slab integral of two weighted sums of total order `< 5`.  This is the engine
for all the product diagrams (the exponents are those of the gain kernel `3 + θ`, possibly merged
with one or two propagators).
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Almost everywhere in `w`, all centres of a weighted list are at positive distance. -/
theorem ae_forall_mem_torusParabolicSize_sub_pos (ps : List (ℝ × SpaceTime)) :
    ∀ᵐ w : SpaceTime ∂volume, ∀ p ∈ ps, 0 < torusParabolicSize (p.2 - w) := by
  induction ps with
  | nil => exact Filter.Eventually.of_forall fun w p hp => by simp at hp
  | cons p ps ih =>
    filter_upwards [ae_torusParabolicSize_sub_pos p.2, ih] with w h1 h2 q hq
    rcases List.mem_cons.1 hq with rfl | h
    · exact h1
    · exact h2 q h

/-- The inner integral: a weighted sum of powers against a power centred at `w`. -/
theorem singularIntLe_inner_spSum {β γ : ℝ} (hβ : 0 < β) (hβ5 : β < 5) (hγ : 0 < γ)
    (hγ5 : γ < 5) (hβγ : 5 < β + γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {qs : List (ℝ × SpaceTime)}, SpNonneg qs → ∀ w : SpaceTime,
      (∀ p ∈ qs, 0 < torusParabolicSize (p.2 - w)) →
      SingularIntLe (fun v => spSum β qs v * singularPow γ w v)
        (C * spSum (β + γ - 5) qs w) := by
  obtain ⟨C, hC, h⟩ := integrable_and_integral_singularPow_mul_le hβ hβ5 hγ hγ5 hβγ
  refine ⟨C, hC, fun {qs} hqs w hpos => ?_⟩
  induction qs with
  | nil => simpa using singularIntLe_zero
  | cons q qs ih =>
    have h1 := h q.2 w (hpos q List.mem_cons_self)
    have h1' : SingularIntLe (fun v => singularPow β q.2 v * singularPow γ w v)
      (C * torusParabolicSize (q.2 - w) ^ (5 - β - γ)) := ⟨h1.1, h1.2⟩
    have h2 := (h1'.const_mul hqs.head).add
      (ih hqs.tail (fun p hp => hpos p (List.mem_cons_of_mem _ hp)))
    refine (h2.mono_right (le_of_eq ?_)).congr_fun (fun v => ?_)
    · rw [spSum_cons]
      simp only [singularPow, show -(β + γ - 5) = 5 - β - γ by ring]
      ring
    · rw [spSum_cons]
      ring

/-- **The chain integral.** -/
theorem productChain_bound {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hβ5 : β < 5)
    (hγ5 : γ < 5) (hβγ : 5 < β + γ) (hout : α + (β + γ - 5) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : SpaceTime → SpaceTime → ℝ} {Λ T : ℝ} (τ : ℝ)
      {ps qs : List (ℝ × SpaceTime)}, 0 ≤ Λ → 0 ≤ T → SpNonneg ps → SpNonneg qs →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
        Λ * Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T} (spSum α ps) w *
          (spSum β qs v * singularPow γ w v)) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * Λ * (spWeight ps * spWeight qs) * (1 + T) := by
  obtain ⟨Cin, hCin, hin⟩ := singularIntLe_inner_spSum hβ hβ5 hγ hγ5 hβγ
  have hδ : 0 < β + γ - 5 := by linarith
  refine ⟨Cin * (2 * (80 / (5 - (α + (β + γ - 5))) + 2)), by positivity, ?_⟩
  intro F Λ T τ ps qs hΛ hT hps hqs hmeas hFG
  set S : Set SpaceTime := {w : SpaceTime | |w.1 - τ| ≤ T} with hS
  set m : SpaceTime → ℝ := Set.indicator S (spSum α ps) with hm
  have hm0 : ∀ w, 0 ≤ m w := fun w =>
    Set.indicator_nonneg (fun w _ => spSum_nonneg hps w) w
  have hmm : Measurable m := (measurable_spSum α ps).indicator (measurableSet_abs_fst_sub_le τ T)
  have hout' := singularIntLe_slabAt_spSum_mul_spSum τ hα hδ hout hT hps hqs
  set H : SpaceTime → ℝ := fun w => Λ * Cin *
    Set.indicator S (fun w => spSum α ps w * spSum (β + γ - 5) qs w) w with hH
  have hHle : SingularIntLe H (Λ * Cin * (spWeight ps * spWeight qs *
      (2 * (80 / (5 - (α + (β + γ - 5))) + 2 * T)))) := by
    have := hout'.const_mul (mul_nonneg hΛ hCin)
    exact this
  have hG : ∀ᵐ w : SpaceTime ∂volume, Integrable (fun v =>
      Λ * m w * (spSum β qs v * singularPow γ w v)) := by
    filter_upwards [ae_forall_mem_torusParabolicSize_sub_pos qs] with w hw
    exact (hin hqs w hw).1.const_mul _
  have hGH : ∀ᵐ w : SpaceTime ∂volume, ∫ v, Λ * m w * (spSum β qs v * singularPow γ w v) ≤
      H w := by
    filter_upwards [ae_forall_mem_torusParabolicSize_sub_pos qs] with w hw
    have := (hin hqs w hw).2
    rw [integral_const_mul]
    have hnn : 0 ≤ Λ * m w := mul_nonneg hΛ (hm0 w)
    have h2 := mul_le_mul_of_nonneg_left this hnn
    refine h2.trans (le_of_eq ?_)
    by_cases hw' : w ∈ S
    · simp only [hH, hm, Set.indicator_of_mem hw']
      ring
    · simp only [hH, hm, Set.indicator_of_notMem hw']
      ring
  have hFG' : ∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume,
      |F w v| ≤ Λ * m w * (spSum β qs v * singularPow γ w v) := hFG
  obtain ⟨hint, hbd⟩ := integrable_prod_of_two_level (F := F) hmeas hG hGH hHle.1 hFG'
  refine ⟨hint, hbd.trans (hHle.2.trans ?_)⟩
  have hw0 : 0 ≤ spWeight ps * spWeight qs := mul_nonneg (spWeight_nonneg hps) (spWeight_nonneg hqs)
  have hX : 2 * (80 / (5 - (α + (β + γ - 5))) + 2 * T) ≤
      2 * (80 / (5 - (α + (β + γ - 5))) + 2) * (1 + T) := by
    have h80 : 0 ≤ 80 / (5 - (α + (β + γ - 5))) :=
      div_nonneg (by norm_num) (by linarith)
    nlinarith
  calc Λ * Cin * (spWeight ps * spWeight qs *
        (2 * (80 / (5 - (α + (β + γ - 5))) + 2 * T)))
      ≤ Λ * Cin * (spWeight ps * spWeight qs *
        (2 * (80 / (5 - (α + (β + γ - 5))) + 2) * (1 + T))) := by
        gcongr
    _ = _ := by ring

end RegularityStructures

end
