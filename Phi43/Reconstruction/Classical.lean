/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MildIdentification
public import Phi43.ClassicalSolution.Uniqueness

/-!
# Mild solutions started at a positive time are the classical solution

The last step of the identification of the reconstructed solution with the classical one, in
restart form.  If `u` is a classical solution of
`∂_t u = Δu - u³ + c u + f` and `s > 0`, then `t ↦ u (s + t)` is a classical solution with forcing
`f(s + ·)` and datum `u s` (`isClassicalSolution_shift`), the datum `u s` is smooth
(`isSmoothOnTorus_of_classical`), and every continuous path `W` on `[0, T]` with `W 0 = u s`
satisfying the mild equation for the forcing `f(s + ·)` equals `u (s + ·)` on `[0, T]`
(`mild_path_eq_classical`).
-/

public section

open Set Filter Topology RegularityStructures.PDE
open scoped ContDiff

namespace RegularityStructures.Phi43

/-- The time shifted forcing `f(s + ·)`. -/
@[expose] def shiftForcing (s : ℝ) (f : SpaceTime → ℝ) : SpaceTime → ℝ :=
  fun p => f (p.1 + s, p.2)

theorem isSmoothOnSpaceTime_shiftForcing {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f) (s : ℝ) :
    IsSmoothOnSpaceTime (shiftForcing s f) := by
  unfold IsSmoothOnSpaceTime shiftForcing at *
  exact hf.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

theorem isClassicalSolution_shift {c : ℝ} {f : SpaceTime → ℝ} {u₀ : C(Torus3, ℝ)}
    {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u) {s : ℝ} (hs : 0 ≤ s) :
    IsClassicalSolution c (shiftForcing s f) (u s) (fun t => u (s + t)) where
  continuousOn := by
    refine ContinuousOn.comp (g := fun z : ℝ × Torus3 => u z.1 z.2) (f := fun z : ℝ × Torus3 =>
      (s + z.1, z.2)) hu.continuousOn
      ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn ?_
    intro z hz
    exact ⟨by simpa using add_nonneg hs hz.1, mem_univ _⟩
  initial := by simp
  contDiffOn := by
    refine ContDiffOn.comp (g := fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (f := fun p : ℝ × (Fin 3 → ℝ) => (s + p.1, p.2)) hu.contDiffOn
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn ?_
    intro p hp
    exact ⟨by simpa using add_pos_of_nonneg_of_pos hs hp.1, mem_univ _⟩
  equation t ht y := by
    have h1 := hu.equation (s + t) (add_pos_of_nonneg_of_pos hs ht) y
    have e : deriv (fun r => u (s + r) (torusProj y)) t =
        deriv (fun r => u r (torusProj y)) (s + t) := by
      exact deriv_comp_const_add s t (f := fun r => u r (torusProj y))
    rw [e, h1]
    simp [shiftForcing, add_comm]

theorem isSmoothOnTorus_of_classical {c : ℝ} {f : SpaceTime → ℝ} {u₀ : C(Torus3, ℝ)}
    {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u) {s : ℝ} (hs : 0 < s) :
    IsSmoothOnTorus (u s) := by
  unfold IsSmoothOnTorus
  have h : ContDiffOn ℝ ∞ (fun y : Fin 3 → ℝ => u s (torusProj y)) univ := by
    refine ContDiffOn.comp (g := fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2))
      (f := fun y : Fin 3 → ℝ => (s, y)) hu.contDiffOn
      (contDiff_const.prodMk contDiff_id).contDiffOn ?_
    intro y _
    exact ⟨hs, mem_univ _⟩
  exact contDiffOn_univ.1 h
/-- **A continuous mild path started at `u s` is the classical solution.** -/
theorem mild_path_eq_classical {c : ℝ} {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u) {s : ℝ}
    (hs : 0 < s) {T : ℝ} (hT : 0 ≤ T) (W : ℝ → C(Torus3, ℝ)) (hW : Continuous W)
    (hW0 : W 0 = u s)
    (hmild : ∀ t ∈ Ioc 0 T, W t = heatOp t (u s) + duhamel (fun r =>
      nemytskii (cubicHeatNonlinearity c (isSmoothOnSpaceTime_shiftForcing hf s)) r (W r)) t) :
    ∀ t ∈ Icc 0 T, W t = u (s + t) := by
  have hfs := isSmoothOnSpaceTime_shiftForcing hf s
  have hm : IsMildSolution (cubicHeatNonlinearity c hfs) (u s) T W := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      simp [hW0, duhamel_zero, heatOp_zero_left]
    · exact hmild t ⟨h0, ht.2⟩
  have hcont : ContinuousOn (fun z : SpaceTime => W z.1 z.2) (Icc 0 T ×ˢ univ) :=
    (continuous_eval.comp (hW.comp continuous_fst |>.prodMk continuous_snd)).continuousOn
  obtain ⟨v, hv, hWv⟩ := cubic_mildSolution_eq_classical c hfs
    (isSmoothOnTorus_of_classical hu hs) hT hcont hm
  have hu' := isClassicalSolution_shift hu hs.le
  intro t ht
  rw [hWv t ht]
  exact classicalSolution_unique c hv hu' t ht.1

end RegularityStructures.Phi43

end
