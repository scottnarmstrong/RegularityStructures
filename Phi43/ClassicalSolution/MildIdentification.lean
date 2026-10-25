/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.MildUniqueness
public import Phi43.ClassicalSolution.WellPosed

/-!
# A finite-window mild solution is the classical solution

A continuous mild solution of the renormalised equation (3.1) of the statement on a finite time
window coincides there with the classical solution of Definition 2.6. The cubic
jet-system bootstrap supplies smoothness and the PDE; the finite-window maximum principle
gives equality on the interior, and continuity includes the terminal time. Global existence
and uniqueness of the classical solution come from item (W4) of Lemma 4.1 of the statement; they
are not hypotheses about the mild path.

Source: [Hai14, Proposition 9.10]. The extra bootstrap is needed because Definition 2.6 of the
statement asks for smooth solutions.
-/

public noncomputable section

open Set Filter Topology

namespace RegularityStructures.Phi43

theorem cubic_mildSolution_eq_classical
    (c : ℝ) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (hu₀ : IsSmoothOnTorus u₀) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → C(Torus3, ℝ)}
    (hu : ContinuousOn (fun z : SpaceTime => u z.1 z.2) (Icc 0 T ×ˢ univ))
    (hmild : PDE.IsMildSolution (cubicHeatNonlinearity c hf) u₀ T u) :
    ∃ v : ℝ → C(Torus3, ℝ), IsClassicalSolution c f u₀ v ∧
      ∀ t ∈ Icc 0 T, u t = v t := by
  obtain ⟨v, hv⟩ := classicalSolution_exists c hf hu₀
  obtain ⟨hinit, hsm, heq⟩ := cubic_mildSolution_smooth_and_equation c hf hu₀ hT hu hmild
  refine ⟨v, hv, ?_⟩
  have hvc : ContinuousOn (fun z : SpaceTime => v z.1 z.2) (Icc 0 T ×ˢ univ) :=
    hv.continuousOn.mono fun z hz => ⟨hz.1.1, hz.2⟩
  have hvs := hv.contDiffOn.mono
    (show Ioo (0 : ℝ) T ×ˢ (univ : Set (Fin 3 → ℝ)) ⊆ Ioi 0 ×ˢ univ from
      fun z hz => ⟨hz.1.1, hz.2⟩)
  by_cases hT0 : T = 0
  · subst T
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [ht0, hinit, hv.initial]
  have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
  have hinterior : EqOn u v (Ico 0 T) := by
    intro t ht
    have hb := finiteWindow_cubic_classical_sup_stability c hu hvc hinit hv.initial
      hsm hvs heq (fun s hs => hv.equation s hs.1) ht.1 ht.2 0 le_rfl
      (fun _ _ _ => by simp only [sub_self, abs_zero, le_refl]) t ⟨ht.1, le_rfl⟩
    apply sub_eq_zero.mp
    apply norm_le_zero_iff.mp
    simpa only [zero_mul] using hb
  apply hinterior.of_subset_closure
    (ContinuousMap.continuousOn_of_continuousOn_uncurry u hu)
    (ContinuousMap.continuousOn_of_continuousOn_uncurry v hvc) Ico_subset_Icc_self
  rw [closure_Ico hTpos.ne]

end RegularityStructures.Phi43

end
