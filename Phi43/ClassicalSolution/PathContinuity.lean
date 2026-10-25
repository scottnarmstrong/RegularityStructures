/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution
public import RegularityStructures.Torus.HolderBesov
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Continuity of classical-solution paths

This is the path-continuity half of item (W5) of Lemma 4.1 of the statement, for the classical
solutions of Definition 2.6. The proof uses uniform continuity on the compact torus
to turn continuity of the periodic space-time lift into continuity in the supremum norm;
the negative-order heat-semigroup seminorm is bounded by that norm.
-/

public section

open Set

namespace RegularityStructures.Phi43

/-- **(W5), path continuity.** Classical solutions are continuous paths into `𝒞^η`. -/
theorem classicalSolution_continuousOn (η : NegExponent) {c : ℝ} {f : SpaceTime → ℝ}
    {u₀ : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)} (hu : IsClassicalSolution c f u₀ u) :
    ContinuousOn (fun t => toHolderBesov η (u t)) (Ici 0) := by
  have h_u : ContinuousOn u (Ici 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let D : Type := Ici (0 : ℝ)
    let uD : D → C(Torus3, ℝ) := fun t => u t
    have hD : Continuous uD := by
      rw [continuous_iff_continuousAt]
      intro t
      apply (ContinuousMap.tendsto_iff_tendstoUniformly).2
      have hg : Continuous (fun p : D × Torus3 => (p.1.1, p.2)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
      have hcomp := hu.continuousOn.comp (s := Set.univ ×ˢ Set.univ)
        (t := Ici 0 ×ˢ Set.univ) hg.continuousOn (by
        intro p hp
        exact ⟨p.1.2, Set.mem_univ _⟩)
      -- The closed half-line is locally compact as a subtype.
      have hF : ContinuousOn (Function.uncurry (fun s : D => fun x => u s x))
          (Set.univ ×ˢ Set.univ) := by
        change ContinuousOn (fun p : D × Torus3 => u p.1 p.2) (Set.univ ×ˢ Set.univ)
        exact hcomp.congr (fun p _ => by rfl)
      exact @ContinuousOn.tendstoUniformly D Torus3 ℝ _ _
        (isClosed_Ici.locallyCompactSpace) _ _ (fun s : D => fun x => u s x) t Set.univ
        Filter.univ_mem hF
    change Continuous (fun t : D => u t)
    exact hD
  have h_lip : LipschitzWith (1 : NNReal) (toHolderBesov η) := by
    intro g h
    rw [edist_dist, edist_dist]
    simp only [ENNReal.coe_one, one_mul]
    apply ENNReal.ofReal_le_ofReal
    rw [dist_eq_norm (toHolderBesov η g) (toHolderBesov η h),
      ← toHolderBesov_sub η g h, norm_toHolderBesov, dist_eq_norm g h]
    rw [← ENNReal.toReal_ofReal (norm_nonneg (g - h)), ofReal_norm]
    exact ENNReal.toReal_mono enorm_ne_top (holderBesovENorm_le η.2.le (g - h))
  exact h_lip.continuous.comp_continuousOn h_u

end RegularityStructures.Phi43

end
