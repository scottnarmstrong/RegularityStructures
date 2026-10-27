module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded Lipschitz derivative fields of a compactly supported smooth seed
-/

public section

namespace GlobalPhi43.MW20

open scoped BoundedContinuousFunction ContDiff NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every derivative of a smooth compactly supported seed has a finite global bound. -/
theorem compactSmooth_jet_bound {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) : ∃ C ≥ 0, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := hs.exists_bound_iteratedFDeriv hf n
  exact ⟨C, hC, fun x => hb n le_rfl x⟩

/-- The actual n-th derivative, bundled with its proved uniform bound. -/
@[expose] noncomputable def compactSmoothJet (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) : E →ᵇ (E [×n]→L[ℝ] F) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (iteratedFDeriv ℝ n f)
    (hf.continuous_iteratedFDeriv (by simp))
    (Classical.choose (compactSmooth_jet_bound hf hs n))
    (Classical.choose_spec (compactSmooth_jet_bound hf hs n)).2

/-- A bound on the next derivative gives a global Lipschitz bound for each jet. -/
theorem compactSmoothJet_lipschitz (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) : ∃ K : ℝ≥0, LipschitzWith K (compactSmoothJet f hf hs n) := by
  obtain ⟨C, hC, hb⟩ := compactSmooth_jet_bound hf hs (n + 1)
  refine ⟨⟨C, hC⟩, ?_⟩
  change LipschitzWith ⟨C, hC⟩ (iteratedFDeriv ℝ n f)
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · have hfn : ContDiff ℝ (n + 1) f := hf.of_le (by simp)
    exact hfn.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n)
  · intro x
    change ‖fderiv ℝ (iteratedFDeriv ℝ n f) x‖ ≤ C
    rw [norm_fderiv_iteratedFDeriv]
    exact hb x

/-- The derivative relation between two consecutive actual seed jets. -/
theorem compactSmoothJet_hasFDerivAt (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (n : ℕ) (x : E) :
    HasFDerivAt (compactSmoothJet f hf hs n)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F)
        (compactSmoothJet f hf hs (n + 1) x)) x := by
  have hfn : ContDiff ℝ (n + 1) f := hf.of_le (by simp)
  have hd := (hfn.differentiable_iteratedFDeriv
    (m := n) (by exact_mod_cast Nat.lt_succ_self n) x).hasFDerivAt
  change HasFDerivAt (iteratedFDeriv ℝ n f)
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F)
      (iteratedFDeriv ℝ (n + 1) f x)) x
  simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using! hd

end GlobalPhi43.MW20
