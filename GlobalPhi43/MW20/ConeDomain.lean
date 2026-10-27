/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.ConeEstimate
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Domain version of the positive-radius cone estimate

The cone witness and residual bound imply the pointwise estimate and the
supremum estimate together. Boundedness of the coefficient image is derived,
not assumed. This is the domain/supremum component of MW20 (2.37); the residual
bound must still be attached to the source's optimal-affine seminorm.
-/

public section

namespace GlobalPhi43.MW20

variable {E V : Type*} [SeminormedAddCommGroup V]

/-- Apply the spatial cone condition at each point of a domain. `pair` will be
the spatial dot product and `d` the parabolic distance in the MW20 application.
No topological or smoothness restriction is needed for this algebraic step. -/
theorem cone_estimate_on_domain (D : Set E) (ν : E → V) (U : E → E → ℝ)
    (pair : V → E → E → ℝ) (d : E → E → ℝ) {r κ lam A M : ℝ}
    (hr : 0 < r)
    (hcone : ∀ x ∈ D, ∀ a : V, ∃ y ∈ D,
      d x y = r ∧ lam * ‖a‖ * r ≤ |pair a x y|)
    (hres : ∀ x ∈ D, ∀ y ∈ D, d x y = r →
      |U x y - pair (ν x) x y| ≤ A * r ^ κ)
    (hU : ∀ x ∈ D, ∀ y ∈ D, d x y = r → |U x y| ≤ M) :
    ∀ x ∈ D, lam * ‖ν x‖ ≤ A * r ^ (κ - 1) + M / r := by
  intro x hx
  obtain ⟨y, hy, hdist, hpair⟩ := hcone x hx (ν x)
  exact cone_estimate_at_positive_radius hr hpair
    (hres x hx y hy hdist) (hU x hx y hy hdist)

/-- Supremum form of (2.37), with coefficient-image boundedness proved from the
positive cone coefficient. Nonemptiness is exactly the source's domain premise. -/
theorem cone_estimate_sup (D : Set E) (hD : D.Nonempty) (ν : E → V)
    (U : E → E → ℝ) (pair : V → E → E → ℝ) (d : E → E → ℝ)
    {r κ lam A M : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (hcone : ∀ x ∈ D, ∀ a : V, ∃ y ∈ D,
      d x y = r ∧ lam * ‖a‖ * r ≤ |pair a x y|)
    (hres : ∀ x ∈ D, ∀ y ∈ D, d x y = r →
      |U x y - pair (ν x) x y| ≤ A * r ^ κ)
    (hU : ∀ x ∈ D, ∀ y ∈ D, d x y = r → |U x y| ≤ M) :
    BddAbove ((fun x => ‖ν x‖) '' D) ∧
      lam * sSup ((fun x => ‖ν x‖) '' D) ≤ A * r ^ (κ - 1) + M / r := by
  have hpoint := cone_estimate_on_domain D ν U pair d hr hcone hres hU
  have hupper : ∀ b ∈ ((fun x => ‖ν x‖) '' D),
      b ≤ (A * r ^ (κ - 1) + M / r) / lam := by
    rintro b ⟨x, hx, rfl⟩
    exact (le_div_iff₀ hlam).2 (by simpa only [mul_comm] using hpoint x hx)
  refine ⟨⟨_, hupper⟩, ?_⟩
  have hsup := csSup_le (hD.image (fun x => ‖ν x‖)) hupper
  simpa only [mul_comm] using (le_div_iff₀ hlam).1 hsup

end GlobalPhi43.MW20

end
