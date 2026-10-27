module

public import GlobalPhi43.MW20.CylinderSup
public import GlobalPhi43.Local.RadiusGeometry

/-! Testing geometry for the large-scale row, with the literal range k > 2. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The ordinary parent inset is contained in the mixed-time interior.
The converse is not used: the mixed lower time remains r²+d². -/
theorem sourceCylinder_add_subset_mixed {r d : ℝ} (hr : 0 ≤ r) (hd : 0 ≤ d) :
    sourceCylinder (r + d) ⊆ Local.cylinderInterior r d := by
  intro x hx
  refine ⟨?_, hx.2.1, fun i => ?_⟩
  · nlinarith [hx.1, mul_nonneg hr hd]
  · have hi := abs_lt.mp (hx.2.2 i)
    constructor <;> linarith [hi.1, hi.2]

/-- At T=d0/k the testing ball stays in D_(d0*(k-1)/k).
No extra restriction k >= 3 is needed. -/
theorem large_scale_testing_ball_subset {r d₀ k : ℝ}
    (hr : 0 ≤ r) (hd₀ : 0 < d₀) (hk : 2 < k)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder (r + d₀)) :
    Local.pastBall x (d₀ / k) ⊆ Local.cylinderInterior r (d₀ * (k - 1) / k) := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hd : 0 ≤ d₀ * (k - 1) / k := by positivity
  have hbudget : d₀ * (k - 1) / k + d₀ / k ≤ d₀ := by
    apply le_of_eq
    field_simp
    ring
  exact Local.pastBall_subset_interior hd (by positivity) hbudget
    (sourceCylinder_add_subset_mixed hr hd₀.le hx)

end GlobalPhi43.MW20
