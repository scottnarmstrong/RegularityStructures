module

public import GlobalPhi43.MW20.PastBallTesting

/-!
# Diameter and nesting of the literal source testing balls
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- Both points of a source past ball have distance at most twice its radius. -/
theorem pastBall_pair_distance {x a b : ParabolicSpace} {T : ℝ}
    (ha : a ∈ Local.pastBall x T) (hb : b ∈ Local.pastBall x T) :
    Local.pdist a b ≤ 2 * T := by
  have ht := Local.pdist_triangle a x b
  rw [Local.pdist_symm a x] at ht
  linarith [ha.1, hb.1]

/-- The nested open balls fit inside the actual summed-radius past ball. -/
theorem pastBall_nested_subset {x y : ParabolicSpace} {L T : ℝ}
    (hy : y ∈ Local.pastBall x L) :
    Local.pastBall y T ⊆ Local.pastBall x (L + T) := by
  intro z hz
  refine ⟨?_, lt_trans hz.2 hy.2⟩
  have ht := Local.pdist_triangle x y z
  linarith [hy.1, hz.1]

end GlobalPhi43.MW20
