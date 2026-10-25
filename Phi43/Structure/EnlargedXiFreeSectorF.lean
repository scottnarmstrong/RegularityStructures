/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedAbstractF
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock

/-!
# The Xi-free sector of the enlarged Φ⁴₃ structure

The block containing every symbol except `Ξ` is a genuine sector.  Its graded
part is coordinatewise, while its invariance is the structural block
invariance already proved for the enlarged extension group.  This is the
sector hypothesis used by the structural-block version of the Φ⁴₃ fixed point
([Hai14, Proposition 9.8], on the enlarged structure, where the Xi-free block
commutes with the structure group).
-/

public section

namespace RegularityStructures.Phi43

theorem phi43XiFreeF_isSector (κ : Kappa) :
    (phi43RegularityStructureF κ).IsSector (blockSpan phi43XiFreeF) where
  graded α a ha := by
    refine mem_blockSpan_of_forall fun i hi => ?_
    rw [homogeneousProj_apply]
    split_ifs with hdeg
    · exact eq_zero_of_notMem_of_mem_blockSpan ha hi
    · rfl
  invariant g hg a ha := by
    refine mem_blockSpan_of_forall fun i hi => ?_
    have hiNoise : i = .old .noise := by
      simpa [phi43XiFreeF] using hi
    subst i
    rw [phi43ExtensionGroupF_noise_coord κ g hg]
    exact eq_zero_of_notMem_of_mem_blockSpan ha (by simp [phi43XiFreeF])

end RegularityStructures.Phi43

end
