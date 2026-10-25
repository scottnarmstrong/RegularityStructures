/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Reconstruction.Ansatz
public import Phi43.Identification.FixedPointExpansion

/-!
# Pointwise expansion of the abstract solution

The expansion of the abstract solution, the first step of its identification with the classical
solution [Hai14, (9.22)].
`phi43_expansion_pointwise`: a vector `u ∈ V ∩ T_{<γ}` which satisfies the fixed point equation
`u = -Q_{<γ} K + v` with `K ≡ I (blockProj (Q_{<κ} u³))` and `v ≡ Ψ` modulo the polynomials is
`u = Ψ + φ·1 - I(Ψ³) - 3φ I(Ψ²) + ∑ᵢ φᵢ Xᵢ`, with `φ = u_1` and `φᵢ = u_{Xᵢ}`.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43_expansion_pointwise (κ : Kappa) (u K v : SymbolF → ℝ) (hV : u ∈ phi43SectorV)
    (hT : u ∈ lowerSubspace (phi43RegularityStructureF κ).deg (gamma κ))
    (hU : u = -RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg (gamma κ) K + v)
    (hK : K - phi43IntegrationF (RegularityStructures.blockProj phi43XiFreeF
        (RegularityStructures.lowerProj (phi43RegularityStructureF κ).deg κ.1
          ((phi43ProductF κ).mul u ((phi43ProductF κ).mul u u)))) ∈
      (phi43PolynomialSectorF κ).subspace)
    (hv : v - phi43EF .psi ∈ (phi43PolynomialSectorF κ).subspace) :
    u = phi43AnsatzF 1 (u (.old .one)) (-1) (-3 * u (.old .one)) (fun i => u (.old (.x i))) := by
  have he := eq_phi43AnsatzF_of_mem κ hV hT
  obtain ⟨a, φ, c₃, c₂, ψ, he', hφ, hψ⟩ : ∃ (a φ c₃ c₂ : ℝ) (ψ : Fin 3 → ℝ),
      u = phi43AnsatzF a φ c₃ c₂ ψ ∧ φ = u (.old .one) ∧ ψ = fun i => u (.old (.x i)) :=
    ⟨_, _, _, _, _, he, rfl, rfl⟩
  rw [← hφ, ← hψ]
  have hK' := hK
  rw [he'] at hK'
  have key := phi43_expansion_of_fixedPoint κ a φ c₃ c₂ ψ K v (by rw [← he']; exact hU) hK' hv
  obtain ⟨h1, h2, h3⟩ := key
  rw [he', h1, h2, h3]

end RegularityStructures.Phi43

end
