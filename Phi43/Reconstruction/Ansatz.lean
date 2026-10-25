/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.CubeFull
public import Phi43.FixedPointF.Degrees
import Mathlib.Tactic.Linarith

/-!
# Elements of `V ∩ T_{<γ}` are ansatz vectors

The expansion of the abstract solution, in the identification of the reconstructed solution with
the classical one: a vector of the
solution sector `V` of degrees `< γ = 1 + 3κ` has non-zero coordinates only at
`Ψ, 1, I(Ψ³), I(Ψ²), Xᵢ` (`phi43AnsatzF`), because the other symbols of `V` (`X₀`, `XᵢXⱼ`, `I(Ψ)`
and the planted integrals) have degree `≥ γ`.
-/

public section

namespace RegularityStructures.Phi43

theorem eq_phi43AnsatzF_of_mem (κ : Kappa) {a : SymbolF → ℝ} (hV : a ∈ phi43SectorV)
    (hT : a ∈ lowerSubspace (phi43RegularityStructureF κ).deg (gamma κ)) :
    a = phi43AnsatzF (a (.old .psi)) (a (.old .one)) (a (.old .iPsiCube)) (a (.old .iPsiSq))
      (fun i => a (.old (.x i))) := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hT' := (mem_lowerSubspace).1 hT
  have hV' := mem_phi43SectorV.1 hV
  funext τ
  have hdeg : ∀ σ, gamma κ ≤ phi43DegreeF κ σ → a σ = 0 := fun σ h => hT' σ h
  cases τ with
  | planted p =>
      have := phi43DegreeF_planted_ge κ p
      have h0 := hdeg (.planted p) (by simp only [gamma]; linarith)
      simp [phi43AnsatzF, phi43EF, Finset.sum_apply, h0]
  | old τ =>
      have hs : ∀ σ : Symbol, (phi43AnsatzF (a (.old .psi)) (a (.old .one)) (a (.old .iPsiCube))
          (a (.old .iPsiSq)) (fun i => a (.old (.x i)))) (.old σ) =
          if σ = .psi then a (.old .psi) else if σ = .one then a (.old .one)
          else if σ = .iPsiCube then a (.old .iPsiCube) else if σ = .iPsiSq then a (.old .iPsiSq)
          else match σ with | .x i => a (.old (.x i)) | _ => 0 := by
        intro σ
        cases σ <;> simp [phi43AnsatzF, phi43EF, Finset.sum_apply, Pi.single_apply]
      rw [hs]
      cases τ
      · simp
      · rw [hV' _ (by simp [phi43VBool])]; simp
      · rw [hdeg _ (by simp only [phi43DegreeF, homogeneity, gamma]; linarith)]; simp
      · simp
      · rw [hdeg _ (by simp only [phi43DegreeF, homogeneity, gamma]; linarith)]; simp
      · simp
      · rw [hdeg _ (by simp only [phi43DegreeF, homogeneity, gamma]; linarith)]; simp
      all_goals first
        | (simp; done)
        | (rw [hV' _ (by simp [phi43VBool])]; simp)

end RegularityStructures.Phi43

end
