/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedAll
public import Phi43.Structure.QuadraticIntegration
public import RegularityStructures.Abstract.IntExt.Basic

/-!
# The planted data of the enlarged `Φ⁴₃` structure, in the `IntExt` format

[Hai14, Theorem 5.14, Definition 5.7]. The twelve old `Ψ`-containing symbols other than `Ψ, Ψ²,
Ψ³` are `phi43PlantDE`; `phi43PlantNewE` sends such a symbol to its planted integral. We prove that
the generic integration `IntExt.intExt old new D I` of the extension data, for the old
integration `I = phi43AbstractIntegration`, is `phi43IntegrationF`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The twelve old symbols whose integral is planted. -/
def phi43PlantDE : Finset Symbol := Finset.univ.image Phi43PlantSource.symbol

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem mem_phi43PlantDE {d : Symbol} : d ∈ phi43PlantDE ↔ ∃ τ : Phi43PlantSource, τ.symbol = d := by
  simp [phi43PlantDE]

theorem phi43PlantSource_symbol_mem (τ : Phi43PlantSource) : τ.symbol ∈ phi43PlantDE :=
  mem_phi43PlantDE.2 ⟨τ, rfl⟩

theorem phi43PlantDE_ne_noise {d : Symbol} (hd : d ∈ phi43PlantDE) : d ≠ .noise := by
  obtain ⟨τ, rfl⟩ := mem_phi43PlantDE.1 hd
  cases τ <;> simp [Phi43PlantSource.symbol]

theorem phi43PlantDE_ne_psi {d : Symbol} (hd : d ∈ phi43PlantDE) : d ≠ .psi := by
  obtain ⟨τ, rfl⟩ := mem_phi43PlantDE.1 hd
  cases τ <;> simp [Phi43PlantSource.symbol]

theorem phi43PlantDE_ne_psiSq {d : Symbol} (hd : d ∈ phi43PlantDE) : d ≠ .psiSq := by
  obtain ⟨τ, rfl⟩ := mem_phi43PlantDE.1 hd
  cases τ <;> simp [Phi43PlantSource.symbol]

theorem phi43PlantDE_ne_psiCube {d : Symbol} (hd : d ∈ phi43PlantDE) : d ≠ .psiCube := by
  obtain ⟨τ, rfl⟩ := mem_phi43PlantDE.1 hd
  cases τ <;> simp [Phi43PlantSource.symbol]

end RegularityStructures.Phi43

end
