/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GModelsConstantShift

/-!
# Asymptotic equality of the constant shifts across mollifiers

Given the `ρ`-independent limits of `wickConstant − hairerWickConstant` and
`sunsetConstant − hairerSunsetConstant` (`constantsComparison`), the shifts `gModelsShift N ρ c ε`
and `gModelsShift N ρ' c ε'` are asymptotically equal as `(ε, ε') → (0⁺, 0⁺)`.
-/

public section

open Filter Topology

namespace RegularityStructures.Phi43

/-- The difference of the shifts for two mollifiers tends to `0`. -/
theorem tendsto_norm_gModelsShift_sub (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ)
    (c : RenormalisationConstants) {L₁ L₂ : ℝ}
    (h1 : Tendsto (fun ε : ℝ => wickConstant ρ ε - hairerWickConstant N ρ ε) (𝓝[>] 0) (𝓝 L₁))
    (h2 : Tendsto (fun ε : ℝ => sunsetConstant ρ ε - hairerSunsetConstant N ρ ε) (𝓝[>] 0)
      (𝓝 L₂))
    (h1' : Tendsto (fun ε : ℝ => wickConstant ρ' ε - hairerWickConstant N ρ' ε) (𝓝[>] 0)
      (𝓝 L₁))
    (h2' : Tendsto (fun ε : ℝ => sunsetConstant ρ' ε - hairerSunsetConstant N ρ' ε) (𝓝[>] 0)
      (𝓝 L₂)) :
    Tendsto (fun e : ℝ × ℝ => ‖gModelsShift N ρ c e.1 - gModelsShift N ρ' c e.2‖)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have a1 := (h1.comp tendsto_fst).sub (h1'.comp (tendsto_snd (f := 𝓝[>] (0 : ℝ))
    (g := 𝓝[>] (0 : ℝ))))
  have a2 := (h2.comp tendsto_fst).sub (h2'.comp (tendsto_snd (f := 𝓝[>] (0 : ℝ))
    (g := 𝓝[>] (0 : ℝ))))
  rw [sub_self] at a1 a2
  have a := a1.prodMk_nhds a2
  have e : (fun e : ℝ × ℝ => gModelsShift N ρ c e.1 - gModelsShift N ρ' c e.2) =
      fun e => ((wickConstant ρ e.1 - hairerWickConstant N ρ e.1) -
          (wickConstant ρ' e.2 - hairerWickConstant N ρ' e.2),
        (sunsetConstant ρ e.1 - hairerSunsetConstant N ρ e.1) -
          (sunsetConstant ρ' e.2 - hairerSunsetConstant N ρ' e.2)) := by
    funext e
    refine Prod.ext ?_ ?_ <;> simp only [gModelsShift, Prod.fst_sub, Prod.snd_sub] <;> ring
  have := tendsto_zero_iff_norm_tendsto_zero.1 (e ▸ a : Tendsto
    (fun e : ℝ × ℝ => gModelsShift N ρ c e.1 - gModelsShift N ρ' c e.2) _ (𝓝 0))
  exact this

end RegularityStructures.Phi43

end
