/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Maximal solutions and the blow-up alternative

[Hai14, Proposition 7.11 and the discussion after it]: local solutions can be patched together
"in exactly the same way as for classical solutions", so that local solutions fail to be global
only through explosion of the norm of the restart datum `(Ru)(t, ·)`. This file proves the
patching argument abstractly.

**Setting.** `𝒮` is the space of restart data (for Φ⁴₃: `u(t, ·) = (Ru)(t, ·) ∈ C^η`) with a size
`size : 𝒮 → ℝ`; a trajectory is a map `u : ℝ → 𝒮`; `Sol a T u` means "`u` solves the equation on
`[0, T]` with initial datum `a`". The hypotheses are explicit theorem parameters:

* `hcongr`: `Sol a T u` only depends on `u` on `[0, T]`;
* `hrestr`: a solution on `[0, T]` is a solution on `[0, T']` for `0 < T' ≤ T`;
* `huniq`: two solutions on `[0, T]` with the same datum agree on `[0, T]` (local uniqueness);
* `hexist`: local existence with a time depending only on the size of the datum:
  for every `L` there is `τ > 0` such that every datum with `size a ≤ L` has a solution on
  `[0, τ]` ([Hai14, Theorem 7.8]);
* `hglue`: a solution on `[0, s]` followed by a solution on `[0, T]` restarted from `u(s)` is a
  solution on `[0, s + T]` ([Hai14, Proposition 7.11]).

**Conclusion** (`exists_maximal_solution`): there are `T* ∈ (0, ∞]` and a trajectory `u` with

* `u` solves the equation on `[0, T]` for every `T < T*`;
* every solution on some `[0, T]` has `T < T*` and coincides with `u` there (in particular no
  solution reaches `T*`);
* if `T* < ∞` then `size (u t) → ∞` as `t ↑ T*` (blow-up alternative).

`exists_global_solution_of_bound`: an a priori bound on the size of solutions gives `T* = ∞`.

Source: [Hai14, Proposition 7.11, Corollary 7.12 and the text between].
-/

public section

open Set Filter Topology
open scoped ENNReal

namespace RegularityStructures

variable {𝒮 : Type*} (size : 𝒮 → ℝ) (Sol : 𝒮 → ℝ → (ℝ → 𝒮) → Prop)

/-- Two solutions with the same datum agree on the common interval. -/
theorem sol_agree
    (hrestr : ∀ a T T' u, Sol a T u → 0 < T' → T' ≤ T → Sol a T' u)
    (huniq : ∀ a T u w, Sol a T u → Sol a T w → ∀ t ∈ Icc 0 T, u t = w t) {a : 𝒮}
    {T₁ T₂ : ℝ} {w₁ w₂ : ℝ → 𝒮} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (h₁ : Sol a T₁ w₁)
    (h₂ : Sol a T₂ w₂) {t : ℝ} (ht : t ∈ Icc 0 (min T₁ T₂)) : w₁ t = w₂ t :=
  huniq a _ w₁ w₂ (hrestr a T₁ _ w₁ h₁ (lt_min hT₁ hT₂) (min_le_left _ _))
    (hrestr a T₂ _ w₂ h₂ (lt_min hT₁ hT₂) (min_le_right _ _)) t ht

/-- **Maximal solutions and the blow-up alternative** ([Hai14, Proposition 7.11] and the
discussion after it). Under local existence with a time depending only on the size of the
datum, local uniqueness, and the restart (gluing) property, every datum `a` has a maximal
solution on `[0, T*)`; every solution is a restriction of it; and if `T* < ∞` the size of the
restart datum blows up at `T*`. -/
theorem exists_maximal_solution
    (hcongr : ∀ a T u w, Sol a T u → (∀ t ∈ Icc 0 T, u t = w t) → Sol a T w)
    (hrestr : ∀ a T T' u, Sol a T u → 0 < T' → T' ≤ T → Sol a T' u)
    (huniq : ∀ a T u w, Sol a T u → Sol a T w → ∀ t ∈ Icc 0 T, u t = w t)
    (hexist : ∀ L, ∃ τ > 0, ∀ a, size a ≤ L → ∃ u, Sol a τ u)
    (hglue : ∀ a s T u w, 0 < s → 0 < T → Sol a s u → Sol (u s) T w →
      Sol a (s + T) (fun t => if t ≤ s then u t else w (t - s)))
    (a : 𝒮) :
    ∃ (Tstar : ℝ≥0∞) (u : ℝ → 𝒮), 0 < Tstar ∧
      (∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar → Sol a T u) ∧
      (∀ T : ℝ, 0 < T → ∀ w, Sol a T w →
        ENNReal.ofReal T < Tstar ∧ ∀ t ∈ Icc 0 T, w t = u t) ∧
      (Tstar ≠ ⊤ → Tendsto (fun t => size (u t)) (𝓝[<] Tstar.toReal) atTop) := by
  classical
  -- the set of existence times and its supremum
  set A : Set ℝ := {T | 0 < T ∧ ∃ w, Sol a T w} with hA
  set Tstar : ℝ≥0∞ := ⨆ T ∈ A, ENNReal.ofReal T with hTstar
  have hle : ∀ T ∈ A, ENNReal.ofReal T ≤ Tstar := fun T hT => le_biSup (fun T => _) hT
  have hlt : ∀ t : ℝ, ENNReal.ofReal t < Tstar → ∃ T ∈ A, t < T := by
    intro t ht
    obtain ⟨T, hTA, htT⟩ := lt_biSup_iff.1 ht
    exact ⟨T, hTA, (ENNReal.ofReal_lt_ofReal_iff hTA.1).1 htT⟩
  -- the maximal trajectory
  set u : ℝ → 𝒮 := fun t =>
    if h : ∃ T, T ∈ A ∧ t ≤ T then (Classical.choose (Classical.choose_spec h).1.2) t else a
    with hu_def
  have hu : ∀ T (w : ℝ → 𝒮), 0 < T → Sol a T w → ∀ t ∈ Icc 0 T, w t = u t := by
    intro T w hT hw t ht
    have h : ∃ T, T ∈ A ∧ t ≤ T := ⟨T, ⟨hT, w, hw⟩, ht.2⟩
    rw [hu_def]
    simp only [dite_eq_left h]
    set T' := Classical.choose h with hT'
    have hT'A : T' ∈ A := (Classical.choose_spec h).1
    have htT' : t ≤ T' := (Classical.choose_spec h).2
    exact sol_agree Sol hrestr huniq hT hT'A.1 hw (Classical.choose_spec hT'A.2)
      ⟨ht.1, le_min ht.2 htT'⟩
  -- solutions extend strictly
  have hextend : ∀ T (w : ℝ → 𝒮), 0 < T → Sol a T w → ∃ T' ∈ A, T < T' := by
    intro T w hT hw
    obtain ⟨τ, hτ, hτex⟩ := hexist (size (w T))
    obtain ⟨z, hz⟩ := hτex (w T) le_rfl
    exact ⟨T + τ, ⟨by linarith, _, hglue a T τ w z hT hτ hw hz⟩, by linarith⟩
  have hsol : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tstar → Sol a T u := by
    intro T hT hTlt
    obtain ⟨T', hT'A, hTT'⟩ := hlt T hTlt
    obtain ⟨w, hw⟩ := hT'A.2
    exact hcongr a T w u (hrestr a T' T w hw hT hTT'.le)
      (fun t ht => hu T' w hT'A.1 hw t ⟨ht.1, ht.2.trans hTT'.le⟩)
  refine ⟨Tstar, u, ?_, hsol, ?_, ?_⟩
  · -- positivity
    obtain ⟨τ, hτ, hτex⟩ := hexist (size a)
    obtain ⟨z, hz⟩ := hτex a le_rfl
    exact (ENNReal.ofReal_pos.2 hτ).trans_le (hle τ ⟨hτ, z, hz⟩)
  · -- every solution is a restriction of `u`, on a strictly shorter interval
    intro T hT w hw
    obtain ⟨T', hT'A, hTT'⟩ := hextend T w hT hw
    exact ⟨((ENNReal.ofReal_lt_ofReal_iff hT'A.1).2 hTT').trans_le (hle T' hT'A),
      hu T w hT hw⟩
  · -- blow-up
    intro hfin
    set Ts := Tstar.toReal with hTs
    have hTs_eq : ENNReal.ofReal Ts = Tstar := ENNReal.ofReal_toReal hfin
    refine tendsto_atTop.2 fun L => ?_
    obtain ⟨τ, hτ, hτex⟩ := hexist L
    have hpos : 0 < Ts := by
      obtain ⟨τ₀, hτ₀, hτ₀ex⟩ := hexist (size a)
      obtain ⟨z, hz⟩ := hτ₀ex a le_rfl
      have h1 : ENNReal.ofReal τ₀ ≤ ENNReal.ofReal Ts := hTs_eq ▸ hle τ₀ ⟨hτ₀, z, hz⟩
      have h2 := (ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)).1 h1
      linarith
    have hmem : Ioo (max 0 (Ts - τ)) Ts ∈ 𝓝[<] Ts :=
      Ioo_mem_nhdsLT (max_lt hpos (by linarith))
    refine Filter.mem_of_superset hmem fun t ht => ?_
    show L ≤ size (u t)
    by_contra hcon
    have hsize : size (u t) ≤ L := (not_le.1 hcon).le
    have ht0 : 0 < t := (le_max_left _ _).trans_lt ht.1
    have htlt : ENNReal.ofReal t < Tstar := by
      rw [← hTs_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 ht.2
    obtain ⟨z, hz⟩ := hτex (u t) hsize
    have hglued := hglue a t τ u z ht0 hτ (hsol t ht0 htlt) hz
    have hmax := hle (t + τ) ⟨by linarith, _, hglued⟩
    rw [← hTs_eq] at hmax
    have := (ENNReal.ofReal_le_ofReal_iff hpos.le).1 hmax
    linarith [(le_max_right 0 (Ts - τ)).trans_lt ht.1]

/-- **Global existence under an a priori bound**: if the size of every solution stays below `B`
on its interval of existence, the maximal solution is global (`T* = ∞`). -/
theorem exists_global_solution_of_bound
    (hcongr : ∀ a T u w, Sol a T u → (∀ t ∈ Icc 0 T, u t = w t) → Sol a T w)
    (hrestr : ∀ a T T' u, Sol a T u → 0 < T' → T' ≤ T → Sol a T' u)
    (huniq : ∀ a T u w, Sol a T u → Sol a T w → ∀ t ∈ Icc 0 T, u t = w t)
    (hexist : ∀ L, ∃ τ > 0, ∀ a, size a ≤ L → ∃ u, Sol a τ u)
    (hglue : ∀ a s T u w, 0 < s → 0 < T → Sol a s u → Sol (u s) T w →
      Sol a (s + T) (fun t => if t ≤ s then u t else w (t - s)))
    (a : 𝒮) {B : ℝ} (hB : ∀ T u, 0 < T → Sol a T u → ∀ t ∈ Icc 0 T, size (u t) ≤ B) :
    ∃ u : ℝ → 𝒮, ∀ T : ℝ, 0 < T → Sol a T u := by
  obtain ⟨Tstar, u, hpos, hsol, -, hblow⟩ :=
    exists_maximal_solution size Sol hcongr hrestr huniq hexist hglue a
  by_cases hfin : Tstar = ⊤
  · exact ⟨u, fun T hT => hsol T hT (hfin ▸ ENNReal.ofReal_lt_top)⟩
  · exfalso
    have hTs_eq : ENNReal.ofReal Tstar.toReal = Tstar := ENNReal.ofReal_toReal hfin
    have hTs : 0 < Tstar.toReal := ENNReal.toReal_pos hpos.ne' hfin
    have hev := (tendsto_atTop.1 (hblow hfin)) (B + 1)
    have hmem : Ioo (Tstar.toReal / 2) Tstar.toReal ∈ 𝓝[<] Tstar.toReal :=
      Ioo_mem_nhdsLT (by linarith)
    obtain ⟨t, ht1, ht2⟩ := (hev.and (Filter.mem_of_superset hmem fun t ht => ht)).exists
    have ht0 : 0 < t := by linarith [ht2.1]
    have htlt : ENNReal.ofReal t < Tstar := by
      rw [← hTs_eq]
      exact (ENNReal.ofReal_lt_ofReal_iff hTs).2 ht2.2
    have := hB t u ht0 (hsol t ht0 htlt) t ⟨ht0.le, le_rfl⟩
    linarith

end RegularityStructures

end
