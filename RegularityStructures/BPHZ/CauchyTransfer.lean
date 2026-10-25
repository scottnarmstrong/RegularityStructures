/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.CauchyInProbability

/-!
# Transferring tightness and Cauchy in probability through a good event

Abstract probability steps for comparing a family `X` (sizes or distances of the models of
interest) with a reference family controlled in `L¹`.  A pointwise transfer statement
"on the good event where the reference sizes are at most `B`, `X` is bounded by (a constant times)
the reference distance" turns tightness (resp. convergence in probability to `0`) of the reference
into the same property of `X`, plus an independently controlled additive part.

* `exists_measure_lt_add_le_of_transfer` (tightness);
* `tendsto_measure_lt_add_of_transfer` (Cauchy in probability).
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Tightness through a good event.**  If the reference sizes `A` and the additive sizes `Nz`
have bounded first moments (a.e. measurable), and on `{A ε ≤ B}` the size `X ε` is bounded by a
constant `K` depending only on `B` (for all `B` large), then `X + Nz` is tight on `(0, 1]`. -/
theorem exists_measure_lt_add_le_of_transfer {A Nz X : ℝ → Ω → ℝ≥0∞} {C₁ C₂ : ℝ}
    (hAm : ∀ ε, 0 < ε → ε ≤ 1 → AEMeasurable (A ε) P)
    (hAmom : ∀ ε, 0 < ε → ε ≤ 1 → ∫⁻ ω, A ε ω ∂P ≤ ENNReal.ofReal C₁)
    (hNm : ∀ ε, 0 < ε → ε ≤ 1 → AEMeasurable (Nz ε) P)
    (hNmom : ∀ ε, 0 < ε → ε ≤ 1 → ∫⁻ ω, Nz ε ω ∂P ≤ ENNReal.ofReal C₂)
    (hT : ∃ B₀ : ℝ, ∀ B ≥ B₀, ∃ K : ℝ, ∀ ε, 0 < ε → ε ≤ 1 → ∀ᵐ ω ∂P,
      A ε ω ≤ ENNReal.ofReal B → X ε ω ≤ ENNReal.ofReal K)
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ B : ℝ, ∀ ε, 0 < ε → ε ≤ 1 → P {ω | ENNReal.ofReal B < X ε ω + Nz ε ω} ≤
      ENNReal.ofReal ϑ := by
  have h2 : 0 < ϑ / 2 := by positivity
  obtain ⟨B₁, hB₁⟩ := exists_measure_lt_le_of_lintegral_rpow_le (P := P) (S := A) (S' := A)
    (p := 1) (C := C₁) one_pos (fun _ _ _ => Filter.EventuallyEq.rfl.le) hAm
    (fun ε h0 h1 => by simpa using hAmom ε h0 h1) h2
  obtain ⟨B₂, hB₂⟩ := exists_measure_lt_le_of_lintegral_rpow_le (P := P) (S := Nz) (S' := Nz)
    (p := 1) (C := C₂) one_pos (fun _ _ _ => Filter.EventuallyEq.rfl.le) hNm
    (fun ε h0 h1 => by simpa using hNmom ε h0 h1) h2
  obtain ⟨B₀, hB₀⟩ := hT
  obtain ⟨K, hK⟩ := hB₀ (max B₁ B₀) (le_max_right _ _)
  refine ⟨max K 0 + max B₂ 0, fun ε h0 h1 => ?_⟩
  have hsub : P {ω | ENNReal.ofReal (max K 0 + max B₂ 0) < X ε ω + Nz ε ω} ≤
      P ({ω | ENNReal.ofReal B₁ < A ε ω} ∪ {ω | ENNReal.ofReal B₂ < Nz ε ω}) := by
    refine measure_mono_ae ?_
    filter_upwards [hK ε h0 h1] with ω hω hmem
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot hmem
    have hA : A ε ω ≤ ENNReal.ofReal (max B₁ B₀) := hnot.1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have := hω hA
    refine absurd hmem (not_lt.2 ?_)
    rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    exact add_le_add (this.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      (hnot.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  refine hsub.trans ((measure_union_le _ _).trans ?_)
  calc _ ≤ ENNReal.ofReal (ϑ / 2) + ENNReal.ofReal (ϑ / 2) :=
        add_le_add (hB₁ ε h0 h1) (hB₂ ε h0 h1)
    _ = ENNReal.ofReal ϑ := by rw [← ENNReal.ofReal_add h2.le h2.le]; congr 1; ring

/-- **Cauchy in probability through a good event.**  Suppose the reference sizes `A, A'` are tight
on `(0, 1]`, the reference distance `E` and the additive distance `Nd` tend to `0` in probability
as `(ε, ε') → (0⁺, 0⁺)`, `d → 0`, and on `{A ε ≤ B} ∩ {A' ε' ≤ B}` one has
`X ε ε' ≤ K (d ε ε' + E ε ε')` with `K` depending only on `B` (for all `B` large).  Then
`X + Nd` tends to `0` in probability. -/
theorem tendsto_measure_lt_add_of_transfer {Nd X E : ℝ → ℝ → Ω → ℝ≥0∞}
    {A₁ A₂ : ℝ → Ω → ℝ≥0∞} {d : ℝ → ℝ → ℝ}
    (hA : ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ, ∀ ε, 0 < ε → ε ≤ 1 →
      P {ω | ENNReal.ofReal B < A₁ ε ω} ≤ ENNReal.ofReal ϑ)
    (hA' : ∀ ϑ : ℝ, 0 < ϑ → ∃ B : ℝ, ∀ ε, 0 < ε → ε ≤ 1 →
      P {ω | ENNReal.ofReal B < A₂ ε ω} ≤ ENNReal.ofReal ϑ)
    (hE : ∀ δ : ℝ, 0 < δ → Tendsto (fun e : ℝ × ℝ => P {ω | ENNReal.ofReal δ < E e.1 e.2 ω})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0))
    (hNd : ∀ δ : ℝ, 0 < δ → Tendsto (fun e : ℝ × ℝ => P {ω | ENNReal.ofReal δ < Nd e.1 e.2 ω})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0))
    (hd : Tendsto (fun e : ℝ × ℝ => d e.1 e.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0))
    (hT : ∃ B₀ : ℝ, ∀ B ≥ B₀, ∃ K : ℝ, ∀ ε ε', 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ᵐ ω ∂P, A₁ ε ω ≤ ENNReal.ofReal B → A₂ ε' ω ≤ ENNReal.ofReal B →
        X ε ε' ω ≤ ENNReal.ofReal K * (ENNReal.ofReal (d ε ε') + E ε ε' ω))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun e : ℝ × ℝ => P {ω | ENNReal.ofReal δ < X e.1 e.2 ω + Nd e.1 e.2 ω})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have key : ∀ ϑ : ℝ, 0 < ϑ → ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ),
      P {ω | ENNReal.ofReal δ < X e.1 e.2 ω + Nd e.1 e.2 ω} ≤ ENNReal.ofReal ϑ := by
    intro ϑ hϑ
    have h4 : 0 < ϑ / 4 := by positivity
    obtain ⟨B₁, hB₁⟩ := hA _ h4
    obtain ⟨B₂, hB₂⟩ := hA' _ h4
    obtain ⟨B₀, hB₀⟩ := hT
    set B := max (max B₁ B₂) B₀ with hB
    obtain ⟨K, hK⟩ := hB₀ B (le_max_right _ _)
    set K' : ℝ := max K 0 + 1 with hK'
    have hK'pos : 0 < K' := by positivity
    set δ2 : ℝ := δ / (4 * K') with hδ2
    have hδ2pos : 0 < δ2 := by positivity
    have hI : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x ≤ 1 :=
      Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) fun x hx => ⟨hx.1, hx.2.le⟩
    have hev1 : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < e.1 ∧ e.1 ≤ 1 :=
      tendsto_fst.eventually hI
    have hev2 : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), 0 < e.2 ∧ e.2 ≤ 1 :=
      tendsto_snd.eventually hI
    have hevd : ∀ᶠ e : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ), d e.1 e.2 ≤ δ2 :=
      (hd.eventually (ge_mem_nhds hδ2pos))
    have hevE := (tendsto_order.1 (hE δ2 hδ2pos)).2 (ENNReal.ofReal (ϑ / 4))
      (ENNReal.ofReal_pos.2 h4)
    have hevN := (tendsto_order.1 (hNd (δ / 2) (by positivity))).2 (ENNReal.ofReal (ϑ / 4))
      (ENNReal.ofReal_pos.2 h4)
    filter_upwards [hev1, hev2, hevd, hevE, hevN] with e he1 he2 hed heE heN
    have hsubX : {ω | ENNReal.ofReal (δ / 2) < X e.1 e.2 ω} ≤ᵐ[P]
        ({ω | ENNReal.ofReal B < A₁ e.1 ω} ∪ {ω | ENNReal.ofReal B < A₂ e.2 ω} ∪
          {ω | ENNReal.ofReal δ2 < E e.1 e.2 ω} : Set Ω) := by
      filter_upwards [hK e.1 e.2 he1.1 he1.2 he2.1 he2.2] with ω hω hmem
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot hmem
      have h := hω hnot.1.1 hnot.1.2
      refine absurd hmem (not_lt.2 (h.trans ?_))
      calc ENNReal.ofReal K * (ENNReal.ofReal (d e.1 e.2) + E e.1 e.2 ω)
          ≤ ENNReal.ofReal K' * (ENNReal.ofReal δ2 + ENNReal.ofReal δ2) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (by rw [hK']; linarith [le_max_left K 0]))
              (add_le_add (ENNReal.ofReal_le_ofReal hed) hnot.2)
        _ = ENNReal.ofReal (δ / 2) := by
            rw [← ENNReal.ofReal_add hδ2pos.le hδ2pos.le, ← ENNReal.ofReal_mul hK'pos.le]
            congr 1
            rw [hδ2]
            field_simp
            ring
    have hsubN : {ω | ENNReal.ofReal δ < X e.1 e.2 ω + Nd e.1 e.2 ω} ⊆
        {ω | ENNReal.ofReal (δ / 2) < X e.1 e.2 ω} ∪ {ω | ENNReal.ofReal (δ / 2) < Nd e.1 e.2 ω} := by
      intro ω hω
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hnot hω
      refine absurd hω (not_lt.2 ?_)
      calc _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hnot.1 hnot.2
        _ = ENNReal.ofReal δ := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    have hB1 : P {ω | ENNReal.ofReal B < A₁ e.1 ω} ≤ ENNReal.ofReal (ϑ / 4) :=
      (measure_mono fun ω (hω : ENNReal.ofReal B < A₁ e.1 ω) =>
        (show ENNReal.ofReal B₁ < A₁ e.1 ω from lt_of_le_of_lt
          (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _))) hω)).trans
        (hB₁ e.1 he1.1 he1.2)
    have hB2 : P {ω | ENNReal.ofReal B < A₂ e.2 ω} ≤ ENNReal.ofReal (ϑ / 4) :=
      (measure_mono fun ω (hω : ENNReal.ofReal B < A₂ e.2 ω) =>
        (show ENNReal.ofReal B₂ < A₂ e.2 ω from lt_of_le_of_lt
          (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_left _ _))) hω)).trans
        (hB₂ e.2 he2.1 he2.2)
    have hXb : P {ω | ENNReal.ofReal (δ / 2) < X e.1 e.2 ω} ≤
        ENNReal.ofReal (ϑ / 4) + ENNReal.ofReal (ϑ / 4) + ENNReal.ofReal (ϑ / 4) :=
      (measure_mono_ae hsubX).trans ((measure_union_le _ _).trans
        (add_le_add ((measure_union_le _ _).trans (add_le_add hB1 hB2)) heE.le))
    calc P {ω | ENNReal.ofReal δ < X e.1 e.2 ω + Nd e.1 e.2 ω}
        ≤ P ({ω | ENNReal.ofReal (δ / 2) < X e.1 e.2 ω} ∪
          {ω | ENNReal.ofReal (δ / 2) < Nd e.1 e.2 ω}) := measure_mono hsubN
      _ ≤ _ := measure_union_le _ _
      _ ≤ (ENNReal.ofReal (ϑ / 4) + ENNReal.ofReal (ϑ / 4) + ENNReal.ofReal (ϑ / 4)) +
          ENNReal.ofReal (ϑ / 4) := add_le_add hXb heN.le
      _ = ENNReal.ofReal ϑ := by
          rw [← ENNReal.ofReal_add h4.le h4.le, ← ENNReal.ofReal_add (by positivity) h4.le,
            ← ENNReal.ofReal_add (by positivity) h4.le]
          congr 1; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηt
  · exact (key 1 one_pos).mono fun e he => he.trans le_top
  · have hpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηt
    exact (key _ hpos).mono fun e he => he.trans_eq (ENNReal.ofReal_toReal hηt)

end RegularityStructures
