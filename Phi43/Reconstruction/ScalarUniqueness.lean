/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A weighted Gronwall uniqueness for singular integral inequalities

`scalar_uniqueness`: let `d(t, x)` satisfy `|d(t, x)| ≤ B t^{η/2}` for `0 < t ≤ T`, with
`-2/3 < η < 0`, and suppose that for every `g ≥ 0` (measurable, interval integrable) with
`(a₀ r^η + b₀) |d(r, y)| ≤ g(r)` for `0 < r ≤ t` one has `|d(t, x)| ≤ ∫₀ᵗ g`.  Then `d = 0`.
Used for the spatial periodicity of the unit coordinate of the fixed point: the difference of
two lattice translates satisfies the integral inequality with `ℓ(r) = 3A² r^η + |c|`.
-/

public section

open Set MeasureTheory Filter Topology

namespace RegularityStructures.Phi43

variable {η a₀ b₀ T B : ℝ} {d : ℝ → (Fin 3 → ℝ) → ℝ}

/-- The integral estimate of `stepA`: for `0 < t ≤ τ` small the weighted constant is `≤ 1/2`. -/
theorem exists_small_weight (hη₁ : -2 / 3 < η) (hη0 : η < 0) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ t ∈ Ioc 0 τ₀,
      a₀ * t ^ (η + 1) / (3 * η / 2 + 1) + b₀ * t / (η / 2 + 1) ≤ 1 / 2 := by
  have hp1 : 0 < η + 1 := by linarith
  have h1 : Tendsto (fun t : ℝ => a₀ * t ^ (η + 1) / (3 * η / 2 + 1) + b₀ * t / (η / 2 + 1))
      (𝓝[>] 0) (𝓝 0) := by
    have e1 : Tendsto (fun t : ℝ => t ^ (η + 1)) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuous_rpow_const hp1.le).tendsto 0)
      rw [Real.zero_rpow hp1.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have e2 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have := ((e1.const_mul a₀).div_const (3 * η / 2 + 1)).add ((e2.const_mul b₀).div_const (η / 2 + 1))
    simpa using this
  obtain ⟨ε, hε, hεb⟩ := Metric.tendsto_nhdsWithin_nhds.1 h1 (1 / 2) (by norm_num)
  refine ⟨ε / 2, half_pos hε, fun t ht => ?_⟩
  have := hεb (show t ∈ Ioi 0 from ht.1) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2])
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- The hypothesis `h2` of the uniqueness lemma, as a predicate. -/
@[expose] def SingularGronwall (η a₀ b₀ T : ℝ) (d : ℝ → (Fin 3 → ℝ) → ℝ) : Prop :=
  ∀ t ∈ Ioc 0 T, ∀ x (g : ℝ → ℝ), (∀ r, 0 ≤ g r) → Measurable g → IntervalIntegrable g volume 0 t →
    (∀ r ∈ Ioc 0 t, ∀ y, (a₀ * r ^ η + b₀) * |d r y| ≤ g r) →
      |d t x| ≤ ∫ r in (0 : ℝ)..t, g r

theorem integral_weight {t : ℝ} (ht : 0 < t) (hη₁ : -2 / 3 < η) (hη0 : η < 0) (c : ℝ) :
    ∫ r in (0 : ℝ)..t, c * (a₀ * |r| ^ (3 * η / 2) + b₀ * |r| ^ (η / 2)) =
      c * (a₀ * (t ^ (3 * η / 2 + 1) / (3 * η / 2 + 1)) +
        b₀ * (t ^ (η / 2 + 1) / (η / 2 + 1))) := by
  have h3 : -1 < 3 * η / 2 := by linarith
  have h1 : -1 < η / 2 := by linarith
  have e : ∀ r ∈ uIcc 0 t, c * (a₀ * |r| ^ (3 * η / 2) + b₀ * |r| ^ (η / 2)) =
      c * (a₀ * r ^ (3 * η / 2) + b₀ * r ^ (η / 2)) := by
    intro r hr
    rw [uIcc_of_le ht.le] at hr
    simp only [abs_of_nonneg hr.1]
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((intervalIntegral.intervalIntegrable_rpow' h3).const_mul a₀)
      ((intervalIntegral.intervalIntegrable_rpow' h1).const_mul b₀),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl h3), integral_rpow (Or.inl h1),
    Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  ring

theorem intervalIntegrable_weight {t : ℝ} (ht : 0 < t) (hη₁ : -2 / 3 < η) (hη0 : η < 0) (c : ℝ) :
    IntervalIntegrable (fun r : ℝ => c * (a₀ * |r| ^ (3 * η / 2) + b₀ * |r| ^ (η / 2)))
      volume 0 t := by
  have h3 : -1 < 3 * η / 2 := by linarith
  have h1 : -1 < η / 2 := by linarith
  refine IntervalIntegrable.congr (fun r hr => ?_)
    (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) h3).const_mul a₀).add
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) h1).const_mul b₀)
      |>.const_mul c)
  have hr0 : 0 ≤ r := by
    rw [uIoc_of_le ht.le] at hr
    exact hr.1.le
  simp only [abs_of_nonneg hr0]

/-- **Step A**: on a short interval the bound halves at each iteration. -/
theorem sU_stepA (hη₁ : -2 / 3 < η) (hη0 : η < 0)
    (h1 : ∀ t ∈ Ioc 0 T, ∀ x, |d t x| ≤ B * t ^ (η / 2))
    (h2 : SingularGronwall η a₀ b₀ T d) {τ₀ : ℝ}
    (hsmall : ∀ t ∈ Ioc 0 τ₀, a₀ * t ^ (η + 1) / (3 * η / 2 + 1) + b₀ * t / (η / 2 + 1) ≤ 1 / 2)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hB : 0 ≤ B) :
    ∀ k : ℕ, ∀ t ∈ Ioc 0 (min τ₀ T), ∀ x, |d t x| ≤ B / 2 ^ k * t ^ (η / 2) := by
  intro k
  induction k with
  | zero =>
      intro t ht x
      simpa using h1 t ⟨ht.1, ht.2.trans (min_le_right _ _)⟩ x
  | succ k ih =>
      intro t ht x
      have htT : t ∈ Ioc 0 T := ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
      have hc : 0 ≤ B / 2 ^ k := by positivity
      set g : ℝ → ℝ := fun r => B / 2 ^ k * (a₀ * |r| ^ (3 * η / 2) + b₀ * |r| ^ (η / 2)) with hg
      have hg0 : ∀ r, 0 ≤ g r := fun r => mul_nonneg hc (add_nonneg
        (mul_nonneg ha₀ (Real.rpow_nonneg (abs_nonneg _) _))
        (mul_nonneg hb₀ (Real.rpow_nonneg (abs_nonneg _) _)))
      have hgm : Measurable g := by
        simp only [hg]
        fun_prop
      have hgi := intervalIntegrable_weight (a₀ := a₀) (b₀ := b₀) ht.1 hη₁ hη0 (B / 2 ^ k)
      have hb := h2 t htT x g hg0 hgm hgi (fun r hr y => by
        have hrT : r ∈ Ioc 0 (min τ₀ T) := ⟨hr.1, hr.2.trans ht.2⟩
        have hd := ih r hrT y
        have hℓ : 0 ≤ a₀ * r ^ η + b₀ := add_nonneg (mul_nonneg ha₀ (Real.rpow_nonneg hr.1.le _)) hb₀
        calc (a₀ * r ^ η + b₀) * |d r y| ≤ (a₀ * r ^ η + b₀) * (B / 2 ^ k * r ^ (η / 2)) :=
              mul_le_mul_of_nonneg_left hd hℓ
          _ = g r := by
              simp only [hg, abs_of_pos hr.1]
              have : r ^ (3 * η / 2) = r ^ η * r ^ (η / 2) := by
                rw [← Real.rpow_add hr.1]; congr 1; ring
              rw [this]; ring)
      refine hb.trans ?_
      rw [integral_weight ht.1 hη₁ hη0]
      have htτ : t ∈ Ioc 0 τ₀ := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
      have hs := hsmall t htτ
      have hp : 0 < t ^ (η / 2) := Real.rpow_pos_of_pos ht.1 _
      have e1 : t ^ (3 * η / 2 + 1) = t ^ (η / 2) * t ^ (η + 1) := by
        rw [← Real.rpow_add ht.1]; congr 1; ring
      have e2 : t ^ (η / 2 + 1) = t ^ (η / 2) * t := by
        rw [Real.rpow_add ht.1, Real.rpow_one]
      rw [e1, e2]
      have : B / 2 ^ k * (a₀ * (t ^ (η / 2) * t ^ (η + 1) / (3 * η / 2 + 1)) +
          b₀ * (t ^ (η / 2) * t / (η / 2 + 1))) =
          B / 2 ^ k * t ^ (η / 2) * (a₀ * t ^ (η + 1) / (3 * η / 2 + 1) + b₀ * t / (η / 2 + 1)) := by
        ring
      rw [this, pow_succ]
      calc _ ≤ B / 2 ^ k * t ^ (η / 2) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hs (mul_nonneg hc hp.le)
        _ = B / (2 ^ k * 2) * t ^ (η / 2) := by ring

theorem eq_zero_of_halving {x C : ℝ} (h : ∀ k : ℕ, |x| ≤ C / 2 ^ k) : x = 0 := by
  have hlim : Tendsto (fun k : ℕ => C / 2 ^ k) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul C
    simpa [div_eq_mul_inv, one_div, inv_pow] using this
  have := ge_of_tendsto' hlim h
  exact abs_nonpos_iff.1 this

theorem sU_stepA_zero (hη₁ : -2 / 3 < η) (hη0 : η < 0)
    (h1 : ∀ t ∈ Ioc 0 T, ∀ x, |d t x| ≤ B * t ^ (η / 2))
    (h2 : SingularGronwall η a₀ b₀ T d) {τ₀ : ℝ}
    (hsmall : ∀ t ∈ Ioc 0 τ₀, a₀ * t ^ (η + 1) / (3 * η / 2 + 1) + b₀ * t / (η / 2 + 1) ≤ 1 / 2)
    (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hB : 0 ≤ B) :
    ∀ t ∈ Ioc 0 (min τ₀ T), ∀ x, d t x = 0 := by
  intro t ht x
  refine eq_zero_of_halving (C := B * t ^ (η / 2))
    fun k => ?_
  have := sU_stepA hη₁ hη0 h1 h2 hsmall ha₀ hb₀ hB k t ht x
  rwa [div_mul_eq_mul_div] at this

theorem intervalIntegrable_indicator_Ioi_const (K t₁ r : ℝ) (hr : 0 ≤ r) :
    IntervalIntegrable ((Ioi t₁).indicator fun _ => K) volume 0 r := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr]
  exact (integrableOn_const (by simp) (by simp)).indicator measurableSet_Ioi

theorem integral_indicator_Ioi_const (K : ℝ) {t₁ r : ℝ} (h0 : 0 ≤ t₁) (hr : t₁ ≤ r) :
    ∫ ρ in (0 : ℝ)..r, (Ioi t₁).indicator (fun _ => K) ρ = K * (r - t₁) := by
  rw [intervalIntegral.integral_of_le (h0.trans hr), setIntegral_indicator measurableSet_Ioi]
  have : Ioc 0 r ∩ Ioi t₁ = Ioc t₁ r := by
    ext ρ
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h0.trans_lt h1, h2⟩, h1⟩
  rw [this, setIntegral_const, Real.volume_real_Ioc_of_le hr]
  simp [mul_comm]

/-- **Step B**: extension of the vanishing by a step of uniform length. -/
theorem sU_stepB (hη₁ : -2 / 3 < η) (hη0 : η < 0)
    (h1 : ∀ t ∈ Ioc 0 T, ∀ x, |d t x| ≤ B * t ^ (η / 2))
    (h2 : SingularGronwall η a₀ b₀ T d) (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀) (hB : 0 ≤ B)
    {τ₀ δ t₁ : ℝ} (hτ₀ : 0 < τ₀) (hδL : δ * (a₀ * τ₀ ^ η + b₀) ≤ 1 / 2)
    (hτt : τ₀ ≤ t₁) (hZ : ∀ r ∈ Ioc 0 t₁, ∀ y, d r y = 0) :
    ∀ r ∈ Ioc 0 (min T (t₁ + δ)), ∀ y, d r y = 0 := by
  have ht₁ : 0 < t₁ := hτ₀.trans_le hτt
  set B₁ := B * t₁ ^ (η / 2) with hB₁
  have hB₁0 : 0 ≤ B₁ := mul_nonneg hB (Real.rpow_nonneg ht₁.le _)
  set L₀ := a₀ * τ₀ ^ η + b₀ with hL₀
  have hL₀0 : 0 ≤ L₀ := add_nonneg (mul_nonneg ha₀ (Real.rpow_nonneg hτ₀.le _)) hb₀
  have key : ∀ j : ℕ, ∀ r ∈ Ioc 0 (min T (t₁ + δ)), ∀ y, |d r y| ≤ B₁ / 2 ^ j := by
    intro j
    induction j with
    | zero =>
        intro r hr y
        by_cases hrt : r ≤ t₁
        · rw [hZ r ⟨hr.1, hrt⟩ y]; simpa using hB₁0
        · have hrT : r ∈ Ioc 0 T := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
          have := h1 r hrT y
          refine this.trans ?_
          simp only [pow_zero, div_one, hB₁]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht₁ (not_le.1 hrt).le
            (by linarith)) hB
    | succ j ih =>
        intro r hr y
        by_cases hrt : r ≤ t₁
        · rw [hZ r ⟨hr.1, hrt⟩ y, abs_zero]; positivity
        · have hrT : r ∈ Ioc 0 T := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
          set K := L₀ * (B₁ / 2 ^ j) with hK
          have hK0 : 0 ≤ K := by positivity
          set g : ℝ → ℝ := (Ioi t₁).indicator (fun _ => K) with hg
          have hg0 : ∀ ρ, 0 ≤ g ρ := fun ρ => indicator_nonneg (fun _ _ => hK0) ρ
          have hgm : Measurable g := measurable_const.indicator measurableSet_Ioi
          have hgi : IntervalIntegrable g volume 0 r :=
            intervalIntegrable_indicator_Ioi_const K t₁ r hr.1.le
          have hb := h2 r hrT y g hg0 hgm hgi (fun ρ hρ y' => by
            by_cases hρt : ρ ≤ t₁
            · rw [hZ ρ ⟨hρ.1, hρt⟩ y']
              simp only [abs_zero, mul_zero]
              exact hg0 ρ
            · have hρτ : τ₀ ≤ ρ := hτt.trans (not_le.1 hρt).le
              have hℓ : a₀ * ρ ^ η + b₀ ≤ L₀ := by
                have : ρ ^ η ≤ τ₀ ^ η := Real.rpow_le_rpow_of_nonpos hτ₀ hρτ hη0.le
                simp only [hL₀]; nlinarith
              have hd := ih ρ ⟨hρ.1, hρ.2.trans hr.2⟩ y'
              calc (a₀ * ρ ^ η + b₀) * |d ρ y'| ≤ L₀ * (B₁ / 2 ^ j) :=
                    mul_le_mul hℓ hd (abs_nonneg _) hL₀0
                _ = g ρ := by simp [hg, hK, not_le.1 hρt])
          refine hb.trans ?_
          rw [hg, integral_indicator_Ioi_const K ht₁.le (not_le.1 hrt).le]
          have hr1 : r - t₁ ≤ δ := by
            have := hr.2.trans (min_le_right _ _); linarith
          calc K * (r - t₁) ≤ K * δ := mul_le_mul_of_nonneg_left hr1 hK0
            _ = (δ * L₀) * (B₁ / 2 ^ j) := by rw [hK]; ring
            _ ≤ (1 / 2) * (B₁ / 2 ^ j) := mul_le_mul_of_nonneg_right hδL (by positivity)
            _ = B₁ / 2 ^ (j + 1) := by rw [pow_succ]; ring
  intro r hr y
  exact eq_zero_of_halving fun k => key k r hr y

/-- **Weighted Gronwall uniqueness** for the singular integral inequality. -/
theorem scalar_uniqueness (hη₁ : -2 / 3 < η) (hη0 : η < 0) (ha₀ : 0 ≤ a₀) (hb₀ : 0 ≤ b₀)
    (hB : 0 ≤ B) (h1 : ∀ t ∈ Ioc 0 T, ∀ x, |d t x| ≤ B * t ^ (η / 2))
    (h2 : SingularGronwall η a₀ b₀ T d) : ∀ t ∈ Ioc 0 T, ∀ x, d t x = 0 := by
  obtain ⟨τ₀, hτ₀, hsmall⟩ := exists_small_weight hη₁ hη0 (a₀ := a₀) (b₀ := b₀)
  set L₀ := a₀ * τ₀ ^ η + b₀ with hL₀
  have hL₀0 : 0 ≤ L₀ := add_nonneg (mul_nonneg ha₀ (Real.rpow_nonneg hτ₀.le _)) hb₀
  set δ := 1 / (2 * (L₀ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδL : δ * L₀ ≤ 1 / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hstep : ∀ n : ℕ, ∀ r ∈ Ioc 0 (min T (τ₀ + n * δ)), ∀ y, d r y = 0 := by
    intro n
    induction n with
    | zero =>
        intro r hr y
        have := sU_stepA_zero hη₁ hη0 h1 h2 hsmall ha₀ hb₀ hB r (by
          simpa [min_comm] using hr) y
        exact this
    | succ n ih =>
        by_cases hTn : T ≤ τ₀ + n * δ
        · intro r hr y
          refine ih r ⟨hr.1, ?_⟩ y
          have h1' : min T (τ₀ + (n + 1 : ℕ) * δ) = T := by
            refine min_eq_left ?_
            push_cast; nlinarith
          rw [h1'] at hr
          rw [min_eq_left hTn]
          exact hr.2
        · have hlt : τ₀ + n * δ < T := not_le.1 hTn
          have ht₁ : min T (τ₀ + n * δ) = τ₀ + n * δ := min_eq_right hlt.le
          have := sU_stepB hη₁ hη0 h1 h2 ha₀ hb₀ hB hτ₀ hδL (t₁ := τ₀ + n * δ)
            (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) (by rw [← ht₁]; exact ih)
          intro r hr y
          refine this r ?_ y
          have e : τ₀ + n * δ + δ = τ₀ + ((n + 1 : ℕ) : ℝ) * δ := by push_cast; ring
          rwa [e]
  intro t ht x
  obtain ⟨n, hn⟩ := exists_nat_ge ((T - τ₀) / δ)
  have hTn : T ≤ τ₀ + n * δ := by
    have := (div_le_iff₀ hδpos).1 hn
    linarith
  exact hstep n t ⟨ht.1, ht.2.trans (by rw [min_eq_left hTn])⟩ x

end RegularityStructures.Phi43

end
