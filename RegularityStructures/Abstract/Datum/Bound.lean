/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Datum.BoundAux
public import RegularityStructures.Abstract.Datum.LiftCoeff
public import RegularityStructures.Abstract.Datum.SeqTaylor

/-!
# The increment of the Taylor lift

For `F` smooth on `{t > 0}` with `|D^k F| ≤ K_k A t^{(η - |k|_𝔰)/2}` for `t ≤ 1`, the coefficient
`l` of `f(y) - Γ_{yx} f(x)` (with `f = liftOf P γ₀ F`) is `(D^l F(y) - T_x^{<γ₀ - |l|}(D^l F)(y)) / l!`,
the Taylor remainder of `D^l F`. It is bounded by
`C A ρ₀^{η - γ₀} ‖y - x‖_𝔰^{γ₀ - |l|_𝔰}` whenever `‖y - x‖_𝔰 ≤ ρ₀` and `ρ₀² ≤ x₀, y₀ ≤ 1`
(`coeff_increment_le`): the Taylor expansion is taken coordinate by coordinate (`seq_taylor`), the
terms of parabolic degree `≥ γ₀ - |l|` are bounded by the derivative bounds on the box between `x`
and `y`, whose time coordinates lie in `[ρ₀², 1]`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Datum

/-- The derivative bounds satisfied by `P_t a` for `a ∈ 𝒞^η`, `‖a‖_η ≤ A`. -/
structure DerivBound (η A : ℝ) (Kc : (Fin 4 → ℕ) → ℝ) (F : ParabolicSpace → ℝ) : Prop where
  smooth : SmoothPos F
  bound : ∀ (k : Fin 4 → ℕ) (z : ParabolicSpace), 0 < z.1 → z.1 ≤ 1 →
    |D k F z| ≤ Kc k * A * z.1 ^ ((η - (wt k : ℝ)) / 2)

/-- The constant of the increment bound. -/
def liftConst (N : ℕ) (Kc : (Fin 4 → ℕ) → ℝ) : ℝ :=
  ((N : ℝ) ^ 4 + (N : ℝ) ^ 3 + (N : ℝ) ^ 2 + N + 1) * ∑ k ∈ box (2 * N), Kc k

end RegularityStructures.Datum

end

public section

open scoped ContDiff
open Set

namespace RegularityStructures.Datum

theorem DerivBound.bound_rho {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F : ParabolicSpace → ℝ}
    (hF : DerivBound η A Kc F) (hη : η < 0) {ρ₀ : ℝ} (hρ : 0 < ρ₀) (k : Fin 4 → ℕ)
    {w : ParabolicSpace} (hw : ρ₀ ^ 2 ≤ w.1) (hw1 : w.1 ≤ 1) (hKA : 0 ≤ Kc k * A) :
    |D k F w| ≤ Kc k * A * ρ₀ ^ (η - (wt k : ℝ)) := by
  have hpos : 0 < w.1 := lt_of_lt_of_le (by positivity) hw
  refine (hF.bound k w hpos hw1).trans (mul_le_mul_of_nonneg_left ?_ hKA)
  exact rpow_half_le hρ hw (by linarith [(Nat.cast_nonneg (wt k) : (0 : ℝ) ≤ wt k)])

theorem sum_range_le_mul {n : ℕ} {f : ℕ → ℝ} {θ : ℝ} (hf : ∀ a ∈ Finset.range n, f a ≤ θ) :
    ∑ a ∈ Finset.range n, f a ≤ n * θ := by
  calc ∑ a ∈ Finset.range n, f a ≤ ∑ _a ∈ Finset.range n, θ := Finset.sum_le_sum hf
    _ = n * θ := by simp

/-- A single term of the Taylor remainders: a monomial of parabolic degree `≥ μ` times the
derivative bound. -/
theorem monomial_mul_bound_le {ρ₀ r μ α : ℝ} {c : Fin 4 → ℝ} {w : ParabolicSpace}
    (hc : c = parabolicCoords w) (hr : r = parabolicNorm w) (hρ : 0 < ρ₀) (hrρ : r ≤ ρ₀)
    (hμ : 0 ≤ μ) (k : Fin 4 → ℕ) (hk : μ ≤ (wt k : ℝ)) {K : ℝ} (hK : 0 ≤ K) :
    (∏ i, |c i| ^ k i) * (K * ρ₀ ^ (α - (wt k : ℝ))) ≤ K * (ρ₀ ^ (α - μ) * r ^ μ) := by
  have hr0 : 0 ≤ r := hr ▸ parabolicNorm_nonneg w
  have h1 : ∏ i, |c i| ^ k i ≤ r ^ (wt k : ℝ) := by
    rw [Real.rpow_natCast, hc, hr]
    exact prod_abs_coord_pow_le w k
  have h2 := rpow_mul_rpow_le α hρ hr0 hrρ hμ hk
  calc (∏ i, |c i| ^ k i) * (K * ρ₀ ^ (α - (wt k : ℝ)))
      = K * ((∏ i, |c i| ^ k i) * ρ₀ ^ (α - (wt k : ℝ))) := by ring
    _ ≤ K * (r ^ (wt k : ℝ) * ρ₀ ^ (α - (wt k : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hρ.le _)
    _ ≤ K * (ρ₀ ^ (α - μ) * r ^ μ) := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        rw [mul_comm]
        exact h2

theorem stOfCoords_parabolicCoords (w : ParabolicSpace) : stOfCoords (parabolicCoords w) = w := by
  ext j
  · simp [stOfCoords, parabolicCoords]
  · fin_cases j <;> simp [stOfCoords, parabolicCoords]

theorem parabolicCoords_zero (w : ParabolicSpace) : parabolicCoords w 0 = w.1 := by
  simp [parabolicCoords]

theorem taylorCoeff_prod (c : Fin 4 → ℝ) (a : Fin 4 → ℕ) :
    taylorCoeff (c 3) (a 3) * (taylorCoeff (c 2) (a 2) * (taylorCoeff (c 1) (a 1) *
      taylorCoeff (c 0) (a 0))) = (∏ i, c i ^ a i) / multiFactorial a := by
  simp only [taylorCoeff, multiFactorial, Fin.prod_univ_four]
  field_simp

/-- **The increment of the Taylor lift.** -/
theorem coeff_increment_le {η A : ℝ} {Kc : (Fin 4 → ℕ) → ℝ} {F : ParabolicSpace → ℝ}
    (hF : DerivBound η A Kc F) (hη : η < 0) (hA : 0 ≤ A) (hKc : ∀ k, 0 ≤ Kc k)
    {N : ℕ} {γ₀ : ℝ} (hγN : γ₀ ≤ N) {x y : ParabolicSpace} {ρ₀ : ℝ} (hρ : 0 < ρ₀)
    (hx : ρ₀ ^ 2 ≤ x.1) (hy : ρ₀ ^ 2 ≤ y.1) (hx1 : x.1 ≤ 1) (hy1 : y.1 ≤ 1)
    (hr : parabolicNorm (y - x) ≤ ρ₀) (l : PolyIndex N) (hl : polyDeg N l < γ₀) :
    |liftCoeff N γ₀ F y l - polyTranslate (parabolicCoords (y - x)) (liftCoeff N γ₀ F x) l| ≤
      liftConst N Kc * A * ρ₀ ^ (η - γ₀) * parabolicNorm (y - x) ^ (γ₀ - polyDeg N l) := by
  set c := parabolicCoords (y - x) with hc
  set r := parabolicNorm (y - x) with hr_def
  set μ : ℝ := γ₀ - (wt ⇑l.1 : ℝ) with hμ
  have hlw : (0 : ℝ) ≤ (wt ⇑l.1 : ℝ) := Nat.cast_nonneg _
  have hμpos : 0 < μ := by
    rw [polyDeg_eq_wt] at hl
    linarith
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  set G := D ⇑l.1 F with hG
  have hGs : SmoothPos G := hF.smooth.D _
  have hy_eq : y = x + stOfCoords c := by
    rw [hc, stOfCoords_parabolicCoords]
    abel
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < x.1 + s * c 0 := by
    intro s hs
    rw [hc, parabolicCoords_zero, Prod.fst_sub]
    have : x.1 + s * (y.1 - x.1) = (1 - s) * x.1 + s * y.1 := by ring
    rw [this]
    have hx0 : 0 < x.1 := lt_of_lt_of_le (by positivity) hx
    have hy0 : 0 < y.1 := lt_of_lt_of_le (by positivity) hy
    rcases hs.1.eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hx0
    · have : 0 < s * y.1 := mul_pos h0 hy0
      nlinarith [hs.2, hx0]
  set B : (Fin 4 → ℕ) → ℝ := fun k => Kc (k + ⇑l.1) * A * ρ₀ ^ (η - (wt (k + ⇑l.1) : ℝ)) with hB
  have hBd : ∀ (k : Fin 4 → ℕ) (w : ParabolicSpace),
      (∃ s ∈ Icc (0 : ℝ) 1, w.1 = x.1 + s * c 0) → |D k G w| ≤ B k := by
    rintro k w ⟨s, hs, hw⟩
    have hw' : w.1 = (1 - s) * x.1 + s * y.1 := by
      rw [hw, hc, parabolicCoords_zero, Prod.fst_sub]; ring
    have hlo : ρ₀ ^ 2 ≤ w.1 := by
      rw [hw']
      nlinarith [hs.1, hs.2]
    have hhi : w.1 ≤ 1 := by
      rw [hw']
      nlinarith [hs.1, hs.2]
    rw [hG, ← D_add hF.smooth k ⇑l.1]
    exact hF.bound_rho hη hρ (k + ⇑l.1) hlo hhi (mul_nonneg (hKc _) hA)
  have hTay := seq_taylor hGs x c hpos N B hBd
  rw [← hy_eq] at hTay
  set θ : ℝ := (∑ k ∈ box (2 * N), Kc k) * A * ρ₀ ^ (η - γ₀) * r ^ μ with hθ
  -- the term bound
  have hterm : ∀ k : Fin 4 → ℕ, (∀ i, k i ≤ N) → μ ≤ (wt k : ℝ) →
      (∏ i, |c i| ^ k i) * B k ≤ θ := by
    intro k hk hμk
    have hmem : k + ⇑l.1 ∈ box (2 * N) := by
      rw [mem_box]
      intro i
      have := coord_lt_of_weight_lt l.2 i
      have h1 := hk i
      simp only [Pi.add_apply]
      omega
    have hKle : Kc (k + ⇑l.1) ≤ ∑ k ∈ box (2 * N), Kc k :=
      Finset.single_le_sum (f := Kc) (fun k _ => hKc k) hmem
    have hexp : η - (wt (k + ⇑l.1) : ℝ) = (η - (wt ⇑l.1 : ℝ)) - (wt k : ℝ) := by
      rw [wt_add]; push_cast; ring
    have h := monomial_mul_bound_le (c := c) (w := y - x) hc hr_def hρ hr (le_of_lt hμpos) k hμk
      (α := η - (wt ⇑l.1 : ℝ)) (mul_nonneg (hKc (k + ⇑l.1)) hA)
    have hexp2 : η - (wt ⇑l.1 : ℝ) - μ = η - γ₀ := by rw [hμ]; ring
    rw [hexp2] at h
    have hBk : B k = Kc (k + ⇑l.1) * A * ρ₀ ^ ((η - (wt ⇑l.1 : ℝ)) - (wt k : ℝ)) := by
      rw [hB]; simp only; rw [hexp]
    rw [hBk]
    refine h.trans ?_
    calc Kc (k + ⇑l.1) * A * (ρ₀ ^ (η - γ₀) * r ^ μ)
        ≤ (∑ k ∈ box (2 * N), Kc k) * A * (ρ₀ ^ (η - γ₀) * r ^ μ) := by
          gcongr
      _ = θ := by rw [hθ]; ring
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    have : 0 ≤ ∑ k ∈ box (2 * N), Kc k := Finset.sum_nonneg fun k _ => hKc k
    positivity
  have hμN : μ ≤ (N : ℝ) := by linarith
  -- the remainder
  have hN : (N : ℝ) = N := rfl
  have hRem : (∑ a3 ∈ Finset.range N, ∑ a2 ∈ Finset.range N, ∑ a1 ∈ Finset.range N,
        |c 3| ^ a3 * |c 2| ^ a2 * |c 1| ^ a1 * (B ![N, a1, a2, a3] * |c 0| ^ N) +
      ∑ a3 ∈ Finset.range N, ∑ a2 ∈ Finset.range N,
        |c 3| ^ a3 * |c 2| ^ a2 * (B ![0, N, a2, a3] * |c 1| ^ N) +
      ∑ a3 ∈ Finset.range N, |c 3| ^ a3 * (B ![0, 0, N, a3] * |c 2| ^ N) +
        B ![0, 0, 0, N] * |c 3| ^ N) ≤ ((N : ℝ) ^ 3 + (N : ℝ) ^ 2 + N + 1) * θ := by
    have t1 : ∀ a3 ∈ Finset.range N, ∀ a2 ∈ Finset.range N, ∀ a1 ∈ Finset.range N,
        |c 3| ^ a3 * |c 2| ^ a2 * |c 1| ^ a1 * (B ![N, a1, a2, a3] * |c 0| ^ N) ≤ θ := by
      intro a3 h3 a2 h2 a1 h1
      rw [Finset.mem_range] at h3 h2 h1
      have := hterm ![N, a1, a2, a3] (by intro i; fin_cases i <;> simp <;> omega)
        (by
          have : N ≤ wt ![N, a1, a2, a3] := by simp [wt]; omega
          exact hμN.trans (by exact_mod_cast this))
      simp only [Fin.prod_univ_four] at this
      simp at this
      linarith
    have t2 : ∀ a3 ∈ Finset.range N, ∀ a2 ∈ Finset.range N,
        |c 3| ^ a3 * |c 2| ^ a2 * (B ![0, N, a2, a3] * |c 1| ^ N) ≤ θ := by
      intro a3 h3 a2 h2
      rw [Finset.mem_range] at h3 h2
      have := hterm ![0, N, a2, a3] (by intro i; fin_cases i <;> simp <;> omega)
        (by
          have : N ≤ wt ![0, N, a2, a3] := by simp [wt]; omega
          exact hμN.trans (by exact_mod_cast this))
      simp only [Fin.prod_univ_four] at this
      simp at this
      linarith
    have t3 : ∀ a3 ∈ Finset.range N, |c 3| ^ a3 * (B ![0, 0, N, a3] * |c 2| ^ N) ≤ θ := by
      intro a3 h3
      rw [Finset.mem_range] at h3
      have := hterm ![0, 0, N, a3] (by intro i; fin_cases i <;> simp; omega)
        (by
          have : N ≤ wt ![0, 0, N, a3] := by simp [wt]
          exact hμN.trans (by exact_mod_cast this))
      simp only [Fin.prod_univ_four] at this
      simp at this
      linarith
    have t4 : B ![0, 0, 0, N] * |c 3| ^ N ≤ θ := by
      have := hterm ![0, 0, 0, N] (by intro i; fin_cases i <;> simp)
        (by
          have : N ≤ wt ![0, 0, 0, N] := by simp [wt]
          exact hμN.trans (by exact_mod_cast this))
      simp only [Fin.prod_univ_four] at this
      simp at this
      linarith
    have s1 : ∑ a3 ∈ Finset.range N, ∑ a2 ∈ Finset.range N, ∑ a1 ∈ Finset.range N,
        |c 3| ^ a3 * |c 2| ^ a2 * |c 1| ^ a1 * (B ![N, a1, a2, a3] * |c 0| ^ N) ≤
        (N : ℝ) ^ 3 * θ := by
      calc _ ≤ ∑ a3 ∈ Finset.range N, ∑ a2 ∈ Finset.range N, (N : ℝ) * θ :=
            Finset.sum_le_sum fun a3 h3 => Finset.sum_le_sum fun a2 h2 =>
              sum_range_le_mul fun a1 h1 => t1 a3 h3 a2 h2 a1 h1
        _ = (N : ℝ) ^ 3 * θ := by simp; ring
    have s2 : ∑ a3 ∈ Finset.range N, ∑ a2 ∈ Finset.range N,
        |c 3| ^ a3 * |c 2| ^ a2 * (B ![0, N, a2, a3] * |c 1| ^ N) ≤ (N : ℝ) ^ 2 * θ := by
      calc _ ≤ ∑ a3 ∈ Finset.range N, (N : ℝ) * θ :=
            Finset.sum_le_sum fun a3 h3 =>
              sum_range_le_mul fun a2 h2 => t2 a3 h3 a2 h2
        _ = (N : ℝ) ^ 2 * θ := by simp; ring
    have s3 : ∑ a3 ∈ Finset.range N, |c 3| ^ a3 * (B ![0, 0, N, a3] * |c 2| ^ N) ≤
        (N : ℝ) * θ := sum_range_le_mul t3
    linarith
  -- the main term
  have hmain : ∑ a3 ∈ Finset.range N, ∑ a2 ∈ Finset.range N, ∑ a1 ∈ Finset.range N,
      ∑ a0 ∈ Finset.range N, taylorCoeff (c 3) a3 * (taylorCoeff (c 2) a2 *
        (taylorCoeff (c 1) a1 * (taylorCoeff (c 0) a0 * D ![a0, a1, a2, a3] G x))) =
      ∑ a ∈ box N, (∏ i, c i ^ a i) / multiFactorial a * D a G x := by
    rw [← sum_nested_four N (fun a => (∏ i, c i ^ a i) / multiFactorial a * D a G x)]
    refine Finset.sum_congr rfl fun a3 _ => Finset.sum_congr rfl fun a2 _ =>
      Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a0 _ => ?_
    have := taylorCoeff_prod c ![a0, a1, a2, a3]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
    rw [← this]
    ring
  -- the high terms
  have hHigh : |∑ a ∈ (box N).filter (fun a => ¬ (wt a : ℝ) < μ),
      (∏ i, c i ^ a i) / multiFactorial a * D a G x| ≤ (N : ℝ) ^ 4 * θ := by
    have hterm2 : ∀ a ∈ (box N).filter (fun a => ¬ (wt a : ℝ) < μ),
        |(∏ i, c i ^ a i) / multiFactorial a * D a G x| ≤ θ := by
      intro a ha
      rw [Finset.mem_filter, mem_box] at ha
      have hBa : |D a G x| ≤ B a := hBd a x ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
      have hmf := one_le_multiFactorial a
      have h1 : |(∏ i, c i ^ a i) / multiFactorial a| ≤ ∏ i, |c i| ^ a i := by
        rw [abs_div, abs_of_pos (multiFactorial_pos a), Finset.abs_prod]
        simp only [abs_pow]
        exact div_le_self (Finset.prod_nonneg fun i _ => by positivity) hmf
      rw [abs_mul]
      refine le_trans (mul_le_mul h1 hBa (abs_nonneg _) (Finset.prod_nonneg fun i _ => by positivity))
        (hterm a (fun i => (ha.1 i).le) (not_lt.1 ha.2))
    calc _ ≤ ∑ a ∈ (box N).filter (fun a => ¬ (wt a : ℝ) < μ),
          |(∏ i, c i ^ a i) / multiFactorial a * D a G x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ (box N).filter (fun a => ¬ (wt a : ℝ) < μ), θ := Finset.sum_le_sum hterm2
      _ = ((box N).filter (fun a => ¬ (wt a : ℝ) < μ)).card * θ := by simp
      _ ≤ (N : ℝ) ^ 4 * θ := by
          refine mul_le_mul_of_nonneg_right ?_ hθ0
          have : ((box N).filter (fun a => ¬ (wt a : ℝ) < μ)).card ≤ N ^ 4 := by
            refine (Finset.card_filter_le _ _).trans ?_
            simp [box, Fintype.card_piFinset]
          exact_mod_cast this
  -- assembling
  have hsplit : ∑ a ∈ box N, (∏ i, c i ^ a i) / multiFactorial a * D a G x =
      ∑ a ∈ taylorIdx N μ, (∏ i, c i ^ a i) / multiFactorial a * D a G x +
        ∑ a ∈ (box N).filter (fun a => ¬ (wt a : ℝ) < μ),
          (∏ i, c i ^ a i) / multiFactorial a * D a G x :=
    (Finset.sum_filter_add_sum_filter_not (box N) (fun a => (wt a : ℝ) < μ) _).symm
  have hpoly : polyTranslate c (liftCoeff N γ₀ F x) l =
      (1 / multiFactorial ⇑l.1) *
        ∑ a ∈ taylorIdx N μ, (∏ i, c i ^ a i) / multiFactorial a * D a G x := by
    rw [polyTranslate_liftCoeff hF.smooth hγN c x l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : multiFactorial a ≠ 0 := (multiFactorial_pos a).ne'
    have h2 : multiFactorial ⇑l.1 ≠ 0 := (multiFactorial_pos _).ne'
    rw [hG]
    field_simp
  have hycoeff : liftCoeff N γ₀ F y l = G y / multiFactorial ⇑l.1 := by
    simp [liftCoeff, hl, hG]
  have hmf1 := one_le_multiFactorial ⇑l.1
  have hmfpos := multiFactorial_pos ⇑l.1
  rw [hpoly, hycoeff]
  have e1 : G y / multiFactorial ⇑l.1 - 1 / multiFactorial ⇑l.1 *
      ∑ a ∈ taylorIdx N μ, (∏ i, c i ^ a i) / multiFactorial a * D a G x =
      (1 / multiFactorial ⇑l.1) * (G y - ∑ a ∈ taylorIdx N μ,
        (∏ i, c i ^ a i) / multiFactorial a * D a G x) := by ring
  rw [e1, abs_mul, abs_of_pos (by positivity : 0 < 1 / multiFactorial ⇑l.1)]
  have e2 : G y - ∑ a ∈ taylorIdx N μ, (∏ i, c i ^ a i) / multiFactorial a * D a G x =
      (G y - ∑ a ∈ box N, (∏ i, c i ^ a i) / multiFactorial a * D a G x) +
        ∑ a ∈ (box N).filter (fun a => ¬ (wt a : ℝ) < μ),
          (∏ i, c i ^ a i) / multiFactorial a * D a G x := by
    rw [hsplit]; ring
  have hfin : |G y - ∑ a ∈ taylorIdx N μ, (∏ i, c i ^ a i) / multiFactorial a * D a G x| ≤
      ((N : ℝ) ^ 4 + (N : ℝ) ^ 3 + (N : ℝ) ^ 2 + N + 1) * θ := by
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [hmain] at hTay
    have := hTay.trans hRem
    linarith [this, hHigh]
  have hle : 1 / multiFactorial ⇑l.1 ≤ 1 := by
    rw [div_le_one hmfpos]; exact hmf1
  calc 1 / multiFactorial ⇑l.1 * |G y - ∑ a ∈ taylorIdx N μ,
        (∏ i, c i ^ a i) / multiFactorial a * D a G x|
      ≤ 1 * |G y - ∑ a ∈ taylorIdx N μ, (∏ i, c i ^ a i) / multiFactorial a * D a G x| :=
        mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ ≤ ((N : ℝ) ^ 4 + (N : ℝ) ^ 3 + (N : ℝ) ^ 2 + N + 1) * θ := by rw [one_mul]; exact hfin
    _ = liftConst N Kc * A * ρ₀ ^ (η - γ₀) * r ^ (γ₀ - polyDeg N l) := by
        rw [hθ, liftConst, polyDeg_eq_wt]
        ring

end RegularityStructures.Datum

end
