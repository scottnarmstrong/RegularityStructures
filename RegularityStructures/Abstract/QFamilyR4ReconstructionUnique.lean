/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.QFamilyR4Uniqueness
public import RegularityStructures.Abstract.ReconstructionR4

/-!
# Hairer's (3.3) characterises the reconstruction on `ℝ⁴`

For the auxiliary semigroup on `ℝ⁴`, a model `M` with `|(Q_t Π_x e_i)(x)| ≤ C_Π t^{deg i/4}`, all
homogeneities below `γ` larger than `-4`, `γ > 0`, and `f ∈ D^γ`:

* `Model.besov_reconstruct`, `Model.measurable_reconstruct`: `Rf` is an admissible `Q`-family
  (Besov exponent `r4BesovExponent 𝒯 γ = min(0, min_{deg i < γ} deg i) > -4`);
* `Model.eq_reconstruct_of_abs_pairing_le` (**Hairer's uniqueness**, [Hai14, Theorem 3.10]: "if
  `γ > 0`, then the bound (3.3) defines `Rf` uniquely"): an admissible `Q`-family `Λ` with
  `|⟨Λ − Π_x f(x), φ^λ_x⟩| ≤ C λ^γ` for all `0 < λ ≤ 1` and `x`, for one `φ ∈ B^4` with
  `∫ φ ≠ 0`, is `Rf`;
* `Model.abs_sub_le_of_abs_pairing_le` (**(3.3) ⟹ `Q`-form**) and
  `Model.abs_pairing_le_of_abs_sub_le` (**`Q`-form ⟹ (3.3)**), and the equivalences
  `Model.eq_reconstruct_iff_abs_pairing_le`, `Model.exists_abs_pairing_le_iff_exists_abs_sub_le`.

Source: [Hai14, Theorem 3.10 and (3.3)].
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Besov exponent of the reconstruction: `min(0, min_{deg i < γ} deg i)`. -/
def r4BesovExponent (𝒯 : RegularityStructure ι) (γ : ℝ) : ℝ :=
  (insert 0 (𝒯.degreesBelow γ)).min' (Finset.insert_nonempty _ _)

end RegularityStructures

end

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem r4BesovExponent_nonpos (𝒯 : RegularityStructure ι) (γ : ℝ) :
    r4BesovExponent 𝒯 γ ≤ 0 :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem r4BesovExponent_le_deg (𝒯 : RegularityStructure ι) {γ : ℝ} {i : ι}
    (hi : 𝒯.deg i < γ) : r4BesovExponent 𝒯 γ ≤ 𝒯.deg i :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem ((𝒯.mem_degreesBelow).2 ⟨i, hi, rfl⟩))

theorem neg_four_lt_r4BesovExponent (𝒯 : RegularityStructure ι) {γ : ℝ}
    (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i) : -4 < r4BesovExponent 𝒯 γ := by
  refine (Finset.lt_min'_iff _ _).2 fun a ha => ?_
  rcases Finset.mem_insert.1 ha with rfl | ha
  · norm_num
  · obtain ⟨i, hi, rfl⟩ := (𝒯.mem_degreesBelow).1 ha
    exact hdeg i hi

namespace Model

variable {𝒯 : RegularityStructure ι} (M : Model 𝒯 parabolicSemigroup) {γ CPi Cf : ℝ}
  {f : ParabolicSpace → ι → ℝ}

/-- The reconstruction is of Besov type with exponent `r4BesovExponent 𝒯 γ`. -/
theorem besov_reconstruct (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi)
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf) :
    ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |M.reconstruct f u y| ≤
      (Fintype.card ι + modelReconstructionConst 𝒯 parabolicSemigroup γ) * CPi * Cf *
        u ^ (r4BesovExponent 𝒯 γ / 4) :=
  fun _ hu y => M.abs_reconstruct_le hγ hPi hCPi hf hfb hCf (r4BesovExponent_nonpos 𝒯 γ)
    (fun _ hi => r4BesovExponent_le_deg 𝒯 hi) hu y

theorem measurable_reconstruct (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi)
    (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f) (hCf : 0 ≤ Cf)
    {u : ℝ} (hu : 0 < u) : Measurable (M.reconstruct f u) :=
  parabolicSemigroup.measurable_reconstruct (M.isGerm_germ hPi hf) hγ
    (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha) (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hCf hCPi)) (M.isCoherent_germ hPi hCPi hf hfb hCf) hu

/-- **Hairer's uniqueness on `ℝ⁴`** ([Hai14, Theorem 3.10]: for `γ > 0` the bound (3.3) defines
`Rf` uniquely): an admissible `Q`-family `Λ` with `|⟨Λ − Π_x f(x), φ^λ_x⟩| ≤ C λ^γ` for all
`0 < λ ≤ 1` and all `x`, for one `φ ∈ B^4` with `∫ φ ≠ 0`, is the reconstruction `Rf`. -/
theorem eq_reconstruct_of_abs_pairing_le (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {Λ : ℝ → ParabolicSpace → ℝ} (hΛ : Λ ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α CΛ : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ CΛ * u ^ (α / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) (hφ0 : ∫ w, φ w ≠ 0) {C₃ : ℝ}
    (h33 : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, |parabolicSemigroup.pairing
      (fun t y => Λ t y - M.regPi x (f x) t y) (rescaledTestFunction φ c x)| ≤ C₃ * c ^ γ) :
    Λ = M.reconstruct f := by
  have hR := M.reconstruct_mem hγ hPi hCPi hf hfb hCf
  have hRm := fun u (hu : 0 < u) => M.measurable_reconstruct hγ hPi hCPi hf hfb hCf hu
  have hRb := M.besov_reconstruct hγ hPi hCPi hf hfb hCf
  have hαR := neg_four_lt_r4BesovExponent 𝒯 hdeg
  have hD : Λ - M.reconstruct f ∈ parabolicSemigroup.distributions :=
    parabolicSemigroup.distributions.sub_mem hΛ hR
  have hDm : ∀ u, 0 < u → Measurable ((Λ - M.reconstruct f) u) :=
    fun u hu => (hΛm u hu).sub (hRm u hu)
  have hDb := besov_sub hb hRb
  set cR := r4ReconstructionConst 𝒯 γ * CPi * Cf with hcR
  have key : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, |parabolicSemigroup.pairing (Λ - M.reconstruct f)
      (rescaledTestFunction φ c x)| ≤ (C₃ + cR) * c ^ γ := by
    intro c hc x
    obtain ⟨hT, hTb⟩ := M.abs_pairing_rescaledTestFunction_le hγ hPi hCPi hf hfb hCf hdeg hφ
      hc.1 hc.2 x
    have hTD := tendsto_integral_rescaledTestFunction hD hDm (lt_min hα hαR) hDb hφ hc.1 x
    -- the regularisations of `Rf − Π_x f(x)` paired with `φ^c_x` are integrable for `s ≤ 1`
    have hloc := M.isLocalOrder_reconstructSubAt hγ hPi hCPi hf hfb hCf x
    have hL : parabolicSemigroup.LocalData (M.reconstructSubAt f x) x γ
        (insert γ (𝒯.degreesBelow γ))
        ((modelReconstructionConst 𝒯 parabolicSemigroup γ + Fintype.card ι) * CPi * Cf) :=
      ⟨M.reconstructSubAt_mem hγ hPi hCPi hf hfb hCf x,
        fun u hu => M.measurable_reconstructSubAt hγ hPi hCPi hf hfb hCf x hu,
        mul_nonneg (mul_nonneg (add_nonneg (modelReconstructionConst_nonneg 𝒯 _ hγ.le)
          (Nat.cast_nonneg _)) hCPi) hCf,
        fun a ha => by
          rcases Finset.mem_insert.1 ha with rfl | ha
          · exact le_rfl
          · exact (𝒯.lt_of_mem_degreesBelow ha).le,
        hloc⟩
    have hsum : Tendsto (fun s => ∫ y, (Λ s y - M.regPi x (f x) s y) *
        rescaledTestFunction φ c x y) (𝓝[>] 0)
        (𝓝 (parabolicSemigroup.pairing (Λ - M.reconstruct f) (rescaledTestFunction φ c x) +
          parabolicSemigroup.pairing (M.reconstructSubAt f x) (rescaledTestFunction φ c x))) := by
      refine (hTD.add hT).congr' ?_
      filter_upwards [Ioc_mem_nhdsGT one_pos] with s hs
      have i1 := integrable_mul_of_besov hD hDm hDb (integrable_rescaledTestFunction hφ hc.1 x)
        hs.1
      have i2 := hL.integrable_mul hs (isSupported_rescaledTestFunction hφ hc.1 x)
      rw [← integral_add i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Pi.sub_apply, reconstructSubAt]
      ring
    have hp := parabolicSemigroup.pairing_eq_of_tendsto hsum
    have h1 := h33 c hc x
    rw [hp] at h1
    calc |parabolicSemigroup.pairing (Λ - M.reconstruct f) (rescaledTestFunction φ c x)|
        = |(parabolicSemigroup.pairing (Λ - M.reconstruct f) (rescaledTestFunction φ c x) +
            parabolicSemigroup.pairing (M.reconstructSubAt f x) (rescaledTestFunction φ c x)) -
            parabolicSemigroup.pairing (M.reconstructSubAt f x) (rescaledTestFunction φ c x)| := by
          congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ C₃ * c ^ γ + cR * c ^ γ := add_le_add h1 hTb
      _ = (C₃ + cR) * c ^ γ := by ring
  have hε : Tendsto (fun c : ℝ => (C₃ + cR) * c ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_rpow_const hγ.le).const_mul (C₃ + cR)).tendsto 0
    rw [Real.zero_rpow hγ.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact sub_eq_zero.1 (eq_zero_of_abs_pairing_rescaledTestFunction_le hD hDm (lt_min hα hαR)
    hDb hφ hφ0 hε key)

/-- **(3.3) implies the `Q`-form bound**: an admissible `Q`-family satisfying the
test-function bound (3.3) satisfies `|Λ_t(x) − (Q_t Π_x f(x))(x)| ≤ c C_Π C_f t^{γ/4}` for
`0 < t ≤ 1`, with the constant of the reconstruction theorem. -/
theorem abs_sub_le_of_abs_pairing_le (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {Λ : ℝ → ParabolicSpace → ℝ} (hΛ : Λ ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α CΛ : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ CΛ * u ^ (α / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) (hφ0 : ∫ w, φ w ≠ 0) {C₃ : ℝ}
    (h33 : ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, |parabolicSemigroup.pairing
      (fun t y => Λ t y - M.regPi x (f x) t y) (rescaledTestFunction φ c x)| ≤ C₃ * c ^ γ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : ParabolicSpace) :
    |Λ t x - M.regPi x (f x) t x| ≤
      modelReconstructionConst 𝒯 parabolicSemigroup γ * CPi * Cf * t ^ (γ / 4) := by
  rw [M.eq_reconstruct_of_abs_pairing_le hγ hPi hCPi hf hfb hCf hdeg hΛ hΛm hα hb hφ hφ0 h33]
  exact M.abs_reconstruct_sub_le hγ hPi hCPi hf hfb hCf ht x

/-- **The `Q`-form bound implies (3.3)**: a `Q`-family with
`|Λ_t(x) − (Q_t Π_x f(x))(x)| ≤ C' t^{γ/4}` (`0 < t ≤ 1`) satisfies, for every `φ ∈ B^4`,
`0 < λ ≤ 1` and `x`, that `⟨Λ − Π_x f(x), φ^λ_x⟩` exists and is at most
`r4ReconstructionConst 𝒯 γ · C_Π C_f λ^γ` in absolute value. -/
theorem abs_pairing_le_of_abs_sub_le (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {Λ : ℝ → ParabolicSpace → ℝ} (hΛ : Λ ∈ parabolicSemigroup.distributions) {C' : ℝ}
    (hQ : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |Λ t x - M.regPi x (f x) t x| ≤ C' * t ^ (γ / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1)
    (x : ParabolicSpace) :
    Tendsto (fun s => ∫ y, (Λ s y - M.regPi x (f x) s y) * rescaledTestFunction φ c x y)
        (𝓝[>] 0) (𝓝 (parabolicSemigroup.pairing (fun t y => Λ t y - M.regPi x (f x) t y)
          (rescaledTestFunction φ c x))) ∧
      |parabolicSemigroup.pairing (fun t y => Λ t y - M.regPi x (f x) t y)
        (rescaledTestFunction φ c x)| ≤ r4ReconstructionConst 𝒯 γ * CPi * Cf * c ^ γ := by
  have e := M.eq_reconstruct hγ hPi hCPi hf hfb hCf hΛ hQ
  subst e
  exact M.abs_pairing_rescaledTestFunction_le hγ hPi hCPi hf hfb hCf hdeg hφ hc.1 hc.2 x

/-- **(3.3) characterises `Rf` among admissible `Q`-families** ([Hai14, Theorem 3.10]). -/
theorem eq_reconstruct_iff_abs_pairing_le (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {Λ : ℝ → ParabolicSpace → ℝ} (hΛ : Λ ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α CΛ : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ CΛ * u ^ (α / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) (hφ0 : ∫ w, φ w ≠ 0) :
    Λ = M.reconstruct f ↔ ∃ C₃, ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, |parabolicSemigroup.pairing
      (fun t y => Λ t y - M.regPi x (f x) t y) (rescaledTestFunction φ c x)| ≤ C₃ * c ^ γ := by
  refine ⟨fun e => ⟨r4ReconstructionConst 𝒯 γ * CPi * Cf, fun c hc x => ?_⟩,
    fun ⟨C₃, h33⟩ => M.eq_reconstruct_of_abs_pairing_le hγ hPi hCPi hf hfb hCf hdeg hΛ hΛm hα hb
      hφ hφ0 h33⟩
  subst e
  exact (M.abs_pairing_rescaledTestFunction_le hγ hPi hCPi hf hfb hCf hdeg hφ hc.1 hc.2 x).2

/-- **(3.3) and the `Q`-form bound are equivalent** for admissible `Q`-families. -/
theorem exists_abs_pairing_le_iff_exists_abs_sub_le (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {Λ : ℝ → ParabolicSpace → ℝ} (hΛ : Λ ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α CΛ : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ CΛ * u ^ (α / 4))
    {φ : ParabolicSpace → ℝ} (hφ : φ ∈ testFunctionClass 4) (hφ0 : ∫ w, φ w ≠ 0) :
    (∃ C₃, ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, |parabolicSemigroup.pairing
      (fun t y => Λ t y - M.regPi x (f x) t y) (rescaledTestFunction φ c x)| ≤ C₃ * c ^ γ) ↔
      ∃ C', ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |Λ t x - M.regPi x (f x) t x| ≤ C' * t ^ (γ / 4) := by
  refine ⟨fun ⟨_, h33⟩ => ⟨_, fun t ht x =>
      M.abs_sub_le_of_abs_pairing_le hγ hPi hCPi hf hfb hCf hdeg hΛ hΛm hα hb hφ hφ0 h33 ht x⟩,
    fun ⟨_, hQ⟩ => ⟨_, fun c hc x =>
      (M.abs_pairing_le_of_abs_sub_le hγ hPi hCPi hf hfb hCf hdeg hΛ hQ hφ hc x).2⟩⟩

/-- **Uniqueness with all test functions**: an admissible `Q`-family with
`|⟨Λ − Π_x f(x), φ^λ_x⟩| ≤ C λ^γ` uniformly over `φ ∈ B^4`, `0 < λ ≤ 1` and `x` (Hairer's form
of (3.3)) is `Rf`. -/
theorem eq_reconstruct_of_forall_abs_pairing_le (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) (hdeg : ∀ i, 𝒯.deg i < γ → -4 < 𝒯.deg i)
    {Λ : ℝ → ParabolicSpace → ℝ} (hΛ : Λ ∈ parabolicSemigroup.distributions)
    (hΛm : ∀ u, 0 < u → Measurable (Λ u)) {α CΛ : ℝ} (hα : -4 < α)
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ y, |Λ u y| ≤ CΛ * u ^ (α / 4)) {C₃ : ℝ}
    (h33 : ∀ φ ∈ testFunctionClass 4, ∀ c ∈ Ioc (0 : ℝ) 1, ∀ x, |parabolicSemigroup.pairing
      (fun t y => Λ t y - M.regPi x (f x) t y) (rescaledTestFunction φ c x)| ≤ C₃ * c ^ γ) :
    Λ = M.reconstruct f := by
  obtain ⟨φ, hφ, hφ0⟩ := exists_mem_testFunctionClass 4
  exact M.eq_reconstruct_of_abs_pairing_le hγ hPi hCPi hf hfb hCf hdeg hΛ hΛm hα hb hφ hφ0.ne'
    (h33 φ hφ)

end Model

end RegularityStructures

end
