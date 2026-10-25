/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Germ
public import RegularityStructures.Abstract.GermCoherence
public import RegularityStructures.Analysis.Semigroup.Reconstruction

/-!
# The reconstruction theorem

Let `γ > 0`, let `M = (Π, Γ)` be a model with `|(Q_t Π_x e_i)(x)| ≤ C_Π t^{deg i/ℓ}` and let
`f ∈ D^γ` with constant `C_f`. The reconstruction `Rf = M.reconstruct f` is the reconstruction of
the germ `F_y = Π_y f(y)` (`RegularisingSemigroup.reconstruct`). Then
([Hos25, Theorem 4.1] with `p = q = ∞`, `w = v = 1`; [Hai14, Theorem 3.10]):

* `Rf` is a distribution (`reconstruct_mem`);
* `|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f t^{γ/ℓ}` for `0 < t ≤ 1` (`abs_reconstruct_sub_le`),
  with `c = modelReconstructionConst 𝒯 K γ` depending only on `𝒯`, `K` and `γ`;
* `Rf` is the only distribution with such a bound (`eq_reconstruct`);
* `f ↦ Rf` is linear (`reconstruct_add`, `reconstruct_smul`);
* the local Lipschitz bound in the model (`abs_reconstruct_sub_reconstruct_le`):
  `|(Q_t (R¹f¹ − Π¹_x f¹(x) − R²f² + Π²_x f²(x)))(x)| ≤ c (C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||)
  t^{γ/ℓ}` ([Hos25, Theorem 4.1], second part; [Hai14, (3.4)]);
* the Besov bound `|(Q_t Rf)(x)| ≲ C_Π C_f t^{α/ℓ}` for `α ≤ min(0, deg)`
  (`abs_reconstruct_le`, [Hos25, (4.1)]).

`exists_reconstruction` packages existence, the bound and uniqueness with the constant chosen
before the model and the modelled distribution.

Source: [Hos25, Section 4], [Hai14, Section 3].
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

/-- The constant of the reconstruction theorem, `|ι| · c(K, γ, A_{<γ})`. -/
def modelReconstructionConst (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ)
    (γ : ℝ) : ℝ :=
  Fintype.card ι * K.reconstructionConst γ (𝒯.degreesBelow γ)

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The reconstruction `Rf` of a modelled distribution: the semigroup reconstruction of the germ
`y ↦ Π_y f(y)`. -/
def reconstruct (M : Model 𝒯 K) (f : E → ι → ℝ) : ℝ → E → ℝ :=
  K.reconstruct (M.germ f)

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

theorem RegularisingSemigroup.IsGerm.sub {K : RegularisingSemigroup E μ}
    {F G : E → ℝ → E → ℝ} (hF : K.IsGerm F) (hG : K.IsGerm G) :
    K.IsGerm (fun y => F y - G y) where
  mem y := K.distributions.sub_mem (hF.mem y) (hG.mem y)
  measurable_diag _ ht := (hF.measurable_diag ht).sub (hG.measurable_diag ht)
  bounded_diag _ ht := by
    obtain ⟨B, hB⟩ := hF.bounded_diag ht
    obtain ⟨B', hB'⟩ := hG.bounded_diag ht
    exact ⟨B + B', fun y => (abs_sub _ _).trans (add_le_add (hB y) (hB' y))⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modelReconstructionConst_nonneg (𝒯 : RegularityStructure ι)
    (K : RegularisingSemigroup E μ) {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ modelReconstructionConst 𝒯 K γ :=
  mul_nonneg (Nat.cast_nonneg _) (K.reconstructionConst_nonneg hγ _)

namespace Model

section Single

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} [SFinite μ]
  (M : Model 𝒯 K) {γ CPi Cf : ℝ} (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi)
  {f : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
  (hCf : 0 ≤ Cf)

include hγ hPi hCPi hf hfb hCf

/-- `Rf` is a distribution. -/
theorem reconstruct_mem : M.reconstruct f ∈ K.distributions :=
  K.reconstruct_mem (M.isGerm_germ hPi hf) hγ (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCf hCPi)) (M.isCoherent_germ hPi hCPi hf hfb hCf)

/-- **Reconstruction bound** [Hos25, (4.2)], [Hai14, (3.3)]:
`|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f t^{γ/ℓ}` for `0 < t ≤ 1`. -/
theorem abs_reconstruct_sub_le {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |M.reconstruct f t x - M.regPi x (f x) t x| ≤
      modelReconstructionConst 𝒯 K γ * CPi * Cf * t ^ (γ / K.order) := by
  have h := K.abs_reconstruct_sub_diag_le (M.isGerm_germ hPi hf) hγ
    (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCf hCPi))
    (M.isCoherent_germ hPi hCPi hf hfb hCf) ht x
  calc |M.reconstruct f t x - M.regPi x (f x) t x|
      ≤ K.reconstructionConst γ (𝒯.degreesBelow γ) * (Fintype.card ι * (Cf * CPi)) *
          t ^ (γ / K.order) := h
    _ = modelReconstructionConst 𝒯 K γ * CPi * Cf * t ^ (γ / K.order) := by
        rw [modelReconstructionConst]
        ring

/-- **Uniqueness**: a distribution `Λ` with `|(Q_t (Λ − Π_x f(x)))(x)| ≤ C' t^{γ/ℓ}` is `Rf`. -/
theorem eq_reconstruct {Λ : ℝ → E → ℝ} (hΛ : Λ ∈ K.distributions) {C' : ℝ}
    (hb : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |Λ t x - M.regPi x (f x) t x| ≤ C' * t ^ (γ / K.order)) :
    Λ = M.reconstruct f :=
  K.eq_reconstruct (M.isGerm_germ hPi hf) hγ (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCf hCPi)) (M.isCoherent_germ hPi hCPi hf hfb hCf)
    hΛ hb

/-- **Besov bound** [Hos25, (4.1)]: if `α ≤ 0` and `α ≤ deg i` for all `deg i < γ`, then
`|(Q_t Rf)(x)| ≤ (|ι| + c) C_Π C_f t^{α/ℓ}` for `0 < t ≤ 1`. -/
theorem abs_reconstruct_le {α : ℝ} (hα : α ≤ 0) (hαdeg : ∀ i, 𝒯.deg i < γ → α ≤ 𝒯.deg i)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |M.reconstruct f t x| ≤
      (Fintype.card ι + modelReconstructionConst 𝒯 K γ) * CPi * Cf * t ^ (α / K.order) := by
  have hB : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ y, |M.germ f y s y| ≤
      (Fintype.card ι * (Cf * CPi)) * s ^ (α / K.order) := by
    intro s hs y
    refine (M.abs_diag_germ_le hPi hf hfb hs y).trans ?_
    calc ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), Cf * CPi * s ^ (𝒯.deg j / K.order)
        ≤ ∑ _j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), Cf * CPi * s ^ (α / K.order) := by
          refine Finset.sum_le_sum fun j hj => ?_
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCf hCPi)
          exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2
            (div_le_div_of_nonneg_right (hαdeg j (Finset.mem_filter.1 hj).2) K.order_pos.le)
      _ = (Finset.univ.filter (fun j => 𝒯.deg j < γ)).card * (Cf * CPi * s ^ (α / K.order)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card ι * (Cf * CPi * s ^ (α / K.order)) := by
          refine mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) ?_
          exact mul_nonneg (mul_nonneg hCf hCPi) (Real.rpow_nonneg hs.1.le _)
      _ = (Fintype.card ι * (Cf * CPi)) * s ^ (α / K.order) := by ring
  have h := K.abs_reconstruct_le (M.isGerm_germ hPi hf) hγ
    (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCf hCPi))
    (M.isCoherent_germ hPi hCPi hf hfb hCf) hα hB ht x
  calc |M.reconstruct f t x|
      ≤ (Fintype.card ι * (Cf * CPi) + K.reconstructionConst γ (𝒯.degreesBelow γ) *
          (Fintype.card ι * (Cf * CPi))) * t ^ (α / K.order) := h
    _ = (Fintype.card ι + modelReconstructionConst 𝒯 K γ) * CPi * Cf * t ^ (α / K.order) := by
        rw [modelReconstructionConst]
        ring



/-- **Local order of `Rf − Π_{x₀} f(x₀)` at `x₀`**: for `0 < u ≤ 1` and every `y`,
`|(Q_u (Rf − Π_{x₀} f(x₀)))(y)| ≤ C ∑_{a ∈ A ∪ {γ}} u^{a/ℓ} d(y, x₀)^{γ−a}` with
`C = (c + |ι|) C_Π C_f`. This is the input of the test-function form of the reconstruction bound. -/
theorem abs_reconstruct_sub_regPi_le {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (x₀ y : E) :
    |M.reconstruct f u y - M.regPi x₀ (f x₀) u y| ≤
      (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf *
        ∑ a ∈ insert γ (𝒯.degreesBelow γ), u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) := by
  have hγA : γ ∉ 𝒯.degreesBelow γ := fun h => lt_irrefl γ (𝒯.lt_of_mem_degreesBelow h)
  have h1 := M.abs_reconstruct_sub_le hγ hPi hCPi hf hfb hCf hu y
  have h2 := M.isCoherent_germ hPi hCPi hf hfb hCf hu x₀ y
  have hS : 0 ≤ ∑ a ∈ 𝒯.degreesBelow γ, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) :=
    Finset.sum_nonneg fun a _ =>
      mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
  have hu' : 0 ≤ u ^ (γ / K.order) := Real.rpow_nonneg hu.1.le _
  have hc := modelReconstructionConst_nonneg 𝒯 K hγ.le
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [Finset.sum_insert hγA, sub_self, Real.rpow_zero, mul_one]
  calc |M.reconstruct f u y - M.regPi x₀ (f x₀) u y|
      = |(M.reconstruct f u y - M.regPi y (f y) u y) +
          -(M.germ f x₀ u y - M.germ f y u y)| := by
        rw [germ, germ]
        ring_nf
    _ ≤ |M.reconstruct f u y - M.regPi y (f y) u y| + |M.germ f x₀ u y - M.germ f y u y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg]
    _ ≤ modelReconstructionConst 𝒯 K γ * CPi * Cf * u ^ (γ / K.order) +
          Fintype.card ι * (Cf * CPi) *
            ∑ a ∈ 𝒯.degreesBelow γ, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) :=
        add_le_add h1 h2
    _ ≤ (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf *
          (u ^ (γ / K.order) +
            ∑ a ∈ 𝒯.degreesBelow γ, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a)) := by
        have e1 : modelReconstructionConst 𝒯 K γ * CPi * Cf * u ^ (γ / K.order) ≤
            (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf * u ^ (γ / K.order) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hcard) hCPi) hCf) hu'
        have e2 : Fintype.card ι * (Cf * CPi) *
              ∑ a ∈ 𝒯.degreesBelow γ, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) ≤
            (modelReconstructionConst 𝒯 K γ + Fintype.card ι) * CPi * Cf *
              ∑ a ∈ 𝒯.degreesBelow γ, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a) := by
          rw [show (Fintype.card ι : ℝ) * (Cf * CPi) = Fintype.card ι * CPi * Cf by ring]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc) hCPi) hCf) hS
        rw [mul_add]
        exact add_le_add e1 e2

end Single

section Lipschitz

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} [SFinite μ]

/-- **Local Lipschitz bound in the model** ([Hos25, Theorem 4.1], [Hai14, (3.4)]): for two models
and `fⁱ ∈ D^γ(Mⁱ)`,
`|(Q_t (R¹f¹ − R²f²))(x) − (Q_t (Π¹_x f¹(x) − Π²_x f²(x)))(x)|
  ≤ c (C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||) t^{γ/ℓ}`. -/
theorem abs_reconstruct_sub_reconstruct_le (M₁ M₂ : Model 𝒯 K) {γ : ℝ} (hγ : 0 < γ)
    {CPi₁ CPi₂ CdPi Cf₁ Cf₂ Cdf : ℝ}
    (hPi₁ : M₁.PiBoundOn γ CPi₁ univ) (hPi₂ : M₂.PiBoundOn γ CPi₂ univ)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi univ) (hCPi₁ : 0 ≤ CPi₁) (hCPi₂ : 0 ≤ CPi₂)
    (hCdPi : 0 ≤ CdPi) {f₁ f₂ : E → ι → ℝ} (hf₁ : f₁ ∈ M₁.modelledDistributions γ)
    (hf₂ : f₂ ∈ M₂.modelledDistributions γ) (hfb₁ : M₁.ModelledBoundOn γ Cf₁ univ f₁)
    (hfb₂ : M₂.ModelledBoundOn γ Cf₂ univ f₂) (hdf : M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂)
    (hCf₁ : 0 ≤ Cf₁) (hCf₂ : 0 ≤ Cf₂) (hCdf : 0 ≤ Cdf) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (x : E) :
    |(M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x) -
        (M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x)| ≤
      modelReconstructionConst 𝒯 K γ * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (γ / K.order) := by
  have hA : ∀ a ∈ 𝒯.degreesBelow γ, a < γ := fun _ ha => 𝒯.lt_of_mem_degreesBelow ha
  have hG₁ := M₁.isGerm_germ hPi₁ hf₁
  have hG₂ := M₂.isGerm_germ hPi₂ hf₂
  have hc₁ := M₁.isCoherent_germ hPi₁ hCPi₁ hf₁ hfb₁ hCf₁
  have hc₂ := M₂.isCoherent_germ hPi₂ hCPi₂ hf₂ hfb₂ hCf₂
  have hcd := isCoherent_germ_sub M₁ M₂ hPi₂ hdPi hf₁ hf₂ hfb₁ hdf hCf₁ hCdf hCdPi hCPi₂
  have hsub := K.reconstruct_sub hG₁ hG₂ hγ hA
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCf₁ hCPi₁))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCf₂ hCPi₂)) hc₁ hc₂
  have h := K.abs_reconstruct_sub_diag_le (hG₁.sub hG₂) hγ hA
    (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg hCf₁ hCdPi) (mul_nonneg hCdf hCPi₂)))
    hcd ht x
  rw [hsub] at h
  calc |(M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x) -
        (M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x)|
      ≤ K.reconstructionConst γ (𝒯.degreesBelow γ) *
          (Fintype.card ι * (Cf₁ * CdPi + Cdf * CPi₂)) * t ^ (γ / K.order) := h
    _ = modelReconstructionConst 𝒯 K γ * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (γ / K.order) := by
        rw [modelReconstructionConst]
        ring

omit [SFinite μ] in
theorem germ_add (M : Model 𝒯 K) (f g : E → ι → ℝ) :
    M.germ (f + g) = fun y => M.germ f y + M.germ g y := by
  funext y t z
  simp [germ, M.regPi_add]

omit [SFinite μ] in
theorem germ_smul (M : Model 𝒯 K) (c : ℝ) (f : E → ι → ℝ) :
    M.germ (c • f) = fun y => c • M.germ f y := by
  funext y t z
  simp [germ, M.regPi_smul]

/-- Linearity of the reconstruction in the modelled distribution. -/
theorem reconstruct_add (M : Model 𝒯 K) {γ CPi : ℝ} (hγ : 0 < γ) (hPi : M.PiBoundOn γ CPi univ)
    (hCPi : 0 ≤ CPi) {f g : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ)
    (hg : g ∈ M.modelledDistributions γ) :
    M.reconstruct (f + g) = M.reconstruct f + M.reconstruct g := by
  obtain ⟨Cf, hfb⟩ := hf.2.2
  obtain ⟨Cg, hgb⟩ := hg.2.2
  have hfb' := hfb.mono M (le_max_left Cf 0)
  have hgb' := hgb.mono M (le_max_left Cg 0)
  rw [reconstruct, germ_add]
  exact K.reconstruct_add (M.isGerm_germ hPi hf) (M.isGerm_germ hPi hg) hγ
    (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_max_right _ _) hCPi))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_max_right _ _) hCPi))
    (M.isCoherent_germ hPi hCPi hf hfb' (le_max_right _ _))
    (M.isCoherent_germ hPi hCPi hg hgb' (le_max_right _ _))

theorem reconstruct_smul (M : Model 𝒯 K) {γ CPi : ℝ} (hγ : 0 < γ)
    (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi) {f : E → ι → ℝ}
    (hf : f ∈ M.modelledDistributions γ) (c : ℝ) :
    M.reconstruct (c • f) = c • M.reconstruct f := by
  obtain ⟨Cf, hfb⟩ := hf.2.2
  have hfb' := hfb.mono M (le_max_left Cf 0)
  rw [reconstruct, germ_smul]
  exact K.reconstruct_smul (M.isGerm_germ hPi hf) c hγ (fun _ ha => 𝒯.lt_of_mem_degreesBelow ha)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (le_max_right _ _) hCPi))
    (M.isCoherent_germ hPi hCPi hf hfb' (le_max_right _ _))


omit [SFinite μ] in
/-- The diagonal difference `|(Q_t (Π¹_x f¹(x) − Π²_x f²(x)))(x)|` is bounded by
`|ι| (C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||) t^{α/ℓ}` for `α ≤ deg i` (all `deg i < γ`),
`0 < t ≤ 1`. -/
theorem abs_regPi_sub_regPi_le (M₁ M₂ : Model 𝒯 K) {γ CPi₂ CdPi Cf₁ Cdf : ℝ}
    (hPi₂ : M₂.PiBoundOn γ CPi₂ univ) (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi univ)
    {f₁ f₂ : E → ι → ℝ} (hf₁ : f₁ ∈ M₁.modelledDistributions γ)
    (hf₂ : f₂ ∈ M₂.modelledDistributions γ) (hfb₁ : M₁.ModelledBoundOn γ Cf₁ univ f₁)
    (hdf : M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂) (hCf₁ : 0 ≤ Cf₁) (hCdf : 0 ≤ Cdf)
    (hCdPi : 0 ≤ CdPi) (hCPi₂ : 0 ≤ CPi₂) {α : ℝ} (hαdeg : ∀ i, 𝒯.deg i < γ → α ≤ 𝒯.deg i)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x| ≤
      Fintype.card ι * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order) := by
  rw [M₁.regPi_eq_sum_filter (hf₁.2.1 x), M₂.regPi_eq_sum_filter (hf₂.2.1 x),
    ← Finset.sum_sub_distrib]
  have hD : 0 ≤ Cf₁ * CdPi + Cdf * CPi₂ :=
    add_nonneg (mul_nonneg hCf₁ hCdPi) (mul_nonneg hCdf hCPi₂)
  have hta : 0 ≤ t ^ (α / K.order) := Real.rpow_nonneg ht.1.le _
  calc |∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
        (f₁ x j * M₁.regPi x (Pi.single j 1) t x - f₂ x j * M₂.regPi x (Pi.single j 1) t x)|
      ≤ ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
          (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hj : 𝒯.deg j < γ := (Finset.mem_filter.1 hj).2
        have htj : t ^ (𝒯.deg j / K.order) ≤ t ^ (α / K.order) :=
          Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
            (div_le_div_of_nonneg_right (hαdeg j hj) K.order_pos.le)
        have h1 := hfb₁.1 x (mem_univ x) j hj
        have h2 := hdPi j hj t ht x (mem_univ x)
        have h3 := hdf.1 x (mem_univ x) j hj
        have h4 := hPi₂ j hj t ht x (mem_univ x)
        have htj0 : 0 ≤ t ^ (𝒯.deg j / K.order) := Real.rpow_nonneg ht.1.le _
        have e : f₁ x j * M₁.regPi x (Pi.single j 1) t x - f₂ x j * M₂.regPi x (Pi.single j 1) t x
            = f₁ x j * (M₁.regPi x (Pi.single j 1) t x - M₂.regPi x (Pi.single j 1) t x) +
              (f₁ x j - f₂ x j) * M₂.regPi x (Pi.single j 1) t x := by ring
        rw [e]
        calc _ ≤ |f₁ x j| * |M₁.regPi x (Pi.single j 1) t x - M₂.regPi x (Pi.single j 1) t x| +
              |f₁ x j - f₂ x j| * |M₂.regPi x (Pi.single j 1) t x| := by
              rw [← abs_mul, ← abs_mul]
              exact abs_add_le _ _
          _ ≤ Cf₁ * (CdPi * t ^ (𝒯.deg j / K.order)) + Cdf * (CPi₂ * t ^ (𝒯.deg j / K.order)) :=
              add_le_add (mul_le_mul h1 h2 (abs_nonneg _) hCf₁)
                (mul_le_mul h3 h4 (abs_nonneg _) hCdf)
          _ = (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (𝒯.deg j / K.order) := by ring
          _ ≤ (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order) :=
              mul_le_mul_of_nonneg_left htj hD
    _ = (Finset.univ.filter (fun j => 𝒯.deg j < γ)).card *
          ((Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * ((Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _)
          (mul_nonneg hD hta)
    _ = _ := by ring

/-- **Besov form of the continuity in the model** ([Hos25, Theorem 4.1], first estimate of the
second part): `|(Q_t (R¹f¹ − R²f²))(x)| ≤ (|ι| + c)(C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||) t^{α/ℓ}`
for `α ≤ 0`, `α ≤ deg i` (all `deg i < γ`), `0 < t ≤ 1`. -/
theorem abs_reconstruct_sub_reconstruct_le_rpow (M₁ M₂ : Model 𝒯 K) {γ : ℝ} (hγ : 0 < γ)
    {CPi₁ CPi₂ CdPi Cf₁ Cf₂ Cdf : ℝ}
    (hPi₁ : M₁.PiBoundOn γ CPi₁ univ) (hPi₂ : M₂.PiBoundOn γ CPi₂ univ)
    (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi univ) (hCPi₁ : 0 ≤ CPi₁) (hCPi₂ : 0 ≤ CPi₂)
    (hCdPi : 0 ≤ CdPi) {f₁ f₂ : E → ι → ℝ} (hf₁ : f₁ ∈ M₁.modelledDistributions γ)
    (hf₂ : f₂ ∈ M₂.modelledDistributions γ) (hfb₁ : M₁.ModelledBoundOn γ Cf₁ univ f₁)
    (hfb₂ : M₂.ModelledBoundOn γ Cf₂ univ f₂) (hdf : M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂)
    (hCf₁ : 0 ≤ Cf₁) (hCf₂ : 0 ≤ Cf₂) (hCdf : 0 ≤ Cdf) {α : ℝ} (hα : α ≤ 0)
    (hαdeg : ∀ i, 𝒯.deg i < γ → α ≤ 𝒯.deg i) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x| ≤
      (Fintype.card ι + modelReconstructionConst 𝒯 K γ) * (Cf₁ * CdPi + Cdf * CPi₂) *
        t ^ (α / K.order) := by
  have h1 := abs_reconstruct_sub_reconstruct_le M₁ M₂ hγ hPi₁ hPi₂ hdPi hCPi₁ hCPi₂ hCdPi hf₁ hf₂
    hfb₁ hfb₂ hdf hCf₁ hCf₂ hCdf ht x
  have h2 := abs_regPi_sub_regPi_le M₁ M₂ hPi₂ hdPi hf₁ hf₂ hfb₁ hdf hCf₁ hCdf hCdPi hCPi₂
    hαdeg ht x
  have hD : 0 ≤ Cf₁ * CdPi + Cdf * CPi₂ :=
    add_nonneg (mul_nonneg hCf₁ hCdPi) (mul_nonneg hCdf hCPi₂)
  have h3 : t ^ (γ / K.order) ≤ t ^ (α / K.order) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
      (div_le_div_of_nonneg_right (hα.trans hγ.le) K.order_pos.le)
  have h4 : modelReconstructionConst 𝒯 K γ * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (γ / K.order) ≤
      modelReconstructionConst 𝒯 K γ * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg (modelReconstructionConst_nonneg 𝒯 K hγ.le) hD)
  calc |M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x|
      = |((M₁.reconstruct f₁ t x - M₂.reconstruct f₂ t x) -
          (M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x)) +
          (M₁.regPi x (f₁ x) t x - M₂.regPi x (f₂ x) t x)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ modelReconstructionConst 𝒯 K γ * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order) +
          Fintype.card ι * (Cf₁ * CdPi + Cdf * CPi₂) * t ^ (α / K.order) :=
        add_le_add (h1.trans h4) h2
    _ = _ := by ring

end Lipschitz

/-- **The reconstruction theorem** [Hos25, Theorem 4.1], [Hai14, Theorem 3.10], with the constant
chosen before the model and the modelled distribution: for `γ > 0` there is `c = c(𝒯, K, γ)` such
that for every model `M` with `‖Π‖ ≤ C_Π` and every `f ∈ D^γ` with `|||f||| ≤ C_f`, the
reconstruction `Rf` is a distribution, `|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f t^{γ/ℓ}` for
`0 < t ≤ 1`, and `Rf` is the only distribution with a bound of this form. -/
theorem exists_reconstruction (𝒯 : RegularityStructure ι) (K : RegularisingSemigroup E μ)
    [SFinite μ] {γ : ℝ} (hγ : 0 < γ) :
    ∃ c, 0 ≤ c ∧ ∀ (M : Model 𝒯 K) ⦃CPi Cf : ℝ⦄ ⦃f : E → ι → ℝ⦄,
      M.PiBoundOn γ CPi univ → 0 ≤ CPi → f ∈ M.modelledDistributions γ →
      M.ModelledBoundOn γ Cf univ f → 0 ≤ Cf →
      M.reconstruct f ∈ K.distributions ∧
      (∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |M.reconstruct f t x - M.regPi x (f x) t x| ≤ c * CPi * Cf * t ^ (γ / K.order)) ∧
      ∀ Λ ∈ K.distributions, (∃ C', ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
        |Λ t x - M.regPi x (f x) t x| ≤ C' * t ^ (γ / K.order)) → Λ = M.reconstruct f :=
  ⟨modelReconstructionConst 𝒯 K γ, modelReconstructionConst_nonneg 𝒯 K hγ.le,
    fun M _ _ _ hPi hCPi hf hfb hCf =>
      ⟨M.reconstruct_mem hγ hPi hCPi hf hfb hCf,
        fun _ ht x => M.abs_reconstruct_sub_le hγ hPi hCPi hf hfb hCf ht x,
        fun _ hΛ ⟨_, hb⟩ => M.eq_reconstruct hγ hPi hCPi hf hfb hCf hΛ hb⟩⟩

end Model

end RegularityStructures

end
