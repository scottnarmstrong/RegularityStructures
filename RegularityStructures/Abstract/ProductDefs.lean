/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration

/-!
# Products on a regularity structure

The algebraic layer of [Hai14, §4] in the graded-basis representation `T = ι → ℝ`:

* `lowerProj deg γ`: the projection `Q_{<γ} : T → T_{<γ}` onto the components of degree `< γ`;
* `RegularityStructure.GradedProduct 𝒯`: a bilinear map `⋆` on `T` with `T_α ⋆ T_β ⊂ T_{α+β}`
  [Hai14, Definition 4.1, first condition]; continuity is automatic in finite dimension
  [Hai14, Remark 4.3];
* `GradedProduct.IsUnital P u`: the basis vector `e_u` has degree `0` and is a two-sided unit,
  the second condition of [Hai14, Definition 4.1]. The theory of §4 never uses it
  ([Hai14, Remark 4.2]), so the results below are stated for graded products, which is more
  general;
* `GradedProduct.IsRegularPair P V W γ`: the pair of sectors `(V, W)` is `γ`-regular
  [Hai14, Definition 4.6]: `Γ (a ⋆ b) = Γ a ⋆ Γ b` for `Γ ∈ G`, `a ∈ V_α`, `b ∈ W_β`,
  `α + β < γ`;
* `GradedProduct.truncMul P γ f g`: the truncated pointwise product
  `(f ⋆_γ g)(x) = Q_{<γ} (f(x) ⋆ g(x))` of `T`-valued functions [Hai14, (4.1), (4.3)].

The main algebraic facts are the decomposition
`Q_{<γ} (a ⋆ b) = ∑_{m + n < γ} Q_m a ⋆ Q_n b` (`lowerProj_mul_eq_sum`) and, for a `γ`-regular
pair, `Γ Q_{<γ} (a ⋆ b) = ∑_{m + n < γ} Γ Q_m a ⋆ Γ Q_n b`
(`IsRegularPair.map_lowerProj_mul`), which is the identity behind [Hai14, (4.5)].

Source: [Hai14] = arXiv:1303.5113v4, §4.
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*}

/-- The projection `Q_{<γ} : T → T_{<γ}`, keeping the coordinates of degree `< γ`. -/
def lowerProj (deg : ι → ℝ) (γ : ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun τ i := if deg i < γ then τ i else 0
  map_add' τ σ := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c τ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

variable [Fintype ι] [DecidableEq ι]

namespace RegularityStructure

/-- A product on the model space `T` of `𝒯` [Hai14, Definition 4.1]: a bilinear map
`(a, b) ↦ a ⋆ b` with `T_α ⋆ T_β ⊂ T_{α+β}`. (Bilinear maps on finite-dimensional spaces are
continuous, [Hai14, Remark 4.3]; the unit condition is `GradedProduct.IsUnital`.) -/
structure GradedProduct (𝒯 : RegularityStructure ι) where
  /-- The product `a ⋆ b`. -/
  mul : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) →ₗ[ℝ] (ι → ℝ)
  mul_mem_homogeneousSubspace : ∀ (α β : ℝ) (a b : ι → ℝ), a ∈ homogeneousSubspace 𝒯.deg α →
    b ∈ homogeneousSubspace 𝒯.deg β → mul a b ∈ homogeneousSubspace 𝒯.deg (α + β)

namespace GradedProduct

variable {𝒯 : RegularityStructure ι}

/-- The pair of sectors `(V, W)` is `γ`-regular [Hai14, Definition 4.6]:
`Γ (a ⋆ b) = (Γ a) ⋆ (Γ b)` for every `Γ ∈ G`, `a ∈ V ∩ T_α`, `b ∈ W ∩ T_β` with `α + β < γ`. -/
def IsRegularPair (P : 𝒯.GradedProduct) (V W : Submodule ℝ (ι → ℝ)) (γ : ℝ) : Prop :=
  ∀ g ∈ 𝒯.group, ∀ α β : ℝ, α + β < γ → ∀ a ∈ V, a ∈ homogeneousSubspace 𝒯.deg α →
    ∀ b ∈ W, b ∈ homogeneousSubspace 𝒯.deg β →
      ((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (P.mul a b) =
        P.mul (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a)
          (((g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) b)

/-- The structure constants `(e_i ⋆ e_j)_k` of the product. -/
def coeff (P : 𝒯.GradedProduct) (i j k : ι) : ℝ :=
  P.mul (Pi.single i 1) (Pi.single j 1) k

/-- The size `∑_{i,j,k} |(e_i ⋆ e_j)_k|` of the product: a constant depending only on `𝒯` and
`⋆`. -/
def const (P : 𝒯.GradedProduct) : ℝ :=
  ∑ i, ∑ j, ∑ k, |P.coeff i j k|

/-- The truncated pointwise product `(f ⋆_γ g)(x) = Q_{<γ} (f(x) ⋆ g(x))` [Hai14, (4.3)]. -/
def truncMul (P : 𝒯.GradedProduct) {E : Type*} (γ : ℝ) (f g : E → ι → ℝ) : E → ι → ℝ :=
  fun x => lowerProj 𝒯.deg γ (P.mul (f x) (g x))

end GradedProduct

end RegularityStructure

end RegularityStructures

end

public section

namespace RegularityStructures

variable {ι : Type*}

section LowerProj

variable {deg : ι → ℝ} {γ : ℝ}

theorem lowerProj_apply (deg : ι → ℝ) (γ : ℝ) (τ : ι → ℝ) (i : ι) :
    lowerProj deg γ τ i = if deg i < γ then τ i else 0 :=
  rfl

theorem lowerProj_apply_of_lt {τ : ι → ℝ} {i : ι} (h : deg i < γ) :
    lowerProj deg γ τ i = τ i := by
  simp [lowerProj_apply, h]

theorem lowerProj_apply_of_le {τ : ι → ℝ} {i : ι} (h : γ ≤ deg i) :
    lowerProj deg γ τ i = 0 := by
  simp [lowerProj_apply, not_lt.2 h]

theorem abs_lowerProj_apply_le (τ : ι → ℝ) (i : ι) : |lowerProj deg γ τ i| ≤ |τ i| := by
  rw [lowerProj_apply]
  split_ifs
  · exact le_rfl
  · simp

theorem lowerProj_mem (τ : ι → ℝ) : lowerProj deg γ τ ∈ lowerSubspace deg γ :=
  fun _ hi => lowerProj_apply_of_le hi

/-- `Q_{<γ} τ = τ` if `τ ∈ T_α` with `α < γ`, and `Q_{<γ} τ = 0` if `γ ≤ α`. -/
theorem lowerProj_of_mem_homogeneousSubspace {α : ℝ} {τ : ι → ℝ}
    (h : τ ∈ homogeneousSubspace deg α) :
    lowerProj deg γ τ = if α < γ then τ else 0 := by
  funext i
  rw [lowerProj_apply]
  by_cases hi : deg i = α
  · rw [hi]
    split_ifs <;> rfl
  · rw [h i hi]
    split_ifs <;> simp [h i hi]

end LowerProj

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Graded subspaces are invariant under `Q_{<γ}`. -/
theorem lowerProj_mem_of_graded {deg : ι → ℝ} {V : Submodule ℝ (ι → ℝ)}
    (hV : ∀ α, ∀ a ∈ V, homogeneousProj deg α a ∈ V) (γ : ℝ) {a : ι → ℝ} (ha : a ∈ V) :
    lowerProj deg γ a ∈ V := by
  have h : lowerProj deg γ a =
      ∑ α ∈ (Finset.univ.image deg).filter (· < γ), homogeneousProj deg α a := by
    conv_lhs => rw [← sum_homogeneousProj deg a]
    rw [map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [lowerProj_of_mem_homogeneousSubspace (homogeneousProj_mem deg α a)]
  rw [h]
  exact Submodule.sum_mem _ fun α _ => hV α a ha

/-- `(g Q_m a)_i = ∑_{deg i' = m} a_{i'} (g e_{i'})_i`. -/
theorem apply_homogeneousProj_apply (deg : ι → ℝ) (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (m : ℝ)
    (a : ι → ℝ) (i : ι) :
    g (homogeneousProj deg m a) i =
      ∑ i', (if deg i' = m then a i' else 0) * g (Pi.single i' 1) i := by
  conv_lhs => rw [eq_sum_single (homogeneousProj deg m a)]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, homogeneousProj_apply]

/-- Coordinates of a sector of regularity `α` vanish below `α`. -/
theorem RegularityStructure.IsSector.apply_eq_zero_of_ofRegularity {𝒯 : RegularityStructure ι}
    {V : Submodule ℝ (ι → ℝ)} {α : ℝ} (hV : RegularityStructure.IsSector.OfRegularity 𝒯 V α)
    {a : ι → ℝ} (ha : a ∈ V) {i : ι} (hi : 𝒯.deg i < α) : a i = 0 := by
  have h := congrFun (hV (𝒯.deg i) hi a ha) i
  simpa [homogeneousProj_apply] using h

namespace RegularityStructure.GradedProduct

variable {𝒯 : RegularityStructure ι} (P : 𝒯.GradedProduct)

/-- `(a ⋆ b)_k = ∑_{i,j} a_i b_j (e_i ⋆ e_j)_k`. -/
theorem mul_apply_eq_sum (a b : ι → ℝ) (k : ι) :
    P.mul a b k = ∑ i, ∑ j, a i * b j * P.coeff i j k := by
  conv_lhs => rw [eq_sum_single a, eq_sum_single b]
  simp only [map_sum, map_smul, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, coeff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `(e_i ⋆ e_j)_k = 0` unless `deg k = deg i + deg j`. -/
theorem coeff_eq_zero {i j k : ι} (h : 𝒯.deg k ≠ 𝒯.deg i + 𝒯.deg j) : P.coeff i j k = 0 :=
  P.mul_mem_homogeneousSubspace _ _ _ _ (single_mem_homogeneousSubspace i 1)
    (single_mem_homogeneousSubspace j 1) k h

theorem const_nonneg : 0 ≤ P.const :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _

/-- The basic coordinate bound: if `|a_i| |b_j| ≤ X` whenever `deg i + deg j = deg k`, then
`|(a ⋆ b)_k| ≤ ‖⋆‖ X`. -/
theorem abs_mul_apply_le {a b : ι → ℝ} {k : ι} {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ i j, 𝒯.deg i + 𝒯.deg j = 𝒯.deg k → |a i| * |b j| ≤ X) :
    |P.mul a b k| ≤ P.const * X := by
  rw [mul_apply_eq_sum]
  have hterm : ∀ i j, |a i * b j * P.coeff i j k| ≤ X * |P.coeff i j k| := by
    intro i j
    by_cases hd : 𝒯.deg k = 𝒯.deg i + 𝒯.deg j
    · rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (h i j hd.symm) (abs_nonneg _)
    · simp [P.coeff_eq_zero hd]
  calc |∑ i, ∑ j, a i * b j * P.coeff i j k|
      ≤ ∑ i, ∑ j, |a i * b j * P.coeff i j k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, X * |P.coeff i j k| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = X * ∑ i, ∑ j, |P.coeff i j k| := by simp only [Finset.mul_sum]
    _ ≤ X * P.const := by
        refine mul_le_mul_of_nonneg_left ?_ hX
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.single_le_sum (f := fun k => |P.coeff i j k|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ k)
    _ = P.const * X := mul_comm _ _

/-- `a ⋆ b = ∑_{m, n} Q_m a ⋆ Q_n b`. -/
theorem mul_eq_sum_homogeneousProj (a b : ι → ℝ) :
    P.mul a b = ∑ m ∈ Finset.univ.image 𝒯.deg, ∑ n ∈ Finset.univ.image 𝒯.deg,
      P.mul (homogeneousProj 𝒯.deg m a) (homogeneousProj 𝒯.deg n b) := by
  conv_lhs => rw [← sum_homogeneousProj 𝒯.deg a, ← sum_homogeneousProj 𝒯.deg b]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

/-- `Q_{<γ} (a ⋆ b) = ∑_{m + n < γ} Q_m a ⋆ Q_n b` [Hai14, (4.3)]. -/
theorem lowerProj_mul_eq_sum (γ : ℝ) (a b : ι → ℝ) :
    lowerProj 𝒯.deg γ (P.mul a b) =
      ∑ m ∈ Finset.univ.image 𝒯.deg, ∑ n ∈ Finset.univ.image 𝒯.deg,
        if m + n < γ then P.mul (homogeneousProj 𝒯.deg m a) (homogeneousProj 𝒯.deg n b)
        else 0 := by
  rw [mul_eq_sum_homogeneousProj, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact lowerProj_of_mem_homogeneousSubspace (P.mul_mem_homogeneousSubspace _ _ _ _
    (homogeneousProj_mem _ _ _) (homogeneousProj_mem _ _ _))

/-- `g a ⋆ g b = ∑_{m, n} g Q_m a ⋆ g Q_n b` for any linear map `g`. -/
theorem mul_map_eq_sum (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (a b : ι → ℝ) :
    P.mul (g a) (g b) = ∑ m ∈ Finset.univ.image 𝒯.deg, ∑ n ∈ Finset.univ.image 𝒯.deg,
      P.mul (g (homogeneousProj 𝒯.deg m a)) (g (homogeneousProj 𝒯.deg n b)) := by
  conv_lhs => rw [← sum_homogeneousProj 𝒯.deg a, ← sum_homogeneousProj 𝒯.deg b]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

theorem truncMul_mem_lowerSubspace {E : Type*} (γ : ℝ) (f g : E → ι → ℝ) (x : E) :
    P.truncMul γ f g x ∈ lowerSubspace 𝒯.deg γ :=
  lowerProj_mem _

/-- The algebraic decomposition (4.4) of [Hai14] for one model, in coordinates of degree `< γ`:
`(Q_{<γ}(b₁ ⋆ b₂) − Γ Q_{<γ}(a₁ ⋆ a₂))_k = (b₁ ⋆ (b₂ − Γa₂))_k + ((b₁ − Γa₁) ⋆ b₂)_k
− ((b₁ − Γa₁) ⋆ (b₂ − Γa₂))_k + (Γa₁ ⋆ Γa₂ − Γ Q_{<γ}(a₁ ⋆ a₂))_k`. -/
theorem lowerProj_mul_sub_map_apply_eq (Γ : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) {γ : ℝ}
    (a₁ a₂ b₁ b₂ : ι → ℝ) {k : ι} (hk : 𝒯.deg k < γ) :
    (lowerProj 𝒯.deg γ (P.mul b₁ b₂) - Γ (lowerProj 𝒯.deg γ (P.mul a₁ a₂))) k =
      P.mul b₁ (b₂ - Γ a₂) k + P.mul (b₁ - Γ a₁) b₂ k - P.mul (b₁ - Γ a₁) (b₂ - Γ a₂) k +
        (P.mul (Γ a₁) (Γ a₂) - Γ (lowerProj 𝒯.deg γ (P.mul a₁ a₂))) k := by
  rw [Pi.sub_apply, lowerProj_apply_of_lt hk]
  simp only [map_sub, LinearMap.sub_apply, Pi.sub_apply]
  ring

section Regular

variable {P} {V W : Submodule ℝ (ι → ℝ)} {γ : ℝ}

/-- For a `γ`-regular pair of graded subspaces, `g Q_{<γ} (a ⋆ b) = ∑_{m + n < γ} g Q_m a ⋆ g Q_n b`
for `g ∈ G`, `a ∈ V`, `b ∈ W`. -/
theorem IsRegularPair.map_lowerProj_mul (hP : P.IsRegularPair V W γ)
    (hV : ∀ α, ∀ a ∈ V, homogeneousProj 𝒯.deg α a ∈ V)
    (hW : ∀ α, ∀ b ∈ W, homogeneousProj 𝒯.deg α b ∈ W)
    {g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)} (hg : g ∈ 𝒯.group) {a b : ι → ℝ} (ha : a ∈ V)
    (hb : b ∈ W) :
    (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (lowerProj 𝒯.deg γ (P.mul a b)) =
      ∑ m ∈ Finset.univ.image 𝒯.deg, ∑ n ∈ Finset.univ.image 𝒯.deg,
        if m + n < γ then
          P.mul ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (homogeneousProj 𝒯.deg m a))
            ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (homogeneousProj 𝒯.deg n b))
        else 0 := by
  rw [lowerProj_mul_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with hmn
  · exact hP g hg m n hmn _ (hV m a ha) (homogeneousProj_mem _ _ _) _ (hW n b hb)
      (homogeneousProj_mem _ _ _)
  · exact map_zero _

/-- For a `γ`-regular pair, `g a ⋆ g b − g Q_{<γ} (a ⋆ b) = ∑_{m + n ≥ γ} g Q_m a ⋆ g Q_n b`
[Hai14, (4.5)]. -/
theorem IsRegularPair.mul_map_sub_map_lowerProj_mul (hP : P.IsRegularPair V W γ)
    (hV : ∀ α, ∀ a ∈ V, homogeneousProj 𝒯.deg α a ∈ V)
    (hW : ∀ α, ∀ b ∈ W, homogeneousProj 𝒯.deg α b ∈ W)
    {g : LinearMap.GeneralLinearGroup ℝ (ι → ℝ)} (hg : g ∈ 𝒯.group) {a b : ι → ℝ} (ha : a ∈ V)
    (hb : b ∈ W) :
    P.mul ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) a) ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) b) -
        (g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (lowerProj 𝒯.deg γ (P.mul a b)) =
      ∑ m ∈ Finset.univ.image 𝒯.deg, ∑ n ∈ Finset.univ.image 𝒯.deg,
        if m + n < γ then 0 else
          P.mul ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (homogeneousProj 𝒯.deg m a))
            ((g : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (homogeneousProj 𝒯.deg n b)) := by
  rw [hP.map_lowerProj_mul hV hW hg ha hb, mul_map_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

end Regular

end RegularityStructure.GradedProduct

end RegularityStructures

end
