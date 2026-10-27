module

public import GlobalPhi43.Attachment.TestGeometry
public import RegularityStructures.Abstract.Model

@[expose] public noncomputable section

open Set RegularityStructures GlobalPhi43.Local
open scoped Pointwise

namespace GlobalPhi43.Flow

/-- The literal growing compact of part 3. -/
def windowSet (k : ℝ) : Set ParabolicSpace :=
  Icc (-17) k ×ˢ pi univ (fun _ : Fin 3 => Icc (-6) 7)

/-- The cover region C_r, including its time margin. -/
def coverRegion (r : ℝ) : Set ParabolicSpace :=
  Icc r (r + 5 / 4) ×ˢ pi univ (fun _ : Fin 3 => Icc (-2) 3)

/-- The slice region C'_r. -/
def sliceRegion (r : ℝ) : Set ParabolicSpace :=
  Icc r (r + 1) ×ˢ pi univ (fun _ : Fin 3 => Icc (-1) 2)

/-- The closed radius-four max-parabolic neighbourhood of the covering and slice regions. -/
def majorantRegion (r : ℝ) : Set ParabolicSpace :=
  (coverRegion r ∪ sliceRegion r) + {z | pdist 0 z ≤ 4}

/-- The intermediate rectangle containing the majorant region. -/
def enlargedRectangle (r : ℝ) : Set ParabolicSpace :=
  Icc (r - 16) (r + 69 / 4) ×ˢ pi univ (fun _ : Fin 3 => Icc (-6) 7)

theorem isCompact_windowSet (k : ℝ) : IsCompact (windowSet k) :=
  isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)

theorem sliceRegion_subset_coverRegion (r : ℝ) : sliceRegion r ⊆ coverRegion r := by
  rintro z ⟨ht, hx⟩
  refine ⟨⟨ht.1, by linarith [ht.2]⟩, ?_⟩
  intro i hi
  have h := hx i hi
  constructor <;> linarith [h.1, h.2]

theorem majorantRegion_subset_rectangle (r : ℝ) : majorantRegion r ⊆ enlargedRectangle r := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have hx' : x ∈ coverRegion r := hx.elim id (fun hh => sliceRegion_subset_coverRegion r hh)
  have hy' := (Attachment.pdist_zero_le_iff (by norm_num : (0 : ℝ) ≤ 4) y).mp hy
  have hyt : -16 ≤ y.1 ∧ y.1 ≤ 16 := by
    constructor <;> nlinarith [hy'.1.1, hy'.1.2]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change r - 16 ≤ x.1 + y.1
    linarith [hx'.1.1, hyt.1]
  · change x.1 + y.1 ≤ r + 69 / 4
    linarith [hx'.1.2, hyt.2]
  · intro i hi
    have hxi := hx'.2 i hi
    have hyi := hy'.2 i hi
    change -6 ≤ x.2 i + y.2 i ∧ x.2 i + y.2 i ≤ 7
    constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

theorem rectangle_subset_windowSet {r k : ℝ} (hr : 0 ≤ r) (hrk : r ≤ k - 18) :
    enlargedRectangle r ⊆ windowSet k := by
  rintro z ⟨ht, hx⟩
  exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hx⟩

/-- The source inclusion, uniform over all real restart times in the range. -/
theorem majorantRegion_subset_windowSet {r k : ℝ} (hr : 0 ≤ r) (hrk : r ≤ k - 18) :
    majorantRegion r ⊆ windowSet k :=
  (majorantRegion_subset_rectangle r).trans (rectangle_subset_windowSet hr hrk)

theorem potentialWindow_subset {r k : ℝ} (hr : 0 ≤ r) (hrk : r ≤ k - 18) :
    Icc r (r + 1) ⊆ Icc (-1) k := by
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

/-- Monotonicity is proved directly from the best-constant definitions. -/
theorem model_normOn_mono {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace E] {μ : MeasureTheory.Measure E} {𝒯 : RegularityStructure ι}
    {K : RegularisingSemigroup E μ} (Z : Model 𝒯 K) (γ : ℝ)
    {S T : Set E} (hST : S ⊆ T) : Z.normOn γ S ≤ Z.normOn γ T := by
  apply add_le_add
  · unfold Model.piNormOn
    refine le_iInf fun C => le_iInf fun hC => ?_
    exact iInf₂_le C (fun i hi t ht x hx => hC i hi t ht x (hST hx))
  · unfold Model.gammaNormOn
    refine le_iInf fun C => le_iInf fun hC => ?_
    exact iInf₂_le C (fun i j hi hj x hx y hy => hC i j hi hj x (hST hx) y (hST hy))

/-- Model norm control on every real restart region, from the actual geometric inclusion. -/
theorem majorant_model_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup ParabolicSpace MeasureTheory.volume}
    (Z : Model 𝒯 K) (γ : ℝ) {r k : ℝ} (hr : 0 ≤ r) (hrk : r ≤ k - 18) :
    Z.normOn γ (majorantRegion r) ≤ Z.normOn γ (windowSet k) :=
  model_normOn_mono Z γ (majorantRegion_subset_windowSet hr hrk)

end GlobalPhi43.Flow
