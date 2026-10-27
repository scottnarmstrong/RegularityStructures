module

public import GlobalPhi43.MW20.SourceConeEstimate

/-! The actual cone witness on the MW20 inset cylinders. We use the source's
spatial supremum norm and change one spatial coordinate, keeping time fixed.
The cone radius is the printed 1/2-d; a fixed angle 1/2 is uniform in R,d. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set

/-- Every source inset cylinder has the uniform spatial cone needed by
Corollary 2.12. The witness is an actual point of the same inset cylinder. -/
theorem cylinderInterior_spatialInteriorCone {R d : ℝ} (hR : R < 1 / 2) :
    SpatialInteriorCone (cylinderInterior R d) (1 / 2 - d) (1 / 2) := by
  intro r hr hrd x hx a
  classical
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 3 => |a i|) Finset.univ_nonempty
  have hnorm : ‖a‖ ≤ |a i| := by
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro j
    simpa only [Real.norm_eq_abs] using hmax j (Finset.mem_univ j)
  have hwidth : r < 1 - R - d := by linarith
  let s : ℝ := if 0 ≤ x.2 i then -r else r
  have hs : |s| = r := by
    dsimp [s]
    split_ifs <;> simp [abs_of_pos hr]
  refine ⟨spatialCoordinateLine x i s, ?_, ?_, ?_⟩
  · obtain ⟨ht, ht₁, hspace⟩ := hx
    refine ⟨ht, ht₁, fun j => ?_⟩
    by_cases hji : j = i
    · subst j
      simp only [spatialCoordinateLine, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
        smul_eq_mul, mul_one]
      dsimp [s]
      split_ifs with hsign
      · obtain ⟨hl, hu⟩ := hspace i
        constructor <;> linarith
      · have hsign' : x.2 i < 0 := lt_of_not_ge hsign
        obtain ⟨hl, hu⟩ := hspace i
        constructor <;> linarith
    · simpa only [spatialCoordinateLine, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne hji, smul_eq_mul, mul_zero, add_zero] using hspace j
  · rw [spatialCoordinateLine_pdist, hs]
  · rw [spatialCoordinateLine_affine, abs_mul, hs]
    have hh := mul_le_mul_of_nonneg_right hnorm hr.le
    have hn := mul_nonneg (norm_nonneg a) hr.le
    linarith

end GlobalPhi43.MW20
