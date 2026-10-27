# Errata and deviations

This document separates printed errors from deliberate choices made by the formalisation. An erratum is a defect in the cited source itself: a missing hypothesis, an incorrect conclusion, or a proof step that does not follow from the printed assumptions. A deviation records a change of scope, convention, topology, interpretation, or proof strategy. Locations below refer to the arXiv versions listed in the source table; theorem and equation numbers are those versions' numbers.

The main source is Hairer, *A theory of regularity structures*, pinned as arXiv:1303.5113v4. The analytic supplement is Hoshino, pinned as arXiv:2310.07396v2. The stochastic sources are Hairer–Steele, pinned as arXiv:2301.10081v3, and Bailleul–Hoshino, pinned as arXiv:2310.10202v4. The global theory follows Mourrat–Weber, pinned as arXiv:1601.01234v3, and Moinat–Weber, pinned as arXiv:1811.05764v1. LOTT24 and BHZ19 are used as methodological and algebraic references; their pinned citations, together with the remaining reference-only sources, are recorded below.

| Source | Errata | Deviations |
|---|---:|---:|
| Hai14 | 1 | 6 |
| Hos25 | 0 | 1 |
| HS23 | 0 | 4 |
| BH26 | 1 | 3 |
| MW20 | 10 | 2 |
| MW17 | 1 | 2 |
| LOTT24 | 0 | 0 |
| BHZ19 | 0 | 0 |
| **Total** | **13** | **18** |

The table counts entries in the source sections below. The final proof-strategy section is explanatory and is not counted separately.

## Hai14: Hairer 2014

### Errata

1. **pp. 91–92, Proposition 6.12 and its proof, (6.10)–(6.12).** Missing hypothesis. Definition 6.2 allows any `η ∈ ℝ`, and Propositions 6.9, 6.13 and 6.16 assume `η ≤ γ` or `η < γ` explicitly. Proposition 6.12 sets `η = (η₁ + α₂) ∧ (η₂ + α₁) ∧ (η₁ + η₂)` but does not assume `η ≤ γ`, and without it the conclusion `f₁ ⋆_γ f₂ ∈ D_P^{γ,η}` can fail. Take the polynomial structure on `ℝ` truncated at degree one (`T = ⟨1, X⟩`, `X ⋆ X = 0`), `P = {0}`, `γ₁ = γ₂ = γ ∈ (1, 2)`, `α₁ = α₂ = 0`, `η₁ = η₂ = 3`, and `f₁ = f₂ = φ 1 + φ′ X` with `φ` smooth and bounded and `φ(x) = x` near `0`. The increments of `fᵢ` vanish near `P`, so `fᵢ ∈ D_P^{γ,3}`, and the printed exponent is `η = 3 > γ`. The `X`-component of the increment of `f₁ ⋆_γ f₂ = φ² 1 + 2φφ′ X` between `x = λ` and `y = 2λ` is `2λ`, while `D_P^{γ,3}` requires it to be `O(λ^{γ−1} λ^{3−γ}) = O(λ²)`. In the proof, the term of (6.12) with `m ≤ η₁` and `n ≤ η₂` has exponent `m + n − γ`, which need not dominate `η − γ`. The correction is to add `η ≤ γ`, or equivalently to conclude `f₁ ⋆_γ f₂ ∈ D_P^{γ, η ∧ γ}`. The hypothesis holds automatically when `ηᵢ ≤ γᵢ`, and Hairer's Φ⁴₃ application, Lemma 9.7, satisfies it. The corrected statement, with the hypothesis `η ≤ γ`, is `Model.singularBoundOn_truncMul_near` in [`WeightedSingularProductNear.lean`](../RegularityStructures/Abstract/WeightedSingularProductNear.lean). The counterexample is explained in the module documentation of [`WeightedSingularProduct.lean`](../RegularityStructures/Abstract/WeightedSingularProduct.lean); it is not a Lean theorem. Effect on the stated theorems: none; the formal statement carries the hypothesis `η ≤ γ`, and every use satisfies it.

### Deviations

1. **Theorem 1.15 and Remarks 1.13, 1.16–1.18.** Hairer states rough initial data in `C^α` and convergence through stopped processes. The formalised headline fixes smooth initial data, keeps Hairer’s exponent interval `(-2/3, -1/2)`, and assembles a path up to its maximal existence time in the completed negative Hölder space. This is a deliberately narrower and differently packaged headline; it does not claim the full rough-data statement from Theorem 1.15. Effect on the stated theorems: The formalised theorem has the stated smooth-data scope rather than Hairer’s full rough-data scope.

2. **Theorem 1.15, Theorem 10.22, and constants (10.33) and (10.41).** Hairer allows suitably chosen counterterms and uses the truncated heat kernel in the model construction. The formalisation names the two Gaussian constants built from the massive heat kernel, fixes the torus and coupling conventions, and incorporates the mass parameter as a fixed linear shift. The comparison with Hairer’s compactly supported kernel is therefore an additional identification step. Effect on the stated theorems: The formalised theorem asserts convergence for the displayed explicit constants; this is stronger and more specific than the literal “suitably chosen constants” wording.

3. **Propositions 9.8 and 9.10, and Theorem 10.22.** Hairer’s proof uses the regularity-structures fixed-point theorem, wavelet/model estimates, and the model convergence theorem in Section 10.5. The formalisation exposes the semigroup reconstruction and Schauder estimates, the finite Φ⁴₃ sector, the explicit renormalised equation, and the stochastic convergence interface as separate mathematical components. Hairer’s results remain the source of the comparison statements, not a claim that the formalisation has reproduced every intermediate construction verbatim. Effect on the stated theorems: No effect on the stated theorems; this is a proof-interface and exposition choice.

4. **Theorem 5.12 (the library statements `Statements.Model.kGamma_mem_modelledDistributions` and `Statements.Model.reconstruct_kGamma`).** Every degree of the regularity structure below `γ` must exceed `−2`, not only the degrees occurring in the sector `V`. This excludes the noise symbol `Ξ` of the Φ⁴₃ structure, of degree `−5/2 − κ`, so these statements do not apply to the Φ⁴₃ structure itself. The integration map has no component in the abstract polynomials, and only the first half of the theorem is stated: the bound `𝒦_γ : D^γ → D^{γ+2}` and (5.17), not the local Lipschitz estimate in the model. A non-degenerate example of the hypotheses is `SchauderWitness.schauderSetting_witness` in [`SchauderSetting.lean`](../tests/Witnesses/SchauderSetting.lean). Effect on the stated theorems: none on Theorem A, which uses the singular Schauder estimate of Section 7 instead.

5. **Theorems 3.10 and 5.12 (the library statements `Statements.Model.exists_reconstruction`, `Statements.Model.abs_reconstruct_sub_reconstruct_le`, `Statements.Model.abs_pairing_rescaledTestFunction_le`, `Statements.Model.eq_reconstruct_of_abs_pairing_le`, `Statements.Model.kGamma_mem_modelledDistributions` and `Statements.Model.reconstruct_kGamma`).** Hairer's bounds are local: the model and the modelled distribution are bounded on compact sets, and so is the conclusion. The library statements assume global bounds (on all of space-time) for the model and for `f`. They therefore do not apply directly to models whose bounds hold only locally, such as the random BPHZ models. Effect on the stated theorems: none on Theorem A; the restriction concerns these library statements only.

6. **Proposition 7.11 (the library statements `Statements.exists_maximal_solution` and `Statements.exists_global_solution_of_bound`).** These are the abstract patching argument behind Proposition 7.11 and the discussion after it, for an arbitrary solution relation with local existence, local uniqueness, restriction and an autonomous gluing hypothesis. They are not Proposition 7.11 itself, which concerns the solutions of the fixed point of Section 7; the hypotheses must be verified for each equation. Effect on the stated theorems: none on Theorem A, whose maximal solution is assembled separately.

## Hos25: Hoshino 2025

### Errata

No source erratum is retained for the pinned text.

### Deviations

1. **Theorem 4.1 and Theorem 5.12.** Hoshino proves semigroup reconstruction and multilevel Schauder estimates in a weighted regularity-integrability setting on the general spaces of the paper. The formalisation uses the semigroup mechanism in the finite Φ⁴₃ sector and its periodic setting, with the weights and model bounds specialised to the theorem at hand. It does not present the whole regularity-integrability framework as a formalised theorem. The library statements of reconstruction and of the Schauder estimate (`RegularityStructures/Statements/`) are specialised in the same way, and also relative to Hairer's Theorems 3.10 and 5.12: a regularity structure has a finite graded basis (a finite-dimensional model space, finitely many homogeneities); reconstruction assumes `γ > 0` and global bounds on the model and on `f`, and its test-function bound and uniqueness statement on `ℝ⁴` assume that every degree below `γ` exceeds `−4`, and uniqueness is among measurable distributions `Λ` with a global bound `|Λ_u| ≤ C u^{α/4}`, `0 < u ≤ 1`, for some `α > −4`; the Schauder statements are for the parabolic heat kernel with gain two, require every degree below `γ` to exceed `−2` (which excludes the Φ⁴₃ noise symbol), require the sector `V` to be a coordinate sector (whenever `a ∈ V` has a nonzero coordinate `j`, the basis vector `e_j` lies in `V`; Hairer's Definition 2.5 allows any graded invariant subspace with homogeneous complements), have an integration map with no polynomial component and non-integrality conditions that can be stronger than `γ + β ∉ ℕ`, assume joint measurability of the model, and state only the first part of Theorem 5.12; the identity (5.17) also assumes a global bound on the model up to level `γ + 2`. Effect on the stated theorems: none on Theorem A, whose proof uses the singular Schauder estimate of Hairer's Section 7; the library statements carry these restrictions as hypotheses.

## HS23: Hairer–Steele 2023

### Errata

No source erratum is retained for the pinned text.

### Deviations

1. **Theorem 2.33 and Remark 2.34.** The theorem gives convergence in probability along the paper’s approximation sequence, while the mollifier-independence argument is stated in a remark through an alternating sequence. The formalisation needs a continuous-parameter, cross-mollifier Cauchy statement with moment bounds, so it supplies that interface explicitly rather than reading an `L^p` rate or a continuous-parameter theorem into Theorem 2.33. Effect on the stated theorems: The formalised stochastic input has stronger quantifiers than the cited theorem and is not attributed to HS23 alone.

2. **Theorem 2.33 and the spectral-gap setup of Sections 2 and 6.** HS23 works on the whole space. The formalisation works with space-periodic noise on `R × T³` and does not use HS23’s whole-space spectral-gap and localisation steps; it proves the needed Gaussian moment bounds directly for the periodic noise (see item 3 of the proof-strategy section). Effect on the stated theorems: The formalised theorem is periodic; HS23 is not cited as already proving that periodic adaptation.

3. **Theorem 2.33 and the finite Φ⁴₃ sector.** HS23 treats a general reduced regularity structure and its BPHZ model. The formalisation identifies the relevant BPHZ characters with the two explicit Φ⁴₃ constants and works in the finite sector needed for the renormalised cubic equation. Effect on the stated theorems: No effect on the stated theorems; this records the narrower algebraic interface actually used.

4. **Lemma 6.4 and the mollifier class.** HS23 does not define the word *mollifier*. The proof of Lemma 6.4 (p. 67) treats `̺ⁿ(z) dz` as a probability measure: it bounds `|ψ^λ − ̺^{n₁} ∗ ψ^λ|` by `∫ |ψ^λ(y) − ψ^λ(y − z)| ̺^{n₁}(z) dz`, and for `λ < 2^{−n₁}` it applies Jensen's inequality. Both steps are valid for nonnegative mollifiers. The formalisation's mollifiers are smooth, compactly supported and of integral one, with no sign condition. It therefore replaces `̺ⁿ` by `|̺ⁿ|` and Jensen's inequality by the Cauchy–Schwarz inequality, at the cost of a factor `‖̺‖_{L¹}`, and carries such `L¹` bounds through the convolution estimates. It also treats every scale `ε ∈ (0, 1]` rather than only the dyadic sequence used in the source. Effect on the stated theorems: none; this is a proof supplement and does not change the smooth-noise equation or its explicit counterterms.

## BH26: Bailleul–Hoshino 2026

### Errata

1. **pp. 29–30, Section 4.6, step §0, and Section 4.7, (4.13).** Gap. Step §0 of the proof of the Cauchy property (4.12) states that `lim_{m,n→∞} ‖h_n − h_m‖_H = 0`, with `h_n = ϱ_n ∗ h`, holds uniformly over `‖h‖_H ≤ 1`. Section 4.7 deduces that the limit does not depend on the approximation of the identity from (4.13), under the condition `lim_{n→∞} sup_{‖h‖_H ≤ 1} ‖h ∗ ϱ_n − h ∗ ϱ̃_n‖_H = 0`. Theorem 19 allows `H = L²(ℝ^d)` for white noise. On `L²` the operator `h ↦ h ∗ k` has norm `sup_ζ |k̂(ζ)|`. For rescalings `ϱ_n = 2^{n|s|} ϱ(2^{n s} ·)`, the norm of `h ↦ h ∗ (ϱ_n − ϱ_{n+1})` is therefore a positive constant independent of `n`. For two kernel shapes at the same scale, the norm of `h ↦ h ∗ (ϱ_n − ϱ̃_n)` equals `sup_ζ |ϱ̂(ζ) − ϱ̃̂(ζ)| > 0` for every `n`. So neither uniform statement holds in the `H` norm, and the same computation applies to every space `H^{−s₀,Q}(w₀)` allowed by Theorem 19. The proof uses `h_n` only through the model norm on the noise-direction symbol. Section 4.2 bounds that norm by `‖h_n‖_{B^{r₀−ε+|s|/p}_{p,∞}(w₀)}`, and since `r₀ < −|s|/2 − s₀`, `H` embeds into this space with a strict loss of regularity. Both uniform convergences hold in that weaker norm, and using it there appears to address the gap. Effect on the stated theorems: none; no conclusion of BH26 is shown to be false, and the formalisation does not use this argument.

### Deviations

1. **Theorem 19 and Sections 2–4.** BH26 uses weighted whole-space model spaces and a regularity-integrability topology. The formalisation uses Hairer’s model topology on a finite periodic sector, with models built from a causal heat kernel. Effect on the stated theorems: No effect on the stated theorems; BH26 is a methodological comparison, not the source of the formalised topology.

2. **Section 6.2, periodic examples.** The periodic Fourier examples in BH26 are not taken as a proof that the periodic white-noise law satisfies every whole-space hypothesis of Theorem 19. The formalisation proves the periodic spectral-gap and model estimates in its own setting. Effect on the stated theorems: No effect on the stated theorems; the periodic theorem is not inferred from the example alone.

3. **Theorem 19 and Corollary 20.** BH26 permits a broad class of preparation maps and renormalisation procedures. The formalisation uses the finite Φ⁴₃ renormalisation procedure and the explicit two-constant identification needed for the equation in the headline theorem. Effect on the stated theorems: No effect on the stated theorems; the formalised result is a specialised application rather than a formalisation of BH26’s full generality.

## MW20: Moinat–Weber 2020

Augustin Moinat and Hendrik Weber, *Space-time localisation for the dynamic Φ⁴₃ model*, Comm. Pure Appl. Math. 73 (2020), 2519–2555, pinned as arXiv:1811.05764v1 (SHA-256 of the PDF `7ea3de7d91c9f1b2c0d3f24cdfd9477292189a03384f3ab01e17f3c81140ff7e`). Page numbers are those printed in that preprint, and the paper's `ε` is written `κ` below where the formalisation uses `κ`. None of the errata below is a counterexample to MW20 Theorem 2.1.

### Errata

1. **pp. 16–18, (4.18), (4.20)–(4.26), smallness factors.** Wrong power of the smallness parameter. Remove the factor `c` before the first sum in (4.18), keeping `c` on the seminorm to be absorbed. The `c`-free cubic forcing and the `c`-free `2‖v‖_D` in (4.13) then give `≲ ‖v‖_D`, not `≲ c‖v‖_D`, in (4.20)–(4.24), and the leading `c²` in (4.25) and both `c²` coefficients in (4.26) become `c`. The zero-tree solution `u = v = (2(t + t₀))^{−1/2}` refutes the printed (4.20), (4.22) and (4.23) as `c ↓ 0`. The corrected coefficients are those obtained by substituting into (4.2)–(4.3). Choosing `k` first and `c` second still closes the argument. Effect on the stated theorems: none; the formal proof uses the corrected coefficients.

2. **p. 9, Lemma 2.11, (2.34)–(2.36); pp. 21–22, Step 3.** Radius mismatch. The hypotheses give `L ≤ d/4` and `L₁, L₂ ≤ d/4`, but the proof evaluates the constants at `L = d/2` and `(L₁, L₂) = (d/2, d/4)`. For this substitution it suffices to assume (2.34) for `0 < T ≤ L ≤ d/2` and (2.35) for `0 < L₁ ≤ d/2`, `0 < L₂ ≤ d/4`, with the displayed majorants. This range change does not correct Lemma 2.11 as a whole: the counterexample of erratum 7 satisfies the enlarged ranges. Effect on the stated theorems: none; the formal proof does not use (2.36) (erratum 7).

3. **p. 4, first inequality in (2.10).** Missing constant. The printed relation is `≤ T^α`. For `n = 1`, `Ψ_{T,1} = Φ_{T/2}` has mass one and support radius at most `T/2`, so for `−5 < α < 0` the first integral is at least `2^{−α} T^α > T^α`. Read `≤ C_{α,Φ} T^α`, uniformly in `n` and `T`; coefficient one is valid for `α ≥ 0`. Effect on the stated theorems: none.

4. **p. 4, support sentence before (2.7).** Wrong radii. The printed radii are `1` and `1 − 2^n`, the latter negative for `n > 0`. The convolution construction gives supports in past balls of radii `T` and `T(1 − 2^{−n})`. The scale identities (2.7)–(2.8) are unchanged. Effect on the stated theorems: none.

5. **p. 6, Remark 2.2, chaos assignment.** Incorrect justification. The text places the supremum seminorm `[τ]_{γ_τ}` in a finite inhomogeneous Wiener chaos of order `n_τ`. Chaos degree applies to the underlying polynomial fields, not to their supremum norms; a nonconstant nonnegative seminorm cannot be an affine Gaussian variable. The stretched-exponential tail (2.22) needs a field and supremum estimate, for example a norm-valued hypercontractivity argument. This corrects the justification; it does not refute (2.22). Effect on the stated theorems: none.

6. **p. 18, (4.32), exponents of `k`.** Substitution misprint. In the parenthesis multiplied by `c`, replace `k^{−1/2+κ}` by `k^{1/2+κ}` and `k^{1+κ}` by `k^{1+2κ}`: with `T = (kM)^{−1}`, the terms `c T^{−1/2−κ} M^{5/2−κ}` of (4.25) and `c M^{2−2κ} T^{−1−2κ}` of (4.26), p. 17, give exactly these powers times `cM³`. For `k ≥ 1` they are dominated by the existing `k^{1/2+5κ}` and `k^{3/2+3κ}` terms, so the aggregate bound holds up to its constant. Effect on the stated theorems: none.

7. **pp. 9–10, Lemma 2.11, (2.36); pp. 22–23, §5.1 Step 4 and (5.6).** False uniform bound. The left side of (2.36) is the unrestricted seminorm `[U]_{κ,D_d}` (all pairs of `D_d`), the right side contains only the short-range `‖U‖_{D_d,d}`, and the constant depends only on `κ` and `A`, not on `d₀`. This fails for smooth bounded `U`. Take `D = P`, `1 < κ < 2`, `0 < d₀ < 1/4`, and `U(x, y) = t_y − t_x`, whose three-point defect vanishes. Under MW20's smoothing, `U_T(x, y) = t_y − t_x − m_T`, so `(∂_t − Δ_y) U_T = 1`. With `A = {κ}`, `M^{(1)}_{D_d,L} = L^{2−κ}` and `M^{(2)} = 0`, the hypotheses (2.34)–(2.35) hold, even on the enlarged ranges of erratum 2, and the right side is `O(d₀²)`. The pair `x = (1/4, 0)`, `y = (3/4, 0)` lies in every `P_d` and gives `[U]_{κ,D_d} ≥ (1/2)^{1−κ/2}`, so (2.36) would force `(1/2)^{1−κ/2} ≤ C_{κ,A}(1 + 2^{κ−2}) d₀^{2−κ} → 0`. A smooth cutoff in time, equal to `t` on `[−1, 2]`, changes none of the tests, so global boundedness does not help. The faulty step is the extension of the small-ball seminorm to all `y ∈ D_d` in Step 4, p. 23; (5.6) already states the unrestricted conclusion. Effect on the stated theorems: none; the formal proof never applies (2.36) and uses instead a radius-local estimate, with left side `sup_{d ≤ d₀} d^κ [U]_{κ,D_d,d}` over pairs at distance at most `d` and a three-point hypothesis without time order.

8. **p. 10, Corollary 2.12, (2.37); p. 23, §5.1.1.** Endpoint typo. The inequality `λ‖ν‖_{D_d} ≤ [U]_{κ,D_d} r^{κ−1} + ‖U‖_{D_d,r} r^{−1}` is asserted for `r ∈ [0, r_d]`, but the reciprocal is undefined at `r = 0`; the proof divides by `r`. Read (2.37) for `0 < r ≤ r_d`, and likewise for the `r^{−κ}` term of (2.38). The cone condition itself may keep `r = 0`. Effect on the stated theorems: none. In a formal statement the closed range would be read with Lean's convention `0⁻¹ = 0`, which would make it false; only positive radii are meaningful.

9. **p. 10, Corollary 2.12, (2.38) and the sentence below it; p. 23, §5.1.1.** Constant too uniform. Below (2.38) the constant is said to depend only on `κ`, hence uniformly over every finite exponent set `A` admitted by (2.35). That is false. Take `κ = 3/2`, `D = P_{1/4}`, `d = d₀ = 1/4`, so `E = D_d = (1/8, 1) × (−1/2, 1/2)³`, one fixed cone, `r_d = 1/4`, `λ = 1/2` and `r = 1/4`. For `n ≥ 4` and distinct spatial coordinates `X₀, X₁` put `ν_n(x) = sin(n X₀(x)) e₁`, `U_n(x, y) = sin(n X₀(x))(X₁(y) − X₁(x))`, and `A_n = {1/2 + j/(2n²) : 1 ≤ j ≤ n²}`. Then `[U_n]_{3/2,E} = 0` with `ν_n` an exact optimal coefficient. The three-point defect is at most `n p q ≤ n p^β q^{3/2−β}` for every `β ∈ A_n`, so (2.35) holds with `M^{(2)} = 1/n`, and (2.34) with `M^{(1)} = 0`. Also `r^{−3/2}‖U_n‖_{E,r} ≤ 2`, while two points at distance `π/(2n)` give `[ν_n]_{1/2,E} ≥ (2n/π)^{1/2}`. The printed bound would need `(2n/π)^{1/2} ≤ C_{3/2}(1/n + 2)` for all `n ≥ 4`. Correction: let the constant depend on `#A`, keeping the cone coefficient `λ`. For an optimal coefficient and `0 < r ≤ r_d`, a sufficient form is `[ν]_{κ−1,D_d} ≤ λ^{−1}[(2^κ + 4)[U]_{κ,D_d} + (#A) M^{(2)}_{D_d,d/4,d/4} + 2 r^{−κ}‖U‖_{D_d,r}]`. Effect on the stated theorems: none; the formal proof applies the corollary with a single exponent and a fixed cone.

10. **p. 16, §4.3, (4.9)–(4.10) and the substitutions into (4.14)–(4.17); p. 14, (4.1).** Wrong amplitude. Hypothesis (4.1) bounds the trees by the parent amplitude `M = ‖v‖_D`: `[Y]_{1−2κ} ≤ c M^{1−2κ}` and `[Z]_{1/2−3κ} ≤ c M^{3/2−3κ}`. The second lines of (4.9) and (4.10) use the child amplitude instead (`3c d^{1/2+κ}‖v‖_{D_d}^{2−2κ}` and `3c ‖v‖_{D_d}^{2−2κ}`). The justified substitution is `3c ‖v‖_{D_d} M^{1−2κ}`, and since `‖v‖_{D_d} ≤ M` the printed comparison goes the wrong way. A smooth, spatially constant solution of the source equations with zero defects and counterterms `C₁ = 2/3`, `C₂ = −2/9` shows that the second line of (4.10) fails: for large `M` all parent tree bounds of (4.1) hold for any fixed `c > 0`, while on the child cylinder `D_d`, `d = 1/4`, one has `v = J = 1`, `U ≡ 0`, `ν = 0` and `[v + Z]_{1−2κ,D_d,d} = d^{1+2κ}`, which would have to be at most `3c`. Correction: keep the first lines of (4.9)–(4.10), substitute (4.1) with the parent amplitude, and replace the child amplitude by `M` on the right of (4.14)–(4.17); (4.12), (4.13) and (4.18) already use the parent amplitude. At `d ≤ d₀ = M^{−1}` this gives the `c`-free bounds needed in the corrected (4.21)–(4.24) (erratum 1). Effect on the stated theorems: none; the formal proof uses the parent-amplitude bounds.

### Deviations

1. **pp. 4, 6, 23, (2.9), (2.16)–(2.19), (5.7), time orientation.** Convention. Ordinary convolution and (5.7) test with `Ψ_T(x − y)`, the recentered seminorms with `Ψ_T(y − x)`; for a past-supported kernel these look in opposite time directions, and spatial evenness does not identify them. The formalisation uses one past-looking smoothing `h_T(x) = ∫ Ψ_T(y − x) h(y) dy` (`GlobalPhi43.mwSmooth`) for the negative norms as well, and proves the dyadic identities for this reflected family; the recentered seminorms are as printed. Effect on the stated theorems: the MW20 estimate is stated and proved in this convention.

2. **pp. 5–7, (2.13)–(2.15), Remark 2.4, integration kernel.** Adapted theorem. MW20 assumes exact PDE identities for its integrated trees. The formalisation uses the trees of the solutions of Theorem A, built with a truncated kernel, and carries the resulting smooth defects `e₁, e₂, e₃` through the local bound, at the costs `‖e₁‖^{1/3}`, `‖e₂‖^{1/2}`, `‖e₃‖^{1/3}`. The statement `GlobalPhi43.mw20DefectBound` is therefore an adaptation of MW20 Theorem 2.1, not a literal application of it, and is proved in full. Effect on the stated theorems: none on their statements; the uniform moment bound is derived from this adapted estimate.

## MW17: Mourrat–Weber 2017

Jean-Christophe Mourrat and Hendrik Weber, *The dynamic Φ⁴₃ model comes down from infinity*, Commun. Math. Phys. 356 (2017), 673–753, pinned as arXiv:1601.01234v3 (SHA-256 of the PDF `5fb03a1937adf2fea5ef4b7713bd87866df6e47057218805d9bb55d73369232b`).

### Errata

1. **pp. 60–62, Appendix A, periodicity and (A.10).** Inconsistent convention. p. 60 uses `ℤ^d`-periodic smooth functions and `L^p([−1, 1]^d, dx)`, and the proof of Proposition A.6, p. 61, again says one-periodic; but (A.10), p. 62, periodises over `(2ℤ)^d`, consistent with the spatial cube of side two. Read the periodic class with period two, or rescale the whole convention. No error in the coming-down-from-infinity theorem follows. Effect on the stated theorems: none.

### Deviations

1. **pp. 1–3, 60–62, spatial period and volume.** Convention. The formalisation keeps the unit torus `ℝ³/ℤ³` with Lebesgue measure of Theorem A, whereas MW17's cube has side two; period, Laplacian, noise covariance and counterterms are those of Theorem A. Effect on the stated theorems: they are stated on the unit torus.

2. **p. 60, (A.7), the state space.** Convention. Like MW17, the formalisation uses the completion of the smooth (here: continuous) periodic functions for the Besov norm with second index `∞`, a separable space, not the generally nonseparable space of all distributions with finite norm. Effect on the stated theorems: the state space `𝒞^η` is this completion, as in Theorem A.

## Reference-only pinned sources

No source-specific erratum or deviation is retained here for the following citations. They provide background, cross-checks, or context for extensions; the formalisation does not claim to reproduce their full theorems.

| Key | Pinned citation |
|---|---|
| CZ20 | arXiv:2005.09287v3 |
| BCZ24 | arXiv:2301.07517v2 |
| LOTT24 | arXiv:2112.10739v3 |
| BOT25 | arXiv:2401.05935v3 |
| Tem25 | arXiv:2303.18192v2 |
| BHZ19 | arXiv:1610.08468v4 |
| CH16 | arXiv:1612.08138v5 |
| BCCH21 | arXiv:1711.10239v4 |
| BH-tour | arXiv:2006.03524v3 |
| Hai-intro | arXiv:1401.3014v2 |
| CC18 | arXiv:1310.6869v3 |
| Kup16 | arXiv:1410.3094v2 |
| CMW23 | arXiv:1910.13854v2 |
| CG25 | arXiv:2510.20716v2 |
| GH21 | arXiv:1810.01700v4 |
| HSi25 | arXiv:2510.19339v1 |
| BOS25 | arXiv:2503.01621v1 |
| Duc25 | arXiv:2109.11380v3 |
| Duc26 | arXiv:2511.07120v2 |
| DPZ96 | G. Da Prato and J. Zabczyk, *Ergodicity for Infinite Dimensional Systems*, Cambridge University Press, 1996, DOI 10.1017/CBO9780511662829 (the Krylov–Bogoliubov construction) |

## Deviations of proof strategy from Hairer 2014

The formalisation’s proof strategy differs from Hairer’s beyond the individual statement changes above:

1. It makes semigroup reconstruction and the multilevel Schauder estimate explicit, instead of taking Hairer’s wavelet-based analytic estimates as the visible interface.
2. It constructs and checks only the finite Φ⁴₃ sector needed for the cubic equation, including the polynomial sector, the structure-group action, and the two-constant renormalisation map. The polynomial symbols are treated separately from the non-polynomial homogeneities, as required by Hairer’s Assumption 5.3. The distinction is illustrated by [`NonIntegralityPolynomial.lean`](../tests/regression/NonIntegralityPolynomial.lean) and [`Phi4HypsInconsistent.lean`](../tests/regression/Phi4HypsInconsistent.lean).
3. It uses Gaussian Poincaré and spectral-gap estimates for the concrete periodic noise and proves the needed cross-mollifier bounds in the finite sector, rather than importing the general whole-space model-convergence theorem as a black box.
4. It identifies the smooth-noise model with the classical mild and PDE solutions, then assembles the limit through its maximal existence time. Measurability of the white-noise family and non-emptiness of the mollifier class are made explicit; the related checks are recorded in [`FakeWhiteNoise.lean`](../tests/regression/FakeWhiteNoise.lean) and [`MollifierExists.lean`](../tests/regression/MollifierExists.lean).
5. It uses a periodic adaptation of the stochastic estimates and the massive heat kernel used to define the explicit constants. The Hairer comparison kernel remains the reference object for the local singularity and counterterm identification.

These choices explain why a source theorem can be the mathematical origin of a component without being a literal description of the formalised proof route. They also delimit the claims: the document records the source correction and the formalisation’s chosen interfaces, not a blanket transfer of every hypothesis or conclusion across the cited papers.
