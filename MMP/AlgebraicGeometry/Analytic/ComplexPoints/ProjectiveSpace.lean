module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProjectiveSpaceCompact
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicTopology.ComplexProjectiveSpace.Cohomology

/-!
# The complex points of projective space

Let `ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]` be projective space over `ℂ`, and `ℙⁿ_ℂ(ℂ)` its set of complex
points with the classical topology. A point `p` lying in the standard chart `Uᵢ = {xᵢ ≠ 0}` has
affine coordinates `vᵢ(p) = (x_j / xᵢ)(p)`, a vector of `ℂⁿ⁺¹` with `i`-th entry `1`; on
`Uᵢ ∩ U_k` the relation `x_j / xᵢ = (x_k / xᵢ)(x_j / x_k)` gives
`vᵢ(p) = (x_k / xᵢ)(p) · v_k(p)`, so the line `ℂ vᵢ(p) ⊆ ℂⁿ⁺¹` does not depend on the chart.
Sending `p` to the orthogonal projection onto this line gives a map `ℙⁿ_ℂ(ℂ) → ℙⁿ(ℂ)` to complex
projective space, modelled as the space of the projection matrices `v v^* / (v^* v)`,
`v ∈ ℂⁿ⁺¹ - 0`.

The map is continuous, since on the open set `Uᵢ(ℂ)` it is the composite of the continuous
evaluations of the `x_j / xᵢ` with `v ↦ v v^* / (v^* v)`. It is injective: the `(i, i)` entry of
the projection onto `ℂ v` vanishes iff `vᵢ = 0`, so two points with the same image lie in a common
chart `Uᵢ`, where the projection recovers `vᵢ(p)` as its `i`-th column divided by its `(i, i)`
entry, and a point of the affine scheme `Uᵢ` is determined by the values of the generators
`x_j / xᵢ` of its coordinate ring. It is surjective: for `vᵢ ≠ 0`, the substitution `xᵢ ↦ 1`,
`x_j ↦ v_j / vᵢ` is a `ℂ`-point of `Uᵢ = Spec ℂ[x₀, …, xₙ]_{(xᵢ)}` with affine coordinates
`vᵢ⁻¹ v`. As `ℙⁿ_ℂ(ℂ)` is compact and `ℙⁿ(ℂ)` is Hausdorff, the map is a homeomorphism.

## Main definitions

* `MMP.Topology.toLineProjection`: the projection onto the line of `ℂⁿ⁺¹` through a point of
  `ℙⁿ_ℂ(ℂ)`.
* `MMP.Topology.underlyingSpaceProjectiveSpaceHomeomorph`: the homeomorphism
  `ℙⁿ_ℂ(ℂ) ≃ₜ ℙⁿ(ℂ)` for the underlying space with the classical topology.
* `MMP.Topology.complexPointsProjectiveSpaceHomeomorph`: the homeomorphism `(ℙⁿ_ℂ)^an ≃ₜ ℙⁿ(ℂ)`
  for the complex realization.

## Main results

* `MMP.Topology.toLineProjection_eq`: the line through `p` is spanned by its affine coordinates in
  any standard chart containing it.
* `MMP.Topology.eq_of_eval_projectiveSpaceStdCoord_eq`,
  `MMP.Topology.exists_eval_projectiveSpaceStdCoord_eq`: over any field `K`, the affine
  coordinates `(x_j / xᵢ)_j` identify `Uᵢ(K)` with the vectors `w ∈ Kⁿ⁺¹` with `wᵢ = 1`.
* `MMP.Topology.continuous_toLineProjection`, `MMP.Topology.injective_toLineProjection`,
  `MMP.Topology.range_toLineProjection`.

## Implementation notes

The homogeneous coordinates are indexed by `Fin (n + 1)`, and the standard charts and their
affine coordinates are `MMP.UnderlyingSpace.projectiveSpaceStdChart` and
`MMP.UnderlyingSpace.projectiveSpaceStdCoord`. The model `ℙⁿ(ℂ)` of projection
matrices is `MMP.Topology.complexProjectiveSpace`, so that the homeomorphism needs no quotient
topology.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology HomogeneousLocalization
open MMP MMP.UnderlyingSpace Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace MMP.Topology

attribute [local instance] MvPolynomial.gradedAlgebra

section Charts

variable {K : Type u} [Field K] {n : ℕ}
  [(AlgebraicGeometry.Proj (polyGrading K n)).Over (Spec (.of K))]

/-- Every `K`-point of `ℙⁿ_K` lies in some standard chart `Uᵢ = {xᵢ ≠ 0}`. -/
lemma exists_top_le_preimage_projectiveSpaceStdChart
    (p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))) :
    ∃ i, ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i := by
  have hx : p.toHom (IsLocalRing.closedPoint K) ∈ ⨆ i, projectiveSpaceStdChart K n i := by
    rw [iSup_basicOpen_X_eq_top K n]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨i, (top_le_preimage_iff p _).mpr hi⟩

/-- At a `K`-point of the standard chart `Uᵢ`, the affine coordinate `xᵢ / xᵢ` evaluates to `1`. -/
@[simp]
lemma eval_projectiveSpaceStdCoord_self
    {p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))}
    {i : Fin (n + 1)} (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i) :
    eval p hp (projectiveSpaceStdCoord K n i i) = 1 := by
  rw [projectiveSpaceStdCoord_self, ← evalRingHom_apply, map_one]

/-- The vector of affine coordinates `(x_j / xᵢ)_j` of a point of `Uᵢ(K)` is nonzero. -/
lemma projectiveSpaceStdCoord_vector_ne_zero
    {p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))}
    {i : Fin (n + 1)} (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i) :
    (fun j ↦ eval p hp (projectiveSpaceStdCoord K n i j)) ≠ 0 :=
  Function.ne_iff.2 ⟨i, by simp [eval_projectiveSpaceStdCoord_self hp]⟩

/-- A `K`-point of the standard chart `Uᵢ` at which `x_k / xᵢ` does not vanish lies in the
standard chart `U_k`. -/
lemma top_le_preimage_of_eval_projectiveSpaceStdCoord_ne_zero
    {p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))} {i k : Fin (n + 1)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i)
    (h : eval p hp (projectiveSpaceStdCoord K n i k) ≠ 0) :
    ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n k := by
  have := (top_le_preimage_basicOpen_iff p hp _).mpr h
  rw [basicOpen_projectiveSpaceStdCoord] at this
  exact this.trans (Scheme.Hom.preimage_mono _ inf_le_right)

/-- At a `K`-point of `Uᵢ ∩ U_k`, the affine coordinates satisfy
`(x_j / xᵢ)(p) = (x_k / xᵢ)(p) · (x_j / x_k)(p)`. -/
lemma eval_projectiveSpaceStdCoord_mul
    {p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))}
    {i k : Fin (n + 1)} (hpi : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i)
    (hpk : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n k) (j : Fin (n + 1)) :
    eval p hpi (projectiveSpaceStdCoord K n i j) =
      eval p hpi (projectiveSpaceStdCoord K n i k) *
        eval p hpk (projectiveSpaceStdCoord K n k j) := by
  have hW : ⊤ ≤ p.toHom ⁻¹ᵁ Proj.basicOpen (polyGrading K n)
      (MvPolynomial.X i * MvPolynomial.X k) := by
    rw [Proj.basicOpen_mul]
    exact fun x hx ↦ ⟨hpi hx, hpk hx⟩
  have e1 := eval_restrict (Proj.basicOpen_mono (polyGrading K n) _ _
    ⟨MvPolynomial.X k, rfl⟩) p hW (projectiveSpaceStdCoord K n i j)
  have e2 := eval_restrict (Proj.basicOpen_mono (polyGrading K n) _ _
    ⟨MvPolynomial.X k, rfl⟩) p hW (projectiveSpaceStdCoord K n i k)
  have e3 := eval_restrict (Proj.basicOpen_mono (polyGrading K n) _ _
    ⟨MvPolynomial.X i, mul_comm _ _⟩) p hW (projectiveSpaceStdCoord K n k j)
  rw [← e1, ← e2, ← e3, projectiveSpaceStdCoord_mul, ← evalRingHom_apply, map_mul]
  rfl

/-- A `K`-point of `ℙⁿ_K` lying in the standard chart `Uᵢ` is the image of a `K`-point of `Uᵢ`. -/
lemma mem_range_mapFun_projectiveSpaceStdChart
    {p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))}
    {i : Fin (n + 1)} (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i) :
    p ∈ Set.range (mapFun (K := K) (projectiveSpaceStdChart K n i).ι) := by
  rwa [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]

/-- The standard chart `Uᵢ = {xᵢ ≠ 0}` of `ℙⁿ_K` is affine. -/
instance isAffine_projectiveSpaceStdChart (i : Fin (n + 1)) :
    IsAffine (projectiveSpaceStdChart K n i).toScheme :=
  Proj.isAffineOpen_basicOpen (polyGrading K n) (MvPolynomial.X i) (X_mem_one K n i) one_pos

/-- A point of the standard chart `Uᵢ(K)` of `ℙⁿ_K(K)` is determined by its affine coordinates
`x_j / xᵢ`. -/
lemma eq_of_eval_projectiveSpaceStdCoord_eq
    (hP : (AlgebraicGeometry.Proj (polyGrading K n) ↘ Spec (.of K)) = projToSpecCoeff K n)
    {p q : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n))} {i : Fin (n + 1)}
    (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i)
    (hq : ⊤ ≤ q.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i)
    (h : ∀ j, eval p hp (projectiveSpaceStdCoord K n i j) =
      eval q hq (projectiveSpaceStdCoord K n i j)) : p = q := by
  set U := projectiveSpaceStdChart K n i
  have hring : evalRingHom p hp = evalRingHom q hq := by
    refine RingHom.eq_of_eqOn_set_dense (closure_projectiveSpaceStdCoord hP i) ?_
    rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
    · simp only [evalRingHom_apply]
      rw [eval_structureRingHomOpens, eval_structureRingHomOpens]
    · simpa only [evalRingHom_apply] using h j
  obtain ⟨p', rfl⟩ := mem_range_mapFun_projectiveSpaceStdChart hp
  obtain ⟨q', rfl⟩ := mem_range_mapFun_projectiveSpaceStdChart hq
  congr 1
  refine UnderlyingSpace.ext (ext_of_isAffine ?_)
  ext a
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (U.ι.appLE U ⊤ U.ι_preimage_self.ge)).2 a
  have hb := RingHom.congr_fun hring b
  rw [evalRingHom_apply, evalRingHom_apply, eval_mapFun_ι, eval_mapFun_ι, evalTop_eq,
    evalTop_eq] at hb
  exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective hb

/-- Every vector `w ∈ Kⁿ⁺¹` with `wᵢ = 1` is the vector of affine coordinates `x_j / xᵢ` of a
point of the standard chart `Uᵢ(K)` of `ℙⁿ_K(K)`. -/
lemma exists_eval_projectiveSpaceStdCoord_eq
    (hP : (AlgebraicGeometry.Proj (polyGrading K n) ↘ Spec (.of K)) = projToSpecCoeff K n)
    (i : Fin (n + 1)) {w : Fin (n + 1) → K} (hw : w i = 1) :
    ∃ (p : UnderlyingSpace K (AlgebraicGeometry.Proj (polyGrading K n)))
      (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart K n i),
      ∀ j, eval p hp (projectiveSpaceStdCoord K n i j) = w j := by
  set U := projectiveSpaceStdChart K n i
  let φ := U.ι.appLE U ⊤ U.ι_preimage_self.ge
  let θ := (Proj.awayToSection (polyGrading K n) (MvPolynomial.X i)).hom
  have hθ : Function.Bijective θ := by
    have := ConcreteCategory.bijective_of_isIso
      (Proj.basicOpenIsoAway (polyGrading K n) (MvPolynomial.X i) (X_mem_one K n i) one_pos).hom
    rwa [Proj.basicOpenIsoAway_hom] at this
  let e := RingEquiv.ofBijective (φ.hom.comp θ) ((ConcreteCategory.bijective_of_isIso φ).comp hθ)
  let ψ : Away (polyGrading K n) (MvPolynomial.X i) →+* K :=
    (MvPolynomial.eval fun j : {j : Fin (n + 1) // j ≠ i} ↦ w j).comp (chartRetract K n i)
  have hψX : ∀ j, ψ (Away.mk (polyGrading K n) (X_mem_one K n i) 1 (MvPolynomial.X j)
      (X_mem_smul K n j)) = w j := by
    intro j
    simp only [ψ, RingHom.comp_apply, chartRetract_mk]
    by_cases hj : j = i
    · subst hj
      rw [setOneHom_X_self, map_one, hw]
    · rw [show (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K) =
        MvPolynomial.X (⟨j, hj⟩ : {j : Fin (n + 1) // j ≠ i}).1 from rfl, setOneHom_X_ne,
        MvPolynomial.eval_X]
  have hψC : ∀ c, ψ (coeffToAway K n i c) = c := by
    intro c
    simp only [ψ, RingHom.comp_apply, coeffToAway_eq_mk, chartRetract_mk, setOneHom_C,
      MvPolynomial.eval_C]
  let ρ : Γ(U.toScheme, ⊤) →+* K := ψ.comp e.symm.toRingHom
  have he : ∀ a, e a = φ (θ a) := fun _ ↦ rfl
  have hρ : ∀ c, ρ (structureRingHom K U.toScheme c) = c := by
    intro c
    rw [show structureRingHom K U.toScheme c = e (coeffToAway K n i c) by
      rw [he, structureRingHom_opens, RingHom.comp_apply,
        structureRingHomOpens_projectiveSpaceStdChart hP]]
    simp only [ρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.symm_apply_apply, hψC]
  let p' := ofRingHom ρ hρ
  have hp : ⊤ ≤ (mapFun (K := K) U.ι p').toHom ⁻¹ᵁ U := by
    have : mapFun (K := K) U.ι p' ∈ Set.range (mapFun (K := K) U.ι) := ⟨p', rfl⟩
    rwa [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι] at this
  refine ⟨mapFun U.ι p', hp, fun j ↦ ?_⟩
  have hy : φ (projectiveSpaceStdCoord K n i j) = e (Away.mk (polyGrading K n) (X_mem_one K n i)
      1 (MvPolynomial.X j) (X_mem_smul K n j)) := rfl
  rw [eval_mapFun_ι, hy, evalTop_ofRingHom]
  simp only [ρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, hψX]

end Charts

/-! ### The homeomorphism `ℙⁿ_ℂ(ℂ) ≅ ℙⁿ(ℂ)` -/

section Homeomorph

/-- For `v ≠ 0`, the `(i, i)` entry of the orthogonal projection onto `ℂ v` is nonzero if and only
if `vᵢ ≠ 0`. -/
lemma lineProjection_apply_self_ne_zero_iff {ι : Type*} [Fintype ι] {v : ι → ℂ} (hv : v ≠ 0)
    (i : ι) : lineProjection v i i ≠ 0 ↔ v i ≠ 0 := by
  simp only [lineProjection, ne_eq, div_eq_zero_iff, sum_mul_conj_ne_zero hv, or_false,
    mul_eq_zero, map_eq_zero, or_self]

variable {n : ℕ} [(AlgebraicGeometry.Proj (polyGrading ℂ n)).Over (Spec (.of ℂ))]

/-- The line of `ℂⁿ⁺¹` through a point `p ∈ ℙⁿ_ℂ(ℂ)`, as its orthogonal projection: the
projection onto the line spanned by the affine coordinates `(x_j / xᵢ)_j` of `p` in any standard
chart `Uᵢ` containing it (`toLineProjection_eq`). -/
def toLineProjection (p : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n))) :
    Fin (n + 1) → Fin (n + 1) → ℂ :=
  lineProjection fun j ↦ eval p (exists_top_le_preimage_projectiveSpaceStdChart p).choose_spec
    (projectiveSpaceStdCoord ℂ n (exists_top_le_preimage_projectiveSpaceStdChart p).choose j)

/-- For a point `p` of the standard chart `Uᵢ`, `toLineProjection p` is the orthogonal projection
onto the line spanned by the affine coordinates `((x_j / xᵢ)(p))_j`. -/
lemma toLineProjection_eq {p : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n))}
    {i : Fin (n + 1)} (hp : ⊤ ≤ p.toHom ⁻¹ᵁ projectiveSpaceStdChart ℂ n i) :
    toLineProjection p = lineProjection fun j ↦ eval p hp (projectiveSpaceStdCoord ℂ n i j) := by
  have hk := (exists_top_le_preimage_projectiveSpaceStdChart p).choose_spec
  set k := (exists_top_le_preimage_projectiveSpaceStdChart p).choose
  have hdef : toLineProjection p =
      lineProjection fun j ↦ eval p hk (projectiveSpaceStdCoord ℂ n k j) := rfl
  have hmul := eval_projectiveSpaceStdCoord_mul hk hp
  have hc : eval p hk (projectiveSpaceStdCoord ℂ n k i) ≠ 0 := by
    have := hmul k
    rw [eval_projectiveSpaceStdCoord_self] at this
    exact left_ne_zero_of_mul (this ▸ one_ne_zero)
  rw [hdef, show (fun j ↦ eval p hk (projectiveSpaceStdCoord ℂ n k j)) =
    eval p hk (projectiveSpaceStdCoord ℂ n k i) •
      fun j ↦ eval p hp (projectiveSpaceStdCoord ℂ n i j) from funext hmul,
    lineProjection_smul (projectiveSpaceStdCoord_vector_ne_zero hp) hc]

/-- `toLineProjection p` is the orthogonal projection onto a line of `ℂⁿ⁺¹`. -/
lemma toLineProjection_mem_lineProjections
    (p : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n))) :
    toLineProjection p ∈ lineProjections n :=
  lineProjection_mem_lineProjections (projectiveSpaceStdCoord_vector_ne_zero _)

/-- `toLineProjection` is continuous for the classical topology on `ℙⁿ_ℂ(ℂ)`. -/
lemma continuous_toLineProjection : Continuous (toLineProjection (n := n)) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  obtain ⟨i, hp⟩ := exists_top_le_preimage_projectiveSpaceStdChart p
  have hS := isOpen_setOf_le_preimage (K := ℂ) (projectiveSpaceStdChart ℂ n i)
  refine ContinuousOn.continuousAt ?_ (hS.mem_nhds hp)
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_lineProjection_comp
    (continuous_pi fun j ↦ continuous_eval _ (projectiveSpaceStdCoord ℂ n i j))
    fun q ↦ projectiveSpaceStdCoord_vector_ne_zero q.2).congr
      fun q ↦ (toLineProjection_eq q.2).symm

/-- `toLineProjection` is injective. -/
lemma injective_toLineProjection
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n) :
    Function.Injective (toLineProjection (n := n)) := by
  intro p q h
  obtain ⟨i, hp⟩ := exists_top_le_preimage_projectiveSpaceStdChart p
  obtain ⟨k, hk⟩ := exists_top_le_preimage_projectiveSpaceStdChart q
  have hv := projectiveSpaceStdCoord_vector_ne_zero hp
  have hpi : lineProjection (fun j ↦ eval p hp (projectiveSpaceStdCoord ℂ n i j)) i i ≠ 0 :=
    (lineProjection_apply_self_ne_zero_iff hv i).2 (by
      simp [eval_projectiveSpaceStdCoord_self hp])
  rw [← toLineProjection_eq hp, h, toLineProjection_eq hk,
    lineProjection_apply_self_ne_zero_iff (projectiveSpaceStdCoord_vector_ne_zero hk)] at hpi
  have hq := top_le_preimage_of_eval_projectiveSpaceStdCoord_ne_zero hk hpi
  rw [toLineProjection_eq hp, toLineProjection_eq hq] at h
  refine eq_of_eval_projectiveSpaceStdCoord_eq hP hp hq fun j ↦ ?_
  have e1 := lineProjection_div_apply hv (l := i) (by
    simp [eval_projectiveSpaceStdCoord_self hp]) j
  have e2 := lineProjection_div_apply (projectiveSpaceStdCoord_vector_ne_zero hq) (l := i) (by
    simp [eval_projectiveSpaceStdCoord_self hq]) j
  rw [h, e2, eval_projectiveSpaceStdCoord_self hp, eval_projectiveSpaceStdCoord_self hq,
    div_one, div_one] at e1
  exact e1.symm

/-- The range of `toLineProjection` is exactly the set `lineProjections n` of orthogonal
projections onto lines of `ℂⁿ⁺¹`. -/
lemma range_toLineProjection
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n) :
    Set.range (toLineProjection (n := n)) = lineProjections n := by
  refine subset_antisymm (Set.range_subset_iff.2 toLineProjection_mem_lineProjections) ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  replace hi : v i ≠ 0 := hi
  obtain ⟨p, hp, hpv⟩ := exists_eval_projectiveSpaceStdCoord_eq (n := n) hP i
    (w := (v i)⁻¹ • v) (by simp [hi])
  refine ⟨p, ?_⟩
  rw [toLineProjection_eq hp, show (fun j ↦ eval p hp (projectiveSpaceStdCoord ℂ n i j)) =
    (v i)⁻¹ • v from funext hpv, lineProjection_smul hv (inv_ne_zero hi)]

variable (n) in
/-- **The complex points of projective space.** The underlying space `ℙⁿ_ℂ(ℂ)` of the scheme
`ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]`, with its classical topology, is homeomorphic to complex projective
space `ℙⁿ(ℂ)`, realized as the space of orthogonal projections of `ℂⁿ⁺¹` onto its lines: a point
with affine coordinates `v = (x_j / xᵢ)_j` in a standard chart goes to the projection onto
`ℂ v`. -/
def underlyingSpaceProjectiveSpaceHomeomorph
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n) :
    UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n)) ≃ₜ complexProjectiveSpace n :=
  haveI := compactSpace_projectiveSpace (K := ℂ) n hP
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fun p ↦ (⟨toLineProjection p, toLineProjection_mem_lineProjections p⟩ :
      lineProjections n))
      ⟨fun p q h ↦ injective_toLineProjection hP (congrArg Subtype.val h), by
        rintro ⟨P, hP'⟩
        obtain ⟨p, rfl⟩ := (range_toLineProjection hP).ge hP'
        exact ⟨p, rfl⟩⟩)
    (continuous_toLineProjection.subtype_mk _)

/-- The homeomorphism `underlyingSpaceProjectiveSpaceHomeomorph` sends `p` to
`toLineProjection p`. -/
@[simp]
lemma coe_underlyingSpaceProjectiveSpaceHomeomorph_apply
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n)
    (p : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n))) :
    (underlyingSpaceProjectiveSpaceHomeomorph n hP p).1 = toLineProjection p :=
  rfl

variable (n) in
/-- **The complex realization of projective space.** `(ℙⁿ_ℂ)^an` is homeomorphic to complex
projective space `ℙⁿ(ℂ)`, realized as the space of orthogonal projections of `ℂⁿ⁺¹` onto its
lines. -/
def complexPointsProjectiveSpaceHomeomorph
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n) :
    MMP.Analytic.ComplexPoints (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) ≃ₜ
      complexProjectiveSpace n :=
  MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace.trans
    (underlyingSpaceProjectiveSpaceHomeomorph n hP)

end Homeomorph

end MMP.Topology
