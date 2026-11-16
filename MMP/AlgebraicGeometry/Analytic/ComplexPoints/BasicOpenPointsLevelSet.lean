module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AffinePointsLevelSet
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Points of a basic open of an affine scheme as a zero set

Let `X` be an affine scheme over a field `K` with ring of global sections `A = Γ(X, X)`, let
`g ∈ A`, and let `P` be a presentation `A_g = K[x_i]_{i ∈ ι} / (f_j)_{j ∈ σ}` of the localization
`A_g` as a `K`-algebra. The `K`-points `q` of `X` at which `g` does not vanish are exactly the
`K`-points of the basic open `D(g) = Spec A_g`: evaluation at `q` extends uniquely to `A_g`. So
evaluating the generators `x_i ∈ A_g` gives a map from `{q ∈ X(K) | g(q) ≠ 0}` to the common zero
set of the relations `f_j` in `K^ι`. When `K` is a topological field this is a homeomorphism: in
one direction the value of `a / g^k` is `a(q) / g(q)^k`, continuous where `g(q) ≠ 0`; in the
other the value of a global section is a polynomial in the coordinates.

This describes the classical topology near a point by equations, without passing through the
open subscheme `D(g)`.

## Main definitions

* `MMP.UnderlyingSpace.nonvanishingLocus K g`: the `K`-points where `g ≠ 0`.
* `MMP.UnderlyingSpace.awayEval`: evaluation `A_g → K` at a point of
  `nonvanishingLocus K g`.
* `MMP.UnderlyingSpace.awayFamily P`: the values of the generators of `P`.
* `MMP.UnderlyingSpace.ofZero`: the `K`-point attached to a common zero of the
  relations of `P`.
* `MMP.UnderlyingSpace.nonvanishingLocusHomeomorph`: the homeomorphism of
  `{g ≠ 0} ⊆ X(K)` with the zero set of the relations of `P`.
* `MMP.UnderlyingSpace.nonvanishingLocusHomeomorphLevelSet`: the same for
  `K = ℝ, ℂ`, onto the level set of the relation map of `P`.

## Main results

* `MMP.UnderlyingSpace.isOpen_nonvanishingLocus`: `{g ≠ 0}` is classically open.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))] [Algebra K Γ(X, ⊤)]

/-- Evaluation of global sections at a `K`-point, as a ring homomorphism. -/
abbrev evalTopRingHom (q : UnderlyingSpace K X) : Γ(X, ⊤) →+* K :=
  evalRingHom (U := ⊤) q (Scheme.Hom.preimage_top _).ge

/-- `evalTopRingHom q` sends a global section `a` to its value `evalTop q a`. -/
@[simp]
lemma evalTopRingHom_apply (q : UnderlyingSpace K X) (a : Γ(X, ⊤)) :
    evalTopRingHom q a = evalTop q a :=
  rfl

/-- A `K`-point of an affine scheme is determined by the values of the global sections. -/
lemma eq_of_forall_evalTop_eq [IsAffine X] {p q : UnderlyingSpace K X}
    (h : ∀ a, evalTop p a = evalTop q a) : p = q := by
  refine UnderlyingSpace.ext (ext_of_isAffine ?_)
  ext a
  have := h a
  rw [evalTop_eq, evalTop_eq] at this
  exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective this

variable (K) in
/-- The `K`-points of `X` at which the global section `g` does not vanish. -/
def nonvanishingLocus (g : Γ(X, ⊤)) : Set (UnderlyingSpace K X) :=
  {q | evalTop q g ≠ 0}

variable {g : Γ(X, ⊤)}

/-- Evaluation at a point where `g` does not vanish, extended to the localization `A_g`. -/
def awayEval (q : nonvanishingLocus K g) : Localization.Away g →+* K :=
  IsLocalization.Away.lift g (g := evalTopRingHom q.1) (isUnit_iff_ne_zero.mpr q.2)

/-- On the image of a global section `a` in `A_g`, `awayEval q` is the value of `a` at `q`. -/
@[simp]
lemma awayEval_algebraMap (q : nonvanishingLocus K g) (a : Γ(X, ⊤)) :
    awayEval q (algebraMap _ _ a) = evalTop q.1 a :=
  IsLocalization.lift_eq _ _

/-- `awayEval q` is the identity on the image of the scalars `K` in `A_g`. -/
lemma awayEval_algebraMap_field (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (q : nonvanishingLocus K g) (c : K) :
    awayEval q (algebraMap K (Localization.Away g) c) = c := by
  rw [IsScalarTower.algebraMap_apply K Γ(X, ⊤) (Localization.Away g), awayEval_algebraMap, hK,
    evalTop_structureRingHom]

/-- `awayEval q` of a polynomial `r` evaluated at elements `y i` of `A_g` is `r` evaluated at
the values `awayEval q (y i)`. -/
lemma awayEval_aeval (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X) {ι : Type*}
    (y : ι → Localization.Away g) (q : nonvanishingLocus K g) (r : MvPolynomial ι K) :
    awayEval q (aeval y r) = MvPolynomial.eval (fun i ↦ awayEval q (y i)) r := by
  induction r using MvPolynomial.induction_on with
  | C c => rw [aeval_C, awayEval_algebraMap_field hK, eval_C]
  | add r s hr hs => rw [map_add, map_add, hr, hs, map_add]
  | mul_X r i hr => rw [map_mul, map_mul, hr, aeval_X, map_mul, eval_X]

variable {ι σ : Type*}

/-- The values at `q` of the generators of a presentation of `A_g`. -/
def awayFamily (P : Algebra.Presentation K (Localization.Away g) ι σ)
    (q : nonvanishingLocus K g) : ι → K :=
  fun i ↦ awayEval q (P.val i)

/-- The values `awayFamily P q` of the generators are a common zero of the relations of `P`. -/
lemma eval_relation_awayFamily (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (q : nonvanishingLocus K g) (j : σ) :
    MvPolynomial.eval (awayFamily P q) (P.relation j) = 0 := by
  change MvPolynomial.eval (fun i ↦ awayEval q (P.val i)) (P.relation j) = 0
  rw [← awayEval_aeval hK, P.aeval_val_relation, map_zero]

/-- The common zeros of the relations of a presentation. -/
def zeroLocus (P : Algebra.Presentation K (Localization.Away g) ι σ) : Set (ι → K) :=
  {v | ∀ j, MvPolynomial.eval v (P.relation j) = 0}

/-- Evaluation at a common zero `v` of the relations of `P`, as a ring homomorphism
`A_g → K`. -/
def presentationEval (P : Algebra.Presentation K (Localization.Away g) ι σ) (v : zeroLocus P) :
    Localization.Away g →+* K :=
  (Ideal.Quotient.lift (RingHom.ker (aeval (R := K) P.val).toRingHom) (MvPolynomial.eval v.1)
      (fun r hr ↦ by
        change r ∈ RingHom.ker (aeval (R := K) P.val) at hr
        rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker] at hr
        have : Ideal.span (Set.range P.relation) ≤ RingHom.ker (MvPolynomial.eval v.1) := by
          rw [Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          exact v.2 j
        exact this hr)).comp
    (RingHom.quotientKerEquivOfSurjective
      (f := (aeval (R := K) P.val).toRingHom) P.aeval_val_surjective).symm.toRingHom

/-- `presentationEval P v` sends the image of a polynomial `r` under the generators of `P` to
the value of `r` at `v`. -/
@[simp]
lemma presentationEval_aeval (P : Algebra.Presentation K (Localization.Away g) ι σ)
    (v : zeroLocus P) (r : MvPolynomial ι K) :
    presentationEval P v (aeval P.val r) = MvPolynomial.eval v.1 r := by
  have h : (RingHom.quotientKerEquivOfSurjective (f := (aeval (R := K) P.val).toRingHom)
      P.aeval_val_surjective).symm (aeval P.val r) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [presentationEval, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h, Ideal.Quotient.lift_mk]

/-- `presentationEval P v` is the identity on the image of the scalars `K` in `A_g`. -/
lemma presentationEval_algebraMap_field (P : Algebra.Presentation K (Localization.Away g) ι σ)
    (v : zeroLocus P) (c : K) :
    presentationEval P v (algebraMap K (Localization.Away g) c) = c := by
  rw [← aeval_C (R := K) P.val c, presentationEval_aeval, eval_C]

/-- The ring homomorphism `A_g → K` of a `K`-point where `g` does not vanish is the evaluation
at the values of the generators. -/
lemma presentationEval_awayFamily (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (q : nonvanishingLocus K g) :
    presentationEval P ⟨awayFamily P q, eval_relation_awayFamily hK P q⟩ = awayEval q := by
  ext s
  obtain ⟨r, rfl⟩ := P.aeval_val_surjective s
  rw [presentationEval_aeval, awayEval_aeval hK]
  rfl

variable [IsAffine X]

/-- The `K`-point of `X` attached to a common zero `v` of the relations of `P`. -/
def ofZero (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (v : zeroLocus P) :
    UnderlyingSpace K X :=
  ofRingHom ((presentationEval P v).comp (algebraMap Γ(X, ⊤) (Localization.Away g))) fun c ↦ by
    rw [RingHom.comp_apply, ← hK, ← IsScalarTower.algebraMap_apply,
      presentationEval_algebraMap_field]

/-- The value of a global section `a` at `ofZero hK P v` is `presentationEval P v` of the image
of `a` in `A_g`. -/
lemma evalTop_ofZero (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (v : zeroLocus P) (a : Γ(X, ⊤)) :
    evalTop (ofZero hK P v) a = presentationEval P v (algebraMap _ _ a) :=
  evalTop_ofRingHom _ _ a

/-- The section `g` does not vanish at the point `ofZero hK P v`. -/
lemma ofZero_mem_nonvanishingLocus (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (v : zeroLocus P) :
    ofZero hK P v ∈ nonvanishingLocus K g := by
  change evalTop _ g ≠ 0
  rw [evalTop_ofZero]
  exact ((IsLocalization.Away.algebraMap_isUnit g).map _).ne_zero

/-- Evaluation on `A_g` at the point `ofZero hK P v` is `presentationEval P v`. -/
lemma awayEval_ofZero (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (v : zeroLocus P) :
    awayEval ⟨ofZero hK P v, ofZero_mem_nonvanishingLocus hK P v⟩ = presentationEval P v :=
  IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, awayEval_algebraMap, evalTop_ofZero])

/-- The values of the generators of `P` at the point `ofZero hK P v` are `v`. -/
lemma awayFamily_ofZero (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (v : zeroLocus P) :
    awayFamily P ⟨ofZero hK P v, ofZero_mem_nonvanishingLocus hK P v⟩ = v.1 :=
  funext fun i ↦ by
    rw [awayFamily, awayEval_ofZero, ← aeval_X (R := K) P.val i, presentationEval_aeval, eval_X]

/-- The point attached to the values `awayFamily P q` of the generators is `q`. -/
lemma ofZero_awayFamily (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (q : nonvanishingLocus K g) :
    ofZero hK P ⟨awayFamily P q, eval_relation_awayFamily hK P q⟩ = q.1 :=
  eq_of_forall_evalTop_eq fun a ↦ by
    rw [evalTop_ofZero, presentationEval_awayFamily hK, awayEval_algebraMap]

/-- The bijection between the `K`-points where `g` does not vanish and the common zeros of the
relations of a presentation of `A_g`. -/
def nonvanishingLocusEquiv (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) :
    nonvanishingLocus K g ≃ zeroLocus P where
  toFun q := ⟨awayFamily P q, eval_relation_awayFamily hK P q⟩
  invFun v := ⟨ofZero hK P v, ofZero_mem_nonvanishingLocus hK P v⟩
  left_inv q := Subtype.ext (ofZero_awayFamily hK P q)
  right_inv v := Subtype.ext (awayFamily_ofZero hK P v)

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] [T1Space K]

omit [Algebra K Γ(X, ⊤)] in
/-- The value of a fixed global section is a continuous function of the `K`-point. -/
lemma continuous_evalTop_apply (a : Γ(X, ⊤)) :
    Continuous fun q : UnderlyingSpace K X ↦ evalTop q a :=
  (continuous_apply a).comp (isInducing_evalTop (K := K) (X := X)).continuous

omit [Algebra K Γ(X, ⊤)] in
/-- The `K`-points where a global section does not vanish form a classically open set. -/
theorem isOpen_nonvanishingLocus (g : Γ(X, ⊤)) : IsOpen (nonvanishingLocus K g) :=
  isOpen_compl_singleton.preimage (continuous_evalTop_apply g)

/-- The value of a fixed element of `A_g` is a continuous function on the `K`-points where `g`
does not vanish. -/
lemma continuous_awayEval_apply (s : Localization.Away g) :
    Continuous fun q : nonvanishingLocus K g ↦ awayEval q s := by
  obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) s
  have hu : ∀ q : nonvanishingLocus K g, awayEval q (algebraMap _ _ (t : Γ(X, ⊤))) ≠ 0 :=
    fun q ↦ ((IsLocalization.map_units (Localization.Away g) t).map _).ne_zero
  have heq : ∀ q : nonvanishingLocus K g, awayEval q (IsLocalization.mk' _ a t) =
      evalTop q.1 a / evalTop q.1 t := fun q ↦ by
    rw [eq_div_iff (by simpa using hu q), ← awayEval_algebraMap, ← awayEval_algebraMap, ← map_mul,
      IsLocalization.mk'_spec]
  simp_rw [heq]
  exact ((continuous_evalTop_apply a).comp continuous_subtype_val).div
    ((continuous_evalTop_apply _).comp continuous_subtype_val) fun q ↦ by simpa using hu q

/-- The bijection `nonvanishingLocusEquiv hK P` is continuous. -/
lemma continuous_nonvanishingLocusEquiv (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) :
    Continuous (nonvanishingLocusEquiv hK P) :=
  (continuous_pi fun i ↦ continuous_awayEval_apply (P.val i)).subtype_mk _

/-- The inverse of the bijection `nonvanishingLocusEquiv hK P` is continuous. -/
lemma continuous_nonvanishingLocusEquiv_symm (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) :
    Continuous (nonvanishingLocusEquiv hK P).symm := by
  refine Continuous.subtype_mk ?_ _
  refine (isInducing_evalTop (K := K) (X := X)).continuous_iff.mpr (continuous_pi fun a ↦ ?_)
  obtain ⟨r, hr⟩ := P.aeval_val_surjective (algebraMap _ (Localization.Away g) a)
  have heq : ∀ v : zeroLocus P, evalTop (ofZero hK P v) a = MvPolynomial.eval v.1 r := fun v ↦ by
    rw [evalTop_ofZero, ← hr]
    exact presentationEval_aeval P v r
  change Continuous fun v : zeroLocus P ↦ evalTop (ofZero hK P v) a
  simp_rw [heq]
  exact (MvPolynomial.continuous_eval r).comp continuous_subtype_val

/-- **The `K`-points of a basic open as a zero set.** For a presentation `P` of `A_g`, evaluation
at the generators is a homeomorphism from the `K`-points where `g` does not vanish onto the
common zeros of the relations of `P` in `K^ι`. -/
def nonvanishingLocusHomeomorph (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) :
    nonvanishingLocus K g ≃ₜ zeroLocus P where
  toEquiv := nonvanishingLocusEquiv hK P
  continuous_toFun := continuous_nonvanishingLocusEquiv hK P
  continuous_invFun := continuous_nonvanishingLocusEquiv_symm hK P

/-- The image of `q` under `nonvanishingLocusHomeomorph hK P` is the family `awayFamily P q`. -/
@[simp]
lemma coe_nonvanishingLocusHomeomorph_apply (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K (Localization.Away g) ι σ) (q : nonvanishingLocus K g) :
    (nonvanishingLocusHomeomorph hK P q : ι → K) = awayFamily P q :=
  rfl

end Topology

end UnderlyingSpace

namespace UnderlyingSpace

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))] [IsAffine X]
  [Algebra 𝕜 Γ(X, ⊤)] {g : Γ(X, ⊤)} {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

/-- The common zeros of the relations of `P` form the level set of the relation map of `P`. -/
lemma zeroLocus_eq_levelSet (P : Algebra.Presentation 𝕜 (Localization.Away g) ι σ) :
    zeroLocus P = SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P) := by
  ext v
  simp only [zeroLocus, Set.mem_setOf_eq, SmoothLevelSet.levelSet, Set.mem_univ, true_and]
  exact ⟨fun h ↦ funext h, fun h j ↦ congrFun h j⟩

/-- For `𝕜 = ℝ, ℂ`, the `𝕜`-points where `g` does not vanish are homeomorphic to the level set
of the relation map of a presentation `P` of `A_g`. When `P` is submersive this level set is a
manifold of dimension `|ι| - |σ|` (`MMP.SmoothLevelSet.isManifold`,
`MMP.SubmersivePresentationLevelSet.isSubmersionOn_relMap`). -/
def nonvanishingLocusHomeomorphLevelSet (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 (Localization.Away g) ι σ) :
    nonvanishingLocus 𝕜 g ≃ₜ
      SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P) :=
  (nonvanishingLocusHomeomorph hK P).trans (Homeomorph.setCongr (zeroLocus_eq_levelSet P))

end UnderlyingSpace

end MMP
