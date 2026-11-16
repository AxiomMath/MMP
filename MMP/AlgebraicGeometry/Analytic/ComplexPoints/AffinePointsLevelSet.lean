module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyAffine
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.SubmersivePresentationLevelSet

/-!
# Points of a presented affine scheme form the zero set of its relations

Let `X` be an affine scheme over a field `K` and let `P` be a presentation
`Γ(X, X) = K[x_i]_{i ∈ ι} / (f_j)_{j ∈ σ}` of its ring of global sections as a `K`-algebra. A
`K`-point `p` of `X` is a `K`-algebra homomorphism `Γ(X, X) → K`, so it is determined by the
values `x_i(p)`, and a vector `v ∈ K^ι` arises in this way exactly when every relation vanishes
at `v`. When `K` is a Hausdorff topological field, evaluation at the generators is therefore a
homeomorphism from `X(K)` onto the zero set `{v ∈ K^ι | f_j(v) = 0 for all j}`.

## Main results

* `MMP.UnderlyingSpace.evalTop_aeval`: the value at `p` of the image of a polynomial `q` under
  `x_i ↦ y_i` is `q` evaluated at the values `y_i(p)`.
* `MMP.UnderlyingSpace.range_evalFamily_val`: the image of evaluation at the generators of a
  presentation is the common zero set of the relations.
* `MMP.UnderlyingSpace.isClosedEmbedding_evalFamily_val`: evaluation at the generators of a
  presentation is a closed embedding `X(K) → K^ι`.
* `MMP.UnderlyingSpace.homeomorphLevelSet`: for `K = ℝ, ℂ`, the homeomorphism of `X(K)` with the
  zero set of the relations in `K^ι`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology MvPolynomial

universe u

namespace MMP

namespace UnderlyingSpace

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  [Algebra K Γ(X, ⊤)]

/-- The value at `p` of `q(y)`, for a polynomial `q` and global sections `y_i`, is `q` evaluated
at the values `y_i(p)`, provided the algebra structure of `Γ(X, X)` is the structure map. -/
theorem evalTop_aeval (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X) {ι : Type*}
    (y : ι → Γ(X, ⊤)) (p : UnderlyingSpace K X) (q : MvPolynomial ι K) :
    evalTop p (aeval y q) = MvPolynomial.eval (evalFamily y p) q := by
  have hring : ∀ a, evalTop p a = evalRingHom (U := ⊤) p (Scheme.Hom.preimage_top _).ge a :=
    fun _ ↦ rfl
  induction q using MvPolynomial.induction_on with
  | C a => rw [aeval_C, hK, evalTop_structureRingHom, eval_C]
  | add q r hq hr => rw [map_add, hring, map_add, ← hring, ← hring, hq, hr, map_add]
  | mul_X q i hq =>
    rw [map_mul, hring, map_mul, ← hring, ← hring, hq, aeval_X, map_mul, eval_X]
    rfl

variable {ι σ : Type*}

/-- The values of the generators of a presentation at a `K`-point satisfy the relations. -/
theorem eval_relation_evalFamily_val (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K Γ(X, ⊤) ι σ) (p : UnderlyingSpace K X) (j : σ) :
    MvPolynomial.eval (evalFamily P.val p) (P.relation j) = 0 := by
  rw [← evalTop_aeval hK, P.aeval_val_relation, evalTop, ← evalRingHom_apply, map_zero]

/-- The generators of a presentation generate `Γ(X, X)` as a ring together with `K`. -/
theorem closure_range_val (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K Γ(X, ⊤) ι σ) :
    Subring.closure (Set.range (structureRingHom K X) ∪ Set.range P.val) = ⊤ := by
  rw [← hK, ← Algebra.adjoin_eq_ring_closure, Algebra.adjoin_range_eq_range_aeval,
    (AlgHom.range_eq_top _).mpr P.aeval_val_surjective, Algebra.top_toSubring]

/-- A vector at which every relation of a presentation of `Γ(X, X)` vanishes is the family of
values of the generators at some `K`-point. -/
theorem exists_evalFamily_val_eq [IsAffine X] (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K Γ(X, ⊤) ι σ) {v : ι → K}
    (hv : ∀ j, MvPolynomial.eval v (P.relation j) = 0) :
    ∃ p : UnderlyingSpace K X, evalFamily P.val p = v := by
  have hker : ∀ q ∈ RingHom.ker (aeval (R := K) P.val).toRingHom,
      MvPolynomial.eval v q = 0 := fun q hq ↦ by
    change q ∈ RingHom.ker (aeval (R := K) P.val) at hq
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker] at hq
    exact (Ideal.span_le (I := RingHom.ker (MvPolynomial.eval v))).mpr
      (Set.range_subset_iff.mpr hv) hq
  let e := RingHom.quotientKerEquivOfSurjective
    (f := (aeval (R := K) P.val).toRingHom) P.aeval_val_surjective
  let ψ : Γ(X, ⊤) →+* K :=
    (Ideal.Quotient.lift _ (MvPolynomial.eval v) hker).comp e.symm.toRingHom
  have hψ : ∀ q, ψ (aeval P.val q) = MvPolynomial.eval v q := fun q ↦ by
    change Ideal.Quotient.lift _ (MvPolynomial.eval v) hker (e.symm (e (Ideal.Quotient.mk _ q))) = _
    rw [RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
  have hψK : ∀ c, ψ (structureRingHom K X c) = c := fun c ↦ by
    rw [← hK, ← aeval_C (R := K) P.val c, hψ, eval_C]
  refine ⟨ofRingHom ψ hψK, funext fun i ↦ ?_⟩
  change evalTop (ofRingHom ψ hψK) (P.val i) = v i
  rw [evalTop_ofRingHom, ← aeval_X (R := K) P.val i, hψ, eval_X]

/-- The image of evaluation at the generators of a presentation of `Γ(X, X)` is the set of
common zeros of the relations. -/
theorem range_evalFamily_val [IsAffine X] (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X)
    (P : Algebra.Presentation K Γ(X, ⊤) ι σ) :
    Set.range (evalFamily (K := K) P.val) = {v | ∀ j, MvPolynomial.eval v (P.relation j) = 0} :=
  Set.ext fun _ ↦ ⟨by rintro ⟨p, rfl⟩; exact eval_relation_evalFamily_val hK P p,
    exists_evalFamily_val_eq hK P⟩

/-- Evaluation at the generators of a presentation of `Γ(X, X)` is a closed embedding
`X(K) → K^ι`, for `K` a Hausdorff topological field. -/
theorem isClosedEmbedding_evalFamily_val [TopologicalSpace K] [IsTopologicalRing K]
    [ContinuousInv₀ K] [T2Space K] [IsAffine X]
    (hK : algebraMap K Γ(X, ⊤) = structureRingHom K X) (P : Algebra.Presentation K Γ(X, ⊤) ι σ) :
    IsClosedEmbedding (evalFamily (K := K) P.val) :=
  isClosedEmbedding_evalFamily _ (closure_range_val hK P)

end UnderlyingSpace

namespace UnderlyingSpace

variable {𝕜 : Type u} [RCLike 𝕜] {X : Scheme.{u}} [X.Over (Spec (.of 𝕜))] [IsAffine X]
  [Algebra 𝕜 Γ(X, ⊤)] {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

/-- Evaluation at the generators of a presentation `P` of `Γ(X, X)` lands in the zero set of the
relation map of `P`. -/
theorem evalFamily_val_mem_levelSet (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 Γ(X, ⊤) ι σ) (p : UnderlyingSpace 𝕜 X) :
    evalFamily P.val p ∈
      SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P) :=
  ⟨Set.mem_univ _, funext fun j ↦ eval_relation_evalFamily_val hK P p j⟩

/-- The image of evaluation at the generators of `P` is the zero set of the relation map. -/
theorem range_evalFamily_val_eq_levelSet (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 Γ(X, ⊤) ι σ) :
    Set.range (evalFamily (K := 𝕜) P.val) =
      SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P) := by
  rw [range_evalFamily_val hK P]
  ext v
  simp only [Set.mem_setOf_eq, SmoothLevelSet.levelSet, Set.mem_univ, true_and]
  exact ⟨fun h ↦ funext h, fun h j ↦ congrFun h j⟩

/-- The `𝕜`-points of an affine scheme with a presentation `P` of its global sections are
homeomorphic, through evaluation at the generators, to the zero set in `𝕜^ι` of the relations
of `P`. -/
def homeomorphLevelSet (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 Γ(X, ⊤) ι σ) :
    UnderlyingSpace 𝕜 X ≃ₜ
      SmoothLevelSet.levelSet Set.univ (SubmersivePresentationLevelSet.relMap P) :=
  ((isClosedEmbedding_evalFamily_val hK P).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (range_evalFamily_val_eq_levelSet hK P))

/-- The image of a `𝕜`-point `p` under `homeomorphLevelSet hK P` is the family of values at `p`
of the generators of `P`. -/
@[simp]
theorem coe_homeomorphLevelSet_apply (hK : algebraMap 𝕜 Γ(X, ⊤) = structureRingHom 𝕜 X)
    (P : Algebra.Presentation 𝕜 Γ(X, ⊤) ι σ) (p : UnderlyingSpace 𝕜 X) :
    (homeomorphLevelSet hK P p : ι → 𝕜) = evalFamily P.val p :=
  rfl

end UnderlyingSpace

end MMP
