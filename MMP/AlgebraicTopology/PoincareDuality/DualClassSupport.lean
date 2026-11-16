module

public import MMP.AlgebraicTopology.PoincareDuality.DualClass
public import MMP.AlgebraicTopology.CapProduct.SupportRetraction
/-!
# Dual classes with supports (Fulton, §19.1)

Let `M` be an oriented real `n`-manifold with fundamental class `μ_M ∈ H_n M`, `A ⊆ M` closed and
`a ∈ H_k A`. A class `c ∈ H^{n-k}(M, M - A)` is *dual to `a`* if `c ∩ μ_M = a`, the cap product
`H^{n-k}(M, M - A) ⊗ H_n M → H_k A` of [Fulton–MacPherson] 3.1.7. Poincaré–Alexander duality
says that, for `A` locally contractible, there is exactly one such class, written `cl^M(a)`.

For `A = M` this is the absolute notion `MMP.borelMooreHomology.IsDualClass`, once
`H_k M` is identified with `H_k` of the subspace `univ ⊆ M` along the inclusion
(`MMP.borelMooreHomology.isDualClassWithSupports_univ_iff`).

## Main definitions

* `MMP.borelMooreHomology.IsDualClassWithSupports`: `c ∈ H^{n-k}(M, M - A)` is dual
  to `a ∈ H_k A` with respect to `μ ∈ H_n M`, i.e. `c ∩ μ = a` in `H_k A`.

## Main results

* `MMP.hasProperNeighbourhoodDeformations_univ`: the whole space has proper
  neighbourhood deformations.
* `MMP.borelMooreHomology.IsDualClassWithSupports.congrDegree_capProduct_eq_pushforward`:
  if `c` is dual to `a ∈ H_k A`, then `c ∩ μ ∈ H_k M` (supports forgotten) is `ι_* a`.
* `MMP.borelMooreHomology.isDualClassWithSupports_univ_iff`: for `A = M` the two
  notions agree.
* `MMP.borelMooreHomology.IsDualClassWithSupports.add`, `.smul`, `.zero`,
  `.right_unique`.

## Implementation notes

The class `μ` is an argument; for Fulton's notion it is a fundamental class
(`MMP.IsFundamentalClass`) of an oriented manifold. The cap product into `H_* A`
(`MMP.borelMooreHomology.capProductSupport`) is defined when `A` has arbitrarily
small proper neighbourhood deformations (`MMP.HasProperNeighbourhoodDeformations`),
and the predicate carries that hypothesis. The cap product lands in degree `n - (n - k)`, which is
identified with `k` by `BorelMooreCross.congrDegree`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* W. Fulton, R. MacPherson, *Categorical framework for the study of singular spaces*, 3.1.7.
-/

@[expose] public noncomputable section

open CategoryTheory Set

universe u

namespace MMP

/-- The whole space has arbitrarily small proper neighbourhood deformations. -/
theorem hasProperNeighbourhoodDeformations_univ (Y : Type*) [TopologicalSpace Y] :
    HasProperNeighbourhoodDeformations (univ : Set Y) := fun M hM ↦ by
  rw [nhdsSet_univ, Filter.mem_top] at hM
  subst hM
  exact ⟨univ, isClosed_univ, by simp, subset_rfl, ContinuousMap.id _, isProperMap_id,
    fun _ _ ↦ rfl, ⟨fun q ↦ q.1.1, continuous_subtype_val.comp continuous_fst⟩,
    isClosed_univ.isClosedEmbedding_subtypeVal.isProperMap.comp isProperMap_fst_of_compactSpace,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ ↦ mem_univ _⟩

namespace borelMooreHomology

open BorelMooreCross

variable {R : Type u} [CommRing R] {M : TopCat.{u}} {A : Set M} {n : ℕ} {k : ℤ}

/-- Borel–Moore push-forward commutes with transport along an equality of degrees. -/
lemma pushforward_congrDegree {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : IsProperMap f) {i i' : ℤ}
    (h : i = i') (x : borelMooreHomology R (ModuleCat.of R R) X i) :
    (pushforward R (ModuleCat.of R R) f hf i').hom (congrDegree R X h x) =
      congrDegree R Y h ((pushforward R (ModuleCat.of R R) f hf i).hom x) := by
  subst h
  rfl

variable (R) in
/-- A class `c ∈ H^{n-k}(M, M - A)` is *dual* to `a ∈ H_k A` with respect to `μ ∈ H_n M`
(Fulton, §19.1, for `μ` the fundamental class of an oriented real `n`-manifold `M`) when
`c ∩ μ = a`, for the cap product `H^{n-k}(M, M - A) ⊗ H_n M → H_k A` of the closed subset `A`
with arbitrarily small proper neighbourhood deformations. -/
def IsDualClassWithSupports (hA : IsClosed A) (hAd : HasProperNeighbourhoodDeformations A)
    (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k) : Prop :=
  congrDegree R (TopCat.of A) (by omega) (capProductSupport R M hA hAd (n - k) n c μ) = a

section

variable {hA : IsClosed A} {hAd : HasProperNeighbourhoodDeformations A}
  {μ : borelMooreHomology R (ModuleCat.of R R) M n}

/-- `c` is dual to `a` exactly when `c ∩ μ = a` in `H_k A`. -/
lemma isDualClassWithSupports_iff
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k) :
    IsDualClassWithSupports R hA hAd μ c a ↔
      congrDegree R (TopCat.of A) (by omega) (capProductSupport R M hA hAd (n - k) n c μ) = a :=
  Iff.rfl

/-- Every class `c` is dual to `c ∩ μ ∈ H_k A`. -/
lemma isDualClassWithSupports_capProductSupport
    (c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)) :
    IsDualClassWithSupports R hA hAd μ c
      (congrDegree R (TopCat.of A) (by omega) (capProductSupport R M hA hAd (n - k) n c μ)) :=
  rfl

/-- The class to which `c` is dual is unique. -/
lemma IsDualClassWithSupports.right_unique
    {c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {a a' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
    (h : IsDualClassWithSupports R hA hAd μ c a) (h' : IsDualClassWithSupports R hA hAd μ c a') :
    a = a' :=
  h.symm.trans h'

/-- The zero class is dual to zero. -/
lemma IsDualClassWithSupports.zero :
    IsDualClassWithSupports R hA hAd μ
      (0 : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)) 0 := by
  simp [IsDualClassWithSupports]

/-- If `c` is dual to `a` and `c'` is dual to `a'`, then `c + c'` is dual to `a + a'`. -/
lemma IsDualClassWithSupports.add
    {c c' : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {a a' : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
    (h : IsDualClassWithSupports R hA hAd μ c a) (h' : IsDualClassWithSupports R hA hAd μ c' a') :
    IsDualClassWithSupports R hA hAd μ (c + c') (a + a') := by
  rw [IsDualClassWithSupports, map_add, LinearMap.add_apply, map_add]
  exact congrArg₂ (· + ·) h h'

/-- If `c` is dual to `a`, then `r • c` is dual to `r • a`. -/
lemma IsDualClassWithSupports.smul
    {c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
    (h : IsDualClassWithSupports R hA hAd μ c a) (r : R) :
    IsDualClassWithSupports R hA hAd μ (r • c) (r • a) := by
  rw [IsDualClassWithSupports, map_smul, LinearMap.smul_apply, map_smul]
  exact congrArg (r • ·) h

/-- **Forgetting the support.** If `c` is dual to `a ∈ H_k A`, then the cap product `c ∩ μ`,
computed in `H_k M`, is the push-forward `ι_* a` along the inclusion `ι : A → M`. -/
lemma IsDualClassWithSupports.congrDegree_capProduct_eq_pushforward
    {c : cohomologyWithSupports R (ModuleCat.of R R) M A (n - k)}
    {a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of A) k}
    (h : IsDualClassWithSupports R hA hAd μ c a) :
    congrDegree R M (by omega) (capProduct R M A (n - k) n c μ) =
      (pushforward R (ModuleCat.of R R) (subsetInclusion A) (isProperMap_subsetInclusion hA)
        k).hom a := by
  rw [← h, pushforward_congrDegree, pushforward_subsetInclusion_capProductSupport]

end

/-- Proper push-forward depends only on the map. -/
lemma pushforward_congr {X Y : TopCat.{u}} {f g : X ⟶ Y} (hfg : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (i : ℤ) :
    pushforward R (ModuleCat.of R R) f hf i = pushforward R (ModuleCat.of R R) g hg i := by
  subst hfg
  rfl

/-- The push-forward along the inclusion `univ ⊆ M` is injective (the inclusion is a
homeomorphism). -/
lemma pushforward_subsetInclusion_univ_injective (i : ℤ) :
    Function.Injective (pushforward R (ModuleCat.of R R) (subsetInclusion (univ : Set M))
      (isProperMap_subsetInclusion isClosed_univ) i).hom :=
  Function.LeftInverse.injective
    (pushforward_symm_pushforward_homeomorph (R := R) (M := ModuleCat.of R R)
      (Homeomorph.Set.univ M) i)

/-- **The case `A = M`.** With respect to `A = univ`, the class `c` is dual to `a ∈ H_k(univ)`
exactly when it is dual, in the absolute sense of `M`, to the image `ι_* a ∈ H_k M` of `a`
along the inclusion `ι : univ → M` (a homeomorphism). -/
theorem isDualClassWithSupports_univ_iff (μ : borelMooreHomology R (ModuleCat.of R R) M n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) M univ (n - k))
    (a : borelMooreHomology R (ModuleCat.of R R) (TopCat.of (univ : Set M)) k) :
    IsDualClassWithSupports R isClosed_univ (hasProperNeighbourhoodDeformations_univ M) μ c a ↔
      IsDualClass R μ c ((pushforward R (ModuleCat.of R R) (subsetInclusion (univ : Set M))
        (isProperMap_subsetInclusion isClosed_univ) k).hom a) := by
  refine ⟨fun h ↦ h.congrDegree_capProduct_eq_pushforward,
    fun h ↦ pushforward_subsetInclusion_univ_injective _ ?_⟩
  rwa [pushforward_congrDegree, pushforward_subsetInclusion_capProductSupport]

end borelMooreHomology

end MMP
