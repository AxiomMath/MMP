module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.Isomorphism
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Pushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ChowGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import MMP.AlgebraicTopology.BorelMoore.IsoDisjointUnionGeneric
public import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ClassicalTopologyCharts
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenImmersionRange

/-!
# Disjoint unions of schemes whose cycle class map is an isomorphism (Fulton, Example 19.1.11(b))

Let a complex scheme `X` be the disjoint union of finitely many open and closed subschemes
`X_l`, with inclusions `ι_l`. If `cl_{X_l} : A_* X_l → H_* X_l` is an isomorphism for every `l`,
so is `cl_X`, for the cycle class map `MMP.Chow.chowCycleClass` on Stacks' Chow groups.

*Proof* (Fulton). Every class of `A_k X` is a sum `∑_l ι_{l*} c_l`, `∑_l ι_{l*}` is an
isomorphism on homology, and `cl ∘ ι_{l*} = ι_{l*} ∘ cl`
(`MMP.Chow.chowCycleClass_properChowPushforward_of_isProper`).

## Main results

* `MMP.Chow.exists_sum_properPushforward_eq`: every `k`-cycle on `X` is `∑_l ι_{l*} c_l`, with
  `c_l` a `k`-cycle on `X_l` for its own structure morphism.
* `MMP.Chow.exists_sum_properChowPushforward_eq`: the same on Chow groups.
* `MMP.Chow.exists_res_piecePushforward`: the push-forwards `ι_{l*}` on Borel–Moore homology have
  restrictions `res_l` with `res_l ∘ ι_{l*} = id`, `res_m ∘ ι_{l*} = 0` for `l ≠ m`, and
  `∑_l ι_{l*} ∘ res_l = id`.
* `MMP.Chow.ChowCycleClassIsIso.of_disjoint_union`: **Fulton, Example 19.1.11(b)**.

## Implementation notes

On the Chow side the piece `U l` carries its own structure morphism `U l ↘ Spec ℂ`, equal to
`(U l).ι ≫ X ↘ Spec ℂ` by `comp_over` but not by definition; the restriction lemmas of Stacks
(`Stacks.Chow.opensRestrictCycle_properPushforward_self` and `_of_disjoint`) are stated for the
composite, so `exists_sum_properPushforward_eq` substitutes the structure morphisms away.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.11.
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Function Stacks.Chow

namespace MMP.Chow

section pieces

variable (C : ChowSituation.{0}) {X : Scheme.{0}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  {ι : Type} [Fintype ι] {U : ι → X.Opens} (h : IsClopenDecomposition U)
  (s : ∀ l, (U l).toScheme ⟶ C.S) [∀ l, LocallyOfFiniteType (s l)] (hs : ∀ l, (U l).ι ≫ f = s l)
  [∀ l, IsProper (U l).ι]

include h hs in
/-- **Every cycle is the sum of the push-forwards of its pieces.** For a finite decomposition of
`X` into open and closed subschemes `U l`, each with a structure morphism `s l` equal to
`(U l).ι ≫ f`, every `k`-cycle `c` on `X` is `∑_l (U l).ι_* c_l` for `k`-cycles `c_l` on `U l`. -/
theorem exists_sum_properPushforward_eq (k : ℤ) (c : CycleGroup C f k) :
    ∃ cl : ∀ l, CycleGroup C (s l) k,
      ∑ l, properPushforward C (s l) f (U l).ι (hs l) k (cl l) = c := by
  classical
  obtain rfl : (fun l ↦ (U l).ι ≫ f) = s := funext hs
  refine ⟨fun l ↦ ⟨opensRestrictCycle (U l) c.1,
    opensRestrictCycle_mem_cyclesOfDimension C f (U l) k c.2⟩, ?_⟩
  refine (cycleGroupClopenEquiv C f h k).injective (funext fun m ↦ ?_)
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single m (fun l _ hlm ↦ Subtype.ext
      (opensRestrictCycle_properPushforward_of_disjoint C f (U l) (U m)
        (h.disjoint l m hlm) k _)) (by simp)]
  exact Subtype.ext (opensRestrictCycle_properPushforward_self C f (U m) k _)

include h hs in
/-- **Every Chow class is the sum of the push-forwards of classes on the pieces.** For a finite
decomposition of `X` into open and closed subschemes `U l`, each with a structure morphism `s l`
equal to `(U l).ι ≫ f`, every `a ∈ A_k(X)` is `∑_l (U l).ι_* a_l` for classes `a_l ∈ A_k(U l)`. -/
theorem exists_sum_properChowPushforward_eq (k : ℤ)
    (hfac : ∀ l, ProperPushforwardFactorsThroughRationalEquivalence C (s l) f (U l).ι (hs l) k)
    (a : chowGroup C f k) :
    ∃ al : ∀ l, chowGroup C (s l) k,
      ∑ l, properChowPushforward C (s l) f (U l).ι (hs l) k (hfac l) (al l) = a := by
  induction a using QuotientAddGroup.induction_on with
  | H c =>
    obtain ⟨cl, hcl⟩ := exists_sum_properPushforward_eq C f h s hs k c
    refine ⟨fun l ↦ QuotientAddGroup.mk' (rationalEquivalences C (s l) k) (cl l), ?_⟩
    simp only [properChowPushforward_mk]
    rw [← map_sum]
    exact congrArg _ hcl

end pieces

variable {R : Type} [CommRing R] {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

section homology

open UnderlyingSpace borelMooreHomology

variable {ι : Type} {U : ι → X.Opens} [∀ l, (U l).toScheme.Over (Spec (.of ℂ))]
  [∀ l, (U l).ι.IsOver (Spec (.of ℂ))]

omit [IsComplexScheme X] in
/-- The complex points of the pieces of a clopen decomposition are pairwise disjoint. -/
theorem pairwise_disjoint_opensRangeMap_ι (hdec : IsClopenDecomposition U) :
    Pairwise (Disjoint on fun l ↦ (opensRangeMap (U l).ι : Set (UnderlyingSpace ℂ X))) := by
  intro l m hlm
  refine Set.disjoint_left.2 fun p hl hm ↦ ?_
  rw [SetLike.mem_coe, mem_opensRangeMap_ι_iff] at hl hm
  exact Set.disjoint_left.1 (TopologicalSpace.Opens.coe_disjoint.2 (hdec.disjoint l m hlm)) hl hm

omit [IsComplexScheme X] in
/-- The complex points of the pieces of a clopen decomposition cover the complex points. -/
theorem exists_mem_opensRangeMap_ι (hdec : IsClopenDecomposition U) (p : UnderlyingSpace ℂ X) :
    ∃ l, p ∈ opensRangeMap (U l).ι := by
  obtain ⟨l, hl⟩ := hdec.exists_mem (p.toHom (IsLocalRing.closedPoint ℂ))
  exact ⟨l, (mem_opensRangeMap_ι_iff (U l) p).2 hl⟩

variable [∀ l, IsProper (U l).ι]

variable (R U) in
/-- The push-forward `ι_{l*}` on Borel–Moore homology along the inclusion of a piece. -/
abbrev piecePushforward (j : ℤ) (l : ι) :
    borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (U l).toScheme)) j →+
      borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) j :=
  (borelMooreHomology.pushforward R (ModuleCat.of R R)
    (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (U l).ι))
    (UnderlyingSpace.isProperMap_map (K := ℂ) (U l).ι) j).hom.toAddMonoidHom

/-- **Homology of a disjoint union.** For a finite decomposition of `X` into open and closed
subschemes `U l`, the push-forwards `ι_{l*}` admit restrictions `res_l` with `res_l ∘ ι_{l*} = id`,
`res_m ∘ ι_{l*} = 0` for `l ≠ m`, and `∑_l ι_{l*} ∘ res_l = id`. -/
theorem exists_res_piecePushforward [Fintype ι] (hdec : IsClopenDecomposition U) (j : ℤ) :
    ∃ res : ∀ l, borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ X)) j →+
        borelMooreHomology R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ (U l).toScheme)) j,
      (∀ l x, res l (piecePushforward R U j l x) = x) ∧
      (∀ l m, l ≠ m → ∀ x, res m (piecePushforward R U j l x) = 0) ∧
      ∀ y, ∑ l, piecePushforward R U j l (res l y) = y := by
  classical
  set M := ModuleCat.of R R
  set Y : TopCat := TopCat.of (UnderlyingSpace ℂ X)
  set V : ι → TopologicalSpace.Opens Y := fun l ↦ opensRangeMap (U l).ι
  have hdisj : Pairwise (Disjoint on fun l ↦ (V l : Set Y)) :=
    pairwise_disjoint_opensRangeMap_ι hdec
  have hcover : ∀ p : Y, ∃ l, p ∈ V l := exists_mem_opensRangeMap_ι hdec
  have hf := isProperMap_clopenInclusion V hdisj hcover
  let e : ∀ l, UnderlyingSpace ℂ (U l).toScheme ≃ₜ V l := fun l ↦ homeomorphOpensRangeMap (U l).ι
  let res : ∀ l, borelMooreHomology R M Y j →+
      borelMooreHomology R M (TopCat.of (UnderlyingSpace ℂ (U l).toScheme)) j := fun l ↦
    ((pushforward R M (TopCat.ofHom ((e l).symm : C(V l, UnderlyingSpace ℂ (U l).toScheme)))
      (e l).symm.isProperMap j).hom ∘ₗ (restrict R M (V l) j).hom).toAddMonoidHom
  have hpush : ∀ l x, piecePushforward R U j l x =
      (pushforward R M (clopenInclusion (V l)) (hf l) j).hom
        ((pushforward R M (TopCat.ofHom (e l : C(UnderlyingSpace ℂ (U l).toScheme, V l)))
          (e l).isProperMap j).hom x) := by
    intro l x
    change (pushforward R M (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (U l).ι))
      (UnderlyingSpace.isProperMap_map (K := ℂ) (U l).ι) j).hom x = _
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    rfl
  refine ⟨res, fun l x ↦ ?_, fun l m hlm x ↦ ?_, fun y ↦ ?_⟩
  · change (pushforward R M _ _ j).hom
      ((restrict R M (V l) j).hom (piecePushforward R U j l x)) = x
    rw [hpush, ← ModuleCat.comp_apply (pushforward R M (clopenInclusion (V l)) (hf l) j),
      pushforward_restrict_self R M (V l) (isClopen_of_disjoint_cover V hdisj hcover l),
      ModuleCat.id_apply]
    exact pushforward_symm_pushforward_homeomorph R M (e l) j x
  · change (pushforward R M _ _ j).hom
      ((restrict R M (V m) j).hom (piecePushforward R U j l x)) = 0
    rw [hpush, ← ModuleCat.comp_apply (pushforward R M (clopenInclusion (V l)) (hf l) j),
      pushforward_restrict_of_disjoint R M (V l) (V m)
        (isClopen_of_disjoint_cover V hdisj hcover m) (hdisj hlm)]
    simp
  · have hs := congrArg (fun f ↦ f.hom y) (sum_restrict_pushforward R M V hdisj hcover hf j)
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_coe, id_eq] at hs
    refine Eq.trans (Finset.sum_congr rfl fun l _ ↦ ?_) hs
    change piecePushforward R U j l
      ((pushforward R M _ _ j).hom ((restrict R M (V l) j).hom y)) = _
    rw [hpush]
    congr 1
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    have : TopCat.ofHom ((e l).symm : C(V l, UnderlyingSpace ℂ (U l).toScheme)) ≫
        TopCat.ofHom (e l : C(UnderlyingSpace ℂ (U l).toScheme, V l)) = 𝟙 _ :=
      TopCat.ext fun x ↦ (e l).apply_symm_apply x
    simp only [this, pushforward_id]
    rfl

end homology

/-- **Fulton, Example 19.1.11(b), disjoint unions, on Stacks' Chow groups.** Let a complex
scheme `X` be the disjoint union of finitely many open and closed subschemes `U l` (pairwise
disjoint open subschemes covering `X`, each a complex scheme through a structure over `ℂ` making
its inclusion a morphism over `ℂ`). If `cl_{U l}` is an isomorphism for every `l`, then `cl_X` is
an isomorphism. -/
theorem ChowCycleClassIsIso.of_disjoint_union {ι : Type} [Finite ι]
    (U : ι → X.Opens) [∀ l, (U l).toScheme.Over (Spec (.of ℂ))]
    [∀ l, (U l).ι.IsOver (Spec (.of ℂ))] (hU : ∀ l m, l ≠ m → Disjoint (U l) (U m))
    (hcov : ⨆ l, U l = ⊤) (h : ∀ l, ChowCycleClassIsIso R (U l).toScheme) :
    ChowCycleClassIsIso R X := by
  have := Fintype.ofFinite ι
  have hdec : IsClopenDecomposition U := ⟨hU, hcov⟩
  have := hdec.isProper_ι
  let C := fieldChowSituation ℂ
  have hfac : ∀ (k : ℤ) l, ProperPushforwardFactorsThroughRationalEquivalence C
      ((U l).toScheme ↘ Spec (.of ℂ)) (X ↘ Spec (.of ℂ)) (U l).ι (comp_over (U l).ι _) k :=
    fun k l ↦ properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ (U l).ι
      (comp_over (U l).ι _) k
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · obtain ⟨res, hself, hne, hH⟩ := exists_res_piecePushforward (R := R) hdec (2 * k : ℕ)
    exact MMP.bijective_of_sum_decomposition
      (inc := fun l ↦ properChowPushforward C _ _ (U l).ι (comp_over (U l).ι _) k (hfac k l))
      (cll := fun l ↦ chowCycleClass (X := (U l).toScheme) R k)
      (push := piecePushforward R U (2 * k : ℕ)) (res := res)
      (fun l a ↦ chowCycleClass_properChowPushforward R (U l).ι (hfac k l) a) hself hne
      (exists_sum_properChowPushforward_eq C _ hdec _ (fun l ↦ comp_over (U l).ι _) k
        (hfac k)) hH fun l ↦ (h l).1 k
  · exact MMP.subsingleton_of_sum_decomposition
      (exists_res_piecePushforward (R := R) hdec _).choose_spec.2.2 fun l ↦ (h l).2 k

end MMP.Chow
