module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.Descent

/-!
# Nef-model equivalence is unchanged by refinement

Let `f : X' ⟶ X` be a projective birational morphism of normal varieties over a base `S`, and let
`D₁`, `D₂` be `ℝ`-Cartier divisors on `X`, nef over `S`, with pull-backs `f^*D₁`, `f^*D₂`. A
curve `Γ' ⊆ X'` over a point of `S` has `f^*D_i · Γ' = 0` exactly when `f(Γ')` is a point or
`D_i · f(Γ') = 0`, and every curve of `X` over a point of `S` is the image of a curve of `X'`,
whose degree is multiplied by a positive integer by the projection formula. Hence `D₁` and `D₂`
have the same zero-degree curves over `S` if and only if `f^*D₁` and `f^*D₂` do.

Consequently equivalence of nef real models (`MMP.Fourfold.IsNefModelEquivalent`) is an
equivalence relation: it is symmetric, and, over a field of characteristic zero (where common
smooth projective resolutions exist), reflexive and transitive. It can be tested on any common
higher projective model: two equivalent nef models have the same zero-degree curves on every
common projective birational model, and conversely, in characteristic zero, agreement on one
such model implies equivalence.

## Main definitions

* `MMP.Mori.specFunctionFieldMap`: the morphism `Spec k(W) ⟶ Spec k(X)` induced by a dominant
  morphism `W ⟶ X` of integral schemes.

## Main results

* `MMP.Fourfold.isNefModelEquivalent_equivalence_and_refinement`.
* `MMP.Mori.RationalMap.IsInverse.isBirational_compHom`: if `h` is an inverse of `p : W ⟶ X` and
  `q : W ⟶ Y` is birational, then `q ∘ h` is birational.
* `MMP.Mori.RationalMap.IsInverse.compHom_comp_eq`: refining a common model `W` by a dominant
  `w : V ⟶ W` does not change the rational map it computes.
* `MMP.Mori.RationalMap.IsInverse.compHom_eq_id`: `p ∘ h` is the identity for an inverse `h`
  of `p`.

## Implementation notes

"`D · Γ = 0`" for an `ℝ`-Cartier divisor `D` means that every presentation `D = ∑ rⱼ Lⱼ` computes
`D · Γ = 0` (`MMP.Flips.IsRIntersectionNumber`), as in `MMP.Fourfold.IsNefModelEquivalent`.
Pull-backs are `MMP.Flips.IsRCartierPullback` and nefness over `S` is
`MMP.Flips.IsRelativelyNef`. The composite of the birational maps in the transitivity statement
is Mathlib's `AlgebraicGeometry.Scheme.RationalMap.comp`, which needs the first map to be
dominant; this is recorded as an instance argument (it follows from birationality). The common
higher model on which equivalence is tested is only required to be a normal variety, not smooth.
In parts (2)–(4) the base `S` is separated over `k`: over a non-separated base two morphisms to
`S` that agree on a dense open need not agree, so a curve contracted over `S` on one model need
not be contracted on the other, and symmetry and transitivity fail.

Proof outline. Let `f : X' ⟶ X` be a proper birational morphism of normal varieties over a field
`k` and `D` an `ℝ`-Cartier divisor on `X` with pull-back `f^*D`. For a proper curve `Γ' ⊆ X'` the
projection formula gives `f^*D · Γ' = 0` when `f(Γ')` is a point and
`f^*D · Γ' = [k(Γ') : k(f Γ')] · D · f(Γ')` when `f(Γ')` is a curve; the field degree is positive.
Every proper curve of `X` is the image of a proper curve of `X'`: the closure of a point closed in
the fibre over its generic point. Hence two `ℝ`-Cartier divisors have the same zero-degree curves
over a base exactly when their pull-backs do.

A rational map `ψ : Z₁ ⤏ Z₂` from an integral scheme is determined by `Spec k(Z₁) ⟶ Z₂`. On a
common model `p : W ⟶ Z₁`, `q : W ⟶ Z₂` with `p` birational and `ψ = q ∘ p⁻¹`, this morphism is
`Spec k(W) ⟶ W ⟶ Z₂` read through the isomorphism `k(Z₁) ≅ k(W)`. This turns symmetry,
reflexivity, transitivity and the comparison of two common models into identities of morphisms
out of spectra of function fields. Two common models `W`, `W₀` have the same image in
`Z₁ ×_k Z₂`, the closure of the image of the generic point, so every curve of `W` not contracted
to a point of `Z₁ ×_k Z₂` has a curve of `W₀` with the same images in `Z₁` and `Z₂`.

The common smooth projective models needed for reflexivity, transitivity and the converse
comparison are produced by
`MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq` (characteristic
zero). Testing on a given common model works over any field: it only uses the projection formula
on that model and on the model recorded by the equivalence, compared through `Z₁ ×_k Z₂`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-! ### Rational maps through function fields -/

namespace MMP.Mori

variable {V W X Y : Scheme.{u}}

/-- The morphism `Spec k(W) ⟶ Spec k(X)` induced by a dominant morphism `p : W ⟶ X` of integral
schemes. -/
noncomputable def specFunctionFieldMap (p : W ⟶ X) [IsIntegral W] [IsIntegral X]
    [IsDominant p] : Spec W.functionField ⟶ Spec X.functionField :=
  Spec.map (CommRingCat.ofHom (functionFieldMap p))

/-- `Spec k(W) ⟶ Spec k(X) ⟶ X` equals `Spec k(W) ⟶ W ⟶ X` for a dominant morphism `p : W ⟶ X`
of integral schemes. -/
@[reassoc]
theorem specFunctionFieldMap_comp_fromSpecStalk [IsIntegral W] [IsIntegral X] (p : W ⟶ X)
    [IsDominant p] :
    specFunctionFieldMap p ≫ X.fromSpecStalk (genericPoint X) =
      W.fromSpecStalk (genericPoint W) ≫ p :=
  functionFieldMap_fromSpecStalk p

/-- `specFunctionFieldMap` is compatible with composition of dominant morphisms. -/
theorem specFunctionFieldMap_comp [IsIntegral W] [IsIntegral X] [IsIntegral Y] (g : W ⟶ X)
    (p : X ⟶ Y) [IsDominant g] [IsDominant p] [IsDominant (g ≫ p)] :
    specFunctionFieldMap (g ≫ p) = specFunctionFieldMap g ≫ specFunctionFieldMap p := by
  rw [← cancel_mono (Y.fromSpecStalk (genericPoint Y)), Category.assoc,
    specFunctionFieldMap_comp_fromSpecStalk, specFunctionFieldMap_comp_fromSpecStalk,
    specFunctionFieldMap_comp_fromSpecStalk_assoc]

/-- `specFunctionFieldMap` depends only on the morphism, not on the proof of dominance. -/
theorem specFunctionFieldMap_congr [IsIntegral W] [IsIntegral X] {p p' : W ⟶ X} [IsDominant p]
    [IsDominant p'] (h : p = p') : specFunctionFieldMap p = specFunctionFieldMap p' := by
  subst h
  rfl

/-- A birational morphism of integral schemes induces an isomorphism of function fields. -/
theorem IsBirationalMorphism.isIso_specFunctionFieldMap [IsIntegral W] [IsIntegral X]
    {p : W ⟶ X} (hp : IsBirationalMorphism p) [IsDominant p] :
    IsIso (specFunctionFieldMap p) := by
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp.functionFieldMap_bijective
  change IsIso (Spec.map (CommRingCat.ofHom (functionFieldMap p)))
  infer_instance

private theorem partialMap_fromFunctionField_eq [IrreducibleSpace X] (g : X.PartialMap Y)
    (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

private theorem genericPoint_mem_of_nonempty [IrreducibleSpace X] {U : X.Opens}
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  (genericPoint_specializes _).mem_open U.2 hU.choose_spec

namespace RationalMap.IsInverse

/-- If `ψ'` is an inverse of `ψ : X ⤏ Y` and `φ : Spec k(X) ⟶ Spec k(Y)` lifts
`Spec k(X) ⟶ Y` along `ψ`, then `Spec k(X) ⟶ Spec k(Y) ⟶ X` along `ψ'` is the canonical map. -/
theorem comp_fromFunctionField_eq [IsIntegral X] [IsIntegral Y] {ψ : X.RationalMap Y}
    {ψ' : Y.RationalMap X} (hinv : IsInverse ψ ψ')
    (φ : Spec X.functionField ⟶ Spec Y.functionField)
    (hφ : φ ≫ Y.fromSpecStalk (genericPoint Y) = ψ.fromFunctionField) :
    φ ≫ ψ'.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_nonempty e.dense_source.nonempty
  have hy : genericPoint Y ∈ e.target := genericPoint_mem_of_nonempty e.dense_target.nonempty
  have hψ : ψ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ' : ψ'.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint Y) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c : φ ≫ e.target.fromSpecStalkOfMem (genericPoint Y) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hφ, hψ,
      Category.assoc]
  rw [hψ', ← Category.assoc, c, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a model `p : W ⟶ X` with `h` inverse to `p`, `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `h ≫ q` is
`Spec k(W) ⟶ W ⟶ Y`. -/
theorem specFunctionFieldMap_comp_fromFunctionField_compHom [IsIntegral W] [IsIntegral X]
    {p : W ⟶ X} [IsDominant p] {h : X.RationalMap W} (hinv : IsInverse p.toRationalMap h)
    (q : W ⟶ Y) :
    specFunctionFieldMap p ≫ (h.compHom q).fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    hinv.comp_fromFunctionField_eq (specFunctionFieldMap p)
      (by rw [specFunctionFieldMap_comp_fromSpecStalk,
        MMP.Flips.RationalMap.fromFunctionField_hom])]

/-- An inverse of a morphism, followed by the morphism, is the identity. -/
theorem compHom_eq_id [IsIntegral W] [IsIntegral X] {p : W ⟶ X} {h : X.RationalMap W}
    (hinv : IsInverse p.toRationalMap h) : h.compHom p = Scheme.RationalMap.id X := by
  have hp : IsBirationalMorphism p := hinv.isBirational
  have := hp.isDominant
  have := hp.isIso_specFunctionFieldMap
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [← cancel_epi (specFunctionFieldMap p),
    hinv.specFunctionFieldMap_comp_fromFunctionField_compHom,
    show Scheme.RationalMap.id X = Scheme.Hom.toRationalMap (𝟙 X) from rfl,
    MMP.Flips.RationalMap.fromFunctionField_hom, Category.comp_id,
    specFunctionFieldMap_comp_fromSpecStalk]

/-- **Birationality on a common model.** If `h` is an inverse of a morphism `p : W ⟶ X` of
integral schemes and `q : W ⟶ Y` is a birational morphism, then `q ∘ h` is birational: on a
nonempty open of `W` where `p` and `q` are both open immersions, `q ∘ h` is the isomorphism
between the two images. -/
theorem isBirational_compHom [IsIntegral W] [IsIntegral X] [IsIntegral Y] {p : W ⟶ X}
    {h : X.RationalMap W} (hh : IsInverse p.toRationalMap h) {q : W ⟶ Y}
    (hq : IsBirationalMorphism q) : IsBirational (h.compHom q) := by
  have hp : IsBirationalMorphism p := hh.isBirational
  have := hp.isDominant
  obtain ⟨Ap, hAp, _⟩ := hp.exists_isOpenImmersion
  obtain ⟨Aq, hAq, _⟩ := hq.exists_isOpenImmersion
  obtain ⟨a, hap, haq⟩ := nonempty_preirreducible_inter Ap.isOpen Aq.isOpen hAp hAq
  let A : W.Opens := Ap ⊓ Aq
  have ha : a ∈ A := ⟨hap, haq⟩
  have : IsOpenImmersion (A.ι ≫ p) := by
    rw [← Scheme.homOfLE_ι W (inf_le_left : A ≤ Ap), Category.assoc]
    infer_instance
  have : IsOpenImmersion (A.ι ≫ q) := by
    rw [← Scheme.homOfLE_ι W (inf_le_right : A ≤ Aq), Category.assoc]
    infer_instance
  let Rp := (A.ι ≫ p).opensRange
  let Rq := (A.ι ≫ q).opensRange
  have hRp : (Rp : Set X).Nonempty := ⟨(A.ι ≫ p) ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩
  have hRq : (Rq : Set Y).Nonempty := ⟨(A.ι ≫ q) ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩
  let e : X.PartialIso Y :=
    { source := Rp
      dense_source := Rp.isOpen.dense hRp
      target := Rq
      dense_target := Rq.isOpen.dense hRq
      iso := (Scheme.Hom.isoOpensRange (A.ι ≫ p)).symm ≪≫ Scheme.Hom.isoOpensRange (A.ι ≫ q) }
  refine ⟨e, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  have := hp.isIso_specFunctionFieldMap
  have hW : genericPoint W ∈ A := genericPoint_mem_of_nonempty ⟨a, ha⟩
  have hX : genericPoint X ∈ Rp := genericPoint_mem_of_nonempty hRp
  have c : specFunctionFieldMap p ≫ Rp.fromSpecStalkOfMem (genericPoint X) hX =
      A.fromSpecStalkOfMem (genericPoint W) hW ≫ (Scheme.Hom.isoOpensRange (A.ι ≫ p)).hom := by
    rw [← cancel_mono Rp.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      specFunctionFieldMap_comp_fromSpecStalk, Category.assoc, Scheme.Hom.isoOpensRange_hom_ι,
      ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  rw [← cancel_epi (specFunctionFieldMap p),
    hh.specFunctionFieldMap_comp_fromFunctionField_compHom]
  change specFunctionFieldMap p ≫ e.toPartialMap.toRationalMap.fromFunctionField = _
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap, partialMap_fromFunctionField_eq _ hX]
  change specFunctionFieldMap p ≫ Rp.fromSpecStalkOfMem (genericPoint X) hX ≫
    ((Scheme.Hom.isoOpensRange (A.ι ≫ p)).inv ≫ (Scheme.Hom.isoOpensRange (A.ι ≫ q)).hom) ≫
      Rq.ι = _
  rw [← Category.assoc, c]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change A.fromSpecStalkOfMem (genericPoint W) hW ≫ (Scheme.Hom.isoOpensRange (A.ι ≫ q)).hom ≫
    (A.ι ≫ q).opensRange.ι = _
  rw [Scheme.Hom.isoOpensRange_hom_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- **Refining a common model.** If `h` is an inverse of `p : W ⟶ X`, `H` an inverse of
`w ≫ p` for a dominant `w : V ⟶ W` of integral schemes, then `(w ≫ q) ∘ H = q ∘ h`. -/
theorem compHom_comp_eq [IsIntegral V] [IsIntegral W] [IsIntegral X] {w : V ⟶ W} {p : W ⟶ X}
    [IsDominant w] {h : X.RationalMap W} {H : X.RationalMap V}
    (hh : IsInverse p.toRationalMap h) (hH : IsInverse (w ≫ p).toRationalMap H) (q : W ⟶ Y) :
    H.compHom (w ≫ q) = h.compHom q := by
  have := IsBirationalMorphism.isDominant (f := p) hh.isBirational
  have hwp : IsBirationalMorphism (w ≫ p) := hH.isBirational
  have := hwp.isDominant
  have := hwp.isIso_specFunctionFieldMap
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [← cancel_epi (specFunctionFieldMap (w ≫ p)),
    hH.specFunctionFieldMap_comp_fromFunctionField_compHom, specFunctionFieldMap_comp w p,
    Category.assoc, hh.specFunctionFieldMap_comp_fromFunctionField_compHom,
    ← specFunctionFieldMap_comp_fromSpecStalk_assoc w]

end RationalMap.IsInverse

end MMP.Mori

namespace MMP.Fourfold.NefModelEquivalence

open CategoryTheory.Limits MMP.Mori

/-! ### `ℝ`-intersection numbers as degrees along the curve -/

section RIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  refine Stacks.Chow.not_subsingleton_of_one_le_topologicalKrullDim C.dim_eq.ge ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ν.surjective a
  obtain ⟨x', rfl⟩ := ν.surjective b
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : MMP.Flips.IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    degreeOn k sX (ν ≫ C.ι) hdim M = degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by
    rw [← Category.assoc]
    infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [degreeOn, degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : MMP.Flips.IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a normal proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sX C L hL d := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have : IsIntegral (normalizationSchemeOverField k p) :=
    (isVariety_normalizationOverField k p).toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  refine ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => ?_⟩
  rw [eq_degreeOn (hd j)]

/-- `D · C = 0` for every presentation of `D` if and only if one presentation gives
`∑ rⱼ deg_C 𝒪_X(Lⱼ) = 0`. -/
private theorem forall_eq_zero_iff (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    (∀ (m' : ℕ) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber k sX D r' L' C x → x = 0) ↔
      ∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ) = 0 := by
  refine ⟨fun h => h _ r L _ (isRIntersectionNumber_sum C r L hL hD), fun h m' r' L' x hx => ?_⟩
  rw [← h]
  exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 D r' L' r L x _ hx
    (isRIntersectionNumber_sum C r L hL hD)

end RIntersection

/-! ### Zero-degree curves -/

section Null

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- `D · Γ = 0`, computed with every presentation of the `ℝ`-divisor `D`. -/
private def IsNull (D : RDivisor X) (Γ : ProperCurve sX) : Prop :=
  ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
    MMP.Flips.IsRIntersectionNumber k sX D r L Γ x → x = 0

/-- `D · Γ = 0` for the proper curve `Γ` with generic point `x`, if there is one. -/
private def NullAt (D : RDivisor X) (x : X) : Prop :=
  ∀ Γ : ProperCurve sX, Γ.point = x → IsNull k sX D Γ

private theorem nullAt_iff (D : RDivisor X) (Γ : ProperCurve sX) {x : X} (hx : Γ.point = x) :
    NullAt k sX D x ↔ IsNull k sX D Γ :=
  ⟨fun h => h Γ hx, fun h Γ' hΓ' => by
    obtain rfl : Γ' = Γ := ProperCurve.ext (hΓ'.trans hx.symm)
    exact h⟩

end Null

/-! ### Degrees of pulled-back divisors on curves -/

section Pullback

variable {k : Type u} [Field k] {V T : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

/-- A proper curve which is not contracted by `u` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (u : V ⟶ T) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : ¬ ∃ t : T, Set.range (Γ.ι ≫ u) = {t} := by
  rintro ⟨t, ht⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨y, rfl⟩ := hx
  have h1 : (Γ.ι ≫ u) y ∈ Set.range (Γ.ι ≫ u) := ⟨y, rfl⟩
  have h2 : (Γ.ι ≫ u) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ u) := ⟨_, rfl⟩
  rw [ht] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `u` is a proper curve. -/
private theorem isProperCurve_map (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : IsProperCurve sT (u Γ.point) := by
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hpt := not_exists_range_eq_singleton u Γ h
  have hcurve := isCurve_imageι_comp sT φ hpt
  have hker := Γ.ker_comp u
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (u Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (u Γ.point) ≫ sT) := by
    have h1 : IsProper (φ.imageι ≫ sT) := isProper_imageι_comp φ sT
    change IsProper (φ.ker.subschemeι ≫ sT) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- The image of a proper curve contracted by `u` is a point, not a proper curve. -/
private theorem not_isProperCurve_of_isContractedBy (u : V ⟶ T) (hu : u ≫ sT = sV)
    (Γ : ProperCurve sV) (h : Γ.IsContractedBy u) : ¬ IsProperCurve sT (u Γ.point) := by
  intro hc
  have hr : ∀ t, curveSubschemeAtι (u Γ.point) t = u Γ.point := fun t => by
    have ht : curveSubschemeAtι (u Γ.point) t ∈ closure {u Γ.point} :=
      range_curveSubschemeAtι (u Γ.point) ▸ ⟨t, rfl⟩
    rw [← Γ.range_comp u hu] at ht
    obtain ⟨c, hc'⟩ := ht
    rw [← hc', Scheme.Hom.comp_apply]
    exact h _ (Γ.range_ι ▸ ⟨c, rfl⟩)
  exact Stacks.Chow.not_subsingleton_of_one_le_topologicalKrullDim hc.dim_eq.ge
    ⟨fun a b => (curveSubschemeAtι (u Γ.point)).isEmbedding.injective
      ((hr a).trans (hr b).symm)⟩

/-- `D` is vacuously numerically trivial at the image of a curve that `u` contracts. -/
private theorem nullAt_of_isContractedBy [QuasiCompact sT] [IsLocallyNoetherian T] [IsNormal T]
    (u : V ⟶ T) (hu : u ≫ sT = sV) (D : RDivisor T) {Γ : ProperCurve sV}
    (hc : Γ.IsContractedBy u) : NullAt k sT D (u Γ.point) :=
  fun Γ' hΓ' => absurd (hΓ' ▸ Γ'.isProperCurve) (not_isProperCurve_of_isContractedBy u hu Γ hc)

/-- A curve contracted by `g` is contracted by `g ≫ p`. -/
private theorem isContractedBy_comp {S : Scheme.{u}} {Γ : ProperCurve sV} {g : V ⟶ T}
    (hc : Γ.IsContractedBy g) (p : T ⟶ S) : Γ.IsContractedBy (g ≫ p) := fun x hx => by
  simp only [Scheme.Hom.comp_apply, hc x hx]

/-- If `u ≫ π` contracts a curve `Γ` that `u` does not contract, then `π` contracts the image
curve `u(Γ)`. -/
private theorem isContractedBy_map {S : Scheme.{u}} (u : V ⟶ T) (hu : u ≫ sT = sV) (π : T ⟶ S)
    (Γ : ProperCurve sV) (h : ¬ Γ.IsContractedBy u) (hΓ : Γ.IsContractedBy (u ≫ π)) :
    (⟨u Γ.point, isProperCurve_map u hu Γ h⟩ : ProperCurve sT).IsContractedBy π := by
  intro y hy
  change y ∈ closure {u Γ.point} at hy
  rw [← ProperCurve.range_comp u hu Γ] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : Γ.ι x ∈ closure {Γ.point} := Γ.range_ι ▸ ⟨x, rfl⟩
  simpa only [Scheme.Hom.comp_apply] using hΓ _ hx

/-- A curve whose generic point maps to that of a curve contracted by `π` is contracted by
`u ≫ π`. -/
private theorem isContractedBy_comp_of_map_eq {S : Scheme.{u}} (u : V ⟶ T) (π : T ⟶ S)
    {Γ' : ProperCurve sV} {Γ : ProperCurve sT} (h : u Γ'.point = Γ.point)
    (hΓ : Γ.IsContractedBy π) : Γ'.IsContractedBy (u ≫ π) := fun x hx => by
  have h1 : u x ∈ closure {Γ.point} := by
    rw [← h]
    exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hx).map u.continuous)
  simp only [Scheme.Hom.comp_apply, h]
  exact hΓ _ h1

/-- A morphism non-constant on a proper curve has positive residue degree at its generic
point. -/
private theorem residueFieldDegree_pos (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : 0 < residueFieldDegree u Γ.point := by
  have hnc := not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; exact hLφ
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

variable [QuasiCompact sV] [QuasiCompact sT] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsLocallyNoetherian T] [IsNormal T]

/-- The pull-back of a Cartier divisor has degree zero on a contracted curve. -/
private theorem degreeOn_isPullback_eq_zero (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) = 0 := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy u hu hD hB Γ hΓ

/-- **Projection formula.** On a curve `Γ` not contracted by `u`, with image the proper curve
`Γ'`, `deg_Γ u^*D = [k(Γ) : k(Γ')] · deg_{Γ'} D`. -/
private theorem degreeOn_isPullback_eq_mul (u : V ⟶ T) (hu : u ≫ sT = sV) {D : Divisor T}
    (hD : D.IsCartier) {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ D.supp}
    {D' : Divisor V} (h : D.IsPullback u hB D') (Γ : ProperCurve sV) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    D'.degreeOn k sV Γ.ι Γ.dim_le (h.isCartier hD) =
      (residueFieldDegree u Γ.point : ℤ) * D.degreeOn k sT Γ'.ι Γ'.dim_le hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sT
  have := QuasiCompact.compactSpace_of_compactSpace sV
  obtain rfl := h.eq hD (Divisor.isPullback_pullback hD hB)
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward u hu hD hB Γ, OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hΓ' ▸ Γ'.isProperCurve)]
  obtain ⟨pt, hpt⟩ := Γ'
  simp only at hΓ'
  subst hΓ'
  simp [OneCycle.degree, Finsupp.linearCombination_single, ProperCurve.degree, Divisor.degreeOn]

/-- An `ℝ`-Cartier pull-back is numerically trivial on every curve the morphism contracts. -/
private theorem forall_eq_zero_of_isRCartierPullback (u : V ⟶ T) (hu : u ≫ sT = sV)
    {D : RDivisor T} {D' : RDivisor V} (h : MMP.Flips.IsRCartierPullback u D D')
    (Γ : ProperCurve sV) (hΓ : Γ.IsContractedBy u) :
    ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber k sV D' r L Γ x → x = 0 := by
  obtain ⟨m, r, L, L', hL, -, hpb, hD'⟩ := h
  choose hB hpb using hpb
  refine (forall_eq_zero_iff Γ r L' (fun j => (hpb j).isCartier (hL j)) hD').2
    (Finset.sum_eq_zero fun j _ => ?_)
  rw [degreeOn_isPullback_eq_zero u hu (hL j) (hpb j) Γ hΓ, Int.cast_zero, mul_zero]

/-- **Projection formula** for numerical triviality: on a curve `Γ` not contracted by `u`, with
image the proper curve `Γ'`, an `ℝ`-Cartier pull-back `u^*D` is numerically trivial on `Γ` if
and only if `D` is numerically trivial on `Γ'`. -/
private theorem forall_eq_zero_iff_of_isRCartierPullback (u : V ⟶ T) (hu : u ≫ sT = sV)
    {D : RDivisor T} {D' : RDivisor V} (h : MMP.Flips.IsRCartierPullback u D D')
    (Γ : ProperCurve sV) (hΓ : ¬ Γ.IsContractedBy u) (Γ' : ProperCurve sT)
    (hΓ' : Γ'.point = u Γ.point) :
    (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber k sV D' r L Γ x → x = 0) ↔
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor T) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber k sT D r L Γ' x → x = 0 := by
  obtain ⟨m, r, L, L', hL, hD, hpb, hD'⟩ := h
  choose hB hpb using hpb
  have hj : ∀ j, ((L' j).degreeOn k sV Γ.ι Γ.dim_le ((hpb j).isCartier (hL j)) : ℝ) =
      residueFieldDegree u Γ.point * ((L j).degreeOn k sT Γ'.ι Γ'.dim_le (hL j) : ℝ) :=
    fun j => by
      rw [degreeOn_isPullback_eq_mul u hu (hL j) (hpb j) Γ Γ' hΓ']
      push_cast
      rfl
  have hc : (residueFieldDegree u Γ.point : ℝ) ≠ 0 := by
    exact_mod_cast (residueFieldDegree_pos u hu Γ hΓ).ne'
  rw [forall_eq_zero_iff Γ r L' (fun j => (hpb j).isCartier (hL j)) hD',
    forall_eq_zero_iff Γ' r L hL hD]
  simp only [hj, mul_left_comm (r _), ← Finset.mul_sum, mul_eq_zero, hc, false_or]

/-- **Zero-degree curves of a pull-back.** For a `k`-morphism `u : V ⟶ T` of normal varieties and
an `ℝ`-Cartier pull-back `u^*D`, a proper curve `Γ ⊆ V` has `u^*D · Γ = 0` exactly when the
proper curve of `T` with generic point `u(ξ_Γ)`, if there is one, has degree zero for `D`. -/
private theorem isNull_iff_nullAt (u : V ⟶ T) (hu : u ≫ sT = sV) {D : RDivisor T}
    {D' : RDivisor V} (h : MMP.Flips.IsRCartierPullback u D D') (Γ : ProperCurve sV) :
    IsNull k sV D' Γ ↔ NullAt k sT D (u Γ.point) := by
  by_cases hc : Γ.IsContractedBy u
  · exact iff_of_true (forall_eq_zero_of_isRCartierPullback u hu h Γ hc)
      (nullAt_of_isContractedBy u hu D hc)
  · rw [nullAt_iff k sT D ⟨u Γ.point, isProperCurve_map u hu Γ hc⟩ rfl]
    exact forall_eq_zero_iff_of_isRCartierPullback u hu h Γ hc _ rfl

end Pullback

/-! ### Comparison through a common model -/

section Model

variable {k : Type u} [Field k] {V W Z₁ Z₂ S : Scheme.{u}} {sV : V ⟶ Spec (.of k)}
  {sW : W ⟶ Spec (.of k)} {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)}
  [IsSeparated sW] [LocallyOfFiniteType sW] [IsSeparated s₁] [LocallyOfFiniteType s₁]
  [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact sW] [QuasiCompact s₁]
  [QuasiCompact s₂] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
  [IsLocallyNoetherian Z₁] [IsNormal Z₁] [IsLocallyNoetherian Z₂] [IsNormal Z₂]

/-- Let `p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂` carry `ℝ`-Cartier pull-backs `D₁`, `D₂` of `B₁`, `B₂` with
the same zero-degree curves among the curves contracted by `p₁ ≫ π₁`. Then for every `k`-morphism
`g : V ⟶ W` and every proper curve `Γ ⊆ V` contracted by `g ≫ p₁ ≫ π₁`, the image points of `Γ`
in `Z₁` and `Z₂` have the same zero-degree behaviour for `B₁` and `B₂`. -/
private theorem nullAt_iff_nullAt_of_model (π₁ : Z₁ ⟶ S) (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂)
    (hp₁ : p₁ ≫ s₁ = sW) (hp₂ : p₂ ≫ s₂ = sW) {B₁ : RDivisor Z₁} {B₂ : RDivisor Z₂}
    {D₁ D₂ : RDivisor W} (hD₁ : MMP.Flips.IsRCartierPullback p₁ B₁ D₁)
    (hD₂ : MMP.Flips.IsRCartierPullback p₂ B₂ D₂)
    (hZ : ∀ Γ : ProperCurve sW, Γ.IsContractedBy (p₁ ≫ π₁) →
      (IsNull k sW D₁ Γ ↔ IsNull k sW D₂ Γ))
    (g : V ⟶ W) (hg : g ≫ sW = sV) (Γ : ProperCurve sV)
    (hΓ : Γ.IsContractedBy (g ≫ p₁ ≫ π₁)) :
    NullAt k s₁ B₁ (p₁ (g Γ.point)) ↔ NullAt k s₂ B₂ (p₂ (g Γ.point)) := by
  by_cases hc : Γ.IsContractedBy g
  · exact iff_of_true
      (nullAt_of_isContractedBy (g ≫ p₁) (by rw [Category.assoc, hp₁, hg]) B₁
        (isContractedBy_comp hc p₁))
      (nullAt_of_isContractedBy (g ≫ p₂) (by rw [Category.assoc, hp₂, hg]) B₂
        (isContractedBy_comp hc p₂))
  · have hΓ' := isContractedBy_map g hg (p₁ ≫ π₁) Γ hc hΓ
    rw [← isNull_iff_nullAt p₁ hp₁ hD₁ ⟨g Γ.point, isProperCurve_map g hg Γ hc⟩,
      ← isNull_iff_nullAt p₂ hp₂ hD₂ ⟨g Γ.point, isProperCurve_map g hg Γ hc⟩]
    exact hZ _ hΓ'

end Model

/-! ### Lifting proper curves along proper morphisms -/

section Lifting

variable {k : Type u} [Field k]

/-- A nonempty fibre of a map out of a Noetherian T₀ space has a point closed in the fibre. -/
private lemma exists_closed_mem_fiber {X Y : Type*} [TopologicalSpace X] [T0Space X]
    [TopologicalSpace.NoetherianSpace X] (f : X → Y) {y : Y} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have : (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (this.mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton (X : Type*) [TopologicalSpace X]
    [Nonempty X] [Subsingleton X] : topologicalKrullDim X = 0 := by
  have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `{y}⁻` is
proper over `k`: it factors through its scheme-theoretic image, which is `{y}⁻`. -/
private lemma isProper_comp_of_closure_range {X B : Scheme.{u}} {sB : B ⟶ Spec (.of k)} {y : B}
    (hy : IsProperCurve sB y) (φ : X ⟶ B) [IsReduced X] [IsProper φ]
    (hφ : closure (Set.range φ.base) = closure {y}) : IsProper (φ ≫ sB) := by
  have hker :
      φ.ker = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {y}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (TopologicalSpace.Closeds.ext (by
      rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hφ]))
  have : IsProper (φ.imageι ≫ sB) := by
    change IsProper (φ.ker.subschemeι ≫ sB)
    rw [hker]
    exact hy.isProper
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- **Lifting proper curves.** Let `h : A ⟶ B` be a proper `k`-morphism of schemes locally of
finite type over `k`, `A` quasi-compact, and `y` the generic point of a proper curve of `B` lying
in the image of `h`. Then `y` is the image of the generic point of a proper curve of `A`: the
closure of a point closed in the fibre over `y`. -/
private theorem exists_properCurve_map_eq {A B : Scheme.{u}} (sA : A ⟶ Spec (.of k))
    (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] (h : A ⟶ B) [IsProper h] (hh : h ≫ sB = sA) {y : B}
    (hy : y ∈ Set.range h.base) (hyc : IsProperCurve sB y) :
    ∃ C : ProperCurve sA, h C.point = y := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber h.base hy
  set ι := curveSubschemeAtι a
  set φ := ι ≫ h
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = y := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {y} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
  have : Subsingleton (φ.base ⁻¹' {φ.base (genericPoint _)}) := by
    suffices ∀ c, φ c = y → c = genericPoint _ from
      ⟨fun u v => Subtype.ext ((this _ (u.2.trans hφgen)).trans (this _ (v.2.trans hφgen)).symm)⟩
    intro c hc
    have hca : a ⤳ ι c := specializes_iff_mem_closure.mpr (range_curveSubschemeAtι a ▸ ⟨c, rfl⟩)
    exact ι.isEmbedding.injective
      ((hamax _ (by rw [← hc, Scheme.Hom.comp_apply]) hca).trans hgen.symm)
  let e := φ.fiberHomeo (φ.base (genericPoint _))
  have : Subsingleton (φ.fiber (φ.base (genericPoint _))) := e.injective.subsingleton
  have : Nonempty (φ.fiber (φ.base (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hh]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ k (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact hyc.dim_eq
  exact ⟨⟨a, hdim, hcomp ▸ isProper_comp_of_closure_range hyc φ hclr⟩, haξ⟩

end Lifting

/-! ### Rational maps through function fields -/

section RationalMaps

variable {V W X Y Z : Scheme.{u}}

/-- Composing a rational map with two morphisms in turn is composing it with their composite. -/
private theorem compHom_compHom (φ : X.RationalMap Y) (f : Y ⟶ Z) {T : Scheme.{u}}
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- **Symmetry of common models.** If `p : W ⟶ X`, `q : W ⟶ Y` are birational morphisms with
inverses `h`, `h'`, then the inverse of `q ∘ p⁻¹` is `p ∘ q⁻¹`. -/
private theorem compHom_eq_of_isInverse_compHom [IsIntegral W] [IsIntegral X] [IsIntegral Y]
    (p : W ⟶ X) (q : W ⟶ Y) (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q)
    {h : X.RationalMap W} {h' : Y.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hh' : MMP.Mori.RationalMap.IsInverse q.toRationalMap h') {ψ' : Y.RationalMap X}
    (hψ : MMP.Mori.RationalMap.IsInverse (h.compHom q) ψ') : h'.compHom p = ψ' := by
  have := hp.isDominant
  have := hq.isDominant
  have := hp.isIso_specFunctionFieldMap
  have := hq.isIso_specFunctionFieldMap
  have hφ : (inv (specFunctionFieldMap p) ≫ specFunctionFieldMap q) ≫
      Y.fromSpecStalk (genericPoint Y) = (h.compHom q).fromFunctionField := by
    rw [Category.assoc, specFunctionFieldMap_comp_fromSpecStalk, IsIso.inv_comp_eq,
      hh.specFunctionFieldMap_comp_fromFunctionField_compHom]
  have key := hψ.comp_fromFunctionField_eq _ hφ
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [← cancel_epi (inv (specFunctionFieldMap p) ≫ specFunctionFieldMap q), key, Category.assoc,
    hh'.specFunctionFieldMap_comp_fromFunctionField_compHom,
    ← specFunctionFieldMap_comp_fromSpecStalk p,
    IsIso.inv_hom_id_assoc]

/-- `Spec k(X) ⟶ Z` along a composite `f.comp g` of rational maps of integral schemes, `f`
dominant: it is `Spec k(X) ⟶ Spec k(Y) ⟶ Z` along `g`, for any lift `φ` of `Spec k(X) ⟶ Y`
along `f`. -/
private theorem fromFunctionField_comp [IsIntegral X] [IsIntegral Y] (f : X.RationalMap Y)
    [f.IsDominant] (g : Y.RationalMap Z) (φ : Spec X.functionField ⟶ Spec Y.functionField)
    (hφ : φ ≫ Y.fromSpecStalk (genericPoint Y) = f.fromFunctionField) :
    (f.comp g).fromFunctionField = φ ≫ g.fromFunctionField := by
  obtain ⟨g₀, rfl⟩ := g.exists_rep
  rw [Scheme.RationalMap.comp_def, Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap]
  set f₀ := f.representative
  have hf : f.fromFunctionField = f₀.fromFunctionField := by
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_representative]
  have hX : genericPoint X ∈ f₀.domain := genericPoint_mem_of_nonempty f₀.dense_domain.nonempty
  have hY : genericPoint Y ∈ g₀.domain := genericPoint_mem_of_nonempty g₀.dense_domain.nonempty
  have hD : genericPoint X ∈ f₀.domain.ι ''ᵁ f₀.hom ⁻¹ᵁ g₀.domain :=
    genericPoint_mem_of_nonempty (f₀.comp g₀).dense_domain.nonempty
  rw [partialMap_fromFunctionField_eq _ hX] at hf
  rw [partialMap_fromFunctionField_eq (f₀.comp g₀) hD, partialMap_fromFunctionField_eq _ hY]
  change (f₀.domain.ι ''ᵁ f₀.hom ⁻¹ᵁ g₀.domain).fromSpecStalkOfMem (genericPoint X) hD ≫
    (f₀.domain.ι.isoImage _).inv ≫ f₀.hom ∣_ g₀.domain ≫ g₀.hom = _
  have c1 : (f₀.domain.ι ''ᵁ f₀.hom ⁻¹ᵁ g₀.domain).fromSpecStalkOfMem (genericPoint X) hD ≫
      (f₀.domain.ι.isoImage (f₀.hom ⁻¹ᵁ g₀.domain)).inv ≫ (f₀.hom ⁻¹ᵁ g₀.domain).ι =
      f₀.domain.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono f₀.domain.ι, Category.assoc, Category.assoc, Scheme.Hom.isoImage_inv_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have c2 : (f₀.domain.ι ''ᵁ f₀.hom ⁻¹ᵁ g₀.domain).fromSpecStalkOfMem (genericPoint X) hD ≫
      (f₀.domain.ι.isoImage (f₀.hom ⁻¹ᵁ g₀.domain)).inv ≫ f₀.hom ∣_ g₀.domain =
      φ ≫ g₀.domain.fromSpecStalkOfMem (genericPoint Y) hY := by
    rw [← cancel_mono g₀.domain.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      reassoc_of% c1, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hφ, hf]
  rw [reassoc_of% c2]

/-- **Composites on a common refinement.** Let `g₀ : V ⟶ W`, `g₁ : V ⟶ W'` with
`g₀ ≫ p₂ = g₁ ≫ q₂`, where `(W, p₁, p₂)` models `ψ₁₂ = p₂ ∘ p₁⁻¹` and `(W', q₂, q₃)` models
`ψ₂₃ = q₃ ∘ q₂⁻¹`. Then `(V, g₀ ≫ p₁, g₁ ≫ q₃)` models `ψ₁₂.comp ψ₂₃`. -/
private theorem compHom_eq_comp_of_isInverse {W' Z₁ Z₂ Z₃ : Scheme.{u}} [IsIntegral V]
    [IsIntegral W] [IsIntegral W'] [IsIntegral Z₁] [IsIntegral Z₂] (g₀ : V ⟶ W) (g₁ : V ⟶ W')
    (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂) (q₂ : W' ⟶ Z₂) (q₃ : W' ⟶ Z₃) (hcomm : g₀ ≫ p₂ = g₁ ≫ q₂)
    (bg₀ : IsBirationalMorphism g₀) (bg₁ : IsBirationalMorphism g₁)
    (bp₁ : IsBirationalMorphism p₁) (bp₂ : IsBirationalMorphism p₂)
    (bq₂ : IsBirationalMorphism q₂) (bP₁ : IsBirationalMorphism (g₀ ≫ p₁))
    {h₁₂ : Z₁.RationalMap W} {h₂₃ : Z₂.RationalMap W'} {H : Z₁.RationalMap V}
    (hh₁₂ : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h₁₂)
    (hh₂₃ : MMP.Mori.RationalMap.IsInverse q₂.toRationalMap h₂₃)
    (hH : MMP.Mori.RationalMap.IsInverse (g₀ ≫ p₁).toRationalMap H)
    {ψ₁₂ : Z₁.RationalMap Z₂} [ψ₁₂.IsDominant] (hψ₁₂ : h₁₂.compHom p₂ = ψ₁₂)
    {ψ₂₃ : Z₂.RationalMap Z₃} (hψ₂₃ : h₂₃.compHom q₃ = ψ₂₃) :
    H.compHom (g₁ ≫ q₃) = ψ₁₂.comp ψ₂₃ := by
  have := bg₀.isDominant
  have := bg₁.isDominant
  have := bp₁.isDominant
  have := bp₂.isDominant
  have := bq₂.isDominant
  have := bP₁.isDominant
  have := bP₁.isIso_specFunctionFieldMap
  refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [fromFunctionField_comp ψ₁₂ ψ₂₃
    (inv (specFunctionFieldMap (g₀ ≫ p₁)) ≫ specFunctionFieldMap (g₀ ≫ p₂)) ?hφ]
  · rw [← cancel_epi (specFunctionFieldMap (g₀ ≫ p₁)),
      hH.specFunctionFieldMap_comp_fromFunctionField_compHom,
      Category.assoc, IsIso.hom_inv_id_assoc, specFunctionFieldMap_congr hcomm,
      specFunctionFieldMap_comp g₁ q₂,
      Category.assoc, ← hψ₂₃, hh₂₃.specFunctionFieldMap_comp_fromFunctionField_compHom,
      ← specFunctionFieldMap_comp_fromSpecStalk_assoc g₁]
  · rw [Category.assoc, specFunctionFieldMap_comp_fromSpecStalk, IsIso.inv_comp_eq,
      specFunctionFieldMap_comp g₀ p₁,
      Category.assoc, ← hψ₁₂, hh₁₂.specFunctionFieldMap_comp_fromFunctionField_compHom,
      ← specFunctionFieldMap_comp_fromSpecStalk_assoc g₀]

/-- On a common model `p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂` of a map `ψ` over `S`, `S` separated over
`k`, the two composites `W ⟶ S` agree. -/
private theorem comp_eq_comp_of_isOver {k : Type u} [Field k] {Z₁ Z₂ S : Scheme.{u}}
    [IsIntegral W] [IsIntegral Z₁] (sS : S ⟶ Spec (.of k)) [IsSeparated sS] (π₁ : Z₁ ⟶ S)
    (π₂ : Z₂ ⟶ S) {ψ : Z₁.RationalMap Z₂} (hψ : MMP.Flips.RationalMap.IsOver π₁ π₂ ψ)
    (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂) (bp₁ : IsBirationalMorphism p₁) {h : Z₁.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h) (hc : h.compHom p₂ = ψ)
    (hs : (p₁ ≫ π₁) ≫ sS = (p₂ ≫ π₂) ≫ sS) : p₁ ≫ π₁ = p₂ ≫ π₂ := by
  have := bp₁.isDominant
  have := isDominant_fromSpecStalk_genericPoint W
  refine ext_of_isDominant_of_isSeparated sS hs (W.fromSpecStalk (genericPoint W)) ?_
  have h1 := hh.specFunctionFieldMap_comp_fromFunctionField_compHom p₂
  rw [hc] at h1
  have h2 : ψ.fromFunctionField ≫ π₂ = Z₁.fromSpecStalk (genericPoint Z₁) ≫ π₁ := by
    rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hψ,
      MMP.Flips.RationalMap.fromFunctionField_hom]
  rw [← reassoc_of% h1, h2, ← specFunctionFieldMap_comp_fromSpecStalk_assoc p₁]

end RationalMaps

/-! ### Two common models have the same image in `Z₁ ×_k Z₂` -/

section TwoModels

variable {k : Type u} [Field k] {Z₁ Z₂ W W₀ : Scheme.{u}} [IsIntegral Z₁] [IsIntegral Z₂]
  [IsIntegral W] [IsIntegral W₀] {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)}

/-- If `Spec 𝒪_{X,x} ⟶ X ⟶ T` factors as `φ ≫ τ`, then `x` maps to the image under `τ` of the
image of the closed point under `φ`. -/
private theorem apply_eq_of_fromSpecStalk_comp_eq {X Y T : Scheme.{u}} (x : X) (ℓ : X ⟶ T)
    (φ : Spec (X.presheaf.stalk x) ⟶ Y) (τ : Y ⟶ T) (e : X.fromSpecStalk x ≫ ℓ = φ ≫ τ) :
    ℓ x = τ (φ (IsLocalRing.closedPoint (X.presheaf.stalk x))) :=
  calc ℓ x = ℓ (X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x))) :=
        congrArg ℓ.base Scheme.fromSpecStalk_closedPoint.symm
    _ = (X.fromSpecStalk x ≫ ℓ) (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (φ ≫ τ) (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
        congrArg (fun ψ : Spec (X.presheaf.stalk x) ⟶ T =>
          ψ (IsLocalRing.closedPoint (X.presheaf.stalk x))) e
    _ = τ (φ (IsLocalRing.closedPoint (X.presheaf.stalk x))) := Scheme.Hom.comp_apply _ _ _

/-- Two common models `(W, p₁, p₂)`, `(W₀, q₁, q₂)` of the same rational map send their generic
points to the same point of `Z₁ ×_k Z₂`. -/
private theorem lift_genericPoint_eq (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂) (q₁ : W₀ ⟶ Z₁)
    (q₂ : W₀ ⟶ Z₂) (hp : p₁ ≫ s₁ = p₂ ≫ s₂) (hq : q₁ ≫ s₁ = q₂ ≫ s₂)
    (bp₁ : IsBirationalMorphism p₁) (bq₁ : IsBirationalMorphism q₁) {h : Z₁.RationalMap W}
    {h₀ : Z₁.RationalMap W₀} (hh : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h)
    (hh₀ : MMP.Mori.RationalMap.IsInverse q₁.toRationalMap h₀)
    (hc : h.compHom p₂ = h₀.compHom q₂) :
    pullback.lift p₁ p₂ hp (genericPoint W) = pullback.lift q₁ q₂ hq (genericPoint W₀) := by
  have := bp₁.isDominant
  have := bq₁.isDominant
  have := bp₁.isIso_specFunctionFieldMap
  have := bq₁.isIso_specFunctionFieldMap
  let τ := inv (specFunctionFieldMap p₁) ≫ W.fromSpecStalk (genericPoint W) ≫
    pullback.lift p₁ p₂ hp
  let τ₀ := inv (specFunctionFieldMap q₁) ≫ W₀.fromSpecStalk (genericPoint W₀) ≫
    pullback.lift q₁ q₂ hq
  have hτ : τ = τ₀ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [τ, τ₀, Category.assoc, pullback.lift_fst, IsIso.inv_comp_eq]
      rw [← specFunctionFieldMap_comp_fromSpecStalk p₁,
        ← specFunctionFieldMap_comp_fromSpecStalk q₁,
        IsIso.inv_hom_id_assoc]
    · simp only [τ, τ₀, Category.assoc, pullback.lift_snd, IsIso.inv_comp_eq]
      rw [← hh.specFunctionFieldMap_comp_fromFunctionField_compHom,
        ← hh₀.specFunctionFieldMap_comp_fromFunctionField_compHom, hc, IsIso.inv_hom_id_assoc]
  have e1 : W.fromSpecStalk (genericPoint W) ≫ pullback.lift p₁ p₂ hp =
      specFunctionFieldMap p₁ ≫ τ := by
    simp only [τ, IsIso.hom_inv_id_assoc]
  have e2 : W₀.fromSpecStalk (genericPoint W₀) ≫ pullback.lift q₁ q₂ hq =
      specFunctionFieldMap q₁ ≫ τ₀ := by
    simp only [τ₀, IsIso.hom_inv_id_assoc]
  rw [apply_eq_of_fromSpecStalk_comp_eq _ _ _ _ e1, apply_eq_of_fromSpecStalk_comp_eq _ _ _ _ e2,
    hτ]
  exact congrArg _ (Subsingleton.elim _ _)

/-- **Curves on two common models.** Let `(W, p₁, p₂)` and `(W₀, q₁, q₂)` be common models of the
same rational map `Z₁ ⤏ Z₂`, with `W₀` proper over `k`. Every proper curve `Γ ⊆ W` which is not
contracted to a point of `Z₁ ×_k Z₂` has a proper curve `Γ₀ ⊆ W₀` with the same images in `Z₁`
and in `Z₂`. -/
private theorem exists_properCurve_of_models [IsSeparated s₂] [LocallyOfFiniteType s₂] [IsProper s₁]
    {sW : W ⟶ Spec (.of k)}
    {sW₀ : W₀ ⟶ Spec (.of k)} [LocallyOfFiniteType sW₀] [QuasiCompact sW₀] (p₁ : W ⟶ Z₁)
    (p₂ : W ⟶ Z₂) (q₁ : W₀ ⟶ Z₁) (q₂ : W₀ ⟶ Z₂) (hp₁ : p₁ ≫ s₁ = sW) (hp₂ : p₂ ≫ s₂ = sW)
    (hq₁ : q₁ ≫ s₁ = sW₀) (hq₂ : q₂ ≫ s₂ = sW₀) [IsProper q₁] (bp₁ : IsBirationalMorphism p₁)
    (bq₁ : IsBirationalMorphism q₁) {h : Z₁.RationalMap W} {h₀ : Z₁.RationalMap W₀}
    (hh : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h)
    (hh₀ : MMP.Mori.RationalMap.IsInverse q₁.toRationalMap h₀)
    (hc : h.compHom p₂ = h₀.compHom q₂) (Γ : ProperCurve sW)
    (hΓ : ¬ Γ.IsContractedBy (pullback.lift p₁ p₂ (hp₁.trans hp₂.symm))) :
    ∃ Γ₀ : ProperCurve sW₀, q₁ Γ₀.point = p₁ Γ.point ∧ q₂ Γ₀.point = p₂ Γ.point := by
  let sP := pullback.fst s₁ s₂ ≫ s₁
  let ℓ := pullback.lift p₁ p₂ (hp₁.trans hp₂.symm)
  let ℓ₀ := pullback.lift q₁ q₂ (hq₁.trans hq₂.symm)
  have hℓ : ℓ ≫ sP = sW := by simp only [ℓ, sP, pullback.lift_fst_assoc, hp₁]
  have hℓ₀ : ℓ₀ ≫ sP = sW₀ := by simp only [ℓ₀, sP, pullback.lift_fst_assoc, hq₁]
  have : IsProper sW₀ := hq₁ ▸ inferInstance
  have : IsProper (ℓ₀ ≫ sP) := hℓ₀ ▸ inferInstance
  have : IsProper ℓ₀ := IsProper.of_comp ℓ₀ sP
  have hy := isProperCurve_map ℓ hℓ Γ hΓ
  have hrange : ℓ Γ.point ∈ Set.range ℓ₀.base := by
    have h1 : ℓ Γ.point ∈ closure {ℓ (genericPoint W)} :=
      specializes_iff_mem_closure.mp ((genericPoint_specializes Γ.point).map ℓ.continuous)
    rw [show ℓ (genericPoint W) = ℓ₀ (genericPoint W₀) from
      lift_genericPoint_eq p₁ p₂ q₁ q₂ _ _ bp₁ bq₁ hh hh₀ hc] at h1
    exact closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self _))
      ℓ₀.isClosedMap.isClosed_range h1
  obtain ⟨Γ₀, hΓ₀⟩ := exists_properCurve_map_eq sW₀ sP ℓ₀ hℓ₀ hrange hy
  refine ⟨Γ₀, ?_, ?_⟩
  · rw [← pullback.lift_fst q₁ q₂ (hq₁.trans hq₂.symm), ← pullback.lift_fst p₁ p₂
      (hp₁.trans hp₂.symm), Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg _ hΓ₀
  · rw [← pullback.lift_snd q₁ q₂ (hq₁.trans hq₂.symm), ← pullback.lift_snd p₁ p₂
      (hp₁.trans hp₂.symm), Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg _ hΓ₀

end TwoModels

/-! ### The four parts -/

section Parts

/-- An `ℝ`-divisor nef over a base is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRelativelyNef {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {π : X ⟶ Y} {D : RDivisor X} (h : MMP.Flips.IsRelativelyNef k sX π D) :
    MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hD, -⟩ := h
  exact ⟨m, r, L, hL, by simp only [hD, MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- In characteristic zero a normal variety has a smooth projective birational model. -/
private theorem exists_smooth_model {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] [IsNormal X] :
    ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (w : W ⟶ X), AlgebraicGeometry.IsVariety k (w ≫ sX) ∧
      MMP.Mori.IsSmoothScheme (w ≫ sX) ∧
      IsProjectiveMorphism w ∧ IsBirationalMorphism w := by
  have : ∀ i : Empty, IsProper ((fun i : Empty => (i.elim : (Empty.elim i : Scheme.{u}) ⟶ X)) i) :=
    fun i => i.elim
  obtain ⟨W, w, hW, bw, -, hsm, pw, -, -, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq sX
      (X := Empty.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (κ := Empty) Empty.elim (fun j => j.elim)
  have : AlgebraicGeometry.IsVariety k (w ≫ sX) := hW.1
  have : IsIntegral W := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := w ≫ sX)
  have : IsNormal W := hW.2
  have : LocallyOfFiniteType (w ≫ sX) := hW.1.toLocallyOfFiniteType
  have : QuasiCompact (w ≫ sX) := hW.1.toQuasiCompact
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sX)
  exact ⟨W, inferInstance, inferInstance, inferInstance,
    QuasiCompact.compactSpace_of_compactSpace (w ≫ sX), w, hW.1, hsm, pw, bw⟩

/-- In characteristic zero two proper birational models of a normal variety have a common
smooth projective birational model. -/
private theorem exists_common_smooth_model {k : Type u} [Field k] [CharZero k]
    {Z W W' : Scheme.{u}} [IsNormal Z] [IsNormal W] [IsNormal W']
    (s : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k s]
    (p : W ⟶ Z) (q : W' ⟶ Z) [IsProper p] [IsProper q]
    (bp : IsBirationalMorphism p) (bq : IsBirationalMorphism q)
    (hp : AlgebraicGeometry.IsVariety k (p ≫ s)) (hq : AlgebraicGeometry.IsVariety k (q ≫ s)) :
    ∃ (V : Scheme.{u}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (_ : CompactSpace V) (w : V ⟶ Z) (g₀ : V ⟶ W) (g₁ : V ⟶ W'),
      AlgebraicGeometry.IsVariety k (w ≫ s) ∧ MMP.Mori.IsSmoothScheme (w ≫ s) ∧
      g₀ ≫ p = w ∧ g₁ ≫ q = w ∧ IsProjectiveMorphism g₀ ∧ IsProjectiveMorphism g₁ ∧
      IsBirationalMorphism g₀ ∧ IsBirationalMorphism g₁ := by
  let X : Bool → Scheme.{u} := fun b => cond b W' W
  let F : ∀ b, X b ⟶ Z := fun b => match b with
    | false => p
    | true => q
  have : ∀ b, IsProper (F b) := fun b => match b with
    | false => inferInstanceAs (IsProper p)
    | true => inferInstanceAs (IsProper q)
  have hFb : ∀ b, IsBirationalMorphism (F b) := fun b => match b with
    | false => bp
    | true => bq
  have hFn : ∀ b, IsNormalVariety k (F b ≫ s) := fun b => match b with
    | false => by
        change IsNormalVariety k (p ≫ s)
        exact ⟨hp, inferInstance⟩
    | true => by
        change IsNormalVariety k (q ≫ s)
        exact ⟨hq, inferInstance⟩
  obtain ⟨V, w, hV, -, g, hsm, -, hg, -, -⟩ :=
    MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq s F hFb hFn
      (κ := Empty) Empty.elim (fun j => j.elim)
  have : AlgebraicGeometry.IsVariety k (w ≫ s) := hV.1
  have : IsIntegral V := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := w ≫ s)
  have : IsNormal V := hV.2
  have : LocallyOfFiniteType (w ≫ s) := hV.1.toLocallyOfFiniteType
  have : QuasiCompact (w ≫ s) := hV.1.toQuasiCompact
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (w ≫ s)
  exact ⟨V, inferInstance, inferInstance, inferInstance,
    QuasiCompact.compactSpace_of_compactSpace (w ≫ s), w, g false, g true, hV.1, hsm,
    (hg false).1, (hg true).1, (hg false).2.1, (hg true).2.1, (hg false).2.2, (hg true).2.2⟩

/-- On a common model `p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂` of a nef-model equivalence over `S`, the two
composites `W ⟶ S` agree. -/
private theorem comp_eq_comp_of_isNefModelEquivalent {k : Type u} [Field k]
    {Z₁ Z₂ S W : Scheme.{u}} [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
    [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂] [IsIntegral W]
    {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)} [QuasiCompact s₁] [QuasiCompact s₂]
    {sS : S ⟶ Spec (.of k)} [IsSeparated sS] {sW : W ⟶ Spec (.of k)} {π₁ : Z₁ ⟶ S}
    {π₂ : Z₂ ⟶ S} {K₁ : Divisor Z₁} {C₁ : RDivisor Z₁} {K₂ : Divisor Z₂} {C₂ : RDivisor Z₂}
    {ψ : Z₁.RationalMap Z₂} (E : MMP.Fourfold.IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ)
    {p₁ : W ⟶ Z₁} {p₂ : W ⟶ Z₂} (hp₁ : p₁ ≫ s₁ = sW) (hp₂ : p₂ ≫ s₂ = sW)
    (bp₁ : IsBirationalMorphism p₁) {h : Z₁.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h) (hc : h.compHom p₂ = ψ) :
    p₁ ≫ π₁ = p₂ ≫ π₂ :=
  comp_eq_comp_of_isOver sS π₁ π₂ E.isOver p₁ p₂ bp₁ hh hc
    (by rw [Category.assoc, E.comp_eq₁, hp₁, Category.assoc, E.comp_eq₂, hp₂])

/-- **Part (1).** Pull-back along a projective birational morphism preserves and reflects
equality of zero-degree curve sets over the base. -/
private theorem forall_isNull_iff_iff_of_isRCartierPullback {k : Type u} [Field k]
    {X X' S : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [QuasiCompact sX] [QuasiCompact sX']
    (hX : MMP.Mori.IsVariety k sX) (hX' : MMP.Mori.IsVariety k sX')
    (f : X' ⟶ X) (hf : f ≫ sX = sX') (hfp : IsProjectiveMorphism f)
    (hfb : IsBirationalMorphism f) (π : X ⟶ S) {D₁ D₂ : RDivisor X} {D₁' D₂' : RDivisor X'}
    (_ : MMP.Flips.IsRelativelyNef k sX π D₁) (_ : MMP.Flips.IsRelativelyNef k sX π D₂)
    (hD₁ : MMP.Flips.IsRCartierPullback f D₁ D₁') (hD₂ : MMP.Flips.IsRCartierPullback f D₂ D₂') :
    (∀ Γ : ProperCurve sX, Γ.IsContractedBy π → (IsNull k sX D₁ Γ ↔ IsNull k sX D₂ Γ)) ↔
      ∀ Γ : ProperCurve sX', Γ.IsContractedBy (f ≫ π) →
        (IsNull k sX' D₁' Γ ↔ IsNull k sX' D₂' Γ) := by
  have := hX
  have := hX'
  have : IsProper f := isProper_of_isProjectiveMorphism f hfp
  have := hfb.isDominant
  have : Surjective f := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  constructor
  · intro H Γ' hΓ'
    rw [isNull_iff_nullAt f hf hD₁, isNull_iff_nullAt f hf hD₂]
    by_cases hc : Γ'.IsContractedBy f
    · exact iff_of_true (nullAt_of_isContractedBy f hf _ hc) (nullAt_of_isContractedBy f hf _ hc)
    · rw [nullAt_iff k sX D₁ ⟨f Γ'.point, isProperCurve_map f hf Γ' hc⟩ rfl,
        nullAt_iff k sX D₂ ⟨f Γ'.point, isProperCurve_map f hf Γ' hc⟩ rfl]
      exact H _ (isContractedBy_map f hf π Γ' hc hΓ')
  · intro H Γ hΓ
    obtain ⟨Γ', hΓ'⟩ := exists_properCurve_map_eq sX' sX f hf (f.surjective Γ.point)
      Γ.isProperCurve
    have := H Γ' (isContractedBy_comp_of_map_eq f π hΓ' hΓ)
    rwa [isNull_iff_nullAt f hf hD₁, isNull_iff_nullAt f hf hD₂, hΓ', nullAt_iff k sX D₁ Γ rfl,
      nullAt_iff k sX D₂ Γ rfl] at this

/-- **Part (2).** Nef-model equivalence is symmetric along an inverse birational map. -/
private theorem isNefModelEquivalent_symm {k : Type u} [Field k] {Z₁ Z₂ S : Scheme.{u}}
    [IsIntegral Z₁]
    [IsLocallyNoetherian Z₁] [IsNormal Z₁] [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    (s₁ : Z₁ ⟶ Spec (.of k)) (s₂ : Z₂ ⟶ Spec (.of k)) [QuasiCompact s₁] [QuasiCompact s₂]
    (sS : S ⟶ Spec (.of k)) [IsSeparated sS] (π₁ : Z₁ ⟶ S) (π₂ : Z₂ ⟶ S)
    (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁) (K₂ : Divisor Z₂) (C₂ : RDivisor Z₂)
    (ψ : Z₁.RationalMap Z₂) (ψ' : Z₂.RationalMap Z₁)
    (E : MMP.Fourfold.IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ)
    (hinv : MMP.Mori.RationalMap.IsInverse ψ ψ') :
    MMP.Fourfold.IsNefModelEquivalent s₂ s₁ sS π₂ π₁ K₂ C₂ K₁ C₁ ψ' := by
  obtain ⟨W, _, _, _, sW, _, p₁, p₂, h, hW, hsm, hp₁, hp₂, pp₁, pp₂, bp₁, bp₂, hh, hc, D₁, D₂,
    hD₁, hD₂, hZ⟩ := E.exists_resolution
  obtain ⟨h', hh'⟩ := bp₂.exists_isInverse
  have hψ' : h'.compHom p₁ = ψ' :=
    compHom_eq_of_isInverse_compHom p₁ p₂ bp₁ bp₂ hh hh' (hc ▸ hinv)
  have hπ := comp_eq_comp_of_isNefModelEquivalent E hp₁ hp₂ bp₁ hh hc
  refine ⟨E.isNormalVariety₂, E.isProjectiveVariety₂, E.comp_eq₂, E.isCanonicalDivisor₂,
    E.isRelativelyNef₂, E.isNormalVariety₁, E.isProjectiveVariety₁, E.comp_eq₁,
    E.isCanonicalDivisor₁, E.isRelativelyNef₁, hinv.isBirational_inverse, ?_, ?_⟩
  · rw [MMP.Flips.RationalMap.IsOver, ← hψ', compHom_compHom, hπ, ← compHom_compHom,
      hh'.compHom_eq_id, Scheme.RationalMap.id_compHom]
  · exact ⟨W, inferInstance, inferInstance, inferInstance, sW, inferInstance, p₂, p₁, h', hW,
      hsm, hp₂, hp₁, pp₂, pp₁, bp₂, bp₁, hh', hψ', D₂, D₁, hD₂, hD₁,
      fun Γ hΓ => (hZ Γ (by
        rw [hπ]
        exact hΓ)).symm⟩

/-- **Part (3), reflexivity**, in characteristic zero. -/
private theorem isNefModelEquivalent_refl {k : Type u} [Field k] (hk : CharZero k)
    {Z₁ S : Scheme.{u}}
    [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁] (s₁ : Z₁ ⟶ Spec (.of k))
    [QuasiCompact s₁] (sS : S ⟶ Spec (.of k)) [IsSeparated sS] (π₁ : Z₁ ⟶ S) (K₁ : Divisor Z₁)
    (C₁ : RDivisor Z₁) (hn : IsNormalVariety k s₁) (hpv : MMP.Mori.IsProjectiveVariety k s₁)
    (hc : π₁ ≫ sS = s₁) (hK : ∃ m : ℕ, K₁.IsCanonicalDivisor s₁ m)
    (hnef : MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor K₁ C₁)) :
    MMP.Fourfold.IsNefModelEquivalent s₁ s₁ sS π₁ π₁ K₁ C₁ K₁ C₁
      (Scheme.RationalMap.id Z₁) := by
  have : AlgebraicGeometry.IsVariety k s₁ := hn.1
  obtain ⟨W, _, _, _, _, w, hW, hsm, pw, bw⟩ := exists_smooth_model s₁
  have := bw.isDominant
  obtain ⟨h, hh⟩ := bw.exists_isInverse
  obtain ⟨G, hG, -⟩ :=
    MMP.Flips.existsUnique_isRCartierPullback w (isCartierCombination_of_isRelativelyNef hnef)
  refine ⟨hn, hpv, hc, hK, hnef, hn, hpv, hc, hK, hnef, MMP.Mori.RationalMap.isBirational_id,
    Scheme.RationalMap.id_compHom π₁, ?_⟩
  exact ⟨W, inferInstance, inferInstance, inferInstance, w ≫ s₁, inferInstance, w, w, h, hW,
    hsm, rfl, rfl, pw, pw, bw, bw, hh, hh.compHom_eq_id, G, G, hG, hG,
    fun Γ _ => Iff.rfl⟩

/-- **Part (3), transitivity**, in characteristic zero. -/
private theorem isNefModelEquivalent_trans {k : Type u} [Field k] (hk : CharZero k)
    {Z₁ Z₂ Z₃ S : Scheme.{u}}
    [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
    [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    [IsIntegral Z₃] [IsLocallyNoetherian Z₃] [IsNormal Z₃]
    (s₁ : Z₁ ⟶ Spec (.of k)) (s₂ : Z₂ ⟶ Spec (.of k)) (s₃ : Z₃ ⟶ Spec (.of k))
    [QuasiCompact s₁] [QuasiCompact s₂] [QuasiCompact s₃]
    (sS : S ⟶ Spec (.of k)) [IsSeparated sS]
    (π₁ : Z₁ ⟶ S) (π₂ : Z₂ ⟶ S) (π₃ : Z₃ ⟶ S) (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁)
    (K₂ : Divisor Z₂) (C₂ : RDivisor Z₂) (K₃ : Divisor Z₃) (C₃ : RDivisor Z₃)
    (ψ₁₂ : Z₁.RationalMap Z₂) [ψ₁₂.IsDominant] (ψ₂₃ : Z₂.RationalMap Z₃)
    (E₁₂ : MMP.Fourfold.IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ₁₂)
    (E₂₃ : MMP.Fourfold.IsNefModelEquivalent s₂ s₃ sS π₂ π₃ K₂ C₂ K₃ C₃ ψ₂₃) :
    MMP.Fourfold.IsNefModelEquivalent s₁ s₃ sS π₁ π₃ K₁ C₁ K₃ C₃ (ψ₁₂.comp ψ₂₃) := by
  obtain ⟨W, _, _, _, sW, _, p₁, p₂, h₁₂, hW, -, hp₁, hp₂, pp₁, pp₂, bp₁, bp₂, hh₁₂, hc₁₂, D₁,
    D₂, hD₁, hD₂, hZ₁₂⟩ := E₁₂.exists_resolution
  obtain ⟨W', _, _, _, sW', _, q₂, q₃, h₂₃, hW', -, hq₂, hq₃, pq₂, pq₃, bq₂, bq₃, hh₂₃, hc₂₃,
    D₂', D₃, hD₂', hD₃, hZ₂₃⟩ := E₂₃.exists_resolution
  have : AlgebraicGeometry.IsVariety k s₁ := E₁₂.isNormalVariety₁.1
  have : AlgebraicGeometry.IsVariety k s₂ := E₁₂.isNormalVariety₂.1
  have : AlgebraicGeometry.IsVariety k s₃ := E₂₃.isNormalVariety₂.1
  have : AlgebraicGeometry.IsVariety k sW := hW
  have : AlgebraicGeometry.IsVariety k sW' := hW'
  have : IsProper p₂ := isProper_of_isProjectiveMorphism p₂ pp₂
  have : IsProper q₂ := isProper_of_isProjectiveMorphism q₂ pq₂
  obtain ⟨V, _, _, _, _, w, g₀, g₁, hV, hsm, hg₀, hg₁, pg₀, pg₁, bg₀, bg₁⟩ :=
    exists_common_smooth_model s₂ p₂ q₂ bp₂ bq₂ (by rw [hp₂]; exact hW) (by rw [hq₂]; exact hW')
  have : AlgebraicGeometry.IsVariety k (w ≫ s₂) := hV
  have hgW : g₀ ≫ sW = w ≫ s₂ := by rw [← hp₂, ← Category.assoc, hg₀]
  have hgW' : g₁ ≫ sW' = w ≫ s₂ := by rw [← hq₂, ← Category.assoc, hg₁]
  have hP₁ : (g₀ ≫ p₁) ≫ s₁ = w ≫ s₂ := by rw [Category.assoc, hp₁, hgW]
  have hP₃ : (g₁ ≫ q₃) ≫ s₃ = w ≫ s₂ := by rw [Category.assoc, hq₃, hgW']
  have bP₁ := MMP.Mori.isBirationalMorphism_comp bg₀ bp₁
  have bP₃ := MMP.Mori.isBirationalMorphism_comp bg₁ bq₃
  have := bP₁.isDominant
  have := bP₃.isDominant
  obtain ⟨H, hH⟩ := bP₁.exists_isInverse
  have hHc : H.compHom (g₁ ≫ q₃) = ψ₁₂.comp ψ₂₃ :=
    compHom_eq_comp_of_isInverse g₀ g₁ p₁ p₂ q₂ q₃ (hg₀.trans hg₁.symm) bg₀ bg₁ bp₁ bp₂ bq₂ bP₁
      hh₁₂ hh₂₃ hH hc₁₂ hc₂₃
  have hπ₁₂ := comp_eq_comp_of_isNefModelEquivalent E₁₂ hp₁ hp₂ bp₁ hh₁₂ hc₁₂
  have hπ₂₃ := comp_eq_comp_of_isNefModelEquivalent E₂₃ hq₂ hq₃ bq₂ hh₂₃ hc₂₃
  have hπ₀ : g₀ ≫ p₁ ≫ π₁ = g₁ ≫ q₂ ≫ π₂ := by
    rw [hπ₁₂, ← Category.assoc, hg₀, ← hg₁, Category.assoc]
  have hπ : (g₀ ≫ p₁) ≫ π₁ = (g₁ ≫ q₃) ≫ π₃ := by
    rw [Category.assoc, hπ₀, hπ₂₃, Category.assoc]
  obtain ⟨G₁, hG₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (g₀ ≫ p₁)
    (isCartierCombination_of_isRelativelyNef E₁₂.isRelativelyNef₁)
  obtain ⟨G₃, hG₃, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (g₁ ≫ q₃)
    (isCartierCombination_of_isRelativelyNef E₂₃.isRelativelyNef₂)
  refine ⟨E₁₂.isNormalVariety₁, E₁₂.isProjectiveVariety₁, E₁₂.comp_eq₁, E₁₂.isCanonicalDivisor₁,
    E₁₂.isRelativelyNef₁, E₂₃.isNormalVariety₂, E₂₃.isProjectiveVariety₂, E₂₃.comp_eq₂,
    E₂₃.isCanonicalDivisor₂, E₂₃.isRelativelyNef₂,
    hHc ▸ hH.isBirational_compHom bP₃, ?_, ?_⟩
  · rw [MMP.Flips.RationalMap.IsOver, ← hHc, compHom_compHom, ← hπ, ← compHom_compHom,
      hH.compHom_eq_id, Scheme.RationalMap.id_compHom]
  · refine ⟨V, inferInstance, inferInstance, inferInstance, w ≫ s₂, inferInstance, g₀ ≫ p₁,
      g₁ ≫ q₃, H, hV, hsm, hP₁, hP₃, IsProjectiveMorphism.comp pg₀ pp₁,
      IsProjectiveMorphism.comp pg₁ pq₃, bP₁, bP₃, hH, hHc, G₁, G₃, hG₁, hG₃,
      fun Γ hΓ => ?_⟩
    change IsNull k (w ≫ s₂) G₁ Γ ↔ IsNull k (w ≫ s₂) G₃ Γ
    rw [isNull_iff_nullAt (g₀ ≫ p₁) hP₁ hG₁ Γ, isNull_iff_nullAt (g₁ ≫ q₃) hP₃ hG₃ Γ]
    simp only [Scheme.Hom.comp_apply]
    have e1 := nullAt_iff_nullAt_of_model π₁ p₁ p₂ hp₁ hp₂ hD₁ hD₂ hZ₁₂ g₀ hgW Γ
      (by simpa only [Category.assoc] using hΓ)
    have e2 := nullAt_iff_nullAt_of_model π₂ q₂ q₃ hq₂ hq₃ hD₂' hD₃ hZ₂₃ g₁ hgW' Γ
      (by rw [← hπ₀]; simpa only [Category.assoc] using hΓ)
    have hpt : p₂ (g₀ Γ.point) = q₂ (g₁ Γ.point) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg₀, hg₁]
    rw [hpt] at e1
    exact e1.trans e2

section Test

variable {k : Type u} [Field k] {Z₁ Z₂ S W : Scheme.{u}}
  [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
  [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂] [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W] {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)} [QuasiCompact s₁]
  [QuasiCompact s₂] {sS : S ⟶ Spec (.of k)} [IsSeparated sS] {sW : W ⟶ Spec (.of k)}
  [QuasiCompact sW] {π₁ : Z₁ ⟶ S} {π₂ : Z₂ ⟶ S} {K₁ : Divisor Z₁} {C₁ : RDivisor Z₁}
  {K₂ : Divisor Z₂} {C₂ : RDivisor Z₂} {ψ : Z₁.RationalMap Z₂} {p₁ : W ⟶ Z₁} {p₂ : W ⟶ Z₂}
  {h : Z₁.RationalMap W} {D₁ D₂ : RDivisor W}

/-- **Part (4), forward.** Equivalent nef models have the same zero-degree curves on every
common projective birational model. -/
private theorem isNull_iff_of_isNefModelEquivalent
    (E : MMP.Fourfold.IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ)
    (hWv : MMP.Mori.IsVariety k sW) (hp₁ : p₁ ≫ s₁ = sW) (hp₂ : p₂ ≫ s₂ = sW)
    (bp₁ : IsBirationalMorphism p₁)
    (hh : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h) (hc : h.compHom p₂ = ψ)
    (hD₁ : MMP.Flips.IsRCartierPullback p₁ (MMP.Flips.logCanonicalDivisor K₁ C₁) D₁)
    (hD₂ : MMP.Flips.IsRCartierPullback p₂ (MMP.Flips.logCanonicalDivisor K₂ C₂) D₂)
    (Γ : ProperCurve sW) (hΓ : Γ.IsContractedBy (p₁ ≫ π₁)) :
    IsNull k sW D₁ Γ ↔ IsNull k sW D₂ Γ := by
  have : AlgebraicGeometry.IsVariety k sW := hWv
  obtain ⟨W₀, _, _, _, sW₀, _, q₁, q₂, h₀, hW₀, -, hq₁, hq₂, pq₁, pq₂, bq₁, bq₂, hh₀, hc₀, D₁₀,
    D₂₀, hD₁₀, hD₂₀, hZ⟩ := E.exists_resolution
  have : AlgebraicGeometry.IsVariety k s₁ := E.isNormalVariety₁.1
  have : AlgebraicGeometry.IsVariety k s₂ := E.isNormalVariety₂.1
  have : AlgebraicGeometry.IsVariety k sW₀ := hW₀
  have : IsProper s₁ := isProper_of_isProjectiveMorphism s₁ E.isProjectiveVariety₁.isProjective
  have : IsProper q₁ := isProper_of_isProjectiveMorphism q₁ pq₁
  rw [isNull_iff_nullAt p₁ hp₁ hD₁ Γ, isNull_iff_nullAt p₂ hp₂ hD₂ Γ]
  by_cases hcon : Γ.IsContractedBy (pullback.lift p₁ p₂ (hp₁.trans hp₂.symm))
  · exact iff_of_true
      (nullAt_of_isContractedBy p₁ hp₁ _ (by
        simpa only [pullback.lift_fst] using isContractedBy_comp hcon (pullback.fst s₁ s₂)))
      (nullAt_of_isContractedBy p₂ hp₂ _ (by
        simpa only [pullback.lift_snd] using isContractedBy_comp hcon (pullback.snd s₁ s₂)))
  · obtain ⟨Γ₀, h1, h2⟩ := exists_properCurve_of_models p₁ p₂ q₁ q₂ hp₁ hp₂ hq₁ hq₂ bp₁ bq₁
      hh hh₀ (hc.trans hc₀.symm) Γ hcon
    have hΓ₀ : Γ₀.IsContractedBy (q₁ ≫ π₁) := fun x hx => by
      have hx' : q₁ x ∈ closure {p₁ Γ.point} := by
        rw [← h1]
        exact specializes_iff_mem_closure.mp
          ((specializes_iff_mem_closure.mpr hx).map q₁.continuous)
      rw [← Γ.range_comp p₁ hp₁] at hx'
      obtain ⟨c, hcx⟩ := hx'
      simpa only [Scheme.Hom.comp_apply, h1, ← hcx] using hΓ (Γ.ι c) (Γ.range_ι ▸ ⟨c, rfl⟩)
    have := hZ Γ₀ hΓ₀
    change IsNull k sW₀ D₁₀ Γ₀ ↔ IsNull k sW₀ D₂₀ Γ₀ at this
    rwa [isNull_iff_nullAt q₁ hq₁ hD₁₀ Γ₀, isNull_iff_nullAt q₂ hq₂ hD₂₀ Γ₀, h1, h2] at this

/-- **Part (4), converse.** In characteristic zero, two nef real models over `S` whose
pulled-back adjoints have the same zero-degree curves on one common model are equivalent. -/
private theorem isNefModelEquivalent_of_isNull
    (hWv : MMP.Mori.IsVariety k sW) (hp₁ : p₁ ≫ s₁ = sW) (hp₂ : p₂ ≫ s₂ = sW)
    (pp₁ : IsProjectiveMorphism p₁) (pp₂ : IsProjectiveMorphism p₂)
    (bp₁ : IsBirationalMorphism p₁) (bp₂ : IsBirationalMorphism p₂)
    (hh : MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h) (hc : h.compHom p₂ = ψ)
    (hD₁ : MMP.Flips.IsRCartierPullback p₁ (MMP.Flips.logCanonicalDivisor K₁ C₁) D₁)
    (hD₂ : MMP.Flips.IsRCartierPullback p₂ (MMP.Flips.logCanonicalDivisor K₂ C₂) D₂)
    (hk : CharZero k) (hn₁ : IsNormalVariety k s₁) (hpv₁ : MMP.Mori.IsProjectiveVariety k s₁)
    (hc₁ : π₁ ≫ sS = s₁) (hK₁ : ∃ m : ℕ, K₁.IsCanonicalDivisor s₁ m)
    (hnef₁ : MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor K₁ C₁))
    (hn₂ : IsNormalVariety k s₂) (hpv₂ : MMP.Mori.IsProjectiveVariety k s₂)
    (hc₂ : π₂ ≫ sS = s₂) (hK₂ : ∃ m : ℕ, K₂.IsCanonicalDivisor s₂ m)
    (hnef₂ : MMP.Flips.IsRelativelyNef k s₂ π₂ (MMP.Flips.logCanonicalDivisor K₂ C₂))
    (hover : MMP.Flips.RationalMap.IsOver π₁ π₂ ψ)
    (hZ : ∀ Γ : ProperCurve sW, Γ.IsContractedBy (p₁ ≫ π₁) →
      (IsNull k sW D₁ Γ ↔ IsNull k sW D₂ Γ)) :
    MMP.Fourfold.IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ := by
  have : AlgebraicGeometry.IsVariety k sW := hWv
  obtain ⟨W', _, _, _, _, w, hW', hsm, pw, bw⟩ := exists_smooth_model sW
  have : AlgebraicGeometry.IsVariety k s₁ := hn₁.1
  have : AlgebraicGeometry.IsVariety k s₂ := hn₂.1
  have bP₁ := MMP.Mori.isBirationalMorphism_comp bw bp₁
  have bP₂ := MMP.Mori.isBirationalMorphism_comp bw bp₂
  have := bw.isDominant
  have := bP₁.isDominant
  have := bP₂.isDominant
  obtain ⟨H, hH⟩ := bP₁.exists_isInverse
  have hHc : H.compHom (w ≫ p₂) = ψ := (hh.compHom_comp_eq hH p₂).trans hc
  obtain ⟨G₁, hG₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (w ≫ p₁)
    (isCartierCombination_of_isRelativelyNef hnef₁)
  obtain ⟨G₂, hG₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback (w ≫ p₂)
    (isCartierCombination_of_isRelativelyNef hnef₂)
  have hP₁ : (w ≫ p₁) ≫ s₁ = w ≫ sW := by rw [Category.assoc, hp₁]
  have hP₂ : (w ≫ p₂) ≫ s₂ = w ≫ sW := by rw [Category.assoc, hp₂]
  refine ⟨hn₁, hpv₁, hc₁, hK₁, hnef₁, hn₂, hpv₂, hc₂, hK₂, hnef₂,
    hc ▸ hh.isBirational_compHom bp₂, hover,
    ⟨W', inferInstance, inferInstance, inferInstance, w ≫ sW, inferInstance, w ≫ p₁, w ≫ p₂, H,
      hW', hsm, hP₁, hP₂, IsProjectiveMorphism.comp pw pp₁,
      IsProjectiveMorphism.comp pw pp₂,
      bP₁, bP₂, hH, hHc, G₁, G₂, hG₁, hG₂, fun Γ hΓ => ?_⟩⟩
  change IsNull k (w ≫ sW) G₁ Γ ↔ IsNull k (w ≫ sW) G₂ Γ
  rw [isNull_iff_nullAt (w ≫ p₁) hP₁ hG₁ Γ, isNull_iff_nullAt (w ≫ p₂) hP₂ hG₂ Γ]
  simp only [Scheme.Hom.comp_apply]
  exact nullAt_iff_nullAt_of_model π₁ p₁ p₂ hp₁ hp₂ hD₁ hD₂ hZ w rfl Γ
    (by simpa only [Category.assoc] using hΓ)

end Test

end Parts

end MMP.Fourfold.NefModelEquivalence

namespace MMP.Fourfold

open MMP.Fourfold.NefModelEquivalence

open MMP.Mori

/-- **Nef-model equivalence is unchanged by refinement.**

1. Let `f : X' ⟶ X` be a projective birational morphism of normal varieties over `k`, `π : X ⟶ S`,
   and `D₁`, `D₂` `ℝ`-divisors on `X` nef over `S` with pull-backs `D₁'`, `D₂'` to `X'`. Then
   `D₁`, `D₂` have the same zero-degree curves over `S` if and only if `D₁'`, `D₂'` do.
2. Over a base `S` separated over `k`, `MMP.Fourfold.IsNefModelEquivalent` is symmetric along an
   inverse birational map.
3. Over a field of characteristic zero it is reflexive (along the identity) and transitive
   (along the composite `ψ₁₂.comp ψ₂₃`).
4. Equivalent nef models have the same zero-degree curves over `S` on every common projective
   birational normal model `W` (`p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂`, `p₂ = ψ ∘ p₁`); conversely, in
   characteristic zero, two nef real models over `S` with a birational map `ψ` over `S` whose
   pulled-back adjoints have the same zero-degree curves on one such `W` are equivalent. -/
@[mmp "lem_fourfold_nef_equivalence_refinement"]
public theorem isNefModelEquivalent_equivalence_and_refinement {k : Type u} [Field k] :
    -- (1) pull-back preserves and reflects equality of zero-degree curve sets
    (∀ {X X' S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
      [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
      (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k)) [QuasiCompact sX] [QuasiCompact sX']
      (_ : MMP.Mori.IsVariety k sX) (_ : MMP.Mori.IsVariety k sX')
      (f : X' ⟶ X) (_ : f ≫ sX = sX') (_ : IsProjectiveMorphism f)
      (_ : IsBirationalMorphism f) (π : X ⟶ S) {D₁ D₂ : RDivisor X} {D₁' D₂' : RDivisor X'}
      (_ : MMP.Flips.IsRelativelyNef k sX π D₁) (_ : MMP.Flips.IsRelativelyNef k sX π D₂)
      (_ : MMP.Flips.IsRCartierPullback f D₁ D₁') (_ : MMP.Flips.IsRCartierPullback f D₂ D₂'),
      (∀ Γ : ProperCurve sX, Γ.IsContractedBy π →
        ((∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            MMP.Flips.IsRIntersectionNumber k sX D₁ r L Γ x → x = 0) ↔
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            MMP.Flips.IsRIntersectionNumber k sX D₂ r L Γ x → x = 0)) ↔
      (∀ Γ : ProperCurve sX', Γ.IsContractedBy (f ≫ π) →
        ((∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X') (x : ℝ),
            MMP.Flips.IsRIntersectionNumber k sX' D₁' r L Γ x → x = 0) ↔
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X') (x : ℝ),
            MMP.Flips.IsRIntersectionNumber k sX' D₂' r L Γ x → x = 0))) ∧
    -- (2) symmetry
    (∀ {Z₁ Z₂ S : Scheme.{u}} [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
      [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
      (s₁ : Z₁ ⟶ Spec (.of k)) (s₂ : Z₂ ⟶ Spec (.of k)) [QuasiCompact s₁] [QuasiCompact s₂]
      (sS : S ⟶ Spec (.of k)) [IsSeparated sS] (π₁ : Z₁ ⟶ S) (π₂ : Z₂ ⟶ S)
      (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁)
      (K₂ : Divisor Z₂) (C₂ : RDivisor Z₂) (ψ : Z₁.RationalMap Z₂) (ψ' : Z₂.RationalMap Z₁),
      IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ →
        MMP.Mori.RationalMap.IsInverse ψ ψ' →
        IsNefModelEquivalent s₂ s₁ sS π₂ π₁ K₂ C₂ K₁ C₁ ψ') ∧
    -- (3) reflexivity and transitivity in characteristic zero
    (CharZero k →
      (∀ {Z₁ S : Scheme.{u}} [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
        (s₁ : Z₁ ⟶ Spec (.of k)) [QuasiCompact s₁] (sS : S ⟶ Spec (.of k)) [IsSeparated sS]
        (π₁ : Z₁ ⟶ S)
        (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁),
        IsNormalVariety k s₁ → MMP.Mori.IsProjectiveVariety k s₁ → π₁ ≫ sS = s₁ →
          (∃ m : ℕ, K₁.IsCanonicalDivisor s₁ m) →
          MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor K₁ C₁) →
          IsNefModelEquivalent s₁ s₁ sS π₁ π₁ K₁ C₁ K₁ C₁ (Scheme.RationalMap.id Z₁)) ∧
      (∀ {Z₁ Z₂ Z₃ S : Scheme.{u}} [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
        [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
        [IsIntegral Z₃] [IsLocallyNoetherian Z₃] [IsNormal Z₃]
        (s₁ : Z₁ ⟶ Spec (.of k)) (s₂ : Z₂ ⟶ Spec (.of k)) (s₃ : Z₃ ⟶ Spec (.of k))
        [QuasiCompact s₁] [QuasiCompact s₂] [QuasiCompact s₃]
        (sS : S ⟶ Spec (.of k)) [IsSeparated sS]
        (π₁ : Z₁ ⟶ S) (π₂ : Z₂ ⟶ S) (π₃ : Z₃ ⟶ S) (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁)
        (K₂ : Divisor Z₂) (C₂ : RDivisor Z₂) (K₃ : Divisor Z₃) (C₃ : RDivisor Z₃)
        (ψ₁₂ : Z₁.RationalMap Z₂) [ψ₁₂.IsDominant] (ψ₂₃ : Z₂.RationalMap Z₃),
        IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ₁₂ →
          IsNefModelEquivalent s₂ s₃ sS π₂ π₃ K₂ C₂ K₃ C₃ ψ₂₃ →
          IsNefModelEquivalent s₁ s₃ sS π₁ π₃ K₁ C₁ K₃ C₃ (ψ₁₂.comp ψ₂₃))) ∧
    -- (4) equivalence can be tested on any common higher projective model
    (∀ {Z₁ Z₂ S W : Scheme.{u}} [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
      [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
      [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
      (s₁ : Z₁ ⟶ Spec (.of k)) (s₂ : Z₂ ⟶ Spec (.of k)) [QuasiCompact s₁] [QuasiCompact s₂]
      (sS : S ⟶ Spec (.of k)) [IsSeparated sS] (sW : W ⟶ Spec (.of k)) [QuasiCompact sW]
      (π₁ : Z₁ ⟶ S) (π₂ : Z₂ ⟶ S) (K₁ : Divisor Z₁) (C₁ : RDivisor Z₁)
      (K₂ : Divisor Z₂) (C₂ : RDivisor Z₂) (ψ : Z₁.RationalMap Z₂)
      (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂) (h : Z₁.RationalMap W) {D₁ D₂ : RDivisor W},
      MMP.Mori.IsVariety k sW → p₁ ≫ s₁ = sW → p₂ ≫ s₂ = sW →
        IsProjectiveMorphism p₁ → IsProjectiveMorphism p₂ → IsBirationalMorphism p₁ →
        IsBirationalMorphism p₂ → MMP.Mori.RationalMap.IsInverse p₁.toRationalMap h →
        h.compHom p₂ = ψ →
        MMP.Flips.IsRCartierPullback p₁ (MMP.Flips.logCanonicalDivisor K₁ C₁) D₁ →
        MMP.Flips.IsRCartierPullback p₂ (MMP.Flips.logCanonicalDivisor K₂ C₂) D₂ →
        (IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ →
          ∀ Γ : ProperCurve sW, Γ.IsContractedBy (p₁ ≫ π₁) →
            ((∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
                MMP.Flips.IsRIntersectionNumber k sW D₁ r L Γ x → x = 0) ↔
              ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
                MMP.Flips.IsRIntersectionNumber k sW D₂ r L Γ x → x = 0)) ∧
        (CharZero k → IsNormalVariety k s₁ → MMP.Mori.IsProjectiveVariety k s₁ →
          π₁ ≫ sS = s₁ → (∃ m : ℕ, K₁.IsCanonicalDivisor s₁ m) →
          MMP.Flips.IsRelativelyNef k s₁ π₁ (MMP.Flips.logCanonicalDivisor K₁ C₁) →
          IsNormalVariety k s₂ → MMP.Mori.IsProjectiveVariety k s₂ → π₂ ≫ sS = s₂ →
          (∃ m : ℕ, K₂.IsCanonicalDivisor s₂ m) →
          MMP.Flips.IsRelativelyNef k s₂ π₂ (MMP.Flips.logCanonicalDivisor K₂ C₂) →
          MMP.Flips.RationalMap.IsOver π₁ π₂ ψ →
          (∀ Γ : ProperCurve sW, Γ.IsContractedBy (p₁ ≫ π₁) →
            ((∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
                MMP.Flips.IsRIntersectionNumber k sW D₁ r L Γ x → x = 0) ↔
              ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (x : ℝ),
                MMP.Flips.IsRIntersectionNumber k sW D₂ r L Γ x → x = 0)) →
          IsNefModelEquivalent s₁ s₂ sS π₁ π₂ K₁ C₁ K₂ C₂ ψ)) :=
  ⟨forall_isNull_iff_iff_of_isRCartierPullback, isNefModelEquivalent_symm,
    fun hk => ⟨isNefModelEquivalent_refl hk, isNefModelEquivalent_trans hk⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hWv hp₁ hp₂ pp₁ pp₂ bp₁ bp₂ hh hc hD₁ hD₂ =>
      ⟨fun E => isNull_iff_of_isNefModelEquivalent E hWv hp₁ hp₂ bp₁ hh hc hD₁ hD₂,
        isNefModelEquivalent_of_isNull hWv hp₁ hp₂ pp₁ pp₂ bp₁ bp₂ hh hc hD₁ hD₂⟩⟩

end MMP.Fourfold
