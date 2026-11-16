module

public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformIdeal
public import MMP.AlgebraicGeometry.Resolution.DivisorialPart
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
public import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional

/-!
# Resolution of singularities: finiteness, codimension-one and monomial-part lemmas

This file collects lemmas from Kollár's *Lectures on resolution of singularities* used in the
construction of resolutions.

* Integral closures: if `S` is integral over `R`, finiteness of the integral closure of `R` in `B`
  implies finiteness of the integral closure of `S` in `B` (the reduction to a polynomial ring
  in the proof of Kollár 1.33).
* Birational geometry of surfaces: a proper birational morphism to a normal variety is an
  isomorphism outside a closed subset of codimension at least two, and a generically finite
  morphism from a surface contracts only finitely many curves (Kollár 2.10–2.16).
* Monomial parts of ideals (Kollár 3.110–3.111): the monomial decomposition `I = 𝒪(-A(I))·N(I)`
  of a triple exists and is unique, the monomial part commutes with flat pull-back with reduced
  base changes, and the nonmonomial part of a birational transform is the controlled transform of
  the nonmonomial part.
* Blow-up sequences (Kollár p. 146): the sequence induced on a closed subscheme commutes with
  flat pull-back.

## Main results

* `MMP.integralClosure_finite_of_isIntegral`
* `MMP.Resolution.exists_two_le_closedsCodimension_compl_isIso_morphismRestrict`
* `MMP.Resolution.finite_setOf_isContractedBy`
* `MMP.Resolution.isMonomialDecomposition_iff`
* `MMP.Resolution.monomialPart_comap`
* `MMP.Resolution.nonmonomialPart_birationalTransform`
* `MMP.Resolution.Kollar.embeddedResolutionSequence_pullback_of_flat`
* `MMP.Resolution.Kollar.embeddedResolutionSequence_pullback_of_flat_of_comm`
* `MMP.Resolution.Kollar.embeddedResolutionLength_le_pullback`
* `MMP.Resolution.Kollar.reduction_embeddedResolutionSequence_pullback_of_flat_of_comm`

## References

* [J. Kollár, *Lectures on resolution of singularities*, Ann. of Math. Stud. 166][kollar2007]
-/

universe u

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-!
### Finiteness of integral closures along an integral extension

Let `R → S → B` be a tower of commutative rings with `S` integral over `R`. By transitivity of
integrality, the integral closure of `S` in `B` coincides, as a subset of `B`, with the integral
closure of `R` in `B`. Consequently, if the integral closure of `R` in `B` is a finite `R`-module,
then the integral closure of `S` in `B` is a finite `S`-module: any finite set of `R`-module
generators also generates it over `S`.

This is the step reducing the finiteness of integral closures for a finitely generated algebra
over a field to the case of a polynomial ring, via Noether normalisation [kollar2007, proof of
Theorem 1.33].

Implementation notes:

The source states this for integral domains `R ⊆ S` with `R` Noetherian, `S` a finite `R`-module
and `B = F` a field containing `S`. None of these is needed: only integrality of `S` over `R` is
used, and `B` may be any commutative `S`-algebra. A finite `R`-algebra is integral
(`Algebra.IsIntegral.of_finite`), so the source's statement is the special case.
-/

section

namespace MMP.Resolution.Proof_lem_kr1b_finiteness_reduce_to_polynomial_ring

/-- Over an integral extension `S / R`, the integral closure of `S` in `B`, viewed as an
`R`-subalgebra, is the integral closure of `R` in `B`. -/
private lemma restrictScalars_integralClosure_eq {R S B : Type*} [CommRing R] [CommRing S]
    [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [Algebra.IsIntegral R S] :
    (integralClosure S B).restrictScalars R = integralClosure R B :=
  SetLike.ext fun x => ⟨isIntegral_trans x, IsIntegral.tower_top⟩

end MMP.Resolution.Proof_lem_kr1b_finiteness_reduce_to_polynomial_ring

namespace MMP

open MMP.Resolution.Proof_lem_kr1b_finiteness_reduce_to_polynomial_ring in
/-- If `S` is integral over `R` and the integral closure of `R` in `B` is a finite `R`-module,
then the integral closure of `S` in `B` is a finite `S`-module. -/
@[mmp "lem_kr1b_finiteness_reduce_to_polynomial_ring"]
public theorem integralClosure_finite_of_isIntegral
    {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    [Algebra.IsIntegral R S] [Module.Finite R (integralClosure R B)] :
    Module.Finite S (integralClosure S B) := by
  have : Module.Finite R (integralClosure S B) :=
    (restrictScalars_integralClosure_eq (R := R) (S := S) (B := B) ▸ inferInstance :
      Module.Finite R ((integralClosure S B).restrictScalars R))
  exact .of_restrictScalars_finite R S _

end MMP

end

/-!
### A proper birational morphism to a normal variety is an isomorphism in codimension one

Let `g : S ⟶ X` be a proper birational morphism of varieties over a field `k`, with `X` normal.
The inverse `g⁻¹ : X ⤏ S` is a morphism on an open `W ⊆ X` whose complement has codimension at
least two, and over `W` the morphism `g` restricts to an isomorphism `g⁻¹(W) ⟶ W`.
-/

section

open CategoryTheory AlgebraicGeometry MMP MMP.Mori

variable {S X : Scheme.{u}}

namespace MMP.Resolution.Proof_lem_kr2a_birational_isomorphism_in_codimension_one

/-- If `g` agrees with the partial isomorphism `e` on `e.source`, then any representative `f`
of the inverse rational map `e⁻¹` is a section of `g` over its domain. -/
private lemma hom_comp_eq_ι [IsReduced X] [X.IsSeparated] (g : S ⟶ X) (e : S.PartialIso X)
    (key : e.source.ι ≫ g = e.iso.hom ≫ e.target.ι) (f : X.PartialMap S)
    (hf : f.toRationalMap = e.symm.toRationalMap) : f.hom ≫ g = f.domain.ι := by
  have h1 : (f.compHom g).toRationalMap = (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hf, ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ g = e.target.ι ≫ 𝟙 X
    rw [key, Iso.inv_hom_id_assoc, Category.comp_id]
  exact ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)).trans (Category.comp_id _)

/-- If `g` agrees with the partial isomorphism `e` on `e.source` and `S` is integral and
separated, then any representative `f` of `e⁻¹` is a retraction of `g` over `g⁻¹(f.domain)`:
both sides agree on the dense open `g⁻¹(f.domain) ∩ e.source`. -/
private lemma morphismRestrict_comp_hom [IsIntegral S] [IsReduced X] [S.IsSeparated]
    (g : S ⟶ X) (e : S.PartialIso X) (key : e.source.ι ≫ g = e.iso.hom ≫ e.target.ι)
    (f : X.PartialMap S) (hf : f.toRationalMap = e.symm.toRationalMap) :
    g ∣_ f.domain ≫ f.hom = (g ⁻¹ᵁ f.domain).ι := by
  have : Nonempty X := ⟨g (Classical.arbitrary S)⟩
  have hσe : X.homOfLE (inf_le_left : f.domain ⊓ e.target ≤ f.domain) ≫ f.hom =
      X.homOfLE (inf_le_right : f.domain ⊓ e.target ≤ e.target) ≫ e.iso.inv ≫ e.source.ι := by
    have h := (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp hf)
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.PartialIso.symm_iso, Iso.symm_hom, Scheme.PartialIso.symm_target] at h
    exact h
  let V : S.Opens := g ⁻¹ᵁ f.domain ⊓ e.source
  have hpt (y : e.source.toScheme) : g (e.source.ι y) = e.target.ι (e.iso.hom y) := by
    rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply]
  have hVne : (V : Set S).Nonempty := by
    obtain ⟨x, hxW, hxt⟩ := (f.dense_domain.inter_of_isOpen_left e.dense_target
      f.domain.isOpen).nonempty
    obtain ⟨y, rfl⟩ : x ∈ Set.range e.target.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨e.source.ι (e.iso.inv y), TopologicalSpace.Opens.mem_inf.mpr ⟨?_, (e.iso.inv y).2⟩⟩
    change g (e.source.ι (e.iso.inv y)) ∈ f.domain
    rwa [hpt, ← Scheme.Hom.comp_apply e.iso.inv e.iso.hom, Iso.inv_hom_id]
  have : IsDominant (S.homOfLE (inf_le_left : V ≤ g ⁻¹ᵁ f.domain)) :=
    AlgebraicGeometry.Opens.isDominant_homOfLE (V.isOpen.dense hVne) _
  let m : V.toScheme ⟶ (f.domain ⊓ e.target).toScheme :=
    IsOpenImmersion.lift (f.domain ⊓ e.target).ι (V.ι ≫ g) (by
      rintro _ ⟨v, rfl⟩
      have hv := TopologicalSpace.Opens.mem_inf.mp v.2
      rw [Scheme.Opens.range_ι]
      refine TopologicalSpace.Opens.mem_inf.mpr ⟨hv.1, ?_⟩
      have hk : g v.1 = e.target.ι (e.iso.hom ⟨v.1, hv.2⟩) := hpt ⟨v.1, hv.2⟩
      change g v.1 ∈ e.target
      rw [hk]
      exact (e.iso.hom ⟨v.1, hv.2⟩).2)
  have hm : m ≫ (f.domain ⊓ e.target).ι = V.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have step1 : S.homOfLE (inf_le_left : V ≤ g ⁻¹ᵁ f.domain) ≫ g ∣_ f.domain =
      m ≫ X.homOfLE (inf_le_left : f.domain ⊓ e.target ≤ f.domain) := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, hm]
    rw [Scheme.homOfLE_ι_assoc]
  have step2 : m ≫ X.homOfLE (inf_le_right : f.domain ⊓ e.target ≤ e.target) =
      S.homOfLE (inf_le_right : V ≤ e.source) ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι]
    simp only [Category.assoc, Scheme.homOfLE_ι, hm, ← key]
    rw [Scheme.homOfLE_ι_assoc]
  refine ext_of_isDominant_of_isSeparated' (⊤_ Scheme)
    (S.homOfLE (inf_le_left : V ≤ g ⁻¹ᵁ f.domain)) ?_
  rw [reassoc_of% step1, hσe, reassoc_of% step2, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι,
    Scheme.homOfLE_ι]

/-- If `g` agrees with the partial isomorphism `e` on `e.source`, with `S` integral and both
schemes separated, then `g` is an isomorphism over the domain of any representative of `e⁻¹`. -/
private lemma isIso_morphismRestrict_domain [IsIntegral S] [IsReduced X] [S.IsSeparated]
    [X.IsSeparated] (g : S ⟶ X) (e : S.PartialIso X)
    (key : e.source.ι ≫ g = e.iso.hom ≫ e.target.ι) (f : X.PartialMap S)
    (hf : f.toRationalMap = e.symm.toRationalMap) : IsIso (g ∣_ f.domain) := by
  have hσ := hom_comp_eq_ι g e key f hf
  let σ' : f.domain.toScheme ⟶ (g ⁻¹ᵁ f.domain).toScheme :=
    IsOpenImmersion.lift (g ⁻¹ᵁ f.domain).ι f.hom (by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      change g (f.hom w) ∈ f.domain
      rw [← Scheme.Hom.comp_apply, hσ]
      exact w.2)
  have hσ' : σ' ≫ (g ⁻¹ᵁ f.domain).ι = f.hom := IsOpenImmersion.lift_fac _ _ _
  refine ⟨σ', ?_, ?_⟩
  · rw [← cancel_mono (g ⁻¹ᵁ f.domain).ι, Category.assoc, hσ',
      morphismRestrict_comp_hom g e key f hf, Category.id_comp]
  · rw [← cancel_mono f.domain.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hσ', hσ,
      Category.id_comp]

end MMP.Resolution.Proof_lem_kr2a_birational_isomorphism_in_codimension_one

namespace MMP.Resolution

open MMP.Resolution.Proof_lem_kr2a_birational_isomorphism_in_codimension_one in
/-- **A proper birational morphism to a normal variety is an isomorphism in codimension one.**
Let `g : S ⟶ X` be a proper birational morphism of varieties over a field `k` with `X` normal.
Then there is an open `W ⊆ X` whose complement has codimension at least two such that
`g ∣_ W : g⁻¹(W) ⟶ W` is an isomorphism. -/
@[mmp "lem_kr2a_birational_isomorphism_in_codimension_one"]
public theorem exists_two_le_closedsCodimension_compl_isIso_morphismRestrict {k : Type u}
    [Field k] {S X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : Mori.IsNormalVariety k sX)
    (g : S ⟶ X) (hS : Mori.IsVariety k (g ≫ sX)) [IsProper g] (hg : Mori.IsBirationalMorphism g) :
    ∃ W : X.Opens, 2 ≤ closedsCodimension W.compl ∧ IsIso (g ∣_ W) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral S := hS.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (g ≫ sX) := hS.toIsSeparated
  have : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX]; infer_instance⟩
  have : S.IsSeparated := ⟨by rw [← Limits.terminal.comp_from (g ≫ sX)]; infer_instance⟩
  have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX g hS hg
  obtain ⟨e, he, hinv⟩ := hg.isInverse_inverse
  generalize Mori.RationalMap.IsBirational.inverse hg = φ at hcodim hinv
  subst hinv
  refine ⟨e.symm.toRationalMap.domain, hcodim, ?_⟩
  exact isIso_morphismRestrict_domain g e
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm e.symm.toRationalMap.toPartialMap
    (Scheme.RationalMap.toRationalMap_toPartialMap _)

end MMP.Resolution

end

/-!
### A generically finite morphism from a surface contracts finitely many curves

Let `f : X ⟶ Y` be a generically finite morphism, with `X` a variety over a field `k` of
dimension at most two. The points of `X` at which the fibre of `f` is positive dimensional form a
proper closed subset of `X`, of dimension at most one, and every curve contracted by `f` is one
of its finitely many one-dimensional irreducible components. Hence `X` contains only finitely many
`f`-exceptional curves.

Implementation notes:

* `f` is *generically finite* if some open `V ⊆ Y` meeting `f(X)` has `f⁻¹(V) → V` finite.
* The statement is about all proper curves `C ⊆ X` with `f(C)` a point, not only those projective
  over `k`; the `f`-exceptional curves are among them.
* No hypothesis on `Y` and no compatibility of `f` with the structure morphisms is needed.
-/

section

open CategoryTheory AlgebraicGeometry MMP MMP.Mori

namespace MMP.Resolution.Proof_lem_kr2a_finitely_many_exceptional_curves

/-- A strict chain of three specializations in a T₀ space bounds its dimension from below. -/
private lemma three_le_topologicalKrullDim {T : Type*} [TopologicalSpace T] [T0Space T]
    {a b c d : T} (hab : a ⤳ b) (hbc : b ⤳ c) (hcd : c ⤳ d) (hab' : a ≠ b) (hbc' : b ≠ c)
    (hcd' : c ≠ d) : 3 ≤ topologicalKrullDim T := by
  let F : T → TopologicalSpace.IrreducibleCloseds T := fun x =>
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  have key : ∀ {x y : T}, x ⤳ y → x ≠ y → F y < F x := fun hxy hne =>
    lt_of_le_of_ne hxy.closure_subset fun h => hne <| Inseparable.eq <|
      inseparable_iff_closure_eq.mpr (congrArg SetLike.coe h).symm
  have := Order.LTSeries.length_le_krullDim
    (RelSeries.fromListIsChain [F d, F c, F b, F a] (by simp)
      (by simp [key hab hab', key hbc hbc', key hcd hcd']))
  simpa [topologicalKrullDim] using this

/-- In a Jacobson T₀ space, a point whose closure meets some open neighbourhood in a finite set
is closed. -/
private lemma isClosed_singleton_of_finite_closure_inter {T : Type*} [TopologicalSpace T]
    [T0Space T] [JacobsonSpace T] {U : Set T} (hU : IsOpen U) {η : T} (hη : η ∈ U)
    (hfin : (closure {η} ∩ U).Finite) : IsClosed {η} := by
  let W : Set T := (⋃ x ∈ (closure {η} ∩ U) \ {η}, closure {x})ᶜ
  have hW : IsOpen W := isOpen_compl_iff.mpr <|
    (hfin.subset Set.diff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  have heq : ({η} : Set T) = closure {η} ∩ (U ∩ W) := by
    ext x
    constructor
    · rintro rfl
      refine ⟨subset_closure rfl, hη, ?_⟩
      simp only [W, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      exact fun y hy hηy => hy.2 ((specializes_iff_mem_closure.mpr hy.1.1).antisymm
        (specializes_iff_mem_closure.mpr hηy)).symm.eq
    · rintro ⟨hxc, hxU, hxW⟩
      by_contra hne
      exact hxW (Set.mem_iUnion₂.mpr ⟨x, ⟨⟨hxc, hxU⟩, hne⟩, subset_closure rfl⟩)
  exact isClosed_singleton_of_isLocallyClosed_singleton
    (heq ▸ ⟨U ∩ W, closure {η}, hU.inter hW, isClosed_closure, Set.inter_comm _ _⟩)

/-- In a quasi-sober T₀ space of dimension at most two with a generic point `g`, let `Z` be a
union of closed irreducible sets not containing `g`. A point of `Z` with a proper specialization
is the generic point of one of these sets. -/
private lemma closure_singleton_mem {T : Type*} [TopologicalSpace T] [T0Space T] [QuasiSober T]
    (hdim : topologicalKrullDim T ≤ 2) {S : Set (Set T)} (hScl : ∀ t ∈ S, IsClosed t)
    (hSirr : ∀ t ∈ S, IsIrreducible t) {g η x : T} (hg : ∀ y, g ⤳ y) (hgS : g ∉ ⋃₀ S)
    (hη : η ∈ ⋃₀ S) (hx : η ⤳ x) (hxη : x ≠ η) : closure {η} ∈ S := by
  obtain ⟨t, ht, hηt⟩ := hη
  have hξ : closure {(hSirr t ht).genericPoint} = t :=
    (hSirr t ht).isGenericPoint_genericPoint_closure.trans (hScl t ht).closure_eq
  by_cases hne : (hSirr t ht).genericPoint = η
  · rwa [← hne, hξ]
  have hξt : (hSirr t ht).genericPoint ∈ t := hξ.subset (subset_closure rfl)
  have hgξ : g ≠ (hSirr t ht).genericPoint := fun h => hgS ⟨t, ht, h ▸ hξt⟩
  exact absurd ((three_le_topologicalKrullDim (hg _)
    (specializes_iff_mem_closure.mpr (hξ.superset hηt)) hx hgξ hne hxη.symm).trans hdim) (by decide)

/-- The generic point of a proper curve has a specialization other than itself. -/
private lemma exists_mem_closure_ne {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) : ∃ x ∈ closure {C.point}, x ≠ C.point := by
  by_contra! h
  have hrange : Set.range C.ι = closure {C.point} := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : Subsingleton C.scheme := ⟨fun a b => C.ι.isClosedEmbedding.injective <| by
    have ha : C.ι a ∈ closure {C.point} := hrange ▸ ⟨a, rfl⟩
    have hb : C.ι b ∈ closure {C.point} := hrange ▸ ⟨b, rfl⟩
    rw [h _ ha, h _ hb]⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A proper curve contracted by `f` does not meet an open set over which `f` is quasi-compact
and locally quasi-finite. -/
private lemma point_notMem_preimage {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [JacobsonSpace X] {f : X ⟶ Y} {V : Y.Opens}
    [LocallyQuasiFinite (f ∣_ V)] [QuasiCompact (f ∣_ V)]
    (C : ProperCurve sX) (hC : C.IsContractedBy f) : C.point ∉ f ⁻¹ᵁ V := by
  intro hη
  have hfin : (closure {C.point} ∩ (f ⁻¹ᵁ V : Set X)).Finite := by
    have h1 := Scheme.Hom.finite_preimage_singleton (f ∣_ V) ⟨f C.point, hη⟩
    refine (h1.image Subtype.val).subset ?_
    rintro x ⟨hxc, hxU⟩
    exact ⟨⟨x, hxU⟩, Subtype.ext ((morphismRestrict_base_coe f V ⟨x, hxU⟩).trans (hC x hxc)),
      rfl⟩
  obtain ⟨x, hx, hne⟩ := exists_mem_closure_ne C
  rw [(isClosed_singleton_of_finite_closure_inter (f ⁻¹ᵁ V).isOpen hη hfin).closure_eq] at hx
  exact hne hx

end MMP.Resolution.Proof_lem_kr2a_finitely_many_exceptional_curves

namespace MMP.Resolution

open MMP.Resolution.Proof_lem_kr2a_finitely_many_exceptional_curves in
/-- **A generically finite morphism from a surface contracts finitely many curves.** Let `X` be a
variety over a field `k` of dimension at most two and `f : X ⟶ Y` a generically finite morphism
(some open `V ⊆ Y` meeting `f(X)` has `f⁻¹(V) → V` finite). Then only finitely many proper curves
`C ⊆ X` have `f(C)` a point; in particular `X` contains only finitely many `f`-exceptional curves
(`MMP.Resolution.IsContractedProjectiveCurve`). -/
@[mmp "lem_kr2a_finitely_many_exceptional_curves"]
public theorem finite_setOf_isContractedBy {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : Mori.IsVariety k sX) (hdim : topologicalKrullDim X ≤ 2)
    {f : X ⟶ Y}
    (hgf : ∃ V : Y.Opens, ((V : Set Y) ∩ Set.range f.base).Nonempty ∧ IsFinite (f ∣_ V)) :
    {C : ProperCurve sX | C.IsContractedBy f}.Finite := by
  obtain ⟨V, ⟨y₀, hy₀V, x₀, rfl⟩, hfin⟩ := hgf
  have : IsIntegral X := hX.toIsIntegral
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  obtain ⟨S, hSf, hScl, hSirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (f ⁻¹ᵁ V).isOpen.isClosed_compl
  have hgen : genericPoint X ∉ ⋃₀ S := hZ ▸ fun h =>
    h <| (genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ V).isOpen |>.mpr ⟨x₀, trivial, hy₀V⟩
  have hmem (C : ProperCurve sX) (hC : C.IsContractedBy f) : closure {C.point} ∈ S := by
    obtain ⟨x, hx, hxne⟩ := exists_mem_closure_ne C
    exact closure_singleton_mem hdim hScl hSirr
      (fun _ => (genericPoint_spec X).specializes (Set.mem_univ _)) hgen
      (hZ ▸ point_notMem_preimage C hC) (specializes_iff_mem_closure.mpr hx) hxne
  refine Set.Finite.of_finite_image (hSf.subset ?_) fun C _ D _ hCD =>
    ProperCurve.ext (Inseparable.eq (inseparable_iff_closure_eq.mpr hCD))
  rintro _ ⟨C, hC, rfl⟩
  exact hmem C hC

end MMP.Resolution

end

/-!
### The monomial part commutes with smooth pull-back and field extension

Let `(X, I, E)` be a triple over `k` and `h : Y → X` a smooth morphism from a smooth variety, or
the projection `X_L → X` for a field extension `L ⊇ k`. With respect to
`h⁻¹E = (h⁻¹E^1, …, h⁻¹E^s)` the monomial part of `h^*I` is the pull-back of the monomial part
of `I`: `A(h^*I) = h^*A(I)`, equivalently `M(h^*I) = h^*M(I)`.

Both kinds of `h` are flat with reduced base changes (`IsReducedFlatBaseChange.of_smooth`,
`IsReducedFlatBaseChange.fieldChange`), and `Y` is smooth and of finite type over a field. This
is what the argument uses: the generic point of each irreducible component of `h⁻¹E^{ik}` lies
over that of `E^{ik}`, `h⁻¹E^{ik}` is reduced, so the orders of `I` and `h^*I` agree there, and
`h^*𝒪_X(-E^{ik})` is the product of the ideals of the components of `h⁻¹E^{ik}`.

Implementation notes:

The divisor `A(I)` is recorded through its ideal `M(I) = 𝒪_X(-A(I))` (`monomialPart`), and the
pull-back of divisors through the inverse image of ideal sheaves; the identity is stated as
`M(h^*I) = h^*M(I)`. The two cases of the source are subsumed by a single hypothesis: `h` flat
with reduced base changes and `Y` smooth, of finite type and quasi-compact over a field `k'`.
-/

section

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Resolution MMP.Resolution.Aux

namespace MMP.Resolution.Proof_lem_kr3e_monomial_part_smooth_pullback

/-- Orders are preserved along a flat morphism whose stalk map carries the maximal ideal onto
the maximal ideal. -/
private lemma multAt_comap_eq_of_map_maximalIdeal {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] (y : Y)
    (hm : (maximalIdeal (X.presheaf.stalk (h y))).map (h.stalkMap y).hom =
      maximalIdeal (Y.presheaf.stalk y)) (I : X.IdealSheafData) :
    multAt (I.comap h) y = multAt I (h y) := by
  rw [multAt, multAt, IdealSheafData.stalk_comap]
  let : Algebra (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) := (h.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) := Flat.stalkMap h y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap y).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (h y)) (Y.presheaf.stalk y) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hpow : ∀ j : ℕ, (maximalIdeal (Y.presheaf.stalk y) ^ j).comap (h.stalkMap y).hom =
      maximalIdeal (X.presheaf.stalk (h y)) ^ j := by
    intro j
    rw [← hm, ← Ideal.map_pow]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat _
  simp only [idealOrder, Ideal.map_le_iff_le_comap, hpow]

/-- The stalk of the vanishing ideal of a closed set `T` at a point of `T` with no proper
generalization in `T` is the maximal ideal. -/
private lemma stalk_vanishingIdeal_eq_maximalIdeal {Y : Scheme.{u}} (T : TopologicalSpace.Closeds Y)
    {y : Y} (hy : y ∈ T) (hmax : ∀ y', y' ⤳ y → y' ∈ T → y' = y) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y =
      maximalIdeal (Y.presheaf.stalk y) := by
  set S := Scheme.IdealSheafData.vanishingIdeal T with hS
  have hsupp : (S.support : Set Y) = T := by
    rw [hS, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨z, rfl⟩ : y ∈ Set.range S.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]; exact hy
  have hz : IsMax z := by
    intro b hb
    have hb' : b ⤳ z := hb
    have : S.subschemeι b = S.subschemeι z :=
      hmax _ (hb'.map S.subschemeι.continuous) (by
        have hb2 : S.subschemeι b ∈ (S.support : Set Y) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨b, rfl⟩
        rw [hsupp] at hb2; exact hb2)
    have := S.subschemeι.isClosedEmbedding.injective this
    rw [this]
  have hdim : ringKrullDim (S.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.2 hz]; rfl
  have : Ring.KrullDimLE 0 (S.subscheme.presheaf.stalk z) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  have hbot : maximalIdeal (S.subscheme.presheaf.stalk z) = ⊥ := by
    rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal, nilradical_eq_zero]; rfl
  rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk, RingHom.ker_eq_comap_bot, ← hbot]
  exact IsLocalRing.maximalIdeal_comap _

/-- The reduced inverse image: for a prime divisor `D`, `h⁻¹D` is the reduced closed subscheme on
the preimage of `D`. -/
private lemma comap_idealSheaf_eq_vanishingIdeal {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (D : AlgebraicGeometry.PrimeDivisor X) :
    D.idealSheaf.comap h =
      Scheme.IdealSheafData.vanishingIdeal (D.idealSheaf.support.preimage h.continuous) := by
  haveI := D.integral
  have hD := Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D.idealSheaf
    D.idealSheaf.support rfl
  have := hh.comap_vanishingIdeal D.idealSheaf.support
    (D.idealSheaf.support.preimage h.continuous) rfl
  rw [← hD] at this
  exact this

/-- **The generic point of a component of `h⁻¹Z`.** Let `η` be the generic point of an
irreducible component of the preimage of a closed subset `Z` of pure codimension one. Then
`h(η)` is the generic point of a prime divisor which is a component of `Z`, the stalk map at `η`
carries the maximal ideal onto the maximal ideal, and `η` has coheight one. -/
private lemma exists_primeDivisor_of_mem_componentsOf_preimage {k k' : Type u} [Field k]
    [Field k'] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (hX : MMP.Mori.IsSmoothScheme sX) (sY : Y ⟶ Spec (.of k'))
    [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY) {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsPureCodimOne Z.support) {η : Y}
    (hW : closure {η} ∈ componentsOf (h ⁻¹' (Z.support : Set X))) :
    ∃ D : AlgebraicGeometry.PrimeDivisor X, D.support ∈ componentsOf (Z.support : Set X) ∧
      h η = D.genericPoint ∧
      (maximalIdeal (X.presheaf.stalk (h η))).map (h.stalkMap η).hom =
        maximalIdeal (Y.presheaf.stalk η) ∧ Order.coheight η = 1 := by
  haveI := hh.flat
  haveI := noetherianSpace_of_finiteType sX
  have hηT : η ∈ h ⁻¹' (Z.support : Set X) := hW.1.2 (subset_closure rfl)
  have hTcl : IsClosed (h ⁻¹' (Z.support : Set X)) := Z.support.isClosed.preimage h.continuous
  -- `η` has no proper generalization in `h⁻¹Z`
  have hmaxT : ∀ y', y' ⤳ η → h y' ∈ (Z.support : Set X) → y' = η := by
    intro y' hy' hy'Z
    have hcl : closure {y'} ⊆ h ⁻¹' (Z.support : Set X) :=
      closure_minimal (Set.singleton_subset_iff.2 hy'Z) hTcl
    have hsub := hW.2 ⟨isIrreducible_singleton.closure, hcl⟩
      (closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy'))
        isClosed_closure)
    have : η ⤳ y' := specializes_iff_mem_closure.2 (hsub (subset_closure rfl))
    exact (hy'.antisymm this).eq
  obtain ⟨V, hV, hxV⟩ : ∃ V ∈ componentsOf (Z.support : Set X), h η ∈ V := by
    simpa [Set.mem_sUnion] using (finite_and_cover_componentsOf Z.support.isClosed).2 hηT
  obtain ⟨ξ, hξZ, rfl⟩ := exists_eq_closure_of_mem_componentsOf Z.support.isClosed hV
  have hcod : Order.coheight ξ = 1 := by
    rw [coheight_eq_codimension_closureSingleton]
    refine hZ _ ⟨hV.1.2, fun W' hW' hle => ?_⟩
    exact hV.2 ⟨W'.isIrreducible, hW'⟩ hle
  set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcod with hDdef
  have hDgen : D.genericPoint = ξ := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hDsupp : (D.support : Set X) = closure {ξ} := by
    rw [support_eq_closure_genericPoint, hDgen]
  -- `h η = ξ`
  obtain ⟨y'', hy''η, hy''ξ⟩ := Flat.generalizingMap h (specializes_iff_mem_closure.2 hxV)
  have hy'' : y'' = η := hmaxT y'' hy''η (by rw [hy''ξ]; exact hξZ)
  have hhη : h η = ξ := hy'' ▸ hy''ξ
  -- the maximal ideals
  have hmξ : IdealSheafData.stalk D.idealSheaf (h η) = maximalIdeal (X.presheaf.stalk (h η)) := by
    have := stalk_idealSheaf_genericPoint D
    rw [hDgen] at this
    rw [hhη]; exact this
  have hm : (maximalIdeal (X.presheaf.stalk (h η))).map (h.stalkMap η).hom =
      maximalIdeal (Y.presheaf.stalk η) := by
    rw [← hmξ, ← IdealSheafData.stalk_comap, comap_idealSheaf_eq_vanishingIdeal hh D]
    refine stalk_vanishingIdeal_eq_maximalIdeal _ ?_ fun y' hy' hy'T => hmaxT y' hy' ?_
    · show h η ∈ (D.support : Set X)
      rw [hDsupp, hhη]; exact subset_closure rfl
    · have hsub : (D.support : Set X) ⊆ Z.support := by rw [hDsupp]; exact hV.1.2
      exact hsub hy'T
  refine ⟨D, by rw [hDsupp]; exact hV, by rw [hDgen, hhη], hm, ?_⟩
  -- `η` has coheight one: `𝒪_{Y,η}` is a discrete valuation ring
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX hX D (x := h η)
    (by show h η ∈ (D.support : Set X); rw [hDsupp, hhη]; exact subset_closure rfl)
  haveI := smooth_of_isSmoothScheme' sY hY
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sY η
  haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk η)
  let : Algebra (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := (h.stalkMap η).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := Flat.stalkMap h η
  have : IsLocalHom (algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap η).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hspan : maximalIdeal (Y.presheaf.stalk η) =
      Ideal.span {(h.stalkMap η).hom π} := by
    rw [← hm, ← hmξ, hπD, Ideal.map_span, Set.image_singleton]
  have hne : maximalIdeal (Y.presheaf.stalk η) ≠ ⊥ := by
    intro hbot
    have h1 := Ideal.comap_map_eq_self_of_faithfullyFlat
      (B := Y.presheaf.stalk η) (maximalIdeal (X.presheaf.stalk (h η)))
    have h2 := Ideal.comap_map_eq_self_of_faithfullyFlat
      (B := Y.presheaf.stalk η) (⊥ : Ideal (X.presheaf.stalk (h η)))
    have hmap : (maximalIdeal (X.presheaf.stalk (h η))).map
        (algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η)) = ⊥ := hm.trans hbot
    rw [hmap, ← Ideal.map_bot (f := algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η)),
      h2] at h1
    have hπm : π ∈ maximalIdeal (X.presheaf.stalk (h η)) := by
      rw [← hmξ, hπD]; exact Ideal.mem_span_singleton_self _
    rw [← h1] at hπm
    exact hπ.ne_zero ((Submodule.mem_bot _).1 hπm)
  have hnf : ¬ IsField (Y.presheaf.stalk η) := by
    intro hf
    exact hne ((IsLocalRing.isField_iff_maximalIdeal_eq).1 hf)
  have hdvr : IsDiscreteValuationRing (Y.presheaf.stalk η) :=
    ((IsDiscreteValuationRing.TFAE (Y.presheaf.stalk η) hnf).out 1 5).2
      (⟨⟨_, hspan⟩⟩ : Submodule.IsPrincipal (maximalIdeal (Y.presheaf.stalk η)))
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (Y.presheaf.stalk η)
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

/-- A monomial part is the finite product over any finite set containing all components. -/
private lemma monomialPart_eq_prod {Z : Scheme.{u}} (I : Z.IdealSheafData) (E : OrderedDivisor Z)
    (G : Finset (AlgebraicGeometry.PrimeDivisor Z)) (hG : ∀ D, E.IsComponent D → D ∈ G) :
    monomialPart I E = ∏ D ∈ G, D.idealSheaf ^ monomialPartCoeff I E D := by
  classical
  refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => hG D ?_
  by_contra hc
  exact hD (by simp [monomialPartCoeff, hc])

private lemma coe_support_comap_E {X Y : Scheme.{u}} (h : Y ⟶ X) (E : OrderedDivisor X) (i) :
    (((E.comap h).E i).support : Set Y) = h ⁻¹' ((E.E i).support : Set X) := by
  show (((E.E i).comap h).support : Set Y) = _
  rw [Scheme.IdealSheafData.support_comap]; rfl

/-- **Components of `h⁻¹E` lie over components of `E` with the same coefficient.** -/
private lemma exists_isComponent_of_isComponent_comap {k k' : Type u} [Field k] [Field k']
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : MMP.Mori.IsSmoothScheme sX) (sY : Y ⟶ Spec (.of k')) [LocallyOfFiniteType sY]
    (hY : MMP.Mori.IsSmoothScheme sY) {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h)
    (I : X.IdealSheafData) {E : OrderedDivisor X}
    (hE : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support) {D' : AlgebraicGeometry.PrimeDivisor Y}
    (hD' : (E.comap h).IsComponent D') :
    ∃ D, E.IsComponent D ∧ h D'.genericPoint = D.genericPoint ∧
      (maximalIdeal (X.presheaf.stalk (h D'.genericPoint))).map
          (h.stalkMap D'.genericPoint).hom = maximalIdeal (Y.presheaf.stalk D'.genericPoint) ∧
      monomialPartCoeff (I.comap h) (E.comap h) D' = monomialPartCoeff I E D := by
  classical
  haveI := hh.flat
  obtain ⟨i, hi⟩ := id hD'
  rw [coe_support_comap_E, support_eq_closure_genericPoint] at hi
  obtain ⟨D, hDc, hgen, hm, -⟩ :=
    exists_primeDivisor_of_mem_componentsOf_preimage sX hX sY hY hh (E.E i) (hE i) hi
  have hcD : E.IsComponent D := ⟨i, hDc⟩
  refine ⟨D, hcD, hgen, hm, ?_⟩
  simp only [monomialPartCoeff, if_pos hD', if_pos hcD]
  rw [multAt_comap_eq_of_map_maximalIdeal h _ hm, hgen]

end MMP.Resolution.Proof_lem_kr3e_monomial_part_smooth_pullback

namespace MMP.Resolution

open MMP.Resolution.Proof_lem_kr3e_monomial_part_smooth_pullback in
/-- **The monomial part commutes with smooth pull-back** (Kollár Def.–Lemma 3.110). Let
`(X, I, E)` be a triple over `k` and `h : Y → X` flat with reduced base changes, with `Y` smooth,
of finite type and quasi-compact over a field `k'` — e.g. a smooth morphism from a smooth variety
(`IsReducedFlatBaseChange.of_smooth`) or the projection `X_L → X` of a field extension
(`IsReducedFlatBaseChange.fieldChange`). Then the monomial part of `h^*I` with respect to
`h⁻¹E` is the pull-back of the monomial part of `I` with respect to `E`. -/
@[mmp "lem_kr3e_monomial_part_smooth_pullback"]
public theorem monomialPart_comap {k k' : Type u} [Field k] [Field k'] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X}
    (hI : IsTriple sX I E) (sY : Y ⟶ Spec (.of k')) (hY : MMP.Mori.IsSmoothScheme sY)
    [LocallyOfFiniteType sY] [QuasiCompact sY] (h : Y ⟶ X) (hh : IsReducedFlatBaseChange h) :
    monomialPart (I.comap h) (E.comap h) = (monomialPart I E).comap h := by
  classical
  obtain ⟨-, hsmX, hlft, hqc, -, -, hsnc⟩ := hI
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  haveI := hh.flat
  haveI := noetherianSpace_of_finiteType sY
  set A := monomialPartCoeff I E
  set B := monomialPartCoeff (I.comap h) (E.comap h)
  set F := (finite_primeDivisor_of_isComponent sX E.E).toFinset
  set F' := (finite_primeDivisor_of_isComponent sY (E.comap h).E).toFinset
  have hmemF : ∀ D, D ∈ F ↔ E.IsComponent D := fun D => Set.Finite.mem_toFinset _
  have hmemF' : ∀ D', D' ∈ F' ↔ (E.comap h).IsComponent D' := fun D' => Set.Finite.mem_toFinset _
  have hMX : monomialPart I E = ∏ D ∈ F, D.idealSheaf ^ A D :=
    monomialPart_eq_prod I E F fun D => (hmemF D).2
  have hMY : monomialPart (I.comap h) (E.comap h) = ∏ D' ∈ F', D'.idealSheaf ^ B D' :=
    monomialPart_eq_prod (I.comap h) (E.comap h) F' fun D => (hmemF' D).2
  have hkey : ∀ D' ∈ F', ∃ D ∈ F, h D'.genericPoint = D.genericPoint ∧
      (maximalIdeal (X.presheaf.stalk (h D'.genericPoint))).map
          (h.stalkMap D'.genericPoint).hom = maximalIdeal (Y.presheaf.stalk D'.genericPoint) ∧
      B D' = A D := fun D' hD' => by
    obtain ⟨D, hD, rest⟩ := exists_isComponent_of_isComponent_comap sX hsmX sY hY hh I
      (fun i => (hsnc.2.1 i).2.1) ((hmemF' D').1 hD')
    exact ⟨D, (hmemF D).2 hD, rest⟩
  apply le_antisymm
  · -- `M(h^*I) ≤ h^*M(I)`: group the prime divisors of `Y` by their image
    rw [hMY, hMX, Stacks.IdealSheaf.comap_finset_prod]
    simp only [Stacks.IdealSheaf.comap_pow]
    set fib : AlgebraicGeometry.PrimeDivisor X → Finset (AlgebraicGeometry.PrimeDivisor Y) :=
      fun D => F'.filter fun D' => h D'.genericPoint = D.genericPoint with hfib
    have hU : F' = F.biUnion fib := by
      ext D'
      simp only [Finset.mem_biUnion, hfib, Finset.mem_filter]
      constructor
      · intro hD'
        obtain ⟨D, hDF, hgen, -, -⟩ := hkey D' hD'
        exact ⟨D, hDF, hD', hgen⟩
      · exact fun ⟨_, _, hD', _⟩ => hD'
    have hdisj : (F : Set (AlgebraicGeometry.PrimeDivisor X)).PairwiseDisjoint fib := by
      intro D₁ _ D₂ _ hne
      refine Finset.disjoint_left.2 fun D' h₁ h₂ => hne ?_
      simp only [hfib, Finset.mem_filter] at h₁ h₂
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h₁.2.symm.trans h₂.2)
    rw [hU, Finset.prod_biUnion hdisj]
    refine Finset.prod_le_prod₀ (fun _ _ => bot_le) fun D hDF => ?_
    have hfibB : ∀ D' ∈ fib D, B D' = A D := by
      intro D' hD'
      simp only [hfib, Finset.mem_filter] at hD'
      obtain ⟨D₀, -, hgen, -, hBA⟩ := hkey D' hD'.1
      rw [hBA, AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hgen.symm.trans hD'.2)]
    rw [Finset.prod_congr rfl fun D' hD' => by rw [hfibB D' hD'], Finset.prod_pow]
    refine pow_le_pow_left₀ bot_le ?_ _
    -- the components over `D` cover `h⁻¹D`
    rw [comap_idealSheaf_eq_vanishingIdeal hh D]
    refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 fun y hy => ?_
    have hy' : h y ∈ (D.support : Set X) := hy
    obtain ⟨j, hj⟩ := (hmemF D).1 hDF
    have hyT : y ∈ h ⁻¹' ((E.E j).support : Set X) := hj.1.2 hy'
    obtain ⟨W, hW, hyW⟩ : ∃ W ∈ componentsOf (h ⁻¹' ((E.E j).support : Set X)), y ∈ W := by
      simpa [Set.mem_sUnion] using
        (finite_and_cover_componentsOf ((E.E j).support.isClosed.preimage h.continuous)).2 hyT
    obtain ⟨η, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf
      ((E.E j).support.isClosed.preimage h.continuous) hW
    obtain ⟨D₂, hD₂c, hgen, -, hcoh⟩ := exists_primeDivisor_of_mem_componentsOf_preimage sX hsmX
      sY hY hh (E.E j) (hsnc.2.1 j).2.1 hW
    set D' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh with hD'def
    have hD'gen : D'.genericPoint = η :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hD'supp : (D'.support : Set Y) = closure {η} := by
      rw [support_eq_closure_genericPoint, hD'gen]
    have hD'F : D' ∈ F' := (hmemF' D').2 ⟨j, by rw [coe_support_comap_E h E j, hD'supp]; exact hW⟩
    have hyD₂ : h y ∈ (D₂.support : Set X) := by
      rw [support_eq_closure_genericPoint, ← hgen, ← specializes_iff_mem_closure]
      exact (specializes_iff_mem_closure.2 hyW).map h.continuous
    have hD₂D : D₂ = D := Aux.PrimeDivisor.eq_of_support_eq
      (eq_of_mem_componentsOf_of_isSmoothScheme sX (E.E j) (hsnc.2.1 j).2.2 hD₂c hj hyD₂ hy')
    have hD'fib : D' ∈ fib D := by
      simp only [hfib, Finset.mem_filter]
      exact ⟨hD'F, by rw [hD'gen, hgen, hD₂D]⟩
    rw [← Finset.mul_prod_erase _ _ hD'fib]
    show y ∈ ((D'.idealSheaf * _).support : Set Y)
    rw [Scheme.IdealSheafData.support_mul]
    left
    show y ∈ (D'.support : Set Y)
    rw [hD'supp]
    exact hyW
  · -- `h^*M(I) ≤ M(h^*I)`: compare at the generic points
    rw [hMY]
    refine le_prod_of_stalk_le sY hY B F' _ fun D' hD' => ?_
    obtain ⟨D, hDF, hgen, hm, hBA⟩ := hkey D' hD'
    rw [IdealSheafData.stalk_comap, hBA, ← hm, ← Ideal.map_pow]
    refine Ideal.map_mono ?_
    have hle : monomialPart I E ≤ D.idealSheaf ^ A D := by
      rw [hMX, ← Finset.mul_prod_erase _ _ hDF]
      exact fun _ => Ideal.mul_le_left
    refine (Flips.ResolutionInputs.stalk_mono hle _).trans ?_
    rw [stalk_pow, hgen, stalk_idealSheaf_genericPoint]

end MMP.Resolution

end

/-!
### Existence and uniqueness of the monomial decomposition

For a triple `(X, I, E)`, the pair `(A(I), N(I))` formed by the monomial part coefficients
`MMP.Resolution.monomialPartCoeff` and the nonmonomial part `MMP.Resolution.nonmonomialPart` is a
monomial decomposition of `I` with respect to `E`, and it is the only one.
-/

section

open CategoryTheory AlgebraicGeometry MMP.Resolution MMP.Resolution.Aux

variable {X : Scheme.{u}}

namespace MMP.Resolution.Proof_lem_kr3e_monomial_decomposition_exists_unique

/-- In a discrete valuation ring the order of `𝔪ⁿ` is `n`. -/
private theorem idealOrder_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    idealOrder (IsLocalRing.maximalIdeal R ^ n) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have key : ∀ j : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ IsLocalRing.maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IsLocalRing.maximalIdeal R ^ n ≤
    IsLocalRing.maximalIdeal R ^ j) => (j : ℕ∞)) n le_rfl le_rfl

/-- In a discrete valuation ring, a nonzero ideal `J` with `ord(𝔪ᵃ · J) = a` is the unit ideal. -/
private theorem eq_top_of_toNat_idealOrder_maximalIdeal_pow_mul {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {a : ℕ} {J : Ideal R} (hJ : J ≠ ⊥)
    (h : (idealOrder (IsLocalRing.maximalIdeal R ^ a * J)).toNat = a) : J = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJ hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq, ← pow_add, idealOrder_maximalIdeal_pow,
    ENat.toNat_coe] at h
  rw [show b = 0 by omega, pow_zero, Ideal.span_singleton_one]

private theorem genericPoint_mem_support (D : AlgebraicGeometry.PrimeDivisor X) :
    D.genericPoint ∈ D.support := by
  have : D.genericPoint ∈ closure ({D.genericPoint} : Set X) := subset_closure rfl
  rwa [← support_eq_closure_genericPoint] at this

/-- On a smooth scheme over a field, the local ring at the generic point of a prime divisor is a
discrete valuation ring. -/
private theorem isDiscreteValuationRing_stalk_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    ∃ _ : IsDomain (X.presheaf.stalk D.genericPoint),
      IsDiscreteValuationRing (X.presheaf.stalk D.genericPoint) := by
  haveI := smooth_of_isSmoothScheme' sX h
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX D.genericPoint
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk D.genericPoint)
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX h D (genericPoint_mem_support D)
  rw [stalk_idealSheaf_genericPoint] at hπD
  refine ⟨inferInstance, ?_⟩
  have hnf : ¬ IsField (X.presheaf.stalk D.genericPoint) := by
    intro hf
    have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [h0, eq_comm, Ideal.span_singleton_eq_bot] at hπD
    exact hπ.ne_zero hπD
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 5 1).mp
    (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint)) from
      ⟨⟨π, hπD⟩⟩)

/-- The generic point of a prime divisor `D` lies on no other prime divisor. -/
private theorem genericPoint_notMem_support {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    {D D' : AlgebraicGeometry.PrimeDivisor X} (hne : D ≠ D') :
    D.genericPoint ∉ D'.support := by
  intro hx
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX h D
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX h D' hx
  have hp : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hb : Ideal.span {π} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
  have hm := IsLocalRing.eq_maximalIdeal (hp.isMaximal hb)
  refine hne (eq_of_stalk_idealSheaf_eq sX h D D' (genericPoint_mem_support D) hx ?_)
  rw [stalk_idealSheaf_genericPoint, hπD, hm]

/-- The stalk of `∏_{D'} I_{D'}^{A D'}` at the generic point of `D` is `𝔪^{A D}`. -/
private theorem stalk_prod_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (F : Finset (AlgebraicGeometry.PrimeDivisor X))
    (hF : ∀ D', A D' ≠ 0 → D' ∈ F) (D : AlgebraicGeometry.PrimeDivisor X) :
    IdealSheafData.stalk (∏ D' ∈ F, D'.idealSheaf ^ A D') D.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ A D := by
  rw [Aux.stalk_prod]
  simp only [Aux.stalk_pow]
  have htop : ∀ D' ∈ F, D' ≠ D →
      IdealSheafData.stalk D'.idealSheaf D.genericPoint ^ A D' = 1 := by
    intro D' _ hne
    rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (genericPoint_notMem_support sX h (Ne.symm hne)), ← Ideal.one_eq_top, one_pow]
  by_cases hD : D ∈ F
  · rw [Finset.prod_eq_single D htop (fun h' => absurd hD h'), stalk_idealSheaf_genericPoint]
  · have h0 : A D = 0 := by
      by_contra h0; exact hD (hF D h0)
    rw [h0, pow_zero]
    exact Finset.prod_eq_one fun D' hD' => htop D' hD' (fun e => hD (e ▸ hD'))

private theorem divisorIdeal_eq_prod (A : AlgebraicGeometry.PrimeDivisor X → ℕ)
    (hfin : (Function.support A).Finite) :
    divisorIdeal A = ∏ D ∈ hfin.toFinset, D.idealSheaf ^ A D := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  intro h0
  exact hD (by show D.idealSheaf ^ A D = 1; rw [h0, pow_zero])

private theorem stalk_divisorIdeal_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    IdealSheafData.stalk (divisorIdeal A) D.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ A D := by
  rw [divisorIdeal_eq_prod A hfin]
  exact stalk_prod_genericPoint sX h A _ (fun D' hD' => by simpa using hD') D

private theorem isEffectiveCartierDivisor_divisorIdeal {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisorIdeal A) := by
  rw [divisorIdeal_eq_prod A hfin]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => isEffectiveCartierDivisor_idealSheaf sX h D

/-- An effective Cartier divisor can be cancelled from a product of ideal sheaves. -/
private theorem le_of_mul_eq_mul {M N N' : X.IdealSheafData}
    (hM : Stacks.Divisors.IsEffectiveCartierDivisor M) (he : M * N = M * N') : N ≤ N' := by
  refine IdealSheafData.le_of_stalk_le _ _ fun x f hf => ?_
  obtain ⟨U, hU, hxU, g, hg, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor M hM x
  set g' := (X.presheaf.germ U x hxU).hom g
  have hg' : g' ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    Stacks.Divisors.germ_mem_nonZeroDivisors hU hg x hxU
  have hst : IdealSheafData.stalk M x = Ideal.span {g'} := by
    rw [IdealSheafData.stalk_eq_map_germ M x ⟨U, hU⟩ hxU, hspan, Ideal.map_span,
      Set.image_singleton]
  have hmem : g' * f ∈ IdealSheafData.stalk (M * N') x := by
    rw [← he, Aux.stalk_mul, hst]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g') hf
  rw [Aux.stalk_mul, hst, Ideal.mem_span_singleton_mul] at hmem
  obtain ⟨z, hz, hgz⟩ := hmem
  rwa [(mul_cancel_left_mem_nonZeroDivisors hg').1 hgz] at hz

/-- The generic point of `D` lies in a closed set `Z` iff `D ⊆ Z`. -/
private theorem genericPoint_mem_support_iff (D : AlgebraicGeometry.PrimeDivisor X)
    (N : X.IdealSheafData) :
    D.genericPoint ∈ (N.support : Set X) ↔ D.support ⊆ (N.support : Set X) := by
  refine ⟨fun hη => ?_, fun hs => hs (genericPoint_mem_support D)⟩
  rw [support_eq_closure_genericPoint]
  exact (N.support.isClosed.closure_subset_iff).2 (Set.singleton_subset_iff.2 hη)

/-- An ideal sheaf nonzero at the generic points of `X` has nonzero stalks everywhere. -/
private theorem stalk_ne_bot {I : X.IdealSheafData} (hI : IsNonzeroAtGenericPoints I) (x : X) :
    IdealSheafData.stalk I x ≠ ⊥ := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen := hZ.1.isGenericPoint_genericPoint_closure
  rw [hZc.closure_eq] at hgen
  have hsp : hZ.1.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hgen.def]; exact hxZ rfl
  intro hb
  refine hI hZ.1.genericPoint (by rw [hgen.def]; exact hZ) ?_
  rw [stalk_eq_map_stalkSpecializes I hsp, hb, Ideal.map_bot]

/-- Uniqueness of the coefficients: for a monomial decomposition `(A, N)`, `A = A(I)`. -/
private theorem eq_monomialPartCoeff {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    {I : X.IdealSheafData} {E : OrderedDivisor X} {A : AlgebraicGeometry.PrimeDivisor X → ℕ}
    {N : X.IdealSheafData} (hd : IsMonomialDecomposition I E A N) :
    A = monomialPartCoeff I E := by
  classical
  funext D
  by_cases hc : E.IsComponent D
  · obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX h D
    have hN : IdealSheafData.stalk N D.genericPoint = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
        (fun hη => hd.not_subset_cosupport D hc ((genericPoint_mem_support_iff D N).1 hη))
    have hI : IdealSheafData.stalk I D.genericPoint =
        IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ A D := by
      rw [hd.eq_mul, Aux.stalk_mul, hN, stalk_divisorIdeal_genericPoint sX h A hd.finite_support,
        Ideal.mul_top]
    simp only [monomialPartCoeff, hc, if_true, multAt, hI, idealOrder_maximalIdeal_pow,
      ENat.toNat_coe]
  · have h0 : A D = 0 := by
      by_contra h0; exact hc (hd.isComponent_of_ne_zero D h0)
    simp [monomialPartCoeff, hc, h0]

/-- Existence: `(A(I), N(I))` is a monomial decomposition of `I`. -/
private theorem isMonomialDecomposition_monomialPart {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X}
    (hT : IsTriple sX I E) :
    IsMonomialDecomposition I E (monomialPartCoeff I E) (nonmonomialPart I E) := by
  classical
  have hmul := monomialPart_mul_nonmonomialPart sX I E hT
  obtain ⟨-, hsm, hlft, hqc, -, hnz, -⟩ := hT
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have hcomp : ∀ D, monomialPartCoeff I E D ≠ 0 → E.IsComponent D := by
    intro D hD
    by_contra hc
    exact hD (by simp [monomialPartCoeff, hc])
  have hfin : (Function.support (monomialPartCoeff I E)).Finite :=
    (finite_primeDivisor_of_isComponent sX E.E).subset fun D hD => hcomp D hD
  refine ⟨hfin, hcomp, hmul.symm, fun D hc hsub => ?_⟩
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX hsm D
  have hI : IdealSheafData.stalk I D.genericPoint =
      IsLocalRing.maximalIdeal _ ^ monomialPartCoeff I E D *
        IdealSheafData.stalk (nonmonomialPart I E) D.genericPoint := by
    conv_lhs => rw [← hmul]
    rw [Aux.stalk_mul, monomialPart, stalk_divisorIdeal_genericPoint sX hsm _ hfin]
  have hord : (multAt I D.genericPoint).toNat = monomialPartCoeff I E D := by
    simp only [monomialPartCoeff, hc, if_true]
  rw [multAt, hI] at hord
  have hb := stalk_ne_bot hnz D.genericPoint
  rw [hI] at hb
  exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1
    (eq_top_of_toNat_idealOrder_maximalIdeal_pow_mul (right_ne_zero_of_mul hb) hord)
    ((genericPoint_mem_support_iff D _).2 hsub)

end MMP.Resolution.Proof_lem_kr3e_monomial_decomposition_exists_unique

namespace MMP.Resolution

open MMP.Resolution.Proof_lem_kr3e_monomial_decomposition_exists_unique in
/-- For a triple `(X, I, E)`, a pair `(A, N)` is a monomial decomposition of `I` with respect to
`E` if and only if `A` is the monomial part `A(I) = ∑ ord_{E^{ik}}(I)·E^{ik}` and `N` is the
nonmonomial part `N(I)`; in particular `(A(I), N(I))` is the unique monomial decomposition. -/
@[mmp "lem_kr3e_monomial_decomposition_exists_unique"]
public theorem isMonomialDecomposition_iff {X : Scheme.{u}} {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsTriple sX I E) (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (N : X.IdealSheafData) :
    IsMonomialDecomposition I E A N ↔
      A = monomialPartCoeff I E ∧ N = nonmonomialPart I E := by
  have hex := isMonomialDecomposition_monomialPart sX h
  obtain ⟨-, hsm, hlft, -, -, -, -⟩ := h
  haveI : LocallyOfFiniteType sX := hlft
  constructor
  · intro hd
    obtain rfl := eq_monomialPartCoeff sX hsm hd
    refine ⟨rfl, ?_⟩
    have hM := isEffectiveCartierDivisor_divisorIdeal sX hsm _ hd.finite_support
    have he : divisorIdeal (monomialPartCoeff I E) * N =
        divisorIdeal (monomialPartCoeff I E) * nonmonomialPart I E :=
      hd.eq_mul.symm.trans hex.eq_mul
    exact le_antisymm (le_of_mul_eq_mul hM he) (le_of_mul_eq_mul hM he.symm)
  · rintro ⟨rfl, rfl⟩
    exact hex

end MMP.Resolution

end

/-!
### The nonmonomial part of a birational transform

Let `(X, I, m, E)` be a marked triple with `m ≥ 1` and `Z ⊆ X` a smooth closed subscheme having
simple normal crossings with `E`, along every irreducible component of which the nonmonomial
part `N(I)` has order `≥ m`. Let `π : B_ZX → X` be the blow-up and `E' = π⁻¹_tot E`. Then
`ord_Z I ≥ m`, and the nonmonomial part of the birational transform `π⁻¹_*(I, m)` with respect
to `E'` is the birational (controlled) transform `π⁻¹_*N(I)` of `N(I)`.

Implementation notes:

The source writes `ord_Z N(I) = μ ≥ m` with one `μ` for all components of `Z`; the statement
asks only `ord_{Z_j} N(I) ≥ m` along every component `Z_j`, the controlled transform of `N(I)`
using the order along each component separately.
-/

section

open CategoryTheory AlgebraicGeometry MMP.Resolution

namespace MMP.Resolution.Proof_lem_kr3e_nonmonomial_part_of_transform

open MMP.Flips.ResolutionInputs (stalk_mono)

private theorem multAt_antitone {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J) (x : X) :
    multAt J x ≤ multAt I x := by
  unfold multAt idealOrder
  exact iSup₂_mono' fun j hj => ⟨j, (stalk_mono h x).trans hj, le_rfl⟩

/-- `ord_Z` is antitone in the ideal. -/
private theorem OrderAlongGE.of_le {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ≤ J)
    {Z : Set X} {m : ℕ∞} (hJ : OrderAlongGE J Z m) : OrderAlongGE I Z m :=
  fun W hW => (hJ W hW).trans (multAt_antitone h _)

/-- An effective Cartier divisor can be cancelled: `A·D = B·D` forces `A = B`. -/
private theorem mul_right_cancel_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {A B D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (h : A * D = B * D) : A = B := by
  have key : ∀ A B : X.IdealSheafData, A * D = B * D → A ≤ B := by
    intro A B h
    refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
    obtain ⟨g, hg, hgs⟩ :=
      AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D hD y
    have hy := congrArg (fun J => IdealSheafData.stalk J y) h
    simp only [IdealSheafData.stalk_mul, hgs] at hy
    intro x hx
    have hxg : x * g ∈ IdealSheafData.stalk B y * Ideal.span {g} :=
      hy ▸ Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self g)
    obtain ⟨b, hb, hbg⟩ := Ideal.mem_mul_span_singleton.mp hxg
    rw [hg.2 hbg] at hb
    exact hb
  exact le_antisymm (key A B h) (key B A h.symm)

private theorem isNonzeroAtGenericPoints_of_le {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I ≤ J) (hI : IsNonzeroAtGenericPoints I) : IsNonzeroAtGenericPoints J :=
  fun η hη hJ => hI η hη (le_bot_iff.mp (hJ ▸ stalk_mono h η))

/-- Splitting `𝒪(-∑_j a_jF_j)` along `a = b + c`. -/
private theorem exceptionalDivisorIdeal_add {X : Scheme.{u}} [IsNoetherian X]
    (Z : X.IdealSheafData) (b c : componentsOf (Z.support : Set X) → ℕ) :
    exceptionalDivisorIdeal Z (b + c) =
      exceptionalDivisorIdeal Z b * exceptionalDivisorIdeal Z c := by
  have : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  unfold exceptionalDivisorIdeal
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun W => pow_add _ _ _

/-- On a smooth scheme, a point of coheight `0` is not in the support of an effective Cartier
divisor. -/
private theorem notMem_support_of_coheight_eq_zero {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : MMP.Mori.IsSmoothScheme sY)
    {K : Y.IdealSheafData} (hK : Stacks.Divisors.IsEffectiveCartierDivisor K) (z : Y)
    (hz : Order.coheight z = 0) : z ∉ (K.support : Set Y) := fun hzK => by
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI := Aux.smooth_of_isSmoothScheme' sY hY
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sY z
  haveI : IsDomain (Y.presheaf.stalk z) := IsRegularLocalRing.isDomain _
  have : Ring.KrullDimLE 0 (Y.presheaf.stalk z) :=
    krullDimLE_of_coheight_le (by rw [hz]; rfl)
  letI := (Ring.KrullDimLE.isField_of_isDomain (R := Y.presheaf.stalk z)).toField
  obtain ⟨g, hg, hgs⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor K hK z
  have : IdealSheafData.stalk K z = ⊤ := by
    rw [hgs, Ideal.span_singleton_eq_top]
    exact isUnit_iff_ne_zero.mpr (isRegular_iff_ne_zero.mp hg)
  exact ((IdealSheafData.stalk_eq_top_iff_notMem_support K z).1 this) hzK

/-- On a smooth scheme an effective Cartier divisor is the ideal of its divisorial part:
`K = 𝒪(-Div K)`. Locally `K = (g)` with `g` a nonzerodivisor of the factorial local ring, and the
prime factors of `g` are the local equations of the components of `cosupp K` through the point. -/
private theorem divisorialPartIdeal_eq_of_isEffectiveCartierDivisor {k : Type u} [Field k]
    {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (hY : MMP.Mori.IsSmoothScheme sY) {K : Y.IdealSheafData}
    (hK : Stacks.Divisors.IsEffectiveCartierDivisor K) : divisorialPartIdeal K = K := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  haveI := Aux.smooth_of_isSmoothScheme' sY hY
  have hdom : ∀ z : Y, IsDomain (Y.presheaf.stalk z) := fun z => by
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY z
    exact IsRegularLocalRing.isDomain _
  set P := divisorialPartIdeal K with hPdef
  have hKP : K ≤ P := le_divisorialPartIdeal sY hY K
  -- the local generator of `K` is nonzero
  have hgen : ∀ z : Y, ∃ g : Y.presheaf.stalk z, g ≠ 0 ∧
      IdealSheafData.stalk K z = Ideal.span {g} := fun z => by
    haveI := hdom z
    obtain ⟨g, hg, hgs⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor K hK z
    exact ⟨g, isRegular_iff_ne_zero.mp hg, hgs⟩
  have hKnz : IsNonzeroAtGenericPoints K := fun η _ h0 => by
    obtain ⟨g, hg0, hgs⟩ := hgen η
    rw [hgs, Ideal.span_singleton_eq_bot] at h0
    exact hg0 h0
  have hzero := notMem_support_of_coheight_eq_zero sY hY hK
  -- along a prime divisor, `P ≤ K`
  have hcod1 : ∀ y : Y, Order.coheight y = 1 →
      IdealSheafData.stalk P y ≤ IdealSheafData.stalk K y := by
    intro y hy1
    by_cases hyK : y ∈ (K.support : Set Y)
    swap
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support K y).2 hyK]; exact le_top
    set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1
    have hDg : D.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy1
    have hDs : (D.support : Set Y) = closure {y} := by
      rw [Aux.support_eq_closure_genericPoint, hDg]
    have hcomp : (D.support : Set Y) ∈ componentsOf (K.support : Set Y) := by
      rw [hDs]
      refine ⟨⟨isIrreducible_singleton.closure,
        (K.support.isClosed.closure_subset_iff).2 (Set.singleton_subset_iff.2 hyK)⟩, ?_⟩
      intro V hV hyV
      have hVc := hV.1.closure
      set ξ := hVc.genericPoint
      have hξ : closure ({ξ} : Set Y) = closure V := hVc.isGenericPoint_genericPoint_closure.trans
        isClosed_closure.closure_eq
      have hξK : ξ ∈ (K.support : Set Y) := by
        have : ξ ∈ closure V := hξ ▸ subset_closure rfl
        exact (K.support.isClosed.closure_subset_iff.2 hV.2) this
      have hξy : ξ ⤳ y :=
        specializes_iff_mem_closure.2 (hξ ▸ subset_closure (hyV (subset_closure rfl)))
      by_cases hne : y = ξ
      · rw [hne, hξ]; exact subset_closure
      · exfalso
        have hlt := MMP.Intersection.lt_of_specializes_of_ne hξy hne
        have h0 : Order.coheight ξ = 0 := by
          have := Order.coheight_strictAnti hlt
            (lt_of_le_of_lt (Order.coheight_anti hlt.le) (by rw [hy1]; decide))
          rw [hy1] at this
          exact ENat.lt_one_iff_eq_zero.1 this
        exact hzero ξ h0 hξK
    set a := (multAt K y).toNat
    have ha : (a : ℕ∞) = multAt K y :=
      ENat.coe_toNat (multAt_ne_top_of_isNonzeroAtGenericPoints hKnz y)
    -- `P ≤ I_D^a`
    have hPD : P ≤ D.idealSheaf ^ a := by
      have hcoef : (divisorialPartCoeff K D).toNat = a := by
        simp [divisorialPartCoeff, hcomp, hDg, a]
      have hfin := finite_support_divisorialPartCoeff K
      have hsub : Function.mulSupport (fun D' : AlgebraicGeometry.PrimeDivisor Y =>
          D'.idealSheaf ^ (divisorialPartCoeff K D').toNat) ⊆ (hfin.toFinset ∪ {D} : Finset _) := by
        intro D' hD'
        rw [Function.mem_mulSupport] at hD'
        simp only [Finset.coe_union, Finset.coe_singleton, Set.Finite.coe_toFinset]
        left
        intro h0
        exact hD' (by rw [h0]; simp)
      rw [hPdef, divisorialPartIdeal, finprod_eq_prod_of_mulSupport_subset _ hsub,
        ← Finset.mul_prod_erase _ _ (Finset.mem_union_right _ (Finset.mem_singleton_self D)),
        hcoef]
      refine IdealSheafData.le_of_stalk_le _ _ fun z => ?_
      rw [Aux.stalk_mul]
      exact Ideal.mul_le_inf.trans inf_le_left
    haveI := hdom y
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sY y
    have hDy : IdealSheafData.stalk D.idealSheaf y =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
      hDg ▸ Aux.stalk_idealSheaf_genericPoint D
    obtain ⟨π, hπ, hπD⟩ := Aux.exists_prime_stalk_idealSheaf sY hY D
      (show y ∈ D.support from hDs ▸ subset_closure rfl)
    rw [hDy] at hπD
    have hnf : ¬ IsField (Y.presheaf.stalk y) := by
      intro hf
      have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
      rw [h0, eq_comm, Ideal.span_singleton_eq_bot] at hπD
      exact hπ.ne_zero hπD
    haveI : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
      ((IsDiscreteValuationRing.TFAE _ hnf).out 5 1).mp
        (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) from ⟨⟨π, hπD⟩⟩)
    obtain ⟨g, hg0, hgs⟩ := hgen y
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := IdealSheafData.stalk K y) (by rw [hgs, Ne, Ideal.span_singleton_eq_bot]; exact hg0)
      hπ.irreducible
    have hKy : IdealSheafData.stalk K y = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n := by
      rw [hn, hπD, Ideal.span_singleton_pow]
    have hna : n ≤ a := by
      have : (n : ℕ∞) ≤ multAt K y := by
        unfold multAt
        rw [natCast_le_idealOrder_iff', hKy]
      exact_mod_cast ha ▸ this
    calc IdealSheafData.stalk P y ≤ IdealSheafData.stalk (D.idealSheaf ^ a) y := stalk_mono hPD y
      _ = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ a := by rw [Aux.stalk_pow, hDy]
      _ ≤ _ := hKy ▸ Ideal.pow_le_pow_right hna
  have hPc : Stacks.Divisors.IsEffectiveCartierDivisor P := by
    refine finprod_induction Stacks.Divisors.IsEffectiveCartierDivisor ?_
      (fun _ _ => AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _) fun D =>
        Stacks.Divisors.isEffectiveCartierDivisor_pow
          (Aux.isEffectiveCartierDivisor_idealSheaf sY hY D) _
    refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun y _ => ⟨1, isRegular_one, ?_⟩
    rw [Ideal.span_singleton_one]
    exact stalk_one y
  refine le_antisymm (IdealSheafData.le_of_stalk_le _ _ fun x => ?_) hKP
  haveI := hdom x
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sY x
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk x)
  obtain ⟨g, hg0, hgs⟩ := hgen x
  obtain ⟨h, -, hhs⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor P hPc x
  obtain ⟨n, rfl⟩ : h ∣ g := by
    have := stalk_mono hKP x
    rwa [hgs, hhs, Ideal.span_singleton_le_span_singleton] at this
  suffices hu : IsUnit n by
    rw [hgs, hhs, Ideal.span_singleton_mul_right_unit hu]
  by_contra hn
  have hn0 : n ≠ 0 := right_ne_zero_of_mul hg0
  obtain ⟨p, hp, hpn⟩ := WfDvdMonoid.exists_irreducible_factor hn hn0
  have hpp : Prime p := hp.prime
  let q : PrimeSpectrum (Y.presheaf.stalk x) :=
    ⟨Ideal.span {p}, (Ideal.span_singleton_prime hpp.ne_zero).2 hpp⟩
  set y := Y.fromSpecStalk x q
  have hsp : y ⤳ x := MMP.Intersection.fromSpecStalk_specializes x q
  have hq : MMP.Intersection.primeOfSpecializes hsp = Ideal.span {p} :=
    MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk x q
  set φ := (Y.presheaf.stalkSpecializes hsp).hom
  have hmem : ∀ c, p ∣ c → φ c ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := fun c hc =>
    show c ∈ MMP.Intersection.primeOfSpecializes hsp from
      hq ▸ Ideal.mem_span_singleton.2 hc
  have hKy : IdealSheafData.stalk K y = Ideal.span {φ (h * n)} := by
    rw [Aux.stalk_eq_map_stalkSpecializes K hsp, hgs, Ideal.map_span, Set.image_singleton]
  have hPy : IdealSheafData.stalk P y = Ideal.span {φ h} := by
    rw [Aux.stalk_eq_map_stalkSpecializes P hsp, hhs, Ideal.map_span, Set.image_singleton]
  have hφ0 : φ (h * n) ≠ 0 := by
    obtain ⟨g', hg'0, hg's⟩ := hgen y
    intro h0
    rw [hKy, h0, Ideal.span_singleton_eq_bot.2 rfl, eq_comm, Ideal.span_singleton_eq_bot] at hg's
    exact hg'0 hg's
  have hy1 : Order.coheight y = 1 := by
    refine le_antisymm (MMP.Intersection.coheight_le_one_of_primeOfSpecializes_eq_span hsp hq) ?_
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    refine hzero y h0 ?_
    by_contra hyK
    have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support K y).2 hyK
    rw [hKy, Ideal.span_singleton_eq_top] at htop
    exact (fun hu => (IsLocalRing.mem_maximalIdeal _).1
      (hmem _ (hpn.trans (dvd_mul_left n h))) hu) htop
  have hle := hcod1 y hy1
  rw [hKy, hPy, Ideal.span_singleton_le_span_singleton, map_mul] at hle
  obtain ⟨c, hc⟩ := hle
  haveI := hdom y
  have hφh : φ h ≠ 0 := left_ne_zero_of_mul (map_mul φ h n ▸ hφ0)
  have : φ n * c = 1 := by
    apply mul_left_cancel₀ hφh
    rw [mul_one, ← mul_assoc, ← hc]
  exact (IsLocalRing.mem_maximalIdeal _).1 (hmem n hpn) (IsUnit.of_mul_eq_one _ this)

/-- A prime divisor inside the support of an ordered divisor whose entries are of pure
codimension one is an irreducible component of one of its entries. -/
private theorem OrderedDivisor.isComponent_of_subset_support {Y : Scheme.{u}} [IsNoetherian Y]
    (E : OrderedDivisor Y) (hE : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support)
    (D : AlgebraicGeometry.PrimeDivisor Y) (hD : D.support ⊆ E.support) : E.IsComponent D := by
  classical
  have hDirr : IsIrreducible D.support := by
    rw [Aux.support_eq_closure_genericPoint]; exact isIrreducible_singleton.closure
  obtain ⟨_, hz, hDz⟩ := isIrreducible_iff_sUnion_isClosed.mp hDirr
    (Finset.univ.image fun i => ((E.E i).support : Set Y))
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (E.E i).support.isClosed)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hD hx)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩),
        hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
  refine ⟨i, ⟨hDirr, hDz⟩, fun V hV hDV => ?_⟩
  have hcl := (E.E i).support.isClosed
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hcl
  obtain ⟨W, hW, hVW⟩ := isIrreducible_iff_sUnion_isClosed.mp hV.1 hfin.toFinset
    (fun W hW => Aux.isClosed_of_mem_componentsOf hcl (hfin.mem_toFinset.1 hW))
    (by rw [hfin.coe_toFinset]; exact hV.2.trans hcov)
  rw [hfin.mem_toFinset] at hW
  let W₀ : TopologicalSpace.IrreducibleCloseds Y :=
    ⟨W, hW.1.1, Aux.isClosed_of_mem_componentsOf hcl hW⟩
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds Y =>
      (W' : Set Y) ⊆ (E.E i).support) W₀ :=
    ⟨hW.1.2, fun V hV hWV => hW.2 ⟨V.isIrreducible, hV⟩ hWV⟩
  have h1 := hE i W₀ hmax
  let D₀ : TopologicalSpace.IrreducibleCloseds Y :=
    ⟨D.support, hDirr, D.idealSheaf.support.isClosed⟩
  have hD₀ : D₀ = TopologicalSpace.IrreducibleCloseds.closureSingleton D.genericPoint := by
    ext1
    exact Aux.support_eq_closure_genericPoint D
  have hD1 : codimension D₀ = 1 := hD₀ ▸ D.codimension_one
  have hle : D₀ ≤ W₀ := show D.support ⊆ W from hDV.trans hVW
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    rw [codimension_eq_coheight] at h1 hD1
    have := Order.coheight_strictAnti hlt (by rw [h1]; decide)
    rw [h1, hD1] at this
    exact lt_irrefl _ this
  · have : W = D.support :=
      congrArg (fun T : TopologicalSpace.IrreducibleCloseds Y => (T : Set Y)) heq.symm
    exact this ▸ hVW

/-- The monomial part `M(I)` is a finite product of powers of the ideals of the prime divisors
that are components of members of `E`. -/
private theorem exists_finset_monomialPart_eq_prod {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] (I : X.IdealSheafData)
    (E : OrderedDivisor X) :
    ∃ S : Finset (AlgebraicGeometry.PrimeDivisor X), (S : Set _) = {D | E.IsComponent D} ∧
      monomialPart I E = ∏ D ∈ S, D.idealSheaf ^ monomialPartCoeff I E D := by
  classical
  obtain ⟨S, hS⟩ := (Aux.finite_primeDivisor_of_isComponent sX E.E).exists_finset_coe
  refine ⟨S, hS, finprod_eq_prod_of_mulSupport_subset _ fun D hD => ?_⟩
  rw [Function.mem_mulSupport] at hD
  rw [Finset.mem_coe, ← Finset.mem_coe, hS]
  by_contra hc
  exact hD (by simp [monomialPartCoeff, OrderedDivisor.IsComponent, show ¬ ∃ i,
    D.support ∈ componentsOf ((E.E i).support : Set X) from hc])

/-- Off the support of `E`, the monomial part `M(I)` is trivial. -/
private theorem stalk_monomialPart_eq_top {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] {I : X.IdealSheafData}
    (E : OrderedDivisor X) {x : X} (hx : x ∉ E.support) :
    IdealSheafData.stalk (monomialPart I E) x = ⊤ := by
  classical
  obtain ⟨S, hS, hM⟩ := exists_finset_monomialPart_eq_prod sX I E
  rw [hM, stalk_prod]
  rw [← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun D hD => ?_
  have hD' : D ∈ (S : Set _) := hD
  rw [hS] at hD'
  obtain ⟨i, hi⟩ := hD'
  have hxD : x ∉ (D.idealSheaf.support : Set X) := fun hxD =>
    hx (Set.mem_iUnion.2 ⟨i, hi.1.2 hxD⟩)
  rw [Aux.stalk_pow, (IdealSheafData.stalk_eq_top_iff_notMem_support _ x).2 hxD, Ideal.top_pow,
    Ideal.one_eq_top]

/-- On a smooth scheme the monomial part `M(I)` is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_monomialPart {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : MMP.Mori.IsSmoothScheme sX) (I : X.IdealSheafData) (E : OrderedDivisor X) :
    Stacks.Divisors.IsEffectiveCartierDivisor (monomialPart I E) := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨S, -, hM⟩ := exists_finset_monomialPart_eq_prod sX I E
  rw [hM]
  refine Finset.prod_induction _ Stacks.Divisors.IsEffectiveCartierDivisor
    (fun _ _ => AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _) ?_ fun D _ =>
      Stacks.Divisors.isEffectiveCartierDivisor_pow
        (Aux.isEffectiveCartierDivisor_idealSheaf sX hX D) _
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun y _ => ⟨1, isRegular_one, ?_⟩
  rw [Ideal.span_singleton_one]
  exact stalk_one y

/-- The order of an ideal does not drop under a local homomorphism. -/
private theorem idealOrder_le_idealOrder_map {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map φ) := by
  unfold idealOrder
  refine iSup₂_mono' fun j hj => ⟨j, (Ideal.map_mono hj).trans ?_, le_rfl⟩
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap φ).ge) j

/-- Orders are unchanged under pull-back along an open immersion. -/
private theorem multAt_comap_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (K : X.IdealSheafData) (y : Y) : multAt (K.comap f) y = multAt K (f y) := by
  unfold multAt
  rw [IdealSheafData.stalk_comap]
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have he : ((f.stalkMap y).hom : _ →+* _) = e.toRingHom := rfl
  rw [he]
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm.toRingHom⟩
  haveI : IsLocalHom e.symm.toRingHom := ⟨fun a ha => by simpa using ha.map e.toRingHom⟩
  refine le_antisymm ?_ (idealOrder_le_idealOrder_map _ _)
  have hss : ((IdealSheafData.stalk K (f y)).map e.toRingHom).map e.symm.toRingHom =
      IdealSheafData.stalk K (f y) := by
    rw [Ideal.map_map]
    simp
  calc _ ≤ idealOrder (((IdealSheafData.stalk K (f y)).map e.toRingHom).map
        e.symm.toRingHom) := idealOrder_le_idealOrder_map _ _
    _ = _ := by rw [hss]

private theorem isSmoothScheme_comp_of_isOpenImmersion {k : Type u} [Field k] {X Y : Scheme.{u}}
    (ψ : Y ⟶ X) [IsOpenImmersion ψ] {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    (hs : MMP.Mori.IsSmoothScheme s) : MMP.Mori.IsSmoothScheme (ψ ≫ s) := by
  have : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := s)).mpr inferInstance
  have : LocallyOfFinitePresentation (ψ ≫ s) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := ψ ≫ s)).mpr inferInstance
  rw [MMP.Mori.isSmoothScheme_iff] at hs ⊢
  infer_instance

private theorem isSmoothScheme_comap_subschemeι_of_isOpenImmersion {k : Type u} [Field k]
    {X Y : Scheme.{u}} (ψ : Y ⟶ X) [IsOpenImmersion ψ] (Z : X.IdealSheafData)
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    (hs : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) :
    MMP.Mori.IsSmoothScheme ((Z.comap ψ).subschemeι ≫ ψ ≫ s) := by
  have e : (Z.comap ψ).subschemeι ≫ ψ ≫ s =
      ((Z.comapIso ψ).hom ≫ Limits.pullback.snd ψ Z.subschemeι) ≫ Z.subschemeι ≫ s := by
    rw [← Z.comapIso_hom_fst ψ, Category.assoc, Category.assoc, ← Category.assoc _ ψ,
      Limits.pullback.condition, Category.assoc]
  rw [e]
  exact isSmoothScheme_comp_of_isOpenImmersion _ hs

/-- Along a prime divisor `D` of `B_ZX` lying over `Z`, the order of a pull-back `π^*J` is the
order of `J` along the component `Z_j` of `Z` through `π(η_D)`. Off the other components, `Z` is
the irreducible `Z_j`; the blow-up commutes with this open restriction, `D` is the exceptional
divisor there, and `ord_F(π^*J) = ord_{Z_j} J` by `orderAlong_comap_blowUpToBase_eq`. -/
private theorem exists_multAt_comap_eq_orderAlong {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : MMP.Mori.IsSmoothScheme sX) {Z : X.IdealSheafData}
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodimZ : HasComponentsOfPositiveCodim (Z.support : Set X))
    [LocallyOfFiniteType (blowUpToBase Z ≫ sX)] (hB : MMP.Mori.IsSmoothScheme (blowUpToBase Z ≫ sX))
    (D : AlgebraicGeometry.PrimeDivisor (blowUp Z))
    (hξ : blowUpToBase Z D.genericPoint ∈ (Z.support : Set X)) :
    ∃ (W : Set X) (hW : W ∈ componentsOf (Z.support : Set X)), blowUpToBase Z D.genericPoint ∈ W ∧
      ∀ J : X.IdealSheafData,
        multAt (J.comap (blowUpToBase Z)) D.genericPoint = orderAlong J hW.1.1 := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  set π := blowUpToBase Z
  set η := D.genericPoint
  set x := π η
  obtain ⟨W0, hW0, hxW0, -, -, -⟩ := exists_component_through sX hX Z hZ ⊥ x hξ
  refine ⟨W0, hW0, hxW0, fun J => ?_⟩
  have hW0c : IsClosed W0 := isClosed_of_mem_componentsOf Z.support.2 hW0
  -- the union `O` of the other components, and its complement `V`
  set O : Set X := ⋃ W ∈ {W | W ∈ componentsOf (Z.support : Set X) ∧ W ≠ W0}, W with hO
  have hOc : IsClosed O :=
    Set.Finite.isClosed_biUnion ((finite_componentsOf Z.support.2).subset fun W hW => hW.1)
      fun W hW => isClosed_of_mem_componentsOf Z.support.2 hW.1
  have hW0O : ∀ y ∈ W0, y ∉ O := by
    intro y hy hyO
    simp only [hO, Set.mem_iUnion] at hyO
    obtain ⟨W, ⟨hW, hne⟩, hyW⟩ := hyO
    obtain ⟨W1, hW1, -, hu1, -, -⟩ := exists_component_through sX hX Z hZ ⊥ y (hW0.1.2 hy)
    exact hne ((hu1 W hW hyW).trans (hu1 W0 hW0 hy).symm)
  have hZV : ∀ y ∈ (Z.support : Set X), y ∉ O → y ∈ W0 := by
    intro y hy hyO
    obtain ⟨W1, hW1, hyW1, -, -, -⟩ := exists_component_through sX hX Z hZ ⊥ y hy
    by_contra hy0
    exact hyO (Set.mem_biUnion (x := W1) ⟨hW1, fun h => hy0 (h ▸ hyW1)⟩ hyW1)
  let V : X.Opens := ⟨Oᶜ, hOc.isOpen_compl⟩
  set j := V.ι
  have hjv : ∀ v, j v = (v : V).1 := fun v => Scheme.Opens.ι_apply V v
  have hxV : x ∈ V := hW0O x hxW0
  have hlift : ∀ y ∈ V, ∃ v, j v = y := fun y hy => ⟨⟨y, hy⟩, hjv _⟩
  have hsuppV : ((Z.comap j).support : Set V) = j ⁻¹' W0 := by
    ext v
    change v ∈ (Z.comap j).support ↔ j v ∈ W0
    rw [mem_support_comap_iff]
    refine ⟨fun h => hZV _ h (by rw [hjv]; exact v.2), fun h => hW0.1.2 h⟩
  have hirr : IsIrreducible ((Z.comap j).support : Set V) := by
    rw [hsuppV]
    obtain ⟨x', hx'⟩ := hlift x hxV
    exact ⟨⟨x', show j x' ∈ W0 by rw [hx']; exact hxW0⟩,
      hW0.1.1.2.preimage j.isOpenEmbedding⟩
  set ζ := hirr.genericPoint
  have hζ : IsGenericPoint ζ ((Z.comap j).support : Set V) :=
    hirr.isGenericPoint_genericPoint_closure.trans (Z.comap j).support.isClosed.closure_eq
  have hjζ : IsGenericPoint (j ζ) W0 := by
    have hζW : j ζ ∈ W0 := (hsuppV ▸ hζ.mem : ζ ∈ j ⁻¹' W0)
    refine subset_antisymm (closure_minimal (Set.singleton_subset_iff.2 hζW) hW0c) ?_
    intro y hy
    have hyV : y ∈ V := hW0O y hy
    obtain ⟨v, hv'⟩ := hlift y hyV
    have hv : v ∈ ((Z.comap j).support : Set V) := by
      rw [hsuppV, Set.mem_preimage, hv']
      exact hy
    have hsp : ζ ⤳ v := hζ.specializes hv
    have := hsp.map j.continuous
    rw [hv'] at this
    exact specializes_iff_mem_closure.1 this
  have hgp : hW0.1.1.genericPoint = j ζ :=
    (show IsGenericPoint _ W0 from
      hW0.1.1.isGenericPoint_genericPoint_closure.trans hW0c.closure_eq).eq hjζ
  -- `Z|_V` has positive codimension
  have hcodim : 1 ≤ codimension
      (⟨(Z.comap j).support, hirr, (Z.comap j).support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds V) := by
    have h1 := hcodimZ W0 hW0
    rw [codimension_eq_coheight, ENat.one_le_iff_ne_zero, Ne, Order.coheight_eq_zero,
      not_isMax_iff] at h1 ⊢
    obtain ⟨T, hT⟩ := h1
    set c := T.isIrreducible.genericPoint
    have hc : IsGenericPoint c (T : Set X) :=
      T.isIrreducible.isGenericPoint_genericPoint_closure.trans T.isClosed.closure_eq
    have hW0T : W0 ⊆ T := by
      have := hT.le
      exact (subset_closure).trans this
    have hcζ : c ⤳ j ζ := hc.specializes (hW0T hjζ.mem)
    have hcV : c ∈ V := hcζ.mem_open V.isOpen (by rw [hjv]; exact (ζ).2)
    have hcW0 : c ∉ W0 := by
      intro hcW
      refine hT.not_ge ?_
      show (T : Set X) ⊆ closure W0
      rw [← hc.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (subset_closure hcW)) isClosed_closure
    obtain ⟨c', hc'⟩ : ∃ c', j c' = c := ⟨⟨c, hcV⟩, hjv _⟩
    refine ⟨TopologicalSpace.IrreducibleCloseds.closureSingleton c', ?_⟩
    have hcζ' : c' ⤳ ζ := (j.isOpenEmbedding.isInducing.specializes_iff).1 (hc' ▸ hcζ)
    refine lt_of_le_of_ne ?_ ?_
    · show ((Z.comap j).support : Set V) ⊆ closure {c'}
      rw [← hζ.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hcζ'))
        isClosed_closure
    · intro heq
      have hmem : c' ∈ ((Z.comap j).support : Set V) := by
        have := congrArg (fun T : TopologicalSpace.IrreducibleCloseds V => (T : Set V)) heq
        change ((Z.comap j).support : Set V) = closure {c'} at this
        rw [this]; exact subset_closure rfl
      rw [hsuppV] at hmem
      exact hcW0 (hc' ▸ hmem)
  -- the blow-up of `Z|_V`
  have hsb : IsSmoothBlowup (j ≫ sX) (Z.comap j) :=
    ⟨isSmoothScheme_comp_of_isOpenImmersion j hX,
      isSmoothScheme_comap_subschemeι_of_isOpenImmersion j Z hZ⟩
  have key := orderAlong_comap_blowUpToBase_eq (j ≫ sX) (Z.comap j) hsb hirr hcodim (J.comap j)
  set hF := isIrreducible_support_exceptionalPrimeDivisor (j ≫ sX) (Z.comap j) hsb hirr hcodim
  set π' := blowUpToBase (Z.comap j)
  set ξ' := hF.genericPoint
  have key' : multAt ((J.comap j).comap π') ξ' = multAt (J.comap j) ζ := key
  have hsupF : (exceptionalPrimeDivisor (j ≫ sX) (Z.comap j) hsb hirr hcodim).support =
      (((Z.comap j).comap π').support : Set (blowUp (Z.comap j))) := rfl
  have hξ'gen : IsGenericPoint ξ' (((Z.comap j).comap π').support : Set (blowUp (Z.comap j))) :=
    hsupF ▸ (hF.isGenericPoint_genericPoint_closure.trans
      (hsupF ▸ ((Z.comap j).comap π').support.isClosed.closure_eq))
  set ψ := canonicalLift j Z
  have hsq := MMP.Resolution.Kollar.isPullback_canonicalLift_of_flat j Z
  haveI : IsOpenImmersion ψ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq inferInstance
  have hcomm : ∀ p, π (ψ p) = j (π' p) := fun p => by
    rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  have hval : multAt (J.comap π) (ψ ξ') = orderAlong J hW0.1.1 := by
    rw [← multAt_comap_of_isOpenImmersion, ← Scheme.IdealSheafData.comap_comp,
      canonicalLift_comp_blowUpToBase, Scheme.IdealSheafData.comap_comp, key',
      multAt_comap_of_isOpenImmersion]
    show _ = multAt J hW0.1.1.genericPoint
    rw [hgp]
  -- `ψ ξ'` is the generic point of `D`
  obtain ⟨p, hp⟩ : η ∈ Set.range (Limits.pullback.snd j π) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    obtain ⟨x', hx'⟩ := hlift x hxV
    exact ⟨x', hx'⟩
  set η'' := hsq.isoPullback.inv p
  have hψη : ψ η'' = η := by
    have e2 : ∀ q, ψ q = Limits.pullback.snd j π (hsq.isoPullback.hom q) := fun q => by
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_hom_snd]
    rw [e2]
    change Limits.pullback.snd j π ((hsq.isoPullback.inv ≫ hsq.isoPullback.hom) p) = η
    rw [Iso.inv_hom_id]
    exact hp
  have hη''F : η'' ∈ (((Z.comap j).comap π').support : Set (blowUp (Z.comap j))) := by
    change η'' ∈ ((Z.comap j).comap π').support
    rw [mem_support_comap_iff, mem_support_comap_iff, ← hcomm, hψη]
    exact hξ
  have hsp : ψ ξ' ⤳ η := hψη ▸ (hξ'gen.specializes hη''F).map ψ.continuous
  have hψξ'Z : ψ ξ' ∈ ((Z.comap π).support : Set (blowUp Z)) := by
    change ψ ξ' ∈ (Z.comap π).support
    rw [mem_support_comap_iff, hcomm, ← mem_support_comap_iff]
    have : ξ' ∈ (((Z.comap j).comap π').support : Set (blowUp (Z.comap j))) := hξ'gen.mem
    change ξ' ∈ ((Z.comap j).comap π').support at this
    rwa [mem_support_comap_iff] at this
  have hη1 : Order.coheight η = 1 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    exact D.codimension_one
  have heq : ψ ξ' = η := by
    by_contra hne
    have hlt := MMP.Intersection.lt_of_specializes_of_ne hsp fun h => hne h.symm
    have h0 : Order.coheight (ψ ξ') = 0 := by
      have := Order.coheight_strictAnti hlt
        (lt_of_le_of_lt (Order.coheight_anti hlt.le) (by rw [hη1]; decide))
      rw [hη1] at this
      exact ENat.lt_one_iff_eq_zero.1 this
    exact notMem_support_of_coheight_eq_zero (blowUpToBase Z ≫ sX) hB
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z) _ h0 hψξ'Z
  rw [← heq, hval]

section Obligations

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData}
  {E : OrderedDivisor X} (h : IsTriple sX I E) {m : ℕ} (hm : 1 ≤ m) {Z : X.IdealSheafData}
  (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZsnc : HasSNCWith E.E Z)
  (hN : OrderAlongGE (nonmonomialPart I E) (Z.support : Set X) m)

include h hm hZ hZsnc hN

/-- `π^*M(I) · 𝒪(-∑_j (μ_j - m)F_j)` is an effective Cartier divisor on `B_ZX`. -/
private theorem isEffectiveCartierDivisor_comap_monomialPart_mul :
    Stacks.Divisors.IsEffectiveCartierDivisor ((monomialPart I E).comap (blowUpToBase Z) *
        exceptionalDivisorIdeal Z fun W =>
          (orderAlong (nonmonomialPart I E) W.2.1.1).toNat - m) := by
  obtain ⟨-, hX, hlft, hqc, -, hI, -⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have hB := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) h hZsnc
  obtain ⟨-, hBsm, hBlft, -, -, -, -⟩ := hB
  haveI : LocallyOfFiniteType (blowUpToBase Z ≫ sX) := hBlft
  have := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z ≫ sX)
  have : LocallyOfFinitePresentation (blowUpToBase Z ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := blowUpToBase Z ≫ sX)).mpr
      inferInstance
  haveI : Smooth (blowUpToBase Z ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).1 hBsm
  refine AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _ ?_
    (isEffectiveCartierDivisor_exceptionalDivisorIdeal sX hX Z hZ _)
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun y _ => ?_
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (blowUpToBase Z ≫ sX) y
  haveI : IsDomain ((blowUp Z).presheaf.stalk y) := IsRegularLocalRing.isDomain _
  obtain ⟨g, -, hgs⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_monomialPart sX hX I E) (blowUpToBase Z y)
  set φ := ((blowUpToBase Z).stalkMap y).hom
  have hst : IdealSheafData.stalk ((monomialPart I E).comap (blowUpToBase Z)) y =
      Ideal.span {φ g} := by
    rw [IdealSheafData.stalk_comap, hgs, Ideal.map_span, Set.image_singleton]
  refine ⟨φ g, isRegular_iff_ne_zero.mpr fun hg0 => ?_, hst⟩
  -- `π^*I ⊆ π^*M(I)` would vanish at `y`, hence at a generic point specializing to `y`.
  have hIM : IdealSheafData.stalk (I.comap (blowUpToBase Z)) y = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [IdealSheafData.stalk_comap, ← Ideal.span_singleton_eq_bot.2 hg0, ← hst,
      IdealSheafData.stalk_comap]
    refine Ideal.map_mono ?_
    conv_lhs => rw [← monomialPart_mul_nonmonomialPart sX I E h]
    rw [IdealSheafData.stalk_mul]
    exact Ideal.mul_le_left (I := IdealSheafData.stalk (monomialPart I E) (blowUpToBase Z y))
      (J := IdealSheafData.stalk (nonmonomialPart I E) (blowUpToBase Z y))
  obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({y} : Set (blowUp Z)) isIrreducible_singleton
  have hCc := isClosed_of_mem_irreducibleComponents C hC
  set η := hC.1.genericPoint
  have hη : closure ({η} : Set (blowUp Z)) = C := by
    rw [hC.1.isGenericPoint_genericPoint_closure, hCc.closure_eq]
  have hηy : η ⤳ y := specializes_iff_mem_closure.2 (hη ▸ hyC rfl)
  refine isNonzeroAtGenericPoints_comap_blowUpToBase Z hI η (hη ▸ hC) ?_
  rw [Aux.stalk_eq_map_stalkSpecializes _ hηy, hIM, Ideal.map_bot]

/-- A prime divisor of `B_ZX` inside the cosupport of `π^*M(I) · 𝒪(-∑_j (μ_j - m)F_j)`, which
lies in `π⁻¹(Supp E ∪ Z) ⊆ Supp π⁻¹_tot E`, is a component of a member of `π⁻¹_tot E`. -/
private theorem isComponent_of_subset_support_comap_monomialPart_mul
    (D : AlgebraicGeometry.PrimeDivisor (blowUp Z))
    (hD : (D.support : Set (blowUp Z)) ⊆ (((monomialPart I E).comap (blowUpToBase Z) *
        exceptionalDivisorIdeal Z fun W =>
          (orderAlong (nonmonomialPart I E) W.2.1.1).toNat - m).support : Set (blowUp Z))) :
    (E.totalTransform Z).IsComponent D := by
  classical
  obtain ⟨-, hX, hlft, hqc, -, -, hE⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have hB := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) h hZsnc
  obtain ⟨-, -, hBlft, hBqc, -, -, hE'⟩ := hB
  haveI : LocallyOfFiniteType (blowUpToBase Z ≫ sX) := hBlft
  haveI : QuasiCompact (blowUpToBase Z ≫ sX) := hBqc
  have := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z ≫ sX)
  have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z ≫ sX)
  have : IsNoetherian (blowUp Z) := ⟨⟩
  refine OrderedDivisor.isComponent_of_subset_support _ (fun i => (hE'.2.1 i).2.1) D
    (hD.trans ?_)
  refine (Set.Subset.trans ?_ (preimage_union_subset_support_totalTransform E
    (fun i => (hE.2.1 i).2.1) Z))
  intro y hy
  by_contra hy'
  simp only [Set.mem_preimage, Set.mem_union, not_or] at hy'
  have hM : IdealSheafData.stalk ((monomialPart I E).comap (blowUpToBase Z)) y = ⊤ := by
    rw [IdealSheafData.stalk_eq_top_iff_notMem_support, mem_support_comap_iff]
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support]
    exact stalk_monomialPart_eq_top sX E hy'.2
  have hF := exists_stalk_exceptionalDivisorIdeal_eq sX hX Z hZ
    (fun W => (orderAlong (nonmonomialPart I E) W.2.1.1).toNat - m) y
  obtain ⟨n, hn, -, -⟩ := hF
  have hZy : IdealSheafData.stalk (Z.comap (blowUpToBase Z)) y = ⊤ := by
    rw [IdealSheafData.stalk_eq_top_iff_notMem_support, mem_support_comap_iff]
    exact hy'.1
  refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ y).1 ?_ hy
  rw [IdealSheafData.stalk_mul, hM, hn, hZy, Ideal.top_pow, Ideal.top_mul]

/-- The divisor `D' = π^*A(I) + ∑_j (μ_j - m) F_j`, `μ_j = ord_{Z_j} N(I)`, is effective and
supported on the components of the members of `π⁻¹_tot E`: `π^*E^{ik}` is the birational
transform of `E^{ik}` plus a multiple of the exceptional divisor. -/
private theorem exists_divisorIdeal_eq_comap_monomialPart_mul :
    ∃ A' : AlgebraicGeometry.PrimeDivisor (blowUp Z) → ℕ, (Function.support A').Finite ∧
      (∀ D, A' D ≠ 0 → (E.totalTransform Z).IsComponent D) ∧
      divisorIdeal A' = (monomialPart I E).comap (blowUpToBase Z) *
        exceptionalDivisorIdeal Z fun W =>
          (orderAlong (nonmonomialPart I E) W.2.1.1).toNat - m := by
  classical
  obtain ⟨-, hX, hlft, hqc, -, -, -⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have hB := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) h hZsnc
  obtain ⟨-, hBsm, hBlft, hBqc, -, -, -⟩ := hB
  haveI : LocallyOfFiniteType (blowUpToBase Z ≫ sX) := hBlft
  haveI : QuasiCompact (blowUpToBase Z ≫ sX) := hBqc
  have := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z ≫ sX)
  have : CompactSpace (blowUp Z) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase Z ≫ sX)
  have : IsNoetherian (blowUp Z) := ⟨⟩
  set J := (monomialPart I E).comap (blowUpToBase Z) *
    exceptionalDivisorIdeal Z fun W => (orderAlong (nonmonomialPart I E) W.2.1.1).toNat - m
  refine ⟨fun D => (divisorialPartCoeff J D).toNat,
    (finite_support_divisorialPartCoeff J).subset fun D hD hD0 => hD (by simp [hD0]), ?_, ?_⟩
  · intro D hD
    refine isComponent_of_subset_support_comap_monomialPart_mul sX h hm hZ hZsnc hN D ?_
    by_contra hsub
    exact hD (by simp [divisorialPartCoeff, show ¬ (D.support : Set (blowUp Z)) ∈
      componentsOf (J.support : Set (blowUp Z)) from fun hc => hsub hc.1.2])
  · exact divisorialPartIdeal_eq_of_isEffectiveCartierDivisor (blowUpToBase Z ≫ sX) hBsm
      (isEffectiveCartierDivisor_comap_monomialPart_mul sX h hm hZ hZsnc hN)

/-- The components of `Z` have positive codimension: a component of codimension `0` would be an
irreducible component of `X`, at whose generic point `N(I) ⊇ I` is nonzero, so of order `0`. -/
private theorem hasComponentsOfPositiveCodim :
    HasComponentsOfPositiveCodim (Z.support : Set X) := by
  obtain ⟨-, hX, hlft, -, -, hI, -⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
  haveI : IsReduced X := by
    haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
      haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
      haveI : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
      infer_instance
    exact isReduced_of_isReduced_stalk X
  intro W hW
  by_contra hlt
  have hcod : codimension (irreducibleClosure hW.1.1) = 0 := by
    rw [codimension_eq_coheight] at hlt ⊢
    exact ENat.lt_one_iff_eq_zero.1 (not_le.1 hlt)
  rw [codimension_eq_coheight, Order.coheight_eq_zero] at hcod
  set η := hW.1.1.genericPoint
  have hgen : closure ({η} : Set X) = closure W := hW.1.1.isGenericPoint_genericPoint_closure
  have hcomp : closure ({η} : Set X) ∈ irreducibleComponents X := by
    rw [hgen]
    refine ⟨hW.1.1.closure, fun C hC hWC => ?_⟩
    let C' : TopologicalSpace.IrreducibleCloseds X := ⟨closure C, hC.closure, isClosed_closure⟩
    have := hcod (b := C') (show closure W ⊆ closure C from hWC.trans subset_closure)
    exact subset_closure.trans this
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents X η hcomp
  have hNnz : IsNonzeroAtGenericPoints (nonmonomialPart I E) :=
    isNonzeroAtGenericPoints_of_le (le_idealColon _ _) hI
  have h1 : (1 : ℕ∞) ≤ multAt (nonmonomialPart I E) η :=
    le_trans (by exact_mod_cast hm) (hN W hW)
  unfold multAt at h1
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by simp, natCast_le_idealOrder_iff', pow_one] at h1
  letI := hfield.toField
  exact hNnz η hcomp (le_bot_iff.1 (h1.trans_eq (IsLocalRing.maximalIdeal_eq_bot)))

/-- `π⁻¹_*(I, m) = 𝒪(-(π^*A + ∑_j (μ_j - m)F_j)) · π⁻¹_*N(I)`: from `I = 𝒪(-A)·N(I)`,
`π^*N(I) = 𝒪(-∑ μ_j F_j)·π⁻¹_*N(I)` and `π^*I = 𝒪(-mF)·π⁻¹_*(I, m)`, cancelling the invertible
`𝒪(-mF)`. -/
private theorem birationalTransform_eq_comap_monomialPart_mul :
    ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I =
      (monomialPart I E).comap (blowUpToBase Z) *
        (exceptionalDivisorIdeal Z fun W =>
          (orderAlong (nonmonomialPart I E) W.2.1.1).toNat - m) *
        controlledTransform Z (nonmonomialPart I E) := by
  obtain ⟨-, hX, hlft, hqc, -, hI, -⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have hcodim := hasComponentsOfPositiveCodim sX h hm hZ hZsnc hN
  have hNnz : IsNonzeroAtGenericPoints (nonmonomialPart I E) :=
    isNonzeroAtGenericPoints_of_le (le_idealColon _ _) hI
  set μ : componentsOf (Z.support : Set X) → ℕ :=
    fun W => (orderAlong (nonmonomialPart I E) W.2.1.1).toNat with hμ
  have hmμ : ∀ W, m ≤ μ W := fun W => by
    have h1 := hN W.1 W.2
    have h2 := multAt_ne_top_of_isNonzeroAtGenericPoints hNnz W.2.1.1.genericPoint
    have := ENat.toNat_le_toNat h1 h2
    simpa using this
  have hsplit : (fun W => μ W - m) + (fun _ => m) = μ := funext fun W => Nat.sub_add_cancel (hmμ W)
  have hDc := isEffectiveCartierDivisor_exceptionalDivisorIdeal sX hX Z hZ (fun _ => m)
  refine mul_right_cancel_of_isEffectiveCartierDivisor hDc ?_
  have h1 : ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I *
      exceptionalDivisorIdeal Z (fun _ => m) = I.comap (blowUpToBase Z) := by
    rw [exceptionalDivisorIdeal_const sX hX Z hZ m]
    exact MarkedIdeal.birationalTransform_mul_eq sX hX Z hZ hcodim ⟨I, m⟩
      (OrderAlongGE.of_le (le_idealColon _ _) hN)
  have h2 : I.comap (blowUpToBase Z) = (monomialPart I E).comap (blowUpToBase Z) *
      (controlledTransform Z (nonmonomialPart I E) * exceptionalDivisorIdeal Z μ) := by
    conv_lhs => rw [← monomialPart_mul_nonmonomialPart sX I E h]
    rw [Stacks.IdealSheaf.comap_mul,
      ← controlledTransform_mul_eq sX hX Z hZ hcodim _ hNnz]
    rfl
  rw [h1, h2, ← hsplit, exceptionalDivisorIdeal_add]
  ac_rfl

/-- Off the centre: if the generic point `η` of a component of a member of `π⁻¹_tot E` does not
lie over `Z`, then `π(η)` is the generic point of a component of a member of `E`, so `N(I)` is
trivial at `π(η)`. -/
private theorem notMem_support_nonmonomialPart_of_notMem
    (D : AlgebraicGeometry.PrimeDivisor (blowUp Z)) (hD : (E.totalTransform Z).IsComponent D)
    (hξ : blowUpToBase Z D.genericPoint ∉ (Z.support : Set X)) :
    blowUpToBase Z D.genericPoint ∉ ((nonmonomialPart I E).support : Set X) := by
  classical
  obtain ⟨-, -, hlft, hqc, -, -, hE⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  set π := blowUpToBase Z
  set η := D.genericPoint
  set ξ := π η
  have hηD : η ∈ (D.support : Set (blowUp Z)) := by
    rw [Aux.support_eq_closure_genericPoint]; exact subset_closure rfl
  obtain ⟨i, hi⟩ := hD
  suffices key : ∀ j : Fin (E.s + 1), (D.support : Set (blowUp Z)) ∈
      componentsOf (closure (totalTransformSet E Z j)) →
        ξ ∉ ((nonmonomialPart I E).support : Set X) by
    exact key i (support_entry_totalTransform E Z i ▸ hi)
  intro i hi
  induction i using Fin.lastCases with
  | last =>
    exfalso
    have hcl : closure (totalTransformSet E Z (Fin.last _)) ⊆ π ⁻¹' (Z.support : Set X) := by
      refine (Z.support.isClosed.preimage π.continuous).closure_subset_iff.2 ?_
      rw [totalTransformSet, Fin.snoc_last]
      simp only [Set.iUnion_subset_iff]
      intro W hW _ x hx
      exact hW.1.2 hx
    exact hξ (hcl (hi.1.2 hηD))
  | cast i₀ =>
    rw [totalTransformSet, Fin.snoc_castSucc] at hi
    set T := π ⁻¹' (((E.E i₀).support : Set X) \ componentsOfCodimAtLeastTwo (Z.support : Set X))
    have hTsub : closure T ⊆ π ⁻¹' (E.E i₀).support :=
      ((E.E i₀).support.isClosed.preimage π.continuous).closure_subset_iff.2 fun x hx => hx.1
    have hξE : ξ ∈ ((E.E i₀).support : Set X) := hTsub (hi.1.2 hηD)
    have hcl := (E.E i₀).support.isClosed
    obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hcl
    obtain ⟨W, hW, hξW⟩ := Set.mem_sUnion.1 (hcov hξE)
    have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf hcl hW
    set w := hW.1.1.genericPoint
    have hw : closure {w} = W := hW.1.1.isGenericPoint_genericPoint_closure.def.trans hWc.closure_eq
    have hwξ : w ⤳ ξ := specializes_iff_mem_closure.2 (hw ▸ hξW)
    have hwZ : w ∉ (Z.support : Set X) := fun hwZ => hξ (hwξ.mem_closed Z.support.isClosed hwZ)
    -- lift the generization `w ⤳ ξ` along the isomorphism `π` off the centre
    let U : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
    haveI := isIso_blowUpToBase_restrict_of_subset_compl_support Z U le_rfl
    let e := (π ∣_ U).homeomorph
    let η' : (π ⁻¹ᵁ U : (blowUp Z).Opens) := ⟨η, hξ⟩
    let w₀ : U := ⟨w, hwZ⟩
    have he : e η' = ⟨ξ, hξ⟩ := Subtype.ext (morphismRestrict_base_coe π U η')
    have hw₀ : w₀ ⤳ e η' := by
      rw [he]
      exact (Topology.IsInducing.subtypeVal.specializes_iff (x := w₀) (y := ⟨ξ, hξ⟩)).1 hwξ
    set w' := (e.symm w₀).1
    have hw'η : w' ⤳ η := by
      have h1 := hw₀.map e.symm.continuous
      have h2 : e.symm (e η') = η' := e.symm_apply_apply η'
      rw [h2] at h1
      exact h1.map (π ⁻¹ᵁ U).ι.continuous
    have hπw' : π w' = w := by
      rw [← morphismRestrict_base_coe π U (e.symm w₀)]
      exact congrArg Subtype.val (e.apply_symm_apply w₀)
    have hw'T : w' ∈ T := by
      refine ⟨hπw' ▸ hW.1.2 (hw ▸ subset_closure rfl), fun h2 => hwZ ?_⟩
      rw [← hπw']
      obtain ⟨W', hW', -, hx⟩ := (mem_componentsOfCodimAtLeastTwo _ _).1 h2
      exact hW'.1.2 hx
    have hsub : closure ({w'} : Set (blowUp Z)) ⊆ D.support :=
      hi.2 ⟨isIrreducible_singleton.closure,
        closure_mono (Set.singleton_subset_iff.2 (subset_closure hw'T)) |>.trans
          closure_closure.subset⟩
        (by rw [Aux.support_eq_closure_genericPoint]
            exact closure_minimal (Set.singleton_subset_iff.2
              (specializes_iff_mem_closure.1 hw'η)) isClosed_closure)
    have hηw' : η ⤳ w' := by
      rw [specializes_iff_mem_closure, ← Aux.support_eq_closure_genericPoint]
      exact hsub (subset_closure rfl)
    have hweq : w = ξ := by rw [← hπw', (hw'η.antisymm hηw').eq]
    rw [hweq] at hw
    rw [← hw] at hW
    -- a prime divisor supported on `closure {ξ}`
    have hcoh : Order.coheight ξ = 1 := by
      rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
      refine (hE.2.1 i₀).2.1 _ ⟨hW.1.2, fun V hV hWV => ?_⟩
      exact hW.2 ⟨V.isIrreducible, hV⟩ hWV
    set D₀ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hcoh
    have hD₀ : (D₀.support : Set X) = closure {ξ} := by
      rw [Aux.support_eq_closure_genericPoint,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    have hmono := (isMonomialDecomposition_iff sX h (monomialPartCoeff I E)
      (nonmonomialPart I E)).2 ⟨rfl, rfl⟩
    intro hξN
    refine hmono.not_subset_cosupport D₀ ⟨i₀, hD₀ ▸ hW⟩ ?_
    rw [hD₀]
    exact closure_minimal (Set.singleton_subset_iff.2 hξN) (nonmonomialPart I E).support.isClosed

/-- Over the centre: at the generic point `η` of a prime divisor lying over `Z`, i.e. of a
component `F_j` of the exceptional divisor, `π^*N(I)` has order exactly `μ_j`, so the controlled
transform `π⁻¹_*N(I)` is trivial at `η`. -/
private theorem notMem_support_controlledTransform_of_mem
    (D : AlgebraicGeometry.PrimeDivisor (blowUp Z))
    (hξ : blowUpToBase Z D.genericPoint ∈ (Z.support : Set X)) :
    D.genericPoint ∉ ((controlledTransform Z (nonmonomialPart I E)).support : Set (blowUp Z)) := by
  classical
  obtain ⟨-, hX, hlft, hqc, -, hI, -⟩ := id h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have hB := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) h hZsnc
  obtain ⟨-, hBsm, hBlft, -, -, -, -⟩ := hB
  haveI : LocallyOfFiniteType (blowUpToBase Z ≫ sX) := hBlft
  have hcodim := hasComponentsOfPositiveCodim sX h hm hZ hZsnc hN
  have hNnz : IsNonzeroAtGenericPoints (nonmonomialPart I E) :=
    isNonzeroAtGenericPoints_of_le (le_idealColon _ _) hI
  obtain ⟨W0, hW0, hxW0, hmult⟩ := exists_multAt_comap_eq_orderAlong sX hX hZ hcodim hBsm D hξ
  set N := nonmonomialPart I E
  set η := D.genericPoint
  set π := blowUpToBase Z
  set μ := (orderAlong N hW0.1.1).toNat
  have hμ : (μ : ℕ∞) = orderAlong N hW0.1.1 :=
    ENat.coe_toNat (multAt_ne_top_of_isNonzeroAtGenericPoints hNnz _)
  intro hη
  have hNm : IdealSheafData.stalk (controlledTransform Z N) η ≤
      IsLocalRing.maximalIdeal ((blowUp Z).presheaf.stalk η) :=
    IsLocalRing.le_maximalIdeal fun htop =>
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ η).1 htop hη
  have : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  letI := Fintype.ofFinite (componentsOf (Z.support : Set X))
  have hCm : IdealSheafData.stalk (controlledTransformDivisorIdeal Z N) η ≤
      IsLocalRing.maximalIdeal ((blowUp Z).presheaf.stalk η) ^ μ := by
    unfold controlledTransformDivisorIdeal
    rw [finprod_eq_prod_of_fintype, stalk_prod]
    refine Ideal.prod_le_inf.trans ((Finset.inf_le (Finset.mem_univ
      (⟨W0, hW0⟩ : componentsOf (Z.support : Set X)))).trans ?_)
    rw [IdealSheafData.stalk_pow]
    refine Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal fun htop => ?_) μ
    refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ η).1 htop ?_
    rw [mem_support_comap_iff]
    change π η ∈ ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure W0)).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]
    exact subset_closure hxW0
  have hprod := controlledTransform_mul_eq sX hX Z hZ hcodim N hNnz
  have hle : IdealSheafData.stalk (N.comap π) η ≤
      IsLocalRing.maximalIdeal ((blowUp Z).presheaf.stalk η) ^ (μ + 1) := by
    rw [← hprod, IdealSheafData.stalk_mul, pow_succ']
    exact Ideal.mul_mono hNm hCm
  have h1 := (natCast_le_idealOrder_iff' _ (μ + 1)).2 hle
  rw [show idealOrder (IdealSheafData.stalk (N.comap π) η) = multAt (N.comap π) η from rfl,
    hmult, ← hμ] at h1
  exact absurd h1 (by norm_cast; omega)

/-- No component of a member of `π⁻¹_tot E` lies in `cosupp π⁻¹_*N(I)`: along each `F_j` the
pull-back `π^*N(I)` has order exactly `μ_j`, and the generic point of the birational transform of
`E^{ik} ⊄ Z` lies where `π` is an isomorphism and `N(I)` has order `0`. -/
private theorem not_subset_support_controlledTransform :
    ∀ D, (E.totalTransform Z).IsComponent D →
      ¬ D.support ⊆ ((controlledTransform Z (nonmonomialPart I E)).support : Set (blowUp Z)) := by
  intro D hD hsub
  have hηD : D.genericPoint ∈ (D.support : Set (blowUp Z)) := by
    rw [Aux.support_eq_closure_genericPoint]; exact subset_closure rfl
  by_cases hξ : blowUpToBase Z D.genericPoint ∈ (Z.support : Set X)
  · exact notMem_support_controlledTransform_of_mem sX h hm hZ hZsnc hN D hξ (hsub hηD)
  · refine notMem_support_nonmonomialPart_of_notMem sX h hm hZ hZsnc hN D hD hξ ?_
    refine (mem_support_comap_iff (blowUpToBase Z) _ _).1 ?_
    by_contra hc
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support] at hc
    refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).1 ?_ (hsub hηD)
    exact top_le_iff.1 (hc ▸ stalk_mono (le_idealColon _ _) _)

/-- `π⁻¹_*N(I)` is the nonmonomial factor of a monomial decomposition of `π⁻¹_*(I, m)` with
respect to `π⁻¹_tot E`. -/
private theorem exists_isMonomialDecomposition_controlledTransform :
    ∃ A', IsMonomialDecomposition ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I
      (E.totalTransform Z) A' (controlledTransform Z (nonmonomialPart I E)) := by
  obtain ⟨A', hfin, hcomp, hA'⟩ :=
    exists_divisorIdeal_eq_comap_monomialPart_mul sX h hm hZ hZsnc hN
  refine ⟨A', hfin, hcomp, ?_, not_subset_support_controlledTransform sX h hm hZ hZsnc hN⟩
  rw [hA']
  exact birationalTransform_eq_comap_monomialPart_mul sX h hm hZ hZsnc hN

end Obligations

end MMP.Resolution.Proof_lem_kr3e_nonmonomial_part_of_transform

namespace MMP.Resolution

open MMP.Resolution.Proof_lem_kr3e_nonmonomial_part_of_transform in
/-- **The nonmonomial part of a birational transform** (Kollár 3.111, Step 1). Let `(X, I, E)` be
a triple, `m ≥ 1`, and `Z ⊆ X` a smooth closed subscheme having simple normal crossings with `E`
such that `ord_{Z_j} N(I) ≥ m` along every irreducible component `Z_j` of `Z`. Then
`ord_Z I ≥ m`, and with respect to `E' = π⁻¹_tot E`, `π : B_ZX → X`, the nonmonomial part of the
birational transform `π⁻¹_*(I, m)` is the controlled transform `π⁻¹_*N(I)`. -/
@[mmp "lem_kr3e_nonmonomial_part_of_transform"]
public theorem nonmonomialPart_birationalTransform {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsTriple sX I E) {m : ℕ} (hm : 1 ≤ m) {Z : X.IdealSheafData}
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZsnc : HasSNCWith E.E Z)
    (hN : OrderAlongGE (nonmonomialPart I E) (Z.support : Set X) m) :
    OrderAlongGE I (Z.support : Set X) m ∧
      nonmonomialPart ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I (E.totalTransform Z) =
        controlledTransform Z (nonmonomialPart I E) := by
  refine ⟨OrderAlongGE.of_le (le_idealColon _ _) hN, ?_⟩
  obtain ⟨A', hA'⟩ := exists_isMonomialDecomposition_controlledTransform sX h hm hZ hZsnc hN
  have h' := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) h hZsnc
  exact ((isMonomialDecomposition_iff _ h' A' _).mp hA').2.symm

end MMP.Resolution

end

/-!
### The induced blow-up sequence commutes with flat pull-back (Kollár, p. 146)

Let `A` be of finite type over a field, `i : X ↪ A` a closed subscheme which is a disjoint union
of varieties, and `𝐁` a blow-up sequence of `A`. Let `h_A : A' → A` be flat with `A'` of finite
type over a field, `X' = X ×_A A'` with projections `h : X' → X` and `i' : X' ↪ A'`, and assume
`X'` is a disjoint union of varieties. Then the sequence induced on `X'` by the pulled-back
ambient sequence `h_A^*𝐁` is the pull-back along `h` of the sequence induced on `X` by `𝐁`:
`𝓑𝓡_{h_A^*𝐁}(X' ⊆ A') = h^*𝓑𝓡_𝐁(X ⊆ A)`, once the latter is cut off at the length
`r_{X'} = max_{C'} j_{C'}` of the former.

Implementation notes:

A flat `h` maps the generic point of a connected component `C'` of `X'` to that of the component
`C` of `X` containing its image, and `j_{C'} = j_C`. The length of `h^*𝓑𝓡_𝐁(X ⊆ A)` is
`r_X = max_C j_C`, the maximum over all components of `X`, while `r_{X'}` only sees the components
met by `h`; the steps of index `≥ r_{X'}` of the pull-back have empty centres. The equality is
therefore stated with the pull-back truncated at `r_{X'}`; when `h` is surjective (e.g. `h_A`
faithfully flat) `r_{X'} ≥ r_X` and the truncation does nothing
(`MMP.Resolution.Kollar.embeddedResolutionLength_le_pullback`).
In general the steps of the pull-back past `r_{X'}` are empty blow-ups, so the two sequences
have the same reduction
(`MMP.Resolution.Kollar.reduction_embeddedResolutionSequence_pullback_of_flat_of_comm`).

The argument only uses the commutative square `i' ≫ h_A = h ≫ i` with `h_A` and `h` flat, never
that it is cartesian, so it is proved for any such square
(`MMP.Resolution.Kollar.embeddedResolutionSequence_pullback_of_flat_of_comm`); this covers other
models of `X ×_A A'`, such as `X ×_k L ↪ A ×_k L` for a field extension `L / k`.
-/

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution
open MMP.Resolution.ClosedBlowupSequence

namespace MMP.Resolution.Proof_lem_kr3f_br_flat_pullback

private theorem truncate_truncate {X : Scheme.{u}} (B : ClosedBlowupSequence X) (a b : ℕ) :
    (B.truncate a).truncate b = B.truncate (min a b) := by
  induction B generalizing a b with
  | nil _ => simp [truncate]
  | cons Z B ih =>
    cases a with
    | zero => simp [truncate]
    | succ a =>
      cases b with
      | zero => simp [truncate]
      | succ b => simp [truncate, ih, Nat.succ_min_succ]

/-- Along a flat `g`, the entry index of a set `S` for `g^*𝐁` is that of `g(S)` for `𝐁`. -/
private theorem entryIndexOfSet_pullback {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [Flat g] (S : Set Y),
      (B.pullback g).entryIndexOfSet S = B.entryIndexOfSet (g.base '' S) := by
  induction B with
  | nil _ => intro Y g _ S; rfl
  | cons Z B ih =>
    intro Y g _ S
    have : Flat (canonicalLift g Z) := Kollar.flat_canonicalLift g Z
    simp only [ClosedBlowupSequence.pullback, ClosedBlowupSequence.entryIndexOfSet]
    have hcond : (((Z.comap g).support : Set Y) ∩ S).Nonempty ↔
        ((Z.support : Set _) ∩ g.base '' S).Nonempty := by
      rw [Scheme.IdealSheafData.support_comap]
      constructor
      · exact fun ⟨y, hy, hyS⟩ => ⟨g.base y, hy, y, hyS, rfl⟩
      · rintro ⟨_, hx, y, hyS, rfl⟩
        exact ⟨y, hx, hyS⟩
    have hset : (canonicalLift g Z).base '' (blowUpToBase (Z.comap g) ⁻¹' S) =
        blowUpToBase Z ⁻¹' (g.base '' S) := by
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨_, hb, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase]
      · rintro ⟨y, hyS, hy⟩
        obtain ⟨b, hb1, hb2⟩ := Scheme.exists_preimage_of_isPullback
          (Kollar.isPullback_canonicalLift_of_flat g Z) y a hy
        exact ⟨b, by simpa [hb1] using hyS, hb2⟩
    by_cases h : ((Z.support : Set _) ∩ g.base '' S).Nonempty
    · rw [if_pos (hcond.mpr h), if_pos h]
    · rw [if_neg (mt hcond.mp h), if_neg h, ih, hset]

/-- An ideal sheaf is determined by its restrictions to the members of an open cover. -/
private theorem idealSheafData_ext_of_comap {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : ⨆ j, U j = ⊤) {I J : X.IdealSheafData}
    (h : ∀ j, I.comap (U j).ι = J.comap (U j).ι) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ j, (U j).toScheme.affineOpens)
    (fun w ↦ ⟨(U w.1).ι ''ᵁ w.2.1, w.2.2.image_of_isOpenImmersion _⟩) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := (U j).toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (⟨x, hj⟩ : U j)) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨j, ⟨W, hW⟩⟩, ⟨_, hxW, rfl⟩⟩
  · rintro ⟨j, W⟩
    have hI := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I (U j).ι W
    have hJ := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (U j).ι W
    rw [h j] at hI
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((U j).ι.appIso W).inv).2) (hI.symm.trans hJ)

/-- The push-forward of an ideal sheaf along the inclusion of a closed open `U` restricts to the
unit ideal on any open disjoint from `U`. -/
private theorem comap_map_eq_top_of_disjoint {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsClosed (U : Set X)) (hUV : Disjoint U V) [QuasiCompact U.ι]
    (K : U.toScheme.IdealSheafData) : (K.map U.ι).comap V.ι = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_map]
  ext x
  simp only [Closeds.coe_preimage, Closeds.coe_closure, Set.mem_preimage, Closeds.coe_bot,
    Set.mem_empty_iff_false, iff_false]
  intro hx
  have h1 : closure (U.ι.base '' (K.support : Set U)) ⊆ U := by
    refine hU.closure_subset_iff.mpr ?_
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have h2 := h1 hx
  have h3 : V.ι x ∈ U ⊓ V := ⟨h2, by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩⟩
  rw [hUV.eq_bot] at h3
  exact h3

/-- The push-forward of an ideal sheaf along the inclusion of a closed open subscheme commutes with
pull-back. -/
private theorem comap_map_eq_map_comap {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) {U : Y.Opens}
    (hU : IsClosed (U : Set Y)) [QuasiCompact U.ι] {U' : Y'.Opens} (hU' : U' = q ⁻¹ᵁ U)
    [QuasiCompact U'.ι] (K : U.toScheme.IdealSheafData) :
    (K.map U.ι).comap q = (K.comap (q.resLE U U' hU'.le)).map U'.ι := by
  subst hU'
  let V : Y.Opens := ⟨(U : Set Y)ᶜ, hU.isOpen_compl⟩
  have hUV : Disjoint U V := by
    rw [disjoint_iff]; ext x; simp [V]
  have hUV' : Disjoint (q ⁻¹ᵁ U) (q ⁻¹ᵁ V) := by
    rw [disjoint_iff]; ext x; simp [V]
  refine idealSheafData_ext_of_comap (fun j : Bool ↦ bif j then q ⁻¹ᵁ U else q ⁻¹ᵁ V) ?_ ?_
  · rw [iSup_bool_eq, eq_top_iff]
    intro x _
    by_cases hx : q x ∈ U
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (_ | _)
    · dsimp only [cond_false]
      rw [comap_map_eq_top_of_disjoint (hU.preimage q.continuous) hUV',
        ← Scheme.IdealSheafData.comap_comp, ← Scheme.Hom.resLE_comp_ι q (le_refl (q ⁻¹ᵁ V)),
        Scheme.IdealSheafData.comap_comp, comap_map_eq_top_of_disjoint hU hUV,
        Scheme.IdealSheafData.comap_top]
    · dsimp only [cond_true]
      rw [ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion,
        ← Scheme.IdealSheafData.comap_comp, ← Scheme.Hom.resLE_comp_ι q (le_refl (q ⁻¹ᵁ U)),
        Scheme.IdealSheafData.comap_comp, ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion]

private theorem quasiCompact_ι {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y] (U : Y.Opens) :
    QuasiCompact U.ι := by
  have : NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set Y)
  infer_instance

private theorem isCartierOver_resLE' {Y A' : Scheme.{u}} [hY : AlgebraicGeometry.IsNoetherian Y]
    (U : Y.Opens) (h : U.toScheme ⟶ A')
    (Z : A'.IdealSheafData) (U' : (blowUp ((Z.comap h).map U.ι)).Opens)
    (hle : U' ≤ blowUpToBase ((Z.comap h).map U.ι) ⁻¹ᵁ U) :
    Stacks.Blowup.IsCartierOver Z
      (Over.mk ((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle ≫ h)) := by
  have hq : QuasiCompact U.ι := quasiCompact_ι U
  have h1 : (Z.comap h) = ((Z.comap h).map U.ι).comap U.ι :=
    (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion U.ι (Z.comap h)).symm
  change Stacks.Divisors.IsEffectiveCartierDivisor
    (Z.comap (((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle) ≫ h))
  rw [Scheme.IdealSheafData.comap_comp,
    congrArg (fun J => J.comap ((blowUpToBase ((Z.comap h).map U.ι)).resLE U U' hle)) h1,
    ← Scheme.IdealSheafData.comap_comp, Scheme.Hom.resLE_comp_ι,
    Scheme.IdealSheafData.comap_comp]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) _

private theorem isCartierOver_of_eq_comap {Y Y' : Scheme.{u}} (q : Y' ⟶ Y)
    {W : Y.IdealSheafData} {W' : Y'.IdealSheafData} (e : W' = W.comap q) :
    Stacks.Blowup.IsCartierOver W (Over.mk (blowUpToBase W' ≫ q)) := by
  subst e; exact isCartierOver_blowUpToBase_comp q W

private theorem flat_blowUpLift_of_eq_comap {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [Flat q]
    {W : Y.IdealSheafData} {W' : Y'.IdealSheafData} (e : W' = W.comap q) :
    Flat (blowUpLift W (blowUpToBase W' ≫ q) (isCartierOver_of_eq_comap q e)) := by
  subst e; exact Kollar.flat_canonicalLift q W

private theorem cons_comap_pullback {Y Y' : Scheme.{u}} (q : Y' ⟶ Y)
    {W : Y.IdealSheafData} {W' : Y'.IdealSheafData} (e : W' = W.comap q)
    (S : ClosedBlowupSequence (blowUp W)) :
    ClosedBlowupSequence.cons (W.comap q) (S.pullback (canonicalLift q W)) =
      .cons W'
        (S.pullback (blowUpLift W (blowUpToBase W' ≫ q) (isCartierOver_of_eq_comap q e))) := by
  subst e; rfl

open ClosedBlowupSequence in
private theorem embeddedAux_pullback {X X' : Scheme.{u}} (hX : X' ⟶ X) (act : ℕ → X.Opens)
    (act' : ℕ → X'.Opens) (hact : ∀ m, act' m = hX ⁻¹ᵁ act m)
    (hcl : ∀ m, IsClosed (act m : Set X)) {A₀ : Scheme.{u}} (C : ClosedBlowupSequence A₀) :
    ∀ {A₀' : Scheme.{u}} (g : A₀' ⟶ A₀) [Flat g] (n : ℕ) (Y Y' : Scheme.{u})
      [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Y']
      (p : Y ⟶ X) (p' : Y' ⟶ X') (q : Y' ⟶ Y) [Flat q]
      (_ : p' ≫ hX = q ≫ p) (U : Y.Opens) (_ : IsClosed (U : Set Y)) (U' : Y'.Opens)
      (hU' : U' = q ⁻¹ᵁ U) (h : U.toScheme ⟶ A₀) (h' : U'.toScheme ⟶ A₀')
      (_ : h' ≫ g = q.resLE U U' hU'.le ≫ h),
      embeddedAux act' (C.pullback g) n Y' p' U' h' = (embeddedAux act C n Y p U h).pullback q := by
  induction C with
  | nil _ => intros; rfl
  | cons Z C ih =>
    intro A₀' g _ n Y Y' _ _ p p' q _ hpq U hU U' hU' h h' hh
    have := quasiCompact_ι U
    have := quasiCompact_ι U'
    show embeddedAux act' (cons (Z.comap g) (C.pullback (canonicalLift g Z))) n Y' p' U' h' = _
    rw [embeddedAux.eq_2, embeddedAux.eq_2, dif_pos (isCartierOver_resLE' U' h' _ _ inf_le_left),
      dif_pos (isCartierOver_resLE' U h _ _ inf_le_left), ClosedBlowupSequence.pullback]
    have hW : ((Z.comap g).comap h').map U'.ι = ((Z.comap h).map U.ι).comap q := by
      rw [comap_map_eq_map_comap q hU hU', ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, hh]
    rw [cons_comap_pullback q hW]
    congr 1
    have := flat_blowUpLift_of_eq_comap q hW
    have := Kollar.flat_canonicalLift g Z
    have := Kollar.isNoetherian_blowUp' ((Z.comap h).map U.ι)
    have := Kollar.isNoetherian_blowUp' (((Z.comap g).comap h').map U'.ι)
    set W := (Z.comap h).map U.ι
    set W' := ((Z.comap g).comap h').map U'.ι
    set q₁ := blowUpLift W (blowUpToBase W' ≫ q) (isCartierOver_of_eq_comap q hW)
    have hq₁ : q₁ ≫ blowUpToBase W = blowUpToBase W' ≫ q := blowUpLift_comp _ _ _
    have hq₁x : ∀ x, blowUpToBase W (q₁ x) = q (blowUpToBase W' x) := fun x ↦ by
      rw [← Scheme.Hom.comp_apply, hq₁, Scheme.Hom.comp_apply]
    refine ih (canonicalLift g Z) (n + 1) _ _ _ _ q₁ ?_ _ ?_ _ ?_ _ _ ?_
    · rw [Category.assoc, hpq, ← Category.assoc, ← hq₁, Category.assoc]
    · exact (hU.preimage (blowUpToBase W).continuous).inter
        ((hcl _).preimage (blowUpToBase W ≫ p).continuous)
    · have hmem : ∀ y, y ∈ U' ↔ q y ∈ U := fun y ↦ by rw [hU']; rfl
      rw [hact]
      ext x
      have hpx : hX (p' (blowUpToBase W' x)) = p (q (blowUpToBase W' x)) := by
        rw [← Scheme.Hom.comp_apply, hpq, Scheme.Hom.comp_apply]
      simp [hmem]
      rw [show (blowUpToBase ((Z.comap h).map U.ι)) (q₁ x) = q ((blowUpToBase W') x) from hq₁x x,
        ← hpx]
    · have hc' := isCartierOver_resLE' U' h' (Z.comap g)
        (blowUpToBase W' ⁻¹ᵁ U' ⊓ (blowUpToBase W' ≫ p') ⁻¹ᵁ act' (n + 1)) inf_le_left
      have hf : Stacks.Blowup.IsCartierOver Z (Over.mk ((blowUpToBase W').resLE U'
          (blowUpToBase W' ⁻¹ᵁ U' ⊓ (blowUpToBase W' ≫ p') ⁻¹ᵁ act' (n + 1)) inf_le_left ≫
            h' ≫ g)) := by
        change Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (_ ≫ h' ≫ g))
        rw [← Category.assoc, Scheme.IdealSheafData.comap_comp]
        exact hc'
      refine (blowUpLift_unique Z _ hf _ ?_).trans (blowUpLift_unique Z _ hf _ ?_).symm
      · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp,
          Category.assoc]
      · rw [Category.assoc, blowUpLift_comp, hh, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono U.ι]
        simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
        exact congrArg (fun k ↦ _ ≫ k) hq₁

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- In a noetherian quasi-sober space whose irreducible components are pairwise disjoint, every
connected component is closed and open and has a generic point. -/
private theorem connectedComponent_isClopen_and_generic [NoetherianSpace T] [QuasiSober T]
    (hd : ∀ C ∈ irreducibleComponents T, ∀ C' ∈ irreducibleComponents T, C ≠ C' → Disjoint C C')
    (x : T) : IsClopen (connectedComponent x) ∧
      ∃ η ∈ connectedComponent x, connectedComponent x ⊆ closure {η} := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hxC : x ∈ C := hxC rfl
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hcompl : Cᶜ = ⋃ C' ∈ {C' ∈ irreducibleComponents T | C' ≠ C}, C' := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨C', hC', hyC'⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      exact ⟨C', ⟨hC', fun h ↦ hy (h ▸ hyC' rfl)⟩, hyC' rfl⟩
    · rintro ⟨C', ⟨hC', hne⟩, hyC'⟩ hyC
      exact Set.disjoint_left.mp (hd C' hC' C hC hne) hyC' hyC
  have hCop : IsOpen C := by
    rw [← isClosed_compl_iff, hcompl]
    exact ((NoetherianSpace.finite_irreducibleComponents).subset fun _ h ↦ h.1).isClosed_biUnion
      fun C' h ↦ isClosed_of_mem_irreducibleComponents C' h.1
  have hcc : connectedComponent x = C :=
    (IsClopen.connectedComponent_subset (show IsClopen C from ⟨hCcl, hCop⟩) hxC).antisymm
      ((IsPreirreducible.isPreconnected hC.1.2).subset_connectedComponent hxC)
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 hCcl
  rw [hcc]
  exact ⟨⟨hCcl, hCop⟩, η, hη.mem, hη.symm.subset⟩

/-- Two points whose closures both contain the connected component they lie in are equal. -/
private theorem eq_of_connectedComponent_subset_closure [T0Space T] {y η₁ η₂ : T}
    (h₁ : η₁ ∈ connectedComponent y) (h₁' : connectedComponent y ⊆ closure {η₁})
    (h₂ : η₂ ∈ connectedComponent y) (h₂' : connectedComponent y ⊆ closure {η₂}) : η₁ = η₂ := by
  have hc₁ : closure {η₁} ⊆ connectedComponent y :=
    isClosed_connectedComponent.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h₁)
  have hc₂ : closure {η₂} ⊆ connectedComponent y :=
    isClosed_connectedComponent.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h₂)
  exact ((specializes_iff_mem_closure.mpr (h₁' h₂)).antisymm
    (specializes_iff_mem_closure.mpr (h₂' h₁))).eq

/-- A generalizing continuous map sends a generic point of a connected component to a generic
point of a connected component, provided the components of the target have generic points. -/
private theorem connectedComponent_subset_closure_image {T' : Type*} [TopologicalSpace T']
    [T0Space T'] {f : T' → T} (hf : Continuous f) (hg : GeneralizingMap f)
    (hT : ∀ y : T, ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η})
    {η' : T'} (hη' : connectedComponent η' ⊆ closure {η'}) :
    connectedComponent (f η') ⊆ closure {f η'} := by
  obtain ⟨η, hη, hηc⟩ := hT (f η')
  obtain ⟨ξ, hξ, hξη⟩ := hg (specializes_iff_mem_closure.mpr (hηc mem_connectedComponent))
  have hξc : ξ ∈ connectedComponent η' :=
    isPreconnected_singleton.closure.subset_connectedComponent
      (specializes_iff_mem_closure.mp hξ) (subset_closure rfl)
  have : ξ = η' := (hξ.antisymm (specializes_iff_mem_closure.mpr (hη' hξc))).eq
  subst this
  rw [hξη]
  rwa [connectedComponent_eq hη] at hηc

end Topology

private theorem isOpen_of_forall_connectedComponent_subset {T : Type*} [TopologicalSpace T]
    (hcl : ∀ x : T, IsOpen (connectedComponent x)) {S : Set T}
    (hS : ∀ x ∈ S, connectedComponent x ⊆ S) : IsOpen S :=
  isOpen_iff_forall_mem_open.mpr fun x hx ↦ ⟨_, hS x hx, hcl x, mem_connectedComponent⟩

section Embedded

variable {X X' A A' : Scheme.{u}} (i : X ⟶ A) (hA : A' ⟶ A) (f : X' ⟶ X) (i' : X' ⟶ A')
  (hsq : i' ≫ hA = f ≫ i) (B : ClosedBlowupSequence A)

include hsq in
private theorem componentEntryIndex_pullback [Flat hA] [Flat f]
    (hT : ∀ y : X, ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η})
    (hT' : ∀ y : X', ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η}) (x' : X') :
    componentEntryIndex (B.pullback hA) i' x' = componentEntryIndex B i (f x') := by
  unfold componentEntryIndex
  rw [dif_pos (hT' x'), dif_pos (hT (f x'))]
  obtain ⟨hη'1, hη'2⟩ := (hT' x').choose_spec
  obtain ⟨hη1, hη2⟩ := (hT (f x')).choose_spec
  have hcc : connectedComponent (hT' x').choose = connectedComponent x' :=
    (connectedComponent_eq hη'1).symm
  have hmem : f (hT' x').choose ∈ connectedComponent (f x') :=
    f.continuous.image_connectedComponent_subset x' ⟨_, hη'1, rfl⟩
  have h1 := connectedComponent_subset_closure_image f.continuous (Flat.generalizingMap f) hT
    (by rw [hcc]; exact hη'2)
  rw [← connectedComponent_eq hmem] at h1
  have heq : f (hT' x').choose = (hT (f x')).choose :=
    eq_of_connectedComponent_subset_closure hmem h1 hη1 hη2
  rw [← heq, ClosedBlowupSequence.entryIndex, ClosedBlowupSequence.entryIndex,
    entryIndexOfSet_pullback, Set.image_singleton, ← Scheme.Hom.comp_apply, hsq,
    Scheme.Hom.comp_apply]

include hsq in
private theorem activeLocus_pullback [Flat hA] [Flat f]
    (hT : ∀ y : X, IsClopen (connectedComponent y) ∧
      ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η})
    (hT' : ∀ y : X', ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η}) (m : ℕ) :
    activeLocus (B.pullback hA) i' m = f ⁻¹ᵁ activeLocus B i m ∧
      IsClosed (activeLocus B i m : Set X) := by
  have hc : ∀ x, ∀ y ∈ connectedComponent x,
      componentEntryIndex B i y = componentEntryIndex B i x := by
    intro x y hy
    unfold componentEntryIndex
    rw [dif_pos (hT x).2, dif_pos (hT y).2]
    obtain ⟨hy1, hy2⟩ := (hT y).2.choose_spec
    obtain ⟨hx1, hx2⟩ := (hT x).2.choose_spec
    have hcy := connectedComponent_eq hy
    rw [eq_of_connectedComponent_subset_closure hy1 hy2 (hcy.subset hx1)
      (hcy.symm.subset.trans hx2)]
  have hop : ∀ x : X, IsOpen (connectedComponent x) := fun x ↦ (hT x).1.isOpen
  have hS : IsOpen {x : X | m < componentEntryIndex B i x} :=
    isOpen_of_forall_connectedComponent_subset hop fun x hx y hy ↦ by
      simpa [Set.mem_setOf_eq, hc x y hy] using hx
  have hSc : IsOpen {x : X | m < componentEntryIndex B i x}ᶜ :=
    isOpen_of_forall_connectedComponent_subset hop fun x hx y hy ↦ by
      simpa [Set.mem_setOf_eq, hc x y hy] using hx
  have hS' : IsOpen {x : X' | m < componentEntryIndex (B.pullback hA) i' x} := by
    simp_rw [componentEntryIndex_pullback i hA f i' hsq B (fun y ↦ (hT y).2) hT']
    exact hS.preimage f.continuous
  unfold activeLocus
  rw [dif_pos hS, dif_pos hS']
  refine ⟨?_, isOpen_compl_iff.mp hSc⟩
  ext x
  simp [componentEntryIndex_pullback i hA f i' hsq B (fun y ↦ (hT y).2) hT']

include hsq in
private theorem embeddedResolutionLength_pullback_le [Flat hA] [Flat f]
    (hT : ∀ y : X, ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η}) :
    embeddedResolutionLength (B.pullback hA) i' ≤ embeddedResolutionLength B i := by
  unfold embeddedResolutionLength
  rcases Set.eq_empty_or_nonempty
      {j | ∃ η : X', connectedComponent η ⊆ closure {η} ∧ j = (B.pullback hA).entryIndex (i' η)}
    with he | hne
  · rw [he, csSup_empty]; exact bot_le
  refine csSup_le_csSup ⟨B.length, ?_⟩ hne ?_
  · rintro j ⟨η, -, rfl⟩
    exact B.entryIndex_le_length _
  · rintro j ⟨η', hη', rfl⟩
    refine ⟨f η', connectedComponent_subset_closure_image f.continuous (Flat.generalizingMap f)
      hT hη', ?_⟩
    rw [ClosedBlowupSequence.entryIndex, ClosedBlowupSequence.entryIndex,
      entryIndexOfSet_pullback, Set.image_singleton, ← Scheme.Hom.comp_apply, hsq,
      Scheme.Hom.comp_apply]

end Embedded

private theorem isNoetherian_of_isDisjointUnionOfVarieties {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (hX : IsDisjointUnionOfVarieties s) :
    AlgebraicGeometry.IsNoetherian X := by
  obtain ⟨_, _, -⟩ := hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  exact {}

/-! ### The tail of empty blow-ups -/

/-- The push-forward of any ideal sheaf along the inclusion of the empty open is the unit
ideal. -/
private theorem map_ι_eq_top_of_eq_bot {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    {U : Y.Opens} (hU : U = ⊥) (K : U.toScheme.IdealSheafData) : K.map U.ι = ⊤ := by
  have := quasiCompact_ι U
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_map]
  have : U.ι.base '' (K.support : Set U) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro _ ⟨y, -, rfl⟩
    have hy : U.ι y ∈ Set.range U.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hy
    have h0 : (U : Set Y) = ∅ := by rw [hU]; rfl
    exact (Set.ext_iff.mp h0 _).mp hy
  apply Closeds.ext
  rw [Closeds.coe_closure, this, closure_empty]
  rfl

/-- Once the active loci are empty from step `N` on, every centre of `embeddedAux` from step `N`
on is empty. -/
private theorem isEmptyAt_embeddedAux {X : Scheme.{u}} (act : ℕ → X.Opens) (N : ℕ)
    (hN : ∀ m, N ≤ m → act m = ⊥) {A₀ : Scheme.{u}} (C : ClosedBlowupSequence A₀) :
    ∀ (n : ℕ) (Y : Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y] (p : Y ⟶ X) (U : Y.Opens)
      (h : U.toScheme ⟶ A₀), (N ≤ n → U = ⊥) → ∀ k, N ≤ n + k →
        k < (embeddedAux act C n Y p U h).length →
          Kollar.IsEmptyAt (embeddedAux act C n Y p U h) k := by
  induction C with
  | nil _ => intro n Y _ p U h _ k _ hk; simp [embeddedAux, length] at hk
  | cons Z C ih =>
    intro n Y _ p U h hU k hk hlen
    rw [embeddedAux.eq_2, dif_pos (isCartierOver_resLE' U h Z _ inf_le_left)] at hlen ⊢
    cases k with
    | zero => exact map_ι_eq_top_of_eq_bot (hU (by omega)) _
    | succ k =>
      have := Kollar.isNoetherian_blowUp' ((Z.comap h).map U.ι)
      refine ih (n + 1) _ _ _ _ ?_ k (by omega) (by simpa [length] using hlen)
      intro hn
      rw [hN _ hn, Scheme.Hom.preimage_bot, inf_bot_eq]

/-- If every centre of `S` from step `a` on is empty, truncating `S` at `a` does not change its
pull-back with empty blow-ups deleted. -/
private theorem pullbackReduced_truncate_of_isEmptyAt {X : Scheme.{u}}
    (S : ClosedBlowupSequence X) : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) (a : ℕ),
      (∀ k, a ≤ k → k < S.length → Kollar.IsEmptyAt S k) →
        (S.truncate a).pullbackReduced g = S.pullbackReduced g := by
  induction S with
  | nil _ => intro Y g a _; cases a <;> rfl
  | cons Z S ih =>
    intro Y g a ha
    have ha' : ∀ b, a ≤ b + 1 → ∀ k, b ≤ k → k < S.length → Kollar.IsEmptyAt S k :=
      fun b hb k hk hkl => ha (k + 1) (by omega) (by simp [length]; omega)
    cases a with
    | zero =>
      have hZ : Z = ⊤ := ha 0 le_rfl (by simp [length])
      have hZ' : Z.comap g = ⊤ := by rw [hZ]; exact Scheme.IdealSheafData.comap_top _
      simp only [Kollar.truncate_zero, pullbackReduced, hZ', dite_true]
      rw [← ih _ 0 (ha' 0 (by omega)), Kollar.truncate_zero]
      rfl
    | succ a =>
      by_cases hZ : Z.comap g = ⊤
      · simp only [truncate, pullbackReduced, hZ, dite_true]
        rw [ih _ a (ha' a le_rfl)]
      · simp only [truncate, pullbackReduced, hZ, dite_false]
        rw [ih _ a (ha' a le_rfl)]

/-- No component of `X` is active from step `r_X` on. -/
private theorem activeLocus_eq_bot {X A : Scheme.{u}} (B : ClosedBlowupSequence A) (i : X ⟶ A)
    (hT : ∀ y : X, ∃ η ∈ connectedComponent y, connectedComponent y ⊆ closure {η}) (m : ℕ)
    (hm : embeddedResolutionLength B i ≤ m) : activeLocus B i m = ⊥ := by
  have hle : ∀ x, componentEntryIndex B i x ≤ embeddedResolutionLength B i := by
    intro x
    unfold componentEntryIndex
    rw [dif_pos (hT x)]
    obtain ⟨h1, h2⟩ := (hT x).choose_spec
    refine le_csSup ⟨B.length, ?_⟩ ⟨(hT x).choose, ?_, rfl⟩
    · rintro j ⟨η, -, rfl⟩
      exact B.entryIndex_le_length _
    · rw [← connectedComponent_eq h1]; exact h2
  unfold activeLocus
  split_ifs
  · ext x
    simp only [Opens.coe_mk, Set.mem_setOf_eq, Opens.coe_bot, Set.mem_empty_iff_false,
      iff_false, not_lt]
    exact (hle x).trans hm
  · rfl

end MMP.Resolution.Proof_lem_kr3f_br_flat_pullback

namespace MMP.Resolution.Kollar

open MMP.Resolution.Proof_lem_kr3f_br_flat_pullback in
/-- **The induced sequence commutes with flat pull-back along a commutative square.** Let
`i : X ⟶ A` and `i' : X' ⟶ A'` be morphisms from disjoint unions of varieties over fields `k`,
`k'`, and `i' ≫ h_A = f ≫ i` a commutative square with `h_A` and `f` flat. Then
`𝓑𝓡_{h_A^*𝐁}(X' ⊆ A')` is `f^*𝓑𝓡_𝐁(X ⊆ A)` truncated at the length of the former. The square
need not be cartesian. -/
public theorem embeddedResolutionSequence_pullback_of_flat_of_comm {k k' : Type u} [Field k]
    [Field k'] {X A X' A' : Scheme.{u}} (sA : A ⟶ Spec (.of k)) (i : X ⟶ A)
    (hX : IsDisjointUnionOfVarieties (i ≫ sA)) (B : ClosedBlowupSequence A)
    (sA' : A' ⟶ Spec (.of k')) (hA : A' ⟶ A) [Flat hA] (f : X' ⟶ X) [Flat f] (i' : X' ⟶ A')
    (hsq : i' ≫ hA = f ≫ i) (hX' : IsDisjointUnionOfVarieties (i' ≫ sA')) :
    embeddedResolutionSequence (B.pullback hA) i' =
      ((embeddedResolutionSequence B i).pullback f).truncate
        (embeddedResolutionLength (B.pullback hA) i') := by
  have := isNoetherian_of_isDisjointUnionOfVarieties hX
  have := isNoetherian_of_isDisjointUnionOfVarieties hX'
  have hT := connectedComponent_isClopen_and_generic hX.2.2.2.2
  have hT' := fun y ↦ (connectedComponent_isClopen_and_generic hX'.2.2.2.2 y).2
  have hact := activeLocus_pullback i hA f i' hsq B hT hT'
  have key := embeddedAux_pullback f (activeLocus B i) (activeLocus (B.pullback hA) i')
    (fun m ↦ (hact m).1) (fun m ↦ (hact m).2) B hA 0 X X' (𝟙 X) (𝟙 X') f (by simp)
    (activeLocus B i 0) (hact 0).2 _ (hact 0).1 ((activeLocus B i 0).ι ≫ i)
    ((activeLocus (B.pullback hA) i' 0).ι ≫ i')
    (by rw [Category.assoc, hsq, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ (hact 0).1.le,
      Category.assoc])
  unfold embeddedResolutionSequence
  rw [key, ← Kollar.pullback_truncate,
    MMP.Resolution.Proof_lem_kr3f_br_flat_pullback.truncate_truncate,
    min_eq_right (embeddedResolutionLength_pullback_le i hA f i' hsq B fun y ↦ (hT y).2)]

open MMP.Resolution.Proof_lem_kr3f_br_flat_pullback in
/-- **The induced sequence commutes with flat pull-back, up to empty blow-ups.** For a
commutative square `i' ≫ h_A = f ≫ i` with `h_A` and `f` flat, and `X`, `X'` disjoint unions of
varieties, `(𝓑𝓡_{h_A^*𝐁}(X' ⊆ A'))^red = (f^*𝓑𝓡_𝐁(X ⊆ A))^red`. The square need not be
cartesian, nor `f` surjective. -/
public theorem reduction_embeddedResolutionSequence_pullback_of_flat_of_comm {k k' : Type u}
    [Field k] [Field k'] {X A X' A' : Scheme.{u}} (sA : A ⟶ Spec (.of k)) (i : X ⟶ A)
    (hX : IsDisjointUnionOfVarieties (i ≫ sA)) (B : ClosedBlowupSequence A)
    (sA' : A' ⟶ Spec (.of k')) (hA : A' ⟶ A) [Flat hA] (f : X' ⟶ X) [Flat f] (i' : X' ⟶ A')
    (hsq : i' ≫ hA = f ≫ i) (hX' : IsDisjointUnionOfVarieties (i' ≫ sA')) :
    (embeddedResolutionSequence (B.pullback hA) i').reduction =
      ((embeddedResolutionSequence B i).pullback f).reduction := by
  have := isNoetherian_of_isDisjointUnionOfVarieties hX
  have := isNoetherian_of_isDisjointUnionOfVarieties hX'
  have hT := connectedComponent_isClopen_and_generic hX.2.2.2.2
  have hT' := fun y ↦ (connectedComponent_isClopen_and_generic hX'.2.2.2.2 y).2
  have hact := activeLocus_pullback i hA f i' hsq B hT hT'
  set act := activeLocus B i
  set act' := activeLocus (B.pullback hA) i'
  set S := embeddedAux act' (B.pullback hA) 0 X' (𝟙 _) (act' 0) ((act' 0).ι ≫ i')
  have key : S = (embeddedAux act B 0 X (𝟙 X) (act 0) ((act 0).ι ≫ i)).pullback f :=
    embeddedAux_pullback f act act' (fun m ↦ (hact m).1) (fun m ↦ (hact m).2) B hA 0 X X'
      (𝟙 X) (𝟙 _) f (by simp) (act 0) (hact 0).2 _ (hact 0).1 ((act 0).ι ≫ i)
      ((act' 0).ι ≫ i')
      (by rw [Category.assoc, hsq, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι _ (hact 0).1.le,
        Category.assoc])
  set r' := embeddedResolutionLength (B.pullback hA) i'
  have hr : r' ≤ embeddedResolutionLength B i :=
    embeddedResolutionLength_pullback_le i hA f i' hsq B fun y ↦ (hT y).2
  have hempty : ∀ n, r' ≤ n → n < S.length → Kollar.IsEmptyAt S n :=
    fun n hn hnl ↦ isEmptyAt_embeddedAux act' r' (fun m ↦ activeLocus_eq_bot _ i' hT' m) _ 0 X'
      (𝟙 _) (act' 0) _ (activeLocus_eq_bot _ i' hT' 0) n (by omega) hnl
  have hS : (embeddedResolutionSequence B i).pullback f =
      S.truncate (embeddedResolutionLength B i) := by
    rw [key, Kollar.pullback_truncate]; rfl
  rw [hS]
  exact (pullbackReduced_truncate_of_isEmptyAt S _ r' hempty).trans
    (pullbackReduced_truncate_of_isEmptyAt S _ _ fun n hn ↦ hempty n (hr.trans hn)).symm

open MMP.Resolution.Proof_lem_kr3f_br_flat_pullback in
/-- Along a flat surjective `f` in a commutative square `i' ≫ h_A = f ≫ i`, the length `r_X` of
the sequence induced on `X` is at most the length `r_{X'}` of the sequence induced on `X'`; hence
the truncation in `embeddedResolutionSequence_pullback_of_flat_of_comm` does nothing. -/
public theorem embeddedResolutionLength_le_pullback {k k' : Type u} [Field k] [Field k']
    {X A X' A' : Scheme.{u}} (sA : A ⟶ Spec (.of k)) (i : X ⟶ A)
    (hX : IsDisjointUnionOfVarieties (i ≫ sA)) (B : ClosedBlowupSequence A)
    (sA' : A' ⟶ Spec (.of k')) (hA : A' ⟶ A) [Flat hA] (f : X' ⟶ X) [Flat f] [Surjective f]
    (i' : X' ⟶ A') (hsq : i' ≫ hA = f ≫ i) (hX' : IsDisjointUnionOfVarieties (i' ≫ sA')) :
    embeddedResolutionLength B i ≤ embeddedResolutionLength (B.pullback hA) i' := by
  have := isNoetherian_of_isDisjointUnionOfVarieties hX
  have := isNoetherian_of_isDisjointUnionOfVarieties hX'
  have hT y := (connectedComponent_isClopen_and_generic hX.2.2.2.2 y).2
  have hT' y := (connectedComponent_isClopen_and_generic hX'.2.2.2.2 y).2
  unfold embeddedResolutionLength
  rcases Set.eq_empty_or_nonempty
      {j | ∃ η : X, connectedComponent η ⊆ closure {η} ∧ j = B.entryIndex (i η)}
    with he | hne
  · rw [he, csSup_empty]; exact bot_le
  refine csSup_le_csSup ⟨(B.pullback hA).length, ?_⟩ hne ?_
  · rintro j ⟨η, -, rfl⟩
    exact (B.pullback hA).entryIndex_le_length _
  · rintro j ⟨η, hη, rfl⟩
    obtain ⟨x', hx'⟩ := f.surjective η
    obtain ⟨η', hη'1, hη'2⟩ := hT' x'
    have hcc : connectedComponent η' = connectedComponent x' := (connectedComponent_eq hη'1).symm
    have hη'c : connectedComponent η' ⊆ closure {η'} := hcc ▸ hη'2
    have h1 := connectedComponent_subset_closure_image f.continuous (Flat.generalizingMap f) hT
      hη'c
    have hmem : f η' ∈ connectedComponent η :=
      hx' ▸ f.continuous.image_connectedComponent_subset x' ⟨_, hη'1, rfl⟩
    rw [← connectedComponent_eq hmem] at h1
    have heq : f η' = η :=
      eq_of_connectedComponent_subset_closure hmem h1 mem_connectedComponent hη
    refine ⟨η', hη'c, ?_⟩
    rw [ClosedBlowupSequence.entryIndex, ClosedBlowupSequence.entryIndex,
      entryIndexOfSet_pullback, Set.image_singleton, ← Scheme.Hom.comp_apply, hsq,
      Scheme.Hom.comp_apply, heq]

/-- **The induced sequence commutes with flat pull-back** (Kollár p. 146): for `A` of finite type
over `k`, a closed subscheme `i : X ↪ A` which is a disjoint union of varieties, a blow-up sequence
`𝐁` of `A`, and a flat `h_A : A' → A` with `A'` of finite type over `k'` such that
`X' = X ×_A A'` is a disjoint union of varieties, `𝓑𝓡_{h_A^*𝐁}(X' ⊆ A')` is the pull-back
`h^*𝓑𝓡_𝐁(X ⊆ A)` along `h = pullback.fst i h_A`, truncated at the length `r_{X'}` of the former. -/
@[mmp "lem_kr3f_br_flat_pullback"]
public theorem embeddedResolutionSequence_pullback_of_flat {k k' : Type u} [Field k] [Field k']
    {X A A' : Scheme.{u}} (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    (i : X ⟶ A) [IsClosedImmersion i] (hX : IsDisjointUnionOfVarieties (i ≫ sA))
    (B : ClosedBlowupSequence A) (sA' : A' ⟶ Spec (.of k')) [LocallyOfFiniteType sA']
    [QuasiCompact sA'] (hA : A' ⟶ A) [Flat hA]
    (hX' : IsDisjointUnionOfVarieties (Limits.pullback.snd i hA ≫ sA')) :
    embeddedResolutionSequence (B.pullback hA) (Limits.pullback.snd i hA) =
      ((embeddedResolutionSequence B i).pullback (Limits.pullback.fst i hA)).truncate
        (embeddedResolutionLength (B.pullback hA) (Limits.pullback.snd i hA)) :=
  embeddedResolutionSequence_pullback_of_flat_of_comm sA i hX B sA' hA _ _
    Limits.pullback.condition.symm hX'

end MMP.Resolution.Kollar

end
