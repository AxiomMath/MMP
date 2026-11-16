module

public import MMP.RingTheory.Presentation.CoveringPresentation
public import MMP.AlgebraicGeometry.Variety.SingularLocus
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.FunctionFieldMap
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain

/-!
# A proper morphism of varieties of the same dimension is generically a hypersurface covering

Let `f : V → W` be a proper surjective morphism of varieties of the same dimension over a field
`K` of characteristic zero. Then there is a nonempty affine open `U ⊆ W` such that

* `U` and `f⁻¹(U)` consist of regular points;
* `f⁻¹(U)` is affine and `f⁻¹(U) → U` is finite;
* the ring map `Γ(U) → Γ(f⁻¹ U)` has a covering presentation
  (`MMP.GenericCovering.CoveringPresentation`) with nonzero conductor element and
  nonzero discriminant-type element `δ`, whose polynomial has degree `deg(V/W)`.

The only point of `V` over the generic point `η_W` of `W` is the generic point `η_V`: if
`f(x) = η_W`, then `f` maps the closure of `x` onto `W`, so `dim W ≤ dim \overline{x} ≤ dim V`,
which forces `\overline{x} = V`. Hence `f` is quasi-finite at `η_V`, and the image under the
closed map `f` of the locus where `f` is not quasi-finite does not contain `η_W`; nor does the
image of the singular locus of `V`, since `η_V` is regular. Off these closed sets and the singular
locus of `W`, `f` is proper and quasi-finite, hence finite (Zariski's main theorem). The covering
presentation of the finite extension `Γ(U) ⊆ Γ(f⁻¹ U)` comes from
`MMP.GenericCovering.exists_coveringPresentation`, and its degree is
`[R(V) : R(W)] = deg(V/W)`.

## Main results

* `MMP.GenericCovering.eq_genericPoint_of_apply_eq_genericPoint`: the generic
  point is the only point over the generic point.
* `MMP.GenericCovering.quasiFiniteAt_genericPoint`: `f` is quasi-finite at the
  generic point.
* `MMP.GenericCovering.exists_isAffineOpen_isFinite`: generic finiteness and
  regularity.
* `MMP.GenericCovering.exists_isAffineOpen_coveringPresentation`: the open `U`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace MMP.GenericCovering

variable {K : Type u} [Field K]

variable {V W : Scheme.{u}} [V.Over (Spec (.of K))] [W.Over (Spec (.of K))]

/-- **The only point over the generic point.** Let `f : V → W` be a morphism over `K` of
varieties of the same dimension. A point `x` with `f(x) = η_W` is the generic point of `V`. -/
theorem eq_genericPoint_of_apply_eq_genericPoint [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of K))] [QuasiCompact (W ↘ Spec (.of K))] (f : V ⟶ W)
    [f.IsOver (Spec (.of K))] (hdim : topologicalKrullDim V = topologicalKrullDim W) {x : V}
    (hx : f x = genericPoint W) : x = genericPoint V := by
  have hle := topologicalKrullDim_closure_singleton_image_le K f (V ↘ Spec (.of K))
    (W ↘ Spec (.of K)) (comp_over f (Spec (.of K))) x
  have hW : topologicalKrullDim (closure ({genericPoint W} : Set W)) = topologicalKrullDim W := by
    rw [genericPoint_closure]
    exact (Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq
  rw [hx, hW, ← hdim] at hle
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of K))
  have hfinV : topologicalKrullDim V ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_locallyOfFiniteType K (V ↘ Spec (.of K))
  have huniv : closure ({x} : Set V) = Set.univ := by
    by_contra hne
    have hfin : topologicalKrullDim (closure ({x} : Set V)) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinV (topologicalKrullDim_subspace_le V _)
    exact absurd hle (not_le.2
      (MMP.topologicalKrullDim_lt_of_isClosed_of_ne_univ isClosed_closure hne hfin))
  exact (show IsGenericPoint x ⊤ from huniv).eq (genericPoint_spec V)

/-- A dominant morphism over `K` of varieties of the same dimension is quasi-finite at the generic
point: it is the only point of its fibre. -/
theorem quasiFiniteAt_genericPoint [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of K))] [QuasiCompact (W ↘ Spec (.of K))] (f : V ⟶ W)
    [f.IsOver (Spec (.of K))] [IsDominant f] [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim V = topologicalKrullDim W) : f.QuasiFiniteAt (genericPoint V) := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have hsub : Subsingleton (f.fiber (f (genericPoint V))) := by
    refine ⟨fun a b ↦ (f.fiberι _).isEmbedding.injective ?_⟩
    have key : ∀ c : f.fiber (f (genericPoint V)), f.fiberι _ c = genericPoint V := fun c ↦ by
      have hc : f.fiberι _ c ∈ f ⁻¹' {f (genericPoint V)} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨c, rfl⟩
      exact eq_genericPoint_of_apply_eq_genericPoint (K := K) f hdim
        (hc.trans (genericPoint_eq_of_isDominant f))
    rw [key a, key b]
  convert isOpen_univ
  exact Set.eq_univ_of_forall fun c ↦ Subsingleton.elim c _

/-- **Generic finiteness and regularity.** Let `f : V → W` be a proper dominant morphism over `K`
of varieties of the same dimension. There is an affine open `U ⊆ W` containing the generic point,
consisting of regular points, such that `f⁻¹(U)` consists of regular points and `f⁻¹(U) → U` is
finite. -/
theorem exists_isAffineOpen_isFinite [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of K))] [QuasiCompact (W ↘ Spec (.of K))] (f : V ⟶ W)
    [f.IsOver (Spec (.of K))] [IsProper f] [IsDominant f] (hdim : topologicalKrullDim V = topologicalKrullDim W) :
    ∃ U : W.Opens, IsAffineOpen U ∧ genericPoint W ∈ U ∧ (U : Set W) ⊆ regularLocus W ∧
      (f ⁻¹ᵁ U : Set V) ⊆ regularLocus V ∧ IsFinite (f ∣_ U) := by
  set Zq : Set V := (f.quasiFiniteLocus : Set V)ᶜ
  set Zs : Set V := singularLocus V
  have hZq : IsClosed Zq := f.quasiFiniteLocus.isOpen.isClosed_compl
  have hZs : IsClosed Zs := isClosed_singularLocus_of_isAlgebraicScheme K V
  set O : Set W := (f '' Zq ∪ f '' Zs ∪ singularLocus W)ᶜ
  have hO : IsOpen O := (((f.isClosedMap _ hZq).union (f.isClosedMap _ hZs)).union
    (isClosed_singularLocus_of_isAlgebraicScheme K W)).isOpen_compl
  have hgen : ∀ x : V, f x = genericPoint W → x = genericPoint V := fun x hx ↦
    eq_genericPoint_of_apply_eq_genericPoint (K := K) f hdim hx
  have hηO : genericPoint W ∈ O := by
    simp only [O, Set.mem_compl_iff, Set.mem_union, Set.mem_image, not_or]
    refine ⟨⟨?_, ?_⟩, fun h ↦ h (genericPoint_mem_regularLocus W)⟩
    · rintro ⟨x, hx, hfx⟩
      rw [hgen x hfx] at hx
      exact hx (Scheme.Hom.mem_quasiFiniteLocus.mpr (quasiFiniteAt_genericPoint (K := K) f hdim))
    · rintro ⟨x, hx, hfx⟩
      rw [hgen x hfx] at hx
      exact hx (genericPoint_mem_regularLocus V)
  obtain ⟨U, hU, hηU, hUO⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) hηO
  have hUO' : ∀ z ∈ (U : Set W), z ∈ O := fun z hz ↦ hUO hz
  refine ⟨U, hU, hηU, fun z hz ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · have := hUO' z hz
    simp only [O, Set.mem_compl_iff, Set.mem_union, not_or] at this
    by_contra h
    exact this.2 h
  · have := hUO' (f x) hx
    simp only [O, Set.mem_compl_iff, Set.mem_union, Set.mem_image, not_or] at this
    by_contra h
    exact this.1.2 ⟨x, h, rfl⟩
  · have hqf : ∀ x ∈ (f ⁻¹ᵁ U : Set V), x ∈ f.quasiFiniteLocus := fun x hx ↦ by
      have := hUO' (f x) hx
      simp only [O, Set.mem_compl_iff, Set.mem_union, Set.mem_image, not_or] at this
      by_contra h
      exact this.1.1 ⟨x, h, rfl⟩
    have : LocallyQuasiFinite ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp]
      refine eq_top_iff.mpr fun x _ ↦ ?_
      exact hqf _ x.2
    have : LocallyQuasiFinite (f ∣_ U ≫ U.ι) := by
      rw [morphismRestrict_ι]; infer_instance
    have := LocallyQuasiFinite.of_comp (f ∣_ U) U.ι
    exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- On an open subscheme `U` of an integral scheme, the germ at the generic point of a section of
`f⁻¹(U)` pulled back along `f ∣_ U` is the image under `R(W) → R(V)` of the germ of the section. -/
theorem germToFunctionField_topIso_appTop {V W : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    (f : V ⟶ W) [IsDominant f] (U : W.Opens) [hU : Nonempty U] [hU' : Nonempty (f ⁻¹ᵁ U)]
    (a : Γ(U, ⊤)) :
    (V.germToFunctionField (f ⁻¹ᵁ U)).hom ((f ⁻¹ᵁ U).topIso.hom.hom ((f ∣_ U).appTop.hom a)) =
      dominantFunctionFieldMap f ((W.germToFunctionField U).hom (U.topIso.hom.hom a)) := by
  have : Nonempty (U.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]; exact hU
  have : Nonempty (f ⁻¹ᵁ (U.ι ''ᵁ ⊤)) := by rw [Scheme.Opens.ι_image_top]; exact hU'
  have key := RingHom.congr_fun (Stacks.Chow.appLE_germToFunctionField_commutes f (U.ι ''ᵁ ⊤)
    (f ⁻¹ᵁ (U.ι ''ᵁ ⊤)) le_rfl) a
  simp only [RingHom.coe_comp, ← Scheme.Hom.app_eq_appLE] at key
  rw [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_hom, morphismRestrict_appTop]
  simp only [Scheme.germToFunctionField] at key ⊢
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply]
  exact key

/-- The global sections of a nonempty affine open subscheme `U` of an integral scheme `X` have
fraction field `R(X)`, through the germ at the generic point. -/
theorem isFractionRing_topIso (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) :
    letI := ((X.germToFunctionField U).hom.comp U.topIso.hom.hom).toAlgebra
    IsFractionRing Γ(U, ⊤) X.functionField := by
  let := ((X.germToFunctionField U).hom.comp U.topIso.hom.hom).toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have hinj : Function.Injective (algebraMap Γ(U, ⊤) X.functionField) :=
    (IsFractionRing.injective Γ(X, U) X.functionField).comp
      U.topIso.commRingCatIsoToRingEquiv.injective
  have : FaithfulSMul Γ(U, ⊤) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) z
  refine ⟨U.topIso.inv.hom x, U.topIso.inv.hom y, ?_⟩
  have h : ∀ t : Γ(X, U), U.topIso.hom.hom (U.topIso.inv.hom t) = t := fun t ↦
    U.topIso.commRingCatIsoToRingEquiv.apply_symm_apply t
  simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply, h]

/-- The two Stacks constructions of the extension of function fields of a dominant morphism of
integral schemes, `dominantFunctionFieldMap` and `functionFieldMap`, agree: both are the stalk
map at the generic point, transported along `f (genericPoint V) = genericPoint W`. -/
private theorem cast_stalkMap_eq_stalkCongr_comp {V W : Scheme.{u}} (f : V ⟶ W) (x : V) {y : W}
    (h : f x = y) (h' : Inseparable y (f x)) :
    (h ▸ f.stalkMap x : W.presheaf.stalk y ⟶ V.presheaf.stalk x) =
      (W.presheaf.stalkCongr h').hom ≫ f.stalkMap x := by
  subst h
  simp

private theorem dominantFunctionFieldMap_eq_functionFieldMap {V W : Scheme.{u}} (f : V ⟶ W)
    [IsIntegral V] [IsIntegral W] [IsDominant f] :
    dominantFunctionFieldMap f = functionFieldMap f := by
  unfold dominantFunctionFieldMap functionFieldMap
  exact congrArg CommRingCat.Hom.hom (cast_stalkMap_eq_stalkCongr_comp f _ _ _)

/-- **A proper morphism of varieties of the same dimension is generically a hypersurface
covering.** Let `f : V → W` be a proper dominant morphism over a field `K` of characteristic zero
of varieties of the same dimension. There is an affine open `U ⊆ W` containing the generic point,
consisting of regular points, with `f⁻¹(U)` affine and consisting of regular points, such that
`Γ(U) → Γ(f⁻¹ U)` has a covering presentation with nonzero conductor element and nonzero `δ`,
whose polynomial has degree `deg(V/W)`, the residue degree of `f` at the generic point of `V`. -/
theorem exists_isAffineOpen_coveringPresentation [CharZero K] [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of K))] [QuasiCompact (V ↘ Spec (.of K))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of K))] [QuasiCompact (W ↘ Spec (.of K))]
    (f : V ⟶ W) [f.IsOver (Spec (.of K))] [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim V = topologicalKrullDim W) :
    ∃ U : W.Opens, IsAffineOpen U ∧ genericPoint W ∈ U ∧ (U : Set W) ⊆ regularLocus W ∧
      (f ⁻¹ᵁ U : Set V) ⊆ regularLocus V ∧ IsAffineOpen (f ⁻¹ᵁ U) ∧
      letI := (f ∣_ U).appTop.hom.toAlgebra
      ∃ P : CoveringPresentation Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤), P.c ≠ 0 ∧ P.δ ≠ 0 ∧
          P.f.natDegree = f.residueDegree (genericPoint V) := by
  obtain ⟨U, hU, hηU, hUreg, hVreg, hfin⟩ := exists_isAffineOpen_isFinite (K := K) f hdim
  have hηV : genericPoint V ∈ f ⁻¹ᵁ U := by
    change f _ ∈ U
    rw [genericPoint_eq_of_isDominant]
    exact hηU
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hηV⟩⟩
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U) := isAffine_of_isAffineHom (f ∣_ U)
  have hU' : IsAffineOpen (f ⁻¹ᵁ U) := inferInstanceAs (IsAffine (f ⁻¹ᵁ U))
  refine ⟨U, hU, hηU, hUreg, hVreg, hU', ?_⟩
  let : Algebra Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤) := (f ∣_ U).appTop.hom.toAlgebra
  have : Module.Finite Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤) :=
    ((isFinite_iff _).1 hfin).2 ⊤ (isAffineOpen_top _)
  let : Algebra Γ(U, ⊤) W.functionField :=
    ((W.germToFunctionField U).hom.comp U.topIso.hom.hom).toAlgebra
  let : Algebra Γ(f ⁻¹ᵁ U, ⊤) V.functionField :=
    ((V.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f ⁻¹ᵁ U).topIso.hom.hom).toAlgebra
  let : Algebra W.functionField V.functionField := (functionFieldMap f).toAlgebra
  let : Algebra Γ(U, ⊤) V.functionField :=
    ((algebraMap Γ(f ⁻¹ᵁ U, ⊤) V.functionField).comp (algebraMap Γ(U, ⊤) _)).toAlgebra
  have : IsScalarTower Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤) V.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(U, ⊤) W.functionField V.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (germToFunctionField_topIso_appTop f U a).trans
      (by rw [dominantFunctionFieldMap_eq_functionFieldMap]; rfl)
  have := isFractionRing_topIso W U hU
  have := isFractionRing_topIso V (f ⁻¹ᵁ U) hU'
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  haveI hdom : IsDomain Γ(U, ⊤) := inferInstance
  haveI : Nontrivial Γ(U, ⊤) := hdom.toNontrivial
  have : CharZero Γ(U, ⊤) :=
    charZero_of_injective_ringHom
      (f := ((Scheme.ΓSpecIso (.of K)).inv ≫ (U.ι ≫ W ↘ Spec (.of K)).appTop).hom)
      (RingHom.injective _)
  have hinj : Function.Injective (algebraMap Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤)) := by
    have h : Function.Injective (algebraMap Γ(U, ⊤) V.functionField) := by
      rw [IsScalarTower.algebraMap_eq Γ(U, ⊤) W.functionField V.functionField]
      exact (algebraMap W.functionField V.functionField).injective.comp
        (IsFractionRing.injective _ _)
    intro a b hab
    apply h
    rw [IsScalarTower.algebraMap_apply Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤) V.functionField, hab,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨P, hc, hδ⟩ := exists_coveringPresentation Γ(U, ⊤) Γ(f ⁻¹ᵁ U, ⊤) hinj
  refine ⟨P, hc, hδ, ?_⟩
  rw [P.natDegree_f_eq_finrank W.functionField V.functionField hc]
  exact (residueDegree_genericPoint_eq_finrank_functionField f).symm

end MMP.GenericCovering
