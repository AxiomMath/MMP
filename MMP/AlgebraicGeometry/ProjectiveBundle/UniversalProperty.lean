module

public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian

/-!
# Universal properties: projective bundles, König's lemma, rigidity

This file collects three universal or existence statements used in the minimal model program.

**Projective bundles.** Let `ℰ` be a locally free `𝒪_X`-module of positive finite rank and
`π : ℙ(ℰ) ⟶ X` its projective bundle `Proj_X(Sym ℰ)`, with tautological quotient
`π^*ℰ ↠ 𝒪_{ℙ(ℰ)}(1)`. For a morphism `p : Y ⟶ X`, a line bundle `ℒ` on `Y` and an epimorphism
`q : p^*ℰ ⟶ ℒ`, there is a unique `X`-morphism `f : Y ⟶ ℙ(ℰ)` together with a unique isomorphism
`f^*𝒪(1) ≅ ℒ` carrying the pulled-back tautological quotient to `q`. Conversely every morphism
`f : Y ⟶ ℙ(ℰ)` pulls the tautological quotient back to an epimorphism onto a line bundle.

**König's lemma.** An infinite rooted tree in which every vertex has finitely many children has
an infinite path from the root through pairwise distinct vertices.

**Rigidity.** Let `f : X ⟶ Z` be proper with `f.c : 𝒪_Z ⟶ f_* 𝒪_X` an isomorphism. A morphism
`g : X ⟶ T` whose underlying map is constant on the fibres of `f` factors uniquely through `f`.

## Main results

* `MMP.existsUnique_hom_projectiveBundle_of_epi`: the universal property of `ℙ(ℰ)` for
  invertible quotients.
* `MMP.Resolution.exists_injective_seq_of_infinite_of_forall_finite_children`: König's lemma
  for finitely branching arborescences.
* `MMP.existsUnique_comp_eq_of_isIso_c`: the unique factorization `f ≫ h = g`.

## Implementation notes

The tautological quotient is `Stacks.ProjectiveBundleSplitting.tautologicalMap`, with target
`tautologicalTwist`, i.e. `𝒪_{ℙ(ℰ)}(1)`. The identification of `p^*ℰ` with `f^*π^*ℰ` is the
canonical one, `Scheme.Modules.pullbackCongr` followed by `Scheme.Modules.pullbackComp`. The
classifying morphism is that of Tag 01O4 for the canonical tautological datum
`Stacks.RelativeProj.tautologicalDatum`, which lives on the other presentation
`Stacks.RelativeProj.projectiveBundle X ℰ` of the bundle; the two presentations are identified
by `Stacks.RelativeProj.bundlePresentationIso`, an isomorphism over `X`.

The tree in König's lemma is a `Quiver.Arborescence`; the order-theoretic form of the result
is `exists_seq_covby_of_forall_covby_finite`.

For rigidity, `f` is closed and, since `f.c` is an isomorphism, surjective, hence a quotient map.
The factorization is built in one step as a morphism of locally ringed spaces: the underlying
map descends along `f`, the sheaf map is `g.c` followed by the pushforward of `inv f.c`, and the
stalk maps are local because composing them with those of `f` gives those of `g`. Uniqueness
holds because `f` is surjective and each `f.app U` is injective.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [EGA II, 4.2.3]
* [J. Kollár, *Lectures on resolution of singularities*][KollarResolution]
-/

universe u v

open CategoryTheory AlgebraicGeometry

namespace MMP

/-! ### The projective bundle represents invertible quotients -/

section ProjectiveBundle

open MMP.Intersection.Scheme.Modules

/-- The coherence of the inverse-image pseudofunctor used to move the tautological quotient
across a comparison `b : P' ⟶ P` over the base. -/
private theorem pullbackComp_coherence {Y P P' X : Scheme.{u}} (h : Y ⟶ P') (b : P' ⟶ P)
    (π : P ⟶ X) (π' : P' ⟶ X) (γ : b ≫ π = π') (p : Y ⟶ X) (hh : h ≫ π' = p)
    (hf : (h ≫ b) ≫ π = p) (M : X.Modules) :
    (Scheme.Modules.pullbackCongr hh).inv.app M ≫
      (Scheme.Modules.pullbackComp h π').inv.app M ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackCongr γ).inv.app M) ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp b π).inv.app M) ≫
      (Scheme.Modules.pullbackComp h b).hom.app ((Scheme.Modules.pullback π).obj M) =
      (Scheme.Modules.pullbackCongr hf).inv.app M ≫
        (Scheme.Modules.pullbackComp (h ≫ b) π).inv.app M := by
  subst γ hh
  have key := Stacks.Modules.pullbackComp_congr_assoc h b π _ rfl _ rfl _ hf M
  have : Mono ((Scheme.Modules.pullbackComp (h ≫ b) π).hom.app M ≫
      (Scheme.Modules.pullbackCongr hf).hom.app M) :=
    inferInstanceAs (Mono ((Scheme.Modules.pullbackComp (h ≫ b) π).app M ≪≫
      (Scheme.Modules.pullbackCongr hf).app M).hom)
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (h ≫ b) π).hom.app M ≫
    (Scheme.Modules.pullbackCongr hf).hom.app M)]
  simp only [Functor.map_comp, Category.assoc] at key
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, NatTrans.id_app, CategoryTheory.Functor.map_id] at key ⊢
  rw [← key]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp

/-- `𝒪^{⊕ 1}` is the structure sheaf. -/
private noncomputable def freeFinOneIsoUnit {X : Scheme.{u}} (U : X.Opens) :
    SheafOfModules.free (R := (U : Scheme.{u}).ringCatSheaf) (ULift.{u} (Fin 1)) ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
  Limits.coproductUniqueIso (fun _ : ULift.{u} (Fin 1) =>
    SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

/-- A line bundle in the sense of `IsLineBundle` is an invertible module. -/
private theorem isLineBundle_iff_isInvertible {X : Scheme.{u}} (L : X.Modules) :
    IsLineBundle L ↔
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := by
  rw [AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨U, hU, ⟨e⟩⟩ := h x
    exact ⟨U, hU, ⟨e ≪≫ freeFinOneIsoUnit U⟩⟩
  · obtain ⟨U, hU, ⟨e⟩⟩ := h x
    exact ⟨U, hU, ⟨e ≪≫ (freeFinOneIsoUnit U).symm⟩⟩

/-- The tautological quotient of `Stacks.RelativeProj.projectiveBundle X ℰ`, pulled back along
`h`, agrees with the tautological map of `projectiveBundle ℰ` pulled back along
`h ≫ (bundlePresentationIso ℰ).inv`, up to the composition isomorphism of inverse images. -/
private theorem overQuotientMap_comp_pullbackComp {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {Y : Scheme.{u}} {p : Y ⟶ X}
    (h : Y ⟶ Stacks.RelativeProj.projectiveBundle X E)
    (hh : h ≫ Stacks.RelativeProj.projectiveBundleToBase X E = p)
    (hf : (h ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv) ≫
      projectiveBundleToBase E = p) :
    (Stacks.RelativeProj.tautologicalDatum E).overQuotientMap h hh ≫
        (Scheme.Modules.pullbackComp h (Stacks.RelativeProj.bundlePresentationIso E).inv).hom.app
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) =
      (Scheme.Modules.pullbackCongr hf).inv.app E ≫
        (Scheme.Modules.pullbackComp (h ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)
          (projectiveBundleToBase E)).inv.app E ≫
        (Scheme.Modules.pullback (h ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) := by
  have nat := (Scheme.Modules.pullbackComp h
    (Stacks.RelativeProj.bundlePresentationIso E).inv).hom.naturality
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))
  simp only [Functor.comp_map] at nat
  have coh := pullbackComp_coherence h (Stacks.RelativeProj.bundlePresentationIso E).inv
    (projectiveBundleToBase E) _ (Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase E)
    p hh hf E
  unfold Stacks.RelativeProj.TautologicalDatum.overQuotientMap
  dsimp only [Stacks.RelativeProj.tautologicalDatum]
  unfold Stacks.RelativeProj.tautologicalDatumUniv
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [nat]
  simp only [← Category.assoc] at coh ⊢
  rw [coh]

/-- Pulling back `𝒪(1)` along any morphism to `projectiveBundle ℰ` keeps the tautological
quotient an epimorphism. -/
private theorem epi_pullback_map_tautologicalMap {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {Y : Scheme.{u}} (f : Y ⟶ projectiveBundle E) :
    Epi ((Scheme.Modules.pullback f).map (Stacks.ProjectiveBundleSplitting.tautologicalMap E
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))) := by
  have := Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)
  have := Functor.preservesEpimorphisms_of_adjunction
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  infer_instance

/-- An invertible quotient `Q` of `p^*ℰ` is classified, in the sense of the canonical tautological
datum on `Stacks.RelativeProj.projectiveBundle X ℰ`, by `g` exactly when the tautological quotient
of `projectiveBundle ℰ`, pulled back along `g ≫ (bundlePresentationIso ℰ).inv`, is isomorphic to
`Q` under `p^*ℰ`. -/
private theorem exists_iso_comp_eq_iff_isEquivalent {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {Y : Scheme.{u}} {p : Y ⟶ X}
    (Q : Stacks.Divisors.InvertibleQuotient Y ((Scheme.Modules.pullback p).obj E))
    (g : Y ⟶ Stacks.RelativeProj.projectiveBundle X E)
    (hg : g ≫ Stacks.RelativeProj.projectiveBundleToBase X E = p)
    (hf : (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv) ≫
      projectiveBundleToBase E = p) :
    (∃ φ : (Scheme.Modules.pullback (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) ≅ Q.L,
        (Scheme.Modules.pullbackCongr hf).inv.app E ≫
          (Scheme.Modules.pullbackComp (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)
            (projectiveBundleToBase E)).inv.app E ≫
          (Scheme.Modules.pullback (g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)).map
            (Stacks.ProjectiveBundleSplitting.tautologicalMap E
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) ≫ φ.hom = Q.q) ↔
      ((Stacks.RelativeProj.tautologicalDatum E).overQuotient _ (Iso.refl _) g hg).IsEquivalent
        Q := by
  have K := overQuotientMap_comp_pullbackComp E g hg hf
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨(Scheme.Modules.pullbackComp g
      (Stacks.RelativeProj.bundlePresentationIso E).inv).app _ ≪≫ φ, ?_⟩
    simp only [Stacks.RelativeProj.TautologicalDatum.overQuotient_q, Iso.refl_hom,
      Category.id_comp, Iso.trans_hom, Iso.app_hom]
    exact (Category.assoc _ _ _).symm.trans ((K =≫ φ.hom).trans (by simpa using hφ))
  · rintro ⟨α, hα⟩
    refine ⟨((Scheme.Modules.pullbackComp g
      (Stacks.RelativeProj.bundlePresentationIso E).inv).app _).symm ≪≫ α, ?_⟩
    simp only [Stacks.RelativeProj.TautologicalDatum.overQuotient_q, Iso.refl_hom,
      Category.id_comp] at hα
    have := K =≫ ((Scheme.Modules.pullbackComp g
      (Stacks.RelativeProj.bundlePresentationIso E).inv).inv.app _ ≫ α.hom)
    exact this.symm.trans ((Category.assoc _ _ _).trans
      ((congrArg _ (Iso.hom_inv_id_app_assoc _ _ _)).trans hα))

/-- **The projective bundle `ℙ(ℰ) = Proj_X(Sym ℰ)` represents invertible quotients of `ℰ`.**
For `p : Y ⟶ X`, a line bundle `ℒ` on `Y` and an epimorphism `q : p^*ℰ ⟶ ℒ`, there is a unique
`f : Y ⟶ ℙ(ℰ)` over `X` and a unique isomorphism `φ : f^*𝒪(1) ≅ ℒ` with
`p^*ℰ ≅ f^*π^*ℰ ⟶ f^*𝒪(1) ⟶ ℒ` equal to `q`. Conversely, for every `f : Y ⟶ ℙ(ℰ)`, the twist
`f^*𝒪(1)` is a line bundle and the pullback of the tautological quotient is an epimorphism. -/
@[mmp "lem_mmp_quotient_projective_bundle_universal"]
public theorem existsUnique_hom_projectiveBundle_of_epi {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] (hE : ∃ e : ℕ, 0 < e ∧ IsLocallyFreeOfRank E e) :
    (∀ {Y : Scheme.{u}} (p : Y ⟶ X) (L : Y.Modules), IsLineBundle L →
      ∀ (q : (Scheme.Modules.pullback p).obj E ⟶ L), Epi q →
        ∃! f : Y ⟶ projectiveBundle E, ∃ h : f ≫ projectiveBundleToBase E = p,
          ∃! φ : (Scheme.Modules.pullback f).obj
              (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
                (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) ≅ L,
            (Scheme.Modules.pullbackCongr h).inv.app E ≫
              (Scheme.Modules.pullbackComp f (projectiveBundleToBase E)).inv.app E ≫
              (Scheme.Modules.pullback f).map
                (Stacks.ProjectiveBundleSplitting.tautologicalMap E
                  (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)) ≫
              φ.hom = q) ∧
    ∀ {Y : Scheme.{u}} (f : Y ⟶ projectiveBundle E),
      IsLineBundle ((Scheme.Modules.pullback f).obj
          (Stacks.ProjectiveBundleSplitting.tautologicalTwist E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))) ∧
        Epi ((Scheme.Modules.pullback f).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap E
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E))) := by
  refine ⟨fun {Y} p L hL q hq => ?_, fun {Y} f => ⟨?_, epi_pullback_map_tautologicalMap E f⟩⟩
  · let Q : Stacks.Divisors.InvertibleQuotient Y ((Scheme.Modules.pullback p).obj E) :=
      ⟨L, (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
        ((isLineBundle_iff_isInvertible L).mp hL), q, hq⟩
    let D := Stacks.RelativeProj.tautologicalDatum E
    let c := D.classifyingMorphismOver _ (Iso.refl _) Q
    have hc : (c.1 ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv) ≫
        projectiveBundleToBase E = p := by
      rw [Category.assoc, Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase, c.2]
    obtain ⟨φ, hφ⟩ := (exists_iso_comp_eq_iff_isEquivalent E Q c.1 c.2 hc).2
      (D.overQuotient_classifyingMorphismOver_isEquivalent _ (Iso.refl _) Q)
    have := epi_pullback_map_tautologicalMap E
      (c.1 ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv)
    refine ⟨_, ⟨hc, φ, hφ, fun φ' hφ' => Iso.ext ?_⟩, ?_⟩
    · have h := hφ'.trans hφ.symm
      rw [NatIso.cancel_natIso_inv_left, NatIso.cancel_natIso_inv_left, cancel_epi] at h
      exact h
    · rintro f' ⟨hf', φ', hφ', -⟩
      obtain ⟨g, rfl⟩ : ∃ g, f' = g ≫ (Stacks.RelativeProj.bundlePresentationIso E).inv :=
        ⟨f' ≫ (Stacks.RelativeProj.bundlePresentationIso E).hom, by simp⟩
      have hg : g ≫ Stacks.RelativeProj.projectiveBundleToBase X E = p := by
        rw [← Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase E, ← Category.assoc, hf']
      have e := (exists_iso_comp_eq_iff_isEquivalent E Q g hg hf').1 ⟨φ', hφ'⟩
      rw [D.eq_of_overQuotient_isEquivalent _ (Iso.refl _) g c.1 hg c.2
        ((Stacks.Divisors.invertibleQuotientSetoid _ _).iseqv.trans e
          ((Stacks.Divisors.invertibleQuotientSetoid _ _).iseqv.symm
            (D.overQuotient_classifyingMorphismOver_isEquivalent _ (Iso.refl _) Q)))]
  · exact (isLineBundle_iff_isInvertible _).mpr
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
        (@Stacks.Modules.isInvertible_pullback _ _ f _
          ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
            (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E
              (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent E)))))

end ProjectiveBundle

/-! ### König's lemma -/

namespace Resolution

/-- A path out of `a` is either trivial or starts with an arrow to a child of `a`. -/
private lemma eq_or_exists_child_of_path {V : Type u} [Quiver.{v} V] {a b : V}
    (p : Quiver.Path a b) :
    b = a ∨ ∃ c, Nonempty (a ⟶ c) ∧ Nonempty (Quiver.Path c b) := by
  induction p with
  | nil => exact Or.inl rfl
  | cons p e ih =>
    rcases ih with rfl | ⟨c, hc, ⟨q⟩⟩
    · exact Or.inr ⟨_, ⟨e⟩, ⟨Quiver.Path.nil⟩⟩
    · exact Or.inr ⟨c, hc, ⟨q.cons e⟩⟩

/-- **The König step.** In a quiver, if a vertex `a` has finitely many children and infinitely
many descendants, then one of its children has infinitely many descendants. -/
private lemma exists_child_infinite_descendants {V : Type u} [Quiver.{v} V] {a : V}
    (hfin : {c : V | Nonempty (a ⟶ c)}.Finite)
    (ha : {b : V | Nonempty (Quiver.Path a b)}.Infinite) :
    ∃ c, Nonempty (a ⟶ c) ∧ {b : V | Nonempty (Quiver.Path c b)}.Infinite := by
  by_contra! h
  refine ha (((hfin.biUnion h).insert a).subset ?_)
  rintro b ⟨p⟩
  rcases eq_or_exists_child_of_path p with rfl | ⟨c, hc, hp⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_biUnion hc hp)

/-- In an arborescence, the depth of the target of an arrow is one more than that of its
source. -/
private lemma length_default_of_arrow {V : Type u} [Quiver.{v} V] [Quiver.Arborescence V]
    {a b : V} (e : a ⟶ b) :
    (default : Quiver.Path (Quiver.root V) b).length =
      (default : Quiver.Path (Quiver.root V) a).length + 1 := by
  rw [← Unique.eq_default ((default : Quiver.Path (Quiver.root V) a).cons e)]
  rfl

/-- **König's lemma.** An infinite rooted tree (an arborescence) in which every vertex has
finitely many children has an infinite path from the root: a sequence `f` with `f 0` the root,
an arrow `f n ⟶ f (n + 1)` for every `n`, and pairwise distinct terms. -/
@[mmp "lem_mmp_resolution_finite_branching_infinite_path"]
public theorem exists_injective_seq_of_infinite_of_forall_finite_children {V : Type u}
    [Quiver.{v} V] [Quiver.Arborescence V] [Infinite V]
    (hfin : ∀ a : V, {b : V | Nonempty (a ⟶ b)}.Finite) :
    ∃ f : ℕ → V, f 0 = Quiver.root V ∧ (∀ n, Nonempty (f n ⟶ f (n + 1))) ∧
      Function.Injective f := by
  let S := {a : V // {b : V | Nonempty (Quiver.Path a b)}.Infinite}
  let next : S → S := fun a =>
    have h := exists_child_infinite_descendants (hfin a.1) a.2
    ⟨h.choose, h.choose_spec.2⟩
  let f : ℕ → V := fun n =>
    (next^[n] ⟨Quiver.root V,
      Set.infinite_univ.mono fun b _ => ⟨default⟩⟩).1
  have hf : ∀ n, Nonempty (f n ⟶ f (n + 1)) := fun n => by
    simp only [f, Function.iterate_succ_apply']
    exact (exists_child_infinite_descendants (hfin _) (next^[n] _).2).choose_spec.1
  have hdepth : ∀ n, (default : Quiver.Path (Quiver.root V) (f n)).length = n := by
    intro n
    induction n with
    | zero => exact Unique.eq_default (Quiver.Path.nil : Quiver.Path (Quiver.root V) _) ▸ rfl
    | succ n ih => rw [length_default_of_arrow (hf n).some, ih]
  exact ⟨f, rfl, hf, fun m n hmn => by rw [← hdepth m, ← hdepth n, hmn]⟩

end Resolution

/-! ### Rigidity of proper morphisms with `f_* 𝒪_X = 𝒪_Z` -/

section Rigidity

open Topology

/-- A morphism `f` with closed range and `f.c` an isomorphism is surjective. -/
private lemma surjective_of_isIso_c {X Z : Scheme.{u}} (f : X ⟶ Z)
    (hf : IsClosed (Set.range f)) [IsIso f.c] : Function.Surjective f := by
  intro z
  by_contra hz
  let U : Z.Opens := ⟨(Set.range f)ᶜ, hf.isOpen_compl⟩
  have hU : f ⁻¹ᵁ U = ⊥ := le_bot_iff.mp fun x hx => (hx ⟨x, rfl⟩).elim
  have : Subsingleton Γ(X, f ⁻¹ᵁ U) := by
    rw [hU]
    infer_instance
  have : IsIso (f.app U) := inferInstanceAs (IsIso (f.c.app _))
  have h10 : (1 : Γ(Z, U)) = 0 :=
    (ConcreteCategory.bijective_of_isIso (f.app U)).1 (Subsingleton.elim _ _)
  have hzU : z ∈ U := fun ⟨x, hx⟩ => hz ⟨x, hx⟩
  have := congrArg (Z.presheaf.germ U z hzU) h10
  simp at this

/-- A restriction map of `X.presheaf` from an open to itself is the identity. -/
private lemma presheaf_map_endo {X : Scheme.{u}} {V : X.Opensᵒᵖ} (φ : V ⟶ V) :
    X.presheaf.map φ = 𝟙 _ := by
  rw [Subsingleton.elim φ (𝟙 _), CategoryTheory.Functor.map_id]

/-- The two factorizations through `f` agree, when `f` is surjective with `f.c` an
isomorphism. -/
private lemma eq_of_comp_eq {X Z T : Scheme.{u}} (f : X ⟶ Z) (hf : Function.Surjective f)
    [IsIso f.c] {h₁ h₂ : Z ⟶ T} (e : f ≫ h₁ = f ≫ h₂) : h₁ = h₂ := by
  have hb : h₁.base = h₂.base := TopCat.hom_ext <| ContinuousMap.ext fun z => by
    obtain ⟨x, rfl⟩ := hf z
    exact congrArg (fun k : X ⟶ T => k x) e
  refine Scheme.Hom.ext hb fun U => ?_
  have : IsIso (f.app (h₂ ⁻¹ᵁ U)) := inferInstanceAs (IsIso (f.c.app _))
  have h := Scheme.Hom.congr_app e U
  simp only [Scheme.Hom.comp_app] at h
  rw [← cancel_mono (f.app (h₂ ⁻¹ᵁ U)), Category.assoc, f.naturality, ← Category.assoc, h]
  simp only [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Category.assoc,
    eqToHom_op, eqToHom_unop, ← Functor.map_comp]
  erw [presheaf_map_endo, Category.comp_id]

/-- **Existence of the factorization.** If `f` is a quotient map on underlying spaces with
`f.c` an isomorphism, then every `g` constant on the fibres of `f` factors through `f`. -/
private lemma exists_comp_eq {X Z T : Scheme.{u}} (f : X ⟶ Z) (hq : IsQuotientMap f)
    [IsIso f.c] (g : X ⟶ T) (hg : ∀ x x' : X, f x = f x' → g x = g x') :
    ∃ h : Z ⟶ T, f ≫ h = g := by
  let h₀ : Z.toTopCat ⟶ T.toTopCat :=
    TopCat.ofHom (hq.lift (f := f.base.hom) g.base.hom hg)
  have hbase : f.base ≫ h₀ = g.base := by
    ext x
    exact congrArg (fun k : C(X, T) => k x) (hq.lift_comp (f := f.base.hom) g.base.hom hg)
  let H : Z.toPresheafedSpace ⟶ T.toPresheafedSpace :=
    { base := h₀
      c := g.c ≫ ((TopCat.Presheaf.pushforwardEq hbase.symm X.presheaf).hom :
          (TopCat.Presheaf.pushforward _ g.base).obj X.presheaf ⟶
            (TopCat.Presheaf.pushforward _ h₀).obj
              ((TopCat.Presheaf.pushforward _ f.base).obj X.presheaf)) ≫
        (TopCat.Presheaf.pushforward _ h₀).map (inv f.c) }
  have key : f.toHom ≫ H = g.toHom := by
    refine PresheafedSpace.Hom.ext _ _ hbase (NatTrans.ext (funext fun U => ?_))
    rw [NatTrans.comp_app]
    erw [PresheafedSpace.comp_c_app, NatTrans.comp_app, NatTrans.comp_app,
      TopCat.Presheaf.pushforward_map_app', Category.assoc, Category.assoc, Category.assoc,
      NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc, TopCat.Presheaf.pushforwardEq_hom_app,
      Functor.whiskerRight_app, ← X.presheaf.map_comp, presheaf_map_endo, Category.comp_id]
  have hloc (z : Z) : IsLocalHom (H.stalkMap z).hom := by
    obtain ⟨x, rfl⟩ := hq.surjective z
    have : IsLocalHom (g.toHom.stalkMap x).hom := g.prop x
    have hcomp : IsLocalHom ((f.toHom ≫ H).stalkMap x).hom := by
      rw [PresheafedSpace.stalkMap.congr_hom _ _ key x, CommRingCat.hom_comp]
      infer_instance
    rw [PresheafedSpace.stalkMap.comp] at hcomp
    have : IsLocalHom ((f.toHom.stalkMap x).hom.comp (H.stalkMap (f x)).hom) := hcomp
    exact isLocalHom_of_comp _ (f.toHom.stalkMap x).hom
  exact ⟨⟨⟨H, hloc⟩⟩, Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' key)⟩

/-- **Rigidity factorization.** Let `f : X ⟶ Z` be proper, with `f.c : 𝒪_Z ⟶ f_* 𝒪_X` an
isomorphism. If `g : X ⟶ T` is constant on the fibres of `f` on underlying points, there is a
unique `h : Z ⟶ T` with `f ≫ h = g`. -/
@[mmp "thm_mmp_proper_fibrewise_constant_factorization"]
public theorem existsUnique_comp_eq_of_isIso_c {X Z T : Scheme.{u}} (f : X ⟶ Z) [IsProper f]
    [IsIso f.c] (g : X ⟶ T) (hg : ∀ x x' : X, f x = f x' → g x = g x') :
    ∃! h : Z ⟶ T, f ≫ h = g := by
  have hf := surjective_of_isIso_c f f.isClosedMap.isClosed_range
  obtain ⟨h, hh⟩ := exists_comp_eq f (f.isClosedMap.isQuotientMap f.continuous hf) g hg
  exact ⟨h, hh, fun h' hh' => eq_of_comp_eq f hf (hh'.trans hh.symm)⟩

end Rigidity

end MMP
