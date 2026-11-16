module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.Principalization
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Morphisms.Smooth.IrreducibleComponents
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.OrderAlongExceptional
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
import MMP.AlgebraicGeometry.Resolution.OrderReduction.Existence
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedClosedEmbedding
import MMP.AlgebraicGeometry.Resolution.Principalization.ComponentRestriction
import MMP.AlgebraicGeometry.Resolution.Principalization.FromOrderReduction
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre

/-!
# The canonical principalization functor `𝓑𝓟^can`

Over a field of characteristic `0`, the assembled order reduction functor `𝓑𝓜𝓞^can_m`, sending a
marked triple `(X, I, m, E)` to `𝓑𝓜𝓞_{dim X, m}(X, I, m, E)`, is an order reduction functor for
marked ideals of order `m` (Kollár 3.69). Feeding `𝓑𝓜𝓞^can_1` into the principalization
construction gives the canonical principalization functor `𝓑𝓟^can` of Kollár 3.72, defined on the
triples `(X, I, E)` of Notation 3.64: `X` smooth, equidimensional and of finite type over a field
of characteristic `0`, `I` nonzero at the generic points of `X`, `E` an ordered snc divisor.

This file proves the properties of `𝓑𝓟^can(X, I, E) = (X_i, Z_i)_{i ≤ r}`, with composites
`Π_i : X_i → X`: it is a smooth blow-up sequence whose centres have simple normal crossings with
`E`; `Π^*I` is monomial; its centres lie over `cosupp I ∪ E^{(2)}`, and over `cosupp I` when the
components of `E` are disjoint, in which case `Π` is an isomorphism over `X ∖ cosupp I`; and it
commutes with smooth morphisms, with change of fields and with closed embeddings when `E = ∅`.
On a smooth variety every `X_i` is a smooth variety and every `Π_i` is projective and birational.
Locally, `𝓑𝓟^can` first blows up the reduced origin of `𝔸^c_k`, `c ≥ 2`, and near a point at
which a reduced closed subscheme `X ⊆ P` of codimension `≥ 2` is smooth, the first nonempty centre
of `𝓑𝓟^can(P, I_X, ∅)` is `X` itself (Kollár, p. 139).

## Main results

* `MMP.Resolution.exists_isOrderReductionFunctorMarked_assembledMarkedOrderReduction`:
  `𝓑𝓜𝓞^can_m` is an order reduction functor (Kollár 3.69).
* `MMP.Resolution.canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus`:
  `𝓑𝓟^can` is a principalization functor away from `E^{(2)}` (Kollár 3.72).
* `MMP.Resolution.canonicalPrincipalization_properties`: the properties (1)–(5) of 3.72.
* `MMP.Resolution.exists_reduction_canonicalPrincipalization_eq_cons_ker_origin`: `𝓑𝓟^can` of
  the ideal of the origin of `𝔸^c_k`, `c ≥ 2`, begins with the blow-up of the origin.
* `MMP.Resolution.isVariety_and_isProjective_toBase_truncate_canonicalPrincipalization`: on a
  smooth variety, the stages of `𝓑𝓟^can` are smooth varieties, projective and birational over it.
* `MMP.Resolution.exists_centersLieOver_compl_and_comap_eq_canonicalPrincipalization`: near a
  smooth point of `X ⊆ P`, the first nonempty centre of `𝓑𝓟^can(P, I_X, ∅)` is `X`.

## Implementation notes

`𝓑𝓟^can` is defined on the snc triples, but it is a principalization functor only on its domain
`MMP.Resolution.triples`, the triples with `X` equidimensional; every clause is stated for triples
in `triples`, and membership of the triples constructed here is part of each conclusion.

`ClosedBlowupSequence` is inductive, without indexed centres. The `i`-th stage with its composite
`Π_i` is the target and `toBase` of `ClosedBlowupSequence.truncate B i`; "`Π_i(Z_i) ⊆ S` for every
`i`" is `ClosedBlowupSequence.CentersLieOver (𝟙 X) S`; and "`Z_l = ∅` for `l < l₀`, and `Z_{l₀}`
is `Z`" is the statement that the reduction `ClosedBlowupSequence.reduction`, which deletes the
empty blow-ups, is `ClosedBlowupSequence.cons Z B'`. The irreducible components of `E` are the
maximal irreducible subsets of its support (`MMP.Resolution.componentsOf`), and `E^{(2)}` is the
set of points on two of them; for an snc divisor it contains `OrderedDivisor.doubleLocus`.

The affine space `𝔸^c_k` is `𝔸(ULift (Fin c); Spec k)`, so that the statements stay universe
polymorphic, and the ideal `𝔪₀` of the origin is the kernel of the zero section
`AffineSpace.homOfVector (𝟙 _) 0`. A reduced closed subscheme `X ⊆ P` is its ideal sheaf `I`, and
"every component of `X` has codimension `≥ 2`" is `2 ≤ MMP.Mori.closedsCodimension I.support`.
Near a smooth point of `X`, `X` is the pull-back of the origin of `𝔸^c_k` along a smooth
`h : U → 𝔸^c_k`, with `U` affine and irreducible so that `(U, I|_U, ∅)` is again a triple; Krull's
height theorem at the generic point of the component gives `c ≥ 2`. Projectivity of `Π_i` is
projectivity in the sense of EGA II 5.5 (`AlgebraicGeometry.IsProjective`): without an ample line
bundle on `X` a blow-up need not embed into any `ℙⁿ_X`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.29, 3.32, 3.34, 3.35, 3.64,
  3.69, 3.70, 3.72 and p. 139][kollar2007]
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

public section

namespace MMP.Resolution

universe u

/-! ### `𝓑𝓜𝓞^can_m` is an order reduction functor -/

/-- Deleting the empty blow-ups of a pull-back to an empty scheme leaves nothing. -/
private lemma pullbackReduced_eq_nil_of_isEmpty {X Y : Scheme.{u}} [IsEmpty Y]
    (B : ClosedBlowupSequence X) (h : Y ⟶ X) : B.pullbackReduced h = .nil Y := by
  induction B with
  | nil X => rfl
  | cons Z B ih =>
    have hZ : Z.comap h = ⊤ :=
      (Scheme.IdealSheafData.support_eq_bot_iff _).1 (SetLike.ext isEmptyElim)
    simpa [ClosedBlowupSequence.pullbackReduced, hZ] using ih _

/-- A marked triple of marking `m` on a nonempty scheme has a dimension. -/
private lemma mem_markedTriplesOfDim_univ {m : ℕ} {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriplesOfMarking m) [Nonempty t.X] :
    t ∈ markedTriplesOfDim Set.univ m := by
  obtain ⟨ht1, hm⟩ := ht
  obtain ⟨-, -, _, _, -⟩ := id ht1
  have : CompactSpace t.X := QuasiCompact.compactSpace_of_compactSpace t.sX
  have hbot : topologicalKrullDim t.X ≠ ⊥ := Order.krullDim_ne_bot_iff.2
    ⟨⟨closure {Classical.arbitrary t.X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.1 hbot
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.1 (show n ≠ ⊤ by
    rintro rfl; exact topologicalKrullDim_ne_top_of_locallyOfFiniteType t.k t.sX hn.symm)
  exact ⟨ht1, hm, d, trivial, hn.symm⟩

/-- `𝓑𝓜𝓞^can_m` is of order `≥ m` and has no empty blow-ups on every marked triple of marking `m`:
on an empty scheme it is the empty sequence, and otherwise it is `𝓑𝓜𝓞_{dim X, m}`. -/
private lemma isOrderGe_and_hasNoEmptyBlowups {m : ℕ}
    (F : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim Set.univ m))
    (hF : ∀ t ht, F.toFun t ht = bmoFamily.{u} (dimNat t.X) m t)
    (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfMarking m) :
    (assembledMarkedOrderReduction m t ht).IsOrderGeMarkedTripleSeq t.sX t.markedIdeal t.E ∧
      (assembledMarkedOrderReduction m t ht).HasNoEmptyBlowups := by
  rcases isEmpty_or_nonempty t.X with hX | hX
  · rw [show assembledMarkedOrderReduction m t ht = .nil t.X from
      pullbackReduced_eq_nil_of_isEmpty _ _]
    exact ⟨ht.1, trivial⟩
  · have ht' := mem_markedTriplesOfDim_univ ht
    rw [show assembledMarkedOrderReduction m t ht = F.toFun t ht' from (hF t ht').symm]
    exact ⟨F.isOrderGeMarkedTripleSeq t ht', F.hasNoEmptyBlowups t ht'⟩

/-- **Kollár Thm. 3.69, all dimensions at once.** For `m ≥ 1`, `assembledMarkedOrderReduction m`
is a smooth blow-up sequence functor of order `≥ m` without empty blow-ups on the marked triples
of marking `m`, and its restriction to the marked triples of any dimension is an order reduction
functor for marked ideals of order `m`. -/
@[mmp "lem_kr3f_assembled_bmo_is_order_reduction_functor"]
theorem exists_isOrderReductionFunctorMarked_assembledMarkedOrderReduction
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking m),
      B.toFun = assembledMarkedOrderReduction m ∧
      IsOrderReductionFunctorMarked m Set.univ
        ⟨fun t ht => B.toFun t ⟨ht.1, ht.2.1⟩,
          fun t ht => B.isOrderGeMarkedTripleSeq t ⟨ht.1, ht.2.1⟩,
          fun t ht => B.hasNoEmptyBlowups t ⟨ht.1, ht.2.1⟩⟩ := by
  obtain ⟨⟨f, hf₁, hf₂⟩, hF, hFR⟩ := exists_isOrderReductionFunctorMarked_bmoFamily m hm
  have key := isOrderGe_and_hasNoEmptyBlowups ⟨f, hf₁, hf₂⟩ hF
  refine ⟨⟨assembledMarkedOrderReduction m, fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩,
    rfl, ?_⟩
  obtain rfl : (fun t ht => assembledMarkedOrderReduction m t ⟨ht.1, ht.2.1⟩) = f :=
    funext₂ fun t ht => (hF t ht).symm
  exact hFR

/-! ### `𝓑𝓟^can` is a principalization functor away from `E^{(2)}` -/

/-- The clauses of `canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus`, all
in one universe `v`: `𝓑𝓟^can` is `principalizationConstructionOnTriples` for `𝓑𝓜𝓞^can_1`, an
order reduction functor with the closed embedding property that ignores empty entries. The
theorem itself states its smooth and field-change clauses in universes of their own. -/
private theorem canonicalPrincipalization_clauses.{v} :
    (∀ (t : FieldBlowupTriple.{v}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).HasNoEmptyBlowups) ∧
      (∀ (t : FieldBlowupTriple.{v}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).IsSmooth t.sX ∧
          (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersHaveSNCWith t.sX
            t.E.support) ∧
      (∀ (t : FieldBlowupTriple.{v}) (ht : t ∈ triples),
        IsMonomialIdeal
          (t.I.comap (canonicalPrincipalization t (triples_subset_sncTriples ht)).toBase)) ∧
      (∀ (t : FieldBlowupTriple.{v}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersLieOver (𝟙 t.X)
          ((t.I.support : Set t.X) ∪ t.E.doubleLocus)) ∧
      CommutesWithSmoothOn triples.{v}
        (fun t ht => canonicalPrincipalization t (triples_subset_sncTriples ht)) ∧
      CommutesWithFieldChangeOn triples.{v}
        (fun t ht => canonicalPrincipalization t (triples_subset_sncTriples ht)) ∧
      ∀ d : ClosedEmbeddingData.{v}, d.E.s = 0 →
        ∀ (hX : d.ambientTriple ∈ triples) (hY : d.embeddedTriple ∈ triples),
          ClosedBlowupSequence.IsPushforward d.j
            (canonicalPrincipalization d.embeddedTriple (triples_subset_sncTriples hY))
            (canonicalPrincipalization d.ambientTriple (triples_subset_sncTriples hX)) := by
  obtain ⟨B, hB, hred⟩ :=
    exists_isOrderReductionFunctorMarked_assembledMarkedOrderReduction.{v} 1 le_rfl
  have h := isPrincipalizationFunctorAwayFromDoubleLocus_principalizationConstruction B hred
    (hB ▸ hasClosedEmbeddingProperty_bmoFamily) (hB ▸ ignoresEmptyEntriesMarked_bmoFamily le_rfl)
  rwa [hB] at h

/-- **Kollár 3.72.** The canonical principalization functor `canonicalPrincipalization`
(`𝓑𝓟^can`) is a principalization functor away from `E^{(2)}` on the triples `(X, I, E)` of
Notation 3.64: (0) it has no empty blow-ups; (1) it is a smooth blow-up sequence whose centers
have simple normal crossings with `E`; (2) the pull-back of `I` is monomial; (3″) its centers lie
over `cosupp I ∪ E^{(2)}`; (4) it commutes with smooth morphisms and with change of fields;
(5) it commutes with closed embeddings for triples with `E = ∅`. -/
@[mmp "lem_kr3f_canonical_bp_is_principalization_functor"]
theorem canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus :
    (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).HasNoEmptyBlowups) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).IsSmooth t.sX ∧
          (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersHaveSNCWith t.sX
            t.E.support) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        IsMonomialIdeal
          (t.I.comap (canonicalPrincipalization t (triples_subset_sncTriples ht)).toBase)) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersLieOver (𝟙 t.X)
          ((t.I.support : Set t.X) ∪ t.E.doubleLocus)) ∧
      CommutesWithSmoothOn triples
        (fun t ht => canonicalPrincipalization t (triples_subset_sncTriples ht)) ∧
      CommutesWithFieldChangeOn triples
        (fun t ht => canonicalPrincipalization t (triples_subset_sncTriples ht)) ∧
      ∀ d : ClosedEmbeddingData.{u}, d.E.s = 0 →
        ∀ (hX : d.ambientTriple ∈ triples) (hY : d.embeddedTriple ∈ triples),
          ClosedBlowupSequence.IsPushforward d.j
            (canonicalPrincipalization d.embeddedTriple (triples_subset_sncTriples hY))
            (canonicalPrincipalization d.ambientTriple (triples_subset_sncTriples hX)) :=
  have h := canonicalPrincipalization_clauses.{u}
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, canonicalPrincipalization_clauses.2.2.2.2.1,
    canonicalPrincipalization_clauses.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-! ### Properties of `𝓑𝓟^can` -/

/-- A blow-up sequence whose centres lie over `S` (`X` mapping to `X₀` by `f`) has composite an
isomorphism over every open of `X` disjoint from `f⁻¹ S`. -/
private theorem isIso_toBase_restrict_of_centersLieOver :
    ∀ {X X₀ : Scheme.{u}} (B : ClosedBlowupSequence X) (f : X ⟶ X₀) (S : Set X₀),
      B.CentersLieOver f S → ∀ V : X.Opens, Disjoint (f ⁻¹' S) (V : Set X) →
        IsIso (B.toBase ∣_ V)
  | _, _, .nil X, f, S, _, V, _ => by
    rw [ClosedBlowupSequence.toBase]
    exact IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (inferInstanceAs (IsIso (𝟙 X))) V
  | _, _, .cons Z B, f, S, h, V, hV => by
    rw [ClosedBlowupSequence.CentersLieOver] at h
    obtain ⟨hZ, hB⟩ := h
    change IsIso ((B.toBase ≫ blowUpToBase Z : B.target ⟶ _) ∣_ V)
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso'
      (isIso_toBase_restrict_of_centersLieOver B _ S hB _
        (Set.disjoint_left.mpr fun _ hy hyV => Set.disjoint_left.mp hV hy hyV))
      (isIso_blowUpToBase_restrict_of_subset_compl_support Z V fun x hxV hxZ =>
        Set.disjoint_left.mp hV (hZ ⟨x, hxZ, rfl⟩) hxV)

section SNC

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- For an snc family `E` and `m ≠ l`, no irreducible component of `Supp E^m` lies in
`Supp E^l`: at its generic point the snc condition gives two distinct parameters, so the local
ring has dimension `≥ 2`, while the component has codimension one. -/
private theorem not_subset_of_mem_componentsOf {s : ℕ} {E : Fin s → X.IdealSheafData}
    (hE : IsSNCFamily sX E) {m l : Fin s} (hml : m ≠ l) {W : Set X}
    (hW : W ∈ componentsOf ((E m).support : Set X)) :
    ¬ W ⊆ (E l).support := by
  intro hWl
  obtain ⟨η, hηm, rfl⟩ := Aux.exists_eq_closure_of_mem_componentsOf (E m).support.isClosed hW
  have hηl : η ∈ ((E l).support : Set X) := hWl (subset_closure rfl)
  obtain ⟨n, z, c, hz, -, hc⟩ := hE.2 η
  have hn : 2 ≤ n := Fin.nontrivial_iff_two_le.mp
    ⟨_, _, fun h : c ⟨m, hηm⟩ = c ⟨l, hηl⟩ => hml (congrArg Subtype.val (hc h))⟩
  -- the component `closure {η}` has codimension one, so the local ring at `η` has dimension one
  have h1 := (hE.1 m).2.1 (IrreducibleCloseds.closureSingleton η)
    ⟨hW.1.2, fun V hV hWV => hW.2 ⟨V.isIrreducible, hV⟩ hWV⟩
  have h2 := hz.2
  rw [Stacks.Divisors.PrimeDivisor.codimension_closureSingleton] at h1
  rw [ringKrullDim_stalk_eq_coheight, h1] at h2
  have : (1 : ℕ) = n := by exact_mod_cast h2
  omega

/-- An irreducible subset of a closed set `D` of a Noetherian space lies in an irreducible
component of `D`. -/
private theorem exists_mem_componentsOf_superset {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {D : Set T} (hD : IsClosed D) {W : Set T} (hW : IsIrreducible W)
    (hWD : W ⊆ D) : ∃ C ∈ componentsOf D, W ⊆ C := by
  classical
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf hD
  obtain ⟨C, hC, hWC⟩ := isIrreducible_iff_sUnion_isClosed.mp hW hfin.toFinset
    (fun C hC => Aux.isClosed_of_mem_componentsOf hD (hfin.mem_toFinset.mp hC))
    (by rw [hfin.coe_toFinset]; exact hWD.trans hcov)
  exact ⟨C, hfin.mem_toFinset.mp hC, hWC⟩

/-- **The double locus lies on two components.** For an ordered divisor `E` whose entries form
an snc family on a Noetherian scheme, a point on two distinct entries of `E` lies on two distinct
irreducible components of `Supp E`. -/
private theorem doubleLocus_subset [NoetherianSpace X] (E : OrderedDivisor X)
    (hE : E.IsSNC sX) :
    E.doubleLocus ⊆ {x | ∃ C ∈ componentsOf E.support, ∃ C' ∈ componentsOf E.support,
      C ≠ C' ∧ x ∈ C ∧ x ∈ C'} := by
  classical
  rintro x ⟨i, j, hij, hxi, hxj⟩
  have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
  -- components of the entries through `x`, and components of `Supp E` containing them
  have hcomp : ∀ m, x ∈ ((E.E m).support : Set X) → ∃ W ∈ componentsOf ((E.E m).support : Set X),
      ∃ C ∈ componentsOf E.support, x ∈ W ∧ W ⊆ C := by
    intro m hxm
    obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf (E.E m).support.isClosed
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp (hcov hxm)
    obtain ⟨C, hC, hWC⟩ := exists_mem_componentsOf_superset hEc hW.1.1
      (hW.1.2.trans (Set.subset_iUnion (fun m => ((E.E m).support : Set X)) m))
    exact ⟨W, hW, C, hC, hxW, hWC⟩
  obtain ⟨Wi, hWi, Ci, hCi, hxWi, hWiCi⟩ := hcomp i hxi
  obtain ⟨Wj, hWj, Cj, hCj, hxWj, hWjCj⟩ := hcomp j hxj
  refine ⟨Ci, hCi, Cj, hCj, ?_, hWiCi hxWi, hWjCj hxWj⟩
  rintro rfl
  -- the common component lies in one entry `E^l`
  obtain ⟨_, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hCi.1.1
    (Finset.univ.image fun l => ((E.E l).support : Set X))
    (fun z hz => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hz
      exact (E.E l).support.isClosed)
    (by
      intro y hy
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 (hCi.1.2 hy)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2 ⟨l, Finset.mem_univ _, rfl⟩),
        hl⟩)
  obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hz
  by_cases hil : i = l
  · subst hil
    exact not_subset_of_mem_componentsOf hE (Ne.symm hij) hWj (hWjCj.trans hCz)
  · exact not_subset_of_mem_componentsOf hE hil hWi (hWiCi.trans hCz)

end SNC

/-- **Kollár 3.72 (3″).** The centres of `𝓑𝓟^can(X, I, E)` lie over the union of `cosupp I`
with the set `E^{(2)}` of points on two distinct irreducible components of `Supp E`. -/
private theorem centersLieOver_union {t : FieldBlowupTriple.{u}} (ht : t ∈ triples) :
    (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersLieOver (𝟙 t.X)
      ((t.I.support : Set t.X) ∪
        {x | ∃ C ∈ componentsOf t.E.support, ∃ C' ∈ componentsOf t.E.support,
          C ≠ C' ∧ x ∈ C ∧ x ∈ C'}) := by
  have := ht.2.2.1
  have := ht.2.2.2.1
  have : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  have : CompactSpace t.X := QuasiCompact.compactSpace_of_compactSpace t.sX
  have : IsNoetherian t.X := {}
  exact (canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{u, u, u}.2.2.2.1
    t ht).mono (Set.union_subset_union_right _ (doubleLocus_subset t.E ht.2.2.2.2.2.2.2))

/-- **Kollár 3.72.** Let `(X, I, E)` be a triple of Notation 3.64 (`t ∈ triples`) and
`𝓑𝓟^can(X, I, E) = (X_i, Z_i)_{i ≤ r}` (`canonicalPrincipalization`) with composite
`Π : X_r → X`. Then (1) it is a smooth blow-up sequence whose centres have simple normal crossings
with `E`; (2) `Π^*I` is monomial; (3) if the irreducible components of `E` are pairwise disjoint,
then every `Π_i(Z_i)` lies in `cosupp I` and `Π` is an isomorphism over `X ∖ cosupp I`;
(3″) every `Π_i(Z_i)` lies in `cosupp I ∪ E^{(2)}`, `E^{(2)}` the points on at least two
irreducible components of `E`; (4) `𝓑𝓟^can` commutes with smooth morphisms and with change of
fields; (5) it commutes with closed embeddings for the triples with `E = ∅`. -/
@[mmp "lem_kr3f_canonical_bp_properties"]
theorem canonicalPrincipalization_properties :
    (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).IsSmooth t.sX ∧
          (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersHaveSNCWith t.sX
            t.E.support) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        IsMonomialIdeal
          (t.I.comap (canonicalPrincipalization t (triples_subset_sncTriples ht)).toBase)) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (componentsOf t.E.support).Pairwise Disjoint →
          (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersLieOver (𝟙 t.X)
              (t.I.support : Set t.X) ∧
            IsIso ((canonicalPrincipalization t (triples_subset_sncTriples ht)).toBase ∣_
              t.I.support.compl)) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (canonicalPrincipalization t (triples_subset_sncTriples ht)).CentersLieOver (𝟙 t.X)
          ((t.I.support : Set t.X) ∪
            {x | ∃ C ∈ componentsOf t.E.support, ∃ C' ∈ componentsOf t.E.support,
              C ≠ C' ∧ x ∈ C ∧ x ∈ C'})) ∧
      CommutesWithSmoothOn triples
        (fun t ht => canonicalPrincipalization t (triples_subset_sncTriples ht)) ∧
      CommutesWithFieldChangeOn triples
        (fun t ht => canonicalPrincipalization t (triples_subset_sncTriples ht)) ∧
      ∀ d : ClosedEmbeddingData.{u}, d.E.s = 0 →
        ∀ (hX : d.ambientTriple ∈ triples) (hY : d.embeddedTriple ∈ triples),
          ClosedBlowupSequence.IsPushforward d.j
            (canonicalPrincipalization d.embeddedTriple (triples_subset_sncTriples hY))
            (canonicalPrincipalization d.ambientTriple (triples_subset_sncTriples hX)) := by
  obtain ⟨-, h1, h2, -, -, -, h6⟩ :=
    canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{u, u, u}
  refine ⟨h1, h2, fun t ht hdisj => ?_, fun _ => centersLieOver_union,
    canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{u, _, u}.2.2.2.2.1,
    canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{u, u, _}.2.2.2.2.2.1,
    h6⟩
  -- (3): with pairwise disjoint components `E^{(2)} = ∅`
  have hc := (centersLieOver_union ht).mono (Set.union_subset le_rfl
    fun x ⟨C, hC, C', hC', hne, hxC, hxC'⟩ =>
      (Set.disjoint_left.mp (hdisj hC hC' hne) hxC hxC').elim)
  exact ⟨hc, isIso_toBase_restrict_of_centersLieOver _ _ _ hc _
    (Set.disjoint_left.mpr fun _ hx hxV => hxV hx)⟩

/-! ### The empty divisor -/

/-- An empty family on a smooth scheme over a field is a simple normal crossing family: every
local ring is regular, hence has a regular system of parameters. -/
private theorem isSNCFamily_of_isEmpty {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] {Λ : Type*} [IsEmpty Λ] (E : Λ → Y.IdealSheafData) :
    IsSNCFamily f E := by
  refine ⟨isEmptyElim, fun x => ?_⟩
  have := isRegularLocalRing_stalk_of_smooth_over_field f x
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (Y.presheaf.stalk x)
  exact ⟨n, z, fun i => isEmptyElim i.1, hz, fun i => isEmptyElim i.1, fun i => isEmptyElim i.1⟩

/-- The empty ordered divisor on a smooth scheme over a field is an ordered snc divisor. -/
private theorem isOrderedSNC_empty {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] : (OrderedDivisor.empty X).IsOrderedSNC sX :=
  ⟨fun i => i.elim0, @isSNCFamily_of_isEmpty _ _ _ sX _ (Fin 0) inferInstance _⟩

/-- The empty ordered divisor has no irreducible components. -/
private theorem pairwise_disjoint_componentsOf_empty {X : Scheme.{u}} :
    (componentsOf (OrderedDivisor.empty X).support).Pairwise Disjoint := by
  intro C hC
  obtain ⟨x, hx⟩ := hC.1.1.nonempty
  obtain ⟨i, -⟩ := Set.mem_iUnion.1 (hC.1.2 hx)
  exact i.elim0

/-! ### The canonical principalization of the ideal of the origin -/

section OriginIdeal

/-- The ideal sheaf of a quasi-compact morphism from a reduced scheme is the vanishing ideal of
the closure of its image. -/
private theorem ker_eq_vanishingIdeal {X Y : Scheme.{u}} (f : Y ⟶ X) [IsReduced Y]
    [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f)) := by
  rw [← Set.image_univ, ← Scheme.IdealSheafData.map_bot]
  have := Scheme.IdealSheafData.map_vanishingIdeal f ⊤
  rwa [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot] at this

variable (k : Type u) [Field k] (c : ℕ)

/-- The global sections of `Spec k` form a field. -/
private theorem isField_Γ_Spec : IsField Γ(Spec (.of k), ⊤) :=
  (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)

/-- A coordinate function on `𝔸^c_k` is nonzero. -/
private theorem coord_ne_zero (i : ULift.{u} (Fin c)) :
    AffineSpace.coord (n := ULift.{u} (Fin c)) (Spec (.of k)) i ≠ 0 := by
  intro h
  have := (isField_Γ_Spec k).nontrivial
  have := AffineSpace.homOfVector_appTop_coord (𝟙 (Spec (.of k)))
    (Pi.single i (1 : Γ(Spec (.of k), ⊤))) i
  rw [h, map_zero, Pi.single_eq_same] at this
  exact zero_ne_one this

/-- The coordinates vanish at the origin. -/
private theorem coord_mem_ker (i : ULift.{u} (Fin c)) :
    AffineSpace.coord (n := ULift.{u} (Fin c)) (Spec (.of k)) i ∈
      RingHom.ker (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
        (𝟙 (Spec (.of k))) 0).appTop.hom := by
  rw [RingHom.mem_ker, AffineSpace.homOfVector_appTop_coord]
  rfl

/-- The ideal of the origin in the ring of functions on `𝔸^c_k`, `c ≥ 2`, has height at least
two: `0 ⊊ (x_0) ⊊ (x_0, …, x_{c-1})`, the middle prime being the kernel of the substitution
`x_0 ↦ 0`. -/
private theorem two_le_height_ker (hc : 2 ≤ c) :
    haveI := (isField_Γ_Spec k).isDomain
    haveI := RingHom.ker_isPrime (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).appTop.hom
    (2 : ℕ∞) ≤ (RingHom.ker (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).appTop.hom).height := by
  have := (isField_Γ_Spec k).isDomain
  have : IsDomain Γ(𝔸(ULift.{u} (Fin c); Spec (.of k)), ⊤) := inferInstance
  set X := 𝔸(ULift.{u} (Fin c); Spec (.of k))
  have hnt : Nontrivial Γ(X, ⊤) := IsDomain.toNontrivial
  have : (⊥ : Ideal Γ(X, ⊤)).IsPrime := Ideal.isPrime_bot
  set z₀ : Spec (.of k) ⟶ X := AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0
  set x : ULift.{u} (Fin c) → Γ(X, ⊤) := AffineSpace.coord (Spec (.of k))
  let i₀ : ULift.{u} (Fin c) := ⟨⟨0, by omega⟩⟩
  let i₁ : ULift.{u} (Fin c) := ⟨⟨1, by omega⟩⟩
  have hi : i₁ ≠ i₀ := fun h => absurd (congrArg (fun i => (i.down : ℕ)) h) (by simp [i₀, i₁])
  let v : ULift.{u} (Fin c) → Γ(X, ⊤) := fun i => if i = i₀ then 0 else x i
  let ψ : X ⟶ X := AffineSpace.homOfVector (X ↘ Spec (.of k)) v
  have hψ : z₀ ≫ ψ = z₀ := by
    refine AffineSpace.hom_ext (by
      rw [Category.assoc, AffineSpace.homOfVector_over])
      fun i => ?_
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord]
    have h0 : z₀.appTop.hom (x i) = 0 := coord_mem_ker k c i
    simp only [v]
    split_ifs
    · rw [map_zero, h0]
    · rfl
  set P := RingHom.ker z₀.appTop.hom
  set q := RingHom.ker ψ.appTop.hom
  have hP : P.IsPrime := RingHom.ker_isPrime _
  have hq : q.IsPrime := RingHom.ker_isPrime _
  have hψx : ∀ i, ψ.appTop.hom (x i) = v i := AffineSpace.homOfVector_appTop_coord _ _
  have hbq : ⊥ < q := by
    refine bot_lt_iff_ne_bot.mpr fun h => coord_ne_zero k c i₀ ?_
    have : x i₀ ∈ q := by rw [RingHom.mem_ker, hψx]; simp [v]
    rw [h] at this
    exact this
  have hqP : q < P := by
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => coord_ne_zero k c i₁ ?_
    · rw [RingHom.mem_ker] at hf ⊢
      rw [← hψ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_zero]
    · have : x i₁ ∈ q := h ▸ coord_mem_ker k c i₁
      rw [RingHom.mem_ker, hψx] at this
      simpa [v, hi] using this
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbq
  rw [Ideal.height_bot, zero_add] at h1
  calc (2 : ℕ∞) = 1 + 1 := rfl
    _ ≤ q.height + 1 := by gcongr
    _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hqP

/-- The stalk of `𝔪₀` at a point `y` of `𝔸^c_k` is generated by the germs of the functions
vanishing at the origin. -/
private theorem stalk_ker_eq_map (y : 𝔸(ULift.{u} (Fin c); Spec (.of k))) :
    IdealSheafData.stalk (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).ker y =
      (RingHom.ker (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
        (𝟙 (Spec (.of k))) 0).appTop.hom).map
        ((𝔸(ULift.{u} (Fin c); Spec (.of k))).presheaf.germ ⊤ y trivial).hom := by
  rw [IdealSheafData.stalk_eq_map_germ _ y ⟨⊤, isAffineOpen_top _⟩ trivial,
    Scheme.ker_of_isAffine]
  congr 1
  exact (Scheme.IdealSheafData.equivOfIsAffine).apply_symm_apply _

/-- The prime ideal of the origin `z₀(p)` of `𝔸^c_k` is the kernel of `z₀^*`. -/
private theorem primeIdealOf_origin (p : Spec (.of k)) :
    ((isAffineOpen_top (𝔸(ULift.{u} (Fin c); Spec (.of k)))).primeIdealOf
      ⟨AffineSpace.homOfVector (n := ULift.{u} (Fin c)) (𝟙 (Spec (.of k))) 0 p,
        trivial⟩).asIdeal =
      RingHom.ker (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
        (𝟙 (Spec (.of k))) 0).appTop.hom := by
  rw [← IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _)
    (by simp) (show p ∈ (⊤ : (Spec (.of k)).Opens) from trivial), PrimeSpectrum.comap_asIdeal]
  let := (isField_Γ_Spec k).toField
  have hb := Ideal.eq_bot_of_prime
    ((isAffineOpen_top (Spec (.of k))).primeIdealOf ⟨p, trivial⟩).asIdeal
  rw [hb, ← RingHom.ker_eq_comap_bot]
  rfl

/-- For `c ≥ 2` the ideal `𝔪₀` of the origin of `𝔸^c_k` is not monomial: at the origin it is
the maximal ideal of a Noetherian local ring of dimension `≥ 2`, which by Krull's height theorem
is not principal. -/
private theorem not_isMonomialIdeal_ker (hc : 2 ≤ c) :
    ¬ IsMonomialIdeal (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).ker := by
  intro h
  have h2 := two_le_height_ker k c hc
  have := (isField_Γ_Spec k).isDomain
  set X := 𝔸(ULift.{u} (Fin c); Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  set z₀ : Spec (.of k) ⟶ X := AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0
  set P := RingHom.ker z₀.appTop.hom
  have : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨n, z, e, -, hst⟩ := h (z₀ p)
  let := X.presheaf.algebra_section_stalk (⟨z₀ p, trivial⟩ : (⊤ : X.Opens))
  have : IsLocalization.AtPrime (X.presheaf.stalk (z₀ p)) P := by
    convert (isAffineOpen_top X).isLocalization_stalk ⟨z₀ p, trivial⟩
    exact (primeIdealOf_origin k c p).symm
  have hm := IsLocalization.AtPrime.map_eq_maximalIdeal P (X.presheaf.stalk (z₀ p))
  rw [stalk_ker_eq_map] at hst
  change P.map (algebraMap Γ(X, ⊤) (X.presheaf.stalk (z₀ p))) = _ at hst
  have hspan : IsLocalRing.maximalIdeal (X.presheaf.stalk (z₀ p)) =
      Ideal.span {∏ i, z i ^ e i} := hm.symm.trans hst
  have hle : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z₀ p))).height ≤ 1 :=
    have : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z₀ p))).IsPrincipal := hspan ▸ ⟨_, rfl⟩
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (z₀ p))) _
      (by simp [Ideal.minimalPrimes_eq_subsingleton_self])
  have : P.height ≤ 1 := by
    rw [← WithBot.coe_le_coe, ← IsLocalization.AtPrime.ringKrullDim_eq_height P
      (X.presheaf.stalk (z₀ p)), ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr hle
  exact absurd (h2.trans this) (by norm_num)

/-- `(𝔸^c_k, 𝔪₀, ∅)` is a triple of Kollár's Notation 3.64 for `k` of characteristic `0` and
`c ≥ 1`. -/
private theorem mem_triples [CharZero k] (hc : 1 ≤ c) :
    (⟨⟨𝔸(ULift.{u} (Fin c); Spec (.of k)),
      (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker, OrderedDivisor.empty _⟩, k,
      𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)⟩ : FieldBlowupTriple.{u}) ∈ triples := by
  set X := 𝔸(ULift.{u} (Fin c); Spec (.of k))
  have : Smooth (X ↘ Spec (.of k)) := smooth_affineSpace_over _ _
  refine ⟨‹_›, isSmoothScheme_of_smooth _, inferInstance, inferInstance,
    TopologicalSpace.Equidimensional.of_preirreducibleSpace _, fun η _ hbot => ?_,
    isOrderedSNC_empty _⟩
  let i₀ : ULift.{u} (Fin c) := ⟨⟨0, by omega⟩⟩
  have hmem := Ideal.mem_map_of_mem (X.presheaf.germ ⊤ η trivial).hom (coord_mem_ker k c i₀)
  rw [← stalk_ker_eq_map, hbot, Ideal.mem_bot, ← map_zero (X.presheaf.germ ⊤ η trivial).hom]
    at hmem
  exact coord_ne_zero k c i₀ (germ_injective_of_isIntegral X (U := ⊤) η trivial hmem)

/-- A smooth nonempty closed subscheme of `𝔸^c_k` supported in the origin is the reduced
origin. -/
private theorem eq_ker_of_isSmoothScheme (Z : (𝔸(ULift.{u} (Fin c); Spec (.of k))).IdealSheafData)
    (hZ : Z ≠ ⊤)
    (hsm : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘
      Spec (.of k)))
    (hsub : (Z.support : Set (𝔸(ULift.{u} (Fin c); Spec (.of k)))) ⊆
      ((AffineSpace.homOfVector (n := ULift.{u} (Fin c)) (𝟙 (Spec (.of k))) 0).ker.support :
        Set (𝔸(ULift.{u} (Fin c); Spec (.of k))))) :
    Z = (AffineSpace.homOfVector (n := ULift.{u} (Fin c)) (𝟙 (Spec (.of k))) 0).ker := by
  have := Aux.isReduced_subscheme_of_isSmoothScheme
    (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) Z hsm
  set z₀ : Spec (.of k) ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k)) :=
    AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0
  have : IsClosedImmersion (z₀ ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) := by
    rw [AffineSpace.homOfVector_over]; infer_instance
  have : IsClosedImmersion z₀ :=
    IsClosedImmersion.of_comp z₀ (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k))
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  have hrange : Set.range z₀ = {z₀ p} := by
    refine Set.ext fun y => ⟨?_, fun hy => ⟨p, hy.symm⟩⟩
    rintro ⟨q, rfl⟩
    rw [Subsingleton.elim q p]
    rfl
  have hsupp : ((z₀.ker.support : Set (𝔸(ULift.{u} (Fin c); Spec (.of k))))) = {z₀ p} := by
    rw [Scheme.Hom.support_ker, hrange, closure_eq_iff_isClosed, ← hrange]
    exact z₀.isClosedEmbedding.isClosed_range
  have hZs : (Z.support : Set (𝔸(ULift.{u} (Fin c); Spec (.of k)))) = {z₀ p} := by
    refine (Set.subset_singleton_iff_eq.mp (hsub.trans hsupp.le)).resolve_left fun h => hZ ?_
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    exact SetLike.coe_injective h
  rw [← Scheme.IdealSheafData.ker_subschemeι Z, ker_eq_vanishingIdeal, ker_eq_vanishingIdeal]
  congr 1
  refine SetLike.coe_injective ?_
  simp only [Closeds.coe_closure]
  rw [Scheme.IdealSheafData.range_subschemeι, hZs, hrange]

/-- A blow-up sequence of `𝔸^c_k`, `c ≥ 2`, without empty blow-ups, smooth, principalizing
`𝔪₀` to a monomial ideal and with centres over the origin begins with the blow-up of the reduced
origin. -/
private theorem eq_cons_ker (hc : 2 ≤ c)
    (B : ClosedBlowupSequence (𝔸(ULift.{u} (Fin c); Spec (.of k))))
    (hne : B.HasNoEmptyBlowups) (hsm : B.IsSmooth (𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘
      Spec (.of k)))
    (hmono : IsMonomialIdeal ((AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).ker.comap B.toBase))
    (hlie : B.CentersLieOver (𝟙 _) ((AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).ker.support : Set (𝔸(ULift.{u} (Fin c); Spec (.of k))))) :
    ∃ B' : ClosedBlowupSequence (blowUp (AffineSpace.homOfVector (n := ULift.{u} (Fin c))
        (𝟙 (Spec (.of k))) 0).ker),
      B = .cons (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker B' := by
  cases B with
  | nil =>
    change IsMonomialIdeal ((AffineSpace.homOfVector (n := ULift.{u} (Fin c))
      (𝟙 (Spec (.of k))) 0).ker.comap (𝟙 _)) at hmono
    rw [Scheme.IdealSheafData.comap_id] at hmono
    exact absurd hmono (not_isMonomialIdeal_ker k c hc)
  | cons Z B' =>
    obtain ⟨-, hZsm, -⟩ := hsm
    obtain ⟨hZlie, -⟩ := hlie
    obtain rfl := eq_ker_of_isSmoothScheme k c Z hne.1 hZsm (by simpa using hZlie)
    exact ⟨B', rfl⟩

/-- **Kollár, p. 139.** Let `k` be a field of characteristic `0`, `2 ≤ c`, and `𝔪₀` the ideal
of the origin of `𝔸^c_k` (the kernel of the zero section `AffineSpace.homOfVector (𝟙 _) 0`). Then
`(𝔸^c_k, 𝔪₀, ∅)` lies in `MMP.Resolution.triples`, and after deleting its empty blow-ups
(`ClosedBlowupSequence.reduction`), `𝓑𝓟^can(𝔸^c_k, 𝔪₀, ∅)`
(`MMP.Resolution.canonicalPrincipalization`) begins with the blow-up of the reduced origin `𝔪₀`. -/
@[mmp "lem_kr3f_bp_of_maximal_ideal_of_origin"]
theorem exists_reduction_canonicalPrincipalization_eq_cons_ker_origin
    (k : Type u) [Field k] [CharZero k] {c : ℕ} (hc : 2 ≤ c) :
    ∃ ht : (⟨⟨𝔸(ULift.{u} (Fin c); Spec (.of k)),
          (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker,
          OrderedDivisor.empty _⟩, k,
          𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)⟩ : FieldBlowupTriple.{u}) ∈ triples,
      ∃ B' : ClosedBlowupSequence (blowUp (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker),
        (canonicalPrincipalization _ (triples_subset_sncTriples ht)).reduction =
          .cons (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker B' := by
  have ht := mem_triples k c (by omega)
  refine ⟨ht, ?_⟩
  have hprop := canonicalPrincipalization_properties.{u, u, u}
  have hne :=
    canonicalPrincipalization_isPrincipalizationFunctorAwayFromDoubleLocus.{u, u, u}.1 _ ht
  obtain ⟨B', hB'⟩ := eq_cons_ker k c hc _ hne (hprop.1 _ ht).1 (hprop.2.1 _ ht)
    (hprop.2.2.1 _ ht pairwise_disjoint_componentsOf_empty).1
  exact ⟨B', (ClosedBlowupSequence.reduction_eq_self hne).trans hB'⟩

end OriginIdeal

section Varieties

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The stages of `𝓑𝓟^can` of a smooth variety -/

/-- On an integral scheme, a nonzero ideal sheaf has nonzero stalk at the generic point. -/
private theorem stalk_genericPoint_ne_bot {X : Scheme.{u}} [IsIntegral X] {I : X.IdealSheafData}
    (hI : I ≠ ⊥) : IdealSheafData.stalk I (genericPoint X) ≠ ⊥ := by
  intro h
  refine hI (Scheme.IdealSheafData.ext (funext fun U => ?_))
  rw [Scheme.IdealSheafData.ideal_bot]
  refine eq_bot_iff.mpr fun a ha => (Ideal.mem_bot).mpr ?_
  by_cases hU : genericPoint X ∈ (U : X.Opens)
  · have hmem := Ideal.mem_map_of_mem (X.presheaf.germ (U : X.Opens) _ hU).hom ha
    rw [← IdealSheafData.stalk_eq_map_germ I _ U hU, h, Ideal.mem_bot] at hmem
    exact germ_injective_of_isIntegral X _ hU (hmem.trans (map_zero _).symm)
  · have hbot : (U : X.Opens) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => hU ?_
      exact ((genericPoint_spec X).mem_open_set_iff (U : X.Opens).isOpen).mpr ⟨x, trivial, hx⟩
    exact @Subsingleton.elim _
      (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)) _ _

/-- On an integral scheme, a nonzero ideal sheaf does not vanish at the generic point. -/
private theorem genericPoint_notMem_support {X : Scheme.{u}} [IsIntegral X]
    {I : X.IdealSheafData} (hI : I ≠ ⊥) : genericPoint X ∉ (I.support : Set X) := by
  intro h
  refine hI (Scheme.IdealSheafData.support_eq_top_iff.mp (eq_top_iff.mpr fun x _ => ?_))
  exact ((genericPoint_spec X).mem_closed_set_iff I.support.isClosed).mp h (Set.mem_univ x)

/-- The identity is birational. -/
private theorem isBirational_id {X : Scheme.{u}} : IsBirational (𝟙 X) := by
  refine ⟨Set.bijOn_id _, fun x _ => ?_⟩
  rw [Scheme.Hom.stalkMap_id]
  exact IsIso.id _

/-- A proper birational morphism between smooth varieties over a field is a birational
morphism. -/
private theorem isBirationalMorphism_of_isBirational {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsProper f] (hX : AlgebraicGeometry.IsVariety k sX)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) (hsX : IsSmoothScheme sX)
    (hsY : IsSmoothScheme (f ≫ sX)) (hb : IsBirational f) : IsBirationalMorphism f := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : LocallyOfFinitePresentation sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  have : Smooth sX := (isSmoothScheme_iff _).1 hsX
  have : Smooth (f ≫ sX) := (isSmoothScheme_iff _).1 hsY
  have : IsNormal X := isNormal_of_smooth_over_field sX
  have : IsNormal Y := isNormal_of_smooth_over_field (f ≫ sX)
  simpa using isBirationalMorphism_comp_of_isBirational f (𝟙 _) hb isBirational_id

/-- The stages of a smooth blow-up sequence over a variety `Y → X`, whose centres lie over a
closed subset `S ⊆ X` missing the generic point, are smooth varieties birational over `X`. -/
private theorem isVariety_and_isBirational_truncate {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) (S : Set X) (hS : genericPoint X ∉ S) :
    ∀ {Y : Scheme.{u}} (B : ClosedBlowupSequence Y) (f : Y ⟶ X),
      AlgebraicGeometry.IsVariety k (f ≫ sX) → IsBirational f → IsSmoothScheme (f ≫ sX) →
      B.IsSmooth (f ≫ sX) → B.CentersLieOver f S → ∀ i : ℕ,
      AlgebraicGeometry.IsVariety k ((B.truncate i).toBase ≫ f ≫ sX) ∧
        IsBirational ((B.truncate i).toBase ≫ f) ∧ IsSmoothScheme ((B.truncate i).toBase ≫ f ≫ sX)
  | _, .nil _, f, hv, hb, hs, _, _, _ => by
    simpa [ClosedBlowupSequence.truncate, ClosedBlowupSequence.toBase] using ⟨hv, hb, hs⟩
  | _, .cons Z B, f, hv, hb, hs, _, _, 0 => by
    simpa [ClosedBlowupSequence.truncate, ClosedBlowupSequence.toBase] using ⟨hv, hb, hs⟩
  | Y, .cons Z B, f, hv, hb, hs, ⟨_, hZsm, hBsm⟩, ⟨hZS, hBS⟩, i + 1 => by
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      have : IsIntegral Y := hv.toIsIntegral
      obtain ⟨y, -, hy⟩ := hb.1.surjOn (show genericPoint X ∈ genericPoints X by
        rw [genericPoints_eq_singleton]; rfl)
      exact hS (hZS ⟨y, by simp [Scheme.IdealSheafData.support_bot], hy⟩)
    have := hv
    obtain ⟨hv', -, hb'⟩ :=
      MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
        (f ≫ sX) Z hZ
    have hsm' := (Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (f ≫ sX) Z
      ⟨hs, hZsm⟩).1
    have := isVariety_and_isBirational_truncate sX S hS B (blowUpToBase Z ≫ f)
      (by rwa [Category.assoc]) (hb'.comp hb)
      (by rw [Category.assoc]; exact isSmoothScheme_of_smooth _) (by rwa [Category.assoc]) hBS i
    rw [show ((ClosedBlowupSequence.cons Z B).truncate (i + 1)).toBase ≫ f ≫ sX =
        (B.truncate i).toBase ≫ blowUpToBase Z ≫ f ≫ sX from Category.assoc _ _ _,
      show ((ClosedBlowupSequence.cons Z B).truncate (i + 1)).toBase ≫ f =
        (B.truncate i).toBase ≫ blowUpToBase Z ≫ f from Category.assoc _ _ _]
    exact this

/-- **Kollár, p. 139.** Let `X` be a smooth variety over a field `k` of characteristic `0` and
`I ≠ ⊥` an ideal sheaf on `X`. Then `(X, I, ∅)` is a triple of Notation 3.64
(`MMP.Resolution.triples`), and for every stage `X_i` of `𝓑𝓟^can(X, I, ∅)`
(`MMP.Resolution.canonicalPrincipalization`), `X_i` is a smooth variety and the composite
`Π_i : X_i → X` is projective and birational. -/
@[mmp "lem_kr3f_bp_sequence_of_variety"]
theorem isVariety_and_isProjective_toBase_truncate_canonicalPrincipalization
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (hX : AlgebraicGeometry.IsVariety k sX) (hsm : IsSmoothScheme sX) (I : X.IdealSheafData)
    (hI : I ≠ ⊥) :
    ∃ ht : (⟨⟨X, I, OrderedDivisor.empty X⟩, k, sX⟩ : FieldBlowupTriple.{u}) ∈ triples,
      ∀ i : ℕ,
        AlgebraicGeometry.IsVariety k
            (((canonicalPrincipalization _ (triples_subset_sncTriples ht)).truncate i).toBase ≫
              sX) ∧
          AlgebraicGeometry.IsProjective
            ((canonicalPrincipalization _ (triples_subset_sncTriples ht)).truncate i).toBase ∧
          IsBirationalMorphism
            ((canonicalPrincipalization _ (triples_subset_sncTriples ht)).truncate i).toBase ∧
          IsSmoothScheme
            (((canonicalPrincipalization _ (triples_subset_sncTriples ht)).truncate i).toBase ≫
              sX) := by
  have : IsIntegral X := hX.toIsIntegral
  have ht : (⟨⟨X, I, OrderedDivisor.empty X⟩, k, sX⟩ : FieldBlowupTriple.{u}) ∈ triples := by
    have : Smooth sX := hsm.smooth
    refine ⟨inferInstance, hsm, inferInstance, inferInstance,
      TopologicalSpace.Equidimensional.of_preirreducibleSpace X, fun η hη => ?_,
      isOrderedSNC_empty sX⟩
    have hgen : IsGenericPoint η (⊤ : Set X) :=
      hη.eq_of_le (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)
    rw [hgen.eq (genericPoint_spec X)]
    exact stalk_genericPoint_ne_bot hI
  refine ⟨ht, fun i => ?_⟩
  obtain ⟨hprop1, -, hprop3, -⟩ := canonicalPrincipalization_properties.{u, u, u}
  obtain ⟨hv, hb, hs⟩ := isVariety_and_isBirational_truncate sX (I.support : Set X)
    (genericPoint_notMem_support hI)
    (canonicalPrincipalization _ (triples_subset_sncTriples ht)) (𝟙 X)
    (by rwa [Category.id_comp]) isBirational_id (by rwa [Category.id_comp])
    (by rw [Category.id_comp]; exact (hprop1 _ ht).1)
    (hprop3 _ ht pairwise_disjoint_componentsOf_empty).1 i
  rw [Category.id_comp] at hv hs
  rw [Category.comp_id] at hb
  have : AlgebraicGeometry.IsNoetherian X :=
    @AlgebraicGeometry.IsNoetherian.mk _ (LocallyOfFiniteType.isLocallyNoetherian sX)
      (QuasiCompact.compactSpace_of_compactSpace sX)
  have hproj := ClosedBlowupSequence.isProjective_toBase
    ((canonicalPrincipalization _ (triples_subset_sncTriples ht)).truncate i)
  have := hproj.isProper
  exact ⟨hv, hproj, isBirationalMorphism_of_isBirational sX _ hX hv hsm hs hb, hs⟩

/-! ### `𝓑𝓟^can` near a smooth point of the centre -/

open ClosedBlowupSequence

/-! ### Blowing up a centre disjoint from an open immersion -/

/-- If the comap of `Z` along `g` is the unit ideal sheaf, `g` misses the support of `Z`. -/
theorem notMem_support_of_comap_eq_top {X Y : Scheme.{u}} {Z : X.IdealSheafData} (g : Y ⟶ X)
    (hZ : Z.comap g = ⊤) (y : Y) : g y ∉ (Z.support : Set X) := by
  intro hy
  have : y ∈ ((Z.comap g).support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hy
  rw [hZ, Scheme.IdealSheafData.support_top] at this
  exact this

/-- If the centre `Z` misses the image of an open immersion `g`, the lift of `g` to `B_Z X` is an
open immersion whose image contains the inverse image of the image of `g`. -/
private theorem isOpenImmersion_blowUpLift_and_preimage_range_subset_range {X Y : Scheme.{u}}
    (Z : X.IdealSheafData) (g : Y ⟶ X) [IsOpenImmersion g] (hZ : Z.comap g = ⊤) :
    IsOpenImmersion (blowUpLift Z g (isCartierOver_of_comap_eq_top g Z hZ)) ∧
      blowUpToBase Z ⁻¹' Set.range g ⊆
        Set.range (blowUpLift Z g (isCartierOver_of_comap_eq_top g Z hZ)) := by
  set π := blowUpToBase Z
  set g' := blowUpLift Z g (isCartierOver_of_comap_eq_top g Z hZ)
  have hg' : g' ≫ π = g := blowUpLift_comp _ _ _
  let V₀ : X.Opens := ⟨(Z.support : Set X)ᶜ, Z.support.isClosed.isOpen_compl⟩
  have hgV : ∀ y, g y ∈ V₀ := notMem_support_of_comap_eq_top g hZ
  have hiso : IsIso (π ∣_ V₀) := isIso_blowUp_restrict_compl_support Z
  have hπg : ∀ y, π (g' y) = g y := fun y => by rw [← Scheme.Hom.comp_apply, hg']
  have hinj : ∀ p q : blowUp Z, π p ∈ V₀ → π p = π q → p = q := by
    intro p q hp hpq
    have hq : q ∈ π ⁻¹ᵁ V₀ := by change π q ∈ V₀; rw [← hpq]; exact hp
    have := (π ∣_ V₀).isOpenEmbedding.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩)
      (Subtype.ext ((morphismRestrict_base_coe π V₀ ⟨p, hp⟩).trans
        (hpq.trans (morphismRestrict_base_coe π V₀ ⟨q, hq⟩).symm)))
    exact congrArg Subtype.val this
  refine ⟨?_, ?_⟩
  · have hr : Set.range g' ⊆ Set.range (π ⁻¹ᵁ V₀).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      change π (g' y) ∈ V₀
      rw [hπg]; exact hgV y
    set g₀ := IsOpenImmersion.lift (π ⁻¹ᵁ V₀).ι g' hr
    have hg₀ : g₀ ≫ (π ⁻¹ᵁ V₀).ι = g' := IsOpenImmersion.lift_fac _ _ _
    have h1 : (g₀ ≫ (π ∣_ V₀)) ≫ V₀.ι = g := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg₀, hg']
    have : IsOpenImmersion ((g₀ ≫ (π ∣_ V₀)) ≫ V₀.ι) := by rw [h1]; infer_instance
    have : IsOpenImmersion (g₀ ≫ (π ∣_ V₀)) := IsOpenImmersion.of_comp _ V₀.ι
    have : IsOpenImmersion g₀ := by
      have e : g₀ = (g₀ ≫ (π ∣_ V₀)) ≫ inv (π ∣_ V₀) := by simp
      rw [e]; infer_instance
    rw [← hg₀]; infer_instance
  · rintro p ⟨y, hy⟩
    refine ⟨y, hinj _ _ ?_ ?_⟩
    · rw [hπg]; exact hgV y
    · rw [hπg]; exact hy

/-! ### Codimension and generic points -/

/-- If every irreducible closed subset of a closed set `S` has codimension `≥ 1`, every irreducible
closed subset `Y ⊆ S` lies strictly inside another irreducible closed subset. -/
private theorem exists_lt_of_one_le_closedsCodimension {T : Type*} [TopologicalSpace T]
    {S : Closeds T} (hS : 1 ≤ closedsCodimension S) (Y : IrreducibleCloseds T)
    (hYS : (Y : Set T) ⊆ S) : ∃ Y₁ : IrreducibleCloseds T, Y < Y₁ := by
  obtain ⟨p, hhead, hlen⟩ :=
    (codimension_iff_exists_chain Y 1).1 (by simpa using le_closedsCodimension_iff.mp hS Y hYS)
  refine ⟨p.last, ?_⟩
  rw [← hhead]
  exact p.strictMono (by rw [Fin.lt_def]; simp [hlen])

/-- An irreducible component of `T` does not lie in a closed set all of whose irreducible closed
subsets have codimension `≥ 1`. -/
private theorem notMem_of_mem_irreducibleComponents {T : Type*} [TopologicalSpace T]
    {S : Closeds T} (hS : 1 ≤ closedsCodimension S) {ξ : T}
    (hξ : closure {ξ} ∈ irreducibleComponents T) : ξ ∉ (S : Set T) := by
  intro hξS
  obtain ⟨Y₁, hlt⟩ := exists_lt_of_one_le_closedsCodimension hS
    ⟨closure {ξ}, hξ.1, isClosed_closure⟩
    (closure_minimal (Set.singleton_subset_iff.2 hξS) S.isClosed)
  exact hlt.not_ge (show (Y₁ : Set T) ⊆ closure {ξ} from
    hξ.2 Y₁.isIrreducible (show closure {ξ} ⊆ (Y₁ : Set T) from hlt.le))

/-- No irreducible closed subset of a closed set all of whose irreducible closed subsets have
codimension `≥ 1` contains a nonempty open set. -/
private theorem not_subset_of_one_le_closedsCodimension {T : Type*} [TopologicalSpace T]
    {S : Closeds T} (hS : 1 ≤ closedsCodimension S) (Y : IrreducibleCloseds T)
    (hYS : (Y : Set T) ⊆ S) {O : Set T} (hO : IsOpen O) (hOne : O.Nonempty) :
    ¬ O ⊆ Y := by
  intro hOY
  obtain ⟨Y₁, hlt⟩ := exists_lt_of_one_le_closedsCodimension hS Y hYS
  have hYY₁ : (Y : Set T) ⊆ Y₁ := hlt.le
  refine hlt.not_ge (show (Y₁ : Set T) ⊆ Y from fun y hy => ?_)
  by_contra hyY
  obtain ⟨o, ho⟩ := hOne
  obtain ⟨z, -, hzO, hzY⟩ := Y₁.isIrreducible.2 O (Y : Set T)ᶜ hO Y.isClosed.isOpen_compl
    ⟨o, hYY₁ (hOY ho), ho⟩ ⟨y, hy, hyY⟩
  exact hzY (hOY hzO)

/-- A point of a scheme whose closure has codimension `≥ 2` has coheight `≥ 2` in the
specialization order. -/
private theorem two_le_coheight_of_two_le_codimension {X : Scheme.{u}} {η : X}
    (h : 2 ≤ codimension (⟨closure {η}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      IrreducibleCloseds X)) : 2 ≤ Order.coheight η := by
  obtain ⟨p, hhead, hlen⟩ := (codimension_iff_exists_chain _ 2).1 h
  let i₀ : Fin (p.length + 1) := ⟨0, by omega⟩
  let i₁ : Fin (p.length + 1) := ⟨1, by omega⟩
  let i₂ : Fin (p.length + 1) := ⟨2, by omega⟩
  have l₀₁ : p i₀ < p i₁ := p.strictMono (by rw [Fin.lt_def]; simp [i₀, i₁])
  have l₁₂ : p i₁ < p i₂ := p.strictMono (by rw [Fin.lt_def]; simp [i₁, i₂])
  have h₀ : p i₀ = p.head := congrArg p (Fin.ext (by simp [i₀]))
  rw [h₀, hhead] at l₀₁
  obtain ⟨y₁, hy₁⟩ := QuasiSober.sober (p i₁).isIrreducible (p i₁).isClosed
  obtain ⟨y₂, hy₂⟩ := QuasiSober.sober (p i₂).isIrreducible (p i₂).isClosed
  have hlt : ∀ {a b : X}, closure {a} ⊂ closure {b} → a < b := fun h => by
    simpa only [lt_iff_le_not_ge, Scheme.le_iff_specializes, specializes_iff_closure_subset]
      using h
  have e₁ : η < y₁ := hlt (by rw [hy₁.def]; exact l₀₁)
  have e₂ : y₁ < y₂ := hlt (by rw [hy₁.def, hy₂.def]; exact l₁₂)
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight y₂ + 1 + 1 := by gcongr; exact bot_le
    _ ≤ Order.coheight y₁ + 1 := by gcongr; exact Order.coheight_add_one_le e₂
    _ ≤ Order.coheight η := Order.coheight_add_one_le e₁

/-- Maximality of `closure {e a}` among the irreducible subsets of a closed set `S` passes to
`closure {a}` and `e⁻¹ S` along an open embedding `e`. -/
private theorem maximal_closure_singleton_preimage {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {e : A → B} (he : Topology.IsOpenEmbedding e) {S : Set B}
    (hS : IsClosed S) {a : A}
    (h : Maximal (fun s : Set B => IsIrreducible s ∧ s ⊆ S) (closure {e a})) :
    Maximal (fun s : Set A => IsIrreducible s ∧ s ⊆ e ⁻¹' S) (closure {a}) := by
  have hcl : closure {a} = e ⁻¹' closure {e a} := by
    rw [he.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
  refine ⟨⟨isIrreducible_singleton.closure, ?_⟩, ?_⟩
  · rw [hcl]; exact Set.preimage_mono h.prop.2
  · rintro s ⟨hs, hsS⟩ has
    have hirr : IsIrreducible (closure (e '' s)) :=
      (hs.image e he.continuous.continuousOn).closure
    have hsub : closure (e '' s) ⊆ S := closure_minimal (Set.image_subset_iff.2 hsS) hS
    have hle : closure {e a} ⊆ closure (e '' s) :=
      closure_mono (Set.singleton_subset_iff.2 ⟨a, has (subset_closure rfl), rfl⟩)
    have := h.2 ⟨hirr, hsub⟩ hle
    rw [hcl]
    exact fun y hy => this (subset_closure ⟨y, hy, rfl⟩)

/-- **Krull's height theorem, geometric form.** On a locally noetherian scheme, if
`closure {η}` is an irreducible component of the support of `I`, then the coheight of `η` is at
most the number of generators of `I` on any affine open containing `η`. -/
private theorem coheight_le_spanRank_ideal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {η : X}
    (hη : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X)) (closure {η}))
    (W : X.affineOpens) (hηW : η ∈ W.1) :
    Order.coheight η ≤ Cardinal.toENat (Submodule.spanRank (I.ideal W)) := by
  have hW : IsAffineOpen W.1 := W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  set x := hW.primeIdealOf ⟨η, hηW⟩ with hx_def
  have hx : hW.fromSpec x = η := hW.fromSpec_primeIdealOf ⟨η, hηW⟩
  -- a point of `Spec Γ(X, W)` lies over the support iff it contains `I(W)`
  have hsupp : ∀ y : Spec Γ(X, W.1),
      hW.fromSpec y ∈ (I.support : Set X) ↔ (I.ideal W : Set Γ(X, W.1)) ⊆ y.asIdeal := by
    intro y
    have hyW : hW.fromSpec y ∈ W.1 := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨y, rfl⟩
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hyW]
    rw [← Set.mem_preimage, hW.fromSpec_preimage_zeroLocus]
    rfl
  have hηsupp : η ∈ (I.support : Set X) := hη.prop.2 (subset_closure rfl)
  have hmin : x.asIdeal ∈ (I.ideal W).minimalPrimes := by
    refine ⟨⟨x.isPrime, (hsupp x).mp (hx ▸ hηsupp)⟩, ?_⟩
    rintro q ⟨hq, hJq⟩ hqx
    let y : Spec Γ(X, W.1) := ⟨q, hq⟩
    have hyx : y ⤳ x := (PrimeSpectrum.le_iff_specializes y x).mp hqx
    have hyη : hW.fromSpec y ⤳ η := hx ▸ hyx.map (hW.fromSpec).continuous
    have hysupp : hW.fromSpec y ∈ (I.support : Set X) := (hsupp y).mpr hJq
    have hcl : closure {hW.fromSpec y} ⊆ closure {η} := by
      refine hη.2 ⟨isIrreducible_singleton.closure, ?_⟩
        (specializes_iff_closure_subset.mp hyη)
      exact (I.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hysupp)
    have hηy : η ⤳ hW.fromSpec y := specializes_iff_closure_subset.mpr hcl
    rw [← hx] at hηy
    have hxy : x ⤳ y := hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hηy
    exact (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hle := Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ hmin
  rwa [idealHeight_eq_coheight _ x,
    show Order.coheight (α := Spec Γ(X, W.1)) x = Order.coheight η from
      (coheight_eq_of_isOpenImmersion (x := x) hW.fromSpec).symm.trans (congrArg _ hx)] at hle

/-- A point at which the stalk of an ideal sheaf vanishes lies in its support. -/
private theorem mem_support_of_stalk_eq_bot {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (h : IdealSheafData.stalk I x = ⊥) : x ∈ (I.support : Set X) := by
  by_contra hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have hx' : x ∉ X.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
    rwa [← Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU]
  rw [Scheme.mem_zeroLocus_iff] at hx'
  push Not at hx'
  obtain ⟨f, hf, hfx⟩ := hx'
  rw [Scheme.mem_basicOpen _ _ _ hxU] at hfx
  have hmem : (X.presheaf.germ U x hxU).hom f ∈ IdealSheafData.stalk I x := by
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU]
    exact Ideal.mem_map_of_mem _ hf
  rw [h, Ideal.mem_bot] at hmem
  rw [hmem] at hfx
  exact not_isUnit_zero hfx

/-! ### Smooth schemes -/

/-- Every point of a scheme smooth over a field has an irreducible open neighbourhood. -/
private theorem exists_isIrreducible_mem_opens {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    ∃ K : X.Opens, x ∈ K ∧ IsIrreducible (K : Set X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal X := isNormal_of_smooth f
  obtain ⟨ι, Y, -, hI, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct_integral_normal X).1 inferInstance
  let h : X ≃ₜ (Σ i, Y i) := e.hom.homeomorph.trans (sigmaMk Y).symm
  set p := h x with hp
  set P : Set X := h ⁻¹' Set.range (@Sigma.mk ι (fun i => Y i) p.1) with hP
  have hPc : IsClopen P := isClopen_range_sigmaMk.preimage h.continuous
  have hPirr : IsIrreducible P := by
    have := hI p.1
    have hR : IsIrreducible (Set.range (@Sigma.mk ι (fun i => Y i) p.1)) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ continuous_sigmaMk.continuousOn
    rw [hP, ← Homeomorph.image_symm]
    exact hR.image _ h.symm.continuous.continuousOn
  exact ⟨⟨P, hPc.isOpen⟩, ⟨p.2, rfl⟩, hPirr⟩

section Origin

open MvPolynomial

/-- Over an affine base, the global sections of `𝔸(n; S)` are the polynomials in the
coordinates. -/
private theorem bijective_eval₂Hom_coord (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    Function.Bijective
      (eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord (n := n) S)) := by
  have : IsIso (AffineSpace.isoOfIsAffine n S).hom.appTop :=
    inferInstanceAs (IsIso ((AffineSpace.isoOfIsAffine n S).hom.app ⊤))
  have h1 := ConcreteCategory.bijective_of_isIso (AffineSpace.isoOfIsAffine n S).hom.appTop
  have h2 := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso
    (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).inv
  have := h1.comp h2
  rw [AffineSpace.isoOfIsAffine_hom_appTop] at this
  convert this using 1
  ext q
  simp only [Function.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

/-- The functions on `𝔸(n; S)` vanishing on the zero section of an affine base `S` form the
ideal generated by the coordinates. -/
private theorem ker_appTop_homOfVector_zero (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    RingHom.ker (AffineSpace.homOfVector (n := n) (𝟙 S) 0).appTop.hom =
      Ideal.span (Set.range (AffineSpace.coord S)) := by
  set φ := eval₂Hom ((𝔸(n; S) ↘ S).appTop).hom (AffineSpace.coord (n := n) S)
  have hφ := bijective_eval₂Hom_coord n S
  have hcomp : (AffineSpace.homOfVector (n := n) (𝟙 S) 0).appTop.hom.comp φ =
      eval₂Hom (RingHom.id _) 0 := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
    · simp only [RingHom.comp_apply, φ, eval₂Hom_C, RingHom.id_apply]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
      rfl
    · simp [φ]
  have hker : RingHom.ker (eval₂Hom (RingHom.id Γ(S, ⊤)) (0 : n → Γ(S, ⊤))) =
      Ideal.span (Set.range X) := by
    ext p
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image, RingHom.mem_ker]
    have h0 : eval₂Hom (RingHom.id Γ(S, ⊤)) (0 : n → Γ(S, ⊤)) p = p.coeff 0 := by
      rw [← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero]; rfl
    rw [h0]
    constructor
    · intro hp m hm
      have hm0 : m ≠ 0 := by rintro rfl; exact (MvPolynomial.mem_support_iff.mp hm) hp
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
      exact ⟨i, Set.mem_univ _, hi⟩
    · intro h
      by_contra hp
      obtain ⟨i, -, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hp)
      exact hi rfl
  have := Ideal.map_comap_of_surjective φ hφ.2
    (RingHom.ker (AffineSpace.homOfVector (n := n) (𝟙 S) 0).appTop.hom)
  have hX : (⇑φ ∘ X) = AffineSpace.coord S := funext fun j => by simp [φ]
  rw [← this, RingHom.comap_ker, hcomp, hker, Ideal.map_span, ← Set.range_comp, hX]

/-- The ideal of the origin of `𝔸^c`, pulled back to an affine scheme, is generated by `c`
elements. -/
private theorem spanRank_ideal_comap_ker_origin_le {k : Type u} [Field k] {c : ℕ}
    {W : Scheme.{u}} [IsAffine W] (h : W ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k))) :
    Cardinal.toENat (Submodule.spanRank
      (((AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h).ideal
        ⟨⊤, isAffineOpen_top W⟩)) ≤ c := by
  rw [Scheme.ker_of_isAffine (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0),
    Stacks.Divisors.ideal_comap_appLE _ _ ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) le_top,
    Stacks.Divisors.ideal_ofIdealTop_top, ker_appTop_homOfVector_zero, Ideal.map_span]
  calc Cardinal.toENat (Submodule.spanRank (Ideal.span _))
      ≤ Cardinal.toENat (Cardinal.mk (ULift.{u} (Fin c))) :=
        Cardinal.toENat.monotone' ((Submodule.spanRank_span_le_card _).trans
          (Cardinal.mk_image_le.trans Cardinal.mk_range_le))
    _ = c := by simp

end Origin

/-! ### The first nonempty centre of a pull-back along an open immersion -/

/-- If the pull-back of `𝐁` along an open immersion `g`, with empty blow-ups deleted, starts with
the centre `W`, then `𝐁` splits as `𝐁_{<i} ++ (Z_i, …)`, where the centres of `𝐁_{<i}` miss the
image of `g`, `g` lifts to an open immersion `g_i` into `X_i` whose image is the inverse image of
the image of `g`, `W = g_i⁻¹ Z_i`, and `i` is the entry index of every set over the image of `g`
meeting the image of `W`. -/
private theorem exists_split_of_pullbackReduced_eq_cons {X₀ : Scheme.{u}} :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) {Y : Scheme.{u}} (g : Y ⟶ X),
      IsOpenImmersion g → ∀ (f : X ⟶ X₀) (V₀ : Set X₀), f ⁻¹' V₀ ⊆ Set.range g →
      ∀ (W : Y.IdealSheafData) (D : ClosedBlowupSequence (blowUp W)),
      B.pullbackReduced g = cons W D →
      ∃ (i : ℕ) (Z : (B.truncate i).target.IdealSheafData)
        (D' : ClosedBlowupSequence (blowUp Z)) (gi : Y ⟶ (B.truncate i).target),
        B = (B.truncate i).append (cons Z D') ∧
        (B.truncate i).CentersLieOver f V₀ᶜ ∧
        IsOpenImmersion gi ∧ gi ≫ (B.truncate i).toBase = g ∧
        (∀ p, f ((B.truncate i).toBase p) ∈ V₀ → p ∈ Set.range gi) ∧ W = Z.comap gi ∧
        ∀ S : Set X, S ⊆ f ⁻¹' V₀ → (∃ y, g y ∈ S ∧ y ∈ (W.support : Set Y)) →
          B.entryIndexOfSet S = i
  | _, .nil _, _, _, _, _, _, _, _, _, h => by simp [pullbackReduced] at h
  | _, .cons Z B, Y, g, hg, f, V₀, hV, W, D, h => by
    by_cases hZ : Z.comap g = ⊤
    · simp only [pullbackReduced, hZ, dite_true] at h
      obtain ⟨hg', hpre⟩ := isOpenImmersion_blowUpLift_and_preimage_range_subset_range Z g hZ
      set g' := blowUpLift Z g (isCartierOver_of_comap_eq_top g Z hZ)
      have hcomp' : g' ≫ blowUpToBase Z = g := blowUpLift_comp _ _ _
      have hπg : ∀ y, blowUpToBase Z (g' y) = g y := fun y => by
        rw [← Scheme.Hom.comp_apply, hcomp']
      have hmiss : ∀ y, g y ∉ (Z.support : Set _) := notMem_support_of_comap_eq_top g hZ
      have hV' : (blowUpToBase Z ≫ f) ⁻¹' V₀ ⊆ Set.range g' := by
        intro p hp
        refine hpre (hV ?_)
        simpa [Scheme.Hom.comp_apply] using hp
      obtain ⟨i, Z', D', gi, hB, hcent, hgi, hcomp, hrange, hW, hidx⟩ :=
        exists_split_of_pullbackReduced_eq_cons B g' hg' (blowUpToBase Z ≫ f) V₀ hV' W D h
      refine ⟨i + 1, Z', D', gi, congrArg (cons Z) hB, ⟨?_, hcent⟩, hgi, ?_, ?_, hW, ?_⟩
      · rintro _ ⟨z, hz, rfl⟩ hzV
        obtain ⟨y, rfl⟩ := hV (show z ∈ f ⁻¹' V₀ by simpa using hzV)
        exact hmiss y hz
      · change gi ≫ (B.truncate i).toBase ≫ blowUpToBase Z = g
        rw [← Category.assoc, hcomp, hcomp']
      · exact hrange
      · intro S hS ⟨y, hyS, hyW⟩
        have hn : ¬ ((Z.support : Set _) ∩ S).Nonempty := by
          rintro ⟨z, hz, hzS⟩
          obtain ⟨y', rfl⟩ := hV (hS hzS)
          exact hmiss y' hz
        simp only [entryIndexOfSet, hn, ite_false]
        rw [hidx (blowUpToBase Z ⁻¹' S) ?_ ⟨y, ?_, hyW⟩]
        · intro p hp
          simpa [Scheme.Hom.comp_apply] using hS hp
        · change blowUpToBase Z (g' y) ∈ S
          rw [hπg]; exact hyS
    · simp only [pullbackReduced, hZ, dite_false] at h
      obtain ⟨hW, -⟩ := cons_eq_cons_iff.1 h
      refine ⟨0, Z, B, g, rfl, trivial, hg, Category.comp_id g, fun p hp => hV hp, hW.symm, ?_⟩
      intro S _ ⟨y, hyS, hyW⟩
      have hn : ((Z.support : Set _) ∩ S).Nonempty := by
        refine ⟨g y, ?_, hyS⟩
        rw [← hW, Scheme.IdealSheafData.support_comap] at hyW
        exact hyW
      simp only [entryIndexOfSet, hn, ite_true]

/-! ### Local data near the smooth point -/

/-- The dimension of `P` at a point of the closed subscheme `X` exceeds that of `X` by a natural
number. -/
private theorem exists_topologicalKrullDimAt_eq_add {k : Type u} [Field k] {P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) [Smooth sP] (I : P.IdealSheafData) (x : I.subscheme) :
    ∃ c : ℕ, topologicalKrullDimAt P (I.subschemeι x) =
      topologicalKrullDimAt I.subscheme x + (c : WithBot ℕ∞) := by
  obtain ⟨nX, hnX⟩ :=
    Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt P k sP (I.subschemeι x)
  obtain ⟨nZ, hnZ⟩ := Stacks.RelativeAssassin.exists_nat_eq_topologicalKrullDimAt I.subscheme k
    (I.subschemeι ≫ sP) x
  have hle :=
    Stacks.AlgebraicGeometry.LimitFibreDimensionBound.topologicalKrullDimAt_le_of_isInducing
      I.subschemeι.isClosedEmbedding.isInducing x
  rw [hnX, hnZ] at hle
  refine ⟨nX - nZ, ?_⟩
  rw [hnX, hnZ, ← Nat.cast_add, Nat.add_sub_cancel' (by exact_mod_cast hle)]

/-- **The codimension bound.** If, on an affine open `W` containing the generic point `η` of an
irreducible component of the support of `I`, the ideal `I` is the pull-back of the ideal of the
origin of `𝔸^c`, and every component of the support has codimension `≥ 2`, then `c ≥ 2`: by
Krull's height theorem the coheight of `η` is at most the `c` generators of `I|_W`. -/
private theorem two_le_of_comap_eq_comap_ker_origin {k : Type u} [Field k] {P : Scheme.{u}}
    [IsLocallyNoetherian P] {I : P.IdealSheafData} (hcodim : 2 ≤ closedsCodimension I.support)
    {η : P} (hη : Maximal (fun s : Set P => IsIrreducible s ∧ s ⊆ (I.support : Set P))
      (closure {η}))
    {W : P.Opens} [IsAffine W] (hηW : η ∈ W) {c : ℕ}
    (h : W.toScheme ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k)))
    (hcomap : I.comap W.ι = (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h) :
    2 ≤ c := by
  let ηW : W.toScheme := ⟨η, hηW⟩
  have e : W.ι ηW = η := by simp [ηW]
  have hmaxW : Maximal (fun s : Set W.toScheme => IsIrreducible s ∧
      s ⊆ ((I.comap W.ι).support : Set W.toScheme)) (closure {ηW}) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact maximal_closure_singleton_preimage W.ι.isOpenEmbedding I.support.isClosed (e ▸ hη)
  have h1 := two_le_coheight_of_two_le_codimension (η := η)
    (le_closedsCodimension_iff.mp hcodim _ hη.prop.2)
  have h2 := coheight_le_spanRank_ideal (I.comap W.ι) hmaxW ⟨⊤, isAffineOpen_top _⟩ trivial
  rw [hcomap, ← coheight_eq_of_isOpenImmersion W.ι, e] at h2
  exact_mod_cast h1.trans (h2.trans (spanRank_ideal_comap_ker_origin_le h))

/-- On an irreducible open `W`, the restriction of an ideal whose support has codimension `≥ 1`
is nonzero at the generic point: otherwise the support would contain the dense set `W`. -/
private theorem isNonzeroAtGenericPoints_comap_ι {P : Scheme.{u}} {I : P.IdealSheafData}
    (hcodim : 1 ≤ closedsCodimension I.support) (W : P.Opens) [IrreducibleSpace W.toScheme] :
    IsNonzeroAtGenericPoints (I.comap W.ι) := by
  intro ξ hξ hst
  have hξS := mem_support_of_stalk_eq_bot _ ξ hst
  rw [Scheme.IdealSheafData.support_comap] at hξS
  have huniv : closure ({ξ} : Set W.toScheme) = Set.univ :=
    Set.eq_univ_of_univ_subset (hξ.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ _))
  have hsub : (W : Set P) ⊆ closure {W.ι ξ} := by
    intro y hy
    have hy' : (⟨y, hy⟩ : W.toScheme) ∈ closure ({ξ} : Set W.toScheme) := by
      rw [huniv]; trivial
    have := image_closure_subset_closure_image W.ι.continuous ⟨_, hy', rfl⟩
    rw [Set.image_singleton] at this
    simpa using this
  exact not_subset_of_one_le_closedsCodimension hcodim
    ⟨closure {W.ι ξ}, isIrreducible_singleton.closure, isClosed_closure⟩
    (closure_minimal (Set.singleton_subset_iff.2 hξS) I.support.isClosed) W.isOpen
    ⟨ξ.1, ξ.2⟩ hsub

/-- Equal triples have heterogeneously equal canonical principalizations. -/
private theorem canonicalPrincipalization_heq_of_eq {s s' : FieldBlowupTriple.{u}}
    (hs : s ∈ triples) (hs' : s' ∈ triples) (h : s = s') :
    HEq (canonicalPrincipalization s (triples_subset_sncTriples hs))
      (canonicalPrincipalization s' (triples_subset_sncTriples hs')) := by
  subst h
  rfl

/-- If on an affine irreducible open `W` of `P` the ideal `I` is the pull-back of the ideal of the
origin of `𝔸^c`, `c ≥ 2`, along a smooth morphism `h` over `k`, and some point of `W` lies in the
support of `I`, then the pull-back of `𝓑𝓟^can(P, I, ∅)` to `W`, after deleting empty blow-ups,
begins with the blow-up of `I|_W`. -/
private theorem exists_pullbackReduced_ι_eq_cons_ker_origin {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (hsm : IsSmoothScheme sP) [QuasiCompact sP]
    {I : P.IdealSheafData} (hcodim1 : 1 ≤ closedsCodimension I.support)
    (ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples)
    (W : P.Opens) [IsAffine W] (hWirr : IsIrreducible (W : Set P)) {c : ℕ} (hc2 : 2 ≤ c)
    (h : W.toScheme ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k))) (hh : Smooth h)
    (hover : h ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k) = W.ι ≫ sP)
    (hcomap : I.comap W.ι = (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h)
    {y : P} (hyW : y ∈ W) (hyS : y ∈ (I.support : Set P)) :
    ∃ D, (canonicalPrincipalization _ (triples_subset_sncTriples ht)).pullbackReduced W.ι =
      cons ((AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h) D := by
  have : Smooth sP := hsm.smooth
  obtain ⟨ht₀, B', hred₀⟩ := exists_reduction_canonicalPrincipalization_eq_cons_ker_origin k hc2
  have hcomm := (canonicalPrincipalization_properties.{u, u, u}).2.2.2.2.1
  have : IrreducibleSpace W.toScheme := Subtype.irreducibleSpace hWirr
  have hQCW : QuasiCompact (W.ι ≫ sP) := (quasiCompact_iff_compactSpace _).2 inferInstance
  have hYW : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}).pullback W.ι ∈
      triples :=
    ⟨‹CharZero k›, isSmoothScheme_of_smooth (W.ι ≫ sP),
      (inferInstance : LocallyOfFiniteType (W.ι ≫ sP)), hQCW,
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace W.toScheme :),
      isNonzeroAtGenericPoints_comap_ι hcodim1 W,
      fun i => i.elim0,
      @isSNCFamily_of_isEmpty _ _ _ (W.ι ≫ sP) _ (Fin 0) inferInstance _⟩
  have hEeq : (OrderedDivisor.empty P).comap W.ι =
      (OrderedDivisor.empty 𝔸(ULift.{u} (Fin c); Spec (.of k))).comap h := by
    simp only [OrderedDivisor.comap, OrderedDivisor.empty]
    congr 1
    funext i
    exact i.elim0
  have hTeq : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}).pullback W.ι =
      (⟨⟨𝔸(ULift.{u} (Fin c); Spec (.of k)), (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker,
        OrderedDivisor.empty _⟩, k, 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)⟩ :
          FieldBlowupTriple.{u}).pullback h := by
    unfold FieldBlowupTriple.pullback
    rw [hcomap, hEeq, ← hover]
  have hY₀ := hTeq ▸ hYW
  have hLOFT : LocallyOfFiniteType (h ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hover]
    infer_instance
  have hQC : QuasiCompact (h ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k)) := by
    rw [hover]
    exact hQCW
  have e1 := hcomm.2 _ ht W.toScheme W.ι inferInstance inferInstance hQCW hYW
  have e2 := hcomm.2 _ ht₀ W.toScheme h hh hLOFT hQC hY₀
  have hBW : ((canonicalPrincipalization _ (triples_subset_sncTriples ht)).pullback W.ι).reduction =
      ((canonicalPrincipalization _ (triples_subset_sncTriples ht₀)).pullback h).reduction :=
    e1.symm.trans ((eq_of_heq (canonicalPrincipalization_heq_of_eq hYW hY₀ hTeq)).trans e2)
  have hne : (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h ≠ ⊤ := fun htop =>
    notMem_support_of_comap_eq_top W.ι (hcomap.trans htop) ⟨y, hyW⟩ hyS
  have h0 : (canonicalPrincipalization _ (triples_subset_sncTriples ht)).pullbackReduced W.ι =
      (cons (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker B').pullbackReduced h := by
    rw [← reduction_pullback, hBW, reduction_pullback, ← pullbackReduced_reduction, hred₀]
  rw [h0]
  exact ⟨_, Kollar.pullbackReduced_cons_of_ne_top _ _ _ hne⟩

/-- **Kollár, p. 139.** Let `P` be a smooth equidimensional scheme of finite type over a field `k`
of characteristic `0`, and `X = I.subscheme ⊆ P` a closed subscheme all of whose
irreducible components have codimension `≥ 2`. Let `𝐁 = 𝓑𝓟^can(P, I, ∅)`
(`MMP.Resolution.canonicalPrincipalization`, defined since `(P, I, ∅) ∈ MMP.Resolution.triples`),
let `η` be the generic point of an irreducible component of `X`, `j = 𝐁.entryIndex η`, and let `x`
be a point of that component at which `X` is smooth. Then there is an open `U ∋ x` of `P` such
that the images in `P` of the first `j` centres of `𝐁` miss `U`, and `𝐁 = 𝐁_{<j} ++ (Z_j, …)`
with `Z_j ∩ Π_j⁻¹(U) = Π_j⁻¹(X ∩ U)` as closed subschemes of `Π_j⁻¹(U)`, where `Π_j` is the
composite `(𝐁.truncate j).toBase`. -/
@[mmp "lem_kr3f_bp_centers_near_smooth_point"]
theorem exists_centersLieOver_compl_and_comap_eq_canonicalPrincipalization
    {k : Type u} [Field k] [CharZero k] {P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    (hsm : IsSmoothScheme sP) [QuasiCompact sP] (hequi : Equidimensional P)
    (I : P.IdealSheafData) (hcodim : 2 ≤ closedsCodimension I.support)
    (η : P) (hη : closure {η} ∈ componentsOf (I.support : Set P))
    (x : I.subscheme) (hx : x ∈ smoothLocus (I.subschemeι ≫ sP))
    (hxC : I.subschemeι.base x ∈ closure {η}) :
    ∃ ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples,
      let B := canonicalPrincipalization _ (triples_subset_sncTriples ht)
      let πj := (B.truncate (B.entryIndex η)).toBase
      ∃ U : P.Opens, I.subschemeι.base x ∈ U ∧
        (B.truncate (B.entryIndex η)).CentersLieOver (𝟙 P) (U : Set P)ᶜ ∧
        ∃ (Z : (B.truncate (B.entryIndex η)).target.IdealSheafData)
          (C : ClosedBlowupSequence (blowUp Z)),
          B = (B.truncate (B.entryIndex η)).append (.cons Z C) ∧
            Z.comap (πj ⁻¹ᵁ U).ι = I.comap ((πj ⁻¹ᵁ U).ι ≫ πj) := by
  have : Smooth sP := hsm.smooth
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian sP
  have hcodim1 : 1 ≤ closedsCodimension I.support := le_trans (by norm_num) hcodim
  have hηmax : Maximal (fun s : Set P => IsIrreducible s ∧ s ⊆ (I.support : Set P))
      (closure {η}) := hη
  have hηS : η ∈ (I.support : Set P) := hηmax.prop.2 (subset_closure rfl)
  have hx'S : I.subschemeι.base x ∈ (I.support : Set P) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
  -- `(P, I, ∅)` is a triple
  have hnzP : IsNonzeroAtGenericPoints I := fun ξ hξ hst =>
    notMem_of_mem_irreducibleComponents hcodim1 hξ (mem_support_of_stalk_eq_bot I ξ hst)
  have ht : (⟨⟨P, I, OrderedDivisor.empty P⟩, k, sP⟩ : FieldBlowupTriple.{u}) ∈ triples :=
    ⟨‹CharZero k›, hsm, inferInstance, inferInstance, hequi, hnzP, isOrderedSNC_empty sP⟩
  refine ⟨ht, ?_⟩
  intro B πj
  -- `X` is near `x` the pull-back of the origin of `𝔸^c` along a smooth morphism
  obtain ⟨V, hxV, hVsm⟩ := mem_smoothLocus_iff.1 hx
  obtain ⟨c, hc⟩ := exists_topologicalKrullDimAt_eq_add sP I x
  obtain ⟨U₁, hxU₁, h₁, hh₁, hover₁, hcomap₁⟩ :=
    Kollar.exists_smooth_comap_ker_origin_eq sP I x ⟨V, hxV, hVsm⟩ hc
  -- shrink to an affine irreducible neighbourhood
  obtain ⟨K, hxK, hKirr⟩ := exists_isIrreducible_mem_opens sP (I.subschemeι x)
  obtain ⟨W, hWaff, hxW, hWsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U₁ ⊓ K) ⟨hxU₁, hxK⟩
  have : IsAffine W := hWaff
  have hWU₁ : W ≤ U₁ := fun y hy => (hWsub hy).1
  have hWirr : IsIrreducible (W : Set P) :=
    ⟨⟨_, hxW⟩, hKirr.2.open_subset W.isOpen (fun y hy => (hWsub hy).2)⟩
  set h : W.toScheme ⟶ 𝔸(ULift.{u} (Fin c); Spec (.of k)) := P.homOfLE hWU₁ ≫ h₁ with hdef
  have hh : Smooth h := by have := hh₁; infer_instance
  have hover : h ≫ 𝔸(ULift.{u} (Fin c); Spec (.of k)) ↘ Spec (.of k) = W.ι ≫ sP := by
    rw [hdef, Category.assoc, hover₁, ← Category.assoc, Scheme.homOfLE_ι]
  have hcomap : I.comap W.ι =
      (AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h := by
    rw [← Scheme.homOfLE_ι P hWU₁, Scheme.IdealSheafData.comap_comp, hcomap₁,
      ← Scheme.IdealSheafData.comap_comp]
  have hηW : η ∈ W := (specializes_iff_mem_closure.2 hxC).mem_open W.isOpen hxW
  -- `c ≥ 2`, by Krull's height theorem at `η`
  have hc2 : 2 ≤ c := two_le_of_comap_eq_comap_ker_origin hcodim hηmax hηW h hcomap
  obtain ⟨D, hD⟩ : ∃ D, B.pullbackReduced W.ι =
      cons ((AffineSpace.homOfVector (𝟙 (Spec (.of k))) 0).ker.comap h) D :=
    exists_pullbackReduced_ι_eq_cons_ker_origin sP hsm hcodim1 ht W hWirr hc2 h hh hover hcomap
      hxW hx'S
  obtain ⟨i, Z, D', gi, hsplit, hcent, hgi, hcomp, hrange, hWeq, hidx⟩ :=
    exists_split_of_pullbackReduced_eq_cons B W.ι inferInstance (𝟙 P) (W : Set P)
      (fun p hp => by rw [Scheme.Opens.range_ι]; exact hp) _ D hD
  have hi : B.entryIndex η = i := hidx {η}
    (fun p hp => by rw [Set.mem_singleton_iff.1 hp]; exact hηW)
    ⟨⟨η, hηW⟩, by simp, by rw [← hcomap, Scheme.IdealSheafData.support_comap]; exact hηS⟩
  subst hi
  have hr : Set.range ((B.truncate (B.entryIndex η)).toBase ⁻¹ᵁ W).ι ⊆ Set.range gi := by
    rw [Scheme.Opens.range_ι]; exact hrange
  refine ⟨W, hxW, hcent, Z, D', hsplit, ?_⟩
  change Z.comap ((B.truncate (B.entryIndex η)).toBase ⁻¹ᵁ W).ι =
    I.comap (((B.truncate (B.entryIndex η)).toBase ⁻¹ᵁ W).ι ≫ (B.truncate (B.entryIndex η)).toBase)
  rw [← IsOpenImmersion.lift_fac gi _ hr, Category.assoc, hcomp,
    Scheme.IdealSheafData.comap_comp Z, ← hWeq, ← hcomap, ← Scheme.IdealSheafData.comap_comp]

end Varieties

end MMP.Resolution
