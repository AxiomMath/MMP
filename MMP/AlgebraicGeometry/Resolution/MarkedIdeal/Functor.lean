module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Sequence

/-!
# Order reduction functors and the disjoining construction (Kollár, *Resolution*, 3.66–3.72)

A *smooth blow-up sequence functor of order `m`* (resp. *`≥ m`*) assigns to every triple
(resp. marked triple) of a class a smooth blow-up sequence of order `m` (resp. `≥ m`) starting
with it, without empty blow-ups (Kollár Def. 3.66). An *order reduction functor* (Thm. 3.68,
3.69) is one whose last ideal has maximal order `< m` and which commutes with smooth morphisms and
with change of fields. In 3.70–3.72 the order reduction functors are assembled by induction on the
dimension, and the principalization functor of 3.35 is built from `𝓑𝓜𝓞_1` by first making the
divisor disjoint: the *disjoining sequence* of `(X, E)` blows up, for `j = 0, …, k - 2`, the
locus of points on at least `k - j` of the (transformed) `E_i`.

## Main definitions

* `MMP.Resolution.OrderBlowupSequenceFunctor`, `MMP.Resolution.OrderGeBlowupSequenceFunctor`.
* `MMP.Resolution.CommutesWithSmoothOn`, `MMP.Resolution.CommutesWithFieldChangeOn` and their
  marked versions.
* `MMP.Resolution.IsOrderReductionFunctorIdeals`, `MMP.Resolution.IsOrderReductionFunctorMarked`,
  `MMP.Resolution.OrderReductionIdealsHoldsUpTo`, `MMP.Resolution.OrderReductionMarkedHoldsUpTo`.
* `MMP.Resolution.identityBlowupSequenceFunctor`.
* `MMP.Resolution.HasClosedEmbeddingProperty`, `MMP.Resolution.IgnoresEmptyEntries`,
  `MMP.Resolution.IgnoresEmptyEntriesMarked`.
* `MMP.Resolution.disjoiningSequence`, `MMP.Resolution.disjoiningDivisor`,
  `MMP.Resolution.disjoiningTotalDivisor`.
* `MMP.Resolution.principalizationConstruction`,
  `MMP.Resolution.IsPrincipalizationFunctorAwayFromDoubleLocus`.

## Implementation notes

The conditions "commutes with smooth morphisms" and "commutes with change of fields" of 3.34 are
stated in `MMP.Resolution.SNCBlowupSequenceFunctor` for functors on all of `𝒯^snc`; the order
reduction functors live on smaller classes (triples of bounded dimension and maximal order), and
the conditions are restated here for a functor on a class `𝒞`, quantifying over pairs of members
of `𝒞`, exactly as in 3.34 otherwise.

A marked triple of a class of marking `m` is a `MarkedTriple` with `t.m = m`. An empty entry
`E^i = ∅` of an ordered divisor is the unit ideal sheaf `⊤`. The double locus `E^{(2)}` is the
set of points lying on at least two of the `E^i`.

The disjoining sequence is built from its stages `(X_j, (E_i^{(j)})_i, (F^{l,(j)})_{l ≤ j})`
(`DisjoiningStage`): the center `Z_j` is the reduced closed subscheme on
`⋃_{|S| = k - j} ⋂_{i ∈ S} E_i^{(j)}`, the new `E_i^{(j+1)}`, `F^{l,(j+1)}` are the reduced
closures of `π_j⁻¹(E_i^{(j)} ∖ Z_j)`, `π_j⁻¹(F^{l,(j)} ∖ Z_j)`, and `F^{j+1,(j+1)} = π_j⁻¹(Z_j)`.
In `E_{X'} = (E^0, …, E^{k-1})` the entry `E^0 = ⋃_i E_i^{(k-1)}` has its reduced structure.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.66–3.72]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Empty entries and the double locus -/

namespace OrderedDivisor

variable {X : Scheme.{u}}

open Classical in
/-- `E^♭`: the ordered divisor obtained from `E = (E^1, …, E^s)` by deleting the entries
`E^i = ∅` (the unit ideal sheaf), keeping the order of the others. -/
def deleteEmpty (E : OrderedDivisor X) : OrderedDivisor X :=
  let L := (List.finRange E.s).filter fun i => E.E i ≠ ⊤
  ⟨L.length, fun j => E.E (L.get j)⟩

/-- The double locus `E^{(2)}`: the points lying on at least two of the `E^i`. -/
def doubleLocus (E : OrderedDivisor X) : Set X :=
  {x | ∃ i j, i ≠ j ∧ x ∈ ((E.E i).support : Set X) ∧ x ∈ ((E.E j).support : Set X)}

end OrderedDivisor

/-! ### Pull-backs and field changes of marked triples -/

namespace MarkedTriple

variable (t : MarkedTriple.{u})

/-- The underlying triple `(X, I, E)` of a marked triple. -/
abbrev toTriple : BlowupTriple.{u} := t.toFieldBlowupTriple.toBlowupTriple

/-- The pulled-back marked triple `(Y, h^*I, m, h⁻¹E)` along `h : Y → X`. -/
def pullback {Y : Scheme.{u}} (h : Y ⟶ t.X) : MarkedTriple.{u} :=
  { t.toFieldBlowupTriple.pullback h with m := t.m }

/-- The field change `(X_{L,σ}, I_{L,σ}, m, E_{L,σ})` of a marked triple along `σ : K ↪ L`. -/
def fieldChange {L : Type u} [Field L] (σ : t.k →+* L) : MarkedTriple.{u} :=
  { t.toFieldBlowupTriple.fieldChange σ with m := t.m }

/-- The marked triple `(X, I, m, E^♭)`, `E^♭` obtained from `E` by deleting its empty entries. -/
def deleteEmpty : MarkedTriple.{u} :=
  { t with E := t.E.deleteEmpty }

end MarkedTriple

/-- The triple `(X, I, E^♭)`. -/
def FieldBlowupTriple.deleteEmpty (t : FieldBlowupTriple.{u}) : FieldBlowupTriple.{u} :=
  { t with E := t.E.deleteEmpty }

/-! ### Enriched blow-up sequence functors -/

/-- A *smooth blow-up sequence functor of order `m`* on a class `𝒞` of triples (Kollár Def. 3.66,
last paragraph): a blow-up sequence functor on `𝒞` sending every `(X, I, E) ∈ 𝒞` to a smooth
blow-up sequence of order `m` starting with `(X, I, E)` none of whose centers is empty. -/
@[mmp "def_kr3c_blowup_sequence_functor_enriched"]
structure OrderBlowupSequenceFunctor (m : ℕ) (𝒞 : Set FieldBlowupTriple.{u}) where
  /-- The underlying blow-up sequence functor. -/
  toFun : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒞
  /-- The value at every member is a smooth blow-up sequence of order `m` starting with it. -/
  isOrderMTripleSeq : ∀ t ht, (toFun t ht).IsOrderMTripleSeq t.sX t.I t.E m
  /-- No center of the value at any member is empty. -/
  hasNoEmptyBlowups : ∀ t ht, (toFun t ht).HasNoEmptyBlowups

/-- A *smooth blow-up sequence functor of order `≥ m`* on a class `𝒞` of marked triples
`(X, I, m, E)` (Kollár Def. 3.66, last paragraph): a blow-up sequence functor on `𝒞` sending
every member to a smooth blow-up sequence of order `≥ m` starting with it none of whose centers
is empty. -/
@[mmp "def_kr3c_blowup_sequence_functor_enriched"]
structure OrderGeBlowupSequenceFunctor (𝒞 : Set MarkedTriple.{u}) where
  /-- The underlying blow-up sequence functor. -/
  toFun : BlowupSequenceFunctor MarkedTriple.toTriple 𝒞
  /-- The value at every member is a smooth blow-up sequence of order `≥ m` starting with it. -/
  isOrderGeMarkedTripleSeq : ∀ t ht,
    (toFun t ht).IsOrderGeMarkedTripleSeq t.sX t.markedIdeal t.E
  /-- No center of the value at any member is empty. -/
  hasNoEmptyBlowups : ∀ t ht, (toFun t ht).HasNoEmptyBlowups

/-! ### Commuting with smooth morphisms and change of fields on a class -/

section Commutes

/-- A blow-up sequence functor `𝐁` on a class `𝒞` of triples *commutes with smooth morphisms*
between members of `𝒞` (Kollár 3.34.1, as `SNCBlowupSequenceFunctor.CommutesWithMorphisms`
with `𝒯^snc` replaced by `𝒞`): for every `(X, I, E) ∈ 𝒞` and smooth `h : Y → X` with `Y` of
finite type over `k` and `(Y, h^*I, h⁻¹E) ∈ 𝒞`, `𝐁(Y, h^*I, h⁻¹E) = h^*𝐁(X, I, E)` if `h` is
surjective, and `𝐁(Y, h^*I, h⁻¹E) = (h^*𝐁(X, I, E))^red` in general. -/
def CommutesWithSmoothOn (𝒞 : Set FieldBlowupTriple.{u})
    (B : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒞) : Prop :=
  (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ 𝒞) (Y : Scheme.{u}) (h : Y ⟶ t.X),
    Smooth h → Surjective h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
      ∀ hY : t.pullback h ∈ 𝒞, B (t.pullback h) hY = (B t ht).pullback h) ∧
  ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ 𝒞) (Y : Scheme.{u}) (h : Y ⟶ t.X),
    Smooth h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
      ∀ hY : t.pullback h ∈ 𝒞, B (t.pullback h) hY = ((B t ht).pullback h).reduction

/-- A blow-up sequence functor `𝐁` on a class `𝒞` of triples *commutes with change of fields*
for members of `𝒞` (Kollár 3.34.2): `𝐁(X_{L,σ}, I_{L,σ}, E_{L,σ}) = 𝐁(X, I, E)_{L,σ}` whenever
both triples are in `𝒞`. -/
def CommutesWithFieldChangeOn (𝒞 : Set FieldBlowupTriple.{u})
    (B : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒞) : Prop :=
  ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ 𝒞) (L : Type u) [Field L] (σ : t.k →+* L)
    (hL : t.fieldChange σ ∈ 𝒞),
    B (t.fieldChange σ) hL = (B t ht).pullback (t.fieldChangeProj σ)

/-- `CommutesWithSmoothOn` for a functor on a class of marked triples, the pulled-back marked
triple being `(Y, h^*I, m, h⁻¹E)`. -/
def CommutesWithSmoothOnMarked (𝒞 : Set MarkedTriple.{u})
    (B : BlowupSequenceFunctor MarkedTriple.toTriple 𝒞) : Prop :=
  (∀ (t : MarkedTriple.{u}) (ht : t ∈ 𝒞) (Y : Scheme.{u}) (h : Y ⟶ t.X),
    Smooth h → Surjective h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
      ∀ hY : t.pullback h ∈ 𝒞, B (t.pullback h) hY = (B t ht).pullback h) ∧
  ∀ (t : MarkedTriple.{u}) (ht : t ∈ 𝒞) (Y : Scheme.{u}) (h : Y ⟶ t.X),
    Smooth h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
      ∀ hY : t.pullback h ∈ 𝒞, B (t.pullback h) hY = ((B t ht).pullback h).reduction

/-- `CommutesWithFieldChangeOn` for a functor on a class of marked triples. -/
def CommutesWithFieldChangeOnMarked (𝒞 : Set MarkedTriple.{u})
    (B : BlowupSequenceFunctor MarkedTriple.toTriple 𝒞) : Prop :=
  ∀ (t : MarkedTriple.{u}) (ht : t ∈ 𝒞) (L : Type u) [Field L] (σ : t.k →+* L)
    (hL : t.fieldChange σ ∈ 𝒞),
    B (t.fieldChange σ) hL = (B t ht).pullback (t.toFieldBlowupTriple.fieldChangeProj σ)

end Commutes

/-! ### Order reduction functors -/

/-- `dim X ∈ N`, the dimension being the Krull dimension of the underlying space. -/
def HasDimensionIn (X : Scheme.{u}) (N : Set ℕ) : Prop :=
  ∃ n ∈ N, topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)

/-- The class of all triples `(X, I, E)` with `dim X ∈ N` and `maxord I ≤ m`. -/
def idealTriplesOfDim (N : Set ℕ) (m : ℕ) : Set FieldBlowupTriple.{u} :=
  {t | t ∈ triples ∧ HasDimensionIn t.X N ∧ maxOrder t.I ≤ m}

/-- The class of all marked triples `(X, I, m, E)` of marking `m` with `dim X ∈ N`. -/
def markedTriplesOfDim (N : Set ℕ) (m : ℕ) : Set MarkedTriple.{u} :=
  {t | t ∈ markedTriples ∧ t.m = m ∧ HasDimensionIn t.X N}

/-- `𝓑𝓞_m` is an *order reduction functor for ideals of order `m` on dimensions `N`* (Kollár
Thm. 3.68 (1)–(2), as a predicate): a smooth blow-up sequence functor of order `m` on the class of
all triples `(X, I, E)` with `dim X ∈ N` and `maxord I ≤ m` such that (1) the last ideal `I_r` of
`𝓑𝓞_m(X, I, E)` has `maxord I_r < m`, (2a) `𝓑𝓞_m` commutes with smooth morphisms between triples
of this class, and (2b) with change of fields for triples of this class. -/
@[mmp "def_kr3c_order_reduction_functor_ideals"]
def IsOrderReductionFunctorIdeals (m : ℕ) (N : Set ℕ)
    (B : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim N m)) : Prop :=
  (∀ t ht, maxOrder ((B.toFun t ht).controlledTransform t.I) < m) ∧
    CommutesWithSmoothOn _ B.toFun ∧ CommutesWithFieldChangeOn _ B.toFun

/-- `𝓑𝓜𝓞_m` is an *order reduction functor for marked ideals of order `m` on dimensions `N`*
(Kollár Thm. 3.69 (1)–(2), as a predicate): a smooth blow-up sequence functor of order `≥ m` on
the class of all marked triples `(X, I, m, E)` with `dim X ∈ N` such that (1) the last ideal
`I_r` of `𝓑𝓜𝓞_m(X, I, m, E)` has `maxord I_r < m`, (2a) `𝓑𝓜𝓞_m` commutes with smooth morphisms
between marked triples of this class, and (2b) with change of fields. -/
@[mmp "def_kr3c_order_reduction_functor_marked"]
def IsOrderReductionFunctorMarked (m : ℕ) (N : Set ℕ)
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim N m)) : Prop :=
  (∀ t ht, maxOrder ((B.toFun t ht).markedTransform t.markedIdeal).I < m) ∧
    CommutesWithSmoothOnMarked _ B.toFun ∧ CommutesWithFieldChangeOnMarked _ B.toFun

/-- *(3.68) holds in dimensions `≤ n`* (Kollár 3.70): for every `m ≥ 1` there is an order
reduction functor for ideals of order `m` on dimensions `{0, 1, …, n}`. -/
@[mmp "def_kr3c_order_reduction_ideals_in_dimension"]
def OrderReductionIdealsHoldsUpTo (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ B : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim {d | d ≤ n} m),
    IsOrderReductionFunctorIdeals m _ B

/-- *(3.69) holds in dimensions `≤ d`* (Kollár 3.70): for every `m ≥ 1` there is an order
reduction functor for marked ideals of order `m` on dimensions `{0, 1, …, d}`. -/
@[mmp "def_kr3c_order_reduction_marked_up_to_dimension"]
def OrderReductionMarkedHoldsUpTo (d : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim {e | e ≤ d} m),
    IsOrderReductionFunctorMarked m _ B

/-- The *identity functor* on a class `𝒞` of triples or marked triples (Kollár 3.70, "resolved
without blow-ups"): every member goes to the blow-up sequence of length `0` starting with it. -/
@[mmp "def_kr3c_identity_functor"]
def identityBlowupSequenceFunctor {T : Type*} (toTriple : T → BlowupTriple.{u}) (𝒞 : Set T) :
    BlowupSequenceFunctor toTriple 𝒞 :=
  fun _ _ => .nil _

/-! ### Properties of `𝓑𝓜𝓞_1` used in 3.71–3.72 -/

/-- The marked triples `(X, I, m, E)` of marking `m`. -/
def markedTriplesOfMarking (m : ℕ) : Set MarkedTriple.{u} :=
  {t | t ∈ markedTriples ∧ t.m = m}

/-- An assignment `𝓑` on the marked triples of marking `1` has the *closed embedding property of
(3.71.2)* (Kollár Claim 3.71.2, as a predicate): `𝓑(X, I, 1, ()) = τ_*𝓑(Y, J, 1, ())` whenever
`τ : Y ↪ X` is a closed embedding of smooth schemes, `τ_*(𝒪_Y/J) = 𝒪_X/I`, and `(X, I, 1, ())`,
`(Y, J, 1, ())` are marked triples (so `J` is nonzero on every irreducible component of `Y`). -/
@[mmp "def_kr3c_closed_embedding_property_marked"]
def HasClosedEmbeddingProperty
    (B : BlowupSequenceFunctor MarkedTriple.toTriple (markedTriplesOfMarking.{u} 1)) : Prop :=
  ∀ d : ClosedEmbeddingData.{u}, d.E.s = 0 →
    ∀ (hX : (⟨d.ambientTriple, 1⟩ : MarkedTriple) ∈ markedTriplesOfMarking 1)
      (hY : (⟨d.embeddedTriple, 1⟩ : MarkedTriple) ∈ markedTriplesOfMarking 1),
      ClosedBlowupSequence.IsPushforward d.j (B ⟨d.embeddedTriple, 1⟩ hY)
        (B ⟨d.ambientTriple, 1⟩ hX)

/-- An assignment `𝓑` on a class `𝒞` of marked triples *ignores empty entries* (Kollár 3.72,
added): for every `(X, I, m, E) ∈ 𝒞`, `(X, I, m, E^♭) ∈ 𝒞` and
`𝓑(X, I, m, E^♭) = 𝓑(X, I, m, E)`. -/
@[mmp "def_kr3c_ignores_empty_divisors"]
def IgnoresEmptyEntriesMarked (𝒞 : Set MarkedTriple.{u})
    (B : BlowupSequenceFunctor MarkedTriple.toTriple 𝒞) : Prop :=
  ∀ t (ht : t ∈ 𝒞), ∃ h : t.deleteEmpty ∈ 𝒞, B t.deleteEmpty h = B t ht

/-- An assignment `𝓑` on a class `𝒞` of triples *ignores empty entries* (Kollár 3.72, added):
for every `(X, I, E) ∈ 𝒞`, `(X, I, E^♭) ∈ 𝒞` and `𝓑(X, I, E^♭) = 𝓑(X, I, E)`. -/
@[mmp "def_kr3c_ignores_empty_divisors"]
def IgnoresEmptyEntries (𝒞 : Set FieldBlowupTriple.{u})
    (B : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒞) : Prop :=
  ∀ t (ht : t ∈ 𝒞), ∃ h : t.deleteEmpty ∈ 𝒞, B t.deleteEmpty h = B t ht

/-! ### The disjoining sequence -/

/-- A stage `(X_j, (E_i^{(j)})_{i ≤ k}, (F^{l,(j)})_{l ≤ j})` of the disjoining sequence. -/
structure DisjoiningStage (k j : ℕ) where
  /-- The scheme `X_j`. -/
  X : Scheme.{u}
  /-- The transforms `E_i^{(j)}` of the `E_i`. -/
  Es : Fin k → X.IdealSheafData
  /-- The transforms `F^{l,(j)}` of the exceptional divisors `F^l`, `1 ≤ l ≤ j`. -/
  Fs : Fin j → X.IdealSheafData

namespace DisjoiningStage

variable {k j : ℕ} (st : DisjoiningStage.{u} k j)

/-- The center `Z_j ⊆ X_j`: the reduced closed subscheme on the points lying on at least `k - j`
of the `E_i^{(j)}`, `⋃_{|S| = k - j} ⋂_{i ∈ S} E_i^{(j)}`. -/
@[mmp "def_kr3c_disjoining_sequence"]
def center : st.X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⨆ S : {S : Finset (Fin k) // S.card = k - j}, ⨅ i ∈ S.1, (st.Es i).support)

/-- The reduced closure `π_j⁻¹(D ∖ Z_j)‾` of the inverse image of `D ∖ Z_j`. -/
def transform (D : st.X.IdealSheafData) : (blowUp st.center).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (blowUpToBase st.center ⁻¹' ((D.support : Set st.X) \ (st.center.support : Set st.X))))

/-- The next stage: `X_{j+1} = B_{Z_j}X_j`, `E_i^{(j+1)}`, `F^{l,(j+1)}` the reduced closures of
`π_j⁻¹(E_i^{(j)} ∖ Z_j)`, `π_j⁻¹(F^{l,(j)} ∖ Z_j)`, and `F^{j+1,(j+1)} = F^{j+1} = π_j⁻¹(Z_j)`. -/
@[mmp "def_kr3c_disjoining_sequence"]
def step : DisjoiningStage.{u} k (j + 1) where
  X := blowUp st.center
  Es i := st.transform (st.Es i)
  Fs := Fin.snoc (α := fun _ => (blowUp st.center).IdealSheafData) (fun l => st.transform (st.Fs l))
    (st.center.comap (blowUpToBase st.center))

/-- The reduced divisor `⋃_i E_i^{(j)}`. -/
def unionEs : st.X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (⨆ i, (st.Es i).support)

/-- The blow-up sequence of the next `n` steps of the disjoining sequence, from stage `j`. -/
def sequence : (n : ℕ) → {j : ℕ} → (st : DisjoiningStage.{u} k j) → ClosedBlowupSequence st.X
  | 0, _, st => .nil st.X
  | n + 1, _, st => .cons st.center (sequence n st.step)

/-- The ordered divisor `(E^0, E^1, …)` at the end of `sequence n st`, with
`E^0 = ⋃_i E_i^{(j + n)}` and `E^l = F^{l,(j + n)}`. -/
def divisor : (n : ℕ) → {j : ℕ} → (st : DisjoiningStage.{u} k j) →
    OrderedDivisor (sequence n st).target
  | 0, j, st => ⟨j + 1, Fin.cons (α := fun _ => st.X.IdealSheafData) st.unionEs st.Fs⟩
  | n + 1, _, st => divisor n st.step

/-- The stage `j + n` reached after `n` steps from stage `j`. -/
def iterate : (n : ℕ) → {j : ℕ} → DisjoiningStage.{u} k j → DisjoiningStage.{u} k (j + n)
  | 0, _, st => st
  | n + 1, _, st => (iterate n st).step

end DisjoiningStage

section Disjoining

variable {X : Scheme.{u}}

/-- The initial stage `X_0 = X`, `E_i^{(0)} = E_i`, no `F`. -/
def disjoiningStart (E : OrderedDivisor X) : DisjoiningStage.{u} E.s 0 :=
  ⟨X, E.E, Fin.elim0⟩

/-- The *disjoining sequence* `(X_j, Z_j)_{j ≤ k-1}` of `(X, E)`, `E = (E_1, …, E_k)` (Kollár
3.72): of length `0` if `k ≤ 1`; for `k ≥ 2`, `Z_j ⊆ X_j` is the reduced closed subscheme on
the points lying on at least `k - j` of the `E_i^{(j)}` and `X_{j+1} = B_{Z_j}X_j`, for
`0 ≤ j ≤ k - 2`. Its end is `X' = X_{k-1}` with composite `π = toBase : X' → X`. -/
@[mmp "def_kr3c_disjoining_sequence"]
def disjoiningSequence : (X : Scheme.{u}) → OrderedDivisor X → ClosedBlowupSequence X
  | X, ⟨0, _⟩ => .nil X
  | X, ⟨1, _⟩ => .nil X
  | X, ⟨k + 2, E⟩ => (disjoiningStart (X := X) ⟨k + 2, E⟩).sequence (k + 1)

/-- The ordered divisor `E_{X'}` at the end of the disjoining sequence (Kollár 3.72): `()` if
`k = 0`, `(E_1)` if `k = 1`, and `(E^0, E^1, …, E^{k-1})` with `E^0 = ⋃_i E_i^{(k-1)}` and
`E^l = F^{l,(k-1)}` if `k ≥ 2`. -/
@[mmp "def_kr3c_disjoining_sequence"]
def disjoiningDivisor : (X : Scheme.{u}) → (E : OrderedDivisor X) →
    OrderedDivisor (disjoiningSequence X E).target
  | X, ⟨0, _⟩ => OrderedDivisor.empty X
  | _, ⟨1, E⟩ => ⟨1, E⟩
  | X, ⟨k + 2, E⟩ => (disjoiningStart (X := X) ⟨k + 2, E⟩).divisor (k + 1)

/-- The stage `j` `(X_j, (E_i^{(j)}), (F^{l,(j)}))` of the disjoining construction for `(X, E)`. -/
def disjoiningStage (E : OrderedDivisor X) (j : ℕ) : DisjoiningStage.{u} E.s (0 + j) :=
  (disjoiningStart E).iterate j

/-- The *total divisor* `D_j` at step `j` of the disjoining sequence (Kollár 3.72): the reduced
divisor `⋃_i E_i^{(j)} ∪ ⋃_{1 ≤ l ≤ j} F^{l,(j)}` on `X_j`, as the family of the reduced
divisors `E_i^{(j)}` and `F^{l,(j)}`. -/
@[mmp "def_kr3c_disjoining_total_divisor"]
def disjoiningTotalDivisor (E : OrderedDivisor X) (j : ℕ) :
    Fin E.s ⊕ Fin (0 + j) → (disjoiningStage E j).X.IdealSheafData :=
  Sum.elim (disjoiningStage E j).Es (disjoiningStage E j).Fs

end Disjoining

/-! ### The principalization construction -/

namespace ClosedBlowupSequence

/-- The concatenation of a blow-up sequence starting with `X` and one starting with its end. -/
def append : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → ClosedBlowupSequence B.target →
    ClosedBlowupSequence X
  | _, nil _, C => C
  | _, cons Z B, C => cons Z (B.append C)

/-- The images in `X₀` of the centers of a blow-up sequence starting with `X` lie in `S ⊆ X₀`,
`X` mapping to `X₀` by `f`. -/
def CentersLieOver : {X X₀ : Scheme.{u}} → ClosedBlowupSequence X → (X ⟶ X₀) → Set X₀ → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons Z B, f, S =>
      (f : _ → _) '' (Z.support : Set _) ⊆ S ∧ B.CentersLieOver (blowUpToBase Z ≫ f) S

end ClosedBlowupSequence

open Classical in
/-- The construction `𝓑𝓟_𝓑` of Kollár 3.72: for an assignment `𝓑` on the marked triples of
marking `1` and `(X, I, E) ∈ 𝒯^snc` with disjoining sequence ending in `π : X' → X` with ordered
divisor `E_{X'}`, `𝓑𝓟_𝓑(X, I, E)` is the concatenation of the disjoining sequence with
`𝓑(X', π^*I, 1, E_{X'})` with its empty blow-ups deleted, if `(X', π^*I, 1, E_{X'})` is a marked
triple, and the disjoining sequence with its empty blow-ups deleted otherwise. -/
@[mmp "def_kr3c_principalization_construction"]
def principalizationConstruction
    (B : BlowupSequenceFunctor MarkedTriple.toTriple (markedTriplesOfMarking.{u} 1)) :
    SNCBlowupSequenceFunctor.{u} := fun (t : FieldBlowupTriple.{u}) _ =>
  let D := disjoiningSequence t.X t.E
  let t' : MarkedTriple.{u} :=
    ⟨⟨⟨D.target, t.I.comap D.toBase, disjoiningDivisor t.X t.E⟩, t.k, D.toBase ≫ t.sX⟩, 1⟩
  if h : t' ∈ markedTriplesOfMarking 1 then (D.append (B t' h)).reduction else D.reduction

/-- A blow-up sequence functor `𝓑𝓟` on `𝒯^snc` is a *principalization functor away from
`E^{(2)}`* (Kollár 3.35 with (3) replaced by (3″)): for every `(X, I, E) ∈ 𝒯^snc`, with centers
`Z_i ⊆ X_i` and composite `Π`, (0) `𝓑𝓟(X, I, E)` has no empty blow-ups; (1) it is a smooth
blow-up sequence (all `Z_i` smooth) and its centers have simple normal crossings with `E`;
(2) `Π^*I` is monomial; (3″) the image of each `Z_i` in `X` lies in `cosupp I ∪ E^{(2)}`;
(4) `𝓑𝓟` commutes with smooth morphisms and with change of fields; (5) `𝓑𝓟` commutes with closed
embeddings for triples with `E = ∅`. -/
@[mmp "def_kr3c_principalization_functor_away_from_divisor"]
def IsPrincipalizationFunctorAwayFromDoubleLocus (BP : SNCBlowupSequenceFunctor.{u}) : Prop :=
  (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples), (BP t ht).HasNoEmptyBlowups) ∧
    (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples),
      (BP t ht).IsSmooth t.sX ∧ (BP t ht).CentersHaveSNCWith t.sX t.E.support) ∧
    (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples),
      IsMonomialIdeal (t.I.comap (BP t ht).toBase)) ∧
    (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples),
      (BP t ht).CentersLieOver (𝟙 t.X) ((t.I.support : Set t.X) ∪ t.E.doubleLocus)) ∧
    BP.CommutesWithMorphisms @Smooth ∧ BP.CommutesWithFieldChange ∧
    BP.CommutesWithClosedEmbeddings {d | d.E.s = 0}

end MMP.Resolution
