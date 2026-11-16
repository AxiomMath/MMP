module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.MMP.Models
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections

/-!
# Blow-up sequences and blow-up sequence functors (Kollár, *Resolution*, 3.15–3.35)

A *blow-up sequence* starting with a scheme `X` is a sequence `X_r → ⋯ → X_1 → X_0 = X` in
which `X_{i+1} = B_{Z_i}X_i` is the blow-up of `X_i` along a closed subscheme `Z_i ⊆ X_i`, the
*centres* being part of the data (Kollár Def. 3.29). This file defines blow-up sequences, their
pull-back along an arbitrary morphism (3.30), restriction to and push-forward from a closed
subscheme (3.30.2–3), deletion of empty blow-ups (3.32), total transforms and total exceptional
sets (3.25), smooth blow-up sequences and centres with simple normal crossings with a divisor
(3.24, 3.25, 3.29), the triples `(X, I, E)` and blow-up sequence functors on them (3.31, 3.35),
and the conditions of 3.34 under which such a functor commutes with smooth morphisms, with
change of fields and with closed embeddings. Finally: monomial ideals (3.16) and
principalizations (§3.3).

## Main definitions

* `MMP.Resolution.ClosedBlowupSequence`: blow-up sequences starting with `X`, with
  `length`, `target` (`X_r`), `toBase` (`Π : X_r → X`), and `truncate`.
* `MMP.Resolution.canonicalLift`: the canonical lift `B_{f⁻¹Z}Y → B_ZX` of `f : Y → X`.
* `MMP.Resolution.ClosedBlowupSequence.pullback`, `…pullbackHom`: `h^*𝐁` and `h_r`.
* `MMP.Resolution.ClosedBlowupSequence.restrict`: `𝐁|_S`.
* `MMP.Resolution.ClosedBlowupSequence.IsPushforward`: `𝐁^X = j_*𝐁(S)`.
* `MMP.Resolution.ClosedBlowupSequence.HasNoEmptyBlowups`, `…reduction`: `𝐁^red`.
* `MMP.Resolution.ClosedBlowupSequence.totalTransform`, `…totalExceptionalSet`.
* `MMP.Resolution.ClosedBlowupSequence.IsSmooth`, `…CentersHaveSNCWith`.
* `MMP.Resolution.OrderedDivisor`: divisors with ordered index set.
* `MMP.Resolution.IsSNCFamily`, `MMP.Resolution.IsSNCClosedSubset`,
  `MMP.Resolution.HasSNCWith`: snc divisors, closed subsets that are snc divisors, and closed
  subschemes having snc with an snc divisor.
* `MMP.Resolution.BlowupTriple`, `MMP.Resolution.FieldBlowupTriple`,
  `MMP.Resolution.BlowupSequenceFunctor`, `MMP.Resolution.sncTriples`,
  `MMP.Resolution.SNCBlowupSequenceFunctor`.
* `MMP.Resolution.SNCBlowupSequenceFunctor.CommutesWith`, `…CommutesWithSurjections`,
  `…CommutesWithMorphisms`, `…CommutesWithFieldChange`, `…CommutesWithClosedEmbeddings`.
* `MMP.Resolution.IsMonomialIdeal`, `MMP.Resolution.IsPrincipalization`.

## Implementation notes

A blow-up sequence is an inductive type: `nil` is the sequence of length `0`, and
`cons Z 𝐁` blows up `Z ⊆ X` and continues with a blow-up sequence `𝐁` starting with `B_ZX`.
So `X_{i+1}` *is* `B_{Z_i}X_i` (StacksDraft's `AlgebraicGeometry.blowUp`, Stacks 01OG), and two
blow-up sequences are equal exactly when they have the same length and the same centres, as in
the source. Closed subschemes are Mathlib's `Scheme.IdealSheafData`, the empty closed subscheme
being `⊤`; the inverse image `f⁻¹Z` (ideal `f^*I`) is `Scheme.IdealSheafData.comap`, the
scheme-theoretic image `j_*Z` is `Scheme.IdealSheafData.map`, and the cosupport of an ideal
sheaf is `Scheme.IdealSheafData.support` (recorded, not restated).

The canonical lift of `f : Y → X` along `Z` is the classifying morphism
`AlgebraicGeometry.blowUpLift` (Stacks 0806) of `B_{f⁻¹Z}Y → Y → X`, on which the inverse image of
`Z` is the exceptional divisor of `B_{f⁻¹Z}Y`, an effective Cartier divisor. By uniqueness in
the universal property it is the composite `B_{f⁻¹Z}Y → B_ZX ×_X Y → B_ZX` of the source.

Blowing up the empty subscheme gives `B_∅X ≅ X` (not `= X`). Deleting an empty blow-up therefore
continues with the rest of the sequence pulled back along `X ≅ B_∅X`; this is how
`ClosedBlowupSequence.reduction` is defined, through `pullbackReduced`, the pull-back with empty
blow-ups deleted.

The *functors* of 3.31 are assignments `𝐁(t)` on the triples `t` of a class; their
functoriality is imposed separately, by the predicates of 3.34, each stated as an equality of
blow-up sequences (`CommutesWith…`). On the snc triples of 3.35 the ground field `k` and the
structure morphism `X → Spec k` are part of the data (`FieldBlowupTriple`); a pulled-back triple
`(Y, h^*I, h⁻¹E)` is over `k` by `Y → X → Spec k`. The source's hypothesis that `h` be smooth
in "`𝐁` commutes with `h`" is dropped: the predicate is stated for any `h`, and the
smooth/étale restriction enters in `CommutesWithSurjections` and `CommutesWithMorphisms`
through a morphism property `P` (`@Smooth` or `@Etale`).

Local coordinates at `x` on a smooth scheme are a regular system of parameters of `𝒪_{X,x}`
(`MMP.Mori.IsRegularSystemOfParameters`), and "`E^i = (z_c = 0)` near `x`" is read on the stalk
at `x`, as in `MMP.Mori.DivisorWithCoeffs.IsSNC`. Unlike that definition, the snc divisors of
Kollár 3.24 are finite families of reduced, possibly reducible, divisors (`IsSNCFamily`).

Hypotheses of the source that only restrict the domain are dropped where the definition makes
sense without them: local noetherianity (kept only in `BlowupTriple.IsAdmissible`), closedness
of `S ⊆ X` in restriction and push-forward, smoothness of `X` in `HasSNCWith`,
`IsMonomialIdeal` and `CentersHaveSNCWith`, and smoothness of the blow-up sequence in
`CentersHaveSNCWith`.

The smooth blow-up of KR 3a is not imported here: `ClosedBlowupSequence.IsSmooth` states
smoothness of `X_i` and `Z_i` directly; the two can be merged later.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.15–3.35]
* [R. Hartshorne, *Algebraic geometry*, II.7.15]
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Blow-up sequences -/

/-- A *blow-up sequence* starting with `X` (Kollár Def. 3.29): `nil` has length `0`; `cons Z 𝐁`
blows up the centre `Z ⊆ X` and continues with a blow-up sequence `𝐁` starting with
`X_1 = B_ZX`. Trivial and empty centres are allowed. Equality is equality of lengths and
centres. -/
@[mmp "def_kr3b_blowup_sequence"]
inductive ClosedBlowupSequence : Scheme.{u} → Type (u + 1)
  /-- The blow-up sequence of length `0`. -/
  | nil (X : Scheme.{u}) : ClosedBlowupSequence X
  /-- Blow up `Z ⊆ X`, then continue on `B_ZX`. -/
  | cons {X : Scheme.{u}} (Z : X.IdealSheafData) (B : ClosedBlowupSequence (blowUp Z)) :
      ClosedBlowupSequence X

namespace ClosedBlowupSequence

/-- The length `r` of a blow-up sequence. -/
@[mmp "def_kr3b_blowup_sequence"]
def length : {X : Scheme.{u}} → ClosedBlowupSequence X → ℕ
  | _, nil _ => 0
  | _, cons _ B => B.length + 1

/-- The last scheme `X_r` of a blow-up sequence. -/
@[mmp "def_kr3b_blowup_sequence"]
def target : {X : Scheme.{u}} → ClosedBlowupSequence X → Scheme.{u}
  | X, nil _ => X
  | _, cons _ B => B.target

/-- The composite `Π = π_0 ∘ ⋯ ∘ π_{r-1} : X_r → X_0 = X`. -/
@[mmp "def_kr3b_blowup_sequence"]
def toBase : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → (B.target ⟶ X)
  | X, nil _ => 𝟙 X
  | _, cons Z B => B.toBase ≫ blowUpToBase Z

/-- The first `i` blow-ups `X_i → ⋯ → X_0` of a blow-up sequence (all of it if `i ≥ r`). -/
@[mmp "def_kr3b_total_exceptional_set"]
def truncate : {X : Scheme.{u}} → ClosedBlowupSequence X → ℕ → ClosedBlowupSequence X
  | X, nil _, _ => nil X
  | X, cons _ _, 0 => nil X
  | _, cons Z B, i + 1 => cons Z (B.truncate i)

/-- Two blow-up sequences starting with `X` with first centres `Z`, `Z'` are equal exactly when
the centres agree and so do the remaining sequences (inductively: same length, same centres). -/
@[mmp "def_kr3b_blowup_sequence"]
theorem cons_eq_cons_iff {X : Scheme.{u}} {Z Z' : X.IdealSheafData}
    {B : ClosedBlowupSequence (blowUp Z)} {B' : ClosedBlowupSequence (blowUp Z')} :
    cons Z B = cons Z' B' ↔ Z = Z' ∧ B ≍ B' :=
  Iff.of_eq (cons.injEq _ _ _ _)

end ClosedBlowupSequence

/-! ### The canonical lift -/

section CanonicalLift

variable {X Y : Scheme.{u}}

/-- On `B_{f⁻¹Z}Y`, the inverse image of `Z` along `B_{f⁻¹Z}Y → Y → X` is the exceptional
divisor, an effective Cartier divisor. -/
theorem isCartierOver_blowUpToBase_comp (f : Y ⟶ X) (Z : X.IdealSheafData) :
    Stacks.Blowup.IsCartierOver Z (Over.mk (blowUpToBase (Z.comap f) ≫ f)) := by
  change Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap (blowUpToBase (Z.comap f) ≫ f))
  rw [Scheme.IdealSheafData.comap_comp]
  exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap f)

/-- The *canonical lift* `f̃_Z : B_{f⁻¹Z}Y → B_ZX` of a morphism `f : Y → X` along a closed
subscheme `Z ⊆ X` (Kollár 3.30; Hartshorne II.7.15): the unique morphism over `f`, by the
universal property of `B_ZX` (Stacks 0806). -/
@[mmp "def_kr3b_blowup_canonical_lift"]
def canonicalLift (f : Y ⟶ X) (Z : X.IdealSheafData) : blowUp (Z.comap f) ⟶ blowUp Z :=
  blowUpLift Z (blowUpToBase (Z.comap f) ≫ f) (isCartierOver_blowUpToBase_comp f Z)

/-- `π_{Z,X} ∘ f̃_Z = f ∘ π_{f⁻¹Z,Y}`. -/
@[reassoc, mmp "def_kr3b_blowup_canonical_lift"]
theorem canonicalLift_comp_blowUpToBase (f : Y ⟶ X) (Z : X.IdealSheafData) :
    canonicalLift f Z ≫ blowUpToBase Z = blowUpToBase (Z.comap f) ≫ f :=
  blowUpLift_comp _ _ _

/-- The canonical lift factors as `B_{f⁻¹Z}Y → B_ZX ×_X Y → B_ZX`, the first map a closed
immersion over `Y` (Kollár 3.30; EGA II 3.5.3, 3.6.2). -/
@[mmp "def_kr3b_blowup_canonical_lift"]
theorem exists_isClosedImmersion_canonicalLift_factor (f : Y ⟶ X) (Z : X.IdealSheafData) :
    ∃ g : blowUp (Z.comap f) ⟶ Limits.pullback (blowUpToBase Z) f,
      IsClosedImmersion g ∧ g ≫ Limits.pullback.snd _ _ = blowUpToBase (Z.comap f) ∧
        g ≫ Limits.pullback.fst _ _ = canonicalLift f Z := by
  set J := Stacks.StrictTransform.ideal f (blowUpToBase Z) (exceptionalIdeal Z)
  set e := strictTransformBlowUpIso f Z
  have hw := e.inv.w
  simp only [Over.mk_hom] at hw
  have hfst : e.inv.left ≫ J.subschemeι ≫ Limits.pullback.fst f (blowUpToBase Z) =
      blowUpToBase (Z.comap f) := hw
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  refine ⟨e.inv.left ≫ J.subschemeι ≫ (Limits.pullbackSymmetry _ _).hom, ?_,
    by simpa using hfst, ?_⟩
  · infer_instance
  · rw [Category.assoc, Category.assoc, Limits.pullbackSymmetry_hom_comp_fst, canonicalLift]
    refine blowUpLift_unique _ _ _ _ ?_
    rw [Category.assoc, Category.assoc, ← Limits.pullback.condition]
    simpa only [Category.assoc] using congrArg (· ≫ f) hfst

end CanonicalLift

/-! ### Pull-back, restriction, push-forward -/

namespace ClosedBlowupSequence

/-- The *pull-back* `h^*𝐁` of a blow-up sequence `𝐁 = (X_i, Z_i)` along a morphism
`h : Y → X` (Kollár 3.30.1): `Y_0 = Y`, `h_0 = h`, `W_i = h_i⁻¹Z_i`, `Y_{i+1} = B_{W_i}Y_i`, and
`h_{i+1}` the canonical lift of `h_i`. -/
@[mmp "def_kr3b_pullback_blowup_sequence"]
def pullback : {X Y : Scheme.{u}} → ClosedBlowupSequence X → (Y ⟶ X) → ClosedBlowupSequence Y
  | _, Y, nil _, _ => nil Y
  | _, _, cons Z B, h => cons (Z.comap h) (B.pullback (canonicalLift h Z))

/-- The last morphism `h_r : Y_r → X_r` of the pull-back `h^*𝐁`. -/
@[mmp "def_kr3b_pullback_blowup_sequence"]
def pullbackHom : {X Y : Scheme.{u}} → (B : ClosedBlowupSequence X) → (h : Y ⟶ X) →
    ((B.pullback h).target ⟶ B.target)
  | _, _, nil _, h => h
  | _, _, cons Z B, h => B.pullbackHom (canonicalLift h Z)

/-- The *restriction* `𝐁|_S = j^*𝐁` of a blow-up sequence starting with `X` to a closed
subscheme `S ⊆ X`, the pull-back along `j : S ↪ X` (Kollár 3.30.2). -/
@[mmp "def_kr3b_restriction_blowup_sequence"]
def restrict {X : Scheme.{u}} (B : ClosedBlowupSequence X) (S : X.IdealSheafData) :
    ClosedBlowupSequence S.subscheme :=
  B.pullback S.subschemeι

/-- The morphism `j_r : S_r → X_r` of the restriction `𝐁|_S`. -/
@[mmp "def_kr3b_restriction_blowup_sequence"]
def restrictHom {X : Scheme.{u}} (B : ClosedBlowupSequence X) (S : X.IdealSheafData) :
    (B.restrict S).target ⟶ B.target :=
  B.pullbackHom S.subschemeι

/-- `𝐁^X` is a *push-forward* of `𝐁(S)` along `j : S → X` (Kollár 3.30.3): both have the same
length and, with `j_0 = j` and `j_{i+1}` the canonical lift of `j_i` along `Z^X_i`, for every
`i < r` the centre `Z^X_i` is the scheme-theoretic image `(j_i)_*Z^S_i` and `j_i⁻¹Z^X_i = Z^S_i`
(the last identification transporting `j_{i+1}` to `S_{i+1} = B_{Z^S_i}S_i`). -/
@[mmp "def_kr3b_pushforward_blowup_sequence"]
def IsPushforward : {S X : Scheme.{u}} → (S ⟶ X) → ClosedBlowupSequence S →
    ClosedBlowupSequence X → Prop
  | _, _, _, nil _, nil _ => True
  | _, _, j, cons ZS BS, cons ZX BX =>
      ∃ h : ZX.comap j = ZS, ZX = ZS.map j ∧
        IsPushforward (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j ZX) BS BX
  | _, _, _, nil _, cons _ _ => False
  | _, _, _, cons _ _, nil _ => False

/-! ### Empty blow-ups -/

/-- A blow-up sequence *has no empty blow-ups* if no centre `Z_i` is empty (Kollár 3.32). -/
@[mmp "def_kr3b_delete_empty_blowups"]
def HasNoEmptyBlowups : {X : Scheme.{u}} → ClosedBlowupSequence X → Prop
  | _, nil _ => True
  | _, cons Z B => Z ≠ ⊤ ∧ B.HasNoEmptyBlowups

/-- If the inverse image of `Z` along `h : Y → X` is empty, `h` lifts to `B_ZX`. -/
theorem isCartierOver_of_comap_eq_top {X Y : Scheme.{u}} (h : Y ⟶ X) (Z : X.IdealSheafData)
    (hZ : Z.comap h = ⊤) : Stacks.Blowup.IsCartierOver Z (Over.mk h) := by
  change Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap h)
  rw [hZ]
  exact Stacks.Divisors.isEffectiveCartierDivisor_top

open Classical in
/-- The pull-back `h^*𝐁` with its empty blow-ups deleted: a step whose pulled-back centre
`h_i⁻¹Z_i` is empty is skipped, the sequence continuing on `Y_i` with `h_i` lifted to
`X_{i+1} = B_{Z_i}X_i` (Kollár 3.32). -/
@[mmp "def_kr3b_delete_empty_blowups"]
def pullbackReduced : {X Y : Scheme.{u}} → ClosedBlowupSequence X → (Y ⟶ X) →
    ClosedBlowupSequence Y
  | _, Y, nil _, _ => nil Y
  | _, _, cons Z B, h =>
      if hZ : Z.comap h = ⊤ then
        B.pullbackReduced (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ))
      else cons (Z.comap h) (B.pullbackReduced (canonicalLift h Z))

/-- The *reduction* `𝐁^red` of a blow-up sequence (Kollár 3.32): every step with empty centre
`Z_i` (for which `X_{i+1} = B_∅X_i ≅ X_i`) is deleted and the remaining steps renumbered. -/
@[mmp "def_kr3b_delete_empty_blowups"]
def reduction {X : Scheme.{u}} (B : ClosedBlowupSequence X) : ClosedBlowupSequence X :=
  B.pullbackReduced (𝟙 X)

/-- The reduction has no empty blow-ups. -/
@[mmp "def_kr3b_delete_empty_blowups"]
theorem hasNoEmptyBlowups_reduction {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    B.reduction.HasNoEmptyBlowups := by
  have key : ∀ {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X),
      (B.pullbackReduced h).HasNoEmptyBlowups := by
    intro X Y B h
    induction B generalizing Y with
    | nil X => simp [pullbackReduced, HasNoEmptyBlowups]
    | cons Z B ih =>
      by_cases hZ : Z.comap h = ⊤
      · simpa [pullbackReduced, hZ] using ih _
      · simpa [pullbackReduced, hZ, HasNoEmptyBlowups] using ih _
  exact key B _

private theorem canonicalLift_id_eq_eqToHom {X : Scheme.{u}} (Z : X.IdealSheafData) :
    canonicalLift (𝟙 X) Z = eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_id Z)) := by
  have key : ∀ (Z' : X.IdealSheafData) (e : Z' = Z),
      eqToHom (congrArg blowUp e) ≫ blowUpToBase Z = blowUpToBase Z' := by
    rintro _ rfl
    simp
  symm
  exact blowUpLift_unique _ _ _ _ (by
    rw [key _ (Scheme.IdealSheafData.comap_id Z)]
    simp)

private theorem pullbackReduced_heq_self {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (hB : B.HasNoEmptyBlowups) {Y : Scheme.{u}} (e : Y = X) (h : Y ⟶ X) (hh : h = eqToHom e) :
    B.pullbackReduced h ≍ B := by
  induction B generalizing Y with
  | nil X =>
    subst e
    rfl
  | cons Z B ih =>
    subst e
    obtain rfl : h = 𝟙 _ := by simpa using hh
    have hc : Z.comap (𝟙 _) = Z := Scheme.IdealSheafData.comap_id Z
    simp only [pullbackReduced, hc ▸ hB.1, dite_false]
    exact heq_of_eq (cons_eq_cons_iff.2
      ⟨hc, ih hB.2 (congrArg blowUp hc) _ (canonicalLift_id_eq_eqToHom Z)⟩)

/-- A blow-up sequence without empty blow-ups is its own reduction. -/
@[mmp "def_kr3b_delete_empty_blowups"]
theorem reduction_eq_self {X : Scheme.{u}} {B : ClosedBlowupSequence X}
    (hB : B.HasNoEmptyBlowups) : B.reduction = B :=
  eq_of_heq (pullbackReduced_heq_self B hB rfl _ (by simp))

/-- Blowing up the empty subscheme changes nothing: `B_∅X → X` is an isomorphism. -/
@[mmp "def_kr3b_delete_empty_blowups"]
theorem isIso_blowUpToBase_top (X : Scheme.{u}) :
    IsIso (blowUpToBase (⊤ : X.IdealSheafData)) := by
  have hc : ∀ {Y : Scheme.{u}} (h : Y ⟶ X), Stacks.Blowup.IsCartierOver (⊤ : X.IdealSheafData)
      (Over.mk h) := fun h =>
    isCartierOver_of_comap_eq_top h ⊤ (by simp)
  refine ⟨blowUpLift ⊤ (𝟙 X) (hc _), ?_, blowUpLift_comp _ _ _⟩
  rw [blowUpLift_unique ⊤ (blowUpToBase ⊤) (hc _) (blowUpToBase ⊤ ≫ blowUpLift ⊤ (𝟙 X) (hc _))
      (by rw [Category.assoc, blowUpLift_comp, Category.comp_id]),
    blowUpLift_unique ⊤ (blowUpToBase ⊤) (hc _) (𝟙 _) (by simp)]

/-! ### Total transforms and the total exceptional set -/

/-- One step of the total transform: `π⁻¹(E ∖ Z)‾ ∪ π⁻¹(Z) ⊆ B_ZX` for `E ⊆ X`. -/
@[mmp "def_kr3b_total_transform"]
def totalTransformStep {X : Scheme.{u}} (Z : X.IdealSheafData) (E : Set X) : Set (blowUp Z) :=
  closure (blowUpToBase Z ⁻¹' (E \ (Z.support : Set X))) ∪
    blowUpToBase Z ⁻¹' (Z.support : Set X)

/-- The *total transform* `Π⁻¹_tot(E) ⊆ X_r` of `E ⊆ X` (Kollár Def. 3.25):
`Π_0⁻¹_tot(E) = E` and `Π_{i+1}⁻¹_tot(E) = π_i⁻¹(Π_i⁻¹_tot(E) ∖ Z_i)‾ ∪ π_i⁻¹(Z_i)`. The
transforms `Π_i⁻¹_tot(E)` are those of the truncations `𝐁.truncate i`. -/
@[mmp "def_kr3b_total_transform"]
def totalTransform : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → Set X → Set B.target
  | _, nil _, E => E
  | _, cons Z B, E => B.totalTransform (totalTransformStep Z E)

/-- The total transform of a closed subset is a closed subset. -/
@[mmp "def_kr3b_total_transform"]
theorem isClosed_totalTransform {X : Scheme.{u}} (B : ClosedBlowupSequence X) {E : Set X}
    (hE : IsClosed E) : IsClosed (B.totalTransform E) := by
  induction B with
  | nil X => exact hE
  | cons Z B ih =>
    exact ih (isClosed_closure.union (Z.support.isClosed.preimage (blowUpToBase Z).continuous))

/-- The *total exceptional set* `Ex_tot(Π) = ⋃_{i<r} Π_{ri}⁻¹(Z_i) ⊆ X_r` (Kollár Def. 3.25).
`Ex_tot(Π_i)` is that of `𝐁.truncate i`. -/
@[mmp "def_kr3b_total_exceptional_set"]
def totalExceptionalSet : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → Set B.target
  | _, nil _ => ∅
  | _, cons Z B => B.toBase ⁻¹' (blowUpToBase Z ⁻¹' (Z.support : Set _)) ∪ B.totalExceptionalSet

/-- The total exceptional set is closed. -/
@[mmp "def_kr3b_total_exceptional_set"]
theorem isClosed_totalExceptionalSet {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    IsClosed B.totalExceptionalSet := by
  induction B with
  | nil X => exact isClosed_empty
  | cons Z B ih =>
    exact ((Z.support.isClosed.preimage (blowUpToBase Z).continuous).preimage
      B.toBase.continuous).union ih

end ClosedBlowupSequence

/-! ### Divisors with ordered index set -/

/-- A finite sequence `E = (E^1, …, E^s)` of closed subschemes of `X`; it is a *divisor with
ordered index set* when `IsOrderedDivisor` holds (Kollár Def. 3.31(1)). -/
@[mmp "def_kr3b_ordered_divisor"]
structure OrderedDivisor (X : Scheme.{u}) where
  /-- The number `s` of divisors. -/
  s : ℕ
  /-- The divisors `E^1, …, E^s`. -/
  E : Fin s → X.IdealSheafData

namespace OrderedDivisor

variable {X Y : Scheme.{u}}

/-- `E = (E^1, …, E^s)` is a *divisor with ordered index set*: every `E^i` is a reduced
effective Cartier divisor (Kollár Def. 3.31(1)). -/
@[mmp "def_kr3b_ordered_divisor"]
def IsOrderedDivisor (E : OrderedDivisor X) : Prop :=
  ∀ i, IsReduced (E.E i).subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor (E.E i)

/-- The support `⋃ᵢ E^i` of `∑ᵢ E^i`. -/
@[mmp "def_kr3b_ordered_divisor"]
def support (E : OrderedDivisor X) : Set X :=
  ⋃ i, ((E.E i).support : Set X)

/-- The inverse image `h⁻¹E = (h⁻¹E^1, …, h⁻¹E^s)`. -/
def comap (E : OrderedDivisor X) (h : Y ⟶ X) : OrderedDivisor Y :=
  ⟨E.s, fun i => (E.E i).comap h⟩

/-- The empty ordered divisor `()`. -/
def empty (X : Scheme.{u}) : OrderedDivisor X := ⟨0, Fin.elim0⟩

end OrderedDivisor

/-! ### Simple normal crossings -/

section SNC

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- A family `E = ∑_{i ∈ Λ} E^i` of closed subschemes of a scheme `X` over `k` is a *simple
normal crossing divisor* (Kollár Def. 3.24): every `E^i` is reduced, of pure codimension one
and smooth over `k`, and for every point `x ∈ X` there are local coordinates `z_1, …, z_n` at
`x` (a regular system of parameters of `𝒪_{X,x}`) and an injective map
`c : {i ∈ Λ | x ∈ E^i} → {1, …, n}`, defined only on the components through `x`, such that
`E^i = (z_{c(i)} = 0)` near `x` (on stalks at `x`) for every `E^i ∋ x`. (The source's index set
`Λ` is finite. Asking for `c(i)` at every `i` would make every nonempty family fail at the
generic points of `X`, where `n = 0`.) -/
@[mmp "def_kr3b_snc_divisor"]
def IsSNCFamily {Λ : Type*} (E : Λ → X.IdealSheafData) : Prop :=
  (∀ i, IsReduced (E i).subscheme ∧ MMP.Mori.IsPureCodimOne (E i).support ∧
      MMP.Mori.IsSmoothScheme ((E i).subschemeι ≫ sX)) ∧
    ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (c : {i // x ∈ (E i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c

/-- An ordered divisor `E` whose sum `∑ᵢ E^i` is a simple normal crossing divisor. -/
@[mmp "def_kr3b_snc_divisor"]
def OrderedDivisor.IsSNC (E : OrderedDivisor X) : Prop :=
  IsSNCFamily sX E.E

/-- The irreducible components of a subset `D` of a topological space: its maximal irreducible
subsets. -/
@[mmp "def_kr3b_snc_closed_subset"]
def componentsOf {T : Type*} [TopologicalSpace T] (D : Set T) : Set (Set T) :=
  {W | Maximal (fun W' : Set T => IsIrreducible W' ∧ W' ⊆ D) W}

/-- The family of irreducible components of `D ⊆ X`, each with its reduced structure. -/
@[mmp "def_kr3b_snc_closed_subset"]
def componentsFamily (D : Set X) : componentsOf D → X.IdealSheafData :=
  fun W => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (W : Set X))

/-- A subset `D` of a scheme `X` over `k` is a *divisor with simple normal crossings*
(Kollár Thm. 3.27(3)): `D` is closed, and either empty or it is of pure codimension one, has
finitely many irreducible components, and the sum of its irreducible components, each with its
reduced structure, is a simple normal crossing divisor. -/
@[mmp "def_kr3b_snc_closed_subset"]
def IsSNCClosedSubset (D : Set X) : Prop :=
  ∃ hD : IsClosed D, D = ∅ ∨
    (MMP.Mori.IsPureCodimOne (⟨D, hD⟩ : Closeds X) ∧ (componentsOf D).Finite ∧
      IsSNCFamily sX (componentsFamily D))

/-- A closed subscheme `Z ⊆ X` *has simple normal crossings with* the family
`E = ∑_{i ∈ Λ} E^i` (Kollár Def. 3.24(4), corrected): for every `x ∈ Z` there are local
coordinates `z_1, …, z_n` at `x` satisfying (1)–(3) of `IsSNCFamily` at `x` (with `c` defined
on the components through `x` only), and a subset
`J ⊆ {1, …, n}` with `Z = (z_j = 0 : j ∈ J)` near `x` (on stalks at `x`). -/
@[mmp "def_kr3b_snc_with_divisor"]
def HasSNCWith {Λ : Type*} (E : Λ → X.IdealSheafData) (Z : X.IdealSheafData) : Prop :=
  ∀ x ∈ (Z.support : Set X), ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x)
      (c : {i // x ∈ (E i).support} → Fin n) (J : Finset (Fin n)),
    MMP.Mori.IsRegularSystemOfParameters z ∧
      (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c ∧
      IdealSheafData.stalk Z x = Ideal.span (z '' (J : Set (Fin n)))

/-- An ideal sheaf `I` on a scheme `X` is *(locally) monomial* (Kollár 3.16(1)): for every
`x ∈ X` there are local coordinates `z_1, …, z_n` at `x` (a regular system of parameters of
`𝒪_{X,x}`) and `c_1, …, c_n ∈ ℕ` with `I·𝒪_{X,x} = (∏ᵢ zᵢ^{cᵢ})·𝒪_{X,x}`. -/
@[mmp "def_kr3b_monomial_ideal"]
def IsMonomialIdeal (I : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (c : Fin n → ℕ),
    MMP.Mori.IsRegularSystemOfParameters z ∧
      IdealSheafData.stalk I x = Ideal.span {∏ i, z i ^ c i}

namespace ClosedBlowupSequence

/-- A blow-up sequence of a scheme `X` over `k` is a *smooth blow-up sequence* (Kollár
Def. 3.29): every `X_i` and every centre `Z_i` (`0 ≤ i < r`) is smooth over `k`, each `X_i`
being over `k` by `X_i → X → Spec k`. -/
@[mmp "def_kr3b_smooth_blowup_sequence"]
def IsSmooth : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → ClosedBlowupSequence X → Prop
  | _, _, nil _ => True
  | _, s, cons Z B => MMP.Mori.IsSmoothScheme s ∧ MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) ∧
      B.IsSmooth (blowUpToBase Z ≫ s)

/-- The centres of a blow-up sequence starting with `X` over `k` *have simple normal crossings
with* `E ⊆ X` (Kollár Def. 3.25): for every `0 ≤ i < r` the total transform
`Π_i⁻¹_tot(E) ⊆ X_i` is a divisor with simple normal crossings and `Z_i` has simple normal
crossings with the sum of the irreducible components of `Π_i⁻¹_tot(E)`. -/
@[mmp "def_kr3b_centers_snc_with_divisor"]
def CentersHaveSNCWith : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → ClosedBlowupSequence X →
    Set X → Prop
  | _, _, nil _, _ => True
  | _, s, cons Z B, E => IsSNCClosedSubset s E ∧ HasSNCWith (componentsFamily E) Z ∧
      B.CentersHaveSNCWith (blowUpToBase Z ≫ s) (totalTransformStep Z E)

end ClosedBlowupSequence

end SNC

/-! ### Triples and blow-up sequence functors -/

/-- A triple `(X, I, E)`: a scheme `X`, an ideal sheaf `I ⊆ 𝒪_X` and a sequence `E` of closed
subschemes (Kollár Def. 3.31). -/
@[mmp "def_kr3b_blowup_sequence_functor"]
structure BlowupTriple where
  /-- The scheme `X`. -/
  X : Scheme.{u}
  /-- The ideal sheaf `I`. -/
  I : X.IdealSheafData
  /-- The divisor with ordered index set `E`. -/
  E : OrderedDivisor X

/-- The ideal sheaf `I ⊆ 𝒪_X` is nonzero at the generic point of every irreducible component
of `X`. -/
@[mmp "def_kr3b_blowup_sequence_functor"]
def IsNonzeroAtGenericPoints {X : Scheme.{u}} (I : X.IdealSheafData) : Prop :=
  ∀ η : X, closure ({η} : Set X) ∈ irreducibleComponents X → IdealSheafData.stalk I η ≠ ⊥

/-- The triple `(X, I, E)` is of the kind of Kollár Def. 3.31: `X` is locally noetherian, `I` is
nonzero at the generic point of every irreducible component of `X`, and `E` is a divisor with
ordered index set. -/
@[mmp "def_kr3b_blowup_sequence_functor"]
def BlowupTriple.IsAdmissible (t : BlowupTriple.{u}) : Prop :=
  IsLocallyNoetherian t.X ∧ IsNonzeroAtGenericPoints t.I ∧ t.E.IsOrderedDivisor

/-- A *blow-up sequence functor* on a class `𝒯` of triples (Kollár Def. 3.31), the triples
being given as the image of `toTriple : T → BlowupTriple` (for the snc triples of 3.35, `T`
also records the ground field): an assignment of a blow-up sequence `𝐁(t)` starting with `X`
to every `t ∈ 𝒯`. Functoriality is imposed separately (3.34). -/
@[mmp "def_kr3b_blowup_sequence_functor"]
def BlowupSequenceFunctor {T : Type*} (toTriple : T → BlowupTriple.{u}) (𝒯 : Set T) :
    Type _ :=
  ∀ t ∈ 𝒯, ClosedBlowupSequence (toTriple t).X

/-- A triple `(X, I, E)` over a field `k`, the field and `X → Spec k` being part of the data
(Kollár 3.34, 3.35). -/
@[mmp "def_kr3b_snc_triples"]
structure FieldBlowupTriple extends BlowupTriple.{u} where
  /-- The ground field `k`. -/
  k : Type u
  [field : Field k]
  /-- The structure morphism `X → Spec k`. -/
  sX : X ⟶ Spec (.of k)

attribute [instance] FieldBlowupTriple.field

namespace FieldBlowupTriple

variable (t : FieldBlowupTriple.{u})

/-- The pulled-back triple `(Y, h^*I, h⁻¹E)` along `h : Y → X`, over `k` by `Y → X → Spec k`. -/
@[mmp "def_kr3b_commutes_with_morphism"]
def pullback {Y : Scheme.{u}} (h : Y ⟶ t.X) : FieldBlowupTriple.{u} where
  X := Y
  I := t.I.comap h
  E := t.E.comap h
  k := t.k
  sX := h ≫ t.sX

variable {L : Type u} [Field L] (σ : t.k →+* L)

/-- `X_{L,σ} = X ×_{Spec k} Spec L`. -/
@[mmp "def_kr3b_field_change_triple"]
abbrev fieldChangeScheme : Scheme.{u} :=
  Limits.pullback t.sX (Spec.map (CommRingCat.ofHom σ))

/-- The projection `p_σ : X_{L,σ} → X`. -/
@[mmp "def_kr3b_field_change_triple"]
abbrev fieldChangeProj : t.fieldChangeScheme σ ⟶ t.X :=
  Limits.pullback.fst _ _

/-- The *field change* `(X_{L,σ}, I_{L,σ}, E_{L,σ}) = (X_{L,σ}, p_σ^*I, p_σ⁻¹E)` of `(X, I, E)`
along `σ : k → L` (Kollár 3.34.2), an `L`-scheme by the second projection. The field change
of a blow-up sequence is its pull-back along `p_σ`. -/
@[mmp "def_kr3b_field_change_triple"]
def fieldChange : FieldBlowupTriple.{u} where
  X := t.fieldChangeScheme σ
  I := t.I.comap (t.fieldChangeProj σ)
  E := t.E.comap (t.fieldChangeProj σ)
  k := L
  sX := Limits.pullback.snd _ _

/-- For `X` of finite type over `k`, `X_{L,σ}` is of finite type over `L`. -/
@[mmp "def_kr3b_field_change_triple"]
theorem fieldChange_finiteType [LocallyOfFiniteType t.sX] [QuasiCompact t.sX] :
    LocallyOfFiniteType (t.fieldChange σ).sX ∧ QuasiCompact (t.fieldChange σ).sX :=
  ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›⟩

end FieldBlowupTriple

/-- The class `𝒯^snc` of triples `(X, I, E)` (Kollár Thm. 3.35): `X` smooth of finite type over a
field `k` of characteristic `0`, `I ⊆ 𝒪_X` a coherent ideal sheaf nonzero at the generic point
of every irreducible component of `X`, and `E` a divisor with ordered index set whose sum is a
simple normal crossing divisor. (On `X` of finite type over `k` every quasi-coherent ideal
sheaf is coherent.) -/
@[mmp "def_kr3b_snc_triples"]
def sncTriples : Set FieldBlowupTriple.{u} :=
  {t | CharZero t.k ∧ MMP.Mori.IsSmoothScheme t.sX ∧ LocallyOfFiniteType t.sX ∧
      QuasiCompact t.sX ∧ IsNonzeroAtGenericPoints t.I ∧ t.E.IsOrderedDivisor ∧
      t.E.IsSNC t.sX}

/-- A blow-up sequence functor on `𝒯^snc` (Kollár 3.31, 3.35). -/
@[mmp "def_kr3b_snc_triples"]
abbrev SNCBlowupSequenceFunctor : Type (u + 1) :=
  BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple sncTriples.{u}

namespace SNCBlowupSequenceFunctor

variable (B : SNCBlowupSequenceFunctor.{u})

/-- `𝐁` *commutes with* `h : Y → X` at `(X, I, E) ∈ 𝒯^snc` (Kollár 3.34.1): if
`(Y, h^*I, h⁻¹E) ∈ 𝒯^snc`, then `𝐁(Y, h^*I, h⁻¹E) = h^*𝐁(X, I, E)` as blow-up sequences. -/
@[mmp "def_kr3b_commutes_with_morphism"]
def CommutesWith (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) {Y : Scheme.{u}}
    (h : Y ⟶ t.X) : Prop :=
  ∀ hY : t.pullback h ∈ sncTriples, B (t.pullback h) hY = (B t ht).pullback h

/-- `𝐁` *commutes with `P` surjections* (Kollár 3.34.1, first bullet; `P` smooth or étale): it
commutes with every surjective `h : Y → X` in `P` with `Y` of finite type over `k`, at every
`(X, I, E) ∈ 𝒯^snc`. -/
@[mmp "def_kr3b_commutes_with_smooth_surjections"]
def CommutesWithSurjections (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) (Y : Scheme.{u}) (h : Y ⟶ t.X),
    P h → Surjective h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
      B.CommutesWith t ht h

/-- `𝐁` *commutes with `P` morphisms* (Kollár 3.34.1; `P` smooth or étale): it commutes with
`P` surjections, and for every `(X, I, E) ∈ 𝒯^snc` and every `h : Y → X` in `P` with `Y` of
finite type over `k`, `𝐁(Y, h^*I, h⁻¹E) = (h^*𝐁(X, I, E))^red`. For `P = @Smooth` this is
"`𝐁` commutes with smooth morphisms". -/
@[mmp "def_kr3b_commutes_with_smooth_morphisms"]
def CommutesWithMorphisms (P : MorphismProperty Scheme.{u}) : Prop :=
  B.CommutesWithSurjections P ∧
    ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) (Y : Scheme.{u}) (h : Y ⟶ t.X),
      P h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
        ∀ hY : t.pullback h ∈ sncTriples, B (t.pullback h) hY = ((B t ht).pullback h).reduction

/-- `𝐁` *commutes with change of fields* (Kollár 3.34.2): for every field extension
`σ : K ↪ L` and every `(X, I, E) ∈ 𝒯^snc` over `K`,
`𝐁(X_{L,σ}, I_{L,σ}, E_{L,σ}) = 𝐁(X, I, E)_{L,σ}`, the pull-back along `p_σ`. -/
@[mmp "def_kr3b_commutes_with_field_change"]
def CommutesWithFieldChange : Prop :=
  ∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) (L : Type u) [Field L] (σ : t.k →+* L)
    (hL : t.fieldChange σ ∈ sncTriples),
    B (t.fieldChange σ) hL = (B t ht).pullback (t.fieldChangeProj σ)

end SNCBlowupSequenceFunctor

/-- *Closed-embedding data* `(j : Y ↪ X; I_Y, I_X; E)` (Kollár 3.34.3): a closed embedding
`j` of schemes over `k`, ideal sheaves `I_X`, `I_Y` with `𝒪_X/I_X = j_*(𝒪_Y/I_Y)`, that is,
`I_X = ker(𝒪_X → j_*(𝒪_Y/I_Y))`, and an ordered divisor `E` on `X`. The conditions
`(X, I_X, E), (Y, I_Y, E|_Y) ∈ 𝒯^snc` are imposed in
`SNCBlowupSequenceFunctor.CommutesWithClosedEmbeddings`. -/
@[mmp "def_kr3b_commutes_with_closed_embeddings"]
structure ClosedEmbeddingData where
  /-- The ground field. -/
  k : Type u
  [field : Field k]
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism. -/
  sX : X ⟶ Spec (.of k)
  /-- The embedded scheme. -/
  Y : Scheme.{u}
  /-- The closed embedding. -/
  j : Y ⟶ X
  /-- The morphism `j` is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion j
  /-- The ideal sheaf on `X`. -/
  IX : X.IdealSheafData
  /-- The ideal sheaf on `Y`. -/
  IY : Y.IdealSheafData
  /-- The ordered divisor on `X`. -/
  E : OrderedDivisor X
  /-- `I_X` is the image of `I_Y` under `j`. -/
  IX_eq : IX = IY.map j

attribute [instance] ClosedEmbeddingData.field

namespace ClosedEmbeddingData

variable (d : ClosedEmbeddingData.{u})

/-- The triple `(X, I_X, E)` over `k`. -/
@[mmp "def_kr3b_commutes_with_closed_embeddings"]
def ambientTriple : FieldBlowupTriple.{u} := ⟨⟨d.X, d.IX, d.E⟩, d.k, d.sX⟩

/-- The triple `(Y, I_Y, E|_Y)` over `k`, `E|_Y = (E^1 ∩ Y, …, E^s ∩ Y)`. -/
@[mmp "def_kr3b_commutes_with_closed_embeddings"]
def embeddedTriple : FieldBlowupTriple.{u} := ⟨⟨d.Y, d.IY, d.E.comap d.j⟩, d.k, d.j ≫ d.sX⟩

end ClosedEmbeddingData

/-- `𝐁` *commutes with closed embeddings* for a class `𝒞` of closed-embedding data (Kollár
3.34.3; e.g. those with `E = ∅`): for all such data with `(X, I_X, E), (Y, I_Y, E|_Y) ∈ 𝒯^snc`,
`𝐁(X, I_X, E)` is a push-forward of `𝐁(Y, I_Y, E|_Y)` along `j`. -/
@[mmp "def_kr3b_commutes_with_closed_embeddings"]
def SNCBlowupSequenceFunctor.CommutesWithClosedEmbeddings (B : SNCBlowupSequenceFunctor.{u})
    (𝒞 : Set ClosedEmbeddingData.{u}) : Prop :=
  ∀ d ∈ 𝒞, ∀ (hX : d.ambientTriple ∈ sncTriples) (hY : d.embeddedTriple ∈ sncTriples),
    ClosedBlowupSequence.IsPushforward d.j (B d.embeddedTriple hY) (B d.ambientTriple hX)

/-! ### Principalization -/

/-- A *principalization* of an ideal sheaf `I ⊆ 𝒪_X` on a variety `X` over `k` (Kollár §3.3):
a birational morphism `g : X' → X` from a smooth variety `X'` over `k` (by `X' → X → Spec k`)
such that the inverse image ideal sheaf `g^*I` is locally principal. Projectivity of `g` is not
required. -/
@[mmp "def_kr3b_principalization"]
def IsPrincipalization {k : Type u} [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (g : X' ⟶ X) : Prop :=
  IsVariety k (g ≫ sX) ∧ MMP.Mori.IsSmoothScheme (g ≫ sX) ∧ MMP.Mori.IsBirationalMorphism g ∧
    Stacks.Divisors.IsLocallyPrincipal (I.comap g)

end MMP.Resolution
