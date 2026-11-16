module

public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Triples and smooth blow-up sequences of order `m` (Kollár, *Resolution*, 3.49, 3.63–3.66)

A *triple* `(X, I, E)` (Kollár Notation 3.64) is a smooth equidimensional scheme `X` of finite type
over a field of characteristic `0`, a coherent ideal sheaf `I` nonzero on every irreducible
component and an ordered simple normal crossing divisor `E`; a *marked triple* `(X, I, m, E)`
adds a marking `m`. A *smooth blow-up of order `m`* of a triple blows up a center `Z` having
simple normal crossings with `E` along which `ord_Z I = m = maxord I`; the triple is then
replaced by its birational transform `(B_ZX, π⁻¹_{Z*}I, π⁻¹_tot E)` (Def. 3.65, 3.66). Iterating
gives the smooth blow-up sequences of order `m` (resp. `≥ m`) starting with a triple (resp.
marked triple), and their plain versions starting with `(X, I)` (resp. `(X, I, m)`) (3.49).

## Main definitions

* `MMP.Resolution.OrderedDivisor.IsOrderedSNC`: ordered snc divisors.
* `MMP.Resolution.IsTriple`, `MMP.Resolution.triples`, `MMP.Resolution.MarkedTriple`,
  `MMP.Resolution.markedTriples`.
* `MMP.Resolution.OrderedDivisor.totalTransform`: `π⁻¹_tot(E)`.
* `MMP.Resolution.ClosedBlowupSequence.markedTransform`, `…controlledTransform`,
  `…orderedTotalTransform`: the iterated transforms `Π⁻¹_*(I, m)`, `I_r`, `E_r`.
* `MMP.Resolution.ClosedBlowupSequence.IsOrderGeMarkedTripleSeq`, `…IsOrderMTripleSeq`,
  `…IsOrderGePlainSeq`, `…IsOrderMPlainSeq`: the four kinds of smooth blow-up sequences.
* `MMP.Resolution.IsSmoothBlowupOfOrder`, `MMP.Resolution.IsSmoothBlowupOfMarkedTriple`.

## Implementation notes

The triples `(X_i, I_i, E_i)` along a blow-up sequence are determined by the sequence and the
starting triple (`I_{i+1}`, `E_{i+1}` are transforms of `I_i`, `E_i`), so the sequences of
Def. 3.66 and 3.49 are predicates on a `ClosedBlowupSequence`, the triples being computed
recursively. Each `X_i` is over `k` by `X_i → X → Spec k`. A smooth blow-up sequence asks
`X_i` and `Z_i` smooth (`ClosedBlowupSequence.IsSmooth`); smoothness of `X_i` is part of the
triple condition and is asked separately in the plain sequences.

The precondition `maxord I ≤ m` of the order-`m` sequences only restricts the domain and is
dropped. Coherence of the ideal sheaves is automatic on schemes of finite type over a field.
Orders and markings are compared in `ℕ∞`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.49, 3.63–3.66]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Ordered snc divisors and triples -/

section Triples

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

attribute [mmp "def_kr3c_ordered_snc_divisor"] OrderedDivisor.support

/-- An *ordered simple normal crossing divisor* `E = (E^1, …, E^s)` on a scheme `X` over `k`
(Kollár Notation 3.64(3)): a divisor with ordered index set whose entries are smooth reduced
divisors (possibly reducible or empty) with `∑ᵢ E^i` a simple normal crossing divisor. Its
support is `OrderedDivisor.support`. -/
@[mmp "def_kr3c_ordered_snc_divisor"]
def OrderedDivisor.IsOrderedSNC (E : OrderedDivisor X) : Prop :=
  E.IsOrderedDivisor ∧ E.IsSNC sX

/-- `(X, I, E)`, `X` over `k` by `s_X`, is a *triple* (Kollár Notation 3.64): `X` is smooth,
equidimensional and of finite type over `k`, `k` has characteristic `0`, `I` is nonzero on
every irreducible component of `X`, and `E` is an ordered snc divisor. -/
@[mmp "def_kr3c_triple"]
def IsTriple (I : X.IdealSheafData) (E : OrderedDivisor X) : Prop :=
  CharZero k ∧ MMP.Mori.IsSmoothScheme sX ∧ LocallyOfFiniteType sX ∧ QuasiCompact sX ∧
    Equidimensional X ∧ IsNonzeroAtGenericPoints I ∧ E.IsOrderedSNC sX

/-- The class of all triples `(X, I, E)` (Kollár Notation 3.64). -/
@[mmp "def_kr3c_triple"]
def triples : Set FieldBlowupTriple.{u} :=
  {t | IsTriple t.sX t.I t.E}

end Triples

/-- A *marked triple* `(X, I, m, E)` (Kollár Notation 3.64 and footnote 1): a triple `(X, I, E)`
over a field together with a marking `m ∈ ℕ`; it is a marked triple when it lies in
`markedTriples`. -/
@[mmp "def_kr3c_marked_triple"]
structure MarkedTriple extends FieldBlowupTriple.{u} where
  /-- The marking `m`. -/
  m : ℕ

namespace MarkedTriple

/-- The marked ideal `(I, m)` of a marked triple. -/
@[mmp "def_kr3c_marked_triple"]
def markedIdeal (t : MarkedTriple.{u}) : MarkedIdeal t.X :=
  ⟨t.I, t.m⟩

/-- The ideal of the marked ideal of a marked triple is its ideal `I`. -/
@[simp] theorem markedIdeal_I (t : MarkedTriple.{u}) : t.markedIdeal.I = t.I := rfl

/-- The marking of the marked ideal of a marked triple is its marking `m`. -/
@[simp] theorem markedIdeal_m (t : MarkedTriple.{u}) : t.markedIdeal.m = t.m := rfl

end MarkedTriple

/-- The class of marked triples: those `(X, I, m, E)` with `(X, I, E)` a triple. -/
@[mmp "def_kr3c_marked_triple"]
def markedTriples : Set MarkedTriple.{u} :=
  {t | t.toFieldBlowupTriple ∈ triples}

/-! ### The total transform of an ordered divisor -/

section TotalTransform

variable {X : Scheme.{u}}

/-- The union `Z^{≥2}` of the irreducible components of `Z` of codimension `≥ 2`. -/
def componentsOfCodimAtLeastTwo (Z : Set X) : Set X :=
  ⋃ (W : Set X) (hW : W ∈ componentsOf Z) (_ : 2 ≤ codimension (irreducibleClosure hW.1.1)), W

/-- The *total transform* `π⁻¹_tot(E)` of a divisor with ordered index set `E = (E^1, …, E^s)`
under the blow-up `π : B_ZX → X` (Kollár Def. 3.65, corrected for trivial blow-ups): the
sequence of `s + 1` reduced divisors whose `i`-th entry (`i ≤ s`) is the birational transform
`π⁻¹_*E^i`, the reduced closure of `π⁻¹(E^i ∖ Z^{≥2})`, and whose last entry is the (reduced)
union of the `F_j = π⁻¹(Z_j)` for the irreducible components `Z_j` of `Z` that are not
irreducible components of `Supp E`. -/
@[mmp "def_kr3c_total_transform_ordered"]
def OrderedDivisor.totalTransform (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    OrderedDivisor (blowUp Z) where
  s := E.s + 1
  E := Fin.snoc (α := fun _ => (blowUp Z).IdealSheafData)
    (fun i => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase Z ⁻¹' ((E.E i).support \ componentsOfCodimAtLeastTwo (Z.support : Set X)))))
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf E.support),
        blowUpToBase Z ⁻¹' W)))

end TotalTransform

/-! ### Transforms along a blow-up sequence -/

namespace ClosedBlowupSequence

/-- The *iterated birational transform* `Π⁻¹_*(I, m) = (I_r, m)` of a marked ideal along a
blow-up sequence, `(I_{i+1}, m) = (π_i)⁻¹_{Z_i*}(I_i, m)` (Kollár Warning 3.63 (1)–(2)). -/
@[mmp "def_kr3c_iterated_marked_transform"]
def markedTransform : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → MarkedIdeal X →
    MarkedIdeal B.target
  | _, nil _, a => a
  | _, cons Z B, a => B.markedTransform (a.birationalTransform Z)

/-- The last ideal `I_r` of the iterated controlled transform `I_{i+1} = (π_i)⁻¹_{Z_i*}I_i`. -/
def controlledTransform : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → X.IdealSheafData →
    B.target.IdealSheafData
  | _, nil _, I => I
  | _, cons Z B, I => B.controlledTransform (MMP.Resolution.controlledTransform Z I)

/-- The last divisor `E_r` of the iterated total transform `E_{i+1} = (π_i)⁻¹_tot E_i`. -/
def orderedTotalTransform : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) →
    OrderedDivisor X → OrderedDivisor B.target
  | _, nil _, E => E
  | _, cons Z B, E => B.orderedTotalTransform (E.totalTransform Z)

variable {k : Type u} [Field k]

/-- A blow-up sequence `(X_i, Z_i)_{i ≤ r}` starting with `X` over `k` is a *smooth blow-up
sequence of order `≥ m` starting with the marked triple `(X, I, m, E)`* (Kollár Def. 3.66
(1′)–(4′)): with `(I_0, m) = (I, m)`, `E_0 = E`, `(I_{i+1}, m) = (π_i)⁻¹_{Z_i*}(I_i, m)` and
`E_{i+1} = (π_i)⁻¹_tot E_i`, every `(X_i, I_i, m, E_i)` is a marked triple and for every `i < r`
the center `Z_i` is smooth, its irreducible components have codimension `≥ 1`, `Z_i` has simple
normal crossings with `∑_j E_i^j`, and `ord_{Z_i} I_i ≥ m`. -/
@[mmp "def_kr3c_blowup_sequence_order_ge_m_marked_triple"]
def IsOrderGeMarkedTripleSeq : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → MarkedIdeal X →
    OrderedDivisor X → ClosedBlowupSequence X → Prop
  | _, s, a, E, nil _ => IsTriple s a.I E
  | X, s, a, E, cons Z B => IsTriple s a.I E ∧ MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) ∧
      HasComponentsOfPositiveCodim (Z.support : Set X) ∧ HasSNCWith E.E Z ∧
      OrderAlongGE a.I (Z.support : Set X) a.m ∧
      B.IsOrderGeMarkedTripleSeq (blowUpToBase Z ≫ s) (a.birationalTransform Z)
        (E.totalTransform Z)

/-- A blow-up sequence starting with `X` over `k` is a *smooth blow-up sequence of order `m`
starting with the triple `(X, I, E)`* (Kollár Def. 3.66 (1)–(4)): with `I_0 = I`, `E_0 = E`,
`I_{i+1} = (π_i)⁻¹_{Z_i*}I_i` (controlled transform) and `E_{i+1} = (π_i)⁻¹_tot E_i`, every
`(X_i, I_i, E_i)` is a triple and for every `i < r` the center `Z_i` is smooth, its
irreducible components have codimension `≥ 1`, `Z_i` has simple normal crossings with
`∑_j E_i^j`, and `ord_{Z_i} I_i = m`. -/
@[mmp "def_kr3c_blowup_sequence_order_m_triple"]
def IsOrderMTripleSeq : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → X.IdealSheafData →
    OrderedDivisor X → ℕ → ClosedBlowupSequence X → Prop
  | _, s, I, E, _, nil _ => IsTriple s I E
  | X, s, I, E, m, cons Z B => IsTriple s I E ∧ MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) ∧
      HasComponentsOfPositiveCodim (Z.support : Set X) ∧ HasSNCWith E.E Z ∧
      OrderAlongEq I (Z.support : Set X) m ∧
      B.IsOrderMTripleSeq (blowUpToBase Z ≫ s) (MMP.Resolution.controlledTransform Z I)
        (E.totalTransform Z) m

/-- A blow-up sequence starting with a smooth `X` over `k` is a *smooth blow-up sequence of
order `≥ m` starting with `(X, I, m)`* (Kollár 3.49): with `(I_0, m) = (I, m)` and
`(I_{i+1}, m) = (π_i)⁻¹_{Z_i*}(I_i, m)`, every `X_i` is smooth, every `I_i` is nonzero on every
irreducible component of `X_i`, and for every `i < r` the center `Z_i` is smooth, its
irreducible components have codimension `≥ 1`, and `ord_{Z_i} I_i ≥ m`. -/
@[mmp "def_kr3c_blowup_sequence_order_ge_m_plain"]
def IsOrderGePlainSeq : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → MarkedIdeal X →
    ClosedBlowupSequence X → Prop
  | _, s, a, nil _ => MMP.Mori.IsSmoothScheme s ∧ IsNonzeroAtGenericPoints a.I
  | X, s, a, cons Z B => MMP.Mori.IsSmoothScheme s ∧ IsNonzeroAtGenericPoints a.I ∧
      MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) ∧
      HasComponentsOfPositiveCodim (Z.support : Set X) ∧
      OrderAlongGE a.I (Z.support : Set X) a.m ∧
      B.IsOrderGePlainSeq (blowUpToBase Z ≫ s) (a.birationalTransform Z)

/-- A blow-up sequence starting with a smooth `X` over `k` is a *smooth blow-up sequence of
order `m` starting with `(X, I)`* (Kollár 3.49): with `I_0 = I` and
`I_{i+1} = (π_i)⁻¹_{Z_i*}I_i` (controlled transform), every `X_i` is smooth, every `I_i` is
nonzero on every irreducible component of `X_i`, and for every `i < r` the center `Z_i` is
smooth, its irreducible components have codimension `≥ 1`, and `ord_{Z_i} I_i = m`. -/
@[mmp "def_kr3c_blowup_sequence_order_m_plain"]
def IsOrderMPlainSeq : {X : Scheme.{u}} → (X ⟶ Spec (.of k)) → X.IdealSheafData → ℕ →
    ClosedBlowupSequence X → Prop
  | _, s, I, _, nil _ => MMP.Mori.IsSmoothScheme s ∧ IsNonzeroAtGenericPoints I
  | X, s, I, m, cons Z B => MMP.Mori.IsSmoothScheme s ∧ IsNonzeroAtGenericPoints I ∧
      MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s) ∧
      HasComponentsOfPositiveCodim (Z.support : Set X) ∧
      OrderAlongEq I (Z.support : Set X) m ∧
      B.IsOrderMPlainSeq (blowUpToBase Z ≫ s) (MMP.Resolution.controlledTransform Z I) m

/-- The iterated birational transform `Π⁻¹_*(I, m)` along a blow-up sequence keeps the
marking: `(B.markedTransform a).m = a.m`. -/
@[mmp "def_kr3c_iterated_marked_transform"]
theorem markedTransform_m {X : Scheme.{u}} (B : ClosedBlowupSequence X) (a : MarkedIdeal X) :
    (B.markedTransform a).m = a.m := by
  induction B with
  | nil => rfl
  | cons Z B ih => exact ih _

end ClosedBlowupSequence

/-! ### Smooth blow-ups of triples -/

section SmoothBlowup

/-- The blow-up `B_ZX → X` of a closed subscheme `Z` is a *smooth blow-up of order `m`* of the
triple `(X, I, E)`, `m = maxord I` (Kollár Def. 3.65 (1)–(2)): every irreducible component of `Z`
has codimension `≥ 1`, `Z` has simple normal crossings with `∑_i E^i`, and `ord_Z I = m`. -/
@[mmp "def_kr3c_smooth_blowup_order_m_triple"]
def IsSmoothBlowupOfOrder (t : FieldBlowupTriple.{u}) (Z : t.X.IdealSheafData) : Prop :=
  HasComponentsOfPositiveCodim (Z.support : Set t.X) ∧ HasSNCWith t.E.E Z ∧
    OrderAlongEq t.I (Z.support : Set t.X) (maxOrder t.I)

open IsLocalRing in
/-- Killing `z(J)` for `n` elements `z` of the maximal ideal of an `n`-dimensional Noetherian
local ring leaves a ring of dimension at least `n - #J`. -/
theorem natCast_sub_card_le_ringKrullDim_quotient_span_image {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {n : ℕ} (z : Fin n → A) (hdim : ringKrullDim A = n)
    (hz : ∀ j, z j ∈ maximalIdeal A) (J : Finset (Fin n)) :
    ((n - J.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ Ideal.span (z '' (J : Set (Fin n)))) := by
  classical
  have h2 := ringKrullDim_le_ringKrullDim_quotient_add_card (J.image z) (by
    intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    rw [SetLike.mem_coe, IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact hz j)
  rw [Finset.coe_image, hdim] at h2
  have hcard : (J.image z).card ≤ J.card := Finset.card_image_le
  generalize ringKrullDim (A ⧸ Ideal.span (z '' (J : Set (Fin n)))) = d at *
  induction d using WithBot.recBotCoe with
  | bot => simp at h2
  | coe d =>
    induction d using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      have h2' : (n : ℕ∞) ≤ ((m : ℕ) : ℕ∞) + ((J.image z).card : ℕ∞) :=
        WithBot.coe_le_coe.mp h2
      have h4 : n ≤ m + (J.image z).card := by exact_mod_cast h2'
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))

open IsLocalRing in
/-- A regular local ring modulo part `z(J)` of a regular system of parameters `z` is regular. -/
theorem isRegularLocalRing_quotient_span_image {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {n : ℕ} (z : Fin n → A) (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (J : Finset (Fin n)) :
    IsRegularLocalRing (A ⧸ Ideal.span (z '' (J : Set (Fin n)))) := by
  classical
  have hzm : ∀ j, z j ∈ maximalIdeal A := fun j => by
    rw [← hz.1]
    exact Ideal.subset_span ⟨j, rfl⟩
  set I := Ideal.span (z '' (J : Set (Fin n))) with hI
  have hIm : I ≤ maximalIdeal A := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, -, rfl⟩
    exact hzm j
  have hne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ hIm))
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
    have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr hIm]
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hgen : maximalIdeal (A ⧸ I) =
      Ideal.span (Ideal.Quotient.mk I '' (z '' ((Jᶜ : Finset (Fin n)) : Set (Fin n)))) := by
    rw [← hmax, ← hz.1, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i ∈ J
      · have : Ideal.Quotient.mk I (z i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span ⟨i, hi, rfl⟩)
        simp [this]
      · exact Ideal.subset_span ⟨_, ⟨i, by simpa using hi, rfl⟩, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨z i, ⟨i, rfl⟩, rfl⟩
  have h1 : (maximalIdeal (A ⧸ I)).spanFinrank ≤ (n - J.card : ℕ) := by
    rw [hgen]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.Finite.image _
      (Set.Finite.image _ (Finset.finite_toSet _)))).trans ?_
    calc _ ≤ ((Jᶜ : Finset (Fin n)) : Set (Fin n)).ncard := by
          refine (Set.ncard_image_le (Set.Finite.image _ (Finset.finite_toSet _))).trans ?_
          exact Set.ncard_image_le (Finset.finite_toSet _)
      _ = (n - J.card : ℕ) := by
          rw [Set.ncard_coe_finset, Finset.card_compl]
          simp
  have h6 : (Submodule.spanFinrank (maximalIdeal (A ⧸ I)) : WithBot ℕ∞) ≤
      ((n - J.card : ℕ) : WithBot ℕ∞) := by exact_mod_cast h1
  exact h6.trans (natCast_sub_card_le_ringKrullDim_quotient_span_image z hz.2 hzm J)

/-- A closed subscheme `Z` of a smooth scheme `X` locally of finite type over a field of
characteristic `0` having simple normal crossings with a family of divisors `E` is smooth over
`k`. -/
theorem isSmoothScheme_subschemeι_of_hasSNCWith {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (hsm : MMP.Mori.IsSmoothScheme sX) {ι : Type*} {E : ι → X.IdealSheafData}
    (Z : X.IdealSheafData) (hZ : HasSNCWith E Z) :
    MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX) := by
  have hXsm : Smooth sX := (MMP.Mori.isSmoothScheme_iff sX).mp hsm
  have : LocallyOfFinitePresentation (Z.subschemeι ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  intro y _
  rw [Scheme.Hom.mem_smoothLocus]
  refine InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap _ y ?_
  refine (Set.ext_iff.mp (smoothAt_locus_eq_regular_locus k (Z.subschemeι ≫ sX)) y).mpr ?_
  have hx : Z.subschemeι y ∈ (Z.support : Set X) := by
    rw [← Z.range_subschemeι]
    exact ⟨y, rfl⟩
  obtain ⟨n, z, c, J, hrsop, -, -, hstalk⟩ := hZ _ hx
  have hA : IsRegularLocalRing (X.presheaf.stalk (Z.subschemeι y)) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX _
  have hq := isRegularLocalRing_quotient_span_image z hrsop J
  rw [← hstalk, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk Z y] at hq
  let f := (Z.subschemeι.stalkMap y).hom
  change IsRegularLocalRing (Z.subscheme.presheaf.stalk y)
  exact IsRegularLocalRing.of_ringEquiv (R := _ ⧸ RingHom.ker f)
    (f.quotientKerEquivOfSurjective (Z.subschemeι.stalkMap_surjective y))

/-- A closed subscheme having simple normal crossings with the snc divisor of a triple is smooth
over `k`. -/
@[mmp "def_kr3c_smooth_blowup_order_m_triple"]
theorem isSmoothScheme_of_hasSNCWith (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (Z : t.X.IdealSheafData) (hZ : HasSNCWith t.E.E Z) :
    MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ t.sX) :=
  have : CharZero t.k := ht.1
  have : LocallyOfFiniteType t.sX := ht.2.2.1
  isSmoothScheme_subschemeι_of_hasSNCWith t.sX ht.2.1 Z hZ

/-- The blow-up `B_ZX → X` of a closed subscheme `Z` is a *smooth blow-up* of the marked triple
`(X, I, m, E)` (Kollár Def. 3.65 (1′)–(2′)): every irreducible component of `Z` has codimension
`≥ 1`, `Z` has simple normal crossings with `∑_i E^i`, and `ord_Z I ≥ m`. -/
@[mmp "def_kr3c_smooth_blowup_marked_triple"]
def IsSmoothBlowupOfMarkedTriple (t : MarkedTriple.{u}) (Z : t.X.IdealSheafData) : Prop :=
  HasComponentsOfPositiveCodim (Z.support : Set t.X) ∧ HasSNCWith t.E.E Z ∧
    OrderAlongGE t.I (Z.support : Set t.X) t.m

end SmoothBlowup

end MMP.Resolution
