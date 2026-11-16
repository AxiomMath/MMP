module

public import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence

/-!
# Snc-preserving resolution of ordered divisor tuples

Let `(V, (I_1, …, I_m), E)` be an ordered divisor tuple over a field `k` of characteristic
zero. There is a finite sequence of order-one transformations of the tuple whose final tuple is
snc at every point, and whose composite `V_r → V` is an isomorphism over an open neighbourhood
of the snc locus of the original tuple; moreover no centre meets the inverse image of that snc
locus.

## Main results

* `MMP.Resolution.OrderedDivisorTuple.exists_transform_sncLocus_eq_univ`.

## Implementation notes

A sequence of order-one transformations is a `MMP.Resolution.ClosedBlowupSequence` whose
centres are, stage by stage, centres of order-one transformations
(`MMP.Resolution.OrderedDivisorTuple.IsTransformCentre`) of the current tuple
(`MMP.Resolution.OrderedDivisorTuple.transform`); the condition is written by recursion on the
sequence, carrying the composite map `p : V_r → V` to the original variety. The snc locus need
not be open, so "an isomorphism over the snc locus" is stated as an isomorphism over some open
`U ⊇ sncLocus`.

The proof is an induction on the dimension of `V` and then on the number `m` of ideals. It runs
on a stronger notion of admissible sequence than the statement's: every centre misses the snc
locus of the tuple it transforms (`ValidS`), which implies that it misses the inverse image of
the original snc locus. One first makes `I_1` reduced with smooth cosupport (order reduction of
the marked ideal `(I_1, 2)`,
`MMP.Resolution.OrderedDivisorTuple.exists_transform_isSmoothScheme_support`), then makes
`I_1 + E` snc by resolving, component by component, the tuples restricted to the components of
the boundary (Step 1), then removes the components of `I_1` lying in other cosupports (Step 2a)
and makes the tuple snc along `cosupp I_1` by resolving the restricted tuples on its components
(Step 2b), and finally resolves the tuple without `I_1` (Step 3). Each restriction step lifts a
sequence on a smooth divisor `D` to the ambient variety by blowing up the images of the centres;
the strict transform of `D` is then the image of the canonical lift. The sequence bookkeeping is in
`MMP.Resolution.TupleResolutionAux`; the auxiliary lemmas of this file live in the namespace
`DivisorTupleSncResolution`.

## References

* [J. Kollár, *Semi log resolutions*, arXiv:0812.3592, Proposition 6]
-/

@[expose] public section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace DivisorTupleSncResolution

open CategoryTheory AlgebraicGeometry MMP.Resolution
open MMP.Resolution.Internal.TupleRestrictionLift MMP.Resolution.TupleResolutionAux

universe u

/-! ### Step 2a: blowing up a Cartier component -/

/-- The components of `S ∖ W`, for a component `W` of `S` with `W` and `S ∖ W` closed, are the
other components of `S`. -/
private theorem componentsOf_diff_of_mem {X : Type*} [TopologicalSpace X] {S W : Set X}
    (hW : W ∈ componentsOf S) (hWc : IsClosed W) (hSW : IsClosed (S \ W)) :
    componentsOf (S \ W) = componentsOf S \ {W} := by
  have hU : ∀ Y : Set X, IsIrreducible Y → Y ⊆ S → Y ⊆ W ∨ Y ⊆ S \ W := fun Y hY hYS =>
    (isPreirreducible_iff_isClosed_union_isClosed.1 hY.2) _ _ hWc hSW
      (fun y hy => by
        by_cases h : y ∈ W
        exacts [Or.inl h, Or.inr ⟨hYS hy, h⟩])
  ext V
  constructor
  · rintro ⟨⟨hVi, hVS⟩, hVmax⟩
    obtain ⟨v, hv⟩ := hVi.nonempty
    refine ⟨⟨⟨hVi, hVS.trans Set.diff_subset⟩, fun Y hY hVY => ?_⟩, fun h => ?_⟩
    · rcases hU Y hY.1 hY.2 with h | h
      · exact absurd (h (hVY hv)) (hVS hv).2
      · exact hVmax ⟨hY.1, h⟩ hVY
    · rw [Set.mem_singleton_iff] at h
      exact (hVS hv).2 (h ▸ hv)
  · rintro ⟨⟨⟨hVi, hVS⟩, hVmax⟩, hVW⟩
    rcases hU V hVi hVS with h | h
    · exact absurd (Set.mem_singleton_iff.2 (le_antisymm h (hVmax hW.1 h))) hVW
    · exact ⟨⟨hVi, h⟩, fun Y hY hVY => hVmax ⟨hY.1, hY.2.trans Set.diff_subset⟩ hVY⟩

/-- A component of the cosupport of a parameter divisor of a tuple contained in the cosupport of
another member of the tuple misses the snc locus. -/
private theorem disjoint_sncLocus_of_subset_support {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (T : OrderedDivisorTuple X) {p q : Fin T.m ⊕ Fin T.E.s} (hpq : p ≠ q)
    {W : Set X} (hW : W ∈ componentsOf ((T.divisors p).support : Set X))
    (hWq : W ⊆ ((T.divisors q).support : Set X)) : Disjoint W T.sncLocus := by
  rw [Set.disjoint_left]
  intro x hxW hx
  obtain ⟨n, z, c, hz, hc, hzc⟩ := hx
  have hxp : x ∈ (T.divisors p).support := hW.1.2 hxW
  have hxq : x ∈ (T.divisors q).support := hWq hxW
  have hne : c ⟨p, hxp⟩ ≠ c ⟨q, hxq⟩ := fun h => hpq (congrArg Subtype.val (hc h))
  let P : PrimeSpectrum (X.presheaf.stalk x) :=
    ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hz (c ⟨p, hxp⟩)⟩
  have hPW : X.fromSpecStalk x P ∈ W :=
    (fromSpecStalk_mem_component_iff hW hxW hz (hzc ⟨p, hxp⟩) P).2
      (Ideal.mem_span_singleton_self _)
  have hle := (fromSpecStalk_mem_support_iff_stalk_le _ x P).1 (hWq hPW)
  rw [hzc ⟨q, hxq⟩, Ideal.span_singleton_le_iff_mem] at hle
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne hle

/-- A divisor which together with the boundary is snc has snc with the boundary. -/
private theorem hasSNCWith_of_isSNCFamily_elim {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {D : X.IdealSheafData} {E : OrderedDivisor X}
    (hD : IsSNCFamily s fun o : Option (Fin E.s) => o.elim D E.E) : HasSNCWith E.E D := by
  intro x hx
  obtain ⟨n, z, c, hz, hzc, hc⟩ := hD.2 x
  refine ⟨n, z, fun i => c ⟨some i.1, i.2⟩, {c ⟨none, hx⟩}, hz, fun i => hzc ⟨some i.1, i.2⟩,
    fun i i' h => ?_, ?_⟩
  · exact Subtype.ext (Option.some_injective _ (congrArg Subtype.val (hc h)))
  · rw [show IdealSheafData.stalk D x = Ideal.span {z (c ⟨none, hx⟩)} from hzc ⟨none, hx⟩]
    simp

/-- An irreducible closed set whose reduced ideal together with the boundary is snc lies in no
boundary entry. -/
private theorem not_subset_support_of_isSNCFamily_elim {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] {s : X ⟶ Spec (.of k)} {W : Set X} (hWc : IsClosed W)
    (hWi : IsIrreducible W) {E : OrderedDivisor X}
    (hD : IsSNCFamily s fun o : Option (Fin E.s) =>
      o.elim (Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩) E.E) (i : Fin E.s) :
    ¬ W ⊆ ((E.E i).support : Set X) := by
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩
  have hDsupp : (D.support : Set X) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  intro hsub
  obtain ⟨x, hxW⟩ := hWi.nonempty
  have hxD : x ∈ D.support := by rwa [← SetLike.mem_coe, hDsupp]
  have hxE : x ∈ (E.E i).support := hsub hxW
  obtain ⟨n, z, c, hz, hzc, hc⟩ := hD.2 x
  have hDx : IdealSheafData.stalk D x = Ideal.span {z (c ⟨none, hxD⟩)} := hzc ⟨none, hxD⟩
  have hEx : IdealSheafData.stalk (E.E i) x = Ideal.span {z (c ⟨some i, hxE⟩)} :=
    hzc ⟨some i, hxE⟩
  let P : PrimeSpectrum (X.presheaf.stalk x) :=
    ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hz (c ⟨none, hxD⟩)⟩
  have hPW : X.fromSpecStalk x P ∈ W := by
    rw [← hDsupp]; exact (fromSpecStalk_mem_support_iff_stalk_le D x P).2 hDx.le
  have hle := (fromSpecStalk_mem_support_iff_stalk_le (E.E i) x P).1 (hsub hPW)
  rw [hEx, Ideal.span_singleton_le_iff_mem] at hle
  have hne : c ⟨none, hxD⟩ ≠ c ⟨some i, hxE⟩ := fun h =>
    Option.some_ne_none i (congrArg Subtype.val (hc h)).symm
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hz hne hle

/-- A closed set of pure codimension one has no components of codimension `≥ 2`. -/
private theorem componentsOfCodimAtLeastTwo_eq_empty {X : Scheme.{u}}
    {S : TopologicalSpace.Closeds X} (hS : MMP.Mori.IsPureCodimOne S) :
    componentsOfCodimAtLeastTwo (S : Set X) = ∅ := by
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_componentsOfCodimAtLeastTwo]
  rintro ⟨W, hW, h2, -⟩
  rw [codimension_eq_one_of_mem_componentsOf hS hW] at h2
  exact absurd h2 (by decide)

/-- Splitting a component `W` off the first entry `I = D * J` of a family snc at `x`, with `D`
supported on `W` and `J` off it, gives the family `J, E, D`, again snc at `x`. -/
private theorem isSNCAt_cons_snoc_of_eq_mul {X : Scheme.{u}} {n : ℕ} {I D J : X.IdealSheafData}
    {E : Fin n → X.IdealSheafData} {W : Set X} (hsplit : I = D * J)
    (hDsupp : (D.support : Set X) = W) (hJsupp : (J.support : Set X) = (I.support : Set X) \ W)
    (hDst : ∀ x ∈ W, IdealSheafData.stalk D x = IdealSheafData.stalk I x) {x : X}
    (h : IsSNCAt (Fin.cons (α := fun _ => X.IdealSheafData) I E) x) :
    IsSNCAt (Fin.cons (α := fun _ => X.IdealSheafData) J
      (Fin.snoc (α := fun _ => X.IdealSheafData) E D)) x := by
  let G : Fin (n + 1 + 1) → X.IdealSheafData :=
    Fin.cons (α := fun _ => X.IdealSheafData) J (Fin.snoc (α := fun _ => X.IdealSheafData) E D)
  let g : Fin (n + 1 + 1) → Fin (n + 1) :=
    Fin.cons (α := fun _ => Fin (n + 1)) 0 (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.succ 0)
  change IsSNCAt G x
  have hDtop : ∀ x, x ∉ W → IdealSheafData.stalk D x = ⊤ := fun x hx =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support D x).2 (by rwa [← SetLike.mem_coe, hDsupp])
  have hG0 : G 0 = J := rfl
  have hGl : G (Fin.last _).succ = D := by simp [G]
  have hGc : ∀ i : Fin n, G i.castSucc.succ = E i := fun i => by simp [G]
  have hg0 : g 0 = 0 := rfl
  have hgl : g (Fin.last _).succ = 0 := by simp [g]
  have hgc : ∀ i : Fin n, g i.castSucc.succ = i.succ := fun i => by simp [g]
  refine h.of_forall g (fun a ha => ?_) (fun a b ha hb hab => ?_)
  · induction a using Fin.cases with
    | zero =>
      rw [hg0, Fin.cons_zero, hG0, hsplit, IdealSheafData.stalk_mul, hDtop x, Ideal.top_mul]
      intro hxW
      rw [hG0, ← SetLike.mem_coe, hJsupp] at ha
      exact ha.2 hxW
    | succ a =>
      induction a using Fin.lastCases with
      | last =>
        rw [hgl, Fin.cons_zero, hGl]
        rw [hGl, ← SetLike.mem_coe, hDsupp] at ha
        exact hDst x ha
      | cast i => rw [hgc, Fin.cons_succ, hGc]
  · have hJW : ∀ c, G c = J → x ∈ (G c).support → x ∉ W := fun c hc hx hxW => by
      rw [hc, ← SetLike.mem_coe, hJsupp] at hx; exact hx.2 hxW
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ b =>
        induction b using Fin.lastCases with
        | last =>
          rw [hGl, ← SetLike.mem_coe, hDsupp] at hb
          exact absurd hb (hJW 0 hG0 ha)
        | cast i => rw [hg0, hgc] at hab; exact absurd hab.symm (Fin.succ_ne_zero _)
    | succ a =>
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.cases with
        | zero =>
          rw [hGl, ← SetLike.mem_coe, hDsupp] at ha
          exact absurd ha (hJW 0 hG0 hb)
        | succ b =>
          induction b using Fin.lastCases with
          | last => rfl
          | cast i => rw [hgl, hgc] at hab; exact absurd hab.symm (Fin.succ_ne_zero _)
      | cast i =>
        induction b using Fin.cases with
        | zero => rw [hg0, hgc] at hab; exact absurd hab (Fin.succ_ne_zero _)
        | succ b =>
          induction b using Fin.lastCases with
          | last => rw [hgl, hgc] at hab; exact absurd hab (Fin.succ_ne_zero _)
          | cast i' => rw [hgc, hgc] at hab; rw [Fin.succ_injective _ hab]

/-- **One step of Step 2a.** A component `W` of the cosupport of `I_1` lying in the cosupport of
another ideal is blown up; it is a Cartier divisor, so the blow-up is an isomorphism, `W` leaves
the first ideal and joins the boundary, and the number of components of the first cosupport
drops. -/
private theorem exists_valid_componentsOf_ncard_lt {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (h0 : 0 < T.m)
    (hS : IsSNCFamily sV (Fin.cons (α := fun _ => V.IdealSheafData) (T.I ⟨0, h0⟩) T.E.E))
    {j : Fin T.m} (hj : j ≠ ⟨0, h0⟩) {W : Set V}
    (hW : W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V))
    (hWj : W ⊆ ((T.I j).support : Set V)) :
    ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ ∃ h : 0 < (finalTuple B T).m,
      IsSNCFamily (B.toBase ≫ sV) (Fin.cons (α := fun _ => B.target.IdealSheafData)
        ((finalTuple B T).I ⟨0, h⟩) (finalTuple B T).E.E) ∧
      (componentsOf (((finalTuple B T).I ⟨0, h⟩).support : Set B.target)).ncard <
        (componentsOf ((T.I ⟨0, h0⟩).support : Set V)).ncard := by
  classical
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsNoetherian V := {}
  have : CharZero k := hT.1
  set I0 := T.I ⟨0, h0⟩ with hI0
  have hP : IsParamDivisor I0 := isParamDivisor_of_isSNCFamily_cons hS
  obtain ⟨hWc, hJc, hsplit, hDst, hdisj⟩ := exists_split_component hP hW
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩ with hDdef
  set J := Scheme.IdealSheafData.vanishingIdeal ⟨_, hJc⟩ with hJdef
  have hDsupp : (D.support : Set V) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hJsupp : (J.support : Set V) = (I0.support : Set V) \ W :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hDsnc := isSNCFamily_elim_component hS hW hWc
  have hDpar : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → V.presheaf.stalk y) (i : Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w i} := by
    intro y hy
    obtain ⟨n, z, c, hz, hc, -⟩ := hDsnc.2 y
    exact ⟨n, z, c ⟨none, hy⟩, hz, hc ⟨none, hy⟩⟩
  have hDcart : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter D hDpar
  haveI : IsIso (blowUpToBase D) := isIso_blowUpToBase_of_isEffectiveCartierDivisor D hDcart
  have : IsLocallyNoetherian (blowUp D) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase D)
  set π := blowUpToBase D with hπ
  have hc : T.IsTransformCentre sV D := ⟨(hDsnc.1 none).2.2, hasSNCWith_of_isSNCFamily_elim hDsnc⟩
  have hdisjS : Disjoint (D.support : Set V) T.sncLocus := by
    rw [hDsupp]
    exact disjoint_sncLocus_of_subset_support T (p := .inl ⟨0, h0⟩) (q := .inl j)
      (fun h => hj (Sum.inl_injective h).symm) hW hWj
  -- the transformed tuple
  have hIle : I0 ≤ D := by rw [hsplit]; exact mul_le_of_le_one_right' le_top
  have hI0' : (T.transform D).I ⟨0, h0⟩ = J.comap π := by
    refine (OrderedDivisorTuple.transform_I_of_le T D ⟨0, h0⟩
      (by rw [hDsupp]; exact hW.1.2)).trans ?_
    rw [← comap_idealColon_of_isIso π I0 D hDcart hIle]
    congr 1
    rw [hsplit]
    exact idealColon_mul_cancel D J hDcart
  have hcod2 : componentsOfCodimAtLeastTwo (D.support : Set V) = ∅ :=
    componentsOfCodimAtLeastTwo_eq_empty (hDsnc.1 none).2.1
  have hEred : ∀ i, T.E.E i = Scheme.IdealSheafData.vanishingIdeal (T.E.E i).support :=
    fun i => by
      haveI := (hT.2.2.2.2.2.1 i).1
      exact (MMP.Positivity.vanishingIdeal_support_of_isReduced _).symm
  have hEc : ∀ i, (T.transform D).E.E (Fin.castSucc i) = (T.E.E i).comap π := by
    intro i
    change (T.E.totalTransform D).E (Fin.castSucc i) = _
    rw [totalTransform_E_eq, hEred i,
      show (T.E.E i).support = TopologicalSpace.Closeds.closure ((T.E.E i).support : Set V) from
        (TopologicalSpace.Closeds.ext (T.E.E i).support.isClosed.closure_eq).symm,
      comap_vanishingIdeal_closure_of_isIso]
    simp only [totalTransformSet, Fin.snoc_castSucc, hcod2, Set.diff_empty, hπ]
  have hWE : W ∉ componentsOf T.E.support := by
    intro hWE'
    have hsub : W ⊆ T.E.support := hWE'.1.2
    obtain ⟨_, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1
      (Finset.univ.image fun i => ((T.E.E i).support : Set V))
      (fun z hz => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact (T.E.E i).support.isClosed)
      (by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub hx)
        exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2
          ⟨i, Finset.mem_univ _, rfl⟩), hi⟩)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact not_subset_support_of_isSNCFamily_elim hWc hW.1.1 hDsnc i hWz
  have hElast : (T.transform D).E.E (Fin.last _) = D.comap π := by
    change (T.E.totalTransform D).E (Fin.last _) = _
    rw [totalTransform_E_eq]
    have hset : totalTransformSet T.E D (Fin.last _) = π ⁻¹' W := by
      simp only [totalTransformSet, Fin.snoc_last]
      ext y
      simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
      constructor
      · rintro ⟨W', hW', -, hy⟩
        rw [hDsupp] at hW'
        rwa [eq_of_mem_componentsOf_of_isIrreducible hW.1.1 hW'] at hy
      · intro hy
        refine ⟨W, ?_, hWE, hy⟩
        rw [hDsupp]
        exact ⟨⟨hW.1.1, subset_rfl⟩, fun Y hY _ => hY.2⟩
    have hDcl : Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure W) = D := by
      rw [hDdef]
      congr 1
      exact TopologicalSpace.Closeds.ext hWc.closure_eq
    rw [hset, ← comap_vanishingIdeal_closure_of_isIso, hDcl]
  -- the family `J + E + W` on `V`
  let G : Fin (T.E.s + 1 + 1) → V.IdealSheafData :=
    Fin.cons (α := fun _ => V.IdealSheafData) J (Fin.snoc (α := fun _ => V.IdealSheafData) T.E.E D)
  have hfam : (Fin.cons (α := fun _ => (blowUp D).IdealSheafData) ((T.transform D).I ⟨0, h0⟩)
      (T.transform D).E.E : Fin (T.E.s + 1 + 1) → (blowUp D).IdealSheafData) =
      fun a => (G a).comap π := by
    funext a
    refine Fin.cases ?_ (fun i => ?_) a
    · simp only [Fin.cons_zero, G]; exact hI0'
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.cons_succ, G, Fin.snoc_last]; exact hElast
      · simp only [Fin.cons_succ, G, Fin.snoc_castSucc]; exact hEc i
  have hGsnc : ∀ x, IsSNCAt G x := fun x => by
    obtain ⟨n, z, c, hz, hzc, hc'⟩ := hS.2 x
    exact isSNCAt_cons_snoc_of_eq_mul hsplit hDsupp hJsupp hDst ⟨n, z, c, hz, hc', hzc⟩
  have hsncnew : IsSNCFamily (π ≫ sV) (Fin.cons (α := fun _ => (blowUp D).IdealSheafData)
      ((T.transform D).I ⟨0, h0⟩) (T.transform D).E.E) := by
    have h := isSNCFamily_of_forall_isSNCAt (s := π ≫ sV) fun y => (hGsnc (π y)).comap_of_isIso π
    rwa [← hfam] at h
  -- the components of the new first cosupport
  have hsupp' : (((T.transform D).I ⟨0, h0⟩).support : Set (blowUp D)) =
      π ⁻¹' ((I0.support : Set V) \ W) := by
    rw [hI0', Scheme.IdealSheafData.support_comap, ← hJsupp]
    rfl
  have hfin : (componentsOf (I0.support : Set V)).Finite :=
    (Aux.finite_and_cover_componentsOf (T := V) I0.support.isClosed).1
  have hlt : (componentsOf (((T.transform D).I ⟨0, h0⟩).support : Set (blowUp D))).ncard <
      (componentsOf (I0.support : Set V)).ncard := by
    have hsurj : Function.Surjective π := π.homeomorph.surjective
    rw [hsupp', componentsOf_preimage_of_isIso π,
      Set.ncard_image_of_injective (f := fun x => (π : blowUp D → V) ⁻¹' x) _
        (Set.preimage_injective.2 hsurj),
      componentsOf_diff_of_mem hW hWc (hJsupp ▸ J.support.isClosed)]
    exact Set.ncard_diff_singleton_lt_of_mem hW hfin
  refine ⟨.cons D (.nil _), ⟨hc, hdisjS, trivial⟩, h0, ?_, hlt⟩
  change IsSNCFamily ((𝟙 _ ≫ π) ≫ sV) _
  rw [Category.id_comp]
  exact hsncnew

/-- A tuple is resolvable once the tuple reached along a valid sequence is, given that the
latter is again an ordered divisor tuple on a target of no larger dimension. -/
private theorem resolvable_of_validS {k : Type u} [Field k] {V : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (hT : IsOrderedDivisorTuple sV T)
    (B : ClosedBlowupSequence V) (hB : ValidS sV B T)
    (h : IsOrderedDivisorTuple (B.toBase ≫ sV) (finalTuple B T) →
      topologicalKrullDim B.target ≤ topologicalKrullDim V →
      Resolvable (B.toBase ≫ sV) (finalTuple B T)) : Resolvable sV T := by
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have hN : T.sncLocus.Nonempty := ⟨_, genericPoint_mem_sncLocus hT⟩
  have hBw : Valid sV T.sncLocus B T := ValidS.valid B hB subset_rfl
  exact resolvable_of_valid B hB (h (isOrderedDivisorTuple_finalTuple B hT hBw hN).1
    (topologicalKrullDim_target_le B hT hN hBw))

/-- **Step 2a**: the components of the cosupport of `I_1` lying in another cosupport are blown up
one at a time; it suffices to resolve the tuples so reached. -/
private theorem resolvable_of_isSNCFamily_cons_of_componentsOf {k : Type u} [Field k] (n : ℕ)
    (m₀ : ℕ)
    (hcont : ∀ {V' : Scheme.{u}} (sV' : V' ⟶ Spec (.of k)) (T' : OrderedDivisorTuple V'),
      IsOrderedDivisorTuple sV' T' → topologicalKrullDim V' ≤ n → T'.m = m₀ →
      ∀ h : 0 < T'.m,
      IsSNCFamily sV' (Fin.cons (α := fun _ => V'.IdealSheafData) (T'.I ⟨0, h⟩) T'.E.E) →
      (∀ j : Fin T'.m, j ≠ ⟨0, h⟩ → ∀ W ∈ componentsOf ((T'.I ⟨0, h⟩).support : Set V'),
        ¬ W ⊆ ((T'.I j).support : Set V')) → Resolvable sV' T') :
    ∀ (N : ℕ) {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V),
      IsOrderedDivisorTuple sV T → topologicalKrullDim V ≤ n → T.m = m₀ → ∀ h0 : 0 < T.m,
      IsSNCFamily sV (Fin.cons (α := fun _ => V.IdealSheafData) (T.I ⟨0, h0⟩) T.E.E) →
      (componentsOf ((T.I ⟨0, h0⟩).support : Set V)).ncard = N → Resolvable sV T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro V sV T hT hdim hm h0 hS hNc
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  by_cases hbad : ∃ j : Fin T.m, j ≠ ⟨0, h0⟩ ∧
      ∃ W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V), W ⊆ ((T.I j).support : Set V)
  · obtain ⟨j, hj, W, hW, hWj⟩ := hbad
    obtain ⟨B, hB, h', hS', hlt⟩ := exists_valid_componentsOf_ncard_lt sV T hT h0 hS hj hW hWj
    exact resolvable_of_validS hT B hB fun hT' hd =>
      ihN _ (hNc ▸ hlt) (B.toBase ≫ sV) _ hT' (hd.trans hdim) (by rw [finalTuple_m, hm])
        h' hS' rfl
  · simp only [not_exists, not_and] at hbad
    exact hcont sV T hT hdim hm h0 hS fun j hj W hW => hbad j hj W hW

/-- Snc of a tuple at a point, the first ideal having there the stalk of `K`, gives snc of `K`
together with the tuple without its first ideal. -/
private theorem isSNCAt_elim_dropFirst_of_mem_sncLocus {X : Scheme.{u}} (T : OrderedDivisorTuple X)
    (h0 : 0 < T.m) {K : X.IdealSheafData} {x : X} (hx : x ∈ T.sncLocus)
    (hK : IdealSheafData.stalk K x = IdealSheafData.stalk (T.I ⟨0, h0⟩) x) :
    IsSNCAt (fun o : Option (Fin (dropFirst T).m ⊕ Fin (dropFirst T).E.s) =>
      o.elim K (dropFirst T).divisors) x := by
  refine IsSNCAt.of_forall hx (fun o => o.elim (Sum.inl ⟨0, h0⟩) (dropFirstIndex T)) ?_ ?_
  · rintro (_ | q) _
    · exact hK
    · exact congrArg (fun J => IdealSheafData.stalk J x) (divisors_dropFirst T q)
  · rintro (_ | q) (_ | q') _ _ h
    · rfl
    · exact absurd h.symm (dropFirstIndex_ne_zero T h0 q')
    · exact absurd h (dropFirstIndex_ne_zero T h0 q)
    · exact congrArg some (dropFirstIndex_injective T h)

/-- The stage predicate of Step 2b: the lifted tuple is the tuple without its first ideal, the
first ideal is the ideal of the strict transform times the pullback of `J`, and the strict
transform lies over `W`. -/
private abbrev DropFirstPred (k : Type u) [Field k] {V : Scheme.{u}} (W : Set V)
    (J : V.IdealSheafData) : LiftPred k V :=
  fun ι _ p T₁ _ Tx => T₁ = dropFirst Tx ∧ ∃ h : 0 < Tx.m,
    Tx.I ⟨0, h⟩ = ι.ker * J.comap p ∧ Set.range (ι ≫ p) ⊆ W

private theorem liftStep_dropFirstPred {k : Type u} [Field k] {V : Scheme.{u}} (W : Set V)
    (J : V.IdealSheafData) (hWJ : ∀ x ∈ W, x ∉ (J.support : Set V)) :
    LiftStep (DropFirstPred k W J) := by
  intro S' W' ι s p T₁ ES Tx Z hinv hES hTS hQ0 hZ hdisj hc h
  obtain ⟨rfl, h0, hI0, hpW⟩ := hQ0
  have : IsClosedImmersion ι := hinv.1
  have hvar : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ s)
  have hsupp : ((Z.map ι).support : Set W') = ι '' Z.support := by
    rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure,
      (ι.isClosedEmbedding.isClosedMap _ Z.support.isClosed).closure_eq]
  set φ := eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι (Z.map ι) with hφ
  have hφπ : φ ≫ blowUpToBase (Z.map ι) = blowUpToBase Z ≫ ι :=
    canonicalLift_comp_blowUpToBase_map ι h
  have hJι : ∀ z, ι z ∉ (J.comap p).support := fun z hz => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap] at hz
    have hz' := hpW ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply] at hz'
    exact hWJ _ hz' hz
  refine ⟨hc, ?_, rfl, h0, ?_, ?_⟩
  · rw [Set.disjoint_left, hsupp]
    rintro _ ⟨z, hz, rfl⟩ hx
    have hst : IdealSheafData.stalk ι.ker (ι z) = IdealSheafData.stalk (Tx.I ⟨0, h0⟩) (ι z) := by
      rw [hI0, IdealSheafData.stalk_mul,
        (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 (hJι z), Ideal.mul_top]
    have h1 := isSNCAt_elim_dropFirst_of_mem_sncLocus Tx h0 hx hst
    have h2 := isSNCAt_comap_of_isSNCAt_elim ι (dropFirst Tx).divisors z h1
    obtain ⟨n, w, c, hw, hwc, hc'⟩ := hTS.2.2.2.2.2.2 z
    have h3 := isSNCAt_sumElim_of_iUnion_support_eq (fun j => ((dropFirst Tx).I j).comap ι)
      (fun j => ((dropFirst Tx).I j).comap ι) (Equiv.refl _) (fun _ => rfl) ES.E
      ((dropFirst Tx).E.comap ι).E z hES ⟨n, w, c, hw, hc', hwc⟩
      (IsSNCAt.of_forall h2 id (fun q _ => by rcases q with j | i <;> rfl)
        fun _ _ _ _ h => h)
    have h4 : z ∈ (⟨(dropFirst Tx).m, fun j => ((dropFirst Tx).I j).comap ι, ES⟩ :
        OrderedDivisorTuple S').sncLocus :=
      IsSNCAt.of_forall h3 id (fun q _ => by rcases q with j | i <;> rfl) fun _ _ _ _ h => h
    exact hdisj.notMem_of_mem_left hz h4
  · have hsub : ((Z.map ι).support : Set W') ⊆ (Tx.I ⟨0, h0⟩).support := by
      rw [hI0]
      exact (Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp Z.subschemeι ι)).trans
        (Scheme.IdealSheafData.support_antitone (mul_le_of_le_one_right' le_top))
    refine (OrderedDivisorTuple.transform_I_of_le Tx (Z.map ι) ⟨0, h0⟩ hsub).trans ?_
    rw [hI0, AlgebraicGeometry.comap_mul, comap_ker_eq_mul_ker_canonicalLift hinv hc h, mul_assoc,
      idealColon_mul_cancel _ _ (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _),
      Scheme.IdealSheafData.comap_comp]
  · rintro _ ⟨z', rfl⟩
    rw [← Category.assoc, hφπ, Category.assoc, Scheme.Hom.comp_apply]
    exact hpW ⟨_, rfl⟩

/-! ### Step 2b: one component at a time -/

/-- The components of the cosupport of the first ideal along which the tuple is not snc. -/
private def badComps {V : Scheme.{u}} (T : OrderedDivisorTuple V) (h0 : 0 < T.m) :
    Set (Set V) :=
  {W | W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V) ∧ ¬ W ⊆ T.sncLocus}

/-- **One step of Step 2b**: resolving along one bad component of the first cosupport. -/
private theorem exists_valid_badComps_ncard_lt {k : Type u} [Field k] (n : ℕ)
    (IH : ∀ n' < n, ResolvableUpTo k n') {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (hdim : topologicalKrullDim V ≤ n) (h0 : 0 < T.m)
    (hS : IsSNCFamily sV (Fin.cons (α := fun _ => V.IdealSheafData) (T.I ⟨0, h0⟩) T.E.E))
    (hI : ∀ j : Fin T.m, j ≠ ⟨0, h0⟩ → ∀ W ∈ badComps T h0, ¬ W ⊆ ((T.I j).support : Set V))
    {W : Set V} (hW : W ∈ badComps T h0) :
    ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ ∃ h : 0 < (finalTuple B T).m,
      IsSNCFamily (B.toBase ≫ sV) (Fin.cons (α := fun _ => B.target.IdealSheafData)
        ((finalTuple B T).I ⟨0, h⟩) (finalTuple B T).E.E) ∧
      (∀ j : Fin (finalTuple B T).m, j ≠ ⟨0, h⟩ → ∀ W' ∈ badComps (finalTuple B T) h,
        ¬ W' ⊆ (((finalTuple B T).I j).support : Set B.target)) ∧
      (badComps (finalTuple B T) h).ncard < (badComps T h0).ncard := by
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsIntegral V := hvar.toIsIntegral
  have : CharZero k := hT.1
  set I0 := T.I ⟨0, h0⟩ with hI0
  have hP : IsParamDivisor I0 := isParamDivisor_of_isSNCFamily_cons hS
  obtain ⟨hWc, hJc, hsplit, hDst, hdisj⟩ := exists_split_component hP hW.1
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩ with hDdef
  set J := Scheme.IdealSheafData.vanishingIdeal ⟨_, hJc⟩ with hJdef
  have hDsupp : (D.support : Set V) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hrangeD : Set.range D.subschemeι = W := by
    rw [Scheme.IdealSheafData.range_subschemeι, hDsupp]
  set T₁ := dropFirst T
  have hT₁ : IsOrderedDivisorTuple sV T₁ :=
    ⟨hT.1, hT.2.1, hT.2.2.1, fun j => hT.2.2.2.1 _, hT.2.2.2.2⟩
  have hDsnc : IsSNCFamily sV fun o : Option (Fin T₁.E.s) => o.elim D T₁.E.E :=
    isSNCFamily_elim_component hS hW.1 hWc
  have hWi : IsIrreducible W := hW.1.1.1
  have hI₁ : ∀ j, ¬ W ⊆ ((T₁.I j).support : Set V) := fun j =>
    hI _ (fun h => by have := congrArg Fin.val h; simp at this) W hW
  have hTD := isOrderedDivisorTuple_restrictTuple hT₁ hWc hWi hDsnc hI₁
  have hWne : W ≠ Set.univ := by
    intro h
    have hη : genericPoint V ∈ W := h ▸ Set.mem_univ _
    exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor _ (hT.2.2.2.1 _).2
      (Stacks.Chow.genericPoint_mem_genericPoints V) (hW.1.1.2 hη)
  obtain ⟨n', hn', hdn'⟩ := exists_lt_topologicalKrullDim_subscheme_le sV hWc hWi hWne hdim
  have hres := IH n' hn' _ _ hTD hdn'
  have hWJ : ∀ x ∈ W, x ∉ (J.support : Set V) := fun x hx hxJ => by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hxJ
    exact hdisj.notMem_of_mem_left hx hxJ
  have hQ0 : DropFirstPred k W J D.subschemeι sV (𝟙 V) T₁ (T₁.E.comap D.subschemeι) T :=
    ⟨rfl, h0, by rwa [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.comap_id],
      by rw [Category.comp_id, hrangeD]⟩
  obtain ⟨B', S', ι', hirr, hnotin, hVS, hV, hinv', hpt, hrange, -, ES, hQf⟩ :=
    exists_validS_restriction_step sV T₁ hT₁ D hDsnc hTD hres _ (liftStep_dropFirstPred W J hWJ)
      T hQ0
  have hVT : Valid sV T.sncLocus B' T := ValidS.valid B' hVS subset_rfl
  have h0' : 0 < (finalTuple B' T).m := by rw [finalTuple_m]; exact h0
  have hI0' : (finalTuple B' T).I ⟨0, h0'⟩ = ι'.ker * J.comap B'.toBase := by
    obtain ⟨-, h, hI, -⟩ := hQf
    rwa [Category.comp_id] at hI
  have hT' := (isOrderedDivisorTuple_finalTuple B' hT hVT ⟨_, genericPoint_mem_sncLocus hT⟩).1
  have hvar' : AlgebraicGeometry.IsVariety k (B'.toBase ≫ sV) := hT'.2.1
  have : IsLocallyNoetherian B'.target := LocallyOfFiniteType.isLocallyNoetherian (B'.toBase ≫ sV)
  have : IsClosedImmersion ι' := hinv'.1
  have hJsupp : (J.support : Set V) = (I0.support : Set V) \ W :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hJy : ∀ y, B'.toBase y ∈ W → y ∉ (J.comap B'.toBase).support := fun y hy h => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap] at h
    have h' : B'.toBase y ∈ (J.support : Set V) := h
    rw [hJsupp] at h'
    exact hdisj.notMem_of_mem_left hy h'
  have hst0 : ∀ y, B'.toBase y ∈ W → IdealSheafData.stalk ((finalTuple B' T).I ⟨0, h0'⟩) y =
      IdealSheafData.stalk ι'.ker y := by
    intro y hy
    rw [hI0', IdealSheafData.stalk_mul,
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2 (hJy y hy), Ideal.mul_top]
  have hker : (ι'.ker.support : Set B'.target) = Set.range ι' := by
    rw [Scheme.Hom.support_ker, ι'.isClosedEmbedding.isClosed_range.closure_eq]
  have hptw : ∀ y, IsSNCAt (Fin.cons (α := fun _ => B'.target.IdealSheafData)
      ((finalTuple B' T).I ⟨0, h0'⟩) (finalTuple B' T).E.E) y := by
    intro y
    by_cases hyW : B'.toBase y ∈ W
    · by_cases hyr : y ∈ Set.range ι'
      · obtain ⟨z, rfl⟩ := hyr
        have h := hpt z
        rw [finalTuple_dropFirst] at h
        exact isSNCAt_cons_of_isSNCAt_elim h (hst0 _ hyW)
      · have hy0 : y ∉ ((finalTuple B' T).I ⟨0, h0'⟩).support := by
          rw [← (IdealSheafData.stalk_eq_top_iff_notMem_support _ _), hst0 y hyW,
            IdealSheafData.stalk_eq_top_iff_notMem_support, ← SetLike.mem_coe, hker]
          exact hyr
        obtain ⟨m, z, c, hz, hzc, hc⟩ := hT'.2.2.2.2.2.2 y
        exact isSNCAt_cons_of_notMem hy0 ⟨m, z, c, hz, hc, hzc⟩ _ rfl id Function.injective_id
          fun i => by simp
    · -- off the component: the tuple `(I_1; E)` is unchanged there
      set T₁₀ : OrderedDivisorTuple V := ⟨1, fun _ => I0, T.E⟩
      have hV₁₀ : Valid sV (Wᶜ) B' T₁₀ := by
        refine (valid_congr_E B' sV _ T₁ T₁₀ rfl).1 (hV.mono B' fun x hx => ?_)
        rwa [hrangeD]
      have hsnc₁₀ : (Wᶜ : Set V) ⊆ T₁₀.sncLocus := by
        intro x _
        obtain ⟨m, z, c, hz, hzc, hc⟩ := hS.2 x
        let g : Fin 1 ⊕ Fin T.E.s → Fin (T.E.s + 1) := Sum.elim (fun _ => 0) Fin.succ
        refine IsSNCAt.of_injective (D := Fin.cons (α := fun _ => V.IdealSheafData) I0 T.E.E)
          ⟨m, z, c, hz, hc, hzc⟩ (fun p => ⟨g p.1, by
            rcases p with ⟨j | i, hp⟩
            · simpa [g] using hp
            · simpa [g] using hp⟩) ?_ ?_
        · rintro ⟨j | i, hp⟩ ⟨j' | i', hp'⟩ h <;>
            simp only [Subtype.mk.injEq, g, Sum.elim_inl, Sum.elim_inr] at h
          · exact Subtype.ext (congrArg Sum.inl (Subsingleton.elim _ _))
          · exact absurd h (Fin.succ_ne_zero _).symm
          · exact absurd h (Fin.succ_ne_zero _)
          · exact Subtype.ext (congrArg Sum.inr (Fin.succ_injective _ h))
        · rintro ⟨j | i, hp⟩ <;> simp [g, T₁₀, OrderedDivisorTuple.divisors]
      have hy := preimage_subset_sncLocus_of_valid B' hV₁₀ hsnc₁₀ hyW
      have hI₁₀ : (finalTuple B' T₁₀).I ⟨0, by rw [finalTuple_m]; exact Nat.one_pos⟩ =
          (finalTuple B' T).I ⟨0, h0'⟩ := by
        rw [finalTuple_I B' T₁₀ ⟨0, Nat.one_pos⟩, finalTuple_I B' T ⟨0, h0⟩]
      have hE₁₀ := finalTuple_E_congr B' T₁₀ T rfl
      exact isSNCAt_cons_of_mem_sncLocus _ _ hy hI₁₀.symm hE₁₀
  -- the components of the new first cosupport
  have : IsNoetherian V := {}
  let Wc : V.Opens := ⟨Wᶜ, hWc.isOpen_compl⟩
  obtain ⟨U, hU, hUiso⟩ := exists_isIso_of_valid B' sV _ T₁ hV
  haveI : IsIso (B'.toBase ∣_ Wc) :=
    isIso_restrict_of_le B'.toBase (V := U) fun x hx => hU (by rwa [hrangeD])
  have hrange' : ∀ z, B'.toBase (ι' z) ∈ W := fun z => by
    have := hrange ⟨z, rfl⟩
    rwa [hrangeD, Scheme.Hom.comp_apply] at this
  have hsnc_range : ∀ z, ι' z ∈ (finalTuple B' T).sncLocus := by
    intro z
    have h := hpt z
    rw [finalTuple_dropFirst] at h
    exact mem_sncLocus_of_isSNCAt_elim_dropFirst _ h0' h (hst0 _ (hrange' z))
  have hQ : ∀ y, B'.toBase y ∉ W → B'.toBase y ∈ T.sncLocus →
      y ∈ (finalTuple B' T).sncLocus := fun y h1 h2 =>
    preimage_subset_sncLocus_of_valid B' (hVT.mono B' Set.inter_subset_right)
      Set.inter_subset_right (show B'.toBase y ∈ Wᶜ ∩ T.sncLocus from ⟨h1, h2⟩)
  have hsupp' : (((finalTuple B' T).I ⟨0, h0'⟩).support : Set B'.target) =
      Set.range ι' ∪ B'.toBase ⁻¹' (J.support : Set V) := by
    rw [hI0']
    change (ι'.ker.support : Set B'.target) ∪ ((J.comap B'.toBase).support : Set B'.target) = _
    rw [hker, Scheme.IdealSheafData.support_comap]
    rfl
  have hI0supp : (I0.support : Set V) = W ∪ J.support := by
    rw [hJsupp]; exact (Set.union_diff_cancel hW.1.1.2).symm
  have hdisj' : Disjoint W (J.support : Set V) := by rw [hJsupp]; exact hdisj
  have key : ∀ W'' ∈ badComps (finalTuple B' T) h0', B'.toBase '' W'' ∈ badComps T h0 ∧
      B'.toBase '' W'' ≠ W ∧ B'.toBase ⁻¹' (B'.toBase '' W'') = W'' := by
    rintro W'' ⟨hc, hb⟩
    rw [hsupp'] at hc
    obtain ⟨h1, h2, h3, h4⟩ := image_mem_componentsOf_of_isIrreducible_preimage (⇑B'.toBase)
      B'.toBase.continuous hWc J.support.isClosed hdisj'
      (fun x hx => mem_range_of_isIso_restrict B'.toBase Wc (x := x) hx)
      (fun Y' hY' h => isIrreducible_preimage_of_isIso_restrict B'.toBase Wc h hY')
      ι'.isClosedEmbedding.isClosed_range (fun _ ⟨z, hz⟩ => hz ▸ hsnc_range z) hQ hc hb
    exact ⟨⟨by rw [hI0supp]; exact h1, h2⟩, h3, h4⟩
  have hfin : (badComps T h0).Finite :=
    (Aux.finite_and_cover_componentsOf (T := V) I0.support.isClosed).1.subset fun W h => h.1
  refine ⟨B', hVS, h0', isSNCFamily_of_forall_isSNCAt hptw, ?_, ?_⟩
  · intro j hj W'' hW'' hsub
    have hj' : (j : ℕ) < T.m := lt_of_lt_of_eq j.2 (finalTuple_m B' T)
    have hj0 : (⟨j, hj'⟩ : Fin T.m) ≠ ⟨0, h0⟩ := fun h =>
      hj (Fin.ext (show (j : ℕ) = 0 from congrArg Fin.val h))
    refine hI ⟨j, hj'⟩ hj0 _ (key W'' hW'').1 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact support_finalTuple_subset B' T ⟨j, hj'⟩ (hsub hy)
  · calc (badComps (finalTuple B' T) h0').ncard ≤ (badComps T h0 \ {W}).ncard :=
          Set.ncard_le_ncard_of_injOn (fun W'' => B'.toBase '' W'')
            (fun W'' h => ⟨(key W'' h).1, (key W'' h).2.1⟩)
            (fun W₁ h₁ W₂ h₂ he => by
              have he' : B'.toBase '' W₁ = B'.toBase '' W₂ := he
              calc W₁ = B'.toBase ⁻¹' (B'.toBase '' W₁) := (key W₁ h₁).2.2.symm
                _ = B'.toBase ⁻¹' (B'.toBase '' W₂) := by rw [he']
                _ = W₂ := (key W₂ h₂).2.2)
            (hfin.subset Set.diff_subset)
      _ < _ := Set.ncard_diff_singleton_lt_of_mem hW hfin

/-- **Step 2b**: resolving along the bad components of the cosupport of `I_1` one at a time, the
tuple becomes snc at every point of that cosupport; it suffices to resolve the tuples so
reached. -/
private theorem resolvable_of_isSNCFamily_cons {k : Type u} [Field k] (n : ℕ)
    (IH : ∀ n' < n, ResolvableUpTo k n') (m₀ : ℕ)
    (hcont : ∀ {V' : Scheme.{u}} (sV' : V' ⟶ Spec (.of k)) (T' : OrderedDivisorTuple V'),
      IsOrderedDivisorTuple sV' T' → topologicalKrullDim V' ≤ n → T'.m = m₀ →
      ∀ h : 0 < T'.m, ((T'.I ⟨0, h⟩).support : Set V') ⊆ T'.sncLocus → Resolvable sV' T') :
    ∀ (N : ℕ) {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V),
      IsOrderedDivisorTuple sV T → topologicalKrullDim V ≤ n → T.m = m₀ → ∀ h0 : 0 < T.m,
      IsSNCFamily sV (Fin.cons (α := fun _ => V.IdealSheafData) (T.I ⟨0, h0⟩) T.E.E) →
      (∀ j : Fin T.m, j ≠ ⟨0, h0⟩ → ∀ W ∈ badComps T h0, ¬ W ⊆ ((T.I j).support : Set V)) →
      (badComps T h0).ncard = N → Resolvable sV T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro V sV T hT hdim hm h0 hS hI hNc
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsNoetherian V := {}
  by_cases hemp : badComps T h0 = ∅
  · refine hcont sV T hT hdim hm h0 fun x hx => ?_
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1
      ((Aux.finite_and_cover_componentsOf (T := V) (T.I ⟨0, h0⟩).support.isClosed).2 hx)
    by_contra hxs
    have hW' : W ∈ badComps T h0 := ⟨hW, fun h => hxs (h hxW)⟩
    rw [hemp] at hW'
    exact hW'
  · obtain ⟨W, hW⟩ := Set.nonempty_iff_ne_empty.2 hemp
    obtain ⟨B, hB, h', hS', hI', hlt⟩ :=
      exists_valid_badComps_ncard_lt n IH sV T hT hdim h0 hS hI hW
    exact resolvable_of_validS hT B hB fun hT' hd =>
      ihN _ (hNc ▸ hlt) (B.toBase ≫ sV) _ hT' (hd.trans hdim) (by rw [finalTuple_m, hm])
        h' hS' hI' rfl

/-- The snc locus of a tuple lies in that of the tuple without its first ideal. -/
private theorem sncLocus_subset_sncLocus_dropFirst {V : Scheme.{u}} (T : OrderedDivisorTuple V) :
    T.sncLocus ⊆ (dropFirst T).sncLocus := by
  intro x hx
  refine IsSNCAt.of_injective hx (fun p => ⟨dropFirstIndex T p.1, by
    have := p.2; rwa [divisors_dropFirst] at this⟩) ?_
    fun p => congrArg (fun I => IdealSheafData.stalk I x) (divisors_dropFirst T p.1)
  intro p p' h
  exact Subtype.ext (dropFirstIndex_injective T (congrArg Subtype.val h))

/-- A sequence whose centres miss the snc loci of the tuples without their first ideals misses
the snc loci of the tuples. -/
private theorem validS_of_validS_dropFirst {k : Type u} [Field k] : ∀ {S : Scheme.{u}}
    (B : ClosedBlowupSequence S) (s : S ⟶ Spec (.of k)) (T : OrderedDivisorTuple S),
    ValidS s B (dropFirst T) → ValidS s B T := by
  intro S B
  induction B with
  | nil S => intros; trivial
  | cons Z B ih =>
    intro s T h
    exact ⟨h.1, h.2.1.mono_right (sncLocus_subset_sncLocus_dropFirst T),
      ih _ (T.transform Z) h.2.2⟩

/-- **Step 3**: with the tuple snc along the cosupport of `I_1`, resolving the tuple without `I_1`
resolves the tuple. -/
private theorem resolvable_of_resolvable_dropFirst {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (h0 : 0 < T.m) (hS : ((T.I ⟨0, h0⟩).support : Set V) ⊆ T.sncLocus)
    (h : Resolvable sV (dropFirst T)) : Resolvable sV T := by
  have : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  obtain ⟨B, hB, hsnc⟩ := h
  have hBS : ValidS sV B T := validS_of_validS_dropFirst B sV T hB
  have hB' : Valid sV T.sncLocus B T := ValidS.valid B hBS subset_rfl
  refine ⟨B, hBS, Set.eq_univ_of_forall fun y => ?_⟩
  rw [finalTuple_dropFirst] at hsnc
  by_cases hy : y ∈ ((finalTuple B T).I ⟨0, by rw [finalTuple_m]; exact h0⟩).support
  · have h1 := support_finalTuple_subset B T ⟨0, h0⟩ hy
    exact preimage_subset_sncLocus_of_valid B (hB'.mono B hS) hS h1
  · have h2 : y ∈ (dropFirst (finalTuple B T)).sncLocus := hsnc ▸ Set.mem_univ y
    set T' := finalTuple B T
    have hm : T'.m = T.m := finalTuple_m B T
    let g := dropFirstIndex T'
    have key : ∀ p : {p // y ∈ (T'.divisors p).support},
        ∃ q : {q // y ∈ ((dropFirst T').divisors q).support}, p.1 = g q.1 ∧
          IdealSheafData.stalk (T'.divisors p.1) y =
            IdealSheafData.stalk ((dropFirst T').divisors q.1) y := by
      rintro ⟨j | i, hp⟩
      · have hj0 : (j : ℕ) ≠ 0 := by
          rintro hj
          obtain rfl : j = ⟨0, by rw [hm]; exact h0⟩ := Fin.ext hj
          exact hy hp
        have hlt : (j : ℕ) - 1 < (dropFirst T').m := by
          have := j.isLt; simp only [dropFirst]; omega
        have hj : j = ⟨((⟨(j : ℕ) - 1, hlt⟩ : Fin (dropFirst T').m) : ℕ) + 1, by
            show (j : ℕ) - 1 + 1 < T'.m; have := j.isLt; omega⟩ :=
          Fin.ext (by show (j : ℕ) = ((j : ℕ) - 1) + 1; omega)
        refine ⟨⟨.inl ⟨(j : ℕ) - 1, hlt⟩, ?_⟩, congrArg Sum.inl hj, ?_⟩
        · change y ∈ (T'.I _).support
          rw [← hj]; exact hp
        · change IdealSheafData.stalk (T'.I j) y = IdealSheafData.stalk (T'.I _) y
          rw [← hj]
      · exact ⟨⟨.inr i, hp⟩, rfl, rfl⟩
    choose f hf using key
    refine IsSNCAt.of_injective h2 f ?_ fun p => (hf p).2
    intro p p' hpp'
    exact Subtype.ext ((hf p).1.trans ((congrArg (fun q => g q.1) hpp').trans (hf p').1.symm))

/-! ### Step 1: the first divisor transverse to the boundary -/

/-- Snc loci only shrink when ideals are added. -/
private theorem sncLocus_subset_of_comp {X : Scheme.{u}} (T : OrderedDivisorTuple X) {m' : ℕ}
    (I' : Fin m' → X.IdealSheafData) (e : Fin m' → Fin T.m) (he : Function.Injective e)
    (hI : ∀ j, I' j = T.I (e j)) :
    T.sncLocus ⊆ (⟨m', I', T.E⟩ : OrderedDivisorTuple X).sncLocus := by
  intro x hx
  refine IsSNCAt.of_forall hx (Sum.map e id) (fun q _ => ?_) fun q q' _ _ h =>
    Sum.map_injective.2 ⟨he, Function.injective_id⟩ h
  rcases q with j | i
  · exact congrArg (fun J => IdealSheafData.stalk J x) (hI j)
  · rfl

/-- A sequence whose centres miss the snc loci of a tuple with fewer ideals misses those of the
tuple. -/
private theorem validS_of_validS_comp {k : Type u} [Field k] : ∀ {S : Scheme.{u}}
    (B : ClosedBlowupSequence S) (s : S ⟶ Spec (.of k)) (T : OrderedDivisorTuple S) {m' : ℕ}
    (I' : Fin m' → S.IdealSheafData) (e : Fin m' → Fin T.m), Function.Injective e →
    (∀ j, I' j = T.I (e j)) → ValidS s B ⟨m', I', T.E⟩ → ValidS s B T := by
  intro S B
  induction B with
  | nil S => intros; trivial
  | cons Z B ih =>
    intro s T m' I' e he hI h
    refine ⟨h.1, h.2.1.mono_right (sncLocus_subset_of_comp T I' e he hI),
      ih _ (T.transform Z) ((⟨m', I', T.E⟩ : OrderedDivisorTuple _).transform Z).I e he
        (fun j => (transform_I_eq_transformIdeal (⟨m', I', T.E⟩ : OrderedDivisorTuple _) Z j).trans
          ((congrArg (transformIdeal Z) (hI j)).trans
            (transform_I_eq_transformIdeal T Z (e j)).symm)) h.2.2⟩

/-- **A component of the first cosupport lying in the boundary** is blown up: it is a Cartier
divisor having snc with the boundary, the blow-up is an isomorphism, and the component leaves
the first ideal. -/
private theorem exists_validS_cartier_boundary {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (h0 : 0 < T.m) (hS : FirstIdealData sV T h0) {W : Set V}
    (hW : W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V)) {i : Fin T.E.s}
    (hWi : W ⊆ ((T.E.E i).support : Set V)) :
    ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ ∃ h : 0 < (finalTuple B T).m,
      FirstIdealData (B.toBase ≫ sV) (finalTuple B T) h ∧
      (componentsOf (((finalTuple B T).I ⟨0, h⟩).support : Set B.target)).ncard <
        (componentsOf ((T.I ⟨0, h0⟩).support : Set V)).ncard := by
  classical
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsNoetherian V := {}
  have : CharZero k := hT.1
  set I0 := T.I ⟨0, h0⟩ with hI0
  have hP : IsParamDivisor I0 := hS.param
  obtain ⟨hWc, hJc, hsplit, hDst, hdisj⟩ := exists_split_component hP hW
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩ with hDdef
  set J := Scheme.IdealSheafData.vanishingIdeal ⟨_, hJc⟩ with hJdef
  have hDsupp : (D.support : Set V) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hJsupp : (J.support : Set V) = (I0.support : Set V) \ W :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hDpar : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → V.presheaf.stalk y) (i : Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w i} := by
    intro y hy
    have hyW : y ∈ W := by rwa [← SetLike.mem_coe, hDsupp] at hy
    obtain ⟨n, z, j, hz, hzj⟩ := hP y (hW.1.2 hyW)
    exact ⟨n, z, j, hz, (hDst y hyW).trans hzj⟩
  have hDcart : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter D hDpar
  haveI : IsIso (blowUpToBase D) := isIso_blowUpToBase_of_isEffectiveCartierDivisor D hDcart
  have : IsLocallyNoetherian (blowUp D) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase D)
  set π := blowUpToBase D with hπ
  have hDsm : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sV) :=
    isSmoothScheme_subscheme_of_stalk_eq_span_parameter sV D hDpar
  have hHas : HasSNCWith T.E.E D := by
    intro x hx
    have hxW : x ∈ W := by rwa [hDsupp] at hx
    obtain ⟨n, z, c, hz, hzc, hc⟩ := hT.2.2.2.2.2.2 x
    have hxi : x ∈ (T.E.E i).support := hWi hxW
    obtain ⟨n', z', j', hz', hz'j⟩ := hDpar x hx
    let P : PrimeSpectrum (V.presheaf.stalk x) :=
      ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hz' j'⟩
    have hPW : V.fromSpecStalk x P ∈ W := by
      rw [← hDsupp]; exact (fromSpecStalk_mem_support_iff_stalk_le D x P).2 hz'j.le
    have hle := (fromSpecStalk_mem_support_iff_stalk_le (T.E.E i) x P).1 (hWi hPW)
    rw [hzc ⟨i, hxi⟩, Ideal.span_singleton_le_iff_mem] at hle
    have heq := span_singleton_eq_of_mem hz' hz j' (c ⟨i, hxi⟩) hle
    refine ⟨n, z, c, {c ⟨i, hxi⟩}, hz, hzc, hc, ?_⟩
    rw [hz'j, ← heq]
    simp
  have hc : T.IsTransformCentre sV D := ⟨hDsm, hHas⟩
  have hdisjS : Disjoint (D.support : Set V) T.sncLocus := by
    rw [hDsupp]
    exact disjoint_sncLocus_of_subset_support T (p := .inl ⟨0, h0⟩) (q := .inr i)
      Sum.inl_ne_inr hW hWi
  have hIle : I0 ≤ D := by rw [hsplit]; exact mul_le_of_le_one_right' le_top
  have hI0' : (T.transform D).I ⟨0, h0⟩ = J.comap π := by
    refine (OrderedDivisorTuple.transform_I_of_le T D ⟨0, h0⟩
      (by rw [hDsupp]; exact hW.1.2)).trans ?_
    rw [← comap_idealColon_of_isIso π I0 D hDcart hIle]
    congr 1
    rw [hsplit]
    exact idealColon_mul_cancel D J hDcart
  have hJred : J.comap π = Scheme.IdealSheafData.vanishingIdeal (J.comap π).support := by
    rw [hJdef, comap_vanishingIdeal_of_isIso]
    congr 1
  have hJpar := exists_stalk_comap_eq_span_parameter π J (fun x hx => by
    have hxS : x ∈ (I0.support : Set V) ∧ x ∉ W := by
      rw [hJsupp] at hx; exact hx
    obtain ⟨n, z, j, hz, hzj⟩ := hP x hxS.1
    refine ⟨n, z, j, hz, ?_⟩
    rw [← hzj, hsplit, IdealSheafData.stalk_mul,
      (IdealSheafData.stalk_eq_top_iff_notMem_support D x).2
        (by rw [← SetLike.mem_coe, hDsupp]; exact hxS.2), Ideal.top_mul])
  have hsupp' : (((T.transform D).I ⟨0, h0⟩).support : Set (blowUp D)) =
      π ⁻¹' ((I0.support : Set V) \ W) := by
    rw [hI0', Scheme.IdealSheafData.support_comap, ← hJsupp]
    rfl
  have hfin : (componentsOf (I0.support : Set V)).Finite :=
    (Aux.finite_and_cover_componentsOf (T := V) I0.support.isClosed).1
  have hlt : (componentsOf (((T.transform D).I ⟨0, h0⟩).support : Set (blowUp D))).ncard <
      (componentsOf (I0.support : Set V)).ncard := by
    have hsurj : Function.Surjective π := π.homeomorph.surjective
    rw [hsupp', componentsOf_preimage_of_isIso π,
      Set.ncard_image_of_injective (f := fun x => (π : blowUp D → V) ⁻¹' x) _
        (Set.preimage_injective.2 hsurj),
      componentsOf_diff_of_mem hW hWc (hJsupp ▸ J.support.isClosed)]
    exact Set.ncard_diff_singleton_lt_of_mem hW hfin
  exact ⟨.cons D (.nil _), ⟨hc, hdisjS, trivial⟩, h0,
    FirstIdealData.of_eq (T := finalTuple (.cons D (.nil _)) T) hI0' hJred hJpar, hlt⟩

/-- **Step 1, first part**: the components of the first cosupport lying in the boundary are
blown up one at a time; it suffices to resolve the tuples so reached. -/
private theorem resolvable_one_of_cartier {k : Type u} [Field k] (n : ℕ)
    (hcont : ∀ {V' : Scheme.{u}} (sV' : V' ⟶ Spec (.of k)) (T' : OrderedDivisorTuple V'),
      IsOrderedDivisorTuple sV' T' → topologicalKrullDim V' ≤ n → T'.m = 1 →
      ∀ h : 0 < T'.m, FirstIdealData sV' T' h →
      (∀ W ∈ componentsOf ((T'.I ⟨0, h⟩).support : Set V'), ∀ i,
        ¬ W ⊆ ((T'.E.E i).support : Set V')) → Resolvable sV' T') :
    ∀ (N : ℕ) {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V),
      IsOrderedDivisorTuple sV T → topologicalKrullDim V ≤ n → T.m = 1 → ∀ h0 : 0 < T.m,
      FirstIdealData sV T h0 → (componentsOf ((T.I ⟨0, h0⟩).support : Set V)).ncard = N →
      Resolvable sV T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro V sV T hT hdim hm h0 hS hNc
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  by_cases hbad : ∃ W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V), ∃ i,
      W ⊆ ((T.E.E i).support : Set V)
  · obtain ⟨W, hW, i, hWi⟩ := hbad
    obtain ⟨B, hB, h', hS', hlt⟩ := exists_validS_cartier_boundary sV T hT h0 hS hW hWi
    exact resolvable_of_validS hT B hB fun hT' hd =>
      ihN _ (hNc ▸ hlt) (B.toBase ≫ sV) _ hT' (hd.trans hdim) (by rw [finalTuple_m, hm])
        h' hS' rfl
  · simp only [not_exists, not_and] at hbad
    exact hcont sV T hT hdim hm h0 hS fun W hW i => hbad W hW i

/-! ### Step 1: the boundary components one at a time -/

/-- Snc at every point of an snc family. -/
private theorem isSNCAt_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {Λ : Type*} {E : Λ → X.IdealSheafData} (h : IsSNCFamily s E) (x : X) :
    IsSNCAt E x := by
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h.2 x
  exact ⟨n, z, c, hz, hinj, hc⟩

/-- Simple normal crossings with a family pass to a family whose members through each point of
the centre have, injectively, the stalks of members of the given family. -/
private theorem hasSNCWith_of_forall {X : Scheme.{u}} {Λ Λ' : Type*} {E : Λ → X.IdealSheafData}
    {E' : Λ' → X.IdealSheafData} {Z : X.IdealSheafData} (h : HasSNCWith E Z) (f : Λ' → Λ)
    (hst : ∀ x ∈ (Z.support : Set X), ∀ i', x ∈ (E' i').support →
      IdealSheafData.stalk (E' i') x = IdealSheafData.stalk (E (f i')) x)
    (hinj : ∀ x ∈ (Z.support : Set X), ∀ i' j', x ∈ (E' i').support → x ∈ (E' j').support →
      f i' = f j' → i' = j') :
    HasSNCWith E' Z := by
  intro x hx
  obtain ⟨n, z, c, J, hz, hc, hcinj, hJ⟩ := h x hx
  have hsupp : ∀ i', x ∈ (E' i').support → x ∈ (E (f i')).support := fun i' hi => by
    by_contra hn
    rw [← IdealSheafData.stalk_eq_top_iff_notMem_support, ← hst x hx i' hi,
      IdealSheafData.stalk_eq_top_iff_notMem_support] at hn
    exact hn hi
  let c' : {i' // x ∈ (E' i').support} → Fin n := fun p => c ⟨f p.1, hsupp p.1 p.2⟩
  have hc' : ∀ p : {i' // x ∈ (E' i').support},
      IdealSheafData.stalk (E' p.1) x = Ideal.span {z (c' p)} := fun p =>
    (hst x hx p.1 p.2).trans (hc ⟨f p.1, hsupp p.1 p.2⟩)
  have hinj' : Function.Injective c' := fun p q hpq =>
    Subtype.ext (hinj x hx p.1 q.1 p.2 q.2 (congrArg Subtype.val (hcinj hpq)))
  exact ⟨n, z, c', J, hz, hc', hinj', hJ⟩

/-- Reduced ideal sheaves with the same support near `y` have the same stalk at `y`. -/
private theorem stalk_eq_of_support_inter_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : IsReduced I.subscheme) (hJ : IsReduced J.subscheme) {U : X.Opens} {y : X} (hy : y ∈ U)
    (h : (I.support : Set X) ∩ U = (J.support : Set X) ∩ U) :
    IdealSheafData.stalk I y = IdealSheafData.stalk J y := by
  have hpre : ∀ p : PrimeSpectrum (X.presheaf.stalk y),
      X.fromSpecStalk y p ∈ (I.support : Set X) ↔ X.fromSpecStalk y p ∈ (J.support : Set X) := by
    intro p
    have hU : X.fromSpecStalk y p ∈ (U : Set X) :=
      (fromSpecStalk_specializes_self y p).mem_open U.isOpen hy
    constructor
    · intro h1
      have h3 : X.fromSpecStalk y p ∈ (I.support : Set X) ∩ U := ⟨h1, hU⟩
      rw [h] at h3
      exact h3.1
    · intro h2
      have h3 : X.fromSpecStalk y p ∈ (J.support : Set X) ∩ U := ⟨h2, hU⟩
      rw [← h] at h3
      exact h3.1
  rw [← MMP.Positivity.vanishingIdeal_support_of_isReduced I,
    ← MMP.Positivity.vanishingIdeal_support_of_isReduced J]
  have hz : ∀ Z : TopologicalSpace.Closeds X, PrimeSpectrum.zeroLocus
      (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) y : Set _) =
      X.fromSpecStalk y ⁻¹' Z := fun Z => by
    rw [← preimage_fromSpecStalk_support, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  calc IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal I.support) y
      = (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal I.support) y).radical :=
        (isRadical_stalk_vanishingIdeal _ y).radical.symm
    _ = PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus
        (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal I.support) y : Set _)) :=
        (PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical _).symm
    _ = PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus
        (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal J.support) y : Set _)) := by
        rw [hz, hz]
        congr 1
        ext p
        exact hpre p
    _ = (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal J.support) y).radical :=
        PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical _
    _ = _ := (isRadical_stalk_vanishingIdeal _ y).radical

/-- A reduced ideal sheaf whose support is `ι(S) ∪ p⁻¹R`, with `ι(S)` missing `p⁻¹R`, has along
`ι(S)` the stalks of the ideal of `ι(S)`. -/
private theorem stalk_eq_stalk_ker_of_support_eq {S W V : Scheme.{u}} (ι : S ⟶ W)
    [IsClosedImmersion ι] (hι : IsReduced ι.ker.subscheme) (E : W.IdealSheafData)
    (hE : IsReduced E.subscheme) (p : W ⟶ V) {R : Set V} (hR : IsClosed R)
    (hsupp : (E.support : Set W) = Set.range ι ∪ p ⁻¹' R) (hdisj : ∀ x ∈ Set.range ι, p x ∉ R)
    {x : W} (hx : x ∈ Set.range ι) :
    IdealSheafData.stalk E x = IdealSheafData.stalk ι.ker x := by
  refine stalk_eq_of_support_inter_eq E ι.ker hE hι
    (U := ⟨(p ⁻¹' R)ᶜ, (hR.preimage p.continuous).isOpen_compl⟩) (hdisj x hx) ?_
  rw [hsupp, Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_union, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff,
    Set.mem_preimage]
  tauto

/-- An irreducible closed set strictly inside one of codimension one has codimension `≥ 2`. -/
private theorem two_le_codimension_of_lt {X : Scheme.{u}}
    {Y H : TopologicalSpace.IrreducibleCloseds X} (hH : codimension H = 1) (h : Y < H) :
    2 ≤ codimension Y := by
  have h' := Order.coheight_add_one_le h
  rwa [← codimension_eq_coheight, ← codimension_eq_coheight, hH] at h'

/-- Every irreducible subset of `D` lies in an irreducible component of `D`. -/
private theorem exists_mem_componentsOf_superset {T : Type*} [TopologicalSpace T] {D Y : Set T}
    (hY : IsIrreducible Y) (hYD : Y ⊆ D) : ∃ W ∈ componentsOf D, Y ⊆ W := by
  obtain ⟨m, hYm, hm⟩ := zorn_subset_nonempty {t : Set T | IsPreirreducible t ∧ t ⊆ D}
    (fun c hc hcc _ => ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ => by
        obtain ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
        obtain ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
        rcases hcc.total hpc hqc with hpq | hqp
        · obtain ⟨w, hwq, hwuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
          exact ⟨w, Set.mem_sUnion_of_mem hwq hqc, hwuv⟩
        · obtain ⟨w, hwp, hwuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
          exact ⟨w, Set.mem_sUnion_of_mem hwp hpc, hwuv⟩,
      Set.sUnion_subset fun t ht => (hc ht).2⟩, fun _ h => Set.subset_sUnion_of_mem h⟩)
    Y ⟨hY.2, hYD⟩
  obtain ⟨y, hy⟩ := hY.nonempty
  refine ⟨m, ?_, hYm⟩
  change Maximal (fun W' : Set T => IsIrreducible W' ∧ W' ⊆ D) m
  exact ⟨⟨⟨⟨y, hYm hy⟩, hm.prop.1⟩, hm.prop.2⟩, fun W hW hmW => hm.2 ⟨hW.1.2, hW.2⟩ hmW⟩

/-- Components of closed sets of pure codimension one, one inside the other, are equal. -/
private theorem eq_of_mem_componentsOf_of_subset {X : Scheme.{u}}
    {A B : TopologicalSpace.Closeds X} (hA : MMP.Mori.IsPureCodimOne A)
    (hB : MMP.Mori.IsPureCodimOne B) {W V : Set X} (hW : W ∈ componentsOf (A : Set X))
    (hV : V ∈ componentsOf (B : Set X)) (h : W ⊆ V) : W = V := by
  have hWc := Aux.isClosed_of_mem_componentsOf A.isClosed hW
  have hVc := Aux.isClosed_of_mem_componentsOf B.isClosed hV
  have hW1 := codimension_eq_one_of_mem_componentsOf hA hW
  have hV1 := codimension_eq_one_of_mem_componentsOf hB hV
  by_contra hne
  have hlt : irreducibleClosure hW.1.1 < irreducibleClosure hV.1.1 := by
    refine lt_of_le_of_ne (fun x hx => closure_mono h hx) fun he => hne ?_
    have := congrArg (fun C : TopologicalSpace.IrreducibleCloseds X => (C : Set X)) he
    change closure W = closure V at this
    rwa [hWc.closure_eq, hVc.closure_eq] at this
  have h2 := two_le_codimension_of_lt hV1 hlt
  rw [hW1] at h2
  exact absurd h2 (by decide)

/-- An irreducible set of codimension `≥ 2` is no component of the support of an ordered divisor
whose entries are of pure codimension one. -/
private theorem notMem_componentsOf_support_of_two_le {X : Scheme.{u}} (E : OrderedDivisor X)
    (hE : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support) {Y : Set X} (hY : IsIrreducible Y)
    (h2 : 2 ≤ codimension (irreducibleClosure hY)) : Y ∉ componentsOf E.support := by
  intro hYE
  obtain ⟨_, hz, hYz⟩ := isIrreducible_iff_sUnion_isClosed.mp hY
    (Finset.univ.image fun i => ((E.E i).support : Set X))
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
      exact (E.E i).support.isClosed)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hYE.1.2 hx)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2
        ⟨i, Finset.mem_univ _, rfl⟩), hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨W, hW, hYW⟩ := exists_mem_componentsOf_superset hY hYz
  have hWY : W ⊆ Y := hYE.2 ⟨hW.1.1, hW.1.2.trans
    (Set.subset_iUnion (fun i => ((E.E i).support : Set X)) i)⟩ hYW
  obtain rfl : Y = W := le_antisymm hYW hWY
  have := codimension_eq_one_of_mem_componentsOf (hE i) hW
  rw [this] at h2
  exact absurd h2 (by decide)

/-- If every component of a closed set has codimension `≥ 2`, the union of its components of
codimension `≥ 2` is the set. -/
private theorem componentsOfCodimAtLeastTwo_eq_self {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] {A : Set X} (hA : IsClosed A)
    (h2 : ∀ W (hW : W ∈ componentsOf A), 2 ≤ codimension (irreducibleClosure hW.1.1)) :
    componentsOfCodimAtLeastTwo A = A := by
  have : IsNoetherian X := {}
  refine subset_antisymm (componentsOfCodimAtLeastTwo_subset A) fun x hx => ?_
  obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 ((Aux.finite_and_cover_componentsOf hA).2 hx)
  exact (mem_componentsOfCodimAtLeastTwo A x).2 ⟨W, hW, h2 W hW, hxW⟩

/-- The new entry of the total transform along a centre all of whose components have
codimension `≥ 2` is the reduced inverse image of the centre. -/
private theorem totalTransform_E_last_of_codim {X : Scheme.{u}} [IsLocallyNoetherian X]
    [CompactSpace X] (E : OrderedDivisor X) (hE : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support)
    (C : X.IdealSheafData)
    (h2 : ∀ W (hW : W ∈ componentsOf (C.support : Set X)),
      2 ≤ codimension (irreducibleClosure hW.1.1)) :
    (E.totalTransform C).E (Fin.last E.s) = Scheme.IdealSheafData.vanishingIdeal
      ⟨blowUpToBase C ⁻¹' C.support, C.support.isClosed.preimage (blowUpToBase C).continuous⟩ := by
  have : IsNoetherian X := {}
  rw [totalTransform_E_eq]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure]
  have hset : totalTransformSet E C (Fin.last E.s) = blowUpToBase C ⁻¹' C.support := by
    simp only [totalTransformSet, Fin.snoc_last]
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
    constructor
    · rintro ⟨W, hW, -, hy⟩
      exact hW.1.2 hy
    · intro hy
      obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1
        ((Aux.finite_and_cover_componentsOf C.support.isClosed).2 hy)
      exact ⟨W, hW, notMem_componentsOf_support_of_two_le E hE hW.1.1 (h2 W hW), hyW⟩
  rw [hset]
  exact (C.support.isClosed.preimage (blowUpToBase C).continuous).closure_eq

/-- The old entries of the total transform along a centre all of whose components have
codimension `≥ 2` are the strict transforms. -/
private theorem support_totalTransform_E_castSucc_of_codim {X : Scheme.{u}}
    (E : OrderedDivisor X) (C : X.IdealSheafData)
    (hC2 : componentsOfCodimAtLeastTwo (C.support : Set X) = C.support) (i : Fin E.s) :
    (((E.totalTransform C).E (Fin.castSucc i)).support : Set (blowUp C)) =
      closure (blowUpToBase C ⁻¹' ((E.E i).support \ C.support)) := by
  rw [totalTransform_E_castSucc, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_closure, hC2]

/-- An entry of an snc family is a parameter divisor. -/
private theorem isParamDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {Λ : Type*}
    {E : Λ → X.IdealSheafData} (h : IsSNCFamily s E) (i : Λ) : IsParamDivisor (E i) := by
  intro x hx
  obtain ⟨n, z, c, hz, hst, -⟩ := h.2 x
  exact ⟨n, z, c ⟨i, hx⟩, hz, hst ⟨i, hx⟩⟩

/-- The tuple with its boundary entry of index `i₀` replaced by `K`. -/
private abbrev modEntry {V : Scheme.{u}} (T : OrderedDivisorTuple V) (i₀ : ℕ)
    (K : V.IdealSheafData) : OrderedDivisorTuple V :=
  ⟨T.m, T.I, ⟨T.E.s, fun j => if (j : ℕ) = i₀ then K else T.E.E j⟩⟩

/-- The boundary entries of index at least `s₀`. -/
private abbrev excDiv {V : Scheme.{u}} (E : OrderedDivisor V) (s₀ : ℕ) : OrderedDivisor V :=
  ⟨E.s - s₀, fun j => E.E ⟨s₀ + j, by have := j.isLt; omega⟩⟩

/-- The first ideal is the ideal of a closed subscheme which together with the boundary entries
of index at least `s₀` is snc. -/
private def ExcSNC {k : Type u} [Field k] {V : Scheme.{u}} (s : V ⟶ Spec (.of k))
    (T : OrderedDivisorTuple V) (s₀ : ℕ) : Prop :=
  s₀ ≤ T.E.s ∧ ∃ h0 : 0 < T.m, ∃ (S : Scheme.{u}) (ιS : S ⟶ V), IsClosedImmersion ιS ∧
    T.I ⟨0, h0⟩ = ιS.ker ∧
    IsSNCFamily s fun o : Option (Fin (excDiv T.E s₀).s) => o.elim ιS.ker (excDiv T.E s₀).E

/-- The components of the boundary entries of index below `s₀` along which the tuple is not
snc, with the index of their entry. -/
private def badPairs {V : Scheme.{u}} (T : OrderedDivisorTuple V) (s₀ : ℕ) : Set (ℕ × Set V) :=
  {q | ∃ h : q.1 < T.E.s, q.1 < s₀ ∧ q.2 ∈ componentsOf ((T.E.E ⟨q.1, h⟩).support : Set V) ∧
    ¬ q.2 ⊆ T.sncLocus}

/-- No bad component lies in the cosupport of the first ideal. -/
private def NoBadInFirst {V : Scheme.{u}} (T : OrderedDivisorTuple V) (s₀ : ℕ) : Prop :=
  ∀ h0 : 0 < T.m, ∀ q ∈ badPairs T s₀, ¬ q.2 ⊆ ((T.I ⟨0, h0⟩).support : Set V)

/-- The total transform of the boundary entries of index at least `s₀` along a centre all of
whose components have codimension `≥ 2` are the entries of index at least `s₀` of the total
transform. -/
private theorem excDiv_totalTransform_E {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (E : OrderedDivisor X) (s₀ : ℕ) (hs₀ : s₀ ≤ E.s) (C : X.IdealSheafData)
    (hE : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support)
    (h2 : ∀ W (hW : W ∈ componentsOf (C.support : Set X)),
      2 ≤ codimension (irreducibleClosure hW.1.1)) (j : ℕ) (hj : j < E.s + 1 - s₀)
    (hj' : j < (excDiv E s₀).s + 1) :
    (E.totalTransform C).E ⟨s₀ + j, by change s₀ + j < E.s + 1; omega⟩ =
      ((excDiv E s₀).totalTransform C).E ⟨j, hj'⟩ := by
  by_cases hjs : s₀ + j < E.s
  · exact (totalTransform_E_castSucc E C ⟨s₀ + j, hjs⟩).trans
      (totalTransform_E_castSucc (excDiv E s₀) C ⟨j, by change j < E.s - s₀; omega⟩).symm
  · have hpA : ∀ i, MMP.Mori.IsPureCodimOne ((excDiv E s₀).E i).support := fun i => hE _
    calc (E.totalTransform C).E ⟨s₀ + j, _⟩ = (E.totalTransform C).E (Fin.last E.s) :=
          congrArg _ (Fin.ext (by show s₀ + j = E.s; omega))
      _ = _ := totalTransform_E_last_of_codim _ hE C h2
      _ = ((excDiv E s₀).totalTransform C).E (Fin.last (excDiv E s₀).s) :=
          (totalTransform_E_last_of_codim _ hpA C h2).symm
      _ = _ := congrArg _ (Fin.ext (by show E.s - s₀ = j; omega))

/-- The invariant `ExcSNC` passes to the transform along a centre inside the first cosupport all
of whose components have codimension `≥ 2`. -/
private theorem excSNC_transform {k : Type u} [Field k] {V : Scheme.{u}} {s : V ⟶ Spec (.of k)}
    {T : OrderedDivisorTuple V} {s₀ : ℕ} (hT : IsOrderedDivisorTuple s T) (hB : ExcSNC s T s₀)
    (C : V.IdealSheafData) (hc : T.IsTransformCentre s C)
    (hCS : ∀ h0 : 0 < T.m, (C.support : Set V) ⊆ (T.I ⟨0, h0⟩).support)
    (h2 : ∀ W (hW : W ∈ componentsOf (C.support : Set V)),
      2 ≤ codimension (irreducibleClosure hW.1.1)) :
    ExcSNC (blowUpToBase C ≫ s) (T.transform C) s₀ := by
  obtain ⟨hs₀, h0, S, ιS, hιS, hI0, hsnc⟩ := hB
  have hvar : AlgebraicGeometry.IsVariety k s := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace s
  let g : Fin (excDiv T.E s₀).s → Fin T.E.s := fun j =>
    ⟨s₀ + j, by have := j.isLt; simp only [excDiv] at this; omega⟩
  have hg : Function.Injective g := fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [g] at this; omega)
  let Taux : OrderedDivisorTuple V := ⟨0, Fin.elim0, excDiv T.E s₀⟩
  have hTaux : IsOrderedDivisorTuple s Taux :=
    ⟨hT.1, hT.2.1, hT.2.2.1, fun j => j.elim0, fun j => hT.2.2.2.2.1 (g j),
      isSNCFamily_comp hT.2.2.2.2.2 g hg⟩
  have hinvS : LiftInvariant ιS s Taux := ⟨hιS, hTaux, hsnc⟩
  have hCred : IsReduced C.subscheme := Aux.isReduced_subscheme_of_isSmoothScheme s C hc.1
  have hle : ιS.ker ≤ C := by
    rw [← MMP.Positivity.vanishingIdeal_support_of_isReduced C, ← hI0]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 (hCS h0)
  have hcS : Taux.IsTransformCentre s C := ⟨hc.1, hasSNCWith_of_forall hc.2 g
    (fun _ _ _ _ => rfl) fun _ _ _ _ _ _ h => hg h⟩
  have key1 := isSNCFamily_transform_of_le hinvS C hle hcS
  have key2 := comap_ker_eq_mul_ker_canonicalLift_of_le hinvS C hle hcS
  have hpT : ∀ i, MMP.Mori.IsPureCodimOne (T.E.E i).support := fun i =>
    (hT.2.2.2.2.2.1 i).2.1
  have hpA : ∀ i, MMP.Mori.IsPureCodimOne ((excDiv T.E s₀).E i).support := fun i =>
    (hTaux.2.2.2.2.2.1 i).2.1
  refine ⟨by change s₀ ≤ T.E.s + 1; omega, h0, _, canonicalLift ιS C,
    Bridges.isClosedImmersion_canonicalLift ιS C, ?_, ?_⟩
  · refine (OrderedDivisorTuple.transform_I_of_le T C ⟨0, h0⟩ (hCS h0)).trans ?_
    rw [hI0, key2]
    exact idealColon_mul_cancel _ _ (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal C)
  · let e : Fin (excDiv (T.transform C).E s₀).s → Fin (Taux.transform C).E.s :=
      Fin.cast (by change T.E.s + 1 - s₀ = T.E.s - s₀ + 1; omega)
    have := isSNCFamily_comp key1 (Option.map e)
      (Option.map_injective (Fin.cast_injective _))
    convert this using 1
    funext o
    rcases o with _ | j
    · rfl
    · exact excDiv_totalTransform_E T.E s₀ hs₀ C hpT h2 j (by
        have := j.isLt; change (j : ℕ) < T.E.s + 1 - s₀ at this; omega) _

/-- Without bad components, a tuple with one ideal satisfying `ExcSNC` is snc everywhere. -/
private theorem sncLocus_eq_univ_of_badPairs_eq_empty {k : Type u} [Field k] {V : Scheme.{u}}
    {s : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} {s₀ : ℕ} (hm : T.m = 1)
    (hB : ExcSNC s T s₀) (hbad : badPairs T s₀ = ∅) : T.sncLocus = Set.univ := by
  obtain ⟨hs₀, h0, S, ιS, hιS, hI0, hsnc⟩ := hB
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hy : ∃ i : Fin T.E.s, (i : ℕ) < s₀ ∧ y ∈ (T.E.E i).support
  · obtain ⟨i, hi, hyi⟩ := hy
    obtain ⟨W, hW, hyW⟩ := exists_mem_componentsOf (D := ((T.E.E i).support : Set V)) hyi
    by_contra hns
    have hq : ((i : ℕ), W) ∈ badPairs T s₀ := ⟨i.isLt, hi, hW, fun h => hns (h hyW)⟩
    rw [hbad] at hq
    exact hq
  · push Not at hy
    rw [mem_sncLocus_iff]
    let f : Fin T.m ⊕ Fin T.E.s → Option (Fin (excDiv T.E s₀).s) :=
      Sum.elim (fun _ => none) fun i => if h : s₀ ≤ (i : ℕ) then
        some ⟨(i : ℕ) - s₀, by change (i : ℕ) - s₀ < T.E.s - s₀; have := i.isLt; omega⟩ else none
    have hsi : ∀ i : Fin T.E.s, y ∈ (T.E.E i).support → s₀ ≤ (i : ℕ) := fun i hi => by
      by_contra h
      exact hy i (by omega) hi
    refine IsSNCAt.of_forall (isSNCAt_of_isSNCFamily hsnc y) f ?_ ?_
    · rintro (j | i) hp
      · obtain rfl : j = ⟨0, h0⟩ := Fin.ext (by have := j.isLt; omega)
        change IdealSheafData.stalk (T.I ⟨0, h0⟩) y = IdealSheafData.stalk ιS.ker y
        rw [hI0]
      · have h1 := hsi i hp
        change IdealSheafData.stalk (T.E.E i) y = IdealSheafData.stalk
          (Option.elim (if h : s₀ ≤ (i : ℕ) then some _ else none) ιS.ker (excDiv T.E s₀).E) y
        rw [dif_pos h1]
        change IdealSheafData.stalk (T.E.E i) y = IdealSheafData.stalk
          (T.E.E ⟨s₀ + ((i : ℕ) - s₀), _⟩) y
        congr 3
        exact Fin.ext (by simp only; omega)
    · rintro (j | i) (j' | i') hp hp' h
      · exact congrArg Sum.inl (Fin.ext (by have := j.isLt; have := j'.isLt; omega))
      · have h1 := hsi i' hp'
        simp [f, dif_pos h1] at h
      · have h1 := hsi i hp
        simp [f, dif_pos h1] at h
      · have h1 := hsi i hp
        have h1' := hsi i' hp'
        simp only [f, Sum.elim_inr, dif_pos h1, dif_pos h1', Option.some.injEq, Fin.mk.injEq] at h
        exact congrArg Sum.inr (Fin.ext (by omega))

/-- At the start, `ExcSNC` holds with all entries original. -/
private theorem excSNC_of_firstIdealData {k : Type u} [Field k] {V : Scheme.{u}}
    {s : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (hT : IsOrderedDivisorTuple s T)
    (h0 : 0 < T.m) (hS : FirstIdealData s T h0) : ExcSNC s T T.E.s := by
  have hvar : AlgebraicGeometry.IsVariety k s := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  have : CharZero k := hT.1
  refine ⟨le_rfl, h0, _, (T.I ⟨0, h0⟩).subschemeι, inferInstance,
    (Scheme.IdealSheafData.ker_subschemeι _).symm, ?_⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  have hempty : ∀ j : Fin (excDiv T.E T.E.s).s, False := fun j => by
    have := j.isLt; change (j : ℕ) < T.E.s - T.E.s at this; omega
  refine isSNCFamily_of_forall_isSNCAt fun y => ?_
  by_cases hy : y ∈ (T.I ⟨0, h0⟩).support
  · obtain ⟨n, z, j, hz, hzj⟩ := hS.param y hy
    refine ⟨n, z, fun _ => j, hz, fun a b _ => ?_, ?_⟩
    · rcases a with ⟨_ | a, ha⟩
      · rcases b with ⟨_ | b, hb⟩
        · rfl
        · exact (hempty b).elim
      · exact (hempty a).elim
    · rintro ⟨_ | a, ha⟩
      · exact hzj
      · exact (hempty a).elim
  · have hno : ∀ o : Option (Fin (excDiv T.E T.E.s).s),
        y ∉ (o.elim (T.I ⟨0, h0⟩) (excDiv T.E T.E.s).E).support := by
      rintro (_ | a)
      · exact hy
      · exact (hempty a).elim
    exact IsSNCAt.of_injective (isSNCAt_of_isSNCFamily hT.2.2.2.2.2 y)
      (fun p => (hno p.1 p.2).elim) (fun p => (hno p.1 p.2).elim) fun p => (hno p.1 p.2).elim

/-- At the start, no component of an original entry lies in the first cosupport. -/
private theorem noBadInFirst_of_firstIdealData {k : Type u} [Field k] {V : Scheme.{u}}
    {s : V ⟶ Spec (.of k)} {T : OrderedDivisorTuple V} (hT : IsOrderedDivisorTuple s T)
    (h0 : 0 < T.m) (hS : FirstIdealData s T h0)
    (hE : ∀ W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V), ∀ i,
      ¬ W ⊆ ((T.E.E i).support : Set V)) :
    NoBadInFirst T T.E.s := by
  have hvar : AlgebraicGeometry.IsVariety k s := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  intro h0' q hq hsub
  obtain ⟨hi, -, hW, -⟩ := hq
  obtain ⟨V₀, hV₀, hWV⟩ := exists_mem_componentsOf_superset hW.1.1 hsub
  have hpS : MMP.Mori.IsPureCodimOne (T.I ⟨0, h0'⟩).support :=
    isPureCodimOne_support_of_stalk_eq_span_parameter _ hS.param
  have heq := eq_of_mem_componentsOf_of_subset (hT.2.2.2.2.2.1 _).2.1 hpS hW hV₀ hWV
  exact hE V₀ hV₀ _ (heq ▸ hW.1.2)

/-- Equality of ordered divisors from equality of their entries. -/
private theorem orderedDivisor_ext {X : Scheme.{u}} {E E' : OrderedDivisor X} (hs : E.s = E'.s)
    (hE : ∀ j : Fin E.s, E.E j = E'.E (Fin.cast hs j)) : E = E' := by
  obtain ⟨s, E⟩ := E
  obtain ⟨s', E'⟩ := E'
  obtain rfl : s = s' := hs
  congr 1
  funext j
  exact hE j

/-- Replacing a boundary entry by the reduced ideal of a closed set off the centre commutes with
the transformation along a centre all of whose components have codimension `≥ 2`. -/
private theorem modEntry_transform {V : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    (Tx : OrderedDivisorTuple V) (i₀ : ℕ) (hi₀ : i₀ < Tx.E.s) (A : TopologicalSpace.Closeds V)
    (C : V.IdealSheafData) (hAC : Disjoint (A : Set V) C.support)
    (hpx : ∀ j, MMP.Mori.IsPureCodimOne (Tx.E.E j).support)
    (hpA : MMP.Mori.IsPureCodimOne (Scheme.IdealSheafData.vanishingIdeal A).support)
    (h2 : ∀ W (hW : W ∈ componentsOf (C.support : Set V)),
      2 ≤ codimension (irreducibleClosure hW.1.1)) :
    (modEntry Tx i₀ (Scheme.IdealSheafData.vanishingIdeal A)).transform C =
      modEntry (Tx.transform C) i₀ (Scheme.IdealSheafData.vanishingIdeal
        ⟨blowUpToBase C ⁻¹' A, A.isClosed.preimage (blowUpToBase C).continuous⟩) := by
  set K := Scheme.IdealSheafData.vanishingIdeal A
  have hpM : ∀ j, MMP.Mori.IsPureCodimOne ((modEntry Tx i₀ K).E.E j).support := by
    intro j
    change MMP.Mori.IsPureCodimOne (if (j : ℕ) = i₀ then K else Tx.E.E j).support
    split_ifs
    · exact hpA
    · exact hpx j
  have hC2 := componentsOfCodimAtLeastTwo_eq_self C.support.isClosed h2
  set K' := Scheme.IdealSheafData.vanishingIdeal (⟨blowUpToBase C ⁻¹' A,
    A.isClosed.preimage (blowUpToBase C).continuous⟩ : TopologicalSpace.Closeds (blowUp C))
  have hE : ∀ j : Fin (Tx.E.s + 1), ((modEntry Tx i₀ K).E.totalTransform C).E j =
      if (j : ℕ) = i₀ then K' else (Tx.E.totalTransform C).E j := by
    intro j
    induction j using Fin.lastCases with
    | last =>
      rw [if_neg (by simp only [Fin.val_last]; omega)]
      exact (totalTransform_E_last_of_codim _ hpM C h2).trans
        (totalTransform_E_last_of_codim _ hpx C h2).symm
    | cast j =>
      rw [Fin.coe_castSucc]
      by_cases hj : (j : ℕ) = i₀
      · rw [if_pos hj]
        refine (totalTransform_E_castSucc (modEntry Tx i₀ K).E C j).trans ?_
        have hK : (modEntry Tx i₀ K).E.E j = K := if_pos hj
        rw [hK]
        congr 1
        apply TopologicalSpace.Closeds.ext
        rw [TopologicalSpace.Closeds.coe_closure, Scheme.IdealSheafData.coe_support_vanishingIdeal,
          hC2, sdiff_eq_left.2 hAC]
        exact (A.isClosed.preimage (blowUpToBase C).continuous).closure_eq
      · rw [if_neg hj]
        have hK : (modEntry Tx i₀ K).E.E j = Tx.E.E j := if_neg hj
        refine (totalTransform_E_castSucc (modEntry Tx i₀ K).E C j).trans ?_
        rw [hK]
        exact (totalTransform_E_castSucc Tx.E C j).symm
  rw [show (modEntry Tx i₀ K).transform C =
    ⟨Tx.m, (Tx.transform C).I, (modEntry Tx i₀ K).E.totalTransform C⟩ from rfl]
  congr 1
  exact orderedDivisor_ext rfl hE

/-- Snc of the strict transform `ι(S)` together with the divisors of a tuple at a point of
`ι(S)` gives snc of the restricted tuple there. -/
private theorem mem_sncLocus_restrict_of_isSNCAt {k : Type u} [Field k] {S W : Scheme.{u}}
    {ι : S ⟶ W} {s : W ⟶ Spec (.of k)} {T : OrderedDivisorTuple W} (hinv : LiftInvariant ι s T)
    {ES : OrderedDivisor S} (hES : ES.support = (T.E.comap ι).support)
    (hTS : IsOrderedDivisorTuple (ι ≫ s) ⟨T.m, fun j => (T.I j).comap ι, ES⟩) (z : S)
    (h : IsSNCAt (fun o : Option (Fin T.m ⊕ Fin T.E.s) => o.elim ι.ker T.divisors) (ι z)) :
    z ∈ (⟨T.m, fun j => (T.I j).comap ι, ES⟩ : OrderedDivisorTuple S).sncLocus := by
  have : IsClosedImmersion ι := hinv.1
  have hvar : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ s)
  have h2 := isSNCAt_comap_of_isSNCAt_elim ι T.divisors z h
  obtain ⟨n, w, c, hw, hwc, hc'⟩ := hTS.2.2.2.2.2.2 z
  have h3 := isSNCAt_sumElim_of_iUnion_support_eq (fun j => (T.I j).comap ι)
    (fun j => (T.I j).comap ι) (Equiv.refl _) (fun _ => rfl) ES.E
    (T.E.comap ι).E z hES ⟨n, w, c, hw, hc', hwc⟩
    (IsSNCAt.of_forall h2 id (fun q _ => by rcases q with j | i <;> rfl) fun _ _ _ _ h => h)
  exact IsSNCAt.of_forall h3 id (fun q _ => by rcases q with j | i <;> rfl) fun _ _ _ _ h => h

/-- The stage predicate of Step 1, processing a component `W` of the boundary entry `i₀` of `T₀`
with `R` the rest of that entry: the lifted tuple is the real one with entry `i₀` replaced by
the inverse image of `R`; the real tuple is an ordered divisor tuple with one ideal satisfying
`ExcSNC`; its entry `i₀` is the strict transform of `W` together with the inverse image of `R`;
the strict transform lies over `W`; the inverse image of `W` lies in the strict transform and the
exceptional entries; and off the inverse image of `W` the original entries are unchanged. -/
private abbrev Step1Pred (k : Type u) [Field k] {V : Scheme.{u}} (s₀ i₀ : ℕ) (W R : Set V)
    (hR : IsClosed R) (T₀ : OrderedDivisorTuple V) (hs₀ : s₀ ≤ T₀.E.s) : LiftPred k V :=
  fun ι s p T₁ _ Tx =>
    T₁ = modEntry Tx i₀
      (Scheme.IdealSheafData.vanishingIdeal ⟨p ⁻¹' R, hR.preimage p.continuous⟩) ∧
    IsOrderedDivisorTuple s Tx ∧ Tx.m = 1 ∧ ExcSNC s Tx s₀ ∧
    (∃ h : i₀ < Tx.E.s, ((Tx.E.E ⟨i₀, h⟩).support : Set _) = Set.range ι ∪ p ⁻¹' R) ∧
    Set.range (ι ≫ p) ⊆ W ∧
    p ⁻¹' W ⊆ Set.range ι ∪ ⋃ (j : Fin Tx.E.s) (_ : s₀ ≤ (j : ℕ)), ((Tx.E.E j).support : Set _) ∧
    ∀ (i : Fin Tx.E.s) (hi : (i : ℕ) < s₀) (y), p y ∉ W →
      (y ∈ (Tx.E.E i).support ↔ p y ∈ (T₀.E.E ⟨i, lt_of_lt_of_le hi hs₀⟩).support)

private theorem liftStep_step1Pred {k : Type u} [Field k] {V : Scheme.{u}} (s₀ i₀ : ℕ)
    (W R : Set V) (hR : IsClosed R) (hWR : Disjoint W R) (T₀ : OrderedDivisorTuple V)
    (hs₀ : s₀ ≤ T₀.E.s) : LiftStep (Step1Pred k s₀ i₀ W R hR T₀ hs₀) := by
  intro S' W' ι s p T₁ ES Tx Z hinv hES hTS hQ0 hZ hdisj hc h
  obtain ⟨rfl, hTx, hm, hB, ⟨hi₀', hsupp0⟩, hpW, hpre, hover⟩ := hQ0
  have : IsClosedImmersion ι := hinv.1
  have hvar : AlgebraicGeometry.IsVariety k s := hinv.2.1.2.1
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ s)
  have h0 : 0 < Tx.m := by omega
  set K := Scheme.IdealSheafData.vanishingIdeal
    (⟨p ⁻¹' R, hR.preimage p.continuous⟩ : TopologicalSpace.Closeds W') with hK
  set C := Z.map ι with hCdef
  have hsuppC : (C.support : Set W') = ι '' Z.support := by
    rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure,
      (ι.isClosedEmbedding.isClosedMap _ Z.support.isClosed).closure_eq]
  have hrangeK : (Set.range ι : Set W') = (ι.ker.support : Set W') := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
  have hιR : ∀ x ∈ Set.range ι, p x ∉ R := by
    rintro _ ⟨z, rfl⟩ hz
    have := hpW ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply] at this
    exact hWR.notMem_of_mem_left this hz
  have hCι : (C.support : Set W') ⊆ Set.range ι := by
    rw [hsuppC]; exact Set.image_subset_range _ _
  have hιred : IsReduced ι.ker.subscheme := (hinv.2.2.1 none).1
  have hst0 : ∀ x ∈ Set.range ι, IdealSheafData.stalk (Tx.E.E ⟨i₀, hi₀'⟩) x =
      IdealSheafData.stalk ι.ker x := fun x hx =>
    stalk_eq_stalk_ker_of_support_eq ι hιred _ (hTx.2.2.2.2.1 _).1 p hR hsupp0 hιR hx
  have hKx : ∀ x ∈ Set.range ι, x ∉ K.support := fun x hx hxK => by
    rw [← SetLike.mem_coe, hK, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hxK
    exact hιR x hx hxK
  have hentry : ∀ j : Fin Tx.E.s, (modEntry Tx i₀ K).E.E j =
      if (j : ℕ) = i₀ then K else Tx.E.E j := fun j => rfl
  -- the generic point of `S'` is off `Z`
  have hSvar : AlgebraicGeometry.IsVariety k (ι ≫ s) := hTS.2.1
  have : IsIntegral S' := hSvar.toIsIntegral
  have hη : genericPoint S' ∉ (Z.support : Set S') := fun hη =>
    hdisj.notMem_of_mem_left hη (genericPoint_mem_sncLocus hTS)
  -- the components of the centre have codimension at least two
  have hirr : IsIrreducible (Set.range ι) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ S').image ι ι.continuous.continuousOn
  have hcomp : Set.range ι ∈ componentsOf (ι.ker.support : Set W') :=
    ⟨⟨hirr, hrangeK.le⟩, fun Y hY _ => hY.2.trans hrangeK.ge⟩
  have h1 := codimension_eq_one_of_mem_componentsOf (hinv.2.2.1 none).2.1 hcomp
  have h2 : ∀ Y (hY : Y ∈ componentsOf (C.support : Set W')),
      2 ≤ codimension (irreducibleClosure hY.1.1) := by
    intro Y hY
    refine two_le_codimension_of_lt h1 (lt_of_le_of_ne
      (fun x hx => closure_mono (hY.1.2.trans hCι) hx) fun he => ?_)
    have h3 := congrArg (fun A : TopologicalSpace.IrreducibleCloseds W' => (A : Set W')) he
    change closure Y = closure (Set.range ι) at h3
    have hYc : IsClosed Y := Aux.isClosed_of_mem_componentsOf C.support.isClosed hY
    rw [hYc.closure_eq, ι.isClosedEmbedding.isClosed_range.closure_eq] at h3
    have h4 : ι (genericPoint S') ∈ (C.support : Set W') := hY.1.2 (by rw [h3]; exact ⟨_, rfl⟩)
    rw [hsuppC] at h4
    obtain ⟨z, hz, hzη⟩ := h4
    exact hη (ι.isClosedEmbedding.injective hzη ▸ hz)
  have hC2 := componentsOfCodimAtLeastTwo_eq_self C.support.isClosed h2
  have hTxI : ∀ j : Fin Tx.m, j = ⟨0, h0⟩ := fun j => Fin.ext (by have := j.isLt; omega)
  -- the centre lies in the first cosupport
  have hCS : ∀ h0' : 0 < Tx.m, (C.support : Set W') ⊆ (Tx.I ⟨0, h0'⟩).support := by
    intro h0' x hx
    by_contra hx0
    have hx' := hx
    rw [hsuppC] at hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    have hx0' : ∀ j : Fin Tx.m, ι z ∉ (Tx.I j).support := fun j hj => by
      obtain rfl := hTxI j
      exact hx0 hj
    refine hdisj.notMem_of_mem_left hz (mem_sncLocus_restrict_of_isSNCAt hinv hES hTS z ?_)
    refine IsSNCAt.of_forall (isSNCAt_of_isSNCFamily hinv.2.2 (ι z))
      (fun o => o.elim none fun q => q.elim (fun _ => none) some) ?_ ?_
    · rintro (_ | j | j) hj
      · rfl
      · exact (hx0' j hj).elim
      · rfl
    · rintro (_ | j | j) (_ | j' | j') hj hj' h
      · rfl
      · exact (hx0' j' hj').elim
      · cases h
      · exact (hx0' j hj).elim
      · exact (hx0' j hj).elim
      · exact (hx0' j hj).elim
      · cases h
      · exact (hx0' j' hj').elim
      · simp only [Option.elim, Sum.elim_inr, Option.some.injEq] at h
        rw [h]
  -- the centre is a centre of the real tuple
  have hHC : ι.ker ≤ C := Scheme.Hom.le_ker_comp Z.subschemeι ι
  have hcons := isSNCFamily_cons_of_elim hinv.2.2
  have hZcons := Kollar.hasSNCWith_cons_of_hasSNCWith s (modEntry Tx i₀ K).E ι.ker hcons C hHC
    hc.2
  have hcx : Tx.IsTransformCentre s C := by
    refine ⟨hc.1, hasSNCWith_of_forall hZcons
      (fun j => if (j : ℕ) = i₀ then 0 else j.succ) ?_ ?_⟩
    · intro x hx j hj
      by_cases hji : (j : ℕ) = i₀
      · obtain rfl : j = ⟨i₀, hi₀'⟩ := Fin.ext hji
        rw [if_pos rfl, Fin.cons_zero]
        exact hst0 x (hCι hx)
      · rw [if_neg hji, Fin.cons_succ, hentry, if_neg hji]
    · intro x hx j j' hj hj' h
      by_cases hji : (j : ℕ) = i₀ <;> by_cases hji' : (j' : ℕ) = i₀
      · exact Fin.ext (hji.trans hji'.symm)
      · rw [if_pos hji, if_neg hji'] at h; exact absurd h.symm (Fin.succ_ne_zero _)
      · rw [if_neg hji, if_pos hji'] at h; exact absurd h (Fin.succ_ne_zero _)
      · rw [if_neg hji, if_neg hji'] at h; exact Fin.succ_injective _ h
  -- the centre misses the snc locus of the real tuple
  have hdx : Disjoint (C.support : Set W') Tx.sncLocus := by
    rw [Set.disjoint_left]
    intro x hx hxs
    have hxι := hCι hx
    have hx' := hx
    rw [hsuppC] at hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    have hnotK : ∀ j : Fin Tx.E.s, ι z ∈ ((modEntry Tx i₀ K).E.E j).support → (j : ℕ) ≠ i₀ :=
      fun j hj hji => by
        rw [hentry, if_pos hji] at hj
        exact hKx _ hxι hj
    refine hdisj.notMem_of_mem_left hz (mem_sncLocus_restrict_of_isSNCAt hinv hES hTS z ?_)
    refine IsSNCAt.of_forall ((mem_sncLocus_iff Tx _).1 hxs)
      (fun o => o.elim (Sum.inr ⟨i₀, hi₀'⟩) id) ?_ ?_
    · rintro (_ | j | j) hj
      · exact (hst0 _ hxι).symm
      · rfl
      · change IdealSheafData.stalk ((modEntry Tx i₀ K).E.E j) _ = _
        rw [hentry, if_neg (hnotK j hj)]
        rfl
    · rintro (_ | j | j) (_ | j' | j') hj hj' h
      · rfl
      · cases h
      · exact absurd (congrArg Fin.val (Sum.inr_injective h)).symm (hnotK j' hj')
      · cases h
      · simp only [Option.elim, id, Sum.inl.injEq] at h
        rw [h]
      · cases h
      · exact absurd (congrArg Fin.val (Sum.inr_injective h)) (hnotK j hj)
      · cases h
      · simp only [Option.elim, id, Sum.inr.injEq] at h
        rw [h]
  have hne : C ≠ ⊥ := by
    intro hC0
    have : IsIntegral W' := hvar.toIsIntegral
    exact hdx.notMem_of_mem_right (genericPoint_mem_sncLocus hTx)
      (by rw [hC0, Scheme.IdealSheafData.support_bot]; trivial)
  set π := blowUpToBase C with hπ
  set φ := eqToHom (congrArg blowUp h.symm) ≫ canonicalLift ι C with hφ
  have hφπ : φ ≫ π = blowUpToBase Z ≫ ι := canonicalLift_comp_blowUpToBase_map ι h
  have hrφ : Set.range φ = closure (π ⁻¹' (Set.range ι \ C.support)) := by
    rw [hφ, range_eqToHom_comp, range_canonicalLift_eq_closure]
  have hpTx : ∀ j, MMP.Mori.IsPureCodimOne (Tx.E.E j).support := fun j =>
    (hTx.2.2.2.2.2.1 j).2.1
  have hpK : MMP.Mori.IsPureCodimOne K.support := by
    have := (hinv.2.1.2.2.2.2.2.1 ⟨i₀, hi₀'⟩).2.1
    rwa [hentry, if_pos rfl] at this
  have hKC : Disjoint (p ⁻¹' R) C.support :=
    Set.disjoint_left.2 fun x hx hxC => hιR x (hCι hxC) hx
  have hcomp' : ∀ y, (π ≫ p) y = p (π y) := fun y => Scheme.Hom.comp_apply _ _ _
  refine ⟨hcx, hdx, ?_, isOrderedDivisorTuple_transform hTx hcx hne, hm,
    excSNC_transform hTx hB C hcx hCS h2, ⟨by change i₀ < Tx.E.s + 1; omega, ?_⟩, ?_, ?_, ?_⟩
  · refine (modEntry_transform Tx i₀ hi₀' _ C hKC hpTx hpK h2).trans ?_
    congr 3
  · change (((Tx.E.totalTransform C).E (Fin.castSucc ⟨i₀, hi₀'⟩)).support : Set (blowUp C)) = _
    rw [support_totalTransform_E_castSucc_of_codim _ C hC2, hsupp0, hrφ, Set.union_diff_distrib,
      Set.preimage_union, closure_union, sdiff_eq_left.2 hKC,
      ((hR.preimage p.continuous).preimage π.continuous).closure_eq]
    congr 1
  · rintro _ ⟨z', rfl⟩
    rw [← Category.assoc, hφπ, Category.assoc, Scheme.Hom.comp_apply]
    exact hpW ⟨_, rfl⟩
  · intro y hy
    have hy' : π y ∈ p ⁻¹' W := by
      change p (π y) ∈ W
      rw [← hcomp']
      exact hy
    by_cases hyC : π y ∈ (C.support : Set W')
    · right
      refine Set.mem_iUnion₂.2 ⟨Fin.last _, by
        have := hB.1; simp only [Fin.val_last]; omega, ?_⟩
      change y ∈ ((Tx.E.totalTransform C).E (Fin.last _)).support
      rw [totalTransform_E_last_of_codim _ hpTx C h2, ← SetLike.mem_coe,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hyC
    · rcases hpre hy' with h1 | h1
      · left
        rw [hrφ]
        exact subset_closure ⟨h1, hyC⟩
      · right
        obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 h1
        refine Set.mem_iUnion₂.2 ⟨Fin.castSucc j, by simpa using hj, ?_⟩
        change y ∈ ((Tx.E.totalTransform C).E (Fin.castSucc j)).support
        rw [← SetLike.mem_coe, support_totalTransform_E_castSucc_of_codim _ C hC2]
        exact subset_closure ⟨hyj, hyC⟩
  · rintro ⟨i, hi'⟩ hi y hyW
    have hiTx : i < Tx.E.s := lt_of_lt_of_le hi hB.1
    have hyW' : p (π y) ∉ W := by rw [← hcomp']; exact hyW
    have hyC : π y ∉ (C.support : Set W') := fun hyC => by
      obtain ⟨z, hz⟩ := hCι hyC
      apply hyW'
      have := hpW ⟨z, rfl⟩
      rwa [Scheme.Hom.comp_apply, hz] at this
    change y ∈ ((Tx.E.totalTransform C).E (Fin.castSucc ⟨i, hiTx⟩)).support ↔ _
    rw [← SetLike.mem_coe, support_totalTransform_E_castSucc_of_codim _ C hC2,
      mem_closure_preimage_diff_iff_of_notMem y hyC (Tx.E.E _).support.isClosed
        C.support.isClosed subset_rfl, hcomp']
    exact hover ⟨i, hiTx⟩ hi (π y) hyW'

/-- The intersection of an irreducible set with an open set meeting it is irreducible. -/
private theorem isIrreducible_inter_open {X : Type*} [TopologicalSpace X] {S O : Set X}
    (hS : IsIrreducible S) (hO : IsOpen O) (hne : (S ∩ O).Nonempty) : IsIrreducible (S ∩ O) := by
  refine ⟨hne, fun u v hu hv ⟨x, hxS, hxu⟩ ⟨y, hyS, hyv⟩ => ?_⟩
  obtain ⟨z, hzS, hzu, hzv⟩ := hS.2 (u ∩ O) (v ∩ O) (hu.inter hO) (hv.inter hO)
    ⟨x, hxS.1, hxu, hxS.2⟩ ⟨y, hyS.1, hyv, hyS.2⟩
  exact ⟨z, ⟨hzS, hzu.2⟩, hzu.1, hzv.1⟩

/-- In an snc family, a component of one entry lies in no other entry. -/
private theorem not_subset_of_mem_componentsOf_of_isSNCFamily {k : Type u} [Field k]
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X] {s : X ⟶ Spec (.of k)} {n : ℕ}
    {E : Fin n → X.IdealSheafData} (h : IsSNCFamily s E) {a b : Fin n} (hab : a ≠ b) {W : Set X}
    (hW : W ∈ componentsOf ((E a).support : Set X)) : ¬ W ⊆ ((E b).support : Set X) := by
  intro hsub
  let T'' : OrderedDivisorTuple X := ⟨0, Fin.elim0, ⟨n, E⟩⟩
  have hs : ∀ x, x ∈ T''.sncLocus := fun x => by
    rw [mem_sncLocus_iff]
    refine IsSNCAt.of_forall (isSNCAt_of_isSNCFamily h x) (Sum.elim Fin.elim0 id) ?_ ?_
    · rintro (j | i) _
      · exact j.elim0
      · rfl
    · rintro (j | i) (j' | i') _ _ hh
      · exact j.elim0
      · exact j.elim0
      · exact j'.elim0
      · exact congrArg Sum.inr hh
  have hd := disjoint_sncLocus_of_subset_support T'' (p := .inr a) (q := .inr b)
    (fun hh => hab (Sum.inr_injective hh)) hW hsub
  obtain ⟨x, hx⟩ := hW.1.1.nonempty
  exact hd.notMem_of_mem_left hx (hs x)

/-- The bad pairs are finitely many. -/
private theorem badPairs_finite {V : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    (T : OrderedDivisorTuple V) (s₀ : ℕ) : (badPairs T s₀).Finite := by
  have : IsNoetherian V := {}
  refine (Set.finite_iUnion fun i : Fin T.E.s => (Set.finite_singleton (i : ℕ)).prod
    (Aux.finite_and_cover_componentsOf (T.E.E i).support.isClosed).1).subset ?_
  rintro ⟨i, W⟩ ⟨hi, -, hW, -⟩
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, Set.mk_mem_prod rfl hW⟩

/-- **One step of Step 1**: resolving along one bad component `W` of an original boundary entry.
The real tuple becomes snc along the strict transform of `W`, and the bad components of the
transformed tuple correspond injectively to bad components of the tuple other than `W`. -/
private theorem exists_validS_badPairs_ncard_lt {k : Type u} [Field k] (n : ℕ)
    (IH : ∀ n' < n, ResolvableUpTo k n') {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (hdim : topologicalKrullDim V ≤ n) (hm : T.m = 1) (s₀ : ℕ) (hB : ExcSNC sV T s₀)
    (hC : NoBadInFirst T s₀) {q : ℕ × Set V} (hq : q ∈ badPairs T s₀) :
    ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ ExcSNC (B.toBase ≫ sV) (finalTuple B T) s₀ ∧
      NoBadInFirst (finalTuple B T) s₀ ∧
      (badPairs (finalTuple B T) s₀).ncard < (badPairs T s₀).ncard := by
  obtain ⟨i₀, W⟩ := q
  have hq' := hq
  obtain ⟨hi₀, hi₀s, hW, hWbad⟩ := hq
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : IsIntegral V := hvar.toIsIntegral
  have : CharZero k := hT.1
  have h0 : 0 < T.m := by omega
  have hs₀ : s₀ ≤ T.E.s := hB.1
  have hsncE := hT.2.2.2.2.2
  have hP : IsParamDivisor (T.E.E ⟨i₀, hi₀⟩) := isParamDivisor_of_isSNCFamily hsncE _
  obtain ⟨hWc, hRc, hsplit, hDst, hdisj⟩ := exists_split_component hP hW
  set R := ((T.E.E ⟨i₀, hi₀⟩).support : Set V) \ W with hRdef
  set D := Scheme.IdealSheafData.vanishingIdeal ⟨W, hWc⟩ with hDdef
  set K := Scheme.IdealSheafData.vanishingIdeal (⟨R, hRc⟩ : TopologicalSpace.Closeds V)
    with hKdef
  have hDsupp : (D.support : Set V) = W := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hKsupp : (K.support : Set V) = R := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hrangeD : Set.range D.subschemeι = W := by
    rw [Scheme.IdealSheafData.range_subschemeι, hDsupp]
  have hKst : ∀ x ∈ R, IdealSheafData.stalk K x = IdealSheafData.stalk (T.E.E ⟨i₀, hi₀⟩) x := by
    intro x hx
    have h := congrArg (fun I => IdealSheafData.stalk I x) hsplit
    rw [h, IdealSheafData.stalk_mul, (IdealSheafData.stalk_eq_top_iff_notMem_support D x).2
      (by rw [← SetLike.mem_coe, hDsupp]; exact hx.2), Ideal.top_mul]
  set T₁ := modEntry T i₀ K with hT₁def
  have hentry : ∀ j : Fin T.E.s, T₁.E.E j = if (j : ℕ) = i₀ then K else T.E.E j := fun j => rfl
  have hWK : ∀ x ∈ W, ∀ j : Fin T.E.s, (j : ℕ) = i₀ → x ∉ (T₁.E.E j).support := by
    intro x hx j hj hxj
    rw [hentry, if_pos hj, ← SetLike.mem_coe, hKsupp] at hxj
    exact hxj.2 hx
  -- `W` together with the modified boundary is snc
  have hD : IsSNCFamily sV fun o : Option (Fin T₁.E.s) => o.elim D T₁.E.E := by
    refine isSNCFamily_of_forall_isSNCAt fun x => IsSNCAt.of_forall
      (isSNCAt_of_isSNCFamily hsncE x) (fun o => o.elim ⟨i₀, hi₀⟩ id) ?_ ?_
    · rintro (_ | j) hj
      · have hxW : x ∈ W := by rw [← hDsupp]; exact hj
        exact hDst x hxW
      · by_cases hji : (j : ℕ) = i₀
        · obtain rfl : j = ⟨i₀, hi₀⟩ := Fin.ext hji
          have hxK : x ∈ (K.support : Set V) := by
            have := hj
            change x ∈ (T₁.E.E ⟨i₀, hi₀⟩).support at this
            rwa [hentry, if_pos rfl] at this
          rw [hKsupp] at hxK
          change IdealSheafData.stalk (T₁.E.E ⟨i₀, hi₀⟩) x = _
          rw [hentry, if_pos rfl]
          exact hKst x hxK
        · change IdealSheafData.stalk (T₁.E.E j) x = _
          rw [hentry, if_neg hji]
          rfl
    · rintro (_ | j) (_ | j') hj hj' h
      · rfl
      · have hxW : x ∈ W := by rw [← hDsupp]; exact hj
        exact (hWK x hxW j' (congrArg Fin.val h).symm hj').elim
      · have hxW : x ∈ W := by rw [← hDsupp]; exact hj'
        exact (hWK x hxW j (congrArg Fin.val h) hj).elim
      · exact congrArg some h
  have hE₁ : IsSNCFamily sV T₁.E.E := isSNCFamily_comp hD some (Option.some_injective _)
  have hT₁ : IsOrderedDivisorTuple sV T₁ := by
    refine ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, fun j => ⟨(hE₁.1 j).1,
      isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ fun y hy => ?_⟩, hE₁⟩
    obtain ⟨m, w, c, hw, hwc, -⟩ := hE₁.2 y
    exact ⟨m, w, c ⟨j, hy⟩, hw, hwc ⟨j, hy⟩⟩
  have hWi : IsIrreducible W := hW.1.1
  have hI₁ : ∀ j, ¬ W ⊆ ((T₁.I j).support : Set V) := fun j hsub => by
    have hj : (j : ℕ) = 0 := by have := j.isLt; change (j : ℕ) < T.m at this; omega
    obtain rfl : j = ⟨0, h0⟩ := Fin.ext hj
    exact hC h0 _ hq' hsub
  have hTD := isOrderedDivisorTuple_restrictTuple hT₁ hWc hWi hD hI₁
  have hWne : W ≠ Set.univ := by
    intro h
    have hη : genericPoint V ∈ W := h ▸ Set.mem_univ _
    exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor _ (hT.2.2.2.2.1 _).2
      (Stacks.Chow.genericPoint_mem_genericPoints V) (hW.1.2 hη)
  obtain ⟨n', hn', hdn'⟩ := exists_lt_topologicalKrullDim_subscheme_le sV hWc hWi hWne hdim
  have hres := IH n' hn' _ _ hTD hdn'
  have hWR : Disjoint W R := Set.disjoint_sdiff_right
  have hQ0 : Step1Pred k s₀ i₀ W R hRc T hs₀ D.subschemeι sV (𝟙 V) T₁
      (T₁.E.comap D.subschemeι) T := by
    refine ⟨rfl, hT, hm, hB, ⟨hi₀, ?_⟩, ?_, ?_, fun i hi y _ => Iff.rfl⟩
    · rw [hrangeD]
      exact (Set.union_diff_cancel hW.1.2).symm
    · rw [Category.comp_id, hrangeD]
    · intro x hx
      left
      rw [hrangeD]
      exact hx
  obtain ⟨B', S', ι', -, -, hVS, hV, hinv', hpt, -, -, ES, hQf⟩ :=
    exists_validS_restriction_step sV T₁ hT₁ D hD hTD hres _
      (liftStep_step1Pred s₀ i₀ W R hRc hWR T hs₀) T hQ0
  obtain ⟨hQ1, hTf, hmf, hBf, ⟨hi₀f, hsuppf⟩, hpWf, hpref, hoverf⟩ := hQf
  rw [Category.comp_id] at hQ1 hsuppf hpWf hpref hoverf
  set Tf := finalTuple B' T with hTfdef
  set p := B'.toBase with hpdef
  have hVT : Valid sV T.sncLocus B' T := ValidS.valid B' hVS subset_rfl
  have hvar' : AlgebraicGeometry.IsVariety k (p ≫ sV) := hTf.2.1
  have : IsLocallyNoetherian B'.target := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sV)
  have : CompactSpace B'.target := QuasiCompact.compactSpace_of_compactSpace (p ≫ sV)
  have : IsClosedImmersion ι' := hinv'.1
  have hιred' : IsReduced ι'.ker.subscheme := (hinv'.2.2.1 none).1
  have hιR' : ∀ x ∈ Set.range ι', p x ∉ R := by
    rintro _ ⟨z, rfl⟩ hz
    have := hpWf ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply] at this
    exact hWR.notMem_of_mem_left this hz
  have hst' : ∀ x ∈ Set.range ι', IdealSheafData.stalk (Tf.E.E ⟨i₀, hi₀f⟩) x =
      IdealSheafData.stalk ι'.ker x := fun x hx =>
    stalk_eq_stalk_ker_of_support_eq ι' hιred' _ (hTf.2.2.2.2.1 _).1 p hRc hsuppf hιR' hx
  set Kf := Scheme.IdealSheafData.vanishingIdeal
    (⟨p ⁻¹' R, hRc.preimage p.continuous⟩ : TopologicalSpace.Closeds B'.target) with hKf
  have hentryf : ∀ j : Fin Tf.E.s, (modEntry Tf i₀ Kf).E.E j =
      if (j : ℕ) = i₀ then Kf else Tf.E.E j := fun j => rfl
  -- the real tuple is snc along the strict transform of `W`
  have hsncι : ∀ z, ι' z ∈ Tf.sncLocus := by
    intro z
    have h := hpt z
    rw [hQ1] at h
    rw [mem_sncLocus_iff]
    refine IsSNCAt.of_forall h (Sum.elim (fun j => some (Sum.inl j))
      fun j => if (j : ℕ) = i₀ then none else some (Sum.inr j)) ?_ ?_
    · rintro (j | j) hj
      · rfl
      · by_cases hji : (j : ℕ) = i₀
        · obtain rfl : j = ⟨i₀, hi₀f⟩ := Fin.ext hji
          change IdealSheafData.stalk (Tf.E.E ⟨i₀, hi₀f⟩) _ = IdealSheafData.stalk
            (Option.elim (if ((⟨i₀, hi₀f⟩ : Fin Tf.E.s) : ℕ) = i₀ then none else
              some (Sum.inr ⟨i₀, hi₀f⟩)) ι'.ker (modEntry Tf i₀ Kf).divisors) _
          rw [if_pos rfl]
          exact hst' _ ⟨z, rfl⟩
        · change IdealSheafData.stalk (Tf.E.E j) _ = IdealSheafData.stalk
            (Option.elim (if (j : ℕ) = i₀ then none else some (Sum.inr j)) ι'.ker
              (modEntry Tf i₀ Kf).divisors) _
          rw [if_neg hji]
          change _ = IdealSheafData.stalk ((modEntry Tf i₀ Kf).E.E j) _
          rw [hentryf, if_neg hji]
    · rintro (j | j) (j' | j') hj hj' h
      · simp only [Sum.elim_inl, Option.some.injEq, Sum.inl.injEq] at h
        rw [h]
      · by_cases h2 : (j' : ℕ) = i₀ <;> simp [h2] at h
      · by_cases h2 : (j : ℕ) = i₀ <;> simp [h2] at h
      · by_cases h1 : (j : ℕ) = i₀ <;> by_cases h2 : (j' : ℕ) = i₀
        · exact congrArg Sum.inr (Fin.ext (h1.trans h2.symm))
        · simp [h1, h2] at h
        · simp [h1, h2] at h
        · simp only [Sum.elim_inr, if_neg h1, if_neg h2, Option.some.injEq, Sum.inr.injEq] at h
          rw [h]
  -- the composite is an isomorphism off `W`
  obtain ⟨U, hU, hUiso⟩ := exists_isIso_of_valid B' sV _ T₁ hV
  let Wc : V.Opens := ⟨Wᶜ, hWc.isOpen_compl⟩
  haveI : IsIso (p ∣_ Wc) :=
    isIso_restrict_of_le p (V := U) fun x hx => hU (by rwa [hrangeD])
  have hQsnc : ∀ y, p y ∈ T.sncLocus → y ∈ Tf.sncLocus := fun y hy =>
    preimage_subset_sncLocus_of_valid B' hVT subset_rfl hy
  have hsuppI := support_finalTuple_subset B' T ⟨0, h0⟩
  have hsncEf := hTf.2.2.2.2.2
  -- the bad components of the final tuple come from bad components of `T` other than `W`
  have key : ∀ q'' ∈ badPairs Tf s₀, ∃ W₀, (q''.1, W₀) ∈ badPairs T s₀ ∧ W₀ ≠ W ∧
      q''.2 = closure (p ⁻¹' (W₀ ∩ Wᶜ)) ∧
      (∀ h0' : 0 < Tf.m, q''.2 ⊆ (Tf.I ⟨0, h0'⟩).support → W₀ ⊆ (T.I ⟨0, h0⟩).support) := by
    rintro ⟨i, W''⟩ ⟨hi, his, hW'', hbad''⟩
    have hiT : i < T.E.s := lt_of_lt_of_le his hs₀
    have hnotW : ¬ W'' ⊆ p ⁻¹' W := by
      intro hsub
      have hsub' := hsub.trans hpref
      have hBc : IsClosed (⋃ (j : Fin Tf.E.s) (_ : s₀ ≤ (j : ℕ)),
          ((Tf.E.E j).support : Set B'.target)) :=
        isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ =>
          (Tf.E.E j).support.isClosed
      rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hW''.1.1.2) _ _
        ι'.isClosedEmbedding.isClosed_range hBc hsub' with h1 | h1
      · exact hbad'' (h1.trans fun _ ⟨z, hz⟩ => hz ▸ hsncι z)
      · obtain ⟨_, hz, hYz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW''.1.1
          ((Finset.univ.filter fun j : Fin Tf.E.s => s₀ ≤ (j : ℕ)).image
            fun j => ((Tf.E.E j).support : Set B'.target))
          (fun z hz => by
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
            exact (Tf.E.E j).support.isClosed)
          (by
            intro x hx
            obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (h1 hx)
            exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image.2
              ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, rfl⟩), hxj⟩)
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hz
        have hj' := (Finset.mem_filter.1 hj).2
        refine not_subset_of_mem_componentsOf_of_isSNCFamily hsncEf (a := ⟨i, hi⟩) (b := j)
          (fun hh => ?_) hW'' hYz
        have := congrArg Fin.val hh
        change i = (j : ℕ) at this
        omega
    have hO : IsOpen (p ⁻¹' Wᶜ) := hWc.isOpen_compl.preimage p.continuous
    have hne : (W'' ∩ p ⁻¹' Wᶜ).Nonempty := by
      by_contra hn
      exact hnotW fun y hy => Classical.byContradiction fun hyW => hn ⟨y, hy, hyW⟩
    have hU'' := isIrreducible_inter_open hW''.1.1 hO hne
    have hdense : W'' ⊆ closure (W'' ∩ p ⁻¹' Wᶜ) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hW''.1.1.2 hO hne
    have hiTi : ∀ y ∈ W'' ∩ p ⁻¹' Wᶜ, p y ∈ ((T.E.E ⟨i, hiT⟩).support : Set V) := fun y hy =>
      (hoverf ⟨i, hi⟩ his y hy.2).1 (hW''.1.2 hy.1)
    obtain ⟨W₀, hW₀, hsubW₀⟩ := exists_mem_componentsOf_superset
      (hU''.image p p.continuous.continuousOn) (Set.image_subset_iff.2 hiTi)
    have hW₀c : IsClosed W₀ :=
      Aux.isClosed_of_mem_componentsOf (T.E.E ⟨i, hiT⟩).support.isClosed hW₀
    obtain ⟨y₀, hy₀⟩ := hne
    have hy₀W₀ : p y₀ ∈ W₀ := hsubW₀ ⟨y₀, hy₀, rfl⟩
    have hne₀ : (W₀ ∩ Wᶜ).Nonempty := ⟨p y₀, hy₀W₀, hy₀.2⟩
    have hW₀' := isIrreducible_inter_open hW₀.1.1 hWc.isOpen_compl hne₀
    have hpre₀ : IsIrreducible (p ⁻¹' (W₀ ∩ Wᶜ)) :=
      isIrreducible_preimage_of_isIso_restrict p Wc hW₀' Set.inter_subset_right
    have hpreE : p ⁻¹' (W₀ ∩ Wᶜ) ⊆ ((Tf.E.E ⟨i, hi⟩).support : Set _) := fun y hy =>
      (hoverf ⟨i, hi⟩ his y hy.2).2 (hW₀.1.2 hy.1)
    have hWhat : W'' = closure (p ⁻¹' (W₀ ∩ Wᶜ)) := by
      have h1 : W'' ⊆ closure (p ⁻¹' (W₀ ∩ Wᶜ)) :=
        hdense.trans (closure_mono fun y hy => ⟨hsubW₀ ⟨y, hy, rfl⟩, hy.2⟩)
      exact le_antisymm h1
        (hW''.2 ⟨hpre₀.closure, closure_minimal hpreE (Tf.E.E _).support.isClosed⟩ h1)
    refine ⟨W₀, ⟨hiT, his, hW₀, fun hsnc => hbad'' fun y hy => ?_⟩, fun he => ?_, hWhat,
      fun h0' hsub => ?_⟩
    · rw [hWhat] at hy
      have hy' : y ∈ p ⁻¹' W₀ :=
        closure_minimal (fun y hy => hy.1) (hW₀c.preimage p.continuous) hy
      exact hQsnc y (hsnc hy')
    · exact hy₀.2 (he ▸ hy₀W₀)
    · have h1 : W₀ ∩ Wᶜ ⊆ (T.I ⟨0, h0⟩).support := by
        intro x hx
        obtain ⟨y, rfl⟩ := mem_range_of_isIso_restrict p Wc (x := x) hx.2
        have hy : y ∈ W'' := by rw [hWhat]; exact subset_closure hx
        exact hsuppI (hsub hy)
      exact (subset_closure_inter_of_isPreirreducible_of_isOpen hW₀.1.1.2 hWc.isOpen_compl
        hne₀).trans (closure_minimal h1 (T.I _).support.isClosed)
  classical
  choose! f hf using key
  have hfin := badPairs_finite T s₀
  refine ⟨B', hVS, hBf, ?_, ?_⟩
  · intro h0' q'' hq'' hsub
    obtain ⟨hb, -, -, himp⟩ := hf q'' hq''
    exact hC h0 _ hb (himp h0' hsub)
  · calc (badPairs Tf s₀).ncard ≤ (badPairs T s₀ \ {(i₀, W)}).ncard :=
          Set.ncard_le_ncard_of_injOn (fun q'' => (q''.1, f q''))
            (fun q'' hq'' => ⟨(hf q'' hq'').1, fun he =>
              (hf q'' hq'').2.1 (congrArg Prod.snd he)⟩)
            (fun q₁ h₁ q₂ h₂ he => by
              have e1 := congrArg Prod.fst he
              have e2 := congrArg Prod.snd he
              simp only at e1 e2
              exact Prod.ext e1 ((hf q₁ h₁).2.2.1.trans (by rw [e2]; exact (hf q₂ h₂).2.2.1.symm)))
            (hfin.subset Set.diff_subset)
      _ < _ := Set.ncard_diff_singleton_lt_of_mem hq' hfin

/-- **Step 1, the loop**: the bad components are resolved one at a time. -/
private theorem resolvable_of_excSNC {k : Type u} [Field k] (n : ℕ)
    (IH : ∀ n' < n, ResolvableUpTo k n') (s₀ : ℕ) :
    ∀ (N : ℕ) {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V),
      IsOrderedDivisorTuple sV T → topologicalKrullDim V ≤ n → T.m = 1 → ExcSNC sV T s₀ →
      NoBadInFirst T s₀ → (badPairs T s₀).ncard = N → Resolvable sV T := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro V sV T hT hdim hm hB hC hNc
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  by_cases hemp : badPairs T s₀ = ∅
  · exact ⟨.nil V, trivial, sncLocus_eq_univ_of_badPairs_eq_empty hm hB hemp⟩
  · obtain ⟨q, hq⟩ := Set.nonempty_iff_ne_empty.2 hemp
    obtain ⟨B, hBv, hB', hC', hlt⟩ :=
      exists_validS_badPairs_ncard_lt n IH sV T hT hdim hm s₀ hB hC hq
    exact resolvable_of_validS hT B hBv fun hT' hd =>
      ihN _ (hNc ▸ hlt) (B.toBase ≫ sV) _ hT' (hd.trans hdim) (by rw [finalTuple_m, hm])
        hB' hC' rfl

/-- **Step 1, second part**: a one-ideal tuple whose first divisor is smooth and has no component
in the boundary is resolved by processing the boundary components one at a time. -/
private theorem resolvable_one_of_not_subset {k : Type u} [Field k] (n : ℕ)
    (IH : ∀ n' < n, ResolvableUpTo k n') {V : Scheme.{u}} (sV : V ⟶ Spec (.of k))
    (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (hdim : topologicalKrullDim V ≤ n) (hm : T.m = 1) (h0 : 0 < T.m)
    (hS : FirstIdealData sV T h0)
    (hE : ∀ W ∈ componentsOf ((T.I ⟨0, h0⟩).support : Set V), ∀ i,
      ¬ W ⊆ ((T.E.E i).support : Set V)) :
    Resolvable sV T :=
  resolvable_of_excSNC n IH T.E.s _ sV T hT hdim hm (excSNC_of_firstIdealData hT h0 hS)
    (noBadInFirst_of_firstIdealData hT h0 hS hE) rfl

/-- **Step 1**: `(V, I_1, E)` can be made snc everywhere. -/
private theorem exists_valid_isSNCFamily_cons {k : Type u} [Field k] (n : ℕ)
    (IH : ∀ n' < n, ResolvableUpTo k n') {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T)
    (hdim : topologicalKrullDim V ≤ n) (h0 : 0 < T.m) (hS : FirstIdealData sV T h0) :
    ∃ B : ClosedBlowupSequence V, ValidS sV B T ∧ ∃ h : 0 < (finalTuple B T).m,
      IsSNCFamily (B.toBase ≫ sV)
        (Fin.cons (α := fun _ => B.target.IdealSheafData) ((finalTuple B T).I ⟨0, h⟩)
          (finalTuple B T).E.E) := by
  have hvar : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : CharZero k := hT.1
  let T₁ : OrderedDivisorTuple V := ⟨1, fun _ => T.I ⟨0, h0⟩, T.E⟩
  have hT₁ : IsOrderedDivisorTuple sV T₁ :=
    ⟨hT.1, hT.2.1, hT.2.2.1, fun _ => hT.2.2.2.1 _, hT.2.2.2.2⟩
  obtain ⟨B, hB, hsnc⟩ := resolvable_one_of_cartier n
    (fun sV' T' hT' hdim' hm' h' hS' hE' =>
      resolvable_one_of_not_subset n IH sV' T' hT' hdim' hm' h' hS' hE') _ sV T₁ hT₁ hdim rfl
    Nat.one_pos ⟨hS.reduced, hS.param⟩ rfl
  have hBT : ValidS sV B T := validS_of_validS_comp B sV T (fun _ => T.I ⟨0, h0⟩)
    (fun _ => ⟨0, h0⟩) (fun a b _ => Subsingleton.elim a b) (fun _ => rfl) hB
  have hBw := ValidS.valid B hBT subset_rfl
  have hT' := (isOrderedDivisorTuple_finalTuple B hT hBw ⟨_, genericPoint_mem_sncLocus hT⟩).1
  have hvar' : AlgebraicGeometry.IsVariety k (B.toBase ≫ sV) := hT'.2.1
  have : IsLocallyNoetherian B.target := LocallyOfFiniteType.isLocallyNoetherian (B.toBase ≫ sV)
  have h' : 0 < (finalTuple B T).m := by rw [finalTuple_m]; exact h0
  refine ⟨B, hBT, h', isSNCFamily_of_forall_isSNCAt fun y => ?_⟩
  have hy : y ∈ (finalTuple B T₁).sncLocus := hsnc ▸ Set.mem_univ y
  exact isSNCAt_cons_of_mem_sncLocus (finalTuple B T₁) (by rw [finalTuple_m]; exact Nat.one_pos) hy
    ((finalTuple_I B T ⟨0, h0⟩).trans (finalTuple_I B T₁ ⟨0, Nat.one_pos⟩).symm)
    (finalTuple_E_congr B T₁ T rfl)

/-- **Main induction**, on the dimension and then on the number of ideals. -/
private theorem resolvableUpTo {k : Type u} [Field k] (n : ℕ) : ResolvableUpTo k n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  have key : ∀ m : ℕ, ∀ {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V),
      IsOrderedDivisorTuple sV T → topologicalKrullDim V ≤ n → T.m = m → Resolvable sV T := by
    intro m
    induction m with
    | zero =>
      intro V sV T hT _ hm
      exact ⟨.nil V, trivial, sncLocus_eq_univ_of_m_eq_zero hT hm⟩
    | succ m ihm =>
      intro V sV T hT hdim hm
      have h0 : 0 < T.m := by omega
      obtain ⟨B₀, hB₀, h₀, hS₀⟩ := exists_valid_firstIdealData sV T hT h0
      refine resolvable_of_validS hT B₀ hB₀ fun hT₀ hdim₀ => ?_
      set V₀ := B₀.target
      set T₀ := finalTuple B₀ T
      have hdim₀' : topologicalKrullDim V₀ ≤ n := hdim₀.trans hdim
      obtain ⟨B₁, hB₁, h₁, hS₁⟩ :=
        exists_valid_isSNCFamily_cons n IH (B₀.toBase ≫ sV) T₀ hT₀ hdim₀' h₀ hS₀
      refine resolvable_of_validS hT₀ B₁ hB₁ fun hT₁ hdim₁ => ?_
      set V₁ := B₁.target
      set T₁ := finalTuple B₁ T₀
      have hdim₁' : topologicalKrullDim V₁ ≤ n := hdim₁.trans hdim₀'
      have hm₁ : T₁.m = m + 1 := by simp only [finalTuple_m, T₁, T₀]; omega
      refine resolvable_of_isSNCFamily_cons_of_componentsOf n (m + 1)
        (fun sV₂ T₂ hT₂ hdim₂ hm₂ h₂ hS₂ hI₂ => ?_) _ _ T₁ hT₁ hdim₁' hm₁ h₁ hS₁ rfl
      refine resolvable_of_isSNCFamily_cons n IH (m + 1)
        (fun sV₃ T₃ hT₃ hdim₃ hm₃ h₃ hS₃ => ?_) _ _ T₂ hT₂ hdim₂ hm₂ h₂ hS₂
        (fun j hj W hW => hI₂ j hj W hW.1) rfl
      refine resolvable_of_resolvable_dropFirst _ _ hT₃ h₃ hS₃ ?_
      refine ihm _ _ ⟨hT₃.1, hT₃.2.1, hT₃.2.2.1, fun j => hT₃.2.2.2.1 _, hT₃.2.2.2.2⟩
        hdim₃ ?_
      simp only [dropFirst, hm₃]
      omega
  intro V sV T hT hdim
  exact key T.m sV T hT hdim rfl

/-- Every ordered divisor tuple over a field is resolvable. -/
private theorem resolvable_of_isOrderedDivisorTuple {k : Type u} [Field k] {V : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V) (hT : IsOrderedDivisorTuple sV T) :
    Resolvable sV T := by
  have : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sV
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim V ≤ n := by
    induction h : topologicalKrullDim V using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h htop
      | coe n => exact ⟨n, le_rfl⟩
  exact resolvableUpTo n sV T hT hn

end DivisorTupleSncResolution

namespace MMP.Resolution

open CategoryTheory AlgebraicGeometry MMP.Resolution
open MMP.Resolution.Internal.TupleRestrictionLift MMP.Resolution.TupleResolutionAux
open DivisorTupleSncResolution

universe u

/-- **Snc-preserving resolution of an ordered divisor tuple.** For an ordered divisor tuple
`T = ((I_1, …, I_m), E)` on `V` over `k`, there is a blow-up sequence `B` starting with `V`
whose centres are, stage by stage, centres of order-one transformations of the current tuple,
each disjoint from the inverse image of `T.sncLocus`, such that the final tuple `T_r` on `V_r`
has snc locus all of `V_r`, and the composite `p : V_r ⟶ V` restricts to an isomorphism over
some open `U` containing `T.sncLocus`. -/
@[mmp "thm_mmp_divisor_tuple_resolution"]
public theorem OrderedDivisorTuple.exists_transform_sncLocus_eq_univ {k : Type u} [Field k]
    {V : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (T : OrderedDivisorTuple V)
    (hT : IsOrderedDivisorTuple sV T) :
    ∃ B : ClosedBlowupSequence V,
      ClosedBlowupSequence.rec
        (motive := fun S _ => (S ⟶ V) → OrderedDivisorTuple S → Prop)
        (fun _ p T' => T'.sncLocus = Set.univ ∧
          ∃ U : V.Opens, T.sncLocus ⊆ U ∧ IsIso (p ∣_ U))
        (fun Z _ ih p T' => T'.IsTransformCentre (p ≫ sV) Z ∧
          Disjoint (Z.support : Set _) (p ⁻¹' T.sncLocus) ∧
          ih (blowUpToBase Z ≫ p) (T'.transform Z))
        B (𝟙 V) T := by
  obtain ⟨B, hBS, hsnc⟩ := resolvable_of_isOrderedDivisorTuple sV T hT
  have : AlgebraicGeometry.IsVariety k sV := hT.2.1
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have hB : Valid sV T.sncLocus B T := ValidS.valid B hBS subset_rfl
  refine ⟨B, (rec_iff sV T.sncLocus (fun p T' => T'.sncLocus = Set.univ ∧
    ∃ U : V.Opens, T.sncLocus ⊆ U ∧ IsIso (p ∣_ U)) B (𝟙 V) T).2 ?_⟩
  simp only [Category.id_comp, Scheme.Hom.id_base, TopCat.coe_id, Set.preimage_id]
  obtain ⟨U, hU, hiso⟩ := exists_isIso_of_valid B sV _ T hB
  exact ⟨hB, hsnc, U, hU, by rwa [Category.comp_id]⟩

end MMP.Resolution
