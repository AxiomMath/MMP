module
public import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
public import MMP.AlgebraicGeometry.Resolution.Blowup.StrictTransform
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart

/-!
# Two steps of Kollár's resolution by order reduction

This file proves two results used in Kollár's resolution of singularities.

The first concerns a blow-up inside a smooth hypersurface. Let `X` be a smooth variety over a
field `k` of characteristic zero, `E = (E^1, …, E^s)` an ordered simple normal crossing divisor
and `H ⊆ X` a smooth hypersurface with `H + ∑ᵢ E^i` a simple normal crossing divisor. Let
`Z ⊆ H` be a smooth closed subscheme having simple normal crossings with `E`, no irreducible
component of which is an irreducible component of `H`, and let `π : B_ZX → X` be the blow-up.
Then the birational transform `H₁ = B_{Z ∩ H}H ⊆ B_ZX` of `H`, together with the entries of the
total transform `π⁻¹_tot(E)`, is a simple normal crossing divisor on `B_ZX`. Indeed `Z` has
simple normal crossings with `H + ∑ᵢ E^i`, so the transforms of its members together with the
exceptional divisor form an snc family; `H₁` is the transform of `H` because `H` is reduced,
and every component of `Z` has codimension at least two, being properly contained in a
component of `H`.

The second is Step 1 of order reduction for marked triples (Kollár 3.111). Let `𝓑` be an
order-reduction family on dimensions `a, …, b`, `m ≥ 1`, and `(X, I, m, E)` a marked triple
with `a ≤ dim X ≤ b`. The Step-1 sequence, which repeatedly applies `𝓑_{dim X, μ}` to
`(X, N(I), E)` for `μ = maxord N(I) ≥ m`, is a smooth blow-up sequence of order `≥ m` starting
with `(X, I, m, E)`, and at its end `(X_1, I_1, m, E_1)` the nonmonomial part satisfies
`maxord N(I_1) < m`. Along one round the nonmonomial part of the transform of `(I, m)` is the
controlled transform of `N(I)`, and the values `μ` strictly decrease.

## Main results

* `MMP.Resolution.Kollar.isSNCFamily_cons_ker_canonicalLift_totalTransform`: the transform of
  `H + ∑ᵢ E^i` under a blow-up inside `H` is snc.
* `MMP.Resolution.isOrderGeMarkedTripleSeq_bmoStepOne`: the Step-1 sequence is of order `≥ m`
  and ends with `maxord N(I₁) < m`.

## Implementation notes

The subscheme `H₁` of `B_ZX` is the closed subscheme cut out by the kernel of the canonical
lift `B_{Z·𝒪_H}H → B_ZX` of the inclusion `H → X` (`MMP.Resolution.canonicalLift`), a closed
immersion. That `H` is a smooth hypersurface is part of the simple normal crossing condition on
`H + ∑ᵢ E^i`, which asks each entry to be reduced, smooth over `k` and of pure codimension one.

The marking `m` of the Step-1 sequence is an explicit argument, as it is for
`MMP.Resolution.bmoStepOne`; the marking field of the marked triple plays no role. A round
applies `𝓑_{dim X, μ}` with `μ = (maxord N(I)).toNat`, so the maximal order of the ideal of a
triple must be finite. This follows from upper semicontinuity of the order in characteristic
zero: at a point `x` with `ord_x I = r`, choose a regular system of parameters `t₁, …, t_d` and
derivations `δᵢ` with `δᵢ(t_j) = δᵢⱼ` near `x`. The Euler identity
`∑ tᵢ δᵢ f ≡ r f (mod 𝔪^{r+1})` for `f ∈ 𝔪^r` gives a word of at most `r` of the `δᵢ` sending a
section `f` of `I` with `f ∉ 𝔪_x^{r+1}` to a unit at `x`. Since a derivation maps `𝔪_y^{n+1}`
into `𝔪_y^n`, this gives `ord_y I ≤ r` on the open set where that unit is invertible, and
quasi-compactness bounds the order on all of `X`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, proof of Cor. 3.85 and 3.111, Step 1]
-/

universe u

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Resolution.Kollar

/-- The complement of an effective Cartier divisor is dense. -/
private theorem dense_compl_support_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Dense (D.support.compl : Set Y) := by
  have : IsAffineHom (Scheme.Opens.ι D.support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι D.support.compl) :=
    (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      D.support.compl).mp
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
  have hdense := (Scheme.Opens.ι D.support.compl).denseRange
  rwa [DenseRange, Scheme.Opens.range_ι] at hdense

/-- For a closed immersion `j : S ⟶ X` of a reduced scheme and a closed subscheme `Z ⊆ X`, the
canonical lift `B_{j⁻¹Z}S ⟶ B_ZX` cuts out the closure of `π⁻¹(S ∖ Z)` with its reduced
structure. -/
private theorem ker_canonicalLift_eq_vanishingIdeal {X S : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] [IsReduced S] (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = Scheme.IdealSheafData.vanishingIdeal
        (.closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)))) := by
  set f := canonicalLift j Z with hf
  set T : Set (blowUp Z) := blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))
  have hsq : ∀ v, blowUpToBase Z (f v) = j (blowUpToBase (Z.comap j) v) := fun v ↦ by
    rw [← Scheme.Hom.comp_apply, hf, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  have : IsReduced (blowUp (Z.comap j)) := isReduced_blowUp (Z.comap j)
  have : IsClosedImmersion f := Bridges.isClosedImmersion_canonicalLift j Z
  set V : Set (blowUp (Z.comap j)) :=
    blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ with hV
  have hVdense : closure V = Set.univ := by
    have h := dense_compl_support_of_isEffectiveCartierDivisor
      ((Z.comap j).comap (blowUpToBase (Z.comap j)))
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (Z.comap j))
    have hV' : (((Z.comap j).comap (blowUpToBase (Z.comap j))).support.compl :
        Set (blowUp (Z.comap j))) = V := by
      ext v
      simp [hV, Scheme.IdealSheafData.support_comap]
    rw [← hV']
    exact h.closure_eq
  have himage : f '' V = T := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨_, (hsq v).symm⟩, ?_⟩
      rw [hsq v]
      simpa [hV] using hv
    · rintro ⟨⟨s, hs⟩, hyZ⟩
      have hs' : s ∉ ((Z.comap j).support : Set S) := by
        simpa [hs] using hyZ
      obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs'
      refine ⟨v, by simpa [hV, hv] using hs', ?_⟩
      have hfv : blowUpToBase Z (f v) = blowUpToBase Z y := by rw [hsq v, hv, hs]
      exact blowUpToBase_injective_of_notMem_support Z (by rwa [hfv]) hfv
  have hrange : Set.range f = closure T := by
    apply subset_antisymm
    · rw [← Set.image_univ, ← hVdense, ← himage]
      exact image_closure_subset_closure_image f.continuous
    · rw [← himage]
      exact closure_minimal (Set.image_subset_range _ _) f.isClosedEmbedding.isClosed_range
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range f, hrange]
  congr 1
  exact TopologicalSpace.Closeds.ext (by
    rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure,
      closure_closure])

/-- Let `H` be a closed subset of pure codimension one of a noetherian scheme and `Z ⊆ H` a closed
subset no irreducible component of which is an irreducible component of `H`. Then every
irreducible component of `Z` has codimension at least two. -/
private theorem two_le_codimension_of_mem_componentsOf {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    {H Z : TopologicalSpace.Closeds X} (hH1 : Mori.IsPureCodimOne H) (hZH : (Z : Set X) ⊆ H)
    (hcomp : ∀ W ∈ componentsOf (Z : Set X), W ∉ componentsOf (H : Set X)) {W : Set X}
    (hW : W ∈ componentsOf (Z : Set X)) : 2 ≤ codimension (irreducibleClosure hW.1.1) := by
  classical
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf Z.isClosed hW
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf H.isClosed
  obtain ⟨H', hH'mem, hWH'⟩ : ∃ H' ∈ componentsOf (H : Set X), W ⊆ H' := by
    obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1 hfin.toFinset
      (fun z hz => Aux.isClosed_of_mem_componentsOf H.isClosed (hfin.mem_toFinset.mp hz))
      (by rw [hfin.coe_toFinset]; exact hW.1.2.trans (hZH.trans hcov))
    exact ⟨z, hfin.mem_toFinset.mp hz, hWz⟩
  have hne : W ≠ H' := fun h => hcomp W hW (h ▸ hH'mem)
  have hH'c : IsClosed H' := Aux.isClosed_of_mem_componentsOf H.isClosed hH'mem
  let C' : TopologicalSpace.IrreducibleCloseds X := ⟨H', hH'mem.1.1, hH'c⟩
  have hC' : codimension C' = 1 :=
    hH1 C' ⟨hH'mem.1.2, fun W' hW' hle => hH'mem.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hlt : irreducibleClosure hW.1.1 < C' := by
    refine lt_of_le_of_ne ?_ ?_
    · change closure W ⊆ H'
      rw [hWc.closure_eq]
      exact hWH'
    · intro h
      apply hne
      have := congrArg (fun C : TopologicalSpace.IrreducibleCloseds X => (C : Set X)) h
      simpa [irreducibleClosure, hWc.closure_eq, C'] using this
  have := Order.coheight_add_one_le hlt
  rw [codimension_eq_coheight] at hC' ⊢
  rw [hC'] at this
  exact le_trans (by norm_num) this

/-- If every irreducible component of `Z` has codimension at least two, then the union of the
components of codimension at least two is `Z` itself. -/
private theorem componentsOfCodimAtLeastTwo_eq_self {X : Scheme.{u}} {Z : Set X}
    (h2 : ∀ W (hW : W ∈ componentsOf Z), 2 ≤ codimension (irreducibleClosure hW.1.1)) :
    componentsOfCodimAtLeastTwo Z = Z := by
  ext x
  rw [mem_componentsOfCodimAtLeastTwo]
  refine ⟨fun ⟨_, hW, _, hx⟩ => hW.1.2 hx, fun hx => ?_⟩
  obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hx
  exact ⟨W, hW, h2 W hW, hxW⟩

/-- The reindexing `Fin (n + 1) → Fin n ⊕ Unit` sending the last index to the exceptional
entry and `castSucc i` to the `i`-th transform. -/
private abbrev lastToInr (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  finSuccEquivLast.trans (Equiv.optionEquivSumPUnit _)

/-- When every irreducible component of the centre `Z ⊆ H` has codimension at least two, the
family `(B_ZH, π⁻¹_tot(E))` is the family of transforms `π⁻¹(D ∖ Z)‾` of the members of
`H + ∑ᵢ E^i` followed by the exceptional divisor, reindexed. -/
private theorem cons_ker_canonicalLift_totalTransform_eq {X : Scheme.{u}} (E : OrderedDivisor X)
    (H Z : X.IdealSheafData) [IsReduced H.subscheme]
    [IsReduced (Z.comap (blowUpToBase Z)).subscheme]
    (hEpure : ∀ i, Mori.IsPureCodimOne (E.E i).support)
    (h2 : ∀ W (hW : W ∈ componentsOf (Z.support : Set X)),
      2 ≤ codimension (irreducibleClosure hW.1.1)) :
    ∀ i : Fin (E.s + 1 + 1), Fin.cons (α := fun _ => (blowUp Z).IdealSheafData)
        (canonicalLift H.subschemeι Z).ker (E.totalTransform Z).E i =
      blowUpTransformFamily (Fin.cons (α := fun _ => X.IdealSheafData) H E.E) Z
        (lastToInr _ i) := by
  have hunion : (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
      (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W) =
      blowUpToBase Z ⁻¹' (Z.support : Set X) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
    refine ⟨fun ⟨_, hW, _, hy⟩ => hW.1.2 hy, fun hy => ?_⟩
    obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hy
    exact ⟨W, hW, fun hWE =>
      OrderedDivisor.not_two_le_codimension_of_mem_componentsOf E hEpure hWE (h2 W hW), hxW⟩
  intro i
  induction i using Fin.lastCases with
  | last =>
    have hcl : TopologicalSpace.Closeds.closure (blowUpToBase Z ⁻¹' (Z.support : Set X)) =
        (Z.comap (blowUpToBase Z)).support :=
      TopologicalSpace.Closeds.ext (by
        rw [TopologicalSpace.Closeds.coe_closure, Scheme.IdealSheafData.support_comap]
        exact (Z.support.isClosed.preimage (blowUpToBase Z).continuous).closure_eq)
    rw [Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionEquivSumPUnit_none]
    change (E.totalTransform Z).E (Fin.last E.s) = _
    simp only [OrderedDivisor.totalTransform, Fin.snoc_last, hunion, hcl,
      Mori.vanishingIdeal_support_eq_self, blowUpTransformFamily, Sum.elim_inr]
  | cast j =>
    rw [Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionEquivSumPUnit_some]
    induction j using Fin.cases with
    | zero =>
      simp only [blowUpTransformFamily, Sum.elim_inl, Fin.castSucc_zero, Fin.cons_zero,
        ker_canonicalLift_eq_vanishingIdeal, Scheme.IdealSheafData.range_subschemeι]
      rfl
    | succ m =>
      simp only [blowUpTransformFamily, Sum.elim_inl, Fin.cons_succ, ← Fin.succ_castSucc]
      change (E.totalTransform Z).E (Fin.castSucc m) = _
      simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc,
        componentsOfCodimAtLeastTwo_eq_self h2]

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The transform of `H + ∑ᵢ E^i` stays snc** (Kollár, proof of Cor. 3.85). Let `X` be a
variety over a field `k` of characteristic zero, `E` an ordered divisor and `H` a closed
subscheme with `H + ∑ᵢ E^i` a simple normal crossing divisor. Let `Z ⊆ H` be a closed
subscheme having simple normal crossings with `E`, no irreducible component of which is
an irreducible component of `H`. Then on the blow-up `B_ZX`, the birational transform
`H₁ = B_{Z·𝒪_H}H`, the kernel of the canonical lift of `H → X`, followed by the entries of the
total transform `π⁻¹_tot(E)`, is a simple normal crossing divisor. -/
@[mmp "lem_kr3d_snc_transform_inside_hypersurface"]
public theorem isSNCFamily_cons_ker_canonicalLift_totalTransform [CharZero k]
    (sX : X ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) (E : OrderedDivisor X) (H : X.IdealSheafData)
    (hHE : IsSNCFamily sX (Fin.cons (α := fun _ => X.IdealSheafData) H E.E))
    (Z : X.IdealSheafData) (hZH : H ≤ Z) (hZ : HasSNCWith E.E Z)
    (hZcomp : ∀ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf (H.support : Set X)) :
    IsSNCFamily (blowUpToBase Z ≫ sX)
      (Fin.cons (α := fun _ => (blowUp Z).IdealSheafData)
        (canonicalLift H.subschemeι Z).ker (E.totalTransform Z).E) := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := {}
  have h := isSNCFamily_blowUpTransformFamily sX hHE
    (hasSNCWith_cons_of_hasSNCWith sX E H hHE Z hZH hZ)
  have : IsReduced H.subscheme := by simpa using (hHE.1 0).1
  have : IsReduced (Z.comap (blowUpToBase Z)).subscheme := (h.1 (Sum.inr ())).1
  rw [funext (cons_ker_canonicalLift_totalTransform_eq E H Z
    (fun i => by simpa using (hHE.1 i.succ).2.1)
    fun W hW => two_le_codimension_of_mem_componentsOf (by simpa using (hHE.1 0).2.1)
      (Scheme.IdealSheafData.support_antitone hZH) hZcomp hW)]
  exact h.comp _ (lastToInr _).injective

end MMP.Resolution.Kollar

end

public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.Resolution

/-- The conclusion for a sequence `S`: it is of order `≥ m` starting with `(X, I, m, E)`
and its end has `maxord N < m`. -/
private def StepOneGood {k : Type u} [Field k] {X : Scheme} (m : ℕ) (s : X ⟶ Spec (.of k))
    (a : MarkedIdeal X) (E : OrderedDivisor X) (S : ClosedBlowupSequence X) : Prop :=
  S.IsOrderGeMarkedTripleSeq s a E ∧
    maxOrder (nonmonomialPart (S.markedTransform a).I (S.orderedTotalTransform E)) < m

private theorem markedTransform_eq_mk {X : Scheme} (S : ClosedBlowupSequence X)
    (a : MarkedIdeal X) : S.markedTransform a = ⟨(S.markedTransform a).I, a.m⟩ := by
  cases h : S.markedTransform a
  have := S.markedTransform_m a
  rw [h] at this
  subst this
  rfl

/-- The end of a sequence of order `≥ m` starting with a marked triple is a marked triple. -/
private theorem isTriple_end {k : Type u} [Field k] {X : Scheme} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), S.IsOrderGeMarkedTripleSeq s a E →
      IsTriple (S.toBase ≫ s) (S.markedTransform a).I (S.orderedTotalTransform E)
  | .nil X, s, a, E, h => by
    change IsTriple (𝟙 X ≫ s) a.I E
    rwa [Category.id_comp]
  | .cons Z S, s, a, E, h => by
    have := isTriple_end S _ _ _ h.2.2.2.2.2
    change IsTriple ((S.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rwa [Category.assoc]

/-- Concatenation: `S` of order `≥ m`, followed by a good sequence starting with its end. -/
private theorem stepOneGood_append {k : Type u} [Field k] (m : ℕ) {X : Scheme} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X) (T : ClosedBlowupSequence S.target),
      S.IsOrderGeMarkedTripleSeq s a E →
      StepOneGood m (S.toBase ≫ s) (S.markedTransform a) (S.orderedTotalTransform E) T →
      StepOneGood m s a E (S.append T)
  | .nil X, s, a, E, T, _, hT => by
    change StepOneGood m (𝟙 X ≫ s) a E T at hT
    rwa [Category.id_comp] at hT
  | .cons Z S, s, a, E, T, hS, hT => by
    have ih := stepOneGood_append m S (blowUpToBase Z ≫ s) (a.birationalTransform Z)
      (E.totalTransform Z) T hS.2.2.2.2.2 (by
        change StepOneGood m ((S.toBase ≫ blowUpToBase Z) ≫ s) _ _ T at hT
        rwa [Category.assoc] at hT)
    exact ⟨⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2.1, ih.1⟩, ih.2⟩

/-- One round: a sequence of order `μ ≥ m` for `(X, N(I), E)` is of order `≥ m` for
`(X, I, m, E)`, and the nonmonomial parts of the transforms of `(I, m)` are the controlled
transforms of `N(I)`. -/
private theorem isOrderGe_of_isOrderM {k : Type u} [Field k] {m μ : ℕ} (hm : 1 ≤ m)
    (hmμ : m ≤ μ) {X : Scheme} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
      (E : OrderedDivisor X), IsTriple s I E →
      S.IsOrderMTripleSeq s (nonmonomialPart I E) E μ →
      S.IsOrderGeMarkedTripleSeq s ⟨I, m⟩ E ∧
        nonmonomialPart (S.markedTransform ⟨I, m⟩).I (S.orderedTotalTransform E) =
          S.controlledTransform (nonmonomialPart I E)
  | .nil _, s, I, E, hI, _ => ⟨hI, rfl⟩
  | .cons Z S, s, I, E, hI, hS => by
    obtain ⟨-, hZsm, hZcod, hZsnc, hZord, hS'⟩ := hS
    have hN : OrderAlongGE (nonmonomialPart I E) (Z.support : Set X) m := fun W hW => by
      rw [hZord W hW]; exact_mod_cast hmμ
    obtain ⟨hIZ, heq⟩ := nonmonomialPart_birationalTransform s hI hm hZsm hZsnc hN
    have hI' := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) hI hZsnc
    rw [← heq] at hS'
    have ih := isOrderGe_of_isOrderM hm hmμ S (blowUpToBase Z ≫ s)
      ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I
      (E.totalTransform Z) hI' hS'
    exact ⟨⟨hI, hZsm, hZcod, hZsnc, hIZ, ih.1⟩, ih.2.trans (congrArg S.controlledTransform heq)⟩

/-! ### Upper semicontinuity of the order -/

section Leibniz

variable {R : Type*} [CommRing R]

/-- A Leibniz additive map sends `M ^ (n + 1)` into `M ^ n`. -/
private theorem leibniz_mem_pow_of_mem_pow_succ (D : R → R) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = a * D b + b * D a) (M : Ideal R) :
    ∀ n : ℕ, ∀ f ∈ M ^ (n + 1), D f ∈ M ^ n
  | 0, _, _ => by simp
  | n + 1, f, hf => by
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun x y hx hy => ?_)
    · rw [hmul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [mul_comm, pow_succ]
      exact Ideal.mul_mem_mul (leibniz_mem_pow_of_mem_pow_succ D hadd hmul M n a ha) hb
    · rw [hadd]; exact Ideal.add_mem _ hx hy

private theorem leibniz_foldl_mem {ι : Type*} (D : ι → R → R)
    (hadd : ∀ i a b, D i (a + b) = D i a + D i b)
    (hmul : ∀ i a b, D i (a * b) = a * D i b + b * D i a) (M : Ideal R) :
    ∀ (w : List ι) (n : ℕ) (f : R), f ∈ M ^ (n + w.length) →
      w.foldl (fun g i => D i g) f ∈ M ^ n
  | [], n, f, hf => by simpa using hf
  | i :: w, n, f, hf => by
    rw [List.foldl_cons]
    refine leibniz_foldl_mem D hadd hmul M w n _ ?_
    refine leibniz_mem_pow_of_mem_pow_succ (D i) (hadd i) (hmul i) M _ f ?_
    simpa [Nat.add_assoc, Nat.add_comm 1] using hf

private theorem euler_mem {d : ℕ} (t : Fin d → R) (D : Fin d → R → R)
    (hadd : ∀ i a b, D i (a + b) = D i a + D i b)
    (hmul : ∀ i a b, D i (a * b) = a * D i b + b * D i a)
    (hD : ∀ i j, D i (t j) = if i = j then 1 else 0) :
    ∀ (r : ℕ) (f : R), f ∈ Ideal.span (Set.range t) ^ r →
      (∑ i, t i * D i f) - (r : R) * f ∈ Ideal.span (Set.range t) ^ (r + 1)
  | 0, f, _ => by
    simp only [Nat.cast_zero, zero_mul, sub_zero, zero_add, pow_one]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  | r + 1, f, hf => by
    set M := Ideal.span (Set.range t)
    have hsumM : ∀ c, ∑ i, t i * D i c ∈ M := fun c =>
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have h0 : ∀ i, D i 0 = 0 := fun i => by have := hadd i 0 0; simpa using this
    let K : Ideal R :=
      { carrier := {f | f ∈ M ^ (r + 1) ∧
          (∑ i, t i * D i f) - ((r + 1 : ℕ) : R) * f ∈ M ^ (r + 1 + 1)}
        add_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          refine ⟨Ideal.add_mem _ ha hb, ?_⟩
          have : (∑ i, t i * D i (a + b)) - ((r + 1 : ℕ) : R) * (a + b) =
              ((∑ i, t i * D i a) - ((r + 1 : ℕ) : R) * a) +
              ((∑ i, t i * D i b) - ((r + 1 : ℕ) : R) * b) := by
            simp only [hadd, mul_add, Finset.sum_add_distrib]; ring
          rw [this]; exact Ideal.add_mem _ ha' hb'
        zero_mem' := by simp [h0]
        smul_mem' := by
          rintro c a ⟨ha, ha'⟩
          refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
          have hs : ∑ i, t i * D i (c * a) =
              c * ∑ i, t i * D i a + (∑ i, t i * D i c) * a := by
            rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => by rw [hmul]; ring
          have : (∑ i, t i * D i (c • a)) - ((r + 1 : ℕ) : R) * (c • a) =
              c * ((∑ i, t i * D i a) - ((r + 1 : ℕ) : R) * a) +
              (∑ i, t i * D i c) * a := by
            rw [smul_eq_mul, hs]; ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha') ?_
          rw [pow_succ' M (r + 1)]
          exact Ideal.mul_mem_mul (hsumM c) ha }
    have hle : M ^ (r + 1) ≤ K := by
      rw [pow_succ]
      refine Ideal.mul_le.2 fun a ha b hb => ?_
      refine Submodule.span_induction (p := fun b _ => a * b ∈ K) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩
        refine ⟨by rw [pow_succ]; exact Ideal.mul_mem_mul ha (Ideal.subset_span ⟨j, rfl⟩), ?_⟩
        have ih := euler_mem t D hadd hmul hD r a ha
        have hs : ∑ i, t i * D i (a * t j) = t j * a + t j * ∑ i, t i * D i a := by
          have : ∀ i, t i * D i (a * t j) = (if i = j then t j * a else 0) +
              t j * (t i * D i a) := fun i => by
            rw [hmul, hD]; split_ifs with h <;> [subst h; skip] <;> ring
          simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
            Finset.mul_sum]
        have : (∑ i, t i * D i (a * t j)) - ((r + 1 : ℕ) : R) * (a * t j) =
            t j * ((∑ i, t i * D i a) - (r : R) * a) := by
          rw [hs]; push_cast; ring
        rw [this, pow_succ' M (r + 1)]
        exact Ideal.mul_mem_mul (Ideal.subset_span ⟨j, rfl⟩) ih
      · simp only [mul_zero]; exact K.zero_mem
      · intro x y _ _ hx hy; rw [mul_add]; exact K.add_mem hx hy
      · intro c x _ hx
        rw [smul_eq_mul, mul_left_comm]; exact K.mul_mem_left c hx
    exact (hle hf).2

/-- Some word of at most `r` of the `Dᵢ` takes `f ∉ 𝔪^{r+1}` out of `𝔪`. -/
private theorem exists_foldl_notMem {d : ℕ} (t : Fin d → R) (D : Fin d → R → R)
    (hadd : ∀ i a b, D i (a + b) = D i a + D i b)
    (hmul : ∀ i a b, D i (a * b) = a * D i b + b * D i a)
    (hD : ∀ i j, D i (t j) = if i = j then 1 else 0)
    (hunit : ∀ n : ℕ, IsUnit ((n + 1 : ℕ) : R)) :
    ∀ (r : ℕ) (f : R), f ∉ Ideal.span (Set.range t) ^ (r + 1) →
      ∃ w : List (Fin d), w.length ≤ r ∧
        w.foldl (fun g i => D i g) f ∉ Ideal.span (Set.range t)
  | 0, f, hf => ⟨[], le_rfl, by simpa using hf⟩
  | r + 1, f, hf => by
    set M := Ideal.span (Set.range t)
    by_cases h1 : f ∈ M ^ (r + 1)
    · have hE := euler_mem t D hadd hmul hD (r + 1) f h1
      have : ∃ i, D i f ∉ M ^ (r + 1) := by
        by_contra hall
        push Not at hall
        apply hf
        have hs : ∑ i, t i * D i f ∈ M ^ (r + 1 + 1) := by
          rw [pow_succ' M (r + 1)]
          exact Ideal.sum_mem _ fun i _ =>
            Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (hall i)
        have h2 : ((r + 1 : ℕ) : R) * f ∈ M ^ (r + 1 + 1) := by
          have := Ideal.sub_mem _ hs hE
          simpa using this
        obtain ⟨u, hu⟩ := hunit r
        have := Ideal.mul_mem_left _ (↑u⁻¹ : R) h2
        rwa [← hu, ← mul_assoc, Units.inv_mul, one_mul] at this
      obtain ⟨i, hi⟩ := this
      obtain ⟨w, hw, hw'⟩ := exists_foldl_notMem t D hadd hmul hD hunit r _ hi
      exact ⟨i :: w, by simp; omega, by simpa using hw'⟩
    · obtain ⟨w, hw, hw'⟩ := exists_foldl_notMem t D hadd hmul hD hunit r f h1
      exact ⟨w, hw.trans (Nat.le_succ _), hw'⟩

end Leibniz

/-- On a scheme over a field of characteristic zero the positive integers are units in every
local ring. -/
private theorem isUnit_natCast_succ_stalk {k : Type u} [Field k] [CharZero k]
    {Y : Scheme} (hY : Y ⟶ Spec (.of k)) (y : Y) (n : ℕ) :
    IsUnit ((n + 1 : ℕ) : Y.presheaf.stalk y) := by
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ hY.app ⊤ ≫ Y.presheaf.germ ⊤ y trivial).hom
  have := (IsUnit.mk0 ((n + 1 : ℕ) : k) (by exact_mod_cast Nat.succ_ne_zero n)).map φ
  rwa [map_natCast] at this

/-- The germ of `D s` at `y` depends only on the germ of `s` at `y`: two representatives agree
on a smaller open, and `D` commutes with restriction. -/
private theorem exists_germ_onSections {k : Type u} [Field k] {Y : Scheme}
    {hY : Y ⟶ Spec (.of k)} (D : Stacks.Curves.SheafDerivationOf hY) {y : Y}
    (z : Y.presheaf.stalk y) :
    ∃ w : Y.presheaf.stalk y, ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
      Y.presheaf.germ U y hy s = z → Y.presheaf.germ U y hy (D.onSections s) = w := by
  obtain ⟨U₀, hy₀, s₀, hs₀⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf z
  refine ⟨Y.presheaf.germ U₀ y hy₀ (D.onSections s₀), fun U hy s hs => ?_⟩
  obtain ⟨W, hyW, iU, iU₀, heq⟩ := Y.presheaf.germ_eq y hy hy₀ s s₀ (hs.trans hs₀.symm)
  refine TopCat.Presheaf.germ_ext _ W hyW iU iU₀ ?_
  exact (D.onSections_restrict (leOfHom iU) s).symm.trans (congrArg _ heq) |>.trans
    (D.onSections_restrict (leOfHom iU₀) s₀)

/-- The map a vector field induces on the local ring `𝒪_{Y, y}`. -/
private noncomputable def stalkFun {k : Type u} [Field k] {Y : Scheme}
    {hY : Y ⟶ Spec (.of k)} (D : Stacks.Curves.SheafDerivationOf hY) {y : Y}
    (z : Y.presheaf.stalk y) : Y.presheaf.stalk y :=
  (exists_germ_onSections D z).choose

private theorem stalkFun_germ {k : Type u} [Field k] {Y : Scheme}
    {hY : Y ⟶ Spec (.of k)} (D : Stacks.Curves.SheafDerivationOf hY) {y : Y} (U : Y.Opens)
    (hy : y ∈ U) (s : Γ(Y, U)) :
    stalkFun D (Y.presheaf.germ U y hy s) = Y.presheaf.germ U y hy (D.onSections s) :=
  ((exists_germ_onSections D _).choose_spec U hy s rfl).symm

private theorem exists_germ_eq_pair {Y : Scheme} (y : Y) (z w : Y.presheaf.stalk y) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (s t : Γ(Y, U)),
      Y.presheaf.germ U y hy s = z ∧ Y.presheaf.germ U y hy t = w := by
  obtain ⟨U₁, h₁, s, hs⟩ := Y.presheaf.exists_germ_eq z
  obtain ⟨U, hU, h, t, ht⟩ := Y.presheaf.exists_le_germ_eq w h₁
  exact ⟨U, h, (Y.presheaf.map (homOfLE hU).op).hom s, t,
    (Y.presheaf.germ_res_apply (homOfLE hU) y h s).trans hs, ht⟩

private theorem stalkFun_add {k : Type u} [Field k] {Y : Scheme}
    {hY : Y ⟶ Spec (.of k)} (D : Stacks.Curves.SheafDerivationOf hY) {y : Y}
    (z w : Y.presheaf.stalk y) : stalkFun D (z + w) = stalkFun D z + stalkFun D w := by
  obtain ⟨U, hy, s, t, rfl, rfl⟩ := exists_germ_eq_pair y z w
  rw [← map_add, stalkFun_germ, stalkFun_germ, stalkFun_germ,
    Stacks.Curves.SheafDerivationOf.onSections_add, map_add]

private theorem stalkFun_mul {k : Type u} [Field k] {Y : Scheme}
    {hY : Y ⟶ Spec (.of k)} (D : Stacks.Curves.SheafDerivationOf hY) {y : Y}
    (z w : Y.presheaf.stalk y) : stalkFun D (z * w) = z * stalkFun D w + w * stalkFun D z := by
  obtain ⟨U, hy, s, t, rfl, rfl⟩ := exists_germ_eq_pair y z w
  rw [← map_mul, stalkFun_germ, stalkFun_germ, stalkFun_germ,
    Stacks.Curves.SheafDerivationOf.onSections_mul, map_add, map_mul, map_mul]

/-- Germs commute with a word in vector fields. -/
private theorem germ_foldl_onSections {k : Type u} [Field k] {Y : Scheme}
    {hY : Y ⟶ Spec (.of k)} {d : ℕ} (δ : Fin d → Stacks.Curves.SheafDerivationOf hY)
    {U : Y.Opens} (y : Y) (hy : y ∈ U) :
    ∀ (w : List (Fin d)) (G : Γ(Y, U)),
      Y.presheaf.germ U y hy (w.foldl (fun g i => (δ i).onSections g) G) =
        w.foldl (fun g i => stalkFun (δ i) g) (Y.presheaf.germ U y hy G)
  | [], _ => rfl
  | i :: w, G => by
    simp only [List.foldl_cons]
    rw [germ_foldl_onSections δ y hy w, stalkFun_germ]

/-- **Upper semicontinuity of the order** on a smooth scheme over a field of characteristic
zero: every point `x` with `ord_x I < ∞` has a neighbourhood on which `ord I ≤ ord_x I`. -/
private theorem exists_nhds_multAt_le {k : Type u} [Field k] [CharZero k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (I : X.IdealSheafData) (x : X) (hx : multAt I x ≠ ⊤) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, multAt I y ≤ multAt I x := by
  classical
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
  obtain ⟨d, t, ht⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  obtain ⟨V, hxV, s, δ, hs, hδ⟩ :=
    MMP.Flips.ResolutionInputs.exists_sheafDerivationOf_dual_of_isRegularSystemOfParameters
      sX x t ht
  set r := (multAt I x).toNat
  have hrx : multAt I x = r := (ENat.coe_toNat hx).symm
  let x' : (V : Scheme) := ⟨x, hxV⟩
  let e : X.presheaf.stalk x ≃+* (V : Scheme).presheaf.stalk x' :=
    (V.stalkIso x').symm.commRingCatIsoToRingEquiv
  have he : ∀ z, e z = (V.ι.stalkMap x').hom z := fun z => by
    change (V.stalkIso x').inv.hom z = _
    rw [Scheme.Opens.stalkIso_inv]
    rfl
  let S : Fin d → Γ((V : Scheme), ⊤) := fun j => V.topIso.inv.hom (s j)
  have hS : ∀ i j, (δ i).onSections (S j) = if i = j then 1 else 0 := by
    intro i j
    have h := congrArg V.topIso.inv.hom (hδ i j)
    simp only [applyDerivation] at h
    rw [Iso.hom_inv_id_apply] at h
    rw [h]
    split_ifs <;> simp
  let t' : Fin d → (V : Scheme).presheaf.stalk x' :=
    fun j => (V : Scheme).presheaf.germ ⊤ x' trivial (S j)
  have ht' : ∀ j, t' j = e (t j) := by
    intro j
    rw [← hs j, he, ← Scheme.Opens.stalkIso_inv]
    have h := congrArg (fun φ => φ.hom (S j)) (Scheme.Opens.germ_stalkIso_inv V ⊤ x' trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    refine h.symm.trans (congrArg (V.stalkIso x').inv.hom ?_)
    simp only [S, Scheme.Opens.topIso, Functor.mapIso_inv]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hspan : Ideal.span (Set.range t') = maximalIdeal _ := by
    have : Set.range t' = e '' Set.range t := by
      rw [← Set.range_comp]; exact congrArg Set.range (funext ht')
    rw [this, ← Ideal.map_span, ht.1, IsLocalRing.map_ringEquiv_maximalIdeal]
  have hD : ∀ i j, stalkFun (δ i) (t' j) = if i = j then 1 else 0 := by
    intro i j
    refine (stalkFun_germ (δ i) ⊤ trivial (S j)).trans ?_
    rw [hS]
    split_ifs <;> simp
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := V) hxV
  have hnot : ¬ IdealSheafData.stalk I x ≤ maximalIdeal _ ^ (r + 1) := by
    rw [← natCast_le_idealOrder_iff']
    change ¬ ((r + 1 : ℕ) : ℕ∞) ≤ multAt I x
    rw [hrx]
    norm_cast
    omega
  obtain ⟨g, hgI, hg⟩ : ∃ g ∈ I.ideal ⟨W, hW⟩,
      (X.presheaf.germ W x hxW).hom g ∉ maximalIdeal _ ^ (r + 1) := by
    by_contra hall
    push Not at hall
    apply hnot
    rw [IdealSheafData.stalk_eq_map_germ I x ⟨W, hW⟩ hxW, Ideal.map_le_iff_le_comap]
    exact fun g hg => hall g hg
  let G : Γ((V : Scheme), V.ι ⁻¹ᵁ W) := (V.ι.app W).hom g
  have hG : ∀ (y' : (V : Scheme)) (hy' : y' ∈ V.ι ⁻¹ᵁ W),
      (V : Scheme).presheaf.germ _ y' hy' G =
        (V.ι.stalkMap y').hom ((X.presheaf.germ W (V.ι y') hy').hom g) :=
    fun y' hy' => (Scheme.Hom.germ_stalkMap_apply V.ι W y' hy' g).symm
  have hx'W : x' ∈ V.ι ⁻¹ᵁ W := hxW
  have hf' : (V : Scheme).presheaf.germ _ x' hx'W G ∉ Ideal.span (Set.range t') ^ (r + 1) := by
    rw [hG, hspan]
    intro hmem
    apply hg
    have key : e ((X.presheaf.germ W x hxW).hom g) ∈
        (maximalIdeal _ ^ (r + 1)).map (e : X.presheaf.stalk x →+* _) := by
      rw [Ideal.map_pow]
      erw [IsLocalRing.map_ringEquiv_maximalIdeal e]
      rwa [he]
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at key
    simpa using key
  obtain ⟨w, hw, hw'⟩ := exists_foldl_notMem t' (fun i => stalkFun (δ i))
    (fun i => stalkFun_add (δ i)) (fun i => stalkFun_mul (δ i))
    hD (isUnit_natCast_succ_stalk (V.ι ≫ sX) x') r _ hf'
  let H := w.foldl (fun g i => (δ i).onSections g) G
  refine ⟨V.ι ''ᵁ ((V : Scheme).basicOpen H), ⟨x', ?_, rfl⟩, ?_⟩
  · change x' ∈ (V : Scheme).basicOpen H
    rw [Scheme.mem_basicOpen _ _ _ hx'W, germ_foldl_onSections]
    rw [hspan] at hw'
    exact (IsLocalRing.notMem_maximalIdeal.1 hw')
  · rintro _ ⟨y', hy', rfl⟩
    change y' ∈ (V : Scheme).basicOpen H at hy'
    have hy'W : y' ∈ V.ι ⁻¹ᵁ W := (V : Scheme).basicOpen_le H hy'
    rw [hrx]
    by_contra hlt
    have hle : ((r + 1 : ℕ) : ℕ∞) ≤ multAt I (V.ι y') := by
      push Not at hlt
      exact_mod_cast Order.add_one_le_of_lt hlt
    rw [multAt, natCast_le_idealOrder_iff'] at hle
    have h1 : (X.presheaf.germ W (V.ι y') hy'W).hom g ∈ maximalIdeal _ ^ (r + 1) := by
      refine hle ?_
      rw [IdealSheafData.stalk_eq_map_germ I _ ⟨W, hW⟩ hy'W]
      exact Ideal.mem_map_of_mem _ hgI
    have h2 : (V : Scheme).presheaf.germ _ y' hy'W G ∈ maximalIdeal _ ^ (1 + w.length) := by
      rw [hG]
      have hm := Ideal.mem_map_of_mem (V.ι.stalkMap y').hom h1
      rw [Ideal.map_pow] at hm
      refine Ideal.pow_le_pow_right (by omega) (Ideal.pow_right_mono ?_ _ hm)
      exact Ideal.map_le_iff_le_comap.2 (le_of_eq (IsLocalRing.maximalIdeal_comap _).symm)
    have h3 := leibniz_foldl_mem (fun i => stalkFun (δ i))
      (fun i => stalkFun_add (δ i))
      (fun i => stalkFun_mul (δ i)) (maximalIdeal _) w 1 _ h2
    rw [pow_one, ← germ_foldl_onSections] at h3
    have hu := (Scheme.mem_basicOpen _ _ _ hy'W).1 hy'
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 hu

/-- The maximal order of an ideal sheaf on a quasi-compact smooth scheme over a field of
characteristic zero is finite as soon as every order is. -/
private theorem maxOrder_ne_top_of_forall {k : Type u} [Field k] [CharZero k]
    {X : Scheme} (sX : X ⟶ Spec (.of k)) [Smooth sX] [CompactSpace X]
    (I : X.IdealSheafData) (hI : ∀ x, multAt I x ≠ ⊤) : maxOrder I ≠ ⊤ := by
  classical
  choose U hxU hU using fun x => exists_nhds_multAt_le sX I x (hI x)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ne_top_of_le_ne_top (ENat.coe_ne_top (T.sup fun x => (multAt I x).toNat)) ?_
  refine iSup₂_le fun z _ => ?_
  obtain ⟨x, hxT, hz⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ z))
  calc multAt I z ≤ multAt I x := hU x z hz
    _ = ((multAt I x).toNat : ℕ∞) := (ENat.coe_toNat (hI x)).symm
    _ ≤ _ := by exact_mod_cast Finset.le_sup (f := fun x => (multAt I x).toNat) hxT

/-- The maximal order of the ideal of a triple is finite: `X` is smooth and quasi-compact of
finite type over a field of characteristic zero and the ideal is nonzero at the generic
points. -/
private theorem maxOrder_ne_top_of_isTriple {k : Type u} [Field k] {X : Scheme}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    maxOrder I ≠ ⊤ := by
  obtain ⟨hchar, hsm, hlft, hqc, -, hnz, -⟩ := h
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := ⟨⟩
  haveI : Smooth s := (MMP.Mori.isSmoothScheme_iff s).1 hsm
  exact maxOrder_ne_top_of_forall s I (multAt_ne_top_of_isNonzeroAtGenericPoints hnz)

/-- A nonempty scheme carrying a triple has Krull dimension `dimNat X`. -/
private theorem topologicalKrullDim_eq_dimNat {k : Type u} [Field k] {X : Scheme}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} [Nonempty X]
    (h : IsTriple s I E) : topologicalKrullDim X = ((dimNat X : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨-, -, hlft, hqc, -⟩ := h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k s
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    unfold topologicalKrullDim
    rw [Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  unfold dimNat
  generalize topologicalKrullDim X = e at htop hbot ⊢
  induction e using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe e =>
    induction e using WithTop.recTopCoe with
    | top => exact absurd rfl htop
    | coe n => rfl

/-- A generic point of `X` lies off a closed subscheme all of whose components have positive
codimension. -/
private theorem notMem_supportSet_of_mem_genericPoints {X : Scheme}
    {Z : X.IdealSheafData} (hZ : HasComponentsOfPositiveCodim (Z.support : Set X)) {ξ : X}
    (hξ : ξ ∈ genericPoints X) : ξ ∉ Z.supportSet := by
  intro h
  have h' : ξ ∈ (Z.support : Set X) := Scheme.IdealSheafData.mem_supportSet_iff_mem_support.1 h
  obtain ⟨W, hW, hξW⟩ := exists_mem_componentsOf h'
  have hD : closure {ξ} ∈ irreducibleComponents X := hξ
  have hDW : closure {ξ} ⊆ closure W := closure_mono (Set.singleton_subset_iff.2 hξW)
  have hcod := hZ W hW
  rw [codimension_eq_coheight] at hcod
  have hmax : IsMax (irreducibleClosure hW.1.1) := fun C hC => by
    have hC' : closure W ⊆ (C : Set X) := hC
    have : (C : Set X) ⊆ closure {ξ} := hD.2 C.isIrreducible (hDW.trans hC')
    exact this.trans hDW
  rw [Order.coheight_eq_zero.2 hmax] at hcod
  exact absurd hcod (by norm_num)

/-- The blow-up of an equidimensional scheme locally of finite type over a field along a closed
subscheme all of whose components have positive codimension has the same dimension. -/
private theorem topologicalKrullDim_blowUp {k : Type u} [Field k] {X : Scheme}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (hX : TopologicalSpace.Equidimensional X)
    (Z : X.IdealSheafData) (hZ : HasComponentsOfPositiveCodim (Z.support : Set X)) :
    topologicalKrullDim (blowUp Z) = topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents (blowUp Z),
    topologicalKrullDim_eq_iSup_irreducibleComponents X]
  apply le_antisymm
  · refine iSup₂_le fun C hC => ?_
    obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z hC
    rw [h]
    exact le_iSup₂ (f := fun D (_ : D ∈ irreducibleComponents X) => topologicalKrullDim D) D hD
  · refine iSup₂_le fun D hD => ?_
    have hgen := hD.1.isGenericPoint_genericPoint_closure
    rw [(isClosed_of_mem_irreducibleComponents D hD).closure_eq] at hgen
    have hξ : hD.1.genericPoint ∈ genericPoints X := by
      change closure {_} ∈ irreducibleComponents X
      rwa [hgen.def]
    obtain ⟨η, hη, -⟩ := (bijOn_genericPoints_blowUpToBase Z).2.2
      ⟨hξ, notMem_supportSet_of_mem_genericPoints hZ hξ⟩
    have hC : closure {η} ∈ irreducibleComponents (blowUp Z) := hη
    obtain ⟨D', hD', h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z hC
    rw [hX D hD D' hD', ← h]
    exact le_iSup₂ (f := fun C (_ : C ∈ irreducibleComponents (blowUp Z)) =>
      topologicalKrullDim C) _ hC

/-- A smooth blow-up sequence of order `μ` starting with a triple keeps the dimension. -/
private theorem dimNat_target {k : Type u} [Field k] {μ : ℕ} {X : Scheme} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
      (E : OrderedDivisor X), S.IsOrderMTripleSeq s I E μ → dimNat S.target = dimNat X
  | .nil _, _, _, _, _ => rfl
  | .cons Z S, s, I, E, hS => by
    obtain ⟨⟨-, -, hlft, -, hX, -⟩, -, hcod, -, -, hS'⟩ := hS
    refine (dimNat_target S _ _ _ hS').trans ?_
    unfold dimNat
    rw [topologicalKrullDim_blowUp s hX Z hcod]

/-- The nonmonomial part of the ideal of a triple is nonzero at the generic points. -/
private theorem isTriple_nonmonomialPart {k : Type u} [Field k] {X : Scheme}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    IsTriple s (nonmonomialPart I E) E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun η hη hbot => h6 η hη (eq_bot_iff.2 ?_), h7⟩
  rw [← hbot]
  exact stalk_le_stalk_of_le (le_idealColon _ _) η

private theorem nonempty_of_one_le_maxOrder {X : Scheme} {I : X.IdealSheafData}
    (h : 1 ≤ maxOrder I) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  simp [maxOrder, maxOrderAlong] at h

/-- `StepOneGood` holds for `if p then x else y` when `p` holds and it holds for `x`. -/
private theorem stepOneGood_ite {k : Type u} [Field k] {X : Scheme} (m : ℕ)
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) {p : Prop} {_ : Decidable p}
    (x y : ClosedBlowupSequence X) (hp : p) (h : StepOneGood m s a E x) :
    StepOneGood m s a E (if p then x else y) := by
  rwa [if_pos hp]

private theorem stepOneGood_bmoStepOneAux {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) {m : ℕ} (hm : 1 ≤ m) {d : ℕ} (hd : d ∈ Set.Icc a b) :
    ∀ (q : ℕ) (t : MarkedTriple.{u}), t ∈ markedTriples → dimNat t.X = d →
      (maxOrder (nonmonomialPart t.I t.E)).toNat < q →
      StepOneGood m t.sX ⟨t.I, m⟩ t.E (bmoStepOneAux B d m q t)
  | 0, _, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | q + 1, t, ht, hdt, hq => by
    have ht0 : IsTriple t.sX t.I t.E := ht
    rw [bmoStepOneAux]
    split_ifs with h0
    · exact ⟨ht0, h0⟩
    · have hNt := isTriple_nonmonomialPart ht0
      have hfin := maxOrder_ne_top_of_isTriple hNt
      have hμ : maxOrder (nonmonomialPart t.I t.E) =
          ((maxOrder (nonmonomialPart t.I t.E)).toNat : ℕ∞) := (ENat.coe_toNat hfin).symm
      have hmμ : m ≤ (maxOrder (nonmonomialPart t.I t.E)).toNat := by
        have := not_lt.1 h0
        rw [hμ] at this
        exact_mod_cast this
      obtain ⟨F, hFB, hF1, -⟩ := hB _ (hm.trans hmμ)
      have hne : Nonempty t.X := nonempty_of_one_le_maxOrder
        (le_trans (by exact_mod_cast hm) (not_lt.1 h0))
      have ht' : (⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ : FieldBlowupTriple.{u}) ∈
          idealTriplesOfDim (Set.Icc a b) (maxOrder (nonmonomialPart t.I t.E)).toNat :=
        ⟨hNt, ⟨d, hd, by rw [← hdt]; exact topologicalKrullDim_eq_dimNat ht0⟩, hμ.le⟩
      have hS := F.isOrderMTripleSeq _ ht'
      have hlast := hF1 _ ht'
      rw [hFB] at hS hlast
      simp only [show dimNat t.X = d from hdt] at hS hlast
      obtain ⟨hS1, hS2⟩ := isOrderGe_of_isOrderM hm hmμ _ t.sX t.I t.E ht0 hS
      dsimp only
      refine stepOneGood_append m _ t.sX ⟨t.I, m⟩ t.E _ hS1 ?_
      have h1' : t.endOf m (B d (maxOrder (nonmonomialPart t.I t.E)).toNat
          ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩) ∈ markedTriples :=
        isTriple_end _ _ _ _ hS1
      refine stepOneGood_ite m _ _ _ _ _ h1' ?_
      rw [markedTransform_eq_mk]
      refine stepOneGood_bmoStepOneAux hB hm hd q _ h1' ?_ ?_
      · exact (dimNat_target _ _ _ _ hS).trans hdt
      · have hlast' : maxOrder ((B d (maxOrder (nonmonomialPart t.I t.E)).toNat
            ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩).controlledTransform
              (nonmonomialPart t.I t.E)) < ((maxOrder (nonmonomialPart t.I t.E)).toNat : ℕ∞) := by
          rwa [← hdt]
        change (maxOrder (nonmonomialPart (ClosedBlowupSequence.markedTransform _ _).I
          (ClosedBlowupSequence.orderedTotalTransform _ _))).toNat < q
        rw [hS2]
        have hne' := ne_top_of_lt hlast'
        rw [← ENat.coe_toNat hne'] at hlast'
        have := ENat.coe_lt_coe.1 hlast'
        omega

/-- **Kollár 3.111, Step 1.** Let `B` be an order-reduction family on dimensions `a, …, b`,
`m ≥ 1`, and `t = (X, I, E)` a marked triple with `a ≤ dim X ≤ b`. Then the Step-1 sequence
`bmoStepOne B (dimNat t.X) m t` is a smooth blow-up sequence of order `≥ m` starting with
`(X, I, m, E)`, and its end `(X_1, I_1, m, E_1)` satisfies `maxord N(I_1) < m`. -/
@[mmp "lem_kr3e_bmo_step_one_result"]
public theorem isOrderGeMarkedTripleSeq_bmoStepOne {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) {m : ℕ} (hm : 1 ≤ m) {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriples) (hdim : dimNat t.X ∈ Set.Icc a b) :
    (bmoStepOne B (dimNat t.X) m t).IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E ∧
      maxOrder (nonmonomialPart (t.endOf m (bmoStepOne B (dimNat t.X) m t)).I
        (t.endOf m (bmoStepOne B (dimNat t.X) m t)).E) < m :=
  stepOneGood_bmoStepOneAux hB hm hdim _ t ht rfl (Nat.lt_succ_self _)

end MMP.Resolution

end
