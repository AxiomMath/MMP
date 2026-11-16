module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions
import MMP.AlgebraicGeometry.Resolution.DivisorialPart

/-!
# Order-`m·s` sequences for the mixed ideal and reduction to the monomial case

This file contains two steps of the reduction of a marked triple `(X, I, m, E)` to the case in
which `I` is monomial (Kollár 3.111, Step 2). Write `N(I)` for the nonmonomial part of `I` and
`K = K_s(I, m) = N(I)^m + I^s` for the mixed ideal.

First, let `m, s ≥ 1` with `maxord K ≤ m·s`, and let `(X_i, Z_i)` be a smooth blow-up sequence of
order `m·s` starting with `(X, K, E)`. Then every truncation of it is a smooth blow-up sequence of
order `≥ m` starting with `(X, I, m, E)` and of order `≥ s` starting with `(X, N(I), s, E)`, and
the controlled transforms of `K` are `N_i^m + I_i^s`, where `I_i`, `N_i` are the marked
transforms of `(I, m)` and `(N(I), s)`. The proof is an induction along the sequence: at a centre
`Z` with `ord_Z K = m·s`, the order of a sum of powers gives `ord_Z N ≥ s` and `ord_Z I ≥ m`;
with `F` the exceptional divisor, `K'·I_F^{ms} = π^*K`, `N'·I_F^s = π^*N` and `I'·I_F^m = π^*I`,
and cancelling the Cartier divisor `I_F^{ms}` gives `K' = N'^m + I'^s`.

Second, suppose `cosupp(I, m)` is disjoint from `cosupp N(I)`, and let `U = X ∖ cosupp N(I)`, on
which `I` is monomial. A smooth blow-up sequence of order `≥ m` starting with
`(U, I|_U, m, E|_U)` has all its centres over `cosupp(I, m)`, which is closed in `X` (upper
semicontinuity of the order) and contained in `U`. So its extension by closure to `X` blows up the
same centres, and every condition on a centre (components and their codimension, snc with the
boundary, the order bound, smoothness) transfers along the open immersion; blowing up commutes
with it, and so do the birational transform and the total transform of the boundary.

## Main results

* An order-`m·s` sequence for `K_s(I, m)`:
  `ClosedBlowupSequence.isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal`.
  An order-`m·s` sequence for `K_s(I, m)` is of order `≥ m` for `(I, m)` and `≥ s` for
  `(N(I), s)`, with controlled transforms `N_i^m + I_i^s`.
* `ClosedBlowupSequence.isOrderGeMarkedTripleSeq_extendByClosure`: a sequence of
  order `≥ m` on `X ∖ cosupp N(I)` extends by closure to one on `X`. It is the case
  `j = U.ι` of `ClosedBlowupSequence.isOrderGeMarkedTripleSeq_extendByClosure_of_cosupport_subset`,
  for any quasi-compact open immersion `j` whose image contains the cosupport.
* Transfer along an open immersion `j` of the conditions on a centre whose support lies in the
  image of `j`: `hasSNCWith_of_comap`, `hasComponentsOfPositiveCodim_of_comap`,
  `orderAlongGE_of_comap`, `le_multAt_of_le_multAt_comap`, `image_subset_cosupport`; and the
  compatibility of blowing up with `j`: `range_canonicalLift`, `birationalTransform_comap`,
  `totalTransform_comap`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.111, Step 2]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- The stalk of a sum of ideal sheaves is the sum of the stalks. -/
private theorem stalk_sup {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hx,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hx,
    show (I ⊔ J).ideal ⟨U, hU⟩ = I.ideal ⟨U, hU⟩ ⊔ J.ideal ⟨U, hU⟩ from rfl, Ideal.map_sup]

/-- Cancelling a positive natural factor in `a * b ≤ a * y` over `ℕ∞`. -/
private theorem natCast_mul_le_iff {a b : ℕ} (ha : 1 ≤ a) (y : ℕ∞) :
    ((a * b : ℕ) : ℕ∞) ≤ a * y ↔ (b : ℕ∞) ≤ y := by
  push_cast
  exact ENat.mul_le_mul_left_iff (by exact_mod_cast (by omega : a ≠ 0)) (ENat.coe_ne_top a)

/-- The order of a sum is the minimum of the orders: `n ≤ ord_x (A + B)` iff `n ≤ ord_x A` and
`n ≤ ord_x B`. -/
private theorem natCast_le_multAt_sup_iff {X : Scheme.{u}} (A B : X.IdealSheafData) (x : X)
    (n : ℕ) : (n : ℕ∞) ≤ multAt (A ⊔ B) x ↔ (n : ℕ∞) ≤ multAt A x ∧ (n : ℕ∞) ≤ multAt B x := by
  simp only [multAt, natCast_le_idealOrder_iff', stalk_sup, sup_le_iff]

/-- At a point with regular local ring, `ord (N^m + I^s) ≥ m·s` gives `ord N ≥ s` and
`ord I ≥ m`. -/
private theorem le_multAt_of_le_multAt_pow_add_pow {X : Scheme.{u}} (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] (N I : X.IdealSheafData) {m s : ℕ} (hm : 1 ≤ m)
    (hs : 1 ≤ s) (h : ((m * s : ℕ) : ℕ∞) ≤ multAt (N ^ m + I ^ s) x) :
    (s : ℕ∞) ≤ multAt N x ∧ (m : ℕ∞) ≤ multAt I x := by
  change ((m * s : ℕ) : ℕ∞) ≤ multAt (N ^ m ⊔ I ^ s) x at h
  rwa [natCast_le_multAt_sup_iff, multAt_pow, multAt_pow, natCast_mul_le_iff hm, mul_comm m s,
    natCast_mul_le_iff hs] at h

/-- Along a smooth centre of constant order `m`, the divisor of the controlled transform is
`I_F^m`. -/
private theorem controlledTransformDivisorIdeal_eq_pow {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) [LocallyOfFiniteType sX]
    [QuasiCompact sX] (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (I : X.IdealSheafData) (m : ℕ) (hI : OrderAlongEq I (Z.support : Set X) m) :
    controlledTransformDivisorIdeal Z I = Z.comap (blowUpToBase Z) ^ m := by
  classical
  haveI := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : Finite (componentsOf (Z.support : Set X)) :=
    (finite_componentsOf Z.support.2).to_subtype
  letI := Fintype.ofFinite (componentsOf (Z.support : Set X))
  have key : ∀ y, IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
      IdealSheafData.stalk (Z.comap (blowUpToBase Z) ^ m) y := by
    intro y
    set x := blowUpToBase Z y
    have hD : IdealSheafData.stalk (controlledTransformDivisorIdeal Z I) y =
        ∏ W : componentsOf (Z.support : Set X), Ideal.map ((blowUpToBase Z).stalkMap y).hom
          (IdealSheafData.stalk (componentsFamily (Z.support : Set X) W) x) ^
            (orderAlong I W.2.1.1).toNat := by
      unfold controlledTransformDivisorIdeal
      rw [finprod_eq_prod_of_fintype, stalk_prod]
      refine Finset.prod_congr rfl fun W _ => ?_
      rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
    rw [hD, IdealSheafData.stalk_pow, IdealSheafData.stalk_comap]
    by_cases hx : x ∈ (Z.support : Set X)
    · obtain ⟨W0, hW0, hxW0, huniq, hstalk, -⟩ := exists_component_through sX hX Z hZ I x hx
      rw [Finset.prod_eq_single (⟨W0, hW0⟩ : componentsOf (Z.support : Set X))]
      · rw [hstalk, hI W0 hW0]
        rfl
      · intro W _ hne
        have : x ∉ (W : Set X) := fun hxW => hne (Subtype.ext (huniq W W.2 hxW))
        simp [stalk_componentsFamily_eq_top Z W.2 this, Ideal.map_top]
      · simp
    · rw [(IdealSheafData.stalk_eq_top_iff_notMem_support Z x).2 hx]
      refine (Finset.prod_eq_one fun W _ => ?_).trans (by simp [Ideal.map_top, Ideal.top_pow])
      simp [stalk_componentsFamily_eq_top Z W.2 fun hxW => hx (W.2.1.2 hxW), Ideal.map_top]
  exact IdealSheafData.eq_of_stalk_eq _ _ key

/-- Cancellation of an effective Cartier divisor: `J·D = J'·D` implies `J = J'`. -/
private theorem eq_of_mul_eq_mul_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    {J J' : X.IdealSheafData} (h : J * D = J' * D) : J = J' := by
  have key : ∀ {A B : X.IdealSheafData}, A * D = B * D → A ≤ B := by
    intro A B hAB
    refine IdealSheafData.le_of_stalk_le _ _ fun y a ha => ?_
    obtain ⟨g, hg, hgs⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D hD y
    have hs := congrArg (fun K => IdealSheafData.stalk K y) hAB
    simp only [IdealSheafData.stalk_mul, hgs] at hs
    have hga : g * a ∈ Ideal.span {g} * IdealSheafData.stalk B y := by
      rw [← mul_comm (IdealSheafData.stalk B y), ← hs, mul_comm]
      exact Ideal.mem_span_singleton_mul.2 ⟨a, ha, rfl⟩
    obtain ⟨z, hz, hzg⟩ := Ideal.mem_span_singleton_mul.1 hga
    rwa [← hg.1 hzg]
  exact le_antisymm (key h) (key h.symm)

/-- A triple stays a triple when its ideal is replaced by one nonzero at the generic points. -/
private theorem isTriple_of_isNonzeroAtGenericPoints {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {K I : X.IdealSheafData} {E : OrderedDivisor X}
    (hK : IsTriple sX K E) (hI : IsNonzeroAtGenericPoints I) : IsTriple sX I E :=
  ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2.1, hI, hK.2.2.2.2.2.2⟩

/-- **One blow-up.** Along a smooth centre `Z` of positive codimension with
`ord_Z (N^m + I^s) = m·s`, one has `ord_Z N ≥ s`, `ord_Z I ≥ m`, and the controlled transform of
`N^m + I^s` is `N'^m + I'^s` for the birational transforms `(N', s)`, `(I', m)`. -/
private theorem step {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (I N : X.IdealSheafData) (E : OrderedDivisor X) (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hK : IsTriple sX (N ^ m + I ^ s) E) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X))
    (hord : OrderAlongEq (N ^ m + I ^ s) (Z.support : Set X) (m * s : ℕ)) :
    OrderAlongGE I (Z.support : Set X) m ∧ OrderAlongGE N (Z.support : Set X) s ∧
      controlledTransform Z (N ^ m + I ^ s) =
        (MarkedIdeal.birationalTransform Z ⟨N, s⟩).I ^ m +
          (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I ^ s := by
  obtain ⟨-, hX, hlft, hqc, -, hKnz, -⟩ := hK
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  haveI : Smooth sX := Aux.smooth_of_isSmoothScheme' sX hX
  have hords : ∀ W (hW : W ∈ componentsOf (Z.support : Set X)),
      (s : ℕ∞) ≤ orderAlong N hW.1.1 ∧ (m : ℕ∞) ≤ orderAlong I hW.1.1 := by
    intro W hW
    haveI : IsRegularLocalRing (X.presheaf.stalk hW.1.1.genericPoint) :=
      isRegularLocalRing_stalk_of_smooth_over_field sX _
    exact le_multAt_of_le_multAt_pow_add_pow _ N I hm hs (hord W hW).ge
  have hI : OrderAlongGE I (Z.support : Set X) m := fun W hW => (hords W hW).2
  have hN : OrderAlongGE N (Z.support : Set X) s := fun W hW => (hords W hW).1
  refine ⟨hI, hN, ?_⟩
  set F := Z.comap (blowUpToBase Z)
  have hF : Stacks.Divisors.IsEffectiveCartierDivisor F :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z
  have h1 : (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I * F ^ m = I.comap (blowUpToBase Z) :=
    MarkedIdeal.birationalTransform_mul_eq sX hX Z hZ hcodim ⟨I, m⟩ hI
  have h2 : (MarkedIdeal.birationalTransform Z ⟨N, s⟩).I * F ^ s = N.comap (blowUpToBase Z) :=
    MarkedIdeal.birationalTransform_mul_eq sX hX Z hZ hcodim ⟨N, s⟩ hN
  have h3 := controlledTransform_mul_eq sX hX Z hZ hcodim _ hKnz
  rw [controlledTransformDivisorIdeal_eq_pow sX hX Z hZ _ _ hord] at h3
  refine eq_of_mul_eq_mul_of_isEffectiveCartierDivisor
    (Stacks.Divisors.isEffectiveCartierDivisor_pow hF (m * s)) ?_
  have h4 : ((MarkedIdeal.birationalTransform Z ⟨N, s⟩).I ^ m +
      (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I ^ s) * F ^ (m * s) =
      ((MarkedIdeal.birationalTransform Z ⟨N, s⟩).I * F ^ s) ^ m +
        ((MarkedIdeal.birationalTransform Z ⟨I, m⟩).I * F ^ m) ^ s := by
    rw [add_mul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm s m]
  rw [h3, h4, h1, h2]
  change (N ^ m ⊔ I ^ s).comap _ = _
  rw [Scheme.IdealSheafData.comap_sup, Stacks.IdealSheaf.comap_pow, Stacks.IdealSheaf.comap_pow]
  rfl

/-- The statement for an arbitrary pair `(I, N)` in place of `(I, N(I))`. -/
private theorem isOrderGeMarkedTripleSeq_truncate_of_pow_add_pow {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (I N : X.IdealSheafData) (E : OrderedDivisor X) (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hI : IsNonzeroAtGenericPoints I) (hN : IsNonzeroAtGenericPoints N)
    (B : ClosedBlowupSequence X) (hB : B.IsOrderMTripleSeq sX (N ^ m + I ^ s) E (m * s))
    (i : ℕ) :
    (B.truncate i).IsOrderGeMarkedTripleSeq sX ⟨I, m⟩ E ∧
      (B.truncate i).IsOrderGeMarkedTripleSeq sX ⟨N, s⟩ E ∧
      (B.truncate i).controlledTransform (N ^ m + I ^ s) =
        ((B.truncate i).markedTransform ⟨N, s⟩).I ^ m +
          ((B.truncate i).markedTransform ⟨I, m⟩).I ^ s := by
  induction B generalizing i with
  | nil X =>
    exact ⟨isTriple_of_isNonzeroAtGenericPoints hB hI,
      isTriple_of_isNonzeroAtGenericPoints hB hN, rfl⟩
  | cons Z B ih =>
    have hK := hB.1
    cases i with
    | zero =>
      exact ⟨isTriple_of_isNonzeroAtGenericPoints hK hI,
        isTriple_of_isNonzeroAtGenericPoints hK hN, rfl⟩
    | succ i =>
      obtain ⟨-, hZ, hcodim, hsnc, hord, hB'⟩ := hB
      obtain ⟨hIZ, hNZ, heq⟩ := step sX I N E m s hm hs hK Z hZ hcodim hord
      rw [heq] at hB'
      have hI' : IsNonzeroAtGenericPoints (MarkedIdeal.birationalTransform Z ⟨I, m⟩).I :=
        isNonzeroAtGenericPoints_idealColon_comap Z hI _
      have hN' : IsNonzeroAtGenericPoints (MarkedIdeal.birationalTransform Z ⟨N, s⟩).I :=
        isNonzeroAtGenericPoints_idealColon_comap Z hN _
      obtain ⟨h1, h2, h3⟩ := ih _ _ _ _ hI' hN' hB' i
      refine ⟨⟨isTriple_of_isNonzeroAtGenericPoints hK hI, hZ, hcodim, hsnc, hIZ, h1⟩,
        ⟨isTriple_of_isNonzeroAtGenericPoints hK hN, hZ, hcodim, hsnc, hNZ, h2⟩, ?_⟩
      change (B.truncate i).controlledTransform (controlledTransform Z (N ^ m + I ^ s)) = _
      rw [heq]
      exact h3

namespace ClosedBlowupSequence

/-- **The mixed ideal along an order-`m·s` sequence** (Kollár 3.111, Step 2). Let `(X, I, m, E)`
be a marked triple with `m, s ≥ 1` and `maxOrder (mixedIdeal I E m s) ≤ m·s`, and let `B` be a
smooth blow-up sequence of order `m·s` starting with `(X, mixedIdeal I E m s, E)`. Then every
truncation `B.truncate i` is a smooth blow-up sequence of order `≥ m` starting with
`(X, I, m, E)` and of order `≥ s` starting with `(X, nonmonomialPart I E, s, E)`, and the
controlled transform of `mixedIdeal I E m s` along it is `N_i ^ m + I_i ^ s`, where `I_i`, `N_i`
are the iterated marked transforms of `(I, m)` and `(nonmonomialPart I E, s)`. -/
@[mmp "lem_kr3e_mixed_ideal_sequence"]
public theorem isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal {k : Type u}
    [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (E : OrderedDivisor X) (m s : ℕ) (hT : IsTriple sX I E) (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hK : maxOrder (mixedIdeal I E m s) ≤ ((m * s : ℕ) : ℕ∞)) (B : ClosedBlowupSequence X)
    (hB : B.IsOrderMTripleSeq sX (mixedIdeal I E m s) E (m * s)) (i : ℕ) :
    (B.truncate i).IsOrderGeMarkedTripleSeq sX ⟨I, m⟩ E ∧
      (B.truncate i).IsOrderGeMarkedTripleSeq sX ⟨nonmonomialPart I E, s⟩ E ∧
      (B.truncate i).controlledTransform (mixedIdeal I E m s) =
        ((B.truncate i).markedTransform ⟨nonmonomialPart I E, s⟩).I ^ m +
          ((B.truncate i).markedTransform ⟨I, m⟩).I ^ s := by
  have hI : IsNonzeroAtGenericPoints I := hT.2.2.2.2.2.1
  have hN : IsNonzeroAtGenericPoints (nonmonomialPart I E) := fun η hη h =>
    hI η hη (eq_bot_iff.2 (h ▸ stalk_le_stalk_of_le (le_idealColon _ _) η))
  exact isOrderGeMarkedTripleSeq_truncate_of_pow_add_pow sX I _ E m s hm hs hI hN B hB i

end ClosedBlowupSequence

section ReductionToMonomial

variable {k : Type u} [Field k]

/-- The order of an ideal does not drop under an isomorphism of local rings: if
`m ≤ ord (φ J)` then `m ≤ ord J`. -/
private theorem natCast_le_idealOrder_of_map {R S : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing S] (φ : R ⟶ S) [IsIso φ] {J : Ideal R} {m : ℕ}
    (h : (m : ℕ∞) ≤ idealOrder (J.map φ.hom)) : (m : ℕ∞) ≤ idealOrder J := by
  rw [natCast_le_idealOrder_iff'] at h ⊢
  have hJ : J = (J.map φ.hom).map (inv φ).hom := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
  rw [hJ]
  refine (Ideal.map_mono h).trans ?_
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono
    (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap _).ge) m

/-- Along an open immersion, `m ≤ ord_u (j^*I)` gives `m ≤ ord_{j u} I`. -/
public theorem le_multAt_of_le_multAt_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (u : U) {m : ℕ} (h : (m : ℕ∞) ≤ multAt (I.comap j) u) :
    (m : ℕ∞) ≤ multAt I (j u) := by
  unfold multAt at h ⊢
  rw [IdealSheafData.stalk_comap] at h
  haveI : IsIso (j.stalkMap u) := inferInstanceAs <| IsIso (j.toLRSHom.stalkMap u)
  exact natCast_le_idealOrder_of_map (j.stalkMap u) (J := IdealSheafData.stalk I (j u)) h

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- A closed subset `C` in the image of an open embedding `f` is an irreducible component of
`D` exactly when `f⁻¹C` is an irreducible component of `f⁻¹D`. -/
private theorem mem_componentsOf_iff_preimage (hf : Topology.IsOpenEmbedding f) {D C : Set α}
    (hC : IsClosed C) (hCf : C ⊆ Set.range f) :
    C ∈ componentsOf D ↔ f ⁻¹' C ∈ componentsOf (f ⁻¹' D) := by
  constructor
  · rintro ⟨⟨hirr, hCD⟩, hmax⟩
    have hne : (f ⁻¹' C).Nonempty := by
      obtain ⟨c, hc⟩ := hirr.nonempty
      obtain ⟨b, rfl⟩ := hCf hc
      exact ⟨b, hc⟩
    refine ⟨⟨⟨hne, hirr.isPreirreducible.preimage hf⟩, Set.preimage_mono hCD⟩, ?_⟩
    rintro T ⟨hT, hTD⟩ hle
    exact Set.image_subset_iff.1 (hmax ⟨hT.image f hf.continuous.continuousOn,
      (Set.image_mono hTD).trans (Set.image_preimage_subset f D)⟩
      ((Set.image_preimage_eq_of_subset hCf).superset.trans (Set.image_mono hle)))
  · rintro ⟨⟨hirr, hCD⟩, hmax⟩
    have hCeq : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCf
    refine ⟨⟨hCeq ▸ hirr.image f hf.continuous.continuousOn, ?_⟩, ?_⟩
    · rw [← hCeq]
      exact (Set.image_mono hCD).trans (Set.image_preimage_subset f D)
    · rintro S ⟨hS, hSD⟩ hle
      have hSne : (f ⁻¹' S).Nonempty := hirr.nonempty.mono (Set.preimage_mono hle)
      have h1 := hmax ⟨⟨hSne, hS.isPreirreducible.preimage hf⟩, Set.preimage_mono hSD⟩
        (Set.preimage_mono hle)
      have hSU : (S ∩ Set.range f).Nonempty := by
        obtain ⟨b, hb⟩ := hSne
        exact ⟨f b, hb, b, rfl⟩
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen hS.isPreirreducible
        hf.isOpen_range hSU).trans (hC.closure_subset_iff.2 ?_)
      rintro _ ⟨hx, b, rfl⟩
      exact h1 hx

/-- `closure (f '' closure (f⁻¹C)) = closure C` for `C` in the image of a continuous `f`. -/
private theorem closure_image_closure_preimage (hf : Continuous f) {C : Set α}
    (hCf : C ⊆ Set.range f) : closure (f '' closure (f ⁻¹' C)) = closure C := by
  rw [closure_image_closure hf, Set.image_preimage_eq_of_subset hCf]

end Topology

/-- The codimension of an irreducible closed subset meeting the image of an open immersion
`j` is that of its inverse image under `j`. -/
private theorem codimension_irreducibleClosure_preimage {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {C : Set X} (hC : IsIrreducible C) (hC' : IsIrreducible (j ⁻¹' C))
    (hCf : C ⊆ Set.range j) :
    codimension (irreducibleClosure hC) = codimension (irreducibleClosure hC') := by
  have hf := j.isOpenEmbedding
  have hmap : irreducibleClosure hC =
      TopologicalSpace.IrreducibleCloseds.map j hf.continuous (irreducibleClosure hC') := by
    ext1
    exact (closure_image_closure_preimage hf.continuous hCf).symm
  rw [hmap, codimension_eq_coheight, codimension_eq_coheight]
  refine (Order.coheight_eq_of_strictMono _
    (TopologicalSpace.IrreducibleCloseds.map_strictMono_of_isInducing hf.isInducing) ?_ _).symm
  intro a b hab
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding j hf
  have hb : (j ⁻¹' (b : Set X)).Nonempty := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    exact ⟨x, hab.le (subset_closure ⟨x, hx, rfl⟩)⟩
  refine ⟨e.symm ⟨b, hb⟩, ?_, ?_⟩
  · rw [← e.lt_iff_lt, OrderIso.apply_symm_apply]
    exact hab
  · exact congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)

/-- The support of `j⁻¹I` is the inverse image of the support of `I`. -/
private theorem coe_support_comap {U X : Scheme.{u}} (j : U ⟶ X) (I : X.IdealSheafData) :
    ((I.comap j).support : Set U) = j ⁻¹' (I.support : Set X) :=
  Set.ext (mem_support_comap_iff j I)

/-- Along an open immersion `j` whose image contains `supp W`, the inverse image of an
irreducible component of `supp W` is an irreducible component of `supp j⁻¹W`. -/
private theorem preimage_mem_componentsOf_support_comap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (W : X.IdealSheafData) (hsupp : (W.support : Set X) ⊆ Set.range j)
    {C : Set X} (hC : C ∈ componentsOf (W.support : Set X)) :
    j ⁻¹' C ∈ componentsOf ((W.comap j).support : Set U) := by
  rw [coe_support_comap]
  exact (mem_componentsOf_iff_preimage j.isOpenEmbedding
    (Aux.isClosed_of_mem_componentsOf W.support.2 hC) (hC.1.2.trans hsupp)).1 hC

/-- snc with the boundary lifts from `U` to `X` along an open immersion containing the centre. -/
public theorem hasSNCWith_of_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : OrderedDivisor X) (W : X.IdealSheafData)
    (hsupp : (W.support : Set X) ⊆ Set.range j)
    (h : HasSNCWith (E.comap j).E (W.comap j)) : HasSNCWith E.E W := by
  intro x hx
  obtain ⟨u, rfl⟩ := hsupp hx
  obtain ⟨n, z, c, J, hz, hE, hinj, hZ⟩ := h u ((mem_support_comap_iff j W u).2 hx)
  haveI : IsIso (j.stalkMap u) := inferInstanceAs <| IsIso (j.toLRSHom.stalkMap u)
  let e' := (asIso (j.stalkMap u)).commRingCatIsoToRingEquiv
  have hmem : ∀ i, u ∈ ((E.comap j).E i).support ↔ j u ∈ (E.E i).support := fun i =>
    mem_support_comap_iff j (E.E i) u
  have hback : ∀ (K : X.IdealSheafData) (A : Ideal (U.presheaf.stalk u)),
      IdealSheafData.stalk (K.comap j) u = A →
        IdealSheafData.stalk K (j u) = A.map (e'.symm : _ →+* _) := by
    intro K A hA
    rw [IdealSheafData.stalk_comap] at hA
    rw [← hA]
    exact (Ideal.map_of_equiv (f := e')).symm
  refine ⟨n, fun i => e'.symm (z i), fun i => c ⟨i.1, (hmem i.1).2 i.2⟩, J,
    isRegularSystemOfParameters_map_ringEquiv e'.symm hz, ?_, ?_, ?_⟩
  · intro i
    rw [hback _ _ (hE ⟨i.1, (hmem i.1).2 i.2⟩), Ideal.map_span, Set.image_singleton]
    rfl
  · intro i i' hii
    exact Subtype.ext (congrArg (fun t => t.1) (hinj hii))
  · rw [hback _ _ hZ, Ideal.map_span, ← Set.image_comp]
    rfl

/-- Positive codimension of the components of the centre lifts from `U` to `X`. -/
public theorem hasComponentsOfPositiveCodim_of_comap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (W : X.IdealSheafData) (hsupp : (W.support : Set X) ⊆ Set.range j)
    (h : HasComponentsOfPositiveCodim ((W.comap j).support : Set U)) :
    HasComponentsOfPositiveCodim (W.support : Set X) := by
  intro C hC
  have hpre := preimage_mem_componentsOf_support_comap j W hsupp hC
  rw [codimension_irreducibleClosure_preimage j hC.1.1 hpre.1.1 (hC.1.2.trans hsupp)]
  exact h _ hpre

/-- The order bound along the centre lifts from `U` to `X`. -/
public theorem orderAlongGE_of_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.IdealSheafData) (hsupp : (W.support : Set X) ⊆ Set.range j) (I : X.IdealSheafData)
    (m : ℕ) (h : OrderAlongGE (I.comap j) ((W.comap j).support : Set U) m) :
    OrderAlongGE I (W.support : Set X) m := by
  intro C hC
  have hpre := preimage_mem_componentsOf_support_comap j W hsupp hC
  have h1 := le_multAt_of_le_multAt_comap j I _ (h _ hpre)
  have hg : j hpre.1.1.genericPoint = hC.1.1.genericPoint := by
    have h2 := hpre.1.1.isGenericPoint_genericPoint_closure.image j.continuous
    rw [closure_image_closure_preimage j.continuous (hC.1.2.trans hsupp)] at h2
    exact h2.eq hC.1.1.isGenericPoint_genericPoint_closure
  unfold orderAlong
  rwa [← hg]

/-- The birational transform commutes with restriction along an open immersion `j`: that of
`(j^*a.I, a.m)` along `j⁻¹W` is the pull-back of that of `a` along `canonicalLift j W`. -/
public theorem birationalTransform_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (s : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme s) (W : X.IdealSheafData)
    (hW : MMP.Mori.IsSmoothScheme (W.subschemeι ≫ s))
    (hcod : HasComponentsOfPositiveCodim (W.support : Set X)) (a : MarkedIdeal X)
    (hord : OrderAlongGE a.I (W.support : Set X) a.m)
    (hU : MMP.Mori.IsSmoothScheme (j ≫ s))
    (hWU : MMP.Mori.IsSmoothScheme ((W.comap j).subschemeι ≫ j ≫ s))
    (hcodU : HasComponentsOfPositiveCodim ((W.comap j).support : Set U))
    (hordU : OrderAlongGE (a.I.comap j) ((W.comap j).support : Set U) a.m) :
    (⟨a.I.comap j, a.m⟩ : MarkedIdeal U).birationalTransform (W.comap j) =
      ⟨(a.birationalTransform W).I.comap (canonicalLift j W), (a.birationalTransform W).m⟩ := by
  have hc := canonicalLift_comp_blowUpToBase j W
  have hDc : Stacks.Divisors.IsEffectiveCartierDivisor
      ((W.comap j).comap (blowUpToBase (W.comap j)) ^ a.m) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (W.comap j)) a.m
  have h1 := MarkedIdeal.birationalTransform_mul_eq (j ≫ s) hU (W.comap j) hWU hcodU
    ⟨a.I.comap j, a.m⟩ hordU
  have h2 := MarkedIdeal.birationalTransform_mul_eq s hX W hW hcod a hord
  have hF : (W.comap j).comap (blowUpToBase (W.comap j)) =
      (W.comap (blowUpToBase W)).comap (canonicalLift j W) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  have h3 : (a.birationalTransform W).I.comap (canonicalLift j W) *
      (W.comap j).comap (blowUpToBase (W.comap j)) ^ a.m =
      (a.I.comap j).comap (blowUpToBase (W.comap j)) := by
    rw [hF, ← Stacks.IdealSheaf.comap_pow, ← Stacks.IdealSheaf.comap_mul, h2,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hc]
  have := eq_of_mul_eq_mul_of_isEffectiveCartierDivisor hDc (h1.trans h3.symm)
  change MarkedIdeal.mk _ a.m = MarkedIdeal.mk _ a.m
  rw [← this]
  rfl

/-- An irreducible component of `j⁻¹D`, for `D` closed in the image of `j`, is the inverse image
of an irreducible component of `D`. -/
private theorem exists_mem_componentsOf_preimage_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {D : Set X} (hD : IsClosed D) (hDj : D ⊆ Set.range j) {T : Set U}
    (hT : T ∈ componentsOf (j ⁻¹' D)) : ∃ C, C ∈ componentsOf D ∧ j ⁻¹' C = T := by
  have hTc : IsClosed T := Aux.isClosed_of_mem_componentsOf (hD.preimage j.continuous) hT
  have hCD : closure (j '' T) ⊆ D :=
    closure_minimal ((Set.image_mono hT.1.2).trans (Set.image_preimage_subset _ _)) hD
  have hpre : j ⁻¹' closure (j '' T) = T := by
    rw [j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous,
      Set.preimage_image_eq _ j.isOpenEmbedding.injective, hTc.closure_eq]
  refine ⟨closure (j '' T), ?_, hpre⟩
  rw [mem_componentsOf_iff_preimage j.isOpenEmbedding isClosed_closure (hCD.trans hDj), hpre]
  exact hT

/-- `j⁻¹(Z^{≥2}) = (j⁻¹Z)^{≥2}` for a closed `Z` in the image of an open immersion `j`. -/
private theorem preimage_componentsOfCodimAtLeastTwo {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {D : Set X} (hD : IsClosed D) (hDj : D ⊆ Set.range j) :
    j ⁻¹' componentsOfCodimAtLeastTwo D = componentsOfCodimAtLeastTwo (j ⁻¹' D) := by
  ext y
  simp only [componentsOfCodimAtLeastTwo, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨C, hC, hcod, hy⟩
    have hCf : C ⊆ Set.range j := hC.1.2.trans hDj
    have hpre := (mem_componentsOf_iff_preimage j.isOpenEmbedding
      (Aux.isClosed_of_mem_componentsOf hD hC) hCf).1 hC
    refine ⟨j ⁻¹' C, hpre, ?_, hy⟩
    rwa [← codimension_irreducibleClosure_preimage j hC.1.1 hpre.1.1 hCf]
  · rintro ⟨T, hT, hcod, hy⟩
    obtain ⟨C, hC, rfl⟩ := exists_mem_componentsOf_preimage_eq j hD hDj hT
    refine ⟨C, hC, ?_, hy⟩
    rwa [codimension_irreducibleClosure_preimage j hC.1.1 hT.1.1 (hC.1.2.trans hDj)]

/-- Pulling back along the blow-up and then the canonical lift is pulling back along `j` and
then the blow-up of `j⁻¹W`. -/
public theorem preimage_canonicalLift_preimage_blowUpToBase {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (W : X.IdealSheafData) (S : Set X) :
    canonicalLift j W ⁻¹' (blowUpToBase W ⁻¹' S) = blowUpToBase (W.comap j) ⁻¹' (j ⁻¹' S) := by
  rw [← Set.preimage_comp, ← Set.preimage_comp, ← TopCat.coe_comp, ← TopCat.coe_comp,
    ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, canonicalLift_comp_blowUpToBase]

/-- The sets cut out by the total transform commute with restriction to the open `U`. -/
private theorem totalTransformSet_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : OrderedDivisor X) (W : X.IdealSheafData)
    (hsupp : (W.support : Set X) ⊆ Set.range j) (i : Fin (E.s + 1)) :
    totalTransformSet (E.comap j) (W.comap j) i =
      canonicalLift j W ⁻¹' totalTransformSet E W i := by
  have hfun := preimage_canonicalLift_preimage_blowUpToBase j W
  have hsc := coe_support_comap j W
  have hsE : ∀ i, (((E.E i).comap j).support : Set U) = j ⁻¹' ((E.E i).support : Set X) :=
    fun i => coe_support_comap j (E.E i)
  have hEs : OrderedDivisor.support (⟨E.s, fun i => (E.E i).comap j⟩ : OrderedDivisor U) =
      j ⁻¹' E.support := by
    simp only [OrderedDivisor.support, Set.preimage_iUnion]
    exact Set.iUnion_congr hsE
  have hWc : IsClosed (W.support : Set X) := W.support.2
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [OrderedDivisor.comap, totalTransformSet, Fin.snoc_last, Set.preimage_iUnion,
      hfun]
    rw [hEs, hsc]
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨T, hT, hTE, hy⟩
      obtain ⟨C, hC, rfl⟩ := exists_mem_componentsOf_preimage_eq j hWc hsupp hT
      refine ⟨C, hC, fun hCE => hTE ?_, hy⟩
      exact (mem_componentsOf_iff_preimage j.isOpenEmbedding
        (Aux.isClosed_of_mem_componentsOf hWc hC) (hC.1.2.trans hsupp)).1 hCE
    · rintro ⟨C, hC, hCE, hy⟩
      have hCc := Aux.isClosed_of_mem_componentsOf hWc hC
      have hCf : C ⊆ Set.range j := hC.1.2.trans hsupp
      refine ⟨j ⁻¹' C, (mem_componentsOf_iff_preimage j.isOpenEmbedding hCc hCf).1 hC,
        fun hTE => hCE ?_, hy⟩
      exact (mem_componentsOf_iff_preimage j.isOpenEmbedding hCc hCf).2 hTE
  · simp only [totalTransformSet, Fin.snoc_castSucc, OrderedDivisor.comap]
    rw [hfun, hsc, hsE, ← preimage_componentsOfCodimAtLeastTwo j hWc hsupp]
    simp only [Set.preimage_diff]

/-- The total transform commutes with restriction to the open `U`. -/
public theorem totalTransform_comap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : OrderedDivisor X) (W : X.IdealSheafData)
    (hsupp : (W.support : Set X) ⊆ Set.range j) :
    (E.comap j).totalTransform (W.comap j) = (E.totalTransform W).comap (canonicalLift j W) := by
  set cl := canonicalLift j W
  have sq := Kollar.isPullback_canonicalLift_of_flat j W
  haveI : IsOpenImmersion cl := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›
  have hvan : ∀ S : Set (blowUp W),
      (Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure S)).comap cl =
        Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (cl ⁻¹' S)) :=
    fun S => IsReducedFlatBaseChange.comap_vanishingIdeal (IsReducedFlatBaseChange.of_smooth cl)
      _ _ (cl.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
        cl.continuous S).symm
  have key : ∀ i : Fin (E.s + 1), ((E.comap j).totalTransform (W.comap j)).E i =
      ((E.totalTransform W).E i).comap cl := by
    intro i
    have h1 := totalTransform_E_eq (E.comap j) (W.comap j) i
    rw [totalTransformSet_comap j E W hsupp i] at h1
    rw [h1, totalTransform_E_eq E W i, hvan]
  exact congrArg (OrderedDivisor.mk (E.s + 1)) (funext key)

/-- The image of the canonical lift `B_{j⁻¹W} U → B_W X` is the inverse image under
`blowUpToBase W` of the image of `j`. -/
public theorem range_canonicalLift {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (W : X.IdealSheafData) :
    Set.range (canonicalLift j W) = blowUpToBase W ⁻¹' Set.range j := by
  have sq := Kollar.isPullback_canonicalLift_of_flat j W
  have hs : Function.Surjective sq.isoPullback.hom := sq.isoPullback.hom.surjective
  rw [← sq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hs.range_eq, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

/-- A centre of order `≥ m` for `j^*I` maps into `cosupp(I, m)`. -/
public theorem image_subset_cosupport {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (s : X ⟶ Spec (.of k)) (hU : MMP.Mori.IsSmoothScheme (j ≫ s)) (Z : U.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ j ≫ s)) (a : MarkedIdeal X)
    (hord : OrderAlongGE (a.I.comap j) (Z.support : Set U) a.m) :
    j '' (Z.support : Set U) ⊆ a.cosupport := by
  rintro _ ⟨u, hu, rfl⟩
  refine le_multAt_of_le_multAt_comap j a.I u ?_
  change (a.m : ℕ∞) ≤ idealOrder _
  rw [natCast_le_idealOrder_iff']
  refine (stalk_le_pow_of_orderAlongGE (j ≫ s) hU Z hZ (a.I.comap j) a.m hord u).trans ?_
  refine Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal fun h => ?_) a.m
  exact ((IdealSheafData.stalk_eq_top_iff_notMem_support Z u).1 h) hu

/-- The statement proved by induction: the extension by closure along a quasi-compact open
immersion `j` whose image contains `cosupp(a)`. -/
private def Claim {U : Scheme.{u}} (B : ClosedBlowupSequence U) : Prop :=
  ∀ {X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X),
    1 ≤ a.m → IsTriple s a.I E → a.cosupport ⊆ Set.range j →
    B.IsOrderGeMarkedTripleSeq (j ≫ s) ⟨a.I.comap j, a.m⟩ (E.comap j) →
    (B.extendByClosure j).IsOrderGeMarkedTripleSeq s a E

/-- The inductive step: a centre `Z ⊆ U` whose image `W` has support in `j(U)`. -/
private theorem isOrderGeMarkedTripleSeq_cons_extendByClosure {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) (hm : 1 ≤ a.m)
    (ht : IsTriple s a.I E) (hcos : a.cosupport ⊆ Set.range j) (W : X.IdealSheafData)
    (Z : U.IdealSheafData) (h : W.comap j = Z) (hsupp : (W.support : Set X) ⊆ Set.range j)
    (B : ClosedBlowupSequence (blowUp Z)) (ih : Claim (k := k) B)
    (htU : IsTriple (j ≫ s) (a.I.comap j) (E.comap j))
    (hZsm : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ j ≫ s))
    (hZcod : HasComponentsOfPositiveCodim (Z.support : Set U))
    (hZsnc : HasSNCWith (E.comap j).E Z)
    (hZord : OrderAlongGE (a.I.comap j) (Z.support : Set U) a.m)
    (hB' : B.IsOrderGeMarkedTripleSeq (blowUpToBase Z ≫ j ≫ s)
      ((⟨a.I.comap j, a.m⟩ : MarkedIdeal U).birationalTransform Z)
      ((E.comap j).totalTransform Z)) :
    (ClosedBlowupSequence.cons W (B.extendByClosure
      (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j W))).IsOrderGeMarkedTripleSeq s a E := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  have hsnc := hasSNCWith_of_comap j E W hsupp hZsnc
  have hWsm : MMP.Mori.IsSmoothScheme (W.subschemeι ≫ s) :=
    isSmoothScheme_of_hasSNCWith ⟨⟨X, a.I, E⟩, k, s⟩ ht W hsnc
  have hcod := hasComponentsOfPositiveCodim_of_comap j W hsupp hZcod
  have hord := orderAlongGE_of_comap j W hsupp a.I a.m hZord
  have sq := Kollar.isPullback_canonicalLift_of_flat j W
  haveI : IsOpenImmersion (canonicalLift j W) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›
  haveI : QuasiCompact (canonicalLift j W) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq ‹_›
  refine ⟨ht, hWsm, hcod, hsnc, hord, ?_⟩
  refine ih (canonicalLift j W) (blowUpToBase W ≫ s) (a.birationalTransform W)
    (E.totalTransform W) hm (isTriple_birationalTransform_totalTransform a ht hsnc) ?_ ?_
  · have hB1 : (ClosedBlowupSequence.cons W (.nil _)).IsOrderGeMarkedTripleSeq s a E :=
      ⟨ht, hWsm, hcod, hsnc, hord, isTriple_birationalTransform_totalTransform a ht hsnc⟩
    refine (ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s a E _ hB1 1).trans ?_
    rw [range_canonicalLift]
    intro x hx
    simp only [ClosedBlowupSequence.truncate, ClosedBlowupSequence.toBase, Category.id_comp,
      Set.mem_preimage] at hx
    exact hcos hx
  · rw [← birationalTransform_comap j s ht.2.1 W hWsm hcod a hord htU.2.1 hZsm hZcod hZord,
      ← totalTransform_comap j E W hsupp, ← Category.assoc, canonicalLift_comp_blowUpToBase,
      Category.assoc]
    exact hB'

/-- `Claim` holds for every sequence, by induction along it. -/
private theorem claim_extendByClosure_aux {U : Scheme.{u}} (B : ClosedBlowupSequence U) :
    Claim (k := k) B := by
  induction B with
  | nil U =>
    intro X j _ _ s a E _ ht _ _
    exact ht
  | cons Z B ih =>
    intro X j _ _ s a E hm ht hcos hB
    obtain ⟨htU, hZsm, hZcod, hZsnc, hZord, hB'⟩ := hB
    rw [ClosedBlowupSequence.extendByClosure,
      dif_pos (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion j Z)]
    have hsupp : ((Z.map j).support : Set X) ⊆ Set.range j := by
      haveI : CharZero k := ht.1
      haveI : LocallyOfFiniteType s := ht.2.2.1
      haveI : Smooth s := (MMP.Mori.isSmoothScheme_iff s).mp ht.2.1
      rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure]
      exact (closure_minimal (image_subset_cosupport j s htU.2.1 Z hZsm a hZord)
        (isClosed_setOf_le_multAt s a.I a.m)).trans hcos
    exact isOrderGeMarkedTripleSeq_cons_extendByClosure j s a E hm ht hcos (Z.map j) Z
      (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion j Z) hsupp B ih htU hZsm hZcod
      hZsnc hZord hB'

/-- **Extension by closure along an open immersion.** Let `(X, a, E)` be a marked triple with
`a.m ≥ 1`, and let `j : U → X` be a quasi-compact open immersion whose image contains
`cosupp a`. The extension by closure along `j` of a smooth blow-up sequence of order `≥ a.m`
starting with `(U, j^*a.I, a.m, j^*E)` is a smooth blow-up sequence of order `≥ a.m` starting
with `(X, a, E)`. -/
public theorem ClosedBlowupSequence.isOrderGeMarkedTripleSeq_extendByClosure_of_cosupport_subset
    {U X : Scheme.{u}} (B : ClosedBlowupSequence U) (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (hm : 1 ≤ a.m) (ht : IsTriple s a.I E) (hcos : a.cosupport ⊆ Set.range j)
    (hB : B.IsOrderGeMarkedTripleSeq (j ≫ s) ⟨a.I.comap j, a.m⟩ (E.comap j)) :
    (B.extendByClosure j).IsOrderGeMarkedTripleSeq s a E :=
  claim_extendByClosure_aux B j s a E hm ht hcos hB

end ReductionToMonomial

namespace ClosedBlowupSequence

/-- Let `(X, I, m, E)` be a marked triple with `m ≥ 1` and `cosupp(I, m)` disjoint from
`cosupp N(I)`, `N(I) = nonmonomialPart I E`, and let `U = X ∖ cosupp N(I)`. The extension by
closure to `X` of a smooth blow-up sequence of order `≥ m` starting with `(U, I|_U, m, E|_U)` is a
smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`. -/
@[mmp "lem_kr3e_reduction_to_monomial"]
public theorem isOrderGeMarkedTripleSeq_extendByClosure {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : OrderedDivisor X) (ht : IsTriple s I E) (hm : 1 ≤ m)
    (hdisj : Disjoint (⟨I, m⟩ : MarkedIdeal X).cosupport
      ((nonmonomialPart I E).support : Set X))
    (U : X.Opens) (hU : U = (nonmonomialPart I E).support.compl)
    (B : ClosedBlowupSequence U)
    (hB : B.IsOrderGeMarkedTripleSeq (U.ι ≫ s) ⟨I.comap U.ι, m⟩ (E.comap U.ι)) :
    (B.extendByClosure U.ι).IsOrderGeMarkedTripleSeq s ⟨I, m⟩ E := by
  haveI : LocallyOfFiniteType s := ht.2.2.1
  haveI : QuasiCompact s := ht.2.2.2.1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := ⟨⟩
  haveI : TopologicalSpace.NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set X)
  have hcos : (⟨I, m⟩ : MarkedIdeal X).cosupport ⊆ Set.range U.ι := by
    intro x hx
    rw [Scheme.Opens.range_ι, hU]
    exact fun h => Set.disjoint_left.1 hdisj hx h
  exact B.isOrderGeMarkedTripleSeq_extendByClosure_of_cosupport_subset U.ι s ⟨I, m⟩ E hm ht
    hcos hB

end ClosedBlowupSequence

end MMP.Resolution

end
