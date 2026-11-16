module

public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion

/-!
# Base change of the ground field: schemes, morphisms, curves and Cartier divisors

Let `k₀ ⊆ K` be fields with `k₀` algebraically closed, and let `π : X ⟶ X₀` be the base change
of a scheme `X₀` over `k₀` along `Spec K ⟶ Spec k₀`, given by a pullback square. This file
collects the comparisons between `X₀` and `X` that do not involve canonical divisors:

* the projection `π` is surjective, flat and quasi-compact, and a point of `X` whose closure is
  `π⁻¹(closure x)` lies over `x`;
* snc closed subsets are supports of snc divisors;
* birationality of a morphism of integral schemes is read off its generic fibre, which is
  insensitive to base change, and so is the exceptional set of a birational morphism to a normal
  target;
* a curve is contracted by a morphism exactly when an ample degree vanishes on it, and proper
  curves on `X₀` base change to proper curves on `X` with the same degrees;
* the sheaf of the pull-back of a Cartier divisor along a dominant morphism of integral schemes
  is the pull-back of its sheaf, and Cartier divisors on a projective variety pull back along `π`;
* the predicate `MMP.ProgramBaseChange.IsBaseChange` saying that a divisor on `X` is the base
  change of a divisor on `X₀`.

## Main definitions

* `MMP.ProgramBaseChange.IsBaseChange`: a divisor on `X` is the base change of one on `X₀`
  along `π`, prime divisor by prime divisor.

## Main results

* `MMP.ProgramBaseChange.isBirationalMorphism_iff_isIso_fiberToSpecResidueField`: a morphism of
  integral schemes is birational exactly when its generic fibre is the spectrum of the function
  field of the target.
* `MMP.ProgramBaseChange.coe_exceptionalSet_eq_preimage_of_isPullback`: the exceptional set of
  a base-changed birational morphism is the preimage of the exceptional set.
* `MMP.ProgramBaseChange.exists_properCurve_baseChange`: proper curves base change to proper
  curves with the same degrees.
* `MMP.ProgramBaseChange.nonempty_pullback_sheaf_iso`: the sheaf of a pull-back Cartier divisor
  is the pull-back of the sheaf.

## References

* [KM98] Kollár, Mori, *Birational Geometry of Algebraic Varieties*.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MMP.Mori MMP.Fourfold

universe u

namespace MMP.ProgramBaseChange

section FieldChangeBasics

/-- The morphism `Spec L ⟶ Spec k` of a field extension is surjective, flat and quasi-compact. -/
public lemma specMap_mem_surjective_flat_quasiCompact {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom σ)) := by
  have h1 : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have h2 : Flat (Spec.map (CommRingCat.ofHom σ)) :=
    Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField _) _)
  exact ⟨⟨h1, h2⟩, inferInstance⟩

/-- A scheme isomorphic to a normal scheme is normal. -/
public lemma isNormal_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [IsNormal Y] : IsNormal X := by
  have hr (x : X) := @asIso _ _ _ _ (e.hom.stalkMap x)
    (IsOpenImmersion.instIsIsoCommRingCatStalkMap e.hom x)
  have hd (x : X) : IsDomain (X.presheaf.stalk x) := by
    have := IsNormal.stalk_isDomain (X := Y) (e.hom x)
    exact (hr x).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain
  exact ⟨hd, fun x => IsIntegrallyClosed.of_equiv (hr x).commRingCatIsoToRingEquiv⟩

end FieldChangeBasics

/-- The projection of a base change along `Spec K ⟶ Spec k₀` is surjective. -/
public lemma surjective_of_isPullback {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    {X₀ X : Scheme.{u}} {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) : Surjective π :=
  MorphismProperty.of_isPullback (P := @Surjective) h.flip
    (specMap_mem_surjective_flat_quasiCompact (algebraMap k₀ K)).1.1

/-- A point lying over `x` whose closure is `π⁻¹(closure x)` maps to `x`. -/
public theorem map_eq_of_closure_eq {X₀ X : Scheme.{u}} {π : X ⟶ X₀} [Surjective π] {x : X₀}
    {w : X} (hw : closure {w} = π.base ⁻¹' closure {x}) : π w = x := by
  obtain ⟨w', hw'⟩ := π.surjective x
  have hw'm : w' ∈ closure {w} := by
    rw [hw, Set.mem_preimage, hw']; exact subset_closure rfl
  have a : π w ⤳ x := hw' ▸ (specializes_iff_mem_closure.mpr hw'm).map π.continuous
  have b : x ⤳ π w := by
    have : w ∈ π.base ⁻¹' closure {x} := hw ▸ subset_closure rfl
    exact specializes_iff_mem_closure.mpr this
  exact (a.antisymm b).eq

/-! ### Snc closed subsets and snc divisors -/

section SNCBridge

open MMP.Resolution TopologicalSpace

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}

/-- A variety is a Noetherian scheme. -/
public theorem isNoetherian_of_isVariety (h : AlgebraicGeometry.IsVariety k sY) :
    IsNoetherian Y := by
  have : LocallyOfFiniteType sY := h.toLocallyOfFiniteType
  have : QuasiCompact sY := h.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  exact ⟨⟩

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {P Q : MMP.Mori.PrimeDivisor Y}
    (h : (P.support : Set Y) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- The ideal sheaf of a prime divisor is the vanishing ideal of its support. -/
private theorem idealSheaf_eq_vanishingIdeal (P : MMP.Mori.PrimeDivisor Y)
    {T : Closeds Y} (hT : (T : Set Y) = P.support) :
    P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal T := by
  have := P.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ (Closeds.ext hT.symm)

/-- The reduced divisor with components a finite set `s` of prime divisors has support `s`. -/
private theorem support_sum_single (s : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ) : Divisor Y).support = s := by
  classical
  ext E
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- A component of a closed subset of pure codimension one is the closure of a point of
codimension one. -/
public theorem exists_coheight_eq_one_of_mem_componentsOf {S : Set Y} (hSc : IsClosed S)
    (hS : MMP.Mori.IsPureCodimOne (⟨S, hSc⟩ : Closeds Y)) {V : Set Y}
    (hV : V ∈ componentsOf S) : ∃ ξ : Y, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf hSc hV
  refine ⟨ξ, hξ, ?_⟩
  rw [← MMP.Flips.codimension_closureSingleton]
  apply hS
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ S
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set Y) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hξ]; exact hle)
    change (W' : Set Y) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- The support of a prime divisor contained in an snc closed subset `S` is an irreducible
component of `S`. -/
private theorem support_mem_componentsOf [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) {P : MMP.Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ S) :
    (P.support : Set Y) ∈ componentsOf S := by
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := hS
  · exfalso
    have := hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
    rw [hempty] at this
    exact this
  · obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf hSc
    obtain ⟨W, hW, hηW⟩ := hcov (hP (MMP.Flips.primeDivisor_genericPoint_mem_support P))
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    have hsp : ξ ⤳ P.genericPoint := specializes_iff_mem_closure.mpr (hWξ ▸ hηW)
    have hξη : ξ = P.genericPoint := by
      by_contra hne
      have hlt : P.genericPoint < ξ := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp)
        fun hle => hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq
      have := Order.coheight_strictAnti hlt
      rw [hξ1, P.coheight_genericPoint] at this
      exact lt_irrefl _ (this (by simp))
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    change closure {P.genericPoint} ∈ _
    rw [← hξη, ← hWξ]
    exact hW

/-- Only finitely many prime divisors are contained in an snc closed subset. -/
private theorem finite_setOf_support_subset [NoetherianSpace Y] {S : Set Y}
    (hS : IsSNCClosedSubset sY S) :
    {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ S}.Finite := by
  refine Set.Finite.of_finite_image ((Aux.finite_and_cover_componentsOf hS.1).1.subset ?_)
    fun P _ Q _ h => primeDivisor_eq_of_support_eq h
  rintro - ⟨P, hP, rfl⟩
  exact support_mem_componentsOf hS hP

/-- **A reduced divisor whose components lie in an snc closed subset is snc.** -/
private theorem isSNC_sum_single_of_support_subset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Set Y} (hS : IsSNCClosedSubset sY S)
    (s : Finset (MMP.Mori.PrimeDivisor Y)) (hs : ∀ P ∈ s, (P.support : Set Y) ⊆ S) :
    (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).IsSNC sY := by
  classical
  have hc : ∀ P ∈ s, (P.support : Set Y) ∈ componentsOf S := fun P hP =>
    support_mem_componentsOf hS (hs P hP)
  obtain ⟨hSc, hempty | ⟨-, -, hfam⟩⟩ := id hS
  · have hs0 : s = ∅ := Finset.eq_empty_of_forall_notMem fun P hP => by
      have := hs P hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
      rw [hempty] at this
      exact this
    subst hs0
    rw [Finset.sum_empty]
    exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sY hsm
  have hG := support_sum_single s
  have hideal : ∀ P (hP : P ∈ s),
      P.idealSheaf = componentsFamily S ⟨(P.support : Set Y), hc P hP⟩ := fun P hP =>
    idealSheaf_eq_vanishingIdeal P (by
      rw [Closeds.coe_closure, (Aux.isClosed_of_mem_componentsOf hSc (hc P hP)).closure_eq])
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [hG] at hP
    rw [hideal P hP]
    exact (hfam.1 _).2.2
  · obtain ⟨m, z, c, hz, hcI, hcinj⟩ := hfam.2 x
    have hs' : ∀ P : {P : MMP.Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        P.1 ∈ s := fun P => hG.subset P.2.1
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor Y //
        P ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ) : Divisor Y).support ∧ x ∈ P.support},
        x ∈ (componentsFamily S ⟨(P.1.support : Set Y), hc P.1 (hs' P)⟩).support := fun P => by
      rw [← SetLike.mem_coe, coe_support_componentsFamily hSc]
      exact P.2.2
    refine ⟨m, z, fun P => c ⟨_, hmem P⟩, hz, fun P Q h => ?_, fun P => ?_⟩
    · have h1 := congrArg (fun V => (V.1.1 : Set Y)) (hcinj h)
      exact Subtype.ext (primeDivisor_eq_of_support_eq h1)
    · rw [hideal P.1 (hs' P)]
      exact hcI ⟨_, hmem P⟩

/-- An snc closed subset of a smooth Noetherian scheme is an snc divisor in the sense of
`MMP.Mori.IsSNCSubset`. -/
public theorem isSNCSubset_of_isSNCClosedSubset [LocallyOfFiniteType sY] [NoetherianSpace Y]
    [IsLocallyNoetherian Y] (hsm : IsSmoothScheme sY) {S : Closeds Y}
    (hS : IsSNCClosedSubset sY (S : Set Y)) : IsSNCSubset sY S := by
  classical
  by_cases hS0 : (S : Set Y) = ∅
  · exact Or.inl (Closeds.ext (by rw [hS0, Closeds.coe_bot]))
  obtain ⟨hSc, hempty | ⟨hpure, -, -⟩⟩ := id hS
  · exact absurd hempty hS0
  set s := (finite_setOf_support_subset hS).toFinset with hs
  have hmem : ∀ P, P ∈ s ↔ (P.support : Set Y) ⊆ S := fun P => by
    rw [hs, Set.Finite.mem_toFinset]; rfl
  refine Or.inr ⟨s, ?_, isSNC_sum_single_of_support_subset hsm hS s fun P hP => (hmem P).mp hP⟩
  apply subset_antisymm
  · exact Set.iUnion₂_subset fun P hP => (hmem P).mp hP
  · intro y hy
    obtain ⟨W, hW, hyW⟩ := (Aux.finite_and_cover_componentsOf hSc).2 hy
    obtain ⟨ξ, hWξ, hξ1⟩ := exists_coheight_eq_one_of_mem_componentsOf hSc hpure hW
    set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξ1
    have hPs : (P.support : Set Y) = W := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hWξ]
    refine Set.mem_iUnion₂.mpr ⟨P, (hmem P).mpr (hPs ▸ hW.1.2), hPs ▸ hyW⟩

end SNCBridge

/-- Cancellation in `WithBot ℕ∞` against a natural number. -/
public lemma le_of_add_eq_add_of_le {a b : WithBot ℕ∞} {c d : ℕ∞} {n : ℕ}
    (ha : a + c = n) (hb : b + d = n) (hab : a ≤ b) : d ≤ c := by
  induction a with
  | bot => simp at ha
  | coe a =>
  induction b with
  | bot => simp at hb
  | coe b =>
  have ha' : a + c = n := by exact_mod_cast ha
  have hb' : b + d = n := by exact_mod_cast hb
  have hab' : a ≤ b := by exact_mod_cast hab
  induction a with
  | top => simp at ha'
  | coe a =>
  induction b with
  | top => simp at hb'
  | coe b =>
  induction c with
  | top => simp at ha'
  | coe c =>
  induction d with
  | top => simp at hb'
  | coe d =>
  have : a + c = n := by exact_mod_cast ha'
  have : b + d = n := by exact_mod_cast hb'
  have : a ≤ b := by exact_mod_cast hab'
  exact_mod_cast (by omega : d ≤ c)

/-! ### Birationality through the generic fibre -/

section Birational

variable {X Y : Scheme.{u}}

/-- A morphism to an irreducible scheme whose generic fibre is the spectrum of the function field
of the target is dominant: that fibre is nonempty. -/
private lemma isDominant_of_isIso_fiberToSpecResidueField [IrreducibleSpace Y] (g : X ⟶ Y)
    [IsIso (g.fiberToSpecResidueField (genericPoint Y))] : IsDominant g := by
  obtain ⟨z⟩ : Nonempty (g.fiber (genericPoint Y)) :=
    ⟨inv (g.fiberToSpecResidueField (genericPoint Y)) (IsLocalRing.closedPoint _)⟩
  have hz : g (g.fiberι _ z) = genericPoint Y := (g.range_fiberι (genericPoint Y)).le ⟨z, rfl⟩
  have h1 : genericPoint Y ∈ Set.range g := ⟨_, hz⟩
  exact ⟨dense_iff_closure_eq.mpr <| Set.eq_univ_of_forall fun y =>
    closure_mono (Set.singleton_subset_iff.mpr h1)
      ((genericPoint_spec Y).specializes (Set.mem_univ y)).mem_closure⟩

/-- A morphism of integral schemes whose generic fibre is the spectrum of the residue field of the
generic point is birational in the sense of [Stacks, Tag 01RO]. -/
private lemma isBirational_of_isIso_fiberToSpecResidueField [IsIntegral X] [IsIntegral Y]
    (g : X ⟶ Y) [h : IsIso (g.fiberToSpecResidueField (genericPoint Y))] : IsBirational g := by
  have := isDominant_of_isIso_fiberToSpecResidueField g
  have hη : g (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant g
  refine ⟨?_, fun x hx' => ?_⟩
  · rw [_root_.genericPoints_eq_singleton, _root_.genericPoints_eq_singleton, ← hη]
    exact Set.bijOn_singleton.mpr rfl
  · rw [_root_.genericPoints_eq_singleton, Set.mem_singleton_iff] at hx'
    subst hx'
    have : IsIso (g.fiberToSpecResidueField (g (genericPoint X))) := hη ▸ h
    have hpre : IsPreimmersion (Spec.map (g.residueFieldMap (genericPoint X))) := by
      rw [← g.asFiberHom_fiberToSpecResidueField]; infer_instance
    have hsurj : Function.Surjective (g.residueFieldMap (genericPoint X)).hom := by
      have h2 : SurjectiveOnStalks (Spec.map (g.residueFieldMap (genericPoint X))) :=
        inferInstance
      rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)] at h2
      exact RingHom.surjectiveOnStalks_iff_of_isLocalHom.mp h2
    have hX : IsIso (X.residue (genericPoint X)) := isIso_residue_genericPoint X
    have hY : IsIso (Y.residue (g (genericPoint X))) := by
      rw [hη]; exact isIso_residue_genericPoint Y
    have hfac : g.stalkMap (genericPoint X) = Y.residue (g (genericPoint X)) ≫
        g.residueFieldMap (genericPoint X) ≫ inv (X.residue (genericPoint X)) := by
      rw [← Category.assoc, IsIso.eq_comp_inv]
      exact (Scheme.residue_residueFieldMap g _).symm
    rw [hfac]
    have : IsIso (g.residueFieldMap (genericPoint X)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        ⟨(g.residueFieldMap (genericPoint X)).hom.injective, hsurj⟩
    infer_instance

/-- For a proper morphism of integral schemes with normal target, birationality is equivalent to
the generic fibre being the spectrum of the function field of the target. -/
public lemma isBirationalMorphism_iff_isIso_fiberToSpecResidueField [IsIntegral X]
    [IsIntegral Y] [IsNormal Y] (g : X ⟶ Y) [IsProper g] :
    MMP.Mori.IsBirationalMorphism g ↔ IsIso (g.fiberToSpecResidueField (genericPoint Y)) := by
  refine ⟨fun hb => isIso_fiberToSpecResidueField_genericPoint_of_isBirational g
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb), fun h => ?_⟩
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso g
    (isBirational_of_isIso_fiberToSpecResidueField g)).1 ‹_›
  have := isDominant_of_isIso_fiberToSpecResidueField g
  have hη : g (genericPoint X) = genericPoint Y := map_genericPoint_of_isDominant g
  have hfin : genericPoint Y ∈ MMP.Resolution.Bridges.finiteFibreLocus g := by
    have : Finite (g.fiber (genericPoint Y)) :=
      Finite.of_equiv _ (Scheme.homeoOfIso
        (asIso (g.fiberToSpecResidueField (genericPoint Y)))).toEquiv.symm
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (g.fiberHomeo _).toEquiv)
  let V : Y.Opens := ⟨_, hU⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g (g ⁻¹ᵁ V) V
    ⟨genericPoint X, show g (genericPoint X) ∈ V from hη ▸ hfin⟩ ⟨_, hfin⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact hiso

/-- In a pullback square, the fibre of the base change over `y'` is a base change of the fibre
over the image of `y'` along a field extension, so one is the spectrum of its residue field
exactly when the other is. -/
public lemma isIso_fiberToSpecResidueField_iff_of_isPullback {X Y X' Y' : Scheme.{u}}
    {p : X' ⟶ X} {g' : X' ⟶ Y'} {g : X ⟶ Y} {q : Y' ⟶ Y} (h : IsPullback p g' g q) (y' : Y') :
    IsIso (g'.fiberToSpecResidueField y') ↔ IsIso (g.fiberToSpecResidueField (q y')) := by
  have L := isPullback_fiberToSpecResidueField_of_isPullback h y'
  have hres := specMap_mem_surjective_flat_quasiCompact (q.residueFieldMap y').hom
  rw [CommRingCat.ofHom_hom] at hres
  exact MorphismProperty.iff_of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u})
    L.flip hres

/-- In a pullback square, the fibre of the base change over `y'` is finite exactly when the fibre
over the image of `y'` is: the first is the base change of the second along a field extension,
which is surjective, and quasi-finiteness is stable under base change. -/
public lemma finite_preimage_singleton_iff_of_isPullback {X Y X' Y' : Scheme.{u}}
    {p : X' ⟶ X} {g' : X' ⟶ Y'} {g : X ⟶ Y} {q : Y' ⟶ Y} (h : IsPullback p g' g q)
    [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact g'] (y' : Y') :
    (g' ⁻¹' {y'}).Finite ↔ (g ⁻¹' {q y'}).Finite := by
  have L := isPullback_fiberToSpecResidueField_of_isPullback h y'
  have hres := specMap_mem_surjective_flat_quasiCompact (q.residueFieldMap y').hom
  rw [CommRingCat.ofHom_hom] at hres
  rw [← Set.finite_coe_iff, ← Set.finite_coe_iff, ← (g'.fiberHomeo y').toEquiv.finite_iff,
    ← (g.fiberHomeo (q y')).toEquiv.finite_iff]
  refine ⟨fun hF => ?_, fun _ => ?_⟩
  · exact @Finite.of_surjective _ _ hF _
      (MorphismProperty.of_isPullback (P := @Surjective) L.flip hres.1.1).surj
  · have : LocallyOfFiniteType (g.fiberToSpecResidueField (q y')) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
    have : QuasiCompact (g.fiberToSpecResidueField (q y')) :=
      inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have : QuasiCompact (g'.fiberToSpecResidueField y') :=
      inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have hl : LocallyQuasiFinite (g.fiberToSpecResidueField (q y')) :=
      locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun _ => Set.toFinite _
    have : LocallyQuasiFinite (g'.fiberToSpecResidueField y') :=
      MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) L hl
    have hfin := (g'.fiberToSpecResidueField y').finite_preimage_singleton
      (IsLocalRing.closedPoint (Y'.residueField y'))
    exact Set.finite_univ_iff.mp
      (hfin.subset fun z _ => Subsingleton.elim (α := PrimeSpectrum (Y'.residueField y')) _ _)

/-- A morphism restricting to an isomorphism over `V` has subsingleton fibres over `V`. -/
private lemma subsingleton_preimage_singleton_of_isIso_restrict (g : X ⟶ Y) (V : Y.Opens)
    [IsIso (g ∣_ V)] (y : Y) (hy : y ∈ V) : (g ⁻¹' {y}).Subsingleton := by
  intro a ha b hb
  have ha' : a ∈ g ⁻¹ᵁ V := show g a ∈ V by rw [Set.mem_singleton_iff.mp ha]; exact hy
  have hb' : b ∈ g ⁻¹ᵁ V := show g b ∈ V by rw [Set.mem_singleton_iff.mp hb]; exact hy
  have e1 := morphismRestrict_base_coe g V ⟨a, ha'⟩
  have e2 := morphismRestrict_base_coe g V ⟨b, hb'⟩
  have := (g ∣_ V).isOpenEmbedding.injective (a₁ := ⟨a, ha'⟩) (a₂ := ⟨b, hb'⟩) (Subtype.ext (by
      rw [e1, e2]
      exact (Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm))
  exact congrArg Subtype.val this

/-- For a proper birational morphism of integral schemes with normal target, the largest open
over which it is an isomorphism is the locus of finite fibres. -/
public lemma coe_biregularLocus_eq_finiteFibreLocus [IsIntegral X] [IsIntegral Y] [IsNormal Y]
    (g : X ⟶ Y) [IsProper g] (hb : MMP.Mori.IsBirationalMorphism g) :
    ((MMP.Mori.biregularLocus g : Y.Opens) : Set Y) =
      MMP.Resolution.Bridges.finiteFibreLocus g := by
  have hb' := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso g hb').1 ‹_›
  refine subset_antisymm (fun y hy => ?_) (MMP.Mori.le_biregularLocus (V := ⟨_, hU⟩) hiso)
  have : IsIso (g ∣_ MMP.Mori.biregularLocus g) := MMP.Mori.isBiregular_biregularLocus g
  exact (subsingleton_preimage_singleton_of_isIso_restrict g _ y hy).finite

/-- **Exceptional sets under base change.** In a pullback square of proper birational morphisms
of integral schemes with normal targets, the exceptional set of the base change is the preimage
of the exceptional set: both are complements of finite-fibre loci, and finiteness of fibres is
insensitive to the field extensions between residue fields. -/
public lemma coe_exceptionalSet_eq_preimage_of_isPullback {X' Y' : Scheme.{u}} {p : X' ⟶ X}
    {g' : X' ⟶ Y'} {g : X ⟶ Y} {q : Y' ⟶ Y} (h : IsPullback p g' g q) [IsIntegral X]
    [IsIntegral Y] [IsNormal Y] [IsIntegral X'] [IsIntegral Y'] [IsNormal Y'] [IsProper g]
    [IsProper g'] (hb : MMP.Mori.IsBirationalMorphism g)
    (hb' : MMP.Mori.IsBirationalMorphism g') :
    (MMP.Mori.exceptionalSet g' : Set X') = p ⁻¹' MMP.Mori.exceptionalSet g := by
  ext x
  simp only [SetLike.mem_coe, MMP.Mori.mem_exceptionalSet, Set.mem_preimage]
  rw [← SetLike.mem_coe, coe_biregularLocus_eq_finiteFibreLocus g' hb', ← SetLike.mem_coe,
    coe_biregularLocus_eq_finiteFibreLocus g hb]
  simp only [MMP.Resolution.Bridges.finiteFibreLocus, Set.mem_ofPred_eq]
  rw [finite_preimage_singleton_iff_of_isPullback h (g' x), ← Scheme.Hom.comp_apply, ← h.w,
    Scheme.Hom.comp_apply]

end Birational

section CurveBaseChange

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Contracted curves and ample degrees -/

section Contraction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- A proper curve which is not contracted by `g` does not have a point as image. -/
private theorem not_exists_range_eq_singleton (g : X ⟶ Y) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : ¬ ∃ y : Y, Set.range (Γ.ι ≫ g) = {y} := by
  rintro ⟨y, hy⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨c, rfl⟩ := hx
  have h1 : (Γ.ι ≫ g) c ∈ Set.range (Γ.ι ≫ g) := ⟨c, rfl⟩
  have h2 : (Γ.ι ≫ g) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ g) := ⟨_, rfl⟩
  rw [hy] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- The image of a proper curve not contracted by `g` is a proper curve. -/
private theorem isProperCurve_map (g : X ⟶ Y) (hg : g ≫ sY = sX) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : IsProperCurve sY (g Γ.point) := by
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hcurve := isCurve_imageι_comp sY φ (not_exists_range_eq_singleton g Γ h)
  have hker := Γ.ker_comp g
  rw [← hφdef] at hker
  have hdim : topologicalKrullDim (curveSubschemeAt (g Γ.point)) = 1 := by
    have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim φ.ker.subscheme = 1 at h1
    rwa [hker] at h1
  have hprop : IsProper (curveSubschemeAtι (g Γ.point) ≫ sY) := by
    have h1 : IsProper (φ.imageι ≫ sY) := isProper_imageι_comp φ sY
    change IsProper (φ.ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1
  exact ⟨hdim, hprop⟩

/-- A morphism over `k` which does not contract a proper curve has positive residue degree at
its generic point: `k(C)` is a finite extension of the function field of the image curve. -/
public theorem residueFieldDegree_pos_of_not_isContractedBy (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (Γ : ProperCurve sX) (h : ¬ Γ.IsContractedBy g) : 0 < residueFieldDegree g Γ.point := by
  have hnc := not_exists_range_eq_singleton g Γ h
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree g Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι g (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

omit [IsSeparated sY] [LocallyOfFiniteType sY] in
/-- An ample invertible sheaf has positive degree on every proper curve. -/
public theorem degree_pos_of_isAmple (D : ProperCurve sY) (H : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple Y H) : 0 < D.degree k H := by
  have := D.isCurve
  exact invertibleCurveDegree_pos_of_isAmple_of_isCurve k (D.ι ≫ sY) D.dim_le _
    (isAmple_pullback_of_isFinite D.ι H hH)

/-- **Contraction is detected by an ample degree.** If the pull-back of an ample invertible
sheaf along `g` has degree zero on a proper curve, then `g` contracts the curve. -/
public theorem isContractedBy_of_degree_pullback_eq_zero (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (H : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 H]
    (hH : Scheme.Modules.IsAmple Y H) (Γ : ProperCurve sX)
    (h0 : Γ.degree k ((Scheme.Modules.pullback g).obj H) = 0) : Γ.IsContractedBy g := by
  by_contra hc
  have hD := isProperCurve_map g hg Γ hc
  rw [Γ.degree_pullback g hg H, dite_eq_left hD] at h0
  have h1 := residueFieldDegree_pos_of_not_isContractedBy g hg Γ hc
  have h2 := degree_pos_of_isAmple ⟨g Γ.point, hD⟩ H hH
  have : (0 : ℤ) <
      (residueFieldDegree g Γ.point : ℤ) * (⟨g Γ.point, hD⟩ : ProperCurve sY).degree k H :=
    mul_pos (by exact_mod_cast h1) h2
  omega

end Contraction

/-! ### Base change of curves -/

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

/-- The kernel of a closed immersion from a reduced scheme is the vanishing ideal of its range. -/
private theorem ker_eq_vanishingIdeal_of_isReduced {Y W : Scheme.{u}} (ι : Y ⟶ W)
    [IsClosedImmersion ι] [IsReduced Y] (T : TopologicalSpace.Closeds W)
    (hT : (T : Set W) = Set.range ι) :
    ι.ker = Scheme.IdealSheafData.vanishingIdeal T := by
  have hrad : ι.ker.radical = ι.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x hx => ?_) Ideal.le_radical
    obtain ⟨n, hn⟩ := hx
    rw [RingHom.mem_ker, map_pow] at hn
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  have : ι.ker.support = T := TopologicalSpace.Closeds.ext <| by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq, hT]
  rw [← this, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- A closed immersion from an integral scheme is, up to isomorphism, the closed immersion of the
closure of the image of the generic point. -/
private theorem exists_iso_curveSubschemeAt {Y W : Scheme.{u}} [IsIntegral Y] (ι : Y ⟶ W)
    [IsClosedImmersion ι] :
    ∃ e : Y ≅ curveSubschemeAt (ι (genericPoint Y)), e.hom ≫ curveSubschemeAtι _ = ι := by
  have hrange : Set.range ι = closure {ι (genericPoint Y)} := by
    rw [← Set.image_singleton, ι.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec Y).def]
    simp
  have hker : ι.ker = (curveSubschemeAtι (ι (genericPoint Y))).ker := by
    rw [ker_eq_vanishingIdeal_of_isReduced ι (TopologicalSpace.Closeds.closure
      {ι (genericPoint Y)}) hrange.symm]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
  have hf : IsIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq ι (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  exact ⟨asIso (IsClosedImmersion.lift (curveSubschemeAtι (ι (genericPoint Y))) ι hker.ge),
    IsClosedImmersion.lift_fac _ _ _⟩

omit [IsAlgClosed k₀] in
/-- The degree of a pulled-back invertible sheaf on a base change of a curve: if `Y → C₀` is the
base change of the curve `C₀` along `k₀ → K` and `Y → X` is the induced morphism, then the degree
of `π^* L` on `Y` equals the degree of `L` on `C₀`, Euler characteristics being invariant under
extension of the ground field. -/
private theorem degreeOn_baseChange {C₀ Y : Scheme.{u}} (ι₀ : C₀ ⟶ X₀) (ι : Y ⟶ X)
    (j : Y ⟶ C₀) [IsProper (ι₀ ≫ s₀)]
    (hc : ι ≫ π = j ≫ ι₀)
    (h : IsPullback j (ι ≫ s) (ι₀ ≫ s₀) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hdim : topologicalKrullDim C₀ ≤ 1) (hdim' : topologicalKrullDim Y ≤ 1)
    (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L]
    [IsProper (ι ≫ s)] :
    degreeOn K s ι hdim' ((Scheme.Modules.pullback π).obj L) = degreeOn k₀ s₀ ι₀ hdim L := by
  have e : (Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback π).obj L) ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι₀).obj L) :=
    (Scheme.Modules.pullbackComp ι π).app L ≪≫ (Scheme.Modules.pullbackCongr hc).app L ≪≫
      ((Scheme.Modules.pullbackComp j ι₀).app L).symm
  unfold degreeOn invertibleCurveDegree
  congr 1
  · refine finsum_congr fun n => ?_
    rw [finrank_cohomologyOverField_eq_of_iso K (ι ≫ s) e n,
      finrank_cohomologyOverField_baseChange_field k₀ K j (ι ≫ s) (ι₀ ≫ s₀) h _ n]
  · refine finsum_congr fun n => ?_
    have eu : SheafOfModules.unit Y.ringCatSheaf ≅
        (Scheme.Modules.pullback j).obj (SheafOfModules.unit C₀.ringCatSheaf) :=
      (Scheme.Modules.pullbackUnitIso j).symm
    have : (SheafOfModules.unit C₀.ringCatSheaf).IsQuasicoherent := inferInstance
    rw [finrank_cohomologyOverField_eq_of_iso K (ι ≫ s) eu n,
      finrank_cohomologyOverField_baseChange_field k₀ K j (ι ≫ s) (ι₀ ≫ s₀) h
        (SheafOfModules.unit C₀.ringCatSheaf) n]

/-- **Base change of curves.** Every proper curve `C₀ ⊆ X₀` has a base change, a proper curve
`C ⊆ X` with closure `π⁻¹(C₀)`, on which every invertible sheaf pulled back from `X₀` has the
degree it has on `C₀`. -/
public theorem exists_properCurve_baseChange
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (C₀ : ProperCurve s₀) :
    ∃ C : ProperCurve s, closure {C.point} = π.base ⁻¹' closure {C₀.point} ∧
      ∀ (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L],
        C.degree K ((Scheme.Modules.pullback π).obj L) = C₀.degree k₀ L := by
  set g := Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) with hg
  set t₀ : C₀.scheme ⟶ Spec (.of k₀) := C₀.ι ≫ s₀ with ht₀
  have hpb : IsPullback (pullback.snd t₀ g) (pullback.fst t₀ g) g t₀ :=
    (IsPullback.of_hasPullback t₀ g).flip
  obtain ⟨Y, j, t, hpb⟩ : ∃ (Y : Scheme.{u}) (j : Y ⟶ C₀.scheme) (t : Y ⟶ Spec (.of K)),
      IsPullback t j g t₀ := ⟨_, _, _, hpb⟩
  have hcomm : (j ≫ C₀.ι) ≫ s₀ = t ≫ g := by
    simpa only [Category.assoc, ← ht₀] using hpb.w.symm
  set ι' : Y ⟶ X := h.lift (j ≫ C₀.ι) t hcomm with hι'
  have hι'π : ι' ≫ π = j ≫ C₀.ι := h.lift_fst _ _ _
  have hι's : ι' ≫ s = t := h.lift_snd _ _ _
  have hsq : IsPullback j ι' C₀.ι π := by
    refine (IsPullback.of_right (h₁₁ := ι') (h₁₂ := s) (h₂₁ := C₀.ι) (h₂₂ := s₀)
      (v₁₁ := j) (v₁₂ := π) (v₁₃ := g) ?_ hι'π h.flip).flip
    rw [hι's]; exact hpb
  haveI : IsClosedImmersion ι' := MorphismProperty.of_isPullback hsq inferInstance
  have hproper : IsProper t₀ := C₀.isProperCurve.isProper
  haveI : IsProper t := MorphismProperty.of_isPullback hpb.flip hproper
  haveI : IrreducibleSpace C₀.scheme := inferInstance
  haveI : GeometricallyIrreducible t₀ :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k₀ C₀.scheme t₀
  haveI : GeometricallyReduced t₀ := geometricallyReduced_of_isReduced t₀
  haveI : GeometricallyIntegral t₀ :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible t₀
  haveI : GeometricallyIntegral t := MorphismProperty.of_isPullback hpb.flip inferInstance
  haveI : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton t
  obtain ⟨e, he⟩ := exists_iso_curveSubschemeAt ι'
  have key : e.inv ≫ ι' = curveSubschemeAtι (ι' (genericPoint Y)) := by
    rw [Iso.inv_comp_eq]; exact he.symm
  haveI : LocallyOfFiniteType t₀ := inferInstance
  have hdimY : topologicalKrullDim Y = topologicalKrullDim C₀.scheme :=
    topologicalKrullDim_baseChange k₀ K j t t₀ hpb.flip
  have hdimC : topologicalKrullDim (curveSubschemeAt (ι' (genericPoint Y))) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph, hdimY]
    exact C₀.dim_eq
  have hpropC : IsProper (curveSubschemeAtι (ι' (genericPoint Y)) ≫ s) := by
    have : curveSubschemeAtι (ι' (genericPoint Y)) ≫ s = e.inv ≫ t := by
      rw [← key, Category.assoc, hι's]
    rw [this]; infer_instance
  let C : ProperCurve s := ⟨ι' (genericPoint Y), ⟨hdimC, hpropC⟩⟩
  have hc : C.ι ≫ π = (e.inv ≫ j) ≫ C₀.ι := by
    change curveSubschemeAtι (ι' (genericPoint Y)) ≫ π = _
    rw [← key]; simp [hι'π]
  have hsqC : IsPullback (e.inv ≫ j) (C.ι ≫ s) (C₀.ι ≫ s₀) g := by
    refine hpb.flip.of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_
      (by simp [ht₀]) (by simp)
    change e.inv ≫ t = curveSubschemeAtι (ι' (genericPoint Y)) ≫ s
    rw [← key, Category.assoc, hι's]
  refine ⟨C, ?_, fun L _ => degreeOn_baseChange s₀ s π C₀.ι C.ι _ hc hsqC C₀.dim_le C.dim_le L⟩
  have hrange : Set.range ι' = π ⁻¹' Set.range C₀.ι := by
    have hs : Function.Surjective hsq.isoPullback.hom :=
      (Scheme.homeoOfIso hsq.isoPullback).surjective
    rw [← hsq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      hs.range_eq, Set.image_univ, Scheme.Pullback.range_snd]
  have he' : Function.Surjective e.inv := (Scheme.homeoOfIso e.symm).surjective
  rw [← C.range_ι, ← C₀.range_ι, ← hrange]
  change Set.range (curveSubschemeAtι (ι' (genericPoint Y))) = _
  rw [← key, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, he'.range_eq,
    Set.image_univ]

/-- A proper curve on `X` whose closure is `π⁻¹(C₀)` has, against every invertible sheaf pulled
back from `X₀`, the degree that sheaf has on `C₀`. -/
public theorem degree_pullback_eq_of_closure_eq
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {C₀ : ProperCurve s₀} {C : ProperCurve s}
    (hC : closure {C.point} = π.base ⁻¹' closure {C₀.point})
    (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L] :
    C.degree K ((Scheme.Modules.pullback π).obj L) = C₀.degree k₀ L := by
  obtain ⟨C', hC', hdeg⟩ := exists_properCurve_baseChange s₀ s π h C₀
  obtain rfl : C' = C := ProperCurve.ext (inseparable_iff_closure_eq.mpr (hC'.trans hC.symm)).eq
  exact hdeg L

/-- **Injectivity.** A linear map `N₁(X₀)_ℝ → N₁(X)_ℝ` sending the class of each proper curve to
the class of its base change is injective: the degree of `π^* L` on `φ z` is the degree of `L`
on `z`. -/
public theorem injective_of_map_numericalClass
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s)
    (hφ : ∀ (C₀ : ProperCurve s₀) (C : ProperCurve s),
      closure {C.point} = π.base ⁻¹' closure {C₀.point} →
        φ (OneCycle.numericalClass s₀ (C₀.cycle ℝ)) = OneCycle.numericalClass s (C.cycle ℝ)) :
    Function.Injective φ := by
  have hφdeg (L : X₀.Modules) [SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L]
      (Z : OneCycle ℝ s₀) :
      NumericalCurveClasses.degree s ((Scheme.Modules.pullback π).obj L)
          (φ (OneCycle.numericalClass s₀ Z)) = OneCycle.degree ℝ s₀ L Z := by
    induction Z using Finsupp.induction_linear with
    | zero => simp
    | add Z₁ Z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | single C₀ a =>
      obtain ⟨C, hC, -⟩ := exists_properCurve_baseChange s₀ s π h C₀
      have hsingle : Finsupp.single C₀ a = a • C₀.cycle ℝ := by
        simp [ProperCurve.cycle, Finsupp.smul_single]
      rw [hsingle, map_smul, map_smul, map_smul, map_smul, hφ C₀ C hC,
        NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
        OneCycle.degree_cycle, degree_pullback_eq_of_closure_eq s₀ s π h hC L]
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective s₀ z
  change (OneCycle.numericallyTrivial s₀).mkQ Z = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, OneCycle.mem_numericallyTrivial]
  intro L _
  rw [← hφdeg L Z, LinearMap.mem_ker.mp hz, map_zero]

end BaseChange

/-! ### The main argument -/

/-- The degree of an invertible sheaf on a proper curve only depends on its isomorphism class. -/
public theorem degree_congr {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    (C : ProperCurve sX) {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    C.degree k L = C.degree k L' := by
  unfold ProperCurve.degree degreeOn invertibleCurveDegree
  congr 1
  refine finsum_congr fun n => ?_
  rw [finrank_cohomologyOverField_eq_of_iso k (C.ι ≫ sX)
    ((Scheme.Modules.pullback C.ι).mapIso e) n]

/-- A projective variety over a field carries an ample invertible sheaf. -/
public theorem exists_isAmple_of_isProjectiveVariety {k : Type u} [Field k] {Z : Scheme.{u}}
    {t : Z ⟶ Spec (.of k)} (hZ : MMP.Mori.IsProjectiveVariety k t) :
    ∃ (H : Z.Modules) (_ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 H),
      Scheme.Modules.IsAmple Z H := by
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨H, hH, hHa⟩ :=
    AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism t M hMa hZ.isProjective
  exact ⟨H, hH, (Stacks.AmpleBridge.isAmple_iff_isAmple _ H).mp hHa⟩

end CurveBaseChange

section SheafPullback

open MMP.Intersection
open MMP.CartierDivisorSheaf Opposite
  TopologicalSpace

section KModel

variable {X : Scheme.{u}} [IsIntegral X]

private noncomputable def ιK (U : X.Opens) :
    X.functionField →+* X.totalQuotientSheaf.obj.obj (op U) :=
  ((functionFieldToTotalQuotientSheaf X).app (op U)).hom

private theorem genericPoint_mem {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U := by
  obtain ⟨x, hx⟩ := hU
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ _, hx⟩

private theorem ιK_germ (U : X.Opens) (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    ιK U (X.presheaf.germ U (genericPoint X) h a) = toK U a :=
  functionFieldToTotalQuotientSheaf_germ X U a h

private theorem ιK_res {U V : X.Opens} (h : V ≤ U) (c : X.functionField) :
    resK h (ιK U c) = ιK V c :=
  (congrArg (fun φ => φ.hom c)
    ((functionFieldToTotalQuotientSheaf X).naturality (homOfLE h).op)).symm

private theorem ιK_injective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Injective (ιK U) :=
  functionFieldToTotalQuotientSheaf_app_injective X U hU

private theorem ιK_surjective (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Function.Surjective (ιK U) := by
  intro s
  have : Nonempty U := hU.to_subtype
  obtain ⟨a, ha⟩ := exists_eq_constantSheafOnSpace_section X X.functionField U inferInstance
    (((totalQuotientSheafIsoConstant X).val.hom.hom.app (op U)) s)
  refine ⟨a, ?_⟩
  change ((totalQuotientSheafIsoConstant X).val.inv.hom.app (op U))
    (((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op U)) a) = s
  rw [← ha]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op U)) (totalQuotientSheafIsoConstant X).val.hom_inv_id) s

end KModel

section Dominant

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

private theorem functionFieldMap_germ (U : X.Opens) (hU : genericPoint X ∈ U) (a : Γ(X, U))
    (hY : genericPoint Y ∈ g ⁻¹ᵁ U) :
    functionFieldMap g (X.presheaf.germ U (genericPoint X) hU a) =
      Y.presheaf.germ (g ⁻¹ᵁ U) (genericPoint Y) hY (g.app U a) := by
  have hx : g (genericPoint Y) ∈ U := hY
  have h1 := MMP.Mori.functionFieldMap_algebraMap_stalk g (genericPoint Y)
    (X.presheaf.germ U (g (genericPoint Y)) hx a)
  have hn : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  have hn' : Nonempty (g ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hY⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a] at h1
  erw [Scheme.Hom.germ_stalkMap_apply g U (genericPoint Y) hx a] at h1
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) (U := g ⁻¹ᵁ U) hY _] at h1
  exact h1

end Dominant

section LocalFraction

variable {Z : Scheme.{u}}

private theorem exists_local_fraction {D : Z.CartierDivisor} {x : Z} {U : Z.Opens} (hxU : x ∈ U)
    (A B : Γ(Z, U)) {e : Z.totalQuotientSheaf.presheaf.stalk x} (he : IsLocalEquationAt D x e)
    (hf : IsFraction e (Z.presheaf.germ U x hxU A) (Z.presheaf.germ U x hxU B)) :
    ∃ (U₀ : Z.Opens) (h₀ : U₀ ≤ U) (_ : x ∈ U₀) (f : (Z.totalQuotientSheaf.obj.obj (op U₀))ˣ),
      IsLocalEquationOn D U₀ f ∧
      toK U₀ (Z.presheaf.map (homOfLE h₀).op B) * (f : Z.totalQuotientSheaf.obj.obj (op U₀)) =
        toK U₀ (Z.presheaf.map (homOfLE h₀).op A) := by
  obtain ⟨U₁, hx₁, f₁, hf₁, rfl⟩ := he
  have h2 := hf.2
  rw [← germ_toTotalQuotient, ← germ_toTotalQuotient] at h2
  have hxW : x ∈ U ⊓ U₁ := ⟨hxU, hx₁⟩
  have e : Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
      (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) * resK inf_le_right (f₁ : _)) =
      Z.totalQuotientSheaf.presheaf.germ (U ⊓ U₁) x hxW
        (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := by
    rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply]
    exact h2
  obtain ⟨U₀, hx₀, i, j, hij⟩ := Z.totalQuotientSheaf.presheaf.germ_eq x hxW hxW _ _ e
  have hij' : i = j := Subsingleton.elim _ _
  subst hij'
  refine ⟨U₀, i.le.trans inf_le_left, hx₀, MMP.Intersection.resUnit (i ≫ homOfLE inf_le_right) f₁,
    isLocalEquationOn_resUnit _ hf₁, ?_⟩
  have h3 : resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op B) *
      resK inf_le_right (f₁ : _)) =
        resK i.le (toK (U ⊓ U₁) (Z.presheaf.map (homOfLE inf_le_left).op A)) := hij
  rw [map_mul, ← resK_toK inf_le_left B, ← resK_toK inf_le_left A, resK_resK, resK_resK,
    resK_resK] at h3
  rw [← resK_toK _ B, ← resK_toK _ A]
  convert h3 using 2
  rfl

end LocalFraction

section Rho

private theorem subsingleton_totalQuotient_of_not_nonempty {Z : Scheme.{u}} {U : Z.Opens}
    (h : ¬ (U : Set Z).Nonempty) : Subsingleton (Z.totalQuotientSheaf.obj.obj (op U)) := by
  have : U = ⊥ := TopologicalSpace.Opens.coe_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp h)
  subst this
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.totalQuotientSheaf)

private def trivRingHom (R S : Type*) [CommRing R] [CommRing S] [Subsingleton S] : R →+* S where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

omit [IsIntegral X] [IsIntegral Y] [IsDominant g] in
private theorem not_nonempty_preimage {U : X.Opens} (h : ¬ (U : Set X).Nonempty) :
    ¬ ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  rintro ⟨y, hy⟩
  exact h ⟨g y, hy⟩

private theorem nonempty_preimage {U : X.Opens} (h : (U : Set X).Nonempty) :
    ((g ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  have hη : genericPoint X ∈ U := genericPoint_mem h
  refine ⟨genericPoint Y, ?_⟩
  change g (genericPoint Y) ∈ U
  rw [map_genericPoint_of_isDominant g]; exact hη

open Classical in
/-- The ring map `𝓜_X(U) → 𝓜_Y(g⁻¹U)` induced by the extension of function fields. -/
private noncomputable def rho (U : X.Opens) :
    X.totalQuotientSheaf.obj.obj (op U) →+* Y.totalQuotientSheaf.obj.obj (op (g ⁻¹ᵁ U)) :=
  if hU : (U : Set X).Nonempty then
    (ιK (g ⁻¹ᵁ U)).comp ((functionFieldMap g).comp
      (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm.toRingHom)
  else
    haveI := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    trivRingHom _ _

private theorem rho_ιK {U : X.Opens} (hU : (U : Set X).Nonempty) (κ : X.functionField) :
    rho g U (ιK U κ) = ιK (g ⁻¹ᵁ U) (functionFieldMap g κ) := by
  unfold rho
  simp only [hU, ↓reduceDIte, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm (ιK U κ) =
      κ :=
    (RingEquiv.ofBijective (ιK U) ⟨ιK_injective U hU, ιK_surjective U hU⟩).symm_apply_apply κ
  rw [this]

private theorem rho_res {U V : X.Opens} (h : V ≤ U) (σ : X.totalQuotientSheaf.obj.obj (op U)) :
    resK (g.preimage_mono h) (rho g U σ) = rho g V (resK h σ) := by
  by_cases hV : (V : Set X).Nonempty
  · have hU : (U : Set X).Nonempty := hV.mono h
    obtain ⟨κ, rfl⟩ := ιK_surjective U hU σ
    rw [rho_ιK g hU, ιK_res h, ιK_res (g.preimage_mono h), rho_ιK g hV]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hV)
    exact Subsingleton.elim _ _

private theorem rho_toK (U : X.Opens) (a : Γ(X, U)) :
    rho g U (toK U a) = toK (g ⁻¹ᵁ U) (g.app U a) := by
  by_cases hU : (U : Set X).Nonempty
  · have hη : genericPoint X ∈ U := genericPoint_mem hU
    have hY : genericPoint Y ∈ g ⁻¹ᵁ U := genericPoint_mem (nonempty_preimage g hU)
    rw [← ιK_germ U hη a, rho_ιK g hU, functionFieldMap_germ g U hη a hY, ιK_germ _ hY]
  · have := subsingleton_totalQuotient_of_not_nonempty (not_nonempty_preimage g hU)
    exact Subsingleton.elim _ _

end Rho

section Key

private theorem exists_common_rep_le {Z : Scheme.{u}} (x : Z) (W : Z.Opens) (hxW : x ∈ W)
    (a b : Z.presheaf.stalk x) :
    ∃ (U : Z.Opens) (_ : U ≤ W) (hx : x ∈ U) (A B : Γ(Z, U)),
      Z.presheaf.germ U x hx A = a ∧ Z.presheaf.germ U x hx B = b := by
  obtain ⟨U₁, hx₁, A, rfl⟩ := Z.presheaf.exists_germ_eq a
  obtain ⟨U₂, hx₂, B, rfl⟩ := Z.presheaf.exists_germ_eq b
  refine ⟨U₁ ⊓ U₂ ⊓ W, inf_le_right, ⟨⟨hx₁, hx₂⟩, hxW⟩,
    Z.presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op A,
    Z.presheaf.map (homOfLE (inf_le_left.trans inf_le_right)).op B, ?_, ?_⟩
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  · exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

private theorem mul_left_cancel_totalQuotient {Z : Scheme.{u}} [IsIntegral Z] {V : Z.Opens}
    (hV : (V : Set Z).Nonempty) {B x y : Z.totalQuotientSheaf.obj.obj (op V)} (hB : B ≠ 0)
    (h : B * x = B * y) : x = y := by
  obtain ⟨x', rfl⟩ := ιK_surjective V hV x
  obtain ⟨y', rfl⟩ := ιK_surjective V hV y
  obtain ⟨B', rfl⟩ := ιK_surjective V hV B
  have hB' : B' ≠ 0 := fun h0 => hB (by rw [h0, map_zero])
  have h' : B' * x' = B' * y' := ιK_injective V hV (by simpa only [map_mul] using h)
  rw [mul_left_cancel₀ hB' h']

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : Y ⟶ X) [IsDominant g]

/-- Local equations of a pull-back are the pulled-back local equations. -/
private theorem exists_local_pullback_equation {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (y : Y) (W : X.Opens) (hW : g y ∈ W) :
    ∃ (U₀ : X.Opens) (_ : U₀ ≤ W) (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U₀) (_ : y ∈ V)
      (f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ) (f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ),
      IsLocalEquationOn E U₀ f₀ ∧ IsLocalEquationOn E' V f' ∧
        resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
          (f' : Y.totalQuotientSheaf.obj.obj (op V)) := by
  obtain ⟨a, b, ⟨e, he, hf⟩, -, hb, e', he', hf'⟩ := h.2 y
  obtain ⟨U, hUW, hxU, A, B, rfl, rfl⟩ := exists_common_rep_le (g y) W hW a b
  obtain ⟨U₀, h₀, hx₀, f₀, hf₀, hAB⟩ := exists_local_fraction hxU A B he hf
  have hyU₀ : y ∈ g ⁻¹ᵁ U₀ := hx₀
  set A₀ := X.presheaf.map (homOfLE h₀).op A with hA₀
  set B₀ := X.presheaf.map (homOfLE h₀).op B with hB₀
  have hgA : X.presheaf.germ U₀ (g y) hx₀ A₀ = X.presheaf.germ U (g y) hxU A :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgB : X.presheaf.germ U₀ (g y) hx₀ B₀ = X.presheaf.germ U (g y) hxU B :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hfr : IsFraction e' (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ A₀))
      (Y.presheaf.germ (g ⁻¹ᵁ U₀) y hyU₀ (g.app U₀ B₀)) := by
    rw [← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀, ← Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀,
      hgA, hgB]
    exact hf'
  obtain ⟨V, h₁, hy₁, f', hf'', hAB'⟩ := exists_local_fraction hyU₀ _ _ he' hfr
  refine ⟨U₀, h₀.trans hUW, V, h₁, hy₁, f₀, f', hf₀, hf'', ?_⟩
  have hne : toK V (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) ≠ 0 := by
    intro h0
    have h1 : Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀) = 0 :=
      MMP.Intersection.injective_toTotalQuotient V (by rw [h0, map_zero])
    have h2 : Y.presheaf.germ V y hy₁ (Y.presheaf.map (homOfLE h₁).op (g.app U₀ B₀)) =
        (g.stalkMap y).hom (X.presheaf.germ U (g y) hxU B) := by
      erw [TopCat.Presheaf.germ_res_apply]
      rw [← hgB]
      exact (Scheme.Hom.germ_stalkMap_apply g U₀ y hx₀ B₀).symm
    rw [h1, map_zero] at h2
    rw [← h2] at hb
    exact zero_notMem_nonZeroDivisors hb
  have e1 := congrArg (fun t => resK h₁ (rho g U₀ t)) hAB
  simp only [map_mul] at e1
  rw [rho_toK, rho_toK, resK_toK, resK_toK] at e1
  exact mul_left_cancel_totalQuotient ⟨y, hy₁⟩ hne (e1.trans hAB'.symm)

private theorem resK_rho_inv {U₀ : X.Opens} {V : Y.Opens} (hV : V ≤ g ⁻¹ᵁ U₀)
    {f₀ : (X.totalQuotientSheaf.obj.obj (op U₀))ˣ} {f' : (Y.totalQuotientSheaf.obj.obj (op V))ˣ}
    (hff : resK hV (rho g U₀ (f₀ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (f' : Y.totalQuotientSheaf.obj.obj (op V))) :
    resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) =
      (↑f'⁻¹ : Y.totalQuotientSheaf.obj.obj (op V)) := by
  have hinv : resK hV (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) *
      (f' : Y.totalQuotientSheaf.obj.obj (op V)) = 1 := by
    rw [← hff, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hinv)

/-- The pull-back of a section of `𝒪_X(E)` over `W` is a section of `𝒪_Y(E')` over `g⁻¹W`. -/
private theorem mem_rho {E : X.CartierDivisor} {E' : Y.CartierDivisor} (h : IsPullback g E E')
    (W : X.Opens) (s : X.totalQuotientSheaf.obj.obj (op W)) (hs : Mem E W s) :
    Mem E' (g ⁻¹ᵁ W) (rho g W s) := by
  refine Mem.of_locally fun y hy => ?_
  obtain ⟨U₀, hU₀, V, hV, hyV, f₀, f', hf₀, hf', hff⟩ := exists_local_pullback_equation g h y W hy
  refine ⟨V, hV.trans (g.preimage_mono hU₀), hyV, ?_⟩
  refine (mem_iff (U := V) (V := V) hf' le_rfl _).2 ?_
  obtain ⟨C, hC⟩ := (mem_iff (U := U₀) (V := U₀) hf₀ le_rfl _).1 (hs.res hU₀)
  refine ⟨Y.presheaf.map (homOfLE hV).op (g.app U₀ C), ?_⟩
  have e1 : resK (hV.trans (g.preimage_mono hU₀)) (rho g W s) =
      resK hV (rho g U₀ (resK hU₀ s)) := by
    rw [← rho_res g hU₀ s, resK_resK]
  rw [e1, ← hC, map_mul, map_mul, rho_toK, resK_toK]
  simp only [resK_id]
  rw [resK_rho_inv g hV hff]

open Opposite in
private theorem epi_of_surjective_on_covering {Z : Scheme.{u}} (B : Z.Opens → Prop)
    (hB : ∀ (U : Z.Opens) (T : CategoryTheory.Sieve U),
      (∀ ⦃V : Z.Opens⦄ (f : V ⟶ U), B V → T f) → T ∈ Opens.grothendieckTopology Z U)
    {M N : Z.Modules} (φ : M ⟶ N)
    (hφ : ∀ V : Z.Opens, B V → Function.Surjective (φ.val.app (op V))) : Epi φ := by
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Z)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map φ).hom :=
    ⟨fun s => hB _ _ fun V f hV => hφ V hV (N.val.map f.op s)⟩
  exact (SheafOfModules.toSheaf Z.ringCatSheaf).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- The map `𝒪_X(E) ⟶ g_* 𝒪_Y(E')`, `s ↦ g^*s`. -/
private noncomputable def lambdaPre {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    (MMP.CartierDivisor.sheaf E).val ⟶
      ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')).val :=
    (PresheafOfModules.homMk
      { app := fun U => AddCommGrpCat.ofHom
          { toFun := fun s => (⟨rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s),
              mem_rho g h U.unop _ (show ↥((MMP.CartierDivisor.sheafSubmodule E).obj U) from s).2⟩ :
                ↥((MMP.CartierDivisor.sheafSubmodule E').obj (op (g ⁻¹ᵁ U.unop))))
            map_zero' := Subtype.ext (by change rho g U.unop 0 = 0; exact map_zero _)
            map_add' := fun s t => Subtype.ext (by
              exact map_add (rho g U.unop) _ _) }
        naturality := fun {U V} i => by
          ext s
          exact Subtype.ext (rho_res g i.unop.le _).symm }
      (fun U r s => Subtype.ext (by
        change rho g U.unop (toK U.unop r * MMP.CartierDivisorSheaf.sectionVal s) =
          toK (g ⁻¹ᵁ U.unop) (g.app U.unop r) *
            rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s)
        rw [map_mul]
        exact congrArg (· * rho g U.unop (MMP.CartierDivisorSheaf.sectionVal s))
          (rho_toK g U.unop r))))

private noncomputable def lambdaHom {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') :
    MMP.CartierDivisor.sheaf E ⟶ (Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E') :=
  (SheafOfModules.fullyFaithfulForget _).preimage (lambdaPre g h)

private theorem lambdaHom_val {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') : (lambdaHom g h).val = lambdaPre g h :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage
    (show (SheafOfModules.forget X.ringCatSheaf).obj (MMP.CartierDivisor.sheaf E) ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj
        ((Scheme.Modules.pushforward g).obj (MMP.CartierDivisor.sheaf E')) from lambdaPre g h)

private theorem sectionVal_lambdaHom_app {E : X.CartierDivisor} {E' : Y.CartierDivisor}
    (h : IsPullback g E E') (U : X.Opens) (s : Γ(MMP.CartierDivisor.sheaf E, U)) :
    MMP.CartierDivisorSheaf.sectionVal ((lambdaHom g h).app U s) =
      rho g U (MMP.CartierDivisorSheaf.sectionVal s) := by
  have := congrArg (fun φ => φ.app (op U) s) (lambdaHom_val g h)
  exact congrArg MMP.CartierDivisorSheaf.sectionVal this

end Key

/-- The invertible sheaf `𝒪_X(D)` of a Cartier divisor. -/
private noncomputable abbrev sh {X : Scheme.{u}} (D : X.CartierDivisor) : X.Modules :=
  MMP.CartierDivisor.sheaf D

/-- The pull-back of `𝒪_X(D)` along a dominant morphism of integral schemes is `𝒪_Y(D')` for
`D'` a pull-back of `D`. -/
public theorem nonempty_pullback_sheaf_iso {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) [IsDominant g]
    {D : X.CartierDivisor} {D' : Y.CartierDivisor} (hD' : MMP.Intersection.IsPullback g D D') :
    Nonempty ((Scheme.Modules.pullback g).obj (MMP.CartierDivisor.sheaf D) ≅
      MMP.CartierDivisor.sheaf D') := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (sh D) := inferInstance
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (sh D') := inferInstance
  have hinvpb : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj (sh D)) :=
    SheafOfModules.isInvertible_pullback g _
  let ℓ := lambdaHom g hD'
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let ψ : (Scheme.Modules.pullback g).obj (sh D) ⟶
      sh D' := (adj.homEquiv _ _).symm ℓ
  have hψ : ∀ (U : X.Opens) (s : Γ(sh D, U)),
      ψ.app (g ⁻¹ᵁ U) ((adj.unit.app (sh D)).app U s) =
        ℓ.app U s := by
    have h1 : ℓ = adj.unit.app (sh D) ≫
        (Scheme.Modules.pushforward g).map ψ := by
      have := (adj.homEquiv _ _).apply_symm_apply ℓ
      rw [Adjunction.homEquiv_unit] at this
      exact this.symm
    exact fun U s => (congrArg (fun φ => φ.app U s) h1).symm
  have hepi : Epi ψ := by
    refine epi_of_surjective_on_covering
      (fun V : Y.Opens => Function.Surjective (ψ.app V)) ?_ ψ (fun V hV => hV)
    intro U T hT
    rw [Opens.mem_grothendieckTopology]
    intro y hy
    obtain ⟨U₀, -, V₀, hV₀, hyV₀, f₀, f', hf₀, hf', hff⟩ :=
      exists_local_pullback_equation g hD' y ⊤ trivial
    refine ⟨V₀ ⊓ U, homOfLE inf_le_right, hT (homOfLE inf_le_right) ?_, ⟨hyV₀, hy⟩⟩
    have hVV₀ : V₀ ⊓ U ≤ V₀ := inf_le_left
    intro t
    have hmem : Mem D' (V₀ ⊓ U) (MMP.CartierDivisorSheaf.sectionVal t) :=
      (show ↥((MMP.CartierDivisor.sheafSubmodule D').obj (op (V₀ ⊓ U))) from t).2
    obtain ⟨a, ha⟩ := (mem_iff (U := V₀) (V := V₀ ⊓ U) hf' hVV₀ _).1 hmem
    let e₀ : Γ(sh D, U₀) :=
      (⟨(↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀)), mem_inv hf₀⟩ :
        ↥((MMP.CartierDivisor.sheafSubmodule D).obj (op U₀)))
    let ε := (adj.unit.app (sh D)).app U₀ e₀
    refine ⟨a • ((Scheme.Modules.pullback g).obj
      (sh D)).presheaf.map
        (homOfLE (hVV₀.trans hV₀)).op ε, ?_⟩
    apply MMP.CartierDivisorSheaf.sectionVal_injective
    rw [Scheme.Modules.Hom.app_smul]
    have nat := PresheafOfModules.naturality_apply ψ.val (homOfLE (hVV₀.trans hV₀)).op ε
    have h4 := nat.trans (congrArg
      ((sh D').val.map (homOfLE (hVV₀.trans hV₀)).op)
      (hψ U₀ e₀))
    have h3 : MMP.CartierDivisorSheaf.sectionVal
        (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (sh D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) =
        resK (hVV₀.trans hV₀) (rho g U₀ (↑f₀⁻¹ : X.totalQuotientSheaf.obj.obj (op U₀))) := by
      have h5 := congrArg MMP.CartierDivisorSheaf.sectionVal h4
      refine h5.trans ?_
      exact congrArg (resK (hVV₀.trans hV₀)) (sectionVal_lambdaHom_app g hD' U₀ e₀)
    change toK (V₀ ⊓ U) a * MMP.CartierDivisorSheaf.sectionVal
      (ψ.app (V₀ ⊓ U) (((Scheme.Modules.pullback g).obj
          (sh D)).presheaf.map
            (homOfLE (hVV₀.trans hV₀)).op ε)) = _
    rw [h3, ← ha, ← resK_resK hVV₀ hV₀, resK_rho_inv g hV₀ hff]
  exact ⟨@asIso _ _ _ _ ψ (Stacks.Chow.GenuineChern.isIso_of_epi_of_isInvertible ψ hinvpb
    inferInstance)⟩

end SheafPullback

section CartierPullback

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]
    {X₀ X : Scheme.{u}} (s₀ : X₀ ⟶ Spec (.of k₀)) (s : X ⟶ Spec (.of K)) (π : X ⟶ X₀)

/-- For `q : Y ⟶ X` flat with `X` integral and `Y` locally Noetherian, every associated point of
`Y` lies over the generic point of `X`: on affine charts an associated prime of `Γ(Y, V)` is the
annihilator of some `b ≠ 0`, and flatness makes `b` torsion-free over `Γ(X, U)`, so the
contracted prime is zero. -/
private theorem map_eq_genericPoint_of_mem_schemeAssociatedPoints {Y X : Scheme.{u}} (q : Y ⟶ X)
    [Flat q] [IsIntegral X] [IsLocallyNoetherian Y] (y : Y)
    (hy : y ∈ Stacks.Divisors.schemeAssociatedPoints Y) :
    q y = genericPoint X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (q ⁻¹ᵁ U).isOpen
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  have : Nonempty U := ⟨⟨q y, hx⟩⟩
  let φ := (q.appLE U V hVU).hom
  let _ : Algebra Γ(X, U) Γ(Y, V) := φ.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, V) := q.flat_appLE hU hV hVU
  have : (SheafOfModules.unit Y.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Y
  have hp :=
    (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      (SheafOfModules.unit Y.ringCatSheaf) V hV hyV).mpr hy
  change IsAssociatedPrimeStacks Γ(Y, V) Γ(Y, V) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal at hp
  obtain ⟨hprime, b, hb⟩ := hp
  have hb0 : b ≠ 0 := by
    intro hh
    apply hprime.one_notMem
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    simp [hh]
  have hpbot : (hU.primeIdealOf ⟨q y, hx⟩).asIdeal = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    have ha' : φ a ∈ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
      have hnat := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hyV
      rw [← hnat] at ha
      exact ha
    rw [← hb, Submodule.mem_colon_span_singleton, Submodule.mem_bot] at ha'
    change φ a * b = 0 at ha'
    have hz : a • (b : Γ(Y, V)) = 0 := ha'
    exact (smul_eq_zero.mp hz).resolve_right hb0
  have hη : genericPoint X ∈ U :=
    (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr (by simpa using ‹Nonempty U›)
  have heq : hU.primeIdealOf ⟨q y, hx⟩ = hU.primeIdealOf ⟨genericPoint X, hη⟩ := by
    apply PrimeSpectrum.ext
    rw [hpbot, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    rfl
  simpa only [hU.fromSpec_primeIdealOf] using congrArg hU.fromSpec heq

/-- Every Cartier divisor on `X₀` has a pull-back along the flat base change `π`. -/
public theorem exists_isPullback
    (h : CategoryTheory.IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    (D₀ : X₀.CartierDivisor) : ∃ D : X.CartierDivisor, MMP.Intersection.IsPullback π D₀ D := by
  have hv : AlgebraicGeometry.IsVariety k₀ s₀ := hX₀.toIsVariety
  have : IsIntegral X₀ := hv.toIsIntegral
  have hft : LocallyOfFiniteType s₀ := inferInstance
  have hg : Flat (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Flat π := MorphismProperty.of_isPullback h.flip hg
  have hfts : LocallyOfFiniteType s := MorphismProperty.of_isPullback h hft
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  refine MMP.Intersection.exists_isPullback fun η hη => ?_
  rw [map_eq_genericPoint_of_mem_schemeAssociatedPoints π η hη]
  have : IsArtinianRing (X₀.presheaf.stalk (genericPoint X₀)) :=
    (inferInstance : IsArtinianRing X₀.functionField)
  exact MMP.Intersection.notMem_cartierSupport_of_isArtinianRing D₀ _

end CartierPullback

section Helpers

/-- A divisor `D` on `X` is the base change of `D₀` on `X₀` along `π : X ⟶ X₀`: its coefficient
at the prime divisor with closure `π⁻¹(closure P₀)` is that of `D₀` at `P₀`, and its support
consists of such prime divisors. -/
@[expose] public def IsBaseChange {R : Type*} [Zero R] {X₀ X : Scheme.{u}} (π : X ⟶ X₀)
    (D₀ : DivisorWithCoeffs R X₀) (D : DivisorWithCoeffs R X) : Prop :=
  (∀ (P₀ : MMP.Mori.PrimeDivisor X₀) (P : MMP.Mori.PrimeDivisor X),
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} → D P = D₀ P₀) ∧
    ∀ P : MMP.Mori.PrimeDivisor X, D P ≠ 0 →
      ∃ P₀ : MMP.Mori.PrimeDivisor X₀,
        closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint}

/-- Base changes of divisors add. -/
public theorem IsBaseChange.add {R : Type*} [AddCommMonoid R] {X₀ X : Scheme.{u}} {π : X ⟶ X₀}
    {D₀ E₀ : DivisorWithCoeffs R X₀} {D E : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D)
    (hE : IsBaseChange π E₀ E) : IsBaseChange π (D₀ + E₀) (D + E) := by
  refine ⟨fun P₀ P hP => by simp [hD.1 P₀ P hP, hE.1 P₀ P hP], fun P hP => ?_⟩
  by_cases h : D P = 0
  · exact hE.2 P (by simpa [h] using hP)
  · exact hD.2 P h

/-- The negative of a base change is the base change of the negative. -/
public theorem IsBaseChange.neg {R : Type*} [AddCommGroup R] {X₀ X : Scheme.{u}} {π : X ⟶ X₀}
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) :
    IsBaseChange π (-D₀) (-D) :=
  ⟨fun P₀ P hP => by simp [hD.1 P₀ P hP], fun P hP => hD.2 P (by simpa using hP)⟩

/-- Integer multiples of a base change are base changes of the multiples. -/
public theorem IsBaseChange.zsmul {R : Type*} [AddCommGroup R] {X₀ X : Scheme.{u}} {π : X ⟶ X₀}
    {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X} (hD : IsBaseChange π D₀ D) (n : ℤ) :
    IsBaseChange π (n • D₀) (n • D) :=
  ⟨fun P₀ P hP => by simp [hD.1 P₀ P hP], fun P hP => hD.2 P fun h => hP (by simp [h])⟩

/-- The base change of an integral divisor is also a base change as a `ℚ`-divisor. -/
public theorem IsBaseChange.toQDivisor {X₀ X : Scheme.{u}} {π : X ⟶ X₀} {D₀ : Divisor X₀}
    {D : Divisor X} (hD : IsBaseChange π D₀ D) :
    IsBaseChange π (Divisor.toQDivisor D₀) (Divisor.toQDivisor D) :=
  ⟨fun P₀ P hP => by
    change ((D P : ℤ) : ℚ) = ((D₀ P₀ : ℤ) : ℚ)
    rw [hD.1 P₀ P hP], fun P hP => hD.2 P fun h => hP (by
      change ((D P : ℤ) : ℚ) = 0
      rw [h]; rfl)⟩

end Helpers

end MMP.ProgramBaseChange
