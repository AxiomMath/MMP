/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Birational contractions, non-exceptional divisors and small contractions

Three facts implicit in §2.1 of *Flips and abundance for algebraic threefolds* (FA).

A birational contraction `f : Y → X` (a proper morphism of varieties of the same dimension with
`𝒪_X = f_* 𝒪_Y`) is surjective and birational: its image is closed, and an open subset of `X`
missing it would have no sections upstairs; and the function field extension `k(X) ⊆ k(Y)` is
finite, so over a dense affine open `U = Spec A` the morphism is finite, `f⁻¹(U) = Spec B` with
`B = 𝒪_Y(f⁻¹U) = 𝒪_X(U) = A`.

A divisor `(Y, f, E)` over a normal variety `X` which is not exceptional has center a prime
divisor `P = f(E)`, the local rings `𝒪_{Y,E}` and `𝒪_{X,P}` are the same subring of the function
field, and `ord_E = ord_P`.

A birational contraction to a normal variety is small exactly when its exceptional set has
codimension at least two: off `f(Ex(f))` every fibre is finite, so `f` is an isomorphism there.

## Main results

* `MMP.Flips.IsBirationalContraction.surjective_and_isBirational`: a birational contraction is
  surjective and birational.
* `MMP.Flips.ProperDivisorOver.exists_primeDivisor_of_not_isExceptional`: a non-exceptional
  divisor over a normal variety is a prime divisor of it, with the same local ring and valuation.
* `MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet`: a birational contraction to
  a normal variety is small if and only if its exceptional set has codimension `≥ 2`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.1.4, 2.1.6,
  2.5
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Flips

/-! ### Codimension and coheight -/

section Codimension

variable {T : Scheme.{u}}

/-- The codimension of the closure of a point is the coheight of the point. -/
theorem codimension_closureSingleton (x : T) :
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton x =
    (irreducibleSetEquivPoints (α := T)).symm x from rfl, Order.coheight_orderIso]

/-- A closed subset has codimension `≥ n` if and only if every point of it has coheight `≥ n`. -/
theorem le_closedsCodimension_iff_le_coheight {C : Closeds T} {n : ℕ∞} :
    n ≤ Mori.closedsCodimension C ↔ ∀ x ∈ (C : Set T), n ≤ Order.coheight x := by
  rw [Mori.le_closedsCodimension_iff]
  refine ⟨fun h x hx => ?_, fun h Z hZ => ?_⟩
  · rw [← codimension_closureSingleton]
    exact h _ (closure_minimal (Set.singleton_subset_iff.mpr hx) C.isClosed)
  · set x := irreducibleSetEquivPoints (α := T) Z
    have hZx : Z = IrreducibleCloseds.closureSingleton x :=
      ((irreducibleSetEquivPoints (α := T)).symm_apply_apply Z).symm
    rw [hZx, codimension_closureSingleton]
    refine h x (hZ ?_)
    rw [hZx]
    exact subset_closure rfl

end Codimension

/-! ### Dimension of the closure of a point -/

section Dimension

variable {k : Type u} [Field k]

/-- On an integral scheme locally of finite type over `k`, the dimension of the closure of a point
plus its coheight is the dimension of the scheme. -/
theorem topologicalKrullDim_closure_singleton_add_coheight {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (y : Y) :
    topologicalKrullDim (closure {y} : Set Y) + Order.coheight y = topologicalKrullDim Y := by
  let _ : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint y)
  rwa [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at h

private theorem le_of_add_eq_add_of_le {a b : WithBot ℕ∞} {c d : ℕ∞}
    (h : a + c = b + d) (hba : b ≤ a) (ha : a ≠ ⊤) (ha' : a ≠ ⊥) : c ≤ d := by
  lift a to ℕ∞ using ha'
  have ha : a ≠ ⊤ := by exact_mod_cast ha
  have : ((a + c : ℕ∞) : WithBot ℕ∞) ≤ ((a + d : ℕ∞) : WithBot ℕ∞) := by
    push_cast; rw [h]; gcongr
  exact (ENat.add_le_add_iff_left ha).mp (WithBot.coe_le_coe.mp this)

/-- For a morphism `f : Y ⟶ X` of varieties of the same dimension, the coheight of a point
`y ∈ Y` is at most that of `f(y)`. -/
theorem coheight_le_coheight_map {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) (hX : Mori.IsVariety k sX) (hY : Mori.IsVariety k sY) (f : Y ⟶ X)
    (hf : f ≫ sX = sY) (hdim : topologicalKrullDim Y = topologicalKrullDim X) (y : Y) :
    Order.coheight y ≤ Order.coheight (f y) := by
  have := hX.toIsIntegral
  have := hY.toIsIntegral
  have := hX.toLocallyOfFiniteType
  have := hY.toLocallyOfFiniteType
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hY' := topologicalKrullDim_closure_singleton_add_coheight sY y
  have hX' := topologicalKrullDim_closure_singleton_add_coheight sX (f y)
  have htr := trdeg_residueField_add sY sX f hf y
  have hle : topologicalKrullDim (closure {f y} : Set X) ≤
      topologicalKrullDim (closure {y} : Set Y) := by
    rw [topologicalKrullDim_closure_singleton_eq_trdeg k X sX,
      topologicalKrullDim_closure_singleton_eq_trdeg k Y sY, WithBot.coe_le_coe]
    exact Cardinal.toENat.monotone' (htr ▸ le_self_add)
  have hne : topologicalKrullDim (closure {y} : Set Y) ≠ ⊤ := by
    intro htop
    have := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
    rw [← hY', htop] at this
    exact this (by
      rw [show (⊤ : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_add, top_add])
  have hne' : topologicalKrullDim (closure {y} : Set Y) ≠ ⊥ := by
    rw [topologicalKrullDim_closure_singleton_eq_trdeg k Y sY]
    exact WithBot.coe_ne_bot
  exact le_of_add_eq_add_of_le (hY'.trans (hdim.trans hX'.symm)) hle hne hne'

end Dimension

/-! ### Birational contractions are modifications -/

section BirationalContraction

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}

/-- A birational contraction is surjective. -/
theorem IsBirationalContraction.surjective (hf : IsBirationalContraction k sX sY f) :
    Surjective f := by
  have := hf.isProper
  have := hf.isIso_app
  have hdom : IsDominant f := by
    refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    let V' : X.Opens := ⟨V, hV⟩
    have hbot : f ⁻¹ᵁ V' = ⊥ := by
      refine Opens.ext ?_
      rw [Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
    have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ V') := by
      rw [hbot]
      infer_instance
    have : Subsingleton Γ(X, V') :=
      (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
    obtain ⟨x, hx⟩ := hVne
    have h10 := congrArg (X.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(X, V')) 0)
    rw [map_one, map_zero] at h10
    exact one_ne_zero h10
  exact ⟨Set.range_eq_univ.mp (by
    rw [← f.isClosedMap.isClosed_range.closure_eq, hdom.denseRange.closure_range])⟩

/-- **FA 2.1.4.** A birational contraction `f : Y ⟶ X` is surjective and birational, that is, a
modification. -/
@[mmp "lem_fa2_birational_contraction_is_birational"]
theorem IsBirationalContraction.surjective_and_isBirational
    (hf : IsBirationalContraction k sX sY f) :
    Surjective f ∧ Mori.RationalMap.IsBirational (X := Y) f.toRationalMap := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have := hf.isProper
  have hfX := hf.isIso_app
  have hsurj := hf.surjective
  refine ⟨hsurj, ?_⟩
  obtain ⟨-, -, hcomp, -, -⟩ := hf.toIsContraction
  subst hcomp
  have := hf.isVariety_target.toLocallyOfFiniteType
  have := hf.isVariety_source.toLocallyOfFiniteType
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sX
  obtain ⟨U₀, hU₀, hfin₀⟩ :=
    Mori.exists_dense_isFinite_restrict_of_topologicalKrullDim_eq sX f hf.dim_eq
  obtain ⟨x, hx⟩ := hU₀.nonempty
  obtain ⟨U, hU, hxU, hUU₀⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ U₀ := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUU₀⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U₀.isOpen
    exact ⟨U, hU, hxU, hUU₀⟩
  have hfin : IsFinite (f ∣_ U) := by
    have hEq : U₀.ι ''ᵁ (U₀.ι ⁻¹ᵁ U) = U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hUU₀]
    have := Stacks.Morphisms.isFinite_respectsIso
    have := Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
    exact (MorphismProperty.arrow_mk_iso_iff @IsFinite
      (morphismRestrictRestrict f U₀ (U₀.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f hEq)).mp
      (IsZariskiLocalAtTarget.restrict hfin₀ _)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U) := isAffine_of_isAffineHom (f ∣_ U)
  have : IsIso (f ∣_ U).appTop := by
    rw [morphismRestrict_appTop]
    exact IsIso.comp_isIso' (hfX _) (Functor.map_isIso _ _)
  have hiso : IsIso (f ∣_ U) := by
    have : IsIso ((f ∣_ U) ≫ U.toScheme.toSpecΓ) := by
      rw [Scheme.toSpecΓ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right (f ∣_ U) U.toScheme.toSpecΓ
  obtain ⟨y, hy⟩ := hsurj.surj x
  exact isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ U) U ⟨y, by simpa [hy] using hxU⟩
    ⟨x, hxU⟩ le_rfl (by rwa [Scheme.Hom.resLE_eq_morphismRestrict])

end BirationalContraction

/-! ### Non-exceptional divisors over a normal variety -/

section NonExceptional

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The image `f(η_E)` of the generic point of a non-exceptional divisor over `X` has coheight
less than two. -/
theorem ProperDivisorOver.not_two_le_coheight_of_not_isExceptional [IsIntegral X]
    [LocallyOfFiniteType sX] (D : ProperDivisorOver k sX) (hD : ¬ D.IsExceptional) :
    ¬ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  intro h2
  refine hD ?_
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint,
    ← topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)]
  gcongr
  exact (WithBot.coe_le_coe.mpr h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)

/-- **FA 2.5.** Let `X` be a normal variety and `(Y, f, E)` a divisor over `X` which is not
exceptional. Then `f(E)` is a prime divisor `P` of `X` (with generic point `f(η_E)`), the local
rings `𝒪_{Y,E}` and `𝒪_{X,P}` are the same subring of `k(X) ≅ k(Y)`, and `ord_E = ord_P`. -/
@[mmp "lem_fa2_nonexceptional_divisor_is_prime_of_x"]
theorem ProperDivisorOver.exists_primeDivisor_of_not_isExceptional [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (hX : Mori.IsNormalVariety k sX)
    (D : ProperDivisorOver k sX) (hD : ¬ D.IsExceptional) :
    haveI := D.isIntegral
    haveI := D.isDominant
    ∃ P : Mori.PrimeDivisor X, (D.center : Set X) = P.support ∧
      D.f D.E.genericPoint = P.genericPoint ∧
      (algebraMap D.E.localRing D.Y.functionField).range.comap (functionFieldMap D.f) =
        (algebraMap P.localRing X.functionField).range ∧
      D.valuation = P.divisorialValuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := hX.1.toLocallyOfFiniteType
  have hc : ¬ 2 ≤ codimension D.toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center]
    exact D.not_two_le_coheight_of_not_isExceptional hD
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hc
  simp only [not_forall, not_not] at hc
  obtain ⟨P, hv⟩ := hc
  have hη : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hval : D.valuation = P.divisorialValuation := by
    change D.toDivisorOver.valuation = _
    rw [hv]
    ext φ
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  refine ⟨P, ?_, hη, ?_, hval⟩
  · rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hη,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  · ext g
    rw [Subring.mem_comap, ← Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      ← Mori.PrimeDivisor.divisorialValuation_le_one_iff, ← hval]
    rfl

end NonExceptional

/-! ### Small birational contractions -/

section Small

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)}

/-- The exceptional set `Ex(f)` is closed. -/
theorem isClosed_exceptionalSet (f : Y ⟶ X) : IsClosed (exceptionalSet f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  simp only [exceptionalSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hy
  obtain ⟨V, hyV, hV⟩ := hy
  refine ⟨V, fun z hz => ?_, V.isOpen, hyV⟩
  simp only [exceptionalSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
  exact ⟨V, hz, hV⟩

/-- The exceptional set `Ex(f)` as a closed subset. -/
def exceptionalCloseds (f : Y ⟶ X) : Closeds Y :=
  ⟨exceptionalSet f, isClosed_exceptionalSet f⟩

@[simp]
theorem coe_exceptionalCloseds (f : Y ⟶ X) :
    (exceptionalCloseds f : Set Y) = exceptionalSet f := rfl

@[simp]
theorem mem_exceptionalCloseds {f : Y ⟶ X} {y : Y} :
    y ∈ exceptionalCloseds f ↔ y ∈ exceptionalSet f := Iff.rfl

/-- A point outside `Ex(f)` has an open neighbourhood on which `f` is an open immersion. -/
theorem exists_isOpenImmersion_of_notMem_exceptionalSet {f : Y ⟶ X} {y : Y}
    (hy : y ∉ exceptionalSet f) : ∃ V : Y.Opens, y ∈ V ∧ IsOpenImmersion (V.ι ≫ f) := by
  simpa [exceptionalSet] using hy

/-- Outside `Ex(f)`, `f` preserves coheights. -/
theorem coheight_map_of_notMem_exceptionalSet {f : Y ⟶ X} {y : Y}
    (hy : y ∉ exceptionalSet f) : Order.coheight (f y) = Order.coheight y := by
  obtain ⟨V, hyV, hV⟩ := exists_isOpenImmersion_of_notMem_exceptionalSet hy
  let y' : V.toScheme := ⟨y, hyV⟩
  exact (coheight_eq_of_isOpenImmersion (x := y') (V.ι ≫ f)).trans
    (coheight_eq_of_isOpenImmersion (x := y') V.ι).symm

/-- For a proper morphism, a fibre missing the exceptional set is finite. -/
theorem finite_preimage_singleton_of_subset_compl_exceptionalSet {f : Y ⟶ X} [IsProper f]
    {x : X} (hfib : f ⁻¹' {x} ⊆ (exceptionalSet f)ᶜ) : (f ⁻¹' {x}).Finite := by
  have hU : ∀ y ∈ f ⁻¹' {x}, ∃ U : Y.Opens, y ∈ U ∧ IsOpenImmersion (U.ι ≫ f) :=
    fun y hy => exists_isOpenImmersion_of_notMem_exceptionalSet (hfib hy)
  choose! U hyU hU using hU
  obtain ⟨t, hts, hcov⟩ :=
    (f.isProperMap.isCompact_preimage isCompact_singleton).elim_nhds_subcover
      (fun y => (U y : Set Y)) (fun y hy => (U y).isOpen.mem_nhds (hyU y hy))
  refine t.finite_toSet.subset fun z hz => ?_
  obtain ⟨y, hyt, hzy⟩ := Set.mem_iUnion₂.mp (hcov hz)
  have hy := hts y hyt
  have := hU y hy
  have hzy' : (⟨z, hzy⟩ : (U y).toScheme) = ⟨y, hyU y hy⟩ :=
    ((U y).ι ≫ f).isOpenEmbedding.injective (hz.trans hy.symm)
  obtain rfl : z = y := congrArg Subtype.val hzy'
  exact hyt

/-- A birational contraction to a normal variety is an isomorphism over the complement of the
image of its exceptional set. -/
theorem IsBirationalContraction.isIso_morphismRestrict_compl_image_exceptionalSet [IsNormal X]
    {f : Y ⟶ X} [IsProper f] (hf : IsBirationalContraction k sX sY f) :
    IsIso (f ∣_ (⟨f '' exceptionalSet f, f.isClosedMap _ (isClosed_exceptionalSet f)⟩ :
      Closeds X).compl) := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have := hf.isVariety_target.toLocallyOfFiniteType
  have := hf.isVariety_target.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  have hbir : AlgebraicGeometry.IsBirational f :=
    Resolution.Bridges.isBirational_of_isBirationalMorphism hf.surjective_and_isBirational.2
  refine Mori.isBiregular_iff_le_biregularLocus.mpr fun x hx => ?_
  have hfin : (f ⁻¹' {x}).Finite :=
    finite_preimage_singleton_of_subset_compl_exceptionalSet fun y hy hyE => hx ⟨y, hyE, hy⟩
  have := IsNormal.stalk_normal (X := X) x
  obtain ⟨U, hxU, hUiso⟩ := exists_isIso_restrict_of_finite_fiber_of_normal f hbir x hfin
  exact Mori.le_biregularLocus hUiso hxU

/-- **FA 2.1.6, "equivalently, the exceptional set has codimension `≥ 2`".** A birational
contraction `f : Y ⟶ X` to a normal variety is small if and only if its exceptional set `Ex(f)`
has codimension at least two in `Y`. -/
@[mmp "lem_fa2_small_iff_exceptional_codim_two"]
theorem isSmall_iff_two_le_closedsCodimension_exceptionalSet [IsNormal X] {f : Y ⟶ X}
    (hf : IsBirationalContraction k sX sY f) :
    IsSmall k sX sY f ↔ 2 ≤ Mori.closedsCodimension (exceptionalCloseds f) := by
  constructor
  · rintro ⟨-, V, W, hV, -, h, hiso⟩
    rw [le_closedsCodimension_iff_le_coheight] at hV ⊢
    intro y hy
    refine hV y ?_
    by_contra hyV
    refine hy ⟨V.compl, hyV, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι f h]
    infer_instance
  · intro hE
    have := hf.isProper
    rw [le_closedsCodimension_iff_le_coheight] at hE
    set E := exceptionalSet f
    let W : Closeds X := ⟨f '' E, f.isClosedMap _ (isClosed_exceptionalSet f)⟩
    let V : Closeds Y := ⟨f ⁻¹' (f '' E), W.isClosed.preimage f.continuous⟩
    have hcoh : ∀ y : Y, Order.coheight y ≤ Order.coheight (f y) :=
      coheight_le_coheight_map sX sY hf.isVariety_target hf.isVariety_source f hf.comp_eq
        hf.dim_eq
    have hiso : IsIso (f ∣_ W.compl) :=
      hf.isIso_morphismRestrict_compl_image_exceptionalSet
    refine ⟨hf, V, W, ?_, ?_, fun y hy => hy, ?_⟩
    · rw [le_closedsCodimension_iff_le_coheight]
      intro y hy
      by_cases hyE : y ∈ E
      · exact hE y hyE
      · obtain ⟨e, he, hfe⟩ := hy
        rw [← coheight_map_of_notMem_exceptionalSet hyE, ← hfe]
        exact (hE e he).trans (hcoh e)
    · rw [le_closedsCodimension_iff_le_coheight]
      rintro x ⟨e, he, rfl⟩
      exact (hE e he).trans (hcoh e)
    · have e₂ : V.compl = f ⁻¹ᵁ W.compl := Opens.ext rfl
      refine (Scheme.Hom.resLE_congr f (U := W.compl) (V := V.compl) (fun y hy => hy) rfl e₂
        (MorphismProperty.isomorphisms Scheme)).mpr ?_
      change IsIso _
      rwa [Scheme.Hom.resLE_eq_morphismRestrict]

end Small

end MMP.Flips
