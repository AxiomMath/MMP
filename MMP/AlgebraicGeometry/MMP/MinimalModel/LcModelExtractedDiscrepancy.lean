module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelDiscrepancyStrict

/-!
# Divisors extracted by a log canonical model have discrepancy below `-1`

Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕`,
through the modification `φ : X ⤏ Y`. A `φ⁻¹`-exceptional prime divisor `F` of `Y` lies over a
point of `X` at which `φ` is not defined, so the discrepancy of `ord_F` strictly increases from
`D_X` to `D_{𝓕,Y}`; with the admissibility of `𝓕` this forces `a(ord_F, D_X) < -1`. In particular
the coefficient of `F` in `D_{𝓕,Y}` is `1`.

## Main results

* `MMP.Flips.IsLogCanonicalModelOf.lt_neg_one_of_isInverseExceptional`.

## Implementation notes

The divisor `ord_F` of `k(X) = k(Y)` is represented on the `X` side by any divisor `E` over `X`
realizing `F` through `φ` (`MMP.Flips.IsRealizedOver`); such an `E` exists by
`MMP.Flips.IsFBirationalTransform`, and `a(ord_F, D_X)` is the discrepancy of its valuation.
Kollár et al. state the remark for the `g`-exceptional divisors of `Y`; for a `g`-exceptional
divisor `φ_* Q` the discrepancy is `-coeff_Q(D_X) ≥ -1`, so the assertion concerns the
`φ⁻¹`-exceptional divisors.

The proof: write `(V, h, E)` for the realization and `x = h(η_E)`. If `φ` were defined at `x`, with
value `y`, then `𝒪_{Y,y} ⊆ 𝒪_{X,x} ⊆ 𝒪_{V,E}` with local inclusions, so `y` is the center of
`ord_F` on `Y`, that is `y = η_F`; since `𝒪_{Y,η_F}` is a valuation ring, `𝒪_{X,x} = 𝒪_{V,E}` is a
discrete valuation ring, so `x` is the generic point of a prime divisor `Q` of `X` with
`φ_* Q = F`, which is impossible. Hence `φ` is not defined at `x`, and the strict comparison of
discrepancies on a log canonical model gives `-c_F = a(ord_F, D_{𝓕,Y}) > a(ord_F, D_X)`. If
`-a(ord_F, D_X) ≤ 1`, admissibility of `𝓕` gives `c_F ≥ -a(ord_F, D_X)`, a contradiction.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.22.4
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips

private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U := by
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  exact (_root_.genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- The generic point of `A` lies over every dense open of `X`, for dominant `a : A ⟶ X`. -/
private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a _ ∈ U
  rw [map_genericPoint_of_isDominant]
  exact genericPoint_mem_of_dense hU

/-- The preimage of a dense open under a dominant morphism of integral schemes is dense. -/
private theorem dense_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : Dense (U : Set X)) :
    Dense ((a ⁻¹ᵁ U : A.Opens) : Set A) :=
  (a ⁻¹ᵁ U).isOpen.dense ⟨_, genericPoint_mem_preimage a hU⟩

/-- The partial map `a⁻¹(dom g) ⟶ dom g ⟶ Y` is, at the generic point, `Spec k(A) ⟶ Spec k(X)`
followed by `g`. -/
private theorem fromFunctionField_morphismRestrict_comp {A X Y : Scheme.{u}} [IsIntegral A]
    [IsIntegral X] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) :
    (Scheme.PartialMap.mk (a ⁻¹ᵁ g.domain) (dense_preimage a g.dense_domain)
      ((a ∣_ g.domain) ≫ g.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField := by
  rw [partialMap_fromFunctionField_eq _ (genericPoint_mem_preimage a g.dense_domain),
    partialMap_fromFunctionField_eq _ (genericPoint_mem_of_dense g.dense_domain)]
  change _ ≫ (a ∣_ g.domain) ≫ g.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono g.domain.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk a).symm

/-- If `p' = g ∘ a` on `a⁻¹(dom g)` for a dominant `a : A ⟶ X`, then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` along `g` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  rw [← fromFunctionField_morphismRestrict_comp, ← hcomm,
    partialMap_fromFunctionField_eq _ (genericPoint_mem_preimage a g.dense_domain)]
  exact Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _

/-- For a partial isomorphism `e` representing a dominant `p : W ⟶ X` of integral schemes,
`Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source := genericPoint_mem_of_dense e.dense_source
  have hX : genericPoint X ∈ e.target := genericPoint_mem_of_dense e.dense_target
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p :=
    h1.trans (Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _)
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Two models `p : W ⟶ X`, `a : A ⟶ X` of the same rational map `m : Spec k(X) ⟶ Y`, on which
prime divisors `F_W` and `E` both give the valuation `ord_F` of `k(Y)`, give the same valuation
of `k(X)`. -/
private theorem valuationOver_eq_of_specMap_comp {X Y W A : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral W] [IsIntegral A] [IsLocallyNoetherian W] [IsLocallyNoetherian A]
    [IsNormal W] [IsNormal A] [IsNormal Y] [IsLocallyNoetherian Y]
    (m : Spec X.functionField ⟶ Y) (p : W ⟶ X) (q : W ⟶ Y) (a : A ⟶ X) (pA : A ⟶ Y)
    [IsDominant p] [IsDominant q] [IsDominant a] [IsDominant pA]
    (hp : Function.Bijective (functionFieldMap p)) (hq : Function.Surjective (functionFieldMap q))
    (hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ pA)
    (FW : Mori.PrimeDivisor W) (E : Mori.PrimeDivisor A) (F : Mori.PrimeDivisor Y)
    (hFW : FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation)
    (hE : E.divisorialValuation.comap (functionFieldMap pA) = F.divisorialValuation) :
    FW.valuationOver p = E.valuationOver a := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ : ∀ s, functionFieldMap p (θ s) = functionFieldMap q s := fun s =>
    ep.apply_symm_apply _
  have hθs : Function.Surjective θ := ep.symm.surjective.comp hq
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q := RingHom.ext hθ
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  have hm : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hW, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
    exact functionFieldMap_fromSpecStalk q
  have hθA : (functionFieldMap a).comp θ = functionFieldMap pA := by
    rw [← hm, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← functionFieldMap_fromSpecStalk pA] at hA
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp hA))
  refine Valuation.ext fun t => ?_
  obtain ⟨s, rfl⟩ := hθs t
  rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply, hθ,
    ← RingHom.comp_apply (functionFieldMap a) θ, hθA, ← Valuation.comap_apply, hFW, ← hE,
    Valuation.comap_apply]

/-- If `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` equals `Spec k(W) ⟶ W ⟶ Y`, then `φ` has a
representative `φ₀` such that `φ₀ ∘ p`, defined on `p⁻¹(dom φ₀)`, equals `q` as a rational map. -/
private theorem exists_partialMap_comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  refine ⟨φ₀, rfl, dense_preimage p φ₀.dense_domain,
    Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  simp only [Scheme.Hom.resLE_eq_morphismRestrict]
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_morphismRestrict_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom]

/-- The valuation of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    Mori.functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩,
    E, rfl⟩

/-- A prime divisor `F_W` of `W` over the generic point of a prime divisor `F` of `Y`, along which
`q : W ⟶ Y` is a local isomorphism, pulls `ord_F` back from `ord_{F_W}`. -/
private theorem comap_divisorialValuation_of_isIso_stalkMap {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian W] [IsLocallyNoetherian Y] [IsNormal W] [IsNormal Y]
    (q : W ⟶ Y) [IsDominant q] (FW : Mori.PrimeDivisor W) (F : Mori.PrimeDivisor Y)
    (heq : q FW.genericPoint = F.genericPoint) [IsIso (q.stalkMap FW.genericPoint)] :
    FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso q FW F heq t]

/-- If `p = g ∘ a` on `a⁻¹(dom g)` for a dominant `a`, then `p = g' ∘ a` on `a⁻¹(dom g')` for
every representative `g'` of the same rational map. -/
private theorem comp_eq_of_toRationalMap_eq {A X Y : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (a : A ⟶ X) [IsDominant a] (p : A ⟶ Y) (g g' : X.PartialMap Y)
    (hgg : g.toRationalMap = g'.toRationalMap)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p = (a ∣_ g.domain) ≫ g.hom) :
    (a ⁻¹ᵁ g'.domain).ι ≫ p = (a ∣_ g'.domain) ≫ g'.hom := by
  let m : A.PartialMap Y :=
    ⟨a ⁻¹ᵁ g'.domain, dense_preimage a g'.dense_domain, (a ∣_ g'.domain) ≫ g'.hom⟩
  have h1 : m.toRationalMap = p.toRationalMap := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      fromFunctionField_morphismRestrict_comp a g',
      ← Scheme.RationalMap.fromFunctionField_toRationalMap, ← hgg,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      specMap_functionFieldMap_fromFunctionField a g p hcomm,
      MMP.Flips.RationalMap.fromFunctionField_hom]
  exact ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)).symm

private theorem surjective_of_comp {R S T : CommRingCat.{u}} {f : R ⟶ S} {g : S ⟶ T}
    (H : Function.Surjective (f ≫ g)) : Function.Surjective g :=
  (ConcreteCategory.coe_comp f g ▸ H).of_comp

private theorem surjective_comp {R S T : CommRingCat.{u}} {f : R ⟶ S} {g : S ⟶ T}
    (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (f ≫ g) :=
  ConcreteCategory.coe_comp f g ▸ hg.comp hf

/-- If `p = g ∘ a` on `a⁻¹(dom g)`, then `p(z) = g(a(z))` for every `z` with `a(z) ∈ dom g`. -/
private theorem apply_eq_of_comp_eq {A X Y : Scheme.{u}} (a : A ⟶ X) (p : A ⟶ Y)
    (g : X.PartialMap Y) {z : A} (hz : a z ∈ g.domain)
    (hV : (a ⁻¹ᵁ g.domain).ι ≫ p = (a ∣_ g.domain) ≫ g.hom) : p z = g.hom ⟨a z, hz⟩ := by
  let v : (a ⁻¹ᵁ g.domain).toScheme := ⟨z, show z ∈ a ⁻¹ᵁ g.domain from hz⟩
  have h1 : ((a ⁻¹ᵁ g.domain).ι ≫ p) v = ((a ∣_ g.domain) ≫ g.hom) v := by rw [hV]
  rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    show (a ∣_ g.domain) v = ⟨a z, hz⟩ from Subtype.ext (morphismRestrict_base_coe _ _ _)] at h1

/-- If `p = h ∘ a` near `z` and the stalk map of `p` at `z` is an isomorphism, then the stalk map
of `a` at `z` is onto: `𝒪_{Y,p(z)} ⟶ 𝒪_{X,a(z)} ⟶ 𝒪_{A,z}` is the stalk map of `p`. -/
private theorem surjective_stalkMap_of_comp_eq {A X Y : Scheme.{u}} (a : A ⟶ X) (p : A ⟶ Y)
    (U : X.Opens) (h : U.toScheme ⟶ Y) (hV : (a ⁻¹ᵁ U).ι ≫ p = (a ∣_ U) ≫ h) (z : A)
    (hz : a z ∈ U) [IsIso (p.stalkMap z)] : Function.Surjective (a.stalkMap z) := by
  let v : (a ⁻¹ᵁ U).toScheme := ⟨z, show z ∈ a ⁻¹ᵁ U from hz⟩
  have hι : Function.Surjective ((a ⁻¹ᵁ U).ι.stalkMap v) := by
    have := (ConcreteCategory.bijective_of_isIso ((a ⁻¹ᵁ U).stalkIso v).inv).2
    rwa [Scheme.Opens.stalkIso_inv] at this
  have s1 : Function.Surjective (((a ⁻¹ᵁ U).ι ≫ p).stalkMap v) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact surjective_comp (ConcreteCategory.bijective_of_isIso (p.stalkMap z)).2 hι
  rw [Scheme.Hom.stalkMap_congr_hom _ _ hV v] at s1
  have s2 := surjective_of_comp s1
  rw [Scheme.Hom.stalkMap_comp] at s2
  change Function.Surjective (a.stalkMap v.1)
  rw [Arrow.iso_w' (morphismRestrictStalkMap a U v)]
  exact surjective_comp (ConcreteCategory.bijective_of_isIso _).2
    (surjective_comp (surjective_of_comp s2) (ConcreteCategory.bijective_of_isIso _).2)

/-- The stalk maps of a dominant morphism of integral schemes are injective. -/
private theorem injective_stalkMap_of_isDominant {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (f : A ⟶ X) [IsDominant f] (x : A) : Function.Injective (f.stalkMap x) := by
  intro b b' hbb
  have := congrArg (algebraMap (A.presheaf.stalk x) A.functionField) hbb
  rw [← MMP.Mori.functionFieldMap_algebraMap_stalk,
    ← MMP.Mori.functionFieldMap_algebraMap_stalk] at this
  exact IsFractionRing.injective _ _ ((functionFieldMap f).injective this)

/-- If `ord_E` pulls back to `ord_F` along a dominant `p`, then `p` maps `η_E` to `η_F`. -/
private theorem map_genericPoint_eq_of_comap_eq {k : Type u} [Field k] {V Y : Scheme.{u}}
    [IsIntegral V] [IsIntegral Y] [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian Y]
    [IsNormal Y] (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] (p : V ⟶ Y) [IsDominant p]
    {E : Mori.PrimeDivisor V} {F : Mori.PrimeDivisor Y}
    (hval : E.divisorialValuation.comap (functionFieldMap p) = F.divisorialValuation) :
    p E.genericPoint = F.genericPoint := by
  refine MMP.Positivity.DivisorOver.eq_of_dominates sY F.divisorialValuation ?_ ?_ ?_ ?_
  · intro b
    rw [← hval, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
      Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨_, rfl⟩
  · intro b hb
    rw [← hval, Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk,
      Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 hb (isUnit_of_map_unit _ _ hu)
  · intro b
    rw [Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨b, rfl⟩
  · intro b hb
    exact (F.divisorialValuation_algebraMap_lt_one_iff b).2 hb

/-- **The center of an extracted divisor lies outside the domain of `φ`.** If a divisor `E` over
`X` realizes a `φ⁻¹`-exceptional prime divisor `F` of `Y` through `φ`, then `φ` is not defined at
the image `E.f(η_E)` of the generic point of `E`. -/
private theorem map_genericPoint_notMem_domain {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hXn : Mori.IsNormalVariety k sX) (hYn : Mori.IsNormalVariety k sY)
    {φ : X.RationalMap Y} {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) :
    E.f E.E.genericPoint ∉ φ.domain := by
  intro hxd
  obtain ⟨g', hxg', hg'⟩ := Scheme.RationalMap.mem_domain.mp hxd
  obtain ⟨g, p, hp, hgφ, hcomm, hval⟩ := hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := hp.isDominant
  haveI : IsSeparated sY := hYn.1.toIsSeparated
  haveI : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = sY ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hV := comp_eq_of_toRationalMap_eq E.f p g g' (hgφ.trans hg'.symm) hcomm
  set η := E.E.genericPoint
  have hpη : p η = g'.hom ⟨E.f η, hxg'⟩ :=
    apply_eq_of_comp_eq E.f p g' hxg' hV
  have hpF : p η = F.genericPoint := map_genericPoint_eq_of_comap_eq sY p hval
  haveI : ValuationRing (Y.presheaf.stalk (p η)) := by
    rw [hpF]
    haveI := F.isDiscreteValuationRing_localRing
    infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing p hp.functionFieldMap_bijective η
  have hsurj := surjective_stalkMap_of_comp_eq E.f p g'.domain g'.hom hV η hxg'
  have hdim : Order.coheight (E.f η) = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective (E.f.stalkMap η).hom
      ⟨injective_stalkMap_of_isDominant E.f η, hsurj⟩)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      E.E.coheight_genericPoint] at h1
    exact_mod_cast h1
  have hc : ¬ 2 ≤ codimension E.toDivisorOver.center := by
    rw [MMP.Positivity.DivisorOver.codimension_center, hdim]
    decide
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hXn] at hc
  push Not at hc
  obtain ⟨P, hvP⟩ := hc
  have hxP : E.f η = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXn.1 hvP
  refine hF P (transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' (hxP ▸ hxg') ?_)
  rw [← hpF, hpη]
  congr 1
  exact Subtype.ext hxP

/-- **Discrepancies of a realized divisor increase strictly on a log canonical model.** If a
divisor `E` over `X` realizes the prime divisor `F` of `Y` through `φ` and `φ` is not defined at
the image `E.f(η_E)` of its generic point, then `a(E, D_X) < a(ord_F, D_{𝓕,Y})`. -/
private theorem isDiscrepancy_lt_of_isRealizedOver {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E)
    (hx : E.f E.E.genericPoint ∉ φ.domain)
    {a b : ℝ} (hb : IsDiscrepancy sY n K_Y G F.divisorialValuation b)
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a) : a < b := by
  obtain ⟨hfP, hgP, hmod, ⟨hXn, hYn, -⟩, -⟩ := id hM.1
  haveI := hfP
  haveI := hgP
  obtain ⟨W, p, q, hWv, hWs, hpP, hqP, hpb, hqb, ⟨ψ, ⟨e, he1, he2⟩, hψq⟩, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model sX sY sZ hXn hYn hZ f g hfs hgs φ hmod
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWv.toIsIntegral
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWn : Mori.IsNormalVariety k (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hqs : q ≫ sY = p ≫ sX := by rw [← hgs, ← hfs, ← Category.assoc, ← hcomm, Category.assoc]
  have KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
    rw [← hψq, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
      specMap_functionFieldMap_fromFunctionField_symm p e he1]
  have hW : IsCommonModel k sX sY sZ (p ≫ sX) f g φ p q :=
    { isVariety_X := hXn.1
      isVariety_Y := hYn.1
      isVariety_Z := hZ
      comp_f := hfs
      comp_g := hgs
      isProper_f := hfP
      isProper_g := hgP
      isModificationOf := hmod
      isNormalVariety := hWn
      comp_p := rfl
      comp_q := hqs
      isProper_p := hpP
      isProper_q := hqP
      isBirationalMorphism_p := hpb
      isBirationalMorphism_q := hqb
      comp_eq := exists_partialMap_comp_eq_of_specMap_fromFunctionField_eq φ p q KF }
  obtain ⟨FW, hFWeq, hFWiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYn (hqs ▸ hWn) hqb F
  have hFW := comap_divisorialValuation_of_isIso_stalkMap q FW F hFWeq
  obtain ⟨g₀, pE, hpE, hg₀, hcE, hval⟩ := hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI := hpE.isDominant
  have hA : Spec.map (CommRingCat.ofHom (functionFieldMap E.f)) ≫ φ.fromFunctionField =
      E.Y.fromSpecStalk (genericPoint E.Y) ≫ pE :=
    hg₀ ▸ specMap_functionFieldMap_fromFunctionField E.f g₀ pE hcE
  have hv := valuationOver_eq_of_specMap_comp φ.fromFunctionField p q E.f pE
    hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective.2 KF hA FW E.E F hFW hval
  exact hM.isDiscrepancy_lt hW (hasNonemptyCenter_valuation E) E rfl hx
    FW.divisorialValuation hv hFW b a hb ha

/-- **Divisors extracted by a log canonical model.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a log
canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕 = c` (`MMP.Flips.IsLogCanonicalModelOf`,
with `G = D_{𝓕,Y}`), through `φ : X ⤏ Y`, where `Z` is a variety over a field `k` of
characteristic zero and `f`, `g` are morphisms over `k`. Let `F` be a
`φ⁻¹`-exceptional prime divisor of `Y`, `E` a divisor over `X` realizing `F` through `φ`, and
`a = a(ord_F, D_X)` the discrepancy of its valuation. Then `a < -1`. -/
@[mmp "lem_fa2_lc_model_exceptional_discrepancy_lt_minus_one"]
public theorem IsLogCanonicalModelOf.lt_neg_one_of_isInverseExceptional {k : Type u} [Field k]
    [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hM : IsLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) {a : ℝ}
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a) : a < -1 := by
  obtain ⟨-, -, -, hFB, hKG, hRel, -⟩ := id hM.1
  obtain ⟨hXn, hYn, -, -, -, -, _, hFs, -, hc, -⟩ := id hFB
  obtain ⟨-, hcmin⟩ := hc F ((hFs F).2 hF)
  have hlt := isDiscrepancy_lt_of_isRealizedOver hZ hfs hgs hM hE
    (map_genericPoint_notMem_domain hXn hYn hF hE)
    (IsFBirationalTransform.isDiscrepancy_divisorialValuation hFB hRel.2.1.2.1 hKG hF) ha
  have hmin := hcmin E a hE ha
  by_contra h
  rw [min_eq_right (by linarith)] at hmin
  linarith

end MMP.Flips
