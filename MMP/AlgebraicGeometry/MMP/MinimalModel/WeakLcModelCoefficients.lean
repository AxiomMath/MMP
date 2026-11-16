module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison

/-!
# The coefficients of a weak log canonical model are forced

Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of `f : (X, D_X) ⟶ Z` with respect to
`𝓕 = (c₁, …, c_k)`, through the modification `φ : X ⤏ Y`. Admissibility of `𝓕` only bounds each
`c_i` between `min {1, -a(ord_{F_i}, D_X)}` and `1`; on a weak log canonical model the lower bound
is attained: `c_i = min {1, -a(ord_{F_i}, D_X)}` for every `φ⁻¹`-exceptional prime `F_i`.

## Main results

* `MMP.Flips.IsWeakLogCanonicalModelOf.eq_min_of_isInverseExceptional`.

## Implementation notes

The divisor `ord_{F_i}` of `k(X) = k(Y)` is represented on the `X` side by any divisor `E` over
`X` realizing `F_i` through `φ` (`MMP.Flips.IsRealizedOver`); such an `E` exists by
`MMP.Flips.IsFBirationalTransform`, and `a(ord_{F_i}, D_X)` is the discrepancy of its valuation.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.21.5, 2.24.2
-/

@[expose] public section

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

private theorem genericPoint_mem_preimage {A X : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (a : A ⟶ X) [IsDominant a] {U : X.Opens} (hU : genericPoint X ∈ U) :
    genericPoint A ∈ a ⁻¹ᵁ U := by
  change a (genericPoint A) ∈ U
  rw [map_genericPoint_of_isDominant]
  exact hU

/-- If `p' = g ∘ a` on `a⁻¹(dom g)` for a dominant `a : A ⟶ X`, then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` along `g` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense g.dense_domain
  have hA := genericPoint_mem_preimage a hx
  rw [partialMap_fromFunctionField_eq g hx]
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint A) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, c1, Category.assoc, ← hcomm, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

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

/-- The composite `p⁻¹(dom φ₀) ⟶ dom φ₀ ⟶ Y` is, at the generic point, `Spec k(W) ⟶ Spec k(X)`
followed by `φ₀`. -/
private theorem fromFunctionField_resLE_comp {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    (p : W ⟶ X) [IsDominant p] (φ₀ : X.PartialMap Y)
    (hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W)) :
    (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
      (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ₀.fromFunctionField := by
  have hx : genericPoint X ∈ φ₀.domain := genericPoint_mem_of_dense φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := genericPoint_mem_of_dense hd
  rw [partialMap_fromFunctionField_eq _ hW, partialMap_fromFunctionField_eq _ hx]
  change (p ⁻¹ᵁ φ₀.domain).fromSpecStalkOfMem (genericPoint W) hW ≫
    p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono φ₀.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk p).symm

/-- Conversely, if `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`, then some
representative `φ₀` of `φ` has `q = φ₀ ∘ p` as rational maps, on the dense open `p⁻¹(dom φ₀)`. -/
private theorem comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  have hW := genericPoint_mem_preimage p (genericPoint_mem_of_dense φ₀.dense_domain)
  refine ⟨φ₀, rfl, (p ⁻¹ᵁ φ₀.domain).isOpen.dense ⟨_, hW⟩,
    Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    RationalMap.fromFunctionField_hom]

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

/-- **Discrepancies of a realized divisor do not decrease on a weak log canonical model.** If a
divisor `E` over `X` realizes the prime divisor `F` of `Y` through `φ`, then
`a(E, D_X) ≤ a(ord_F, D_{𝓕,Y})`. -/
private theorem isDiscrepancy_le_of_isRealizedOver {k : Type u} [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E)
    {a b : ℝ} (hb : IsDiscrepancy sY n K_Y G F.divisorialValuation b)
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a) : a ≤ b := by
  obtain ⟨hfP, hgP, hmod, ⟨hXn, hYn, -⟩, -⟩ := id hM
  obtain ⟨W, p, q, hWv, hWs, hpP, hqP, hpb, hqb, ⟨ψ, ⟨e, he1, he2⟩, hψq⟩, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model sX sY sZ hXn hYn hZ f g hfs hgs φ hmod
  haveI : IsIntegral W := hWv.toIsIntegral
  obtain ⟨_, _⟩ := MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWn : Mori.IsNormalVariety k (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hqs : q ≫ sY = p ≫ sX := by rw [← hgs, ← hfs, ← Category.assoc, ← hcomm, Category.assoc]
  have KF : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
    rw [← hψq, ← he2, RationalMap.fromFunctionField_compHom, ← Category.assoc,
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
      comp_eq := comp_eq_of_specMap_fromFunctionField_eq φ p q KF }
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
  exact (hM.isDiscrepancy_le hW ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    Mori.functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩,
    E, rfl⟩ FW.divisorialValuation hv hFW).2 b a hb ha

/-- **The coefficients of a weak log canonical model are forced.** Let
`g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of `f : (X, D_X) ⟶ Z` with respect to
`𝓕 = c` (`MMP.Flips.IsWeakLogCanonicalModelOf`, with `G = D_{𝓕,Y}`), through `φ : X ⤏ Y`, where
`Z` is a variety over a field `k` of characteristic zero and `f`, `g` are morphisms over `k`.
Let `F` be a `φ⁻¹`-exceptional prime divisor of `Y`, `E` a divisor over `X` realizing `F` through
`φ`, and `a = a(ord_F, D_X)` the discrepancy of its valuation.
Then `c F = min 1 (-a)`. -/
@[mmp "lem_fa2_weak_lc_model_coefficients_forced"]
public theorem IsWeakLogCanonicalModelOf.eq_min_of_isInverseExceptional {k : Type u} [Field k]
    [CharZero k] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    {sZ : Z ⟶ Spec (.of k)} (hZ : Mori.IsVariety k sZ) (hfs : f ≫ sZ = sX) (hgs : g ≫ sZ = sY)
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) {a : ℝ}
    (ha : IsDiscrepancy sX n K_X D_X E.valuation a) :
    c F = min 1 (-a) := by
  obtain ⟨-, -, -, hFB, hKG, hRel, -⟩ := id hM
  obtain ⟨-, -, -, -, -, -, _, hFs, -, hc, -⟩ := id hFB
  obtain ⟨hc1, hcmin⟩ := hc F ((hFs F).2 hF)
  have hle := isDiscrepancy_le_of_isRealizedOver hZ hfs hgs hM hE
    (IsFBirationalTransform.isDiscrepancy_divisorialValuation hFB hRel.2.1.2.1 hKG hF) ha
  exact le_antisymm (le_min hc1 (by linarith)) (hcmin E a hE ha)

end MMP.Flips
