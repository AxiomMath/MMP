module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Nef log birational models of pairs with real boundary

For a pair `(X/Z, B)` with real boundary, a *nef log birational model* is a normal projective
`ℚ`-factorial dlt pair `(Y/Z, B_Y)` with a birational map `X ⤏ Y` over `Z`, where `B_Y` is the
strict transform of `B` plus every prime divisor of `Y` exceptional over `X` with coefficient one,
such that `K_Y + B_Y` is nef over `Z` (for a canonical divisor `K_Y` cut out by the same rational
top form as `K_X`) and, on a common resolution `p : W ⟶ X`, `q : W ⟶ Y`, the
comparison `p^*(K_X + B) - q^*(K_Y + B_Y)` is effective and `q`-exceptional. It is a *log minimal
model* if moreover the comparison has positive coefficient along (the strict transform on `W` of)
every prime divisor of `X` contracted on `Y`. Every prime divisor of `Y` extracted by such a model
has log discrepancy zero with respect to `(X, B)`.

## Main definitions

* `MMP.Fourfold.IsRealLcPair`, `MMP.Fourfold.IsRealDltPair`: lc and dlt pairs with real boundary.
* `MMP.Fourfold.IsLogComparisonResolution`: a common resolution on which the comparison of the
  pulled-back adjoints is effective and exceptional.
* `MMP.Fourfold.IsNefLogBirationalModel`, `MMP.Fourfold.IsRealLogMinimalModel`: nef log
  birational models and log minimal models of a pair with real boundary.

## Main results

* `MMP.Fourfold.IsNefLogBirationalModel.isLogDiscrepancy_eq_zero`,
  `MMP.Fourfold.IsRealLogMinimalModel.isLogDiscrepancy_eq_zero`: every prime divisor extracted by
  a nef log birational model (in particular by a log minimal model) has log discrepancy zero with
  respect to `(X, B)`.

## Implementation notes

* Divisors of `Y` exceptional over `X` are the `φ⁻¹`-exceptional prime divisors
  (`MMP.Flips.RationalMap.IsInverseExceptional`): those that are not the birational transform of a
  prime divisor of `X`. A prime divisor of `X` is *contracted by `φ`* when it is `φ`-exceptional
  (`MMP.Mori.RationalMap.IsExceptional`).
* The boundary is described coefficientwise: `coeff_F B_Y = coeff_F (φ_* B) + 1` when `F` is
  exceptional over `X`, and `coeff_F B_Y = coeff_F (φ_* B)` otherwise.
* In a nef log birational model the canonical divisors `K_X` of `X` and `K_Y` of `Y` are chosen
  compatibly, cut out by one rational top form: on the common resolution `W` there is a
  canonical divisor `K_W` with `p_* K_W = K_X` and `q_* K_W = K_Y` (birational transforms along
  `p` and `q`). Then `K_X = div_X(η)`, `K_Y = div_Y(η)` and `K_W = div_W(η)` for one rational top
  form `η`, and the comparison divisor on `W` does not depend on the compatible choice: changing
  `η` to `f η` changes it by `ord(f)` along `W`-primes, all of which have centre on `X`, so that
  `ord(f) = 0` for the only admissible `f` (units of `X`, as `K_X` is fixed). The same `K_Y` is
  used in the nefness condition and in the comparison.
* A common resolution is a smooth variety `W` with projective birational morphisms
  `p : W ⟶ X`, `q : W ⟶ Y` such that `q ∘ p⁻¹ = φ`. The coefficient of the comparison at a prime
  divisor `P` of `X` is its coefficient at the strict transform `p⁻¹_* P` of `P` on `W`.
* Lc and dlt pairs with real boundary follow `MMP.Intersection.IsLogCanonicalPair` and
  `MMP.Intersection.IsDltPair`, with `K_X + B` required to be `ℝ`-Cartier. A log discrepancy is
  a predicate on its value, and the inequalities are required of all values.
* All notions are stated over an arbitrary field `k`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Lc and dlt pairs with real boundary -/

section RealPair

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A pair `(X, B)` with real boundary is *log canonical*: `X` is a normal variety, `B` is an
effective `ℝ`-divisor, `K_X + B` is `ℝ`-Cartier for a canonical divisor `K_X`, and
`a(E, X, B) ≥ 0` for every divisor `E` over `X`. -/
def IsRealLcPair (B : RDivisor X) : Prop :=
  IsNormalVariety k sX ∧ (∀ P, 0 ≤ B.coeff P) ∧
    (∃ (n : ℕ) (K : Divisor X), K.IsCanonicalDivisor sX n ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B)) ∧
    ∀ (n : ℕ) (E : DivisorOver k sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n B E a → 0 ≤ a

/-- A pair `(X, B)` with real boundary is *dlt*: it is log canonical, the coefficients of `B` are
at most one, and there is a closed subset `Z ⊆ X` such that `X ∖ Z` is smooth, `B|_{X ∖ Z}` has
simple normal crossing support, and `a(E, X, B) > 0` for every divisor `E` over `X` whose centre
on `X` lies in `Z`. -/
def IsRealDltPair (B : RDivisor X) : Prop :=
  IsRealLcPair sX B ∧ (∀ P, B.coeff P ≤ 1) ∧
    ∃ Z : Closeds X,
      MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX) ∧
      DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX)
        (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : X.Opens)) B) ∧
      ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B D a → 0 < a

end RealPair

/-! ### Helpers -/

section Helpers

private theorem topologicalKrullDim_closure_genericPoint_add_one {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (P : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim (closure {P.genericPoint} : Set Y) + 1 = topologicalKrullDim Y := by
  let _ : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  exact_mod_cast h

/-- A prime divisor of `W` whose generic point maps under a proper `q : W ⟶ Y` to the generic
point of a prime divisor of `Y` is not `q`-exceptional. -/
private theorem not_isExceptionalPrimeDivisor_of_genericPoint_eq {k : Type u} [Field k]
    {W Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (q : W ⟶ Y) [IsProper q] (FW : MMP.Mori.PrimeDivisor W) (F : MMP.Mori.PrimeDivisor Y)
    (h : q FW.genericPoint = F.genericPoint) {nY : ℕ} (hdim : topologicalKrullDim Y = nY) :
    ¬ MMP.Flips.IsExceptionalPrimeDivisor sY q FW := by
  rintro ⟨_, _, _, hexc⟩
  change topologicalKrullDim (q '' FW.support : Set Y) + 2 ≤ topologicalKrullDim Y at hexc
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure FW,
    ← q.isClosedMap.closure_image_eq_of_continuous q.continuous, Set.image_singleton, h] at hexc
  have h1 := topologicalKrullDim_closure_genericPoint_add_one sY F
  rw [hdim] at h1 hexc
  generalize topologicalKrullDim (closure {F.genericPoint} : Set Y) = d at h1 hexc
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) from rfl] at h1
      exact ENat.top_ne_natCast nY (WithBot.coe_injective h1)
    | coe d =>
      have h2' : ((d + 2 : ℕ) : WithBot ℕ∞) ≤ ((nY : ℕ) : WithBot ℕ∞) := le_of_eq_of_le rfl hexc
      have e1 : d + 1 = nY := by exact_mod_cast h1
      have e2 : d + 2 ≤ nY := by exact_mod_cast h2'
      omega

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- If a dominant morphism `a : A ⟶ X` of integral schemes is lifted, over the domain `U` of a
partial map `g : X ⇢ Y`, by `p' : A ⟶ Y` (`p' = g ∘ a` on `a⁻¹ U`), then
`Spec k(A) ⟶ Spec k(X) ⟶ Y` is `Spec k(A) ⟶ A ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral A] (a : A ⟶ X) [IsDominant a] (g : X.PartialMap Y) (p' : A ⟶ Y)
    (hcomm : (a ⁻¹ᵁ g.domain).ι ≫ p' = (a ∣_ g.domain) ≫ g.hom) :
    Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ g.fromFunctionField =
      A.fromSpecStalk (genericPoint A) ≫ p' := by
  have hx : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  have hA : genericPoint A ∈ a ⁻¹ᵁ g.domain := by
    change a (genericPoint A) ∈ g.domain
    rwa [map_genericPoint_of_isDominant]
  rw [partialMap_fromFunctionField_eq g hx]
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint A) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, c1, Category.assoc, ← hcomm, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
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
    (FW : MMP.Mori.PrimeDivisor W) (E : MMP.Mori.PrimeDivisor A) (F : MMP.Mori.PrimeDivisor Y)
    (hFW : FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation)
    (hE : E.divisorialValuation.comap (functionFieldMap pA) = F.divisorialValuation) :
    FW.valuationOver p = E.valuationOver a := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ : ∀ s, functionFieldMap p (θ s) = functionFieldMap q s := fun s =>
    ep.apply_symm_apply _
  have hθs : Function.Surjective θ := ep.symm.surjective.comp hq
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  have hm : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hW, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (functionFieldMap p).comp θ = functionFieldMap q from RingHom.ext hθ]
    exact functionFieldMap_fromSpecStalk q
  have hθA : (functionFieldMap a).comp θ = functionFieldMap pA := by
    rw [← hm, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← functionFieldMap_fromSpecStalk pA] at hA
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp hA))
  refine Valuation.ext fun t => ?_
  obtain ⟨s, rfl⟩ := hθs t
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply, MMP.Mori.PrimeDivisor.valuationOver_apply, hθ,
    ← RingHom.comp_apply (functionFieldMap a) θ, hθA, ← Valuation.comap_apply,
    hFW, ← hE, Valuation.comap_apply]

end Helpers

/-! ### Nef log birational models of pairs with real boundary -/

section NefLogBirationalModel

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
  [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- A *common resolution comparing adjoints* for a birational map `φ : X ⤏ Y`, divisors `K_X` on
`X`, `K_Y` on `Y` and `ℝ`-divisors `B_X` on `X`, `B_Y` on `Y`: a smooth variety `W` with
projective birational morphisms `p : W ⟶ X`, `q : W ⟶ Y` such that `q ∘ p⁻¹ = φ`
(`h : X ⤏ W` being the inverse of `p`),
a canonical divisor `K_W` of `W` with `p_* K_W = K_X` and `q_* K_W = K_Y` (so that the canonical
divisors `K_X` of `X` and `K_Y` of `Y` are cut out by one rational top form), and pull-backs
`G_X = p^*(K_X + B_X)` and `G_Y = q^*(K_Y + B_Y)` (as `ℝ`-Cartier divisors) such that
`G_X - G_Y` is effective and `q`-exceptional. -/
structure IsLogComparisonResolution {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] (sW : W ⟶ Spec (.of k)) (φ : X.RationalMap Y) (KX : Divisor X) (BX : RDivisor X)
    (KY : Divisor Y) (BY : RDivisor Y) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
    (GX GY : RDivisor W) : Prop where
  isVariety : MMP.Mori.IsVariety k sW
  isSmoothScheme : MMP.Mori.IsSmoothScheme sW
  comp_eq_left : p ≫ sX = sW
  comp_eq_right : q ≫ sY = sW
  isProjectiveMorphism_left : IsProjectiveMorphism p
  isProjectiveMorphism_right : IsProjectiveMorphism q
  isBirationalMorphism_left : IsBirationalMorphism p
  isBirationalMorphism_right : IsBirationalMorphism q
  isInverse : MMP.Mori.RationalMap.IsInverse p.toRationalMap h
  compHom_eq : h.compHom q = φ
  exists_canonicalDivisor : ∃ (n : ℕ) (KW : Divisor W), KW.IsCanonicalDivisor sW n ∧
    MMP.Mori.RationalMap.transformDivisor p.toRationalMap KW = KX ∧
    MMP.Mori.RationalMap.transformDivisor q.toRationalMap KW = KY
  /-- `G_X` is the pull-back `p^*(K_X + B_X)` as an `ℝ`-Cartier divisor. -/
  isRCartierPullback_left : MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor KX BX) GX
  /-- `G_Y` is the pull-back `q^*(K_Y + B_Y)` as an `ℝ`-Cartier divisor. -/
  isRCartierPullback_right :
    MMP.Flips.IsRCartierPullback q (MMP.Flips.logCanonicalDivisor KY BY) GY
  effective : ∀ P, 0 ≤ (GX - GY).coeff P
  isExceptional : ∀ P, (GX - GY).coeff P ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor sY q P

open Classical in
/-- **Nef log birational model.** Let `(X/Z, B)` be an lc pair with real boundary `B`, over `Z`
by `π`, with canonical divisor `K_X`. A *nef log birational model* of `(X/Z, B)` is a normal
projective `ℚ`-factorial dlt pair `(Y/Z, B_Y)` (over `Z` by `π_Y`) with a birational map
`φ : X ⤏ Y` over `Z` such that `B_Y` is the strict transform `φ_* B` plus every prime divisor of
`Y` exceptional over `X` with coefficient one, the adjoint `K_Y + B_Y` is nef over `Z`, and on a
common resolution `p : W ⟶ X`, `q : W ⟶ Y` the comparison `p^*(K_X + B) - q^*(K_Y + B_Y)` is
effective and `q`-exceptional. Here `K_Y` is a canonical divisor of `Y` compatible with `K_X`
(both cut out by one rational top form): `p_* K_W = K_X` and `q_* K_W = K_Y` for a canonical
divisor `K_W` of the resolution. -/
@[mmp "def_fourfold_lc_log_birational_model"]
structure IsNefLogBirationalModel (π : X ⟶ Z) (πY : Y ⟶ Z) (KX : Divisor X) (B : RDivisor X)
    (KY : Divisor Y) (BY : RDivisor Y) (φ : X.RationalMap Y) : Prop where
  isRealLcPair : IsRealLcPair sX B
  isCanonicalDivisor : ∃ n : ℕ, KX.IsCanonicalDivisor sX n
  comp_eq : π ≫ sZ = sX
  isNormalVariety_model : IsNormalVariety k sY
  isCanonicalDivisor_model : ∃ n : ℕ, KY.IsCanonicalDivisor sY n
  isProjectiveVariety_model : MMP.Mori.IsProjectiveVariety k sY
  comp_eq_model : πY ≫ sZ = sY
  isQFactorial : IsQFactorial sY
  isRealDltPair : IsRealDltPair sY BY
  isBirational : MMP.Mori.RationalMap.IsBirational φ
  isOver : MMP.Flips.RationalMap.IsOver π πY φ
  coeff_boundary : ∀ F : MMP.Mori.PrimeDivisor Y,
    BY.coeff F = (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
      if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0
  isRelativelyNef : MMP.Flips.IsRelativelyNef k sY πY
    (MMP.Flips.logCanonicalDivisor KY BY)
  exists_resolution : ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
      (GX GY : RDivisor W),
    IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY

/-- **Log minimal model of a pair with real boundary.** A nef log birational model
`(Y/Z, B_Y)` of `(X/Z, B)` is a *log minimal model* if, in addition, on a common resolution
`p : W ⟶ X`, `q : W ⟶ Y` as in the definition, the coefficient of the comparison
`p^*(K_X + B) - q^*(K_Y + B_Y)` at every prime divisor `P` of `X` contracted on `Y` (that is, at
the strict transform `p⁻¹_* P` of `P` on `W`) is strictly positive. -/
@[mmp "def_fourfold_lc_log_birational_model"]
structure IsRealLogMinimalModel (π : X ⟶ Z) (πY : Y ⟶ Z) (KX : Divisor X) (B : RDivisor X)
    (KY : Divisor Y) (BY : RDivisor Y) (φ : X.RationalMap Y) : Prop extends
    IsNefLogBirationalModel sX sY sZ π πY KX B KY BY φ where
  exists_resolution_pos : ∃ (W : Scheme.{u}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of k)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
      (GX GY : RDivisor W),
    IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY ∧
    ∀ P : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.IsExceptional φ P →
      ∀ P' : MMP.Mori.PrimeDivisor W, MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' →
        0 < (GX - GY).coeff P'

variable {sX sY sZ}

private theorem valuation_eq_of_isRealizedOver {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {φ : X.RationalMap Y}
    {KX : Divisor X} {B : RDivisor X} {KY : Divisor Y} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y}
    {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY)
    (hWnp : IsNormalVariety k (p ≫ sX)) {F : MMP.Mori.PrimeDivisor Y}
    {E : MMP.Flips.ProperDivisorOver k sX} (hE : MMP.Flips.IsRealizedOver sX φ F E)
    (FW : MMP.Mori.PrimeDivisor W) (hFWeq : q FW.genericPoint = F.genericPoint)
    [IsIso (q.stalkMap FW.genericPoint)] :
    E.toDivisorOver.valuation =
      (⟨W, p, hWnp, hR.isBirationalMorphism_left, FW⟩ : MMP.Mori.DivisorOver k sX).valuation := by
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  obtain ⟨g, pE, hpE, hg, hcomm, hval⟩ := hE
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := hpE.isDominant
  have hFW : FW.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation := by
    refine Valuation.ext fun t => ?_
    rw [Valuation.comap_apply]
    by_cases ht : t = 0
    · rw [ht, map_zero, map_zero, map_zero]
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
      MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
      MMP.Positivity.ord_functionFieldMap_of_isIso q FW F hFWeq t]
  have hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
    obtain ⟨e, he1, he2⟩ := hR.isInverse
    rw [← hR.compHom_eq, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom,
      ← Category.assoc, specMap_functionFieldMap_fromFunctionField_symm p e he1]
  have hA : Spec.map (CommRingCat.ofHom (functionFieldMap E.f)) ≫ φ.fromFunctionField =
      E.Y.fromSpecStalk (genericPoint E.Y) ≫ pE := by
    rw [← hg]
    exact specMap_functionFieldMap_fromFunctionField E.f g pE hcomm
  exact (valuationOver_eq_of_specMap_comp φ.fromFunctionField p q E.f pE
    hpb.functionFieldMap_bijective hqb.functionFieldMap_bijective.2 hW hA FW E.E F hFW
    hval).symm

/-- On a comparison resolution of a nef log birational model, at a prime divisor `FW` of the
resolution mapping onto a prime divisor `F` of the model, the two pull-backs agree. -/
private theorem coeff_left_eq_coeff_right {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X}
    {B : RDivisor X} {KY : Divisor Y} {BY : RDivisor Y} {φ : X.RationalMap Y}
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX B KY BY φ) {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {p : W ⟶ X} {q : W ⟶ Y}
    [IsProper q] {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY)
    (FW : MMP.Mori.PrimeDivisor W) (F : MMP.Mori.PrimeDivisor Y)
    (hFWeq : q FW.genericPoint = F.genericPoint) : GX.coeff FW = GY.coeff FW := by
  have := hY.isNormalVariety_model.1.toLocallyOfFiniteType
  obtain ⟨nY, hKY⟩ := hY.isCanonicalDivisor_model
  by_contra hne
  refine not_isExceptionalPrimeDivisor_of_genericPoint_eq sY q FW F hFWeq
    hKY.topologicalKrullDim_eq (hR.isExceptional FW ?_)
  rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.sub_apply]
  exact sub_ne_zero.mpr hne

/-- On a comparison resolution of a nef log birational model, at a prime divisor `FW` of the
resolution with `𝒪_{Y,F} ≅ 𝒪_{W,FW}` over a newly extracted prime divisor `F`, the coefficient
of `q^*(K_Y + B_Y)` is `K_Y` at `F` plus one. -/
private theorem coeff_right_eq_coeff_add_one {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X}
    {B : RDivisor X} {KY : Divisor Y} {BY : RDivisor Y} {φ : X.RationalMap Y}
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX B KY BY φ) {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of k)} {p : W ⟶ X} {q : W ⟶ Y}
    [IsDominant q] {h : X.RationalMap W} {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX B KY BY p q h GX GY)
    {F : MMP.Mori.PrimeDivisor Y} (hF : MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (FW : MMP.Mori.PrimeDivisor W) (hFWeq : q FW.genericPoint = F.genericPoint)
    [IsIso (q.stalkMap FW.genericPoint)] : GY.coeff FW = (KY.coeff F : ℝ) + 1 := by
  obtain ⟨m₂, s₂, M, M', hMc, hM, hMpb, hGY⟩ := hR.isRCartierPullback_right
  have hKYBY := congrArg (fun D : MMP.Mori.RDivisor Y => D F) hM
  simp only [MMP.Flips.logCanonicalDivisor, Finsupp.add_apply, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul] at hKYBY
  have hBY : BY.coeff F = 1 := by
    rw [hY.coeff_boundary F, if_pos hF,
      show (MMP.Mori.RationalMap.transformDivisor φ B).coeff F = 0 from
        MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne hF B, zero_add]
  have hcoeffGY : GY.coeff FW = ∑ j, s₂ j * (M j).coeff F := by
    rw [hGY, MMP.Flips.coeff_sum_smul_toRDivisor]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback FW F hFWeq (hMc j) (hMpb j).2
  rw [hcoeffGY, ← hBY]
  exact hKYBY.symm

/-- In a nef log birational model `(Y/Z, B_Y)` of `(X/Z, B)`, every newly extracted prime
divisor `F` of `Y` (exceptional over `X`) has log discrepancy `a(F; X, B) = 0`: every divisor
over `X` realizing `F` through `φ` has log discrepancy zero with respect to `(X, B)`. -/
@[mmp "def_fourfold_lc_log_birational_model"]
theorem IsNefLogBirationalModel.isLogDiscrepancy_eq_zero [PerfectField k] {π : X ⟶ Z} {πY : Y ⟶ Z}
    {KX : Divisor X} {B : RDivisor X} {KY : Divisor Y} {BY : RDivisor Y} {φ : X.RationalMap Y}
    (hY : IsNefLogBirationalModel sX sY sZ π πY KX B KY BY φ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : MMP.Flips.RationalMap.IsInverseExceptional φ F) (E : MMP.Flips.ProperDivisorOver k sX)
    (hE : MMP.Flips.IsRealizedOver sX φ F E) (n : ℕ) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver a) : a = 0 := by
  obtain ⟨W, _, _, _, sW, p, q, h, GX, GY, hR⟩ := hY.exists_resolution
  have hXn : IsNormalVariety k sX := hY.isRealLcPair.1
  have hWn : IsNormalVariety k sW := ⟨hR.isVariety, inferInstance⟩
  have hWnp : IsNormalVariety k (p ≫ sX) := hR.comp_eq_left ▸ hWn
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hR.isBirationalMorphism_right.isDominant
  have : LocallyOfFiniteType (p ≫ sX) := hWnp.1.toLocallyOfFiniteType
  have := hR.isVariety
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨FW, hFWeq, hFWiso, hFWtr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0}
      hY.isNormalVariety_model (hR.comp_eq_right ▸ hWn) hR.isBirationalMorphism_right F
  let DW : MMP.Mori.DivisorOver k sX := ⟨W, p, hWnp, hpb, FW⟩
  have hdimX := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  obtain ⟨n₀, hKX⟩ := hY.isCanonicalDivisor
  obtain ⟨nW, KW, hKW, hKWX, hKWY⟩ := hR.exists_canonicalDivisor
  have hdimW : topologicalKrullDim W = topologicalKrullDim X := by
    have := hXn.1
    have := hWnp.1
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm
  obtain rfl : n₀ = n := by exact_mod_cast hKX.topologicalKrullDim_eq.symm.trans hdimX
  obtain rfl : nW = n₀ := by
    exact_mod_cast hKW.topologicalKrullDim_eq.symm.trans (hdimW.trans hdimX)
  obtain ⟨ω, hω0, hωX, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn hWnp hpb hKX
      (hR.comp_eq_left ▸ hKW) hKWX
  obtain ⟨m, r, L, L', hLc, hL, hLpb, hGX⟩ := hR.isRCartierPullback_left
  have hcoeffGX : GX.coeff FW = ∑ i, r i * (L' i).coeff FW := by
    rw [hGX, MMP.Flips.coeff_sum_smul_toRDivisor]
  have hKY : KY.coeff F = KW.coeff FW := hKWY ▸ hFWtr KW
  have hDW : MMP.Intersection.IsLogDiscrepancy sX nW B DW 0 := by
    refine ⟨hXn, inferInstanceAs (IsProper p), ω, hω0, ⟨KX, hKX, fun Γ => ?_⟩, m, r, L, L', hLc,
      fun Γ => ?_, hLpb, ?_⟩
    · rw [← hωX]
      rfl
    · have := congrArg (fun D : MMP.Mori.RDivisor X => D Γ) hL
      simp only [MMP.Flips.logCanonicalDivisor, Finsupp.add_apply, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul] at this
      rwa [← hωX] at this
    · have hord : DW.ordPullback ω = KW.coeff FW := by
        rw [← hωW]
        rfl
      rw [hord, ← hcoeffGX, coeff_left_eq_coeff_right hY hR FW F hFWeq,
        coeff_right_eq_coeff_add_one hY hR hF FW hFWeq, hKY]
      ring
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha hDW
    (valuation_eq_of_isRealizedOver hR hWnp hE FW hFWeq)

/-- In a log minimal model `(Y/Z, B_Y)` of `(X/Z, B)` with real boundary, every newly extracted
prime divisor `F` of `Y` (exceptional over `X`) has log discrepancy `a(F; X, B) = 0`. -/
@[mmp "def_fourfold_lc_log_birational_model"]
theorem IsRealLogMinimalModel.isLogDiscrepancy_eq_zero [PerfectField k] {π : X ⟶ Z} {πY : Y ⟶ Z}
    {KX : Divisor X} {B : RDivisor X} {KY : Divisor Y} {BY : RDivisor Y} {φ : X.RationalMap Y}
    (hY : IsRealLogMinimalModel sX sY sZ π πY KX B KY BY φ) (F : MMP.Mori.PrimeDivisor Y)
    (hF : MMP.Flips.RationalMap.IsInverseExceptional φ F) (E : MMP.Flips.ProperDivisorOver k sX)
    (hE : MMP.Flips.IsRealizedOver sX φ F E) (n : ℕ) (a : ℝ)
    (ha : MMP.Intersection.IsLogDiscrepancy sX n B E.toDivisorOver a) : a = 0 :=
  hY.toIsNefLogBirationalModel.isLogDiscrepancy_eq_zero F hF E hE n a ha

end NefLogBirationalModel

end MMP.Fourfold
