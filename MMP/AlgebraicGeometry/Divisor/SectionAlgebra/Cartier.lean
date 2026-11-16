module

public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.CodimOne
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts

/-!
# The birational transform of the divisor on the relative `Proj` of a divisorial algebra

Let `Y` be an integral, quasi-compact, locally Noetherian, normal scheme, `D` a Weil divisor on
`Y` and `g : Z = Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y`, where the divisorial algebra is generated in degree
one and `Z` is normal. Then the birational transform `g⁻¹_* D` is a Cartier divisor: on the chart
`D₊(a)` over an affine open `W`, for `a ∈ 𝒪_Y(D)(W)` of degree one, the pull-back of `a⁻¹` is a
local equation of `g⁻¹_* D`.

Indeed, the generic point `η_P` of a prime divisor `P` of `Z` meeting `D₊(a)` is a height-one
prime of the chart ring `S_{(a)}`, which is the centre of the valuation ring of a prime divisor
`E` of `Y` along which `v_E(a) = -D_E`. Then `g(η_P)` and `η_E` lie in the same basic opens of `W`,
so `g(η_P) = η_E`, and `g` is an isomorphism around `η_E`. Hence `P = g⁻¹_* E` is the only prime
divisor of `Z` over `E`, the coefficient of `P` in `g⁻¹_* D` is `D_E = v_E(a⁻¹)`, and the order of
the pull-back of `a⁻¹` along `P` is `v_E(a⁻¹)`.

## Main results

* `MMP.eq_of_forall_mem_basicOpen_iff`: two points of an affine open lying in the same basic
  opens are equal.
* `MMP.isIso_stalkMap_of_mem_biregularLocus`: a morphism induces isomorphisms of stalks over its
  biregular locus.
* `MMP.Fourfold.DivisorialSectionAlgebra.exists_primeDivisor_map_genericPoint_eq`: the image of
  the generic point of a prime divisor of the relative `Proj` meeting the chart `D₊(a)`.
* `MMP.Fourfold.DivisorialSectionAlgebra.isLocalEquation_inverseTransformDivisor`: the pull-back
  of `a⁻¹` is a local equation of `g⁻¹_* D` on `D₊(a)`.
* `MMP.Fourfold.DivisorialSectionAlgebra.isCartier_inverseTransformDivisor`: `g⁻¹_* D` is
  Cartier.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], Lemma 6.2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite HomogeneousLocalization

universe u

namespace MMP

/-- Two points of an affine open `W` lying in the same basic opens `D(r)`, `r ∈ Γ(X, W)`, are
equal. -/
theorem eq_of_forall_mem_basicOpen_iff {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    {x y : X} (hx : x ∈ W) (hy : y ∈ W)
    (h : ∀ r : Γ(X, W), x ∈ X.basicOpen r ↔ y ∈ X.basicOpen r) : x = y := by
  have key : ∀ {x y : X}, x ∈ W → y ∈ W →
      (∀ r : Γ(X, W), y ∈ X.basicOpen r → x ∈ X.basicOpen r) → x ⤳ y := by
    intro x y _ hy h
    rw [specializes_iff_forall_open]
    intro U hU hyU
    obtain ⟨r, hr, hyr⟩ := hW.exists_basicOpen_le (⟨y, hyU⟩ : (⟨U, hU⟩ : X.Opens)) hy
    exact hr (h r hyr)
  exact ((key hx hy fun r => (h r).mpr).antisymm (key hy hx fun r => (h r).mp)).eq

/-- A morphism induces isomorphisms of stalks at the points lying over its biregular locus. -/
theorem isIso_stalkMap_of_mem_biregularLocus {X Y : Scheme.{u}} (g : X ⟶ Y) {x : X}
    (hx : g x ∈ MMP.Mori.biregularLocus g) : IsIso (g.stalkMap x) := by
  have : IsIso (g ∣_ MMP.Mori.biregularLocus g) := MMP.Mori.isBiregular_biregularLocus g
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap g (MMP.Mori.biregularLocus g) ⟨x, hx⟩)).mp
    (((isIso_iff_isIso_stalkMap _).mp this).2 ⟨x, hx⟩)

end MMP

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori MMP.Mori.Divisor Stacks.RelativeProj

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}
  (A : DivisorialSectionAlgebra (𝟙 Y) D)

set_option backward.isDefEq.respectTransparency false in
/-- **Prime divisors of the relative `Proj` over a chart.** Let `P` be a prime divisor of
`Proj_Y ⨁_n 𝒪_Y(nD)` whose generic point lies on the chart `D₊(a)` over an affine open `W`, `a`
a nonzero section of degree one. Then the structure morphism maps `η_P` to the generic point of a
prime divisor `E` of `Y` meeting `W` along which `v_E(a) = -D_E`, and into its biregular locus. -/
theorem exists_primeDivisor_map_genericPoint_eq [CompactSpace Y] {W : Y.Opens}
    (hW : IsAffineOpen W) (a : A.situation.sectionPieces W 1) (ha0 : a ≠ 0)
    (P : AlgebraicGeometry.PrimeDivisor A.model)
    (p : Spec (.of (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 a))))
    (hp : (Proj.awayι _ _ (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from
      ⟨a, rfl⟩) one_pos ≫ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)) p =
        P.genericPoint) :
    ∃ (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty),
      E.valuation (A.pieceToRationalFunctions W 1 a
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = WithZero.exp (-D.coeff E) ∧
      A.toBase P.genericPoint = E.genericPoint ∧
      A.toBase P.genericPoint ∈ biregularLocus A.toBase := by
  classical
  have hfa : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 := ⟨a, rfl⟩
  set c := Proj.awayι _ _ hfa one_pos ≫ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)
    with hc
  have hzW : A.toBase P.genericPoint ∈ W := by
    rw [← hp]
    change (c ≫ A.toBase) p ∈ W
    rw [hc, Category.assoc, A.awayι_relativeProjChart_toBase hW hfa]
    exact hW.range_fromSpec.subset ⟨_, rfl⟩
  have hη : genericPoint Y ∈ W :=
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨_, Set.mem_univ _, hzW⟩
  let Z0 : irreducibleComponents Y :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
  let i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} :=
    ⟨Z0, ((isGenericPoint_componentGenericPoint Y Z0).mem_open_set_iff W.isOpen).mpr
      ⟨_, Set.mem_univ _, hzW⟩⟩
  have hf0 : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ≠ 0 := fun h =>
    ha0 ((A.sectionRingToFunctionField_of_eq_zero_iff i 1 a).mp h)
  have : IsDomain (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 a)) :=
    Function.Injective.isDomain _ (A.awayToFunctionField_injective i hfa hf0)
  have hco : Order.coheight (c p) = 1 := hp ▸ P.coheight_genericPoint
  have hp0 : p.asIdeal ≠ ⊥ := by
    intro hp0
    obtain ⟨b, hb⟩ := not_isMax_iff.mp fun h =>
      zero_ne_one ((Order.coheight_eq_zero.mpr h).symm.trans hco)
    obtain ⟨p', rfl⟩ := hb.le.mem_open c.isOpenEmbedding.isOpen_range ⟨p, rfl⟩
    have hle : p'.asIdeal ≤ p.asIdeal := (PrimeSpectrum.le_iff_specializes p' p).mpr
      (c.isOpenEmbedding.isInducing.specializes_iff.mp hb.le)
    rw [hp0, le_bot_iff] at hle
    exact hb.ne (congrArg c (PrimeSpectrum.ext (hle.trans hp0.symm))).symm
  obtain ⟨E, hE, hgood, hmem⟩ := A.exists_primeDivisor_of_height_one i a hf0 p.asIdeal hp0
    fun p' hp' h0 hle => haveI := hp'; MMP.eq_asIdeal_of_coheight_le_one _ p hco.le p' h0 hle
  have hηW : E.genericPoint ∈ W := E.genericPoint_mem_of_nonempty hE
  have hbasic : ∀ r : Γ(Y, W), A.toBase P.genericPoint ∈ Y.basicOpen r ↔
      E.genericPoint ∈ Y.basicOpen r := by
    intro r
    have hbo := A.toBase_relativeProjChart_awayι_mem_basicOpen_iff hW hfa p r
    rw [show A.toBase (A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)
      (Proj.awayι _ _ hfa one_pos p)) = A.toBase P.genericPoint from congrArg A.toBase hp] at hbo
    rw [hbo, Y.mem_basicOpen r E.genericPoint hηW]
    have hval : A.awayToFunctionField i hf0 (fromZeroRingHom _ _
        (Situation.sectionRingZeroMap A.situation W r)) =
        (E.valuationSubringEquiv (Y.presheaf.germ W E.genericPoint hηW r) : _) := by
      change _ = (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.germ W _ hηW).hom r)
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
      exact A.awayToFunctionField_fromZeroRingHom i hf0 r hη
    have heq : ∀ hx, (⟨_, hx⟩ : E.valuationSubring) =
        E.valuationSubringEquiv (Y.presheaf.germ W E.genericPoint hηW r) :=
      fun _ => Subtype.ext hval
    rw [hmem]
    constructor
    · intro hn
      by_contra hu
      refine hn ⟨hval ▸ (E.valuationSubringEquiv _).2, ?_⟩
      rw [heq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun h => hu ((MulEquiv.isUnit_map E.valuationSubringEquiv.toMulEquiv).mp h)
    · rintro hu ⟨hx, hmax⟩
      rw [heq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
      exact hmax (hu.map E.valuationSubringEquiv)
  have hgη : A.toBase P.genericPoint = E.genericPoint :=
    MMP.eq_of_forall_mem_basicOpen_iff hW hzW hηW hbasic
  obtain ⟨r, hr, hηr⟩ := A.exists_basicOpen_le_biregularLocus i hW a hf0 E hE hgood
  exact ⟨E, hE, hgood, hgη, hgη ▸ hr hηr⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The local equation of `g⁻¹_* D` on a chart.** On the chart `D₊(a)` over an affine open `W`,
`a` a nonzero section of degree one of `𝒪_Y(D)` with `a = φ` in `K(Y)`, the pull-back of `φ⁻¹`
along `g : Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y` is a local equation of the birational transform `g⁻¹_* D`. -/
theorem isLocalEquation_inverseTransformDivisor [CompactSpace Y]
    [IsIntegral A.model] [IsLocallyNoetherian A.model] [IsNormal A.model] [IsDominant A.toBase]
    {W : Y.Opens} (hW : IsAffineOpen W) (a : A.situation.sectionPieces W 1) (ha0 : a ≠ 0)
    (φ : (RationalFunctions Y)ˣ)
    (hφ : ∀ (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty),
      A.pieceToRationalFunctions W 1 a ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
        (φ : RationalFunctions Y) E.component) :
    Divisor.IsLocalEquation (X := A.model) (inverseTransformDivisor A.toBase D)
      (Proj.awayι _ _ (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from
        ⟨a, rfl⟩) one_pos ≫ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)).opensRange
      (pullbackRationalFunction A.toBase φ⁻¹ fun Z =>
        MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z) := by
  classical
  intro P hP
  obtain ⟨p, hp⟩ := (P.genericPoint_mem_iff _).mpr hP
  obtain ⟨E, hE, hgood, hgη, hV⟩ := A.exists_primeDivisor_map_genericPoint_eq hW a ha0 P p hp
  have hsome : inverseTransformPrimeDivisor A.toBase E = some P :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hgη hV
  have hcoeff : (inverseTransformDivisor A.toBase D).coeff P = D.coeff E :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hsome (fun E' hE' =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hE').1).symm.trans hgη)) D
  have hordE : E.ord φ = -D.coeff E := by
    rw [hφ E hE, E.valuation_component] at hgood
    exact WithZero.exp_injective hgood
  have : IsIso (A.toBase.stalkMap P.genericPoint) :=
    MMP.isIso_stalkMap_of_mem_biregularLocus _ hV
  have hB := fun Z => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant A.toBase
    (principalDivisor φ⁻¹) Z
  have hW' : A.toBase (componentGenericPoint A.model P.component) ∈ E.component.1 := by
    have h := E.component.2
    simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
    rw [h]
    trivial
  obtain ⟨b, hb⟩ := (isLocalEquation_principalDivisor φ⁻¹ ⊤).exists_unit_stalk
    (show A.toBase (componentGenericPoint A.model P.component) ∈ (⊤ : Y.Opens) from trivial)
    (hB P.component) hW'
  rw [hcoeff, PrimeDivisor.ord_eq_ordUnit]
  change _ = P.ordUnit (pullbackComponent A.toBase hB (isLocalEquation_principalDivisor φ⁻¹ ⊤)
    P.component trivial)
  rw [pullbackComponent_eq hB (isLocalEquation_principalDivisor φ⁻¹ ⊤)
      (show A.toBase (componentGenericPoint A.model P.component) ∈ (⊤ : Y.Opens) from trivial)
      hW' b hb,
    MMP.Positivity.ordUnit_stalkMap_eq_ord P E hgη φ⁻¹ hW' b hb, PrimeDivisor.ord_inv, hordE,
    neg_neg]

set_option backward.isDefEq.respectTransparency false in
/-- **`g⁻¹_* D` is Cartier.** If the divisorial algebra `⨁_n 𝒪_Y(nD)` is generated in degree one
and its relative `Proj` is normal, the birational transform of `D` under
`g : Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y` is a Cartier divisor: on each chart `D₊(a)` it has the pull-back
of `a⁻¹` as a local equation. -/
theorem isCartier_inverseTransformDivisor [CompactSpace Y]
    [IsIntegral A.model] [IsLocallyNoetherian A.model] [IsNormal A.model] [IsDominant A.toBase]
    (hgen : ∀ W : Y.Opens, A.situation.IsLocallyDegreeOneGenerated W) :
    Divisor.IsCartier (X := A.model) (inverseTransformDivisor A.toBase D) := by
  intro z
  obtain ⟨W, hW, hzW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show A.toBase z ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨a, p, ha0, hp⟩ := A.exists_relativeProjChart_awayι_eq hW (hgen W) z hzW
  let Z0 : irreducibleComponents Y :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
  let i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} :=
    ⟨Z0, ((isGenericPoint_componentGenericPoint Y Z0).mem_open_set_iff W.isOpen).mpr
      ⟨_, Set.mem_univ _, hzW⟩⟩
  have hf0 : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ≠ 0 := fun h =>
    ha0 ((A.sectionRingToFunctionField_of_eq_zero_iff i 1 a).mp h)
  obtain ⟨φ, hφ⟩ := PrimeDivisor.exists_units_algebraMap_eq hf0
  have hcomp : ∀ (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty),
      A.pieceToRationalFunctions W 1 a ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
        (φ : RationalFunctions Y) E.component := by
    intro E hE
    apply IsFractionRing.injective _ Y.functionField
    rw [hφ, sectionRingToFunctionField_of]
    exact algebraMap_rationalFunctionsPresheaf_apply_eq (W := W) _ _ i
  exact ⟨(Proj.awayι _ _ (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from
      ⟨a, rfl⟩) one_pos ≫ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)).opensRange,
    ⟨p, hp⟩, _, A.isLocalEquation_inverseTransformDivisor hW a ha0 φ hcomp⟩

end MMP.Fourfold.DivisorialSectionAlgebra
