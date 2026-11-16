module

public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Chart
public import MMP.AlgebraicGeometry.Divisor.Arithmetic

/-!
# The relative `Proj` of a divisorial algebra is an isomorphism in codimension one

Let `Y` be an integral, quasi-compact, locally Noetherian, normal scheme, `D` a Weil divisor on
`Y` and `g : Z = Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y`, where the divisorial algebra is generated in degree
one. Then every point of `Z` of codimension at most one maps into the open of `Y` over which `g` is
an isomorphism. A point `z` lies in a chart `D₊(a) = Spec S_{(a)}` over an affine open `W`, with
`a ∈ 𝒪_Y(D)(W)` of degree one. If `z` is the generic point of the chart, `g z` is the generic point
of `Y`. Otherwise `z` is a height-one prime of `S_{(a)}`, hence the centre of the valuation ring of
a prime divisor `E` of `Y` meeting `W` along which `v_E(a) = -D_E`; then `g z` and the generic
point of `E` lie in the same basic opens of `W`, and off the finitely many prime divisors along
which `a` vanishes, `a⁻¹` is a local equation of `D`, so `g` is an isomorphism there.

## Main results

* `MMP.eq_asIdeal_of_coheight_le_one`: a point of coheight at most one in the image of a
  preimmersion `Spec R ⟶ X` is a prime with no nonzero prime strictly below it.
* `MMP.Fourfold.DivisorialSectionAlgebra.range_relativeProjChart`: the chart over an affine `W`
  is the preimage of `W`.
* `MMP.Fourfold.DivisorialSectionAlgebra.toBase_relativeProjChart_awayι_mem_basicOpen_iff`: the
  image of a point `p` of `D₊(f)` lies in `D(r)` exactly when `r / 1 ∉ p`.
* `MMP.Fourfold.DivisorialSectionAlgebra.exists_basicOpen_le_biregularLocus`: `g` is an
  isomorphism around the generic point of every prime divisor along which `a` has order `-D_E`.
* `MMP.Fourfold.DivisorialSectionAlgebra.toBase_mem_biregularLocus_of_coheight_le_one`,
  `MMP.Fourfold.DivisorialSectionAlgebra.toBase_mem_biregularLocus_of_codimension_le_one`: every
  point of `Z` of codimension at most one maps into the biregular locus of `g`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], Lemma 6.2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite HomogeneousLocalization

universe u

namespace MMP

/-- **Height one in an affine open.** If a preimmersion `h : Spec R ⟶ X` from a domain maps `p`
to a point of coheight at most one, then no nonzero prime lies strictly below `p`. -/
theorem eq_asIdeal_of_coheight_le_one {R : CommRingCat.{u}} [IsDomain R] {X : Scheme.{u}}
    (h : Spec R ⟶ X) [IsPreimmersion h] (p : Spec R) (hp : Order.coheight (h p) ≤ 1)
    (p' : Ideal R) [p'.IsPrime] (hp' : p' ≠ ⊥) (hle : p' ≤ p.asIdeal) : p' = p.asIdeal := by
  by_contra hne
  let P' : Spec R := ⟨p', inferInstance⟩
  let P0 : Spec R := ⟨⊥, Ideal.isPrime_bot⟩
  have hspec : ∀ a b : Spec R, (h a ⤳ h b) ↔ a.asIdeal ≤ b.asIdeal := fun a b =>
    h.isEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes a b).symm
  have hlt1 : h p < h P' := lt_iff_le_not_ge.mpr
    ⟨(hspec P' p).mpr hle, fun h' => hne (le_antisymm hle ((hspec p P').mp h'))⟩
  have hlt2 : h P' < h P0 := lt_iff_le_not_ge.mpr
    ⟨(hspec P0 P').mpr bot_le, fun h' => hp' (le_bot_iff.mp ((hspec P' P0).mp h'))⟩
  have h1 := Order.coheight_add_one_le hlt1
  have h3 : (1 : ℕ∞) ≤ Order.coheight (h P') := le_add_self.trans (Order.coheight_add_one_le hlt2)
  have h4 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (le_trans (by gcongr) h1) hp
  exact absurd h4 (by decide)

end MMP

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori MMP.Mori.Divisor Stacks.RelativeProj

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}
  (A : DivisorialSectionAlgebra (𝟙 Y) D)

set_option backward.isDefEq.respectTransparency false in
/-- The chart over an affine open `W` covers exactly the points of the relative `Proj` lying
over `W`. -/
theorem range_relativeProjChart (W : Y.affineOpens) :
    Set.range (A.situation.relativeProjChart W) = A.toBase ⁻¹' (W.1 : Set Y) := by
  have hpb := A.situation.relativeProjChart_isPullback W
  have hw : A.situation.relativeProjChart W ≫ A.toBase =
      A.situation.projInclusionToOpen W.1 W.2 ≫ W.1.ι := hpb.w
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    change (A.situation.relativeProjChart W ≫ A.toBase) x ∈ W.1
    rw [hw]
    exact (A.situation.projInclusionToOpen W.1 W.2 x).2
  · intro hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A.situation.relativeProjToBase) (g := W.1.ι) x ⟨A.toBase x, hx⟩ rfl
    refine ⟨hpb.isoPullback.inv z, ?_⟩
    change (hpb.isoPullback.inv ≫ A.situation.relativeProjChart W) z = x
    rw [hpb.isoPullback_inv_fst]
    exact hz

set_option backward.isDefEq.respectTransparency false in
/-- The chart `D₊(f) = Spec S_{(f)}` of the relative `Proj` over an affine open `W`, followed by
the structure morphism, is `Spec S_{(f)} ⟶ Spec Γ(W) ⟶ Y`, induced by `r ↦ r / 1`. -/
theorem awayι_relativeProjChart_toBase {W : Y.Opens} (hW : IsAffineOpen W)
    {f : A.situation.sectionRing W} (hf : f ∈ A.situation.sectionRingGrading W 1) :
    Proj.awayι _ f hf one_pos ≫ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens) ≫ A.toBase =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom _ _)) ≫
        Spec.map (Situation.sectionRingZeroMap A.situation W) ≫ hW.fromSpec := by
  have hw : A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens) ≫ A.toBase =
      A.situation.projInclusionToOpen W hW ≫ W.ι :=
    (A.situation.relativeProjChart_isPullback ⟨W, hW⟩).w
  rw [hw, Situation.projInclusionToOpen, Category.assoc, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, Proj.awayι_toSpecZero_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A point `p` of the chart `D₊(f)` over an affine open `W` maps into the basic open `D(r)` of
`r ∈ Γ(Y, W)` exactly when `r / 1 ∉ p`. -/
theorem toBase_relativeProjChart_awayι_mem_basicOpen_iff {W : Y.Opens} (hW : IsAffineOpen W)
    {f : A.situation.sectionRing W} (hf : f ∈ A.situation.sectionRingGrading W 1)
    (p : Spec (.of (Away (A.situation.sectionRingGrading W) f))) (r : Γ(Y, W)) :
    A.toBase (A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)
        (Proj.awayι _ f hf one_pos p)) ∈ Y.basicOpen r ↔
      fromZeroRingHom _ _ (Situation.sectionRingZeroMap A.situation W r) ∉ p.asIdeal := by
  have h := congrArg (fun φ => φ p) (A.awayι_relativeProjChart_toBase hW hf)
  simp only [Scheme.Hom.comp_apply] at h
  refine (Eq.to_iff (congrArg (· ∈ Y.basicOpen r) h)).trans ?_
  change _ ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen r ↔ _
  rw [hW.fromSpec_preimage_basicOpen, PrimeSpectrum.mem_basicOpen]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- If the divisorial algebra is generated in degree one over the affine open `W`, every point of
the relative `Proj` over `W` lies in a chart `D₊(a)` for a nonzero section `a` of degree one. -/
theorem exists_relativeProjChart_awayι_eq {W : Y.Opens} (hW : IsAffineOpen W)
    (hgen : A.situation.IsLocallyDegreeOneGenerated W) (z : A.model) (hz : A.toBase z ∈ W) :
    ∃ (a : A.situation.sectionPieces W 1)
      (p : Spec (.of (Away (A.situation.sectionRingGrading W) (DirectSum.of _ 1 a)))),
      a ≠ 0 ∧ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)
        (Proj.awayι _ _ (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from
          ⟨a, rfl⟩) one_pos p) = z := by
  obtain ⟨x, rfl⟩ : z ∈ Set.range (A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)) := by
    rwa [range_relativeProjChart]
  have hcov := Proj.iSup_basicOpen_eq_top' (A.situation.sectionRingGrading W)
    (Subtype.val : A.situation.sectionRingGrading W 1 → A.situation.sectionRing W)
    (fun s => ⟨1, s.2⟩)
    (by rw [Subtype.range_val]; exact A.situation.adjoin_sectionRingGrading_one_eq_top W hW hgen)
  have hx : x ∈ (⨆ s : A.situation.sectionRingGrading W 1,
      Proj.basicOpen _ (s : A.situation.sectionRing W)) := by
    rw [hcov]
    trivial
  obtain ⟨s, hxa⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨a, ha⟩ := s.2
  rw [← ha] at hxa
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Proj.mem_basicOpen, map_zero] at hxa
    exact hxa (zero_mem _)
  rw [← Proj.opensRange_awayι _ _ (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1
    from ⟨a, rfl⟩) one_pos] at hxa
  obtain ⟨p, rfl⟩ := hxa
  exact ⟨a, p, ha0, rfl⟩

variable [IsIntegral Y] {W : Y.Opens} (i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W})

set_option backward.isDefEq.respectTransparency false in
/-- A section `r` of `𝒪_Y` over `W`, viewed in the chart ring `S_{(f)}` as `r / 1`, goes to its
germ at the generic point in `K(Y)`. -/
theorem awayToFunctionField_fromZeroRingHom {f : A.situation.sectionRing W}
    (hf0 : A.sectionRingToFunctionField i f ≠ 0) (r : Γ(Y, W)) (hη : genericPoint Y ∈ W) :
    A.awayToFunctionField i hf0
        (fromZeroRingHom _ _ (Situation.sectionRingZeroMap A.situation W r)) =
      Y.presheaf.germ W (genericPoint Y) hη r := by
  have h0 : ((Situation.sectionRingZeroMap A.situation W r : A.situation.sectionRingGrading W 0) :
      A.situation.sectionRing W) = A.situation.sectionRingBaseMap W r := by
    change (DirectSum.decompose (A.situation.sectionRingGrading W)
      (A.situation.sectionRingBaseMap W r) 0 : A.situation.sectionRing W) = _
    rw [DirectSum.decompose_of_mem_same _ (Situation.sectionRingBaseMap_mem_zero A.situation W r)]
  have h1 : A.awayToFunctionField i hf0
      (fromZeroRingHom _ _ (Situation.sectionRingZeroMap A.situation W r)) =
      A.sectionRingToFunctionField i (A.situation.sectionRingBaseMap W r) := by
    rw [awayToFunctionField, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
    change IsLocalization.Away.lift f _ (Localization.mk _ 1) = _
    rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq, h0]
  rw [h1, sectionRingToFunctionField, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    A.toPolynomial_sectionRingBaseMap W r, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.germ W _ i.2).hom r) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

set_option backward.isDefEq.respectTransparency false in
/-- **The structure morphism is biregular around a good prime divisor.** If the degree-one section
`a` over the affine open `W` has order exactly `-D_E` along a prime divisor `E` meeting `W`, then
the generic point of `E` has a basic open neighbourhood in `W` over which `Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y`
is an isomorphism. -/
theorem exists_basicOpen_le_biregularLocus [CompactSpace Y] (hW : IsAffineOpen W)
    (a : A.situation.sectionPieces W 1)
    (hf0 : A.sectionRingToFunctionField i (DirectSum.of _ 1 a) ≠ 0)
    (E : MMP.Mori.PrimeDivisor Y) (hE : (E.support ∩ W).Nonempty)
    (hgood : E.valuation (A.pieceToRationalFunctions W 1 a
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩) = WithZero.exp (-D.coeff E)) :
    ∃ r : Γ(Y, W), Y.basicOpen r ≤ biregularLocus A.toBase ∧ E.genericPoint ∈ Y.basicOpen r := by
  classical
  obtain ⟨φ, hφ⟩ := PrimeDivisor.exists_units_algebraMap_eq hf0
  have hcomp : A.pieceToRationalFunctions W 1 a
        ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ =
        (φ : RationalFunctions Y) E.component := by
    apply IsFractionRing.injective _ Y.functionField
    rw [hφ, sectionRingToFunctionField_of]
    exact algebraMap_rationalFunctionsPresheaf_apply_eq (W := W) _ _ i
  rw [hcomp, E.valuation_component, WithZero.exp_inj] at hgood
  set S : Set (MMP.Mori.PrimeDivisor Y) :=
    {E' | (E'.support ∩ W).Nonempty ∧ E'.ord φ ≠ -D.coeff E'}
  have hS : S.Finite := by
    refine ((finite_ord_ne_zero φ).union D.support.finite_toSet).subset fun E' hE' => ?_
    by_contra hne
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff,
      not_or, not_not] at hne
    exact hE'.2 (by rw [hne.1]; change (0 : ℤ) = -(D E'); rw [hne.2, neg_zero])
  set C : Set Y := ⋃ E' ∈ S, (E'.support : Set Y)
  have hC : IsClosed C := hS.isClosed_biUnion fun E' _ =>
    AlgebraicGeometry.PrimeDivisor.support_eq_closure E' ▸ isClosed_closure
  let O : Y.Opens := W ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hηW : E.genericPoint ∈ W := E.genericPoint_mem_of_nonempty hE
  have hηO : E.genericPoint ∈ O := by
    refine ⟨hηW, fun hm => ?_⟩
    obtain ⟨E', hE'S, hηE'⟩ := Set.mem_iUnion₂.mp hm
    obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (PrimeDivisor.eq_genericPoint_of_mem_support E' hηE' E.coheight_genericPoint)
    exact hE'S.2 hgood
  obtain ⟨r, hrO, hηr⟩ := hW.exists_basicOpen_le (⟨E.genericPoint, hηO⟩ : O) hηW
  have hloc : D.IsLocalEquation (Y.basicOpen r) φ⁻¹ := by
    rintro E'' ⟨x, hxE, hxr⟩
    have hxO := hrO hxr
    have hgood'' : E''.ord φ = -D.coeff E'' := by
      by_contra hne
      exact hxO.2 (Set.mem_iUnion₂.mpr ⟨E'', ⟨⟨x, hxE, hxO.1⟩, hne⟩, hxE⟩)
    rw [PrimeDivisor.ord_inv, hgood'', neg_neg]
  exact ⟨r, le_biregularLocus (A.isBiregular_toBase_of_isLocalEquation (hW.basicOpen r) hloc),
    hηr⟩

/-- The generic point of `Y` lies in the biregular locus of the structure morphism. -/
theorem genericPoint_mem_biregularLocus [CompactSpace Y] :
    genericPoint Y ∈ biregularLocus A.toBase := by
  obtain ⟨V, hV, hVne, h0⟩ := exists_isAffineOpen_coeff_eq_zero D
  have hloc : D.IsLocalEquation V 1 := fun E hE => by rw [h0 E hE, PrimeDivisor.ord_one]
  exact le_biregularLocus (A.isBiregular_toBase_of_isLocalEquation hV hloc)
    (((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hVne))

set_option backward.isDefEq.respectTransparency false in
/-- **`Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y` is an isomorphism at the points of codimension at most one.** If
the divisorial algebra is generated in degree one, every point of coheight at most one of its
relative `Proj` maps into the biregular locus of the structure morphism. -/
theorem toBase_mem_biregularLocus_of_coheight_le_one [CompactSpace Y]
    (hgen : ∀ W : Y.Opens, A.situation.IsLocallyDegreeOneGenerated W) (z : A.model)
    (hz : Order.coheight z ≤ 1) : A.toBase z ∈ biregularLocus A.toBase := by
  obtain ⟨W, hW, hzW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show A.toBase z ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨a, p, ha0, rfl⟩ := A.exists_relativeProjChart_awayι_eq hW (hgen W) z hzW
  have hfa : DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 := ⟨a, rfl⟩
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
  have hbo := A.toBase_relativeProjChart_awayι_mem_basicOpen_iff hW hfa p
  have hθ := fun r => A.awayToFunctionField_fromZeroRingHom i hf0 r hη
  by_cases hp0 : p.asIdeal = ⊥
  · obtain ⟨r, hr, hηr⟩ :=
      hW.exists_basicOpen_le (⟨genericPoint Y, A.genericPoint_mem_biregularLocus⟩ :
        biregularLocus A.toBase) hη
    refine hr ((hbo r).mpr fun hmem => ?_)
    rw [hp0, Ideal.mem_bot] at hmem
    have hu := (Y.mem_basicOpen r (genericPoint Y) hη).mp hηr
    rw [← hθ r, hmem, map_zero] at hu
    exact not_isUnit_zero hu
  · have hz' : Order.coheight
        ((Proj.awayι _ _ hfa one_pos ≫ A.situation.relativeProjChart (⟨W, hW⟩ : Y.affineOpens)) p)
          ≤ 1 := hz
    obtain ⟨E, hE, hgood, hmem⟩ := A.exists_primeDivisor_of_height_one i a hf0 p.asIdeal hp0
      fun p' hp' h0 hle => haveI := hp'; MMP.eq_asIdeal_of_coheight_le_one _ p hz' p' h0 hle
    obtain ⟨r, hr, hηr⟩ := A.exists_basicOpen_le_biregularLocus i hW a hf0 E hE hgood
    refine hr ((hbo r).mpr fun hq => ?_)
    obtain ⟨hx, hmax⟩ := (hmem _).mp hq
    have hηW : E.genericPoint ∈ W := E.genericPoint_mem_of_nonempty hE
    have heq : (⟨_, hx⟩ : E.valuationSubring) =
        E.valuationSubringEquiv (Y.presheaf.germ W E.genericPoint hηW r) := by
      refine Subtype.ext ?_
      change _ = (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.germ W _ hηW).hom r)
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
      exact hθ r
    rw [heq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
    exact hmax (((Y.mem_basicOpen r E.genericPoint hηW).mp hηr).map E.valuationSubringEquiv)

/-- If the divisorial algebra is generated in degree one, every point whose closure has codimension
at most one maps into the biregular locus of the structure morphism. -/
theorem toBase_mem_biregularLocus_of_codimension_le_one [CompactSpace Y]
    (hgen : ∀ W : Y.Opens, A.situation.IsLocallyDegreeOneGenerated W) (z : A.model)
    (hz : codimension (TopologicalSpace.IrreducibleCloseds.closureSingleton z) ≤ 1) :
    A.toBase z ∈ biregularLocus A.toBase :=
  A.toBase_mem_biregularLocus_of_coheight_le_one hgen z
    (Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight z ▸ hz)

end MMP.Fourfold.DivisorialSectionAlgebra
