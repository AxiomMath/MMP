module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.LowDiscrepancyJunction
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness

/-!
# Finiteness of the difficulty of an adjunction stratum

For a rational dlt pair `(X, B)` over an algebraically closed field of characteristic zero, and
iterated adjunction data `F` from `(X, B)` to a stratum `(S, B_S)`, the difficulty
`F.difficulty I` is finite. The pair `(S, B_S)` is again dlt, it is klt off `⌊B_S⌋`, and only
finitely many valuations of negative discrepancy lie off `⌊B_S⌋`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fold06.LemMmpStratumDifficultyFinite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold
open scoped WithZero

/-- The support of a prime divisor is a dlt stratum of a dlt pair in which it has coefficient at
least one. -/
private theorem isDltStratum_support {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) (P : MMP.Mori.PrimeDivisor X) (hP : 1 ≤ B.coeff P) :
    IsDltStratum sX B (P.support : Set X) := by
  have hirr : IsIrreducible (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  refine ⟨hB, {P}, Finset.singleton_nonempty P, by simpa using hP, ?_, ?_⟩
  · simpa using hirr.nonempty
  · refine ⟨⟨hirr, by simp⟩, fun T hT _ => ?_⟩
    simpa using hT.2

/-- A normal variety over a field is locally noetherian. -/
private theorem isLocallyNoetherian_of_isNormalVariety {k : Type} [Field k] {T : Scheme.{0}}
    {s : T ⟶ Spec (.of k)} (h : IsNormalVariety k s) : IsLocallyNoetherian T :=
  have := h.1
  LocallyOfFiniteType.isLocallyNoetherian s

/-- **The final pair of iterated adjunction data of a dlt pair is dlt.** -/
private theorem isDltPair_of_stratumAdjunctionData {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S := F.isNormalVariety.2
    haveI := isLocallyNoetherian_of_isNormalVariety F.isNormalVariety
    MMP.Intersection.IsDltPair (ι ≫ sX) BS := by
  induction F with
  | refl h => simpa using hB
  | @step S T ι BS F j BT h ih =>
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal S := F.isNormalVariety.2
    haveI := isLocallyNoetherian_of_isNormalVariety F.isNormalVariety
    have h' : IsAdjunctionStep (𝟙 S ≫ ι ≫ sX) BS j BT := by rwa [Category.id_comp]
    obtain ⟨-, P, hP, hrange, -⟩ := h
    let F' : StratumAdjunctionData (ι ≫ sX) BS (j ≫ 𝟙 S) BT := .step (.refl ih.1.1) j BT h'
    haveI : IsIntegral T := F'.isNormalVariety.1.toIsIntegral
    haveI : IsNormal T := F'.isNormalVariety.2
    haveI := isLocallyNoetherian_of_isNormalVariety F'.isNormalVariety
    simpa using (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
      (isDltStratum_support ih P hP)).1.2 F' (by simpa using hrange)

section Klt

universe u

variable {k : Type u} [Field k] {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
  [IsNormal S] {sS : S ⟶ Spec (.of k)} {BS : QDivisor S}

/-- The inclusion of a nonempty open subscheme of an integral scheme is dominant. -/
private theorem isDominant_ι_of_nonempty (U : S.Opens) [Nonempty U] : IsDominant U.ι :=
  Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)

/-- An open subscheme of the smooth locus is smooth. -/
private theorem isSmoothScheme_ι_of_le_smoothLocus {V : S.Opens} (hV : V ≤ smoothLocus sS) :
    IsSmoothScheme (V.ι ≫ sS) := by
  rw [IsSmoothScheme, eq_top_iff]
  intro x _
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 (hV x.2 : V.ι x ∈ smoothLocus sS)
  refine mem_smoothLocus_iff.2 ⟨V.ι ⁻¹ᵁ W, hxW, ?_⟩
  have : Smooth (W.ι ≫ sS) := hW
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-- If the center of a divisor over `S` meets an open subset, then the image of the generic point
of the divisor lies in it. -/
private theorem map_genericPoint_mem_of_center_meets (D : DivisorOver k sS) {V : S.Opens}
    (hV : ((D.center : Set S) ∩ V).Nonempty) : D.f D.E.genericPoint ∈ V := by
  obtain ⟨x, hx, hxV⟩ := hV
  rw [D.center_eq_closure_genericPoint] at hx
  exact (specializes_iff_mem_closure.mpr hx).mem_open V.isOpen hxV

/-- If `B_S` has nonnegative coefficients and `V` misses `⌊B_S⌋`, every coefficient of `B_S|_V` is
less than one. -/
private theorem coeff_restrictOpen_lt_one (hcoeff : ∀ P : MMP.Mori.PrimeDivisor S, 0 ≤ BS.coeff P)
    {V : S.Opens} (hV : V ≤ BS.roundDown.supp.compl) (E : MMP.Mori.PrimeDivisor V.toScheme) :
    (BS.restrictOpen V).coeff E < 1 := by
  rw [DivisorWithCoeffs.coeff_restrictOpen]
  by_contra hne
  push Not at hne
  have hfl : BS.roundDown.coeff (OpenWeilRestriction.primeDivisorMap V.ι E) ≠ 0 := by
    rw [DivisorWithCoeffs.coeff_roundDown]
    exact (Int.floor_pos.mpr hne).ne'
  have hmem := DivisorWithCoeffs.support_subset_supp hfl
    (MMP.Flips.primeDivisor_genericPoint_mem_support (OpenWeilRestriction.primeDivisorMap V.ι E))
  exact hV E.genericPoint.2 (by
    convert hmem using 1; exact (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm)

/-- A birational morphism from an irreducible scheme to an open subscheme `U` of the integral
scheme `S` is birational as a morphism to `S`. -/
private theorem isBirationalMorphism_comp_ι {Y : Scheme.{u}} [IrreducibleSpace Y]
    (U : S.Opens) {g : Y ⟶ U} (hg : IsBirationalMorphism g) : IsBirationalMorphism (g ≫ U.ι) := by
  have : Nonempty Y := (IrreducibleSpace.isIrreducible_univ Y).nonempty.to_subtype.map Subtype.val
  obtain ⟨W, hWne, hW⟩ := hg.exists_isOpenImmersion
  have : Nonempty W := hWne.to_subtype
  have hd : Dense (((W.ι ≫ g) ≫ U.ι).opensRange : Set S) :=
    ((W.ι ≫ g) ≫ U.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  refine ⟨⟨W, W.isOpen.dense hWne, _, hd, ((W.ι ≫ g) ≫ U.ι).isoOpensRange⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨W, W.isOpen.dense hWne, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom,
    Category.assoc]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans (Scheme.homOfLE_ι_assoc _ _ _).symm

variable [IsAlgClosed k] [CharZero k]

/-- **A divisor over an open subset is a divisor over `S`.** A divisor `(Y, f, E)` over a nonempty
open `U ⊆ S` with discrepancy `a` over `(U, B_S|_U)` gives the divisor `(Y, f ≫ ι_U, E)` over
`S`, whose center meets `U` and whose discrepancy over `(S, B_S)` is `a`. -/
private theorem exists_isDiscrepancy_comp_ι {n : ℕ} {K : Divisor S}
    (hPW : IsPairWith sS n K BS) (U : S.Opens) [Nonempty U] {D : DivisorOver k (U.ι ≫ sS)}
    {a : ℚ} (ha : IsDiscrepancy (U.ι ≫ sS) n (K.restrictOpen U) (BS.restrictOpen U) D a) :
    ∃ D₁ : DivisorOver k sS, ((D₁.center : Set S) ∩ U).Nonempty ∧
      IsDiscrepancy sS n K BS D₁ a := by
  haveI := isDominant_ι_of_nonempty U
  have := D.isIntegral
  let D₁ : DivisorOver k sS := ⟨D.Y, D.f ≫ U.ι, by rw [Category.assoc]; exact D.isNormalVariety,
    isBirationalMorphism_comp_ι U D.isBirationalMorphism, D.E⟩
  have hcen : ((D₁.center : Set S) ∩ U).Nonempty :=
    ⟨_, by rw [D₁.center_eq_closure_genericPoint]; exact subset_closure rfl,
      (D.f D.E.genericPoint).2⟩
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hPW.2.1 D₁
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPW D₁ U hcen
  have hv : (⟨_, D₁.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sS)).valuation = D.valuation := by
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    ext t
    obtain ⟨s, rfl⟩ :=
      (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩).2 t
    refine (congrArg (· s) hval).symm.trans ?_
    change D.E.divisorialValuation (functionFieldMap (D.f ≫ U.ι) s) =
      D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap U.ι s))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hba := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq (hPW.restrictOpen U).1 hv)
    ((hiff b).1 hb) ha
  exact ⟨D₁, hcen, hba ▸ hb⟩

/-- **A dlt pair is klt off its reduced boundary**, divisor by divisor: every divisor over `S`
whose center is not contained in `⌊B_S⌋` has discrepancy `> -1`. -/
private theorem neg_one_lt_of_center_meets (h : MMP.Intersection.IsDltPair sS BS) {n : ℕ}
    {K : Divisor S} (hK : K.IsCanonicalDivisor sS n) {D : DivisorOver k sS} {a : ℚ}
    (ha : IsDiscrepancy sS n K BS D a)
    (hD : ((D.center : Set S) ∩ (BS.roundDown.supp.compl : S.Opens)).Nonempty) : -1 < a := by
  obtain ⟨hPW, hcoeff, U', hU'sm, hsnc, hZ⟩ :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sS hK BS).mp h
  by_cases hc : (D.center : Set S) ⊆ (U' : Set S)ᶜ
  · exact hZ D a hc ha
  set W : S.Opens := BS.roundDown.supp.compl
  set V : S.Opens := U' ⊓ W
  have hηW := map_genericPoint_mem_of_center_meets D hD
  have hηU' : D.f D.E.genericPoint ∈ U' := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxU⟩ := hc
    exact map_genericPoint_mem_of_center_meets D ⟨x, hx, not_not.mp hxU⟩
  have hV : ((D.center : Set S) ∩ V).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hηU', hηW⟩
  haveI : Nonempty V := ⟨⟨_, hηU', hηW⟩⟩
  obtain ⟨hY, hf, E', -, -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPW D V hV
  have hlf : LocallyOfFiniteType sS := hPW.1.1.toLocallyOfFiniteType
  have : ∀ E : MMP.Mori.PrimeDivisor S,
      LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ sS) :=
    fun E => (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := E.idealSheaf.subschemeι ≫ sS)).mpr inferInstance
  have hsncV : (BS.restrictOpen V).IsSNC (V.ι ≫ sS) :=
    MMP.Threefold.Mori.OpenRestriction.isSNC_restrictOpen_of_cover sS (fun _ : Unit => U') V
      (fun x hx => ⟨(), hx.1⟩) BS fun _ => hsnc
  have hklt := MMP.Mori.isKltPair_of_isSNC (V.ι ≫ sS) (hPW.restrictOpen V).1
    (isSmoothScheme_ι_of_le_smoothLocus (inf_le_left.trans hU'sm)) (hPW.restrictOpen V).2.1
    hsncV (coeff_restrictOpen_lt_one (fun P => (hcoeff P).1) inf_le_right)
  exact (MMP.Threefold.Mori.IsKltPair.isDltPair hklt fun E => by
    rw [DivisorWithCoeffs.coeff_restrictOpen]; exact (hcoeff _).1).2 _ a ((hiff a).mp ha)

/-- **Restriction to an open subset, as a log discrepancy.** A divisor `(Y, f, E)` over `S` with
discrepancy `a` whose center meets an open `W` has the valuation of a divisor `D'` over `W`, with
proper structure morphism, of discrepancy `a` and log discrepancy `1 + a` for `(W, B_S|_W)`. -/
private theorem exists_restrict_isLogDiscrepancy {n : ℕ} {K : Divisor S} {D : DivisorOver k sS}
    {a : ℚ} (ha : IsDiscrepancy sS n K BS D a) (W : S.Opens)
    (hD : ((D.center : Set S) ∩ W).Nonempty) :
    haveI : Nonempty W := ⟨⟨hD.choose, hD.choose_spec.2⟩⟩
    haveI : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense ⟨hD.choose, hD.choose_spec.2⟩)
    ∃ D' : DivisorOver k (W.ι ≫ sS), IsProper D'.f ∧
      D'.valuation.comap (functionFieldMap W.ι) = D.valuation ∧
      IsDiscrepancy (W.ι ≫ sS) n (K.restrictOpen W) (BS.restrictOpen W) D' a ∧
      MMP.Intersection.IsLogDiscrepancy (W.ι ≫ sS) n
        (QDivisor.toRDivisor (BS.restrictOpen W)) D' (1 + (a : ℝ)) := by
  haveI : Nonempty W := ⟨⟨hD.choose, hD.choose_spec.2⟩⟩
  haveI := isDominant_ι_of_nonempty W
  obtain ⟨hX, hK, m, hm, hC, -⟩ := id ha
  have hPW : IsPairWith sS n K BS := ⟨hX, hK, m, by exact_mod_cast hm.ne', hC⟩
  have hPWW := hPW.restrictOpen W
  haveI : CompactSpace W := hPWW.1.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : LocallyOfFiniteType (W.ι ≫ sS) := hPWW.1.1.toLocallyOfFiniteType
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPW D W hD
  have ha₁ := (hiff a).mp ha
  obtain ⟨E₂, hE₂⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hPWW.1
    (⟨_, D.f ∣_ W, hY, hf, E'⟩ : DivisorOver k (W.ι ≫ sS))
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWW.isPair hPWW.2.1
    E₂.toDivisorOver
  obtain rfl : c = a := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPWW hE₂ hc ha₁
  refine ⟨E₂.toDivisorOver, E₂.isProper, ?_, hc,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc E₂.isProper⟩
  change E₂.valuation.comap _ = _
  rw [hE₂, hval]

/-- **A dlt pair is klt off its reduced boundary**: the restriction of `(S, B_S)` to a nonempty
open `W` missing `⌊B_S⌋` is a klt pair (`MMP.Fourfold.IsKltPair`). -/
private theorem isKltPair_restrictOpen (h : MMP.Intersection.IsDltPair sS BS) (W : S.Opens)
    [Nonempty W] (hW : W ≤ BS.roundDown.supp.compl) :
    MMP.Fourfold.IsKltPair (W.ι ≫ sS) (BS.restrictOpen W) := by
  obtain ⟨hX, n, K, hK, hQ⟩ := h.1.1
  have hPW : IsPairWith sS n K BS := ⟨hX, hK, hQ⟩
  have hPWW := hPW.restrictOpen W
  refine ⟨⟨inferInstance, inferInstance, hPWW.isPair, fun P => ?_⟩, fun n' D' a' hl => ?_⟩
  · rw [DivisorWithCoeffs.coeff_restrictOpen]; exact h.1.2.1 _
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWW.isPair hPWW.2.1 D'
  have hac : a' = 1 + (c : ℝ) := MMP.Threefold.Bridges.IsLogDiscrepancy.unique hl
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hl.2.1)
  obtain ⟨D₁, hcen, hD₁⟩ := exists_isDiscrepancy_comp_ι hPW W hc
  have := neg_one_lt_of_center_meets h hK hD₁ (hcen.mono (Set.inter_subset_inter_right _ hW))
  have : (-1 : ℝ) < c := by exact_mod_cast this
  rw [hac]; linarith

/-- Pulling valuations back along the inclusion of a nonempty open subscheme is injective. -/
private theorem comap_functionFieldMap_injective (U : S.Opens) [Nonempty U] [IsDominant U.ι] :
    Function.Injective
      (fun ξ : Valuation U.toScheme.functionField ℤᵐ⁰ => ξ.comap (functionFieldMap U.ι)) := by
  have hsurj := (functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨Classical.arbitrary U, trivial⟩).2
  intro v w hvw
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact congrArg (fun v => v y) hvw

/-- A valuation counted by the difficulty is, on the complement `W` of `⌊B_S⌋`, the valuation of
a divisor with proper structure morphism, whose discrepancy `a` satisfies `-1 < a < -α` and whose
log discrepancy is `1 + a`. -/
private theorem exists_of_mem_difficultValuations (h : MMP.Intersection.IsDltPair sS BS)
    (W : S.Opens) [Nonempty W] (hW : W = BS.roundDown.supp.compl) {α : ℝ}
    {v : Valuation S.functionField ℤᵐ⁰} (hv : v ∈ difficultValuations sS BS α) :
    haveI : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense ⟨_, (Classical.arbitrary W).2⟩)
    ∃ (n : ℕ) (K : Divisor S) (a : ℚ) (D' : DivisorOver k (W.ι ≫ sS)),
      (a : ℝ) < -α ∧ -1 < a ∧ IsProper D'.f ∧
      D'.valuation.comap (functionFieldMap W.ι) = v ∧
      IsDiscrepancy (W.ι ≫ sS) n (K.restrictOpen W) (BS.restrictOpen W) D' a ∧
      MMP.Intersection.IsLogDiscrepancy (W.ι ≫ sS) n
        (QDivisor.toRDivisor (BS.restrictOpen W)) D' (1 + (a : ℝ)) := by
  obtain ⟨E, rfl, ⟨n, K, a, ha, hlt⟩, hc⟩ := hv
  have hcen : ((E.center : Set S) ∩ W).Nonempty := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxn⟩ := hc
    subst hW
    exact ⟨x, hx, hxn⟩
  obtain ⟨D', hp, hval, hd, hl⟩ := exists_restrict_isLogDiscrepancy ha W hcen
  exact ⟨n, K, a, D', hlt, neg_one_lt_of_center_meets h ha.2.1 ha (hW ▸ hcen), hp, hval, hd, hl⟩

/-- A valuation counted by the difficulty has its center meeting the complement of `⌊B_S⌋`, which
is therefore nonempty. -/
private theorem nonempty_of_mem_difficultValuations {α : ℝ} {v : Valuation S.functionField ℤᵐ⁰}
    (hv : v ∈ difficultValuations sS BS α) : Nonempty (BS.roundDown.supp.compl : S.Opens) := by
  obtain ⟨E, -, -, hc⟩ := hv
  rw [Set.not_subset] at hc
  obtain ⟨x, -, hxn⟩ := hc
  exact ⟨⟨x, hxn⟩⟩

/-- **Finitely many valuations of negative discrepancy off `⌊B_S⌋`.** For a dlt pair `(S, B_S)`,
only finitely many divisorial valuations of `k(S)` with center not contained in `⌊B_S⌋` have
negative discrepancy. -/
private theorem finite_difficultValuations_zero (h : MMP.Intersection.IsDltPair sS BS) :
    (difficultValuations sS BS 0).Finite := by
  by_cases hne : Nonempty (BS.roundDown.supp.compl : S.Opens)
  swap
  · convert Set.finite_empty
    exact Set.eq_empty_iff_forall_notMem.mpr fun v hv =>
      hne (nonempty_of_mem_difficultValuations hv)
  set W : S.Opens := BS.roundDown.supp.compl with hW
  haveI := isDominant_ι_of_nonempty W
  have hX : IsNormalVariety k (W.ι ≫ sS) := h.1.1.1.restrictOpen W
  have hfin := (isKltPair_restrictOpen h W le_rfl).finite_lowDiscrepancySet
  refine ((hfin.union (((BS.restrictOpen W).support.finite_toSet).image
    fun P => (DivisorOver.ofPrimeDivisor k hX P).valuation)).image
      (fun ξ => ξ.comap (functionFieldMap W.ι))).subset ?_
  intro v hv
  obtain ⟨n, K, a, D', hlt, -, hp, hval, hd, hl⟩ := exists_of_mem_difficultValuations h W hW hv
  refine ⟨D'.valuation, ?_, hval⟩
  have hlt0 : (a : ℝ) < 0 := by simpa using hlt
  by_cases h2 : 2 ≤ codimension D'.center
  · exact Or.inl ⟨⟨D', hp, rfl, h2⟩, 1 + a, ⟨n, D', hp, rfl, hl⟩, by linarith⟩
  · right
    rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at h2
    push Not at h2
    obtain ⟨P, hP⟩ := h2
    refine ⟨P, ?_, hP.symm⟩
    obtain ⟨hXW, hKW, m, hm, hC, -⟩ := id hd
    have hPW : IsPairWith (W.ι ≫ sS) n (K.restrictOpen W) (BS.restrictOpen W) :=
      ⟨hXW, hKW, m, by exact_mod_cast hm.ne', hC⟩
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hKW
      (DivisorOver.ofPrimeDivisor k hX P)
    have e1 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hP hd hc
    have e2 := hc.eq_neg_coeff_of_ofPrimeDivisor hX
    refine Finset.mem_coe.2 <| Finsupp.mem_support_iff.2 fun h0 => ?_
    change (BS.restrictOpen W).coeff P = 0 at h0
    rw [e1, e2, h0] at hlt0
    simp at hlt0

/-- The numbers of the hyperstandard set `D(I)` below a bound `c < 1` are finitely many. -/
private theorem finite_setOf_mem_hyperstandardSet_lt {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b)
    {c : ℝ} (hc : c < 1) : {x | x ∈ hyperstandardSet I ∧ x < c}.Finite := by
  have hfin := MMP.Flips.finite_setOf_standardCoefficient_le (I := I) (fun i => ((i : ℚ) : ℝ))
    (fun i => by exact_mod_cast hI i i.2) (sub_pos.mpr hc)
  refine (hfin.image fun p : ℕ+ × (I → ℕ) =>
    ((p.1 : ℝ) - 1) / p.1 + ∑ i, (p.2 i : ℝ) * ((i : ℚ) : ℝ) / p.1).subset ?_
  rintro x ⟨⟨-, m, hm, r, rfl⟩, hx⟩
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have key : 1 - 1 / (m : ℝ) + ∑ b ∈ I, (r b : ℝ) * (b : ℝ) / (m : ℝ) =
      (((⟨m, hm⟩ : ℕ+) : ℝ) - 1) / ((⟨m, hm⟩ : ℕ+) : ℝ) +
        ∑ i : I, ((fun i : I => r i) i : ℝ) * ((i : ℚ) : ℝ) / ((⟨m, hm⟩ : ℕ+) : ℝ) := by
    simp only [PNat.mk_coe]
    rw [Finset.sum_coe_sort I (fun b => (r b : ℝ) * (b : ℝ) / (m : ℝ))]
    congr 1
    field_simp
  refine ⟨(⟨m, hm⟩, fun i => r i), ?_, key.symm⟩
  change (((⟨m, hm⟩ : ℕ+) : ℝ) - 1) / ((⟨m, hm⟩ : ℕ+) : ℝ) +
        ∑ i : I, ((fun i : I => r i) i : ℝ) * ((i : ℚ) : ℝ) / ((⟨m, hm⟩ : ℕ+) : ℝ) ≤ 1 - (1 - c)
  rw [← key]; linarith

/-- **Each valuation counts for finitely many `α`.** A valuation `v` of negative discrepancy off
`⌊B_S⌋` has a well-defined discrepancy `a > -1`, and lies in the set counted for `α ∈ D(I)` only
when `α < -a`; there are finitely many such `α`. -/
private theorem finite_setOf_mem_difficultValuations (h : MMP.Intersection.IsDltPair sS BS)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b) {v : Valuation S.functionField ℤᵐ⁰}
    (hv : v ∈ difficultValuations sS BS 0) :
    {α | α ∈ hyperstandardSet I ∧ v ∈ difficultValuations sS BS α}.Finite := by
  haveI := nonempty_of_mem_difficultValuations hv
  set W : S.Opens := BS.roundDown.supp.compl with hW
  haveI := isDominant_ι_of_nonempty W
  obtain ⟨n₀, K₀, a₀, D₀, -, ha₀, -, hval₀, -, hl₀⟩ := exists_of_mem_difficultValuations h W hW hv
  have ha₀' : (-1 : ℝ) < a₀ := by exact_mod_cast ha₀
  refine (finite_setOf_mem_hyperstandardSet_lt hI (c := -(a₀ : ℝ)) (by linarith)).subset ?_
  rintro α ⟨hαD, hvα⟩
  obtain ⟨n, K, a, D', hlt, -, -, hval, -, hl⟩ := exists_of_mem_difficultValuations h W hW hvα
  have hvv : D'.valuation = D₀.valuation :=
    comap_functionFieldMap_injective W (hval.trans hval₀.symm)
  have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl hl₀ hvv
  exact ⟨hαD, by linarith⟩

/-- The sets counted for `α ≥ 0` lie in the set counted for `α = 0`. -/
private theorem difficultValuations_subset {α : ℝ} (hα : 0 ≤ α) :
    difficultValuations sS BS α ⊆ difficultValuations sS BS 0 := by
  rintro v ⟨E, hE, ⟨n, K, a, ha, hlt⟩, hc⟩
  exact ⟨E, hE, ⟨n, K, a, ha, by linarith⟩, hc⟩

/-- A sum over `α ∈ A` of the numbers of elements of sets `F α` is finite when all the sets lie in
a finite set `V₀` and each element of `V₀` lies in `F α` for finitely many `α`. -/
private theorem tsum_encard_ne_top {V : Type*} {A : Set ℝ} (F : ℝ → Set V) (V₀ : Set V)
    (hV₀ : V₀.Finite) (hsub : ∀ α ∈ A, F α ⊆ V₀)
    (hα : ∀ v ∈ V₀, {α | α ∈ A ∧ v ∈ F α}.Finite) :
    ∑' α : A, (F α).encard ≠ ⊤ := by
  have hT : (⋃ v ∈ V₀, {α | α ∈ A ∧ v ∈ F α}).Finite := hV₀.biUnion hα
  have hs := hT.preimage (f := ((↑) : A → ℝ)) Subtype.val_injective.injOn
  rw [tsum_eq_sum (s := hs.toFinset) fun α hα' => ?_]
  · exact ENat.sum_ne_top.mpr fun α _ =>
      Set.encard_ne_top_iff.mpr (hV₀.subset (hsub α α.2))
  · rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
    intro v hv
    exact hα' (hs.mem_toFinset.mpr (Set.mem_biUnion (hsub α α.2 hv) ⟨α.2, hv⟩))

/-- **The difficulty of a dlt pair is finite.** -/
private theorem adjunctionPairDifficulty_ne_top (h : MMP.Intersection.IsDltPair sS BS)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b) : adjunctionPairDifficulty sS I BS ≠ ⊤ :=
  tsum_encard_ne_top (A := hyperstandardSet I) (difficultValuations sS BS) _
    (finite_difficultValuations_zero h) (fun _ hα => difficultValuations_subset hα.1.1)
    fun _ hv => finite_setOf_mem_difficultValuations h hI hv

end Klt

end MMP.Fold06.LemMmpStratumDifficultyFinite

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StratumAdjunctionData

open MMP.Mori

/-- **The difficulty of an adjunction stratum is finite.** Let `(X, B)` be a dlt pair
(`MMP.Intersection.IsDltPair`) with `B` a `ℚ`-divisor, over an algebraically closed field `k` of
characteristic zero, and let `I ⊆ (0, 1]` be a finite set of rationals containing `1` and every
nonzero coefficient of `B`. For iterated adjunction data `F` from `(X, B)` to a stratum with pair
`(S, B_S)`, the difficulty `F.difficulty I` (`MMP.Fourfold.StratumAdjunctionData.difficulty`) is
finite. -/
@[mmp "lem_mmp_stratum_difficulty_finite"]
public theorem difficulty_ne_top {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B)
    {I : Finset ℚ} (hI : ∀ b ∈ I, 0 < b ∧ b ≤ 1) (hI1 : (1 : ℚ) ∈ I)
    (hcoeff : ∀ P, B.coeff P ≠ 0 → B.coeff P ∈ I)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    F.difficulty I ≠ ⊤ := by
  have hS := MMP.Fold06.LemMmpStratumDifficultyFinite.isDltPair_of_stratumAdjunctionData hB F
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  haveI : IsNormal S := F.isNormalVariety.2
  haveI := MMP.Fold06.LemMmpStratumDifficultyFinite.isLocallyNoetherian_of_isNormalVariety
    F.isNormalVariety
  exact MMP.Fold06.LemMmpStratumDifficultyFinite.adjunctionPairDifficulty_ne_top hS
    fun b hb => (hI b hb).1

end MMP.Fourfold.StratumAdjunctionData
