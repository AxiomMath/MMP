module
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyDictionary
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel

/-!
# Dlt pairs are log terminal in the sense of *Flips and abundance*

Let `k` be a field of characteristic zero and `(X, B)` a `ℚ`-factorial pair with a rational
boundary `B` which is dlt in the sense of Kollár–Mori (2.37). Then `(X, B)` is log terminal in
the sense of *Flips and abundance* (2.13.1): there is a log resolution `f : Y ⟶ X` of `(X, B)`
such that every prime divisor of `Y` exceptional over `X` has positive log discrepancy.

The proof takes the closed set `Z` of the dlt condition and a log resolution of `(X, Supp B)`
that is an isomorphism over the snc locus `X ∖ Z`. Every exceptional prime divisor then has its
centre in `Z`, so its log discrepancy is positive, and the two conventions for log discrepancies
agree (`MMP.Flips.ProperDivisorOver.isLogDiscrepancy_iff`).

## Main results

* `MMP.Intersection.IsDltPair.isLogTerminal`: a `ℚ`-factorial dlt pair is log terminal in the
  sense of `MMP.Flips.IsLogTerminal`, for every canonical divisor.
* `MMP.Intersection.isLogResolution_of_isSNCClosedSubset`: a resolution which is snc along
  `Ex(f) ∪ f⁻¹(Supp B)` is a log resolution in the sense of `MMP.Flips.IsLogResolution`.
* `MMP.Intersection.isSNCClosedSubset_preimage_of_isSNC_restrictOpen`: if `B|_U` is snc, then
  `U ∩ Supp B` is an snc closed subset of `U`.
* `MMP.Intersection.not_isExceptional_of_mem_biregularLocus`: a divisor over `X` whose centre
  meets the biregular locus of its model is not exceptional.
* `MMP.Intersection.support_mem_componentsOf`,
  `MMP.Intersection.finite_setOf_support_subset`,
  `MMP.Intersection.isSNC_reducedDivisorOf_of_mem_componentsOf`: the prime divisors supported in
  an snc closed subset are finitely many of its components, and their reduced divisor is snc.

## Implementation notes

The source works over `ℂ`; the statement is over any field of characteristic zero. Log
terminality in the sense of *Flips and abundance* is computed with a chosen canonical divisor
`K` of dimension `n`; the statement holds for every such choice.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.37
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.13.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

universe u

namespace MMP.Intersection

open MMP.Mori

/-! ### `ℝ`-Cartier divisors -/

/-- If `m(K + B)` is Cartier for some `m > 0`, then `K + B` is an `ℝ`-combination of Cartier
divisors. -/
private theorem isCartierCombination_toRDivisor_add {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {K : Divisor X} {B : QDivisor X} (h : (Divisor.toQDivisor K + B).IsQCartier) :
    MMP.Flips.IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor B) := by
  obtain ⟨m, hm, M, hM, hMc⟩ := h.exists_pos
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => M, fun _ => hMc, ?_⟩
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine DivisorWithCoeffs.ext' fun Γ => ?_
  have := congrArg (fun G : QDivisor X => G.coeff Γ) hM
  simp only [Divisor.coeff_toQDivisor, smul_add, natCast_zsmul, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_smul, nsmul_eq_mul] at this
  have h' : (M.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by linear_combination this
  have h'' : (M.coeff Γ : ℝ) = m * (K.coeff Γ + B.coeff Γ) := by exact_mod_cast h'
  simp only [← MMP.Flips.toRDivisor_eq_mapCoeffs]
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_one, h'', DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
  field_simp

/-! ### Dimension of the centre -/

/-- A natural-number dimension `n` with `d + 1 = n` is not `≥ d + 2`. -/
private theorem not_add_two_le_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ}
    (h1 : d + ((1 : ℕ∞) : WithBot ℕ∞) = n) : ¬ d + 2 ≤ n := by
  rw [← h1, show (2 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) + 1 by norm_num, ← add_assoc, h1]
  exact_mod_cast (ENat.lt_add_one_iff (ENat.coe_ne_top n)).2 le_rfl |>.not_ge

/-- A divisor `(Y, f, E)` over a variety `X` of dimension `n` with `f(η_E)` in the biregular locus
of `f` is not exceptional: `f(E)` is then a prime divisor of `X`. -/
theorem not_isExceptional_of_mem_biregularLocus {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : MMP.Flips.ProperDivisorOver k sX)
    (h : D.f D.E.genericPoint ∈ biregularLocus D.f) : ¬ D.IsExceptional := by
  intro hEx
  unfold MMP.Flips.ProperDivisorOver.IsExceptional at hEx
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn] at hEx
  have h1 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn, MMP.Positivity.coheight_map_of_mem_biregularLocus D.f h,
    MMP.Mori.PrimeDivisor.coheight_genericPoint] at h1
  exact not_add_two_le_of_add_one_eq h1 hEx

/-! ### Transforms under the inverse of a birational morphism -/

/-- A partial isomorphism representing the rational map of `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A representative `g` of the inverse of a birational morphism `f` is a section of `f` on its
domain. -/
private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- A prime divisor with a nonzero coefficient in the linear extension of a partial map `φ` is the
image of a prime divisor in the support. -/
private theorem exists_mem_support_of_mapPrimeDivisors_ne_zero {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {P : MMP.Mori.PrimeDivisor Y}
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Γ ∈ D.support, φ Γ = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Γ hΓ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases hφ : φ Γ with _ | P'
  · rfl
  · have hP' : P' ≠ P := fun he => hne Γ hΓ (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' hP'

/-- The strict transform of a component `Γ` of `D` under a birational morphism `f` lies over
`Γ`: a prime divisor in the support of `f⁻¹_* D` lies in `f⁻¹(Supp D)`. -/
private theorem support_subset_preimage_of_birationalInverseTransform_ne_zero {X Y : Scheme.{u}}
    [IsReduced Y] [IsReduced X] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {R : Type*} [AddCommMonoid R] (f : Y ⟶ X) (hf : IsBirationalMorphism f)
    {D : DivisorWithCoeffs R X} {P : MMP.Mori.PrimeDivisor Y}
    (h : (MMP.Flips.birationalInverseTransform f hf D).coeff P ≠ 0) :
    ∃ Γ ∈ D.support, (P.support : Set Y) ⊆ f ⁻¹' (Γ.support : Set X) := by
  obtain ⟨Γ, hΓ, hΓP⟩ := exists_mem_support_of_mapPrimeDivisors_ne_zero h
  refine ⟨Γ, hΓ, ?_⟩
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hle : RationalMap.transform (RationalMap.IsBirational.inverse hf) Γ.idealSheaf.support ≤
      ⟨f ⁻¹' (Γ.idealSheaf.support : Set X),
        Γ.idealSheaf.support.isClosed.preimage f.continuous⟩ := by
    refine RationalMap.transform_le_iff.mpr fun g hg => ?_
    rintro _ ⟨q, hq, rfl⟩
    change f (g.hom ⟨q.1, q.2⟩) ∈ (Γ.idealSheaf.support : Set X)
    rw [apply_hom_eq_of_isInverse f e he g (hg.trans he'.symm) q.2]
    exact hq
  rwa [RationalMap.support_transformPrimeDivisor hΓP]

/-! ### Components of an snc closed subset -/

/-- The support of a prime divisor contained in an snc closed subset `D` is an irreducible
component of `D`. -/
theorem support_mem_componentsOf {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {D : Set Y} (hD : IsSNCClosedSubset sY D)
    (P : MMP.Mori.PrimeDivisor Y) (hP : (P.support : Set Y) ⊆ D) :
    (P.support : Set Y) ∈ componentsOf D := by
  have hPirr := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P
  obtain ⟨hcl, hD0 | ⟨hpure, -, -⟩⟩ := hD
  · exact absurd (Set.subset_empty_iff.mp (hD0 ▸ hP)) hPirr.nonempty.ne_empty
  obtain ⟨W, hW, hηW⟩ := exists_mem_componentsOf <| hP <| by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hWcl : IsClosed W := isClosed_of_mem_componentsOf hcl hW
  have hPW : (P.support : Set Y) ⊆ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηW) hWcl
  let Wc : IrreducibleCloseds Y := ⟨W, hW.1.1, hWcl⟩
  let Pc : IrreducibleCloseds Y := ⟨P.support, hPirr, P.idealSheaf.support.isClosed⟩
  have hW1 : codimension Wc = 1 := hpure Wc ⟨hW.1.2, fun V hV hWV => hW.2 ⟨V.isIrreducible, hV⟩ hWV⟩
  have hP1 : codimension Pc = 1 :=
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.codimension_eq_one_of_eq_support Pc P rfl
  have hPWeq : Pc = Wc := by
    by_contra hne
    rw [codimension_eq_coheight] at hW1 hP1
    have := Order.coheight_strictAnti (lt_of_le_of_ne (show Pc ≤ Wc from hPW) hne)
      (hW1 ▸ ENat.one_lt_top)
    rw [hW1, hP1] at this
    exact lt_irrefl _ this
  exact (show (P.support : Set Y) = W from
    congrArg (fun V : IrreducibleCloseds Y => (V : Set Y)) hPWeq) ▸ hW

/-- Only finitely many prime divisors are supported in an snc closed subset. -/
theorem finite_setOf_support_subset {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {D : Set Y} (hD : IsSNCClosedSubset sY D) :
    {P : MMP.Mori.PrimeDivisor Y | (P.support : Set Y) ⊆ D}.Finite := by
  have hfin : (componentsOf D).Finite := by
    obtain ⟨-, hD0 | ⟨-, hfin, -⟩⟩ := id hD
    · exact Set.finite_empty.subset fun W hW =>
        hW.1.1.nonempty.ne_empty (Set.subset_empty_iff.mp (hD0 ▸ hW.1.2))
    · exact hfin
  exact (hfin.preimage fun P _ Q _ hPQ =>
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ.le).subset
    fun P hP => support_mem_componentsOf hD P hP

/-- The reduced divisor on finitely many components of an snc closed subset is an snc divisor,
on a scheme whose local rings have regular systems of parameters. -/
theorem isSNC_reducedDivisorOf_of_mem_componentsOf {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)}
    (hreg : ∀ y : Y, ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y), IsRegularSystemOfParameters z)
    {D : Set Y} (hD : IsSNCClosedSubset sY D) (S : Finset (MMP.Mori.PrimeDivisor Y))
    (hS : ∀ P ∈ S, (P.support : Set Y) ∈ componentsOf D) :
    (MMP.Intersection.reducedDivisorOf S).IsSNC sY := by
  classical
  unfold DivisorWithCoeffs.IsSNC
  rw [MMP.Intersection.support_reducedDivisorOf]
  obtain ⟨-, hD | ⟨-, -, hfam1, hfam2⟩⟩ := hD
  · obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun P hP =>
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P).nonempty.ne_empty
        (Set.subset_empty_iff.mp (hD ▸ (hS P hP).1.2))
    refine ⟨fun E hE => absurd hE (Finset.notMem_empty _), fun x => ?_⟩
    obtain ⟨n, z, hz⟩ := hreg x
    exact ⟨n, z, fun E => absurd E.2.1 (Finset.notMem_empty _), hz,
      fun E => absurd E.2.1 (Finset.notMem_empty _), fun E => absurd E.2.1 (Finset.notMem_empty _)⟩
  · refine ⟨fun E hE => ?_, fun x => ?_⟩
    · have := (hfam1 ⟨_, hS E hE⟩).2.2
      rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
        ⟨_, hS E hE⟩ E rfl] at this
    · obtain ⟨n, z, c, hz, hI, hc⟩ := hfam2 x
      have hmem : ∀ E : {E : MMP.Mori.PrimeDivisor Y // E ∈ S ∧ x ∈ E.support},
          x ∈ (componentsFamily D ⟨_, hS E.1 E.2.1⟩).support := fun E => by
        rw [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
          ⟨_, hS E.1 E.2.1⟩ E.1 rfl]
        exact E.2.2
      refine ⟨n, z, fun E => c ⟨⟨_, hS E.1 E.2.1⟩, hmem E⟩, hz, ?_, fun E => ?_⟩
      · intro E E' hEE'
        exact Subtype.ext (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset
          (congrArg (fun W => W.1.1) (hc hEE')).le)
      · have := hI ⟨⟨_, hS E.1 E.2.1⟩, hmem E⟩
        rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
          ⟨_, hS E.1 E.2.1⟩ E.1 rfl] at this

/-! ### The snc locus -/

/-- If the restriction `B|_U` of `B` to an open `U` is snc, the preimage of `Supp B` in `U` is an
snc closed subset of `U`. -/
theorem isSNCClosedSubset_preimage_of_isSNC_restrictOpen {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) (B : QDivisor X)
    (h : (B.restrictOpen U).IsSNC (U.ι ≫ sX)) :
    IsSNCClosedSubset (U.ι ≫ sX)
      (U.ι ⁻¹' (B.support.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  have h' : (MMP.Intersection.reducedDivisorOf (B.restrictOpen U).support).IsSNC (U.ι ≫ sX) :=
    h.of_support_subset (by rw [MMP.Intersection.support_reducedDivisorOf])
  have hS := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ h'
  rw [MMP.Intersection.support_reducedDivisorOf] at hS
  convert hS using 1
  ext x
  simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨E, hE, hxE⟩
    obtain ⟨F, rfl⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι E x hxE
    refine ⟨F, ?_,
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι F x).mp hxE⟩
    rwa [Finsupp.mem_support_iff] at hE ⊢
  · rintro ⟨F, hF, hxF⟩
    refine ⟨OpenWeilRestriction.primeDivisorMap U.ι F, ?_,
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι F x).mpr hxF⟩
    rwa [Finsupp.mem_support_iff] at hF ⊢

/-- If the inverse transform of `B` under the inclusion of an open `U` is snc, the preimage of
`Supp B` in `U` is an snc closed subset of `U`. -/
theorem isSNCClosedSubset_preimage_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) (B : QDivisor X)
    (h : DivisorWithCoeffs.IsSNC (U.ι ≫ sX) (inverseTransformDivisor U.ι B)) :
    IsSNCClosedSubset (U.ι ≫ sX)
      (U.ι ⁻¹' (B.support.sup fun E => (E.idealSheaf.support : Set X))) :=
  isSNCClosedSubset_preimage_of_isSNC_restrictOpen sX U B <| by
    rwa [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen] at h

/-! ### Log resolutions -/

/-- A scheme separated over a separated scheme is separated. -/
private lemma isSeparated_terminal_from_of_isSeparated {X S : Scheme.{u}} (s : X ⟶ S)
    [IsSeparated s] [IsSeparated (S ↘ ⊤_ Scheme)] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (S ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A scheme smooth over a field has a regular system of parameters at every point. -/
theorem exists_isRegularSystemOfParameters_of_smooth {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [Smooth sY] (y : Y) :
    ∃ (m : ℕ) (z : Fin m → Y.presheaf.stalk y), IsRegularSystemOfParameters z := by
  have := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sY).mp
    inferInstance y
  exact exists_isRegularSystemOfParameters _

/-- **A resolution which is snc along `Ex(f) ∪ f⁻¹(Supp B)` is a log resolution** in the sense of
*Flips and abundance*. -/
theorem isLogResolution_of_isSNCClosedSubset {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {B : QDivisor X}
    (hlv : MMP.Flips.IsLogVariety k sX (QDivisor.toRDivisor B)) {Y : Scheme.{u}} {f : Y ⟶ X}
    (hres : IsResolutionOfVariety sX f)
    (hsnc : IsSNCClosedSubset (f ≫ sX) ((exceptionalSet f : Set Y) ∪
      f ⁻¹' (B.support.sup fun E => (E.idealSheaf.support : Set X)))) :
    MMP.Flips.IsLogResolution sX (QDivisor.toRDivisor B) f := by
  classical
  have hf : IsBirationalMorphism f := hres.isBirationalMorphism
  have : IsSeparated sX := hres.isVariety.toIsSeparated
  have := isSeparated_terminal_from_of_isSeparated sX
  have := hres.isVariety_source
  have : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  have := isSeparated_terminal_from_of_isSeparated (f ≫ sX)
  set T := MMP.Flips.birationalInverseTransform f hf (QDivisor.toRDivisor B)
  have hsub : ∀ P, T.coeff P ≠ 0 ∨ MMP.Flips.IsExceptionalPrimeDivisor sX f P →
      (P.support : Set Y) ⊆ (exceptionalSet f : Set Y) ∪
        f ⁻¹' (B.support.sup fun E => (E.idealSheaf.support : Set X)) := by
    rintro P (hP | ⟨hY, hf', hp, hEx⟩)
    · obtain ⟨Γ, hΓ, hPΓ⟩ :=
        support_subset_preimage_of_birationalInverseTransform_ne_zero f hf hP
      have hΓB : Γ ∈ B.support := by
        rw [Finsupp.mem_support_iff] at hΓ ⊢
        exact fun h0 => hΓ <| by
          change ((B Γ : ℚ) : ℝ) = 0
          rw [h0, Rat.cast_zero]
      exact hPΓ.trans fun y hy => Or.inr <|
        (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X => (E.idealSheaf.support : Set X))
          hΓB) hy
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal (Set.singleton_subset_iff.mpr (Or.inl ?_)) hsnc.1
      rw [SetLike.mem_coe, mem_exceptionalSet]
      exact fun hV => not_isExceptional_of_mem_biregularLocus hn
        (MMP.Flips.ProperDivisorOver.mk ⟨Y, f, hY, hf', P⟩ hp) hV hEx
  have hSfin : {P | T.coeff P ≠ 0 ∨ MMP.Flips.IsExceptionalPrimeDivisor sX f P}.Finite :=
    (finite_setOf_support_subset hsnc).subset hsub
  have : Smooth (f ≫ sX) := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hres.isSmoothScheme
  have hGsnc := isSNC_reducedDivisorOf_of_mem_componentsOf
    (exists_isRegularSystemOfParameters_of_smooth (f ≫ sX)) hsnc hSfin.toFinset
    fun P hP => support_mem_componentsOf hsnc P (hsub P (hSfin.mem_toFinset.mp hP))
  refine ⟨hlv, hres.isVariety_source, hres.isSmoothScheme, hres.isProjective.isProper, hf,
    reducedDivisorOf hSfin.toFinset, fun P => ?_, fun P => ?_, fun P => ?_, hGsnc.1,
    fun p _ => hGsnc.2 p⟩
  · rw [MMP.Intersection.coeff_reducedDivisorOf]
    split_ifs <;> simp
  · rw [MMP.Intersection.coeff_reducedDivisorOf]
    split_ifs with h
    · exact iff_of_true rfl (hSfin.mem_toFinset.mp h)
    · exact iff_of_false (by decide) (h ∘ hSfin.mem_toFinset.mpr)
  · rw [MMP.Intersection.coeff_reducedDivisorOf]
    split_ifs <;> simp

/-! ### Dlt pairs are log terminal -/

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **Dlt pairs are log terminal** in the sense of *Flips and abundance*. Over a field of
characteristic zero, if `(X, B)` is a `ℚ`-factorial pair (`MMP.Fourfold.IsQFactorial`) with
`ℚ`-boundary `B` that is dlt (`MMP.Intersection.IsDltPair`), then for every canonical divisor
`K` of `X` of dimension `n`, `(X, B)` is log terminal (`MMP.Flips.IsLogTerminal`) with respect
to `K`. -/
@[mmp "lem_mmp_dlt_is_fa_lt"]
public theorem IsDltPair.isLogTerminal [CharZero k] {B : QDivisor X}
    (hQ : MMP.Fourfold.IsQFactorial sX) (hB : IsDltPair sX B) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) :
    MMP.Flips.IsLogTerminal sX n K (MMP.Mori.QDivisor.toRDivisor B) := by
  obtain ⟨⟨hpair, hBeff, -⟩, hB1, Z, hZsm, hZsnc, hZpos⟩ := hB
  have hX : MMP.Mori.IsNormalVariety k sX := hpair.1
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hKB : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨n₀, K₀, hK₀, hall⟩ := hpair.isQCartier_of_linearlyEquivalent
    exact hall K (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK hK₀)
  have hlv : MMP.Flips.IsLogVariety k sX (QDivisor.toRDivisor B) :=
    ⟨hX, fun E => ⟨by simpa [QDivisor.coeff_toRDivisor] using hBeff E, by
      rw [QDivisor.coeff_toRDivisor]
      exact_mod_cast hB1 E⟩⟩
  obtain ⟨Y, f, hres, -, hsnc, hiso⟩ :=
    exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX B.support
  have hZV : (Z.compl : X.Opens) ≤ biregularLocus f :=
    le_biregularLocus (hiso _ hZsm (isSNCClosedSubset_preimage_of_isSNC sX _ B hZsnc))
  refine ⟨hlv, hK, isCartierCombination_toRDivisor_add hKB, ?_⟩
  refine ⟨Y, f, isLogResolution_of_isSNCClosedSubset hn hlv hres hsnc,
    fun hY hf hp E hEx b hb => ?_⟩
  set DE := MMP.Flips.ProperDivisorOver.mk ⟨Y, f, hY, hf, E⟩ hp
  refine hZpos n DE.toDivisorOver ?_ b <|
    (MMP.Flips.ProperDivisorOver.isLogDiscrepancy_iff ⟨hX, hK, hKB⟩ DE hres.isSmoothScheme b).mpr hb
  rw [DE.toDivisorOver.center_eq_closure_genericPoint]
  refine closure_minimal (Set.singleton_subset_iff.mpr ?_) Z.isClosed
  by_contra hZ
  exact not_isExceptional_of_mem_biregularLocus hn DE (hZV hZ) hEx

end MMP.Intersection
