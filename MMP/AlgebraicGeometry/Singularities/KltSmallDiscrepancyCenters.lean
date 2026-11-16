module

public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction

universe u

section

/-!
# Centers of exceptional divisors of small log discrepancy over a klt pair

Let `(X, D)` be a Kawamata log terminal pair over a field of characteristic zero. Take a log
resolution `f : Y ⟶ X` whose exceptional set is the union of the `f`-exceptional
prime divisors and whose configuration `H₁, …, H_s` (the `f`-exceptional prime divisors and the
components of `f⁻¹_* D`) satisfies `a_ℓ(H_k) + a_ℓ(H_l) ≥ 2` whenever `H_k ≠ H_l` meet; such a
resolution is obtained from any log resolution by blowing up the components of the intersections
`H_k ∩ H_l` with `a_ℓ(H_k) + a_ℓ(H_l) < 2`, a process that terminates. Let `𝒩` be the finite set of
valuations of the `f`-exceptional prime divisors. For an exceptional divisor `ν ∉ 𝒩` with
`a_ℓ(ν, X, D) < min {2, 2 + discrep(X, D)}`, the center of `ν` on `Y` is not a divisor; the snc
estimate for the crepant boundary `B = ∑ (1 - a_ℓ(H_k)) H_k` on `Y` places it, with codimension
`2`, in exactly one `H_k`, and the bound `discrep(X, D)` rules out an exceptional `H_k`. Since the
center avoids `Ex(f)`, `f` is a local isomorphism at its generic point, and the description
descends to `X`.

## Main results

* `MMP.FourfoldProofs.Fa4KltSmallLogDiscrepancyCentersProof.solution`.

## Implementation notes

The resolution with the pair condition is built from the log resolution of
`MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset` by blowing up bad
components of pairwise intersections; termination uses integer weights bounding the log
discrepancies from below and the Dershowitz–Manna order on multisets. The center of `ν` on `Y`
comes from the valuative criterion for the proper morphism `f`, and the discrepancy of `ν` over
`(Y, D_Y)` is that over `(X, D)` by `MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff`. The
bound `discrep(X, D) ≤ a(H, X, D)` for an `f`-exceptional `H` uses
`MMP.Flips.IsQDiscrepancyWith.isDiscrepancy`, and the snc estimate on `Y` is
`MMP.Flips.codimension_center_eq_two_of_logDiscrepancy_lt_two`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.2
-/

open CategoryTheory AlgebraicGeometry

namespace MMP.FourfoldProofs.Fa4KltSmallLogDiscrepancyCentersProof

section LogResolution

open CategoryTheory TopologicalSpace MMP.Mori MMP.Resolution
open AlgebraicGeometry hiding PrimeDivisor

/-! ### Snc closed subsets are snc divisors -/

/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : MMP.Mori.PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : MMP.Mori.DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : MMP.Mori.PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-! ### Existence of log resolutions -/

/-- **Log resolutions exist** in characteristic zero: the snc-preserving log resolution of the
reduced divisor `Supp D` is a log resolution of `(X, D)`. -/
private theorem exists_isLogResolution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (D : RDivisor X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), MMP.Mori.IsLogResolution sX D g := by
  obtain ⟨Y, f, hres, hpure, hS, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX D.support
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := hres.isVariety_source
  have : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have hsupp_eq : (D.supp : Set X) = D.support.sup fun E => (E.idealSheaf.support : Set X) := by
    rw [DivisorWithCoeffs.supp, Closeds.coe_finset_sup]
    rfl
  rw [← hsupp_eq] at hS
  refine ⟨Y, f, ⟨⟨hres.isProjective.isProper, hres.isBirationalMorphism, hres.isSmoothScheme⟩,
    hpure, isSNCSubset_of_isSNCClosedSubset ?_⟩⟩
  simpa using hS

end LogResolution

open MMP MMP.Flips TopologicalSpace
open MMP.Mori hiding IsLogResolution exceptionalSet

section Setup

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  (n : ℕ) (K : Divisor X) (D : RDivisor X)

/-- The configuration `Ex(f) ∪ f⁻¹(Supp D)` of a morphism `f : Y ⟶ X`. -/
private def cfg {Y : Scheme.{u}} (f : Y ⟶ X) : Closeds Y :=
  Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous

/-- `a` is a log discrepancy over `(X, D)` of the prime divisor `P` of the model `f : Y ⟶ X`. -/
private def IsLD {Y : Scheme.{u}} (f : Y ⟶ X) (P : Mori.PrimeDivisor Y) (a : ℝ) : Prop :=
  ∃ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (hp : IsProper f),
    IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp).valuation a

/-- A *bad* triple `(P, Q, W)`: `P ≠ Q` configuration divisors, `W` a component of `P ∩ Q`, and
log discrepancies of `P` and `Q` with sum `< 2`. -/
private def IsBad {Y : Scheme.{u}} (f : Y ⟶ X)
    (t : Mori.PrimeDivisor Y × Mori.PrimeDivisor Y × Set Y) : Prop :=
  (t.1.support : Set Y) ⊆ cfg D f ∧ (t.2.1.support : Set Y) ⊆ cfg D f ∧ t.1 ≠ t.2.1 ∧
    t.2.2 ∈ Resolution.componentsOf (t.1.support ∩ t.2.1.support : Set Y) ∧
    ∃ a b, IsLD sX n K D f t.1 a ∧ IsLD sX n K D f t.2.1 b ∧ a + b < 2

/-- The invariant of the blow-up procedure: a Kollár–Mori log resolution together with weights
`w ≥ 1` on the configuration divisors bounding their log discrepancies below by `c · w`. -/
private structure Good (c : ℝ) {Y : Scheme.{u}} (f : Y ⟶ X) (w : Mori.PrimeDivisor Y → ℕ) :
    Prop where
  log : Mori.IsLogResolution sX D f
  weight : ∀ P : Mori.PrimeDivisor Y, (P.support : Set Y) ⊆ cfg D f →
    1 ≤ w P ∧ ∀ a, IsLD sX n K D f P a → c * w P ≤ a

open Classical in
/-- The multiset of the numbers `N - (w P + w Q)` over the bad triples `(P, Q, W)`. -/
private noncomputable def measure (N : ℕ) {Y : Scheme.{u}} (f : Y ⟶ X)
    (w : Mori.PrimeDivisor Y → ℕ) : Multiset ℕ :=
  if h : (setOf (IsBad sX n K D f)).Finite then
    h.toFinset.val.map fun t => N - (w t.1 + w t.2.1)
  else 0

end Setup

section Helpers

open MMP.Fourfold.SNCWeight

/-! ### Prime divisors and closed sets -/

/-- The generic point of a prime divisor lies on it. -/
private theorem genericPoint_mem_support {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y) :
    P.genericPoint ∈ (P.support : Set Y) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The generic point of a prime divisor specializes to exactly the points of its support. -/
private theorem genericPoint_specializes_iff {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y) {y : Y} :
    P.genericPoint ⤳ y ↔ y ∈ (P.support : Set Y) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact specializes_iff_mem_closure

/-- A prime divisor lies in a closed set exactly when its generic point does. -/
private theorem support_subset_iff {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y) {T : Set Y}
    (hT : IsClosed T) : (P.support : Set Y) ⊆ T ↔ P.genericPoint ∈ T := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨fun h => h (subset_closure rfl),
    fun h => closure_minimal (Set.singleton_subset_iff.mpr h) hT⟩

/-- The prime divisors contained in `⋃_{E ∈ s} E` are the members of `s`. -/
private theorem support_subset_iUnion_iff {Y : Scheme.{u}} {s : Finset (Mori.PrimeDivisor Y)}
    {P : Mori.PrimeDivisor Y} :
    (P.support : Set Y) ⊆ ⋃ E ∈ s, (E.support : Set Y) ↔ P ∈ s :=
  ⟨fun h => by
    obtain ⟨E, hE, hPE⟩ := PrimeDivisorUnion.exists_subset_of_isIrreducible
      (fun E _ => PrimeDivisorUnion.isClosed_support E)
      (PrimeDivisorUnion.isIrreducible_support P) h
    rwa [PrimeDivisorUnion.eq_of_support_subset hPE], fun h => Set.subset_biUnion_of_mem
    (u := fun E : Mori.PrimeDivisor Y => (E.support : Set Y)) h⟩

/-- The support of `∑_{E ∈ s} E` is `s`. -/
private theorem support_sum_single {Y : Scheme.{u}} (s : Finset (Mori.PrimeDivisor Y)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support = s := by
  classical
  ext P
  simp [Finsupp.mem_support_iff, Finsupp.finset_sum_apply, Finsupp.single_apply]

/-- The valuation of a prime divisor `P` of `X`, viewed as a divisor over `X`, is `ord_P`. -/
private theorem valuation_ofPrimeDivisor {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation :=
  Valuation.ext fun φ => by
    change P.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (D : RDivisor X)

/-- The configuration of a Kollár–Mori log resolution is a finite union of prime divisors whose
reduced sum is snc. -/
private theorem exists_finset_cfg {Y : Scheme.{u}} {f : Y ⟶ X}
    (hlog : Mori.IsLogResolution sX D f) :
    ∃ s : Finset (Mori.PrimeDivisor Y), (⋃ E ∈ s, (E.support : Set Y)) = cfg D f ∧
      (MMP.Intersection.reducedDivisorOf s).IsSNC (f ≫ sX) := by
  classical
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, ?_⟩
    · change _ = ((Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous :
        Closeds Y) : Set Y)
      rw [h]
      simp
    · haveI := hlog.isSmoothScheme.smooth
      rw [DivisorWithCoeffs.isSNC_iff_of_support_eq (D' := (0 : Divisor Y))
        (by rw [MMP.Intersection.support_reducedDivisorOf]; rfl)]
      exact DivisorWithCoeffs.isSNC_zero _
  · exact ⟨s, hs, (DivisorWithCoeffs.isSNC_iff_of_support_eq
      ((MMP.Intersection.support_reducedDivisorOf s).trans
        (support_sum_single s).symm)).mpr hsnc⟩

/-! ### Transforms of prime divisors under `f⁻¹` -/

/-- A partial isomorphism representing the rational map of `f` agrees with `f` on its source. -/
private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
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

/-- The transform of a prime divisor `P` under a rational map defined at its generic point is the
closure of the image of that generic point. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X)
    (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint_mem_support P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := (genericPoint_specializes_iff P).mpr hq
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · exact Set.singleton_subset_iff.mpr ⟨⟨P.genericPoint, hP⟩, genericPoint_mem_support P, rfl⟩

/-- A rational map defined at the generic point of `P` and sending it to the generic point of `E`
transforms `P` into `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties, the transform of a prime
divisor `P` of `X` under `f⁻¹` is the prime divisor `E` of `Y` with `f(η_E) = η_P`. -/
private theorem transformPrimeDivisor_inverse_eq_some {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : Mori.PrimeDivisor X) (E : Mori.PrimeDivisor Y)
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsDominant f := hf.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  set g := MMP.Mori.RationalMap.IsBirational.inverse hf with hg_def
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY.1 hf
    have h2 := le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- **Valuative criterion at a divisor.** A proper birational morphism `f : Y ⟶ X` onto a normal
scheme is an isomorphism of local rings over the generic point of each prime divisor `Q` of `X`. -/
private theorem exists_primeDivisor_isIso_stalkMap {Y X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirationalMorphism f) (Q : Mori.PrimeDivisor X) :
    ∃ E : Mori.PrimeDivisor Y,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso {Y X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (E : Mori.PrimeDivisor Y) (Q : Mori.PrimeDivisor X)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- Outside `Ex(f)`, a prime divisor lies over a prime divisor with the same valuation. -/
private theorem exists_valuationOver_eq {Y X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (P : Mori.PrimeDivisor Y) (hP : P.genericPoint ∉ (Mori.exceptionalSet f : Set Y)) :
    ∃ Γ : Mori.PrimeDivisor X, f P.genericPoint = Γ.genericPoint ∧
      P.valuationOver f = Γ.divisorialValuation := by
  have hb : f P.genericPoint ∈ Mori.biregularLocus f := not_not.mp hP
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm, ?_⟩
  have := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hb
  exact valuationOver_eq_of_isIso f P _
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm

end Helpers

section Configuration

open MMP.Fourfold.SNCWeight

/-- If `d + c = n`, then `d + 2 ≤ n` exactly when `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h
    rw [← WithBot.coe_natCast, ← h, ← WithBot.coe_ofNat, ← WithBot.coe_add, WithBot.coe_le_coe,
      add_comm d, add_comm d]
    exact ENat.add_le_add_iff_right fun hd => by simp [hd] at h

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- A divisor over `X` is exceptional exactly when its center has codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX) :
    E.IsExceptional ↔ 2 ≤ Order.coheight (E.f E.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [E.center_eq_toDivisorOver_center, E.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (E.f E.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

variable [IsLocallyNoetherian X] [IsNormal X]

/-- A prime divisor of `Y` is exceptional over `X` exactly when its generic point lies in the
exceptional set. -/
private theorem isExceptionalPrimeDivisor_iff (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} {f : Y ⟶ X} [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (P : Mori.PrimeDivisor Y) :
    IsExceptionalPrimeDivisor sX f P ↔ P.genericPoint ∈ (Mori.exceptionalSet f : Set Y) := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  constructor
  · rintro ⟨hY', hf', hp', hE⟩
    have h2 := (isExceptional_iff_two_le_coheight hn _).mp hE
    by_contra hmem
    have hb : f P.genericPoint ∈ Mori.biregularLocus f := not_not.mp hmem
    change 2 ≤ Order.coheight (f P.genericPoint) at h2
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  · intro hmem
    refine ⟨hY, hf, inferInstance, (isExceptional_iff_two_le_coheight hn _).mpr ?_⟩
    change 2 ≤ Order.coheight (f P.genericPoint)
    by_contra hlt
    apply Mori.mem_exceptionalSet.mp hmem
    refine MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX f hY.1 hf ?_
    rw [ringKrullDim_stalk_eq_coheight]
    have : Order.coheight (f P.genericPoint) ≤ 1 := by
      by_contra h1
      exact hlt (Order.add_one_le_of_lt (not_le.mp h1))
    exact_mod_cast this

/-- Off the exceptional set, a prime divisor has nonzero coefficient in `f⁻¹_* D` exactly when it
lies over `Supp D`. -/
private theorem coeff_birationalInverseTransform_ne_zero_iff (hX : IsNormalVariety k sX)
    (D : RDivisor X) {Y : Scheme.{u}} {f : Y ⟶ X} [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : Mori.PrimeDivisor Y)
    (hP : P.genericPoint ∉ (Mori.exceptionalSet f : Set Y)) :
    (birationalInverseTransform f hf D).coeff P ≠ 0 ↔
      f P.genericPoint ∈ (DivisorWithCoeffs.supp D : Set X) := by
  haveI := hY.1.toIsIntegral
  haveI := hY.2
  haveI : IsLocallyNoetherian Y := hY.1.toLocallyOfFiniteType.isLocallyNoetherian
  have hb : f P.genericPoint ∈ Mori.biregularLocus f := not_not.mp hP
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb, P.coheight_genericPoint]
  set Γ : Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hΓ : f P.genericPoint = Γ.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
  have htr := transformPrimeDivisor_inverse_eq_some hX f hY hf Γ P hΓ
  have huniq : ∀ Γ', MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hf) Γ' = some P → Γ' = Γ := by
    intro Γ' h'
    obtain ⟨P', hP', -⟩ := exists_primeDivisor_isIso_stalkMap f hf Γ'
    have h'' := transformPrimeDivisor_inverse_eq_some hX f hY hf Γ' P' hP'
    rw [h'] at h''
    obtain rfl := Option.some.inj h''
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP'.symm.trans hΓ)
  have hc : (birationalInverseTransform f hf D).coeff P = D.coeff Γ :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr huniq D
  rw [hc, hΓ]
  constructor
  · intro h
    exact DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, h, genericPoint_mem_support Γ⟩
  · intro h
    obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    rwa [PrimeDivisorUnion.eq_of_support_subset
      ((support_subset_iff _ (PrimeDivisorUnion.isClosed_support _)).mpr hmem)]

/-- The exceptional set `MMP.Flips.exceptionalSet f` is contained in `Mori.exceptionalSet f`, the
complement of the preimage of the biregular locus. -/
private theorem flipsExceptionalSet_subset_exceptionalSet {Y : Scheme.{u}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hmem
  apply hy
  haveI : IsIso (f ∣_ Mori.biregularLocus f) := Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ Mori.biregularLocus f, not_not.mp hmem, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- An exceptional prime divisor lies in the exceptional set. -/
private theorem support_subset_flipsExceptionalSet [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) {Y : Scheme.{u}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y}
    (hP : IsExceptionalPrimeDivisor sX f P) :
    (P.support : Set Y) ⊆ MMP.Flips.exceptionalSet f := by
  intro y hy hV
  obtain ⟨V, hyV, hV⟩ := hV
  have hsp : P.genericPoint ⤳ y := (genericPoint_specializes_iff P).mpr hy
  have hηV : P.genericPoint ∈ V := hsp.mem_open V.isOpen hyV
  have hη : P.genericPoint ∉ MMP.Flips.exceptionalSet f := fun h => h ⟨V, hηV, hV⟩
  obtain ⟨hY', hf', hp', hE⟩ := hP
  have h2 := (isExceptional_iff_two_le_coheight hn _).mp hE
  change 2 ≤ Order.coheight (f P.genericPoint) at h2
  rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hη, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

end Configuration

section Exceptional

/-- If `a ≫ b` is an isomorphism, `a` is dominant, the source of `b` is reduced and `b` is
separated, then `b` is an isomorphism. -/
private lemma isIso_of_isIso_comp {A B V : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ V) [IsIso (a ≫ b)]
    [IsDominant a] [IsReduced B] [IsSeparated b] : IsIso b := by
  refine ⟨⟨inv (a ≫ b) ≫ a, ?_, by simp⟩⟩
  refine ext_of_isDominant_of_isSeparated b ?_ a ?_
  · simp
  · rw [← Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id]

/-- If `h ≫ g` is an isomorphism over `V`, with `h` dominant, `X'` reduced and `g` separated,
then `g` is an isomorphism over `V` and `h` over `g⁻¹(V)`. -/
private lemma isBiregular_of_isBiregular_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] {V : X.Opens}
    (hV : IsBiregular (h ≫ g) V) : IsBiregular g V ∧ IsBiregular h (g ⁻¹ᵁ V) := by
  unfold IsBiregular at hV ⊢
  rw [morphismRestrict_comp] at hV
  have : IsDominant (h ∣_ g ⁻¹ᵁ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant h› _
  have : IsSeparated (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› _
  have := @isIso_of_isIso_comp _ _ _ (h ∣_ g ⁻¹ᵁ V) (g ∣_ V) hV _ _ _
  exact ⟨this, @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ V) this hV⟩

/-- `Ex(h ≫ g) = Ex(h) ∪ h⁻¹(Ex(g))` when `h` is dominant, `X'` is reduced and `g` is separated
and universally closed. -/
private lemma exceptionalSet_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] [UniversallyClosed g] :
    Mori.exceptionalSet (h ≫ g) =
      Mori.exceptionalSet h ⊔ (Mori.exceptionalSet g).preimage h.continuous := by
  apply SetLike.coe_injective
  ext y
  change y ∈ Mori.exceptionalSet (h ≫ g) ↔ y ∈ Mori.exceptionalSet h ∨
    h y ∈ Mori.exceptionalSet g
  simp only [Mori.mem_exceptionalSet]
  constructor
  · intro hy
    by_contra hne
    push Not at hne
    obtain ⟨hyh, hyg⟩ := hne
    apply hy
    have hcl : IsClosed (g '' (biregularLocus h : Set X')ᶜ) :=
      g.isClosedMap _ (biregularLocus h).isOpen.isClosed_compl
    let W : X.Opens := biregularLocus g ⊓ ⟨_, hcl.isOpen_compl⟩
    have hWg : IsBiregular g W :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have hWh : IsBiregular h (g ⁻¹ᵁ W) := by
      refine isBiregular_iff_le_biregularLocus.mpr ?_
      intro x hx
      by_contra hxU
      exact hx.2 ⟨x, hxU, rfl⟩
    have hiso : IsBiregular (h ≫ g) W := by
      unfold IsBiregular at *
      rw [morphismRestrict_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hWh hWg
    refine le_biregularLocus hiso ⟨hyg, ?_⟩
    rintro ⟨x, hx, hxy⟩
    have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
    have hxy' : g x = g (h y) := hxy.trans (Scheme.Hom.comp_apply h g y)
    have hx' : g x ∈ biregularLocus g := hxy' ▸ hyg
    have hinj := (g ∣_ biregularLocus g).isOpenEmbedding.injective
      (a₁ := (⟨x, hx'⟩ : g ⁻¹ᵁ biregularLocus g)) (a₂ := ⟨h y, hyg⟩)
    have : x = h y := congrArg Subtype.val (hinj (Subtype.ext
      ((morphismRestrict_base_coe g _ _).trans (hxy'.trans
        (morphismRestrict_base_coe g (biregularLocus g) ⟨h y, hyg⟩).symm))))
    exact hx (this ▸ hyh)
  · intro hy hmem
    have hb := isBiregular_of_isBiregular_comp h g (isBiregular_biregularLocus (h ≫ g))
    rcases hy with hy | hy
    · exact hy (le_biregularLocus hb.2 hmem)
    · exact hy (le_biregularLocus hb.1 hmem)

end Exceptional

section Combinatorics

/-- **The Dershowitz–Manna step.** Let `φ` send the elements of `B` satisfying `p` injectively,
with the same key, into `A ∖ {a₀}`, and let every other element of `B` have key less than that of
`a₀ ∈ A`. Then the multiset of keys of `B` is smaller than that of `A` in the Dershowitz–Manna
order. -/
private theorem isDershowitzMannaLT_map {α β : Type*} [DecidableEq α] (A : Finset α)
    (B : Finset β) (key : α → ℕ) (key' : β → ℕ) (p : β → Prop) [DecidablePred p] (φ : β → α)
    (hφ : ∀ b ∈ B, p b → φ b ∈ A)
    (hinj : ∀ b ∈ B, ∀ b' ∈ B, p b → p b' → φ b = φ b' → b = b')
    (hkey : ∀ b ∈ B, p b → key (φ b) = key' b) (a₀ : α) (ha₀ : a₀ ∈ A)
    (ha₀' : ∀ b ∈ B, p b → φ b ≠ a₀) (hlt : ∀ b ∈ B, ¬ p b → key' b < key a₀) :
    Multiset.IsDershowitzMannaLT (B.val.map key') (A.val.map key) := by
  set B₁ := B.filter p with hB₁
  set B₂ := B.filter (fun b => ¬ p b) with hB₂
  set A₁ := B₁.image φ with hA₁def
  have hA₁ : A₁ ⊆ A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter] at hb
    exact hφ b hb.1 hb.2
  have ha₀Z : a₀ ∈ A.filter (· ∉ A₁) := by
    refine Finset.mem_filter.mpr ⟨ha₀, fun h => ?_⟩
    obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp h
    rw [Finset.mem_filter] at hb
    exact ha₀' b hb.1 hb.2 hb'
  refine ⟨A₁.val.map key, B₂.val.map key', (A.filter (· ∉ A₁)).val.map key, ?_, ?_, ?_, ?_⟩
  · intro h0
    have h1 : key a₀ ∈ (A.filter (· ∉ A₁)).val.map key :=
      Multiset.mem_map_of_mem _ (Finset.mem_val.mpr ha₀Z)
    rw [h0] at h1
    exact Multiset.notMem_zero _ h1
  · have h1 : B.val = B₁.val + B₂.val := by
      rw [hB₁, hB₂, Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]
    have hinj' : Set.InjOn φ (B₁ : Set β) := by
      intro b hb b' hb' h
      rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
      exact hinj b hb.1 b' hb'.1 hb.2 hb'.2 h
    have h2 : A₁.val.map key = B₁.val.map key' := by
      rw [hA₁def, Finset.image_val_of_injOn hinj', Multiset.map_map]
      refine Multiset.map_congr rfl fun b hb => ?_
      rw [Finset.mem_val, Finset.mem_filter] at hb
      exact hkey b hb.1 hb.2
    rw [h1, Multiset.map_add, h2]
  · have h1 : A.val = (A.filter (· ∈ A₁)).val + (A.filter (· ∉ A₁)).val := by
      rw [Finset.filter_val, Finset.filter_val, Multiset.filter_add_not]
    have h2 : A.filter (· ∈ A₁) = A₁ := by
      ext a
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun h => hA₁ h
    rw [h1, Multiset.map_add, h2]
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hy
    rw [Finset.mem_val, Finset.mem_filter] at hb
    exact ⟨key a₀, Multiset.mem_map_of_mem _ (Finset.mem_val.mpr ha₀Z), hlt b hb.1 hb.2⟩

end Combinatorics

section Main

open MMP.Fourfold.SNCWeight

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {n : ℕ} {K : Divisor X} {D : RDivisor X}

omit [CharZero k] in
/-- Log discrepancies over a klt pair are positive. -/
private theorem IsLD.pos (hklt : IsKawamataLogTerminal sX n K D) {Y : Scheme.{u}} {f : Y ⟶ X}
    {P : Mori.PrimeDivisor Y} {a : ℝ} (h : IsLD sX n K D f P a) : 0 < a := by
  obtain ⟨hY, hf, hp, b, hb, rfl⟩ := h
  exact hklt.2.2.2 _ hb.2.2.1 _ ⟨b, hb, rfl⟩

/-- Log discrepancies are unique. -/
private theorem IsLD.eq {Y : Scheme.{u}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y} {a a' : ℝ}
    (h : IsLD sX n K D f P a) (h' : IsLD sX n K D f P a') : a = a' := by
  obtain ⟨hY, hf, hp, b, hb, rfl⟩ := h
  obtain ⟨hY', hf', hp', b', hb', rfl⟩ := h'
  rw [IsDiscrepancy.eq hb hb']

omit [CharZero k] in
/-- The reduced sum of the configuration is an snc divisor in the sense of FA. -/
private theorem isSNCDivisor_reducedDivisorOf {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {s : Finset (Mori.PrimeDivisor Y)} (hsnc : (MMP.Intersection.reducedDivisorOf s).IsSNC sY) :
    IsSNCDivisor sY (MMP.Intersection.reducedDivisorOf s) := by
  refine ⟨MMP.Intersection.isReducedEffective_reducedDivisorOf s, fun P hP => hsnc.1 P hP,
    fun p _ => ?_⟩
  obtain ⟨m, z, j, hz, hj, hI⟩ := hsnc.2 p
  exact ⟨m, z, j, hz, hj, hI⟩

/-- On a smooth birational model `f : Y ⟶ X`, the pull-back `f^*ω` of a rational `n`-form with
canonical divisor `div ω` has canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback (hX : IsNormalVariety k sX)
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have hn := hK.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm.trans hn)
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
        hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0)

/-- **Discrepancies of the prime divisors of a smooth model.** If `f : Y ⟶ X` is a smooth
birational model and `div(f^*ω) + D_Y = f^*(div ω + D)`, then every prime divisor `R` of `Y` has
discrepancy `a(R, X, D) = -coeff_R D_Y`. -/
private theorem isDiscrepancy_valuationOver (hX : IsNormalVariety k sX)
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + D)) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X} [IsProper f]
    [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) {DY : RDivisor Y}
    (hpb : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + DY))
    (R : Mori.PrimeDivisor Y) :
    IsDiscrepancy sX n (divisorOfForm ω) D (R.valuationOver f) (-DY.coeff R) := by
  have hKY := isCanonicalDivisor_divisorOfForm_pullback hX hω0 hK hY hf hYsm
  have hKDY : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX f ω)) + DY) := by
    obtain ⟨m, r, L₀, L, hLc, -, hL, heq⟩ := hpb
    exact ⟨m, r, L, fun j => (hL j).2.isCartier (hLc j), by
      rw [heq]; simp only [toRDivisor_eq_mapCoeffs]⟩
  let ER : ProperDivisorOver k (f ≫ sX) :=
    ⟨DivisorOver.ofPrimeDivisor k hY R, (inferInstance : IsProper (𝟙 Y))⟩
  have hER : ER.valuation = R.divisorialValuation := valuation_ofPrimeDivisor hY R
  have h1 := isDiscrepancy_divisorialValuation hY _
    (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
      hf.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hK.topologicalKrullDim_eq) hω0)
    hKY hKDY R
  rw [← hER] at h1
  have h2 := (isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hY hf hpb hKY ER _).mpr h1
  rwa [hER] at h2

/-- **The log discrepancy of a divisor over a stratum.** Let `f : Y ⟶ X` be a log resolution with
configuration `∑ H_k`, and `ν` a divisor over `Y` whose center lies in `P ∩ Q` for two distinct
configuration divisors. Then `a_ℓ(P) + a_ℓ(Q) ≤ a_ℓ(ν)` over `(X, D)`: on `Y`, with the crepant
boundary `D_Y = ∑ (1 - a_ℓ(H_k)) H_k`, the snc log discrepancy formula gives
`a_ℓ(ν) = l + ∑ n_k a_ℓ(H_k)` with `n_P, n_Q ≥ 1`. -/
private theorem add_le_of_isLogDiscrepancy (hklt : IsKawamataLogTerminal sX n K D)
    {Y : Scheme.{u}} [IsIntegral Y] {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f)
    [IsDominant f] {P Q : Mori.PrimeDivisor Y} (hP : (P.support : Set Y) ⊆ cfg D f)
    (hQ : (Q.support : Set Y) ⊆ cfg D f) (hPQ : P ≠ Q)
    (ν : ProperDivisorOver k (f ≫ sX)) (hνP : (ν.center : Set Y) ⊆ P.support)
    (hνQ : (ν.center : Set Y) ⊆ Q.support) {b aP aQ : ℝ}
    (hb : IsLogDiscrepancy sX n K D (ν.valuation.comap (functionFieldMap f)) b)
    (haP : IsLD sX n K D f P aP) (haQ : IsLD sX n K D f Q aQ) : aP + aQ ≤ b := by
  classical
  have hX : IsNormalVariety k sX := hklt.1.isNormalVariety
  obtain ⟨hYnv, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  haveI := hYnv.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hYnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYnv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : Mori.IsVariety k (f ≫ sX) := hYnv.1
  obtain ⟨s, hs, hsnc⟩ := exists_finset_cfg sX D hlog
  have hPs : P ∈ s := support_subset_iUnion_iff.mp (hs ▸ hP)
  have hQs : Q ∈ s := support_subset_iUnion_iff.mp (hs ▸ hQ)
  -- the form and the presentation
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨hK, hKD, _, E₀, ω, m, r, L, _, hωK, hw⟩ := id ha
  obtain ⟨_, _, hω0, hLc, hsum, _⟩ := hw
  subst hωK
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant f (hLc j)
  set ωY := pullbackRationalPluriForms sX f ω
  set DY : RDivisor Y := ∑ j, r j • Divisor.toRDivisor (L' j) -
    Divisor.toRDivisor (divisorOfForm ωY) with hDY
  have hDYsum : Divisor.toRDivisor (divisorOfForm ωY) + DY =
      ∑ j, r j • Divisor.toRDivisor (L' j) := by
    rw [hDY]; abel
  have hpb : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L, L', hLc, hsum, fun j => ⟨_, hL' j⟩, hDYsum⟩
  have hKY := isCanonicalDivisor_divisorOfForm_pullback hX hω0 hK hYnv hfb hlog.isSmoothScheme
  have hcrep := isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hYnv hfb hpb hKY
  have hprime := isDiscrepancy_valuationOver hX hω0 hK hKD hYnv hfb hlog.isSmoothScheme hpb
  have hIsLD : ∀ R : Mori.PrimeDivisor Y,
      IsLD sX n (divisorOfForm ω) D f R (1 - DY.coeff R) :=
    fun R => ⟨hYnv, hfb, inferInstance, -DY.coeff R, hprime R, by ring⟩
  have hpos : ∀ R ∈ s, 0 ≤ 1 - DY.coeff R := fun R _ => (IsLD.pos hklt (hIsLD R)).le
  have hP1 : aP = 1 - DY.coeff P := IsLD.eq haP (hIsLD P)
  have hQ1 : aQ = 1 - DY.coeff Q := IsLD.eq haQ (hIsLD Q)
  -- the crepant boundary is supported on the configuration
  have hBS : ∀ R : Mori.PrimeDivisor Y, DY.coeff R ≠ 0 →
      R ∈ (MMP.Intersection.reducedDivisorOf s).support := by
    intro R hR
    rw [MMP.Intersection.support_reducedDivisorOf]
    by_contra hRs
    apply hR
    have hRc : ¬ (R.support : Set Y) ⊆ cfg D f := fun h =>
      hRs (support_subset_iUnion_iff.mp (hs ▸ h))
    rw [support_subset_iff R (cfg D f).isClosed] at hRc
    simp only [cfg, Closeds.coe_sup, Set.mem_union, Closeds.coe_preimage, Set.mem_preimage,
      not_or] at hRc
    obtain ⟨hRex, hRD⟩ := hRc
    obtain ⟨Γ, hΓ, hval⟩ := exists_valuationOver_eq f R hRex
    have h1 := hprime R
    rw [hval] at h1
    have h2 := IsDiscrepancy.eq_neg_coeff h1
    have hΓ0 : D.coeff Γ = 0 := by
      by_contra h0
      exact hRD (hΓ ▸ DivisorWithCoeffs.mem_supp_iff.mpr ⟨Γ, h0, genericPoint_mem_support Γ⟩)
    linarith
  obtain ⟨l, nn, hbeq, -, hn0, -, -⟩ :=
    exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor (f ≫ sX) hYnv.1 hlog.isSmoothScheme
      (isSNCDivisor_reducedDivisorOf hsnc) hBS ν (b := 1 + a) ⟨a, (hcrep ν a).mp ha, rfl⟩
  rw [MMP.Intersection.support_reducedDivisorOf] at hbeq hn0
  have hnP : (1 : ℝ) ≤ nn P := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => ((hn0 P hPs).mp h) hνP
  have hnQ : (1 : ℝ) ≤ nn Q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => ((hn0 Q hQs).mp h) hνQ
  have hsub : ({P, Q} : Finset (Mori.PrimeDivisor Y)) ⊆ s :=
    Finset.insert_subset hPs (Finset.singleton_subset_iff.mpr hQs)
  have hle : ∑ R ∈ ({P, Q} : Finset (Mori.PrimeDivisor Y)), (nn R : ℝ) * (1 - DY.coeff R) ≤
      ∑ R ∈ s, (nn R : ℝ) * (1 - DY.coeff R) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun R hR _ =>
      mul_nonneg (Nat.cast_nonneg _) (hpos R hR)
  rw [Finset.sum_pair hPQ] at hle
  have h1 := mul_le_mul_of_nonneg_right hnP (hpos P hPs)
  have h2 := mul_le_mul_of_nonneg_right hnQ (hpos Q hQs)
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  rw [hP1, hQ1, hbeq]
  linarith

omit [CharZero k] in
/-- The components of an snc divisor form an snc family. -/
private theorem isSNCFamily_idealSheaf_of_isSNC {Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of k)} {R : Type*} [Zero R] {T : MMP.Mori.DivisorWithCoeffs R Y}
    (hT : T.IsSNC g) : Resolution.IsSNCFamily g (fun E : T.support => E.1.idealSheaf) := by
  refine ⟨fun E => ⟨?_, PrimeDivisorUnion.isPureCodimOne_support E.1, hT.1 E.1 E.2⟩,
    fun x => ?_⟩
  · haveI := E.1.integral
    infer_instance
  · obtain ⟨m, z, j, hz, hj, hI⟩ := hT.2 x
    refine ⟨m, z, fun E => j ⟨E.1.1, E.1.2, E.2⟩, hz, fun E => hI ⟨E.1.1, E.1.2, E.2⟩,
      fun E E' h => ?_⟩
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj (hj h)))

omit [CharZero k] in
open PrimeDivisorUnion StratumBlowup SNCBlowup MMP.Threefold.Resolution in
/-- The exceptional set of the blow-up of a smooth centre of codimension two is the preimage of
the centre. -/
private theorem coe_exceptionalSet_blowUpToBase {Y : Scheme.{u}} [IsIntegral Y]
    {sY : Y ⟶ Spec (.of k)} {I : Y.IdealSheafData} (h : Resolution.IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc2 : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) = 2) :
    (Mori.exceptionalSet (blowUpToBase I) : Set (blowUp I)) = blowUpToBase I ⁻¹' I.support := by
  have hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    norm_num [hc2]
  ext x
  constructor
  · intro hx
    by_contra hxI
    exact Mori.mem_exceptionalSet.mp hx (mem_biregularLocus_of_notMem I hxI)
  · intro hxI
    refine Mori.mem_exceptionalSet.mpr fun hb => ?_
    set E := excE sY h hirr hc
    have hxE : x ∈ (E.support : Set (blowUp I)) := by rwa [coe_support_excE]
    have hsp : E.genericPoint ⤳ x := (genericPoint_specializes_iff E).mpr hxE
    have hηb : blowUpToBase I E.genericPoint ∈ Mori.biregularLocus (blowUpToBase I) :=
      (hsp.map (blowUpToBase I).continuous).mem_open (Mori.biregularLocus _).isOpen hb
    have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus (blowUpToBase I) hηb
    rw [E.coheight_genericPoint] at h1
    have hcl := BlowupCrepancy.closure_map_genericPoint_excE sY h hirr hc
    have heq : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) =
        IrreducibleCloseds.closureSingleton (blowUpToBase I E.genericPoint) :=
      IrreducibleCloseds.ext hcl.symm
    rw [heq, MMP.Flips.codimension_closureSingleton, h1] at hc2
    exact absurd hc2 (by decide)

open PrimeDivisorUnion StratumBlowup SNCBlowup MMP.Threefold.Resolution in
/-- **One blow-up.** Blowing up a component `W` of `P ∩ Q`, for distinct configuration divisors
`P` and `Q` of a log resolution `f : Y ⟶ X`, gives a log resolution `π ≫ f` whose configuration
divisors are the exceptional divisor `E` and the strict transforms `st G` of the configuration
divisors of `f`. The strict transforms keep their log discrepancies, `E` has log discrepancy at
least `a_ℓ(P) + a_ℓ(Q)`, and every component of `st G₁ ∩ st G₂` is the strict transform of a
component `V ≠ W` of `G₁ ∩ G₂`. -/
private theorem exists_blowup (hklt : IsKawamataLogTerminal sX n K D) {Y : Scheme.{u}}
    [IsIntegral Y] {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f) {P Q : Mori.PrimeDivisor Y}
    (hP : (P.support : Set Y) ⊆ cfg D f) (hQ : (Q.support : Set Y) ⊆ cfg D f) (hPQ : P ≠ Q)
    {W : Set Y} (hW : W ∈ Resolution.componentsOf (P.support ∩ Q.support : Set Y))
    {aP aQ : ℝ} (haP : IsLD sX n K D f P aP) (haQ : IsLD sX n K D f Q aQ) :
    ∃ (Y' : Scheme.{u}) (π : Y' ⟶ Y) (E : Mori.PrimeDivisor Y')
      (st : Mori.PrimeDivisor Y → Mori.PrimeDivisor Y'),
      Mori.IsLogResolution sX D (π ≫ f) ∧
      (∀ R : Mori.PrimeDivisor Y', (R.support : Set Y') ⊆ cfg D (π ≫ f) ↔
        R = E ∨ ∃ G : Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ cfg D f ∧ st G = R) ∧
      (∀ G, st G ≠ E) ∧ Function.Injective st ∧
      (∀ G a, IsLD sX n K D (π ≫ f) (st G) a ↔ IsLD sX n K D f G a) ∧
      (∀ b, IsLD sX n K D (π ≫ f) E b → aP + aQ ≤ b) ∧
      (∀ G₁ G₂ : Mori.PrimeDivisor Y, (G₁.support : Set Y) ⊆ cfg D f →
        (G₂.support : Set Y) ⊆ cfg D f → G₁ ≠ G₂ →
        ∀ C ∈ Resolution.componentsOf ((st G₁).support ∩ (st G₂).support : Set Y'),
          ∃ V ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y), V ≠ W ∧
            C = closure (π ⁻¹' (V \ W))) := by
  classical
  have hX : IsNormalVariety k sX := hklt.1.isNormalVariety
  obtain ⟨hYnv, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  haveI := hYnv.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hYnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYnv.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : Smooth (f ≫ sX) := hlog.isSmoothScheme.smooth
  haveI : IsDominant f := hfb.isDominant
  obtain ⟨s, hs, hsnc⟩ := exists_finset_cfg sX D hlog
  set T := MMP.Intersection.reducedDivisorOf s
  have hTs : T.support = s := MMP.Intersection.support_reducedDivisorOf s
  have hcfgT : ∀ G : Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ cfg D f ↔ G ∈ T.support := by
    intro G
    rw [hTs, ← hs]
    exact support_subset_iUnion_iff
  have hPT : P ∈ T.support := (hcfgT P).mp hP
  have hQT : Q ∈ T.support := (hcfgT Q).mp hQ
  have hWcl : IsClosed W := Resolution.Aux.isClosed_of_mem_componentsOf
    ((isClosed_support P).inter (isClosed_support Q)) hW
  -- the centre
  obtain ⟨I, hirr, hIsm, hWI, hIsub, hIst, -, hIv⟩ := exists_centre (f ≫ sX) hsnc hPT hQT hPQ
    hW.1.1.2.isPreconnected hW.1.1.1
    (hW.1.2.trans Set.inter_subset_left)
    (hW.1.2.trans Set.inter_subset_right)
  have hIW : (I.support : Set Y) = W := (hW.2 ⟨hirr, hIsub⟩ hWI).antisymm hWI
  -- the snc family of the configuration, and the classification of double intersections
  let H : T.support → Y.IdealSheafData := fun E => E.1.idealSheaf
  have hH : Resolution.IsSNCFamily (f ≫ sX) H := isSNCFamily_idealSheaf_of_isSNC hsnc
  let i₁ : T.support := ⟨P, hPT⟩
  let i₂ : T.support := ⟨Q, hQT⟩
  have hne : i₁ ≠ i₂ := fun h => hPQ (congrArg Subtype.val h)
  let W' : Resolution.componentsOf ((H i₁).support ∩ (H i₂).support : Set Y) := ⟨W, hW⟩
  have hZ : Resolution.componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W' = I := by
    rw [hIv]
    unfold Resolution.componentsFamily
    congr 1
    ext1
    rw [Closeds.coe_closure]
    exact hWcl.closure_eq.trans hIW.symm
  have hclass := (Resolution.blowUp_snc_pair_stratum (f ≫ sX) H hH hne W').2.2
  subst hZ
  set I := Resolution.componentsFamily ((H i₁).support ∩ (H i₂).support : Set Y) W'
  have hc2 := codimension_centre_eq_two (f ≫ sX) hsnc hPT hQT hPQ hirr hIsm hIsub hIst
  have hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    norm_num [hc2]
  have hbl : Resolution.IsSmoothBlowup (f ≫ sX) I := ⟨hlog.isSmoothScheme, hIsm⟩
  set π := blowUpToBase I
  haveI := isIntegral_blowUp_of_one_le_codimension I hirr hc
  haveI := isDominant_blowUpToBase I hirr hc
  haveI : IsProper π := AlgebraicGeometry.isProper_blowUpToBase (I := I)
  have hπb : IsBirationalMorphism π := isBirationalMorphism_blowUpToBase I hirr hc
  haveI : Smooth (π ≫ f ≫ sX) :=
    (Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup (f ≫ sX) I hbl).1
  have hπsm : IsSmoothScheme (π ≫ f ≫ sX) := Resolution.isSmoothScheme_of_smooth _
  set E := excE (f ≫ sX) hbl hirr hc
  have hGI : ∀ G : Mori.PrimeDivisor Y, G.genericPoint ∉ (I.support : Set Y) :=
    genericPoint_notMem_of_subset_inter I hPQ hIsub
  let st : Mori.PrimeDivisor Y → Mori.PrimeDivisor (blowUp I) := fun G => strictPrime I G (hGI G)
  have hstη : ∀ G, π (st G).genericPoint = G.genericPoint := fun G =>
    map_genericPoint_strictPrime I (hGI G)
  -- the log resolution `π` of `(Y, T)`
  set Δ : RDivisor Y := Divisor.toRDivisor T with hΔ
  have hΔsupp : (DivisorWithCoeffs.supp Δ : Set Y) = ⋃ E ∈ s, (E.support : Set Y) := by
    rw [DivisorWithCoeffs.coe_supp, ← hTs]
    congr 1
    ext P
    simp [hΔ, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
  have hExπ := coe_exceptionalSet_blowUpToBase hbl hirr hc2
  have hnew := iUnion_newPrimes (f ≫ sX) hPQ hIsub hbl hirr hc hPT
  have hIcfg : (I.support : Set Y) ⊆ cfg D f := hIsub.trans (Set.inter_subset_left.trans hP)
  have hπlog : Mori.IsLogResolution (f ≫ sX) Δ π := by
    refine ⟨⟨inferInstance, hπb, hπsm⟩, ?_, Or.inr ⟨newPrimes (f ≫ sX) hPQ hIsub hbl hirr hc T,
      ?_, ?_⟩⟩
    · have : Mori.exceptionalSet π = E.idealSheaf.support :=
        Closeds.ext (hExπ.trans (coe_support_excE (f ≫ sX) hbl hirr hc).symm)
      rw [this]
      exact isPureCodimOne_support E
    · rw [hnew, Closeds.coe_sup, hExπ, Closeds.coe_preimage, hΔsupp, hTs, ← Set.preimage_union]
      congr 1
      refine (Set.union_eq_right.mpr ?_).symm
      exact hIcfg.trans hs.symm.le
    · have := isSNC_newBoundary (f ≫ sX) hPQ hIsub hbl hirr hc hlog.isSmoothScheme hsnc hPT hQT
        hIst
      exact (DivisorWithCoeffs.isSNC_iff_of_support_eq
        ((support_sum_single _).trans
          (MMP.Intersection.support_reducedDivisorOf _).symm)).mpr this
  have hle : Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous ≤
      DivisorWithCoeffs.supp Δ := by
    intro y hy
    change y ∈ (DivisorWithCoeffs.supp Δ : Set Y)
    rw [hΔsupp, hs]
    exact hy
  have hlog' : Mori.IsLogResolution sX D (π ≫ f) := hlog.comp hle hπlog
  obtain ⟨hY'nv, -, -⟩ := hlog'.toIsSmoothResolution.isNormalVariety hX
  -- the configuration of `π ≫ f`
  have hcfg' : ∀ x : blowUp I, x ∈ (cfg D (π ≫ f) : Set (blowUp I)) ↔
      π x ∈ (cfg D f : Set Y) := by
    intro x
    have hEx : x ∈ (Mori.exceptionalSet (π ≫ f) : Set (blowUp I)) ↔
        π x ∈ (I.support : Set Y) ∨ π x ∈ (Mori.exceptionalSet f : Set Y) := by
      rw [exceptionalSet_comp π f]
      change x ∈ (Mori.exceptionalSet π : Set (blowUp I)) ∨
        π x ∈ (Mori.exceptionalSet f : Set Y) ↔ _
      rw [hExπ]
      rfl
    have hI' : π x ∈ (I.support : Set Y) → π x ∈ (cfg D f : Set Y) := fun h => hIcfg h
    simp only [cfg, Closeds.coe_sup, Closeds.coe_preimage, Set.mem_union, Set.mem_preimage,
      Scheme.Hom.comp_apply] at hI' ⊢
    rw [hEx]
    tauto
  have hcfgnew : (cfg D (π ≫ f) : Set (blowUp I)) =
      ⋃ H ∈ newPrimes (f ≫ sX) hPQ hIsub hbl hirr hc T, (H.support : Set (blowUp I)) := by
    rw [hnew]
    ext x
    rw [hcfg' x, hTs, hs]
    rfl
  have hR : ∀ R : Mori.PrimeDivisor (blowUp I), (R.support : Set (blowUp I)) ⊆ cfg D (π ≫ f) ↔
      R = E ∨ ∃ G : Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ cfg D f ∧ st G = R := by
    intro R
    rw [hcfgnew, support_subset_iUnion_iff, mem_newPrimes]
    simp only [hcfgT]
    rfl
  have hstE : ∀ G, st G ≠ E := by
    intro G h
    have h1 : π E.genericPoint ∈ (I.support : Set Y) := by
      have h0 : E.genericPoint ∈ (E.support : Set (blowUp I)) := genericPoint_mem_support E
      rwa [coe_support_excE] at h0
    rw [← h, hstη] at h1
    exact hGI G h1
  have hstinj : Function.Injective st := fun G₁ G₂ h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hstη G₁).symm.trans ((congrArg (fun R => π R.genericPoint) h).trans (hstη G₂)))
  -- valuations
  haveI := hY'nv.2
  haveI : LocallyOfFiniteType ((π ≫ f) ≫ sX) := hY'nv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((π ≫ f) ≫ sX)
  have hval : ∀ G, (st G).valuationOver (π ≫ f) = G.valuationOver f := by
    intro G
    haveI := isIso_stalkMap_of_mem_biregularLocus π (show π (st G).genericPoint ∈ _ from
      (hstη G) ▸ mem_biregularLocus_of_notMem I (hGI G))
    have h1 := valuationOver_eq_of_isIso π (st G) G (hstη G)
    refine Valuation.ext fun g => ?_
    rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply π f g,
      ← Mori.PrimeDivisor.valuationOver_apply (st G) π, h1]
  have hLD : ∀ G a, IsLD sX n K D (π ≫ f) (st G) a ↔ IsLD sX n K D f G a := by
    intro G a
    constructor
    · rintro ⟨h1, h2, h3, h⟩
      refine ⟨hYnv, hfb, inferInstance, ?_⟩
      have hv : (ProperDivisorOver.mk ⟨blowUp I, π ≫ f, h1, h2, st G⟩ h3).valuation =
          (ProperDivisorOver.mk ⟨Y, f, hYnv, hfb, G⟩ inferInstance).valuation := hval G
      rwa [hv] at h
    · rintro ⟨h1, h2, h3, h⟩
      refine ⟨hY'nv, hlog'.isBirationalMorphism, hlog'.isProper, ?_⟩
      have hv : (ProperDivisorOver.mk ⟨blowUp I, π ≫ f, hY'nv, hlog'.isBirationalMorphism, st G⟩
          hlog'.isProper).valuation =
          (ProperDivisorOver.mk ⟨Y, f, h1, h2, G⟩ h3).valuation := hval G
      rwa [hv]
  have hEb : ∀ b, IsLD sX n K D (π ≫ f) E b → aP + aQ ≤ b := by
    rintro b ⟨h1, h2, h3, hb⟩
    have hνnv : IsNormalVariety k (π ≫ f ≫ sX) := by rwa [← Category.assoc]
    let ν : ProperDivisorOver k (f ≫ sX) := ⟨⟨blowUp I, π, hνnv, hπb, E⟩, inferInstance⟩
    have hcen : (ν.center : Set Y) ⊆ I.support := by
      rw [ProperDivisorOver.coe_center]
      change π '' (E.support : Set (blowUp I)) ⊆ _
      rw [coe_support_excE]
      exact Set.image_preimage_subset _ _
    have hνv : ν.valuation.comap (functionFieldMap f) =
        (ProperDivisorOver.mk ⟨blowUp I, π ≫ f, h1, h2, E⟩ h3).valuation := by
      refine Valuation.ext fun g => ?_
      change E.valuationOver π (functionFieldMap f g) = E.valuationOver (π ≫ f) g
      rw [Mori.PrimeDivisor.valuationOver_apply, Mori.PrimeDivisor.valuationOver_apply,
        MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    exact add_le_of_isLogDiscrepancy hklt hlog hP hQ hPQ ν
      (hcen.trans (hIsub.trans Set.inter_subset_left))
      (hcen.trans (hIsub.trans Set.inter_subset_right)) (hνv ▸ hb) haP haQ
  -- components of double intersections of strict transforms
  have hstsupp : ∀ G : Mori.PrimeDivisor Y, ((st G).support : Set (blowUp I)) =
      closure (π ⁻¹' ((G.support : Set Y) \ W)) := by
    intro G
    apply le_antisymm
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ?_)
      rw [Set.mem_preimage, hstη]
      exact ⟨genericPoint_mem_support G, fun h => hGI G (hIW ▸ h)⟩
    · refine closure_minimal ?_ (isClosed_support _)
      rintro x ⟨hxG, hxW⟩
      exact mem_support_strictPrime I (hGI G) (fun h => hxW (hIW ▸ h)) hxG
  have hD : ∀ (G : Mori.PrimeDivisor Y) (hGT : G ∈ T.support),
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (π ⁻¹'
        ((H ⟨G, hGT⟩).support \ (W' : Set Y))))).support : Set (blowUp I)) = (st G).support := by
    intro G hGT
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hstsupp]
  have hpair : ∀ G₁ G₂ : Mori.PrimeDivisor Y, (G₁.support : Set Y) ⊆ cfg D f →
      (G₂.support : Set Y) ⊆ cfg D f → G₁ ≠ G₂ →
      ∀ C ∈ Resolution.componentsOf ((st G₁).support ∩ (st G₂).support : Set (blowUp I)),
        ∃ V ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y), V ≠ W ∧
          C = closure (π ⁻¹' (V \ W)) := by
    intro G₁ G₂ hG₁ hG₂ hG C hC
    have hG₁T := (hcfgT G₁).mp hG₁
    have hG₂T := (hcfgT G₂).mp hG₂
    have hne' : (some ⟨G₁, hG₁T⟩ : Option T.support) ≠ some ⟨G₂, hG₂T⟩ := fun h =>
      hG (congrArg Subtype.val (Option.some.inj h))
    have h3 := hclass (some ⟨G₁, hG₁T⟩) (some ⟨G₂, hG₂T⟩) hne' C
      (by dsimp only; rw [hD G₁ hG₁T, hD G₂ hG₂T]; exact hC)
    rcases h3 with ⟨i, j, hi, hj, V, hV, hVW, hCV⟩ | ⟨j, hj, -⟩
    · obtain rfl := (Option.some.inj hi)
      obtain rfl := (Option.some.inj hj)
      exact ⟨V, hV, hVW, hCV⟩
    · rcases hj with ⟨h, -⟩ | ⟨-, h⟩ <;> cases h
  exact ⟨blowUp I, π, E, st, hlog', hR, hstE, hstinj, hLD, hEb, hpair⟩

omit [CharZero k] in
/-- There are finitely many bad triples. -/
private theorem finite_isBad {Y : Scheme.{u}} {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f) :
    (setOf (IsBad sX n K D f)).Finite := by
  classical
  obtain ⟨s, hs, -⟩ := exists_finset_cfg sX D hlog
  haveI : IsProper f := hlog.isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  haveI : Smooth (f ≫ sX) := hlog.isSmoothScheme.smooth
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNoetherian Y := {}
  refine Set.Finite.subset (s.finite_toSet.biUnion fun P _ => s.finite_toSet.biUnion fun Q _ =>
    (Set.finite_singleton P).prod ((Set.finite_singleton Q).prod
      (Resolution.Aux.finite_and_cover_componentsOf ((PrimeDivisorUnion.isClosed_support P).inter
        (PrimeDivisorUnion.isClosed_support Q))).1)) ?_
  rintro ⟨P, Q, V⟩ ⟨hP, hQ, -, hV, -⟩
  simp only [Set.mem_iUnion]
  exact ⟨P, support_subset_iUnion_iff.mp (hs ▸ hP), Q, support_subset_iUnion_iff.mp (hs ▸ hQ),
    rfl, rfl, hV⟩

/-- One blow-up of a bad component lowers the measure. -/
private theorem exists_good_lt (hklt : IsKawamataLogTerminal sX n K D) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 2 ≤ c * N) {Y : Scheme.{u}} {f : Y ⟶ X} {w : Mori.PrimeDivisor Y → ℕ}
    (hG : Good sX n K D c f w) {t : Mori.PrimeDivisor Y × Mori.PrimeDivisor Y × Set Y}
    (ht : IsBad sX n K D f t) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X) (w' : Mori.PrimeDivisor Y' → ℕ),
      Good sX n K D c f' w' ∧
        Multiset.IsDershowitzMannaLT (measure sX n K D N f' w') (measure sX n K D N f w) := by
  classical
  obtain ⟨P, Q, W⟩ := t
  obtain ⟨hP, hQ, hPQ, hW, aP, aQ, haP, haQ, -⟩ := id ht
  haveI : IsIntegral Y :=
    (hG.log.toIsSmoothResolution.isNormalVariety hklt.1.isNormalVariety).1.1.toIsIntegral
  obtain ⟨Y', π, E, st, hlog', hR, hstE, hstinj, hLD, hEb, hpair⟩ :=
    exists_blowup hklt hG.log hP hQ hPQ hW haP haQ
  -- the new weights
  let w' : Mori.PrimeDivisor Y' → ℕ := fun R =>
    if h : ∃ G, st G = R then w h.choose else w P + w Q
  have hw'st : ∀ G, w' (st G) = w G := by
    intro G
    have h : ∃ G', st G' = st G := ⟨G, rfl⟩
    simp only [w', dif_pos h]
    rw [hstinj h.choose_spec]
  have hw'E : w' E = w P + w Q := by
    simp only [w']
    rw [dif_neg]
    rintro ⟨G, hG⟩
    exact hstE G hG
  have hwP := hG.weight P hP
  have hwQ := hG.weight Q hQ
  have hG' : Good sX n K D c (π ≫ f) w' := by
    refine ⟨hlog', fun R hR' => ?_⟩
    rcases (hR R).mp hR' with rfl | ⟨G, hG₀, rfl⟩
    · refine ⟨by rw [hw'E]; omega, fun b hb => ?_⟩
      rw [hw'E]
      push_cast
      linarith [hEb b hb, hwP.2 aP haP, hwQ.2 aQ haQ]
    · rw [hw'st]
      exact ⟨(hG.weight G hG₀).1, fun a ha => (hG.weight G hG₀).2 a ((hLD G a).mp ha)⟩
  -- badness bounds the weights
  have hbound : ∀ b ∈ (finite_isBad (n := n) (K := K) hlog').toFinset,
      w' b.1 + w' b.2.1 < N := by
    rintro ⟨R₁, R₂, C⟩ hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, -, -, a, a', ha, ha', hlt⟩ := hb
    have h1 := (hG'.weight R₁ hR₁).2 a ha
    have h2 := (hG'.weight R₂ hR₂).2 a' ha'
    have : (c : ℝ) * ((w' R₁ + w' R₂ : ℕ) : ℝ) < c * N := by push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_left this hc.le
  -- the map from bad triples avoiding `E` to old bad triples
  let down : Mori.PrimeDivisor Y' → Mori.PrimeDivisor Y := fun R =>
    if h : ∃ G, st G = R then h.choose else P
  have hdown : ∀ G, down (st G) = G := by
    intro G
    have h : ∃ G', st G' = st G := ⟨G, rfl⟩
    simp only [down, dif_pos h]
    exact hstinj h.choose_spec
  let Vc : Mori.PrimeDivisor Y' × Mori.PrimeDivisor Y' × Set Y' → Set Y := fun b =>
    if h : ∃ V : Set Y, ∃ G₁ G₂ : Mori.PrimeDivisor Y, st G₁ = b.1 ∧ st G₂ = b.2.1 ∧
        V ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y) ∧ V ≠ W ∧
        b.2.2 = closure (π ⁻¹' (V \ W)) then h.choose else ∅
  let φ : Mori.PrimeDivisor Y' × Mori.PrimeDivisor Y' × Set Y' →
      Mori.PrimeDivisor Y × Mori.PrimeDivisor Y × Set Y := fun b => (down b.1, down b.2.1, Vc b)
  have hdesc : ∀ b ∈ (finite_isBad (n := n) (K := K) hlog').toFinset, (b.1 ≠ E ∧ b.2.1 ≠ E) →
      ∃ G₁ G₂ : Mori.PrimeDivisor Y, (G₁.support : Set Y) ⊆ cfg D f ∧
        (G₂.support : Set Y) ⊆ cfg D f ∧ G₁ ≠ G₂ ∧ b.1 = st G₁ ∧ b.2.1 = st G₂ ∧
        φ b = (G₁, G₂, Vc b) ∧
        Vc b ∈ Resolution.componentsOf (G₁.support ∩ G₂.support : Set Y) ∧ Vc b ≠ W ∧
        b.2.2 = closure (π ⁻¹' (Vc b \ W)) := by
    rintro ⟨R₁, R₂, C⟩ hb ⟨h₁, h₂⟩
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, hR₁₂, hC, -⟩ := hb
    obtain ⟨G₁, hG₁, rfl⟩ := ((hR R₁).mp hR₁).resolve_left h₁
    obtain ⟨G₂, hG₂, rfl⟩ := ((hR R₂).mp hR₂).resolve_left h₂
    have hG₁₂ : G₁ ≠ G₂ := fun h => hR₁₂ (h ▸ rfl)
    obtain ⟨V₀, hV₀, hV₀W, hCV₀⟩ := hpair G₁ G₂ hG₁ hG₂ hG₁₂ C hC
    have hex : ∃ V : Set Y, ∃ G₁' G₂' : Mori.PrimeDivisor Y, st G₁' = st G₁ ∧ st G₂' = st G₂ ∧
        V ∈ Resolution.componentsOf (G₁'.support ∩ G₂'.support : Set Y) ∧ V ≠ W ∧
        C = closure (π ⁻¹' (V \ W)) := ⟨V₀, G₁, G₂, rfl, rfl, hV₀, hV₀W, hCV₀⟩
    have hVc : Vc (st G₁, st G₂, C) = hex.choose := dif_pos hex
    obtain ⟨G₁', G₂', e₁, e₂, hV1, hV2, hV3⟩ := hex.choose_spec
    obtain rfl := hstinj e₁
    obtain rfl := hstinj e₂
    refine ⟨G₁', G₂', hG₁, hG₂, hG₁₂, rfl, rfl, ?_, hVc ▸ hV1, hVc ▸ hV2, hVc ▸ hV3⟩
    simp only [φ, hdown]
  refine ⟨Y', π ≫ f, w', hG', ?_⟩
  simp only [measure, dif_pos (finite_isBad (n := n) (K := K) hG.log),
    dif_pos (finite_isBad (n := n) (K := K) hlog')]
  refine isDershowitzMannaLT_map _ _ _ _ (fun b => b.1 ≠ E ∧ b.2.1 ≠ E) φ ?_ ?_ ?_ (P, Q, W)
    ((Set.Finite.mem_toFinset _).mpr ht) ?_ ?_
  · intro b hb hpb
    obtain ⟨G₁, G₂, hG₁, hG₂, hG₁₂, e₁, e₂, hφb, hV1, -, -⟩ := hdesc b hb hpb
    rw [hφb, Set.Finite.mem_toFinset]
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨-, -, -, -, a, a', ha, ha', hlt⟩ := hb
    rw [e₁] at ha
    rw [e₂] at ha'
    exact ⟨hG₁, hG₂, hG₁₂, hV1, a, a', (hLD G₁ a).mp ha, (hLD G₂ a').mp ha', hlt⟩
  · intro b hb b' hb' hpb hpb' h
    obtain ⟨G₁, G₂, -, -, -, e₁, e₂, hφb, -, -, hC⟩ := hdesc b hb hpb
    obtain ⟨G₁', G₂', -, -, -, e₁', e₂', hφb', -, -, hC'⟩ := hdesc b' hb' hpb'
    rw [hφb, hφb'] at h
    obtain ⟨rfl, rfl, hV⟩ := Prod.ext_iff.mp h |>.imp id Prod.ext_iff.mp
    obtain ⟨R₁, R₂, C⟩ := b
    obtain ⟨R₁', R₂', C'⟩ := b'
    simp only at e₁ e₂ e₁' e₂' hC hC' hV
    rw [e₁, e₂, e₁', e₂', hC, hC', hV]
  · intro b hb hpb
    obtain ⟨G₁, G₂, -, -, -, e₁, e₂, hφb, -, -, -⟩ := hdesc b hb hpb
    rw [hφb]
    simp only [e₁, e₂, hw'st]
  · intro b hb hpb h
    obtain ⟨G₁, G₂, -, -, -, -, -, hφb, -, hVW, -⟩ := hdesc b hb hpb
    rw [hφb] at h
    exact hVW (congrArg (fun x => x.2.2) h)
  · intro b hb hpb
    have hbd := hbound b hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, hR₁₂, -⟩ := hb
    simp only [not_and_or, not_not] at hpb
    have h1 := (hG'.weight _ hR₁).1
    have h2 := (hG'.weight _ hR₂).1
    show N - (w' b.1 + w' b.2.1) < N - (w P + w Q)
    rcases hpb with h | h
    · rw [h, hw'E] at hbd h1 ⊢
      omega
    · rw [h, hw'E] at hbd h2 ⊢
      omega

/-- Blowing up bad components terminates. -/
private theorem exists_good_not_isBad (hklt : IsKawamataLogTerminal sX n K D) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 2 ≤ c * N) (m : Multiset ℕ) :
    ∀ {Y : Scheme.{u}} (f : Y ⟶ X) (w : Mori.PrimeDivisor Y → ℕ), Good sX n K D c f w →
      measure sX n K D N f w = m →
      ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X), Mori.IsLogResolution sX D f' ∧
        ∀ t, ¬ IsBad sX n K D f' t := by
  induction m using (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction with
  | _ m ih =>
    intro Y f w hG hm
    by_cases h : ∃ t, IsBad sX n K D f t
    · obtain ⟨t, ht⟩ := h
      obtain ⟨Y', f', w', hG', hlt⟩ := exists_good_lt hklt hc hN hG ht
      exact ih _ (hm ▸ hlt) f' w' hG' rfl
    · exact ⟨Y, f, hG.log, fun t ht => h ⟨t, ht⟩⟩

/-- The initial log resolution, with all weights `1`. -/
private theorem exists_good_init (hklt : IsKawamataLogTerminal sX n K D) :
    ∃ (c : ℝ) (_ : 0 < c) (Y : Scheme.{u}) (f : Y ⟶ X), Good sX n K D c f fun _ => 1 := by
  classical
  obtain ⟨Y, f, hlog⟩ :=
    MMP.FourfoldProofs.Fa4KltSmallLogDiscrepancyCentersProof.exists_isLogResolution sX
      hklt.1.isNormalVariety D
  obtain ⟨s, hs, -⟩ := exists_finset_cfg sX D hlog
  let g : Mori.PrimeDivisor Y → ℝ := fun P =>
    if h : ∃ a, IsLD sX n K D f P a then h.choose else 1
  have hgpos : ∀ P, 0 < g P := by
    intro P
    simp only [g]
    split_ifs with h
    · exact IsLD.pos hklt h.choose_spec
    · exact one_pos
  set A : Finset ℝ := insert 1 (s.image g)
  have hA : A.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨A.min' hA, ?_, Y, f, hlog, fun P hP => ⟨le_rfl, fun a ha => ?_⟩⟩
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_min_image A id hA
    rw [show A.min' hA = x from le_antisymm (Finset.min'_le _ _ hx)
      (Finset.le_min' _ _ _ fun y hy => hxe y hy)]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact one_pos
    · obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hx
      exact hgpos P
  · have hPs : P ∈ s := support_subset_iUnion_iff.mp (hs ▸ hP)
    have hgP : g P = a := by
      have h : ∃ a, IsLD sX n K D f P a := ⟨a, ha⟩
      simp only [g, dif_pos h]
      exact IsLD.eq h.choose_spec ha
    rw [Nat.cast_one, mul_one, ← hgP]
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hPs))

omit [CharZero k] in
/-- **The exceptional set of a Kollár–Mori log resolution.** Its `Ex(f)` is the union of the
`f`-exceptional prime divisors: every component of `Ex(f)` has codimension one and lies in a
configuration divisor, hence is one. -/
private theorem flipsExceptionalSet_eq_iUnion (hklt : IsKawamataLogTerminal sX n K D)
    {Y : Scheme.{u}} {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f) :
    MMP.Flips.exceptionalSet f =
      ⋃ (P : Mori.PrimeDivisor Y) (_ : IsExceptionalPrimeDivisor sX f P), (P.support : Set Y) := by
  have hX : IsNormalVariety k sX := hklt.1.isNormalVariety
  have hn : topologicalKrullDim X = n := hklt.2.1.topologicalKrullDim_eq
  obtain ⟨hYnv, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  obtain ⟨s, hs, -⟩ := exists_finset_cfg sX D hlog
  ext y
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hy
    have hyM : y ∈ (Mori.exceptionalSet f : Set Y) := flipsExceptionalSet_subset_exceptionalSet f hy
    obtain ⟨W, hW, hyW⟩ := MMP.Resolution.exists_mem_componentsOf hyM
    let W' : IrreducibleCloseds Y := ⟨W, hW.1.1,
      MMP.Resolution.Aux.isClosed_of_mem_componentsOf (Mori.exceptionalSet f).isClosed hW⟩
    have hcod : codimension W' = 1 := hlog.isPureCodimOne_exceptionalSet W'
      ⟨hW.1.2, fun V hV hWV => hW.2 ⟨V.isIrreducible, hV⟩ hWV⟩
    have hWcfg : W ⊆ ⋃ E ∈ s, (E.support : Set Y) := hs ▸ hW.1.2.trans fun _ => Or.inl
    obtain ⟨E, -, hWE⟩ := PrimeDivisorUnion.exists_subset_of_isIrreducible
      (fun E _ => PrimeDivisorUnion.isClosed_support E) hW.1.1 hWcfg
    let E' : IrreducibleCloseds Y := ⟨E.support, PrimeDivisorUnion.isIrreducible_support E,
      PrimeDivisorUnion.isClosed_support E⟩
    have hWE' : W' = E' := by
      by_contra hne
      have h1 := Order.coheight_add_one_le (show W' < E' from lt_of_le_of_ne hWE hne)
      rw [← codimension_eq_coheight, ← codimension_eq_coheight, hcod,
        PrimeDivisorUnion.codimension_eq_one_of_eq_support E' E rfl] at h1
      exact absurd h1 (by decide)
    have hEW : (E.support : Set Y) = W := congrArg SetLike.coe hWE'.symm
    exact ⟨E, (isExceptionalPrimeDivisor_iff hX hn hYnv hfb E).mpr
      (hW.1.2 (hEW ▸ genericPoint_mem_support E)), hEW ▸ hyW⟩
  · rintro ⟨P, hP, hyP⟩
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    exact support_subset_flipsExceptionalSet hn hP hyP

/-- A Kollár–Mori log resolution with no bad triple is a log resolution whose exceptional set is
the union of the exceptional prime divisors, and any two distinct meeting configuration divisors
have log discrepancies summing to at least `2`. -/
private theorem two_le_logDiscrepancy_add_of_not_isBad (hklt : IsKawamataLogTerminal sX n K D)
    {Y : Scheme.{u}} {f : Y ⟶ X} (hlog : Mori.IsLogResolution sX D f)
    (hno : ∀ t, ¬ IsBad sX n K D f t) :
    IsLogResolution sX D f ∧
      MMP.Flips.exceptionalSet f =
        ⋃ (P : Mori.PrimeDivisor Y) (_ : IsExceptionalPrimeDivisor sX f P), (P.support : Set Y) ∧
      ∀ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (hp : IsProper f)
        (P Q : Mori.PrimeDivisor Y), P ≠ Q →
        (IsExceptionalPrimeDivisor sX f P ∨ (birationalInverseTransform f hf D).coeff P ≠ 0) →
        (IsExceptionalPrimeDivisor sX f Q ∨ (birationalInverseTransform f hf D).coeff Q ≠ 0) →
        ((P.support : Set Y) ∩ Q.support).Nonempty →
        ∀ a b : ℝ,
          IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp).valuation a →
          IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, Q⟩ hp).valuation b →
          2 ≤ a + b := by
  classical
  have hX : IsNormalVariety k sX := hklt.1.isNormalVariety
  have hn : topologicalKrullDim X = n := hklt.2.1.topologicalKrullDim_eq
  obtain ⟨hYnv, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
  have hfb := hlog.isBirationalMorphism
  haveI : IsProper f := hlog.isProper
  obtain ⟨s, hs, hsnc⟩ := exists_finset_cfg sX D hlog
  have hcfg : ∀ P : Mori.PrimeDivisor Y, (P.support : Set Y) ⊆ cfg D f ↔
      P.genericPoint ∈ (Mori.exceptionalSet f : Set Y) ∨
        f P.genericPoint ∈ (DivisorWithCoeffs.supp D : Set X) := by
    intro P
    rw [support_subset_iff P (cfg D f).isClosed]
    simp only [cfg, Closeds.coe_sup, Set.mem_union, Closeds.coe_preimage, Set.mem_preimage]
  have hmem : ∀ P : Mori.PrimeDivisor Y, P ∈ s ↔
      IsExceptionalPrimeDivisor sX f P ∨ (birationalInverseTransform f hfb D).coeff P ≠ 0 := by
    intro P
    rw [← support_subset_iUnion_iff, hs, hcfg, isExceptionalPrimeDivisor_iff hX hn hYnv hfb]
    by_cases hP : P.genericPoint ∈ (Mori.exceptionalSet f : Set Y)
    · simp [hP]
    · rw [coeff_birationalInverseTransform_ne_zero_iff hX D hYnv hfb P hP]
  refine ⟨⟨hklt.1, hYnv.1, hlog.isSmoothScheme, hlog.isProper, hfb,
    MMP.Intersection.reducedDivisorOf s, MMP.Intersection.isReducedEffective_reducedDivisorOf s,
    fun P => ?_,
    isSNCDivisor_reducedDivisorOf hsnc⟩, flipsExceptionalSet_eq_iUnion hklt hlog, ?_⟩
  · rw [MMP.Intersection.coeff_reducedDivisorOf, or_comm, ← hmem]
    split_ifs with h <;> simp [h]
  · intro hY' hf' hp' P Q hPQ hP hQ hPQne a b ha hb
    have hP' : (P.support : Set Y) ⊆ cfg D f := by
      rw [← hs]; exact support_subset_iUnion_iff.mpr ((hmem P).mpr hP)
    have hQ' : (Q.support : Set Y) ⊆ cfg D f := by
      rw [← hs]; exact support_subset_iUnion_iff.mpr ((hmem Q).mpr hQ)
    obtain ⟨x, hx⟩ := hPQne
    obtain ⟨W, hW, -⟩ := MMP.Resolution.exists_mem_componentsOf hx
    by_contra hlt
    exact hno (P, Q, W) ⟨hP', hQ', hPQ, hW, a, b, ⟨hY', hf', hp', ha⟩, ⟨hY', hf', hp', hb⟩,
      not_le.mp hlt⟩

end Main

section PairCondition

/-- Over a klt pair there is a log resolution `f : Y ⟶ X` whose exceptional set is the union of the
`f`-exceptional prime divisors, such that any two distinct meeting configuration divisors `P`, `Q`
satisfy `2 ≤ a_ℓ(P) + a_ℓ(Q)`. -/
private theorem exists_isLogResolution_two_le_logDiscrepancy_add {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {D : RDivisor X}
    (hklt : IsKawamataLogTerminal sX n K D) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsLogResolution sX D f ∧
      exceptionalSet f =
        ⋃ (P : Mori.PrimeDivisor Y) (_ : IsExceptionalPrimeDivisor sX f P), (P.support : Set Y) ∧
      ∀ (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) (hp : IsProper f)
        (P Q : Mori.PrimeDivisor Y), P ≠ Q →
        (IsExceptionalPrimeDivisor sX f P ∨ (birationalInverseTransform f hf D).coeff P ≠ 0) →
        (IsExceptionalPrimeDivisor sX f Q ∨ (birationalInverseTransform f hf D).coeff Q ≠ 0) →
        ((P.support : Set Y) ∩ Q.support).Nonempty →
        ∀ a b : ℝ,
          IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, P⟩ hp).valuation a →
          IsLogDiscrepancy sX n K D (ProperDivisorOver.mk ⟨Y, f, hY, hf, Q⟩ hp).valuation b →
          2 ≤ a + b := by
  obtain ⟨c, hc, Y₀, f₀, hG⟩ := exists_good_init hklt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 / c ≤ N := exists_nat_ge _
  have hN' : 2 ≤ c * N := by
    rw [div_le_iff₀ hc] at hN
    linarith
  obtain ⟨Y, f, hlog, hno⟩ := exists_good_not_isBad hklt hc hN' _ f₀ _ hG rfl
  exact ⟨Y, f, two_le_logDiscrepancy_add_of_not_isBad hklt hlog hno⟩

end PairCondition

section Lifting

open scoped WithZero

/-- A divisor over a normal variety which is not exceptional has the valuation of a prime divisor
of the variety. -/
private theorem exists_primeDivisor_divisorialValuation_eq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) (hD : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.valuation = P.divisorialValuation := by
  obtain ⟨P, hP⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  exact ⟨P, hP.trans (valuation_ofPrimeDivisor hX P)⟩

/-- A divisor over a normal variety is exceptional (in the sense of Kollár–Mori) if and only if
its center has codimension at least two. -/
private theorem divisorOver_isExceptional_iff_two_le_coheight {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := TopologicalSpace.Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, every divisor `D` over
`X` has the valuation of a divisor `E` over `Y`, read on `k(X)` through `f^*`. -/
private theorem exists_properDivisorOver_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) [IsProper f]
    (D : ProperDivisorOver k sX) :
    haveI : IsDominant f := hf.isDominant
    ∃ E : ProperDivisorOver k (f ≫ sX), E.valuation.comap (functionFieldMap f) = D.valuation := by
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    exact congrArg D.valuation (e.symm_apply_apply t)
  -- `ξ` dominates the local ring of a point of `Y` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : Y, (∀ a : Y.presheaf.stalk x,
      ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
    set z := D.f D.E.genericPoint
    have hw : ∀ b : X.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
          D.valuation (algebraMap _ X.functionField b) := by
      intro b
      simpa only [Valuation.comap_apply] using
        congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
    let R := ξ.valuationSubring
    let φ : X.presheaf.stalk z →+* R :=
      ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D.toDivisorOver z rfl _)
    have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hex : ValuativeCriterion.Existence f := by
      have h : @IsProper _ _ f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq f :=
      { R := R
        K := Y.functionField
        i₁ := Y.fromSpecStalk (genericPoint Y)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk f,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
        Y.fromSpecStalk (genericPoint Y) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
        Y.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (Y.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : Y.presheaf.stalk x,
        algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]; exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(Y)`: `ord_E` on `D.Y`, along `k(Y) ≅ k(X) ≅ k(D.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  exact ⟨D', by rw [hv, hξ]⟩

/-- A dominant morphism of integral schemes maps the generic point of `Y` outside the support of
every `ℚ`-divisor on `X`. -/
private theorem map_componentGenericPoint_notMem_supp {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (C : QDivisor X)
    (Z : irreducibleComponents Y) : f (componentGenericPoint Y Z) ∉ C.supp := by
  rw [MMP.Threefold.Mori.CanonUniq.componentGenericPoint_eq, map_genericPoint_of_isDominant]
  intro h
  obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support E hE

/-- Every divisor over `X` has a discrepancy `a_ω(E, X, B)` with respect to a pair `(X, B)` with
`K_X + B` `ℚ`-Cartier. -/
private theorem exists_isQDiscrepancyWith {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hX : IsNormalVariety k sX)
    (hK : K.IsCanonicalDivisor sX n) (hKB : (Divisor.toQDivisor K + B).IsQCartier)
    (E : ProperDivisorOver k sX) :
    ∃ (ω : RationalPluriForms sX n 1) (a : ℚ), IsQDiscrepancyWith sX n B ω E a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  have hKB' : (Divisor.toQDivisor (divisorOfForm ω) + B).IsQCartier := hdiv ▸ hKB
  have hB := map_componentGenericPoint_notMem_supp E.f (Divisor.toQDivisor (divisorOfForm ω) + B)
  obtain ⟨G, hG, -⟩ := hKB'.existsUnique_isPullback hB
  exact ⟨ω, _, hX, hK.1, hω0, hKB', hB, G, hG, rfl⟩

/-- The divisor `(Y', f ∘ g, E)` over `X` of a divisor `(Y', g, E)` over `Y`. -/
private def compDivisorOver {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f]
    (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : ProperDivisorOver k (f ≫ sX)) :
    ProperDivisorOver k sX where
  Y := E.Y
  f := E.f ≫ f
  isNormalVariety := by
    simpa only [Category.assoc] using E.isNormalVariety
  isBirationalMorphism := by
    haveI := E.isIntegral
    haveI := E.isProper
    exact isBirationalMorphism_comp_of_isBirational f E.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism E.isBirationalMorphism)
  E := E.E
  isProper := by
    haveI := E.isProper
    infer_instance

/-- The valuation of the composite divisor over `X` is `ord_E ∘ f^*`. -/
private theorem compDivisorOver_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : ProperDivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext a
  change E.E.divisorialValuation _ = E.E.divisorialValuation _
  congr 1
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply E.f f a).symm

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (E : ProperDivisorOver k sX) : HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  refine ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-! ### Local isomorphisms near a point off the exceptional set -/

/-- If `f` restricted to an open `V` is an open immersion, `f` induces isomorphisms of local rings
at the points of `V`. -/
private theorem isIso_stalkMap_of_isOpenImmersion_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (V : Y.Opens) [IsOpenImmersion (V.ι ≫ f)] (v : V.toScheme) : IsIso (f.stalkMap (V.ι v)) := by
  have h1 := IsOpenImmersion.instIsIsoCommRingCatStalkMap (V.ι ≫ f) v
  have h2 := IsOpenImmersion.instIsIsoCommRingCatStalkMap V.ι v
  rw [Scheme.Hom.stalkMap_comp] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h1

/-- Let `f` restrict to an open immersion on an open `V`, and let `P'` be a prime divisor of `Y`
with generic point in `V` lying over the generic point of a prime divisor `P` of `X`. At a point
`y ∈ V`, the isomorphism `f^♯ : 𝒪_{X,f(y)} ≅ 𝒪_{Y,y}` carries the ideal of `P` to that of `P'`. -/
private theorem map_stalk_idealSheaf_of_isOpenImmersion_comp {X Y : Scheme.{u}} (f : Y ⟶ X)
    (V : Y.Opens) [IsOpenImmersion (V.ι ≫ f)] (P : Mori.PrimeDivisor X)
    (P' : Mori.PrimeDivisor Y) (hgen : f P'.genericPoint = P.genericPoint)
    (hP'V : P'.genericPoint ∈ V) (v : V.toScheme) :
    Ideal.map (f.stalkMap (V.ι v)).hom (IdealSheafData.stalk P.idealSheaf (f (V.ι v))) =
      IdealSheafData.stalk P'.idealSheaf (V.ι v) := by
  set w : V.toScheme := ⟨P'.genericPoint, hP'V⟩
  have hc : Order.coheight w = 1 :=
    (coheight_eq_of_isOpenImmersion (x := w) V.ι).symm.trans P'.coheight_genericPoint
  let E' : AlgebraicGeometry.PrimeDivisor V.toScheme :=
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hc
  have h1 : OpenWeilRestriction.primeDivisorMap (V.ι ≫ f) E' = P := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hgen
  have h2 : OpenWeilRestriction.primeDivisorMap V.ι E' = P' := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    rfl
  have hI1 := MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap (V.ι ≫ f) E'
  have hI2 := MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap V.ι E'
  rw [h1] at hI1
  rw [h2] at hI2
  have s1 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map (V.ι ≫ f) P.idealSheaf v
  have s2 := MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map V.ι P'.idealSheaf v
  rw [hI1] at s1
  rw [hI2, s1] at s2
  have hcomp : Ideal.map ((V.ι ≫ f).stalkMap v).hom
      (IdealSheafData.stalk P.idealSheaf (f (V.ι v))) =
      Ideal.map (V.ι.stalkMap v).hom (Ideal.map (f.stalkMap (V.ι v)).hom
        (IdealSheafData.stalk P.idealSheaf (f (V.ι v)))) := by
    rw [Ideal.map_map]
    have h' : ((V.ι ≫ f).stalkMap v).hom =
        (V.ι.stalkMap v).hom.comp (f.stalkMap (V.ι v)).hom := by
      rw [← CommRingCat.hom_comp]
      exact congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp V.ι f v)
    exact congrArg (fun g => Ideal.map g _) h'
  have s3 := hcomp.symm.trans s2
  have h3 := IsOpenImmersion.instIsIsoCommRingCatStalkMap V.ι v
  have hb := ConcreteCategory.bijective_of_isIso (V.ι.stalkMap v)
  have := congrArg (Ideal.comap (V.ι.stalkMap v).hom) s3
  rwa [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at this

/-- Let `f` restrict to an open immersion on an open `V ∋ y`. Every prime divisor `Q` of `X`
through `f y` is the image of a prime divisor `Q'` of `Y` through `y`, with `f(η_{Q'}) = η_Q` and
`ord_{Q'} = ord_Q` on `k(X)`. -/
private theorem exists_primeDivisor_of_isOpenImmersion_comp {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (V : Y.Opens) [IsOpenImmersion (V.ι ≫ f)] (v : V.toScheme)
    (Q : Mori.PrimeDivisor X) (hQ : f (V.ι v) ∈ Q.support) :
    ∃ Q' : Mori.PrimeDivisor Y, V.ι v ∈ Q'.support ∧ f Q'.genericPoint = Q.genericPoint ∧
      Q'.valuationOver f = Q.divisorialValuation := by
  have hspQ : Q.genericPoint ⤳ f (V.ι v) := (genericPoint_specializes_iff Q).mpr hQ
  obtain ⟨vQ, hvQ⟩ : Q.genericPoint ∈ Set.range (V.ι ≫ f) :=
    hspQ.mem_open (IsOpenImmersion.isOpen_range (V.ι ≫ f)) ⟨v, rfl⟩
  have hcQ : Order.coheight (V.ι vQ) = 1 := by
    rw [coheight_eq_of_isOpenImmersion (x := vQ) V.ι,
      ← coheight_eq_of_isOpenImmersion (x := vQ) (V.ι ≫ f)]
    change Order.coheight ((V.ι ≫ f) vQ) = 1
    rw [hvQ]
    exact Q.coheight_genericPoint
  let Q' : Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcQ
  have hQ'g : Q'.genericPoint = V.ι vQ :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcQ
  have hQ'gen : f Q'.genericPoint = Q.genericPoint := by rw [hQ'g]; exact hvQ
  haveI : IsIso (f.stalkMap Q'.genericPoint) := by
    rw [hQ'g]; exact isIso_stalkMap_of_isOpenImmersion_comp f V vQ
  refine ⟨Q', ?_, hQ'gen, valuationOver_eq_of_isIso f Q' Q hQ'gen⟩
  have hspY : V.ι vQ ⤳ V.ι v := by
    have h1 : (V.ι ≫ f) vQ ⤳ (V.ι ≫ f) v := hvQ ▸ hspQ
    exact ((Scheme.Hom.isOpenEmbedding (V.ι ≫ f)).isInducing.specializes_iff.mp h1).map
      V.ι.continuous
  exact (genericPoint_specializes_iff Q').mp (by rw [hQ'g]; exact hspY)

end Lifting

open scoped WithZero in
/-- For a Kawamata log terminal pair `(X, D)` over a field of characteristic zero, with `D` an
effective `ℚ`-divisor, there is a finite set `𝒩` of exceptional divisors with nonempty center on
`X` such that every exceptional divisor `ν ∉ 𝒩` with nonempty center and log discrepancy
`b < min {2, 2 + discrep(X, D)}` has a component `P` of `D` with `0 < D.coeff P` and
`2 - D.coeff P ≤ b`, such that the center `W` of `ν` has codimension `2`, lies in `P` and in no
other component of `D`, and both `𝒪_{X,η_W}` and `𝒪_{X,η_W} / I_{P,η_W}` are regular local
rings. -/
theorem solution {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (h : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor D)) (hD : D.IsEffective) :
    ∃ 𝒩 : Set (Valuation X.functionField ℤᵐ⁰), 𝒩.Finite ∧
      (∀ ν ∈ 𝒩, HasNonemptyCenter k sX ν ∧
        ∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) ∧
      ∀ ν : Valuation X.functionField ℤᵐ⁰, ν ∉ 𝒩 → HasNonemptyCenter k sX ν →
        (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) →
        ∀ b : ℝ, IsLogDiscrepancy sX n K (QDivisor.toRDivisor D) ν b →
          (b : EReal) < min 2 (1 + (1 + discrep sX n D)) →
          ∃ P : Mori.PrimeDivisor X, 0 < D.coeff P ∧ 2 - (D.coeff P : ℝ) ≤ b ∧
            ∀ E : ProperDivisorOver k sX, E.valuation = ν →
              codimension E.center = 2 ∧ (E.center : Set X) ⊆ P.support ∧
              (∀ Q : Mori.PrimeDivisor X, D.coeff Q ≠ 0 → (E.center : Set X) ⊆ Q.support →
                Q = P) ∧
              IsRegularLocalRing (X.presheaf.stalk E.center.isIrreducible.genericPoint) ∧
              IsRegularLocalRing (X.presheaf.stalk E.center.isIrreducible.genericPoint ⧸
                IdealSheafData.stalk P.idealSheaf E.center.isIrreducible.genericPoint) := by
  classical
  have hX : IsNormalVariety k sX := h.1.isNormalVariety
  have hK : K.IsCanonicalDivisor sX n := h.2.1
  have hKD := h.2.2.1
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  obtain ⟨Y, f, hlog, hEx, hpair⟩ := exists_isLogResolution_two_le_logDiscrepancy_add h
  obtain ⟨-, hYvar, hYsm, hfp, hfb, G, hG01, hGiff, hGsnc⟩ := id hlog
  -- instances on `Y`
  haveI : IsIntegral Y := hYvar.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hYvar.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : Smooth (f ≫ sX) := hYsm.smooth
  haveI : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  haveI : IsNormal Y := AlgebraicGeometry.isNormal_of_smooth (f ≫ sX)
  haveI : CompactSpace Y := hYvar.toQuasiCompact.compactSpace_of_compactSpace
  haveI := hfp
  haveI : IsDominant f := hfb.isDominant
  have hY : IsNormalVariety k (f ≫ sX) := ⟨hYvar, inferInstance⟩
  -- a rational form with `div_X(ω) = K`
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hdiv : divisorOfForm ω = K := DivisorWithCoeffs.ext' hω
  subst hdiv
  set D' : RDivisor X := QDivisor.toRDivisor D with hD'
  -- the crepant boundary `D_Y`: `div_Y(f^*ω) + D_Y = f^*(K_X + D)`
  obtain ⟨GP, hGP, -⟩ := existsUnique_isRCartierPullback f hKD
  set σ := pullbackRationalPluriForms sX f ω with hσ
  set DY : RDivisor Y := GP - Divisor.toRDivisor (divisorOfForm σ) with hDYdef
  have hDY : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D')
      (Divisor.toRDivisor (divisorOfForm σ) + DY) := by
    rwa [hDYdef, add_sub_cancel]
  have hKY := isCanonicalDivisor_divisorOfForm_pullback hX hω0 hK hY hfb hYsm
  have hcrep := isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hY hfb hDY hKY
  -- the divisor `(Y, f, P)` over `X` of a prime divisor `P` of `Y`
  let toX : Mori.PrimeDivisor Y → ProperDivisorOver k sX := fun P =>
    ProperDivisorOver.mk ⟨Y, f, hY, hfb, P⟩ hfp
  -- `a(P, X, D) = -coeff_P D_Y`
  have hF1 : ∀ P : Mori.PrimeDivisor Y,
      IsDiscrepancy sX n (divisorOfForm ω) D' (toX P).valuation (-DY.coeff P) :=
    isDiscrepancy_valuationOver hX hω0 hK hKD hY hfb hYsm hDY
  -- off `Ex(f)`, the coefficients of `D_Y` are those of `D`
  have hcoeffY : ∀ (R : Mori.PrimeDivisor Y) (Γ : Mori.PrimeDivisor X),
      R.valuationOver f = Γ.divisorialValuation → DY.coeff R = D.coeff Γ := by
    intro R Γ hRΓ
    have h1 := hF1 R
    rw [show (toX R).valuation = Γ.divisorialValuation from hRΓ] at h1
    have := h1.eq_neg_coeff
    rw [hD', QDivisor.coeff_toRDivisor] at this
    linarith
  -- klt: the coefficients of `D_Y` are `< 1`
  have hF3 : ∀ P, DY.coeff P < 1 := by
    intro P
    have := h.2.2.2 _ (hasNonemptyCenter_valuation (toX P)) _ ⟨_, hF1 P, rfl⟩
    linarith
  -- `D_Y` is supported on the snc divisor `G`
  have hsupp : ∀ P, DY.coeff P ≠ 0 → G.coeff P = 1 := by
    obtain ⟨Ex, aE, GP', hEx', hGP', -, hform⟩ := discrepancy_formula hX D' ω hω0 hK hKD f hY hfb
    have hGG : GP' = GP := IsRCartierPullback.eq f hGP' hGP
    intro P hP
    refine (hGiff P).mpr ?_
    by_cases hex : IsExceptionalPrimeDivisor sX f P
    · exact Or.inr hex
    · left
      have hPEx : P ∉ Ex := fun h => hex ((hEx' P).mp h)
      have h := DFunLike.congr_fun hform P
      simp only [Finsupp.add_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
        Finsupp.single_apply, Finset.sum_ite_eq', hPEx, if_false, add_zero, hGG] at h
      rw [DivisorWithCoeffs.coeff_apply] at hP ⊢
      rw [← hσ] at h
      rw [hDYdef, Finsupp.sub_apply, ← h] at hP
      simpa using hP
  have hGmem : ∀ P, P ∈ G.support ↔ G.coeff P = 1 := by
    intro P
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
    rcases hG01 P with h0 | h1 <;> simp [*]
  -- the set `𝒩` of valuations of the `f`-exceptional prime divisors
  let 𝒩 : Set (Valuation X.functionField ℤᵐ⁰) :=
    {ν | ∃ P, IsExceptionalPrimeDivisor sX f P ∧ (toX P).valuation = ν}
  refine ⟨𝒩, ?_, ?_, ?_⟩
  · refine (G.support.finite_toSet.image fun P => (toX P).valuation).subset ?_
    rintro ν ⟨P, hP, rfl⟩
    exact ⟨P, (hGmem P).mpr ((hGiff P).mpr (Or.inr hP)), rfl⟩
  · rintro ν ⟨P, ⟨hY', hf', hp', hE⟩, rfl⟩
    exact ⟨hasNonemptyCenter_valuation _, toX P, hE, rfl⟩
  intro ν hν𝒩 hνc ⟨E₀, hE₀ex, hE₀ν⟩ b hb hlt
  obtain ⟨a, ha, rfl⟩ := hb
  have hlt2 : 1 + a < 2 := by
    have h : ((1 + a : ℝ) : EReal) < ((2 : ℝ) : EReal) := hlt.trans_le (min_le_left _ _)
    exact EReal.coe_lt_coe_iff.mp h
  have hltd : (((1 + a : ℝ)) : EReal) < 1 + (1 + discrep sX n D) := hlt.trans_le (min_le_right _ _)
  -- `ν` has a center on `Y`, and `a_ℓ(ν, Y, D_Y) = a_ℓ(ν, X, D)`
  obtain ⟨EY, hEY⟩ := exists_properDivisorOver_comap_eq hY hfb E₀
  have haY := (hcrep EY a).mp (by rw [hEY, hE₀ν]; exact ha)
  -- the center of `ν` on `Y` is not a divisor
  have hcod : 2 ≤ codimension EY.center := by
    rw [EY.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]
    by_contra hlt'
    have hne : ¬ EY.toDivisorOver.IsExceptional := fun hM =>
      hlt' ((divisorOver_isExceptional_iff_two_le_coheight hY _).mp hM)
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_divisorialValuation_eq hY _ hne
    have hνQ : (toX Q).valuation = ν := by
      rw [← hE₀ν, ← hEY]
      ext g
      change Q.divisorialValuation (functionFieldMap f g) =
        EY.toDivisorOver.valuation (functionFieldMap f g)
      rw [hQ]
    by_cases hQex : IsExceptionalPrimeDivisor sX f Q
    · exact hν𝒩 ⟨Q, hQex, hνQ⟩
    · apply hQex
      refine ⟨hY, hfb, hfp, ?_⟩
      have hc := ProperDivisorOver.center_eq_of_valuation_eq hX.1 (hνQ.trans hE₀ν.symm)
      unfold ProperDivisorOver.IsExceptional
      rw [hc]
      exact hE₀ex
  have hpairY : ∀ P ∈ G.support, ∀ Q ∈ G.support, P ≠ Q →
      ((P.support : Set Y) ∩ Q.support).Nonempty → 2 ≤ (1 - DY.coeff P) + (1 - DY.coeff Q) := by
    intro P hP Q hQ hPQ hmeet
    exact hpair hY hfb hfp P Q hPQ ((hGiff P).mp ((hGmem P).mp hP)).symm
      ((hGiff Q).mp ((hGmem Q).mp hQ)).symm hmeet _ _ ⟨_, hF1 P, by ring⟩ ⟨_, hF1 Q, by ring⟩
  obtain ⟨hcod2, PY, hPYG, hWPY, huniq, hpos, hle⟩ :=
    codimension_center_eq_two_of_logDiscrepancy_lt_two (f ≫ sX) hYvar hYsm hGsnc
      (fun P hP => (hGmem P).mpr (hsupp P hP)) (fun P _ => (hF3 P).le) hpairY EY hcod
      ⟨a, haY, rfl⟩ hlt2
  -- the component `PY` is not exceptional: `discrep(X, D) ≤ a(PY, X, D) = -coeff_PY D_Y`
  have hKQ : (Divisor.toQDivisor (divisorOfForm ω) + D).IsQCartier := by
    refine QDivisor.isQCartier_of_isCartierCombination ?_
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    exact hKD
  have hPYne : ¬ IsExceptionalPrimeDivisor sX f PY := by
    rintro ⟨hY', hf', hp', hE⟩
    obtain ⟨ω', q, hq⟩ := exists_isQDiscrepancyWith hX hK hKQ (toX PY)
    have hqd := (hq.isDiscrepancy hK hKQ hE).eq (hF1 PY)
    have hdle : discrep sX n D ≤ ((-DY.coeff PY : ℝ) : EReal) :=
      sInf_le ⟨toX PY, ω', q, hE, hq, by rw [hqd]⟩
    have h1 : (1 : EReal) + (1 + discrep sX n D) ≤ ((2 - DY.coeff PY : ℝ) : EReal) := by
      calc (1 : EReal) + (1 + discrep sX n D) ≤ 1 + (1 + ((-DY.coeff PY : ℝ) : EReal)) :=
            by gcongr
        _ = ((2 - DY.coeff PY : ℝ) : EReal) := by
          rw [← EReal.coe_one, ← EReal.coe_add, ← EReal.coe_add]
          congr 1
          ring
    have h2 : ((2 - DY.coeff PY : ℝ) : EReal) ≤ ((1 + a : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hle
    exact (hltd.trans_le (h1.trans h2)).false
  -- so `PY` is the strict transform of a component `P` of `D`, with `coeff_PY D_Y = coeff_P D`
  have hPYne' : ¬ (toX PY).toDivisorOver.IsExceptional := fun hM =>
    hPYne ⟨hY, hfb, hfp, (isExceptional_iff_two_le_coheight hn _).mpr
      ((divisorOver_isExceptional_iff_two_le_coheight hX _).mp hM)⟩
  obtain ⟨P, hPv⟩ := exists_primeDivisor_divisorialValuation_eq hX _ hPYne'
  have hcoef : DY.coeff PY = D.coeff P := hcoeffY PY P hPv
  have hPgen : f PY.genericPoint = P.genericPoint := by
    let EP : ProperDivisorOver k sX :=
      ⟨DivisorOver.ofPrimeDivisor k hX P, (inferInstance : IsProper (𝟙 X))⟩
    have hc := ProperDivisorOver.center_eq_of_valuation_eq hX.1 (D := toX PY) (D' := EP)
      (hPv.trans (valuation_ofPrimeDivisor hX P).symm)
    have h1 := congrArg (fun W : IrreducibleCloseds X => (W : Set X)) hc
    simp only [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq
  refine ⟨P, ?_, ?_, fun E hE => ?_⟩
  · have : (0 : ℝ) < D.coeff P := hcoef ▸ hpos
    exact_mod_cast this
  · rwa [← hcoef]
  -- the center of `ν` on `Y` is the closure of `y`, and its center on `X` that of `f(y)`
  have hWY : (EY.center : Set Y) = closure {EY.f EY.E.genericPoint} := by
    rw [EY.center_eq_toDivisorOver_center]
    exact EY.toDivisorOver.center_eq_closure_genericPoint
  have hEc : E.center = (compDivisorOver f hfb EY).center :=
    ProperDivisorOver.center_eq_of_valuation_eq hX.1
      (hE.trans (hE₀ν.symm.trans (hEY.symm.trans (compDivisorOver_valuation f hfb EY).symm)))
  have hWX : (E.center : Set X) = closure {f (EY.f EY.E.genericPoint)} := by
    rw [hEc, ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint]
    rfl
  rw [EY.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center] at hcod2
  generalize EY.f EY.E.genericPoint = y at hWY hWX hcod2
  have hgen : E.center.isIrreducible.genericPoint = f y := by
    have h1 := E.center.isIrreducible.isGenericPoint_genericPoint E.center.isClosed
    have h2 : IsGenericPoint (f y) (E.center : Set X) := hWX ▸ isGenericPoint_closure
    exact h1.eq h2
  rw [hgen]
  have hyW : y ∈ (EY.center : Set Y) := hWY ▸ subset_closure rfl
  have hyPY : y ∈ PY.support := hWPY hyW
  have hspPY : PY.genericPoint ⤳ y := (genericPoint_specializes_iff PY).mpr hyPY
  have hWsub : ∀ Q : Mori.PrimeDivisor Y, y ∈ Q.support →
      (EY.center : Set Y) ⊆ Q.support := fun Q hQ => by
    rw [hWY]
    exact closure_minimal (Set.singleton_subset_iff.mpr hQ)
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support Q)
  -- `y` lies on no `f`-exceptional divisor, so `f` is an open immersion near `y`
  have hyEx : y ∉ Flips.exceptionalSet f := by
    intro hy'
    rw [hEx] at hy'
    obtain ⟨Q, hQex, hyQ⟩ := Set.mem_iUnion₂.mp hy'
    have := huniq Q ((hGmem Q).mpr ((hGiff Q).mpr (Or.inr hQex))) (hWsub Q hyQ)
    exact hPYne (this ▸ hQex)
  obtain ⟨V, hyV, hVimm⟩ : ∃ V : Y.Opens, y ∈ V ∧ IsOpenImmersion (V.ι ≫ f) := not_not.mp hyEx
  obtain ⟨v, rfl⟩ : ∃ v : V.toScheme, V.ι v = y := ⟨⟨y, hyV⟩, rfl⟩
  have hiso := isIso_stalkMap_of_isOpenImmersion_comp f V v
  let e := (asIso (f.stalkMap (V.ι v))).commRingCatIsoToRingEquiv
  have hco : Order.coheight (f (V.ι v)) = Order.coheight (V.ι v) := by
    have h := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  have hfPY : f (V.ι v) ∈ P.support :=
    (genericPoint_specializes_iff P).mp (by rw [← hPgen]; exact hspPY.map f.continuous)
  have hPYV : PY.genericPoint ∈ V := hspPY.mem_open V.isOpen hyV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rwa [codimension_eq_coheight_genericPoint, hgen, hco]
  · -- `Center_X(ν) ⊆ P`
    rw [hWX, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hfPY
    exact closure_minimal (Set.singleton_subset_iff.mpr hfPY) isClosed_closure
  · -- no other component of `D` contains the center
    intro Q hQ hWQ
    obtain ⟨QY, hyQY, hQYgen, hQYv⟩ :=
      exists_primeDivisor_of_isOpenImmersion_comp f V v Q (hWQ (hWX ▸ subset_closure rfl))
    have hQYG : QY ∈ G.support := (hGmem QY).mpr (hsupp QY fun h0 => hQ (by
      exact_mod_cast (hcoeffY QY Q hQYv).symm.trans h0))
    have hQP := huniq QY hQYG (hWsub QY hyQY)
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change Q.genericPoint = P.genericPoint
    rw [← hQYgen, ← hPgen, hQP]
  · -- `X` is regular at the generic point of the center
    have hreg : IsRegularLocalRing (Y.presheaf.stalk (V.ι v)) :=
      (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk (f ≫ sX)).mp
        inferInstance _
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · -- `P` is regular at the generic point of the center
    have hq : IsRegularLocalRing (Y.presheaf.stalk (V.ι v) ⧸
        IdealSheafData.stalk PY.idealSheaf (V.ι v)) :=
      MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk (f ≫ sX) PY.idealSheaf
        (hGsnc.2.1 PY hPYG) hyPY
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv _ _ e
      (map_stalk_idealSheaf_of_isOpenImmersion_comp f V P PY hPgen hPYV v).symm).symm

end MMP.FourfoldProofs.Fa4KltSmallLogDiscrepancyCentersProof

end

section

/-!
# Centers of exceptional divisors of small log discrepancy over a klt pair

Let `(X, D)` be a Kawamata log terminal pair, with `D = ∑ⱼ dⱼ Dⱼ` an effective `ℚ`-divisor. Then,
apart from finitely many exceptional divisors of `k(X)`, every exceptional divisor `ν` of `k(X)`
with nonempty center on `X` and `a_ℓ(ν, X, D) < min {2, 1 + logdiscrep(X, D)}` is "seen" by a
single component of `D`: there is `j` with `dⱼ > 0` such that `Center_X(ν)` is an irreducible
closed subset of codimension `2` lying in `Dⱼ` and in no other component of `D`, `X` and `Dⱼ`
are regular at its generic point, and `a_ℓ(ν, X, D) ≥ 2 - dⱼ`. Here
`logdiscrep(X, D) = 1 + discrep(X, D)`.

The source's printed version asserts more (that every such `ν` is obtained by blowing up the
generic point of its center); that stronger form is false, and only the description of the
center survives.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_finite_forall_logDiscrepancy_lt_min`: the statement
  above.

## Implementation notes

* An exceptional divisor of `k(X)` with nonempty center on `X` is a valuation `ν` of `k(X)` with
  `MMP.Flips.HasNonemptyCenter` that is the valuation of an exceptional divisor `(Y, f, E)` over
  `X`, as in `MMP.Flips.smallLogDiscrepancySet`. Its center is the center `f(E)` of any such
  realization; the conclusion is asserted for every realization.
* The components `Dⱼ` of `D` are the prime divisors `P` with `D.coeff P ≠ 0`, and `dⱼ = D.coeff P`.
* `Dⱼ` is regular at the generic point `η` of the center when the local ring
  `𝒪_{X,η} / I_{Dⱼ,η}` of `Dⱼ` at `η` is regular.
* The bound `min {2, 1 + logdiscrep(X, D)}` is taken in `EReal`, where `discrep` lives.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

namespace MMP.Flips

open MMP.Mori

/-- FA 4.12.2.1 over an arbitrary field of characteristic zero: for a klt pair `(X, D)` with `D`
effective, every exceptional divisor of small log discrepancy outside a finite set has its center
in codimension `2` on a single component `P` of `D`, where `X` and `P` are regular;
`IsKawamataLogTerminal.exists_finite_forall_logDiscrepancy_lt_min` is the special case of an
algebraically closed field. -/
public theorem IsKawamataLogTerminal.exists_finite_forall_logDiscrepancy_lt_min_of_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (h : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor D)) (hD : D.IsEffective) :
    ∃ 𝒩 : Set (Valuation X.functionField ℤᵐ⁰), 𝒩.Finite ∧
      (∀ ν ∈ 𝒩, HasNonemptyCenter k sX ν ∧
        ∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) ∧
      ∀ ν : Valuation X.functionField ℤᵐ⁰, ν ∉ 𝒩 → HasNonemptyCenter k sX ν →
        (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) →
        ∀ b : ℝ, IsLogDiscrepancy sX n K (QDivisor.toRDivisor D) ν b →
          (b : EReal) < min 2 (1 + (1 + discrep sX n D)) →
          ∃ P : Mori.PrimeDivisor X, 0 < D.coeff P ∧ 2 - (D.coeff P : ℝ) ≤ b ∧
            ∀ E : ProperDivisorOver k sX, E.valuation = ν →
              codimension E.center = 2 ∧ (E.center : Set X) ⊆ P.support ∧
              (∀ Q : Mori.PrimeDivisor X, D.coeff Q ≠ 0 → (E.center : Set X) ⊆ Q.support →
                Q = P) ∧
              IsRegularLocalRing (X.presheaf.stalk E.center.isIrreducible.genericPoint) ∧
              IsRegularLocalRing (X.presheaf.stalk E.center.isIrreducible.genericPoint ⧸
                IdealSheafData.stalk P.idealSheaf E.center.isIrreducible.genericPoint) :=
  MMP.FourfoldProofs.Fa4KltSmallLogDiscrepancyCentersProof.solution sX h hD

/-- **FA 4.12.2.1.** Let `(X, D)` be a Kawamata log terminal pair, `X` of dimension `n` with
canonical divisor `K`, and `D` an effective `ℚ`-divisor. There is a finite set `𝒩` of exceptional
divisors of `k(X)` with nonempty center on `X` such that every exceptional divisor `ν ∉ 𝒩` of
`k(X)` with nonempty center on `X` and log discrepancy
`a_ℓ(ν, X, D) = b < min {2, 2 + discrep(X, D)}` has a component `P` of `D` with `D.coeff P > 0`
and `2 - D.coeff P ≤ b`, such that the center `W` of `ν` has codimension `2`, lies in `P` and in
no other component of `D`, and both `𝒪_{X,η_W}` and `𝒪_{X,η_W} / I_{P,η_W}` are regular local
rings. -/
@[mmp "lem_fa4_klt_small_log_discrepancy_centers"]
public theorem IsKawamataLogTerminal.exists_finite_forall_logDiscrepancy_lt_min {k : Type u}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : QDivisor X}
    (h : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor D)) (hD : D.IsEffective) :
    ∃ 𝒩 : Set (Valuation X.functionField ℤᵐ⁰), 𝒩.Finite ∧
      (∀ ν ∈ 𝒩, HasNonemptyCenter k sX ν ∧
        ∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) ∧
      ∀ ν : Valuation X.functionField ℤᵐ⁰, ν ∉ 𝒩 → HasNonemptyCenter k sX ν →
        (∃ E : ProperDivisorOver k sX, E.IsExceptional ∧ E.valuation = ν) →
        ∀ b : ℝ, IsLogDiscrepancy sX n K (QDivisor.toRDivisor D) ν b →
          (b : EReal) < min 2 (1 + (1 + discrep sX n D)) →
          ∃ P : Mori.PrimeDivisor X, 0 < D.coeff P ∧ 2 - (D.coeff P : ℝ) ≤ b ∧
            ∀ E : ProperDivisorOver k sX, E.valuation = ν →
              codimension E.center = 2 ∧ (E.center : Set X) ⊆ P.support ∧
              (∀ Q : Mori.PrimeDivisor X, D.coeff Q ≠ 0 → (E.center : Set X) ⊆ Q.support →
                Q = P) ∧
              IsRegularLocalRing (X.presheaf.stalk E.center.isIrreducible.genericPoint) ∧
              IsRegularLocalRing (X.presheaf.stalk E.center.isIrreducible.genericPoint ⧸
                IdealSheafData.stalk P.idealSheaf E.center.isIrreducible.genericPoint) :=
  IsKawamataLogTerminal.exists_finite_forall_logDiscrepancy_lt_min_of_charZero sX h hD

end MMP.Flips

end
