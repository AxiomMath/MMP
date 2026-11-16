module

public import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction

/-!
# Log resolutions of klt pairs satisfying the pair condition (FA 4.12.2)

Let `(X, D)` be a Kawamata log terminal log variety over a field of characteristic zero. There is
a log resolution `f : Y ⟶ X` of `(X, D)` whose exceptional set `Ex(f)` is the union of the
`f`-exceptional prime divisors and such that any two distinct meeting prime divisors of `Y`, each
exceptional or a component of `f⁻¹_* D`, have log discrepancies with sum at least `2`.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_isLogResolution_two_le_logDiscrepancy_add`

## Implementation notes

One starts from a Kollár–Mori log resolution (`MMP.Mori.exists_isLogResolution`) and blows up
bad components of intersections of pairs of divisors; termination uses integer weights bounding
the log discrepancies from below and the Dershowitz–Manna order on multisets. The auxiliary
lemmas live in the namespace `Proof_lem_fa4_resolution_blowups_achieve_pair_condition`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Proof_lem_fa4_resolution_blowups_achieve_pair_condition

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

/-- A prime divisor lies in a closed set exactly when its generic point does. -/
private theorem support_subset_iff {Y : Scheme.{u}} (P : Mori.PrimeDivisor Y) {T : Set Y}
    (hT : IsClosed T) : (P.support : Set Y) ⊆ T ↔ P.genericPoint ∈ T := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact ⟨fun h => h (subset_closure rfl),
    fun h => closure_minimal (Set.singleton_subset_iff.mpr h) hT⟩

/-- A prime divisor whose generic point lies on another one is that one. -/
private theorem eq_of_genericPoint_mem_support {Y : Scheme.{u}} {P Q : Mori.PrimeDivisor Y}
    (h : P.genericPoint ∈ (Q.support : Set Y)) : P = Q :=
  PrimeDivisorUnion.eq_of_support_subset
    ((support_subset_iff P (PrimeDivisorUnion.isClosed_support Q)).mpr h)

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

/-- The coefficients of the reduced divisor of `s` are `0` or `1`. -/
private theorem coeff_reducedDivisorOf_eq_zero_or_eq_one {Y : Scheme.{u}}
    (s : Finset (Mori.PrimeDivisor Y)) (P : Mori.PrimeDivisor Y) :
    (MMP.Intersection.reducedDivisorOf s).coeff P = 0 ∨
      (MMP.Intersection.reducedDivisorOf s).coeff P = 1 := by
  classical
  rw [MMP.Intersection.coeff_reducedDivisorOf]
  split_ifs <;> simp

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
      ((MMP.Intersection.support_reducedDivisorOf s).trans (support_sum_single s).symm)).mpr hsnc⟩

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
      exact closure_mono
        (Set.singleton_subset_iff.mpr ⟨primeDivisor_genericPoint_mem_support P, hP⟩)
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · exact Set.singleton_subset_iff.mpr
      ⟨⟨P.genericPoint, hP⟩, primeDivisor_genericPoint_mem_support P, rfl⟩

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

/-- **Valuative criterion at a divisor.** For a proper birational morphism `f : Y ⟶ X` onto a
normal scheme, the generic point of each prime divisor `Q` of `X` is the image of the generic point
of a prime divisor of `Y`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {Y X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsProper f] (hf : IsBirationalMorphism f) (Q : Mori.PrimeDivisor X) :
    ∃ E : Mori.PrimeDivisor Y, f E.genericPoint = Q.genericPoint := by
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
  obtain ⟨E, rfl⟩ : ∃ E : Mori.PrimeDivisor Y, E.genericPoint = x :=
    ⟨_, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco⟩
  exact ⟨E, hx⟩

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{X,Q} ⟶ 𝒪_{Y,E}` is an isomorphism, then `v_E`, seen on
`k(X)` through `f`, is `v_Q`. -/
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
  haveI := hf.isDominant
  obtain ⟨Γ, hΓ, -⟩ := exists_valuationOver_eq f P hP
  have htr := transformPrimeDivisor_inverse_eq_some hX f hY hf Γ P hΓ
  have huniq : ∀ Γ', MMP.Mori.RationalMap.transformPrimeDivisor
      (MMP.Mori.RationalMap.IsBirational.inverse hf) Γ' = some P → Γ' = Γ := by
    intro Γ' h'
    obtain ⟨P', hP'⟩ := exists_primeDivisor_map_genericPoint_eq f hf Γ'
    have h'' := transformPrimeDivisor_inverse_eq_some hX f hY hf Γ' P' hP'
    rw [h'] at h''
    obtain rfl := Option.some.inj h''
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP'.symm.trans hΓ)
  have hc : (birationalInverseTransform f hf D).coeff P = D.coeff Γ :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr huniq D
  rw [hc, hΓ]
  refine ⟨fun h => DivisorWithCoeffs.mem_supp_iff.mpr
    ⟨Γ, h, primeDivisor_genericPoint_mem_support Γ⟩, fun h => ?_⟩
  obtain ⟨E, hE, hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rwa [eq_of_genericPoint_mem_support hmem]

/-- The exceptional set of `f`, the points with no open neighbourhood on which `f` is an open
immersion, lies in the complement of the preimage of the biregular locus. -/
private theorem flipsExceptionalSet_subset {Y : Scheme.{u}} (f : Y ⟶ X) :
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
  have hsp : P.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
    exact specializes_iff_mem_closure.mpr hy
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

/-- The exceptional set of a composite. -/
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
private theorem IsLD.unique {Y : Scheme.{u}} {f : Y ⟶ X} {P : Mori.PrimeDivisor Y} {a a' : ℝ}
    (h : IsLD sX n K D f P a) (h' : IsLD sX n K D f P a') : a = a' := by
  obtain ⟨hY, hf, hp, b, hb, rfl⟩ := h
  obtain ⟨hY', hf', hp', b', hb', rfl⟩ := h'
  rw [IsDiscrepancy.eq hb hb']

omit [CharZero k] in
/-- The reduced sum of the configuration is an snc divisor in the sense of FA. -/
private theorem isSNCDivisor_reducedDivisorOf {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {s : Finset (Mori.PrimeDivisor Y)} (hsnc : (MMP.Intersection.reducedDivisorOf s).IsSNC sY) :
    IsSNCDivisor sY (MMP.Intersection.reducedDivisorOf s) :=
  ⟨coeff_reducedDivisorOf_eq_zero_or_eq_one s, hsnc.1, fun p _ => hsnc.2 p⟩

/-- **The log discrepancy of a divisor over a stratum.** Let `f : Y ⟶ X` be a log resolution with
configuration `∑ H_k`, and `ν` a divisor over `Y` whose center lies in `P ∩ Q` for two distinct
configuration divisors. Then `a_ℓ(P) + a_ℓ(Q) ≤ a_ℓ(ν)` over `(X, D)`. -/
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
  have hn : topologicalKrullDim X = n := hklt.2.1.topologicalKrullDim_eq
  obtain ⟨hYnv, hYdim, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hX
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
    rw [hDY]
    abel
  have hpb : IsRCartierPullback f (Divisor.toRDivisor (divisorOfForm ω) + D)
      (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L, L', hLc, hsum, fun j => ⟨_, hL' j⟩, hDYsum⟩
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hωY0 : ωY ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
      hfb.functionFieldMap_bijective hd hω0
  have hnY : topologicalKrullDim Y = n := hYdim.trans hn
  have hKY : (divisorOfForm ωY).IsCanonicalDivisor (f ≫ sX) n := by
    obtain ⟨K₀, hK₀⟩ :=
      MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hlog.isSmoothScheme hnY
    exact hK₀.of_linearlyEquivalent <| by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYnv hK₀ hωY0
  have hKDY : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ωY) + DY) :=
    ⟨m, r, L', fun j => (hL' j).isCartier (hLc j), by
      rw [hDYsum]
      simp only [toRDivisor_eq_mapCoeffs]⟩
  have hcrep := isDiscrepancy_comap_functionFieldMap_iff hX hω0 hK hKD f hYnv hfb hpb hKY
  have hprime : ∀ R : Mori.PrimeDivisor Y,
      IsDiscrepancy sX n (divisorOfForm ω) D (R.valuationOver f) (-DY.coeff R) := by
    intro R
    let ER : ProperDivisorOver k (f ≫ sX) :=
      ⟨DivisorOver.ofPrimeDivisor k hYnv R, (inferInstance : IsProper (𝟙 Y))⟩
    have hER : ER.valuation = R.divisorialValuation := Valuation.ext fun g => by
      change R.divisorialValuation (functionFieldMap (𝟙 Y) g) = _
      rw [MMP.Mori.functionFieldMap_id_apply]
    have h1 := isDiscrepancy_divisorialValuation hYnv ωY hωY0 hKY hKDY R
    rw [← hER] at h1
    have h2 := (hcrep ER _).mpr h1
    rwa [hER] at h2
  have hIsLD : ∀ R : Mori.PrimeDivisor Y,
      IsLD sX n (divisorOfForm ω) D f R (1 - DY.coeff R) :=
    fun R => ⟨hYnv, hfb, inferInstance, -DY.coeff R, hprime R, by ring⟩
  have hpos : ∀ R ∈ s, 0 ≤ 1 - DY.coeff R := fun R _ => (IsLD.pos hklt (hIsLD R)).le
  have hP1 : aP = 1 - DY.coeff P := IsLD.unique haP (hIsLD P)
  have hQ1 : aQ = 1 - DY.coeff Q := IsLD.unique haQ (hIsLD Q)
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
      exact hRD (hΓ ▸ DivisorWithCoeffs.mem_supp_iff.mpr
        ⟨Γ, h0, primeDivisor_genericPoint_mem_support Γ⟩)
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

open PrimeDivisorUnion StratumBlowup SNCBlowup MMP.Threefold.Resolution in
omit [CharZero k] in
/-- The exceptional set of the blow-up of a smooth centre of codimension two is the preimage of
the centre. -/
private theorem coe_exceptionalSet_blowUpToBase {Y : Scheme.{u}} [IsIntegral Y]
    {sY : Y ⟶ Spec (.of k)} {I : Y.IdealSheafData} (h : Resolution.IsSmoothBlowup sY I)
    (hirr : IsIrreducible (I.support : Set Y))
    (hc2 : codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) = 2) :
    (Mori.exceptionalSet (blowUpToBase I) : Set (blowUp I)) = blowUpToBase I ⁻¹' I.support := by
  have hc : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds Y) := by
    rw [hc2]
    norm_num
  ext x
  constructor
  · intro hx
    by_contra hxI
    exact Mori.mem_exceptionalSet.mp hx (mem_biregularLocus_of_notMem I hxI)
  · intro hxI
    refine Mori.mem_exceptionalSet.mpr fun hb => ?_
    set E := excE sY h hirr hc
    have hxE : x ∈ (E.support : Set (blowUp I)) := by rwa [coe_support_excE]
    have hsp : E.genericPoint ⤳ x := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
      exact specializes_iff_mem_closure.mpr hxE
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
  obtain ⟨I, hirr, hIsm, hWI, hIsub, hIst, -, hIv⟩ := exists_centre (f ≫ sX) hsnc hPT hQT hPQ
    hW.1.1.2.isPreconnected hW.1.1.1
    (hW.1.2.trans Set.inter_subset_left)
    (hW.1.2.trans Set.inter_subset_right)
  have hIW : (I.support : Set Y) = W := (hW.2 ⟨hirr, hIsub⟩ hWI).antisymm hWI
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
    rw [hc2]
    norm_num
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
        ((support_sum_single _).trans (MMP.Intersection.support_reducedDivisorOf _).symm)).mpr this
  have hle : Mori.exceptionalSet f ⊔ (DivisorWithCoeffs.supp D).preimage f.continuous ≤
      DivisorWithCoeffs.supp Δ := by
    intro y hy
    change y ∈ (DivisorWithCoeffs.supp Δ : Set Y)
    rw [hΔsupp, hs]
    exact hy
  have hlog' : Mori.IsLogResolution sX D (π ≫ f) := hlog.comp hle hπlog
  obtain ⟨hY'nv, -, -⟩ := hlog'.toIsSmoothResolution.isNormalVariety hX
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
      have h0 : E.genericPoint ∈ (E.support : Set (blowUp I)) :=
        primeDivisor_genericPoint_mem_support E
      rwa [coe_support_excE] at h0
    rw [← h, hstη] at h1
    exact hGI G h1
  have hstinj : Function.Injective st := fun G₁ G₂ h =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hstη G₁).symm.trans ((congrArg (fun R => π R.genericPoint) h).trans (hstη G₂)))
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
  have hstsupp : ∀ G : Mori.PrimeDivisor Y, ((st G).support : Set (blowUp I)) =
      closure (π ⁻¹' ((G.support : Set Y) \ W)) := by
    intro G
    apply le_antisymm
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ?_)
      rw [Set.mem_preimage, hstη]
      exact ⟨primeDivisor_genericPoint_mem_support G, fun h => hGI G (hIW ▸ h)⟩
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
      (by dsimp only; rwa [hD G₁ hG₁T, hD G₂ hG₂T])
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
  let w' : Mori.PrimeDivisor Y' → ℕ := Function.extend st w fun _ => w P + w Q
  have hw'st : ∀ G, w' (st G) = w G := hstinj.extend_apply w _
  have hw'E : w' E = w P + w Q :=
    Function.extend_apply' _ _ _ fun ⟨G, hG⟩ => hstE G hG
  have hwP := hG.weight P hP
  have hwQ := hG.weight Q hQ
  have hG' : Good sX n K D c (π ≫ f) w' := by
    refine ⟨hlog', fun R hR' => ?_⟩
    rcases (hR R).mp hR' with rfl | ⟨G, hG₀, rfl⟩
    · refine ⟨by rw [hw'E]; omega, fun b hb => ?_⟩
      rw [hw'E]
      have h0 := hEb b hb
      have h1 := hwP.2 aP haP
      have h2 := hwQ.2 aQ haQ
      push_cast
      linarith
    · rw [hw'st]
      exact ⟨(hG.weight G hG₀).1, fun a ha => (hG.weight G hG₀).2 a ((hLD G a).mp ha)⟩
  have hbound : ∀ b ∈ (finite_isBad (n := n) (K := K) hlog').toFinset,
      w' b.1 + w' b.2.1 < N := by
    rintro ⟨R₁, R₂, C⟩ hb
    rw [Set.Finite.mem_toFinset] at hb
    obtain ⟨hR₁, hR₂, -, -, a, a', ha, ha', hlt⟩ := hb
    have h1 := (hG'.weight R₁ hR₁).2 a ha
    have h2 := (hG'.weight R₂ hR₂).2 a' ha'
    have : (c : ℝ) * ((w' R₁ + w' R₂ : ℕ) : ℝ) < c * N := by push_cast; linarith
    exact_mod_cast lt_of_mul_lt_mul_left this hc.le
  let down : Mori.PrimeDivisor Y' → Mori.PrimeDivisor Y := Function.extend st id fun _ => P
  have hdown : ∀ G, down (st G) = G := hstinj.extend_apply id _
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
    change N - (w' b.1 + w' b.2.1) < N - (w P + w Q)
    rcases hpb with h | h
    · rw [h, hw'E] at hbd h1 ⊢
      omega
    · rw [h, hw'E] at hbd h2 ⊢
      omega

/-- From a `Good` model there is a Kollár–Mori log resolution of `(X, D)` with no bad triples. -/
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
    ∃ c : ℝ, 0 < c ∧ ∃ (Y : Scheme.{u}) (f : Y ⟶ X), Good sX n K D c f fun _ => 1 := by
  classical
  obtain ⟨Y, f, hlog⟩ := MMP.Mori.exists_isLogResolution sX hklt.1.isNormalVariety D
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
  · rcases Finset.mem_insert.mp (A.min'_mem hA) with h | h
    · exact h ▸ one_pos
    · obtain ⟨P, -, hP⟩ := Finset.mem_image.mp h
      exact hP ▸ hgpos P
  · have hPs : P ∈ s := support_subset_iUnion_iff.mp (hs ▸ hP)
    have hgP : g P = a := by
      have h : ∃ a, IsLD sX n K D f P a := ⟨a, ha⟩
      simp only [g, dif_pos h]
      exact IsLD.unique h.choose_spec ha
    rw [Nat.cast_one, mul_one, ← hgP]
    exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g hPs))

omit [CharZero k] in
/-- **The exceptional set of a Kollár–Mori log resolution.** Its `Ex(f)` is the union of the
supports of the `f`-exceptional prime divisors. -/
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
    have hyM : y ∈ (Mori.exceptionalSet f : Set Y) := flipsExceptionalSet_subset f hy
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
      (hW.1.2 (hEW ▸ primeDivisor_genericPoint_mem_support E)), hEW ▸ hyW⟩
  · rintro ⟨P, hP, hyP⟩
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    exact support_subset_flipsExceptionalSet hn hP hyP

/-- A Kollár–Mori log resolution without bad triples has the required properties. -/
private theorem isLogResolution_and_pairCondition_of_forall_not_isBad
    (hklt : IsKawamataLogTerminal sX n K D) {Y : Scheme.{u}} {f : Y ⟶ X}
    (hlog : Mori.IsLogResolution sX D f) (hno : ∀ t, ¬ IsBad sX n K D f t) :
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
    MMP.Intersection.reducedDivisorOf s, coeff_reducedDivisorOf_eq_zero_or_eq_one s, fun P => ?_,
    isSNCDivisor_reducedDivisorOf hsnc⟩, flipsExceptionalSet_eq_iUnion hklt hlog, ?_⟩
  · rw [MMP.Intersection.coeff_reducedDivisorOf, or_comm, ← hmem]
    split_ifs with h <;> simp [h]
  · intro hY' hf' hp' P Q hPQ hP hQ hPQne a b ha hb
    have hP' : (P.support : Set Y) ⊆ cfg D f :=
      hs ▸ support_subset_iUnion_iff.mpr ((hmem P).mpr hP)
    have hQ' : (Q.support : Set Y) ⊆ cfg D f :=
      hs ▸ support_subset_iUnion_iff.mpr ((hmem Q).mpr hQ)
    obtain ⟨x, hx⟩ := hPQne
    obtain ⟨W, hW, -⟩ := MMP.Resolution.exists_mem_componentsOf hx
    by_contra hlt
    exact hno (P, Q, W) ⟨hP', hQ', hPQ, hW, a, b, ⟨hY', hf', hp', ha⟩, ⟨hY', hf', hp', hb⟩,
      not_le.mp hlt⟩

end Main

end Proof_lem_fa4_resolution_blowups_achieve_pair_condition

namespace MMP.Flips

open MMP.Mori

open Proof_lem_fa4_resolution_blowups_achieve_pair_condition

/-- **Log resolutions with the pair condition (FA 4.12.2).** Let `(X, D)` be a Kawamata log
terminal log variety over a field `k` of characteristic zero, with canonical divisor `K` of
dimension `n`. There is a log resolution `f : Y ⟶ X` of `(X, D)` such that `Ex(f)` is the union
of the supports of the prime divisors of `Y` exceptional over `X`, and such that for any two
distinct prime divisors `P ≠ Q` of `Y`, each either exceptional over `X` or a component of
`f⁻¹_* D`, with `P ∩ Q ≠ ∅`, the log discrepancies satisfy `a_ℓ(P, X, D) + a_ℓ(Q, X, D) ≥ 2`. -/
@[mmp "lem_fa4_resolution_blowups_achieve_pair_condition"]
public theorem IsKawamataLogTerminal.exists_isLogResolution_two_le_logDiscrepancy_add
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K : Divisor X} {D : RDivisor X} (hklt : IsKawamataLogTerminal sX n K D) :
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
  exact ⟨Y, f, isLogResolution_and_pairCondition_of_forall_not_isBad hklt hlog hno⟩

end MMP.Flips

end
