module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativeBasepointFree
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
public import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.Singularities.UniformLowDiscrepanciesNearKlt
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil
public import MMP.AlgebraicGeometry.FiberSpace.NumericallyTrivialDescent
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
public import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula
public import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres

section

open CategoryTheory AlgebraicGeometry
open scoped WithZero

universe u

namespace MMP.Flips.ProperDivisorOver

open MMP.Mori

/-- For a proper birational morphism `f : Y ⟶ X` from a normal variety, every divisor `D` over
`X` has the valuation of a divisor `E` over `Y`, read on `k(X)` through `f^*`. -/
private theorem exists_comap_functionFieldMap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
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
          D.valuation (algebraMap _ X.functionField b) := fun b => by
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
    · rw [hga]
      exact (g.hom a).2
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

end MMP.Flips.ProperDivisorOver

end

section

/-!
# Adjoints across a projective numerically trivial small modification

Let `φ : X ⟶ T` and `ψ : Y ⟶ T` be small proper birational morphisms of normal projective
varieties and `(X, Δ)` a klt pair with `K_X + Δ` numerically `φ`-trivial. The basepoint-free
theorem makes a Cartier multiple `D = r(K_X + Δ)` relatively free over `T`, and the descent of
relatively free numerically trivial divisors makes `φ_* D = r(K_T + Δ_T)` Cartier. Since `φ` and
`ψ` contract no prime divisor, the inverse transform of a divisor along either map undoes its
transform, and the pull-back of a Cartier divisor is its inverse transform. So
`r(K_X + Δ) = φ^* r(K_T + Δ_T)` and `r(K_Y + Δ_Y) = ψ^* r(K_T + Δ_T)` as Weil divisors. Eventual
freeness and free pencils then pass through `T` by the crepant comparison along morphisms with
`φ_* 𝒪_X = 𝒪_T`. The images of the free linear systems are compared through `T`, and klt
transfers through the crepant pull-backs.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne`

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4.4, 15.9
-/

open CategoryTheory AlgebraicGeometry
open scoped WithZero

namespace MMP.FourfoldProofs.FourfoldFa15ProjectiveTrivialFlopBundleProof

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP MMP.Flips MMP.Mori

section Coefficients

variable {X Y : Scheme.{0}}

/-- Relabelling prime divisors commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem toQDivisor_mapPrimeDivisors (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y))
    (D : Divisor X) :
    Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single E c =>
    have hs : Divisor.toQDivisor (Finsupp.single E c) = Finsupp.single E (c : ℚ) :=
      Finsupp.mapRange_single (hf := map_zero _)
    rw [hs, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E with
    | none => simp
    | some F =>
      exact Finsupp.mapRange_single (hf := map_zero _)

end Coefficients

/-! ### Small birational morphisms -/

section Small

variable {X T : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]

/-- The generic point of a prime divisor lies outside every closed subset of codimension at
least two. -/
private theorem genericPoint_notMem_of_two_le_closedsCodimension {Z : Scheme.{0}}
    (P : Mori.PrimeDivisor Z) {V : TopologicalSpace.Closeds Z} (hV : 2 ≤ closedsCodimension V) :
    P.genericPoint ∉ (V : Set Z) := by
  intro h
  have h2 := (le_closedsCodimension_iff.mp hV)
    (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
    (V.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h))
  have h1 : codimension (TopologicalSpace.IrreducibleCloseds.closureSingleton
      P.genericPoint) = 1 := P.codimension_one
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- A morphism which is an isomorphism in codimension one maps the generic point of a prime
divisor to a point of codimension one. -/
private theorem coheight_map_genericPoint_eq_one {g : X ⟶ T} (hgs : IsIsoInCodimOne g)
    (P : Mori.PrimeDivisor X) : Order.coheight (g P.genericPoint) = 1 := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := hgs
  have hPV := genericPoint_notMem_of_two_le_closedsCodimension P hV
  let U : X.Opens := V.compl
  let U' : T.Opens := W.compl
  let q : U.toScheme := ⟨P.genericPoint, hPV⟩
  let e : U.toScheme ⟶ U'.toScheme := g.resLE U' U hle
  haveI : IsIso e := hiso
  have e1 : Order.coheight (U.ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding
  have e2 : Order.coheight (e q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ e.isOpenEmbedding
  have e3 : Order.coheight (U'.ι (e q)) = Order.coheight (e q) :=
    Topology.IsOpenEmbedding.coheight_eq _ U'.ι.isOpenEmbedding
  have h : U'.ι (e q) = g P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rfl
  rw [← h, e3, e2, ← e1]
  exact P.coheight_genericPoint

/-- Along a small birational morphism `g : X ⟶ T`, the inverse transform undoes the transform:
no prime divisor of `X` is contracted. -/
private theorem inverseTransformDivisor_transformDivisor {g : X ⟶ T} [IsProper g]
    [IsSeparated (T ↘ ⊤_ Scheme)] (hg : IsBirationalMorphism g) (hgs : IsIsoInCodimOne g)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    inverseTransformDivisor g (RationalMap.transformDivisor g.toRationalMap D) = D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h']
  | single P c =>
    have hco := coheight_map_genericPoint_eq_one hgs P
    rw [RationalMap.transformDivisor_single_of_eq_some
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g P _).mpr
        (PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm),
      inverseTransformDivisor_single_of_eq_some
        (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
          (PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
          (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hco.le))]

/-- Along a small birational morphism, the coefficient of an inverse transform at a prime divisor
`P` is the coefficient at the image prime divisor. -/
private theorem coeff_inverseTransformDivisor {g : X ⟶ T} [IsProper g]
    [IsSeparated (T ↘ ⊤_ Scheme)] (hg : IsBirationalMorphism g) (hgs : IsIsoInCodimOne g)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R T) (P : Mori.PrimeDivisor X) :
    (inverseTransformDivisor g D).coeff P =
      D.coeff (PrimeDivisor.ofCoheightOne (g P.genericPoint)
        (coheight_map_genericPoint_eq_one hgs P)) := by
  have hco := coheight_map_genericPoint_eq_one hgs P
  have hE := PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hbir := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hco.le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hE.symm
      hbir) (fun E' hE' => ?_) D
  exact PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hE').1.symm.trans hE.symm)

/-- Along a small birational morphism `g : X ⟶ T`, the pull-back of a Cartier divisor is its
inverse transform: no prime divisor of `X` is `g`-exceptional. -/
private theorem exists_isPullback_of_inverseTransformDivisor_eq {g : X ⟶ T} [IsProper g]
    [IsSeparated (T ↘ ⊤_ Scheme)] (hg : IsBirationalMorphism g) (hgs : IsIsoInCodimOne g)
    {M : Divisor T} (hM : M.IsCartier) {M' : Divisor X} (hM' : inverseTransformDivisor g M = M') :
    ∃ hB : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ M.supp,
      M.IsPullback g hB M' := by
  subst hM'
  haveI : IsDominant g := hg.isDominant
  have hB := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant g M
  refine ⟨hB, ?_⟩
  have hpb := Divisor.isPullback_pullback hM hB
  convert hpb using 1
  refine Finsupp.ext fun P => ?_
  have hco := coheight_map_genericPoint_eq_one hgs P
  have hbir := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hco.le
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus g hbir
  rw [← DivisorWithCoeffs.coeff_apply (M.pullback hM hB),
    MMP.Positivity.coeff_eq_of_isPullback P _ (PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
      hM hpb, ← DivisorWithCoeffs.coeff_apply, coeff_inverseTransformDivisor hg hgs]

/-- Along a small birational morphism, the coefficient of a transform at the image of a prime
divisor `P` is the coefficient at `P`. -/
private theorem coeff_transformDivisor {g : X ⟶ T} [IsProper g]
    [IsSeparated (T ↘ ⊤_ Scheme)] (hg : IsBirationalMorphism g) (hgs : IsIsoInCodimOne g)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) (P : Mori.PrimeDivisor X) :
    (RationalMap.transformDivisor g.toRationalMap D).coeff
        (PrimeDivisor.ofCoheightOne (g P.genericPoint) (coheight_map_genericPoint_eq_one hgs P)) =
      D.coeff P := by
  rw [← coeff_inverseTransformDivisor hg hgs, inverseTransformDivisor_transformDivisor hg hgs]

/-- A morphism which is an isomorphism in codimension one hits the generic point of every prime
divisor of the target with the generic point of a prime divisor of the source. -/
private theorem exists_map_genericPoint_eq {g : X ⟶ T} (hgs : IsIsoInCodimOne g)
    (E : Mori.PrimeDivisor T) : ∃ P : Mori.PrimeDivisor X, g P.genericPoint = E.genericPoint := by
  obtain ⟨V, W, -, hW, hle, hiso⟩ := hgs
  have hEW := genericPoint_notMem_of_two_le_closedsCodimension E hW
  let U : X.Opens := V.compl
  let U' : T.Opens := W.compl
  let e : U.toScheme ⟶ U'.toScheme := g.resLE U' U hle
  haveI : IsIso e := hiso
  let y : U'.toScheme := ⟨E.genericPoint, hEW⟩
  let q : U.toScheme := (inv e) y
  have hq : e q = y := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have h : g (U.ι q) = E.genericPoint := by
    have : U'.ι (e q) = g (U.ι q) := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rw [← this, hq]
    rfl
  have e1 : Order.coheight (U.ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding
  have e2 : Order.coheight (e q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ e.isOpenEmbedding
  have e3 : Order.coheight (U'.ι y) = Order.coheight y :=
    Topology.IsOpenEmbedding.coheight_eq _ U'.ι.isOpenEmbedding
  have hco : Order.coheight (U.ι q) = 1 := by
    rw [e1, ← e2, hq, ← e3]
    exact E.coheight_genericPoint
  exact ⟨PrimeDivisor.ofCoheightOne _ hco,
    (congrArg g (PrimeDivisor.genericPoint_ofCoheightOne _ hco)).trans h⟩

/-- Along a small birational morphism over a perfect field, the divisor of the pull-back of a
rational form is the inverse transform of its divisor. -/
private theorem divisorOfForm_pullbackRationalPluriForms {k : Type} [Field k] [PerfectField k]
    {sT : T ⟶ Spec (.of k)} [LocallyOfFiniteType sT] {g : X ⟶ T} [IsProper g]
    [IsSeparated (T ↘ ⊤_ Scheme)] (hg : IsBirationalMorphism g) (hgs : IsIsoInCodimOne g)
    [LocallyOfFiniteType (g ≫ sT)] {d : ℕ}
    (hd : letI := functionFieldAlgebra sT; (Algebra.trdeg k T.functionField).toNat = d)
    (ω : RationalPluriForms sT d 1) :
    haveI : IsDominant g := hg.isDominant
    divisorOfForm (pullbackRationalPluriForms sT g ω) =
      inverseTransformDivisor g (divisorOfForm ω) := by
  haveI : IsDominant g := hg.isDominant
  refine Finsupp.ext fun P => ?_
  have hco := coheight_map_genericPoint_eq_one hgs P
  have hE := PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hbir := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hco.le
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus g hbir
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
    coeff_inverseTransformDivisor hg hgs, coeff_divisorOfForm, coeff_divisorOfForm]
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso g hg.functionFieldMap_bijective
    hd P _ hE.symm ω

end Small

/-! ### Pull-backs of `ℚ`-divisors from a Cartier multiple -/

section QPullback

variable {X T : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian T] [IsNormal T]

/-- A point outside the support of a divisor is outside the support of its multiples. -/
private theorem notMem_supp_zsmul {T : Scheme.{0}} {B : Divisor T} (n : ℤ) {x : T}
    (hx : x ∉ B.supp) : x ∉ (n • B).supp := by
  rw [DivisorWithCoeffs.mem_supp_iff] at hx ⊢
  rintro ⟨E, hE, hxE⟩
  refine hx ⟨E, fun h => hE ?_, hxE⟩
  rw [DivisorWithCoeffs.coeff_smul, h, smul_zero]

/-- If `rN` is a Cartier divisor `M` with pull-back `M'` and `M' = rL`, then `L` is the pull-back
of the `ℚ`-divisor `N`. -/
private theorem QDivisor.pullback_eq_of_isPullback {g : X ⟶ T} {N : QDivisor T}
    (hN : N.IsQCartier) {r : ℕ} (hr : 0 < r) {M : Divisor T} (hMc : M.IsCartier)
    (hM : Divisor.toQDivisor M = (r : ℤ) • N)
    {hB : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ M.supp}
    {M' : Divisor X} (hpb : M.IsPullback g hB M') {L : QDivisor X}
    (hL : Divisor.toQDivisor M' = (r : ℤ) • L)
    (hBN : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ N.supp) :
    N.pullback hN hBN = L := by
  refine QDivisor.IsPullback.pullback_eq hN ?_
  intro m hm D hD hDc
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hBD : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ D.supp := fun Z hZ =>
    hBN Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hD] at hZ)
  have hrD : (r : ℤ) • D = (m : ℤ) • M := Divisor.toQDivisor_injective (by
    rw [map_zsmul, map_zsmul, hD, hM, smul_smul, smul_smul, mul_comm])
  refine ⟨D.pullback hDc hBD, ?_, Divisor.isPullback_pullback hDc hBD⟩
  have h₁ := (Divisor.isPullback_pullback hDc hBD).zsmul hDc (r : ℤ)
    (fun Z => notMem_supp_zsmul _ (hBD Z))
  have h₂ := (hpb.zsmul hMc (m : ℤ) (fun Z => notMem_supp_zsmul _ (hB Z))).of_eq hrD.symm
    (hB₂ := fun Z => notMem_supp_zsmul _ (hBD Z))
  have h₃ := congrArg Divisor.toQDivisor (h₁.eq (hDc.zsmul _) h₂)
  rw [map_zsmul, map_zsmul, hL, smul_comm] at h₃
  exact smul_right_injective _ hr' h₃

end QPullback

section RealDivisors

variable {X : Scheme.{0}}

/-- If `M = r (D + Δ)` as `ℚ`-divisors, then `D + Δ = r⁻¹ M` as `ℝ`-divisors. -/
private theorem toRDivisor_add_eq_inv_smul {D M : Divisor X} {Δ : QDivisor X} {r : ℕ}
    (hr : 0 < r) (h : Divisor.toQDivisor M = (r : ℤ) • (Divisor.toQDivisor D + Δ)) :
    Divisor.toRDivisor D + QDivisor.toRDivisor Δ = ((r : ℝ)⁻¹) • Divisor.toRDivisor M := by
  ext E
  have h1 := congrArg (fun F : QDivisor X => F E) h
  change ((M.coeff E : ℤ) : ℚ) = (r : ℤ) • (((D.coeff E : ℤ) : ℚ) + Δ.coeff E) at h1
  change ((D.coeff E : ℤ) : ℝ) + ((Δ.coeff E : ℚ) : ℝ) = (r : ℝ)⁻¹ * ((M.coeff E : ℤ) : ℝ)
  have h2 : ((M.coeff E : ℤ) : ℝ) = (r : ℝ) * (((D.coeff E : ℤ) : ℝ) + ((Δ.coeff E : ℚ) : ℝ)) := by
    have := congrArg (Rat.cast : ℚ → ℝ) h1
    rw [zsmul_eq_mul] at this
    push_cast at this
    exact this
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [h2]
  field_simp

/-- If `M = r (D + Δ)` with `M` Cartier, then `D + Δ` is an `ℝ`-combination of Cartier
divisors. -/
private theorem isCartierCombination_of_toQDivisor_eq [IsLocallyNoetherian X] [IsNormal X]
    {D M : Divisor X} {Δ : QDivisor X} {r : ℕ} (hr : 0 < r) (hMc : M.IsCartier)
    (h : Divisor.toQDivisor M = (r : ℤ) • (Divisor.toQDivisor D + Δ)) :
    IsCartierCombination (Divisor.toRDivisor D + QDivisor.toRDivisor Δ) :=
  ⟨1, fun _ => (r : ℝ)⁻¹, fun _ => M, fun _ => hMc, by
    rw [Fin.sum_univ_one, ← toRDivisor_eq_mapCoeffs, toRDivisor_add_eq_inv_smul hr h]⟩

end RealDivisors

/-! ### The basepoint-free theorem and descent -/

section Descent

/-- On an integral proper scheme of dimension zero an invertible sheaf has a nonzero section. -/
private theorem finrank_ne_zero_of_dim_zero {κ : Type} [Field κ] {Z : Scheme.{0}}
    (g : Z ⟶ Spec (.of κ)) [IsProper g] [IsIntegral Z] [IsLocallyNoetherian Z]
    (hd : topologicalKrullDim Z = 0) (P : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 P] :
    Module.finrank κ (cohomologyOverField κ g P 0) ≠ 0 := by
  have hall : ∀ x : Z, x = genericPoint Z := by
    intro x
    have hmin := Order.krullDim_nonpos_iff_forall_isMin.1 (le_of_eq hd)
    let W : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    let T : TopologicalSpace.IrreducibleCloseds Z :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have hTW : T ≤ W := hmin T fun _ _ => Set.mem_univ _
    have hx : IsGenericPoint x ⊤ := by
      change closure {x} = Set.univ
      exact Set.eq_univ_of_univ_subset hTW
    exact hx.eq (genericPoint_spec Z)
  obtain ⟨U, -, e, hxU, he⟩ := MMP.Intersection.exists_isTrivializingGenerator P
    (show genericPoint Z ∈ (⊤ : Z.Opens) from trivial)
  have hU : U = ⊤ := eq_top_iff.2 fun y _ => by rwa [hall y]
  subst hU
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := (he ⊤ le_rfl).1 (a₁ := (1 : Γ(Z, ⊤))) (a₂ := 0) (by
      simp only [MMP.Intersection.modules_map_id, h0, smul_zero])
    exact one_ne_zero h1
  haveI : SheafOfModules.IsCoherent P :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z P
  haveI := finiteDimensional_cohomologyOverField_of_isProper κ g P 0
  haveI : Nontrivial (cohomologyOverField κ g P 0) :=
    @Equiv.nontrivial _ _ (cohomologyOverFieldZeroIsoSections κ g P).toLinearEquiv.toEquiv
      ⟨⟨e, 0, he0⟩⟩
  exact (Module.finrank_pos (R := κ) (M := cohomologyOverField κ g P 0)).ne'

/-- For a birational morphism of integral schemes, the residue field at the generic point of the
source is algebraic over that of its image. -/
private theorem residueFieldTranscendenceDegree_genericPoint_eq_zero {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsIntegral Z] (h : Y ⟶ Z) (hb : IsBirationalMorphism h) :
    residueFieldTranscendenceDegree h (genericPoint Y) = 0 := by
  haveI : IsDominant h := hb.isDominant
  have hbij := hb.functionFieldMap_bijective
  have hn := AlgebraicGeometry.residueFieldMap_comp_genericResidueEquivOfDominant h
  have hsurj : Function.Surjective (h.residueFieldMap (genericPoint Y)).hom := by
    intro x
    obtain ⟨y, hy⟩ := hbij.surjective ((AlgebraicGeometry.genericResidueEquiv Y).symm x)
    refine ⟨AlgebraicGeometry.genericResidueEquivOfDominant h y, ?_⟩
    have := congrArg (fun φ => φ y) hn
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, hy]
    simp
  letI := (h.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have : Algebra.IsAlgebraic (Z.residueField (h (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj x
    exact isAlgebraic_algebraMap a
  unfold residueFieldTranscendenceDegree
  rw [_root_.trdeg_eq_zero]
  simp

/-- For a birational morphism `h` of projective varieties the zero divisor is `h`-big. -/
private theorem isRelativelyBig_zero_of_isBirationalMorphism {k : Type} [Field k]
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sY]
    [AlgebraicGeometry.IsProjectiveVariety k sZ] (h : Y ⟶ Z) (hf : h ≫ sZ = sY)
    (hb : IsBirationalMorphism h) : (0 : QDivisor Y).IsRelativelyBig h := by
  haveI : IsProper (h ≫ sZ) := hf ▸ (inferInstance : IsProper sY)
  haveI : IsProper h := IsProper.of_comp h sZ
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hfib : topologicalKrullDim (h.fiber (h (genericPoint Y))) = 0 := by
    rw [MMP.Flips.topologicalKrullDim_fiber_genericPoint,
      residueFieldTranscendenceDegree_genericPoint_eq_zero h hb]
    rfl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, topologicalKrullDim Y = a := by
    have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sY
    have hbot : topologicalKrullDim Y ≠ ⊥ := fun hb =>
      ((Order.krullDim_eq_bot_iff.mp hb).false
        (TopologicalSpace.IrreducibleCloseds.closureSingleton (genericPoint Y))).elim
    induction hX : topologicalKrullDim Y using WithBot.recBotCoe with
    | bot => exact absurd hX hbot
    | coe a' =>
      have ha : a' ≠ ⊤ := by rintro rfl; exact h1 hX
      lift a' to ℕ using ha
      exact ⟨a', rfl⟩
  have hb' : topologicalKrullDim (closure (Set.range h.base)) = a := by
    have := MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range h k sY sZ hf
    rw [hfib, zero_add, ha] at this
    exact this.symm
  have hrank : relativeGenericRank h (0 : Divisor Y).divisorialSheaf ≠ 0 := by
    haveI := (Divisor.isCartier_zero (X := Y)).isInvertibleModule_divisorialSheaf
    haveI : IsProper (h.fiberToSpecResidueField (h (genericPoint Y))) :=
      inferInstanceAs (IsProper (Limits.pullback.snd h (Z.fromSpecResidueField _)))
    haveI : IsIntegral (h.fiber (h (genericPoint Y))) := MMP.Mori.isIntegral_generic_fibre h
    haveI := isLocallyNoetherian_fiber_of_locallyOfFiniteType h (h (genericPoint Y))
    rw [MMP.Mori.relativeGenericRank_eq_finrank_fibre h]
    exact finrank_ne_zero_of_dim_zero _ hfib _
  refine ⟨1, one_pos, 0, by simp, Divisor.isCartier_zero, a, a, ha, hb', 1 / 2, by norm_num, 0,
    fun m _ => ?_⟩
  rw [smul_zero, Nat.sub_self, pow_zero, mul_one]
  have : (1 : ℝ) ≤ relativeGenericRank h (0 : Divisor Y).divisorialSheaf :=
    mod_cast Nat.one_le_iff_ne_zero.2 hrank
  linarith

/-- A Cartier divisor of degree zero on every curve contracted by `φ` is `φ`-nef. -/
private theorem isRelativelyNef_of_degreeOn_eq_zero {k : Type} [Field k]
    {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (φ : X ⟶ T) {D : Divisor X} (hDc : D.IsCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy φ → D.degreeOn k sX C.ι C.dim_le hDc = 0) :
    (Divisor.toQDivisor D).IsRelativelyNef sX φ := by
  have hQ : (Divisor.toQDivisor D).IsQCartier := ⟨1, one_ne_zero, D, by simp, hDc⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hQ fun C hC => ?_
  rw [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le D hDc, h C hC]
  simp

/-- A Cartier multiple of a numerically `φ`-trivial `ℚ`-divisor has degree zero on every curve
contracted by `φ`. -/
private theorem degree_eq_zero_of_isNumericallyTrivialOver {k : Type} [Field k]
    {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (φ : X ⟶ T) {L : QDivisor X}
    (hL : IsNumericallyTrivialOver k sX φ (QDivisor.toRDivisor L))
    {m : ℕ} (hm : 0 < m) {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • L)
    (hDc : D.IsCartier) (C : Mori.ProperCurve sX) (hC : C.IsContractedBy φ) :
    haveI := hDc.isInvertibleModule_divisorialSheaf
    C.degree k D.divisorialSheaf = 0 := by
  haveI := hDc.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 D.divisorialSheaf :=
    ‹Stacks.Ample.IsInvertibleModule X D.divisorialSheaf›
  exact MMP.Flips.IsNumericallyTrivialOver.degree_eq_zero hL hm hD hDc C hC

/-- **Relative freeness of the adjoint** over an algebraically closed field. -/
private theorem exists_isRelativelyFreeDivisor_of_isAlgClosed {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hX : Mori.IsProjectiveVariety k sX) (hT : Mori.IsProjectiveVariety k sT)
    {φ : X ⟶ T} (hφT : φ ≫ sT = sX) [IsProper φ] (hφ : IsBirationalMorphism φ)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor Δ))
    (htriv : IsNumericallyTrivialOver k sX φ (QDivisor.toRDivisor (Divisor.toQDivisor K + Δ))) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + Δ) ∧
      D.IsCartier ∧ MMP.Fourfold.IsRelativelyFreeDivisor φ D := by
  haveI := hX
  haveI := hT
  have hXn : IsNormalVariety k sX := ⟨hX.toIsVariety, inferInstance⟩
  have hB : IsBoundary (QDivisor.toRDivisor Δ) := hklt.1.isBoundary
  have hQ : (Divisor.toQDivisor K + Δ).IsQCartier := by
    refine QDivisor.isQCartier_of_isCartierCombination ?_
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    exact hklt.2.2.1
  have hkltM : IsKltPair sX n K Δ :=
    (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sX n K Δ hXn hklt.2.1 hB hQ).1 hklt
  have hΔ : 0 ≤ Δ := fun P => by
    have h := (hB P).1
    rw [QDivisor.coeff_toRDivisor] at h
    exact_mod_cast h
  obtain ⟨r₀, hr₀, D, hD, hDc⟩ := hQ.exists_pos
  have hset : IsProjectiveSetting k sX sT φ := ⟨inferInstance, inferInstance, hX, hT, hφT⟩
  have hDnef : (Divisor.toQDivisor D).IsRelativelyNef sX φ :=
    isRelativelyNef_of_degreeOn_eq_zero φ hDc
      (degree_eq_zero_of_isNumericallyTrivialOver φ htriv hr₀ hD hDc)
  have hr₀' : (r₀ : ℚ) ≠ 0 := by exact_mod_cast hr₀.ne'
  have hzero : (1 / (r₀ : ℚ)) • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ = 0 := by
    rw [hD, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast, one_div,
      inv_mul_cancel₀ hr₀', one_smul, sub_sub, sub_self]
  have hnef : ((1 / (r₀ : ℚ)) • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsRelativelyNef
      sX φ := by
    rw [hzero]
    simpa using isRelativelyNef_of_degreeOn_eq_zero (sX := sX) φ (Divisor.isCartier_zero (X := X))
      fun C _ => Divisor.degreeOn_zero' k sX C.ι C.dim_le
  have hbig : ((1 / (r₀ : ℚ)) • Divisor.toQDivisor D - Divisor.toQDivisor K - Δ).IsRelativelyBig
      φ := by
    rw [hzero]
    exact isRelativelyBig_zero_of_isBirationalMorphism sX sT φ hφT hφ
  obtain ⟨b₀, hb₀⟩ := exists_forall_ge_isRelativelyFreeDivisor_of_isKltPair hset hkltM hΔ hDc
    hDnef (by positivity) hnef hbig
  refine ⟨(b₀ + 1) * r₀, by positivity, ((b₀ + 1 : ℕ) : ℤ) • D, ?_, hDc.zsmul _,
    hb₀ _ (Nat.le_succ b₀)⟩
  rw [map_zsmul, hD, smul_smul]
  push_cast
  rfl

/-- **Descent of a relatively free numerically trivial Cartier divisor along a small
contraction.** If `D = mL` is Cartier and `φ`-free, with `L` numerically `φ`-trivial, then
`φ_* D` is Cartier: `𝒪_X(D) ≅ φ^* 𝒪_T(B)` for a Cartier divisor `B` on `T`, so
`D = φ^* B - div(φ^* u)` and `φ_* D = B - div(u)`. -/
private theorem isCartier_transformDivisor_of_isRelativelyFreeDivisor {k : Type} [Field k]
    {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hX : Mori.IsProjectiveVariety k sX) (hT : Mori.IsProjectiveVariety k sT)
    {φ : X ⟶ T} (hφT : φ ≫ sT = sX) [IsProper φ] (hφ : IsBirationalMorphism φ)
    (hφs : IsIsoInCodimOne φ) {L : QDivisor X}
    (hL : IsNumericallyTrivialOver k sX φ (QDivisor.toRDivisor L))
    {m : ℕ} (hm : 0 < m) {D : Divisor X} (hD : Divisor.toQDivisor D = (m : ℤ) • L)
    (hDc : D.IsCartier) (hfree : MMP.Fourfold.IsRelativelyFreeDivisor φ D) :
    Divisor.IsCartier (RationalMap.transformDivisor φ.toRationalMap D) := by
  haveI : IsDominant φ := hφ.isDominant
  have hTn : IsNormalVariety k sT := ⟨hT.toIsVariety, inferInstance⟩
  have hXn : IsNormalVariety k (φ ≫ sT) := hφT ▸ ⟨hX.toIsVariety, inferInstance⟩
  have hφO : ∀ U : T.Opens, IsIso (φ.app U) :=
    MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism sX sT hX.toIsVariety hTn φ hφ
  have hcon : IsContraction k sT sX φ := ⟨hT.toIsVariety, hX.toIsVariety, hφT, inferInstance, hφO⟩
  haveI := hDc.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 D.divisorialSheaf :=
    ‹Stacks.Ample.IsInvertibleModule X D.divisorialSheaf›
  obtain ⟨Mₜ, hMₜ, ⟨e⟩⟩ := hcon.exists_isInvertible_pullback_iso D.divisorialSheaf hfree
    (degree_eq_zero_of_isNumericallyTrivialOver φ hL hm hD hDc)
  haveI : Stacks.Ample.IsInvertibleModule T Mₜ := hMₜ
  obtain ⟨B, hBc, ⟨eB⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso Mₜ
  have hB0 := MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant φ B
  have hpb := Divisor.isPullback_pullback hBc hB0
  have hlin := linearlyEquivalent_of_divisorialSheaf_iso
    (hpb.divisorialSheafIso (hBc := hBc) ≪≫ (Scheme.Modules.pullback φ).mapIso eB ≪≫ e)
  obtain ⟨u, hu⟩ := hlin
  obtain ⟨u', hu', rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hφ u
  have hDeq : D = B.pullback hBc hB0 - principalDivisor (pullbackRationalFunction φ u' hu') := by
    rw [← hu, sub_sub_cancel]
  rw [hDeq, map_sub, MMP.Positivity.transformDivisor_of_isPullback_divisor hTn hXn hφ hBc hpb,
    MMP.Positivity.transformDivisor_principalDivisor_pullback hTn hXn hφ u' hu']
  exact hBc.sub (Divisor.isCartier_principalDivisor u')

/-- A Cartier divisor with base point free complete linear system is free relative to any
morphism. -/
private theorem isRelativelyFreeDivisor_of_isBasepointFree {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] (φ : X ⟶ T) {D : Divisor X} (hDc : D.IsCartier) (hD : D.IsBasepointFree) :
    MMP.Fourfold.IsRelativelyFreeDivisor φ D := by
  refine MMP.Fourfold.isRelativelyFreeDivisor_of_forall_exists φ fun x => ?_
  have hx : x ∉ (D.baseLocus : Set X) := by
    rw [show D.baseLocus = ⊥ from hD]; exact fun h => h
  rw [Divisor.mem_baseLocus_iff] at hx
  push Not at hx
  obtain ⟨σ, hσ, hxσ⟩ := hx
  have hcoeff : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P + P.ord (Divisor.isUnit_sectionToRationalFunctions hσ).unit =
        (D.zeroDivisor σ hσ).coeff P := by
    intro P
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, add_comm]
  refine ⟨⊤, trivial, (Divisor.isUnit_sectionToRationalFunctions hσ).unit, fun P _ => ?_,
    fun P hxP => ?_⟩
  · rw [hcoeff P]
    exact Divisor.zeroDivisor_nonneg _ σ hσ P
  · rw [hcoeff P]
    by_contra hne
    exact hxσ (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, hne, hxP⟩)

end Descent

/-! ### Canonical divisors and klt pairs across small modifications -/

section Singularities

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type} [Field k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] : IsSeparated (T ↘ ⊤_ Scheme) := by
  rw [show (T ↘ ⊤_ Scheme) = sT ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The transform of a canonical divisor along a small proper birational morphism over `k` is a
canonical divisor. -/
private theorem isCanonicalDivisor_transformDivisor {k : Type} [Field k] [CharZero k]
    {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hX : Mori.IsProjectiveVariety k sX) (hT : Mori.IsProjectiveVariety k sT)
    {φ : X ⟶ T} (hφT : φ ≫ sT = sX) [IsProper φ] (hφ : IsBirationalMorphism φ)
    (hφs : IsIsoInCodimOne φ) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sT n (RationalMap.transformDivisor φ.toRationalMap K) := by
  haveI := hX.toIsVariety
  haveI := hT.toIsVariety
  haveI : IsDominant φ := hφ.isDominant
  have hTn : IsNormalVariety k sT := ⟨hT.toIsVariety, inferInstance⟩
  have hXn : IsNormalVariety k (φ ≫ sT) := hφT ▸ ⟨hX.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType (φ ≫ sT) := hφT ▸ inferInstance
  have hdim : topologicalKrullDim T = n := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sX hφ]
    exact hK.topologicalKrullDim_eq
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sT hTn hdim
  exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hTn hXn hφ hKT
    (hφT ▸ hK)

/-- The inverse transform of a canonical divisor along a small proper birational morphism over
`k` is a canonical divisor. -/
private theorem isCanonicalDivisor_inverseTransformDivisor {k : Type} [Field k] [CharZero k]
    {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hY : Mori.IsProjectiveVariety k sY) (hT : Mori.IsProjectiveVariety k sT)
    {ψ : Y ⟶ T} (hψT : ψ ≫ sT = sY) [IsProper ψ] (hψ : IsBirationalMorphism ψ)
    (hψs : IsIsoInCodimOne ψ) {n : ℕ} {KT : Divisor T} (hK : KT.IsCanonicalDivisor sT n) :
    Divisor.IsCanonicalDivisor sY n (inverseTransformDivisor ψ KT) := by
  haveI := hY.toIsVariety
  haveI := hT.toIsVariety
  haveI : IsDominant ψ := hψ.isDominant
  haveI : IsSeparated sT := hT.toIsVariety.toIsSeparated
  haveI := isSeparated_toTerminal sT
  have hTn : IsNormalVariety k sT := ⟨hT.toIsVariety, inferInstance⟩
  have hYn : IsNormalVariety k (ψ ≫ sT) := hψT ▸ ⟨hY.toIsVariety, inferInstance⟩
  haveI : LocallyOfFiniteType (ψ ≫ sT) := hψT ▸ inferInstance
  have hdim : topologicalKrullDim Y = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sY hψ]
    exact hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sY
    ⟨hY.toIsVariety, inferInstance⟩ hdim
  obtain ⟨KY, hKY, hKYe⟩ := MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq
    hTn hYn hψ hK (hψT ▸ hK₀)
  rw [← hKYe, inverseTransformDivisor_transformDivisor hψ hψs]
  exact hψT ▸ hKY

/-- The boundary condition transfers along `X ⟶ T ⟵ Y`: the coefficients of `ψ⁻¹_* φ_* Δ` are
coefficients of `Δ`. -/
private theorem isBoundary_inverseTransformDivisor_flopBaseDivisor {X Y T : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsSeparated (T ↘ ⊤_ Scheme)]
    {φ : X ⟶ T} {ψ : Y ⟶ T} [IsProper φ] [IsProper ψ] (hφ : IsBirationalMorphism φ)
    (hψ : IsBirationalMorphism ψ) (hφs : IsIsoInCodimOne φ) (hψs : IsIsoInCodimOne ψ)
    {Δ : QDivisor X} (hΔ : IsBoundary (QDivisor.toRDivisor Δ)) :
    IsBoundary (QDivisor.toRDivisor (inverseTransformDivisor ψ (flopBaseDivisor φ Δ))) := by
  intro Q
  rw [QDivisor.coeff_toRDivisor, coeff_inverseTransformDivisor hψ hψs]
  obtain ⟨P, hP⟩ := exists_map_genericPoint_eq hφs
    (PrimeDivisor.ofCoheightOne (ψ Q.genericPoint) (coheight_map_genericPoint_eq_one hψs Q))
  have hPE :
      PrimeDivisor.ofCoheightOne (φ P.genericPoint) (coheight_map_genericPoint_eq_one hφs P) =
      PrimeDivisor.ofCoheightOne (ψ Q.genericPoint) (coheight_map_genericPoint_eq_one hψs Q) :=
    PrimeDivisor.genericPoint_injective ((PrimeDivisor.genericPoint_ofCoheightOne _ _).trans hP)
  rw [← hPE, flopBaseDivisor, coeff_transformDivisor hφ hφs]
  simpa only [QDivisor.coeff_toRDivisor] using hΔ P

/-- **Discrepancies transfer along `X ⟶ T ⟵ Y`.** With `K_T = div(ω)`, `K_X = div(φ^*ω)`,
`K_Y = div(ψ^*ω)` and crepant boundaries, every discrepancy of `(Y, D_Y)` is a discrepancy of
`(X, D_X)`. -/
private theorem exists_isDiscrepancy_of_isDiscrepancy {k : Type} [Field k] [PerfectField k]
    {X Y T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hTn : IsNormalVariety k sT) {φ : X ⟶ T} {ψ : Y ⟶ T} [IsProper φ] [IsProper ψ]
    [LocallyOfFiniteType (φ ≫ sT)] [LocallyOfFiniteType (ψ ≫ sT)]
    (hXn : IsNormalVariety k (φ ≫ sT)) (hYn : IsNormalVariety k (ψ ≫ sT))
    (hφ : IsBirationalMorphism φ) (hψ : IsBirationalMorphism ψ) {n : ℕ}
    {ω : RationalPluriForms sT n 1} (hω0 : ω ≠ 0)
    (hKω : (divisorOfForm ω).IsCanonicalDivisor sT n) {DT : RDivisor T}
    (hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + DT))
    {DX : RDivisor X} {DY : RDivisor Y}
    (hDX : haveI : IsDominant φ := hφ.isDominant
      IsRCartierPullback φ (Divisor.toRDivisor (divisorOfForm ω) + DT)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sT φ ω)) + DX))
    (hKX : haveI : IsDominant φ := hφ.isDominant
      (divisorOfForm (pullbackRationalPluriForms sT φ ω)).IsCanonicalDivisor (φ ≫ sT) n)
    (hDY : haveI : IsDominant ψ := hψ.isDominant
      IsRCartierPullback ψ (Divisor.toRDivisor (divisorOfForm ω) + DT)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sT ψ ω)) + DY))
    (hKY : haveI : IsDominant ψ := hψ.isDominant
      (divisorOfForm (pullbackRationalPluriForms sT ψ ω)).IsCanonicalDivisor (ψ ≫ sT) n)
    (F : Valuation Y.functionField ℤᵐ⁰) (hF : HasNonemptyCenter k (ψ ≫ sT) F) (a : ℝ)
    (ha : haveI : IsDominant ψ := hψ.isDominant
      IsDiscrepancy (ψ ≫ sT) n (divisorOfForm (pullbackRationalPluriForms sT ψ ω)) DY F a) :
    ∃ G : Valuation X.functionField ℤᵐ⁰,
      haveI : IsDominant φ := hφ.isDominant
      IsDiscrepancy (φ ≫ sT) n (divisorOfForm (pullbackRationalPluriForms sT φ ω)) DX G a := by
  haveI : IsDominant φ := hφ.isDominant
  haveI : IsDominant ψ := hψ.isDominant
  obtain ⟨-, EY, rfl⟩ := hF
  have h1 := (isDiscrepancy_comap_functionFieldMap_iff hTn hω0 hKω hKD ψ hYn hψ hDY hKY EY a).2 ha
  obtain ⟨-, -, ⟨-, ET, hET⟩, -⟩ := id h1
  obtain ⟨EX, hEX⟩ := ProperDivisorOver.exists_comap_functionFieldMap_eq hXn hφ ET
  refine ⟨EX.valuation,
    (isDiscrepancy_comap_functionFieldMap_iff hTn hω0 hKω hKD φ hXn hφ hDX hKX EX a).1 ?_⟩
  rw [hEX, hET]
  exact h1

/-- **klt is preserved by a crepant small modification.** If `(X, Δ)` is klt, and
`r(K + Δ)`, `r(K_Y + Δ_Y)` are the pull-backs of one Cartier divisor `M = r(K_T + Δ_T)` on `T`
along small proper birational morphisms, where `K_T = φ_* K`, `Δ_T = φ_* Δ`, `K_Y = ψ⁻¹_* K_T`
and `Δ_Y = ψ⁻¹_* Δ_T`, then `(Y, Δ_Y)` is klt. -/
private theorem isKawamataLogTerminal_of_isPullback {k : Type} [Field k] [CharZero k]
    {X Y T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    [IsSeparated (T ↘ ⊤_ Scheme)] (hTn : IsNormalVariety k sT)
    {φ : X ⟶ T} {ψ : Y ⟶ T} [IsProper φ] [IsProper ψ]
    [LocallyOfFiniteType (φ ≫ sT)] [LocallyOfFiniteType (ψ ≫ sT)]
    (hXn : IsNormalVariety k (φ ≫ sT)) (hYn : IsNormalVariety k (ψ ≫ sT))
    (hφ : IsBirationalMorphism φ) (hψ : IsBirationalMorphism ψ)
    (hφs : IsIsoInCodimOne φ) (hψs : IsIsoInCodimOne ψ)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKawamataLogTerminal (φ ≫ sT) n K (QDivisor.toRDivisor Δ))
    (hKT : Divisor.IsCanonicalDivisor sT n (RationalMap.transformDivisor φ.toRationalMap K))
    (hKY : Divisor.IsCanonicalDivisor (ψ ≫ sT) n
      (inverseTransformDivisor ψ (RationalMap.transformDivisor φ.toRationalMap K)))
    {r : ℕ} (hr : 0 < r) {M : Divisor T} (hMc : M.IsCartier)
    (hM : Divisor.toQDivisor M = (r : ℤ) • (Divisor.toQDivisor
      (RationalMap.transformDivisor φ.toRationalMap K) + flopBaseDivisor φ Δ))
    {MX : Divisor X} {hBX : ∀ Z : irreducibleComponents X, φ (componentGenericPoint X Z) ∉ M.supp}
    (hMX : M.IsPullback φ hBX MX)
    (hMXe : Divisor.toQDivisor MX = (r : ℤ) • (Divisor.toQDivisor K + Δ))
    {MY : Divisor Y} {hBY : ∀ Z : irreducibleComponents Y, ψ (componentGenericPoint Y Z) ∉ M.supp}
    (hMY : M.IsPullback ψ hBY MY)
    (hMYe : Divisor.toQDivisor MY = (r : ℤ) • (Divisor.toQDivisor
      (inverseTransformDivisor ψ (RationalMap.transformDivisor φ.toRationalMap K)) +
      inverseTransformDivisor ψ (flopBaseDivisor φ Δ))) :
    IsKawamataLogTerminal (ψ ≫ sT) n
      (inverseTransformDivisor ψ (RationalMap.transformDivisor φ.toRationalMap K))
      (QDivisor.toRDivisor (inverseTransformDivisor ψ (flopBaseDivisor φ Δ))) := by
  haveI : IsDominant φ := hφ.isDominant
  haveI : IsDominant ψ := hψ.isDominant
  -- a rational top form on `T` with divisor `K_T`, and its pull-backs
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hTn hKT
  have hdivω : divisorOfForm ω = RationalMap.transformDivisor φ.toRationalMap K :=
    Finsupp.ext hωK
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sT)
    hKT.topologicalKrullDim_eq
  have hpbX : divisorOfForm (pullbackRationalPluriForms sT φ ω) = K := by
    rw [divisorOfForm_pullbackRationalPluriForms hφ hφs hd, hdivω,
      inverseTransformDivisor_transformDivisor hφ hφs]
  have hpbY : divisorOfForm (pullbackRationalPluriForms sT ψ ω) =
      inverseTransformDivisor ψ (RationalMap.transformDivisor φ.toRationalMap K) := by
    rw [divisorOfForm_pullbackRationalPluriForms hψ hψs hd, hdivω]
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sT n := by rwa [hdivω]
  have hTeq : Divisor.toRDivisor (divisorOfForm ω) +
      QDivisor.toRDivisor (flopBaseDivisor φ Δ) = ((r : ℝ)⁻¹) • Divisor.toRDivisor M := by
    rw [hdivω]; exact toRDivisor_add_eq_inv_smul hr hM
  have hKD : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) +
      QDivisor.toRDivisor (flopBaseDivisor φ Δ)) := by
    rw [hdivω]; exact isCartierCombination_of_toQDivisor_eq hr hMc hM
  have hDX : IsRCartierPullback φ (Divisor.toRDivisor (divisorOfForm ω) +
      QDivisor.toRDivisor (flopBaseDivisor φ Δ))
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sT φ ω)) +
        QDivisor.toRDivisor Δ) := by
    refine ⟨1, fun _ => (r : ℝ)⁻¹, fun _ => M, fun _ => MX, fun _ => hMc, ?_,
      fun _ => ⟨hBX, hMX⟩, ?_⟩
    · rwa [Fin.sum_univ_one]
    · rw [Fin.sum_univ_one, hpbX]; exact toRDivisor_add_eq_inv_smul hr hMXe
  have hDY : IsRCartierPullback ψ (Divisor.toRDivisor (divisorOfForm ω) +
      QDivisor.toRDivisor (flopBaseDivisor φ Δ))
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sT ψ ω)) +
        QDivisor.toRDivisor (inverseTransformDivisor ψ (flopBaseDivisor φ Δ))) := by
    refine ⟨1, fun _ => (r : ℝ)⁻¹, fun _ => M, fun _ => MY, fun _ => hMc, ?_,
      fun _ => ⟨hBY, hMY⟩, ?_⟩
    · rwa [Fin.sum_univ_one]
    · rw [Fin.sum_univ_one, hpbY]; exact toRDivisor_add_eq_inv_smul hr hMYe
  have hKX' : (divisorOfForm (pullbackRationalPluriForms sT φ ω)).IsCanonicalDivisor
      (φ ≫ sT) n := by
    rw [hpbX]
    exact hklt.2.1
  have hKY' : (divisorOfForm (pullbackRationalPluriForms sT ψ ω)).IsCanonicalDivisor
      (ψ ≫ sT) n := by
    rwa [hpbY]
  refine ⟨⟨hYn, isBoundary_inverseTransformDivisor_flopBaseDivisor hφ hψ hφs hψs
      hklt.1.isBoundary⟩, hKY,
    isCartierCombination_of_toQDivisor_eq hr (Divisor.IsPullback.isCartier hMY hMc) hMYe,
    fun F hF b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hb
  rw [← hpbY] at ha
  obtain ⟨G, hG⟩ := exists_isDiscrepancy_of_isDiscrepancy hTn hXn hYn hφ hψ hω0 hKω hKD hDX hKX' hDY
    hKY' F hF a ha
  rw [hpbX] at hG
  exact hklt.2.2.2 G hG.2.2.1 (1 + a) ⟨a, hG, rfl⟩

end Singularities

/-! ### Images of linear systems -/

section BasisChange

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)
open Stacks.AlgebraicGeometry.ProjectiveSpaceCoordinateSquare (basisSections
  generatesStalks_basisSections morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso)
open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

attribute [local instance] globalSectionsModule

variable (k : Type) [Field k] {X : Scheme.{0}} [X.Over (Spec (.of k))] (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]

private theorem topologicalKrullDim_linearSystemImage_eq_closure {ι : Type}
    (b : Module.Basis ι k Γ(L, ⊤)) :
    topologicalKrullDim (linearSystemImage k L b) =
      topologicalKrullDim (closure (Set.range (linearSystemMap k L b).base)) := by
  have hemb := (linearSystemImageIdeal k L b).subschemeι.isClosedEmbedding.isEmbedding
  rw [hemb.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  have : Set.range (linearSystemImageIdeal k L b).subschemeι.base =
      closure (Set.range (linearSystemMap k L b).base) := by
    rw [Scheme.IdealSheafData.range_subschemeι, linearSystemImageIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [this]

private theorem linearSystemMap_comp_basisProjectiveSpaceOfModuleIso {ι : Type}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (c : Module.Basis (Fin (n + 1)) k (ι →₀ k))
    (hgen : GeneratesStalks (fun i => b.repr.symm (c i))) :
    linearSystemMap k L b ≫ (basisProjectiveSpaceOfModuleIso c).hom.left =
      (linearSystemLocus k L b).ι ≫
        toProjectiveSpaceOver (fun i => b.repr.symm (c i)) hgen (X ↘ Spec (.of k)) := by
  rw [linearSystemMap, morphismOfGeneratingSections_comp_basisProjectiveSpaceOfModuleIso]
  refine CategoryTheory.Limits.pullback.hom_ext ?_ ?_
  · rw [toProjectiveSpaceOver_fst, Category.assoc, toProjectiveSpaceOver_fst]
    rfl
  · rw [toProjectiveSpaceOver_snd, Category.assoc, toProjectiveSpaceOver_snd,
      comp_toProjectiveSpaceAtUniverse _ _ _
        (pullbackTuple (linearSystemLocus k L b).ι ⟨L, ‹_›, _, hgen⟩).generates]
    congr 1

private theorem topologicalKrullDim_closure_range_homeomorph_comp {A B C : Type*}
    [TopologicalSpace B] [TopologicalSpace C] (f : A → B) (E : B ≃ₜ C) :
    topologicalKrullDim (closure (Set.range (E ∘ f))) =
      topologicalKrullDim (closure (Set.range f)) := by
  rw [Set.range_comp, ← E.image_closure]
  exact (E.image _).isHomeomorph.topologicalKrullDim_eq.symm

private theorem range_comp_of_range_eq_univ {A B C : Scheme.{0}} (i : A ⟶ B) (h : B ⟶ C)
    (hi : Set.range i.base = Set.univ) : Set.range (i ≫ h).base = Set.range h.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hi, Set.image_univ]

private theorem topologicalKrullDim_linearSystemImage_eq_toProjectiveSpaceOver {ι : Type}
    (b : Module.Basis ι k Γ(L, ⊤)) {n : ℕ} (c : Module.Basis (Fin (n + 1)) k (ι →₀ k))
    (hgen : GeneratesStalks (fun i => b.repr.symm (c i)))
    (htop : linearSystemLocus k L b = ⊤) :
    topologicalKrullDim (linearSystemImage k L b) =
      topologicalKrullDim (closure (Set.range
        (toProjectiveSpaceOver (fun i => b.repr.symm (c i)) hgen (X ↘ Spec (.of k))).base)) := by
  rw [topologicalKrullDim_linearSystemImage_eq_closure]
  let g := (basisProjectiveSpaceOfModuleIso c).hom.left
  haveI : IsIso g :=
    inferInstanceAs (IsIso ((Over.forget _).map (basisProjectiveSpaceOfModuleIso c).hom))
  have key : topologicalKrullDim (closure (Set.range (linearSystemMap k L b ≫ g).base)) =
      topologicalKrullDim (closure (Set.range (linearSystemMap k L b).base)) :=
    topologicalKrullDim_closure_range_homeomorph_comp _ (Scheme.homeoOfIso (asIso g))
  have hU : Set.range (linearSystemLocus k L b).ι.base = Set.univ := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι, htop]
    rfl
  rw [← key, linearSystemMap_comp_basisProjectiveSpaceOfModuleIso k L b c hgen]
  erw [range_comp_of_range_eq_univ _ _ hU]
  rfl

/-- **The dimension of the image of a free linear system does not depend on the basis.** -/
private theorem topologicalKrullDim_linearSystemImage_eq_of_linearSystemLocus_eq_top
    [Nonempty X] [FiniteDimensional k Γ(L, ⊤)] {ι ι' : Type}
    (b : Module.Basis ι k Γ(L, ⊤)) (b' : Module.Basis ι' k Γ(L, ⊤))
    (htop : linearSystemLocus k L b = ⊤) (htop' : linearSystemLocus k L b' = ⊤) :
    topologicalKrullDim (linearSystemImage k L b) =
      topologicalKrullDim (linearSystemImage k L b') := by
  haveI : Finite ι := Module.Finite.finite_basis b
  have hι : 0 < Nat.card ι := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have hx : x ∈ linearSystemLocus k L b := htop ▸ trivial
    obtain ⟨i, -⟩ := (mem_linearSystemLocus_iff k L b x).1 hx
    haveI : Nonempty ι := ⟨i⟩
    exact Nat.card_pos
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt hι
  let e : Fin (n + 1) ≃ ι := (finCongr (by omega)).trans (Finite.equivFin ι).symm
  let c : Module.Basis (Fin (n + 1)) k (ι →₀ k) :=
    (Finsupp.basisSingleOne (R := k) (ι := ι)).reindex e.symm
  let c' := c.map (b.repr.symm.trans b'.repr)
  have hcc : ∀ i, b'.repr.symm (c' i) = b.repr.symm (c i) := fun i => by
    simp [c']
  have hψ : ⨆ v : Γ(L, ⊤), Stacks.NonvanishingOpen.nonvanishingOpen X L
      ((LinearMap.id : Γ(L, ⊤) →ₗ[k] Γ(L, ⊤)) v) = ⊤ :=
    eq_top_iff.2 (htop.ge.trans (iSup_le fun i => le_iSup_of_le (b i) le_rfl))
  have hgen : GeneratesStalks (fun i => b.repr.symm (c i)) :=
    generatesStalks_basisSections (c.map b.repr.symm) LinearMap.id hψ
  have hgen' : GeneratesStalks (fun i => b'.repr.symm (c' i)) := by
    simpa only [hcc] using hgen
  rw [topologicalKrullDim_linearSystemImage_eq_toProjectiveSpaceOver k L b c hgen htop,
    topologicalKrullDim_linearSystemImage_eq_toProjectiveSpaceOver k L b' c' hgen' htop']
  have key : ∀ (s s' : Fin (n + 1) → Γ(L, ⊤)) (hs : GeneratesStalks s)
      (hs' : GeneratesStalks s'), s = s' →
      topologicalKrullDim (closure (Set.range
        (toProjectiveSpaceOver s hs (X ↘ Spec (.of k))).base)) =
      topologicalKrullDim (closure (Set.range
        (toProjectiveSpaceOver s' hs' (X ↘ Spec (.of k))).base)) := by
    rintro s _ hs hs' rfl
    rfl
  exact key _ _ hgen hgen' (funext fun i => (hcc i).symm)

end BasisChange

section LinearSystem

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule) in
/-- The global sections of a Cartier divisor on a proper scheme over `k` form a
finite-dimensional `k`-vector space. -/
private theorem finiteDimensional_globalSections_divisorialSheaf (k : Type) [Field k]
    {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    (sT : T ⟶ Spec (.of k)) [IsProper sT] {B : Divisor T} (hBc : B.IsCartier) :
    letI : T.Over (Spec (.of k)) := ⟨sT⟩
    haveI := hBc.isInvertibleModule_divisorialSheaf
    letI := globalSectionsModule k T B.divisorialSheaf
    FiniteDimensional k Γ(B.divisorialSheaf, ⊤) := by
  letI : T.Over (Spec (.of k)) := ⟨sT⟩
  haveI := hBc.isInvertibleModule_divisorialSheaf
  have : AlgebraicGeometry.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      B.divisorialSheaf := ‹Stacks.Ample.IsInvertibleModule T B.divisorialSheaf›
  have : B.divisorialSheaf.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible T B.divisorialSheaf
  have := finiteDimensional_cohomologyOverField_of_isProper k sT B.divisorialSheaf 0
  have e := (cohomologyOverFieldZeroLinearIso k sT B.divisorialSheaf).toLinearEquiv
  have hEq : sT.appLE ⊤ ⊤ (by simp) = sT.appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  have key : ∀ φ : k →+* Γ(T, ⊤),
      φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appLE ⊤ ⊤ (by simp)).hom →
        (letI := Module.compHom Γ(B.divisorialSheaf, ⊤) φ;
          FiniteDimensional k Γ(B.divisorialSheaf, ⊤)) := by
    rintro φ rfl
    have h := Module.Finite.equiv e
    exact h
  refine key _ ?_
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ sT.appTop).hom = _
  rw [hEq]

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule) in
/-- Let `p : X ⟶ T` be a morphism of normal projective varieties with `p_* 𝒪_X = 𝒪_T`, `B` a
Cartier divisor on `T` and `B' = p^* B` base point free. For any bases of `H⁰(X, B')` and
`H⁰(T, B)`, the images of the morphisms the two linear systems define have the same dimension. -/
private theorem topologicalKrullDim_linearSystemImage_eq_of_isPullback_of_isBasepointFree
    {k : Type} [Field k] {X T : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    (hX : Mori.IsProjectiveVariety k sX) (hT : Mori.IsProjectiveVariety k sT)
    (p : X ⟶ T) (hps : p ≫ sT = sX) (hp : ∀ U : T.Opens, IsIso (p.app U))
    {B : Divisor T} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ B.supp}
    {B' : Divisor X} (hpb : B.IsPullback p hB B') (hB'c : B'.IsCartier)
    (hfree : B'.IsBasepointFree) :
    letI : X.Over (Spec (.of k)) := ⟨sX⟩
    letI : T.Over (Spec (.of k)) := ⟨sT⟩
    haveI := hB'c.isInvertibleModule_divisorialSheaf
    haveI := hBc.isInvertibleModule_divisorialSheaf
    letI := globalSectionsModule k X B'.divisorialSheaf
    letI := globalSectionsModule k T B.divisorialSheaf
    ∀ (ι : Type) (b' : Module.Basis ι k Γ(B'.divisorialSheaf, ⊤))
      (ι' : Type) (b : Module.Basis ι' k Γ(B.divisorialSheaf, ⊤)),
      topologicalKrullDim (linearSystemImage k B'.divisorialSheaf b') =
        topologicalKrullDim (linearSystemImage k B.divisorialSheaf b) := by
  letI : X.Over (Spec (.of k)) := ⟨sX⟩
  letI : T.Over (Spec (.of k)) := ⟨sT⟩
  haveI := hB'c.isInvertibleModule_divisorialSheaf
  haveI := hBc.isInvertibleModule_divisorialSheaf
  letI := globalSectionsModule k X B'.divisorialSheaf
  letI := globalSectionsModule k T B.divisorialSheaf
  intro ι b' ι' b
  haveI : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism sX hX.isProjective
  haveI : IsProper (T ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism sT hT.isProjective
  haveI : Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback p).obj B.divisorialSheaf) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback p _
  haveI : IsProper (p ≫ sT) := hps ▸ inferInstance
  haveI : IsProper p := IsProper.of_comp p sT
  haveI : Nonempty T := ⟨p (Nonempty.some inferInstance)⟩
  have hsurj : Function.Surjective p.base := (p.surjective_of_isIso_app hp).surj
  have hps' : p ≫ (T ↘ Spec (.of k)) = X ↘ Spec (.of k) := hps
  let Q := MMP.Flips.pullbackDivisorialSectionsEquiv k p hps' hp hBc hpb
  have hQ :=
    MMP.Flips.divisorialSheafIso_hom_app_pullbackDivisorialSectionsEquiv k p hps' hp hBc hpb
  let b₀ := b'.map Q.symm
  have hb₀ : b₀.map Q = b' := by ext i; simp [b₀]
  have htopX : linearSystemLocus k B'.divisorialSheaf b' = ⊤ :=
    Divisor.IsBasepointFree.linearSystemLocus_eq_top k hB'c hfree b'
  have htop₀ : linearSystemLocus k B.divisorialSheaf b₀ = ⊤ := by
    have h := MMP.Flips.linearSystemLocus_map_of_pullback k p _ _
      (hpb.divisorialSheafIso (hBc := hBc)) Q hQ b₀
    rw [hb₀, htopX] at h
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨x, rfl⟩ := hsurj y
    exact (h ▸ trivial : x ∈ p ⁻¹ᵁ linearSystemLocus k B.divisorialSheaf b₀)
  have htopT : linearSystemLocus k B.divisorialSheaf b = ⊤ := by
    refine linearSystemLocus_eq_top_of_forall k _ b fun y => ?_
    obtain ⟨i, hi⟩ := (mem_linearSystemLocus_iff k _ b₀ y).1 (htop₀ ▸ trivial)
    exact ⟨b₀ i, hi⟩
  haveI : IsProper sT := isProper_of_isProjectiveMorphism sT hT.isProjective
  haveI := finiteDimensional_globalSections_divisorialSheaf k sT hBc
  rw [← hb₀, MMP.Flips.topologicalKrullDim_linearSystemImage_eq_of_isPullback k p hps' hp hBc hpb
      b₀ htop₀]
  exact topologicalKrullDim_linearSystemImage_eq_of_linearSystemLocus_eq_top k _ b₀ b htop₀ htopT

end LinearSystem

end MMP.FourfoldProofs.FourfoldFa15ProjectiveTrivialFlopBundleProof

end

section

/-!
# Log canonical divisors across a projective numerically trivial small modification

Let `φ : X ⟶ T` and `ψ : Y ⟶ T` be proper birational morphisms of normal projective varieties over
an algebraically closed field `k` of characteristic zero, both isomorphisms in codimension one. Let
`(X, Δ)` be a klt pair with `Δ` a `ℚ`-divisor and `K_X + Δ` numerically `φ`-trivial. Put
`Δ_T = φ_* Δ`, `K_T = φ_* K_X`, and let `Δ_Y`, `K_Y` be their strict transforms on `Y`. Then some
positive multiple `r (K_T + Δ_T)` is an integral Cartier divisor whose pullbacks along `φ` and `ψ`
are `r (K_X + Δ)` and `r (K_Y + Δ_Y)`, `K_T` is a canonical divisor of `T`, and `(Y, Δ_Y)` is klt.
Moreover `K_X + Δ` and `K_Y + Δ_Y` are eventually free simultaneously, their free linear systems in
a common multiple have images of the same dimension, and they are eventually free and composed
of a pencil simultaneously.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne`

## Implementation notes

The complex numbers of the source are replaced by an arbitrary algebraically closed field of
characteristic zero. The canonical divisors on `T` and `Y` are the birational transforms of the
chosen `K_X` (`MMP.Mori.RationalMap.transformDivisor` along `φ`, then
`MMP.Mori.inverseTransformDivisor` along `ψ`); this is the compatible choice of canonical forms of
the source. Equalities with pullbacks are equalities of Weil divisors, with the Cartier pullback
`MMP.Mori.Divisor.IsPullback`. The dimension of the image of the morphism defined by a base point
free linear system is that of `MMP.Mori.linearSystemImage`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4.4, 15.9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

open MMP.FourfoldProofs.FourfoldFa15ProjectiveTrivialFlopBundleProof in
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule) in
/-- **Adjoints across a projective numerically trivial small modification** (FA 15.4.4, 15.9). Let
`φ : X ⟶ T` and `ψ : Y ⟶ T` be proper birational morphisms over `k` (algebraically closed,
characteristic zero) of normal projective varieties, isomorphisms in codimension one
(`MMP.Flips.IsIsoInCodimOne`). Let `(X, Δ)` be klt (`MMP.Flips.IsKawamataLogTerminal`) with
canonical divisor `K` of dimension `n`, and `K + Δ` numerically `φ`-trivial. Put `K_T = φ_* K`,
`Δ_T = φ_* Δ`, `K_Y = ψ⁻¹_* K_T`, `Δ_Y = ψ⁻¹_* Δ_T`. Then:
* `K_T` is a canonical divisor of `T`, and there are `r > 0` and a Cartier divisor `M` on `T`
  with `M = r (K_T + Δ_T)`, `φ^* M = r (K + Δ)` and `ψ^* M = r (K_Y + Δ_Y)`;
* `(Y, Δ_Y)` is klt;
* `K + Δ` is eventually free iff `K_Y + Δ_Y` is (`MMP.Flips.IsEventuallyFree`);
* if `m (K + Δ)` and `m (K_Y + Δ_Y)` are base point free Cartier divisors `M_X`, `M_Y`, the
  images of the morphisms they define have the same dimension;
* `K + Δ` is eventually free and composed of a pencil iff `K_Y + Δ_Y` is
  (`MMP.Flips.IsEventuallyFreePencil`). -/
@[mmp "lem_fourfold_fa15_projective_trivial_flop_bundle"]
public theorem IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y T : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    (hX : Mori.IsProjectiveVariety k sX) (hY : Mori.IsProjectiveVariety k sY)
    (hT : Mori.IsProjectiveVariety k sT)
    {φ : X ⟶ T} {ψ : Y ⟶ T} (hφT : φ ≫ sT = sX) (hψT : ψ ≫ sT = sY)
    [IsProper φ] [IsProper ψ] (hφ : IsBirationalMorphism φ) (hψ : IsBirationalMorphism ψ)
    (hφs : IsIsoInCodimOne φ) (hψs : IsIsoInCodimOne ψ)
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor Δ))
    (htriv : IsNumericallyTrivialOver k sX φ (QDivisor.toRDivisor (Divisor.toQDivisor K + Δ))) :
    let KT : Divisor T := RationalMap.transformDivisor φ.toRationalMap K
    let ΔT : QDivisor T := flopBaseDivisor φ Δ
    let KY : Divisor Y := inverseTransformDivisor ψ KT
    let ΔY : QDivisor Y := inverseTransformDivisor ψ ΔT
    KT.IsCanonicalDivisor sT n ∧
    (∃ r : ℕ, 0 < r ∧ ∃ M : Divisor T,
      Divisor.toQDivisor M = (r : ℤ) • (Divisor.toQDivisor KT + ΔT) ∧ M.IsCartier ∧
      (∃ (MX : Divisor X) (hB : ∀ Z : irreducibleComponents X,
          φ (componentGenericPoint X Z) ∉ M.supp),
        Divisor.toQDivisor MX = (r : ℤ) • (Divisor.toQDivisor K + Δ) ∧ M.IsPullback φ hB MX) ∧
      (∃ (MY : Divisor Y) (hB : ∀ Z : irreducibleComponents Y,
          ψ (componentGenericPoint Y Z) ∉ M.supp),
        Divisor.toQDivisor MY = (r : ℤ) • (Divisor.toQDivisor KY + ΔY) ∧
          M.IsPullback ψ hB MY)) ∧
    IsKawamataLogTerminal sY n KY (QDivisor.toRDivisor ΔY) ∧
    (IsEventuallyFree k sX (Divisor.toQDivisor K + Δ) ↔
      IsEventuallyFree k sY (Divisor.toQDivisor KY + ΔY)) ∧
    (∀ (m : ℕ) (MX : Divisor X) (MY : Divisor Y), 0 < m →
      Divisor.toQDivisor MX = (m : ℤ) • (Divisor.toQDivisor K + Δ) →
      Divisor.toQDivisor MY = (m : ℤ) • (Divisor.toQDivisor KY + ΔY) →
      ∀ (hMX : MX.IsCartier) (hMY : MY.IsCartier), MX.IsBasepointFree → MY.IsBasepointFree →
        letI : X.Over (Spec (.of k)) := ⟨sX⟩
        letI : Y.Over (Spec (.of k)) := ⟨sY⟩
        haveI := hMX.isInvertibleModule_divisorialSheaf
        haveI := hMY.isInvertibleModule_divisorialSheaf
        letI := globalSectionsModule k X MX.divisorialSheaf
        letI := globalSectionsModule k Y MY.divisorialSheaf
        ∀ (ιX : Type) (bX : Module.Basis ιX k Γ(MX.divisorialSheaf, ⊤))
          (ιY : Type) (bY : Module.Basis ιY k Γ(MY.divisorialSheaf, ⊤)),
          topologicalKrullDim (linearSystemImage k MX.divisorialSheaf bX) =
            topologicalKrullDim (linearSystemImage k MY.divisorialSheaf bY)) ∧
    (IsEventuallyFreePencil k sX (Divisor.toQDivisor K + Δ) ↔
      IsEventuallyFreePencil k sY (Divisor.toQDivisor KY + ΔY)) := by
  intro KT ΔT KY ΔY
  have hXnv : IsNormalVariety k sX := ⟨hX.toIsVariety, inferInstance⟩
  have hYnv : IsNormalVariety k sY := ⟨hY.toIsVariety, inferInstance⟩
  have hTnv : IsNormalVariety k sT := ⟨hT.toIsVariety, inferInstance⟩
  haveI : IsSeparated sT := hT.toIsVariety.toIsSeparated
  haveI := isSeparated_toTerminal sT
  have hφO : ∀ U : T.Opens, IsIso (φ.app U) :=
    MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism sX sT hX.toIsVariety hTnv φ hφ
  have hψO : ∀ U : T.Opens, IsIso (ψ.app U) :=
    MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism sY sT hY.toIsVariety hTnv ψ hψ
  -- the adjoints on `X`, `T`, `Y` and their transforms
  have htr : ∀ D : Divisor X, Divisor.toQDivisor (RationalMap.transformDivisor φ.toRationalMap D) =
      RationalMap.transformDivisor φ.toRationalMap (Divisor.toQDivisor D) :=
    toQDivisor_mapPrimeDivisors _
  have hinvψ : ∀ D : Divisor T, Divisor.toQDivisor (inverseTransformDivisor ψ D) =
      inverseTransformDivisor ψ (Divisor.toQDivisor D) :=
    toQDivisor_mapPrimeDivisors _
  have htrL : ∀ m : ℤ, RationalMap.transformDivisor φ.toRationalMap
      (m • (Divisor.toQDivisor K + Δ)) = m • (Divisor.toQDivisor KT + ΔT) := by
    intro m
    rw [map_zsmul, map_add, ← htr]
    rfl
  have hinvL : ∀ m : ℤ, inverseTransformDivisor ψ (m • (Divisor.toQDivisor KT + ΔT)) =
      m • (Divisor.toQDivisor KY + ΔY) := by
    intro m
    rw [map_zsmul, map_add, ← hinvψ]
  -- the Cartier adjoint on `T`
  obtain ⟨r, hr, D₀, hD₀, hD₀c, hD₀f⟩ :=
    exists_isRelativelyFreeDivisor_of_isAlgClosed hX hT hφT hφ hklt htriv
  have hMc : Divisor.IsCartier (RationalMap.transformDivisor φ.toRationalMap D₀) :=
    isCartier_transformDivisor_of_isRelativelyFreeDivisor hX hT hφT hφ hφs htriv hr hD₀ hD₀c hD₀f
  set M := RationalMap.transformDivisor φ.toRationalMap D₀ with hMdef
  have hM : Divisor.toQDivisor M = (r : ℤ) • (Divisor.toQDivisor KT + ΔT) := by
    rw [hMdef, htr, hD₀, htrL]
  obtain ⟨hBX, hMX⟩ := exists_isPullback_of_inverseTransformDivisor_eq hφ hφs hMc
    (inverseTransformDivisor_transformDivisor hφ hφs D₀)
  obtain ⟨hBY, hMY⟩ := exists_isPullback_of_inverseTransformDivisor_eq hψ hψs hMc rfl
  have hMYe : Divisor.toQDivisor (inverseTransformDivisor ψ M) =
      (r : ℤ) • (Divisor.toQDivisor KY + ΔY) := by
    rw [hinvψ, hM, hinvL]
  have hKT : Divisor.IsCanonicalDivisor sT n KT :=
    isCanonicalDivisor_transformDivisor hX hT hφT hφ hφs hklt.2.1
  have hKY : Divisor.IsCanonicalDivisor sY n KY :=
    isCanonicalDivisor_inverseTransformDivisor hY hT hψT hψ hψs hKT
  -- the `ℚ`-Cartier adjoint on `T` and its pull-backs
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hN : (Divisor.toQDivisor KT + ΔT).IsQCartier := ⟨r, hr', M, hM, hMc⟩
  have hsuppM : M.supp = (Divisor.toQDivisor KT + ΔT).supp :=
    QDivisor.supp_eq_of_toQDivisor_eq hr' hM
  have hBNX : ∀ Z : irreducibleComponents X,
      φ (componentGenericPoint X Z) ∉ (Divisor.toQDivisor KT + ΔT).supp := fun Z => by
    rw [← hsuppM]
    exact hBX Z
  have hBNY : ∀ Z : irreducibleComponents Y,
      ψ (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor KT + ΔT).supp := fun Z => by
    rw [← hsuppM]
    exact hBY Z
  have hpbX : (Divisor.toQDivisor KT + ΔT).pullback hN hBNX = Divisor.toQDivisor K + Δ :=
    QDivisor.pullback_eq_of_isPullback hN hr hMc hM hMX hD₀ hBNX
  have hpbY : (Divisor.toQDivisor KT + ΔT).pullback hN hBNY = Divisor.toQDivisor KY + ΔY :=
    QDivisor.pullback_eq_of_isPullback hN hr hMc hM hMY hMYe hBNY
  have hLX : (Divisor.toQDivisor K + Δ).IsQCartier := ⟨r, hr', D₀, hD₀, hD₀c⟩
  have hLY : (Divisor.toQDivisor KY + ΔY).IsQCartier := ⟨r, hr', _, hMYe, hMY.isCartier hMc⟩
  refine ⟨hKT, ⟨r, hr, M, hM, hMc, ⟨D₀, hBX, hD₀, hMX⟩, ⟨_, hBY, hMYe, hMY⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · subst hφT hψT
    exact isKawamataLogTerminal_of_isPullback hTnv hXnv hYnv hφ hψ hφs hψs hklt hKT hKY hr hMc hM
      hMX hD₀ hMY hMYe
  · exact (isEventuallyFree_iff_of_qLinearlyEquivalent_pullback k sX sT hXnv hTnv φ hφT hφO hN
      ⟨hBNX, by rw [hpbX]⟩).trans
      (isEventuallyFree_iff_of_qLinearlyEquivalent_pullback k sY sT hYnv hTnv ψ hψT hψO hN
      ⟨hBNY, by rw [hpbY]⟩).symm
  · intro m MX MY hm hMX' hMY' hMXc hMYc hMXf hMYf
    have hBc : Divisor.IsCartier (RationalMap.transformDivisor φ.toRationalMap MX) :=
      isCartier_transformDivisor_of_isRelativelyFreeDivisor hX hT hφT hφ hφs htriv hm hMX' hMXc
        (isRelativelyFreeDivisor_of_isBasepointFree φ hMXc hMXf)
    obtain ⟨_, hpb₁⟩ := exists_isPullback_of_inverseTransformDivisor_eq hφ hφs hBc
      (inverseTransformDivisor_transformDivisor hφ hφs MX)
    obtain ⟨_, hpb₂⟩ := exists_isPullback_of_inverseTransformDivisor_eq hψ hψs hBc
      (Divisor.toQDivisor_injective (by rw [hMY', hinvψ, htr, hMX', htrL, hinvL]))
    have h₁ := topologicalKrullDim_linearSystemImage_eq_of_isPullback_of_isBasepointFree
      hX hT φ hφT hφO hBc hpb₁ hMXc hMXf
    have h₂ := topologicalKrullDim_linearSystemImage_eq_of_isPullback_of_isBasepointFree
      hY hT ψ hψT hψO hBc hpb₂ hMYc hMYf
    intro ιX bX ιY bY
    letI : T.Over (Spec (.of k)) := ⟨sT⟩
    haveI := hBc.isInvertibleModule_divisorialSheaf
    letI := Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule k T
      (Divisor.divisorialSheaf (RationalMap.transformDivisor φ.toRationalMap MX))
    rw [h₁ ιX bX _ (Module.Basis.ofVectorSpace k _), h₂ ιY bY _ (Module.Basis.ofVectorSpace k _)]
  · exact (isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback k sX sT hX hT φ hφT hφO hLX
      hN ⟨hBNX, by rw [hpbX]⟩).trans
      (isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback k sY sT hY hT ψ hψT hψO hLY hN
      ⟨hBNY, by rw [hpbY]⟩).symm

end MMP.Flips

end
