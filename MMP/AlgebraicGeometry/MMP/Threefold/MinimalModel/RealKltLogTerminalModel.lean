module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.MMP.Flip.NumericalClassTransport
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.RealKltProgram
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialDiscrepancyIncrease
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.Intersection.RelativePicardNumberFinite
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Log terminal models of pseudo-effective projective real klt threefolds

Let `g : X ⟶ S` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold with canonical divisor `K`, and let `(X, B)` be a klt pair with effective real boundary
`B`. If `K + B` is pseudo-effective over `S`, then `(X, B)` has a log terminal model over `S`:
a birational contraction `φ : X ⤏ Y` over `S` to a projective `ℚ`-factorial variety `Y` such
that `(Y, φ_* B)` is klt, `K_Y + φ_* B` is nef over `S`, and on a common resolution
`p : W ⟶ X`, `q : W ⟶ Y` the difference `p^*(K + B) - q^*(K_Y + φ_* B)` is effective and
`q`-exceptional, with positive coefficient along the strict transform of every prime divisor of
`X` contracted by `φ`.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective`.

## Implementation notes

The birational contraction, its nefness over `S` and the effective `q`-exceptional comparison are
`MMP.Fourfold.IsNefWeakModel`, with `K_Y = φ_* K`. Pseudo-effectivity over `S` is
`MMP.Fourfold.KCartierDivisor.IsRelativelyPseudoEffective` of a real Cartier divisor
`∑ rᵢ Aᵢ` whose Weil divisor `∑ rᵢ [Aᵢ]` is `K + B`. The strict transform of a prime divisor
`P` of `X` on `W` is the prime divisor `P'` of `W` with `p_* P' = P`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_thm_fourfold_projective_real_threefold_log_model

open MMP.Fourfold MMP.Mori MMP.Flips

/-! ### Generalities -/

section Generalities

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_of_isQFactorial {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsQFactorial sX) (D : RDivisor X) : IsCartierCombination D := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨D.support.card, fun i => D (e.symm i) / m (e.symm i),
    fun i => ((m (e.symm i) : ℕ) : ℤ) • Finsupp.single (e.symm i : MMP.Mori.PrimeDivisor X) 1,
    fun i => hmC _, ?_⟩
  simp only [← toRDivisor_eq_mapCoeffs]
  have hterm : ∀ P : MMP.Mori.PrimeDivisor X, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor X)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor X) 1 :
        Divisor X)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor X)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

/-- A morphism injective on points contracts no proper curve: the closure of the generic point of
a contracted curve would be a single point. -/
private theorem not_isContractedBy_of_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) {f : X ⟶ Y} (hf : Function.Injective f) :
    ¬ C.IsContractedBy f := by
  intro hC
  have hcl : closure ({C.point} : Set X) = {C.point} :=
    Set.Subset.antisymm (fun x hx => hf (hC x hx)) subset_closure
  have hsub : Subsingleton C.scheme := by
    refine ⟨fun a b => C.ι.isClosedEmbedding.injective ?_⟩
    have hra : ∀ c : C.scheme, C.ι c = C.point := fun c => by
      have hc : C.ι c ∈ Set.range C.ι := ⟨c, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hcl] at hc
      exact hc
    rw [hra a, hra b]
  have hdisc : DiscreteTopology C.scheme := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- Over a morphism injective on points every `ℝ`-Cartier divisor is relatively nef. -/
private theorem isRelativelyNef_of_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}
    (hf : Function.Injective f) {D : RDivisor X} (hD : IsCartierCombination D) :
    IsRelativelyNef k sX f D := by
  obtain ⟨m, r, L, hL, hDL⟩ := hD
  exact ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hDL,
    fun C hC => absurd hC (not_isContractedBy_of_injective C hf)⟩

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) : ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have hdisc : DiscreteTopology C.scheme := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp_of_isCurveNormalization {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 := isCurve_ι C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    {C : ProperCurve sX} {L : Divisor X} {hL : L.IsCartier} {d : ℤ}
    (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with a proper curve, computed on the
normalization of the curve. -/
private theorem exists_isCartierIntersectionNumber (k : Type) [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (C : ProperCurve sY) (L : Divisor Y) (hL : L.IsCartier) :
    ∃ d, IsCartierIntersectionNumber k sY C L hL d := by
  let p := C.ι ≫ sY
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- Relative nefness is invariant under adding a divisor linearly equivalent to `0`: such a
divisor has degree `0` along every proper curve. -/
private theorem isRelativelyNef_add_of_linearlyEquivalent {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {D : RDivisor X} (hD : IsRelativelyNef k sX f D) {E : Divisor X}
    (hE : E.LinearlyEquivalent 0) : IsRelativelyNef k sX f (D + Divisor.toRDivisor E) := by
  have hEc : E.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hE Divisor.isCartier_zero
  obtain ⟨m, r, L, hL, hDL, hnef⟩ := hD
  refine ⟨m + 1, Fin.snoc r 1, Fin.snoc L E, fun j => ?_, ?_, fun C hC x hx => ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hEc
    · simpa using hL j
  · rw [Fin.sum_univ_castSucc, hDL]
    simp
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    choose e he using fun j => exists_isCartierIntersectionNumber k sX C (L j) (hL j)
    have h1 := hnef C hC (∑ j, r j * e j) ⟨hL, e, hDL, he, rfl⟩
    have hcast : ∀ j : Fin m, d j.castSucc = e j := fun j => by
      rw [eq_degreeOn_of_isCartierIntersectionNumber (hd j.castSucc),
        eq_degreeOn_of_isCartierIntersectionNumber (he j)]
      exact Divisor.degreeOn_congr (by simp) _ _
    have hlast : d (Fin.last m) = 0 := by
      rw [eq_degreeOn_of_isCartierIntersectionNumber (hd (Fin.last m)),
        Divisor.degreeOn_congr (by simp) _ hEc]
      exact Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hEc hE
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hcast, Int.cast_zero, mul_zero, add_zero]
    exact h1

/-- An `f`-ample `ℝ`-divisor is `f`-nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {A : RDivisor X} (hA : IsRelativelyAmple f A) :
    IsRelativelyNef k sX f A := by
  obtain ⟨m, r, L, -, hr, hLa, hAL⟩ := hA
  refine ⟨m, r, L, fun j => (hLa j).1, hAL, fun C hC x hx => ?_⟩
  obtain ⟨hL, d, -, hd, rfl⟩ := hx
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le ?_
  rw [eq_degreeOn_of_isCartierIntersectionNumber (hd j)]
  obtain ⟨hLc, hamp⟩ := hLa j
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hM : MMP.Mori.IsRelativelyAmple f (L j).divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact_mod_cast (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy
    f _ hM C hC).le

/-- An isomorphism preserves coheights. -/
private theorem coheight_map_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) :
    Order.coheight (f x) = Order.coheight x :=
  Topology.IsOpenEmbedding.coheight_eq _ f.isOpenEmbedding

/-- A small contraction preserves the coheight of every point of coheight at most one. -/
private theorem coheight_map_of_isSmall {k : Type} [Field k] {X Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z} (hf : IsSmall k sZ sX f)
    (x : X) (hx : Order.coheight x ≤ 1) : Order.coheight (f x) = Order.coheight x := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := hf.exists_isIso
  have hP : x ∈ V.compl := fun hmem => by
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) x hmem
    exact absurd (this.trans hx) (by decide)
  obtain ⟨y, hy⟩ : x ∈ Set.range (Scheme.Opens.ι (X := X) V.compl) := by
    rw [Scheme.Opens.range_ι]; exact hP
  have h1 : f x = (Scheme.Opens.ι (X := Z) W.compl) (f.resLE W.compl V.compl hle y) := by
    rw [← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
  rw [h1, Topology.IsOpenEmbedding.coheight_eq _ (Scheme.Opens.ι (X := Z) W.compl).isOpenEmbedding,
    Topology.IsOpenEmbedding.coheight_eq _ (f.resLE W.compl V.compl hle).isOpenEmbedding,
    ← Topology.IsOpenEmbedding.coheight_eq _ (Scheme.Opens.ι (X := X) V.compl).isOpenEmbedding,
    hy]

/-- Over the biregular locus a morphism is injective. -/
private theorem eq_of_apply_eq_of_mem_biregularLocus {X Y : Scheme.{0}} (g : X ⟶ Y) {x x' : X}
    (h : g x = g x') (hx : g x ∈ (MMP.Mori.biregularLocus g : Y.Opens)) : x = x' := by
  haveI : IsIso (g ∣_ MMP.Mori.biregularLocus g) := MMP.Mori.isBiregular_biregularLocus g
  obtain ⟨a, ha⟩ : x ∈ Set.range (g ⁻¹ᵁ MMP.Mori.biregularLocus g).ι := by
    rw [Scheme.Opens.range_ι]; exact hx
  obtain ⟨a', ha'⟩ : x' ∈ Set.range (g ⁻¹ᵁ MMP.Mori.biregularLocus g).ι := by
    rw [Scheme.Opens.range_ι]
    change g x' ∈ (MMP.Mori.biregularLocus g : Y.Opens)
    rw [← h]; exact hx
  have hι : ∀ b, (MMP.Mori.biregularLocus g).ι ((g ∣_ MMP.Mori.biregularLocus g) b) =
      g ((g ⁻¹ᵁ MMP.Mori.biregularLocus g).ι b) := fun b => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hb : (g ∣_ MMP.Mori.biregularLocus g) a = (g ∣_ MMP.Mori.biregularLocus g) a' :=
    (MMP.Mori.biregularLocus g).ι.isOpenEmbedding.injective (by rw [hι, hι, ha, ha', h])
  rw [← ha, ← ha', (g ∣_ MMP.Mori.biregularLocus g).isOpenEmbedding.injective hb]

/-- Two points over a point of coheight at most one of a normal scheme, along a proper birational
morphism, coincide. -/
private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (g : X ⟶ Y) [IsProper g] (hg : IsBirationalMorphism g)
    {x x' : X} (h : g x = g x') (hx : Order.coheight (g x) ≤ 1) : x = x' :=
  eq_of_apply_eq_of_mem_biregularLocus g h
    (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg hx)

/-- The coefficient of a birational transform along a proper birational morphism at a prime
divisor `Q` is the coefficient at the prime divisor over `Q`. -/
private theorem coeff_transformDivisor_toRationalMap {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {g : X ⟶ Y}
    (hX : IsNormalVariety k (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    {G : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hGQ : g G.genericPoint = Q.genericPoint) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    (MMP.Mori.RationalMap.transformDivisor (X := X) g.toRationalMap D).coeff Q = D.coeff G := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨E, hE, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hg Q
  have hEG : E = G := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_of_coheight_le_one g hg (hE.trans hGQ.symm)
      (by rw [hE, Q.coheight_genericPoint]))
  subst hEG
  exact htr D

/-- The coefficient of an inverse transform along a proper birational morphism onto a normal
scheme at a prime divisor `F` lying over a prime divisor `Q` is the coefficient at `Q`. -/
private theorem coeff_inverseTransformDivisor {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (g : X ⟶ Y) [IsProper g] (hg : IsBirationalMorphism g)
    {F : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hFQ : g F.genericPoint = Q.genericPoint) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) :
    (inverseTransformDivisor g D).coeff F = D.coeff Q := by
  have hV : g F.genericPoint ∈ MMP.Mori.biregularLocus g :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
      (by rw [hFQ, Q.coheight_genericPoint])
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hFQ hV)
    (fun Q' hQ' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hQ').1.symm.trans hFQ)) D

/-- A point of coheight at most one of an integral scheme is the generic point or the generic
point of a prime divisor. -/
private theorem eq_genericPoint_or_exists_primeDivisor {X : Scheme.{0}} [IsIntegral X] {x : X}
    (hx : Order.coheight x ≤ 1) :
    x = genericPoint X ∨ ∃ P : MMP.Mori.PrimeDivisor X, P.genericPoint = x := by
  rcases hx.lt_or_eq with h0 | h1
  · left
    have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h0)
    have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have h1 : x ⤳ genericPoint X := hmax (show x ≤ genericPoint X from hgen)
    exact (h1.antisymm hgen).eq
  · exact Or.inr ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1⟩

end Generalities

/-! ### Rational top forms along birational morphisms -/

section Forms

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] {sZ : Z ⟶ Spec (.of ℂ)}
  [LocallyOfFiniteType sZ]

/-- Pull-back of rational top forms along a birational morphism is surjective. -/
private theorem exists_pullbackRationalPluriForms_eq (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ} (hd : topologicalKrullDim Z = d)
    (τ : RationalPluriForms (f ≫ sZ) d 1) :
    ∃ ω : RationalPluriForms sZ d 1, pullbackRationalPluriForms sZ f ω = τ := by
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hd
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd'
  obtain ⟨g, hg⟩ := hbij.2 ((ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1).repr τ ())
  refine ⟨g • ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1 (), ?_⟩
  change pullbackForms (K := Z.functionField) (K' := X.functionField) 1 _ = τ
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]
  change functionFieldMap f g • _ = τ
  rw [hg]
  exact basis_unit_repr_smul _ τ

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ} (hd : topologicalKrullDim Z = d) :
    pullbackRationalPluriForms sZ f (0 : RationalPluriForms sZ d 1) = 0 := by
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hd
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd'
  change pullbackForms (K := Z.functionField) (K' := X.functionField) 1 0 = 0
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp

/-- Pull-back of rational top forms along a birational morphism is injective on nonzero forms. -/
private theorem pullbackRationalPluriForms_ne_zero (f : X ⟶ Z) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ} (hd : topologicalKrullDim Z = d)
    {ω : RationalPluriForms sZ d 1} (hω0 : ω ≠ 0) : pullbackRationalPluriForms sZ f ω ≠ 0 := by
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hd
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hbij hd'
  have key := pullbackForms_eq (K' := X.functionField) hω₀ 1 ω
  intro h0
  have h : pullbackFormsAlong hω₀ 1 ω = 0 := key.symm.trans h0
  unfold pullbackFormsAlong at h
  apply hω0
  have hc := (smul_eq_zero.mp h).resolve_right
    ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).ne_zero ())
  have hc0 : (ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1).repr ω () = 0 :=
    (algebraMap Z.functionField X.functionField).injective (by rw [hc, map_zero])
  rw [← basis_unit_repr_smul (ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1) ω,
    hc0, zero_smul]
  rfl

variable [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian Z]
  [IsNormal Z] [CompactSpace Z]

/-- The push-forward of the divisor of a pulled-back form is the divisor of the form. -/
private theorem transformDivisor_divisorOfForm_pullback (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
    (hX : IsNormalVariety ℂ (f ≫ sZ)) [IsProper f] (hf : IsBirationalMorphism f)
    [LocallyOfFiniteType (f ≫ sZ)] {d : ℕ} (hd : topologicalKrullDim Z = d)
    (ω : RationalPluriForms sZ d 1) :
    haveI : IsDominant f := hf.isDominant
    MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap
      (divisorOfForm (pullbackRationalPluriForms sZ f ω)) = divisorOfForm ω := by
  haveI : IsDominant f := hf.isDominant
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hd
  refine Finsupp.ext fun Q => ?_
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hX hf Q
  haveI := hiso
  rw [htr]
  change E.ordForm _ = Q.ordForm ω
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hf.functionFieldMap_bijective
    hd' E Q heq ω

/-- The divisor of a form pulled back along a proper birational morphism contracting no divisor
is the inverse transform of the divisor of the form. -/
private theorem divisorOfForm_pullback_eq_inverseTransformDivisor (hZ : IsNormalVariety ℂ sZ)
    {g : X ⟶ Z} (hX : IsNormalVariety ℂ (g ≫ sZ)) [IsProper g] (hg : IsBirationalMorphism g)
    [LocallyOfFiniteType (g ≫ sZ)]
    (hcod : ∀ F : MMP.Mori.PrimeDivisor X, Order.coheight (g F.genericPoint) = 1) {d : ℕ}
    (hd : topologicalKrullDim Z = d) (ω : RationalPluriForms sZ d 1) :
    haveI : IsDominant g := hg.isDominant
    divisorOfForm (pullbackRationalPluriForms sZ g ω) =
      inverseTransformDivisor g (divisorOfForm ω) := by
  haveI : IsDominant g := hg.isDominant
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hd
  refine Finsupp.ext fun F => ?_
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ (hcod F)
  have hQ : g F.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ (hcod F)).symm
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hX hg Q
  have hEF : E = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_of_coheight_le_one g hg (heq.trans hQ.symm)
      (by rw [heq, Q.coheight_genericPoint]))
  subst hEF
  haveI := hiso
  rw [← DivisorWithCoeffs.coeff_apply,
    ← DivisorWithCoeffs.coeff_apply (inverseTransformDivisor g _),
    coeff_inverseTransformDivisor g hg hQ]
  change E.ordForm _ = Q.ordForm ω
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso g hg.functionFieldMap_bijective
    hd' E Q heq ω

end Forms

/-! ### Rational maps -/

section RationalMaps

/-- A complex scheme separated over `ℂ` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- Composing a rational map with two morphisms in turn is composing it with their composite. -/
private theorem compHom_compHom {X Y Z T : Scheme.{0}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- The rational map of a morphism, composed with a morphism, is the rational map of the
composite. -/
private theorem toRationalMap_compHom {X Z T : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ T) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-- If `h` is an inverse of `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_id_of_isInverse {W X : Scheme.{0}} [IsReduced W] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (p : W ⟶ X) {h : X.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he, rfl⟩ := hh
  have hsrc : e.source.ι ≫ p = e.iso.hom ≫ e.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
  change (e.symm.toPartialMap.compHom p).toRationalMap =
    (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap
  rw [Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [hsrc, Iso.inv_hom_id_assoc, Category.comp_id]

/-- A representative of an inverse of `p` is a section of `p`. -/
private theorem apply_hom_of_isInverse {W X : Scheme.{0}} [IsReduced W] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (p : W ⟶ X) {h : X.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (g' : X.PartialMap W)
    (hg' : g'.toRationalMap = h) {x : X} (hx : x ∈ g'.domain) : p (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom p).toRationalMap = (Scheme.Hom.toPartialMap (𝟙 X)).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', compHom_eq_id_of_isInverse p hh]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq h1 hx trivial
  change (g'.hom ≫ p) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- The transform of a prime divisor `G` of `X` along `q ∘ p⁻¹`, for `p : W ⟶ X` proper
birational onto a normal scheme, is read on the prime divisor `P` of `W` over `G`. -/
private theorem transformPrimeDivisor_compHom_eq_some_iff {W X Y : Scheme.{0}} [IsIntegral W]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X ↘ ⊤_ Scheme)]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (p : W ⟶ X) [IsProper p] (hp : IsBirationalMorphism p)
    {h : X.RationalMap W} (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (q : W ⟶ Y)
    {G : MMP.Mori.PrimeDivisor X} {P : MMP.Mori.PrimeDivisor W}
    (hPG : p P.genericPoint = G.genericPoint) (F : MMP.Mori.PrimeDivisor Y) :
    MMP.Mori.RationalMap.transformPrimeDivisor (h.compHom q) G = some F ↔
      q P.genericPoint = F.genericPoint := by
  have hG1 : Order.coheight G.genericPoint ≤ 1 := G.coheight_genericPoint.le
  have hdom := MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h
    (compHom_eq_id_of_isInverse p hh) hG1
  obtain ⟨g', hxg', hg'⟩ := Scheme.RationalMap.mem_domain.mp hdom
  have hpw := apply_hom_of_isInverse p hh g' hg' hxg'
  have hw : g'.hom ⟨G.genericPoint, hxg'⟩ = P.genericPoint :=
    eq_of_apply_eq_of_coheight_le_one p hp (hpw.trans hPG.symm) (by rw [hpw]; exact hG1)
  have hrep : (g'.compHom q).toRationalMap = h.compHom q := by
    rw [← hg', Scheme.RationalMap.compHom_toRationalMap]
  have hval : (g'.compHom q).hom ⟨G.genericPoint, hxg'⟩ = q P.genericPoint := by
    rw [← hw]
    rfl
  refine ⟨fun hT => ?_, fun hq => ?_⟩
  · rw [← hval]
    exact (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hT (g'.compHom q) hrep
      hxg').symm
  · refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
      ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g'.compHom q, hxg', hrep⟩, ?_⟩
    have h1 : MMP.Mori.RationalMap.transform (h.compHom q) G.idealSheaf.support =
        F.idealSheaf.support := by
      apply SetLike.coe_injective
      rw [MMP.Flips.coe_transform_eq_closure_singleton (g'.compHom q) hrep G hxg', hval, hq]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure F).symm
    have := F.integral
    rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- A partial map which is an open immersion represents a birational map. -/
private theorem isBirational_of_isOpenImmersion {X Y : Scheme.{0}} [IrreducibleSpace Y]
    (c : X.PartialMap Y) [IsOpenImmersion c.hom] [Nonempty c.domain] :
    MMP.Mori.RationalMap.IsBirational c.toRationalMap := by
  have hd : Dense (c.hom.opensRange : Set Y) :=
    c.hom.opensRange.2.dense ⟨_, Classical.arbitrary c.domain, rfl⟩
  refine ⟨⟨c.domain, c.dense_domain, c.hom.opensRange, hd, c.hom.isoOpensRange⟩, ?_⟩
  change Scheme.PartialMap.toRationalMap
    ⟨c.domain, c.dense_domain, c.hom.isoOpensRange.hom ≫ c.hom.opensRange.ι⟩ = _
  rw [Scheme.Hom.isoOpensRange_hom_ι]

/-- Restricting the source of a partial isomorphism does not change its rational map. -/
private theorem toRationalMap_restrictSource {X Y : Scheme.{0}} (e : X.PartialIso Y)
    (U : X.Opens) (hU : Dense (U : Set X)) (hUe : U ≤ e.source) :
    (e.restrictSource U hU hUe).toRationalMap = e.toRationalMap := by
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialIso.toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, hUe, ?_⟩
  have key : (Scheme.Opens.isoOfLE hUe).inv ≫ (e.source.ι ⁻¹ᵁ U).ι = X.homOfLE hUe := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  change X.homOfLE (le_refl U) ≫ (((Scheme.Opens.isoOfLE hUe).inv ≫
      (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ U)).hom) ≫
      (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ U)).hom) ≫
      (e.target.ι ''ᵁ (e.iso.hom ''ᵁ (e.source.ι ⁻¹ᵁ U))).ι =
    X.homOfLE hUe ≫ e.iso.hom ≫ e.target.ι
  rw [Scheme.homOfLE_rfl, Category.id_comp, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Category.assoc, Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, key]

/-- The composite `q ∘ p⁻¹` of a birational morphism with the inverse of another is
birational. -/
private theorem isBirational_compHom_of_isInverse {W X Y : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace X] [IrreducibleSpace Y] (p : W ⟶ X) {h : X.RationalMap W}
    (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (q : W ⟶ Y)
    (hq : IsBirationalMorphism q) [IsSeparated (Y ↘ ⊤_ Scheme)] [IsReduced W] :
    MMP.Mori.RationalMap.IsBirational (h.compHom q) := by
  obtain ⟨e₀, he₀, rfl⟩ := hh
  obtain ⟨e₁, he₁⟩ := hq
  have hsrc : e₁.source.ι ≫ q = e₁.iso.hom ≫ e₁.target.ι :=
    ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp he₁)).symm
  set U : W.Opens := e₀.source ⊓ e₁.source
  have hU : Dense (U : Set W) := e₀.dense_source.inter_of_isOpen_left e₁.dense_source
    e₀.source.isOpen
  set e₀' := e₀.restrictSource U hU inf_le_left
  have he₀' : e₀'.symm.toRationalMap = e₀.symm.toRationalMap :=
    MMP.Positivity.PartialIso.symm_toRationalMap_eq (toRationalMap_restrictSource e₀ U hU _)
  rw [← he₀', ← Scheme.RationalMap.compHom_toRationalMap]
  have hU1 : U.ι ≫ q = W.homOfLE (inf_le_right : U ≤ e₁.source) ≫ e₁.iso.hom ≫ e₁.target.ι := by
    rw [← hsrc, Scheme.homOfLE_ι_assoc]
  have hUq : IsOpenImmersion (U.ι ≫ q) := by rw [hU1]; infer_instance
  haveI : IsOpenImmersion (e₀'.symm.toPartialMap.compHom q).hom :=
    @IsOpenImmersion.comp _ _ _ e₀'.iso.inv (U.ι ≫ q) inferInstance hUq
  haveI : Nonempty (e₀'.symm.toPartialMap.compHom q).domain := by
    obtain ⟨z, hz⟩ := (e₀'.symm.toPartialMap.compHom q).dense_domain.nonempty
    exact ⟨⟨z, hz⟩⟩
  exact isBirational_of_isOpenImmersion _

/-- `d + 2 ≤ n` when `d + c = n` and `2 ≤ c`. -/
private theorem withBot_add_two_le_of {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n)
    (h2 : 2 ≤ c) : d + 2 ≤ n := by
  calc d + 2 = d + ((2 : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ d + (c : WithBot ℕ∞) := add_le_add le_rfl (WithBot.coe_le_coe.mpr h2)
    _ = n := h

/-- A prime divisor of `W` whose image has coheight at least two is exceptional. -/
private theorem isExceptionalPrimeDivisor_of_two_le_coheight {k : Type} [Field k]
    {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hn : topologicalKrullDim Y = n) {q : W ⟶ Y} (hW : IsNormalVariety k (q ≫ sY)) [IsProper q]
    (hq : IsBirationalMorphism q) (P : MMP.Mori.PrimeDivisor W)
    (h2 : 2 ≤ Order.coheight (q P.genericPoint)) : IsExceptionalPrimeDivisor sY q P := by
  refine ⟨hW, hq, inferInstance, ?_⟩
  unfold ProperDivisorOver.IsExceptional
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (q P.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_of h h2

end RationalMaps

/-! ### A smooth projective model dominating the program -/

section Tower

/-- A composite of proper birational morphisms onto normal integral schemes is birational. -/
private theorem isBirationalMorphism_comp' {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] [IsNormal Y] [IsNormal Z] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (p : X ⟶ Y) (f : Y ⟶ Z) [IsProper p] [IsProper f] (hp : IsBirationalMorphism p)
    (hf : IsBirationalMorphism f) : IsBirationalMorphism (p ≫ f) :=
  MMP.Mori.isBirationalMorphism_comp_of_isBirational f p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hp)

/-- **A smooth projective model dominating a sequence of elementary steps.** For models
`M₀, …, M_n` and steps `M_i ⟶ Z_i ⟵ M_{i+1}` of proper birational morphisms of normal projective
complex varieties, there is a smooth projective variety `W` with projective birational morphisms
`p_i : W ⟶ M_i`, `i ≤ m`, commuting with the steps. -/
private theorem exists_tower {M : ℕ → Scheme.{0}} [∀ i, IsIntegral (M i)]
    [∀ i, IsLocallyNoetherian (M i)] [∀ i, IsNormal (M i)] {Z : ℕ → Scheme.{0}}
    (s : ∀ i, M i ⟶ Spec (.of ℂ)) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) (f : ∀ i, M i ⟶ Z i)
    (fp : ∀ i, M (i + 1) ⟶ Z i) (n : ℕ)
    (hM : ∀ i ≤ n, MMP.Mori.IsProjectiveVariety ℂ (s i))
    (hZ : ∀ i < n, IsNormalVariety ℂ (sZ i))
    (hf : ∀ i < n, IsProper (f i) ∧ IsBirationalMorphism (f i) ∧ f i ≫ sZ i = s i)
    (hfp : ∀ i < n, IsProper (fp i) ∧ IsBirationalMorphism (fp i) ∧ fp i ≫ sZ i = s (i + 1)) :
    ∀ m ≤ n, ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (sW : W ⟶ Spec (.of ℂ)) (p : ∀ i, i ≤ m → (W ⟶ M i)),
      MMP.Mori.IsVariety ℂ sW ∧ IsSmoothScheme sW ∧ MMP.Mori.IsProjectiveVariety ℂ sW ∧
      (∀ i (hi : i ≤ m), p i hi ≫ s i = sW ∧ IsProjectiveMorphism (p i hi) ∧
        IsBirationalMorphism (p i hi)) ∧
      ∀ i (hi : i < m), p i hi.le ≫ f i = p (i + 1) hi ≫ fp i := by
  intro m
  induction m with
  | zero =>
    intro _
    have hM0 := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hM 0 (Nat.zero_le n))
    haveI : AlgebraicGeometry.IsVariety ℂ (s 0) := hM0.1
    have hX0 : IsNormalVariety ℂ (𝟙 (M 0) ≫ s 0) := by
      rw [Category.id_comp]; exact ⟨hM0.1, inferInstance⟩
    obtain ⟨W, w, hW, hwb, -, hsm, hwp, -, -, hproj⟩ :=
      MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (k := ℂ)
        (s 0) (ι := Unit) (X := fun _ => M 0) (fun _ => 𝟙 (M 0))
        (fun _ => isBirationalMorphism_of_isIso _) (fun _ => hX0) (κ := Empty) Empty.elim
        (fun j => j.elim)
    haveI : IsIntegral W := hW.1.toIsIntegral
    haveI : LocallyOfFiniteType (w ≫ s 0) := hW.1.toLocallyOfFiniteType
    haveI : QuasiCompact (w ≫ s 0) := hW.1.toQuasiCompact
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ s 0)
    haveI : IsNormal W := hW.2
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (w ≫ s 0)
    refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, w ≫ s 0,
      fun i hi => match i, hi with | 0, _ => w, hW.1, hsm, hproj (hM 0 (Nat.zero_le n)),
      fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    exact ⟨rfl, hwp, hwb⟩
  | succ m ih =>
    intro hm
    obtain ⟨W, _, _, _, _, sW, p, hWv, hWsm, hWproj, hp, hpq⟩ := ih (by omega)
    obtain ⟨hfP, hfB, hfs⟩ := hf m hm
    obtain ⟨hfpP, hfpB, hfps⟩ := hfp m hm
    have hZm := hZ m hm
    haveI : AlgebraicGeometry.IsVariety ℂ (sZ m) := hZm.1
    haveI : IsNormal (Z m) := hZm.2
    haveI : IsIntegral (Z m) := hZm.1.toIsIntegral
    haveI : LocallyOfFiniteType (sZ m) := hZm.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (Z m) := LocallyOfFiniteType.isLocallyNoetherian (sZ m)
    haveI := hfP
    haveI := hfpP
    obtain ⟨hpm, hpmP, hpmB⟩ := hp m le_rfl
    haveI : IsProper (p m le_rfl) := isProper_of_isProjectiveMorphism _ hpmP
    have hMm1 := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hM (m + 1) hm)
    let T : Bool → Scheme.{0} := fun b => cond b W (M (m + 1))
    let F : ∀ b, T b ⟶ Z m := fun b =>
      Bool.rec (motive := fun b => T b ⟶ Z m) (fp m) (p m le_rfl ≫ f m) b
    haveI hFP : ∀ b, IsProper (F b) := fun b => by
      cases b
      · exact hfpP
      · exact (inferInstance : IsProper (p m le_rfl ≫ f m))
    have hFB : ∀ b, IsBirationalMorphism (F b) := fun b => by
      cases b
      · exact hfpB
      · change IsBirationalMorphism (p m le_rfl ≫ f m)
        exact isBirationalMorphism_comp' _ _ hpmB hfB
    have hFN : ∀ b, IsNormalVariety ℂ (F b ≫ sZ m) := fun b => by
      cases b
      · change IsNormalVariety ℂ (fp m ≫ sZ m)
        rw [hfps]
        exact ⟨hMm1.1, inferInstance⟩
      · change IsNormalVariety ℂ ((p m le_rfl ≫ f m) ≫ sZ m)
        rw [Category.assoc, hfs, hpm]
        exact ⟨hWv, inferInstance⟩
    obtain ⟨W', w, hW', hwb, g, hsm, hwp, hg, -, -⟩ :=
      MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq (k := ℂ)
        (sZ m) (ι := Bool) (X := T) F hFB hFN (κ := Empty) Empty.elim (fun j => j.elim)
    haveI : IsIntegral W' := hW'.1.toIsIntegral
    haveI : LocallyOfFiniteType (w ≫ sZ m) := hW'.1.toLocallyOfFiniteType
    haveI : QuasiCompact (w ≫ sZ m) := hW'.1.toQuasiCompact
    haveI : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ m)
    haveI : IsNormal W' := hW'.2
    haveI : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ m)
    obtain ⟨hg1, hg1P, hg1B⟩ := hg true
    obtain ⟨hg0, hg0P, hg0B⟩ := hg false
    let gt : W' ⟶ W := g true
    let gf : W' ⟶ M (m + 1) := g false
    haveI : IsProper gt := isProper_of_isProjectiveMorphism _ hg1P
    have hgt : gt ≫ p m le_rfl ≫ f m = w := hg1
    have hgf : gf ≫ fp m = w := hg0
    have hsW : gt ≫ sW = w ≫ sZ m := by
      rw [← hgt, ← hpm, Category.assoc, Category.assoc, hfs]
    let p' : ∀ i, i ≤ m + 1 → (W' ⟶ M i) := fun i hi =>
      if h : i ≤ m then gt ≫ p i h else (by obtain rfl : i = m + 1 := (by omega); exact gf)
    have hp'1 : ∀ i (h : i ≤ m) (h' : i ≤ m + 1), p' i h' = gt ≫ p i h := fun i h h' => dif_pos h
    have hp'2 : p' (m + 1) le_rfl = gf := dif_neg (Nat.not_succ_le_self m)
    refine ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, w ≫ sZ m, p', hW'.1,
      hsm, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [← hsW]
      exact (MMP.Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hsW ▸ hW'.1,
        hg1P.comp ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hWproj).2⟩
    · by_cases h : i ≤ m
      · rw [hp'1 i h hi]
        obtain ⟨hpi, hpiP, hpiB⟩ := hp i h
        haveI : IsProper (p i h) := isProper_of_isProjectiveMorphism _ hpiP
        refine ⟨by rw [Category.assoc, hpi, hsW], hg1P.comp hpiP, isBirationalMorphism_comp' _ _
          hg1B hpiB⟩
      · obtain rfl : i = m + 1 := by omega
        rw [hp'2]
        exact ⟨by rw [← hfps, ← Category.assoc, hgf], hg0P, hg0B⟩
    · by_cases h : i + 1 ≤ m
      · rw [hp'1 i (by omega) hi.le, hp'1 (i + 1) h hi, Category.assoc, hpq i h, Category.assoc]
      · obtain rfl : i = m := by omega
        rw [hp'1 i le_rfl hi.le, hp'2, Category.assoc, hgt, hgf]

/-- The morphisms of a tower dominating a sequence of steps over `S` all lie over `S`. -/
private theorem tower_comp_eq {M Z : ℕ → Scheme.{0}} {W S : Scheme.{0}} (f : ∀ i, M i ⟶ Z i)
    (fp : ∀ i, M (i + 1) ⟶ Z i) (hZ : ∀ i, Z i ⟶ S) (π : ∀ i, M i ⟶ S) (n : ℕ)
    (hf : ∀ i < n, f i ≫ hZ i = π i) (hfp : ∀ i < n, fp i ≫ hZ i = π (i + 1))
    (p : ∀ i, i ≤ n → (W ⟶ M i))
    (hpq : ∀ i (hi : i < n), p i hi.le ≫ f i = p (i + 1) hi ≫ fp i) :
    ∀ i (hi : i ≤ n), p i hi ≫ π i = p 0 (Nat.zero_le n) ≫ π 0 := by
  intro i
  induction i with
  | zero => exact fun _ => rfl
  | succ j ih =>
    intro hj
    rw [← hfp j hj, ← Category.assoc, ← hpq j hj, Category.assoc, hf j hj]
    exact ih (Nat.le_of_succ_le hj)

end Tower

/-! ### Discrepancies on a common model -/

section Discrepancies

/-- Pull-back of rational top forms along a composite of morphisms inducing isomorphisms of
function fields is the composite of the pull-backs. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f] [IsDominant g] [LocallyOfFiniteType (f ≫ sX)]
    (hf : Function.Bijective (functionFieldMap f)) (hg : Function.Bijective (functionFieldMap g))
    {d : ℕ} (hd : topologicalKrullDim X = d) {m : ℤ} (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd'
  have hdY : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd'
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hdY
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The divisor of the pull-back of a form along a morphism depends only on the morphism. -/
private theorem divisorOfForm_pullback_congr {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {sX : X ⟶ Spec (.of ℂ)} {f g : Y ⟶ X}
    [IsDominant f] [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] [LocallyOfFiniteType (g ≫ sX)]
    (h : f = g) {d : ℕ} (τ : RationalPluriForms sX d 1) :
    divisorOfForm (pullbackRationalPluriForms sX f τ) =
      divisorOfForm (pullbackRationalPluriForms sX g τ) := by
  subst h
  rfl

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-- The valuation of a prime divisor `P` of `W` through `p : W ⟶ X`, restricted to `k(Z)` along
`f : X ⟶ Z`, is its valuation through `p ≫ f`. -/
private theorem valuation_comap_functionFieldMap {k : Type} [Field k] {W X Z : Scheme.{0}}
    [IsIntegral X] [IsIntegral Z] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {p : W ⟶ X} {h : W ⟶ Z} {f : X ⟶ Z} [IsDominant f] [IsProper p] [IsProper h]
    (hph : p ≫ f = h) (hWp : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p)
    (hWh : IsNormalVariety k (h ≫ sZ)) (hh : IsBirationalMorphism h)
    (P : MMP.Mori.PrimeDivisor W) :
    (ProperDivisorOver.mk ⟨W, p, hWp, hp, P⟩ inferInstance :
        ProperDivisorOver k sX).valuation.comap (functionFieldMap f) =
      (ProperDivisorOver.mk ⟨W, h, hWh, hh, P⟩ inferInstance :
        ProperDivisorOver k sZ).valuation := by
  subst hph
  haveI : IsIntegral W := hWp.1.toIsIntegral
  haveI : IsNormal W := hWp.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : IsDominant p := hp.isDominant
  refine Valuation.ext fun t => ?_
  change P.divisorialValuation (functionFieldMap p (functionFieldMap f t)) =
    P.divisorialValuation (functionFieldMap (p ≫ f) t)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

open scoped WithZero in
/-- **The discrepancy does not depend on the canonical divisor within its linear equivalence
class.** If `a = a(F, D)` is computed with a canonical divisor `K` and `K₂ ∼ K` is another
canonical divisor, then `a` is also the discrepancy computed with `K₂`: for `K₂ = K + div(φ)`
replace `ω` by `φ ω` and add `div(φ)` to the presentation of `K + D`; both the order of the form
and the coefficient of the pull-back change by `v_E(φ)`. -/
private theorem isDiscrepancy_of_linearlyEquivalent {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K K₂ : Divisor X} {D : RDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : IsDiscrepancy sX n K D F a) (hK₂ : K₂.IsCanonicalDivisor sX n)
    (hl : K₂.LinearlyEquivalent K) : IsDiscrepancy sX n K₂ D F a := by
  obtain ⟨-, -, hF, E, ω, m, r, L, hEF, hωK, hX, hn, hω0, hLc, hsum, Lp, hLp, ha⟩ := h
  obtain ⟨φ, hφ⟩ := hl
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : QuasiCompact (E.f ≫ sX) := E.isNormalVariety.1.toQuasiCompact
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  set Z0 : irreducibleComponents X := pointComponent (genericPoint X) with hZ0
  set c : X.functionField := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
    with hc_def
  have hc : c ≠ 0 := (φ.isUnit.map _).ne_zero
  have hZ : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.component = Z0 := fun Γ => Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  have hcΓ : ∀ Γ : MMP.Mori.PrimeDivisor X,
      Scheme.ord c Γ.genericPoint = (principalDivisor φ).coeff Γ := by
    intro Γ
    rw [coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have hK₂e : K₂ = K + principalDivisor φ := by rw [← hφ]; abel
  have hcω0 : c • ω ≠ 0 := smul_ne_zero hc hω0
  have hdiv : divisorOfForm (c • ω) = K₂ := by
    refine Finsupp.ext fun Γ => ?_
    change (divisorOfForm (c • ω)).coeff Γ = K₂.coeff Γ
    rw [coeff_divisorOfForm, Γ.ordForm_smul_of_topologicalKrullDim_eq hn hc hω0, hK₂e,
      DivisorWithCoeffs.coeff_add, ← hωK, coeff_divisorOfForm, hcΓ]
    ring
  have hφE : ∀ Z, E.f (componentGenericPoint E.Y Z) ∉ (principalDivisor φ).supp :=
    MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant E.f _
  have hN' := Divisor.isPullback_principalDivisor φ hφE
  have hN'E : ((principalDivisor (pullbackRationalFunction E.f φ hφE)).coeff E.E : ℝ) =
      Scheme.ord (functionFieldMap E.f c) E.E.genericPoint := by
    exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hN'
      (Divisor.isLocalEquation_principalDivisor φ ⊤) E.E trivial Z0
  have hord : E.toDivisorOver.ordPullback (c • ω) =
      E.toDivisorOver.ordPullback ω + Scheme.ord (functionFieldMap E.f c) E.E.genericPoint := by
    let := functionFieldAlgebra sX
    obtain ⟨b, N, hN⟩ := E.toDivisorOver.exists_ordPullback_eq hX hn
    have hb0 : (ZTensorPower.basis b 1).repr ω () ≠ 0 := repr_ne_zero_of_ne_zero b hω0
    have hrep : (ZTensorPower.basis b 1).repr (c • ω) () =
        c * (ZTensorPower.basis b 1).repr ω () :=
      congrArg (· ()) (LinearEquiv.map_smul (ZTensorPower.basis b 1).repr c ω)
    rw [hN 1 _ hcω0, hN 1 ω hω0, hrep, map_mul,
      Scheme.ord_mul ((map_ne_zero (functionFieldMap E.f)).mpr hc)
        ((map_ne_zero (functionFieldMap E.f)).mpr hb0)]
    ring
  have hLc₂ : ∀ j, (Fin.cons (principalDivisor φ) L : Fin (m + 1) → Divisor X) j |>.IsCartier :=
    Fin.cases (Divisor.isCartier_principalDivisor φ) hLc
  have hsum₂ : Divisor.toRDivisor (divisorOfForm (c • ω)) + D =
      ∑ j, (Fin.cons 1 r : Fin (m + 1) → ℝ) j •
        Divisor.toRDivisor ((Fin.cons (principalDivisor φ) L : Fin (m + 1) → Divisor X) j) := by
    rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, one_smul]
    simp only [Fin.cons_succ]
    rw [← hsum, hdiv, hK₂e, map_add, ← hωK]
    abel
  refine ⟨hK₂, ⟨m + 1, Fin.cons 1 r, Fin.cons (principalDivisor φ) L, hLc₂, ?_⟩, hF, E, c • ω,
    m + 1, Fin.cons 1 r, Fin.cons (principalDivisor φ) L, hEF, hdiv, hX, hn, hcω0, hLc₂, hsum₂,
    Fin.cons (principalDivisor (pullbackRationalFunction E.f φ hφE)) Lp,
    Fin.cases ⟨hφE, hN'⟩ hLp, ?_⟩
  · rw [← hdiv, hsum₂]
    simp only [toRDivisor_eq_mapCoeffs]
  · rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, one_mul, hN'E, hord, ha]
    simp only [Fin.cons_succ]
    push_cast
    ring

open scoped WithZero in
/-- Discrepancies only depend on the structure morphism. -/
private theorem isDiscrepancy_of_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {s s' : X ⟶ Spec (.of ℂ)} (h : s = s')
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] {n : ℕ} {K : Divisor X} {D : RDivisor X}
    {v : Valuation X.functionField ℤᵐ⁰} {a : ℝ} (ha : IsDiscrepancy s n K D v a) :
    IsDiscrepancy s' n K D v a := by
  subst h
  exact ha

/-- Two canonical divisors of a normal complex variety are linearly equivalent. -/
private theorem linearlyEquivalent_of_isCanonicalDivisor_of_isNormalVariety {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} {K K' : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hK' : K'.IsCanonicalDivisor sX n) : K.LinearlyEquivalent K' := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨τ, hτ0, hτ⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  have hτK : divisorOfForm τ = K := Finsupp.ext hτ
  have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK' hτ0
  rwa [one_zsmul, hτK] at h

/-- A divisor linearly equivalent to `K'` differs from it by a divisor linearly equivalent to
zero. -/
private theorem sub_linearlyEquivalent_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {K K' : Divisor X}
    (h : K.LinearlyEquivalent K') : (K - K').LinearlyEquivalent 0 := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, by rwa [sub_zero]⟩

/-- The exceptional set of a morphism, the points with no open neighbourhood on which it is an
open immersion, lies in the complement of the preimage of its biregular locus. -/
private theorem flipsExceptionalSet_subset {X Y : Scheme.{0}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hmem
  apply hy
  haveI : IsIso (f ∣_ MMP.Mori.biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ MMP.Mori.biregularLocus f, not_not.mp hmem, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- A divisor over `X` whose image has coheight at most one is not exceptional. -/
private theorem not_isExceptional_of_coheight_le_one {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : ProperDivisorOver k sX)
    (h : Order.coheight (E.f E.E.genericPoint) ≤ 1) : ¬ E.IsExceptional := by
  intro hE
  unfold ProperDivisorOver.IsExceptional at hE
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hE
  have e := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (E.f E.E.genericPoint)
  rw [hn] at e
  generalize topologicalKrullDim (closure {E.f E.E.genericPoint} : Set X) = a at hE e
  generalize Order.coheight (E.f E.E.genericPoint) = c at h e
  induction a using WithBot.recBotCoe with
  | bot => simp at e
  | coe a =>
    have e' : a + c = (n : ℕ∞) := by exact_mod_cast e
    have hE' : a + 2 ≤ (n : ℕ∞) := by
      rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at hE
      exact_mod_cast hE
    clear e hE
    induction a using ENat.recTopCoe with
    | top => simp at e'
    | coe m =>
      induction c using ENat.recTopCoe with
      | top => simp at h
      | coe j =>
        have e2 : m + j = n := by exact_mod_cast e'
        have h2 : m + 2 ≤ n := by exact_mod_cast hE'
        have h3 : j ≤ 1 := by exact_mod_cast h
        omega

/-- A prime divisor which is not exceptional over `Z` maps to a point of coheight one. -/
private theorem coheight_map_eq_one_of_not_isExceptionalPrimeDivisor {Y Z : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) {g : Y ⟶ Z} [IsProper g] (hY : IsNormalVariety ℂ (g ≫ sZ))
    (hg : IsBirationalMorphism g) {n : ℕ} (hn : topologicalKrullDim Z = n)
    (P : MMP.Mori.PrimeDivisor Y) (hP : ¬ IsExceptionalPrimeDivisor sZ g P) :
    Order.coheight (g P.genericPoint) = 1 := by
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI := hZ.1
  haveI := hY.1
  have hdim : topologicalKrullDim Y = topologicalKrullDim Z :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (g ≫ sZ) hg).symm
  refine le_antisymm ?_ ?_
  · by_contra h
    have h2 : 2 ≤ Order.coheight (g P.genericPoint) := by
      simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h)
    exact hP (isExceptionalPrimeDivisor_of_two_le_coheight hn hY hg P h2)
  · rw [← P.coheight_genericPoint]
    exact coheight_le_coheight_map sZ (g ≫ sZ) hZ.1 hY.1 g rfl hdim _

/-- The coefficient of the birational inverse transform `g⁻¹_* D` along a prime divisor `F` over
a prime divisor `Q` is the coefficient of `D` along `Q`. -/
private theorem coeff_birationalInverseTransform {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY) {g : X ⟶ Y}
    (hX : IsNormalVariety ℂ (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    {F : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hFQ : g F.genericPoint = Q.genericPoint) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) :
    (birationalInverseTransform g hg D).coeff F = D.coeff Q := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsSeparated (g ≫ sY) := hX.1.toIsSeparated
  haveI := isSeparated_toTerminal sY
  haveI := isSeparated_toTerminal (g ≫ sY)
  have hh := MMP.Mori.RationalMap.IsBirational.isInverse_inverse hg
  have e : MMP.Mori.RationalMap.IsBirational.inverse hg =
      (MMP.Mori.RationalMap.IsBirational.inverse hg).compHom (𝟙 X) := by
    obtain ⟨φ, hφ⟩ := (MMP.Mori.RationalMap.IsBirational.inverse hg).exists_rep
    rw [← hφ, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
  have key : ∀ {Q' : MMP.Mori.PrimeDivisor Y} {F' : MMP.Mori.PrimeDivisor X},
      g F'.genericPoint = Q'.genericPoint → ∀ F'' : MMP.Mori.PrimeDivisor X,
      (MMP.Mori.RationalMap.transformPrimeDivisor
        (MMP.Mori.RationalMap.IsBirational.inverse hg) Q' = some F'' ↔
        F'.genericPoint = F''.genericPoint) := by
    intro Q' F' h F''
    rw [e]
    exact transformPrimeDivisor_compHom_eq_some_iff g hg hh (𝟙 X) h F''
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq ((key hFQ F).mpr rfl)
    (fun Q' hQ' => ?_) D
  obtain ⟨F', hF', -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hY hX hg Q'
  have h1 := (key hF' F).mp hQ'
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hF'.symm.trans (by rw [h1]; exact hFQ))

end Discrepancies

/-! ### One step of the program -/

section Step

variable {Xa Xb Z : Scheme.{0}} [IsIntegral Xa] [CompactSpace Xa] [IsLocallyNoetherian Xa]
  [IsNormal Xa] [IsIntegral Xb] [CompactSpace Xb] [IsLocallyNoetherian Xb] [IsNormal Xb]
  {sa : Xa ⟶ Spec (.of ℂ)} {sb : Xb ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  {f : Xa ⟶ Z} {fp : Xb ⟶ Z} {Ka : Divisor Xa} {Ba : RDivisor Xa} {Kb : Divisor Xb}
  {Bb : RDivisor Xb}

variable (sa sb sZ f fp Ka Ba Kb Bb) in
/-- An elementary step `X_a ⟶ Z ⟵ X_b` of a `(K + B)`-program between projective
`ℚ`-factorial varieties: `f` is a `(K_a + B_a)`-negative birational contraction, `f⁺` is a
proper birational morphism contracting no divisor, `B_b = (f⁺)⁻¹_* f_* B_a`, `K_b + B_b` is
`f⁺`-nef, and either `f` is divisorial and `f⁺` an isomorphism, or `f` is small. -/
private structure IsStep : Prop where
  isNormalVariety_target : IsNormalVariety ℂ sZ
  isContraction : IsContraction ℂ sZ sa f
  isProper : IsProper f
  isProper_flip : IsProper fp
  comp_eq : f ≫ sZ = sa
  comp_eq_flip : fp ≫ sZ = sb
  isProjectiveVariety_source : MMP.Mori.IsProjectiveVariety ℂ sa
  isProjectiveVariety_flip : MMP.Mori.IsProjectiveVariety ℂ sb
  isQFactorial_source : IsQFactorial sa
  isQFactorial_flip : IsQFactorial sb
  isBirationalMorphism : IsBirationalMorphism f
  isBirationalMorphism_flip : IsBirationalMorphism fp
  coheight_flip : ∀ y : Xb, Order.coheight y ≤ 1 → Order.coheight (fp y) = Order.coheight y
  isCanonicalDivisor_source : ∃ n : ℕ, Ka.IsCanonicalDivisor sa n
  isCanonicalDivisor_flip : ∃ n : ℕ, Kb.IsCanonicalDivisor sb n
  eq_flipTransform : Bb = flipTransform f fp Ba
  isRelativelyAntiAmple : IsRelativelyAntiAmple f (logCanonicalDivisor Ka Ba)
  isRelativelyNef_flip : IsRelativelyNef ℂ sb fp (logCanonicalDivisor Kb Bb)
  divisorial_or_small : (IsIso fp ∧ ∃ E : MMP.Mori.PrimeDivisor Xa,
      (MMP.Mori.exceptionalSet f : Set Xa) = E.support) ∨
    ∀ x : Xa, Order.coheight x ≤ 1 → Order.coheight (f x) = Order.coheight x

/-- The canonical divisor `(f⁺)⁻¹_* f_* K'` of a step is again the divisor of a rational top
form, when `K'` is. -/
private theorem IsStep.exists_divisorOfForm_eq [LocallyOfFiniteType sa] [LocallyOfFiniteType sb]
    (hS : IsStep sa sb sZ f fp Ka Ba Kb Bb)
    {K' : Divisor Xa} {d : ℕ} (hd : topologicalKrullDim Xa = d) {τ : RationalPluriForms sa d 1}
    (hτ : τ ≠ 0) (hτK : divisorOfForm τ = K') :
    ∃ τ' : RationalPluriForms sb d 1, τ' ≠ 0 ∧ divisorOfForm τ' = flipTransform f fp K' := by
  have hZ := hS.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := (hZ.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI := hS.isProper
  haveI := hS.isProper_flip
  haveI : IsDominant f := hS.isBirationalMorphism.isDominant
  haveI : IsDominant fp := hS.isBirationalMorphism_flip.isDominant
  have hXa := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS.isProjectiveVariety_source
  have hXb := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS.isProjectiveVariety_flip
  haveI := hZ.1
  haveI := hXa.1
  have hdZ : topologicalKrullDim Z = d :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sa
      hS.isBirationalMorphism).trans hd
  have hfs := hS.comp_eq
  have hfps := hS.comp_eq_flip
  have hXan : IsNormalVariety ℂ (f ≫ sZ) := by rw [hfs]; exact ⟨hXa.1, inferInstance⟩
  have hXbn : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hfps]; exact ⟨hXb.1, inferInstance⟩
  have hcod : ∀ F : MMP.Mori.PrimeDivisor Xb, Order.coheight (fp F.genericPoint) = 1 := fun F => by
    rw [hS.coheight_flip _ F.coheight_genericPoint.le, F.coheight_genericPoint]
  subst hfs hfps
  obtain ⟨ω, rfl⟩ :=
    exists_pullbackRationalPluriForms_eq f hS.isBirationalMorphism.functionFieldMap_bijective hdZ τ
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hτ (pullbackRationalPluriForms_zero f hS.isBirationalMorphism.functionFieldMap_bijective
      hdZ)
  refine ⟨pullbackRationalPluriForms sZ fp ω,
    pullbackRationalPluriForms_ne_zero fp hS.isBirationalMorphism_flip.functionFieldMap_bijective
      hdZ hω0, ?_⟩
  rw [← hτK]
  change _ = inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := Xa)
    f.toRationalMap (divisorOfForm (pullbackRationalPluriForms sZ f ω)))
  rw [transformDivisor_divisorOfForm_pullback hZ hXan hS.isBirationalMorphism hdZ ω,
    divisorOfForm_pullback_eq_inverseTransformDivisor hZ hXbn hS.isBirationalMorphism_flip hcod
      hdZ ω]

/-- Points of a common model over a codimension-one point of `X_b` lie over a
codimension-one point of `X_a`, and the transform `(f⁺)⁻¹_* f_*` reads coefficients there. -/
private theorem IsStep.coeff_flipTransform (hS : IsStep sa sb sZ f fp Ka Ba Kb Bb)
    {W : Scheme.{0}} [IsIntegral W] {sW : W ⟶ Spec (.of ℂ)} (hW : IsNormalVariety ℂ sW)
    (p : W ⟶ Xa) (q : W ⟶ Xb) (hps : p ≫ sa = sW) (hqs : q ≫ sb = sW) (hpq : p ≫ f = q ≫ fp)
    (x : W) (hx : Order.coheight (q x) ≤ 1) :
    Order.coheight (p x) ≤ 1 ∧ ∀ (G : MMP.Mori.PrimeDivisor Xa) (F : MMP.Mori.PrimeDivisor Xb),
      p x = G.genericPoint → q x = F.genericPoint → ∀ {R : Type} [AddCommMonoid R]
        (D : DivisorWithCoeffs R Xa), (flipTransform f fp D).coeff F = D.coeff G := by
  have hZ := hS.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hS.isProper
  haveI := hS.isProper_flip
  have hXa := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS.isProjectiveVariety_source
  have hXb := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS.isProjectiveVariety_flip
  haveI := hZ.1
  haveI := hXa.1
  have hdim : topologicalKrullDim Xa = topologicalKrullDim Z :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sa
      hS.isBirationalMorphism).symm
  have hfp : Order.coheight (fp (q x)) ≤ 1 := by rwa [hS.coheight_flip _ hx]
  have hpx : f (p x) = fp (q x) := by
    rw [← Scheme.Hom.comp_apply, hpq, Scheme.Hom.comp_apply]
  refine ⟨(coheight_le_coheight_map sZ sa hZ.1 hXa.1 f hS.comp_eq hdim (p x)).trans
    (hpx ▸ hfp), fun G F hG hF => ?_⟩
  intro R _ D
  have hF1 : Order.coheight (fp F.genericPoint) = 1 := by
    rw [← hF, hS.coheight_flip _ hx, hF, F.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hF1
  have hQ : fp F.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hF1).symm
  have hGQ : f G.genericPoint = Q.genericPoint := by rw [← hG, hpx, hF, hQ]
  have hXan : IsNormalVariety ℂ (f ≫ sZ) := by rw [hS.comp_eq]; exact ⟨hXa.1, inferInstance⟩
  change (inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := Xa)
    f.toRationalMap D)).coeff F = D.coeff G
  rw [coeff_inverseTransformDivisor fp hS.isBirationalMorphism_flip hQ,
    coeff_transformDivisor_toRationalMap hZ hXan hS.isBirationalMorphism hGQ]

/-- If the exceptional set of a birational morphism `f` is the support of a prime divisor `E`,
then so is the exceptional set of `f ≫ inv f⁺` for an isomorphism `f⁺`. -/
private theorem exceptionalSet_comp_inv_eq {X Y T : Scheme.{0}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (f : X ⟶ T) (fp : Y ⟶ T) [IsIso fp] [IsProper f]
    (hf : IsBirationalMorphism f) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) :
    MMP.Flips.exceptionalSet (f ≫ inv fp) = (E.support : Set X) := by
  apply Set.Subset.antisymm
  · intro y hy
    rw [← hE]
    by_contra hmem
    apply hy
    haveI : IsIso (f ∣_ MMP.Mori.biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
    refine ⟨f ⁻¹ᵁ MMP.Mori.biregularLocus f, not_not.mp hmem, ?_⟩
    rw [← Category.assoc, ← morphismRestrict_ι]
    infer_instance
  · intro y hy hV
    obtain ⟨V, hyV, hV⟩ := hV
    have hsp : E.genericPoint ⤳ y := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
      exact specializes_iff_mem_closure.mpr hy
    have hηV : E.genericPoint ∈ V := hsp.mem_open V.isOpen hyV
    have hη : E.genericPoint ∉ MMP.Flips.exceptionalSet (f ≫ inv fp) :=
      fun h => h ⟨V, hηV, hV⟩
    have h1 := MMP.Flips.coheight_map_of_notMem_exceptionalSet hη
    rw [Scheme.Hom.comp_apply, coheight_map_of_isIso, E.coheight_genericPoint] at h1
    have hmem : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
      rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    exact hmem (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f
      hf h1.le)

/-- If `f (p η_P)` has coheight at least two while `p η_P` has coheight at most one, then `p`
maps the support of `P` into the prime divisor `E` supporting the exceptional set of `f`. -/
private theorem image_support_subset_of_two_le_coheight {W X T : Scheme.{0}} (f : X ⟶ T)
    (p : W ⟶ X) (P : MMP.Mori.PrimeDivisor W) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support)
    (hf2 : 2 ≤ Order.coheight (f (p P.genericPoint)))
    (hp1 : Order.coheight (p P.genericPoint) ≤ 1) :
    p '' (P.support : Set W) ⊆ E.support := by
  have hpE : p P.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
    by_contra hn
    have hn' : p P.genericPoint ∉ MMP.Flips.exceptionalSet f :=
      fun h => hn (flipsExceptionalSet_subset f h)
    rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hn'] at hf2
    exact absurd (hf2.trans hp1) (by decide)
  rw [hE] at hpE
  have hcl : IsClosed (E.support : Set X) := hE ▸ (MMP.Mori.exceptionalSet f).isClosed
  rintro y ⟨x, hx, rfl⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact ((specializes_iff_mem_closure.mpr hx).map p.continuous).mem_closed hcl hpE

/-- In the divisorial case `f⁺` is an isomorphism, and the birational transform of `B` along
`f ≫ (f⁺)⁻¹` is `(f⁺)⁻¹_* f_* B`. -/
private theorem transformDivisor_comp_inv_eq_flipTransform (hZ : IsNormalVariety ℂ sZ)
    [IsProper f] [IsProper fp] [IsIso fp] (hf : IsBirationalMorphism f)
    (hfp : IsBirationalMorphism fp) (hXan : IsNormalVariety ℂ (f ≫ sZ))
    (hXbn : IsNormalVariety ℂ (fp ≫ sZ))
    (hcod : ∀ F : MMP.Mori.PrimeDivisor Xb, Order.coheight (fp F.genericPoint) = 1)
    (B : RDivisor Xa) :
    MMP.Mori.RationalMap.transformDivisor (X := Xa) (f ≫ inv fp).toRationalMap B =
      flipTransform f fp B := by
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hs' : (f ≫ inv fp) ≫ fp ≫ sZ = f ≫ sZ := by simp
  have hXa' : IsNormalVariety ℂ ((f ≫ inv fp) ≫ fp ≫ sZ) := by rwa [hs']
  haveI : LocallyOfFiniteType ((f ≫ inv fp) ≫ fp ≫ sZ) := hXa'.1.toLocallyOfFiniteType
  have hf'b : IsBirationalMorphism (f ≫ inv fp) :=
    isBirationalMorphism_comp' f (inv fp) hf (isBirationalMorphism_of_isIso _)
  refine Finsupp.ext fun F => ?_
  have hF1 := hcod F
  have hQ : fp F.genericPoint =
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hF1 :
        MMP.Mori.PrimeDivisor Z).genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hF1).symm
  obtain ⟨G, hG, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZ hXan hf
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hF1)
  have hGF : (f ≫ inv fp) G.genericPoint = F.genericPoint := by
    rw [Scheme.Hom.comp_apply, hG.trans hQ.symm, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply (flipTransform f fp B),
    coeff_transformDivisor_toRationalMap hXbn hXa' hf'b hGF]
  change _ = (inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := Xa)
    f.toRationalMap B)).coeff F
  rw [coeff_inverseTransformDivisor fp hfp hQ,
    coeff_transformDivisor_toRationalMap hZ hXan hf hG]

/-- **The comparison of one step on a common model.** On a smooth common model `p : W ⟶ X_a`,
`q : W ⟶ X_b` of a step, with compatible canonical divisors `K'` and `(f⁺)⁻¹_* f_* K'`, the
difference `p^*(K' + B_a) - q^*((f⁺)⁻¹_* f_* K' + B_b)` is effective, vanishes along the primes
not contracted by `q`, and is positive along the primes contracted by `q` but not by `p`. -/
private theorem IsStep.coeff_sub [LocallyOfFiniteType sa] [LocallyOfFiniteType sb]
    (hS : IsStep sa sb sZ f fp Ka Ba Kb Bb)
    {K' : Divisor Xa} {d : ℕ} (hd : topologicalKrullDim Xa = d) {τ : RationalPluriForms sa d 1}
    (hτ : τ ≠ 0) (hτK : divisorOfForm τ = K')
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {sW : W ⟶ Spec (.of ℂ)} (hW : IsNormalVariety ℂ sW)
    (p : W ⟶ Xa) (q : W ⟶ Xb) [IsProper p] [IsProper q] (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hps : p ≫ sa = sW) (hqs : q ≫ sb = sW)
    (hpq : p ≫ f = q ≫ fp) {Ga Gb : RDivisor W}
    (hGa : IsRCartierPullback p (logCanonicalDivisor K' Ba) Ga)
    (hGb : IsRCartierPullback q (logCanonicalDivisor (flipTransform f fp K') Bb) Gb)
    (P : MMP.Mori.PrimeDivisor W) :
    0 ≤ (Ga - Gb).coeff P ∧
      (Order.coheight (q P.genericPoint) ≤ 1 → (Ga - Gb).coeff P = 0) ∧
      (Order.coheight (p P.genericPoint) ≤ 1 → ¬ Order.coheight (q P.genericPoint) ≤ 1 →
        0 < (Ga - Gb).coeff P) := by
  have hZ := hS.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := (hZ.1.toQuasiCompact).compactSpace_of_compactSpace
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI := hS.isProper
  haveI := hS.isProper_flip
  haveI : IsDominant f := hS.isBirationalMorphism.isDominant
  haveI : IsDominant fp := hS.isBirationalMorphism_flip.isDominant
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hXa := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS.isProjectiveVariety_source
  have hXb := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS.isProjectiveVariety_flip
  haveI := hZ.1
  haveI := hXa.1
  haveI := hXb.1
  haveI : QuasiCompact sa := hXa.1.toQuasiCompact
  haveI : QuasiCompact sb := hXb.1.toQuasiCompact
  have hdZ : topologicalKrullDim Z = d :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sa
      hS.isBirationalMorphism).trans hd
  have hdb : topologicalKrullDim Xb = d :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sb
      hS.isBirationalMorphism_flip).symm.trans hdZ
  have hXan : IsNormalVariety ℂ sa := ⟨hXa.1, inferInstance⟩
  have hXbn : IsNormalVariety ℂ sb := ⟨hXb.1, inferInstance⟩
  obtain ⟨na, hKa⟩ := hS.isCanonicalDivisor_source
  obtain ⟨nb, hKb⟩ := hS.isCanonicalDivisor_flip
  have hna : na = d := by
    have := hKa.topologicalKrullDim_eq
    rw [hd] at this
    exact_mod_cast this.symm
  have hnb : nb = d := by
    have := hKb.topologicalKrullDim_eq
    rw [hdb] at this
    exact_mod_cast this.symm
  rw [hna] at hKa
  rw [hnb] at hKb
  have hK'Ka : K'.LinearlyEquivalent Ka := by
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXan hKa hτ
    rwa [one_zsmul, hτK] at h
  have hK'can : K'.IsCanonicalDivisor sa d := hKa.of_linearlyEquivalent hK'Ka
  have hcod : ∀ F : MMP.Mori.PrimeDivisor Xb, Order.coheight (fp F.genericPoint) = 1 :=
    fun F => by rw [hS.coheight_flip _ F.coheight_genericPoint.le, F.coheight_genericPoint]
  have hBXc := isCartierCombination_of_isQFactorial hS.isQFactorial_source
  have hBYc := isCartierCombination_of_isQFactorial hS.isQFactorial_flip
  have hanti := hS.isRelativelyAntiAmple
  have hnefb := hS.isRelativelyNef_flip
  have hBb := hS.eq_flipTransform
  have hcontr := hS.isContraction
  have hdiv := hS.divisorial_or_small
  have hfs := hS.comp_eq
  have hfps := hS.comp_eq_flip
  subst hfs hfps hBb
  have hbij := hS.isBirationalMorphism.functionFieldMap_bijective
  have hbijp := hS.isBirationalMorphism_flip.functionFieldMap_bijective
  obtain ⟨ω, rfl⟩ := exists_pullbackRationalPluriForms_eq f hbij hdZ τ
  have hω0 : ω ≠ 0 := by
    rintro rfl
    exact hτ (pullbackRationalPluriForms_zero f hbij hdZ)
  subst hτK
  have hωb0 : pullbackRationalPluriForms sZ fp ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero fp hbijp hdZ hω0
  have hKb' : divisorOfForm (pullbackRationalPluriForms sZ fp ω) =
      flipTransform f fp (divisorOfForm (pullbackRationalPluriForms sZ f ω)) := by
    change _ = inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := Xa)
      f.toRationalMap (divisorOfForm (pullbackRationalPluriForms sZ f ω)))
    rw [transformDivisor_divisorOfForm_pullback hZ hXan hS.isBirationalMorphism hdZ ω,
      divisorOfForm_pullback_eq_inverseTransformDivisor hZ hXbn hS.isBirationalMorphism_flip hcod
        hdZ ω]
  rw [← hKb'] at hGb
  have hKbKb : (divisorOfForm (pullbackRationalPluriForms sZ fp ω)).LinearlyEquivalent Kb := by
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXbn hKb hωb0
    rwa [one_zsmul] at h
  have hKbcan : (divisorOfForm (pullbackRationalPluriForms sZ fp ω)).IsCanonicalDivisor
      (fp ≫ sZ) d := hKb.of_linearlyEquivalent hKbKb
  have hWp : IsNormalVariety ℂ (p ≫ f ≫ sZ) := by rwa [hps]
  have hWq : IsNormalVariety ℂ (q ≫ fp ≫ sZ) := by rwa [hqs]
  haveI : LocallyOfFiniteType (p ≫ f ≫ sZ) := hWp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ fp ≫ sZ) := hWq.1.toLocallyOfFiniteType
  have hWcomp : divisorOfForm (pullbackRationalPluriForms (f ≫ sZ) p
        (pullbackRationalPluriForms sZ f ω)) =
      divisorOfForm (pullbackRationalPluriForms (fp ≫ sZ) q
        (pullbackRationalPluriForms sZ fp ω)) := by
    rw [pullbackRationalPluriForms_comp f p hbij hpb.functionFieldMap_bijective hdZ ω,
      pullbackRationalPluriForms_comp fp q hbijp hqb.functionFieldMap_bijective hdZ ω]
    exact divisorOfForm_pullback_congr hpq ω
  obtain ⟨aX, aY, hdX, hdY, -, hcoeff⟩ := pullback_sub_pullback_eq_sum_discrepancy hXan hXbn p q
    hWp hWq hpb hqb _ _ (pullbackRationalPluriForms_ne_zero f hbij hdZ hω0) hωb0 hK'can hKbcan
    hWcomp (hBXc _) (hBYc _) hGa hGb
  rw [hcoeff P]
  -- the valuation of `P` on `Z`
  have hpfb : IsBirationalMorphism (p ≫ f) := isBirationalMorphism_comp' p f hpb
    hS.isBirationalMorphism
  have hWZ : IsNormalVariety ℂ ((p ≫ f) ≫ sZ) := by rwa [Category.assoc]
  have hvX := valuation_comap_functionFieldMap rfl hWp hpb hWZ hpfb P
  have hvY := valuation_comap_functionFieldMap hpq.symm hWq hqb hWZ hpfb P
  have hpx : f (p P.genericPoint) = fp (q P.genericPoint) := by
    rw [← Scheme.Hom.comp_apply, hpq, Scheme.Hom.comp_apply]
  refine ⟨?_, ?_, ?_⟩
  · -- effectivity: the comparison of discrepancies over `Z`
    set D : RDivisor Z := MMP.Mori.RationalMap.transformDivisor (X := Xa) f.toRationalMap Ba
      with hD
    have e1 : birationalInverseTransform f hS.isBirationalMorphism D +
        (Ba - birationalInverseTransform f hS.isBirationalMorphism D) = Ba := by abel
    have e2 : birationalInverseTransform fp hS.isBirationalMorphism_flip D +
        (flipTransform f fp Ba - birationalInverseTransform fp hS.isBirationalMorphism_flip D) =
          flipTransform f fp Ba := by abel
    have hEX : ∀ P' : MMP.Mori.PrimeDivisor Xa, ¬ IsExceptionalPrimeDivisor sZ f P' →
        (Ba - birationalInverseTransform f hS.isBirationalMorphism D).coeff P' = 0 := by
      intro P' hP'
      have h1 := coheight_map_eq_one_of_not_isExceptionalPrimeDivisor hZ hXan
        hS.isBirationalMorphism hdZ P' hP'
      have hQ : f P'.genericPoint =
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1 :
            MMP.Mori.PrimeDivisor Z).genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm
      rw [DivisorWithCoeffs.coeff_sub,
        coeff_birationalInverseTransform hZ hXan hS.isBirationalMorphism hQ, hD,
        coeff_transformDivisor_toRationalMap hZ hXan hS.isBirationalMorphism hQ, sub_self]
    have hEY : ∀ P' : MMP.Mori.PrimeDivisor Xb, ¬ IsExceptionalPrimeDivisor sZ fp P' →
        (flipTransform f fp Ba -
          birationalInverseTransform fp hS.isBirationalMorphism_flip D).coeff P' = 0 := by
      intro P' hP'
      have h1 := coheight_map_eq_one_of_not_isExceptionalPrimeDivisor hZ hXbn
        hS.isBirationalMorphism_flip hdZ P' hP'
      have hQ : fp P'.genericPoint =
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1 :
            MMP.Mori.PrimeDivisor Z).genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm
      rw [DivisorWithCoeffs.coeff_sub,
        coeff_birationalInverseTransform hZ hXbn hS.isBirationalMorphism_flip hQ]
      change (inverseTransformDivisor fp D).coeff P' - _ = 0
      rw [coeff_inverseTransformDivisor fp hS.isBirationalMorphism_flip hQ, sub_self]
    have hAX : IsRelativelyNef ℂ (f ≫ sZ) f
        (-logCanonicalDivisor (divisorOfForm (pullbackRationalPluriForms sZ f ω))
          (birationalInverseTransform f hS.isBirationalMorphism D +
            (Ba - birationalInverseTransform f hS.isBirationalMorphism D))) := by
      rw [e1]
      have h1 := isRelativelyNef_of_isRelativelyAmple (k := ℂ) (f ≫ sZ)
        (hanti : IsRelativelyAmple f (-logCanonicalDivisor Ka Ba))
      have h2 := isRelativelyNef_add_of_linearlyEquivalent h1
        (sub_linearlyEquivalent_zero hK'Ka.symm)
      convert h2 using 1
      simp only [logCanonicalDivisor, map_sub]
      abel
    have hAY : IsRelativelyNef ℂ (fp ≫ sZ) fp
        (logCanonicalDivisor (divisorOfForm (pullbackRationalPluriForms sZ fp ω))
          (birationalInverseTransform fp hS.isBirationalMorphism_flip D +
            (flipTransform f fp Ba -
              birationalInverseTransform fp hS.isBirationalMorphism_flip D))) := by
      rw [e2]
      have h2 := isRelativelyNef_add_of_linearlyEquivalent hnefb
        (sub_linearlyEquivalent_zero hKbKb)
      convert h2 using 1
      simp only [logCanonicalDivisor, map_sub]
      abel
    have hle := (isDiscrepancy_le_of_isRelativelyNef hZ hXan hXbn hS.isBirationalMorphism
      hS.isBirationalMorphism_flip (ω := ω) rfl rfl hEX hEY hAX hAY
      (hasNonemptyCenter_valuation _) hvX hvY).2.2 (aX P) (aY P)
      (by rw [e1]; exact hdX P) (by rw [e2]; exact hdY P)
    linarith
  · -- vanishing along the primes not contracted by `q`
    intro hq1
    obtain ⟨hp1, htr⟩ := hS.coeff_flipTransform hW p q hps hqs hpq P.genericPoint hq1
    have hnexX := not_isExceptional_of_coheight_le_one hd
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance) hp1
    have hnexY := not_isExceptional_of_coheight_le_one hdb
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance) hq1
    obtain ⟨G, -, hG, -, hvG⟩ :=
      ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXan _ hnexX
    obtain ⟨F, -, hF, -, hvF⟩ :=
      ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXbn _ hnexY
    have haX := hdX P
    have haY := hdY P
    rw [hvG] at haX
    rw [hvF] at haY
    rw [haX.eq_neg_coeff, haY.eq_neg_coeff, htr G F hG hF Ba]
    ring
  · -- positivity along the primes contracted by `q` but not by `p`
    intro hp1 hq2
    have hq2' : 2 ≤ Order.coheight (q P.genericPoint) := by
      simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp hq2)
    have hdimb : topologicalKrullDim Xb = topologicalKrullDim Z := hdb.trans hdZ.symm
    have hfq : Order.coheight (q P.genericPoint) ≤ Order.coheight (fp (q P.genericPoint)) :=
      coheight_le_coheight_map sZ (fp ≫ sZ) hZ.1 hXb.1 fp rfl hdimb _
    have hf2 : 2 ≤ Order.coheight (f (p P.genericPoint)) := by
      rw [hpx]; exact hq2'.trans hfq
    rcases hdiv with ⟨hiso, E₀, hE₀⟩ | hsmall
    swap
    · exact absurd ((hf2.trans (hsmall _ hp1).le).trans hp1) (by decide)
    haveI := hiso
    -- the divisorial contraction `X_a ⟶ X_b`
    have hs' : (f ≫ inv fp) ≫ fp ≫ sZ = f ≫ sZ := by simp
    have hqf' : p ≫ f ≫ inv fp = q := by
      rw [← Category.assoc, hpq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have hf'b : IsBirationalMorphism (f ≫ inv fp) := isBirationalMorphism_comp' f (inv fp)
      hS.isBirationalMorphism (isBirationalMorphism_of_isIso _)
    have hXa' : IsNormalVariety ℂ ((f ≫ inv fp) ≫ fp ≫ sZ) := by rwa [hs']
    haveI : LocallyOfFiniteType ((f ≫ inv fp) ≫ fp ≫ sZ) := hXa'.1.toLocallyOfFiniteType
    have hcon : IsBirationalContraction ℂ (fp ≫ sZ) ((f ≫ inv fp) ≫ fp ≫ sZ) (f ≫ inv fp) :=
      { isVariety_target := hXb.1
        isVariety_source := hXa'.1
        comp_eq := rfl
        isProper := inferInstance
        isIso_app := fun U => by
          have h1 : IsIso ((inv fp).app U) := inferInstance
          have h2 := hcontr.isIso_app ((inv fp) ⁻¹ᵁ U)
          rw [Scheme.Hom.comp_app]
          exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
        dim_eq := hd.trans hdb.symm }
    have hEx := exceptionalSet_comp_inv_eq f fp hS.isBirationalMorphism hE₀
    have hA' : IsRelativelyAntiAmple (f ≫ inv fp) (logCanonicalDivisor Ka Ba) := by
      obtain ⟨m, r, L, hm, hr, hL, heq⟩ := hanti
      refine ⟨m, r, L, hm, hr, fun j => ?_, heq⟩
      obtain ⟨hc, hamp⟩ := hL j
      exact ⟨hc, fun U hU => hamp ((inv fp) ⁻¹ᵁ U) (hU.preimage_of_isIso (inv fp))⟩
    have hDY := transformDivisor_comp_inv_eq_flipTransform hZ hS.isBirationalMorphism
      hS.isBirationalMorphism_flip hXan hXbn hcod Ba
    -- forms computing `K_a` on `X_a` and its transform on `X_b`
    have hKa' : Ka.IsCanonicalDivisor ((f ≫ inv fp) ≫ fp ≫ sZ) d := by rwa [hs']
    obtain ⟨τa, hτa0, hτa⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXa' hKa'
    have hdivτa : divisorOfForm τa = Ka := Finsupp.ext hτa
    obtain ⟨ωb, rfl⟩ := exists_pullbackRationalPluriForms_eq (sZ := fp ≫ sZ) (f ≫ inv fp)
      hf'b.functionFieldMap_bijective hdb τa
    have hωb0 : ωb ≠ 0 := by
      rintro rfl
      exact hτa0 (pullbackRationalPluriForms_zero (sZ := fp ≫ sZ) (f ≫ inv fp)
        hf'b.functionFieldMap_bijective hdb)
    have hωbKb : (divisorOfForm ωb).LinearlyEquivalent Kb := by
      have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXbn hKb hωb0
      rwa [one_zsmul] at h
    have hωbcan : (divisorOfForm ωb).IsCanonicalDivisor (fp ≫ sZ) d :=
      hKb.of_linearlyEquivalent hωbKb
    have ha : IsDiscrepancy ((f ≫ inv fp) ≫ fp ≫ sZ) d Ka Ba
        (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
          ProperDivisorOver ℂ (f ≫ sZ)).valuation (aX P) :=
      isDiscrepancy_of_eq hs'.symm
        (isDiscrepancy_of_linearlyEquivalent (hdX P) hKa hK'Ka.symm)
    have ha' : IsDiscrepancy (fp ≫ sZ) d (divisorOfForm ωb) (flipTransform f fp Ba)
        (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance :
          ProperDivisorOver ℂ (fp ≫ sZ)).valuation (aY P) :=
      isDiscrepancy_of_linearlyEquivalent (hdY P) hωbcan
        (linearlyEquivalent_of_isCanonicalDivisor_of_isNormalVariety hXbn hωbcan hKbcan)
    have hWp' : IsNormalVariety ℂ (p ≫ (f ≫ inv fp) ≫ fp ≫ sZ) := by rwa [hs']
    have hv := valuation_comap_functionFieldMap (sZ := fp ≫ sZ) hqf' hWp hpb hWq hqb P
    have hcen : ((ProperDivisorOver.mk ⟨W, p, hWp', hpb, P⟩ inferInstance :
        ProperDivisorOver ℂ ((f ≫ inv fp) ≫ fp ≫ sZ)).center : Set Xa) ⊆ E₀.support :=
      image_support_subset_of_two_le_coheight f p P hE₀ hf2 hp1
    have hlt := (IsBirationalContraction.isDiscrepancy_lt_iff_center_subset hXbn hXa' hcon hEx
      rfl hdivτa (hBXc _) hA' hDY (hBYc _) (hasNonemptyCenter_valuation _) hv
      (Bv := ProperDivisorOver.mk ⟨W, p, hWp', hpb, P⟩ inferInstance) rfl ha ha').mpr hcen
    linarith

end Step

/-! ### Intersection numbers with curves on `ℚ`-factorial varieties -/

section RIntersection

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY] [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor has an intersection number with every proper
curve. -/
private theorem exists_isRIntersectionNumber (hY : IsQFactorial sY) (G : RDivisor Y)
    (C : ProperCurve sY) : ∃ x : ℝ, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor Y),
      IsRIntersectionNumber ℂ sY G r L C x := by
  obtain ⟨m, r, L, hL, hG⟩ := isCartierCombination_of_isQFactorial hY G
  choose d hd using fun j => exists_isCartierIntersectionNumber ℂ sY C (L j) (hL j)
  exact ⟨∑ j, r j * d j, m, r, L, hL, d, by simpa only [toRDivisor_eq_mapCoeffs] using hG, hd,
    rfl⟩

/-- The intersection number `G · C` of an `ℝ`-divisor on a `ℚ`-factorial variety with a proper
curve. -/
private noncomputable def rIntersection (hY : IsQFactorial sY) (C : ProperCurve sY)
    (G : RDivisor Y) : ℝ :=
  (exists_isRIntersectionNumber hY G C).choose

/-- `rIntersection` is the value of every presentation. -/
private theorem rIntersection_eq (hY : IsQFactorial sY) {C : ProperCurve sY} {G : RDivisor Y}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor Y} {x : ℝ}
    (h : IsRIntersectionNumber ℂ sY G r L C x) : rIntersection hY C G = x := by
  obtain ⟨m', r', L', h'⟩ := (exists_isRIntersectionNumber hY G C).choose_spec
  exact (IsRIntersectionNumber.eq_and_linear ℂ sY C).1 G r' L' r L _ _ h' h

/-- The empty presentation of the zero divisor has intersection number zero. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sY) :
    IsRIntersectionNumber ℂ sY (0 : RDivisor Y) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor Y) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- The intersection number with a proper curve, as a linear form. -/
private noncomputable def rIntersectionₗ (hY : IsQFactorial sY) (C : ProperCurve sY) :
    RDivisor Y →ₗ[ℝ] ℝ where
  toFun := rIntersection hY C
  map_add' G₁ G₂ := by
    obtain ⟨m₁, r₁, L₁, h₁⟩ := (exists_isRIntersectionNumber hY G₁ C).choose_spec
    obtain ⟨m₂, r₂, L₂, h₂⟩ := (exists_isRIntersectionNumber hY G₂ C).choose_spec
    have h := (IsRIntersectionNumber.eq_and_linear ℂ sY C).2 G₁ G₂ r₁ L₁ r₂ L₂ _ _ 1 1 h₁ h₂
    simp only [one_smul, one_mul] at h
    exact rIntersection_eq hY h
  map_smul' c G := by
    obtain ⟨m₁, r₁, L₁, h₁⟩ := (exists_isRIntersectionNumber hY G C).choose_spec
    have h := (IsRIntersectionNumber.eq_and_linear ℂ sY C).2 G 0 r₁ L₁ _ _ _ _ c 0 h₁
      (isRIntersectionNumber_zero C)
    simp only [smul_zero, add_zero, mul_zero] at h
    rw [RingHom.id_apply, smul_eq_mul]
    exact rIntersection_eq hY h

private theorem rIntersectionₗ_apply (hY : IsQFactorial sY) (C : ProperCurve sY)
    (G : RDivisor Y) : rIntersectionₗ hY C G = rIntersection hY C G :=
  rfl

/-- The intersection number of a Cartier divisor with a proper curve is its degree. -/
private theorem rIntersection_toRDivisor (hY : IsQFactorial sY) (C : ProperCurve sY)
    {w : Divisor Y} (hw : w.IsCartier) :
    rIntersection hY C (Divisor.toRDivisor w) = (w.degreeOn ℂ sY C.ι C.dim_le hw : ℝ) := by
  obtain ⟨d, hd⟩ := exists_isCartierIntersectionNumber ℂ sY C w hw
  rw [rIntersection_eq hY (m := 1) (r := fun _ => 1) (L := fun _ => w)
    ⟨fun _ => hw, fun _ => d, by simp, fun _ => hd, rfl⟩,
    eq_degreeOn_of_isCartierIntersectionNumber hd]
  simp

/-- A divisor linearly equivalent to zero has intersection number zero with every proper
curve. -/
private theorem rIntersection_toRDivisor_of_linearlyEquivalent [CompactSpace Y]
    (hY : IsQFactorial sY) (C : ProperCurve sY) {E : Divisor Y} (hE : E.LinearlyEquivalent 0) :
    rIntersection hY C (Divisor.toRDivisor E) = 0 := by
  have hEc : E.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hE Divisor.isCartier_zero
  rw [rIntersection_toRDivisor hY C hEc,
    Divisor.degreeOn_eq_zero_of_linearlyEquivalent sY C.ι C.dim_le hEc hE, Int.cast_zero]

/-- The degree of a Cartier divisor on a proper curve is the degree of any Weil divisor with
isomorphic divisorial sheaf. -/
private theorem intersectionNumber_ofCartier_eq_degreeOn [CompactSpace Y] (A : Y.CartierDivisor)
    {w : Divisor Y} (hw : w.IsCartier)
    (e : MMP.CartierDivisor.sheaf A ≅ w.divisorialSheaf) (C : ProperCurve sY) :
    (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ A) =
      (w.degreeOn ℂ sY C.ι C.dim_le hw : ℝ) := by
  haveI := hw.isInvertibleModule_divisorialSheaf
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast degreeOn_eq_of_iso ℂ sY C.ι C.dim_le e

/-- Every `ℝ`-divisor on a `ℚ`-factorial variety has an `ℝ`-Cartier divisor with the same
intersection numbers with all proper curves. -/
private theorem exists_kCartierDivisor_intersectionNumber_eq [CompactSpace Y]
    (hY : IsQFactorial sY) (G : RDivisor Y) :
    ∃ N : KCartierDivisor ℝ Y, ∀ C : ProperCurve sY,
      (C.cycle ℝ).intersectionNumber N = rIntersection hY C G := by
  obtain ⟨m, r, L, hL, hG⟩ := isCartierCombination_of_isQFactorial hY G
  have hiso : ∀ j, ∃ A : Y.CartierDivisor,
      Nonempty ((L j).divisorialSheaf ≅ MMP.CartierDivisor.sheaf A) := fun j => by
    haveI := (hL j).isInvertibleModule_divisorialSheaf
    exact MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf _
  choose A hA using hiso
  refine ⟨∑ j, r j • KCartierDivisor.ofCartier ℝ (A j), fun C => ?_⟩
  choose d hd using fun j => exists_isCartierIntersectionNumber ℂ sY C (L j) (hL j)
  have hx : IsRIntersectionNumber ℂ sY G r L C (∑ j, r j * d j) :=
    ⟨hL, d, by simpa only [toRDivisor_eq_mapCoeffs] using hG, hd, rfl⟩
  rw [rIntersection_eq hY hx]
  have hlin : (C.cycle ℝ).intersectionNumber (∑ j, r j • KCartierDivisor.ofCartier ℝ (A j)) =
      ∑ j, r j * (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ (A j)) := by
    simp only [OneCycle.intersectionNumber, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  rw [hlin]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intersectionNumber_ofCartier_eq_degreeOn (A j) (hL j) (hA j).some.symm C,
    ← eq_degreeOn_of_isCartierIntersectionNumber (hd j)]

end RIntersection

/-! ### Weil divisors of `ℝ`-Cartier divisors -/

section WeilOfCartier

open MMP.Intersection

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A point of coheight zero of an integral locally Noetherian scheme lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero (A : X.CartierDivisor) {x : X}
    (hx : Order.coheight x = 0) : x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

variable [TopologicalSpace.NoetherianSpace X]

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    show P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor `[A]` of a Cartier divisor. -/
private noncomputable def weilOfCartier (A : X.CartierDivisor) : Divisor X :=
  (exists_isWeilDivisorOfCartier A).choose

private theorem isWeilDivisorOfCartier_weilOfCartier (A : X.CartierDivisor) :
    IsWeilDivisorOfCartier A (weilOfCartier A) :=
  (exists_isWeilDivisorOfCartier A).choose_spec

/-- The Weil divisor of a Cartier divisor is unique. -/
private theorem weilOfCartier_eq {A : X.CartierDivisor} {w : Divisor X}
    (h : IsWeilDivisorOfCartier A w) : weilOfCartier A = w := by
  refine Finsupp.ext fun P => ?_
  rw [← MMP.Mori.DivisorWithCoeffs.coeff_apply, ← MMP.Mori.DivisorWithCoeffs.coeff_apply]
  exact ((isWeilDivisorOfCartier_weilOfCartier A) P).unique (h P)

/-- The Weil `ℝ`-divisor `∑ cⱼ [Aⱼ]` of an `ℝ`-Cartier divisor `∑ cⱼ Aⱼ`. -/
private noncomputable def weilOfKCartier : KCartierDivisor ℝ X →ₗ[ℝ] RDivisor X :=
  Finsupp.linearCombination ℝ fun A => Divisor.toRDivisor (weilOfCartier A)

private theorem weilOfKCartier_single (A : X.CartierDivisor) (c : ℝ) :
    weilOfKCartier (Finsupp.single A c) = c • Divisor.toRDivisor (weilOfCartier A) :=
  Finsupp.linearCombination_single ℝ c A

/-- The Weil divisor of an effective Cartier divisor is effective. -/
private theorem weilOfCartier_nonneg {A : X.CartierDivisor}
    (hA : MMP.Intersection.IsEffective A) : 0 ≤ weilOfCartier A :=
  MMP.Mori.DivisorWithCoeffs.isEffective_iff_nonneg.mp fun P =>
    ((isWeilDivisorOfCartier_weilOfCartier A) P).nonneg_of_isEffective hA

variable [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- The intersection number of the Weil divisor of an `ℝ`-Cartier divisor with a proper curve is
the intersection number of the `ℝ`-Cartier divisor. -/
private theorem rIntersection_weilOfKCartier (hX : IsQFactorial sX) (C : ProperCurve sX)
    (N : KCartierDivisor ℝ X) :
    rIntersectionₗ hX C (weilOfKCartier N) = (C.cycle ℝ).intersectionNumber N := by
  induction N using Finsupp.induction_linear with
  | zero => simp [OneCycle.intersectionNumber]
  | add N₁ N₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂]
    simp only [OneCycle.intersectionNumber, map_add, LinearMap.add_apply]
  | single A c =>
    have hw := isWeilDivisorOfCartier_weilOfCartier A
    rw [weilOfKCartier_single, map_smul, smul_eq_mul, rIntersectionₗ_apply,
      rIntersection_toRDivisor hX C hw.isCartier,
      ← intersectionNumber_ofCartier_eq_degreeOn A hw.isCartier
        hw.nonempty_sheaf_iso_divisorialSheaf.some C,
      OneCycle.intersectionNumber_ofCartier]
    simp [OneCycle.intersectionNumber, OneCycle.intersectionPairing]

/-- The Weil divisor of an `ℝ`-Cartier divisor of degree zero on the curves contracted by `f` is
numerically trivial over `f`. -/
private theorem isNumericallyTrivialOver_weilOfKCartier (hX : IsQFactorial sX) {S : Scheme.{0}}
    (f : X ⟶ S) {N : KCartierDivisor ℝ X} (hN : N ∈ LinearMap.ker (relativeDegreeMap sX f)) :
    IsNumericallyTrivialOver ℂ sX f (weilOfKCartier N) := by
  unfold IsNumericallyTrivialOver IsNumericallyEquivalentOver
  refine ⟨isCartierCombination_of_isQFactorial hX _, isCartierCombination_of_isQFactorial hX _,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  rw [← rIntersection_eq hX h₁, ← rIntersection_eq hX h₂,
    show rIntersection hX C (0 : RDivisor X) = 0 from map_zero (rIntersectionₗ hX C),
    ← rIntersectionₗ_apply, rIntersection_weilOfKCartier hX C N]
  have h0 := congr_fun (LinearMap.mem_ker.mp hN) ⟨C, hC⟩
  simpa [relativeDegreeMap, OneCycle.intersectionNumber] using h0

end WeilOfCartier

/-! ### Transforms of integral divisors -/

section TransformInt

variable {X Y : Scheme.{0}}

/-- The birational transform commutes with a change of coefficients along an additive map. -/
private theorem transformDivisor_mapCoeffsAddMonoidHom {R S : Type*} [AddCommGroup R]
    [AddCommGroup S] (f : R →+ S) (φ : X.RationalMap Y) (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    have h1 : ∀ (Z : Scheme.{0}) (Q : MMP.Mori.PrimeDivisor Z),
        DivisorWithCoeffs.mapCoeffsAddMonoidHom f (Finsupp.single Q r) =
          Finsupp.single Q (f r) := fun Z Q => by
      rw [DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply]
      exact Finsupp.mapRange_single
    rw [h1, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
    · exact (map_zero (DivisorWithCoeffs.mapCoeffsAddMonoidHom f)).symm
    · exact (h1 Y Q).symm

/-- The birational transform commutes with regarding a divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor (φ : X.RationalMap Y) (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ D) :=
  transformDivisor_mapCoeffsAddMonoidHom _ φ D

/-- The birational transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg (φ : X.RationalMap Y) {D : Divisor X} (hD : 0 ≤ D) :
    0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  rw [← D.sum_single, Finsupp.sum, map_sum]
  refine Finset.sum_nonneg fun P _ => ?_
  rw [MMP.Mori.RationalMap.transformDivisor_single]
  rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
  · exact le_rfl
  · exact Finsupp.single_nonneg.mpr (Finsupp.le_def.mp hD P)

end TransformInt

/-! ### Fibre-type contractions of negative extremal rays -/

section FibreType

/-- A morphism of projective `k`-varieties is projective. -/
private theorem isProjective_of_comp_eq {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) : IsProjective f := by
  have : IsSeparated sY := hY.toIsVariety.toIsSeparated
  let γ : X ⟶ Limits.pullback sX sY := Limits.pullback.lift (𝟙 X) f (by simp [hf])
  have : IsClosedImmersion γ :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) γ
      (Limits.pullback.fst sX sY) inferInstance
      (by simp only [γ, Limits.pullback.lift_fst]; infer_instance)
  have hγ : γ ≫ Limits.pullback.snd sX sY = f := Limits.pullback.lift_snd _ _ _
  rw [← hγ]
  exact ((MMP.isProjectiveMorphism_of_isClosedImmersion γ).comp
    (hX.isProjective.baseChange sY)).isProjective

/-- A contraction is dominant: an open set missing its image has no sections upstairs. -/
private theorem isDominant_of_isContraction {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}
    (hf : MMP.Flips.IsContraction k sX sY f) : IsDominant f := by
  have hfX := hf.isIso_app
  refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  let V' : X.Opens := ⟨V, hV⟩
  have hbot : f ⁻¹ᵁ V' = ⊥ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
  have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(X, V') :=
    (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
  obtain ⟨x, hx⟩ := hVne
  have h10 := congrArg (X.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(X, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

/-- The generic point of an integral scheme lies on no prime divisor. -/
private theorem genericPoint_notMem_supp {Y : Scheme.{0}} [IsIntegral Y] (G : Divisor Y) :
    genericPoint Y ∉ (MMP.Mori.DivisorWithCoeffs.supp G : Set Y) := by
  intro h
  obtain ⟨E, -, hE⟩ := MMP.Mori.DivisorWithCoeffs.mem_supp_iff.mp h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have h1 : E.genericPoint ⤳ genericPoint Y := specializes_iff_mem_closure.mpr hE
  have h2 : genericPoint Y ⤳ E.genericPoint := (genericPoint_spec Y).specializes (Set.mem_univ _)
  have h3 : E.genericPoint = genericPoint Y := (h1.antisymm h2).eq
  have hmax : IsMax (genericPoint Y) := fun y _ =>
    (show genericPoint Y ⤳ y from (genericPoint_spec Y).specializes (Set.mem_univ y))
  have h0 : Order.coheight (genericPoint Y) = 0 := Order.coheight_eq_zero.mpr hmax
  have h4 := E.coheight_genericPoint
  rw [h3, h0] at h4
  exact zero_ne_one h4

variable {Y V S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} [QuasiCompact sY]

/-- **Effective divisors are nonnegative on a negative extremal ray of fibre type.** Let
`f : Y ⟶ V` be a contraction of fibre type of a ray `R` of `NE̅(Y/S)` on which an `ℝ`-divisor
`L` is negative. For every curve `C₀` contracted by `f` and every effective divisor `G`,
`G · C₀ ≥ 0`: some curve `Γ` contracted by `f` is not contained in `Supp G`, so `G · Γ ≥ 0`, and
the classes of `Γ` and `C₀` are positive multiples of the generator of `R`. -/
private theorem rIntersection_nonneg_of_isContractedBy (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hYQ : IsQFactorial sY) (hV : MMP.Mori.IsVariety ℂ sV) {fn : Y ⟶ V} [IsProper fn]
    [IsDominant fn] (hfV : fn ≫ sV = sY) (hdimV : topologicalKrullDim V < topologicalKrullDim Y)
    {πY : Y ⟶ S} {hn : V ⟶ S} (hfS : fn ≫ hn = πY)
    {Rn : Set (RelativeNumericalCurveClasses sY πY)}
    (hRn : ∃ v, v ≠ 0 ∧ Rn = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
    (hface : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy πY),
      C.IsContractedBy fn ↔ C.relativeClass πY hC ∈ Rn)
    {L : RDivisor Y}
    (hneg : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy πY), C.relativeClass πY hC ∈ Rn →
      ∀ (m : ℕ) (r : Fin m → ℝ) (Ls : Fin m → Divisor Y) (x : ℝ),
        IsRIntersectionNumber ℂ sY L r Ls C x → x < 0)
    {C₀ : ProperCurve sY} (hC₀ : C₀.IsContractedBy fn) {G : Divisor Y} (hG : 0 ≤ G) :
    0 ≤ rIntersection hYQ C₀ (Divisor.toRDivisor G) := by
  have hYv := ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hY).1
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism _ ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hY).2
  have hcon : ∀ C : ProperCurve sY, C.IsContractedBy fn → C.IsContractedBy πY := fun C hC x hx => by
    rw [← hfS, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  obtain ⟨mG, hm, hmG⟩ := hYQ.2 G
  set G' : Divisor Y := (mG : ℤ) • G with hG'
  have hG'0 : 0 ≤ G' := by
    rw [Finsupp.le_def] at hG ⊢
    intro P
    simp only [hG', Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
    exact mul_nonneg (by positivity) (by simpa using hG P)
  -- a contracted curve not contained in `Supp G'`
  obtain ⟨Γ, hΓ, hΓB⟩ := MMP.Fourfold.exists_properCurve_isContractedBy_of_lt hYv hV fn
    hfV hdimV (MMP.Mori.DivisorWithCoeffs.isClosed_supp G') (genericPoint_notMem_supp G')
  obtain ⟨c, hc⟩ := MMP.Threefold.Mori.exists_ι_eq_point Γ.point
  have hdeg := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sY Γ.ι Γ.dim_le G' hmG hG'0
    ⟨c, by rw [hc]; exact hΓB⟩).1
  have hΓpos : 0 ≤ rIntersection hYQ Γ (Divisor.toRDivisor G') := by
    rw [rIntersection_toRDivisor hYQ Γ hmG]
    exact_mod_cast hdeg
  -- the classes of `Γ` and `C₀` lie on the ray
  obtain ⟨v, -, hRv⟩ := hRn
  have hΓR := (hface Γ (hcon Γ hΓ)).mp hΓ
  have hC₀R := (hface C₀ (hcon C₀ hC₀)).mp hC₀
  rw [hRv] at hΓR hC₀R
  obtain ⟨c₁, hc₁, hc₁v⟩ := hΓR
  obtain ⟨c₀, hc₀, hc₀v⟩ := hC₀R
  obtain ⟨N, hN⟩ := exists_kCartierDivisor_intersectionNumber_eq hYQ (Divisor.toRDivisor G')
  have hI : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy πY),
      RelativeNumericalCurveClasses.intersectionNumber N (C.relativeClass πY hC) =
        rIntersection hYQ C (Divisor.toRDivisor G') := fun C hC => by
    rw [← hN C]
    rfl
  -- the class of `Γ` is not zero, since `L` is negative on it
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    obtain ⟨NL, hNL⟩ := exists_kCartierDivisor_intersectionNumber_eq hYQ L
    obtain ⟨mL, rL, LL, hLL⟩ := (exists_isRIntersectionNumber hYQ L Γ).choose_spec
    have hlt := hneg Γ (hcon Γ hΓ) ((hface Γ (hcon Γ hΓ)).mp hΓ) mL rL LL _ hLL
    have h0 : RelativeNumericalCurveClasses.intersectionNumber NL (Γ.relativeClass πY (hcon Γ hΓ))
        = 0 := by rw [← hc₁v, zero_smul, map_zero]
    have h1 : RelativeNumericalCurveClasses.intersectionNumber NL
        (Γ.relativeClass πY (hcon Γ hΓ)) = rIntersection hYQ Γ L := by
      rw [← hNL Γ]
      rfl
    rw [h1] at h0
    change (exists_isRIntersectionNumber hYQ L Γ).choose < 0 at hlt
    change (exists_isRIntersectionNumber hYQ L Γ).choose = 0 at h0
    linarith
  have hvpos : 0 ≤ RelativeNumericalCurveClasses.intersectionNumber N v := by
    have h := hI Γ (hcon Γ hΓ)
    rw [← hc₁v, map_smul, smul_eq_mul] at h
    rw [← h] at hΓpos
    exact (mul_nonneg_iff_of_pos_left (lt_of_le_of_ne hc₁ (Ne.symm hc₁0))).mp hΓpos
  have hC₀pos : 0 ≤ rIntersection hYQ C₀ (Divisor.toRDivisor G') := by
    rw [← hI C₀ (hcon C₀ hC₀), ← hc₀v, map_smul, smul_eq_mul]
    exact mul_nonneg hc₀ hvpos
  have hsm : Divisor.toRDivisor G' = (mG : ℝ) • Divisor.toRDivisor G := by
    rw [hG', map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    simp
  rw [hsm, ← rIntersectionₗ_apply, map_smul, smul_eq_mul, rIntersectionₗ_apply] at hC₀pos
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm)).mp hC₀pos

/-- **A pseudo-effective adjoint cannot end at a negative fibre-type contraction.** Let
`φ : X ⤏ Y` be a birational contraction over `S` of normal `ℚ`-factorial projective varieties,
`D` an `ℝ`-Cartier divisor on `X` pseudo-effective over `S`, and `f : Y ⟶ V` a fibre-type
contraction over `S` of a ray `R` of `NE̅(Y/S)` on which an `ℝ`-divisor `L` numerically equal to
`φ_* D` over `S` is negative. This is impossible: for a curve `C₀` contracted by `f`, the linear
form `D' ↦ φ_*[D'] · C₀` is defined on `N¹(X/S)`, continuous since `N¹(X/S)` is
finite-dimensional, nonnegative on the effective cone, but negative at `D`. -/
private theorem false_of_isRelativelyPseudoEffective {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {g : X ⟶ S} {πY : Y ⟶ S}
    (hg : g ≫ sS = sX) (hπY : πY ≫ sS = sY) {φ : X.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hφS : MMP.Flips.RationalMap.IsOver g πY φ)
    (hφE : ∀ F : MMP.Mori.PrimeDivisor Y, ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F)
    (hV : MMP.Mori.IsVariety ℂ sV) {fn : Y ⟶ V} [IsProper fn] [IsDominant fn]
    (hfV : fn ≫ sV = sY) (hdimV : topologicalKrullDim V < topologicalKrullDim Y)
    {hn : V ⟶ S} (hfS : fn ≫ hn = πY) {Rn : Set (RelativeNumericalCurveClasses sY πY)}
    (hRn : ∃ v, v ≠ 0 ∧ Rn = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
    (hface : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy πY),
      C.IsContractedBy fn ↔ C.relativeClass πY hC ∈ Rn)
    {L : RDivisor Y}
    (hneg : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy πY), C.relativeClass πY hC ∈ Rn →
      ∀ (m : ℕ) (r : Fin m → ℝ) (Ls : Fin m → Divisor Y) (x : ℝ),
        IsRIntersectionNumber ℂ sY L r Ls C x → x < 0)
    {m : ℕ} {r : Fin m → ℝ} {A : Fin m → X.CartierDivisor} {w : Fin m → Divisor X}
    (hw : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (A i) (w i))
    (hD : KCartierDivisor.IsRelativelyPseudoEffective sX g (∑ i, Finsupp.single (A i) (r i)))
    (hL : ∀ C : ProperCurve sY, C.IsContractedBy πY → rIntersection hYQ C L =
      rIntersection hYQ C (MMP.Mori.RationalMap.transformDivisor φ
        (∑ i, r i • Divisor.toRDivisor (w i)))) : False := by
  haveI : IsNoetherian X := ⟨⟩
  have hYv := ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hY).1
  haveI : IsProper sY :=
    isProper_of_isProjectiveMorphism _ ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hY).2
  have hcon : ∀ C : ProperCurve sY, C.IsContractedBy fn → C.IsContractedBy πY := fun C hC x hx => by
    rw [← hfS, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  -- a curve contracted by `f`
  obtain ⟨C₀, hC₀, -⟩ := MMP.Fourfold.exists_properCurve_isContractedBy_of_lt hYv hV fn
    hfV hdimV (B := ∅) isClosed_empty (Set.notMem_empty _)
  have hC₀S := hcon C₀ hC₀
  -- the linear form `D' ↦ φ_*[D'] · C₀`
  let lam : KCartierDivisor ℝ X →ₗ[ℝ] ℝ := (rIntersectionₗ hYQ C₀).comp
    ((MMP.Mori.RationalMap.transformDivisorₗ ℝ φ).comp weilOfKCartier)
  have hlam : ∀ N, lam N = rIntersection hYQ C₀
      (MMP.Mori.RationalMap.transformDivisor φ (weilOfKCartier N)) := fun N => by
    simp only [lam, LinearMap.comp_apply, MMP.Mori.RationalMap.transformDivisorₗ_apply,
      rIntersectionₗ_apply]
  have hker : LinearMap.ker (relativeDegreeMap sX g) ≤ LinearMap.ker lam := by
    intro N hN
    have h1 := isNumericallyTrivialOver_weilOfKCartier hXQ g hN
    have h2 := (MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_pullback_eq sX sY sS
      hXQ hX hYQ hY hS g πY hg hπY hφ hφS hφE h1).1
    unfold IsNumericallyTrivialOver IsNumericallyEquivalentOver at h2
    obtain ⟨-, -, h2⟩ := h2
    obtain ⟨m₁, r₁, L₁, h₁⟩ := (exists_isRIntersectionNumber hYQ
      (MMP.Mori.RationalMap.transformDivisor φ (weilOfKCartier N)) C₀).choose_spec
    have := h2 C₀ hC₀S m₁ r₁ L₁ _ 0 Fin.elim0 Fin.elim0 0 h₁ (isRIntersectionNumber_zero C₀)
    rw [LinearMap.mem_ker, hlam]
    exact this
  let lamBar : MMP.Fourfold.RelativeNumericalDivisorClasses sX g →ₗ[ℝ] ℝ :=
    (LinearMap.ker (relativeDegreeMap sX g)).liftQ lam hker
  -- `lamBar` is continuous, since `N¹(X/S)` is finite-dimensional
  have hgp : IsProjective g := isProjective_of_comp_eq hX hS hg
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsVariety ℂ sS := ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hS).1
  haveI := MMP.Fourfold.RelativeNumericalDivisorClasses.finiteDimensional_of_isProjectiveVariety
    sX sS g hgp hg
  let ι := (LinearMap.ker (relativeDegreeMap sX g)).liftQ (relativeDegreeMap sX g) le_rfl
  haveI : IsTopologicalAddGroup (MMP.Fourfold.RelativeNumericalDivisorClasses sX g) :=
    topologicalAddGroup_induced ι
  haveI : ContinuousSMul ℝ (MMP.Fourfold.RelativeNumericalDivisorClasses sX g) :=
    continuousSMul_induced ι
  have hinj : Function.Injective ι := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  haveI : T2Space (MMP.Fourfold.RelativeNumericalDivisorClasses sX g) :=
    Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, hinj⟩
  have hcont : Continuous lamBar := LinearMap.continuous_of_finiteDimensional lamBar
  -- `lamBar` is nonnegative on the effective cone
  have hgen : ∀ E : X.CartierDivisor, MMP.Intersection.IsEffective E →
      0 ≤ lam (KCartierDivisor.ofCartier ℝ E) := fun E hE => by
    rw [hlam, KCartierDivisor.ofCartier, weilOfKCartier_single, one_smul,
      transformDivisor_toRDivisor]
    exact rIntersection_nonneg_of_isContractedBy hY hYQ hV hfV hdimV hfS hRn hface hneg hC₀
      (transformDivisor_nonneg φ (weilOfCartier_nonneg hE))
  have hcone : (MMP.Fourfold.relativeEffectiveCone sX g :
      Set (MMP.Fourfold.RelativeNumericalDivisorClasses sX g)) ⊆
      {x | 0 ≤ lamBar x} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨E, hE, rfl⟩ := hx
      exact hgen E hE
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      have e : c • x = (c : ℝ) • x := rfl
      rw [e, map_smul, smul_eq_mul]
      exact mul_nonneg c.2 hx
  have hclosed :
      IsClosed {x : MMP.Fourfold.RelativeNumericalDivisorClasses sX g | 0 ≤ lamBar x} :=
    isClosed_le continuous_const hcont
  have hDpos := closure_minimal hcone hclosed hD
  -- but `lamBar` is negative at `D`
  have hDw : weilOfKCartier (∑ i, Finsupp.single (A i) (r i)) =
      ∑ i, r i • Divisor.toRDivisor (w i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weilOfKCartier_single, weilOfCartier_eq (hw i)]
  change 0 ≤ lam (∑ i, Finsupp.single (A i) (r i)) at hDpos
  rw [hlam, hDw, ← hL C₀ hC₀S] at hDpos
  obtain ⟨mL, rL, LL, hLL⟩ := (exists_isRIntersectionNumber hYQ L C₀).choose_spec
  have hlt := hneg C₀ hC₀S ((hface C₀ hC₀S).mp hC₀) mL rL LL _ hLL
  change 0 ≤ (exists_isRIntersectionNumber hYQ L C₀).choose at hDpos
  linarith

end FibreType

private theorem solution : ∀ {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B)
    (hpsef : ∃ (m : ℕ) (r : Fin m → ℝ) (A : Fin m → X.CartierDivisor) (w : Fin m → Divisor X),
      (∀ i, MMP.Intersection.IsWeilDivisorOfCartier (A i) (w i)) ∧
      logCanonicalDivisor K B = ∑ i, r i • Divisor.toRDivisor (w i) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX g (∑ i, Finsupp.single (A i) (r i))),
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ S) (φ : X.RationalMap Y),
      IsNefWeakModel sX sY sS g πY K B φ ∧ IsQFactorial sY ∧
      IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B) ∧
      ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
        (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W),
        MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sX = sW ∧ q ≫ sY = sW ∧
          IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
          IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
          h.compHom q = φ ∧
          ∃ GX GY : RDivisor W,
            IsRCartierPullback p (logCanonicalDivisor K B) GX ∧
            IsRCartierPullback q
              (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                (MMP.Mori.RationalMap.transformDivisor φ B)) GY ∧
            (∀ P, 0 ≤ (GX - GY).coeff P) ∧
            (∀ P, (GX - GY).coeff P ≠ 0 → IsExceptionalPrimeDivisor sY q P) ∧
            ∀ P : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.IsExceptional φ P →
              ∀ P' : MMP.Mori.PrimeDivisor W,
                MMP.Mori.RationalMap.transformPrimeDivisor p.toRationalMap P' = some P →
                0 < (GX - GY).coeff P' := by
  intro X S _ _ _ _ sX sS g K B hX hS hg hXQ hdim hK hB0 hB hpsef
  obtain ⟨n, Yi, sYi, hYint, hYcpt, hYln, hYnorm, πY, KY, BY, R, Zi, sZi, f, h, fp, hmod, hstep,
    hend⟩ := IsRealKltPair.exists_program_isRelativelyNef_or_isFibreType hX hS hg hXQ hdim hK hB0 hB
  haveI := hYint
  haveI := hYcpt
  haveI := hYln
  haveI := hYnorm
  have hlft : ∀ i ≤ n, LocallyOfFiniteType (modelStr sX sYi i) := fun i hi =>
    ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hmod i hi).1).1.toLocallyOfFiniteType
  have hcan :
      ∀ i ≤ n, ∃ m, Divisor.IsCanonicalDivisor (modelStr sX sYi i) m (divisorSeq K KY i) := by
    intro i hi
    cases i with
    | zero => exact hK
    | succ j =>
      obtain ⟨-, -, -, -, -, hcase⟩ := hstep j (by omega)
      rcases hcase with ⟨-, -, hKY, -⟩ | hfl
      · exact hKY
      · exact hfl.isCanonicalDivisor_flip
  -- the steps of the program
  have hStep : ∀ i < n, IsStep (modelStr sX sYi i) (sYi i) (sZi i) (f i) (fp i)
      (divisorSeq K KY i) (divisorSeq B BY i) (KY i) (BY i) := by
    intro i hi
    obtain ⟨-, -, hface, hneg, hfph, hcase⟩ := hstep i hi
    have hmi := hmod i hi.le
    have hmi1 := hmod (i + 1) hi
    have hc := hneg.isContraction
    haveI : IsProper (f i) := hc.isProper
    haveI : QuasiCompact (sYi i) :=
      ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hmi1.1).1.toQuasiCompact
    rcases hcase with ⟨⟨hfb, E, hE⟩, hiso, hKY, hBY⟩ | hfl
    · haveI := hiso
      haveI : IsIntegral (Zi i) := hneg.isNormalVariety_target.1.toIsIntegral
      haveI : IsDominant (f i) := hfb.isDominant
      have hhS : h i ≫ sS = sZi i := by
        refine ext_of_isDominant_of_isSeparated (Limits.terminal.from _)
          (Limits.terminal.hom_ext _ _) (f i) ?_
        rw [← Category.assoc, hface.comp_eq, hmi.2.2.2.1, hc.comp_eq]
      exact
        { isNormalVariety_target := hneg.isNormalVariety_target
          isContraction := hc
          isProper := hc.isProper
          isProper_flip := inferInstance
          comp_eq := hc.comp_eq
          comp_eq_flip := by rw [← hhS, ← Category.assoc, hfph]; exact hmi1.2.2.2.1
          isProjectiveVariety_source := hmi.1
          isProjectiveVariety_flip := hmi1.1
          isQFactorial_source := hmi.2.1
          isQFactorial_flip := hmi1.2.1
          isBirationalMorphism := hfb
          isBirationalMorphism_flip := isBirationalMorphism_of_isIso _
          coheight_flip := fun y _ => coheight_map_of_isIso _ y
          isCanonicalDivisor_source := hcan i hi.le
          isCanonicalDivisor_flip := hKY
          eq_flipTransform := hBY
          isRelativelyAntiAmple := hneg.isRelativelyAntiAmple
          isRelativelyNef_flip := isRelativelyNef_of_injective _
            (fp i).isOpenEmbedding.injective (isCartierCombination_of_isQFactorial hmi1.2.1 _)
          divisorial_or_small := Or.inl ⟨hiso, E, hE⟩ }
    · exact
        { isNormalVariety_target := hneg.isNormalVariety_target
          isContraction := hc
          isProper := hc.isProper
          isProper_flip := isProper_of_isProjectiveMorphism _ hfl.isProjectiveMorphism_flip
          comp_eq := hc.comp_eq
          comp_eq_flip := hfl.isSmall_flip.comp_eq
          isProjectiveVariety_source := hmi.1
          isProjectiveVariety_flip := hmi1.1
          isQFactorial_source := hmi.2.1
          isQFactorial_flip := hmi1.2.1
          isBirationalMorphism := hfl.isBirationalMorphism
          isBirationalMorphism_flip := hfl.isBirationalMorphism_flip
          coheight_flip := coheight_map_of_isSmall hfl.isSmall_flip
          isCanonicalDivisor_source := hcan i hi.le
          isCanonicalDivisor_flip := hfl.isCanonicalDivisor_flip
          eq_flipTransform := hfl.eq_flipTransform
          isRelativelyAntiAmple := hneg.isRelativelyAntiAmple
          isRelativelyNef_flip := isRelativelyNef_of_isRelativelyAmple _ hfl.isRelativelyAmple_flip
          divisorial_or_small := Or.inr (coheight_map_of_isSmall hfl.isSmall) }
  -- a smooth projective model dominating every model of the program
  obtain ⟨W, _, _, _, _, sW, p, hWv, hWsm, hWproj, hp, hpq⟩ : ∃ (W : Scheme.{0})
      (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W) (_ : CompactSpace W)
      (sW : W ⟶ Spec (.of ℂ)) (p : ∀ i, i ≤ n → (W ⟶ modelSeq X Yi i)),
      MMP.Mori.IsVariety ℂ sW ∧ IsSmoothScheme sW ∧ MMP.Mori.IsProjectiveVariety ℂ sW ∧
      (∀ i (hi : i ≤ n), p i hi ≫ modelStr sX sYi i = sW ∧ IsProjectiveMorphism (p i hi) ∧
        IsBirationalMorphism (p i hi)) ∧
      ∀ i (hi : i < n), p i hi.le ≫ f i = p (i + 1) hi ≫ fp i :=
    exists_tower (modelStr sX sYi) sZi f fp n (fun i hi => (hmod i hi).1)
      (fun i hi => (hStep i hi).isNormalVariety_target)
      (fun i hi => ⟨(hStep i hi).isProper, (hStep i hi).isBirationalMorphism, (hStep i hi).comp_eq⟩)
      (fun i hi => ⟨(hStep i hi).isProper_flip, (hStep i hi).isBirationalMorphism_flip,
        (hStep i hi).comp_eq_flip⟩) n le_rfl
  -- the compatible canonical divisors
  let K' : ∀ i, Divisor (modelSeq X Yi i) := fun i =>
    Nat.rec (motive := fun i => Divisor (modelSeq X Yi i)) K
      (fun i D => flipTransform (f i) (fp i) D) i
  have hτ : ∀ i (hi : i ≤ n), haveI := hlft i hi
      ∃ τ : RationalPluriForms (modelStr sX sYi i) 3 1, τ ≠ 0 ∧ divisorOfForm τ = K' i := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨d, hd⟩ := hK
      have hd3 : d = 3 := by
        have := hd.topologicalKrullDim_eq
        rw [hdim] at this
        exact_mod_cast this.symm
      subst hd3
      have hXn : IsNormalVariety ℂ sX :=
        ⟨((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hX).1, inferInstance⟩
      haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
      obtain ⟨τ, hτ0, hτ⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hd
      exact ⟨τ, hτ0, Finsupp.ext hτ⟩
    | succ j ih =>
      intro hi
      haveI := hlft j (by omega)
      haveI : LocallyOfFiniteType (sYi j) := hlft (j + 1) hi
      obtain ⟨τ, hτ0, hτK⟩ := ih (by omega)
      exact (hStep j (by omega)).exists_divisorOfForm_eq (hmod j (by omega)).2.2.1 hτ0 hτK
  have hGex : ∀ i, ∃ G : RDivisor W, ∀ hi : i ≤ n,
        IsRCartierPullback (p i hi) (logCanonicalDivisor (K' i) (divisorSeq B BY i)) G := by
    intro i
    by_cases hi : i ≤ n
    · haveI : IsDominant (p i hi) := (hp i hi).2.2.isDominant
      obtain ⟨G, hG, -⟩ := existsUnique_isRCartierPullback (p i hi)
        (isCartierCombination_of_isQFactorial (hmod i hi).2.1
          (logCanonicalDivisor (K' i) (divisorSeq B BY i)))
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose G hG using hGex
  -- the comparison along each step
  have hcoeff : ∀ i (hi : i < n), ∀ P : MMP.Mori.PrimeDivisor W, 0 ≤ (G i - G (i + 1)).coeff P ∧
      (Order.coheight (p (i + 1) hi P.genericPoint) ≤ 1 → (G i - G (i + 1)).coeff P = 0) ∧
      (Order.coheight (p i hi.le P.genericPoint) ≤ 1 →
        ¬ Order.coheight (p (i + 1) hi P.genericPoint) ≤ 1 → 0 < (G i - G (i + 1)).coeff P) := by
    intro i hi P
    haveI := hlft i hi.le
    haveI : LocallyOfFiniteType (sYi i) := hlft (i + 1) hi
    obtain ⟨τ, hτ0, hτK⟩ := hτ i hi.le
    haveI : IsProper (p i hi.le) := isProper_of_isProjectiveMorphism _ (hp i hi.le).2.1
    haveI : IsProper (show W ⟶ Yi i from p (i + 1) hi) :=
      isProper_of_isProjectiveMorphism _ (hp (i + 1) hi).2.1
    exact (hStep i hi).coeff_sub (hmod i hi.le).2.2.1 hτ0 hτK ⟨hWv, inferInstance⟩ (p i hi.le)
      (p (i + 1) hi)
      (hp i hi.le).2.2 (hp (i + 1) hi).2.2 (hp i hi.le).1 (hp (i + 1) hi).1 (hpq i hi)
      (hG i hi.le) (hG (i + 1) hi) P
  have hcoh : ∀ i (hi : i < n), ∀ x : W, Order.coheight (p (i + 1) hi x) ≤ 1 →
      Order.coheight (p i hi.le x) ≤ 1 :=
    fun i hi x hx => ((hStep i hi).coeff_flipTransform ⟨hWv, inferInstance⟩ (p i hi.le)
      (p (i + 1) hi) (hp i hi.le).1 (hp (i + 1) hi).1 (hpq i hi) x hx).1
  have hcohn : ∀ x : W, Order.coheight (p n le_rfl x) ≤ 1 →
      ∀ i (hi : i ≤ n), Order.coheight (p i hi x) ≤ 1 := by
    intro x hx i hi
    have key : ∀ j i (hi : i ≤ n), i + j = n → Order.coheight (p i hi x) ≤ 1 := by
      intro j
      induction j with
      | zero => intro i hi hij; rw [Nat.add_zero] at hij; subst hij; exact hx
      | succ j ih => intro i hi hij; exact hcoh i (by omega) x (ih (i + 1) (by omega) (by omega))
    exact key (n - i) i hi (by omega)
  have hp0 := hp 0 (Nat.zero_le n)
  have hpn := hp n le_rfl
  haveI : IsProper (p 0 (Nat.zero_le n)) := isProper_of_isProjectiveMorphism _ hp0.2.1
  haveI : IsProper (p n le_rfl) := isProper_of_isProjectiveMorphism _ hpn.2.1
  obtain ⟨h₀, hh₀⟩ := RationalMap.IsBirational.exists_isInverse hp0.2.2
  set φ : X.RationalMap (modelSeq X Yi n) := h₀.compHom (p n le_rfl) with hφ
  have hXv : IsNormalVariety ℂ sX :=
    ⟨((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hX).1, inferInstance⟩
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI := isSeparated_toTerminal sX
  have hXnv : IsNormalVariety ℂ (modelStr sX sYi n) :=
    ⟨((MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hmod n le_rfl).1).1, inferInstance⟩
  haveI : IsSeparated (modelStr sX sYi n) := hXnv.1.toIsSeparated
  haveI := isSeparated_toTerminal (modelStr sX sYi n)
  have hWnv : IsNormalVariety ℂ sW := ⟨hWv, inferInstance⟩
  -- primes of `W` over primes of the models
  have hprime : ∀ i (hi : i ≤ n) (P : MMP.Mori.PrimeDivisor W),
      Order.coheight (p i hi P.genericPoint) ≤ 1 →
      ∃ G : MMP.Mori.PrimeDivisor (modelSeq X Yi i), p i hi P.genericPoint = G.genericPoint := by
    intro i hi P hP
    have hXi := (MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hmod i hi).1
    haveI := hXi.1
    haveI := hWv
    have hdim := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
      (modelStr sX sYi i) sW (hp i hi).2.2).symm
    have hge := coheight_le_coheight_map (modelStr sX sYi i) sW hXi.1 hWv (p i hi) (hp i hi).1
      hdim P.genericPoint
    rw [P.coheight_genericPoint] at hge
    have h1 : Order.coheight (p i hi P.genericPoint) = 1 := le_antisymm hP hge
    exact ⟨_, (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1).symm⟩
  have hover : ∀ i (hi : i ≤ n) (G : MMP.Mori.PrimeDivisor (modelSeq X Yi i)),
      ∃ P : MMP.Mori.PrimeDivisor W, p i hi P.genericPoint = G.genericPoint := by
    intro i hi G
    have hXi : IsNormalVariety ℂ (modelStr sX sYi i) :=
      ⟨((MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hmod i hi).1).1, inferInstance⟩
    haveI : IsProper (p i hi) := isProper_of_isProjectiveMorphism _ (hp i hi).2.1
    have hWi : IsNormalVariety ℂ (p i hi ≫ modelStr sX sYi i) := by rwa [(hp i hi).1]
    obtain ⟨E, hE, -⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0}
      hXi hWi (hp i hi).2.2 G
    exact ⟨E, hE⟩
  -- the transform along `φ`, read on `W`
  haveI : IsSeparated (modelSeq X Yi 0 ↘ ⊤_ Scheme) :=
    (isSeparated_toTerminal sX : IsSeparated (X ↘ ⊤_ Scheme))
  have hφT : ∀ (G : MMP.Mori.PrimeDivisor X) (P : MMP.Mori.PrimeDivisor W),
      p 0 (Nat.zero_le n) P.genericPoint = G.genericPoint →
      ∀ F, RationalMap.transformPrimeDivisor φ G = some F ↔
        p n le_rfl P.genericPoint = F.genericPoint := fun G P hPG F =>
    transformPrimeDivisor_compHom_eq_some_iff (p 0 (Nat.zero_le n)) hp0.2.2 hh₀ (p n le_rfl)
      hPG F
  -- the birational transform along `φ` is the transform along the program
  have hφD : ∀ {R : Type} [AddCommMonoid R] (Dseq : ∀ i, DivisorWithCoeffs R (modelSeq X Yi i)),
      (∀ i < n, Dseq (i + 1) = flipTransform (f i) (fp i) (Dseq i)) →
      RationalMap.transformDivisor φ (Dseq 0) = Dseq n := by
    intro R _ Dseq hD
    refine Finsupp.ext fun F => ?_
    obtain ⟨P, hP⟩ := hover n le_rfl F
    have hc := hcohn P.genericPoint (by rw [hP, F.coheight_genericPoint])
    obtain ⟨G₀, hG₀⟩ := hprime 0 (Nat.zero_le n) P (hc 0 (Nat.zero_le n))
    have hchain : ∀ i (hi : i ≤ n), ∃ G : MMP.Mori.PrimeDivisor (modelSeq X Yi i),
        p i hi P.genericPoint = G.genericPoint ∧ (Dseq i).coeff G = (Dseq 0).coeff G₀ := by
      intro i
      induction i with
      | zero => exact fun _ => ⟨G₀, hG₀, rfl⟩
      | succ j ih =>
        intro hj
        obtain ⟨G, hG, hGc⟩ := ih (Nat.le_of_succ_le hj)
        obtain ⟨G', hG'⟩ := hprime (j + 1) hj P (hc (j + 1) hj)
        refine ⟨G', hG', ?_⟩
        rw [hD j hj, ← hGc]
        exact ((hStep j hj).coeff_flipTransform hWnv (p j (Nat.le_of_succ_le hj)) (p (j + 1) hj)
          (hp j (Nat.le_of_succ_le hj)).1 (hp (j + 1) hj).1 (hpq j hj) P.genericPoint
          (hc (j + 1) hj)).2 G G' hG hG' (Dseq j)
    obtain ⟨Gn, hGn, hGnc⟩ := hchain n le_rfl
    have hGnF : Gn = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hGn.symm.trans hP)
    subst hGnF
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply (Dseq n), hGnc]
    refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq ((hφT G₀ P hG₀ Gn).mpr hP)
      (fun G' hG' => ?_) (Dseq 0)
    obtain ⟨P', hP'⟩ := hover 0 (Nat.zero_le n) G'
    have h1 := (hφT G' P' hP' Gn).mp hG'
    have hPP : P'.genericPoint = P.genericPoint :=
      eq_of_apply_eq_of_coheight_le_one (p n le_rfl) hpn.2.2 (h1.trans hP.symm)
        (by rw [h1, Gn.coheight_genericPoint])
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (hP'.symm.trans ((congrArg _ hPP).trans hG₀))
  have hφK : RationalMap.transformDivisor φ K = K' n := hφD K' fun _ _ => rfl
  have hφB : RationalMap.transformDivisor φ B = divisorSeq B BY n :=
    hφD (divisorSeq B BY) fun i hi => (hStep i hi).eq_flipTransform
  have hφexc : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor W),
      RationalMap.IsExceptional φ P →
      RationalMap.transformPrimeDivisor (p 0 (Nat.zero_le n)).toRationalMap P' = some P →
      Order.coheight (p 0 (Nat.zero_le n) P'.genericPoint) ≤ 1 ∧
        ¬ Order.coheight (p n le_rfl P'.genericPoint) ≤ 1 := by
    intro P P' hP hP'
    have hP'P : p 0 (Nat.zero_le n) P'.genericPoint = P.genericPoint :=
      (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ P' P).mp hP'
    refine ⟨((congrArg (Order.coheight (α := X)) hP'P).trans P.coheight_genericPoint).le,
      fun hc => ?_⟩
    obtain ⟨F, hF⟩ := hprime n le_rfl P' hc
    have hT := (hφT P P' hP'P F).mpr hF
    rcases hP with hnd | ⟨-, h2⟩
    · exact hnd (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hT).1
    · have hmem : F.genericPoint ∈
          (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set _) := by
        rw [← MMP.Mori.RationalMap.support_transformPrimeDivisor hT,
          AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) F.genericPoint hmem
      rw [F.coheight_genericPoint] at this
      exact absurd this (by decide)
  have hexcq : ∀ P : MMP.Mori.PrimeDivisor W, ¬ Order.coheight (p n le_rfl P.genericPoint) ≤ 1 →
      IsExceptionalPrimeDivisor (modelStr sX sYi n) (p n le_rfl) P := by
    intro P hP
    haveI : LocallyOfFiniteType (modelStr sX sYi n) := hlft n le_rfl
    have hWn : IsNormalVariety ℂ (p n le_rfl ≫ modelStr sX sYi n) := by rwa [hpn.1]
    exact isExceptionalPrimeDivisor_of_two_le_coheight (hmod n le_rfl).2.2.1 hWn hpn.2.2 P
      (by
        rcases le_or_gt (Order.coheight (p n le_rfl P.genericPoint)) 1 with h | h
        · exact absurd h hP
        · have := Order.add_one_le_of_lt h
          rwa [one_add_one_eq_two] at this)
  have hqc : QuasiCompact (modelStr sX sYi n) :=
    ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp (hmod n le_rfl).1).1.toQuasiCompact
  -- the telescoping sum of the comparisons
  have htel : ∀ P, (G 0 - G n).coeff P = ∑ i ∈ Finset.range n, (G i - G (i + 1)).coeff P := by
    intro P
    simp only [DivisorWithCoeffs.coeff_sub]
    exact (Finset.sum_range_sub' (fun i => (G i).coeff P) n).symm
  have hEff : ∀ P, 0 ≤ (G 0 - G n).coeff P := fun P => by
    rw [htel]
    exact Finset.sum_nonneg fun i hi => (hcoeff i (Finset.mem_range.mp hi) P).1
  have hExc : ∀ P, (G 0 - G n).coeff P ≠ 0 →
      IsExceptionalPrimeDivisor (modelStr sX sYi n) (p n le_rfl) P := fun P hP => by
    refine hexcq P fun hc => hP ?_
    rw [htel]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    exact (hcoeff i hi P).2.1 (hcohn _ hc (i + 1) hi)
  have hPos : ∀ (P : MMP.Mori.PrimeDivisor X), RationalMap.IsExceptional φ P →
      ∀ P' : MMP.Mori.PrimeDivisor W,
        RationalMap.transformPrimeDivisor (p 0 (Nat.zero_le n)).toRationalMap P' = some P →
        0 < (G 0 - G n).coeff P' := fun P hP P' hP' => by
    obtain ⟨h0, hn⟩ := hφexc P P' hP hP'
    obtain ⟨j, hj, hj0, hj1⟩ : ∃ (j : ℕ) (hj : j < n),
        Order.coheight (p j hj.le P'.genericPoint) ≤ 1 ∧
        ¬ Order.coheight (p (j + 1) hj P'.genericPoint) ≤ 1 := by
      by_contra! hcon
      have : ∀ i (hi : i ≤ n), Order.coheight (p i hi P'.genericPoint) ≤ 1 := by
        intro i hi
        induction i with
        | zero => exact h0
        | succ k ih => exact hcon k hi (ih (Nat.le_of_succ_le hi))
      exact hn (this n le_rfl)
    rw [htel]
    exact Finset.sum_pos' (fun i hi => (hcoeff i (Finset.mem_range.mp hi) P').1)
      ⟨j, Finset.mem_range.mpr hj, (hcoeff j hj P').2.2 hj0 hj1⟩
  have hGY : IsRCartierPullback (p n le_rfl)
      (logCanonicalDivisor (RationalMap.transformDivisor φ K)
        (RationalMap.transformDivisor φ B)) (G n) := by
    rw [hφK, hφB]; exact hG n le_rfl
  -- the tower lies over `S`
  have hpS := tower_comp_eq f fp h (modelMap g πY) n (fun i hi => (hstep i hi).2.2.1.comp_eq)
    (fun i hi => (hstep i hi).2.2.2.2.1) p hpq
  have hφover : MMP.Flips.RationalMap.IsOver g (modelMap g πY n) φ := by
    have e : (h₀.compHom (p n le_rfl)).compHom (modelMap g πY n) =
        (modelMap g πY 0).toRationalMap := by
      rw [compHom_compHom, hpS n le_rfl, ← compHom_compHom,
        compHom_eq_id_of_isInverse _ hh₀, toRationalMap_compHom, Category.id_comp]
    exact e
  have hφnex : ∀ F : MMP.Mori.PrimeDivisor (modelSeq X Yi n),
      ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := fun F hF => by
    obtain ⟨P, hP⟩ := hover n le_rfl F
    obtain ⟨G₀, hG₀⟩ := hprime 0 (Nat.zero_le n) P
      (hcohn P.genericPoint (by rw [hP, F.coheight_genericPoint]) 0 (Nat.zero_le n))
    exact hF G₀ ((hφT G₀ P hG₀ F).mpr hP)
  -- the nefness of the last adjoint
  have hnefK : IsRelativelyNef ℂ (modelStr sX sYi n) (modelMap g πY n)
      (logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n)) := by
    rcases hend with hend | hft
    · exact hend
    · exfalso
      obtain ⟨Rn, V, _, _, _, sV, fn, hn, hRn, hnegR, hface, hVp, hNE, hdimV⟩ := hft
      obtain ⟨mD, rD, AD, wD, hwD, hKB, hpe⟩ := hpsef
      haveI := hqc
      haveI : QuasiCompact sX := hXv.1.toQuasiCompact
      have hYQ := (hmod n le_rfl).2.1
      have hcontr := hNE.isContraction
      haveI : IsProper fn := hcontr.isProper
      haveI : IsDominant fn := isDominant_of_isContraction hcontr
      have hT : MMP.Mori.RationalMap.transformDivisor φ
          (∑ i, rD i • Divisor.toRDivisor (wD i)) =
            Divisor.toRDivisor (K' n) + divisorSeq B BY n := by
        rw [← hKB, logCanonicalDivisor, map_add, transformDivisor_toRDivisor, hφK, hφB]
      have hKK : Divisor.LinearlyEquivalent (divisorSeq K KY n - K' n) 0 := by
        haveI := hlft n le_rfl
        obtain ⟨τ, hτ0, hτK⟩ := hτ n le_rfl
        obtain ⟨m, hm⟩ := hcan n le_rfl
        have hm3 : m = 3 := by
          have := hm.topologicalKrullDim_eq
          rw [(hmod n le_rfl).2.2.1] at this
          exact_mod_cast this.symm
        subst hm3
        obtain ⟨ψ, hψ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXnv hm hτ0
        rw [one_zsmul, hτK] at hψ
        exact sub_linearlyEquivalent_zero (Divisor.LinearlyEquivalent.symm
          (⟨ψ, hψ⟩ : Divisor.LinearlyEquivalent (K' n) (divisorSeq K KY n)))
      refine false_of_isRelativelyPseudoEffective hX hXQ (hmod n le_rfl).1 hYQ hS hg
        (hmod n le_rfl).2.2.2.1 (isBirational_compHom_of_isInverse _ hh₀ _ hpn.2.2) hφover hφnex
        ((MMP.Mori.isProjectiveVariety_iff ℂ _).mp hVp).1 hcontr.comp_eq hdimV hface.comp_eq
        hRn.2 hface.isContractedBy_iff hnegR hwD hpe ?_
      intro C _
      rw [hT]
      have e : logCanonicalDivisor (divisorSeq K KY n) (divisorSeq B BY n) =
          (Divisor.toRDivisor (K' n) + divisorSeq B BY n) +
            Divisor.toRDivisor (divisorSeq K KY n - K' n) := by
        simp only [logCanonicalDivisor, map_sub]
        abel
      rw [e, ← rIntersectionₗ_apply, map_add, rIntersectionₗ_apply, rIntersectionₗ_apply,
        rIntersection_toRDivisor_of_linearlyEquivalent hYQ C hKK, add_zero]
  have hnefn : IsRelativelyNef ℂ (modelStr sX sYi n) (modelMap g πY n)
      (logCanonicalDivisor (RationalMap.transformDivisor φ K)
        (RationalMap.transformDivisor φ B)) := by
    rw [hφK, hφB]
    haveI := hlft n le_rfl
    obtain ⟨τ, hτ0, hτK⟩ := hτ n le_rfl
    obtain ⟨m, hm⟩ := hcan n le_rfl
    have hm3 : m = 3 := by
      have := hm.topologicalKrullDim_eq
      rw [(hmod n le_rfl).2.2.1] at this
      exact_mod_cast this.symm
    subst hm3
    obtain ⟨ψ, hψ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXnv hm hτ0
    have hE : (K' n - divisorSeq K KY n).LinearlyEquivalent 0 :=
      ⟨ψ, by rw [sub_zero, ← hτK, ← hψ, one_zsmul]⟩
    have := isRelativelyNef_add_of_linearlyEquivalent hnefK hE
    convert this using 1
    simp only [logCanonicalDivisor, map_sub]
    abel
  have hWM : IsNefWeakModel sX (modelStr sX sYi n) sS g (modelMap g πY n) K B φ :=
    { isNormalVariety_source := hXv
      isProjectiveVariety_source := hX
      comp_eq_source := hg
      isCanonicalDivisor := hK
      isCartierCombination := isCartierCombination_of_isQFactorial hXQ _
      isNormalVariety_target := hXnv
      isProjectiveVariety_target := (hmod n le_rfl).1
      comp_eq_target := (hmod n le_rfl).2.2.2.1
      isBirational := isBirational_compHom_of_isInverse _ hh₀ _ hpn.2.2
      isOver := hφover
      not_isInverseExceptional := hφnex
      isRelativelyNef := hnefn
      exists_resolution := ⟨W, inferInstance, inferInstance, inferInstance, sW,
        p 0 (Nat.zero_le n), p n le_rfl, h₀, hWv, hWsm, hp0.1, hpn.1, hp0.2.1, hpn.2.1, hp0.2.2,
        hpn.2.2, hh₀, rfl, G 0, G n, hG 0 (Nat.zero_le n), hGY, hEff, hExc⟩ }
  exact ⟨modelSeq X Yi n, inferInstance, inferInstance, inferInstance, modelStr sX sYi n, hqc,
    modelMap g πY n, φ, hWM, (hmod n le_rfl).2.1, by rw [hφB]; exact (hmod n le_rfl).2.2.2.2,
    W, inferInstance, inferInstance, inferInstance, sW, p 0 (Nat.zero_le n), p n le_rfl, h₀, hWv,
    hWsm, hp0.1, hpn.1, hp0.2.1, hpn.2.1, hp0.2.2, hpn.2.2, hh₀, rfl, G 0, G n,
    hG 0 (Nat.zero_le n), hGY, hEff, hExc, hPos⟩

end Proof_thm_fourfold_projective_real_threefold_log_model

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Log terminal models of pseudo-effective projective real klt threefolds.** Let `g : X ⟶ S` be
a morphism of projective complex varieties, `X` a normal `ℚ`-factorial threefold with canonical
divisor `K`, and `(X, B)` a klt pair with effective real boundary. If `K + B` is pseudo-effective
over `S`, there is a nef weak model `φ : X ⤏ Y` over `S` with `Y` projective and `ℚ`-factorial and
`(Y, φ_* B)` klt, and a common resolution `p : W ⟶ X`, `q : W ⟶ Y` on which
`p^*(K + B) - q^*(K_Y + φ_* B)` is effective, `q`-exceptional, and positive along the strict
transform of every `φ`-exceptional prime divisor of `X`. -/
@[mmp "thm_fourfold_projective_real_threefold_log_model"]
public theorem IsRealKltPair.exists_isNefWeakModel_of_isRelativelyPseudoEffective
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B : RDivisor X}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB0 : 0 ≤ B) (hB : IsRealKltPair sX B)
    (hpsef : ∃ (m : ℕ) (r : Fin m → ℝ) (A : Fin m → X.CartierDivisor) (w : Fin m → Divisor X),
      (∀ i, MMP.Intersection.IsWeilDivisorOfCartier (A i) (w i)) ∧
      logCanonicalDivisor K B = ∑ i, r i • Divisor.toRDivisor (w i) ∧
      KCartierDivisor.IsRelativelyPseudoEffective sX g (∑ i, Finsupp.single (A i) (r i))) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (_ : QuasiCompact sY) (πY : Y ⟶ S) (φ : X.RationalMap Y),
      IsNefWeakModel sX sY sS g πY K B φ ∧ IsQFactorial sY ∧
      IsRealKltPair sY (MMP.Mori.RationalMap.transformDivisor φ B) ∧
      ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
        (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W),
        MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sX = sW ∧ q ≫ sY = sW ∧
          IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
          IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
          h.compHom q = φ ∧
          ∃ GX GY : RDivisor W,
            IsRCartierPullback p (logCanonicalDivisor K B) GX ∧
            IsRCartierPullback q
              (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                (MMP.Mori.RationalMap.transformDivisor φ B)) GY ∧
            (∀ P, 0 ≤ (GX - GY).coeff P) ∧
            (∀ P, (GX - GY).coeff P ≠ 0 → IsExceptionalPrimeDivisor sY q P) ∧
            ∀ P : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.IsExceptional φ P →
              ∀ P' : MMP.Mori.PrimeDivisor W,
                MMP.Mori.RationalMap.transformPrimeDivisor p.toRationalMap P' = some P →
                0 < (GX - GY).coeff P' :=
                  by
                    revert X S sX sS g K B hX hS hg hXQ hdim hK hB0 hB hpsef
                    exact Proof_thm_fourfold_projective_real_threefold_log_model.solution

end MMP.Fourfold
