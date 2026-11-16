module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.Flip.ProcedureDivisorSpan
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.ChowForm.FibreChowForm
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Small `(K + Θ')`-negative contractions in the first MMP of the flipping procedure

Let `P = (π, (F_j), H')` be a procedure datum (`MMP.Flips.ProcedureDatum`) for `(X, D, f)`,
`f : X ⟶ Z`, and let `(Y', Θ', h')` belong to the class `𝒮₁(H')` of the first MMP
(`MMP.Flips.ProcedureDatum.IsInFirstClass`). Let `φ : Y' ⟶ W` be a small
`(K + Θ')`-negative extremal contraction over `Z` (`MMP.Flips.IsNegativeExtremalContraction`,
`MMP.Flips.IsSmall`, with `φ ≫ g = h'`). Then every curve contracted by `φ` lies in
`Supp h'^*H' = h'⁻¹(Supp H')`, and some prime divisor of `Y'` contained in `h'⁻¹(Supp H')`, which
then has coefficient `1` in `Θ'`, is `φ`-negative (`MMP.Flips.IsRelativelyNegative`).

A contracted curve `Γ` is contracted by `h'`, which is an isomorphism over `Z ∖ Supp H'`, so it
lies over `Supp H'`. Writing `h'^*H' = ∑ m_F F`, one has `h'^*H' · Γ = 0`; the components `F`
span `N¹(Y'/Z)` (`MMP.Flips.ProcedureDatum.exists_isNumericallyEquivalentOver_of_isQFactorial`),
and `(K + Θ') · Γ < 0`, so some `F · Γ < 0`. Since `ρ(Y'/W) = 1`, all contracted curves are
numerically proportional, so this `F` is `φ`-negative.

The second conclusion uses only that `h'` is a projective birational morphism from a normal
`ℚ`-factorial variety whose exceptional prime divisors lie in `h'⁻¹(Supp H')`, along which `Θ'`
has coefficient `1`, and needs neither smallness nor the isomorphism over `Z ∖ Supp H'`: the
components of the strict transform `h'⁻¹_*H'` lie over `Supp H'` for any birational `h'`. This
weaker form is what survives the flips of the program.

## Main results

* `MMP.Flips.ProcedureDatum.IsInFirstClass.exists_isRelativelyNegative_of_isSmall`: every
  `φ`-contracted curve lies in `h'⁻¹(Supp H')`, and some component of `h'⁻¹(Supp H')` with
  coefficient `1` in `Θ'` is `φ`-negative.
* `MMP.Flips.ProcedureDatum.exists_isRelativelyNegative_of_exceptional_subset`: the `φ`-negative
  component, for a projective birational `h'` whose exceptional divisors lie over `Supp H'`.

## Implementation notes

The extremal ray `R` of `NE(Y'/Z)` enters only through its contraction: a small
`(K + Θ')`-negative extremal contraction `φ : Y' ⟶ W` over `Z` (so `ρ(Y'/W) = 1` and
`-(K + Θ')` is `φ`-ample) contracts exactly one `(K + Θ')`-negative extremal ray of `NE(Y'/Z)`,
so the statement is made for `φ`. The support of the pull-back `h'^*H'` of the effective Cartier
divisor `H'` is written as the preimage `h'⁻¹(Supp H')`
(`MMP.Flips.supp_eq_preimage_supp_of_isPullback`), and an irreducible component of it as a prime
divisor contained in it. The source works over `ℂ`; the statements are made over an arbitrary
field `k`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 18.12.3, 18.13
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips

open MMP.Mori

/-! ### Intersection numbers with proper curves -/

/-- A proper curve, as a scheme, has more than one point. -/
private theorem not_subsingleton_scheme {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) : ¬ Subsingleton C.scheme := by
  intro
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  have : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  have : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  refine not_subsingleton_scheme C ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
  obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
  exact (hy x).trans (hy x').symm

/-- A normalization `ν : C' ⟶ C` of a proper curve with `dim C' ≤ 1` is a curve over `k`. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
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

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by
    rw [← Category.assoc]
    infer_instance
  have := isCurve_comp C hν hdim
  have := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rwa [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- The degree of `𝒪_X(L)` along a proper curve `C` is the intersection number `L · C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  have : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn C (L j) (hL j), rfl⟩

end Intersection

/-! ### Positivity and relative Picard number one -/

section PicardNumberOne

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D) (hDc : D.IsCartier)
    (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- On an integral normal scheme, every Cartier Weil divisor `D` has a Cartier divisor whose
degree on every proper curve is `deg_C 𝒪_X(D)`. -/
private theorem exists_cartierDivisor_degree_eq [IsIntegral X] (D : Divisor X)
    (hD : D.IsCartier) : ∃ E : X.CartierDivisor, ∀ C : ProperCurve sX,
      (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        (D.degreeOn k sX C.ι C.dim_le hD : ℝ) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  refine ⟨E, fun C => ?_⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

/-- If `N¹(X/Z)` is one-dimensional, some proper curve is contracted by `f`. -/
private theorem exists_isContractedBy_of_finrank_eq_one {Z : Scheme.{u}} (f : X ⟶ Z)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  haveI := Module.finite_of_finrank_eq_succ hfin
  obtain ⟨v, hv⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp (by rw [hfin]; exact one_pos)
  obtain ⟨δ, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors] at hv
  push Not at hv
  exact hv.imp fun _ h => h.1

/-- **Numerical proportionality in a one-dimensional `N¹(X/Z)`.** If `N¹(X/Z)` is
one-dimensional and `δH` is not numerically trivial on some contracted curve, then every
`ℝ`-Cartier divisor `δL` is numerically `f`-equivalent to a multiple `c • δH`. -/
private theorem exists_intersectionNumber_eq_mul_of_finrank_eq_one {Z : Scheme.{u}} (f : X ⟶ Z)
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    (δH δL : KCartierDivisor ℝ X) {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (h₀ : (C₀.cycle ℝ).intersectionNumber δH ≠ 0) :
    ∃ c : ℝ, ∀ C : ProperCurve sX, C.IsContractedBy f →
      (C.cycle ℝ).intersectionNumber δL = c * (C.cycle ℝ).intersectionNumber δH := by
  have hne : (Submodule.Quotient.mk δH : RelativeNumericalDivisorClasses sX f) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors]
    exact fun h => h₀ (h C₀ hC₀)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin (Submodule.Quotient.mk δL)
  have hmem : δL - c • δH ∈ relativeNumericallyTrivialDivisors sX f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      hc, sub_self]
  refine ⟨c, fun C hC => ?_⟩
  have := (mem_relativeNumericallyTrivialDivisors sX f).mp hmem C hC
  simp only [OneCycle.intersectionNumber, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul] at this ⊢
  linarith

/-- **Proportionality of degrees in `ρ(X/Z) = 1`.** If `N¹(X/Z)` is one-dimensional and the
Cartier divisor `A` has nonzero degree on some contracted curve, the degrees of any Cartier
divisor `B` on the contracted curves are a fixed real multiple of those of `A`. -/
private theorem exists_degreeOn_eq_mul_of_finrank_eq_one [IsIntegral X] {Z : Scheme.{u}}
    (f : X ⟶ Z) (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    {A B : Divisor X} (hA : A.IsCartier) (hB : B.IsCartier) {C₀ : ProperCurve sX}
    (hC₀ : C₀.IsContractedBy f) (h₀ : A.degreeOn k sX C₀.ι C₀.dim_le hA ≠ 0) :
    ∃ c : ℝ, ∀ C : ProperCurve sX, C.IsContractedBy f →
      (B.degreeOn k sX C.ι C.dim_le hB : ℝ) = c * A.degreeOn k sX C.ι C.dim_le hA := by
  obtain ⟨EA, hEA⟩ := exists_cartierDivisor_degree_eq (sX := sX) A hA
  obtain ⟨EB, hEB⟩ := exists_cartierDivisor_degree_eq (sX := sX) B hB
  obtain ⟨c, hc⟩ := exists_intersectionNumber_eq_mul_of_finrank_eq_one f hfin
    (KCartierDivisor.ofCartier ℝ EA) (KCartierDivisor.ofCartier ℝ EB) hC₀
    (by simpa [hEA] using h₀)
  exact ⟨c, fun C hC => by simpa only [hEA, hEB] using hc C hC⟩

end PicardNumberOne

/-! ### Curves contracted by a morphism which is an isomorphism over an open -/

/-- A proper curve contracted by `h : Y ⟶ Z` has its generic point outside `h⁻¹(U)` whenever `h`
is an isomorphism over the open `U ⊆ Z`. -/
private theorem point_notMem_preimage_of_isContractedBy {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY] (C : ProperCurve sY)
    (h : Y ⟶ Z) (hC : C.IsContractedBy h) (U : Z.Opens) [IsIso (h ∣_ U)] :
    C.point ∉ h ⁻¹ᵁ U := by
  intro hpt
  have hinj : ∀ x ∈ closure ({C.point} : Set Y), x ∈ h ⁻¹ᵁ U → x = C.point := by
    intro x hx hxU
    have e : ∀ a, h ((h ⁻¹ᵁ U).ι a) = U.ι ((h ∣_ U) a) := fun a => by
      rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
    obtain ⟨a, rfl⟩ : x ∈ Set.range (h ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨b, hb⟩ : C.point ∈ Set.range (h ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
    rw [← hb]
    congr 1
    refine (h ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective ?_)
    rw [← e, ← e, hb]
    exact hC _ hx
  have hlc : IsLocallyClosed ({C.point} : Set Y) := by
    refine ⟨h ⁻¹ᵁ U, closure {C.point}, (h ⁻¹ᵁ U).isOpen, isClosed_closure, ?_⟩
    ext x
    refine ⟨?_, fun hx => hinj x hx.2 hx.1⟩
    rintro rfl
    exact ⟨hpt, subset_closure rfl⟩
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have hcl : closure ({C.point} : Set Y) = {C.point} :=
    (isClosed_singleton_of_isLocallyClosed_singleton hlc).closure_eq
  refine not_subsingleton_scheme C ⟨fun a b => C.ι.isClosedEmbedding.injective ?_⟩
  have ha : C.ι a ∈ closure ({C.point} : Set Y) := by rw [← C.range_ι]; exact ⟨a, rfl⟩
  have hb : C.ι b ∈ closure ({C.point} : Set Y) := by rw [← C.range_ι]; exact ⟨b, rfl⟩
  rw [hcl] at ha hb
  exact ha.trans hb.symm

/-! ### Coefficients and supports -/

/-- A prime divisor whose support lies in `Supp D` has nonzero coefficient in `D`. -/
private theorem coeff_ne_zero_of_support_subset_supp {R : Type*} [Zero R] {X : Scheme.{u}}
    {D : DivisorWithCoeffs R X} {E : Mori.PrimeDivisor X}
    (h : (E.support : Set X) ⊆ D.supp) : D.coeff E ≠ 0 := by
  have hη : E.genericPoint ∈ (E.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨E', hE', hmem⟩ := DivisorWithCoeffs.mem_supp_iff.mp (h hη)
  rwa [MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem] at hE'

/-- **The strict transform lies over the divisor.** For a birational morphism `h : Y ⟶ Z` of
reduced separated schemes, a prime divisor `Q` of `Y` with nonzero coefficient in `h⁻¹_*B` is
the transform of a component `P` of `B`, so `h(η_Q) = η_P ∈ Supp B`. -/
private theorem map_genericPoint_mem_supp_of_coeff_ne_zero {Y Z : Scheme.{u}} [IsReduced Y]
    [IsReduced Z] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)] {R : Type*}
    [AddCommMonoid R] (h : Y ⟶ Z) (hbir : IsBirationalMorphism h) {B : DivisorWithCoeffs R Z}
    {Q : Mori.PrimeDivisor Y} (hQ : (birationalInverseTransform h hbir B).coeff Q ≠ 0) :
    h Q.genericPoint ∈ (B.supp : Set Z) := by
  classical
  rw [birationalInverseTransform, ← Finsupp.sum_single B, Finsupp.sum, map_sum,
    DivisorWithCoeffs.coeff, Finsupp.finset_sum_apply] at hQ
  obtain ⟨P, hPB, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  rw [Mori.RationalMap.transformDivisor_single] at hne
  obtain ⟨Q', hPQ⟩ : ∃ Q', Mori.RationalMap.transformPrimeDivisor
      (RationalMap.IsBirational.inverse hbir) P = some Q' := by
    cases hP : Mori.RationalMap.transformPrimeDivisor (RationalMap.IsBirational.inverse hbir) P
    · simp [hP] at hne
    · exact ⟨_, rfl⟩
  rw [hPQ, Option.elim, Finsupp.single_apply_ne_zero] at hne
  obtain ⟨rfl, -⟩ := hne
  obtain ⟨e, he, he'⟩ := hbir.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hPQ).1
  have hcomp : (g'.compHom h).toRationalMap = (Scheme.PartialMap.id Z).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← he',
      ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ h = e.target.ι ≫ 𝟙 Z
    have hs : e.source.ι ≫ h = e.iso.hom ≫ e.target.ι :=
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
    rw [hs, Iso.inv_hom_id_assoc, Category.comp_id]
  have hmap := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hcomp hP trivial
  change (g'.hom ≫ h) ⟨P.genericPoint, hP⟩ = (Z.topIso.hom ≫ 𝟙 Z) ⟨P.genericPoint, trivial⟩
    at hmap
  have hhg : h (g'.hom ⟨P.genericPoint, hP⟩) = P.genericPoint := by
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (hmap.trans ?_)
    rw [Category.comp_id, Scheme.topIso_hom]
    rfl
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some hPQ g' hg' hP, hhg]
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, Finsupp.mem_support_iff.mp hPB, ?_⟩
  change P.genericPoint ∈ (P.support : Set Z)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-! ### Intersection numbers of `ℝ`-divisors through Cartier multiples of prime divisors -/

section CartierMultiples

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- `(c / μ) • (μ Q) = c Q` for a prime divisor `Q` and `μ > 0`. -/
private theorem div_smul_toRDivisor_zsmul_single (Q : Mori.PrimeDivisor X) {μ : ℕ} (hμ : 0 < μ)
    (c : ℝ) :
    (c / μ) • Divisor.toRDivisor ((μ : ℤ) • Finsupp.single Q (1 : ℤ)) = Finsupp.single Q c := by
  classical
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.smul_apply, ← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toRDivisor,
    DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply]
  have : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ.ne'
  split_ifs
  · simp only [smul_eq_mul, mul_one, Int.cast_natCast]
    field_simp
  · simp

/-- If every prime divisor `P` has a Cartier multiple `μ P • P`, every `ℝ`-divisor `D` has the
intersection number `D · C = ∑_P D_P ((μ P • P · C) / μ P)` with every proper curve `C`. -/
private theorem exists_isRIntersectionNumber_sum_support (C : ProperCurve sX)
    (μ : Mori.PrimeDivisor X → ℕ) (hμpos : ∀ P, 0 < μ P)
    (hμ : ∀ P, Divisor.IsCartier ((μ P : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X))
    (D : RDivisor X) :
    ∃ (n : ℕ) (r : Fin n → ℝ) (L : Fin n → Divisor X), IsRIntersectionNumber k sX D r L C
      (∑ P ∈ D.support, D P * ((Divisor.degreeOn k sX C.ι C.dim_le
        ((μ P : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X) (hμ P) : ℝ) / μ P)) := by
  classical
  let e := D.support.equivFin
  let Q : Fin D.support.card → Mori.PrimeDivisor X := fun j => (e.symm j : Mori.PrimeDivisor X)
  let r : Fin D.support.card → ℝ := fun j => D (Q j) / μ (Q j)
  let L : Fin D.support.card → Divisor X := fun j => (μ (Q j) : ℤ) • Finsupp.single (Q j) 1
  have h := isRIntersectionNumber_sum_degreeOn (k := k) C r L (fun j => hμ (Q j))
  have hD : ∑ j, r j • Divisor.toRDivisor (L j) = D := by
    rw [Finset.sum_congr rfl fun j _ => div_smul_toRDivisor_zsmul_single (Q j) (hμpos (Q j)) _,
      Equiv.sum_comp e.symm (fun x : D.support => Finsupp.single (x : Mori.PrimeDivisor X) (D x)),
      Finset.sum_coe_sort D.support (fun P => Finsupp.single P (D P))]
    exact Finsupp.sum_single D
  have hx : ∑ j, r j * (((L j).degreeOn k sX C.ι C.dim_le (hμ (Q j))) : ℝ) =
      ∑ P ∈ D.support, D P * ((Divisor.degreeOn k sX C.ι C.dim_le
        ((μ P : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X) (hμ P) : ℝ) / μ P) := by
    rw [Equiv.sum_comp e.symm (fun x : D.support => D x / μ x * (Divisor.degreeOn k sX C.ι
      C.dim_le ((μ x : ℤ) • Finsupp.single (x : Mori.PrimeDivisor X) (1 : ℤ) : Divisor X)
        (hμ x) : ℝ)), Finset.sum_coe_sort D.support (fun P => D P / μ P *
      (Divisor.degreeOn k sX C.ι C.dim_le ((μ P : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X)
        (hμ P) : ℝ))]
    exact Finset.sum_congr rfl fun P _ => by ring
  rw [hD, hx] at h
  exact ⟨_, r, L, h⟩

end CartierMultiples

/-- **The pull-back of a Cartier divisor has degree zero on a curve contracted by the first
factor.** For `φ : Y ⟶ W`, `g : W ⟶ Z` with `W` separated and of finite type over `k` and `B` a
Cartier divisor on `Z`, `(φ ≫ g)^*B · C = 0` for every proper curve `C` contracted by `φ`. -/
private theorem degreeOn_pullback_comp_eq_zero {k : Type u} [Field k] {Y W Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [QuasiCompact sY] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated sW] [LocallyOfFiniteType sW]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (φ : Y ⟶ W) (g : W ⟶ Z)
    (hφ : φ ≫ sW = sY) {B : Divisor Z} (hBc : B.IsCartier)
    (hB : ∀ T : irreducibleComponents Y, (φ ≫ g) (componentGenericPoint Y T) ∉ B.supp)
    (C : ProperCurve sY) (hC : C.IsContractedBy φ) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    (B.pullback hBc hB).degreeOn k sY C.ι C.dim_le (hBc.isCartier_pullback (φ ≫ g) hB) = 0 := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI := (hBc.isCartier_pullback (φ ≫ g) hB).isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hBc (φ ≫ g) hB
  let e' : (B.pullback hBc hB).divisorialSheaf ≅
      (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback g).obj B.divisorialSheaf) :=
    e ≪≫ ((Scheme.Modules.pullbackComp φ g).app B.divisorialSheaf).symm
  rw [Divisor.degreeOn, degreeOn_eq_of_iso k sY C.ι C.dim_le e']
  exact ProperCurve.degree_pullback_eq_zero_of_isContractedBy φ hφ C hC _

/-! ### Relative negativity of a prime divisor -/

/-- If `∑_{i ∈ supp H} H_i x_i = 0` with `H ≥ 0`, and some `H_{i₀} ≠ 0` has `x_{i₀} ≠ 0`, then
some `i` with `H_i ≠ 0` has `x_i < 0`. -/
private theorem exists_ne_zero_and_neg_of_sum_mul_eq_zero {ι : Type*} {H : ι →₀ ℝ} {x : ι → ℝ}
    (hH : ∀ i, 0 ≤ H i) (hsum : ∑ i ∈ H.support, H i * x i = 0) {i₀ : ι} (hi₀ : H i₀ ≠ 0)
    (hx : x i₀ ≠ 0) : ∃ i, H i ≠ 0 ∧ x i < 0 := by
  by_contra! hall
  exact mul_ne_zero hi₀ hx <| (Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
    mul_nonneg (hH i) (hall i (Finsupp.mem_support_iff.mp hi))).mp hsum i₀
      (Finsupp.mem_support_iff.mpr hi₀)

section Negativity

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **Negativity spreads along a contraction with `ρ = 1`.** If `N¹(X/Z)` is one-dimensional, `A`
is `f`-ample and the Cartier divisor `M` is negative on one contracted curve `Γ`, then `M` is
negative on every curve contracted by `f`. -/
private theorem degreeOn_neg_of_finrank_eq_one [IsIntegral X] [CompactSpace X] {Z : Scheme.{u}}
    (f : X ⟶ Z) (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    {A M : Divisor X} (hA : IsRelativelyAmpleCartier f A) (hAc : A.IsCartier) (hMc : M.IsCartier)
    {Γ : ProperCurve sX} (hΓ : Γ.IsContractedBy f) (hMΓ : M.degreeOn k sX Γ.ι Γ.dim_le hMc < 0)
    {C : ProperCurve sX} (hC : C.IsContractedBy f) :
    M.degreeOn k sX C.ι C.dim_le hMc < 0 := by
  have hAΓ := degreeOn_pos_of_isRelativelyAmpleCartier f hA hAc Γ hΓ
  obtain ⟨c, hc⟩ := exists_degreeOn_eq_mul_of_finrank_eq_one f hfin hAc hMc hΓ hAΓ.ne'
  have hcneg : c < 0 := by
    have h1 := hc Γ hΓ
    have : (0 : ℝ) < (A.degreeOn k sX Γ.ι Γ.dim_le hAc : ℝ) := by exact_mod_cast hAΓ
    have : ((M.degreeOn k sX Γ.ι Γ.dim_le hMc : ℤ) : ℝ) < 0 := by exact_mod_cast hMΓ
    nlinarith
  have hAC : (0 : ℝ) < (A.degreeOn k sX C.ι C.dim_le hAc : ℝ) := by
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier f hA hAc C hC
  exact_mod_cast (hc C hC).trans_lt (mul_neg_of_neg_of_pos hcneg hAC)

/-- A prime divisor `F` with a Cartier multiple `μ F` negative on every curve contracted by the
proper morphism `f` is `f`-negative. -/
private theorem isRelativelyNegative_single_of_degreeOn_neg {W : Scheme.{u}} {f : X ⟶ W}
    [IsProper f] (F : Mori.PrimeDivisor X) {μ : ℕ} (hμ : 0 < μ)
    (hMc : Divisor.IsCartier ((μ : ℤ) • Finsupp.single F (1 : ℤ) : Divisor X))
    (hneg : ∀ C : ProperCurve sX, C.IsContractedBy f →
      Divisor.degreeOn k sX C.ι C.dim_le _ hMc < 0) :
    IsRelativelyNegative k sX f (Finsupp.single F (1 : ℝ)) := by
  have hpres : Finsupp.single F (1 : ℝ) = ∑ _j : Fin 1, (1 / (μ : ℝ)) •
      Divisor.toRDivisor ((μ : ℤ) • Finsupp.single F (1 : ℤ) : Divisor X) := by
    rw [Fin.sum_univ_one, div_smul_toRDivisor_zsmul_single F hμ]
  refine ⟨‹_›, ⟨1, fun _ => 1 / (μ : ℝ), fun _ => _, fun _ => hMc, ?_⟩, fun C hC => ?_⟩
  · simpa only [toRDivisor_eq_mapCoeffs] using hpres
  · have hxC := isRIntersectionNumber_sum_degreeOn (k := k) C (fun _ : Fin 1 => 1 / (μ : ℝ))
      (fun _ => _) (fun _ => hMc)
    rw [← hpres] at hxC
    refine ⟨⟨_, _, _, _, hxC⟩, fun m r L y hy => ?_⟩
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ y _ hy hxC, Fin.sum_univ_one]
    exact mul_neg_of_pos_of_neg (by positivity) (by exact_mod_cast hneg C hC)

/-- The divisor `Δ` of a `Δ`-negative extremal contraction `φ` is negative on every curve `Γ`
contracted by `φ`. -/
private theorem exists_isRIntersectionNumber_neg_of_isNegativeExtremalContraction [CompactSpace X]
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} {Δ : RDivisor X} {φ : X ⟶ W}
    (hφ : IsNegativeExtremalContraction k sX sW Δ φ) {Γ : ProperCurve sX}
    (hΓ : Γ.IsContractedBy φ) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX Δ r L Γ x ∧ x < 0 := by
  obtain ⟨mA, a, A, hmA, ha, hA, hEq⟩ := hφ.isRelativelyAntiAmple
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have hEpres : Δ = ∑ j, (-a j) • Divisor.toRDivisor (A j) := by
    rw [← neg_neg Δ, hEq]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hEΓ := isRIntersectionNumber_sum_degreeOn (k := k) Γ (fun j => -a j) A hAc
  rw [← hEpres] at hEΓ
  refine ⟨_, _, _, _, hEΓ, ?_⟩
  have : Nonempty (Fin mA) := ⟨⟨0, hmA⟩⟩
  have hAΓ : ∀ j, 0 < (A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) := fun j =>
    degreeOn_pos_of_isRelativelyAmpleCartier φ (hA j) (hAc j) Γ hΓ
  have : 0 < ∑ j, a j * ((A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (ha j) (by exact_mod_cast hAΓ j)) Finset.univ_nonempty
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- If the Cartier divisor `H ≥ 0` has `H · Γ = 0` and some component `Q₀` of `H` has
`(μ Q₀ • Q₀) · Γ ≠ 0`, then some component `F` of `H` has `(μ F • F) · Γ < 0`. -/
private theorem exists_coeff_ne_zero_degreeOn_neg_of_degreeOn_eq_zero (Γ : ProperCurve sX)
    (μ : Mori.PrimeDivisor X → ℕ) (hμpos : ∀ P, 0 < μ P)
    (hμc : ∀ P, Divisor.IsCartier ((μ P : ℤ) • Finsupp.single P (1 : ℤ) : Divisor X))
    {H : Divisor X} (hHc : H.IsCartier) (hHnn : ∀ Q, 0 ≤ H.coeff Q)
    (hH0 : H.degreeOn k sX Γ.ι Γ.dim_le hHc = 0) {Q₀ : Mori.PrimeDivisor X}
    (hQ₀H : H.coeff Q₀ ≠ 0) (hQ₀ : (Divisor.degreeOn k sX Γ.ι Γ.dim_le _ (hμc Q₀) : ℝ) / μ Q₀ ≠ 0) :
    ∃ F, H.coeff F ≠ 0 ∧ Divisor.degreeOn k sX Γ.ι Γ.dim_le _ (hμc F) < 0 := by
  have hHΓ1 := isRIntersectionNumber_sum_degreeOn (k := k) Γ (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => H) (fun _ => hHc)
  rw [show ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor H = Divisor.toRDivisor H by simp] at hHΓ1
  obtain ⟨nH, rH, LH, hHΓ2⟩ :=
    exists_isRIntersectionNumber_sum_support Γ μ hμpos hμc (Divisor.toRDivisor H)
  have hHsum := (IsRIntersectionNumber.eq_and_linear k sX Γ).1 _ _ _ _ _ _ _ hHΓ1 hHΓ2
  simp only [hH0, Int.cast_zero, mul_zero, Finset.sum_const_zero] at hHsum
  obtain ⟨F, hFH, hFx⟩ := exists_ne_zero_and_neg_of_sum_mul_eq_zero
    (fun Q => show (0 : ℝ) ≤ H.coeff Q by exact_mod_cast hHnn Q) hHsum.symm
    (show (H.coeff Q₀ : ℝ) ≠ 0 by exact_mod_cast hQ₀H) hQ₀
  refine ⟨F, fun h0 => hFH (show (H.coeff F : ℝ) = 0 by rw [h0, Int.cast_zero]), ?_⟩
  have : (0 : ℝ) < μ F := by exact_mod_cast hμpos F
  exact_mod_cast (div_neg_iff.mp hFx).resolve_left (fun h => this.not_gt h.2) |>.1

end Negativity

/-- The divisor `H'` of a procedure datum is effective. -/
public theorem ProcedureDatum.isEffective_H' {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) : DivisorWithCoeffs.IsEffective P.H' := fun E => by
  rcases P.isReduced_H' E with h | h <;> simp [h]

/-- Over a birational `h : Y ⟶ Z`, a prime divisor with nonzero coefficient in a divisor `G`
supported on strict transforms of components of `H'` and on exceptional divisors over `Supp H'`
is a component of `h^*H'`. -/
private theorem ProcedureDatum.coeff_pullback_H'_ne_zero_of_ne_zero {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsLocallyNoetherian Z] [IsNormal Z]
    {D : RDivisor X} {f : X ⟶ Z} (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsSeparated (Y ↘ ⊤_ Scheme)]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {h : Y ⟶ Z} [IsDominant h] (hbir : IsBirationalMorphism h)
    (hexc : ∀ E : Mori.PrimeDivisor Y, IsExceptionalPrimeDivisor sZ h E →
      (E.support : Set Y) ⊆ h.base ⁻¹' (P.H'.supp : Set Z))
    {G : RDivisor Y} (hGcomp : ∀ E : Mori.PrimeDivisor Y, G E ≠ 0 →
      birationalInverseTransform h hbir P.H' E ≠ 0 ∨ IsExceptionalPrimeDivisor sZ h E)
    {Q : Mori.PrimeDivisor Y} (hQ : G Q ≠ 0) :
    (P.H'.pullback P.isCartier_H'
      (map_componentGenericPoint_notMem_supp_of_isDominant h P.H')).coeff Q ≠ 0 := by
  have hsupp := supp_eq_preimage_supp_of_isPullback P.isCartier_H' P.isEffective_H'
    (Divisor.isPullback_pullback P.isCartier_H'
      (map_componentGenericPoint_notMem_supp_of_isDominant h P.H'))
  apply coeff_ne_zero_of_support_subset_supp
  rw [hsupp]
  rcases hGcomp Q hQ with hT | hX
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr
      (map_genericPoint_mem_supp_of_coeff_ne_zero h hbir hT))
      (P.H'.isClosed_supp.preimage h.continuous)
  · exact hexc Q hX

/-- **A `φ`-negative component over `Supp H'`, without the isomorphism over `Z ∖ Supp H'`.** Let
`P` be a procedure datum with divisor `H'` on `Z`, over a field `k`, and let `h : Y' ⟶ Z` be a
projective birational morphism from a normal `ℚ`-factorial variety, every
`h`-exceptional prime divisor of which lies in `h⁻¹(Supp H')`, with a boundary `Θ'` having
coefficient `1` along every prime divisor in `h⁻¹(Supp H')`. Let `φ : Y' ⟶ W` be a
`(K + Θ')`-negative extremal contraction with `φ ≫ g = h`. Then some prime divisor `E` of `Y'`
contained in `h⁻¹(Supp H')` is `φ`-negative. -/
public theorem ProcedureDatum.exists_isRelativelyNegative_of_exceptional_subset
    {k : Type u} [Field k] {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {K : Divisor Y} {Θ : RDivisor Y} {h : Y ⟶ Z}
    (hYq : MMP.Fourfold.IsQFactorial sY) (hsY : h ≫ sZ = sY) (hhp : IsProjectiveMorphism h)
    (hbir : IsBirationalMorphism h)
    (hexc : ∀ E : Mori.PrimeDivisor Y, IsExceptionalPrimeDivisor sZ h E →
      (E.support : Set Y) ⊆ h.base ⁻¹' (P.H'.supp : Set Z))
    (hcoeff : ∀ E : Mori.PrimeDivisor Y,
      (E.support : Set Y) ⊆ h.base ⁻¹' (P.H'.supp : Set Z) → Θ.coeff E = 1)
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} {φ : Y ⟶ W} {g : W ⟶ Z} (hg : φ ≫ g = h)
    (hφ : IsNegativeExtremalContraction k sY sW (Divisor.toRDivisor K + Θ) φ) :
    ∃ E : Mori.PrimeDivisor Y, (E.support : Set Y) ⊆ h.base ⁻¹' (P.H'.supp : Set Z) ∧
      Θ.coeff E = 1 ∧ IsRelativelyNegative k sY φ (Finsupp.single E (1 : ℝ)) := by
  classical
  subst hg
  haveI : IsProper (φ ≫ g) := (IsProjectiveMorphism.isProjective hhp).isProper
  haveI : IsDominant (φ ≫ g) := hbir.isDominant
  haveI : IsSeparated sY := hYq.1.1.toIsSeparated
  haveI : Y.IsSeparated := ⟨by
    rw [show Limits.terminal.from Y = sY ≫ Limits.terminal.from _ from
      Limits.terminal.hom_ext _ _]
    infer_instance⟩
  haveI : Z.IsSeparated := Scheme.isSeparated_of_surjective_universallyClosed (φ ≫ g)
  have hWv := hφ.isNormalVariety_target.1
  haveI : IsSeparated sW := hWv.toIsSeparated
  haveI : LocallyOfFiniteType sW := hWv.toLocallyOfFiniteType
  obtain ⟨mA, -, A, hmA, -, hA, -⟩ := hφ.isRelativelyAntiAmple
  have hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sY φ) = 1 :=
    Module.finrank_eq_of_rank_eq
      (by rw [Cardinal.toENat_eq_one.mp hφ.relativePicardNumber_eq_one]; rfl)
  obtain ⟨Γ, hΓ⟩ := exists_isContractedBy_of_finrank_eq_one φ hfin
  have hΓh : Γ.IsContractedBy (φ ≫ g) := fun x hx => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ x hx]
  obtain ⟨_, _, _, _, hEΓ, hEneg⟩ :=
    exists_isRIntersectionNumber_neg_of_isNegativeExtremalContraction hφ hΓ
  -- `ℚ`-factoriality: Cartier multiples `μ Q • Q` of the prime divisors
  choose μ hμpos hμc using fun Q : Mori.PrimeDivisor Y => hYq.2 (Finsupp.single Q 1)
  -- `K + Θ ≡ G` over `Z` with `G` supported on components of `h⁻¹_*H'` and `h`-exceptional
  -- divisors; some `Q₀ ∈ Supp G` meets `Γ` nontrivially
  obtain ⟨G, hGcomp, hGeq⟩ :=
    P.exists_isNumericallyEquivalentOver_of_isQFactorial hYq hsY hbir hφ.isCartierCombination
  obtain ⟨nG, rG, LG, hGΓ⟩ := exists_isRIntersectionNumber_sum_support Γ μ hμpos hμc G
  obtain ⟨Q₀, -, hQ₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    ((hGeq.2.2 Γ hΓh _ _ _ _ _ _ _ _ hEΓ hGΓ) ▸ hEneg.ne)
  rw [mul_ne_zero_iff] at hQ₀
  -- the pull-back `H = h^*H'`, effective with `Supp H = h⁻¹(Supp H')`
  have hB := map_componentGenericPoint_notMem_supp_of_isDominant (φ ≫ g) P.H'
  set H := P.H'.pullback P.isCartier_H' hB
  have hHpb : P.H'.IsPullback (φ ≫ g) hB H := Divisor.isPullback_pullback P.isCartier_H' hB
  have hsupp := supp_eq_preimage_supp_of_isPullback P.isCartier_H' P.isEffective_H' hHpb
  have hHnn : ∀ Q, 0 ≤ H.coeff Q := fun Q =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) P.isCartier_H'
      (fun P' _ => P.isEffective_H' P') hHpb Q ((Q.genericPoint_mem_iff ((φ ≫ g) ⁻¹ᵁ ⊤)).mp trivial)
  -- `H · Γ = 0`, so some `F₀ ∈ Supp H` has `F₀ · Γ < 0`
  haveI : CompactSpace Z := (φ ≫ g).surjective.compactSpace (φ ≫ g).continuous
  obtain ⟨F₀, hF₀H, hMΓ⟩ := exists_coeff_ne_zero_degreeOn_neg_of_degreeOn_eq_zero Γ μ hμpos hμc
    (P.isCartier_H'.isCartier_pullback (φ ≫ g) hB) hHnn
    (degreeOn_pullback_comp_eq_zero φ g hφ.isContraction.comp_eq P.isCartier_H' hB Γ hΓ)
    (P.coeff_pullback_H'_ne_zero_of_ne_zero hbir hexc hGcomp hQ₀.1) hQ₀.2
  have hF₀supp : (F₀.support : Set Y) ⊆ (φ ≫ g).base ⁻¹' (P.H'.supp : Set Z) :=
    hsupp ▸ DivisorWithCoeffs.support_subset_supp hF₀H
  -- `F₀` is negative on every curve contracted by `φ`, since `ρ(Y/W) = 1`
  haveI := hφ.isContraction.isProper
  exact ⟨F₀, hF₀supp, hcoeff F₀ hF₀supp,
    isRelativelyNegative_single_of_degreeOn_neg F₀ (hμpos F₀) (hμc F₀)
      fun C hC => degreeOn_neg_of_finrank_eq_one φ hfin (hA ⟨0, hmA⟩) (hA _).1 (hμc F₀) hΓ hMΓ hC⟩

/-- **Curves of a small extremal contraction in the first procedure MMP** (FA 18.12.3, 18.13).
Let `P` be a procedure datum for `(X, D, f)` with divisor `H'` on `Z`, over a field `k`, let
`(Y', Θ', h')` belong to the class `𝒮₁(H')`
(`MMP.Flips.ProcedureDatum.IsInFirstClass`, with canonical divisor `K` of `Y'`), and let
`φ : Y' ⟶ W` be a small `(K + Θ')`-negative extremal contraction with `φ ≫ g = h'`. Then every
curve contracted by `φ` lies in `h'⁻¹(Supp H')`, and there is a prime divisor `E` of `Y'`
contained in `h'⁻¹(Supp H')`, with coefficient `1` in `Θ'`, which is `φ`-negative. -/
@[mmp "lem_fa18_procedure_flipping_curves_in_support"]
public theorem ProcedureDatum.IsInFirstClass.exists_isRelativelyNegative_of_isSmall
    {k : Type u} [Field k] {X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsLocallyNoetherian Z] [IsNormal Z] {D : RDivisor X} {f : X ⟶ Z}
    (P : ProcedureDatum k sZ D f) {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K : Divisor Y} {Θ : RDivisor Y} {h : Y ⟶ Z}
    (hY : P.IsInFirstClass sY n K Θ h)
    {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} {φ : Y ⟶ W} {g : W ⟶ Z} (hg : φ ≫ g = h)
    (hφ : IsNegativeExtremalContraction k sY sW (Divisor.toRDivisor K + Θ) φ)
    (hs : IsSmall k sW sY φ) :
    (∀ C : ProperCurve sY, C.IsContractedBy φ →
      closure ({C.point} : Set Y) ⊆ h.base ⁻¹' (P.H'.supp : Set Z)) ∧
    ∃ E : Mori.PrimeDivisor Y, (E.support : Set Y) ⊆ h.base ⁻¹' (P.H'.supp : Set Z) ∧
      Θ.coeff E = 1 ∧ IsRelativelyNegative k sY φ (Finsupp.single E (1 : ℝ)) := by
  subst hg
  have hYn : IsNormalVariety k sY := hY.isQFactorialLogTerminalPair.isNormalVariety
  have hsY : (φ ≫ g) ≫ sZ = sY := hY.comp_eq
  have hbir : IsBirationalMorphism (φ ≫ g) := hY.isBirationalMorphism
  haveI : IsProper (φ ≫ g) := (IsProjectiveMorphism.isProjective hY.isProjectiveMorphism).isProper
  haveI : IsIso ((φ ≫ g) ∣_ P.H'.supp.compl) := hY.isIso_restrict
  haveI : IsDominant (φ ≫ g) := hbir.isDominant
  refine ⟨fun C hC => closure_minimal (Set.singleton_subset_iff.mpr (by
    by_contra hnot
    refine point_notMem_preimage_of_isContractedBy C (φ ≫ g) (fun x hx => ?_) P.H'.supp.compl hnot
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]))
    (P.H'.isClosed_supp.preimage (φ ≫ g).continuous), ?_⟩
  -- exceptional primes lie in `Supp h^*H' = h⁻¹(Supp H')`
  have hB := map_componentGenericPoint_notMem_supp_of_isDominant (φ ≫ g) P.H'
  have hHpb := Divisor.isPullback_pullback P.isCartier_H' hB
  have hexc := (P.exceptional_subset_supp_pullback (hsY ▸ hYn) hbir hHpb).1
  rw [supp_eq_preimage_supp_of_isPullback P.isCartier_H' P.isEffective_H' hHpb] at hexc
  exact P.exists_isRelativelyNegative_of_exceptional_subset
    ⟨hYn, hY.isQFactorialLogTerminalPair.isQFactorial⟩ hsY hY.isProjectiveMorphism hbir hexc
    hY.coeff_eq_one rfl hφ

end MMP.Flips
