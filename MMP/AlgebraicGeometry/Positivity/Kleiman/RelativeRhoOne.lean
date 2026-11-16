module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant

/-!
# The relative Kleiman criterion in relative Picard number one

Let `g : Y ⟶ Z` be a projective morphism of normal varieties over an algebraically closed field
of characteristic zero with `ρ(Y/Z) = 1`, and `D = ∑ⱼ aⱼ Lⱼ` an `ℝ`-Cartier divisor which is
`g`-nef and not numerically `g`-trivial. Some contracted curve `C₀` has `D · C₀ > 0`. Since
`N¹(Y/Z)` is spanned by the class of `D`, every `ℝ`-Cartier divisor `δ` satisfies
`δ · z = c_δ (D · z)` on `N₁(Y/Z)`, and the classes of `N₁(Y/Z)` are separated by Cartier
divisors; hence `D` is positive on every nonzero class of the closed relative cone, and so is
every Cartier divisor of positive degree on `C₀`. Such Cartier divisors are `g`-ample by the
relative Kleiman criterion for Cartier divisors.

To pass to real coefficients, pick an integer `N ≫ 0`, write `N aⱼ = cⱼ + fⱼ` with `cⱼ ∈ ℤ` and
`0 < fⱼ ≤ 1`, and a Cartier divisor `H = ± Lⱼ₀` of positive degree on `C₀`. For `M ≫ 0` the
identity
`N D = (∑ cⱼ Lⱼ - (m + 1) M H) + ∑ⱼ fⱼ (M H + Lⱼ) + (m + 1 - ∑ fⱼ) M H`
writes `D` as a positive real combination of Cartier divisors of positive degree on `C₀`.

## Main results

* `MMP.Flips.isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one`: the relative
  Kleiman criterion in relative Picard number one.

## Implementation notes

`ρ(Y/Z)` is `MMP.Flips.relativePicardNumber`, the real dimension of the `ℝ`-Cartier divisors
modulo numerical equivalence on curves contracted by `g`. An `ℝ`-Cartier divisor is an
`MMP.Mori.RDivisor` satisfying `MMP.Flips.IsCartierCombination`; `g`-nefness, numerical
`g`-triviality and `g`-ampleness are `MMP.Flips.IsRelativelyNef`,
`MMP.Flips.IsNumericallyTrivialOver` and `MMP.Flips.IsRelativelyAmple`. Projectivity is
`AlgebraicGeometry.IsProjective`, and `g` is a morphism over `k`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.13, 2.16
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.44
-/

namespace MMP.Flips.RelativeRhoOne

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

section Normalization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
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
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- An integral scheme proper over `k` is a `k`-variety. -/
private theorem isVariety_of_isProper {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [hp : IsProper f] : AlgebraicGeometry.IsVariety k f :=
  { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
    toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have := isVariety_of_isProper (ν ≫ C.ι ≫ sX)
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) [IsDominant f] [LocallyOfFiniteType f]
    (hf : IsBirationalMorphism f) : degreeOver f = 1 := by
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_of_isCurveNormalization C hν hdim
  have hc2 := C.isCurve
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

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

end Normalization

section Classes

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- On an integral normal scheme, a Cartier Weil divisor `D` has `𝒪_X(D) ≅ 𝒪_X(E)` for a Cartier
divisor `E`, whose degree on every proper curve is `deg_C 𝒪_X(D)`. -/
private theorem exists_cartierDivisor_iso [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral X] (D : Divisor X) (hD : D.IsCartier) :
    ∃ E : X.CartierDivisor,
      Nonempty (D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) ∧
      ∀ C : ProperCurve sX, (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        (D.degreeOn k sX C.ι C.dim_le hD : ℝ) := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf D.divisorialSheaf
  refine ⟨E, ⟨e⟩, fun C => ?_⟩
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sX C.ι C.dim_le e).symm

variable {sX} in
/-- `L ↦ deg_C 𝒪_X(L)` as an additive map on Cartier divisors. -/
private noncomputable def degreeHom [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (C : ProperCurve sX) : Divisor.cartierSubgroup (X := X) →+ ℤ where
  toFun L := (L : Divisor X).degreeOn k sX C.ι C.dim_le L.2
  map_zero' := Divisor.degreeOn_zero' k sX C.ι C.dim_le
  map_add' L₁ L₂ := Divisor.degreeOn_add k sX C.ι C.dim_le L₁.1 L₂.1 L₁.2 L₂.2

variable (f : X ⟶ Y)

local notation "I" => RelativeNumericalCurveClasses.intersectionNumber

private theorem intersectionNumber_relativeNumericalClass' (δ : KCartierDivisor ℝ X)
    (Z : relativeOneCycles sX f) :
    I δ (relativeNumericalClass sX f Z) = OneCycle.intersectionPairing δ (Z : OneCycle ℝ sX) :=
  rfl

/-- `(z · δ)` is additive in `δ`. -/
private theorem intersectionNumber_add (δ₁ δ₂ : KCartierDivisor ℝ X) :
    RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f) (δ₁ + δ₂) =
      I δ₁ + I δ₂ :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun Z => by
    change OneCycle.intersectionPairing _ (Z : OneCycle ℝ sX) = _
    rw [map_add]; rfl

/-- `(z · δ)` is homogeneous in `δ`. -/
private theorem intersectionNumber_smul (c : ℝ) (δ : KCartierDivisor ℝ X) :
    RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f) (c • δ) = c • I δ :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun Z => by
    change OneCycle.intersectionPairing _ (Z : OneCycle ℝ sX) = _
    rw [map_smul]; rfl

/-- A numerically `f`-trivial `ℝ`-Cartier divisor vanishes on `N₁(X/Y)`. -/
private theorem intersectionNumber_eq_zero_of_mem_relativeNumericallyTrivialDivisors
    {δ : KCartierDivisor ℝ X} (hδ : δ ∈ relativeNumericallyTrivialDivisors sX f)
    (z : RelativeNumericalCurveClasses sX f) :
    I δ z = 0 := by
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [intersectionNumber_relativeNumericalClass']
  have hle : relativeOneCycles sX f ≤
      LinearMap.ker (OneCycle.intersectionPairing (sX := sX) δ) := by
    rw [relativeOneCycles, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨C, hC, rfl⟩
    exact LinearMap.mem_ker.mpr ((mem_relativeNumericallyTrivialDivisors sX f).mp hδ C hC)
  exact LinearMap.mem_ker.mp (hle hZ)

/-- `z ↦ (z · δ)` is continuous on `N₁(X/Y)`. -/
private theorem continuous_intersectionNumber (δ : KCartierDivisor ℝ X) :
    Continuous (RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f) δ) := by
  induction δ using Finsupp.induction_linear with
  | zero =>
    rw [← zero_smul ℝ (0 : KCartierDivisor ℝ X), intersectionNumber_smul, zero_smul]
    exact continuous_const
  | add δ₁ δ₂ h₁ h₂ => simpa [intersectionNumber_add] using h₁.add h₂
  | single E c =>
    have : ⇑(RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f)
        (Finsupp.single E c)) = fun z => c * RelativeNumericalCurveClasses.degree sX f
          (MMP.CartierDivisor.sheaf E) z := by
      funext z
      obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
      simp [intersectionNumber_relativeNumericalClass', OneCycle.intersectionPairing,
        RelativeNumericalCurveClasses.degree_relativeNumericalClass, OneCycle.cartierDegree]
    rw [this]
    exact continuous_const.mul (RelativeNumericalCurveClasses.continuous_degree sX f _)

/-- On an integral scheme, Cartier divisors separate the points of `N₁(X/Y)`. -/
private theorem eq_zero_of_forall_intersectionNumber_ofCartier [IsIntegral X]
    (z : RelativeNumericalCurveClasses sX f)
    (h : ∀ E : X.CartierDivisor, I (KCartierDivisor.ofCartier ℝ E) z = 0) : z = 0 := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  rw [mem_relativeNumericallyTrivial, OneCycle.mem_numericallyTrivial]
  intro L _
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := h E
  rw [intersectionNumber_relativeNumericalClass', ← OneCycle.intersectionNumber,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- An `ℝ`-Cartier divisor nonnegative on the contracted curves is nonnegative on `NE̅(X/Y)`. -/
private theorem intersectionNumber_nonneg_of_mem_relativeClosedConeOfCurves
    (δ : KCartierDivisor ℝ X)
    (hδ : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ (C.cycle ℝ).intersectionNumber δ)
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    0 ≤ I δ z := by
  have hcl : IsClosed {z : RelativeNumericalCurveClasses sX f | 0 ≤ I δ z} :=
    isClosed_le continuous_const (continuous_intersectionNumber sX f δ)
  have hsub : (relativeConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) ⊆
      {z | 0 ≤ I δ z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hδ C hC
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq, LinearMap.map_smul_of_tower] at hx ⊢
      exact smul_nonneg c.2 hx
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal hsub hcl hz

/-- **Proportionality in relative Picard number one.** If `N¹(X/Y)` is one-dimensional and
`δ₀` is not numerically `f`-trivial, witnessed by a contracted curve `C₀`, then every `ℝ`-Cartier
divisor `δ` is proportional to `δ₀` on `N₁(X/Y)`. -/
private theorem exists_intersectionNumber_eq_mul
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    {δ₀ : KCartierDivisor ℝ X} {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (h₀ : (C₀.cycle ℝ).intersectionNumber δ₀ ≠ 0) (δ : KCartierDivisor ℝ X) :
    ∃ c : ℝ, ∀ z : RelativeNumericalCurveClasses sX f, I δ z = c * I δ₀ z := by
  have hne : (Submodule.Quotient.mk δ₀ : RelativeNumericalDivisorClasses sX f) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors]
    exact fun h => h₀ (h C₀ hC₀)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin (Submodule.Quotient.mk δ)
  have hmem : δ - c • δ₀ ∈ relativeNumericallyTrivialDivisors sX f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      hc, sub_self]
  refine ⟨c, fun z => ?_⟩
  have := intersectionNumber_eq_zero_of_mem_relativeNumericallyTrivialDivisors sX f hmem z
  rw [sub_eq_add_neg, ← neg_smul, intersectionNumber_add, intersectionNumber_smul] at this
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at this
  linarith

/-- **Positivity in relative Picard number one.** If `N¹(X/Y)` is one-dimensional and `δ₀` is
nonnegative on the contracted curves and positive on the contracted curve `C₀`, then every
`ℝ`-Cartier divisor positive on `C₀` is positive on every nonzero class of `NE̅(X/Y)`. -/
private theorem intersectionNumber_pos_of_mem_relativeClosedConeOfCurves [IsIntegral X]
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    (δ₀ : KCartierDivisor ℝ X)
    (hnef : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 ≤ (C.cycle ℝ).intersectionNumber δ₀)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (h₀ : 0 < (C₀.cycle ℝ).intersectionNumber δ₀) (δ : KCartierDivisor ℝ X)
    (hδ : 0 < (C₀.cycle ℝ).intersectionNumber δ) :
    ∀ z ∈ relativeClosedConeOfCurves sX f, z ≠ 0 → 0 < I δ z := by
  obtain ⟨c, hc⟩ := exists_intersectionNumber_eq_mul sX f hfin hC₀ h₀.ne' δ
  have hC₀c : (C₀.cycle ℝ).intersectionNumber δ = c * (C₀.cycle ℝ).intersectionNumber δ₀ :=
    hc (C₀.relativeClass f hC₀)
  have hcpos : 0 < c := pos_of_mul_pos_left (hC₀c ▸ hδ) h₀.le
  intro z hz hz0
  rw [hc z]
  refine mul_pos hcpos ?_
  rcases (intersectionNumber_nonneg_of_mem_relativeClosedConeOfCurves sX f δ₀ hnef hz).lt_or_eq
    with h | h
  · exact h
  · refine absurd (eq_zero_of_forall_intersectionNumber_ofCartier sX f z fun E => ?_) hz0
    obtain ⟨c', hc'⟩ :=
      exists_intersectionNumber_eq_mul sX f hfin hC₀ h₀.ne' (KCartierDivisor.ofCartier ℝ E)
    rw [hc' z, ← h, mul_zero]

end Classes

section Ample

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- If `𝒪_X(D) ≅ 𝒪_X(E)` and `𝒪_X(E)` is `f`-ample, the Cartier Weil divisor `D` is `f`-ample
over every affine open of the target. -/
private theorem isRelativelyAmpleCartier_of_iso {f : X ⟶ Y} [QuasiCompact f] {D : Divisor X}
    (hD : D.IsCartier) {E : X.CartierDivisor}
    (e : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E)
    (h : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf E)) :
    IsRelativelyAmpleCartier f D := by
  have := hD.isInvertibleModule_divisorialSheaf
  have h' : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, hamp⟩ := h y
    exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso
        e.symm)).mp hamp⟩
  exact ⟨hD, fun U hU =>
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance h').2 U hU⟩

end Ample

section Combination

/-- **Positive real combinations of elements of positive degree.** Let `d : G →+ ℤ` be a degree
on an abelian group `G` and `ι : G →+ V` a map to a real vector space. If `∑ⱼ aⱼ d(xⱼ) > 0`,
then `∑ⱼ aⱼ ι(xⱼ)` is a combination `∑ᵢ rᵢ ι(yᵢ)` with at least one term, all `rᵢ > 0` and all
`d(yᵢ) > 0`. -/
private theorem exists_sum_smul_eq_of_pos {G V : Type*} [AddCommGroup G] [AddCommGroup V]
    [Module ℝ V] (d : G →+ ℤ) (ι : G →+ V) {m : ℕ} (a : Fin m → ℝ) (x : Fin m → G)
    (hpos : 0 < ∑ j, a j * (d (x j) : ℝ)) :
    ∃ (n : ℕ) (r : Fin n → ℝ) (y : Fin n → G), 1 ≤ n ∧ (∀ i, 0 < r i) ∧ (∀ i, 0 < d (y i)) ∧
      ∑ j, a j • ι (x j) = ∑ i, r i • ι (y i) := by
  -- an element `H = ± x j₀` of positive degree
  obtain ⟨j₀, hj₀⟩ : ∃ j, d (x j) ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hpos
  set H : G := (d (x j₀)).sign • x j₀ with hHdef
  have hH : 1 ≤ d H := by
    rw [hHdef, map_zsmul, smul_eq_mul, Int.sign_mul_self_eq_abs]
    exact Int.one_le_abs hj₀
  -- the constants `M` and `N`
  set M : ℕ := ∑ j, (d (x j)).natAbs + 1 with hM
  have hM1 : 1 ≤ M := Nat.le_add_left 1 _
  have hMj : ∀ j, ((d (x j)).natAbs : ℤ) < M := fun j => by
    have := Finset.single_le_sum (f := fun j => (d (x j)).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    omega
  set α : ℝ := ∑ j, a j * (d (x j) : ℝ) with hα
  set B : ℝ := ∑ j, |(d (x j) : ℝ)| + ((m : ℝ) + 1) * M * (d H : ℝ)
  have hB : 0 < B := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (mul_pos (mul_pos (by positivity) (by exact_mod_cast hM1)) (by exact_mod_cast hH))
  obtain ⟨N, hN⟩ := exists_nat_gt (B / α)
  have hNα : B < N * α := (div_lt_iff₀ hpos).mp hN
  have hNpos : (0 : ℝ) < N := (div_pos hB hpos).trans hN
  -- `N aⱼ = cⱼ + fⱼ` with `0 < fⱼ ≤ 1`
  set c : Fin m → ℤ := fun j => ⌈(N : ℝ) * a j⌉ - 1 with hcdef
  set f : Fin m → ℝ := fun j => N * a j - c j with hfdef
  have hc : ∀ j, (c j : ℝ) = N * a j - f j := fun j => by simp only [hfdef]; ring
  have hf0 : ∀ j, 0 < f j := fun j => by
    simp only [hfdef, hcdef]; push_cast; linarith [Int.ceil_lt_add_one ((N : ℝ) * a j)]
  have hf1 : ∀ j, f j ≤ 1 := fun j => by
    simp only [hfdef, hcdef]; push_cast; linarith [Int.le_ceil ((N : ℝ) * a j)]
  have hfsum : ∑ j, f j ≤ m := (Finset.sum_le_sum fun j _ => hf1 j).trans (by simp)
  set P : G := ∑ j, c j • x j - (((m : ℤ) + 1) * M) • H with hPdef
  have hP : 0 < d P := by
    have hdP : (d P : ℝ) = ∑ j, (c j : ℝ) * d (x j) - ((m : ℝ) + 1) * M * d H := by
      simp only [hPdef, map_sub, map_sum, map_zsmul, smul_eq_mul]
      push_cast
      ring
    have hsum : N * α - ∑ j, |(d (x j) : ℝ)| ≤ ∑ j, (c j : ℝ) * d (x j) := by
      rw [hα, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have hfd : f j * d (x j) ≤ |(d (x j) : ℝ)| := by
        refine (le_abs_self _).trans ?_
        rw [abs_mul, abs_of_pos (hf0 j)]
        exact mul_le_of_le_one_left (abs_nonneg _) (hf1 j)
      rw [hc]
      nlinarith
    have : (0 : ℝ) < d P := by rw [hdP]; linarith
    exact_mod_cast this
  have hMH : 0 < d ((M : ℤ) • H) := by
    rw [map_zsmul, smul_eq_mul]
    exact mul_pos (by omega) (by omega)
  have hMHx : ∀ j, 0 < d ((M : ℤ) • H + x j) := by
    intro j
    rw [map_add, map_zsmul, smul_eq_mul]
    have h1 : (M : ℤ) ≤ M * d H := le_mul_of_one_le_right (by positivity) hH
    have h2 : -(d (x j)) ≤ ((d (x j)).natAbs : ℤ) := by omega
    linarith [hMj j]
  refine ⟨m + 2, Fin.cons ((N : ℝ)⁻¹) (Fin.cons (((m : ℝ) + 1 - ∑ j, f j) / N)
      fun j => f j / N),
    Fin.cons P (Fin.cons ((M : ℤ) • H) fun j => (M : ℤ) • H + x j), by omega, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
    · simpa using hNpos
    · simp only [Fin.cons_zero, Fin.cons_succ]
      exact div_pos (by linarith) hNpos
    · simp only [Fin.cons_succ]
      exact div_pos (hf0 j) hNpos
  · intro i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
    · exact hP
    · exact hMH
    · exact hMHx j
  · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hPdef, map_sub, map_sum, map_add, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℝ, hc, sub_smul, mul_smul, Finset.sum_sub_distrib, smul_add,
      Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← Finset.sum_smul]
    have e : ∑ j, (f j / N) • ι (x j) = (N : ℝ)⁻¹ • ∑ j, f j • ι (x j) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, div_eq_inv_mul]
    rw [e, ← Finset.sum_div]
    push_cast
    match_scalars <;> field_simp <;> ring

end Combination

end MMP.Flips.RelativeRhoOne

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori RelativeRhoOne

/-- **Relative Kleiman criterion in Picard number one.** Let `k` be algebraically closed of
characteristic zero and `g : Y ⟶ Z` a projective morphism of normal `k`-varieties with
`ρ(Y/Z) = 1`. An `ℝ`-Cartier divisor `D` on `Y` that is `g`-nef and not numerically `g`-trivial
is `g`-ample. -/
@[mmp "thm_mmp_threefold_real_relative_kleiman_rho_one"]
public theorem isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    (hZ : IsNormalVariety k sZ) [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [QuasiCompact sY] (g : Y ⟶ Z) (hg : IsProjective g) (hgs : g ≫ sZ = sY)
    (hρ : relativePicardNumber sY g = 1) (D : RDivisor Y) (hD : IsCartierCombination D)
    (hnef : IsRelativelyNef k sY g D) (hD₀ : ¬ IsNumericallyTrivialOver k sY g D) :
    IsRelativelyAmple g D := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : MMP.Mori.IsVariety k sY := hY.1
  haveI : MMP.Mori.IsVariety k sZ := hZ.1
  haveI : QuasiCompact g := hg.quasiCompact
  have hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sY g) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; exact Nat.cast_one.symm)
  obtain ⟨m, a, L, hL, hDL, hnefC⟩ := hnef
  set deg : ProperCurve sY → Fin m → ℤ := fun C j => (L j).degreeOn k sY C.ι C.dim_le (hL j)
  have hIR : ∀ C : ProperCurve sY, IsRIntersectionNumber k sY D a L C (∑ j, a j * deg C j) :=
    fun C => isRIntersectionNumber_sum_degreeOn D a L hL hDL C
  have hnn : ∀ C : ProperCurve sY, C.IsContractedBy g → 0 ≤ ∑ j, a j * deg C j :=
    fun C hC => hnefC C hC _ (hIR C)
  -- a contracted curve on which `D` is positive
  obtain ⟨C₀, hC₀, hpos⟩ : ∃ C : ProperCurve sY, C.IsContractedBy g ∧
      0 < ∑ j, a j * (deg C j : ℝ) := by
    by_contra hcon
    push Not at hcon
    refine hD₀ ⟨hD, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, ?_⟩
    intro C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂
    have hwd := (IsRIntersectionNumber.eq_and_linear k sY C).1
    have h0 : IsRIntersectionNumber k sY (0 : RDivisor Y) (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 C 0 :=
      ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩
    rw [hwd D r₁ L₁ a L x₁ _ h₁ (hIR C), hwd 0 r₂ L₂ _ _ x₂ 0 h₂ h0]
    exact le_antisymm (hcon C hC) (hnn C hC)
  -- Cartier divisors of positive degree on `C₀` are `g`-ample
  choose E hEiso hEdeg using fun j => exists_cartierDivisor_iso sY (L j) (hL j)
  set δ₀ : KCartierDivisor ℝ Y := ∑ j, a j • KCartierDivisor.ofCartier ℝ (E j) with hδ₀def
  have hδ₀ : ∀ C : ProperCurve sY,
      (C.cycle ℝ).intersectionNumber δ₀ = ∑ j, a j * (deg C j : ℝ) := by
    intro C
    simp only [hδ₀def, OneCycle.intersectionNumber, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := hEdeg j C
    simp only [OneCycle.intersectionNumber] at h
    rw [h]
  have hamp : ∀ (P : Divisor Y) (hP : P.IsCartier),
      0 < P.degreeOn k sY C₀.ι C₀.dim_le hP → IsRelativelyAmpleCartier g P := by
    intro P hP hPpos
    obtain ⟨F, ⟨e⟩, hF⟩ := exists_cartierDivisor_iso sY P hP
    refine isRelativelyAmpleCartier_of_iso hP e ?_
    refine (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sZ sY g hg
      hgs F).2 ?_
    exact intersectionNumber_pos_of_mem_relativeClosedConeOfCurves sY g hfin δ₀
      (fun C hC => (hδ₀ C).symm ▸ hnn C hC) hC₀ (by rw [hδ₀]; exact hpos) _
      (by rw [hF]; exact_mod_cast hPpos)
  -- write `D` as a positive combination of Cartier divisors of positive degree on `C₀`
  obtain ⟨n, r, y, hn, hr, hy, heq⟩ := exists_sum_smul_eq_of_pos (degreeHom C₀)
    (Divisor.toRDivisor.comp (Divisor.cartierSubgroup (X := Y)).subtype) a
    (fun j => ⟨L j, hL j⟩) hpos
  exact ⟨n, r, fun i => (y i : Divisor Y), hn, hr, fun i => hamp _ (y i).2 (hy i),
    hDL.trans heq⟩

end MMP.Flips

end
