module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection

section

/-!
# Basic properties of relative ampleness

Let `f : Y ⟶ X` be a proper morphism of normal varieties over an algebraically closed field of
characteristic zero. Write `N₁(Y/X)` for the real classes of curves contracted by `f` and
`NE̅(Y/X)` for their closed cone; a Cartier divisor `M` defines the linear form `z ↦ (z · M)` on
`N₁(Y/X)`, and a presentation `∑ⱼ rⱼ Mⱼ` of an `ℝ`-Cartier divisor the form `∑ⱼ rⱼ (z · Mⱼ)`,
which depends only on the divisor.

* (a) A projective `f` has an `f`-ample invertible sheaf (EGA II 4.6); on the integral normal `Y`
  it is `𝒪_Y(L)` for the divisor `L` of a local frame.
* (b) `L + f^*N` is `f`-ample by the pull-back twist; `m L` is `f`-ample since its form is
  `m` times that of `L`, by the relative Kleiman criterion (`f` is projective by (d)).
* (c) An `f`-ample line bundle has positive degree on a contracted curve, and `L · C` is that
  degree, whichever normalization of `C` computes it.
* (d) A proper morphism to a Noetherian scheme with an `f`-ample invertible sheaf is projective.
* (e) If `L = ∑ rⱼ Lⱼ` with `rⱼ > 0` and `Lⱼ` `f`-ample, the form of `L` is positive on
  `NE̅(Y/X) ∖ 0`, so `L` is `f`-ample by the relative Kleiman criterion.
* (f) If `D = ∑ sᵢ Mᵢ` is numerically equivalent over `X` to `A = ∑ rⱼ Lⱼ` `f`-ample, the forms
  of `D` and `A` agree. With `H = L₀`, ampleness is open in the directions `Mᵢ`, which bounds
  `|(z · Mᵢ)| ≤ (2/δ) (z · H)` on `NE̅(Y/X)`; writing `N sᵢ = cᵢ + tᵢ` with `cᵢ ∈ ℤ` and
  `0 < tᵢ ≤ 1`, the identity `N D = (∑ cᵢ Mᵢ - κ H) + κ (H + ∑ (tᵢ/κ) Mᵢ)` presents `D` as a
  positive combination of an `f`-ample Cartier divisor (Kleiman) and an `f`-ample `ℝ`-divisor.

## Main results

* `MMP.Mori.exists_isCartier_divisorialSheaf_iso`: an invertible module on an integral,
  locally Noetherian, normal, quasi-compact scheme is `𝒪(D)` for a Cartier divisor `D`.
* `MMP.Flips.IsRelativelyAmpleCartier.isRelativelyAmple`,
  `MMP.Flips.isRelativelyAmpleCartier_of_isRelativelyAmple`: an `f`-ample Cartier divisor (ample
  over every affine open of `X`) is the same as one ample over an affine neighbourhood of every
  point, for `f` quasi-compact.
* `MMP.Flips.relativelyAmple_basics`: the six properties (a)–(f).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.13.4, 2.16.3
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.44
* [A. Grothendieck, *Éléments de géométrie algébrique II*][EGA2], 4.6
-/

universe u

namespace MMP.Mori

open AlgebraicGeometry CategoryTheory

/-- **An invertible module is `𝒪(D)` for a Cartier divisor.** On an integral, locally
Noetherian, normal, quasi-compact scheme `Y`, every invertible `𝒪_Y`-module `L` is isomorphic to
`𝒪_Y(D)` for some Cartier divisor `D`. -/
public theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    Y.isLocalRing
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := ha, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

end MMP.Mori

namespace MMP.Flips

open AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- An `f`-ample Cartier divisor is ample over an affine neighbourhood of every point. -/
public theorem IsRelativelyAmpleCartier.isRelativelyAmple {f : Y ⟶ X} {W : Divisor Y}
    (hW : IsRelativelyAmpleCartier f W) : W.IsRelativelyAmple f hW.1 := by
  obtain ⟨hWc, hamp⟩ := hW
  have := hWc.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, hamp V hV⟩

/-- A Cartier divisor ample over an affine neighbourhood of every point is `f`-ample. -/
public theorem isRelativelyAmpleCartier_of_isRelativelyAmple {f : Y ⟶ X} [QuasiCompact f]
    {W : Divisor Y} (hW : W.IsCartier) (h : W.IsRelativelyAmple f hW) :
    IsRelativelyAmpleCartier f W := by
  have := hW.isInvertibleModule_divisorialSheaf
  exact ⟨hW, fun U hU =>
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance h).2 U hU⟩

end MMP.Flips

namespace MMP.Flips.RelativeAmpleBasics

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Normalization

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
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
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
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

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) := {}
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
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
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

end Normalization

section Classes

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)

/-- Linear forms on `N₁(Y/X)` which agree on the classes of the contracted curves are equal. -/
private theorem linearMap_ext_relativeClass
    {φ ψ : RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ}
    (h : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy f),
      φ (C.relativeClass f hC) = ψ (C.relativeClass f hC)) : φ = ψ := by
  have hsp : relativeOneCycles sY f = Submodule.span ℝ
      ((fun C => Finsupp.single C (1 : ℝ)) '' {C : ProperCurve sY | C.IsContractedBy f}) := by
    rw [relativeOneCycles, Finsupp.supported_eq_span_single]
  have key : ∀ (x : OneCycle ℝ sY) (hx : x ∈ Submodule.span ℝ
      ((fun C => Finsupp.single C (1 : ℝ)) '' {C : ProperCurve sY | C.IsContractedBy f})),
      φ (relativeNumericalClass sY f ⟨x, hsp ▸ hx⟩) =
        ψ (relativeNumericalClass sY f ⟨x, hsp ▸ hx⟩) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨C, hC, rfl⟩ := hx
      exact h C hC
    | zero =>
      have : (⟨0, hsp ▸ Submodule.zero_mem _⟩ : relativeOneCycles sY f) = 0 := rfl
      rw [this, map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      have : (⟨x + y, hsp ▸ Submodule.add_mem _ hx hy⟩ : relativeOneCycles sY f) =
          ⟨x, hsp ▸ hx⟩ + ⟨y, hsp ▸ hy⟩ := rfl
      rw [this, map_add, map_add, map_add, ihx, ihy]
    | smul c x hx ih =>
      have : (⟨c • x, hsp ▸ Submodule.smul_mem _ c hx⟩ : relativeOneCycles sY f) =
          c • ⟨x, hsp ▸ hx⟩ := rfl
      rw [this, map_smul, map_smul, map_smul, ih]
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  obtain ⟨Z, hZ⟩ := Z
  exact key Z (hsp ▸ hZ)

variable [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The linear form `z ↦ (z · M)` on `N₁(Y/X)` of a Cartier divisor `M`, through `𝒪_Y(M)`. -/
private noncomputable def degFun (M : Divisor Y) (hM : M.IsCartier) :
    RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hM.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sY f M.divisorialSheaf

/-- On the class of a contracted curve `C`, the form of `M` is `deg_C 𝒪_Y(M)`. -/
private theorem degFun_relativeClass (M : Divisor Y) (hM : M.IsCartier) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) :
    degFun sY f M hM (C.relativeClass f hC) = (M.degreeOn k sY C.ι C.dim_le hM : ℝ) := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hM.isInvertibleModule_divisorialSheaf
  exact OneCycle.degree_cycle ℝ _ C

/-- The linear form `z ↦ (z · ∑ⱼ rⱼ Lⱼ)` of a presentation. -/
private noncomputable def presFun {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) : RelativeNumericalCurveClasses sY f →ₗ[ℝ] ℝ :=
  ∑ j, r j • degFun sY f (L j) (hL j)

/-- On the class of a contracted curve `C`, the form of `∑ⱼ rⱼ Lⱼ` is `∑ⱼ rⱼ deg_C 𝒪_Y(Lⱼ)`. -/
private theorem presFun_relativeClass {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (C : ProperCurve sY) (hC : C.IsContractedBy f) :
    presFun sY f r L hL (C.relativeClass f hC) =
      ∑ j, r j * ((L j).degreeOn k sY C.ι C.dim_le (hL j) : ℝ) := by
  simp [presFun, degFun_relativeClass]

/-- Two presentations of the same `ℝ`-divisor give the same linear form on `N₁(Y/X)`. -/
private theorem presFun_eq_of_eq {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor Y)
    (hL' : ∀ j, (L' j).IsCartier)
    (h : ∑ j, r j • Divisor.toRDivisor (L j) = ∑ j, r' j • Divisor.toRDivisor (L' j)) :
    presFun sY f r L hL = presFun sY f r' L' hL' := by
  refine linearMap_ext_relativeClass sY f fun C hC => ?_
  rw [presFun_relativeClass, presFun_relativeClass]
  exact (IsRIntersectionNumber.eq_and_linear k sY C).1 _ r L r' L' _ _
    (isRIntersectionNumber_sum_degreeOn _ r L hL rfl C)
    (isRIntersectionNumber_sum_degreeOn _ r' L' hL' h C)

end Classes

section Ample

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- If `𝒪_Y(W) ≅ 𝒪_Y(E)` and `W` is `f`-ample, then `𝒪_Y(E)` is `f`-ample. -/
private theorem isRelativelyAmple_sheaf_of_iso {f : Y ⟶ X} {W : Divisor Y}
    (hW : IsRelativelyAmpleCartier f W) {E : Y.CartierDivisor}
    (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) :
    MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf E) := by
  have h := hW.isRelativelyAmple
  have := hW.1.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).mp
      hamp⟩

/-- If `𝒪_Y(W) ≅ 𝒪_Y(E)` and `𝒪_Y(E)` is `f`-ample, the Cartier divisor `W` is `f`-ample. -/
private theorem isRelativelyAmpleCartier_of_iso {f : Y ⟶ X} [QuasiCompact f] {D : Divisor Y}
    (hD : D.IsCartier) {E : Y.CartierDivisor}
    (e : D.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E)
    (h : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf E)) :
    IsRelativelyAmpleCartier f D := by
  have := hD.isInvertibleModule_divisorialSheaf
  refine isRelativelyAmpleCartier_of_isRelativelyAmple hD fun y => ?_
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  exact ⟨V, hV, hyV, (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso
      e.symm)).mp hamp⟩

end Ample

section Kleiman

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)
  [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

/-- A Cartier divisor `W` on an integral `Y` has `𝒪_Y(W) ≅ 𝒪_Y(E)` for a Cartier divisor `E`,
whose linear form on `N₁(Y/X)` is that of `W`. -/
private theorem exists_cartierDivisor_degFun [IsIntegral Y] (W : Divisor Y) (hW : W.IsCartier) :
    ∃ E : Y.CartierDivisor,
      Nonempty (W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf E) ∧
      RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
        degFun sY f W hW := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hW.isInvertibleModule_divisorialSheaf
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf W.divisorialSheaf
  refine ⟨E, ⟨e⟩, linearMap_ext_relativeClass sY f fun C hC => ?_⟩
  rw [degFun_relativeClass]
  change (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) = _
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
  exact_mod_cast (degreeOn_eq_of_iso k sY C.ι C.dim_le e).symm

variable [CompactSpace Y] [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sY]
  (hfp : IsProjective f) (hfs : f ≫ sX = sY)

include hfp hfs in
/-- An `f`-ample Cartier divisor is positive on `NE̅(Y/X) ∖ 0`. -/
private theorem degFun_pos_of_isRelativelyAmpleCartier {W : Divisor Y}
    (hW : IsRelativelyAmpleCartier f W) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < degFun sY f W hW.1 z := by
  have : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  obtain ⟨E, ⟨e⟩, hE⟩ := exists_cartierDivisor_degFun sY f W hW.1
  have h := (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sX sY f
    hfp hfs E).mp (isRelativelyAmple_sheaf_of_iso hW e)
  intro z hz hz0
  rw [← hE]
  exact h z hz hz0

include hfp hfs in
/-- The relative Kleiman criterion for a Cartier divisor of `Y`. -/
private theorem isRelativelyAmpleCartier_of_degFun_pos {W : Divisor Y} (hW : W.IsCartier)
    (h : ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < degFun sY f W hW z) :
    IsRelativelyAmpleCartier f W := by
  have : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety k sY).toIsIntegral
  have : IsProper f := hfp.isProper
  obtain ⟨E, ⟨e⟩, hE⟩ := exists_cartierDivisor_degFun sY f W hW
  refine isRelativelyAmpleCartier_of_iso hW e
    ((isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos sX sY f
      hfp hfs E).mpr fun z hz hz0 => ?_)
  rw [hE]
  exact h z hz hz0

end Kleiman

section Clauses

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
  (sX : X ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  [QuasiCompact sY] (f : Y ⟶ X) [IsProper f]

/-- (d) A proper morphism with an `f`-ample Cartier divisor is projective. -/
private theorem isProjective_of_exists_isRelativelyAmpleCartier (hX : IsNormalVariety k sX)
    (h : ∃ L : Divisor Y, IsRelativelyAmpleCartier f L) : IsProjective f := by
  obtain ⟨L, hL⟩ := h
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have := hL.1.isInvertibleModule_divisorialSheaf
  exact MMP.isProjective_of_isProper_of_isRelativelyAmple f _
    hL.isRelativelyAmple

omit [QuasiCompact sY] [IsProper f] in
/-- (a) A projective morphism of integral `Y` has an `f`-ample Cartier divisor. -/
private theorem exists_isRelativelyAmpleCartier_of_isProjective (hY : IsNormalVariety k sY)
    (hfp : IsProjective f) : ∃ L : Divisor Y, IsRelativelyAmpleCartier f L := by
  have : IsIntegral Y := hY.1.toIsIntegral
  obtain ⟨⟨L, hL, hrel, -⟩, -⟩ := MMP.Foundations.IsProjective.exists_isRelativelyAmple hfp
  obtain ⟨D, hD, ⟨e⟩⟩ := exists_isCartier_divisorialSheaf_iso L
  have := hD.isInvertibleModule_divisorialSheaf
  refine ⟨D, hD, fun U hU => ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ U).ι.toLRSHom.toShHom).mapIso
      e.symm)).mp (hrel.2 U hU)

omit [IsProper f] in
/-- (c) An `f`-ample Cartier divisor has positive degree on every contracted curve. -/
private theorem pos_of_isCartierIntersectionNumber {L : Divisor Y}
    (hL : IsRelativelyAmpleCartier f L) (hLc : L.IsCartier) (C : ProperCurve sY)
    (hC : C.IsContractedBy f) (d : ℤ) (hd : IsCartierIntersectionNumber k sY C L hLc d) :
    0 < d := by
  rw [eq_degreeOn_of_isCartierIntersectionNumber hd]
  have := hLc.isInvertibleModule_divisorialSheaf
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _
    hL.isRelativelyAmple C hC

end Clauses

section RealClauses

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- A sum of two `f`-ample `ℝ`-divisors is `f`-ample. -/
private theorem isRelativelyAmple_add {f : Y ⟶ X} {A A' : RDivisor Y}
    (hA : IsRelativelyAmple f A) (hA' : IsRelativelyAmple f A') : IsRelativelyAmple f (A + A') := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  obtain ⟨m', r', L', -, hr', hL', rfl⟩ := hA'
  refine ⟨m + m', Fin.append r r', Fin.append L L', by omega, fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hr j
    · simpa using hr' j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [Fin.sum_univ_add]; simp

/-- A positive multiple of an `f`-ample `ℝ`-divisor is `f`-ample. -/
private theorem isRelativelyAmple_smul {f : Y ⟶ X} {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) {c : ℝ} (hc : 0 < c) : IsRelativelyAmple f (c • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := hA
  exact ⟨m, fun j => c * r j, L, hm, fun j => mul_pos hc (hr j), hL, by
    rw [Finset.smul_sum]; simp [smul_smul]⟩

/-- An `f`-ample Cartier divisor is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor {f : Y ⟶ X} {H : Divisor Y}
    (hH : IsRelativelyAmpleCartier f H) :
    IsRelativelyAmple f (Divisor.toRDivisor H) :=
  ⟨1, fun _ => 1, fun _ => H, le_rfl, fun _ => one_pos, fun _ => hH, by simp⟩

variable {k : Type} [Field k] (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY] (f : Y ⟶ X)
  [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
  [AlgebraicGeometry.IsVariety k sY] (hfp : IsProjective f) (hfs : f ≫ sX = sY)

include hfp hfs in
/-- Every presentation of an `f`-ample `ℝ`-divisor is positive on `NE̅(Y/X) ∖ 0`. -/
private theorem presFun_pos_of_isRelativelyAmple {A : RDivisor Y} (hA : IsRelativelyAmple f A)
    {m : ℕ} (a : Fin m → ℝ) (M : Fin m → Divisor Y) (hM : ∀ j, (M j).IsCartier)
    (hAeq : A = ∑ j, a j • Divisor.toRDivisor (M j)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, z ≠ 0 → 0 < presFun sY f a M hM z := by
  obtain ⟨n, r, L, hn, hr, hL, rfl⟩ := hA
  rw [presFun_eq_of_eq sY f a M hM r L (fun j => (hL j).1) hAeq.symm]
  intro z hz hz0
  simp only [presFun, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun j _ => mul_pos (hr j)
    (degFun_pos_of_isRelativelyAmpleCartier sY f sX hfp hfs (hL j) z hz hz0))
    Finset.univ_nonempty

include hfp hfs in
/-- Every presentation of an `f`-ample `ℝ`-divisor is nonnegative on `NE̅(Y/X)`. -/
private theorem presFun_nonneg_of_isRelativelyAmple {A : RDivisor Y}
    (hA : IsRelativelyAmple f A) {m : ℕ} (a : Fin m → ℝ) (M : Fin m → Divisor Y)
    (hM : ∀ j, (M j).IsCartier) (hAeq : A = ∑ j, a j • Divisor.toRDivisor (M j)) :
    ∀ z ∈ relativeClosedConeOfCurves sY f, 0 ≤ presFun sY f a M hM z := by
  intro z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · exact (presFun_pos_of_isRelativelyAmple sY f sX hfp hfs hA a M hM hAeq z hz hz0).le

include hfp hfs in
/-- (b) Positive multiples of an `f`-ample Cartier divisor are `f`-ample. -/
private theorem isRelativelyAmpleCartier_zsmul {L : Divisor Y} (hL : IsRelativelyAmpleCartier f L)
    (m : ℤ) (hm : 0 < m) : IsRelativelyAmpleCartier f (m • L) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hm.le).symm⟩
  rw [natCast_zsmul]
  have hn : (0 : ℝ) < n := by exact_mod_cast hm
  refine isRelativelyAmpleCartier_of_degFun_pos sY f sX hfp hfs (hL.1.nsmul n) fun z hz hz0 => ?_
  have h : degFun sY f (n • L) (hL.1.nsmul n) = (n : ℝ) • degFun sY f L hL.1 :=
    linearMap_ext_relativeClass sY f fun C hC => by
      rw [LinearMap.smul_apply, degFun_relativeClass, degFun_relativeClass,
        Divisor.degreeOn_nsmul' k sY C.ι C.dim_le L hL.1 n, smul_eq_mul]
      push_cast; ring
  rw [h, LinearMap.smul_apply, smul_eq_mul]
  exact mul_pos hn (degFun_pos_of_isRelativelyAmpleCartier sY f sX hfp hfs hL z hz hz0)

include hfp hfs in
/-- (e) A Cartier divisor which is `f`-ample as an `ℝ`-divisor is `f`-ample. -/
private theorem isRelativelyAmpleCartier_of_isRelativelyAmple_toRDivisor {L : Divisor Y}
    (hLc : L.IsCartier) (hA : IsRelativelyAmple f (Divisor.toRDivisor L)) :
    IsRelativelyAmpleCartier f L := by
  refine isRelativelyAmpleCartier_of_degFun_pos sY f sX hfp hfs hLc fun z hz hz0 => ?_
  have h := presFun_pos_of_isRelativelyAmple sY f sX hfp hfs hA (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => L) (fun _ => hLc) (by simp) z hz hz0
  simpa [presFun] using h

end RealClauses

section Arithmetic

/-- If `h ± (δ/2) m ≥ 0` then `|m| ≤ (2/δ) h`. -/
private theorem abs_le_of_nonneg_add_half_smul {δ h m : ℝ} (hδ : 0 < δ)
    (h₁ : 0 ≤ h + δ / 2 * m) (h₂ : 0 ≤ h + -(δ / 2) * m) : |m| ≤ 2 / δ * h := by
  have e : 2 / δ * (δ / 2) = 1 := by field_simp
  have hδ' : 0 ≤ 2 / δ := by positivity
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hδ' h₁, mul_nonneg hδ' h₂]

/-- Every real number is an integer plus a remainder in `(0, 1]`. -/
private theorem exists_int_sub_mem_Ioc (x : ℝ) : ∃ c : ℤ, 0 < x - c ∧ x - c ≤ 1 :=
  ⟨⌈x⌉ - 1, by push_cast; linarith [Int.ceil_lt_add_one x], by push_cast; linarith [Int.le_ceil x]⟩

/-- The rearrangement `N ∑ sᵢ vᵢ = (∑ cᵢ vᵢ - κ h) + κ (h + ∑ (tᵢ/κ) vᵢ)` when
`cᵢ = N sᵢ - tᵢ`. -/
private theorem sum_smul_eq_smul_add_smul {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι] {s c t : ι → ℝ} (v : ι → V) (h : V) {N κ : ℝ} (hN : N ≠ 0) (hκ : κ ≠ 0)
    (hct : ∀ i, c i = N * s i - t i) :
    ∑ i, s i • v i =
      (1 / N) • (∑ i, c i • v i - κ • h) + (κ / N) • (h + ∑ i, (t i / κ) • v i) := by
  have hs : ∀ i, s i = 1 / N * c i + κ / N * (t i / κ) := fun i => by
    rw [hct]; field_simp; ring
  simp only [smul_sub, smul_add, Finset.smul_sum, smul_smul]
  rw [show 1 / N * κ = κ / N by ring]
  conv_lhs => simp only [hs, add_smul, Finset.sum_add_distrib]
  abel

/-- The positivity estimate behind (f): if `r h ≤ φ`, `|mᵢ| ≤ B h`, `0 < tᵢ ≤ 1` and
`κ + p B < N r`, then `N φ - ∑ tᵢ mᵢ - κ h > 0` for `h > 0`. -/
private theorem sub_sum_mul_sub_pos {p : ℕ} {N r κ B φ h : ℝ} {t m : Fin p → ℝ} (hN : 0 ≤ N)
    (hNr : κ + p * B < N * r) (hh : 0 < h) (hlow : r * h ≤ φ) (hm : ∀ i, |m i| ≤ B * h)
    (ht0 : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1) : 0 < N * φ - ∑ i, t i * m i - κ * h := by
  have hb : ∑ i, t i * m i ≤ p * (B * h) := by
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      show t i * m i ≤ B * h by
        nlinarith [le_abs_self (m i), hm i, abs_nonneg (m i), ht0 i, ht1 i]
  nlinarith [mul_le_mul_of_nonneg_left hlow hN, mul_pos (sub_pos.2 hNr) hh]

end Arithmetic

section NumericalInvariance

variable {k : Type} [Field k] {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
  [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]

/-- `M ↦ deg_C 𝒪_Y(M)` as an additive map on Cartier divisors. -/
private noncomputable def degreeHom (C : ProperCurve sY) :
    Divisor.cartierSubgroup (X := Y) →+ ℤ where
  toFun L := (L : Divisor Y).degreeOn k sY C.ι C.dim_le L.2
  map_zero' := Divisor.degreeOn_zero' k sY C.ι C.dim_le
  map_add' L₁ L₂ := Divisor.degreeOn_add k sY C.ι C.dim_le L₁.1 L₂.1 L₁.2 L₂.2

/-- The Cartier divisor `∑ cᵢ Mᵢ - κ H` as an element of the Cartier subgroup. -/
private noncomputable def cartierComb {p : ℕ} (c : Fin p → ℤ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (κ : ℤ) (H : Divisor Y) (hH : H.IsCartier) :
    Divisor.cartierSubgroup (X := Y) :=
  ∑ i, c i • (⟨M i, hM i⟩ : Divisor.cartierSubgroup (X := Y)) - κ • ⟨H, hH⟩

omit [CompactSpace Y] in
private theorem coe_cartierComb {p : ℕ} (c : Fin p → ℤ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (κ : ℤ) (H : Divisor Y) (hH : H.IsCartier) :
    (cartierComb c M hM κ H hH : Divisor Y) = ∑ i, c i • M i - κ • H := by
  simp [cartierComb]

variable (f : Y ⟶ X)

omit [CompactSpace Y] in
/-- The linear form of `∑ cᵢ Mᵢ - κ H` is `∑ cᵢ (· Mᵢ) - κ (· H)`. -/
private theorem degFun_cartierComb {p : ℕ} (c : Fin p → ℤ) (M : Fin p → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (κ : ℤ) (H : Divisor Y) (hH : H.IsCartier) :
    degFun sY f _ (cartierComb c M hM κ H hH).2 =
      ∑ i, (c i : ℝ) • degFun sY f (M i) (hM i) - (κ : ℝ) • degFun sY f H hH :=
  linearMap_ext_relativeClass sY f fun C hC => by
    have e : (cartierComb c M hM κ H hH : Divisor Y).degreeOn k sY C.ι C.dim_le
        (cartierComb c M hM κ H hH).2 = degreeHom sY C (cartierComb c M hM κ H hH) := rfl
    refine (degFun_relativeClass sY f _ (cartierComb c M hM κ H hH).2 C hC).trans ?_
    rw [e]
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      degFun_relativeClass, cartierComb, map_sub, map_sum, map_zsmul]
    push_cast
    rfl

variable [IsAlgClosed k] [CharZero k] (sX : X ⟶ Spec (.of k))
  [AlgebraicGeometry.IsVariety k sX] [AlgebraicGeometry.IsVariety k sY]
  (hfp : IsProjective f) (hfs : f ≫ sX = sY)

include hfp hfs in
/-- If `H + ∑ tᵢ Mᵢ` is `f`-ample whenever all `|tᵢ| < δ`, then on `NE̅(Y/X)` every `Mᵢ` is
bounded by `H`: `|(z · Mᵢ)| ≤ (2/δ) (z · H)`. -/
private theorem abs_degFun_le_of_isRelativelyAmple_add {p : ℕ} {H : Divisor Y}
    (hH : H.IsCartier) {M : Fin p → Divisor Y} (hM : ∀ i, (M i).IsCartier) {δ : ℝ} (hδ : 0 < δ)
    (hpert : ∀ t : Fin p → ℝ, (∀ i, |t i| < δ) →
      IsRelativelyAmple f (Divisor.toRDivisor H + ∑ i, t i • Divisor.toRDivisor (M i)))
    (i : Fin p) : ∀ z ∈ relativeClosedConeOfCurves sY f,
      |degFun sY f (M i) (hM i) z| ≤ 2 / δ * degFun sY f H hH z := by
  have hside : ∀ σ : ℝ, |σ| < δ → ∀ z ∈ relativeClosedConeOfCurves sY f,
      0 ≤ degFun sY f H hH z + σ * degFun sY f (M i) (hM i) z := by
    intro σ hσ z hz
    have h := hpert (Pi.single i σ) fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hσ
      · simpa [Pi.single_apply, hj] using hδ
    have := presFun_nonneg_of_isRelativelyAmple sY f sX hfp hfs h ![1, σ] ![H, M i]
      (fun j => by fin_cases j; exacts [hH, hM i])
      (by simp [Fin.sum_univ_two, Pi.single_apply]) z hz
    simpa [presFun, Fin.sum_univ_two] using this
  intro z hz
  exact abs_le_of_nonneg_add_half_smul hδ
    (hside _ (by rw [abs_of_pos (by positivity)]; linarith) z hz)
    (hside _ (by rw [abs_neg, abs_of_pos (by positivity)]; linarith) z hz)

include hfp hfs in
/-- (f) An `ℝ`-Cartier divisor numerically equivalent over `X` to an `f`-ample one is `f`-ample.
Writing `D = ∑ᵢ sᵢ Mᵢ`, `A = ∑ⱼ rⱼ Lⱼ` and `H = L₀`, the forms of `D` and `A` agree on
`N₁(Y/X)`; perturbing `H` in the directions `Mᵢ` bounds `|Mᵢ| ≤ (2/δ) H` on `NE̅(Y/X)`, and with
`N sᵢ = cᵢ + tᵢ` (`cᵢ ∈ ℤ`, `0 < tᵢ ≤ 1`),
`N D = (∑ cᵢ Mᵢ - κ H) + κ (H + ∑ (tᵢ/κ) Mᵢ)` exhibits `D` as a positive combination of an
`f`-ample Cartier divisor (by the relative Kleiman criterion) and an `f`-ample `ℝ`-divisor. -/
private theorem isRelativelyAmple_of_isNumericallyEquivalentOver [IsLocallyNoetherian X]
    [IsNormal X] [IsProper f] (hY : IsNormalVariety k sY) (hX : IsNormalVariety k sX)
    {D A : RDivisor Y} (hDA : IsNumericallyEquivalentOver k sY f D A)
    (hA : IsRelativelyAmple f A) : IsRelativelyAmple f D := by
  obtain ⟨⟨p, s, M, hM, hD⟩, -, hnum⟩ := hDA
  replace hD : D = ∑ i, s i • Divisor.toRDivisor (M i) := hD
  obtain ⟨m, r, L, hm, hr, hL, hAeq⟩ := hA
  set i₀ : Fin m := ⟨0, hm⟩
  set H := L i₀
  have hHa : IsRelativelyAmpleCartier f H := hL i₀
  -- the forms of `D` and `A` agree, so `D ≥ r₀ H` on `NE̅(Y/X)`
  have hφ : presFun sY f s M hM = presFun sY f r L (fun j => (hL j).1) :=
    linearMap_ext_relativeClass sY f fun C hC => by
      rw [presFun_relativeClass, presFun_relativeClass]
      exact hnum C hC p s M _ m r L _ (isRIntersectionNumber_sum_degreeOn D s M hM hD C)
        (isRIntersectionNumber_sum_degreeOn A r L (fun j => (hL j).1) hAeq C)
  have hlow : ∀ z ∈ relativeClosedConeOfCurves sY f,
      r i₀ * degFun sY f H hHa.1 z ≤ presFun sY f s M hM z := fun z hz => by
    rw [hφ]
    simp only [presFun, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.single_le_sum (f := fun j => r j * degFun sY f (L j) (hL j).1 z)
      (fun j _ => mul_nonneg (hr j).le ?_) (Finset.mem_univ i₀)
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · exact (degFun_pos_of_isRelativelyAmpleCartier sY f sX hfp hfs (hL j) z hz hz0).le
  -- perturbation of `H` in the directions `Mᵢ`
  obtain ⟨δ, hδ, hpert⟩ := exists_pos_isRelativelyAmple_add_sum_smul k sY sX hY hX f hfs
    (isRelativelyAmple_toRDivisor hHa) (fun i => Divisor.toRDivisor (M i))
    (fun i => ⟨1, fun _ => 1, fun _ => M i, fun _ => hM i, by simp; rfl⟩)
  -- the integers `κ`, `N` and the splitting `N sᵢ = cᵢ + tᵢ`
  obtain ⟨κ, hκ⟩ := exists_nat_gt (1 / δ)
  have hκpos : (0 : ℝ) < κ := lt_trans (by positivity) hκ
  have hκδ : 1 < κ * δ := by rwa [div_lt_iff₀ hδ] at hκ
  obtain ⟨N, hN⟩ := exists_nat_gt ((κ + p * (2 / δ)) / r i₀)
  have hNr : κ + p * (2 / δ) < N * r i₀ := by rwa [div_lt_iff₀ (hr i₀)] at hN
  have hNpos : (0 : ℝ) < N :=
    pos_of_mul_pos_left (lt_of_le_of_lt (by positivity) hNr) (hr i₀).le
  choose c ht0 ht1 using fun i => exists_int_sub_mem_Ioc ((N : ℝ) * s i)
  -- `G = ∑ cᵢ Mᵢ - κ H` is `f`-ample by the relative Kleiman criterion
  set G := cartierComb c M hM κ H hHa.1
  have hGa : IsRelativelyAmpleCartier f G :=
    isRelativelyAmpleCartier_of_degFun_pos sY f sX hfp hfs G.2 fun z hz hz0 => by
      have hsum : ∑ i, (c i : ℝ) * degFun sY f (M i) (hM i) z = N * presFun sY f s M hM z -
          ∑ i, (N * s i - c i) * degFun sY f (M i) (hM i) z := by
        simp [sub_mul, presFun, Finset.mul_sum, mul_assoc]
      simp only [G, degFun_cartierComb, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, hsum, Int.cast_natCast]
      exact sub_sum_mul_sub_pos hNpos.le hNr
        (degFun_pos_of_isRelativelyAmpleCartier sY f sX hfp hfs hHa z hz hz0) (hlow z hz)
        (fun i => abs_degFun_le_of_isRelativelyAmple_add sY f sX hfp hfs hHa.1 hM hδ hpert i z hz)
        ht0 ht1
  -- `A' = H + ∑ (tᵢ/κ) Mᵢ` is `f`-ample, and `D = (1/N) G + (κ/N) A'`
  have hA'a := hpert (fun i => (N * s i - c i) / κ) fun i => by
    rw [abs_of_pos (div_pos (ht0 i) hκpos), div_lt_iff₀ hκpos]
    linarith [ht1 i]
  have hGR : Divisor.toRDivisor (G : Divisor Y) =
      ∑ i, (c i : ℝ) • Divisor.toRDivisor (M i) - (κ : ℝ) • Divisor.toRDivisor H := by
    rw [coe_cartierComb, map_sub, map_sum, map_zsmul]
    simp only [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]
  rw [hD, sum_smul_eq_smul_add_smul _ (Divisor.toRDivisor H) hNpos.ne' hκpos.ne'
    (c := fun i => (c i : ℝ)) (t := fun i => N * s i - c i) (fun i => by ring), ← hGR]
  exact isRelativelyAmple_add (isRelativelyAmple_smul (isRelativelyAmple_toRDivisor hGa)
    (by positivity)) (isRelativelyAmple_smul hA'a (by positivity))

end NumericalInvariance

end MMP.Flips.RelativeAmpleBasics

end

section

/-!
## The main statement

Let `k` be an algebraically closed field of characteristic zero and `f : Y ⟶ X` a proper morphism
of normal `k`-varieties. Then:

* (a) if `f` is projective, `Y` carries an `f`-ample Cartier divisor;
* (b) if `L` is an `f`-ample Cartier divisor and `N` a Cartier divisor on `X`, then `L + f^*N` is
  `f`-ample, and so is `m • L` for every integer `m > 0`;
* (c) an `f`-ample Cartier divisor has positive degree on every irreducible curve `C ⊆ Y` with
  `f(C)` a point;
* (d) if `Y` carries an `f`-ample Cartier divisor, `f` is projective;
* (e) a Cartier divisor which is `f`-ample as an `ℝ`-Cartier divisor is `f`-ample as a Cartier
  divisor;
* (f) if `f` is projective, an `ℝ`-Cartier divisor numerically equivalent over `X` to an
  `f`-ample `ℝ`-Cartier divisor is `f`-ample.

### Implementation notes

`f`-ampleness of a Cartier divisor is `MMP.Flips.IsRelativelyAmpleCartier` (the restriction of
`𝒪_Y(L)` to the preimage of every affine open of `X` is ample), and of an `ℝ`-Cartier divisor
`MMP.Flips.IsRelativelyAmple` (a positive real combination of `f`-ample Cartier divisors).
The pull-back `f^*N` of (b) is a Weil divisor `N'` on `Y` with `N.IsPullback f hN N'`
(`MMP.Mori.Divisor.IsPullback`), defined when the generic point of `Y` maps outside `Supp N`.
The intersection number `L · C` of (c) is `MMP.Flips.IsCartierIntersectionNumber`, and every
value of it is positive. Projectivity is `AlgebraicGeometry.IsProjective`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

open MMP.Flips.RelativeAmpleBasics in
/-- **Basic properties of relative ampleness.** For a proper morphism `f : Y ⟶ X` of normal
varieties over an algebraically closed field of characteristic zero:
(a) if `f` is projective there is an `f`-ample Cartier divisor;
(b) `L + f^*N` and `m • L` (`m > 0`) are `f`-ample for `L` `f`-ample and `N` Cartier on `X`;
(c) an `f`-ample `L` has `L · C > 0` on every curve `C` contracted by `f`;
(d) if there is an `f`-ample Cartier divisor, `f` is projective;
(e) a Cartier divisor that is `f`-ample as an `ℝ`-Cartier divisor is `f`-ample;
(f) if `f` is projective, an `ℝ`-Cartier divisor numerically equivalent over `X` to an `f`-ample
one is `f`-ample. -/
@[mmp "lem_mmp_foundation_fa2_full_relative_ample_basics"]
public theorem relativelyAmple_basics
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    (hX : IsNormalVariety k sX) [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [QuasiCompact sY] [IsLocallyNoetherian X] [IsNormal X]
    (f : Y ⟶ X) [IsProper f] (hf : f ≫ sX = sY) :
    -- (a)
    (IsProjective f → ∃ L : Divisor Y, IsRelativelyAmpleCartier f L) ∧
    -- (b)
    (∀ L : Divisor Y, IsRelativelyAmpleCartier f L →
      (∀ (N : Divisor X), N.IsCartier →
        ∀ (hN : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ N.supp)
          (N' : Divisor Y), N.IsPullback f hN N' → IsRelativelyAmpleCartier f (L + N')) ∧
      ∀ m : ℤ, 0 < m → IsRelativelyAmpleCartier f (m • L)) ∧
    -- (c)
    (∀ L : Divisor Y, IsRelativelyAmpleCartier f L →
      ∀ (hL : L.IsCartier) (C : ProperCurve sY), C.IsContractedBy f →
        ∀ d : ℤ, IsCartierIntersectionNumber k sY C L hL d → 0 < d) ∧
    -- (d)
    ((∃ L : Divisor Y, IsRelativelyAmpleCartier f L) → IsProjective f) ∧
    -- (e)
    (∀ L : Divisor Y, L.IsCartier → IsRelativelyAmple f (Divisor.toRDivisor L) →
      IsRelativelyAmpleCartier f L) ∧
    -- (f)
    (IsProjective f → ∀ D A : RDivisor Y, IsNumericallyEquivalentOver k sY f D A →
      IsRelativelyAmple f A → IsRelativelyAmple f D) := by
  have : AlgebraicGeometry.IsVariety k sX := hX.1
  have : AlgebraicGeometry.IsVariety k sY := hY.1
  have hd := isProjective_of_exists_isRelativelyAmpleCartier sX f hX
  refine ⟨exists_isRelativelyAmpleCartier_of_isProjective sY f hY,
    fun L hL => ⟨fun N hNc hN N' hN' => ?_,
      isRelativelyAmpleCartier_zsmul sY f sX (hd ⟨L, hL⟩) hf hL⟩,
    fun L hL hLc C hC d hdd => pos_of_isCartierIntersectionNumber sY f hL hLc C hC d hdd, hd,
    fun L hLc hA => ?_,
    fun hfp D A hDA hA => isRelativelyAmple_of_isNumericallyEquivalentOver sY f sX hfp hf hY hX
      hDA hA⟩
  · have hN'c := hN'.isCartier hNc
    exact isRelativelyAmpleCartier_of_isRelativelyAmple (hL.1.add hN'c)
      (MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback f hL.1
        hL.isRelativelyAmple hNc hN' hN'c)
  · obtain ⟨m, r, Ls, hm, -, hLs, -⟩ := id hA
    exact isRelativelyAmpleCartier_of_isRelativelyAmple_toRDivisor sY f sX
      (hd ⟨_, hLs ⟨0, hm⟩⟩) hf hLc hA

end MMP.Flips

end
