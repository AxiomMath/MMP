module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Fourfold.RealLcPositiveGap
public import MMP.AlgebraicGeometry.Singularities.RealKltPolytope
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeRhoOne

/-!
# A uniform radial neighbourhood of a nef real klt adjoint on a fourfold

Let `f : Y ⟶ Z` be a morphism of projective complex varieties, with `Y` a normal `ℚ`-factorial
fourfold with canonical divisor `K_Y`. Let `(Y, B)` be a klt pair with effective real boundary
such that `D = K_Y + B` is nef over `Z`, and suppose `a > 0` bounds from below every positive
degree `D · L` on a curve `L` contracted by `f`. Put `ε = a / (2 (a + 8))`. For every klt pair
`(Y, C)` with effective real boundary and every `0 < t < ε`, every extremal ray of the relative
closed cone of curves `NE̅(Y/Z)` on which `D_t = (1 - t) D + t (K_Y + C)` is negative is `D`-null.

A `D_t`-negative ray is `(K_Y + C)`-negative since `D` is nef over `Z`. The rational curve `L`
spanning it given by
`MMP.Fourfold.exists_pos_forall_isExtremalRay_exists_isRationalCurve_neg_eight_le` has
`(K_Y + C) · L ≥ -8`; if `D · L > 0` then `D · L ≥ a` and `D_t · L ≥ a - t (a + 8) > a / 2 > 0`,
a contradiction.

## Main results

* `MMP.Fourfold.forall_isExtremalRay_null_of_isRealKltPair_of_lt_div`.

## Implementation notes

An `ℝ`-Cartier divisor is paired with a class `u ∈ N₁(Y/Z)` through a presentation `∑ cᵢ Mᵢ` by
Cartier divisors `Mᵢ`, as `∑ cᵢ (u · 𝒪_Y(Mᵢ))` computed with
`MMP.Mori.RelativeNumericalCurveClasses.degree`; a curve `L` contracted by `f` has class
`MMP.Mori.ProperCurve.relativeClass`. The pairing does not depend on the presentation, so
negativity on a ray asks for one presentation, while the lower bound `a` and nullness are
asserted for all of them. The dimension of `Y` is the `4` of
`MMP.Mori.Divisor.IsCanonicalDivisor`. The base `Z` is a projective variety, so `f` is
projective.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

section

namespace Proof_lem_fourfold_birational_fourfold_radial_ray

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.Mori MMP.Fourfold

open MMP.Flips

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
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
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
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
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

/-! ### Pairing classes with Cartier divisors -/

section Pairing

variable {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ Z)

/-- The degree `u · 𝒪_Y(M)` of a relative class on a Cartier divisor `M`. -/
private noncomputable def pair (M : Divisor Y) (hM : M.IsCartier)
    (u : RelativeNumericalCurveClasses sY f) : ℝ :=
  haveI := hM.isInvertibleModule_divisorialSheaf
  RelativeNumericalCurveClasses.degree sY f M.divisorialSheaf u

private theorem pair_add (M : Divisor Y) (hM : M.IsCartier) (u v : RelativeNumericalCurveClasses sY f) :
    pair f M hM (u + v) = pair f M hM u + pair f M hM v := map_add _ _ _

private theorem pair_smul (M : Divisor Y) (hM : M.IsCartier) (s : ℝ) (u : RelativeNumericalCurveClasses sY f) :
    pair f M hM (s • u) = s * pair f M hM u := map_smul _ _ _

private theorem pair_congr {M M' : Divisor Y} (h : M = M') (hM : M.IsCartier)
    (hM' : M'.IsCartier) (u : RelativeNumericalCurveClasses sY f) : pair f M hM u = pair f M' hM' u := by
  subst h; rfl

variable [QuasiCompact sY] in
private theorem pair_relativeClass (M : Divisor Y) (hM : M.IsCartier) (L : ProperCurve sY)
    (hL : L.IsContractedBy f) :
    pair f M hM (L.relativeClass f hL) = (M.degreeOn ℂ sY L.ι L.dim_le hM : ℝ) := by
  simp only [pair, ProperCurve.relativeClass,
    RelativeNumericalCurveClasses.degree_relativeNumericalClass, OneCycle.degree_cycle]
  rfl

variable [QuasiCompact sY] in
/-- A nef `ℝ`-Cartier divisor over `Z`, computed from any presentation by Cartier divisors, has
nonnegative degree on every curve contracted by `f`. -/
private theorem pair_nonneg_of_isRelativelyNef {D : RDivisor Y}
    (hD : MMP.Flips.IsRelativelyNef ℂ sY f D) {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor Y)
    (hM : ∀ i, (M i).IsCartier) (hDM : D = ∑ i, c i • Divisor.toRDivisor (M i))
    (L : ProperCurve sY) (hL : L.IsContractedBy f) :
    0 ≤ ∑ i, c i * pair f (M i) (hM i) (L.relativeClass f hL) := by
  obtain ⟨m, r, L', hL', hDL', hnn⟩ := hD
  have h1 := isRIntersectionNumber_sum_degreeOn D c M hM hDM L
  have h2 := isRIntersectionNumber_sum_degreeOn D r L' hL' hDL' L
  simp only [pair_relativeClass]
  rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sY L).1 D _ _ _ _ _ _ h1 h2]
  exact hnn L hL _ h2

private theorem sum_append_mul_pair {n₁ n₂ : ℕ} (c₁ : Fin n₁ → ℝ) (M₁ : Fin n₁ → Divisor Y)
    (hM₁ : ∀ i, (M₁ i).IsCartier) (c₂ : Fin n₂ → ℝ) (M₂ : Fin n₂ → Divisor Y)
    (hM₂ : ∀ i, (M₂ i).IsCartier) (hM : ∀ i, (Fin.append M₁ M₂ i).IsCartier)
    (u : RelativeNumericalCurveClasses sY f) :
    ∑ i, Fin.append c₁ c₂ i * pair f (Fin.append M₁ M₂ i) (hM i) u =
      ∑ i, c₁ i * pair f (M₁ i) (hM₁ i) u + ∑ i, c₂ i * pair f (M₂ i) (hM₂ i) u := by
  rw [Fin.sum_univ_add]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · rw [Fin.append_left, pair_congr f (Fin.append_left M₁ M₂ i) _ (hM₁ i)]
  · rw [Fin.append_right, pair_congr f (Fin.append_right M₁ M₂ i) _ (hM₂ i)]

end Pairing

/-! ### Divisors supported on a finite family of primes -/

section Support

variable {Y : Scheme.{0}} {r : ℕ}

/-- A divisor supported on the injective family `p` is the sum of its coefficients along `p`. -/
private theorem eq_sum_single_coeff {R : Type*} [AddCommMonoid R]
    {p : Fin r → MMP.Mori.PrimeDivisor Y} (hp : Function.Injective p)
    {D : DivisorWithCoeffs R Y}
    (hD : ∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) :
    D = ∑ i, Finsupp.single (p i) (D.coeff (p i)) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum_of_support_subset D (s := Finset.univ.image p) (g := Finsupp.single)
    (fun P hP => by simpa using hD P (by simpa [DivisorWithCoeffs.coeff_apply] using hP))
    (fun _ _ => Finsupp.single_zero _), Finset.sum_image fun i _ j _ h => hp h]
  rfl

/-- Casting the coefficients of `∑ᵢ vᵢ pᵢ` from `ℚ` to `ℝ`. -/
private theorem toRDivisor_sum_single (p : Fin r → MMP.Mori.PrimeDivisor Y) (v : Fin r → ℚ) :
    QDivisor.toRDivisor (∑ i, Finsupp.single (p i) (v i)) =
      ∑ i, Finsupp.single (p i) (v i : ℝ) := by
  classical
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => DivisorWithCoeffs.ext' fun P => ?_
  rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/-- The coefficients of `∑ᵢ vᵢ pᵢ` are nonnegative when the `vᵢ` are. -/
private theorem coeff_sum_single_nonneg (p : Fin r → MMP.Mori.PrimeDivisor Y) {v : Fin r → ℚ}
    (hv : ∀ i, 0 ≤ v i) (P : MMP.Mori.PrimeDivisor Y) :
    0 ≤ (∑ i, Finsupp.single (p i) (v i) : QDivisor Y).coeff P := by
  classical
  rw [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  exact Finset.sum_nonneg fun i _ => by
    rw [Finsupp.single_apply]; split_ifs <;> simp [hv i]

end Support

/-! ### A rational lc polytope through two klt boundaries -/

section Polytope

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)}

/-- Two effective real klt boundaries on a projective `ℚ`-factorial complex variety lie in the
convex hull of finitely many effective rational lc boundaries: the union of the vertex sets of
rational klt polytopes around each of them, on the primes carrying either. -/
private theorem exists_lcPolytope (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hYq : IsQFactorial sY) {B C : RDivisor Y} (hB0 : ∀ P, 0 ≤ B.coeff P)
    (hB : IsRealKltPair sY B) (hC0 : ∀ P, 0 ≤ C.coeff P) (hC : IsRealKltPair sY C) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (V : ι → QDivisor Y),
      (∀ i P, 0 ≤ (V i).coeff P) ∧ (∀ i, MMP.Intersection.IsLogCanonicalPair sY (V i)) ∧
      B ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)) ∧
      C ∈ convexHull ℝ (Set.range fun i => QDivisor.toRDivisor (V i)) := by
  classical
  -- a finite family of primes carrying `B` and `C`
  set s : Finset (MMP.Mori.PrimeDivisor Y) := B.support ∪ C.support
  set p : Fin s.card → MMP.Mori.PrimeDivisor Y := fun i => (s.equivFin.symm i).1 with hpdef
  have hp : Function.Injective p := Subtype.val_injective.comp s.equivFin.symm.injective
  have hsp : ∀ P ∈ s, P ∈ Set.range p := fun P hP => ⟨s.equivFin ⟨P, hP⟩, by simp [hpdef]⟩
  have hBp : ∀ P, B.coeff P ≠ 0 → P ∈ Set.range p := fun P hP => hsp P
    (Finset.mem_union_left _ (by simpa [DivisorWithCoeffs.coeff_apply] using hP))
  have hCp : ∀ P, C.coeff P ≠ 0 → P ∈ Set.range p := fun P hP => hsp P
    (Finset.mem_union_right _ (by simpa [DivisorWithCoeffs.coeff_apply] using hP))
  have h0p : ∀ P, (0 : QDivisor Y).coeff P ≠ 0 → P ∈ Set.range p := fun P hP =>
    absurd (by simp [DivisorWithCoeffs.coeff_apply]) hP
  -- rational klt polytopes around `B` and `C`
  obtain ⟨VB, -, hBint, hVB0, hVBklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sY hY
    hYq B (Finsupp.le_def.2 hB0) hB 0 le_rfl (by rw [map_zero]; exact Finsupp.le_def.2 hB0)
    p hp hBp h0p
  obtain ⟨VC, -, hCint, hVC0, hVCklt⟩ := exists_rationalPolytope_isKltPair_of_isRealKltPair sY hY
    hYq C (Finsupp.le_def.2 hC0) hC 0 le_rfl (by rw [map_zero]; exact Finsupp.le_def.2 hC0)
    p hp hCp h0p
  -- the polytope spanned by both vertex sets
  set V : Finset (Fin s.card → ℚ) := VB ∪ VC
  let Vq : V → QDivisor Y := fun v => ∑ i, Finsupp.single (p i) ((v : Fin s.card → ℚ) i)
  let Φ : (Fin s.card → ℝ) →ₗ[ℝ] RDivisor Y :=
    ∑ i, (Finsupp.lsingle (p i)).comp (LinearMap.proj i)
  have hΦ : ∀ x, Φ x = ∑ i, Finsupp.single (p i) (x i) := fun x => by simp [Φ]
  have hrange : Set.range (fun v => QDivisor.toRDivisor (Vq v)) =
      Φ '' ((fun v i => (v i : ℝ)) '' (V : Set (Fin s.card → ℚ))) := by
    ext D
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, ⟨v, v.2, rfl⟩, by rw [hΦ]; exact (toRDivisor_sum_single p _).symm⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨⟨v, hv⟩, by rw [hΦ]; exact toRDivisor_sum_single p v⟩
  have hmem : ∀ W : Finset (Fin s.card → ℚ), W ⊆ V → ∀ D : RDivisor Y,
      (∀ P, D.coeff P ≠ 0 → P ∈ Set.range p) →
      (fun i => D.coeff (p i) : Fin s.card → ℝ) ∈
        intrinsicInterior ℝ (convexHull ℝ ((fun (v : Fin s.card → ℚ) i => (v i : ℝ)) ''
          (W : Set (Fin s.card → ℚ)))) →
      D ∈ convexHull ℝ (Set.range fun v => QDivisor.toRDivisor (Vq v)) := by
    intro W hW D hD hint
    rw [hrange, ← LinearMap.image_convexHull]
    refine ⟨_, convexHull_mono (Set.image_mono (by exact_mod_cast hW))
      (intrinsicInterior_subset hint), ?_⟩
    rw [hΦ]
    exact (eq_sum_single_coeff hp hD).symm
  -- the vertices are effective and klt, hence lc
  have hVnn : ∀ v ∈ V, ∀ i, 0 ≤ v i := by
    intro v hv i
    rcases Finset.mem_union.1 hv with hv | hv
    · simpa [DivisorWithCoeffs.coeff_apply] using hVB0 _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩) i
    · simpa [DivisorWithCoeffs.coeff_apply] using hVC0 _ (subset_convexHull ℝ _ ⟨v, hv, rfl⟩) i
  have hV0 : ∀ v P, 0 ≤ (Vq v).coeff P := fun v => coeff_sum_single_nonneg p (hVnn _ v.2)
  have hVlc : ∀ v : V, MMP.Intersection.IsLogCanonicalPair sY (Vq v) := by
    intro v
    have hk : IsKltPair sY (Vq v) := by
      rcases Finset.mem_union.1 v.2 with hv | hv
      · exact hVBklt _ hv
      · exact hVCklt _ hv
    exact ⟨hk.1.isPair, hV0 v, fun n E a h => (hk.2 n E a h).le⟩
  obtain ⟨_, v, hv, -⟩ := convexHull_nonempty_iff.1 ⟨_, intrinsicInterior_subset hBint⟩
  exact ⟨V, inferInstance, ⟨⟨v, Finset.mem_union_left _ hv⟩⟩, Vq, hV0, hVlc,
    hmem VB Finset.subset_union_left B hBp hBint, hmem VC Finset.subset_union_right C hCp hCint⟩

end Polytope

/-! ### The radial bound and the ray -/

/-- The arithmetic of the radial bound. Let `x ≥ 0` be `D · L`, either `0` or at least `a`, let
`y = D_t · L < 0`, and let `(K_Y + C) · L = t⁻¹ y - (1 - t) t⁻¹ x ≥ -8`. If
`0 < t < a / (2 (a + 8))`, then `x = 0`. -/
private theorem eq_zero_of_neg_eight_le {a t x y : ℝ} (ha : 0 < a) (ht0 : 0 < t)
    (ht : t < a / (2 * (a + 8))) (hx0 : 0 ≤ x) (hxa : 0 < x → a ≤ x) (hy : y < 0)
    (h8 : -8 ≤ t⁻¹ * y + -(1 - t) / t * x) : x = 0 := by
  have h8t : -8 * t ≤ y - (1 - t) * x := by
    have e : t * (t⁻¹ * y + -(1 - t) / t * x) = y - (1 - t) * x := by
      field_simp; ring
    rw [← e]; nlinarith [mul_le_mul_of_nonneg_left h8 ht0.le]
  have htt : t * (2 * (a + 8)) < a := (lt_div_iff₀ (by positivity)).1 ht
  have ht1 : t < 1 := by nlinarith
  refine le_antisymm (not_lt.1 fun hpos => ?_) hx0
  nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) (sub_nonneg.2 (hxa hpos))]

/-- A homogeneous function vanishing on a nonzero class of an extremal ray vanishes on the
whole ray. -/
private theorem eq_zero_of_mem_isExtremalRay {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N R : Set V} (hR : IsExtremalRay ℝ N R) (φ : V → ℝ)
    (hφ : ∀ (s : ℝ) u, φ (s • u) = s * φ u) {v : V} (hv : v ∈ R) (hv0 : v ≠ 0)
    (h : φ v = 0) : ∀ u ∈ R, φ u = 0 := by
  obtain ⟨-, w, -, rfl⟩ := hR
  obtain ⟨s₀, -, rfl⟩ := hv
  rintro _ ⟨s₁, -, rfl⟩
  have hs₀ : s₀ ≠ 0 := by rintro rfl; exact hv0 (zero_smul _ _)
  rw [hφ] at h ⊢
  rw [(mul_eq_zero.1 h).resolve_left hs₀, mul_zero]

private theorem solution

    {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : Y ⟶ Z} (hf : f ≫ sZ = sY)
    (hYq : IsQFactorial sY) {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 4)
    {B : RDivisor Y} (hB0 : ∀ P, 0 ≤ B.coeff P) (hB : IsRealKltPair sY B)
    (hD : MMP.Flips.IsRelativelyNef ℂ sY f (MMP.Flips.logCanonicalDivisor K B))
    {a : ℝ} (ha : 0 < a)
    (hgap : ∀ (L : ProperCurve sY) (hL : L.IsContractedBy f)
      (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor Y) (hM : ∀ i, (M i).IsCartier),
      Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
      0 < ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
        RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf (L.relativeClass f hL)) →
      a ≤ ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
        RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf (L.relativeClass f hL)))
    {C : RDivisor Y} (hC0 : ∀ P, 0 ≤ C.coeff P) (hC : IsRealKltPair sY C)
    {t : ℝ} (ht0 : 0 < t) (ht : t < a / (2 * (a + 8)))
    {R : Set (RelativeNumericalCurveClasses sY f)}
    (hR : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sY f : Set (RelativeNumericalCurveClasses sY f)) R)
    (hneg : ∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor Y) (hM : ∀ i, (M i).IsCartier),
      (1 - t) • (Divisor.toRDivisor K + B) + t • (Divisor.toRDivisor K + C) =
          ∑ i, c i • Divisor.toRDivisor (M i) ∧
        ∀ u ∈ R, u ≠ 0 →
          ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf u) < 0)
    (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor Y) (hM : ∀ i, (M i).IsCartier)
    (hDM : Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i)) :
    ∀ u ∈ R, ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf u) = 0 := by
  intro u hu
  change ∑ i, c i * pair f (M i) (hM i) u = 0
  obtain ⟨n', c', M', hM', hDt, hnegR⟩ := hneg
  have ht1 : t < 1 := ht.trans ((div_lt_one (by positivity)).2 (by linarith))
  obtain ⟨ι, _, ⟨i₀⟩, V, hV0, hVlc, hBP, hCP⟩ := exists_lcPolytope hY hYq hB0 hB hC0 hC
  -- the uniform rational curve on the polytope, applied at `(1 - t) B + t C`
  obtain ⟨τ, -, hcurve⟩ := exists_pos_forall_isExtremalRay_exists_isRationalCurve_neg_eight_le
    hY hZ hf hYq hK hV0 hVlc (subset_convexHull ℝ _ ⟨i₀, rfl⟩) (κ := Unit) (r := fun _ => 1)
    (fun _ => one_pos) (by simp) (Bj := fun _ => V i₀)
    (fun _ => subset_convexHull ℝ _ ⟨i₀, rfl⟩) (fun _ => hVlc i₀) (by simp)
  obtain ⟨L, hL, -, hLR, hL0, h8, -⟩ := hcurve R hR ⟨(1 - t) • B + t • C,
    convex_convexHull ℝ _ hBP hCP (by linarith) ht0.le (by ring), n', c', M', hM',
    by rw [← hDt]; module, hnegR⟩
  -- the length bound at `C`, read through `K_Y + C = t⁻¹ D_t - (1 - t) t⁻¹ D`
  have hM'' : ∀ i, (Fin.append M' M i).IsCartier :=
    Fin.addCases (fun j => by rw [Fin.append_left]; exact hM' j)
      (fun j => by rw [Fin.append_right]; exact hM j)
  have hKC : Divisor.toRDivisor K + C = ∑ i, Fin.append (t⁻¹ • c') ((-(1 - t) / t) • c) i •
      Divisor.toRDivisor (Fin.append M' M i) := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, mul_smul,
      ← Finset.smul_sum, ← hDt, ← hDM]
    have : t ≠ 0 := ht0.ne'
    match_scalars <;> field_simp <;> ring
  have h8' := h8 C hCP _ _ _ hM'' hKC
  change -8 ≤ ∑ i, Fin.append (t⁻¹ • c') ((-(1 - t) / t) • c) i *
    pair f (Fin.append M' M i) (hM'' i) (L.relativeClass f hL) at h8'
  rw [sum_append_mul_pair f _ _ hM' _ _ hM] at h8'
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum] at h8'
  -- `D · L = 0`, hence `D` vanishes on the ray spanned by `[L]`
  refine eq_zero_of_mem_isExtremalRay hR (fun u => ∑ i, c i * pair f (M i) (hM i) u)
    (fun s u => by simp only [pair_smul, mul_left_comm (c _), ← Finset.mul_sum]) hLR hL0
    (eq_zero_of_neg_eight_le ha ht0 ht (pair_nonneg_of_isRelativelyNef f hD c M hM hDM L hL)
      (hgap L hL n c M hM hDM) (hnegR _ hLR hL0) h8') u hu

end Proof_lem_fourfold_birational_fourfold_radial_ray

end

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **A uniform radial neighbourhood of a nef real klt adjoint.** Let `f : Y ⟶ Z` be a morphism
of projective complex varieties, `Y` normal `ℚ`-factorial of dimension four with canonical
divisor `K`, let `(Y, B)` be a klt pair with effective real boundary (`MMP.Fourfold.IsRealKltPair`)
such that `D = K + B` is nef over `Z`, and let `a > 0` be such that `a ≤ D · L` whenever
`0 < D · L` for a curve `L` contracted by `f`. Then for every klt pair `(Y, C)` with effective
real boundary and every `0 < t < a / (2 (a + 8))`, every extremal ray `R` of `NE̅(Y/Z)` on which
`(1 - t) D + t (K + C)` is negative (for some presentation by Cartier divisors) is `D`-null: the
pairing of `D` with every class in `R`, computed from any presentation of `D` by Cartier
divisors, is zero. -/
@[mmp "lem_fourfold_birational_fourfold_radial_ray"]
public theorem forall_isExtremalRay_null_of_isRealKltPair_of_lt_div
    {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : Y ⟶ Z} (hf : f ≫ sZ = sY)
    (hYq : IsQFactorial sY) {K : Divisor Y} (hK : K.IsCanonicalDivisor sY 4)
    {B : RDivisor Y} (hB0 : ∀ P, 0 ≤ B.coeff P) (hB : IsRealKltPair sY B)
    (hD : MMP.Flips.IsRelativelyNef ℂ sY f (MMP.Flips.logCanonicalDivisor K B))
    {a : ℝ} (ha : 0 < a)
    (hgap : ∀ (L : ProperCurve sY) (hL : L.IsContractedBy f)
      (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor Y) (hM : ∀ i, (M i).IsCartier),
      Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i) →
      0 < ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
        RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf (L.relativeClass f hL)) →
      a ≤ ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
        RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf (L.relativeClass f hL)))
    {C : RDivisor Y} (hC0 : ∀ P, 0 ≤ C.coeff P) (hC : IsRealKltPair sY C)
    {t : ℝ} (ht0 : 0 < t) (ht : t < a / (2 * (a + 8)))
    {R : Set (RelativeNumericalCurveClasses sY f)}
    (hR : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sY f : Set (RelativeNumericalCurveClasses sY f)) R)
    (hneg : ∃ (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor Y) (hM : ∀ i, (M i).IsCartier),
      (1 - t) • (Divisor.toRDivisor K + B) + t • (Divisor.toRDivisor K + C) =
          ∑ i, c i • Divisor.toRDivisor (M i) ∧
        ∀ u ∈ R, u ≠ 0 →
          ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf u) < 0)
    (n : ℕ) (c : Fin n → ℝ) (M : Fin n → Divisor Y) (hM : ∀ i, (M i).IsCartier)
    (hDM : Divisor.toRDivisor K + B = ∑ i, c i • Divisor.toRDivisor (M i)) :
    ∀ u ∈ R, ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sY f (M i).divisorialSheaf u) = 0 :=
        by revert Y Z sY sZ hY hZ f hf hYq K hK B hB0 hB hD a ha hgap C hC0 hC t ht0 ht R hR hneg n c M hM hDM; first | exact Proof_lem_fourfold_birational_fourfold_radial_ray.solution | exact Proof_lem_fourfold_birational_fourfold_radial_ray.solution _ | exact Proof_lem_fourfold_birational_fourfold_radial_ray.solution _ _ | exact Proof_lem_fourfold_birational_fourfold_radial_ray.solution _ _ _ | exact Proof_lem_fourfold_birational_fourfold_radial_ray.solution _ _ _ _

end MMP.Fourfold

