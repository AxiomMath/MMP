module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.ContractionFibreLength
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.NegativeFaceCurve
public import MMP.AlgebraicGeometry.MMP.Contraction.Existence
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.CountableDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.AlgClosedExtension
public import MMP.AlgebraicGeometry.Geometrically.CurveClassesBaseChange
public import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.ComplexTransfer
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.Analysis.Convex.FiniteDimensional
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
public import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.RationalCurveSmoothLocus
public import MMP.AlgebraicGeometry.Curves.RationalCurveImage
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.ProjectiveSpace.ZeroLocusFactorization
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary

/-!
# Lengths of negative extremal rays of projective klt pairs in characteristic zero

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a klt pair with
`B` an effective `ℚ`-divisor and `X` a projective variety over `k` of dimension `n`. Every
`(K_X + B)`-negative extremal ray `R` of the closed cone of curves `NE̅(X) ⊆ N₁(X)_ℝ` is
spanned by the class of a rational curve `T ⊆ X` with `0 < -(K_X + B) · T ≤ 2n`.

The contraction theorem gives the contraction `f : X ⟶ Z` of `R`, with a positive-dimensional
fibre on which `-(K_X + B)` is relatively ample. The morphism, the fibre and the pair are
descended to a countable algebraically closed subfield of `k`, embedded in `ℂ`, where the
complex length theorem applies; the rational curve and its degree are then transported back.

## Main results

* `MMP.Fourfold.exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed`: the
  statement above.

## Implementation notes

* The klt condition is `MMP.Mori.IsKltPair` with a canonical divisor `K` of dimension `n`; this
  pins `n = dim X`. Effectivity of `B` is `0 ≤ B`.
* The ray is `MMP.Fourfold.IsNegativeExtremalRayOf` for the `ℚ`-Cartier divisor `K + B`, and
  `(K + B) · T` is `MMP.Fourfold.QDivisor.curveForm` evaluated on the class of `T` in
  `N₁(X)_ℝ`.
* The curve `T` is a `MMP.Mori.ProperCurve`, recorded by its generic point, whose reduced closed
  subscheme is a rational curve in the sense of `MMP.Mori.IsRationalCurve`. "Spanning `R`"
  means `R = ℝ_{≥0} · [T]`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

section

/-!
## Proof outline

The pair is the base change of a projective klt pair `(X₀, B₀)` over a countable algebraically
closed subfield `k₀ ⊆ k`, and `R` is the image of a negative extremal ray `R₀` of `NE̅(X₀)` under
the base-extension isomorphism `N₁(X₀)_ℝ ≃ N₁(X)_ℝ`. Over `k₀` the contraction theorem gives the
contraction `f₀ : X₀ ⟶ Z₀` of `R₀` and a curve contracted to a closed point `z₀`. The field `k₀`
embeds in `ℂ`. The base change `f_ℂ` of `f₀` is a contraction of `X_ℂ` on which `-(K + B)` is
relatively ample, so its fibre over the point above `z₀` contains a rational curve `Q` with
`0 < -(K + B) · Q ≤ 2n`. Embed `X₀ ⊆ ℙᴺ_{k₀}`. Rational curves of degree at most `e` in the
fibre `F₀ = f₀⁻¹(z₀)` are the points of a finitely generated `k₀`-algebra of binary forms; it has a
`ℂ`-point (from `Q`), hence a `k₀`-point by the Nullstellensatz, hence a rational curve
`T₀ ⊆ F₀` of degree at most `deg Q`. Its class lies in `R₀`, and since `R₀` is a ray the bound
for `Q` gives `0 < -(K + B) · T₀ ≤ 2n`. The base change `T` of `T₀` is a rational curve on `X`
spanning `R`, with the same degree.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold
  MMP.ProgramBaseChange MMP.Fourfold.SmoothLocusSlopeBound

namespace MMP.FourfoldProofs.FourfoldProjectiveKltRayLengthCharZeroProof

/-! ### Rays -/

section Ray

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonzero vector of an extremal ray spans it. -/
private theorem eq_ray_of_mem {N R : Set V} (hR : IsExtremalRay ℝ N R) {u : V} (hu : u ∈ R)
    (hu0 : u ≠ 0) : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • u = w} := by
  obtain ⟨-, v, hv, rfl⟩ := hR
  obtain ⟨a, ha, rfl⟩ := hu
  have ha0 : a ≠ 0 := by rintro rfl; simp at hu0
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c / a, div_nonneg hc ha, by rw [smul_smul, div_mul_cancel₀ c ha0]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * a, mul_nonneg hc ha, by rw [mul_smul]⟩

/-- **The length bound along a ray.** Let `u, v` lie on an extremal ray, `d` and `κ` be linear
forms with `0 < d u ≤ d v` and `0 < κ v ≤ b`. Then `0 < κ u ≤ b`. -/
private theorem pos_and_le_of_mem_ray {N R : Set V} (hR : IsExtremalRay ℝ N R) {u v : V}
    (hu : u ∈ R) (hv : v ∈ R) (d κ : V →ₗ[ℝ] ℝ) (hdu : 0 < d u) (hduv : d u ≤ d v)
    (hκv : 0 < κ v) {b : ℝ} (hκb : κ v ≤ b) : 0 < κ u ∧ κ u ≤ b := by
  have hdv : 0 < d v := hdu.trans_le hduv
  have hv0 : v ≠ 0 := by rintro rfl; simp at hdv
  obtain ⟨c, hc, rfl⟩ : ∃ c : ℝ, 0 ≤ c ∧ c • v = u := by rwa [eq_ray_of_mem hR hv hv0] at hu
  rw [map_smul, smul_eq_mul] at hdu hduv
  rw [map_smul, smul_eq_mul]
  have hc0 : 0 < c := pos_of_mul_pos_left hdu hdv.le
  have hc1 : c ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  exact ⟨mul_pos hc0 hκv, by nlinarith⟩

end Ray

/-! ### Contracted curves -/

section Contracted

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The image of a curve contracted by a proper morphism is a closed point. -/
private theorem isClosed_singleton_of_isContractedBy (C : ProperCurve sX) (f : X ⟶ Y)
    [IsProper f] (hC : C.IsContractedBy f) : IsClosed ({f C.point} : Set Y) := by
  have h : f.base '' closure {C.point} = {f C.point} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hC x hx
    · rintro _ rfl
      exact ⟨C.point, subset_closure rfl, rfl⟩
  rw [← h]
  exact f.isClosedMap _ isClosed_closure

/-- A set containing a proper curve has dimension at least one. -/
private theorem one_le_topologicalKrullDim_of_subset (C : ProperCurve sX) {S : Set X}
    (hS : closure {C.point} ⊆ S) : 1 ≤ topologicalKrullDim S := by
  have hmem : ∀ c, C.ι c ∈ S := fun c => hS (C.range_ι ▸ ⟨c, rfl⟩)
  have hi : Topology.IsInducing (S.codRestrict C.ι hmem) :=
    C.ι.isClosedEmbedding.isInducing.codRestrict hmem
  have h := hi.topologicalKrullDim_le
  rwa [C.dim_eq] at h

/-- A morphism contracting a proper curve is not an isomorphism. -/
private theorem not_isIso_of_isContractedBy (C : ProperCurve sX) (f : X ⟶ Y)
    (hC : C.IsContractedBy f) : ¬ IsIso f := by
  intro hiso
  have hinj : Function.Injective f := f.isOpenEmbedding.injective
  have hsub : Subsingleton C.scheme := by
    refine ⟨fun a b => C.ι.isClosedEmbedding.injective ?_⟩
    have hmem : ∀ c : C.scheme, C.ι c ∈ closure ({C.point} : Set X) := fun c =>
      C.range_ι ▸ ⟨c, rfl⟩
    rw [hinj (hC _ (hmem a)), hinj (hC _ (hmem b))]
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

end Contracted

/-! ### Descent of the pair to a countable algebraically closed field -/

/-- A prime divisor of the base change lying over the generic point of a prime divisor `P₀` is
the base change of `P₀`. -/
private theorem closure_eq_of_map_genericPoint_eq {k₀ K : Type} [Field k₀] [Field K]
    [Algebra k₀ K] [IsAlgClosed k₀] [IsAlgClosed K] {X₀ X : Scheme.{0}} [IsIntegral X₀]
    [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {P₀ : MMP.Mori.PrimeDivisor X₀} {P : MMP.Mori.PrimeDivisor X}
    (hP : π P.genericPoint = P₀.genericPoint) :
    closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  obtain ⟨P', hP', -⟩ := exists_primeDivisor_baseChange h P₀
  have hmem : P.genericPoint ∈ closure {P'.genericPoint} := by
    rw [hP', Set.mem_preimage, hP]; exact subset_closure rfl
  have heq : P'.genericPoint = P.genericPoint :=
    eq_of_specializes_of_coheight_eq_one (specializes_iff_mem_closure.mpr hmem)
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P')
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P)
  rw [← heq, hP']

/-- A divisor with the coefficients of a program's base change is a base change. -/
private theorem isBaseChange_of_coeff {k₀ K : Type} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] [IsAlgClosed K] {X₀ X : Scheme.{0}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    {R : Type*} [Zero R] {D₀ : DivisorWithCoeffs R X₀} {D : DivisorWithCoeffs R X}
    (h1 : ∀ (P : MMP.Mori.PrimeDivisor X) (P₀ : MMP.Mori.PrimeDivisor X₀),
      π P.genericPoint = P₀.genericPoint → D.coeff P = D₀.coeff P₀)
    (h2 : ∀ P : MMP.Mori.PrimeDivisor X,
      (∀ P₀ : MMP.Mori.PrimeDivisor X₀, π P.genericPoint ≠ P₀.genericPoint) → D.coeff P = 0) :
    IsBaseChange π D₀ D := by
  haveI : Surjective π := surjective_of_isPullback h
  refine ⟨fun P₀ P hP => h1 P P₀ (map_eq_of_closure_eq hP), fun P hP => ?_⟩
  by_contra hne
  push Not at hne
  refine hP (h2 P fun P₀ hP₀ => hne P₀ ?_)
  exact closure_eq_of_map_genericPoint_eq h hP₀

/-- The program with no steps from a projective lc pair. -/
private noncomputable def trivialProgram {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {K : Divisor X} {B : QDivisor X} (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX B) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) :
    Program sX K B where
  n := 0
  Y := fun _ => X
  sY := fun _ => sX
  KY := fun _ => K
  BY := fun _ => B
  R := fun _ => ∅
  Z := fun _ => X
  sZ := fun _ => sX
  f := fun i => match i with
    | 0 => 𝟙 X
    | _ + 1 => 𝟙 X
  fp := fun _ => 𝟙 X
  isProjectiveVariety := hX
  isLogCanonicalPair := hlc
  isCanonicalDivisor := hK
  isPermittedStep := fun i hi => absurd hi (by simp)
  KY_eq := fun i hi => absurd hi (by simp)
  BY_eq := fun i hi => absurd hi (by simp)
  hasFinal := False
  finalRay := ∅
  T := X
  sT := sX
  g := eqToHom rfl
  final_spec := fun h => h.elim

/-- A klt pair with effective boundary is log canonical. -/
private theorem isLogCanonicalPair_of_isKltPair {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hklt : IsKltPair sX n K B) (hB : 0 ≤ B) : MMP.Intersection.IsLogCanonicalPair sX B := by
  have hnn : ∀ P, 0 ≤ B.coeff P := fun P => hB P
  have hP : MMP.Fourfold.IsPair sX B := ⟨inferInstance, inferInstance, hklt.1.isPair, hnn⟩
  have h4 := (isKltPair_iff_mori_isKltPair sX hklt.1.2.1 hP).2 hklt
  exact ⟨hklt.1.isPair, hnn, fun m D a ha => (h4.2 m D a ha).le⟩

/-- **Descent of a projective klt pair.** A projective klt pair over an algebraically closed field
`k` of characteristic zero is the base change of a projective variety `X₀` over a countable
algebraically closed subfield `k₀ ⊆ k`, with divisors `K₀`, `B₀` whose base changes are `K`,
`B`. -/
private theorem exists_isPullback_isBaseChange {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsProjectiveVariety k sX) {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hklt : IsKltPair sX n K B) (hB : 0 ≤ B) :
    ∃ (k₀ : Subfield k) (_ : Countable k₀) (_ : IsAlgClosed k₀) (X₀ : Scheme.{0})
      (_ : IsIntegral X₀) (_ : CompactSpace X₀) (_ : IsLocallyNoetherian X₀) (_ : IsNormal X₀)
      (s₀ : X₀ ⟶ Spec (.of k₀)) (K₀ : Divisor X₀) (B₀ : QDivisor X₀) (π : X ⟶ X₀),
      IsPullback π sX s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ k))) ∧
        MMP.Mori.IsProjectiveVariety k₀ s₀ ∧ IsBaseChange π K₀ K ∧ IsBaseChange π B₀ B := by
  let P := trivialProgram hX (isLogCanonicalPair_of_isKltPair hklt hB) ⟨n, hklt.1.2.1⟩
  obtain ⟨k₀, hc, ha, X₀, i1, i2, i3, i4, s₀, K₀, B₀, P₀, -, πX, -, -, hmod, -, -, -⟩ :=
    P.exists_countable_isAlgClosed_subfield_program
  obtain ⟨hpb, hcoeff, hzero⟩ := hmod 0 (by simp [P, trivialProgram])
  have hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀ := P₀.isProjectiveVariety
  haveI : LocallyOfFiniteType (modelStr s₀ P₀.sY 0) := hX₀.toLocallyOfFiniteType
  refine ⟨k₀, hc, ha, X₀, i1, i2, i3, i4, s₀, K₀, B₀, πX 0, hpb, hX₀,
    isBaseChange_of_coeff hpb (fun E E₀ hE => (hcoeff E E₀ hE).1) (fun E hE => (hzero E hE).1),
    isBaseChange_of_coeff hpb (fun E E₀ hE => (hcoeff E E₀ hE).2) (fun E hE => (hzero E hE).2)⟩

/-! ### Klt pairs under base change -/

/-- Effectivity is detected after algebraically closed base extension. -/
private theorem nonneg_iff_of_isPullback {k₀ K : Type} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{0}} [IsIntegral X₀] [IsIntegral X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {B₀ : QDivisor X₀} {B : QDivisor X}
    (hB : IsBaseChange π B₀ B) : 0 ≤ B₀ ↔ 0 ≤ B := by
  haveI : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  refine ⟨fun h0 P => ?_, fun h0 P₀ => ?_⟩
  · by_cases hP : B P = 0
    · simp [hP]
    · obtain ⟨P₀, hP₀⟩ := hB.2 P hP
      rw [hB.1 P₀ P hP₀]
      exact h0 P₀
  · obtain ⟨P, hP, -⟩ := exists_primeDivisor_baseChange h P₀
    rw [← hB.1 P₀ P hP]
    exact h0 P

/-- **Klt is tested on one log resolution.** Let `(X, B)` be a pair, `π : W ⟶ X` a log
resolution of `(X, B)` and `B_W` the crepant pull-back of `(X, B)` on `W`. Then `(X, B)` is klt
if and only if every coefficient of `B_W` is less than one. -/
private theorem isKltPair_iff_forall_coeff_lt_one {k : Type} [Field k] {X W : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Fourfold.IsPair sX B) {π : W ⟶ X}
    (hπ : MMP.Fourfold.IsLogResolution sX B π) (hW : IsNormalVariety k (π ≫ sX)) {n : ℕ}
    {K : Divisor X} {BW : QDivisor W}
    (hBW : IsCrepantBoundary sX n K B π hW hπ.isBirationalMorphism BW) :
    MMP.Fourfold.IsKltPair sX B ↔ ∀ F, BW.coeff F < 1 := by
  haveI : IsAlgClosed k := hB.isAlgClosed
  haveI : CharZero k := hB.charZero
  refine ⟨fun hk F => ?_, fun hlt => ?_⟩
  · have h0 := hk.2 n _ _
      (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBW F) hπ.isProper)
    have h1 : ((BW.coeff F : ℚ) : ℝ) < 1 := by push_cast at h0; linarith
    exact_mod_cast h1
  have hP : MMP.Mori.IsPair sX B := hB.isPair
  have hbir : MMP.Mori.IsBirationalMorphism π := hπ.isBirationalMorphism
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (π ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : IsNormal W := hW.2
  haveI : IsDominant π := hbir.isDominant
  haveI : AlgebraicGeometry.IsVariety k sX := hP.1.1
  haveI : AlgebraicGeometry.IsVariety k (π ≫ sX) := hW.1
  haveI : CompactSpace W := hW.1.toQuasiCompact.compactSpace_of_compactSpace
  refine ⟨hB, fun n' D a ha => ?_⟩
  -- `n' = dim X = dim W` is positive, and `n' = n`
  have hdimX : topologicalKrullDim X = n' :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  have hdimW : topologicalKrullDim W = n' :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (π ≫ sX) hbir).symm.trans
      hdimX
  obtain ⟨F₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimW
    (MMP.Fourfold.ne_zero_of_topologicalKrullDim_eq hdimX D)
  have hK : K.IsCanonicalDivisor sX n := (hBW F₀).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hdimX
  -- `a = 1 + c` for the discrepancy `c = a(D, X, B) = a(D', W, B_W) > -1`
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  obtain ⟨KW, hKW⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sX) hπ.isSmoothScheme hdimW
  obtain ⟨-, hcr⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP π hW hbir hK hKW
    (Or.inl hBW)
  obtain ⟨D', hD'⟩ := MMP.Fourfold.exists_divisorOver_valuation_eq_comap π hπ.isProper
    hbir.functionFieldMap_bijective hW D
  obtain ⟨S, hS, hsnc⟩ := MMP.Fourfold.exists_isSNC_superset_support hP.1 hπ hW hBW
  have h : (-1 : ℝ) < c := by
    exact_mod_cast MMP.Fourfold.neg_one_lt_of_isDiscrepancy_of_isSNC hW hπ.isSmoothScheme hKW S
      hS hsnc hlt ((hcr D' D hD' c).2 hc)
  linarith

/-- **Klt pairs are detected after algebraically closed base extension.** -/
private theorem isKltPair_iff_of_isPullback {k₀ K : Type} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] [IsAlgClosed K] [CharZero k₀]
    {X₀ X : Scheme.{0}} [IsIntegral X₀] [CompactSpace X₀] [IsLocallyNoetherian X₀] [IsNormal X₀]
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {n : ℕ} {K₀ : Divisor X₀} {KK : Divisor X}
    (hK : IsBaseChange π K₀ KK) {B₀ : QDivisor X₀} {B : QDivisor X} (hB : IsBaseChange π B₀ B)
    (hB₀ : 0 ≤ B₀) :
    IsKltPair s₀ n K₀ B₀ ↔ IsKltPair s n KK B := by
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap k₀ K).injective).mp inferInstance
  haveI : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  have hdim : topologicalKrullDim X = topologicalKrullDim X₀ :=
    (invariants_of_isPullback s₀ h).2.2
  have hB' : 0 ≤ B := (nonneg_iff_of_isPullback h hX₀ hB).1 hB₀
  -- klt in the sense of log discrepancies is detected on a log resolution and its base change
  have h4 : ∀ (hP₀ : MMP.Fourfold.IsPair s₀ B₀) (hP : MMP.Fourfold.IsPair s B),
      MMP.Fourfold.IsKltPair s₀ B₀ ↔ MMP.Fourfold.IsKltPair s B := by
    intro hP₀ hP
    obtain ⟨W₀, W, μ₀, μ, πW, hWsq, hcomm, hW₀, hsm₀, hlog₀, hlog⟩ :=
      exists_isLogResolution_isPullback h hX₀ hB
    obtain ⟨m, K₀', KK', hW₀n, hWn, BW₀, BW, hcb₀, hcb, hbc⟩ :=
      exists_isCrepantBoundary_isBaseChange h hX₀ hB hP₀.isPair hWsq hcomm hW₀ hsm₀
        hlog₀.isBirationalMorphism hlog.isBirationalMorphism
    rw [isKltPair_iff_forall_coeff_lt_one s₀ hP₀ hlog₀ hW₀n hcb₀,
      isKltPair_iff_forall_coeff_lt_one s hP hlog hWn hcb]
    haveI : IsIntegral W₀ := hW₀.toIsIntegral
    haveI : IsIntegral W := hWn.1.toIsIntegral
    haveI : LocallyOfFiniteType (μ₀ ≫ s₀) := hW₀.toLocallyOfFiniteType
    exact forall_coeff_iff_of_isBaseChange hWsq hbc (p := fun c => c < 1) zero_lt_one
  have hcan : ∀ {m : ℕ}, (∃ m' : ℕ, K₀.IsCanonicalDivisor s₀ m') →
      (∃ m' : ℕ, KK.IsCanonicalDivisor s m') → (K₀.IsCanonicalDivisor s₀ m ↔
        KK.IsCanonicalDivisor s m) := by
    rintro m ⟨m₀, hm₀⟩ ⟨m₁, hm₁⟩
    have hd : (m₀ : WithBot ℕ∞) = m₁ := by
      rw [← hm₀.topologicalKrullDim_eq, ← hm₁.topologicalKrullDim_eq, hdim]
    obtain rfl : m₀ = m₁ := by exact_mod_cast hd
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · obtain rfl : m = m₀ := by
        exact_mod_cast hm.topologicalKrullDim_eq.symm.trans hm₀.topologicalKrullDim_eq
      exact hm₁
    · obtain rfl : m = m₀ := by
        exact_mod_cast hm.topologicalKrullDim_eq.symm.trans hm₁.topologicalKrullDim_eq
      exact hm₀
  constructor
  · intro hk
    have hP₀ : MMP.Fourfold.IsPair s₀ B₀ :=
      ⟨inferInstance, inferInstance, hk.1.isPair, fun P => hB₀ P⟩
    have hP : MMP.Fourfold.IsPair s B :=
      ⟨inferInstance, inferInstance, (isPair_iff_of_isBaseChange h hX₀ hB).1 hk.1.isPair,
        fun P => hB' P⟩
    have hc := (exists_isCanonicalDivisor_iff h hX₀ hK).1 ⟨n, hk.1.2.1⟩
    have hKc : KK.IsCanonicalDivisor s n := (hcan ⟨n, hk.1.2.1⟩ hc).1 hk.1.2.1
    exact (isKltPair_iff_mori_isKltPair s hKc hP).1
      ((h4 hP₀ hP).1 ((isKltPair_iff_mori_isKltPair s₀ hk.1.2.1 hP₀).2 hk))
  · intro hk
    have hP : MMP.Fourfold.IsPair s B :=
      ⟨inferInstance, inferInstance, hk.1.isPair, fun P => hB' P⟩
    have hP₀ : MMP.Fourfold.IsPair s₀ B₀ :=
      ⟨inferInstance, inferInstance, (isPair_iff_of_isBaseChange h hX₀ hB).2 hk.1.isPair,
        fun P => hB₀ P⟩
    have hc := (exists_isCanonicalDivisor_iff h hX₀ hK).2 ⟨n, hk.1.2.1⟩
    have hKc : K₀.IsCanonicalDivisor s₀ n := (hcan hc ⟨n, hk.1.2.1⟩).2 hk.1.2.1
    exact (isKltPair_iff_mori_isKltPair s₀ hKc hP₀).1
      ((h4 hP₀ hP).2 ((isKltPair_iff_mori_isKltPair s hk.1.2.1 hP).2 hk))

/-! ### Rational curves under base change -/

/-- `ℙ¹_K` is the base change of `ℙ¹_{k₀}` along `Spec K ⟶ Spec k₀`. -/
private theorem exists_isPullback_projectiveLine (k₀ K : Type) [Field k₀] [Field K]
    [Algebra k₀ K] :
    ∃ p : projectiveLine K ⟶ projectiveLine k₀,
      IsPullback p (projectiveLine K ↘ Spec (.of K)) (projectiveLine k₀ ↘ Spec (.of k₀))
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
  let e : ∀ (R : Type) [CommRing R], projectiveLine R ≅ projectiveSpaceOverRing 1 (.of R) :=
    fun R _ => projectiveLineIsoProj R ≪≫
      (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso R 1).symm
  have he : ∀ (R : Type) [CommRing R], (e R).hom ≫ pullback.fst (terminal.from (Spec (.of R)))
      (terminal.from (projectiveSpaceAtUniverse.{0} 1)) = projectiveLine R ↘ Spec (.of R) := by
    intro R _
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff,
      Iso.inv_hom_id_assoc]
    exact projectiveLineIsoProj_hom_comp_projToSpecCoeff R
  refine ⟨(e K).hom ≫ projectiveSpaceFieldExtensionMap k₀ K 1 ≫ (e k₀).inv, ?_⟩
  refine IsPullback.of_iso (isPullback_projectiveSpaceFieldExtensionMap k₀ K 1) (e K).symm
    (e k₀).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [← he K]
  · simp [← he k₀]
  · simp

/-- The kernel of a quasi-compact morphism from a reduced scheme is the vanishing ideal of the
closure of its range. -/
private theorem ker_eq_vanishingIdeal_closure_range {Y W : Scheme.{0}} (f : Y ⟶ W)
    [QuasiCompact f] [IsReduced Y] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range f)) := by
  have hrad : f.ker.radical = f.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    refine le_antisymm (fun x ⟨n, hn⟩ => ?_) Ideal.le_radical
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ⟨n, hn⟩)
  have hs : f.ker.support = Closeds.closure (Set.range f) :=
    Closeds.ext (by rw [Scheme.Hom.support_ker]; rfl)
  rw [← hs, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

/-- **Base change of a rational curve.** If `T₀` is the image of a morphism `ℙ¹_{k₀} ⟶ X₀`
over `k₀`, then the base change `T` of `T₀` (the curve whose closure is `π⁻¹(T₀)`) is a rational
curve: it is the image of the base-changed morphism `ℙ¹_K ⟶ X`. -/
private theorem isRationalCurve_of_isPullback {k₀ K : Type} [Field k₀] [Field K] [Algebra k₀ K]
    [IsAlgClosed k₀] [IsAlgClosed K]
    {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    [IsSeparated s₀] [AlgebraicGeometry.IsProperVariety K s]
    (g₀ : projectiveLine k₀ ⟶ X₀) (hg₀ : g₀ ≫ s₀ = projectiveLine k₀ ↘ Spec (.of k₀))
    (T₀ : ProperCurve s₀) (hT₀ : closure (Set.range g₀) = closure {T₀.point})
    (T : ProperCurve s) (hT : closure {T.point} = π.base ⁻¹' closure {T₀.point}) :
    IsRationalCurve s
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) := by
  obtain ⟨p, hp⟩ := exists_isPullback_projectiveLine k₀ K
  have hsq : IsPullback (pullback.fst g₀ π) (pullback.snd g₀ π ≫ s)
      (projectiveLine k₀ ↘ Spec (.of k₀)) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
    rw [← hg₀]; exact (IsPullback.of_hasPullback g₀ π).paste_vert h
  set e := hp.isoIsPullback _ _ hsq with he
  set g : projectiveLine K ⟶ X := e.hom ≫ pullback.snd g₀ π with hgdef
  have hg : g ≫ s = projectiveLine K ↘ Spec (.of K) := by
    rw [hgdef, Category.assoc, IsPullback.isoIsPullback_hom_snd]
  -- the range of `g` is `π⁻¹(T₀) = T`
  haveI : IsProper (g₀ ≫ s₀) := hg₀ ▸ inferInstance
  haveI : IsProper g₀ := IsProper.of_comp g₀ s₀
  have hr₀ : Set.range g₀ = closure {T₀.point} := by
    rw [← hT₀, (g₀.isClosedMap.isClosed_range).closure_eq]
  have hr : Set.range g = closure {T.point} := by
    have hes : Function.Surjective e.hom := (Scheme.homeoOfIso e).surjective
    rw [hgdef, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hes.range_eq,
      Set.image_univ, Scheme.Pullback.range_snd, hr₀, hT]
  -- the image of `ℙ¹_K` is a rational curve
  have hbot := isRationalCurve_bot_projectiveLine K
  set ι := (⊥ : (projectiveLine K).IdealSheafData).subschemeι with hι
  haveI : IsIntegral (⊥ : (projectiveLine K).IdealSheafData).subscheme := hbot.1.1
  haveI : IsProper g := by
    haveI : IsProper (g ≫ s) := hg ▸ inferInstance
    exact IsProper.of_comp g s
  have hιs : Function.Surjective ι := (Scheme.homeoOfIso (asIso ι)).surjective
  have hrι : Set.range (ι ≫ g) = closure {T.point} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hιs.range_eq, Set.image_univ, hr]
  have hnc :
      ¬ (g.base '' ((⊥ : (projectiveLine K).IdealSheafData).support : Set _)).Subsingleton := by
    intro hsub
    rw [Scheme.IdealSheafData.support_bot, TopologicalSpace.Closeds.coe_top, Set.image_univ, hr]
      at hsub
    have h1 := one_le_topologicalKrullDim_of_subset T (subset_refl _)
    haveI : Subsingleton (closure ({T.point} : Set X)) := hsub.coe_sort
    haveI : DiscreteTopology (closure ({T.point} : Set X)) := Subsingleton.discreteTopology
    have h0 := topologicalKrullDim_zero_of_discreteTopology (closure ({T.point} : Set X))
    exact absurd (h1.trans h0) (by decide)
  have hrat := IsRationalCurve.ker_subschemeι_comp hg hbot hnc
  rw [ker_eq_vanishingIdeal_closure_range, hrι] at hrat
  convert hrat using 2
  exact Closeds.ext (by simp only [Closeds.coe_closure, closure_closure])

/-! ### Descent of a rational curve of bounded degree -/

/-- **Nullstellensatz.** A finitely generated algebra over an algebraically closed field `k₀`
which maps to some field has a `k₀`-point. -/
private theorem nonempty_algHom_of_ringHom {k₀ A K : Type} [Field k₀] [IsAlgClosed k₀]
    [CommRing A] [Algebra k₀ A] [Algebra.FiniteType k₀ A] [Field K] (χ : A →+* K) :
    Nonempty (A →ₐ[k₀] k₀) := by
  haveI : Nontrivial A := χ.domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k₀ (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k₀ m) (Ideal.Quotient.mkₐ_surjective k₀ m)
  haveI : Module.Finite k₀ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k₀ (A ⧸ m)
  let e : k₀ ≃ₐ[k₀] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId k₀ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k₀ m)⟩

/-! #### Binary forms -/

section BinaryForms

attribute [local instance] MvPolynomial.gradedAlgebra

open Polynomial in
/-- **Descent of binary solutions.** If homogeneous equations over an algebraically closed field
`k₀` have a nonconstant solution in binary forms of degree at most `e` over an extension field,
they have one over `k₀`. -/
private theorem hasBinarySolution_descent {k₀ K : Type} [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K] {r N : ℕ} (G : Fin r → MvPolynomial (Fin (N + 1)) k₀) {e : ℕ}
    (h : HasBinarySolution K (fun l => (G l).map (algebraMap k₀ K)) e) :
    HasBinarySolution k₀ G e := by
  classical
  obtain ⟨f, hdeg, heq, k, k', a, b, hne⟩ := h
  set m : K := (f k).coeff a * (f k').coeff b - (f k).coeff b * (f k').coeff a with hm
  have hm0 : m ≠ 0 := sub_ne_zero.mpr hne
  let S : Finset K := insert m⁻¹ (Finset.univ.biUnion fun i =>
    (Finset.range (e + 1)).image (f i).coeff)
  let A : Subalgebra k₀ K := Algebra.adjoin k₀ (S : Set K)
  haveI : Algebra.FiniteType k₀ A :=
    (Subalgebra.fg_iff_finiteType (R := k₀) A).mp (Subalgebra.fg_adjoin_finset S)
  have hcoeff : ∀ i n, n ∈ Finset.range (e + 1) → (f i).coeff n ∈ A := fun i n hn =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ hn⟩)))
  have hinv : m⁻¹ ∈ A := Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  obtain ⟨ψ⟩ := nonempty_algHom_of_ringHom (k₀ := k₀) (A := A) A.val.toRingHom
  -- `f` lifted to `A[X]`
  let f' : Fin (N + 1) → A[X] := fun i => ∑ n ∈ (Finset.range (e + 1)).attach,
    monomial n.1 ⟨(f i).coeff n.1, hcoeff i n.1 n.2⟩
  have hf' : ∀ i, (f' i).map (A.val : A →+* K) = f i := by
    intro i
    simp only [f', Polynomial.map_sum, Polynomial.map_monomial]
    conv_rhs => rw [(f i).as_sum_range' (e + 1) (Nat.lt_succ_of_le (hdeg i))]
    exact Finset.sum_attach (Finset.range (e + 1)) (fun n => monomial n ((f i).coeff n))
  have hc' : ∀ i n, ((f' i).coeff n : K) = (f i).coeff n := by
    intro i n
    simpa using congrArg (fun p => p.coeff n) (hf' i)
  have hmap : ∀ {B : Type} [CommRing B] [Algebra k₀ B] (χ : A →ₐ[k₀] B)
      (p : MvPolynomial (Fin (N + 1)) k₀),
      (MvPolynomial.aeval f' p).map (χ : A →+* B) =
        MvPolynomial.aeval (fun i => (f' i).map (χ : A →+* B)) p := by
    intro B _ _ χ p
    simpa [Polynomial.coe_mapAlgHom] using
      congrArg (fun φ : MvPolynomial (Fin (N + 1)) k₀ →ₐ[k₀] B[X] => φ p)
        (MvPolynomial.comp_aeval (R := k₀) f' (Polynomial.mapAlgHom χ))
  let c : A := (f' k).coeff a * (f' k').coeff b - (f' k).coeff b * (f' k').coeff a
  have hcm : (c : K) = m := by
    simp only [c, Subalgebra.coe_sub, Subalgebra.coe_mul, hc', hm]
  have hcu : (⟨m⁻¹, hinv⟩ : A) * c = 1 := Subtype.ext (by
    rw [Subalgebra.coe_mul, hcm, inv_mul_cancel₀ hm0]; rfl)
  refine ⟨fun i => (f' i).map (ψ : A →+* k₀), fun i => ?_, fun l => ?_, k, k', a, b, ?_⟩
  · refine (Polynomial.natDegree_map_le).trans ?_
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => ?_
    have h2 : (f i).coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg i).trans_lt hn)
    exact Subtype.ext (by rw [hc', h2]; rfl)
  · have hinj : Function.Injective (Polynomial.map (A.val : A →+* K)) :=
      Polynomial.map_injective _ Subtype.val_injective
    have h1 : MvPolynomial.aeval f' (G l) = 0 := by
      apply hinj
      rw [Polynomial.map_zero, hmap A.val, ← heq l, MvPolynomial.aeval_map_algebraMap]
      simp only [hf']
    rw [← hmap ψ, h1, Polynomial.map_zero]
  · simp only [Polynomial.coeff_map]
    intro hψ
    have h0 : ψ c = 0 := by
      simp only [c, map_sub, map_mul, RingHom.coe_coe] at hψ ⊢; rw [hψ, sub_self]
    have := congrArg ψ hcu
    rw [map_mul, h0, mul_zero, map_one] at this
    exact zero_ne_one this

end BinaryForms

/-- **Descent of a bounded rational curve from `ℂ`.** Let `X₀` be a projective variety over an
algebraically closed subfield `k₀` of `ℂ`, `X` its base change to `ℂ` and `F₀ ⊆ X₀` closed. If a
rational curve `Q ⊆ X` lies over `F₀`, then for an invertible sheaf `L₀` on `X₀` (the hyperplane
sheaf of an embedding `X₀ ⊆ ℙᴺ_{k₀}`) there is a curve `T₀ ⊆ F₀`, the image of a morphism
`ℙ¹_{k₀} ⟶ X₀`, with `0 < deg_{T₀} L₀ ≤ deg_Q L₀`. -/
private theorem exists_properCurve_degree_le_of_isRationalCurve {k₀ : Type} [Field k₀]
    [IsAlgClosed k₀] [Algebra k₀ ℂ]
    {X₀ : Scheme.{0}} (s₀ : X₀ ⟶ Spec (.of k₀)) (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀)
    {X : Scheme.{0}} {s : X ⟶ Spec (.of ℂ)} {π : X ⟶ X₀}
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ))))
    {F₀ : Set X₀} (hF₀ : IsClosed F₀) (Q : ProperCurve s)
    (hQ : IsRationalCurve s
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({Q.point} : Set X))))
    (hQF : π.base '' closure {Q.point} ⊆ F₀) :
    ∃ (L₀ : X₀.Modules) (_ : SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L₀)
      (T₀ : ProperCurve s₀) (g₀ : projectiveLine k₀ ⟶ X₀),
      g₀ ≫ s₀ = projectiveLine k₀ ↘ Spec (.of k₀) ∧
      closure (Set.range g₀) = closure {T₀.point} ∧ closure {T₀.point} ⊆ F₀ ∧
      0 < T₀.degree k₀ L₀ ∧
      haveI := MMP.Mori.isInvertible_pullback_obj π L₀
      T₀.degree k₀ L₀ ≤ Q.degree ℂ ((Scheme.Modules.pullback π).obj L₀) := by
  classical
  haveI : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsProjectiveVariety k₀ s₀ := hX₀
  -- the embedding `j : X₀ ⟶ ℙᴺ_{k₀}` and its hyperplane sheaf `L₀`
  obtain ⟨N, j, hj, hjs⟩ : ∃ (N : ℕ) (j : X₀ ⟶ projectiveSpaceOverRing N (.of k₀)),
      IsClosedImmersion j ∧ j ≫ pullback.fst (terminal.from (Spec (.of k₀)))
        (terminal.from (projectiveSpaceAtUniverse.{0} N)) = s₀ := hX₀.isProjective
  set O₀ := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of k₀))
    with hO₀
  haveI : SheafOfModules.IsInvertible _ _ O₀ :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
      (Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf N _)
  set L₀ := (Scheme.Modules.pullback j).obj O₀ with hL₀
  haveI hL₀i : SheafOfModules.IsInvertible X₀.presheaf X₀.ringCatSheaf.2 L₀ :=
    MMP.Mori.isInvertible_pullback_obj j O₀
  -- the closed subvariety `E₀ = closure {π (Q)} ⊆ F₀`
  set y₀ := π Q.point with hy₀def
  have hy₀ : y₀ ∈ F₀ := hQF ⟨Q.point, subset_closure rfl, rfl⟩
  set E : X₀.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y₀} : Set X₀)) with hEdef
  haveI : IsIntegral E.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  have hErange : Set.range E.subschemeι = closure {y₀} := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  set ι₀ := E.subschemeι ≫ j with hι₀def
  set sE := E.subschemeι ≫ s₀ with hsE
  haveI : IsProper sE := inferInstance
  haveI : AlgebraicGeometry.IsProperVariety k₀ sE := {}
  have hι₀ : ι₀ ≫ pullback.fst (terminal.from (Spec (.of k₀)))
      (terminal.from (projectiveSpaceAtUniverse.{0} N)) = sE := by
    rw [hι₀def, Category.assoc, hjs]
  obtain ⟨r, G, hG, hspan⟩ := exists_homogeneous_generators (MMP.Fourfold.closedSubschemeIdeal ι₀)
  -- the embedding over `ℂ`
  have hP := isPullback_projectiveSpaceFieldExtensionMap k₀ ℂ N
  set jC : X ⟶ projectiveSpaceOverRing N (.of ℂ) := hP.lift (π ≫ j) s (by
    rw [Category.assoc, hjs]; exact h.w) with hjCdef
  have hjC1 : jC ≫ projectiveSpaceFieldExtensionMap k₀ ℂ N = π ≫ j := hP.lift_fst _ _ _
  have hjC2 : jC ≫ pullback.fst (terminal.from (Spec (.of ℂ)))
      (terminal.from (projectiveSpaceAtUniverse.{0} N)) = s := hP.lift_snd _ _ _
  have hsqj : IsPullback π jC j (projectiveSpaceFieldExtensionMap k₀ ℂ N) :=
    IsPullback.of_bot (by rw [hjC2, hjs]; exact h) hjC1.symm hP
  haveI : IsClosedImmersion jC := MorphismProperty.of_isPullback hsqj hj
  set OC := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf N (Spec (.of ℂ))
    with hOC
  haveI : SheafOfModules.IsInvertible _ _ OC :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
      (Stacks.ProjectiveSpace.isInvertibleModule_projectiveSpaceTwistingSheaf N _)
  haveI := MMP.Mori.isInvertible_pullback_obj jC OC
  haveI := MMP.Mori.isInvertible_pullback_obj π L₀
  have eO : (Scheme.Modules.pullback jC).obj OC ≅ (Scheme.Modules.pullback π).obj L₀ :=
    (Scheme.Modules.pullback jC).mapIso
      ((Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_snd N
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ)))).symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm) ≪≫
      (Scheme.Modules.pullbackComp _ _).app O₀ ≪≫
      (Scheme.Modules.pullbackCongr hjC1).app O₀ ≪≫ ((Scheme.Modules.pullbackComp π j).app O₀).symm
  -- `Q` gives a binary solution over `ℂ`
  set LQ := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({Q.point} : Set X)) with hLQ
  haveI : IsProper (LQ.subschemeι ≫ s) := hQ.2.1
  have hdegQ : degreeOn ℂ s LQ.subschemeι hQ.1.2.le ((Scheme.Modules.pullback jC).obj OC) =
      Q.degree ℂ ((Scheme.Modules.pullback π).obj L₀) :=
    degreeOn_eq_of_iso ℂ s _ _ eO
  have hampC : Scheme.Modules.IsAmple X ((Scheme.Modules.pullback jC).obj OC) :=
    isAmple_pullback_of_isFinite jC OC
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr
        (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf N (Spec (.of ℂ))))
  have hpos : 0 < degreeOn ℂ s LQ.subschemeι hQ.1.2.le ((Scheme.Modules.pullback jC).obj OC) :=
    haveI := Q.isCurve
    invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ (Q.ι ≫ s) Q.dim_le _
      (isAmple_pullback_of_isFinite Q.ι _ hampC)
  have hmem : ∀ l, (G l).map (algebraMap k₀ ℂ) ∈
      (MMP.Fourfold.closedSubschemeIdeal (LQ.subschemeι ≫ jC)).toIdeal := by
    intro l
    obtain ⟨d, hd⟩ := hG l
    refine mem_closedSubschemeIdeal_of_preimage_eq_bot _ (hd.map _) ?_
    have hE0 := preimage_eq_bot_of_mem_closedSubschemeIdeal ι₀ hd
      (hspan ▸ Ideal.subset_span ⟨l, rfl⟩)
    rw [← preimage_projBasicOpen, Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage jC]
    refine le_bot_iff.mp fun x hx => ?_
    have hx' : x ∈ (LQ.subschemeι ≫ π ≫ j) ⁻¹ᵁ projBasicOpen k₀ N (G l) := by
      rw [Scheme.Hom.comp_preimage, ← hjC1]
      exact hx
    obtain ⟨w, hw⟩ : π (LQ.subschemeι x) ∈ Set.range E.subschemeι := by
      rw [hErange]
      have hxQ : LQ.subschemeι x ∈ closure ({Q.point} : Set X) := by
        have : LQ.subschemeι x ∈ Set.range LQ.subschemeι := ⟨x, rfl⟩
        rwa [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
      have := image_closure_subset_closure_image π.continuous ⟨_, hxQ, rfl⟩
      rwa [Set.image_singleton] at this
    have : w ∈ ι₀ ⁻¹ᵁ projBasicOpen k₀ N (G l) := by
      change j (E.subschemeι w) ∈ projBasicOpen k₀ N (G l)
      rw [hw]
      exact hx'
    rw [hE0] at this
    exact absurd this (by simp)
  obtain ⟨e, he, hsol⟩ := hasBinarySolution_of_isRationalCurve s jC hjC2
    (fun l => (G l).map (algebraMap k₀ ℂ)) (fun l => (hG l).imp fun d hd => hd.map _) LQ hQ
    hmem hpos
  -- descend the solution to `k₀`, and read off a rational curve `L₀' ⊆ E₀`
  obtain ⟨L', hL', h0, hle⟩ :=
    exists_isRationalCurve_of_hasBinarySolution sE ι₀ hι₀ G hG hspan
      (hasBinarySolution_descent G hsol)
  -- the curve `T₀ ⊆ X₀`: the image of `L'`
  haveI : IsIntegral L'.subscheme := hL'.1.1
  haveI : IsProper (L'.subschemeι ≫ sE) := hL'.2.1
  set c := L'.subschemeι ≫ E.subschemeι with hc
  set t₀ := c (genericPoint L'.subscheme) with ht₀
  have hrc : Set.range c = closure {t₀} := by
    rw [← Set.image_singleton, c.isClosedEmbedding.closure_image_eq,
      (genericPoint_spec L'.subscheme).def]
    simp
  -- `L'` is, over `X₀`, the reduced closed subscheme on the closure of `t₀`
  have hker : c.ker = (curveSubschemeAtι t₀).ker := by
    rw [ker_eq_vanishingIdeal_closure_range c, hrc]
    unfold curveSubschemeAtι
    rw [Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    exact Closeds.ext (by simp only [Closeds.coe_closure, closure_closure])
  haveI : IsIso (IsClosedImmersion.lift (curveSubschemeAtι t₀) c hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq c (curveSubschemeAtι _) _
      (IsClosedImmersion.lift_fac _ _ _) hker
  set e₁ := asIso (IsClosedImmersion.lift (curveSubschemeAtι t₀) c hker.ge) with he₁def
  have he₁ : e₁.hom ≫ curveSubschemeAtι t₀ = c := IsClosedImmersion.lift_fac _ _ _
  have hcι : curveSubschemeAtι t₀ = e₁.inv ≫ c := by rw [← he₁, Iso.inv_hom_id_assoc]
  haveI hcs : IsProper (c ≫ s₀) := by rw [hc, Category.assoc]; exact hL'.2.1
  have hT₀ : IsProperCurve s₀ t₀ := by
    refine ⟨?_, ?_⟩
    · rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e₁).isHomeomorph]
      exact hL'.1.2
    · rw [hcι, Category.assoc]; infer_instance
  let T₀ : ProperCurve s₀ := ⟨t₀, hT₀⟩
  have hT₀deg : T₀.degree k₀ L₀ = degreeOn k₀ sE L'.subschemeι hL'.1.2.le
      ((Scheme.Modules.pullback ι₀).obj O₀) := by
    haveI : IsProper (T₀.ι ≫ s₀) := hT₀.isProper
    haveI := MMP.Mori.isInvertible_pullback_obj E.subschemeι L₀
    change degreeOn k₀ s₀ T₀.ι T₀.dim_le L₀ = _
    rw [← MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k₀ s₀ c T₀.ι hL'.1.2.le T₀.dim_le e₁ he₁
      L₀]
    haveI : IsProper ((L'.subschemeι ≫ E.subschemeι) ≫ s₀) := hcs
    exact
      (MMP.Threefold.Resolution.degreeOn_comp k₀ s₀ E.subschemeι L'.subschemeι hL'.1.2.le L₀).trans
        (degreeOn_eq_of_iso k₀ sE L'.subschemeι hL'.1.2.le
          ((Scheme.Modules.pullbackComp E.subschemeι j).app O₀))
  -- the morphism `g₀ : ℙ¹_{k₀} ⟶ X₀` onto `T₀`
  obtain ⟨ν, hν, hνf, hνb⟩ := hL'.2.2
  haveI : IsDominant ν := hνb.isDominant
  have hνr : Set.range ν = Set.univ := by
    rw [← ν.denseRange.closure_range, ν.isClosedMap.isClosed_range.closure_eq]
  refine ⟨L₀, hL₀i, T₀, ν ≫ c, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, Category.assoc, Category.assoc]
    exact hν
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hνr, Set.image_univ, hrc,
      closure_closure]
  · change closure {t₀} ⊆ F₀
    rw [← hrc]
    have hsub : Set.range c ⊆ Set.range E.subschemeι := by
      rintro _ ⟨x, rfl⟩
      exact ⟨L'.subschemeι x, by rw [hc, Scheme.Hom.comp_apply]⟩
    exact (hsub.trans hErange.le).trans
      (hF₀.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hy₀))
  · rw [hT₀deg]; exact h0
  · have hdQ := hpos
    rw [hdegQ] at hdQ he
    rw [hT₀deg]
    calc _ ≤ (e : ℤ) := hle
      _ ≤ ((Q.degree ℂ ((Scheme.Modules.pullback π).obj L₀)).toNat : ℤ) := by exact_mod_cast he
      _ = _ := Int.toNat_of_nonneg hdQ.le

/-! ### The theorem over a countable field -/

/-- **The contraction of a negative extremal ray** (the contraction theorem with relative
Kleiman). A `(K + B)`-negative extremal ray `R` of a projective klt pair has a contraction
`f : X ⟶ Z` onto a projective variety, on which `-(K + B)` has a relatively ample multiple; `R`
contains the class of a curve, and `1 ≤ n`. -/
private theorem exists_isContractionOfRay {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsProjectiveVariety k sX) {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hklt : IsKltPair sX n K B) (hB : 0 ≤ B) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of k)) (f : X ⟶ Z),
      IsContractionOfRay sX sZ R f ∧ MMP.Mori.IsProjectiveVariety k sZ ∧
        (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f ∧
        (∃ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R) ∧ 1 ≤ n := by
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  obtain ⟨hQ, hRay, hneg⟩ := hR
  obtain ⟨v, hv0, hRv⟩ := hRay.2
  have hface : IsNegativeExtremalFace ℝ
      (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2) R := by
    refine ⟨hRay.1, ?_, fun z hz hz0 => hneg z hz hz0⟩
    rw [hRv]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_nonneg ha hb, add_smul a b v⟩
  have hBe : B.IsEffective := DivisorWithCoeffs.isEffective_iff_nonneg.2 hB
  have : QuasiCompact sX := inferInstance
  obtain ⟨Z, sZ, ψ, hψ, hZ⟩ :=
    exists_isContractionOfFace_of_isNegativeExtremalFace (k := k) hklt hBe hface
  have hR0 : R ≠ {0} := by
    intro h
    have : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
    rw [h] at this
    exact hv0 this
  obtain ⟨C, hC⟩ :=
    exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace hklt hBe hface hR0
  have : AlgebraicGeometry.IsProjectiveVariety k sZ := hψ.isProjectiveVariety_target
  have hproj : IsProjectiveMorphism (ψ ≫ sZ) := by
    rw [hψ.comp_eq]; exact AlgebraicGeometry.IsProjectiveVariety.isProjective
  have : IsSeparated sZ := inferInstance
  have : IsProper (ψ ≫ sZ) := hψ.comp_eq ▸ inferInstance
  have : IsProper ψ := IsProper.of_comp ψ sZ
  have hcontraction : IsContraction sX sZ ψ :=
    { isNormalVariety_source := hklt.1.1
      isNormalVariety_target := hZ
      comp_eq := hψ.comp_eq
      isProjectiveMorphism := IsProjectiveMorphism.of_comp ψ sZ hproj
      surjective := (Scheme.Hom.surjective_of_isIso_app ψ hψ.isIso_app).surj
      isIso_app := hψ.isIso_app }
  have hn : 1 ≤ n := by
    have h1 := C.ι.isClosedEmbedding.isInducing.topologicalKrullDim_le
    rw [C.dim_eq, hklt.1.2.1.1] at h1
    exact_mod_cast h1
  refine ⟨Z, sZ, ψ, ⟨hcontraction, hψ.isContractedBy_iff⟩, hψ.isProjectiveVariety_target,
    hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sZ hklt.1.1 hX
      hψ.isProjectiveVariety_target ⟨n, hklt.1.2.1⟩ hQ hRay (fun u hu hu0 => ?_) ψ hψ.comp_eq
      (fun C hC => (hψ.isContractedBy_iff C).1 hC), ⟨C, hC⟩, hn⟩
  simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using hneg u hu hu0

/-- **The theorem over a subfield of `ℂ`.** Over an algebraically closed field `k₀` of
characteristic zero embedded in `ℂ`, every `(K + B)`-negative extremal ray `R₀` of a projective
klt pair contains the class of a curve `T₀ ⊆ X₀`, the image of a morphism `ℙ¹_{k₀} ⟶ X₀`, with
`0 < -(K + B) · T₀ ≤ 2n`. -/
private theorem exists_properCurve_of_ringHom_complex {k₀ : Type} [Field k₀] [IsAlgClosed k₀]
    [CharZero k₀] (σ : k₀ →+* ℂ)
    {X₀ : Scheme.{0}} [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (s₀ : X₀ ⟶ Spec (.of k₀)) (hX₀ : MMP.Mori.IsProjectiveVariety k₀ s₀) {n : ℕ}
    {K₀ : Divisor X₀} {B₀ : QDivisor X₀} (hklt : IsKltPair s₀ n K₀ B₀) (hB : 0 ≤ B₀)
    {R₀ : Set (NumericalCurveClasses s₀)}
    (hR : IsNegativeExtremalRayOf s₀ (Divisor.toQDivisor K₀ + B₀) R₀) :
    ∃ (T₀ : ProperCurve s₀) (g₀ : projectiveLine k₀ ⟶ X₀),
      g₀ ≫ s₀ = projectiveLine k₀ ↘ Spec (.of k₀) ∧
      closure (Set.range g₀) = closure {T₀.point} ∧
      OneCycle.numericalClass s₀ (T₀.cycle ℝ) ∈ R₀ ∧
      0 < -QDivisor.curveForm s₀ (Divisor.toQDivisor K₀ + B₀) hklt.1.2.2
          (OneCycle.numericalClass s₀ (T₀.cycle ℝ)) ∧
      -QDivisor.curveForm s₀ (Divisor.toQDivisor K₀ + B₀) hklt.1.2.2
          (OneCycle.numericalClass s₀ (T₀.cycle ℝ)) ≤ 2 * n := by
  classical
  obtain ⟨Z₀, t₀, f₀, hray, hZ₀, hamp₀, ⟨C₀, hC₀⟩, hn⟩ :=
    exists_isContractionOfRay s₀ hX₀ hklt hB hR
  letI : Algebra k₀ ℂ := σ.toAlgebra
  set A : Spec (.of ℂ) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ))
    with hA
  haveI : LocallyOfFiniteType s₀ := hX₀.toLocallyOfFiniteType
  haveI : QuasiCompact s₀ := hX₀.toQuasiCompact
  haveI : LocallyOfFiniteType t₀ := hZ₀.toLocallyOfFiniteType
  -- the base change `f' : X' ⟶ Z'` of the contraction to `ℂ`
  have hπ' : IsPullback (pullback.fst s₀ A) (pullback.snd s₀ A) s₀ A :=
    IsPullback.of_hasPullback s₀ A
  set X' := pullback s₀ A with hX'def
  set s' : X' ⟶ Spec (.of ℂ) := pullback.snd s₀ A with hs'
  set π' : X' ⟶ X₀ := pullback.fst s₀ A with hπ'def
  obtain ⟨hnor, hint, -⟩ := invariants_of_isPullback s₀ hπ'
  haveI : IsIntegral X' := hint.1 inferInstance
  haveI : IsNormal X' := hnor.1 inferInstance
  haveI : LocallyOfFiniteType s' := MorphismProperty.of_isPullback hπ' inferInstance
  haveI : QuasiCompact s' := MorphismProperty.of_isPullback hπ' inferInstance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian s'
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace s'
  have hX' : MMP.Mori.IsProjectiveVariety ℂ s' :=
    (isProjectiveVariety_iff_of_isPullback s₀ s' π' hπ').1 hX₀
  have hπZ : IsPullback (pullback.fst t₀ A) (pullback.snd t₀ A) t₀ A :=
    IsPullback.of_hasPullback t₀ A
  set Z' := pullback t₀ A with hZ'def
  set t' : Z' ⟶ Spec (.of ℂ) := pullback.snd t₀ A with ht'
  set πZ : Z' ⟶ Z₀ := pullback.fst t₀ A with hπZdef
  have hcomm : (π' ≫ f₀) ≫ t₀ = s' ≫ A := by
    rw [Category.assoc, hray.comp_eq]; exact hπ'.w
  set f' : X' ⟶ Z' := pullback.lift (π' ≫ f₀) s' hcomm with hf'def
  have hf'π : f' ≫ πZ = π' ≫ f₀ := pullback.lift_fst _ _ _
  have hf's : f' ≫ t' = s' := pullback.lift_snd _ _ _
  -- the base-changed pair and ray
  obtain ⟨K', hK'⟩ : ∃ K' : Divisor X', IsBaseChange π' K₀ K' :=
    MMP.ProgramBaseChange.exists_divisor_baseChange hπ' K₀
  obtain ⟨B', hB'c⟩ : ∃ B' : QDivisor X', IsBaseChange π' B₀ B' :=
    MMP.ProgramBaseChange.exists_divisor_baseChange hπ' B₀
  have hklt' : IsKltPair s' n K' B' := (isKltPair_iff_of_isPullback hπ' hX₀ hK' hB'c hB).1 hklt
  have hB' : 0 ≤ B' := (nonneg_iff_of_isPullback hπ' hX₀ hB'c).1 hB
  have hD' : IsBaseChange π' (Divisor.toQDivisor K₀ + B₀) (Divisor.toQDivisor K' + B') :=
    hK'.toQDivisor.add hB'c
  let φ' := numericalCurveClassesBaseChange s₀ s' π' hπ' hX₀
  have hφ' := numericalCurveClassesBaseChange_eq_of_isPullback s₀ s' π' hπ' hX₀
  have hray' : IsContractionOfRay s' t'
      ((φ' : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses s') '' R₀) f' :=
    (isContractionOfRay_iff hπ' hπZ hX₀ hZ₀ f₀ hray.comp_eq f' hf's hf'π _ hφ' R₀).1 hray
  have hamp' : (-(Divisor.toQDivisor K' + B')).HasRelativelyAmpleMultiple f' :=
    (hasRelativelyAmpleMultiple_iff hπ' hπZ hX₀ hZ₀ f₀ hray.comp_eq f' hf's hf'π
      hD'.neg).1 hamp₀
  -- the base change `C'` of the curve `C₀` is contracted by `f'`
  haveI : Surjective π' := surjective_of_isPullback hπ'
  obtain ⟨C', hC', -⟩ := exists_properCurve_baseChange s₀ s' π' hπ' C₀
  have hC'c : C'.IsContractedBy f' := (hray'.isContractedBy_iff C').2 ⟨_, hC₀, hφ' C₀ C' hC'⟩
  have hC'π : π' C'.point = C₀.point := map_eq_of_closure_eq hC'
  -- properness of `f'` and `f₀`
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ s' := hX'
  have hZ' : MMP.Mori.IsProjectiveVariety ℂ t' :=
    (isProjectiveVariety_iff_of_isPullback t₀ t' πZ hπZ).1 hZ₀
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ t' := hZ'
  haveI : AlgebraicGeometry.IsProjectiveVariety k₀ t₀ := hZ₀
  haveI : AlgebraicGeometry.IsProjectiveVariety k₀ s₀ := hX₀
  haveI : IsProper (f' ≫ t') := hf's ▸ inferInstance
  haveI : IsProper f' := IsProper.of_comp f' t'
  haveI : IsProper (f₀ ≫ t₀) := hray.comp_eq ▸ inferInstance
  haveI : IsProper f₀ := IsProper.of_comp f₀ t₀
  -- `f'` is not an isomorphism
  have hnt : ¬ IsIso f' := not_isIso_of_isContractedBy C' f' hC'c
  -- the fibre of `f'` through `C'`
  set z' := f' C'.point with hz'def
  have hz' : IsClosed ({z'} : Set Z') := isClosed_singleton_of_isContractedBy C' f' hC'c
  have hzdim : 0 < topologicalKrullDim (f' ⁻¹' {z'}) :=
    zero_lt_one.trans_le (one_le_topologicalKrullDim_of_subset C' fun x hx => hC'c x hx)
  obtain ⟨-, hall⟩ := exists_isRationalCurve_of_isContraction_of_isRelativelyAmple_neg s' hn
    hklt' hB' t' f' hray'.toIsContraction hnt hamp'.isRelativelyAmple_toRDivisor
  obtain ⟨Q, hQ, hQz, hQpos, hQle, -⟩ := hall z' hz' hzdim
  -- `Q` lies over the fibre `F₀ = f₀⁻¹(z₀)`
  set z₀ := f₀ C₀.point with hz₀def
  have hz₀ : IsClosed ({z₀} : Set Z₀) :=
    isClosed_singleton_of_isContractedBy C₀ f₀ ((hray.isContractedBy_iff C₀).2 hC₀)
  have hQF : π'.base '' closure {Q.point} ⊆ f₀ ⁻¹' {z₀} := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : f' x = z' := hQz hx
    change f₀ (π' x) = z₀
    rw [← Scheme.Hom.comp_apply, ← hf'π, Scheme.Hom.comp_apply, h1, hz'def,
      ← Scheme.Hom.comp_apply, hf'π, Scheme.Hom.comp_apply, hC'π]
  obtain ⟨L₀, _, T₀, g₀, hg₀, hrange, hT₀F, hT₀pos, hT₀le⟩ :=
    exists_properCurve_degree_le_of_isRationalCurve s₀ hX₀ hπ'
      (hz₀.preimage f₀.continuous) Q hQ hQF
  -- `T₀` is contracted by `f₀`, so its class lies in `R₀`
  have hT₀R : OneCycle.numericalClass s₀ (T₀.cycle ℝ) ∈ R₀ := by
    refine (hray.isContractedBy_iff T₀).1 fun x hx => ?_
    rw [hT₀F hx, hT₀F (subset_closure rfl)]
  -- `Q` is numerically the base change of a curve `Q₀` of `X₀`, with class in `R₀`
  obtain ⟨Q₀, Q₀', hQ₀', hQdeg⟩ := exists_properCurve_degree_eq_of_isPullback s₀ s' π' hπ' hX₀ Q
  have hQcl :
      OneCycle.numericalClass s' (Q₀'.cycle ℝ) = OneCycle.numericalClass s' (Q.cycle ℝ) := by
    rw [OneCycle.numericalClass_eq_iff]
    intro L _
    rw [OneCycle.degree_cycle, OneCycle.degree_cycle, hQdeg L]
  have hQc : Q.IsContractedBy f' := fun x hx => by rw [hQz hx, hQz (subset_closure rfl)]
  have hQ₀R : OneCycle.numericalClass s₀ (Q₀.cycle ℝ) ∈ R₀ := by
    obtain ⟨r, hr, hre⟩ := (hray'.isContractedBy_iff Q).1 hQc
    have : r = OneCycle.numericalClass s₀ (Q₀.cycle ℝ) :=
      φ'.injective (hre.trans ((hφ' Q₀ Q₀' hQ₀').trans hQcl).symm)
    exact this ▸ hr
  have hformQ : QDivisor.curveForm s' (Divisor.toQDivisor K' + B') hklt'.1.2.2
      (OneCycle.numericalClass s' (Q.cycle ℝ)) =
      QDivisor.curveForm s₀ (Divisor.toQDivisor K₀ + B₀) hklt.1.2.2
        (OneCycle.numericalClass s₀ (Q₀.cycle ℝ)) := by
    rw [← hQcl]
    exact curveForm_numericalClass_eq_of_isBaseChange hπ' hX₀ hD' _ _ Q₀ Q₀' hQ₀'
  haveI := MMP.Mori.isInvertible_pullback_obj π' L₀
  have hdegQ : NumericalCurveClasses.degree s₀ L₀ (OneCycle.numericalClass s₀ (Q₀.cycle ℝ)) =
      (Q.degree ℂ ((Scheme.Modules.pullback π').obj L₀) : ℝ) := by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, ← hQdeg,
      degree_pullback_eq_of_closure_eq s₀ s' π' hπ' hQ₀' L₀]
  have hdegT : NumericalCurveClasses.degree s₀ L₀ (OneCycle.numericalClass s₀ (T₀.cycle ℝ)) =
      (T₀.degree k₀ L₀ : ℝ) := by
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  obtain ⟨h1, h2⟩ := pos_and_le_of_mem_ray hR.2.1 hT₀R hQ₀R
    (NumericalCurveClasses.degree s₀ L₀)
    (-QDivisor.curveForm s₀ (Divisor.toQDivisor K₀ + B₀) hklt.1.2.2)
    (by rw [hdegT]; exact_mod_cast hT₀pos) (by rw [hdegT, hdegQ]; exact_mod_cast hT₀le)
    (by simpa only [LinearMap.neg_apply, hformQ] using hQpos)
    (b := 2 * n) (by simpa only [LinearMap.neg_apply, hformQ] using hQle)
  exact ⟨T₀, g₀, hg₀, hrange, hT₀R, h1, h2⟩

end MMP.FourfoldProofs.FourfoldProjectiveKltRayLengthCharZeroProof

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold
  MMP.ProgramBaseChange MMP.Fourfold.SmoothLocusSlopeBound

@[expose] public section

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldProjectiveKltRayLengthCharZeroProof in
/-- **Lengths of negative extremal rays in characteristic zero.** Let `k` be an algebraically
closed field of characteristic zero, `X` a projective variety over `k`, and `(X, B)` a klt pair
with `B ≥ 0` a `ℚ`-divisor and `K` a canonical divisor of dimension `n`. Every `(K + B)`-negative
extremal ray `R` of `NE̅(X)` is `ℝ_{≥0} · [T]` for a rational curve `T ⊆ X` with
`0 < -(K + B) · T ≤ 2n`. -/
@[mmp "thm_fourfold_projective_klt_ray_length_char_zero"]
public theorem exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf_of_isAlgClosed
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX] [CompactSpace X]
    {n : ℕ} {K : Divisor X} {B : QDivisor X} (hklt : MMP.Mori.IsKltPair sX n K B) (hB : 0 ≤ B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ T : ProperCurve sX,
      IsRationalCurve sX
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({T.point} : Set X))) ∧
        R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w} ∧
        0 < -QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2
            (OneCycle.numericalClass sX (T.cycle ℝ)) ∧
        -QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2
            (OneCycle.numericalClass sX (T.cycle ℝ)) ≤ 2 * n := by
  have hX : MMP.Mori.IsProjectiveVariety k sX := inferInstance
  obtain ⟨k₀, _, _, X₀, _, _, _, _, s₀, K₀, B₀, π, hπ, hX₀, hK, hBc⟩ :=
    exists_isPullback_isBaseChange sX hX hklt hB
  have hB₀ : 0 ≤ B₀ := (nonneg_iff_of_isPullback hπ hX₀ hBc).2 hB
  have hklt₀ : MMP.Mori.IsKltPair s₀ n K₀ B₀ :=
    (isKltPair_iff_of_isPullback hπ hX₀ hK hBc hB₀).2 hklt
  let φ := numericalCurveClassesBaseChange s₀ sX π hπ hX₀
  have hφ := numericalCurveClassesBaseChange_eq_of_isPullback s₀ sX π hπ hX₀
  set R₀ : Set (NumericalCurveClasses s₀) := φ.symm '' R with hR₀def
  have hRR : R = (φ : NumericalCurveClasses s₀ →ₗ[ℝ] NumericalCurveClasses sX) '' R₀ := by
    rw [hR₀def, Set.image_image]; simp
  have hD : IsBaseChange π (Divisor.toQDivisor K₀ + B₀) (Divisor.toQDivisor K + B) :=
    hK.toQDivisor.add hBc
  have hR₀ : IsNegativeExtremalRayOf s₀ (Divisor.toQDivisor K₀ + B₀) R₀ :=
    (isNegativeExtremalRayOf_iff hπ hX₀ hD φ hφ R₀).2 (hRR ▸ hR)
  obtain ⟨σ⟩ := MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.1 k₀
  obtain ⟨T₀, g₀, hg₀, hrange, hT₀R, hpos, hle⟩ :=
    exists_properCurve_of_ringHom_complex σ s₀ hX₀ hklt₀ hB₀ hR₀
  obtain ⟨T, hT, -⟩ := exists_properCurve_baseChange s₀ sX π hπ T₀
  have hTR : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R := hRR ▸ ⟨_, hT₀R, hφ T₀ T hT⟩
  have hform : QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2
      (OneCycle.numericalClass sX (T.cycle ℝ)) =
      QDivisor.curveForm s₀ (Divisor.toQDivisor K₀ + B₀) hklt₀.1.2.2
        (OneCycle.numericalClass s₀ (T₀.cycle ℝ)) :=
    curveForm_numericalClass_eq_of_isBaseChange hπ hX₀ hD _ _ T₀ T hT
  have hT0 : OneCycle.numericalClass sX (T.cycle ℝ) ≠ 0 := by
    intro h0
    rw [hform.symm, h0, map_zero, neg_zero] at hpos
    exact lt_irrefl _ hpos
  haveI : IsSeparated s₀ := hX₀.toIsSeparated
  refine ⟨T, isRationalCurve_of_isPullback hπ g₀ hg₀ T₀ hrange T hT,
    eq_ray_of_mem hR.2.1 hTR hT0, by rwa [hform], by rwa [hform]⟩

end MMP.Fourfold

end
