module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
public import MMP.AlgebraicGeometry.Morphisms.Birational.Transform
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import MMP.AlgebraicGeometry.Divisor.LinearSeries
public import MMP.AlgebraicGeometry.Modules.AssociatedPoints
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Divisorial
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.ProjectiveSpace.ProjComparison
import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic

/-!
# Curve classes, strip base loci, small models, and cyclic covers

This file collects five auxiliary results from Kollár–Mori that are used in the proofs of the
cone and rationality theorems and in the construction of cyclic covers.

* **Relative curve classes.** For a morphism `f : X ⟶ Y` of `k`-schemes, the intersection
  number `(z · D)` of a class `z ∈ N₁(X/Y)` with an `ℝ`-Cartier divisor `D` is well defined and
  `ℝ`-bilinear. If `X` is integral and `N₁(X/Y)` is finite dimensional, the forms
  `z ↦ (z · D)` span the dual space, and the topology of `N₁(X/Y)` is the Euclidean one.
* **Strip base loci.** For a rationality datum `(X, Δ, a, H)` with nef threshold `r`, the base
  locus `L(p, q) = Bs|pH + qa(K_X + Δ)|` is nonempty whenever `p > 0` and `aq - rp > 0`.
* **Small proper models.** If `g : Z ⟶ Y` is proper and its exceptional set has codimension at
  least two, then `𝒪_Y(B) = g_* 𝒪_Z(g⁻¹_* B)` inside `K(Y) = K(Z)`.
* **Sections avoiding associated points.** On a projective scheme with an ample line bundle
  `L`, take a coherent sheaf `F` and a closed point `x` that is not an associated point of
  `F`. Then for `r ≫ 0`, some section of `L^{⊗r}` vanishes at `x` and multiplication by it is
  injective on `F`.
* **The local form of a cyclic cover.** If `g` is a local equation of `M` on `U`, then the
  algebra of the cyclic cover defined by `(M, m, φ)` is `𝒪_X(U)[t]/(tᵐ - gᵐφ)` over `U`.

## Main results

* `MMP.Mori.RelativeNumericalCurveClasses.intersectionNumberEq_wellDefined`
* `MMP.Mori.RelativeNumericalCurveClasses.span_intersectionNumber_eq_top_and_isModuleTopology`
* `MMP.Mori.IsRationalityDatum.stripBaseLocus_ne_bot`
* `MMP.Mori.Divisor.mem_divisorialSubmodule_inverseTransformDivisor_iff`
* `MMP.Mori.eventually_exists_section_notMem_nonvanishingLocus_mono`
* `MMP.Mori.DivisorialCyclicCover.exists_algEquiv_adjoinRoot_of_isLocalEquation`

## Implementation notes

* The equality `𝒪_Y(B) = g_* 𝒪_Z(g⁻¹_* B)` is stated section by section, through the function
  field map `AlgebraicGeometry.functionFieldMap g` of the dominant morphism `g`.
* A section `s` *vanishes at* `x` when `x ∉ Stacks.Ample.nonvanishingLocus M s`. Multiplication
  by `s` is `(ρ_ F).inv ≫ F ◁ φ`, where `φ : 𝒪_X ⟶ M` corresponds to `s` under
  `SheafOfModules.unitHomEquiv`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Ex. 2.16,
  2.50, 2.52, proof of Theorem 3.5 (Step 4), proof of Corollary 5.72, Lemma 6.2
* [R. Hartshorne, *Algebraic geometry*], II.5.17, II.7.6
-/

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### The pairing `N₁(X/Y) × Div(X)_ℝ → ℝ` and the topology of `N₁(X/Y)` -/

section RelativeCurveClasses

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

/-- The relative intersection number `(z · D)` is additive in the divisor `D`. -/
private lemma intersectionNumber_add (z : RelativeNumericalCurveClasses sX f)
    (D₁ D₂ : KCartierDivisor ℝ X) :
    RelativeNumericalCurveClasses.intersectionNumber (D₁ + D₂) z =
      RelativeNumericalCurveClasses.intersectionNumber D₁ z +
        RelativeNumericalCurveClasses.intersectionNumber D₂ z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  simp [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber]

/-- The relative intersection number `(z · D)` is homogeneous in the divisor `D`. -/
private lemma intersectionNumber_smul (c : ℝ) (z : RelativeNumericalCurveClasses sX f)
    (D : KCartierDivisor ℝ X) :
    RelativeNumericalCurveClasses.intersectionNumber (c • D) z =
      c * RelativeNumericalCurveClasses.intersectionNumber D z := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  simp [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber]

/-- On an integral scheme, the degree form of an invertible sheaf on `N₁(X/Y)` is the
intersection form of a Cartier divisor. -/
private lemma exists_degree_eq_intersectionNumber [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    ∃ E : X.CartierDivisor, RelativeNumericalCurveClasses.degree sX f L =
      RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) := by
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  refine ⟨E, LinearMap.ext fun z => ?_⟩
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.degree_relativeNumericalClass,
    RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree,
    OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- The degree forms of invertible sheaves separate the points of `N₁(X/Y)`: a nonzero class
has nonzero degree against some invertible sheaf. -/
private lemma exists_degree_ne_zero {z : RelativeNumericalCurveClasses sX f} (hz : z ≠ 0) :
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      RelativeNumericalCurveClasses.degree sX f L z ≠ 0 := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  by_contra! h
  exact hz <| (Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => h L inferInstance)

/-- `N₁(X/Y)` is Hausdorff, the degree forms separating its points. -/
private lemma t2Space : T2Space (RelativeNumericalCurveClasses sX f) := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨L, _, hL⟩ := exists_degree_ne_zero (sub_ne_zero.mpr hxy)
  rw [map_sub, sub_ne_zero] at hL
  exact separated_by_continuous (RelativeNumericalCurveClasses.continuous_degree sX f L) hL

end RelativeCurveClasses

/-- For every relative class `z ∈ N₁(X/Y)` and `ℝ`-Cartier divisor `D` there is exactly one
`r` with `(z · D) = r`, and this value is given by an `ℝ`-bilinear form on
`N₁(X/Y) × Div(X)_ℝ`. -/
@[mmp "lem_km1b_relative_class_pairing_well_defined"]
public theorem RelativeNumericalCurveClasses.intersectionNumberEq_wellDefined
    {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y) :
    (∀ (z : RelativeNumericalCurveClasses sX f) (D : KCartierDivisor ℝ X),
        ∃! r : ℝ, z.IntersectionNumberEq D r) ∧
      ∃ B : RelativeNumericalCurveClasses sX f →ₗ[ℝ] KCartierDivisor ℝ X →ₗ[ℝ] ℝ,
        ∀ (z : RelativeNumericalCurveClasses sX f) (D : KCartierDivisor ℝ X) (r : ℝ),
          z.IntersectionNumberEq D r ↔ B z D = r :=
  ⟨fun z D => by
    simpa only [RelativeNumericalCurveClasses.intersectionNumberEq_iff] using existsUnique_eq',
  LinearMap.mk₂ ℝ (fun z D => RelativeNumericalCurveClasses.intersectionNumber D z)
    (fun _ _ _ => map_add _ _ _) (fun _ _ _ => map_smul _ _ _) intersectionNumber_add
    intersectionNumber_smul,
  RelativeNumericalCurveClasses.intersectionNumberEq_iff⟩

/-- If `X` is integral and `N₁(X/Y)` is finite dimensional, the forms `z ↦ (z · D)`, `D` an
`ℝ`-Cartier divisor on `X`, span `N₁(X/Y)^*`, and the topology of `N₁(X/Y)` is its canonical
topology as a finite-dimensional real vector space. -/
@[mmp "lem_km1b_relative_numerical_topology_is_euclidean"]
public theorem RelativeNumericalCurveClasses.span_intersectionNumber_eq_top_and_isModuleTopology
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) (f : X ⟶ Y)
    [FiniteDimensional ℝ (RelativeNumericalCurveClasses sX f)] :
    Submodule.span ℝ (Set.range fun D : KCartierDivisor ℝ X =>
        (RelativeNumericalCurveClasses.intersectionNumber D :
          Module.Dual ℝ (RelativeNumericalCurveClasses sX f))) = ⊤ ∧
      IsModuleTopology ℝ (RelativeNumericalCurveClasses sX f) := by
  refine ⟨Submodule.span_eq_top_of_ne_zero fun z hz => ?_, ?_⟩
  · obtain ⟨L, _, hL⟩ := exists_degree_ne_zero hz
    obtain ⟨E, hE⟩ := exists_degree_eq_intersectionNumber (sX := sX) (f := f) L
    exact ⟨_, ⟨KCartierDivisor.ofCartier ℝ E, rfl⟩, by simpa only [← hE] using hL⟩
  · haveI : IsTopologicalAddGroup (RelativeNumericalCurveClasses sX f) :=
      topologicalAddGroup_iInf fun L => topologicalAddGroup_iInf fun _ =>
        topologicalAddGroup_induced _
    haveI : ContinuousSMul ℝ (RelativeNumericalCurveClasses sX f) :=
      continuousSMul_iInf fun L => continuousSMul_iInf fun _ => continuousSMul_induced _
    haveI := t2Space (sX := sX) (f := f)
    exact isModuleTopologyOfFiniteDimensional

/-! ### Strip base loci above the nef threshold

If `L(p, q) = Bs|pH + qa(K_X + Δ)|` were empty, every curve `C` would contain a point where some
section of `𝒪_X(pH + qa(K_X + Δ))` does not vanish. The divisor of zeros of that section is
effective, linearly equivalent to `pH + qa(K_X + Δ)`, and does not contain `C`, so the degree
on `C` is `≥ 0`. Dividing by `p`, the divisor `H + (aq/p)(K_X + Δ)` would be nef with
`aq/p > r`, which contradicts the nef threshold. -/

section StripBaseLocus

open TopologicalSpace

/-- The round-down of an integral `ℚ`-divisor is the divisor itself. -/
private theorem roundDown_toQDivisor {X : Scheme.{u}} (E : Divisor X) :
    (Divisor.toQDivisor E).roundDown = E :=
  DivisorWithCoeffs.ext' fun _ => by simp

/-- A Cartier divisor has nonnegative degree on a curve `C` meeting the complement of its base
locus: the divisor of zeros of a section not vanishing at a point of `C` is an effective Cartier
divisor, linearly equivalent to `M`, not containing `C`. -/
private theorem degreeOn_nonneg_of_notMem_baseLocus {k : Type u} [Field k] {C X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] (i : C ⟶ X) [IsProper (i ≫ sX)] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1) {M : Divisor X} (hM : M.IsCartier) {c : C}
    (hc : i c ∉ (M.baseLocus : Set X)) : 0 ≤ M.degreeOn k sX i hdim hM := by
  rw [Divisor.mem_baseLocus_iff] at hc
  push Not at hc
  obtain ⟨σ, hσ, hcσ⟩ := hc
  have hP := Divisor.isCartier_principalDivisor (Divisor.isUnit_sectionToRationalFunctions hσ).unit
  have h0 : 0 ≤ (MMP.Mori.principalDivisor _ + M).degreeOn k sX i hdim (hP.add hM) :=
    (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX i hdim _ (hP.add hM)
      (M.zeroDivisor_nonneg σ hσ) ⟨c, hcσ⟩).1
  rwa [Divisor.degreeOn_add k sX i hdim _ _ hP hM,
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX i hdim hP
      (Divisor.linearlyEquivalent_principalDivisor_zero _), zero_add] at h0

/-- **KM 3.4, Step 4.** For a rationality datum `(X, Δ, a, H)` with nef threshold `r` of `H` with
respect to `K_X + Δ`, and integers `p > 0`, `q` with `aq - rp > 0`, the strip base locus
`L(p, q) = Bs|pH + qa(K_X + Δ)|` is nonempty: `pH + qa(K_X + Δ)` is not nef, hence its complete
linear system is not basepoint free. -/
@[mmp "lem_km3b_strip_not_free"]
public theorem IsRationalityDatum.stripBaseLocus_ne_bot {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {a : ℤ} {H : Divisor X} (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    {p q : ℤ} (hp : 0 < p) (hpq : 0 < (a * q : ℝ) - r * p) :
    stripBaseLocus K Δ a H p q ≠ ⊥ := by
  intro hfree
  obtain ⟨E, hEA, hEC⟩ := hD.isCartierDivisor
  have hHC := hD.isCartier_H
  have ha := hD.pos
  have hM : stripDivisor K Δ a H p q = p • H + q • E := by
    simp only [stripDivisor, ← hEA, roundDown_toQDivisor]
  obtain ⟨hHq, hKq, -⟩ := hr.1
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine hr.2 ((a * q : ℝ) / p) (by rw [lt_div_iff₀ hp']; linarith)
    ⟨hHq, hKq, fun C i _ _ _ hC => ?_⟩
  obtain ⟨c⟩ : Nonempty C := inferInstance
  have hc : i c ∉ ((p • H + q • E).baseLocus : Set X) := by
    rw [← hM, ← stripBaseLocus, hfree]
    simp
  have h0 := degreeOn_nonneg_of_notMem_baseLocus sX i hC.le ((hHC.zsmul p).add (hEC.zsmul q)) hc
  rw [Divisor.degreeOn_add k sX i hC.le _ _ (hHC.zsmul p) (hEC.zsmul q),
    MMP.Fourfold.degreeOn_zsmul sX i hC.le H hHC p,
    MMP.Fourfold.degreeOn_zsmul sX i hC.le E hEC q] at h0
  rw [QDivisor.intersectionNumber_toQDivisor k sX i hC.le H hHC hHq,
    QDivisor.intersectionNumber_eq_of_smul k sX i hC.le _ hKq (m := a.toNat) (by omega) E hEC
      (by rw [Int.toNat_of_nonneg ha.le]; exact hEA)]
  have hat : ((a.toNat : ℕ) : ℚ) = (a : ℚ) := by exact_mod_cast Int.toNat_of_nonneg ha.le
  have h0' : (0 : ℝ) ≤ p * (H.degreeOn k sX i hC.le hHC : ℝ) +
      q * (E.degreeOn k sX i hC.le hEC : ℝ) := by exact_mod_cast h0
  have ha' : (a : ℝ) ≠ 0 := by positivity
  rw [hat]
  push_cast
  calc (0 : ℝ) ≤ (p * (H.degreeOn k sX i hC.le hHC : ℝ) +
        q * (E.degreeOn k sX i hC.le hEC : ℝ)) / p := by positivity
    _ = _ := by field_simp

end StripBaseLocus

/-! ### Divisorial sheaves and small proper models

Let `V ⊆ Y` be the locus over which `g` is an isomorphism. The generic point of a prime divisor
`F` of `Z` lies outside `Ex(g)`, so `g(η_F) ∈ V` is the generic point of a prime divisor `E` of
`Y`. Conversely the generic point of every prime divisor of `Y` lies in `V`. Under this
correspondence `g⁻¹_* E = F`, and `g` is a local isomorphism at `η_F`. So the conditions
`div_Z(g^* φ) + g⁻¹_* B ≥ 0` and `div_Y(φ) + B ≥ 0` are the same conditions, read on
corresponding prime divisors. -/

section SmallModel

open TopologicalSpace Opposite Order

section RationalFunctions

variable {X : Scheme.{u}} [IsIntegral X]

private theorem germ_eq_rationalFunctionsEquivFunctionField_symm (U : X.Opens) (s : Γ(X, U))
    (h : genericPoint X ∈ U) (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ U) :
    (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s) Z =
      X.presheaf.germ U (componentGenericPoint X Z) hZ s := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  let D : Stacks.Chow.DenseOpen X := ⟨U, U.isOpen.dense ⟨_, h⟩⟩
  have key : (rationalFunctionsEquivFunctionField X).symm (X.presheaf.germ U (genericPoint X) h s)
      = (Stacks.Chow.rationalFunctionsEquivStalks X).1 (Stacks.Chow.ofSection X D s) := by
    rw [RingEquiv.symm_apply_eq, ← (Stacks.Chow.rationalFunctionsEquivFunctionField X).2 D s h]
    change _ = (Stacks.Chow.rationalFunctionsEquivFunctionField X).1
      ((Stacks.Chow.rationalFunctionsEquivStalks X).1.symm _)
    rw [RingEquiv.symm_apply_apply]
  rw [key]
  exact (Stacks.Chow.rationalFunctionsEquivStalks X).2 D s Z hZ

private theorem componentGenericPoint_eq (Z : irreducibleComponents X) :
    componentGenericPoint X Z = genericPoint X := by
  have hZ : Z.1 = Set.univ := by
    simpa [irreducibleComponents_eq_singleton] using Z.2
  have h1 := isGenericPoint_componentGenericPoint X Z
  rw [hZ] at h1
  exact h1.eq (genericPoint_spec X)

private theorem stalkSpecializes_rationalFunctionsEquivFunctionField_symm
    (Z : irreducibleComponents X) (φ : X.functionField) :
    (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
        (Set.mem_univ (componentGenericPoint X Z)))).hom
      ((rationalFunctionsEquivFunctionField X).symm φ Z) = φ := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) φ
  have hZ : componentGenericPoint X Z ∈ U := componentGenericPoint_eq Z ▸ hx
  rw [germ_eq_rationalFunctionsEquivFunctionField_symm U s hx Z hZ,
    TopCat.Presheaf.germ_stalkSpecializes_apply]

end RationalFunctions

section Valuation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

private theorem valuation_rationalFunctionsEquivFunctionField_symm (E : MMP.Mori.PrimeDivisor X)
    (φ : X.functionField) :
    E.valuation ((rationalFunctionsEquivFunctionField X).symm φ E.component) =
      X.ordHom E.genericPoint E.coheight_genericPoint φ := by
  set a := (rationalFunctionsEquivFunctionField X).symm φ E.component
  let ψ := (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
        (Set.mem_univ (componentGenericPoint X E.component)))).hom
  have hψ : ψ a = φ := stalkSpecializes_rationalFunctionsEquivFunctionField_symm _ φ
  letI := E.toComponent.hom.toAlgebra
  haveI := isFractionRing_stalkToRationalFunctions E.genericPoint_mem_component
  haveI : Ring.KrullDimLE 1 E.localRing := krullDimLE_of_coheight_le E.coheight_genericPoint.le
  let alg1 := IsLocalization.algEquiv (nonZeroDivisors E.localRing)
    (X.presheaf.stalk (componentGenericPoint X E.component)) (FractionRing E.localRing)
  let Eq := (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
    X.functionField).toRingEquiv
  have hEq : ∀ r : E.localRing, Eq (algebraMap E.localRing (FractionRing E.localRing) r) =
      algebraMap E.localRing X.functionField (RingEquiv.refl E.localRing r) := fun r =>
    (IsLocalization.algEquiv (nonZeroDivisors E.localRing) (FractionRing E.localRing)
      X.functionField).commutes r
  have hcomp : Eq (alg1 a) = φ := by
    rw [← hψ]
    have : (Eq.toRingHom.comp alg1.toRingEquiv.toRingHom) = ψ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors E.localRing) ?_
      ext r
      simp only [RingHom.comp_apply]
      change Eq (alg1 (algebraMap _ _ r)) = _
      rw [AlgEquiv.commutes, hEq]
      change _ = ψ ((X.presheaf.stalkSpecializes E.specializes_genericPoint).hom r)
      simp only [ψ]
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
      rfl
    exact congrArg (fun f => f a) this
  change Ring.ordFrac E.localRing (alg1 a) = Ring.ordFrac E.localRing φ
  rw [← hcomp]
  exact (Stacks.Chow.ordFrac_congr (RingEquiv.refl E.localRing) Eq hEq (alg1 a)).symm

private theorem ordGE_iff (E : MMP.Mori.PrimeDivisor X) (n : ℤ) (φ : X.functionField) :
    E.OrdGE n ((rationalFunctionsEquivFunctionField X).symm φ E.component) ↔
      φ = 0 ∨ n ≤ X.ord φ E.genericPoint := by
  unfold MMP.Mori.PrimeDivisor.OrdGE
  rw [valuation_rationalFunctionsEquivFunctionField_symm]
  have h0 : (rationalFunctionsEquivFunctionField X).symm φ E.component = 0 ↔ φ = 0 := by
    constructor
    · intro h
      rw [← stalkSpecializes_rationalFunctionsEquivFunctionField_symm E.component φ, h, map_zero]
    · rintro rfl
      rw [map_zero]
      rfl
  rw [h0]
  by_cases hφ : φ = 0
  · simp [hφ]
  · simp only [hφ, false_or]
    rw [(Scheme.ord_eq_iff E.coheight_genericPoint hφ).mp rfl]
    exact WithZero.exp_le_exp

end Valuation

section Transport

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

private theorem isIso_stalkMap_of_mem_biregularLocus {x : Z} (hx : g x ∈ biregularLocus g) :
    IsIso (g.stalkMap x) := by
  set V := biregularLocus g
  haveI : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  let p : (g ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  haveI : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hc : IsIso (((g ⁻¹ᵁ V).ι ≫ g).stalkMap p) := inferInstance
  rw [Scheme.Hom.stalkMap_comp (g ⁻¹ᵁ V).ι g p] at hc
  have hι : IsIso ((g ⁻¹ᵁ V).ι.stalkMap p) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap ((g ⁻¹ᵁ V).ι p))
    ((g ⁻¹ᵁ V).ι.stalkMap p) hι hc

private theorem specializes_of_mem_biregularLocus {z z' : Z} (hz : g z ∈ biregularLocus g)
    (hz' : g z' ∈ biregularLocus g) (h : g z' ⤳ g z) : z' ⤳ z := by
  set V := biregularLocus g
  haveI : IsIso (g ∣_ V) := isBiregular_biregularLocus g
  let p : (g ⁻¹ᵁ V).toScheme := ⟨z, hz⟩
  let p' : (g ⁻¹ᵁ V).toScheme := ⟨z', hz'⟩
  have hι : ∀ q : (g ⁻¹ᵁ V).toScheme, V.ι ((g ∣_ V) q) = g ((g ⁻¹ᵁ V).ι q) := fun q => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have h1 : V.ι ((g ∣_ V) p') ⤳ V.ι ((g ∣_ V) p) := by rwa [hι, hι]
  exact ((g ∣_ V).isOpenEmbedding.isInducing.specializes_iff.mp
    (V.ι.isOpenEmbedding.isInducing.specializes_iff.mp h1)).map (g ⁻¹ᵁ V).ι.continuous

private theorem ord_functionFieldMap [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsDominant g] (hgen : g (genericPoint Z) ∈ biregularLocus g)
    {x : Z} (hx : g x ∈ biregularLocus g) (φ : Y.functionField) :
    Z.ord (functionFieldMap g φ) x = Y.ord φ (g x) := by
  rw [← dominantFunctionFieldMap_eq_functionFieldMap]
  exact Stacks.Chow.ord_dominantFunctionFieldMap_of_isIso_stalkMap g
    (isIso_stalkMap_of_mem_biregularLocus g hgen) x (isIso_stalkMap_of_mem_biregularLocus g hx)
    (MMP.Positivity.coheight_map_of_mem_biregularLocus g hx) φ

private theorem eq_of_specializes_of_coheight_eq_one {T : Scheme.{u}} {x y : T} (h : x ⤳ y)
    (hx : coheight x = 1) (hy : coheight y = 1) : x = y := by
  by_contra hne
  have hlt : y < x := lt_of_le_not_ge (h : y ≤ x) (fun h' => hne (h.antisymm h').eq)
  have := Order.coheight_strictAnti hlt (by rw [hx]; exact ENat.one_lt_top)
  rw [hx, hy] at this
  exact lt_irrefl _ this

private theorem idealSheaf_eq_vanishingIdeal_support {T : Scheme.{u}}
    (D : MMP.Mori.PrimeDivisor T) :
    D.idealSheaf = Scheme.IdealSheafData.vanishingIdeal D.idealSheaf.support := by
  have := D.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl

private theorem genericPoint_mem_support {T : Scheme.{u}} (D : MMP.Mori.PrimeDivisor T) :
    D.genericPoint ∈ (D.idealSheaf.support : Set T) := by
  rw [← AlgebraicGeometry.PrimeDivisor.support, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

private theorem inverseTransformPrimeDivisor_eq_some_iff_of_map_genericPoint
    {E : MMP.Mori.PrimeDivisor Y} {F : MMP.Mori.PrimeDivisor Z}
    (hF : g F.genericPoint = E.genericPoint) (hV : E.genericPoint ∈ biregularLocus g)
    (E' : MMP.Mori.PrimeDivisor Y) :
    inverseTransformPrimeDivisor g E' = some F ↔ E' = E := by
  constructor
  · intro h
    have hsupp := support_inverseTransformPrimeDivisor h
    have hmem : F.genericPoint ∈ (inverseTransform g E'.idealSheaf.support : Set Z) := by
      have := genericPoint_mem_support F
      rwa [← AlgebraicGeometry.PrimeDivisor.support, hsupp] at this
    have hsub : (inverseTransform g E'.idealSheaf.support : Set Z) ⊆
        g ⁻¹' (E'.idealSheaf.support : Set Y) :=
      closure_minimal (fun z hz => hz.1)
        ((E'.idealSheaf.support).isClosed.preimage g.continuous)
    have h1 : E.genericPoint ∈ (E'.idealSheaf.support : Set Y) := hF ▸ hsub hmem
    have h2 : E'.genericPoint ⤳ E.genericPoint := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_specializes_of_coheight_eq_one h2 E'.coheight_genericPoint E.coheight_genericPoint)
  · rintro rfl
    rw [inverseTransformPrimeDivisor_eq_some_iff]
    refine ⟨⟨E'.genericPoint, genericPoint_mem_support E', hV⟩, ?_⟩
    rw [idealSheaf_eq_vanishingIdeal_support F, inverseTransformIdeal]
    congr 1
    ext1
    change (F.idealSheaf.support : Set Z) =
      closure (g ⁻¹' ((E'.idealSheaf.support : Set Y) ∩ biregularLocus g))
    rw [← AlgebraicGeometry.PrimeDivisor.support, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    apply le_antisymm
    · refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, ?_⟩) <;>
        change g F.genericPoint ∈ _ <;> rw [hF]
      exacts [genericPoint_mem_support E', hV]
    · refine closure_minimal (fun z hz => ?_) isClosed_closure
      have hz1 : E'.genericPoint ⤳ g z := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hz.1
      rw [← hF] at hz1
      exact specializes_iff_mem_closure.mp (specializes_of_mem_biregularLocus g hz.2 (hF ▸ hV) hz1)

private theorem coeff_inverseTransformDivisor
    {E : MMP.Mori.PrimeDivisor Y} {F : MMP.Mori.PrimeDivisor Z}
    (hF : g F.genericPoint = E.genericPoint) (hV : E.genericPoint ∈ biregularLocus g)
    (B : Divisor Y) : (inverseTransformDivisor g B).coeff F = B.coeff E := by
  induction B using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, h, h']
  | single E' r =>
    rw [inverseTransformDivisor_single]
    by_cases hE : E' = E
    · subst hE
      rw [(inverseTransformPrimeDivisor_eq_some_iff_of_map_genericPoint g hF hV E').mpr rfl]
      simp [DivisorWithCoeffs.coeff_single_self]
    · rw [DivisorWithCoeffs.coeff_single_of_ne hE]
      cases hc : inverseTransformPrimeDivisor g E' with
      | none => rfl
      | some F' =>
        have hF' : F' ≠ F := by
          rintro rfl
          exact hE ((inverseTransformPrimeDivisor_eq_some_iff_of_map_genericPoint g hF hV E').mp hc)
        exact DivisorWithCoeffs.coeff_single_of_ne hF' r

/-- If `Ex(g)` has codimension at least two, every point of `Z` of coheight at most one maps
into the biregular locus of `g`. -/
private theorem map_mem_biregularLocus_of_coheight_le_one
    (hEx : 2 ≤ closedsCodimension (exceptionalSet g)) {z : Z} (hz : coheight z ≤ 1) :
    g z ∈ biregularLocus g := by
  by_contra h
  exact absurd ((MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hEx
    (mem_exceptionalSet.mpr h)).trans hz) (by decide)

private theorem bijective_functionFieldMap [IsIntegral Y] [IsIntegral Z] [IsDominant g]
    (hgen : g (genericPoint Z) ∈ biregularLocus g) : Function.Bijective (functionFieldMap g) := by
  rw [← dominantFunctionFieldMap_eq_functionFieldMap]
  exact (Stacks.Chow.functionFieldEquiv_of_isIso_stalkMap g
    (isIso_stalkMap_of_mem_biregularLocus g hgen)).bijective

/-- A prime divisor of `Y` whose generic point lies in the biregular locus of `g` is the image
of a prime divisor of `Z`. -/
private theorem exists_primeDivisor_map_genericPoint_eq {E : MMP.Mori.PrimeDivisor Y}
    (hE : E.genericPoint ∈ biregularLocus g) :
    ∃ F : MMP.Mori.PrimeDivisor Z, g F.genericPoint = E.genericPoint := by
  haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  let q : (biregularLocus g).toScheme := ⟨E.genericPoint, hE⟩
  let p := (inv (g ∣_ biregularLocus g)) q
  have hp : (g ∣_ biregularLocus g) p = q := by
    simp only [p]
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hgz : g ((g ⁻¹ᵁ biregularLocus g).ι p) = E.genericPoint := by
    rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hp]
    rfl
  have hcz : coheight ((g ⁻¹ᵁ biregularLocus g).ι p) = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g (hgz ▸ hE), hgz]
    exact E.coheight_genericPoint
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcz,
    (congrArg g (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcz)).trans hgz⟩

/-- The image of the generic point of a prime divisor of `Z` lying in the biregular locus of
`g` is the generic point of a prime divisor of `Y`. -/
private theorem exists_primeDivisor_eq_map_genericPoint {F : MMP.Mori.PrimeDivisor Z}
    (hF : g F.genericPoint ∈ biregularLocus g) :
    ∃ E : MMP.Mori.PrimeDivisor Y, g F.genericPoint = E.genericPoint := by
  have hc : coheight (g F.genericPoint) = 1 :=
    (MMP.Positivity.coheight_map_of_mem_biregularLocus g hF).trans F.coheight_genericPoint
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm⟩

/-- On corresponding prime divisors `F ↦ E`, the condition `div(g^* φ) + g⁻¹_* B ≥ 0` at `F`
is the condition `div(φ) + B ≥ 0` at `E`. -/
private theorem orderCondition_iff_of_map_genericPoint [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] [IsDominant g]
    (hgen : g (genericPoint Z) ∈ biregularLocus g)
    {E : MMP.Mori.PrimeDivisor Y} {F : MMP.Mori.PrimeDivisor Z}
    (hF : g F.genericPoint = E.genericPoint) (hV : E.genericPoint ∈ biregularLocus g)
    (B : Divisor Y) (φ : Y.functionField) :
    (functionFieldMap g φ = 0 ∨
        -(inverseTransformDivisor g B).coeff F ≤ Z.ord (functionFieldMap g φ) F.genericPoint) ↔
      (φ = 0 ∨ -B.coeff E ≤ Y.ord φ E.genericPoint) := by
  rw [coeff_inverseTransformDivisor g hF hV B, ord_functionFieldMap g hgen (hF ▸ hV) φ, hF,
    map_eq_zero_iff _ (functionFieldMap g).injective]

end Transport

private theorem mem_divisorialSubmodule_iff {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (U : X.Opens) (φ : X.functionField) :
    (rationalFunctionsPresheaf X).map (homOfLE le_top : U ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv X).symm
          ((rationalFunctionsEquivFunctionField X).symm φ)) ∈ D.divisorialSubmodule U ↔
      ∀ E : MMP.Mori.PrimeDivisor X, E.genericPoint ∈ U →
        (φ = 0 ∨ -D.coeff E ≤ X.ord φ E.genericPoint) := by
  rw [Divisor.mem_divisorialSubmodule]
  refine forall_congr' fun E => ?_
  rw [← ordGE_iff]
  exact ⟨fun h hU => h ⟨E.genericPoint, genericPoint_mem_support E, hU⟩,
    fun h hne => h (E.genericPoint_mem_of_nonempty hne)⟩

/-- **KM Lemma 6.2, (2) ⇒ (1), first claim.** Let `g : Z ⟶ Y` be a proper dominant morphism of
locally Noetherian normal integral schemes whose exceptional set has codimension at least two,
and `B` a divisor on `Y`. Then `𝒪_Y(B) = g_* 𝒪_Z(g⁻¹_* B)` inside `K(Y) = K(Z)`: for every open
`U ⊆ Y` and every `φ ∈ K(Y)`, `φ` is a section of `𝒪_Y(B)` over `U` if and only if
`functionFieldMap g φ` is a section of `𝒪_Z(g⁻¹_* B)` over `g⁻¹(U)`. -/
@[mmp "lem_km3c_small_model_pushforward"]
public theorem Divisor.mem_divisorialSubmodule_inverseTransformDivisor_iff {Y Z : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (g : Z ⟶ Y)
    [IsProper g] [IsDominant g] (hEx : 2 ≤ closedsCodimension (exceptionalSet g))
    (B : Divisor Y) (U : Y.Opens) (φ : Y.functionField) :
    (rationalFunctionsPresheaf Y).map (homOfLE le_top : U ⟶ ⊤).op
        ((rationalFunctionsPresheafTopEquiv Y).symm
          ((rationalFunctionsEquivFunctionField Y).symm φ)) ∈ B.divisorialSubmodule U ↔
      (rationalFunctionsPresheaf Z).map (homOfLE le_top : g ⁻¹ᵁ U ⟶ ⊤).op
          ((rationalFunctionsPresheafTopEquiv Z).symm
            ((rationalFunctionsEquivFunctionField Z).symm (functionFieldMap g φ))) ∈
        Divisor.divisorialSubmodule (inverseTransformDivisor g B) (g ⁻¹ᵁ U) := by
  have hgen : g (genericPoint Z) ∈ biregularLocus g :=
    map_mem_biregularLocus_of_coheight_le_one g hEx <| by
      rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)]
      exact zero_le_one
  have hYV (E : MMP.Mori.PrimeDivisor Y) : E.genericPoint ∈ biregularLocus g :=
    MMP.Positivity.mem_biregularLocus_of_coheight_le_one g (bijective_functionFieldMap g hgen)
      hEx E.coheight_genericPoint.le
  rw [mem_divisorialSubmodule_iff, mem_divisorialSubmodule_iff]
  constructor
  · intro h F hF
    obtain ⟨E, hE⟩ := exists_primeDivisor_eq_map_genericPoint g
      (map_mem_biregularLocus_of_coheight_le_one g hEx F.coheight_genericPoint.le)
    exact (orderCondition_iff_of_map_genericPoint g hgen hE (hYV E) B φ).mpr (h E (hE ▸ hF))
  · intro h E hE
    obtain ⟨F, hF⟩ := exists_primeDivisor_map_genericPoint_eq g (hYV E)
    exact (orderCondition_iff_of_map_genericPoint g hgen hF (hYV E) B φ).mp
      (h F (show g F.genericPoint ∈ U from hF ▸ hE))

end SmallModel

/-! ### Sections of high powers of an ample sheaf avoiding associated points

For `r ≫ 0` there is `s ∈ H⁰(X, L^{⊗r})` that vanishes at `x` and at no associated point of
`F`. This follows from Serre generation of `I_x ⊗ L^{⊗r}` and prime avoidance over the
infinite field `k`. Multiplication by such an `s` is injective on `F`, because its kernel has
no associated point. -/

section SectionAvoidingAssociatedPoints

open MonoidalCategory
open MMP.Intersection.Scheme.Modules (IsLineBundle tensorPow)

/-- A scheme projective over a field is Noetherian. -/
private theorem isNoetherian_of_isProjectiveMorphism (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (hX : IsProjectiveMorphism (X ↘ Spec (.of k))) : IsNoetherian X := by
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  exact AlgebraicGeometry.IsNoetherian.mk

/-- A line bundle (locally free of rank one) is an invertible `𝒪_X`-module. -/
private theorem isInvertibleModule_of_isLineBundle {X : Scheme.{u}} (L : X.Modules)
    (hL : IsLineBundle L) : Stacks.Ample.IsInvertibleModule X L := by
  refine (AlgebraicGeometry.isInvertible_iff_exists_restrict_iso_unit X L).2 fun x => ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL x
  exact ⟨U, hxU, ⟨e ≪≫ Limits.coproductUniqueIso _⟩⟩

/-- Tensor powers of an invertible module are invertible. -/
private theorem isInvertibleModule_tensorPow {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (r : ℕ) :
    Stacks.Ample.IsInvertibleModule X (tensorPow L r) := by
  induction r with
  | zero => exact Stacks.Ample.isInvertibleModule_unit X
  | succ n ih =>
    have h1 : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (tensorPow L n) :=
      ih
    have h2 : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := ‹_›
    exact Stacks.Chow.isInvertible_tensorObj (tensorPow L n) L

/-- Left whiskering for the monoidal structure on `X.Modules` is
`AlgebraicGeometry.Scheme.Modules.tensorLeftMap`. -/
private theorem whiskerLeft_eq_tensorLeftMap {X : Scheme.{u}} (F G H : X.Modules) (φ : G ⟶ H) :
    F ◁ φ = (Scheme.Modules.tensorLeftMap F φ : F ⊗ G ⟶ F ⊗ H) := by
  rw [← id_tensorHom]
  have := Stacks.SheafOfModules.OnSpace.monoidal_tensorHom X.toRingedSpace (𝟙 F) φ
  erw [Category.id_comp, Category.comp_id] at this
  refine this.trans ?_
  erw [Functor.uncurry_obj_map]
  exact (congrArg (· ≫ _) (congrArg (fun t => NatTrans.app t G)
    (CategoryTheory.Functor.map_id _ F))).trans (Category.id_comp _)

/-- If `u : F ⟶ F ⊗ A` and `g : A ⟶ B` are bijective on stalks at `ξ`, then `u ≫ F ◁ g` is
injective on stalks at `ξ`. -/
private theorem injective_stalkLinearMap_comp_whiskerLeft {X : Scheme.{u}} (F A B : X.Modules)
    (u : F ⟶ F ⊗ A) (g : A ⟶ B) (ξ : X)
    (hu : Function.Bijective (stalkLinearMap _ _ u ξ))
    (hg : Function.Bijective (stalkLinearMap A B g ξ)) :
    Function.Injective (stalkLinearMap F (F ⊗ B) (u ≫ F ◁ g) ξ) := by
  rw [whiskerLeft_eq_tensorLeftMap]
  exact (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_comp _ _ ξ hu
    (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_tensorLeftMap F g ξ hg)).injective

/-- Multiplication by a section `s` of a line bundle `M` is injective on a coherent sheaf `F` as
soon as `s` vanishes at no associated point of `F`: the kernel is a coherent subsheaf of `F`
whose associated points are associated points of `F`, and at such a point `s` generates `M`, so
multiplication by `s` is an isomorphism on stalks there. -/
private theorem mono_mul_of_forall_isAssociatedPoint_mem_nonvanishingLocus (k : Type u)
    [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsNoetherian X] (F : X.Modules)
    [SheafOfModules.IsCoherent F] (L : X.Modules) (hLb : IsLineBundle L) (r : ℕ)
    (s : MMP.Intersection.H0 k (tensorPow L r))
    (h : ∀ ξ, Stacks.Divisors.IsAssociatedPoint F ξ →
      ξ ∈ Stacks.Ample.nonvanishingLocus (tensorPow L r) s) :
    Mono ((ρ_ F).inv ≫ F ◁ (SheafOfModules.unitHomEquiv (tensorPow L r)).symm
      s.toSections) := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : Stacks.Ample.IsInvertibleModule X L := isInvertibleModule_of_isLineBundle L hLb
  have : Stacks.Ample.IsInvertibleModule X (tensorPow L r) := isInvertibleModule_tensorPow L r
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent (M := F)
  have : (tensorPow L r).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have : (F ⊗ tensorPow L r).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace F _ ‹_› ‹_›
  have hφ : (SheafOfModules.unitHomEquiv (tensorPow L r)).symm s.toSections =
      Stacks.EnriquesSeveriZariski.sectionHom (tensorPow L r) s := rfl
  refine Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
    _ fun ξ => ?_
  by_cases hξ : Stacks.Divisors.IsAssociatedPoint F ξ
  · left
    rw [hφ]
    exact injective_stalkLinearMap_comp_whiskerLeft F _ _ _ _ ξ
      (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse _ _
        (ρ_ F).inv_hom_id (ρ_ F).hom_inv_id ξ)
      (Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_sectionHom (tensorPow L r) s
        (h ξ hξ))
  · exact Or.inr hξ

/-- A morphism of modules can only shrink the nonvanishing locus of a global section. -/
private theorem nonvanishingLocus_app_subset {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus N (φ.app ⊤ s) ⊆ Stacks.Ample.nonvanishingLocus M s := by
  intro x hx hs
  refine hx ?_
  rw [← Stacks.ModuleStalk.mapFun_Γgerm]
  exact Stacks.SectionProduct.mapFun_mem_maximalSmul φ x hs

/-- An isomorphism of modules preserves the nonvanishing locus of a global section. -/
private theorem nonvanishingLocus_iso_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (s : Γ(M, ⊤)) :
    Stacks.Ample.nonvanishingLocus N (e.hom.app ⊤ s) = Stacks.Ample.nonvanishingLocus M s := by
  refine (nonvanishingLocus_app_subset e.hom s).antisymm ?_
  have h : e.inv.app ⊤ (e.hom.app ⊤ s) = s := by
    change ((e.hom ≫ e.inv).app ⊤) s = s
    rw [Iso.hom_inv_id]
    rfl
  conv_lhs => rw [← h]
  exact nonvanishingLocus_app_subset e.inv _

/-- On a scheme proper over `k`, an ample line bundle in the sense of `MMP.Intersection.IsAmple`
is ample in the sense of `Stacks.Ample.IsAmple`. -/
private theorem isAmple_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : MMP.Intersection.IsAmple k L) :
    Stacks.Ample.IsAmple X L := by
  obtain ⟨d, hd, hva⟩ := hL
  obtain ⟨eP⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L d
  exact ((Stacks.AmpleRelativeFiniteType.tfae_six (X ↘ Spec (.of k)) L).out 5 1).1
    (⟨d, hd, MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple k _ _ hva eP.symm⟩ :
      ∃ d : ℕ, 1 ≤ d ∧
      Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver (X ↘ Spec (.of k))
        (Stacks.Ample.tensorPowModule X L (d : ℤ)))

open Stacks.SectionsVanishingOnSubscheme Stacks.Chow.BertiniChain in
/-- For `r ≫ 0` there is a section of `L^{⊗r}` vanishing at the closed point `x` and at no point
of a given finite set `S ∌ x`: the sections vanishing at `x` generate `L^{⊗r}` off `x` (Serre),
so for each `ξ ∈ S` those vanishing at `ξ` form a proper subspace, and a vector space over an
infinite field is not a finite union of proper subspaces. -/
private theorem eventually_exists_section_notMem_nonvanishingLocus (k : Type u) [Field k]
    [Infinite k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (hX : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (L : X.Modules) (hLb : IsLineBundle L) (hL : MMP.Intersection.IsAmple k L)
    (x : X) (hx : IsClosed ({x} : Set X)) (S : Set X) (hS : S.Finite) (hxS : x ∉ S) :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ s : MMP.Intersection.H0 k (tensorPow L r),
      x ∉ Stacks.Ample.nonvanishingLocus (tensorPow L r) s ∧
        ∀ ξ ∈ S, ξ ∈ Stacks.Ample.nonvanishingLocus (tensorPow L r) s := by
  have : IsProper (X ↘ Spec (.of k)) := isProper_of_isProjectiveMorphism _ hX
  have : Stacks.Ample.IsInvertibleModule X L := isInvertibleModule_of_isLineBundle L hLb
  have hample : Stacks.Ample.IsAmple X L := isAmple_of_isAmple k L hL
  set I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩
  obtain ⟨n₀, hn₀⟩ := exists_bound_generatesOffSupport k (X ↘ Spec (.of k)) I L hample
  rw [Filter.eventually_atTop]
  refine ⟨n₀.toNat, fun r hr => ?_⟩
  have hgen := hn₀ (r : ℤ) (by omega)
  have : Finite S := hS.to_subtype
  have hne : ∀ ξ : S, vanishingAtSubmodule k (X ↘ Spec (.of k)) I L (r : ℤ) ξ ≠ ⊤ := fun ξ =>
    vanishingAtSubmodule_ne_top k _ I L _ hgen fun h => hxS ((show (ξ : X) = x from h) ▸ ξ.2)
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
  obtain ⟨e⟩ := MMP.Resolution.Bridges.nonempty_tensorPow_iso_tensorPowModule X L r
  let t : Γ(Stacks.Ample.tensorPowModule X L (r : ℤ), ⊤) :=
    ((v : Stacks.Bertini.globalSections k (X ↘ Spec (.of k))
      (Stacks.Ample.tensorPowModule X L (r : ℤ))) : _)
  have hnv : Stacks.Ample.nonvanishingLocus (tensorPow L r) (e.inv.app ⊤ t) =
      Stacks.Ample.nonvanishingLocus _ t :=
    nonvanishingLocus_iso_app e.symm t
  refine ⟨e.inv.app ⊤ t, ?_, fun ξ hξ => ?_⟩
  · rw [hnv]
    exact fun h => h (Γgerm_mem_maximalSmul_of_mem_vanishingSections k _ I L _ x
      (Set.mem_singleton x) v)
  · rw [hnv]
    exact fun h => hv ⟨ξ, hξ⟩ ((notMem_nvOpen_iff _ _ _).2 h)

/-- On a projective scheme over `k` with an ample line bundle `L`, a coherent sheaf `F` and a
closed point `x` that is not an associated point of `F`: for all large `r` there is a global
section `s` of `L^{⊗r}` vanishing at `x` such that multiplication by `s`,
`F ≅ F ⊗ 𝒪_X ⟶ F ⊗ L^{⊗r}`, is a monomorphism. -/
@[mmp "lem_km5c_section_avoiding_associated_points"]
public theorem eventually_exists_section_notMem_nonvanishingLocus_mono (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (hX : IsProjectiveMorphism (X ↘ Spec (.of k)))
    (L : X.Modules) (hLb : IsLineBundle L) (hL : MMP.Intersection.IsAmple k L)
    (F : X.Modules) [SheafOfModules.IsCoherent F]
    (x : X) (hx : IsClosed ({x} : Set X)) (hxF : ¬ Stacks.Divisors.IsAssociatedPoint F x) :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ s : MMP.Intersection.H0 k (tensorPow L r),
      x ∉ Stacks.Ample.nonvanishingLocus (tensorPow L r) s ∧
        Mono ((ρ_ F).inv ≫ F ◁ (SheafOfModules.unitHomEquiv (tensorPow L r)).symm
          s.toSections) := by
  have : IsNoetherian X := isNoetherian_of_isProjectiveMorphism k hX
  have : Infinite k := IsAlgClosed.instInfinite
  filter_upwards [eventually_exists_section_notMem_nonvanishingLocus k hX L hLb hL x hx
    (Stacks.Divisors.associatedPoints F) (MMP.Foundations.finite_associatedPoints F) hxF]
    with r ⟨s, hsx, hsS⟩
  exact ⟨s, hsx, mono_mul_of_forall_isAssociatedPoint_mem_nonvanishingLocus k F L hLb r s hsS⟩

end SectionAvoidingAssociatedPoints

end MMP.Mori

/-! ### The local form of a cyclic cover

If `g` is a local equation of `M` on `U`, then `𝒪_X(-iM)(U) = gⁱ 𝒪_X(U)` for every `i`. Hence
`𝒜(U) = ⊕_{i<m} 𝒪_X(U) tⁱ` with `t = g e₁`, and the multiplication rule gives
`tᵐ = gᵐ φ e₀ = u`. So `t ↦ g e₁` is an isomorphism `𝒪_X(U)[t]/(tᵐ - u) ≅ 𝒜(U)`, and on `U`,
`div u = m div g + div φ = mM + div φ`. -/

namespace MMP.Mori.DivisorialCyclicCover

open Opposite Polynomial

section LocalForm

variable {X : Scheme.{u}}

private theorem phiOn_mul (a b : (RationalFunctions X)ˣ) (U : X.Opens) :
    phiOn (a * b) U = phiOn a U * phiOn b U := rfl

private theorem phiOn_pow (a : (RationalFunctions X)ˣ) (U : X.Opens) (n : ℕ) :
    phiOn (a ^ n) U = phiOn a U ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, phiOn_mul, ih, pow_succ]

variable [IsLocallyNoetherian X] [IsNormal X]

private theorem isLocalEquation_nsmul {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation U ψ) (n : ℕ) : (n • D).IsLocalEquation U (ψ ^ n) := by
  simpa using h.zsmul (n : ℤ)

/-- A local equation `ψ` of `D` on `U` is a section of `𝒪_X(-D)` over `U`. -/
private theorem isDivisorialSection_neg_phiOn {D : Divisor X} {U : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (h : D.IsLocalEquation U ψ) :
    (-D).IsDivisorialSection U (phiOn ψ U) := fun E hE =>
  Or.inr (by
    change _ ≤ E.valuation ((ψ : RationalFunctions X) E.component)
    rw [PrimeDivisor.valuation_component, DivisorWithCoeffs.coeff_neg, neg_neg, h E hE])

/-- If `ψ` is a local equation of `D` on `U`, every section of `𝒪_X(-D)` over `U` is a regular
multiple of `ψ`: `𝒪_X(-D)(U) = ψ 𝒪_X(U)`. -/
private theorem exists_eq_mul_phiOn {D : Divisor X} {U : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (h : D.IsLocalEquation U ψ) {f : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (hf : (-D).IsDivisorialSection U f) :
    ∃ c : Γ(X, U), f = (toRationalFunctionsPresheaf X).app (op U) c * phiOn ψ U := by
  obtain ⟨c, hc⟩ := (h.neg.isLocalGenerator_invSection U le_rfl).2
    (show Γ((-D).divisorialSheaf, U) from (⟨f, hf⟩ : (-D).divisorialSubmodule U))
  refine ⟨c, funext fun Z => ?_⟩
  have := congrFun (congrArg Subtype.val hc) Z
  change X.presheaf.germ U _ Z.2 c * ((ψ⁻¹⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z.1
    = f Z at this
  rw [inv_inv] at this
  rw [← this]
  rfl

variable [CompactSpace X] (m : ℕ) [NeZero m] {M : Divisor X} {φ : (RationalFunctions X)ˣ}
  (hφ : 0 ≤ principalDivisor φ + m • M) {U : X.Opens} {g : (RationalFunctions X)ˣ}
  (hg : M.IsLocalEquation U g)

include hg in
/-- The generator `t = g e₁` of `𝒜(U)` over `𝒪_X(U)`. -/
private noncomputable def localRoot : (localSubalgebra m M hφ).carrier U :=
  ⟨reduce m φ U (monomial 1 (phiOn g U)), monomial 1 (phiOn g U), fun k => by
    rw [coeff_monomial]
    split_ifs with h
    · subst h
      rw [one_smul]
      exact isDivisorialSection_neg_phiOn hg
    · exact Submodule.zero_mem _, rfl⟩

omit [NeZero m] in
private theorem reduce_C (a : (rationalFunctionsPresheaf X).obj (op U)) :
    reduce m φ U (C a) = ((ofRationalFunctions m φ).app (op U)).hom a := by
  funext Z
  rw [reduce_apply, Polynomial.map_C, AdjoinRoot.mk_C]
  rfl

/-- `c tⁿ = c gⁿ eₙ` in `𝓛(U)`. -/
private theorem coe_algebraMap_mul_localRoot_pow (c : Γ(X, U)) (n : ℕ) :
    (((localSubalgebra m M hφ).algebraMap U c * localRoot m hφ hg ^ n : _) :
        (ambient m φ).obj (op U)) =
      reduce m φ U
        (monomial n (((toRationalFunctionsPresheaf X).app (op U)).hom c * phiOn g U ^ n)) := by
  rw [Subring.coe_mul, SubmonoidClass.coe_pow]
  change ((ofRationalFunctions m φ).app (op U)).hom _ * reduce m φ U (monomial 1 _) ^ n = _
  rw [← reduce_C, ← map_pow, monomial_pow, one_mul, ← map_mul, C_mul_monomial]
  rfl

/-- `tᵐ = gᵐ φ`. -/
private theorem localRoot_pow {v : Γ(X, U)}
    (hv : (toRationalFunctionsPresheaf X).app (op U) v = phiOn (g ^ m * φ) U) :
    localRoot m hφ hg ^ m = (localSubalgebra m M hφ).algebraMap U v := by
  apply Subtype.ext
  have h1 := coe_algebraMap_mul_localRoot_pow m hφ hg 1 m
  rw [map_one, one_mul, map_one, one_mul] at h1
  rw [h1, reduce_monomial_of_le m φ le_rfl, Nat.sub_self, monomial_zero_left, reduce_C]
  refine congrArg _ ?_
  rw [mul_comm, ← phiOn_pow, ← phiOn_mul]
  exact hv.symm

/-- `∑_{i<m} cᵢ tⁱ = ∑_{i<m} cᵢ gⁱ eᵢ` in `𝓛(U)`. -/
private theorem coe_sum_algebraMap_mul_localRoot_pow (c : ℕ → Γ(X, U)) :
    ((∑ n ∈ Finset.range m, (localSubalgebra m M hφ).algebraMap U (c n) * localRoot m hφ hg ^ n :
        _) : (ambient m φ).obj (op U)) =
      reduce m φ U (∑ i : Fin m,
        monomial (i : ℕ)
          (((toRationalFunctionsPresheaf X).app (op U)).hom (c i) * phiOn g U ^ (i : ℕ))) := by
  rw [AddSubmonoidClass.coe_finset_sum, map_sum, Fin.sum_univ_eq_sum_range
    (fun n => reduce m φ U (monomial n (((toRationalFunctionsPresheaf X).app (op U)).hom (c n) *
      phiOn g U ^ n)))]
  exact Finset.sum_congr rfl fun n _ => coe_algebraMap_mul_localRoot_pow m hφ hg (c n) n

/-- **`1, t, …, tᵐ⁻¹` is a basis of `𝒜(U)` over `𝒪_X(U)`**: a combination `∑_{i<m} cᵢ tⁱ`
vanishes only if every `cᵢ` does, and every section of `𝒜(U)` is such a combination. -/
private theorem localRoot_basis :
    (∀ c : ℕ → Γ(X, U), ∑ n ∈ Finset.range m,
        (localSubalgebra m M hφ).algebraMap U (c n) * localRoot m hφ hg ^ n = 0 →
        ∀ k < m, c k = 0) ∧
      ∀ x : (localSubalgebra m M hφ).carrier U, ∃ c : ℕ → Γ(X, U), ∑ n ∈ Finset.range m,
        (localSubalgebra m M hφ).algebraMap U (c n) * localRoot m hφ hg ^ n = x := by
  refine ⟨fun c hc k hk => ?_, fun x => ?_⟩
  · have := congrArg (coeff m φ U k) (congrArg Subtype.val hc)
    rw [coe_sum_algebraMap_mul_localRoot_pow, coeff_reduce_sum, dif_pos hk,
      ZeroMemClass.coe_zero, map_zero, ← phiOn_pow] at this
    have hunit : IsUnit (phiOn (g ^ k) U) := isUnit_iff_exists_inv.mpr
      ⟨phiOn (g ^ k)⁻¹ U, by rw [← phiOn_mul, mul_inv_cancel]; rfl⟩
    exact toRationalFunctionsPresheaf_app_injective U
      ((hunit.mul_left_eq_zero.mp this).trans (map_zero _).symm)
  · have hx : ∀ n : ℕ, ∃ c : Γ(X, U), coeff m φ U n x.1 =
        ((toRationalFunctionsPresheaf X).app (op U)).hom c * phiOn g U ^ n := fun n => by
      have := (mem_carrier_iff m M hφ).mp x.2 n
      rw [smul_neg] at this
      rw [← phiOn_pow]
      exact exists_eq_mul_phiOn (isLocalEquation_nsmul hg n) this
    choose c hc using hx
    refine ⟨c, Subtype.ext ?_⟩
    rw [coe_sum_algebraMap_mul_localRoot_pow]
    conv_rhs => rw [← reduce_sum_coeff m φ x.1,
      ← Fin.sum_univ_eq_sum_range (fun n => monomial n (coeff m φ U n x.1)) m]
    simp only [hc]

end LocalForm

/-- Every element of `R[X]/(Xᵐ - v)` is the class of a polynomial of degree `< m`. -/
theorem exists_eq_mk_sum_range_monomial {R : Type*} [CommRing R] (m : ℕ) [NeZero m] (v : R)
    (y : AdjoinRoot (Polynomial.X ^ m - C v)) :
    ∃ c : ℕ → R, y = AdjoinRoot.mk _ (∑ n ∈ Finset.range m, monomial n (c n)) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨(p %ₘ (Polynomial.X ^ m - C v)).coeff, ?_⟩
  rw [← as_sum_range' _ m ?_, AdjoinRoot.mk_eq_mk]
  · refine ⟨p /ₘ (Polynomial.X ^ m - C v), ?_⟩
    rw [sub_eq_iff_eq_add, add_comm]
    exact (modByMonic_add_div p _).symm
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · rw [Subsingleton.elim (p %ₘ _) 0, natDegree_zero]
    exact Nat.pos_of_ne_zero (NeZero.ne m)
  · refine (natDegree_modByMonic_lt p (monic_X_pow_sub_C v (NeZero.ne m))
      fun h => NeZero.ne m ?_).trans_eq natDegree_X_pow_sub_C
    have := congrArg natDegree h
    rwa [natDegree_X_pow_sub_C, natDegree_one] at this

/-- **Local form of a cyclic cover.** If `g` is a local equation of `M` on `U`, then `u = gᵐ φ` is
a regular function on `U`, it is a local equation of `div φ + mM` on `U`, and
`𝒪_X(U)[t]/(tᵐ - u) ≅ 𝒜(U)` as `𝒪_X(U)`-algebras by `t ↦ g e₁`. -/
@[mmp "lem_km5d_divisorial_cyclic_cover_local_form"]
public theorem exists_algEquiv_adjoinRoot_of_isLocalEquation {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (m : ℕ) [NeZero m] (M : Divisor X)
    {φ : (RationalFunctions X)ˣ} (hφ : 0 ≤ principalDivisor φ + m • M) {U : X.Opens}
    {g : (RationalFunctions X)ˣ} (hg : M.IsLocalEquation U g) :
    ∃ v : Γ(X, U), ((toRationalFunctionsPresheaf X).app (op U)).hom v = phiOn (g ^ m * φ) U ∧
      (principalDivisor φ + m • M).IsLocalEquation U (g ^ m * φ) ∧
      letI := ((localSubalgebra m M hφ).algebraMap U).toAlgebra
      ∃ e : AdjoinRoot (Polynomial.X ^ m - C v) ≃ₐ[Γ(X, U)] (localSubalgebra m M hφ).carrier U,
        ((e (AdjoinRoot.root _) : (localSubalgebra m M hφ).carrier U) :
            (ambient m φ).obj (op U)) =
          reduce m φ U (monomial 1 (phiOn g U)) := by
  have hloc : (principalDivisor φ + m • M).IsLocalEquation U (g ^ m * φ) := by
    rw [mul_comm]
    exact (show (principalDivisor φ).IsLocalEquation U φ from
      fun E _ => coeff_principalDivisor φ E).add (isLocalEquation_nsmul hg m)
  obtain ⟨v, hv⟩ := ((isDivisorialSection_neg_phiOn hloc).mono (neg_nonpos.mpr hφ)).exists_eq
  refine ⟨v, hv, hloc, ?_⟩
  letI := ((localSubalgebra m M hφ).algebraMap U).toAlgebra
  let e₀ : AdjoinRoot (Polynomial.X ^ m - C v) →ₐ[Γ(X, U)] _ :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId Γ(X, U) _) (localRoot m hφ hg) (by
      change aeval _ _ = 0
      rw [map_sub, aeval_X_pow, aeval_C, localRoot_pow m hφ hg hv]
      exact sub_self _)
  have he₀ : ∀ c : ℕ → Γ(X, U), e₀ (AdjoinRoot.mk _ (∑ n ∈ Finset.range m, monomial n (c n))) =
      ∑ n ∈ Finset.range m, (localSubalgebra m M hφ).algebraMap U (c n) * localRoot m hφ hg ^ n :=
    fun c => by
      change aeval _ _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun n _ => aeval_monomial _
  have hinj : Function.Injective e₀ := by
    refine (injective_iff_map_eq_zero e₀).2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := exists_eq_mk_sum_range_monomial m v y
    rw [he₀] at hy
    have hc := (localRoot_basis m hφ hg).1 c hy
    rw [Finset.sum_eq_zero fun n hn => by rw [hc n (Finset.mem_range.mp hn), monomial_zero_right],
      map_zero]
  have hsurj : Function.Surjective e₀ := fun x => by
    obtain ⟨c, rfl⟩ := (localRoot_basis m hφ hg).2 x
    exact ⟨_, he₀ c⟩
  exact ⟨AlgEquiv.ofBijective e₀ ⟨hinj, hsurj⟩,
    congrArg Subtype.val (AdjoinRoot.liftAlgHom_root _ _ _ _ : e₀ (AdjoinRoot.root _) = _)⟩

end MMP.Mori.DivisorialCyclicCover
