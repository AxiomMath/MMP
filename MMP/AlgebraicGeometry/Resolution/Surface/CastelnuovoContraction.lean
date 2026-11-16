module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuasiProjectiveRegularSurface
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.QuasiProjectiveContraction
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Locality
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalType
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus

/-!
# Relative contraction of a smooth `(-1)`-curve

Let `k` be an algebraically closed field of any characteristic, `Y` a smooth surface over `k`,
`Z` a separated `k`-scheme of finite type and `p : Y ⟶ Z` a proper `k`-morphism. A smooth proper
rational curve `C ⊆ Y` with `(C²) = -1` and `p(C)` a point is contracted by a proper birational
morphism `c : Y ⟶ Y'` onto a smooth surface, an isomorphism off `C`, through which `p` factors
by a proper `p' : Y' ⟶ Z`.

## Main results

* `MMP.Resolution.Bridges.exists_contraction_of_isMinusOneCurve`: the relative contraction.

## Implementation notes

* A *smooth surface* `Y` over `k`, with structure morphism `sY`, is `IsVariety k sY`,
  `MMP.Mori.IsSmoothScheme sY` and `topologicalKrullDim Y = 2`, as in
  `MMP.Threefold.Mori.Surfaces`. The instances `QuasiCompact sY`, `IsLocallyNoetherian Y`,
  `IsNormal Y` hold on a smooth surface and are needed to state `(C · C)`.
* A smooth proper rational curve with `(C²) = -1` is `MMP.Mori.IsMinusOneCurve`: a prime divisor
  `C`, proper over `k`, with `C ≅ ℙ¹_k` over `k` and `(C · C) = -1`. Over an algebraically closed
  field a smooth proper rational curve is `ℙ¹_k`, and a curve on a surface is a prime divisor.
* `c` is an isomorphism off `C` and contracts `C`: there is a point `q ∈ Y'` with `c⁻¹(Y' ∖ q)`
  equal to `Y ∖ C` and `c` restricting to an isomorphism over `Y' ∖ q`.
* The proof goes through Stacks, Tags 0C5N and 0C2N (2): `C` is an
  exceptional curve of the first kind (`AlgebraicGeometry.Scheme.IdealSheafData.
  IsExceptionalCurveOfFirstKind`), `p` is quasi-projective, and the contraction theorem
  supplies `c` and `p'` with `AlgebraicGeometry.IsContractionOfExceptionalCurve`.

## References

* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
* [Stacks Project, Tag 0C5N](https://stacks.math.columbia.edu/tag/0C5N)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution.Bridges

open MMP.Mori (IsMinusOneCurve IsSmoothScheme IsBirationalMorphism)

variable {k : Type u} [Field k] [IsAlgClosed k] {Y Z : Scheme.{u}}
  (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))

/-! ### The steps of the proof -/

section Steps

omit [IsAlgClosed k] in
/-- A scheme smooth over a field `k` is regular. -/
theorem isRegular_of_isSmoothScheme (hsm : IsSmoothScheme sY) : IsRegular Y := by
  have hcov : (⨆ U : {U : Y.Opens | Smooth (U.ι ≫ sY)}, (U : Y.Opens)) = ⊤ := by
    rw [← hsm, MMP.Mori.smoothLocus, sSup_eq_iSup']
  refine (isRegular_iff_regular_stalks Y).2 ⟨?_, fun x => ?_⟩
  · rw [isLocallyNoetherian_iff_openCover (Y.openCoverOfIsOpenCover _ hcov)]
    intro U
    have : Smooth (U.1.ι ≫ sY) := U.2
    have : LocallyOfFinitePresentation (U.1.ι ≫ sY) := inferInstance
    have hft : LocallyOfFiniteType (U.1.ι ≫ sY) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.1 inferInstance
    exact @LocallyOfFiniteType.isLocallyNoetherian _ _ (U.1.ι ≫ sY) hft inferInstance
  · obtain ⟨U, hxU, hU⟩ :=
      MMP.Mori.mem_smoothLocus_iff.1 (hsm ▸ trivial : x ∈ MMP.Mori.smoothLocus sY)
    have : Smooth (U.ι ≫ sY) := hU
    have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sY) ⟨x, hxU⟩
    exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨x, hxU⟩).commRingCatIsoToRingEquiv

omit [IsAlgClosed k] in
/-- **Residual (i).** A smooth proper rational curve `C ≅ ℙ¹_k` (glued model `projectiveLine k`)
is isomorphic, over `k`, to the graded model `projectiveLineProj k = Proj k[T₀, T₁]`, by the
comparison `projectiveLineIsoProj`. -/
private theorem exists_iso_projectiveLineProj_of_isMinusOneCurve [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] {C : MMP.Mori.PrimeDivisor Y}
    (hC : IsMinusOneCurve sY C) :
    ∃ e : projectiveLineProj k ≅ C.idealSheaf.subscheme,
      e.hom ≫ C.idealSheaf.subschemeι ≫ sY =
        Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1 := by
  obtain ⟨e, he⟩ := hC.2.1
  refine ⟨(projectiveLineIsoProj k).symm ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, he]
  rw [← projectiveLineIsoProj_hom_comp_projToSpecCoeff, Iso.inv_hom_id_assoc]

open MMP.Mori DivisorWithCoeffs in
/-- **Local equations of a prime divisor with an invertible ideal sheaf.** Near every point, the
ideal of `P` on an affine open `W` is generated by `f`, and the unit `φ` of `K(Y)` which is `f` on
the components meeting `W` and `1` elsewhere is a local equation of `P` on `W`. (Reproved from
`MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme`, whose local equation is not exported.) -/
private theorem exists_localEquation_of_isEffectiveCartierDivisor
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf) (x : Y) :
    ∃ (W : Y.affineOpens) (_ : x ∈ (W : Y.Opens)) (f : Γ(Y, (W : Y.Opens)))
      (φ : (RationalFunctions Y)ˣ),
      P.idealSheaf.ideal W = Ideal.span {f} ∧
      Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) W φ ∧
      ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ (W : Y.Opens)),
        (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
  classical
  haveI := P.integral
  have hsame : ∀ E : Mori.PrimeDivisor Y, E.genericPoint ∈ P.support → P = E := by
    intro E hE
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
    have hle : E.genericPoint ≤ P.genericPoint := specializes_iff_mem_closure.mpr hE
    by_contra hne
    have hlt : E.genericPoint < P.genericPoint := lt_of_le_not_ge hle fun h =>
      hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (Specializes.antisymm (show E.genericPoint ⤳ P.genericPoint from h)
          (show P.genericPoint ⤳ E.genericPoint from hle)).eq.symm)
    have h2 := Order.coheight_add_one_le hlt
    rw [Mori.PrimeDivisor.coheight_genericPoint, Mori.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

  obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor
      P.idealSheaf hcart x
  have hgerm : ∀ y (hy : y ∈ W), IdealSheafData.stalk P.idealSheaf y =
      Ideal.span {(Y.presheaf.germ W y hy).hom f} := by
    intro y hy
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ P.idealSheaf y ⟨W, hW⟩ hy, hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzd : ∀ y (hy : y ∈ W), (Y.presheaf.germ W y hy).hom f ∈
      nonZeroDivisors (Y.presheaf.stalk y) := fun y hy =>
    Stacks.Divisors.germ_mem_nonZeroDivisors hW hf y hy
  let u : ∀ Z : irreducibleComponents Y, (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ :=
    fun Z => if h : componentGenericPoint Y Z ∈ W then
      (by
        letI := (RationalFunctions.isField_stalk Y Z).toField
        exact (isUnit_iff_ne_zero.2 (nonZeroDivisors.ne_zero (hnzd _ h))).unit)
      else 1
  let φ : (RationalFunctions Y)ˣ := (RationalFunctions.unitsEquiv Y).symm u
  have hφall : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ W _ hZ).hom f := by
    intro Z hZ
    change ((u Z : (Y.presheaf.stalk (componentGenericPoint Y Z))ˣ) :
      Y.presheaf.stalk (componentGenericPoint Y Z)) = _
    simp only [u]
    rw [dif_pos hZ]
    rfl
  refine ⟨⟨W, hW⟩, hxW, f, φ, hspan, ?_, hφall⟩
  rintro E ⟨y, hyE, hyW⟩
  have hηW : E.genericPoint ∈ W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyE
    exact (specializes_iff_mem_closure.mpr hyE).mem_open W.isOpen hyW
  have hZW : componentGenericPoint Y E.component ∈ W :=
    E.specializes_genericPoint.mem_open W.isOpen hηW
  have key : E.toComponent.hom ((Y.presheaf.germ W _ hηW).hom f) =
      (φ : RationalFunctions Y) E.component := by
    rw [hφall _ hZW]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  by_cases hEP : P = E
  · subst hEP
    rw [coeff_single_self]
    have hmem : P.genericPoint ∈ P.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hg0 := nonZeroDivisors.ne_zero (hnzd _ hηW)
    have hprime : Prime ((Y.presheaf.germ W _ hηW).hom f) := by
      rw [← Ideal.span_singleton_prime hg0, ← hgerm _ hηW]
      obtain ⟨y', hy'⟩ : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι]
        exact hmem
      rw [← hy', ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
      exact RingHom.ker_isPrime _
    exact (P.ord_eq_one_of_irreducible hprime.irreducible key).symm
  · rw [coeff_single_of_ne hEP]
    have hnm : E.genericPoint ∉ P.support := fun h => hEP (hsame E h)
    have htop := (AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_notMem_support
      P.idealSheaf _).2 hnm
    rw [hgerm _ hηW, Ideal.span_singleton_eq_top] at htop
    exact (E.ord_eq_zero_of_isUnit htop key).symm

open MMP.Mori DivisorWithCoeffs Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On an open `V` carrying a rank-one dual basis of `𝒪_Y(P)` and a local equation `φ`, equal to
`f` there, the coordinate of the section `1` generates the same ideal as `f`. -/
private theorem span_evalAt_eq_span_of_isLocalEquation
    [IsLocallyNoetherian Y] [IsNormal Y] (P : Mori.PrimeDivisor Y)
    (hD0 : 0 ≤ (Finsupp.single P 1 : Divisor Y)) (V : Y.Opens)
    (b : Stacks.SheafOfModules.DualBasisOne Y.sheaf.obj
      (structureSheafRing Y.toRingedSpace).property
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)) V)
    (f : Γ(Y, V)) (φ : (RationalFunctions Y)ˣ)
    (hloc : Divisor.IsLocalEquation (Finsupp.single P 1 : Divisor Y) V φ)
    (hφ : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
      (φ : RationalFunctions Y) Z = (Y.presheaf.germ V _ hZ).hom f) :
    Ideal.span ({(evalAt (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y))
      (dualBasisCoord (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)) b)
      ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map
        (homOfLE le_top).op ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))))} :
        Set Γ(Y, V)) =
      Ideal.span {f} := by
  set c := evalAt _ (dualBasisCoord _ b)
      ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map (homOfLE le_top).op
        ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))) with hc
  have h1 := smul_dualBasisSection b
    ((Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y)).presheaf.map (homOfLE le_top).op
      ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)))
  have inj : ∀ x y : Γ(Y, V),
      (∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
        (Y.presheaf.germ V _ Z.2).hom x = (Y.presheaf.germ V _ Z.2).hom y) → x = y :=
    fun x y h => toRationalFunctionsPresheaf_app_injective V (funext h)
  have E1 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      (Y.presheaf.germ V _ Z.2).hom c * (dualBasisSection _ b).1 Z = 1 := fun Z =>
    congrArg (fun m : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) => m.1 Z) h1
  have hgsec : (Divisor.IsDivisorialSection (Finsupp.single P 1 : Divisor Y) V
      (fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1)) := by
    intro E hE
    have h0 : E.OrdGE (E.ord φ⁻¹) (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y)
        E.component) := Or.inr (E.valuation_component φ⁻¹).ge
    refine h0.mono (le_of_eq ?_)
    rw [PrimeDivisor.ord_inv, ← hloc E hE]
  let g : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) :=
    ⟨fun Z => ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1, hgsec⟩
  have h2 := smul_dualBasisSection b g
  have E2 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 =
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g) *
          (dualBasisSection _ b).1 Z := fun Z =>
    (congrArg (fun m : Γ(Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor Y), V) => m.1 Z)
      h2).symm
  have E3 : ∀ Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ V},
      ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z.1 *
        (φ : RationalFunctions Y) Z.1 = 1 := by
    intro Z
    rw [← Pi.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Pi.one_apply]
  have hhsec : (Divisor.IsDivisorialSection (0 : Divisor Y) V
      (fun Z => (φ : RationalFunctions Y) Z.1 * (dualBasisSection _ b).1 Z)) := by
    intro E hE
    have hψ : E.OrdGE (E.ord φ) ((φ : RationalFunctions Y) E.component) :=
      Or.inr (E.valuation_component φ).ge
    refine (hψ.mul ((dualBasisSection _ b).2 E hE)).mono (le_of_eq ?_)
    rw [← hloc E hE]
    simp
  obtain ⟨s', hs'⟩ := Divisor.IsDivisorialSection.exists_eq hhsec
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨evalAt _ (dualBasisCoord _ b) g, inj _ _ fun Z => ?_⟩
    rw [map_mul, ← hφ Z.1 Z.2]
    linear_combination (-(Y.presheaf.germ V _ Z.2).hom c) * E3 Z +
      ((Y.presheaf.germ V _ Z.2).hom c * (φ : RationalFunctions Y) Z.1) * E2 Z +
      ((φ : RationalFunctions Y) Z.1 *
        (Y.presheaf.germ V _ Z.2).hom (evalAt _ (dualBasisCoord _ b) g)) * E1 Z
  · rw [Ideal.span_singleton_le_span_singleton]
    refine ⟨s', inj _ _ fun Z => ?_⟩
    have hs'Z : (Y.presheaf.germ V _ Z.2).hom s' =
        (φ : RationalFunctions Y) Z.1 * (dualBasisSection _ b).1 Z := congrFun hs' Z
    rw [map_mul, hs'Z, ← hφ Z.1 Z.2]
    linear_combination (-(φ : RationalFunctions Y) Z.1) * E1 Z

omit [IsAlgClosed k] in
/-- **Bridge.** On a smooth surface the divisorial sheaf `𝒪_Y(C)` of a prime divisor `C`, in the
sense of `MMP.Mori.Divisor.divisorialSheaf`, is the sheaf `𝒪_Y(C) = ℋom(ℐ_C, 𝒪_Y)` of the
Stacks project.

Route: `AlgebraicGeometry.invertibleSheafIsoZeroSchemeOfIsRegularSection` applied to the invertible
module `𝒪_Y(C)` and its section `divisorialSheafOneSection` gives `𝒪_Y(C) ≅ 𝒪_Y(Z(1))`; what
remains is `Z(1) = C.idealSheaf`, i.e. on an affine open `V` carrying a dual basis (e.g. inside an
open `W` where `C` has a local equation `f` generating `ℐ_C`), `𝒪_Y(C)(V) = f⁻¹ 𝒪(V)`. -/
private theorem nonempty_divisorialSheaf_single_iso_invertibleSheaf'
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (C : MMP.Mori.PrimeDivisor Y)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf)
    (hD : MMP.Mori.Divisor.IsCartier (Finsupp.single C 1 : MMP.Mori.Divisor Y)) :
    Nonempty (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y) ≅
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules)) := by
  classical
  have hD0 : 0 ≤ (Finsupp.single C 1 : MMP.Mori.Divisor Y) :=
    Finsupp.single_nonneg.2 zero_le_one
  have hinv := hD.isInvertibleModule_divisorialSheaf
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) := hinv
  let s := (MMP.Mori.Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)
  have hreg : ∀ U : Y.Opens, Function.Injective fun r : Γ(Y, U) =>
      r • (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op s := by
    intro U r r' h
    refine MMP.Mori.toRationalFunctionsPresheaf_app_injective U (funext fun Z => ?_)
    have := congrArg (fun m => m.1 Z) h
    change Y.presheaf.germ U _ Z.2 r * 1 = Y.presheaf.germ U _ Z.2 r' * 1 at this
    rwa [mul_one, mul_one] at this
  have hZ : AlgebraicGeometry.zeroScheme Y
      (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) s =
      C.idealSheaf := by
    have hloc : ∀ x : Y, ∃ V : Y.affineOpens, x ∈ (V : Y.Opens) ∧
        (AlgebraicGeometry.zeroScheme Y
          (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) s).ideal V =
          C.idealSheaf.ideal V := by
      intro x
      obtain ⟨W, hxW, f, φ, hspan, hlocW, hφ⟩ :=
        exists_localEquation_of_isEffectiveCartierDivisor C hcart x
      obtain ⟨V, hxV, hVW, ⟨b⟩⟩ := AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) x hxW
      refine ⟨V, hxV, ?_⟩
      rw [AlgebraicGeometry.zeroScheme_ideal_eq_span_evalAt
        (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) s V b,
        ← C.idealSheaf.map_ideal hVW, hspan, Ideal.map_span, Set.image_singleton]
      exact span_evalAt_eq_span_of_isLocalEquation C hD0 (V : Y.Opens) b
        (Y.presheaf.map (homOfLE hVW).op f) φ (hlocW.mono hVW) fun Z hZ => by
          rw [hφ Z (hVW hZ)]
          exact (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hVW) _ hZ f).symm
    choose U hxU hU using hloc
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top U
      (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) hU
  exact ⟨AlgebraicGeometry.invertibleSheafIsoZeroScheme
    (MMP.Mori.Divisor.divisorialSheaf (Finsupp.single C 1 : MMP.Mori.Divisor Y)) s hreg ≪≫
    eqToIso (by rw [hZ])⟩

omit [IsAlgClosed k] in
/-- **Residual (ii).** The normal sheaf of a `(-1)`-curve `C ≅ ℙ¹` on a smooth surface pulls
back to `𝒪(-1)` along every `k`-isomorphism `e : ℙ¹ ≅ C`: it is `𝒪_Y(C)|_C`, of degree
`(C²) = -1` (`IsIntersectionNumber`), and a line bundle on `ℙ¹` of degree `d` is `𝒪(d)`. -/
private theorem isExceptionalCurveOfFirstKind_of_isMinusOneCurve_aux [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY)
    (C : MMP.Mori.PrimeDivisor Y) (hC : IsMinusOneCurve sY C)
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf)
    (e : projectiveLineProj k ≅ C.idealSheaf.subscheme)
    (he : e.hom ≫ C.idealSheaf.subschemeι ≫ sY =
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) :
    C.idealSheaf.IsExceptionalCurveOfFirstKind k e := by
  refine ⟨hcart, ?_⟩
  have hcartD : MMP.Mori.Divisor.IsCartier (Finsupp.single C 1 : MMP.Mori.Divisor Y) :=
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm C
  obtain ⟨d, ⟨φ⟩⟩ :=
    AlgebraicGeometry.ExceptionalCurveContraction.exists_iso_twistingSheaf_pullback (e := e)
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf)
  suffices hd : d = -1 by
    subst hd
    exact ⟨(RingedSpaceModuleAdjunction.modulePullback e.hom.toLRSHom.toShHom).mapIso
      (Stacks.Divisors.normalSheafIsoInvertibleSheaf C.idealSheaf) ≪≫ φ⟩
  obtain ⟨hprop, hdim1, hQ, hnum⟩ := hC.2.2
  have hq : (MMP.Mori.Divisor.toQDivisor (Finsupp.single C 1 : MMP.Mori.Divisor Y)) =
      (Finsupp.single C 1 : MMP.Mori.QDivisor Y) := by
    refine Finsupp.ext fun E => ?_
    change ((Finsupp.single C (1 : ℤ) E : ℤ) : ℚ) = Finsupp.single C (1 : ℚ) E
    by_cases h : C = E
    · subst h; simp
    · simp [h]
  have hnumZ : MMP.Mori.Divisor.degreeOn k sY C.idealSheaf.subschemeι hdim1
      (Finsupp.single C 1) hcartD = -1 := by
    have h1 := MMP.Mori.QDivisor.intersectionNumber_toQDivisor k sY C.idealSheaf.subschemeι hdim1
      _ hcartD (hq ▸ hQ)
    have h2 : (MMP.Mori.Divisor.degreeOn k sY C.idealSheaf.subschemeι hdim1
      (Finsupp.single C 1) hcartD : ℚ) = -1 := by
      rw [← h1, ← hnum]
      congr 1
    exact_mod_cast h2
  have := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨b⟩ := nonempty_divisorialSheaf_single_iso_invertibleSheaf' C hcart hcartD
  have := hprop
  have : IsProper (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have hdimP := (topologicalKrullDim_projectiveLineProj k).le
  have hLst : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (structureSheafRing Y.toRingedSpace).property
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf) :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf C.idealSheaf
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hLst
  have hM : AlgebraicGeometry.SheafOfModules.IsInvertible C.idealSheaf.subscheme.presheaf
      C.idealSheaf.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules)) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      C.idealSheaf.subschemeι.toLRSHom.toShHom _ hL
  have hP : AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveLineProj k).presheaf
      (projectiveLineProj k).ringCatSheaf.2 ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules))) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      e.hom.toLRSHom.toShHom _ hM
  have h1 : MMP.Mori.degreeOn k sY C.idealSheaf.subschemeι hdim1
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) = -1 := by
    rw [← hnumZ]
    have := hcartD.isInvertibleModule_divisorialSheaf
    exact MMP.Mori.degreeOn_eq_of_iso k sY C.idealSheaf.subschemeι hdim1 b.symm
  have h2 : MMP.Mori.degreeOn k sY C.idealSheaf.subschemeι hdim1
      (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules) =
      invertibleCurveDegree k (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) hdimP
        ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules))) := by
    have key : ∀ (g : projectiveLineProj k ⟶ Spec (.of k)) [IsProper g],
        e.hom ≫ C.idealSheaf.subschemeι ≫ sY = g →
        invertibleCurveDegree k (C.idealSheaf.subschemeι ≫ sY) hdim1
          ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules)) =
        invertibleCurveDegree k g hdimP ((Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback C.idealSheaf.subschemeι).obj
            (Stacks.Divisors.invertibleSheaf' C.idealSheaf : Y.Modules))) := by
      intro g _ hg
      subst hg
      unfold invertibleCurveDegree
      congr 1
      · exact finsum_congr fun n => by
          rw [finrank_cohomologyOverField_pullback k e.hom _ _ n]
      · exact finsum_congr fun n => by
          rw [finrank_cohomologyOverField_unit_pushforward k e.hom _ n]
    exact key _ he
  have h3 := (@invertibleCurveDegree_eq_of_iso k _ _
    (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) _ hdimP _ _ hP
    (Stacks.PicardUFD.isInvertible_twistingSheaf k 1 d) φ).trans
    (invertibleCurveDegree_twistingSheaf_projectiveLineProj k d)
  omega

omit [IsAlgClosed k] in
/-- A `(-1)`-curve on a smooth surface is an exceptional curve of the first kind: its ideal is an
effective Cartier divisor, and its normal sheaf, pulled back along some `ℙ¹_k ≅ C`, is
`𝒪(-1)`. -/
theorem exists_isExceptionalCurveOfFirstKind_of_isMinusOneCurve [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] (hsm : IsSmoothScheme sY) (C : MMP.Mori.PrimeDivisor Y)
    (hC : IsMinusOneCurve sY C) :
    ∃ e : projectiveLineProj k ≅ C.idealSheaf.subscheme,
      C.idealSheaf.IsExceptionalCurveOfFirstKind k e := by
  have hYreg := ((isRegular_iff_regular_stalks Y).1 (isRegular_of_isSmoothScheme sY hsm)).2
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor C.idealSheaf :=
    PrimeDivisor.isEffectiveCartierDivisor_idealSheaf
      (fun x => by
        have := hYreg x
        exact IsRegularLocalRing.uniqueFactorizationMonoid _) C
  obtain ⟨e, he⟩ := exists_iso_projectiveLineProj_of_isMinusOneCurve sY hC
  exact ⟨e, isExceptionalCurveOfFirstKind_of_isMinusOneCurve_aux sY hsm C hC hcart e he⟩

omit [IsAlgClosed k] in
/-- A proper morphism from a smooth surface over `k` to a scheme of finite type over `k` is
quasi-projective (Stacks, Tag 0C5N). -/
theorem isQuasiProjective_of_smoothSurface [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (hsm : IsSmoothScheme sY) (hdim : topologicalKrullDim Y = 2) (p : Y ⟶ Z) [IsProper p] :
    IsQuasiProjective p := by
  have : IsNoetherian Z := isNoetherian_of_finiteType sZ
  exact isQuasiProjective_of_isRegular_of_topologicalKrullDim_le_two p
    (isRegular_of_isSmoothScheme sY hsm) hdim.le

omit [IsAlgClosed k] in
/-- The contraction theorem (Stacks, Tag 0C2N (2)) applied to an exceptional curve of the first
kind in a fibre of a quasi-projective `p`. -/
theorem exists_isContractionOfExceptionalCurve_of_isQuasiProjective [LocallyOfFiniteType sZ]
    [QuasiCompact sZ] (p : Y ⟶ Z) [LocallyOfFiniteType p] [QuasiCompact p]
    (hp : IsQuasiProjective p) {D : Y.IdealSheafData} {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e) {z : Z}
    (hz : p.base '' (D.support : Set Y) = {z}) :
    ∃ (Y' : Scheme.{u}) (c : Y ⟶ Y') (p' : Y' ⟶ Z),
      IsContractionOfExceptionalCurve D c ∧ c ≫ p' = p ∧ IsQuasiProjective p' := by
  have : IsNoetherian Z := isNoetherian_of_finiteType sZ
  exact exists_isContractionOfExceptionalCurve_isQuasiProjective p hE z
    (fun x hx => hz.subset ⟨x, hx, rfl⟩) hp

variable {sY}

omit [IsAlgClosed k] in
/-- The centre `z` of a contraction: a closed, non-isolated regular point of dimension two over
which `D` lies, off which the contraction is an isomorphism. -/
private theorem IsContractionOfExceptionalCurve.exists_centre {Y' : Scheme.{u}}
    {D : Y.IdealSheafData} {c : Y ⟶ Y'} (hc : IsContractionOfExceptionalCurve D c) :
    ∃ (z : Y') (hz : IsClosed ({z} : Set Y')), Dense ({z}ᶜ : Set Y') ∧
      IsRegularLocalRing (Y'.presheaf.stalk z) ∧ ringKrullDim (Y'.presheaf.stalk z) = 2 ∧
      (D.support : Set Y) = c ⁻¹' {z} ∧
      IsIso (c ∣_ (⟨{z}ᶜ, hz.isOpen_compl⟩ : Y'.Opens)) := by
  obtain ⟨z, hz, hreg, hdim, hD, e, he⟩ := hc.exists_blowUp_iso
  have hI : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{z}, hz⟩ : TopologicalSpace.Closeds Y')).support : Set Y') = {z} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hsupp : (D.support : Set Y) = c ⁻¹' {z} := by
    rw [hD, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hI]
  refine ⟨z, hz, ?_, hreg, hdim, hsupp, isIso_morphismRestrict_compl_of_blowUp_iso _ z hz hI e he⟩
  have hdim' : Order.coheight z = 2 := by
    have h1 : (Order.coheight z : WithBot ℕ∞) = 2 := by
      rw [← ringKrullDim_stalk_eq_coheight, hdim]
    refine WithBot.coe_injective (h1.trans ?_)
    rfl
  have hnm : ¬ IsMax z := by
    intro h
    have := (Order.coheight_eq_zero.2 h)
    rw [hdim'] at this
    simp at this
  obtain ⟨y, hzy, hyz⟩ := not_isMax_iff.1 hnm
  have hspec : y ⤳ z := hzy
  have hyW : y ∈ ({z}ᶜ : Set Y') := fun h => hyz (by rw [Set.mem_singleton_iff.1 h])
  have hz2 : z ∈ closure ({z}ᶜ : Set Y') :=
    closure_mono (Set.singleton_subset_iff.2 hyW) hspec.mem_closure
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro y'
  by_cases hy : y' = z
  · rw [hy]; exact hz2
  · exact subset_closure hy

/-- A contraction of an exceptional curve `D` is an isomorphism off `D` and contracts `D` to a
point. -/
theorem IsContractionOfExceptionalCurve.exists_isIso_morphismRestrict {Y' : Scheme.{u}}
    {D : Y.IdealSheafData} {c : Y ⟶ Y'} (hc : IsContractionOfExceptionalCurve D c) :
    ∃ (q : Y') (U : Y'.Opens), (U : Set Y') = {q}ᶜ ∧
      (c ⁻¹ᵁ U : Set Y) = (D.support : Set Y)ᶜ ∧ IsIso (c ∣_ U) := by
  obtain ⟨z, hz, -, -, -, hsupp, hiso⟩ := IsContractionOfExceptionalCurve.exists_centre hc
  refine ⟨z, ⟨{z}ᶜ, hz.isOpen_compl⟩, rfl, ?_, hiso⟩
  rw [hsupp]
  rfl

omit [IsAlgClosed k] in
/-- A contraction of an exceptional curve is surjective: it is proper, and its image contains the
dense open complement of the centre. -/
private theorem IsContractionOfExceptionalCurve.surjective_base {Y' : Scheme.{u}}
    {D : Y.IdealSheafData} {c : Y ⟶ Y'} (hc : IsContractionOfExceptionalCurve D c) :
    Surjective c := by
  have := AlgebraicGeometry.IsContractionOfExceptionalCurve.isProper hc
  obtain ⟨z, hz, hdense, -, -, -, hoff⟩ := IsContractionOfExceptionalCurve.exists_centre hc
  let W : Y'.Opens := ⟨({z} : Set Y')ᶜ, hz.isOpen_compl⟩
  have : IsIso (c ∣_ W) := hoff
  have hW : (W : Set Y') ⊆ Set.range c.base := by
    intro y hyW
    obtain ⟨x, hx⟩ := (asIso (c ∣_ W)).hom.homeomorph.surjective ⟨y, hyW⟩
    refine ⟨(c ⁻¹ᵁ W).ι x, ?_⟩
    have : ((c ∣_ W) ≫ W.ι) x = y := congrArg (fun t : W => (t : Y')) hx
    rwa [morphismRestrict_ι] at this
  have : closure (({z} : Set Y')ᶜ) ⊆ Set.range c.base :=
    closure_minimal hW c.isClosedMap.isClosed_range
  rw [hdense.closure_eq] at this
  exact ⟨fun y => this (Set.mem_univ y)⟩

omit [IsAlgClosed k] in
/-- If `c` restricts to an isomorphism over a nonempty open `U`, then `c ⁻¹ᵁ U` is nonempty. -/
private theorem nonempty_preimage_of_isIso_morphismRestrict {Y' : Scheme.{u}} (c : Y ⟶ Y')
    (U : Y'.Opens) [IsIso (c ∣_ U)] (hU : (U : Set Y').Nonempty) :
    ((c ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨x, -⟩ := (asIso (c ∣_ U)).hom.homeomorph.surjective ⟨y, hy⟩
  exact ⟨x.1, x.2⟩

omit [IsAlgClosed k] in
/-- The stalks of the target of a contraction at the points off the centre are regular, being
those of the isomorphic open subscheme of the regular source. -/
private theorem isRegularLocalRing_stalk_of_isIso_morphismRestrict {Y' : Scheme.{u}}
    (c : Y ⟶ Y') (U : Y'.Opens) [IsIso (c ∣_ U)]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : Y') (hx : x ∈ U) :
    IsRegularLocalRing (Y'.presheaf.stalk x) := by
  let e : (c ⁻¹ᵁ U).toScheme ≅ U.toScheme := asIso (c ∣_ U)
  let x' : U := ⟨x, hx⟩
  let w : (c ⁻¹ᵁ U).toScheme := e.inv x'
  have h1 : IsRegularLocalRing ((c ⁻¹ᵁ U).toScheme.presheaf.stalk w) := by
    have := hY w.1
    exact IsRegularLocalRing.of_ringEquiv ((c ⁻¹ᵁ U).stalkIso w).commRingCatIsoToRingEquiv.symm
  have h2 : IsRegularLocalRing (U.toScheme.presheaf.stalk x') := by
    have : IsIso (e.inv.stalkMap x') := IsOpenImmersion.instIsIsoCommRingCatStalkMap e.inv x'
    exact IsRegularLocalRing.of_ringEquiv (asIso (e.inv.stalkMap x')).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso x').commRingCatIsoToRingEquiv

omit [IsAlgClosed k] in
/-- A contraction of an exceptional curve on a `k`-variety is a birational morphism. -/
theorem IsContractionOfExceptionalCurve.isBirationalMorphism
    (hY : AlgebraicGeometry.IsVariety k sY) {Y' : Scheme.{u}} {D : Y.IdealSheafData}
    {c : Y ⟶ Y'} (hc : IsContractionOfExceptionalCurve D c) : IsBirationalMorphism c := by
  have := hY.toIsIntegral
  obtain ⟨z, hz, hdense, -, -, -, hiso⟩ := IsContractionOfExceptionalCurve.exists_centre hc
  let U : Y'.Opens := ⟨({z} : Set Y')ᶜ, hz.isOpen_compl⟩
  have : IsIso (c ∣_ U) := hiso
  have : Nonempty Y' := ⟨z⟩
  have hdY : Dense ((c ⁻¹ᵁ U : Y.Opens) : Set Y) :=
    (c ⁻¹ᵁ U).isOpen.dense (nonempty_preimage_of_isIso_morphismRestrict c U hdense.nonempty)
  refine ⟨⟨c ⁻¹ᵁ U, hdY, U, hdense, asIso (c ∣_ U)⟩, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨c ⁻¹ᵁ U, hdY, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, asIso_hom, Scheme.topIso_hom]
  rw [morphismRestrict_ι]
  erw [Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]

/-- If `c : Y ⟶ Y'` contracts an exceptional curve on a smooth surface `Y` over `k`, and
`p' : Y' ⟶ Z` is quasi-projective over a separated `k`-scheme of finite type, then `Y'` is a
smooth surface over `k`. -/
theorem IsContractionOfExceptionalCurve.isVariety_and_isSmoothScheme_and_topologicalKrullDim_eq_two
    [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (hY : AlgebraicGeometry.IsVariety k sY) (hsm : IsSmoothScheme sY)
    (hdim : topologicalKrullDim Y = 2) {Y' : Scheme.{u}} {D : Y.IdealSheafData} {c : Y ⟶ Y'}
    {p' : Y' ⟶ Z} (hc : IsContractionOfExceptionalCurve D c) (hp' : IsQuasiProjective p') :
    AlgebraicGeometry.IsVariety k (p' ≫ sZ) ∧ IsSmoothScheme (p' ≫ sZ) ∧
      topologicalKrullDim Y' = 2 := by
  have hYi := hY.toIsIntegral
  have hYreg := ((isRegular_iff_regular_stalks Y).1 (isRegular_of_isSmoothScheme sY hsm)).2
  obtain ⟨z, hz, hdense, hregz, -, -, hiso⟩ := IsContractionOfExceptionalCurve.exists_centre hc
  let U : Y'.Opens := ⟨({z} : Set Y')ᶜ, hz.isOpen_compl⟩
  have : IsIso (c ∣_ U) := hiso
  have hreg : ∀ x : Y', IsRegularLocalRing (Y'.presheaf.stalk x) := by
    intro x
    by_cases hx : x = z
    · exact hx ▸ hregz
    · exact isRegularLocalRing_stalk_of_isIso_morphismRestrict c U hYreg x hx
  have hsurj := IsContractionOfExceptionalCurve.surjective_base hc
  have : Nonempty Y' := ⟨z⟩
  have hirr : IrreducibleSpace Y' := by
    have h := (IrreducibleSpace.isIrreducible_univ Y).image c.base c.continuous.continuousOn
    rw [Set.image_univ, hsurj.surj.range_eq] at h
    exact (irreducibleSpace_def Y').2 h
  have : ∀ x : Y', IsReduced (Y'.presheaf.stalk x) := fun x => by
    have := hreg x
    have : IsDomain (Y'.presheaf.stalk x) := IsRegularLocalRing.isDomain _
    infer_instance
  have : IsReduced Y' := isReduced_of_isReduced_stalk Y'
  have : IsIntegral Y' := isIntegral_of_irreducibleSpace_of_isReduced Y'
  have : IsSeparated p' := hp'.isSeparated
  have : LocallyOfFiniteType p' := hp'.locallyOfFiniteType
  have : QuasiCompact p' := hp'.quasiCompact
  have hvar : AlgebraicGeometry.IsVariety k (p' ≫ sZ) := {}
  refine ⟨hvar, ?_, ?_⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hsm' : InfinitesimalLifting.SmoothAt (p' ≫ sZ) x :=
      (smoothAt_locus_eq_regular_locus k (p' ≫ sZ)).symm.subset (hreg x)
    obtain ⟨V, hxV, hV⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp _ x).1 hsm'
    exact MMP.Mori.le_smoothLocus (p' ≫ sZ) hV hxV
  · have h1 := topologicalKrullDim_eq_of_isOpen k Y sY ((c ⁻¹ᵁ U : Y.Opens) : Set Y)
      (c ⁻¹ᵁ U).isOpen (nonempty_preimage_of_isIso_morphismRestrict c U hdense.nonempty)
    have h2 := topologicalKrullDim_eq_of_isOpen k Y' (p' ≫ sZ) (U : Set Y') U.isOpen
      hdense.nonempty
    have h3 : topologicalKrullDim ((c ⁻¹ᵁ U : Y.Opens) : Set Y) =
        topologicalKrullDim (U : Set Y') :=
      IsHomeomorph.topologicalKrullDim_eq _ (asIso (c ∣_ U)).hom.homeomorph.isHomeomorph
    rw [h2, ← h3, ← h1, hdim]

/-- If `c ≫ p' = p` with `p` proper, `c` proper surjective and `p'` quasi-projective, then `p'` is
proper. -/
theorem isProper_of_comp_of_isContractionOfExceptionalCurve {Y' : Scheme.{u}}
    {D : Y.IdealSheafData} {c : Y ⟶ Y'} {p : Y ⟶ Z} {p' : Y' ⟶ Z} [IsProper p]
    (hc : IsContractionOfExceptionalCurve D c) (hcp : c ≫ p' = p)
    (hp' : IsQuasiProjective p') : IsProper p' := by
  have := hp'.isSeparated
  have := hp'.locallyOfFiniteType
  have := IsContractionOfExceptionalCurve.surjective_base hc
  have := AlgebraicGeometry.IsContractionOfExceptionalCurve.isProper hc
  have : UniversallyClosed (c ≫ p') := by
    rw [hcp]
    infer_instance
  have : UniversallyClosed p' := UniversallyClosed.of_comp_surjective c p'
  exact ⟨⟩

end Steps

/-! ### The contraction -/

/-- **Relative contraction of a smooth minus-one curve.** Let `k` be an algebraically closed field
of arbitrary characteristic, let `Y` be a smooth surface over `k`, let `Z` be a separated
finite-type `k`-scheme and `p : Y → Z` proper. If `C ⊂ Y` is a smooth proper rational curve with
`C² = -1` and `p(C)` a point, then there are a smooth surface `Y'`, a proper birational
contraction `c : Y → Y'` isomorphic off `C`, and a proper `p' : Y' → Z` with `p = p' ∘ c`. -/
@[mmp "lem_mmp_foundation_relative_castelnuovo_contraction"]
theorem exists_contraction_of_isMinusOneCurve [QuasiCompact sY] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (hY : AlgebraicGeometry.IsVariety k sY) (hsm : IsSmoothScheme sY)
    (hdim : topologicalKrullDim Y = 2) (p : Y ⟶ Z) [IsProper p] (_hp : p ≫ sZ = sY)
    (C : MMP.Mori.PrimeDivisor Y) (hC : IsMinusOneCurve sY C)
    (hpC : ∃ z : Z, p.base '' (C.support : Set Y) = {z}) :
    ∃ (Y' : Scheme.{u}) (c : Y ⟶ Y') (p' : Y' ⟶ Z),
      (AlgebraicGeometry.IsVariety k (p' ≫ sZ) ∧ IsSmoothScheme (p' ≫ sZ) ∧
        topologicalKrullDim Y' = 2) ∧
      IsProper c ∧ IsBirationalMorphism c ∧
      (∃ (q : Y') (U : Y'.Opens), (U : Set Y') = {q}ᶜ ∧
        (c ⁻¹ᵁ U : Set Y) = (C.support : Set Y)ᶜ ∧ IsIso (c ∣_ U)) ∧
      IsProper p' ∧ c ≫ p' = p := by
  obtain ⟨z, hz⟩ := hpC
  obtain ⟨e, hE⟩ :=
    exists_isExceptionalCurveOfFirstKind_of_isMinusOneCurve sY hsm C hC
  obtain ⟨Y', c, p', hc, hcp, hp'⟩ :=
    exists_isContractionOfExceptionalCurve_of_isQuasiProjective sZ p
      (isQuasiProjective_of_smoothSurface sY sZ hsm hdim p) hE (z := z) hz
  refine ⟨Y', c, p',
    IsContractionOfExceptionalCurve.isVariety_and_isSmoothScheme_and_topologicalKrullDim_eq_two
      sZ hY hsm hdim hc hp',
    AlgebraicGeometry.IsContractionOfExceptionalCurve.isProper hc,
    IsContractionOfExceptionalCurve.isBirationalMorphism hY hc,
    IsContractionOfExceptionalCurve.exists_isIso_morphismRestrict hc,
    isProper_of_comp_of_isContractionOfExceptionalCurve hc hcp hp', hcp⟩

end MMP.Resolution.Bridges
