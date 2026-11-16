module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.SurfaceBirationalSimplicial
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CurveCartierLocal
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericFibreResidueFieldCriterion

/-!
# The finite relative cone and the null matrix of a surface contraction

Let `f : S ⟶ T` be a projective contraction (`f_* 𝒪_S = 𝒪_T`) of normal projective varieties
over an algebraically closed field `k` of characteristic zero, with `S` a `ℚ`-factorial surface
and `dim T ∈ {1, 2}`, and let `L` be a `ℚ`-Cartier divisor on `S` which is `f`-nef and `f`-big.
The closed relative cone of curves `NE̅(S/T)` is then spanned by the classes of finitely many
curves contracted by `f`. The face `{z ∈ NE̅(S/T) : (z · L) = 0}` cut out by `L` is spanned by the
classes of finitely many distinct contracted curves `C₁, …, C_r`. Since `S` is `ℚ`-factorial,
each `Cᵢ` is a `ℚ`-Cartier divisor, and the matrix `((Cᵢ · Cⱼ))` is symmetric and negative
definite with nonnegative off-diagonal entries.

When `dim T = 2` the contraction is birational and the `Cᵢ` are among its exceptional curves.
When `dim T = 1` the `Cᵢ` are components of finitely many special fibres; since `L` is positive
on a fibre, they form a proper subset of the components of each fibre, and Zariski's lemma
applies.

## Main results

* `MMP.Mori.exists_faceOfNefForm_relativeClosedConeOfCurves_eq_hull_posDef_neg`: `NE̅(S/T)` is a
  finite cone, and its `L`-null face is spanned by finitely many contracted curves whose
  intersection matrix is negative definite.
* `MMP.Fourfold.IsContraction.isBirationalMorphism_of_topologicalKrullDim_eq`: a contraction
  onto a variety of the same dimension is birational.

## Implementation notes

A `ℚ`-Cartier divisor is an element of `MMP.Mori.KCartierDivisor ℚ S`, a `ℚ`-linear combination
of Cartier divisors. Its pairing with `N₁(S/T)` is
`MMP.Mori.RelativeNumericalCurveClasses.intersectionNumber` applied to its real form
`MMP.Fourfold.KCartierDivisor.toReal L`, and the `L`-zero face is `MMP.Mori.faceOfNefForm` of
that linear form. Finite generation is stated in the stronger form the proof gives: `NE̅(S/T)`
is the cone spanned by the classes of a finite set of contracted curves. An irreducible curve
`Cᵢ` is recorded as a proper curve together with the prime divisor `Pᵢ` that has the same
generic point. The entry `(Cᵢ · Cⱼ)` is the intersection number
`MMP.Mori.QDivisor.intersectionNumber` of the `ℚ`-Cartier divisor `Pᵢ` with the curve `Cⱼ`.
"Negative definite" is `Matrix.PosDef` of the negated real matrix, which includes symmetry.
The source works over `ℂ`. The statement is made over any algebraically closed field of
characteristic zero.

The auxiliary lemmas live in the namespace `Proof_lem_mmp_surface_positive_base_null_face`,
opened only for the main result. If `dim T = 2` the contraction is birational and the cone is
spanned by its finitely many exceptional curves
(`MMP.Mori.relativeClosedConeOfCurves_eq_hull_of_isBirationalMorphism`). If `dim T = 1`, `T` is
a smooth curve and every contracted curve is a component of a fibre `f^* P`. The base field
`k(T)` is algebraically closed in `k(S)`, because `f_* 𝒪_S = 𝒪_T` and `S` is normal, so the
generic fibre is geometrically irreducible; the finiteness of the reducible fibres follows from
the triviality of the separable closure of `k(T)` in `k(S)` and [Stacks, Tag 0559]. All fibre
cycles are numerically proportional, so `NE̅(S/T)` is spanned by one fibre and the components of the
finitely many remaining fibres; this finite cone is closed, being sliced by the degree of an
`f`-ample divisor. Writing a multiple of `L` as `A + E` with `A` `f`-ample and `E` effective
(Kodaira's lemma), `L` is positive on every fibre, so its zero curves form a proper subset of the
components of each fibre and Zariski's lemma makes their intersection matrix negative definite.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §4.1
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-- **An equidimensional contraction is birational.** A contraction `f : S ⟶ T` onto a variety
of the same dimension as `S` is a birational morphism. -/
theorem IsContraction.isBirationalMorphism_of_topologicalKrullDim_eq {k : Type u} [Field k]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} {f : S ⟶ T}
    (hf : IsContraction sS sT f) (hdim : topologicalKrullDim S = topologicalKrullDim T) :
    IsBirationalMorphism f := by
  have hSv : MMP.Mori.IsVariety k sS := hf.isNormalVariety_source.1
  have hTv : MMP.Mori.IsVariety k sT := hf.isNormalVariety_target.1
  have : IsIntegral S := hSv.toIsIntegral
  have : IsIntegral T := hTv.toIsIntegral
  have : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have hproj := hf.isProjectiveMorphism
  have : IsProper f := hproj.isProjective.isProper
  have : Surjective f := ⟨hf.surjective⟩
  have hfin := MMP.Mori.finite_functionField_of_topologicalKrullDim_eq sT f hdim
  let : Algebra T.functionField S.functionField := (dominantFunctionFieldMap f).toAlgebra
  have h0 : Algebra.trdeg T.functionField S.functionField = 0 := by
    have : Module.Finite T.functionField S.functionField := by
      convert hfin using 3
      exact congrArg RingHom.toAlgebra (MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap f)
    exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)
  obtain ⟨U, hne, hU⟩ := (exists_affineOpen_isFinite_restrict_iff_eq_genericPoint f
    (Or.inr inferInstance)).mpr (eq_genericPoint_of_trdeg_functionField_eq_zero f h0)
  have hUa : IsAffineOpen (⊤ : (U : T.Opens).toScheme.Opens) := by
    have : IsAffine (U : T.Opens).toScheme := U.2
    exact isAffineOpen_top _
  have hiso₁ : IsIso ((f ∣_ (U : T.Opens)) ∣_ ⊤) := by
    rw [isIso_morphismRestrict_iff_isIso_app _ hUa, morphismRestrict_app]
    have h1 := hf.isIso_app ((U : T.Opens).ι ''ᵁ ⊤)
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ h1 ?_
    exact (S.presheaf.mapIso
      (eqToIso (image_morphismRestrict_preimage f (U : T.Opens) ⊤)).op).isIso_hom
  have hiso : IsIso (f ∣_ (U : T.Opens)) := by
    have e := morphismRestrictRestrict f (U : T.Opens) ⊤
    rw [Scheme.Opens.ι_image_top] at e
    exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).mp hiso₁
  rw [← Scheme.Hom.resLE_eq_morphismRestrict] at hiso
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, rfl⟩ := hf.surjective y
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f _ _ ⟨x, hy⟩ ⟨_, hy⟩ le_rfl hiso

end MMP.Fourfold

namespace Proof_lem_mmp_surface_positive_base_null_face

open TopologicalSpace Opposite

/-! ### Faces of finitely generated cones -/

/-- The face of a cone spanned by a set `G` on which a linear form `ℓ` is nonnegative, cut out
by `ℓ`, is spanned by the members of `G` on which `ℓ` vanishes. -/
private theorem faceOfNefForm_hull_eq {V : Type*} [AddCommGroup V] [Module ℝ V] (G : Set V)
    (ℓ : Module.Dual ℝ V) (hℓ : ∀ g ∈ G, 0 ≤ ℓ g) :
    MMP.Mori.faceOfNefForm (PointedCone.hull ℝ G : Set V) ℓ =
      (PointedCone.hull ℝ {g ∈ G | ℓ g = 0} : Set V) := by
  ext z
  constructor
  · rintro ⟨hz, hℓz⟩
    obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hz
    have hsum : ∑ i, ((c i : ℝ) * ℓ (g i)) = 0 := by
      refine Eq.trans ?_ hℓz
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show c i • (g i : V) = (c i : ℝ) • (g i : V) from rfl, map_smul, smul_eq_mul]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (c i).2 (hℓ _ (g i).2)).mp hsum
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases mul_eq_zero.mp (hterm i (Finset.mem_univ i)) with h | h
    · rw [show c i = 0 from Subtype.ext h, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(g i).2, h⟩)
  · intro hz
    refine ⟨Submodule.span_mono (fun g hg => hg.1) hz, ?_⟩
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx.2
    | zero => exact map_zero ℓ
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx =>
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, hx, smul_zero]

/-! ### Local trivializations of divisorial sheaves -/

section Trivialization

open MMP.Mori

variable {S : Scheme.{u}} [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]

/-- The section over `U` of the sheaf of rational functions given by a rational function. -/
private def ratSection (ψ : RationalFunctions S) (U : S.Opens) :
    ToType ((rationalFunctionsPresheaf S).obj (op U)) := fun Z => ψ Z.1

private theorem isDivisorialSection_inv {D : Divisor S} {U : S.Opens}
    {ψ : (RationalFunctions S)ˣ} (hψ : D.IsLocalEquation U ψ) :
    D.IsDivisorialSection U
      (ratSection ((ψ⁻¹ : (RationalFunctions S)ˣ) : RationalFunctions S) U) :=
  fun E hE => Or.inr (by
    change WithZero.exp _ ≤
      E.valuation (((ψ⁻¹ : (RationalFunctions S)ˣ) : RationalFunctions S) E.component)
    rw [E.valuation_component, PrimeDivisor.ord_inv, ← hψ E hE])

private theorem isDivisorialSection_zero_mul {D : Divisor S} {U : S.Opens}
    {ψ : (RationalFunctions S)ˣ} (hψ : D.IsLocalEquation U ψ) (φ : D.divisorialSubmodule U) :
    (0 : Divisor S).IsDivisorialSection U
      (fun Z => (ψ : RationalFunctions S) Z.1 * φ.1 Z) := by
  have h := (Divisor.divisorialMulLinearMap ψ (D' := D - MMP.Mori.principalDivisor ψ)
    (fun E => by rw [DivisorWithCoeffs.coeff_sub, MMP.Mori.coeff_principalDivisor,
      sub_add_cancel]) U φ).2
  intro E hE
  have h2 := h E hE
  rw [DivisorWithCoeffs.coeff_sub, MMP.Mori.coeff_principalDivisor, ← hψ E hE, sub_self] at h2
  simpa using h2

/-- The regular function `ψ φ` attached to a section `φ` of `𝒪_X(D)` over an open where `ψ` is a
local equation of `D`. -/
private noncomputable def trivSection {D : Divisor S} {U : S.Opens}
    {ψ : (RationalFunctions S)ˣ} (hψ : D.IsLocalEquation U ψ) (φ : D.divisorialSubmodule U) :
    Γ(S, U) :=
  (Divisor.IsDivisorialSection.exists_eq (isDivisorialSection_zero_mul hψ φ)).choose

private theorem germ_trivSection {D : Divisor S} {U : S.Opens} {ψ : (RationalFunctions S)ˣ}
    (hψ : D.IsLocalEquation U ψ) (φ : D.divisorialSubmodule U)
    (Z : {Z : irreducibleComponents S // componentGenericPoint S Z ∈ U}) :
    S.presheaf.germ U _ Z.2 (trivSection hψ φ) = (ψ : RationalFunctions S) Z.1 * φ.1 Z :=
  congrFun (Divisor.IsDivisorialSection.exists_eq
    (isDivisorialSection_zero_mul hψ φ)).choose_spec Z

private theorem trivSection_eq_iff {D : Divisor S} {U : S.Opens} {ψ : (RationalFunctions S)ˣ}
    (hψ : D.IsLocalEquation U ψ) (φ : D.divisorialSubmodule U) (r : Γ(S, U)) :
    trivSection hψ φ = r ↔ ∀ Z : {Z : irreducibleComponents S // componentGenericPoint S Z ∈ U},
      (ψ : RationalFunctions S) Z.1 * φ.1 Z = S.presheaf.germ U _ Z.2 r := by
  constructor
  · rintro rfl Z
    exact (germ_trivSection hψ φ Z).symm
  · exact fun h => toRationalFunctionsPresheaf_app_injective U
      (funext fun Z => (germ_trivSection hψ φ Z).trans (h Z))

private theorem mul_inv_apply (ψ : (RationalFunctions S)ˣ) (Z : irreducibleComponents S) :
    (ψ : RationalFunctions S) Z * ((ψ⁻¹ : (RationalFunctions S)ˣ) : RationalFunctions S) Z = 1 := by
  rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]

/-- **The trivialization of `𝒪_X(D)` by a local equation.** On an open `U` where `ψ` is a local
equation of `D`, multiplication by `ψ` identifies the sections of `𝒪_X(D)` over `U` with the
regular functions on `U` (algebraic Hartogs). -/
private noncomputable def trivEquiv {D : Divisor S} {U : S.Opens} {ψ : (RationalFunctions S)ˣ}
    (hψ : D.IsLocalEquation U ψ) : Γ(D.divisorialSheaf, U) ≃ₗ[Γ(S, U)] Γ(S, U) :=
  show D.divisorialSubmodule U ≃ₗ[Γ(S, U)] Γ(S, U) from
  { toFun := trivSection hψ
    invFun r := r • (⟨ratSection ((ψ⁻¹ : (RationalFunctions S)ˣ) : RationalFunctions S) U,
      isDivisorialSection_inv hψ⟩ : D.divisorialSubmodule U)
    map_add' φ φ' := by
      refine (trivSection_eq_iff hψ _ _).mpr fun Z => ?_
      rw [map_add, germ_trivSection, germ_trivSection]
      change _ * (φ.1 Z + φ'.1 Z) = _
      ring
    map_smul' r φ := by
      refine (trivSection_eq_iff hψ _ _).mpr fun Z => ?_
      rw [RingHom.id_apply, smul_eq_mul, map_mul, germ_trivSection]
      change _ * (S.presheaf.germ U _ Z.2 r * φ.1 Z) = _
      ring
    left_inv φ := by
      apply Subtype.ext
      funext Z
      change S.presheaf.germ U _ Z.2 (trivSection hψ φ) * _ = φ.1 Z
      rw [germ_trivSection]
      change _ * _ * ((ψ⁻¹ : (RationalFunctions S)ˣ) : RationalFunctions S) Z.1 = _
      linear_combination (φ.1 Z) * mul_inv_apply ψ Z.1
    right_inv r := by
      refine (trivSection_eq_iff hψ _ _).mpr fun Z => ?_
      change (ψ : RationalFunctions S) Z.1 * (S.presheaf.germ U _ Z.2 r *
        ((ψ⁻¹ : (RationalFunctions S)ˣ) : RationalFunctions S) Z.1) = _
      linear_combination (S.presheaf.germ U _ Z.2 r) * mul_inv_apply ψ Z.1 }

end Trivialization

/-! ### Intersection numbers against a multiple of a prime divisor -/

section Symmetry

open MMP.Mori

variable {S : Scheme.{u}} [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]

/-- The divisorial sheaf of a Cartier divisor, as an invertible module in the spelling of the
zero-scheme API. -/
private theorem isInvertible_divisorialSheaf {D : Divisor S} (hD : D.IsCartier) :
    AlgebraicGeometry.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property
      D.divisorialSheaf :=
  hD.isInvertibleModule_divisorialSheaf

/-- The zero scheme of the canonical section `1` of `𝒪_X(D)`, for `D` effective and Cartier. -/
private noncomputable def oneZeroScheme {D : Divisor S} (hD0 : 0 ≤ D) (hD : D.IsCartier) :
    S.IdealSheafData :=
  haveI := isInvertible_divisorialSheaf hD
  AlgebraicGeometry.zeroScheme S D.divisorialSheaf
    ((Divisor.divisorialSheafOneSection hD0).eval (op ⊤))

private theorem stalk_oneZeroScheme {D : Divisor S} (hD0 : 0 ≤ D) (hD : D.IsCartier) {U : S.Opens}
    {ψ : (RationalFunctions S)ˣ} (hψ : D.IsLocalEquation U ψ) (W : S.affineOpens)
    (hWU : W.1 ≤ U) (x : S) (hx : x ∈ W.1) :
    IdealSheafData.stalk (oneZeroScheme hD0 hD) x = Ideal.span {((S.presheaf.germ W.1 x hx).hom
      (trivEquiv (hψ.mono hWU) (D.divisorialSheaf.presheaf.map (homOfLE le_top).op
        ((Divisor.divisorialSheafOneSection hD0).eval (op ⊤)))))} := by
  haveI := isInvertible_divisorialSheaf hD
  exact Stacks.Divisors.stalk_zeroScheme_eq_span_germ D.divisorialSheaf _ W
    (trivEquiv (hψ.mono hWU)) _ rfl x hx

private theorem germ_trivEquiv_one {D : Divisor S} (hD0 : 0 ≤ D) {U : S.Opens}
    {ψ : (RationalFunctions S)ˣ} (hψ : D.IsLocalEquation U ψ)
    (Z : {Z : irreducibleComponents S // componentGenericPoint S Z ∈ U}) :
    S.presheaf.germ U _ Z.2 (trivEquiv hψ (D.divisorialSheaf.presheaf.map (homOfLE le_top).op
        ((Divisor.divisorialSheafOneSection hD0).eval (op ⊤)))) =
      (ψ : RationalFunctions S) Z.1 := by
  refine (germ_trivSection hψ _ Z).trans ?_
  change _ * (1 : RationalFunctions S) Z.1 = _
  rw [Pi.one_apply, mul_one]

/-- **The multiplicity of the zero scheme along a prime divisor.** At the generic point of a prime
divisor `Q`, the local ring of the zero scheme of the canonical section of `𝒪_X(D)` has length
`d_Q`. -/
private theorem length_quotient_stalk_oneZeroScheme {D : Divisor S} (hD0 : 0 ≤ D) (hD : D.IsCartier)
    (Q : MMP.Mori.PrimeDivisor S) :
    Module.length (S.presheaf.stalk Q.genericPoint) (S.presheaf.stalk Q.genericPoint ⧸
      IdealSheafData.stalk (oneZeroScheme hD0 hD) Q.genericPoint) = (D.coeff Q).toNat := by
  obtain ⟨U, hξU, ψ, hψ⟩ := hD Q.genericPoint
  obtain ⟨W₀, hW₀, hξW, hWU⟩ := exists_isAffineOpen_mem_and_subset (U := U) hξU
  set W : S.affineOpens := ⟨W₀, hW₀⟩
  rw [stalk_oneZeroScheme hD0 hD hψ W hWU _ hξW]
  set a := trivEquiv (hψ.mono hWU) (D.divisorialSheaf.presheaf.map (homOfLE le_top).op
        ((Divisor.divisorialSheafOneSection hD0).eval (op ⊤)))
  set b : Q.localRing := (S.presheaf.germ W.1 Q.genericPoint hξW).hom a
  have := Q.isDiscreteValuationRing_localRing
  -- the image of `b` in the function field is `ψ`
  have hηW : componentGenericPoint S Q.component ∈ W.1 :=
    Q.specializes_genericPoint.mem_open W.1.isOpen hξW
  have hb : Q.toComponent.hom b = (ψ : RationalFunctions S) Q.component := by
    have h1 := germ_trivEquiv_one hD0 (hψ.mono hWU) ⟨Q.component, hηW⟩
    refine Eq.trans ?_ h1
    change (S.presheaf.stalkSpecializes Q.specializes_genericPoint).hom
      ((S.presheaf.germ W.1 Q.genericPoint hξW).hom a) = _
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact (Units.ne_zero ((RationalFunctions.unitsEquiv S ψ) Q.component)) hb.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Q.localRing
  obtain ⟨n, w, hbw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hn : (n : ℤ) = D.coeff Q := by
    have h := Q.valuation_component ψ
    rw [← hb, hbw, map_mul, map_pow, map_mul, map_pow, Q.valuation_toComponent_of_isUnit w.isUnit,
      Q.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul,
      ← hψ Q ⟨Q.genericPoint, ?_, hξU⟩] at h
    · simpa using WithZero.exp_injective h
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hspan : Ideal.span {b} = IsLocalRing.maximalIdeal Q.localRing ^ n := by
    rw [hbw, Ideal.span_singleton_mul_left_unit w.isUnit,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow]
  rw [hspan, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ← hn]
  simp

/-- An ideal sheaf whose stalk at `x` is the unit ideal does not contain `x` in its support. -/
private theorem notMem_support_of_stalk_eq_top (I : S.IdealSheafData) {x : S}
    (h : IdealSheafData.stalk I x = ⊤) : x ∉ I.support := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW, Scheme.mem_zeroLocus_iff]
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨W, hW⟩ hxW] at h
  intro hall
  have hle : Ideal.map (S.presheaf.germ W x hxW).hom (I.ideal ⟨W, hW⟩) ≤
      IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    have := hall g hg
    rw [Scheme.mem_basicOpen _ _ _ hxW] at this
    exact (IsLocalRing.mem_maximalIdeal _).mpr this
  rw [h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- Off the support of `D`, the zero scheme of the canonical section is the unit ideal. -/
private theorem notMem_support_oneZeroScheme {D : Divisor S} (hD0 : 0 ≤ D) (hD : D.IsCartier)
    {x : S} (hx : x ∉ D.supp) : x ∉ (oneZeroScheme hD0 hD).support := by
  set U : S.Opens := ⟨(D.supp : Set S)ᶜ, D.supp.isClosed.isOpen_compl⟩
  have hψ : D.IsLocalEquation U 1 := by
    intro E hE
    rw [PrimeDivisor.ord_one]
    by_contra hne
    obtain ⟨y, hyE, hyU⟩ := hE
    exact hyU (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hyE⟩)
  obtain ⟨W₀, hW₀, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (U := U) (show x ∈ U from hx)
  set W : S.affineOpens := ⟨W₀, hW₀⟩
  refine notMem_support_of_stalk_eq_top _ ?_
  rw [stalk_oneZeroScheme hD0 hD hψ W hWU _ hxW]
  have ha : trivEquiv (hψ.mono hWU) (D.divisorialSheaf.presheaf.map (homOfLE le_top).op
      ((Divisor.divisorialSheafOneSection hD0).eval (op ⊤))) = 1 := by
    apply toRationalFunctionsPresheaf_app_injective W₀
    funext Z
    rw [map_one]
    exact (germ_trivEquiv_one hD0 (hψ.mono hWU) Z).trans rfl
  rw [ha, map_one, Ideal.span_singleton_one]

/-- The canonical section `1` of `𝒪_X(D)` is nonzero on an integral scheme. -/
private theorem divisorialSheafOneSection_eval_ne_zero [IsIntegral S] {D : Divisor S}
    (hD0 : 0 ≤ D) :
    (Divisor.divisorialSheafOneSection hD0).eval (op ⊤) ≠ 0 := by
  intro h
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents S) := by
    obtain ⟨x⟩ : Nonempty S := inferInstance
    obtain ⟨Z, hZ⟩ := MMP.Mori.exists_mem_irreducibleComponents x
    exact ⟨Z⟩
  have h1 := congrArg (fun φ : D.divisorialSubmodule ⊤ => φ.1 ⟨Z, trivial⟩) h
  change (1 : S.presheaf.stalk (componentGenericPoint S Z)) = 0 at h1
  have hf := RationalFunctions.isField_stalk (X := S) Z
  obtain ⟨a, b, hab⟩ := hf.exists_pair_ne
  exact hab (by rw [← one_mul a, ← one_mul b, h1, zero_mul, zero_mul])

/-- Off its support, an ideal sheaf induces the unit ideal in the local ring. -/
private theorem stalk_eq_top_of_notMem_support (I : S.IdealSheafData) {x : S}
    (hx : x ∉ I.support) : IdealSheafData.stalk I x = ⊤ := by
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW,
    Scheme.mem_zeroLocus_iff] at hx
  push Not at hx
  obtain ⟨g, hg, hgx⟩ := hx
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨W, hW⟩ hxW]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hg)
    ((Scheme.mem_basicOpen _ _ _ hxW).1 hgx)

/-- The support of `N Q` is the support of `Q`, for `0 < N`. -/
private theorem mem_supp_smul_single_iff {Q : MMP.Mori.PrimeDivisor S} {N : ℕ} (hN : 0 < N)
    (x : S) : x ∈ (((N : ℤ) • Finsupp.single Q 1 : Divisor S)).supp ↔ x ∈ Q.support := by
  classical
  rw [DivisorWithCoeffs.mem_supp_iff]
  constructor
  · rintro ⟨E, hE, hxE⟩
    have : E = Q := by
      by_contra hne
      apply hE
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hne]
    exact this ▸ hxE
  · intro hx
    refine ⟨Q, ?_, hx⟩
    simp [DivisorWithCoeffs.coeff_apply, hN.ne']

/-- The multiplicity of the structure sheaf of a closed subscheme at a point is the length of the
quotient of the local ring by the stalk of the ideal sheaf. -/
private theorem sheafMultiplicity_pushforward_subschemeι (I : S.IdealSheafData) (z : I.subscheme) :
    Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward I.subschemeι).obj
        (Stacks.Ample.unitModule I.subscheme)) (I.subschemeι z) =
      (Module.length (S.presheaf.stalk (I.subschemeι z))
        (S.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z))).toNat := by
  unfold Stacks.Chow.sheafMultiplicity
  congr 2
  rw [Stacks.Chow.length_stalk_pushforwardStructureSheaf I.subschemeι z
    (IsClosedImmersion.isClosedEmbedding I.subschemeι).isInducing]
  letI : Module (S.presheaf.stalk (I.subschemeι z)) (I.subscheme.presheaf.stalk z) :=
    Module.compHom (I.subscheme.presheaf.stalk z) (I.subschemeι.stalkMap z).hom
  let e : (S.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z)) ≃+*
      I.subscheme.presheaf.stalk z :=
    (Ideal.quotEquivOfEq (IdealSheafData.ker_stalkMap_subschemeι_eq_stalk I z).symm).trans
      (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective z))
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = (I.subschemeι.stalkMap z).hom a := fun a => rfl
  let e' : (S.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z)) ≃ₗ[
      S.presheaf.stalk (I.subschemeι z)] I.subscheme.presheaf.stalk z :=
    { e.toAddEquiv with
      map_smul' := fun r q => by
        induction q using Submodule.Quotient.induction_on with
        | H a =>
          change e (Ideal.Quotient.mk _ (r * a)) =
            (I.subschemeι.stalkMap z).hom r * e (Ideal.Quotient.mk _ a)
          rw [he, he, map_mul] }
  exact e'.length_eq.symm

/-- The intersection number depends on the family of invertible sheaves only through its values. -/
private theorem intersectionNumber_congr_family {k : Type u} [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    {L M : Fin d → X.Modules} [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)] (h : L = M) :
    intersectionNumber k f i d hd L = intersectionNumber k f i d hd M := by
  subst h
  rfl

private theorem coeff_natCast_smul_single_self (Q : MMP.Mori.PrimeDivisor S) (N : ℕ) :
    ((N : ℤ) • Finsupp.single Q 1 : Divisor S).coeff Q = N := by
  classical
  simp [DivisorWithCoeffs.coeff_apply]

private theorem genericPoint_mem_support_oneZeroScheme (Q : MMP.Mori.PrimeDivisor S) {N : ℕ}
    (hN : 0 < N) (hD0 : 0 ≤ ((N : ℤ) • Finsupp.single Q 1 : Divisor S))
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) :
    Q.genericPoint ∈ (oneZeroScheme hD0 hD).support := by
  have hlen := length_quotient_stalk_oneZeroScheme hD0 hD Q
  by_contra h
  rw [stalk_eq_top_of_notMem_support _ h] at hlen
  have : Module.length (S.presheaf.stalk Q.genericPoint)
      (S.presheaf.stalk Q.genericPoint ⧸ (⊤ : Ideal (S.presheaf.stalk Q.genericPoint))) = 0 :=
    Module.length_eq_zero
  rw [this, coeff_natCast_smul_single_self] at hlen
  have h0 : ((N : ℤ)).toNat = 0 := by exact_mod_cast hlen.symm
  omega

private theorem genericPoint_mem_range_subschemeι_oneZeroScheme (Q : MMP.Mori.PrimeDivisor S)
    {N : ℕ} (hN : 0 < N) (hD0 : 0 ≤ ((N : ℤ) • Finsupp.single Q 1 : Divisor S))
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) :
    Q.genericPoint ∈ Set.range (oneZeroScheme hD0 hD).subschemeι := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact genericPoint_mem_support_oneZeroScheme Q hN hD0 hD

private theorem support_oneZeroScheme_natCast_smul_single (Q : MMP.Mori.PrimeDivisor S) {N : ℕ}
    (hN : 0 < N) (hD0 : 0 ≤ ((N : ℤ) • Finsupp.single Q 1 : Divisor S))
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) :
    ((oneZeroScheme hD0 hD).support : Set S) = Q.support := by
  refine subset_antisymm (fun x hx => ?_) ?_
  · by_contra hxQ
    exact notMem_support_oneZeroScheme hD0 hD
      (fun h => hxQ ((mem_supp_smul_single_iff hN x).mp h)) hx
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr
      (genericPoint_mem_support_oneZeroScheme Q hN hD0 hD)) (oneZeroScheme hD0 hD).support.isClosed

private theorem supp_pushforward_oneZeroScheme (Q : MMP.Mori.PrimeDivisor S) {N : ℕ}
    (hN : 0 < N) (hD0 : 0 ≤ ((N : ℤ) • Finsupp.single Q 1 : Divisor S))
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) :
    _root_.SheafOfModules.supp ((Scheme.Modules.pushforward
      ((oneZeroScheme hD0 hD).subschemeι ≫ 𝟙 S)).obj
        (Stacks.Ample.unitModule (oneZeroScheme hD0 hD).subscheme)) = Q.support := by
  rw [Stacks.Chow.supp_pushforwardStructureSheaf,
    ← support_oneZeroScheme_natCast_smul_single Q hN hD0 hD,
    ← Scheme.IdealSheafData.range_subschemeι]
  rfl

private theorem sheafMultiplicity_pushforward_oneZeroScheme (Q : MMP.Mori.PrimeDivisor S) {N : ℕ}
    (hN : 0 < N) (hD0 : 0 ≤ ((N : ℤ) • Finsupp.single Q 1 : Divisor S))
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) :
    Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pushforward
      ((oneZeroScheme hD0 hD).subschemeι ≫ 𝟙 S)).obj
        (Stacks.Ample.unitModule (oneZeroScheme hD0 hD).subscheme)) Q.genericPoint = N := by
  obtain ⟨z, hz⟩ := genericPoint_mem_range_subschemeι_oneZeroScheme Q hN hD0 hD
  have e : (Scheme.Modules.pushforward ((oneZeroScheme hD0 hD).subschemeι ≫ 𝟙 S)).obj
      (Stacks.Ample.unitModule (oneZeroScheme hD0 hD).subscheme) ≅
      (Scheme.Modules.pushforward (oneZeroScheme hD0 hD).subschemeι).obj
        (Stacks.Ample.unitModule (oneZeroScheme hD0 hD).subscheme) :=
    ((Scheme.Modules.pushforwardComp (oneZeroScheme hD0 hD).subschemeι (𝟙 S)).app _).symm ≪≫
      (Scheme.Modules.pushforwardId S).app _
  rw [Stacks.Chow.sheafMultiplicity_eq_of_iso e, ← hz, sheafMultiplicity_pushforward_subschemeι,
    hz, length_quotient_stalk_oneZeroScheme hD0 hD Q, coeff_natCast_smul_single_self]
  simp

private theorem subschemeι_genericPoint_vanishingIdeal_closure (x : S)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set S))).subscheme] :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set S))).subschemeι
      (genericPoint (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set S))).subscheme) = x := by
  set Y := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set S)) with hY
  have h := (genericPoint_spec Y.subscheme).image Y.subschemeι.continuous
  rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
    Y.support.isClosed.closure_eq] at h
  refine h.eq ?_
  rw [hY, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  exact isGenericPoint_closure

private theorem support_eq_of_topDimIntegralSubscheme {F : S.Modules}
    {Q : MMP.Mori.PrimeDivisor S} (hsuppF : _root_.SheafOfModules.supp F = Q.support)
    (hdimF : topologicalKrullDim (_root_.SheafOfModules.supp F) = 1)
    (W : TopDimIntegralSubscheme F) : (W.1.support : Set S) = Q.support := by
  have := W.2.1
  set w := W.1.subschemeι (genericPoint W.1.subscheme)
  have hw : IsGenericPoint w (W.1.support : Set S) := by
    have h := (genericPoint_spec W.1.subscheme).image W.1.subschemeι.continuous
    rwa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι,
      W.1.support.isClosed.closure_eq] at h
  have hwQ : w ∈ Q.support := by
    rw [← hsuppF]
    exact W.2.2.1 hw.mem
  have hξ : IsGenericPoint Q.genericPoint (Q.support : Set S) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isGenericPoint_closure
  have hhw : Order.height w = 1 := by
    have h1 : topologicalKrullDim W.1.subscheme = 1 := W.2.2.2.trans hdimF
    rw [← topologicalKrullDim_range_eq W.1.subschemeι,
      Scheme.IdealSheafData.range_subschemeι, ← hw.def,
      MMP.topologicalKrullDim_closure_singleton_eq_height] at h1
    exact_mod_cast h1
  have hhξ : Order.height Q.genericPoint = 1 := by
    have h1 := hdimF
    rw [hsuppF, ← hξ.def, MMP.topologicalKrullDim_closure_singleton_eq_height] at h1
    exact_mod_cast h1
  have hle : w ≤ Q.genericPoint :=
    Scheme.le_iff_specializes.mpr (hξ.specializes hwQ)
  have hweq : w = Q.genericPoint := by
    by_contra hne
    have hlt' : w < Q.genericPoint := lt_of_le_not_ge hle fun h => hne
      ((Scheme.le_iff_specializes.mp hle).antisymm (Scheme.le_iff_specializes.mp h)).eq.symm
    have hlt := Order.height_strictMono hlt' (by rw [hhw]; decide)
    rw [hhw, hhξ] at hlt
    exact lt_irrefl _ hlt
  rw [← hw.def, hweq, hξ.def]

private theorem subsingleton_topDimIntegralSubscheme {F : S.Modules}
    {Q : MMP.Mori.PrimeDivisor S} (hsuppF : _root_.SheafOfModules.supp F = Q.support)
    (hdimF : topologicalKrullDim (_root_.SheafOfModules.supp F) = 1) :
    Subsingleton (TopDimIntegralSubscheme F) :=
  ⟨fun W W' => TopDimIntegralSubscheme.val_injective F (by
    change (W.1.support : Set S) = (W'.1.support : Set S)
    rw [support_eq_of_topDimIntegralSubscheme hsuppF hdimF W,
      support_eq_of_topDimIntegralSubscheme hsuppF hdimF W'])⟩

variable {k : Type u} [Field k] (sS : S ⟶ Spec (.of k))

private theorem intersectionNumber_tail_vanishingIdeal_eq_degreeOn [IsProper sS]
    (CQ : ProperCurve sS)
    (M L : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    (hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({CQ.point} : Set S))).subscheme ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![M, L] j) :=
      fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
    intersectionNumber k sS (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({CQ.point} : Set S))).subschemeι 1 hd (fun t => ![M, L] t.succ) =
      MMP.Mori.degreeOn k sS CQ.ι CQ.dim_le L := by
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({CQ.point} : Set S))).subscheme :=
    inferInstanceAs (IsIntegral CQ.scheme)
  haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![M, L] j) :=
    fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
  rw [intersectionNumber_congr_family sS _ 1 _
    (show (fun t : Fin 1 => ![M, L] t.succ) = fun _ => L from
      funext fun t => by fin_cases t; rfl)]
  exact intersectionNumber_one_eq_invertibleCurveDegree k sS _ _ L

private theorem intersectionNumber_divisorialSheaf_eq_mul_degreeOn_of_compactSpace [IsIntegral S]
    [IsProper sS] (hSdim : topologicalKrullDim S = 2)
    (Q : MMP.Mori.PrimeDivisor S) (CQ : ProperCurve sS)
    (hCQ : CQ.point = Q.genericPoint) {N : ℕ} (hN : 0 < N)
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L] :
    haveI := hD.isInvertibleModule_divisorialSheaf
    haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        (![((N : ℤ) • Finsupp.single Q 1 : Divisor S).divisorialSheaf, L] j) :=
      fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
    AlgebraicGeometry.intersectionNumber k sS (𝟙 S) 2 hSdim.le
        ![((N : ℤ) • Finsupp.single Q 1 : Divisor S).divisorialSheaf, L] =
      N * MMP.Mori.degreeOn k sS CQ.ι CQ.dim_le L := by
  classical
  set D : Divisor S := (N : ℤ) • Finsupp.single Q 1
  have hD0 : 0 ≤ D := smul_nonneg (Int.natCast_nonneg N) (Finsupp.single_nonneg.2 zero_le_one)
  haveI hinvD := hD.isInvertibleModule_divisorialSheaf
  haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (![D.divisorialSheaf, L] j) :=
    fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
  haveI := isInvertible_divisorialSheaf hD
  set t := Divisor.divisorialSheafOneSection hD0
  have hreg := isRegularSection_of_eval_top_ne_zero D.divisorialSheaf t
    (divisorialSheafOneSection_eval_ne_zero hD0)
  haveI hDv : Stacks.Divisors.IsEffectiveCartierDivisor (oneZeroScheme hD0 hD) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection S _ t).2 hreg
  obtain ⟨e, -⟩ := (existsUnique_invertibleSheafIso_zeroScheme S _ t hreg).exists
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k sS (𝟙 S) 1 hSdim.le
    ![D.divisorialSheaf, L] (oneZeroScheme hD0 hD)
    ((Scheme.Modules.pullbackId S).app D.divisorialSheaf ≪≫ e.symm)]
  set Z := oneZeroScheme hD0 hD
  have : Nonempty Z.subscheme :=
    (genericPoint_mem_range_subschemeι_oneZeroScheme Q hN hD0 hD).elim fun z _ => ⟨z⟩
  have hZdim : topologicalKrullDim Z.subscheme = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k sS Z hDv
      (by rw [hSdim]; rfl)
  rw [intersectionNumber_eq_sum_topDimComponents k sS (Z.subschemeι ≫ 𝟙 S) 1 hZdim]
  set F := (Scheme.Modules.pushforward (Z.subschemeι ≫ 𝟙 S)).obj
    (Stacks.Ample.unitModule Z.subscheme) with hF
  have hsuppF : _root_.SheafOfModules.supp F = Q.support :=
    supp_pushforward_oneZeroScheme Q hN hD0 hD
  have hdimF : topologicalKrullDim (_root_.SheafOfModules.supp F) = 1 := by
    rw [hF, Stacks.Chow.supp_pushforwardStructureSheaf, topologicalKrullDim_range_eq, hZdim]
    rfl
  set Y := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({CQ.point} : Set S)) with hY
  haveI hYint : IsIntegral Y.subscheme := inferInstanceAs (IsIntegral CQ.scheme)
  let W₀ : TopDimIntegralSubscheme F := ⟨Y, hYint, by
    rw [hY, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hCQ,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hsuppF], CQ.dim_eq.trans hdimF.symm⟩
  haveI := subsingleton_topDimIntegralSubscheme hsuppF hdimF
  haveI := uniqueOfSubsingleton W₀
  rw [finsum_unique, show (default : TopDimIntegralSubscheme F) = W₀ from Subsingleton.elim _ _]
  have hgp : W₀.genericPt = CQ.point := subschemeι_genericPoint_vanishingIdeal_closure CQ.point
  have hmult : Stacks.Chow.sheafMultiplicity F CQ.point = N := by
    rw [hCQ]
    exact sheafMultiplicity_pushforward_oneZeroScheme Q hN hD0 hD
  have hint : intersectionNumber k sS W₀.1.subschemeι 1
      (topologicalKrullDim_subscheme_le_of_topDimIntegralSubscheme _ hZdim W₀)
      (fun t => ![D.divisorialSheaf, L] t.succ) = MMP.Mori.degreeOn k sS CQ.ι CQ.dim_le L :=
    intersectionNumber_tail_vanishingIdeal_eq_degreeOn sS CQ D.divisorialSheaf L _
  rw [hgp, hmult, hint]

end Symmetry

/-! ### Zariski's lemma: linear algebra -/

section ZariskiLinearAlgebra

open Matrix Finset

/-- The quadratic form of a symmetric matrix with `M n = 0` as a sum of squares of differences. -/
private theorem quadratic_eq_neg_sum_sq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ)
    (hsymm : ∀ i j, M i j = M j i) (n : ι → ℝ) (hn : ∀ i, n i ≠ 0)
    (hMn : ∀ i, ∑ j, M i j * n j = 0) (x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * M i j =
      -(1 / 2) * ∑ i, ∑ j, M i j * n i * n j * (x i / n i - x j / n j) ^ 2 := by
  have hx : ∀ i, x i = n i * (x i / n i) := fun i => by field_simp [hn i]
  set y : ι → ℝ := fun i => x i / n i
  have h1 : ∑ i, ∑ j, M i j * n i * n j * y i ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ∑ j, M i j * n i * n j * y i ^ 2 = (n i * y i ^ 2) * ∑ j, M i j * n j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hMn i, mul_zero]
  have h2 : ∑ i, ∑ j, M i j * n i * n j * y j ^ 2 = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ i, M i j * n i * n j * y j ^ 2 = (n j * y j ^ 2) * ∑ i, M j i * n i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hsymm i j]; ring
    rw [this, hMn j, mul_zero]
  have h3 : ∑ i, ∑ j, x i * x j * M i j = ∑ i, ∑ j, M i j * n i * n j * (y i * y j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hx i, hx j]; ring
  have h4 : ∑ i, ∑ j, M i j * n i * n j * (y i - y j) ^ 2 =
      ∑ i, ∑ j, M i j * n i * n j * y i ^ 2 + ∑ i, ∑ j, M i j * n i * n j * y j ^ 2 -
        2 * ∑ i, ∑ j, M i j * n i * n j * (y i * y j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h3]
  change _ = -(1 / 2) * ∑ i, ∑ j, M i j * n i * n j * (y i - y j) ^ 2
  rw [h4, h1, h2]
  ring

/-- **Zariski's lemma, linear algebra.** Let `M` be a real symmetric matrix with nonnegative
off-diagonal entries, `n` a positive vector with `M n = 0`, and suppose the graph of the nonzero
entries is connected. Then `xᵀ M x < 0` for every `x ≠ 0` vanishing somewhere. -/
private theorem quadratic_neg_of_connected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hsymm : ∀ i j, M i j = M j i) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) (n : ι → ℝ)
    (hn : ∀ i, 0 < n i) (hMn : ∀ i, ∑ j, M i j * n j = 0)
    (hconn : ∀ K : Finset ι, K.Nonempty → K ≠ Finset.univ → ∃ i ∈ K, ∃ j ∉ K, M i j ≠ 0)
    (x : ι → ℝ) (hx : x ≠ 0) (i₀ : ι) (hi₀ : x i₀ = 0) :
    ∑ i, ∑ j, x i * x j * M i j < 0 := by
  rw [quadratic_eq_neg_sum_sq M hsymm n (fun i => (hn i).ne') hMn x]
  set y : ι → ℝ := fun i => x i / n i
  have hterm : ∀ i j, 0 ≤ M i j * n i * n j * (x i / n i - x j / n j) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hoff i j hij) (hn i).le) (hn j).le) (sq_nonneg _)
  have hnn : 0 ≤ ∑ i, ∑ j, M i j * n i * n j * (x i / n i - x j / n j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  rcases hnn.lt_or_eq with hpos | hzero
  · linarith
  exfalso
  have hall : ∀ i j, M i j * n i * n j * (x i / n i - x j / n j) ^ 2 = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hterm i j).mp hzero.symm i (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm i j).mp h1 j (Finset.mem_univ _)
  -- `y` vanishes on everything
  set K : Finset ι := Finset.univ.filter fun i => x i = 0
  have hK : K = Finset.univ := by
    by_contra hne
    obtain ⟨i, hi, j, hj, hij⟩ := hconn K ⟨i₀, by simp [K, hi₀]⟩ hne
    have hxi : x i = 0 := (Finset.mem_filter.mp hi).2
    have hxj : x j ≠ 0 := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have := hall i j
    rw [hxi, zero_div, zero_sub, neg_sq] at this
    have hnj := (hn j).ne'
    have hni := (hn i).ne'
    have : x j / n j = 0 := by
      have h' : M i j * n i * n j ≠ 0 := mul_ne_zero (mul_ne_zero hij hni) hnj
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp this).resolve_left h')
    exact hxj (by rwa [div_eq_zero_iff, or_iff_left hnj] at this)
  refine hx (funext fun i => ?_)
  have hi : i ∈ K := by rw [hK]; exact Finset.mem_univ i
  exact (Finset.mem_filter.mp hi).2

/-- **Zariski's lemma on a proper subset.** With `M`, `n` as in
`quadratic_neg_of_connected`, the restriction of `-M` to the image of an injective map missing
some index is positive definite. -/
private theorem posDef_neg_submatrix_of_connected {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] (M : Matrix ι ι ℝ)
    (hsymm : ∀ i j, M i j = M j i) (hoff : ∀ i j, i ≠ j → 0 ≤ M i j) (n : ι → ℝ)
    (hn : ∀ i, 0 < n i) (hMn : ∀ i, ∑ j, M i j * n j = 0)
    (hconn : ∀ K : Finset ι, K.Nonempty → K ≠ Finset.univ → ∃ i ∈ K, ∃ j ∉ K, M i j ≠ 0)
    (g : J → ι) (hg : Function.Injective g) (i₀ : ι) (hi₀ : i₀ ∉ Set.range g) :
    (-(M.submatrix g g)).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [conjTranspose_apply, hsymm (g j) (g i)]
  set y : ι → ℝ := Function.extend g x 0
  have hyg : ∀ j, y (g j) = x j := fun j => hg.extend_apply x 0 j
  have hy0 : ∀ i ∉ Set.range g, y i = 0 := fun i hi => by
    simp only [y, Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hi ⟨a, ha⟩), Pi.zero_apply]
  have hy : y ≠ 0 := by
    intro h
    apply hx
    funext j
    rw [← hyg j, h, Pi.zero_apply, Pi.zero_apply]
  have hneg := quadratic_neg_of_connected M hsymm hoff n hn hMn hconn y hy i₀ (hy0 i₀ hi₀)
  have hsum : ∀ F : ι → ℝ, (∀ i ∉ Set.range g, F i = 0) → ∑ i, F i = ∑ j, F (g j) := by
    intro F hF
    exact (Fintype.sum_of_injective g hg (fun j => F (g j)) F hF (fun _ => rfl)).symm
  have e : ∑ i, ∑ j, y i * y j * M i j = ∑ a, ∑ b, x a * x b * M (g a) (g b) := by
    rw [hsum _ (fun i hi => by simp [hy0 i hi])]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsum _ (fun i hi => by simp [hy0 i hi])]
    simp [hyg]
  have e2 : star x ⬝ᵥ ((-(M.submatrix g g)) *ᵥ x) = -∑ a, ∑ b, x a * x b * M (g a) (g b) := by
    simp only [dotProduct, mulVec, neg_apply, submatrix_apply, star_trivial, mul_sum,
      ← sum_neg_distrib]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by
      rw [Matrix.neg_apply, submatrix_apply]; ring
  rw [e2, ← e]
  linarith

end ZariskiLinearAlgebra

/-! ### Curves and prime divisors on a surface -/

section Geometry

open MMP.Mori

variable {k : Type u} [Field k] {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)}

/-- On a surface, the generic point of a proper curve is the generic point of a prime divisor. -/
private theorem exists_primeDivisor_genericPoint_eq [IsIntegral S] [LocallyOfFiniteType sS]
    (hSdim : topologicalKrullDim S = 2) (C : ProperCurve sS) :
    ∃ P : MMP.Mori.PrimeDivisor S, P.genericPoint = C.point := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS C.point
  rw [← MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, C.dim_eq, hSdim] at h
  have h1 : Order.coheight C.point = 1 := by
    generalize Order.coheight C.point = c at h ⊢
    have h' : 1 + c = 2 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
    induction c using ENat.recTopCoe with
    | top => simp at h'
    | coe n => norm_cast at h' ⊢; omega
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ h1⟩

variable [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]

/-- **Distinct curves meet nonnegatively.** On a `ℚ`-factorial variety, if `P ≠ Q` are prime
divisors and `C_Q` is the proper curve with the generic point of `Q`, then `(P · C_Q) ≥ 0`. -/
private theorem intersectionNumber_single_nonneg_of_ne (hS : MMP.Fourfold.IsQFactorial sS)
    (P Q : MMP.Mori.PrimeDivisor S) (hPQ : P ≠ Q) (CQ : ProperCurve sS)
    (hCQ : CQ.point = Q.genericPoint) :
    0 ≤ (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sS CQ.ι CQ.dim_le
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  classical
  refine (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sS _ _ ?_ CQ ?_).1
  · intro E
    rw [MMP.Threefold.Resolution.toQDivisor_single]
    change (0 : ℚ) ≤ (Finsupp.single P ((1 : ℤ) : ℚ)) E
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  · intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [MMP.Threefold.Resolution.toQDivisor_single] at hE
    have hEP : P = E := by
      by_contra hne
      exact hE (by simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hne])
    subst hEP
    rw [hCQ] at hxE
    exact hPQ (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support P Q hxE)

/-- On a `ℚ`-factorial `S`, finitely many prime divisors have a common positive Cartier
multiple. -/
private theorem exists_pos_isCartier_smul_single (hS : MMP.Fourfold.IsQFactorial sS)
    {ι : Type*} [Fintype ι] (P : ι → MMP.Mori.PrimeDivisor S) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ((N : ℤ) • Finsupp.single (P i) 1 : Divisor S).IsCartier := by
  classical
  choose m hm hmC using fun i => hS.2 (Finsupp.single (P i) 1)
  refine ⟨∏ j, m j, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ m (Finset.mem_univ i), Nat.cast_mul, mul_comm, mul_smul]
  exact (hmC i).zsmul _

private theorem isCartier_sum {ι : Type*} (s : Finset ι) (D : ι → Divisor S)
    (h : ∀ j, (D j).IsCartier) : (∑ j ∈ s, D j).IsCartier :=
  Divisor.cartierSubgroup.sum_mem fun j _ => h j

/-- The degree along a curve is additive over finite sums of Cartier divisors. -/
private theorem degreeOn_sum (C : ProperCurve sS) {ι : Type*} (s : Finset ι) (D : ι → Divisor S)
    (h : ∀ j, (D j).IsCartier) :
    (∑ j ∈ s, D j).degreeOn k sS C.ι C.dim_le (isCartier_sum s D h) =
      ∑ j ∈ s, (D j).degreeOn k sS C.ι C.dim_le (h j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Divisor.degreeOn_congr Finset.sum_empty _ Divisor.isCartier_zero, Finset.sum_empty]
    exact Divisor.degreeOn_zero' k sS C.ι C.dim_le
  | insert a s ha ih =>
    rw [Divisor.degreeOn_congr (Finset.sum_insert ha) _ ((h a).add (isCartier_sum s D h)),
      Finset.sum_insert ha, ← ih]
    exact Divisor.degreeOn_add k sS C.ι C.dim_le _ _ _ _

/-- A curve `C` whose generic point lies on no component of an effective Cartier divisor `D` has
`deg_C 𝒪(D) ≥ 0`. -/
private theorem degreeOn_nonneg_of_coeff_eq_zero (D : Divisor S) (hD : D.IsCartier) (h0 : 0 ≤ D)
    (C : ProperCurve sS) (P : MMP.Mori.PrimeDivisor S) (hC : C.point = P.genericPoint)
    (hP : D P = 0) : 0 ≤ D.degreeOn k sS C.ι C.dim_le hD := by
  obtain ⟨c, hc⟩ := MMP.Threefold.Mori.exists_ι_eq_point C.point
  refine (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sS C.ι C.dim_le D hD h0
    ⟨c, ?_⟩).1
  change curveSubschemeAtι C.point c ∉ _
  rw [hc, hC]
  intro hmem
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
  obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P hxE
  exact hE hP

/-- **The weights of an anti-ample divisor.** Let `Pᵢ` be distinct prime divisors with Cartier
multiples `Dᵢ = N Pᵢ` (`N > 0`), and `W ≥ 0` a Cartier divisor. On a curve `C` with the generic
point of `Pⱼ` and `deg_C 𝒪(W) < 0`, the weights `W(Pᵢ) ≥ 0` satisfy
`∑ᵢ W(Pᵢ) deg_C 𝒪(Dᵢ) < 0`. -/
private theorem sum_mul_degreeOn_neg {ι : Type*} [Fintype ι] {P : ι → MMP.Mori.PrimeDivisor S}
    (hP : Function.Injective P) {N : ℕ} (hN : 0 < N)
    (hD : ∀ i, ((N : ℤ) • Finsupp.single (P i) 1 : Divisor S).IsCartier)
    {W : Divisor S} (hW0 : 0 ≤ W) (hWc : W.IsCartier) (C : ProperCurve sS) (j : ι)
    (hC : C.point = (P j).genericPoint) (hWC : W.degreeOn k sS C.ι C.dim_le hWc < 0) :
    ∑ i, W (P i) * ((N : ℤ) • Finsupp.single (P i) 1 : Divisor S).degreeOn k sS C.ι C.dim_le
      (hD i) < 0 := by
  classical
  set D : ι → Divisor S := fun i => (N : ℤ) • Finsupp.single (P i) 1
  have hsumc : (∑ i, W (P i) • D i).IsCartier := isCartier_sum _ _ fun i => (hD i).zsmul _
  set R : Divisor S := (N : ℤ) • W - ∑ i, W (P i) • D i
  have hRc : R.IsCartier := (hWc.zsmul _).sub hsumc
  have hR : ∀ E, R E = if ∃ i, P i = E then 0 else N * W E := fun E => by
    simp only [R, D, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply, smul_eq_mul]
    split_ifs with h
    · obtain ⟨i, rfl⟩ := h
      rw [Fintype.sum_eq_single i fun l hl => by simp [hP.ne hl]]
      simp [mul_comm]
    · push Not at h
      simp [h]
  have hR0 : 0 ≤ R := fun E => by
    change 0 ≤ R E
    rw [hR]
    split_ifs
    exacts [le_rfl, mul_nonneg (Int.natCast_nonneg N) (hW0 E)]
  have hRdeg := degreeOn_nonneg_of_coeff_eq_zero R hRc hR0 C (P j) hC (by rw [hR, if_pos ⟨j, rfl⟩])
  have h := Divisor.degreeOn_add k sS C.ι C.dim_le R _ hRc hsumc
  rw [Divisor.degreeOn_congr (sub_add_cancel _ _) _ (hWc.zsmul _),
    Divisor.degreeOn_zsmul' k sS C.ι C.dim_le W hWc,
    degreeOn_sum C _ _ fun i => (hD i).zsmul _] at h
  rw [Finset.sum_congr rfl fun i _ => Divisor.degreeOn_zsmul' k sS C.ι C.dim_le (D i) (hD i) _]
    at h
  have : (0 : ℤ) < N := by exact_mod_cast hN
  nlinarith

/-- The intersection number of a prime divisor `P` with a curve is `(1/N) deg 𝒪(N P)` for any
`N > 0` with `N P` Cartier. -/
private theorem intersectionNumber_single_eq_div (hS : MMP.Fourfold.IsQFactorial sS)
    (P : MMP.Mori.PrimeDivisor S) {N : ℕ} (hN : 0 < N)
    (hD : ((N : ℤ) • Finsupp.single P 1 : Divisor S).IsCartier) (C : ProperCurve sS) :
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sS C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
    (((N : ℤ) • Finsupp.single P 1 : Divisor S).degreeOn k sS C.ι C.dim_le hD : ℚ) / N := by
  refine QDivisor.intersectionNumber_eq_of_smul k sS C.ι C.dim_le _ _ hN _ hD ?_
  rw [map_zsmul]

/-- The Stacks intersection number `(L₁ · L₂ · S)` of two invertible sheaves on a proper surface
is symmetric. -/
private theorem intersectionNumber_pair_comm [IsProper sS] (hSdim : topologicalKrullDim S ≤ 2)
    (L₁ L₂ : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L₁]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L₂] :
    haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![L₁, L₂] j) :=
      fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
    haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![L₂, L₁] j) :=
      fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
    AlgebraicGeometry.intersectionNumber k sS (𝟙 S) 2 hSdim ![L₁, L₂] =
      AlgebraicGeometry.intersectionNumber k sS (𝟙 S) 2 hSdim ![L₂, L₁] := by
  haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (![L₁, L₂] j) :=
    fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
  have h := AlgebraicGeometry.intersectionNumber_comp_perm k sS (𝟙 S) 2 hSdim ![L₁, L₂]
    (Equiv.swap 0 1)
  refine h.symm.trans ?_
  congr 1
  funext j
  fin_cases j <;> rfl

/-- **The intersection number against a multiple of a prime divisor.** Let `S` be a normal proper
surface, `Q` a prime divisor with proper curve `C_Q`, and `N > 0` with `N Q` Cartier. For every
invertible sheaf `L`, `(𝒪_S(N Q) · L · S) = N · deg_{C_Q} L`. -/
private theorem intersectionNumber_divisorialSheaf_eq_mul_degreeOn [IsIntegral S] [IsProper sS]
    (hSdim : topologicalKrullDim S = 2) (Q : MMP.Mori.PrimeDivisor S) (CQ : ProperCurve sS)
    (hCQ : CQ.point = Q.genericPoint) {N : ℕ} (hN : 0 < N)
    (hD : ((N : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier) (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L] :
    haveI := QuasiCompact.compactSpace_of_compactSpace sS
    haveI := hD.isInvertibleModule_divisorialSheaf
    haveI : ∀ j, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
        (![((N : ℤ) • Finsupp.single Q 1 : Divisor S).divisorialSheaf, L] j) :=
      fun j => Fin.cases ‹_› (fun j => Fin.cases ‹_› (fun j => j.elim0) j) j
    AlgebraicGeometry.intersectionNumber k sS (𝟙 S) 2 hSdim.le
        ![((N : ℤ) • Finsupp.single Q 1 : Divisor S).divisorialSheaf, L] =
      N * MMP.Mori.degreeOn k sS CQ.ι CQ.dim_le L := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  exact intersectionNumber_divisorialSheaf_eq_mul_degreeOn_of_compactSpace sS hSdim Q CQ hCQ hN hD L

/-- **Symmetry of intersection numbers on a `ℚ`-factorial surface.** For prime divisors `P`, `Q`
with proper curves `C_P`, `C_Q` of the same generic points, `(Q · C_P) = (P · C_Q)`. -/
private theorem intersectionNumber_single_comm (hS : MMP.Fourfold.IsQFactorial sS)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hSdim : topologicalKrullDim S = 2)
    (P Q : MMP.Mori.PrimeDivisor S) (CP CQ : ProperCurve sS)
    (hCP : CP.point = P.genericPoint) (hCQ : CQ.point = Q.genericPoint) :
    (Divisor.toQDivisor (Finsupp.single Q 1)).intersectionNumber k sS CP.ι CP.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
      (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sS CQ.ι CQ.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  classical
  by_cases hPQ : P = Q
  · subst hPQ
    have : CP = CQ := ProperCurve.ext (hCP.trans hCQ.symm)
    subst this
    rfl
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  have : IsIntegral S := hSv.toIsIntegral
  have : IsProper sS := ((MMP.Mori.isProjectiveVariety_iff k sS).mp hSp).2.isProjective.isProper
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  obtain ⟨mP, hmP, hP⟩ := hS.2 (Finsupp.single P 1)
  obtain ⟨mQ, hmQ, hQ⟩ := hS.2 (Finsupp.single Q 1)
  have hN : 0 < mP * mQ := Nat.mul_pos hmP hmQ
  have hDP : (((mP * mQ : ℕ) : ℤ) • Finsupp.single P 1 : Divisor S).IsCartier := by
    rw [Nat.cast_mul, mul_comm, mul_smul]
    exact hP.zsmul _
  have hDQ : (((mP * mQ : ℕ) : ℤ) • Finsupp.single Q 1 : Divisor S).IsCartier := by
    rw [Nat.cast_mul, mul_smul]
    exact hQ.zsmul _
  rw [intersectionNumber_single_eq_div hS Q hN hDQ CP,
    intersectionNumber_single_eq_div hS P hN hDP CQ]
  congr 1
  have := hDP.isInvertibleModule_divisorialSheaf
  have := hDQ.isInvertibleModule_divisorialSheaf
  have key1 := intersectionNumber_divisorialSheaf_eq_mul_degreeOn hSdim Q CQ hCQ hN hDQ
    (((mP * mQ : ℕ) : ℤ) • Finsupp.single P 1 : Divisor S).divisorialSheaf
  have key2 := intersectionNumber_divisorialSheaf_eq_mul_degreeOn hSdim P CP hCP hN hDP
    (((mP * mQ : ℕ) : ℤ) • Finsupp.single Q 1 : Divisor S).divisorialSheaf
  rw [intersectionNumber_pair_comm] at key1
  have h : ((mP * mQ : ℕ) : ℤ) * MMP.Mori.degreeOn k sS CP.ι CP.dim_le
      (((mP * mQ : ℕ) : ℤ) • Finsupp.single Q 1 : Divisor S).divisorialSheaf =
      ((mP * mQ : ℕ) : ℤ) * MMP.Mori.degreeOn k sS CQ.ι CQ.dim_le
      (((mP * mQ : ℕ) : ℤ) • Finsupp.single P 1 : Divisor S).divisorialSheaf :=
    key2.symm.trans key1
  have h' := mul_left_cancel₀ (by exact_mod_cast hN.ne' : ((mP * mQ : ℕ) : ℤ) ≠ 0) h
  exact_mod_cast h'

end Geometry

/-! ### Fibres over a curve -/

section Fibre

open MMP.Mori

variable {k : Type u} [Field k] {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)}
  [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]

/-- On a proper surface, every prime divisor is the support of a proper curve. -/
private theorem exists_properCurve_of_primeDivisor [IsIntegral S] [LocallyOfFiniteType sS]
    [IsProper sS] (hSdim : topologicalKrullDim S = 2) (E : MMP.Mori.PrimeDivisor S) :
    ∃ C : ProperCurve sS, C.point = E.genericPoint := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS E.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, hSdim] at h
  have h1 : topologicalKrullDim (closure ({E.genericPoint} : Set S)) = 1 := by
    generalize topologicalKrullDim (closure ({E.genericPoint} : Set S)) = c at h ⊢
    induction c using WithBot.recBotCoe with
    | bot => exact absurd h (by decide)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd h (by decide)
      | coe d =>
        have h' : ((d + 1 : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by
          push_cast; exact h
        have hd : d = 1 := by
          have : d + 1 = 2 := by exact_mod_cast h'
          omega
        subst hd; rfl
  exact ⟨⟨E.genericPoint, isProperCurve_of_isProper sS
    (by rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, h1])⟩, rfl⟩

/-- Intersection numbers are additive over finite sums of `ℚ`-divisors, on a `ℚ`-factorial
variety. -/
private theorem intersectionNumber_finset_sum (hS : MMP.Fourfold.IsQFactorial sS) {ι : Type*}
    (s : Finset ι) (G : ι → QDivisor S) (C : ProperCurve sS) :
    (∑ i ∈ s, G i).intersectionNumber k sS C.ι C.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
      ∑ i ∈ s, (G i).intersectionNumber k sS C.ι C.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (MMP.Fourfold.intersectionNumber_congr sS C.ι C.dim_le _ QDivisor.isQCartier_zero
      rfl).trans (MMP.Fourfold.intersectionNumber_zero sS C.ι C.dim_le)
  | insert a s ha ih =>
    rw [MMP.Fourfold.intersectionNumber_congr sS C.ι C.dim_le _
      ((MMP.Fourfold.isQCartier_of_isQFactorial sS hS (G a)).add
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS (∑ i ∈ s, G i))) (Finset.sum_insert ha),
      QDivisor.intersectionNumber_add' k sS C.ι C.dim_le (G a) (∑ i ∈ s, G i)
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _)
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _), Finset.sum_insert ha, ih]

/-- `(D · C) = ∑_E d_E (E · C)` for a divisor `D` on a `ℚ`-factorial variety. -/
private theorem intersectionNumber_toQDivisor_eq_sum (hS : MMP.Fourfold.IsQFactorial sS)
    (D : Divisor S) (C : ProperCurve sS) :
    (Divisor.toQDivisor D).intersectionNumber k sS C.ι C.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
      ∑ E ∈ D.support, (D E : ℚ) * (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber
        k sS C.ι C.dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  classical
  have hD : Divisor.toQDivisor D =
      ∑ E ∈ D.support, (D E : ℚ) • Divisor.toQDivisor (Finsupp.single E 1) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [show (Finsupp.single E (D E) : Divisor S) = (D E) • Finsupp.single E 1 by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
  rw [MMP.Fourfold.intersectionNumber_congr sS C.ι C.dim_le _
    (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) hD, intersectionNumber_finset_sum hS]
  refine Finset.sum_congr rfl fun E _ => ?_
  exact MMP.Fourfold.intersectionNumber_smul sS C.ι C.dim_le _
    (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) _ _

/-- A prime divisor lies in the pull-back of a closed point exactly when it maps to that point. -/
private theorem mem_support_iff_of_isPullback_single {T : Scheme.{u}} [IsLocallyNoetherian T]
    [IsNormal T] [CompactSpace T] (f : S ⟶ T) (P : MMP.Mori.PrimeDivisor T)
    (hc : IsClosed ({P.genericPoint} : Set T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    (E : MMP.Mori.PrimeDivisor S) : E ∈ F.support ↔ f E.genericPoint = P.genericPoint :=
  ⟨fun h => by
    by_contra hne
    exact (Finsupp.mem_support_iff.mp h)
      (MMP.Fourfold.coeff_eq_zero_of_isPullback_single f P hc hF E hne),
    fun h => Finsupp.mem_support_iff.mpr
      (MMP.Fourfold.coeff_pos_of_isPullback_single f P hF E h).ne'⟩

/-- **An irreducible fibre has a single component.** If the fibre over a closed point is
irreducible, any two prime divisors in the support of its pull-back are equal. -/
private theorem eq_of_mem_support_of_isIrreducible {T : Scheme.{u}} [IsLocallyNoetherian T]
    [IsNormal T] [CompactSpace T] (f : S ⟶ T) (P : MMP.Mori.PrimeDivisor T)
    (hc : IsClosed ({P.genericPoint} : Set T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    (hirr : IsIrreducible (f ⁻¹' {P.genericPoint})) {E E' : MMP.Mori.PrimeDivisor S}
    (hE : E ∈ F.support) (hE' : E' ∈ F.support) : E' = E := by
  classical
  have hcov : f ⁻¹' {P.genericPoint} ⊆ ⋃₀ ((F.support.image
      (fun G : MMP.Mori.PrimeDivisor S => (G.support : Set S)) : Finset (Set S)) :
        Set (Set S)) := by
    intro x hx
    obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp
      (MMP.Fourfold.mem_supp_of_isPullback_single f P hF (x := x) hx)
    exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨G, Finsupp.mem_support_iff.mpr hG, rfl⟩), hxG⟩
  obtain ⟨z, hz, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hirr _
    (fun z hz => by
      obtain ⟨G, -, rfl⟩ := Finset.mem_image.mp hz
      exact G.idealSheaf.support.isClosed) hcov
  obtain ⟨E₁, -, rfl⟩ := Finset.mem_image.mp hz
  have hall : ∀ G ∈ F.support, G = E₁ := fun G hG =>
    (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E₁ G
      (hsub ((mem_support_iff_of_isPullback_single f P hc hF G).mp hG))).symm
  rw [hall E' hE', hall E hE]

/-- A prime divisor `E` meeting trivially a proper curve whose generic point is that of another
prime divisor `E'` is disjoint from `E'`. -/
private theorem notMem_support_of_intersectionNumber_eq_zero (hS : MMP.Fourfold.IsQFactorial sS)
    {E E' : MMP.Mori.PrimeDivisor S} (hne : E ≠ E') (C : ProperCurve sS)
    (hC : C.point = E'.genericPoint)
    (hzero : (Divisor.toQDivisor (Finsupp.single E 1)).intersectionNumber k sS C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) = 0)
    {x : S} (hx : x ∈ E'.support) : x ∉ E.support := by
  classical
  intro hxE
  have h0 : 0 ≤ Divisor.toQDivisor (Finsupp.single E 1) := fun G => by
    rw [MMP.Threefold.Resolution.toQDivisor_single]
    change (0 : ℚ) ≤ (Finsupp.single E ((1 : ℤ) : ℚ)) G
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  have hpt : C.point ∉ (Divisor.toQDivisor (Finsupp.single E 1)).supp := by
    intro hmem
    obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    rw [MMP.Threefold.Resolution.toQDivisor_single] at hG
    have hGE : E = G := by
      by_contra hne'
      exact hG (by simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hne'])
    rw [← hGE, hC] at hxG
    exact hne (MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E E' hxG)
  have hiff := ((MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sS _
    (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) h0 C hpt).2).mp hzero
  refine hiff x ?_ (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, ?_, hxE⟩)
  · rw [hC]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact specializes_iff_mem_closure.mpr hx
  · rw [MMP.Threefold.Resolution.toQDivisor_single]
    simp [DivisorWithCoeffs.coeff_apply]

/-- **A connected fibre is numerically connected.** If the fibre `f^*P` over a closed point is
connected, every proper nonempty set `K` of its components contains some `E` meeting some
component `E'` outside `K` nontrivially. -/
private theorem exists_intersectionNumber_ne_zero_of_isPreconnected {T : Scheme.{u}}
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] (hS : MMP.Fourfold.IsQFactorial sS)
    (f : S ⟶ T) (P : MMP.Mori.PrimeDivisor T)
    (hfib : _root_.IsPreconnected (f ⁻¹' {P.genericPoint}))
    (hc : IsClosed ({P.genericPoint} : Set T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    (CE : MMP.Mori.PrimeDivisor S → ProperCurve sS) (hCE : ∀ E, (CE E).point = E.genericPoint)
    (K : Finset {E // E ∈ F.support}) (hK : K.Nonempty) (hKne : K ≠ Finset.univ) :
    ∃ E ∈ K, ∃ E' ∉ K, (Divisor.toQDivisor (Finsupp.single E.1 1)).intersectionNumber k sS
      (CE E'.1).ι (CE E'.1).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) ≠ 0 := by
  classical
  have hoverF := mem_support_iff_of_isPullback_single f P hc hF
  by_contra hcon
  push Not at hcon
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : {E // E ∈ F.support}, E₁ ∉ K := by
    by_contra h
    push Not at h
    exact hKne (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨E₂, hE₂⟩ := hK
  have hdisj : ∀ E ∈ K, ∀ E' ∉ K, ∀ x ∈ E'.1.support, x ∉ E.1.support := fun E hE E' hE' _ hx =>
    notMem_support_of_intersectionNumber_eq_zero hS (fun h => hE' (by rwa [← Subtype.ext h]))
      (CE E'.1) (hCE _) (hcon E hE E' hE') hx
  set T₀ : Set S := ⋃ E ∈ K, (E.1.support : Set S)
  set T₁ : Set S := ⋃ E ∈ Finset.univ.filter (· ∉ K), (E.1.support : Set S)
  have hT₀ : IsClosed T₀ := isClosed_biUnion_finset fun E _ => E.1.idealSheaf.support.isClosed
  have hT₁ : IsClosed T₁ := isClosed_biUnion_finset fun E _ => E.1.idealSheaf.support.isClosed
  have hgp : ∀ E : MMP.Mori.PrimeDivisor S, E.genericPoint ∈ (E.support : Set S) := fun E => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hcover : f ⁻¹' {P.genericPoint} ⊆ T₀ ∪ T₁ := by
    intro x hx
    obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp
      (MMP.Fourfold.mem_supp_of_isPullback_single f P hF hx)
    have hGι : G ∈ F.support := Finsupp.mem_support_iff.mpr hG
    by_cases hGK : (⟨G, hGι⟩ : {E // E ∈ F.support}) ∈ K
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨_, hGK, hxG⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGK⟩, hxG⟩)
  have hm₀ : (f ⁻¹' {P.genericPoint} ∩ T₀).Nonempty :=
    ⟨E₂.1.genericPoint, (hoverF E₂.1).mp E₂.2, Set.mem_iUnion₂.mpr ⟨E₂, hE₂, hgp _⟩⟩
  have hm₁ : (f ⁻¹' {P.genericPoint} ∩ T₁).Nonempty :=
    ⟨E₁.1.genericPoint, (hoverF E₁.1).mp E₁.2,
      Set.mem_iUnion₂.mpr ⟨E₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE₁⟩, hgp _⟩⟩
  obtain ⟨x, -, hx₀, hx₁⟩ := isPreconnected_closed_iff.mp hfib T₀ T₁ hT₀ hT₁ hcover hm₀ hm₁
  obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.mp hx₀
  obtain ⟨E', hE', hxE'⟩ := Set.mem_iUnion₂.mp hx₁
  exact hdisj E hE E' (Finset.mem_filter.mp hE').2 x hxE' hxE

/-- **Zariski's lemma for a fibre.** Let `F = f^*P` be the fibre over a closed point `P` of a
contraction `f : S ⟶ T` of a `ℚ`-factorial projective surface with connected fibres. The
intersection matrix of distinct components `Q_j` of `F` is negative definite as soon as some
component `E₀` of `F` is missing among them. -/
private theorem posDef_neg_of_fibre {T : Scheme.{u}} [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] (hS : MMP.Fourfold.IsQFactorial sS)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hSdim : topologicalKrullDim S = 2) (f : S ⟶ T)
    (hfib : ∀ y : T, _root_.IsPreconnected (f ⁻¹' {y})) (P : MMP.Mori.PrimeDivisor T)
    (hc : IsClosed ({P.genericPoint} : Set T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    {J : Type*} [Fintype J] [DecidableEq J] (Q : J → MMP.Mori.PrimeDivisor S)
    (hQ : Function.Injective Q) (C : J → ProperCurve sS)
    (hCQ : ∀ j, (C j).point = (Q j).genericPoint)
    (hover : ∀ j, f (Q j).genericPoint = P.genericPoint)
    (E₀ : MMP.Mori.PrimeDivisor S) (hE₀ : f E₀.genericPoint = P.genericPoint)
    (hE₀Q : ∀ j, Q j ≠ E₀) :
    (-(Matrix.of fun i j : J =>
      ((Divisor.toQDivisor (Finsupp.single (Q i) 1)).intersectionNumber k sS (C j).ι
        (C j).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℝ))).PosDef := by
  classical
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  have : IsIntegral S := hSv.toIsIntegral
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : IsProper sS := ((MMP.Mori.isProjectiveVariety_iff k sS).mp hSp).2.isProjective.isProper
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  choose CE hCE using fun E : MMP.Mori.PrimeDivisor S =>
    exists_properCurve_of_primeDivisor (sS := sS) hSdim E
  have hoverF := mem_support_iff_of_isPullback_single f P hc hF
  have hspec : ∀ {x z : S}, f x = P.genericPoint → x ⤳ z → f z = P.genericPoint := by
    intro x z hx hxz
    have h := hxz.map f.continuous
    rw [hx] at h
    exact h.mem_closed hc rfl
  set ι := {E // E ∈ F.support}
  set A : Matrix ι ι ℝ := Matrix.of fun E E' : ι =>
    ((Divisor.toQDivisor (Finsupp.single E.1 1)).intersectionNumber k sS (CE E'.1).ι
      (CE E'.1).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℝ)
  set n : ι → ℝ := fun E => ((F E.1 : ℤ) : ℝ)
  have hsymm : ∀ E E' : ι, A E E' = A E' E := fun E E' => by
    simp only [A, Matrix.of_apply]
    exact_mod_cast (intersectionNumber_single_comm hS hSp hSdim E'.1 E.1 (CE E'.1) (CE E.1)
      (hCE _) (hCE _))
  have hoff : ∀ E E' : ι, E ≠ E' → 0 ≤ A E E' := fun E E' h => by
    simp only [A, Matrix.of_apply]
    exact_mod_cast intersectionNumber_single_nonneg_of_ne hS E.1 E'.1
      (fun h' => h (Subtype.ext h')) (CE E'.1) (hCE _)
  have hn : ∀ E : ι, 0 < n E := fun E => by
    have := MMP.Fourfold.coeff_pos_of_isPullback_single f P hF E.1 ((hoverF E.1).mp E.2)
    rw [DivisorWithCoeffs.coeff_apply] at this
    show (0 : ℝ) < ((F E.1 : ℤ) : ℝ)
    exact_mod_cast this
  have hMn : ∀ E : ι, ∑ E', A E E' * n E' = 0 := by
    intro E
    have hγ : ∀ x : S, (CE E.1).point ⤳ x → f x = P.genericPoint := fun x hx =>
      hspec (by rw [hCE]; exact (hoverF E.1).mp E.2) hx
    have h0 := MMP.Fourfold.intersectionNumber_eq_zero_of_isPullback_single f sS hS P hF
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) (CE E.1) hγ
    rw [intersectionNumber_toQDivisor_eq_sum hS] at h0
    have h1 : ∑ E' : ι, A E E' * n E' = ((∑ E' ∈ F.support, (F E' : ℚ) *
        (Divisor.toQDivisor (Finsupp.single E' 1)).intersectionNumber k sS (CE E.1).ι
          (CE E.1).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℚ) : ℝ) := by
      rw [Rat.cast_sum, ← Finset.sum_coe_sort F.support]
      refine Finset.sum_congr rfl fun E' _ => ?_
      rw [hsymm]
      simp only [A, n, Matrix.of_apply]
      push_cast
      ring
    rw [h1, h0, Rat.cast_zero]
  have hconn : ∀ K : Finset ι, K.Nonempty → K ≠ Finset.univ →
      ∃ E ∈ K, ∃ E' ∉ K, A E E' ≠ 0 := fun K hK hKne => by
    obtain ⟨E, hE, E', hE', h⟩ :=
      exists_intersectionNumber_ne_zero_of_isPreconnected hS f P (hfib P.genericPoint) hc hF CE
        hCE K hK hKne
    exact ⟨E, hE, E', hE', Rat.cast_ne_zero.mpr h⟩
  set g : J → ι := fun j => ⟨Q j, (hoverF _).mpr (hover j)⟩
  have hg : Function.Injective g := fun i j h => hQ (congrArg Subtype.val h)
  have hE₀ι : (⟨E₀, (hoverF E₀).mpr hE₀⟩ : ι) ∉ Set.range g := by
    rintro ⟨j, hj⟩
    exact hE₀Q j (congrArg Subtype.val hj)
  have hM := posDef_neg_submatrix_of_connected A hsymm hoff n hn hMn hconn g hg _ hE₀ι
  have hCEQ : ∀ j, CE (Q j) = C j := fun j => ProperCurve.ext ((hCE _).trans (hCQ j).symm)
  convert hM using 2
  ext i j
  simp only [A, g, Matrix.of_apply, Matrix.submatrix_apply]
  rw [hCEQ]

end Fibre

/-! ### The fibre class -/

section FibreClass

open MMP.Mori

variable {k : Type u} [Field k] {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)}
  [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]

/-- **Exchange of intersection numbers.** On a `ℚ`-factorial projective surface, with a proper
curve `C_E` chosen for every prime divisor `E`, `∑_E b_E (A · C_E) = ∑_G a_G (B · C_G)`. -/
private theorem sum_mul_intersectionNumber_comm (hS : MMP.Fourfold.IsQFactorial sS)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hSdim : topologicalKrullDim S = 2)
    (CE : MMP.Mori.PrimeDivisor S → ProperCurve sS) (hCE : ∀ E, (CE E).point = E.genericPoint)
    (A B : Divisor S) :
    ∑ E ∈ B.support, (B E : ℚ) * (Divisor.toQDivisor A).intersectionNumber k sS (CE E).ι
        (CE E).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
      ∑ G ∈ A.support, (A G : ℚ) * (Divisor.toQDivisor B).intersectionNumber k sS (CE G).ι
        (CE G).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  calc _ = ∑ E ∈ B.support, ∑ G ∈ A.support, (B E : ℚ) * ((A G : ℚ) *
        (Divisor.toQDivisor (Finsupp.single G 1)).intersectionNumber k sS (CE E).ι (CE E).dim_le
          (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _)) :=
        Finset.sum_congr rfl fun E _ => by
          rw [intersectionNumber_toQDivisor_eq_sum hS A (CE E), Finset.mul_sum]
    _ = ∑ G ∈ A.support, ∑ E ∈ B.support, (B E : ℚ) * ((A G : ℚ) *
        (Divisor.toQDivisor (Finsupp.single G 1)).intersectionNumber k sS (CE E).ι (CE E).dim_le
          (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _)) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun G _ => by
        rw [intersectionNumber_toQDivisor_eq_sum hS B (CE G), Finset.mul_sum]
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [intersectionNumber_single_comm hS hSp hSdim E G (CE E) (CE G) (hCE E) (hCE G)]
        ring

/-- In an irreducible space of finite dimension, a closed irreducible subset of full dimension is
the whole space. -/
private theorem eq_univ_of_topologicalKrullDim_eq {X : Type*} [TopologicalSpace X]
    [IrreducibleSpace X] (Z : Set X) (hZ : IsClosed Z) (hZi : IsIrreducible Z) {d : ℕ}
    (hX : topologicalKrullDim X = d) (h : topologicalKrullDim Z = d) : Z = Set.univ := by
  by_contra hne
  let Zc : IrreducibleCloseds X := ⟨Z, hZi, hZ⟩
  let Tc : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt : Zc < Tc := lt_of_le_of_ne (fun _ _ => Set.mem_univ _)
    (fun h' => hne (congrArg (fun W : IrreducibleCloseds X => (W : Set X)) h'))
  have h1 : topologicalKrullDim Z ≤ Order.height Zc := by
    rw [Order.height_eq_krullDim_Iic]
    refine Order.krullDim_le_of_strictMono
      (fun W => ⟨IrreducibleCloseds.map (f := ((↑) : Z → X))
        Topology.IsInducing.subtypeVal.continuous W, ?_⟩) ?_
    · show closure (((↑) : Z → X) '' W) ⊆ Z
      exact closure_minimal (by rintro _ ⟨w, -, rfl⟩; exact w.2) hZ
    · intro a b hab
      exact IrreducibleCloseds.map_strictMono_of_isInducing Topology.IsInducing.subtypeVal hab
  have h2 : (Order.height Tc : WithBot ℕ∞) ≤ topologicalKrullDim X := Order.height_le_krullDim Tc
  have hZfin : Order.height Zc < ⊤ := by
    have := (Order.height_mono hlt.le).trans (WithBot.coe_le_coe.mp (h2.trans_eq hX))
    exact lt_of_le_of_lt this (WithTop.coe_lt_top _)
  have h3 := Order.height_strictMono hlt hZfin
  rw [h, ← WithBot.coe_natCast] at h1
  rw [hX, ← WithBot.coe_natCast] at h2
  exact lt_irrefl _
    ((WithBot.coe_le_coe.mp h1).trans_lt (h3.trans_le (WithBot.coe_le_coe.mp h2)))

/-- Intersection numbers along two closed immersions with the same ideal sheaf agree. -/
private theorem intersectionNumber_subschemeι_congr {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] {I J : X.IdealSheafData} (h : I = J)
    [IsProper (I.subschemeι ≫ sX)] [IsProper (J.subschemeι ≫ sX)]
    (hI : topologicalKrullDim I.subscheme ≤ 1) (hJ : topologicalKrullDim J.subscheme ≤ 1)
    (D : QDivisor X) (hD : D.IsQCartier) :
    D.intersectionNumber k sX I.subschemeι hI hD =
      D.intersectionNumber k sX J.subschemeι hJ hD := by
  subst h
  rfl

variable {T : Scheme.{u}} {sT : T ⟶ Spec (.of k)} [IsLocallyNoetherian T] [IsNormal T]
  [QuasiCompact sT]

/-- **The fibre divisor on a vertical curve.** A curve mapping to a point meets the pull-back of
a Cartier divisor trivially. -/
private theorem intersectionNumber_pullback_eq_zero_of_vertical
    (hS : MMP.Fourfold.IsQFactorial sS) (hSv : MMP.Mori.IsVariety k sS)
    (hTv : MMP.Mori.IsVariety k sT) (f : S ⟶ T) (hfs : f ≫ sT = sS)
    (P : MMP.Mori.PrimeDivisor T)
    (hPc : MMP.Mori.Divisor.IsCartier (Finsupp.single P 1 : Divisor T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    (C : ProperCurve sS) (hpt : ∃ w, Set.range (C.ι ≫ f) = {w}) :
    (Divisor.toQDivisor F).intersectionNumber k sS C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) = 0 := by
  haveI := hSv
  haveI := hTv
  haveI : MMP.Mori.IsCurve k (C.ι ≫ sS) := MMP.Threefold.Resolution.isCurve_ι_comp C
  have hBQ : ∀ Z : irreducibleComponents S, f (componentGenericPoint S Z) ∉
      (Divisor.toQDivisor (Finsupp.single P 1 : Divisor T)).supp := by
    rwa [Divisor.supp_toQDivisor]
  have h := QDivisor.isPullback_toQDivisor hPc hBQ hF
  exact MMP.Mori.intersectionNumber_pullback_eq_zero k sS sT f hfs C.ι
    (QDivisor.isQCartier_toQDivisor hPc) h hpt

/-- **The fibre divisor on a horizontal curve.** For a curve `C` dominating `T` there is `d`,
the degree `[k(C) : k(T)]`, with `(f^*P · C) = d · (P · T)` for every prime divisor `P` of `T`. -/
private theorem exists_intersectionNumber_pullback_eq_of_horizontal [IsIntegral T]
    (hS : MMP.Fourfold.IsQFactorial sS) (hSv : MMP.Mori.IsVariety k sS)
    (hTv : MMP.Mori.IsVariety k sT) (hTdim : topologicalKrullDim T = 1) (f : S ⟶ T)
    (hfs : f ≫ sT = sS) (C : ProperCurve sS) (hnc : ¬ ∃ w, Set.range (C.ι ≫ f) = {w})
    (CT : ProperCurve sT) (hCT : CT.point = genericPoint T) :
    ∃ d : ℚ, ∀ (P : MMP.Mori.PrimeDivisor T)
      (hPc : MMP.Mori.Divisor.IsCartier (Finsupp.single P 1 : Divisor T))
      {hB : ∀ Z : irreducibleComponents S,
        f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
      {F : Divisor S} (_hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F),
      (Divisor.toQDivisor F).intersectionNumber k sS C.ι C.dim_le
          (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
        d * (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sT CT.ι CT.dim_le
          (QDivisor.isQCartier_toQDivisor hPc) := by
  haveI := hSv
  haveI := hTv
  haveI : MMP.Mori.IsCurve k (C.ι ≫ sS) := MMP.Threefold.Resolution.isCurve_ι_comp C
  haveI : MMP.Mori.IsCurve k ((C.ι ≫ f) ≫ sT) := by
    rw [Category.assoc, hfs]
    infer_instance
  haveI : IsProper ((C.ι ≫ f) ≫ sT) := by
    rw [Category.assoc, hfs]
    infer_instance
  haveI : IsSeparated sT := hTv.toIsSeparated
  haveI : LocallyOfFiniteType sT := hTv.toLocallyOfFiniteType
  have hcurve := MMP.Mori.isCurve_imageι_comp sT (C.ι ≫ f) hnc
  haveI : IsIntegral (C.ι ≫ f).image :=
    @AlgebraicGeometry.IsVariety.toIsIntegral k _ _ _ hcurve.toIsVariety
  have hker : (C.ι ≫ f).ker = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({CT.point} : Set T)) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    congr 1
    apply Closeds.ext
    rw [Closeds.coe_closure, Closeds.coe_closure, hCT, (genericPoint_spec T).def]
    have hirr : IsIrreducible (closure (Set.range (C.ι ≫ f))) :=
      (show IsIrreducible (Set.range (C.ι ≫ f)) by
        rw [← Set.image_univ]
        exact (IrreducibleSpace.isIrreducible_univ _).image _
          (C.ι ≫ f).continuous.continuousOn).closure
    have hdim : topologicalKrullDim (closure (Set.range (C.ι ≫ f))) =
        ((1 : ℕ) : WithBot ℕ∞) := by
      have h1 := topologicalKrullDim_range_eq (C.ι ≫ f).imageι
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure] at h1
      rw [h1]
      exact hcurve.topologicalKrullDim_eq_one
    exact eq_univ_of_topologicalKrullDim_eq _ isClosed_closure hirr (by rw [hTdim]; rfl) hdim
  haveI : IsProper (C.ι ≫ f) := IsProper.of_comp (C.ι ≫ f) sT
  have hlft : LocallyOfFiniteType ((C.ι ≫ f).toImage ≫ (C.ι ≫ f).imageι) := by
    rw [Scheme.Hom.toImage_imageι]; infer_instance
  haveI : LocallyOfFiniteType (C.ι ≫ f).toImage := LocallyOfFiniteType.of_comp hlft
  haveI : IsProper ((C.ι ≫ f).imageι ≫ sT) := isProper_imageι_comp (C.ι ≫ f) sT
  refine ⟨(degreeOver (C.ι ≫ f).toImage : ℚ), fun P hPc hB F hF => ?_⟩
  have hBQ : ∀ Z : irreducibleComponents S, f (componentGenericPoint S Z) ∉
      (Divisor.toQDivisor (Finsupp.single P 1 : Divisor T)).supp := by
    rwa [Divisor.supp_toQDivisor]
  have h := QDivisor.isPullback_toQDivisor hPc hBQ hF
  rw [MMP.Mori.intersectionNumber_pullback_eq_degreeOver_mul k sS sT f hfs C.ι
    (QDivisor.isQCartier_toQDivisor hPc) h hcurve]
  congr 1
  exact intersectionNumber_subschemeι_congr hker _ _ _ _

/-- **Fibre divisors on an arbitrary curve.** For every proper curve `C` of `S` there is `d ∈ ℚ`
with `(f^*P · C) = d · (P · T)` for every prime divisor `P` of `T`: `d = 0` if `C` is vertical and
`d = [k(C) : k(T)]` otherwise. -/
private theorem exists_intersectionNumber_pullback_eq_mul [IsIntegral T]
    (hS : MMP.Fourfold.IsQFactorial sS) (hSv : MMP.Mori.IsVariety k sS)
    (hTv : MMP.Mori.IsVariety k sT) (hTdim : topologicalKrullDim T = 1) (f : S ⟶ T)
    (hfs : f ≫ sT = sS) (C : ProperCurve sS) (CT : ProperCurve sT)
    (hCT : CT.point = genericPoint T) :
    ∃ d : ℚ, ∀ (P : MMP.Mori.PrimeDivisor T)
      (hPc : MMP.Mori.Divisor.IsCartier (Finsupp.single P 1 : Divisor T))
      {hB : ∀ Z : irreducibleComponents S,
        f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
      {F : Divisor S} (_hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F),
      (Divisor.toQDivisor F).intersectionNumber k sS C.ι C.dim_le
          (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
        d * (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sT CT.ι CT.dim_le
          (QDivisor.isQCartier_toQDivisor hPc) := by
  by_cases hpt : ∃ w, Set.range (C.ι ≫ f) = {w}
  · refine ⟨0, fun P hPc hB F hF => ?_⟩
    rw [zero_mul]
    exact intersectionNumber_pullback_eq_zero_of_vertical hS hSv hTv f hfs P hPc hF C hpt
  · exact exists_intersectionNumber_pullback_eq_of_horizontal hS hSv hTv hTdim f hfs C hpt CT hCT

/-- **All fibres are numerically proportional.** For fibre divisors `F = f^*P`, `F' = f^*P'` and
every divisor `D`, `(P' · T) ∑_E F_E (D · C_E) = (P · T) ∑_E F'_E (D · C_E)`. -/
private theorem fibre_sum_relation [IsIntegral T]
    (hS : MMP.Fourfold.IsQFactorial sS) (hSp : MMP.Mori.IsProjectiveVariety k sS)
    (hSdim : topologicalKrullDim S = 2) (hTv : MMP.Mori.IsVariety k sT)
    (hTdim : topologicalKrullDim T = 1) (f : S ⟶ T) (hfs : f ≫ sT = sS)
    (CE : MMP.Mori.PrimeDivisor S → ProperCurve sS) (hCE : ∀ E, (CE E).point = E.genericPoint)
    (CT : ProperCurve sT) (hCT : CT.point = genericPoint T)
    (P P' : MMP.Mori.PrimeDivisor T)
    (hPc : MMP.Mori.Divisor.IsCartier (Finsupp.single P 1 : Divisor T))
    (hP'c : MMP.Mori.Divisor.IsCartier (Finsupp.single P' 1 : Divisor T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    {hB' : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P' 1 : Divisor T)}
    {F' : Divisor S} (hF' : Divisor.IsPullback f (Finsupp.single P' 1 : Divisor T) hB' F')
    (D : Divisor S) :
    (Divisor.toQDivisor (Finsupp.single P' 1)).intersectionNumber k sT CT.ι CT.dim_le
        (QDivisor.isQCartier_toQDivisor hP'c) *
      ∑ E ∈ F.support, (F E : ℚ) * (Divisor.toQDivisor D).intersectionNumber k sS (CE E).ι
        (CE E).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
    (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sT CT.ι CT.dim_le
        (QDivisor.isQCartier_toQDivisor hPc) *
      ∑ E ∈ F'.support, (F' E : ℚ) * (Divisor.toQDivisor D).intersectionNumber k sS (CE E).ι
        (CE E).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  choose d hd using fun G : MMP.Mori.PrimeDivisor S =>
    exists_intersectionNumber_pullback_eq_mul hS hSv hTv hTdim f hfs (CE G) CT hCT
  rw [sum_mul_intersectionNumber_comm hS hSp hSdim CE hCE D F,
    sum_mul_intersectionNumber_comm hS hSp hSdim CE hCE D F']
  simp only [fun G => hd G P hPc hF, fun G => hd G P' hP'c hF', Finset.mul_sum]
  refine Finset.sum_congr rfl fun G _ => ?_
  ring

end FibreClass

/-! ### Closed finite cones -/

section ClosedCone

open Set

/-- **A finite cone is closed.** In a Hausdorff real topological vector space, the cone spanned by
a finite set on which a continuous linear form is positive is closed: slicing by the form, it is
the union of `0` and the rays through a compact convex hull. -/
private theorem isClosed_hull_of_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] (G : Set V)
    (hG : G.Finite) (ℓ : V →ₗ[ℝ] ℝ) (hℓc : Continuous ℓ) (hℓ : ∀ g ∈ G, 0 < ℓ g) :
    IsClosed (PointedCone.hull ℝ G : Set V) := by
  classical
  set K : Set V := convexHull ℝ ((fun g => (ℓ g)⁻¹ • g) '' G) with hK
  have hKc : IsCompact K := (hG.image _).isCompact_convexHull ℝ
  have hKhull : K ⊆ (PointedCone.hull ℝ G : Set V) := by
    refine convexHull_min ?_ (PointedCone.hull ℝ G).convex
    rintro _ ⟨g, hg, rfl⟩
    have h1 : (ℓ g)⁻¹ • g =
        (⟨(ℓ g)⁻¹, (inv_pos.mpr (hℓ g hg)).le⟩ : {c : ℝ // 0 ≤ c}) • g := rfl
    show (ℓ g)⁻¹ • g ∈ _
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hg)
  have hKℓ : ∀ x ∈ K, ℓ x = 1 := by
    intro x hx
    have hconv : Convex ℝ (ℓ ⁻¹' {1} : Set V) := (convex_singleton (1 : ℝ)).linear_preimage ℓ
    refine (convexHull_min ?_ hconv) hx
    rintro _ ⟨g, hg, rfl⟩
    simp [map_smul, (hℓ g hg).ne']
  have hnn : ∀ v ∈ (PointedCone.hull ℝ G : Set V), 0 ≤ ℓ v := by
    intro v hv
    obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hv
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ => by
      rw [show c i • (g i : V) = (c i : ℝ) • (g i : V) from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg (c i).2 (hℓ _ (g i).2).le
  have hdecomp : ∀ v ∈ (PointedCone.hull ℝ G : Set V), v = 0 ∨ ∃ x ∈ K, v = ℓ v • x := by
    intro v hv
    obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.mp hv
    have hv' : ∑ i, c i • (g i : V) = ∑ i, (c i : ℝ) • (g i : V) := rfl
    rw [hv']
    set t := ∑ i, (c i : ℝ) * ℓ (g i) with ht
    have hℓv : ℓ (∑ i, (c i : ℝ) • (g i : V)) = t := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have hterm : ∀ i, 0 ≤ (c i : ℝ) * ℓ (g i) := fun i =>
      mul_nonneg (c i).2 (hℓ _ (g i).2).le
    rcases (Finset.sum_nonneg fun i _ => hterm i : 0 ≤ t).lt_or_eq with htpos | ht0
    · right
      refine ⟨t⁻¹ • ∑ i, (c i : ℝ) • (g i : V), ?_, ?_⟩
      · have e : t⁻¹ • ∑ i, (c i : ℝ) • (g i : V) =
            ∑ i, ((c i : ℝ) * ℓ (g i) / t) • ((ℓ (g i))⁻¹ • (g i : V)) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, smul_smul]
          congr 1
          have := (hℓ _ (g i).2).ne'
          field_simp
        rw [e]
        refine (convex_convexHull ℝ _).sum_mem (fun i _ => div_nonneg (hterm i) htpos.le) ?_
          fun i _ => subset_convexHull ℝ _ ⟨g i, (g i).2, rfl⟩
        rw [← Finset.sum_div, ← ht, div_self htpos.ne']
      · rw [hℓv, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
    · left
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).mp ht0.symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases mul_eq_zero.mp (hall i (Finset.mem_univ _)) with h | h
      · rw [show (c i : ℝ) = 0 from h, zero_smul]
      · exact absurd h (hℓ _ (g i).2).ne'
  refine closure_subset_iff_isClosed.mp fun z hz => ?_
  set M := ℓ z + 1
  set Img : Set V := (fun p : ℝ × V => p.1 • p.2) '' (Icc 0 M ×ˢ K)
  have hImg : IsClosed (Img ∪ {0}) :=
    ((isCompact_Icc.prod hKc).image (continuous_fst.smul continuous_snd)).isClosed.union
      isClosed_singleton
  set U : Set V := ℓ ⁻¹' Iio M
  have hU : IsOpen U := isOpen_Iio.preimage hℓc
  have hzU : z ∈ U := show ℓ z < M by simp [M]
  have hsub : U ∩ (PointedCone.hull ℝ G : Set V) ⊆ Img ∪ {0} := by
    rintro v ⟨hvU, hv⟩
    rcases hdecomp v hv with h0 | ⟨x, hx, hvx⟩
    · exact Or.inr h0
    · exact Or.inl ⟨(ℓ v, x), ⟨⟨hnn v hv, le_of_lt hvU⟩, hx⟩, hvx.symm⟩
  have hz' : z ∈ Img ∪ {0} :=
    hImg.closure_subset (closure_mono hsub (hU.inter_closure ⟨hzU, hz⟩))
  rcases hz' with ⟨⟨t, x⟩, ⟨⟨ht0, -⟩, hx⟩, rfl⟩ | h0
  · change t • x ∈ (PointedCone.hull ℝ G : Set V)
    have : t • x = (⟨t, ht0⟩ : {c : ℝ // 0 ≤ c}) • x := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (hKhull hx)
  · rw [show z = 0 from h0]; exact Submodule.zero_mem _

end ClosedCone

/-! ### Degrees of Cartier divisors and their Weil divisors -/

section WeilBridge

open MMP.Mori MMP.Intersection

variable {k : Type u} [Field k] {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)}

/-- `N₁(S/T)` is a topological additive group. -/
private theorem isTopologicalAddGroup_relative (f : S ⟶ T) :
    IsTopologicalAddGroup (RelativeNumericalCurveClasses sS f) :=
  topologicalAddGroup_iInf fun _ => topologicalAddGroup_iInf fun _ =>
    topologicalAddGroup_induced _

/-- Scalar multiplication on `N₁(S/T)` is jointly continuous. -/
private theorem continuousSMul_relative (f : S ⟶ T) :
    ContinuousSMul ℝ (RelativeNumericalCurveClasses sS f) :=
  continuousSMul_iInf fun _ => continuousSMul_iInf fun _ => continuousSMul_induced _

/-- `N₁(S/T)` is Hausdorff: the degree forms separate its points. -/
private theorem t2Space_relative (f : S ⟶ T) : T2Space (RelativeNumericalCurveClasses sS f) := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨Z, hZ⟩ := relativeNumericalClass_surjective sS f (x - y)
  have hL : ∃ (L : S.Modules) (_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L),
      RelativeNumericalCurveClasses.degree sS f L (x - y) ≠ 0 := by
    by_contra! h
    refine sub_ne_zero.mpr hxy ?_
    rw [← hZ]
    refine (Submodule.Quotient.mk_eq_zero _).mpr
      (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
    have := h L inferInstance
    rwa [← hZ] at this
  obtain ⟨L, _, hL⟩ := hL
  rw [map_sub, sub_ne_zero] at hL
  exact separated_by_continuous (RelativeNumericalCurveClasses.continuous_degree sS f L) hL

/-- Two classes in `N₁(S/T)` with the same degree against every invertible sheaf are equal. -/
private theorem eq_of_forall_degree_eq {f : S ⟶ T} {z₁ z₂ : RelativeNumericalCurveClasses sS f}
    (h : ∀ (L : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L],
      RelativeNumericalCurveClasses.degree sS f L z₁ =
        RelativeNumericalCurveClasses.degree sS f L z₂) : z₁ = z₂ := by
  obtain ⟨Z, hZ⟩ := relativeNumericalClass_surjective sS f (z₁ - z₂)
  refine sub_eq_zero.mp ?_
  rw [← hZ]
  refine (Submodule.Quotient.mk_eq_zero _).mpr
    (OneCycle.mem_numericallyTrivial.mpr fun L _ => ?_)
  have := congrArg (RelativeNumericalCurveClasses.degree sS f L) hZ
  rw [map_sub, h L, sub_self] at this
  exact this

/-- The degree of the class of a contracted curve. -/
private theorem degree_relativeClass {f : S ⟶ T} (L : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L] (C : ProperCurve sS)
    (hC : C.IsContractedBy f) :
    RelativeNumericalCurveClasses.degree sS f L (C.relativeClass f hC) = C.degree k L := by
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  exact OneCycle.degree_cycle ℝ L C

/-- The degree of the sheaf of a sum of Cartier divisors along a proper curve. -/
private theorem degree_sheaf_add (B B' : S.CartierDivisor) (C : ProperCurve sS) :
    C.degree k (MMP.CartierDivisor.sheaf (B + B')) =
      C.degree k (MMP.CartierDivisor.sheaf B) +
        C.degree k (MMP.CartierDivisor.sheaf B') := by
  haveI : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.toRingedSpace.presheaf,
        S.toRingedSpace.IsSheaf⟩).obj (MMP.CartierDivisor.sheaf B)).obj
          (MMP.CartierDivisor.sheaf B')) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible S.presheaf S.ringCatSheaf.2 _ _
  haveI h2 : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2
      ((MMP.CartierDivisor.sheaf B).tensorObj
        (MMP.CartierDivisor.sheaf B')) := this
  unfold ProperCurve.degree
  rw [← degreeOn_tensorSheaf k sS C.ι C.dim_le (hLM := this)]
  exact (degreeOn_eq_of_iso k sS C.ι C.dim_le
    (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm

/-- The degree along a proper curve, as an additive map on Cartier divisors. -/
private noncomputable def degreeSheafHom (C : ProperCurve sS) : S.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun B => C.degree k (MMP.CartierDivisor.sheaf B))
    fun B B' => degree_sheaf_add B B' C

private theorem degreeSheafHom_apply (C : ProperCurve sS) (B : S.CartierDivisor) :
    degreeSheafHom (k := k) C B = C.degree k (MMP.CartierDivisor.sheaf B) := rfl

/-- Linearly equivalent Cartier divisors have the same degree along a proper curve. -/
private theorem degree_sheaf_eq_of_linearlyEquivalent {B B' : S.CartierDivisor}
    (h : MMP.Intersection.LinearlyEquivalent B B') (C : ProperCurve sS) :
    C.degree k (MMP.CartierDivisor.sheaf B) =
      C.degree k (MMP.CartierDivisor.sheaf B') := by
  obtain ⟨c, hc⟩ := (MMP.Intersection.mem_principalSubgroup_iff).1 h
  have hB : B = B' + MMP.Intersection.principalDivisor c := by rw [hc]; abel
  subst hB
  exact degreeOn_eq_of_iso k sS C.ι C.dim_le ((MMP.CartierDivisor.sheafAddPrincipalIso B' c).symm ≪≫
      Iso.refl (MMP.CartierDivisor.sheaf B'))

/-- A point of height zero lies in the support of no Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero [IsIntegral S]
    [IsLocallyNoetherian S] (A : S.CartierDivisor) {x : S} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (S.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (S.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier [IsIntegral S] [IsLocallyNoetherian S]
    [TopologicalSpace.NoetherianSpace S] (A : S.CartierDivisor) :
    ∃ w : Divisor S, IsWeilDivisorOfCartier A w := by
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

variable [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS]

/-- The degree of `𝒪_S(A)` along a curve is the degree of the Weil divisor of `A`. -/
private theorem degree_sheaf_eq_degreeOn {A : S.CartierDivisor} {w : Divisor S}
    (hw : IsWeilDivisorOfCartier A w) (C : ProperCurve sS) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sS
    C.degree k (MMP.CartierDivisor.sheaf A) =
      w.degreeOn k sS C.ι C.dim_le hw.isCartier := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  haveI := hw.isCartier.isInvertibleModule_divisorialSheaf
  exact degreeOn_eq_of_iso k sS C.ι C.dim_le hw.nonempty_sheaf_iso_divisorialSheaf.some

/-- On a `ℚ`-factorial variety the intersection number of a Cartier divisor is its degree. -/
private theorem intersectionNumber_toQDivisor_eq_degreeOn (hS : MMP.Fourfold.IsQFactorial sS)
    (D : Divisor S) (hD : D.IsCartier) (C : ProperCurve sS) :
    (Divisor.toQDivisor D).intersectionNumber k sS C.ι C.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) =
      (D.degreeOn k sS C.ι C.dim_le hD : ℚ) := by
  rw [QDivisor.intersectionNumber_eq_of_smul k sS C.ι C.dim_le _ _ one_pos D hD (by simp)]
  simp

/-- On a `ℚ`-factorial variety the degree of an invertible sheaf `L ≅ 𝒪_S(A)` along a curve is
the intersection number of the Weil divisor of `A`. -/
private theorem degree_eq_intersectionNumber_of_iso (hS : MMP.Fourfold.IsQFactorial sS)
    {L : S.Modules} [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 L]
    {A : S.CartierDivisor} (e : L ≅ MMP.CartierDivisor.sheaf A) {w : Divisor S}
    (hw : IsWeilDivisorOfCartier A w) (C : ProperCurve sS) :
    (C.degree k L : ℝ) = (((Divisor.toQDivisor w).intersectionNumber k sS C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℚ) : ℝ) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sS
  rw [intersectionNumber_toQDivisor_eq_degreeOn hS w hw.isCartier,
    ← degree_sheaf_eq_degreeOn hw]
  have : C.degree k L = C.degree k (MMP.CartierDivisor.sheaf A) :=
    degreeOn_eq_of_iso k sS C.ι C.dim_le e
  rw [this]
  push_cast
  rfl

end WeilBridge

section RealIntersection

open MMP.Mori

variable {k : Type u} [Field k] {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)}

/-- `(C · D) = ∑_B c_B deg_C 𝒪(B)` for a `ℚ`-Cartier divisor `D = ∑ c_B B`. -/
private theorem cycle_intersectionNumber_toReal (C : ProperCurve sS) (c : KCartierDivisor ℚ S) :
    (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal c) =
      ∑ B ∈ c.support, (c B : ℝ) * C.degree k (MMP.CartierDivisor.sheaf B) := by
  rw [OneCycle.intersectionNumber_eq_sum]
  simp only [MMP.Fourfold.KCartierDivisor.toReal, Finsupp.mapRange.addMonoidHom_apply]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp [ProperCurve.cycle, Finsupp.sum]

/-- The degree of the realization of an integral `ℚ`-Cartier divisor. -/
private theorem degree_sheaf_realization (C : ProperCurve sS) (c : KCartierDivisor ℚ S)
    (h : ∀ D, ∃ n : ℤ, c D = n) :
    ((C.degree k (MMP.CartierDivisor.sheaf
        (MMP.Mori.KCartierDivisor.realization c h)) : ℤ) : ℝ) =
      (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal c) := by
  rw [cycle_intersectionNumber_toReal, ← degreeSheafHom_apply,
    MMP.Mori.KCartierDivisor.realization, Finsupp.sum, map_sum]
  simp only [map_zsmul, degreeSheafHom_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun D _ => ?_
  congr 1
  have := Classical.choose_spec (h D)
  exact_mod_cast (congrArg (fun q : ℚ => (q : ℝ)) this).symm

end RealIntersection

/-! ### The generic fibre over a curve -/

section GenericFibre

open Polynomial

/-- **Integral rational functions descend along `g_* 𝒪_X = 𝒪_Y`.** Let `g : X ⟶ Y` with `X`
normal and integral and `g_* 𝒪_X = 𝒪_Y`. A rational function on `X` which is a root of a monic
polynomial with coefficients in `Γ(Y, V)` is the pull-back of a section over `V`. -/
private theorem exists_app_eq_of_isIntegral {X Y : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (g : X ⟶ Y) (hiso : ∀ V : Y.Opens, IsIso (g.app V)) (V : Y.Opens) [Nonempty (g ⁻¹ᵁ V)]
    (z : X.functionField) (q : Γ(Y, V)[X]) (hq : q.Monic)
    (hqz : (q.map (g.app V ≫ X.germToFunctionField (g ⁻¹ᵁ V)).hom).eval z = 0) :
    ∃ s : Γ(Y, V), X.germToFunctionField (g ⁻¹ᵁ V) (g.app V s) = z := by
  have hloc : ∀ x : (g ⁻¹ᵁ V : X.Opens), ∃ a : X.presheaf.stalk x.1,
      algebraMap (X.presheaf.stalk x.1) X.functionField a = z := by
    intro x
    haveI := IsNormal.stalk_normal (X := X) x.1
    have hint : IsIntegral (X.presheaf.stalk x.1) z := by
      refine ⟨q.map ((g.app V ≫ X.presheaf.germ (g ⁻¹ᵁ V) x.1 x.2).hom), hq.map _, ?_⟩
      have hφ : (algebraMap (X.presheaf.stalk x.1) X.functionField).comp
          (g.app V ≫ X.presheaf.germ (g ⁻¹ᵁ V) x.1 x.2).hom =
          (g.app V ≫ X.germToFunctionField (g ⁻¹ᵁ V)).hom := RingHom.ext fun s => by
        rw [RingHom.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply,
          X.algebraMap_germ_eq_germToFunctionField]
      rw [eval₂_eq_eval_map, Polynomial.map_map, hφ]
      exact hqz
    exact IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_forall_mem_range X (g ⁻¹ᵁ V) z hloc
  refine ⟨inv (g.app V) t, ?_⟩
  rw [← ht]
  congr 1
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]

/-- **The base field is separably closed in the function field.** For `g : X ⟶ Y` with `X`
normal and integral and `g_* 𝒪_X = 𝒪_Y`, the residue field of `Y` at the image of the generic
point of `X` is separably closed in the function field of `X`. -/
private theorem separableClosure_residueField_eq_bot {X Y : Scheme.{u}} [IsIntegral X]
    [IsNormal X] (g : X ⟶ Y) (hiso : ∀ V : Y.Opens, IsIso (g.app V)) {y : Y}
    (hy : g (genericPoint X) = y) :
    letI := residueFieldAlgebraOfEq g hy
    separableClosure (Y.residueField y) (X.residueField (genericPoint X)) = ⊥ := by
  subst hy
  letI := residueFieldAlgebraOfEq g (rfl : g (genericPoint X) = g (genericPoint X))
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have hres : Function.Bijective (X.residue (genericPoint X)).hom :=
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective (genericPoint X)⟩
  let e : X.functionField ≃+* X.residueField (genericPoint X) :=
    RingEquiv.ofBijective (X.residue (genericPoint X)).hom hres
  have he : ∀ a : X.functionField, e a = (X.residue (genericPoint X)).hom a := fun _ => rfl
  refine eq_bot_iff.mpr fun z hz => ?_
  rw [IntermediateField.mem_bot]
  obtain ⟨p, hpm, hpz⟩ := (mem_separableClosure_iff.mp hz).isIntegral
  -- lift the coefficients to a neighbourhood of `g (genericPoint X)`
  choose Vn hVn sn hsn using fun n : ℕ =>
    Y.presheaf.germ_exist (Y.residue_surjective (g (genericPoint X)) (p.coeff n)).choose
  set d := p.natDegree
  set V : Y.Opens := (Finset.range (d + 1)).inf Vn
  have hyV : g (genericPoint X) ∈ V := by
    have : ∀ t : Finset ℕ, g (genericPoint X) ∈ t.inf Vn := by
      intro t
      induction t using Finset.induction_on with
      | empty => trivial
      | insert a t ha ih => rw [Finset.inf_insert]; exact ⟨hVn a, ih⟩
    exact this _
  have hVle : ∀ n ∈ Finset.range (d + 1), V ≤ Vn n := fun n hn => Finset.inf_le hn
  set ρ : Γ(Y, V) →+* Y.residueField (g (genericPoint X)) :=
    (Y.presheaf.germ V (g (genericPoint X)) hyV ≫ Y.residue (g (genericPoint X))).hom
  have hlifts : p ∈ Polynomial.lifts ρ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ Finset.range (d + 1)
    · refine ⟨Y.presheaf.map (homOfLE (hVle n hn)).op (sn n), ?_⟩
      change (Y.residue (g (genericPoint X))).hom (Y.presheaf.germ V (g (genericPoint X)) hyV
        (Y.presheaf.map (homOfLE (hVle n hn)).op (sn n))) = _
      rw [Y.presheaf.germ_res_apply, hsn n]
      exact (Y.residue_surjective (g (genericPoint X)) (p.coeff n)).choose_spec
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt]
      simp only [Finset.mem_range, not_lt] at hn
      omega
  obtain ⟨q, hqp, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hpm
  haveI : Nonempty (g ⁻¹ᵁ V) := ⟨⟨(genericPoint X), hyV⟩⟩
  -- the comparison of the two routes from `Γ(Y, V)` to the residue field of `X`
  have hcomp : ∀ s : Γ(Y, V), e (X.germToFunctionField (g ⁻¹ᵁ V) (g.app V s)) =
      algebraMap (Y.residueField (g (genericPoint X))) (X.residueField (genericPoint X)) (ρ s) := by
    intro s
    rw [he]
    change (X.residue (genericPoint X)).hom
        (X.presheaf.germ (g ⁻¹ᵁ V) (genericPoint X) hyV (g.app V s)) =
      (g.residueFieldMap (genericPoint X)).hom
        ((Y.residue (g (genericPoint X))).hom (Y.presheaf.germ V (g (genericPoint X)) hyV s))
    rw [← Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Scheme.residue_residueFieldMap]
    rfl
  have hqz : (q.map (g.app V ≫ X.germToFunctionField (g ⁻¹ᵁ V)).hom).eval (e.symm z) = 0 := by
    apply e.injective
    have : (e.toRingHom.comp (g.app V ≫ X.germToFunctionField (g ⁻¹ᵁ V)).hom) =
        (algebraMap (Y.residueField (g (genericPoint X)))
          (X.residueField (genericPoint X))).comp ρ :=
      RingHom.ext hcomp
    rw [map_zero, Polynomial.eval_map]
    rw [show e (eval₂ (g.app V ≫ X.germToFunctionField (g ⁻¹ᵁ V)).hom (e.symm z) q) =
        eval₂ (e.toRingHom.comp (g.app V ≫ X.germToFunctionField (g ⁻¹ᵁ V)).hom)
          (e (e.symm z)) q from Polynomial.hom_eval₂ q _ e.toRingHom _]
    rw [this, e.apply_symm_apply, ← Polynomial.eval₂_map, hqp]
    exact hpz
  obtain ⟨s, hs⟩ := exists_app_eq_of_isIntegral g hiso V (e.symm z) q hqm hqz
  refine ⟨ρ s, ?_⟩
  rw [← hcomp, hs, e.apply_symm_apply]

/-- The preimage of a point of an open `U ⊆ Y` under the restriction `φ ∣_ U` is its preimage
under `φ`. -/
private theorem image_ι_preimage_restrict {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens)
    (p : (U : Scheme.{u})) : (φ ⁻¹ᵁ U).ι '' ((φ ∣_ U) ⁻¹' {p}) = φ ⁻¹' {U.ι p} := by
  have key : ∀ x' : ((φ ⁻¹ᵁ U : X.Opens) : Scheme.{u}),
      U.ι ((φ ∣_ U) x') = φ ((φ ⁻¹ᵁ U).ι x') := fun x' => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  ext x
  constructor
  · rintro ⟨x', hx', rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx' ⊢
    rw [← key, hx']
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    have hxU : x ∈ φ ⁻¹ᵁ U := by
      have : U.ι p ∈ (U : Set Y) := by rw [← Scheme.Opens.range_ι]; exact ⟨p, rfl⟩
      show φ x ∈ U
      rwa [hx]
    let x' : ((φ ⁻¹ᵁ U : X.Opens) : Scheme.{u}) := ⟨x, hxU⟩
    have hx' : (φ ⁻¹ᵁ U).ι x' = x := rfl
    refine ⟨x', ?_, hx'⟩
    refine U.ι.isOpenEmbedding.injective ?_
    rw [key x', hx', hx]

/-- Over an open on which a restriction is geometrically irreducible, the fibres are
irreducible. -/
private theorem isIrreducible_preimage_of_geometricallyIrreducible {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (U : Y.Opens) [GeometricallyIrreducible (φ ∣_ U)] (p : (U : Scheme.{u})) :
    IsIrreducible (φ ⁻¹' {U.ι p}) := by
  rw [← image_ι_preimage_restrict, ← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ _).image _
    ((φ ∣_ U).fiberι p).continuous.continuousOn).image _ (φ ⁻¹ᵁ U).ι.continuous.continuousOn

/-- **Irreducible fibres over a dense open.** Let `f : S ⟶ T` be a surjective morphism of finite
type, with `S` normal and integral, `T` integral and `f_* 𝒪_S = 𝒪_T`. Then the fibres of `f`
over the points of a nonempty open subset of `T` are irreducible. -/
private theorem exists_isOpen_isIrreducible_preimage {S T : Scheme.{u}} [IsIntegral S]
    [IsNormal S] [IsIntegral T] (f : S ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (hiso : ∀ V : T.Opens, IsIso (f.app V)) (hsurj : Function.Surjective f) :
    ∃ W : Set T, IsOpen W ∧ W.Nonempty ∧ ∀ t ∈ W, IsIrreducible (f ⁻¹' {t}) := by
  obtain ⟨V₀, hV₀, hηV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint T) trivial
  haveI : IsAffine V₀ := hV₀
  haveI : Nonempty V₀ := ⟨⟨_, hηV⟩⟩
  obtain ⟨x₀, hx₀⟩ := hsurj (genericPoint T)
  haveI : Nonempty (f ⁻¹ᵁ V₀) := ⟨⟨x₀, show f x₀ ∈ V₀ from hx₀ ▸ hηV⟩⟩
  set g := f ∣_ V₀ with hgdef
  have hgiso : ∀ W : V₀.toScheme.Opens, IsIso (g.app W) := by
    intro W
    rw [hgdef, morphismRestrict_app]
    have h1 := hiso (V₀.ι ''ᵁ W)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1
      (S.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f V₀ W)).op).isIso_hom
  have hgsurj : Function.Surjective g := by
    intro v
    obtain ⟨x, hx⟩ := hsurj (V₀.ι v)
    have hxU : x ∈ f ⁻¹ᵁ V₀ := by
      have : V₀.ι v ∈ (V₀ : Set T) := by rw [← Scheme.Opens.range_ι]; exact ⟨v, rfl⟩
      show f x ∈ V₀
      rwa [hx]
    let x' : ((f ⁻¹ᵁ V₀ : S.Opens) : Scheme.{u}) := ⟨x, hxU⟩
    refine ⟨x', V₀.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hgdef, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact hx
  have hgen : g (genericPoint (f ⁻¹ᵁ V₀)) = genericPoint V₀ :=
    g.base_genericPoint_eq_of_denseRange hgsurj.denseRange (genericPoint_spec V₀)
  have hcompiso : ∀ W, IsIso ((g ≫ V₀.toScheme.isoSpec.hom).app W) := by
    intro W
    rw [Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Scheme.Hom.instIsIsoCommRingCatApp _ W) (hgiso _)
  letI := residueFieldAlgebraOfEq (g ≫ V₀.toScheme.isoSpec.hom)
    (comp_isoSpec_genericPoint_eq g hgen)
  have hsep := separableClosure_residueField_eq_bot (g ≫ V₀.toScheme.isoSpec.hom) hcompiso
    (comp_isoSpec_genericPoint_eq g hgen)
  have hgi : GeometricallyIrreducible (g.fiberToSpecResidueField (genericPoint V₀)) :=
    (geometricallyIrreducible_fiber_genericPoint_iff_residueField_of_isAffine g hgen).mpr
      ((separableClosure.eq_bot_iff_geometricallyIrreducible _ _).mp hsep)
  obtain ⟨W, hWne, hW⟩ := geometricallyIrreducibleAfterShrinking g inferInstance inferInstance
    inferInstance _ (genericPoint_spec V₀) hgi
  refine ⟨V₀.ι '' (W : Set V₀), V₀.ι.isOpenEmbedding.isOpenMap _ W.isOpen, ?_, ?_⟩
  · obtain ⟨w⟩ := hWne
    exact ⟨_, w.1, w.2, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [← image_ι_preimage_restrict f V₀ w]
    have h := isIrreducible_preimage_of_geometricallyIrreducible g W ⟨w, hw⟩
    exact h.image _ (f ⁻¹ᵁ V₀).ι.continuous.continuousOn

/-- On an integral scheme of dimension one, every point other than the generic point is closed. -/
private theorem isClosed_singleton_of_ne_genericPoint {T : Scheme.{u}} [IsIntegral T]
    (hT : topologicalKrullDim T = 1) {z : T} (hz : z ≠ genericPoint T) :
    IsClosed ({z} : Set T) := by
  have h1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hT hz
  refine closure_subset_iff_isClosed.mp fun w hw => ?_
  by_contra hne
  have hsp : z ⤳ w := specializes_iff_mem_closure.mpr hw
  have hlt : w < z := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun h =>
    hne (Set.mem_singleton_iff.mpr (hsp.antisymm (Scheme.le_iff_specializes.mp h)).symm.eq)
  have h2 := Order.coheight_strictAnti hlt (by rw [h1]; exact ENat.coe_lt_top 1)
  rw [h1] at h2
  have hle := Stacks.AlgebraicGeometry.AmpleDimensionOne.coheight_le_one T hT w
  have hle' : Order.coheight w ≤ 1 := by exact_mod_cast hle
  exact absurd (h2.trans_le hle') (lt_irrefl _)

/-- On a Noetherian integral scheme of dimension one, a nonempty open set has finite complement. -/
private theorem finite_compl_of_isOpen {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : topologicalKrullDim T = 1) {W : Set T} (hW : IsOpen W)
    (hne : W.Nonempty) : Wᶜ.Finite := by
  haveI : IsNoetherian T := ⟨⟩
  have hη : genericPoint T ∈ W :=
    ((genericPoint_spec T).mem_open_set_iff hW).mpr (by simpa using hne)
  obtain ⟨Sset, hSf, hSc, hSi, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hW.isClosed_compl
  rw [hSeq]
  refine hSf.sUnion fun t ht => ?_
  have hg := (hSi t ht).isGenericPoint_genericPoint (hSc t ht)
  have hzt : (hSi t ht).genericPoint ∈ t := hg.mem
  have hzW : (hSi t ht).genericPoint ∈ Wᶜ := by
    rw [hSeq]
    exact ⟨t, ht, hzt⟩
  have hz : (hSi t ht).genericPoint ≠ genericPoint T := fun h => hzW (h ▸ hη)
  have hclosed := isClosed_singleton_of_ne_genericPoint hT hz
  rw [← hg.def, hclosed.closure_eq]
  exact Set.finite_singleton _

end GenericFibre

/-! ### The two cases -/

section Cases

open MMP.Mori

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS] [IrreducibleSpace S]

/-- **The birational case.** If `dim T = 2`, then `NE̅(S/T)` is spanned by finitely many
contracted curves, and the intersection matrix of any finite family of distinct contracted
curves is negative definite. -/
private theorem cone_and_posDef_of_dim_two
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hTp : MMP.Mori.IsProjectiveVariety k sT)
    (hS : MMP.Fourfold.IsQFactorial sS)
    (hSdim : topologicalKrullDim S = 2) (hTdim : topologicalKrullDim T = 2) :
    (∃ s : Finset {C : ProperCurve sS // C.IsContractedBy f},
      relativeClosedConeOfCurves sS f =
        PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
          C.1.relativeClass f C.2) '' (s : Set _))) ∧
    ∀ (r : ℕ) (C : Fin r → ProperCurve sS) (_hC : ∀ i, (C i).IsContractedBy f)
      (P : Fin r → MMP.Mori.PrimeDivisor S),
      Function.Injective C → (∀ i, (C i).point = (P i).genericPoint) →
      (-(Matrix.of fun i j : Fin r =>
        ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sS (C j).ι
          (C j).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℝ))).PosDef := by
  classical
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  have : IsIntegral S := hSv.toIsIntegral
  have hT := hf.isNormalVariety_target
  have : IsIntegral T := hT.1.toIsIntegral
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have hproj := hf.isProjectiveMorphism
  have : IsProper f := hproj.isProjective.isProper
  have hSq : IsQuasiProjectiveVariety k sS :=
    @IsProjectiveVariety.isQuasiProjectiveVariety k _ S sS hSp
  have hTq : IsQuasiProjectiveVariety k sT :=
    @IsProjectiveVariety.isQuasiProjectiveVariety k _ T sT hTp
  have hgb : IsBirationalMorphism f :=
    hf.isBirationalMorphism_of_topologicalKrullDim_eq (hSdim.trans hTdim.symm)
  obtain ⟨hfin, hcone, -, -⟩ := relativeClosedConeOfCurves_eq_hull_of_isBirationalMorphism hS hT
    hSq hTq hSdim hTdim f hf.comp_eq hproj.isProjective hgb
  refine ⟨?_, fun r C hC P hCinj hCP => ?_⟩
  · have : Finite {C : ProperCurve sS // C.IsContractedBy f} := hfin.to_subtype
    letI := Fintype.ofFinite {C : ProperCurve sS // C.IsContractedBy f}
    refine ⟨Finset.univ, ?_⟩
    rw [hcone, Finset.coe_univ, Set.image_univ]
  -- an effective Cartier `W` with `-W` relatively ample
  have hgf := MMP.Threefold.Resolution.exists_isFinite_morphismRestrict_of_isBirationalMorphism hgb
  obtain ⟨W, hW0, hWc, hWamp⟩ :=
    MMP.Threefold.Resolution.exists_isCartier_isRelativelyAmple_neg_of_isProjectiveMorphism hSv
      hT.1 (Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine
        Stacks.VeryAmplePowersUniformDegree.immersionTwistGapUniform sT hTq.isQuasiProjective)
      hproj hgf
  have hWneg : ∀ C : ProperCurve sS, C.IsContractedBy f →
      W.degreeOn k sS C.ι C.dim_le hWc < 0 := by
    intro C hC
    have := hWc.neg.isInvertibleModule_divisorialSheaf
    have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _
      hWamp C hC
    change 0 < (-W).degreeOn k sS C.ι C.dim_le hWc.neg at hpos
    linarith [Divisor.degreeOn_neg' k sS C.ι C.dim_le W hWc]
  have hPinj : Function.Injective P := fun i j h =>
    hCinj (ProperCurve.ext ((hCP i).trans ((congrArg _ h).trans (hCP j).symm)))
  obtain ⟨N, hN, hDc⟩ := exists_pos_isCartier_smul_single hS P
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  refine MMP.MatrixPosDef.posDef_neg_of_offDiag_nonneg_of_sum_mul_neg _ (fun i j => ?_)
    (fun i j hij => ?_)
    (fun i => (W (P i) : ℝ)) (fun i => by exact_mod_cast hW0 (P i)) fun j => ?_
  · simp only [Matrix.of_apply]
    exact_mod_cast intersectionNumber_single_comm hS hSp hSdim (P j) (P i) (C j) (C i)
      (hCP j) (hCP i)
  · simp only [Matrix.of_apply]
    exact_mod_cast intersectionNumber_single_nonneg_of_ne hS (P i) (P j) (hPinj.ne hij) (C j)
      (hCP j)
  · have key := sum_mul_degreeOn_neg hPinj hN hDc hW0 hWc (C j) j (hCP j) (hWneg _ (hC j))
    simp only [Matrix.of_apply]
    rw [Finset.sum_congr rfl fun i _ => by
      rw [intersectionNumber_single_eq_div hS (P i) hN (hDc i) (C j)]]
    have key' : (∑ i, (W (P i) : ℚ) * ((((N : ℤ) • Finsupp.single (P i) 1 : Divisor S).degreeOn
        k sS (C j).ι (C j).dim_le (hDc i) : ℚ) / N)) < 0 := by
      have e : (∑ i, (W (P i) : ℚ) * ((((N : ℤ) • Finsupp.single (P i) 1 : Divisor S).degreeOn
          k sS (C j).ι (C j).dim_le (hDc i) : ℚ) / N)) =
          (∑ i, ((W (P i) * ((N : ℤ) • Finsupp.single (P i) 1 : Divisor S).degreeOn
          k sS (C j).ι (C j).dim_le (hDc i) : ℤ) : ℚ)) / N := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast; ring
      rw [e]
      exact div_neg_of_neg_of_pos (by exact_mod_cast key) hNq
    exact_mod_cast key'

/-- A curve whose generic point maps to a closed point is contracted. -/
private theorem isContractedBy_of_isClosed {T' : Scheme.{u}} (g : S ⟶ T') (C : ProperCurve sS)
    (hC : IsClosed ({g C.point} : Set T')) : C.IsContractedBy g := by
  intro x hx
  have h := (specializes_iff_mem_closure.mpr hx).map g.continuous
  exact (h.mem_closed hC rfl).symm ▸ rfl

/-- The image of a contracted curve is a point. -/
private theorem range_ι_comp_eq_singleton {T' : Scheme.{u}} (g : S ⟶ T') (C : ProperCurve sS)
    (hC : C.IsContractedBy g) : Set.range (C.ι ≫ g) = {g C.point} := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    have hc : C.ι c ∈ closure ({C.point} : Set S) := by rw [← C.range_ι]; exact ⟨c, rfl⟩
    exact hC _ hc
  · rintro rfl
    obtain ⟨c, hc⟩ : C.point ∈ Set.range C.ι := by rw [C.range_ι]; exact subset_closure rfl
    exact ⟨c, by simp [hc]⟩

/-- Under a closed map, the image of a contracted curve is a closed point. -/
private theorem isClosed_singleton_of_isContractedBy {T' : Scheme.{u}} (g : S ⟶ T')
    (hg : IsClosedMap g) (C : ProperCurve sS) (hC : C.IsContractedBy g) :
    IsClosed ({g C.point} : Set T') := by
  have h1 : g '' closure ({C.point} : Set S) = {g C.point} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨C.point, subset_closure rfl, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx
  rw [← h1]
  exact hg _ isClosed_closure

/-- A surjective morphism from an irreducible scheme to an integral one maps the generic point to
the generic point. -/
private theorem map_componentGenericPoint_eq_genericPoint [IsIntegral T] (f : S ⟶ T)
    (hf : Function.Surjective f) (Z : irreducibleComponents S) :
    f (componentGenericPoint S Z) = genericPoint T := by
  have hZ : Z.1 = Set.univ := by
    have h : Z.1 ∈ ({Set.univ} : Set (Set S)) :=
      (irreducibleComponents_eq_singleton (X := S)) ▸ Z.2
    exact h
  have hgp := isGenericPoint_componentGenericPoint S Z
  rw [hZ] at hgp
  refine IsGenericPoint.eq ?_ (genericPoint_spec T)
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ closure {componentGenericPoint S Z} := by
    rw [hgp.def]
    trivial
  have := image_closure_subset_closure_image f.continuous ⟨x, hx, rfl⟩
  rwa [Set.image_singleton] at this

/-- **Kodaira's lemma, numerically.** An `f`-big `ℚ`-Cartier divisor `L` has a positive multiple
`N L` whose degree on every proper curve is `deg 𝒪(A) + deg 𝒪(E)`, with `A` an `f`-ample and `E`
an effective Cartier divisor. -/
private theorem exists_degree_eq_ample_add_effective
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hTp : MMP.Mori.IsProjectiveVariety k sT)
    (L : KCartierDivisor ℚ S) (hLbig : MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ f L) :
    ∃ N : ℕ, 0 < N ∧ ∃ A E : S.CartierDivisor,
      IsRelativelyAmple f (MMP.CartierDivisor.sheaf A) ∧
      MMP.Intersection.IsEffective E ∧ ∀ C : ProperCurve sS,
        (N : ℝ) * (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) =
          C.degree k (MMP.CartierDivisor.sheaf A) +
            C.degree k (MMP.CartierDivisor.sheaf E) := by
  obtain ⟨m, hm, hint, hbig⟩ := hLbig
  haveI := hSp
  haveI := hTp
  obtain ⟨m', hm', A, E, hA, hE, hlin⟩ :=
    (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sS sT f hf.comp_eq
      _).1 hbig
  refine ⟨m' * m, Nat.mul_pos hm' hm, A, E, hA, hE, fun C => ?_⟩
  have h1 := degree_sheaf_eq_of_linearlyEquivalent (k := k) hlin C
  rw [degree_sheaf_add A E C] at h1
  have h2 : C.degree k (MMP.CartierDivisor.sheaf
      (m' • MMP.Mori.KCartierDivisor.realization ((m : ℚ) • L) hint)) =
      m' * C.degree k (MMP.CartierDivisor.sheaf
        (MMP.Mori.KCartierDivisor.realization ((m : ℚ) • L) hint)) := by
    rw [← degreeSheafHom_apply, map_nsmul, degreeSheafHom_apply, nsmul_eq_mul]
  have h3 := degree_sheaf_realization (k := k) C _ hint
  have h4 : MMP.Fourfold.KCartierDivisor.toReal ((m : ℚ) • L) =
      (m : ℝ) • MMP.Fourfold.KCartierDivisor.toReal L := by
    ext D
    simp [MMP.Fourfold.KCartierDivisor.toReal]
  rw [h4] at h3
  have h5 : (C.cycle ℝ).intersectionNumber ((m : ℝ) • MMP.Fourfold.KCartierDivisor.toReal L) =
      (m : ℝ) * (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) := by
    simp [OneCycle.intersectionNumber]
  rw [h5] at h3
  have h6 := congrArg (fun z : ℤ => (z : ℝ)) (h2.symm.trans h1)
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_add] at h6
  rw [h3] at h6
  push_cast
  linarith

/-- **A finite set of curves spanning the cone.** If `L` is `f`-big and the class of every
contracted curve lies in the cone spanned by a finite set `s` of contracted curves, then `NE̅(S/T)`
is that cone. -/
private theorem relativeClosedConeOfCurves_eq_hull_of_finite
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hTp : MMP.Mori.IsProjectiveVariety k sT)
    (L : KCartierDivisor ℚ S) (hLbig : MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ f L)
    (s : Set {C : ProperCurve sS // C.IsContractedBy f}) (hs : s.Finite)
    (hmem : ∀ C : {C : ProperCurve sS // C.IsContractedBy f}, C.1.relativeClass f C.2 ∈
      PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
        C.1.relativeClass f C.2) '' s)) :
    relativeClosedConeOfCurves sS f =
      PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
        C.1.relativeClass f C.2) '' s) := by
  haveI := isTopologicalAddGroup_relative (sS := sS) f
  haveI := continuousSMul_relative (sS := sS) f
  haveI := t2Space_relative (sS := sS) f
  obtain ⟨N, hN, A, E, hA, hE, -⟩ := exists_degree_eq_ample_add_effective f hf hSp hTp L hLbig
  have hclosed : IsClosed (PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f}
      => C.1.relativeClass f C.2) '' s) : Set (RelativeNumericalCurveClasses sS f)) := by
    refine isClosed_hull_of_pos _ (hs.image _)
      (RelativeNumericalCurveClasses.degree sS f (MMP.CartierDivisor.sheaf A))
      (RelativeNumericalCurveClasses.continuous_degree sS f _) ?_
    rintro _ ⟨C, -, rfl⟩
    rw [degree_relativeClass]
    exact_mod_cast MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
      _ hA C.1 C.2
  have hcone : relativeConeOfCurves sS f = PointedCone.hull ℝ
      ((fun C : {C : ProperCurve sS // C.IsContractedBy f} => C.1.relativeClass f C.2) '' s) := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨C, rfl⟩
      exact hmem C
    · rintro _ ⟨C, -, rfl⟩
      exact ⟨C, rfl⟩
  rw [relativeClosedConeOfCurves, PointedCone.closure_eq, hcone, hclosed.closure_eq]

/-- A prime divisor of an integral scheme `T` has positive degree on a proper curve through the
generic point of `T`. -/
private theorem intersectionNumber_toQDivisor_single_pos [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [QuasiCompact sT] (CT : ProperCurve sT) (hCT : CT.point = genericPoint T)
    (P : MMP.Mori.PrimeDivisor T) (hP : Divisor.IsCartier (Finsupp.single P 1 : Divisor T)) :
    0 < (Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sT CT.ι CT.dim_le
      (QDivisor.isQCartier_toQDivisor hP) := by
  classical
  have h0 : 0 ≤ Divisor.toQDivisor (Finsupp.single P 1 : Divisor T) := fun Q => by
    change (0 : ℚ) ≤ (((Finsupp.single P 1 : Divisor T) Q : ℤ) : ℚ)
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  have hpt : CT.point ∉ (Divisor.toQDivisor (Finsupp.single P 1 : Divisor T)).supp := by
    rw [Divisor.supp_toQDivisor, hCT]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  obtain ⟨hnn, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sT _
    (QDivisor.isQCartier_toQDivisor hP) h0 CT hpt
  refine lt_of_le_of_ne hnn fun h => hiff.mp h.symm P.genericPoint
    (by rw [hCT]; exact (genericPoint_spec T).specializes trivial) ?_
  rw [Divisor.supp_toQDivisor]
  refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, by simp [DivisorWithCoeffs.coeff_apply], ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- A proper integral curve `T` is a proper curve through its own generic point. -/
private theorem exists_properCurve_point_eq_genericPoint [IsIntegral T] [IsProper sT]
    (hTdim : topologicalKrullDim T = 1) : ∃ CT : ProperCurve sT, CT.point = genericPoint T := by
  have hdim : topologicalKrullDim (closure ({genericPoint T} : Set T)) = 1 := by
    rw [(genericPoint_spec T).def, ← hTdim]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ T).isHomeomorph
  exact ⟨⟨genericPoint T, isProperCurve_of_isProper sT
    (by rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hdim])⟩, rfl⟩

/-- **The fibre classes are proportional.** For fibre divisors `F = f^*P`, `F' = f^*P'`, the
classes `∑_E F_E [C_E]` and `∑_E F'_E [C_E]` in `N₁(S/T)` satisfy
`(P' · T) [F] = (P · T) [F']`. -/
private theorem smul_fibreClass_eq [IsIntegral S] [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [QuasiCompact sT]
    (hS : MMP.Fourfold.IsQFactorial sS) (hSp : MMP.Mori.IsProjectiveVariety k sS)
    (hSdim : topologicalKrullDim S = 2) (hTv : MMP.Mori.IsVariety k sT)
    (hTdim : topologicalKrullDim T = 1) (f : S ⟶ T) (hfs : f ≫ sT = sS)
    (CE : MMP.Mori.PrimeDivisor S → ProperCurve sS) (hCE : ∀ E, (CE E).point = E.genericPoint)
    (CT : ProperCurve sT) (hCT : CT.point = genericPoint T)
    (P P' : MMP.Mori.PrimeDivisor T)
    (hPc : MMP.Mori.Divisor.IsCartier (Finsupp.single P 1 : Divisor T))
    (hP'c : MMP.Mori.Divisor.IsCartier (Finsupp.single P' 1 : Divisor T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    {hB' : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P' 1 : Divisor T)}
    {F' : Divisor S} (hF' : Divisor.IsPullback f (Finsupp.single P' 1 : Divisor T) hB' F')
    (hc : ∀ E ∈ F.support, (CE E).IsContractedBy f)
    (hc' : ∀ E ∈ F'.support, (CE E).IsContractedBy f) :
    ((Divisor.toQDivisor (Finsupp.single P' 1)).intersectionNumber k sT CT.ι CT.dim_le
        (QDivisor.isQCartier_toQDivisor hP'c) : ℝ) •
      ∑ E ∈ F.support.attach, ((F E.1 : ℤ) : ℝ) • (CE E.1).relativeClass f (hc E.1 E.2) =
    ((Divisor.toQDivisor (Finsupp.single P 1)).intersectionNumber k sT CT.ι CT.dim_le
        (QDivisor.isQCartier_toQDivisor hPc) : ℝ) •
      ∑ E ∈ F'.support.attach, ((F' E.1 : ℤ) : ℝ) • (CE E.1).relativeClass f (hc' E.1 E.2) := by
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : IsNoetherian S := ⟨⟩
  refine eq_of_forall_degree_eq fun Lm _ => ?_
  obtain ⟨EL, ⟨eL⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf Lm
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier EL
  have hdeg : ∀ (G : Divisor S) (hG : ∀ E ∈ G.support, (CE E).IsContractedBy f),
      RelativeNumericalCurveClasses.degree sS f Lm
        (∑ E ∈ G.support.attach, ((G E.1 : ℤ) : ℝ) • (CE E.1).relativeClass f (hG E.1 E.2)) =
      ((∑ E ∈ G.support, (G E : ℚ) * (Divisor.toQDivisor w).intersectionNumber k sS (CE E).ι
        (CE E).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℚ) : ℝ) := by
    intro G hG
    simp only [map_sum, map_smul, degree_relativeClass, smul_eq_mul]
    rw [Finset.sum_attach G.support (fun E => ((G E : ℤ) : ℝ) * ((CE E).degree k Lm : ℝ)),
      Rat.cast_sum]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [degree_eq_intersectionNumber_of_iso hS eL hw]
    push_cast
    ring
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, hdeg, hdeg]
  have := congrArg (fun q : ℚ => (q : ℝ))
    (fibre_sum_relation hS hSp hSdim hTv hTdim f hfs CE hCE CT hCT P P' hPc hP'c hF hF' w)
  simp only [Rat.cast_mul] at this
  exact this

private theorem relativeClass_congr {f : S ⟶ T} {C₁ C₂ : ProperCurve sS} (h : C₁ = C₂)
    (h₁ : C₁.IsContractedBy f) (h₂ : C₂.IsContractedBy f) :
    C₁.relativeClass f h₁ = C₂.relativeClass f h₂ := by
  subst h
  rfl

/-- A vector proportional, with positive coefficients, to a member of a pointed cone lies in it. -/
private theorem mem_of_smul_eq_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {H : PointedCone ℝ V} {c φ ψ : V} {n a a₀ : ℝ} (hn : 0 < n) (ha : 0 < a) (ha₀ : 0 < a₀)
    (hφ : φ = n • c) (key : a₀ • φ = a • ψ) (hψ : ψ ∈ H) : c ∈ H := by
  have : c = (n⁻¹ * (a₀⁻¹ * a)) • ψ := by
    rw [mul_smul, mul_smul, ← key, hφ, smul_smul a₀⁻¹, inv_mul_cancel₀ ha₀.ne', one_smul,
      smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  rw [this]
  exact PointedCone.smul_mem _ (by positivity) hψ

/-- **The finite cone over a curve.** If `dim T = 1`, then `NE̅(S/T)` is spanned by the classes of
finitely many contracted curves: the components of the finitely many fibres which are not
irreducible, and of one further fibre, whose class is that of every fibre. -/
private theorem exists_finset_cone_of_dim_one
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hTp : MMP.Mori.IsProjectiveVariety k sT)
    (hS : MMP.Fourfold.IsQFactorial sS)
    (hSdim : topologicalKrullDim S = 2) (hTdim : topologicalKrullDim T = 1)
    (L : KCartierDivisor ℚ S) (hLbig : MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ f L) :
    ∃ s : Finset {C : ProperCurve sS // C.IsContractedBy f},
      relativeClosedConeOfCurves sS f =
        PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
          C.1.relativeClass f C.2) '' (s : Set _)) := by
  classical
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  have : IsIntegral S := hSv.toIsIntegral
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : IsNoetherian S := ⟨⟩
  have hT := hf.isNormalVariety_target
  have hTv : MMP.Mori.IsVariety k sT := hT.1
  have : IsIntegral T := hT.1.toIsIntegral
  have : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  have : QuasiCompact sT := hT.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : IsNormal T := hT.2
  have : LocallyOfFinitePresentation sT :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hTs : IsSmoothScheme sT := (MMP.Mori.isSmoothScheme_iff sT).mpr
    (smooth_of_isRegular_over_perfectField sT
      (isRegular_of_isNormal_of_topologicalKrullDim_le_one T hTdim.le))
  have : IsProper sS := ((MMP.Mori.isProjectiveVariety_iff k sS).mp hSp).2.isProjective.isProper
  have : IsProper sT := ((MMP.Mori.isProjectiveVariety_iff k sT).mp hTp).2.isProjective.isProper
  have : IsProper f := hf.isProjectiveMorphism.isProjective.isProper
  have hcart : ∀ D : Divisor T, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hTs
  have hη : ∀ (D : Divisor T) (Z : irreducibleComponents S),
      f (componentGenericPoint S Z) ∉ D.supp := fun D Z => by
    rw [map_componentGenericPoint_eq_genericPoint f hf.surjective]
    exact MMP.Fourfold.genericPoint_notMem_supp D
  -- the fibre divisors over the closed points of `T`
  have hfib : ∀ y : T, IsClosed ({y} : Set T) → ∃ (P : MMP.Mori.PrimeDivisor T) (F : Divisor S),
      P.genericPoint = y ∧ Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) (hη _) F := by
    intro y hy
    have hy1 : Order.coheight y = 1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hTdim
      (fun h => MMP.Fourfold.not_isClosed_genericPoint hTdim (h ▸ hy))
    exact ⟨_, _, AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hy1,
      Divisor.isPullback_pullback (f := f) (hcart _) (hη _)⟩
  choose Pf Ff hPf hFf using hfib
  choose CE hCE using fun E : MMP.Mori.PrimeDivisor S =>
    exists_properCurve_of_primeDivisor (sS := sS) hSdim E
  have hoverF : ∀ y hy (E : MMP.Mori.PrimeDivisor S), E ∈ (Ff y hy).support ↔
      f E.genericPoint = y := fun y hy E => by
    rw [mem_support_iff_of_isPullback_single f (Pf y hy) ((hPf y hy).symm ▸ hy) (hFf y hy), hPf]
  have hFpos : ∀ y hy E, E ∈ (Ff y hy).support → 0 < Ff y hy E := fun y hy E hE =>
    MMP.Fourfold.coeff_pos_of_isPullback_single f (Pf y hy) (hFf y hy) E
      (by rw [hPf]; exact (hoverF y hy E).mp hE)
  have hcontr : ∀ y hy E, E ∈ (Ff y hy).support → (CE E).IsContractedBy f := fun y hy E hE =>
    isContractedBy_of_isClosed f (CE E) (by rw [hCE, (hoverF y hy E).mp hE]; exact hy)
  -- the curve `T` itself
  obtain ⟨CT, hCT⟩ := exists_properCurve_point_eq_genericPoint (sT := sT) hTdim
  set a : ∀ y : T, IsClosed ({y} : Set T) → ℚ := fun y hy =>
    (Divisor.toQDivisor (Finsupp.single (Pf y hy) 1)).intersectionNumber k sT CT.ι CT.dim_le
      (QDivisor.isQCartier_toQDivisor (hcart _)) with ha
  have hapos : ∀ y hy, 0 < a y hy := fun y hy =>
    intersectionNumber_toQDivisor_single_pos CT hCT (Pf y hy) (hcart _)
  -- the topology of `N₁(S/T)`
  haveI := isTopologicalAddGroup_relative (sS := sS) f
  haveI := continuousSMul_relative (sS := sS) f
  haveI := t2Space_relative (sS := sS) f
  -- the classes of the fibres
  set Φ : ∀ y : T, IsClosed ({y} : Set T) → RelativeNumericalCurveClasses sS f := fun y hy =>
    ∑ E ∈ (Ff y hy).support.attach,
      ((Ff y hy E.1 : ℤ) : ℝ) • (CE E.1).relativeClass f (hcontr y hy E.1 E.2) with hΦ
  have hprop : ∀ y hy y' hy', (a y' hy' : ℝ) • Φ y hy = (a y hy : ℝ) • Φ y' hy' :=
    fun y hy y' hy' => smul_fibreClass_eq hS hSp hSdim hTv hTdim f hf.comp_eq CE hCE CT hCT
      (Pf y hy) (Pf y' hy') (hcart _) (hcart _) (hFf y hy) (hFf y' hy') (hcontr y hy)
      (hcontr y' hy')
  -- a dense open of irreducible fibres
  obtain ⟨W, hWo, hWne, hWirr⟩ :=
    exists_isOpen_isIrreducible_preimage f hf.isIso_app hf.surjective
  have hBfin : Wᶜ.Finite := finite_compl_of_isOpen hTdim hWo hWne
  obtain ⟨y₀, -, hy₀⟩ := isClosed_univ.exists_closed_singleton (⟨genericPoint T, trivial⟩ :
    (Set.univ : Set T).Nonempty)
  set B : Set T := insert y₀ Wᶜ with hB
  have hBf : B.Finite := hBfin.insert y₀
  -- the generating curves
  have hηW : genericPoint T ∈ W :=
    ((genericPoint_spec T).mem_open_set_iff hWo).mpr (by simpa using hWne)
  have hBc : ∀ y ∈ B, IsClosed ({y} : Set T) := by
    rintro y (rfl | hy)
    · exact hy₀
    · exact isClosed_singleton_of_ne_genericPoint hTdim (fun h => hy (h ▸ hηW))
  have hsfin : {C : {C : ProperCurve sS // C.IsContractedBy f} | f C.1.point ∈ B}.Finite := by
    choose EC hEC using fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
      exists_primeDivisor_genericPoint_eq (sS := sS) hSdim C.1
    refine Set.Finite.of_finite_image (f := EC) ?_ (fun C₁ _ C₂ _ h =>
      Subtype.ext (ProperCurve.ext ((hEC C₁).symm.trans ((congrArg _ h).trans (hEC C₂)))))
    refine (hBf.biUnion' (t := fun y hy => ((Ff y (hBc y hy)).support : Set _))
      fun y hy => (Ff y (hBc y hy)).support.finite_toSet).subset ?_
    rintro _ ⟨C, hC, rfl⟩
    refine Set.mem_iUnion₂.mpr ⟨f C.1.point, hC, ?_⟩
    exact Finset.mem_coe.mpr ((hoverF _ _ _).mpr (by rw [hEC]))
  set G : Set (RelativeNumericalCurveClasses sS f) :=
    (fun C : {C : ProperCurve sS // C.IsContractedBy f} => C.1.relativeClass f C.2) ''
      (hsfin.toFinset : Set _)
  set H := PointedCone.hull ℝ G
  have hmem : ∀ C : {C : ProperCurve sS // C.IsContractedBy f}, C.1.relativeClass f C.2 ∈ H := by
    intro C
    by_cases hCB : f C.1.point ∈ B
    · exact Submodule.subset_span ⟨C, hsfin.mem_toFinset.mpr hCB, rfl⟩
    have hy := isClosed_singleton_of_isContractedBy f f.isClosedMap C.1 C.2
    have hyW : f C.1.point ∈ W := of_not_not fun h => hCB (Or.inr h)
    obtain ⟨E, hE⟩ := exists_primeDivisor_genericPoint_eq (sS := sS) hSdim C.1
    have hEsupp : E ∈ (Ff _ hy).support := (hoverF _ hy E).mpr (by rw [hE])
    have hsingle : ∀ E' ∈ (Ff _ hy).support, E' = E := fun E' hE' =>
      eq_of_mem_support_of_isIrreducible f (Pf _ hy) ((hPf _ hy).symm ▸ hy) (hFf _ hy)
        (by rw [hPf]; exact hWirr _ hyW) hEsupp hE'
    have hΦy : Φ _ hy = ((Ff _ hy E : ℤ) : ℝ) • C.1.relativeClass f C.2 := by
      simp only [hΦ]
      rw [Finset.sum_eq_single_of_mem ⟨E, hEsupp⟩ (Finset.mem_attach _ _)
        (fun b _ hb => absurd (Subtype.ext (hsingle b.1 b.2)) hb)]
      exact congrArg _ (relativeClass_congr (ProperCurve.ext ((hCE E).trans hE)) _ _)
    have hΦ₀ : Φ y₀ hy₀ ∈ H := by
      refine Submodule.sum_mem _ fun E' _ => ?_
      refine PointedCone.smul_mem _ (by exact_mod_cast (hFpos _ _ _ E'.2).le)
        (Submodule.subset_span ⟨⟨CE E'.1, hcontr _ _ _ E'.2⟩, hsfin.mem_toFinset.mpr ?_, rfl⟩)
      show f (CE E'.1).point ∈ B
      rw [hCE, (hoverF _ _ _).mp E'.2]
      exact Or.inl rfl
    exact mem_of_smul_eq_smul (by exact_mod_cast hFpos _ hy E hEsupp)
      (by exact_mod_cast hapos _ hy) (by exact_mod_cast hapos y₀ hy₀) hΦy (hprop _ hy y₀ hy₀) hΦ₀
  exact ⟨hsfin.toFinset, relativeClosedConeOfCurves_eq_hull_of_finite f hf hSp hTp L hLbig _
    hsfin.toFinset.finite_toSet hmem⟩

/-- **The fibre divisor is nef on curves.** The pull-back of a closed point of `T` has nonnegative
intersection number with every proper curve on `S`. -/
private theorem intersectionNumber_pullback_single_nonneg [IsProper sS] [IsLocallyNoetherian T]
    [IsNormal T] [QuasiCompact sT] [CompactSpace T]
    (hS : MMP.Fourfold.IsQFactorial sS) (hSv : MMP.Mori.IsVariety k sS)
    (hTv : MMP.Mori.IsVariety k sT) (f : S ⟶ T) (hfs : f ≫ sT = sS)
    (P : MMP.Mori.PrimeDivisor T)
    (hPc : MMP.Mori.Divisor.IsCartier (Finsupp.single P 1 : Divisor T))
    {hB : ∀ Z : irreducibleComponents S,
      f (componentGenericPoint S Z) ∉ DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor T)}
    {F : Divisor S} (hF : Divisor.IsPullback f (Finsupp.single P 1 : Divisor T) hB F)
    (hy : IsClosed ({P.genericPoint} : Set T)) (C : ProperCurve sS) :
    0 ≤ (Divisor.toQDivisor F).intersectionNumber k sS C.ι C.dim_le
      (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  by_cases hC : f C.point = P.genericPoint
  · exact (intersectionNumber_pullback_eq_zero_of_vertical hS hSv hTv f hfs P hPc hF C
      ⟨_, range_ι_comp_eq_singleton f C (isContractedBy_of_isClosed f C (hC ▸ hy))⟩).ge
  have hF0 : 0 ≤ Divisor.toQDivisor F := fun Q => by
    change (0 : ℚ) ≤ ((F Q : ℤ) : ℚ)
    by_cases hQ : Q ∈ F.support
    · exact_mod_cast (show 0 < F Q from MMP.Fourfold.coeff_pos_of_isPullback_single f P hF Q
        ((mem_support_iff_of_isPullback_single f P hy hF Q).mp hQ)).le
    · simp [Finsupp.notMem_support_iff.mp hQ]
  refine (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sS _ _ hF0 C ?_).1
  rw [Divisor.supp_toQDivisor]
  intro hmem
  obtain ⟨G, hG, hxG⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxG
  have hsp := (specializes_iff_mem_closure.mpr hxG).map f.continuous
  rw [(mem_support_iff_of_isPullback_single f P hy hF G).mp (Finsupp.mem_support_iff.mpr hG)] at hsp
  exact hC (hsp.mem_closed hy rfl)

/-- **A big divisor is nonzero on every fibre.** Over every closed point of the curve `T`, some
component of the fibre has nonzero intersection number with `L`. -/
private theorem exists_primeDivisor_intersectionNumber_ne_zero_of_dim_one
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hTp : MMP.Mori.IsProjectiveVariety k sT)
    (hS : MMP.Fourfold.IsQFactorial sS)
    (hSdim : topologicalKrullDim S = 2) (hTdim : topologicalKrullDim T = 1)
    (L : KCartierDivisor ℚ S)
    (hLbig : MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ f L) (y : T)
    (hy : IsClosed ({y} : Set T)) :
    ∃ E : MMP.Mori.PrimeDivisor S, f E.genericPoint = y ∧ ∀ C : ProperCurve sS,
      C.point = E.genericPoint →
        (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) ≠ 0 := by
  classical
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  have : IsIntegral S := hSv.toIsIntegral
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : IsNoetherian S := ⟨⟩
  have hT := hf.isNormalVariety_target
  have hTv : MMP.Mori.IsVariety k sT := hT.1
  have : IsIntegral T := hT.1.toIsIntegral
  have : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  have : QuasiCompact sT := hT.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : IsNormal T := hT.2
  have : LocallyOfFinitePresentation sT :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hTs : IsSmoothScheme sT := (MMP.Mori.isSmoothScheme_iff sT).mpr
    (smooth_of_isRegular_over_perfectField sT
      (isRegular_of_isNormal_of_topologicalKrullDim_le_one T hTdim.le))
  have : IsProper sS := ((MMP.Mori.isProjectiveVariety_iff k sS).mp hSp).2.isProjective.isProper
  have hcart : ∀ D : Divisor T, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hTs
  have hη : ∀ (D : Divisor T) (Z : irreducibleComponents S),
      f (componentGenericPoint S Z) ∉ D.supp := fun D Z => by
    rw [map_componentGenericPoint_eq_genericPoint f hf.surjective]
    exact MMP.Fourfold.genericPoint_notMem_supp D
  -- the fibre over `y`
  have hy1 : Order.coheight y = 1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hTdim
    (fun h => MMP.Fourfold.not_isClosed_genericPoint hTdim (h ▸ hy))
  set Py := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1
  have hPy : MMP.Mori.PrimeDivisor.genericPoint Py = y :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  obtain ⟨F, hF⟩ : ∃ F : Divisor S, Divisor.IsPullback f (Finsupp.single Py 1 : Divisor T)
      (hη _) F :=
    ⟨_, Divisor.isPullback_pullback (f := f) (hcart (Finsupp.single Py 1)) (hη _)⟩
  choose CE hCE using fun E : MMP.Mori.PrimeDivisor S =>
    exists_properCurve_of_primeDivisor (sS := sS) hSdim E
  have hoverF : ∀ E : MMP.Mori.PrimeDivisor S, E ∈ F.support ↔ f E.genericPoint = y :=
    fun E => by rw [mem_support_iff_of_isPullback_single f Py (hPy ▸ hy) hF, hPy]
  have hFpos : ∀ E ∈ F.support, 0 < F E := fun E hE =>
    MMP.Fourfold.coeff_pos_of_isPullback_single f Py hF E (hPy ▸ (hoverF E).mp hE)
  have hcontr : ∀ E ∈ F.support, (CE E).IsContractedBy f := fun E hE =>
    isContractedBy_of_isClosed f (CE E) (by rw [hCE, (hoverF E).mp hE]; exact hy)
  have hne : F.support.Nonempty := by
    obtain ⟨x, hx⟩ := hf.surjective y
    obtain ⟨G, hG, -⟩ := DivisorWithCoeffs.mem_supp_iff.mp
      (MMP.Fourfold.mem_supp_of_isPullback_single f Py hF (hx.trans hPy.symm))
    exact ⟨G, Finsupp.mem_support_iff.mpr hG⟩
  -- the decomposition `N L ≡ A + E`
  obtain ⟨N, hN, A, E, hA, hE, hdeg⟩ :=
    exists_degree_eq_ample_add_effective f hf hSp hTp L hLbig
  have hApos : 0 < ∑ G ∈ F.support, F G * (CE G).degree k (MMP.CartierDivisor.sheaf A) :=
    Finset.sum_pos (fun G hG => mul_pos (hFpos G hG)
      (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hA (CE G)
        (hcontr G hG))) hne
  have hEnn : 0 ≤ ∑ G ∈ F.support, F G * (CE G).degree k (MMP.CartierDivisor.sheaf E) := by
    obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier E
    have hw0 : ∀ P, 0 ≤ w P := fun P => (hw P).nonneg_of_isEffective hE
    have e1 : ((∑ G ∈ F.support, F G * (CE G).degree k
        (MMP.CartierDivisor.sheaf E) : ℤ) : ℚ) =
        ∑ G ∈ F.support, (F G : ℚ) * (Divisor.toQDivisor w).intersectionNumber k sS (CE G).ι
          (CE G).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
      push_cast
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [degree_sheaf_eq_degreeOn hw, intersectionNumber_toQDivisor_eq_degreeOn hS w hw.isCartier]
    rw [sum_mul_intersectionNumber_comm hS hSp hSdim CE hCE w F] at e1
    have hnn : 0 ≤ ∑ G ∈ w.support, (w G : ℚ) * (Divisor.toQDivisor F).intersectionNumber k sS
        (CE G).ι (CE G).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) :=
      Finset.sum_nonneg fun G _ => mul_nonneg (by exact_mod_cast hw0 G)
        (intersectionNumber_pullback_single_nonneg hS hSv hTv f hf.comp_eq Py (hcart _) hF
          (hPy ▸ hy) (CE G))
    have : (0 : ℚ) ≤ ((∑ G ∈ F.support, F G * (CE G).degree k
        (MMP.CartierDivisor.sheaf E) : ℤ) : ℚ) := e1 ▸ hnn
    exact_mod_cast this
  -- hence `L` is positive on the fibre
  have hLpos : 0 < ∑ G ∈ F.support, (F G : ℝ) *
      ((CE G).cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) := by
    have e : (N : ℝ) * ∑ G ∈ F.support, (F G : ℝ) *
        ((CE G).cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) =
        ((∑ G ∈ F.support, F G * (CE G).degree k (MMP.CartierDivisor.sheaf A) +
          ∑ G ∈ F.support, F G * (CE G).degree k (MMP.CartierDivisor.sheaf E) :
            ℤ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun G _ => ?_
      rw [← mul_add, ← hdeg]
      ring
    have hpos : (0 : ℝ) < ((∑ G ∈ F.support, F G * (CE G).degree k
        (MMP.CartierDivisor.sheaf A) + ∑ G ∈ F.support, F G * (CE G).degree k
          (MMP.CartierDivisor.sheaf E) : ℤ) : ℝ) := by
      exact_mod_cast add_pos_of_pos_of_nonneg hApos hEnn
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)
  obtain ⟨G, hG, hG0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLpos.ne'
  refine ⟨G, (hoverF G).mp hG, fun C hC => ?_⟩
  have : C = CE G := ProperCurve.ext (hC.trans (hCE G).symm)
  subst this
  exact fun h => hG0 (by rw [h, mul_zero])

/-- **The case of a curve.** If `dim T = 1`, then `NE̅(S/T)` is spanned by finitely many
contracted curves, and the intersection matrix of any finite family of distinct contracted
curves on which `L` vanishes is negative definite. -/
private theorem cone_and_posDef_of_dim_one
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : MMP.Mori.IsProjectiveVariety k sS) (hTp : MMP.Mori.IsProjectiveVariety k sT)
    (hS : MMP.Fourfold.IsQFactorial sS)
    (hSdim : topologicalKrullDim S = 2) (hTdim : topologicalKrullDim T = 1)
    (L : KCartierDivisor ℚ S)
    (hLnef : MMP.Fourfold.KCartierDivisor.IsRelativelyNefQ sS f L)
    (hLbig : MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ f L) :
    (∃ s : Finset {C : ProperCurve sS // C.IsContractedBy f},
      relativeClosedConeOfCurves sS f =
        PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
          C.1.relativeClass f C.2) '' (s : Set _))) ∧
    ∀ (r : ℕ) (C : Fin r → ProperCurve sS) (_hC : ∀ i, (C i).IsContractedBy f)
      (P : Fin r → MMP.Mori.PrimeDivisor S),
      Function.Injective C → (∀ i, (C i).point = (P i).genericPoint) →
      (∀ i, ((C i).cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) = 0) →
      (-(Matrix.of fun i j : Fin r =>
        ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sS (C j).ι
          (C j).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℝ))).PosDef := by
  classical
  have hSv : MMP.Mori.IsVariety k sS := hS.1.1
  have : IsIntegral S := hSv.toIsIntegral
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have hT := hf.isNormalVariety_target
  have : IsIntegral T := hT.1.toIsIntegral
  have : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  have : QuasiCompact sT := hT.1.toQuasiCompact
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have : IsNormal T := hT.2
  have : LocallyOfFinitePresentation sT :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hTs : IsSmoothScheme sT := (MMP.Mori.isSmoothScheme_iff sT).mpr
    (smooth_of_isRegular_over_perfectField sT
      (isRegular_of_isNormal_of_topologicalKrullDim_le_one T hTdim.le))
  have hproj := hf.isProjectiveMorphism
  have : IsProper f := hproj.isProjective.isProper
  have hfib : ∀ y : T, _root_.IsPreconnected (f ⁻¹' {y}) := fun y =>
    (f.isConnected_preimage_singleton_of_isIso_app hf.isIso_app y).isPreconnected
  have hη : ∀ (D : Divisor T) (Z : irreducibleComponents S),
      f (componentGenericPoint S Z) ∉ D.supp := fun D Z => by
    rw [map_componentGenericPoint_eq_genericPoint f hf.surjective]
    exact MMP.Fourfold.genericPoint_notMem_supp D
  have hcart : ∀ D : Divisor T, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hTs
  refine ⟨exists_finset_cone_of_dim_one f hf hSp hTp hS hSdim hTdim L hLbig,
    fun r C hC P hCinj hCP hzero => ?_⟩
  set φ : Fin r → T := fun i => f (C i).point
  refine MMP.MatrixPosDef.posDef_of_eq_zero_of_ne_of_posDef_submatrix φ _ (fun i j hij => ?_)
    (fun y => ?_)
  · -- curves over distinct points are disjoint
    simp only [Matrix.neg_apply, Matrix.of_apply, neg_eq_zero, Rat.cast_eq_zero]
    refine MMP.Fourfold.intersectionNumber_eq_zero_of_disjoint sS hS _ _ (C j) fun x hx hxs => ?_
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxs
    rw [MMP.Threefold.Resolution.toQDivisor_single] at hE
    have hEP : P i = E := by
      by_contra hne
      exact hE (by simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hne])
    subst hEP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxE
    change x ∈ closure {(P i).genericPoint} at hxE
    rw [← hCP i] at hxE
    exact hij ((hC i x hxE).symm.trans (hC j x (specializes_iff_mem_closure.mp hx)))
  · by_cases hJ : ∃ i, φ i = y
    · obtain ⟨i₀, hi₀⟩ := hJ
      have hyc : IsClosed ({y} : Set T) := hi₀ ▸
        isClosed_singleton_of_isContractedBy f f.isClosedMap _ (hC i₀)
      have hy1 : Order.coheight y = 1 := MMP.Fourfold.coheight_eq_one_of_ne_genericPoint hTdim
        (fun h => MMP.Fourfold.not_isClosed_genericPoint hTdim (h ▸ hyc))
      set Py := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hy1
      have hPy : MMP.Mori.PrimeDivisor.genericPoint Py = y :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      have hF := Divisor.isPullback_pullback (f := f) (hcart (Finsupp.single Py 1)) (hη _)
      obtain ⟨E₀, hE₀, hE₀L⟩ := exists_primeDivisor_intersectionNumber_ne_zero_of_dim_one f hf hSp
        hTp hS hSdim hTdim L hLbig y hyc
      have hblock := posDef_neg_of_fibre hS hSp hSdim f hfib Py (hPy ▸ hyc) hF
        (J := {i // φ i = y}) (fun j => P j.1)
        (fun a b h => Subtype.ext (hCinj (ProperCurve.ext ((hCP a.1).trans
          ((congrArg _ h).trans (hCP b.1).symm)))))
        (fun j => C j.1) (fun j => hCP j.1) (fun j => by rw [← hCP j.1, hPy]; exact j.2) E₀
        (by rw [hPy]; exact hE₀) (fun j hj => hE₀L (C j.1) ((hCP j.1).trans (by rw [hj]))
          (hzero j.1))
      convert hblock using 1
      ext i j
      rfl
    · haveI : IsEmpty {i // φ i = y} := ⟨fun ⟨i, hi⟩ => hJ ⟨i, hi⟩⟩
      refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
      · ext i
        exact isEmptyElim i
      · exact absurd (funext isEmptyElim) hx

end Cases

end Proof_lem_mmp_surface_positive_base_null_face

namespace MMP.Mori

open Proof_lem_mmp_surface_positive_base_null_face

/-- **The finite relative cone and the null matrix of a surface contraction.** Let `f : S ⟶ T` be
a projective contraction of normal projective varieties over an algebraically closed field `k`
of characteristic zero, with `S` a `ℚ`-factorial surface and `dim T ∈ {1, 2}`, and let `L` be an
`f`-nef and `f`-big `ℚ`-Cartier divisor on `S`. Then:
* `NE̅(S/T)` is the cone spanned by the classes of finitely many curves contracted by `f`;
* there are finitely many distinct contracted curves `C₁, …, C_r`, with prime divisors `Pᵢ`
  having the same generic points, such that the face `{z ∈ NE̅(S/T) : (z · L) = 0}` is the cone
  spanned by their classes;
* the matrix `((Pᵢ · Cⱼ))` is negative definite, and its off-diagonal entries are nonnegative. -/
@[mmp "lem_mmp_surface_positive_base_null_face"]
theorem exists_faceOfNefForm_relativeClosedConeOfCurves_eq_hull_posDef_neg
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {S T : Scheme.{u}} {sS : S ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)}
    [IsLocallyNoetherian S] [IsNormal S] [QuasiCompact sS] [IrreducibleSpace S]
    (f : S ⟶ T) (hf : MMP.Fourfold.IsContraction sS sT f)
    (hSp : IsProjectiveVariety k sS) (hTp : IsProjectiveVariety k sT)
    (hS : MMP.Fourfold.IsQFactorial sS) (hSdim : topologicalKrullDim S = 2)
    (hTdim : topologicalKrullDim T = 1 ∨ topologicalKrullDim T = 2) (L : KCartierDivisor ℚ S)
    (hLnef : MMP.Fourfold.KCartierDivisor.IsRelativelyNefQ sS f L)
    (hLbig : MMP.Fourfold.KCartierDivisor.IsRelativelyBigQ f L) :
    (∃ s : Finset {C : ProperCurve sS // C.IsContractedBy f},
      relativeClosedConeOfCurves sS f =
        PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
          C.1.relativeClass f C.2) '' (s : Set _))) ∧
    ∃ (r : ℕ) (C : Fin r → ProperCurve sS) (hC : ∀ i, (C i).IsContractedBy f)
      (P : Fin r → PrimeDivisor S),
      Function.Injective C ∧ (∀ i, (C i).point = (P i).genericPoint) ∧
      faceOfNefForm (relativeClosedConeOfCurves sS f : Set (RelativeNumericalCurveClasses sS f))
          (RelativeNumericalCurveClasses.intersectionNumber
            (MMP.Fourfold.KCartierDivisor.toReal L)) =
        (PointedCone.hull ℝ (Set.range fun i => (C i).relativeClass f (hC i)) :
          Set (RelativeNumericalCurveClasses sS f)) ∧
      (-(Matrix.of fun i j : Fin r =>
        ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sS (C j).ι
          (C j).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℝ))).PosDef ∧
      ∀ i j : Fin r, i ≠ j →
        0 ≤ (Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sS (C j).ι
          (C j).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) := by
  classical
  have : IsIntegral S := hS.1.1.toIsIntegral
  have : LocallyOfFiniteType sS := hS.1.1.toLocallyOfFiniteType
  -- the finite cone and negative definiteness on `L`-trivial families
  obtain ⟨⟨s, hs⟩, hneg⟩ : (∃ s : Finset {C : ProperCurve sS // C.IsContractedBy f},
      relativeClosedConeOfCurves sS f =
        PointedCone.hull ℝ ((fun C : {C : ProperCurve sS // C.IsContractedBy f} =>
          C.1.relativeClass f C.2) '' (s : Set _))) ∧
      ∀ (r : ℕ) (C : Fin r → ProperCurve sS) (_hC : ∀ i, (C i).IsContractedBy f)
        (P : Fin r → MMP.Mori.PrimeDivisor S),
        Function.Injective C → (∀ i, (C i).point = (P i).genericPoint) →
        (∀ i, ((C i).cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal L) = 0) →
        (-(Matrix.of fun i j : Fin r =>
          ((Divisor.toQDivisor (Finsupp.single (P i) 1)).intersectionNumber k sS (C j).ι
            (C j).dim_le (MMP.Fourfold.isQCartier_of_isQFactorial sS hS _) : ℝ))).PosDef := by
    rcases hTdim with h1 | h2
    · exact cone_and_posDef_of_dim_one f hf hSp hTp hS hSdim h1 L hLnef hLbig
    · obtain ⟨hc, hn⟩ := cone_and_posDef_of_dim_two f hf hSp hTp hS hSdim h2
      exact ⟨hc, fun r C hC P hCi hCP _ => hn r C hC P hCi hCP⟩
  -- the linear form `z ↦ (z · L)`
  set ℓ := RelativeNumericalCurveClasses.intersectionNumber (sX := sS) (f := f)
    (MMP.Fourfold.KCartierDivisor.toReal L)
  have hℓ : ∀ C : {C : ProperCurve sS // C.IsContractedBy f},
      ℓ (C.1.relativeClass f C.2) = (C.1.cycle ℝ).intersectionNumber
        (MMP.Fourfold.KCartierDivisor.toReal L) := fun C => rfl
  -- the `L`-trivial curves of `s`, enumerated
  set s₀ := s.filter fun C => ℓ (C.1.relativeClass f C.2) = 0
  set e := s₀.equivFin
  set Cs : Fin s₀.card → ProperCurve sS := fun i => (e.symm i).1.1
  have hCs : ∀ i, (Cs i).IsContractedBy f := fun i => (e.symm i).1.2
  choose P hP using fun i => exists_primeDivisor_genericPoint_eq hSdim (Cs i)
  have hCinj : Function.Injective Cs := fun i j h =>
    e.symm.injective (Subtype.ext (Subtype.ext h))
  have hzero : ∀ i, ((Cs i).cycle ℝ).intersectionNumber
      (MMP.Fourfold.KCartierDivisor.toReal L) = 0 := fun i =>
    (hℓ _).symm.trans (Finset.mem_filter.mp (e.symm i).2).2
  refine ⟨⟨s, hs⟩, s₀.card, Cs, hCs, P, hCinj, fun i => (hP i).symm, ?_,
    hneg _ Cs hCs P hCinj (fun i => (hP i).symm) hzero, fun i j hij => ?_⟩
  · rw [hs, faceOfNefForm_hull_eq _ ℓ ?_]
    · congr 2
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Set.mem_range]
      constructor
      · rintro ⟨⟨C, hC, rfl⟩, hz⟩
        refine ⟨e ⟨C, Finset.mem_filter.mpr ⟨hC, hz⟩⟩, ?_⟩
        simp [Cs]
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(e.symm i).1, (Finset.mem_filter.mp (e.symm i).2).1, rfl⟩,
          (Finset.mem_filter.mp (e.symm i).2).2⟩
    · rintro _ ⟨C, -, rfl⟩
      rw [hℓ]
      exact hLnef C.1 C.2
  · refine intersectionNumber_single_nonneg_of_ne hS (P i) (P j) (fun h => hij ?_) (Cs j)
      (hP j).symm
    exact hCinj (ProperCurve.ext ((hP i).symm.trans ((congrArg _ h).trans (hP j))))

end MMP.Mori
