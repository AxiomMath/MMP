module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.DltFloor.Sdlt
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedSdltSurface
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
public import MMP.AlgebraicGeometry.MMP.Threefold.Flip.FloorProgramInputs
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedThreefoldHorizontalFloor
public import MMP.AlgebraicGeometry.MMP.Threefold.VerticalFloorPencil
public import MMP.AlgebraicGeometry.MMP.BasepointFree.DltFloorSemiample
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.Divisor.PullbackExistence
public import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.ChowForm.FibreChowForm
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Complemented projective lc threefolds are relatively good

Let `(X, B)` be an effective rational log canonical pair on a normal projective complex
threefold, and `f : X ⟶ Z` a morphism to a projective variety such that `D = K_X + B` is `f`-nef.
If an effective `ℚ`-Cartier `ℚ`-divisor `A` makes `(X, B + A)` log canonical and
`D + A ∼_ℚ f^*H` for a `ℚ`-Cartier divisor `H` on `Z`, then `D` is `f`-semiample.

## Main results

* `MMP.Fourfold.isRelativelySemiample_of_isLogCanonicalPair_add_of_qLinearlyEquivalent`.

## Implementation notes

The morphism `f` need not be dominant, so `f^*H` is the pull-back of an invertible sheaf: the
condition `D + A ∼_ℚ f^*H` is stated as `D + A ∼_ℚ G` (`MMP.Mori.QDivisor.QLinearlyEquivalent`)
for a `ℚ`-divisor `G` on `X` with `𝒪_X(mG) ≅ f^*M` for some `m > 0` and some invertible
`𝒪_Z`-module `M` (namely `M = 𝒪_Z(mH)`), as in
`MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`. On the
integral projective variety `Z` every invertible sheaf is `𝒪_Z(H)` for a Cartier divisor `H`, so
this is the source's condition. "`D` is `f`-semiample" is
`MMP.Fourfold.QDivisor.IsRelativelySemiample f D`. The canonical divisor `K_X` is any canonical
divisor of `X`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

namespace Proof_thm_fourfold_projective_complemented_lc_threefold_good

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Relative semiampleness and relatively free multiples -/

section Conversion

open MMP.Intersection

/-- An epimorphic counit of `f^* ⊣ f_*` stays epimorphic along an isomorphism of modules. -/
private theorem epi_counit_of_iso {X Z : Scheme.{0}} (f : X ⟶ Z) {M N : X.Modules} (e : N ≅ M)
    (h : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hnat := adj.counit.naturality e.hom
  have heq : adj.counit.app N =
      (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).map e.hom ≫
        adj.counit.app M ≫ e.inv := by
    rw [← Category.assoc, hnat, Functor.id_map, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [heq]
  infer_instance

/-- On an integral locally Noetherian scheme, a point of coheight zero lies in the support of no
Cartier divisor. -/
private theorem notMem_cartierSupport_of_coheight_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (A : X.CartierDivisor) {x : X} (hx : Order.coheight x = 0) :
    x ∉ cartierSupport A := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le (by simp [hx])
  have : IsArtinianRing (X.presheaf.stalk x) := isArtinianRing_iff_krullDimLE_zero.mpr this
  exact notMem_cartierSupport_of_isArtinianRing A x

/-- Every Cartier divisor on a Noetherian integral scheme has a Weil divisor. -/
private theorem exists_isWeilDivisorOfCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] (A : X.CartierDivisor) :
    ∃ w : Divisor X, IsWeilDivisorOfCartier A w := by
  have hfin := MMP.Mori.finite_setOf_genericPoint_mem (isClosed_cartierSupport A)
    (fun s hs h0 => notMem_cartierSupport_of_coheight_eq_zero A h0 hs)
  refine ⟨Finsupp.ofSupportFinite (fun P => primeDivisorOrder P A) (hfin.subset fun P hP => ?_),
    fun P => ?_⟩
  · by_contra h
    have hg : (primeDivisorSubvariety P).genericPoint = P.genericPoint := rfl
    refine hP ((isOrderAlong_primeDivisorOrder A P).eq_zero_of_not_subset fun h' => h ?_)
    change P.genericPoint ∈ cartierSupport A
    rw [← hg]
    exact genericPoint_mem_cartierSupport_iff.mpr h'
  · rw [MMP.Mori.DivisorWithCoeffs.coeff_apply, Finsupp.ofSupportFinite_coe]
    exact isOrderAlong_primeDivisorOrder A P

/-- The Weil divisor of the realization of `q • C`, for a `ℚ`-Cartier divisor `C` with Weil
`ℚ`-divisor `D`, is `q • D`. -/
private theorem coeff_eq_mul_of_isWeilDivisorOfCartier_realization {X : Scheme.{0}}
    [IsLocallyNoetherian X] {D : QDivisor X} {C : KCartierDivisor ℚ X}
    (hC : ∀ P : MMP.Mori.PrimeDivisor X,
      D.coeff P = C.sum fun E c => c * (primeDivisorOrder P E : ℚ)) {q : ℕ}
    (h : ∀ E, ∃ n : ℤ, ((q : ℚ) • C) E = n) {B : Divisor X}
    (hB : IsWeilDivisorOfCartier (KCartierDivisor.realization ((q : ℚ) • C) h) B)
    (P : MMP.Mori.PrimeDivisor X) : (B.coeff P : ℚ) = q * D.coeff P := by
  classical
  have hc : ∀ E, ((Classical.choose (h E) : ℤ) : ℚ) = ((q : ℚ) • C) E := fun E =>
    (Classical.choose_spec (h E)).symm
  rw [← (hB P).primeDivisorOrder_eq, KCartierDivisor.realization, Finsupp.sum, map_sum,
    Int.cast_sum, hC P, Finsupp.sum, Finset.mul_sum]
  have hz : ∀ E ∈ C.support, E ∉ ((q : ℚ) • C).support →
      (q : ℚ) * (C E * (primeDivisorOrder P E : ℚ)) = 0 := fun E _ hE => by
    rw [Finsupp.notMem_support_iff, Finsupp.smul_apply, smul_eq_mul] at hE
    rw [← mul_assoc, hE, zero_mul]
  rw [← Finset.sum_subset (Finsupp.support_smul (b := (q : ℚ)) (g := C)) hz]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul, hc, Finsupp.smul_apply, smul_eq_mul, mul_assoc]

/-- `KCartierDivisor.realization` depends only on the divisor. -/
private theorem realization_congr {X : Scheme.{0}} {c c' : KCartierDivisor ℚ X}
    (e : c = c') (h : ∀ D, ∃ n : ℤ, c D = n) (h' : ∀ D, ∃ n : ℤ, c' D = n) :
    KCartierDivisor.realization c h = KCartierDivisor.realization c' h' := by
  subst e; rfl

/-- A `ℚ`-divisor `Q` with `nQ` the Weil divisor of an `f`-free Cartier divisor is semiample over
the base. -/
private theorem isRelativelySemiample_of_isRelativelyFreeCartier {X Z : Scheme.{0}}
    [IsLocallyNoetherian X] (f : X ⟶ Z) (Q : QDivisor X) (n : ℕ) (hn : 0 < n) (D' : Divisor X)
    (hQ : ∀ P, (D'.coeff P : ℚ) = n * Q.coeff P) (E : X.CartierDivisor)
    (hE : IsWeilDivisorOfCartier E D') (hfree : IsRelativelyFreeCartier f E) :
    QDivisor.IsRelativelySemiample f Q := by
  classical
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨Finsupp.single E ((n : ℚ)⁻¹), fun P => ?_, n, hn, ?_⟩
  · rw [Finsupp.sum_single_index (by simp),
      (isOrderAlong_primeDivisorOrder E P).unique (hE P), hQ P]
    field_simp
  · have hc : (n : ℚ) • Finsupp.single E ((n : ℚ)⁻¹) =
        (Finsupp.single E (1 : ℤ)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
      rw [Finsupp.smul_single, Finsupp.mapRange_single, smul_eq_mul, mul_inv_cancel₀ hn',
        Int.cast_one]
    refine ⟨fun D => ⟨(Finsupp.single E (1 : ℤ)) D, by rw [hc]; rfl⟩, ?_⟩
    rw [realization_congr hc _ (fun D => ⟨(Finsupp.single E (1 : ℤ)) D, rfl⟩),
      KCartierDivisor.realization_eq_sum, Finsupp.sum_single_index (by simp), one_smul]
    exact hfree

/-- The order of a regular function at a point of coheight one is the length of its quotient. -/
private theorem scheme_ord_algebraMap {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {z : X} (hz : Order.coheight z = 1) {a : X.presheaf.stalk z} (ha : a ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField a) z = (Ring.ord _ a).toNat := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (X.presheaf.stalk z) X.functionField a ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  rw [Scheme.ord_eq_iff hz hne]
  unfold Scheme.ordHom
  rw [Ring.ordFrac_eq_ord _ ha]
  have hnzd : a ∈ nonZeroDivisors _ := mem_nonZeroDivisors_of_ne_zero ha
  exact Ring.ordMonoidWithZeroHom_eq_coe (R := X.presheaf.stalk z) hnzd
    (ENat.natCast_toNat (Ring.ord_ne_top hnzd)).symm

/-- An integral scheme is its own unique irreducible component. -/
private theorem univ_mem_irreducibleComponents (X : Scheme.{0}) [IsIntegral X] :
    (Set.univ : Set X) ∈ irreducibleComponents X := by
  rw [irreducibleComponents_eq_singleton]; rfl

private theorem specializes_genericPoint {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem genericPoint_specializes {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

/-- A rational function `φ ∈ K(Y)`, read in every factor of `K(Y) = ∏_Z 𝒪_{Y,η_Z}`. -/
private noncomputable def toRationalFunctions {Y : Scheme.{0}} [IsIntegral Y] :
    Y.functionField →+* RationalFunctions Y :=
  RingHom.pi fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

private theorem stalkSpecializes_toRationalFunctions {Y : Scheme.{0}} [IsIntegral Y]
    (Z : irreducibleComponents Y) (φ : Y.functionField) :
    (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom
      (toRationalFunctions φ Z) = φ := by
  change (Y.presheaf.stalkSpecializes _).hom ((Y.presheaf.stalkSpecializes _).hom φ) = φ
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- `v_P` on the factor `𝒪_{Y,η}` of `K(Y)` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y P.component)) :
    P.valuation s = (P.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes P.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- The order along `P` of the unit of `K(Y)` defined by `φ ≠ 0` is `ord_{η_P}(φ)`. -/
private theorem ord_toRationalFunctions {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (P : MMP.Mori.PrimeDivisor Y) {φ : Y.functionField}
    (hφ : φ ≠ 0) (ψ : (RationalFunctions Y)ˣ) (hψ : (ψ : RationalFunctions Y) =
      toRationalFunctions φ) : P.ord ψ = Scheme.ord φ P.genericPoint := by
  have h2 := valuation_eq_inv_divisorialValuation P ((ψ : RationalFunctions Y) P.component)
  rw [hψ, stalkSpecializes_toRationalFunctions, ← hψ, P.valuation_component,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hφ, ← WithZero.exp_neg,
    neg_neg] at h2
  exact WithZero.exp_injective h2

/-- A Cartier Weil divisor on a normal integral Noetherian scheme is the Weil divisor of a
Cartier divisor. -/
private theorem exists_isWeilDivisorOfCartier_of_isCartier {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {L : Divisor X} (hL : L.IsCartier) :
    ∃ E : X.CartierDivisor, IsWeilDivisorOfCartier E L := by
  classical
  have : IsNoetherian X := ⟨⟩
  have := hL.isInvertibleModule_divisorialSheaf
  obtain ⟨E₀, ⟨e₀⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier E₀
  obtain ⟨e₁⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (e₀ ≪≫ e₁)
  -- `φ` as a rational function `r₀` on the integral scheme `X`
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, univ_mem_irreducibleComponents X⟩⟩
  set r₀ : X.functionField := (X.presheaf.stalkSpecializes (genericPoint_specializes Z₀)).hom
    ((φ : RationalFunctions X) Z₀) with hr₀
  have hr : toRationalFunctions r₀ = (φ : RationalFunctions X) := by
    funext Z
    have hmem : ∀ W : irreducibleComponents X, (W : Set X) = Set.univ := fun W => by
      have h1 : (W : Set X) ∈ ({Set.univ} : Set (Set X)) := by
        rw [← irreducibleComponents_eq_singleton]; exact W.2
      exact h1
    have hZ : Z₀ = Z := Subtype.ext ((hmem Z₀).trans (hmem Z).symm)
    subst hZ
    change (X.presheaf.stalkSpecializes _).hom ((X.presheaf.stalkSpecializes _).hom _) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hr0 : r₀ ≠ 0 := by
    intro h0
    have : Nontrivial (RationalFunctions X) := Pi.nontrivial_at Z₀
    rw [h0, map_zero] at hr
    exact φ.ne_zero hr.symm
  have hordφ : ∀ Q : MMP.Mori.PrimeDivisor X, Q.ord φ = Scheme.ord r₀ Q.genericPoint :=
    fun Q => ord_toRationalFunctions Q hr0 φ hr.symm
  -- the principal Cartier divisor of `r₀`
  set c : (X.totalQuotientSheaf.obj.obj (Opposite.op ⊤))ˣ :=
    Units.map (MMP.CartierDivisorSheaf.ofFunctionField (X := X) ⊤).toMonoidHom
      (Units.mk0 r₀ hr0) with hc
  set Pc := MMP.Intersection.principalDivisor c with hPc
  have hPord : ∀ Q : MMP.Mori.PrimeDivisor X,
      primeDivisorOrder Q Pc = Scheme.ord r₀ Q.genericPoint := by
    intro Q
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (X.presheaf.stalk Q.genericPoint)) r₀
    have hbK : algebraMap _ X.functionField (b : X.presheaf.stalk Q.genericPoint) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    have hb0 : (b : X.presheaf.stalk Q.genericPoint) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hab
      exact mul_ne_zero hr0 hbK hab
    have hloc : IsLocalEquationAt Pc Q.genericPoint
        (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _)) :=
      ⟨⊤, trivial, c, isLocalEquationOn_principalDivisor c, rfl⟩
    have hfrac : IsFraction (X.totalQuotientSheaf.presheaf.germ ⊤ Q.genericPoint trivial (c : _))
        a b := by
      refine ⟨isUnit_stalkToTotalQuotient_of_mem_nonZeroDivisors b.2, ?_⟩
      apply (totalQuotientStalkToFunctionField_bijective Q.genericPoint).1
      rw [map_mul, totalQuotientStalkToFunctionField_stalkToTotalQuotient,
        totalQuotientStalkToFunctionField_stalkToTotalQuotient]
      erw [MMP.CartierDivisorSheaf.totalQuotientStalkToFunctionField_germ_top_ofFunctionField]
      rw [mul_comm]
      exact hab
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (primeDivisorSubvariety Q).genericPoint) :=
      krullDimLE_of_coheight_le Q.coheight_genericPoint.le
    have hO := isOrderAlong_of_isFraction (V := primeDivisorSubvariety Q) hloc
      (mem_nonZeroDivisors_of_ne_zero ha0) b.2 hfrac
    rw [hO.primeDivisorOrder_eq]
    have h1 := Scheme.ord_mul (x := Q.genericPoint) hr0 hbK
    rw [hab, scheme_ord_algebraMap Q.coheight_genericPoint ha0,
      scheme_ord_algebraMap Q.coheight_genericPoint hb0] at h1
    change ((Ring.ord _ a).toNat : ℤ) -
      ((Ring.ord _ (b : X.presheaf.stalk Q.genericPoint)).toNat : ℤ) = _
    linarith
  refine ⟨E₀ + Pc, fun Q => ?_⟩
  have h := isOrderAlong_primeDivisorOrder (E₀ + Pc) Q
  have e : primeDivisorOrder Q (E₀ + Pc) = L.coeff Q := by
    have hLQ := congrArg (fun D : Divisor X => D.coeff Q) hφ
    simp only [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor] at hLQ
    rw [map_add, (hw Q).primeDivisorOrder_eq, hPord, ← hordφ]
    omega
  rwa [e] at h

/-- A `ℚ`-divisor with a relatively free Cartier multiple is relatively semiample. -/
private theorem isRelativelySemiample_of_isRelativelyFreeDivisor {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    (D : QDivisor X)
    (h : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsCartier ∧
      IsRelativelyFreeDivisor f L) :
    QDivisor.IsRelativelySemiample f D := by
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ := h
  obtain ⟨E, hE⟩ := exists_isWeilDivisorOfCartier_of_isCartier hLc
  obtain ⟨e⟩ := hE.nonempty_sheaf_iso_divisorialSheaf
  refine isRelativelySemiample_of_isRelativelyFreeCartier f D m hm L (fun P => ?_) E hE
    (epi_counit_of_iso f e hfree)
  have := congrArg (fun Q : QDivisor X => Q.coeff P) hL
  simpa [zsmul_eq_mul] using this

/-- A relatively semiample `ℚ`-divisor has a relatively free Cartier multiple. -/
private theorem exists_isRelativelyFreeDivisor_of_isRelativelySemiample {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    (D : QDivisor X) (h : QDivisor.IsRelativelySemiample f D) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsCartier ∧
      IsRelativelyFreeDivisor f L := by
  classical
  have : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := h
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier
    (KCartierDivisor.realization ((q : ℚ) • C) hint)
  refine ⟨q, hq, w, ?_, hw.isCartier, ?_⟩
  · ext P
    rw [Divisor.coeff_toQDivisor, coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hw P]
    simp [DivisorWithCoeffs.coeff_apply]
  · obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
    exact epi_counit_of_iso f e.symm hfree

end Conversion

/-! ### Descent along a finite morphism of the base -/

/-- **The orders of a regular function.** A regular function `a` on `V` whose germ at `x` is a
unit is a unit `ψ` of `K(X)` with `v_P(ψ) ≥ 0` along every prime divisor meeting `V`,
`v_P(ψ) ≥ 1` along those whose generic point is a zero of `a`, and `v_P(ψ) = 0` along those
meeting the nonvanishing locus of `a`. -/
private theorem exists_unit_ord_of_section {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {V : X.Opens} (a : Γ(X, V)) {x : X} (hx : x ∈ X.basicOpen a) :
    ∃ ψ : (RationalFunctions X)ˣ,
      (∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ V → 0 ≤ P.ord ψ) ∧
      (∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ V → P.genericPoint ∉ X.basicOpen a →
        1 ≤ P.ord ψ) ∧
      (∀ P : MMP.Mori.PrimeDivisor X, ∀ y ∈ P.support, y ∈ X.basicOpen a → P.ord ψ = 0) := by
  have hxV : x ∈ V := X.basicOpen_le a hx
  have hmemZ : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ V := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
    exact ((genericPoint_spec X).specializes trivial).mem_open V.isOpen hxV
  have hux : IsUnit ((X.presheaf.germ V x hxV).hom a) := (X.mem_basicOpen a x hxV).mp hx
  have hunitZ : ∀ Z : irreducibleComponents X,
      IsUnit ((X.presheaf.germ V (componentGenericPoint X Z) (hmemZ Z)).hom a) := fun Z => by
    have hsp : componentGenericPoint X Z ⤳ x := by
      rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
      exact (genericPoint_spec X).specializes trivial
    rw [← TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxV hsp]
    exact hux.map _
  let ψ : (RationalFunctions X)ˣ :=
    (RationalFunctions.unitsEquiv X).symm fun Z => (hunitZ Z).unit
  have hψ : ∀ Z, (ψ : RationalFunctions X) Z =
      (X.presheaf.germ V (componentGenericPoint X Z) (hmemZ Z)).hom a := fun Z => rfl
  have hcomp : ∀ (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ V),
      (ψ : RationalFunctions X) P.component =
        P.toComponent.hom ((X.presheaf.germ V P.genericPoint hP).hom a) := fun P hP => by
    rw [hψ]
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _).symm
  have hne : ∀ (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ V),
      (X.presheaf.germ V P.genericPoint hP).hom a ≠ 0 := fun P hP h0 => by
    have h1 := hcomp P hP
    rw [h0, map_zero, hψ] at h1
    exact (hunitZ P.component).ne_zero h1
  refine ⟨ψ, fun P hP => ?_, fun P hP hPa => ?_, fun P y hy hya => ?_⟩
  · have h1 := P.valuation_component ψ
    rw [hcomp P hP] at h1
    have h2 := P.one_le_valuation_toComponent (hne P hP)
    rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    exact h2
  · set β := (X.presheaf.germ V P.genericPoint hP).hom a with hβdef
    have hβ : β ∈ IsLocalRing.maximalIdeal P.localRing := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hPa ((X.mem_basicOpen a P.genericPoint hP).mpr hu)
    have := P.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton'] at hβ
    obtain ⟨γ, hγ⟩ := hβ
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      exact hne P hP (by rw [← hβdef, ← hγ, zero_mul])
    have h1 := P.valuation_component ψ
    rw [hcomp P hP, ← hβdef, ← hγ, map_mul, map_mul,
      P.valuation_toComponent_of_irreducible hϖ] at h1
    have h2 := P.one_le_valuation_toComponent hγ0
    have h3 : WithZero.exp (1 : ℤ) ≤ WithZero.exp (P.ord ψ) := by
      rw [← h1]
      calc WithZero.exp (1 : ℤ) = 1 * WithZero.exp 1 := (one_mul _).symm
        _ ≤ P.valuation (P.toComponent.hom γ) * WithZero.exp 1 := by gcongr
    exact WithZero.exp_le_exp.mp h3
  · have hyP : P.genericPoint ⤳ y := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
      exact specializes_iff_mem_closure.mpr hy
    have hPa : P.genericPoint ∈ X.basicOpen a := hyP.mem_open (X.basicOpen a).isOpen hya
    have hP : P.genericPoint ∈ V := X.basicOpen_le a hPa
    exact P.ord_eq_zero_of_isUnit ((X.mem_basicOpen a P.genericPoint hP).mp hPa)
      (hcomp P hP).symm

/-- **Relative freeness descends along a finite morphism of the base.** If `L` is a Cartier
divisor on `X` which is relatively free over `W` for `h : X ⟶ W`, and `κ : W ⟶ Z` is finite,
then `L` is relatively free over `Z`. Near `x`, a generating section `ψ` over `h⁻¹U'` may have
poles along prime divisors of `X` lying over `κ⁻¹V ∖ U'`, `V` an affine neighbourhood of
`κ(h(x))`; multiplying by a high power of a function on the affine `κ⁻¹V` vanishing on
`κ⁻¹V ∖ U'` and not at `h(x)` removes them. -/
private theorem isRelativelyFreeDivisor_comp_of_isFinite {X W Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (h : X ⟶ W)
    (κ : W ⟶ Z) [IsFinite κ] {L : Divisor X} (hL : L.IsCartier)
    (hfree : IsRelativelyFreeDivisor h L) : IsRelativelyFreeDivisor (h ≫ κ) L := by
  classical
  refine isRelativelyFreeDivisor_of_forall_exists (h ≫ κ) fun x => ?_
  obtain ⟨U', hxU', ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree h hL hfree x
  obtain ⟨V, hV, hzV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show κ (h x) ∈ (⊤ : Z.Opens) from trivial)
  have hW' : IsAffineOpen (κ ⁻¹ᵁ V) := hV.preimage κ
  obtain ⟨t, ht, hxt⟩ := hW'.exists_basicOpen_le (V := U') ⟨h x, hxU'⟩ (show κ (h x) ∈ V from hzV)
  have hxt' : x ∈ X.basicOpen (h.app (κ ⁻¹ᵁ V) t) := by
    rw [← Scheme.preimage_basicOpen]; exact hxt
  obtain ⟨χ, hχ0, hχ1, hχx⟩ := exists_unit_ord_of_section (h.app (κ ⁻¹ᵁ V) t) hxt'
  -- the finitely many prime divisors with a pole
  set S : Finset (MMP.Mori.PrimeDivisor X) :=
    (L + principalDivisor ψ).support.filter fun P => L.coeff P + P.ord ψ < 0
  set N : ℕ := ∑ P ∈ S, (L.coeff P + P.ord ψ).natAbs
  have hN : ∀ P ∈ S, -(L.coeff P + P.ord ψ) ≤ N := fun P hP => by
    have := Finset.single_le_sum (f := fun P => (L.coeff P + P.ord ψ).natAbs)
      (fun _ _ => Nat.zero_le _) hP
    have h' : -(L.coeff P + P.ord ψ) ≤ ((L.coeff P + P.ord ψ).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs _
    exact h'.trans (by exact_mod_cast this)
  have hmemS : ∀ P : MMP.Mori.PrimeDivisor X, L.coeff P + P.ord ψ < 0 → P ∈ S := fun P hP => by
    refine Finset.mem_filter.mpr ⟨?_, hP⟩
    rw [Finsupp.mem_support_iff]
    change (L + principalDivisor ψ).coeff P ≠ 0
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact hP.ne
  refine ⟨V, hzV, ψ * χ ^ N, fun P hP => ?_, fun P hxP => ?_⟩
  · have hPV : P.genericPoint ∈ h ⁻¹ᵁ (κ ⁻¹ᵁ V) := (P.genericPoint_mem_iff _).mpr hP
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, nsmul_eq_mul]
    by_cases hneg : L.coeff P + P.ord ψ < 0
    · have hPU' : h P.genericPoint ∉ U' := fun hU => by
        have := h1 P ((P.genericPoint_mem_iff _).mp hU)
        omega
      have hPt : P.genericPoint ∉ X.basicOpen (h.app (κ ⁻¹ᵁ V) t) := by
        rw [← Scheme.preimage_basicOpen]
        exact fun hb => hPU' (ht hb)
      have := hχ1 P hPV hPt
      have := hN P (hmemS P hneg)
      nlinarith
    · have := hχ0 P hPV
      have : (0 : ℤ) ≤ N * P.ord χ := mul_nonneg (by positivity) this
      omega
  · rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, hχx P x hxP hxt', smul_zero, add_zero]
    exact h2 P hxP

/-! ### Pull-backs of `ℚ`-Cartier `ℚ`-divisors -/

section QPullback

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y] [CompactSpace X] {f : X ⟶ Y}

/-- **One multiple determines the pull-back.** If `mB` is a Cartier divisor `D` whose pull-back
is `mB'`, then `B'` is the pull-back of `B`. -/
private theorem isPullback_of_smul {B : QDivisor Y} (hBq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    {B' : QDivisor X} {m : ℕ} (hm : 0 < m) {D : Divisor Y}
    (hD : Divisor.toQDivisor D = (m : ℤ) • B) (hDc : D.IsCartier) {D' : Divisor X}
    (hD' : Divisor.toQDivisor D' = (m : ℤ) • B')
    (hp : D.IsPullback f (fun Z hZ => hB Z (by
        rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)) D') :
    B.IsPullback f hB B' := by
  have h := QDivisor.isPullback_pullback hBq hB
  obtain ⟨D'', hD'', hp''⟩ := h m hm D hD hDc
  have hDD : D'' = D' := hp''.eq hDc hp
  have hmm : (m : ℤ) • B.pullback hBq hB = (m : ℤ) • B' := by rw [← hD'', ← hD', hDD]
  have hpb : B.pullback hBq hB = B' := by
    ext E
    have := congrArg (fun G : QDivisor X => G.coeff E) hmm
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
    exact mul_left_cancel₀ (by exact_mod_cast hm.ne') this
  exact hpb ▸ h

/-- **Additivity of the pull-back of `ℚ`-Cartier `ℚ`-divisors.** -/
private theorem isPullback_add {B₁ B₂ : QDivisor Y} (hq₁ : B₁.IsQCartier) (hq₂ : B₂.IsQCartier)
    {hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp}
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (B₁ + B₂).supp)
    {B₁' B₂' : QDivisor X} (h₁ : B₁.IsPullback f hB₁ B₁') (h₂ : B₂.IsPullback f hB₂ B₂') :
    (B₁ + B₂).IsPullback f hB (B₁' + B₂') := by
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c⟩ := hq₁.exists_pos
  obtain ⟨m₂, hm₂, D₂, hD₂, hD₂c⟩ := hq₂.exists_pos
  have hm : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  have hE₁ : Divisor.toQDivisor ((m₂ : ℤ) • D₁) = ((m₁ * m₂ : ℕ) : ℤ) • B₁ := by
    rw [map_zsmul, hD₁, smul_smul]; push_cast; rw [mul_comm]
  have hE₂ : Divisor.toQDivisor ((m₁ : ℤ) • D₂) = ((m₁ * m₂ : ℕ) : ℤ) • B₂ := by
    rw [map_zsmul, hD₂, smul_smul]; push_cast; rfl
  obtain ⟨E₁', hE₁', hp₁⟩ := h₁ _ hm _ hE₁ (hD₁c.zsmul _)
  obtain ⟨E₂', hE₂', hp₂⟩ := h₂ _ hm _ hE₂ (hD₂c.zsmul _)
  have hE : Divisor.toQDivisor ((m₂ : ℤ) • D₁ + (m₁ : ℤ) • D₂) =
      ((m₁ * m₂ : ℕ) : ℤ) • (B₁ + B₂) := by rw [map_add, hE₁, hE₂, smul_add]
  refine isPullback_of_smul (hq₁.add hq₂) hm hE ((hD₁c.zsmul _).add (hD₂c.zsmul _))
    (D' := E₁' + E₂') (by rw [map_add, hE₁', hE₂', smul_add]) ?_
  exact Divisor.IsPullback.add (hD₁c.zsmul _) (hD₂c.zsmul _) _ hp₁ hp₂

/-- **The pull-back commutes with integral multiples.** -/
private theorem isPullback_zsmul {B : QDivisor Y} (hq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp} (n : ℤ)
    (hBn : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (n • B).supp)
    {B' : QDivisor X} (h : B.IsPullback f hB B') : (n • B).IsPullback f hBn (n • B') := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  have hnq : (n • B).IsQCartier := by
    refine ⟨m, by exact_mod_cast hm.ne', n • D, ?_, hDc.zsmul n⟩
    rw [map_zsmul, hD, smul_comm]
  refine isPullback_of_smul hnq hm (D := n • D) (by rw [map_zsmul, hD, smul_comm]) (hDc.zsmul n)
    (D' := n • D') (by rw [map_zsmul, hD', smul_comm]) ?_
  exact hp.zsmul hDc n _

end QPullback

/-! ### Pull-backs of relatively nef divisors -/

section Nef

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {Y Y' : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {sY' : Y' ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) (hs : h ≫ sY = sY') [QuasiCompact sY'] [CompactSpace Y] [CompactSpace Y']
    {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve sY') (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn ℂ sY' C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn ℂ sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h hs hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_left_of_eq_true (eq_true (hC ▸ C.isProperCurve))]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {Y Y' : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {sY' : Y' ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) (hs : h ≫ sY = sY') [QuasiCompact sY'] [CompactSpace Y] [CompactSpace Y']
    {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve sY') (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn ℂ sY' C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h hs hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_right_of_eq_false (eq_false hc), map_zero]

/-- **Pull-backs of relatively nef divisors are relatively nef.** If `D` is `f`-nef and `D'` is
the pull-back of `D` along `p : V ⟶ X`, then `D'` is `(p ≫ f)`-nef: a curve `C ⊆ V` contracted
by `p ≫ f` maps to a point or to a curve contracted by `f`, and the projection formula computes
`(p^*D · C)`. -/
private theorem isRelativelyNef_of_isPullback {V X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (p : V ⟶ X) [IsProper p]
    [QuasiCompact (p ≫ sX)] (f : X ⟶ Z) {D : QDivisor X} (hD : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, p (componentGenericPoint V Z) ∉ D.supp}
    {D' : QDivisor V} (h : D.IsPullback p hB D') (hnef : D.IsRelativelyNef sX f) :
    D'.IsRelativelyNef (p ≫ sX) (p ≫ f) := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (p ≫ sX) (h.isQCartier hD)
    fun C hC => ?_
  obtain ⟨E, E', hEc, hEB, hE, hE', hp⟩ := h.exists_cartierIndex hD
  have hm := QDivisor.cartierIndex_pos hD
  have hE'c : E'.IsCartier := hp.isCartier hEc
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ (p ≫ sX) C.ι C.dim_le D' (h.isQCartier hD) hm E'
    hE'c hE', Divisor.degreeOn_congr (hp.pullback_eq hEc).symm hE'c (hEc.isCartier_pullback p hEB)]
  refine div_nonneg ?_ (by positivity)
  by_cases hc : IsProperCurve sX (p C.point)
  · let C'' : ProperCurve sX := ⟨_, hc⟩
    have : IsProper (C''.ι ≫ sX) := C''.isProper_ι_comp
    have hCf : C''.IsContractedBy f := by
      intro y hy
      have hsub : closure ({p C.point} : Set X) ⊆ p '' closure ({C.point} : Set V) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩)
          (p.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC z hz
    rw [degreeOn_pullback_eq_mul p rfl hEc hEB C C'' rfl]
    have h0 := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hD C'' hCf
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C''.ι C''.dim_le D hD hm E hEc hE] at h0
    have h1 : (0 : ℚ) ≤ (E.degreeOn ℂ sX C''.ι C''.dim_le hEc : ℚ) := by
      have hm' : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast hm
      have := mul_nonneg h0 hm'.le
      rwa [div_mul_cancel₀ _ hm'.ne'] at this
    push_cast
    exact mul_nonneg (by positivity) h1
  · rw [degreeOn_pullback_eq_zero p rfl hEc hEB C hc]
    simp

/-- A proper curve which is not contracted by `g` does not have a point as image. -/
private theorem not_exists_range_eq_singleton {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (g : X ⟶ Y) (Γ : ProperCurve sX)
    (h : ¬ Γ.IsContractedBy g) : ¬ ∃ y : Y, Set.range (Γ.ι ≫ g) = {y} := by
  rintro ⟨y, hy⟩
  refine h fun x hx => ?_
  rw [← Γ.range_ι] at hx
  obtain ⟨c, rfl⟩ := hx
  have h1 : (Γ.ι ≫ g) c ∈ Set.range (Γ.ι ≫ g) := ⟨c, rfl⟩
  have h2 : (Γ.ι ≫ g) (genericPoint Γ.scheme) ∈ Set.range (Γ.ι ≫ g) := ⟨_, rfl⟩
  rw [hy] at h1 h2
  rw [Scheme.Hom.comp_apply] at h1 h2
  rw [Γ.ι_genericPoint] at h2
  exact h1.trans h2.symm

/-- A morphism over `ℂ` which does not contract a proper curve has positive residue degree at
its generic point: `ℂ(C)` is a finite extension of the function field of the image curve. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY]
    (g : X ⟶ Y) (hg : g ≫ sY = sX)
    (Γ : ProperCurve sX) (h : ¬ Γ.IsContractedBy g) : 0 < residueFieldDegree g Γ.point := by
  have hnc := not_exists_range_eq_singleton g Γ h
  set φ := Γ.ι ≫ g with hφdef
  have hφ : φ ≫ sY = Γ.ι ≫ sX := by rw [hφdef, Category.assoc, hg]
  have : IsProper (φ ≫ sY) := hφ ▸ inferInstance
  have : IsProper φ := IsProper.of_comp _ sY
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve ℂ (φ ≫ sY) := hφ ▸ inferInstance
  have hdeg : residueFieldDegree g Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι g (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  let := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sY φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

/-- **Relative nefness descends along a proper surjective morphism.** If the pull-back `D'` of a
`ℚ`-Cartier `ℚ`-divisor `D` along a proper surjective `q : W ⟶ Y` is `(q ≫ g)`-nef, then `D` is
`g`-nef: every curve `C' ⊆ Y` contracted by `g` is the image of a curve `C ⊆ W`, contracted by
`q ≫ g`, and `(q^*D · C) = [k(C) : k(C')] (D · C')` with a positive degree. -/
private theorem isRelativelyNef_of_isPullback_of_surjective {W Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (q : W ⟶ Y) [IsProper q] [Surjective q] [QuasiCompact (q ≫ sY)] (g : Y ⟶ Z)
    {D : QDivisor Y} (hD : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ D.supp}
    {D' : QDivisor W} (h : D.IsPullback q hB D') (hnef : D'.IsRelativelyNef (q ≫ sY) (q ≫ g)) :
    D.IsRelativelyNef sY g := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := QuasiCompact.compactSpace_of_compactSpace (q ≫ sY)
  have : LocallyOfFiniteType (q ≫ sY) := inferInstance
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sY hD fun C' hC' => ?_
  obtain ⟨C, hCp, hCimg⟩ := ProperCurve.exists_map_eq (q ≫ sY) sY q rfl C'
  have hCc : C.IsContractedBy (q ≫ g) := by
    intro x hx
    have hqx : q x ∈ closure ({C'.point} : Set Y) := hCimg ▸ ⟨x, hx, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hC' _ hqx, ← hCp]
  have hnc : ¬ C.IsContractedBy q := by
    intro hcq
    have hcl : closure ({C'.point} : Set Y) = {C'.point} := by
      rw [← hCimg]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Set.mem_singleton_iff, hcq x hx, hCp]
      · rintro rfl
        exact ⟨C.point, subset_closure rfl, hCp⟩
    have h1 := C'.dim_eq
    have hr : Set.range C'.ι = {C'.point} := by rw [ProperCurve.range_ι, hcl]
    have : Subsingleton C'.scheme := ⟨fun a b => by
      apply C'.ι.isClosedEmbedding.injective
      have ha : C'.ι a ∈ Set.range C'.ι := ⟨a, rfl⟩
      have hb : C'.ι b ∈ Set.range C'.ι := ⟨b, rfl⟩
      rw [hr] at ha hb
      exact ha.trans hb.symm⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C'.scheme
    rw [h1] at h0
    exact absurd h0 (by decide)
  have hpos := residueFieldDegree_pos_of_not_isContractedBy q rfl C hnc
  obtain ⟨E, E', hEc, hEB, hE, hE', hp⟩ := h.exists_cartierIndex hD
  have hm := QDivisor.cartierIndex_pos hD
  have hE'c : E'.IsCartier := hp.isCartier hEc
  have h0 := QDivisor.IsRelativelyNef.intersectionNumber_nonneg (q ≫ sY) hnef (h.isQCartier hD) C
    hCc
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ (q ≫ sY) C.ι C.dim_le D' (h.isQCartier hD) hm E'
    hE'c hE', Divisor.degreeOn_congr (hp.pullback_eq hEc).symm hE'c
      (hEc.isCartier_pullback q hEB), degreeOn_pullback_eq_mul q rfl hEc hEB C C' hCp.symm] at h0
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sY C'.ι C'.dim_le D hD hm E hEc hE]
  have hm' : (0 : ℚ) < D.cartierIndex hD := by exact_mod_cast hm
  have h1 : (0 : ℚ) ≤
      ((residueFieldDegree q C.point : ℤ) * E.degreeOn ℂ sY C'.ι C'.dim_le hEc : ℤ) := by
    have := mul_nonneg h0 hm'.le
    rw [div_mul_cancel₀ _ hm'.ne'] at this
    exact_mod_cast this
  have hpos' : (0 : ℚ) < (residueFieldDegree q C.point : ℚ) := by exact_mod_cast hpos
  push_cast at h1
  exact div_nonneg (nonneg_of_mul_nonneg_right (by linarith) hpos') hm'.le

end Nef

/-! ### Passing to a crepant dlt modification -/

/-- A dominant morphism of integral schemes of finite type over `ℂ` inducing an isomorphism of
function fields preserves dimension. -/
private theorem topologicalKrullDim_eq_of_bijective {X V : Scheme.{0}} [IsIntegral X]
    [IsIntegral V] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (p : V ⟶ X) [IsDominant p]
    [LocallyOfFiniteType (p ≫ sX)] (hbij : Function.Bijective (functionFieldMap p)) :
    topologicalKrullDim V = topologicalKrullDim X := by
  have hT := toENat_trdeg_functionField (sX := sX)
  have hC := toENat_trdeg_functionField (sX := p ≫ sX)
  rw [← hT, ← hC]
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have h' := trdeg_add_eq ℂ X.functionField (A := V.functionField)
  have : Algebra.IsAlgebraic X.functionField V.functionField := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hbij.2 x
    exact isAlgebraic_algebraMap a⟩
  rw [← h', trdeg_eq_zero (R := X.functionField) (A := V.functionField), add_zero]

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [LocallyOfFiniteType sX] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ X)
    [IsDominant f] (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Discrepancies of a log canonical pair are at least `-1`**, for every divisor `(Y, f, E)`
over `X` with `f` not necessarily proper: replace `f` by a proper model with the same valuation,
whose log discrepancy is `1 + a`. -/
private theorem neg_one_le_of_isLogCanonicalPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} (hP : IsPairWith sX n K Δ)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX Δ) {D : DivisorOver ℂ sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  have : CompactSpace X := haveI := hP.1.1.toQuasiCompact
    QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hP.1 D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    E.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hE
  have h1 := hlc.2.2 n _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')

/-- A log discrepancy `A(E, X, Δ)` of a pair, at any index, is `1 + a(E, X, Δ)` for the
Kollár–Mori discrepancy computed with a given canonical divisor `K`. -/
private theorem exists_isDiscrepancy_of_isLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n n' : ℕ} {K : Divisor X} {Δ : QDivisor X} (hP : MMP.Mori.IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {D : DivisorOver ℂ sX} {b : ℝ}
    (hb : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor Δ) D b) :
    ∃ a : ℚ, IsDiscrepancy sX n K Δ D a ∧ b = 1 + a := by
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hb).symm.trans
      hK.topologicalKrullDim_eq
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨a, ha, ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha b).mp hb).2⟩

/-- The pull-back predicate only depends on the divisor, not on the proof of `(∗)`. -/
private theorem isPullback_congr {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B₁ B₂ : QDivisor Y} (h : B₁ = B₂)
    {hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp}
    {B₁' B₂' : QDivisor X} (h' : B₁' = B₂') (hp : B₁.IsPullback f hB₁ B₁') :
    B₂.IsPullback f hB₂ B₂' := by
  subst h h'
  exact hp

/-- **A compatible canonical divisor on a birational model.** For a proper birational morphism
`p : V ⟶ X` of normal complex varieties and a canonical divisor `K = div(ω)` of `X`, the divisor
`K_V = div(p^*ω)` is a canonical divisor of `V` with `p_* K_V = K`. -/
private theorem exists_compatible_canonicalDivisor {X V : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hXn : IsNormalVariety ℂ sX) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] (p : V ⟶ X) [IsProper p] (hp : IsBirationalMorphism p)
    (hVn : IsNormalVariety ℂ (p ≫ sX)) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    haveI : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType (p ≫ sX) := hVn.1.toLocallyOfFiniteType
    haveI : IsDominant p := hp.isDominant
    ∃ KV : Divisor V, KV.IsCanonicalDivisor (p ≫ sX) n ∧
      (∃ ω : RationalPluriForms sX n 1, ω ≠ 0 ∧ divisorOfForm ω = K ∧
        divisorOfForm (pullbackRationalPluriForms sX p ω) = KV) ∧
      RationalMap.transformDivisor (X := V) p.toRationalMap KV = K := by
  have : LocallyOfFiniteType sX := hXn.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (p ≫ sX) := hVn.1.toLocallyOfFiniteType
  have : IsDominant p := hp.isDominant
  have : AlgebraicGeometry.IsVariety ℂ sX := hXn.1
  have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hVn.1
  have hbij := hp.functionFieldMap_bijective
  have hX3 := hK.topologicalKrullDim_eq
  have hV3 : topologicalKrullDim V = n := by
    rw [topologicalKrullDim_eq_of_bijective sX p hbij, hX3]
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hK
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hX3
  have hτ0 := pullbackRationalPluriForms_ne_zero p hbij hd hω0
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor (p ≫ sX) hVn hV3
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hVn hK₀ hτ0
  rw [one_zsmul] at hlin
  have hωK : divisorOfForm ω = K := by
    ext Γ
    exact hω Γ
  refine ⟨_, hK₀.of_linearlyEquivalent hlin, ⟨ω, hω0, hωK, rfl⟩, ?_⟩
  ext P
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hXn hVn hp P
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, htr, ← hωK]
  have := hiso
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso p hbij hd E P heq ω

/-- The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective. -/
private theorem nonneg_of_isPullback {X V : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] {p : V ⟶ X} {A : QDivisor X}
    (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents V, p (componentGenericPoint V Z) ∉ A.supp}
    {AV : QDivisor V} (h : A.IsPullback p hB AV) : 0 ≤ AV := by
  intro P
  obtain ⟨E, E', hEc, hEB, hE, hE', hp'⟩ := h.exists_cartierIndex hAq
  have hm := QDivisor.cartierIndex_pos hAq
  have hE0 : ∀ Q : MMP.Mori.PrimeDivisor X, (Q.support ∩ (⊤ : X.Opens)).Nonempty →
      0 ≤ E.coeff Q := fun Q _ => by
    have h1 := congrArg (fun G : QDivisor X => G.coeff Q) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
    have h2 : (0 : ℚ) ≤ A.coeff Q := hA0 Q
    have : (0 : ℚ) ≤ (E.coeff Q : ℚ) := by rw [h1]; positivity
    exact_mod_cast this
  have h3 := coeff_nonneg_of_isPullback_of_isEffectiveOn hEc hE0 hp' P
    ((P.genericPoint_mem_iff _).mp trivial)
  have h4 := congrArg (fun G : QDivisor V => G.coeff P) hE'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h4
  have h5 : (0 : ℚ) ≤ (E'.coeff P : ℚ) := by exact_mod_cast h3
  rw [h4] at h5
  have hm' : (0 : ℚ) < (A.cartierIndex hAq : ℕ) := by exact_mod_cast hm
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm')).mp h5

/-- A `ℚ`-divisor `ℚ`-linearly equivalent to a `ℚ`-Cartier one is `ℚ`-Cartier. -/
private theorem isQCartier_of_qLinearlyEquivalent {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D G : QDivisor X}
    (hD : D.IsQCartier) (h : D.QLinearlyEquivalent G) : G.IsQCartier := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  obtain ⟨c, hc, E, hE, hEc⟩ := hD.exists_pos
  refine ⟨((c * m : ℕ) : ℤ), by positivity, (m : ℤ) • E - (c : ℤ) • principalDivisor φ, ?_,
    (hEc.zsmul _).sub ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩
  rw [map_sub, map_zsmul, map_zsmul, hE, ← hφ, smul_smul, smul_smul, smul_sub]
  push_cast
  rw [mul_comm (m : ℤ) (c : ℤ)]
  abel

/-- **`ℚ`-linear equivalence pulls back.** If `D, G` are `ℚ`-Cartier with pull-backs `D', G'`
along a dominant `p` and `m(D - G) = div φ`, then `m(D' - G') = div(p^*φ)`. -/
private theorem qLinearlyEquivalent_pullback {X V : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] (p : V ⟶ X) [IsDominant p] {D G : QDivisor X}
    (hD : D.IsQCartier) (hG : G.IsQCartier)
    {hBD : ∀ Z : irreducibleComponents V, p (componentGenericPoint V Z) ∉ D.supp}
    {hBG : ∀ Z : irreducibleComponents V, p (componentGenericPoint V Z) ∉ G.supp}
    {D' G' : QDivisor V} (hpD : D.IsPullback p hBD D') (hpG : G.IsPullback p hBG G') {m : ℕ}
    (φ : (RationalFunctions X)ˣ)
    (hφ : (m : ℤ) • (D - G) = Divisor.toQDivisor (principalDivisor φ)) :
    (m : ℤ) • (D' - G') = Divisor.toQDivisor (principalDivisor (pullbackRationalFunction p φ
      (map_componentGenericPoint_notMem_supp_of_isDominant p _))) := by
  have hφc := Divisor.isCartier_principalDivisor φ
  have hnGq : ((-1 : ℤ) • G).IsQCartier := by
    obtain ⟨c, hc, E, hE, hEc⟩ := hG
    exact ⟨c, hc, -E, by rw [map_neg, hE, smul_comm, neg_one_smul], hEc.neg⟩
  have hDGq : (D + (-1 : ℤ) • G).IsQCartier := hD.add hnGq
  have h1 := isPullback_zsmul hDGq (m : ℤ)
    (map_componentGenericPoint_notMem_supp_of_isQCartier p
      (show ((m : ℤ) • (D + (-1 : ℤ) • G)).IsQCartier from
        ⟨1, one_ne_zero, principalDivisor φ, by
          rw [one_smul, ← hφ, neg_one_smul, ← sub_eq_add_neg], hφc⟩))
    (isPullback_add hD hnGq (map_componentGenericPoint_notMem_supp_of_isQCartier p hDGq)
      hpD (isPullback_zsmul hG (-1 : ℤ)
        (map_componentGenericPoint_notMem_supp_of_isQCartier p hnGq) hpG))
  have h2 := QDivisor.isPullback_toQDivisor hφc
    (map_componentGenericPoint_notMem_supp_of_isQCartier p (QDivisor.isQCartier_toQDivisor hφc))
    (Divisor.isPullback_principalDivisor φ
      (map_componentGenericPoint_notMem_supp_of_isDominant p _))
  have h1' := isPullback_congr (show (m : ℤ) • (D + (-1 : ℤ) • G) =
      Divisor.toQDivisor (principalDivisor φ) by rw [← hφ, neg_one_smul, ← sub_eq_add_neg])
    (show (m : ℤ) • (D' + (-1 : ℤ) • G') = (m : ℤ) • (D' - G') by
        rw [neg_one_smul, ← sub_eq_add_neg]) h1
    (hB₂ := map_componentGenericPoint_notMem_supp_of_isQCartier p
      (QDivisor.isQCartier_toQDivisor hφc))
  exact ((QDivisor.isQCartier_toQDivisor hφc).existsUnique_isPullback _).unique h1' h2

/-- A divisor whose sheaf is the pull-back of an invertible module is Cartier. -/
private theorem isCartier_of_iso_pullback {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X] [CompactSpace X] (f : X ⟶ Z) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M] {L : Divisor X}
    (e : L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M) : L.IsCartier := fun x => by
  obtain ⟨U, hU, ψ, hψ⟩ := exists_isLocalEquation_preimage_of_iso_pullback f M e (f x)
  exact ⟨f ⁻¹ᵁ U, hU, ψ, hψ⟩

/-- **Transport to a `ℚ`-factorial dlt modification.** Let `p : V ⟶ X` be a projective crepant
`ℚ`-factorial dlt modification of `(X, B)`
(`MMP.Fourfold.ProjectiveFloorProgramInputs.exists_crepant_dltModification`, with the inputs
`P(3)`). Then `K_V + Δ_V = p^*(K_X + B)`, and the pull-backs of `A` and `G` to `V` carry the
complement: `K_V + Δ_V` is `(p ≫ f)`-nef, `A_V = p^*A ≥ 0` is `ℚ`-Cartier, `(V, Δ_V + A_V)` is
lc with coefficients at most one, and `K_V + Δ_V + A_V ∼_ℚ G_V` with `𝒪_V(mG_V) ≅ (p ≫ f)^*M`. -/
private theorem transport {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hX3 : topologicalKrullDim X = 3)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3) {B : QDivisor X}
    (hlcB : MMP.Intersection.IsLogCanonicalPair sX B) (f : X ⟶ Z)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (_ : CompactSpace V) (p : V ⟶ X) (_ : IsProper p) (_ : Surjective p)
      (hp : IsBirationalMorphism p) (hVn : IsNormalVariety ℂ (p ≫ sX)) (KV : Divisor V)
      (ΔV AV GV : QDivisor V),
      Mori.IsProjectiveVariety ℂ (p ≫ sX) ∧ IsQFactorial (p ≫ sX) ∧ topologicalKrullDim V = 3 ∧
      KV.IsCanonicalDivisor (p ≫ sX) 3 ∧ 0 ≤ ΔV ∧ Mori.IsDltPair (p ≫ sX) 3 KV ΔV ∧
      MMP.Intersection.IsDltPair (p ≫ sX) ΔV ∧
      (Divisor.toQDivisor KV + ΔV).IsRelativelyNef (p ≫ sX) (p ≫ f) ∧ 0 ≤ AV ∧
      AV.IsQCartier ∧ IsLcPair (p ≫ sX) 3 KV (ΔV + AV) ∧
      MMP.Intersection.IsLogCanonicalPair (p ≫ sX) (ΔV + AV) ∧
      (Divisor.toQDivisor KV + ΔV + AV).QLinearlyEquivalent GV ∧
      (∃ m : ℕ, 0 < m ∧ ∃ L : Divisor V, Divisor.toQDivisor L = (m : ℤ) • GV ∧
        Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (p ≫ f)).obj M)) ∧
      (∃ hB, (Divisor.toQDivisor K + B).IsPullback p hB (Divisor.toQDivisor KV + ΔV)) ∧
      IsCrepantBoundary sX 3 K B p hVn hp ΔV ∧
      (∀ E : MMP.Mori.PrimeDivisor V, RationalMap.IsExceptional (X := V) p.toRationalMap E →
        MMP.Intersection.IsLogDiscrepancy sX 3 (QDivisor.toRDivisor B)
          (⟨V, p, hVn, hp, E⟩ : DivisorOver ℂ sX) 0 ∧ ΔV.coeff E = 1) ∧
      (letI := functionFieldMapAlgebra p; Module.Finite X.functionField V.functionField) := by
  have hXv := (Mori.isProjectiveVariety_iff ℂ sX).mp hX
  have : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  obtain ⟨V, _, _, _, p, hp, hVQ, ΔV, hpproj, hVdlt, hcrep, hexc⟩ :=
    projectiveFloorProgramInputs_three.exists_crepant_dltModification sX hX
      (by rw [hX3]; rfl) hlcB
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hVQ.1.1
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : IsDominant p := hp.isDominant
  have hVp : Mori.IsProjectiveVariety ℂ (p ≫ sX) :=
    (Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hVQ.1.1, hpproj.comp hXv.2⟩
  have hbij := hp.functionFieldMap_bijective
  have hV3 : topologicalKrullDim V = 3 := by
    rw [topologicalKrullDim_eq_of_bijective sX p hbij, hX3]
  obtain ⟨KV, hKV, hcompat, htrans⟩ := exists_compatible_canonicalDivisor hlcB.1.1 p hp hVQ.1 hK
  have hPB : MMP.Mori.IsPair sX B := hlcB.1
  obtain ⟨-, -, hB', hpb⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hPB p hVQ.1 hp hK
    hKV (Or.inl hcompat) (hcrep K hK)
  have hVdlt' : Mori.IsDltPair (p ≫ sX) 3 KV ΔV :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (p ≫ sX) hKV ΔV).mp hVdlt
  have hΔV0 : 0 ≤ ΔV := fun P => hVdlt.1.2.1 P
  have hnefV : (Divisor.toQDivisor KV + ΔV).IsRelativelyNef (p ≫ sX) (p ≫ f) :=
    isRelativelyNef_of_isPullback p f hnef.1 hpb hnef
  obtain ⟨AV, hAVpb⟩ : ∃ AV : QDivisor V,
      A.IsPullback p (map_componentGenericPoint_notMem_supp_of_isQCartier p hAq) AV :=
    ⟨_, QDivisor.isPullback_pullback hAq _⟩
  have hAV0 : 0 ≤ AV := nonneg_of_isPullback hA0 hAq hAVpb
  have hAVq : AV.IsQCartier := hAVpb.isQCartier hAq
  have hKBAq : (Divisor.toQDivisor K + B + A).IsQCartier := hnef.1.add hAq
  have hpbBA : (Divisor.toQDivisor K + (B + A)).IsPullback p
      (map_componentGenericPoint_notMem_supp_of_isQCartier p (by rw [← add_assoc]; exact hKBAq))
      (Divisor.toQDivisor KV + (ΔV + AV)) := by
    exact isPullback_congr (add_assoc _ _ _) (add_assoc _ _ _) (isPullback_add hnef.1 hAq
      (map_componentGenericPoint_notMem_supp_of_isQCartier p hKBAq) hpb hAVpb)
  obtain ⟨hpairV, hdisc⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hlc.1 p hVQ.1 hp hK hKV
    (Or.inr ⟨inferInstance, htrans, _, hpbBA⟩)
  have hPX : IsPairWith sX 3 K (B + A) :=
    ⟨hlcB.1.1, hK, by rw [← add_assoc]; exact hKBAq⟩
  have hlcVI : MMP.Intersection.IsLogCanonicalPair (p ≫ sX) (ΔV + AV) := by
    refine ⟨hpairV, fun P => add_nonneg (hΔV0 P) (hAV0 P), fun n D b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := exists_isDiscrepancy_of_isLogDiscrepancy hpairV hKV hb
    have hv := MMP.Mori.valuation_compDivisorOver p hVQ.1 hp D
    have ha' := (hdisc D (MMP.Mori.compDivisorOver p hVQ.1 hp D) hv a).mp ha
    have h1 : (-1 : ℚ) ≤ a := neg_one_le_of_isLogCanonicalPair hPX hlc ha'
    have h2 : (-1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    linarith
  have hlcV : IsLcPair (p ≫ sX) 3 KV (ΔV + AV) := by
    refine ⟨⟨hVQ.1, hKV, ?_⟩, le_discrep_iff.mpr fun D a hD ha => ?_⟩
    · rw [← add_assoc]
      have := hpbBA.isQCartier (by rw [← add_assoc]; exact hKBAq)
      rwa [← add_assoc] at this
    · have hv := MMP.Mori.valuation_compDivisorOver p hVQ.1 hp D
      have ha' := (hdisc D (MMP.Mori.compDivisorOver p hVQ.1 hp D) hv a).mp ha
      have h1 : (-1 : ℚ) ≤ a := neg_one_le_of_isLogCanonicalPair hPX hlc ha'
      have h2 : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by exact_mod_cast h1)
      simpa using h2
  obtain ⟨GV, hDGV, hGMV⟩ : ∃ GV : QDivisor V,
      (Divisor.toQDivisor KV + ΔV + AV).QLinearlyEquivalent GV ∧
      ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor V, Divisor.toQDivisor L = (m : ℤ) • GV ∧
        Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (p ≫ f)).obj M) := by
    have hGq := isQCartier_of_qLinearlyEquivalent hKBAq hDG
    obtain ⟨m, hm, φ, hφ⟩ := hDG
    set GV := QDivisor.pullback G hGq (map_componentGenericPoint_notMem_supp_of_isQCartier p hGq)
    have hGVpb : G.IsPullback p _ GV := QDivisor.isPullback_pullback hGq _
    refine ⟨GV, ⟨m, hm, _, qLinearlyEquivalent_pullback p hKBAq hGq
      (isPullback_add hnef.1 hAq (map_componentGenericPoint_notMem_supp_of_isQCartier p hKBAq)
        hpb hAVpb) hGVpb φ hφ⟩, ?_⟩
    · obtain ⟨m₀, hm₀, L, hL, ⟨e⟩⟩ := hGM
      have hLc := isCartier_of_iso_pullback f M e
      obtain ⟨LV, hLV, hpL⟩ := hGVpb m₀ hm₀ L hL hLc
      refine ⟨m₀, hm₀, LV, hLV, ⟨?_⟩⟩
      exact hpL.divisorialSheafIso (hBc := hLc) ≪≫ (Scheme.Modules.pullback p).mapIso e ≪≫
        (Scheme.Modules.pullbackComp p f).app M
  have hfin : letI := functionFieldMapAlgebra p
      Module.Finite X.functionField V.functionField := by
    let := functionFieldMapAlgebra p
    exact Module.Finite.of_surjective (Algebra.linearMap X.functionField V.functionField) hbij.2
  exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, p, inferInstance,
    inferInstance, hp, hVQ.1, KV, ΔV, AV, GV, hVp, hVQ, hV3, hKV, hΔV0, hVdlt', hVdlt, hnefV,
    hAV0, hAVq, hlcV, hlcVI, hDGV, hGMV, ⟨_, hpb⟩, hcrep K hK, hexc, hfin⟩

/-! ### Canonical divisors on crepant models and linear equivalence -/

/-- **Relative nefness is invariant under linear equivalence.** -/
private theorem isRelativelyNef_add_principalDivisor {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    {f : X ⟶ Z}
    {D : QDivisor X} (hnef : D.IsRelativelyNef sX f) (φ : (RationalFunctions X)ˣ) :
    (D + Divisor.toQDivisor (principalDivisor φ)).IsRelativelyNef sX f := by
  have hφc := Divisor.isCartier_principalDivisor φ
  have hφq := QDivisor.isQCartier_toQDivisor hφc
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX (hnef.1.add hφq)
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le D _ hnef.1 hφq]
  have h0 : (Divisor.toQDivisor (principalDivisor φ)).intersectionNumber ℂ sX C.ι C.dim_le hφq =
      0 := by
    rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le _ hφq one_pos
      (principalDivisor φ) hφc (by simp)]
    have hlin : (principalDivisor φ).LinearlyEquivalent 0 := ⟨φ, by rw [sub_zero]⟩
    have := hφc.isInvertibleModule_divisorialSheaf
    have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
    have := degreeOn_eq_of_iso ℂ sX C.ι C.dim_le hlin.divisorialSheafIso
    change (principalDivisor φ).degreeOn ℂ sX C.ι C.dim_le hφc = _ at this
    rw [show (principalDivisor φ).degreeOn ℂ sX C.ι C.dim_le hφc = 0 from
      this.trans (Divisor.degreeOn_zero' ℂ sX C.ι C.dim_le)]
    simp
  rw [h0, add_zero]
  exact QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef hnef.1 C hC

/-- Relative nefness only depends on the structure morphism through its value. -/
private theorem isRelativelyNef_congr_structure {X Z : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {s s' : X ⟶ Spec (.of ℂ)} (hss : s = s') [QuasiCompact s] [QuasiCompact s']
    {f : X ⟶ Z} {D : QDivisor X} (h : D.IsRelativelyNef s f) : D.IsRelativelyNef s' f := by
  subst hss
  exact h

/-- **Compatible canonical divisors on a common crepant model.** If `W` is a common normal model
of `(X, B)` and `(Y, B_Y)` with the same crepant boundary `Δ_W`, there are canonical divisors
`K_W`, `K'_W` of `W` with `p_* K_W = K_X`, `q_* K'_W = K_Y`, `K_W + Δ_W = p^*(K_X + B)`,
`K'_W + Δ_W = q^*(K_Y + B_Y)`, and `K'_W - K_W` principal. -/
private theorem crepant_model_setup {X Y W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    {K : Divisor X} {B : QDivisor X} (hP : MMP.Mori.IsPair sX B) (hK : K.IsCanonicalDivisor sX 3)
    {KY : Divisor Y} {BY : QDivisor Y} (hPY : MMP.Mori.IsPair sY BY)
    (hKY : KY.IsCanonicalDivisor sY 3) (p : W ⟶ X) (q : W ⟶ Y) [IsProper p] [IsProper q]
    {ΔW : QDivisor W} (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
    (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q) (hs : p ≫ sX = q ≫ sY)
    (hcX : IsCrepantBoundary sX 3 K B p hWX hp ΔW)
    (hcY : IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) :
    ∃ (KW KW' : Divisor W) (φ : (RationalFunctions W)ˣ),
      KW.IsCanonicalDivisor (p ≫ sX) 3 ∧
      RationalMap.transformDivisor (X := W) p.toRationalMap KW = K ∧
      (∃ hB, (Divisor.toQDivisor K + B).IsPullback p hB (Divisor.toQDivisor KW + ΔW)) ∧
      KW'.IsCanonicalDivisor (q ≫ sY) 3 ∧
      RationalMap.transformDivisor (X := W) q.toRationalMap KW' = KY ∧
      (∃ hB, (Divisor.toQDivisor KY + BY).IsPullback q hB (Divisor.toQDivisor KW' + ΔW)) ∧
      KW' - KW = principalDivisor φ := by
  obtain ⟨KW, hKW, -, htr⟩ := exists_compatible_canonicalDivisor hP.1 p hp hWX hK
  obtain ⟨KW', hKW', -, htr'⟩ := exists_compatible_canonicalDivisor hPY.1 q hq hWY hKY
  obtain ⟨-, -, hB1, hpb1⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hP p hWX hp hK hKW
    (Or.inr ⟨inferInstance, htr⟩) hcX
  obtain ⟨-, -, hB2, hpb2⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hPY q hWY hq hKY
    hKW' (Or.inr ⟨inferInstance, htr'⟩) hcY
  have hKW2 : KW.IsCanonicalDivisor (q ≫ sY) 3 := hs ▸ hKW
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (q ≫ sY) hWY
    hKW' hKW2
  exact ⟨KW, KW', φ, hKW, htr, ⟨hB1, hpb1⟩, hKW', htr', ⟨hB2, hpb2⟩, hφ⟩

/-! ### Relative semiampleness under pull-back and descent -/

/-- Clearing the denominator of `c`: if `D = mB`, then `num(c) D = (den(c) m)(cB)`. -/
private theorem toQDivisor_num_zsmul {X : Scheme.{0}} {B : QDivisor X} {m : ℕ} {D : Divisor X}
    (hD : Divisor.toQDivisor D = (m : ℤ) • B) (c : ℚ) :
    Divisor.toQDivisor (c.num • D) = ((c.den * m : ℕ) : ℤ) • (c • B) := by
  rw [map_zsmul, hD]
  ext E
  simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul]
  push_cast
  rw [← Rat.mul_den_eq_num c]
  ring

/-- A rational multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem isQCartier_qsmul {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hq : B.IsQCartier) (c : ℚ) : (c • B).IsQCartier := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hq.exists_pos
  exact ⟨_, by positivity, c.num • D, toQDivisor_num_zsmul hD c, hDc.zsmul _⟩

/-- The pull-back commutes with rational multiples. -/
private theorem isPullback_qsmul {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace X] {f : X ⟶ Y} {B : QDivisor Y}
    (hq : B.IsQCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp} (c : ℚ)
    (hBc : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (c • B).supp)
    {B' : QDivisor X} (h : B.IsPullback f hB B') : (c • B).IsPullback f hBc (c • B') := by
  obtain ⟨m, hm, D, hD, hDc⟩ := hq.exists_pos
  obtain ⟨D', hD', hp⟩ := h m hm D hD hDc
  exact isPullback_of_smul (isQCartier_qsmul hq c) (Nat.mul_pos c.den_pos hm)
    (toQDivisor_num_zsmul hD c) (hDc.zsmul _) (toQDivisor_num_zsmul hD' c) (hp.zsmul hDc c.num _)

/-- **Pull-backs of relatively semiample divisors are relatively semiample.** -/
private theorem isRelativelySemiample_pullback {Y Y' Z : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (e : Y' ⟶ Y) [IsDominant e]
    (g : Y ⟶ Z) {D : QDivisor Y}
    {hB : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉ D.supp}
    {D' : QDivisor Y'} (h : D.IsPullback e hB D') (hs : QDivisor.IsRelativelySemiample g D) :
    QDivisor.IsRelativelySemiample (e ≫ g) D' := by
  classical
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample g D hs
  obtain ⟨L', hL', hpL⟩ := h m hm L hL hLc
  have hL'c : L'.IsCartier := hpL.isCartier hLc
  refine isRelativelySemiample_of_isRelativelyFreeDivisor (e ≫ g) D'
    ⟨m, hm, L', hL', hL'c, isRelativelyFreeDivisor_of_forall_exists (e ≫ g) fun y => ?_⟩
  obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree g hLc hfree (e y)
  have hψ : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉
      (principalDivisor ψ).supp := map_componentGenericPoint_notMem_supp_of_isDominant e _
  set ψ' := pullbackRationalFunction e ψ hψ
  set F : Divisor Y := L + principalDivisor ψ with hF
  have hFc : F.IsCartier := hLc.add (Divisor.isCartier_principalDivisor ψ)
  have hFB : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉ F.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant e _
  have hpF : F.IsPullback e hFB (L' + principalDivisor ψ') :=
    hpL.add hLc (Divisor.isCartier_principalDivisor ψ) hFB
      (Divisor.isPullback_principalDivisor ψ hψ)
  have hcoeff : ∀ P : MMP.Mori.PrimeDivisor Y', (L' + principalDivisor ψ').coeff P =
      L'.coeff P + P.ord ψ' := fun P => by
    rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  refine ⟨U, hU, ψ', fun P hP => ?_, fun P hyP => ?_⟩
  · rw [← hcoeff]
    refine coeff_nonneg_of_isPullback_of_isEffectiveOn hFc (V := g ⁻¹ᵁ U) (fun Q hQ => ?_) hpF P hP
    rw [hF, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
    exact h1 Q hQ
  · rw [← hcoeff]
    have hyF : e y ∉ F.supp := by
      rw [DivisorWithCoeffs.mem_supp_iff]
      rintro ⟨Q, hQ, hyQ⟩
      apply hQ
      rw [hF, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
      exact h2 Q hyQ
    set N : Y.Opens := ⟨(F.supp : Set Y)ᶜ, F.supp.isClosed.isOpen_compl⟩
    have hN1 : F.IsLocalEquation N 1 := by
      rintro Q ⟨z, hzQ, hzN⟩
      rw [PrimeDivisor.ord_one]
      by_contra hne
      exact hzN (DivisorWithCoeffs.mem_supp_iff.mpr ⟨Q, hne, hzQ⟩)
    have hPN : (P.support ∩ e ⁻¹ᵁ N).Nonempty := ⟨y, hyP, hyF⟩
    rw [hpF N 1 hN1 P hPN, pullbackComponent_eq hFB hN1 _ (mem_pointComponent _) 1 (by simp),
      map_one, PrimeDivisor.ordUnit_one]

/-- **Relative semiampleness descends along a proper birational morphism.** -/
private theorem isRelativelySemiample_of_pullback {Y Y' Z : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (hY : IsNormalVariety ℂ sY)
    (e : Y' ⟶ Y) [IsProper e] [Surjective e] (hY' : IsNormalVariety ℂ (e ≫ sY))
    (hfin : letI := functionFieldMapAlgebra e; Module.Finite Y.functionField Y'.functionField)
    (g : Y ⟶ Z) {D : QDivisor Y} (hD : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉ D.supp}
    {D' : QDivisor Y'} (h : D.IsPullback e hB D')
    (hs : QDivisor.IsRelativelySemiample (e ≫ g) D') : QDivisor.IsRelativelySemiample g D := by
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample _ _ hs
  refine isRelativelySemiample_of_isRelativelyFreeDivisor g D
    (exists_isRelativelyFreeDivisor_of_pullback (e ≫ sY) sY hY' hY e rfl hfin g D hD
      ⟨m, hm, L, ?_, hLc, hfree⟩)
  rw [h.pullback_eq hD, hL]

/-! ### The complement on the pencil model -/

/-- Push-forward along a proper birational morphism of normal varieties commutes with regarding
divisors as `ℚ`-divisors. -/
private theorem transformDivisor_toQDivisor {W Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian W] [IsNormal W]
    (hY : IsNormalVariety ℂ sY) {q : W ⟶ Y} (hW : IsNormalVariety ℂ (q ≫ sY)) [IsProper q]
    (hq : IsBirationalMorphism q) (D : Divisor W) :
    RationalMap.transformDivisor (X := W) q.toRationalMap (Divisor.toQDivisor D) =
      Divisor.toQDivisor (RationalMap.transformDivisor (X := W) q.toRationalMap D) := by
  ext P
  obtain ⟨E, -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hq P
  have h1 := Divisor.coeff_toQDivisor D E
  have h2 := Divisor.coeff_toQDivisor (RationalMap.transformDivisor (X := W) q.toRationalMap D) P
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at h1 h2
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, htr, h1, h2, htr]

/-- Push-forward of an effective divisor along a proper birational morphism is effective. -/
private theorem transformDivisor_nonneg {W Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian W] [IsNormal W]
    (hY : IsNormalVariety ℂ sY) {q : W ⟶ Y} (hW : IsNormalVariety ℂ (q ≫ sY)) [IsProper q]
    (hq : IsBirationalMorphism q) {D : QDivisor W} (hD : 0 ≤ D) :
    0 ≤ RationalMap.transformDivisor (X := W) q.toRationalMap D := by
  intro P
  obtain ⟨E, -, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hq P
  rw [htr]
  exact hD E

/-- **Principal divisors push forward to principal divisors**, and every unit of `K(W)` is the
pull-back of a unit of `K(Y)`, for a proper birational morphism `q : W ⟶ Y` of normal
varieties. -/
private theorem exists_transformDivisor_principalDivisor {W Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hY : IsNormalVariety ℂ sY) {q : W ⟶ Y} (hW : IsNormalVariety ℂ (q ≫ sY)) [IsProper q]
    (hq : IsBirationalMorphism q) (ψ : (RationalFunctions W)ˣ) :
    ∃ (ψY : (RationalFunctions Y)ˣ) (hψY : ∀ Z : irreducibleComponents W,
        q (componentGenericPoint W Z) ∉ (principalDivisor ψY).supp),
      pullbackRationalFunction q ψY hψY = ψ ∧
      RationalMap.transformDivisor (X := W) q.toRationalMap (principalDivisor ψ) =
        principalDivisor ψY := by
  obtain ⟨ψY, hψY, hpb⟩ := exists_pullbackRationalFunction_eq hq ψ
  refine ⟨ψY, hψY, hpb, ?_⟩
  rw [← hpb]
  exact MMP.Positivity.transformDivisor_principalDivisor_pullback hY hW hq ψY hψY

/-- The pull-back of a unit of `K(Y)` with trivial divisor has trivial divisor. -/
private theorem principalDivisor_pullback_eq_zero {W Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] (q : W ⟶ Y)
    (ψY : (RationalFunctions Y)ˣ) (hψY : ∀ Z : irreducibleComponents W,
        q (componentGenericPoint W Z) ∉ (principalDivisor ψY).supp)
    (h0 : principalDivisor ψY = 0) :
    principalDivisor (pullbackRationalFunction q ψY hψY) = 0 := by
  have h1 := Divisor.isPullback_principalDivisor ψY hψY
  have h2 : (principalDivisor ψY).IsPullback q hψY 0 :=
    Divisor.IsPullback.of_eq h0.symm (Divisor.isPullback_zero (by rw [← h0]; exact hψY))
  exact h1.eq (Divisor.isCartier_principalDivisor ψY) h2

/-- **The discrepancy does not depend on the canonical divisor within its linear equivalence
class**: only the pair and the forms enter. -/
private theorem isDiscrepancy_of_linearlyEquivalent {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {n : ℕ}
    {K K' : Divisor X} (hK' : K'.IsCanonicalDivisor sX n) (φ : (RationalFunctions X)ˣ)
    (hφ : K' - K = principalDivisor φ) {Δ : QDivisor X} {D : DivisorOver ℂ sX} {a : ℚ}
    (h : IsDiscrepancy sX n K Δ D a) : IsDiscrepancy sX n K' Δ D a := by
  obtain ⟨hX, -, m, hm, ⟨C, hC, hCc⟩, U, hU, τ, hτ, ha⟩ := h
  refine ⟨hX, hK', m, hm, ⟨C + (m : ℤ) • principalDivisor φ, ?_,
    hCc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩, U, hU, τ, hτ, ha⟩
  rw [map_add, hC, map_zsmul, ← hφ, map_sub, ← smul_add]
  congr 1
  abel

/-- Discrepancies only depend on the structure morphism through its value. -/
private theorem isDiscrepancy_congr_structure {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {s s' : X ⟶ Spec (.of ℂ)} (hss : s = s') {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {D : DivisorOver ℂ s} {a : ℚ}
    (h : IsDiscrepancy s n K Δ D a) : IsDiscrepancy s' n K Δ (hss ▸ D) a := by
  subst hss
  exact h

/-- `m • (m⁻¹ • D) = D` for a `ℚ`-divisor `D` and `m > 0`. -/
private theorem natCast_zsmul_inv_smul {X : Scheme.{0}} {m : ℕ} (hm : 0 < m) (D : QDivisor X) :
    (m : ℤ) • ((m : ℚ)⁻¹ • D) = D := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_natCast,
    mul_inv_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

/-- **Transporting the complement to the pencil model.** On the crepant model `(Y, B_Y)`,
`A_Y = q_* p^* A` is an effective `ℚ`-Cartier complement: `(Y, B_Y + A_Y)` is lc and
`K_Y + B_Y + A_Y ∼_ℚ G_Y` with `𝒪_Y(mG_Y) ≅ g^*M`. -/
private theorem exists_complement_on_model {X Z Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] [IsIntegral Z]
    {K : Divisor X} {B : QDivisor X} (hKB : Mori.IsDltPair sX 3 K B)
    (f : X ⟶ Z) (hcon : MMP.Fourfold.IsContraction sX sZ f)
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier)
    (hlcI : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ Z)
    (KY : Divisor Y) (BY : QDivisor Y)
    (hgY : g ≫ sZ = sY) (hYdlt : Mori.IsDltPair sY 3 KY BY)
    (hW : ∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sY 3 KY BY q hWY hq ΔW) :
    ∃ AY : QDivisor Y, 0 ≤ AY ∧ AY.IsQCartier ∧
      MMP.Intersection.IsLogCanonicalPair sY (BY + AY) ∧ ∃ GY : QDivisor Y,
        (Divisor.toQDivisor KY + BY + AY).QLinearlyEquivalent GY ∧
        ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor Y, Divisor.toQDivisor L = (m : ℤ) • GY ∧
          Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj M) := by
  classical
  obtain ⟨W, p, q, ΔW, hWX, hWY, hp, hq, hpp, hqp, hpq, hcX, hcY⟩ := hW
  have hXn : IsNormalVariety ℂ sX := hKB.1.1
  have hYn : IsNormalVariety ℂ sY := hYdlt.1.1
  have : AlgebraicGeometry.IsVariety ℂ sX := hXn.1
  have : AlgebraicGeometry.IsVariety ℂ sY := hYn.1
  have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hWX.1
  have : AlgebraicGeometry.IsVariety ℂ (q ≫ sY) := hWY.1
  have : IsIntegral W := hWX.1.toIsIntegral
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  have : IsNormal W := hWX.2
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : IsProper p := isProper_of_isProjectiveMorphism p hpp
  have : IsProper q := isProper_of_isProjectiveMorphism q hqp
  have : IsDominant p := hp.isDominant
  have : IsDominant q := hq.isDominant
  have hs : p ≫ sX = q ≫ sY := by
    rw [← hcon.comp_eq, ← hgY, ← Category.assoc, hpq, Category.assoc]
  obtain ⟨KW, KW', φ, hKW, htrW, ⟨hB1, hpbX⟩, hKW', htrW', ⟨hB2, hpbY⟩, hφ⟩ :=
    crepant_model_setup hKB.1.isPair hKB.1.2.1 hYdlt.1.isPair hYdlt.1.2.1 p q hWX hWY hp hq hs
      hcX hcY
  set T := RationalMap.transformDivisor (X := W) (R := ℚ) q.toRationalMap with hT
  -- the complement on `W` and on `Y`
  have hpbA := QDivisor.isPullback_pullback (f := p) hAq
    (map_componentGenericPoint_notMem_supp_of_isQCartier p hAq)
  set AW := A.pullback hAq (map_componentGenericPoint_notMem_supp_of_isQCartier p hAq) with hAWdef
  have hAW0 : 0 ≤ AW := nonneg_of_isPullback hA hAq hpbA
  set AY : QDivisor Y := T AW with hAYdef
  have hAY0 : 0 ≤ AY := transformDivisor_nonneg hYn hWY hq hAW0
  -- the base divisor
  obtain ⟨m, hm, φ₁, hφ₁⟩ := hDG
  obtain ⟨m₀, hm₀, L, hL, ⟨e⟩⟩ := hGM
  have hLc := isCartier_of_iso_pullback f M e
  have hKBq : (Divisor.toQDivisor K + B).IsQCartier := hKB.1.2.2
  have hKBAq : (Divisor.toQDivisor K + B + A).IsQCartier := hKBq.add hAq
  have hGq : G.IsQCartier := isQCartier_of_qLinearlyEquivalent hKBAq ⟨m, hm, φ₁, hφ₁⟩
  have hpbG := QDivisor.isPullback_pullback (f := p) hGq
    (map_componentGenericPoint_notMem_supp_of_isQCartier p hGq)
  set GW := G.pullback hGq (map_componentGenericPoint_notMem_supp_of_isQCartier p hGq)
  obtain ⟨LW, hLW, hpL⟩ := hpbG m₀ hm₀ L hL hLc
  have eLW : LW.divisorialSheaf ≅ (Scheme.Modules.pullback (q ≫ g)).obj M := by
    rw [← hpq]
    exact hpL.divisorialSheafIso (hBc := hLc) ≪≫ (Scheme.Modules.pullback p).mapIso e ≪≫
      (Scheme.Modules.pullbackComp p f).app M
  -- a Cartier divisor `L_Y` with `𝒪_Y(L_Y) ≅ g^*M`
  have : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback g).obj M) :=
    MMP.Fourfold.isInvertibleModule_pullback g M
  obtain ⟨LY, hLYc, ⟨eLY⟩⟩ : ∃ LY : Divisor Y, LY.IsCartier ∧
      Nonempty (LY.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj M) := by
    obtain ⟨E₀, ⟨e₀⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf
      ((Scheme.Modules.pullback g).obj M)
    have : IsNoetherian Y := ⟨⟩
    obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier E₀
    obtain ⟨e₁⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
    exact ⟨w, hw.isCartier, ⟨e₁.symm ≪≫ e₀.symm⟩⟩
  have hLYB : ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ LY.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant q _
  have hpLY := Divisor.isPullback_pullback (f := q) hLYc hLYB
  set LYW := LY.pullback hLYc hLYB
  have eLYW : LYW.divisorialSheaf ≅ (Scheme.Modules.pullback (q ≫ g)).obj M :=
    hpLY.divisorialSheafIso (hBc := hLYc) ≪≫ (Scheme.Modules.pullback q).mapIso eLY ≪≫
      (Scheme.Modules.pullbackComp q g).app M
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso (eLYW ≪≫ eLW.symm)
  -- the relation on `W`
  have hpbD : (Divisor.toQDivisor K + B + A).IsPullback p
      (map_componentGenericPoint_notMem_supp_of_isQCartier p hKBAq)
      (Divisor.toQDivisor KW + ΔW + AW) := isPullback_add hKBq hAq _ hpbX hpbA
  have hφW := qLinearlyEquivalent_pullback p hKBAq hGq hpbD hpbG φ₁ hφ₁
  set φ₁W := pullbackRationalFunction p φ₁ (map_componentGenericPoint_notMem_supp_of_isDominant p _)
  -- push-forwards to `Y`
  obtain ⟨φY, -, -, hTφ⟩ := exists_transformDivisor_principalDivisor hYn hWY hq φ
  obtain ⟨φ₁Y, -, -, hTφ₁⟩ := exists_transformDivisor_principalDivisor hYn hWY hq φ₁W
  obtain ⟨ψY, -, -, hTψ⟩ := exists_transformDivisor_principalDivisor hYn hWY hq ψ
  have hTq : ∀ D : Divisor W, T (Divisor.toQDivisor D) =
      Divisor.toQDivisor (RationalMap.transformDivisor (X := W) q.toRationalMap D) :=
    transformDivisor_toQDivisor hYn hWY hq
  have hTKW' : T (Divisor.toQDivisor KW') = Divisor.toQDivisor KY := by rw [hTq, htrW']
  have hTKB : T (Divisor.toQDivisor KW' + ΔW) = Divisor.toQDivisor KY + BY :=
    MMP.Positivity.transformDivisor_of_isPullback hYn hWY hq hYdlt.1.2.2 hB2 hpbY
  have hTΔ : T ΔW = BY := by
    rw [map_add, hTKW'] at hTKB
    exact add_left_cancel hTKB
  have hTKW : T (Divisor.toQDivisor KW) = Divisor.toQDivisor KY -
      Divisor.toQDivisor (principalDivisor φY) := by
    have : KW = KW' - principalDivisor φ := by rw [← hφ]; abel
    rw [this, map_sub, map_sub, hTKW', hTq, hTφ]
  have hTLY : T (Divisor.toQDivisor LYW) = Divisor.toQDivisor LY := by
    rw [hTq, MMP.Positivity.transformDivisor_of_isPullback_divisor hYn hWY hq hLYc hpLY]
  have hTLW : T (Divisor.toQDivisor LW) = Divisor.toQDivisor LY -
      Divisor.toQDivisor (principalDivisor ψY) := by
    have : LW = LYW - principalDivisor ψ := by rw [← hψ]; abel
    rw [this, map_sub, map_sub, hTLY, hTq, hTψ]
  have h1 : (m : ℤ) • (T (Divisor.toQDivisor KW) + BY + AY - T GW) =
      Divisor.toQDivisor (principalDivisor φ₁Y) := by
    have := congrArg T hφW
    rw [map_zsmul, map_sub, map_add, map_add, hTΔ, hTq (principalDivisor φ₁W), hTφ₁] at this
    exact this
  have h2 : (m₀ : ℤ) • T GW = Divisor.toQDivisor LY - Divisor.toQDivisor (principalDivisor ψY) := by
    rw [← map_zsmul, ← hLW, hTLW]
  set GY : QDivisor Y := (m₀ : ℚ)⁻¹ • Divisor.toQDivisor LY with hGYdef
  have hGY : (m₀ : ℤ) • GY = Divisor.toQDivisor LY := natCast_zsmul_inv_smul hm₀ _
  set χ : (RationalFunctions Y)ˣ := φ₁Y ^ (m₀ : ℤ) * ψY ^ (-(m : ℤ)) * φY ^ ((m * m₀ : ℕ) : ℤ)
  have hχ : Divisor.toQDivisor (principalDivisor χ) =
      (m₀ : ℤ) • Divisor.toQDivisor (principalDivisor φ₁Y) -
        (m : ℤ) • Divisor.toQDivisor (principalDivisor ψY) +
        ((m * m₀ : ℕ) : ℤ) • Divisor.toQDivisor (principalDivisor φY) := by
    ext P
    simp only [χ, Divisor.coeff_toQDivisor, coeff_principalDivisor, PrimeDivisor.ord_mul,
      PrimeDivisor.ord_zpow, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  have hχY : ((m * m₀ : ℕ) : ℤ) • (Divisor.toQDivisor KY + BY + AY - GY) =
      Divisor.toQDivisor (principalDivisor χ) := by
    rw [hχ]
    push_cast
    linear_combination (norm := module) (m₀ : ℤ) • h1 - ((m : ℤ) * m₀) • hTKW + (m : ℤ) • h2 -
      (m : ℤ) • hGY
  have hDGY : (Divisor.toQDivisor KY + BY + AY).QLinearlyEquivalent GY :=
    ⟨m * m₀, Nat.mul_pos hm hm₀, χ, hχY⟩
  have hYq : (Divisor.toQDivisor KY + BY).IsQCartier := hYdlt.1.2.2
  have hGYq : GY.IsQCartier := ⟨m₀, by exact_mod_cast hm₀.ne', LY, hGY.symm, hLYc⟩
  have hYAq : (Divisor.toQDivisor KY + BY + AY).IsQCartier :=
    isQCartier_of_qLinearlyEquivalent hGYq hDGY.symm
  have hAYq : AY.IsQCartier := by
    have := hYAq.add (isQCartier_qsmul hYq (-1))
    convert this using 1
    module
  -- the pull-back of `A_Y` to `W` is `A_W`
  have hpbAY := QDivisor.isPullback_pullback (f := q) hAYq
    (map_componentGenericPoint_notMem_supp_of_isQCartier q hAYq)
  set AW' := AY.pullback hAYq (map_componentGenericPoint_notMem_supp_of_isQCartier q hAYq)
  have hpbDY : (Divisor.toQDivisor KY + BY + AY).IsPullback q
      (map_componentGenericPoint_notMem_supp_of_isQCartier q hYAq)
      (Divisor.toQDivisor KW' + ΔW + AW') := isPullback_add hYq hAYq _ hpbY hpbAY
  have hpbGY := QDivisor.isPullback_pullback (f := q) hGYq
    (map_componentGenericPoint_notMem_supp_of_isQCartier q hGYq)
  set GYW := GY.pullback hGYq (map_componentGenericPoint_notMem_supp_of_isQCartier q hGYq)
  have hGYW : (m₀ : ℤ) • GYW = Divisor.toQDivisor LYW := by
    obtain ⟨D', hD', hp'⟩ := hpbGY m₀ hm₀ LY hGY.symm hLYc
    rw [← hD', hp'.eq hLYc hpLY]
  have hW1 := qLinearlyEquivalent_pullback q hYAq hGYq hpbDY hpbGY χ hχY
  set χW := pullbackRationalFunction q χ (map_componentGenericPoint_notMem_supp_of_isDominant q _)
  set ξ : (RationalFunctions W)ˣ := χW * φ ^ (-((m * m₀ : ℕ) : ℤ)) * ψ ^ (m : ℤ) *
    φ₁W ^ (-(m₀ : ℤ))
  have hξ : ((m * m₀ : ℕ) : ℤ) • (AW' - AW) = Divisor.toQDivisor (principalDivisor ξ) := by
    have e1 : Divisor.toQDivisor (principalDivisor ξ) =
        Divisor.toQDivisor (principalDivisor χW) -
          ((m * m₀ : ℕ) : ℤ) • Divisor.toQDivisor (principalDivisor φ) +
          (m : ℤ) • Divisor.toQDivisor (principalDivisor ψ) -
          (m₀ : ℤ) • Divisor.toQDivisor (principalDivisor φ₁W) := by
      ext P
      simp only [ξ, Divisor.coeff_toQDivisor, coeff_principalDivisor, PrimeDivisor.ord_mul,
        PrimeDivisor.ord_zpow, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    have hφq : Divisor.toQDivisor KW' - Divisor.toQDivisor KW =
        Divisor.toQDivisor (principalDivisor φ) := by rw [← hφ, map_sub]
    have hψq : Divisor.toQDivisor LYW - Divisor.toQDivisor LW =
        Divisor.toQDivisor (principalDivisor ψ) := by rw [← hψ, map_sub]
    rw [e1]
    push_cast at hW1 ⊢
    linear_combination (norm := module) hW1 - (m₀ : ℤ) • hφW - ((m : ℤ) * m₀) • hφq +
      (m : ℤ) • hψq + (m : ℤ) • hGYW + (m : ℤ) • hLW
  have hAW' : AW' = AW := by
    obtain ⟨ξY, hξY, hξpb, hTξ⟩ := exists_transformDivisor_principalDivisor hYn hWY hq ξ
    have hT0 : T (Divisor.toQDivisor (principalDivisor ξ)) = 0 := by
      rw [← hξ, map_zsmul, map_sub,
        MMP.Positivity.transformDivisor_of_isPullback hYn hWY hq hAYq _ hpbAY, sub_self,
        smul_zero]
    rw [hTq, hTξ] at hT0
    have hξY0 : principalDivisor ξY = 0 := by
      ext P
      have := congrArg (fun D : QDivisor Y => D.coeff P) hT0
      simpa using this
    have hξ0 : principalDivisor ξ = 0 := by
      rw [← hξpb]; exact principalDivisor_pullback_eq_zero q ξY hξY hξY0
    rw [hξ0, map_zero] at hξ
    have hN : ((m * m₀ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hm hm₀).ne'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hξ).resolve_left hN)
  -- `(Y, B_Y + A_Y)` is lc: its discrepancies are those of `(X, B + A)` through `W`
  have hYAq' : (Divisor.toQDivisor KY + (BY + AY)).IsQCartier := by
    rw [← add_assoc]; exact hYAq
  have hXAq' : (Divisor.toQDivisor K + (B + A)).IsQCartier := by
    rw [← add_assoc]; exact hKBAq
  have hpbYA : (Divisor.toQDivisor KY + (BY + AY)).IsPullback q
      (map_componentGenericPoint_notMem_supp_of_isQCartier q hYAq')
      (Divisor.toQDivisor KW' + (ΔW + AW)) :=
    isPullback_congr (add_assoc _ _ _) (by rw [hAW', add_assoc]) hpbDY
  have hpbXA : (Divisor.toQDivisor K + (B + A)).IsPullback p
      (map_componentGenericPoint_notMem_supp_of_isQCartier p hXAq')
      (Divisor.toQDivisor KW + (ΔW + AW)) :=
    isPullback_congr (add_assoc _ _ _) (add_assoc _ _ _) hpbD
  have hPYA : MMP.Mori.IsPair sY (BY + AY) := ⟨hYn, 3, KY, hYdlt.1.2.1, hYAq'⟩
  have hPX : IsPairWith sX 3 K (B + A) := ⟨hXn, hKB.1.2.1, hXAq'⟩
  obtain ⟨-, hdiscY⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hPYA q hWY hq hYdlt.1.2.1
    hKW' (Or.inr ⟨inferInstance, htrW', _, hpbYA⟩)
  obtain ⟨-, hdiscX⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hlcI.1 p hWX hp hKB.1.2.1
    hKW (Or.inr ⟨inferInstance, htrW, _, hpbXA⟩)
  have hlcY : MMP.Intersection.IsLogCanonicalPair sY (BY + AY) := by
    refine ⟨hPYA, fun P => add_nonneg (hYdlt.2.1 P).1 (hAY0 P), fun n D b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := exists_isDiscrepancy_of_isLogDiscrepancy hPYA hYdlt.1.2.1 hb
    obtain ⟨E, hE⟩ := MMP.Mori.exists_divisorOver_comap_eq hWY hq D
    have haW := (hdiscY E D hE a).mpr ha
    have hKWq : KW.IsCanonicalDivisor (q ≫ sY) 3 := hs ▸ hKW
    have haW2 := isDiscrepancy_of_linearlyEquivalent hKWq φ⁻¹
      (by rw [MMP.Mori.principalDivisor_inv, ← hφ]; abel) haW
    have haW3 := isDiscrepancy_congr_structure hs.symm haW2
    have hv := MMP.Mori.valuation_compDivisorOver p hWX hp (hs.symm ▸ E)
    have haX := (hdiscX (hs.symm ▸ E) (MMP.Mori.compDivisorOver p hWX hp (hs.symm ▸ E)) hv a).mp
      haW3
    have h1 := neg_one_le_of_isLogCanonicalPair hPX hlcI haX
    have : (-1 : ℝ) ≤ a := by exact_mod_cast h1
    linarith
  exact ⟨AY, hAY0, hAYq, hlcY, GY, hDGY, m₀, hm₀, LY, hGY.symm, ⟨eLY⟩⟩

/-! ### The pencil on the `ℚ`-factorial model -/

/-- **The pulled-back pencil has exact floor support.** On a crepant dlt modification
`e : Y' ⟶ Y` of the dlt pair `(Y, B_Y)`, the pull-back `P' = e^*P` of an effective `ℚ`-Cartier `P`
with support exactly `⌊B_Y⌋` has support exactly `⌊B_{Y'}⌋`: an `e`-exceptional prime has
coefficient one in `B_{Y'}`, and positive coefficient in `P'` because `(Y, B_Y - εP)` is klt. -/
private theorem pencil_support {Y Y' : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] [CompactSpace Y'] {KY : Divisor Y} {BY : QDivisor Y}
    (hYdlt : Mori.IsDltPair sY 3 KY BY) (hYdltI : MMP.Intersection.IsDltPair sY BY)
    (e : Y' ⟶ Y) [IsProper e] (he : IsBirationalMorphism e) (hY'n : IsNormalVariety ℂ (e ≫ sY))
    {BY' : QDivisor Y'} (hcrep : IsCrepantBoundary sY 3 KY BY e hY'n he BY')
    (hexc : ∀ E : MMP.Mori.PrimeDivisor Y', RationalMap.IsExceptional (X := Y') e.toRationalMap E →
      MMP.Intersection.IsLogDiscrepancy sY 3 (QDivisor.toRDivisor BY)
        (⟨Y', e, hY'n, he, E⟩ : DivisorOver ℂ sY) 0 ∧ BY'.coeff E = 1)
    {P : QDivisor Y} (hP0 : 0 ≤ P) (hPq : P.IsQCartier)
    (hPsupp : ∀ E : MMP.Mori.PrimeDivisor Y, P.coeff E ≠ 0 ↔ BY.roundDown.coeff E ≠ 0)
    (hT : BY.roundDown ≠ 0) :
    ∃ P' : QDivisor Y', (∃ hB, P.IsPullback e hB P') ∧ 0 ≤ P' ∧ P'.IsQCartier ∧
      (∀ E : MMP.Mori.PrimeDivisor Y', P'.coeff E ≠ 0 ↔ BY'.roundDown.coeff E ≠ 0) ∧
      BY'.roundDown ≠ 0 := by
  classical
  have hYn := hYdlt.1.1
  have hKY := hYdlt.1.2.1
  have : AlgebraicGeometry.IsVariety ℂ sY := hYn.1
  have : AlgebraicGeometry.IsVariety ℂ (e ≫ sY) := hY'n.1
  have : IsDominant e := he.isDominant
  have hbij := he.functionFieldMap_bijective
  have hPB : MMP.Mori.IsPair sY BY := hYdltI.1.1
  obtain ⟨K', hK', -, htr⟩ := exists_compatible_canonicalDivisor hYn e he hY'n hKY
  obtain ⟨-, -, hB1, hpbB⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hPB e hY'n he hKY hK'
    (Or.inr ⟨inferInstance, htr⟩) hcrep
  have hpbP := QDivisor.isPullback_pullback (f := e) hPq
    (map_componentGenericPoint_notMem_supp_of_isQCartier e hPq)
  set P' := P.pullback hPq (map_componentGenericPoint_notMem_supp_of_isQCartier e hPq)
  have hP'0 : 0 ≤ P' := nonneg_of_isPullback hP0 hPq hpbP
  have hP'q : P'.IsQCartier := hpbP.isQCartier hPq
  have hKBq : (Divisor.toQDivisor KY + BY).IsQCartier := hYdlt.1.2.2
  have hTP : RationalMap.transformDivisor (X := Y') e.toRationalMap P' = P :=
    MMP.Positivity.transformDivisor_of_isPullback hYn hY'n he hPq _ hpbP
  have hTKB : RationalMap.transformDivisor (X := Y') e.toRationalMap
      (Divisor.toQDivisor K' + BY') = Divisor.toQDivisor KY + BY :=
    MMP.Positivity.transformDivisor_of_isPullback hYn hY'n he hKBq _ hpbB
  -- non-exceptional primes are strict transforms
  have hnonexc : ∀ E' : MMP.Mori.PrimeDivisor Y',
      ¬ RationalMap.IsExceptional (X := Y') e.toRationalMap E' →
      ∃ Γ : MMP.Mori.PrimeDivisor Y, P'.coeff E' = P.coeff Γ ∧ BY'.coeff E' = BY.coeff Γ := by
    intro E' hE'
    obtain ⟨Γ, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hYn
      (⟨Y', e, hY'n, he, E'⟩ : DivisorOver ℂ sY) hE'
    have hx : e E'.genericPoint = Γ.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hYn.1 hv
    obtain ⟨E'', heq, hiso, htrΓ⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hYn hY'n he Γ
    have hE : E'' = E' := by
      have := hiso
      have := Γ.isDiscreteValuationRing_localRing
      have : ValuationRing (Y.presheaf.stalk (e E''.genericPoint)) := by
        rw [heq]; infer_instance
      have : ValuationRing (Y.presheaf.stalk (e E'.genericPoint)) := by
        rw [hx]; infer_instance
      have : IsIso (e.stalkMap E'.genericPoint) :=
        MMP.Positivity.isIso_stalkMap_of_valuationRing e hbij E'.genericPoint
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (MMP.Positivity.eq_of_isIso_stalkMap e hbij (hx.trans heq.symm))
    subst hE
    refine ⟨Γ, ?_, ?_⟩
    · have h := htrΓ P'
      rw [hTP] at h
      exact h.symm
    · have h1 := htrΓ (Divisor.toQDivisor K' + BY')
      rw [hTKB] at h1
      have h2 := htrΓ K'
      rw [htr] at h2
      have h1' : (Divisor.toQDivisor KY + BY).coeff Γ = (Divisor.toQDivisor K' + BY').coeff E'' :=
        h1
      rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
        Divisor.coeff_toQDivisor] at h1'
      have h2' : KY.coeff Γ = K'.coeff E'' := h2
      rw [h2'] at h1'
      linarith
  -- exceptional primes have positive coefficient in `P'`: `(Y, B_Y - εP)` is klt
  have hexcP : ∀ E' : MMP.Mori.PrimeDivisor Y',
      RationalMap.IsExceptional (X := Y') e.toRationalMap E' → 0 < P'.coeff E' := by
    intro E' hE'
    set S : ℚ := ∑ Γ ∈ P.support, P Γ with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun Γ _ => hP0 Γ
    have hS : ∀ Γ, P.coeff Γ ≤ S := fun Γ => by
      by_cases hΓ : Γ ∈ P.support
      · exact Finset.single_le_sum (f := fun Γ => P Γ) (fun Γ _ => hP0 Γ) hΓ
      · rw [DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp hΓ]; exact hS0
    set ε : ℚ := (S + 1)⁻¹ with hεdef
    have hε0 : 0 < ε := by positivity
    have hεP : ∀ Γ, ε * P.coeff Γ < 1 := fun Γ => by
      have h1 : ε * P.coeff Γ ≤ ε * S := mul_le_mul_of_nonneg_left (hS Γ) hε0.le
      have h2 : ε * S < 1 := by
        rw [hεdef, inv_mul_lt_iff₀ (by positivity)]; linarith
      linarith
    set Bε : QDivisor Y := BY - ε • P with hBεdef
    have hcoeffε : ∀ Γ, Bε.coeff Γ = BY.coeff Γ - ε * P.coeff Γ := fun Γ => by
      rw [hBεdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have hfloor : ∀ Γ, P.coeff Γ ≠ 0 → BY.coeff Γ = 1 := fun Γ hΓ => by
      have h1 := (hPsupp Γ).mp hΓ
      rw [DivisorWithCoeffs.coeff_roundDown] at h1
      have h2 := hYdlt.2.1 Γ
      by_contra hne
      exact h1 (Int.floor_eq_zero_iff.mpr ⟨h2.1, lt_of_le_of_ne h2.2 hne⟩)
    have h0 : 0 ≤ Bε := fun Γ => by
      change 0 ≤ Bε.coeff Γ
      rw [hcoeffε]
      by_cases hΓ : P.coeff Γ = 0
      · rw [hΓ, mul_zero, sub_zero]; exact (hYdlt.2.1 Γ).1
      · rw [hfloor Γ hΓ]; linarith [hεP Γ]
    have hle : Bε ≤ BY := fun Γ => by
      change Bε.coeff Γ ≤ BY.coeff Γ
      rw [hcoeffε]
      have := mul_nonneg hε0.le (show (0 : ℚ) ≤ P.coeff Γ from hP0 Γ)
      linarith
    have hq : (BY - Bε).IsQCartier := by
      rw [hBεdef, sub_sub_cancel]; exact isQCartier_qsmul hPq ε
    have hdltε := MMP.Intersection.IsDltPair.of_le sY hYdltI h0 hle hq
    have hlt : ∀ Γ, Bε.coeff Γ < 1 := fun Γ => by
      rw [hcoeffε]
      by_cases hΓ : P.coeff Γ = 0
      · rw [hΓ, mul_zero, sub_zero]
        have h1 : BY.roundDown.coeff Γ = 0 := by
          by_contra h; exact ((hPsupp Γ).mpr h) hΓ
        rw [DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_zero_iff] at h1
        exact h1.2
      · have h1 := hP0 Γ
        have h2 : 0 < ε * P.coeff Γ := mul_pos hε0 (lt_of_le_of_ne h1 (Ne.symm hΓ))
        linarith [(hYdlt.2.1 Γ).2]
    have hklt := MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hdltε hlt
    have hnεq : (-ε • P).IsQCartier := isQCartier_qsmul hPq (-ε)
    have hBεq : (Divisor.toQDivisor KY + Bε).IsQCartier := by
      have := hKBq.add hnεq
      rwa [hBεdef, ← add_sub_assoc, sub_eq_add_neg, ← neg_smul]
    have hpbε : (Divisor.toQDivisor KY + Bε).IsPullback e
        (map_componentGenericPoint_notMem_supp_of_isQCartier e hBεq)
        (Divisor.toQDivisor K' + (BY' - ε • P')) :=
      isPullback_congr (by rw [hBεdef, neg_smul, ← sub_eq_add_neg, add_sub_assoc])
        (by rw [neg_smul, ← sub_eq_add_neg, add_sub_assoc])
        (isPullback_add hKBq hnεq
          (map_componentGenericPoint_notMem_supp_of_isQCartier e (hKBq.add hnεq)) hpbB
          (isPullback_qsmul hPq (-ε)
            (map_componentGenericPoint_notMem_supp_of_isQCartier e hnεq) hpbP))
    obtain ⟨hpairY', hdisc⟩ := MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hklt.1.isPair e hY'n
      he hKY hK' (Or.inr ⟨inferInstance, htr, _, hpbε⟩)
    set D₀ := DivisorOver.ofPrimeDivisor ℂ hY'n E'
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpairY' hK' D₀
    have ha' := ha.eq_neg_coeff_of_ofPrimeDivisor hY'n
    have hv := MMP.Mori.valuation_compDivisorOver e hY'n he D₀
    have haY := (hdisc D₀ (MMP.Mori.compDivisorOver e hY'n he D₀) hv a).mp ha
    have hprop : IsProper (MMP.Mori.compDivisorOver e hY'n he D₀).f := by
      change IsProper (𝟙 Y' ≫ e); infer_instance
    have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy haY hprop
    have hpos := hklt.2 3 _ _ hlog
    rw [ha', DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      (hexc E' hE').2] at hpos
    have : (0 : ℚ) < ε * P'.coeff E' := by
      have h : (0 : ℝ) < ((ε * P'.coeff E' : ℚ) : ℝ) := by push_cast at hpos ⊢; linarith
      exact_mod_cast h
    exact (pos_iff_pos_of_mul_pos this).mp hε0
  have hsupp' : ∀ E' : MMP.Mori.PrimeDivisor Y', P'.coeff E' ≠ 0 ↔ BY'.roundDown.coeff E' ≠ 0 := by
    intro E'
    by_cases hE' : RationalMap.IsExceptional (X := Y') e.toRationalMap E'
    · have h1 := (hexc E' hE').2
      constructor
      · intro _; rw [DivisorWithCoeffs.coeff_roundDown, h1]; norm_num
      · intro _; exact (hexcP E' hE').ne'
    · obtain ⟨Γ, h1, h2⟩ := hnonexc E' hE'
      rw [h1, DivisorWithCoeffs.coeff_roundDown, h2, ← DivisorWithCoeffs.coeff_roundDown]
      exact hPsupp Γ
  refine ⟨P', ⟨_, hpbP⟩, hP'0, hP'q, hsupp', ?_⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, BY.roundDown.coeff Γ ≠ 0 := by
    by_contra h
    push Not at h
    exact hT (Finsupp.ext h)
  have hPΓ := (hPsupp Γ).mpr hΓ
  intro h0
  have hP'z : P' = 0 := by
    ext E'
    by_contra hne
    have := (hsupp' E').mp hne
    rw [h0] at this
    exact this rfl
  rw [hP'z, map_zero] at hTP
  exact hPΓ (by rw [← hTP]; rfl)

section FloorGluing

open MMP.Flips

/-! ### Adjunction on the floor components -/

/-- On a log canonical pair every coefficient of the boundary is at most one: the log
discrepancy of a prime divisor `P` is `1 - coeff_P`. -/
private theorem coeff_le_one_of_isLogCanonicalPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ≤ 1 := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, -, hlc⟩ := hB
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  have hd : IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hX P) (-B.coeff P) := by
    refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
    rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
    have hPV : (P.support ∩ (V : Set X)).Nonempty := by
      refine ⟨P.genericPoint, ?_, hV⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    linear_combination -hτ.2 P hPV
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd
    (show IsProper (𝟙 X) from inferInstance))
  have h1 : ((B.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast h1

/-- For a pair `(X, Δ)`, `K + Δ` is `ℚ`-Cartier for every canonical divisor `K` of `X`. -/
private theorem isQCartier_add_of_isPair {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X} (h : MMP.Mori.IsPair sX Δ)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    (Divisor.toQDivisor K + Δ).IsQCartier := by
  obtain ⟨hX, n₀, K₀, hK₀, hQ⟩ := h
  exact hQ.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK₀ hK)

/-- An integral locally Noetherian normal scheme with a point other than its generic point has a
prime divisor: a minimal prime over a nonzero element of the maximal ideal of the local ring at
that point has height one by Krull's principal ideal theorem. -/
private theorem nonempty_primeDivisor_of_ne_genericPoint {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : x ≠ genericPoint X) :
    Nonempty (MMP.Mori.PrimeDivisor X) := by
  set R := X.presheaf.stalk x
  have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro h0
    have hη : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    have hx' : x ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact specializes_rfl
    obtain ⟨p₁, hp₁⟩ := hη
    obtain ⟨p₂, hp₂⟩ := hx'
    have hall : ∀ p : PrimeSpectrum R, p.asIdeal = ⊥ := fun p =>
      le_bot_iff.mp (h0 ▸ IsLocalRing.le_maximalIdeal p.2.ne_top)
    have : p₁ = p₂ := PrimeSpectrum.ext ((hall p₁).trans (hall p₂).symm)
    exact hx (by rw [← hp₂, ← this, hp₁])
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hle : Ideal.span {a} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr ha
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  have : q.IsPrime := hq.1.1
  have h1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
  have h0 : q.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hq0
    exact ha0 (by
      have : a ∈ q := hq.1.2 (Ideal.mem_span_singleton_self a)
      rwa [hq0, Ideal.mem_bot] at this)
  have hq1 : q.height = 1 := le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0)
  obtain ⟨E, -, -⟩ := MMP.Mori.exists_primeDivisor_isLocalization (x := x) ⟨q, inferInstance⟩ hq1
  exact ⟨E⟩

/-- A scheme of positive dimension has a point other than a given one. -/
private theorem exists_ne_of_topologicalKrullDim_pos {X : Scheme.{0}} {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim X = n) (y : X) : ∃ x : X, x ≠ y := by
  by_contra h
  push Not at h
  have : Subsingleton X := ⟨fun a b => (h a).trans (h b).symm⟩
  have : DiscreteTopology X := Subsingleton.discreteTopology
  have h0 := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at h0
  norm_cast at h0
  omega

/-- If `m₀ B` is the Cartier divisor `D₀` for an `f`-nef `ℚ`-divisor `B`, then `D₀` has
nonnegative degree on every curve contracted by `f`. -/
private theorem degreeOn_nonneg_of_isRelativelyNef {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {f : X ⟶ Y} {B : QDivisor X}
    (hB : B.IsRelativelyNef sX f) {m₀ : ℕ} (hm₀ : 0 < m₀) {D₀ : Divisor X} (hD₀c : D₀.IsCartier)
    (hD₀B : Divisor.toQDivisor D₀ = (m₀ : ℤ) • B) (C : MMP.Mori.ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ D₀.degreeOn ℂ sX C.ι C.dim_le hD₀c := by
  have h := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hB hB.fst C hC
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le B hB.fst hm₀ D₀ hD₀c hD₀B] at h
  exact_mod_cast ((div_nonneg_iff.1 h).resolve_right fun h => (Nat.cast_pos.2 hm₀).not_ge h.2).1

/-- **Residue adjunction for one adjunction step.** Let `(S, B_S)` arise from `(Y, B_Y)` by an
adjunction step `j : S ⟶ Y`, `Y` a normal complex variety of dimension `n + 1 ≥ 2` with
`K_Y + B_Y` `ℚ`-Cartier. There are a rational top form `σ` on `Y` with `div σ ∼ K_Y` and a
rational top form `ρ` on `S` with `div ρ ∼ K_S` such that `div ρ + B_S` is the pull-back of the
`ℚ`-Cartier divisor `div σ + B_Y`: `ρ` is the Poincaré residue of a form `σ` with a simple pole
along `S`. -/
private theorem exists_isPullback_divisorOfForm_add {Y S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY)
    {n : ℕ} (hn : 0 < n) (hdim : topologicalKrullDim Y = n + 1) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY (n + 1)) {BY : QDivisor Y}
    (hBq : (Divisor.toQDivisor KY + BY).IsQCartier)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {j : S ⟶ Y} [LocallyOfFiniteType (j ≫ sY)] {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) {KS : Divisor S} (hKS : KS.IsCanonicalDivisor (j ≫ sY) n) :
    ∃ (σ : RationalPluriForms sY (n + 1) 1) (ρ : RationalPluriForms (j ≫ sY) n 1),
      (divisorOfForm σ).LinearlyEquivalent KY ∧ (divisorOfForm ρ).LinearlyEquivalent KS ∧
      (Divisor.toQDivisor (divisorOfForm σ) + BY).IsQCartier ∧
      ∃ hgen : ∀ Z : irreducibleComponents S,
          j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (divisorOfForm σ) + BY).supp,
        (Divisor.toQDivisor (divisorOfForm σ) + BY).IsPullback j hgen
          (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
  classical
  obtain ⟨hSn, P, -, hPr, hci, -⟩ := id hS
  have := hci
  obtain ⟨x, hx⟩ := exists_ne_of_topologicalKrullDim_pos hn hKS.topologicalKrullDim_eq
    (genericPoint S)
  obtain ⟨Q⟩ := nonempty_primeDivisor_of_ne_genericPoint hx
  obtain ⟨σ, hσ0, hσP, -, ρ, hρ, hρ0, -⟩ :=
    exists_form_of_residue_order sY hYn hdim j hSn P hPr Q
  have hσK : (divisorOfForm σ).LinearlyEquivalent KY := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hKY hσ0
  have hρK : (divisorOfForm ρ).LinearlyEquivalent KS := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSn hKS hρ0
  have hD : (Divisor.toQDivisor (divisorOfForm σ) + BY).IsQCartier :=
    hBq.add_of_linearlyEquivalent hσK.symm
  exact ⟨σ, ρ, hσK, hρK, hD,
    hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hPr σ hσ0 hσP ρ hρ hD⟩

/-- **Adjunction preserves relative nefness.** Let `(S, B_S)` arise from `(Y, B_Y)` by one
adjunction step `j : S ⟶ Y` (`MMP.Fourfold.IsAdjunctionStep`), `Y` a normal complex variety of
dimension `n + 1 ≥ 2` with `K_Y + B_Y` `ℚ`-Cartier and nef over `g : Y ⟶ Z`. Then `K_S + B_S` is
nef over `g ∘ j`. Indeed for a rational top form `σ` with a simple pole along `S` and Poincaré
residue `ρ`, `div ρ + B_S` is the pull-back of `div σ + B_Y`, so the degree of `K_S + B_S` on a
curve `C ⊆ S` contracted over `Z` is a positive multiple of the degree of `K_Y + B_Y` on `j(C)`,
or zero. -/
private theorem isRelativelyNef_of_isAdjunctionStep {Y Z S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] [QuasiCompact sY] [IsSeparated sY] (hYn : IsNormalVariety ℂ sY)
    {n : ℕ} (hn : 0 < n) (hdim : topologicalKrullDim Y = n + 1) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY (n + 1)) {BY : QDivisor Y}
    (hBq : (Divisor.toQDivisor KY + BY).IsQCartier) {gY : Y ⟶ Z}
    (hnef : QDivisor.IsRelativelyNef sY gY (Divisor.toQDivisor KY + BY))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {j : S ⟶ Y} [QuasiCompact (j ≫ sY)] {BS : QDivisor S} (hS : IsAdjunctionStep sY BY j BS)
    {KS : Divisor S} (hKS : KS.IsCanonicalDivisor (j ≫ sY) n) :
    QDivisor.IsRelativelyNef (j ≫ sY) (j ≫ gY) (Divisor.toQDivisor KS + BS) := by
  classical
  obtain ⟨hSn, P, -, hPr, hci, -⟩ := id hS
  have := hci
  have : LocallyOfFiniteType (j ≫ sY) := hSn.1.toLocallyOfFiniteType
  obtain ⟨σ, ρ, hσK, hρK, hD, hgen, hpb⟩ :=
    exists_isPullback_divisorOfForm_add hYn hn hdim hKY hBq hS hKS
  obtain ⟨c, hc, L, hL, hLc⟩ : ∃ c : ℕ, 0 < c ∧ ∃ L : Divisor Y,
      Divisor.toQDivisor L = (c : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BY) ∧
        L.IsCartier := by
    obtain ⟨c, hc, L, hL, hLc⟩ := hD.exists_pos
    exact ⟨c, hc, L, hL, hLc⟩
  obtain ⟨L', hL', hLp⟩ := hpb c hc L hL hLc
  have hL'c : L'.IsCartier := hLp.isCartier hLc
  -- the Cartier multiples of the adjoints
  set LY : Divisor Y := L + (c : ℤ) • (KY - divisorOfForm σ)
  set LS : Divisor S := L' + (c : ℤ) • (KS - divisorOfForm ρ)
  have hLYL : LY.LinearlyEquivalent L := by
    rw [Divisor.linearlyEquivalent_iff_sub_mem_range,
      show LY - L = (c : ℤ) • (KY - divisorOfForm σ) from add_sub_cancel_left _ _]
    exact AddSubgroup.zsmul_mem _ (Divisor.linearlyEquivalent_iff_sub_mem_range.mp hσK.symm) _
  have hLSL : LS.LinearlyEquivalent L' := by
    rw [Divisor.linearlyEquivalent_iff_sub_mem_range,
      show LS - L' = (c : ℤ) • (KS - divisorOfForm ρ) from add_sub_cancel_left _ _]
    exact AddSubgroup.zsmul_mem _ (Divisor.linearlyEquivalent_iff_sub_mem_range.mp hρK.symm) _
  have hLYc : LY.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hLYL hLc
  have hLSc : LS.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hLSL hL'c
  have hLY : Divisor.toQDivisor LY = (c : ℤ) • (Divisor.toQDivisor KY + BY) := by
    rw [map_add, map_zsmul, map_sub, hL, ← smul_add]
    congr 1
    abel
  have hLS : Divisor.toQDivisor LS = (c : ℤ) • (Divisor.toQDivisor KS + BS) := by
    rw [map_add, map_zsmul, map_sub, hL', ← smul_add]
    congr 1
    abel
  have hSq : (Divisor.toQDivisor KS + BS).IsQCartier :=
    ⟨c, by exact_mod_cast hc.ne', LS, hLS, hLSc⟩
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (k := ℂ) (j ≫ sY) hSq
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ (j ≫ sY) C.ι C.dim_le _ hSq hc LS hLSc hLS]
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  have := hLc.isInvertibleModule_divisorialSheaf
  have := hLYc.isInvertibleModule_divisorialSheaf
  have := hL'c.isInvertibleModule_divisorialSheaf
  have := hLSc.isInvertibleModule_divisorialSheaf
  have e1 : LS.degreeOn ℂ (j ≫ sY) C.ι C.dim_le hLSc =
      C.degree ℂ ((Scheme.Modules.pullback j).obj L.divisorialSheaf) := by
    rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ (j ≫ sY) C.ι C.dim_le
      (hLSL.divisorialSheafIso ≪≫ hLp.divisorialSheafIso (hBc := hLc))]
    rfl
  rw [e1, C.degree_pullback j rfl]
  split_ifs with h
  · set Γ : MMP.Mori.ProperCurve sY := ⟨j C.point, h⟩ with hΓ
    have : IsProper (Γ.ι ≫ sY) := MMP.Mori.ProperCurve.isProper_ι_comp Γ
    suffices hdeg : 0 ≤ Γ.degree ℂ L.divisorialSheaf by
      exact_mod_cast (mul_nonneg (Nat.cast_nonneg _) hdeg : (0 : ℤ) ≤ _)
    have e2 : Γ.degree ℂ L.divisorialSheaf = LY.degreeOn ℂ sY Γ.ι Γ.dim_le hLYc := by
      rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sY Γ.ι Γ.dim_le hLYL.divisorialSheafIso]
      rfl
    rw [e2]
    refine degreeOn_nonneg_of_isRelativelyNef hnef hc hLYc hLY Γ fun y hy => ?_
    have hcl : IsClosed (j '' closure {C.point}) := j.isClosedMap _ isClosed_closure
    have hsub : ({j C.point} : Set Y) ⊆ j '' closure {C.point} :=
      Set.singleton_subset_iff.mpr ⟨C.point, subset_closure rfl, rfl⟩
    obtain ⟨x, hx, rfl⟩ := closure_minimal hsub hcl hy
    simpa only [Scheme.Hom.comp_apply] using hC x hx
  · exact le_rfl

/-- A local generator of the adjoint on `U` restricts to one on every smaller open. -/
private theorem isAdjointGeneratorOn_mono {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n m : ℕ} {Θ : ∀ i, QDivisor (N.X i)} {U U' : T.Opens}
    (h : U' ≤ U) {g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hg : IsAdjointGeneratorOn N n m Θ U g) : IsAdjointGeneratorOn N n m Θ U' g :=
  ⟨fun i => (hg.1 i).mono fun _ hz => h hz, fun i j P P' h₁ h₂ h₃ h₄ =>
    hg.2 i j P P' h₁ (h h₂) h₃ h₄⟩

/-! ### Functions on the floor and its normalization -/

/-- Every point of `T` lies under a point of some normalization component. -/
private theorem exists_base_eq {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (x : T) : ∃ i z, (N.n i).base z = x := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hsurj : Surjective (slcCurveNormalization T hT) := Scheme.surjective_normalization T hT
  obtain ⟨w, rfl⟩ := hsurj.surj x
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  refine ⟨i, z, ?_⟩
  have h1 : (Limits.Sigma.ι N.X i ≫ φ.hom ≫ slcCurveNormalization T hT).base z =
      (N.n i).base z := by
    rw [hφ, Limits.Sigma.ι_desc]
  have h2 : φ.hom.base (φ.inv.base w) = w := by
    rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
    rfl
  rw [← h1, Scheme.Hom.comp_apply, ← sigmaMk_mk, hz, Scheme.Hom.comp_apply, h2]

/-- **Functions on a reduced scheme are detected on its normalization.** A function on an open
`U` of the reduced scheme `T` whose pull-back to every normalization component meeting `U`
vanishes in the function field is zero. -/
private theorem eq_zero_of_forall_germToFunctionField_eq_zero {k : Type} [Field k]
    {T : Scheme.{0}} [IsReduced T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {U : T.Opens} (b : Γ(T, U))
    (h : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b) = 0) : b = 0 := by
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := exists_base_eq N x
  have hzU : z ∈ N.n i ⁻¹ᵁ U := T.basicOpen_le b hx
  have : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hzU⟩⟩
  have hz : z ∈ (N.X i).basicOpen ((N.n i).app U b) := by
    rw [← Scheme.preimage_basicOpen]
    exact hx
  have h0 : (N.n i).app U b = 0 :=
    (N.X i).germToFunctionField_injective (N.n i ⁻¹ᵁ U)
      ((h i inferInstance).trans (map_zero _).symm)
  rw [h0, Scheme.basicOpen_zero] at hz
  exact hz

/-- A unit multiple of a local generator is a local generator. -/
private theorem isLocalGenerator_smul_of_isUnit {X : Scheme.{0}} {L : X.Modules} {W : X.Opens}
    {a : Γ(L, W)} (ha : MMP.Mori.IsLocalGenerator L W a) {u : Γ(X, W)} (hu : IsUnit u) :
    MMP.Mori.IsLocalGenerator L W (u • a) := by
  intro V hV
  obtain ⟨v, rfl⟩ := hu
  have hres : L.presheaf.map (homOfLE hV).op ((v : Γ(X, W)) • a) =
      X.presheaf.map (homOfLE hV).op (v : Γ(X, W)) • L.presheaf.map (homOfLE hV).op a :=
    MMP.Mori.modules_res_smul hV _ a
  set w : Γ(X, V)ˣ := v.map (X.presheaf.map (homOfLE hV).op).hom
  have hw : (w : Γ(X, V)) = X.presheaf.map (homOfLE hV).op (v : Γ(X, W)) := rfl
  have key : (fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op ((v : Γ(X, W)) • a)) =
      (fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op a) ∘ (fun c => c * w) := by
    funext c
    simp only [Function.comp_apply, hres, ← hw, mul_smul]
  rw [key]
  exact (ha V hV).comp (Units.mulRight_bijective w)

/-! ### Local generators of `𝒪_Y(m(K_Y + B_Y))` from local equations -/

/-- **Forms attached to local equations.** Let `C = m(K + Δ)` be a divisor on a normal complex
variety with canonical divisor `K`. There is a map `φ ↦ F(φ)` from units of `K(X)` to rational
`m`-canonical forms such that `F(φ)` generates `𝒪_X(m(K + Δ))` wherever `φ` is a local equation
of `C`, and such that `F(φ) = r F(φ')` whenever `φ⁻¹ = r φ'⁻¹` on an open `V` for a function `r`
on `V`: `F(φ)` is the form `ω^{⊗m}/φ` for a rational top form `ω` with `div ω = K`. -/
private theorem exists_chartForm {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n) {Δ : QDivisor Y} {m : ℕ}
    {C : Divisor Y} (hC : Divisor.toQDivisor C = (m : ℤ) • (Divisor.toQDivisor K + Δ)) :
    ∃ F : (RationalFunctions Y)ˣ → RationalPluriForms sY n m,
      (∀ (U : Y.Opens) (φ : (RationalFunctions Y)ˣ), C.IsLocalEquation U φ →
        GeneratesOn Δ m U (F φ)) ∧
      ∀ (φ φ' : (RationalFunctions Y)ˣ) (V : Y.Opens) [Nonempty V] (r : Γ(Y, V)),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
          ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z =
            Y.presheaf.germ V _ hZ r * ((φ'⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z) →
        F φ = (Y.germToFunctionField V).hom r • F φ' := by
  classical
  have hn := hK.topologicalKrullDim_eq
  let := functionFieldAlgebra sY
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hYn hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYn hK
  have hsub : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  obtain ⟨Z₀, -⟩ := exists_mem_irreducibleComponents y₀
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  let g : (RationalFunctions Y)ˣ → Y.functionField := fun φ =>
    (MMP.Positivity.componentToFunctionField Z₀).hom (φ.val Z₀)
  have hginv : ∀ φ : (RationalFunctions Y)ˣ,
      (MMP.Positivity.componentToFunctionField Z₀).hom
        (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z₀) = (g φ)⁻¹ := by
    intro φ
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    change (MMP.Positivity.componentToFunctionField Z₀).hom
      (((φ⁻¹ * φ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z₀) = 1
    rw [inv_mul_cancel, Units.val_one, Pi.one_apply, map_one]
  refine ⟨fun φ => (c ^ (m : ℤ) * (g φ)⁻¹) • ZTensorPower.basis b m (), ?_, ?_⟩
  · intro U φ hφ
    have hg0 : g φ ≠ 0 := ((φ.isUnit.map (Pi.evalRingHom _ Z₀)).map _).ne_zero
    have hg : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.ord φ = Y.ord (g φ) Γ.genericPoint := fun Γ => by
      rw [MMP.Positivity.ord_eq_ord_componentToFunctionField Γ φ, Subsingleton.elim Γ.component Z₀]
    have hcg : c ^ (m : ℤ) * (g φ)⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg0)
    set τ : RationalPluriForms sY n m := (c ^ (m : ℤ) * (g φ)⁻¹) • ZTensorPower.basis b m ()
    have hrepr : (ZTensorPower.basis b m).repr τ () = c ^ (m : ℤ) * (g φ)⁻¹ := by
      simp [τ]
    have hτ : τ ≠ 0 := smul_ne_zero hcg ((ZTensorPower.basis b m).ne_zero ())
    refine ⟨hτ, fun Γ hΓ => ?_⟩
    obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hN 1 ω hω0
    have e2 := hN m τ hτ
    rw [hrepr, Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg0), ord_zpow _ hc,
      ← zpow_neg_one, ord_zpow _ hg0] at e2
    rw [← hc_def, hω Γ] at e1
    have hCΓ : (C.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ) := by
      have := congrArg (fun D : QDivisor Y => D.coeff Γ) hC
      rw [mul_add]
      simpa [zsmul_eq_mul] using this
    have hgΓ : C.coeff Γ = Y.ord (g φ) Γ.genericPoint := (hφ Γ hΓ).trans (hg Γ)
    have e1' : (K.coeff Γ : ℚ) = Y.ord c Γ.genericPoint + N := by exact_mod_cast (by omega : _)
    have e2' : (Γ.ordForm τ : ℚ) =
        m * Y.ord c Γ.genericPoint + -1 * Y.ord (g φ) Γ.genericPoint + m * N := by
      exact_mod_cast e2
    have hgΓ' : (C.coeff Γ : ℚ) = Y.ord (g φ) Γ.genericPoint := by exact_mod_cast hgΓ
    linear_combination e2' - (m : ℚ) * e1' + hgΓ' - hCΓ
  · intro φ φ' V _ r hrel
    obtain ⟨v⟩ : Nonempty V := inferInstance
    obtain ⟨Z₁, hZ₁⟩ := exists_mem_irreducibleComponents v.1
    obtain rfl : Z₁ = Z₀ := Subsingleton.elim _ _
    have hZ₀ : componentGenericPoint Y Z₁ ∈ V :=
      ((isGenericPoint_componentGenericPoint Y Z₁).mem_open_set_iff V.isOpen).mpr
        ⟨v.1, hZ₁, v.2⟩
    have key : (g φ)⁻¹ = (Y.germToFunctionField V).hom r * (g φ')⁻¹ := by
      rw [← hginv, ← hginv, hrel Z₁ hZ₀, map_mul]
      congr 1
      exact TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hZ₀ _ r
    simp only []
    rw [key, show c ^ (m : ℤ) * ((Y.germToFunctionField V).hom r * (g φ')⁻¹) =
      (Y.germToFunctionField V).hom r * (c ^ (m : ℤ) * (g φ')⁻¹) by ring]
    exact mul_smul _ _ _

/-! ### Residues of local generators -/

/-- **Residues of unit multiples.** If `τ = r τ'` for a function `r` on an open `V` containing
the generic point of the floor component `S`, then `Res_S τ = (r|_S) Res_S τ'`. -/
private theorem isPoincareResidue_eq_germ_smul {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    [IsIntegral S] {j : S ⟶ Y} {BY : QDivisor Y} {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) {n m : ℕ} {V : Y.Opens} [Nonempty V]
    [Nonempty (j ⁻¹ᵁ V)] (hV : j (genericPoint S) ∈ V) (r : Γ(Y, V))
    {τ τ' : RationalPluriForms sY (n + 1) m} (hτ : τ = (Y.germToFunctionField V).hom r • τ')
    {ρ ρ' : RationalPluriForms (j ≫ sY) n m} (hρ : IsPoincareResidue sY j n m τ ρ)
    (hρ' : IsPoincareResidue sY j n m τ' ρ') :
    ρ = (S.germToFunctionField (j ⁻¹ᵁ V)).hom (j.app V r) • ρ' := by
  have h1 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ'
    (Y.presheaf.germ V _ hV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← hτ, Scheme.Hom.germ_stalkMap_apply] at h1
  exact IsPoincareResidue.unique hS hρ h1

/-- **The residue of a local generator is nonzero.** Let `(S, B_S)` arise from `(Y, B_Y)` by an
adjunction step along the prime divisor `P = j(S)`, with `B_Y ≤ 1`, and let `τ` generate
`𝒪_Y(m(K_Y + B_Y))` on an open `W` meeting `P`. Then `Res_S τ ≠ 0`: `τ` has a pole of order
exactly `m` along `P`, so `τ = v σ^{⊗m}` for a form `σ` with a simple pole along `P` and a unit
`v` of `𝒪_{Y,P}`, and `Res_S τ = v̄ (Res_S σ)^{⊗m}`. -/
private theorem isPoincareResidue_ne_zero_of_generatesOn {Y S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY) {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim Y = n + 1)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] {j : S ⟶ Y}
    [LocallyOfFiniteType (j ≫ sY)] {BY : QDivisor Y} {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) (hdimS : topologicalKrullDim S = n)
    (hle : ∀ P, BY.coeff P ≤ 1) {M : ℕ} (hM : 0 < M) {W : Y.Opens}
    {τ : RationalPluriForms sY (n + 1) M} (hτ : GeneratesOn BY M W τ)
    (hW : j (genericPoint S) ∈ W) {ρ : RationalPluriForms (j ≫ sY) n M}
    (hρ : IsPoincareResidue sY j n M τ ρ) : ρ ≠ 0 := by
  classical
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨hSn, P, hP1, hPr, hci, -⟩ := id hS
  have := hci
  have hjP : j (genericPoint S) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hPr
  have hBP : BY.coeff P = 1 := le_antisymm (hle P) hP1
  have hdim' : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  obtain ⟨x, hx⟩ := exists_ne_of_topologicalKrullDim_pos hn hdimS (genericPoint S)
  obtain ⟨Q⟩ := nonempty_primeDivisor_of_ne_genericPoint hx
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    exists_form_of_residue_order sY hYn hdim j hSn P hPr Q
  set τ₀ := MMP.CyclicChartDifferent.Aux.pluriPow σ M with hτ₀def
  have hτ₀0 : τ₀ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdim' hσ0 M
  have hordτ₀ : P.ordForm τ₀ = -((M + 1 : ℕ) : ℤ) := by
    rw [hτ₀def, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow hdim' hσ0 P M, hσP]
    ring
  have hρ₀ := MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjP hdim hρσ M
  have hρ₀0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdimS hρσ0 M
  -- the ratio `u = τ / τ₀`
  let := functionFieldAlgebra sY
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) hdim'
  set B := ZTensorPower.basis b ((M + 1 : ℕ) : ℤ)
  have hc₀ : B.repr τ₀ () ≠ 0 := repr_ne_zero_of_ne_zero b hτ₀0
  set u := B.repr τ () / B.repr τ₀ ()
  have hτu : τ = u • τ₀ := by
    rw [← basis_unit_repr_smul B τ, ← basis_unit_repr_smul B τ₀]
    exact (by rw [← mul_smul, div_mul_cancel₀ _ hc₀] :
      (B.repr τ () • B () : ZTensorPower _ _ _) = u • B.repr τ₀ () • B ())
  have hu0 : u ≠ 0 := div_ne_zero (repr_ne_zero_of_ne_zero b hτ.1) hc₀
  have hPW : (P.support ∩ (W : Set Y)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hjP ▸ hW⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hordu : Y.ord u P.genericPoint = 0 := by
    have e1 := hτ.2 P hPW
    rw [hτu, P.ordForm_smul_of_topologicalKrullDim_eq hdim' hu0 hτ₀0, hordτ₀, hBP] at e1
    push_cast at e1
    have : (Y.ord u P.genericPoint : ℚ) = 0 := by linarith
    exact_mod_cast this
  obtain ⟨v, hv, hvu⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    (j (genericPoint S)) hu0 fun Γ hΓ => by
      rw [hjP] at hΓ
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      exact hordu
  have h1 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ₀ v
  rw [hvu, ← hτu] at h1
  rw [IsPoincareResidue.unique hS hρ h1]
  exact smul_ne_zero ((hv.map (j.stalkMap (genericPoint S)).hom).ne_zero) hρ₀0

/-- The image of a section in the function field does not change under restriction. -/
private theorem germToFunctionField_app_res {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (i : N.ι) {U U' : T.Opens} (hU : U' ≤ U) (f : Γ(T, U))
    [Nonempty (N.n i ⁻¹ᵁ U')] [Nonempty (N.n i ⁻¹ᵁ U)] :
    ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
        ((N.n i).app U' (T.presheaf.map (homOfLE hU).op f)) =
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) := by
  have h := congrArg (fun φ => ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom (φ.hom f))
    ((N.n i).naturality (homOfLE hU).op)
  simp only [CommRingCat.comp_apply] at h
  rw [h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **Comparing coefficients against two families of forms.** On a reduced `T`, if
`t = b ρ = b' ρ'` on every normalization component meeting `U` and `ρ = r ρ'` with `ρ' ≠ 0`, then
`b r = b'` on `U`. -/
private theorem mul_eq_of_smul_eq {k : Type} [Field k] {T : Scheme.{0}} [IsReduced T]
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n m : ℕ} {U : T.Opens} {b b' r : Γ(T, U)}
    {t ρ ρ' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hρ : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      ρ i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U r) • ρ' i)
    (hρ'0 : ∀ i, ρ' i ≠ 0)
    (ht : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b) • ρ i)
    (ht' : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b') • ρ' i) :
    b * r = b' := by
  refine sub_eq_zero.mp (eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_)
  have h := (ht i hi).symm.trans (ht' i hi)
  rw [hρ i hi, smul_smul] at h
  rw [map_sub, map_sub, map_mul, map_mul]
  exact sub_eq_zero.mpr (smul_left_injective _ (hρ'0 i) h)

/-- The restriction of a local generator to a smaller open is a local generator. -/
private theorem isLocalGenerator_res {X : Scheme.{0}} {L : X.Modules} {W W' : X.Opens}
    {a : Γ(L, W)} (ha : MMP.Mori.IsLocalGenerator L W a) (hW : W' ≤ W) :
    MMP.Mori.IsLocalGenerator L W' (L.presheaf.map (homOfLE hW).op a) := by
  intro V hV
  have h := ha V (hV.trans hW)
  rwa [show L.presheaf.map (homOfLE (hV.trans hW)).op a =
    L.presheaf.map (homOfLE hV).op (L.presheaf.map (homOfLE hW).op a) from
      (MMP.Mori.modules_res_res hV hW a).symm] at h

/-! ### Relative generation from local generators -/

/-- A locally surjective morphism of sheaves of modules is an epimorphism. -/
private theorem epi_of_locally_surjective {X : Scheme.{0}} {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ (U : X.Opens) (b : Γ(B, U)) (x : X), x ∈ U → ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      ∃ a : Γ(A, V), φ.val.app (Opposite.op V) a = B.presheaf.map (homOfLE hV).op b) :
    Epi φ := by
  have h' : TopCat.Presheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map φ).hom :=
    (TopCat.Presheaf.isLocallySurjective_iff _).2 fun U b x hx => by
      obtain ⟨V, hV, hxV, a, ha⟩ := h U b x hx
      exact ⟨V, hV, ⟨a, ha⟩, hxV⟩
  have hls : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map φ) := h'
  have : Epi ((SheafOfModules.toSheaf _).map φ) := Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf _).epi_of_epi_map this

/-- Morphisms of modules commute with restriction of sections. -/
private theorem modules_hom_app_res {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G)
    {A B : X.Opens} (i : A ⟶ B) (x : Γ(F, B)) :
    φ.app A (F.presheaf.map i.op x) = G.presheaf.map i.op (φ.app B x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congrArg (fun f => f x) (congrArg ConcreteCategory.hom (φ.mapPresheaf.naturality i.op))

/-- **Relative generation from a section generating near each point.** If every point `x` of `T`
has an open `V ∋ f(x)` and a section of `F` over `f⁻¹(V)` which freely generates `F` near `x`,
then `f^* f_* F ⟶ F` is surjective. -/
private theorem epi_counit_of_forall_exists_isLocalGenerator {T Z : Scheme.{0}} (f : T ⟶ Z)
    (F : T.Modules)
    (h : ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V) (σ : Γ(F, f ⁻¹ᵁ V)) (U₀ : T.Opens) (_ : x ∈ U₀)
      (hU₀ : U₀ ≤ f ⁻¹ᵁ V), MMP.Mori.IsLocalGenerator F U₀ (F.presheaf.map (homOfLE hU₀).op σ)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  set A := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj F)
  refine epi_of_locally_surjective _ fun U b x hx => ?_
  obtain ⟨V, hxV, σ, U₀, hxU₀, hU₀, hgen⟩ := h x
  let y : Γ(A, f ⁻¹ᵁ V) := (adj.unit.app ((Scheme.Modules.pushforward f).obj F)).app V σ
  have hy : (adj.counit.app F).app (f ⁻¹ᵁ V) y = σ :=
    congrArg (fun ψ => (Scheme.Modules.Hom.app ψ V).hom σ) (adj.right_triangle_components F)
  have hVU₀ : U ⊓ U₀ ≤ U₀ := inf_le_right
  have hVU : U ⊓ U₀ ≤ U := inf_le_left
  set r := hgen.coord hVU₀ (F.presheaf.map (homOfLE hVU).op b)
  refine ⟨U ⊓ U₀, hVU, ⟨hx, hxU₀⟩, r • A.presheaf.map (homOfLE (hVU₀.trans hU₀)).op y, ?_⟩
  have hnat : (adj.counit.app F).app (U ⊓ U₀) (A.presheaf.map (homOfLE (hVU₀.trans hU₀)).op y) =
      F.presheaf.map (homOfLE (hVU₀.trans hU₀)).op ((adj.counit.app F).app (f ⁻¹ᵁ V) y) :=
    modules_hom_app_res (adj.counit.app F) (homOfLE (hVU₀.trans hU₀)) y
  change (adj.counit.app F).app (U ⊓ U₀) (r • A.presheaf.map (homOfLE (hVU₀.trans hU₀)).op y) =
    F.presheaf.map (homOfLE hVU).op b
  rw [Scheme.Modules.Hom.app_smul, hnat, hy, ← MMP.Mori.modules_res_res hVU₀ hU₀ σ]
  exact hgen.coord_smul_eq hVU₀ _

/-- **Generation of the adjoint on the floor gives relative generation of the restricted
adjoint.** Let `ι : T ⟶ Y` be the floor of a pair `(Y, B_Y)` on a normal complex variety of
dimension `n + 1`, with
normalization components `νᵢ : Tᵢ ⟶ T` and boundaries `Θᵢ`, such that the residues of local
generators of `𝒪_Y(m(K_Y + B_Y))` are exactly the local generators of the adjoint on `T` up to
units of `𝒪_T`. If over a neighbourhood of every point of `Z` a family of forms on the `Tᵢ` is
locally a multiple of a local generator of the adjoint, a unit multiple at the given point, then
`ι^* 𝒪_Y(E)` is generated over `Z` for some Cartier multiple `E = m'(K_Y + B_Y)`. -/
private theorem exists_epi_counit_of_isAdjointGeneratorOn
    {Y Z T : Scheme.{0}} {n : ℕ} (hn : 0 < n) [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY (n + 1)) {BY : QDivisor Y}
    (hBY : MMP.Mori.IsPair sY BY)
    (ι : T ⟶ Y) [IsClosedImmersion ι] [IsReduced T]
    {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents (ι ≫ sY) hfin) (Θ : ∀ i, QDivisor (N.X i))
    [∀ i, CompactSpace (N.X i)] (hdimN : ∀ i, topologicalKrullDim (N.X i) = n)
    (hstep : ∀ i, IsAdjunctionStep sY BY (N.n i ≫ ι) (Θ i)) (hle : ∀ P, BY.coeff P ≤ 1)
    (hdict : ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor →
      ∀ (W : Y.Opens) (τ : RationalPluriForms sY (n + 1) m), GeneratesOn BY m W τ →
        (∃ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n m,
          ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
            IsPoincareResidue sY (N.n i ≫ ι) n m τ (ρ i)) ∧
        ∀ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n m,
          (∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
            IsPoincareResidue sY (N.n i ≫ ι) n m τ (ρ i)) →
          (∀ i, ρ i ≠ 0) → IsAdjointGeneratorOn N n m Θ (ι ⁻¹ᵁ W) ρ ∧
          ∀ U : T.Opens, U ≤ ι ⁻¹ᵁ W → ∀ g : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n m,
            IsAdjointGeneratorOn N n m Θ U g →
            ∃ e : Γ(T, U)ˣ, ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
              g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom
                ((N.n i).app U (e : Γ(T, U))) • ρ i)
    (gY : Y ⟶ Z) {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hgen : ∀ m : ℕ, 0 < m → m₀ ∣ m → ∀ x : T, ∃ (V : Z.Opens) (_ : (ι ≫ gY) x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n m),
      (∀ y ∈ (ι ≫ gY) ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ (ι ≫ gY) ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n m), IsAdjointGeneratorOn N n m Θ U g) ∧
      ∀ (U : T.Opens), U ≤ (ι ≫ gY) ⁻¹ᵁ V → ∀ g : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n m,
        IsAdjointGeneratorOn N n m Θ U g →
        ∀ y ∈ U, ∃ (U' : T.Opens) (_ : y ∈ U') (_ : U' ≤ U) (a : Γ(T, U')),
          (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' a) • g i) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ E : Divisor Y,
      Divisor.toQDivisor E = (m' : ℚ) • (Divisor.toQDivisor KY + BY) ∧ E.IsCartier ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ gY)).counit.app
        ((Scheme.Modules.pullback ι).obj E.divisorialSheaf)) := by
  classical
  have : ∀ i, LocallyOfFiniteType (N.n i ≫ ι ≫ sY) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  have : ∀ i, LocallyOfFiniteType ((N.n i ≫ ι) ≫ sY) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hBq := isQCartier_add_of_isPair hBY hKY
  obtain ⟨c, hc, F, hF, hFc⟩ := hBq.exists_pos
  set M : ℕ := m₀ * c with hMdef
  have hMpos : 0 < M := Nat.mul_pos hm₀ hc
  set E : Divisor Y := (m₀ : ℤ) • F with hEdef
  have hEq : Divisor.toQDivisor E = (M : ℤ) • (Divisor.toQDivisor KY + BY) := by
    rw [hEdef, map_zsmul, hF, smul_smul, hMdef]
    push_cast
    ring_nf
  have hEc : E.IsCartier := hFc.zsmul _
  have hMC : ((M : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor := ⟨E, hEq, hEc⟩
  refine ⟨M, hMpos, E, by rw [hEq, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ], hEc, ?_⟩
  have := hEc.isInvertibleModule_divisorialSheaf
  obtain ⟨Fch, hFgen, hFrel⟩ := exists_chartForm hYn hKY hEq
  have hdimY : topologicalKrullDim Y = (n : ℕ) + 1 := by
    rw [hKY.topologicalKrullDim_eq]; norm_cast
  refine epi_counit_of_forall_exists_isLocalGenerator (ι ≫ gY) _ fun x => ?_
  obtain ⟨V, hxV, t, ht⟩ := hgen M hMpos (dvd_mul_right m₀ c) x
  set O := (ι ≫ gY) ⁻¹ᵁ V with hOdef
  -- local data at each point of `O`
  have data : ∀ y : O, ∃ (U' : T.Opens) (_ : y.1 ∈ U') (_ : U' ≤ O) (b : Γ(T, U'))
      (W : Y.Opens) (_ : U' ≤ ι ⁻¹ᵁ W) (ψ : (RationalFunctions Y)ˣ) (_ : E.IsLocalEquation W ψ)
      (ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n M),
      (∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
        IsPoincareResidue sY (N.n i ≫ ι) n M (Fch ψ) (ρ i)) ∧ (∀ i, ρ i ≠ 0) ∧
      (y.1 = x → IsUnit b) ∧
      ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
        t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' b) • ρ i := by
    intro y
    obtain ⟨U₀, hyU₀, hU₀V, g, hg₀⟩ := ht.1 y.1 y.2
    obtain ⟨U, hyU, hUU₀, a, ha, hta⟩ := ht.2 U₀ hU₀V g hg₀ y.1 hyU₀
    have hg := isAdjointGeneratorOn_mono hUU₀ hg₀
    have hUV := hUU₀.trans hU₀V
    obtain ⟨W, hyW, ψ, hψ⟩ := hEc (ι y.1)
    have hτ := hFgen W ψ hψ
    obtain ⟨ρ', hρ'⟩ := (hdict M hMpos hMC W (Fch ψ) hτ).1
    let ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) n M := fun i =>
      if ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty then ρ' i else g i
    have hρres : ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
        IsPoincareResidue sY (N.n i ≫ ι) n M (Fch ψ) (ρ i) := fun i h => by
      simp only [ρ, ite_eq_left h]
      exact hρ' i h
    have hρ0 : ∀ i, ρ i ≠ 0 := by
      intro i
      by_cases h : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty
      · simp only [ρ, ite_eq_left h]
        obtain ⟨z, hz⟩ := h
        have hgW : (N.n i ≫ ι) (genericPoint (N.X i)) ∈ W :=
          ((genericPoint_spec (N.X i)).specializes trivial).map
            (N.n i ≫ ι).base.hom.continuous |>.mem_open W.isOpen hz
        exact isPoincareResidue_ne_zero_of_generatesOn hYn (n := n) hn hdimY
          (hstep i) (hdimN i) hle hMpos hτ hgW (hρ' i ⟨z, hz⟩)
      · simp only [ρ, ite_eq_right h]
        exact (hg.1 i).1
    set U' : T.Opens := U ⊓ ι ⁻¹ᵁ W with hU'def
    obtain ⟨e, he⟩ := ((hdict M hMpos hMC W (Fch ψ) hτ).2 ρ hρres hρ0).2 U' inf_le_right g
      (isAdjointGeneratorOn_mono inf_le_left hg)
    refine ⟨U', ⟨hyU, hyW⟩, inf_le_left.trans hUV,
      T.presheaf.map (homOfLE (inf_le_left : U' ≤ U)).op a * e, W, inf_le_right, ψ, hψ, ρ,
      hρres, hρ0, fun h => ((ha h).map (T.presheaf.map (homOfLE inf_le_left).op).hom).mul
        e.isUnit, fun i hi => ?_⟩
    have : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    rw [hta i inferInstance, he i hi, smul_smul, map_mul, map_mul,
      germToFunctionField_app_res N i inf_le_left a]
  choose U' hyU' hU'O b W hW ψ hψ ρ hρres hρ0 hbx ht' using data
  -- the local sections `b_y · ψ_y⁻¹|_T`
  set FT := (Scheme.Modules.pullback ι).obj E.divisorialSheaf with hFT
  set u := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app E.divisorialSheaf with hu
  let pb : ∀ A : Y.Opens, Γ(E.divisorialSheaf, A) → Γ(FT, ι ⁻¹ᵁ A) := fun A a => u.app A a
  have hpbnat : ∀ (A B : Y.Opens) (h : A ≤ B) (a : Γ(E.divisorialSheaf, B)),
      FT.presheaf.map (homOfLE (ι.preimage_mono h)).op (pb B a) =
        pb A (E.divisorialSheaf.presheaf.map (homOfLE h).op a) := fun A B h a =>
    (modules_hom_app_res u (homOfLE h) a).symm
  have hpbsmul : ∀ (A : Y.Opens) (r : Γ(Y, A)) (a : Γ(E.divisorialSheaf, A)),
      pb A (r • a) = ι.app A r • pb A a := fun A r a =>
    Scheme.Modules.Hom.app_smul u r a
  let s : ∀ y : O, Γ(FT, U' y) := fun y =>
    FT.presheaf.map (homOfLE (hW y)).op (pb (W y) (hψ y).invSection)
  let σ : ∀ y : O, Γ(FT, U' y) := fun y => b y • s y
  have hcompat : TopCat.Presheaf.IsCompatible FT.presheaf U' σ := by
    intro y z
    have hQW : U' y ⊓ U' z ≤ ι ⁻¹ᵁ (W y ⊓ W z) := fun p hp => ⟨hW y hp.1, hW z hp.2⟩
    -- the transition function `r` on `W_y ∩ W_z`
    have hgz := (hψ z).isLocalGenerator_invSection
    set r := hgz.coord (inf_le_right : W y ⊓ W z ≤ W z)
      (E.divisorialSheaf.presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op
        (hψ y).invSection) with hrdef
    have hr : r • E.divisorialSheaf.presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op
        (hψ z).invSection =
        E.divisorialSheaf.presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op
          (hψ y).invSection :=
      hgz.coord_smul_eq _ _
    have hs : ∀ v : O, ∀ (hv : U' y ⊓ U' z ≤ U' v) (hvW : W y ⊓ W z ≤ W v),
        FT.presheaf.map (homOfLE hv).op (s v) =
          FT.presheaf.map (homOfLE hQW).op
            (pb (W y ⊓ W z) (E.divisorialSheaf.presheaf.map (homOfLE hvW).op
              (hψ v).invSection)) := by
      intro v hv hvW
      rw [← hpbnat _ _ hvW, MMP.Mori.modules_res_res]
      exact (MMP.Mori.modules_res_res hQW (ι.preimage_mono hvW) _).symm
    set rT : Γ(T, U' y ⊓ U' z) := T.presheaf.map (homOfLE hQW).op (ι.app (W y ⊓ W z) r)
      with hrT
    have hsyz : FT.presheaf.map (homOfLE (inf_le_left : U' y ⊓ U' z ≤ U' y)).op (s y) =
        rT • FT.presheaf.map (homOfLE (inf_le_right : U' y ⊓ U' z ≤ U' z)).op (s z) := by
      rw [hs y inf_le_left inf_le_left, hs z inf_le_right inf_le_right, ← hr, hpbsmul]
      exact MMP.Mori.modules_res_smul hQW _ _
    -- the coefficients satisfy `b_y r = b_z` on `U'_y ∩ U'_z`
    have hrel : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W y ⊓ W z),
        (((ψ y)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z =
          Y.presheaf.germ (W y ⊓ W z) _ hZ r *
            (((ψ z)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z := fun Z hZ =>
      (congrArg (fun a : Γ(E.divisorialSheaf, W y ⊓ W z) =>
        (show E.divisorialSubmodule (W y ⊓ W z) from a).1 ⟨Z, hZ⟩) hr).symm
    have hb : T.presheaf.map (homOfLE (inf_le_left : U' y ⊓ U' z ≤ U' y)).op (b y) * rT =
        T.presheaf.map (homOfLE (inf_le_right : U' y ⊓ U' z ≤ U' z)).op (b z) := by
      refine mul_eq_of_smul_eq N (t := t) (ρ := ρ y) (ρ' := ρ z) (fun i hi => ?_) (hρ0 z)
        (fun i hi => ?_) (fun i hi => ?_)
      · have := hi
        set p := hi.some.1
        have hp : p ∈ N.n i ⁻¹ᵁ (U' y ⊓ U' z) := hi.some.2
        have hpW : (N.n i ≫ ι) p ∈ W y ⊓ W z := hQW hp
        have : Nonempty (W y ⊓ W z : Y.Opens) := ⟨⟨_, hpW⟩⟩
        have : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ (W y ⊓ W z)) := ⟨⟨p, hpW⟩⟩
        have : Nonempty (N.n i ⁻¹ᵁ (ι ⁻¹ᵁ (W y ⊓ W z))) := ⟨⟨p, hpW⟩⟩
        have hgW : (N.n i ≫ ι) (genericPoint (N.X i)) ∈ W y ⊓ W z :=
          ((genericPoint_spec (N.X i)).specializes trivial).map
            (N.n i ≫ ι).base.hom.continuous |>.mem_open (W y ⊓ W z).isOpen hpW
        have h1 := isPoincareResidue_eq_germ_smul (hstep i) hgW r
          (hFrel _ _ (W y ⊓ W z) r hrel) (hρres y i ⟨p, hpW.1⟩) (hρres z i ⟨p, hpW.2⟩)
        rw [h1]
        congr 1
        rw [hrT, germToFunctionField_app_res N i hQW (ι.app (W y ⊓ W z) r)]
        rfl
      · have := hi
        have : Nonempty (N.n i ⁻¹ᵁ U' y) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
        rw [germToFunctionField_app_res N i (inf_le_left : U' y ⊓ U' z ≤ U' y) (b y)]
        exact ht' y i inferInstance
      · have := hi
        have : Nonempty (N.n i ⁻¹ᵁ U' z) := ⟨⟨hi.some.1, hi.some.2.2⟩⟩
        rw [germToFunctionField_app_res N i (inf_le_right : U' y ⊓ U' z ≤ U' z) (b z)]
        exact ht' z i inferInstance
    change FT.presheaf.map (homOfLE (inf_le_left : U' y ⊓ U' z ≤ U' y)).op (b y • s y) =
      FT.presheaf.map (homOfLE (inf_le_right : U' y ⊓ U' z ≤ U' z)).op (b z • s z)
    rw [MMP.Mori.modules_res_smul, MMP.Mori.modules_res_smul, hsyz, smul_smul, hb]
  obtain ⟨σO, hσO, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := ⟨FT.presheaf, FT.isSheaf⟩) U' O
    (fun y => homOfLE (hU'O y))
    (fun z hz => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hyU' ⟨z, hz⟩⟩) σ
    hcompat
  have hxO : x ∈ O := hxV
  refine ⟨V, hxV, σO, U' ⟨x, hxO⟩, hyU' _, hU'O _, ?_⟩
  rw [hσO ⟨x, hxO⟩]
  exact isLocalGenerator_smul_of_isUnit (isLocalGenerator_res
    (isLocalGenerator_pullback_unit ι _ (hψ _).isLocalGenerator_invSection) (hW _))
    (hbx _ rfl)

end FloorGluing

/-- **The complement restricts to a floor component.** Let `(S, B_S)` arise from `(Y, B)` by an
adjunction step `j : S ⟶ Y` along a prime divisor `P` of coefficient one, `Y` a normal complex
variety of dimension `n + 1 ≥ 2` with `K_Y + B` `ℚ`-Cartier and `B ≤ 1`. Let `A ≥ 0` be
`ℚ`-Cartier with `(B + A) ≤ 1`, and `K_Y + B + A ∼_ℚ G` with `𝒪_Y(m₀G) ≅ g^*M` for an invertible
`M` on `Z`. Then `A_S = j^*A` is effective `ℚ`-Cartier and there is `G_S ∼_ℚ K_S + B_S + A_S`
with `𝒪_S(m₀G_S) ≅ (g ∘ j)^*M`: move `m₀G` off `P` by a principal divisor and pull back. -/
private theorem exists_floor_component_complement {Y Z S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY) {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim Y = n + 1) {K : Divisor Y} (hK : K.IsCanonicalDivisor sY (n + 1))
    {B : QDivisor Y} (hBq : (Divisor.toQDivisor K + B).IsQCartier) (hle : ∀ P, B.coeff P ≤ 1)
    {A : QDivisor Y} (hA : 0 ≤ A) (hAq : A.IsQCartier) (hAle : ∀ P, (B + A).coeff P ≤ 1)
    {G : QDivisor Y} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (g : Y ⟶ Z) (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M] {m₀ : ℕ} (hm₀ : 0 < m₀)
    {L : Divisor Y} (hL : Divisor.toQDivisor L = (m₀ : ℤ) • G)
    (eL : L.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj M)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {j : S ⟶ Y} {BS : QDivisor S} (hS : IsAdjunctionStep sY B j BS) {KS : Divisor S}
    (hKS : KS.IsCanonicalDivisor (j ≫ sY) n) :
    ∃ AS : QDivisor S, 0 ≤ AS ∧ AS.IsQCartier ∧ ∃ GS : QDivisor S,
      (Divisor.toQDivisor KS + BS + AS).QLinearlyEquivalent GS ∧
      ∃ LS : Divisor S, Divisor.toQDivisor LS = (m₀ : ℤ) • GS ∧
        Nonempty (LS.divisorialSheaf ≅ (Scheme.Modules.pullback (j ≫ g)).obj M) := by
  classical
  obtain ⟨hSn, P, hP1, hPr, hci, -⟩ := id hS
  have := hci
  have : LocallyOfFiniteType (j ≫ sY) := hSn.1.toLocallyOfFiniteType
  have hBP : B.coeff P = 1 := le_antisymm (hle P) hP1
  have hAP : A.coeff P = 0 := by
    have h1 := hAle P
    rw [DivisorWithCoeffs.coeff_add, hBP] at h1
    exact le_antisymm (by linarith) (hA P)
  -- the pull-back of `A`
  have hAj := MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hPr hAP
  have hpbA := QDivisor.isPullback_pullback (f := j) hAq hAj
  set AS := A.pullback hAq hAj with hASdef
  -- a form with a simple pole along `P` and its residue
  obtain ⟨x, hx⟩ := exists_ne_of_topologicalKrullDim_pos hn hKS.topologicalKrullDim_eq
    (genericPoint S)
  obtain ⟨Q⟩ := nonempty_primeDivisor_of_ne_genericPoint hx
  obtain ⟨σ, hσ0, hσP, -, ρ, hρ, hρ0, -⟩ :=
    exists_form_of_residue_order sY hYn hdim j hSn P hPr Q
  obtain ⟨φ, hφ⟩ : (divisorOfForm σ).LinearlyEquivalent K := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hK hσ0
  obtain ⟨ψ, hψ⟩ : (divisorOfForm ρ).LinearlyEquivalent KS := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSn hKS hρ0
  have hDq : (Divisor.toQDivisor (divisorOfForm σ) + B).IsQCartier :=
    hBq.add_of_linearlyEquivalent (Divisor.LinearlyEquivalent.symm ⟨φ, hφ⟩)
  obtain ⟨hgen, hpb⟩ :=
    hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hPr σ hσ0 hσP ρ hρ hDq
  -- `L` is Cartier; move it off `P`
  have hLc := isCartier_of_iso_pullback g M eL
  obtain ⟨ϖ, hϖ⟩ := MMP.Positivity.PrimeDivisor.exists_ord_eq_one P
  set ξ : (RationalFunctions Y)ˣ := ϖ ^ (-(L.coeff P)) with hξdef
  set L' : Divisor Y := L + principalDivisor ξ with hL'def
  have hL'P : L'.coeff P = 0 := by
    simp [hL'def, ξ, coeff_principalDivisor, PrimeDivisor.ord_zpow, hϖ]
  have hL'L : L'.LinearlyEquivalent L := ⟨ξ, by simp [hL'def]⟩
  have hL'c : L'.IsCartier := hLc.add (Divisor.isCartier_principalDivisor ξ)
  have hL'j := MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hPr hL'P
  obtain ⟨L'S, hpL'⟩ := hL'c.exists_isPullback hL'j
  -- the `ℚ`-divisor `D = (div σ + B) + A - m₀⁻¹ L'` and its pull-back
  set c : ℚ := -(m₀ : ℚ)⁻¹ with hc
  set DY : QDivisor Y := (Divisor.toQDivisor (divisorOfForm σ) + B) + A +
    c • Divisor.toQDivisor L' with hDYdef
  have hσPc : (divisorOfForm σ).coeff P = -1 := by rw [coeff_divisorOfForm, hσP]
  have hL'q : (Divisor.toQDivisor L').IsQCartier := QDivisor.isQCartier_toQDivisor hL'c
  have hcL'q := isQCartier_qsmul hL'q c
  have hDAq := hDq.add hAq
  have hDYq : DY.IsQCartier := hDAq.add hcL'q
  have hDYP : DY.coeff P = 0 := by
    simp only [hDYdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, hσPc, hBP, hAP, hL'P, smul_eq_mul]
    norm_num
  have sp : ∀ {D : QDivisor Y}, D.coeff P = 0 →
      ∀ T : irreducibleComponents S, j (componentGenericPoint S T) ∉ D.supp := fun h =>
    MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hPr h
  have hpbL' := QDivisor.isPullback_toQDivisor hL'c (sp (by
    rw [Divisor.coeff_toQDivisor, hL'P]; rfl)) hpL'
  have hpbcL' := isPullback_qsmul hL'q c (sp (by
    rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, hL'P]; simp)) hpbL'
  have hpbDA := isPullback_add hDq hAq (sp (by
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      hσPc, hBP, hAP]; norm_num)) hpb hpbA
  have hpbDY := isPullback_add hDAq hcL'q (sp hDYP) hpbDA hpbcL'
  set DS : QDivisor S := (Divisor.toQDivisor (divisorOfForm ρ) + BS) + AS +
    c • Divisor.toQDivisor L'S with hDSdef
  -- `k m₀ D` is principal on `Y`
  obtain ⟨k, hk, φ₁, hφ₁⟩ := hDG
  set χ : (RationalFunctions Y)ˣ := φ₁ ^ (m₀ : ℤ) * φ ^ ((k * m₀ : ℕ) : ℤ) * ξ ^ (-(k : ℤ))
    with hχdef
  have hχ : ((k * m₀ : ℕ) : ℤ) • DY = Divisor.toQDivisor (principalDivisor χ) := by
    have e1 : Divisor.toQDivisor (principalDivisor χ) =
        (m₀ : ℤ) • Divisor.toQDivisor (principalDivisor φ₁) +
          ((k * m₀ : ℕ) : ℤ) • Divisor.toQDivisor (principalDivisor φ) -
          (k : ℤ) • Divisor.toQDivisor (principalDivisor ξ) := by
      ext E
      simp only [χ, Divisor.coeff_toQDivisor, coeff_principalDivisor, PrimeDivisor.ord_mul,
        PrimeDivisor.ord_zpow, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    have hφq : Divisor.toQDivisor (divisorOfForm σ) - Divisor.toQDivisor K =
        Divisor.toQDivisor (principalDivisor φ) := by rw [← hφ, map_sub]
    have hξq : Divisor.toQDivisor L' - Divisor.toQDivisor L =
        Divisor.toQDivisor (principalDivisor ξ) := by
      rw [hL'def, map_add]; abel
    have hcm : (m₀ : ℚ) * c = -1 := by
      rw [hc, mul_neg, mul_inv_cancel₀ (by exact_mod_cast hm₀.ne')]
    rw [e1, hDYdef]
    ext E
    have a1 := congrArg (fun D : QDivisor Y => D.coeff E) hφ₁
    have a2 := congrArg (fun D : QDivisor Y => D.coeff E) hφq
    have a3 := congrArg (fun D : QDivisor Y => D.coeff E) hξq
    have a4 := congrArg (fun D : QDivisor Y => D.coeff E) hL
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul] at a1 a2 a3 a4 ⊢
    push_cast at a1 a2 a3 a4 ⊢
    linear_combination (m₀ : ℚ) * a1 + ((k : ℚ) * m₀) * a2 - (k : ℚ) * a3 -
      (k : ℚ) * a4 + ((k : ℚ) * (Divisor.toQDivisor L').coeff E) * hcm
  have hχP : (principalDivisor χ).coeff P = 0 := by
    have := congrArg (fun D : QDivisor Y => D.coeff P) hχ
    simp only [DivisorWithCoeffs.coeff_smul, hDYP, smul_zero, Divisor.coeff_toQDivisor] at this
    exact_mod_cast this.symm
  have hχj := MMP.CyclicChartDifferent.map_componentGenericPoint_notMem_supp j P hPr hχP
  have hχc := Divisor.isCartier_principalDivisor χ
  have h2 := QDivisor.isPullback_toQDivisor hχc (sp (by
      rw [Divisor.coeff_toQDivisor, hχP]; rfl))
    (Divisor.isPullback_principalDivisor χ hχj)
  have h1 := isPullback_zsmul hDYq ((k * m₀ : ℕ) : ℤ) (sp (by
    rw [DivisorWithCoeffs.coeff_smul, hDYP, smul_zero])) hpbDY
  have h1' := isPullback_congr hχ rfl h1 (hB₂ := sp (by
    rw [Divisor.coeff_toQDivisor, hχP]; rfl))
  have hDS : ((k * m₀ : ℕ) : ℤ) • DS = Divisor.toQDivisor (principalDivisor
      (pullbackRationalFunction j χ hχj)) :=
    ((QDivisor.isQCartier_toQDivisor hχc).existsUnique_isPullback _).unique h1' h2
  -- the divisors on `S`
  set GS : QDivisor S := (m₀ : ℚ)⁻¹ • Divisor.toQDivisor L'S with hGSdef
  refine ⟨AS, nonneg_of_isPullback hA hAq hpbA, hpbA.isQCartier hAq, GS, ?_, L'S, ?_, ⟨?_⟩⟩
  · refine ⟨k * m₀, Nat.mul_pos hk hm₀,
      pullbackRationalFunction j χ hχj * ψ ^ (-((k * m₀ : ℕ) : ℤ)), ?_⟩
    have hψq : Divisor.toQDivisor (divisorOfForm ρ) - Divisor.toQDivisor KS =
        Divisor.toQDivisor (principalDivisor ψ) := by rw [← hψ, map_sub]
    ext E
    have a1 := congrArg (fun D : QDivisor S => D.coeff E) hDS
    have a2 := congrArg (fun D : QDivisor S => D.coeff E) hψq
    simp only [hDSdef, hGSdef, hc, Divisor.coeff_toQDivisor, coeff_principalDivisor,
      PrimeDivisor.ord_mul, PrimeDivisor.ord_zpow, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      zsmul_eq_mul] at a1 a2 ⊢
    push_cast at a1 a2 ⊢
    linear_combination a1 - ((k : ℚ) * m₀) * a2
  · exact (natCast_zsmul_inv_smul hm₀ _).symm
  · exact hpL'.divisorialSheafIso (hBc := hL'c) ≪≫
      (Scheme.Modules.pullback j).mapIso (hL'L.divisorialSheafIso ≪≫ eL) ≪≫
      (Scheme.Modules.pullbackComp j g).app M

/-! ### The whole floor -/

/-- **The restriction of the adjoint to the whole floor is relatively generated.** For a
complemented `ℚ`-factorial projective dlt threefold `(Y, B)` over `Z` with nonempty floor
`T = ⌊B⌋`, some Cartier multiple `E = m(K_Y + B)` has `𝒪_Y(E)|_T` generated over `Z`: the floor
dictionary makes `(T, Δ_T; (K_Y + B)|_T)` an sdlt adjoint surface, the complement restricts to
every floor component (`exists_floor_component_complement`), the complemented sdlt surface theorem
generates the adjoint of `T` over `Z`, and its local generators are unit multiples of residues of
local generators of `𝒪_Y(E)`, so that the sections glue to sections of `𝒪_Y(E)|_T`. -/
private theorem floor_epi {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [QuasiCompact sY]
    (hYp : Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hY3 : topologicalKrullDim Y = 3) {K : Divisor Y} {B : QDivisor Y} (hB : 0 ≤ B)
    (hdlt : Mori.IsDltPair sY 3 K B) (hdltI : MMP.Intersection.IsDltPair sY B)
    (hZ : Mori.IsProjectiveVariety ℂ sZ) (g : Y ⟶ Z) (hg : g ≫ sZ = sY)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sY g) {A : QDivisor Y} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlcI : MMP.Intersection.IsLogCanonicalPair sY (B + A))
    {G : QDivisor Y} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor Y, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback g).obj M))
    (hT : B.roundDown ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor Y,
      Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor K + B) ∧ E.IsCartier ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction
          (B.roundDown.suppIdeal.subschemeι ≫ g)).counit.app
        ((Scheme.Modules.pullback B.roundDown.suppIdeal.subschemeι).obj E.divisorialSheaf)) := by
  classical
  set ι := B.roundDown.suppIdeal.subschemeι with hιdef
  have : IsReduced B.roundDown.suppIdeal.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrange : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set Y) := by
    have h1 : Set.range ι.base = (B.roundDown.suppIdeal.support : Set Y) :=
      Scheme.IdealSheafData.range_subschemeι _
    rw [h1, DivisorWithCoeffs.suppIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext x
    simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, Set.mem_iUnion,
      Finsupp.mem_support_iff, DivisorWithCoeffs.coeff_apply, exists_prop]
  have hpairF : MMP.Fourfold.IsPair sY B := ⟨inferInstance, inferInstance, hdltI.1.1, fun P => hB P⟩
  obtain ⟨-, hfin, N, Δ, Θ, hsdlt, hadj, -, hres⟩ :=
    isCMScheme_and_exists_isSdltAdjointPair_of_isDltPair (n := 2) (by rw [hY3]; rfl)
      hdlt.1.2.1 hYp hQ hpairF hdltI hT ι hrange
  have hci : ∀ i, IsClosedImmersion (N.n i ≫ ι) := fun i => by
    obtain ⟨-, P, -, -, hc, -⟩ := hadj i
    exact hc
  have : ∀ i, CompactSpace (N.X i) := fun i =>
    haveI := hci i
    QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ ι)
  have : ∀ i, QuasiCompact (N.n i ≫ ι ≫ sY) := fun i => by
    have := hci i
    rw [← Category.assoc]
    infer_instance
  choose KN hKN using hsdlt.exists_isDltPair
  have hKNc : ∀ i, (KN i).IsCanonicalDivisor (N.n i ≫ ι ≫ sY) 2 := fun i => (hKN i).1.2.1
  have hKNc' : ∀ i, (KN i).IsCanonicalDivisor ((N.n i ≫ ι) ≫ sY) 2 := fun i => by
    simpa only [Category.assoc] using hKNc i
  have hYn : IsNormalVariety ℂ sY := hdltI.1.1.1
  have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  have : IsSeparated sY := hYn.1.toIsSeparated
  have hK : K.IsCanonicalDivisor sY (2 + 1) := hdlt.1.2.1
  have hdim : topologicalKrullDim Y = (2 : ℕ) + 1 := by rw [hY3]; rfl
  have hBq : (Divisor.toQDivisor K + B).IsQCartier := hdlt.1.2.2
  have hle : ∀ P, B.coeff P ≤ 1 := hdltI.2.1
  have hnefc : ∀ i, (Divisor.toQDivisor (KN i) + Θ i).IsRelativelyNef (N.n i ≫ ι ≫ sY)
      (N.n i ≫ ι ≫ g) := fun i => by
    have := hci i
    have h := isRelativelyNef_of_isAdjunctionStep (j := N.n i ≫ ι) hYn (n := 2) (by norm_num)
      hdim hK hBq hnef (hadj i) (hKNc' i)
    simpa only [Category.assoc] using h
  obtain ⟨m₀, hm₀, L, hL, ⟨eL⟩⟩ := hGM
  have hcomp := fun i => exists_floor_component_complement (j := N.n i ≫ ι) hYn (n := 2)
    (by norm_num) hdim hK hBq hle hA hAq (coeff_le_one_of_isLogCanonicalPair hlcI) hDG g M hm₀
    hL eL (hadj i) (hKNc' i)
  choose AS hAS0 hASq GS hGS LS hLS hLSe using hcomp
  obtain ⟨ms, hms, hgen⟩ := hsdlt.exists_isAdjointGeneratorOn_of_add_qLinearlyEquivalent
    (fun i => haveI := hci i; IsClosedImmersion.of_comp (N.n i) ι) hZ
    (ι ≫ g) (by rw [Category.assoc, hg]) hKNc hnefc hAS0 hASq hGS M
    ⟨m₀, hm₀, fun i => ⟨LS i, hLS i, ⟨(hLSe i).some ≪≫ eqToIso (by rw [Category.assoc])⟩⟩⟩
  exact exists_epi_counit_of_isAdjointGeneratorOn (n := 2) (by norm_num) hYn hK hdltI.1.1 ι N Θ
    (fun i => by exact_mod_cast (hKNc i).topologicalKrullDim_eq) hadj hle hres g hms hgen

/-! ### The floor of the pencil model -/

/-- **The floor case.** On the crepant dlt model `(Y, B_Y)` of the pencil lemma with nonempty
floor `T = ⌊B_Y⌋`, the restriction of `K_Y + B_Y` to the whole floor is semiample over `Z` by the
complemented sdlt surface theorem, and the floor-union criterion makes `K_Y + B_Y` semiample. -/
private theorem floor_case {X Z Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    [IsIntegral Z]
    {K : Divisor X} {B : QDivisor X} (hKB : Mori.IsDltPair sX 3 K B)
    (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hcon : MMP.Fourfold.IsContraction sX sZ f)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA : 0 ≤ A) (hAq : A.IsQCartier)
    (hlcI : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ Z)
    (KY : Divisor Y) (BY : QDivisor Y) (hYp : Mori.IsProjectiveVariety ℂ sY)
    (hgY : g ≫ sZ = sY) (hYdlt : Mori.IsDltPair sY 3 KY BY)
    (hW : ∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ Y) (ΔW : QDivisor W)
        (hWX : IsNormalVariety ℂ (p ≫ sX)) (hWY : IsNormalVariety ℂ (q ≫ sY))
        (hp : IsBirationalMorphism p) (hq : IsBirationalMorphism q),
        IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ p ≫ f = q ≫ g ∧
          IsCrepantBoundary sX 3 K B p hWX hp ΔW ∧ IsCrepantBoundary sY 3 KY BY q hWY hq ΔW)
    (hP : ∃ P : QDivisor Y, 0 ≤ P ∧ P.IsQCartier ∧
        (∀ E : MMP.Mori.PrimeDivisor Y, P.coeff E ≠ 0 ↔ BY.roundDown.coeff E ≠ 0) ∧
        ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ ≤ δ₀ →
          QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY - δ • P))
    (hT : BY.roundDown ≠ 0) :
    QDivisor.IsRelativelySemiample g (Divisor.toQDivisor KY + BY) := by
  obtain ⟨P, hP0, hPq, hPsupp, δ₀, hδ₀, hsemi⟩ := hP
  have hKY := hYdlt.1.2.1
  have hY3 : topologicalKrullDim Y = 3 := hKY.topologicalKrullDim_eq
  have hYv := (Mori.isProjectiveVariety_iff ℂ sY).mp hYp
  have : AlgebraicGeometry.IsVariety ℂ sY := hYv.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hYdltI : MMP.Intersection.IsDltPair sY BY :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sY hKY BY).mpr hYdlt
  obtain ⟨AY, hAY0, hAYq, hlcAY, GY, hDGY, hGMY⟩ := exists_complement_on_model sX sZ hKB f
    hcon hA hAq hlcI hDG M hGM sY g KY BY hgY hYdlt hW
  have hnefY : (Divisor.toQDivisor KY + BY).IsRelativelyNef sY g := by
    obtain ⟨W, p, q, ΔW, hWX, hWY, hp, hq, hpp, hqp, hpq, hcX, hcY⟩ := hW
    have : AlgebraicGeometry.IsVariety ℂ sX := hKB.1.1.1
    have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hWX.1
    have : IsIntegral W := hWX.1.toIsIntegral
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
    have : IsNormal W := hWX.2
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
    have : IsProper p := isProper_of_isProjectiveMorphism p hpp
    have : IsProper q := isProper_of_isProjectiveMorphism q hqp
    have : AlgebraicGeometry.IsVariety ℂ (q ≫ sY) := hWY.1
    have hs : p ≫ sX = q ≫ sY := by
      rw [← hcon.comp_eq, ← hgY, ← Category.assoc, hpq, Category.assoc]
    obtain ⟨KW, KW', φ, -, -, ⟨_, hpbX⟩, -, -, ⟨_, hpbY⟩, hφ⟩ :=
      crepant_model_setup hKB.1.isPair hKB.1.2.1 hYdlt.1.isPair hKY p q hWX hWY hp hq hs hcX hcY
    have hnefW := isRelativelyNef_add_principalDivisor
      (isRelativelyNef_of_isPullback p f hnef.1 hpbX hnef) φ
    have heq : Divisor.toQDivisor KW + ΔW + Divisor.toQDivisor (principalDivisor φ) =
        Divisor.toQDivisor KW' + ΔW := by
      rw [← hφ, map_sub]; abel
    rw [heq, hpq] at hnefW
    have : IsDominant q := hq.isDominant
    exact isRelativelyNef_of_isPullback_of_surjective q g hYdlt.1.2.2 hpbY
      (isRelativelyNef_congr_structure hs hnefW)
  obtain ⟨Y', _, _, _, _, e, _, _, he, hY'n, KY', BY', AY', GY', hY'p, hY'Q, hY'3, -, hBY'0,
    hY'dlt, hY'dltI, hnefY', hAY'0, hAY'q, -, hlcY', hDGY', hGMY', ⟨hBpb, hpbY⟩, hcrepY, hexcY,
    hfinY⟩ := transport sY hYp hY3 hKY hYdltI.1 g hnefY hAY0 hAYq hlcAY hDGY M hGMY
  have : AlgebraicGeometry.IsVariety ℂ (e ≫ sY) := hY'n.1
  have : IsDominant e := he.isDominant
  obtain ⟨P', ⟨_, hP'pb⟩, hP'0, hP'q, hP'supp, hT'⟩ :=
    pencil_support sY hYdlt hYdltI e he hY'n hcrepY hexcY hP0 hPq hPsupp hT
  have hKBq : (Divisor.toQDivisor KY + BY).IsQCartier := hYdlt.1.2.2
  have hsemi' : ∀ᶠ ε : ℚ in nhdsWithin 0 (Set.Ioi 0),
      QDivisor.IsRelativelySemiample (e ≫ g) (Divisor.toQDivisor KY' + BY' - ε • P') := by
    filter_upwards [Ioc_mem_nhdsGT hδ₀] with ε hε
    have hεq : (-ε • P).IsQCartier := isQCartier_qsmul hPq (-ε)
    have h1 := isPullback_add hKBq hεq
      (map_componentGenericPoint_notMem_supp_of_isQCartier e (hKBq.add hεq)) hpbY
      (isPullback_qsmul hPq (-ε) (map_componentGenericPoint_notMem_supp_of_isQCartier e hεq)
        hP'pb)
    have hDεq : (Divisor.toQDivisor KY + BY - ε • P).IsQCartier := by
      rw [sub_eq_add_neg, ← neg_smul]; exact hKBq.add hεq
    have h2 := isPullback_congr (show Divisor.toQDivisor KY + BY + -ε • P =
        Divisor.toQDivisor KY + BY - ε • P by rw [neg_smul, ← sub_eq_add_neg])
      (show Divisor.toQDivisor KY' + BY' + -ε • P' = Divisor.toQDivisor KY' + BY' - ε • P' by
        rw [neg_smul, ← sub_eq_add_neg]) h1
      (hB₂ := map_componentGenericPoint_notMem_supp_of_isQCartier e hDεq)
    exact isRelativelySemiample_pullback e g h2 (hsemi ε hε.1 hε.2)
  have hepi := floor_epi (e ≫ sY) sZ hY'p hY'Q hY'3 hBY'0 hY'dlt hY'dltI hZ (e ≫ g)
    (by rw [Category.assoc, hgY]) hnefY' hAY'0 hAY'q hlcY' hDGY' M hGMY' hT'
  have hZv := (Mori.isProjectiveVariety_iff ℂ sZ).mp hZ
  have : AlgebraicGeometry.IsVariety ℂ sZ := hZv.1
  have hfp : IsProjectiveMorphism (e ≫ g) := IsProjectiveMorphism.of_comp (e ≫ g) sZ
    (by rw [Category.assoc, hgY]; exact ((Mori.isProjectiveVariety_iff ℂ _).mp hY'p).2)
  have hs' := QDivisor.isRelativelySemiample_of_isDltPair_of_restrict_roundDown (e ≫ sY) sZ hZ
    (e ≫ g) (by rw [Category.assoc, hgY]) hfp KY' BY' hY'Q hY'dlt P' hP'0 hP'q
    (by
      ext x
      rw [SetLike.mem_coe, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff,
        DivisorWithCoeffs.mem_supp_iff]
      exact exists_congr fun E => and_congr_left fun _ => hP'supp E) hsemi' hepi
  exact isRelativelySemiample_of_pullback hYdlt.1.1 e hY'n hfinY g hKBq hpbY hs'

/-! ### The case of a contraction onto a surface or a threefold -/

/-- **The contraction case.** If a component of `⌊B⌋` dominates a surface base this is
`MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent_of_dense`;
otherwise the pencil lemma gives a crepant dlt model `(Y, B_Y)` whose semiampleness is
equivalent to that of `(X, B)`, and the floor case concludes. -/
private theorem core_contraction {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] [IsIntegral Z] [IsNormal Z]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : Mori.IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (hZ23 : topologicalKrullDim Z = 2 ∨ topologicalKrullDim Z = 3) (f : X ⟶ Z)
    (hcon : MMP.Fourfold.IsContraction sX sZ f)
    (hconn : ∀ z : Z, _root_.IsConnected (f ⁻¹' {z}))
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A))
    (hlcI : MMP.Intersection.IsLogCanonicalPair sX (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  by_cases hhor : topologicalKrullDim Z = 2 ∧ ∃ E : MMP.Mori.PrimeDivisor X,
      B.roundDown.coeff E ≠ 0 ∧ f.base E.genericPoint = genericPoint Z
  · obtain ⟨hZ2, E, hE, hEη⟩ := hhor
    refine exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent_of_dense sX sZ
      hXp hQ hX3 hB hKB hZ hZ2 f hcon.comp_eq hcon.isProjectiveMorphism hconn hcon.isIso_app hnef
      hA hAq hlc hDG M hGM ⟨E, ?_, ?_⟩
    · have h1 := hKB.2.1 E
      rw [DivisorWithCoeffs.coeff_roundDown] at hE
      by_contra hlt
      exact hE (Int.floor_eq_zero_iff.mpr ⟨h1.1, not_le.mp hlt⟩)
    · have hη : genericPoint Z ∈ f '' (E.support : Set X) := by
        refine ⟨E.genericPoint, ?_, hEη⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      refine Dense.mono (Set.singleton_subset_iff.mpr hη) ?_
      rw [dense_iff_closure_eq, ← (genericPoint_spec Z).def]
  · have hcase : topologicalKrullDim Z = 3 ∨ (topologicalKrullDim Z = 2 ∧
        ∀ E : MMP.Mori.PrimeDivisor X, B.roundDown.coeff E ≠ 0 →
          f.base E.genericPoint ≠ genericPoint Z) := by
      rcases hZ23 with h2 | h3
      · exact Or.inr ⟨h2, fun E hE hEη => hhor ⟨h2, E, hE, hEη⟩⟩
      · exact Or.inl h3
    obtain ⟨Y, _, _, _, sY, g, KY, BY, hYp, hgY, hYdlt, hWc, hPpen, hiff, hempty⟩ :=
      exists_isRelativelySemiample_sub_smul_of_isDltPair_of_add_qLinearlyEquivalent hXp hX3 hQ hZ
        hcon hB hKB hnef hcase hA hAq hlc hDG M hGM
    refine exists_isRelativelyFreeDivisor_of_isRelativelySemiample f _ ?_
    by_cases hT : BY.roundDown = 0
    · exact hempty hT
    · exact hiff.mp (floor_case sX sZ hKB hZ f hcon hnef hA hAq hlcI hDG M hGM sY g
        KY BY hYp hgY hYdlt hWc hPpen hT)

/-! ### The `ℚ`-factorial dlt case -/

/-- A dominant morphism of integral schemes of finite type over `ℂ` does not raise dimension:
`k(W) ⊆ k(X)`, and dimensions are transcendence degrees. -/
private theorem topologicalKrullDim_le_of_isDominant {X W : Scheme.{0}} [IsIntegral X]
    [IsIntegral W] (sW : W ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sW] (h : X ⟶ W) [IsDominant h]
    [LocallyOfFiniteType (h ≫ sW)] : topologicalKrullDim W ≤ topologicalKrullDim X := by
  have hT := toENat_trdeg_functionField (sX := sW)
  have hC := toENat_trdeg_functionField (sX := h ≫ sW)
  rw [← hT, ← hC]
  let := functionFieldAlgebra sW
  let := functionFieldAlgebra (h ≫ sW)
  let := functionFieldMapAlgebra h
  have := isScalarTower_functionFieldMap sW h
  have h' := trdeg_add_eq ℂ W.functionField (A := X.functionField)
  rw [← h', map_add]
  exact WithBot.coe_le_coe.mpr le_self_add

/-- A finite morphism into a scheme which is H-projective over a field is H-projective over that
field. -/
private theorem isProjectiveMorphism_comp_of_isFinite {Y' Y : Scheme.{0}} (g : Y' ⟶ Y)
    [IsFinite g] (sY : Y ⟶ Spec (.of ℂ)) (hY : IsProjectiveMorphism sY) :
    IsProjectiveMorphism (g ≫ sY) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sY
    (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sY hY.isHQuasiProjective)
  have hg : IsProjectiveMorphism g :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_isQuasiProjective g L hLa (isQuasiProjective_of_isFinite g),
        inferInstance⟩
  exact hg.comp hY

/-- **The `ℚ`-factorial dlt case** over an arbitrary projective base: Stein factorize `f` as
`X ⟶ W ⟶ Z`; over a base `W` of dimension at most one this is
`MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`, otherwise
`X ⟶ W` is a contraction onto a surface or a threefold; relative freeness over `W` descends to
`Z` along the finite `W ⟶ Z`. -/
private theorem core {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hXp : Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hX3 : topologicalKrullDim X = 3) {K : Divisor X} {B : QDivisor X} (hB : 0 ≤ B)
    (hKB : Mori.IsDltPair sX 3 K B) (hZ : Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) (hlc : IsLcPair sX 3 K (B + A))
    (hlcI : MMP.Intersection.IsLogCanonicalPair sX (B + A)) {G : QDivisor X}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  have hXv := (Mori.isProjectiveVariety_iff ℂ sX).mp hXp
  have hZv := (Mori.isProjectiveVariety_iff ℂ sZ).mp hZ
  have : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  have : AlgebraicGeometry.IsVariety ℂ sZ := hZv.1
  have : IsProper sX := isProper_of_isProjectiveMorphism _ hXv.2
  have : IsProper (f ≫ sZ) := hf ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sZ
  have hXn : IsNormalVariety ℂ sX := hKB.1.1
  obtain ⟨W, h, κ, ⟨hSt⟩, hhp, hhs, hiso, hconn, hκ, hWn⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isNormalVariety sX sZ hXn hZv.1 f hf
  have hhk : h ≫ κ = f := hSt.comp
  have : IsIntegral W := hWn.1.toIsIntegral
  have : IsNormal W := hWn.2
  have : AlgebraicGeometry.IsVariety ℂ (κ ≫ sZ) := hWn.1
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (κ ≫ sZ)
  have hhW : h ≫ κ ≫ sZ = sX := by rw [← Category.assoc, hhk, hf]
  have hWp : Mori.IsProjectiveVariety ℂ (κ ≫ sZ) :=
    (Mori.isProjectiveVariety_iff ℂ _).mpr ⟨hWn.1, isProjectiveMorphism_comp_of_isFinite κ sZ hZv.2⟩
  have hhproj : IsProjectiveMorphism h :=
    IsProjectiveMorphism.of_comp h (κ ≫ sZ) (by rw [hhW]; exact hXv.2)
  -- hypotheses over `W`
  have : Stacks.Ample.IsInvertibleModule W ((Scheme.Modules.pullback κ).obj M) :=
    MMP.Fourfold.isInvertibleModule_pullback κ M
  have hGM' : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅
        (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback κ).obj M)) := by
    obtain ⟨m, hm, L, hL, ⟨e⟩⟩ := hGM
    refine ⟨m, hm, L, hL, ⟨e ≪≫ ?_⟩⟩
    rw [← hhk]
    exact ((Scheme.Modules.pullbackComp h κ).app M).symm
  have hnef' : (Divisor.toQDivisor K + B).IsRelativelyNef sX h := by
    obtain ⟨hq, hn⟩ := hnef
    refine ⟨hq, fun C hC => hn C fun x hx => ?_⟩
    rw [← hhk, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hdimW : topologicalKrullDim W ≤ 3 := by
    have : LocallyOfFiniteType (h ≫ κ ≫ sZ) := by rw [hhW]; infer_instance
    have : IsDominant h := ⟨hhs.surj.denseRange⟩
    exact hX3 ▸ topologicalKrullDim_le_of_isDominant (κ ≫ sZ) h
  suffices hW : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor h L by
    obtain ⟨m, hm, L, hL, hLc, hfree⟩ := hW
    exact ⟨m, hm, L, hL, hLc, hhk ▸ isRelativelyFreeDivisor_comp_of_isFinite h κ hLc hfree⟩
  by_cases hsmall : topologicalKrullDim W ≤ 1
  · exact exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent sX (κ ≫ sZ)
      hXp hQ hX3 hB hKB hWp h hhW ((topologicalKrullDim_subspace_le W _).trans hsmall) hnef'
      hA hAq hDG _ hGM'
  · have hW23 : topologicalKrullDim W = 2 ∨ topologicalKrullDim W = 3 := by
      generalize topologicalKrullDim W = d at hsmall hdimW
      induction d using WithBot.recBotCoe with
      | bot => exact absurd bot_le hsmall
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hdimW (by decide)
        | coe n =>
          have h3' : (n : ℕ∞) ≤ 3 := WithBot.coe_le_coe.mp hdimW
          have h3 : n ≤ 3 := by exact_mod_cast h3'
          have h1 : ¬ n ≤ 1 := fun h => hsmall (WithBot.coe_le_coe.mpr (by exact_mod_cast h))
          interval_cases n
          · left; rfl
          · right; rfl
    exact core_contraction sX (κ ≫ sZ) hXp hQ hX3 hB hKB hWp hW23 h
      ⟨hXn, hWn, hhW, hhproj, hhs.surj, hiso⟩ hconn hnef' hA hAq hlc hlcI hDG _ hGM'

/-- **The reduction to a `ℚ`-factorial dlt modification.** Transport the data to a projective
crepant `ℚ`-factorial dlt modification `p : V ⟶ X` (`transport`), apply `core` over `p ≫ f`, and
descend relative freeness along the proper birational `p`
(`MMP.Fourfold.exists_isRelativelyFreeDivisor_of_pullback`). -/
private theorem reduction {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hX3 : topologicalKrullDim X = 3)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3) {B : QDivisor X}
    (hlcB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  have hXv := (Mori.isProjectiveVariety_iff ℂ sX).mp hX
  have : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  obtain ⟨V, _, _, _, _, p, _, _, hp, hVn, KV, ΔV, AV, GV, hVp, hVQ, hV3, -, hΔV0, hVdlt', -,
    hnefV, hAV0, hAVq, hlcV, hlcVI, hDGV, hGMV, ⟨_, hpb⟩, -, -, hfin⟩ :=
    transport sX hX hX3 hK hlcB f hnef hA0 hAq hlc hDG M hGM
  have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hVn.1
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ := core (p ≫ sX) sZ hVp hVQ hV3 hΔV0 hVdlt' hZ (p ≫ f)
    (by rw [Category.assoc, hf]) hnefV hAV0 hAVq hlcV hlcVI hDGV M hGMV
  refine exists_isRelativelyFreeDivisor_of_pullback (p ≫ sX) sX hVn hlcB.1.1 p rfl hfin f _
    hnef.1 ⟨m, hm, L, ?_, hLc, hfree⟩
  rw [hpb.pullback_eq hnef.1, hL]

private theorem solution :
    ∀ {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hX3 : topologicalKrullDim X = 3)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3) {B : QDivisor X}
    (hlcB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)),
    QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) := by
  intro X Z sX sZ _ _ _ _ _ hX hX3 K hK B hlcB hZ f hf hnef A hA0 hAq hlc G hDG M _ hGM
  exact isRelativelySemiample_of_isRelativelyFreeDivisor f _
    (reduction sX sZ hX hX3 hK hlcB hZ f hf hnef hA0 hAq hlc hDG M hGM)

end Proof_thm_fourfold_projective_complemented_lc_threefold_good

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Complemented projective lc threefolds are relatively good.** Let `X` be a projective
threefold over `ℂ` (`MMP.Mori.IsProjectiveVariety`), `K` a canonical divisor of `X` and `B` a
`ℚ`-divisor with `(X, B)` log canonical (`MMP.Intersection.IsLogCanonicalPair`), and let
`f : X ⟶ Z` be a morphism over `ℂ` to a projective variety with `K + B` relatively nef over `f`
(`MMP.Mori.QDivisor.IsRelativelyNef`). Suppose `A ≥ 0` is a `ℚ`-Cartier `ℚ`-divisor with
`(X, B + A)` log canonical and `K + B + A ∼_ℚ G`, where `𝒪_X(mG) ≅ f^*M` for some `m > 0` and an
invertible `𝒪_Z`-module `M`. Then `K + B` is semiample over `f`
(`MMP.Fourfold.QDivisor.IsRelativelySemiample`). -/
@[mmp "thm_fourfold_projective_complemented_lc_threefold_good"]
public theorem isRelativelySemiample_of_isLogCanonicalPair_add_of_qLinearlyEquivalent
    {X Z : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hX3 : topologicalKrullDim X = 3)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 3) {B : QDivisor X}
    (hlcB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    {A : QDivisor X} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {G : QDivisor X} (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G)
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    QDivisor.IsRelativelySemiample f (Divisor.toQDivisor K + B) :=
      by revert X Z sX sZ hX hX3 K hK B hlcB hZ f hf hnef A hA0 hAq hlc G hDG M hGM; first | exact Proof_thm_fourfold_projective_complemented_lc_threefold_good.solution | exact Proof_thm_fourfold_projective_complemented_lc_threefold_good.solution _ | exact Proof_thm_fourfold_projective_complemented_lc_threefold_good.solution _ _ | exact Proof_thm_fourfold_projective_complemented_lc_threefold_good.solution _ _ _ | exact Proof_thm_fourfold_projective_complemented_lc_threefold_good.solution _ _ _ _

end MMP.Fourfold

