module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.BirationalFloorLowering
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltModification
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeSections
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# A crepant dlt model with a semiample pencil off its whole floor

Let `g : X ⟶ Z` be a projective birational morphism of normal projective complex fourfolds, and
let `(X, B)` be a `ℚ`-factorial dlt pair with rational boundary whose adjoint `D = K_X + B` is
nef over `Z`. Then there is a projective `ℚ`-factorial dlt pair `(Y, B_Y)` over `Z`, crepant
birational to `(X, B)` (the adjoints `K_X + B` and `K_Y + B_Y` have the same pull-back to a common
resolution), together with an effective `ℚ`-Cartier divisor `P` on `Y` whose support is exactly
the reduced floor `⌊B_Y⌋`, such that `K_Y + B_Y - δP` is semiample over `Z` for every
sufficiently small rational `δ > 0`. Moreover the central adjoint `K_Y + B_Y` is nef over `Z`,
it is semiample over `Z` if and only if `D` is, and if the floor `⌊B_Y⌋` is empty then `D` is
semiample over `Z`.

## Main results

* `MMP.Fourfold.IsDltPair.exists_isRelativelySemiample_sub_smul_of_supp_eq_roundDown`.

## Implementation notes

Crepant birationality is a birational map `φ : X ⤏ Y` over `Z` with a common resolution
`p : W ⟶ X`, `q : W ⟶ Y` (`MMP.Fourfold.IsLogComparisonResolution`) on which `p^*(K_X + B)` and
`q^*(K_Y + B_Y)` are the same divisor `G`; the canonical divisors `K_X`, `K_Y` are compatible
(cut out by one rational top form). Semiampleness over `Z` is
`MMP.Fourfold.QDivisor.IsRelativelySemiample` along the structure morphism `Y ⟶ Z`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_lem_fourfold_dlt_semiample_floor_pencil

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP MMP.Fourfold MMP.Mori MMP.Flips

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
    show P.genericPoint ∈ cartierSupport A
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
  Pi.ringHom fun Z => (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom

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
  haveI : IsNoetherian X := ⟨⟩
  haveI := hL.isInvertibleModule_divisorialSheaf
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
    haveI : Nontrivial (RationalFunctions X) := Pi.nontrivial_at Z₀
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
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := h
  obtain ⟨w, hw⟩ := exists_isWeilDivisorOfCartier
    (KCartierDivisor.realization ((q : ℚ) • C) hint)
  refine ⟨q, hq, w, ?_, hw.isCartier, ?_⟩
  · ext P
    rw [Divisor.coeff_toQDivisor, coeff_eq_mul_of_isWeilDivisorOfCartier_realization hC hint hw P]
    simp [DivisorWithCoeffs.coeff_apply, zsmul_eq_mul]
  · obtain ⟨e⟩ := hw.nonempty_sheaf_iso_divisorialSheaf
    exact epi_counit_of_iso f e.symm hfree

end Conversion

/-! ### Pull-backs of `ℚ`-Cartier `ℚ`-divisors -/

/-- If `D = mB` then `kD = (mk)B`. -/
private theorem toQDivisor_natCast_smul {X : Scheme.{0}} {D : Divisor X} {B : QDivisor X}
    {m : ℕ} (hD : Divisor.toQDivisor D = (m : ℤ) • B) (k : ℕ) :
    Divisor.toQDivisor ((k : ℤ) • D) = ((m * k : ℕ) : ℤ) • B := by
  rw [map_zsmul, hD, smul_smul]; push_cast; rw [mul_comm]

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
  have hE₁ := toQDivisor_natCast_smul hD₁ m₂
  have hE₂ : Divisor.toQDivisor ((m₁ : ℤ) • D₂) = ((m₁ * m₂ : ℕ) : ℤ) • B₂ :=
    Nat.mul_comm m₂ m₁ ▸ toQDivisor_natCast_smul hD₂ m₁
  obtain ⟨E₁', hE₁', hp₁⟩ := h₁ _ hm _ hE₁ (hD₁c.zsmul _)
  obtain ⟨E₂', hE₂', hp₂⟩ := h₂ _ hm _ hE₂ (hD₂c.zsmul _)
  have hE : Divisor.toQDivisor ((m₂ : ℤ) • D₁ + (m₁ : ℤ) • D₂) =
      ((m₁ * m₂ : ℕ) : ℤ) • (B₁ + B₂) := by rw [map_add, hE₁, hE₂, smul_add]
  refine isPullback_of_smul (hq₁.add hq₂) hm hE ((hD₁c.zsmul _).add (hD₂c.zsmul _))
    (D' := E₁' + E₂') (by rw [map_add, hE₁', hE₂', smul_add]) ?_
  exact Divisor.IsPullback.add (hD₁c.zsmul _) (hD₂c.zsmul _) _ hp₁ hp₂

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
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

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
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

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
  haveI := QuasiCompact.compactSpace_of_compactSpace sX
  haveI := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
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
    haveI : IsProper (C''.ι ≫ sX) := C''.isProper_ι_comp
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

end Nef

/-- The pull-back predicate only depends on the divisor, not on the proof of `(∗)`. -/
private theorem isPullback_congr {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {B₁ B₂ : QDivisor Y} (h : B₁ = B₂)
    {hB₁ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₁.supp}
    {hB₂ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B₂.supp}
    {B₁' B₂' : QDivisor X} (h' : B₁' = B₂') (hp : B₁.IsPullback f hB₁ B₁') :
    B₂.IsPullback f hB₂ B₂' := by
  subst h h'
  exact hp

/-! ### Relative semiampleness under pull-back and descent -/

/-- If `D = mB` then `c.num • D = (c.den * m) • (c • B)`: a rational multiple of `B` has an
integral multiple which is an integral multiple of `D`. -/
private theorem toQDivisor_num_smul {X : Scheme.{0}} {D : Divisor X} {B : QDivisor X} {m : ℕ}
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
  exact ⟨((c.den * m : ℕ) : ℤ), by positivity, c.num • D, toQDivisor_num_smul hD c, hDc.zsmul _⟩

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
    (toQDivisor_num_smul hD c) (hDc.zsmul _) (toQDivisor_num_smul hD' c) (hp.zsmul hDc c.num _)

/-- **Pull-backs of relatively semiample divisors are relatively semiample.** -/
private theorem isRelativelySemiample_pullback {Y Y' Z : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (e : Y' ⟶ Y) [IsDominant e]
    (g : Y ⟶ Z) {D : QDivisor Y} (hD : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉ D.supp}
    {D' : QDivisor Y'} (h : D.IsPullback e hB D') (hs : QDivisor.IsRelativelySemiample g D) :
    QDivisor.IsRelativelySemiample (e ≫ g) D' := by
  classical
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ := exists_isRelativelyFreeDivisor_of_isRelativelySemiample g D hs
  obtain ⟨L', hL', hpL⟩ := h m hm L hL hLc
  have hL'c : L'.IsCartier := hpL.isCartier hLc
  refine isRelativelySemiample_of_isRelativelyFreeDivisor (e ≫ g) D'
    ⟨m, hm, L', hL', hL'c, isRelativelyFreeDivisor_of_forall_exists (e ≫ g) fun y => ?_⟩
  obtain ⟨U, hU, ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree g hLc hfree (e y)
  have hψ : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉
      (principalDivisor ψ).supp := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant e _
  set ψ' := pullbackRationalFunction e ψ hψ
  set F : Divisor Y := L + principalDivisor ψ with hF
  have hFc : F.IsCartier := hLc.add (Divisor.isCartier_principalDivisor ψ)
  have hFB : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉ F.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant e _
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

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper_of_isDominant {X Y : Scheme.{0}} (p : X ⟶ Y) [IsProper p]
    [IsDominant p] : Surjective p :=
  ⟨fun x => by
    have hx := (isDominant_iff p).mp ‹IsDominant p› x
    rwa [p.isClosedMap.isClosed_range.closure_eq] at hx⟩

/-- A birational morphism of integral schemes induces a finite extension of function fields. -/
private theorem finite_functionField_of_isBirationalMorphism {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Y} (hp : IsBirationalMorphism p) :
    letI := (haveI := hp.isDominant; functionFieldMapAlgebra p)
    Module.Finite Y.functionField X.functionField := by
  haveI := hp.isDominant
  letI := functionFieldMapAlgebra p
  exact Module.Finite.of_surjective (Algebra.linearMap Y.functionField X.functionField)
    hp.functionFieldMap_bijective.2

/-- **Relative semiampleness is birationally invariant.** If `D'` is the pull-back of a
`ℚ`-Cartier `D` along a proper birational morphism `e : Y' ⟶ Y` of normal varieties, then `D'` is
semiample over `Z` exactly when `D` is. -/
private theorem isRelativelySemiample_iff_of_isPullback {Y Y' Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y']
    (hY : IsNormalVariety ℂ sY) (e : Y' ⟶ Y) [IsProper e] (he : IsBirationalMorphism e)
    (hY' : IsNormalVariety ℂ (e ≫ sY)) (g : Y ⟶ Z) {D : QDivisor Y} (hD : D.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y', e (componentGenericPoint Y' Z) ∉ D.supp}
    {D' : QDivisor Y'} (h : D.IsPullback e hB D') :
    QDivisor.IsRelativelySemiample (e ≫ g) D' ↔ QDivisor.IsRelativelySemiample g D := by
  haveI := he.isDominant
  haveI := surjective_of_isProper_of_isDominant e
  refine ⟨fun hs => ?_, isRelativelySemiample_pullback e g hD h⟩
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ := exists_isRelativelyFreeDivisor_of_isRelativelySemiample _ _ hs
  refine isRelativelySemiample_of_isRelativelyFreeDivisor g D
    (exists_isRelativelyFreeDivisor_of_pullback (e ≫ sY) sY hY' hY e rfl
      (finite_functionField_of_isBirationalMorphism he) g D hD ⟨m, hm, L, ?_, hLc, hfree⟩)
  rw [h.pullback_eq hD, hL]

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

/-- The dimension index of a canonical divisor is the dimension of the variety. -/
private theorem eq_of_isCanonicalDivisor {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {s : X ⟶ Spec (.of ℂ)} {n m : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor s n)
    (hd : topologicalKrullDim X = m) : n = m := by
  exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hd

/-- The adjoint `K + Δ` of a `ℚ`-boundary, regarded as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_toRDivisor {X : Scheme.{0}} (K : Divisor X) (Δ : QDivisor X) :
    logCanonicalDivisor K (QDivisor.toRDivisor Δ) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + Δ) := by
  rw [logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-! ### Transforms of divisors along the steps -/

/-- A separated variety is separated over the terminal scheme. -/
private theorem isSeparated_terminal {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} (h : IsNormalVariety k s) : IsSeparated (X ↘ ⊤_ Scheme) := by
  haveI := h.1
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- If `g'` represents `φ` at the generic point of `P` and sends it to the generic point of `E`,
then the transform of `P` under `φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq' {X Y : Scheme.{0}}
    [IsReduced X] [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {P : MMP.Mori.PrimeDivisor X} {E : MMP.Mori.PrimeDivisor Y}
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [MMP.Flips.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- A representative of a rational map `ψ` with `fp ∘ ψ = f` satisfies `fp ∘ g' = f` pointwise on
its domain. -/
private theorem apply_hom_eq_of_compHom_eq {X Y W : Scheme.{0}} [IsReduced X]
    [IsSeparated (W ↘ ⊤_ Scheme)] {ψ : X.RationalMap Y} {fp : Y ⟶ W} {f : X ⟶ W}
    (h : ψ.compHom fp = f.toRationalMap) (g' : X.PartialMap Y) (hg' : g'.toRationalMap = ψ)
    (x : g'.domain) : fp (g'.hom x) = f x := by
  have h1 : (g'.compHom fp).equiv f.toPartialMap := by
    rw [← Scheme.PartialMap.toRationalMap_eq_iff, Scheme.RationalMap.compHom_toRationalMap, hg',
      h]
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp h1
  have h3 := congrArg (fun φ => φ.base x) h2
  simp only [Scheme.PartialMap.compHom] at h3
  exact h3

/-- The coefficient of a transform at `Q` is the coefficient at the unique prime sent to `Q`. -/
private theorem transformDivisor_apply_of_forall_iff {X Y : Scheme.{0}} {ψ : X.RationalMap Y}
    {Q : MMP.Mori.PrimeDivisor Y} {E : MMP.Mori.PrimeDivisor X}
    (h : ∀ E' : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor ψ E' = some Q ↔ E' = E)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor ψ D Q = D E := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hD, hD']
  | single P r =>
    rw [MMP.Mori.RationalMap.transformDivisor_single]
    by_cases hP : P = E
    · subst hP
      rw [(h P).mpr rfl]
      simp
    · rw [Finsupp.single_apply, if_neg hP]
      rcases hψ : MMP.Mori.RationalMap.transformPrimeDivisor ψ P with _ | Q'
      · rfl
      · have hQ' : Q' ≠ Q := fun e => hP ((h P).mp (by rw [hψ, e]))
        simp [Finsupp.single_apply, hQ']

variable {k : Type} [Field k] {X₁ X₂ W : Scheme.{0}} [IsIntegral X₁] [CompactSpace X₁]
  [IsLocallyNoetherian X₁] [IsNormal X₁] [IsIntegral X₂] [CompactSpace X₂]
  [IsLocallyNoetherian X₂] [IsNormal X₂] [IsIntegral W] [CompactSpace W]
  [IsLocallyNoetherian W] [IsNormal W] {s₁ : X₁ ⟶ Spec (.of k)} {s₂ : X₂ ⟶ Spec (.of k)}
  {sW : W ⟶ Spec (.of k)} in
/-- **Transforms along a step over the base of its contraction.** Let `f : X₁ ⟶ W` and
`fp : X₂ ⟶ W` be proper birational morphisms of normal varieties and `ψ : X₁ ⤏ X₂` a rational map
with `fp ∘ ψ = f`. Then `fp_* ψ_* D = f_* D` for every divisor `D` on `X₁`. -/
private theorem transformDivisor_transformDivisor_of_compHom_eq (hX₁ : IsNormalVariety k s₁)
    (hX₂ : IsNormalVariety k s₂) (hW : IsNormalVariety k sW) {f : X₁ ⟶ W} {fp : X₂ ⟶ W}
    (hfW : f ≫ sW = s₁) (hfpW : fp ≫ sW = s₂) [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) {ψ : X₁.RationalMap X₂}
    (hψ : ψ.compHom fp = f.toRationalMap) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X₁) :
    MMP.Mori.RationalMap.transformDivisor (X := X₂) fp.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor ψ D) =
      MMP.Mori.RationalMap.transformDivisor (X := X₁) f.toRationalMap D := by
  classical
  haveI := hW.1
  haveI := isSeparated_terminal hW
  haveI := isSeparated_terminal hX₂
  haveI : IsSeparated f := IsSeparated.of_comp f sW
  haveI : IsSeparated fp := IsSeparated.of_comp fp sW
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant fp := hfp.isDominant
  refine Finsupp.ext fun P' => ?_
  obtain ⟨E, hE, -, htrE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hW (hfW ▸ hX₁) hf P'
  obtain ⟨Q, hQ, -, htrQ⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hW (hfpW ▸ hX₂) hfp P'
  rw [htrE, htrQ]
  have := P'.isDiscreteValuationRing_localRing
  -- the unique point of `X₁` (resp. `X₂`) over `η_{P'}`
  have huniq₁ : ∀ x : X₁, f x = P'.genericPoint → x = E.genericPoint := fun x hx => by
    haveI : ValuationRing (W.presheaf.stalk (f E.genericPoint)) := by rw [hE]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      E.genericPoint
    haveI : ValuationRing (W.presheaf.stalk (f x)) := by rw [hx]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective x
    exact (MMP.Positivity.eq_of_isIso_stalkMap f hf.functionFieldMap_bijective
      (hx.trans hE.symm)).symm
  have huniq₂ : ∀ y : X₂, fp y = P'.genericPoint → y = Q.genericPoint := fun y hy => by
    haveI : ValuationRing (W.presheaf.stalk (fp Q.genericPoint)) := by rw [hQ]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hfp.functionFieldMap_bijective
      Q.genericPoint
    haveI : ValuationRing (W.presheaf.stalk (fp y)) := by rw [hy]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fp hfp.functionFieldMap_bijective y
    exact (MMP.Positivity.eq_of_isIso_stalkMap fp hfp.functionFieldMap_bijective
      (hy.trans hQ.symm)).symm
  refine transformDivisor_apply_of_forall_iff (fun E' => ⟨fun h => ?_, ?_⟩) D
  · obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h
    obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
    have h1 := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP
    have h2 := apply_hom_eq_of_compHom_eq hψ g' hg' ⟨E'.genericPoint, hP⟩
    rw [← h1, hQ] at h2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (huniq₁ _ h2.symm)
  · intro hE'
    rw [hE']
    have hdom : E.genericPoint ∈ ψ.domain := MMP.Flips.RationalMap.mem_domain_of_coheight_le_one
      f fp ψ hψ E.coheight_genericPoint.le
    obtain ⟨g', hP, hg'⟩ := Scheme.RationalMap.mem_domain.mp hdom
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq' g' hg' hP ?_
    have h2 := apply_hom_eq_of_compHom_eq hψ g' hg' ⟨E.genericPoint, hP⟩
    rw [hE] at h2
    exact (huniq₂ _ h2).symm

/-- The birational transform of divisors commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem transformDivisor_toQDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single P n =>
    have hP : Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
      ext E
      change ((Finsupp.single P n E : ℤ) : ℚ) = Finsupp.single P (n : ℚ) E
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rw [hP, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    cases MMP.Mori.RationalMap.transformPrimeDivisor φ P with
    | none => simp
    | some E =>
      ext F
      change Finsupp.single E (n : ℚ) F = ((Finsupp.single E n F : ℤ) : ℚ)
      rw [Finsupp.single_apply, Finsupp.single_apply]
      by_cases hEF : E = F <;> simp [hEF]

/-! ### Birational maps through a common model -/

/-- Let `p : W ⟶ X` and `q : W ⟶ Y` be birational morphisms out of an irreducible scheme. Then
`p` has an inverse `h : X ⤏ W` with `p ∘ h = id` and `q ∘ h : X ⤏ Y` birational: on a dense open
`V ⊆ W` where both `p` and `q` are open immersions, `h` is `(p|_V)⁻¹` and `q ∘ h` is
`q|_V ∘ (p|_V)⁻¹`. -/
private theorem exists_isInverse_and_isBirational_compHom {W X Y : Scheme.{0}}
    [IrreducibleSpace W] {p : W ⟶ X} {q : W ⟶ Y} (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) :
    ∃ h : X.RationalMap W, MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
      MMP.Mori.RationalMap.IsBirational (h.compHom q) ∧
      h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  haveI : Nonempty W := (IrreducibleSpace.isIrreducible_univ W).nonempty.to_subtype.map (·.1)
  haveI := hp.isDominant
  haveI := hq.isDominant
  obtain ⟨A, hA, hAo⟩ := hp.exists_isOpenImmersion
  obtain ⟨B, hB, hBo⟩ := hq.exists_isOpenImmersion
  set V : W.Opens := A ⊓ B
  have hV : (V : Set W).Nonempty := by
    obtain ⟨a, ha, hb⟩ := (IrreducibleSpace.isIrreducible_univ W).isPreirreducible A B A.isOpen
      B.isOpen (by simpa using hA) (by simpa using hB)
    exact ⟨a, hb⟩
  have hVd : Dense (V : Set W) := V.isOpen.dense hV
  haveI : IsOpenImmersion (V.ι ≫ p) := by
    rw [← W.homOfLE_ι (inf_le_left : V ≤ A), Category.assoc]; infer_instance
  haveI : IsOpenImmersion (V.ι ≫ q) := by
    rw [← W.homOfLE_ι (inf_le_right : V ≤ B), Category.assoc]; infer_instance
  haveI : IsDominant V.ι := Opens.isDominant_ι hVd
  let G : W.PartialIso X :=
    { source := V
      dense_source := hVd
      target := (V.ι ≫ p).opensRange
      dense_target := by rw [Scheme.Hom.coe_opensRange]; exact (V.ι ≫ p).denseRange
      iso := (V.ι ≫ p).isoOpensRange }
  let Gq : W.PartialIso Y :=
    { source := V
      dense_source := hVd
      target := (V.ι ≫ q).opensRange
      dense_target := by rw [Scheme.Hom.coe_opensRange]; exact (V.ι ≫ q).denseRange
      iso := (V.ι ≫ q).isoOpensRange }
  have hG : G.toRationalMap = p.toRationalMap := by
    rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨V, hVd, le_rfl, le_top, ?_⟩
    change W.homOfLE le_rfl ≫ (Scheme.Hom.isoOpensRange (V.ι ≫ p)).hom ≫
        (V.ι ≫ p).opensRange.ι = W.homOfLE (le_top : V ≤ ⊤) ≫ W.topIso.hom ≫ p
    rw [Scheme.Hom.isoOpensRange_hom_ι, Scheme.topIso_hom, Scheme.homOfLE_ι_assoc,
      Scheme.homOfLE_ι_assoc]
  refine ⟨G.symm.toRationalMap, ⟨G, hG, rfl⟩, ⟨G.symm.trans' Gq rfl, ?_⟩, ?_⟩
  · rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨(V.ι ≫ p).opensRange, G.dense_target, le_rfl, le_rfl, ?_⟩
    change X.homOfLE le_rfl ≫ ((V.ι ≫ p).isoOpensRange.symm ≪≫ W.isoOfEq rfl ≪≫
        (V.ι ≫ q).isoOpensRange).hom ≫ (V.ι ≫ q).opensRange.ι =
      X.homOfLE le_rfl ≫ ((V.ι ≫ p).isoOpensRange.inv ≫ V.ι) ≫ q
    simp [Scheme.Hom.isoOpensRange_hom_ι]
  · rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨(V.ι ≫ p).opensRange, G.dense_target, le_rfl, le_top, ?_⟩
    change X.homOfLE le_rfl ≫ ((V.ι ≫ p).isoOpensRange.inv ≫ V.ι) ≫ p =
      X.homOfLE (le_top : (V.ι ≫ p).opensRange ≤ ⊤) ≫ X.topIso.hom ≫ 𝟙 X
    have e : (V.ι ≫ p).isoOpensRange.inv ≫ (V.ι ≫ p) = (V.ι ≫ p).opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    rw [Category.assoc, e]
    simp [Scheme.topIso_hom]

/-- The rational map of a composite of morphisms. -/
private theorem toRationalMap_compHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- `(φ ∘ f) ∘ g = φ ∘ (g ∘ f)` for a rational map `φ` and morphisms `f`, `g`. -/
private theorem compHom_compHom {X Y Z T : Scheme.{0}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ', rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-! ### The common resolution lies over the base -/

/-- The restriction of a partial map to the generic point is read off its domain. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{0}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{0}}
    [IsIntegral X] [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (_root_.genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (_root_.genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Two morphisms from an integral scheme to a separated scheme which agree at the generic
point are equal. -/
private theorem eq_of_fromSpecStalk_genericPoint_comp_eq {W Z : Scheme.{0}} [IsIntegral W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {a b : W ⟶ Z}
    (h : W.fromSpecStalk (genericPoint W) ≫ a = W.fromSpecStalk (genericPoint W) ≫ b) :
    a = b := by
  have hr : a.toRationalMap = b.toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom, h]
  have e := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)
    (f := a.toPartialMap) (g := b)).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp hr)
  have e' : W.topIso.hom ≫ a = W.topIso.hom ≫ b := by
    refine e.trans ?_
    rw [Scheme.topIso_hom]
    rfl
  exact (cancel_epi _).mp e'

/-- **A common resolution of models over `Z` commutes over `Z`.** If `φ : X ⤏ Y` lies over
`g : X ⟶ Z` and `g_Y : Y ⟶ Z`, and `p : W ⟶ X`, `q : W ⟶ Y` is a common resolution with
`q ∘ p⁻¹ = φ`, then `g ∘ p = g_Y ∘ q`. -/
private theorem comp_eq_comp_of_isLogComparisonResolution {X Y Z W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {φ : X.RationalMap Y} {KX : Divisor X} {BX : RDivisor X}
    {KY : Divisor Y} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX BX KY BY p q h GX GY)
    [IsSeparated (Z ↘ ⊤_ Scheme)] {g : X ⟶ Z} {gY : Y ⟶ Z}
    (hover : MMP.Flips.RationalMap.IsOver g gY φ) : p ≫ g = q ≫ gY := by
  haveI : IsDominant p := hR.isBirationalMorphism_left.isDominant
  have hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
    obtain ⟨e, he1, he2⟩ := hR.isInverse
    rw [← hR.compHom_eq, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
      specMap_functionFieldMap_fromFunctionField_symm p e he1]
  apply eq_of_fromSpecStalk_genericPoint_comp_eq
  rw [← Category.assoc, ← Category.assoc, ← hW, ← functionFieldMap_fromSpecStalk p,
    Category.assoc, Category.assoc, ← MMP.Flips.RationalMap.fromFunctionField_hom,
    ← MMP.Flips.RationalMap.fromFunctionField_compHom, hover]

/-! ### Coefficients on a crepant dlt model -/

/-- A discrepancy `a(E, X, Δ)` of a divisor `(Y, f, E)` over `X` whose centre is the generic point
of a prime divisor `P` of `X` is `-coeff_P(Δ)`. -/
private theorem IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : MMP.Mori.IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : MMP.Mori.DivisorOver ℂ sX} {P : MMP.Mori.PrimeDivisor X}
    (hP : D.f D.E.genericPoint = P.genericPoint) {a : ℚ}
    (h : MMP.Mori.IsDiscrepancy sX n K Δ D a) : a = -Δ.coeff P := by
  obtain ⟨hX', hK, m, hm, hC, U, hU, τ, hτ, hτa⟩ := h
  refine MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX (P := P)
    ⟨hX', hK, m, hm, hC, U, ?_, τ, hτ, ?_⟩
  · convert hU using 2
    exact hP.symm
  · rw [hτa, MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX
      hK.topologicalKrullDim_eq
      (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX D P hP)]

/-- **Crepant boundaries of a klt pair have coefficients `< 1`.** On a proper birational model
`f : Y ⟶ X` the coefficient of the crepant boundary of a klt pair `(X, Δ)` along a prime divisor
`F` is `1 - a(F, X, Δ) < 1`. -/
private theorem coeff_lt_one_of_isKltPair_of_isCrepantBoundary {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hklt : MMP.Fourfold.IsKltPair sX Δ) {f : Y ⟶ X}
    [IsProper f] (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (F : MMP.Mori.PrimeDivisor Y) : ΔY.coeff F < 1 := by
  have h := hklt.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΔY F)
    (show IsProper f from inferInstance))
  have : ((ΔY.coeff F : ℚ) : ℝ) < 1 := by push_cast at h; linarith
  exact_mod_cast this

/-- The birational transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg' {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R] (φ : X.RationalMap Y)
    {D : DivisorWithCoeffs R X} (hD : 0 ≤ D) :
    0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  rw [← Finsupp.sum_single D, map_finsuppSum, Finsupp.sum]
  refine Finset.sum_nonneg fun E _ => ?_
  rw [MMP.Mori.RationalMap.transformDivisor_single]
  cases MMP.Mori.RationalMap.transformPrimeDivisor φ E with
  | none => exact le_rfl
  | some E' => exact Finsupp.single_nonneg.mpr (hD E)

/-- Two `ℚ`-divisors with the same prime divisors of nonzero coefficient have the same support. -/
private theorem supp_eq_of_forall_coeff_ne_zero_iff {Y : Scheme.{0}} {D D' : QDivisor Y}
    (h : ∀ F : MMP.Mori.PrimeDivisor Y, D.coeff F ≠ 0 ↔ D'.coeff F ≠ 0) : D.supp = D'.supp := by
  refine SetLike.ext fun x => ?_
  rw [DivisorWithCoeffs.mem_supp_iff, DivisorWithCoeffs.mem_supp_iff]
  simp only [h]

/-- The arithmetic of the floor: a coefficient `b ∈ [0, 1]` of a dlt boundary and the coefficient
`c ≥ 0` of the pencil with `b - t c < 1`, where either `b = 1` or `c` is an integer at most `b`,
satisfy `c ≠ 0 ↔ ⌊b⌋ ≠ 0`. -/
private theorem ne_zero_iff_floor_ne_zero {b c t : ℚ} (ht : 0 < t) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hlt : b - t * c < 1) (key : b = 1 ∨ ∃ z : ℤ, c = z ∧ (z : ℚ) ≤ b) :
    c ≠ 0 ↔ ((⌊b⌋ : ℤ) : ℚ) ≠ 0 := by
  have hfl : ((⌊b⌋ : ℤ) : ℚ) ≠ 0 ↔ b = 1 := by
    constructor
    · intro h
      by_contra hb
      have h1 : b < 1 := lt_of_le_of_ne hb1 hb
      have : ⌊b⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hb0, h1⟩
      exact h (by simp [this])
    · rintro rfl
      simp
  rw [hfl]
  constructor
  · intro hc
    rcases key with h | ⟨z, rfl, hz⟩
    · exact h
    · have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast hc0
      have hz1 : z ≠ 0 := fun h0 => hc (by simp [h0])
      have : (1 : ℚ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
      linarith
  · rintro rfl hc
    rw [hc, mul_zero, sub_zero] at hlt
    exact lt_irrefl _ hlt

/-- **The pencil on a crepant dlt model.** Let `e : V ⟶ X'` be a crepant dlt lift of an lc pair
`(X', B')` on a `ℚ`-factorial fourfold, `K_V` a canonical divisor with `e_* K_V = K'`, and `T`
an effective divisor with `T ≤ B'` such that `(X', B' - t₀ T)` is klt. Then `P = e^* T` is
effective and `ℚ`-Cartier with support exactly `⌊B_V⌋`, `K_V + B_V = e^*(K' + B')`, the
perturbations `K_V + B_V - δ P = e^*(K' + B' - δ T)` inherit semiampleness over `Z`, and
`K_V + B_V` inherits nefness. -/
private theorem dltModel {X' V Z : Scheme.{0}} [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V]
    [IsNormal V] {sX' : X' ⟶ Spec (.of ℂ)} (hQ' : IsQFactorial sX') {K' : Divisor X'}
    (hK' : K'.IsCanonicalDivisor sX' 4) {B' : QDivisor X'} {T : Divisor X'} {t₀ : ℚ}
    (ht₀ : 0 < t₀) (hklt' : MMP.Fourfold.IsKltPair sX' (B' - t₀ • Divisor.toQDivisor T))
    (hT0 : 0 ≤ T) (hTB : Divisor.toQDivisor T ≤ B') {g' : X' ⟶ Z}
    (hsemi : ∀ t : ℚ, 0 < t → t ≤ t₀ → QDivisor.IsRelativelySemiample g'
      (Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor T))
    (hnef' : QDivisor.IsRelativelyNef sX' g' (Divisor.toQDivisor K' + B'))
    {e : V ⟶ X'} {BV : QDivisor V} (hL : IsCrepantDltLift sX' K' B' e BV) {KV : Divisor V}
    (hKV : KV.IsCanonicalDivisor (e ≫ sX') 4)
    (hKVe : MMP.Mori.RationalMap.transformDivisor (X := V) e.toRationalMap KV = K') :
    ∃ P : QDivisor V, 0 ≤ P ∧ P.IsQCartier ∧
      P.supp = (Divisor.toQDivisor BV.roundDown).supp ∧
      (∀ δ : ℚ, 0 < δ → δ ≤ t₀ → QDivisor.IsRelativelySemiample (e ≫ g')
        (Divisor.toQDivisor KV + BV - δ • P)) ∧
      QDivisor.IsRelativelyNef (e ≫ sX') (e ≫ g') (Divisor.toQDivisor KV + BV) ∧
      ∃ hB, (Divisor.toQDivisor K' + B').IsPullback e hB (Divisor.toQDivisor KV + BV) := by
  classical
  have hX'n : IsNormalVariety ℂ sX' := hQ'.1
  haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
  haveI : IsSeparated sX' := hX'n.1.toIsSeparated
  haveI : QuasiCompact sX' := hX'n.1.toQuasiCompact
  haveI : IsProper e := isProper_of_isProjectiveMorphism e hL.isProjectiveMorphism
  have heb : IsBirationalMorphism e := hL.isBirationalMorphism
  haveI : IsDominant e := heb.isDominant
  have hVn : IsNormalVariety ℂ (e ≫ sX') := hL.isQFactorial.1
  haveI : QuasiCompact (e ≫ sX') := hVn.1.toQuasiCompact
  -- the crepant boundary, in dimension four
  have hcrep : IsCrepantBoundary sX' 4 K' B' e hL.isQFactorial.1 heb BV := by
    obtain ⟨n, hn⟩ := hL.isCrepantBoundary
    intro F
    have h := hn F
    obtain rfl := eq_of_isCanonicalDivisor h.2.1 hK'.topologicalKrullDim_eq
    exact h
  have hpairB' : MMP.Mori.IsPair sX' B' := hL.isLogCanonicalPair.1
  obtain ⟨-, -, hBc, hpb⟩ := MMP.Mori.IsPair.isPullback_of_isCrepantBoundary hpairB' e hVn heb hK'
    hKV (Or.inr ⟨inferInstance, hKVe⟩) hcrep
  -- the pencil `P = e^* T`
  have hTq : (Divisor.toQDivisor T).IsQCartier := isQCartier_of_isQFactorial sX' hQ' _
  have hTB' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e hTq
  have hP : (Divisor.toQDivisor T).IsPullback e hTB' ((Divisor.toQDivisor T).pullback hTq hTB') :=
    QDivisor.isPullback_pullback hTq hTB'
  set P := (Divisor.toQDivisor T).pullback hTq hTB' with hPdef
  have hP0 : 0 ≤ P := nonneg_of_isPullback (fun Q => by
    show (0 : ℚ) ≤ (Divisor.toQDivisor T).coeff Q
    rw [Divisor.coeff_toQDivisor]
    exact_mod_cast (show (0 : ℤ) ≤ T.coeff Q from hT0 Q)) hTq hP
  have hPq : P.IsQCartier := hP.isQCartier hTq
  have hDq : (Divisor.toQDivisor K' + B').IsQCartier := isQCartier_of_isQFactorial sX' hQ' _
  -- pull-backs of the perturbations
  have hpbδ : ∀ δ : ℚ, ∃ hB, (Divisor.toQDivisor K' + B' - δ • Divisor.toQDivisor T).IsPullback
      e hB (Divisor.toQDivisor KV + BV - δ • P) := by
    intro δ
    have h1 := isPullback_qsmul hTq (-δ)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e
        (isQCartier_qsmul hTq (-δ))) hP
    have h2 := isPullback_add hDq (isQCartier_qsmul hTq (-δ))
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e
        (hDq.add (isQCartier_qsmul hTq (-δ)))) hpb h1
    exact ⟨MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e
      (isQCartier_of_isQFactorial sX' hQ' _),
      isPullback_congr (by rw [neg_smul, ← sub_eq_add_neg]) (by rw [neg_smul, ← sub_eq_add_neg])
        h2⟩
  refine ⟨P, hP0, hPq, ?_, fun δ hδ hδt => ?_, ?_, hBc, hpb⟩
  · -- the support of the pencil is the floor
    have hlowpair : IsPairWith sX' 4 K' (B' - t₀ • Divisor.toQDivisor T) :=
      ⟨hX'n, hK', isQCartier_of_isQFactorial sX' hQ' _⟩
    obtain ⟨hBl, hpbl⟩ := hpbδ t₀
    have hcrepl : IsCrepantBoundary sX' 4 K' (B' - t₀ • Divisor.toQDivisor T) e
        hL.isQFactorial.1 heb (BV - t₀ • P) :=
      MMP.Threefold.Mori.isCrepantBoundary_of_add_eq_pullback hlowpair e hL.isQFactorial.1 heb
        hKV hKVe ⟨MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier e hlowpair.2.2,
          isPullback_congr (add_sub_assoc _ _ _) (add_sub_assoc _ _ _) hpbl⟩
    refine supp_eq_of_forall_coeff_ne_zero_iff fun F => ?_
    have hlt := coeff_lt_one_of_isKltPair_of_isCrepantBoundary hklt' hL.isQFactorial.1 heb
      hcrepl F
    have hle : BV.coeff F ≤ 1 := hL.isDltPair.2.1 F
    have hge : 0 ≤ BV.coeff F := hL.isDltPair.1.2.1 F
    have hP0F : 0 ≤ P.coeff F := hP0 F
    simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hlt
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown]
    refine ne_zero_iff_floor_ne_zero ht₀ hge hle hP0F hlt ?_
    by_cases hF : F.support ⊆ MMP.Intersection.exceptionalLocus e
    · left
      obtain ⟨E, hE, hBV⟩ := hL.boundary_eq
      have h2 : 0 ≤ (MMP.Flips.birationalInverseTransform e heb B').coeff F :=
        transformDivisor_nonneg' _ (fun Q => hL.isLogCanonicalPair.2.1 Q) F
      have h1 : BV.coeff F = (MMP.Flips.birationalInverseTransform e heb B').coeff F + 1 := by
        rw [hBV, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hE F, if_pos hF]
        push_cast
        ring
      linarith
    · right
      obtain ⟨Q, hQ, -⟩ := MMP.Intersection.exists_primeDivisor_genericPoint_eq_of_not_subset hF
      have e1 := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq hX'n
        (D := ⟨V, e, hL.isQFactorial.1, heb, F⟩) hQ.symm (hcrep F)
      have e2 := IsDiscrepancy.eq_neg_coeff_of_map_genericPoint_eq hX'n
        (D := ⟨V, e, hL.isQFactorial.1, heb, F⟩) hQ.symm (hcrepl F)
      simp only [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        Divisor.coeff_toQDivisor] at e1 e2
      refine ⟨T.coeff Q, ?_, ?_⟩
      · have : t₀ * P.coeff F = t₀ * T.coeff Q := by linarith
        exact mul_left_cancel₀ ht₀.ne' this
      · have := hTB Q
        rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
          Divisor.coeff_toQDivisor] at this
        linarith
  · obtain ⟨hBδ, hpδ⟩ := hpbδ δ
    exact isRelativelySemiample_pullback e g' (isQCartier_of_isQFactorial sX' hQ' _) hpδ
      (hsemi δ hδ hδt)
  · exact isRelativelyNef_of_isPullback e g' hDq hpb hnef'

/-- **A common smooth model of two birational models over a normal base.** For proper birational
morphisms `f₁ : W ⟶ Z` and `f₂ : V ⟶ Z` from normal varieties, there is a smooth variety `W'`
birational over `Z` with projective birational morphisms `a : W' ⟶ W` and `r : W' ⟶ V` over
`Z`. -/
private theorem exists_common_resolution {Z W V : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sZ] [IsNormal Z] (f₁ : W ⟶ Z) (f₂ : V ⟶ Z) [IsProper f₁]
    [IsProper f₂] (hf₁ : IsBirationalMorphism f₁) (hf₂ : IsBirationalMorphism f₂)
    (h₁ : IsNormalVariety ℂ (f₁ ≫ sZ)) (h₂ : IsNormalVariety ℂ (f₂ ≫ sZ)) :
    ∃ (W' : Scheme.{0}) (w : W' ⟶ Z) (a : W' ⟶ W) (r : W' ⟶ V),
      IsNormalVariety ℂ (w ≫ sZ) ∧ IsBirationalMorphism w ∧ MMP.Mori.IsSmoothScheme (w ≫ sZ) ∧
      a ≫ f₁ = w ∧ IsProjectiveMorphism a ∧ IsBirationalMorphism a ∧
      r ≫ f₂ = w ∧ IsProjectiveMorphism r ∧ IsBirationalMorphism r := by
  let Xf : Bool → Scheme.{0} := fun b => Bool.rec V W b
  let F : ∀ b, Xf b ⟶ Z := fun b => Bool.rec (motive := fun b => Xf b ⟶ Z) f₂ f₁ b
  have hFp : ∀ b, IsProper (F b) := by
    intro b
    cases b
    · exact inferInstanceAs (IsProper f₂)
    · exact inferInstanceAs (IsProper f₁)
  obtain ⟨W', w, hW, hwb, gg, hs, -, hg, -, -⟩ :=
    @MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq ℂ _ _ Z sZ _ _
      Bool _ Xf F hFp
      (fun b => Bool.rec (motive := fun b => IsBirationalMorphism (F b)) hf₂ hf₁ b)
      (fun b => Bool.rec (motive := fun b => IsNormalVariety ℂ (F b ≫ sZ)) h₂ h₁ b)
      Empty _ Empty.elim (fun j => j.elim)
  exact ⟨W', w, gg true, gg false, hW, hwb, hs, (hg true).1, (hg true).2.1, (hg true).2.2,
    (hg false).1, (hg false).2.1, (hg false).2.2⟩

/-- **The crepant dlt model over a floor-lowering model.** Let `(X', B')` be the end of the
floor-lowering program for `(X, B)` over `Z`: `X'` is `ℚ`-factorial, `(X', B')` is lc,
`(X', B' - t₀T)` is klt for an effective divisor `T ≤ B'`, `K' + B'` is nef over `Z` and
`K' + B' - tT` is semiample over `Z` for `0 < t ≤ t₀`, and `K + B`, `K' + B'` have the same
pull-back to a common resolution. Then a crepant dlt lift `(Y, B_Y)` of `(X', B')`, with the
pencil `P = e^* T`, satisfies the conclusion of
`MMP.Fourfold.IsDltPair.exists_isRelativelySemiample_sub_smul_of_supp_eq_roundDown`. -/
private theorem core {X Z X' W : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) {K : Divisor X} {B : QDivisor X} (hZn : IsNormalVariety ℂ sZ)
    {g : X ⟶ Z} (hgZ : g ≫ sZ = sX) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sX g (Divisor.toQDivisor K + B))
    {g' : X' ⟶ Z} (hg'Z : g' ≫ sZ = sX') (hg' : IsProjectiveMorphism g')
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hQ' : IsQFactorial sX') {K' : Divisor X'}
    (hK' : ∃ n : ℕ, K'.IsCanonicalDivisor sX' n) {B' : QDivisor X'} {T : Divisor X'} {t₀ : ℚ}
    (ht₀ : 0 < t₀) (hlc' : MMP.Intersection.IsLogCanonicalPair sX' B')
    (hklt' : MMP.Fourfold.IsKltPair sX' (B' - t₀ • Divisor.toQDivisor T))
    (hT0 : 0 ≤ T) (hTB : Divisor.toQDivisor T ≤ B')
    (hsemi : ∀ t : ℚ, 0 < t → t ≤ t₀ → QDivisor.IsRelativelySemiample g'
      (Divisor.toQDivisor K' + B' - t • Divisor.toQDivisor T))
    (hnef' : QDivisor.IsRelativelyNef sX' g' (Divisor.toQDivisor K' + B'))
    {φ : X.RationalMap X'} (hover : MMP.Flips.RationalMap.IsOver g g' φ)
    {p : W ⟶ X} {q : W ⟶ X'} {h : X.RationalMap W} {G : RDivisor W}
    (hres : IsLogComparisonResolution sX sX' sW φ K (QDivisor.toRDivisor B) K'
      (QDivisor.toRDivisor B') p q h G G) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of ℂ)) (KY : Divisor Y) (BY : QDivisor Y)
      (gY : Y ⟶ Z) (φ : X.RationalMap Y) (P : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ IsQFactorial sY ∧ KY.IsCanonicalDivisor sY 4 ∧
      MMP.Intersection.IsDltPair sY BY ∧
      gY ≫ sZ = sY ∧ IsProjectiveMorphism gY ∧
      MMP.Mori.RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver g gY φ ∧
      (∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) (G : RDivisor W),
          IsLogComparisonResolution sX sY sW φ K (QDivisor.toRDivisor B) KY
            (QDivisor.toRDivisor BY) p q h G G) ∧
      0 ≤ P ∧ P.IsQCartier ∧ P.supp = (Divisor.toQDivisor BY.roundDown).supp ∧
      (∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
        QDivisor.IsRelativelySemiample gY (Divisor.toQDivisor KY + BY - δ • P)) ∧
      QDivisor.IsRelativelyNef sY gY (Divisor.toQDivisor KY + BY) ∧
      (QDivisor.IsRelativelySemiample gY (Divisor.toQDivisor KY + BY) ↔
        QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B)) ∧
      (BY.roundDown = 0 → QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B)) := by
  classical
  -- the varieties `X`, `X'`, `W` and `Z`
  have hXn : IsNormalVariety ℂ sX := hQ.1
  have hX'n : IsNormalVariety ℂ sX' := hQ'.1
  have hWn : IsNormalVariety ℂ sW := ⟨hres.isVariety, inferInstance⟩
  haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXn.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'n.1
  haveI : AlgebraicGeometry.IsVariety ℂ sW := hWn.1
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZn.1
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sW := hWn.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hpb : IsBirationalMorphism p := hres.isBirationalMorphism_left
  have hqb : IsBirationalMorphism q := hres.isBirationalMorphism_right
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hres.isProjectiveMorphism_left
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hres.isProjectiveMorphism_right
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hg
  haveI : IsProper g' := isProper_of_isProjectiveMorphism g' hg'
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hdimW : topologicalKrullDim W = 4 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sW hpb).symm.trans hdim
  have hdim' : topologicalKrullDim X' = 4 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' sW hqb).trans hdimW
  have hK'4 : K'.IsCanonicalDivisor sX' 4 := by
    obtain ⟨n, hn⟩ := hK'
    exact eq_of_isCanonicalDivisor hn hdim' ▸ hn
  -- the morphisms over `Z`
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal hZn
  have hpq : p ≫ g = q ≫ g' := comp_eq_comp_of_isLogComparisonResolution hres hover
  haveI : LocallyOfFiniteType g' :=
    LocallyOfFiniteType.of_comp (g := sZ) (f := g') (by rw [hg'Z]; infer_instance)
  have hg'b : IsBirationalMorphism g' :=
    MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_of_comp_left q g' hqb
      (hpq ▸ MMP.Mori.isBirationalMorphism_comp hpb hgb)
  -- the crepant dlt lift `e : Y ⟶ X'`
  obtain ⟨V, _, _, _, e, BV, hL⟩ := exists_isCrepantDltLift sX' hX' hdim' hK'4 hlc'
  haveI : IsProper e := isProper_of_isProjectiveMorphism e hL.isProjectiveMorphism
  have heb : IsBirationalMorphism e := hL.isBirationalMorphism
  haveI : IsDominant e := heb.isDominant
  have hVn : IsNormalVariety ℂ (e ≫ sX') := hL.isQFactorial.1
  haveI : QuasiCompact (e ≫ sX') := hVn.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (e ≫ sX')
  haveI : LocallyOfFiniteType (e ≫ sX') := hVn.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ (e ≫ sX') := hVn.1
  have hdimV : topologicalKrullDim V = 4 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX' (e ≫ sX') heb).symm.trans
      hdim'
  -- a common smooth model `W₂` of `W` and `V` over `Z`
  have hpgN : IsNormalVariety ℂ ((p ≫ g) ≫ sZ) := by
    rw [Category.assoc, hgZ, hres.comp_eq_left]; exact hWn
  have hegN : IsNormalVariety ℂ ((e ≫ g') ≫ sZ) := by
    rw [Category.assoc, hg'Z]; exact hVn
  obtain ⟨W₂, w, a, r, hW₂n, hwb, hW₂s, haw, haP, hab, hrw, hrP, hrb⟩ :=
    exists_common_resolution sZ (p ≫ g) (e ≫ g') (MMP.Mori.isBirationalMorphism_comp hpb hgb)
      (MMP.Mori.isBirationalMorphism_comp heb hg'b) hpgN hegN
  haveI : IsIntegral W₂ := hW₂n.1.toIsIntegral
  haveI : IsNormal W₂ := hW₂n.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hW₂n.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W₂ := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : QuasiCompact (w ≫ sZ) := hW₂n.1.toQuasiCompact
  haveI : CompactSpace W₂ := QuasiCompact.compactSpace_of_compactSpace (w ≫ sZ)
  haveI : AlgebraicGeometry.IsVariety ℂ (w ≫ sZ) := hW₂n.1
  haveI : IsProper a := isProper_of_isProjectiveMorphism a haP
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hrP
  haveI : IsDominant a := hab.isDominant
  haveI : IsDominant r := hrb.isDominant
  haveI : IsDominant w := hwb.isDominant
  have hapW : (a ≫ p) ≫ sX = w ≫ sZ := by rw [← haw, ← hgZ]; simp only [Category.assoc]
  have haW : a ≫ sW = w ≫ sZ := by rw [← hres.comp_eq_left, ← Category.assoc, hapW]
  have hrV : r ≫ e ≫ sX' = w ≫ sZ := by rw [← hrw, ← hg'Z]; simp only [Category.assoc]
  have hra : r ≫ e = a ≫ q := by
    haveI : IsDominant ((r ≫ e) ≫ g') := by rw [Category.assoc, hrw]; infer_instance
    refine MMP.Fourfold.Oai4C1.Main.eq_of_comp_eq hg'b ?_
    rw [Category.assoc, hrw, Category.assoc, ← hpq, haw]
  have hapb : IsBirationalMorphism (a ≫ p) := MMP.Mori.isBirationalMorphism_comp hab hpb
  have haqb : IsBirationalMorphism (a ≫ q) := MMP.Mori.isBirationalMorphism_comp hab hqb
  haveI : IsProper (a ≫ p) := inferInstance
  haveI : IsProper (a ≫ q) := inferInstance
  haveI : IsProper (r ≫ e) := inferInstance
  have hW₂X : IsNormalVariety ℂ ((a ≫ p) ≫ sX) := hapW ▸ hW₂n
  have hW₂W : IsNormalVariety ℂ (a ≫ sW) := haW ▸ hW₂n
  have hW₂V : IsNormalVariety ℂ (r ≫ e ≫ sX') := hrV ▸ hW₂n
  -- canonical divisors: `K_{W₂}` over `K_W`, and `K_Y = r_* K_{W₂}`
  obtain ⟨n, KW, hKW, hKWp, hKWq⟩ := hres.exists_canonicalDivisor
  obtain rfl := eq_of_isCanonicalDivisor hKW hdimW
  haveI : LocallyOfFiniteType (a ≫ sW) := hW₂W.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ (a ≫ sW) := hW₂W.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (a ≫ sW) hW₂W (n := 4)
    (by rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW (a ≫ sW) hab]
        exact hdimW)
  obtain ⟨KW₂, hKW₂, hKW₂a⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hWn hW₂W hab hKW hK₀
  obtain ⟨KV₀, hKV₀⟩ := MMP.Mori.exists_isCanonicalDivisor (e ≫ sX') hVn (n := 4) hdimV
  haveI : LocallyOfFiniteType (r ≫ e ≫ sX') := hW₂V.1.toLocallyOfFiniteType
  set KY : Divisor V := MMP.Mori.RationalMap.transformDivisor (X := W₂) r.toRationalMap KW₂
    with hKYdef
  have hKY : KY.IsCanonicalDivisor (e ≫ sX') 4 :=
    MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hVn hW₂V hrb hKV₀
      (by rw [hrV, ← haW]; exact hKW₂)
  have hKYe : MMP.Mori.RationalMap.transformDivisor (X := V) e.toRationalMap KY = K' := by
    rw [hKYdef, transformDivisor_transformDivisor_of_compHom_eq hW₂V hVn hX'n
        (f := r ≫ e) (by rw [Category.assoc]) rfl
        (MMP.Mori.isBirationalMorphism_comp hrb heb) heb (toRationalMap_compHom r e), hra,
      ← transformDivisor_transformDivisor_of_compHom_eq hW₂W hWn hX'n (f := a ≫ q)
        (by rw [Category.assoc, ← hres.comp_eq_right]) hres.comp_eq_right haqb hqb
        (toRationalMap_compHom a q), hKW₂a, hKWq]
  have hKWX : MMP.Mori.RationalMap.transformDivisor (X := W₂) (a ≫ p).toRationalMap KW₂ = K := by
    rw [← transformDivisor_transformDivisor_of_compHom_eq hW₂W hWn hXn (f := a ≫ p)
        (by rw [Category.assoc, hres.comp_eq_left]) hres.comp_eq_left hapb hpb (toRationalMap_compHom a p), hKW₂a,
      hKWp]
  -- the pencil and the crepant identity on `Y`
  obtain ⟨P, hP0, hPq, hPsupp, hPsemi, hnefY, hBc, hpbY⟩ :=
    dltModel hQ' hK'4 ht₀ hklt' hT0 hTB hsemi hnef' hL hKY hKYe
  -- the birational map `X ⤏ Y` through `W₂`
  obtain ⟨h₂, hinv₂, hbir₂, hid₂⟩ := exists_isInverse_and_isBirational_compHom hapb hrb
  have hoverY : MMP.Flips.RationalMap.IsOver g (e ≫ g') (h₂.compHom r) := by
    show (h₂.compHom r).compHom (e ≫ g') = g.toRationalMap
    have hid₂' : h₂.compHom (a ≫ p) = (Scheme.Hom.toRationalMap (𝟙 X) : X.RationalMap X) := hid₂
    rw [compHom_compHom, hrw, ← haw, ← Category.assoc, ← compHom_compHom, hid₂',
      toRationalMap_compHom, Category.id_comp]
  -- a common Cartier multiple `M (K + B)`, `M (K' + B')`
  have hDq : (Divisor.toQDivisor K + B).IsQCartier := hD.1
  have hD'q : (Divisor.toQDivisor K' + B').IsQCartier := isQCartier_of_isQFactorial sX' hQ' _
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c⟩ := hDq.exists_pos
  obtain ⟨m₂, hm₂, D₂, hD₂, hD₂c⟩ := hD'q.exists_pos
  have hM : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  set M := m₁ * m₂ with hMdef
  have hDX : Divisor.toQDivisor ((m₂ : ℤ) • D₁) = ((M : ℕ) : ℤ) • (Divisor.toQDivisor K + B) :=
    toQDivisor_natCast_smul hD₁ m₂
  have hDX' : Divisor.toQDivisor ((m₁ : ℤ) • D₂) =
      ((M : ℕ) : ℤ) • (Divisor.toQDivisor K' + B') := by
    rw [hMdef, Nat.mul_comm]; exact toQDivisor_natCast_smul hD₂ m₁
  set DX := (m₂ : ℤ) • D₁
  set DX' := (m₁ : ℤ) • D₂
  have hDXc : DX.IsCartier := hD₁c.zsmul _
  have hDX'c : DX'.IsCartier := hD₂c.zsmul _
  -- the pull-backs to `W` agree
  have hGX := Divisor.isPullback_pullback hDXc
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p DX)
  have hGX' := Divisor.isPullback_pullback hDX'c
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant q DX')
  set GX := DX.pullback hDXc (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p DX)
  set GX' := DX'.pullback hDX'c
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant q DX')
  have hGG : GX = GX' := by
    have h1 := isRCartierPullback_of_zsmul_eq p hM hDXc hDX.symm ⟨_, hGX⟩
    have h2 := isRCartierPullback_of_zsmul_eq q hM hDX'c hDX'.symm ⟨_, hGX'⟩
    have hl := hres.isRCartierPullback_left
    have hr := hres.isRCartierPullback_right
    rw [logCanonicalDivisor_toRDivisor] at hl hr
    have e1 := IsRCartierPullback.eq p hl h1
    have e2 := IsRCartierPullback.eq q hr h2
    have hM0 : (1 / (M : ℝ)) ≠ 0 := by positivity
    exact Divisor.toRDivisor_injective (smul_right_injective _ hM0 (e1.symm.trans e2))
  have hGXc : GX.IsCartier := hGX.isCartier hDXc
  have hG₂ := Divisor.isPullback_pullback hGXc
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant a GX)
  set G₂ := GX.pullback hGXc (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant a GX)
  have hG₂X : DX.IsPullback (a ≫ p)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (a ≫ p) DX) G₂ :=
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl hGX hG₂ _
  have hG₂X' : DX'.IsPullback (a ≫ q)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (a ≫ q) DX') G₂ := by
    have hGX'' : DX'.IsPullback q
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant q DX') GX := by
      rw [hGG]; exact hGX'
    exact MMP.ProgramBaseChange.divisor_isPullback_comp rfl hGX'' hG₂ _
  -- the pull-back to `Y` of `M (K' + B')`
  obtain ⟨DY, hDY, hpDY⟩ := hpbY M hM DX' hDX' hDX'c
  have hDYc : DY.IsCartier := hpDY.isCartier hDX'c
  have hDYr : DY.IsPullback r
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant r DY) G₂ := by
    have h1 := Divisor.isPullback_pullback hDYc
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant r DY)
    have h2 : DX'.IsPullback (a ≫ q)
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant (a ≫ q) DX')
        (DY.pullback hDYc
          (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant r DY)) :=
      MMP.ProgramBaseChange.divisor_isPullback_comp hra hpDY h1 _
    have h3 : DY.pullback hDYc
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant r DY) = G₂ :=
      h2.eq hDX'c hG₂X'
    rw [← h3]
    exact h1
  -- `K + B` and `K_Y + B_Y` pull back to the same `ℚ`-divisor `Ψ` on `W₂`
  set Ψ : QDivisor W₂ := ((M : ℚ)⁻¹) • Divisor.toQDivisor G₂ with hΨdef
  have hΨ : Divisor.toQDivisor G₂ = ((M : ℕ) : ℤ) • Ψ := by
    rw [hΨdef]
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    ext F
    simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
  have hYq : (Divisor.toQDivisor KY + BV).IsQCartier := hpbY.isQCartier hD'q
  have hKBp : (Divisor.toQDivisor K + B).IsPullback (a ≫ p)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier (a ≫ p) hDq) Ψ :=
    isPullback_of_smul hDq hM hDX hDXc hΨ hG₂X
  have hKYp : (Divisor.toQDivisor KY + BV).IsPullback r
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier r hYq) Ψ :=
    isPullback_of_smul hYq hM hDY hDYc hΨ hDYr
  have hwg : r ≫ e ≫ g' = (a ≫ p) ≫ g := by rw [hrw, ← haw, Category.assoc]
  have hequiv : QDivisor.IsRelativelySemiample (e ≫ g') (Divisor.toQDivisor KY + BV) ↔
      QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B) := by
    rw [← isRelativelySemiample_iff_of_isPullback hVn r hrb hW₂V (e ≫ g') hYq hKYp, hwg,
      isRelativelySemiample_iff_of_isPullback hXn (a ≫ p) hapb hW₂X g hDq hKBp]
  -- the comparison on `W₂`
  have hKW₂' : KW₂.IsCanonicalDivisor (w ≫ sZ) 4 := haW ▸ hKW₂
  have hres₂ : IsLogComparisonResolution sX (e ≫ sX') (w ≫ sZ) (h₂.compHom r) K
      (QDivisor.toRDivisor B) KY (QDivisor.toRDivisor BV) (a ≫ p) r h₂
      ((1 / (M : ℝ)) • Divisor.toRDivisor G₂) ((1 / (M : ℝ)) • Divisor.toRDivisor G₂) :=
    { isVariety := hW₂n.1
      isSmoothScheme := hW₂s
      comp_eq_left := hapW
      comp_eq_right := hrV
      isProjectiveMorphism_left := haP.comp hres.isProjectiveMorphism_left
      isProjectiveMorphism_right := hrP
      isBirationalMorphism_left := hapb
      isBirationalMorphism_right := hrb
      isInverse := hinv₂
      compHom_eq := rfl
      exists_canonicalDivisor := ⟨4, KW₂, hKW₂', hKWX, rfl⟩
      isRCartierPullback_left := by
        rw [logCanonicalDivisor_toRDivisor]
        exact isRCartierPullback_of_zsmul_eq (a ≫ p) hM hDXc hDX.symm ⟨_, hG₂X⟩
      isRCartierPullback_right := by
        rw [logCanonicalDivisor_toRDivisor]
        exact isRCartierPullback_of_zsmul_eq r hM hDYc hDY.symm ⟨_, hDYr⟩
      effective := fun P => by simp
      isExceptional := fun P hP => absurd (by simp) hP }
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, e ≫ sX', KY, BV, e ≫ g',
    h₂.compHom r, P,
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨hVn.1, hL.isProjectiveMorphism.comp ((AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mp hX').2⟩,
    hL.isQFactorial, hKY, hL.isDltPair, by rw [Category.assoc, hg'Z],
    hL.isProjectiveMorphism.comp hg', hbir₂, hoverY,
    ⟨W₂, inferInstance, inferInstance, inferInstance, w ≫ sZ, a ≫ p, r, h₂, _, hres₂⟩,
    hP0, hPq, hPsupp, ⟨t₀, ht₀, fun δ hδ hδt => hPsemi δ hδ hδt.le⟩, hnefY, hequiv, ?_⟩
  -- an empty floor: the pencil vanishes
  intro hfloor
  have hP00 : P = 0 := by
    ext F
    by_contra hF
    have hmem : F.genericPoint ∈ P.supp := DivisorWithCoeffs.mem_supp_iff.mpr ⟨F, hF, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    rw [hPsupp, hfloor] at hmem
    obtain ⟨E, hE, -⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    exact hE (by simp)
  have h1 := hPsemi (t₀ / 2) (by positivity) (by linarith)
  rw [hP00, smul_zero, sub_zero] at h1
  exact hequiv.mp h1

/-! ### The main proof -/

private theorem solution
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 4)
    {g : X ⟶ Z} (hgZ : g ≫ sZ = sX) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sX g (Divisor.toQDivisor K + B)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of ℂ)) (KY : Divisor Y) (BY : QDivisor Y)
      (gY : Y ⟶ Z) (φ : X.RationalMap Y) (P : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ IsQFactorial sY ∧ KY.IsCanonicalDivisor sY 4 ∧
      MMP.Intersection.IsDltPair sY BY ∧
      gY ≫ sZ = sY ∧ IsProjectiveMorphism gY ∧
      MMP.Mori.RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver g gY φ ∧
      (haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
       ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) (G : RDivisor W),
          IsLogComparisonResolution sX sY sW φ K (QDivisor.toRDivisor B) KY
            (QDivisor.toRDivisor BY) p q h G G) ∧
      0 ≤ P ∧ P.IsQCartier ∧ P.supp = (Divisor.toQDivisor BY.roundDown).supp ∧
      (∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
        QDivisor.IsRelativelySemiample gY (Divisor.toQDivisor KY + BY - δ • P)) ∧
      QDivisor.IsRelativelyNef sY gY (Divisor.toQDivisor KY + BY) ∧
      (QDivisor.IsRelativelySemiample gY (Divisor.toQDivisor KY + BY) ↔
        QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B)) ∧
      (BY.roundDown = 0 → QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B)) := by
  classical
  obtain ⟨t₀, ht₀, Pr, BU, hn, hproj, hfin, hBU, hlk, hnull, hnef', φ, hφb, hover, hnoext, hB',
    hBlow, hsemi, W, _, _, _, sW, p, q, h, G, hres⟩ :=
    IsDltPair.exists_relativeDltProgram_sub_smul_roundDown hX hdim hQ hK hB hZ hZn hdimZ hgZ hg hgb
      hD
  haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
  have hle : ((Pr.n.toNat : ℕ) : ℕ∞) ≤ Pr.n := (ENat.coe_toNat hn).le
  have hmodel := Pr.isRelativeDltModel Pr.n.toNat hle
  -- the reduced boundary `T' = φ_* ⌊B⌋` on the last model
  set T := MMP.Mori.RationalMap.transformDivisor φ B.roundDown with hTdef
  have hTq : MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor B.roundDown) =
      Divisor.toQDivisor T := transformDivisor_toQDivisor φ _
  have hT0 : 0 ≤ T := transformDivisor_nonneg' φ fun E => by
    show (0 : ℤ) ≤ B.roundDown.coeff E
    rw [DivisorWithCoeffs.coeff_roundDown]
    exact Int.floor_nonneg.mpr (hB.1.2.1 E)
  have hTB : Divisor.toQDivisor T ≤ divisorSeq B BU Pr.n.toNat := by
    rw [← hTq, hB', ← sub_nonneg, ← map_sub]
    refine transformDivisor_nonneg' φ fun E => ?_
    show (0 : ℚ) ≤ (B - Divisor.toQDivisor B.roundDown).coeff E
    rw [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown,
      sub_nonneg]
    exact Int.floor_le _
  have hklt := (hlk Pr.n.toNat hle).2
  rw [hBlow, hTq] at hklt
  exact core hdim hQ hZn hgZ hg hgb hD hmodel.comp_eq hmodel.isProjectiveMorphism
    (hproj.2 Pr.n.toNat hle) hmodel.isQFactorial hmodel.isCanonicalDivisor ht₀
    (hlk Pr.n.toNat hle).1 hklt hT0 hTB (fun t ht htt => hTq ▸ hsemi t ht htt) hnef' hover hres

end Proof_lem_fourfold_dlt_semiample_floor_pencil

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A crepant dlt model with a semiample pencil off its whole floor.** Let `g : X ⟶ Z` be a
projective birational morphism of normal projective complex fourfolds, `(X, B)` a `ℚ`-factorial
dlt pair (`MMP.Intersection.IsDltPair`) with canonical divisor `K` and `K + B` nef over `Z`.
Then there are a projective `ℚ`-factorial dlt pair `(Y, B_Y)` with canonical divisor `K_Y`, a
projective morphism `g_Y : Y ⟶ Z`, and a birational map `φ : X ⤏ Y` over `Z` such that
`K + B` and `K_Y + B_Y` have the same pull-back to a common resolution, and an effective
`ℚ`-Cartier `P` on `Y` with `Supp P = Supp ⌊B_Y⌋`, such that
* `K_Y + B_Y - δP` is semiample over `Z` for every rational `0 < δ < δ₀`, for some `δ₀ > 0`;
* `K_Y + B_Y` is nef over `Z`;
* `K_Y + B_Y` is semiample over `Z` if and only if `K + B` is;
* if `⌊B_Y⌋ = 0`, then `K + B` is semiample over `Z`. -/
@[mmp "lem_fourfold_dlt_semiample_floor_pencil"]
public theorem IsDltPair.exists_isRelativelySemiample_sub_smul_of_supp_eq_roundDown
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hQ : IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 4)
    {g : X ⟶ Z} (hgZ : g ≫ sZ = sX) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sX g (Divisor.toQDivisor K + B)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : CompactSpace Y) (_ : IsLocallyNoetherian Y)
      (_ : IsNormal Y) (sY : Y ⟶ Spec (.of ℂ)) (KY : Divisor Y) (BY : QDivisor Y)
      (gY : Y ⟶ Z) (φ : X.RationalMap Y) (P : QDivisor Y),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ IsQFactorial sY ∧ KY.IsCanonicalDivisor sY 4 ∧
      MMP.Intersection.IsDltPair sY BY ∧
      gY ≫ sZ = sY ∧ IsProjectiveMorphism gY ∧
      MMP.Mori.RationalMap.IsBirational φ ∧ MMP.Flips.RationalMap.IsOver g gY φ ∧
      (haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
       ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
          (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W) (G : RDivisor W),
          IsLogComparisonResolution sX sY sW φ K (QDivisor.toRDivisor B) KY
            (QDivisor.toRDivisor BY) p q h G G) ∧
      0 ≤ P ∧ P.IsQCartier ∧ P.supp = (Divisor.toQDivisor BY.roundDown).supp ∧
      (∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 < δ → δ < δ₀ →
        QDivisor.IsRelativelySemiample gY (Divisor.toQDivisor KY + BY - δ • P)) ∧
      QDivisor.IsRelativelyNef sY gY (Divisor.toQDivisor KY + BY) ∧
      (QDivisor.IsRelativelySemiample gY (Divisor.toQDivisor KY + BY) ↔
        QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B)) ∧
      (BY.roundDown = 0 → QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B)) :=
        by revert X Z sX sZ hX hdim hQ K hK B hB hZ hZn hdimZ g hgZ hg hgb hD; first | exact Proof_lem_fourfold_dlt_semiample_floor_pencil.solution | exact Proof_lem_fourfold_dlt_semiample_floor_pencil.solution _ | exact Proof_lem_fourfold_dlt_semiample_floor_pencil.solution _ _ | exact Proof_lem_fourfold_dlt_semiample_floor_pencil.solution _ _ _ | exact Proof_lem_fourfold_dlt_semiample_floor_pencil.solution _ _ _ _

end MMP.Fourfold

