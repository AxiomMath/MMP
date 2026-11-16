module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.MMP.Fourfold.Preadmissible.SurfaceConductorDescent
public import MMP.AlgebraicGeometry.MMP.Surface.ComplementedLcSemiample
public import MMP.AlgebraicGeometry.MMP.Surface.CrepantDltModification
public import MMP.AlgebraicGeometry.MMP.Abundance.PreadmissibleGenerationSurface
public import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
public import MMP.AlgebraicGeometry.MMP.Abundance.Curve.SlcPrescribedSections
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Divisor.CartierLineBundle
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorPullback
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Singularities.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.AlgebraicGeometry.Singularities.Slc.NodeResidueForm
public import MMP.AlgebraicGeometry.Divisor.MeromorphicFunctionField

/-!
# Complemented relative abundance for projective sdlt surfaces

Let `(T, Δ; L)` be a projective sdlt adjoint pair of pure dimension two over `ℂ`, with
normalization `ν : ⨿ᵢ Tᵢ ⟶ T` and boundaries `Θᵢ = Cᵢ + Δᵢ`, so that `ν^*L|_{Tᵢ} = K_{Tᵢ} + Θᵢ`,
and let `f : T ⟶ Z` be a morphism to a projective complex variety. Suppose `L` is `f`-nef and
`L + A ∼_ℚ f^*H` for an effective rational Cartier divisor `A` on `T` and a rational Cartier
divisor `H` on `Z`. Then `L` is `f`-semiample on the whole union `T`: in every degree `m` divisible
by some `m₀ > 0`, near every fibre of `f` the sheaf `𝒪_T(mL)` has sections generating it at any
given point. These sections are sections of the invertible sheaf on `T` itself, so their components
agree, with the residue identification, across the conductor; semiampleness of every
`K_{Tᵢ} + Θᵢ` alone does not give them.

The proof makes each `K_{Tᵢ} + Θᵢ` semiample over `Z` by the complemented normal lc surface
theorem, twists by a common pull-back from `Z` to make the normalized adjoints globally
semiample, and descends preadmissible section systems on crepant dlt models through the
conductor (`MMP.Fourfold.IsSdltAdjointPair.existsUnique_pullback_eq_of_mem_preadmissibleSections`).

## Main results

* `MMP.Fourfold.IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_add_qLinearlyEquivalent`.

## Implementation notes

* As in `MMP.Fourfold.IsSdltAdjointPair`, the adjoint `L = K_T + Δ` is not a divisor on `T`; a
  section of `𝒪_T(mL)` over an open `W` is a family `t = (tᵢ)ᵢ` of rational `m`-canonical forms
  on the `Tᵢ` which, for every local generator `g` of `𝒪_T(mL)` on an open `U ⊆ W`
  (`MMP.Fourfold.IsAdjointGeneratorOn`), is `ν^*a · g` near every point `y ∈ U` for a function
  `a`; it generates at `y` when `a` is a unit at `y`. Local generators are unique up to units of
  `𝒪_T`, so it is equivalent to ask this for one generator near each point; the statement asks it
  for all of them, together with the existence of generators in degree `m`, so that it can be
  read against any generator system, such as Poincaré residues of generators on an ambient
  space. `f`-semiampleness of `L` is surjectivity of `f^* f_* 𝒪_T(mL) → 𝒪_T(mL)`, that is, for
  every `x ∈ T` a section over `f⁻¹(V)`, `V` a neighbourhood of `f(x)`, generating at `x`. It is
  stated for every positive multiple `m` of some `m₀`, so that `m` can be chosen divisible by any
  given index.
* As for semi-dlt pairs, the irreducible components of `T` are required to be normal: every
  `νᵢ` is a closed immersion. Otherwise a conductor curve of a component may be glued to itself,
  where the residue condition of `MMP.Fourfold.IsAdjointGeneratorOn` compares no two distinct
  branches, and local generators of `𝒪_T(mL)` are then not unique up to units of `𝒪_T`.
* Nefness and the complement are read on the normalization, where they are statements about
  `ℚ`-divisors: `L` is `f`-nef if and only if every `ν^*L|_{Tᵢ} = K_{Tᵢ} + Θᵢ` is
  `(νᵢ ≫ f)`-nef, `ν` being finite and surjective; the complement enters through
  `Aᵢ = νᵢ^*A ≥ 0`, `ℚ`-Cartier, with `K_{Tᵢ} + Θᵢ + Aᵢ ∼_ℚ (νᵢ ≫ f)^*H`. The `Aᵢ` are not
  required to come from one divisor on `T`. As in
  `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`, the
  pull-back of `H` is that of the invertible sheaf `M = 𝒪_Z(mH)`, so `Z` need not be normal;
  one `M` and one `m` serve every component.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

section

namespace Proof_thm_mmp_surface_complemented_sdlt_relative_abundance

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Mori MMP.Flips

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The `m`-th power of the adjoint of an sdlt pair is generated by global sections: for every
`x` there is a family `t` which near every point `y` is `ν^*a · g` for a local generator `g` of
`𝒪_T(mL)`, with `a` a unit near `x`. -/
private def IsGloballyGeneratedAdjoint {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (Θ : ∀ i, QDivisor (N.X i)) (m : ℕ) : Prop :=
  ∀ x : T, ∃ t : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m,
    ∀ y : T, ∃ (U : T.Opens) (_ : y ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m)
      (a : Γ(T, U)), IsAdjointGeneratorOn N 2 m Θ U g ∧ (y = x → IsUnit a) ∧
        ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
          t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i

/-! ### Pull-backs of local equations -/

/-- The generic point of an integral scheme is an associated point. -/
private theorem genericPoint_mem_schemeAssociatedPoints (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] :
    genericPoint X ∈ Stacks.Divisors.schemeAssociatedPoints X :=
  mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X
    (by rw [irreducibleComponents_eq_singleton]; rfl) (genericPoint_spec X)

open MMP.Intersection in
/-- The pull-back of a regular local equation is a local equation of the pull-back. -/
private theorem isLocalEquationAt_of_isPullback {X Y : Scheme.{0}} (g : X ⟶ Y)
    {H : Y.CartierDivisor} {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {W : Y.Opens}
    {h : Γ(Y, W)} (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit)
    {x : X} (hx : g x ∈ W) :
    IsLocalEquationAt HX x
      (stalkToTotalQuotient x (X.presheaf.germ (g ⁻¹ᵁ W) x hx (g.app W h))) := by
  have h1 : IsLocalEquationAt H (g x)
      (stalkToTotalQuotient (g x) (Y.presheaf.germ W (g x) hx h)) :=
    ⟨W, hx, hu.unit, hloc, germ_toTotalQuotient hx h⟩
  have hf : ∀ {Z : Scheme.{0}} {z : Z} (c : Z.presheaf.stalk z),
      IsFraction (stalkToTotalQuotient z c) c 1 := fun c => ⟨by simp, by simp⟩
  have := hHX.isLocalEquationAt h1 (hf _) (by rw [map_one]; exact hf _)
  rwa [Scheme.Hom.germ_stalkMap_apply] at this

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

/-- The order of `v⁻¹` is minus the order of `v`. -/
private theorem scheme_ord_inv' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {v : X.functionField} (hv : v ≠ 0) {z : X} : X.ord v⁻¹ z = -X.ord v z := by
  simpa [zpow_neg_one] using MMP.Mori.ord_zpow z hv (-1)

open MMP.Intersection in
/-- The order of the pull-back of a Cartier divisor along a prime divisor is the order of the
pulled-back local equation. -/
private theorem primeDivisorOrder_eq_ord_of_isPullback {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (g : X ⟶ Y) {H : Y.CartierDivisor}
    {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {W : Y.Opens} {h : Γ(Y, W)}
    (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit)
    (P : MMP.Mori.PrimeDivisor X) (hP : g P.genericPoint ∈ W)
    (hne : X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h) ≠ 0) :
    primeDivisorOrder P HX = X.ord (algebraMap _ X.functionField
      (X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h))) P.genericPoint := by
  set V := primeDivisorSubvariety P
  set c : X.presheaf.stalk V.genericPoint :=
    X.presheaf.germ (g ⁻¹ᵁ W) P.genericPoint hP (g.app W h) with hc
  have hloc' : IsLocalEquationAt HX V.genericPoint (stalkToTotalQuotient V.genericPoint c) :=
    isLocalEquationAt_of_isPullback g hHX hu hloc hP
  have : Ring.KrullDimLE 1 (X.presheaf.stalk V.genericPoint) :=
    krullDimLE_of_coheight_le P.coheight_genericPoint.le
  have hO := isOrderAlong_of_isFraction (V := V) hloc' (mem_nonZeroDivisors_of_ne_zero hne)
    (one_mem _) ⟨by simp, by rw [map_one, one_mul]⟩
  rw [hO.primeDivisorOrder_eq, scheme_ord_algebraMap P.coheight_genericPoint hne]
  simp only [Ring.ord_one, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  rfl

open MMP.Intersection in
/-- Off the support of `H`, a regular local equation of `H` is a unit at the point. -/
private theorem isUnit_germ_of_notMem_cartierSupport {Y : Scheme.{0}} {H : Y.CartierDivisor}
    {W : Y.Opens} {h : Γ(Y, W)} (hu : IsUnit (toTotalQuotient W h))
    (hloc : IsLocalEquationOn H W hu.unit) {y : Y} (hy : y ∈ W) (hnot : y ∉ cartierSupport H) :
    IsUnit (Y.presheaf.germ W y hy h) := by
  have e1 : IsLocalEquationAt H y (stalkToTotalQuotient _ (Y.presheaf.germ W y hy h)) :=
    ⟨W, hy, hu.unit, hloc, germ_toTotalQuotient (X := Y) hy h⟩
  obtain ⟨w, hw⟩ := (isLocalEquationAt_one_of_notMem_cartierSupport hnot).exists_eq_mul_units e1
  rw [one_mul] at hw
  rw [stalkToTotalQuotient_injective _ hw]
  exact w.isUnit

open MMP.Intersection in
/-- The pull-back of a regular local equation of `H` along a morphism from an integral scheme
satisfying the pull-back condition has non-zero germs. -/
private theorem germ_ne_zero_of_isPullback {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] (g : X ⟶ Y) {H : Y.CartierDivisor}
    {HX : X.CartierDivisor} (hHX : IsPullback g H HX) {W : Y.Opens} {h : Γ(Y, W)}
    (hu : IsUnit (toTotalQuotient W h)) (hloc : IsLocalEquationOn H W hu.unit) {x : X}
    (hx : g x ∈ W) : X.presheaf.germ (g ⁻¹ᵁ W) x hx (g.app W h) ≠ 0 := by
  intro h0
  have hsec : g.app W h = 0 := germ_injective_of_isIntegral X x hx (by rw [h0, map_zero])
  set ξ := genericPoint X
  have hξ : ξ ∈ g ⁻¹ᵁ W :=
    ((genericPoint_spec X).mem_open_set_iff (g ⁻¹ᵁ W).isOpen).mpr ⟨x, trivial, hx⟩
  have hξ' : g ξ ∈ W := hξ
  have h2 := (isUnit_germ_of_notMem_cartierSupport hu hloc hξ'
    (hHX.1 ξ (genericPoint_mem_schemeAssociatedPoints X))).map (g.stalkMap ξ).hom
  rw [Scheme.Hom.germ_stalkMap_apply, hsec, map_zero] at h2
  exact not_isUnit_zero h2

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
      simpa [irreducibleComponents_eq_singleton] using W.2
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
    MMP.CartierDivisorPullback.ofFunctionField ⊤ (Units.mk0 r₀ hr0) with hc
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

/-! ### The normalization components -/

/-- A scheme projective over a field is quasi-compact. -/
private theorem compactSpace_of_isProjectiveMorphism {X : Scheme.{0}}
    {s : X ⟶ Spec (.of ℂ)} (hs : IsProjectiveMorphism s) : CompactSpace X :=
  haveI : IsProper s := isProper_of_isProjectiveMorphism s hs
  (quasiCompact_iff_compactSpace s).mp inferInstance

/-- The normalization of a projective sdlt pair has finitely many components. -/
private theorem finite_ι {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) : Finite N.ι := by
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : CompactSpace T := compactSpace_of_isProjectiveMorphism hΔ.isProjectiveMorphism
  haveI : IsNoetherian T := ⟨⟩
  haveI : IsReduced T := hΔ.isBoundary.2.1
  obtain ⟨φ, -⟩ := N.exists_iso
  haveI : IsFinite (slcCurveNormalization T hT) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field ℂ sT) hT
  haveI : CompactSpace (Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT) :=
    QuasiCompact.compactSpace_of_compactSpace (slcCurveNormalization T hT)
  haveI : CompactSpace ↥(∐ N.X : Scheme.{0}) := (Scheme.homeoOfIso φ).symm.compactSpace
  haveI : CompactSpace (Σ i, N.X i) := (sigmaMk N.X).symm.compactSpace
  have hcov : (Set.univ : Set (Σ i, N.X i)) ⊆
      ⋃ i, Set.range (@Sigma.mk N.ι (fun j => ↥(N.X j)) i) := by
    rintro ⟨i, y⟩ -
    exact Set.mem_iUnion.mpr ⟨i, y, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun i => isOpen_range_sigmaMk) hcov
  refine Set.finite_univ_iff.mp (t.finite_toSet.subset fun i _ => ?_)
  obtain ⟨x⟩ : Nonempty (N.X i) := inferInstance
  obtain ⟨j, hj, y, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ⟨i, x⟩))
  have hji : j = i := congrArg Sigma.fst hy
  exact hji ▸ hj

/-- A finite morphism is quasi-projective: the structure sheaf of its source is relatively ample,
the inverse image of an affine open being affine. -/
private theorem isQuasiProjective_of_isFinite {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] :
    IsQuasiProjective f := by
  refine ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X, ?_⟩
  refine (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f
    (Stacks.Ample.unitModule X)).mp ?_
  refine (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr ?_
  intro V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  infer_instance

/-- A finite morphism into a scheme projective over a field is projective over that field. -/
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

/-- The normalization components of a projective sdlt pair are projective varieties. -/
private theorem isProjectiveVariety_normalization {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) (i : N.ι) :
    Mori.IsProjectiveVariety ℂ (N.n i ≫ sT) := by
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  haveI := N.isFinite_n i
  haveI : MMP.Mori.IsVariety ℂ (N.n i ≫ sT) := (N.isNormalVariety i).1
  exact ⟨isProjectiveMorphism_comp_of_isFinite (N.n i) sT hΔ.isProjectiveMorphism⟩

/-- The normalization pairs `(Tᵢ, Θᵢ)` of an sdlt pair are log canonical. -/
private theorem isLogCanonicalPair_normalization {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) (i : N.ι) :
    MMP.Intersection.IsLogCanonicalPair (N.n i ≫ sT) (Θ i) := by
  obtain ⟨K, hK⟩ := hΔ.exists_isDltPair i
  exact ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair _ hK.1.2.1 _).mpr hK).1

/-- The normalization components of an sdlt pair of dimension `n` have dimension `n`. -/
private theorem topologicalKrullDim_normalization {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) (i : N.ι) :
    topologicalKrullDim (N.X i) = n := by
  obtain ⟨K, hK⟩ := hΔ.exists_isDltPair i
  exact hK.1.2.1.1

/-- **Step 1.** Every normalized adjoint `K_{Tᵢ} + Θᵢ` is semiample over `Z`, for every canonical
divisor of `Tᵢ`, by the complemented normal lc surface theorem. -/
private theorem isRelativelySemiample_normalization
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
    [∀ i, QuasiCompact (N.n i ≫ sT)] [∀ i, CompactSpace (N.X i)]
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {K : ∀ i, Divisor (N.X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (N.n i ≫ sT) 2)
    (hnef : ∀ i, (Divisor.toQDivisor (K i) + Θ i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ f))
    {A : ∀ i, QDivisor (N.X i)} (hA : ∀ i, 0 ≤ A i) (hAq : ∀ i, (A i).IsQCartier)
    {G : ∀ i, QDivisor (N.X i)}
    (hDG : ∀ i, (Divisor.toQDivisor (K i) + Θ i + A i).QLinearlyEquivalent (G i))
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (N.X i), Divisor.toQDivisor L = (m : ℤ) • G i ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (N.n i ≫ f)).obj M))
    (i : N.ι) (K' : Divisor (N.X i)) (hK' : K'.IsCanonicalDivisor (N.n i ≫ sT) 2) :
    QDivisor.IsRelativelySemiample (N.n i ≫ f) (Divisor.toQDivisor K' + Θ i) := by
  obtain ⟨m₀, hm₀, hL₀⟩ := hGM
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ :=
    MMP.Threefold.exists_isRelativelyFreeDivisor_of_isLogCanonicalPair_of_add_qLinearlyEquivalent
      (N.n i ≫ sT) sZ (isProjectiveVariety_normalization h i) (hK i)
      (isLogCanonicalPair_normalization h i) hZ (N.n i ≫ f) (by rw [Category.assoc, hf])
      (hnef i) (hA i) (hAq i) (hDG i) M ⟨m₀, hm₀, hL₀ i⟩
  obtain ⟨φ, hφ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (N.n i ≫ sT)
    (N.isNormalVariety i) hK' (hK i)
  have hpow : ∀ n : ℕ, principalDivisor (φ ^ n) = (n : ℤ) • principalDivisor φ := by
    intro n
    rw [natCast_zsmul]
    exact map_nsmul Mori.principalDivisorHom n (Additive.ofMul φ)
  refine isRelativelySemiample_of_isRelativelyFreeDivisor (N.n i ≫ f) _
    ⟨m, hm, L + (m : ℤ) • principalDivisor φ, ?_, hLc.add ((Divisor.isCartier_principalDivisor φ).zsmul _),
      ?_⟩
  · rw [map_add, hL, map_zsmul, ← hφ, map_sub]
    simp only [smul_add, smul_sub]
    abel
  · have hle : (L + (m : ℤ) • principalDivisor φ).LinearlyEquivalent L :=
      ⟨φ ^ m, by rw [add_sub_cancel_left, hpow]⟩
    exact epi_counit_of_iso (N.n i ≫ f) hle.divisorialSheafIso hfree

/-! ### Pull-back of forms -/

/-- The pull-back of forms along a birational morphism is injective. -/
private theorem pullbackRationalPluriForms_injective {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [IsDominant f] (hf : IsBirationalMorphism f) {d : ℕ} (hd : topologicalKrullDim X = d)
    (m : ℤ) :
    Function.Injective (pullbackRationalPluriForms sX f (d := d) (m := m)) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hd)
  have key : ∀ σ σ' : PluriForms ℂ X.functionField d m,
      pullbackFormsAlong hω m σ = pullbackFormsAlong hω m σ' → σ = σ' := by
    intro σ σ' h1
    set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
    refine b.repr.injective (Finsupp.ext fun u => ?_)
    obtain rfl : u = () := rfl
    have h2 := congrArg (fun σ => (ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m).repr
      σ ()) h1
    simp only [repr_pullbackFormsAlong] at h2
    exact hbij.injective h2
  intro τ τ' h
  refine key τ τ' ?_
  rw [← pullbackForms_eq hω m τ, ← pullbackForms_eq hω m τ']
  exact h

/-- The pull-back of a nonzero form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [IsDominant f] (hf : IsBirationalMorphism f) {d : ℕ} (hd : topologicalKrullDim X = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hd)
  intro h0
  have h1 : pullbackFormsAlong hω m τ = 0 := (pullbackForms_eq hω m τ).symm.trans h0
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    (Module.Basis.ne_zero _ _) h1

/-! ### Crepant models -/

/-- The order of the pull-back of `h • τ` along a divisor over `X` is the order of the pull-back
of `h` plus that of `τ`. -/
private theorem ordPullback_smul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : DivisorOver ℂ sX) {m : ℤ} {h : X.functionField}
    (hh : h ≠ 0) {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    D.ordPullback (h • τ) = D.Y.ord (functionFieldMap D.f h) D.E.genericPoint + D.ordPullback τ := by
  let := functionFieldAlgebra sX
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  have hc : (ZTensorPower.basis b m).repr τ () ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  have hrep : (ZTensorPower.basis b m).repr (h • τ) () =
      h * (ZTensorPower.basis b m).repr τ () := by
    have := congrArg (fun f => f ()) ((ZTensorPower.basis b m).repr.map_smul h τ)
    simp only [Finsupp.smul_apply, smul_eq_mul] at this
    exact (congrArg (fun f => f ()) (congrArg (ZTensorPower.basis b m).repr rfl)).trans this
  rw [hN m _ (smul_ne_zero hh hτ), hN m τ hτ, hrep, map_mul,
    Scheme.ord_mul ((map_ne_zero _).mpr hh) ((map_ne_zero _).mpr hc)]
  ring

/-- **The adjoint of a crepant model of a pair with globally semiample adjoint is globally
semiample.** If `(Y, B_Y)` is crepant over `(X, B)` and `K_X + B` is semiample, so is
`K_Y + B_Y`: a global section `σ` of `𝒪_X(m(K_X + B))` generating at `q(y)` pulls back to a
section of `𝒪_Y(m(K_Y + B_Y))` generating at `y`, since near `q(η_E)` it is a regular multiple
`h τ` of a local generator `τ`, and `ord_E q^*τ = -m b_E` by crepancy. -/
private theorem isRelativelySemiample_of_isCrepantBoundary {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) {B : QDivisor X}
    (hsemi : QDivisor.IsRelativelySemiample sX (Divisor.toQDivisor K + B))
    (q : Y ⟶ X) (hY : IsNormalVariety ℂ (q ≫ sX)) (hq : IsBirationalMorphism q)
    {BY : QDivisor Y} (hcrep : IsCrepantBoundary sX 2 K B q hY hq BY) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (q ≫ sX) 2) :
    QDivisor.IsRelativelySemiample (q ≫ sX) (Divisor.toQDivisor KY + BY) := by
  classical
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsDominant q := hq.isDominant
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (q ≫ sX)
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample sX _ hsemi
  have hLco : ∀ Γ, (L.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := fun Γ => by
    have := congrArg (fun Q : QDivisor X => Q.coeff Γ) hL
    simp [zsmul_eq_mul] at this
    rw [this]; ring
  have hdX : topologicalKrullDim X = (2 : ℕ) := hK.1
  have hdY : topologicalKrullDim Y = (2 : ℕ) := hKY.1
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdX
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := q ≫ sX) hdY
  obtain ⟨bX⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hdX
  obtain ⟨bY⟩ := MMP.Fourfold.exists_basis_topForms (sX := q ≫ sX) hdY
  obtain ⟨ωX, hωX0, hωX⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨ωY, hωY0, hωY⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hKY
  set c₀ := (ZTensorPower.basis bX 1).repr ωX () with hc₀_def
  set d₀ := (ZTensorPower.basis bY 1).repr ωY () with hd₀_def
  have hc₀ : c₀ ≠ 0 := repr_ne_zero_of_ne_zero bX hωX0
  have hd₀ : d₀ ≠ 0 := repr_ne_zero_of_ne_zero bY hωY0
  -- forms on `X` in degree `m` along the basis
  let F : X.functionField → RationalPluriForms sX 2 m := fun c =>
    c • (ZTensorPower.basis bX (m : ℤ)) ()
  have hFrepr : ∀ c, (ZTensorPower.basis bX (m : ℤ)).repr (F c) () = c := fun c => by
    simp [F]
  have hF0 : ∀ c, c ≠ 0 → F c ≠ 0 := fun c hc =>
    smul_ne_zero hc ((ZTensorPower.basis bX (m : ℤ)).ne_zero ())
  have hFmul : ∀ h c, F (h * c) = h • F c := fun h c => mul_smul h c _
  have hordF : ∀ (Γ : Mori.PrimeDivisor X) (c : X.functionField), c ≠ 0 →
      (Γ.ordForm (F c) : ℤ) = X.ord c Γ.genericPoint - m * X.ord c₀ Γ.genericPoint +
        m * K.coeff Γ := by
    intro Γ c hc
    obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul htrX bX
    have h1 := hN 1 ωX hωX0
    rw [hωX] at h1
    rw [hN m (F c) (hF0 c hc), hFrepr]
    rw [← hc₀_def] at h1
    linear_combination (-(m : ℤ)) * h1
  -- forms on `Y` along the basis
  have hordY : ∀ (E : Mori.PrimeDivisor Y) (ν : RationalPluriForms (q ≫ sX) 2 m), ν ≠ 0 →
      (E.ordForm ν : ℤ) = Y.ord ((ZTensorPower.basis bY (m : ℤ)).repr ν ()) E.genericPoint -
        m * Y.ord d₀ E.genericPoint + m * KY.coeff E := by
    intro E ν hν
    obtain ⟨N, hN⟩ := E.exists_ordForm_eq_ord_add_mul htrY bY
    have h1 := hN 1 ωY hωY0
    rw [hωY] at h1
    rw [hN m ν hν]
    rw [← hd₀_def] at h1
    linear_combination (-(m : ℤ)) * h1
  -- the crepancy computation along every prime divisor of `Y`
  let DE : Mori.PrimeDivisor Y → DivisorOver ℂ sX := fun E => ⟨Y, q, hY, hq, E⟩
  have key : ∀ E : Mori.PrimeDivisor Y, ∃ U : X.Opens, q E.genericPoint ∈ U ∧
      ∃ rφ : X.functionField, rφ ≠ 0 ∧
        (∀ Γ : Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
          L.coeff Γ = X.ord rφ Γ.genericPoint) ∧
        ((DE E).ordPullback (F (rφ⁻¹ * c₀ ^ m)) : ℚ) = -(m * BY.coeff E) := by
    intro E
    obtain ⟨U, hxU, φ, hφ⟩ := hLc (q E.genericPoint)
    obtain ⟨rφ, hrφ0, hrφ⟩ := MMP.Positivity.exists_ord_eq_of_units φ
    have hc : rφ⁻¹ * c₀ ^ m ≠ 0 := mul_ne_zero (inv_ne_zero hrφ0) (pow_ne_zero _ hc₀)
    have hLU : ∀ Γ : Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
        L.coeff Γ = X.ord rφ Γ.genericPoint := fun Γ hΓ => by rw [hφ Γ hΓ, hrφ]
    refine ⟨U, hxU, rφ, hrφ0, hLU, ?_⟩
    have hgen : GeneratesOn B m U (F (rφ⁻¹ * c₀ ^ m)) := by
      refine ⟨hF0 _ hc, fun Γ hΓ => ?_⟩
      have e1 := hordF Γ _ hc
      rw [Scheme.ord_mul (inv_ne_zero hrφ0) (pow_ne_zero _ hc₀), Scheme.ord_pow hc₀,
        scheme_ord_inv' hrφ0, ← hLU Γ hΓ] at e1
      have e2 := hLco Γ
      have e3 : ((Γ.ordForm (F (rφ⁻¹ * c₀ ^ m)) : ℤ) : ℚ) =
          -(L.coeff Γ : ℚ) + m * K.coeff Γ := by
        rw [e1]; push_cast; ring
      rw [e3, e2]
      ring
    have hdisc : IsDiscrepancy sX 2 K B (DE E)
        (((DE E).ordPullback (F (rφ⁻¹ * c₀ ^ m)) : ℚ) / m) := by
      refine ⟨hX, hK, m, hm, ⟨L, hL, hLc⟩, U, hxU, _, hgen, ?_⟩
      have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
    have e := IsDiscrepancy.eq hdisc (hcrep E)
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [div_eq_iff hm'] at e
    linarith
  -- the divisor `m(K_Y + B_Y)`
  have hBYint : ∀ E, ∃ z : ℤ, (z : ℚ) = m * BY.coeff E := fun E => by
    obtain ⟨U, -, rφ, -, -, h⟩ := key E
    exact ⟨-(DE E).ordPullback (F (rφ⁻¹ * c₀ ^ m)), by push_cast; linarith⟩
  set BYm : Divisor Y := DivisorWithCoeffs.roundDown ((m : ℤ) • BY) with hBYm_def
  have hBYm : ∀ E, (BYm.coeff E : ℚ) = m * BY.coeff E := fun E => by
    obtain ⟨z, hz⟩ := hBYint E
    rw [hBYm_def, DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul]
    push_cast
    rw [← hz, Int.floor_intCast]
  set DY : Divisor Y := (m : ℤ) • KY + BYm with hDY_def
  have hDYco : ∀ E, (DY.coeff E : ℚ) = m * (KY.coeff E + BY.coeff E) := fun E => by
    rw [hDY_def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    push_cast
    rw [hBYm]
    ring
  -- a section of `𝒪_Y(DY)` generating at every given point
  have hloc : ∀ y : Y, ∃ ψ : Y.functionField, ψ ≠ 0 ∧
      (∀ E : Mori.PrimeDivisor Y, 0 ≤ DY.coeff E + Y.ord ψ E.genericPoint) ∧
      ∀ E : Mori.PrimeDivisor Y, y ∈ E.support → DY.coeff E + Y.ord ψ E.genericPoint = 0 := by
    intro y
    obtain ⟨U₀, hU₀, ψ, hψ1, hψ2⟩ :=
      exists_coeff_add_ord_eq_zero_of_isRelativelyFree sX hLc hfree (q y)
    obtain ⟨r, hr0, hr⟩ := MMP.Positivity.exists_ord_eq_of_units ψ
    have hall : ∀ Γ : Mori.PrimeDivisor X, 0 ≤ L.coeff Γ + X.ord r Γ.genericPoint := by
      intro Γ
      rw [← hr]
      refine hψ1 Γ ⟨Γ.genericPoint, ?_, ?_⟩
      · rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      · show sX Γ.genericPoint ∈ U₀
        rwa [Subsingleton.elim (sX Γ.genericPoint) (sX (q y))]
    have hzero : ∀ Γ : Mori.PrimeDivisor X, q y ∈ Γ.support →
        L.coeff Γ + X.ord r Γ.genericPoint = 0 := fun Γ hΓ => by
      rw [← hr]; exact hψ2 Γ hΓ
    set σ := F (r * c₀ ^ m) with hσ_def
    have hσ0 : σ ≠ 0 := hF0 _ (mul_ne_zero hr0 (pow_ne_zero _ hc₀))
    have hpσ0 : pullbackRationalPluriForms sX q σ ≠ 0 :=
      pullbackRationalPluriForms_ne_zero sX q hq hdX hσ0
    set ψY := (ZTensorPower.basis bY (m : ℤ)).repr (pullbackRationalPluriForms sX q σ) () *
      (d₀ ^ m)⁻¹ with hψY_def
    have hrepY0 : (ZTensorPower.basis bY (m : ℤ)).repr (pullbackRationalPluriForms sX q σ) () ≠ 0 :=
      repr_ne_zero_of_ne_zero bY hpσ0
    have hψY0 : ψY ≠ 0 := mul_ne_zero hrepY0 (inv_ne_zero (pow_ne_zero _ hd₀))
    -- the computation along a prime divisor `E` of `Y`
    have hE : ∀ E : Mori.PrimeDivisor Y, ∃ u : X.presheaf.stalk (q E.genericPoint),
        DY.coeff E + Y.ord ψY E.genericPoint =
          Y.ord (algebraMap _ Y.functionField ((q.stalkMap E.genericPoint).hom u))
            E.genericPoint ∧ (q.stalkMap E.genericPoint).hom u ≠ 0 ∧
          (y ∈ E.support → IsUnit u) := by
      intro E
      obtain ⟨U, hxU, rφ, hrφ0, hLU, hpull⟩ := key E
      set h := r * rφ with hh_def
      have hh0 : h ≠ 0 := mul_ne_zero hr0 hrφ0
      have hτ0 : F (rφ⁻¹ * c₀ ^ m) ≠ 0 :=
        hF0 _ (mul_ne_zero (inv_ne_zero hrφ0) (pow_ne_zero _ hc₀))
      have hσeq : σ = h • F (rφ⁻¹ * c₀ ^ m) := by
        rw [← hFmul, hσ_def, hh_def]
        congr 1
        field_simp
      have hordh : ∀ Γ : Mori.PrimeDivisor X, q E.genericPoint ∈ Γ.support →
          X.ord h Γ.genericPoint = L.coeff Γ + X.ord r Γ.genericPoint := by
        intro Γ hΓ
        rw [Scheme.ord_mul hr0 hrφ0, ← hLU Γ ⟨_, hΓ, hxU⟩]
        ring
      obtain ⟨u, hu⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
        (q E.genericPoint) hh0 fun Γ hΓ => by rw [hordh Γ hΓ]; exact hall Γ
      have hu0 : u ≠ 0 := by rintro rfl; rw [map_zero] at hu; exact hh0 hu.symm
      have hfh : functionFieldMap q h =
          algebraMap _ Y.functionField ((q.stalkMap E.genericPoint).hom u) := by
        rw [← hu, functionFieldMap_algebraMap_stalk]
      refine ⟨u, ?_, fun h0 => hh0 ((map_eq_zero (functionFieldMap q)).mp
        (by rw [hfh, h0, map_zero])), fun hyE => ?_⟩
      · have e1 := ordPullback_smul hX hdX (DE E) hh0 hτ0
        have e2 : (DE E).ordPullback σ = E.ordForm (pullbackRationalPluriForms sX q σ) := rfl
        rw [← hσeq] at e1
        have e3 := hordY E _ hpσ0
        have e4 : Y.ord ψY E.genericPoint =
            Y.ord ((ZTensorPower.basis bY (m : ℤ)).repr (pullbackRationalPluriForms sX q σ) ())
              E.genericPoint - m * Y.ord d₀ E.genericPoint := by
          rw [hψY_def, Scheme.ord_mul hrepY0 (inv_ne_zero (pow_ne_zero _ hd₀)),
            scheme_ord_inv' (pow_ne_zero _ hd₀), Scheme.ord_pow hd₀]
          ring
        have e5 : (DE E).Y.ord (functionFieldMap (DE E).f h) (DE E).E.genericPoint =
            Y.ord (algebraMap _ Y.functionField ((q.stalkMap E.genericPoint).hom u))
              E.genericPoint := by
          show Y.ord (functionFieldMap q h) E.genericPoint = _
          rw [hfh]
        have e6 := hDYco E
        have e7 := hBYm E
        have : ((DY.coeff E + Y.ord ψY E.genericPoint : ℤ) : ℚ) =
            (Y.ord (algebraMap _ Y.functionField ((q.stalkMap E.genericPoint).hom u))
              E.genericPoint : ℚ) := by
          rw [Int.cast_add, e4, ← e5]
          have e1' : ((DE E).ordPullback σ : ℚ) =
              ((DE E).Y.ord (functionFieldMap (DE E).f h) (DE E).E.genericPoint : ℚ) +
                ((DE E).ordPullback (F (rφ⁻¹ * c₀ ^ m)) : ℚ) := by exact_mod_cast e1
          rw [e2, e3] at e1'
          push_cast at e1' ⊢
          rw [hpull] at e1'
          rw [e6]
          linarith
        exact_mod_cast this
      · -- `h` is a unit at `q(η_E)` when `y ∈ E`
        have hsp : q E.genericPoint ⤳ q y := by
          have : E.genericPoint ⤳ y := by
            rw [specializes_iff_mem_closure, ← PrimeDivisor.support_eq_closure]; exact hyE
          exact this.map q.continuous
        obtain ⟨u', hu', hu'h⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
          (q E.genericPoint) hh0 fun Γ hΓ => by
            rw [hordh Γ hΓ]
            refine hzero Γ ?_
            have hcl : IsClosed (Γ.support : Set X) := by
              rw [PrimeDivisor.support_eq_closure]; exact isClosed_closure
            exact hsp.mem_closed hcl hΓ
        have : u = u' := IsFractionRing.injective _ (X.functionField) (hu.trans hu'h.symm)
        rw [this]; exact hu'
    refine ⟨ψY, hψY0, fun E => ?_, fun E hyE => ?_⟩
    · obtain ⟨u, hu, hne, -⟩ := hE E
      rw [hu, scheme_ord_algebraMap E.coheight_genericPoint hne]
      positivity
    · obtain ⟨u, hu, -, hunit⟩ := hE E
      rw [hu]
      exact E.ord_algebraMap_of_isUnit ((hunit hyE).map _)
  choose ψY hψY0 hψY1 hψY2 using hloc
  have hunits : ∀ y, ∃ φ : (RationalFunctions Y)ˣ,
      ∀ E : Mori.PrimeDivisor Y, E.ord φ = Y.ord (ψY y) E.genericPoint := fun y =>
    MMP.Positivity.exists_units_of_ne_zero (hψY0 y)
  choose φY hφY using hunits
  -- `DY` is relatively free
  have hfreeY : IsRelativelyFreeDivisor (q ≫ sX) DY :=
    isRelativelyFreeDivisor_of_forall_exists (q ≫ sX) fun y =>
      ⟨⊤, trivial, φY y, fun E _ => by rw [hφY]; exact hψY1 y E,
        fun E hyE => by rw [hφY]; exact hψY2 y E hyE⟩
  -- `DY` is Cartier
  have hCartY : DY.IsCartier := by
    intro y
    set Ey : Divisor Y := DY + principalDivisor (φY y) with hEy
    have hEyco : ∀ E, Ey.coeff E = DY.coeff E + Y.ord (ψY y) E.genericPoint := fun E => by
      rw [hEy, DivisorWithCoeffs.coeff_add, coeff_principalDivisor, hφY]
    let W : Set Y := (⋃ E ∈ Ey.support, (E.support : Set Y))ᶜ
    have hWo : IsOpen W := by
      refine (Set.Finite.isClosed_biUnion Ey.support.finite_toSet fun E _ => ?_).isOpen_compl
      rw [PrimeDivisor.support_eq_closure]; exact isClosed_closure
    refine ⟨⟨W, hWo⟩, ?_, (φY y)⁻¹, fun E hE => ?_⟩
    · intro hy
      obtain ⟨E, hE, hyE⟩ := Set.mem_iUnion₂.mp hy
      have h0 := hEyco E
      rw [hψY2 y E hyE] at h0
      exact (Finsupp.mem_support_iff.mp hE) h0
    · have hE0 : Ey.coeff E = 0 := by
        by_contra hne
        obtain ⟨z, hzE, hzW⟩ := hE
        exact hzW (Set.mem_biUnion (Finsupp.mem_support_iff.mpr hne) hzE)
      rw [hEyco, ← hφY] at hE0
      rw [Mori.PrimeDivisor.ord_inv]
      omega
  refine isRelativelySemiample_of_isRelativelyFreeDivisor (q ≫ sX) _
    ⟨m, hm, DY, ?_, hCartY, hfreeY⟩
  ext E
  rw [Divisor.coeff_toQDivisor, hDYco]
  simp [zsmul_eq_mul]
  ring

/-! ### Global generation of the twisted adjoint -/

/-- **Step 3.** If every normalized adjoint of a projective sdlt surface pair is globally
semiample, the adjoint is globally generated in every sufficiently divisible degree: crepant
`ℚ`-factorial dlt models, surface preadmissible generation and preadmissible conductor
descent. -/
private theorem exists_isGloballyGeneratedAdjoint
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
    (hsemi : ∀ (i : N.ι) (K : Divisor (N.X i)), K.IsCanonicalDivisor (N.n i ≫ sT) 2 →
      QDivisor.IsRelativelySemiample (N.n i ≫ sT) (Divisor.toQDivisor K + Θ i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → IsGloballyGeneratedAdjoint N Θ m := by
  classical
  haveI := finite_ι h
  haveI : ∀ i, CompactSpace (N.X i) := fun i =>
    compactSpace_of_isProjectiveMorphism (isProjectiveVariety_normalization h i).isProjective
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hKX : ∀ i, ∃ K : Divisor (N.X i), K.IsCanonicalDivisor (N.n i ≫ sT) 2 := fun i => by
    obtain ⟨K, hK⟩ := h.exists_isDltPair i
    exact ⟨K, hK.1.2.1⟩
  choose KX hKX using hKX
  have hmodel := fun i => MMP.Threefold.exists_crepant_dltModification_of_surface (N.n i ≫ sT)
    (isProjectiveVariety_normalization h i) (topologicalKrullDim_normalization h i)
    (isLogCanonicalPair_normalization h i)
  choose Y hYi hYn hYN q hq hYQ BY hqp hYp hYdlt hcrep _hexc using hmodel
  have hdimY : ∀ i, topologicalKrullDim (Y i) = 2 := fun i => by
    haveI : MMP.Mori.IsVariety ℂ (N.n i ≫ sT) := (N.isNormalVariety i).1
    haveI : MMP.Mori.IsVariety ℂ (q i ≫ N.n i ≫ sT) := (hYQ i).1.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N.n i ≫ sT)
      (q i ≫ N.n i ≫ sT) (hq i)]
    exact topologicalKrullDim_normalization h i
  haveI : ∀ i, CompactSpace (Y i) := fun i =>
    compactSpace_of_isProjectiveMorphism (hYp i).isProjective
  haveI : ∀ i, IsDominant (q i) := fun i => (hq i).isDominant
  have hBpair : ∀ i, Fourfold.IsPair (q i ≫ N.n i ≫ sT) (BY i) := fun i =>
    ⟨inferInstance, inferInstance, (hYdlt i).1.1, (hYdlt i).1.2.1⟩
  have hKY : ∀ i, ∃ K : Divisor (Y i), K.IsCanonicalDivisor (q i ≫ N.n i ≫ sT) 2 := fun i => by
    obtain ⟨-, n, K, hK, -⟩ := (hYdlt i).1.1
    have hn : (n : WithBot ℕ∞) = 2 := hK.1.symm.trans (hdimY i)
    have hn' : n = 2 := by exact_mod_cast hn
    exact ⟨K, hn' ▸ hK⟩
  choose KY hKY using hKY
  have hsemiY : ∀ i, QDivisor.IsRelativelySemiample (q i ≫ N.n i ≫ sT)
      (Divisor.toQDivisor (KY i) + BY i) := fun i =>
    isRelativelySemiample_of_isCrepantBoundary (N.isNormalVariety i) (hKX i)
      (hsemi i (KX i) (hKX i)) (q i) (hYQ i).1 (hq i) (hcrep i (KX i) (hKX i)) (hKY i)
  obtain ⟨mg, hmg, hgen⟩ := exists_generatesOn_of_mem_preadmissibleSections hYp hdimY hYQ
    hBpair hYdlt hKY hsemiY
  obtain ⟨md, hmd, hdesc⟩ := h.exists_existsUnique_pullback_eq_of_mem_preadmissibleSections q
    hqp hYQ (fun i => ⟨KX i, (hYQ i).1, hq i, hcrep i (KX i) (hKX i)⟩)
  refine ⟨2 * (mg * md), by positivity, fun m hm0 hm x => ?_⟩
  have hev : Even m := (even_two_mul _).two_dvd.trans hm |> even_iff_two_dvd.mpr
  have hdvd : ∀ a, a ∣ mg * md → a ∣ m := fun a ha =>
    ha.trans ((dvd_mul_left _ _).trans hm)
  obtain ⟨⟨R⟩, hgenR⟩ := hgen m hm0 (hdvd _ (dvd_mul_right _ _)) hev
  obtain ⟨hdesc1, hdesc2⟩ := hdesc m (hdvd _ (dvd_mul_left _ _)) hev R
  obtain ⟨s, hs, t, U, hxU, g, a, ha, hga, hta, hpt⟩ := hdesc2 (fun i y => hgenR R i y) x
  obtain ⟨t₁, ⟨ht₁, hpt₁⟩, -⟩ := hdesc1 s hs
  have htt : t = t₁ := funext fun i =>
    pullbackRationalPluriForms_injective (N.n i ≫ sT) (q i) (hq i)
      (topologicalKrullDim_normalization h i) m ((hpt i).trans (hpt₁ i).symm)
  refine ⟨t, fun y => ?_⟩
  by_cases hyx : y = x
  · subst hyx
    exact ⟨U, hxU, g, a, hga.1, fun _ => ha, hta⟩
  · obtain ⟨U', hyU', g', a', hga', hta'⟩ := ht₁ y
    exact ⟨U', hyU', g', a', hga'.1, fun h => absurd h hyx, htt ▸ hta'⟩

/-- Multiplying a form by the `k`-th power of the pull-back `ν^*u` of a function `u` on `T`
multiplies its residue presentation along a conductor component by `ū^k`. -/
private theorem isLogResiduePresentation_pow_smul {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n m : ℕ} {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V V' : T.Opens} (hV : V' ≤ V)
    {hP : (N.n i).base P.genericPoint ∈ V} (hP' : (N.n i).base P.genericPoint ∈ V')
    {av : Fin (n - 1) → Γ(T, V)} {g : Γ(T, V)} {ε : ℤ} {s : RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsLogResiduePresentation N n m i P V hP av g ε s) (u : Γ(T, V'))
    {φ : (N.X i).functionField}
    (hφ : algebraMap _ (N.X i).functionField ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V')
      P.genericPoint hP' ((N.n i).app V' u)) = φ) (e : ℕ) :
    IsLogResiduePresentation N n m i P V' hP'
      (fun j => T.presheaf.map (homOfLE hV).op (av j))
      (T.presheaf.map (homOfLE hV).op g * u ^ e) ε (φ ^ e • s) := by
  unfold IsLogResiduePresentation at hs ⊢
  obtain ⟨z, h0, hz, hseq, hda, hres⟩ := hs
  have R1 : ∀ t : Γ(T, V), (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP'
      ((N.n i).app V' (T.presheaf.map (homOfLE hV).op t)) =
      (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V t) := by
    intro t
    rw [← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply,
      TopCat.Presheaf.germ_res_apply]
  set w := (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' u)
    with hw_def
  dsimp only
  refine ⟨z, h0 * w ^ e, hz, ?_, ?_, ?_⟩
  · rw [hseq]
    simp only [R1, map_mul, map_pow, hφ]
    rw [mul_comm]
    exact smul_smul _ _ _
  · simp only [R1]
    exact hda
  · simp only [map_mul, map_pow, R1]
    rw [← hw_def, hres]
    ring

/-- The germ at the generic point of a restricted pull-back is that of the pull-back. -/
private theorem germToFunctionField_app_map {X Y : Scheme.{0}} [IsIntegral X] (ν : X ⟶ Y)
    {U U' : Y.Opens} (h : U' ≤ U) (a : Γ(Y, U)) [Nonempty (ν ⁻¹ᵁ U')] [Nonempty (ν ⁻¹ᵁ U)] :
    (X.germToFunctionField (ν ⁻¹ᵁ U')).hom (ν.app U' (Y.presheaf.map (homOfLE h).op a)) =
      (X.germToFunctionField (ν ⁻¹ᵁ U)).hom (ν.app U a) := by
  have hg : ν (genericPoint X) ∈ U' := by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (ν ⁻¹ᵁ U')›
    exact ((genericPoint_spec X).mem_open_set_iff (ν ⁻¹ᵁ U').isOpen).mpr ⟨z, trivial, hz⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (U := ν ⁻¹ᵁ U') hg,
    ← Scheme.algebraMap_germ_eq_germToFunctionField X (U := ν ⁻¹ᵁ U) (h hg)]
  congr 1
  rw [← Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply,
    Scheme.Hom.germ_stalkMap_apply]

open MMP.Intersection in
/-- **Step 4: removing the base twist.** If `Θ'ᵢ = Θᵢ + c (f ∘ νᵢ)^*H` for an effective Cartier
divisor `H` on `Z`, `cm` is an integer and the twisted adjoint is globally generated in degree
`m`, then the adjoint is relatively generated over `Z` in degree `m`: over an open `W ⊆ Z` on
which `H` has the regular local equation `h`, the sections `(f ∘ νᵢ)^*h^{cm} · tᵢ` are relative
generators. -/
private theorem untwist
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
    {Z : Scheme.{0}} (f : T ⟶ Z) {H : Z.CartierDivisor} (hH : IsEffective H)
    {HN : ∀ i, (N.X i).CartierDivisor} (hHN : ∀ i, IsPullback (N.n i ≫ f) H (HN i))
    {c : ℚ} (hc : 0 < c) {Θ' : ∀ i, QDivisor (N.X i)}
    (hΘ' : ∀ i P, (Θ' i).coeff P = (Θ i).coeff P + c * primeDivisorOrder P (HN i))
    {m : ℕ} (hcm : ((m : ℚ) * c).den = 1)
    (hgen : IsGloballyGeneratedAdjoint N Θ' m) :
    ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N 2 m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i := by
  classical
  -- the exponent `e = cm`
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℚ) = m * c := by
    refine ⟨((m : ℚ) * c).num.toNat, ?_⟩
    have h0 : 0 ≤ ((m : ℚ) * c).num := Rat.num_nonneg.mpr (by positivity)
    rw [← Rat.coe_int_num_of_den_eq_one hcm]
    exact_mod_cast Int.toNat_of_nonneg h0
  have hdim : ∀ i, topologicalKrullDim (N.X i) = 2 := fun i => by
    obtain ⟨K, hK⟩ := h.exists_isDltPair i
    exact hK.1.2.1.1
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  intro x
  obtain ⟨W, hfxW, hW, hu, hloc⟩ := hH (f x)
  obtain ⟨t', ht'⟩ := hgen x
  let φ : ∀ i, (N.X i).functionField := fun i =>
    if hW' : Nonempty ((N.n i ≫ f) ⁻¹ᵁ W) then
      haveI := hW'
      (N.X i).germToFunctionField ((N.n i ≫ f) ⁻¹ᵁ W) ((N.n i ≫ f).app W hW)
    else 1
  have hφ : ∀ i (y : N.X i) (hy : (N.n i ≫ f) y ∈ W), φ i =
      algebraMap _ _ ((N.X i).presheaf.germ _ y hy ((N.n i ≫ f).app W hW)) := by
    intro i y hy
    have hW' : Nonempty ((N.n i ≫ f) ⁻¹ᵁ W) := ⟨⟨y, hy⟩⟩
    simp only [φ, dif_pos hW']
    exact (Scheme.algebraMap_germ_eq_germToFunctionField (N.X i)
      (U := (N.n i ≫ f) ⁻¹ᵁ W) hy _).symm
  have hφ0 : ∀ i, φ i ≠ 0 := by
    intro i
    by_cases hW' : Nonempty ((N.n i ≫ f) ⁻¹ᵁ W)
    · obtain ⟨⟨y, hy⟩⟩ := hW'
      rw [hφ i y hy]
      have := germ_ne_zero_of_isPullback (N.n i ≫ f) (hHN i) hu hloc hy
      rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
    · simp only [φ]
      rw [dif_neg hW']
      exact one_ne_zero
  refine ⟨W, hfxW, fun i => φ i ^ e • t' i, fun y hy => ?_⟩
  obtain ⟨U, hyU, g', a, hg', hax, hta⟩ := ht' y
  let U' : T.Opens := U ⊓ f ⁻¹ᵁ W
  have hU'U : U' ≤ U := inf_le_left
  refine ⟨U', ⟨hyU, hy⟩, inf_le_right, fun i => φ i ^ e • g' i,
    T.presheaf.map (homOfLE hU'U).op a, ⟨fun i => ⟨?_, fun Γ hΓ => ?_⟩, ?_⟩, ?_, ?_⟩
  · exact smul_ne_zero (pow_ne_zero _ (hφ0 i)) (hg'.1 i).1
  · have hηΓ : Γ.genericPoint ∈ (N.n i) ⁻¹ᵁ U' := by
      have h1 := hΓ
      rw [PrimeDivisor.support_eq_closure,
        closure_inter_open_nonempty_iff (TopologicalSpace.Opens.isOpen _)] at h1
      obtain ⟨z, hz, hzU⟩ := h1
      rwa [Set.mem_singleton_iff.mp hz] at hzU
    have hηmem : Γ.genericPoint ∈ Γ.support := by
      rw [PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have e1 := (hg'.1 i).2 Γ ⟨Γ.genericPoint, hηmem, hηΓ.1⟩
    have hyW : (N.n i ≫ f) Γ.genericPoint ∈ W := hηΓ.2
    have hord : (N.X i).ord (φ i) Γ.genericPoint = primeDivisorOrder Γ (HN i) := by
      rw [hφ i _ hyW]
      exact (primeDivisorOrder_eq_ord_of_isPullback (N.n i ≫ f) (hHN i) hu hloc Γ hyW
        (germ_ne_zero_of_isPullback (N.n i ≫ f) (hHN i) hu hloc hyW)).symm
    rw [Γ.ordForm_smul_of_topologicalKrullDim_eq (hdim i) (pow_ne_zero _ (hφ0 i)) (hg'.1 i).1,
      Scheme.ord_pow (hφ0 i), hord]
    rw [hΘ'] at e1
    push_cast
    linear_combination e1 + (primeDivisorOrder Γ (HN i) : ℚ) * he
  · intro i j P P' heq hQU hQD hne
    obtain ⟨V, hP, hP', av, gg, h1, h2⟩ := hg'.2 i j P P' heq (hU'U hQU) hQD hne
    let V' : T.Opens := V ⊓ f ⁻¹ᵁ W
    have hV' : V' ≤ V := inf_le_left
    have hV'W : V' ≤ f ⁻¹ᵁ W := inf_le_right
    have hQV' : (N.n i).base P.genericPoint ∈ V' := ⟨hP, hQU.2⟩
    have hQ'V' : (N.n j).base P'.genericPoint ∈ V' := heq ▸ hQV'
    let u : Γ(T, V') := T.presheaf.map (homOfLE hV'W).op (f.app W hW)
    have hφu : ∀ (l : N.ι) (R : MMP.Mori.PrimeDivisor (N.X l))
        (hR : (N.n l).base R.genericPoint ∈ V'),
        algebraMap _ (N.X l).functionField ((N.X l).presheaf.germ ((N.n l) ⁻¹ᵁ V')
          R.genericPoint hR ((N.n l).app V' u)) = φ l := by
      intro l R hR
      rw [hφ l R.genericPoint (hV'W hR)]
      congr 1
      rw [← Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply,
        Scheme.Hom.germ_stalkMap_apply]
      rfl
    exact ⟨V', hQV', hQ'V', fun l => T.presheaf.map (homOfLE hV').op (av l),
      T.presheaf.map (homOfLE hV').op gg * u ^ e,
      isLogResiduePresentation_pow_smul N hV' hQV' h1 u (hφu i P hQV') e,
      isLogResiduePresentation_pow_smul N hV' hQ'V' h2 u (hφu j P' hQ'V') e⟩
  · rintro rfl
    exact (hax rfl).map _
  · intro i hi
    have hi' : Nonempty (N.n i ⁻¹ᵁ U) := by
      obtain ⟨⟨z, hz⟩⟩ := hi
      exact ⟨⟨z, hU'U hz⟩⟩
    show φ i ^ e • t' i = _
    rw [hta i hi', smul_comm, germToFunctionField_app_map (N.n i) hU'U a]

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
  haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hzU⟩⟩
  have hz : z ∈ (N.X i).basicOpen ((N.n i).app U b) := by
    rw [← Scheme.preimage_basicOpen]
    exact hx
  have h0 : (N.n i).app U b = 0 :=
    (N.X i).germToFunctionField_injective (N.n i ⁻¹ᵁ U) ((h i inferInstance).trans (map_zero _).symm)
  rw [h0, Scheme.basicOpen_zero] at hz
  exact hz

section SdltUniqueness

open MMP.Flips

/-! ### Descent of functions along the normalization of a seminormal scheme -/

/-- In a reduced ring, `a² = c²` and `a³ = c³` force `a = c`: `(a - c)³ = 0`. -/
private theorem eq_of_sq_eq_of_cube_eq {R : Type*} [CommRing R] [IsReduced R] {a c : R}
    (h2 : a ^ 2 = c ^ 2) (h3 : a ^ 3 = c ^ 3) : a = c := by
  have h : (a - c) ^ 3 = 0 := by
    have e1 : a ^ 2 * c = c ^ 3 := by rw [h2]; ring
    have e2 : a * c ^ 2 = a ^ 3 := by rw [← h2]; ring
    linear_combination 4 * h3 - 3 * e1 + 3 * e2
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨3, h⟩)

/-- **Seminormal descent along a finite family of quotients.** Let `A` be a ring in which
`x³ = y²` forces `x = a², y = a³` for some `a` (seminormality), and `p_k : A → B_k` finitely many
surjections onto domains, jointly injective. Suppose that for every `k` some `c_k ∈ A` vanishes in
every `B_l`, `l ≠ k`, with `M_k ⊆ √(p_k(c_k))` for an ideal `M_k` of `B_k`. Then an element
`(f_k)` of `∏ B_k` congruent to the image of a single `r ∈ A` modulo every `M_k` comes from `A`.
The conductor `𝔠 = {b | b ∏ B_k ⊆ A}` contains the `p(c_k)` and is radical by seminormality
(`b² ∈ 𝔠` gives `(bx)², (bx)³ ∈ A`, so `bx ∈ A`), so it contains `f - p(r)`. -/
private theorem exists_eq_of_forall_sub_mem {A : Type*} [CommRing A]
    (hA : ∀ x y : A, x ^ 3 = y ^ 2 → ∃ a : A, x = a ^ 2 ∧ y = a ^ 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*} [∀ k, CommRing (B k)]
    [∀ k, IsDomain (B k)]
    (p : ∀ k, A →+* B k) (hinj : Function.Injective (Pi.ringHom p))
    (hsurj : ∀ k, Function.Surjective (p k)) (M : ∀ k, Ideal (B k))
    (hc : ∀ k, ∃ c : A, (∀ l, l ≠ k → p l c = 0) ∧ M k ≤ (Ideal.span {p k c}).radical)
    (f : ∀ k, B k) (r : A) (hf : ∀ k, f k - p k r ∈ M k) :
    ∃ a : A, ∀ k, p k a = f k := by
  classical
  set φ := Pi.ringHom p with hφ
  have hφa : ∀ a l, φ a l = p l a := fun _ _ => rfl
  let C : Set (∀ k, B k) := {b | ∀ x, ∃ a, φ a = b * x}
  have hCmul : ∀ b ∈ C, ∀ y, b * y ∈ C := fun b hb y x => by
    obtain ⟨a, ha⟩ := hb (y * x); exact ⟨a, by rw [ha, mul_assoc]⟩
  have hCadd : ∀ b ∈ C, ∀ b' ∈ C, b + b' ∈ C := fun b hb b' hb' x => by
    obtain ⟨a, ha⟩ := hb x; obtain ⟨a', ha'⟩ := hb' x
    exact ⟨a + a', by rw [map_add, ha, ha', add_mul]⟩
  have hCsum : ∀ (s : Finset ι) (b : ι → ∀ k, B k), (∀ k ∈ s, b k ∈ C) → ∑ k ∈ s, b k ∈ C := by
    intro s b hb
    induction s using Finset.induction_on with
    | empty => intro x; exact ⟨0, by simp⟩
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact hCadd _ (hb k (Finset.mem_insert_self _ _)) _
        (ih fun l hl => hb l (Finset.mem_insert_of_mem hl))
  choose c hc0 hcM using hc
  have hφc : ∀ k, φ (c k) ∈ C := fun k x => by
    obtain ⟨a', ha'⟩ := hsurj k (x k)
    refine ⟨c k * a', funext fun l => ?_⟩
    rw [map_mul, Pi.mul_apply, Pi.mul_apply]
    simp only [hφa]
    by_cases hl : l = k
    · subst hl; rw [ha']
    · rw [hc0 k l hl, zero_mul, zero_mul]
  set b : ∀ k, B k := f - φ r with hb
  have hbM : ∀ k, ∃ N : ℕ, ∃ y, b k ^ N = p k (c k) * y := fun k => by
    obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp (hcM k (by
      simpa [hb, hφa] using hf k))
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hN
    exact ⟨N, y, by rw [mul_comm]; exact hy.symm⟩
  choose N y hy using hbM
  set N' := ∑ k, N k with hN'
  have hNk : ∀ k, N k ≤ N' := fun k =>
    Finset.single_le_sum (fun l _ => Nat.zero_le (N l)) (Finset.mem_univ k)
  have hbN : b ^ N' ∈ C := by
    have hdec : b ^ N' = ∑ k, φ (c k) * Pi.single k (b k ^ (N' - N k) * y k) := by
      funext l
      simp only [Pi.pow_apply, Finset.sum_apply, Pi.mul_apply]
      rw [Finset.sum_eq_single l]
      · rw [Pi.single_eq_same, hφa, ← mul_assoc, mul_comm (p l (c l)), mul_assoc, ← hy l,
          ← pow_add, Nat.sub_add_cancel (hNk l)]
      · intro k _ hk; rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero]
      · intro h; exact absurd (Finset.mem_univ l) h
    rw [hdec]
    exact hCsum _ _ fun k _ => hCmul _ (hφc k) _
  have hsq : ∀ b, b ^ 2 ∈ C → b ∈ C := fun b hb x => by
    obtain ⟨a₂, ha₂⟩ := hb (x ^ 2)
    obtain ⟨a₃, ha₃⟩ := hb (b * x ^ 3)
    have h23 : a₂ ^ 3 = a₃ ^ 2 := hinj (by
      rw [map_pow, map_pow, ha₂, ha₃]; ring)
    obtain ⟨a, h2, h3⟩ := hA a₂ a₃ h23
    refine ⟨a, eq_of_sq_eq_of_cube_eq ?_ ?_⟩
    · rw [← map_pow, ← h2, ha₂]; ring
    · rw [← map_pow, ← h3, ha₃]; ring
  have hpow : ∀ j : ℕ, ∀ b, b ^ (2 ^ j) ∈ C → b ∈ C := by
    intro j
    induction j with
    | zero => intro b hb; simpa using hb
    | succ j ih =>
      intro b hb
      refine ih b (hsq _ ?_)
      rwa [← pow_mul, ← pow_succ]
  have hbC : b ∈ C := by
    refine hpow N' _ ?_
    have hle : N' ≤ 2 ^ N' := (Nat.lt_two_pow_self).le
    rw [← Nat.sub_add_cancel hle, pow_add, mul_comm]
    exact hCmul _ hbN _
  obtain ⟨a', ha'⟩ := hbC 1
  refine ⟨r + a', fun k => ?_⟩
  have := congrFun ha' k
  rw [hφa, mul_one, hb, Pi.sub_apply, hφa] at this
  rw [map_add, this]
  ring

/-- Localizations of seminormal rings satisfy the existence half of seminormality: if
`x³ = y²` in `M⁻¹R`, write `x = X/u²`, `y = Y/u³` and clear the remaining denominator. -/
private theorem exists_sq_cube_of_isLocalization {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hR : IsSeminormalRing R) {x y : S}
    (h : x ^ 3 = y ^ 2) : ∃ a : S, x = a ^ 2 ∧ y = a ^ 3 := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M x
  obtain ⟨⟨b, t⟩, hb⟩ := IsLocalization.surj M y
  simp only at ha hb
  set X : R := a * s * t ^ 2 with hX
  set Y : R := b * s ^ 3 * t ^ 2 with hY
  have hxu : x * (algebraMap R S s * algebraMap R S t) ^ 2 = algebraMap R S X := by
    simp only [hX, map_mul, map_pow]
    linear_combination (algebraMap R S s * algebraMap R S t ^ 2) * ha
  have hyu : y * (algebraMap R S s * algebraMap R S t) ^ 3 = algebraMap R S Y := by
    simp only [hY, map_mul, map_pow]
    linear_combination (algebraMap R S s ^ 3 * algebraMap R S t ^ 2) * hb
  have hXY : algebraMap R S (X ^ 3) = algebraMap R S (Y ^ 2) := by
    rw [map_pow, map_pow, ← hxu, ← hyu]
    linear_combination (algebraMap R S s * algebraMap R S t) ^ 6 * h
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M S).mp hXY
  have hcube : ((w : R) ^ 2 * X) ^ 3 = ((w : R) ^ 3 * Y) ^ 2 := by
    calc ((w : R) ^ 2 * X) ^ 3 = (w : R) ^ 5 * ((w : R) * X ^ 3) := by ring
      _ = (w : R) ^ 5 * ((w : R) * Y ^ 2) := by rw [hw]
      _ = ((w : R) ^ 3 * Y) ^ 2 := by ring
  obtain ⟨c, ⟨hc2, hc3⟩, -⟩ := hR _ _ hcube
  obtain ⟨v, hv⟩ := IsLocalization.map_units S (w * (s * t))
  have hv' : (v : S) = algebraMap R S w * (algebraMap R S s * algebraMap R S t) := by
    rw [hv]; simp only [Submonoid.coe_mul, map_mul]
  refine ⟨algebraMap R S c * (↑v⁻¹ : S), ?_, ?_⟩
  · have e : algebraMap R S c ^ 2 = x * (↑v : S) ^ 2 := by
      rw [← map_pow, ← hc2, map_mul, ← hxu, hv', map_pow]; ring
    calc x = x * ((↑v : S) * ↑v⁻¹) ^ 2 := by rw [Units.mul_inv, one_pow, mul_one]
      _ = (algebraMap R S c * (↑v⁻¹ : S)) ^ 2 := by rw [mul_pow (algebraMap R S c), e]; ring
  · have e : algebraMap R S c ^ 3 = y * (↑v : S) ^ 3 := by
      rw [← map_pow, ← hc3, map_mul, ← hyu, hv', map_pow]; ring
    calc y = y * ((↑v : S) * ↑v⁻¹) ^ 3 := by rw [Units.mul_inv, one_pow, mul_one]
      _ = (algebraMap R S c * (↑v⁻¹ : S)) ^ 3 := by rw [mul_pow (algebraMap R S c), e]; ring

/-- The local rings of a seminormal scheme satisfy the existence half of seminormality. -/
private theorem stalk_exists_sq_cube {X : Scheme.{0}} (hX : IsSeminormal X) (x : X)
    {a b : X.presheaf.stalk x} (h : a ^ 3 = b ^ 2) : ∃ c, a = c ^ 2 ∧ b = c ^ 3 := by
  obtain ⟨V, hxV, hV⟩ := hX x
  have hVa : IsAffineOpen (V : X.Opens) := V.2
  letI := (X.presheaf.germ (V : X.Opens) x hxV).hom.toAlgebra
  haveI := hVa.isLocalization_stalk ⟨x, hxV⟩
  exact exists_sq_cube_of_isLocalization (hVa.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl hV h

/-- Evaluating equal residues `ḡ₁ (dx̄₁)^{⊗m} = ḡ₂ (dx̄₂)^{⊗m}` of logarithmic pluriforms in
dimension two against a derivation `D` of the residue field. -/
private theorem logPluriResidue_eval {k : Type*} [Field k] {O : Type*} [CommRing O]
    {L : Type*} [Field L] [Algebra k L] [Algebra O L] {m : ℕ} {g₁ g₂ : O} {x₁ x₂ : Fin 1 → O}
    (h : MMP.Fourfold.logPluriResidue (O := O) k L m 1 g₁ x₁ =
      MMP.Fourfold.logPluriResidue (O := O) k L m 1 g₂ x₂) (D : Derivation k L L) :
    algebraMap O L g₁ * D (algebraMap O L (x₁ 0)) ^ m =
      algebraMap O L g₂ * D (algebraMap O L (x₂ 0)) ^ m := by
  set φ : Module.Dual L Ω[L⁄k] := D.liftKaehlerDifferential
  have := congrArg (PiTensorProduct.dualDistrib
    (PiTensorProduct.tprod L fun _ : Fin m =>
      exteriorPower.pairingDual L Ω[L⁄k] 1 (exteriorPower.ιMulti L 1 fun _ => φ))) h
  simp only [MMP.Fourfold.logPluriResidue, map_smul, PiTensorProduct.dualDistrib_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti, smul_eq_mul, Matrix.det_unique, Matrix.of_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  simpa [φ, Derivation.liftKaehlerDifferential_comp_D] using this

/-- The logarithmic pluriform `g (t⁻¹ dt ∧ dx)^{⊗m}` of `MMP.Fourfold.logPluriForm`, written with
the case split of `MMP.Fourfold.IsLogResiduePresentation`. -/
private theorem logPluriForm_eq_dite {k K O : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing O] [Algebra O K] (m : ℕ) (h : O) (t : O) (x : Fin 1 → O) :
    MMP.Fourfold.logPluriForm (O := O) k K m 1 h t x =
      algebraMap O K h • PiTensorProduct.tprod K (fun _ : Fin m =>
        exteriorPower.ιMulti K 2 (fun j : Fin 2 => if hj : j.val = 0 then
          (algebraMap O K t)⁻¹ • KaehlerDifferential.D k K (algebraMap O K t) else
          KaehlerDifferential.D k K (algebraMap O K (x ⟨j.val - 1, by omega⟩)))) := by
  unfold MMP.Fourfold.logPluriForm
  congr 2
  funext c
  have hv : (fun j : Fin 2 => if hj : j.val = 0 then
          (algebraMap O K t)⁻¹ • KaehlerDifferential.D k K (algebraMap O K t) else
          KaehlerDifferential.D k K (algebraMap O K (x ⟨j.val - 1, by omega⟩))) =
      Function.update (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t))
        (fun i => KaehlerDifferential.D k K (algebraMap O K (x i))) : Fin 2 → Ω[K⁄k]) 0
        ((algebraMap O K t)⁻¹ • KaehlerDifferential.D k K (algebraMap O K t)) := by
    funext j
    fin_cases j
    · simp
    · simp [Function.update, Fin.cons]
      rfl
  rw [hv, AlternatingMap.map_update_smul]
  erw [Function.update_eq_self]

/-- **Comparing two residue presentations on one branch.** If `s = u s'` on the normalization
component `Tᵢ`, with residue presentations `ε ḡ (dā)^{⊗m}` of `s` and `ε' ḡ' (dā')^{⊗m}` of `s'`
along the prime divisor `P` of `Tᵢ`, then for every derivation `D` of `κ(P)`,
`ε ḡ D(ā)^m = ū ε' ḡ' D(ā')^m`. -/
private theorem isLogResiduePresentation_eval {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : MMP.Flips.NormalizationComponents sT hT} {m : ℕ} {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V V' : T.Opens} {hP : (N.n i).base P.genericPoint ∈ V}
    {hP' : (N.n i).base P.genericPoint ∈ V'} {a : Fin (2 - 1) → Γ(T, V)}
    {a' : Fin (2 - 1) → Γ(T, V')} {g : Γ(T, V)} {g' : Γ(T, V')} {ε ε' : ℤ}
    {s s' : RationalPluriForms (N.n i ≫ sT) 2 m}
    (h : IsLogResiduePresentation N 2 m i P V hP a g ε s)
    (h' : IsLogResiduePresentation N 2 m i P V' hP' a' g' ε' s')
    (u : (N.X i).presheaf.stalk P.genericPoint)
    (hu : s = algebraMap _ (N.X i).functionField u • s') :
    letI : Algebra ℂ ((N.X i).residueField P.genericPoint) :=
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (N.n i ≫ sT).appTop ≫
        (N.X i).Γevaluation P.genericPoint).hom.toAlgebra
    ∀ D : Derivation ℂ ((N.X i).residueField P.genericPoint)
        ((N.X i).residueField P.genericPoint),
      ((ε : (N.X i).residueField P.genericPoint) * (N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V g))) *
        D ((N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V (a 0)))) ^ m =
      (N.X i).residue P.genericPoint u *
        ((ε' : (N.X i).residueField P.genericPoint) * (N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' g'))) *
        D ((N.X i).residue P.genericPoint
          ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP'
            ((N.n i).app V' (a' 0)))) ^ m := by
  letI : Algebra ℂ ((N.X i).residueField P.genericPoint) :=
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (N.n i ≫ sT).appTop ≫
        (N.X i).Γevaluation P.genericPoint).hom.toAlgebra
  intro D
  obtain ⟨z₁, h₁, hz₁, hs₁, -, hr₁⟩ := h
  obtain ⟨z₂, h₂, hz₂, hs₂, -, hr₂⟩ := h'
  beta_reduce at hs₁ hs₂ hr₁ hr₂
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  haveI := P.integral
  have hjP : P.idealSheaf.subschemeι (genericPoint P.idealSheaf.subscheme) = P.genericPoint := rfl
  letI := stalkAlgebra (N.n i ≫ sT) P.genericPoint
  letI := functionFieldAlgebra (N.n i ≫ sT)
  haveI := isScalarTower_stalk_functionField (N.n i ≫ sT) P.genericPoint
  letI : Algebra ((N.X i).presheaf.stalk P.genericPoint) ((N.X i).residueField P.genericPoint) :=
    ((N.X i).residue P.genericPoint).hom.toAlgebra
  haveI : IsScalarTower ℂ ((N.X i).presheaf.stalk P.genericPoint)
      ((N.X i).residueField P.genericPoint) := IsScalarTower.of_algebraMap_eq' rfl
  have hfacts := stalk_facts_of_eq_genericPoint (sY := N.n i ≫ sT) P hjP
  haveI : Module.Free ((N.X i).presheaf.stalk P.genericPoint)
      Ω[(N.X i).presheaf.stalk P.genericPoint⁄ℂ] := hfacts.2.1
  have key := exists_uniformizer_of_eq_genericPoint (sY := N.n i ≫ sT)
    (j := P.idealSheaf.subschemeι) P hjP
  obtain ⟨ϖ, r, hϖ0, hr, hunif⟩ : ∃ (ϖ : (N.X i).presheaf.stalk P.genericPoint)
      (r : Ω[(N.X i).presheaf.stalk P.genericPoint⁄ℂ] →ₗ[(N.X i).presheaf.stalk P.genericPoint]
        (N.X i).presheaf.stalk P.genericPoint),
      (P.idealSheaf.subschemeι.stalkMap (genericPoint P.idealSheaf.subscheme)).hom ϖ = 0 ∧
      r (KaehlerDifferential.D ℂ _ ϖ) = 1 ∧
      ∀ t : (N.X i).presheaf.stalk P.genericPoint,
        (N.X i).ord (algebraMap _ (N.X i).functionField t) P.genericPoint = 1 →
          ∃ v, IsUnit v ∧ t = v * ϖ := by
    obtain ⟨ϖ, r, h1, h2, -, -, h5⟩ := key
    exact ⟨ϖ, r, h1, h2, h5⟩
  have hϖL : algebraMap ((N.X i).presheaf.stalk P.genericPoint)
      ((N.X i).residueField P.genericPoint) ϖ = 0 := by
    have hm : ϖ ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk P.genericPoint) := by
      by_contra hc
      have hu := (IsLocalRing.notMem_maximalIdeal.mp hc).map
        (P.idealSheaf.subschemeι.stalkMap (genericPoint P.idealSheaf.subscheme)).hom
      exact not_isUnit_zero (hϖ0 ▸ hu)
    exact (IsLocalRing.residue_eq_zero_iff ϖ).mpr hm
  have hO : ∀ z : (N.X i).functionField, (N.X i).ord z P.genericPoint = 1 →
      ∃ v : (N.X i).presheaf.stalk P.genericPoint, IsUnit v ∧
        algebraMap _ (N.X i).functionField (v * ϖ) = z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      have := congrFun Scheme.ord_zero P.genericPoint
      simp only [Pi.zero_apply] at this
      omega
    obtain ⟨t, ht⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
      P.genericPoint hz0 fun Γ hΓ => by
        obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
        omega
    obtain ⟨v, hv, rfl⟩ := hunif t (by rw [ht]; exact hz)
    exact ⟨v, hv, ht⟩
  obtain ⟨v₁, hv₁, rfl⟩ := hO z₁ hz₁
  obtain ⟨v₂, hv₂, rfl⟩ := hO z₂ hz₂
  set x₁ : Fin 1 → (N.X i).presheaf.stalk P.genericPoint := fun l =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V (a l))
  set x₂ : Fin 1 → (N.X i).presheaf.stalk P.genericPoint := fun l =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V') P.genericPoint hP' ((N.n i).app V' (a' l))
  have e₁ : s = logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) ℂ
      (N.X i).functionField m 1 h₁ (v₁ * ϖ) x₁ := by
    rw [hs₁, logPluriForm_eq_dite]
  have e₂ : s' = logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) ℂ
      (N.X i).functionField m 1 h₂ (v₂ * ϖ) x₂ := by
    rw [hs₂, logPluriForm_eq_dite]
  have heq : logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) ℂ
      (N.X i).functionField m 1 h₁ (v₁ * ϖ) x₁ =
      logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) ℂ
      (N.X i).functionField m 1 (u * h₂) (v₂ * ϖ) x₂ := by
    have hmul : logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) ℂ
        (N.X i).functionField m 1 (u * h₂) (v₂ * ϖ) x₂ =
        algebraMap _ (N.X i).functionField u • logPluriForm
          (O := (N.X i).presheaf.stalk P.genericPoint) ℂ (N.X i).functionField m 1 h₂ (v₂ * ϖ)
          x₂ := by
      simp only [logPluriForm, map_mul, mul_smul]
    exact e₁.symm.trans (hu.trans (by rw [e₂]; exact hmul.symm))
  have hres := logPluriResidue_eq_of_logPluriForm_eq (k := ℂ) (K := (N.X i).functionField)
    (L := (N.X i).residueField P.genericPoint) IsLocalRing.residue_surjective hϖL hr hv₁ hv₂
    x₁ x₂ heq
  have := logPluriResidue_eval hres D
  rw [map_mul] at this
  change (N.X i).residue P.genericPoint h₁ * _ = (N.X i).residue P.genericPoint u *
    (N.X i).residue P.genericPoint h₂ * _ at this
  rw [hr₁, hr₂] at this
  exact this

/-- If `(c b)^{⊗n}` is written in the basis `b^{⊗n}` of the `n`-th tensor power of a line,
its coordinate is `cⁿ`. -/
private theorem tprod_smul_eq_smul_basis {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Module.Basis Unit K L) (c : K) (n : ℕ) :
    ∀ τ : ZTensorPower K L (n : ℤ),
      τ = (PiTensorProduct.tprod K (fun _ : Fin n => c • b ()) : TensorPower K n L) →
      τ = c ^ n • ZTensorPower.basis b n () := by
  rintro τ rfl
  rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  change _ = ((Basis.piTensorProduct fun _ : Fin n => b).reindex (Equiv.ofUnique _ _)) ()
  rw [Module.Basis.reindex_apply, Basis.piTensorProduct_apply]

/-- If `dv₁ ∧ ⋯ ∧ dv_d = c σ` for a generator `σ` of `Ω^d_{A/k}`, then
`(dv₁ ∧ ⋯ ∧ dv_d)^{⊗n}` has coordinate `cⁿ` along `σ^{⊗n}`. -/
private theorem formCoeff_tprod_ιMulti {k A K : Type*} [CommRing k] [CommRing A] [Field K]
    [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] {d : ℕ}
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0)
    {v : Fin d → A} {c : A}
    (hc : exteriorPower.ιMulti A d (fun j => KaehlerDifferential.D k A (v j)) = c • σ)
    (n : ℕ) : ∀ τ : PluriForms k K d n,
      τ = (PiTensorProduct.tprod K (fun _ : Fin n => exteriorPower.ιMulti K d
        (fun j => KaehlerDifferential.D k K (algebraMap A K (v j)))) : TensorPower K n _) →
      formCoeff A hσ h0 τ = algebraMap A K c ^ n := by
  intro τ hτ
  have hv : exteriorPower.ιMulti K d (fun j => KaehlerDifferential.D k K (algebraMap A K (v j))) =
      algebraMap A K c • topFormsBasis A hσ h0 () := by
    have := congrArg (topFormsMap k A K d) hc
    rw [topFormsMap_ιMulti, map_smul] at this
    simp only [KaehlerDifferential.map_D] at this
    rw [topFormsBasis_apply, algebraMap_smul, ← this]
  rw [hv] at hτ
  have := tprod_smul_eq_smul_basis (topFormsBasis A hσ h0) (algebraMap A K c) n τ hτ
  rw [formCoeff, this]
  simp

/-- **Forms built from regular functions are regular.** On a normal variety of dimension `d`,
`(dv₁ ∧ ⋯ ∧ dv_d)^{⊗m}` has no pole along a prime divisor `Γ` when the `vⱼ` are regular at the
generic point of `Γ`. -/
private theorem zero_le_ordForm_tprod_ιMulti {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) (Γ : MMP.Mori.PrimeDivisor X) (m : ℕ)
    (v : Fin d → X.presheaf.stalk Γ.genericPoint) :
    letI := functionFieldAlgebra sX
    ∀ τ : RationalPluriForms sX d m,
      τ = (PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti X.functionField d (fun j =>
          KaehlerDifferential.D ℂ X.functionField (algebraMap _ X.functionField (v j)))) :
          TensorPower X.functionField m _) →
      τ ≠ 0 → 0 ≤ Γ.ordForm τ := by
  letI := functionFieldAlgebra sX
  intro τ hτ hτ0
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  obtain ⟨σ, hσ, h0⟩ := Γ.exists_topForms_generator_of_topologicalKrullDim_eq (sX := sX) hd
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hσ ▸ Submodule.mem_top
    (x := exteriorPower.ιMulti Γ.localRing d fun j => KaehlerDifferential.D ℂ Γ.localRing (v j)))
  have hcoeff := formCoeff_tprod_ιMulti hσ h0 hc.symm m τ hτ
  rw [Γ.ordForm_eq τ hσ h0, hcoeff]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hc0 : algebraMap Γ.localRing X.functionField c ≠ 0 := by
    intro h
    exact hτ0 ((formCoeff_eq_zero_iff (m := (m : ℤ)) hσ h0 τ).1
      (by rw [hcoeff, h, zero_pow hm.ne']))
  rw [← zpow_natCast, MMP.Mori.ord_zpow _ hc0]
  have hv' := (Γ.divisorialValuation_le_one_iff _).2 ⟨c, rfl⟩
  rw [Γ.divisorialValuation_eq_exp_neg_ord hc0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv'
  have hc1 : 0 ≤ X.ord (algebraMap Γ.localRing X.functionField c) Γ.genericPoint := by omega
  exact mul_nonneg (by positivity) hc1

/-- **The residue of a local generator along a conductor component is a unit.** If `s ≠ 0` has
order `-m` along the prime divisor `P` of the surface `Tᵢ` and residue presentation
`ε ḡ (dā)^{⊗m}` along `P` with `ε ≠ 0`, then `ḡ(P) ≠ 0`: writing `s = h (t⁻¹ dt ∧ da)^{⊗m}`,
the form `(dt ∧ da)^{⊗m}` has no pole, so `ord_P h ≤ 0` and `h` is a unit. -/
private theorem residue_ne_zero_of_isLogResiduePresentation {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : MMP.Flips.NormalizationComponents sT hT} {m : ℕ} {i : N.ι}
    {P : MMP.Mori.PrimeDivisor (N.X i)} {V : T.Opens} {hP : (N.n i).base P.genericPoint ∈ V}
    {a : Fin (2 - 1) → Γ(T, V)} {g : Γ(T, V)} {ε : ℤ} (hε : ε ≠ 0)
    {s : RationalPluriForms (N.n i ≫ sT) 2 m}
    (h : IsLogResiduePresentation N 2 m i P V hP a g ε s)
    (hdim : topologicalKrullDim (N.X i) = (2 : ℕ)) (hs0 : s ≠ 0)
    (hord : P.ordForm s = -(m : ℤ)) :
    (N.X i).residue P.genericPoint
      ((N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V g)) ≠ 0 := by
  obtain ⟨z, h₁, hz, hs, -, hr⟩ := h
  beta_reduce at hs hr
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (N.n i ≫ sT)
  have hz0 : z ≠ 0 := by
    rintro rfl
    have := congrFun Scheme.ord_zero P.genericPoint
    simp only [Pi.zero_apply] at this
    omega
  obtain ⟨t, rfl⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg
    P.genericPoint hz0 fun Γ hΓ => by
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      omega
  set x : Fin 1 → (N.X i).presheaf.stalk P.genericPoint := fun l =>
    (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V (a l))
  set τ : RationalPluriForms (N.n i ≫ sT) 2 m :=
    (PiTensorProduct.tprod (N.X i).functionField (fun _ : Fin m =>
      exteriorPower.ιMulti (N.X i).functionField 2 (fun j =>
        KaehlerDifferential.D ℂ (N.X i).functionField
          (algebraMap _ (N.X i).functionField ((Fin.cons t x : Fin 2 → _) j)))) :
      TensorPower (N.X i).functionField m _) with hτdef
  have hst : s = (algebraMap _ (N.X i).functionField h₁ *
      (algebraMap _ (N.X i).functionField t)⁻¹ ^ m) • τ := by
    have e : s = logPluriForm (O := (N.X i).presheaf.stalk P.genericPoint) ℂ
        (N.X i).functionField m 1 h₁ t x := by
      rw [hs, logPluriForm_eq_dite]
    rw [e, logPluriForm, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_smul, hτdef]
    congr 2
  have hτ0 : τ ≠ 0 := by
    rintro h0
    rw [hst, h0, smul_zero] at hs0
    exact hs0 rfl
  have hh0 : algebraMap _ (N.X i).functionField h₁ ≠ 0 := by
    rintro h0
    rw [hst, h0, zero_mul, zero_smul] at hs0
    exact hs0 rfl
  have hc : algebraMap _ (N.X i).functionField h₁ *
      (algebraMap _ (N.X i).functionField t)⁻¹ ^ m ≠ 0 :=
    mul_ne_zero hh0 (pow_ne_zero _ (inv_ne_zero hz0))
  have hτord := zero_le_ordForm_tprod_ιMulti hdim P m (Fin.cons t x) τ rfl hτ0
  rw [hst, P.ordForm_smul_of_topologicalKrullDim_eq hdim hc hτ0, Scheme.ord_mul hh0
    (pow_ne_zero _ (inv_ne_zero hz0)), ← zpow_natCast, MMP.Mori.ord_zpow _ (inv_ne_zero hz0),
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hz0, hz] at hord
  have hh1 : (N.X i).ord (algebraMap _ (N.X i).functionField h₁) P.genericPoint = 0 := by
    have hv' := (P.divisorialValuation_le_one_iff _).2 ⟨h₁, rfl⟩
    rw [P.divisorialValuation_eq_exp_neg_ord hh0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv'
    nlinarith
  obtain ⟨w, hw, hwh⟩ := MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    P.genericPoint hh0 fun Γ hΓ => by
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      exact hh1
  obtain rfl : w = h₁ := IsFractionRing.injective _ (N.X i).functionField hwh
  intro h0
  have h2 : (N.X i).residue P.genericPoint w ≠ 0 := by
    change IsLocalRing.residue _ w ≠ 0
    rw [Ne, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.notMem_maximalIdeal.mpr hw)
  rw [hr, h0, mul_zero] at h2
  exact h2 rfl

/-- **Two local generators differ by a unit at every point.** On a normal variety of dimension
`d`, if `s` and `s'` both generate `𝒪(m(K + Θ))` on an open `W`, then at every point `z ∈ W`,
`s = u s'` for a unit `u` of `𝒪_z` (algebraic Hartogs). -/
private theorem exists_isUnit_stalk_smul_eq_of_generatesOn {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) {Θ : QDivisor X} {m : ℕ} {W : X.Opens}
    {s s' : RationalPluriForms sX d m} (hs : GeneratesOn Θ m W s) (hs' : GeneratesOn Θ m W s')
    {z : X} (hz : z ∈ W) :
    ∃ u : X.presheaf.stalk z, IsUnit u ∧ s = algebraMap _ X.functionField u • s' := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set B := ZTensorPower.basis b ((m : ℕ) : ℤ)
  have hc' : B.repr s' () ≠ 0 := repr_ne_zero_of_ne_zero b hs'.1
  set q := B.repr s () / B.repr s' ()
  have hq : s = q • s' := by
    rw [← basis_unit_repr_smul B s, ← basis_unit_repr_smul B s']
    exact (by rw [← mul_smul, div_mul_cancel₀ _ hc'] :
      (B.repr s () • B () : ZTensorPower _ _ _) = q • B.repr s' () • B ())
  have hq0 : q ≠ 0 := div_ne_zero (repr_ne_zero_of_ne_zero b hs.1) hc'
  obtain ⟨u, hu, hqu⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero z hq0
    fun Γ hΓ => by
      have hΓW : (Γ.support ∩ (W : Set X)).Nonempty := ⟨z, hΓ, hz⟩
      have e1 := hs.2 Γ hΓW
      have e2 := hs'.2 Γ hΓW
      rw [hq, Γ.ordForm_smul_of_topologicalKrullDim_eq hd hq0 hs'.1] at e1
      push_cast at e1
      have : ((X.ord q Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
      exact_mod_cast this
  exact ⟨u, hu, by rw [hqu]; exact hq⟩

/-- The map `𝒪_{Y,y} ⟶ 𝒪_{X,x}` for `f(x) = y`, on germs. -/
private theorem stalkSpecializes_stalkMap_germ {X Y : Scheme.{0}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f.base x ⤳ y) (V : Y.Opens) (hy : y ∈ V) (e : Γ(Y, V)) :
    (Y.presheaf.stalkSpecializes h ≫ f.stalkMap x).hom (Y.presheaf.germ V y hy e) =
      X.presheaf.germ (f ⁻¹ᵁ V) x (h.mem_open V.isOpen hy) (f.app V e) := by
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- For a closed immersion `f` with `f(x) = y`, `𝒪_{Y,y} ⟶ 𝒪_{X,x}` is surjective. -/
private theorem surjective_stalkSpecializes_stalkMap {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] {x : X} {y : Y} (hxy : f.base x = y) (h : f.base x ⤳ y) :
    Function.Surjective (Y.presheaf.stalkSpecializes h ≫ f.stalkMap x).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact SurjectiveOnStalks.stalkMap_surjective f x

/-- In a local domain of dimension at most one, the maximal ideal lies in the radical of every
nonzero principal ideal. -/
private theorem maximalIdeal_le_radical_span {B : Type*} [CommRing B] [IsLocalRing B] [IsDomain B]
    (hB : ringKrullDim B ≤ 1) {b : B} (hb : b ≠ 0) :
    IsLocalRing.maximalIdeal B ≤ (Ideal.span {b}).radical := by
  haveI : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.2 hB
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J ⟨hJb, hJ⟩ => ?_
  have hJ0 : J ≠ ⊥ := fun h0 => hb (by
    have : b ∈ J := hJb (Ideal.mem_span_singleton_self b)
    rwa [h0, Ideal.mem_bot] at this)
  have hJm := (Ring.krullDimLE_one_iff_of_isPrime_bot.1 inferInstance) J hJ0 hJ
  exact (IsLocalRing.eq_maximalIdeal hJm).ge

/-- Two surjections `p : A → B`, `q : A → C` of local rings induce an isomorphism of residue
fields, both being the residue field of `A`. -/
private theorem exists_residueField_ringEquiv {A B C : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C] (p : A →+* B) (q : A →+* C)
    (hp : Function.Surjective p) (hq : Function.Surjective q) :
    ∃ τ : IsLocalRing.ResidueField B ≃+* IsLocalRing.ResidueField C,
      ∀ a, τ (IsLocalRing.residue B (p a)) = IsLocalRing.residue C (q a) := by
  set fp := (IsLocalRing.residue B).comp p
  set fq := (IsLocalRing.residue C).comp q
  have hfp : Function.Surjective fp := IsLocalRing.residue_surjective.comp hp
  have hfq : Function.Surjective fq := IsLocalRing.residue_surjective.comp hq
  have hkp : RingHom.ker fp = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective fp hfp)
  have hkq : RingHom.ker fq = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective fq hfq)
  set ep := RingHom.quotientKerEquivOfSurjective hfp
  set eq' := RingHom.quotientKerEquivOfSurjective hfq
  refine ⟨ep.symm.trans ((Ideal.quotEquivOfEq (hkp.trans hkq.symm)).trans eq'), fun a => ?_⟩
  have h1 : ep.symm (IsLocalRing.residue B (p a)) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk]
  rfl

/-- A derivation transported along an isomorphism of algebras. -/
private theorem exists_derivation_transport {R F G : Type*} [CommRing R] [CommRing F]
    [CommRing G] [Algebra R F] [Algebra R G] (τ : F ≃ₐ[R] G) (D : Derivation R F F) :
    ∃ D' : Derivation R G G, ∀ y, D' (τ y) = τ (D y) := by
  refine ⟨Derivation.mk' (τ.toLinearMap ∘ₗ D.toLinearMap ∘ₗ τ.symm.toLinearMap) fun a b => ?_,
    fun y => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
    change τ (D (τ.symm a * τ.symm b)) = a • τ (D (τ.symm b)) + b • τ (D (τ.symm a))
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, map_add, map_mul,
      map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  · simp

/-- **Residues of the ratio of two local generators agree across a double point.** Let `s, s'` be
local generators of the adjoint of the sdlt surface `T` on `U`
(`MMP.Fourfold.IsAdjointGeneratorOn`) and `x ∈ U` a point of the double locus lying on two distinct
normalization components, over the codimension-one points `y₀ ∈ T_{k₀}` and `y ∈ T_k`. If
`s = u₀ s'` near `y₀` and `s = u s'` near `y`, and `r ∈ 𝒪_{T,x}` has `r(y₀) = u₀(y₀)`, then
`r(y) = u(y)`: evaluating the two residue presentations of `s` and of `s'` against a derivation `D`
with `D(ā') ≠ 0`, transported between the two branches through `κ(x)`, gives `ū₀ = ū` in `κ(x)`. -/
private theorem residue_eq_of_isAdjointGeneratorOn {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} (hci : ∀ i, IsClosedImmersion (N.n i))
    (hdim : ∀ i, topologicalKrullDim (N.X i) = (2 : ℕ)) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (Θ i).coeff P = 1)
    {m : ℕ} {U : T.Opens} {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m}
    (hs : IsAdjointGeneratorOn N 2 m Θ U s) (hs' : IsAdjointGeneratorOn N 2 m Θ U s')
    {x : T} (hxU : x ∈ U) (hxD : x ∈ (doubleIntersectionLocus T : Set T))
    {k₀ k : N.ι} (hk : k₀ ≠ k) {y₀ : N.X k₀} {y : N.X k}
    (hy₀ : (N.n k₀).base y₀ = x) (hy : (N.n k).base y = x)
    (hc₀ : Order.coheight y₀ = 1) (hc : Order.coheight y = 1)
    (h₀ : (N.n k₀).base y₀ ⤳ x) (h : (N.n k).base y ⤳ x)
    {u₀ : (N.X k₀).presheaf.stalk y₀} {u : (N.X k).presheaf.stalk y}
    (hu₀ : s k₀ = algebraMap _ (N.X k₀).functionField u₀ • s' k₀)
    (hu : s k = algebraMap _ (N.X k).functionField u • s' k)
    (r : T.presheaf.stalk x)
    (hr : IsLocalRing.residue _ ((T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap y₀).hom r) =
      IsLocalRing.residue _ u₀) :
    IsLocalRing.residue _ ((T.presheaf.stalkSpecializes h ≫ (N.n k).stalkMap y).hom r) =
      IsLocalRing.residue _ u := by
  classical
  obtain ⟨P₀, rfl⟩ : ∃ P : MMP.Mori.PrimeDivisor (N.X k₀), P.genericPoint = y₀ :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y₀ hc₀,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc₀⟩
  obtain ⟨P, rfl⟩ : ∃ P : MMP.Mori.PrimeDivisor (N.X k), P.genericPoint = y :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc⟩
  subst hy₀
  have h₄ : (⟨k₀, P₀.genericPoint⟩ : Σ i, N.X i) ≠ ⟨k, P.genericPoint⟩ :=
    fun he => hk (congrArg Sigma.fst he)
  obtain ⟨V, hP₀V, hPV, a, g, hpr₀, hpr⟩ := hs.2 k₀ k P₀ P hy.symm hxU hxD h₄
  obtain ⟨V', hP₀V', hPV', a', g', hpr₀', hpr'⟩ := hs'.2 k₀ k P₀ P hy.symm hxU hxD h₄
  -- the two residue fields, with the `ℂ`-structures of the presentations
  letI alg₀ : Algebra ℂ ((N.X k₀).residueField P₀.genericPoint) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (N.n k₀ ≫ sT).appTop ≫
      (N.X k₀).Γevaluation P₀.genericPoint).hom.toAlgebra
  letI alg : Algebra ℂ ((N.X k).residueField P.genericPoint) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (N.n k ≫ sT).appTop ≫
      (N.X k).Γevaluation P.genericPoint).hom.toAlgebra
  -- the identification of the residue fields through `κ(x)`
  haveI := hci k₀
  haveI := hci k
  obtain ⟨τ, hτ⟩ : ∃ τ : (N.X k₀).residueField P₀.genericPoint ≃+*
      (N.X k).residueField P.genericPoint, ∀ a,
      τ ((N.X k₀).residue P₀.genericPoint
        ((T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap P₀.genericPoint).hom a)) =
      (N.X k).residue P.genericPoint
        ((T.presheaf.stalkSpecializes h ≫ (N.n k).stalkMap P.genericPoint).hom a) :=
    exists_residueField_ringEquiv
      (T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap P₀.genericPoint).hom
      (T.presheaf.stalkSpecializes h ≫ (N.n k).stalkMap P.genericPoint).hom
      (surjective_stalkSpecializes_stalkMap _ rfl h₀) (surjective_stalkSpecializes_stalkMap _ hy h)
  have hgerm : ∀ (W : T.Opens) (hW : (N.n k₀).base P₀.genericPoint ∈ W) (f : Γ(T, W)),
      τ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ W)
          P₀.genericPoint hW ((N.n k₀).app W f))) =
        (N.X k).residue P.genericPoint ((N.X k).presheaf.germ ((N.n k) ⁻¹ᵁ W)
          P.genericPoint (h.mem_open W.isOpen hW) ((N.n k).app W f)) := by
    intro W hW f
    have e₀ := stalkSpecializes_stalkMap_germ (N.n k₀) h₀ W hW f
    have e₁ := stalkSpecializes_stalkMap_germ (N.n k) h W hW f
    have := hτ (T.presheaf.germ W _ hW f)
    rw [e₀, e₁] at this
    exact this
  -- `τ` is `ℂ`-linear
  have hcomp₀ : ∀ c : ℂ, algebraMap ℂ ((N.X k₀).residueField P₀.genericPoint) c =
      (N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ ⊤)
        P₀.genericPoint trivial
        ((N.n k₀).app ⊤ (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sT.appTop).hom c))) := fun c => rfl
  have hcomp : ∀ c : ℂ, algebraMap ℂ ((N.X k).residueField P.genericPoint) c =
      (N.X k).residue P.genericPoint ((N.X k).presheaf.germ ((N.n k) ⁻¹ᵁ ⊤)
        P.genericPoint (h.mem_open (⊤ : T.Opens).isOpen trivial)
        ((N.n k).app ⊤ (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sT.appTop).hom c))) := fun c => rfl
  let τA : (N.X k₀).residueField P₀.genericPoint ≃ₐ[ℂ] (N.X k).residueField P.genericPoint :=
    AlgEquiv.ofRingEquiv (f := τ) fun c => by
      rw [hcomp₀, hgerm ⊤ trivial, hcomp]
  -- a derivation of `κ(P₀)` not killing `ā'`
  obtain ⟨-, -, -, -, hda', -⟩ := id hpr₀'
  set v := KaehlerDifferential.D ℂ ((N.X k₀).residueField P₀.genericPoint)
    ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
      P₀.genericPoint hP₀V' ((N.n k₀).app V' (a' 0)))) with hvdef
  have hv : v ≠ 0 := fun h0 =>
    hda' ((exteriorPower.ιMulti _ _).map_coord_zero (0 : Fin (2 - 1)) h0)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ((N.X k₀).residueField P₀.genericPoint)
      Ω[(N.X k₀).residueField P₀.genericPoint⁄ℂ], φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv ((Module.forall_dual_apply_eq_zero_iff _ v).mp hcon)
  set D₀ := φ.compDer (KaehlerDifferential.D ℂ ((N.X k₀).residueField P₀.genericPoint))
  obtain ⟨D, hD⟩ := exists_derivation_transport τA D₀
  -- the two evaluations
  have E₀ := isLogResiduePresentation_eval hpr₀ hpr₀' u₀ hu₀ D₀
  have E := isLogResiduePresentation_eval hpr hpr' u hu D
  have hτD : ∀ (W : T.Opens) (hW : (N.n k₀).base P₀.genericPoint ∈ W) (f : Γ(T, W)),
      D ((N.X k).residue P.genericPoint ((N.X k).presheaf.germ ((N.n k) ⁻¹ᵁ W)
          P.genericPoint (h.mem_open W.isOpen hW) ((N.n k).app W f))) =
        τ (D₀ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ W)
          P₀.genericPoint hW ((N.n k₀).app W f)))) := by
    intro W hW f
    rw [← hgerm W hW f]
    exact hD _
  rw [← hgerm V hP₀V g, ← hgerm V' hP₀V' g', hτD V hP₀V (a 0), hτD V' hP₀V' (a' 0)] at E
  have E₀' := congrArg τ E₀
  simp only [map_mul, map_pow, map_intCast] at E₀'
  -- nonvanishing
  have hord : P₀.ordForm (s' k₀) = -(m : ℤ) := by
    have := (hs'.1 k₀).2 P₀ ⟨P₀.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P₀,
      hxU⟩
    rw [hΘ k₀ P₀ hxD, mul_one] at this
    have h2 : ((P₀.ordForm (s' k₀) : ℤ) : ℚ) = ((-(m : ℤ) : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2
  have hg0 := residue_ne_zero_of_isLogResiduePresentation one_ne_zero hpr₀' (hdim k₀)
    (hs'.1 k₀).1 hord
  have hY : τ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
        P₀.genericPoint hP₀V' ((N.n k₀).app V' g'))) *
      τ (D₀ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
        P₀.genericPoint hP₀V' ((N.n k₀).app V' (a' 0))))) ^ m ≠ 0 :=
    mul_ne_zero ((map_ne_zero τ).mpr hg0) (pow_ne_zero _ ((map_ne_zero τ).mpr hφ))
  have hsign : (((-1 : ℤ) ^ m : ℤ) : (N.X k).residueField P.genericPoint) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have key : τ ((N.X k₀).residue P₀.genericPoint u₀) = (N.X k).residue P.genericPoint u := by
    have h3 : (((-1 : ℤ) ^ m : ℤ) : (N.X k).residueField P.genericPoint) *
        (τ ((N.X k₀).residue P₀.genericPoint u₀) - (N.X k).residue P.genericPoint u) *
        (τ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
          P₀.genericPoint hP₀V' ((N.n k₀).app V' g'))) *
        τ (D₀ ((N.X k₀).residue P₀.genericPoint ((N.X k₀).presheaf.germ ((N.n k₀) ⁻¹ᵁ V')
          P₀.genericPoint hP₀V' ((N.n k₀).app V' (a' 0))))) ^ m) = 0 := by
      push_cast at E E₀' ⊢
      linear_combination E - (-1 : (N.X k).residueField P.genericPoint) ^ m * E₀'
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact absurd h5 hsign
      · exact sub_eq_zero.mp h5
    · exact absurd h4 hY
  have h6 := hτ r
  rw [show (N.X k₀).residue P₀.genericPoint
      ((T.presheaf.stalkSpecializes h₀ ≫ (N.n k₀).stalkMap P₀.genericPoint).hom r) =
      (N.X k₀).residue P₀.genericPoint u₀ from hr, key] at h6
  exact h6.symm

/-- The union of the components not passing through `x` is closed. -/
private theorem isClosed_iUnion_range_of_notMem {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [Finite N.ι] (hci : ∀ i, IsClosedImmersion (N.n i))
    (x : T) : IsClosed (⋃ (i : N.ι) (_ : x ∉ Set.range (N.n i).base), Set.range (N.n i).base) :=
  isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => by
    haveI := hci i
    exact (N.n i).isClosedEmbedding.isClosed_range

/-- **Functions on `T` are detected on the components through a point.** A germ at `x` of the
reduced scheme `T` vanishing on every normalization component through `x` is zero. -/
private theorem stalk_eq_zero_of_forall_stalkMap {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i)) {x : T}
    (y : ∀ i : {i // x ∈ Set.range (N.n i).base}, N.X i.1)
    (hy : ∀ i : {i // x ∈ Set.range (N.n i).base}, (N.n i.1).base (y i) ⤳ x) (a : T.presheaf.stalk x)
    (ha : ∀ i : {i // x ∈ Set.range (N.n i).base}, (T.presheaf.stalkSpecializes (hy i) ≫ (N.n i.1).stalkMap (y i)).hom a = 0) :
    a = 0 := by
  classical
  obtain ⟨V₀, hxV₀, e, rfl⟩ := TopCat.Presheaf.germ_exist T.presheaf a
  set C := ⋃ (i : N.ι) (_ : x ∉ Set.range (N.n i).base), Set.range (N.n i).base
  have hC := isClosed_iUnion_range_of_notMem N hci x
  have hxC : x ∉ C := by
    intro h
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
    exact hi hxi
  set V : T.Opens := V₀ ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hxV : x ∈ V := ⟨hxV₀, hxC⟩
  have hVV₀ : V ≤ V₀ := inf_le_left
  have hres : T.presheaf.map (homOfLE hVV₀).op e = 0 := by
    refine eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_
    have hz := hi.some.2
    set z := hi.some.1
    have hxi : x ∈ Set.range (N.n i).base := by
      by_contra hxi
      exact hz.2 (Set.mem_iUnion₂.mpr ⟨i, hxi, z, rfl⟩)
    set k : {i // x ∈ Set.range (N.n i).base} := ⟨i, hxi⟩
    have hyV : y k ∈ N.n k.1 ⁻¹ᵁ V := (hy k).mem_open V.isOpen hxV
    have h1 := ha k
    rw [← TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hVV₀) x hxV e,
      stalkSpecializes_stalkMap_germ] at h1
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hyV]
    exact (congrArg (algebraMap _ _) h1).trans (map_zero _)
  rw [← TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hVV₀) x hxV e, hres, map_zero]

/-- **A germ vanishing on all components through `x` but one.** For components `l ≠ k` through
`x`, there is a germ at `x` vanishing on the `T_l` but not on `T_k`: a function on an affine
neighbourhood of `x` with a basic open containing the generic point of `T_k` and avoiding the
other components. -/
private theorem exists_stalk_vanishing {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i))
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base) {x : T}
    (y : ∀ i : {i // x ∈ Set.range (N.n i).base}, N.X i.1)
    (hy : ∀ i : {i // x ∈ Set.range (N.n i).base}, (N.n i.1).base (y i) ⤳ x) (k : {i // x ∈ Set.range (N.n i).base}) :
    ∃ c : T.presheaf.stalk x,
      (∀ l : {i // x ∈ Set.range (N.n i).base}, l ≠ k → (T.presheaf.stalkSpecializes (hy l) ≫ (N.n l.1).stalkMap (y l)).hom c = 0) ∧
      (T.presheaf.stalkSpecializes (hy k) ≫ (N.n k.1).stalkMap (y k)).hom c ≠ 0 := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVa : IsAffineOpen V := hV
  set Z := ⋃ (j : N.ι) (_ : j ≠ k.1), Set.range (N.n j).base
  have hZ : IsClosed Z := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => by
    haveI := hci j
    exact (N.n j).isClosedEmbedding.isClosed_range
  have hηx : (N.n k.1).base (genericPoint (N.X k.1)) ⤳ x :=
    (((genericPoint_spec (N.X k.1)).specializes trivial).map (N.n k.1).base.hom.continuous).trans
      (hy k)
  have hηV : (N.n k.1).base (genericPoint (N.X k.1)) ∈ V := hηx.mem_open V.isOpen hxV
  set W : T.Opens := V ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨f, hfW, hηf⟩ := hVa.exists_basicOpen_le (V := W) ⟨_, hηV, hgen k⟩ hηV
  refine ⟨T.presheaf.germ V x hxV f, fun l hl => ?_, ?_⟩
  · rw [stalkSpecializes_stalkMap_germ]
    have h0 : (N.n l.1).app V f = 0 := by
      rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
      refine eq_bot_iff.mpr fun z hz => ?_
      have := (hfW hz).2
      exact this (Set.mem_iUnion₂.mpr ⟨l, fun h => hl (Subtype.ext h), z, rfl⟩)
    rw [h0, map_zero]
  · rw [stalkSpecializes_stalkMap_germ]
    intro h0
    have hne : (N.n k.1).app V f ≠ 0 := by
      intro h1
      have : genericPoint (N.X k.1) ∈ (N.X k.1).basicOpen ((N.n k.1).app V f) := by
        rw [← Scheme.preimage_basicOpen]
        exact hηf
      rw [h1, Scheme.basicOpen_zero] at this
      exact this
    exact hne (germ_injective_of_isIntegral _ _ _ (h0.trans (map_zero _).symm))

/-- A point with a proper generalization and a local ring of dimension at most one has
coheight one. -/
private theorem coheight_eq_one_of_lt {X : Scheme.{0}} {y η : X} (hηy : η ⤳ y) (hne : η ≠ y)
    (hd : ringKrullDim (X.presheaf.stalk y) ≤ 1) : Order.coheight y = 1 := by
  have h1 : Order.coheight y ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight] at hd
    exact_mod_cast hd
  have h0 : Order.coheight y ≠ 0 := by
    rw [Ne, Order.coheight_eq_zero]
    intro hmax
    have hle : y ≤ η := hηy
    exact hne (hηy.antisymm (hmax hle)).eq
  exact le_antisymm h1 (ENat.one_le_iff_ne_zero.mpr h0)

/-- **Local descent of the ratio of two adjoint generators.** Let `T` be a reduced seminormal
surface whose normalization components `νᵢ : Tᵢ ⟶ T` are closed immersions with distinct
generic points, and `s, s'` local generators of the adjoint of `T` on `U`. Near every point
`x ∈ U` which lies on a single component, or whose local ring has dimension at most one, there
is a function `e` with `sᵢ = ν^*e · s'ᵢ`: the ratios `uₖ = sₖ / s'ₖ` are units at the points over
`x`, agree in `κ(x)` (`residue_eq_of_isAdjointGeneratorOn`), and so come from `𝒪_{T,x}` by
seminormality (`exists_eq_of_forall_sub_mem`). -/
private theorem exists_local_smul_eq_of_isAdjointGeneratorOn {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] (hsn : IsSeminormal T) [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i))
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base)
    (hdim : ∀ i, topologicalKrullDim (N.X i) = (2 : ℕ)) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (Θ i).coeff P = 1)
    {m : ℕ} {U : T.Opens} {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m}
    (hs : IsAdjointGeneratorOn N 2 m Θ U s) (hs' : IsAdjointGeneratorOn N 2 m Θ U s')
    (x : T) (hxU : x ∈ U)
    (hx : ringKrullDim (T.presheaf.stalk x) ≤ 1 ∨
      ∀ i j, x ∈ Set.range (N.n i).base → x ∈ Set.range (N.n j).base → i = j) :
    ∃ V : T.Opens, x ∈ V ∧ V ≤ U ∧ ∃ e : Γ(T, V), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ V)),
      s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V e) • s' i := by
  classical
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  haveI : Fintype {i // x ∈ Set.range (N.n i).base} := Fintype.ofFinite _
  choose y hyx using fun k : {i // x ∈ Set.range (N.n i).base} => k.2
  have hy : ∀ k : {i // x ∈ Set.range (N.n i).base}, (N.n k.1).base (y k) ⤳ x :=
    fun k => by rw [hyx k]
  set p : ∀ k : {i // x ∈ Set.range (N.n i).base},
      T.presheaf.stalk x →+* (N.X k.1).presheaf.stalk (y k) := fun k =>
    (T.presheaf.stalkSpecializes (hy k) ≫ (N.n k.1).stalkMap (y k)).hom with hpdef
  have hsurj : ∀ k, Function.Surjective (p k) := fun k => by
    haveI := hci k.1
    exact surjective_stalkSpecializes_stalkMap _ (hyx k) (hy k)
  have hinj : Function.Injective (Pi.ringHom p) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact stalk_eq_zero_of_forall_stalkMap N hci y hy a fun k => congrFun ha k
  have hyU : ∀ k : {i // x ∈ Set.range (N.n i).base}, y k ∈ N.n k.1 ⁻¹ᵁ U := fun k => by
    change (N.n k.1).base (y k) ∈ U
    rw [hyx k]
    exact hxU
  choose u hu hsu using fun k : {i // x ∈ Set.range (N.n i).base} =>
    exists_isUnit_stalk_smul_eq_of_generatesOn (hdim k.1) (hs.1 k.1) (hs'.1 k.1) (hyU k)
  obtain ⟨i₀, z₀, hz₀⟩ := exists_base_eq N x
  set k₀ : {i // x ∈ Set.range (N.n i).base} := ⟨i₀, z₀, hz₀⟩
  obtain ⟨r, hr⟩ := hsurj k₀ (u k₀)
  -- the descended germ
  obtain ⟨a, ha⟩ : ∃ a, ∀ k, p k a = u k := by
    by_cases hsingle : ∀ k k' : {i // x ∈ Set.range (N.n i).base}, k = k'
    · exact ⟨r, fun k => by rw [hsingle k k₀]; exact hr⟩
    push Not at hsingle
    obtain ⟨k₁, k₂, h12⟩ := hsingle
    have hxd : ringKrullDim (T.presheaf.stalk x) ≤ 1 := hx.resolve_right fun h =>
      h12 (Subtype.ext (h k₁.1 k₂.1 k₁.2 k₂.2))
    have hdimB : ∀ k, ringKrullDim ((N.X k.1).presheaf.stalk (y k)) ≤ 1 := fun k =>
      (ringKrullDim_le_of_surjective (p k) (hsurj k)).trans hxd
    choose c hc0 hck using fun k => exists_stalk_vanishing N hci hgen y hy k
    -- every component through `x` has another one
    have hother : ∀ k : {i // x ∈ Set.range (N.n i).base}, ∃ k', k' ≠ k := fun k => by
      by_cases h1 : k₁ = k
      · exact ⟨k₂, fun h => h12 (h1.trans h.symm)⟩
      · exact ⟨k₁, h1⟩
    -- the points over `x` have coheight one
    have hcoh : ∀ k, Order.coheight (y k) = 1 := fun k => by
      obtain ⟨k', hk'⟩ := hother k
      refine coheight_eq_one_of_lt ((genericPoint_spec (N.X k.1)).specializes trivial)
        (fun h => hgen k.1 (Set.mem_iUnion₂.mpr ⟨k'.1, fun h' => hk' (Subtype.ext h'),
          ⟨y k', by rw [hyx k', h, hyx k]⟩⟩)) (hdimB k)
    -- `x` lies on the double locus
    have hxD : x ∈ (doubleIntersectionLocus T : Set T) := by
      refine subset_closure ⟨?_, fun hreg => ?_⟩
      · obtain ⟨k', hk'⟩ := hother k₀
        refine coheight_eq_one_of_lt (((genericPoint_spec (N.X k₀.1)).specializes trivial).map
          (N.n k₀.1).base.hom.continuous |>.trans (hy k₀)) (fun h => hgen k₀.1
            (Set.mem_iUnion₂.mpr ⟨k'.1, fun h' => hk' (Subtype.ext h'), by rw [h]; exact k'.2⟩))
          hxd
      · haveI := IsRegularLocalRing.isDomain (T.presheaf.stalk x)
        have h0 : c k₁ * c k₂ = 0 := hinj (by
          funext l
          show p l (c k₁ * c k₂) = p l 0
          rw [map_zero, map_mul]
          by_cases hl : l = k₁
          · subst hl
            rw [hc0 k₂ l h12, mul_zero]
          · rw [hc0 k₁ l hl, zero_mul])
        rcases mul_eq_zero.mp h0 with h | h
        · exact hck k₁ (by rw [h, map_zero])
        · exact hck k₂ (by rw [h, map_zero])
    refine exists_eq_of_forall_sub_mem (fun _ _ h => stalk_exists_sq_cube hsn x h) p hinj hsurj
      (fun k => IsLocalRing.maximalIdeal _)
      (fun k => ⟨c k, hc0 k, maximalIdeal_le_radical_span (hdimB k) (hck k)⟩) u r fun k => ?_
    by_cases hk : k = k₀
    · subst hk
      rw [hr, sub_self]
      exact zero_mem _
    have hres := residue_eq_of_isAdjointGeneratorOn hci hdim hΘ hs hs' hxU hxD
      (fun h => hk (Subtype.ext h).symm) (hyx k₀) (hyx k) (hcoh k₀) (hcoh k) (hy k₀) (hy k)
      (hsu k₀) (hsu k) r (by rw [show (T.presheaf.stalkSpecializes (hy k₀) ≫
        (N.n k₀.1).stalkMap (y k₀)).hom r = u k₀ from hr])
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub]
    exact sub_eq_zero.mpr hres.symm
  -- the function near `x`
  obtain ⟨V₀, hxV₀, e, he⟩ := TopCat.Presheaf.germ_exist T.presheaf a
  set C := ⋃ (i : N.ι) (_ : x ∉ Set.range (N.n i).base), Set.range (N.n i).base
  have hC := isClosed_iUnion_range_of_notMem N hci x
  have hxC : x ∉ C := by
    intro h
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
    exact hi hxi
  set V : T.Opens := V₀ ⊓ U ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  have hxV : x ∈ V := ⟨⟨hxV₀, hxU⟩, hxC⟩
  have hVV₀ : V ≤ V₀ := fun z hz => hz.1.1
  refine ⟨V, hxV, fun z hz => hz.1.2, T.presheaf.map (homOfLE hVV₀).op e, fun i hi => ?_⟩
  have hz := hi.some.2
  have hxi : x ∈ Set.range (N.n i).base := by
    by_contra hxi
    exact hz.2 (Set.mem_iUnion₂.mpr ⟨i, hxi, hi.some.1, rfl⟩)
  set k : {i // x ∈ Set.range (N.n i).base} := ⟨i, hxi⟩
  have hyV : y k ∈ N.n k.1 ⁻¹ᵁ V := (hy k).mem_open V.isOpen hxV
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField _ hyV]
  have hgerm : (N.X k.1).presheaf.germ (N.n k.1 ⁻¹ᵁ V) (y k) hyV
      ((N.n k.1).app V (T.presheaf.map (homOfLE hVV₀).op e)) = u k := by
    rw [← stalkSpecializes_stalkMap_germ (N.n k.1) (hy k) V hxV,
      TopCat.Presheaf.germ_res_apply, he]
    exact ha k
  rw [hgerm]
  exact hsu k

/-- **Gluing coefficients along the normalization, and extending them across codimension two.**
Let `T` be reduced and `S₂` with normalization components `νᵢ : Tᵢ ⟶ T`, and let `s, s'` be
families of forms on the `Tᵢ` with `s'ᵢ ≠ 0`. Suppose every point `x ∈ U` that has a local ring of
dimension at most one, or that lies on a single component, has a neighbourhood `V` and a function
`e` on `V` with `sᵢ = ν^*e · s'ᵢ`. Then there is such a function on all of `U`: the local
functions agree on overlaps, as they are detected on the normalization, and the glued function
on the union `W'` extends across `U ∖ W'`, whose local rings have dimension at least two. -/
private theorem exists_smul_eq_of_forall_exists_local {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [IsLocallyNoetherian T]
    (hS2 : SatisfiesS2 T) {n m : ℕ} {U : T.Opens}
    {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m} (hs'0 : ∀ i, s' i ≠ 0)
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base)
    (hloc : ∀ x ∈ U, (ringKrullDim (T.presheaf.stalk x) ≤ 1 ∨
        ∀ i j, x ∈ Set.range (N.n i).base → x ∈ Set.range (N.n j).base → i = j) →
      ∃ V : T.Opens, x ∈ V ∧ V ≤ U ∧ ∃ e : Γ(T, V), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ V)),
        s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V e) • s' i) :
    ∃ e : Γ(T, U), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e) • s' i := by
  classical
  set J := {x : T // x ∈ U ∧ (ringKrullDim (T.presheaf.stalk x) ≤ 1 ∨
    ∀ i j, x ∈ Set.range (N.n i).base → x ∈ Set.range (N.n j).base → i = j)}
  choose V hxV hVU e he using fun x : J => hloc x.1 x.2.1 x.2.2
  set W' : T.Opens := ⨆ x : J, V x with hW'
  have hVW : ∀ x : J, V x ≤ W' := fun x => le_iSup V x
  have hW'U : W' ≤ U := iSup_le hVU
  -- the local functions agree on overlaps
  have hcompat : TopCat.Presheaf.IsCompatible T.presheaf V e := by
    intro x y
    refine sub_eq_zero.mp (eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_)
    haveI := hi
    haveI : Nonempty (N.n i ⁻¹ᵁ V x) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    haveI : Nonempty (N.n i ⁻¹ᵁ V y) := ⟨⟨hi.some.1, hi.some.2.2⟩⟩
    have h1 := he x i inferInstance
    have h2 := he y i inferInstance
    rw [map_sub, map_sub]
    erw [germToFunctionField_app_map (N.n i) inf_le_left, germToFunctionField_app_map (N.n i) inf_le_right]
    refine sub_eq_zero.mpr (smul_left_injective _ (hs'0 i) ?_)
    exact h1.symm.trans h2
  obtain ⟨e', he', -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := T.sheaf) V W'
    (fun x => homOfLE (hVW x)) (fun z hz => by
      obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx⟩) e hcompat
  -- extension across codimension two
  have hcodim : ∀ z ∈ U, z ∉ W' → 2 ≤ ringKrullDim (T.presheaf.stalk z) := by
    intro z hz hzW
    refine Order.succ_le_of_lt (not_le.mp fun hd : ringKrullDim (T.presheaf.stalk z) ≤ 1 => hzW ?_)
    exact hVW ⟨z, hz, Or.inl hd⟩ (hxV _)
  obtain ⟨E, hE⟩ := (MMP.Flips.bijective_presheaf_map_of_satisfiesS2 hS2 hW'U hcodim).2 e'
  refine ⟨E, fun i hi => ?_⟩
  -- the generic point of `Tᵢ` lies on a single component
  obtain ⟨⟨z, hz⟩⟩ := hi
  have hηU : (N.n i).base (genericPoint (N.X i)) ∈ U :=
    ((genericPoint_spec (N.X i)).specializes trivial).map
      (N.n i).base.hom.continuous |>.mem_open U.isOpen hz
  have hone : ∀ a b, (N.n i).base (genericPoint (N.X i)) ∈ Set.range (N.n a).base →
      (N.n i).base (genericPoint (N.X i)) ∈ Set.range (N.n b).base → a = b := by
    intro a b ha hb
    have hai : a = i := by
      by_contra h
      exact hgen i (Set.mem_iUnion₂.mpr ⟨a, h, ha⟩)
    have hbi : b = i := by
      by_contra h
      exact hgen i (Set.mem_iUnion₂.mpr ⟨b, h, hb⟩)
    rw [hai, hbi]
  set x₀ : J := ⟨_, hηU, Or.inr hone⟩
  haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hz⟩⟩
  haveI : Nonempty (N.n i ⁻¹ᵁ V x₀) := ⟨⟨genericPoint (N.X i), hxV x₀⟩⟩
  rw [← germToFunctionField_app_map (N.n i) ((hVW x₀).trans hW'U) E, show
    T.presheaf.map (homOfLE ((hVW x₀).trans hW'U)).op E = e x₀ from by
      rw [← he' x₀, ← hE]
      change _ = T.presheaf.map _ (T.presheaf.map _ E)
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl]
  exact he x₀ i inferInstance

/-- **Any two local generators of the adjoint of a seminormal `S₂` surface differ by a
function.** Let `T` be a reduced, seminormal, `S₂` surface whose normalization components are
closed immersions with distinct generic points, and `s, s'` local generators of the adjoint of
`T` on `U` (`MMP.Fourfold.IsAdjointGeneratorOn`). Then `s = ν^*e · s'` for a function `e` on
`U`: locally by `exists_local_smul_eq_of_isAdjointGeneratorOn`, and globally by gluing and
extending across the closed points (`exists_smul_eq_of_forall_exists_local`). -/
private theorem exists_smul_eq_of_isAdjointGeneratorOn {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] [IsLocallyNoetherian T]
    (hS2 : SatisfiesS2 T) (hsn : IsSeminormal T) [Finite N.ι]
    (hci : ∀ i, IsClosedImmersion (N.n i))
    (hgen : ∀ i, (N.n i).base (genericPoint (N.X i)) ∉
      ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base)
    (hdim : ∀ i, topologicalKrullDim (N.X i) = (2 : ℕ)) {Θ : ∀ i, QDivisor (N.X i)}
    (hΘ : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) → (Θ i).coeff P = 1)
    {m : ℕ} {U : T.Opens} {s s' : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m}
    (hs : IsAdjointGeneratorOn N 2 m Θ U s) (hs' : IsAdjointGeneratorOn N 2 m Θ U s') :
    ∃ e : Γ(T, U), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      s i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e) • s' i :=
  exists_smul_eq_of_forall_exists_local N hS2 (fun i => (hs'.1 i).1) hgen fun x hx hxd =>
    exists_local_smul_eq_of_isAdjointGeneratorOn N hsn hci hgen hdim hΘ hs hs' x hx hxd

end SdltUniqueness

/-- A point specializing to a generic point of a `T₀` space is that generic point. -/
private theorem eq_of_specializes_of_mem_genericPoints {α : Type*} [TopologicalSpace α]
    [T0Space α] {x y : α} (h : x ⤳ y) (hy : y ∈ genericPoints α) : x = y := by
  have h1 : closure {y} = closure {x} :=
    Maximal.eq_of_le hy isIrreducible_singleton.closure (specializes_iff_closure_subset.mp h)
  exact (inseparable_iff_closure_eq.mpr h1.symm).eq

/-- A continuous map with open range sends a generic point of its source to a generic point of
its target. -/
private theorem mem_genericPoints_of_isOpen_range {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {q : α → β} (hq : Continuous q) (ho : IsOpen (Set.range q)) {η : α}
    (hη : closure ({η} : Set α) = Set.univ) : q η ∈ genericPoints β := by
  refine ⟨isIrreducible_singleton.closure, fun S hS hle => ?_⟩
  have hR : Set.range q ⊆ closure {q η} := by
    rintro _ ⟨a, rfl⟩
    have : a ∈ closure ({η} : Set α) := hη ▸ Set.mem_univ a
    exact map_mem_closure hq this fun b hb => by rw [Set.mem_singleton_iff.mp hb]; rfl
  have hne : (S ∩ Set.range q).Nonempty := ⟨q η, hle (subset_closure rfl), η, rfl⟩
  have hS' : S ⊆ closure (S ∩ Set.range q) := by
    intro s hs
    rw [mem_closure_iff]
    intro o ho' hso
    obtain ⟨z, hzS, hzo, hzR⟩ := hS.2 o (Set.range q) ho' ho ⟨s, hs, hso⟩ hne
    exact ⟨z, hzo, hzS, hzR⟩
  calc S ⊆ closure (S ∩ Set.range q) := hS'
    _ ⊆ closure (closure {q η}) := closure_mono (Set.inter_subset_right.trans hR)
    _ = closure {q η} := closure_closure

/-- **The generic point of a normalization component lies on no other component.** It lies over
a generic point `ξ` of the reduced scheme `T`; a component through `ξ` has its generic point at
`ξ`, and the normalization bijects generic points, so the two components coincide. -/
private theorem genericPoint_notMem_iUnion_range {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) [IsReduced T] (i : N.ι) :
    (N.n i).base (genericPoint (N.X i)) ∉ ⋃ (j : N.ι) (_ : j ≠ i), Set.range (N.n j).base := by
  intro hmem
  obtain ⟨j, hji, z, hz⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨φ, hφ⟩ := N.exists_iso
  set ν := slcCurveNormalization T hT
  have hbir : IsBirational ν := Scheme.isBirational_normalization T hT
  have hn : ∀ k, N.n k = Limits.Sigma.ι N.X k ≫ φ.hom ≫ ν := fun k => by
    rw [hφ, Limits.Sigma.ι_desc]
  have hp : ∀ k, (Limits.Sigma.ι N.X k ≫ φ.hom).base (genericPoint (N.X k)) ∈
      genericPoints (Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT) := fun k =>
    mem_genericPoints_of_isOpen_range (Limits.Sigma.ι N.X k ≫ φ.hom).continuous
      (Limits.Sigma.ι N.X k ≫ φ.hom).isOpenEmbedding.isOpen_range
      (genericPoint_spec (N.X k)).def
  have hνk : ∀ k, ν.base ((Limits.Sigma.ι N.X k ≫ φ.hom).base (genericPoint (N.X k))) =
      (N.n k).base (genericPoint (N.X k)) := fun k => by
    rw [hn k]; rfl
  have hξ : (N.n i).base (genericPoint (N.X i)) ∈ genericPoints T :=
    hνk i ▸ hbir.bijOn.mapsTo (hp i)
  have hj : (N.n j).base (genericPoint (N.X j)) = (N.n i).base (genericPoint (N.X i)) := by
    refine eq_of_specializes_of_mem_genericPoints ?_ hξ
    rw [← hz]
    exact ((genericPoint_spec (N.X j)).specializes (Set.mem_univ z)).map (N.n j).continuous
  have heq := hbir.bijOn.injOn (hp j) (hp i) ((hνk j).trans (hj.trans (hνk i).symm))
  simp only [Scheme.Hom.comp_apply] at heq
  have heq' := φ.hom.homeomorph.injective heq
  rw [← sigmaMk_mk, ← sigmaMk_mk] at heq'
  exact hji (congrArg Sigma.fst ((sigmaMk N.X).injective heq'))

/-- Local generators of the adjoint of an sdlt pair restrict to smaller opens. -/
private theorem isAdjointGeneratorOn_mono {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n m : ℕ} {Θ : ∀ i, QDivisor (N.X i)} {U U' : T.Opens}
    (hU : U' ≤ U) {g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hg : IsAdjointGeneratorOn N n m Θ U g) : IsAdjointGeneratorOn N n m Θ U' g :=
  ⟨fun i => (hg.1 i).mono fun _ hz => hU hz,
    fun i j Q Q' e₁ e₂ e₃ e₄ => hg.2 i j Q Q' e₁ (hU e₂) e₃ e₄⟩

/-- **Local generators of the adjoint of an sdlt surface with normal components are unique up to
units**: two local generators `g, g'` on `U` satisfy `g = ν^*e · g'` for a unit `e` of `𝒪_T(U)`. -/
private theorem exists_unit_smul_eq_of_isAdjointGeneratorOn
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
    (hci : ∀ i, IsClosedImmersion (N.n i)) {m : ℕ} {U : T.Opens}
    {g g' : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m}
    (hg : IsAdjointGeneratorOn N 2 m Θ U g) (hg' : IsAdjointGeneratorOn N 2 m Θ U g') :
    ∃ e : Γ(T, U), IsUnit e ∧ ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e) • g' i := by
  classical
  obtain ⟨⟨-, hft, -⟩, hred, -⟩ := h.isNFold
  haveI := hred
  haveI : LocallyOfFiniteType sT := hft
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI := finite_ι h
  have hgen := genericPoint_notMem_iUnion_range N
  choose KN hKN using h.exists_isDltPair
  have hdim : ∀ i, topologicalKrullDim (N.X i) = (2 : ℕ) := fun i => by
    exact_mod_cast (hKN i).1.2.1.topologicalKrullDim_eq
  have hΘ : ∀ i (Q : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base Q.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
        (Θ i).coeff Q = 1 := by
    intro i Q hQ
    rw [h.isAdjointBoundary i Q, adjointBoundaryCoeff, if_pos hQ, Finset.sum_eq_zero,
      add_zero]
    intro Γ hΓ
    rw [if_neg]
    intro h'
    exact h.genericPoint_not_mem_doubleIntersectionLocus Γ hΓ (h' ▸ hQ)
  obtain ⟨e₁, he₁⟩ := exists_smul_eq_of_isAdjointGeneratorOn N h.satisfiesS2
    h.isSeminormal hci hgen hdim hΘ hg hg'
  obtain ⟨e₂, he₂⟩ := exists_smul_eq_of_isAdjointGeneratorOn N h.satisfiesS2
    h.isSeminormal hci hgen hdim hΘ hg' hg
  have h12 : e₁ * e₂ = 1 := by
    refine sub_eq_zero.mp (eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_)
    have h3 := he₁ i hi
    rw [he₂ i hi, smul_smul] at h3
    have h0 : (((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e₁) *
        ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U e₂) - 1) • g i = 0 := by
      rw [sub_smul, ← h3, one_smul, sub_self]
    rw [map_sub, map_mul, map_one, map_sub, map_mul, map_one]
    exact (smul_eq_zero.mp h0).resolve_right (hg.1 i).1
  exact ⟨e₁, IsUnit.of_mul_eq_one _ h12, he₁⟩

private theorem solution :
    ∀ {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
      {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
      {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
      {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
      (hci : ∀ i, IsClosedImmersion (N.n i))
      [inst1 : ∀ i, QuasiCompact (N.n i ≫ sT)] [inst2 : ∀ i, CompactSpace (N.X i)]
      {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
      (f : T ⟶ Z) (hf : f ≫ sZ = sT)
      {K : ∀ i, Divisor (N.X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (N.n i ≫ sT) 2)
      (hnef : ∀ i, (Divisor.toQDivisor (K i) + Θ i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ f))
      {A : ∀ i, QDivisor (N.X i)} (hA : ∀ i, 0 ≤ A i) (hAq : ∀ i, (A i).IsQCartier)
      {G : ∀ i, QDivisor (N.X i)}
      (hDG : ∀ i, (Divisor.toQDivisor (K i) + Θ i + A i).QLinearlyEquivalent (G i))
      (M : Z.Modules) [inst3 : Stacks.Ample.IsInvertibleModule Z M]
      (hGM : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (N.X i), Divisor.toQDivisor L = (m : ℤ) • G i ∧
        Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (N.n i ≫ f)).obj M)),
      ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
        (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m),
        (∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
          (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m), IsAdjointGeneratorOn N 2 m Θ U g) ∧
        ∀ (U : T.Opens), U ≤ f ⁻¹ᵁ V → ∀ g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m,
          IsAdjointGeneratorOn N 2 m Θ U g →
          ∀ y ∈ U, ∃ (U' : T.Opens) (_ : y ∈ U') (_ : U' ≤ U) (a : Γ(T, U')),
            (y = x → IsUnit a) ∧
            ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
              t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
                ((N.n i).app U' a) • g i := by
  intro T sT hT N Δ Θ h hci _ _ Z sZ hZ f hf K hK hnef A hA hAq G hDG M _ hGM
  haveI : IsLocallyNoetherian T := by
    obtain ⟨⟨-, hft, -⟩, -⟩ := h.isNFold
    exact LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : IsIntegral Z := hZ.toIsVariety.toIsIntegral
  have hsemiZ := isRelativelySemiample_normalization h hZ f hf hK hnef hA hAq hDG M hGM
  obtain ⟨H, c, hH, -, hc, -, HT, HN, hHT, hHN, Δ', Θ', -, hΘ', h', hsemi'⟩ :=
    h.exists_isSdltAdjointPair_add_pullback N sZ hZ.isProjective f hf
      (fun i K' hK' => hsemiZ i K' hK') 1 one_pos
  obtain ⟨m₁, hm₁, hgen⟩ := exists_isGloballyGeneratedAdjoint h' fun i K' hK' => (hsemi' i K' hK').1
  refine ⟨m₁ * c.den, Nat.mul_pos hm₁ c.den_pos, fun m hm hdvd x => ?_⟩
  have hcm : ((m : ℚ) * c).den = 1 := by
    obtain ⟨k, rfl⟩ := hdvd
    push_cast
    rw [show (m₁ : ℚ) * c.den * k * c = ((m₁ * k : ℕ) : ℚ) * (c.den * c) by push_cast; ring,
      Rat.den_mul_eq_num, show ((m₁ * k : ℕ) : ℚ) * c.num = ((m₁ * k * c.num : ℤ) : ℚ) by
        push_cast; ring]
    exact Rat.den_intCast _
  obtain ⟨V, hxV, t, ht⟩ := untwist h f hH hHN hc hΘ' hcm
    (hgen m hm ((dvd_mul_right _ _).trans hdvd)) x
  refine ⟨V, hxV, t, fun y hy => ?_, fun U hUV g hg y hyU => ?_⟩
  · obtain ⟨U, hyU, hUV, g, -, hg, -⟩ := ht y hy
    exact ⟨U, hyU, hUV, g, hg⟩
  · obtain ⟨U₀, hyU₀, -, g₀, a₀, hg₀, ha₀, hta₀⟩ := ht y (hUV hyU)
    let U' : T.Opens := U ⊓ U₀
    have hU'U : U' ≤ U := inf_le_left
    have hU'U₀ : U' ≤ U₀ := inf_le_right
    obtain ⟨e, he, hge⟩ := exists_unit_smul_eq_of_isAdjointGeneratorOn h hci
      (isAdjointGeneratorOn_mono hU'U₀ hg₀) (isAdjointGeneratorOn_mono hU'U hg)
    refine ⟨U', ⟨hyU, hyU₀⟩, hU'U, T.presheaf.map (homOfLE hU'U₀).op a₀ * e,
      fun hyx => ((ha₀ hyx).map _).mul he, fun i hi => ?_⟩
    have hi₀ : Nonempty (N.n i ⁻¹ᵁ U₀) := by
      obtain ⟨⟨z, hz⟩⟩ := hi
      exact ⟨⟨z, hU'U₀ hz⟩⟩
    rw [hta₀ i hi₀, hge i hi, smul_smul, map_mul, map_mul,
      germToFunctionField_app_map (N.n i) hU'U₀ a₀]

end Proof_thm_mmp_surface_complemented_sdlt_relative_abundance

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Complemented relative abundance for projective sdlt surfaces.** Let `(T, Δ; L)` be a
projective sdlt adjoint pair of dimension two over `ℂ` (`MMP.Fourfold.IsSdltAdjointPair`) with
normal irreducible components `νᵢ : Tᵢ ⟶ T` (closed immersions) and boundaries `Θᵢ`, canonical
divisors `Kᵢ` of the `Tᵢ`, and `f : T ⟶ Z` a morphism to a projective complex variety. Suppose `L`
is `f`-nef, i.e. every `Kᵢ + Θᵢ` is `(νᵢ ≫ f)`-nef, and that `L + A ∼_ℚ f^*H` with `A` effective
rational Cartier: there are effective `ℚ`-Cartier `Aᵢ` on the `Tᵢ`, `ℚ`-divisors
`Gᵢ ∼_ℚ Kᵢ + Θᵢ + Aᵢ`, an invertible `𝒪_Z`-module `M` and `m > 0` with `𝒪_{Tᵢ}(mGᵢ) ≅ (νᵢ ≫ f)^*M`
for every `i`. Then `L` is `f`-semiample: there is `m₀ > 0` such that for every positive multiple
`m` of `m₀` and every `x ∈ T` there are an open `V ∋ f(x)` of `Z` and a section `t` of `𝒪_T(mL)`
over `f⁻¹(V)` generating `𝒪_T(mL)` at `x`: `𝒪_T(mL)` has local generators near every point of
`f⁻¹(V)`, and for every local generator `g` of `𝒪_T(mL)` on an open `U ⊆ f⁻¹(V)`
(`MMP.Fourfold.IsAdjointGeneratorOn`), near each point `y ∈ U` the section `t` is `ν^*a · g` for a
function `a`, a unit when `y = x`. -/
@[mmp "thm_mmp_surface_complemented_sdlt_relative_abundance"]
public theorem IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_add_qLinearlyEquivalent
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N 2 Δ Θ)
    (hci : ∀ i, IsClosedImmersion (N.n i))
    [∀ i, QuasiCompact (N.n i ≫ sT)] [∀ i, CompactSpace (N.X i)]
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : Mori.IsProjectiveVariety ℂ sZ)
    (f : T ⟶ Z) (hf : f ≫ sZ = sT)
    {K : ∀ i, Divisor (N.X i)} (hK : ∀ i, (K i).IsCanonicalDivisor (N.n i ≫ sT) 2)
    (hnef : ∀ i, (Divisor.toQDivisor (K i) + Θ i).IsRelativelyNef (N.n i ≫ sT) (N.n i ≫ f))
    {A : ∀ i, QDivisor (N.X i)} (hA : ∀ i, 0 ≤ A i) (hAq : ∀ i, (A i).IsQCartier)
    {G : ∀ i, QDivisor (N.X i)}
    (hDG : ∀ i, (Divisor.toQDivisor (K i) + Θ i + A i).QLinearlyEquivalent (G i))
    (M : Z.Modules) [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (N.X i), Divisor.toQDivisor L = (m : ℤ) • G i ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (N.n i ≫ f)).obj M)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, 0 < m → m₀ ∣ m → ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m),
      (∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m), IsAdjointGeneratorOn N 2 m Θ U g) ∧
      ∀ (U : T.Opens), U ≤ f ⁻¹ᵁ V → ∀ g : ∀ i, RationalPluriForms (N.n i ≫ sT) 2 m,
        IsAdjointGeneratorOn N 2 m Θ U g →
        ∀ y ∈ U, ∃ (U' : T.Opens) (_ : y ∈ U') (_ : U' ≤ U) (a : Γ(T, U')),
          (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' a) • g i :=
              by revert T sT hT N Δ Θ h hci Z sZ hZ f hf K hK hnef A hA hAq G hDG M hGM; first | exact Proof_thm_mmp_surface_complemented_sdlt_relative_abundance.solution | exact Proof_thm_mmp_surface_complemented_sdlt_relative_abundance.solution _ | exact Proof_thm_mmp_surface_complemented_sdlt_relative_abundance.solution _ _ | exact Proof_thm_mmp_surface_complemented_sdlt_relative_abundance.solution _ _ _ | exact Proof_thm_mmp_surface_complemented_sdlt_relative_abundance.solution _ _ _ _

end MMP.Fourfold

