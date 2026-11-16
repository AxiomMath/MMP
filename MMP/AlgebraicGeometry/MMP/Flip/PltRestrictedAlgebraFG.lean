module

public import MMP.AlgebraicGeometry.MMP.Flip.RestrictedAlgebraFG
public import MMP.AlgebraicGeometry.Singularities.PltTerminalRestriction
public import MMP.AlgebraicGeometry.SpreadingOut.LocalEquations
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberSNC
public import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
public import MMP.AlgebraicGeometry.Divisor.SectionZeroDivisor
public import MMP.AlgebraicGeometry.MMP.Abundance.NumericalDimensionOnePencil

section

/-!
# Finite generation of a plt restricted adjoint algebra with an ample boundary

The restricted algebra of a Cartier multiple `D = q(K_X + S + B + A)` along `S` is finitely
generated over `Γ(Z, 𝒪_Z)`. The proof passes to a log resolution on which the strict transform
of `S` is smooth with a terminal restricted boundary, replaces `A` by a general ample boundary
in the same `ℚ`-linear class, applies finite generation for prepared restricted algebras, and
transports the result back through a Veronese subalgebra.

## References

* [C. Hacon, J. McKernan, *Extension theorems and the existence of flips*][HaconMcKernan2007]
-/

open CategoryTheory AlgebraicGeometry Polynomial

namespace MMP.FourfoldProofs.FourfoldPreparePltRestrictedAlgebraProof

open MMP.Mori MMP.Fourfold
open scoped Topology

/-- `div(φⁿ) = n · div(φ)`. -/
private theorem principalDivisor_zpow {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (φ : (RationalFunctions X)ˣ) (n : ℤ) :
    MMP.Mori.principalDivisor (φ ^ n) = n • MMP.Mori.principalDivisor φ := by
  refine Finsupp.ext fun P => ?_
  change (MMP.Mori.principalDivisor (φ ^ n)).coeff P = (n • MMP.Mori.principalDivisor φ).coeff P
  rw [DivisorWithCoeffs.coeff_smul, MMP.Mori.coeff_principalDivisor, MMP.Mori.coeff_principalDivisor,
    MMP.Mori.PrimeDivisor.ord_zpow, smul_eq_mul]

/-- The restriction algebra of the zero divisor along `S` is generated over `Γ(X, 𝒪_X)` by `t`. -/
private theorem finiteType_weilRestriction_zero
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (S : MMP.Mori.PrimeDivisor X) (B : Divisor X) (hB0 : B = 0) (hS : B.coeff S = 0) :
    ((weilRestrictionMap hS).rangeRestrict.comp
      ((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict (weilSectionAlgebra B)
        (fun s => Subring.mem_comap.mp
          ((comap_C_weilSectionAlgebra B).ge ⟨s, rfl⟩)))).FiniteType := by
  subst hB0
  set ι := (C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict
    (weilSectionAlgebra 0)
    (fun s => Subring.mem_comap.mp ((comap_C_weilSectionAlgebra 0).ge ⟨s, rfl⟩)) with hι
  letI := ((weilRestrictionMap hS).rangeRestrict.comp ι).toAlgebra
  have hXmem : (Polynomial.X : (RationalFunctions X)[X]) ∈ weilSectionAlgebra (0 : Divisor X) := by
    have h := (monomial_mem_weilSectionAlgebra (B := (0 : Divisor X)) (m := 1)
      (g := 1)).mpr (by rw [smul_zero]; exact one_mem_divisorialSections le_rfl)
    rwa [monomial_one_one_eq_X] at h
  set x : weilSectionAlgebra (0 : Divisor X) := ⟨Polynomial.X, hXmem⟩ with hx
  refine ⟨⟨{(weilRestrictionMap hS).rangeRestrict x}, ?_⟩⟩
  rw [Finset.coe_singleton, eq_top_iff]
  intro r _
  obtain ⟨p, hp⟩ := r.2
  have hr : r = (weilRestrictionMap hS).rangeRestrict p := Subtype.ext hp.symm
  rw [hr]
  have hc : ∀ m, ∃ s : Γ(X, ⊤), globalSectionsToRationalFunctions s =
      (p : (RationalFunctions X)[X]).coeff m := by
    intro m
    have := p.2 m
    rw [smul_zero, mem_divisorialSections_zero_iff] at this
    exact this
  choose s hs using hc
  have hpsum : p = ∑ m ∈ (p : (RationalFunctions X)[X]).support, ι (s m) * x ^ m := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    conv_lhs => rw [as_sum_support_C_mul_X_pow (p : (RationalFunctions X)[X])]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, hι, RingHom.codRestrict_apply,
      RingHom.comp_apply, hs]
  rw [hpsum, map_sum]
  refine Subalgebra.sum_mem _ fun m _ => ?_
  rw [map_mul, map_pow, ← RingHom.comp_apply (weilRestrictionMap hS).rangeRestrict ι,
    ← RingHom.algebraMap_toAlgebra ((weilRestrictionMap hS).rangeRestrict.comp ι)]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _)

/-- **A finite normal affine model under a projective variety over an affine base.** Let
`p : V ⟶ Z` be a projective morphism from a normal complex variety to a normal affine complex
variety such that every rational function on `V` is a quotient of two functions pulled back from
`Z`. Then the Stein factorization `V ⟶ W ⟶ Z` of `p` has `W` a normal affine variety, `W ⟶ Z`
finite and `V ⟶ W` projective and birational. -/
private theorem exists_finite_normal_affine_model {Z V : Scheme.{0}} [IsAffine Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {sV : V ⟶ Spec (.of ℂ)}
    (hV : IsNormalVariety ℂ sV) (p : V ⟶ Z) (hp : p ≫ sZ = sV) (hpp : IsProjectiveMorphism p)
    (hgen : haveI := hV.1.toIsIntegral
      ∀ x : V.functionField, ∃ a b : Γ(Z, ⊤),
        V.germToFunctionField ⊤ (p.appTop b) ≠ 0 ∧
          x * V.germToFunctionField ⊤ (p.appTop b) = V.germToFunctionField ⊤ (p.appTop a)) :
    ∃ (W : Scheme.{0}) (κ : W ⟶ Z) (h : V ⟶ W), IsFinite κ ∧ IsNormalVariety ℂ (κ ≫ sZ) ∧
      IsAffine W ∧ h ≫ κ = p ∧ IsProjectiveMorphism h ∧ IsBirationalMorphism h := by
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : IsNormal V := hV.2
  haveI : AlgebraicGeometry.IsVariety ℂ sV := hV.1
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpp
  obtain ⟨W, h, κ, ⟨hS⟩, hP, hsurj, -, -, hfin, hvar, -, hnorm, hproj, -⟩ :=
    MMP.Resolution.Bridges.exists_steinFactorization_of_isVariety sV sZ p hp
  haveI := hfin
  haveI : IsAffine W := isAffine_of_isAffineHom κ
  haveI : IsIntegral W := hvar.toIsIntegral
  haveI := hsurj
  haveI := hP
  haveI : IsDominant h := inferInstance
  refine ⟨W, κ, h, hfin, ⟨hvar, hnorm hV.2⟩, inferInstance, hS.comp, hproj hpp, ?_⟩
  have hρ : ∀ c : Γ(Z, ⊤), functionFieldMap h (W.germToFunctionField ⊤ (κ.appTop c)) =
      V.germToFunctionField ⊤ (p.appTop c) := by
    intro c
    rw [MMP.Spreading.functionFieldMap_germToFunctionField h ⊤ ⊤ le_top, ← hS.comp,
      Scheme.Hom.comp_appTop, show h.appLE ⊤ ⊤ le_top = h.appTop from
        (Scheme.Hom.app_eq_appLE h).symm]
    rfl
  have hsurjF : Function.Surjective (functionFieldMap h) := by
    intro x
    obtain ⟨a, b, hb0, hab⟩ := hgen x
    refine ⟨W.germToFunctionField ⊤ (κ.appTop a) / W.germToFunctionField ⊤ (κ.appTop b), ?_⟩
    rw [map_div₀, hρ, hρ, ← hab, mul_div_cancel_right₀ _ hb0]
  have hbij : Function.Bijective (functionFieldMap h) :=
    ⟨(functionFieldMap h).injective, hsurjF⟩
  have hη : h (genericPoint V) = genericPoint W := map_genericPoint_of_isDominant h
  have hbir : AlgebraicGeometry.IsBirational h := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hη]
      exact Set.bijOn_singleton.mpr rfl
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      have : IsIso ((W.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
          h.stalkMap (genericPoint V)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hbij
      exact IsIso.of_isIso_comp_left (W.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom _
  haveI : Finite (irreducibleComponents V) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
  obtain ⟨U, U', hUU', hU, hU', hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational h hbir (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE h U U' hU.nonempty hU'.nonempty hUU' hiso

/-! ### Sections of divisorial sheaves and their pull-backs -/

section Sections

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A unit `φ` of `K(X)` is a section of `𝒪_X(D)` exactly when `div φ + D ≥ 0`. -/
private theorem coe_mem_divisorialSections_iff {D : Divisor X} (φ : (RationalFunctions X)ˣ) :
    (φ : RationalFunctions X) ∈ divisorialSections D ↔
      ∀ P : MMP.Mori.PrimeDivisor X, -D.coeff P ≤ P.ord φ := by
  rw [mem_divisorialSections]
  have hne : ∀ P : MMP.Mori.PrimeDivisor X, (φ : RationalFunctions X) P.component ≠ 0 :=
    fun P => (φ.isUnit.map (Pi.evalRingHom _ P.component)).ne_zero
  constructor
  · intro h P
    have hP := h P ⟨P.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P,
      trivial⟩
    change P.OrdGE _ ((φ : RationalFunctions X) P.component) at hP
    rcases hP with h0 | hv
    · exact absurd h0 (hne P)
    · rwa [P.valuation_component φ, WithZero.exp_le_exp] at hv
  · intro h P _
    change P.OrdGE _ ((φ : RationalFunctions X) P.component)
    exact Or.inr (by rw [P.valuation_component φ, WithZero.exp_le_exp]; exact h P)

/-- A nonzero rational function lies in `H⁰(X, 𝒪_X(D))` exactly when `div g + D ≥ 0`. -/
private theorem mem_sectionsIn_iff {D : Divisor X} {g : X.functionField} (hg : g ≠ 0) :
    g ∈ sectionsIn D ↔ ∀ P : MMP.Mori.PrimeDivisor X, -D.coeff P ≤ X.ord g P.genericPoint := by
  change (∀ P : MMP.Mori.PrimeDivisor X, _) ↔ _
  refine forall_congr' fun P => ?_
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord P hg, WithZero.exp_le_exp, neg_le]

/-- The two descriptions of `H⁰(X, 𝒪_X(D))`, in `K(X)` and in `k(X)`, agree on units. -/
private theorem coe_mem_divisorialSections_iff_mem_sectionsIn {D : Divisor X}
    (φ : (RationalFunctions X)ˣ) :
    (φ : RationalFunctions X) ∈ divisorialSections D ↔
      rationalFunctionsEquivFunctionField X φ ∈ sectionsIn D := by
  have hne : rationalFunctionsEquivFunctionField X φ ≠ 0 :=
    (φ.isUnit.map (rationalFunctionsEquivFunctionField X)).ne_zero
  rw [coe_mem_divisorialSections_iff, mem_sectionsIn_iff hne]
  simp only [MMP.Mori.PrimeDivisor.ord_eq_ord_rationalFunctionsEquivFunctionField]

end Sections

section Pullbacks

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- **The pull-back of an effective Cartier divisor is effective.** -/
private theorem nonneg_of_isPullback {f : Y ⟶ X} {B : Divisor X} (hBc : B.IsCartier)
    (hB0 : 0 ≤ B) {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (h : B.IsPullback f hB B') : 0 ≤ B' := by
  intro E
  change 0 ≤ B'.coeff E
  obtain ⟨U, hyU, φ, hφ⟩ := hBc (f E.genericPoint)
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hyU
  rw [h U φ hφ E hE]
  set W := pointComponent (f (componentGenericPoint Y E.component))
  have hW : f (componentGenericPoint Y E.component) ∈ W.1 := mem_pointComponent _
  have hsp : componentGenericPoint Y E.component ⤳ E.genericPoint := E.specializes_genericPoint
  have hsp' : f (componentGenericPoint Y E.component) ⤳ f E.genericPoint :=
    f.base.hom.map_specializes hsp
  have hyW : f E.genericPoint ∈ W.1 :=
    hsp'.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) hW
  obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hyW φ fun Γ hΓ => by
    rw [← hφ Γ ⟨_, hΓ, hyU⟩]
    exact hB0 Γ
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk (E.map_componentGenericPoint_mem f hE) (hB _) hW
  rw [pullbackComponent_eq hB hφ _ hW a ha]
  have har : (a : X.presheaf.stalk _) = (X.presheaf.stalkSpecializes hsp').hom r := by
    apply stalkToRationalFunctions_injective hW
    rw [ha, ← hr]
    change _ = (X.presheaf.stalkSpecializes hsp' ≫ X.presheaf.stalkSpecializes _).hom r
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  set s := (f.stalkMap E.genericPoint).hom r with hsdef
  have hu : ((Units.map (f.stalkMap (componentGenericPoint Y E.component)).hom.toMonoidHom a :
      (Y.presheaf.stalk _)ˣ) : Y.presheaf.stalk _) = E.toComponent.hom s := by
    change (f.stalkMap (componentGenericPoint Y E.component)).hom (a : X.presheaf.stalk _) = _
    rw [har, Scheme.Hom.stalkSpecializes_stalkMap_apply]
    rfl
  have hs0 : s ≠ 0 := by
    intro h0
    have := (Units.map (f.stalkMap (componentGenericPoint Y E.component)).hom.toMonoidHom
      a).ne_zero
    rw [hu, h0, map_zero] at this
    exact this rfl
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hval := E.valuation_eq_exp_ordUnit
    (Units.map (f.stalkMap (componentGenericPoint Y E.component)).hom.toMonoidHom a)
  rw [hu, hv, map_mul, map_pow, map_mul, map_pow, E.valuation_toComponent_of_isUnit v.isUnit,
    E.valuation_toComponent_of_irreducible hϖ, one_mul, ← WithZero.exp_nsmul,
    WithZero.exp_inj] at hval
  rw [← hval]
  positivity

/-- **Sections along a proper birational morphism.** Let `μ : Y ⟶ X` be a proper birational
morphism of normal varieties, `B` a Cartier divisor on `X` with pull-back `B'`, and `E'` an
effective divisor on `Y` none of whose components lies over a prime divisor of `X`. A unit `φ` of
`K(X)` is a section of `𝒪_X(B)` exactly when `μ^*φ` is a section of `𝒪_Y(B' + E')`. -/
private theorem coe_mem_divisorialSections_iff_pullback {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {μ : Y ⟶ X}
    (hY : IsNormalVariety k (μ ≫ sX)) [IsProper μ] (hμ : IsBirationalMorphism μ)
    {B : Divisor X} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (hpb : B.IsPullback μ hB B') {E' : Divisor Y} (hE' : 0 ≤ E')
    (hEx : ∀ P : MMP.Mori.PrimeDivisor Y, E'.coeff P ≠ 0 →
      ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint)
    (φ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor φ).supp) :
    (φ : RationalFunctions X) ∈ divisorialSections B ↔
      (pullbackRationalFunction μ φ hφ : RationalFunctions Y) ∈ divisorialSections (B' + E') := by
  haveI : IsDominant μ := hμ.isDominant
  rw [coe_mem_divisorialSections_iff, coe_mem_divisorialSections_iff]
  have hsum : (MMP.Mori.principalDivisor φ + B).IsPullback μ
      (fun Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' μ _ Z)
      (MMP.Mori.principalDivisor (pullbackRationalFunction μ φ hφ) + B') :=
    Divisor.IsPullback.add (Divisor.isCartier_principalDivisor φ) hBc _
      (Divisor.isPullback_principalDivisor φ hφ) hpb
  constructor
  · intro h P
    have h0 : 0 ≤ MMP.Mori.principalDivisor φ + B := fun Γ => by
      change 0 ≤ (MMP.Mori.principalDivisor φ + B).coeff Γ
      rw [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor]
      linarith [h Γ]
    have h1 := nonneg_of_isPullback ((Divisor.isCartier_principalDivisor φ).add hBc) h0 hsum P
    have h2 := hE' P
    change 0 ≤ (MMP.Mori.principalDivisor _ + B').coeff P at h1
    change 0 ≤ E'.coeff P at h2
    rw [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor] at h1
    rw [DivisorWithCoeffs.coeff_add]
    linarith
  · intro h Γ
    obtain ⟨P, heq, hiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hY hμ Γ
    haveI := hiso
    have hc := MMP.Positivity.coeff_eq_of_isPullback P Γ heq
      ((Divisor.isCartier_principalDivisor φ).add hBc) hsum
    have hE0 : E'.coeff P = 0 := by
      by_contra hne
      exact hEx P hne Γ heq
    have h1 := h P
    rw [DivisorWithCoeffs.coeff_add, hE0, add_zero] at h1
    rw [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor, DivisorWithCoeffs.coeff_add,
      MMP.Mori.coeff_principalDivisor] at hc
    linarith

/-- **The restriction to a prime divisor of a function regular along it.** -/
private theorem isRestrictionAlong_stalkSpecializes_iff {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (T : MMP.Mori.PrimeDivisor Y)
    (b : Y.presheaf.stalk (T.idealSheaf.subschemeι
      (haveI := T.integral; genericPoint T.idealSheaf.subscheme)))
    (h : haveI := T.integral; T.idealSheaf.subscheme.functionField) :
    haveI := T.integral
    IsRestrictionAlong T (Y.presheaf.stalkSpecializes (genericPoint_specializes _) b) h ↔
      h = (T.idealSheaf.subschemeι.stalkMap (genericPoint T.idealSheaf.subscheme)).hom b := by
  haveI := T.integral
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hinj : Function.Injective (algebraMap (Y.presheaf.stalk (T.idealSheaf.subschemeι
        (genericPoint T.idealSheaf.subscheme))) Y.functionField) :=
      IsFractionRing.injective _ _
    rw [hinj (ha.trans rfl)]
  · rintro rfl
    exact ⟨b, rfl, rfl⟩

/-- Multiplying a section by a unit `θ` shifts the divisor by `div θ`. -/
private theorem coe_mul_mem_divisorialSections_iff {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : Divisor X}
    (φ θ : (RationalFunctions X)ˣ) :
    ((φ * θ : (RationalFunctions X)ˣ) : RationalFunctions X) ∈ divisorialSections D ↔
      (φ : RationalFunctions X) ∈ divisorialSections (D + MMP.Mori.principalDivisor θ) := by
  rw [coe_mem_divisorialSections_iff, coe_mem_divisorialSections_iff]
  refine forall_congr' fun P => ?_
  rw [MMP.Mori.PrimeDivisor.ord_mul, DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor]
  constructor <;> intro h <;> linarith

end Pullbacks

/-! ### The residue field of `X` along `S` is the function field of its strict transform -/

section ResidueField

variable {X Y : Scheme.{0}} (μ : Y ⟶ X) (S : MMP.Mori.PrimeDivisor X) (T : MMP.Mori.PrimeDivisor Y)
  [IsIntegral T.idealSheaf.subscheme]
  (hTS : μ T.genericPoint = S.genericPoint) [IsIso (μ.stalkMap T.genericPoint)]

/-- The restriction `𝒪_{X,η_S} ≅ 𝒪_{Y,η_T} → k(T)` to the strict transform `T` of `S`. -/
private noncomputable def restrictionToStrictTransform :
    X.presheaf.stalk S.genericPoint →+*
      T.idealSheaf.subscheme.functionField :=
  (T.idealSheaf.subschemeι.stalkMap (genericPoint T.idealSheaf.subscheme)).hom.comp <|
    (Y.presheaf.stalkCongr (Inseparable.of_eq (rfl : T.genericPoint =
      T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme)))).hom.hom.comp <|
      (μ.stalkMap T.genericPoint).hom.comp
        (X.presheaf.stalkCongr (Inseparable.of_eq hTS.symm)).hom.hom

private theorem restrictionToStrictTransform_surjective :
    Function.Surjective (restrictionToStrictTransform μ S T hTS) := by
  refine (T.idealSheaf.subschemeι.stalkMap_surjective _).comp ?_
  refine (ConcreteCategory.bijective_of_isIso
    (Y.presheaf.stalkCongr _).hom).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso (μ.stalkMap T.genericPoint)).2.comp ?_
  exact (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkCongr _).hom).2

/-- `κ(η_S) ≅ k(T)` for the strict transform `T` of `S`. -/
private noncomputable def residueFieldEquiv :
    X.residueField S.genericPoint ≃+*
      T.idealSheaf.subscheme.functionField :=
  have hker : IsLocalRing.maximalIdeal (X.presheaf.stalk S.genericPoint) =
      RingHom.ker (restrictionToStrictTransform μ S T hTS) :=
    (IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (restrictionToStrictTransform_surjective μ S T hTS))).symm
  (Ideal.quotEquivOfEq hker).trans
    (RingHom.quotientKerEquivOfSurjective (restrictionToStrictTransform_surjective μ S T hTS))

private theorem residueFieldEquiv_residue (a : X.presheaf.stalk S.genericPoint) :
    residueFieldEquiv μ S T hTS (X.residue S.genericPoint a) =
      restrictionToStrictTransform μ S T hTS a :=
  rfl

/-- The restriction `𝒪_{Y,η_T} → k(T)`. -/
private noncomputable def restrictionAlongT :
    Y.presheaf.stalk T.genericPoint →+*
      T.idealSheaf.subscheme.functionField :=
  (T.idealSheaf.subschemeι.stalkMap (genericPoint T.idealSheaf.subscheme)).hom.comp
    (Y.presheaf.stalkCongr (Inseparable.of_eq (rfl : T.genericPoint =
      T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme)))).hom.hom

omit [IsIso (μ.stalkMap T.genericPoint)] in
private theorem restrictionToStrictTransform_eq (a : X.presheaf.stalk S.genericPoint) :
    restrictionToStrictTransform μ S T hTS a = restrictionAlongT T
      ((μ.stalkMap T.genericPoint).hom ((X.presheaf.stalkCongr (Inseparable.of_eq hTS.symm)).hom a)) :=
  rfl

/-- **The restriction of a pull-back.** Let `φ` be a unit of `K(X)` regular along `S`, the image
of `a ∈ 𝒪_{X,η_S}`, and `θ` a unit of `K(Y)` that is a unit `t` of `𝒪_{Y,η_T}`. The restriction
to `T` of `μ^*φ · θ⁻ʲ` is `a|_T · (t|_T)⁻ʲ`. -/
private theorem isRestrictionAlong_pullback_mul_iff [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsDominant μ]
    (φ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor φ).supp)
    (a : X.presheaf.stalk S.genericPoint)
    (ha : S.toComponent.hom a = (φ : RationalFunctions X) S.component)
    (θ : (RationalFunctions Y)ˣ) (t : (Y.presheaf.stalk T.genericPoint)ˣ)
    (ht : (stalkToRationalFunctions Y T.genericPoint_mem_component).hom t =
      (θ : RationalFunctions Y) T.component) (j : ℕ)
    (h : T.idealSheaf.subscheme.functionField) :
    IsRestrictionAlong T (rationalFunctionsEquivFunctionField Y
        (((pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ j : (RationalFunctions Y)ˣ)) :
          RationalFunctions Y)) h ↔
      h = restrictionToStrictTransform μ S T hTS a * (restrictionAlongT T (t : _))⁻¹ ^ j := by
  set a' := (X.presheaf.stalkCongr (Inseparable.of_eq hTS.symm)).hom a with ha'
  set b : Y.presheaf.stalk T.genericPoint :=
    (μ.stalkMap T.genericPoint).hom a' * ((t⁻¹ : (Y.presheaf.stalk T.genericPoint)ˣ) :
      Y.presheaf.stalk T.genericPoint) ^ j with hb
  have h1 : rationalFunctionsEquivFunctionField X (φ : RationalFunctions X) =
      algebraMap (X.presheaf.stalk S.genericPoint) X.functionField a := by
    rw [← MMP.Positivity.componentToFunctionField_apply S.component, ← ha]
    exact MMP.Mori.algebraMap_stalkSpecializes _ a
  have h2 : algebraMap (X.presheaf.stalk S.genericPoint) X.functionField a =
      algebraMap (X.presheaf.stalk (μ T.genericPoint)) X.functionField a' :=
    (MMP.Mori.algebraMap_stalkSpecializes (Inseparable.of_eq hTS.symm).ge a).symm
  have h3 : rationalFunctionsEquivFunctionField Y (θ : RationalFunctions Y) =
      algebraMap (Y.presheaf.stalk T.genericPoint) Y.functionField (t : _) := by
    rw [← MMP.Positivity.componentToFunctionField_apply T.component, ← ht]
    exact MMP.Mori.algebraMap_stalkSpecializes _ _
  have h3' : rationalFunctionsEquivFunctionField Y ((θ⁻¹ : (RationalFunctions Y)ˣ) :
      RationalFunctions Y) = algebraMap (Y.presheaf.stalk T.genericPoint) Y.functionField
        ((t⁻¹ : (Y.presheaf.stalk T.genericPoint)ˣ) : _) := by
    have hθ0 : rationalFunctionsEquivFunctionField Y (θ : RationalFunctions Y) ≠ 0 :=
      (θ.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
    refine mul_right_cancel₀ hθ0 ?_
    rw [← map_mul, Units.inv_mul, map_one, h3, ← map_mul, Units.inv_mul, map_one]
  have key : rationalFunctionsEquivFunctionField Y
      (((pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ j : (RationalFunctions Y)ˣ)) :
        RationalFunctions Y) = algebraMap (Y.presheaf.stalk T.genericPoint) Y.functionField b := by
    rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow,
      rationalFunctionsEquivFunctionField_pullbackRationalFunction μ φ hφ, h1, h2,
      MMP.Mori.functionFieldMap_algebraMap_stalk μ T.genericPoint a', h3', hb, map_mul, map_pow]
  have hspec : Y.presheaf.stalkSpecializes (genericPoint_specializes _)
      ((Y.presheaf.stalkCongr (Inseparable.of_eq (rfl : T.genericPoint =
        T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme)))).hom b) =
      algebraMap (Y.presheaf.stalk T.genericPoint) Y.functionField b :=
    MMP.Mori.algebraMap_stalkSpecializes (Inseparable.of_eq (rfl : T.genericPoint =
      T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme))).ge b
  rw [key, ← hspec]
  refine (isRestrictionAlong_stalkSpecializes_iff T _ h).trans ?_
  change h = restrictionAlongT T b ↔ _
  rw [hb, map_mul, map_pow, map_units_inv, restrictionToStrictTransform_eq]

omit [IsIso (μ.stalkMap T.genericPoint)] in
/-- The restriction to `T` of (the germ at `η_S` of) a global function of `X`. -/
private theorem restrictionToStrictTransform_germ (s : Γ(X, ⊤)) :
    restrictionToStrictTransform μ S T hTS (X.presheaf.germ ⊤ S.genericPoint trivial s) =
      T.idealSheaf.subscheme.presheaf.germ ⊤ (genericPoint _) trivial
        ((T.idealSheaf.subschemeι ≫ μ).appTop s) := by
  rw [restrictionToStrictTransform_eq]
  have e1 : (X.presheaf.stalkCongr (Inseparable.of_eq hTS.symm)).hom.hom
      ((X.presheaf.germ ⊤ S.genericPoint trivial).hom s) =
      (X.presheaf.germ ⊤ (μ T.genericPoint) trivial).hom s :=
    congrArg (fun φ => φ.hom s)
      (X.presheaf.germ_stalkSpecializes (U := ⊤) trivial (Inseparable.of_eq hTS.symm).ge)
  have e2 : (μ.stalkMap T.genericPoint).hom ((X.presheaf.germ ⊤ (μ T.genericPoint) trivial).hom s)
      = (Y.presheaf.germ (μ ⁻¹ᵁ ⊤) T.genericPoint trivial).hom ((μ.app ⊤).hom s) :=
    Scheme.Hom.germ_stalkMap_apply μ ⊤ T.genericPoint trivial s
  have e3 : restrictionAlongT T ((Y.presheaf.germ (μ ⁻¹ᵁ ⊤) T.genericPoint trivial).hom
      ((μ.app ⊤).hom s)) = (T.idealSheaf.subscheme.presheaf.germ
        (T.idealSheaf.subschemeι ⁻¹ᵁ (μ ⁻¹ᵁ ⊤)) (genericPoint _) trivial).hom
          ((T.idealSheaf.subschemeι.app (μ ⁻¹ᵁ ⊤)).hom ((μ.app ⊤).hom s)) := by
    have e3a : (Y.presheaf.stalkCongr (Inseparable.of_eq (rfl : T.genericPoint =
        T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme)))).hom.hom
          ((Y.presheaf.germ (μ ⁻¹ᵁ ⊤) T.genericPoint trivial).hom ((μ.app ⊤).hom s)) =
        (Y.presheaf.germ (μ ⁻¹ᵁ ⊤) (T.idealSheaf.subschemeι (genericPoint _)) trivial).hom
          ((μ.app ⊤).hom s) :=
      congrArg (fun φ => φ.hom ((μ.app ⊤).hom s))
        (Y.presheaf.germ_stalkSpecializes (U := μ ⁻¹ᵁ ⊤) (y := T.genericPoint)
          (x := T.idealSheaf.subschemeι (genericPoint _)) trivial
          (Inseparable.of_eq (rfl : T.genericPoint =
            T.idealSheaf.subschemeι (genericPoint T.idealSheaf.subscheme))).ge)
    exact (congrArg _ e3a).trans (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _)
  erw [e1, e2, e3]
  rfl

end ResidueField

/-- **The function field of the strict transform comes from the base.** If `S` maps birationally
onto its image in the affine `Z`, every rational function on the strict transform `T` of `S` is a
quotient of two functions pulled back from `Z`. -/
private theorem exists_mul_germ_eq_germ {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsAffine Z] (μ : Y ⟶ X) (f : X ⟶ Z)
    [QuasiCompact f] (S : MMP.Mori.PrimeDivisor X) (T : MMP.Mori.PrimeDivisor Y)
    (hTS : μ T.genericPoint = S.genericPoint) [IsIso (μ.stalkMap T.genericPoint)]
    (hSbir : IsBirationalMorphism (S.idealSheaf.subschemeι ≫ f).toImage) :
    haveI := T.integral
    ∀ x : T.idealSheaf.subscheme.functionField, ∃ a b : Γ(Z, ⊤),
      T.idealSheaf.subscheme.germToFunctionField ⊤
        ((T.idealSheaf.subschemeι ≫ μ ≫ f).appTop b) ≠ 0 ∧
      x * T.idealSheaf.subscheme.germToFunctionField ⊤
        ((T.idealSheaf.subschemeι ≫ μ ≫ f).appTop b) =
        T.idealSheaf.subscheme.germToFunctionField ⊤
          ((T.idealSheaf.subschemeι ≫ μ ≫ f).appTop a) := by
  haveI := T.integral
  haveI := S.integral
  set φS := S.idealSheaf.subschemeι ≫ f with hφS
  have hbij := hSbir.functionFieldMap_bijective
  obtain ⟨hIa, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine φS.imageι
  haveI := hIa
  haveI : IsIso (Scheme.Hom.stalkMap (𝟙 X) S.genericPoint) := inferInstance
  set ΦS := residueFieldEquiv (𝟙 X) S S rfl
  set ΦT := residueFieldEquiv μ S T hTS
  set Ψ := ΦS.symm.trans ΦT with hΨ
  have hΨg : ∀ s : Γ(X, ⊤), Ψ (S.idealSheaf.subscheme.germToFunctionField ⊤
      ((S.idealSheaf.subschemeι ≫ 𝟙 X).appTop s)) =
      T.idealSheaf.subscheme.germToFunctionField ⊤ ((T.idealSheaf.subschemeι ≫ μ).appTop s) := by
    intro s
    have h1 : ΦS (X.residue S.genericPoint (X.presheaf.germ ⊤ S.genericPoint trivial s)) =
        S.idealSheaf.subscheme.germToFunctionField ⊤ ((S.idealSheaf.subschemeι ≫ 𝟙 X).appTop s) :=
      (residueFieldEquiv_residue (𝟙 X) S S rfl _).trans
        (restrictionToStrictTransform_germ (𝟙 X) S S rfl s)
    have h2 : ΦT (X.residue S.genericPoint (X.presheaf.germ ⊤ S.genericPoint trivial s)) =
        T.idealSheaf.subscheme.germToFunctionField ⊤ ((T.idealSheaf.subschemeι ≫ μ).appTop s) :=
      (residueFieldEquiv_residue μ S T hTS _).trans (restrictionToStrictTransform_germ μ S T hTS s)
    rw [← h1, ← h2, hΨ, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  intro x
  obtain ⟨w, hw⟩ := hbij.2 (Ψ.symm x)
  have := functionField_isFractionRing_of_isAffineOpen φS.image ⊤ (isAffineOpen_top _)
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := Γ(φS.image, ⊤)) w
  obtain ⟨a, rfl⟩ := hsurj α
  obtain ⟨b, rfl⟩ := hsurj β
  have hgerm : ∀ c : Γ(Z, ⊤), functionFieldMap φS.toImage
      (algebraMap Γ(φS.image, ⊤) φS.image.functionField (φS.imageι.appTop c)) =
      S.idealSheaf.subscheme.germToFunctionField ⊤ ((S.idealSheaf.subschemeι ≫ 𝟙 X).appTop
        (f.appTop c)) := by
    intro c
    change functionFieldMap φS.toImage (φS.image.germToFunctionField ⊤ _) = _
    rw [MMP.Spreading.functionFieldMap_germToFunctionField φS.toImage ⊤ ⊤ le_top]
    congr 1
    rw [show φS.toImage.appLE ⊤ ⊤ le_top = φS.toImage.appTop from
      (Scheme.Hom.app_eq_appLE φS.toImage).symm]
    change ((φS.toImage ≫ φS.imageι).appTop) c = _
    rw [Scheme.Hom.toImage_imageι, hφS, Scheme.Hom.comp_appTop]
    rfl
  have hb0 : algebraMap Γ(φS.image, ⊤) φS.image.functionField (φS.imageι.appTop b) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hβ)
  refine ⟨a, b, ?_, ?_⟩
  · intro h0
    apply hb0
    apply (functionFieldMap φS.toImage).injective
    rw [hgerm, map_zero]
    apply Ψ.injective
    rw [hΨg, map_zero, ← h0]
    rfl
  · have hx : x = Ψ (functionFieldMap φS.toImage
        (algebraMap _ φS.image.functionField (φS.imageι.appTop a) /
          algebraMap _ φS.image.functionField (φS.imageι.appTop b))) := by
      rw [hw, RingEquiv.apply_symm_apply]
    rw [hx, map_div₀, map_div₀, hgerm, hgerm, hΨg, hΨg]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at *
    rw [div_mul_cancel₀]
    · intro h0
      apply hb0
      apply (functionFieldMap φS.toImage).injective
      rw [hgerm, map_zero]
      apply Ψ.injective
      rw [hΨg, map_zero]
      exact h0

/-! ### Transport of finite generation -/

section Twist

/-- The twist `p(t) ↦ Φ(p)(c t)` of polynomial rings along a ring isomorphism `Φ` and a unit
`c`, as a ring isomorphism. -/
private noncomputable def twistEquiv {K L : Type*} [CommRing K] [CommRing L] (Φ : K ≃+* L)
    (c : Lˣ) : K[X] ≃+* L[X] :=
  (mapEquiv Φ).trans
    { toFun := fun p => p.comp (C (c : L) * Polynomial.X)
      invFun := fun p => p.comp (C ((c⁻¹ : Lˣ) : L) * Polynomial.X)
      left_inv := fun p => by
        simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, Units.mul_inv,
          C_1, one_mul, comp_X]
      right_inv := fun p => by
        simp only [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, Units.inv_mul,
          C_1, one_mul, comp_X]
      map_mul' := fun p q => mul_comp p q _
      map_add' := fun p q => add_comp }

private theorem coeff_twistEquiv {K L : Type*} [CommRing K] [CommRing L] (Φ : K ≃+* L)
    (c : Lˣ) (p : K[X]) (j : ℕ) :
    (twistEquiv Φ c p).coeff j = Φ (p.coeff j) * (c : L) ^ j := by
  simp only [twistEquiv, RingEquiv.trans_apply, mapEquiv_apply, RingEquiv.coe_mk,
    Equiv.coe_fn_mk]
  rw [comp, eval₂_eq_sum_range, finset_sum_coeff]
  simp only [mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro b _ hb
    simp [Ne.symm hb]
  · intro hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [natDegree_map_eq_of_injective Φ.injective] at hj
    rw [coeff_map, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

private theorem twistEquiv_C {K L : Type*} [CommRing K] [CommRing L] (Φ : K ≃+* L) (c : Lˣ)
    (x : K) : twistEquiv Φ c (C x) = C (Φ x) := by
  simp [twistEquiv]

/-- Finite generation transported along a ring isomorphism of polynomial rings that matches
constants. -/
private theorem finiteType_codRestrict_of_eq_closure {A K L : Type*} [CommRing A] [CommRing K]
    [CommRing L] (ιK : A →+* K) (ιL : A →+* L) (Ψ : L[X] ≃+* K[X])
    (hΨC : ∀ a, Ψ (C (ιL a)) = C (ιK a)) (RX : Subring K[X]) (RY : Set L[X])
    (hΨR : ∀ p, Ψ p ∈ RX ↔ p ∈ RY) (G : Finset L[X])
    (hG : RY = Subring.closure (Set.range (C.comp ιL) ∪ ↑G))
    (hC : ∀ a, C (ιK a) ∈ RX) :
    ((C.comp ιK).codRestrict RX hC).FiniteType := by
  classical
  letI := ((C.comp ιK).codRestrict RX hC).toAlgebra
  have hmem : ∀ g ∈ G, Ψ g ∈ RX := fun g hg =>
    (hΨR g).mpr (by rw [hG]; exact Subring.subset_closure (Or.inr hg))
  let G' : Finset RX := G.attach.image fun g => ⟨Ψ g.1, hmem g.1 g.2⟩
  refine ⟨⟨G', ?_⟩⟩
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨p, rfl⟩ := Ψ.surjective x
  have hp : p ∈ Subring.closure (Set.range (C.comp ιL) ∪ ↑G) := by
    have := (hΨR p).mp hx
    rw [hG] at this
    exact this
  let R' : Subring L[X] := (((Algebra.adjoin A (G' : Set RX)).toSubring.map RX.subtype).comap
    Ψ.toRingHom)
  have hle : Subring.closure (Set.range (C.comp ιL) ∪ ↑G) ≤ R' := by
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · refine ⟨algebraMap A RX a, Subalgebra.algebraMap_mem _ a, ?_⟩
      simp [RingHom.algebraMap_toAlgebra, hΨC]
    · refine ⟨⟨Ψ y, hmem y hy⟩, Algebra.subset_adjoin ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨(⟨y, hy⟩ : {x // x ∈ G}), Finset.mem_attach _ _, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hle hp
  have : z = ⟨Ψ p, hx⟩ := Subtype.ext hzx
  exact this ▸ hz

end Twist

/-- **Sections of the resolution model.** In the situation of
`finiteType_weilRestriction_of_model`, a unit `φ` of `K(X)` is a section of `𝒪_X(jB)` exactly when
`μ^*φ · θ⁻ʲ` is a section of `𝒪_Y(j D_Y)`. -/
private theorem mem_sectionsIn_iff_of_model {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (μ : Y ⟶ X) (hY : IsNormalVariety ℂ (μ ≫ sX)) [IsProper μ]
    (hμ : IsBirationalMorphism μ) {B : Divisor X} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (hpb : B.IsPullback μ hB B') {E' : Divisor Y} (hE' : 0 ≤ E')
    (hEx : ∀ P : MMP.Mori.PrimeDivisor Y, E'.coeff P ≠ 0 →
      ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint)
    (θ : (RationalFunctions Y)ˣ) {DY : Divisor Y}
    (hDY : DY = B' + E' + MMP.Mori.principalDivisor θ) (j : ℕ) (φ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor φ).supp) :
    (φ : RationalFunctions X) ∈ divisorialSections ((j : ℕ) • B) ↔
      rationalFunctionsEquivFunctionField Y
        (((pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ j : (RationalFunctions Y)ˣ)) :
          RationalFunctions Y) ∈ sectionsIn ((j : ℤ) • DY) := by
  haveI : IsDominant μ := hμ.isDominant
  rw [← coe_mem_divisorialSections_iff_mem_sectionsIn, ← Nat.cast_smul_eq_nsmul ℤ j B]
  have hjpb := hpb.zsmul hBc (j : ℤ)
    (fun Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' μ _ Z)
  rw [coe_mem_divisorialSections_iff_pullback hX hY hμ (hBc.zsmul _) hjpb
    (E' := (j : ℤ) • E') (fun P => by
      change 0 ≤ ((j : ℤ) • E').coeff P
      rw [DivisorWithCoeffs.coeff_smul]
      exact mul_nonneg (by positivity) (hE' P))
    (fun P hP => hEx P (by
      rw [DivisorWithCoeffs.coeff_smul] at hP
      exact right_ne_zero_of_mul hP)) φ hφ]
  have hDYj : (j : ℤ) • DY = ((j : ℤ) • B' + (j : ℤ) • E') +
      MMP.Mori.principalDivisor (θ ^ (j : ℤ)) := by
    rw [hDY, principalDivisor_zpow, smul_add, smul_add]
  have hcancel : pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ j * θ ^ (j : ℤ) =
      pullbackRationalFunction μ φ hφ := by
    rw [zpow_natCast, mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]
  rw [hDYj, ← coe_mul_mem_divisorialSections_iff, hcancel]

/-- **A restricted section that does not vanish along `T`.** In the situation of
`finiteType_weilRestriction_of_model`, a section of `𝒪_X(B)` that is a unit along `S` restricts to
a nonzero element of the image series of `D_Y` in degree one. -/
private theorem imageSeries_one_ne_bot_of_model {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (μ : Y ⟶ X) (hY : IsNormalVariety ℂ (μ ≫ sX)) [IsProper μ]
    (hμ : IsBirationalMorphism μ) (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y) [IsIntegral T.idealSheaf.subscheme]
    (hTS : μ T.genericPoint = S.genericPoint) {B : Divisor X} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (hpb : B.IsPullback μ hB B') {E' : Divisor Y} (hE' : 0 ≤ E')
    (hEx : ∀ P : MMP.Mori.PrimeDivisor Y, E'.coeff P ≠ 0 →
      ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint)
    (θ : (RationalFunctions Y)ˣ) (hθT : T.ord θ = 0) {DY : Divisor Y}
    (hDY : DY = B' + E' + MMP.Mori.principalDivisor θ) (φ : (RationalFunctions X)ˣ)
    (hφB : (φ : RationalFunctions X) ∈ divisorialSections B) (hφS : S.ord φ = 0) :
    imageSeries DY T 1 ≠ ⊥ := by
  haveI : IsDominant μ := hμ.isDominant
  haveI : ValuationRing (X.presheaf.stalk (μ T.genericPoint)) := by
    rw [hTS]
    haveI := S.isDiscreteValuationRing_localRing
    infer_instance
  haveI : IsIso (μ.stalkMap T.genericPoint) :=
    MMP.Positivity.isIso_stalkMap_of_valuationRing μ hμ.functionFieldMap_bijective T.genericPoint
  have hTonly : ∀ E : MMP.Mori.PrimeDivisor Y, T.genericPoint ∈ E.support → E = T := fun E hE =>
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (E.eq_genericPoint_of_mem_support hE T.coheight_genericPoint)).symm
  have hSonly : ∀ E : MMP.Mori.PrimeDivisor X, S.genericPoint ∈ E.support → E = S := fun E hE =>
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (E.eq_genericPoint_of_mem_support hE S.coheight_genericPoint)).symm
  obtain ⟨t, ht⟩ := exists_unit_stalk_of_forall_ord_eq_zero T.genericPoint_mem_component θ
    fun E hE => by rw [hTonly E hE]; exact hθT
  obtain ⟨a, ha⟩ := exists_unit_stalk_of_forall_ord_eq_zero S.genericPoint_mem_component φ
    fun E hE => by rw [hSonly E hE]; exact hφS
  have hφ := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' μ
      (MMP.Mori.principalDivisor φ) Z
  have hg := (mem_sectionsIn_iff_of_model hX μ hY hμ hBc hpb hE' hEx θ hDY 1 φ hφ).mp
    (by rwa [one_smul])
  have hr := (isRestrictionAlong_pullback_mul_iff μ S T hTS φ hφ (a : _) ha θ t ht 1 _).mpr rfl
  intro hbot
  have hmem : restrictionToStrictTransform μ S T hTS (a : _) *
      (restrictionAlongT T (t : _))⁻¹ ^ 1 ∈ imageSeries DY T 1 :=
    AddSubgroup.subset_closure ⟨_, by simpa using hg, hr⟩
  rw [hbot, AddSubgroup.mem_bot] at hmem
  have h1 : restrictionToStrictTransform μ S T hTS (a : _) ≠ 0 := (a.isUnit.map _).ne_zero
  have h2 : (restrictionAlongT T (t : _))⁻¹ ≠ 0 := inv_ne_zero (t.isUnit.map _).ne_zero
  exact mul_ne_zero h1 (pow_ne_zero 1 h2) hmem

/-- **The orders of the transported section along `T`.** In the situation of
`imageSeries_one_ne_bot_of_model`, on a smooth `Y` with `T` smooth, the restriction `h` of
`μ^*φ · θ⁻¹` is a nonzero element of the image series of `D_Y` in degree one, and along every prime
divisor `Q` of `T`, `ord_Q(h) + coeff_Q(D_Y|_T)` is the coefficient of `Q` in the restriction of
the effective divisor `div(μ^*φ) + B' + E'`. -/
private theorem exists_mem_imageSeries_ord_add_eq {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (μ : Y ⟶ X) (hY : IsNormalVariety ℂ (μ ≫ sX)) [IsProper μ]
    (hμ : IsBirationalMorphism μ) (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y) [IsIntegral T.idealSheaf.subscheme]
    [IsLocallyNoetherian T.idealSheaf.subscheme]
    (hsmY : IsSmoothScheme (μ ≫ sX)) (hsmT : IsSmoothScheme (T.idealSheaf.subschemeι ≫ μ ≫ sX))
    (hTS : μ T.genericPoint = S.genericPoint) {B : Divisor X} (hBc : B.IsCartier)
    (hBS : B.coeff S = 0)
    {hB : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (hpb : B.IsPullback μ hB B') {E' : Divisor Y} (hE' : 0 ≤ E')
    (hEx : ∀ P : MMP.Mori.PrimeDivisor Y, E'.coeff P ≠ 0 →
      ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint)
    (θ : (RationalFunctions Y)ˣ) (hθT : T.ord θ = 0) {DY : Divisor Y}
    (hDY : DY = B' + E' + MMP.Mori.principalDivisor θ) (φ : (RationalFunctions X)ˣ)
    (hφ : ∀ Z : irreducibleComponents Y,
      μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor φ).supp)
    (hφB : (φ : RationalFunctions X) ∈ divisorialSections B) (hφS : S.ord φ = 0) :
    ∃ h ∈ imageSeries DY T 1, h ≠ 0 ∧ ∀ Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme,
      T.idealSheaf.subscheme.ord h Q.genericPoint + (DY.restrictPrimeDivisor T).coeff Q =
        ((MMP.Mori.principalDivisor (pullbackRationalFunction μ φ hφ) + B' +
          E').restrictPrimeDivisor T).coeff Q := by
  classical
  haveI : IsDominant μ := hμ.isDominant
  haveI : ValuationRing (X.presheaf.stalk (μ T.genericPoint)) := by
    rw [hTS]
    haveI := S.isDiscreteValuationRing_localRing
    infer_instance
  haveI : IsIso (μ.stalkMap T.genericPoint) :=
    MMP.Positivity.isIso_stalkMap_of_valuationRing μ hμ.functionFieldMap_bijective T.genericPoint
  have hTonly : ∀ E : MMP.Mori.PrimeDivisor Y, T.genericPoint ∈ E.support → E = T := fun E hE =>
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (E.eq_genericPoint_of_mem_support hE T.coheight_genericPoint)).symm
  have hSonly : ∀ E : MMP.Mori.PrimeDivisor X, S.genericPoint ∈ E.support → E = S := fun E hE =>
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (E.eq_genericPoint_of_mem_support hE S.coheight_genericPoint)).symm
  obtain ⟨t, ht⟩ := exists_unit_stalk_of_forall_ord_eq_zero T.genericPoint_mem_component θ
    fun E hE => by rw [hTonly E hE]; exact hθT
  obtain ⟨a, ha⟩ := exists_unit_stalk_of_forall_ord_eq_zero S.genericPoint_mem_component φ
    fun E hE => by rw [hSonly E hE]; exact hφS
  have hg := (mem_sectionsIn_iff_of_model hX μ hY hμ hBc hpb hE' hEx θ hDY 1 φ hφ).mp
    (by rwa [one_smul])
  have hr := (isRestrictionAlong_pullback_mul_iff μ S T hTS φ hφ (a : _) ha θ t ht 1 _).mpr rfl
  set h := restrictionToStrictTransform μ S T hTS (a : _) *
    (restrictionAlongT T (t : _))⁻¹ ^ 1 with hhdef
  have hmem : h ∈ imageSeries DY T 1 := AddSubgroup.subset_closure ⟨_, by simpa using hg, hr⟩
  have hh0 : h ≠ 0 := by
    have h1 : restrictionToStrictTransform μ S T hTS (a : _) ≠ 0 := (a.isUnit.map _).ne_zero
    have h2 : (restrictionAlongT T (t : _))⁻¹ ≠ 0 := inv_ne_zero (t.isUnit.map _).ne_zero
    exact mul_ne_zero h1 (pow_ne_zero 1 h2)
  refine ⟨h, hmem, hh0, fun Q => ?_⟩
  set g : (RationalFunctions Y)ˣ := pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ 1 with hgdef
  obtain ⟨b, hb1, hb2⟩ := hr
  -- the restriction of a principal divisor
  have hrestr : ∀ s : Finset (MMP.Mori.PrimeDivisor Y),
      (∀ E : MMP.Mori.PrimeDivisor Y,
        Y.ord (algebraMap _ Y.functionField b) E.genericPoint ≠ 0 → E ∈ s) →
      T.idealSheaf.subscheme.ord
          ((T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom b) Q.genericPoint =
        ∑ E ∈ s, (E.intersectionLength T.idealSheaf.subschemeι Q : ℤ) *
          Y.ord (algebraMap _ Y.functionField b) E.genericPoint := by
    intro s hs
    haveI : AlgebraicGeometry.IsVariety ℂ (μ ≫ sX) := hY.1
    haveI : AlgebraicGeometry.IsVariety ℂ (T.idealSheaf.subschemeι ≫ μ ≫ sX) := ⟨⟩
    haveI : Smooth (μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff (μ ≫ sX)).mp hsmY
    haveI : Smooth (T.idealSheaf.subschemeι ≫ μ ≫ sX) :=
      (MMP.Mori.isSmoothScheme_iff (T.idealSheaf.subschemeι ≫ μ ≫ sX)).mp hsmT
    have hbu : IsUnit b := by
      refine isUnit_of_map_unit (T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom b ?_
      have hbh : (T.idealSheaf.subschemeι.stalkMap (genericPoint _)).hom b = h := hb2
      rw [hbh]
      exact isUnit_iff_ne_zero.mpr hh0
    exact MMP.Mori.PrimeDivisor.ord_restrict_eq_sum_intersectionLength_mul_ord (μ ≫ sX)
      T.idealSheaf.subschemeι b hbu Q s hs
  have hbK : algebraMap _ Y.functionField b =
      rationalFunctionsEquivFunctionField Y (g : RationalFunctions Y) := hb1
  have hordE : ∀ E : MMP.Mori.PrimeDivisor Y,
      Y.ord (algebraMap _ Y.functionField b) E.genericPoint =
        (MMP.Mori.principalDivisor g).coeff E := by
    intro E
    rw [hbK, MMP.Mori.coeff_principalDivisor, E.ord_eq_ord_rationalFunctionsEquivFunctionField]
  have hZDY : MMP.Mori.principalDivisor (pullbackRationalFunction μ φ hφ) + B' + E' =
      DY + MMP.Mori.principalDivisor g := by
    refine DivisorWithCoeffs.ext' fun E => ?_
    rw [hDY, hgdef]
    simp only [DivisorWithCoeffs.coeff_add, MMP.Mori.coeff_principalDivisor,
      MMP.Mori.PrimeDivisor.ord_mul, MMP.Mori.PrimeDivisor.ord_pow,
      MMP.Mori.PrimeDivisor.ord_inv, one_smul]
    ring
  have hDYT : DY.coeff T = 0 := by
    have hB'T : B'.coeff T = 0 := by
      rw [MMP.Positivity.coeff_eq_of_isPullback T S hTS hBc hpb, hBS]
    have hE'T : E'.coeff T = 0 := by
      by_contra h0
      exact hEx T h0 S hTS
    rw [hDY, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      MMP.Mori.coeff_principalDivisor, hB'T, hE'T, hθT, add_zero, add_zero]
  have hgT : (MMP.Mori.principalDivisor g).coeff T = 0 := by
    have hpbφ := Divisor.isPullback_principalDivisor (f := μ) φ hφ
    have h1 := MMP.Positivity.coeff_eq_of_isPullback T S hTS
      (Divisor.isCartier_principalDivisor φ) hpbφ
    rw [MMP.Mori.coeff_principalDivisor, MMP.Mori.coeff_principalDivisor] at h1
    rw [hgdef, MMP.Mori.coeff_principalDivisor, MMP.Mori.PrimeDivisor.ord_mul,
      MMP.Mori.PrimeDivisor.ord_pow, MMP.Mori.PrimeDivisor.ord_inv, h1, hφS, hθT]
    simp
  haveI : IsNoetherian Y := ⟨⟩
  rw [hZDY, DivisorWithCoeffs.restrictPrimeDivisor_add _ _ T hDYT hgT,
    DivisorWithCoeffs.coeff_add, add_comm, add_left_cancel_iff,
    DivisorWithCoeffs.coeff_restrictPrimeDivisor _ T hgT Q, Finsupp.sum, ← hb2,
    hrestr (MMP.Mori.principalDivisor g).support
      (fun E hE => Finsupp.mem_support_iff.mpr (by
        change (MMP.Mori.principalDivisor g).coeff E ≠ 0
        rwa [← hordE]))]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [hordE, nsmul_eq_mul]
  rfl

/-- **Transport of finite generation from a resolution.** Let `μ : Y ⟶ X` be a proper birational
morphism of normal complex varieties over the affine `Z`, `T` the strict transform of the prime
divisor `S`, `B` a Cartier divisor on `X` not containing `S`, with pull-back `B'`, and
`D_Y = B' + E' + div θ` with `E' ≥ 0` exceptional and `θ` a unit along `T`. If the algebra of
restrictions of `D_Y` to `T` is generated over `Γ(Z, 𝒪_Z)` by finitely many polynomials, then the
restriction algebra of `B` along `S` is of finite type over `Γ(Z, 𝒪_Z)`. -/
private theorem finiteType_weilRestriction_of_model {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [IsAffine Z] {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (μ : Y ⟶ X) (hY : IsNormalVariety ℂ (μ ≫ sX)) [IsProper μ]
    (hμ : IsBirationalMorphism μ) (f : X ⟶ Z) (S : MMP.Mori.PrimeDivisor X)
    (T : MMP.Mori.PrimeDivisor Y) [IsIntegral T.idealSheaf.subscheme]
    (hTS : μ T.genericPoint = S.genericPoint) {B : Divisor X} (hBc : B.IsCartier)
    (hBS : B.coeff S = 0) {hB : ∀ Z : irreducibleComponents Y, μ (componentGenericPoint Y Z) ∉ B.supp}
    {B' : Divisor Y} (hpb : B.IsPullback μ hB B') {E' : Divisor Y} (hE' : 0 ≤ E')
    (hEx : ∀ P : MMP.Mori.PrimeDivisor Y, E'.coeff P ≠ 0 →
      ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint)
    (θ : (RationalFunctions Y)ˣ) (hθT : T.ord θ = 0) {DY : Divisor Y}
    (hDY : DY = B' + E' + MMP.Mori.principalDivisor θ)
    (G : Finset (T.idealSheaf.subscheme.functionField)[X])
    (hG : {p : (T.idealSheaf.subscheme.functionField)[X] |
        ∀ j : ℕ, p.coeff j ∈ imageSeries DY T j} =
      (Subring.closure (Set.range (C.comp
        ((T.idealSheaf.subscheme.presheaf.germ ⊤ (genericPoint _) trivial).hom.comp
          ((T.idealSheaf.subschemeι ≫ μ ≫ f ≫ Z.isoSpec.hom).appTop.hom.comp
            (Scheme.ΓSpecIso (.of Γ(Z, ⊤))).inv.hom))) ∪ ↑G) : Set _)) :
    ((weilRestrictionMap hBS).rangeRestrict.comp
      (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict (weilSectionAlgebra B)
        (fun s => Subring.mem_comap.mp ((comap_C_weilSectionAlgebra B).ge ⟨s, rfl⟩))).comp
          f.appTop.hom)).FiniteType := by
  classical
  haveI : IsDominant μ := hμ.isDominant
  have hbij := hμ.functionFieldMap_bijective
  haveI : ValuationRing (X.presheaf.stalk (μ T.genericPoint)) := by
    rw [hTS]
    haveI := S.isDiscreteValuationRing_localRing
    infer_instance
  haveI : IsIso (μ.stalkMap T.genericPoint) :=
    MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij T.genericPoint
  set Φ := residueFieldEquiv μ S T hTS with hΦ
  -- the class of `θ` along `T`
  have hTonly : ∀ E : MMP.Mori.PrimeDivisor Y, T.genericPoint ∈ E.support → E = T := fun E hE =>
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (E.eq_genericPoint_of_mem_support hE T.coheight_genericPoint)).symm
  obtain ⟨t, ht⟩ := exists_unit_stalk_of_forall_ord_eq_zero T.genericPoint_mem_component θ
    fun E hE => by rw [hTonly E hE]; exact hθT
  set c : (T.idealSheaf.subscheme.functionField)ˣ :=
    Units.map (restrictionAlongT T).toMonoidHom t with hc
  -- the pieces `V_j` of the restriction algebra of `B`
  set V : ℕ → Set (X.residueField S.genericPoint) := fun j =>
    {r | ∃ g ∈ divisorialSections ((j : ℕ) • B), ∃ hg : g ∈ localSubring S,
      residueAlong S ⟨g, hg⟩ = r} with hV
  have hV0 : ∀ j, (0 : X.residueField S.genericPoint) ∈ V j := fun j =>
    ⟨0, zero_mem _, zero_mem _, map_zero (residueAlong S)⟩
  -- the restriction of the pull-back of a section
  have hres : ∀ (j : ℕ) (φ : (RationalFunctions X)ˣ)
      (hφ : ∀ Z : irreducibleComponents Y,
        μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor φ).supp)
      (hl : (φ : RationalFunctions X) ∈ localSubring S) (h : T.idealSheaf.subscheme.functionField),
      IsRestrictionAlong T (rationalFunctionsEquivFunctionField Y
          (((pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ j : (RationalFunctions Y)ˣ)) :
            RationalFunctions Y)) h ↔
        h = Φ (residueAlong S ⟨_, hl⟩) * ((c⁻¹ : (_)ˣ) : _) ^ j := by
    intro j φ hφ hl h
    obtain ⟨a, ha⟩ := hl
    rw [isRestrictionAlong_pullback_mul_iff μ S T hTS φ hφ a ha θ t ht j h, residueAlong_eq _ ha,
      hΦ, residueFieldEquiv_residue, hc, Units.val_inv_eq_inv_val]
    rfl
  -- sections of `j D_Y` are the twisted pull-backs of sections of `j B`
  have hsec := fun (j : ℕ) (φ : (RationalFunctions X)ˣ) hφ =>
    mem_sectionsIn_iff_of_model hX μ hY hμ hBc hpb hE' hEx θ hDY j φ hφ
  -- units of `K(Y)` are pull-backs
  have hpull : ∀ ψ : (RationalFunctions Y)ˣ, ∃ (φ : (RationalFunctions X)ˣ)
      (hφ : ∀ Z : irreducibleComponents Y,
        μ (componentGenericPoint Y Z) ∉ (MMP.Mori.principalDivisor φ).supp),
      pullbackRationalFunction μ φ hφ = ψ := by
    intro ψ
    have hψ0 : rationalFunctionsEquivFunctionField Y (ψ : RationalFunctions Y) ≠ 0 :=
      (ψ.isUnit.map (rationalFunctionsEquivFunctionField Y)).ne_zero
    obtain ⟨x, hx⟩ := hbij.2 (rationalFunctionsEquivFunctionField Y (ψ : RationalFunctions Y))
    have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx; exact hψ0 hx.symm
    set φ : (RationalFunctions X)ˣ :=
      Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom (Units.mk0 x hx0)
    have hφ := fun Z =>
      MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' μ
        (MMP.Mori.principalDivisor φ) Z
    refine ⟨φ, hφ, Units.ext ((rationalFunctionsEquivFunctionField Y).injective ?_)⟩
    rw [rationalFunctionsEquivFunctionField_pullbackRationalFunction μ φ hφ, ← hx]
    simp [φ]
  have hW : ∀ (j : ℕ) (h : T.idealSheaf.subscheme.functionField),
      h ∈ imageSeries DY T j ↔ ∃ r ∈ V j, h = Φ r * ((c⁻¹ : (_)ˣ) : _) ^ j := by
    intro j
    have hMN : ∀ h : T.idealSheaf.subscheme.functionField,
        (∃ g ∈ sectionsIn ((j : ℤ) • DY), IsRestrictionAlong T g h) ↔
          ∃ r ∈ V j, h = Φ r * ((c⁻¹ : (_)ˣ) : _) ^ j := by
      intro h
      constructor
      · rintro ⟨g, hg, hgh⟩
        by_cases hg0 : g = 0
        · subst hg0
          obtain ⟨b, hb0, rfl⟩ := hgh
          have hinj : Function.Injective (algebraMap (Y.presheaf.stalk (T.idealSheaf.subschemeι
              (genericPoint T.idealSheaf.subscheme))) Y.functionField) :=
            IsFractionRing.injective _ _
          have hb : b = 0 := hinj (hb0.trans (map_zero _).symm)
          exact ⟨0, hV0 j, by rw [hb, map_zero, map_zero, zero_mul]⟩
        · set ψ : (RationalFunctions Y)ˣ :=
            Units.map (rationalFunctionsEquivFunctionField Y).symm.toMonoidHom (Units.mk0 g hg0)
          obtain ⟨φ, hφ, hφψ⟩ := hpull (ψ * θ ^ j)
          have hgψ : g = rationalFunctionsEquivFunctionField Y
              (((pullbackRationalFunction μ φ hφ * (θ⁻¹) ^ j : (RationalFunctions Y)ˣ)) :
                RationalFunctions Y) := by
            rw [hφψ, mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
            simp [ψ]
          rw [hgψ, ← hsec] at hg
          have hl := divisorialSections_le_localSubring (B := B) hBS j hg
          rw [hgψ, hres j φ hφ hl] at hgh
          exact ⟨_, ⟨_, hg, hl, rfl⟩, hgh⟩
      · rintro ⟨r, ⟨g, hg, hl, rfl⟩, rfl⟩
        by_cases hg0 : g = 0
        · subst hg0
          refine ⟨0, (sectionsSubgroup _).zero_mem, ⟨0, map_zero _, ?_⟩⟩
          rw [map_zero]
          change 0 = Φ (residueAlong S 0) * _
          rw [map_zero, map_zero, zero_mul]
        · have hge : rationalFunctionsEquivFunctionField X g ≠ 0 := fun h0 =>
            hg0 ((map_eq_zero_iff _ (rationalFunctionsEquivFunctionField X).injective).mp h0)
          obtain ⟨φ, rfl⟩ : ∃ φ : (RationalFunctions X)ˣ, (φ : RationalFunctions X) = g :=
            ⟨Units.map (rationalFunctionsEquivFunctionField X).symm.toMonoidHom
              (Units.mk0 _ hge), by simp⟩
          have hφ := fun Z =>
            MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' μ
              (MMP.Mori.principalDivisor φ) Z
          exact ⟨_, (hsec j φ hφ).mp hg, (hres j φ hφ hl _).mpr rfl⟩
    intro h
    constructor
    · intro hh
      let NJ : AddSubgroup T.idealSheaf.subscheme.functionField :=
        { carrier := {h | ∃ r ∈ V j, h = Φ r * ((c⁻¹ : (_)ˣ) : _) ^ j}
          zero_mem' := ⟨0, hV0 j, by rw [map_zero, zero_mul]⟩
          add_mem' := by
            rintro _ _ ⟨_, ⟨g₁, hg₁, hl₁, rfl⟩, rfl⟩ ⟨_, ⟨g₂, hg₂, hl₂, rfl⟩, rfl⟩
            refine ⟨_, ⟨g₁ + g₂, add_mem hg₁ hg₂, add_mem hl₁ hl₂, rfl⟩, ?_⟩
            rw [← add_mul, ← map_add, ← map_add]
            rfl
          neg_mem' := by
            rintro _ ⟨_, ⟨g, hg, hl, rfl⟩, rfl⟩
            refine ⟨_, ⟨-g, neg_mem hg, neg_mem hl, rfl⟩, ?_⟩
            rw [← neg_mul, ← map_neg, ← map_neg]
            rfl }
      have hle : imageSeries DY T j ≤ NJ :=
        (AddSubgroup.closure_le _).mpr fun h hh => (hMN h).mp hh
      exact hle hh
    · intro hh
      exact AddSubgroup.subset_closure ((hMN h).mpr hh)
  have hR : ∀ q : (X.residueField S.genericPoint)[X],
      q ∈ (weilRestrictionMap hBS).range ↔ ∀ j : ℕ, q.coeff j ∈ V j := by
    intro q
    change q ∈ weilRestrictionAlgebra hBS ↔ _
    rw [mem_weilRestrictionAlgebra_iff]
    constructor
    · rintro ⟨p, hp, hpq⟩ j
      obtain ⟨a, ha, hq⟩ := hpq j
      exact ⟨p.coeff j, hp j, ⟨a, ha⟩, by rw [residueAlong_eq _ ha, hq]⟩
    · intro h
      choose g hg hgl hgr using h
      have hc : ∀ n, (∑ m ∈ q.support, monomial m (g m)).coeff n =
          if n ∈ q.support then g n else 0 := fun n => by
        rw [finset_sum_coeff]
        simp only [coeff_monomial]
        exact Finset.sum_ite_eq' _ _ _
      refine ⟨∑ m ∈ q.support, monomial m (g m), fun n => ?_, fun n => ?_⟩
      · rw [hc]
        split_ifs
        · exact hg n
        · exact zero_mem _
      · rw [hc]
        split_ifs with hn
        · obtain ⟨a, ha⟩ := hgl n
          exact ⟨a, ha, by rw [← hgr n, residueAlong_eq _ ha]⟩
        · refine ⟨0, by simp, ?_⟩
          rw [map_zero]
          exact notMem_support_iff.mp hn
  -- the constants
  have hloc : ∀ a : Γ(Z, ⊤),
      (globalSectionsToRationalFunctions (X := X)) (f.appTop.hom a) ∈ localSubring S := fun a =>
    divisorialSections_le_localSubring (B := (0 : Divisor X)) (S := S) (by simp) 0
      (by rw [zero_smul]; exact mem_divisorialSections_zero_iff.mpr ⟨_, rfl⟩)
  set ιX : Γ(Z, ⊤) →+* X.residueField S.genericPoint :=
    (residueAlong S).comp (((globalSectionsToRationalFunctions (X := X)).comp
      f.appTop.hom).codRestrict (localSubring S) hloc) with hιX
  set ιY : Γ(Z, ⊤) →+* T.idealSheaf.subscheme.functionField :=
    (T.idealSheaf.subscheme.presheaf.germ ⊤ (genericPoint _) trivial).hom.comp
      ((T.idealSheaf.subschemeι ≫ μ ≫ f ≫ Z.isoSpec.hom).appTop.hom.comp
        (Scheme.ΓSpecIso (.of Γ(Z, ⊤))).inv.hom) with hιY
  have hιXY : ∀ a, ιY a = Φ (ιX a) := by
    intro a
    have hS : S.toComponent.hom (X.presheaf.germ ⊤ S.genericPoint trivial (f.appTop.hom a)) =
        (globalSectionsToRationalFunctions (f.appTop.hom a) : RationalFunctions X) S.component := by
      erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      rfl
    have h1 : ιX a = X.residue S.genericPoint
        (X.presheaf.germ ⊤ S.genericPoint trivial (f.appTop.hom a)) := residueAlong_eq _ hS
    rw [h1, hΦ, residueFieldEquiv_residue, restrictionToStrictTransform_germ, hιY]
    simp only [RingHom.comp_apply]
    congr 1
    have e : T.idealSheaf.subschemeι ≫ μ ≫ f ≫ Z.isoSpec.hom =
        (T.idealSheaf.subschemeι ≫ μ) ≫ f ≫ Z.isoSpec.hom := by simp only [Category.assoc]
    have hiso : (CommRingCat.Hom.hom (Scheme.ΓSpecIso Γ(Z, ⊤)).hom)
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ↑Γ(Z, ⊤))).inv) a) = a :=
      (Scheme.ΓSpecIso Γ(Z, ⊤)).inv_hom_id_apply a
    rw [e, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.isoSpec, asIso_hom,
      Scheme.toSpecΓ_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [hiso]
  have hCX : ∀ a, C (ιX a) ∈ (weilRestrictionMap hBS).range := fun a =>
    (hR _).mpr fun j => by
      rw [coeff_C]
      split_ifs with hj
      · subst hj
        exact ⟨_, by rw [zero_smul]; exact mem_divisorialSections_zero_iff.mpr ⟨_, rfl⟩,
          hloc a, rfl⟩
      · exact ⟨0, zero_mem _, zero_mem _, map_zero (residueAlong S)⟩
  have hgoal : (weilRestrictionMap hBS).rangeRestrict.comp
      (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict (weilSectionAlgebra B)
        (fun s => Subring.mem_comap.mp ((comap_C_weilSectionAlgebra B).ge ⟨s, rfl⟩))).comp
          f.appTop.hom) = (C.comp ιX).codRestrict (weilRestrictionMap hBS).range hCX := by
    refine RingHom.ext fun a => Subtype.ext ?_
    change weilRestrictionMap hBS ⟨C (globalSectionsToRationalFunctions (f.appTop.hom a)), _⟩ =
      C (ιX a)
    ext m
    obtain ⟨a', ha'⟩ := hloc a
    rw [coeff_C]
    split_ifs with hm
    · subst hm
      rw [coeff_weilRestrictionMap hBS _ 0 (a := a') (by rw [coeff_C_zero]; exact ha')]
      exact (residueAlong_eq _ ha').symm
    · rw [coeff_weilRestrictionMap hBS _ m (a := 0) (by simp [coeff_C, hm])]
      exact map_zero _
  rw [hgoal]
  set c' : (X.residueField S.genericPoint)ˣ := Units.map Φ.symm.toMonoidHom c with hc'
  refine finiteType_codRestrict_of_eq_closure ιX ιY (twistEquiv Φ.symm c') (fun a => ?_)
    (weilRestrictionMap hBS).range _ (fun p => ?_) G hG hCX
  · rw [twistEquiv_C, hιXY, RingEquiv.symm_apply_apply]
  · rw [hR, Set.mem_setOf_eq]
    refine forall_congr' fun j => ?_
    rw [coeff_twistEquiv, hW]
    constructor
    · intro hj
      refine ⟨_, hj, ?_⟩
      have hΦc : Φ ((c' : X.residueField S.genericPoint)) = (c : _) := by simp [hc']
      rw [map_mul, map_pow, RingEquiv.apply_symm_apply, hΦc, mul_assoc, ← mul_pow,
        Units.mul_inv, one_pow, mul_one]
    · rintro ⟨r, hr, hrj⟩
      have hc'v : ((c' : X.residueField S.genericPoint)) = Φ.symm (c : _) := by simp [hc']
      rw [hrj, hc'v, map_mul, map_pow, RingEquiv.symm_apply_apply, mul_assoc, ← mul_pow,
        ← map_mul, Units.inv_mul, map_one, one_pow, mul_one]
      exact hr

/-! ### The bounds of the snc discrepancy formula -/

section SNCBounds

private theorem exists_lt_one_forall_le {ι : Type*} (s : Finset ι) (c : ι → ℚ)
    (h : ∀ i ∈ s, c i < 1) : ∃ m : ℚ, 0 ≤ m ∧ m < 1 ∧ ∀ i ∈ s, c i ≤ m := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, le_rfl, by norm_num, by simp⟩
  · obtain ⟨i, hi, hmax⟩ := s.exists_max_image c hs
    exact ⟨max (c i) 0, le_max_right _ _, max_lt (h i hi) (by norm_num),
      fun j hj => le_max_of_le_left (hmax j hj)⟩

/-- The snc discrepancy bound exceeds `-1` when all coefficients are at most one and only `T`
may have coefficient one. -/
private theorem neg_one_lt_snc_inf {ι : Type*} [DecidableEq ι] (S : Finset ι) (T : ι)
    (c : ι → ℚ) (meet : ι → ι → Prop) (hc1 : ∀ E ∈ S, c E ≤ 1)
    (hcT : ∀ E ∈ S, E ≠ T → c E < 1) :
    ((-1 : ℝ) : EReal) < (⨅ (E ∈ S) (F ∈ S) (_ : E ≠ F) (_ : meet E F),
        (((1 - c E - c F : ℚ) : ℝ) : EReal)) ⊓ (⨅ E ∈ S, (((1 - c E : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  obtain ⟨m, hm0, hm1, hm⟩ := exists_lt_one_forall_le (S.erase T) c fun E hE =>
    hcT E (Finset.mem_of_mem_erase hE) (Finset.ne_of_mem_erase hE)
  have key : (((-m : ℚ) : ℝ) : EReal) ≤ (⨅ (E ∈ S) (F ∈ S) (_ : E ≠ F) (_ : meet E F),
      (((1 - c E - c F : ℚ) : ℝ) : EReal)) ⊓ (⨅ E ∈ S, (((1 - c E : ℚ) : ℝ) : EReal)) ⊓ 1 := by
    refine le_inf (le_inf ?_ ?_) ?_
    · refine le_iInf₂ fun E hE => le_iInf₂ fun F hF => le_iInf₂ fun hEF _ => ?_
      rw [EReal.coe_le_coe_iff, Rat.cast_le]
      by_cases hET : E = T
      · subst hET
        have := hm F (Finset.mem_erase.mpr ⟨Ne.symm hEF, hF⟩)
        linarith [hc1 E hE]
      · have := hm E (Finset.mem_erase.mpr ⟨hET, hE⟩)
        linarith [hc1 F hF]
    · refine le_iInf₂ fun E hE => ?_
      rw [EReal.coe_le_coe_iff, Rat.cast_le]
      linarith [hc1 E hE]
    · have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
      have : ((-m : ℚ) : ℝ) ≤ 1 := by push_cast; linarith
      exact_mod_cast this
  refine lt_of_lt_of_le ?_ key
  rw [EReal.coe_lt_coe_iff]
  have hm1' : (m : ℝ) < 1 := by exact_mod_cast hm1
  push_cast
  linarith

end SNCBounds

/-- The coefficients of the prepared boundary `T + s H + (Γ - T) + t F⁺`. -/
private theorem coeff_preparedBoundary {Y : Scheme.{0}} (T : MMP.Mori.PrimeDivisor Y)
    (H F : Divisor Y) (Γ : QDivisor Y) (s t : ℚ) (E : MMP.Mori.PrimeDivisor Y) :
    (Divisor.toQDivisor (Finsupp.single T 1) + s • Divisor.toQDivisor H +
        ((Γ - Divisor.toQDivisor (Finsupp.single T 1)) + t • Divisor.toQDivisor (F ⊔ 0))).coeff E =
      s * H.coeff E + Γ.coeff E + t * max ((F.coeff E : ℤ) : ℚ) 0 := by
  simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
    DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
  have : ((F ⊔ 0 : Divisor Y).coeff E : ℚ) = max (F.coeff E : ℚ) 0 := by
    change (((F ⊔ 0 : Divisor Y) E : ℤ) : ℚ) = _
    rw [Finsupp.sup_apply]
    push_cast
    rfl
  rw [this]
  ring

/-- The generic point of an exceptional prime divisor of a morphism of normal schemes is not
mapped to the generic point of a prime divisor. -/
private theorem map_genericPoint_ne_of_isExceptional {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (X ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (P : MMP.Mori.PrimeDivisor Y)
    (hP : MMP.Mori.RationalMap.IsExceptional (X := Y) f.toRationalMap P)
    (Γ : MMP.Mori.PrimeDivisor X) : f P.genericPoint ≠ Γ.genericPoint := by
  intro he
  have h2 := (MMP.Positivity.isExceptional_toRationalMap_iff P).mp hP
  have hmem : f P.genericPoint ∈
      (TopologicalSpace.Closeds.closure (f '' (P.idealSheaf.support : Set Y)) : Set X) :=
    subset_closure ⟨P.genericPoint, by
      have h := AlgebraicGeometry.PrimeDivisor.support_eq_closure P
      have h' : P.genericPoint ∈ (P.support : Set Y) := by rw [h]; exact subset_closure rfl
      exact h', rfl⟩
  have h3 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2 _ hmem
  rw [he, MMP.Mori.PrimeDivisor.coheight_genericPoint] at h3
  exact absurd h3 (by decide)

/-- Every prime divisor whose generic point lies in `Ex(μ) ∪ μ⁻¹(Supp Δ)` is a component of the
snc divisor of a log resolution `μ` of `(X, Δ)`. -/
private theorem exists_finset_isSNC_of_isLogResolution {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {Δ : MMP.Mori.RDivisor X} {μ : Y ⟶ X}
    (hlog : MMP.Mori.IsLogResolution sX Δ μ) (s₀ : Finset (MMP.Mori.PrimeDivisor Y))
    (hne : s₀.Nonempty)
    (hs₀ : ∀ P ∈ s₀, P.genericPoint ∈ MMP.Mori.exceptionalSet μ ⊔ Δ.supp.preimage μ.continuous) :
    ∃ S₀ : Finset (MMP.Mori.PrimeDivisor Y), s₀ ⊆ S₀ ∧
      MMP.Mori.DivisorWithCoeffs.IsSNC (μ ≫ sX) (∑ P ∈ S₀, Finsupp.single P (1 : ℤ)) := by
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · obtain ⟨P, hP⟩ := hne
    have := hs₀ P hP
    rw [h, ← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at this
    exact this.elim
  · refine ⟨s, fun P hP => ?_, hsnc⟩
    have hmem := hs₀ P hP
    rw [← SetLike.mem_coe, ← hs] at hmem
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hmem
    have hEP : E = P := (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (E.eq_genericPoint_of_mem_support hPE P.coheight_genericPoint)).symm
    exact hEP ▸ hE
/-- The support of `∑_{E ∈ s} E` is `s`. -/
private theorem support_sum_single_one {W : Scheme.{0}} (s : Finset (MMP.Mori.PrimeDivisor W)) :
    (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support = s := by
  classical
  ext P
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

/-- **A margin for canonical perturbations of a terminal snc boundary.** Let `(W, Ψ₀)` be a real
terminal pair on a smooth variety, with `Ψ₀` snc. There is `ε > 0` such that
`discrep(W, Ψ₀ + Θ) ≥ 0` for every `ℚ`-divisor `Θ` with coefficients in `[0, ε]` for which
`Ψ₀ + Θ` is supported on an snc divisor. Two meeting components of `Ψ₀` have coefficients of sum
`< 1`, since blowing up a component of their intersection gives an exceptional divisor of
discrepancy `1 - a - b`. -/
private theorem exists_pos_forall_zero_le_discrep_add {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)} (hW : IsNormalVariety ℂ sW)
    (hsm : IsSmoothScheme sW) {n : ℕ} (hn : 2 ≤ n) {KW : Divisor W}
    (hK : KW.IsCanonicalDivisor sW n) {Ψ₀ : QDivisor W} (hsnc : Ψ₀.IsSNC sW)
    (hterm : IsRealTerminalPair sW (QDivisor.toRDivisor Ψ₀)) :
    ∃ ε : ℚ, 0 < ε ∧ ∀ S : Finset (MMP.Mori.PrimeDivisor W),
      DivisorWithCoeffs.IsSNC sW (∑ E ∈ S, Finsupp.single E (1 : ℤ)) →
      ∀ Θ : QDivisor W, (Ψ₀ + Θ).support ⊆ S → (∀ P, 0 ≤ Θ.coeff P) →
        (∀ P, Θ.coeff P ≤ ε) → 0 ≤ discrep sW n KW (Ψ₀ + Θ) := by
  classical
  haveI : IsSeparated sW := hW.1.toIsSeparated
  haveI : IsSeparated (W ↘ ⊤_ Scheme) := by
    rw [show (W ↘ ⊤_ Scheme) = sW ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  haveI : QuasiCompact sW := hW.1.toQuasiCompact
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hdim : topologicalKrullDim W = n := hK.topologicalKrullDim_eq
  have hpair : IsPairWith sW n KW Ψ₀ := ⟨hW, hK, isQCartier_of_isSmoothScheme hsm _⟩
  -- the coefficients of `Ψ₀` are `< 1`
  have hone : ∀ E, Ψ₀.coeff E < 1 := fun E => by
    by_cases h : Ψ₀.coeff E = 0
    · rw [h]; norm_num
    · have := (hterm.1.2.1 E (by rw [QDivisor.coeff_toRDivisor]; exact_mod_cast h)).2
      rw [QDivisor.coeff_toRDivisor] at this
      exact_mod_cast this
  -- two meeting components of `Ψ₀` have coefficients of sum `< 1`
  have hsnc₀ : DivisorWithCoeffs.IsSNC sW (∑ E ∈ Ψ₀.support, Finsupp.single E (1 : ℤ)) :=
    (DivisorWithCoeffs.isSNC_iff_of_support_eq (support_sum_single_one _)).mpr hsnc
  have hpair2 : ∀ E ∈ Ψ₀.support, ∀ F ∈ Ψ₀.support, E ≠ F →
      (E.support ∩ F.support).Nonempty → Ψ₀.coeff E + Ψ₀.coeff F < 1 := by
    intro E hE F hF hEF hmeet
    obtain ⟨D, hDex, hDc⟩ :=
      exists_isExceptional_isDiscrepancy_eq_one_sub_sub hW hsm hdim hsnc₀ hE hF hEF hmeet
    obtain ⟨Ep, hEpv⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hW D
    have hEpex : Ep.toDivisorOver.IsExceptional := by
      by_contra hnot
      obtain ⟨P, hPv⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hW _ hnot
      have hc1 := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hW
        (hEpv.symm.trans hPv)
      haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      exact map_genericPoint_ne_of_isExceptional D.E hDex P hc1
    obtain ⟨c0, hc0⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK D
    obtain ⟨c, hc⟩ :=
      MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK Ep.toDivisorOver
    have e0 := hDc KW Ψ₀ subset_rfl c0 hc0
    have e1 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hpair hEpv hc hc0
    have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc Ep.isProper
    have h1 := hterm.2 n Ep.toDivisorOver _ hEpex hlog
    have hc' : (0 : ℝ) < c := by linarith
    have hc'' : (0 : ℚ) < c := by exact_mod_cast hc'
    linarith
  -- the margin `ε`
  have key : ∀ x : ℚ, 0 < x → ∀ᶠ ε in 𝓝[>] (0 : ℚ), 2 * ε ≤ x := by
    intro x hx
    have ht : Filter.Tendsto (fun ε : ℚ => 2 * ε) (𝓝[>] 0) (𝓝 0) := by
      have h : Filter.Tendsto (fun ε : ℚ => 2 * ε) (𝓝 0) (𝓝 0) :=
        (continuous_const.mul continuous_id).tendsto' 0 0 (by simp)
      exact h.mono_left nhdsWithin_le_nhds
    exact ht.eventually (Iic_mem_nhds hx)
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℚ), 0 < ε ∧ 2 * ε ≤ 1 ∧
      (∀ E ∈ Ψ₀.support, 2 * ε ≤ 1 - Ψ₀.coeff E) ∧
      ∀ E ∈ Ψ₀.support, ∀ F ∈ Ψ₀.support, E ≠ F ∧ (E.support ∩ F.support).Nonempty →
        2 * ε ≤ 1 - Ψ₀.coeff E - Ψ₀.coeff F := by
    refine (eventually_mem_nhdsWithin).and ((key 1 one_pos).and
      (((Filter.eventually_all_finset _).mpr fun E _ => key _ (by linarith [hone E])).and
        ((Filter.eventually_all_finset _).mpr fun E hE =>
          (Filter.eventually_all_finset _).mpr fun F hF => ?_)))
    by_cases h : E ≠ F ∧ (E.support ∩ F.support).Nonempty
    · exact (key _ (by linarith [hpair2 E hE F hF h.1 h.2])).mono fun ε hε _ => hε
    · exact Filter.Eventually.of_forall fun ε h' => absurd h' h
  obtain ⟨ε, hε0, hε1, hεs, hεp⟩ := hall.exists
  have hε0' : (0 : ℚ) < ε := hε0
  refine ⟨ε, hε0', fun S hS Θ hΘS hΘ0 hΘε => ?_⟩
  have hz : ∀ E, E ∉ Ψ₀.support → Ψ₀.coeff E = 0 := fun E hE => Finsupp.notMem_support_iff.mp hE
  have hcoeff : ∀ E ∈ S, (Ψ₀ + Θ).coeff E ≤ 1 := fun E _ => by
    rw [DivisorWithCoeffs.coeff_add]
    by_cases hE : E ∈ Ψ₀.support
    · linarith [hεs E hE, hΘε E]
    · rw [hz E hE]; linarith [hΘε E]
  rw [discrep_eq_of_isSNC sW hW hsm hn hK S hΘS hS hcoeff]
  refine le_inf (le_inf ?_ ?_) zero_le_one
  · refine le_iInf₂ fun E hE => le_iInf₂ fun F hF => le_iInf₂ fun hEF hmeet => ?_
    rw [EReal.coe_nonneg, Rat.cast_nonneg, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add]
    have hE1 := hΘε E
    have hF1 := hΘε F
    by_cases hE' : E ∈ Ψ₀.support <;> by_cases hF' : F ∈ Ψ₀.support
    · linarith [hεp E hE' F hF' ⟨hEF, hmeet⟩]
    · rw [hz F hF']; linarith [hεs E hE']
    · rw [hz E hE']; linarith [hεs F hF']
    · rw [hz E hE', hz F hF']; linarith
  · refine le_iInf₂ fun E hE => ?_
    rw [EReal.coe_nonneg, Rat.cast_nonneg]
    linarith [hcoeff E hE]

/-- A prime divisor of a variety of dimension `n + 1` has dimension `n`. -/
private theorem topologicalKrullDim_subscheme_primeDivisor {Y : Scheme.{0}} [IsIntegral Y]
    (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY] {n : ℕ}
    (hY : topologicalKrullDim Y = n + 1) (T : MMP.Mori.PrimeDivisor Y) :
    topologicalKrullDim T.idealSheaf.subscheme = n := by
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
    show (T.idealSheaf.support : Set Y) = closure {T.genericPoint} from
      AlgebraicGeometry.PrimeDivisor.support_eq_closure T]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY T.genericPoint
  rw [MMP.Mori.PrimeDivisor.coheight_genericPoint, hY] at h
  generalize topologicalKrullDim (closure {T.genericPoint} : Set Y) = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot =>
    simp only [WithBot.bot_add] at h
    exact (WithBot.bot_ne_coe (a := ((n : ℕ∞) + 1)) (by exact_mod_cast h)).elim
  | coe a =>
    have h' : a + 1 = (n : ℕ∞) + 1 := by exact_mod_cast h
    have := (ENat.add_left_injective_of_ne_top (by simp : (1 : ℕ∞) ≠ ⊤)) h'
    rw [this]; rfl

section Restriction

variable {Y : Scheme.{0}} [IsLocallyNoetherian Y] [CompactSpace Y]
  (D : Finset (MMP.Mori.PrimeDivisor Y)) (T : MMP.Mori.PrimeDivisor Y) (hTD : T ∉ D)

include hTD in
/-- The coefficient of `Θ|_T`, for `Θ` supported on `D ∌ T`, as a sum over `D`. -/
private theorem coeff_restrictPrimeDivisor_eq_sum (Θ : QDivisor Y) (hΘ : Θ.support ⊆ D)
    (Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme) :
    (Θ.restrictPrimeDivisor T).coeff Q =
      ∑ E ∈ D, (E.intersectionLength T.idealSheaf.subschemeι Q : ℚ) * Θ.coeff E := by
  haveI : IsNoetherian Y := ⟨⟩
  have hΘT : Θ.coeff T = 0 := Finsupp.notMem_support_iff.mp fun h => hTD (hΘ h)
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor Θ T hΘT Q,
    Finsupp.sum_of_support_subset Θ hΘ _ (fun _ _ => smul_zero _)]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [nsmul_eq_mul]
  rfl

include hTD in
/-- The coefficient of `(∑_{E ∈ D} E)|_T` is the sum of the local intersection lengths. -/
private theorem coeff_restrictPrimeDivisor_sum_single (Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme) :
    ((DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).coeff Q : ℤ) =
      ∑ E ∈ D, (E.intersectionLength T.idealSheaf.subschemeι Q : ℤ) := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  have happ : ∀ E, (∑ E ∈ D, Finsupp.single E (1 : ℤ)) E = if E ∈ D then 1 else 0 := by
    intro E
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hT0 : DivisorWithCoeffs.coeff (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T = 0 := by
    change (∑ E ∈ D, Finsupp.single E (1 : ℤ)) T = 0
    rw [happ, if_neg hTD]
  rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor _ T hT0 Q,
    Finsupp.sum_of_support_subset _ (support_sum_single_one D).le _ (fun _ _ => smul_zero _)]
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [happ, if_pos hE, nsmul_eq_mul, mul_one]

include hTD in
/-- The restriction to `T` of a `ℚ`-divisor supported on `D ∌ T` is supported on the support of
`(∑_{E ∈ D} E)|_T`. -/
private theorem support_restrictPrimeDivisor_subset (Θ : QDivisor Y) (hΘ : Θ.support ⊆ D) :
    (Θ.restrictPrimeDivisor T).support ⊆
      (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).support := by
  intro Q hQ
  rw [Finsupp.mem_support_iff] at hQ ⊢
  change (Θ.restrictPrimeDivisor T).coeff Q ≠ 0 at hQ
  change (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).coeff Q ≠ 0
  rw [coeff_restrictPrimeDivisor_eq_sum D T hTD Θ hΘ Q] at hQ
  obtain ⟨E, hE, hE0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hlen : E.intersectionLength T.idealSheaf.subschemeι Q ≠ 0 := by
    intro h; apply hE0; rw [h]; simp
  intro h0
  have := coeff_restrictPrimeDivisor_sum_single D T hTD Q
  rw [h0, eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at this
  exact hlen (by exact_mod_cast this E hE)

include hTD in
/-- If `(∑_{E ∈ D} E)|_T` has all its nonzero coefficients equal to `1`, the restriction to `T`
of a `ℚ`-divisor supported on `D ∌ T` with coefficients in `[0, ε]` has coefficients in
`[0, ε]`. -/
private theorem coeff_restrictPrimeDivisor_mem_Icc
    (hST : ∀ Q ∈ (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).support,
      (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).coeff Q = 1)
    (Θ : QDivisor Y) (hΘ : Θ.support ⊆ D) {ε : ℚ} (hε : 0 ≤ ε) (hΘ0 : ∀ P, 0 ≤ Θ.coeff P)
    (hΘε : ∀ P, Θ.coeff P ≤ ε) (Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme) :
    0 ≤ (Θ.restrictPrimeDivisor T).coeff Q ∧ (Θ.restrictPrimeDivisor T).coeff Q ≤ ε := by
  rw [coeff_restrictPrimeDivisor_eq_sum D T hTD Θ hΘ Q]
  refine ⟨Finset.sum_nonneg fun E _ => mul_nonneg (by positivity) (hΘ0 E), ?_⟩
  have hsum := coeff_restrictPrimeDivisor_sum_single D T hTD Q
  have hle : (∑ E ∈ D, (E.intersectionLength T.idealSheaf.subschemeι Q : ℚ)) ≤ 1 := by
    have h1 : ((DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).coeff Q : ℤ) ≤ 1 := by
      by_cases hQ : Q ∈ (DivisorWithCoeffs.restrictPrimeDivisor (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).support
      · rw [hST Q hQ]
      · have h0 : (DivisorWithCoeffs.restrictPrimeDivisor
            (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).coeff Q = 0 :=
          Finsupp.notMem_support_iff.mp hQ
        rw [h0]; norm_num
    rw [hsum] at h1
    exact_mod_cast h1
  calc ∑ E ∈ D, (E.intersectionLength T.idealSheaf.subschemeι Q : ℚ) * Θ.coeff E
      ≤ ∑ E ∈ D, (E.intersectionLength T.idealSheaf.subschemeι Q : ℚ) * ε :=
        Finset.sum_le_sum fun E _ => mul_le_mul_of_nonneg_left (hΘε E) (by positivity)
    _ = (∑ E ∈ D, (E.intersectionLength T.idealSheaf.subschemeι Q : ℚ)) * ε := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hle hε
    _ = ε := one_mul ε

end Restriction

section Bertini

/-- **A general member of a linear system misses a given point.** If one of finitely many
sections `t_i` of `𝒪_Y(D)`, `D` Cartier, has divisor of zeros missing `y`, then for `c` off the
zero set of a nonzero linear form, `∑ cᵢ tᵢ` is nonzero with divisor of zeros missing `y`. -/
private theorem exists_polynomial_notMem_supp_zeroDivisor {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (sY : Y ⟶ Spec (.of ℂ))
    {D : Divisor Y} (hD : D.IsCartier) {N : ℕ} (t : Fin (N + 1) → D.divisorialSubmodule ⊤)
    (y : Y) (j : Fin (N + 1)) (hj : t j ≠ 0) (hyj : y ∉ (D.zeroDivisor (t j) hj).supp) :
    ∃ P : MvPolynomial (Fin (N + 1)) ℂ, P ≠ 0 ∧ ∀ c : Fin (N + 1) → ℂ,
      MvPolynomial.eval c P ≠ 0 → ∃ hc : (∑ i, scalarsToGlobalSections ℂ sY (c i) • t i) ≠ 0,
        y ∉ (D.zeroDivisor _ hc).supp := by
  classical
  obtain ⟨W, hyW, ψ, hψ⟩ := hD y
  obtain ⟨C, hyC⟩ : ∃ C : irreducibleComponents Y, y ∈ C.1 := ⟨_, mem_pointComponent y⟩
  have hρinj : Function.Injective (stalkToRationalFunctions Y hyC).hom :=
    stalkToRationalFunctions_injective hyC
  -- the order of a section times the local equation along a prime divisor through `y`
  have hordσ : ∀ (σ : D.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (E : MMP.Mori.PrimeDivisor Y),
      y ∈ E.support → E.ord ((Divisor.isUnit_sectionToRationalFunctions hσ).unit * ψ) =
        (D.zeroDivisor σ hσ).coeff E := by
    intro σ hσ E hE
    rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor,
      MMP.Mori.PrimeDivisor.ord_mul, hψ E ⟨y, hE, hyW⟩]
  -- the stalk element of a section
  have hsec : ∀ σ : D.divisorialSubmodule ⊤, ∃ r : Y.presheaf.stalk y,
      (stalkToRationalFunctions Y hyC).hom r =
        Divisor.sectionToRationalFunctions σ C * (ψ : RationalFunctions Y) C := by
    intro σ
    by_cases hσ : σ = 0
    · refine ⟨0, ?_⟩
      subst hσ
      have : Divisor.sectionToRationalFunctions (0 : D.divisorialSubmodule ⊤) = 0 :=
        map_zero (rationalFunctionsPresheafTopEquiv Y)
      rw [map_zero, this]
      simp
    · obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hyC
        ((Divisor.isUnit_sectionToRationalFunctions hσ).unit * ψ) fun E hE => by
          rw [hordσ σ hσ E hE]
          exact Divisor.zeroDivisor_nonneg D σ hσ E
      exact ⟨r, hr⟩
  choose r hr using hsec
  -- the scalars and the linear combinations
  set e : ℂ →+* Y.presheaf.stalk y :=
    (Y.presheaf.Γgerm y).hom.comp (scalarsToGlobalSections ℂ sY) with he
  have hρe : ∀ s : Γ(Y, ⊤), (stalkToRationalFunctions Y hyC).hom ((Y.presheaf.Γgerm y).hom s) =
      (Y.presheaf.germ ⊤ (componentGenericPoint Y C) trivial).hom s := fun s =>
    congrArg (fun φ => φ.hom s) (Y.presheaf.germ_stalkSpecializes (U := ⊤) trivial
      ((isGenericPoint_componentGenericPoint Y C).specializes hyC))
  have hτC : ∀ c : Fin (N + 1) → ℂ,
      Divisor.sectionToRationalFunctions (∑ i, scalarsToGlobalSections ℂ sY (c i) • t i) C =
        ∑ i, (Y.presheaf.germ ⊤ (componentGenericPoint Y C) trivial).hom
          (scalarsToGlobalSections ℂ sY (c i)) * Divisor.sectionToRationalFunctions (t i) C := by
    intro c
    have hadd : Divisor.sectionToRationalFunctions
        (∑ i, scalarsToGlobalSections ℂ sY (c i) • t i) =
        ∑ i, Divisor.sectionToRationalFunctions (scalarsToGlobalSections ℂ sY (c i) • t i) := by
      unfold Divisor.sectionToRationalFunctions
      rw [Submodule.coe_sum, map_sum]
    rw [hadd, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hlin : ∀ c : Fin (N + 1) → ℂ, (stalkToRationalFunctions Y hyC).hom
      (∑ i, e (c i) * r (t i)) =
      Divisor.sectionToRationalFunctions (∑ i, scalarsToGlobalSections ℂ sY (c i) • t i) C *
        (ψ : RationalFunctions Y) C := by
    intro c
    rw [map_sum, hτC, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hr, he, RingHom.comp_apply, hρe, mul_assoc]
  -- the coefficient vectors along which the combination vanishes at `y`
  let p : Submodule ℂ (Fin (N + 1) → ℂ) :=
    { carrier := {c | ∑ i, e (c i) * r (t i) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Pi.add_apply, map_add, add_mul,
          Finset.sum_add_distrib] at *
        exact Ideal.add_mem _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro a c hc
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc] at *
        rw [← Finset.mul_sum]
        exact Ideal.mul_mem_left _ _ hc }
  have hjp : (Pi.single j 1 : Fin (N + 1) → ℂ) ∉ p := by
    intro h
    change ∑ i, e ((Pi.single j 1 : Fin (N + 1) → ℂ) i) * r (t i) ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) at h
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp),
      Pi.single_eq_same, map_one, one_mul] at h
    have hz : ∀ E : MMP.Mori.PrimeDivisor Y, y ∈ E.support →
        E.ord ((Divisor.isUnit_sectionToRationalFunctions hj).unit * ψ) = 0 := by
      intro E hE
      rw [hordσ _ hj E hE]
      by_contra h0
      exact hyj (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, h0, hE⟩)
    obtain ⟨a, ha⟩ := exists_unit_stalk_of_forall_ord_eq_zero hyC _ hz
    have hra : r (t j) = a := hρinj (by rw [hr, ha]; rfl)
    exact (IsLocalRing.mem_maximalIdeal _).mp h (hra ▸ a.isUnit)
  obtain ⟨ℓ, hℓ, hpℓ⟩ := Submodule.exists_le_ker_of_notMem hjp
  let P : MvPolynomial (Fin (N + 1)) ℂ :=
    ∑ i, MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c P = ℓ c := by
    intro c
    rw [LinearMap.pi_apply_eq_sum_univ ℓ c]
    simp only [P, MvPolynomial.eval_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 2
    ext k
    simp [Pi.single_apply, eq_comm]
  refine ⟨P, fun h => hℓ (by rw [← heval, h, map_zero]), fun c hc => ?_⟩
  have hcp : c ∉ p := fun h => hc (by rw [heval]; exact hpℓ h)
  have hunit : IsUnit (∑ i, e (c i) * r (t i)) := by
    by_contra h
    exact hcp ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hτ : (∑ i, scalarsToGlobalSections ℂ sY (c i) • t i) ≠ 0 := by
    intro h0
    have h1 := hlin c
    rw [h0] at h1
    have h2 : Divisor.sectionToRationalFunctions (0 : D.divisorialSubmodule ⊤) = 0 :=
      map_zero (rationalFunctionsPresheafTopEquiv Y)
    rw [h2] at h1
    have h3 : ∑ i, e (c i) * r (t i) = 0 := hρinj (by rw [h1, map_zero]; simp)
    exact hunit.ne_zero h3
  refine ⟨hτ, fun hmem => ?_⟩
  obtain ⟨E, hE0, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  apply hE0
  rw [← hordσ _ hτ E hyE]
  have hspec : E.genericPoint ⤳ y := specializes_iff_mem_closure.mpr (by
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact hyE)
  have hyE' : y ∈ E.component.1 := E.support_subset_component hyE
  obtain rfl : C = E.component := eq_of_mem_irreducibleComponents hyC hyE'
  refine E.ord_eq_zero_of_isUnit (a := (Y.presheaf.stalkSpecializes hspec).hom
    (∑ i, e (c i) * r (t i))) (hunit.map _) ?_
  rw [E.toComponent_stalkSpecializes hspec hyE', hlin c]
  rfl

end Bertini

/-! ### Ample twists of a pull-back and their free multiples -/

section AmpleTwists

open RingedSpaceModuleAdjunction

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIsoPullback {X Y : Scheme.{0}} (f : X ⟶ Y)
    (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- **Generating sections of a divisorial sheaf, in Weil form.** If finitely many global sections
generate `𝒪_Y(D)`, `D` Cartier, every point of `Y` lies off the divisor of zeros of one of them. -/
private theorem exists_fin_forall_notMem_supp_zeroDivisor {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {D : Divisor Y} (hD : D.IsCartier)
    (σ : D.divisorialSheaf.GeneratingSections) [Finite σ.I] :
    ∃ (n : ℕ) (t : Fin (n + 1) → D.divisorialSubmodule ⊤),
      ∀ y : Y, ∃ (i : Fin (n + 1)) (hi : t i ≠ 0), y ∉ (D.zeroDivisor (t i) hi).supp := by
  haveI := hD.isInvertibleModule_divisorialSheaf
  have hspan := (generates_iff_stalkwise_generates _ _ σ.s).mp σ.epi
  have key : ∀ y : Y, ∃ i, ∃ hi : ((σ.s i).eval (Opposite.op ⊤) : D.divisorialSubmodule ⊤) ≠ 0,
      y ∉ (D.zeroDivisor _ hi).supp := by
    intro y
    obtain ⟨i, hi⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top
      D.divisorialSheaf (fun j => (σ.s j).eval (Opposite.op ⊤)) y (hspan y)
    have hy : y ∈ Stacks.Ample.nonvanishingLocus D.divisorialSheaf ((σ.s i).eval (Opposite.op ⊤)) :=
      hi
    have hne : ((σ.s i).eval (Opposite.op ⊤) : D.divisorialSubmodule ⊤) ≠ 0 := by
      intro h0
      have h1 : Stacks.Ample.nonvanishingLocus D.divisorialSheaf
          ((σ.s i).eval (Opposite.op ⊤)) = ∅ := by
        rw [show ((σ.s i).eval (Opposite.op ⊤)) = (0 : Γ(D.divisorialSheaf, ⊤)) from h0]
        exact Stacks.Ample.nonvanishingLocus_zero _
      rw [h1] at hy
      exact hy
    refine ⟨i, hne, ?_⟩
    have h2 := MMP.Mori.Divisor.nonvanishingLocus_eq_compl_supp_zeroDivisor hD _ hne
    have hy' : y ∈ (((D.zeroDivisor _ hne).supp : Set Y)ᶜ) := h2 ▸ hy
    exact hy'
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  obtain ⟨i₀, -, -⟩ := key y₀
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin σ.I
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (fun h => (Fin.elim0 (h ▸ e i₀)))
  refine ⟨n, fun j => (σ.s (e.symm j)).eval (Opposite.op ⊤), fun y => ?_⟩
  obtain ⟨i, hi, hy⟩ := key y
  refine ⟨e i, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact ⟨hi, hy⟩

/-- **Ample twists of a pull-back, with free multiples** ([Stacks, Tags 0C4K and 01Q3]). Let
`μ : Y ⟶ X` and `f : X ⟶ Z` be quasi-compact, `Z` affine, `Y` a variety on which every divisor is
Cartier, `L₀` an `f`-ample Cartier divisor on `X` with pull-back `μ^*L₀` and `-F` a `μ`-ample
divisor on `Y`. For all large `N'`, some positive multiple `G` of `N' μ^*L₀ - F` is ample over
`Spec Γ(Z, 𝒪_Z)` and finitely many sections of `𝒪_Y(G)` have no common zero. -/
private theorem exists_isRelativelyAmpleCartier_smul_sub_and_free
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsAffine Z]
    {sY : Y ⟶ Spec (.of ℂ)} (hYv : AlgebraicGeometry.IsVariety ℂ sY)
    (hcart : ∀ D : Divisor Y, D.IsCartier)
    (μ : Y ⟶ X) [QuasiCompact μ] (f : X ⟶ Z) [QuasiCompact f]
    {L₀ : Divisor X} (hL₀c : L₀.IsCartier) (hL₀ : L₀.IsRelativelyAmple f hL₀c)
    {hB : ∀ Z' : irreducibleComponents Y, μ (componentGenericPoint Y Z') ∉ L₀.supp}
    {PL : Divisor Y} (hPL : L₀.IsPullback μ hB PL)
    {F : Divisor Y} (hF : MMP.Flips.IsRelativelyAmpleCartier μ (-F)) :
    ∃ n₀ : ℕ, ∀ N' : ℕ, n₀ ≤ N' → ∃ c : ℕ, 0 < c ∧
      MMP.Flips.IsRelativelyAmpleCartier (μ ≫ f ≫ Z.isoSpec.hom)
        ((c : ℤ) • ((N' : ℤ) • PL - F)) ∧
      ∃ (n : ℕ) (t : Fin (n + 1) → (((c : ℤ) • ((N' : ℤ) • PL - F)).divisorialSubmodule ⊤)),
        ∀ y : Y, ∃ (i : Fin (n + 1)) (hi : t i ≠ 0),
          y ∉ (Divisor.zeroDivisor _ (t i) hi).supp := by
  obtain ⟨hFc, hFamp⟩ := hF
  haveI := hFc.isInvertibleModule_divisorialSheaf
  haveI := hL₀c.isInvertibleModule_divisorialSheaf
  have hPLc : PL.IsCartier := hcart PL
  haveI := hPLc.isInvertibleModule_divisorialSheaf
  set g : X ⟶ Spec Γ(Z, ⊤) := f ≫ Z.isoSpec.hom with hg
  have hLS : Stacks.RelativeAmple.IsRelativelyAmple μ (-F).divisorialSheaf :=
    ⟨inferInstance, hFamp⟩
  have hMf : Stacks.RelativeAmple.IsRelativelyAmple f L₀.divisorialSheaf :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance hL₀
  have hMS : Stacks.RelativeAmple.IsRelativelyAmple g L₀.divisorialSheaf :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple g _).mpr
      ((Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f _).mp hMf)
  obtain ⟨n₀, hn₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp μ g _ _
    hLS hMS
  refine ⟨n₀, fun N' hN' => ?_⟩
  set G₁ : Divisor Y := (N' : ℤ) • PL - F with hG₁
  have hG₁c : G₁.IsCartier := hcart G₁
  haveI := hG₁c.isInvertibleModule_divisorialSheaf
  -- `𝒪_Y(-F) ⊗ μ^* 𝒪_X(L₀)^{⊗ N'} ≅ 𝒪_Y(G₁)`
  have eB : (modulePullback μ.toLRSHom.toShHom).obj L₀.divisorialSheaf ≅ PL.divisorialSheaf :=
    modulePullbackIsoPullback μ _ ≪≫ (hPL.divisorialSheafIso (hBc := hL₀c)).symm
  obtain ⟨eN⟩ := MMP.LcBpf.nonempty_tensorPowModule_iso_divisorialSheaf PL hPLc N'
  have hG₁eq : -F + N' • PL = G₁ := by
    rw [hG₁, Nat.cast_smul_eq_nsmul ℤ N' PL]
    abel
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule μ (-F).divisorialSheaf
      L₀.divisorialSheaf N' ≅ G₁.divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso μ _ N' ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso Y _ _ eB N' ≪≫ eN) ≪≫
      hFc.divisorialSheafTensorIso (hPLc.nsmul N') ≪≫ eqToIso (by rw [hG₁eq])
  have hGS : Stacks.RelativeAmple.IsRelativelyAmple (μ ≫ g) G₁.divisorialSheaf :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn₀ N' hN')
  -- Serre generation for `𝒪_Y(G₁) ⊗ 𝒪_Y(G₁)^{⊗ m} ≅ 𝒪_Y((m + 1) G₁)`
  have hGabs : Stacks.Ample.IsAmple Y G₁.divisorialSheaf :=
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (μ ≫ g) _).mp hGS
  haveI := (MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul sY hYv
    G₁ G₁).1
  have hqc := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    G₁.divisorialSheaf
  obtain ⟨m₀, hm₀⟩ :=
    (Stacks.AmpleLocalGeneration.quasiSeparatedSpace_and_isEventuallyGloballyGenerated_of_isAmple
      _ hGabs).2 G₁.divisorialSheaf hqc.1 hqc.2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m₀ ≤ (m : ℤ) := ⟨m₀.toNat, Int.self_le_toNat m₀⟩
  obtain ⟨σ, hσ⟩ := hm₀ (m : ℤ) hm
  set c : ℕ := m + 1 with hc
  have hcG : ((c : ℤ) • G₁).IsCartier := hcart _
  haveI := hcG.isInvertibleModule_divisorialSheaf
  have hceq : G₁ + m • G₁ = (c : ℤ) • G₁ := by
    rw [hc, Nat.cast_smul_eq_nsmul ℤ (m + 1) G₁, succ_nsmul']
  have hceq' : c • G₁ = (c : ℤ) • G₁ := (Nat.cast_smul_eq_nsmul ℤ c G₁).symm
  -- the ampleness of `c G₁`
  obtain ⟨eC⟩ := MMP.LcBpf.nonempty_tensorPowModule_iso_divisorialSheaf G₁ hG₁c c
  have hcS : Stacks.RelativeAmple.IsRelativelyAmple (μ ≫ g) ((c : ℤ) • G₁).divisorialSheaf :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ (eC ≪≫ eqToIso (by rw [hceq']))).mp
      (Stacks.Tag01VUReduction.isRelativelyAmple_tensorPowModule_of_isRelativelyAmple _ _ c
        (by omega) hGS)
  -- the generating sections of `𝒪_Y(c G₁)`
  obtain ⟨eM⟩ := MMP.LcBpf.nonempty_tensorPowModule_iso_divisorialSheaf G₁ hG₁c m
  letI := Stacks.SheafInternalHom.schemeMonoidalCategory Y
  let pI := Stacks.TensorSheafSpellingIso.monoidalTensorIso Y G₁.divisorialSheaf
      (Stacks.Ample.tensorPowModule Y G₁.divisorialSheaf (m : ℤ)) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso Y (Iso.refl _) eM ≪≫
    hG₁c.divisorialSheafTensorIso (hG₁c.nsmul m) ≪≫ eqToIso (by rw [hceq])
  let p := pI.hom
  haveI : @Epi (SheafOfModules.{0} Y.ringCatSheaf) _ _ _ p :=
    @IsIso.epi_of_iso _ _ _ _ p inferInstance
  haveI : Finite (σ.ofEpi p).I := hσ
  obtain ⟨n, t, ht⟩ := exists_fin_forall_notMem_supp_zeroDivisor hcG (σ.ofEpi p)
  exact ⟨c, by omega, ⟨hcG, hcS.2⟩, n, t, ht⟩

end AmpleTwists

/-- **The prepared boundary is plt, for `N'` large.** On a smooth variety `Y` with a canonical
divisor `K_Y`, let `Γ₀ ≥ 0` have coefficient one along a smooth prime divisor `T` and coefficients
less than one elsewhere, supported in an snc set `S₀ ∋ T`, with `((Γ₀ - T)|_T)` terminal, and let
`F₀` be supported in `S₀` off `T`. For all large `N'`, every `c > 0` and every reduced `H ≥ 0`
with no component in `S₀` and `S₀ + H` snc, the boundary `T + H/(cN'm₀) + (Γ₀ - T) + F₀⁺/(N'm₀)`
has round-down `T` and is plt, with `H/(cN'm₀)` added once more, and its restriction to `T`
(with `2H/(cN'm₀)`) is canonical. -/
private theorem exists_bound_isPltPair_preparedBoundary
    {d : ℕ} (hd : 2 ≤ d) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [DecidableEq (MMP.Mori.PrimeDivisor Y)] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : IsNormalVariety ℂ sY) (hsm : IsSmoothScheme sY) (hdimY : topologicalKrullDim Y = d + 1)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY (d + 1))
    (T : MMP.Mori.PrimeDivisor Y) (Γ₀ : QDivisor Y) (F₀ : Divisor Y)
    (S₀ : Finset (MMP.Mori.PrimeDivisor Y)) {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hΓ₀ : 0 ≤ Γ₀) (hΓT : Γ₀.coeff T = 1) (hΓlt : ∀ P, P ≠ T → Γ₀.coeff P < 1)
    (hTsm : IsSmoothScheme (T.idealSheaf.subschemeι ≫ sY))
    (hΨsnc : ((Γ₀ - Finsupp.single T 1).restrictPrimeDivisor T).IsSNC
      (T.idealSheaf.subschemeι ≫ sY))
    [IsIntegral T.idealSheaf.subscheme] [IsLocallyNoetherian T.idealSheaf.subscheme]
    [IsNormal T.idealSheaf.subscheme]
    (hTterm : IsRealTerminalPair (T.idealSheaf.subschemeι ≫ sY)
        (QDivisor.toRDivisor ((Γ₀ - Finsupp.single T 1).restrictPrimeDivisor T)))
    (hFT : F₀.coeff T = 0) (hTS₀ : T ∈ S₀) (hΓS₀ : ∀ P, Γ₀.coeff P ≠ 0 → P ∈ S₀)
    (hFS₀ : ∀ P, F₀.coeff P ≠ 0 → P ∈ S₀) :
    ∃ n₁ : ℕ, ∀ N' c : ℕ, n₁ ≤ N' → 0 < c → ∀ H : Divisor Y, 0 ≤ H →
      (∀ P, H.coeff P ≤ 1) → (∀ P, H.coeff P ≠ 0 → P ∉ S₀) →
      DivisorWithCoeffs.IsSNC sY (∑ P ∈ S₀ ∪ H.support, Finsupp.single P (1 : ℤ)) →
      (Divisor.toQDivisor (Finsupp.single T 1) + ((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H +
          ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
            ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))).roundDown = Finsupp.single T 1 ∧
        IsPltPair sY (d + 1) KY (Divisor.toQDivisor (Finsupp.single T 1) +
          ((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H +
          ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
            ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))) ∧
        IsPltPair sY (d + 1) KY (Divisor.toQDivisor (Finsupp.single T 1) +
          ((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H +
          ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
            ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)) +
          ((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H) ∧
        ∃ KS : Divisor T.idealSheaf.subscheme,
          IsCanonicalPair (T.idealSheaf.subschemeι ≫ sY) d KS
            ((2 • (((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H) +
              ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
                ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))).restrictPrimeDivisor T) := by
  classical
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  -- the bound `m < 1` on the coefficients of `Γ₀` off `T`, and the size of `F₀`
  obtain ⟨mΓ, hmΓ0, hmΓ1, hmΓ⟩ := exists_lt_one_forall_le (S₀.erase T) Γ₀.coeff
    fun E hE => hΓlt E (Finset.ne_of_mem_erase hE)
  set MF : ℚ := ∑ E ∈ S₀, max ((F₀.coeff E : ℤ) : ℚ) 0 with hMF
  have hMF0 : 0 ≤ MF := Finset.sum_nonneg fun E _ => le_max_right _ _
  have hFle : ∀ E, max ((F₀.coeff E : ℤ) : ℚ) 0 ≤ MF := by
    intro E
    by_cases hE : E ∈ S₀
    · exact Finset.single_le_sum (f := fun E => max ((F₀.coeff E : ℤ) : ℚ) 0)
        (fun E _ => le_max_right _ _) hE
    · have : F₀.coeff E = 0 := by
        by_contra h0
        exact hE (hFS₀ E h0)
      rw [this]
      simpa using hMF0
  obtain ⟨n₁a, hn₁a⟩ := exists_nat_gt (MF / (1 - mΓ))
  obtain ⟨n₁b, hcanT⟩ : ∃ n₁b : ℕ, ∀ N' c : ℕ, n₁b ≤ N' → 0 < c → ∀ H : Divisor Y, 0 ≤ H →
      (∀ P, H.coeff P ≤ 1) → (∀ P, H.coeff P ≠ 0 → P ∉ S₀) →
      DivisorWithCoeffs.IsSNC sY (∑ P ∈ S₀ ∪ H.support, Finsupp.single P (1 : ℤ)) →
      ∃ KS : Divisor T.idealSheaf.subscheme,
        IsCanonicalPair (T.idealSheaf.subschemeι ≫ sY) d KS
          ((2 • (((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H) +
            ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
              ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))).restrictPrimeDivisor T) := by
    -- the strict transform `T`, a smooth variety of dimension `d`
    have hTnv' : IsNormalVariety ℂ (T.idealSheaf.subschemeι ≫ sY) := by
      haveI : AlgebraicGeometry.IsVariety ℂ sY := hY.1
      exact ⟨⟨⟩, inferInstance⟩
    haveI : QuasiCompact (T.idealSheaf.subschemeι ≫ sY) := hTnv'.1.toQuasiCompact
    haveI : CompactSpace T.idealSheaf.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace (T.idealSheaf.subschemeι ≫ sY)
    have hdimT : topologicalKrullDim T.idealSheaf.subscheme = d :=
      topologicalKrullDim_subscheme_primeDivisor sY hdimY T
    obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety
      (T.idealSheaf.subschemeι ≫ sY) hTnv' hdimT
    have hTQ : Divisor.toQDivisor (Finsupp.single T (1 : ℤ)) = Finsupp.single T (1 : ℚ) := by
      refine DivisorWithCoeffs.ext' fun E => ?_
      rw [Divisor.coeff_toQDivisor]
      by_cases h : T = E
      · subst h
        rw [DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_self,
          Int.cast_one]
      · rw [DivisorWithCoeffs.coeff_single_of_ne h, DivisorWithCoeffs.coeff_single_of_ne h,
          Int.cast_zero]
    have hΨ₀snc : ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)).restrictPrimeDivisor T).IsSNC
        (T.idealSheaf.subschemeι ≫ sY) := by
      rw [hTQ]; exact hΨsnc
    have hΨ₀term : IsRealTerminalPair (T.idealSheaf.subschemeι ≫ sY)
        (QDivisor.toRDivisor
          ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)).restrictPrimeDivisor T)) := by
      rw [hTQ]; exact hTterm
    obtain ⟨ε, hε, hA⟩ :=
      exists_pos_forall_zero_le_discrep_add hTnv' hTsm hd hKT hΨ₀snc hΨ₀term
    refine ⟨⌈(2 + MF) / ε⌉₊ + 1, fun N' c hN' hc H hH0 hH1 hHS₀ hHsnc => ⟨KT, ?_⟩⟩
    have hN'pos : (0 : ℚ) < N' := by exact_mod_cast (by omega : 0 < N')
    have hN'ε : (2 + MF) / ε < N' := by
      have h1 := Nat.le_ceil ((2 + MF) / ε)
      have h2 : ((⌈(2 + MF) / ε⌉₊ + 1 : ℕ) : ℚ) ≤ N' := by exact_mod_cast hN'
      push_cast at h2
      linarith
    have hm₀1 : (1 : ℚ) ≤ m₀ := by exact_mod_cast hm₀
    have hc1 : (1 : ℚ) ≤ c := by exact_mod_cast hc
    have hHT : H.coeff T = 0 := by
      by_contra h
      exact hHS₀ T h hTS₀
    have hmaxc' : ∀ P, (((F₀ ⊔ 0 : Divisor Y).coeff P : ℤ) : ℚ) =
        max ((F₀.coeff P : ℤ) : ℚ) 0 := fun P => by
      change (((F₀ ⊔ 0 : Divisor Y) P : ℤ) : ℚ) = _
      rw [Finsupp.sup_apply]
      push_cast
      rfl
    -- the perturbation `Θ` of `Γ₀ - T`
    set Θ : QDivisor Y := 2 • (((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H) +
      ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0) with hΘdef
    have hΘc : ∀ P, Θ.coeff P = 2 * (((c * N' * m₀ : ℕ) : ℚ)⁻¹ * ((H.coeff P : ℤ) : ℚ)) +
        ((N' * m₀ : ℕ) : ℚ)⁻¹ * max ((F₀.coeff P : ℤ) : ℚ) 0 := by
      intro P
      simp only [hΘdef, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        Divisor.coeff_toQDivisor, smul_eq_mul, nsmul_eq_mul, hmaxc']
      push_cast
      ring
    have hΘ0 : ∀ P, 0 ≤ Θ.coeff P := fun P => by
      rw [hΘc]
      have h1 : (0 : ℚ) ≤ ((H.coeff P : ℤ) : ℚ) := by exact_mod_cast hH0 P
      exact add_nonneg (mul_nonneg zero_le_two (mul_nonneg (by positivity) h1))
        (mul_nonneg (by positivity) (le_max_right _ _))
    have hΘε : ∀ P, Θ.coeff P ≤ ε := fun P => by
      rw [hΘc]
      have h1 : ((H.coeff P : ℤ) : ℚ) ≤ 1 := by exact_mod_cast hH1 P
      have hA1 : ((c * N' * m₀ : ℕ) : ℚ)⁻¹ ≤ (N' : ℚ)⁻¹ := by
        push_cast
        apply inv_anti₀ hN'pos
        have : (N' : ℚ) ≤ c * N' := le_mul_of_one_le_left hN'pos.le hc1
        nlinarith
      have hA2 : ((N' * m₀ : ℕ) : ℚ)⁻¹ ≤ (N' : ℚ)⁻¹ := by
        push_cast
        exact inv_anti₀ hN'pos (le_mul_of_one_le_right hN'pos.le hm₀1)
      have hF := hFle P
      have hmax0 : 0 ≤ max ((F₀.coeff P : ℤ) : ℚ) 0 := le_max_right _ _
      have e1 : ((c * N' * m₀ : ℕ) : ℚ)⁻¹ * ((H.coeff P : ℤ) : ℚ) ≤ (N' : ℚ)⁻¹ :=
        calc _ ≤ ((c * N' * m₀ : ℕ) : ℚ)⁻¹ * 1 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (N' : ℚ)⁻¹ := by rw [mul_one]; exact hA1
      have e2 : ((N' * m₀ : ℕ) : ℚ)⁻¹ * max ((F₀.coeff P : ℤ) : ℚ) 0 ≤ (N' : ℚ)⁻¹ * MF :=
        mul_le_mul hA2 hF hmax0 (by positivity)
      have hεN : (2 + MF) * (N' : ℚ)⁻¹ ≤ ε := by
        rw [← div_eq_mul_inv, div_le_iff₀ hN'pos]
        rw [div_lt_iff₀ hε] at hN'ε
        linarith
      nlinarith
    -- the support `D` of `Γ₀ - T + Θ` off `T`
    set D : Finset (MMP.Mori.PrimeDivisor Y) := (S₀ ∪ H.support).erase T with hDdef
    have hTD : T ∉ D := Finset.notMem_erase T _
    have hTmem : T ∈ S₀ ∪ H.support := Finset.mem_union_left _ hTS₀
    have hsncD : DivisorWithCoeffs.IsSNC sY
        (Finsupp.single T (1 : ℤ) + ∑ E ∈ D, Finsupp.single E (1 : ℤ)) := by
      have h : Finsupp.single T (1 : ℤ) +
          ∑ E ∈ (S₀ ∪ H.support).erase T, Finsupp.single E (1 : ℤ) =
          ∑ E ∈ S₀ ∪ H.support, Finsupp.single E (1 : ℤ) :=
        Finset.add_sum_erase _ (fun E => Finsupp.single E (1 : ℤ)) hTmem
      rw [hDdef, h]
      exact hHsnc
    haveI : AlgebraicGeometry.IsVariety ℂ sY := hY.1
    haveI : Smooth sY := by
      first
        | exact (MMP.Mori.isSmoothScheme_iff sY).mp hsm
        | exact MMP.Mori.isSmoothScheme_iff.mp hsm
    obtain ⟨hSTsnc, hST1⟩ :=
      DivisorWithCoeffs.isSNC_restrictPrimeDivisor_sum_single sY T D hTD hsncD
    have hΘD : Θ.support ⊆ D := by
      intro P hP
      have hP' : Θ.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
      have hPT : P ≠ T := by
        rintro rfl
        apply hP'
        rw [hΘc, hHT, hFT]
        simp
      refine Finset.mem_erase.mpr ⟨hPT, ?_⟩
      by_cases hHP : H.coeff P = 0
      · have hFP : F₀.coeff P ≠ 0 := by
          intro hFP
          apply hP'
          rw [hΘc, hHP, hFP]
          simp
        exact Finset.mem_union_left _ (hFS₀ P hFP)
      · exact Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hHP)
    have hΓD : (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)).support ⊆ D := by
      intro P hP
      have hP' : (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)).coeff P ≠ 0 :=
        Finsupp.mem_support_iff.mp hP
      rw [DivisorWithCoeffs.coeff_sub, hTQ] at hP'
      by_cases hPT : P = T
      · subst hPT
        rw [DivisorWithCoeffs.coeff_single_self, hΓT, sub_self] at hP'
        exact absurd rfl hP'
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPT), sub_zero] at hP'
        exact Finset.mem_erase.mpr ⟨hPT, Finset.mem_union_left _ (hΓS₀ P hP')⟩
    have hΓT0 : (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)).coeff T = 0 := by
      rw [DivisorWithCoeffs.coeff_sub, hTQ, DivisorWithCoeffs.coeff_single_self, hΓT, sub_self]
    have hΘT : Θ.coeff T = 0 := by
      rw [hΘc, hHT, hFT]
      simp
    have hrest : (2 • (((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H) +
        ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
          ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))).restrictPrimeDivisor T =
        (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)).restrictPrimeDivisor T +
          Θ.restrictPrimeDivisor T := by
      rw [show 2 • (((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H) +
          ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
            ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)) =
          (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) + Θ by rw [hΘdef]; abel]
      exact DivisorWithCoeffs.restrictPrimeDivisor_add _ _ T hΓT0 hΘT
    rw [hrest]
    refine ⟨⟨hTnv', hKT, isQCartier_of_isSmoothScheme hTsm _⟩, ?_⟩
    have hSTsnc' : DivisorWithCoeffs.IsSNC (T.idealSheaf.subschemeι ≫ sY)
        (∑ Q ∈ (DivisorWithCoeffs.restrictPrimeDivisor
          (∑ E ∈ D, Finsupp.single E (1 : ℤ) : Divisor Y) T).support,
            Finsupp.single Q (1 : ℤ)) :=
      (DivisorWithCoeffs.isSNC_iff_of_support_eq (support_sum_single_one _)).mpr hSTsnc
    refine hA _ hSTsnc' _ ?_
      (fun Q => (coeff_restrictPrimeDivisor_mem_Icc D T hTD hST1 Θ hΘD hε.le hΘ0 hΘε Q).1)
      (fun Q => (coeff_restrictPrimeDivisor_mem_Icc D T hTD hST1 Θ hΘD hε.le hΘ0 hΘε Q).2)
    refine Finsupp.support_add.trans (Finset.union_subset ?_ ?_)
    · exact support_restrictPrimeDivisor_subset D T hTD _ hΓD
    · exact support_restrictPrimeDivisor_subset D T hTD _ hΘD
  refine ⟨max (max n₁a n₁b) 3, fun N' c hN' hc H hH0 hH1 hHS₀ hHsnc => ?_⟩
  have hN'a : n₁a ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN'
  have hN'b : n₁b ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN'
  have hN'3 : 3 ≤ N' := le_trans (le_max_right _ _) hN'
  have hN'0 : (0 : ℚ) < N' := by exact_mod_cast (by omega : 0 < N')
  have hm₀1 : (1 : ℚ) ≤ m₀ := by exact_mod_cast hm₀
  have hc1 : (1 : ℚ) ≤ c := by exact_mod_cast hc
  set t : ℚ := ((N' * m₀ : ℕ) : ℚ)⁻¹ with ht
  set a : ℕ := c * N' * m₀ with ha
  have ht0 : 0 ≤ t := by positivity
  have htMF : t * MF < 1 - mΓ := by
    have h1 : t ≤ (N' : ℚ)⁻¹ := by
      rw [ht]
      push_cast
      exact inv_anti₀ hN'0 (le_mul_of_one_le_right hN'0.le hm₀1)
    have h2 : MF / (1 - mΓ) < N' := lt_of_lt_of_le hn₁a (by exact_mod_cast hN'a)
    have h3 : MF < (1 - mΓ) * N' := by
      rw [div_lt_iff₀ (by linarith)] at h2
      linarith
    calc t * MF ≤ (N' : ℚ)⁻¹ * MF := mul_le_mul_of_nonneg_right h1 hMF0
      _ < (N' : ℚ)⁻¹ * ((1 - mΓ) * N') := mul_lt_mul_of_pos_left h3 (by positivity)
      _ = 1 - mΓ := by field_simp
  have ha3 : (3 : ℚ) ≤ a := by
    rw [ha]
    push_cast
    have h3 : (3 : ℚ) ≤ N' := by exact_mod_cast hN'3
    have h1 : (N' : ℚ) ≤ c * N' := le_mul_of_one_le_left (by positivity) hc1
    have h2 : (c * N' : ℚ) ≤ c * N' * m₀ := le_mul_of_one_le_right (by positivity) hm₀1
    linarith
  have hHT : H.coeff T = 0 := by
    by_contra h
    exact hHS₀ T h hTS₀
  have hHcomp : ∀ E, H.coeff E ≠ 0 →
      Γ₀.coeff E = 0 ∧ F₀.coeff E = 0 ∧ H.coeff E = 1 ∧ E ≠ T := by
    intro E hE
    have hES : E ∉ S₀ := hHS₀ E hE
    refine ⟨?_, ?_, ?_, fun h => hES (h ▸ hTS₀)⟩
    · by_contra h
      exact hES (hΓS₀ E h)
    · by_contra h
      exact hES (hFS₀ E h)
    · have h0 : 0 ≤ H.coeff E := hH0 E
      have := hH1 E
      omega
  have hoff : ∀ E, E ≠ T → H.coeff E = 0 →
      Γ₀.coeff E + t * max ((F₀.coeff E : ℤ) : ℚ) 0 < 1 := by
    intro E hET _
    by_cases hE : E ∈ S₀
    · have h1 := hmΓ E (Finset.mem_erase.mpr ⟨hET, hE⟩)
      have h2 : t * max ((F₀.coeff E : ℤ) : ℚ) 0 ≤ t * MF :=
        mul_le_mul_of_nonneg_left (hFle E) ht0
      linarith
    · have hΓE : Γ₀.coeff E = 0 := by
        by_contra h
        exact hE (hΓS₀ E h)
      have hFE : F₀.coeff E = 0 := by
        by_contra h
        exact hE (hFS₀ E h)
      rw [hΓE, hFE]
      simp
  have hcoef := fun (s' : ℚ) E => coeff_preparedBoundary T H F₀ Γ₀ s' t E
  have hΓ0 : ∀ E, 0 ≤ Γ₀.coeff E := fun E => hΓ₀ E
  -- the coefficients of the boundaries `Δ_Y + j A_Y`, `j = 1, 2`
  have hbounds : ∀ s' : ℚ, 0 ≤ s' → s' < 1 → ∀ E,
      0 ≤ s' * H.coeff E + Γ₀.coeff E + t * max ((F₀.coeff E : ℤ) : ℚ) 0 ∧
      (E = T → s' * H.coeff E + Γ₀.coeff E + t * max ((F₀.coeff E : ℤ) : ℚ) 0 = 1) ∧
      (E ≠ T → s' * H.coeff E + Γ₀.coeff E + t * max ((F₀.coeff E : ℤ) : ℚ) 0 < 1) := by
    intro s' hs0 hs1 E
    have hHE0 : (0 : ℚ) ≤ H.coeff E := by exact_mod_cast hH0 E
    refine ⟨add_nonneg (add_nonneg (mul_nonneg hs0 hHE0) (hΓ0 E))
      (mul_nonneg ht0 (le_max_right _ _)), fun hE => ?_, fun hE => ?_⟩
    · subst hE
      rw [hHT, hFT, hΓT]
      simp
    · by_cases hHE : H.coeff E = 0
      · rw [hHE]
        simpa using hoff E hE hHE
      · obtain ⟨hΓE, hFE, hH1E, -⟩ := hHcomp E hHE
        rw [hΓE, hFE, hH1E]
        simpa using hs1
  have hsupp : ∀ s' : ℚ, ∀ E, s' * H.coeff E + Γ₀.coeff E + t * max ((F₀.coeff E : ℤ) : ℚ) 0 ≠ 0 →
      E ∈ S₀ ∪ H.support := by
    intro s' E hE
    rw [Finset.mem_union]
    by_cases hHE : H.coeff E = 0
    · left
      by_contra hES
      have hΓE : Γ₀.coeff E = 0 := by
        by_contra h
        exact hES (hΓS₀ E h)
      have hFE : F₀.coeff E = 0 := by
        by_contra h
        exact hES (hFS₀ E h)
      apply hE
      rw [hHE, hΓE, hFE]
      simp
    · exact Or.inr (Finsupp.mem_support_iff.mpr hHE)
  have hplt_of : ∀ s' : ℚ, 0 ≤ s' → s' < 1 →
      IsPltPair sY (d + 1) KY (Divisor.toQDivisor (Finsupp.single T 1) +
        s' • Divisor.toQDivisor H + ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
          t • Divisor.toQDivisor (F₀ ⊔ 0))) := by
    intro s' hs0 hs1
    refine ⟨⟨hY, hKY, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩, ?_⟩
    rw [MMP.Mori.discrep_eq_of_isSNC sY hY hsm (by omega) hKY (S₀ ∪ H.support)
      (fun E hE => hsupp s' E (by
        rw [← hcoef]
        exact Finsupp.mem_support_iff.mp hE)) hHsnc
      (fun E _ => by
        rw [hcoef]
        by_cases hET : E = T
        · exact ((hbounds s' hs0 hs1 E).2.1 hET).le
        · exact ((hbounds s' hs0 hs1 E).2.2 hET).le)]
    refine neg_one_lt_snc_inf _ T _ _ (fun E _ => ?_) (fun E _ hET => ?_)
    · rw [hcoef]
      by_cases hET : E = T
      · exact ((hbounds s' hs0 hs1 E).2.1 hET).le
      · exact ((hbounds s' hs0 hs1 E).2.2 hET).le
    · rw [hcoef]
      exact (hbounds s' hs0 hs1 E).2.2 hET
  have ha1 : (a : ℚ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have ha2 : 2 * (a : ℚ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by linarith)]
    linarith
  refine ⟨?_, ?_, ?_, hcanT N' c hN'b hc H hH0 hH1 hHS₀ hHsnc⟩
  · refine Finsupp.ext fun E => ?_
    change (DivisorWithCoeffs.roundDown _).coeff E =
      DivisorWithCoeffs.coeff (Finsupp.single T (1 : ℤ) : Divisor Y) E
    rw [DivisorWithCoeffs.coeff_roundDown, hcoef]
    obtain ⟨h0, hT, hnT⟩ := hbounds _ (by positivity) ha1 E
    by_cases hET : E = T
    · rw [hT hET, hET]
      simp [DivisorWithCoeffs.coeff_apply]
    · rw [Int.floor_eq_zero_iff.mpr ⟨h0, hnT hET⟩]
      simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, Ne.symm hET]
  · exact hplt_of _ (by positivity) ha1
  · have heq : Divisor.toQDivisor (Finsupp.single T 1) + (a : ℚ)⁻¹ • Divisor.toQDivisor H +
        ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) + t • Divisor.toQDivisor (F₀ ⊔ 0)) +
        (a : ℚ)⁻¹ • Divisor.toQDivisor H =
        Divisor.toQDivisor (Finsupp.single T 1) + (2 * (a : ℚ)⁻¹) • Divisor.toQDivisor H +
        ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) + t • Divisor.toQDivisor (F₀ ⊔ 0)) := by
      rw [two_mul, add_smul]
      abel
    rw [heq]
    exact hplt_of _ (by positivity) ha2

/-- A common denominator: some positive multiple of two `ℚ`-divisors is integral. -/
private theorem exists_pos_toQDivisor_eq_smul_smul {Y : Scheme.{0}} (Γ₀ E : QDivisor Y) :
    ∃ d₀ : ℕ, 0 < d₀ ∧
      (∃ Γ₀' : Divisor Y, Divisor.toQDivisor Γ₀' = (d₀ : ℤ) • Γ₀) ∧
      ∃ E₀' : Divisor Y, Divisor.toQDivisor E₀' = (d₀ : ℤ) • E := by
  classical
  set d₀ : ℕ := (∏ P ∈ Γ₀.support, (Γ₀.coeff P).den) * ∏ P ∈ E.support, (E.coeff P).den
  have hdvd : ∀ (G : QDivisor Y) (P : MMP.Mori.PrimeDivisor Y),
      G.coeff P ≠ 0 → (∏ Q ∈ G.support, (G.coeff Q).den) ∣ d₀ →
      ∃ z : ℤ, (d₀ : ℚ) * G.coeff P = z := by
    intro G P hP hG
    have h1 : (G.coeff P).den ∣ d₀ :=
      (Finset.dvd_prod_of_mem (fun Q => (G.coeff Q).den)
        (Finsupp.mem_support_iff.mpr hP)).trans hG
    obtain ⟨k, hk⟩ := h1
    refine ⟨(G.coeff P).num * k, ?_⟩
    rw [hk]
    push_cast
    linear_combination (k : ℚ) * Rat.mul_den_eq_num (G.coeff P)
  have hint : ∀ G : QDivisor Y, (∏ Q ∈ G.support, (G.coeff Q).den) ∣ d₀ →
      ∃ G' : Divisor Y, Divisor.toQDivisor G' = (d₀ : ℤ) • G := by
    intro G hG
    choose! z hz using fun P (hP : G.coeff P ≠ 0) => hdvd G P hP hG
    refine ⟨Finsupp.onFinset G.support (fun P => if G.coeff P = 0 then 0 else z P) ?_, ?_⟩
    · intro P hP
      by_contra h
      exact hP (if_pos (Finsupp.notMem_support_iff.mp h))
    · refine Finsupp.ext fun P => ?_
      change ((DivisorWithCoeffs.coeff (Finsupp.onFinset _ _ _ : Divisor Y) P : ℤ) : ℚ) =
        ((d₀ : ℤ) • G).coeff P
      rw [DivisorWithCoeffs.coeff_smul]
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.onFinset_apply]
      by_cases h : G P = 0
      · simp only [h, ↓reduceIte, Int.cast_zero, smul_zero]
      · simp only [h, ↓reduceIte]
        rw [← hz P h, zsmul_eq_mul]
        push_cast; rfl
  refine ⟨d₀, Nat.pos_of_ne_zero (by
    simp only [d₀, ne_eq, mul_eq_zero, Finset.prod_eq_zero_iff, not_or]
    exact ⟨fun ⟨P, _, h⟩ => (Γ₀.coeff P).den_nz h, fun ⟨P, _, h⟩ => (E.coeff P).den_nz h⟩),
    hint Γ₀ (dvd_mul_right _ _), hint E (dvd_mul_left _ _)⟩

open Classical in
/-- **A general member of a free linear system** ([Bertini]). If finitely many sections of
`𝒪_Y(G)`, `G` on a smooth variety, have no common zero, a general member `H` of their span is
reduced, has no component in a given snc set `S₀`, makes `S₀ + H` snc, and misses finitely
many given points. -/
private theorem exists_generalMember_isSNC_notMem_supp {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY) (hsm : IsSmoothScheme sY) (G : Divisor Y)
    {n : ℕ}
    (tG : Fin (n + 1) → G.divisorialSubmodule ⊤)
    (htG : ∀ y : Y, ∃ (i : Fin (n + 1)) (hi : tG i ≠ 0), y ∉ (G.zeroDivisor (tG i) hi).supp)
    (S₀ : Finset (MMP.Mori.PrimeDivisor Y))
    (hS₀snc : DivisorWithCoeffs.IsSNC sY (∑ P ∈ S₀, Finsupp.single P (1 : ℤ))) (Ξ : Finset Y) :
    ∃ (τ : G.divisorialSubmodule ⊤) (hτ : τ ≠ 0),
      (∀ P, (G.zeroDivisor τ hτ).coeff P ≤ 1) ∧
      (∀ P, (G.zeroDivisor τ hτ).coeff P ≠ 0 → P ∉ S₀) ∧
      DivisorWithCoeffs.IsSNC sY
        (∑ P ∈ S₀ ∪ (G.zeroDivisor τ hτ).support, Finsupp.single P (1 : ℤ)) ∧
      ∀ y ∈ Ξ, y ∉ (G.zeroDivisor τ hτ).supp := by
  classical
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  have hGc : G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm G
  have htG' : ∀ y : Y, ∃ (i : Fin (n + 1)) (hi : tG i ≠ 0),
      y ∉ (G.zeroDivisor (tG i) hi).supp := htG
  -- a general member is reduced, snc with `S₀` and has no component in `S₀`
  obtain ⟨P₂, hP₂, hsncB⟩ : ∃ P₂ : MvPolynomial (Fin (n + 1)) ℂ, P₂ ≠ 0 ∧
      ∀ c' : Fin (n + 1) → ℂ, MvPolynomial.eval c' P₂ ≠ 0 →
        ∀ hτ' : (∑ i, scalarsToGlobalSections ℂ sY (c' i) • tG i) ≠ 0,
          (∀ E, (G.zeroDivisor _ hτ').coeff E ≤ 1) ∧ ∃ T' : Finset (MMP.Mori.PrimeDivisor Y),
            (∀ E, (G.zeroDivisor _ hτ').coeff E ≠ 0 → E ∈ T') ∧ Disjoint T' S₀ ∧
            DivisorWithCoeffs.IsSNC sY (∑ E ∈ T' ∪ S₀, Finsupp.single E (1 : ℤ)) := by
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : AlgebraicGeometry.IsVariety ℂ sY := hY.1
    haveI : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).mp hsm
    haveI : IsSmoothVariety ℂ (Y ↘ Spec (.of ℂ)) :=
      { toIsVariety := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY),
        toSmooth := (inferInstance : Smooth sY) }
    obtain ⟨Q, hQ0, hQ⟩ := MMP.Mori.exists_polynomial_zeroDivisor_eq_sum_isSNC (k := ℂ)
      (Y := Y) G hGc tG htG' S₀ hS₀snc
    refine ⟨Q, hQ0, fun c' hc' hτ' => ?_⟩
    obtain ⟨T', hT', hT'S, hsncT', -⟩ := hQ c' hc' hτ'
    refine ⟨fun E => ?_, T', fun E hE => ?_, hT'S, hsncT'⟩
    · refine (congrArg (fun D : Divisor Y => D.coeff E) hT').trans_le ?_
      change (∑ E' ∈ T', Finsupp.single E' (1 : ℤ)) E ≤ 1
      rw [Finsupp.finset_sum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    by_contra hET
    apply hE
    refine (congrArg (fun D : Divisor Y => D.coeff E) hT').trans ?_
    change (∑ E ∈ T', Finsupp.single E (1 : ℤ)) E = 0
    rw [Finsupp.finset_sum_apply]
    exact Finset.sum_eq_zero fun E' hE' => Finsupp.single_eq_of_ne (by
      rintro rfl
      exact hET hE')
  -- a general member misses any given point
  have hav : ∀ y : Y, ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧
      ∀ c' : Fin (n + 1) → ℂ, MvPolynomial.eval c' P ≠ 0 →
        ∃ hc' : (∑ i, scalarsToGlobalSections ℂ sY (c' i) • tG i) ≠ 0,
          y ∉ (G.zeroDivisor _ hc').supp := fun y => by
    obtain ⟨j, hj, hyj⟩ := htG' y
    exact exists_polynomial_notMem_supp_zeroDivisor sY hGc tG y j hj hyj
  choose Pav hPav hPavc using hav
  set y₀ : Y := genericPoint Y
  set P : MvPolynomial (Fin (n + 1)) ℂ := P₂ * Pav y₀ * ∏ y ∈ Ξ, Pav y with hPdef
  have hP : P ≠ 0 := mul_ne_zero (mul_ne_zero hP₂ (hPav y₀))
    (Finset.prod_ne_zero_iff.mpr fun y _ => hPav y)
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (n + 1) → ℂ, MvPolynomial.eval c' P ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun c' => by rw [h c', map_zero])
  rw [hPdef, map_mul, map_mul, map_prod] at hc'
  have h2 : MvPolynomial.eval c' P₂ ≠ 0 := fun h => hc' (by rw [h]; ring)
  have h0 : MvPolynomial.eval c' (Pav y₀) ≠ 0 := fun h => hc' (by rw [h]; ring)
  have h3 : ∀ y ∈ Ξ, MvPolynomial.eval c' (Pav y) ≠ 0 := fun y hy h => hc' (by
    rw [Finset.prod_eq_zero hy h]; ring)
  obtain ⟨hτ, -⟩ := hPavc y₀ c' h0
  obtain ⟨hle1, T', hT'1, hT'2, hT'3⟩ := hsncB c' h2 hτ
  refine ⟨_, hτ, hle1, fun P hP hPS => ?_, ?_, fun y hy => ?_⟩
  · exact Finset.disjoint_left.mp hT'2 (hT'1 P hP) hPS
  · refine hT'3.of_support_subset ?_
    rw [support_sum_single_one, support_sum_single_one]
    intro E hE
    rcases Finset.mem_union.mp hE with h | h
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (hT'1 E (Finsupp.mem_support_iff.mp h))
  · exact (hPavc y c' (h3 y hy)).2

/-- The boundary `(Γ - T) + t F⁺` is effective when `Γ ≥ 0` has coefficient one along `T` and
`t ≥ 0`. -/
private theorem zero_le_sub_single_add_smul_sup {Y : Scheme.{0}} (T : MMP.Mori.PrimeDivisor Y)
    (Γ₀ : QDivisor Y) (F₀ : Divisor Y) (hΓ₀ : 0 ≤ Γ₀) (hΓT : Γ₀.coeff T = 1) {t : ℚ}
    (ht : 0 ≤ t) :
    0 ≤ (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) + t • Divisor.toQDivisor (F₀ ⊔ 0) := by
  classical
  have hmaxc : ∀ P, (((F₀ ⊔ 0 : Divisor Y).coeff P : ℤ) : ℚ) = max ((F₀.coeff P : ℤ) : ℚ) 0 :=
    fun P => by
      change (((F₀ ⊔ 0 : Divisor Y) P : ℤ) : ℚ) = _
      rw [Finsupp.sup_apply]
      push_cast
      rfl
  intro P
  change 0 ≤ ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
    t • Divisor.toQDivisor (F₀ ⊔ 0)).coeff P
  have hT1 : (Divisor.toQDivisor (Finsupp.single T (1 : ℤ))).coeff P =
      if P = T then 1 else 0 := by
    rw [Divisor.coeff_toQDivisor]
    by_cases hPT : P = T
    · subst hPT
      rw [DivisorWithCoeffs.coeff_single_self, if_pos rfl, Int.cast_one]
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPT), if_neg hPT, Int.cast_zero]
  have hP := DivisorWithCoeffs.coeff_add (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1))
    (t • Divisor.toQDivisor (F₀ ⊔ 0)) P
  rw [DivisorWithCoeffs.coeff_sub, hT1] at hP
  have hFm : 0 ≤ t * max ((F₀.coeff P : ℤ) : ℚ) 0 := mul_nonneg ht (le_max_right _ _)
  have hsm0 : (t • Divisor.toQDivisor (F₀ ⊔ 0)).coeff P = t * max ((F₀.coeff P : ℤ) : ℚ) 0 := by
    rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul, hmaxc]
  rw [hP, hsm0]
  split_ifs with hPT
  · subst hPT
    rw [hΓT]
    linarith
  · have := hΓ₀ P
    change 0 ≤ Γ₀.coeff P at this
    linarith

/-- Clearing the denominators of the prepared boundary `T + H/a + (Γ - T) + F⁺/(N'm₀)`,
`a = cN'm₀`, with `d₀ Γ` integral. -/
private theorem toQDivisor_eq_smul_preparedBoundary {Y : Scheme.{0}} (T : MMP.Mori.PrimeDivisor Y)
    (H F₀ Γ₀' : Divisor Y) (Γ₀ : QDivisor Y) {N₀ M d₀ m q c N' m₀ : ℕ} (hN' : 0 < N')
    (hm₀ : 0 < m₀) (hc : 0 < c) (hΓ₀' : Divisor.toQDivisor Γ₀' = (d₀ : ℤ) • Γ₀) :
    Divisor.toQDivisor (((N₀ * M * d₀ * m * q : ℕ) : ℤ) • H +
      ((N₀ * (c * N' * m₀) * M * m * q : ℕ) : ℤ) • Γ₀' +
        ((N₀ * c * M * d₀ * m * q : ℕ) : ℤ) • (F₀ ⊔ 0)) =
      ((N₀ * (c * N' * m₀ * M * d₀ * m) * q : ℕ) : ℚ) •
        (Divisor.toQDivisor (Finsupp.single T 1) +
          ((c * N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor H +
          ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
            ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))) := by
  have hmaxc : ∀ P, (((F₀ ⊔ 0 : Divisor Y).coeff P : ℤ) : ℚ) = max ((F₀.coeff P : ℤ) : ℚ) 0 :=
    fun P => by
      change (((F₀ ⊔ 0 : Divisor Y) P : ℤ) : ℚ) = _
      rw [Finsupp.sup_apply]
      push_cast
      rfl
  have hΓ₀'c : ∀ P, ((Γ₀'.coeff P : ℤ) : ℚ) = d₀ * Γ₀.coeff P := fun P => by
    have := congrArg (fun G : QDivisor Y => G.coeff P) hΓ₀'
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] using this
  refine DivisorWithCoeffs.ext' fun P => ?_
  rw [DivisorWithCoeffs.coeff_smul, coeff_preparedBoundary]
  simp only [map_add, map_zsmul, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
    Divisor.coeff_toQDivisor, smul_eq_mul, zsmul_eq_mul, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  rw [hΓ₀'c, hmaxc]
  have hN'q : (N' : ℚ) ≠ 0 := by exact_mod_cast hN'.ne'
  have hm₀q : (m₀ : ℚ) ≠ 0 := by exact_mod_cast hm₀.ne'
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

/-- The exceptional correction `E' = k₁ E₀' + k₂ (-F)⁺` is effective and has no component over a
prime divisor of `X`, when `E₀' = d₀ E` with `E ≥ 0` and every component of `E` or `F` is
exceptional. -/
private theorem nonneg_and_map_genericPoint_ne {X Y : Scheme.{0}} (μ : Y ⟶ X) (E : QDivisor Y)
    (E₀' F₀ : Divisor Y) {d₀ : ℕ} (k₁ k₂ : ℕ)
    (hE₀'c : ∀ P, ((E₀'.coeff P : ℤ) : ℚ) = d₀ * E.coeff P) (hE0 : 0 ≤ E)
    (hcent : ∀ P : MMP.Mori.PrimeDivisor Y, (E.coeff P ≠ 0 ∨ F₀.coeff P ≠ 0) →
      ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint) :
    0 ≤ (k₁ : ℤ) • E₀' + (k₂ : ℤ) • ((-F₀) ⊔ 0) ∧
      ∀ P : MMP.Mori.PrimeDivisor Y, ((k₁ : ℤ) • E₀' + (k₂ : ℤ) • ((-F₀) ⊔ 0)).coeff P ≠ 0 →
        ∀ Γ : MMP.Mori.PrimeDivisor X, μ P.genericPoint ≠ Γ.genericPoint := by
  refine ⟨fun P => ?_, fun P hP Γ hPΓ => ?_⟩
  · change 0 ≤ ((k₁ : ℤ) • E₀' + (k₂ : ℤ) • ((-F₀) ⊔ 0)).coeff P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul]
    have h1 : (0 : ℚ) ≤ ((E₀'.coeff P : ℤ) : ℚ) := by
      rw [hE₀'c]
      exact mul_nonneg (Nat.cast_nonneg _) (hE0 P)
    have h2 : 0 ≤ ((-F₀) ⊔ 0 : Divisor Y).coeff P := by
      change 0 ≤ ((-F₀) ⊔ 0 : Divisor Y) P
      rw [Finsupp.sup_apply]
      exact le_max_right _ _
    have h1' : 0 ≤ E₀'.coeff P := by exact_mod_cast h1
    rw [smul_eq_mul, smul_eq_mul]
    exact add_nonneg (mul_nonneg (Int.natCast_nonneg _) h1') (mul_nonneg (Int.natCast_nonneg _) h2)
  · rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_smul] at hP
    by_cases hEP : E.coeff P = 0
    · have h1 : E₀'.coeff P = 0 := by
        have := hE₀'c P
        rw [hEP, mul_zero] at this
        exact_mod_cast this
      have hFP : F₀.coeff P ≠ 0 := by
        intro hF
        apply hP
        have h2 : ((-F₀) ⊔ 0 : Divisor Y).coeff P = 0 := by
          change ((-F₀) ⊔ 0 : Divisor Y) P = 0
          rw [Finsupp.sup_apply]
          change max (-(F₀.coeff P)) 0 = 0
          rw [hF]
          rfl
        rw [h1, h2]
        simp
      exact hcent P (Or.inr hFP) Γ hPΓ
    · exact hcent P (Or.inl hEP) Γ hPΓ

/-- **An exceptional anti-ample divisor and the ample twists** ([KM98, Lemma 2.62]). For a
projective birational `μ : Y ⟶ X` from a smooth variety onto a `ℚ`-factorial normal variety, there
is an exceptional divisor `F₀` with `-F₀` relatively ample over `X`; for all large `N'` some
positive multiple of `N' μ^*L₀ - F₀` is ample over `Spec Γ(Z, 𝒪_Z)` and globally generated by
finitely many sections. -/
private theorem exists_isExceptional_isRelativelyAmpleCartier_smul_sub
    {X Y Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsAffine Z]
    {sX : X ⟶ Spec (.of ℂ)} (hXnv : IsNormalVariety ℂ sX) (hXQ : IsQFactorial sX)
    (μ : Y ⟶ X) (hY : IsNormalVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ)
    (hμp : IsProjectiveMorphism μ) (hsm : IsSmoothScheme (μ ≫ sX))
    (f : X ⟶ Z) (hfp : IsProjectiveMorphism f)
    {L₀ : Divisor X} (hL₀c : L₀.IsCartier) (hL₀amp : L₀.IsRelativelyAmple f hL₀c)
    (hBY : ∀ (G : Divisor X) (Z : irreducibleComponents Y),
      μ (componentGenericPoint Y Z) ∉ G.supp)
    {PL : Divisor Y} (hPL : L₀.IsPullback μ (hBY L₀) PL) :
    ∃ F₀ : Divisor Y,
      (∀ P : MMP.Mori.PrimeDivisor Y, F₀.coeff P ≠ 0 →
        MMP.Mori.RationalMap.IsExceptional (X := Y) μ.toRationalMap P) ∧
      ∃ n₀ : ℕ, ∀ N' : ℕ, n₀ ≤ N' → ∃ c : ℕ, 0 < c ∧
        MMP.Flips.IsRelativelyAmpleCartier (μ ≫ f ≫ Z.isoSpec.hom)
          ((c : ℤ) • ((N' : ℤ) • PL - F₀)) ∧
        ∃ (n : ℕ) (t : Fin (n + 1) → (((c : ℤ) • ((N' : ℤ) • PL - F₀)).divisorialSubmodule ⊤)),
          ∀ y : Y, ∃ (i : Fin (n + 1)) (hi : t i ≠ 0),
            y ∉ (Divisor.zeroDivisor _ (t i) hi).supp := by
  haveI : LocallyOfFiniteType sX := hXnv.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXnv.1.toIsSeparated
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (μ ≫ sX) := hY.1.toQuasiCompact
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hμp
  -- KM 2.62: an ample `H_μ` on `Y` with `μ^*(μ_* H_μ) = H_μ + F`, `F ≥ 0` exceptional
  obtain ⟨Hk, hHkc, Fq, -, hHkamp, -, -, hFqex, hBk, hpbk⟩ :=
    MMP.Mori.exists_isRelativelyAmple_isPullback_transformDivisor_eq_add sX (μ ≫ sX) hXQ hY μ
      rfl hμp hμ
  -- a Cartier multiple `q μ_* H_μ` on the `ℚ`-factorial `X`, with pull-back `q(H_μ + F)`
  obtain ⟨q₀, hq₀, hq₀c⟩ := hXQ.2 (RationalMap.transformDivisor (X := Y) μ.toRationalMap Hk)
  obtain ⟨Gy, hGyQ, hGy⟩ := hpbk q₀ hq₀ _ (by rw [map_zsmul]) hq₀c
  refine ⟨Gy - (q₀ : ℤ) • Hk, fun P hP => hFqex P fun h0 => hP ?_, ?_⟩
  · have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hGyQ
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
      DivisorWithCoeffs.coeff_add, zsmul_eq_mul] at h1
    have h0' : Fq.coeff P = 0 := h0
    rw [h0', add_zero, Int.cast_natCast] at h1
    rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have h2 : ((Gy.coeff P - (q₀ : ℤ) * Hk.coeff P : ℤ) : ℚ) = 0 := by
      push_cast; linarith
    exact_mod_cast h2
  · -- `-F₀ = q H_μ - μ^*(q μ_* H_μ)` is `μ`-ample
    have hHkC : MMP.Flips.IsRelativelyAmpleCartier μ Hk := by
      haveI := hHkc.isInvertibleModule_divisorialSheaf
      exact ⟨hHkc, fun U hU =>
        (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple μ _
          inferInstance hHkamp).2 U hU⟩
    have hbasics := MMP.Flips.relativelyAmple_basics (μ ≫ sX) sX hY hXnv μ rfl
    have hqHk := hbasics.2.1 Hk hHkC |>.2 (q₀ : ℤ) (by exact_mod_cast hq₀)
    have hnegGy := hGy.zsmul hq₀c (-1) (hBY _)
    have hnegF : MMP.Flips.IsRelativelyAmpleCartier μ (-(Gy - (q₀ : ℤ) • Hk)) := by
      have h := (hbasics.2.1 _ hqHk).1 _ (hq₀c.zsmul (-1)) (hBY _) _ hnegGy
      rw [show -(Gy - (q₀ : ℤ) • Hk) = (q₀ : ℤ) • Hk + (-1 : ℤ) • Gy by abel]
      exact h
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
    exact exists_isRelativelyAmpleCartier_smul_sub_and_free hY.1
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsm) μ f hL₀c hL₀amp hPL hnegF

/-- **Finite generation of a Veronese subalgebra.** In the situation of
`MMP.Fourfold.finiteType_weilRestrictionAlgebra_of_birationalFiniteGenerationProperty`, the
restricted algebra of some positive multiple `N • D` is finitely generated over `Γ(Z, 𝒪_Z)`. On a log
resolution `μ : Y ⟶ X` whose strict transform `T` of `S` is smooth with a terminal restricted
boundary (`exists_isLogResolution_isRealTerminalPair_restrictPrimeDivisor`), a general member `H`
of a free multiple of `N' μ^*L₀ - F₀`, with `F₀` exceptional and `-F₀` relatively ample, gives a
prepared boundary on `Y`; `restrictedImageAlgebra_fg_of_birationalFiniteGenerationProperty`
applies there, and `finiteType_weilRestriction_of_model` transports the result to `X`. -/
private theorem exists_veronese_finiteType
    {d : ℕ} (hd : 2 ≤ d) (hF : BirationalFiniteGenerationProperty d)
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hZ : IsNormalVariety ℂ sZ) [IsAffine Z]
    (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = d + 1)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX (d + 1))
    (S : MMP.Mori.PrimeDivisor X) (B : QDivisor X) (hB : 0 ≤ B) (hBS : B.coeff S = 0)
    (hB1 : ∀ P, B.coeff P < 1)
    (hplt : IsPltPair sX (d + 1) K (Finsupp.single S 1 + B))
    (A₀ : QDivisor X) (hA₀ : A₀.HasRelativelyAmpleMultiple f)
    (A : QDivisor X) (hA : A.QLinearlyEquivalent A₀)
    (hsec : ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X,
      Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + (Finsupp.single S 1 + B + A)) ∧
      ∃ φ : (RationalFunctions X)ˣ, (φ : RationalFunctions X) ∈ divisorialSections D ∧
        S.ord φ + D.coeff S = 0)
    (hSbir : IsBirationalMorphism (S.idealSheaf.subschemeι ≫ f).toImage)
    (q : ℕ) (D : Divisor X) (hDC : D.IsCartier)
    (hD : Divisor.toQDivisor D = (q : ℤ) • (Divisor.toQDivisor K + (Finsupp.single S 1 + B + A)))
    (hDS : D.coeff S = 0) :
    ∃ N : ℕ, 0 < N ∧
      ((weilRestrictionMap (B := (N : ℤ) • D) (S := S)
          (by rw [DivisorWithCoeffs.coeff_smul, hDS, smul_zero])).rangeRestrict.comp
        (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict
          (weilSectionAlgebra ((N : ℤ) • D))
          (fun s => Subring.mem_comap.mp
            ((comap_C_weilSectionAlgebra ((N : ℤ) • D)).ge ⟨s, rfl⟩))).comp
            f.appTop.hom)).FiniteType := by
  classical
  have hXnv : IsNormalVariety ℂ sX := hplt.1.1
  haveI : LocallyOfFiniteType sX := hXnv.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXnv.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hZ.2
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hD0 : D = 0 := Divisor.toQDivisor_injective (by rw [hD, Nat.cast_zero, zero_smul, map_zero])
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
    haveI : IsNoetherianRing Γ(Z, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Z⟩
    have hfin : f.appTop.hom.Finite := by
      have h := finiteGlobalSectionsOfProper Γ(Z, ⊤) inferInstance (f ≫ Z.isoSpec.hom)
        inferInstance
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
      exact RingHom.Finite.of_comp_finite h
    exact ⟨1, one_pos, (finiteType_weilRestriction_zero S _ (by rw [hD0, smul_zero]) _).comp
      hfin.finiteType⟩
  -- the resolution
  obtain ⟨Y, μ, hlog, hY, hμ, Γ₀, E, T, hΓ₀, hE0, hΓE, hEx, hcrep, hTS, hΓT, hΓlt, hTsm, hΨ0,
    hΨsnc, hTln, hTn, hTterm⟩ :=
    exists_isLogResolution_isRealTerminalPair_restrictPrimeDivisor sX hXQ (d + 1) K S B hB hBS
      hB1 hplt
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (μ ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  haveI : QuasiCompact (μ ≫ sX) := hY.1.toQuasiCompact
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hlog.isProjectiveMorphism
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (μ ≫ sX)
  haveI := T.integral
  haveI := hTln
  haveI := hTn
  have hsm : IsSmoothScheme (μ ≫ sX) := hlog.isSmoothScheme
  -- the base ring `Γ(Z, 𝒪_Z)`
  letI : Algebra ℂ Γ(Z, ⊤) := (sZ.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(Z, ⊤) := by
    have h : RingHom.FiniteType sZ.appTop.hom :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
    exact h.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : IsIntegrallyClosed Γ(Z, ⊤) :=
    (isNormal_iff_forall_affineOpen_normal Z).mp inferInstance ⟨⊤, isAffineOpen_top Z⟩
      inferInstance
  haveI : IsDomain Γ(Z, ⊤) := inferInstance
  set π : Y ⟶ Spec Γ(Z, ⊤) := μ ≫ f ≫ Z.isoSpec.hom with hπdef
  have hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(Z, ⊤))) = μ ≫ sX := by
    have h2 : CommRingCat.ofHom (algebraMap ℂ Γ(Z, ⊤)) =
        (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sZ.appTop := rfl
    rw [h2, Spec.map_comp, hπdef, Category.assoc, Category.assoc,
      ← Category.assoc Z.isoSpec.hom, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id, hf]
  have hπp : IsProjectiveMorphism π := by
    refine IsProjectiveMorphism.of_comp π Z.isoSpec.inv ?_
    rw [hπdef, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hlog.isProjectiveMorphism.comp hfp
  -- canonical divisors `K = div ω` on `X` and `K_Y⁰ = div μ^*ω` on `Y`
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXnv hK
  haveI : IsDominant μ := hμ.isDominant
  have hdimY : topologicalKrullDim Y = d + 1 := by
    haveI := hXnv.1
    haveI := hY.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (μ ≫ sX) hμ, hdim]
  have hτ0 : pullbackRationalPluriForms sX μ ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' μ hμ.functionFieldMap_bijective
      (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hdim) hω0
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (μ ≫ sX) hY hdimY
  set KY₀ : Divisor Y := divisorOfForm (pullbackRationalPluriForms sX μ ω) with hKY₀def
  have hKY₀ : KY₀.IsCanonicalDivisor (μ ≫ sX) (d + 1) := by
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀ hτ0
    rw [one_zsmul] at h
    exact hK₀.of_linearlyEquivalent h
  have hωK : divisorOfForm ω = K := Finsupp.ext fun Γ => (coeff_divisorOfForm ω Γ).trans (hω Γ)
  -- the crepant pull-back of `K + S + B`
  have hPSB : MMP.Mori.IsPair sX (Finsupp.single S 1 + B) := hplt.1.isPair
  obtain ⟨hpb, -, -⟩ := hPSB.isPullback_of_isCrepantBoundary μ hY hμ hK hKY₀
    (Or.inl ⟨ω, hω0, hωK, rfl⟩) hcrep
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c⟩ := hplt.1.2.2.exists_pos
  obtain ⟨D₁Y, hD₁Y, hD₁Yc, hB₁, hD₁pb⟩ := hpb m₁ hm₁ D₁ hD₁ hD₁c
  -- a canonical divisor of `Y` with coefficient `-1` along `T`
  obtain ⟨u, hu⟩ := MMP.Positivity.PrimeDivisor.exists_ord_eq_one T
  set cu : ℤ := -1 - KY₀.coeff T with hcu
  set KY : Divisor Y := KY₀ + MMP.Mori.principalDivisor (u ^ cu) with hKYdef
  have hKY : KY.IsCanonicalDivisor (μ ≫ sX) (d + 1) :=
    hKY₀.of_linearlyEquivalent ⟨u ^ cu, by rw [hKYdef]; abel⟩
  have hKYT : KY.coeff T = -1 := by
    rw [hKYdef, DivisorWithCoeffs.coeff_add, principalDivisor_zpow, DivisorWithCoeffs.coeff_smul,
      MMP.Mori.coeff_principalDivisor, hu, hcu]
    simp
  -- the `f`-ample multiple `L₀ = m₀ A₀`, and `M (A - A₀) = div ψ`
  obtain ⟨m₀, hm₀, L₀, hL₀c, hL₀, hL₀amp⟩ := hA₀
  obtain ⟨M, hM, ψ, hψ⟩ := hA
  have hBY : ∀ (G : Divisor X) (Z : irreducibleComponents Y),
      μ (componentGenericPoint Y Z) ∉ G.supp :=
    fun G Z => MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' μ G Z
  -- `M m₀ m₁ D = q M m₀ D₁ + q M m₁ L₀ + q m₀ m₁ div ψ` on `X`
  set N₀ : ℕ := M * m₀ * m₁ with hN₀
  have hrelX : (N₀ : ℤ) • D = ((q * M * m₀ : ℕ) : ℤ) • D₁ + ((q * M * m₁ : ℕ) : ℤ) • L₀ +
      ((q * m₀ * m₁ : ℕ) : ℤ) • principalDivisor ψ := by
    apply Divisor.toQDivisor_injective
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul, hD, hD₁, hL₀, ← hψ, hN₀]
    push_cast
    module
  -- the pull-back of `N₀ D` to `Y`
  obtain ⟨PL, hPL⟩ := hL₀c.exists_isPullback (f := μ) (hBY L₀)
  set ψY := pullbackRationalFunction μ ψ (hBY _) with hψY
  have hψpb := Divisor.isPullback_principalDivisor (f := μ) ψ (hBY _)
  set Dpb : Divisor Y := ((q * M * m₀ : ℕ) : ℤ) • D₁Y + ((q * M * m₁ : ℕ) : ℤ) • PL +
    ((q * m₀ * m₁ : ℕ) : ℤ) • principalDivisor ψY with hDpbdef
  have hDpb : ((N₀ : ℤ) • D).IsPullback μ (hBY _) Dpb := by
    refine Divisor.IsPullback.of_eq hrelX.symm ?_ (hB₁ := hBY _)
    refine Divisor.IsPullback.add ((hD₁c.zsmul _).add (hL₀c.zsmul _))
      ((Divisor.isCartier_principalDivisor ψ).zsmul _) (hBY _)
      (Divisor.IsPullback.add (hD₁c.zsmul _) (hL₀c.zsmul _) (hBY _)
        (hD₁pb.zsmul hD₁c _ (hBY _)) (hPL.zsmul hL₀c _ (hBY _)) (hB₁ := hBY _) (hB₂ := hBY _))
      (hψpb.zsmul (Divisor.isCartier_principalDivisor ψ) _ (hBY _)) (hB₁ := hBY _) (hB₂ := hBY _)
  -- the exceptional divisor `F₀` with `-F₀` ample over `X`, and the ample twists
  obtain ⟨F₀, hF₀ex, n₀, hamp⟩ := exists_isExceptional_isRelativelyAmpleCartier_smul_sub hXnv hXQ
    μ hY hμ hlog.isProjectiveMorphism hsm f hfp hL₀c hL₀amp hBY hPL
  -- the snc configuration of the resolution
  obtain ⟨S₀, hTS₀, hΓS₀, hFS₀, hES₀, hS₀snc⟩ : ∃ S₀ : Finset (MMP.Mori.PrimeDivisor Y),
      T ∈ S₀ ∧ (∀ P, Γ₀.coeff P ≠ 0 → P ∈ S₀) ∧ (∀ P, F₀.coeff P ≠ 0 → P ∈ S₀) ∧
      (∀ P, E.coeff P ≠ 0 → P ∈ S₀) ∧
      DivisorWithCoeffs.IsSNC (μ ≫ sX) (∑ P ∈ S₀, Finsupp.single P (1 : ℤ)) := by
    have hgenmem : ∀ {W : Scheme.{0}} (P : MMP.Mori.PrimeDivisor W),
        P.genericPoint ∈ (P.support : Set W) := fun P => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have hexc_mem : ∀ P : MMP.Mori.PrimeDivisor Y,
        MMP.Mori.RationalMap.IsExceptional (X := Y) μ.toRationalMap P →
        P.genericPoint ∈ MMP.Mori.exceptionalSet μ ⊔
          (QDivisor.toRDivisor (Finsupp.single S 1 + B)).supp.preimage μ.continuous :=
      fun P hP => by
        rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup]
        exact Or.inl (MMP.Positivity.support_subset_exceptionalSet P hP (hgenmem P))
    have hsupp_mem : ∀ (P : MMP.Mori.PrimeDivisor Y) (Q : MMP.Mori.PrimeDivisor X),
        μ P.genericPoint = Q.genericPoint →
        DivisorWithCoeffs.coeff (Finsupp.single S 1 + B : QDivisor X) Q ≠ 0 →
        P.genericPoint ∈ MMP.Mori.exceptionalSet μ ⊔
          (QDivisor.toRDivisor (Finsupp.single S 1 + B)).supp.preimage μ.continuous :=
      fun P Q hPQ hQ => by
        rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup]
        refine Or.inr ?_
        change μ P.genericPoint ∈ (QDivisor.toRDivisor (Finsupp.single S 1 + B)).supp
        rw [DivisorWithCoeffs.mem_supp_iff]
        refine ⟨Q, ?_, hPQ ▸ hgenmem Q⟩
        rw [QDivisor.coeff_toRDivisor]
        exact_mod_cast hQ
    obtain ⟨S₀, hsub, hsnc⟩ := exists_finset_isSNC_of_isLogResolution hlog.toIsLogResolution
      (insert T (Γ₀.support ∪ F₀.support ∪ E.support)) (Finset.insert_nonempty _ _) (by
        intro P hP
        rcases Finset.mem_insert.mp hP with rfl | hP
        · refine hsupp_mem P S hTS ?_
          rw [DivisorWithCoeffs.coeff_add, hBS, add_zero]
          simp [DivisorWithCoeffs.coeff_apply]
        rcases Finset.mem_union.mp hP with hP | hP
        · rcases Finset.mem_union.mp hP with hP | hP
          · have hΓP : Γ₀.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
            by_cases hPex : MMP.Mori.RationalMap.IsExceptional (X := Y) μ.toRationalMap P
            · exact hexc_mem P hPex
            · obtain ⟨Q, hQv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional
                hXnv ⟨Y, μ, hY, hμ, P⟩ hPex
              have hPQ := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hXnv hQv
              obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy
                (MMP.Mori.IsPairWith.isPair hplt.1) hK
                (DivisorOver.ofPrimeDivisor ℂ hXnv Q)
              have h1 := ha'.eq_neg_coeff_of_ofPrimeDivisor hXnv
              have h2 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hplt.1 hQv (hcrep P) ha'
              have hEP : E.coeff P = 0 := by
                have h := congrArg (fun G : QDivisor Y => G.coeff P) hΓE
                have hΓ0 := hΓ₀ P
                have hE0' := hE0 P
                change min (Γ₀.coeff P) (E.coeff P) = 0 at h
                rcases min_choice (Γ₀.coeff P) (E.coeff P) with hm | hm
                · exact absurd (hm ▸ h) hΓP
                · exact hm ▸ h
              refine hsupp_mem P Q hPQ fun h0 => hΓP ?_
              rw [DivisorWithCoeffs.coeff_sub, hEP] at h2
              linarith only [h1, h2, h0]
          · exact hexc_mem P (hF₀ex P (Finsupp.mem_support_iff.mp hP))
        · exact Finset.mem_coe.mp (Finset.mem_coe.mpr hP) |> fun hP =>
            hexc_mem P (hEx P (Finsupp.mem_support_iff.mp hP)))
    refine ⟨S₀, hsub (Finset.mem_insert_self _ _), fun P hP => hsub ?_, fun P hP => hsub ?_,
      fun P hP => hsub ?_, hsnc⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finsupp.mem_support_iff.mpr hP)))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finsupp.mem_support_iff.mpr hP)))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hP))
  -- the singularities of the prepared boundary, for `N'` large
  have hFT₀ : F₀.coeff T = 0 := by
    by_contra h
    exact map_genericPoint_ne_of_isExceptional T (hF₀ex T h) S hTS
  obtain ⟨n₁, hsing⟩ := exists_bound_isPltPair_preparedBoundary hd hY hsm hdimY hKY T Γ₀ F₀ S₀
    hm₀ hΓ₀ hΓT hΓlt hTsm hΨsnc hTterm hFT₀ hTS₀ hΓS₀ hFS₀
  -- the choice of `N'`, `c` and the system `|G|`, `G = c (N' μ^*L₀ - F₀)`
  set N' : ℕ := max (max n₀ n₁) 3 with hN'
  obtain ⟨c, hc, hGamp, n, tG, htG⟩ := hamp N' (le_trans (le_max_left _ _) (le_max_left _ _))
  revert tG htG
  set G : Divisor Y := (c : ℤ) • ((N' : ℤ) • PL - F₀) with hGdef
  intro tG htG
  set a : ℕ := c * N' * m₀ with ha_def
  have ha3 : 3 ≤ a := by
    have : 1 ≤ c * m₀ := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc 3 ≤ N' := le_max_right _ _
      _ ≤ c * m₀ * N' := Nat.le_mul_of_pos_left _ (by positivity)
      _ = a := by rw [ha_def]; ring
  -- the multiple `N = N₀ N₁` and the degree `q' = N q`
  obtain ⟨d₀, hd₀, ⟨Γ₀', hΓ₀'⟩, E₀', hE₀'⟩ := exists_pos_toQDivisor_eq_smul_smul Γ₀ E
  obtain ⟨m, hm, Dm, hDm, φ, hφ, hφS⟩ := hsec
  set N₁ : ℕ := a * M * d₀ * m with hN₁
  set N : ℕ := N₀ * N₁ with hNdef
  have hN : 0 < N := by positivity
  set q' : ℕ := N * q with hq'
  have hq'0 : 0 < q' := by positivity
  have hNpb : ((N : ℤ) • D).IsPullback μ (hBY _) ((N₁ : ℤ) • Dpb) := by
    have h := hDpb.zsmul (hDC.zsmul _) (N₁ : ℤ) (hBY _)
    refine Divisor.IsPullback.of_eq ?_ h
    rw [smul_smul, hNdef]
    push_cast
    ring_nf
  -- a section of `𝒪_X(N D)` not vanishing along `S`, from `hsec`
  have hDmS : Dm.coeff S = 0 := by
    have h1 : (q : ℤ) • Divisor.toQDivisor Dm = (m : ℤ) • Divisor.toQDivisor D := by
      rw [hDm, hD, smul_smul, smul_smul, mul_comm]
    have h2 := congrArg (fun G : QDivisor X => G.coeff S) h1
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, hDS, zsmul_eq_mul,
      Int.cast_zero, mul_zero] at h2
    have hq0 : ((q : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    exact_mod_cast (mul_eq_zero.mp h2).resolve_left hq0
  set kk : ℕ := N₀ * a * M * d₀ * q with hkk
  have hkDm : (kk : ℤ) • Dm = (N : ℤ) • D := by
    apply Divisor.toQDivisor_injective
    rw [map_zsmul, map_zsmul, hDm, hD, smul_smul, smul_smul, hkk, hNdef, hN₁]
    congr 1
    push_cast
    ring
  have hφk : ((φ ^ kk : (RationalFunctions X)ˣ) : RationalFunctions X) ∈
      divisorialSections ((N : ℤ) • D) := by
    rw [← hkDm, coe_mem_divisorialSections_iff]
    have h := (coe_mem_divisorialSections_iff φ).mp hφ
    intro P
    rw [MMP.Mori.PrimeDivisor.ord_pow, DivisorWithCoeffs.coeff_smul, smul_eq_mul, nsmul_eq_mul]
    have h' := mul_le_mul_of_nonneg_left (h P) (Int.natCast_nonneg kk)
    linarith only [h']
  have hφkS : S.ord (φ ^ kk) = 0 := by
    have h0 : S.ord φ = 0 := by rwa [hDmS, add_zero] at hφS
    rw [MMP.Mori.PrimeDivisor.ord_pow, h0, nsmul_zero]
  set E' : Divisor Y := ((N₀ * a * M * m * q : ℕ) : ℤ) • E₀' +
    ((N₀ * c * M * d₀ * m * q : ℕ) : ℤ) • ((-F₀) ⊔ 0) with hE'def
  -- the effective divisor `div(μ^*φ^kk) + B' + E'` of the transported section, and the points
  -- of `Y` over its components on `T`, which the general member avoids
  set φY : (RationalFunctions Y)ˣ := pullbackRationalFunction μ (φ ^ kk) (hBY _) with hφYdef
  set Zeff : Divisor Y := MMP.Mori.principalDivisor φY + (N₁ : ℤ) • Dpb + E' with hZdef
  haveI := Classical.decEq Y
  set Ξ : Finset Y := (Zeff.restrictPrimeDivisor T).support.image
    (fun Q => T.idealSheaf.subschemeι Q.genericPoint) with hΞdef
  -- the general member `H` of `|G|`
  obtain ⟨τ, hτ, hH1, hHS₀, hHsnc, hHΞ⟩ :=
    exists_generalMember_isSNC_notMem_supp hY hsm G tG htG S₀ hS₀snc Ξ
  set H : Divisor Y := G.zeroDivisor τ hτ with hHdef
  have hH0 : 0 ≤ H := Divisor.zeroDivisor_nonneg G τ hτ
  have hHa : MMP.Flips.IsRelativelyAmpleCartier π H := by
    obtain ⟨hGc, hG⟩ := hGamp
    have hlin : H.LinearlyEquivalent G :=
      ⟨(MMP.Mori.Divisor.isUnit_sectionToRationalFunctions hτ).unit, by
        rw [hHdef, Divisor.zeroDivisor_eq]
        abel⟩
    have hHc : H.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm H
    refine ⟨hHc, fun U hU => ?_⟩
    haveI := hHc.isInvertibleModule_divisorialSheaf
    haveI := hGc.isInvertibleModule_divisorialSheaf
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((RingedSpaceModuleAdjunction.modulePullback (π ⁻¹ᵁ U).ι.toLRSHom.toShHom).mapIso
        hlin.divisorialSheafIso)).mpr (hG U hU)
  obtain ⟨hfloor, hpltY, hpltY', hcan⟩ :=
    hsing N' c (le_trans (le_max_right _ _) (le_max_left _ _)) hc H hH0 hH1 hHS₀ hHsnc
  -- the strict transform `T` of `S`, with its finite normal affine model `T₀`
  have hTnv : IsNormalVariety ℂ (T.idealSheaf.subschemeι ≫ μ ≫ sX) := by
    haveI : AlgebraicGeometry.IsVariety ℂ (μ ≫ sX) := hY.1
    exact ⟨⟨⟩, inferInstance⟩
  have hTp : IsProjectiveMorphism (T.idealSheaf.subschemeι ≫ μ ≫ f) := by
    obtain ⟨m', k, hk, hkq⟩ := hlog.isProjectiveMorphism.comp hfp
    haveI := hk
    exact ⟨m', T.idealSheaf.subschemeι ≫ k, inferInstance, by rw [Category.assoc, hkq]⟩
  haveI : ValuationRing (X.presheaf.stalk (μ T.genericPoint)) := by
    rw [hTS]
    haveI := S.isDiscreteValuationRing_localRing
    infer_instance
  haveI : IsIso (μ.stalkMap T.genericPoint) :=
    MMP.Positivity.isIso_stalkMap_of_valuationRing μ hμ.functionFieldMap_bijective
      T.genericPoint
  have hTgen : ∀ x : T.idealSheaf.subscheme.functionField, ∃ a b : Γ(Z, ⊤),
      T.idealSheaf.subscheme.germToFunctionField ⊤
        ((T.idealSheaf.subschemeι ≫ μ ≫ f).appTop b) ≠ 0 ∧
      x * T.idealSheaf.subscheme.germToFunctionField ⊤
        ((T.idealSheaf.subschemeι ≫ μ ≫ f).appTop b) =
        T.idealSheaf.subscheme.germToFunctionField ⊤
          ((T.idealSheaf.subschemeι ≫ μ ≫ f).appTop a) := by
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
    exact exists_mul_germ_eq_germ μ f S T hTS hSbir
  obtain ⟨T₀, κ, fT, hκ, hT₀, hT₀a, hfT, hfTp, hfTb⟩ :=
    exists_finite_normal_affine_model hZ hTnv (T.idealSheaf.subschemeι ≫ μ ≫ f)
      (by rw [Category.assoc, Category.assoc, hf]) hTp hTgen
  have hg : (κ ≫ Z.isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(Z, ⊤))) =
      κ ≫ sZ := by
    have h2 : CommRingCat.ofHom (algebraMap ℂ Γ(Z, ⊤)) =
        (Scheme.ΓSpecIso (.of ℂ)).inv ≫ sZ.appTop := rfl
    rw [h2, Spec.map_comp, Category.assoc, ← Category.assoc Z.isoSpec.hom,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI := hκ
  have hgfin : IsFinite (κ ≫ Z.isoSpec.hom) := inferInstance
  have hfg : fT ≫ κ ≫ Z.isoSpec.hom = T.idealSheaf.subschemeι ≫ π := by
    rw [← Category.assoc, hfT, hπdef]
    simp only [Category.assoc]
  have hmaxc : ∀ P, (((F₀ ⊔ 0 : Divisor Y).coeff P : ℤ) : ℚ) = max ((F₀.coeff P : ℤ) : ℚ) 0 :=
    fun P => by
      change (((F₀ ⊔ 0 : Divisor Y) P : ℤ) : ℚ) = _
      rw [Finsupp.sup_apply]
      push_cast
      rfl
  -- the boundary `B_Y` is effective
  have hBY0 : 0 ≤ (Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
      ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0) :=
    zero_le_sub_single_add_smul_sup T Γ₀ F₀ hΓ₀ hΓT (by positivity)
  -- `q' Δ_Y` is an integral divisor
  set Dint : Divisor Y := ((N₀ * M * d₀ * m * q : ℕ) : ℤ) • H +
    ((N₀ * a * M * m * q : ℕ) : ℤ) • Γ₀' + ((N₀ * c * M * d₀ * m * q : ℕ) : ℤ) • (F₀ ⊔ 0)
    with hDintdef
  have hΓ₀'c : ∀ P, ((Γ₀'.coeff P : ℤ) : ℚ) = d₀ * Γ₀.coeff P := fun P => by
    have := congrArg (fun G : QDivisor Y => G.coeff P) hΓ₀'
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] using this
  have hE₀'c : ∀ P, ((E₀'.coeff P : ℤ) : ℚ) = d₀ * E.coeff P := fun P => by
    have := congrArg (fun G : QDivisor Y => G.coeff P) hE₀'
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] using this
  have hDint : Divisor.toQDivisor Dint = (q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
      (a : ℚ)⁻¹ • Divisor.toQDivisor H +
      ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
        ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0))) := by
    have hN'0 : 0 < N' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact toQDivisor_eq_smul_preparedBoundary T H F₀ Γ₀' Γ₀ hN'0 hm₀ hc hΓ₀'
  have hqΔ' : ((q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
      (a : ℚ)⁻¹ • Divisor.toQDivisor H +
      ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
        ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)))).roundDown = Dint := by
    rw [← hDint]
    refine Finsupp.ext fun P => ?_
    change (DivisorWithCoeffs.roundDown _).coeff P = Dint.coeff P
    rw [DivisorWithCoeffs.coeff_roundDown, Divisor.coeff_toQDivisor, Int.floor_intCast]
  -- the data `E'`, `θ` of the comparison `D_Y = N₁ f^*(N₀ D) + E' + div θ`
  set σ : (RationalFunctions Y)ˣ := (MMP.Mori.Divisor.isUnit_sectionToRationalFunctions hτ).unit with hσ
  set θ : (RationalFunctions Y)ˣ := u ^ ((q' : ℤ) * cu) * σ ^ ((N₀ * M * d₀ * m * q : ℕ) : ℤ) *
    ψY ^ (-((N₀ * a * d₀ * m * q : ℕ) : ℤ)) with hθdef
  have hDYeq : (q' : ℤ) • KY + ((q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
      (a : ℚ)⁻¹ • Divisor.toQDivisor H +
      ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
        ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)))).roundDown =
      (N₁ : ℤ) • Dpb + E' + MMP.Mori.principalDivisor θ := by
    rw [hqΔ']
    apply Divisor.toQDivisor_injective
    refine Finsupp.ext fun P => ?_
    change (Divisor.toQDivisor _).coeff P = (Divisor.toQDivisor _).coeff P
    have hD₁Yc := congrArg (fun G : QDivisor Y => G.coeff P) hD₁Y
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, smul_eq_mul] at hD₁Yc
    have hHc : ((H.coeff P : ℤ) : ℚ) = (P.ord σ : ℚ) + c * (N' * PL.coeff P - F₀.coeff P) := by
      have hGc : ((G.coeff P : ℤ) : ℚ) = c * (N' * PL.coeff P - F₀.coeff P) := by
        rw [hGdef, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
          DivisorWithCoeffs.coeff_smul, smul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [hHdef, Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add,
        MMP.Mori.coeff_principalDivisor, Int.cast_add, hGc]
    have hmaxF : max ((F₀.coeff P : ℤ) : ℚ) 0 = F₀.coeff P + max (-((F₀.coeff P : ℤ) : ℚ)) 0 := by
      rcases le_total 0 ((F₀.coeff P : ℤ) : ℚ) with h | h
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
        ring
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
        ring
    have hmaxN : (((-F₀) ⊔ 0 : Divisor Y).coeff P : ℚ) = max (-((F₀.coeff P : ℤ) : ℚ)) 0 := by
      change ((((-F₀) ⊔ 0 : Divisor Y) P : ℤ) : ℚ) = _
      rw [Finsupp.sup_apply]
      push_cast
      rfl
    simp only [Divisor.coeff_toQDivisor, map_add, map_zsmul, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul, hKYdef, hDintdef, hDpbdef, hE'def, hθdef,
      MMP.Mori.coeff_principalDivisor, MMP.Mori.PrimeDivisor.ord_mul,
      MMP.Mori.PrimeDivisor.ord_zpow]
    push_cast
    rw [hΓ₀'c, hE₀'c, hmaxc, hmaxN, hHc, hmaxF, hD₁Yc, hq', hNdef, hN₁, hN₀, ha_def]
    simp only [zsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hHT : H.coeff T = 0 := by
    by_contra h
    exact hHS₀ T h hTS₀
  have hET : E.coeff T = 0 := by
    have h := congrArg (fun G : QDivisor Y => G.coeff T) hΓE
    simp only [DivisorWithCoeffs.coeff_zero] at h
    change min (Γ₀.coeff T) (E.coeff T) = 0 at h
    rw [hΓT] at h
    have h0 : 0 ≤ E.coeff T := hE0 T
    rcases le_total 1 (E.coeff T) with h1 | h1
    · rw [min_eq_left h1] at h
      norm_num at h
    · rw [min_eq_right h1] at h
      exact h
  have hθT : T.ord θ = 0 := by
    have hDpbT : Dpb.coeff T = 0 := by
      rw [MMP.Positivity.coeff_eq_of_isPullback T S hTS (hDC.zsmul _) hDpb,
        DivisorWithCoeffs.coeff_smul, hDS, smul_zero]
    have hDintT : (Dint.coeff T : ℚ) = q' := by
      have h := congrArg (fun G : QDivisor Y => G.coeff T) hDint
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
      rw [h, coeff_preparedBoundary, hHT, hFT₀, hΓT]
      simp
    have hE'T : E'.coeff T = 0 := by
      rw [hE'def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        DivisorWithCoeffs.coeff_smul]
      have h1 : E₀'.coeff T = 0 := by
        have := hE₀'c T
        rw [hET, mul_zero] at this
        exact_mod_cast this
      have h2 : ((-F₀) ⊔ 0 : Divisor Y).coeff T = 0 := by
        change ((-F₀) ⊔ 0 : Divisor Y) T = 0
        rw [Finsupp.sup_apply]
        change max (-(F₀.coeff T)) 0 = 0
        rw [hFT₀]
        rfl
      rw [h1, h2]
      simp
    have h := congrArg (fun G : Divisor Y => (G.coeff T : ℚ)) hDYeq
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      MMP.Mori.coeff_principalDivisor, smul_eq_mul] at h
    rw [hqΔ'] at h
    rw [hKYT, hDpbT, hE'T] at h
    push_cast at h
    rw [hDintT] at h
    have : ((T.ord θ : ℤ) : ℚ) = 0 := by linarith only [h]
    exact_mod_cast this
  obtain ⟨hE'0, hE'ex⟩ := nonneg_and_map_genericPoint_ne μ E E₀' F₀ (N₀ * a * M * m * q)
    (N₀ * c * M * d₀ * m * q) hE₀'c hE0 fun P hP Γ => hP.elim
      (fun h => map_genericPoint_ne_of_isExceptional P (hEx P h) Γ)
      (fun h => map_genericPoint_ne_of_isExceptional P (hF₀ex P h) Γ)
  -- the degree `q'` of the prepared algebra
  have hqΔ : ((q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
      (a : ℚ)⁻¹ • Divisor.toQDivisor H +
      ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
        ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)))).IsCartierDivisor :=
    ⟨Dint, hDint, MMP.Fourfold.isCartier_of_isSmoothScheme hsm _⟩
  have hne : imageSeries ((q' : ℤ) • KY + ((q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
      (a : ℚ)⁻¹ • Divisor.toQDivisor H +
      ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
        ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)))).roundDown) T 1 ≠ ⊥ :=
    imageSeries_one_ne_bot_of_model hXnv μ hY hμ S T hTS (hDC.zsmul _) hNpb hE'0 hE'ex θ
      hθT hDYeq (φ ^ kk) hφk hφkS
  have hgen : ∀ Q : MMP.Mori.PrimeDivisor T.idealSheaf.subscheme,
      (H.restrictPrimeDivisor T).coeff Q ≠ 0 → ∀ n : ℕ, 0 < n → ∃ j : ℕ, 0 < j ∧ ∃ k : ℤ,
        (n : ℤ) * k < j ∧ ∃ h ∈ imageSeries ((q' : ℤ) • KY + ((q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
        (a : ℚ)⁻¹ • Divisor.toQDivisor H +
        ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
          ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)))).roundDown) T j,
          h ≠ 0 ∧ WithZero.exp ((j : ℤ) *
            (((q' : ℤ) • KY + ((q' : ℚ) • (Divisor.toQDivisor (Finsupp.single T 1) +
        (a : ℚ)⁻¹ • Divisor.toQDivisor H +
        ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
          ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)))).roundDown).restrictPrimeDivisor T).coeff Q - k) ≤ Q.divisorialValuation h := by
    intro Q hQ n hn
    obtain ⟨h, hh, hh0, hord⟩ := exists_mem_imageSeries_ord_add_eq hXnv μ hY hμ S T hsm hTsm hTS
      (hDC.zsmul _) (by rw [DivisorWithCoeffs.coeff_smul, hDS, smul_zero]) hNpb hE'0 hE'ex θ hθT
      hDYeq (φ ^ kk) (hBY _) hφk hφkS
    refine ⟨1, one_pos, 0, by simp, h, hh, hh0, ?_⟩
    have hZQ : (Zeff.restrictPrimeDivisor T).coeff Q = 0 := by
      by_contra hZ
      have hmemΞ : T.idealSheaf.subschemeι Q.genericPoint ∈ Ξ :=
        Finset.mem_image.mpr ⟨Q, Finsupp.mem_support_iff.mpr hZ, rfl⟩
      apply hHΞ _ hmemΞ
      haveI : IsNoetherian Y := ⟨⟩
      rw [DivisorWithCoeffs.coeff_restrictPrimeDivisor H T hHT Q, Finsupp.sum] at hQ
      obtain ⟨E, hE, hE0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
      rw [DivisorWithCoeffs.mem_supp_iff]
      refine ⟨E, Finsupp.mem_support_iff.mp hE, ?_⟩
      by_contra hnot
      apply hE0
      rw [MMP.Mori.PrimeDivisor.intersectionLength_eq_zero_of_notMem _ E hnot, zero_smul]
    rw [Q.divisorialValuation_eq_exp_neg_ord hh0, WithZero.exp_le_exp]
    have h1 := hord Q
    rw [← hφYdef, ← hZdef, hZQ] at h1
    rw [Nat.cast_one, one_mul, sub_zero]
    linarith only [h1]
  obtain ⟨Gfin, hGfin⟩ := restrictedImageAlgebra_fg_of_birationalFiniteGenerationProperty d hd hF
    (A₀ := Γ(Z, ⊤)) Y (μ ≫ sX) π hπ hπp hsm KY hKY T hKYT hTsm H a
    ((a : ℚ)⁻¹ • Divisor.toQDivisor H)
    ((Γ₀ - Divisor.toQDivisor (Finsupp.single T 1)) +
      ((N' * m₀ : ℕ) : ℚ)⁻¹ • Divisor.toQDivisor (F₀ ⊔ 0)) _ hH0 hHa ha3 rfl hBY0 rfl hfloor
    hpltY hpltY' hcan T₀ (κ ≫ sZ) (κ ≫ Z.isoSpec.hom) fT hg hgfin hT₀ hT₀a hfg hfTp hfTb q'
    hq'0 hqΔ hne hgen
  -- the transport to `X`
  have hNS : ((N : ℤ) • D).coeff S = 0 := by rw [DivisorWithCoeffs.coeff_smul, hDS, smul_zero]
  have hfin := finiteType_weilRestriction_of_model hXnv μ hY hμ f S T hTS (hDC.zsmul _)
    hNS hNpb hE'0 hE'ex θ hθT hDYeq Gfin hGfin
  exact ⟨N, hN, hfin⟩

/-! ### Veronese descent in a polynomial ring -/

section Veronese

variable {A L : Type*} [CommRing A] [Field L] [Algebra A L] (R : Subalgebra A L[X])

/-- The elements of a subalgebra `R ⊆ L[t]` homogeneous of degree `m` in `t`. -/
private def degreePart (m : ℕ) : Submodule A R where
  carrier := {x | ∀ i, i ≠ m → (x : L[X]).coeff i = 0}
  add_mem' {x y} hx hy i hi := by
    change ((x : L[X]) + (y : L[X])).coeff i = 0
    rw [coeff_add, hx i hi, hy i hi, add_zero]
  zero_mem' i _ := by
    change (0 : L[X]).coeff i = 0
    rw [coeff_zero]
  smul_mem' a x hx i hi := by
    change (a • (x : L[X])).coeff i = 0
    rw [coeff_smul, hx i hi, smul_zero]

variable {R}

private theorem coe_eq_monomial_of_mem_degreePart {m : ℕ} {x : R} (hx : x ∈ degreePart R m) :
    (x : L[X]) = monomial m ((x : L[X]).coeff m) := by
  ext i
  rw [coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hx i (Ne.symm h)

private theorem gradedMonoid_degreePart : SetLike.GradedMonoid (degreePart R) where
  one_mem i hi := by
    change (1 : L[X]).coeff i = 0
    rw [coeff_one, if_neg hi]
  mul_mem {m n x y} hx hy i hi := by
    change ((x : L[X]) * (y : L[X])).coeff i = 0
    rw [coe_eq_monomial_of_mem_degreePart hx, coe_eq_monomial_of_mem_degreePart hy,
      monomial_mul_monomial, coeff_monomial, if_neg (Ne.symm hi)]

private theorem coeff_coeAddMonoidHom_degreePart (x : DirectSum ℕ fun m => degreePart R m)
    (i : ℕ) : ((DirectSum.coeAddMonoidHom (degreePart R) x : R) : L[X]).coeff i =
      ((x i : R) : L[X]).coeff i := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    rw [DirectSum.coeAddMonoidHom_of, DirectSum.of_apply]
    split_ifs with h
    · subst h; rfl
    · change ((y : R) : L[X]).coeff i = (0 : L[X]).coeff i
      rw [coeff_zero]
      exact y.2 i (Ne.symm h)
  | add x y hx hy => simp [map_add, Polynomial.coeff_add, hx, hy]

variable (hgr : ∀ q ∈ R, ∀ m, monomial m (q.coeff m) ∈ R)

include hgr

private theorem isInternal_degreePart : DirectSum.IsInternal (degreePart R) := by
  classical
  constructor
  · intro x y hxy
    ext m i
    have hx := coeff_coeAddMonoidHom_degreePart x m
    have hy := coeff_coeAddMonoidHom_degreePart y m
    rw [coe_eq_monomial_of_mem_degreePart (x m).2,
      coe_eq_monomial_of_mem_degreePart (y m).2, coeff_monomial, coeff_monomial, ← hx, ← hy, hxy]
  · intro p
    refine ⟨∑ m ∈ (p : L[X]).support, DirectSum.of (fun m => degreePart R m) m
      ⟨⟨monomial m ((p : L[X]).coeff m), hgr _ p.2 m⟩,
        fun i hi => by simp [coeff_monomial, Ne.symm hi]⟩, ?_⟩
    apply Subtype.ext
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    rw [AddSubmonoidClass.coe_finset_sum]
    exact (as_sum_support _).symm

/-- The grading of `R ⊆ L[t]` by the degree in `t`. -/
private noncomputable abbrev degreeGradedAlgebra : GradedAlgebra (degreePart R) :=
  { gradedMonoid_degreePart, (isInternal_degreePart hgr).chooseDecomposition with }

private theorem coe_decompose_degreePart (x : R) (n : ℕ) :
    letI := degreeGradedAlgebra hgr
    ((DirectSum.decompose (degreePart R) x n : R) : L[X]) =
      monomial n ((x : L[X]).coeff n) := by
  letI := degreeGradedAlgebra hgr
  rw [coe_eq_monomial_of_mem_degreePart (DirectSum.decompose _ x n).2,
    ← coeff_coeAddMonoidHom_degreePart]
  congr 3
  exact congrArg _ (DirectSum.Decomposition.left_inv (ℳ := degreePart R) x)

/-- **Veronese descent in `L[t]`.** Let `R ⊆ L[t]` be an `A`-subalgebra, `A` Noetherian, containing
the homogeneous components of its elements. If the algebra of `q` with `q(t^N) ∈ R` is finitely
generated over `A`, for some `N ≥ 1`, so is `R`. -/
private theorem fg_of_fg_comap_expand [IsNoetherianRing A] {N : ℕ} (hN : 0 < N)
    (h : (R.comap ((expand L N).restrictScalars A)).FG) : R.FG := by
  letI := degreeGradedAlgebra hgr
  rw [Subalgebra.fg_iff_finiteType,
    MMP.Fourfold.finiteType_iff_veroneseSubalgebra_fg (degreePart R) hN]
  have hmap : (MMP.Fourfold.veroneseSubalgebra (degreePart R) N).map R.val =
      (R.comap ((expand L N).restrictScalars A)).map ((expand L N).restrictScalars A) := by
    ext x
    simp only [Subalgebra.mem_map, Subalgebra.mem_comap, AlgHom.coe_restrictScalars',
      Subalgebra.coe_val]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hv : ∀ n, ¬ N ∣ n → (y : L[X]).coeff n = 0 := fun n hn => by
        have := MMP.Fourfold.mem_veroneseSubalgebra_iff.mp hy n hn
        have h2 := congrArg (fun z : R => (z : L[X])) this
        simp only [coe_decompose_degreePart hgr, ZeroMemClass.coe_zero] at h2
        exact (monomial_eq_zero_iff _ _).mp h2
      have he : expand L N (contract N (y : L[X])) = y := by
        ext n
        rw [coeff_expand hN]
        split_ifs with hn
        · obtain ⟨k, rfl⟩ := hn
          rw [coeff_contract hN.ne', Nat.mul_div_cancel_left k hN, mul_comm]
        · exact (hv n hn).symm
      exact ⟨contract N (y : L[X]), by rw [he]; exact y.2, he⟩
    · rintro ⟨p, hp, rfl⟩
      refine ⟨⟨_, hp⟩, MMP.Fourfold.mem_veroneseSubalgebra_iff.mpr fun n hn => ?_, rfl⟩
      apply Subtype.ext
      rw [coe_decompose_degreePart hgr]
      simp [coeff_expand hN, hn]
  exact Subalgebra.fg_of_fg_map _ R.val Subtype.val_injective (hmap ▸ h.map _)

end Veronese

/-- **Veronese descent for ring maps into `L[t]`.** Let `ι : A →+* L`, `A` Noetherian, and let
`R, R' ⊆ L[t]` be subrings containing the constants `ι(A)`, with `R` containing the homogeneous
components of its elements and `R' = {q | q(t^N) ∈ R}` for some `N ≥ 1`. If `R'` is of finite type
over `A`, so is `R`. -/
private theorem finiteType_codRestrict_of_comap_expand {A L : Type*} [CommRing A]
    [IsNoetherianRing A] [Field L] (ι : A →+* L) (R R' : Subring L[X])
    (hC : ∀ a, C (ι a) ∈ R) (hC' : ∀ a, C (ι a) ∈ R')
    (hgr : ∀ q ∈ R, ∀ m, monomial m (q.coeff m) ∈ R) {N : ℕ} (hN : 0 < N)
    (hR' : ∀ q, q ∈ R' ↔ expand L N q ∈ R)
    (h : ((C.comp ι).codRestrict R' hC').FiniteType) :
    ((C.comp ι).codRestrict R hC).FiniteType := by
  letI := ι.toAlgebra
  have hmem : ∀ (S : Subring L[X]), (∀ a, C (ι a) ∈ S) →
      ∀ a, algebraMap A L[X] a ∈ S := fun S hS a => by
    rw [Polynomial.algebraMap_apply, RingHom.algebraMap_toAlgebra]
    exact hS a
  let RA : Subalgebra A L[X] := { R with algebraMap_mem' := hmem R hC }
  let RA' : Subalgebra A L[X] := { R' with algebraMap_mem' := hmem R' hC' }
  have key : ∀ (SA : Subalgebra A L[X]) (hS : ∀ a, C (ι a) ∈ SA.toSubring),
      ((C.comp ι).codRestrict SA.toSubring hS).FiniteType ↔ SA.FG := by
    intro SA hS
    show (algebraMap A SA).FiniteType ↔ SA.FG
    exact RingHom.finiteType_algebraMap.trans (Subalgebra.fg_iff_finiteType SA).symm
  have hcomap : RA.comap ((expand L N).restrictScalars A) = RA' := by
    ext q
    rw [Subalgebra.mem_comap, AlgHom.coe_restrictScalars']
    exact (hR' q).symm
  refine (key RA hC).mpr (fg_of_fg_comap_expand hgr hN ?_)
  rw [hcomap]
  exact (key RA' hC').mp h

/-! ### Veronese descent for the restriction algebra -/

section VeroneseRestriction

variable {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]

/-- A polynomial over `k(S)` lies in the restriction algebra of `B` exactly when its coefficient
in each degree `j` is the residue of a section of `𝒪_X(jB)`. -/
private theorem mem_range_weilRestrictionMap_iff {B : Divisor X} {S : MMP.Mori.PrimeDivisor X}
    (hBS : B.coeff S = 0) (q : (X.residueField S.genericPoint)[X]) :
    q ∈ (weilRestrictionMap hBS).range ↔ ∀ j : ℕ, ∃ g ∈ divisorialSections ((j : ℕ) • B),
      ∃ hg : g ∈ localSubring S, residueAlong S ⟨g, hg⟩ = q.coeff j := by
  change q ∈ weilRestrictionAlgebra hBS ↔ _
  rw [mem_weilRestrictionAlgebra_iff]
  constructor
  · rintro ⟨p, hp, hpq⟩ j
    obtain ⟨a, ha, hq⟩ := hpq j
    exact ⟨p.coeff j, hp j, ⟨a, ha⟩, by rw [residueAlong_eq _ ha, hq]⟩
  · intro h
    choose g hg hgl hgr using h
    have hc : ∀ n, (∑ m ∈ q.support, monomial m (g m)).coeff n =
        if n ∈ q.support then g n else 0 := fun n => by
      rw [finset_sum_coeff]
      simp only [coeff_monomial]
      exact Finset.sum_ite_eq' _ _ _
    refine ⟨∑ m ∈ q.support, monomial m (g m), fun n => ?_, fun n => ?_⟩
    · rw [hc]
      split_ifs
      · exact hg n
      · exact zero_mem _
    · rw [hc]
      split_ifs with hn
      · obtain ⟨a, ha⟩ := hgl n
        exact ⟨a, ha, by rw [← hgr n, residueAlong_eq _ ha]⟩
      · refine ⟨0, by simp, ?_⟩
        rw [map_zero]
        exact notMem_support_iff.mp hn

/-- The functions pulled back from `Z` are regular along every prime divisor of `X`. -/
private theorem mem_localSubring_appTop (f : X ⟶ Z) (S : MMP.Mori.PrimeDivisor X)
    (a : Γ(Z, ⊤)) : globalSectionsToRationalFunctions (f.appTop.hom a) ∈ localSubring S :=
  divisorialSections_le_localSubring (B := (0 : Divisor X)) (S := S) (by simp) 0
    (by rw [zero_smul]; exact mem_divisorialSections_zero_iff.mpr ⟨_, rfl⟩)

/-- The residues along `S` of the functions pulled back from `Z`, `Γ(Z, 𝒪_Z) → k(S)`. -/
private noncomputable def baseResidue (f : X ⟶ Z) (S : MMP.Mori.PrimeDivisor X) :
    Γ(Z, ⊤) →+* X.residueField S.genericPoint :=
  (residueAlong S).comp (((globalSectionsToRationalFunctions (X := X)).comp
    f.appTop.hom).codRestrict (localSubring S) (mem_localSubring_appTop f S))

private theorem C_baseResidue_mem_range (f : X ⟶ Z) (S : MMP.Mori.PrimeDivisor X)
    {B : Divisor X} (hBS : B.coeff S = 0) (a : Γ(Z, ⊤)) :
    C (baseResidue f S a) ∈ (weilRestrictionMap hBS).range := by
  refine (mem_range_weilRestrictionMap_iff hBS _).mpr fun j => ?_
  rw [coeff_C]
  split_ifs with hj
  · subst hj
    exact ⟨_, by rw [zero_smul]; exact mem_divisorialSections_zero_iff.mpr ⟨_, rfl⟩,
      mem_localSubring_appTop f S a, rfl⟩
  · exact ⟨0, zero_mem _, zero_mem _, map_zero (residueAlong S)⟩

/-- The structure map `Γ(Z, 𝒪_Z) → Γ(X, 𝒪_X) → ⊕ H⁰(X, 𝒪_X(mB)) → k(S)[t]` of the restriction
algebra is the inclusion of the constants `baseResidue f S`. -/
private theorem weilRestriction_comp_appTop_eq (f : X ⟶ Z) (S : MMP.Mori.PrimeDivisor X)
    {B : Divisor X} (hBS : B.coeff S = 0) :
    (weilRestrictionMap hBS).rangeRestrict.comp
      (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict (weilSectionAlgebra B)
        (fun s => Subring.mem_comap.mp ((comap_C_weilSectionAlgebra B).ge ⟨s, rfl⟩))).comp
          f.appTop.hom) =
      (C.comp (baseResidue f S)).codRestrict (weilRestrictionMap hBS).range
        (C_baseResidue_mem_range f S hBS) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  change weilRestrictionMap hBS ⟨C (globalSectionsToRationalFunctions (f.appTop.hom a)), _⟩ =
    C (baseResidue f S a)
  ext m
  obtain ⟨a', ha'⟩ := mem_localSubring_appTop f S a
  rw [coeff_C]
  split_ifs with hm
  · subst hm
    rw [coeff_weilRestrictionMap hBS _ 0 (a := a') (by rw [coeff_C_zero]; exact ha')]
    exact (residueAlong_eq _ ha').symm
  · rw [coeff_weilRestrictionMap hBS _ m (a := 0) (by simp [coeff_C, hm])]
    exact map_zero _

end VeroneseRestriction

/-- **Veronese descent for the restricted algebra.** If the restricted algebra of `N • D` along
`S` is finitely generated over `Γ(Z, 𝒪_Z)`, so is that of `D`: after regrading `t^N ↦ t`, the
former is the `N`-th Veronese subalgebra of the latter, a graded domain inside `k(S)[t]`
(`MMP.Fourfold.finiteType_iff_veroneseSubalgebra_fg`). -/
private theorem finiteType_of_finiteType_smul
    {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Z) [IsAffine Z] (hZ : IsNoetherianRing Γ(Z, ⊤))
    (S : MMP.Mori.PrimeDivisor X) (D : Divisor X) (hDS : D.coeff S = 0) (N : ℕ) (hN : 0 < N)
    (h : ((weilRestrictionMap (B := (N : ℤ) • D) (S := S)
          (by rw [DivisorWithCoeffs.coeff_smul, hDS, smul_zero])).rangeRestrict.comp
        (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict
          (weilSectionAlgebra ((N : ℤ) • D))
          (fun s => Subring.mem_comap.mp
            ((comap_C_weilSectionAlgebra ((N : ℤ) • D)).ge ⟨s, rfl⟩))).comp
            f.appTop.hom)).FiniteType) :
    ((weilRestrictionMap hDS).rangeRestrict.comp
      (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict (weilSectionAlgebra D)
        (fun s => Subring.mem_comap.mp ((comap_C_weilSectionAlgebra D).ge ⟨s, rfl⟩))).comp
          f.appTop.hom)).FiniteType := by
  haveI := hZ
  have hNS : ((N : ℤ) • D).coeff S = 0 := by rw [DivisorWithCoeffs.coeff_smul, hDS, smul_zero]
  have hsm : ∀ i : ℕ, i • ((N : ℤ) • D) = (i * N) • D := fun i => by
    rw [Nat.cast_smul_eq_nsmul ℤ N D, smul_smul]
  rw [weilRestriction_comp_appTop_eq f S hDS]
  rw [weilRestriction_comp_appTop_eq f S hNS] at h
  refine finiteType_codRestrict_of_comap_expand (baseResidue f S) _ _ _ _ (fun q hq m => ?_) hN
    (fun q => ?_) h
  · rw [mem_range_weilRestrictionMap_iff] at hq ⊢
    intro j
    rw [coeff_monomial]
    split_ifs with hmj
    · subst hmj
      exact hq m
    · exact ⟨0, zero_mem _, zero_mem _, map_zero (residueAlong S)⟩
  · rw [mem_range_weilRestrictionMap_iff, mem_range_weilRestrictionMap_iff]
    constructor
    · intro hq j
      rw [coeff_expand hN]
      split_ifs with hj
      · obtain ⟨k, rfl⟩ := hj
        rw [Nat.mul_div_cancel_left k hN]
        obtain ⟨g, hg, hl, hr⟩ := hq k
        rw [hsm, mul_comm] at hg
        exact ⟨g, hg, hl, hr⟩
      · exact ⟨0, zero_mem _, zero_mem _, map_zero (residueAlong S)⟩
    · intro hq i
      obtain ⟨g, hg, hl, hr⟩ := hq (i * N)
      rw [coeff_expand hN, if_pos (dvd_mul_left N i), Nat.mul_div_cancel i hN] at hr
      exact ⟨g, by rw [hsm]; exact hg, hl, hr⟩

end MMP.FourfoldProofs.FourfoldPreparePltRestrictedAlgebraProof

end

section

/-!
# Finite generation of a plt restricted adjoint algebra with an ample boundary

Assume the birational finite-generation property `F(d)` for some `d ≥ 2`. Let `f : X ⟶ Z` be a
projective morphism of complex varieties, with `Z` normal and affine and `X` normal,
`ℚ`-factorial and of dimension `d + 1`. Let `(X, S + B)` be a rational plt pair with `S` a prime
divisor, `B ≥ 0`, `S` not a component of `B` and every coefficient of `B` less than one. Let `A`
be a `ℚ`-divisor in a relatively ample rational Cartier class, and put `Δ = S + B + A`. If some
multiple of `K_X + Δ` has a section not vanishing identically along `S`, and `S` maps
birationally onto its image in `Z`, then for every Cartier multiple `D = q(K_X + Δ)` the
restricted algebra `⊕_j im(H⁰(X, jD) → k(S))` is a finitely generated `Γ(Z, 𝒪_Z)`-algebra.

## Main results

* `MMP.Fourfold.finiteType_weilRestrictionAlgebra_of_birationalFiniteGenerationProperty`.

## Implementation notes

The source chooses the representative `A` of the ample class very general, with sufficiently
large denominator. The statement is made for every `ℚ`-divisor `A` in the class: if
`A' ∼_ℚ A` and neither contains `S`, then `m(A - A') = div φ` with `ord_S φ = 0`, so
multiplication by powers of `φ` identifies the Veronese subalgebras of the two restricted
algebras, and finite generation passes from one to the other by the Veronese lemma. The
hypothesis that a multiple of `K_X + Δ` has a section not vanishing on `S` is invariant in the
same way.

The restricted algebra of an integral divisor `D` is `MMP.Fourfold.weilRestrictionAlgebra`, which
needs `D` to have coefficient zero along `S`; for `D = q(K_X + Δ)` this is the normalisation in
which `K_X` has coefficient `-1` along `S`, under which `(K_X + S)|_S = K_S`. It is a
`Γ(Z, 𝒪_Z)`-algebra through `Γ(Z, 𝒪_Z) → Γ(X, 𝒪_X)` and the degree-zero inclusion followed by
restriction; finite generation is `RingHom.FiniteType` of that map.

## References

* [C. Hacon, J. McKernan, *Extension theorems and the existence of flips*][HaconMcKernan2007]
-/

open CategoryTheory AlgebraicGeometry Polynomial

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Finite generation of a plt restricted adjoint algebra with an ample boundary.** Assume
`F(d)` (`MMP.Fourfold.BirationalFiniteGenerationProperty d`) with `d ≥ 2`. Let `f : X ⟶ Z` be a
projective morphism of complex varieties, `Z` normal affine, `X` normal `ℚ`-factorial of
dimension `d + 1` with canonical divisor `K`, `(X, S + B)` plt with `S` prime, `B ≥ 0` rational,
`B.coeff S = 0` and all coefficients of `B` less than one. Let `A₀` be `f`-ample `ℚ`-Cartier,
`A ∼_ℚ A₀`, and `Δ = S + B + A`. Suppose some multiple `m(K + Δ)` is an integral divisor with a
nonzero section `φ` not vanishing along `S` (`ord_S φ + (m(K + Δ))_S = 0`), and that `S` maps
birationally onto its scheme-theoretic image in `Z`. Then for every Cartier divisor `D` with
`D = q(K + Δ)` and `D.coeff S = 0`, the restriction algebra `weilRestrictionAlgebra` of `D` along
`S` is of finite type over `Γ(Z, 𝒪_Z)`. -/
@[mmp "thm_fourfold_prepare_plt_restricted_algebra"]
public theorem finiteType_weilRestrictionAlgebra_of_birationalFiniteGenerationProperty
    {d : ℕ} (hd : 2 ≤ d) (hF : BirationalFiniteGenerationProperty d)
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (hfp : IsProjectiveMorphism f) (hZ : IsNormalVariety ℂ sZ) [IsAffine Z]
    (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = d + 1)
    (K : Divisor X) (hK : K.IsCanonicalDivisor sX (d + 1))
    (S : Mori.PrimeDivisor X) (B : QDivisor X) (hB : 0 ≤ B) (hBS : B.coeff S = 0)
    (hB1 : ∀ P, B.coeff P < 1)
    (hplt : IsPltPair sX (d + 1) K (Finsupp.single S 1 + B))
    (A₀ : QDivisor X) (hA₀ : A₀.HasRelativelyAmpleMultiple f)
    (A : QDivisor X) (hA : A.QLinearlyEquivalent A₀)
    (hsec : ∃ m : ℕ, 0 < m ∧ ∃ D : Divisor X,
      Divisor.toQDivisor D = (m : ℤ) • (Divisor.toQDivisor K + (Finsupp.single S 1 + B + A)) ∧
      ∃ φ : (RationalFunctions X)ˣ, (φ : RationalFunctions X) ∈ divisorialSections D ∧
        S.ord φ + D.coeff S = 0)
    (hSbir : IsBirationalMorphism (S.idealSheaf.subschemeι ≫ f).toImage)
    (q : ℕ) (D : Divisor X) (hDC : D.IsCartier)
    (hD : Divisor.toQDivisor D = (q : ℤ) • (Divisor.toQDivisor K + (Finsupp.single S 1 + B + A)))
    (hDS : D.coeff S = 0) :
    ((weilRestrictionMap hDS).rangeRestrict.comp
      (((C.comp (globalSectionsToRationalFunctions (X := X))).codRestrict (weilSectionAlgebra D)
        (fun s => Subring.mem_comap.mp ((comap_C_weilSectionAlgebra D).ge ⟨s, rfl⟩))).comp
          f.appTop.hom)).FiniteType := by
  open MMP.FourfoldProofs.FourfoldPreparePltRestrictedAlgebraProof in
  obtain ⟨N, hN, h⟩ := exists_veronese_finiteType hd hF f hf hfp hZ hXQ hdim K hK S B hB hBS
    hB1 hplt A₀ hA₀ A hA hsec hSbir q D hDC hD hDS
  have hZN : IsNoetherianRing Γ(Z, ⊤) := by
    haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Z⟩
  open MMP.FourfoldProofs.FourfoldPreparePltRestrictedAlgebraProof in
  exact finiteType_of_finiteType_smul f hZN S D hDS N hN h

end MMP.Fourfold

end
