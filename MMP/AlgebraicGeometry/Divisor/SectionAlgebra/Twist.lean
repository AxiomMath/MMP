module

public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneChartAgreement
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# The divisorial sheaf of the birational transform is `𝒪(1)` on the charts

Let `Y` be an integral, quasi-compact, locally Noetherian, normal scheme, `D` a Weil divisor on
`Y` and `g : Z = Proj_Y ⨁_n 𝒪_Y(nD) ⟶ Y`, where the divisorial algebra is generated in degree
one and `Z` is normal. Over an affine open `W` of `Y`, the restriction of `𝒪_Z(g⁻¹_* D)` to the
chart `Proj ⨁_n 𝒪_Y(nD)(W)` is isomorphic to the twisting sheaf `𝒪(1)` of the chart.

On the standard open `D₊(a)`, `a` a nonzero section of degree one, both sheaves are free of rank
one: `𝒪(1)` on the generator `a`, and `𝒪_Z(g⁻¹_* D)` on the pull-back of `a`, viewed as a rational
function, since the pull-back of `a⁻¹` is a local equation of `g⁻¹_* D` there. Matching the
generators gives comparisons over the opens of `D₊(a)`, and two charts give the same comparison
because the transition function `a / b` of `𝒪(1)` on `D₊(a) ∩ D₊(b)` is the pull-back of the
rational function `a / b`.

## Main definitions

* `MMP.Mori.Divisor.restrictFrameEquiv`: for a local equation `ψ` of `D` on the image of an open
  `U` under an open immersion `j`, multiplication by `ψ⁻¹` identifies `𝒪` with the restriction of
  `𝒪_X(D)` along `j` over every open of `U`.
* `MMP.Mori.Divisor.projLocalEquiv`: the chartwise comparisons `𝒪(1) ≅ j^* 𝒪_X(D)` over the
  standard opens of `Proj`, as a gluing datum.

## Main results

* `MMP.Mori.Divisor.nonempty_restrict_divisorialSheaf_iso_twistingSheaf`: `j^* 𝒪_X(D) ≅ 𝒪(1)`.
* `DivisorialSectionAlgebra.nonempty_restrict_divisorialSheaf_iso_twistingSheaf_of_transition`:
  `𝒪_Z(g⁻¹_* D)` is `𝒪(1)` on the charts.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998], Lemma 6.2.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite HomogeneousLocalization

universe u

namespace MMP.ProjFraction

attribute [local instance] ProjectiveSpectrum.isPrime

variable {S : Type u} [CommRing S] {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The fraction `a / b`, for `a`, `b` homogeneous of the same degree, at a point of `D₊(b)`. -/
def fracFun {d : ℕ} {a b : S} (ha : a ∈ 𝒮 d) (hb : b ∈ 𝒮 d)
    {W : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 b) (x : W) :
    AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.mk ⟨d, ⟨a, ha⟩, ⟨b, hb⟩, hW x.2⟩

/-- The value of `fracFun` at a point is the fraction `a / b` in the localization at that point. -/
theorem val_fracFun {d : ℕ} {a b : S} (ha : a ∈ 𝒮 d) (hb : b ∈ 𝒮 d)
    {W : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 b) (x : W) :
    (fracFun 𝒮 ha hb hW x).val = Localization.mk a ⟨b, hW x.2⟩ :=
  HomogeneousLocalization.val_mk _

/-- The section `a / b` of the structure sheaf of `Proj 𝒮` over an open contained in `D₊(b)`. -/
def fracSection {d : ℕ} {a b : S} (ha : a ∈ 𝒮 d) (hb : b ∈ 𝒮 d)
    {W : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 b) :
    Γ(AlgebraicGeometry.Proj 𝒮, W) :=
  (show (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) from
    ⟨fracFun 𝒮 ha hb hW, fun x => ⟨W, x.2, 𝟙 _, d, ⟨a, ha⟩, ⟨b, hb⟩, fun y => hW y.2,
      fun _ => rfl⟩⟩)

/-- The restriction of the section `a / b` to a smaller open is the section `a / b` there. -/
theorem map_fracSection {d : ℕ} {a b : S} (ha : a ∈ 𝒮 d) (hb : b ∈ 𝒮 d)
    {V W : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮)}
    (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒮 b) (hWV : W ≤ V) :
    ((AlgebraicGeometry.Proj 𝒮).presheaf.map (homOfLE hWV).op).hom (fracSection 𝒮 ha hb hV) =
      fracSection 𝒮 ha hb (hWV.trans hV) :=
  rfl

/-- `b / b = 1`. -/
@[simp]
theorem fracSection_self {d : ℕ} {b : S} (hb : b ∈ 𝒮 d)
    {W : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 b) :
    fracSection 𝒮 hb hb hW = 1 := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  change (fracFun 𝒮 hb hb hW x).val = (1 : AtPrime 𝒮 x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_one, val_fracFun, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- `(a / b) · b = a` at every point of `D₊(b)`, for `b` of degree one, read against the
trivializing value `b` of `𝒪(1)`. -/
theorem val_fracFun_mul_trivializingFun {a b : S} (ha : a ∈ 𝒮 1) (hb : b ∈ 𝒮 1)
    {W : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 b) (x : W) :
    (fracFun 𝒮 ha hb hW x).val *
        Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun 𝒮 1 hW x =
      Localization.mk a 1 := by
  rw [val_fracFun, Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun,
    Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, Int.toNat_one, pow_one,
    show ((-1 : ℤ)).toNat = 0 from rfl, pow_zero, one_mul, mul_one]
  ring

end MMP.ProjFraction

namespace MMP.Mori.Divisor

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {D : Divisor X}
  {P : Scheme.{u}} (j : P ⟶ X) [IsOpenImmersion j] {U : P.Opens} {ψ : (RationalFunctions X)ˣ}

/-- A section of the restriction of `𝒪_X(D)` along `j` over `V`, read in `𝒦_X(j(V))`. -/
def restrictVal {V : P.Opens} (t : (D.divisorialSheaf.restrict j).val.obj (op V)) :
    ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V))) :=
  (show D.divisorialSubmodule (j ''ᵁ V) from t).1

omit [CompactSpace X] in
/-- Reading a section of the restriction of `𝒪_X(D)` in `𝒦_X(j(V))` is injective. -/
theorem restrictVal_injective {V : P.Opens} :
    Function.Injective (restrictVal (D := D) j (V := V)) :=
  fun _ _ h => Subtype.ext h

/-- The local generator `ψ⁻¹` of `𝒪_X(D)` over `j(V)`, for a local equation `ψ` of `D` on `j(U)`
and an open `V ⊆ U`, as a section of the restriction of `𝒪_X(D)` along `j`. -/
def restrictFrameSection (hψ : D.IsLocalEquation (j ''ᵁ U) ψ) {V : P.Opens} (hV : V ≤ U) :
    (D.divisorialSheaf.restrict j).val.obj (op V) :=
  ⟨rationalFunctionsRestrict (j ''ᵁ V) ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X), by
    have hψV : D.IsLocalEquation (j ''ᵁ V) ψ := hψ.mono (j.image_mono hV)
    have h := (mem_divisorialSubmodule_nsmul_iff_of_isLocalEquation hψV 1
      (rationalFunctionsRestrict (j ''ᵁ V)
        ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))).mpr
      ⟨1, by rw [map_one, mul_one, pow_one]⟩
    rwa [Nat.cast_one, one_smul] at h⟩

/-- The section `restrictFrameSection` is `ψ⁻¹` in `𝒦_X(j(V))`. -/
theorem restrictVal_restrictFrameSection (hψ : D.IsLocalEquation (j ''ᵁ U) ψ) {V : P.Opens}
    (hV : V ≤ U) :
    restrictVal j (restrictFrameSection j hψ hV) =
      rationalFunctionsRestrict (j ''ᵁ V) ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) :=
  rfl

/-- Multiplication of the generator `ψ⁻¹` by sections of `𝒪_P(V)` is a bijection onto the
restriction of `𝒪_X(D)` along `j` over `V`. -/
theorem restrictFrameSection_smul_bijective (hψ : D.IsLocalEquation (j ''ᵁ U) ψ) {V : P.Opens}
    (hV : V ≤ U) :
    Function.Bijective (LinearMap.toSpanSingleton (ToType (P.ringCatSheaf.obj.obj (op V)))
      ((D.divisorialSheaf.restrict j).val.obj (op V)) (restrictFrameSection j hψ hV)) := by
  have hunit : rationalFunctionsRestrict (j ''ᵁ V)
      ((ψ : (RationalFunctions X)ˣ) : RationalFunctions X) *
      rationalFunctionsRestrict (j ''ᵁ V) ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
        1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  constructor
  · intro r s hrs
    have h := congrArg (restrictVal j) hrs
    change (j.appIso V).inv r • rationalFunctionsRestrict (j ''ᵁ V) _ =
      (j.appIso V).inv s • rationalFunctionsRestrict (j ''ᵁ V) _ at h
    rw [Algebra.smul_def, Algebra.smul_def] at h
    have h' := congrArg (rationalFunctionsRestrict (j ''ᵁ V)
      ((ψ : (RationalFunctions X)ˣ) : RationalFunctions X) * ·) h
    simp only [mul_left_comm _ (algebraMap _ _ _), hunit, mul_one] at h'
    exact (ConcreteCategory.bijective_of_isIso (j.appIso V).inv).1
      (toRationalFunctionsPresheaf_app_injective _ h')
  · intro t
    have hψV : D.IsLocalEquation (j ''ᵁ V) ψ := hψ.mono (j.image_mono hV)
    have ht : restrictVal j t ∈ (((1 : ℕ) : ℤ) • D).divisorialSubmodule (j ''ᵁ V) := by
      rw [Nat.cast_one, one_smul]
      exact (show D.divisorialSubmodule (j ''ᵁ V) from t).2
    rw [mem_divisorialSubmodule_nsmul_iff_of_isLocalEquation hψV 1] at ht
    obtain ⟨r, hr⟩ := ht
    refine ⟨(j.appIso V).hom r, restrictVal_injective j ?_⟩
    change (j.appIso V).inv ((j.appIso V).hom r) • rationalFunctionsRestrict (j ''ᵁ V) _ = _
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, Algebra.smul_def,
      mul_comm, hr, pow_one]

/-- **The frame of `𝒪_X(D)` along an open immersion.** For a local equation `ψ` of `D` on `j(U)`,
multiplication by `ψ⁻¹` is an isomorphism `𝒪_P(V) ≅ (j^* 𝒪_X(D))(V)` for every open `V ⊆ U`. -/
def restrictFrameEquiv (hψ : D.IsLocalEquation (j ''ᵁ U) ψ) {V : P.Opens} (hV : V ≤ U) :
    ToType (P.ringCatSheaf.obj.obj (op V)) ≃ₗ[ToType (P.ringCatSheaf.obj.obj (op V))]
      (D.divisorialSheaf.restrict j).val.obj (op V) :=
  LinearEquiv.ofBijective _ (restrictFrameSection_smul_bijective j hψ hV)

/-- The frame sends `r` to `r ψ⁻¹` in `𝒦_X(j(V))`. -/
theorem restrictVal_restrictFrameEquiv (hψ : D.IsLocalEquation (j ''ᵁ U) ψ) {V : P.Opens}
    (hV : V ≤ U) (r : ToType (P.ringCatSheaf.obj.obj (op V))) :
    restrictVal j (restrictFrameEquiv j hψ hV r) =
      algebraMap Γ(X, j ''ᵁ V) _ ((j.appIso V).inv r) *
        rationalFunctionsRestrict (j ''ᵁ V)
          ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) :=
  rfl

omit [CompactSpace X] in
/-- Restricting a section of the restriction of `𝒪_X(D)` along `j` from `V` to `W` restricts its
value from `𝒦_X(j(V))` to `𝒦_X(j(W))`. -/
theorem restrictVal_restrictₛₗ {V W : P.Opens} (hWV : W ≤ V)
    (t : (D.divisorialSheaf.restrict j).val.obj (op V)) :
    restrictVal j ((D.divisorialSheaf.restrict j).val.restrictₛₗ (homOfLE hWV).op t) =
      (rationalFunctionsPresheaf X).map (homOfLE (j.image_mono hWV)).op (restrictVal j t) :=
  rfl

/-- The frame of `𝒪_X(D)` along `j` commutes with restriction. -/
theorem restrictFrameEquiv_map (hψ : D.IsLocalEquation (j ''ᵁ U) ψ) {V W : P.Opens}
    (hV : V ≤ U) (hWV : W ≤ V) (r : Γ(P, V)) :
    restrictFrameEquiv j hψ (hWV.trans hV) (P.presheaf.map (homOfLE hWV).op r) =
      (D.divisorialSheaf.restrict j).val.restrictₛₗ (homOfLE hWV).op
        (restrictFrameEquiv j hψ hV r) := by
  apply restrictVal_injective j
  change algebraMap Γ(X, j ''ᵁ W) _ ((j.appIso W).inv (P.presheaf.map (homOfLE hWV).op r)) *
      rationalFunctionsRestrict (j ''ᵁ W) ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
    (rationalFunctionsPresheaf X).map (homOfLE (j.image_mono hWV)).op
      (algebraMap Γ(X, j ''ᵁ V) _ ((j.appIso V).inv r) *
        rationalFunctionsRestrict (j ''ᵁ V) ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))
  rw [map_mul]
  congr 1
  have h : (j.appIso W).inv (P.presheaf.map (homOfLE hWV).op r) =
      X.presheaf.map (homOfLE (j.image_mono hWV)).op ((j.appIso V).inv r) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, j.appIso_inv_naturality]
    rfl
  change (toRationalFunctionsPresheaf X).app _ _ = (rationalFunctionsPresheaf X).map _
    ((toRationalFunctionsPresheaf X).app _ _)
  rw [h, toRationalFunctionsPresheaf_app_map]

/-- Two frames of `𝒪_X(D)` along `j` agree on the common opens of their domains as soon as the
coefficients differ by the transition function `u` with `ψ₁⁻¹ = u ψ₂⁻¹`. -/
theorem restrictFrameEquiv_eq_of_mul {U₁ U₂ : P.Opens} {ψ₁ ψ₂ : (RationalFunctions X)ˣ}
    (hψ₁ : D.IsLocalEquation (j ''ᵁ U₁) ψ₁) (hψ₂ : D.IsLocalEquation (j ''ᵁ U₂) ψ₂) {V : P.Opens}
    (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (u : Γ(P, V))
    (hu : algebraMap Γ(X, j ''ᵁ V) _ ((j.appIso V).inv u) *
        rationalFunctionsRestrict (j ''ᵁ V)
          ((ψ₂⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
      rationalFunctionsRestrict (j ''ᵁ V) ((ψ₁⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))
    (r₁ r₂ : Γ(P, V)) (hr : r₂ = r₁ * u) :
    restrictFrameEquiv j hψ₁ h₁ r₁ = restrictFrameEquiv j hψ₂ h₂ r₂ := by
  apply restrictVal_injective j
  change algebraMap Γ(X, j ''ᵁ V) _ ((j.appIso V).inv r₁) *
      rationalFunctionsRestrict (j ''ᵁ V) ((ψ₁⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
    algebraMap Γ(X, j ''ᵁ V) _ ((j.appIso V).inv r₂) *
      rationalFunctionsRestrict (j ''ᵁ V) ((ψ₂⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
  rw [hr, map_mul, map_mul, mul_assoc, hu]

/-! ### Gluing the frames over the standard opens of a `Proj` -/

section ProjGlue

open Stacks.AlgebraicGeometry.ProjTrivialization MMP.ProjFraction
open Stacks.SheafOfModules.OModuleLocalPresheaf

attribute [local instance] ProjectiveSpectrum.isPrime

variable {S : Type u} [CommRing S] {σ : Type u} [SetLike σ S] [AddSubgroupClass σ S]
  {𝒮 : ℕ → σ} [GradedRing 𝒮]

/-- The twisting sheaf `𝒪(1)` of `Proj 𝒮`, as a module over the structure sheaf of the scheme. -/
local notation3 (prettyPrint := false) "𝒪(1)[" 𝒮 "]" =>
  (show (AlgebraicGeometry.Proj 𝒮).Modules from ProjectiveSpectrum.Proj.twistingSheaf 𝒮 1)

/-- The comparison `𝒪(1)(V) ≅ (j^* 𝒪_X(D))(V)` over an open `V ⊆ D₊(f)`, for `f` of degree one and
`ψ` a local equation of `D` on `j(D₊(f))`: it sends `α f` to `α ψ⁻¹`. -/
def projChartEquiv (j : AlgebraicGeometry.Proj 𝒮 ⟶ X) [IsOpenImmersion j] {f : S} (hf : f ∈ 𝒮 1)
    {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 f) ψ)
    {V : (AlgebraicGeometry.Proj 𝒮).Opens} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒮 f) :
    (𝒪(1)[𝒮]).val.obj (op V) ≃ₗ[ToType ((AlgebraicGeometry.Proj 𝒮).ringCatSheaf.obj.obj (op V))]
      (D.divisorialSheaf.restrict j).val.obj (op V) :=
  let e : ToType ((AlgebraicGeometry.Proj 𝒮).ringCatSheaf.obj.obj (op V)) ≃ₗ[
      ToType ((AlgebraicGeometry.Proj 𝒮).ringCatSheaf.obj.obj (op V))]
      (𝒪(1)[𝒮]).val.obj (op V) := trivializingEquiv 𝒮 hf 1 hV
  e.symm.trans (restrictFrameEquiv j hψ hV)

/-- `projChartEquiv` is the frame `restrictFrameEquiv` applied to the coefficient of `t` against
the generator `f` of `𝒪(1)`. -/
theorem projChartEquiv_apply (j : AlgebraicGeometry.Proj 𝒮 ⟶ X) [IsOpenImmersion j] {f : S}
    (hf : f ∈ 𝒮 1) {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 f) ψ)
    {V : (AlgebraicGeometry.Proj 𝒮).Opens} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : (𝒪(1)[𝒮]).val.obj (op V)) :
    projChartEquiv j hf hψ hV t = restrictFrameEquiv j hψ hV (twistOneCoeff 𝒮 hf hV t) :=
  rfl

/-- The comparison `projChartEquiv` commutes with restriction. -/
theorem projChartEquiv_map (j : AlgebraicGeometry.Proj 𝒮 ⟶ X) [IsOpenImmersion j] {f : S}
    (hf : f ∈ 𝒮 1) {ψ : (RationalFunctions X)ˣ}
    (hψ : D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 f) ψ)
    {V W : (AlgebraicGeometry.Proj 𝒮).Opens} (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hWV : W ≤ V) (t : (𝒪(1)[𝒮]).val.obj (op V)) :
    projChartEquiv j hf hψ (hWV.trans hV) ((𝒪(1)[𝒮]).val.restrictₛₗ (homOfLE hWV).op t) =
      (D.divisorialSheaf.restrict j).val.restrictₛₗ (homOfLE hWV).op
        (projChartEquiv j hf hψ hV t) := by
  rw [projChartEquiv_apply, projChartEquiv_apply]
  have h := twistOneCoeff_map 𝒮 hf hV (hWV.trans hV) hWV t
  rw [show twistOneCoeff 𝒮 hf (hWV.trans hV) ((𝒪(1)[𝒮]).val.restrictₛₗ (homOfLE hWV).op t) =
    (AlgebraicGeometry.Proj 𝒮).presheaf.map (homOfLE hWV).op (twistOneCoeff 𝒮 hf hV t) from h]
  exact restrictFrameEquiv_map j hψ hV hWV _

/-- Two charts give the same comparison, given that the transition function `f / g` of `𝒪(1)`
relates the two local generators: `ψ_f⁻¹ = (f / g) ψ_g⁻¹` on `j(D₊(g))`. -/
theorem projChartEquiv_agree (j : AlgebraicGeometry.Proj 𝒮 ⟶ X) [IsOpenImmersion j] {f g : S}
    (hf : f ∈ 𝒮 1) (hg : g ∈ 𝒮 1) {φ ψ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 f) φ)
    (hψ : D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 g) ψ)
    (hK : algebraMap Γ(X, j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 g) _
        ((j.appIso (ProjectiveSpectrum.basicOpen 𝒮 g)).inv (fracSection 𝒮 hf hg le_rfl)) *
        rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 g)
          ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
      rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 g)
        ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))
    {V : (AlgebraicGeometry.Proj 𝒮).Opens}
    (hVf : V ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hVg : V ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (t : (𝒪(1)[𝒮]).val.obj (op V)) :
    projChartEquiv j hf hφ hVf t = projChartEquiv j hg hψ hVg t := by
  rw [projChartEquiv_apply, projChartEquiv_apply]
  have key := twistOneCoeff_mul_comm 𝒮 hf hg hVf hVg (fracSection 𝒮 hf hg hVg)
    (fracSection 𝒮 hf hf hVf)
    (fun x => (val_fracFun_mul_trivializingFun 𝒮 hf hg hVg x).trans
      (val_fracFun_mul_trivializingFun 𝒮 hf hf hVf x).symm) t
  rw [fracSection_self 𝒮 hf hVf, mul_one] at key
  refine restrictFrameEquiv_eq_of_mul j hφ hψ hVf hVg (fracSection 𝒮 hf hg hVg) ?_ _ _ key.symm
  have h : (j.appIso V).inv (fracSection 𝒮 hf hg hVg) =
      X.presheaf.map (homOfLE (j.image_mono hVg)).op
        ((j.appIso (ProjectiveSpectrum.basicOpen 𝒮 g)).inv (fracSection 𝒮 hf hg le_rfl)) := by
    rw [← map_fracSection 𝒮 hf hg le_rfl hVg]
    exact congrArg (fun φ => φ.hom (fracSection 𝒮 hf hg le_rfl))
      (j.appIso_inv_naturality (homOfLE hVg).op)
  have h2 := congrArg ((rationalFunctionsPresheaf X).map (homOfLE (j.image_mono hVg)).op) hK
  rw [map_mul] at h2
  change (toRationalFunctionsPresheaf X).app _ _ * _ = _
  rw [h, toRationalFunctionsPresheaf_app_map]
  exact h2

/-- The gluing datum of the comparison `𝒪(1) ≅ j^* 𝒪_X(D)`: the chartwise comparisons over the
standard opens `D₊(f_k)` of a family of degree-one elements covering `Proj 𝒮`. -/
def projLocalEquiv (j : AlgebraicGeometry.Proj 𝒮 ⟶ X) [IsOpenImmersion j] {ι : Type u}
    {f : ι → S} (hf : ∀ k, f k ∈ 𝒮 1) {ψ : ι → (RationalFunctions X)ˣ}
    (hψ : ∀ k, D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f k)) (ψ k))
    (hcov : (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) ≤ ⨆ k, ProjectiveSpectrum.basicOpen 𝒮 (f k))
    (hK : ∀ k l, algebraMap Γ(X, j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f l)) _
        ((j.appIso (ProjectiveSpectrum.basicOpen 𝒮 (f l))).inv
          (fracSection 𝒮 (hf k) (hf l) le_rfl)) *
        rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f l))
          (((ψ l)⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
      rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f l))
        (((ψ k)⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) :
    LocalEquiv (ofSheafOfModules (𝒪(1)[𝒮]) ⊤) (ofSheafOfModules (D.divisorialSheaf.restrict j) ⊤)
      ι where
  cover k := ProjectiveSpectrum.basicOpen 𝒮 (f k)
  cover_le _ := le_top
  le_iSup_cover := hcov
  equiv k _ hV := projChartEquiv j (hf k) (hψ k) hV
  equiv_map k _ _ hV hWV t := projChartEquiv_map j (hf k) (hψ k) hV hWV t
  equiv_agree k l _ hk hl t := projChartEquiv_agree j (hf k) (hf l) (hψ k) (hψ l) (hK k l) hk hl t

/-- **`j^* 𝒪_X(D) ≅ 𝒪(1)`.** Let `j : Proj 𝒮 ⟶ X` be an open immersion and `f_k` degree-one
elements whose standard opens cover `Proj 𝒮`. If `ψ_k` is a local equation of `D` on `j(D₊(f_k))`
and `ψ_k⁻¹ = (f_k / f_l) ψ_l⁻¹` on `j(D₊(f_l))`, then the restriction of `𝒪_X(D)` along `j` is
isomorphic to the twisting sheaf `𝒪(1)`. -/
theorem nonempty_restrict_divisorialSheaf_iso_twistingSheaf (j : AlgebraicGeometry.Proj 𝒮 ⟶ X)
    [IsOpenImmersion j] {ι : Type u} {f : ι → S} (hf : ∀ k, f k ∈ 𝒮 1)
    {ψ : ι → (RationalFunctions X)ˣ}
    (hψ : ∀ k, D.IsLocalEquation (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f k)) (ψ k))
    (hcov : (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) ≤ ⨆ k, ProjectiveSpectrum.basicOpen 𝒮 (f k))
    (hK : ∀ k l, algebraMap Γ(X, j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f l)) _
        ((j.appIso (ProjectiveSpectrum.basicOpen 𝒮 (f l))).inv
          (fracSection 𝒮 (hf k) (hf l) le_rfl)) *
        rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f l))
          (((ψ l)⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) =
      rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen 𝒮 (f l))
        (((ψ k)⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) :
    Nonempty (D.divisorialSheaf.restrict j ≅ ProjectiveSpectrum.Proj.twistingSheaf 𝒮 1) :=
  ⟨(projLocalEquiv j hf hψ hcov hK).gluedIso.symm⟩

end ProjGlue

end MMP.Mori.Divisor

namespace MMP.Fourfold.DivisorialSectionAlgebra

open MMP.Mori MMP.Mori.Divisor Stacks.RelativeProj MMP.ProjFraction

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {D : Divisor Y}
  (A : DivisorialSectionAlgebra (𝟙 Y) D)

/-- A nonzero section `a` of degree one over `W`, as a unit `φ` of `K(Y)`: `a = φ` in `𝒦_Y(W)`. -/
theorem exists_units_pieceToRationalFunctions_eq {W : Y.Opens}
    (a : A.situation.sectionPieces W 1) (ha0 : a ≠ 0) :
    ∃ φ : (RationalFunctions Y)ˣ,
      ∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
        A.pieceToRationalFunctions W 1 a i = (φ : RationalFunctions Y) i.1 := by
  have hηW : genericPoint Y ∈ W := by
    by_contra hη
    apply ha0
    have h1 : A.pieceToRationalFunctions W 1 a = 0 := funext fun Z => absurd
      (((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨_, Set.mem_univ _, Z.2⟩) hη
    rw [pieceToRationalFunctions_apply] at h1
    exact (A.sectionEquiv 1 (Int.natCast_nonneg 1) W).injective
      (Subtype.ext (h1.trans (by rw [map_zero]; rfl)))
  let Z0 : irreducibleComponents Y :=
    ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; exact Set.mem_singleton _⟩
  let i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W} :=
    ⟨Z0, ((isGenericPoint_componentGenericPoint Y Z0).mem_open_set_iff W.isOpen).mpr
      ((genericPoint_spec Y).mem_open_set_iff W.isOpen |>.mp hηW)⟩
  obtain ⟨φ, hφ⟩ := PrimeDivisor.exists_units_algebraMap_eq
    (mt (A.sectionRingToFunctionField_of_eq_zero_iff i 1 a).mp ha0)
  refine ⟨φ, fun i' => IsFractionRing.injective _ Y.functionField ?_⟩
  rw [hφ, sectionRingToFunctionField_of]
  exact algebraMap_rationalFunctionsPresheaf_apply_eq (W := W) _ _ i

/-- **`𝒪_Z(g⁻¹_* D)` is `𝒪(1)` on the charts**, granted the transition identity: on the chart
`Proj ⨁_n 𝒪_Y(nD)(W)` over an affine open `W` on which the algebra is generated in degree one,
if for nonzero sections `a, b` of degree one, read as units `φ_a, φ_b` of `K(Y)`, the section
`a / b` of the chart is `g^*φ_a / g^*φ_b` on `D₊(b)`, then the restriction of `𝒪_Z(g⁻¹_* D)` to the
chart is the twisting sheaf `𝒪(1)`. -/
theorem nonempty_restrict_divisorialSheaf_iso_twistingSheaf_of_transition [CompactSpace Y]
    [IsIntegral A.model] [IsLocallyNoetherian A.model] [IsNormal A.model] [CompactSpace A.model]
    [IsDominant A.toBase] {W : Y.Opens} (hW : IsAffineOpen W)
    (hgen : A.situation.IsLocallyDegreeOneGenerated W)
    (j : AlgebraicGeometry.Proj (A.situation.sectionRingGrading W) ⟶ A.model)
    [IsOpenImmersion j] (hj : j = A.situation.relativeProjChart ⟨W, hW⟩)
    (hK : ∀ (a b : A.situation.sectionPieces W 1) (φ ψ : (RationalFunctions Y)ˣ),
      a ≠ 0 → b ≠ 0 →
      (∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
        A.pieceToRationalFunctions W 1 a i = (φ : RationalFunctions Y) i.1) →
      (∀ i : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W},
        A.pieceToRationalFunctions W 1 b i = (ψ : RationalFunctions Y) i.1) →
      algebraMap Γ(A.model, j ''ᵁ ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b)) _
        ((j.appIso (ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))).inv
          (fracSection (A.situation.sectionRingGrading W) (d := 1)
            (show DirectSum.of _ 1 a ∈ A.situation.sectionRingGrading W 1 from ⟨a, rfl⟩)
            (show DirectSum.of _ 1 b ∈ A.situation.sectionRingGrading W 1 from ⟨b, rfl⟩) le_rfl)) *
        rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))
          (((pullbackRationalFunction A.toBase ψ⁻¹ fun Z =>
          map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z)⁻¹ :
            (RationalFunctions A.model)ˣ) : RationalFunctions A.model) =
      rationalFunctionsRestrict (j ''ᵁ ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 b))
          (((pullbackRationalFunction A.toBase φ⁻¹ fun Z =>
          map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z)⁻¹ :
            (RationalFunctions A.model)ˣ) : RationalFunctions A.model)) :
    Nonempty (Scheme.Modules.restrict
        (Divisor.divisorialSheaf (X := A.model) (inverseTransformDivisor A.toBase D))
        j ≅
      ProjectiveSpectrum.Proj.twistingSheaf (A.situation.sectionRingGrading W) 1) := by
  classical
  let ι := {a : A.situation.sectionPieces W 1 // a ≠ 0}
  let φ : ι → (RationalFunctions Y)ˣ := fun a =>
    (A.exists_units_pieceToRationalFunctions_eq a.1 a.2).choose
  have hφ := fun a : ι => (A.exists_units_pieceToRationalFunctions_eq a.1 a.2).choose_spec
  have hf : ∀ a : ι, DirectSum.of _ 1 a.1 ∈ A.situation.sectionRingGrading W 1 :=
    fun a => ⟨a.1, rfl⟩
  have hψ : ∀ a : ι, Divisor.IsLocalEquation (X := A.model) (inverseTransformDivisor A.toBase D)
      (j ''ᵁ ProjectiveSpectrum.basicOpen _ (DirectSum.of _ 1 a.1))
      (pullbackRationalFunction A.toBase (φ a)⁻¹ fun Z =>
        map_componentGenericPoint_notMem_supp_of_isDominant A.toBase _ Z) := by
    intro a
    have h := A.isLocalEquation_inverseTransformDivisor hW a.1 a.2 (φ a) fun E hE => hφ a _
    rw [Scheme.Hom.opensRange_comp, Proj.opensRange_awayι] at h
    subst hj
    exact h
  refine nonempty_restrict_divisorialSheaf_iso_twistingSheaf _ hf hψ ?_
    (fun a b => hK a.1 b.1 (φ a) (φ b) a.2 b.2 (hφ a) (hφ b))
  intro x _
  have hcov := Proj.iSup_basicOpen_eq_top' (A.situation.sectionRingGrading W)
    (Subtype.val : A.situation.sectionRingGrading W 1 → A.situation.sectionRing W)
    (fun s => ⟨1, s.2⟩) (by
      rw [Subtype.range_val]
      exact A.situation.adjoin_sectionRingGrading_one_eq_top W hW hgen)
  have hx : x ∈ (⨆ s : A.situation.sectionRingGrading W 1,
      Proj.basicOpen _ (s : A.situation.sectionRing W)) := by
    rw [hcov]
    trivial
  obtain ⟨s, hxa⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨a, ha⟩ := s.2
  rw [← ha] at hxa
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Proj.mem_basicOpen, map_zero] at hxa
    exact hxa (zero_mem _)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha0⟩, hxa⟩

end MMP.Fourfold.DivisorialSectionAlgebra
