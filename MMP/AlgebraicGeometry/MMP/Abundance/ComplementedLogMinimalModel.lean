module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedDltFourfoldBirational
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogMinimalModelComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
public import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Complemented log minimal models over a birational base are good

Let `f : X ⟶ Z` be a projective birational morphism of normal projective complex fourfolds, and
let `B`, `A` be effective `ℚ`-divisors on `X` with `A` `ℚ`-Cartier, `(X, B + A)` log canonical and
`K_X + B + A ∼_ℚ f^*H` for a `ℚ`-Cartier `ℚ`-divisor `H` on `Z`. Then every log minimal model
`(M/Z, B_M)` of `(X/Z, B)` with `M` projective is good: `K_M + B_M` is semiample over `Z`.

## Main results

* `MMP.Fourfold.IsLogMinimalModel.isGoodLogMinimalModel_of_add_qLinearlyEquivalent_pullback`.

## Implementation notes

The conclusion is stated as `MMP.Fourfold.IsGoodLogMinimalModel`, which is the log minimal model
together with the relative semiampleness of `K_M + B_M` over `π_M : M ⟶ Z`. The pull-back `f^*H`
is `MMP.Mori.QDivisor.pullback` along `f`; it needs the image of the generic point of `X` to lie
outside `Supp H`, which holds for every `H` because `f` is birational, so the hypothesis `hfH`
only makes the pull-back defined.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_thm_fourfold_projective_birational_complemented_log_models_good

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

/-- The birational transform of divisors commutes with regarding a `ℚ`-divisor as an
`ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : QDivisor X) :
    RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{0}} (Q : MMP.Mori.PrimeDivisor Z) (r : ℚ),
      QDivisor.toRDivisor (Finsupp.single Q r) = Finsupp.single Q (r : ℝ) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero (Rat.castHom ℝ).toAddMonoidHom)
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, RationalMap.transformDivisor_single, RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor φ P with
    | none => exact (map_zero _).symm
    | some E => exact (hs E r).symm

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-Cartier pull-back. -/
private theorem isRCartierPullback_pullback {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {D : QDivisor X} (hDq : D.IsQCartier) (hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp) :
    MMP.Flips.IsRCartierPullback f (QDivisor.toRDivisor D)
      (QDivisor.toRDivisor (D.pullback hDq hB)) := by
  have hG := QDivisor.isPullback_pullback hDq hB
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  obtain ⟨D₀', hD₀', hp⟩ := hG _ hm D₀ hD₀ hD₀c
  have hmR : ((D.cartierIndex hDq : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => ((D.cartierIndex hDq : ℕ) : ℝ)⁻¹, fun _ => D₀, fun _ => D₀',
    fun _ => hD₀c, ?_, fun _ => ⟨_, hp⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    ext P
    have := congrArg (fun T : QDivisor X => T.coeff P) hD₀
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((D₀.coeff P : ℤ) : ℝ) = (((D₀.coeff P : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast
    field_simp
  · rw [Fin.sum_univ_one]
    ext P
    have := congrArg (fun T : QDivisor Y => T.coeff P) hD₀'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((D₀'.coeff P : ℤ) : ℝ) = (((D₀'.coeff P : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast
    field_simp

/-- A `ℚ`-linear equivalence `m (D₁ - D₂) = div φ`, read as an identity of `ℝ`-divisors. -/
private theorem smul_toRDivisor_eq_iff {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X]
    (D₁ D₂ : QDivisor X) (m : ℕ) (φ : (RationalFunctions X)ˣ) :
    (m : ℤ) • (D₁ - D₂) = Divisor.toQDivisor (principalDivisor φ) ↔
      (m : ℝ) • QDivisor.toRDivisor D₁ =
        (m : ℝ) • QDivisor.toRDivisor D₂ + Divisor.toRDivisor (principalDivisor φ) := by
  constructor
  · intro h
    ext P
    have := congrArg (fun T : QDivisor X => T.coeff P) h
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast] at this
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, smul_eq_mul]
    have h' := congrArg (fun t : ℚ => (t : ℝ)) this
    push_cast at h'
    linarith
  · intro h
    ext P
    have := congrArg (fun T : RDivisor X => T.coeff P) h
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, smul_eq_mul] at this
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast]
    have h' : (((m : ℚ) * (D₁.coeff P - D₂.coeff P) : ℚ) : ℝ) =
        (((principalDivisor φ).coeff P : ℚ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'

/-- The adjoint `K + B` of a `ℚ`-divisor, read as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_toRDivisor {X : Scheme.{0}} (K : Divisor X) (B : QDivisor X) :
    MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [MMP.Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- `K + B ∼_ℚ D` is the identity `m (K + B) = m D + div u` of `ℝ`-divisors for some `m > 0`. -/
private theorem qLinearlyEquivalent_iff_smul_logCanonicalDivisor_eq {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (K : Divisor X) (B D : QDivisor X) :
    (Divisor.toQDivisor K + B).QLinearlyEquivalent D ↔
      ∃ m : ℕ, 0 < m ∧ ∃ u : (RationalFunctions X)ˣ,
        (m : ℝ) • MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
          (m : ℝ) • QDivisor.toRDivisor D + Divisor.toRDivisor (principalDivisor u) := by
  simp only [QDivisor.QLinearlyEquivalent, smul_toRDivisor_eq_iff, logCanonicalDivisor_toRDivisor]

/-- `ℚ`-linear equivalence is preserved by adding a common `ℚ`-divisor. -/
private theorem qLinearlyEquivalent_add_right {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D₁ D₂ : QDivisor X} (h : D₁.QLinearlyEquivalent D₂)
    (E : QDivisor X) : (D₁ + E).QLinearlyEquivalent (D₂ + E) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  exact ⟨m, hm, φ, by rwa [add_sub_add_right_eq_sub]⟩

/-- For a pair `(X, Δ)`, `K + Δ` is `ℚ`-Cartier for every canonical divisor `K` of `X`. -/
private theorem isQCartier_add_of_isPair {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X} (h : MMP.Mori.IsPair sX Δ)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    (Divisor.toQDivisor K + Δ).IsQCartier := by
  obtain ⟨hX, n₀, K₀, hK₀, hQ⟩ := h
  exact hQ.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK₀ hK)

/-- An open immersion of integral schemes induces an isomorphism of function fields. -/
private theorem functionFieldMap_bijective_of_isOpenImmersion {W Y : Scheme.{0}} [IsIntegral W]
    [IsIntegral Y] (f : W ⟶ Y) [IsOpenImmersion f] [IsDominant f] :
    Function.Bijective (functionFieldMap f) := by
  rw [functionFieldMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- A representative `g` of a rational map `φ` over `Z` (`q ∘ φ = π`) commutes with the
structure morphisms on its domain: `q ∘ g = π|_{dom g}`. -/
private theorem hom_comp_eq_of_isOver {W Y Z : Scheme.{0}} [IsReduced W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (π : W ⟶ Z) (q : Y ⟶ Z) {φ : W.RationalMap Y}
    (hover : MMP.Flips.RationalMap.IsOver π q φ) (g : W.PartialMap Y)
    (hg : g.toRationalMap = φ) : g.hom ≫ q = g.domain.ι ≫ π := by
  have heq : W.homOfLE (inf_le_left : g.domain ⊓ ⊤ ≤ g.domain) ≫ g.hom ≫ q =
      W.homOfLE inf_le_right ≫ W.topIso.hom ≫ π := by
    have := (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)).mp
      (Scheme.PartialMap.toRationalMap_eq_iff.mp
        ((Scheme.RationalMap.compHom_toRationalMap g q).trans ((congrArg _ hg).trans hover)))
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom] at this
    exact this
  have h := W.homOfLE (le_inf le_rfl le_top : g.domain ≤ g.domain ⊓ ⊤) ≫= heq
  rwa [Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_rfl, Category.id_comp, Scheme.topIso_hom,
    Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_ι_assoc] at h

/-- **The base of a birational map over a birational morphism is birational.** -/
private theorem isBirationalMorphism_of_isOver {W Y Z : Scheme.{0}} [IsIntegral W] [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (π : W ⟶ Z) (q : Y ⟶ Z) [IsProper q]
    (hπ : IsBirationalMorphism π) {φ : W.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hover : MMP.Flips.RationalMap.IsOver π q φ) :
    IsBirationalMorphism q := by
  have : IsDominant π := hπ.isDominant
  obtain ⟨e, he⟩ := hφ
  set h : e.source.toScheme ⟶ Y := e.iso.hom ≫ e.target.ι
  have hc : h ≫ q = e.source.ι ≫ π := hom_comp_eq_of_isOver π q hover e.toPartialMap he
  haveI : Nonempty e.source := ⟨⟨_, e.dense_source.nonempty.some_mem⟩⟩
  haveI : IsDominant h := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant e.source.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  haveI : IsDominant q := by
    constructor
    have : IsDominant (e.source.ι ≫ π) := inferInstance
    refine Dense.mono ?_ (IsDominant.denseRange (f := e.source.ι ≫ π))
    rintro _ ⟨x, rfl⟩
    exact ⟨h x, by rw [← Scheme.Hom.comp_apply, hc]⟩
  have hbh := functionFieldMap_bijective_of_isOpenImmersion h
  have hbO := functionFieldMap_bijective_of_isOpenImmersion e.source.ι
  have hbq : Function.Bijective (functionFieldMap q) := by
    refine ⟨(functionFieldMap q).injective, fun t => ?_⟩
    obtain ⟨s, hs⟩ := (hbO.comp hπ.functionFieldMap_bijective).surjective (functionFieldMap h t)
    refine ⟨s, hbh.injective ?_⟩
    rwa [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hc,
      ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hqη : q (genericPoint Y) = genericPoint Z := map_genericPoint_of_isDominant q
  have hbir : IsBirational q := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, ← hqη]
      exact Set.bijOn_singleton.mpr rfl
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      have : IsIso ((Z.presheaf.stalkCongr (Inseparable.of_eq hqη.symm)).hom ≫
          q.stalkMap (genericPoint Y)) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hbq
      exact IsIso.of_isIso_comp_left (Z.presheaf.stalkCongr (Inseparable.of_eq hqη.symm)).hom _
  have hbid : IsBirational (𝟙 Y) := by
    refine ⟨?_, fun x _ => inferInstance⟩
    simpa using Set.bijOn_id (genericPoints Y)
  simpa using isBirationalMorphism_comp_of_isBirational q (𝟙 Y) hbir hbid

/-- Two morphisms into `M` which agree after `q` agree, if their common composite lands in an
open `O` over which `q` is an isomorphism. -/
private theorem eq_of_comp_eq_of_isIso_morphismRestrict {T M V : Scheme.{0}} (q : M ⟶ V)
    (O : V.Opens) [IsIso (q ∣_ O)] {x₁ x₂ : T ⟶ M} (h : x₁ ≫ q = x₂ ≫ q)
    (hr : Set.range ⇑(x₁ ≫ q) ⊆ (O : Set V)) : x₁ = x₂ := by
  have h₁ : Set.range x₁ ⊆ Set.range (q ⁻¹ᵁ O).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hr ⟨t, rfl⟩
  have h₂ : Set.range x₂ ⊆ Set.range (q ⁻¹ᵁ O).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    have := hr ⟨t, rfl⟩
    rwa [h] at this
  let y₁ := IsOpenImmersion.lift (q ⁻¹ᵁ O).ι x₁ h₁
  let y₂ := IsOpenImmersion.lift (q ⁻¹ᵁ O).ι x₂ h₂
  have e₁ : y₁ ≫ (q ⁻¹ᵁ O).ι = x₁ := IsOpenImmersion.lift_fac _ _ _
  have e₂ : y₂ ≫ (q ⁻¹ᵁ O).ι = x₂ := IsOpenImmersion.lift_fac _ _ _
  have : y₁ ≫ (q ∣_ O) = y₂ ≫ (q ∣_ O) := by
    rw [← cancel_mono O.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, e₁, ← Category.assoc, e₂, h]
  rw [← e₁, ← e₂, (cancel_mono (q ∣_ O)).mp this]

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{0}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- The rational map of a morphism `f` sends the generic point by `f`. -/
private theorem fromFunctionField_toRationalMap_hom {X Y : Scheme.{0}} [IrreducibleSpace X]
    (f : X ⟶ Y) :
    (f.toRationalMap).fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ f := by
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ (by trivial)]
  exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap f _

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{0}}
    [IsIntegral X] [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
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

/-- **Compatibility on a common model over the base.** If `φ : X ⤏ M` lies over `Z`
(`π_M ∘ φ = f`), `g₁ : W ⟶ X`, `g₂ : W ⟶ M` satisfy `g₁ ≫ f = g₂ ≫ π_M`, `ψ` is inverse to `g₁`,
and `π_M` is an isomorphism over an open containing the generic point of `Z`, then
`g₂ ∘ ψ = φ`. -/
private theorem compHom_eq_of_isInverse {X W M Z : Scheme.{0}} [IsIntegral X] [IsIntegral W]
    [IsIntegral M] [IsIntegral Z] (f : X ⟶ Z) (g₁ : W ⟶ X) (g₂ : W ⟶ M) (πM : M ⟶ Z)
    [IsDominant g₁] [IsDominant g₂] [IsDominant πM]
    (O : Z.Opens) [IsIso (πM ∣_ O)] (hO : genericPoint Z ∈ O)
    (hcomm : g₁ ≫ f = g₂ ≫ πM) {φ : X.RationalMap M}
    (hφ : MMP.Flips.RationalMap.IsOver f πM φ) {ψ : X.RationalMap W}
    (hψ : MMP.Mori.RationalMap.IsInverse g₁.toRationalMap ψ)
    (hbij : Function.Bijective (functionFieldMap g₁)) :
    ψ.compHom g₂ = φ := by
  obtain ⟨e, he1, he2⟩ := hψ
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [MMP.Flips.RationalMap.fromFunctionField_compHom]
  haveI : IsIso (CommRingCat.ofHom (functionFieldMap g₁)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap g₁))), ← Category.assoc,
    ← he2, specMap_functionFieldMap_fromFunctionField_symm g₁ e he1]
  refine eq_of_comp_eq_of_isIso_morphismRestrict πM O ?_ ?_
  · rw [Category.assoc, Category.assoc, ← MMP.Flips.RationalMap.fromFunctionField_compHom, hφ,
      fromFunctionField_toRationalMap_hom, ← hcomm, ← Category.assoc (Spec.map _),
      functionFieldMap_fromSpecStalk g₁, Category.assoc]
  · rintro _ ⟨t, rfl⟩
    have ht : W.fromSpecStalk (genericPoint W) t = genericPoint W := by
      have : t = IsLocalRing.closedPoint (W.presheaf.stalk (genericPoint W)) :=
        Subsingleton.elim _ _
      rw [this, Scheme.fromSpecStalk_closedPoint]
    change πM (g₂ (W.fromSpecStalk (genericPoint W) t)) ∈ O
    rw [ht, map_genericPoint_of_isDominant g₂, map_genericPoint_of_isDominant πM]
    exact hO

/-- The generic point of the normal target of a proper birational morphism of varieties lies in
the biregular locus. -/
private theorem genericPoint_mem_biregularLocus {M V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (q : M ⟶ V) (hV : MMP.Mori.IsVariety ℂ sV)
    (hM : MMP.Mori.IsVariety ℂ (q ≫ sV)) [IsIntegral V] [IsNormal V] [IsProper q]
    (hq : IsBirationalMorphism q) : genericPoint V ∈ biregularLocus q := by
  by_contra hη
  have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
    (MMP.Mori.two_le_closedsCodimension_compl_biregularLocus sV q (hY := hV) (hX := hM) hq) (genericPoint V) hη
  rw [Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec V).specializes trivial] at h2
  exact absurd h2 (by decide)

/-- **The structure morphism of a log minimal model over a birational base is birational.** The
birational map `φ : X ⤏ M` lies over `Z`, and `f : X ⟶ Z` is birational. -/
private theorem isBirationalMorphism_of_isLogMinimalModel {X Z M : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sM : M ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z}
    (hfb : IsBirationalMorphism f) {πM : M ⟶ Z} {KM : Divisor M} {B : QDivisor X}
    {BM : QDivisor M} {φ : X.RationalMap M} (hM : IsLogMinimalModel sX sZ sM f πM B KM BM φ) :
    IsBirationalMorphism πM := by
  have hZv := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsSeparated sZ := hZv.toIsSeparated
  haveI : IsProper πM := isProper_of_isProjectiveMorphism πM hM.isProjectiveMorphism_model
  have : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = sZ ≫ Limits.terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  exact isBirationalMorphism_of_isOver f πM hfb hM.isBirational hM.isOver

/-- **A common resolution comparing the adjoints.** For a projective log minimal model
`(M/Z, B_M)` of `(X/Z, B)` over a projective birational `f : X ⟶ Z`, there are a smooth
projective variety `W` with projective birational `p : W ⟶ X`, `q : W ⟶ M` over `Z` and a
canonical divisor `K'` of `X` such that `p^*(K' + B) - q^*(K_M + B_M)` is effective and
exceptional over `M`. -/
private theorem exists_isLogComparisonResolution {X Z M : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM] [QuasiCompact sM]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {f : X ⟶ Z} (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {πM : M ⟶ Z} {KM : Divisor M} (hKM : KM.IsCanonicalDivisor sM 4) {B : QDivisor X}
    {BM : QDivisor M} {φ : X.RationalMap M} (hM : IsLogMinimalModel sX sZ sM f πM B KM BM φ)
    (hMp : MMP.Mori.IsProjectiveVariety ℂ sM) (hπb : IsBirationalMorphism πM)
    (hdimM : topologicalKrullDim M = 4) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (_ : CompactSpace W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ X) (q : W ⟶ M)
      (ψ : X.RationalMap W) (K' : Divisor X) (GX GM : RDivisor W),
      K'.IsCanonicalDivisor sX 4 ∧ p ≫ f = q ≫ πM ∧
      IsLogComparisonResolution sX sM sW φ K' (QDivisor.toRDivisor B) KM
        (QDivisor.toRDivisor BM) p q ψ GX GM := by
  classical
  /- The varieties and morphisms. -/
  have hZv := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  have hMv := ((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hMp).1
  haveI : IsIntegral Z := hZv.toIsIntegral
  have hXn : IsNormalVariety ℂ sX := hM.isNormalVariety
  have hMn : IsNormalVariety ℂ sM := ⟨hMv, inferInstance⟩
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hfp
  haveI : IsProper πM := isProper_of_isProjectiveMorphism πM hM.isProjectiveMorphism_model
  haveI := hfb.isDominant
  haveI := hπb.isDominant
  /- A smooth projective common model `W` of `X` and `M` over `Z`. -/
  have hXZn : IsNormalVariety ℂ (f ≫ sZ) := hf ▸ hXn
  have hMZn : IsNormalVariety ℂ (πM ≫ sZ) := hM.comp_eq_model ▸ hMn
  let Xf : Bool → Scheme.{0} := fun i => Bool.rec M X i
  let ff : ∀ i, Xf i ⟶ Z := fun i => Bool.rec (motive := fun i => Xf i ⟶ Z) πM f i
  obtain ⟨W, w, hWn, -, g, hWs, hwp, hg, -, -⟩ :=
    @MMP.Resolution.exists_isSmoothScheme_isProjectiveMorphism_forall_valuation_eq ℂ _ _ Z
      sZ _ _ Bool _ Xf ff (fun i => by cases i <;> assumption)
      (fun i => by cases i; exacts [hπb, hfb])
      (fun i => by cases i; exacts [hMZn, hXZn])
      Empty _ Empty.elim (fun j => j.elim)
  obtain ⟨hg₁, hg₁p, hg₁b⟩ := hg true
  obtain ⟨hg₂, hg₂p, hg₂b⟩ := hg false
  set p : W ⟶ X := g true
  set q : W ⟶ M := g false
  change p ≫ f = w at hg₁
  change q ≫ πM = w at hg₂
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI : LocallyOfFiniteType (w ≫ sZ) := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (w ≫ sZ)
  haveI : IsProper w := isProper_of_isProjectiveMorphism w hwp
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace w
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hg₁p
  haveI : IsProper q := isProper_of_isProjectiveMorphism _ hg₂p
  haveI := hg₁b.isDominant
  haveI := hg₂b.isDominant
  have hpq : p ≫ f = q ≫ πM := hg₁.trans hg₂.symm
  have hpX : p ≫ sX = w ≫ sZ := by rw [← hf, ← Category.assoc, hg₁]
  have hqM : q ≫ sM = w ≫ sZ := by rw [← hM.comp_eq_model, ← Category.assoc, hg₂]
  /- The inverse of `p` and the compatibility `q ∘ p⁻¹ = φ`. -/
  obtain ⟨ψ, hψ⟩ := RationalMap.IsBirational.exists_isInverse hg₁b
  haveI : IsIso (πM ∣_ biregularLocus πM) := isBiregular_biregularLocus πM
  have hφ' : ψ.compHom q = φ := compHom_eq_of_isInverse f p q πM (biregularLocus πM)
    (genericPoint_mem_biregularLocus sZ πM hZv hMZn.1 hπb) hpq hM.isOver hψ
    hg₁b.functionFieldMap_bijective
  /- Canonical divisors compatible through a canonical divisor `K_W` of `W`. -/
  have hWpn : IsNormalVariety ℂ (p ≫ sX) := hpX ▸ hWn
  have hWqn : IsNormalVariety ℂ (q ≫ sM) := hqM ▸ hWn
  haveI : MMP.Mori.IsVariety ℂ (q ≫ sM) := hWqn.1
  haveI : LocallyOfFiniteType (p ≫ sX) := hWpn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sM) := hWqn.1.toLocallyOfFiniteType
  have hdimW : topologicalKrullDim W = 4 := hdimM ▸
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sM (q ≫ sM) hg₂b).symm
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme
    (q ≫ sM) (by rw [hqM]; exact hWs) (n := 4) (by exact_mod_cast hdimW)
  obtain ⟨KW, hKWc, hKWM⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hMn hWqn hg₂b hKM hK₀
  set K' : Divisor X := RationalMap.transformDivisor (X := W) p.toRationalMap KW
  have hK' : K'.IsCanonicalDivisor sX 4 :=
    MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hXn hWpn hg₁b hK
      (by rw [hpX, ← hqM]; exact hKWc)
  /- The pull-backs of the adjoints and their comparison on `W`. -/
  have hDq := isQCartier_add_of_isPair hM.isLogCanonicalPair.1 hK'
  have hNq := isQCartier_add_of_isPair hM.isDltPair.1.1 hKM
  have hGX := isRCartierPullback_pullback hDq
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p _)
  have hGM := isRCartierPullback_pullback hNq
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' q _)
  rw [← logCanonicalDivisor_toRDivisor] at hGX hGM
  have hKW : ∃ (n : ℕ) (KW : Divisor W), KW.IsCanonicalDivisor (w ≫ sZ) n ∧
      MMP.Mori.RationalMap.transformDivisor p.toRationalMap KW = K' ∧
      MMP.Mori.RationalMap.transformDivisor q.toRationalMap KW = KM :=
    ⟨4, KW, by rw [← hqM]; exact hKWc, rfl, hKWM⟩
  obtain ⟨hnn, hexc⟩ := IsLogMinimalModel.nonneg_sub_and_isExceptionalPrimeDivisor hX hZ hM
    (sW := w ≫ sZ) hWn.1 hWs hpX hqM hg₁p hg₂p hg₁b hg₂b hψ hφ' hKW hGX hGM
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, w ≫ sZ, p, q, ψ, K', _, _,
    hK', hpq, hWn.1, hWs, hpX, hqM, hg₁p, hg₂p, hg₁b, hg₂b, hψ, hφ', hKW, hGX, hGM, hnn, hexc⟩

private theorem solution : ∀ {X Z M : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM] [QuasiCompact sM]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 4)
    {f : X ⟶ Z} (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f)
    (hfb : IsBirationalMorphism f)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B A : QDivisor X} (hB0 : 0 ≤ B) (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {H : QDivisor Z} (hHq : H.IsQCartier)
    (hfH : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ H.supp)
    (hlin : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent (H.pullback hHq hfH))
    {πM : M ⟶ Z} {KM : Divisor M} {BM : QDivisor M} {φ : X.RationalMap M}
    (hM : IsLogMinimalModel sX sZ sM f πM B KM BM φ)
    (hMp : MMP.Mori.IsProjectiveVariety ℂ sM),
    IsGoodLogMinimalModel sX sZ sM f πM B KM BM φ := by
  intro X Z M _ _ _ _ _ _ _ _ _ _ _ sX _ sZ sM _ _ hX hdim hZ hZn hdimZ f hf hfp hfb K hK B A
    hB0 hA0 hAq hlc H hHq hfH hlin πM KM BM φ hM hMp
  refine ⟨hM, ?_⟩
  haveI := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  have hπb := isBirationalMorphism_of_isLogMinimalModel hZ hfb hM
  haveI := hπb.isDominant
  have : MMP.Mori.IsVariety ℂ (πM ≫ sZ) :=
    hM.comp_eq_model ▸ ((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hMp).1
  have hdimM : topologicalKrullDim M = 4 := hdimZ ▸
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (πM ≫ sZ) hπb).symm
  obtain ⟨n, hKM⟩ := hM.isCanonicalDivisor
  obtain rfl : n = 4 := by exact_mod_cast hKM.topologicalKrullDim_eq.symm.trans hdimM
  /- The comparison on a common resolution, with a canonical divisor `K'` of `X`. -/
  obtain ⟨W, _, _, _, _, sW, p, q, ψ, K', GX, GM, hK', hpq, hR⟩ :=
    exists_isLogComparisonResolution hX hZ hf hfp hfb hK hKM hM hMp hπb hdimM
  haveI := hR.isBirationalMorphism_left.isDominant
  /- The complement identity on `X` for `K'`, transported to `M`. -/
  rw [add_assoc] at hlin
  obtain ⟨m, hm, u, hu⟩ := (qLinearlyEquivalent_iff_smul_logCanonicalDivisor_eq _ _ _).mp
    ((qLinearlyEquivalent_add_right (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor
      sX hM.isNormalVariety hK' hK).qLinearlyEquivalent _).trans hlin)
  have hAp := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p A
  obtain ⟨⟨hAM0, hAMq⟩, ⟨HM, uM, hHM, -, hlinM⟩, -, -, hlcM, -⟩ :=
    hR.transport_lcComplement hZ hfp hM.isProjectiveMorphism_model hf hM.comp_eq_model
      hM.isLogCanonicalPair hM.isDltPair.1 hpq hA0 hAq hlc hHq
      (isRCartierPullback_pullback hHq hfH) hm hu (isRCartierPullback_pullback hAq hAp)
      (transformDivisor_toRDivisor _ _)
  /- The nef complemented dlt theorem on `M`. -/
  have hgH := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' πM H
  rw [MMP.Flips.IsRCartierPullback.eq πM hHM (isRCartierPullback_pullback hHq hgH)] at hlinM
  refine IsDltPair.isRelativelySemiample_of_add_qLinearlyEquivalent_pullback hMp hdimM
    hM.isQFactorial hKM hM.isDltPair hZ hZn hM.comp_eq_model hM.isProjectiveMorphism_model hπb
    hM.isRelativelyNef hAM0 hAMq hlcM hHq hgH ?_
  rw [add_assoc]
  exact (qLinearlyEquivalent_iff_smul_logCanonicalDivisor_eq _ _ _).mpr ⟨m, hm, uM, hlinM⟩

end Proof_thm_fourfold_projective_birational_complemented_log_models_good

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Complemented log minimal models over a birational base are good.** Let `f : X ⟶ Z` be a
projective birational morphism over `ℂ` of normal projective fourfolds
(`MMP.Mori.IsProjectiveVariety`, `MMP.Mori.IsBirationalMorphism`), `K` a canonical divisor of `X`,
and `B`, `A` effective `ℚ`-divisors on `X` with `A` `ℚ`-Cartier, `(X, B + A)` log canonical
(`MMP.Intersection.IsLogCanonicalPair`) and `K + B + A ∼_ℚ f^*H`
(`MMP.Mori.QDivisor.QLinearlyEquivalent`, `MMP.Mori.QDivisor.pullback`) for a `ℚ`-Cartier
`ℚ`-divisor `H` on `Z`. Then every log minimal model `(M/Z, B_M)` of `(X/Z, B)`
(`MMP.Fourfold.IsLogMinimalModel`) with `M` projective is good
(`MMP.Fourfold.IsGoodLogMinimalModel`): `K_M + B_M` is semiample over `Z`. -/
@[mmp "thm_fourfold_projective_birational_complemented_log_models_good"]
public theorem IsLogMinimalModel.isGoodLogMinimalModel_of_add_qLinearlyEquivalent_pullback
    {X Z M : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sZ : Z ⟶ Spec (.of ℂ)}
    {sM : M ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sM] [QuasiCompact sM]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    (hdimZ : topologicalKrullDim Z = 4)
    {f : X ⟶ Z} (hf : f ≫ sZ = sX) (hfp : IsProjectiveMorphism f)
    (hfb : IsBirationalMorphism f)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B A : QDivisor X} (hB0 : 0 ≤ B) (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sX (B + A))
    {H : QDivisor Z} (hHq : H.IsQCartier)
    (hfH : ∀ T : irreducibleComponents X, f (componentGenericPoint X T) ∉ H.supp)
    (hlin : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent (H.pullback hHq hfH))
    {πM : M ⟶ Z} {KM : Divisor M} {BM : QDivisor M} {φ : X.RationalMap M}
    (hM : IsLogMinimalModel sX sZ sM f πM B KM BM φ)
    (hMp : MMP.Mori.IsProjectiveVariety ℂ sM) :
    IsGoodLogMinimalModel sX sZ sM f πM B KM BM φ :=
      by revert X Z M sX sZ sM hX hdim hZ hZn hdimZ f hf hfp hfb K hK B A hB0 hA0 hAq hlc H hHq hfH hlin πM KM BM φ hM hMp; first | exact Proof_thm_fourfold_projective_birational_complemented_log_models_good.solution | exact Proof_thm_fourfold_projective_birational_complemented_log_models_good.solution _ | exact Proof_thm_fourfold_projective_birational_complemented_log_models_good.solution _ _ | exact Proof_thm_fourfold_projective_birational_complemented_log_models_good.solution _ _ _ | exact Proof_thm_fourfold_projective_birational_complemented_log_models_good.solution _ _ _ _

end MMP.Fourfold

