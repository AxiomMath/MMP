module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.RationalProgram
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Divisor.AmpleSectionDivisor
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion

/-!
# Klt compactifications from the rational program

Let `d ≥ 2` and assume `Q(d)`. A projective morphism `S ⟶ T` from a `ℚ`-factorial normal complex
variety of dimension `d` to a normal affine complex variety, with a klt boundary `C` on `S`,
extends to a projective morphism `(S̄, C̄) ⟶ T̄` of a `ℚ`-factorial klt pair onto a normal
projective compactification of `T`, with `S̄ ×_{T̄} T = S` and `C̄|_S = C`.

The base `T` is compactified by normalizing `ℙⁿ` in `T`, and `S` by normalizing `ℙᴺ_{T̄}` in `S`;
the result `S₀` contains `S` as the open subscheme over `T`. Over a log resolution `π : W ⟶ S₀`
of the closure of `C`, the boundary `C_W` is the strict transform of `C` plus, along every
exceptional prime divisor `E` with centre in `S`, a rational coefficient `c_E < 1` exceeding
`1 - a(E, S, C)`. The program of `Q(d)` for `(W, C_W)` over `S₀` gives `q : Y ⟶ S₀`. Over `S`,
with `K_S = div(ω)` for the form `ω` of `K_Y`, the divisor `q^*(K_S + C) - (K_Y + C_Y)` vanishes
along the non-exceptional prime divisors and has negative coefficient `1 - a(E, S, C) - c_E`
along every exceptional one, while its negative is nef over `S`; the negativity lemma shows that
there is no exceptional prime divisor. A projective birational morphism onto a `ℚ`-factorial
variety without exceptional divisors is an isomorphism, so `Y ×_{S₀} S = S`.

## Main results

* `MMP.Fourfold.exists_kltCompactification_of_rationalBirationalProgramProperty`: the klt
  compactification.
* `MMP.Fourfold.hom_comp_eq_of_isOver`: a representative of a rational map over a base commutes
  with the structure morphisms on its domain.
* `MMP.Fourfold.map_genericPoint_eq_and_divisorialValuation_eq`: if a birational map over a base
  sends `P` to `Q`, then `η_P` and `η_Q` have the same image in the base, and the divisorial
  valuations of `P` and `Q` agree on its function field.
* `MMP.Fourfold.transformDivisor_apply_eq`: over a base birational to the source, the coefficient
  of `φ_* P` in `φ_* D` is that of `P` in `D`.
* `MMP.Fourfold.isBirationalMorphism_of_isOver`: a proper morphism under a birational map over a
  birational morphism is birational.
* `MMP.Fourfold.isRelativelyNef_of_isRCartierPullback_of_isOpenImmersion`: relative nefness
  restricts along open immersions; in particular nef over `T̄` restricts to nef over an open
  `T ⊆ T̄`.
* `MMP.Fourfold.exists_genericPoint_eq_of_not_isExceptionalPrimeDivisor`: a prime divisor not
  exceptional for a proper birational morphism of normal varieties maps onto a prime divisor.
* `MMP.Fourfold.two_le_coheight_of_isExceptional`: an exceptional prime divisor has centre of
  codimension at least two.

## Implementation notes

* The compactification of the base is that of [Stacks, Tag 0B3H] followed by normalization; the
  normalization of `ℙᴺ_{T̄}` in `S` restricts over `ℙᴺ_T` to `S`, since normalization commutes
  with open base change and `S ⟶ ℙᴺ_T` is a closed immersion.
* The coefficient `c_E` is chosen separately for every exceptional prime divisor `E` of `W` with
  centre in `S`, rather than as `1 - ε` for one `ε`: this needs no finiteness of the set of
  exceptional divisors, only that the log discrepancy of a divisor over `S` depends on its
  valuation alone.
* That the morphism `Y ×_{S₀} S ⟶ S` without exceptional divisors is an isomorphism is read off
  from Kollár–Mori 2.62: the anti-ample exceptional divisor it provides is zero, so the structure
  sheaf is relatively ample, the morphism is finite, and a finite birational morphism onto a
  normal variety is an isomorphism.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.62, 3.39
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori

/-- The normalization of `P` in a normal integral scheme `X` along a quasi-compact immersion
`e : X ⟶ P`, where `P ⟶ B` is H-projective and `B` is H-projective over a field, is normal and
H-projective over `B` and over the field, and contains `X` as an open subscheme. -/
private theorem normalization_isProjectiveMorphism {k : Type} [Field k] {X P B : Scheme.{0}}
    (sB : B ⟶ Spec (.of k)) (hB : IsProjectiveMorphism sB) (g : P ⟶ B)
    (hg : IsProjectiveMorphism g) (e : X ⟶ P) [IsImmersion e] [QuasiCompact e]
    [IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] :
    IsOpenImmersion e.toNormalization ∧ IsNormal e.normalization ∧
      IsIntegral e.normalization ∧ IsProjectiveMorphism (e.fromNormalization ≫ g) ∧
      IsProjectiveMorphism (e.fromNormalization ≫ g ≫ sB) := by
  have : IsProper g := isProper_of_isProjectiveMorphism g hg
  have : IsProper sB := isProper_of_isProjectiveMorphism sB hB
  have hNagata : IsNagataScheme P := isNagataScheme_of_locallyOfFiniteType_over_field k (g ≫ sB)
  have hfin : IsFinite e.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType e hNagata
  have hcomp : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite :=
    fun V hV => by
      have : IsNoetherian V :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hV }
      exact finite_irreducibleComponents_of_isNoetherian
  have hproj : IsProjective (e.fromNormalization ≫ g ≫ sB) :=
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite e.fromNormalization).comp
      (hg.comp hB).isProjective
  have h2 : IsProjectiveMorphism (e.fromNormalization ≫ g ≫ sB) :=
    isProjectiveMorphism_of_isProjective _ (Stacks.Ample.unitModule (Spec (.of k)))
      (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of k))) hproj
  refine ⟨inferInstance, isNormal_normalization e hcomp, inferInstance,
    IsProjectiveMorphism.of_comp _ sB (by simpa using h2), h2⟩

/-- A normal affine complex variety has a normal projective compactification. -/
private theorem exists_normal_projective_compactification
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ)) (hT : IsNormalVariety ℂ sT) [IsAffine T] :
    ∃ (Tbar : Scheme.{0}) (sTbar : Tbar ⟶ Spec (.of ℂ)) (ι : T ⟶ Tbar),
      MMP.Mori.IsProjectiveVariety ℂ sTbar ∧ IsNormalVariety ℂ sTbar ∧
      IsOpenImmersion ι ∧ ι ≫ sTbar = sT := by
  obtain ⟨hTv, hTn⟩ := hT
  have : IsIntegral T := hTv.toIsIntegral
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  have hqp : IsQuasiProjective sT :=
    Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom sT inferInstance
  obtain ⟨n, i, hi, hiqc, hip⟩ := isHQuasiProjective_of_isQuasiProjective sT
    (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hqp
  have : IsImmersion i := hi
  have : QuasiCompact i := hiqc
  have hπ : IsProjectiveMorphism (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) :=
    ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨hopen, hnorm, hint, -, hproj⟩ := normalization_isProjectiveMorphism (k := ℂ)
    (𝟙 _) (isProjectiveMorphism_id _) _ hπ i
  have hs : i.toNormalization ≫ i.fromNormalization ≫
      (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) ≫ 𝟙 _ = sT := by
    rw [Category.comp_id, ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hip]
  have hv : AlgebraicGeometry.IsVariety ℂ (i.fromNormalization ≫
      (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) ≫ 𝟙 _) := by
    have := isProper_of_isProjectiveMorphism _ hproj
    exact { }
  exact ⟨i.normalization, _, i.toNormalization,
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hv, hproj⟩,
    ⟨hv, hnorm⟩, hopen, hs⟩

/-- Normalizing along a closed immersion followed by an open immersion `e = i ≫ u` changes
nothing over the open: the square `X ⟶ X̃`, `X ⟶ P'`, `X̃ ⟶ P`, `P' ⟶ P` is a pull-back. -/
private theorem isPullback_toNormalization {X P' P : Scheme.{0}} (i : X ⟶ P')
    [IsClosedImmersion i] (u : P' ⟶ P) [IsOpenImmersion u] [QuasiCompact (i ≫ u)]
    [QuasiSeparated (i ≫ u)] :
    IsPullback (i ≫ u).toNormalization i (i ≫ u).fromNormalization u := by
  set e := i ≫ u with he
  have hsnd : pullback.snd e u = pullback.fst e u ≫ i := by
    rw [← cancel_mono u, Category.assoc, ← he, pullback.condition]
  have : IsIntegralHom (pullback.snd e u) := by rw [hsnd]; infer_instance
  refine IsPullback.of_iso_pullback ⟨by rw [Scheme.Hom.toNormalization_fromNormalization]⟩
    (asIso (inv (pullback.fst e u) ≫ (pullback.snd e u).toNormalization ≫
      e.normalizationPullback u)) ?_ ?_
  · simp only [asIso_hom, Category.assoc]
    rw [IsIso.inv_comp_eq]
    exact Scheme.Hom.toNormalization_normalizationPullback_fst e u
  · simp only [asIso_hom, Category.assoc]
    rw [IsIso.inv_comp_eq, Scheme.Hom.normalizationPullback_snd,
      Scheme.Hom.toNormalization_fromNormalization, hsnd]

/-- A projective morphism `S ⟶ T` from a normal variety extends over an open immersion
`T ⟶ T̄` into a projective variety to a projective morphism `S₀ ⟶ T̄` of a normal variety, with
`S = S₀ ×_{T̄} T`. -/
private theorem exists_normal_projective_extension
    {T Tbar : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ)) (sTbar : Tbar ⟶ Spec (.of ℂ))
    (hTbar : MMP.Mori.IsProjectiveVariety ℂ sTbar) [IsAffine T] (ι : T ⟶ Tbar)
    [IsOpenImmersion ι] (hιs : ι ≫ sTbar = sT)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSv : IsNormalVariety ℂ sS)
    (f : S ⟶ T) (hfs : f ≫ sT = sS) (hf : IsProjectiveMorphism f) :
    ∃ (S₀ : Scheme.{0}) (_ : IsIntegral S₀) (_ : IsLocallyNoetherian S₀) (_ : IsNormal S₀)
      (sS₀ : S₀ ⟶ Spec (.of ℂ)) (f₀ : S₀ ⟶ Tbar) (j₀ : S ⟶ S₀) (_ : IsOpenImmersion j₀),
      MMP.Mori.IsProjectiveVariety ℂ sS₀ ∧ IsNormalVariety ℂ sS₀ ∧
      IsProjectiveMorphism f₀ ∧ f₀ ≫ sTbar = sS₀ ∧ IsPullback j₀ f f₀ ι := by
  obtain ⟨N, i, hi, hif⟩ := hf
  have := hi
  have hTbarv := hTbar.toIsVariety
  have := hTbarv.toIsIntegral
  set π := projectiveSpaceOver N Tbar ↘ Tbar with hπ
  set u := pullback.fst π ι with hu
  set i' : S ⟶ pullback π ι := i ≫ (projectiveSpaceOverBaseChangeIso N ι).inv with hi'
  have hi'f : i' ≫ pullback.snd π ι = f := by
    rw [hi', Category.assoc, ← projectiveSpaceOverBaseChangeIso_hom_over N ι, Iso.inv_hom_id_assoc,
      hif]
  have : QuasiCompact (ι ≫ sTbar) := by rw [hιs]; infer_instance
  have : QuasiCompact ι := QuasiCompact.of_comp ι sTbar
  have hS : (i' ≫ u) ≫ π ≫ sTbar = sS := by
    rw [Category.assoc, hu, pullback.condition_assoc, ← Category.assoc, hi'f, hιs, hfs]
  have : QuasiSeparated ((i' ≫ u) ≫ π ≫ sTbar) := by
    rw [hS]; have := hSv.1.toIsSeparated; infer_instance
  have : QuasiSeparated (i' ≫ u) := QuasiSeparated.of_comp _ (π ≫ sTbar)
  have hπp : IsProjectiveMorphism π := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  obtain ⟨hopen, hnorm, hint, hf₀, hs₀⟩ := normalization_isProjectiveMorphism (k := ℂ) sTbar
    hTbar.isProjective π hπp (i' ≫ u)
  have : IsProper ((i' ≫ u).fromNormalization ≫ π ≫ sTbar) :=
    isProper_of_isProjectiveMorphism _ hs₀
  have hv : AlgebraicGeometry.IsVariety ℂ ((i' ≫ u).fromNormalization ≫ π ≫ sTbar) := { }
  have : IsLocallyNoetherian (i' ≫ u).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian ((i' ≫ u).fromNormalization ≫ π ≫ sTbar)
  refine ⟨_, hint, inferInstance, hnorm, _, (i' ≫ u).fromNormalization ≫ π,
    (i' ≫ u).toNormalization, hopen, (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hv, hs₀⟩,
    ⟨hv, hnorm⟩, hf₀, Category.assoc _ _ _, ?_⟩
  have h := (isPullback_toNormalization i' u).paste_vert (IsPullback.of_hasPullback π ι)
  rwa [hi'f] at h

/-! ### Function fields and divisorial valuations -/

section Valuations

variable {X Y Z : Scheme.{0}}

/-- The extension of function fields of a composite of dominant morphisms. -/
private theorem functionFieldMap_comp_apply [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [IsDominant a] [IsDominant b] (t : Z.functionField) :
    functionFieldMap (a ≫ b) t = functionFieldMap a (functionFieldMap b t) := by
  suffices h : CommRingCat.ofHom (functionFieldMap (a ≫ b)) =
      CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) from
    congrArg (fun φ => CommRingCat.Hom.hom φ t) h
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  rw [functionFieldMap_fromSpecStalk (a ≫ b)]
  have h1 := functionFieldMap_fromSpecStalk a
  have h2 := functionFieldMap_fromSpecStalk b
  have hof : CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) =
      CommRingCat.ofHom (functionFieldMap b) ≫ CommRingCat.ofHom (functionFieldMap a) := rfl
  rw [hof, Spec.map_comp, Category.assoc, h2,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap a))), h1]
  exact (Category.assoc _ _ _).symm

/-- The extension of function fields along a commutative square. -/
private theorem functionFieldMap_apply_of_comp_eq [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    {X' : Scheme.{0}} [IsIntegral X'] (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X ⟶ X') (b' : X' ⟶ Z)
    [IsDominant a] [IsDominant b] [IsDominant a'] [IsDominant b'] (h : a ≫ b = a' ≫ b')
    (t : Z.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap a' (functionFieldMap b' t) := by
  rw [← functionFieldMap_comp_apply, ← functionFieldMap_comp_apply]
  congr 1
  simp only [h]

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The divisorial valuations of prime divisors `E ⊆ Y`, `P ⊆ X` with `f(η_E) = η_P` and
`𝒪_{X,P} ≅ 𝒪_{Y,E}` correspond under `f^*`. -/
private theorem divisorialValuation_functionFieldMap_of_isIso [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y) (P : MMP.Mori.PrimeDivisor X)
    (heq : f E.genericPoint = P.genericPoint) [IsIso (f.stalkMap E.genericPoint)]
    (g : X.functionField) :
    E.divisorialValuation (functionFieldMap f g) = P.divisorialValuation g := by
  by_cases hg : g = 0
  · simp [hg]
  have hg' : functionFieldMap f g ≠ 0 := (map_ne_zero (functionFieldMap f)).mpr hg
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq g]

end Valuations

/-! ### Prime divisors along a birational map over a base -/

section Birational

variable {W Y Z : Scheme.{0}}

/-- An open immersion of integral schemes induces an isomorphism of function fields. -/
private theorem functionFieldMap_bijective_of_isOpenImmersion [IsIntegral W] [IsIntegral Y]
    (f : W ⟶ Y) [IsOpenImmersion f] [IsDominant f] : Function.Bijective (functionFieldMap f) := by
  rw [functionFieldMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- An open immersion with nonempty source into an irreducible scheme is dominant. -/
private theorem isDominant_of_isOpenImmersion [IrreducibleSpace Y] (f : W ⟶ Y) [IsOpenImmersion f]
    [Nonempty W] : IsDominant f := by
  constructor
  obtain ⟨x⟩ := ‹Nonempty W›
  exact f.isOpenEmbedding.isOpen_range.dense ⟨_, ⟨x, rfl⟩⟩

/-- A representative of a birational map of integral schemes into a separated scheme is dominant
and induces an isomorphism of function fields. -/
private theorem isDominant_and_bijective_of_isBirational [IsIntegral W] [IsIntegral Y]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : W.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (g : W.PartialMap Y) (hg : g.toRationalMap = φ)
    [Nonempty g.domain] :
    ∃ _ : IsDominant g.hom, Function.Bijective (functionFieldMap g.hom) := by
  obtain ⟨e, he⟩ := hφ
  have heq := (Scheme.PartialMap.equiv_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp (hg.trans he.symm))
  simp only [Scheme.PartialMap.restrict_hom] at heq
  set O : W.Opens := g.domain ⊓ e.source with hO
  have hOne : (O : Set W).Nonempty :=
    (g.dense_domain.inter_open_nonempty _ e.source.isOpen
      e.dense_source.nonempty).mono fun y hy => ⟨hy.2, hy.1⟩
  haveI : Nonempty O := ⟨⟨hOne.some, hOne.some_mem⟩⟩
  set r := W.homOfLE (inf_le_left : O ≤ g.domain)
  set r' := W.homOfLE (inf_le_right : O ≤ e.source)
  have hr : r ≫ g.hom = r' ≫ e.iso.hom ≫ e.target.ι := heq
  have hoi : IsOpenImmersion (r ≫ g.hom) := by
    rw [hr]
    infer_instance
  haveI : IsDominant (r ≫ g.hom) := isDominant_of_isOpenImmersion _
  haveI : IsDominant r := isDominant_of_isOpenImmersion _
  haveI : IsDominant g.hom := ⟨(IsDominant.denseRange (f := r ≫ g.hom)).mono <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨r x, rfl⟩⟩
  refine ⟨inferInstance, ?_⟩
  have h1 := functionFieldMap_bijective_of_isOpenImmersion (r ≫ g.hom)
  have h2 := functionFieldMap_bijective_of_isOpenImmersion r
  have hc : ⇑(functionFieldMap (r ≫ g.hom)) = functionFieldMap r ∘ functionFieldMap g.hom :=
    funext fun t => functionFieldMap_comp_apply r g.hom t
  rw [hc] at h1
  exact ⟨h1.injective.of_comp, fun t => by
    obtain ⟨s, hs⟩ := h1.surjective (functionFieldMap r t)
    exact ⟨s, h2.injective hs⟩⟩

/-- A representative `g` of a rational map `φ` over `Z` (`q ∘ φ = π`) commutes with the
structure morphisms on its domain: `q ∘ g = π|_{dom g}`. -/
public theorem hom_comp_eq_of_isOver [IsReduced W] [IsSeparated (Z ↘ ⊤_ Scheme)] (π : W ⟶ Z)
    (q : Y ⟶ Z) {φ : W.RationalMap Y} (hover : MMP.Flips.RationalMap.IsOver π q φ)
    (g : W.PartialMap Y) (hg : g.toRationalMap = φ) : g.hom ≫ q = g.domain.ι ≫ π := by
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

/-- **Prime divisors along a birational map over a base.** Let `φ : W ⤏ Y` be a birational map
over `Z` (`q ∘ φ = π`) of normal integral schemes, with `Y`, `Z` separated, and `P ⊆ W`,
`Q ⊆ Y` prime divisors with `φ_* P = Q`. Then `π(η_P) = q(η_Q)`, and the divisorial valuations
of `P` and `Q` agree on `k(Z)`. -/
public theorem map_genericPoint_eq_and_divisorialValuation_eq [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    (π : W ⟶ Z) (q : Y ⟶ Z) [IsDominant π] [IsDominant q] {φ : W.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hover : MMP.Flips.RationalMap.IsOver π q φ)
    {P : MMP.Mori.PrimeDivisor W} {Q : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) :
    π P.genericPoint = q Q.genericPoint ∧
      ∀ t : Z.functionField, Q.divisorialValuation (functionFieldMap q t) =
        P.divisorialValuation (functionFieldMap π t) := by
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h
  obtain ⟨g, hP, hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hQ := MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g hg hP
  haveI : Nonempty g.domain := ⟨⟨_, hP⟩⟩
  obtain ⟨_, hbij⟩ := isDominant_and_bijective_of_isBirational hφ g hg
  have hc := hom_comp_eq_of_isOver π q hover g hg
  haveI : IsDominant g.domain.ι := isDominant_of_isOpenImmersion _
  obtain ⟨PO, hPO⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff g.domain.ι P).2 (by
    rw [Scheme.Opens.range_ι]; exact hP)
  have hηO : g.domain.ι PO.genericPoint = P.genericPoint := by
    have := OpenWeilRestriction.genericPoint_primeDivisorMap g.domain.ι PO
    rw [hPO] at this
    exact this.symm
  have hhη : g.hom PO.genericPoint = Q.genericPoint := by
    rw [hQ, show PO.genericPoint = ⟨P.genericPoint, hP⟩ from
      Subtype.ext ((Scheme.Opens.ι_apply _ _).symm.trans hηO)]
  refine ⟨?_, fun t => ?_⟩
  · rw [← hηO, ← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply, hhη]
  · have := Q.isDiscreteValuationRing_localRing
    haveI : ValuationRing (Y.presheaf.stalk (g.hom PO.genericPoint)) := by
      rw [hhη]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing g.hom hbij PO.genericPoint
    rw [← divisorialValuation_functionFieldMap_of_isIso g.hom PO Q hhη,
      functionFieldMap_apply_of_comp_eq g.hom q g.domain.ι π hc,
      divisorialValuation_functionFieldMap_of_isIso g.domain.ι PO P hηO]

/-- On a separated integral normal scheme, a prime divisor is determined by its divisorial
valuation: its local ring is the centre of the valuation ring. -/
private theorem eq_of_divisorialValuation_eq {k : Type} [Field k] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (sW : W ⟶ Spec (.of k)) [IsSeparated sW]
    {P P' : MMP.Mori.PrimeDivisor W} (h : P.divisorialValuation = P'.divisorialValuation) :
    P = P' := by
  have hmem : ∀ E : MMP.Mori.PrimeDivisor W, E.divisorialValuation = P.divisorialValuation →
      (∀ a : W.presheaf.stalk E.genericPoint,
        algebraMap _ W.functionField a ∈ P.divisorialValuation.valuationSubring) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk E.genericPoint),
        algebraMap _ W.functionField a ∈ P.divisorialValuation.valuationSubring.nonunits := by
    intro E hE
    rw [← hE]
    refine ⟨fun a => (Valuation.mem_valuationSubring_iff _ _).2
      ((E.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩), fun a ha => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    have key := Valuation.isEquiv_valuation_valuationSubring E.divisorialValuation 1
      (algebraMap _ W.functionField a)
    rw [map_one, map_one] at key
    exact not_le.mp (key.not.mp (not_le.mpr ((E.divisorialValuation_algebraMap_lt_one_iff a).2 ha)))
  obtain ⟨h1, h2⟩ := hmem P rfl
  obtain ⟨h1', h2'⟩ := hmem P' h.symm
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Flips.eq_of_isLocal_le_valuationSubring sW _ h1 h2 h1' h2')

/-- **Coefficients along a birational map over a base.** If `φ_* P = Q` for a birational map
`φ : W ⤏ Y` over `Z`, with `π : W ⟶ Z` inducing an isomorphism of function fields, then the
coefficient of `Q` in `φ_* D` is that of `P` in `D`. -/
public theorem transformDivisor_apply_eq {k : Type} [Field k] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsSeparated (Y ↘ ⊤_ Scheme)] [IsSeparated (Z ↘ ⊤_ Scheme)]
    (sW : W ⟶ Spec (.of k)) [IsSeparated sW]
    (π : W ⟶ Z) (q : Y ⟶ Z) [IsDominant π] [IsDominant q]
    (hπ : Function.Bijective (functionFieldMap π)) {φ : W.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hover : MMP.Flips.RationalMap.IsOver π q φ)
    {P : MMP.Mori.PrimeDivisor W} {Q : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R W) :
    MMP.Mori.RationalMap.transformDivisor φ D Q = D P := by
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h (fun E' hE' => ?_) D
  have h1 := (map_genericPoint_eq_and_divisorialValuation_eq π q hφ hover h).2
  have h2 := (map_genericPoint_eq_and_divisorialValuation_eq π q hφ hover hE').2
  refine eq_of_divisorialValuation_eq sW (Valuation.ext fun t => ?_)
  obtain ⟨s, rfl⟩ := hπ.surjective t
  rw [← h1, ← h2]

/-- **The base of a birational map over a birational morphism is birational.** If `φ : W ⤏ Y` is
birational, `q : Y ⟶ Z` is proper and `q ∘ φ = π` for a birational morphism `π`, then `q` is a
birational morphism. -/
public theorem isBirationalMorphism_of_isOver [IsIntegral W] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (π : W ⟶ Z) (q : Y ⟶ Z) [IsProper q]
    (hπ : IsBirationalMorphism π) {φ : W.RationalMap Y}
    (hφ : MMP.Mori.RationalMap.IsBirational φ) (hover : MMP.Flips.RationalMap.IsOver π q φ) :
    IsBirationalMorphism q := by
  have : IsDominant π := hπ.isDominant
  obtain ⟨e, he⟩ := hφ
  set h : e.source.toScheme ⟶ Y := e.iso.hom ≫ e.target.ι
  have hc : h ≫ q = e.source.ι ≫ π := hom_comp_eq_of_isOver π q hover e.toPartialMap he
  haveI : Nonempty e.source := ⟨⟨_, e.dense_source.nonempty.some_mem⟩⟩
  haveI : IsDominant h := isDominant_of_isOpenImmersion _
  haveI : IsDominant e.source.ι := isDominant_of_isOpenImmersion _
  haveI : IsDominant q := by
    refine ⟨(IsDominant.denseRange (f := e.source.ι ≫ π)).mono ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ⟨h x, by rw [← Scheme.Hom.comp_apply, hc]⟩
  have hbh := functionFieldMap_bijective_of_isOpenImmersion h
  have hbO := functionFieldMap_bijective_of_isOpenImmersion e.source.ι
  have hbq : Function.Bijective (functionFieldMap q) := by
    refine ⟨(functionFieldMap q).injective, fun t => ?_⟩
    obtain ⟨s, hs⟩ := (hbO.comp hπ.functionFieldMap_bijective).surjective (functionFieldMap h t)
    refine ⟨s, hbh.injective ?_⟩
    rwa [functionFieldMap_apply_of_comp_eq h q e.source.ι π hc]
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

end Birational

/-! ### Projective birational morphisms without exceptional divisors -/

section NoExceptional

/-- A quasi-affine scheme universally closed over an affine scheme is affine. -/
private theorem isAffine_of_isQuasiAffine_of_universallyClosed {X Y : Scheme.{0}} (g : X ⟶ Y)
    [X.IsQuasiAffine] [IsAffine Y] [UniversallyClosed g] : IsAffine X := by
  have hfac : X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv) = g := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have : UniversallyClosed (X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv)) := by
    rw [hfac]; infer_instance
  have : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated _ (Spec.map g.appTop ≫ Y.isoSpec.inv)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- A proper morphism is finite if every point of the target has an affine neighbourhood with
quasi-affine preimage. -/
private theorem isFinite_of_isProper_of_isQuasiAffine_preimage {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsProper f]
    (H : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ (f ⁻¹ᵁ U).toScheme.IsQuasiAffine) :
    IsFinite f := by
  have : IsAffineHom f := by
    refine isAffineHom_of_forall_exists_isAffineOpen f fun y => ?_
    obtain ⟨U, hy, hU, hq⟩ := H y
    refine ⟨U, hy, hU, ?_⟩
    have : IsAffine U.toScheme := hU
    exact isAffine_of_isQuasiAffine_of_universallyClosed (f ∣_ U)
  have : IsIntegralHom f :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr ⟨inferInstance, inferInstance⟩

/-- **A projective birational morphism onto a `ℚ`-factorial variety without exceptional prime
divisors is an isomorphism.** -/
private theorem isIso_of_forall_not_isExceptional {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (hX : IsQFactorial sX)
    (hY : IsNormalVariety k sY) (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f)
    (hE : ∀ E : MMP.Mori.PrimeDivisor Y,
      ¬ MMP.Mori.RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    IsIso f := by
  obtain ⟨F, e, he, -, hFE, D, hD, hDF, hamp⟩ :=
    exists_isRelativelyAmple_neg_smul_of_isExceptional sX sY hX hY f hfs hfp hfb
  have hF : F = 0 := Finsupp.ext fun E => by_contra fun h => hE E (hFE E h)
  have hD0 : -D = 0 := by
    rw [Divisor.toQDivisor_injective (by rw [hDF, hF, smul_zero, map_zero] :
      Divisor.toQDivisor D = Divisor.toQDivisor 0), neg_zero]
  have : IsIntegral X := hX.1.1.toIsIntegral
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsProper f := isProper_of_isProjectiveMorphism f hfp
  have : IsFinite f := by
    refine isFinite_of_isProper_of_isQuasiAffine_preimage f fun x => ?_
    have := hD.neg.isInvertibleModule_divisorialSheaf
    obtain ⟨V, hV, hxV, hVamp⟩ := hamp x
    refine ⟨V, hxV, hV, ?_⟩
    have hφ : (-D).IsLocalEquation (f ⁻¹ᵁ V) 1 := hD0 ▸ Divisor.isLocalEquation_zero _
    exact (Stacks.RelativeVeryAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule _ _
      (MMP.Threefold.Resolution.modulePullbackIsoRestrict' (f ⁻¹ᵁ V) (-D).divisorialSheaf ≪≫
        hφ.restrictDivisorialSheafIso)).mpr hVamp
  exact (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)).2 this

end NoExceptional

/-! ### Intersection numbers as degrees along curves -/

section Intersection

open MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_ι (k := k) C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- **`ℚ`-nefness is `ℝ`-nefness.** A `ℚ`-Cartier `ℚ`-divisor nef over `Y` is, as an `ℝ`-divisor,
`ℝ`-Cartier and nef over `Y`. -/
private theorem isRelativelyNef_toRDivisor {Y : Scheme.{u}} {f : X ⟶ Y} {D : QDivisor X}
    (h : QDivisor.IsRelativelyNef sX f D) :
    MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D) := by
  obtain ⟨hD, hh⟩ := h
  set N := D.cartierIndex hD
  have hNpos : (0 : ℚ) < N := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set L : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hLc : L.IsCartier := (D.cartierIndexSMul hD).2
  have hLD : ∀ P, (L.coeff P : ℚ) = N * D.coeff P := fun P => by
    have := congrArg (fun G : QDivisor X => G.coeff P) (QDivisor.toQDivisor_cartierIndexSMul D hD)
    simpa [zsmul_eq_mul] using this
  refine ⟨1, fun _ => ((1 / N : ℚ) : ℝ), fun _ => L, fun _ => hLc, ?_, fun C hC x hx => ?_⟩
  · ext P
    rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      QDivisor.coeff_toRDivisor, smul_eq_mul, ← Rat.cast_intCast, hLD P]
    push_cast
    field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast hNpos.ne']
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    have key := hh C hC
    rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
      Finsupp.sum_single_index (by simp)] at key
    simp only [smul_eq_mul, mul_one] at key
    rw [Fin.sum_univ_one, eq_degreeOn_of_isCartierIntersectionNumber k sX (hd 0)]
    exact (by exact_mod_cast key :
      (0 : ℝ) ≤ ((1 / N : ℚ) : ℝ) * (L.degreeOn k sX C.ι C.dim_le hLc : ℝ))

end Intersection

/-! ### Nefness along open immersions -/

section Nef

open MMP.Flips

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- **Relative nefness restricts along open immersions.** Let `q : W ⟶ Z` be an open immersion
and `p : W ⟶ Y` a morphism with `p ≫ πY = q ≫ πZ` for `πY : Y ⟶ S`, `πZ : Z ⟶ S`. If `M` is an
`ℝ`-Cartier divisor on `Z` nef over `S`, its pull-back `q^*M` is nef over `Y`. In particular
(`S = T̄`, `Y = T` an open of `T̄`, `W` the preimage of `T` in `Z`), a divisor nef over `T̄`
restricts to one nef over `T`. -/
public theorem isRelativelyNef_of_isRCartierPullback_of_isOpenImmersion {k : Type u} [Field k]
    {W Y Z S : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ]
    [LocallyOfFiniteType sZ] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ Y)
    (q : W ⟶ Z) [IsOpenImmersion q] [QuasiCompact (q ≫ sZ)] (hpq : p ≫ πY = q ≫ πZ)
    {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') : IsRelativelyNef k (q ≫ sZ) p M' := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨m, r, L₀, L₁, hL₀, hMeq, hpb, hM'eq⟩ := hM'
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  refine ⟨m, r, _, hL₁c, hM'eq, fun C hC x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) C r _ hL₁c
  rw [← hM'eq] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sZ) C).1 _ _ _ _ _ _ _ hx hx0]
  by_cases hc : IsProperCurve sZ (q C.point)
  · obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ProperCurve sZ, C₀.point = q C.point := ⟨⟨_, hc⟩, rfl⟩
    have hC₀c : C₀.IsContractedBy πZ := by
      intro z hz
      rw [hC₀] at hz ⊢
      have hcl : IsClosed (q '' closure ({C.point} : Set W)) := by
        have : IsProper ((C.ι ≫ q) ≫ sZ) := by rw [Category.assoc]; exact C.isProper_ι_comp
        have : IsProper (C.ι ≫ q) := IsProper.of_comp _ sZ
        have h := (C.ι ≫ q).isClosedMap.isClosed_range
        rwa [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          range_curveSubschemeAtι] at h
      have hsub : closure ({q C.point} : Set Z) ⊆ q '' closure ({C.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩) hcl
      obtain ⟨w, hw, rfl⟩ := hsub hz
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, hC w hw]
    have hdeg : ∀ j, ((((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) : ℤ) : ℝ) =
        (residueFieldDegree q C.point : ℝ) * (L₀ j).degreeOn k sZ C₀.ι C₀.dim_le (hL₀ j) := by
      intro j
      rw [degreeOn_pullback_eq_mul q (hL₀ j) (hB j) C C₀ hC₀]
      push_cast; rfl
    obtain ⟨mM, rM, LM, hLM, hMeq', hMall⟩ := hM
    have hMx := isRIntersectionNumber_sum_degreeOn k sZ C₀ rM LM hLM
    rw [← hMeq'] at hMx
    have h0 := isRIntersectionNumber_sum_degreeOn k sZ C₀ r L₀ hL₀
    rw [← hMeq] at h0
    have hnn := hMall C₀ hC₀c _ hMx
    rw [(IsRIntersectionNumber.eq_and_linear k sZ C₀).1 _ _ _ _ _ _ _ hMx h0] at hnn
    simp only [hdeg, mul_left_comm (r _), ← Finset.mul_sum]
    exact mul_nonneg (Nat.cast_nonneg _) hnn
  · have hdeg : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) = 0 := fun j => degreeOn_pullback_eq_zero q (hL₀ j) (hB j) C hc
    simp [hdeg]

end Nef

/-! ### Divisors, forms and exceptionality -/

section Helpers

open MMP.Flips

variable {X Y : Scheme.{u}}

/-- A `ℚ`-Cartier `ℚ`-divisor is, as an `ℝ`-divisor, `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor_of_isQCartier [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (hD : D.IsQCartier) :
    IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, D', hD', hc⟩ := hD
  refine ⟨1, fun _ => ((m : ℝ))⁻¹, fun _ => D', fun _ => hc, ?_⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  ext E
  have h := congrArg (fun G : QDivisor X => G.coeff E) hD'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, ← toRDivisor_eq_mapCoeffs,
    Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, smul_eq_mul]
  have h' : ((D'.coeff E : ℚ) : ℝ) = ((m * D.coeff E : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  rw [show ((D'.coeff E : ℤ) : ℝ) = (m : ℝ) * (D.coeff E : ℝ) from h', ← mul_assoc,
    inv_mul_cancel₀ hm', one_mul]

/-- A difference of `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub [IsLocallyNoetherian Y] [IsNormal Y]
    {D₁ D₂ : RDivisor Y} (h₁ : IsCartierCombination D₁)
    (h₂ : IsCartierCombination D₂) : IsCartierCombination (D₁ - D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ (-r₂), Fin.append L₁ L₂, fun j => ?_, ?_⟩
  · exact Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier)
      (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i) j
  · simp [Fin.sum_univ_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]

/-- Equal `ℝ`-Cartier divisors are numerically equivalent. -/
private theorem isNumericallyEquivalentOver_of_eq {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (f : X ⟶ Y)
    {N₁ N₂ : RDivisor X} (h : N₁ = N₂) (hN : IsCartierCombination N₁) :
    IsNumericallyEquivalentOver k sX f N₁ N₂ := by
  subst h
  exact ⟨hN, hN, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ h₁ h₂ =>
    (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩

/-- The order of a form does not depend on how the structure morphism is written. -/
private theorem ordForm_cast {k : Type u} [Field k] [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms s d m) (E : MMP.Mori.PrimeDivisor X) :
    E.ordForm (h ▸ τ : RationalPluriForms s' d m) = E.ordForm τ := by
  subst h; rfl

/-- **The pull-back of forms along a morphism inducing an isomorphism of function fields is
surjective.** -/
private theorem pullbackRationalPluriForms_surjective {k : Type u} [Field k] [PerfectField k]
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (m : ℤ) :
    Function.Surjective (pullbackRationalPluriForms sX f (d := d) (m := m)) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  intro τ'
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hf.surjective (b'.repr τ' ())
  refine ⟨c • b (), ?_⟩
  have hpb : pullbackRationalPluriForms sX f (c • b ()) = pullbackFormsAlong hω m (c • b ()) :=
    pullbackForms_eq hω m _
  rw [hpb]
  refine b'.repr.injective (Finsupp.ext fun u => ?_)
  obtain rfl : u = () := rfl
  rw [repr_pullbackFormsAlong]
  have hb : b.repr (b ()) () = 1 := by rw [Module.Basis.repr_self, Finsupp.single_eq_same]
  change algebraMap _ _ (b.repr (c • b ()) ()) = _
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, hb, smul_eq_mul, mul_one]
  exact hc

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero {k : Type u} [Field k] [IsIntegral X]
    [IsIntegral Y] (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsDominant f] {d : ℕ} {m : ℤ} :
    pullbackRationalPluriForms sX f (0 : RationalPluriForms sX d m) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  unfold pullbackRationalPluriForms
  have h := MMP.Fourfold.pullbackForms_smul (K' := Y.functionField) (d := d) (m := m)
    (0 : X.functionField) (0 : PluriForms k X.functionField d m)
  rwa [zero_smul, map_zero, zero_smul] at h

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- **A non-exceptional prime divisor maps onto a prime divisor.** For a proper birational
morphism `p : W ⟶ Y` of normal varieties and a prime divisor `P` of `W` not exceptional over `Y`,
`p(η_P)` is the generic point of a prime divisor of `Y`. -/
public theorem exists_genericPoint_eq_of_not_isExceptionalPrimeDivisor {k : Type u}
    [Field k] {W Y : Scheme.{u}} [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {p : W ⟶ Y}
    (hW : IsNormalVariety k (p ≫ sY)) [IsProper p] (hp : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) (hP : ¬ IsExceptionalPrimeDivisor sY p P) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, p P.genericPoint = Q.genericPoint := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : MMP.Mori.IsVariety k sY := hY.1
  haveI : MMP.Mori.IsVariety k (p ≫ sY) := hW.1
  have hdim : topologicalKrullDim W = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hp).symm
  have h1 : 1 ≤ Order.coheight (p P.genericPoint) := by
    have := coheight_le_coheight_map sY (p ≫ sY) hY.1 hW.1 p rfl hdim P.genericPoint
    rwa [P.coheight_genericPoint] at this
  have h2 : Order.coheight (p P.genericPoint) ≤ 1 := by
    by_contra! h2
    refine hP ⟨hW, hp, inferInstance, ?_⟩
    obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sY
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn]
    have hd := topologicalKrullDim_closure_singleton_add_coheight sY (p P.genericPoint)
    rw [hn] at hd
    exact (withBot_add_two_le_iff hd).mpr (Order.add_one_le_of_lt h2)
  have hco : Order.coheight (p P.genericPoint) = 1 := le_antisymm h2 h1
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- The image of the generic point of a prime divisor exceptional for a morphism has coheight at
least two. -/
public theorem two_le_coheight_of_isExceptional {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y}
    (E : MMP.Mori.PrimeDivisor X)
    (hE : MMP.Mori.RationalMap.IsExceptional (X := X) f.toRationalMap E) :
    2 ≤ Order.coheight (f E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight] at hE
  refine hE _ (subset_closure ⟨E.genericPoint, ?_, rfl⟩)
  change E.genericPoint ∈ E.support
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- **The pull-back of forms along a morphism inducing an isomorphism of function fields is
injective.** -/
private theorem pullbackRationalPluriForms_injective {k : Type u} [Field k] [PerfectField k]
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (m : ℤ) :
    Function.Injective (pullbackRationalPluriForms sX f (d := d) (m := m)) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have key : ∀ σ σ' : PluriForms k X.functionField d m,
      pullbackFormsAlong hω m σ = pullbackFormsAlong hω m σ' → σ = σ' := by
    intro σ σ' h1
    set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
    refine b.repr.injective (Finsupp.ext fun u => ?_)
    obtain rfl : u = () := rfl
    have h2 := congrArg (fun σ => (ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m).repr
      σ ()) h1
    simp only [repr_pullbackFormsAlong] at h2
    exact hf.injective h2
  intro τ τ' h
  refine key τ τ' ?_
  rw [← pullbackForms_eq hω m τ, ← pullbackForms_eq hω m τ']
  exact h

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsOpenImmersion f] [Nonempty X] : topologicalKrullDim X = topologicalKrullDim Y := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have hne : ((f.opensRange : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ⟨Nonempty.some inferInstance, rfl⟩⟩
  have h := (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k _ (_ ↘ Spec (.of k)) _
      (TopologicalSpace.Opens.isOpen _) hne).symm
  rw [(Scheme.homeoOfIso f.isoOpensRange).isHomeomorph.topologicalKrullDim_eq]
  exact h

/-- A scheme separated over an affine scheme is separated. -/
private theorem isSeparated_toTerminal {R : CommRingCat.{u}} (s : X ⟶ Spec R) [IsSeparated s] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec R ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

end Helpers

/-! ### Negativity over `S` -/

section Negativity

open MMP.Flips

/-- **No exceptional divisors over `S`.** Let `q_S : P ⟶ S` be a proper birational morphism onto a
`ℚ`-factorial variety with a klt boundary `C`, and `a : P ⟶ Y` an open immersion into a normal
variety `Y` over `S₀ ⊇ S` with `K_Y + C_Y` nef over `S₀`. If the coefficients of `C_Y` along the
non-exceptional prime divisors of `P` are those of `C`, and exceed `1 - a(E, S, C)` along the
exceptional ones, then `q_S` has no exceptional prime divisor. -/
private theorem not_isExceptional_of_isRelativelyNef {d : ℕ}
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSQ : IsQFactorial sS) (hSd : topologicalKrullDim S = d)
    (C : QDivisor S) (hC : IsKltPair sS C)
    {S₀ Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (hY : IsNormalVariety ℂ sY) (q : Y ⟶ S₀) (j₀ : S ⟶ S₀)
    (KY : Divisor Y) (hKY : ∃ m, KY.IsCanonicalDivisor sY m) (CY : QDivisor Y)
    (hnef : haveI := hY.1.toQuasiCompact
      QDivisor.IsRelativelyNef sY q (Divisor.toQDivisor KY + CY))
    {P : Scheme.{0}} [IsIntegral P] [IsLocallyNoetherian P] [IsNormal P] [CompactSpace P]
    (a : P ⟶ Y) [IsOpenImmersion a] (qS : P ⟶ S) [IsProper qS]
    (hqSb : IsBirationalMorphism qS) (hw : a ≫ q = qS ≫ j₀) (hPv : IsNormalVariety ℂ (qS ≫ sS))
    (hsq : qS ≫ sS = a ≫ sY)
    (hne : ∀ (E : MMP.Mori.PrimeDivisor P) (Γ : MMP.Mori.PrimeDivisor S),
      qS E.genericPoint = Γ.genericPoint →
        CY.coeff (OpenWeilRestriction.primeDivisorMap a E) = C.coeff Γ)
    (hexc : ∀ E : MMP.Mori.PrimeDivisor P, 2 ≤ Order.coheight (qS E.genericPoint) →
      ∀ (n : ℕ) (b : ℝ), MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor C)
        ⟨P, qS, hPv, hqSb, E⟩ b → 1 - b < CY.coeff (OpenWeilRestriction.primeDivisorMap a E)) :
    ∀ E : MMP.Mori.PrimeDivisor P,
      ¬ MMP.Mori.RationalMap.IsExceptional (X := P) qS.toRationalMap E := by
  intro E₀ hE₀
  have hSv := hSQ.1.1
  have hYv := hY.1
  have : LocallyOfFiniteType sS := hSv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : QuasiCompact sY := hYv.toQuasiCompact
  have : QuasiCompact sS := hSv.toQuasiCompact
  have : IsSeparated sS := hSv.toIsSeparated
  have : IsSeparated sY := hYv.toIsSeparated
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have := isSeparated_toTerminal sS
  have hE₀c := two_le_coheight_of_isExceptional E₀ hE₀
  have : IsDominant qS := hqSb.isDominant
  have : IsDominant a := isDominant_of_isOpenImmersion a
  have : Nonempty P := ⟨E₀.genericPoint⟩
  have : MMP.Mori.IsVariety ℂ sS := hSv
  have : MMP.Mori.IsVariety ℂ (qS ≫ sS) := hPv.1
  have hdP : topologicalKrullDim P = d :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (qS ≫ sS) hqSb).symm.trans
      hSd
  have hdY : topologicalKrullDim Y = d :=
    (topologicalKrullDim_eq_of_isOpenImmersion sY a).symm.trans hdP
  obtain ⟨m, hKYm⟩ := hKY
  obtain rfl : m = d := by
    have := hKYm.topologicalKrullDim_eq
    rw [hdY] at this
    exact_mod_cast this.symm
  -- the forms
  have hdS' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sS) hSd
  have hdY' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hdY
  obtain ⟨ωY, hωY0, hωY⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hKYm
  have hbija := functionFieldMap_bijective_of_isOpenImmersion a
  set ωP : RationalPluriForms (qS ≫ sS) m 1 :=
    hsq.symm ▸ pullbackRationalPluriForms sY a ωY with hωPdef
  have hωP : ∀ E : MMP.Mori.PrimeDivisor P,
      E.ordForm ωP = KY.coeff (OpenWeilRestriction.primeDivisorMap a E) := by
    intro E
    rw [ordForm_cast]
    have hη : a E.genericPoint = (OpenWeilRestriction.primeDivisorMap a E).genericPoint :=
      (OpenWeilRestriction.genericPoint_primeDivisorMap a E).symm
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso a hbija hdY' E _ hη ωY,
      hωY]
  have hωP0 : ωP ≠ 0 := by
    intro h0
    have h1 : pullbackRationalPluriForms sY a ωY = 0 := by
      have : ∀ (s s' : P ⟶ Spec (.of ℂ)) (h : s = s') (τ : RationalPluriForms s m 1),
          (h ▸ τ : RationalPluriForms s' m 1) = 0 → τ = 0 := by
        intro s s' h τ hτ; subst h; exact hτ
      exact this _ _ hsq.symm (pullbackRationalPluriForms sY a ωY) h0
    exact hωY0 (pullbackRationalPluriForms_injective sY a hbija hdY' 1
      (h1.trans (pullbackRationalPluriForms_zero sY a).symm))
  obtain ⟨ωS, hωS⟩ := pullbackRationalPluriForms_surjective sS qS
    hqSb.functionFieldMap_bijective hdS' 1 ωP
  have hωS0 : ωS ≠ 0 := by
    rintro rfl
    exact hωP0 (hωS.symm.trans (pullbackRationalPluriForms_zero sS qS))
  have hbijq := hqSb.functionFieldMap_bijective
  -- the canonical divisor `K_S = div(ω_S)`
  obtain ⟨-, nS, KS, hKS, -⟩ := hC.1.isPair
  obtain rfl : nS = m := by
    have := hKS.topologicalKrullDim_eq
    rw [hSd] at this
    exact_mod_cast this.symm
  set K' : Divisor S := divisorOfForm ωS with hK'def
  have hK' : K'.IsCanonicalDivisor sS nS :=
    hKS.of_linearlyEquivalent (by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSQ.1 hKS hωS0)
  -- `G = q_S^*(K_S + C)`
  have hLq : (Divisor.toQDivisor K' + C).IsQCartier := isQCartier_of_isQFactorial sS hSQ _
  have hLc := isCartierCombination_toRDivisor_of_isQCartier hLq
  obtain ⟨mL, r, Ls, hLs, hLeq⟩ := hLc
  have hB : ∀ j (Z : irreducibleComponents P), qS (componentGenericPoint P Z) ∉ (Ls j).supp :=
    fun j Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant qS (Ls j) Z
  set Ls' : Fin mL → Divisor P := fun j => (Ls j).pullback (hLs j) (hB j) with hLs'def
  have hpbj : ∀ j, (Ls j).IsPullback qS (hB j) (Ls' j) := fun j =>
    Divisor.isPullback_pullback (hLs j) (hB j)
  set G : RDivisor P := ∑ j, r j • Divisor.toRDivisor (Ls' j) with hGdef
  have hG : IsRCartierPullback qS (QDivisor.toRDivisor (Divisor.toQDivisor K' + C)) G :=
    ⟨mL, r, Ls, Ls', hLs, by rw [hLeq]; simp only [toRDivisor_eq_mapCoeffs],
      fun j => ⟨hB j, hpbj j⟩, rfl⟩
  have hGc : IsCartierCombination G :=
    ⟨mL, r, Ls', fun j => (hLs j).isCartier_pullback qS (hB j), by
      simp only [hGdef, toRDivisor_eq_mapCoeffs]⟩
  -- `A = (K_Y + C_Y)|_P`
  have hMnef := isRelativelyNef_toRDivisor ℂ sY hnef
  obtain ⟨mM, rM, LM, hLM, hMeq, -⟩ := id hMnef
  have hBM : ∀ j (Z : irreducibleComponents P), a (componentGenericPoint P Z) ∉ (LM j).supp :=
    fun j Z => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant a (LM j) Z
  set LM' : Fin mM → Divisor P := fun j => (LM j).pullback (hLM j) (hBM j) with hLM'def
  set A : RDivisor P := ∑ j, rM j • Divisor.toRDivisor (LM' j) with hAdef
  have hA : IsRCartierPullback a (QDivisor.toRDivisor (Divisor.toQDivisor KY + CY)) A :=
    ⟨mM, rM, LM, LM', hLM, hMeq,
      fun j => ⟨hBM j, Divisor.isPullback_pullback (hLM j) (hBM j)⟩, rfl⟩
  have hAc : IsCartierCombination A :=
    ⟨mM, rM, LM', fun j => (hLM j).isCartier_pullback a (hBM j), by
      simp only [hAdef, toRDivisor_eq_mapCoeffs]⟩
  have hAnef : IsRelativelyNef ℂ (a ≫ sY) qS A :=
    isRelativelyNef_of_isRCartierPullback_of_isOpenImmersion j₀ q qS a hw.symm hMnef hA
  have hAnef' : IsRelativelyNef ℂ (qS ≫ sS) qS A := by
    have key : ∀ (s s' : P ⟶ Spec (.of ℂ)) (_ : QuasiCompact s) (_ : QuasiCompact s'), s = s' →
        IsRelativelyNef ℂ s qS A → IsRelativelyNef ℂ s' qS A := by
      intro s s' _ _ h hA'
      subst h
      exact hA'
    exact key _ _ inferInstance inferInstance hsq.symm hAnef
  -- `G - A` vanishes along the non-exceptional prime divisors
  have hBG : ∀ P' : MMP.Mori.PrimeDivisor P, ¬ IsExceptionalPrimeDivisor sS qS P' →
      0 ≤ (G - A).coeff P' := by
    intro P' hP'
    obtain ⟨Γ, hΓ⟩ := exists_genericPoint_eq_of_not_isExceptionalPrimeDivisor hSQ.1 hPv hqSb P' hP'
    have := Γ.isDiscreteValuationRing_localRing
    haveI : ValuationRing (S.presheaf.stalk (qS P'.genericPoint)) := by
      rw [hΓ]; infer_instance
    haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing qS hbijq P'.genericPoint
    have hη : a P'.genericPoint = (OpenWeilRestriction.primeDivisorMap a P').genericPoint :=
      (OpenWeilRestriction.genericPoint_primeDivisorMap a P').symm
    rw [DivisorWithCoeffs.coeff_sub, coeff_eq_of_isRCartierPullback P' Γ hΓ hG,
      coeff_eq_of_isRCartierPullback P' _ hη hA]
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      hK'def, coeff_divisorOfForm, hne P' Γ hΓ, ← hωP P']
    rw [← hωS, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso qS hbijq hdS' P' Γ hΓ ωS]
    simp
  have hBeff := isEffective_of_isNumericallyEquivalentOver_pullback ℂ sS (qS ≫ sS) hSQ.1 hPv qS
    rfl hqSb (isCartierCombination_toRDivisor_of_isQCartier hLq) hG hAc hAnef'
    (isCartierCombination_sub hGc hAc) hBG
    (isNumericallyEquivalentOver_of_eq (qS ≫ sS) qS (add_sub_cancel A G).symm hGc)
  -- the coefficient along `E₀`
  set D₀ : DivisorOver ℂ sS := ⟨P, qS, hPv, hqSb, E₀⟩ with hD₀
  set b₀ : ℝ := 1 + (D₀.ordPullback ωS : ℝ) - ∑ j, r j * ((Ls' j).coeff E₀ : ℝ) with hb₀
  have hlog : MMP.Intersection.IsLogDiscrepancy sS nS (QDivisor.toRDivisor C) D₀ b₀ := by
    refine ⟨hSQ.1, inferInstanceAs (IsProper qS), ωS, hωS0, ⟨K', hK', fun Γ => rfl⟩, mL, r, Ls,
      Ls', hLs, fun Γ => ?_, fun j => ⟨hB j, hpbj j⟩, rfl⟩
    have h := congrArg (fun D : RDivisor S => D.coeff Γ) hLeq
    simp only [← toRDivisor_eq_mapCoeffs, MMP.Flips.coeff_sum_smul_toRDivisor] at h
    rw [← h]
    simp [hK'def, Divisor.coeff_toQDivisor]
  have h1 := hexc E₀ hE₀c nS b₀ hlog
  have hord : (D₀.ordPullback ωS : ℤ) = KY.coeff (OpenWeilRestriction.primeDivisorMap a E₀) := by
    change E₀.ordForm (pullbackRationalPluriForms sS qS ωS) = _
    rw [hωS, hωP]
  have hη₀ : a E₀.genericPoint = (OpenWeilRestriction.primeDivisorMap a E₀).genericPoint :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap a E₀).symm
  have hAcoef := coeff_eq_of_isRCartierPullback E₀ _ hη₀ hA
  have hGcoef : G.coeff E₀ = ∑ j, r j * ((Ls' j).coeff E₀ : ℝ) :=
    MMP.Flips.coeff_sum_smul_toRDivisor r Ls' E₀
  have h2 := hBeff E₀
  rw [DivisorWithCoeffs.coeff_sub, hAcoef, hGcoef] at h2
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    at h2
  have h3 : ((D₀.ordPullback ωS : ℤ) : ℝ) =
      ((KY.coeff (OpenWeilRestriction.primeDivisorMap a E₀) : ℤ) : ℝ) := by rw [hord]
  push_cast at h2 h3
  linarith

end Negativity

/-! ### The boundary on a log resolution -/

section Boundary

open MMP.Flips

/-- **The coefficients of a klt boundary on a `ℚ`-factorial variety are less than one**: the log
discrepancy of a prime divisor `P` of `X` is `1 - Ω_P`. -/
private theorem coeff_lt_one_of_isKltPair {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hXQ : IsQFactorial sX)
    {Ω : QDivisor X} (hΩ : IsKltPair sX Ω) (P : MMP.Mori.PrimeDivisor X) :
    (Ω.coeff P : ℝ) < 1 := by
  obtain ⟨hX, n, K, hK, -⟩ := hΩ.1.isPair
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hrelD⟩ := isCartierCombination_toRDivisor_of_isQCartier
    (isQCartier_of_isQFactorial sX hXQ (Divisor.toQDivisor K + Ω))
  have hrel : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (QDivisor.toRDivisor (Divisor.toQDivisor K + Ω)).coeff Γ = ∑ i, r i * (C i).coeff Γ := by
    intro Γ
    rw [hrelD]
    simp only [← toRDivisor_eq_mapCoeffs, MMP.Flips.coeff_sum_smul_toRDivisor]
  let E := DivisorOver.ofPrimeDivisor ℂ hX P
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : CompactSpace E.Y := inferInstanceAs (CompactSpace X)
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hC j)
  have hco : ∀ j, ((L' j).coeff E.E : ℝ) = (C j).coeff P := by
    intro j
    obtain ⟨U, hU, φ, hφ⟩ := hC j P.genericPoint
    have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF (hL' j) hφ E.E hU
      (MMP.Mori.pointComponent P.genericPoint)
    have hPU : (P.support ∩ U).Nonempty := (P.genericPoint_mem_iff U).mp hU
    have h2 := hφ P hPU
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
    have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hZ] at h2
    change (L' j).coeff P = X.ord (functionFieldMap (𝟙 X) _) P.genericPoint at h1
    rw [functionFieldMap_id_apply] at h1
    exact_mod_cast h1.trans h2.symm
  have hord : E.ordPullback ω = P.ordForm ω := DivisorOver.ordPullback_ofPrimeDivisor hX hn P ω
  have hrel' : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) +
      (QDivisor.toRDivisor Ω).coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hrel Γ]
    simp [hωK Γ, Divisor.coeff_toQDivisor]
  have hlog : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Ω) E
      (1 + (E.ordPullback ω : ℝ) - ∑ i, r i * (L' i).coeff E.E) :=
    ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, m, r, C, L',
      hC, hrel', fun j => ⟨_, hL' j⟩, rfl⟩
  have hpos := hΩ.2 n E _ hlog
  have hP := hrel' P
  simp_rw [hco, hord] at hpos
  rw [QDivisor.coeff_toRDivisor] at hP
  linarith

/-- **The boundary on a log resolution.** Let `π : W ⟶ S₀` be a log resolution of the closure in
`S₀` of a klt boundary `C` on an open `j₀ : S ⟶ S₀` with `S` `ℚ`-factorial. There is an snc
`ℚ`-divisor `C_W` with coefficients in `[0, 1)` which is `C` along the strict transforms of the
prime divisors of `S`, and exceeds `1 - a(E, S, C)` along the prime divisors `E` of `W` whose
centre on `S` has codimension at least two. -/
private theorem exists_boundary_of_isLogResolution
    {S₀ : Scheme.{0}} [IsIntegral S₀] [IsLocallyNoetherian S₀] [IsNormal S₀]
    (sS₀ : S₀ ⟶ Spec (.of ℂ)) (hS₀n : IsNormalVariety ℂ sS₀)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSQ : IsQFactorial sS)
    (j₀ : S ⟶ S₀) [IsOpenImmersion j₀] (C : QDivisor S) (hC : IsKltPair sS C)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (π : W ⟶ S₀) (hπ : MMP.Mori.IsLogResolution sS₀
      (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j₀) (QDivisor.toRDivisor C)) π) :
    ∃ CW : QDivisor W, (∀ P, 0 ≤ CW.coeff P ∧ CW.coeff P < 1) ∧
      DivisorWithCoeffs.IsSNC (π ≫ sS₀) CW ∧
      (∀ (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor S),
        π P.genericPoint = j₀ Γ.genericPoint → CW.coeff P = C.coeff Γ) ∧
      (∀ (P : MMP.Mori.PrimeDivisor W) (x : S), π P.genericPoint = j₀ x →
        2 ≤ Order.coheight x → ∀ D : DivisorOver ℂ sS,
        (haveI := hπ.isBirationalMorphism.isDominant
         haveI := isDominant_of_isOpenImmersion j₀
         ∀ t : S₀.functionField, D.valuation (functionFieldMap j₀ t) =
          P.divisorialValuation (functionFieldMap π t)) →
        ∀ (n : ℕ) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor C) D a →
          1 - a < CW.coeff P) := by
  classical
  set Δ₀ : RDivisor S₀ :=
    Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j₀) (QDivisor.toRDivisor C) with hΔ₀
  have hπb := hπ.isBirationalMorphism
  have : IsDominant π := hπb.isDominant
  have : IsDominant j₀ := isDominant_of_isOpenImmersion j₀
  have : IsProper π := hπ.isProper
  have hWv := hπ.toIsSmoothResolution.isNormalVariety hS₀n
  have : LocallyOfFiniteType (π ≫ sS₀) := hWv.1.1.toLocallyOfFiniteType
  have : LocallyOfFinitePresentation (π ≫ sS₀) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := π ≫ sS₀)).mpr inferInstance
  have := hS₀n.1.toIsSeparated
  have := isSeparated_toTerminal sS₀
  -- the components of `Ex(π) ∪ π⁻¹(Supp Δ₀)`
  obtain ⟨s, hs, hsnc⟩ : ∃ s : Finset (MMP.Mori.PrimeDivisor W),
      (⋃ E ∈ s, E.support) =
        ((MMP.Mori.exceptionalSet π ⊔ Δ₀.supp.preimage π.continuous :
          TopologicalSpace.Closeds W) : Set W) ∧
      DivisorWithCoeffs.IsSNC (π ≫ sS₀) (∑ E ∈ s, Finsupp.single E (1 : ℤ)) := by
    rcases hπ.isSNCSubset with h | h
    · refine ⟨∅, ?_, ?_⟩
      · rw [h]; simp
      · simpa using DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) (π ≫ sS₀)
          hπ.isSmoothScheme
    · exact h
  have hmem : ∀ P : MMP.Mori.PrimeDivisor W, P.genericPoint ∈
      ((MMP.Mori.exceptionalSet π ⊔ Δ₀.supp.preimage π.continuous :
          TopologicalSpace.Closeds W) : Set W) → P ∈ s := by
    intro P hP
    rw [← hs] at hP
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hP
    rwa [(MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P hPE).symm]
  -- the coefficients along the exceptional prime divisors over `S`
  have hc : ∀ P : MMP.Mori.PrimeDivisor W, ∃ c : ℚ, 0 ≤ c ∧ c < 1 ∧
      ∀ D : DivisorOver ℂ sS,
        (∀ t : S₀.functionField, D.valuation (functionFieldMap j₀ t) =
          P.divisorialValuation (functionFieldMap π t)) →
        ∀ (n : ℕ) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor C) D a →
          1 - a < c := by
    intro P
    by_cases hD : ∃ (D : DivisorOver ℂ sS) (n : ℕ) (a : ℝ),
        (∀ t : S₀.functionField, D.valuation (functionFieldMap j₀ t) =
          P.divisorialValuation (functionFieldMap π t)) ∧
        MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor C) D a
    · obtain ⟨D₀, n₀, a₀, hD₀, hl₀⟩ := hD
      have ha₀ : 0 < a₀ := hC.2 n₀ D₀ a₀ hl₀
      obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show max 0 (1 - a₀) < 1 by
        rw [max_lt_iff]; constructor <;> linarith)
      refine ⟨c, ?_, ?_, fun D hD n a hl => ?_⟩
      · exact_mod_cast (le_max_left _ _).trans hc1.le
      · exact_mod_cast hc2
      · have hv : D.valuation = D₀.valuation := Valuation.ext fun t => by
          obtain ⟨t', rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion j₀).surjective t
          rw [hD, hD₀]
        rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl hl₀ hv]
        exact (le_max_right _ _).trans_lt hc1
    · exact ⟨0, le_rfl, by norm_num, fun D hD' n a hl => (hD ⟨D, n, a, hD', hl⟩).elim⟩
  choose c hc0 hc1 hc2 using hc
  -- the coefficients
  let f : MMP.Mori.PrimeDivisor W → ℚ := fun P =>
    if h : ∃ Γ : MMP.Mori.PrimeDivisor S, π P.genericPoint = j₀ Γ.genericPoint then
      C.coeff h.choose
    else if ∃ x : S, π P.genericPoint = j₀ x ∧ 2 ≤ Order.coheight x then c P else 0
  have hf : ∀ P, f P ≠ 0 → P ∈ s := by
    intro P hP
    refine hmem P ?_
    by_cases h : ∃ Γ : MMP.Mori.PrimeDivisor S, π P.genericPoint = j₀ Γ.genericPoint
    · simp only [f, dif_pos h] at hP
      have hspec := h.choose_spec
      generalize h.choose = Γ at hP hspec
      refine Or.inr ?_
      change π P.genericPoint ∈ Δ₀.supp
      rw [DivisorWithCoeffs.mem_supp_iff]
      refine ⟨OpenWeilRestriction.primeDivisorMap j₀ Γ, ?_, ?_⟩
      · rw [DivisorWithCoeffs.coeff_apply, hΔ₀, Finsupp.mapDomain_apply_of_injective
          (OpenWeilRestriction.primeDivisorMap_injective j₀)]
        change ((C.coeff Γ : ℚ) : ℝ) ≠ 0
        exact_mod_cast hP
      · rw [hspec, ← OpenWeilRestriction.genericPoint_primeDivisorMap,
          AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
    · simp only [f, dif_neg h] at hP
      split_ifs at hP with h'
      · obtain ⟨x, hx, hx2⟩ := h'
        refine Or.inl (MMP.Positivity.support_subset_exceptionalSet P ?_ ?_)
        · rw [MMP.Positivity.isExceptional_toRationalMap_iff,
            MMP.Flips.le_closedsCodimension_iff_le_coheight]
          intro y hy
          have hsp : π P.genericPoint ⤳ y := by
            refine specializes_iff_mem_closure.mpr ((closure_minimal ?_ isClosed_closure) hy)
            rintro _ ⟨z, hz, rfl⟩
            have : P.genericPoint ⤳ z := by
              change z ∈ P.support at hz
              rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hz
              exact specializes_iff_mem_closure.mpr hz
            exact (this.map π.continuous).mem_closure
          have hco : Order.coheight (π P.genericPoint) = Order.coheight x := by
            rw [hx]; exact Topology.IsOpenEmbedding.coheight_eq _ j₀.isOpenEmbedding
          exact hx2.trans (hco ▸ Order.coheight_anti (α := S₀) hsp)
        · change P.genericPoint ∈ P.support
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact subset_closure rfl
      · exact absurd rfl hP
  refine ⟨Finsupp.onFinset s f hf, fun P => ?_, ?_, fun P Γ hPΓ => ?_,
    fun P x hx hx2 D hD n a hl => ?_⟩
  · change 0 ≤ f P ∧ f P < 1
    simp only [f]
    split_ifs with h h'
    · refine ⟨hC.1.nonneg _, ?_⟩
      exact_mod_cast coeff_lt_one_of_isKltPair hSQ hC h.choose
    · exact ⟨hc0 P, hc1 P⟩
    · exact ⟨le_rfl, one_pos⟩
  · refine hsnc.of_support_subset fun P hP => ?_
    have hPs := Finsupp.support_onFinset_subset hP
    rw [Finsupp.mem_support_iff]
    simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', if_pos hPs]
    exact one_ne_zero
  · have h : ∃ Γ : MMP.Mori.PrimeDivisor S, π P.genericPoint = j₀ Γ.genericPoint := ⟨Γ, hPΓ⟩
    have hΓ : h.choose = Γ := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (j₀.isOpenEmbedding.injective (h.choose_spec.symm.trans hPΓ))
    change f P = _
    simp only [f, dif_pos h, hΓ]
  · have h : ¬ ∃ Γ : MMP.Mori.PrimeDivisor S, π P.genericPoint = j₀ Γ.genericPoint := by
      rintro ⟨Γ, hΓ⟩
      have hxΓ : x = Γ.genericPoint := j₀.isOpenEmbedding.injective (hx.symm.trans hΓ)
      rw [hxΓ, Γ.coheight_genericPoint] at hx2
      exact absurd hx2 (by decide)
    change 1 - a < ((f P : ℚ) : ℝ)
    simp only [f, dif_neg h]
    rw [if_pos ⟨x, hx, hx2⟩]
    exact hc2 P D hD n a hl

end Boundary

/-! ### The program over `S` -/

section Core

/-- **The output of the program is an isomorphism over `S`.** Let `π : W ⟶ S₀` be a birational
morphism, `j₀ : S ⟶ S₀` an open immersion of a `ℚ`-factorial variety carrying a klt boundary `C`,
and `(Y, C_Y) ⟶ S₀` a projective model with `K_Y + C_Y` nef over `S₀`, birational to `W` over
`S₀` by `φ`, extracting no divisor, with `C_Y = φ_* C_W`. Suppose the coefficients of `C_W` are
those of `C` along the strict transforms of the prime divisors of `S`, and exceed `1 - a(E, S, C)`
along the prime divisors `E` of `W` whose centre on `S` has codimension at least two. Then
`Y ×_{S₀} S = S` and `C_Y|_S = C`. -/
private theorem exists_isPullback_of_isRelativelyNef {d : ℕ}
    {S₀ : Scheme.{0}} [IsIntegral S₀] [IsLocallyNoetherian S₀] [IsNormal S₀]
    (sS₀ : S₀ ⟶ Spec (.of ℂ)) (hS₀n : IsNormalVariety ℂ sS₀)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSQ : IsQFactorial sS) (hSd : topologicalKrullDim S = d)
    (j₀ : S ⟶ S₀) [IsOpenImmersion j₀] (hj₀ : j₀ ≫ sS₀ = sS)
    (C : QDivisor S) (hC : IsKltPair sS C)
    {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (π : W ⟶ S₀) (hπb : IsBirationalMorphism π) (hW : IsNormalVariety ℂ (π ≫ sS₀))
    (CW : QDivisor W)
    (hCW1 : ∀ (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor S),
      π P.genericPoint = j₀ Γ.genericPoint → CW.coeff P = C.coeff Γ)
    (hCW2 : ∀ (P : MMP.Mori.PrimeDivisor W) (x : S), π P.genericPoint = j₀ x →
      2 ≤ Order.coheight x → ∀ D : DivisorOver ℂ sS,
      (haveI := hπb.isDominant
       haveI := isDominant_of_isOpenImmersion j₀
       ∀ t : S₀.functionField, D.valuation (functionFieldMap j₀ t) =
        P.divisorialValuation (functionFieldMap π t)) →
      ∀ (n : ℕ) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor C) D a →
        1 - a < CW.coeff P)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (sY : Y ⟶ Spec (.of ℂ)) (hY : IsNormalVariety ℂ sY) (q : Y ⟶ S₀)
    (hq : IsProjectiveMorphism q) (hqs : q ≫ sS₀ = sY)
    (KY : Divisor Y) (hKY : ∃ m, KY.IsCanonicalDivisor sY m) (CY : QDivisor Y)
    (hnef : QDivisor.IsRelativelyNef sY q (Divisor.toQDivisor KY + CY))
    (φ : W.RationalMap Y) (hφ : MMP.Mori.RationalMap.IsBirational φ)
    (hover : MMP.Flips.RationalMap.IsOver π q φ)
    (hCY : CY = MMP.Mori.RationalMap.transformDivisor φ CW)
    (hsurj : ∀ Q : MMP.Mori.PrimeDivisor Y,
      ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) :
    ∃ (j : S ⟶ Y) (_ : IsOpenImmersion j), IsPullback j (𝟙 S) q j₀ ∧
      ∀ Γ : MMP.Mori.PrimeDivisor S,
        CY.coeff (OpenWeilRestriction.primeDivisorMap j Γ) = C.coeff Γ := by
  have hS₀v := hS₀n.1
  have hWv := hW.1
  have hYv := hY.1
  have hSv := hSQ.1.1
  have : IsSeparated sS₀ := hS₀v.toIsSeparated
  have : IsSeparated sY := hYv.toIsSeparated
  have : IsSeparated (π ≫ sS₀) := hWv.toIsSeparated
  have := isSeparated_toTerminal sY
  have := isSeparated_toTerminal sS₀
  have : IsDominant π := hπb.isDominant
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have hqb : IsBirationalMorphism q := isBirationalMorphism_of_isOver π q hπb hφ hover
  have : IsDominant q := hqb.isDominant
  have hπbij := hπb.functionFieldMap_bijective
  -- the base change of `q` to `S`
  set P := pullback q j₀ with hPdef
  set a : P ⟶ Y := pullback.fst q j₀ with ha
  set qS : P ⟶ S := pullback.snd q j₀ with hqS
  have hpb : IsPullback a qS q j₀ := IsPullback.of_hasPullback q j₀
  have hqsurj : Function.Surjective q := by
    have h1 := q.isClosedMap.isClosed_range.closure_eq
    rw [(IsDominant.denseRange (f := q)).closure_range] at h1
    exact Set.range_eq_univ.mp h1.symm
  have : Nonempty P := by
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    obtain ⟨y, hy⟩ := hqsurj (j₀ x)
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := j₀) y x hy
    exact ⟨z⟩
  have : IsIntegral P := isIntegral_of_isOpenImmersion a
  have hsq : qS ≫ sS = a ≫ sY := by
    rw [← hj₀, ← hqs, ← Category.assoc, ← hpb.w, Category.assoc]
  have hqSp : IsProjectiveMorphism qS := hq.baseChange j₀
  have : IsProper qS := isProper_of_isProjectiveMorphism qS hqSp
  have hPv : IsNormalVariety ℂ (qS ≫ sS) := by
    have : QuasiCompact sS := hSv.toQuasiCompact
    have : IsSeparated (qS ≫ sS) := by rw [hsq]; infer_instance
    have : LocallyOfFiniteType (qS ≫ sS) := by
      have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
      rw [hsq]; infer_instance
    exact ⟨{ }, isNormal_of_isOpenImmersion a⟩
  have : IsNormal P := hPv.2
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (qS ≫ sS)
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (qS ≫ sS)
  have hqSb : IsBirationalMorphism qS := by
    obtain ⟨V, hVne, hV⟩ := hqb.exists_isOpenImmersion
    set O : P.Opens := a ⁻¹ᵁ V
    have hOne : (O : Set P).Nonempty := by
      obtain ⟨y, hyR, hyV⟩ := ((V.isOpen.dense hVne).inter_open_nonempty _ a.opensRange.isOpen
        ⟨a (Classical.arbitrary P), ⟨_, rfl⟩⟩)
      obtain ⟨z, rfl⟩ : y ∈ Set.range a := hyR
      exact ⟨z, hyV⟩
    have hrange : Set.range (O.ι ≫ a) ⊆ Set.range V.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact x.2
    have hlift : IsOpenImmersion ((O.ι ≫ qS) ≫ j₀) := by
      rw [Category.assoc, ← hpb.w, ← Category.assoc,
        ← IsOpenImmersion.lift_fac V.ι (O.ι ≫ a) hrange, Category.assoc]
      infer_instance
    have : IsOpenImmersion (O.ι ≫ qS) := IsOpenImmersion.of_comp _ j₀
    exact MMP.Spreading.isBirationalMorphism_of_isOpenImmersion_ι_comp' qS O hOne
  have : IsDominant a := isDominant_of_isOpenImmersion a
  have : IsDominant j₀ := isDominant_of_isOpenImmersion j₀
  have : IsDominant qS := hqSb.isDominant
  -- the strict transform on `W` of a prime divisor of `P`
  have htr : ∀ E : MMP.Mori.PrimeDivisor P, ∃ PW : MMP.Mori.PrimeDivisor W,
      MMP.Mori.RationalMap.transformPrimeDivisor φ PW =
        some (OpenWeilRestriction.primeDivisorMap a E) ∧
      π PW.genericPoint = j₀ (qS E.genericPoint) := by
    intro E
    obtain ⟨PW, hPW⟩ := hsurj (OpenWeilRestriction.primeDivisorMap a E)
    refine ⟨PW, hPW, ?_⟩
    rw [(map_genericPoint_eq_and_divisorialValuation_eq π q hφ hover hPW).1]
    change q (OpenWeilRestriction.primeDivisorMap a E).genericPoint = _
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap, ← Scheme.Hom.comp_apply, hpb.w,
      Scheme.Hom.comp_apply]
  have hne : ∀ (E : MMP.Mori.PrimeDivisor P) (Γ : MMP.Mori.PrimeDivisor S),
      qS E.genericPoint = Γ.genericPoint →
        CY.coeff (OpenWeilRestriction.primeDivisorMap a E) = C.coeff Γ := by
    intro E Γ hE
    obtain ⟨PW, hPW, hπη⟩ := htr E
    rw [hE] at hπη
    rw [hCY, ← hCW1 PW Γ hπη]
    exact transformDivisor_apply_eq (π ≫ sS₀) π q hπbij hφ hover hPW CW
  have hexc : ∀ E : MMP.Mori.PrimeDivisor P, 2 ≤ Order.coheight (qS E.genericPoint) →
      ∀ (n : ℕ) (b : ℝ), MMP.Intersection.IsLogDiscrepancy sS n (QDivisor.toRDivisor C)
        ⟨P, qS, hPv, hqSb, E⟩ b → 1 - b < CY.coeff (OpenWeilRestriction.primeDivisorMap a E) := by
    intro E hE n b hb
    obtain ⟨PW, hPW, hπη⟩ := htr E
    have hv := (map_genericPoint_eq_and_divisorialValuation_eq π q hφ hover hPW).2
    have hη : a E.genericPoint = (OpenWeilRestriction.primeDivisorMap a E).genericPoint :=
      (OpenWeilRestriction.genericPoint_primeDivisorMap a E).symm
    have key := hCW2 PW (qS E.genericPoint) hπη hE ⟨P, qS, hPv, hqSb, E⟩ (fun t => by
      change E.divisorialValuation (functionFieldMap qS (functionFieldMap j₀ t)) = _
      rw [functionFieldMap_apply_of_comp_eq qS j₀ a q hpb.w.symm t,
        divisorialValuation_functionFieldMap_of_isIso a E _ hη, hv]) n b hb
    have h2 : (MMP.Mori.RationalMap.transformDivisor φ CW).coeff
        (OpenWeilRestriction.primeDivisorMap a E) = CW.coeff PW :=
      transformDivisor_apply_eq (π ≫ sS₀) π q hπbij hφ hover hPW CW
    rw [hCY, h2]
    exact key
  have hnoexc : ∀ E : MMP.Mori.PrimeDivisor P,
      ¬ MMP.Mori.RationalMap.IsExceptional (X := P) qS.toRationalMap E :=
    not_isExceptional_of_isRelativelyNef sS hSQ hSd C hC sY hY q j₀ KY hKY CY hnef a qS hqSb
      hpb.w hPv hsq hne hexc
  have hiso : IsIso qS :=
    isIso_of_forall_not_isExceptional sS (qS ≫ sS) hSQ hPv qS rfl hqSp hqSb hnoexc
  refine ⟨inv qS ≫ a, inferInstance, ?_, fun Γ => ?_⟩
  · exact hpb.of_iso (asIso qS) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)
  · set Q := OpenWeilRestriction.primeDivisorMap (inv qS ≫ a) Γ
    obtain ⟨PW, hPW⟩ := hsurj Q
    have hη := (map_genericPoint_eq_and_divisorialValuation_eq π q hφ hover hPW).1
    have hQη : MMP.Mori.PrimeDivisor.genericPoint Q = a (inv qS Γ.genericPoint) := by
      change Q.genericPoint = _
      rw [OpenWeilRestriction.genericPoint_primeDivisorMap, Scheme.Hom.comp_apply]
    have hπη : π PW.genericPoint = j₀ Γ.genericPoint := by
      rw [hη, hQη, ← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply,
        ← Scheme.Hom.comp_apply (inv qS) qS, IsIso.inv_hom_id]
      rfl
    rw [hCY, ← hCW1 PW Γ hπη]
    exact transformDivisor_apply_eq (π ≫ sS₀) π q hπbij hφ hover hPW CW

end Core

/-- **The birational core.** Let `S₀` be a normal projective complex variety of dimension `d` and
`j₀ : S ⟶ S₀` an open immersion of a `ℚ`-factorial `S` carrying a klt boundary `C`. Under `Q(d)`
there is a projective `ℚ`-factorial klt pair `(Y, C_Y)` with a projective morphism `q : Y ⟶ S₀`
which is an isomorphism over `S`, and `C_Y|_S = C`. -/
private theorem exists_kltModel_isPullback
    {d : ℕ} (hQ : RationalBirationalProgramProperty d)
    {S₀ : Scheme.{0}} [IsIntegral S₀] [IsLocallyNoetherian S₀] [IsNormal S₀]
    (sS₀ : S₀ ⟶ Spec (.of ℂ)) (hS₀p : MMP.Mori.IsProjectiveVariety ℂ sS₀)
    (hS₀n : IsNormalVariety ℂ sS₀) (hS₀d : topologicalKrullDim S₀ = d)
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSQ : IsQFactorial sS)
    (j₀ : S ⟶ S₀) [IsOpenImmersion j₀] (hj₀ : j₀ ≫ sS₀ = sS)
    (C : QDivisor S) (hC : IsKltPair sS C) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (sY : Y ⟶ Spec (.of ℂ)) (q : Y ⟶ S₀) (CY : QDivisor Y) (j : S ⟶ Y) (_ : IsOpenImmersion j),
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ IsQFactorial sY ∧
      IsProjectiveMorphism q ∧ q ≫ sS₀ = sY ∧ IsKltPair sY CY ∧
      IsPullback j (𝟙 S) q j₀ ∧
      ∀ W : MMP.Mori.PrimeDivisor S,
        CY.coeff (OpenWeilRestriction.primeDivisorMap j W) = C.coeff W := by
  have hS₀v := hS₀n.1
  have : LocallyOfFiniteType sS₀ := hS₀v.toLocallyOfFiniteType
  have hSd : topologicalKrullDim S = d :=
    (topologicalKrullDim_eq_of_isOpenImmersion sS₀ j₀).trans hS₀d
  -- a projective log resolution of the closure of `C`
  obtain ⟨W, π, hπ, hπp⟩ := MMP.Mori.exists_isLogResolution_isProjectiveMorphism sS₀ hS₀n
    (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j₀) (QDivisor.toRDivisor C))
  have hres := hπ.toIsSmoothResolution
  have : IsIntegral W := hres.isIntegral
  have : IsNormal W := hres.isNormal
  obtain ⟨hWn, hWd, -⟩ := hres.isNormalVariety hS₀n
  have : LocallyOfFiniteType (π ≫ sS₀) := hWn.1.toLocallyOfFiniteType
  have : QuasiCompact (π ≫ sS₀) := hWn.1.toQuasiCompact
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sS₀)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (π ≫ sS₀)
  obtain ⟨CW, hCWb, hCWsnc, hCW1, hCW2⟩ :=
    exists_boundary_of_isLogResolution sS₀ hS₀n sS hSQ j₀ C hC π hπ
  have hWp : MMP.Mori.IsProjectiveVariety ℂ (π ≫ sS₀) :=
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hWn.1, hπp.comp hS₀p.isProjective⟩
  have hWdim : topologicalKrullDim W = d := hWd.trans hS₀d
  have : AlgebraicGeometry.IsVariety ℂ (π ≫ sS₀) := hWn.1
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (π ≫ sS₀) hres.isSmoothScheme
    hWdim
  -- run the program over `S₀`
  obtain ⟨Pg, hn, -, -, hYQ, hYp, hqp, hYk, hnef, φ, hφb, hover, hCY, hsurj⟩ :=
    hQ.2 W (π ≫ sS₀) S₀ sS₀ π hWp hWn hres.isSmoothScheme hWdim hS₀p hS₀n hS₀d rfl hπp
      hres.isBirationalMorphism K hK CW hCWb hCWsnc
  have hmodel := Pg.isRelativeDltModel Pg.n.toNat (by rw [ENat.coe_toNat hn])
  obtain ⟨j, hj, hpb, hcoeff⟩ := exists_isPullback_of_isRelativelyNef sS₀ hS₀n sS hSQ hSd j₀ hj₀
    C hC π hres.isBirationalMorphism hWn CW hCW1 hCW2 _ hYQ.1 _ hqp hmodel.comp_eq _
    hmodel.isCanonicalDivisor _ hnef φ hφb hover hCY hsurj
  exact ⟨_, inferInstance, inferInstance, inferInstance, _, _, _, j, hj, hYp, hYQ, hqp,
    hmodel.comp_eq, hYk, hpb, hcoeff⟩

/-- **Klt compactification from the rational program.** Let `d ≥ 2` with `Q(d)`, let `T` be a
normal affine complex variety, `f : S ⟶ T` a projective morphism over `ℂ` from a `ℚ`-factorial
(normal) complex variety `S` of dimension `d`, and `C` a `ℚ`-divisor on `S` with `(S, C)` klt
(`MMP.Fourfold.IsKltPair`; in particular `C ≥ 0`). Then there are an open immersion
`ι : T ⟶ T̄` over `ℂ` into a normal projective variety `T̄`, a projective morphism `f̄ : S̄ ⟶ T̄`
over `ℂ` from a `ℚ`-factorial projective variety `S̄`, a klt pair `(S̄, C̄)` and a morphism
`j : S ⟶ S̄` making `S` the pull-back `S̄ ×_{T̄} T`, such that the restriction of `C̄` along the
open immersion `j` is `C`. -/
@[mmp "lem_fourfold_klt_compactification_from_rational_program"]
public theorem exists_kltCompactification_of_rationalBirationalProgramProperty
    {d : ℕ} (_hd : 2 ≤ d) (hQ : RationalBirationalProgramProperty d)
    {T : Scheme.{0}} (sT : T ⟶ Spec (.of ℂ)) (hT : IsNormalVariety ℂ sT) [IsAffine T]
    {S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (sS : S ⟶ Spec (.of ℂ)) (hSQ : IsQFactorial sS) (hSd : topologicalKrullDim S = d)
    (f : S ⟶ T) (hfs : f ≫ sT = sS) (hf : IsProjectiveMorphism f)
    (C : QDivisor S) (hC : IsKltPair sS C) :
    ∃ (Tbar : Scheme.{0}) (sTbar : Tbar ⟶ Spec (.of ℂ)) (ι : T ⟶ Tbar),
      MMP.Mori.IsProjectiveVariety ℂ sTbar ∧ IsNormalVariety ℂ sTbar ∧
      IsOpenImmersion ι ∧ ι ≫ sTbar = sT ∧
      ∃ (Sbar : Scheme.{0}) (_ : IsIntegral Sbar) (_ : IsLocallyNoetherian Sbar)
        (_ : IsNormal Sbar) (sSbar : Sbar ⟶ Spec (.of ℂ)) (fbar : Sbar ⟶ Tbar)
        (Cbar : QDivisor Sbar) (j : S ⟶ Sbar) (_ : IsOpenImmersion j),
        MMP.Mori.IsProjectiveVariety ℂ sSbar ∧ IsQFactorial sSbar ∧
        IsProjectiveMorphism fbar ∧ fbar ≫ sTbar = sSbar ∧
        IsKltPair sSbar Cbar ∧
        IsPullback j f fbar ι ∧
        ∀ W : MMP.Mori.PrimeDivisor S,
          Cbar.coeff (OpenWeilRestriction.primeDivisorMap j W) = C.coeff W := by
  obtain ⟨Tbar, sTbar, ι, hTp, hTn, hι, hιs⟩ := exists_normal_projective_compactification sT hT
  obtain ⟨S₀, _, _, _, sS₀, f₀, j₀, _, hS₀p, hS₀n, hf₀, hf₀s, hpb₀⟩ :=
    exists_normal_projective_extension sT sTbar hTp ι hιs sS hSQ.1 f hfs hf
  have : LocallyOfFiniteType sS₀ := hS₀p.toLocallyOfFiniteType
  have hS₀d : topologicalKrullDim S₀ = d :=
    (topologicalKrullDim_eq_of_isOpenImmersion sS₀ j₀).symm.trans hSd
  obtain ⟨Y, _, _, _, sY, q, CY, j, _, hYp, hYQ, hq, hqs, hYk, hpb, hcoeff⟩ :=
    exists_kltModel_isPullback hQ sS₀ hS₀p hS₀n hS₀d sS hSQ j₀
      (by rw [← hfs, ← hιs, ← hpb₀.w_assoc, hf₀s]) C hC
  refine ⟨Tbar, sTbar, ι, hTp, hTn, hι, hιs, Y, inferInstance, inferInstance, inferInstance, sY,
    q ≫ f₀, CY, j, inferInstance, hYp, hYQ, hq.comp hf₀, by rw [Category.assoc, hf₀s, hqs], hYk,
    ?_, hcoeff⟩
  simpa using hpb.paste_vert hpb₀

end MMP.Fourfold
