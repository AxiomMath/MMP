module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Steps
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.MMP.Flip.DivisorNormalizationLift
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Surface.ContractionChainBound
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Eventually no flipping curve lies in a divisor whose transforms contain no flipped curve

Let `(X_i, D_i, φ_i, φ_i⁺)_{i < L}` be a sequence of flips for `(X, D)` with `X` a threefold over
a field `K` of characteristic zero, and let `G` be a reduced divisor on `X` with birational
transforms `G_i` on `X_i` (`G_0 = G`, `G_{i+1} = g_{i*} G_i`). Suppose that from some index `i₀`
on no flipped curve of `φ_i⁺` lies in `G_{i+1}`. Then from some later index `i₁` on no flipping
curve of `φ_i` lies in `G_i`.

For each component `G^l` of `G`, the flip `g_i` induces, for `i ≥ i₀`, a proper birational
morphism `(G^l_i)^ν ⟶ (G^l_{i+1})^ν` of normalizations, which contracts a curve whenever a
flipping curve of `φ_i` lies in `G^l_i` and is an isomorphism otherwise; a chain of contractions
of curves starting from the normal surface `(G^l_{i₀})^ν` has bounded length.

## Main results

* `MMP.Flips.SequenceOfFlips.exists_forall_not_subset_supp_of_isFlippingCurve`: the statement
  above.

## Implementation notes

The transforms are a family `G i : Divisor X_i` indexed by all `i : ℕ` and constrained only for
`i + 1 < L`. The divisor `G` on `X` is its term `G 0` on `X_0`, the model with `X_0 = X`
(`MMP.Flips.SequenceOfFlips.model_zero`). A curve `C` is contained in `G_i` when
`C ⊆ Supp G_i`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Claim 4.13.3
-/

namespace MMP.Flips.Fa4NoFlippingCurve

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips MMP.Fourfold

section Normalization

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- A prime divisor of a variety, with its reduced structure, is a variety. -/
private theorem isVariety_subscheme (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    haveI := P.integral
    AlgebraicGeometry.IsVariety k (P.idealSheaf.subschemeι ≫ sX) := by
  haveI := P.integral
  haveI : AlgebraicGeometry.IsVariety k sX := hX
  exact (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance,
    inferInstance⟩

/-- The normalization of a prime divisor of a variety is a normal variety. -/
private theorem isNormalVariety_normalization (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    IsNormalVariety k (primeDivisorNormalization P ≫ sX) := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  refine ⟨?_, h.2.1⟩
  have h1 := h.1
  rwa [← Category.assoc] at h1

/-- The normalization of a prime divisor of a variety is finite. -/
private theorem isFinite_normalization (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    IsFinite (primeDivisorNormalization P) := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  have h1 : IsFinite (P.idealSheaf.subscheme.normalization
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) := h.2.2.1
  exact MorphismProperty.comp_mem _ _ _ h1 inferInstance

/-- On an integral scheme locally of finite type over a field, a prime divisor has codimension
one: its dimension plus one is the dimension of the scheme. -/
private theorem topologicalKrullDim_support_add_one [IsIntegral X]
    [LocallyOfFiniteType sX] (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (P.support : Set X) + 1 = topologicalKrullDim X := by
  let _ : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact_mod_cast h

/-- The normalization of a prime divisor of a threefold is a surface. -/
private theorem topologicalKrullDim_normalization (hX : MMP.Mori.IsVariety k sX)
    (h3 : topologicalKrullDim X = 3) (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (primeDivisorNormalizationScheme P) = 2 := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  haveI := h.1
  haveI : AlgebraicGeometry.IsVariety k sX := hX
  haveI : IsIntegral X := hX.toIsIntegral
  have e1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
    (P.idealSheaf.subschemeι ≫ sX) (P.idealSheaf.subscheme.normalization
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) ≫
        (P.idealSheaf.subschemeι ≫ sX)) h.2.2.2.2
  change topologicalKrullDim (P.idealSheaf.subscheme.normalizationScheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) = 2
  rw [← e1, topologicalKrullDim_subscheme_eq]
  have := topologicalKrullDim_support_add_one sX P
  rw [h3] at this
  exact ENat.WithBot.add_one_cancel.mp (this.trans rfl)

/-- The normalization of a prime divisor maps the generic point to the generic point. -/
private theorem primeDivisorNormalization_genericPoint (P : MMP.Mori.PrimeDivisor X)
    [IsIntegral (primeDivisorNormalizationScheme P)] :
    primeDivisorNormalization P (genericPoint (primeDivisorNormalizationScheme P)) =
      P.genericPoint := by
  have := P.integral
  have hz : genericPoint (primeDivisorNormalizationScheme P) ∈
      genericPoints (primeDivisorNormalizationScheme P) := by
    rw [genericPoints_eq_singleton]; rfl
  have h := Scheme.normalization_mem_genericPoints P.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) hz
  rw [genericPoints_eq_singleton] at h
  change P.idealSheaf.subschemeι _ = P.idealSheaf.subschemeι _
  congr 1

/-- The normalization of a prime divisor of a variety is surjective on the stalk at the generic
point: it is a birational morphism followed by the closed immersion `P ⟶ X`. -/
private theorem surjective_stalkMap_normalization (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) [IsIntegral (primeDivisorNormalizationScheme P)] :
    Function.Surjective ((primeDivisorNormalization P).stalkMap
      (genericPoint (primeDivisorNormalizationScheme P))) := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.2.2.2.2
  have hiso := hb.2 (genericPoint (primeDivisorNormalizationScheme P))
    (by rw [genericPoints_eq_singleton]; rfl)
  rw [primeDivisorNormalization, Scheme.Hom.stalkMap_comp]
  exact ((ConcreteCategory.isIso_iff_bijective _).mp hiso).2.comp
    (P.idealSheaf.subschemeι.stalkMap_surjective _)

end Normalization

section Flip

/-- A morphism which restricts to an isomorphism over an open `U` is an isomorphism on the stalks
at the points over `U`. -/
private theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{0}} (g : X ⟶ Y)
    (U : Y.Opens) [IsIso (g ∣_ U)] (x : X) (hx : g x ∈ U) : IsIso (g.stalkMap x) := by
  have h1 : IsIso ((g ∣_ U).stalkMap ⟨x, hx⟩) :=
    ((isIso_iff_isIso_stalkMap (g ∣_ U)).mp inferInstance).2 _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictStalkMap g U ⟨x, hx⟩)).mp h1

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- A partial map `g₀` whose composite with `φp` is equivalent to `φ` satisfies
`g₀.hom ≫ φp = g₀.domain.ι ≫ φ`. -/
private theorem hom_comp_eq_of_compHom_equiv {X X' Z : Scheme.{0}} [IsReduced X] [Z.IsSeparated]
    (g₀ : X.PartialMap X') {φ : X ⟶ Z} {φp : X' ⟶ Z}
    (h : (g₀.compHom φp).equiv φ.toPartialMap) : g₀.hom ≫ φp = g₀.domain.ι ≫ φ := by
  obtain ⟨W, hW, hWl, hWr, hWe⟩ := h
  have hWl' : W ≤ g₀.domain := hWl
  have : IsDominant (X.homOfLE hWl') := Opens.isDominant_homOfLE hW _
  refine ext_of_isDominant (X.homOfLE hWl') ?_
  rw [Scheme.homOfLE_ι_assoc]
  simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom] at hWe
  refine hWe.trans ?_
  simp only [Scheme.Hom.toPartialMap]
  exact Scheme.homOfLE_ι_assoc ..

/-- A morphism `ψ` with `ψ ≫ ν'` agreeing with `ν` followed by a partial map `g₀` on a dense
open satisfies `ψ ≫ ν' ≫ φp = ν ≫ φ` when `g₀` composed with `φp` is equivalent to `φ`. -/
private theorem comp_eq_of_resLE_comp_eq {A B X X' Z : Scheme.{0}} [IsReduced A] [IsReduced X]
    [Z.IsSeparated] (ψ : A ⟶ B) (ν : A ⟶ X) (ν' : B ⟶ X') (g₀ : X.PartialMap X') {φ : X ⟶ Z}
    {φp : X' ⟶ Z} (h : (g₀.compHom φp).equiv φ.toPartialMap) (U : A.Opens)
    (hUd : Dense (U : Set A)) (hU : U ≤ ν ⁻¹ᵁ g₀.domain)
    (hUeq : U.ι ≫ ψ ≫ ν' = ν.resLE g₀.domain U hU ≫ g₀.hom) : ψ ≫ ν' ≫ φp = ν ≫ φ := by
  have : IsDominant U.ι := Opens.isDominant_ι hUd
  refine ext_of_isDominant U.ι ?_
  calc U.ι ≫ ψ ≫ ν' ≫ φp = (U.ι ≫ ψ ≫ ν') ≫ φp := by simp only [Category.assoc]
    _ = (ν.resLE g₀.domain U hU ≫ g₀.hom) ≫ φp := by rw [hUeq]
    _ = U.ι ≫ ν ≫ φ := by
      rw [Category.assoc, hom_comp_eq_of_compHom_equiv g₀ h, ← Category.assoc,
        Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- If `ψ ≫ ν' ≫ φp = ν ≫ φ`, `ν` is surjective on the stalk at `x` and `φ` is an isomorphism on
the stalk at `ν x`, then `ψ` is surjective on the stalk at `x`. -/
private theorem surjective_stalkMap_of_comp_eq {A B X X' Z : Scheme.{0}} (ψ : A ⟶ B) (ν : A ⟶ X)
    (ν' : B ⟶ X') (φ : X ⟶ Z) (φp : X' ⟶ Z) (h : ψ ≫ ν' ≫ φp = ν ≫ φ) (x : A)
    (hν : Function.Surjective (ν.stalkMap x)) [IsIso (φ.stalkMap (ν x))] :
    Function.Surjective (ψ.stalkMap x) := by
  have e1 := Scheme.Hom.stalkMap_congr_hom _ _ h x
  have e2 := Scheme.Hom.stalkMap_comp ψ (ν' ≫ φp) x
  have e3 := Scheme.Hom.stalkMap_comp ν φ x
  intro y
  obtain ⟨a, rfl⟩ := hν y
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (φ.stalkMap (ν x))).2 a
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Z.presheaf.stalkCongr (Inseparable.of_eq (congrArg (fun f : A ⟶ Z ↦ f x) h))).hom).2 b
  refine ⟨(ν' ≫ φp).stalkMap _ c, ?_⟩
  exact congrArg (fun f ↦ f c) (e2.symm.trans (e1.trans (congrArg (_ ≫ ·) e3)))

/-- A morphism of integral schemes sending the generic point to the generic point and surjective
on the stalk there is birational. -/
private theorem isBirational_of_surjective_stalkMap {A B : Scheme.{0}} [IsIntegral A]
    [IsIntegral B] (ψ : A ⟶ B) (hψ : ψ (genericPoint A) = genericPoint B)
    (hs : Function.Surjective (ψ.stalkMap (genericPoint A))) : IsBirational ψ := by
  have hfield : IsField (B.presheaf.stalk (ψ (genericPoint A))) := by
    rw [hψ]
    exact Field.toIsField B.functionField
  let := hfield.toField
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hψ
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(ψ.stalkMap _).hom.injective, hs⟩

/-- A morphism `ψ : P^ν ⟶ (P⁺)^ν` of normalizations agreeing on a dense open with a partial map
`g₀` transforming `P` to `P⁺` sends the generic point to the generic point. -/
private theorem normalization_hom_apply_genericPoint {X X' : Scheme.{0}} [IsReduced X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {P : MMP.Mori.PrimeDivisor X} {Pp : MMP.Mori.PrimeDivisor X'}
    [IsIntegral (primeDivisorNormalizationScheme P)]
    [IsIntegral (primeDivisorNormalizationScheme Pp)] [IsFinite (primeDivisorNormalization Pp)]
    (g₀ : X.PartialMap X')
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor g₀.toRationalMap P = some Pp)
    (ψ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Pp)
    (U : (primeDivisorNormalizationScheme P).Opens)
    (hUd : Dense (U : Set (primeDivisorNormalizationScheme P)))
    (hU : U ≤ primeDivisorNormalization P ⁻¹ᵁ g₀.domain)
    (hUeq : U.ι ≫ ψ ≫ primeDivisorNormalization Pp =
      (primeDivisorNormalization P).resLE g₀.domain U hU ≫ g₀.hom) :
    ψ (genericPoint (primeDivisorNormalizationScheme P)) =
      genericPoint (primeDivisorNormalizationScheme Pp) := by
  have hηU : genericPoint (primeDivisorNormalizationScheme P) ∈ U :=
    ((genericPoint_spec (primeDivisorNormalizationScheme P)).mem_open_set_iff U.isOpen).mpr
      (by simpa using hUd.nonempty)
  have hνη := primeDivisorNormalization_genericPoint P
  have hdom : P.genericPoint ∈ g₀.domain := hνη ▸ hU hηU
  have hg₀P : g₀.hom ⟨P.genericPoint, hdom⟩ = Pp.genericPoint := by
    have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor hP
    rw [MMP.Flips.coe_transform_eq_closure_singleton g₀ rfl P hdom,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
    exact (inseparable_iff_closure_eq.2 h1).eq.symm
  let x : U.toScheme := ⟨_, hηU⟩
  have h1 : primeDivisorNormalization Pp (ψ (genericPoint (primeDivisorNormalizationScheme P)))
      = g₀.hom ((primeDivisorNormalization P).resLE g₀.domain U hU x) :=
    congrArg (fun f : U.toScheme ⟶ X' ↦ f x) hUeq
  have h3 : (primeDivisorNormalization P).resLE g₀.domain U hU x = ⟨P.genericPoint, hdom⟩ :=
    Subtype.ext ((Scheme.Hom.coe_resLE_apply _ _ _).trans hνη)
  rw [h3, hg₀P] at h1
  exact (eq_of_specializes_of_isFinite (primeDivisorNormalization Pp)
    ((genericPoint_spec _).specializes (Set.mem_univ _))
    ((primeDivisorNormalization_genericPoint Pp).trans h1.symm)).symm

variable {k : Type} [Field k] {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {E : RDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}

/-- **The morphism of normalizations along a flip.** Let `φ⁺ : X⁺ ⟶ Z` be a flip of `φ : X ⟶ Z`
with birational map `g`, `P ⊆ X` a prime divisor with transform `P⁺ = g_* P`, and
`ψ : P^ν ⟶ (P⁺)^ν` a morphism of normalizations agreeing with `g` on a dense open subset. Then
`ψ` is a proper birational morphism over `k`. -/
private theorem normalization_hom_spec (hflip : IsFlip k sX sZ sX' E φ φp g)
    {P : MMP.Mori.PrimeDivisor X} {Pp : MMP.Mori.PrimeDivisor X'}
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor g P = some Pp)
    (ψ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Pp)
    (hψ : ∃ g₀ : X.PartialMap X', g₀.toRationalMap = g ∧
      ∃ U : (primeDivisorNormalizationScheme P).Opens,
        Dense (U : Set (primeDivisorNormalizationScheme P)) ∧
        ∃ hU : U ≤ primeDivisorNormalization P ⁻¹ᵁ g₀.domain,
          U.ι ≫ ψ ≫ primeDivisorNormalization Pp =
            (primeDivisorNormalization P).resLE g₀.domain U hU ≫ g₀.hom) :
    ψ ≫ primeDivisorNormalization Pp ≫ sX' = primeDivisorNormalization P ≫ sX ∧
      IsProper ψ ∧ IsBirationalMorphism ψ := by
  have hsm := hflip.isSmall_source
  have hsm' := hflip.isSmall
  have hvX : MMP.Mori.IsVariety k sX := hsm.isVariety_source
  have hvX' : MMP.Mori.IsVariety k sX' := hsm'.isVariety_source
  haveI : IsProper φ := hsm.isProper
  haveI : IsProper φp := hsm'.isProper
  haveI : AlgebraicGeometry.IsVariety k sZ := hsm.isVariety_target
  haveI : AlgebraicGeometry.IsVariety k sX := hvX
  haveI : AlgebraicGeometry.IsVariety k sX' := hvX'
  haveI : Z.IsSeparated := ⟨isSeparated_terminal sZ⟩
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_terminal sX'
  have hN := isNormalVariety_normalization sX hvX P
  haveI : IsIntegral (primeDivisorNormalizationScheme P) := hN.1.toIsIntegral
  haveI : IsIntegral (primeDivisorNormalizationScheme Pp) :=
    (isNormalVariety_normalization sX' hvX' Pp).1.toIsIntegral
  haveI : IsReduced (primeDivisorNormalizationScheme P) := isReduced_of_isIntegral _
  haveI : LocallyOfFiniteType (primeDivisorNormalization P ≫ sX) :=
    hN.1.toLocallyOfFiniteType
  haveI := isFinite_normalization sX hvX P
  haveI := isFinite_normalization sX' hvX' Pp
  haveI : IsIntegral X := hvX.toIsIntegral
  obtain ⟨g₀, rfl, U, hUd, hU, hUeq⟩ := hψ
  have hover : ψ ≫ primeDivisorNormalization Pp ≫ φp = primeDivisorNormalization P ≫ φ :=
    comp_eq_of_resLE_comp_eq ψ _ _ g₀ (by
      rw [← Scheme.PartialMap.toRationalMap_eq_iff]
      exact hflip.isModificationOf.2) U hUd hU hUeq
  have hstr : ψ ≫ primeDivisorNormalization Pp ≫ sX' = primeDivisorNormalization P ≫ sX := by
    simpa only [Category.assoc, hsm'.comp_eq, hsm.comp_eq] using hover =≫ sZ
  have hprop : IsProper ψ := by
    haveI : IsProper (ψ ≫ primeDivisorNormalization Pp ≫ φp) := by
      rw [hover]
      infer_instance
    exact IsProper.of_comp ψ (primeDivisorNormalization Pp ≫ φp)
  haveI : LocallyOfFiniteType ψ := by
    haveI : LocallyOfFiniteType (ψ ≫ primeDivisorNormalization Pp ≫ sX') := by
      rw [hstr]
      infer_instance
    exact locallyOfFiniteType_of_comp ψ (primeDivisorNormalization Pp ≫ sX')
  haveI : IsIso (φ.stalkMap (primeDivisorNormalization P
      (genericPoint (primeDivisorNormalizationScheme P)))) := by
    obtain ⟨W, hW, hWP, -⟩ := exists_isIso_morphismRestrict_of_isSmall hsm
    exact isIso_stalkMap_of_isIso_morphismRestrict φ W _
      (by
        rw [primeDivisorNormalization_genericPoint]
        exact hWP P)
  exact ⟨hstr, hprop, isBirationalMorphism_of_isBirational ψ
    (isBirational_of_surjective_stalkMap ψ
      (normalization_hom_apply_genericPoint g₀ hP ψ U hUd hU hUeq)
      (surjective_stalkMap_of_comp_eq ψ _ _ φ φp hover _
        (surjective_stalkMap_normalization sX hvX P)))⟩

end Flip

section Chain

/-- A proper curve contracted by `ψ` is, with its reduced structure, a `ψ`-exceptional curve. -/
private theorem exists_isExceptionalCurve_of_isContractedBy {k : Type} [Field k]
    {Y Y' : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} (ψ : Y ⟶ Y') (C : ProperCurve sY)
    (hC : C.IsContractedBy ψ) : ∃ C' : Y.IdealSheafData, IsExceptionalCurve ψ C' := by
  refine ⟨Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {C.point}),
    ⟨StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure, C.dim_eq⟩, ψ C.point, ?_⟩
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hC x hx
  · rintro rfl
    exact ⟨C.point, subset_closure rfl, rfl⟩

/-- The finiteness instances carried by a normal variety. -/
private theorem normalVariety_instances {K : Type} [Field K] {Z : Scheme.{0}}
    {s : Z ⟶ Spec (.of K)} (h : IsNormalVariety K s) :
    IsIntegral Z ∧ IsNormal Z ∧ IsLocallyNoetherian Z ∧ CompactSpace Z ∧
      TopologicalSpace.NoetherianSpace Z := by
  have := h.1
  have := h.2
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Z := ⟨⟩
  exact ⟨h.1.toIsIntegral, h.2, inferInstance, inferInstance, inferInstance⟩

/-- **Exceptional curves pull back along birational morphisms of surfaces.** If `h : A ⟶ B` is a
proper birational morphism of normal surfaces and `E` is a `ψ`-exceptional curve on `B`, then
some curve on `A` (the birational transform of `E`) is `(h ≫ ψ)`-exceptional. -/
private theorem exists_isExceptionalCurve_comp {K : Type} [Field K] {A B C : Scheme.{0}}
    {sA : A ⟶ Spec (.of K)} {sB : B ⟶ Spec (.of K)} (hA : IsNormalVariety K sA)
    (hB : IsNormalVariety K sB) (hdA : topologicalKrullDim A = 2)
    (hdB : topologicalKrullDim B = 2) (h : A ⟶ B) [IsProper h] (hb : IsBirationalMorphism h)
    (ψ : B ⟶ C) {E : B.IdealSheafData} (hE : IsExceptionalCurve ψ E) :
    ∃ E' : A.IdealSheafData, IsExceptionalCurve (h ≫ ψ) E' := by
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hA
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hB
  obtain ⟨hcurve, himage⟩ := isCurveIn_inverseTransformIdeal h
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb) hdA.le hdB hE.1
  obtain ⟨x, hx⟩ := hE.2
  refine ⟨_, hcurve, x, ?_⟩
  have hc : (h ≫ ψ).base '' (inverseTransform h E.support : Set A) =
      ψ.base '' (h.base '' (inverseTransform h E.support : Set A)) := by
    rw [Set.image_image]; rfl
  rw [support_inverseTransformIdeal, hc]
  exact (congrArg _ himage).trans hx

/-- A composite of proper birational morphisms of normal varieties over a base is one. -/
private theorem isProper_isBirationalMorphism_comp {K : Type} [Field K] {A B C : Scheme.{0}}
    {sA : A ⟶ Spec (.of K)} {sB : B ⟶ Spec (.of K)} {sC : C ⟶ Spec (.of K)}
    (hA : IsNormalVariety K sA) (hB : IsNormalVariety K sB) (hC : IsNormalVariety K sC)
    {f : A ⟶ B} {g : B ⟶ C}
    (hf : f ≫ sB = sA ∧ IsProper f ∧ IsBirationalMorphism f)
    (hg : g ≫ sC = sB ∧ IsProper g ∧ IsBirationalMorphism g) :
    (f ≫ g) ≫ sC = sA ∧ IsProper (f ≫ g) ∧ IsBirationalMorphism (f ≫ g) := by
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hA
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hB
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hC
  obtain ⟨hf₁, _, hf₃⟩ := hf
  obtain ⟨hg₁, _, hg₃⟩ := hg
  exact ⟨by rw [Category.assoc, hg₁, hf₁], inferInstance,
    isBirationalMorphism_comp_of_isBirational g f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hg₃)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf₃)⟩

/-- The indices of a chain of contractions: `0`, then one past each contracting step. -/
private def chainIndex (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => t n + 1

/-- **Contractions along a chain of normal surfaces are finitely many.** In a chain
`N 0 → N 1 → ⋯` of proper birational morphisms of normal surfaces over a field of characteristic
zero, only finitely many steps map a curve to a point. -/
private theorem finite_setOf_exists_isExceptionalCurve {K : Type} [Field K] [CharZero K]
    (N : ℕ → Scheme.{0}) (s : ∀ j, N j ⟶ Spec (.of K)) (ψ : ∀ j, N j ⟶ N (j + 1))
    (hN : ∀ j, IsNormalVariety K (s j) ∧ topologicalKrullDim (N j) = 2)
    (hψ : ∀ j, ψ j ≫ s (j + 1) = s j ∧ IsProper (ψ j) ∧ IsBirationalMorphism (ψ j)) :
    {j | ∃ C : (N j).IdealSheafData, IsExceptionalCurve (ψ j) C}.Finite := by
  set B := {j | ∃ C : (N j).IdealSheafData, IsExceptionalCurve (ψ j) C}
  obtain ⟨M, hM⟩ := MMP.Mori.exists_forall_length_le_of_isExceptionalCurve_chain K (s 0)
    (hN 0).1 (hN 0).2
  by_contra hinf
  have hcomp : ∀ a b, a ≤ b → ∃ h : N a ⟶ N b,
      h ≫ s b = s a ∧ IsProper h ∧ IsBirationalMorphism h := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨𝟙 _, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _⟩
    | succ b _ ih =>
      obtain ⟨h, hh⟩ := ih
      exact ⟨h ≫ ψ b, isProper_isBirationalMorphism_comp (hN a).1 (hN b).1 (hN (b + 1)).1 hh (hψ b)⟩
  have hinf' : (Set.ofPred (· ∈ B)).Infinite := hinf
  set t := Nat.nth (· ∈ B)
  have ht : ∀ n, chainIndex t n ≤ t n := by
    intro n
    cases n with
    | zero => exact Nat.zero_le _
    | succ n => exact Nat.nth_strictMono hinf' (Nat.lt_succ_self n)
  choose h hh using fun n ↦ hcomp (chainIndex t n) (t n) (ht n)
  have key := hM (M + 1) (fun n ↦ N (chainIndex t n)) (fun n ↦ s (chainIndex t n))
    (fun n ↦ h n ≫ ψ (t n)) (Iso.refl _) (Category.id_comp _) (fun i _ ↦ hN _) ?_
  · omega
  intro i _
  change (h i ≫ ψ (t i)) ≫ s (t i + 1) = s (chainIndex t i) ∧ IsProper (h i ≫ ψ (t i)) ∧
    IsBirationalMorphism (h i ≫ ψ (t i)) ∧
      ∃ C : (N (chainIndex t i)).IdealSheafData, IsExceptionalCurve (h i ≫ ψ (t i)) C
  obtain ⟨h₁, h₂, h₃⟩ := isProper_isBirationalMorphism_comp (hN (chainIndex t i)).1 (hN (t i)).1
    (hN (t i + 1)).1 (hh i) (hψ (t i))
  obtain ⟨-, _, hb⟩ := hh i
  obtain ⟨E, hE⟩ : t i ∈ B := Nat.nth_mem_of_infinite hinf' i
  exact ⟨h₁, h₂, h₃,
    exists_isExceptionalCurve_comp (hN _).1 (hN _).1 (hN _).2 (hN _).2 (h i) hb (ψ (t i)) hE⟩

end Chain

section Divisors

variable {X Y : Scheme.{0}}

open Classical in
/-- The coefficient of `Q` in the image of `D` under a partial map of prime divisors is the sum of
the coefficients of the prime divisors sent to `Q`. -/
private theorem mapPrimeDivisors_apply
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X)
    (Q : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.mapPrimeDivisors φ D Q = D.sum fun P r => if φ P = some Q then r else 0 := by
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun P _ => ?_
  rcases φ P with _ | Q' <;> simp [Finsupp.single_apply]

/-- The transform of an effective divisor is effective. -/
private theorem transformDivisor_apply_nonneg (f : MMP.Mori.RationalMap X Y) {D : Divisor X}
    (hD : ∀ P, 0 ≤ D P) (Q : MMP.Mori.PrimeDivisor Y) :
    0 ≤ MMP.Mori.RationalMap.transformDivisor f D Q := by
  classical
  rw [MMP.Mori.RationalMap.transformDivisor, mapPrimeDivisors_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun P _ => by split_ifs <;> simp [hD P]

/-- For an effective divisor `D`, the coefficient of `f_* P` in `f_* D` is at least that of `P`
in `D`. -/
private theorem le_transformDivisor_apply (f : MMP.Mori.RationalMap X Y) {D : Divisor X}
    (hD : ∀ P, 0 ≤ D P) {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor f P = some Q) :
    D P ≤ MMP.Mori.RationalMap.transformDivisor f D Q := by
  classical
  by_cases hPs : P ∈ D.support
  · rw [MMP.Mori.RationalMap.transformDivisor, mapPrimeDivisors_apply, Finsupp.sum]
    simpa [hP] using Finset.single_le_sum (f := fun P => if f.transformPrimeDivisor P = some Q
      then D P else 0) (fun P _ => by split_ifs <;> simp [hD P]) hPs
  · rw [Finsupp.notMem_support_iff.mp hPs]
    exact transformDivisor_apply_nonneg f hD Q

/-- A prime divisor with nonzero coefficient in `f_* D` is the transform of a prime divisor with
nonzero coefficient in `D`. -/
private theorem exists_transformPrimeDivisor_eq_some_of_transformDivisor_apply_ne_zero
    (f : MMP.Mori.RationalMap X Y) {D : Divisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformDivisor f D Q ≠ 0) :
    ∃ P, D P ≠ 0 ∧ MMP.Mori.RationalMap.transformPrimeDivisor f P = some Q := by
  classical
  rw [MMP.Mori.RationalMap.transformDivisor, mapPrimeDivisors_apply] at h
  obtain ⟨P, hP, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨P, Finsupp.mem_support_iff.mp hP, Classical.byContradiction fun hc => hne (if_neg hc)⟩

/-- An irreducible set contained in the support of a divisor lies in one of its components. -/
private theorem exists_subset_support_of_subset_supp {D : Divisor X} {C : Set X}
    (hC : IsIrreducible C) (h : C ⊆ (D.supp : Set X)) :
    ∃ P, D P ≠ 0 ∧ C ⊆ P.support := by
  classical
  suffices ∀ s : Finset (MMP.Mori.PrimeDivisor X),
      C ⊆ ((s.sup fun E => E.idealSheaf.support : TopologicalSpace.Closeds X) : Set X) →
        ∃ P ∈ s, C ⊆ P.support by
    obtain ⟨P, hP, hCP⟩ := this D.support h
    exact ⟨P, Finsupp.mem_support_iff.mp hP, hCP⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    obtain ⟨x, hx⟩ := hC.nonempty
    simpa using hs hx
  | insert a s _ ih =>
    intro hs
    rw [Finset.sup_insert, TopologicalSpace.Closeds.coe_sup] at hs
    obtain ⟨z, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hC
      {(a.idealSheaf.support : Set X), ((s.sup fun E => E.idealSheaf.support :
        TopologicalSpace.Closeds X) : Set X)}
      (by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact a.idealSheaf.support.isClosed
        · rw [Finset.mem_singleton.mp hz]
          exact TopologicalSpace.Closeds.isClosed _)
      (by rwa [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton])
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact ⟨a, Finset.mem_insert_self _ _, hCz⟩
    · rw [Finset.mem_singleton.mp hz'] at hCz
      obtain ⟨P, hP, hCP⟩ := ih hCz
      exact ⟨P, Finset.mem_insert_of_mem hP, hCP⟩

end Divisors

section Sequence

variable {K : Type} [Field K] {X : Scheme.{0}} {sX : X ⟶ Spec (.of K)} {n : ℕ}
  {KX : Divisor X} {D : QDivisor X}

/-- The successive transforms `P, g_a* P, g_{a+1}* g_a* P, …` of a prime divisor `P` of `X_a`
along a sequence of flips, `none` from the first step at which the transform is not a prime
divisor. -/
private noncomputable def flipChain (S : SequenceOfFlips sX n KX D) (a : ℕ)
    (P : MMP.Mori.PrimeDivisor (S.model a).1) :
    ∀ j, Option (MMP.Mori.PrimeDivisor (S.model (a + j)).1)
  | 0 => some P
  | j + 1 =>
    (flipChain S a P j).bind (MMP.Mori.RationalMap.transformPrimeDivisor (S.flipMap (a + j)))

private theorem flipChain_succ (S : SequenceOfFlips sX n KX D) (a : ℕ)
    (P : MMP.Mori.PrimeDivisor (S.model a).1) (j : ℕ) :
    flipChain S a P (j + 1) =
      (flipChain S a P j).bind (MMP.Mori.RationalMap.transformPrimeDivisor (S.flipMap (a + j))) :=
  rfl

/-- Once the chain of transforms stops, it stays stopped. -/
private theorem flipChain_eq_none_of_le (S : SequenceOfFlips sX n KX D) (a : ℕ)
    (P : MMP.Mori.PrimeDivisor (S.model a).1) {j j' : ℕ} (hjj' : j ≤ j')
    (h : flipChain S a P j = none) : flipChain S a P j' = none := by
  induction j', hjj' using Nat.le_induction with
  | base => exact h
  | succ m _ ih => rw [flipChain_succ, ih, Option.bind_none]

/-- The chain of transforms stops at most once. -/
private theorem subsingleton_setOf_flipChain_stops (S : SequenceOfFlips sX n KX D) (a : ℕ)
    (P : MMP.Mori.PrimeDivisor (S.model a).1) :
    {j | (flipChain S a P j).isSome ∧ flipChain S a P (j + 1) = none}.Subsingleton := by
  intro j hj j' hj'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · simp [flipChain_eq_none_of_le S a P (Nat.succ_le_of_lt h) hj.2] at hj'
  · simp [flipChain_eq_none_of_le S a P (Nat.succ_le_of_lt h) hj'.2] at hj

/-- In a sequence of flips of infinite length starting at a threefold, every model is a
threefold. -/
private theorem topologicalKrullDim_model (S : SequenceOfFlips sX n KX D)
    (hlt : ∀ m : ℕ, (m : ℕ∞) < S.length) (hX : topologicalKrullDim X = 3) (i : ℕ) :
    topologicalKrullDim (S.model i).1 = 3 := by
  induction i with
  | zero => exact (congrArg Sigma.fst S.model_zero).symm ▸ hX
  | succ i ih =>
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    rw [(S.isFlip i (hlt _)).isSmall.dim_eq, ← (S.isSmall i (hlt _)).dim_eq, ih]

/-- **Flipping curves in a chain of transforms are finitely many.** Let `Q j` be prime divisors
of the models `X_{a+j}` of a sequence of flips of a threefold over a field of characteristic zero,
each `Q (j + 1)` the transform of `Q j`, and suppose no flipped curve of `φ_{a+j}⁺` lies in
`Q (j + 1)`. Then only finitely many `Q j` contain a flipping curve of `φ_{a+j}`. -/
private theorem finite_setOf_exists_isFlippingCurve_subset [CharZero K]
    (S : SequenceOfFlips sX n KX D) (hlt : ∀ m : ℕ, (m : ℕ∞) < S.length)
    (hX : topologicalKrullDim X = 3) (a : ℕ) (Q : ∀ j, MMP.Mori.PrimeDivisor (S.model (a + j)).1)
    (hQ : ∀ j, MMP.Mori.RationalMap.transformPrimeDivisor (S.flipMap (a + j)) (Q j) =
      some (Q (j + 1)))
    (hno : ∀ j, ∀ C : Set (S.model (a + j + 1)).1,
      haveI := S.isLocallyNoetherian_model (a + j)
      haveI := S.isNormal_model (a + j)
      haveI := S.compactSpace_model (a + j)
      haveI := S.isLocallyNoetherian_model (a + j + 1)
      haveI := S.isNormal_model (a + j + 1)
      haveI := S.compactSpace_model (a + j + 1)
      IsFlippedCurveOf K (S.model (a + j)).2.1 (S.baseStr (a + j)) (S.model (a + j + 1)).2.1
        (logCanonicalDivisor (S.model (a + j)).2.2.1
          (QDivisor.toRDivisor (S.model (a + j)).2.2.2))
        (S.contraction (a + j)) (S.flip (a + j)) (S.flipMap (a + j)) C →
      ¬ C ⊆ (Q (j + 1)).support) :
    {j | ∃ C, IsFlippingCurve K (S.model (a + j)).2.1 (S.baseStr (a + j))
      (S.contraction (a + j)) C ∧ C ⊆ (Q j).support}.Finite := by
  have hvar i : MMP.Mori.IsVariety K (S.model i).2.1 := (S.isNormalVariety_model i (hlt i)).1
  have hdim := topologicalKrullDim_model S hlt hX
  have hA : ∀ j, ∃ ψ : primeDivisorNormalizationScheme (Q j) ⟶
      primeDivisorNormalizationScheme (Q (j + 1)),
      ∃ g₀ : (S.model (a + j)).1.PartialMap (S.model (a + j + 1)).1,
        g₀.toRationalMap = S.flipMap (a + j) ∧
        ∃ U : (primeDivisorNormalizationScheme (Q j)).Opens,
          Dense (U : Set (primeDivisorNormalizationScheme (Q j))) ∧
          ∃ hU : U ≤ primeDivisorNormalization (Q j) ⁻¹ᵁ g₀.domain,
            U.ι ≫ ψ ≫ primeDivisorNormalization (Q (j + 1)) =
              (primeDivisorNormalization (Q j)).resLE g₀.domain U hU ≫ g₀.hom := by
    intro j
    haveI := S.isLocallyNoetherian_model (a + j)
    haveI := S.isNormal_model (a + j)
    haveI := S.compactSpace_model (a + j)
    haveI := S.isLocallyNoetherian_model (a + j + 1)
    haveI := S.isNormal_model (a + j + 1)
    haveI := S.compactSpace_model (a + j + 1)
    exact exists_normalization_hom_of_forall_isFlippedCurveOf_not_subset K _ _ _ _ _ _ _
      (S.isFlip (a + j) (hlt _)) (hdim _) (Q j) (Q (j + 1)) (hQ j) (hno j)
  choose ψ hψ using hA
  have hspec j : ψ j ≫ primeDivisorNormalization (Q (j + 1)) ≫ (S.model (a + j + 1)).2.1 =
      primeDivisorNormalization (Q j) ≫ (S.model (a + j)).2.1 ∧
      IsProper (ψ j) ∧ IsBirationalMorphism (ψ j) := by
    haveI := S.isLocallyNoetherian_model (a + j)
    haveI := S.isNormal_model (a + j)
    haveI := S.compactSpace_model (a + j)
    haveI := S.isLocallyNoetherian_model (a + j + 1)
    haveI := S.isNormal_model (a + j + 1)
    haveI := S.compactSpace_model (a + j + 1)
    exact normalization_hom_spec (S.isFlip (a + j) (hlt _)) (hQ j) (ψ j) (hψ j)
  refine (finite_setOf_exists_isExceptionalCurve (K := K)
    (fun j => primeDivisorNormalizationScheme (Q j))
    (fun j => primeDivisorNormalization (Q j) ≫ (S.model (a + j)).2.1) ψ
    (fun j => ⟨isNormalVariety_normalization _ (hvar _) _,
      topologicalKrullDim_normalization _ (hvar _) (hdim _) _⟩) hspec).subset
    fun j ⟨C, hC, hCQ⟩ => ?_
  haveI := S.isLocallyNoetherian_model (a + j)
  haveI := S.isNormal_model (a + j)
  haveI := S.compactSpace_model (a + j)
  haveI := S.isLocallyNoetherian_model (a + j + 1)
  haveI := S.isNormal_model (a + j + 1)
  haveI := S.compactSpace_model (a + j + 1)
  obtain ⟨C', hC'⟩ := IsFlip.exists_properCurve_isContractedBy_normalization
    (S.isFlip (a + j) (hlt _)) (hdim _) (hQ j) (hno j) ⟨C, hC, hCQ⟩ (ψ j) (hψ j)
  exact exists_isExceptionalCurve_of_isContractedBy (ψ j) C' hC'

/-- Transforms of a reduced effective divisor along a sequence of flips are effective. -/
private theorem transforms_nonneg (S : SequenceOfFlips sX n KX D) (G : ∀ i, Divisor (S.model i).1)
    (hG0 : MMP.Intersection.IsReducedEffective (G 0))
    (hG : ∀ i, G (i + 1) = MMP.Mori.RationalMap.transformDivisor (S.flipMap i) (G i)) :
    ∀ i P, 0 ≤ G i P := by
  intro i
  induction i with
  | zero =>
    intro P
    rcases hG0 P with h | h
    · exact h.ge
    · change 0 ≤ DivisorWithCoeffs.coeff (G 0) P
      rw [h]
      exact zero_le_one
  | succ i ih =>
    intro P
    rw [hG i]
    exact transformDivisor_apply_nonneg _ ih P

/-- Along a sequence of effective transforms, transforms of components stay components. -/
private theorem transforms_ne_zero_of_flipChain (S : SequenceOfFlips sX n KX D)
    (G : ∀ i, Divisor (S.model i).1)
    (hG : ∀ i, G (i + 1) = MMP.Mori.RationalMap.transformDivisor (S.flipMap i) (G i))
    (hnonneg : ∀ i P, 0 ≤ G i P) {i₀ : ℕ} {P : MMP.Mori.PrimeDivisor (S.model i₀).1}
    (hP : G i₀ P ≠ 0) : ∀ j Q, flipChain S i₀ P j = some Q → G (i₀ + j) Q ≠ 0 := by
  intro j
  induction j with
  | zero =>
    intro Q hQ
    cases Option.some.inj hQ
    exact hP
  | succ j ih =>
    intro Q hQ
    rw [flipChain_succ, Option.bind_eq_some_iff] at hQ
    obtain ⟨Q', hQ', hQQ'⟩ := hQ
    have h1 := lt_of_le_of_ne (hnonneg _ Q') (Ne.symm (ih Q' hQ'))
    have h2 := le_transformDivisor_apply (S.flipMap (i₀ + j)) (hnonneg (i₀ + j)) hQQ'
    rw [← hG (i₀ + j)] at h2
    exact (lt_of_lt_of_le h1 h2).ne'

/-- Every component of the transform `G_{i₀ + j}` is the transform of a component of `G_{i₀}`. -/
private theorem exists_flipChain_eq_some (S : SequenceOfFlips sX n KX D)
    (G : ∀ i, Divisor (S.model i).1)
    (hG : ∀ i, G (i + 1) = MMP.Mori.RationalMap.transformDivisor (S.flipMap i) (G i)) (i₀ : ℕ) :
    ∀ j (Q : MMP.Mori.PrimeDivisor (S.model (i₀ + j)).1), G (i₀ + j) Q ≠ 0 →
      ∃ P, G i₀ P ≠ 0 ∧ flipChain S i₀ P j = some Q := by
  intro j
  induction j with
  | zero => exact fun Q hQ => ⟨Q, hQ, rfl⟩
  | succ j ih =>
    intro Q hQ
    have hQ' : MMP.Mori.RationalMap.transformDivisor (S.flipMap (i₀ + j)) (G (i₀ + j)) Q ≠ 0 := by
      rwa [← hG (i₀ + j)]
    obtain ⟨Q', hQ'0, hQQ'⟩ :=
      exists_transformPrimeDivisor_eq_some_of_transformDivisor_apply_ne_zero _ hQ'
    obtain ⟨P, hP, hPQ'⟩ := ih Q' hQ'0
    exact ⟨P, hP, by rw [flipChain_succ, hPQ', Option.bind_some, hQQ']⟩

/-- Along the chain of transforms of a component of `G_{i₀}`, a flipping curve lies in a
transform that has a further transform only finitely often. -/
private theorem finite_setOf_flipChain_isFlippingCurve [CharZero K]
    (S : SequenceOfFlips sX n KX D) (hlt : ∀ m : ℕ, (m : ℕ∞) < S.length)
    (hX : topologicalKrullDim X = 3) (G : ∀ i, Divisor (S.model i).1) (i₀ : ℕ)
    (hno : ∀ j, ∀ C : Set (S.model (i₀ + j + 1)).1,
      haveI := S.isLocallyNoetherian_model (i₀ + j)
      haveI := S.isNormal_model (i₀ + j)
      haveI := S.compactSpace_model (i₀ + j)
      haveI := S.isLocallyNoetherian_model (i₀ + j + 1)
      haveI := S.isNormal_model (i₀ + j + 1)
      haveI := S.compactSpace_model (i₀ + j + 1)
      IsFlippedCurveOf K (S.model (i₀ + j)).2.1 (S.baseStr (i₀ + j)) (S.model (i₀ + j + 1)).2.1
        (logCanonicalDivisor (S.model (i₀ + j)).2.2.1
          (QDivisor.toRDivisor (S.model (i₀ + j)).2.2.2))
        (S.contraction (i₀ + j)) (S.flip (i₀ + j)) (S.flipMap (i₀ + j)) C →
      ¬ C ⊆ (G (i₀ + j + 1)).supp)
    (P : MMP.Mori.PrimeDivisor (S.model i₀).1)
    (hpos : ∀ j Q, flipChain S i₀ P j = some Q → G (i₀ + j) Q ≠ 0) :
    {j | ∃ Q₀, flipChain S i₀ P j = some Q₀ ∧ (flipChain S i₀ P (j + 1)).isSome ∧
      ∃ C, IsFlippingCurve K (S.model (i₀ + j)).2.1 (S.baseStr (i₀ + j))
        (S.contraction (i₀ + j)) C ∧ C ⊆ Q₀.support}.Finite := by
  by_contra hinf
  have hsome : ∀ j, (flipChain S i₀ P j).isSome := by
    intro j
    obtain ⟨j', ⟨Q₀, hQ₀, -⟩, hjj'⟩ := Set.Infinite.exists_gt hinf j
    rcases h : flipChain S i₀ P j with _ | Q
    · simp [flipChain_eq_none_of_le S i₀ P hjj'.le h] at hQ₀
    · rfl
  let Q j : MMP.Mori.PrimeDivisor (S.model (i₀ + j)).1 := (flipChain S i₀ P j).get (hsome j)
  have hQc j : flipChain S i₀ P j = some (Q j) := (Option.some_get _).symm
  have hQ j : MMP.Mori.RationalMap.transformPrimeDivisor (S.flipMap (i₀ + j)) (Q j) =
      some (Q (j + 1)) := by
    simpa [flipChain_succ, hQc j] using hQc (j + 1)
  refine hinf ((finite_setOf_exists_isFlippingCurve_subset S hlt hX i₀ Q hQ
    fun j C hC hCQ => hno j C hC
      (hCQ.trans (DivisorWithCoeffs.support_subset_supp (hpos _ _ (hQc (j + 1)))))).subset ?_)
  rintro j ⟨Q₀, hQ₀, -, hC⟩
  obtain rfl : Q j = Q₀ := Option.some_inj.mp ((hQc j).symm.trans hQ₀)
  exact hC

end Sequence

end MMP.Flips.Fa4NoFlippingCurve

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

open Fa4NoFlippingCurve MMP.Fourfold in
/-- **FA Claim 4.13.3.** Let `S` be a sequence of flips for `(X, D)` with `X` a threefold over a
field `K` of characteristic zero, and `G i` divisors on the models `X_i` with `G 0` reduced and
`G (i + 1) = g_{i*} (G i)` for `i + 1 < L`. If for every `i ≥ i₀` with `i + 1 < L` no flipped
curve of `φ_i⁺` is contained in `Supp G_{i+1}`, then there is `i₁ ≥ i₀` such that for every
`i ≥ i₁` with `i + 1 < L` no flipping curve of `φ_i` is contained in `Supp G_i`. -/
@[mmp "lem_fa4_eventually_no_flipping_curve_in_g"]
public theorem SequenceOfFlips.exists_forall_not_subset_supp_of_isFlippingCurve
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {sX : X ⟶ Spec (.of K)} {n : ℕ}
    {KX : Divisor X} {D : QDivisor X} (S : SequenceOfFlips sX n KX D)
    (hX : topologicalKrullDim X = 3) (G : ∀ i, Divisor (S.model i).1)
    (hG0 : MMP.Intersection.IsReducedEffective (G 0))
    (hG : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length →
      G (i + 1) = Mori.RationalMap.transformDivisor (S.flipMap i) (G i)) (i₀ : ℕ)
    (h₀ : ∀ i ≥ i₀, ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model (i + 1)).1,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.compactSpace_model i
      haveI := S.isLocallyNoetherian_model (i + 1)
      haveI := S.isNormal_model (i + 1)
      haveI := S.compactSpace_model (i + 1)
      IsFlippedCurveOf K (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
        (logCanonicalDivisor (S.model i).2.2.1 (QDivisor.toRDivisor (S.model i).2.2.2))
        (S.contraction i) (S.flip i) (S.flipMap i) C →
      ¬ C ⊆ (G (i + 1)).supp) :
    ∃ i₁ ≥ i₀, ∀ i ≥ i₁, ((i + 1 : ℕ) : ℕ∞) < S.length → ∀ C : Set (S.model i).1,
      IsFlippingCurve K (S.model i).2.1 (S.baseStr i) (S.contraction i) C →
      ¬ C ⊆ (G i).supp := by
  classical
  by_cases hL : S.length = ⊤
  swap
  · obtain ⟨L, hL'⟩ := WithTop.ne_top_iff_exists.mp hL
    refine ⟨max i₀ L, le_max_left _ _, fun i hi hlt => absurd hlt ?_⟩
    rw [← hL']
    have := le_max_right i₀ L
    exact fun h => absurd (ENat.coe_lt_coe.mp h) (by omega)
  have hlt : ∀ m : ℕ, (m : ℕ∞) < S.length := fun m => hL ▸ ENat.coe_lt_top m
  have hG' i := hG i (hlt _)
  have hnonneg := transforms_nonneg S G hG0 hG'
  let Death (P : MMP.Mori.PrimeDivisor (S.model i₀).1) : Set ℕ :=
    {j | (flipChain S i₀ P j).isSome ∧ flipChain S i₀ P (j + 1) = none}
  let Contr (P : MMP.Mori.PrimeDivisor (S.model i₀).1) : Set ℕ :=
    {j | ∃ Q₀, flipChain S i₀ P j = some Q₀ ∧ (flipChain S i₀ P (j + 1)).isSome ∧
      ∃ C, IsFlippingCurve K (S.model (i₀ + j)).2.1 (S.baseStr (i₀ + j))
        (S.contraction (i₀ + j)) C ∧ C ⊆ Q₀.support}
  have hContr : ∀ P, G i₀ P ≠ 0 → (Contr P).Finite := fun P hP =>
    finite_setOf_flipChain_isFlippingCurve S hlt hX G i₀
      (fun j C hC => h₀ (i₀ + j) (Nat.le_add_right _ _) (hlt _) C hC) P
      (transforms_ne_zero_of_flipChain S G hG' hnonneg hP)
  have hF : (⋃ P ∈ (G i₀).support, (Death P ∪ Contr P)).Finite :=
    (G i₀).support.finite_toSet.biUnion fun P hP =>
      (subsingleton_setOf_flipChain_stops S i₀ P).finite.union
        (hContr P (Finsupp.mem_support_iff.mp hP))
  obtain ⟨m, hm⟩ := hF.bddAbove
  refine ⟨i₀ + m + 1, by omega, fun i hi _ C hC hCsub => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show i₀ ≤ i by omega)
  obtain ⟨-, -, -, -, z, -, hmax, -⟩ := id hC
  obtain ⟨Q₀, hQ₀, hCQ₀⟩ := exists_subset_support_of_subset_supp hmax.1.1 hCsub
  obtain ⟨P, hP, hcP⟩ := exists_flipChain_eq_some S G hG' i₀ j Q₀ hQ₀
  have hjF : j ∈ ⋃ P ∈ (G i₀).support, (Death P ∪ Contr P) := by
    refine Set.mem_biUnion (Finsupp.mem_support_iff.mpr hP) ?_
    rcases h : flipChain S i₀ P (j + 1) with _ | Q₁
    · exact Or.inl ⟨by rw [hcP]; rfl, h⟩
    · exact Or.inr ⟨Q₀, hcP, by rw [h]; rfl, C, hC, hCQ₀⟩
  have := hm hjF
  omega

end MMP.Flips
