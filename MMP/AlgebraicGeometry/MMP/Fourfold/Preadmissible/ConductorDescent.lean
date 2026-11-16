module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.SemismoothDoubleLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelProperties
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Preadmissible section systems descend through the conductor

Let `(T, Δ; L)` be a projective sdlt adjoint pair of dimension `n`, with normalization components
`νᵢ : Tᵢ ⟶ T` carrying the boundaries `Θᵢ = Cᵢ + Δᵢ`, and let `pᵢ : Yᵢ ⟶ Tᵢ` be projective
birational morphisms from normal projective varieties with `Cᵢ` the crepant boundary of
`(Tᵢ, Θᵢ)` on `Yᵢ`, so that `K_{Yᵢ} + Cᵢ = pᵢ^*(νᵢ^*L)` and `(Yᵢ, Cᵢ)` is dlt. Let `m` be an
even integer such that `mL` is Cartier, and such that the adjoints of all strata of the `(Yᵢ, Cᵢ)`
are Cartier in degree `m`. Then every preadmissible section system `(sᵢ)` on the `Yᵢ` is the
pull-back of a unique section of `𝒪_T(mL)`; and if preadmissible systems generate
`𝒪_{Yᵢ}(m(K_{Yᵢ} + Cᵢ))` at every point of every `Yᵢ`, the descended sections generate
`𝒪_T(mL)` at every point of `T`.

The proof descends each `sᵢ` to the normal variety `Tᵢ` by `pᵢ_* 𝒪_{Yᵢ} = 𝒪_{Tᵢ}`, glues the
components across the generic points of the double locus, where preadmissibility identifies the
two (even) residues, which is exactly the condition for a pair of branch functions to descend
through `R[x, y]/(xy) ↪ R[x] × R[y]`, and extends over the remaining codimension-two set by the
`S₂` property of `T`.

## Main results

* `MMP.Fourfold.IsSdltAdjointPair.existsUnique_pullback_eq_of_mem_preadmissibleSections`.

## Implementation notes

As in `MMP.Fourfold.IsSdltAdjointPair`, a section of `𝒪_T(mL)` is a family `t = (tᵢ)ᵢ` of
rational `m`-canonical forms on the normalization components which is, near every point of `T`,
the product `ν^*f · g` of a function `f` on an open `U ⊆ T` and a local generator `g` of
`𝒪_T(mL)` on `U` (`MMP.Fourfold.IsAdjointGeneratorOn`); it generates `𝒪_T(mL)` at `x` when `f`
can be taken to be a unit near `x`. That `mL` is Cartier is the existence of such local generators
around every point, each of whose residues along a conductor component `P ⊆ Tᵢ` is the pull-back
`ν^*(ḡ (dā)^{⊗m})` of a form on the double locus (`MMP.Fourfold.IsLogResiduePresentation` with
sign `1`). For two distinct branches over the same point this is part of
`MMP.Fourfold.IsAdjointGeneratorOn`; for a conductor component glued to itself by an involution `τ`
(a pinch point) it is the extra condition that the residue is `τ`-invariant, without which
`ν^*(mL)` would be Cartier but `mL` need not be. Section systems on the `Yᵢ` are the preadmissible
subspace
`MMP.Fourfold.preadmissibleSections` of a residue-restriction system
`MMP.Fourfold.ResidueRestriction` for the pairs `(Yᵢ, Cᵢ)` in degree `m`, which records that the
`(Yᵢ, Cᵢ)` are projective rational dlt pairs of dimension `n`, that `m` is even and that the
stratum adjoints are Cartier. The descent of `t` to `(sᵢ)` is pull-back of forms along the
function-field extensions of the `pᵢ` (`MMP.Mori.pullbackRationalPluriForms`). The source works
over `ℂ`; the statement is over a field `k`, which `MMP.Fourfold.IsPair` forces to be
algebraically closed of characteristic zero.

The proof works locally on `T` with a local generator `g` of `𝒪_T(mL)`. Writing
`sᵢ = pᵢ^*(φᵢ gᵢ)`, crepancy makes each `φᵢ` regular on the normalization. Over a
codimension-one point `Q` of the double locus the normalization has at most two branches of total
residue degree two, and a `κ(Q)`-isomorphism of the residue fields of two branches induces a
crepant birational map between the adjunction strata of their strict transforms; it is crepant
because the residues of one local generator of `𝒪_T(mL)` generate both adjoints and correspond
under it, and when the strata are points every such map is crepant. Preadmissibility then
identifies the values of the `φᵢ` at the branches, so the `φᵢ` descend through the seminormal
local rings of `T` in codimension one and extend over codimension two by `S₂`.

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- The property of a local generator `g` of `𝒪_T(mL)` on `U` used throughout: it generates
`𝒪_T(m(K_T + Δ))` on `U` (`MMP.Fourfold.IsAdjointGeneratorOn`) and its residue along every
conductor component over `U` is pulled back from the double locus. -/
private def IsResidueGenerator {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (n m : ℕ) (Θ : ∀ i, QDivisor (N.X i)) (U : T.Opens)
    (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m) : Prop :=
  IsAdjointGeneratorOn N n m Θ U g ∧
    ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
      (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
      ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
        (g' : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g' 1 (g i)

/-- The generic point of a prime divisor specializes to every point of its support. -/
private theorem specializes_of_mem_support {X : Scheme.{0}} (D : Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ D.support) : D.genericPoint ⤳ x := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
  exact specializes_iff_mem_closure.mpr hx

/-- Every point of `T` lies under a point of some normalization component. -/
private theorem exists_base_eq {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
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

/-- **Orders of crepant pull-backs of local generators.** If `C` is the crepant boundary of
`(X, Θ)` on a birational model `p : Y ⟶ X` and `g` generates `𝒪_X(m(K_X + Θ))` on an open `W`
containing the image of the generic point of a prime divisor `F` of `Y`, then
`ord_F(p^*g) = -m · coeff_F(C)`. -/
private theorem ordForm_pullback_eq_of_generatesOn {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Θ : QDivisor X} {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ X) [IsDominant p]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {C : QDivisor Y}
    (hC : IsCrepantBoundary sX n K Θ p hY hp C) (F : Mori.PrimeDivisor Y) {m : ℕ} {W : X.Opens}
    (hW : p.base F.genericPoint ∈ W) {g : RationalPluriForms sX n m}
    (hg : GeneratesOn Θ m W g) :
    (F.ordForm (pullbackRationalPluriForms sX p g) : ℚ) = -(m * C.coeff F) := by
  obtain ⟨hX, hK, m', hm', -, U', hU', τ, hτ, hτa⟩ := hC F
  set D : DivisorOver k sX := ⟨Y, p, hY, hp, F⟩
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m').repr τ () with hc_def
  set c' := (ZTensorPower.basis b m).repr g () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hg.1
  set g₀ : X.functionField := c ^ (m : ℤ) * c' ^ (-(m' : ℤ)) with hg₀_def
  have hg₀ : g₀ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord : ∀ Γ : Mori.PrimeDivisor X, p.base F.genericPoint ∈ Γ.support →
      X.ord g₀ Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hτ.2 Γ ⟨_, hΓ, hU'⟩
    have e2 := hg.2 Γ ⟨_, hΓ, hW⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ hτ.1
    have f2 : (Γ.ordForm g : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m g hg.1
    rw [hg₀_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have : ((m : ℚ) * X.ord c Γ.genericPoint + -(m' : ℚ) * X.ord c' Γ.genericPoint) = 0 := by
      linear_combination (m : ℚ) * e1 - (m' : ℚ) * e2 - (m : ℚ) * f1 + (m' : ℚ) * f2
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg₀ hord
  have hY0 : Y.ord (functionFieldMap p g₀) F.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact F.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap p c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg₀_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : ((m : ℚ) * Y.ord (functionFieldMap p c) F.genericPoint +
      -(m' : ℚ) * Y.ord (functionFieldMap p c') F.genericPoint) = 0 := by
    exact_mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (Y.ord (functionFieldMap p c) F.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ hτ.1
  have h2 : (D.ordPullback g : ℚ) =
      (Y.ord (functionFieldMap p c') F.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m g hg.1
  have key : (m' : ℚ) * ((D.ordPullback g : ℚ) + m * C.coeff F) = 0 := by
    linear_combination (m' : ℚ) * h2 - (m : ℚ) * hτa - (m : ℚ) * h1 - hY0'
  have hm0 : (m' : ℚ) ≠ 0 := by positivity
  have := (mul_eq_zero.mp key).resolve_left hm0
  change (D.ordPullback g : ℚ) = _
  linarith

/-- A regular function at a point `y` has nonnegative order along every prime divisor through
`y`. -/
private theorem ord_algebraMap_stalk_nonneg {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} (F : Mori.PrimeDivisor Y) (hyF : y ∈ F.support)
    {b : Y.presheaf.stalk y} (hb : algebraMap (Y.presheaf.stalk y) Y.functionField b ≠ 0) :
    0 ≤ Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField b) F.genericPoint := by
  have hspec : F.genericPoint ⤳ y := specializes_of_mem_support F hyF
  have h1 : F.divisorialValuation (algebraMap (Y.presheaf.stalk y) Y.functionField b) ≤ 1 :=
    (F.divisorialValuation_le_one_iff _).mpr
      ⟨(Y.presheaf.stalkSpecializes hspec).hom b, Mori.algebraMap_stalkSpecializes hspec b⟩
  rw [F.divisorialValuation_eq_exp_neg_ord hb, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

/-- **A nonzero non-unit at a point vanishes along a prime divisor through it** (the converse of
algebraic Hartogs): on a normal integral locally Noetherian scheme, a nonzero element of the
maximal ideal of `𝒪_{Y,y}` has positive order along some prime divisor through `y`. -/
private theorem exists_ord_pos_of_not_isUnit {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} {b : Y.presheaf.stalk y} (hb : b ≠ 0)
    (hu : ¬IsUnit b) : ∃ F : Mori.PrimeDivisor Y, y ∈ F.support ∧
      0 < Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField b) F.genericPoint := by
  have hb' : algebraMap (Y.presheaf.stalk y) Y.functionField b ≠ 0 :=
    fun h => hb (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField (by simpa using h))
  by_contra hF
  push Not at hF
  obtain ⟨u, hu', hub⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hb'
    fun F hyF => le_antisymm (hF F hyF) (ord_algebraMap_stalk_nonneg F hyF hb')
  exact hu (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField hub ▸ hu')

/-- The pull-back of a function from `T` to a model `Y ⟶ X ⟶ T` of a normalization component, as
a rational function on `Y`, is the image of its germ at a point of `Y`. -/
private theorem functionFieldMap_germToFunctionField {T X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (ν : X ⟶ T) (p : Y ⟶ X) [IsDominant p] {U : T.Opens} (f : Γ(T, U)) (y : Y)
    (hy : ν.base (p.base y) ∈ U) [Nonempty (ν ⁻¹ᵁ U)] :
    functionFieldMap p ((X.germToFunctionField (ν ⁻¹ᵁ U)).hom (ν.app U f)) =
      algebraMap (Y.presheaf.stalk y) Y.functionField
        (((p ≫ ν).stalkMap y).hom (T.presheaf.germ U ((p ≫ ν).base y) hy f)) := by
  have h1 : (X.germToFunctionField (ν ⁻¹ᵁ U)).hom (ν.app U f) =
      algebraMap (X.presheaf.stalk (p.base y)) X.functionField
        (X.presheaf.germ (ν ⁻¹ᵁ U) (p.base y) hy (ν.app U f)) := by
    change _ = (X.presheaf.stalkSpecializes _).hom _
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply ..).symm
  rw [h1, functionFieldMap_algebraMap_stalk]
  congr 1
  rw [Scheme.Hom.stalkMap_comp]
  exact congrArg (p.stalkMap y).hom (Scheme.Hom.germ_stalkMap_apply ν U (p.base y) hy f).symm

/-- Pull-back of rational pluriforms is semilinear along the extension of function fields. -/
private theorem pullbackRationalPluriForms_smul {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y] (p : Y ⟶ X) [IsDominant p] {d : ℕ}
    {m : ℤ} (φ : X.functionField) (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms sX p (φ • τ) =
      functionFieldMap p φ • pullbackRationalPluriForms sX p τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  exact MMP.Fourfold.pullbackForms_smul (K := X.functionField) (K' := Y.functionField) φ τ

/-- **The point is a non-vanishing point of the descended function.** Let `g` generate
`𝒪_{Tᵢ}(m(K_{Tᵢ} + Θᵢ))` on `νᵢ⁻¹(U)` and let `Cᵢ` be the crepant boundary of `(Tᵢ, Θᵢ)` on
`Yᵢ`. If `pᵢ^*(νᵢ^*f · g)` generates `𝒪_{Yᵢ}(m(K_{Yᵢ} + Cᵢ))` near a point `y` over `x ∈ U`,
then `f` does not vanish at `x`. -/
private theorem mem_basicOpen_of_generatesOn {k : Type} [Field k] [PerfectField k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Θ : ∀ i, QDivisor (N.X i)} {i : N.ι}
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ N.X i)
    [IsDominant p] {C : QDivisor Y}
    (hcrep : ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism p), IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) p hY hp C)
    {m : ℕ} {U : T.Opens} {g : RationalPluriForms (N.n i ≫ sT) n m}
    (hg : GeneratesOn (Θ i) m (N.n i ⁻¹ᵁ U) g) (f : Γ(T, U)) (y : Y) {V : Y.Opens} (hyV : y ∈ V)
    (hyU : (N.n i).base (p.base y) ∈ U) [Nonempty (N.n i ⁻¹ᵁ U)]
    (hgen : GeneratesOn C m V (pullbackRationalPluriForms (N.n i ≫ sT) p
      (((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) • g))) :
    (N.n i).base (p.base y) ∈ T.basicOpen f := by
  obtain ⟨K, hY, hp, hC⟩ := hcrep
  set φ := ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) with hφ
  set b := ((p ≫ N.n i).stalkMap y).hom (T.presheaf.germ U ((p ≫ N.n i).base y) hyU f) with hb
  have hψ := functionFieldMap_germToFunctionField (N.n i) p f y hyU
  rw [← hφ, ← hb] at hψ
  have hs := hgen
  rw [pullbackRationalPluriForms_smul] at hs
  have hφ0 : functionFieldMap p φ ≠ 0 := fun h0 => hs.1 (by rw [h0, zero_smul])
  have hg0 : pullbackRationalPluriForms (N.n i ≫ sT) p g ≠ 0 :=
    fun h0 => hs.1 (by rw [h0, smul_zero])
  have hb0 : b ≠ 0 := fun h0 => hφ0 (by rw [hψ, h0, map_zero])
  rw [Scheme.mem_basicOpen _ _ _ hyU]
  by_contra hu
  have hbu : ¬IsUnit b := fun h => hu ((isUnit_map_iff ((p ≫ N.n i).stalkMap y).hom _).mp h)
  obtain ⟨F, hyF, hF⟩ := exists_ord_pos_of_not_isUnit hb0 hbu
  rw [← hψ] at hF
  have hspec : F.genericPoint ⤳ y := specializes_of_mem_support F hyF
  have hW : p.base F.genericPoint ∈ N.n i ⁻¹ᵁ U :=
    ((hspec.map p.continuous).mem_open (N.n i ⁻¹ᵁ U).isOpen) hyU
  have hcr := ordForm_pullback_eq_of_generatesOn p hY hp hC F hW hg
  have hgF := hs.2 F ⟨y, hyF, hyV⟩
  haveI : LocallyOfFiniteType (p ≫ N.n i ≫ sT) := hY.1.toLocallyOfFiniteType
  have hdY : letI := functionFieldAlgebra (p ≫ N.n i ≫ sT)
      (Algebra.trdeg k Y.functionField).toNat = n := by
    obtain ⟨hX, hK, -⟩ := hC F
    haveI : LocallyOfFiniteType (N.n i ≫ sT) := hX.1.toLocallyOfFiniteType
    rw [← trdeg_functionField_eq_of_bijective (N.n i ≫ sT) p hp.functionFieldMap_bijective]
    exact toNat_trdeg_functionField_of_topologicalKrullDim_eq hK.topologicalKrullDim_eq
  rw [F.ordForm_smul hdY hφ0 hg0] at hgF
  push_cast at hgF
  have : (0 : ℚ) < Y.ord (functionFieldMap p φ) F.genericPoint := by exact_mod_cast hF
  linarith

/-- The image of a section in the function field does not change under restriction. -/
private theorem germToFunctionField_app_res {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (i : N.ι) {U U' : T.Opens} (hU : U' ≤ U) (f : Γ(T, U))
    [Nonempty (N.n i ⁻¹ᵁ U')] [Nonempty (N.n i ⁻¹ᵁ U)] :
    ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' (f |_ U')) =
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) := by
  have h := congrArg (fun φ => ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom (φ.hom f))
    ((N.n i).naturality (homOfLE hU).op)
  simp only [CommRingCat.comp_apply] at h
  change ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
    ((N.n i).app U' (T.presheaf.map (homOfLE hU).op f)) = _
  rw [h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Pull-back of rational pluriforms along a birational morphism is bijective. -/
private theorem pullbackRationalPluriForms_bijective {k : Type} [Field k] [PerfectField k]
    {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) (g : Y ⟶ X) [IsIntegral Y] [IsDominant g]
    (hg : IsBirationalMorphism g) (m : ℤ) :
    Function.Bijective (pullbackRationalPluriForms (d := d) (m := m) sX g) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  have hbij := hg.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hbij
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  have key : ∀ τ : RationalPluriForms sX d m,
      b'.repr (pullbackRationalPluriForms sX g τ) () = functionFieldMap g (b.repr τ ()) :=
    fun τ => by
      rw [show pullbackRationalPluriForms sX g τ = pullbackFormsAlong hω m τ from
        pullbackForms_eq hω m τ]
      exact repr_pullbackFormsAlong hω m τ
  refine ⟨fun τ τ' he => ?_, fun σ => ?_⟩
  · have h1 := congrArg (fun x => b'.repr x ()) he
    simp only [key] at h1
    rw [← basis_unit_repr_smul b τ, ← basis_unit_repr_smul b τ', hbij.1 h1]
  · obtain ⟨c, hc⟩ := hbij.2 (b'.repr σ ())
    refine ⟨(c • b () : RationalPluriForms sX d m), b'.repr.injective (Finsupp.ext fun u => ?_)⟩
    obtain rfl := Subsingleton.elim u ()
    refine (key _).trans ?_
    rw [← hc]
    simp

/-- The pull-back of a local generator to a crepant model is a local generator of the crepant
boundary over the preimage. -/
private theorem generatesOn_pullback {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {n : ℕ} (hd : topologicalKrullDim X = n) {K : Divisor X}
    {Θ : QDivisor X} {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (p : Y ⟶ X) [IsDominant p] (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p)
    {C : QDivisor Y} (hC : IsCrepantBoundary sX n K Θ p hY hp C) {m : ℕ} {W : X.Opens}
    {g : RationalPluriForms sX n m} (hg : GeneratesOn Θ m W g) :
    GeneratesOn C m (p ⁻¹ᵁ W) (pullbackRationalPluriForms sX p g) := by
  have h00 : pullbackRationalPluriForms sX p (0 : RationalPluriForms sX n m) = 0 := by
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (p ≫ sX)
    let ep : FunctionFieldEquiv (p ≫ sX) sX :=
      functionFieldAlgEquiv sX p hp.functionFieldMap_bijective
    exact map_zero (pluriformPullback (p ≫ sX) sX ep.toHom n m)
  refine ⟨fun h0 => hg.1 ((pullbackRationalPluriForms_bijective sX hd p hp m).1
    (h0.trans h00.symm)), fun F hF => ?_⟩
  obtain ⟨y, hyF, hyW⟩ := hF
  have hFy : F.genericPoint ⤳ y := specializes_of_mem_support F hyF
  have hW : p.base F.genericPoint ∈ W := (hFy.map p.continuous).mem_open W.isOpen hyW
  rw [ordForm_pullback_eq_of_generatesOn p hY hp hC F hW hg]
  ring

/-- Restricting a local generator to a smaller open keeps it a local generator. -/
private theorem IsResidueGenerator.mono {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n m : ℕ} {Θ : ∀ i, QDivisor (N.X i)} {U U' : T.Opens}
    {g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m} (hg : IsResidueGenerator N n m Θ U g)
    (hU : U' ≤ U) : IsResidueGenerator N n m Θ U' g :=
  ⟨⟨fun i => (hg.1.1 i).mono fun _ hx => hU hx,
    fun i j P P' h₁ h₂ h₃ h₄ => hg.1.2 i j P P' h₁ (hU h₂) h₃ h₄⟩,
    fun i P h₁ h₂ => hg.2 i P (hU h₁) h₂⟩

/-- **The strict transform of a codimension-one point.** For a proper birational morphism
`p : Y ⟶ X` of normal varieties, every codimension-one point `x` of `X` is the image of the generic
point of a prime divisor `Γ'` of `Y`, and `p` is an isomorphism of local rings there. -/
private theorem exists_strictTransform {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (hX : IsNormalVariety k sX)
    (p : Y ⟶ X) [IsDominant p] [IsProper p] (hp : IsBirationalMorphism p) (x : X)
    (hx : Order.coheight x = 1) :
    ∃ Γ' : Mori.PrimeDivisor Y, p.base Γ'.genericPoint = x ∧ IsIso (p.stalkMap Γ'.genericPoint) ∧
      ∀ f, Y.ord (functionFieldMap p f) Γ'.genericPoint = X.ord f x := by
  set P : Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx
  have hPx : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hx
  have hsmall : IsSmallMorphism sX sX (𝟙 X) :=
    ⟨hX, hX, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _, by
      rw [(exceptionalSet_eq_bot_iff (𝟙 X)).mpr inferInstance, le_closedsCodimension_iff]
      intro W hW
      obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
      exact absurd (hW hw) (by simp)⟩
  obtain ⟨Γ', Q, hval, himg, himg'⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism (sXp := sX) hX hp hsmall P
  have hsupp : p.base '' (Γ'.support : Set Y) = P.support := by rw [himg, ← himg']; simp
  have hgen : p.base Γ'.genericPoint = P.genericPoint := by
    obtain ⟨w, hw, hwη⟩ : P.genericPoint ∈ p.base '' (Γ'.support : Set Y) := by
      rw [hsupp]; exact MMP.Spreading.genericPoint_mem_support P
    have h1 : Γ'.genericPoint ⤳ w := specializes_of_mem_support Γ' hw
    have h2 : p.base Γ'.genericPoint ⤳ P.genericPoint := hwη ▸ h1.map p.continuous
    have h3 : P.genericPoint ⤳ p.base Γ'.genericPoint :=
      specializes_of_mem_support P (hsupp ▸ ⟨_, MMP.Spreading.genericPoint_mem_support Γ', rfl⟩)
    exact (h2.antisymm h3).eq
  have hordall : ∀ f, Y.ord (functionFieldMap p f) Γ'.genericPoint = X.ord f x := by
    intro f
    by_cases hf0 : f = 0
    · subst hf0; rw [map_zero, Scheme.ord_zero, Scheme.ord_zero]; rfl
    have hfY : functionFieldMap p f ≠ 0 := (map_ne_zero _).mpr hf0
    have h1 := congrArg (fun w => w f) hval
    simp only [MMP.Mori.PrimeDivisor.valuationOver_apply, functionFieldMap_id_apply] at h1
    rw [Γ'.divisorialValuation_eq_exp_neg_ord hfY, P.divisorialValuation_eq_exp_neg_ord hf0] at h1
    rw [← hPx]
    exact neg_inj.mp (WithZero.exp_injective h1)
  refine ⟨Γ', hgen.trans hPx, ?_, hordall⟩
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  have hbij := hp.functionFieldMap_bijective
  have hcomm : ∀ a : X.presheaf.stalk (p.base Γ'.genericPoint),
      algebraMap _ Y.functionField ((p.stalkMap Γ'.genericPoint).hom a) =
        functionFieldMap p (algebraMap _ X.functionField a) := fun a =>
    (functionFieldMap_algebraMap_stalk p Γ'.genericPoint a).symm
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · have h1 := congrArg (algebraMap _ Y.functionField) hab
    rw [hcomm, hcomm] at h1
    exact IsFractionRing.injective _ X.functionField (hbij.1 h1)
  · obtain ⟨f, hf⟩ := hbij.2 (algebraMap _ Y.functionField c)
    by_cases hf0 : f = 0
    · refine ⟨0, IsFractionRing.injective _ Y.functionField ?_⟩
      rw [map_zero, map_zero, ← hf, hf0, map_zero]
    have hz : Order.coheight (p.base Γ'.genericPoint) = 1 := by rwa [hgen, hPx]
    have hfY : functionFieldMap p f ≠ 0 := (map_ne_zero _).mpr hf0
    have hv : 0 ≤ Y.ord (functionFieldMap p f) Γ'.genericPoint := by
      have h1 : Γ'.divisorialValuation (functionFieldMap p f) ≤ 1 := by
        rw [hf]; exact (Γ'.divisorialValuation_le_one_iff _).mpr ⟨c, rfl⟩
      rw [Γ'.divisorialValuation_eq_exp_neg_ord hfY, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h1
      omega
    rw [hordall, ← hPx, ← hgen] at hv
    obtain ⟨a, ha⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hz hf0).mpr hv
    refine ⟨a, IsFractionRing.injective _ Y.functionField ?_⟩
    rw [hcomm, ha, hf]

/-- **Step 1: the quotient by a local generator is regular on the normalization.** For a
preadmissible (indeed any) system `s` with `pᵢ^* tᵢ = sᵢ` and a local generator `g` of
`𝒪_T(mL)` on `U`, `tᵢ = φᵢ · gᵢ` for a rational function `φᵢ` on `Tᵢ` which is regular at every
point of `νᵢ⁻¹(U)`: its order along a prime divisor `Γ` of `Tᵢ` is the order of `pᵢ^*φᵢ` along the
strict transform of `Γ`, which is `ord(sᵢ) + m·coeff(Cᵢ) ≥ 0` by crepancy. -/
private theorem exists_regular_smul_eq {k : Type} [Field k] [PerfectField k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Θ : ∀ i, QDivisor (N.X i)} (i : N.ι)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ N.X i)
    [IsDominant p] (hproj : IsProjectiveMorphism p) {C : QDivisor Y}
    (hcrep : ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism p), IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) p hY hp C)
    {m : ℕ} {U : T.Opens} {g : RationalPluriForms (N.n i ≫ sT) n m}
    (hg : GeneratesOn (Θ i) m (N.n i ⁻¹ᵁ U) g)
    (s : logPluricanonicalSections (p ≫ N.n i ≫ sT) n m C)
    (t : RationalPluriForms (N.n i ≫ sT) n m)
    (ht : pullbackRationalPluriForms (N.n i ≫ sT) p t = (s : _))
    (hdim : topologicalKrullDim (N.X i) = n) :
    ∃ φ : (N.X i).functionField, t = φ • g ∧ ∀ z ∈ N.n i ⁻¹ᵁ U,
      φ ∈ (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range := by
  obtain ⟨K, hY, hp, hC⟩ := hcrep
  let := functionFieldAlgebra (N.n i ≫ sT)
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p ≫ N.n i ≫ sT) := hY.1.toLocallyOfFiniteType
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hproj
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := N.n i ≫ sT) hdim
  have hdY : letI := functionFieldAlgebra (p ≫ N.n i ≫ sT)
      (Algebra.trdeg k Y.functionField).toNat = n := by
    rw [← trdeg_functionField_eq_of_bijective (N.n i ≫ sT) p hp.functionFieldMap_bijective]
    exact hd
  let := functionFieldAlgebra (p ≫ N.n i ≫ sT)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap (N.n i ≫ sT) p
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective (N.n i ≫ sT) p
    hp.functionFieldMap_bijective hd
  set B := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) (m : ℤ)
  have hg0 : B.repr g () ≠ 0 := repr_ne_zero_of_ne_zero _ hg.1
  set φ := B.repr t () / B.repr g () with hφdef
  have htφ : t = φ • g := by
    have e1 := basis_unit_repr_smul B t
    have e2 := basis_unit_repr_smul B g
    refine e1.symm.trans (Eq.trans ?_ (congrArg (φ • ·) e2))
    refine Eq.trans ?_ (smul_smul φ (B.repr g ()) (B ())).symm
    congr 1
    rw [hφdef, div_mul_cancel₀ _ hg0]
  refine ⟨φ, htφ, fun z hz => ?_⟩
  by_cases hφ0 : φ = 0
  · exact ⟨0, by rw [map_zero, hφ0]⟩
  suffices key : ∀ Γ : Mori.PrimeDivisor (N.X i), z ∈ Γ.support →
      0 ≤ (N.X i).ord φ Γ.genericPoint by
    obtain ⟨r, hr⟩ :=
      MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg z hφ0 key
    exact ⟨r, hr⟩
  intro Γ hzΓ
  -- the strict transform of `Γ` on `Y`
  obtain ⟨Γ', hΓ', -, hordΓ⟩ :=
    exists_strictTransform (N.isNormalVariety i) p hp Γ.genericPoint Γ.coheight_genericPoint
  have hW : p.base Γ'.genericPoint ∈ N.n i ⁻¹ᵁ U :=
    hΓ' ▸ (specializes_of_mem_support Γ hzΓ).mem_open (N.n i ⁻¹ᵁ U).isOpen hz
  have hcr := ordForm_pullback_eq_of_generatesOn p hY hp hC Γ' hW hg
  -- the order of `s` along the strict transform
  have hpg0 := (generatesOn_pullback hdim p hY hp hC hg).1
  have hfφ0 : functionFieldMap p φ ≠ 0 := (map_ne_zero _).mpr hφ0
  have hs : (s : RationalPluriForms (p ≫ N.n i ≫ sT) n m) =
      functionFieldMap p φ • pullbackRationalPluriForms (N.n i ≫ sT) p g := by
    rw [← ht, htφ, pullbackRationalPluriForms_smul]
  have hs0 : (s : RationalPluriForms (p ≫ N.n i ≫ sT) n m) ≠ 0 := by
    rw [hs]
    exact smul_ne_zero hfφ0 hpg0
  have hmem := ((mem_logPluricanonicalSections _).mp s.2).2 Γ'
    ⟨Γ'.genericPoint, MMP.Spreading.genericPoint_mem_support Γ', trivial⟩ hs0
  rw [hs, Γ'.ordForm_smul hdY hfφ0 hpg0, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_smul] at hmem
  have hfl : ⌊((m : ℤ) • C.coeff Γ' : ℚ)⌋ =
      -Γ'.ordForm (pullbackRationalPluriForms (N.n i ≫ sT) p g) := by
    rw [zsmul_eq_mul, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [hfl] at hmem
  rw [← hordΓ φ]
  omega

/-- The residue map `𝒪_{T,Q} → κ(x)` at a point `x` of a normalization component over `Q`. -/
private noncomputable def branchMap {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {i : N.ι} (x : N.X i) {Q : T}
    (hx : (N.n i).base x = Q) : T.presheaf.stalk Q →+* (N.X i).residueField x :=
  ((N.X i).residue x).hom.comp (((N.n i).stalkMap x).hom.comp
    (T.presheaf.stalkSpecializes (show (N.n i).base x ⤳ Q by rw [hx])).hom)

/-- Each normalization component `νᵢ : Tᵢ ⟶ T` of a scheme of finite type over a field is a
finite morphism: it is the inclusion of a clopen summand followed by the finite normalization. -/
private theorem isFinite_normalizationComponent {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [LocallyOfFiniteType sT] (N : NormalizationComponents sT hT) (i : N.ι) :
    IsFinite (N.n i) := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hi : IsClosedImmersion (Limits.Sigma.ι N.X i) := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    have : Set.range (Limits.Sigma.ι N.X i) = sigmaMk N.X '' Set.range (Sigma.mk i) := by
      ext x; simp [← sigmaMk_mk]
    rw [this]
    exact (sigmaMk N.X).isClosedMap _ isClosed_range_sigmaMk
  haveI : IsFinite (slcCurveNormalization T hT) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sT) hT
  have h1 : N.n i = Limits.Sigma.ι N.X i ≫ φ.hom ≫ slcCurveNormalization T hT := by
    rw [hφ, Limits.Sigma.ι_desc]
  rw [h1]
  infer_instance

/-- The dimension of an irreducible component of a scheme of finite type over a field is the
local dimension at its generic point. -/
private theorem topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint' {k : Type} [Field k]
    {Y : Scheme.{0}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    topologicalKrullDim Z = topologicalKrullDimAt Y hZ.1.genericPoint := by
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hη := hZ.1.isGenericPoint_genericPoint_closure
  rw [hZc.closure_eq] at hη
  have hηZ : hZ.1.genericPoint ∈ Z := hη.mem
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y s]
  refine le_antisymm
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents Y ∧
      hZ.1.genericPoint ∈ Z'}) => topologicalKrullDim Z') Z ⟨hZ, hηZ⟩) (iSup₂_le fun Z' hZ' => ?_)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {hZ.1.genericPoint} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- An open subscheme of an `n`-fold is an `n`-fold. -/
private theorem isNFold_opens {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {n : ℕ} (h : IsNFold sT n) (U : T.Opens) : IsNFold (U.ι ≫ sT) n := by
  obtain ⟨⟨h1, h2, h3⟩, hred, hdim⟩ := h
  have : IsNoetherian T := by
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
    have : CompactSpace T := (quasiCompact_iff_compactSpace sT).mp h3
    exact {}
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, fun Z hZ => ?_⟩
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint' (U.ι ≫ sT) hZ,
    ← U.ι.isOpenEmbedding.topologicalKrullDimAt_eq,
    topologicalKrullDimAt_eq_iSup_irreducibleComponents k T sT]
  refine le_antisymm (iSup₂_le fun D hD => (hdim D hD.1).le) ?_
  have hC := irreducibleComponent_mem_irreducibleComponents (U.ι hZ.1.genericPoint)
  rw [← hdim _ hC]
  exact le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents T ∧
    U.ι hZ.1.genericPoint ∈ D}) => topologicalKrullDim D) _ ⟨hC, mem_irreducibleComponent⟩

/-- A point closed in an open subscheme of a scheme of finite type over a field is closed. -/
private theorem isClosed_singleton_of_opens {k : Type} [Field k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [LocallyOfFiniteType sT] (U : T.Opens) {x : U.toScheme}
    (hx : IsClosed ({x} : Set U.toScheme)) : IsClosed ({U.ι x} : Set T) := by
  have := LocallyOfFiniteType.jacobsonSpace sT
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [show ({U.ι x} : Set T) = U.ι.base '' {x} from Set.image_singleton.symm]
  exact hx.isLocallyClosed.image U.ι.isOpenEmbedding.isInducing
    U.ι.isOpenEmbedding.isOpen_range.isLocallyClosed

/-- A point of an open subscheme is smooth exactly when it is a smooth point of the scheme. -/
private theorem mem_smoothLocus_ι_iff {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} [LocallyOfFiniteType sT] (U : T.Opens) (y : U.toScheme) :
    y ∈ smoothLocus (U.ι ≫ sT) ↔ U.ι y ∈ smoothLocus sT := by
  have : LocallyOfFinitePresentation sT :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus, smoothLocus_eq_smoothLocus,
    ← Scheme.Hom.preimage_smoothLocus_eq]
  rfl

/-- The completed local model of a point is read on an open subscheme. -/
private theorem hasCompletedLocalModel_ι {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} (U : T.Opens) (y : U.toScheme) {σ : Type*} {h : MvPowerSeries σ k}
    (hy : HasCompletedLocalModel sT (U.ι y) h) : HasCompletedLocalModel (U.ι ≫ sT) y h := by
  obtain ⟨F⟩ := hy
  let e : T.presheaf.stalk (U.ι y) ≃+* U.toScheme.presheaf.stalk y :=
    (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
  have he : ∀ c, e (stalkStructureMap sT (U.ι y) c) = stalkStructureMap (U.ι ≫ sT) y c :=
    fun c => stalkMap_stalkStructureMap (sX := sT) U.ι y c
  obtain ⟨E, hE⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv e
  letI := (stalkStructureMap sT (U.ι y)).toAlgebra
  letI := (stalkStructureMap (U.ι ≫ sT) y).toAlgebra
  refine ⟨AlgEquiv.ofRingEquiv (f := E.symm.trans F.toRingEquiv) fun c => ?_⟩
  have h1 : algebraMap k (CompletedLocalRing U.toScheme y) c =
      algebraMap (U.toScheme.presheaf.stalk y) (CompletedLocalRing U.toScheme y)
        (stalkStructureMap (U.ι ≫ sT) y c) :=
    IsScalarTower.algebraMap_apply k _ _ c
  have h2 : algebraMap k (CompletedLocalRing T (U.ι y)) c =
      algebraMap (T.presheaf.stalk (U.ι y)) (CompletedLocalRing T (U.ι y))
        (stalkStructureMap sT (U.ι y) c) :=
    IsScalarTower.algebraMap_apply k _ _ c
  rw [RingEquiv.trans_apply, h1, ← he, ← hE, RingEquiv.symm_apply_apply, ← h2]
  exact F.commutes c

/-- A double normal crossing point of `T` lying in an open subscheme is a double normal crossing
point of the open subscheme. -/
private theorem isDoubleNormalCrossingPoint_ι {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} {n : ℕ} (U : T.Opens) (y : U.toScheme)
    (hy : IsDoubleNormalCrossingPoint sT n (U.ι y)) :
    IsDoubleNormalCrossingPoint (U.ι ≫ sT) n y := by
  obtain ⟨hT, hc, hm⟩ := hy
  refine ⟨isNFold_opens hT U, ?_, hasCompletedLocalModel_ι U y hm⟩
  have := hc.preimage U.ι.continuous
  rwa [show ({U.ι y} : Set T) = U.ι.base '' {y} from Set.image_singleton.symm,
    U.ι.isOpenEmbedding.injective.preimage_image] at this

/-- The local ring of a scheme at a point smooth over a field is regular. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus' {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {y : X} (hy : y ∈ smoothLocus sX) :
    IsRegularLocalRing (X.presheaf.stalk y) := by
  obtain ⟨U, hyU, hU⟩ := mem_smoothLocus_iff.mp hy
  have : Smooth (U.ι ≫ sX) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sX) ⟨y, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv

/-- No point of the double locus is a smooth point. -/
private theorem notMem_smoothLocus_of_mem_doubleIntersectionLocus {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)} {Q : T}
    (hQ : Q ∈ (doubleIntersectionLocus T : Set T)) : Q ∉ smoothLocus sT := by
  have hsub : {η : T | Order.coheight η = 1 ∧ ¬ IsRegularLocalRing (T.presheaf.stalk η)} ⊆
      ((smoothLocus sT : Set T))ᶜ := fun η hη hs =>
    hη.2 (isRegularLocalRing_stalk_of_mem_smoothLocus' hs)
  exact closure_minimal hsub (smoothLocus sT).isOpen.isClosed_compl hQ

/-- Away from a closed subset of codimension at least two, a scheme with only double normal
crossings in codimension one is semismooth. -/
private theorem exists_isSemismooth_compl {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} {n : ℕ} (h : IsNcInCodimOne sT n) :
    ∃ Z : TopologicalSpace.Closeds T, 2 ≤ closedsCodimension Z ∧
      IsSemismooth (Scheme.Opens.ι (Z.compl : T.Opens) ≫ sT) n := by
  obtain ⟨hT, Z, hZ, hpts⟩ := h
  have : LocallyOfFiniteType sT := hT.1.2.1
  refine ⟨Z, hZ, isNFold_opens hT _, fun x hx => ?_⟩
  have hxZ : Scheme.Opens.ι (Z.compl : T.Opens) x ∉ Z := x.2
  rcases hpts _ (isClosed_singleton_of_opens sT _ hx) hxZ with hs | hd
  · exact Or.inl ((mem_smoothLocus_ι_iff _ x).mpr hs)
  · exact Or.inr (Or.inl (isDoubleNormalCrossingPoint_ι _ x hd))

/-- The residue degree `[κ(x) : κ(f x)]` of a morphism at a point. -/
private noncomputable def residueDegree' {X S : Scheme.{0}} (f : X ⟶ S) (x : X) : ℕ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (S.residueField (f x)) (X.residueField x)

/-- The residue field of the fibre at a point is the residue field of the source, as an
extension of the residue field of the base. -/
private theorem finrank_residueField_fiber_eq {X S : Scheme.{0}} (f : X ⟶ S) (x : X) :
    letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
      (((f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) (by simp)).hom.comp
        ((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
          (f.fiberToSpecResidueField (f x)).appTop).hom).toAlgebra
    Module.finrank (S.residueField (f x))
        (IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) =
      residueDegree' f x ∧
    ((letI := (f.residueFieldMap x).hom.toAlgebra;
      Module.Finite (S.residueField (f x)) (X.residueField x)) →
    Module.Finite (S.residueField (f x))
        (IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))) := by
  letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    (((f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) (by simp)).hom.comp
      ((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop).hom).toAlgebra
  letI := (f.residueFieldMap x).hom.toAlgebra
  have key := f.fiberResidueFieldHom_algebraMap x
  let e : (X.residueField x : Type) ≃ₐ[S.residueField (f x)]
      IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (f.fiberResidueFieldHom x).hom
      (f.bijective_fiberResidueFieldHom x)) fun a => by
        have := congrArg (fun φ => φ.hom a) key
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
        exact this.symm
  exact ⟨e.toLinearEquiv.finrank_eq.symm, fun _ => Module.Finite.equiv e.toLinearEquiv⟩

/-- `finrank_residueField_fiber_eq` at an arbitrary point `w` of the fibre over `s`. -/
private theorem finrank_residueField_fiber_eq' {X S : Scheme.{0}} (f : X ⟶ S) {x : X} {s : S}
    (hx : f x = s) (w : f.fiber s) (hw : f.fiberι s w = x) :
    letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk w) :=
      (((f.fiber s).presheaf.germ ⊤ w (by simp)).hom.comp
        ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
          (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
    Module.finrank (S.residueField s)
        (IsLocalRing.ResidueField ((f.fiber s).presheaf.stalk w)) = residueDegree' f x := by
  subst hx
  obtain rfl : w = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (hw.trans (f.fiberι_asFiber x).symm)
  exact (finrank_residueField_fiber_eq f x).1

/-- **The residue degrees over a point are bounded by the rank.** For a finite flat morphism
`f : X ⟶ S` and distinct points `x₁, …, x_r` of `X` over `s`, `∑ [κ(xᵢ) : κ(s)] ≤ rk_s f`. -/
private theorem sum_residueDegree_le_finrank {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f]
    [Flat f] (s : S) (F : Finset X) (hF : ∀ x ∈ F, f x = s) :
    ∑ x ∈ F, residueDegree' f x ≤ f.finrank s := by
  classical
  have : IsFinite (f.fiberToSpecResidueField s) := MorphismProperty.of_isPullback
    (P := @IsFinite) (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) ‹IsFinite f›
  have : Flat (f.fiberToSpecResidueField s) := MorphismProperty.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) ‹Flat f›
  set t : Spec (S.residueField s) := IsLocalRing.closedPoint _
  have ht : S.fromSpecResidueField s t = s := Scheme.fromSpecResidueField_apply s t
  have hpb := Scheme.Hom.finrank_pullback_snd f (S.fromSpecResidueField s) t
  rw [ht] at hpb
  rw [← hpb]
  change _ ≤ (f.fiberToSpecResidueField s).finrank t
  refine le_of_le_of_eq ?_ ((@Stacks.Morphisms.finrank_eq_finrank_sections_of_specField _ _ _
      (f.fiberToSpecResidueField s) ‹_› ‹_› t).trans
    (@finrank_globalSections_eq_finsum_finrank_stalk (S.residueField s) _ _
      (f.fiberToSpecResidueField s) ‹_›)).symm
  have hfin : Finite (f.fiber s) :=
    finite_of_isFinite_over_field (S.residueField s) (f.fiberToSpecResidueField s)
  letI := Fintype.ofFinite (f.fiber s)
  rw [finsum_eq_sum_of_fintype]
  by_cases hne : Nonempty (f.fiber s)
  swap
  · have : F = ∅ := Finset.eq_empty_of_forall_notMem fun x hx =>
      hne ⟨(f.fiberHomeo s).symm ⟨x, hF x hx⟩⟩
    subst this
    simp
  let w : X → f.fiber s := fun x =>
    if hx : f x = s then (f.fiberHomeo s).symm ⟨x, hx⟩ else Classical.arbitrary _
  have hw : ∀ x ∈ F, f.fiberι s (w x) = x := fun x hx => by
    simp only [w, dif_pos (hF x hx)]
    exact f.fiberι_fiberHomeo_symm s ⟨x, hF x hx⟩
  have hinj : Set.InjOn w F := fun x hx y hy hxy => by
    rw [← hw x hx, ← hw y hy, hxy]
  have hle : ∀ y : f.fiber s,
      (letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk y) :=
        (((f.fiber s).presheaf.germ ⊤ y (by simp)).hom.comp
          ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
            (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
      Module.finrank (S.residueField s)
        (IsLocalRing.ResidueField ((f.fiber s).presheaf.stalk y))) ≤
      (letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk y) :=
        (((f.fiber s).presheaf.germ ⊤ y (by simp)).hom.comp
          ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
            (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
      Module.finrank (S.residueField s) ((f.fiber s).presheaf.stalk y)) := by
    intro y
    letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk y) :=
      (((f.fiber s).presheaf.germ ⊤ y (by simp)).hom.comp
        ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
          (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
    have hfs := @finite_stalk_of_isFinite_over_field (S.residueField s) _ _
      (f.fiberToSpecResidueField s) ‹_› y
    have hpos : 0 < Module.finrank (S.residueField s) ((f.fiber s).presheaf.stalk y) :=
      Module.finrank_pos
    have heq := @finrank_stalk_eq_length_mul_finrank_residueField (S.residueField s) _ _
      (f.fiberToSpecResidueField s) ‹_› y
    change Module.finrank _ _ ≤ Module.finrank _ _
    rw [heq] at hpos ⊢
    rcases Nat.eq_zero_or_pos (Module.length ((f.fiber s).presheaf.stalk y)
      ((f.fiber s).presheaf.stalk y)).toNat with h0 | h0
    · rw [h0, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact Nat.le_mul_of_pos_left _ h0
  calc ∑ x ∈ F, residueDegree' f x
      = ∑ x ∈ F, (letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk (w x)) :=
          (((f.fiber s).presheaf.germ ⊤ (w x) (by simp)).hom.comp
            ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
              (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
          Module.finrank (S.residueField s)
            (IsLocalRing.ResidueField ((f.fiber s).presheaf.stalk (w x)))) :=
        Finset.sum_congr rfl fun x hx =>
          (finrank_residueField_fiber_eq' f (hF x hx) (w x) (hw x hx)).symm
    _ ≤ ∑ x ∈ F, (letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk (w x)) :=
          (((f.fiber s).presheaf.germ ⊤ (w x) (by simp)).hom.comp
            ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
              (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
          Module.finrank (S.residueField s) ((f.fiber s).presheaf.stalk (w x))) :=
        Finset.sum_le_sum fun x _ => hle (w x)
    _ = ∑ y ∈ F.image w, (letI : Algebra (S.residueField s) ((f.fiber s).presheaf.stalk y) :=
          (((f.fiber s).presheaf.germ ⊤ y (by simp)).hom.comp
            ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
              (f.fiberToSpecResidueField s).appTop).hom).toAlgebra
          Module.finrank (S.residueField s) ((f.fiber s).presheaf.stalk y)) :=
        by rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- The residue degree is invariant under residue-bijective changes of source and target. -/
private theorem residueDegree'_eq_of_comp_eq {X X' S S' : Scheme.{0}} (f : X ⟶ S)
    (f' : X' ⟶ S') (a : X' ⟶ X) (b : S' ⟶ S) (h : a ≫ f = f' ≫ b) (x' : X')
    (ha : Function.Bijective (a.residueFieldMap x').hom)
    (hb : Function.Bijective (b.residueFieldMap (f' x')).hom) :
    residueDegree' f' x' = residueDegree' f (a x') := by
  have h1 : residueDegree' f (a x') =
      (letI := ((a ≫ f).residueFieldMap x').hom.toAlgebra
      Module.finrank (S.residueField ((a ≫ f) x')) (X'.residueField x')) := by
    letI := (f.residueFieldMap (a x')).hom.toAlgebra
    letI := ((a ≫ f).residueFieldMap x').hom.toAlgebra
    refine Algebra.finrank_eq_of_equiv_equiv
      (RingEquiv.refl _ : S.residueField (f (a x')) ≃+* S.residueField ((a ≫ f) x'))
      (RingEquiv.ofBijective (a.residueFieldMap x').hom ha) ?_
    ext c
    show ((a ≫ f).residueFieldMap x').hom c = (a.residueFieldMap x').hom
      ((f.residueFieldMap (a x')).hom c)
    rw [Scheme.residueFieldMap_comp]
    rfl
  have h2 : residueDegree' f' x' =
      (letI := ((f' ≫ b).residueFieldMap x').hom.toAlgebra
      Module.finrank (S.residueField ((f' ≫ b) x')) (X'.residueField x')) := by
    letI := (f'.residueFieldMap x').hom.toAlgebra
    letI := ((f' ≫ b).residueFieldMap x').hom.toAlgebra
    refine (Algebra.finrank_eq_of_equiv_equiv
      (RingEquiv.ofBijective (b.residueFieldMap (f' x')).hom hb :
        S.residueField ((f' ≫ b) x') ≃+* S'.residueField (f' x'))
      (RingEquiv.refl _) ?_).symm
    ext c
    show (f'.residueFieldMap x').hom ((b.residueFieldMap (f' x')).hom c) =
      ((f' ≫ b).residueFieldMap x').hom c
    rw [Scheme.residueFieldMap_comp]
    rfl
  rw [h1, h2, h]

/-- A closed immersion induces isomorphisms of residue fields. -/
private theorem bijective_residueFieldMap_of_isClosedImmersion' {X Z : Scheme.{0}} (i : Z ⟶ X)
    [IsClosedImmersion i] (z : Z) : Function.Bijective (i.residueFieldMap z).hom := by
  refine ⟨(i.residueFieldMap z).hom.injective, fun c => ?_⟩
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨a, rfl⟩ := i.stalkMap_surjective z b
  refine ⟨X.residue (i z) a, ?_⟩
  exact congrArg (fun φ => φ.hom a) (Scheme.residue_residueFieldMap i z)

/-- The residue degree of a finite morphism is at least one. -/
private theorem one_le_residueDegree' {X S : Scheme.{0}} (f : X ⟶ S) [IsFinite f] (x : X) :
    1 ≤ residueDegree' f x := by
  have : IsFinite (f.fiberToSpecResidueField (f x)) := MorphismProperty.of_isPullback
    (P := @IsFinite) (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))) ‹IsFinite f›
  rw [← finrank_residueField_fiber_eq' f rfl (f.asFiber x) (f.fiberι_asFiber x)]
  letI : Algebra (S.residueField (f x)) ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    (((f.fiber (f x)).presheaf.germ ⊤ (f.asFiber x) (by simp)).hom.comp
      ((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop).hom).toAlgebra
  have hfs := @finite_stalk_of_isFinite_over_field (S.residueField (f x)) _ _
    (f.fiberToSpecResidueField (f x)) ‹_› (f.asFiber x)
  have : Module.Finite (S.residueField (f x))
      (IsLocalRing.ResidueField ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :=
    Module.Finite.of_surjective
      (IsScalarTower.toAlgHom (S.residueField (f x)) _ _).toLinearMap
      IsLocalRing.residue_surjective
  exact Module.finrank_pos

/-- **Residue degrees through a finite flat double cover.** Let `p : D' ⟶ D` be finite flat of
rank `2` at `s`, embedded by closed immersions `ι' : D' ⟶ X`, `ι : D ⟶ S` over `μ : X ⟶ S`,
with every point of `X` over `ι s` in the image of `ι'`. Then the residue degrees of `μ` at
distinct points over `ι s` sum to at most `2`. -/
private theorem sum_residueDegree_le_two_of_closedImmersion {X S D D' : Scheme.{0}}
    (μ : X ⟶ S) (p : D' ⟶ D) [IsFinite p] [Flat p] (ι' : D' ⟶ X) (ι : D ⟶ S)
    [IsClosedImmersion ι'] [IsClosedImmersion ι] (hsq : p ≫ ι = ι' ≫ μ) (s : D)
    (hrk : p.finrank s = 2) (hcov : ∀ y : X, μ y = ι s → y ∈ Set.range ι'.base)
    (G : Finset X) (hG : ∀ y ∈ G, μ y = ι s) :
    ∑ y ∈ G, residueDegree' μ y ≤ 2 := by
  classical
  rcases isEmpty_or_nonempty D' with hD' | hD'
  · have : G = ∅ := Finset.eq_empty_of_forall_notMem fun y hy => by
      obtain ⟨w, -⟩ := hcov y (hG y hy)
      exact hD'.false w
    subst this
    simp
  choose! z hz using hcov
  have hzs : ∀ y ∈ G, p (z y) = s := fun y hy => by
    apply ι.isEmbedding.injective
    have := congrArg (fun φ => φ.base (z y)) hsq
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
    rw [this, hz y (hG y hy), hG y hy]
  have hinj : Set.InjOn z G := fun y hy y' hy' hyy' => by
    rw [← hz y (hG y hy), ← hz y' (hG y' hy'), hyy']
  have hdeg : ∀ y ∈ G, residueDegree' μ y = residueDegree' p (z y) := fun y hy => by
    rw [residueDegree'_eq_of_comp_eq μ p ι' ι hsq.symm (z y)
      (bijective_residueFieldMap_of_isClosedImmersion' ι' (z y))
      (bijective_residueFieldMap_of_isClosedImmersion' ι (p (z y))), hz y (hG y hy)]
  calc ∑ y ∈ G, residueDegree' μ y = ∑ y ∈ G, residueDegree' p (z y) :=
        Finset.sum_congr rfl hdeg
    _ = ∑ w ∈ G.image z, residueDegree' p w := (Finset.sum_image hinj).symm
    _ ≤ p.finrank s := sum_residueDegree_le_finrank p s _ fun w hw => by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
        exact hzs y hy
    _ = 2 := hrk

/-- **Residue degrees of the normalization of a semismooth scheme.** Over a singular point `q`
of a semismooth `n`-fold, the residue degrees of the normalization at distinct points sum to at
most `2`. -/
private theorem sum_residueDegree_normalization_le_two {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {n : ℕ} (h : IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) (q : X)
    (hq : q ∉ smoothLocus sX)
    (G : Finset (Stacks.AlgebraicGeometry.Normalization.normalizationScheme X hX))
    (hG : ∀ y ∈ G, Stacks.AlgebraicGeometry.Normalization.normalization X hX y = q) :
    ∑ y ∈ G, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization X hX) y ≤ 2 := by
  obtain ⟨hfin, hflat, hrk⟩ := h.isFinite_flat_finrank_subschemeMap_normalization hX
  set I := MMP.Resolution.reducedSingularLocus sX
  have hqI : q ∈ Set.range I.subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι, MMP.Resolution.support_reducedSingularLocus]
    exact hq
  obtain ⟨s, hs⟩ := hqI
  refine sum_residueDegree_le_two_of_closedImmersion _ _ _ _
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _) s (congrFun hrk s) ?_ G
    (fun y hy => (hG y hy).trans hs.symm)
  intro y hy
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Scheme.IdealSheafData.support_comap]
  show _ ∈ (I.support : Set X)
  rw [hy, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨s, rfl⟩

/-- An open immersion induces isomorphisms of residue fields. -/
private theorem bijective_residueFieldMap_of_isOpenImmersion' {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) : Function.Bijective (f.residueFieldMap x).hom :=
  ConcreteCategory.bijective_of_isIso _

/-- **Residue degrees of the normalization are read on an open subscheme.** If over the point
`q ∈ U` the residue degrees of the normalization of the open subscheme `U` sum to at most `2`,
so do those of the normalization of `T`. -/
private theorem sum_residueDegree_normalization_le_two_of_opens {T : Scheme.{0}}
    (hT : ∀ V : T.Opens, IsCompact (V : Set T) → (irreducibleComponents V).Finite)
    (U : T.Opens)
    (hU : ∀ V : U.toScheme.Opens, IsCompact (V : Set U.toScheme) →
      (irreducibleComponents V).Finite) (q : U.toScheme)
    (hbound : ∀ G : Finset (Stacks.AlgebraicGeometry.Normalization.normalizationScheme
        U.toScheme hU), (∀ y ∈ G, Stacks.AlgebraicGeometry.Normalization.normalization
        U.toScheme hU y = q) →
      ∑ y ∈ G, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization
        U.toScheme hU) y ≤ 2)
    (G : Finset (Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT))
    (hG : ∀ y ∈ G, Stacks.AlgebraicGeometry.Normalization.normalization T hT y = U.ι q) :
    ∑ y ∈ G, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization T hT) y ≤ 2 := by
  classical
  have hpb : IsPullback (normalizationSchemeMap U.ι hU hT)
      (Stacks.AlgebraicGeometry.Normalization.normalization U.toScheme hU)
      (Stacks.AlgebraicGeometry.Normalization.normalization T hT) U.ι :=
    isPullback_normalizationSchemeMap_of_etale U.ι hT
  have hν : IsOpenImmersion (normalizationSchemeMap U.ι hU hT) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip inferInstance
  have hlift : ∀ y : Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT,
      Stacks.AlgebraicGeometry.Normalization.normalization T hT y = U.ι q →
      ∃ y' : Stacks.AlgebraicGeometry.Normalization.normalizationScheme U.toScheme hU,
        normalizationSchemeMap U.ι hU hT y' = y ∧
        Stacks.AlgebraicGeometry.Normalization.normalization U.toScheme hU y' = q := by
    intro y hy
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f :=
      Stacks.AlgebraicGeometry.Normalization.normalization T hT) (g := U.ι) y q hy
    refine ⟨hpb.isoPullback.inv z, ?_, ?_⟩
    · exact (congrArg (fun φ => φ.base z) hpb.isoPullback_inv_fst).trans hz1
    · exact (congrArg (fun φ => φ.base z) hpb.isoPullback_inv_snd).trans hz2
  rcases isEmpty_or_nonempty
    (Stacks.AlgebraicGeometry.Normalization.normalizationScheme U.toScheme hU) with hE | hE
  · have : G = ∅ := Finset.eq_empty_of_forall_notMem fun y hy => by
      obtain ⟨y', -⟩ := hlift y (hG y hy)
      exact hE.false y'
    subst this
    simp
  choose! z hz1 hz2 using hlift
  have hinj : Set.InjOn z G := fun y hy y' hy' hyy' => by
    rw [← hz1 y (hG y hy), ← hz1 y' (hG y' hy'), hyy']
  have hdeg : ∀ y ∈ G, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization
      T hT) y = residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization
      U.toScheme hU) (z y) := fun y hy => by
    have e := residueDegree'_eq_of_comp_eq _ _ _ U.ι hpb.w (z y)
      (bijective_residueFieldMap_of_isOpenImmersion' (normalizationSchemeMap U.ι hU hT) (z y))
      (bijective_residueFieldMap_of_isOpenImmersion' U.ι _)
    rw [hz1 y (hG y hy)] at e
    exact e.symm
  calc ∑ y ∈ G, _ = ∑ y ∈ G, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization
        U.toScheme hU) (z y) := Finset.sum_congr rfl hdeg
    _ = ∑ w ∈ G.image z, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization
        U.toScheme hU) w := (Finset.sum_image hinj).symm
    _ ≤ 2 := hbound _ fun w hw => by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
        exact hz2 y (hG y hy)

/-- **The branches over a codimension-one double point.** The residue degrees over `κ(Q)` of
the points of the normalization components lying over a codimension-one point `Q` of the double
locus sum to at most `2`: away from a closed subset of codimension two `T` is semismooth, and
there the restriction of the normalization to the double locus is a double cover. -/
private theorem sum_residueDegree_branch_le_two {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) {Q : T}
    (hQ : Order.coheight Q = 1) (hQD : Q ∈ (doubleIntersectionLocus T : Set T))
    (F : Finset (Σ i, N.X i)) (hF : ∀ a ∈ F, (N.n a.1).base a.2 = Q) :
    ∑ a ∈ F, residueDegree' (N.n a.1) a.2 ≤ 2 := by
  classical
  obtain ⟨Z, hZ, hss⟩ := exists_isSemismooth_compl h.isNcInCodimOne
  set U : T.Opens := Z.compl with hUdef
  have hQU : Q ∈ U := fun hQZ => by
    have := (le_closedsCodimension_iff_le_coheight.mp hZ) Q hQZ
    rw [hQ] at this
    exact absurd this (by decide)
  obtain ⟨⟨h1, h2, h3⟩, -, -⟩ := h.isNFold
  have : IsNoetherian T := by
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
    have : CompactSpace T := (quasiCompact_iff_compactSpace sT).mp h3
    exact {}
  have hU : ∀ V : U.toScheme.Opens, IsCompact (V : Set U.toScheme) →
      (irreducibleComponents V).Finite := by
    have : TopologicalSpace.NoetherianSpace U.toScheme :=
      TopologicalSpace.NoetherianSpace.set (U : Set T)
    exact fun V _ => @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _ _
      (TopologicalSpace.NoetherianSpace.set (V : Set U.toScheme))
  set q : U.toScheme := ⟨Q, hQU⟩
  have hq : U.ι q = Q := rfl
  have hqs : q ∉ smoothLocus (U.ι ≫ sT) := by
    rw [mem_smoothLocus_ι_iff, hq]
    exact notMem_smoothLocus_of_mem_doubleIntersectionLocus hQD
  have hboundU := sum_residueDegree_normalization_le_two hss hU q hqs
  have hboundT := sum_residueDegree_normalization_le_two_of_opens hT U hU q hboundU
  obtain ⟨φ, hφ⟩ := N.exists_iso
  let e : (Σ i, N.X i) → Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT :=
    fun a => (Limits.Sigma.ι N.X a.1 ≫ φ.hom) a.2
  have hsq : ∀ i, (Limits.Sigma.ι N.X i ≫ φ.hom) ≫
      Stacks.AlgebraicGeometry.Normalization.normalization T hT = N.n i ≫ 𝟙 T := fun i => by
    rw [Category.assoc, show φ.hom ≫ Stacks.AlgebraicGeometry.Normalization.normalization T hT =
      Limits.Sigma.desc N.n from hφ, Limits.Sigma.ι_desc, Category.comp_id]
  have he : ∀ a ∈ F, Stacks.AlgebraicGeometry.Normalization.normalization T hT (e a) = U.ι q :=
    fun a ha => (congrArg (fun ψ => ψ.base a.2) (hsq a.1)).trans (hF a ha)
  have hinj : Set.InjOn e F := fun a _ b _ hab => by
    have h1 : (Limits.Sigma.ι N.X a.1) a.2 = (Limits.Sigma.ι N.X b.1) b.2 :=
      φ.hom.isOpenEmbedding.injective hab
    rwa [sigmaι_eq_iff] at h1
  have hdeg : ∀ a ∈ F, residueDegree' (N.n a.1) a.2 =
      residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization T hT) (e a) :=
    fun a _ => residueDegree'_eq_of_comp_eq _ _ _ (𝟙 T) (hsq a.1) a.2
      (bijective_residueFieldMap_of_isOpenImmersion' _ _)
      (by rw [Scheme.residueFieldMap_id]; exact Function.bijective_id)
  calc ∑ a ∈ F, residueDegree' (N.n a.1) a.2
      = ∑ a ∈ F, residueDegree' (Stacks.AlgebraicGeometry.Normalization.normalization T hT)
          (e a) := Finset.sum_congr rfl hdeg
    _ = ∑ y ∈ F.image e, residueDegree'
          (Stacks.AlgebraicGeometry.Normalization.normalization T hT) y :=
        (Finset.sum_image hinj).symm
    _ ≤ 2 := hboundT _ fun y hy => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
        exact he a ha

/-- The branch map at a point `x` is the residue field extension `κ(νᵢ x) → κ(x)` precomposed
with the residue map. -/
private theorem branchMap_apply_eq {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {i : N.ι} (x : N.X i)
    (a : T.presheaf.stalk ((N.n i).base x)) :
    branchMap N x rfl a = ((N.n i).residueFieldMap x).hom (T.residue _ a) := by
  have h := congrArg (fun φ => φ.hom a) (Scheme.residue_residueFieldMap (N.n i) x)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [h]
  simp only [branchMap, TopCat.Presheaf.stalkSpecializes_refl, RingHom.comp_apply]
  rfl

/-- **The branches over a double point** (double normal crossings in codimension one). Over a
codimension-one point `Q` of the double locus the normalization has either only branches with
residue field `κ(Q)`, or a single branch whose residue field is a quadratic extension of `κ(Q)`,
with an involution fixing exactly `κ(Q)`: the residue degrees over `Q` sum to at most `2`
(`sum_residueDegree_branch_le_two`), and a quadratic extension in characteristic zero is
Galois. -/
private theorem branchMap_surjective_or_exists_unique {k : Type} [Field k] [CharZero k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) (Q : T)
    (hQ : Order.coheight Q = 1) (hQD : Q ∈ (doubleIntersectionLocus T : Set T)) :
    (∀ i (x : N.X i) (hx : (N.n i).base x = Q), Function.Surjective (branchMap N x hx)) ∨
    ∃ (i₀ : N.ι) (x₀ : N.X i₀) (hx₀ : (N.n i₀).base x₀ = Q),
      (∀ i (x : N.X i), (N.n i).base x = Q → (⟨i, x⟩ : Σ i, N.X i) = ⟨i₀, x₀⟩) ∧
      ∃ τ : (N.X i₀).residueField x₀ ≃+* (N.X i₀).residueField x₀,
        (∀ a, τ (branchMap N x₀ hx₀ a) = branchMap N x₀ hx₀ a) ∧
        ∀ e, τ e = e → e ∈ (branchMap N x₀ hx₀).range := by
  classical
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  have hone : ∀ i (x : N.X i), 1 ≤ residueDegree' (N.n i) x := fun i x => by
    haveI := isFinite_normalizationComponent N i
    exact one_le_residueDegree' (N.n i) x
  have hle : ∀ i (x : N.X i), (N.n i).base x = Q → residueDegree' (N.n i) x ≤ 2 :=
    fun i x hx => by
      have := sum_residueDegree_branch_le_two h hQ hQD {⟨i, x⟩} (by simpa using hx)
      simpa using this
  by_cases hall : ∀ i (x : N.X i), (N.n i).base x = Q → residueDegree' (N.n i) x = 1
  · left
    intro i x hx
    subst hx
    intro c
    letI := ((N.n i).residueFieldMap x).hom.toAlgebra
    obtain ⟨b, hb⟩ := (finrank_eq_one_iff_of_nonzero' (1 : (N.X i).residueField x)
      one_ne_zero).mp (hall i x rfl) c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective b
    refine ⟨a, ?_⟩
    rw [branchMap_apply_eq, ← hb, Algebra.smul_def, mul_one, ← ha]
    rfl
  · right
    push Not at hall
    obtain ⟨i₀, x₀, hx₀, hd⟩ := hall
    have hd2 : residueDegree' (N.n i₀) x₀ = 2 := by
      have := hle i₀ x₀ hx₀; have := hone i₀ x₀; omega
    refine ⟨i₀, x₀, hx₀, fun i x hx => ?_, ?_⟩
    · by_contra hne
      have hsum := sum_residueDegree_branch_le_two h hQ hQD {⟨i, x⟩, ⟨i₀, x₀⟩}
        (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro a (rfl | rfl) <;> assumption)
      rw [Finset.sum_pair hne] at hsum
      dsimp only at hsum
      have := hone i x
      omega
    · subst hx₀
      letI := ((N.n i₀).residueFieldMap x₀).hom.toAlgebra
      let χ : k →+* T.residueField ((N.n i₀).base x₀) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sT.appTop ≫ T.Γevaluation _).hom
      haveI : CharZero (T.residueField ((N.n i₀).base x₀)) :=
        charZero_of_injective_ringHom χ.injective
      haveI : FiniteDimensional (T.residueField ((N.n i₀).base x₀)) ((N.X i₀).residueField x₀) :=
        Module.finite_of_finrank_pos (show 0 < residueDegree' (N.n i₀) x₀ by omega)
      haveI : Algebra.IsQuadraticExtension (T.residueField ((N.n i₀).base x₀))
          ((N.X i₀).residueField x₀) := { finrank_eq_two' := hd2 }
      have hcard := IsGalois.card_aut_eq_finrank (T.residueField ((N.n i₀).base x₀))
        ((N.X i₀).residueField x₀)
      have hcard2 : Nat.card ((N.X i₀).residueField x₀ ≃ₐ[T.residueField ((N.n i₀).base x₀)]
          (N.X i₀).residueField x₀) = 2 := hcard.trans hd2
      obtain ⟨τ, hτ1, hτ⟩ := (Nat.card_eq_two_iff' 1).mp hcard2
      refine ⟨τ.toRingEquiv, fun a => ?_, fun e he => ?_⟩
      · rw [branchMap_apply_eq]
        exact τ.commutes _
      · have hmem : e ∈ Set.range (algebraMap (T.residueField ((N.n i₀).base x₀))
            ((N.X i₀).residueField x₀)) := by
          refine (IsGalois.mem_range_algebraMap_iff_fixed e).mpr fun σ => ?_
          by_cases hσ : σ = 1
          · rw [hσ]; rfl
          · rwa [hτ σ hσ]
        obtain ⟨b, rfl⟩ := hmem
        obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective b
        refine ⟨a, ?_⟩
        rw [branchMap_apply_eq, ← ha]
        rfl

/-! ### Crepancy of the branch identifications -/

section CrepancyTools

open MMP.Threefold.Mori.Helpers MMP.Threefold.Mori.ModelIndependence
open scoped WithZero

/-- **Orders of pulled-back forms along a valuation.** Let `σ : k(X') ≅ k(X)` be a
`k`-isomorphism, `Γ` a prime divisor of `X` and `(Y, f, E)` a divisor over `X'` whose valuation
is `v_Γ ∘ σ`. Then `ord_Γ(σ^* τ) = ord_E(f^* τ)` for every rational form `τ` on `X'`. -/
private theorem ordForm_pluriformPullback_eq_ordPullback {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {n : ℕ} (hn' : topologicalKrullDim X' = n)
    (σ : FunctionFieldEquiv sX sX') (Γ : MMP.Mori.PrimeDivisor X) (D : DivisorOver k sX')
    (hv : ∀ g : X'.functionField, D.valuation g = Γ.divisorialValuation ((σ.toHom) g))
    {m : ℤ} (τ : RationalPluriForms sX' n m) :
    Γ.ordForm (pluriformPullback sX sX' σ.toHom n m τ) = D.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX') := D.isNormalVariety.1.toLocallyOfFiniteType
  let A := functionFieldAlgebra sX
  let A' := functionFieldAlgebra sX'
  let AY := functionFieldAlgebra (D.f ≫ sX')
  let Af := functionFieldMapAlgebra D.f
  have hT1 := isScalarTower_functionFieldMap sX' D.f
  have hb := D.isBirationalMorphism.functionFieldMap_bijective
  let F := RingEquiv.ofBijective _ hb
  let φ : D.Y.functionField →+* X.functionField := (σ.toHom).toRingHom.comp F.symm.toRingHom
  have hφ : ∀ g, φ (functionFieldMap D.f g) = (σ.toHom) g := fun g => by
    change (σ.toHom) (F.symm (F g)) = _
    rw [F.symm_apply_apply]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨g, rfl⟩ := σ.surjective z
    exact ⟨functionFieldMap D.f g, hφ g⟩
  have hval : ∀ y : D.Y.functionField,
      Γ.divisorialValuation (φ y) = D.E.divisorialValuation y := by
    intro y
    obtain ⟨g, rfl⟩ := hb.2 y
    rw [hφ g, ← hv g]
    rfl
  have hord : ∀ y : D.Y.functionField,
      X.ord (φ y) Γ.genericPoint = D.Y.ord y D.E.genericPoint := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [Scheme.ord_zero]
    · have hey : φ y ≠ 0 := (map_ne_zero φ).mpr hy
      have h1 := hval y
      rw [Γ.divisorialValuation_eq_exp_neg_ord hey, D.E.divisorialValuation_eq_exp_neg_ord hy,
        WithZero.exp_inj] at h1
      omega
  have h12 : ∀ a1 : D.E.localRing, ∃ a2 : Γ.localRing,
      algebraMap Γ.localRing X.functionField a2 =
        φ (algebraMap D.E.localRing D.Y.functionField a1) := by
    intro a1
    have : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField a1) ≤ 1 :=
      (D.E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    obtain ⟨a2, ha2⟩ := (Γ.divisorialValuation_le_one_iff _).mp this
    exact ⟨a2, ha2⟩
  have h21 : ∀ a2 : Γ.localRing, ∃ a1 : D.E.localRing,
      φ (algebraMap D.E.localRing D.Y.functionField a1) =
        algebraMap Γ.localRing X.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hφs (algebraMap Γ.localRing X.functionField a2)
    have : D.E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (Γ.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (D.E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ := exists_ringHom_bijective_of_range φ h12 h21
  have hd : (Algebra.trdeg k X'.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hn'
  have htr : Algebra.trdeg k X'.functionField = Algebra.trdeg k D.Y.functionField :=
    trdeg_functionField_eq_of_bijective sX' D.f hb
  have htrσ : Algebra.trdeg k X'.functionField = Algebra.trdeg k X.functionField :=
    AlgEquiv.trdeg_eq σ
  have hd1 : (Algebra.trdeg k D.Y.functionField).toNat = n := by rwa [← htr]
  letI := stalkAlgebra (D.f ≫ sX') D.E.genericPoint
  letI := stalkAlgebra sX Γ.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX') D.E.genericPoint
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  letI Aφ : Algebra D.Y.functionField X.functionField := φ.toAlgebra
  have hTφ : IsScalarTower k D.Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap k X.functionField c = φ (algebraMap k D.Y.functionField c)
    rw [IsScalarTower.algebraMap_apply k X'.functionField D.Y.functionField c]
    change _ = φ (functionFieldMap D.f (algebraMap k X'.functionField c))
    rw [hφ]
    exact ((σ.toHom).commutes c).symm
  letI : Algebra D.E.localRing Γ.localRing := ψ.toAlgebra
  letI : Algebra D.E.localRing X.functionField :=
    ((algebraMap Γ.localRing X.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k D.E.localRing Γ.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective Γ.localRing X.functionField
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      ← IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c]
    exact IsScalarTower.algebraMap_apply k D.Y.functionField X.functionField c
  have hS2 : IsScalarTower D.E.localRing Γ.localRing X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower D.E.localRing D.Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k D.E.localRing X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap Γ.localRing X.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing Γ.localRing c]
    rfl
  have : Algebra.EssFiniteType k D.Y.functionField :=
    essFiniteType_functionField (sX := D.f ≫ sX')
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX' D.f hb hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator (k := k) (K := D.Y.functionField)
    (K' := X.functionField) (htr.symm.trans htrσ) hd1
  have hω0φ : IsPullbackGenerator X.functionField
      (topFormsMap k X'.functionField D.Y.functionField n ω0) :=
    IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  obtain ⟨σE, hσE, h0σE⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX') hd1
  have hωT : IsPullbackGenerator X.functionField
      (topFormsMap k D.E.localRing D.Y.functionField n σE) :=
    IsPullbackGenerator.of_span hω1 (span_singleton_topFormsMap (nonZeroDivisors _) hσE) h0σE
  have key := ordAt_pullbackForms_eq (k := k) (K := D.Y.functionField) (K' := X.functionField)
    (A := D.E.localRing) (A' := Γ.localRing) (d := n) (m := m) hψb
    (v := fun y => D.Y.ord y D.E.genericPoint) (v' := fun y => X.ord y Γ.genericPoint)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => Γ.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => Γ.ord_algebraMap_of_isUnit ha)
    hord hσE hωT (pullbackForms (K' := D.Y.functionField) m τ)
  let Aσ : Algebra X'.functionField X.functionField := (σ.toHom).toRingHom.toAlgebra
  have tσ : @IsScalarTower k X'.functionField X.functionField _ Aσ.toSMul _ := by
    letI := Aσ; exact IsScalarTower.of_algebraMap_eq fun c => ((σ.toHom).commutes c).symm
  have t3 : @IsScalarTower X'.functionField D.Y.functionField X.functionField Af.toSMul
      Aφ.toSMul Aσ.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Af Aφ Aσ fun g => (hφ g).symm
  have hcomp := @pullbackForms_comp k _ n m X'.functionField D.Y.functionField
    X.functionField _ _ _ A' AY A Af Aφ Aσ hT1 hTφ tσ t3 ω0 hω0 hω0φ τ
  calc Γ.ordForm (pluriformPullback sX sX' σ.toHom n m τ)
      = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (@pullbackForms k _ X'.functionField X.functionField _ _ A' A Aσ tσ n m τ) := rfl
    _ = ordAt Γ.localRing (fun y => X.ord y Γ.genericPoint)
          (pullbackForms (K' := X.functionField) m
            (pullbackForms (K' := D.Y.functionField) m τ)) := by rw [hcomp]
    _ = D.ordPullback τ := key

/-- **Orders along divisors over two birational varieties.** Let `σ : k(X') ≅ k(X)` and let `D`,
`D'` be divisors over `X`, `X'` with `v_{D'} = v_D ∘ σ`. Then `ord_D(σ^* τ) = ord_{D'}(τ)` for
every rational form `τ` on `X'`. -/
private theorem ordPullback_pluriformPullback_eq {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') {n : ℕ} (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n)
    (σ : FunctionFieldEquiv sX sX') (D : DivisorOver k sX) (D' : DivisorOver k sX')
    (hv : ∀ g, D'.valuation g = D.valuation ((σ.toHom) g)) {m : ℤ}
    (τ : RationalPluriForms sX' n m) :
    D.ordPullback (pluriformPullback sX sX' σ.toHom n m τ) = D'.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  haveI := hX.1
  haveI := D.isNormalVariety.1
  have hnY : topologicalKrullDim D.Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (D.f ≫ sX)
      D.isBirationalMorphism).symm.trans hn
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra (D.f ≫ sX)
  let ep : FunctionFieldEquiv (D.f ≫ sX) sX :=
    functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
  let σ' : FunctionFieldEquiv (D.f ≫ sX) sX' := σ.trans ep
  have h1 : pullbackRationalPluriForms sX D.f (pluriformPullback sX sX' σ.toHom n m τ) =
      pluriformPullback (D.f ≫ sX) sX' σ'.toHom n m τ :=
    pluriformPullback_comp (sX := D.f ≫ sX) (sX' := sX) (sX'' := sX') hnY hn hn' m
      ep.toHom σ.toHom τ
  change D.E.ordForm (pullbackRationalPluriForms sX D.f _) = _
  rw [h1]
  refine ordForm_pluriformPullback_eq_ordPullback D.isNormalVariety hX' hn' σ' D.E D'
    (fun g => ?_) τ
  rw [hv]
  rfl

/-- The canonical morphism from the spectrum of a stalk to a scheme over a field, followed by the
structure morphism, is the spectrum of the structure map of the stalk. -/
private theorem fromSpecStalk_comp_eq' {k : Type} [Field k] {X : Scheme.{0}} (p : X)
    (sX : X ⟶ Spec (.of k)) :
    X.fromSpecStalk p ≫ sX = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)) := by
  have h1 : sX = X.toSpecΓ ≫ Spec.map sX.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [h1]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

/-- **Centres of valuations on a proper variety.** A valuation ring of the function field of an
integral scheme proper over `k`, containing `k`, dominates the local ring of some point. -/
private theorem exists_dominated_of_isProper {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (R : ValuationSubring X.functionField)
    (hk : ∀ c : k, (letI := functionFieldAlgebra sX; algebraMap k X.functionField c) ∈ R) :
    ∃ x : X, (∀ a : X.presheaf.stalk x, algebraMap _ X.functionField a ∈ R) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        algebraMap _ X.functionField a ∈ R.nonunits := by
  letI := functionFieldAlgebra sX
  let φk : k →+* R := (algebraMap k X.functionField).codRestrict R hk
  have hex : ValuativeCriterion.Existence sX := by
    have h : @IsProper _ _ sX := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq sX :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom φk)
      commSq := ⟨by
        rw [fromSpecStalk_comp_eq', ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
      X.fromSpecStalk (genericPoint X) := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let g := Scheme.stalkClosedPointTo l
  have hg : g ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
      X.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hga : ∀ a : X.presheaf.stalk x,
      algebraMap _ X.functionField a = ((g.hom a : R) : X.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hg).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hga]; exact (g.hom a).2
  · rw [hga]
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨(g.hom a).2, ?_⟩
    have : (⟨_, (g.hom a).2⟩ : R) = g.hom a := rfl
    rw [this]
    exact (IsLocalRing.mem_maximalIdeal _).2
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))

/-- **Transport of divisors over along a birational map.** Let `σ : k(X') ≅ k(X)` with `X'` a
proper normal variety. Every divisor `D` over `X` has a proper divisor `D'` over `X'` with
valuation `v_D ∘ σ`: its valuation ring dominates the local ring of a point of `X'` by the
valuative criterion. -/
private theorem exists_properDivisorOver_comap {k : Type} [Field k] {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    (hX' : IsNormalVariety k sX') [IsProper sX'] (σ : FunctionFieldEquiv sX sX')
    (D : DivisorOver k sX) :
    ∃ D' : ProperDivisorOver k sX', ∀ g, D'.valuation g = D.valuation ((σ.toHom) g) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  have := D.isIntegral
  set ξ : Valuation X'.functionField ℤᵐ⁰ := D.valuation.comap (σ.toHom : X'.functionField →+* _)
  have hξ : ∀ g, ξ g = D.valuation ((σ.toHom) g) := fun g => rfl
  set R := ξ.valuationSubring
  have hk : ∀ c : k, algebraMap k X'.functionField c ∈ R := fun c => by
    rw [Valuation.mem_valuationSubring_iff, hξ, AlgHom.commutes]
    set z := D.f D.E.genericPoint
    letI := stalkAlgebra sX z
    haveI := isScalarTower_stalk_functionField sX z
    rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk z) X.functionField c]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _
  obtain ⟨x, h1, h2⟩ := exists_dominated_of_isProper sX' R hk
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k sX' ξ := by
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    letI := functionFieldAlgebra (D.f ≫ sX)
    let eY := functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨σ.trans eY, ?_⟩
    ext t
    rfl
  haveI : AlgebraicGeometry.IsVariety k sX' := hX'.1
  obtain ⟨D', -, hv, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hdiv x
    (fun a => (Valuation.mem_valuationSubring_iff _ _).1 (h1 a))
    (fun a ha => by
      have hm := h2 a ha
      rw [ValuationSubring.mem_nonunits_iff] at hm
      exact (Valuation.IsEquiv.lt_one_iff_lt_one
        (Valuation.isEquiv_valuation_valuationSubring ξ)).2 hm)
  exact ⟨D', fun g => by rw [hv]; rfl⟩

/-- **Log discrepancies through a birational map with matching local generators**, one direction.
Let `σ : k(X') ≅ k(X)` with `X'` proper, and suppose that for every divisor `D` over `X` and every
divisor `D'` over `X'` with `v_{D'} = v_D ∘ σ` there are local generators `Ω`, `Ω'` of
`𝒪(m(K + B))`, `𝒪(m(K' + B'))` near the centres of `D`, `D'` with `σ^*Ω' = Ω`. Then every log
discrepancy of `(X, B)` along a valuation `v` is a log discrepancy of `(X', B')` along `v ∘ σ`:
both are `1 + ord_D(Ω)/m`. -/
private theorem hasLogDiscrepancy_comap_of_forall_generatesOn {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') [IsProper sX'] {e : ℕ} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX e) (hK' : K'.IsCanonicalDivisor sX' e) {B : QDivisor X}
    {B' : QDivisor X'} {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hC' : ((m : ℤ) • (Divisor.toQDivisor K' + B')).IsCartierDivisor)
    (σ : FunctionFieldEquiv sX sX')
    (H : ∀ (D : DivisorOver k sX) (D' : DivisorOver k sX'),
      (∀ g, D'.valuation g = D.valuation ((σ.toHom) g)) →
      ∃ (W : X.Opens) (W' : X'.Opens) (Ω : RationalPluriForms sX e m)
        (Ω' : RationalPluriForms sX' e m),
        D.f D.E.genericPoint ∈ W ∧ D'.f D'.E.genericPoint ∈ W' ∧ GeneratesOn B m W Ω ∧
        GeneratesOn B' m W' Ω' ∧ pluriformPullback sX sX' σ.toHom e m Ω' = Ω)
    (v : Valuation X.functionField ℤᵐ⁰) (a : ℝ) (h : HasLogDiscrepancy sX B v a) :
    HasLogDiscrepancy sX' B' (v.comap (σ.toHom : X'.functionField →+* X.functionField)) a := by
  haveI : PerfectField k := PerfectField.ofCharZero
  obtain ⟨n₀, D, rfl, hD⟩ := h
  have hn₀ : n₀ = e := by
    have := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD).symm.trans
      hK.topologicalKrullDim_eq
    exact_mod_cast this
  subst hn₀
  obtain ⟨D', hD'⟩ := exists_properDivisorOver_comap hX' σ D
  obtain ⟨W, W', Ω, Ω', hc, hc', hΩ, hΩ', hσΩ⟩ := H D D'.toDivisorOver hD'
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdisc : IsDiscrepancy sX n₀ K B D ((D.ordPullback Ω : ℚ) / m) :=
    ⟨hX, hK, m, hm, hC, W, hc, Ω, hΩ, by field_simp⟩
  have hdisc' : IsDiscrepancy sX' n₀ K' B' D'.toDivisorOver
      ((D'.toDivisorOver.ordPullback Ω' : ℚ) / m) :=
    ⟨hX', hK', m, hm, hC', W', hc', Ω', hΩ', by field_simp⟩
  have hn : topologicalKrullDim X = n₀ := hK.topologicalKrullDim_eq
  have hn' : topologicalKrullDim X' = n₀ := hK'.topologicalKrullDim_eq
  have hord : D.ordPullback Ω = D'.toDivisorOver.ordPullback Ω' := by
    rw [← hσΩ]
    exact ordPullback_pluriformPullback_eq hX hX' hn hn' σ D D'.toDivisorOver hD' Ω'
  have ha := ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hdisc a).mp hD).2
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hdisc' D'.isProper
  refine ⟨n₀, D'.toDivisorOver, ?_, ?_⟩
  · ext g
    exact hD' g
  · rw [ha, hord]
    exact hlog

/-- **Crepant birational maps from matching local generators.** Let `σ : k(X') ≅ k(X)` be a
birational map of proper normal pairs `(X, B)`, `(X', B')` of dimension `e` with `m(K + B)`,
`m(K' + B')` Cartier, such that near the centres of any two divisors `D` over `X` and `D'` over
`X'` with `v_{D'} = v_D ∘ σ` there are local generators `Ω`, `Ω'` with `σ^*Ω' = Ω`. Then `σ` is
crepant. -/
private theorem isCrepantBirationalMap_of_forall_generatesOn {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') [IsProper sX] [IsProper sX'] {e : ℕ} {K : Divisor X}
    {K' : Divisor X'} (hK : K.IsCanonicalDivisor sX e) (hK' : K'.IsCanonicalDivisor sX' e)
    {B : QDivisor X} {B' : QDivisor X'} {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hC' : ((m : ℤ) • (Divisor.toQDivisor K' + B')).IsCartierDivisor)
    (σ : FunctionFieldEquiv sX sX')
    (H : ∀ (D : DivisorOver k sX) (D' : DivisorOver k sX'),
      (∀ g, D'.valuation g = D.valuation ((σ.toHom) g)) →
      ∃ (W : X.Opens) (W' : X'.Opens) (Ω : RationalPluriForms sX e m)
        (Ω' : RationalPluriForms sX' e m),
        D.f D.E.genericPoint ∈ W ∧ D'.f D'.E.genericPoint ∈ W' ∧ GeneratesOn B m W Ω ∧
        GeneratesOn B' m W' Ω' ∧ pluriformPullback sX sX' σ.toHom e m Ω' = Ω) :
    IsCrepantBirationalMap sX sX' B B' σ := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sX'
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have hn : topologicalKrullDim X = e := hK.topologicalKrullDim_eq
  have hn' : topologicalKrullDim X' = e := hK'.topologicalKrullDim_eq
  -- the symmetric hypothesis for `σ⁻¹`
  have H' : ∀ (D' : DivisorOver k sX') (D : DivisorOver k sX),
      (∀ g, D.valuation g = D'.valuation (((FunctionFieldEquiv.toHom sX' sX σ.symm)) g)) →
      ∃ (W' : X'.Opens) (W : X.Opens) (Ω' : RationalPluriForms sX' e m)
        (Ω : RationalPluriForms sX e m),
        D'.f D'.E.genericPoint ∈ W' ∧ D.f D.E.genericPoint ∈ W ∧ GeneratesOn B' m W' Ω' ∧
        GeneratesOn B m W Ω ∧
          pluriformPullback sX' sX (FunctionFieldEquiv.toHom sX' sX σ.symm) e m Ω = Ω' := by
    intro D' D hv
    have hv' : ∀ g, D'.valuation g = D.valuation ((σ.toHom) g) := fun g => by
      rw [hv]
      congr 1
      exact (σ.symm_apply_apply g).symm
    obtain ⟨W, W', Ω, Ω', hc, hc', hΩ, hΩ', hσΩ⟩ := H D D' hv'
    refine ⟨W', W, Ω', Ω, hc', hc, hΩ', hΩ, ?_⟩
    rw [← hσΩ, pluriformPullback_comp hn' hn hn' (m : ℤ)
      (FunctionFieldEquiv.toHom sX' sX σ.symm) σ.toHom Ω']
    have h1 : (FunctionFieldEquiv.toHom sX' sX σ.symm).comp σ.toHom =
        (1 : FunctionFieldEquiv sX' sX').toHom := by
      ext g
      exact σ.symm_apply_apply g
    rw [h1, pluriformPullback_one hn' (m : ℤ) Ω']
  intro v a
  refine ⟨hasLogDiscrepancy_comap_of_forall_generatesOn hX hX' hK hK' hm hC hC' σ H v a,
    fun h => ?_⟩
  have := hasLogDiscrepancy_comap_of_forall_generatesOn hX' hX hK' hK hm hC' hC σ.symm H' _ a h
  convert this using 1
  ext g
  change v g = v (σ (σ.symm g))
  rw [σ.apply_symm_apply]

/-- Two nonzero rational `m`-canonical forms of top degree differ by a nonzero rational
function. -/
private theorem exists_smul_eq_of_ne_zero {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) {m : ℤ} {τ τ' : RationalPluriForms sX d m} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : ∃ f : X.functionField, f ≠ 0 ∧ τ = f • τ' := by
  letI := functionFieldAlgebra sX
  obtain ⟨b⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hd
  let bb := ZTensorPower.basis b m
  let v : RationalPluriForms sX d m := bb ()
  have e : ∀ σ : RationalPluriForms sX d m, σ = bb.repr σ () • v := fun σ => by
    conv_lhs => rw [← bb.sum_repr σ]
    simp only [Fintype.univ_unit, Finset.sum_singleton]
    rfl
  set c := bb.repr τ ()
  set c' := bb.repr τ' ()
  have e1 : τ = c • v := e τ
  have e2 : τ' = c' • v := e τ'
  have hc : c ≠ 0 := fun h => hτ (by rw [e1, h, zero_smul])
  have hc' : c' ≠ 0 := fun h => hτ' (by rw [e2, h, zero_smul])
  refine ⟨c / c', div_ne_zero hc hc', ?_⟩
  rwa [e2, smul_smul, div_mul_cancel₀ _ hc']

/-- **The residue of a local generator is a local generator.** Let `j : S ⟶ Y` be an adjunction
step of a pair `(Y, C)` with `m(K_Y + C)` Cartier, and `τ` a local generator of
`𝒪_Y(m(K_Y + C))` on an open `W` meeting `S`. Then its Poincaré residue generates
`𝒪_S(m(K_S + C_S))` on `j⁻¹W`, `C_S` the different: near every point of `S ∩ W` it is a unit
multiple of the residue of a generator whose residue generates. -/
private theorem generatesOn_of_isPoincareResidue {k : Type} [Field k] [CharZero k]
    {Y S : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y]
    [CompactSpace Y] [LocallyOfFiniteType sY] (hY : IsNormalVariety k sY) {n : ℕ}
    (hdim : topologicalKrullDim Y = n + 1) (hn : n ≠ 0) {C : QDivisor Y} {j : S ⟶ Y}
    {BS : QDivisor S} [IsIntegral S] [IsNormal S] [IsLocallyNoetherian S] [CompactSpace S]
    (hj : IsAdjunctionStep sY C j BS) (hdimS : topologicalKrullDim S = n) {m : ℕ} (hm : 0 < m)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor sY (n + 1))
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + C)).IsCartierDivisor) {W : Y.Opens}
    (hW : j (genericPoint S) ∈ W) {τ : RationalPluriForms sY (n + 1) m}
    (hτ : GeneratesOn C m W τ) {ρ : RationalPluriForms (j ≫ sY) n m}
    (hρ : IsPoincareResidue sY j n m τ ρ) :
    GeneratesOn BS m (j ⁻¹ᵁ W) ρ := by
  classical
  haveI : PerfectField k := PerfectField.ofCharZero
  obtain ⟨hT, P, -, hrange, hci, -⟩ := id hj
  haveI := hci
  have hjP : j (genericPoint S) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hrange
  haveI : LocallyOfFiniteType (j ≫ sY) := hT.1.toLocallyOfFiniteType
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimS hn
  obtain ⟨τ₁, hτ₁0, hτ₁P, -, ρ₁, hρ₁, hρ₁0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sY hY hdim j hT P hrange Q
  obtain ⟨φ, hφ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK (m := 1) hτ₁0
  rw [one_smul] at hφ
  have hlin : K.LinearlyEquivalent (divisorOfForm τ₁) := Divisor.LinearlyEquivalent.symm ⟨φ, hφ⟩
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hQC : (Divisor.toQDivisor (divisorOfForm τ₁) + C).IsQCartier :=
    (show (Divisor.toQDivisor K + C).IsQCartier from ⟨m, hm', hC⟩).add_of_linearlyEquivalent hlin
  have hpb0 := hj.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hrange τ₁ hτ₁0 hτ₁P
    ρ₁ hρ₁ hQC
  have hE : Divisor.toQDivisor (divisorOfForm τ₁) + Finsupp.single P 1 + (C - Finsupp.single P 1) =
      Divisor.toQDivisor (divisorOfForm τ₁) + C := by abel
  rw [← hE] at hpb0
  obtain ⟨hgen, hpb⟩ := hpb0
  obtain ⟨D, hD, hDc⟩ := hC
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  set DM : Divisor Y := D + ((M + 1 : ℕ) : ℤ) • Mori.principalDivisor φ with hDMdef
  have hDM : Divisor.toQDivisor DM = ((M + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm τ₁) + Finsupp.single P 1 + (C - Finsupp.single P 1)) := by
    rw [hE, hDMdef, map_add, hD, map_zsmul, ← hφ, map_sub, smul_add, smul_add, smul_sub]
    abel
  have hDMc : DM.IsCartier := hDc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)
  -- the local comparison
  have hd1 : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  have key : ∀ x : S, j x ∈ W → ∃ (U : Y.Opens) (ρ' : RationalPluriForms (j ≫ sY) n (M + 1 : ℕ))
      (u : S.presheaf.stalk x), j x ∈ U ∧ GeneratesOn BS (M + 1) (j ⁻¹ᵁ U) ρ' ∧ IsUnit u ∧
      ρ = (S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes trivial)).hom u • ρ' := by
    intro x hxW
    obtain ⟨U, hxU, τ', hτ', ρ', hρ', hρ'g⟩ :=
      MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sY hdim j hT hdimS P
        hrange (C - Finsupp.single P 1) τ₁ hτ₁0 ρ₁ hρ₁ hρ₁0 BS hgen hpb M DM hDM hDMc x
    have hCC : Finsupp.single P 1 + (C - Finsupp.single P 1) = C := by abel
    rw [hCC] at hτ'
    obtain ⟨f, hf0, hf⟩ := exists_smul_eq_of_ne_zero hd1 hτ.1 hτ'.1
    -- `f` has no zero or pole through `j x`
    have hordf : ∀ Γ : Mori.PrimeDivisor Y, j x ∈ Γ.support → Y.ord f Γ.genericPoint = 0 := by
      intro Γ hΓ
      have h1 := hτ.2 Γ ⟨j x, hΓ, hxW⟩
      have h2 := hτ'.2 Γ ⟨j x, hΓ, hxU⟩
      rw [hf, Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq Γ hd1 hf0 hτ'.1] at h1
      push_cast at h1 h2
      exact_mod_cast (by linarith : ((Y.ord f Γ.genericPoint : ℤ) : ℚ) = 0)
    obtain ⟨r, hr⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg (j x) hf0
      fun Γ hΓ => (hordf Γ hΓ).ge
    obtain ⟨r', hr'⟩ := exists_algebraMap_stalk_eq_of_forall_ord_nonneg (j x) (inv_ne_zero hf0)
      fun Γ hΓ => by
        have h11 := Scheme.ord_mul (x := Γ.genericPoint) (one_ne_zero (α := Y.functionField))
          (one_ne_zero (α := Y.functionField))
        rw [mul_one] at h11
        have hinv := Scheme.ord_mul (x := Γ.genericPoint) hf0 (inv_ne_zero hf0)
        rw [mul_inv_cancel₀ hf0, hordf Γ hΓ] at hinv
        omega
    have hru : IsUnit r := by
      refine isUnit_iff_exists_inv.mpr ⟨r', IsFractionRing.injective _ Y.functionField ?_⟩
      rw [map_mul, hr, hr', mul_inv_cancel₀ hf0, map_one]
    have hsp : j (genericPoint S) ⤳ j x :=
      j.base.hom.map_specializes ((genericPoint_spec S).specializes trivial)
    set b := (Y.presheaf.stalkSpecializes hsp).hom r
    have hb : algebraMap _ Y.functionField b = f := by
      rw [Mori.algebraMap_stalkSpecializes, hr]
    have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ' b
    rw [hb, ← hf] at hres
    have hρeq := MMP.Fourfold.IsPoincareResidue.unique hj hρ hres
    refine ⟨U, ρ', (j.stalkMap x).hom r, hxU, hρ'g, hru.map _, ?_⟩
    rw [hρeq]
    congr 1
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ _ r
  -- conclusion
  obtain ⟨U₀, ρ₀, u₀, -, hρ₀, hu₀, hρρ₀⟩ := key (genericPoint S) hW
  have hu₀' : (S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes trivial)).hom u₀
      ≠ 0 := (hu₀.map _).ne_zero
  refine ⟨by rw [hρρ₀]; exact smul_ne_zero hu₀' hρ₀.1, fun F hF => ?_⟩
  obtain ⟨x, hxF, hxW⟩ := hF
  obtain ⟨U, ρ', u, hxU, hρ'g, hu, hρρ'⟩ := key x hxW
  have hun : (S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes trivial)).hom u
      ≠ 0 := (hu.map _).ne_zero
  have hdS : topologicalKrullDim S = (n : WithBot ℕ∞) := hdimS
  have hFx : F.genericPoint ⤳ x := specializes_of_mem_support F hxF
  have hord0 : S.ord ((S.presheaf.stalkSpecializes
      ((genericPoint_spec S).specializes trivial)).hom u) F.genericPoint = 0 := by
    have e1 := Mori.algebraMap_stalkSpecializes hFx u
    have e2 : (S.presheaf.stalkSpecializes ((genericPoint_spec S).specializes trivial)).hom u =
        algebraMap (S.presheaf.stalk x) S.functionField u := rfl
    rw [e2, ← e1]
    exact F.ord_algebraMap_of_isUnit (hu.map _)
  rw [hρρ', Mori.PrimeDivisor.ordForm_smul_of_topologicalKrullDim_eq F hdS hun hρ'g.1, hord0,
    zero_add]
  exact hρ'g.2 F ⟨x, hxF, hxU⟩

/-- **A divisor with coefficient one is a stratum of length one.** A prime divisor `P` of a
component `X_l` of a residue-restriction system along which the boundary has coefficient at least
one is the image of an adjunction step `ι : T ⟶ X_l`, and `T` has dimension one less. -/
private theorem exists_adjunctionStep_of_one_le_coeff {k : Type} [Field k] {I : Type*}
    {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of k)} [∀ i, IsIntegral (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)] {B : ∀ i, QDivisor (X i)} {e m : ℕ}
    (R : ResidueRestriction sX B (e + 1) m) (l : I) (P : MMP.Mori.PrimeDivisor (X l))
    (hP : 1 ≤ (B l).coeff P) :
    ∃ (T : Scheme.{0}) (ι : T ⟶ X l) (BT : QDivisor T) (h : MMP.Mori.IsPair (sX l) (B l))
      (_ : IsAdjunctionStep (𝟙 (X l) ≫ sX l) (B l) ι BT),
      Set.range ι.base = (P.support : Set (X l)) ∧ topologicalKrullDim T = e := by
  have hPl := R.setting.isPair l
  haveI := hPl.isAlgClosed
  haveI := hPl.charZero
  haveI : PerfectField k := PerfectField.ofCharZero
  have hX := hPl.isPair.isNormalVariety
  haveI : LocallyOfFiniteType (sX l) := hX.1.toLocallyOfFiniteType
  have hinter : (⋂ Q ∈ ({P} : Finset (MMP.Mori.PrimeDivisor (X l))), (Q.support : Set (X l))) =
      P.support := by simp
  have hS : IsDltStratum (sX l) (B l) (P.support : Set (X l)) := by
    refine ⟨R.setting.isDltPair l, {P}, Finset.singleton_nonempty _, by simpa using hP, ?_, ?_⟩
    · rw [hinter]
      exact ⟨P.genericPoint, by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
    · rw [hinter]
      refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
  obtain ⟨T, ι, BT, hrange, ⟨F⟩⟩ := hS.exists_isStratumAdjunctionPair_and_isDltPair.1.1
  haveI := F.isIntegral_stratum
  haveI : IsClosedImmersion ι := F.isClosedImmersion
  haveI : LocallyOfFiniteType (ι ≫ sX l) := F.isNormalVariety.1.toLocallyOfFiniteType
  have hdim : topologicalKrullDim T = e := by
    have h1 := trdeg_add_one_of_eq_genericPoint (sY := sX l) P
      (MMP.CyclicChartDifferent.Aux.map_genericPoint_eq ι P hrange)
    have h2 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX l)
      (R.setting.topologicalKrullDim_eq l)
    rw [topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX l)]
    congr 1
    omega
  have hlen := StratumAdjunctionData.dim_add_length (R.setting.topologicalKrullDim_eq l) F hdim
  cases F with
  | refl h₀ =>
    exfalso
    have h1 : genericPoint (X l) ∈ Set.range (𝟙 (X l) : X l ⟶ X l).base := ⟨_, rfl⟩
    rw [hrange] at h1
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support P h1
  | step F' j BT' hj =>
    cases F' with
    | step F₃ _ _ _ =>
      simp only [StratumAdjunctionData.length] at hlen
      omega
    | refl h' =>
      refine ⟨_, j, BT, h', hj, ?_, ?_⟩
      · rw [← hrange]; rfl
      · exact hdim

/-- **The residue field of a branch is the function field of its stratum.** Let `p : Y ⟶ X` be
an isomorphism on the local rings at `j(η_S)`, for an integral closed subscheme `j : S ⟶ Y`. Then
`κ(p(j(η_S))) ≅ k(S)` through the stalk maps. -/
private theorem exists_residueField_ringEquiv_functionField {X Y S : Scheme.{0}} [IsIntegral S]
    (p : Y ⟶ X) (j : S ⟶ Y) [IsClosedImmersion j] (hiso : IsIso (p.stalkMap (j (genericPoint S)))) :
    ∃ E : X.residueField (p (j (genericPoint S))) ≃+* S.functionField,
      ∀ a : X.presheaf.stalk (p (j (genericPoint S))), E (X.residue _ a) =
        (j.stalkMap (genericPoint S)).hom ((p.stalkMap (j (genericPoint S))).hom a) := by
  let ψ : X.presheaf.stalk (p (j (genericPoint S))) →+* S.functionField :=
    (j.stalkMap (genericPoint S)).hom.comp (p.stalkMap (j (genericPoint S))).hom
  have hψ : Function.Surjective ψ :=
    (j.stalkMap_surjective (genericPoint S)).comp (ConcreteCategory.bijective_of_isIso _).2
  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
  refine ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ),
    fun a => ?_⟩
  change (RingHom.quotientKerEquivOfSurjective hψ) ((Ideal.quotEquivOfEq hker.symm)
    (Ideal.Quotient.mk _ a)) = ψ a
  rw [Ideal.quotEquivOfEq_mk]
  rfl

/-- `φ^*(c w^{⊗a}) = φ(c) (φ^*w)^{⊗a}` for every `d`-form `w`, on varieties of dimension `d`. -/
private theorem pluriformPullback_smul_formPow'' {k : Type} [Field k] {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] [CharZero k] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX')
    (w : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k])
    (a : ℕ) (c : X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    pluriformPullback sX sX' φ d a (c • formPow w a) =
      φ c • formPow (topFormsMap k X'.functionField X.functionField d w) a := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_functionFieldHom hX hX' φ
    have e1 : (formPow w 0 : PluriForms k X'.functionField d (0 : ℕ)) = formPow ω 0 := by
      unfold formPow; congr 1; funext i; exact i.elim0
    have e2 : (formPow (topFormsMap k X'.functionField X.functionField d w) 0 :
        PluriForms k X.functionField d (0 : ℕ)) =
        formPow (topFormsMap k X'.functionField X.functionField d ω) 0 := by
      unfold formPow; congr 1; funext i; exact i.elim0
    rw [e1, e2]
    exact pluriformPullback_smul_formPow φ hω 0 c
  by_cases hw : w = 0
  · have h0 : ∀ {K : Type} [Field K] [Algebra k K],
        (formPow (0 : ⋀[K]^d Ω[K⁄k]) a : PluriForms k K d a) = 0 := by
      intro K _ _
      unfold formPow
      exact (PiTensorProduct.tprod K).map_coord_zero ⟨0, ha⟩ rfl
    subst hw
    rw [map_zero (topFormsMap k X'.functionField X.functionField d), h0, h0, smul_zero, smul_zero]
    exact map_zero (pluriformPullback sX sX' φ d a)
  · obtain ⟨b⟩ := exists_basis_topForms (sX := sX') hX'
    have hspan : Submodule.span X'.functionField {w} = ⊤ := by
      have hc : b.repr w () ≠ 0 := by
        intro h
        apply hw
        rw [← b.sum_repr w]
        simp [h]
      obtain ⟨r, hr⟩ : ∃ r, r = b.repr w () := ⟨_, rfl⟩
      rw [← hr] at hc
      refine Submodule.eq_top_iff'.mpr fun x => Submodule.mem_span_singleton.mpr
        ⟨b.repr x () / r, ?_⟩
      have hx : x = b.repr x () • b () := by
        conv_lhs => rw [← b.sum_repr x]
        simp
      have hw' : w = r • b () := by
        conv_lhs => rw [← b.sum_repr w]
        simp [hr]
      rw [hw', smul_smul, div_mul_cancel₀ _ hc, ← hx]
    exact pluriformPullback_smul_formPow φ
      (isPullbackGenerator_functionFieldHom hX hX' φ hspan hw) a c

/-- The image of `c • ιMulti (D ∘ v)` under `φ^*`. -/
private theorem topFormsMap_smul_ιMulti_D' {k : Type} [Field k] {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X'] (φ : FunctionFieldHom sX sX') {d : ℕ}
    (c : X'.functionField) (v : Fin d → X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    topFormsMap k X'.functionField X.functionField d
        (c • exteriorPower.ιMulti X'.functionField d
          fun i => KaehlerDifferential.D k X'.functionField (v i)) =
      φ c • exteriorPower.ιMulti X.functionField d
          fun i => KaehlerDifferential.D k X.functionField (φ (v i)) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  rw [LinearMap.map_smul, topFormsMap_ιMulti, algebra_compatible_smul X.functionField c]
  simp only [KaehlerDifferential.map_D]
  rfl

/-- The logarithmic top form `z⁻¹ dz ∧ db₁ ∧ ⋯ ∧ db_e`, written with its first factor split off. -/
private theorem ιMulti_dite_eq_smul {k K : Type*} [Field k] [Field K] [Algebra k K] {e : ℕ}
    (z : K) (b : Fin e → K) :
    exteriorPower.ιMulti K (e + 1) (fun l : Fin (e + 1) =>
        if hl : l.val = 0 then z⁻¹ • KaehlerDifferential.D k K z
        else KaehlerDifferential.D k K (b ⟨l.val - 1, by omega⟩)) =
      z⁻¹ • exteriorPower.ιMulti K (e + 1)
        (Fin.cons (KaehlerDifferential.D k K z) fun i => KaehlerDifferential.D k K (b i)) := by
  have h : (fun l : Fin (e + 1) =>
      if hl : l.val = 0 then z⁻¹ • KaehlerDifferential.D k K z
      else KaehlerDifferential.D k K (b ⟨l.val - 1, by omega⟩)) =
      Function.update (Fin.cons (KaehlerDifferential.D k K z)
        fun i => KaehlerDifferential.D k K (b i) : Fin (e + 1) → Ω[K⁄k]) 0
        (z⁻¹ • KaehlerDifferential.D k K z) := by
    funext l
    refine Fin.cases ?_ (fun i => ?_) l
    · simp
    · have hi : (Fin.succ i).val ≠ 0 := by simp
      rw [dif_neg hi, Function.update_of_ne (Fin.succ_ne_zero i), Fin.cons_succ]
      congr 2
  rw [h, AlternatingMap.map_update_smul]
  congr 2
  exact Function.update_eq_self 0 _

/-- **The residue of a presented form along a strict transform.** Let `p : Y ⟶ X` be birational,
an isomorphism on the local rings at the generic point `j(η_S)` of an integral closed subscheme
`j : S ⟶ Y`, preserving orders there. If `τ = h (dz/z ∧ da₁ ∧ ⋯ ∧ da_e)^{⊗m}` on `X` with
`ord z = 1` at `p(j(η_S))`, then the Poincaré residue of `p^*τ` along `S` is
`h̄ (dā₁ ∧ ⋯ ∧ dā_e)^{⊗m}`. -/
private theorem isPoincareResidue_pullback_of_presentation {k : Type} [Field k] [CharZero k]
    {X Y S : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral S] (p : Y ⟶ X) [IsDominant p] (j : S ⟶ Y)
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (p ≫ sX)] {e m : ℕ}
    (hX : topologicalKrullDim X = (e + 1 : ℕ)) (hY : topologicalKrullDim Y = (e + 1 : ℕ))
    (hb : Function.Bijective (functionFieldMap p))
    (hord : ∀ f, Y.ord (functionFieldMap p f) (j (genericPoint S)) =
      X.ord f (p (j (genericPoint S))))
    (z h : X.presheaf.stalk (p (j (genericPoint S))))
    (hz : X.ord (algebraMap _ X.functionField z) (p (j (genericPoint S))) = 1)
    (a : Fin e → X.presheaf.stalk (p (j (genericPoint S))))
    (τ : RationalPluriForms sX (e + 1) m)
    (hτ : letI := functionFieldAlgebra sX
      τ = algebraMap _ X.functionField h • (PiTensorProduct.tprod X.functionField
        (fun _ : Fin m => exteriorPower.ιMulti X.functionField (e + 1) (fun l : Fin (e + 1) =>
          if hl : l.val = 0 then (algebraMap _ X.functionField z)⁻¹ •
              KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField z)
          else KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (a ⟨l.val - 1, by omega⟩)))) :
        TensorPower X.functionField m (⋀[X.functionField]^(e + 1) Ω[X.functionField⁄k]))) :
    letI := functionFieldAlgebra (j ≫ p ≫ sX)
    IsPoincareResidue (p ≫ sX) j e m (pullbackRationalPluriForms sX p τ)
      ((j.stalkMap (genericPoint S)).hom ((p.stalkMap (j (genericPoint S))).hom h) •
        formPow (exteriorPower.ιMulti S.functionField e fun i =>
          KaehlerDifferential.D k S.functionField
            ((j.stalkMap (genericPoint S)).hom
              ((p.stalkMap (j (genericPoint S))).hom (a i)))) m) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (p ≫ sX)
  letI := functionFieldAlgebra (j ≫ p ≫ sX)
  let ep : FunctionFieldEquiv (p ≫ sX) sX := functionFieldAlgEquiv sX p hb
  have hpb : ∀ ω : RationalPluriForms sX (e + 1) m,
      pullbackRationalPluriForms sX p ω = pluriformPullback (p ≫ sX) sX ep.toHom (e + 1) m ω :=
    fun ω => rfl
  have hφ : ∀ a', (ep.toHom) a' = functionFieldMap p a' := fun a' => rfl
  refine ⟨(p.stalkMap (j (genericPoint S))).hom z, (p.stalkMap (j (genericPoint S))).hom h,
    fun i => (p.stalkMap (j (genericPoint S))).hom (a i), ?_, ?_, ?_⟩
  · rw [← functionFieldMap_algebraMap_stalk, hord, hz]
  · rw [hpb, hτ]
    have e1 := pluriformPullback_smul_formPow'' hY hX ep.toHom
      (exteriorPower.ιMulti X.functionField (e + 1) (fun l : Fin (e + 1) =>
          if hl : l.val = 0 then (algebraMap _ X.functionField z)⁻¹ •
              KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField z)
          else KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (a ⟨l.val - 1, by omega⟩)))) m
      (algebraMap _ X.functionField h)
    refine e1.trans ?_
    have hdite := ιMulti_dite_eq_smul (k := k) (algebraMap _ X.functionField z)
      (fun i => algebraMap _ X.functionField (a i))
    simp only at hdite
    rw [hdite]
    have hc : ∀ {K : Type} [Field K] [Algebra k K] (a₀ : K) (b : Fin e → K),
        (Fin.cons (KaehlerDifferential.D k K a₀) (fun i => KaehlerDifferential.D k K (b i)) :
          Fin (e + 1) → Ω[K⁄k]) =
          fun i => KaehlerDifferential.D k K ((Fin.cons a₀ b : Fin (e + 1) → K) i) := by
      intro K _ _ a₀ b
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    rw [hc, topFormsMap_smul_ιMulti_D', hc]
    simp only [hφ, map_inv₀, formPow, functionFieldMap_algebraMap_stalk]
    congr 4
    funext _
    congr 2
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [functionFieldMap_algebraMap_stalk]
  · rfl

/-- `σ^*(c (db₁ ∧ ⋯ ∧ db_e)^{⊗m}) = σ(c) (dσ(b₁) ∧ ⋯ ∧ dσ(b_e))^{⊗m}`. -/
private theorem pluriformPullback_smul_formPow_ιMulti {k : Type} [Field k] [CharZero k]
    {X X' : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X]
    [IsIntegral X'] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {e : ℕ}
    (hX : topologicalKrullDim X = e) (hX' : topologicalKrullDim X' = e)
    (σ : FunctionFieldHom sX sX') (m : ℕ) (c : X'.functionField) (b : Fin e → X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    pluriformPullback sX sX' σ e m (c • formPow (exteriorPower.ιMulti X'.functionField e
        fun i => KaehlerDifferential.D k X'.functionField (b i)) m) =
      σ c • formPow (exteriorPower.ιMulti X.functionField e
        fun i => KaehlerDifferential.D k X.functionField (σ (b i))) m := by
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  refine (pluriformPullback_smul_formPow'' hX hX' σ _ m c).trans ?_
  have e2 := topFormsMap_smul_ιMulti_D' σ 1 b
  rw [one_smul, map_one, one_smul] at e2
  rw [e2]

/-- A power of a nonzero rational top form is nonzero. -/
private theorem formPow_ne_zero {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {e : ℕ}
    (hX : topologicalKrullDim X = e)
    {ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^e Ω[X.functionField⁄k]} (hω : ω ≠ 0)
    (m : ℕ) : (letI := functionFieldAlgebra sX; formPow ω m : RationalPluriForms sX e m) ≠ 0 := by
  letI := functionFieldAlgebra sX
  obtain ⟨B⟩ := MMP.Fourfold.exists_basis_topForms (sX := sX) hX
  let b := basisOfSpanSingleton (MMP.Spreading.span_singleton_eq_top_of_basis_unit B hω) hω
  have hb : b () = ω := basisOfSpanSingleton_apply _ _ _
  rw [← hb, ← ZTensorPower.basis_natCast]
  exact (ZTensorPower.basis b m).ne_zero ()

/-- The empty wedge product is nonzero. -/
private theorem ιMulti_zero_ne_zero {k K : Type*} [Field k] [Field K] [Algebra k K]
    (v : Fin 0 → Ω[K⁄k]) : exteriorPower.ιMulti K 0 v ≠ 0 := by
  intro h
  have h1 := congrArg (fun w : ⋀[K]^0 Ω[K⁄k] => (w : ExteriorAlgebra K Ω[K⁄k])) h
  simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
    ZeroMemClass.coe_zero] at h1
  exact one_ne_zero h1

/-- The order along a local ring of a power of a top form with integral coefficients is
nonnegative. -/
private theorem ordAt_formPow_topFormsMap_nonneg {k A K : Type*} [CommRing k] [CommRing A]
    [Field K] [Algebra k A] [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]
    {d : ℕ} {v : K → ℤ} (hv : ∀ a : A, 0 ≤ v (algebraMap A K a)) (x : ⋀[A]^d Ω[A⁄k]) (m : ℕ) :
    0 ≤ ordAt (m := (m : ℤ)) A v (formPow (topFormsMap k A K d x) m) := by
  classical
  unfold ordAt
  split_ifs with h
  · obtain ⟨hσ, h0⟩ := h.choose_spec
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := x))
    rw [← ha, map_smul, ← algebraMap_smul K a, formPow_smul, formCoeff,
      ← topFormsBasis_apply hσ h0 (), repr_smul_formPow, ← map_pow]
    exact hv _
  · exact le_rfl

/-- The power of a top form `db₁ ∧ ⋯ ∧ db_d` with each `bᵢ` regular along `P` has nonnegative
order along `P`. -/
private theorem ordForm_formPow_ιMulti_D_nonneg {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (P : Mori.PrimeDivisor X) {d : ℕ} (b : Fin d → X.presheaf.stalk P.genericPoint) (m : ℕ) :
    letI := functionFieldAlgebra sX
    0 ≤ P.ordForm (sX := sX) (d := d) (m := m)
      (formPow (exteriorPower.ιMulti X.functionField d fun l =>
      KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (b l))) m :
        RationalPluriForms sX d m) := by
  letI := stalkAlgebra sX P.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX P.genericPoint
  have e1 : exteriorPower.ιMulti X.functionField d (fun l =>
      KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField (b l))) =
      topFormsMap k (X.presheaf.stalk P.genericPoint) X.functionField d
        (exteriorPower.ιMulti _ d fun l => KaehlerDifferential.D k _ (b l)) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext l
    rw [KaehlerDifferential.map_D]
  unfold PrimeDivisor.ordForm
  rw [e1]
  refine ordAt_formPow_topFormsMap_nonneg (fun a => ?_) _ m
  by_cases ha : algebraMap _ X.functionField a = 0
  · rw [ha, Scheme.ord_zero]; exact le_of_eq rfl
  exact (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord P.coheight_genericPoint ha).mp ⟨a, rfl⟩

/-- **A pole of full order along a divisor of a curve has a nonzero residue.** If a rational
`m`-canonical form `τ ≠ 0` on a normal curve has order `-m` along `P`, its Poincaré residue at
the point `S` lying over `P` is nonzero. -/
theorem isPoincareResidue_ne_zero_of_ordForm_eq {k : Type} [Field k] [PerfectField k]
    {Y S : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [LocallyOfFiniteType sY] (hY : topologicalKrullDim Y = (1 : ℕ)) {j : S ⟶ Y} [IsIntegral S]
    [LocallyOfFiniteType (j ≫ sY)] (hS : topologicalKrullDim S = (0 : ℕ))
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint S) = P.genericPoint) {m : ℕ}
    {τ : RationalPluriForms sY 1 m} (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -(m : ℤ))
    {ρ : RationalPluriForms (j ≫ sY) 0 m} (hρ : IsPoincareResidue sY j 0 m τ ρ) : ρ ≠ 0 := by
  classical
  letI := functionFieldAlgebra sY
  letI := functionFieldAlgebra (j ≫ sY)
  obtain ⟨t, g, x, ht, hτe, hρe⟩ := hρ
  have hy1 : Order.coheight (j (genericPoint S)) = 1 := by
    rw [hP]; exact P.coheight_genericPoint
  have htr : ∀ a : Y.presheaf.stalk (j (genericPoint S)),
      ∃ a' : Y.presheaf.stalk P.genericPoint,
        algebraMap _ Y.functionField a' = algebraMap _ Y.functionField a := by
    have key : ∀ y (_ : y = P.genericPoint) (a : Y.presheaf.stalk y),
        ∃ a' : Y.presheaf.stalk P.genericPoint,
          algebraMap _ Y.functionField a' = algebraMap _ Y.functionField a := by
      rintro _ rfl a; exact ⟨a, rfl⟩
    exact key _ hP
  obtain ⟨t', ht'⟩ := htr t
  set ω := exteriorPower.ιMulti Y.functionField 1 (fun _ : Fin 1 =>
    KaehlerDifferential.D k Y.functionField (algebraMap _ Y.functionField t')) with hωdef
  have hω : (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ _ t))
      fun i : Fin 0 => KaehlerDifferential.D k Y.functionField (algebraMap _ _ (x i))) =
      fun _ : Fin 1 => KaehlerDifferential.D k Y.functionField
        (algebraMap _ Y.functionField t') := by
    funext l
    rw [Fin.fin_one_eq_zero l, Fin.cons_zero, ht']
  have hτe' : τ = (algebraMap _ Y.functionField g * ((algebraMap _ Y.functionField t)⁻¹) ^ m) •
      (formPow ω m : RationalPluriForms sY 1 m) := by
    rw [hτe, mul_smul, ← formPow_smul, hωdef, ← hω]
    rfl
  have hg0 : algebraMap _ Y.functionField g ≠ 0 := by
    intro h; apply hτ0; rw [hτe, h, zero_smul]; rfl
  have ht0 : algebraMap _ Y.functionField t ≠ 0 := by
    intro h; rw [h, Scheme.ord_zero] at ht; exact zero_ne_one ht
  have hω0 : (formPow ω m : RationalPluriForms sY 1 m) ≠ 0 := by
    intro h; apply hτ0; rw [hτe', h, smul_zero]; rfl
  have hc0 : algebraMap _ Y.functionField g * ((algebraMap _ Y.functionField t)⁻¹) ^ m ≠ 0 :=
    mul_ne_zero hg0 (pow_ne_zero _ (inv_ne_zero ht0))
  have h1 : P.ordForm τ = Y.ord (algebraMap _ Y.functionField g *
      ((algebraMap _ Y.functionField t)⁻¹) ^ m) P.genericPoint +
        P.ordForm (sX := sY) (d := 1) (m := m) (formPow ω m) := by
    rw [hτe']
    exact P.ordForm_smul_of_topologicalKrullDim_eq (sX := sY) (d := 1) (m := m)
      (τ := (formPow ω m : RationalPluriForms sY 1 m)) hY hc0 hω0
  rw [hτ] at h1
  have h2 : 0 ≤ P.ordForm (sX := sY) (d := 1) (m := m) (formPow ω m) :=
    ordForm_formPow_ιMulti_D_nonneg P (fun _ => t') m
  have hgnn : 0 ≤ Y.ord (algebraMap _ Y.functionField g) (j (genericPoint S)) :=
    (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hy1 hg0).mp ⟨g, rfl⟩
  rw [inv_pow, ← zpow_natCast, ← zpow_neg, Scheme.ord_mul hg0 (zpow_ne_zero _ ht0),
    ord_zpow _ ht0, ← hP, ht]
    at h1
  have hg1 : Y.ord (algebraMap _ Y.functionField g) (j (genericPoint S)) = 0 := by
    push_cast at h1; linarith
  -- `g` is a unit of the local ring
  have hgi : (algebraMap _ Y.functionField g)⁻¹ ∈
      (algebraMap (Y.presheaf.stalk (j (genericPoint S))) Y.functionField).range := by
    refine (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord hy1 (inv_ne_zero hg0)).mpr ?_
    have := ord_zpow (j (genericPoint S)) hg0 (-1)
    rw [zpow_neg, zpow_one] at this
    rw [this, hg1, mul_zero]
  obtain ⟨u, hu⟩ := hgi
  have hgu : g * u = 1 := IsFractionRing.injective (Y.presheaf.stalk (j (genericPoint S)))
    Y.functionField (by rw [map_mul, hu, mul_inv_cancel₀ hg0, map_one])
  have hθ : (j.stalkMap (genericPoint S)).hom g ≠ 0 :=
    ((isUnit_iff_exists_inv.mpr ⟨u, hgu⟩).map (j.stalkMap (genericPoint S)).hom).ne_zero
  rw [hρe]
  exact smul_ne_zero hθ (formPow_ne_zero hS (ιMulti_zero_ne_zero (k := k) _) m)

/-- **Crepancy between points.** A normal variety of dimension zero carries no divisors over it,
so every isomorphism of function fields of two such varieties is crepant. -/
theorem isCrepantBirationalMap_of_topologicalKrullDim_eq_zero {k : Type} [Field k]
    {T T' : Scheme.{0}} {sT : T ⟶ Spec (.of k)} {sT' : T' ⟶ Spec (.of k)} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T']
    (hT : topologicalKrullDim T = 0) (hT' : topologicalKrullDim T' = 0) (B : QDivisor T)
    (B' : QDivisor T') (σ : FunctionFieldEquiv sT sT') :
    IsCrepantBirationalMap sT sT' B B' σ := by
  have key : ∀ {S : Scheme.{0}} {s : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S]
      [IsNormal S], topologicalKrullDim S = 0 → ∀ (C : QDivisor S) v a,
      ¬ HasLogDiscrepancy s C v a := by
    intro S s _ _ _ hS C v a h
    obtain ⟨n, D, -, hD⟩ := h
    obtain ⟨hSv, -⟩ := hD
    have := D.isIntegral
    haveI := hSv.1
    haveI := D.isNormalVariety.1
    have hY : topologicalKrullDim D.Y = 0 :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism s (D.f ≫ s)
        D.isBirationalMorphism).symm.trans hS
    have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim D.E.genericPoint
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hY] at h1
    exact absurd h1 (by decide)
  intro v a
  exact ⟨fun h => absurd h (key hT B v a), fun h => absurd h (key hT' B' _ a)⟩

/-- **Centres on a separated base through two models.** Let `π : S ⟶ T`, `π' : S' ⟶ T` map the
generic points of integral schemes `S`, `S'` to a common point of `T`, separated over `k`, and
`σ : k(S') ≅ k(S)` be compatible with the two maps on local rings at that point. For divisors
`D` over `S` and `D'` over `S'` with `v_{D'} = v_D ∘ σ`, the centres of `D` and `D'` have the
same image in `T`: both are the image of the closed point of the valuation ring. -/
private theorem map_center_eq_of_valuation_eq {k : Type} [Field k] {T S S' : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] [IsIntegral S] [IsIntegral S']
    {sS : S ⟶ Spec (.of k)} {sS' : S' ⟶ Spec (.of k)} (π : S ⟶ T) (π' : S' ⟶ T)
    (hπ' : π' (genericPoint S') ⤳ π (genericPoint S))
    (σ : S'.functionField ≃+* S.functionField)
    (hσ : ∀ a, σ ((π'.stalkMap (genericPoint S')).hom ((T.presheaf.stalkSpecializes hπ').hom a)) =
      (π.stalkMap (genericPoint S)).hom a)
    (D : DivisorOver k sS) (D' : DivisorOver k sS')
    (hv : ∀ g, D'.valuation g = D.valuation (σ g)) :
    π (D.f D.E.genericPoint) = π' (D'.f D'.E.genericPoint) := by
  set w := D.valuation
  set w' := D'.valuation
  obtain ⟨l, hl, hlc⟩ := MMP.Positivity.DivisorOver.exists_spec_valuationSubring_hom w
    (D.f D.E.genericPoint)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl)
  obtain ⟨l', hl', hlc'⟩ := MMP.Positivity.DivisorOver.exists_spec_valuationSubring_hom w'
    (D'.f D'.E.genericPoint)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D' _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D' _ rfl)
  let f : w'.valuationSubring →+* w.valuationSubring :=
    (σ.toRingHom.comp w'.valuationSubring.subtype).codRestrict w.valuationSubring fun g => by
    rw [Valuation.mem_valuationSubring_iff]
    change w (σ g) ≤ 1
    rw [← hv]
    exact (Valuation.mem_valuationSubring_iff _ _).1 g.2
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (σ.injective (congrArg Subtype.val hab)), fun c => ?_⟩
    refine ⟨⟨σ.symm c, ?_⟩, Subtype.ext ?_⟩
    · rw [Valuation.mem_valuationSubring_iff, hv, σ.apply_symm_apply]
      exact (Valuation.mem_valuationSubring_iff _ _).1 c.2
    · exact σ.apply_symm_apply c
  haveI : IsLocalHom f := ⟨fun a ha => by
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    obtain ⟨b', rfl⟩ := hf.2 b
    have : f (a * b') = f 1 := by rw [map_mul, hb, map_one]
    exact isUnit_iff_exists_inv.mpr ⟨b', hf.1 this⟩⟩
  let α := CommRingCat.ofHom (algebraMap w.valuationSubring S.functionField)
  let α' := CommRingCat.ofHom (algebraMap w'.valuationSubring S'.functionField)
  have hfα : CommRingCat.ofHom f ≫ α = α' ≫ CommRingCat.ofHom σ.toRingHom := by
    ext; rfl
  let L₁ : Spec (.of w.valuationSubring) ⟶ T := l ≫ π
  let L₂ : Spec (.of w.valuationSubring) ⟶ T := Spec.map (CommRingCat.ofHom f) ≫ l' ≫ π'
  have hgen : Spec.map α ≫ L₁ = Spec.map α ≫ L₂ := by
    have e1 : Spec.map α ≫ L₁ = Spec.map (π.stalkMap (genericPoint S)) ≫
        T.fromSpecStalk (π (genericPoint S)) := by
      rw [← Category.assoc, hl, Scheme.SpecMap_stalkMap_fromSpecStalk]
    have e2 : Spec.map α ≫ L₂ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (π'.stalkMap (genericPoint S')) ≫ T.fromSpecStalk (π' (genericPoint S')) := by
      change Spec.map α ≫ Spec.map (CommRingCat.ofHom f) ≫ l' ≫ π' = _
      rw [← Category.assoc, ← Spec.map_comp, hfα, Spec.map_comp, Category.assoc,
        ← Category.assoc (Spec.map α'), hl', Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [e1, e2, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hπ', ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a
    exact (hσ a).symm
  have key : ∀ g g' : Spec (.of w.valuationSubring) ⟶ Spec (.of k),
      Spec.map α ≫ g = Spec.map α ≫ g' → g = g' := by
    intro g g' h
    obtain ⟨p, rfl⟩ : ∃ p, Spec.map p = g := ⟨_, Spec.map_preimage g⟩
    obtain ⟨p', rfl⟩ : ∃ p, Spec.map p = g' := ⟨_, Spec.map_preimage g'⟩
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    have h' := Spec.map_injective h
    congr 1
    ext c
    exact congrArg (fun q => q.hom c) h'
  have hll : L₂ ≫ sT = L₁ ≫ sT := key _ _ (by
    have := congrArg (· ≫ sT) hgen.symm
    simpa only [Category.assoc] using this)
  let Sq : ValuativeCommSq sT :=
    { R := w.valuationSubring
      K := S.functionField
      i₁ := Spec.map α ≫ L₁
      i₂ := L₁ ≫ sT
      commSq := ⟨by rw [Category.assoc]⟩ }
  have hS := IsSeparated.valuativeCriterion sT Sq
  let Lf₁ : Sq.commSq.LiftStruct := ⟨L₁, rfl, rfl⟩
  let Lf₂ : Sq.commSq.LiftStruct := ⟨L₂, hgen.symm, hll⟩
  have hLL := congrArg CommSq.LiftStruct.l (Subsingleton.elim Lf₁ Lf₂)
  have h1 : L₁ (IsLocalRing.closedPoint w.valuationSubring) = π (D.f D.E.genericPoint) := by
    change π (l (IsLocalRing.closedPoint w.valuationSubring)) = _
    rw [hlc]
  have h2 : L₂ (IsLocalRing.closedPoint w.valuationSubring) = π' (D'.f D'.E.genericPoint) := by
    change π' (l' (Spec.map (CommRingCat.ofHom f) (IsLocalRing.closedPoint w.valuationSubring))) = _
    haveI : IsLocalHom (CommRingCat.ofHom f).hom := ‹IsLocalHom f›
    rw [Spec_closedPoint, hlc']
  rw [← h1, ← h2]
  exact congrArg (fun m : Spec (.of w.valuationSubring) ⟶ T =>
    m (IsLocalRing.closedPoint w.valuationSubring)) hLL

end CrepancyTools

/-- The generic point of a normalization component maps to a generic point of an irreducible
component of `T`: the normalization is birational. -/
private theorem isMax_base_genericPoint {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] (N : NormalizationComponents sT hT) (i : N.ι) :
    IsMax ((N.n i).base (genericPoint (N.X i))) := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  set e := Limits.Sigma.ι N.X i ≫ φ.hom with he
  have hmax : IsMax (e.base (genericPoint (N.X i))) := by
    intro y hy
    have hy' : y ⤳ e.base (genericPoint (N.X i)) := Scheme.le_iff_specializes.mp hy
    obtain ⟨u, rfl⟩ : y ∈ Set.range e.base :=
      hy'.mem_open e.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    have h1 : genericPoint (N.X i) ⤳ u := (genericPoint_spec (N.X i)).specializes (Set.mem_univ u)
    exact Scheme.le_iff_specializes.mpr (h1.map e.continuous)
  have hbir := Scheme.isBirational_normalization T hT
  have hgen := hbir.1.mapsTo (Stacks.Chow.mem_genericPoints_of_isMax hmax)
  have heq : (T.normalization hT).base (e.base (genericPoint (N.X i))) =
      (N.n i).base (genericPoint (N.X i)) := by
    have h1 : (e ≫ slcCurveNormalization T hT) = N.n i := by
      rw [he, Category.assoc, hφ, Limits.Sigma.ι_desc]
    rw [← h1]
    rfl
  rw [← heq]
  exact Stacks.Chow.isMax_of_mem_genericPoints ⟨_, hgen⟩

/-- A locally quasi-finite morphism has discrete fibres, so two points of a fibre one of which
specializes to the other are equal. -/
private theorem eq_of_specializes_of_base_eq {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {a b : X} (h : a ⤳ b) (hab : f.base a = f.base b) : a = b := by
  haveI := (f.isDiscrete_preimage_singleton (f.base b)).to_subtype
  have h' : (⟨a, hab⟩ : f.base ⁻¹' {f.base b}) ⤳ ⟨b, rfl⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

/-- **Points over a codimension-one point have codimension one.** A point of a normalization
component lying over a codimension-one point of `T` has codimension one: the finite map `νᵢ`
strictly preserves generization, and it maps the generic point of `Tᵢ` to a generic point. -/
private theorem coheight_eq_one_of_base_eq {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] [LocallyOfFiniteType sT] (N : NormalizationComponents sT hT) {i : N.ι}
    (x : N.X i) {Q : T} (hx : (N.n i).base x = Q) (hQ : Order.coheight Q = 1) :
    Order.coheight x = 1 := by
  haveI := isFinite_normalizationComponent N i
  have hmono : StrictMono (N.n i).base := by
    intro a b hab
    have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map (N.n i).continuous))
      fun hle => hab.not_ge ?_
    have h1 : (N.n i).base a ⤳ (N.n i).base b := Scheme.le_iff_specializes.mp hle
    have heq : (N.n i).base b = (N.n i).base a :=
      ((hba.map (N.n i).continuous).antisymm h1).eq
    rw [eq_of_specializes_of_base_eq (N.n i) hba heq]
  refine le_antisymm ((Order.coheight_le_coheight_apply_of_strictMono _ hmono x).trans_eq
    (hx ▸ hQ)) ?_
  rw [ENat.one_le_iff_ne_zero]
  intro h0
  have hmax : IsMax x := Order.coheight_eq_zero.mp h0
  have hxg : x = genericPoint (N.X i) := by
    have h1 : genericPoint (N.X i) ⤳ x := (genericPoint_spec (N.X i)).specializes (Set.mem_univ x)
    have h2 := hmax (Scheme.le_iff_specializes.mpr h1)
    exact (Scheme.le_iff_specializes.mp h2).antisymm h1 |>.eq
  have := isMax_base_genericPoint N i
  rw [← hxg, hx] at this
  rw [Order.coheight_eq_zero.mpr this] at hQ
  exact zero_ne_one hQ

/-- **The stratum of a branch.** Let `x ∈ Tᵢ` lie over a codimension-one point `Q` of the double
locus. The strict transform `Γ ⊆ Yᵢ` of the prime divisor `closure {x}` has coefficient one in
`Cᵢ`, so it is the image of an adjunction step `j : S ⟶ Yᵢ` of dimension one less; `pᵢ` is an
isomorphism of local rings at `j(η_S)`, preserving orders, with `pᵢ(j(η_S)) = x`. -/
private theorem exists_branchStratum {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {e : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N (e + 1) Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) (e + 1) K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C (e + 1) m)
    {U : T.Opens} {g : ∀ i, RationalPluriForms (N.n i ≫ sT) (e + 1) m}
    (hg : IsResidueGenerator N (e + 1) m Θ U g) {Q : T} (hQU : Q ∈ U)
    (hQ : Order.coheight Q = 1) (hQD : Q ∈ (doubleIntersectionLocus T : Set T)) {i : N.ι}
    (x : N.X i) (hx : (N.n i).base x = Q) :
    ∃ (S : Scheme.{0}) (j : S ⟶ Y i) (BS : QDivisor S)
      (_ : MMP.Mori.IsPair (p i ≫ N.n i ≫ sT) (C i))
      (hj : IsAdjunctionStep (𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT) (C i) j BS),
      haveI : IsIntegral S := hj.1.1.toIsIntegral
      topologicalKrullDim S = e ∧ (p i).base (j (genericPoint S)) = x ∧
      IsIso ((p i).stalkMap (j (genericPoint S))) ∧
      (∀ f, (Y i).ord (functionFieldMap (p i) f) (j (genericPoint S)) = (N.X i).ord f x) ∧
      ∃ Γ : Mori.PrimeDivisor (Y i), j (genericPoint S) = Γ.genericPoint ∧
        Γ.ordForm (pullbackRationalPluriForms (N.n i ≫ sT) (p i) (g i)) = -(m : ℤ) := by
  have hPi := R.setting.isPair i
  haveI := hPi.charZero
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  have hX := N.isNormalVariety i
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := hX.1.toLocallyOfFiniteType
  obtain ⟨K, hY, hp, hC⟩ := hcrep i
  haveI : IsProper (p i) := isProper_of_isProjectiveMorphism (p i) (hproj i)
  have hx1 := coheight_eq_one_of_base_eq N x hx hQ
  obtain ⟨Γ, hΓx, hΓiso, hΓord⟩ := exists_strictTransform hX (p i) hp x hx1
  set P : Mori.PrimeDivisor (N.X i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
  have hPx : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hx1
  have hxU : x ∈ N.n i ⁻¹ᵁ U := show (N.n i).base x ∈ U by rwa [hx]
  have hW : (p i).base Γ.genericPoint ∈ N.n i ⁻¹ᵁ U := by rwa [hΓx]
  have hordΓ := ordForm_pullback_eq_of_generatesOn (p i) hY hp hC Γ hW (hg.1.1 i)
  have hgP := (hg.1.1 i).2 P ⟨x, hPx ▸ MMP.Spreading.genericPoint_mem_support P, hxU⟩
  haveI := hX.1
  haveI := hY.1
  have hdimX : topologicalKrullDim (N.X i) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N.n i ≫ sT)
      (p i ≫ N.n i ≫ sT) hp).trans (R.setting.topologicalKrullDim_eq i)
  have hv : ∀ f, (⟨Y i, p i, hY, hp, Γ⟩ : DivisorOver k (N.n i ≫ sT)).valuation f =
      P.divisorialValuation (((1 : FunctionFieldEquiv (N.n i ≫ sT) (N.n i ≫ sT)).toHom) f) := by
    intro f
    change Γ.divisorialValuation (functionFieldMap (p i) f) = P.divisorialValuation f
    by_cases hf0 : f = 0
    · subst hf0; simp
    have hfY : functionFieldMap (p i) f ≠ 0 := (map_ne_zero _).mpr hf0
    rw [Γ.divisorialValuation_eq_exp_neg_ord hfY, P.divisorialValuation_eq_exp_neg_ord hf0,
      hΓord, hPx]
  have hrel := ordForm_pluriformPullback_eq_ordPullback hX hX hdimX
    (1 : FunctionFieldEquiv (N.n i ≫ sT) (N.n i ≫ sT)) P ⟨Y i, p i, hY, hp, Γ⟩ hv (g i)
  rw [pluriformPullback_one hdimX] at hrel
  change P.ordForm (g i) = Γ.ordForm (pullbackRationalPluriForms _ (p i) (g i)) at hrel
  have hΘ : (Θ i).coeff P = 1 := by
    rw [h.isAdjointBoundary i P]
    unfold adjointBoundaryCoeff
    rw [if_pos (by rwa [hPx, hx]), Finset.sum_eq_zero fun Γ' hΓ' => if_neg fun heq =>
      h.genericPoint_not_mem_doubleIntersectionLocus Γ' hΓ' (by rwa [← heq, hPx, hx])]
    simp
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast R.setting.pos.ne'
  have hCΓ : (C i).coeff Γ = 1 := by
    rw [hrel, hordΓ, hΘ] at hgP
    exact mul_left_cancel₀ hm0 (by linarith)
  obtain ⟨S, j, BS, hpair, hj, hrange, hdim⟩ :=
    exists_adjunctionStep_of_one_le_coeff R i Γ hCΓ.ge
  haveI : IsIntegral S := hj.1.1.toIsIntegral
  obtain ⟨-, -, -, -, hci, -⟩ := id hj
  haveI := hci
  have hjΓ : j (genericPoint S) = Γ.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j Γ hrange
  have hΓm : Γ.ordForm (pullbackRationalPluriForms (N.n i ≫ sT) (p i) (g i)) = -(m : ℤ) := by
    have h1 := hordΓ
    rw [hCΓ, mul_one] at h1
    exact_mod_cast h1
  exact ⟨S, j, BS, hpair, hj, hdim, by rwa [hjΓ], by rwa [hjΓ],
    fun f => by rw [hjΓ]; exact hΓord f, Γ, hjΓ, hΓm⟩

/-- The specialization map between the stalks at equal points is bijective. -/
private theorem bijective_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (hxy : x = y) : Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

/-- **The residue of a presented generator along a branch stratum.** If the residue of `τ` along
the prime divisor `P` of `Tᵢ` is presented as `ε ḡ (dā)^{⊗m}` by functions `a`, `g` on `T`, then
along the stratum `S` of the strict transform the residue of `pᵢ^*τ` is
`ε θ(ḡ) (dθ(ā))^{⊗m}`, `θ : 𝒪_{Tᵢ,P} → k(S)` the composite of the stalk maps. -/
private theorem isPoincareResidue_pullback_of_isLogResiduePresentation {k : Type} [Field k]
    [CharZero k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {e m : ℕ} {i : N.ι} {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsIntegral S] (p : Y ⟶ N.X i) [IsDominant p] (j : S ⟶ Y)
    [IsClosedImmersion j] [LocallyOfFiniteType (p ≫ N.n i ≫ sT)]
    (hX : topologicalKrullDim (N.X i) = (e + 1 : ℕ)) (hY : topologicalKrullDim Y = (e + 1 : ℕ))
    (hb : Function.Bijective (functionFieldMap p))
    (hiso : IsIso (p.stalkMap (j (genericPoint S))))
    (hord : ∀ f, Y.ord (functionFieldMap p f) (j (genericPoint S)) =
      (N.X i).ord f (p (j (genericPoint S))))
    (P : Mori.PrimeDivisor (N.X i)) (hsp : p (j (genericPoint S)) ⤳ P.genericPoint)
    (hq : p (j (genericPoint S)) = P.genericPoint) {V : T.Opens}
    (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (e + 1 - 1) → Γ(T, V)) (g' : Γ(T, V))
    (ε : ℤ) {τ : RationalPluriForms (N.n i ≫ sT) (e + 1) m}
    (hpres : IsLogResiduePresentation N (e + 1) m i P V hP a g' ε τ) :
    letI := functionFieldAlgebra (j ≫ p ≫ N.n i ≫ sT)
    let θ : (N.X i).presheaf.stalk P.genericPoint →+* S.functionField :=
      (j.stalkMap (genericPoint S)).hom.comp ((p.stalkMap (j (genericPoint S))).hom.comp
        ((N.X i).presheaf.stalkSpecializes hsp).hom)
    let pull : Γ(T, V) → (N.X i).presheaf.stalk P.genericPoint := fun f =>
      (N.X i).presheaf.germ ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V f)
    IsPoincareResidue (p ≫ N.n i ≫ sT) j e m
      (pullbackRationalPluriForms (N.n i ≫ sT) p τ)
      (((ε : S.functionField) * θ (pull g')) •
        formPow (exteriorPower.ιMulti S.functionField e fun l =>
          KaehlerDifferential.D k S.functionField (θ (pull (a l)))) m) := by
  intro θ pull
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
  letI := functionFieldAlgebra (N.n i ≫ sT)
  letI := functionFieldAlgebra (j ≫ p ≫ N.n i ≫ sT)
  obtain ⟨z, hh, hz1, hτ, -, hres⟩ := hpres
  set ψ := ((N.X i).presheaf.stalkSpecializes hsp).hom
  have hψ : ∀ b, algebraMap _ (N.X i).functionField (ψ b) =
      algebraMap _ (N.X i).functionField b := fun b => Mori.algebraMap_stalkSpecializes hsp b
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [Scheme.ord_zero] at hz1
    exact zero_ne_one hz1
  obtain ⟨z1, hz1'⟩ := (Scheme.mem_range_algebraMap_stalk_iff_zero_le_ord
    P.coheight_genericPoint hz0).mpr (by rw [hz1]; exact zero_le_one)
  have key := isPoincareResidue_pullback_of_presentation p j hX hY hb hord (ψ z1) (ψ hh)
    (by rw [hψ, hz1', hq]; exact hz1) (fun l => ψ (pull (a l))) τ (by
      rw [hτ]
      simp only [hψ, hz1']
      rfl)
  -- `θ` kills the maximal ideal
  have hθs : Function.Surjective θ := by
    intro c
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective (genericPoint S) c
    obtain ⟨b', rfl⟩ := (ConcreteCategory.bijective_of_isIso (p.stalkMap _)).2 b
    obtain ⟨b'', rfl⟩ := (bijective_stalkSpecializes_of_eq hsp hq).2 b'
    exact ⟨b'', rfl⟩
  have hker : RingHom.ker θ = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective θ hθs)
  have hθε : θ hh = (ε : S.functionField) * θ (pull g') := by
    have hm : hh - (ε : (N.X i).presheaf.stalk P.genericPoint) * pull g' ∈
        IsLocalRing.maximalIdeal _ := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_mul, map_intCast, sub_eq_zero]
      exact hres
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_intCast, sub_eq_zero] at hm
    exact hm
  convert key using 2
  · rw [← hθε]; rfl

/-- **The birational identification of two branch strata.** Let `S ⊆ Yᵢ`, `S' ⊆ Yⱼ` be integral
closed subschemes with `pᵢ`, `pⱼ` isomorphisms of local rings at their generic points, over the
points `x = pᵢ(η_S)`, `x' = pⱼ(η_{S'})` of the normalization over the same point of `T`, and
`σ : κ(x') ≅ κ(x)` compatible with the branch maps. Then `σ` is the restriction of a
`k`-isomorphism `σ_S : k(S') ≅ k(S)` compatible with the maps from the local ring of `T`. -/
private theorem exists_functionFieldEquiv_of_branchMap {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {i i' : N.ι} {Y Y' S S' : Scheme.{0}} [IsIntegral S]
    [IsIntegral S'] (p : Y ⟶ N.X i) (p' : Y' ⟶ N.X i') (j : S ⟶ Y) (j' : S' ⟶ Y')
    [IsClosedImmersion j] [IsClosedImmersion j']
    (hiso : IsIso (p.stalkMap (j (genericPoint S))))
    (hiso' : IsIso (p'.stalkMap (j' (genericPoint S'))))
    (hx' : (N.n i').base (p' (j' (genericPoint S'))) = (N.n i).base (p (j (genericPoint S))))
    (σ : (N.X i').residueField (p' (j' (genericPoint S'))) ≃+*
      (N.X i).residueField (p (j (genericPoint S))))
    (hσ : ∀ a, σ (branchMap N (p' (j' (genericPoint S'))) hx' a) =
      branchMap N (p (j (genericPoint S))) rfl a) :
    ∃ σS : FunctionFieldEquiv (j ≫ 𝟙 Y ≫ p ≫ N.n i ≫ sT) (j' ≫ 𝟙 Y' ≫ p' ≫ N.n i' ≫ sT),
      (∀ a, σS (((j' ≫ p' ≫ N.n i').stalkMap (genericPoint S')).hom
          ((T.presheaf.stalkSpecializes (show (N.n i').base (p' (j' (genericPoint S'))) ⤳
            (N.n i).base (p (j (genericPoint S))) by rw [hx'])).hom a)) =
        ((j ≫ p ≫ N.n i).stalkMap (genericPoint S)).hom a) ∧
      ∀ r r', σS ((j'.stalkMap (genericPoint S')).hom ((p'.stalkMap _).hom r')) =
          (j.stalkMap (genericPoint S)).hom ((p.stalkMap _).hom r) ↔
        σ ((N.X i').residue _ r') = (N.X i).residue _ r := by
  obtain ⟨E, hE⟩ := exists_residueField_ringEquiv_functionField p j hiso
  obtain ⟨E', hE'⟩ := exists_residueField_ringEquiv_functionField p' j' hiso'
  set hsp : (N.n i').base (p' (j' (genericPoint S'))) ⤳ (N.n i).base (p (j (genericPoint S))) :=
    (show (N.n i').base (p' (j' (genericPoint S'))) ⤳ (N.n i).base (p (j (genericPoint S))) by
      rw [hx'])
  let σ₀ : S'.functionField ≃+* S.functionField := (E'.symm.trans σ).trans E
  have hπ : ∀ a : T.presheaf.stalk ((N.n i).base (p (j (genericPoint S)))),
      ((j ≫ p ≫ N.n i).stalkMap (genericPoint S)).hom a =
      E (branchMap N (p (j (genericPoint S))) rfl a) := by
    intro a
    have e1 : ((j ≫ p ≫ N.n i).stalkMap (genericPoint S)).hom a =
        (j.stalkMap (genericPoint S)).hom ((p.stalkMap (j (genericPoint S))).hom
          (((N.n i).stalkMap (p (j (genericPoint S)))).hom a)) := by
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]; rfl
    rw [e1, ← hE]
    congr 1
    simp only [branchMap, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hπ' : ∀ a : T.presheaf.stalk ((N.n i).base (p (j (genericPoint S)))),
      ((j' ≫ p' ≫ N.n i').stalkMap (genericPoint S')).hom
        ((T.presheaf.stalkSpecializes hsp).hom a) =
      E' (branchMap N (p' (j' (genericPoint S'))) hx' a) := by
    intro a
    have e1 : ((j' ≫ p' ≫ N.n i').stalkMap (genericPoint S')).hom
        ((T.presheaf.stalkSpecializes hsp).hom a) =
        (j'.stalkMap (genericPoint S')).hom ((p'.stalkMap (j' (genericPoint S'))).hom
          (((N.n i').stalkMap (p' (j' (genericPoint S')))).hom
            ((T.presheaf.stalkSpecializes hsp).hom a))) := by
      rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]; rfl
    rw [e1, ← hE']
    rfl
  have hσ₀ : ∀ a : T.presheaf.stalk ((N.n i).base (p (j (genericPoint S)))),
      σ₀ (((j' ≫ p' ≫ N.n i').stalkMap (genericPoint S')).hom
      ((T.presheaf.stalkSpecializes hsp).hom a)) =
      ((j ≫ p ≫ N.n i).stalkMap (genericPoint S)).hom a := by
    intro a
    rw [hπ', hπ]
    simp only [σ₀, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, hσ]
  letI := functionFieldAlgebra (j ≫ 𝟙 Y ≫ p ≫ N.n i ≫ sT)
  letI := functionFieldAlgebra (j' ≫ 𝟙 Y' ≫ p' ≫ N.n i' ≫ sT)
  have hk : ∀ c : k, σ₀ (algebraMap k S'.functionField c) = algebraMap k S.functionField c := by
    intro c
    have h1 : algebraMap k S.functionField c =
        ((j ≫ p ≫ N.n i).stalkMap (genericPoint S)).hom
          (stalkStructureMap sT ((N.n i).base (p (j (genericPoint S)))) c) :=
      (stalkMap_stalkStructureMap (sX := sT) (j ≫ p ≫ N.n i) (genericPoint S) c).symm
    have h2 : algebraMap k S'.functionField c =
        ((j' ≫ p' ≫ N.n i').stalkMap (genericPoint S')).hom
          ((T.presheaf.stalkSpecializes hsp).hom
            (stalkStructureMap sT ((N.n i).base (p (j (genericPoint S)))) c)) := by
      rw [show (T.presheaf.stalkSpecializes hsp).hom
          (stalkStructureMap sT ((N.n i).base (p (j (genericPoint S)))) c) =
          stalkStructureMap sT ((N.n i').base (p' (j' (genericPoint S')))) c from
        TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _]
      exact (stalkMap_stalkStructureMap (sX := sT) (j' ≫ p' ≫ N.n i') (genericPoint S') c).symm
    rw [h1, h2, hσ₀]
  refine ⟨AlgEquiv.ofRingEquiv (f := σ₀) hk, hσ₀, fun r r' => ?_⟩
  change σ₀ _ = _ ↔ _
  rw [← hE', ← hE]
  simp only [σ₀, RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
  exact E.injective.eq_iff

/-- The value at the generic point of a branch stratum of the pull-back of a function on `T`. -/
private theorem stalkMap_comp_germ_eq {T X Y S : Scheme.{0}} (n : X ⟶ T) (p : Y ⟶ X)
    (j : S ⟶ Y) [IsIntegral S] (P : Mori.PrimeDivisor X)
    (hsp : p (j (genericPoint S)) ⤳ P.genericPoint) {V : T.Opens} (hP : n.base P.genericPoint ∈ V)
    (hV : n.base (p (j (genericPoint S))) ∈ V) (f : Γ(T, V)) :
    (j.stalkMap (genericPoint S)).hom ((p.stalkMap (j (genericPoint S))).hom
        ((X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ (n ⁻¹ᵁ V) P.genericPoint hP
          (n.app V f)))) =
      ((j ≫ p ≫ n).stalkMap (genericPoint S)).hom (T.presheaf.germ V _ hV f) := by
  have e1 : (X.presheaf.stalkSpecializes hsp).hom (X.presheaf.germ (n ⁻¹ᵁ V) P.genericPoint hP
      (n.app V f)) = X.presheaf.germ (n ⁻¹ᵁ V) (p (j (genericPoint S))) hV (n.app V f) :=
    TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [e1, ← Scheme.Hom.germ_stalkMap_apply n V _ hV f, Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_comp]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Residues of a local generator on two branch strata correspond.** Let `g` be a local
generator of `𝒪_T(mL)` on `U` (`m` even) whose residues along the conductor are presented by
functions on `T`, and let `S ⊆ Yᵢ`, `S' ⊆ Yⱼ` be the strata of the strict transforms of two
branches over a codimension-one point `Q ∈ U` of the double locus, with `σ_S : k(S') ≅ k(S)`
compatible with the maps from `𝒪_{T,Q}`. Then the residues `Ω`, `Ω'` of `pᵢ^*gᵢ`, `pⱼ^*gⱼ` along
`S`, `S'` satisfy `σ_S^*Ω' = Ω`: both are pulled back from the same form `ḡ (dā)^{⊗m}`. -/
private theorem exists_isPoincareResidue_pair_of_isResidueGenerator {k : Type} [Field k]
    [CharZero k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {e m : ℕ} (hm : Even m) {Θ : ∀ i, QDivisor (N.X i)}
    {U : T.Opens} {g : ∀ i, RationalPluriForms (N.n i ≫ sT) (e + 1) m}
    (hg : IsResidueGenerator N (e + 1) m Θ U g) {i i' : N.ι} {Y Y' S S' : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsIntegral S] [IsIntegral S'] (p : Y ⟶ N.X i) (p' : Y' ⟶ N.X i') [IsDominant p]
    [IsDominant p'] (j : S ⟶ Y) (j' : S' ⟶ Y') [IsClosedImmersion j] [IsClosedImmersion j']
    [LocallyOfFiniteType (p ≫ N.n i ≫ sT)] [LocallyOfFiniteType (p' ≫ N.n i' ≫ sT)]
    [LocallyOfFiniteType (j ≫ p ≫ N.n i ≫ sT)] [LocallyOfFiniteType (j' ≫ p' ≫ N.n i' ≫ sT)]
    (hX : topologicalKrullDim (N.X i) = (e + 1 : ℕ))
    (hX' : topologicalKrullDim (N.X i') = (e + 1 : ℕ))
    (hY : topologicalKrullDim Y = (e + 1 : ℕ)) (hY' : topologicalKrullDim Y' = (e + 1 : ℕ))
    (hS : topologicalKrullDim S = e) (hS' : topologicalKrullDim S' = e)
    (hb : Function.Bijective (functionFieldMap p)) (hb' : Function.Bijective (functionFieldMap p'))
    (hiso : IsIso (p.stalkMap (j (genericPoint S))))
    (hiso' : IsIso (p'.stalkMap (j' (genericPoint S'))))
    (hord : ∀ f, Y.ord (functionFieldMap p f) (j (genericPoint S)) =
      (N.X i).ord f (p (j (genericPoint S))))
    (hord' : ∀ f, Y'.ord (functionFieldMap p' f) (j' (genericPoint S')) =
      (N.X i').ord f (p' (j' (genericPoint S'))))
    (hx1 : Order.coheight (p (j (genericPoint S))) = 1)
    (hx1' : Order.coheight (p' (j' (genericPoint S'))) = 1)
    (hx' : (N.n i').base (p' (j' (genericPoint S'))) = (N.n i).base (p (j (genericPoint S))))
    (hQU : (N.n i).base (p (j (genericPoint S))) ∈ U)
    (hQD : (N.n i).base (p (j (genericPoint S))) ∈ (doubleIntersectionLocus T : Set T))
    (σS : FunctionFieldEquiv (j ≫ 𝟙 Y ≫ p ≫ N.n i ≫ sT) (j' ≫ 𝟙 Y' ≫ p' ≫ N.n i' ≫ sT))
    (hσS : ∀ a, σS (((j' ≫ p' ≫ N.n i').stalkMap (genericPoint S')).hom
          ((T.presheaf.stalkSpecializes (show (N.n i').base (p' (j' (genericPoint S'))) ⤳
            (N.n i).base (p (j (genericPoint S))) by rw [hx'])).hom a)) =
        ((j ≫ p ≫ N.n i).stalkMap (genericPoint S)).hom a) :
    ∃ (Ω : RationalPluriForms (j ≫ p ≫ N.n i ≫ sT) e m)
      (Ω' : RationalPluriForms (j' ≫ p' ≫ N.n i' ≫ sT) e m),
      IsPoincareResidue (p ≫ N.n i ≫ sT) j e m
        (pullbackRationalPluriForms (N.n i ≫ sT) p (g i)) Ω ∧
      IsPoincareResidue (p' ≫ N.n i' ≫ sT) j' e m
        (pullbackRationalPluriForms (N.n i' ≫ sT) p' (g i')) Ω' ∧
      pluriformPullback (j ≫ 𝟙 Y ≫ p ≫ N.n i ≫ sT) (j' ≫ 𝟙 Y' ≫ p' ≫ N.n i' ≫ sT) σS.toHom e m
        Ω' = Ω := by
  classical
  set x := p (j (genericPoint S))
  set x' := p' (j' (genericPoint S'))
  set P : Mori.PrimeDivisor (N.X i) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx1
  have hPx : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hx1
  set P' : Mori.PrimeDivisor (N.X i') := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x' hx1'
  have hPx' : P'.genericPoint = x' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hx1'
  have hPU : (N.n i).base P.genericPoint ∈ U := by rwa [hPx]
  have hPD : (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) := by
    rwa [hPx]
  have hPP' : (N.n i).base P.genericPoint = (N.n i').base P'.genericPoint := by
    rw [hPx, hPx', hx']
  -- a common presentation of the residues of `gᵢ` and `gⱼ`
  obtain ⟨V, hP, hP', a, g', ε, ε', hε, hε', hpres, hpres'⟩ :
      ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
        (hP' : (N.n i').base P'.genericPoint ∈ V) (a : Fin (e + 1 - 1) → Γ(T, V))
        (g' : Γ(T, V)) (ε ε' : ℤ), (ε : S.functionField) = 1 ∧ (ε' : S'.functionField) = 1 ∧
        IsLogResiduePresentation N (e + 1) m i P V hP a g' ε (g i) ∧
        IsLogResiduePresentation N (e + 1) m i' P' V hP' a g' ε' (g i') := by
    by_cases hbb : (⟨i, P.genericPoint⟩ : Σ i, N.X i) = ⟨i', P'.genericPoint⟩
    · obtain ⟨V, hP, a, g', hpres⟩ := hg.2 i P hPU hPD
      obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp hbb
      have hPP := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (eq_of_heq hh)
      have key : ∀ (P₀ : Mori.PrimeDivisor (N.X i)), P = P₀ →
          ∃ hP₀ : (N.n i).base P₀.genericPoint ∈ V,
            IsLogResiduePresentation N (e + 1) m i P₀ V hP₀ a g' 1 (g i) := by
        rintro _ rfl
        exact ⟨hP, hpres⟩
      obtain ⟨hP'', hpres''⟩ := key P' hPP
      exact ⟨V, hP, hP'', a, g', 1, 1, by simp, by simp, hpres, hpres''⟩
    · obtain ⟨V, hP, hP', a, g', hpres, hpres'⟩ := hg.1.2 i i' P P' hPP' hPU hPD hbb
      refine ⟨V, hP, hP', a, g', 1, (-1) ^ m, by simp, by simp [hm.neg_one_pow], hpres, hpres'⟩
  have hsp : x ⤳ P.genericPoint := by rw [hPx]
  have hsp' : x' ⤳ P'.genericPoint := by rw [hPx']
  have hres := isPoincareResidue_pullback_of_isLogResiduePresentation N p j hX hY hb hiso hord P
    hsp hPx.symm hP a g' ε hpres
  have hres' := isPoincareResidue_pullback_of_isLogResiduePresentation N p' j' hX' hY' hb' hiso'
    hord' P' hsp' hPx'.symm hP' a g' ε' hpres'
  refine ⟨_, _, hres, hres', ?_⟩
  have hxV : (N.n i).base x ∈ V := by rwa [← hPx]
  have hxV' : (N.n i').base x' ∈ V := by rwa [← hPx']
  have hT1 := fun f => stalkMap_comp_germ_eq (N.n i) p j P hsp hP hxV f
  have hT2 := fun f => stalkMap_comp_germ_eq (N.n i') p' j' P' hsp' hP' hxV' f
  have hσf : ∀ f : Γ(T, V),
      σS ((j'.stalkMap (genericPoint S')).hom ((p'.stalkMap (j' (genericPoint S'))).hom
        (((N.X i').presheaf.stalkSpecializes hsp').hom ((N.X i').presheaf.germ
          ((N.n i') ⁻¹ᵁ V) P'.genericPoint hP' ((N.n i').app V f))))) =
      (j.stalkMap (genericPoint S)).hom ((p.stalkMap (j (genericPoint S))).hom
        (((N.X i).presheaf.stalkSpecializes hsp).hom ((N.X i).presheaf.germ
          ((N.n i) ⁻¹ᵁ V) P.genericPoint hP ((N.n i).app V f)))) := by
    intro f
    rw [hT1, hT2, ← hσS]
    congr 2
    exact (TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _).symm
  refine (pluriformPullback_smul_formPow_ιMulti hS hS' σS.toHom m _ _).trans ?_
  congr 1
  · rw [map_mul, hε, hε']
    simp only [map_one, one_mul]
    exact hσf g'
  · congr 2
    funext l
    congr 1
    exact hσf (a l)

/-- **The branch identification is crepant.** For two branch strata `S`, `S'` over a
codimension-one point of the double locus and the birational identification `σ_S` compatible
with `𝒪_T`, `σ_S : (S, B_S) ⇢ (S', B_{S'})` is crepant: near the common image in `T` of the
centres of corresponding divisors, the residues of a local generator of `𝒪_T(mL)` generate both
adjoints and correspond under `σ_S`. -/
private theorem isCrepantBirationalMap_branch {k : Type} [Field k] [CharZero k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {e : ℕ} (he : e ≠ 0) {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N (e + 1) Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) (e + 1) K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C (e + 1) m)
    (hm : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) (e + 1) m),
      IsResidueGenerator N (e + 1) m Θ U g)
    {i i' : N.ι} {S S' : Scheme.{0}} {j : S ⟶ Y i} {j' : S' ⟶ Y i'} {BS : QDivisor S}
    {BS' : QDivisor S'} (hpair : MMP.Mori.IsPair (p i ≫ N.n i ≫ sT) (C i))
    (hpair' : MMP.Mori.IsPair (p i' ≫ N.n i' ≫ sT) (C i'))
    (hj : IsAdjunctionStep (𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT) (C i) j BS)
    (hj' : IsAdjunctionStep (𝟙 (Y i') ≫ p i' ≫ N.n i' ≫ sT) (C i') j' BS')
    [IsIntegral S] [IsIntegral S'] [IsNormal S] [IsNormal S'] [IsLocallyNoetherian S]
    [IsLocallyNoetherian S']
    (hS : topologicalKrullDim S = e) (hS' : topologicalKrullDim S' = e)
    (hiso : IsIso ((p i).stalkMap (j (genericPoint S))))
    (hiso' : IsIso ((p i').stalkMap (j' (genericPoint S'))))
    (hord : ∀ f, (Y i).ord (functionFieldMap (p i) f) (j (genericPoint S)) =
      (N.X i).ord f ((p i) (j (genericPoint S))))
    (hord' : ∀ f, (Y i').ord (functionFieldMap (p i') f) (j' (genericPoint S')) =
      (N.X i').ord f ((p i') (j' (genericPoint S'))))
    (hQ : Order.coheight ((N.n i).base ((p i) (j (genericPoint S)))) = 1)
    (hQD : (N.n i).base ((p i) (j (genericPoint S))) ∈ (doubleIntersectionLocus T : Set T))
    (hx' : (N.n i').base ((p i') (j' (genericPoint S'))) =
      (N.n i).base ((p i) (j (genericPoint S))))
    (σS : FunctionFieldEquiv (j ≫ 𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT)
      (j' ≫ 𝟙 (Y i') ≫ p i' ≫ N.n i' ≫ sT))
    (hσS : ∀ a, σS (((j' ≫ p i' ≫ N.n i').stalkMap (genericPoint S')).hom
          ((T.presheaf.stalkSpecializes (show (N.n i').base ((p i') (j' (genericPoint S'))) ⤳
            (N.n i).base ((p i) (j (genericPoint S))) by rw [hx'])).hom a)) =
        (((j ≫ p i ≫ N.n i).stalkMap (genericPoint S)).hom a)) :
    IsCrepantBirationalMap (j ≫ 𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT)
      (j' ≫ 𝟙 (Y i') ≫ p i' ≫ N.n i' ≫ sT) BS BS' σS := by
  classical
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI : IsSeparated sT := h.isNFold.1.1
  obtain ⟨-, -, -, -, hci, -⟩ := id hj
  obtain ⟨-, -, -, -, hci', -⟩ := id hj'
  haveI := hci
  haveI := hci'
  -- the varieties and their dimensions
  have hYv := (MMP.Mori.isProjectiveVariety_iff k _).mp (R.setting.isProjectiveVariety i)
  have hYv' := (MMP.Mori.isProjectiveVariety_iff k _).mp (R.setting.isProjectiveVariety i')
  haveI : IsProper (p i ≫ N.n i ≫ sT) := isProper_of_isProjectiveMorphism _ hYv.2
  haveI : IsProper (p i' ≫ N.n i' ≫ sT) := isProper_of_isProjectiveMorphism _ hYv'.2
  haveI : LocallyOfFiniteType (p i ≫ N.n i ≫ sT) := hYv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p i' ≫ N.n i' ≫ sT) := hYv'.1.toLocallyOfFiniteType
  haveI : IsProper (j ≫ 𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT) :=
    show IsProper (j ≫ p i ≫ N.n i ≫ sT) by infer_instance
  haveI : IsProper (j' ≫ 𝟙 (Y i') ≫ p i' ≫ N.n i' ≫ sT) :=
    show IsProper (j' ≫ p i' ≫ N.n i' ≫ sT) by infer_instance
  haveI : LocallyOfFiniteType (j ≫ p i ≫ N.n i ≫ sT) := hj.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (j' ≫ p i' ≫ N.n i' ≫ sT) := hj'.1.1.toLocallyOfFiniteType
  haveI : CompactSpace (Y i) := QuasiCompact.compactSpace_of_compactSpace (p i ≫ N.n i ≫ sT)
  haveI : CompactSpace (Y i') := QuasiCompact.compactSpace_of_compactSpace (p i' ≫ N.n i' ≫ sT)
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (j ≫ p i ≫ N.n i ≫ sT)
  haveI : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (j' ≫ p i' ≫ N.n i' ≫ sT)
  obtain ⟨Kx, hYn, hp, hC⟩ := hcrep i
  obtain ⟨Kx', hYn', hp', hC'⟩ := hcrep i'
  have hdY : topologicalKrullDim (Y i) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    R.setting.topologicalKrullDim_eq i
  have hdY' : topologicalKrullDim (Y i') = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    R.setting.topologicalKrullDim_eq i'
  have hX := N.isNormalVariety i
  have hX' := N.isNormalVariety i'
  haveI := hX.1
  haveI := hX'.1
  haveI := hYn.1
  haveI := hYn'.1
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (N.n i' ≫ sT) := hX'.1.toLocallyOfFiniteType
  have hdX : topologicalKrullDim (N.X i) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N.n i ≫ sT)
      (p i ≫ N.n i ≫ sT) hp).trans hdY
  have hdX' : topologicalKrullDim (N.X i') = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N.n i' ≫ sT)
      (p i' ≫ N.n i' ≫ sT) hp').trans hdY'
  have hx1 := coheight_eq_one_of_base_eq N _ rfl hQ
  have hx1' := coheight_eq_one_of_base_eq N _ hx' hQ
  -- canonical divisors on `Y` and on the strata
  obtain ⟨dY, KY, hKY, hKYC⟩ := R.setting.isCartierDivisor i (.refl hpair)
  obtain ⟨dY', KY', hKY', hKYC'⟩ := R.setting.isCartierDivisor i' (.refl hpair')
  obtain ⟨d, K, hK, hKC⟩ := R.setting.isCartierDivisor i (.step (.refl hpair) j BS hj)
  obtain ⟨d', K', hK', hKC'⟩ := R.setting.isCartierDivisor i' (.step (.refl hpair') j' BS' hj')
  have hdYe : dY = e + 1 := by exact_mod_cast hKY.topologicalKrullDim_eq.symm.trans hdY
  have hdYe' : dY' = e + 1 := by exact_mod_cast hKY'.topologicalKrullDim_eq.symm.trans hdY'
  have hde : d = e := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hS
  have hde' : d' = e := by exact_mod_cast hK'.topologicalKrullDim_eq.symm.trans hS'
  subst hdYe hdYe' hde hde'
  refine isCrepantBirationalMap_of_forall_generatesOn hj.1 hj'.1 hK hK' R.setting.pos hKC hKC' σS
    fun D D' hv => ?_
  letI := functionFieldAlgebra (j ≫ 𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT)
  letI := functionFieldAlgebra (j' ≫ 𝟙 (Y i') ≫ p i' ≫ N.n i' ≫ sT)
  have hc := map_center_eq_of_valuation_eq sT (j ≫ p i ≫ N.n i) (j' ≫ p i' ≫ N.n i')
    (show (N.n i').base ((p i') (j' (genericPoint S'))) ⤳ (N.n i).base ((p i) (j (genericPoint S)))
      by rw [hx']) σS.toRingEquiv hσS D D' hv
  obtain ⟨Ut, htU, gt, hgt⟩ := hm ((j ≫ p i ≫ N.n i) (D.f D.E.genericPoint))
  have hQt : (N.n i).base ((p i) (j (genericPoint S))) ∈ Ut :=
    (((genericPoint_spec S).specializes (Set.mem_univ (D.f D.E.genericPoint))).map
      (j ≫ p i ≫ N.n i).continuous).mem_open Ut.isOpen htU
  obtain ⟨Ω, Ω', hΩ, hΩ', hσΩ⟩ := exists_isPoincareResidue_pair_of_isResidueGenerator N
    R.setting.even hgt (p i) (p i') j j' hdX hdX' hdY hdY' hS hS' hp.functionFieldMap_bijective
    hp'.functionFieldMap_bijective hiso hiso' hord hord' hx1 hx1' hx' hQt hQD σS hσS
  have hτ := generatesOn_pullback hdX (p i) hYn hp hC (hgt.1.1 i)
  have hτ' := generatesOn_pullback hdX' (p i') hYn' hp' hC' (hgt.1.1 i')
  have hW : j (genericPoint S) ∈ (p i) ⁻¹ᵁ (N.n i ⁻¹ᵁ Ut) := hQt
  have hW' : j' (genericPoint S') ∈ (p i') ⁻¹ᵁ (N.n i' ⁻¹ᵁ Ut) := by
    show (N.n i').base ((p i') (j' (genericPoint S'))) ∈ Ut
    rwa [hx']
  refine ⟨j ⁻¹ᵁ ((p i) ⁻¹ᵁ (N.n i ⁻¹ᵁ Ut)), j' ⁻¹ᵁ ((p i') ⁻¹ᵁ (N.n i' ⁻¹ᵁ Ut)), Ω, Ω', htU,
    ?_, ?_, ?_, hσΩ⟩
  · show (j' ≫ p i' ≫ N.n i') (D'.f D'.E.genericPoint) ∈ Ut
    rwa [← hc]
  · exact generatesOn_of_isPoincareResidue hYn (by exact_mod_cast hdY) he hj hS R.setting.pos hKY
      hKYC hW hτ hΩ
  · exact generatesOn_of_isPoincareResidue hYn' (by exact_mod_cast hdY') he hj' hS' R.setting.pos
      hKY' hKYC' hW' hτ' hΩ'

/-- Pluriform pull-back along `φ` is `φ`-semilinear. -/
private theorem pluriformPullback_smul_of_functionFieldHom {k : Type} [Field k] {X X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
    (φ : FunctionFieldHom sX sX') {d : ℕ} {m : ℤ} (c : X'.functionField)
    (τ : RationalPluriForms sX' d m) :
    pluriformPullback sX sX' φ d m (c • τ) = φ c • pluriformPullback sX sX' φ d m τ := by
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact MMP.Fourfold.pullbackForms_smul (K := X'.functionField) (K' := X.functionField) c τ

/-- **Preadmissibility identifies the values at the branches.** For two points `x ⊆ Tᵢ`,
`x' ⊆ Tⱼ` over a codimension-one point `Q` of the double locus and a `κ(Q)`-isomorphism
`σ : κ(x') ≅ κ(x)`, the values at `x'` and `x` of the functions `φⱼ`, `φᵢ` of step 1 correspond
under `σ`. The isomorphism `σ` induces a crepant birational map between the adjunction pairs of
the strict transforms of the two branches on `Yⱼ`, `Yᵢ`, since both adjoints are generated by
residues of `pᵢ^*gᵢ`, which are pulled back from `Q`; preadmissibility of `s` identifies the
residues of `sⱼ` and `sᵢ`, which are `φⱼ`, `φᵢ` times those pulled-back forms. -/
private theorem branchValue_eq_of_mem_preadmissibleSections {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C n m)
    (hm : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsResidueGenerator N n m Θ U g)
    (s : ∀ i, logPluricanonicalSections (p i ≫ N.n i ≫ sT) n m (C i))
    (hs : s ∈ preadmissibleSections R) (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
    (ht : ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _))
    {U : T.Opens} {g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hg : IsResidueGenerator N n m Θ U g) (φ : ∀ i, (N.X i).functionField)
    (htφ : ∀ i, t i = φ i • g i) (Q : T) (hQU : Q ∈ U) (hQ : Order.coheight Q = 1)
    (hQD : Q ∈ (doubleIntersectionLocus T : Set T)) {i j : N.ι} (x : N.X i) (x' : N.X j)
    (hx : (N.n i).base x = Q) (hx' : (N.n j).base x' = Q)
    (σ : (N.X j).residueField x' ≃+* (N.X i).residueField x)
    (hσ : ∀ a, σ (branchMap N x' hx' a) = branchMap N x hx a)
    (r : (N.X i).presheaf.stalk x) (hr : algebraMap _ (N.X i).functionField r = φ i)
    (r' : (N.X j).presheaf.stalk x') (hr' : algebraMap _ (N.X j).functionField r' = φ j) :
    σ ((N.X j).residue x' r') = (N.X i).residue x r := by
  classical
  have hPi := R.setting.isPair i
  haveI : CharZero k := hPi.charZero
  haveI : PerfectField k := PerfectField.ofCharZero
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  obtain ⟨Kx, hYn, hp, hC⟩ := hcrep i
  obtain ⟨Kx', hYn', hp', hC'⟩ := hcrep j
  have hX := N.isNormalVariety i
  have hX' := N.isNormalVariety j
  haveI := hX.1
  haveI := hX'.1
  haveI := hYn.1
  haveI := hYn'.1
  haveI : LocallyOfFiniteType (N.n i ≫ sT) := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (N.n j ≫ sT) := hX'.1.toLocallyOfFiniteType
  have hdX : topologicalKrullDim (N.X i) = (n : WithBot ℕ∞) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N.n i ≫ sT)
      (p i ≫ N.n i ≫ sT) hp).trans (R.setting.topologicalKrullDim_eq i)
  have hdX' : topologicalKrullDim (N.X j) = (n : WithBot ℕ∞) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (N.n j ≫ sT)
      (p j ≫ N.n j ≫ sT) hp').trans (R.setting.topologicalKrullDim_eq j)
  have hx1 := coheight_eq_one_of_base_eq N x hx hQ
  have hx1' := coheight_eq_one_of_base_eq N x' hx' hQ
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    rintro rfl
    have h1 := AlgebraicGeometry.coheight_le_topologicalKrullDim x
    rw [hx1, hdX] at h1
    exact absurd h1 (by decide)
  have hdY : topologicalKrullDim (Y i) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    R.setting.topologicalKrullDim_eq i
  have hdY' : topologicalKrullDim (Y j) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    R.setting.topologicalKrullDim_eq j
  have hYv := (MMP.Mori.isProjectiveVariety_iff k _).mp (R.setting.isProjectiveVariety i)
  have hYv' := (MMP.Mori.isProjectiveVariety_iff k _).mp (R.setting.isProjectiveVariety j)
  haveI : IsProper (p i ≫ N.n i ≫ sT) := isProper_of_isProjectiveMorphism _ hYv.2
  haveI : IsProper (p j ≫ N.n j ≫ sT) := isProper_of_isProjectiveMorphism _ hYv'.2
  haveI : LocallyOfFiniteType (p i ≫ N.n i ≫ sT) := hYv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (p j ≫ N.n j ≫ sT) := hYv'.1.toLocallyOfFiniteType
  haveI : CompactSpace (Y i) := QuasiCompact.compactSpace_of_compactSpace (p i ≫ N.n i ≫ sT)
  haveI : CompactSpace (Y j) := QuasiCompact.compactSpace_of_compactSpace (p j ≫ N.n j ≫ sT)
  -- the strata of the strict transforms of the two branches
  obtain ⟨S, ι₁, BS, hpair, hj, hdS, hxS, hiso, hord, Γ, hΓ, hΓm⟩ :=
    exists_branchStratum h p hproj hcrep R hg hQU hQ hQD x hx
  obtain ⟨S', ι₂, BS', hpair', hj', hdS', hxS', hiso', hord', Γ', hΓ', hΓm'⟩ :=
    exists_branchStratum h p hproj hcrep R hg hQU hQ hQD x' hx'
  haveI : IsIntegral S := hj.1.1.toIsIntegral
  haveI : IsIntegral S' := hj'.1.1.toIsIntegral
  haveI : IsNormal S := hj.1.2
  haveI : IsNormal S' := hj'.1.2
  obtain ⟨-, -, -, -, hci, -⟩ := id hj
  obtain ⟨-, -, -, -, hci', -⟩ := id hj'
  haveI := hci
  haveI := hci'
  haveI : LocallyOfFiniteType (ι₁ ≫ p i ≫ N.n i ≫ sT) := hj.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (ι₂ ≫ p j ≫ N.n j ≫ sT) := hj'.1.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (ι₁ ≫ p i ≫ N.n i ≫ sT)
  haveI : IsLocallyNoetherian S' :=
    LocallyOfFiniteType.isLocallyNoetherian (ι₂ ≫ p j ≫ N.n j ≫ sT)
  haveI : IsProper (ι₁ ≫ p i ≫ N.n i ≫ sT) := inferInstance
  haveI : IsProper (ι₂ ≫ p j ≫ N.n j ≫ sT) := inferInstance
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (ι₁ ≫ p i ≫ N.n i ≫ sT)
  haveI : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace (ι₂ ≫ p j ≫ N.n j ≫ sT)
  subst hxS hxS'
  subst hx
  -- the birational identification of the strata and its crepancy
  obtain ⟨σS, hσS, hσr⟩ :=
    exists_functionFieldEquiv_of_branchMap N (p i) (p j) ι₁ ι₂ hiso hiso' hx' σ hσ
  have hcS : IsCrepantBirationalMap (ι₁ ≫ 𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT)
      (ι₂ ≫ 𝟙 (Y j) ≫ p j ≫ N.n j ≫ sT) BS BS' σS := by
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      exact isCrepantBirationalMap_of_topologicalKrullDim_eq_zero (by simpa using hdS)
        (by simpa using hdS') BS BS' σS
    · exact isCrepantBirationalMap_branch he.ne' h p hproj hcrep R hm hpair hpair' hj hj' hdS
        hdS' hiso hiso' hord hord' hQ hQD hx' σS hσS
  -- preadmissibility along the two length-one flags
  have hpre := hs i j (.step (.refl hpair) ι₁ BS hj) (.step (.refl hpair') ι₂ BS' hj') e le_rfl
    le_rfl hdS hdS' σS hcS
  -- the residues of `sᵢ` and `sⱼ`
  obtain ⟨ρ₀, ⟨-, hρ₀⟩, ρ, hρr, hρ⟩ :=
    (R.isIteratedResidue i (.step (.refl hpair) ι₁ BS hj) e (s i) hdS).rec'
  obtain ⟨ρ₀', ⟨-, hρ₀'⟩, ρ', hρr', hρ'⟩ :=
    (R.isIteratedResidue j (.step (.refl hpair') ι₂ BS' hj') e (s j) hdS').rec'
  have e1 : ρ₀ = ((s i : _) : RationalPluriForms (p i ≫ N.n i ≫ sT) (e + 1) m) := eq_of_heq hρ₀
  have e1' : ρ₀' = ((s j : _) : RationalPluriForms (p j ≫ N.n j ≫ sT) (e + 1) m) :=
    eq_of_heq hρ₀'
  have e3 : R.toFun i (.step (.refl hpair) ι₁ BS hj) e (s i) = ρ := eq_of_heq hρ
  have e3' : R.toFun j (.step (.refl hpair') ι₂ BS' hj') e (s j) = ρ' := eq_of_heq hρ'
  subst e1 e1'
  have hsi : ((s i : _) : RationalPluriForms (p i ≫ N.n i ≫ sT) (e + 1) m) =
      algebraMap _ (Y i).functionField (((p i).stalkMap _).hom r) •
        pullbackRationalPluriForms (N.n i ≫ sT) (p i) (g i) := by
    rw [← ht, htφ, pullbackRationalPluriForms_smul, ← hr, functionFieldMap_algebraMap_stalk]
  have hsj : ((s j : _) : RationalPluriForms (p j ≫ N.n j ≫ sT) (e + 1) m) =
      algebraMap _ (Y j).functionField (((p j).stalkMap _).hom r') •
        pullbackRationalPluriForms (N.n j ≫ sT) (p j) (g j) := by
    rw [← ht, htφ, pullbackRationalPluriForms_smul, ← hr', functionFieldMap_algebraMap_stalk]
  -- the residues of the pulled-back generator
  obtain ⟨Ω, Ω', hΩ, hΩ', hσΩ⟩ := exists_isPoincareResidue_pair_of_isResidueGenerator N
    R.setting.even hg (p i) (p j) ι₁ ι₂ hdX hdX' hdY hdY' hdS hdS' hp.functionFieldMap_bijective
    hp'.functionFieldMap_bijective hiso hiso' hord hord' hx1 hx1' hx' hQU hQD σS hσS
  have hρeq : ρ = (ι₁.stalkMap (genericPoint S)).hom (((p i).stalkMap _).hom r) • Ω := by
    rw [hsi] at hρr
    exact IsPoincareResidue.unique hj hρr
      (MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hΩ _)
  have hρeq' : ρ' = (ι₂.stalkMap (genericPoint S')).hom (((p j).stalkMap _).hom r') • Ω' := by
    rw [hsj] at hρr'
    exact IsPoincareResidue.unique hj' hρr'
      (MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hΩ' _)
  -- the residue `Ω` is nonzero
  have hτ := generatesOn_pullback hdX (p i) hYn hp hC (hg.1.1 i)
  have hΩ0 : Ω ≠ 0 := by
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      exact isPoincareResidue_ne_zero_of_ordForm_eq hdY hdS Γ hΓ hτ.1 hΓm hΩ
    · obtain ⟨dY, KY, hKY, hKYC⟩ := R.setting.isCartierDivisor i (.refl hpair)
      have hdYe : dY = e + 1 := by
        have := hKY.topologicalKrullDim_eq.symm.trans hdY; exact_mod_cast this
      subst hdYe
      have hW : ι₁ (genericPoint S) ∈ (p i) ⁻¹ᵁ (N.n i ⁻¹ᵁ U) := hQU
      exact (generatesOn_of_isPoincareResidue hYn (by exact_mod_cast hdY) he.ne' hj hdS
        R.setting.pos hKY hKYC hW hτ hΩ).1
  -- cancel `Ω`
  have h1 := pluriformPullback_smul_of_functionFieldHom
    (sX := ι₁ ≫ 𝟙 (Y i) ≫ p i ≫ N.n i ≫ sT) (sX' := ι₂ ≫ 𝟙 (Y j) ≫ p j ≫ N.n j ≫ sT)
    σS.toHom (d := e) (m := m) ((ι₂.stalkMap (genericPoint S')).hom (((p j).stalkMap _).hom r'))
    Ω'
  rw [hσΩ] at h1
  rw [e3, e3', hρeq, hρeq'] at hpre
  have key := h1.symm.trans hpre
  have hc : σS ((ι₂.stalkMap (genericPoint S')).hom (((p j).stalkMap _).hom r')) =
      (ι₁.stalkMap (genericPoint S)).hom (((p i).stalkMap _).hom r) := by
    by_contra hne
    apply hΩ0
    have h2 : (σS ((ι₂.stalkMap (genericPoint S')).hom (((p j).stalkMap _).hom r')) -
        (ι₁.stalkMap (genericPoint S)).hom (((p i).stalkMap _).hom r)) • Ω = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr key
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)
  exact (hσr r r').mp hc

/-- **Step 2: preadmissibility glues the branches at a double point.** At a codimension-one
point `Q ∈ U` of the double locus, the regular functions `φᵢ` of step 1 have a common value: there
is a function `a` on `T` near `Q` with `φᵢ - νᵢ^*a` vanishing at every point of the normalization
over `Q`. -/
private theorem exists_common_value_of_mem_preadmissibleSections {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C n m)
    (hm : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsResidueGenerator N n m Θ U g)
    (s : ∀ i, logPluricanonicalSections (p i ≫ N.n i ≫ sT) n m (C i))
    (hs : s ∈ preadmissibleSections R) (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
    (ht : ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _))
    {U : T.Opens} {g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hg : IsResidueGenerator N n m Θ U g) (φ : ∀ i, (N.X i).functionField)
    (htφ : ∀ i, t i = φ i • g i)
    (hφ : ∀ i, ∀ z ∈ N.n i ⁻¹ᵁ U,
      φ i ∈ (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range)
    (Q : T) (hQU : Q ∈ U) (hQ : Order.coheight Q = 1)
    (hQD : Q ∈ (doubleIntersectionLocus T : Set T)) :
    ∃ (V : T.Opens) (hQV : Q ∈ V) (a : Γ(T, V)), ∀ i (x : N.X i)
      (hx : (N.n i).base x = Q),
      haveI : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨x, show (N.n i).base x ∈ V from hx ▸ hQV⟩⟩
      ∃ r ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk x),
        algebraMap ((N.X i).presheaf.stalk x) (N.X i).functionField r =
          φ i - ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V a) := by
  classical
  have hrv : ∀ i (x : N.X i), (N.n i).base x = Q →
      ∃ r : (N.X i).presheaf.stalk x, algebraMap _ (N.X i).functionField r = φ i :=
    fun i x hx => hφ i x (show (N.n i).base x ∈ U by rwa [hx])
  have hval := fun {i j : N.ι} (x : N.X i) (x' : N.X j) hx hx' σ hσ r hr r' hr' =>
    branchValue_eq_of_mem_preadmissibleSections h p hproj hcrep R hm s hs t ht hg φ htφ Q hQU
      hQ hQD (i := i) (j := j) x x' hx hx' σ hσ r hr r' hr'
  -- a common value in `𝒪_{T,Q}`
  obtain ⟨c, hc⟩ : ∃ c : T.presheaf.stalk Q, ∀ i (x : N.X i) (hx : (N.n i).base x = Q)
      (r : (N.X i).presheaf.stalk x), algebraMap _ (N.X i).functionField r = φ i →
      branchMap N x hx c = (N.X i).residue x r := by
    haveI : CharZero k := by
      obtain ⟨i₁, -, -⟩ := exists_base_eq N Q
      exact (R.setting.isPair i₁).charZero
    rcases branchMap_surjective_or_exists_unique h Q hQ hQD with hall | ⟨i₀, x₀, hx₀, huniq, τ,
      hτ, hfix⟩
    · obtain ⟨i₀, x₀, hx₀⟩ := exists_base_eq N Q
      obtain ⟨r₀, hr₀⟩ := hrv i₀ x₀ hx₀
      obtain ⟨c, hc⟩ := hall i₀ x₀ hx₀ ((N.X i₀).residue x₀ r₀)
      refine ⟨c, fun i x hx r hr => ?_⟩
      have hker : ∀ {i} (x : N.X i) (hx : (N.n i).base x = Q),
          RingHom.ker (branchMap N x hx) = IsLocalRing.maximalIdeal (T.presheaf.stalk Q) :=
        fun x hx =>
          IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hall _ x hx))
      let σ : (N.X i).residueField x ≃+* (N.X i₀).residueField x₀ :=
        ((RingHom.quotientKerEquivOfSurjective (hall i x hx)).symm.trans
          (Ideal.quotEquivOfEq ((hker x hx).trans (hker x₀ hx₀).symm))).trans
          (RingHom.quotientKerEquivOfSurjective (hall i₀ x₀ hx₀))
      have hσ : ∀ a, σ (branchMap N x hx a) = branchMap N x₀ hx₀ a := by
        intro a
        have e1 : (RingHom.quotientKerEquivOfSurjective (hall i x hx)).symm
            (branchMap N x hx a) = Ideal.Quotient.mk _ a := by
          rw [RingEquiv.symm_apply_eq]; rfl
        simp only [σ, RingEquiv.trans_apply, e1, Ideal.quotEquivOfEq_mk]
        rfl
      have e := hval x₀ x hx₀ hx σ hσ r₀ hr₀ r hr
      apply σ.injective
      rw [hσ, hc, e]
    · obtain ⟨r₀, hr₀⟩ := hrv i₀ x₀ hx₀
      have hτr := hval x₀ x₀ hx₀ hx₀ τ hτ r₀ hr₀ r₀ hr₀
      obtain ⟨c, hc⟩ := hfix _ hτr
      refine ⟨c, fun i x hx r hr => ?_⟩
      obtain ⟨rfl, hxx⟩ := Sigma.mk.inj_iff.mp (huniq i x hx)
      obtain rfl := eq_of_heq hxx
      have hrr : r = r₀ := IsFractionRing.injective _ (N.X i).functionField (hr.trans hr₀.symm)
      rw [hrr, hc]
  obtain ⟨V, hQV, a, ha⟩ := T.presheaf.germ_exist c
  refine ⟨V, hQV, a, fun i x hx => ?_⟩
  obtain ⟨r, hr⟩ := hrv i x hx
  have hxV : (N.n i).base x ∈ V := by rwa [hx]
  set gx := ((N.n i).stalkMap x).hom (T.presheaf.germ V ((N.n i).base x) hxV a)
  refine ⟨r - gx, ?_, ?_⟩
  · rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    have h1 := hc i x hx r hr
    change ((N.X i).residue x).hom r = ((N.X i).residue x).hom gx
    rw [← h1, ← ha]
    change ((N.X i).residue x).hom (((N.n i).stalkMap x).hom
      ((T.presheaf.stalkSpecializes _).hom (T.presheaf.germ V Q hQV a))) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  · rw [map_sub, hr]
    congr 1
    have e1 : gx = (N.X i).presheaf.germ (N.n i ⁻¹ᵁ V) x hxV ((N.n i).app V a) :=
      Scheme.Hom.germ_stalkMap_apply (N.n i) V x hxV a
    rw [e1]
    haveI : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨x, hxV⟩⟩
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := N.X i) (U := N.n i ⁻¹ᵁ V) hxV _

/-- A family `φ` of rational functions on the normalization components *descends on* `V` if it
is the pull-back of a function on `V`. -/
private def DescendsOn {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (φ : ∀ i, (N.X i).functionField) (V : T.Opens) : Prop :=
  ∃ b : Γ(T, V), ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ V)),
    φ i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V b)

/-- On a reduced scheme a nonzero section has a nonzero germ at a generic point of an
irreducible component. -/
private theorem exists_mem_genericPoints_germ_ne_zero' {Y : Scheme.{0}} [IsReduced Y]
    {V : Y.Opens} (t : Γ(Y, V)) (ht : t ≠ 0) :
    ∃ (y : Y) (hy : y ∈ V), y ∈ genericPoints Y ∧ Y.presheaf.germ V y hy t ≠ 0 := by
  have hb : Y.basicOpen t ≠ ⊥ := fun h => ht ((basicOpen_eq_bot_iff t).mp h)
  obtain ⟨z, hz⟩ : ∃ z, z ∈ Y.basicOpen t := by
    by_contra! h
    exact hb (eq_bot_iff.2 fun x hx => (h x hx).elim)
  let C : irreducibleComponents Y :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  have hηz : (genericPoints.ofComponent C).1 ⤳ z := specializes_iff_mem_closure.mpr <|
    (genericPoints.isGenericPoint_ofComponent C).symm ▸ mem_irreducibleComponent
  have hηb : (genericPoints.ofComponent C).1 ∈ Y.basicOpen t :=
    hηz.mem_open (Y.basicOpen t).isOpen hz
  have hηV : (genericPoints.ofComponent C).1 ∈ V := Y.basicOpen_le t hηb
  refine ⟨_, hηV, (genericPoints.ofComponent C).2, ?_⟩
  exact ((Y.mem_basicOpen t _ hηV).mp hηb).ne_zero

/-- **Generic points of `T` come from the normalization components.** Every generic point `η` of
an irreducible component of the reduced scheme `T` is the image `νᵢ(ηᵢ)` of the generic point of a
normalization component, and `νᵢ` is an isomorphism of local rings there. -/
private theorem exists_base_genericPoint_eq {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] (N : NormalizationComponents sT hT) {η : T} (hη : η ∈ genericPoints T) :
    ∃ i, (N.n i).base (genericPoint (N.X i)) = η ∧
      IsIso ((N.n i).stalkMap (genericPoint (N.X i))) := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hbir : IsBirational (slcCurveNormalization T hT) := Scheme.isBirational_normalization T hT
  obtain ⟨w, hw, hwη⟩ := hbir.1.surjOn hη
  obtain ⟨⟨i, u⟩, hu⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  set e := Limits.Sigma.ι N.X i ≫ φ.hom with he
  have heu : e.base u = w := by
    have h2 : φ.hom.base (φ.inv.base w) = w := by
      rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
      rfl
    rw [he, Scheme.Hom.comp_apply, ← sigmaMk_mk, hu, h2]
  have hne : e ≫ slcCurveNormalization T hT = N.n i := by
    rw [he, Category.assoc, hφ, Limits.Sigma.ι_desc]
  have hu0 : u = genericPoint (N.X i) := by
    have hmax : IsMax w := Stacks.Chow.isMax_of_mem_genericPoints ⟨w, hw⟩
    have h1 : genericPoint (N.X i) ⤳ u :=
      (genericPoint_spec (N.X i)).specializes (Set.mem_univ u)
    have h2 : e.base u ≤ e.base (genericPoint (N.X i)) :=
      Scheme.le_iff_specializes.mpr (h1.map e.continuous)
    rw [heu] at h2
    have h3 := hmax h2
    rw [← heu, Scheme.le_iff_specializes] at h3
    have h4 : u ⤳ genericPoint (N.X i) := e.isOpenEmbedding.toIsInducing.specializes_iff.mp h3
    exact (h4.antisymm h1).eq
  subst hu0
  refine ⟨i, ?_, ?_⟩
  · rw [← hne]
    change (slcCurveNormalization T hT).base (e.base _) = η
    rw [heu, hwη]
  · have key : ∀ g : N.X i ⟶ T, g = e ≫ slcCurveNormalization T hT →
        IsIso (g.stalkMap (genericPoint (N.X i))) := by
      intro g hg
      subst hg
      rw [Scheme.Hom.stalkMap_comp]
      haveI h1 : IsIso ((slcCurveNormalization T hT).stalkMap
          (e.base (genericPoint (N.X i)))) := by
        rw [heu]; exact hbir.2 w hw
      have h2 : IsIso (e.stalkMap (genericPoint (N.X i))) :=
        IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
    exact key _ hne.symm

/-- On a reduced scheme, a nonzero element of a local ring stays nonzero at some generic point
specializing to the point: it lies outside some minimal prime. -/
private theorem exists_genericPoint_stalkSpecializes_ne_zero {T : Scheme.{0}} [IsReduced T]
    {Q : T} (c : T.presheaf.stalk Q) (hc : c ≠ 0) :
    ∃ (η : T) (h : η ⤳ Q), η ∈ genericPoints T ∧ (T.presheaf.stalkSpecializes h).hom c ≠ 0 := by
  obtain ⟨p, hp, hcp⟩ : ∃ p ∈ minimalPrimes (T.presheaf.stalk Q), c ∉ p := by
    by_contra hall
    push Not at hall
    have : c ∈ nilradical (T.presheaf.stalk Q) := by
      rw [nilradical_eq_sInf_minimalPrimes]; exact Submodule.mem_sInf.mpr hall
    exact hc (IsReduced.eq_zero c this)
  have hpp : p.IsPrime := hp.1.1
  let q : PrimeSpectrum (T.presheaf.stalk Q) := ⟨p, hpp⟩
  have h := Stacks.Chow.specializes_fromSpecStalk Q q
  refine ⟨_, h, ?_, ?_⟩
  · apply Stacks.Chow.mem_genericPoints_of_isMax
    rw [← Order.coheight_eq_zero]
    refine (Stacks.Chow.coheight_fromSpecStalk_eq_height Q q).trans ?_
    change p.height = 0
    exact Ideal.height_eq_zero_iff.mpr hp
  · letI := (T.presheaf.stalkSpecializes h).hom.toAlgebra
    haveI := Stacks.Chow.isLocalization_stalk_of_specializes h q rfl
    have hu : IsUnit (algebraMap (T.presheaf.stalk Q)
        (T.presheaf.stalk (T.fromSpecStalk Q q)) c) :=
      IsLocalization.map_units _ (⟨c, hcp⟩ : p.primeCompl)
    exact hu.ne_zero

/-- **A function on `T` is detected on the normalization.** A nonzero function on an open `V` of
the reduced scheme `T` has a nonzero pull-back to the function field of some normalization
component meeting `V`: it has a nonzero germ at a generic point of `T`, where the normalization
is an isomorphism of local rings. -/
private theorem exists_germToFunctionField_ne_zero {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] (N : NormalizationComponents sT hT) {V : T.Opens} (c : Γ(T, V))
    (hc : c ≠ 0) : ∃ i, ∃ _ : Nonempty (N.n i ⁻¹ᵁ V),
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V c) ≠ 0 := by
  obtain ⟨η, hηV, hη, hgerm⟩ := exists_mem_genericPoints_germ_ne_zero' c hc
  obtain ⟨i, hηeq, hiso⟩ := exists_base_genericPoint_eq N hη
  subst hηeq
  haveI : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨_, hηV⟩⟩
  refine ⟨i, inferInstance, fun h0 => hgerm ?_⟩
  apply (ConcreteCategory.bijective_of_isIso ((N.n i).stalkMap (genericPoint (N.X i)))).1
  rwa [Scheme.Hom.germ_stalkMap_apply (N.n i) V (genericPoint (N.X i)) hηV c, map_zero]

/-- **Descents glue.** On the reduced scheme `T`, a function is determined by its pull-backs to
the normalization components, so descents over the members of a family of opens glue to a descent
over their union. -/
private theorem descendsOn_iSup {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} [IsReduced T] {φ : ∀ i, (N.X i).functionField}
    {ι : Type} (V : ι → T.Opens) (hV : ∀ j, DescendsOn N φ (V j)) :
    DescendsOn N φ (⨆ j, V j) := by
  choose b hb using hV
  have hcompat : TopCat.Presheaf.IsCompatible T.presheaf V b := by
    intro j j'
    by_contra hne
    obtain ⟨i, hi, hi0⟩ := exists_germToFunctionField_ne_zero N _ (sub_ne_zero.mpr hne)
    apply hi0
    have hj : Nonempty (N.n i ⁻¹ᵁ V j) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    have hj' : Nonempty (N.n i ⁻¹ᵁ V j') := ⟨⟨hi.some.1, hi.some.2.2⟩⟩
    rw [map_sub, map_sub, sub_eq_zero]
    have e1 := germToFunctionField_app_res N i (inf_le_left : V j ⊓ V j' ≤ V j) (b j)
    have e2 := germToFunctionField_app_res N i (inf_le_right : V j ⊓ V j' ≤ V j') (b j')
    exact e1.trans ((hb j i hj).symm.trans ((hb j' i hj').trans e2.symm))
  obtain ⟨t, ht, -⟩ := T.sheaf.existsUnique_gluing V b hcompat
  refine ⟨t, fun i hi => ?_⟩
  obtain ⟨x, hx⟩ := hi.some
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hne : Nonempty (N.n i ⁻¹ᵁ V j) := ⟨⟨x, hj⟩⟩
  have hle : V j ≤ iSup V := le_iSup V j
  have e1 := germToFunctionField_app_res N i hle t
  have e2 : t |_ V j = b j := ht j
  exact (hb j i hne).trans ((congrArg (fun s => ((N.X i).germToFunctionField
    (N.n i ⁻¹ᵁ V j)).hom ((N.n i).app (V j) s)) e2).symm.trans e1)

/-- **Descent at a normal point.** If the local ring of `T` at `z ∈ U` is a normal domain, then
the normalization is an isomorphism over a neighbourhood of `z`, so a family `φ` regular on
`ν⁻¹(U)` descends near `z`. -/
private theorem exists_descendsOn_of_isIntegrallyClosed {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) {U : T.Opens}
    (φ : ∀ i, (N.X i).functionField)
    (hφ : ∀ i, ∀ z ∈ N.n i ⁻¹ᵁ U,
      φ i ∈ (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range)
    (z : T) (hz : z ∈ U) [IsDomain (T.presheaf.stalk z)]
    [IsIntegrallyClosed (T.presheaf.stalk z)] :
    ∃ V : T.Opens, z ∈ V ∧ V ≤ U ∧ DescendsOn N φ V := by
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI : IsProper sT := isProper_of_isProjectiveMorphism sT h.isProjectiveMorphism
  haveI : CompactSpace T := (quasiCompact_iff_compactSpace sT).mp inferInstance
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI : IsNoetherian T := ⟨⟩
  obtain ⟨φe, hφe⟩ := N.exists_iso
  haveI : IsFinite (slcCurveNormalization T hT) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sT) hT
  haveI : IsNormal (Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hT) :=
    Scheme.isNormal_normalizationScheme_of_isReduced T hT
  have hbir : IsBirational (slcCurveNormalization T hT) := Scheme.isBirational_normalization T hT
  obtain ⟨V₀, hzV₀, hiso⟩ := exists_isIso_restrict_of_finite_fiber_of_normal
    (slcCurveNormalization T hT) hbir z (Scheme.Hom.finite_preimage_singleton _ _)
  have hsurj : Surjective (slcCurveNormalization T hT) := Scheme.surjective_normalization T hT
  obtain ⟨w, hw⟩ := hsurj.surj z
  -- the unique preimage of `z`
  have huniq : ∀ w', (slcCurveNormalization T hT).base w' = z → w' = w := by
    intro w' hw'
    have hinj : Function.Injective ((slcCurveNormalization T hT) ∣_ V₀).base :=
      ((slcCurveNormalization T hT) ∣_ V₀).isOpenEmbedding.injective
    have h1 : w' ∈ (slcCurveNormalization T hT) ⁻¹ᵁ V₀ := by
      change (slcCurveNormalization T hT).base w' ∈ V₀; rwa [hw']
    have h2 : w ∈ (slcCurveNormalization T hT) ⁻¹ᵁ V₀ := by
      change (slcCurveNormalization T hT).base w ∈ V₀; rwa [hw]
    have := hinj (a₁ := ⟨w', h1⟩) (a₂ := ⟨w, h2⟩) (Subtype.ext (by
      exact (morphismRestrict_base_coe (slcCurveNormalization T hT) V₀ ⟨w', h1⟩).trans
        (hw'.trans (hw.symm.trans
          (morphismRestrict_base_coe (slcCurveNormalization T hT) V₀ ⟨w, h2⟩).symm))))
    exact congrArg Subtype.val this
  obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk N.X).surjective (φe.inv.base w)
  set e := Limits.Sigma.ι N.X i ≫ φe.hom with he
  have hex : e.base x = w := by
    have h2 : φe.hom.base (φe.inv.base w) = w := by
      rw [← Scheme.Hom.comp_apply φe.inv φe.hom, Iso.inv_hom_id]
      rfl
    rw [he, Scheme.Hom.comp_apply, ← sigmaMk_mk, hx, h2]
  have hne : e ≫ slcCurveNormalization T hT = N.n i := by
    rw [he, Category.assoc, hφe, Limits.Sigma.ι_desc]
  have hxz : (N.n i).base x = z := by
    rw [← hne]; change (slcCurveNormalization T hT).base (e.base x) = z
    rw [hex, hw]
  -- the stalk map of `νᵢ` at `x` is an isomorphism
  have hst : IsIso ((N.n i).stalkMap x) := by
    have key : ∀ g : N.X i ⟶ T, g = e ≫ slcCurveNormalization T hT → IsIso (g.stalkMap x) := by
      intro g hg
      subst hg
      rw [Scheme.Hom.stalkMap_comp]
      have hmem : (slcCurveNormalization T hT).base (e.base x) ∈ V₀ := by rwa [hex, hw]
      have h1 := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (morphismRestrictStalkMap (slcCurveNormalization T hT) V₀ ⟨e.base x, hmem⟩)
      have h1' : IsIso ((slcCurveNormalization T hT).stalkMap (e.base x)) :=
        h1.mp (IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _)
      have h2 : IsIso (e.stalkMap x) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1' h2
    exact key _ hne.symm
  -- a germ on `T` lifting `φᵢ`
  have hxU : x ∈ N.n i ⁻¹ᵁ U := by change (N.n i).base x ∈ U; rwa [hxz]
  obtain ⟨r, hr⟩ := hφ i x hxU
  obtain ⟨V₁, hxV₁, b₀, hb₀⟩ := T.presheaf.germ_exist
    ((inv ((N.n i).stalkMap x)).hom r)
  -- the other branches avoid a neighbourhood of `z`
  set Z : Set T := (slcCurveNormalization T hT).base '' (Set.range e.base)ᶜ with hZ
  have hZc : IsClosed Z :=
    (slcCurveNormalization T hT).isClosedMap _ e.isOpenEmbedding.isOpen_range.isClosed_compl
  have hzZ : z ∉ Z := by
    rintro ⟨w', hw'r, hw'z⟩
    exact hw'r ⟨x, hex.trans (huniq w' hw'z).symm⟩
  set V : T.Opens := V₁ ⊓ U ⊓ ⟨Zᶜ, hZc.isOpen_compl⟩ with hV
  have hzV : z ∈ V := ⟨⟨hxz ▸ hxV₁, hz⟩, hzZ⟩
  have hVV₁ : V ≤ V₁ := le_trans inf_le_left inf_le_left
  refine ⟨V, hzV, le_trans inf_le_left inf_le_right, b₀ |_ V, fun j hj => ?_⟩
  by_cases hji : j = i
  · subst hji
    have : Nonempty (N.n j ⁻¹ᵁ V₁) := ⟨⟨x, hxV₁⟩⟩
    rw [germToFunctionField_app_res N j hVV₁ b₀]
    rw [← hr]
    have h1 : ((N.X j).germToFunctionField (N.n j ⁻¹ᵁ V₁)).hom ((N.n j).app V₁ b₀) =
        algebraMap ((N.X j).presheaf.stalk x) (N.X j).functionField
          ((N.X j).presheaf.germ (N.n j ⁻¹ᵁ V₁) x hxV₁ ((N.n j).app V₁ b₀)) := by
      change _ = ((N.X j).presheaf.stalkSpecializes _).hom _
      exact (TopCat.Presheaf.germ_stalkSpecializes_apply ..).symm
    rw [h1, ← Scheme.Hom.germ_stalkMap_apply, hb₀]
    congr 1
    symm
    change ((inv ((N.n j).stalkMap x)) ≫ (N.n j).stalkMap x).hom r = r
    rw [IsIso.inv_hom_id]
    rfl
  · exfalso
    obtain ⟨⟨x', hx'⟩⟩ := hj
    apply hx'.2
    refine ⟨(Limits.Sigma.ι N.X j ≫ φe.hom).base x', ?_, ?_⟩
    · rintro ⟨x'', hx''⟩
      have h1 : (Limits.Sigma.ι N.X i).base x'' = (Limits.Sigma.ι N.X j).base x' := by
        have := congrArg φe.inv.base hx''
        simp only [he, Scheme.Hom.comp_apply] at this
        have hinv : ∀ y, φe.inv.base (φe.hom.base y) = y := fun y => by
          rw [← Scheme.Hom.comp_apply φe.hom φe.inv, Iso.hom_inv_id]; rfl
        rwa [hinv, hinv] at this
      have := (sigmaι_eq_iff N.X i j x'' x').mp h1
      exact hji (congrArg Sigma.fst this).symm
    · have h2 : (Limits.Sigma.ι N.X j ≫ φe.hom) ≫ slcCurveNormalization T hT = N.n j := by
        rw [Category.assoc, hφe, Limits.Sigma.ι_desc]
      rw [← Scheme.Hom.comp_apply, h2]

/-- In a reduced ring, `a² = a'²` and `a³ = a'³` force `a = a'`. -/
private theorem eq_of_sq_eq_of_cube_eq {S : Type*} [CommRing S] [IsReduced S] {a a' : S}
    (h2 : a ^ 2 = a' ^ 2) (h3 : a ^ 3 = a' ^ 3) : a = a' := by
  have hn : IsNilpotent (a - a') := ⟨3, by linear_combination 4 * h3 - 3 * a' * h2 - 3 * a * h2⟩
  exact sub_eq_zero.mp hn.eq_zero

/-- **Roots in a seminormal ring.** If `A ⊆ L` with `L` reduced and `A` seminormal, then
`c² ∈ A` and `c³ ∈ A` force `c ∈ A`. -/
private theorem mem_range_of_sq_cube {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    [IsReduced L]
    (hinj : Function.Injective (algebraMap A L)) (hsn : IsSeminormalRing A) {c : L}
    (h2 : c ^ 2 ∈ (algebraMap A L).range) (h3 : c ^ 3 ∈ (algebraMap A L).range) :
    c ∈ (algebraMap A L).range := by
  obtain ⟨x, hx⟩ := h2
  obtain ⟨y, hy⟩ := h3
  have hxy : x ^ 3 = y ^ 2 := hinj (by rw [map_pow, map_pow, hx, hy, ← pow_mul, ← pow_mul])
  obtain ⟨a, ⟨ha2, ha3⟩, -⟩ := hsn.existsUnique_of_cube_eq_square hxy
  exact ⟨a, eq_of_sq_eq_of_cube_eq (by rw [← map_pow, ← ha2, hx]) (by rw [← map_pow, ← ha3, hy])⟩

/-- In a seminormal subring of a reduced ring, an element all of whose high powers lie in the
subring lies in it. -/
private theorem mem_range_of_forall_pow_mem_range {A L : Type*} [CommRing A] [CommRing L]
    [Algebra A L] [IsReduced L] (hinj : Function.Injective (algebraMap A L))
    (hsn : IsSeminormalRing A) {b : L}
    (N : ℕ) (h : ∀ j, N ≤ j → b ^ j ∈ (algebraMap A L).range) :
    b ∈ (algebraMap A L).range := by
  induction N with
  | zero => simpa using h 1 (Nat.zero_le _)
  | succ N ih =>
    apply ih
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · rcases N with _ | N
      · simpa using h 1 le_rfl
      · refine mem_range_of_sq_cube hinj hsn ?_ ?_
        · rw [← pow_mul]; exact h _ (by nlinarith)
        · rw [← pow_mul]; exact h _ (by nlinarith)
    · exact h j hlt

/-- **High powers of a branch-vanishing element lie in the conductor.** Let `A` be a local
Noetherian ring and `b` integral over `A` in an `A`-algebra `L`. Suppose `b` lies generically in
`A` (away from the maximal ideal some `s ∉ p` has `s b ∈ A`) and `b` lies in every prime of
`A[b]` over the maximal ideal. Then `b^j ∈ A` for all large `j`: the conductor of `A[b]/A` is
primary to the maximal ideal, and a power of `b` lies in `m A[b]`. -/
private theorem exists_forall_pow_mem_range {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    [IsLocalRing A] [IsNoetherianRing A] {b : L} (hint : IsIntegral A b)
    (hgen : ∀ p : Ideal A, p.IsPrime → p ≠ IsLocalRing.maximalIdeal A →
      ∃ s ∉ p, algebraMap A L s * b ∈ (algebraMap A L).range)
    (hb : ∀ P : Ideal (Algebra.adjoin A {b}), P.IsPrime →
      Ideal.comap (algebraMap A (Algebra.adjoin A {b})) P = IsLocalRing.maximalIdeal A →
      (⟨b, Algebra.self_mem_adjoin_singleton A b⟩ : Algebra.adjoin A {b}) ∈ P) :
    ∃ N, ∀ j, N ≤ j → b ^ j ∈ (algebraMap A L).range := by
  set C := Algebra.adjoin A {b} with hC
  set R := (algebraMap A L).range
  -- every element of `C` is generically in `A`
  have hgen' : ∀ p : Ideal A, p.IsPrime → p ≠ IsLocalRing.maximalIdeal A → ∀ c ∈ C,
      ∃ s ∉ p, algebraMap A L s * c ∈ R := by
    intro p hp hpm c hc
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx; exact hgen p hp hpm
    | algebraMap a => exact ⟨1, hp.ne_top' ∘ fun h => (Ideal.eq_top_of_isUnit_mem _ h isUnit_one),
        ⟨a, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, hp.mul_notMem hs ht, ?_⟩
      have : algebraMap A L (s * t) * (x + y) =
          algebraMap A L t * (algebraMap A L s * x) +
            algebraMap A L s * (algebraMap A L t * y) := by
        rw [map_mul]; ring
      rw [this]
      exact R.add_mem (R.mul_mem ⟨t, rfl⟩ hsx) (R.mul_mem ⟨s, rfl⟩ hty)
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, hp.mul_notMem hs ht, ?_⟩
      have : algebraMap A L (s * t) * (x * y) =
          (algebraMap A L s * x) * (algebraMap A L t * y) := by rw [map_mul]; ring
      rw [this]
      exact R.mul_mem hsx hty
  -- the conductor
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, ∀ s, s ∈ J ↔ ∀ c ∈ C, algebraMap A L s * c ∈ R :=
    ⟨{ carrier := {s | ∀ c ∈ C, algebraMap A L s * c ∈ R}
       add_mem' := fun {s t} hs ht c hc => by
         rw [map_add, add_mul]; exact R.add_mem (hs c hc) (ht c hc)
       zero_mem' := fun c _ => by rw [map_zero, zero_mul]; exact R.zero_mem
       smul_mem' := fun a s hs c hc => by
         rw [smul_eq_mul, map_mul, mul_assoc]; exact R.mul_mem ⟨a, rfl⟩ (hs c hc) },
      fun _ => Iff.rfl⟩
  obtain ⟨G, hG⟩ := hint.fg_adjoin_singleton
  have hGC : ∀ g ∈ G, g ∈ C := fun g hg => by
    have : g ∈ Subalgebra.toSubmodule C := hG ▸ Submodule.subset_span hg
    exact this
  have hmJ : IsLocalRing.maximalIdeal A ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hJP, hP⟩ => ?_
    by_cases hPm : P = IsLocalRing.maximalIdeal A
    · exact hPm.ge
    exfalso
    classical
    choose! s hs hsg using fun g (hg : g ∈ G) => hgen' P hP hPm g (hGC g hg)
    have hprod : (∏ g ∈ G, s g) ∉ P := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨g, hg, hgP⟩
      exact hs g hg hgP
    apply hprod
    apply hJP
    rw [hJ]
    intro c hc
    have hc' : c ∈ Submodule.span A (G : Set L) := hG ▸ hc
    clear hc
    induction hc' using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase G s hx, map_mul, mul_comm (algebraMap A L (s x)), mul_assoc]
      exact R.mul_mem ⟨_, rfl⟩ (hsg x hx)
    | zero => rw [mul_zero]; exact R.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact R.add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap A L _), mul_assoc]
      exact R.mul_mem ⟨a, rfl⟩ hx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hmJ (IsNoetherian.noetherian _)
  -- `b` lies in the radical of `m C`
  set b' : C := ⟨b, Algebra.self_mem_adjoin_singleton A b⟩
  have hbrad : b' ∈ (Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.mpr fun P ⟨hmP, hP⟩ => hb P hP ?_
    have h1 : IsLocalRing.maximalIdeal A ≤ Ideal.comap (algebraMap A C) P := by
      intro x hx
      exact Ideal.mem_comap.mpr (hmP (Ideal.mem_map_of_mem (algebraMap A C) hx))
    exact le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap _).ne_top) h1
  obtain ⟨L₀, hL₀⟩ := hbrad
  refine ⟨L₀ * N, fun j hj => ?_⟩
  have hmem : b' ^ j ∈ Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A ^ N) := by
    rw [Ideal.map_pow]
    have : b' ^ (L₀ * N) ∈ Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A) ^ N := by
      rw [pow_mul]; exact Ideal.pow_mem_pow hL₀ N
    rw [← Nat.add_sub_cancel' hj, pow_add]
    exact Ideal.mul_mem_right _ _ this
  have key : ∀ x ∈ Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A ^ N), ∀ c : C,
      ((c * x : C) : L) ∈ R := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      intro c
      have := (hJ _).mp (hN hs) c c.2
      simpa [mul_comm] using this
    | zero => intro c; simpa using R.zero_mem
    | add x y _ _ hx hy => intro c; simpa [mul_add] using R.add_mem (hx c) (hy c)
    | smul c' x _ hx => intro c; simpa [smul_eq_mul, ← mul_assoc] using hx (c * c')
  simpa using key _ hmem 1

/-- The normalization of the projective scheme `T` has finitely many components. -/
private theorem finite_ι_of_isSdltAdjointPair' {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (hΔ : IsSdltAdjointPair N n Δ Θ) : Finite N.ι := by
  haveI : IsProper sT := isProper_of_isProjectiveMorphism sT hΔ.isProjectiveMorphism
  haveI : CompactSpace T := (quasiCompact_iff_compactSpace sT).mp inferInstance
  haveI : LocallyOfFiniteType sT := hΔ.isNFold.1.2.1
  obtain ⟨φ, -⟩ := N.exists_iso
  haveI : IsFinite (slcCurveNormalization T hT) :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k sT) hT
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

/-- A reduced localization of a seminormal ring is seminormal: a solution of `x³ = y²` with
denominators is rescaled to one in the ring. -/
private theorem isSeminormalRing_of_isLocalization {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] [IsReduced S] (hA : IsSeminormalRing A) :
    IsSeminormalRing S := by
  intro x y hxy
  refine existsUnique_of_exists_of_unique ?_ fun a a' ha ha' =>
    eq_of_sq_eq_of_cube_eq (ha.1.symm.trans ha'.1) (ha.2.symm.trans ha'.2)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  simp only at hxy ⊢
  have hs := IsLocalization.map_units S s
  have ht := IsLocalization.map_units S t
  have es := IsLocalization.mk'_spec S a s
  have et := IsLocalization.mk'_spec S b t
  set x := IsLocalization.mk' S a s
  set y := IsLocalization.mk' S b t
  -- clear denominators: `X = a t (s t m)²`-type rescaling
  have h1 : algebraMap A S (a ^ 3 * t ^ 2) = algebraMap A S (b ^ 2 * s ^ 3) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← es, ← et]
    linear_combination (algebraMap A S s ^ 3 * algebraMap A S t ^ 2) * hxy
  obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) h1
  set w : A := s * t
  set X : A := a * t * w * m ^ 2
  set Y : A := b * s * w ^ 2 * m ^ 3
  have hXY : X ^ 3 = Y ^ 2 := by
    simp only [X, Y, w]
    linear_combination (s ^ 3 * t ^ 4 * (m : A) ^ 5) * hm
  obtain ⟨c, ⟨hc2, hc3⟩, -⟩ := hA.existsUnique_of_cube_eq_square hXY
  have hu := IsLocalization.map_units S (s * t * m)
  obtain ⟨u, hu'⟩ := hu
  have huu : (u : S) * ↑u⁻¹ = 1 := u.mul_inv
  have hc2' : algebraMap A S c ^ 2 = algebraMap A S X := by rw [← map_pow, hc2]
  have hc3' : algebraMap A S c ^ 3 = algebraMap A S Y := by rw [← map_pow, hc3]
  refine ⟨algebraMap A S c * ↑u⁻¹, ?_, ?_⟩
  · apply (u ^ 2).isUnit.mul_left_cancel
    have e1 : ((u ^ 2 : Sˣ) : S) * (algebraMap A S c * ↑u⁻¹) ^ 2 = algebraMap A S X := by
      rw [← hc2']; push_cast; linear_combination (algebraMap A S c) ^ 2 * (↑u * ↑u⁻¹ + 1) * huu
    rw [e1]
    simp only [X, w, Units.val_pow_eq_pow_val, hu', Submonoid.coe_mul, map_mul, map_pow]
    linear_combination (algebraMap A S s * algebraMap A S t ^ 2 * algebraMap A S (m : A) ^ 2) * es
  · apply (u ^ 3).isUnit.mul_left_cancel
    have e1 : ((u ^ 3 : Sˣ) : S) * (algebraMap A S c * ↑u⁻¹) ^ 3 = algebraMap A S Y := by
      rw [← hc3']; push_cast
      linear_combination (algebraMap A S c) ^ 3 * ((↑u * ↑u⁻¹) ^ 2 + (↑u * ↑u⁻¹) + 1) * huu
    rw [e1]
    simp only [Y, w, Units.val_pow_eq_pow_val, hu', Submonoid.coe_mul, map_mul, map_pow]
    linear_combination
      (algebraMap A S s ^ 3 * algebraMap A S t ^ 2 * algebraMap A S (m : A) ^ 3) * et

/-- The local ring of `T` at a point of codimension at most one outside the double locus is a
normal domain: a field at a generic point of the reduced `T`, and a regular local ring of
dimension one, hence a discrete valuation ring, at a codimension-one point. -/
private theorem isDomain_and_isIntegrallyClosed_stalk {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) (z : T)
    (hz : Order.coheight z ≤ 1)
    (hzD : Order.coheight z = 1 → z ∉ (doubleIntersectionLocus T : Set T)) :
    IsDomain (T.presheaf.stalk z) ∧ IsIntegrallyClosed (T.presheaf.stalk z) := by
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  rcases (show Order.coheight z = 0 ∨ Order.coheight z = 1 by
    rcases eq_or_ne (Order.coheight z) 0 with h0 | h0
    · exact Or.inl h0
    · right
      refine le_antisymm hz ?_
      exact ENat.one_le_iff_ne_zero.mpr h0) with h0 | h1
  · haveI : Ring.KrullDimLE 0 (T.presheaf.stalk z) :=
      krullDimLE_of_coheight_le (by rw [h0]; rfl)
    letI := (Ring.KrullDimLE.isField_of_isReduced (R := T.presheaf.stalk z)).toField
    exact ⟨inferInstance, Field.instIsIntegrallyClosed _⟩
  · have hreg : IsRegularLocalRing (T.presheaf.stalk z) := by
      by_contra hreg
      exact hzD h1 (subset_closure ⟨h1, hreg⟩)
    haveI := hreg
    haveI := IsRegularLocalRing.isDomain (T.presheaf.stalk z)
    have hdim : ringKrullDim (T.presheaf.stalk z) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h1]; rfl
    have hnf : ¬IsField (T.presheaf.stalk z) := by
      intro hf
      letI := hf.toField
      have : ringKrullDim (T.presheaf.stalk z) = 0 := ringKrullDim_eq_zero_of_field _
      rw [hdim] at this
      exact one_ne_zero this
    have hcot : Module.finrank (IsLocalRing.ResidueField (T.presheaf.stalk z))
        (IsLocalRing.CotangentSpace (T.presheaf.stalk z)) = 1 := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace (T.presheaf.stalk z)).mp hreg
      rw [hdim] at this
      exact_mod_cast this
    haveI : IsDiscreteValuationRing (T.presheaf.stalk z) :=
      ((IsDiscreteValuationRing.TFAE (T.presheaf.stalk z) hnf).out 1 6).mpr hcot
    exact ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 1600000 in
/-- **The seminormal step.** On the seminormal `S₂` scheme `T`, a family `ψ` of rational functions
on the normalization components, regular on `ν⁻¹(W)` and vanishing at every point of the
normalization over a codimension-one point `Q ∈ W`, descends near `Q`: in the local ring
`𝒪_{T,Q}` a power of `ψ` lies in the conductor (`exists_forall_pow_mem_range`) and seminormality
extracts the root (`mem_range_of_forall_pow_mem_range`). -/
private theorem exists_descendsOn_of_forall_mem_maximalIdeal {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) {W : T.Opens}
    (ψ : ∀ i, (N.X i).functionField)
    (hψ : ∀ i, ∀ z ∈ N.n i ⁻¹ᵁ W,
      ψ i ∈ (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range)
    (Q : T) (hQW : Q ∈ W) (hQ : Order.coheight Q = 1)
    (hψQ : ∀ i (x : N.X i), (N.n i).base x = Q →
      ∃ r ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk x),
        algebraMap ((N.X i).presheaf.stalk x) (N.X i).functionField r = ψ i) :
    ∃ V : T.Opens, Q ∈ V ∧ V ≤ W ∧ DescendsOn N ψ V := by
  classical
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  haveI hfin : Finite N.ι := finite_ι_of_isSdltAdjointPair' h
  haveI := fun i => isFinite_normalizationComponent N i
  -- the branches through `Q`, with a chosen point over `Q`
  let I := {i : N.ι // ∃ x : N.X i, (N.n i).base x = Q}
  choose xI hxI using fun i : I => i.2
  have hsp : ∀ i : I, (N.n i.1).base (xI i) ⤳ Q := fun i => by rw [hxI i]
  -- the ring maps `𝒪_{T,Q} → k(Tᵢ)`
  let κ : ∀ i : I, T.presheaf.stalk Q →+* (N.X i.1).functionField := fun i =>
    (algebraMap ((N.X i.1).presheaf.stalk (xI i)) (N.X i.1).functionField).comp
      (((N.n i.1).stalkMap (xI i)).hom.comp (T.presheaf.stalkSpecializes (hsp i)).hom)
  have hκ : ∀ (V : T.Opens) (hQV : Q ∈ V) (c : Γ(T, V)) (i : I) [Nonempty (N.n i.1 ⁻¹ᵁ V)],
      κ i (T.presheaf.germ V Q hQV c) =
        ((N.X i.1).germToFunctionField (N.n i.1 ⁻¹ᵁ V)).hom ((N.n i.1).app V c) := by
    intro V hQV c i _
    have hxV : (N.n i.1).base (xI i) ∈ V := by rwa [hxI i]
    change algebraMap _ _ (((N.n i.1).stalkMap (xI i)).hom
      ((T.presheaf.stalkSpecializes (hsp i)).hom (T.presheaf.germ V Q hQV c))) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := N.X i.1)
      (U := N.n i.1 ⁻¹ᵁ V) hxV _
  letI : Algebra (T.presheaf.stalk Q) (∀ i : I, (N.X i.1).functionField) :=
    (Pi.ringHom κ).toAlgebra
  have halg : ∀ c i, algebraMap (T.presheaf.stalk Q) (∀ i : I, (N.X i.1).functionField) c i =
      κ i c := fun _ _ => rfl
  let b : ∀ i : I, (N.X i.1).functionField := fun i => ψ i.1
  have hinj : Function.Injective
      (algebraMap (T.presheaf.stalk Q) (∀ i : I, (N.X i.1).functionField)) := by
    refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
    by_contra hc0
    obtain ⟨η, hηQ, hη, hne⟩ := exists_genericPoint_stalkSpecializes_ne_zero c hc0
    obtain ⟨i, hηi, hiso⟩ := exists_base_genericPoint_eq N hη
    have hiI : ∃ x : N.X i, (N.n i).base x = Q := by
      have hcl : IsClosed (Set.range (N.n i).base) := (N.n i).isClosedMap.isClosed_range
      exact hηQ.mem_closed hcl ⟨_, hηi⟩
    set j : I := ⟨i, hiI⟩
    have h0 : κ j c = 0 := congrFun hc j
    apply hne
    subst hηi
    have hgen : genericPoint (N.X i) ⤳ xI j :=
      (genericPoint_spec (N.X i)).specializes (Set.mem_univ _)
    have e1 : κ j c = ((N.n i).stalkMap (genericPoint (N.X i))).hom
        ((T.presheaf.stalkSpecializes ((hgen.map (N.n i).continuous).trans (hsp j))).hom c) := by
      change ((N.X i).presheaf.stalkSpecializes _).hom (((N.n i).stalkMap (xI j)).hom
        ((T.presheaf.stalkSpecializes (hsp j)).hom c)) = _
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply (N.n i) _ _ hgen]
      congr 1
      rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]
    rw [e1] at h0
    apply (ConcreteCategory.bijective_of_isIso ((N.n i).stalkMap (genericPoint (N.X i)))).1
    rwa [map_zero]
  have hsn : IsSeminormalRing (T.presheaf.stalk Q) := by
    obtain ⟨U₀, hQU₀, hU₀⟩ := h.isSeminormal Q
    letI := T.presheaf.algebra_section_stalk (U := U₀.1) ⟨Q, hQU₀⟩
    haveI := U₀.2.isLocalization_stalk ⟨Q, hQU₀⟩
    exact isSeminormalRing_of_isLocalization (U₀.2.primeIdealOf ⟨Q, hQU₀⟩).asIdeal.primeCompl hU₀
  -- an affine neighbourhood of `Q` and the sections `ψ̂ᵢ` over it
  obtain ⟨W₀, hW₀, hQW₀, hW₀W⟩ : ∃ W₀ : T.Opens, IsAffineOpen W₀ ∧ Q ∈ W₀ ∧ W₀ ≤ W := by
    obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hQ', hle⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hQW W.isOpen
    exact ⟨W₀, hW₀, hQ', hle⟩
  have hne₀ : ∀ i : I, Nonempty (N.n i.1 ⁻¹ᵁ W₀) := fun i =>
    ⟨⟨xI i, show (N.n i.1).base (xI i) ∈ W₀ by rwa [hxI i]⟩⟩
  choose ψs hψs using fun i : I =>
    haveI := hne₀ i
    MMP.Intersection.exists_germToFunctionField_eq_of_forall_mem_range_stalk
      (X := N.X i.1) (N.n i.1 ⁻¹ᵁ W₀) (z := ψ i.1) fun z hz => hψ i.1 z (hW₀W hz)
  have hint : IsIntegral (T.presheaf.stalk Q) b := by
    haveI := Fintype.ofFinite I
    have hpi : ∀ i : I, ∃ p : Polynomial Γ(T, W₀), p.Monic ∧
        p.eval₂ ((N.n i.1).app W₀).hom (ψs i) = 0 := fun i =>
      IsIntegralHom.isIntegral_app (N.n i.1) W₀ hW₀ (ψs i)
    choose p hpm hp0 using hpi
    refine ⟨∏ i : I, (p i).map (T.presheaf.germ W₀ Q hQW₀).hom,
      Polynomial.monic_prod_of_monic _ _ fun i _ => (hpm i).map _, ?_⟩
    funext j
    rw [Polynomial.eval₂_finset_prod, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    have := hne₀ j
    have e := Polynomial.hom_eval₂ ((p j).map (T.presheaf.germ W₀ Q hQW₀).hom)
      (algebraMap (T.presheaf.stalk Q) (∀ i : I, (N.X i.1).functionField))
      (Pi.evalRingHom (fun i : I => (N.X i.1).functionField) j) b
    simp only [Pi.evalRingHom_apply] at e
    rw [e, Polynomial.eval₂_map]
    change Polynomial.eval₂ ((κ j).comp (T.presheaf.germ W₀ Q hQW₀).hom) (ψ j.1) (p j) = 0
    have hcomp : (κ j).comp (T.presheaf.germ W₀ Q hQW₀).hom =
        ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom.comp ((N.n j.1).app W₀).hom :=
      RingHom.ext fun c => hκ W₀ hQW₀ c j
    rw [hcomp, ← hψs j, ← Polynomial.hom_eval₂, hp0 j, map_zero]
  have hgen : ∀ p : Ideal (T.presheaf.stalk Q), p.IsPrime →
      p ≠ IsLocalRing.maximalIdeal (T.presheaf.stalk Q) →
      ∃ s ∉ p, algebraMap _ (∀ i : I, (N.X i.1).functionField) s * b ∈
        (algebraMap (T.presheaf.stalk Q) (∀ i : I, (N.X i.1).functionField)).range := by
    intro p hp hpm
    let q : PrimeSpectrum (T.presheaf.stalk Q) := ⟨p, hp⟩
    have hηQ : T.fromSpecStalk Q q ⤳ Q := Stacks.Chow.specializes_fromSpecStalk Q q
    have hη0 : Order.coheight (T.fromSpecStalk Q q) = 0 := by
      refine (Stacks.Chow.coheight_fromSpecStalk_eq_height Q q).trans ?_
      change p.height = 0
      have hdim : ringKrullDim (T.presheaf.stalk Q) = 1 := by
        rw [ringKrullDim_stalk_eq_coheight, hQ]; rfl
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
        (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) hpm)
      have h2 := Ideal.height_le_ringKrullDim_of_ne_top
        (IsLocalRing.maximalIdeal.isMaximal (T.presheaf.stalk Q)).ne_top
      rw [hdim] at h2
      have h3 : (IsLocalRing.maximalIdeal (T.presheaf.stalk Q)).height ≤ 1 := by exact_mod_cast h2
      have h4 := h1.trans h3
      exact (ENat.add_one_le_iff (by intro h; simp [h] at h4)).mp h4 |> ENat.lt_one_iff_eq_zero.mp
    generalize hηdef : T.fromSpecStalk Q q = η at hηQ hη0
    obtain ⟨hd, hic⟩ := isDomain_and_isIntegrallyClosed_stalk h η
      (by rw [hη0]; exact zero_le_one) (fun h1 => by rw [hη0] at h1; exact absurd h1 zero_ne_one)
    have hηW : η ∈ W := hηQ.mem_open W.isOpen hQW
    obtain ⟨Vη, hηV, -, cη, hcη⟩ := exists_descendsOn_of_isIntegrallyClosed h ψ hψ η hηW
    have hηW₀ : η ∈ W₀ := hηQ.mem_open W₀.isOpen hQW₀
    obtain ⟨s, hsV, hηs⟩ := hW₀.exists_basicOpen_le ⟨η, hηV⟩ hηW₀
    obtain ⟨n', a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen T W₀ hW₀ s (cη |_ T.basicOpen s)
    set gs := T.presheaf.germ W₀ Q hQW₀ s
    set ga := T.presheaf.germ W₀ Q hQW₀ a
    refine ⟨gs ^ (n' + 1), ?_, ⟨gs * ga, ?_⟩⟩
    · intro hmem
      have hsp : gs ∈ p := hp.mem_of_pow_mem _ hmem
      letI := (T.presheaf.stalkSpecializes hηQ).hom.toAlgebra
      haveI := Stacks.Chow.isLocalization_stalk_of_specializes hηQ q hηdef
      have hu : IsUnit (algebraMap (T.presheaf.stalk Q) (T.presheaf.stalk η) gs) := by
        change IsUnit ((T.presheaf.stalkSpecializes hηQ).hom gs)
        rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
        exact (T.mem_basicOpen s η hηW₀).mp hηs
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ p _).mp hu) hsp
    · funext j
      change κ j (gs * ga) = κ j (gs ^ (n' + 1)) * ψ j.1
      have hj0 := hne₀ j
      rw [map_mul, map_pow]
      have hs1 : κ j gs = ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom
          ((N.n j.1).app W₀ s) := hκ W₀ hQW₀ s j
      have ha1 : κ j ga = ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom
          ((N.n j.1).app W₀ a) := hκ W₀ hQW₀ a j
      by_cases hj : Nonempty (N.n j.1 ⁻¹ᵁ T.basicOpen s)
      · have hVj : Nonempty (N.n j.1 ⁻¹ᵁ Vη) := ⟨⟨hj.some.1, hsV hj.some.2⟩⟩
        have hψj : ψ j.1 = ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ T.basicOpen s)).hom
            ((N.n j.1).app _ (cη |_ T.basicOpen s)) := by
          rw [germToFunctionField_app_res N j.1 hsV cη]; exact hcη j.1 hVj
        rw [hs1, ha1, ← germToFunctionField_app_res N j.1 (T.basicOpen_le s) s,
          ← germToFunctionField_app_res N j.1 (T.basicOpen_le s) a, ha, hψj, map_mul, map_mul,
          map_pow, map_pow]
        ring
      · have hs0 : (N.n j.1).app W₀ s = 0 := by
          rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
          exact eq_bot_iff.mpr fun x hx => hj ⟨⟨x, hx⟩⟩
        rw [hs1, hs0, map_zero]
        ring
  have hbP : ∀ P : Ideal (Algebra.adjoin (T.presheaf.stalk Q) {b}), P.IsPrime →
      Ideal.comap (algebraMap (T.presheaf.stalk Q) (Algebra.adjoin (T.presheaf.stalk Q) {b})) P =
        IsLocalRing.maximalIdeal (T.presheaf.stalk Q) →
      (⟨b, Algebra.self_mem_adjoin_singleton _ b⟩ :
        Algebra.adjoin (T.presheaf.stalk Q) {b}) ∈ P := by
    intro P hP hPm
    haveI := hP
    haveI := Fintype.ofFinite I
    let C := Algebra.adjoin (T.presheaf.stalk Q) {b}
    let πj : ∀ j : I, C →+* (N.X j.1).functionField := fun j =>
      (Pi.evalRingHom (fun i : I => (N.X i.1).functionField) j).comp C.val.toRingHom
    -- a branch whose kernel lies in `P`
    obtain ⟨j, hj⟩ : ∃ j : I, RingHom.ker (πj j) ≤ P := by
      have hinf : (Finset.univ.inf fun j => RingHom.ker (πj j)) ≤ P := by
        intro x hx
        have hx0 : x = 0 := by
          apply Subtype.ext
          funext j'
          have := (Finset.inf_le (f := fun j => RingHom.ker (πj j)) (Finset.mem_univ j')) hx
          exact this
        rw [hx0]; exact P.zero_mem
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.inf_le' hP).mp hinf
      exact ⟨j, hj⟩
    letI : Algebra C (N.X j.1).functionField := (πj j).toAlgebra
    have hπ : ∀ a, algebraMap C (N.X j.1).functionField
        (algebraMap (T.presheaf.stalk Q) C a) = κ j a := fun _ => rfl
    let D := integralClosure C (N.X j.1).functionField
    obtain ⟨P'', -, hP''p, hP''⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := D) P ⊥
      (by
        intro x hx
        apply hj
        change algebraMap C (N.X j.1).functionField x = 0
        have : algebraMap C D x = 0 := hx
        have := congrArg Subtype.val this
        exact this)
    haveI := hP''p
    -- sections over `νⱼ⁻¹ W₀` land in the integral closure
    have hSD : ∀ t : Γ(N.X j.1, N.n j.1 ⁻¹ᵁ W₀),
        IsIntegral C (((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom t) := by
      intro t
      have := hne₀ j
      obtain ⟨p, hpm, hp0⟩ := IsIntegralHom.isIntegral_app (N.n j.1) W₀ hW₀ t
      refine ⟨p.map ((algebraMap (T.presheaf.stalk Q) C).comp (T.presheaf.germ W₀ Q hQW₀).hom),
        hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap C (N.X j.1).functionField).comp
          ((algebraMap (T.presheaf.stalk Q) C).comp (T.presheaf.germ W₀ Q hQW₀).hom) =
          ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom.comp ((N.n j.1).app W₀).hom :=
        RingHom.ext fun c => (hπ _).trans (hκ W₀ hQW₀ c j)
      rw [hcomp, ← Polynomial.hom_eval₂, hp0, map_zero]
    let θS : Γ(N.X j.1, N.n j.1 ⁻¹ᵁ W₀) →+* D :=
      ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom.codRestrict D hSD
    let q := Ideal.comap θS P''
    haveI hqp : q.IsPrime := Ideal.comap_isPrime θS P''
    have hV : IsAffineOpen (N.n j.1 ⁻¹ᵁ W₀) := hW₀.preimage (N.n j.1)
    let y := hV.fromSpec ⟨q, hqp⟩
    have hyV : y ∈ N.n j.1 ⁻¹ᵁ W₀ := by
      have : y ∈ Set.range hV.fromSpec.base := ⟨_, rfl⟩
      rwa [hV.range_fromSpec] at this
    have hprime : hV.primeIdealOf ⟨y, hyV⟩ = ⟨q, hqp⟩ :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨y, hyV⟩)
    -- the contraction of `q` to `W₀` is the prime of `Q`
    have hcomp : θS.comp ((N.n j.1).app W₀).hom = (algebraMap C D).comp
        ((algebraMap (T.presheaf.stalk Q) C).comp (T.presheaf.germ W₀ Q hQW₀).hom) := by
      haveI := hne₀ j
      exact RingHom.ext fun c => Subtype.ext ((hκ W₀ hQW₀ c j).symm.trans (hπ _).symm)
    have hcomapQ : q.comap ((N.n j.1).app W₀).hom = (hW₀.primeIdealOf ⟨Q, hQW₀⟩).asIdeal := by
      change Ideal.comap ((N.n j.1).app W₀).hom (Ideal.comap θS P'') = _
      rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, ← Ideal.comap_comap, ← Ideal.under_def _ P'', hP'', hPm,
        hW₀.primeIdealOf_eq_map_closedPoint]
      rfl
    have hνy : (N.n j.1).base y = Q := by
      have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := N.n j.1) (x := y) W₀ hW₀
        (N.n j.1 ⁻¹ᵁ W₀) hV le_rfl hyV
      rw [hprime, ← Scheme.Hom.app_eq_appLE] at h1
      have h2 : hW₀.primeIdealOf ⟨(N.n j.1).base y, hyV⟩ = hW₀.primeIdealOf ⟨Q, hQW₀⟩ := by
        rw [← h1]; ext1; exact hcomapQ
      have := congrArg hW₀.fromSpec.base h2
      rwa [hW₀.fromSpec_primeIdealOf, hW₀.fromSpec_primeIdealOf] at this
    -- `ψ̂ⱼ` vanishes at `y`, so lies in `q`
    have hψq : ψs j ∈ q := by
      obtain ⟨r, hrm, hr⟩ := hψQ j.1 y hνy
      haveI := hne₀ j
      have hgerm : (N.X j.1).presheaf.germ _ y hyV (ψs j) = r :=
        IsFractionRing.injective ((N.X j.1).presheaf.stalk y) (N.X j.1).functionField (by
          rw [hr, Scheme.algebraMap_germ_eq_germToFunctionField, hψs j])
      have hny : y ∉ (N.X j.1).basicOpen (ψs j) := fun hy => by
        have := ((N.X j.1).mem_basicOpen (ψs j) y hyV).mp hy
        rw [hgerm] at this
        exact (IsLocalRing.mem_maximalIdeal _).mp hrm this
      by_contra hq
      apply hny
      have hmem : (⟨q, hqp⟩ : PrimeSpectrum Γ(N.X j.1, N.n j.1 ⁻¹ᵁ W₀)) ∈
          PrimeSpectrum.basicOpen (ψs j) := hq
      rwa [← hV.fromSpec_preimage_basicOpen] at hmem
    have h2 : θS (ψs j) = algebraMap C D
        ⟨b, Algebra.self_mem_adjoin_singleton _ b⟩ := by
      apply Subtype.ext
      change ((N.X j.1).germToFunctionField (N.n j.1 ⁻¹ᵁ W₀)).hom (ψs j) = b j
      exact hψs j
    rw [← hP'']
    change algebraMap C D ⟨b, _⟩ ∈ P''
    rwa [← h2]
  obtain ⟨N₀, hN₀⟩ := exists_forall_pow_mem_range hint hgen hbP
  obtain ⟨c, hc⟩ := mem_range_of_forall_pow_mem_range hinj hsn N₀ hN₀
  obtain ⟨V₁, hQV₁, c₀, hc₀⟩ := T.presheaf.germ_exist c
  -- the components not through `Q` avoid a neighbourhood of `Q`
  set Z : Set T := ⋃ i ∈ {i : N.ι | ¬ ∃ x : N.X i, (N.n i).base x = Q}, Set.range (N.n i).base
  have hZ : IsClosed Z := by
    refine Set.Finite.isClosed_biUnion (Set.toFinite _) fun i _ => ?_
    exact (N.n i).isClosedMap.isClosed_range
  have hQZ : Q ∉ Z := by
    simp only [Z, Set.mem_iUnion, Set.mem_range, Set.mem_setOf_eq]
    rintro ⟨i, hi, x, hx⟩
    exact hi ⟨x, hx⟩
  set V : T.Opens := V₁ ⊓ W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hVV₁ : V ≤ V₁ := le_trans inf_le_left inf_le_left
  refine ⟨V, ⟨⟨hQV₁, hQW⟩, hQZ⟩, le_trans inf_le_left inf_le_right, c₀ |_ V, fun i hi => ?_⟩
  have hiI : ∃ x : N.X i, (N.n i).base x = Q := by
    by_contra hiI
    obtain ⟨⟨y, hy⟩⟩ := hi
    exact hy.2 (Set.mem_biUnion hiI ⟨y, rfl⟩)
  have hi₁ : Nonempty (N.n i ⁻¹ᵁ V₁) := ⟨⟨hi.some.1, hVV₁ hi.some.2⟩⟩
  rw [germToFunctionField_app_res N i hVV₁ c₀]
  have e1 := hκ V₁ hQV₁ c₀ ⟨i, hiI⟩
  rw [hc₀] at e1
  rw [← e1, ← halg, hc]

/-- **Descent at a codimension-one double point** (the seminormal step). At a codimension-one
point `Q` of the double locus, the seminormal local ring `𝒪_{T,Q}` contains every element of its
normalization vanishing at all branches over `Q`. So a family `φ` regular on `ν⁻¹(U)` with a
common value at the branches over `Q` descends near `Q`. -/
private theorem exists_descendsOn_of_mem_doubleIntersectionLocus {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) {U : T.Opens}
    (φ : ∀ i, (N.X i).functionField)
    (hφ : ∀ i, ∀ z ∈ N.n i ⁻¹ᵁ U,
      φ i ∈ (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range)
    (Q : T) (hQU : Q ∈ U) (hQ : Order.coheight Q = 1)
    (hglue : ∃ (V : T.Opens) (hQV : Q ∈ V) (a : Γ(T, V)), ∀ i (x : N.X i)
        (hx : (N.n i).base x = Q),
        haveI : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨x, show (N.n i).base x ∈ V from hx ▸ hQV⟩⟩
        ∃ r ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk x),
          algebraMap ((N.X i).presheaf.stalk x) (N.X i).functionField r =
            φ i - ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V a)) :
    ∃ V : T.Opens, Q ∈ V ∧ V ≤ U ∧ DescendsOn N φ V := by
  classical
  obtain ⟨V', hQV', a, ha⟩ := hglue
  set g : ∀ i, (N.X i).functionField := fun i =>
    if hi : Nonempty (N.n i ⁻¹ᵁ V') then
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V')).hom ((N.n i).app V' a) else 0 with hgdef
  have hg : ∀ i (hi : Nonempty (N.n i ⁻¹ᵁ V')),
      g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V')).hom ((N.n i).app V' a) :=
    fun i hi => by rw [hgdef]; exact dif_pos hi
  have hψ : ∀ i, ∀ z ∈ N.n i ⁻¹ᵁ (U ⊓ V'), φ i - g i ∈
      (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range := by
    intro i z hz
    have hi : Nonempty (N.n i ⁻¹ᵁ V') := ⟨⟨z, hz.2⟩⟩
    obtain ⟨r, hr⟩ := hφ i z hz.1
    refine ⟨r - (N.X i).presheaf.germ (N.n i ⁻¹ᵁ V') z hz.2 ((N.n i).app V' a), ?_⟩
    rw [map_sub, hr, hg i hi]
    congr 1
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := N.X i) (U := N.n i ⁻¹ᵁ V') hz.2 _
  have hψQ : ∀ i (x : N.X i), (N.n i).base x = Q →
      ∃ r ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk x),
        algebraMap ((N.X i).presheaf.stalk x) (N.X i).functionField r = φ i - g i := by
    intro i x hx
    have hi : Nonempty (N.n i ⁻¹ᵁ V') := ⟨⟨x, show (N.n i).base x ∈ V' from hx ▸ hQV'⟩⟩
    rw [hg i hi]
    exact ha i x hx
  obtain ⟨V, hQV, hVle, b, hb⟩ := exists_descendsOn_of_forall_mem_maximalIdeal h
    (fun i => φ i - g i) hψ Q ⟨hQU, hQV'⟩ hQ hψQ
  have hVV' : V ≤ V' := hVle.trans inf_le_right
  refine ⟨V, hQV, hVle.trans inf_le_left, b + a |_ V, fun i hi => ?_⟩
  have hi' : Nonempty (N.n i ⁻¹ᵁ V') := ⟨⟨hi.some.1, hVV' hi.some.2⟩⟩
  have e1 := hb i hi
  rw [map_add, map_add, germToFunctionField_app_res N i hVV' a, ← hg i hi', ← e1]
  ring

/-- The preimage in a normalization component of an open containing every generic point of an
open `U ⊇ V` with `νᵢ⁻¹(U) ≠ ∅` is non-empty. -/
private theorem nonempty_preimage_of_coheight_eq_zero {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    [IsReduced T] (N : NormalizationComponents sT hT) (i : N.ι) {U W : T.Opens}
    (hW : ∀ z ∈ U, Order.coheight z = 0 → z ∈ W) (hU : Nonempty (N.n i ⁻¹ᵁ U)) :
    Nonempty (N.n i ⁻¹ᵁ W) := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  have hη : (N.n i).base (genericPoint (N.X i)) ∈ U :=
    (((genericPoint_spec (N.X i)).specializes (Set.mem_univ x)).map
      (N.n i).continuous).mem_open U.isOpen hx
  exact ⟨⟨_, hW _ hη (Order.coheight_eq_zero.mpr (isMax_base_genericPoint N i))⟩⟩

/-- **Step 3: descent through the conductor and extension over codimension two.** A family of
rational functions `φᵢ` on the normalization components, regular on `ν⁻¹(U)` and having a common
value at the branches over every codimension-one point of the double locus in `U`, is, near every
point of `U`, the pull-back of a function on `T`: such functions glue on an open subset of `U`
containing all codimension-one points, and extend over its complement since `T` is `S₂`. -/
private theorem exists_section_of_forall_coheight_eq_one {k : Type} [Field k]
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ) {U : T.Opens}
    (φ : ∀ i, (N.X i).functionField)
    (hφ : ∀ i, ∀ z ∈ N.n i ⁻¹ᵁ U,
      φ i ∈ (algebraMap ((N.X i).presheaf.stalk z) (N.X i).functionField).range)
    (hglue : ∀ Q ∈ U, Order.coheight Q = 1 → Q ∈ (doubleIntersectionLocus T : Set T) →
      ∃ (V : T.Opens) (hQV : Q ∈ V) (a : Γ(T, V)), ∀ i (x : N.X i)
        (hx : (N.n i).base x = Q),
        haveI : Nonempty (N.n i ⁻¹ᵁ V) := ⟨⟨x, show (N.n i).base x ∈ V from hx ▸ hQV⟩⟩
        ∃ r ∈ IsLocalRing.maximalIdeal ((N.X i).presheaf.stalk x),
          algebraMap ((N.X i).presheaf.stalk x) (N.X i).functionField r =
            φ i - ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ V)).hom ((N.n i).app V a))
    (x : T) (hx : x ∈ U) :
    ∃ (U' : T.Opens) (_ : x ∈ U') (_ : U' ≤ U) (f : Γ(T, U')),
      ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
        φ i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' f) := by
  haveI : IsReduced T := h.isBoundary.2.1
  haveI : LocallyOfFiniteType sT := h.isNFold.1.2.1
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  set W : T.Opens := ⨆ V : {V : T.Opens // V ≤ U ∧ DescendsOn N φ V}, V.1 with hWdef
  have hWU : W ≤ U := iSup_le fun V => V.2.1
  have hlocal : ∀ z ∈ U, (∃ V : T.Opens, z ∈ V ∧ V ≤ U ∧ DescendsOn N φ V) → z ∈ W :=
    fun z _ ⟨V, hzV, hVU, hV⟩ => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVU, hV⟩, hzV⟩
  have hcodim1 : ∀ z ∈ U, Order.coheight z ≤ 1 → z ∈ W := by
    intro z hz hz1
    by_cases hD : Order.coheight z = 1 ∧ z ∈ (doubleIntersectionLocus T : Set T)
    · exact hlocal z hz (exists_descendsOn_of_mem_doubleIntersectionLocus h φ hφ z hz hD.1
        (hglue z hz hD.1 hD.2))
    · obtain ⟨h1, h2⟩ := isDomain_and_isIntegrallyClosed_stalk h z hz1
        fun h1 h2 => hD ⟨h1, h2⟩
      exact hlocal z hz (exists_descendsOn_of_isIntegrallyClosed h φ hφ z hz)
  have hcodim : ∀ z ∈ U, z ∉ W → 2 ≤ ringKrullDim (T.presheaf.stalk z) := by
    intro z hz hzW
    rw [ringKrullDim_stalk_eq_coheight]
    by_contra hlt
    have : Order.coheight z ≤ 1 := by
      have h2 : ((Order.coheight z : ℕ∞) : WithBot ℕ∞) < ((2 : ℕ∞) : WithBot ℕ∞) :=
        not_le.mp hlt
      have h3 : Order.coheight z < 2 := WithBot.coe_lt_coe.mp h2
      exact Order.le_of_lt_succ h3
    exact hzW (hcodim1 z hz this)
  obtain ⟨bW, hbW⟩ := descendsOn_iSup (fun V : {V : T.Opens // V ≤ U ∧ DescendsOn N φ V} => V.1)
    fun V => V.2.2
  obtain ⟨f, hf⟩ := (bijective_presheaf_map_of_satisfiesS2 h.satisfiesS2 hWU hcodim).2 bW
  refine ⟨U, hx, le_rfl, f, fun i hi => ?_⟩
  have hiW : Nonempty (N.n i ⁻¹ᵁ W) := nonempty_preimage_of_coheight_eq_zero N i
    (fun z hz hz0 => hcodim1 z hz (by rw [hz0]; exact zero_le_one)) hi
  rw [hbW i hiW, ← hf]
  exact germToFunctionField_app_res N i hWU f

/-- **Local descent relative to a given generator.** Under the hypotheses of the theorem, let `t`
be the family of rational forms on the normalization with `p_i^* t_i = s_i` for a preadmissible
system `s`. For every local generator `g` of `𝒪_T(mL)` on an open `U` whose residues are pulled
back from the double locus, `t` is, near every point of `U`, a function on `T` times `g`. -/
private theorem exists_local_descent_of_isResidueGenerator {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C n m)
    (hm : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsResidueGenerator N n m Θ U g)
    (s : ∀ i, logPluricanonicalSections (p i ≫ N.n i ≫ sT) n m (C i))
    (hs : s ∈ preadmissibleSections R) (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
    (ht : ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) {U : T.Opens}
    {g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m} (hg : IsResidueGenerator N n m Θ U g)
    (x : T) (hxU : x ∈ U) :
    ∃ (U' : T.Opens) (_ : x ∈ U') (_ : U' ≤ U) (f : Γ(T, U')),
      ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
        t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' f) • g i := by
  choose φ hφt hφ using fun i =>
    haveI := (R.setting.isPair i).charZero
    exists_regular_smul_eq i (p i) (hproj i) (hcrep i) (hg.1.1 i) (s i) (t i) (ht i)
      (h.exists_isDltPair i).choose_spec.1.2.1.topologicalKrullDim_eq
  have hglue := fun Q hQU hQ hQD => exists_common_value_of_mem_preadmissibleSections h p hproj
    hcrep R hm s hs t ht hg φ hφt hφ Q hQU hQ hQD
  obtain ⟨U', hxU', hU', f, hf⟩ := exists_section_of_forall_coheight_eq_one h φ hφ hglue x hxU
  exact ⟨U', hxU', hU', f, fun i hi => by rw [hφt i, hf i hi]⟩

/-- **Local descent.** Under the hypotheses of the theorem, the family `t` of rational forms on
the normalization with `p_i^* t_i = s_i` for a preadmissible system `s` is, near every point of
`T`, a function on `T` times a local generator. -/
private theorem exists_local_descent {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C n m)
    (hm : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsResidueGenerator N n m Θ U g)
    (s : ∀ i, logPluricanonicalSections (p i ≫ N.n i ≫ sT) n m (C i))
    (hs : s ∈ preadmissibleSections R) (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
    (ht : ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) (x : T) :
    ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
      (f : Γ(T, U)), IsResidueGenerator N n m Θ U g ∧
        ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
          t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) • g i := by
  obtain ⟨U, hxU, g, hg⟩ := hm x
  obtain ⟨U', hxU', hU', f, hf⟩ :=
    exists_local_descent_of_isResidueGenerator h p hproj hcrep R hm s hs t ht hg x hxU
  exact ⟨U', hxU', g, f, hg.mono hU', hf⟩

/-- **Preadmissibility gives actual conductor descent.** Let `(T, Δ; L)` be an sdlt adjoint pair
of dimension `n` (`MMP.Fourfold.IsSdltAdjointPair`) with normalization components `νᵢ : Tᵢ ⟶ T`
and boundaries `Θᵢ = Cᵢ + Δᵢ`. Let `pᵢ : Yᵢ ⟶ Tᵢ` be projective birational morphisms with `Cᵢ`
the crepant boundary of `(Tᵢ, Θᵢ)` on `Yᵢ` (`MMP.Mori.IsCrepantBoundary`), and let `R` be a
residue-restriction system for the dlt pairs `(Yᵢ, Cᵢ)` in an even degree `m`
(`MMP.Fourfold.ResidueRestriction`) such that `𝒪_T(mL)` has local generators around every point
(`MMP.Fourfold.IsAdjointGeneratorOn`) whose residue along every conductor component, including one
glued to itself, is pulled back from the double locus (`MMP.Fourfold.IsLogResiduePresentation`).
Then
* every preadmissible system `s ∈ MMP.Fourfold.preadmissibleSections R` is, componentwise, the
  pull-back `pᵢ^* tᵢ` of a unique section `t` of `𝒪_T(mL)`, i.e. of a unique family `t` of
  rational `m`-canonical forms on the `Tᵢ` which near every point of `T` is `ν^*f · g` for a
  function `f` and a local generator `g`; moreover, near every point of `U`, this `t` is
  `ν^*f · g` for a function `f` and ANY given local generator `g` of `𝒪_T(mL)` on `U`;
* if preadmissible systems generate `𝒪_{Yᵢ}(m(K_{Yᵢ} + Cᵢ))` at every point of every `Yᵢ`,
  then for every point `x ∈ T` there is a preadmissible system whose descended section is, near
  `x`, a unit times a local generator of `𝒪_T(mL)`. -/
@[mmp "lem_fourfold_preadmissible_conductor_descent"]
public theorem IsSdltAdjointPair.existsUnique_pullback_eq_of_mem_preadmissibleSections
    {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n : ℕ} {Δ : QWeilDivisor T}
    {Θ : ∀ i, QDivisor (N.X i)} (h : IsSdltAdjointPair N n Δ Θ)
    {Y : N.ι → Scheme.{0}} [∀ i, IsIntegral (Y i)] [∀ i, IsLocallyNoetherian (Y i)]
    [∀ i, IsNormal (Y i)] (p : ∀ i, Y i ⟶ N.X i) [∀ i, IsDominant (p i)]
    (hproj : ∀ i, IsProjectiveMorphism (p i)) {C : ∀ i, QDivisor (Y i)}
    (hcrep : ∀ i, ∃ (K : Divisor (N.X i)) (hY : IsNormalVariety k (p i ≫ N.n i ≫ sT))
      (hp : IsBirationalMorphism (p i)),
      IsCrepantBoundary (N.n i ≫ sT) n K (Θ i) (p i) hY hp (C i))
    {m : ℕ} (R : ResidueRestriction (fun i => p i ≫ N.n i ≫ sT) C n m)
    (hm : ∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      IsAdjointGeneratorOn N n m Θ U g ∧
        ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
          (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
          ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
            (g' : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g' 1 (g i)) :
    (∀ s ∈ preadmissibleSections R,
      (∃! t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m,
        (∀ x : T, ∃ (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
          (f : Γ(T, U)), (IsAdjointGeneratorOn N n m Θ U g ∧
              ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
                (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
                ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
                  (a : Fin (n - 1) → Γ(T, V)) (g' : Γ(T, V)),
                  IsLogResiduePresentation N n m i P V hP a g' 1 (g i)) ∧
            ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
              t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) • g i) ∧
        ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) ∧
      ∀ t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m,
        (∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) →
        ∀ (U : T.Opens) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
          (IsAdjointGeneratorOn N n m Θ U g ∧
            ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
              (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
              ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V)
                (a : Fin (n - 1) → Γ(T, V)) (g' : Γ(T, V)),
                IsLogResiduePresentation N n m i P V hP a g' 1 (g i)) →
          ∀ x ∈ U, ∃ (U' : T.Opens) (_ : x ∈ U') (_ : U' ≤ U) (f : Γ(T, U')),
            ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
              t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' f) • g i) ∧
    ((∀ (i : N.ι) (y : Y i), ∃ s ∈ preadmissibleSections R, ∃ V : (Y i).Opens, y ∈ V ∧
        GeneratesOn (C i) m V ((s i : logPluricanonicalSections (p i ≫ N.n i ≫ sT) n m (C i)) :
          RationalPluriForms (p i ≫ N.n i ≫ sT) n m)) →
      ∀ x : T, ∃ s ∈ preadmissibleSections R, ∃ (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m)
        (U : T.Opens) (_ : x ∈ U) (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m) (f : Γ(T, U)),
        IsUnit f ∧ (IsAdjointGeneratorOn N n m Θ U g ∧
          ∀ i (P : Mori.PrimeDivisor (N.X i)), (N.n i).base P.genericPoint ∈ U →
            (N.n i).base P.genericPoint ∈ (doubleIntersectionLocus T : Set T) →
            ∃ (V : T.Opens) (hP : (N.n i).base P.genericPoint ∈ V) (a : Fin (n - 1) → Γ(T, V))
              (g' : Γ(T, V)), IsLogResiduePresentation N n m i P V hP a g' 1 (g i)) ∧
        (∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
          t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) • g i) ∧
        ∀ i, pullbackRationalPluriForms (N.n i ≫ sT) (p i) (t i) = (s i : _)) := by
  have hbij : ∀ i, Function.Bijective
      (pullbackRationalPluriForms (d := n) (m := (m : ℤ)) (N.n i ≫ sT) (p i)) := by
    intro i
    haveI := (R.setting.isPair i).charZero
    obtain ⟨-, -, hp, -⟩ := hcrep i
    haveI : LocallyOfFiniteType (N.n i ≫ sT) := (N.isNormalVariety i).1.toLocallyOfFiniteType
    obtain ⟨K', hK'⟩ := h.exists_isDltPair i
    exact pullbackRationalPluriForms_bijective _ hK'.1.2.1.topologicalKrullDim_eq (p i) hp m
  refine ⟨fun s hs => ?_, fun hgen x => ?_⟩
  · choose t ht using fun i => (hbij i).2 (s i : _)
    refine ⟨⟨t, ⟨exists_local_descent h p hproj hcrep R hm s hs t ht, ht⟩, ?_⟩, ?_⟩
    · rintro t' ⟨-, ht'⟩
      exact funext fun i => (hbij i).1 ((ht' i).trans (ht i).symm)
    · intro t' ht' U g hg x hxU
      exact exists_local_descent_of_isResidueGenerator h p hproj hcrep R hm s hs t' ht' hg x hxU
  · obtain ⟨i, z, hz⟩ := exists_base_eq N x
    haveI := isProper_of_isProjectiveMorphism (p i) (hproj i)
    obtain ⟨y, rfl⟩ := (p i).surjective z
    obtain ⟨s, hs, V, hyV, hsV⟩ := hgen i y
    choose t ht using fun i => (hbij i).2 (s i : _)
    obtain ⟨U, hxU, g, f, hg, htf⟩ := exists_local_descent h p hproj hcrep R hm s hs t ht x
    subst hz
    have hne : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨_, hxU⟩⟩
    haveI := (R.setting.isPair i).charZero
    have hxf := mem_basicOpen_of_generatesOn (p i) (hcrep i) (hg.1.1 i) f y hyV hxU
      (by rwa [← htf i hne, ht i])
    refine ⟨s, hs, t, T.basicOpen f, hxf, g, f |_ T.basicOpen f,
      T.toRingedSpace.isUnit_res_basicOpen f, hg.mono (T.basicOpen_le f), fun j hj => ?_, ht⟩
    have : Nonempty (N.n j ⁻¹ᵁ U) :=
      ⟨⟨hj.some.1, T.basicOpen_le f hj.some.2⟩⟩
    rw [germToFunctionField_app_res N j (T.basicOpen_le f) f]
    exact htf j this

end MMP.Fourfold
