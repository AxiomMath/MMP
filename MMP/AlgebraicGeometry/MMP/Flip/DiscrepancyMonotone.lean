module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.Combinatorics.WeightedGraph.ChainDeterminant

/-!
# Discrepancies do not decrease under flips

Let `(X, D)` be a log variety with canonical divisor `K_X` and `K_X + D` `ℝ`-Cartier, let
`f : X ⟶ Z` be a small birational contraction with `-(K_X + D)` `f`-ample, and let
`(f⁺ : X⁺ ⟶ Z, φ : X ⤏ X⁺)` be a flip of `f` with respect to `K_X + D`, with `D⁺ = φ_* D`.
Then `a(B, X⁺, D⁺) ≥ a(B, X, D)` for every divisor `B` of `k(X)` with nonempty center on `Z`.

## Main results

* `MMP.Flips.IsFlip.isDiscrepancy_le`: discrepancies do not decrease under flips.

## Implementation notes

The function fields `k(X)`, `k(Z)`, `k(X⁺)` are identified through the birational morphisms `f`
and `f⁺`: a valuation `B` of `k(X)` and a valuation `B⁺` of `k(X⁺)` are the same divisor when their
restrictions to `k(Z)` agree, and the center of `B` on `Z` is that of its restriction to `k(Z)`.
Discrepancies are the predicate `MMP.Flips.IsDiscrepancy`, which does not depend on the choice of
canonical divisor, so the canonical divisor `K⁺` of `X⁺` is arbitrary.

The base field is assumed perfect (the source works over `ℂ`). Over a perfect field every
divisorial valuation ring of `k(X)` is smooth over `k`, so `Ω^n` of it is free of rank one and the
order of a top form along a divisor is defined; over an imperfect field this fails, and the
discrepancy is no longer independent of the choice of canonical divisor.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.27
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP MMP.Mori

/-! ### Small birational contractions -/

section Small

variable {k : Type u} [Field k] {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}

/-- A small birational contraction preserves the coheight of every point of coheight at most
one: such a point lies outside the exceptional set. -/
private theorem coheight_map_eq_of_isSmall [IsNormal Z] (hf : IsSmall k sZ sX f) {x : X}
    (hx : Order.coheight x ≤ 1) : Order.coheight (f x) = Order.coheight x := by
  have h := (isSmall_iff_two_le_closedsCodimension_exceptionalSet
    hf.toIsBirationalContraction).mp hf
  rw [le_closedsCodimension_iff_le_coheight] at h
  refine coheight_map_of_notMem_exceptionalSet fun hxe => ?_
  exact absurd ((h x hxe).trans hx) (by norm_num)

/-- A small birational contraction is injective on the points of coheight at most one. -/
private theorem eq_of_apply_eq_of_isSmall (hf : IsSmall k sZ sX f) {x y : X}
    (hx : Order.coheight x ≤ 1) (hy : Order.coheight y ≤ 1) (h : f x = f y) : x = y := by
  obtain ⟨-, V, W, hV, -, hVW, hiso⟩ := hf
  rw [le_closedsCodimension_iff_le_coheight] at hV
  have hxV : x ∈ V.compl := fun hxV => absurd ((hV x hxV).trans hx) (by norm_num)
  have hyV : y ∈ V.compl := fun hyV => absurd ((hV y hyV).trans hy) (by norm_num)
  set U : X.Opens := V.compl
  set U' : Z.Opens := W.compl
  have key : ∀ z : U.toScheme, U'.ι (f.resLE U' U hVW z) = f z.1 := by
    intro z
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
    rfl
  exact congrArg Subtype.val ((f.resLE U' U hVW).isOpenEmbedding.injective
    (U'.ι.isOpenEmbedding.injective ((key ⟨x, hxV⟩).trans (h.trans (key ⟨y, hyV⟩).symm))))

/-- Over a point of coheight one, a small birational contraction has a point of coheight one. -/
private theorem exists_apply_eq_of_isSmall [IsNormal Z] (hf : IsSmall k sZ sX f) {z : Z}
    (hz : Order.coheight z = 1) : ∃ x, Order.coheight x = 1 ∧ f x = z := by
  obtain ⟨x, rfl⟩ := hf.toIsBirationalContraction.surjective_and_isBirational.1.surj z
  have hle : Order.coheight x ≤ 1 := hz ▸ coheight_le_coheight_map sZ sX hf.isVariety_target
    hf.isVariety_source f hf.comp_eq hf.dim_eq x
  exact ⟨x, (coheight_map_eq_of_isSmall hf hle).symm.trans hz, rfl⟩

end Small

/-! ### Transforms of prime divisors -/

section Transform

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A rational map which is a morphism in codimension one is defined at the generic point of
every prime divisor. -/
private theorem RationalMap.IsMorphismInCodimOne.definedAt_genericPoint {X Y : Scheme.{u}}
    {φ : X.RationalMap Y} (hφ : RationalMap.IsMorphismInCodimOne φ) (P : Mori.PrimeDivisor X) :
    Mori.RationalMap.DefinedAt φ P.genericPoint := by
  by_contra hnd
  have h2 := Mori.le_closedsCodimension_iff.mp hφ
    (TopologicalSpace.IrreducibleCloseds.closureSingleton P.genericPoint)
    (closure_minimal (Set.singleton_subset_iff.mpr hnd) (Mori.RationalMap.dom φ).compl.isClosed)
  rw [codimension_eq_coheight, show TopologicalSpace.IrreducibleCloseds.closureSingleton
      P.genericPoint = (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
    Order.coheight_orderIso, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

variable {k : Type u} [Field k] {X X' Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsReduced X]
  [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (X' ↘ ⊤_ Scheme)]
  {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'}

/-- A representative `g'` of a rational map `g` over `Z` satisfies `f⁺ ∘ g' = f` on its
domain. -/
private theorem apply_hom_of_isOver (hover : g.compHom fp = f.toRationalMap)
    (g' : X.PartialMap X') (hg' : g'.toRationalMap = g) (x : g'.domain) :
    fp (g'.hom x) = f x.1 := by
  have h : (g'.compHom fp).toRationalMap = f.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', hover]
  have h2 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  change (g'.compHom fp).hom x = _
  rw [h2]
  rfl

/-- If `g_*(R) = F`, then `f⁺(η_F) = f(η_R)`. -/
private theorem apply_genericPoint_of_transformPrimeDivisor_eq_some
    (hover : g.compHom fp = f.toRationalMap) {R : Mori.PrimeDivisor X}
    {F : Mori.PrimeDivisor X'} (h : Mori.RationalMap.transformPrimeDivisor g R = some F) :
    fp F.genericPoint = f R.genericPoint := by
  obtain ⟨g', hR, hg'⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hR]
  exact apply_hom_of_isOver hover g' hg' ⟨_, hR⟩

variable [IsNormal Z]

/-- Under a map `g` over `Z` which is a morphism in codimension one between small birational
contractions, every prime divisor has a transform. -/
private theorem exists_transformPrimeDivisor_eq_some (hover : g.compHom fp = f.toRationalMap)
    (hg : RationalMap.IsMorphismInCodimOne g) (hf : IsSmall k sZ sX f)
    (hfp : IsSmall k sZ sX' fp) (R : Mori.PrimeDivisor X) :
    ∃ F, Mori.RationalMap.transformPrimeDivisor g R = some F := by
  obtain ⟨g', hR, hg'⟩ := Mori.RationalMap.definedAt_iff.mp
    (hg.definedAt_genericPoint R)
  have hx'z : fp (g'.hom ⟨R.genericPoint, hR⟩) = f R.genericPoint :=
    apply_hom_of_isOver hover g' hg' _
  have hz : Order.coheight (f R.genericPoint) = 1 :=
    (coheight_map_eq_of_isSmall hf R.coheight_genericPoint.le).trans R.coheight_genericPoint
  have hle : Order.coheight (g'.hom ⟨R.genericPoint, hR⟩) ≤ 1 := by
    rw [← hz, ← hx'z]
    exact coheight_le_coheight_map sZ sX' hfp.isVariety_target hfp.isVariety_source fp
      hfp.comp_eq hfp.dim_eq _
  have hx' : Order.coheight (g'.hom ⟨R.genericPoint, hR⟩) = 1 :=
    (coheight_map_eq_of_isSmall hfp hle).symm.trans (hx'z ▸ hz)
  exact ⟨_, transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hR
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx')⟩

/-- Every prime divisor of `X⁺` is the transform of a prime divisor of `X`. -/
private theorem exists_transformPrimeDivisor_eq (hover : g.compHom fp = f.toRationalMap)
    (hg : RationalMap.IsMorphismInCodimOne g) (hf : IsSmall k sZ sX f)
    (hfp : IsSmall k sZ sX' fp) (F : Mori.PrimeDivisor X') :
    ∃ R, Mori.RationalMap.transformPrimeDivisor g R = some F := by
  have hz : Order.coheight (fp F.genericPoint) = 1 :=
    (coheight_map_eq_of_isSmall hfp F.coheight_genericPoint.le).trans F.coheight_genericPoint
  obtain ⟨x, hx, hxz⟩ := exists_apply_eq_of_isSmall hf hz
  obtain ⟨F', hF'⟩ := exists_transformPrimeDivisor_eq_some hover hg hf hfp
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx)
  have hgp : Mori.PrimeDivisor.genericPoint (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx) =
      x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hx
  have h1 : fp F'.genericPoint = fp F.genericPoint := by
    rw [apply_genericPoint_of_transformPrimeDivisor_eq_some hover hF', hgp, hxz]
  exact ⟨_, hF'.trans (congrArg some (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_of_isSmall hfp F'.coheight_genericPoint.le F.coheight_genericPoint.le h1)))⟩

/-- The coefficient of `g_* Δ` along `F` is that of `Δ` along the prime divisor `R` with
`g_*(R) = F`. -/
private theorem transformDivisor_apply_of_eq_some {R' : Type*} [AddCommMonoid R']
    (hover : g.compHom fp = f.toRationalMap) (hf : IsSmall k sZ sX f) {R : Mori.PrimeDivisor X}
    {F : Mori.PrimeDivisor X'} (h : Mori.RationalMap.transformPrimeDivisor g R = some F)
    (Δ : DivisorWithCoeffs R' X) : Mori.RationalMap.transformDivisor g Δ F = Δ R := by
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h (fun R₁ h₁ => ?_) Δ
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_of_isSmall hf R₁.coheight_genericPoint.le R.coheight_genericPoint.le ?_)
  rw [← apply_genericPoint_of_transformPrimeDivisor_eq_some hover h₁,
    apply_genericPoint_of_transformPrimeDivisor_eq_some hover h]

end Transform

/-! ### Rational top forms -/

section PullbackForms

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}

/-- Along an isomorphism of fields with a pull-back generator, the pull-back of forms is
surjective. -/
private theorem pullbackForms_surjective (hK : Function.Surjective (algebraMap K K'))
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Surjective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  have hrepr : ∀ τ : PluriForms k K d m,
      b'.repr (pullbackForms (K' := K') m τ) () = algebraMap K K' (b.repr τ ()) := by
    intro τ
    rw [pullbackForms_eq hω]
    unfold pullbackFormsAlong
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_left rfl, mul_one]
  intro ρ
  obtain ⟨c, hc⟩ := hK (b'.repr ρ ())
  refine ⟨c • b (), b'.ext_elem fun i => ?_⟩
  cases i
  rw [hrepr, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self,
    Finsupp.single_apply, ite_eq_left rfl, mul_one, hc]

end PullbackForms

section Forms

variable {k : Type u} [Field k] [PerfectField k]

/-- Every rational top form on `W` is the pull-back of one on `X` along a birational `q`. -/
private theorem exists_pullbackRationalPluriForms_eq {W X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral W] [LocallyOfFiniteType sX] (q : W ⟶ X)
    [IsDominant q] (hq : Function.Bijective (functionFieldMap q)) (hs : q ≫ sX = sW) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sW n 1} (hτ : τ ≠ 0) :
    ∃ τ' : RationalPluriForms sX n 1, τ' ≠ 0 ∧
      (hs ▸ pullbackRationalPluriForms sX q τ' : RationalPluriForms sW n 1) = τ := by
  subst hs
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (q ≫ sX)
  let := functionFieldMapAlgebra q
  have := isScalarTower_functionFieldMap sX q
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX q hq
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
  obtain ⟨τ', hτ'⟩ := pullbackForms_surjective (K := X.functionField) (K' := W.functionField) hq.2
    hω 1 τ
  refine ⟨τ', fun h0 => hτ ?_, hτ'⟩
  rw [← hτ', h0]
  change pullbackForms (K := X.functionField) (K' := W.functionField) 1 0 = 0
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  simp

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X U : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsIntegral U] (hX : IsNormalVariety k sX) {p : U ⟶ X} [IsDominant p]
    (hp : IsBirationalMorphism p) {n : ℕ} (hn : topologicalKrullDim X = n) {m : ℤ}
    {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hp.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn)
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- Divisors of forms do not see a rewriting of the structure morphism. -/
private theorem divisorOfForm_cast {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
    [CompactSpace W] {s₁ s₂ : W ⟶ Spec (.of k)} [LocallyOfFiniteType s₁]
    [LocallyOfFiniteType s₂] (h : s₁ = s₂) {d : ℕ} {m : ℤ} (ρ : RationalPluriForms s₁ d m) :
    divisorOfForm (h ▸ ρ : RationalPluriForms s₂ d m) = divisorOfForm ρ := by
  subst h
  rfl

/-- The divisors of two nonzero rational top forms on a normal variety are linearly
equivalent. -/
private theorem linearlyEquivalent_divisorOfForm {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ ω : RationalPluriForms sX n 1} (hτ : τ ≠ 0) (hω : ω ≠ 0) :
    Divisor.LinearlyEquivalent (divisorOfForm τ) (divisorOfForm ω) := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero hc), ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm,
    coeff_divisorOfForm, e1, e2]
  ring

/-- Multiplying a rational `n`-form by `c ∈ k(X)ˣ` adds `v_E(c)` to its order along `E`. -/
private theorem ordPullback_smul {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    (E : ProperDivisorOver k sX) [IsIntegral E.Y] [IsLocallyNoetherian E.Y] [IsDominant E.f]
    {c : X.functionField} {ω : RationalPluriForms sX n 1} (hc : c ≠ 0) (hω0 : ω ≠ 0) :
    E.toDivisorOver.ordPullback (c • ω) =
      E.toDivisorOver.ordPullback ω + Scheme.ord (functionFieldMap E.f c) E.E.genericPoint := by
  have := E.isNormal
  let := functionFieldAlgebra sX
  obtain ⟨b, N, hN⟩ := E.toDivisorOver.exists_ordPullback_eq hX hn
  have hb0 : (ZTensorPower.basis b 1).repr ω () ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hrep : (ZTensorPower.basis b 1).repr (c • ω) () =
      c * (ZTensorPower.basis b 1).repr ω () :=
    congrArg (· ()) (LinearEquiv.map_smul (ZTensorPower.basis b 1).repr c ω)
  rw [hN 1 _ (smul_ne_zero hc hω0), hN 1 ω hω0, hrep, map_mul,
    Scheme.ord_mul ((map_ne_zero (functionFieldMap E.f)).mpr hc)
      ((map_ne_zero (functionFieldMap E.f)).mpr hb0)]
  ring

/-- **The discrepancy does not depend on the canonical divisor within its linear equivalence
class.** If `a = a(F, D)` is computed with a canonical divisor `K` and `K₂ ∼ K` is another
canonical divisor, then `a` is also the discrepancy computed with `K₂`. -/
private theorem isDiscrepancy_of_linearlyEquivalent {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {n : ℕ} {K K₂ : Divisor X} {D : RDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : IsDiscrepancy sX n K D F a) (hK₂ : K₂.IsCanonicalDivisor sX n)
    (hl : K₂.LinearlyEquivalent K) : IsDiscrepancy sX n K₂ D F a := by
  obtain ⟨-, -, hF, E, ω, m, r, L, hEF, hωK, hX, hn, hω0, hLc, hsum, Lp, hLp, ha⟩ := h
  obtain ⟨φ, hφ⟩ := hl
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have : QuasiCompact (E.f ≫ sX) := E.isNormalVariety.1.toQuasiCompact
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  set Z0 : irreducibleComponents X := pointComponent (genericPoint X)
  set c : X.functionField := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
  have hc : c ≠ 0 := (φ.isUnit.map _).ne_zero
  have hZ : ∀ Γ : Mori.PrimeDivisor X, Γ.component = Z0 := fun Γ => Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  have hcΓ : ∀ Γ : Mori.PrimeDivisor X,
      Scheme.ord c Γ.genericPoint = (principalDivisor φ).coeff Γ := by
    intro Γ
    rw [coeff_principalDivisor, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord, hZ]
  have hK₂e : K₂ = K + principalDivisor φ := by rw [← hφ]; abel
  have hcω0 : c • ω ≠ 0 := smul_ne_zero hc hω0
  have hdiv : divisorOfForm (c • ω) = K₂ := by
    refine Finsupp.ext fun Γ => ?_
    change (divisorOfForm (c • ω)).coeff Γ = K₂.coeff Γ
    rw [coeff_divisorOfForm, Γ.ordForm_smul_of_topologicalKrullDim_eq hn hc hω0, hK₂e,
      DivisorWithCoeffs.coeff_add, ← hωK, coeff_divisorOfForm, hcΓ]
    ring
  have hφE : ∀ Z, E.f (componentGenericPoint E.Y Z) ∉ (principalDivisor φ).supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant E.f _
  have hN' := Divisor.isPullback_principalDivisor φ hφE
  have hN'E : ((principalDivisor (pullbackRationalFunction E.f φ hφE)).coeff E.E : ℝ) =
      Scheme.ord (functionFieldMap E.f c) E.E.genericPoint := by
    exact_mod_cast MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hN'
      (Divisor.isLocalEquation_principalDivisor φ ⊤) E.E trivial Z0
  have hLc₂ : ∀ j, (Fin.cons (principalDivisor φ) L : Fin (m + 1) → Divisor X) j |>.IsCartier :=
    Fin.cases (Divisor.isCartier_principalDivisor φ) hLc
  have hsum₂ : Divisor.toRDivisor (divisorOfForm (c • ω)) + D =
      ∑ j, (Fin.cons 1 r : Fin (m + 1) → ℝ) j •
        Divisor.toRDivisor ((Fin.cons (principalDivisor φ) L : Fin (m + 1) → Divisor X) j) := by
    rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, one_smul]
    simp only [Fin.cons_succ]
    rw [← hsum, hdiv, hK₂e, map_add, ← hωK]
    abel
  refine ⟨hK₂, ⟨m + 1, Fin.cons 1 r, Fin.cons (principalDivisor φ) L, hLc₂, ?_⟩, hF, E, c • ω,
    m + 1, Fin.cons 1 r, Fin.cons (principalDivisor φ) L, hEF, hdiv, hX, hn, hcω0, hLc₂, hsum₂,
    Fin.cons (principalDivisor (pullbackRationalFunction E.f φ hφE)) Lp,
    Fin.cases ⟨hφE, hN'⟩ hLp, ?_⟩
  · rw [← hdiv, hsum₂]
    simp only [toRDivisor_eq_mapCoeffs]
  · rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, one_mul, hN'E,
      ordPullback_smul hX hn E hc hω0, ha]
    simp only [Fin.cons_succ]
    push_cast
    ring

end Forms

/-! ### Prime divisors of a common model which are not exceptional over the base -/

section NonExceptional

variable {k : Type u} [Field k]

/-- With `d + c = n`, `d + 2 ≤ n` if and only if `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.coe_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- On a variety of dimension `n`, a divisor over `X` is exceptional iff its centre has
codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ} (hn : topologicalKrullDim X = n)
    (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

/-- Let `u : W ⟶ Y` be a proper birational morphism of normal varieties and `v : Y ⟶ Z` a
morphism of varieties of the same dimension. A prime divisor `Q` of `W` whose image in `Z` has
coheight at most one maps onto a prime divisor `R` of `Y`, and `ord_Q = ord_R`. -/
private theorem exists_primeDivisor_of_not_two_le_coheight {W Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hY : IsNormalVariety k sY) (hZ : Mori.IsVariety k sZ) (v : Y ⟶ Z)
    (hv : v ≫ sZ = sY) (hdim : topologicalKrullDim Y = topologicalKrullDim Z) {n : ℕ}
    (hn : topologicalKrullDim Y = n) (u : W ⟶ Y) [IsProper u]
    (hW : IsNormalVariety k (u ≫ sY)) (hu : IsBirationalMorphism u) (Q : Mori.PrimeDivisor W)
    (hQ : ¬ 2 ≤ Order.coheight (v (u Q.genericPoint))) :
    ∃ R : Mori.PrimeDivisor Y, u Q.genericPoint = R.genericPoint ∧
      (ProperDivisorOver.mk ⟨W, u, hW, hu, Q⟩ inferInstance : ProperDivisorOver k sY).valuation =
        R.divisorialValuation := by
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  obtain ⟨R, -, hgen, -, hval⟩ := ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hY
    (ProperDivisorOver.mk ⟨W, u, hW, hu, Q⟩ inferInstance) fun hexc => hQ <|
      ((isExceptional_iff_two_le_coheight hn _).mp hexc).trans
        (coheight_le_coheight_map sZ sY hZ hY.1 v hv hdim _)
  exact ⟨R, hgen, hval⟩

/-- The valuation of the divisor `(X, 𝟙, R)` over `X` is `ord_R`. -/
private theorem valuation_ofPrimeDivisor {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    (R : Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX R).valuation = R.divisorialValuation :=
  Valuation.ext fun g => by
    change R.divisorialValuation (functionFieldMap (𝟙 X) g) = _
    rw [functionFieldMap_id_apply]

/-- The order of `u^*ω` along a prime divisor `Q` of `W` mapping onto a prime divisor `R` of `X`
with `ord_Q = ord_R` is the order of `ω` along `R`. -/
private theorem ordForm_pullback_eq_of_valuation_eq [PerfectField k] {W X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n) (u : W ⟶ X)
    [IsProper u] (hW : IsNormalVariety k (u ≫ sX)) (hu : IsBirationalMorphism u)
    (Q : Mori.PrimeDivisor W) (R : Mori.PrimeDivisor X)
    (hv : (ProperDivisorOver.mk ⟨W, u, hW, hu, Q⟩ inferInstance :
      ProperDivisorOver k sX).valuation = R.divisorialValuation)
    (ω : RationalPluriForms sX n 1) :
    (DivisorOver.mk W u hW hu Q).ordPullback ω = R.ordForm ω := by
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn
    (D' := DivisorOver.ofPrimeDivisor k hX R) (hv.trans (valuation_ofPrimeDivisor hX R).symm) ω,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn]

end NonExceptional

/-! ### Intersection numbers on a common model -/

section Intersection

section Normalization

variable {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
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
private theorem isCurve_comp_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
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
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp_of_isCurveNormalization C hν hdim
  have hc2 := isCurve_ι C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber {C : ProperCurve sX}
    {L : Divisor X} {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

end Normalization

variable {k : Type u} [Field k]

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {Y Y' : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {sY' : Y' ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) (hs : h ≫ sY = sY') [QuasiCompact sY'] [CompactSpace Y] [CompactSpace Y']
    {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve sY') (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k sY' C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h hs hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {Y Y' : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {sY' : Y' ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) (hs : h ≫ sY = sY') [QuasiCompact sY'] [CompactSpace Y] [CompactSpace Y']
    {D : Divisor Y} (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve sY') (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k sY' C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h hs hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- An `f`-ample Cartier divisor has positive degree on every curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] (hX : Mori.IsVariety k sX) (f : X ⟶ Z) {A : Divisor X}
    (hA : IsRelativelyAmpleCartier f A) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < A.degreeOn k sX C.ι C.dim_le hA.1 := by
  obtain ⟨hAc, hamp⟩ := hA
  have := hAc.isInvertibleModule_divisorialSheaf
  have h : Mori.IsRelativelyAmple f A.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hX f _ h C hC

/-- The pull-back of a `v`-ample Cartier divisor along `h` has nonnegative degree on every curve
contracted by `h ≫ v`. -/
private theorem degreeOn_pullback_nonneg {W Y Z : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [QuasiCompact sW]
    (hY : Mori.IsVariety k sY) (h : W ⟶ Y) [IsProper h] (hs : h ≫ sY = sW) (v : Y ⟶ Z)
    {A : Divisor Y} (hA : IsRelativelyAmpleCartier v A)
    (hB : ∀ Z : irreducibleComponents W, h (componentGenericPoint W Z) ∉ A.supp)
    (C : ProperCurve sW) (hC : C.IsContractedBy (h ≫ v)) :
    0 ≤ (A.pullback hA.1 hB).degreeOn k sW C.ι C.dim_le (hA.1.isCartier_pullback h hB) := by
  have := hY.toIsSeparated
  have := hY.toLocallyOfFiniteType
  have := hY.toQuasiCompact
  by_cases hc : IsProperCurve sY (h C.point)
  · let C'' : ProperCurve sY := ⟨_, hc⟩
    have hCf : C''.IsContractedBy v := by
      intro y hy
      have hsub : closure ({h C.point} : Set Y) ⊆ h '' closure ({C.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩)
          (h.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC z hz
    rw [degreeOn_pullback_eq_mul h hs hA.1 hB C C'' rfl]
    exact mul_nonneg (Nat.cast_nonneg _)
      (degreeOn_pos_of_isRelativelyAmpleCartier hY v hA C'' hCf).le
  · rw [degreeOn_pullback_eq_zero h hs hA.1 hB C hc]

/-- On a common model `p : W ⟶ X`, `q : W ⟶ X⁺` with `p ≫ f = q ≫ f⁺`, the divisor
`∑ s_j q^*A_j + ∑ t_i p^*B_i` is `(p ≫ f)`-nef for `f⁺`-ample Cartier divisors `A_j`, `f`-ample
Cartier divisors `B_i` and `s_j, t_i ≥ 0`, by the projection formula. -/
private theorem isRelativelyNef_sum_pullback {W X X' Z : Scheme.{u}} {sW : W ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [QuasiCompact sW]
    (hX : Mori.IsVariety k sX) (hX' : Mori.IsVariety k sX')
    (p : W ⟶ X) (q : W ⟶ X') [IsProper p] [IsProper q] (hps : p ≫ sX = sW)
    (hqs : q ≫ sX' = sW) (f : X ⟶ Z) (fp : X' ⟶ Z) (hcomm : p ≫ f = q ≫ fp)
    {mA : ℕ} (s : Fin mA → ℝ) (hs : ∀ j, 0 ≤ s j) (A : Fin mA → Divisor X')
    (hA : ∀ j, IsRelativelyAmpleCartier fp (A j))
    (hAq : ∀ j, ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ (A j).supp)
    {mB : ℕ} (t : Fin mB → ℝ) (ht : ∀ i, 0 ≤ t i) (B : Fin mB → Divisor X)
    (hB : ∀ i, IsRelativelyAmpleCartier f (B i))
    (hBp : ∀ i, ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ (B i).supp) :
    IsRelativelyNef k sW (p ≫ f)
      (∑ j, s j • Divisor.toRDivisor ((A j).pullback (hA j).1 (hAq j)) +
        ∑ i, t i • Divisor.toRDivisor ((B i).pullback (hB i).1 (hBp i))) := by
  set LA : Fin mA → Divisor W := fun j => (A j).pullback (hA j).1 (hAq j)
  set LB : Fin mB → Divisor W := fun i => (B i).pullback (hB i).1 (hBp i)
  have hLA : ∀ j, (LA j).IsCartier := fun j => (hA j).1.isCartier_pullback q (hAq j)
  have hLB : ∀ i, (LB i).IsCartier := fun i => (hB i).1.isCartier_pullback p (hBp i)
  have hL : ∀ j, (Fin.append LA LB j).IsCartier :=
    Fin.addCases (fun j => by rw [Fin.append_left]; exact hLA j)
      (fun i => by rw [Fin.append_right]; exact hLB i)
  refine ⟨mA + mB, Fin.append s t, Fin.append LA LB, hL, ?_, fun C hC x hx => ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, LA, LB]
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    rw [Fin.sum_univ_add]
    refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (Finset.sum_nonneg fun i _ => ?_)
    · have h1 := eq_degreeOn_of_isCartierIntersectionNumber (hd (Fin.castAdd mB j))
      rw [Divisor.degreeOn_congr (Fin.append_left LA LB j) _ (hLA j)] at h1
      rw [Fin.append_left, h1]
      exact mul_nonneg (hs j) (Int.cast_nonneg_iff.mpr
        (degreeOn_pullback_nonneg hX' q hqs fp (hA j) (hAq j) C (hcomm ▸ hC)))
    · have h1 := eq_degreeOn_of_isCartierIntersectionNumber (hd (Fin.natAdd mA i))
      rw [Divisor.degreeOn_congr (Fin.append_right LA LB i) _ (hLB i)] at h1
      rw [Fin.append_right, h1]
      exact mul_nonneg (ht i) (Int.cast_nonneg_iff.mpr
        (degreeOn_pullback_nonneg hX p hps f (hB i) (hBp i) C hC))

end Intersection

/-! ### Cartier combinations -/

section CartierCombination

variable {R : Type*} [Ring R] {Y : Scheme.{u}} [IsLocallyNoetherian Y] [IsNormal Y]

/-- The zero divisor is a Cartier combination. -/
private theorem isCartierCombination_zero : IsCartierCombination (0 : DivisorWithCoeffs R Y) :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩

/-- A sum of Cartier combinations is a Cartier combination. -/
private theorem isCartierCombination_add {D D' : DivisorWithCoeffs R Y}
    (hD : IsCartierCombination D) (hD' : IsCartierCombination D') :
    IsCartierCombination (D + D') := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := hD
  obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := hD'
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂,
    Fin.addCases (fun j => by rw [Fin.append_left]; exact hL₁ j)
      (fun i => by rw [Fin.append_right]; exact hL₂ i), ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The negative of a Cartier combination is a Cartier combination. -/
private theorem isCartierCombination_neg {D : DivisorWithCoeffs R Y}
    (hD : IsCartierCombination D) : IsCartierCombination (-D) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  exact ⟨m, fun j => -r j, L, hL, by simp only [neg_smul, Finset.sum_neg_distrib]⟩

end CartierCombination

/-! ### The negativity lemma -/

section Negativity

variable {k : Type u} [Field k]

/-- **Negativity lemma.** If `M` is an `h`-nef `ℝ`-Cartier divisor for a proper birational
morphism `h : Y ⟶ Z` of normal varieties, and `-M` has nonnegative coefficients along the prime
divisors which are not exceptional over `Z`, then `-M` is effective. -/
private theorem isEffective_neg_of_isRelativelyNef {Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sY] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsLocallyNoetherian Y] [IsNormal Y] (hZ : IsNormalVariety k sZ) (hY : IsNormalVariety k sY)
    (h : Y ⟶ Z) (hs : h ≫ sZ = sY) [IsProper h] (hb : IsBirationalMorphism h) {M : RDivisor Y}
    (hM : IsCartierCombination M) (hnef : IsRelativelyNef k sY h M)
    (hexc : ∀ P, ¬ IsExceptionalPrimeDivisor sZ h P → 0 ≤ (-M).coeff P) : (-M).IsEffective := by
  have h0 : IsRCartierPullback h (0 : RDivisor Z) (0 : RDivisor Y) :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  refine isEffective_of_isNumericallyEquivalentOver_pullback k sZ sY hZ hY h hs hb
    isCartierCombination_zero h0 hM hnef (isCartierCombination_neg hM) hexc ?_
  rw [add_neg_cancel]
  exact ⟨isCartierCombination_zero, isCartierCombination_zero,
    fun C _ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h1 h2 =>
      (IsRIntersectionNumber.eq_and_linear k sY C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h1 h2⟩

end Negativity

/-! ### Comparison on a common model -/

section Comparison

variable {k : Type u} [Field k] [PerfectField k] {X X' Z W : Scheme.{u}}
  {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  [LocallyOfFiniteType sX'] [IsIntegral W] [IsLocallyNoetherian W] [CompactSpace W]
  {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'} {p : W ⟶ X} {q : W ⟶ X'}
  [IsProper p] [IsProper q] [IsDominant p] [IsDominant q]
  [LocallyOfFiniteType (p ≫ sX)] [LocallyOfFiniteType (q ≫ sX')] {n : ℕ}

/-- On a common model `p : W ⟶ X`, `q : W ⟶ X⁺` over `Z` of two small birational contractions,
if `div(q^*ω⁺) = div(p^*ω)` then `div ω⁺ + g_* D = g_*(div ω + D)`. -/
private theorem toRDivisor_divisorOfForm_add_transformDivisor [IsNormal Z] [IsNormal W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (X' ↘ ⊤_ Scheme)] (hX : IsNormalVariety k sX)
    (hX' : IsNormalVariety k sX') (hover : g.compHom fp = f.toRationalMap)
    (hg : RationalMap.IsMorphismInCodimOne g) (hf : IsSmall k sZ sX f)
    (hfp : IsSmall k sZ sX' fp) (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n) (hWp : IsNormalVariety k (p ≫ sX))
    (hWq : IsNormalVariety k (q ≫ sX')) (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hcomm : p ≫ f = q ≫ fp) {ω : RationalPluriForms sX n 1}
    {ωp : RationalPluriForms sX' n 1}
    (hωW : divisorOfForm (pullbackRationalPluriForms sX' q ωp) =
      divisorOfForm (pullbackRationalPluriForms sX p ω)) (D : RDivisor X) :
    Divisor.toRDivisor (divisorOfForm ωp) + Mori.RationalMap.transformDivisor g D =
      Mori.RationalMap.transformDivisor g (Divisor.toRDivisor (divisorOfForm ω) + D) := by
  refine Finsupp.ext fun F => ?_
  obtain ⟨R, hRF⟩ := exists_transformPrimeDivisor_eq hover hg hf hfp F
  rw [Finsupp.add_apply, transformDivisor_apply_of_eq_some hover hf hRF,
    transformDivisor_apply_of_eq_some hover hf hRF, Finsupp.add_apply]
  congr 1
  change (Divisor.toRDivisor (divisorOfForm ωp)).coeff F =
    (Divisor.toRDivisor (divisorOfForm ω)).coeff R
  rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_divisorOfForm]
  norm_cast
  obtain ⟨Q, hQF, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX' hWq hqb F
  rw [← MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso q
    hqb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn')
    Q F hQF ωp]
  have hQ := congrArg (fun D : Divisor W => D.coeff Q) hωW
  simp only [coeff_divisorOfForm] at hQ
  rw [hQ]
  have hcoh : Order.coheight (f (p Q.genericPoint)) = 1 := by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, hQF]
    exact (coheight_map_eq_of_isSmall hfp F.coheight_genericPoint.le).trans
      F.coheight_genericPoint
  obtain ⟨R', hR'gen, hR'val⟩ := exists_primeDivisor_of_not_two_le_coheight hX
    hf.isVariety_target f hf.comp_eq hf.dim_eq hn p hWp hpb Q (by rw [hcoh]; norm_num)
  have e1 : f R'.genericPoint = f R.genericPoint := by
    rw [← hR'gen, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, hQF,
      apply_genericPoint_of_transformPrimeDivisor_eq_some hover hRF]
  obtain rfl : R' = R := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_of_isSmall hf R'.coheight_genericPoint.le R.coheight_genericPoint.le e1)
  exact ordForm_pullback_eq_of_valuation_eq hX hn p hWp hpb Q R' hR'val ω

/-- On a common model over `Z` of two small birational contractions, the discrepancies of
`(X, D)` and `(X⁺, g_* D)` agree along every prime divisor that is not exceptional over `Z`. -/
private theorem discrepancy_eq_of_not_isExceptional [IsIntegral Z] [IsNormal Z]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (X' ↘ ⊤_ Scheme)] [IsProper f] [IsNormal W]
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX')
    (hover : g.compHom fp = f.toRationalMap)
    (hg : RationalMap.IsMorphismInCodimOne g) (hf : IsSmall k sZ sX f)
    (hfp : IsSmall k sZ sX' fp) (hn : topologicalKrullDim X = n)
    (hn' : topologicalKrullDim X' = n) (hWp : IsNormalVariety k (p ≫ sX))
    (hWq : IsNormalVariety k (q ≫ sX')) (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hcomm : p ≫ f = q ≫ fp) {K : Divisor X} {K' : Divisor X'}
    {D : RDivisor X} {Q : Mori.PrimeDivisor W} (hQ : ¬ IsExceptionalPrimeDivisor sZ (p ≫ f) Q)
    {α β : ℝ}
    (hα : IsDiscrepancy sX n K D
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, Q⟩ inferInstance).valuation α)
    (hβ : IsDiscrepancy sX' n K' (Mori.RationalMap.transformDivisor g D)
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, Q⟩ inferInstance).valuation β) :
    α = β := by
  have : LocallyOfFiniteType sZ := hf.isVariety_target.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hWZ : IsNormalVariety k ((p ≫ f) ≫ sZ) := by rw [Category.assoc, hf.comp_eq]; exact hWp
  have hnc : ¬ 2 ≤ Order.coheight (f (p Q.genericPoint)) := fun h2 =>
    hQ ⟨hWZ, isBirationalMorphism_comp_of_isBirational f p
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb), inferInstance,
      (isExceptional_iff_two_le_coheight (hf.dim_eq.symm.trans hn) _).mpr h2⟩
  have hnc' : ¬ 2 ≤ Order.coheight (fp (q Q.genericPoint)) := by
    rwa [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
  obtain ⟨R, hRgen, hRval⟩ := exists_primeDivisor_of_not_two_le_coheight hX hf.isVariety_target
    f hf.comp_eq hf.dim_eq hn p hWp hpb Q hnc
  obtain ⟨F, hFgen, hFval⟩ := exists_primeDivisor_of_not_two_le_coheight hX'
    hf.isVariety_target fp hfp.comp_eq hfp.dim_eq hn' q hWq hqb Q hnc'
  rw [hRval] at hα
  rw [hFval] at hβ
  obtain ⟨F', hF'⟩ := exists_transformPrimeDivisor_eq_some hover hg hf hfp R
  have e1 : fp F'.genericPoint = fp F.genericPoint := by
    rw [apply_genericPoint_of_transformPrimeDivisor_eq_some hover hF', ← hRgen, ← hFgen,
      ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  obtain rfl : F' = F := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq_of_isSmall hfp F'.coheight_genericPoint.le F.coheight_genericPoint.le e1)
  rw [hα.eq_neg_coeff, hβ.eq_neg_coeff]
  exact congrArg _ (transformDivisor_apply_of_eq_some hover hf hF' D).symm

/-- **Discrepancies do not decrease under a flip, on a common model.** Let `(f⁺, g)` be a flip of
`f` with respect to `K + D`, `p : W ⟶ X`, `q : W ⟶ X⁺` a common normal model over `Z`, and
`K = div ω`, `div ω⁺` canonical divisors with `div(q^*ω⁺) = div(p^*ω)`. Then along every prime
divisor `Q` of `W`, `a(Q, X, D) ≤ a(Q, X⁺, g_* D)`. -/
private theorem discrepancy_le_of_isFlip [IsIntegral Z] [IsDominant f] [IsDominant fp]
    [IsNormal W] {K : Divisor X} {D : RDivisor X}
    (hflip : IsFlip k sX sZ sX' (Divisor.toRDivisor K + D) f fp g)
    (hn : topologicalKrullDim X = n) (hn' : topologicalKrullDim X' = n)
    (hWp : IsNormalVariety k (p ≫ sX)) (hWq : IsNormalVariety k (q ≫ sX'))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hcomm : p ≫ f = q ≫ fp)
    {ω : RationalPluriForms sX n 1} {ωp : RationalPluriForms sX' n 1} (hω0 : ω ≠ 0)
    (hωp0 : ωp ≠ 0) (hωK : divisorOfForm ω = K) (hK : K.IsCanonicalDivisor sX n)
    (hKp : (divisorOfForm ωp).IsCanonicalDivisor sX' n)
    (hωW : divisorOfForm (pullbackRationalPluriForms sX' q ωp) =
      divisorOfForm (pullbackRationalPluriForms sX p ω))
    (Q : Mori.PrimeDivisor W) {α β : ℝ}
    (hα : IsDiscrepancy sX n K D
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, Q⟩ inferInstance).valuation α)
    (hβ : IsDiscrepancy sX' n (divisorOfForm ωp) (Mori.RationalMap.transformDivisor g D)
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, Q⟩ inferInstance).valuation β) :
    α ≤ β := by
  subst hωK
  have hX := hflip.isNormalVariety_source
  have hX' := hflip.isNormalVariety_flip
  have hZ := hflip.isNormalVariety_target
  have hf := hflip.isSmall_source
  have hfp := hflip.isSmall
  have hover : g.compHom fp = f.toRationalMap := hflip.isModificationOf.2
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated sX' := hX'.1.toIsSeparated
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : QuasiCompact sX' := hX'.1.toQuasiCompact
  have : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal sZ
  have : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_terminal sX'
  have : IsProper f := hf.isProper
  have hsW : q ≫ sX' = p ≫ sX := by
    rw [← hfp.comp_eq, ← hf.comp_eq, ← Category.assoc, ← Category.assoc, hcomm]
  -- `K + D = -∑ tᵢ Bᵢ` and `div ω⁺ + g_* D = ∑ sⱼ Aⱼ` with `Bᵢ` `f`-ample, `Aⱼ` `f⁺`-ample
  have hEp := toRDivisor_divisorOfForm_add_transformDivisor hX hX' hover
    hflip.isMorphismInCodimOne hf hfp hn hn' hWp hWq hpb hqb hcomm hωW D
  obtain ⟨mA, s, A, -, hs, hA, hAeq⟩ := hflip.isRelativelyAmple_transform
  obtain ⟨mB, t, Bd, -, ht, hBd, hBeq⟩ := hflip.isRelativelyAntiAmple
  have hAq j := map_componentGenericPoint_notMem_supp_of_isDominant q (A j)
  have hBp i := map_componentGenericPoint_notMem_supp_of_isDominant p (Bd i)
  set GY : RDivisor W := ∑ j, s j • Divisor.toRDivisor ((A j).pullback (hA j).1 (hAq j))
    with hGY_def
  set GB : RDivisor W := ∑ i, t i • Divisor.toRDivisor ((Bd i).pullback (hBd i).1 (hBp i))
    with hGB_def
  have hGY : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ωp) +
      Mori.RationalMap.transformDivisor g D) GY :=
    ⟨mA, s, A, fun j => (A j).pullback (hA j).1 (hAq j), fun j => (hA j).1, hEp.trans hAeq,
      fun j => ⟨hAq j, Divisor.isPullback_pullback (hA j).1 (hAq j)⟩, rfl⟩
  have hGX : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + D) (-GB) :=
    ⟨mB, fun i => -t i, Bd, fun i => (Bd i).pullback (hBd i).1 (hBp i), fun i => (hBd i).1,
      by
        rw [← neg_neg (Divisor.toRDivisor _ + D), hBeq]
        simp only [neg_smul, Finset.sum_neg_distrib],
      fun i => ⟨hBp i, Divisor.isPullback_pullback (hBd i).1 (hBp i)⟩,
      by simp only [hGB_def, neg_smul, Finset.sum_neg_distrib]⟩
  -- FA (2.23.4): `-GB - GY = ∑_Q [a(Q, X⁺, D⁺) - a(Q, X, D)] Q`
  obtain ⟨aX, aY, hdX, hdY, -, hcoeff⟩ := pullback_sub_pullback_eq_sum_discrepancy hX hX' p q
    hWp hWq hpb hqb ω ωp hω0 hωp0 hK hKp hωW.symm hflip.isCartierCombination
    (hEp ▸ hflip.isCartierCombination_transform) hGX hGY
  have hcoeff' P : (-(GY + GB)).coeff P = aY P - aX P := by
    rw [← hcoeff P]
    congr 1
    abel
  -- the negativity lemma over `Z`
  have heff := isEffective_neg_of_isRelativelyNef hZ (hsW ▸ hWq) (p ≫ f)
    (by rw [Category.assoc, hf.comp_eq]) (isBirationalMorphism_comp_of_isBirational f p
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb))
    (isCartierCombination_add
      ⟨mA, s, _, fun j => (hA j).1.isCartier_pullback q (hAq j), by
        simp only [hGY_def, toRDivisor_eq_mapCoeffs]⟩
      ⟨mB, t, _, fun i => (hBd i).1.isCartier_pullback p (hBp i), by
        simp only [hGB_def, toRDivisor_eq_mapCoeffs]⟩)
    (isRelativelyNef_sum_pullback hX.1 hX'.1 p q rfl hsW f fp hcomm s (fun j => (hs j).le) A hA
      hAq t (fun i => (ht i).le) Bd hBd hBp)
    fun P hP => by
      rw [hcoeff' P, discrepancy_eq_of_not_isExceptional hX hX' hover hflip.isMorphismInCodimOne
        hf hfp hn hn' hWp hWq hpb hqb hcomm hP (hdX P) (hdY P), sub_self]
  have h := heff Q
  rw [hcoeff' Q, ← hα.eq (hdX Q), ← hβ.eq (hdY Q)] at h
  linarith

end Comparison

/-- **Discrepancies do not decrease under flips** (FA 2.27). Let `(X, D)` be a log variety of
dimension `n` with canonical divisor `K`, let `f : X ⟶ Z` be a small birational contraction and
`(fp, g)` a flip of `f` with respect to `K + D` (`MMP.Flips.IsFlip`), and let
`D⁺ = transformDivisor g D`. If `B` is a divisor of `k(X)` whose restriction to `k(Z)` has
nonempty center on `Z`, and `B⁺` is the divisor of `k(X⁺)` with the same restriction to `k(Z)`,
then `a(B, X, D) ≤ a(B⁺, X⁺, D⁺)` for any canonical divisor `K⁺` of `X⁺`. -/
@[mmp "thm_fa2_flip_discrepancies_do_not_decrease"]
public theorem IsFlip.isDiscrepancy_le {k : Type u} [Field k] [PerfectField k]
    {X Z X' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsIntegral Z]
    {n : ℕ} {K : Divisor X} {D : RDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'}
    [IsDominant f] [IsDominant fp]
    (hXD : IsLogVariety k sX D) (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlip k sX sZ sX' (Divisor.toRDivisor K + D) f fp g)
    {B : Valuation X.functionField ℤᵐ⁰} {B' : Valuation X'.functionField ℤᵐ⁰}
    (hBZ : HasNonemptyCenter k sZ (B.comap (functionFieldMap f)))
    (hBB' : B'.comap (functionFieldMap fp) = B.comap (functionFieldMap f))
    {K' : Divisor X'} {a a' : ℝ} (ha : IsDiscrepancy sX n K D B a)
    (ha' : IsDiscrepancy sX' n K' (Mori.RationalMap.transformDivisor g D) B' a') :
    a ≤ a' := by
  have hX : IsNormalVariety k sX := hflip.isNormalVariety_source
  have hX' : IsNormalVariety k sX' := hflip.isNormalVariety_flip
  haveI : IsProper f := hflip.isSmall_source.isProper
  haveI : IsProper fp := hflip.isProper
  obtain ⟨-, -, -, E, ω, _, _, _, hEB, hωK, hEw⟩ := id ha
  obtain ⟨hK', -, -, _, ω', _, _, _, -, hω'K, hE'w⟩ := id ha'
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hn' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  -- a common model on which `B` is a prime divisor `P`
  obtain ⟨W, p, q, hWp, hpb, hpp, hqp, hqb, -, hcomm, P, hP⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hX' f fp g
      hflip.isModificationOf.1 hflip.isModificationOf.2 E.toDivisorOver
  haveI : IsProper p := hpp
  haveI : IsProper q := hqp
  have hsW : q ≫ sX' = p ≫ sX := by
    rw [← hflip.isSmall.comp_eq, ← hflip.isSmall_source.comp_eq, ← Category.assoc,
      ← Category.assoc, hcomm]
  have hWq : IsNormalVariety k (q ≫ sX') := hsW ▸ hWp
  haveI : IsIntegral W := hWp.1.toIsIntegral
  haveI : IsNormal W := hWp.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hWp.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (q ≫ sX') := hWq.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : QuasiCompact (p ≫ sX) := hWp.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hPB : (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
      ProperDivisorOver k sX).valuation = B := hP.trans hEB
  have hPB' : (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance :
      ProperDivisorOver k sX').valuation = B' := by
    refine Valuation.ext fun x => ?_
    obtain ⟨z, rfl⟩ := hflip.isSmall.isBirationalMorphism.functionFieldMap_bijective.2 x
    have h1 := congrArg (fun v : Valuation Z.functionField ℤᵐ⁰ => v z) hBB'
    simp only [Valuation.comap_apply] at h1
    rw [h1, ← hPB]
    change P.divisorialValuation (functionFieldMap q (functionFieldMap fp z)) =
      P.divisorialValuation (functionFieldMap p (functionFieldMap f z))
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply q fp,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply p f,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm]
  -- the form `ω⁺` on `X⁺` with `q^*ω⁺ = p^*ω`, whose divisor is canonical, `∼ K'`
  obtain ⟨ωp, hωp0, hωp⟩ := exists_pullbackRationalPluriForms_eq q
    hqb.functionFieldMap_bijective hsW hn' (pullbackRationalPluriForms_ne_zero hX hpb hn hEw.2.2.1)
  have hlin : (divisorOfForm ωp).LinearlyEquivalent K' :=
    hω'K ▸ linearlyEquivalent_divisorOfForm hX' hn' hωp0 hE'w.2.2.1
  have hKp : (divisorOfForm ωp).IsCanonicalDivisor sX' n := hK'.of_linearlyEquivalent hlin
  exact discrepancy_le_of_isFlip hflip hn hn' hWp hWq hpb hqb hcomm hEw.2.2.1 hωp0 hωK hK hKp
    (by rw [← hωp, divisorOfForm_cast]) P (hPB ▸ ha)
    (hPB' ▸ isDiscrepancy_of_linearlyEquivalent ha' hKp hlin)

end MMP.Flips
