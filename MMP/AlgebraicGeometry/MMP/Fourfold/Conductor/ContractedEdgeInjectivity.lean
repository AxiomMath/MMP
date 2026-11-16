module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity
public import MMP.AlgebraicGeometry.Intersection.CartierRestriction
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
public import MMP.AlgebraicGeometry.Intersection.EulerPolynomialGenericRank
public import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SurfaceClassKernel
public import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
public import MMP.AlgebraicGeometry.Resolution.SNCPullback
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul
public import MMP.AlgebraicGeometry.SubschemeOver
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPullbackCorollaries
import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree

/-!
# Injectivity on oriented systems with contracted supporting surfaces

Let `f : Z ⟶ X` be a projective birational morphism from a smooth projective complex fourfold `Z`
to a normal variety `X`, and let `D = ∑ᵢ mᵢ Bᵢ`, all `mᵢ > 0`, be a divisor on `Z` whose support
`B = ⋃ᵢ Bᵢ` is an snc divisor and such that `-D` is Cartier and `f`-ample. Let `a` be an oriented
coefficient system on the double surfaces of `B`, with divisors `Zᵢ(a)` on the threefolds `Bᵢ`.
If every double surface `S` with `a_S ≠ 0` has image of dimension at most one in `X`, and every
class `[Zᵢ(a)]` vanishes in `H_4(Bᵢ, ℚ)`, then `a = 0`. No condition is put on the images of the
components `Bᵢ` themselves: only the surfaces carrying `a` need to be contracted.

The proof rests on the weighted surface identity
`∑_S w_S b_S² (D · S · 𝓗_S) = ∑ᵢ (Zᵢ(a)|_S · 𝓗_S)/mᵢ + ∑_T w_T c_T² (𝓗 · T)`, `w > 0`,
stated for a family of invertible sheaves `𝓗_S` on the double surfaces `S` whose degrees on the
triple curves `T ⊆ S` do not depend on `S`. Every term of the identity is an intersection number
on a single surface, so no line bundle on `Z` is needed. Each `Zᵢ(a)` is numerically trivial on
`Bᵢ` (the degree comparison of `MMP.Threefold.isNumericallyTrivial_of_divisorClass_eq_zero`), so
the middle sum vanishes. The proof applies the identity twice.

* With `𝓗_S = g_S^* M_C`, for `g_S : S ⟶ C = f(S)` and `M_C` ample on the integral curve `C`
  (`𝒪_S` when `f(S)` is a point), the triple-curve terms are nonnegative and `D · S · 𝓗_S < 0`
  whenever `S` maps onto a curve: a power of `M_C` is `𝒪_C(P)` for a nonempty effective divisor
  `P`, its pull-back cuts `S` in curves contracted by `f`, and `-D` is positive on those. So no
  supported surface maps onto a curve.
* With `𝓗_S = A|_S`, `A` ample on `Z`, every supported surface is contracted to a point, on which
  `-D` is ample; so `D · S · A < 0` on every supported surface, and the identity forces `a = 0`.

## Main results

* `MMP.Fourfold.eq_zero_of_mem_verticalSurfaceCoefficients_of_surfaceCoefficientClasses_eq_zero`:
  the map `a ↦ ([Zᵢ(a)])ᵢ` is injective on the oriented systems supported on surfaces mapping to
  dimension at most one.

## Implementation notes

* The components `Bᵢ` are the prime divisors in the support of `D` and `mᵢ` is the coefficient
  of `D` at `Bᵢ`; the snc condition `DivisorWithCoeffs.IsSNC` depends only on the support.
* The oriented systems supported on surfaces with image of dimension at most one in `X` are
  `MMP.Fourfold.verticalSurfaceCoefficients f D`, and the family of classes `([Zᵢ(a)])ᵢ` in
  `⨁ᵢ H_4(Bᵢ, ℚ)` is `MMP.Fourfold.surfaceCoefficientClasses D a`.
* "`-D` is `f`-antiample" is `MMP.Mori.Divisor.IsRelativelyAmple f (-D)`.
* The source applies the identity with `H = f^* H_X` for an ample `H_X` on `X`, which needs `X`
  projective. The family `S ↦ g_S^* M_{f(S)}` takes the place of `f^* H_X`: only its restrictions to
  the supported surfaces enter the identity, and these are compatible on the triple curves since a
  triple curve maps either onto `f(S)` or to a point. The algebra of the identity is the one of
  `MMP.Fourfold.sum_sq_mul_intersectionNumber_doubleSurface_eq`, with its local computations redone
  on the surfaces.
* The auxiliary lemmas of the proof live in the namespace
  `MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open scoped MMP.SubschemeOver

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The invertible sheaf of an effective Cartier divisor is invertible, in the
`Scheme.ringCatSheaf` spelling. -/
private instance isInvertible_invertibleSheaf' {Y : Scheme} (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (Stacks.Divisors.invertibleSheaf' D : Y.Modules) :=
  Stacks.Divisors.invertibleSheaf_isInvertible D

/-- The pull-back of the invertible sheaf of an effective Cartier divisor is invertible. -/
private instance isInvertible_pullback_invertibleSheaf' {C Y : Scheme} (i : C ⟶ Y)
    (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj (Stacks.Divisors.invertibleSheaf' D)) :=
  MMP.Mori.isInvertible_pullback_obj i _

namespace MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP MMP.Mori MMP.Fourfold

/-! ### Double surfaces, triple curves and the algebra of the weighted identity -/

section Core

/-- The identity at one triple curve `T ⊆ Eᵢ ∩ Eⱼ ∩ Eₗ`, `i < j < l`: with
`u = b_{ij,T}`, `v = b_{il,T}`, `w = b_{jl,T}`, the left side carries `mᵢ mⱼ mₗ (u² + v² + w²)`,
the off-diagonal terms of `∑ᵢ Zᵢ(a)²/mᵢ` carry `2 mᵢ mⱼ mₗ (uv - uw + vw)` (the coefficients
`a_{ji} = -a_{ij}`, `a_{li} = -a_{il}`, `a_{lj} = -a_{jl}` entering by antisymmetry), and the
difference is `mᵢ mⱼ mₗ (u - v + w)²`. -/
private theorem triple_curve_identity (mi mj ml aij ail ajl : ℚ) (hi : mi ≠ 0) (hj : mj ≠ 0)
    (hl : ml ≠ 0) :
    mi * mj * (aij / (mi * mj)) ^ 2 * ml + mi * ml * (ail / (mi * ml)) ^ 2 * mj +
        mj * ml * (ajl / (mj * ml)) ^ 2 * mi =
      2 * (1 / mi * aij * ail) + 2 * (1 / mj * -aij * ajl) + 2 * (1 / ml * -ail * -ajl) +
        mi * mj * ml * (aij / (mi * mj) - ail / (mi * ml) + ajl / (mj * ml)) ^ 2 := by
  field_simp
  ring

/-- The Cartier divisor `εᵢ` of a component `Eᵢ` of `B` is effective with closed subscheme
`Eᵢ`. -/
private theorem exists_isEffective_eps (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ)
    {B : Divisor Z} (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (i : B.support) :
    ∃ h : MMP.Intersection.IsEffective (ε i),
      MMP.CartierDivisor.subscheme (ε i) h = i.1.idealSheaf :=
  haveI := hvar
  (hε i).isEffective_and_subscheme_eq_of_isSmoothScheme sZ hsm

/-- The Cartier divisor `π_P` of a prime divisor `P` of a component `Eᵢ` is effective with closed
subscheme `P`: the component is a smooth variety. -/
private theorem exists_isEffective_pi (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (i : B.support) (P : Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    ∃ h : MMP.Intersection.IsEffective (π i P),
      MMP.CartierDivisor.subscheme (π i P) h = P.idealSheaf := by
  have := i.1.integral
  have : AlgebraicGeometry.IsVariety k (i.1.idealSheaf.subschemeι ≫ sZ) := ⟨⟩
  exact (hπ i P).isEffective_and_subscheme_eq_of_isSmoothScheme _ (hB.1 i.1 i.2)

/-- A component `E_b` of an snc divisor has simple normal crossings with the other components. -/
private theorem hasSNCWith_component {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} {B : Divisor Z}
    (hB : B.IsSNC sZ) (b : B.support) :
    MMP.Resolution.HasSNCWith (fun c : {c : B.support // c ≠ b} => c.1.1.idealSheaf)
      b.1.idealSheaf := by
  intro x hx
  obtain ⟨n, z, j, hz, hj, hI⟩ := hB.2 x
  refine ⟨n, z, fun i => j ⟨i.1.1.1, i.1.1.2, i.2⟩, {j ⟨b.1, b.2, hx⟩}, hz,
    fun i => hI ⟨i.1.1.1, i.1.1.2, i.2⟩, ?_, ?_⟩
  · intro i i' h
    have := hj h
    exact Subtype.ext (Subtype.ext (Subtype.ext (Subtype.mk.inj this)))
  · rw [Finset.coe_singleton, Set.image_singleton]
    exact hI ⟨b.1, b.2, hx⟩

/-- Distinct prime divisors do not contain one another. -/
private theorem not_support_subset_of_ne {Z : Scheme.{0}} {E E' : Mori.PrimeDivisor Z}
    (h : E ≠ E') : ¬ (E.support ⊆ E'.support) := by
  intro hsub
  have hη : E.genericPoint ∈ E'.support := hsub (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hη
  have hsp : E'.genericPoint ⤳ E.genericPoint := specializes_iff_mem_closure.2 hη
  by_cases he : E.genericPoint = E'.genericPoint
  · exact h (AlgebraicGeometry.PrimeDivisor.genericPoint_injective he)
  · have h2 := Order.coheight_add_one_le
      (MMP.Intersection.lt_of_specializes_of_ne hsp he)
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by decide)

/-- No other component contains an irreducible component of `E_b`. -/
private theorem not_component_subset {Z : Scheme.{0}} {B : Divisor Z} (b : B.support)
    (c : {c : B.support // c ≠ b}) :
    ∀ W ∈ MMP.Resolution.componentsOf (b.1.idealSheaf.support : Set Z),
      ¬ W ⊆ (c.1.1.idealSheaf.support : Set Z) := by
  intro W hW hWc
  have hirr : IsIrreducible (b.1.idealSheaf.support : Set Z) := by
    change IsIrreducible (b.1.support : Set Z)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  have hWb : (b.1.idealSheaf.support : Set Z) ⊆ W := hW.2 ⟨hirr, le_rfl⟩ hW.1.2
  exact not_support_subset_of_ne (fun e => c.2 (Subtype.ext e.symm)) (hWb.trans hWc)

/-- **`E_a ∩ E_b` as a divisor on `E_b`.** For components `a ≠ b` of a reduced snc divisor, the
inverse image of `E_a` in `E_b` is a reduced effective Cartier divisor on `E_b`. -/
private theorem isEffectiveCartierDivisor_comap_component {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {a b : B.support}
    (hab : a ≠ b) :
    Stacks.Divisors.IsEffectiveCartierDivisor (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι) ∧
      IsReduced (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι).subscheme := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  exact MMP.Resolution.isEffectiveCartierDivisor_and_isReduced_comap_of_hasSNCWith
    (hasSNCWith_component hB b) (not_component_subset b) ⟨a, hab⟩

/-- **`𝒪(εₐ)|_{E_b} ≅ 𝒪_{E_b}(Eₐ ∩ E_b)`** for components `a ≠ b`. -/
private theorem nonempty_pullback_eps_iso (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ)
    {B : Divisor Z} (hB : B.IsSNC sZ) (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    {a b : B.support} (hab : a ≠ b) :
    Nonempty ((Scheme.Modules.pullback b.1.idealSheaf.subschemeι).obj
        (MMP.CartierDivisor.sheaf (ε a)) ≅
      (Stacks.Divisors.invertibleSheaf' (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι) :
        b.1.idealSheaf.subscheme.Modules)) := by
  obtain ⟨he, hsub⟩ := exists_isEffective_eps k sZ hvar hsm ε hε a
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor a.1.idealSheaf :=
    hsub ▸ MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme he
  have hP : Stacks.Divisors.IsPullbackDefined b.1.idealSheaf.subschemeι a.1.idealSheaf :=
    (isEffectiveCartierDivisor_comap_component hB hab).1
  exact ⟨(Scheme.Modules.pullback b.1.idealSheaf.subschemeι).mapIso
      (MMP.CartierDivisor.sheafIsoInvertibleSheaf (ε a) he ≪≫
        eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hsub)) ≪≫
    Stacks.Divisors.invertibleSheafPullbackIso b.1.idealSheaf.subschemeι a.1.idealSheaf⟩

/-- At each point of `Eₐ ∩ E_b`, the ideal of `Eₐ ∩ E_b` in `E_b` is generated by one member of a
regular system of parameters. -/
private theorem stalk_comap_component {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {a b : B.support}
    (hab : a ≠ b) :
    ∀ y ∈ (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → b.1.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (a.1.idealSheaf.comap b.1.idealSheaf.subschemeι) y =
          Ideal.span {w j} := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  intro y hy
  obtain ⟨m, w, c', hw, hc, -⟩ := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
    (hasSNCWith_component hB b) (not_component_subset b) y
  exact ⟨m, w, c' ⟨⟨a, hab⟩, hy⟩, hw, hc ⟨⟨a, hab⟩, hy⟩⟩

/-- Every double surface `S ⊆ Eᵢ ∩ Eⱼ` is (the image of) a prime divisor of `Eᵢ`: `S` is a
connected component of `Eⱼ ∩ Eᵢ` read on `Eᵢ`, a divisor cut out by regular parameters. -/
private theorem exists_primeDivisor_image_support_eq {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    ∃ P : Mori.PrimeDivisor σ.fst.idealSheaf.subscheme,
      σ.fst.idealSheaf.subschemeι '' P.support = σ.carrier := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  set ι := σ.fst.idealSheaf.subschemeι
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ι
  have : NoetherianSpace σ.fst.idealSheaf.subscheme :=
    ι.isClosedEmbedding.isEmbedding.noetherianSpace
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  set D' := σ.snd.idealSheaf.comap ι
  obtain ⟨x, hx, hxc⟩ := σ.isComponent
  have hrange : Set.range ι = (σ.fst.idealSheaf.support : Set Z) := by
    rw [← σ.fst.idealSheaf.range_subschemeι]
  obtain ⟨y, rfl⟩ : x ∈ Set.range ι := hrange ▸ hx.1
  have hyD : y ∈ (D'.support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact hx.2
  have hD := stalk_comap_component (B := B) hB (a := ⟨σ.snd, σ.snd_mem⟩)
    (b := ⟨σ.fst, σ.fst_mem⟩) hab
  obtain ⟨P, hP⟩ := MMP.Mori.exists_primeDivisor_support_eq_connectedComponentIn D' hD hyD
  refine ⟨P, ?_⟩
  have himg : ι '' (D'.support : Set _) = σ.fst.support ∩ σ.snd.support := by
    apply subset_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨(hrange ▸ ⟨w, rfl⟩ : ι w ∈ (σ.fst.idealSheaf.support : Set Z)), ?_⟩
      have hw' : w ∈ ((σ.snd.idealSheaf.comap ι).support : Set _) := hw
      rw [Scheme.IdealSheafData.support_comap] at hw'
      exact hw'
    · rintro z ⟨h1, h2⟩
      obtain ⟨w, rfl⟩ : z ∈ Set.range ι := hrange ▸ h1
      refine ⟨w, ?_, rfl⟩
      change w ∈ ((σ.snd.idealSheaf.comap ι).support : Set _)
      rw [Scheme.IdealSheafData.support_comap]
      exact h2
  rw [hP, MMP.Mori.image_connectedComponentIn_of_isEmbedding ι.isClosedEmbedding.isEmbedding hyD,
    himg, hxc]

/-- The prime divisor `ρ(σ)` of `Eᵢ` underlying a double surface `σ` of `(Eᵢ, Eⱼ)`. -/
private noncomputable def rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    Mori.PrimeDivisor σ.fst.idealSheaf.subscheme :=
  (exists_primeDivisor_image_support_eq hB σ).choose

private theorem image_support_rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    σ.fst.idealSheaf.subschemeι '' (rho hB σ).support = σ.carrier :=
  (exists_primeDivisor_image_support_eq hB σ).choose_spec

/-- The closure of the image of the generic point of `ρ(σ)` is the double surface. -/
private theorem closure_genericPoint_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    closure {σ.fst.idealSheaf.subschemeι (rho hB σ).genericPoint} = σ.carrier := by
  rw [← Set.image_singleton, σ.fst.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_support_rho]

/-- **Double surfaces of a component are determined by their surface.** Two double surfaces with
the same first component and the same surface are equal: were their second components distinct,
the surface would lie in three components, and at its generic point, of coheight one on `Eᵢ`,
two distinct members of a regular system of parameters of `𝒪_{Eᵢ}` would cut out the other two. -/
private theorem eq_of_fst_eq_of_carrier_eq {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {σ τ : DoubleSurface B} (h₁ : σ.fst = τ.fst) (h₃ : σ.carrier = τ.carrier) : σ = τ := by
  by_cases h₂ : σ.snd = τ.snd
  · exact DoubleSurface.ext h₁ h₂ h₃
  exfalso
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set b : B.support := ⟨σ.fst, σ.fst_mem⟩
  set ι := σ.fst.idealSheaf.subschemeι
  set η := (rho hB σ).genericPoint
  have hηS : ι η ∈ σ.carrier := by
    rw [← image_support_rho hB σ]
    refine ⟨η, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hτS : ι η ∈ τ.carrier := h₃ ▸ hηS
  obtain ⟨m, w, c', hw, -, hinj⟩ := MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
    (hasSNCWith_component hB b) (not_component_subset b) η
  have hne1 : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ b :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  have hne2 : (⟨τ.snd, τ.snd_mem⟩ : B.support) ≠ b :=
    fun h => τ.fst_ne_snd (h₁ ▸ (congrArg Subtype.val h).symm)
  have hm1 : η ∈ ((σ.snd.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact (σ.carrier_subset hηS).2
  have hm2 : η ∈ ((τ.snd.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact (τ.carrier_subset hτS).2
  have hc : c' ⟨⟨_, hne1⟩, hm1⟩ ≠ c' ⟨⟨_, hne2⟩, hm2⟩ := fun h =>
    h₂ (congrArg (fun e => e.1.1.1) (hinj h))
  have hdim := hw.2
  rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hdim
  have hm : m = 1 := by exact_mod_cast hdim.symm
  subst hm
  exact hc (Subsingleton.elim _ _)

/-- A double surface is closed. -/
private theorem isClosed_carrier {Z : Scheme.{0}} {B : Divisor Z} (σ : DoubleSurface B) :
    IsClosed σ.carrier := by
  obtain ⟨x, hx, hxc⟩ := σ.isComponent
  rw [← hxc, connectedComponentIn_eq_image hx]
  exact (σ.fst.idealSheaf.support.isClosed.inter
    σ.snd.idealSheaf.support.isClosed).isClosedEmbedding_subtypeVal.isClosedMap _
    isClosed_connectedComponent

/-- On a Noetherian scheme the rest of `Eᵢ ∩ Eⱼ` off a double surface is closed: it is the union of
the finitely many other connected components. -/
private theorem isClosed_inter_diff_carrier {Z : Scheme.{0}} [NoetherianSpace Z] {B : Divisor Z}
    (σ : DoubleSurface B) :
    IsClosed ((σ.fst.support ∩ σ.snd.support) \ σ.carrier) := by
  have hF : IsClosed (σ.fst.support ∩ σ.snd.support) :=
    σ.fst.idealSheaf.support.isClosed.inter σ.snd.idealSheaf.support.isClosed
  have hfin := DoubleSurface.finite_connectedComponentIn hF
  have heq : (σ.fst.support ∩ σ.snd.support) \ σ.carrier =
      ⋃ C ∈ {C | ∃ x ∈ σ.fst.support ∩ σ.snd.support,
        connectedComponentIn (σ.fst.support ∩ σ.snd.support) x = C} \ {σ.carrier}, C := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨hz, hzc⟩
      refine ⟨_, ⟨⟨z, hz, rfl⟩, fun h => hzc (h ▸ mem_connectedComponentIn hz)⟩,
        mem_connectedComponentIn hz⟩
    · rintro ⟨C, ⟨⟨x, hx, rfl⟩, hne⟩, hzC⟩
      refine ⟨connectedComponentIn_subset _ _ hzC, fun hzc => hne ?_⟩
      rw [σ.carrier_eq_connectedComponentIn hzc, connectedComponentIn_eq hzC]
  rw [heq]
  refine hfin.sdiff.isClosed_biUnion fun C hC => ?_
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hC
  rw [connectedComponentIn_eq_image hx]
  exact hF.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent

/-- `Eⱼ ∩ Eᵢ = ρ(σ) ⊔ T'` on `Eᵢ`, with `T'` (the other connected components) disjoint from
`ρ(σ)`. -/
private theorem exists_closeds_sup_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    ∃ T' : Closeds σ.fst.idealSheaf.subscheme,
      (rho hB σ).idealSheaf.support ⊔ T' =
        (σ.snd.idealSheaf.comap σ.fst.idealSheaf.subschemeι).support ∧
      Disjoint (rho hB σ).idealSheaf.support T' := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  set ι := σ.fst.idealSheaf.subschemeι
  set P := rho hB σ
  have hrange : Set.range ι = (σ.fst.idealSheaf.support : Set Z) := by
    rw [← σ.fst.idealSheaf.range_subschemeι]
  have hPS : (P.support : Set _) = ι ⁻¹' σ.carrier := by
    rw [← image_support_rho hB σ, Set.preimage_image_eq _ ι.isClosedEmbedding.injective]
  let T' : TopologicalSpace.Closeds σ.fst.idealSheaf.subscheme :=
    ⟨ι ⁻¹' ((σ.fst.support ∩ σ.snd.support) \ σ.carrier),
      (isClosed_inter_diff_carrier σ).preimage ι.continuous⟩
  refine ⟨T', ?_, ?_⟩
  · apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_sup]
    change (P.support : Set _) ∪ _ = ((σ.snd.idealSheaf.comap ι).support : Set _)
    rw [Scheme.IdealSheafData.support_comap, hPS]
    ext z
    simp only [T', TopologicalSpace.Closeds.coe_mk, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_union, Set.mem_preimage, Set.mem_sdiff, Set.mem_inter_iff]
    have hz : ι z ∈ (σ.fst.idealSheaf.support : Set Z) := hrange ▸ ⟨z, rfl⟩
    constructor
    · rintro (h | h)
      · exact (σ.carrier_subset h).2
      · exact h.1.2
    · intro h
      by_cases hc : ι z ∈ σ.carrier
      · exact Or.inl hc
      · exact Or.inr ⟨⟨hz, h⟩, hc⟩
  · rw [disjoint_iff]
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_inf, TopologicalSpace.Closeds.coe_bot]
    change (P.support : Set _) ∩ _ = ∅
    rw [hPS]
    ext z
    simp only [T', TopologicalSpace.Closeds.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun h _ => h

/-- **`Eⱼ ∩ Eᵢ = ρ(σ) + R` on `Eᵢ`, with `R` missing `ρ(σ)`.** For a double surface `σ` of
`(Eᵢ, Eⱼ)`, the divisor `Eⱼ ∩ Eᵢ` of `Eᵢ` is the sum of the prime divisor `ρ(σ)` and the
effective Cartier divisor `R` of the other connected components, and `R` restricts trivially to
`ρ(σ)`. -/
private theorem exists_comap_eq_rho_mul {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) :
    ∃ R : σ.fst.idealSheaf.subscheme.IdealSheafData,
      σ.snd.idealSheaf.comap σ.fst.idealSheaf.subschemeι = (rho hB σ).idealSheaf * R ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (rho hB σ).idealSheaf ∧
      Stacks.Divisors.IsEffectiveCartierDivisor R ∧
      R.comap (rho hB σ).idealSheaf.subschemeι = ⊤ := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  set ι := σ.fst.idealSheaf.subschemeι
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ι
  set P := rho hB σ
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  have hD := stalk_comap_component (B := B) hB (a := ⟨σ.snd, σ.snd_mem⟩)
    (b := ⟨σ.fst, σ.fst_mem⟩) hab
  set D' := σ.snd.idealSheaf.comap ι
  have : IsReduced D'.subscheme := (isEffectiveCartierDivisor_comap_component hB hab).2
  obtain ⟨T', hST, hdisj⟩ := exists_closeds_sup_rho hB σ
  have := P.integral
  have hPV : P.idealSheaf = Scheme.IdealSheafData.vanishingIdeal P.idealSheaf.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  refine ⟨Scheme.IdealSheafData.vanishingIdeal T', ?_, ?_, ?_, ?_⟩
  · rw [hPV]
    exact MMP.Mori.eq_vanishingIdeal_mul_vanishingIdeal D' _ T' hST hdisj
  · rw [hPV]
    exact MMP.Resolution.isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
      (MMP.Mori.stalk_vanishingIdeal_eq_span_parameter D' hD _ T' hST hdisj)
  · rw [sup_comm] at hST
    exact MMP.Resolution.isEffectiveCartierDivisor_of_stalk_eq_span_parameter _
      (MMP.Mori.stalk_vanishingIdeal_eq_span_parameter D' hD T' _ hST hdisj.symm)
  · rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    apply TopologicalSpace.Closeds.ext
    rw [TopologicalSpace.Closeds.coe_preimage, TopologicalSpace.Closeds.coe_bot,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz₀ : P.idealSheaf.subschemeι z ∈ P.idealSheaf.support := by
      rw [← SetLike.mem_coe, ← P.idealSheaf.range_subschemeι]; exact ⟨z, rfl⟩
    have : P.idealSheaf.subschemeι z ∈ ((P.idealSheaf.support ⊓ T' : Closeds _) : Set _) :=
      ⟨hz₀, hz⟩
    rw [hdisj.eq_bot] at this
    exact this

/-- The coefficient of `Zᵢ(a)` along `ρ(σ)` is `a σ`. -/
private theorem surfaceCoefficientCoeff_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) (σ : DoubleSurface B) :
    surfaceCoefficientCoeff a σ.fst (rho hB σ) = a σ := by
  rw [surfaceCoefficientCoeff]
  have hcl := closure_genericPoint_rho hB σ
  refine (finsum_eq_single _ ⟨σ, rfl, hcl.symm⟩ fun τ hτ => absurd ?_ hτ).trans rfl
  exact Subtype.ext (eq_of_fst_eq_of_carrier_eq hB τ.2.1 (τ.2.2.trans hcl))

/-- The surface of a double surface `σ` of `(Eᵢ, Eⱼ)` is the image of `ρ(σ)` in `Z`. -/
private theorem range_comp_rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    Set.range ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) = σ.carrier := by
  rw [← image_support_rho hB σ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  congr 1
  exact (rho hB σ).idealSheaf.range_subschemeι

/-- `ρ(σ)` read on a component `E` equal to the first component of `σ`. -/
public noncomputable def rhoOf {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {E : Mori.PrimeDivisor Z}
    (σ : DoubleSurface B) (h : σ.fst = E) : Mori.PrimeDivisor E.idealSheaf.subscheme :=
  h ▸ rho hB σ

public theorem image_support_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E) :
    E.idealSheaf.subschemeι '' (rhoOf hB σ h).support = σ.carrier := by
  subst h; exact image_support_rho hB σ

private theorem surfaceCoefficientCoeff_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E) :
    surfaceCoefficientCoeff a E (rhoOf hB σ h) = a σ := by
  subst h; exact surfaceCoefficientCoeff_rho hB a σ

/-- The image of the support of a prime divisor of `E` is the closure of the image of its generic
point. -/
private theorem image_support_eq_closure {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    E.idealSheaf.subschemeι '' P.support = closure {E.idealSheaf.subschemeι P.genericPoint} := by
  rw [← Set.image_singleton, E.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- Prime divisors of `E` with the same image in `Z` are equal. -/
private theorem eq_of_image_support_eq {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    {P Q : Mori.PrimeDivisor E.idealSheaf.subscheme}
    (h : E.idealSheaf.subschemeι '' P.support = E.idealSheaf.subschemeι '' Q.support) : P = Q := by
  rw [image_support_eq_closure, image_support_eq_closure] at h
  have hQ : IsGenericPoint (E.idealSheaf.subschemeι Q.genericPoint)
      (closure {E.idealSheaf.subschemeι P.genericPoint}) := by
    rw [h]; exact isGenericPoint_closure
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (E.idealSheaf.subschemeι.isClosedEmbedding.injective (isGenericPoint_closure.eq hQ))

private theorem rhoOf_injective {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} {σ τ : DoubleSurface B} (h : σ.fst = E) (h' : τ.fst = E)
    (he : rhoOf hB σ h = rhoOf hB τ h') : σ = τ := by
  refine eq_of_fst_eq_of_carrier_eq hB (h.trans h'.symm) ?_
  rw [← image_support_rhoOf hB σ h, ← image_support_rhoOf hB τ h', he]

/-- **(2c) The coefficient of `Zᵢ(a)` vanishes off the prime divisors `ρ(σ)`.** -/
private theorem surfaceCoefficientCoeff_eq_zero {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : ∀ (σ : DoubleSurface B) (h : σ.fst = E), rhoOf hB σ h ≠ P) :
    surfaceCoefficientCoeff a E P = 0 := by
  rw [surfaceCoefficientCoeff]
  have : IsEmpty {σ : DoubleSurface B // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}} := by
    refine ⟨fun σ => hP σ.1 σ.2.1 (eq_of_image_support_eq ?_)⟩
    rw [image_support_rhoOf, σ.2.2, image_support_eq_closure]
  exact finsum_of_isEmpty _

/-- **(2d) `Zᵢ(a) = ∑_{σ ⊆ Eᵢ} a_σ ρ(σ)`**, as an expansion of finitely supported sums. -/
public theorem sum_surfaceCoefficientDivisor {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) (E : Mori.PrimeDivisor Z)
    [Fintype {σ : DoubleSurface B // σ.fst = E}]
    {M : Type*} [AddCommMonoid M] (f : Mori.PrimeDivisor E.idealSheaf.subscheme → ℚ → M)
    (hf : ∀ P, f P 0 = 0) :
    (surfaceCoefficientDivisor a E).sum f =
      ∑ σ : {σ : DoubleSurface B // σ.fst = E}, f (rhoOf hB σ.1 σ.2) (a σ.1) := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  have hsub : (surfaceCoefficientDivisor a E).support ⊆
      Finset.univ.image fun σ : {σ : DoubleSurface B // σ.fst = E} => rhoOf hB σ.1 σ.2 := by
    intro P hP
    by_contra hnot
    refine Finsupp.mem_support_iff.mp hP ?_
    rw [← DivisorWithCoeffs.coeff_apply, coeff_surfaceCoefficientDivisor]
    refine surfaceCoefficientCoeff_eq_zero hB a P fun σ h he => hnot ?_
    exact Finset.mem_image.mpr ⟨⟨σ, h⟩, Finset.mem_univ _, he⟩
  rw [Finsupp.sum_of_support_subset _ hsub _ fun P _ => hf P, Finset.sum_image
    fun σ _ τ _ he => Subtype.ext (rhoOf_injective hB σ.2 τ.2 he)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← DivisorWithCoeffs.coeff_apply, coeff_surfaceCoefficientDivisor,
    surfaceCoefficientCoeff_rhoOf]

/-- Distinct double surfaces of the same ordered pair `(Eᵢ, Eⱼ)` give disjoint prime divisors
`ρ` of `Eᵢ`. -/
private theorem disjoint_support_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} {σ τ : DoubleSurface B} (h : σ.fst = E) (h' : τ.fst = E)
    (h₂ : σ.snd = τ.snd) (hne : σ ≠ τ) :
    Disjoint (rhoOf hB σ h).support (rhoOf hB τ h').support := by
  have hd := DoubleSurface.disjoint_carrier (h.trans h'.symm) h₂ hne
  rw [← image_support_rhoOf hB σ h, ← image_support_rhoOf hB τ h'] at hd
  exact (Set.disjoint_image_iff E.idealSheaf.subschemeι.isClosedEmbedding.injective).mp hd

/-! ### Bookkeeping: triple curves, coefficients and numbers extended by zero -/

/-- The first component of a double surface, as an element of the support. -/
private abbrev fstS {Z : Scheme.{0}} {B : Divisor Z} (σ : DoubleSurface B) : B.support :=
  ⟨σ.fst, σ.fst_mem⟩

/-- The second component of a double surface, as an element of the support. -/
private abbrev sndS {Z : Scheme.{0}} {B : Divisor Z} (σ : DoubleSurface B) : B.support :=
  ⟨σ.snd, σ.snd_mem⟩

/-- `T` is a connected component of `E₁ ∩ E₂ ∩ E₃`. -/
private def IsTripleCurve {Z : Scheme.{0}} (E₁ E₂ E₃ : Mori.PrimeDivisor Z) (T : Set Z) : Prop :=
  T.Nonempty ∧ T ⊆ E₁.support ∩ E₂.support ∩ E₃.support ∧
    ∃ x ∈ E₁.support ∩ E₂.support ∩ E₃.support,
      connectedComponentIn (E₁.support ∩ E₂.support ∩ E₃.support) x = T

private theorem isTripleCurve_congr {Z : Scheme.{0}} {E₁ E₂ E₃ F₁ F₂ F₃ : Mori.PrimeDivisor Z}
    (h : E₁.support ∩ E₂.support ∩ E₃.support = F₁.support ∩ F₂.support ∩ F₃.support)
    (T : Set Z) : IsTripleCurve E₁ E₂ E₃ T ↔ IsTripleCurve F₁ F₂ F₃ T := by
  unfold IsTripleCurve; rw [h]

private theorem IsTripleCurve.isPreconnected {Z : Scheme.{0}} {E₁ E₂ E₃ : Mori.PrimeDivisor Z}
    {T : Set Z} (h : IsTripleCurve E₁ E₂ E₃ T) : _root_.IsPreconnected T := by
  obtain ⟨-, -, x, -, rfl⟩ := h
  exact isPreconnected_connectedComponentIn

private theorem finite_isTripleCurve {Z : Scheme.{0}} [NoetherianSpace Z]
    (E₁ E₂ E₃ : Mori.PrimeDivisor Z) : {T | IsTripleCurve E₁ E₂ E₃ T}.Finite :=
  (DoubleSurface.finite_connectedComponentIn
    ((E₁.idealSheaf.support.isClosed.inter E₂.idealSheaf.support.isClosed).inter
      E₃.idealSheaf.support.isClosed)).subset fun _ h => h.2.2

/-- The triple curves of `E₁ ∩ E₂ ∩ E₃`, as a finset. -/
private noncomputable def tcs {Z : Scheme.{0}} [NoetherianSpace Z]
    (E₁ E₂ E₃ : Mori.PrimeDivisor Z) : Finset (Set Z) :=
  (finite_isTripleCurve E₁ E₂ E₃).toFinset

private theorem mem_tcs {Z : Scheme.{0}} [NoetherianSpace Z] {E₁ E₂ E₃ : Mori.PrimeDivisor Z}
    {T : Set Z} : T ∈ tcs E₁ E₂ E₃ ↔ IsTripleCurve E₁ E₂ E₃ T := by
  simp [tcs]

private theorem tcs_congr {Z : Scheme.{0}} [NoetherianSpace Z]
    {E₁ E₂ E₃ F₁ F₂ F₃ : Mori.PrimeDivisor Z}
    (h : E₁.support ∩ E₂.support ∩ E₃.support = F₁.support ∩ F₂.support ∩ F₃.support) :
    tcs E₁ E₂ E₃ = tcs F₁ F₂ F₃ := by
  ext T; rw [mem_tcs, mem_tcs, isTripleCurve_congr h]

/-- The coefficient `a_{xy,T}`, extended by zero. -/
private noncomputable def coeffT {Z : Scheme.{0}} {B : Divisor Z} (a : DoubleSurface B → ℚ)
    (x y : B.support) (T : Set Z) : ℚ := by
  classical
  exact if h : x ≠ y ∧ T.Nonempty ∧ T ⊆ x.1.support ∩ y.1.support then
    coeffAlong a x.2 y.2 (fun e => h.1 (Subtype.ext e)) h.2.1 h.2.2 else 0

private theorem coeffAlong_eq_coeffT {Z : Scheme.{0}} {B : Divisor Z} (a : DoubleSurface B → ℚ)
    (x y : B.support) (hne : x.1 ≠ y.1) {T : Set Z} (hT : T.Nonempty)
    (hTE : T ⊆ x.1.support ∩ y.1.support) :
    coeffAlong a x.2 y.2 hne hT hTE = coeffT a x y T := by
  rw [coeffT, dite_eq_left ⟨fun e => hne (congrArg Subtype.val e), hT, hTE⟩]

private theorem coeffT_swap {Z : Scheme.{0}} {B : Divisor Z} {a : DoubleSurface B → ℚ}
    (ha : a ∈ orientedSurfaceCoefficients B) (x y : B.support) {T : Set Z}
    (hTc : _root_.IsPreconnected T) : coeffT a y x T = -coeffT a x y T := by
  by_cases h : x ≠ y ∧ T.Nonempty ∧ T ⊆ x.1.support ∩ y.1.support
  · rw [← coeffAlong_eq_coeffT a x y (fun e => h.1 (Subtype.ext e)) h.2.1 h.2.2,
      ← coeffAlong_eq_coeffT a y x (fun e => h.1 (Subtype.ext e.symm)) h.2.1
        (Set.inter_comm x.1.support y.1.support ▸ h.2.2)]
    exact coeffAlong_swap ha x.2 y.2 _ h.2.1 h.2.2 hTc
  · have h' : ¬ (y ≠ x ∧ T.Nonempty ∧ T ⊆ y.1.support ∩ x.1.support) := fun h' =>
      h ⟨h'.1.symm, h'.2.1, Set.inter_comm y.1.support x.1.support ▸ h'.2.2⟩
    rw [coeffT, coeffT, dite_eq_right h, dite_eq_right h', neg_zero]

/-- **Ordered distinct triples, grouped by their sorted form.** -/
private theorem sum_distinct_eq_sum_sorted {ι M : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommMonoid M] [∀ x y z : ι, Decidable (x ≠ y ∧ x ≠ z ∧ y ≠ z)]
    [∀ i j l : ι, Decidable (i < j ∧ j < l)] (F : ι → ι → ι → M) :
    ∑ x, ∑ y, ∑ z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then F x y z else 0) =
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then
        F i j l + F i l j + F j i l + F j l i + F l i j + F l j i else 0) := by
  have key : ∀ x y z : ι, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then F x y z else 0) =
      (if x < y ∧ y < z then F x y z else 0) + (if x < z ∧ z < y then F x y z else 0) +
      (if y < x ∧ x < z then F x y z else 0) + (if z < x ∧ x < y then F x y z else 0) +
      (if y < z ∧ z < x then F x y z else 0) + (if z < y ∧ y < x then F x y z else 0) := by
    intro x y z
    rcases lt_trichotomy x y with h1 | h1 | h1 <;> rcases lt_trichotomy x z with h2 | h2 | h2 <;>
      rcases lt_trichotomy y z with h3 | h3 | h3 <;>
      simp_all [ne_of_lt, ne_of_gt, not_lt_of_gt] <;> order
  have h2 : ∑ x, ∑ y, ∑ z, (if x < z ∧ z < y then F x y z else 0) =
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then F i l j else 0) :=
    Finset.sum_congr rfl fun x _ => Finset.sum_comm
  have h3 : ∑ x, ∑ y, ∑ z, (if y < x ∧ x < z then F x y z else 0) =
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then F j i l else 0) := Finset.sum_comm
  have h4 : ∑ x, ∑ y, ∑ z, (if z < x ∧ x < y then F x y z else 0) =
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then F j l i else 0) := by
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  have h5 : ∑ x, ∑ y, ∑ z, (if y < z ∧ z < x then F x y z else 0) =
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then F l i j else 0) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  have h6 : ∑ x, ∑ y, ∑ z, (if z < y ∧ y < x then F x y z else 0) =
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then F l j i else 0) := by
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm,
      Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  simp_rw [key, Finset.sum_add_distrib, ite_add_zero, Finset.sum_add_distrib]
  rw [h2, h3, h4, h5, h6]

open Classical in
/-- A triple curve of `Eₓ ∩ E_y ∩ E_z` lies in exactly one double surface of `(Eₓ, E_y)`. -/
private theorem sum_ite_subset_carrier {Z : Scheme.{0}} {B : Divisor Z} [Fintype (DoubleSurface B)]
    {M : Type*} [AddCommMonoid M] (a : DoubleSurface B → ℚ) (x y z : B.support) {T : Set Z}
    (hT : IsTripleCurve x.1 y.1 z.1 T) (φ : ℚ → M) :
    ∑ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y ∧ T ⊆ σ.carrier then φ (a σ) else 0) =
      if x ≠ y then φ (coeffT a x y T) else 0 := by
  classical
  have hTxy : T ⊆ x.1.support ∩ y.1.support := fun t ht => (hT.2.1 ht).1
  split_ifs with hxy
  · have hne : x.1 ≠ y.1 := fun e => hxy (Subtype.ext e)
    set τ := DoubleSurface.through x.2 y.2 hne hT.1 hTxy
    rw [Finset.sum_eq_single τ]
    · rw [ite_eq_left ⟨rfl, rfl,
        DoubleSurface.subset_through x.2 y.2 hne hT.1 hTxy hT.isPreconnected⟩,
        ← coeffAlong_eq_coeffT a x y hne hT.1 hTxy]
      rfl
    · intro σ _ hστ
      rw [ite_eq_right]
      rintro ⟨hx, hy, hσ⟩
      refine hστ (DoubleSurface.eq_through x.2 y.2 hne hT.1 hTxy hT.isPreconnected σ
        (congrArg Subtype.val hx) (congrArg Subtype.val hy) ⟨hT.1.some, hσ hT.1.some_mem,
          hT.1.some_mem⟩)
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun σ _ => ite_eq_right ?_
    rintro ⟨hx, hy, -⟩
    exact σ.fst_ne_snd (congrArg Subtype.val (hx.trans ((not_ne_iff.mp hxy).trans hy.symm)))

open Classical in
/-- Sums over double surfaces, fibred by their ordered pair of components. -/
private theorem sum_doubleSurface_eq_sum_pair {Z : Scheme.{0}} {B : Divisor Z}
    [Fintype (DoubleSurface B)] {M : Type*} [AddCommMonoid M] (Φ : DoubleSurface B → M) :
    ∑ σ, Φ σ = ∑ x : B.support, ∑ y : B.support,
      ∑ σ, (if fstS σ = x ∧ sndS σ = y then Φ σ else 0) := by
  classical
  symm
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [ite_and]

open Classical in
/-- A sum over all double surfaces is the sum over those with `fst < snd` of the terms of a double
surface and of its swap. -/
private theorem sum_doubleSurface_eq_sum_lt_add_swap {Z : Scheme.{0}} {B : Divisor Z}
    [Fintype (DoubleSurface B)] [LinearOrder B.support] {M : Type*} [AddCommMonoid M]
    (g : DoubleSurface B → M) :
    ∑ σ, g σ = ∑ σ, (if fstS σ < sndS σ then g σ + g σ.swap else 0) := by
  classical
  have hsw : Function.Involutive (DoubleSurface.swap (B := B)) := DoubleSurface.swap_swap
  have h1 : ∑ σ, (if sndS σ < fstS σ then g σ else 0) =
      ∑ σ, (if fstS σ < sndS σ then g σ.swap else 0) :=
    (Equiv.sum_comp hsw.toPerm (fun σ => if sndS σ < fstS σ then g σ else 0)).symm.trans
      (Finset.sum_congr rfl fun σ _ => rfl)
  have h2 : ∀ σ : DoubleSurface B, g σ =
      (if fstS σ < sndS σ then g σ else 0) + (if sndS σ < fstS σ then g σ else 0) := by
    intro σ
    have hne : fstS σ ≠ sndS σ := fun e => σ.fst_ne_snd (congrArg Subtype.val e)
    rcases lt_or_gt_of_ne hne with h | h
    · rw [ite_eq_left h, ite_eq_right (not_lt_of_gt h), add_zero]
    · rw [ite_eq_right (not_lt_of_gt h), ite_eq_left h, zero_add]
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_add_distrib, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs <;> simp

open Classical in
/-- **The transversal terms of the left side, per ordered pair.** For the double surfaces of
`(Eₓ, E_y)`, the curve terms `∑_{z ≠ x, y} g_z ∑_{T ⊆ σ} N_T` regroup over the triple curves. -/
private theorem sum_lhs_transversal {Z : Scheme.{0}} {B : Divisor Z} [Fintype (DoubleSurface B)]
    [NoetherianSpace Z] (a : DoubleSurface B → ℚ) (x y : B.support) (φ : ℚ → ℚ)
    (g : B.support → ℚ) (N : Set Z → ℚ) :
    ∑ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y then φ (a σ) * ∑ z : B.support,
      (if z ≠ x ∧ z ≠ y then g z * ∑ T ∈ tcs x.1 y.1 z.1,
        (if T ⊆ σ.carrier then N T else 0) else 0) else 0) =
    ∑ z : B.support, ∑ T ∈ tcs x.1 y.1 z.1,
      (if z ≠ x ∧ z ≠ y ∧ x ≠ y then φ (coeffT a x y T) * g z * N T else 0) := by
  have h1 : ∀ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y then φ (a σ) * ∑ z : B.support,
      (if z ≠ x ∧ z ≠ y then g z * ∑ T ∈ tcs x.1 y.1 z.1,
        (if T ⊆ σ.carrier then N T else 0) else 0) else 0) =
      ∑ z : B.support, ∑ T ∈ tcs x.1 y.1 z.1, (if fstS σ = x ∧ sndS σ = y ∧ T ⊆ σ.carrier then
        (if z ≠ x ∧ z ≠ y then φ (a σ) * g z * N T else 0) else 0) := by
    intro σ
    by_cases hσ : fstS σ = x ∧ sndS σ = y
    · rw [ite_eq_left hσ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z ≠ x ∧ z ≠ y
      · rw [ite_eq_left hz, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hT : T ⊆ σ.carrier
        · rw [ite_eq_left hT, ite_eq_left ⟨hσ.1, hσ.2, hT⟩, ite_eq_left hz]; ring
        · rw [ite_eq_right hT, ite_eq_right fun h => hT h.2.2, mul_zero, mul_zero]
      · rw [ite_eq_right hz, mul_zero]
        exact (Finset.sum_eq_zero fun T _ => by split_ifs <;> rfl).symm
    · rw [ite_eq_right hσ]
      exact (Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun T _ =>
        ite_eq_right fun h => hσ ⟨h.1, h.2.1⟩).symm
  rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [sum_ite_subset_carrier a x y z (mem_tcs.mp hT)
    (fun q => if z ≠ x ∧ z ≠ y then φ q * g z * N T else 0)]
  by_cases hxy : x ≠ y <;> by_cases hz : z ≠ x ∧ z ≠ y <;> simp [hxy, hz]

open Classical in
/-- The inner sum of the transversal terms of the right side, regrouped over the triple curves. -/
private theorem sum_rhs_transversal_inner {Z : Scheme.{0}} {B : Divisor Z}
    [Fintype (DoubleSurface B)] [NoetherianSpace Z] (a : DoubleSurface B → ℚ) (x y : B.support)
    (σ : DoubleSurface B) (N : Set Z → ℚ) :
    ∑ τ : DoubleSurface B, (if fstS τ = x ∧ sndS τ ≠ y then a σ * a τ * ∑ T ∈ tcs x.1 y.1 τ.snd,
        (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) =
      ∑ z : B.support, ∑ T ∈ tcs x.1 y.1 z.1,
        (if T ⊆ σ.carrier ∧ x ≠ z ∧ z ≠ y then a σ * coeffT a x z T * N T else 0) := by
  have h1 : ∀ τ : DoubleSurface B, (if fstS τ = x ∧ sndS τ ≠ y then a σ * a τ *
      ∑ T ∈ tcs x.1 y.1 τ.snd, (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) =
      ∑ z : B.support, ∑ T ∈ tcs x.1 y.1 z.1, (if fstS τ = x ∧ sndS τ = z ∧ T ⊆ τ.carrier then
        (if T ⊆ σ.carrier ∧ z ≠ y then a σ * a τ * N T else 0) else 0) := by
    intro τ
    rw [Finset.sum_eq_single (sndS τ)]
    · by_cases hτ : fstS τ = x ∧ sndS τ ≠ y
      · rw [ite_eq_left hτ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        by_cases hT : T ⊆ σ.carrier ∧ T ⊆ τ.carrier
        · rw [ite_eq_left hT, ite_eq_left ⟨hτ.1, rfl, hT.2⟩, ite_eq_left ⟨hT.1, hτ.2⟩]
        · rw [ite_eq_right hT, mul_zero]
          split_ifs with h h' <;> first | rfl | exact absurd ⟨h'.1, h.2.2⟩ hT
      · rw [ite_eq_right hτ]
        refine (Finset.sum_eq_zero fun T _ => ?_).symm
        split_ifs with h h' <;> first | rfl | exact absurd ⟨h.1, h'.2⟩ hτ
    · intro z _ hz
      exact Finset.sum_eq_zero fun T _ => ite_eq_right fun h => hz h.2.1.symm
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun τ _ => h1 τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hT' : IsTripleCurve x.1 z.1 y.1 T :=
    (isTripleCurve_congr (by rw [Set.inter_right_comm]) T).mp (mem_tcs.mp hT)
  rw [sum_ite_subset_carrier a x z y hT'
    (fun q => if T ⊆ σ.carrier ∧ z ≠ y then a σ * q * N T else 0)]
  by_cases hxz : x ≠ z
  · rw [ite_eq_left hxz]
    by_cases hz : T ⊆ σ.carrier ∧ z ≠ y
    · rw [ite_eq_left hz, ite_eq_left ⟨hz.1, hxz, hz.2⟩]
    · rw [ite_eq_right hz, ite_eq_right fun h => hz ⟨h.1, h.2.2⟩]
  · rw [ite_eq_right hxz, ite_eq_right fun h => hxz h.2.1]

open Classical in
/-- **The transversal terms of the right side, per ordered pair.** -/
private theorem sum_rhs_transversal {Z : Scheme.{0}} {B : Divisor Z} [Fintype (DoubleSurface B)]
    [NoetherianSpace Z] (a : DoubleSurface B → ℚ) (x y : B.support) (r : ℚ) (N : Set Z → ℚ) :
    ∑ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y then r * ∑ τ : DoubleSurface B,
      (if fstS τ = x ∧ sndS τ ≠ y then a σ * a τ * ∑ T ∈ tcs x.1 y.1 τ.snd,
        (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) else 0) =
    ∑ z : B.support, ∑ T ∈ tcs x.1 y.1 z.1,
      (if x ≠ y ∧ x ≠ z ∧ y ≠ z then r * coeffT a x y T * coeffT a x z T * N T else 0) := by
  have h1 : ∀ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y then r * ∑ τ : DoubleSurface B,
      (if fstS τ = x ∧ sndS τ ≠ y then a σ * a τ * ∑ T ∈ tcs x.1 y.1 τ.snd,
        (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) else 0) =
      ∑ z : B.support, ∑ T ∈ tcs x.1 y.1 z.1, (if fstS σ = x ∧ sndS σ = y ∧ T ⊆ σ.carrier then
        (if x ≠ z ∧ z ≠ y then r * a σ * coeffT a x z T * N T else 0) else 0) := by
    intro σ
    rw [sum_rhs_transversal_inner]
    by_cases hσ : fstS σ = x ∧ sndS σ = y
    · rw [ite_eq_left hσ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hT : T ⊆ σ.carrier
      · by_cases hz : x ≠ z ∧ z ≠ y
        · rw [ite_eq_left ⟨hT, hz⟩, ite_eq_left ⟨hσ.1, hσ.2, hT⟩, ite_eq_left hz]; ring
        · rw [ite_eq_right fun h => hz h.2, ite_eq_left ⟨hσ.1, hσ.2, hT⟩, ite_eq_right hz, mul_zero]
      · rw [ite_eq_right fun h => hT h.1, ite_eq_right fun h => hT h.2.2, mul_zero]
    · rw [ite_eq_right hσ]
      exact (Finset.sum_eq_zero fun z _ => Finset.sum_eq_zero fun T _ =>
        ite_eq_right fun h => hσ ⟨h.1, h.2.1⟩).symm
  rw [Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [sum_ite_subset_carrier a x y z (mem_tcs.mp hT)
    (fun q => if x ≠ z ∧ z ≠ y then r * q * coeffT a x z T * N T else 0)]
  by_cases hxy : x ≠ y
  · rw [ite_eq_left hxy]
    by_cases hz : x ≠ z ∧ z ≠ y
    · rw [ite_eq_left hz, ite_eq_left ⟨hxy, hz.1, hz.2.symm⟩]
    · rw [ite_eq_right hz, ite_eq_right fun h => hz ⟨h.2.1, h.2.2.symm⟩]
  · rw [ite_eq_right hxy, ite_eq_right fun h => hxy h.1]

/-- Sums over the components and the double surfaces with that first component. -/
private theorem sum_fst_subtype {Z : Scheme.{0}} {B : Divisor Z} [Fintype (DoubleSurface B)]
    [∀ i : B.support, Fintype {σ : DoubleSurface B // σ.fst = i.1}] {M : Type*}
    [AddCommMonoid M] (G : ∀ i : B.support, {σ : DoubleSurface B // σ.fst = i.1} → M) :
    ∑ i, ∑ σ, G i σ = ∑ σ : DoubleSurface B, G (fstS σ) ⟨σ, rfl⟩ := by
  refine (Fintype.sum_sigma (fun p : (Σ i : B.support, {σ : DoubleSurface B // σ.fst = i.1}) =>
    G p.1 p.2)).symm.trans ?_
  refine Fintype.sum_equiv
    { toFun := fun p => p.2.1
      invFun := fun σ => ⟨fstS σ, ⟨σ, rfl⟩⟩
      left_inv := by rintro ⟨⟨E, hE⟩, σ, h⟩; change σ.fst = E at h; subst h; rfl
      right_inv := fun σ => rfl } _ _ ?_
  rintro ⟨⟨E, hE⟩, σ, h⟩; change σ.fst = E at h; subst h; rfl

open Classical in
/-- **The transversal part of the left side, over ordered distinct triples.** -/
private theorem sum_lhs_off {Z : Scheme.{0}} {B : Divisor Z} [Fintype (DoubleSurface B)]
    [NoetherianSpace Z] [LinearOrder B.support] (a : DoubleSurface B → ℚ) (m : B.support → ℚ)
    (N : Set Z → ℚ) :
    ∑ σ : DoubleSurface B, (if fstS σ < sndS σ then m (fstS σ) * m (sndS σ) *
        (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * ∑ z, (if z ≠ fstS σ ∧ z ≠ sndS σ then
          m z * ∑ T ∈ tcs σ.fst σ.snd z.1, (if T ⊆ σ.carrier then N T else 0) else 0) else 0) =
      ∑ x, ∑ y, ∑ z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then (if x < y then
        ∑ T ∈ tcs x.1 y.1 z.1, m x * m y * (coeffT a x y T / (m x * m y)) ^ 2 * m z * N T
        else 0) else 0) := by
  rw [sum_doubleSurface_eq_sum_pair]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have h1 : ∀ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y then
      (if fstS σ < sndS σ then m (fstS σ) * m (sndS σ) *
        (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * ∑ z, (if z ≠ fstS σ ∧ z ≠ sndS σ then
          m z * ∑ T ∈ tcs σ.fst σ.snd z.1, (if T ⊆ σ.carrier then N T else 0) else 0) else 0)
      else 0) = if x < y then (if fstS σ = x ∧ sndS σ = y then
        (fun q => m x * m y * (q / (m x * m y)) ^ 2) (a σ) * ∑ z, (if z ≠ x ∧ z ≠ y then
          m z * ∑ T ∈ tcs x.1 y.1 z.1, (if T ⊆ σ.carrier then N T else 0) else 0) else 0)
      else 0 := by
    intro σ
    by_cases h : fstS σ = x ∧ sndS σ = y
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, ite_true]
    · rw [ite_eq_right h]; split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun σ _ => h1 σ]
  by_cases hxy : x < y
  · simp only [ite_eq_left hxy]
    refine (sum_lhs_transversal a x y (fun q => m x * m y * (q / (m x * m y)) ^ 2) m N).trans ?_
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : x ≠ y ∧ x ≠ z ∧ y ≠ z
    · rw [ite_eq_left hz]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [ite_eq_left ⟨hz.2.1.symm, hz.2.2.symm, hz.1⟩]
    · rw [ite_eq_right hz]
      refine Finset.sum_eq_zero fun T _ => ite_eq_right fun h => hz ⟨h.2.2, h.1.symm, h.2.1.symm⟩
  · simp only [ite_eq_right hxy, Finset.sum_const_zero]
    exact (Finset.sum_eq_zero fun z _ => by split_ifs <;> rfl).symm

open Classical in
/-- **The transversal part of the right side, over ordered distinct triples.** -/
private theorem sum_rhs_off {Z : Scheme.{0}} {B : Divisor Z} [Fintype (DoubleSurface B)]
    [NoetherianSpace Z] (a : DoubleSurface B → ℚ) (m : B.support → ℚ) (N : Set Z → ℚ) :
    ∑ σ : DoubleSurface B, (1 / m (fstS σ)) * ∑ τ : DoubleSurface B,
      (if fstS τ = fstS σ ∧ sndS τ ≠ sndS σ then a σ * a τ * ∑ T ∈ tcs σ.fst σ.snd τ.snd,
        (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) =
      ∑ x, ∑ y, ∑ z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then ∑ T ∈ tcs x.1 y.1 z.1,
        1 / m x * coeffT a x y T * coeffT a x z T * N T else 0) := by
  rw [sum_doubleSurface_eq_sum_pair]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have h1 : ∀ σ : DoubleSurface B, (if fstS σ = x ∧ sndS σ = y then
      (1 / m (fstS σ)) * ∑ τ : DoubleSurface B,
      (if fstS τ = fstS σ ∧ sndS τ ≠ sndS σ then a σ * a τ * ∑ T ∈ tcs σ.fst σ.snd τ.snd,
        (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) else 0) =
      (if fstS σ = x ∧ sndS σ = y then (1 / m x) * ∑ τ : DoubleSurface B,
      (if fstS τ = x ∧ sndS τ ≠ y then a σ * a τ * ∑ T ∈ tcs x.1 y.1 τ.snd,
        (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) else 0) := by
    intro σ
    by_cases h : fstS σ = x ∧ sndS σ = y
    · obtain ⟨rfl, rfl⟩ := h; rfl
    · rw [ite_eq_right h, ite_eq_right h]
  rw [Finset.sum_congr rfl fun σ _ => h1 σ, sum_rhs_transversal a x y (1 / m x) N]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : x ≠ y ∧ x ≠ z ∧ y ≠ z
  · rw [ite_eq_left hz]
    exact Finset.sum_congr rfl fun T _ => ite_eq_left hz
  · rw [ite_eq_right hz]
    exact Finset.sum_eq_zero fun T _ => ite_eq_right hz

open Classical in
/-- **The transversal parts, regrouped per triple curve.** Over each sorted triple `i < j < l` and
each triple curve `T`, the left side carries `mᵢ mⱼ mₗ (u² + v² + w²)`, the right side's
off-diagonal terms `2 mᵢ mⱼ mₗ (uv - uw + vw)`, and the difference is the curve term
(`triple_curve_identity`). -/
private theorem sum_off_eq {Z : Scheme.{0}} {B : Divisor Z} [NoetherianSpace Z]
    [LinearOrder B.support] {a : DoubleSurface B → ℚ} (ha : a ∈ orientedSurfaceCoefficients B)
    (m : B.support → ℚ) (hm : ∀ i, 0 < m i) (N : Set Z → ℚ) :
    ∑ x, ∑ y, ∑ z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then (if x < y then
        ∑ T ∈ tcs x.1 y.1 z.1, m x * m y * (coeffT a x y T / (m x * m y)) ^ 2 * m z * N T
        else 0) else 0) =
      ∑ x, ∑ y, ∑ z, (if x ≠ y ∧ x ≠ z ∧ y ≠ z then ∑ T ∈ tcs x.1 y.1 z.1,
        1 / m x * coeffT a x y T * coeffT a x z T * N T else 0) +
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then ∑ T ∈ tcs i.1 j.1 l.1, m i * m j * m l *
        (coeffT a i j T / (m i * m j) - coeffT a i l T / (m i * m l) +
          coeffT a j l T / (m j * m l)) ^ 2 * N T else 0) := by
  rw [sum_distinct_eq_sum_sorted, sum_distinct_eq_sum_sorted, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : i < j ∧ j < l
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
    obtain ⟨hij, hjl⟩ := h
    have hil := hij.trans hjl
    have hi := (hm i).ne'
    have hj := (hm j).ne'
    have hl := (hm l).ne'
    simp only [ite_eq_left hij, ite_eq_left hil, ite_eq_left hjl, ite_eq_right (not_lt_of_gt hij),
      ite_eq_right (not_lt_of_gt hil), ite_eq_right (not_lt_of_gt hjl), add_zero]
    have e1 : tcs i.1 l.1 j.1 = tcs i.1 j.1 l.1 :=
      tcs_congr (by ext; simp only [Set.mem_inter_iff]; tauto)
    have e2 : tcs j.1 i.1 l.1 = tcs i.1 j.1 l.1 :=
      tcs_congr (by ext; simp only [Set.mem_inter_iff]; tauto)
    have e3 : tcs j.1 l.1 i.1 = tcs i.1 j.1 l.1 :=
      tcs_congr (by ext; simp only [Set.mem_inter_iff]; tauto)
    have e4 : tcs l.1 i.1 j.1 = tcs i.1 j.1 l.1 :=
      tcs_congr (by ext; simp only [Set.mem_inter_iff]; tauto)
    have e5 : tcs l.1 j.1 i.1 = tcs i.1 j.1 l.1 :=
      tcs_congr (by ext; simp only [Set.mem_inter_iff]; tauto)
    rw [e1, e2, e3, e4, e5]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hc := (mem_tcs.mp hT).isPreconnected
    rw [coeffT_swap ha i j hc, coeffT_swap ha i l hc, coeffT_swap ha j l hc]
    linear_combination N T * triple_curve_identity (m i) (m j) (m l) (coeffT a i j T)
      (coeffT a i l T) (coeffT a j l T) hi hj hl
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, add_zero]

open Classical in
/-- **The identity for one Cartier divisor `c`, from the five local computations.** With
`NS(S, l) = (ε_l · c · S)`, `X_i(P, Q) = (π_P · π_Q · c|)_{Eᵢ}` and `N(T) = (c · T)`: the diagonal
terms `l ∈ {i, j}` of the left side are the diagonal terms of `∑ᵢ Zᵢ(a)²/mᵢ`, and the transversal
terms regroup per triple curve (`sum_off_eq`). -/
private theorem core_identity {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) [Fintype (DoubleSurface B)]
    [NoetherianSpace Z] [LinearOrder B.support]
    (a : DoubleSurface B → ℚ) (ha : a ∈ orientedSurfaceCoefficients B)
    (m : B.support → ℚ) (hm : ∀ i, 0 < m i)
    (NS : Set Z → B.support → ℚ)
    (X : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      Mori.PrimeDivisor i.1.idealSheaf.subscheme → ℚ) (N : Set Z → ℚ)
    (hL1 : ∀ σ : DoubleSurface B, a σ ≠ 0 →
      NS σ.carrier (sndS σ) = X (fstS σ) (rho hB σ) (rho hB σ))
    (hT1 : ∀ (σ : DoubleSurface B) (l : B.support), a σ ≠ 0 → l ≠ fstS σ → l ≠ sndS σ →
      NS σ.carrier l = ∑ T ∈ tcs σ.fst σ.snd l.1, if T ⊆ σ.carrier then N T else 0)
    (hD0 : ∀ (i : B.support) (σ τ : DoubleSurface B) (h : σ.fst = i.1) (h' : τ.fst = i.1),
      σ.snd = τ.snd → σ ≠ τ → X i (rhoOf hB σ h) (rhoOf hB τ h') = 0)
    (hT2 : ∀ (i : B.support) (σ τ : DoubleSurface B) (h : σ.fst = i.1) (h' : τ.fst = i.1),
      a σ ≠ 0 → σ.snd ≠ τ.snd → X i (rhoOf hB σ h) (rhoOf hB τ h') =
        ∑ T ∈ tcs i.1 σ.snd τ.snd, if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) :
    ∑ σ, (if fstS σ < sndS σ then m (fstS σ) * m (sndS σ) *
        (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * ∑ l, m l * NS σ.carrier l else 0) =
      ∑ i, (1 / m i) * (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * X i P Q) +
      ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then ∑ T ∈ tcs i.1 j.1 l.1, m i * m j * m l *
        (coeffT a i j T / (m i * m j) - coeffT a i l T / (m i * m l) +
          coeffT a j l T / (m j * m l)) ^ 2 * N T else 0) := by
  -- the right side: expand `Zᵢ(a)` twice and reindex by the double surfaces
  have hR1 : ∀ i : B.support, (1 / m i) * (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * X i P Q) =
      ∑ σ : {σ : DoubleSurface B // σ.fst = i.1}, (1 / m i) *
        ∑ τ : {σ : DoubleSurface B // σ.fst = i.1},
          a σ.1 * a τ.1 * X i (rhoOf hB σ.1 σ.2) (rhoOf hB τ.1 τ.2) := by
    intro i
    rw [sum_surfaceCoefficientDivisor hB a i.1 _ (fun P => by simp [Finsupp.sum]),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [sum_surfaceCoefficientDivisor hB a i.1 _ (fun Q => by simp)]
  have hinner : ∀ σ : DoubleSurface B,
      ∑ τ : {τ : DoubleSurface B // τ.fst = (fstS σ).1},
        a σ * a τ.1 * X (fstS σ) (rhoOf hB σ rfl) (rhoOf hB τ.1 τ.2) =
      a σ * a σ * X (fstS σ) (rho hB σ) (rho hB σ) +
        ∑ τ : DoubleSurface B, (if fstS τ = fstS σ ∧ sndS τ ≠ sndS σ then a σ * a τ *
          ∑ T ∈ tcs σ.fst σ.snd τ.snd,
            (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) := by
    intro σ
    have hsplit : ∀ τ : {τ : DoubleSurface B // τ.fst = (fstS σ).1},
        a σ * a τ.1 * X (fstS σ) (rhoOf hB σ rfl) (rhoOf hB τ.1 τ.2) =
        (if τ.1 = σ then a σ * a τ.1 * X (fstS σ) (rhoOf hB σ rfl) (rhoOf hB τ.1 τ.2) else 0) +
        (if τ.1.snd ≠ σ.snd then a σ * a τ.1 * ∑ T ∈ tcs σ.fst σ.snd τ.1.snd,
          (if T ⊆ σ.carrier ∧ T ⊆ τ.1.carrier then N T else 0) else 0) := by
      intro τ
      by_cases h1 : τ.1 = σ
      · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; exact not_not.mpr rfl), add_zero]
      · rw [ite_eq_right h1, zero_add]
        by_cases h2 : τ.1.snd ≠ σ.snd
        · by_cases ha0 : a σ = 0
          · simp [ha0]
          · rw [ite_eq_left h2, hT2 (fstS σ) σ τ.1 rfl τ.2 ha0 (Ne.symm h2)]
        · rw [ite_eq_right h2, hD0 (fstS σ) σ τ.1 rfl τ.2 (not_ne_iff.mp h2).symm (Ne.symm h1),
            mul_zero]
    rw [Finset.sum_congr rfl fun τ _ => hsplit τ, Finset.sum_add_distrib]
    congr 1
    · rw [Fintype.sum_eq_single (⟨σ, rfl⟩ : {τ : DoubleSurface B // τ.fst = (fstS σ).1})
        (fun τ hτ => ite_eq_right fun h => hτ (Subtype.ext h)), ite_eq_left rfl]
      rfl
    · rw [← Finset.sum_subtype (Finset.univ.filter fun τ : DoubleSurface B => τ.fst = σ.fst)
        (by simp) (fun τ => if τ.snd ≠ σ.snd then a σ * a τ * ∑ T ∈ tcs σ.fst σ.snd τ.snd,
          (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0), Finset.sum_filter]
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases h1 : τ.fst = σ.fst
      · by_cases h2 : τ.snd = σ.snd
        · rw [ite_eq_left h1, ite_eq_right (not_not.mpr h2),
            ite_eq_right fun h => h.2 (Subtype.ext h2)]
        · rw [ite_eq_left h1, ite_eq_left h2,
            ite_eq_left ⟨Subtype.ext h1, fun h => h2 (congrArg Subtype.val h)⟩]
      · rw [ite_eq_right h1, ite_eq_right fun h => h1 (congrArg Subtype.val h.1)]
  have hRHS1 : ∑ i, (1 / m i) * (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * X i P Q) =
      ∑ σ : DoubleSurface B, (1 / m (fstS σ)) * (a σ * a σ * X (fstS σ) (rho hB σ) (rho hB σ)) +
      ∑ σ : DoubleSurface B, (1 / m (fstS σ)) * ∑ τ : DoubleSurface B,
        (if fstS τ = fstS σ ∧ sndS τ ≠ sndS σ then a σ * a τ * ∑ T ∈ tcs σ.fst σ.snd τ.snd,
          (if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then N T else 0) else 0) := by
    rw [Finset.sum_congr rfl fun i _ => hR1 i, sum_fst_subtype, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => (congrArg _ (hinner σ)).trans (mul_add _ _ _)
  -- the left side: split the sum over `l` into `l = j`, `l = i` and the rest
  have hLsplit : ∀ σ : DoubleSurface B, a σ ≠ 0 → ∑ l, m l * NS σ.carrier l =
      m (sndS σ) * X (fstS σ) (rho hB σ) (rho hB σ) +
      m (fstS σ) * X (sndS σ) (rho hB σ.swap) (rho hB σ.swap) +
      ∑ z, (if z ≠ fstS σ ∧ z ≠ sndS σ then m z * ∑ T ∈ tcs σ.fst σ.snd z.1,
        (if T ⊆ σ.carrier then N T else 0) else 0) := by
    intro σ ha0
    have ha0' : a σ.swap ≠ 0 := by rw [ha σ]; exact neg_ne_zero.2 ha0
    have hne : sndS σ ≠ fstS σ := fun e => σ.fst_ne_snd (congrArg Subtype.val e).symm
    have h3 : ∀ z, m z * NS σ.carrier z =
        (if z = sndS σ then m (sndS σ) * X (fstS σ) (rho hB σ) (rho hB σ) else 0) +
        (if z = fstS σ then m (fstS σ) * X (sndS σ) (rho hB σ.swap) (rho hB σ.swap) else 0) +
        (if z ≠ fstS σ ∧ z ≠ sndS σ then m z * ∑ T ∈ tcs σ.fst σ.snd z.1,
          (if T ⊆ σ.carrier then N T else 0) else 0) := by
      intro z
      by_cases h1 : z = sndS σ
      · subst h1
        rw [ite_eq_left rfl, ite_eq_right hne, ite_eq_right fun h => h.2 rfl, hL1 σ ha0, add_zero,
          add_zero]
      · by_cases h2 : z = fstS σ
        · subst h2
          rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right fun h => h.1 rfl, zero_add, add_zero]
          exact congrArg _ (hL1 σ.swap ha0')
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left ⟨h2, h1⟩, zero_add, zero_add,
            hT1 σ z ha0 h2 h1]
    rw [Finset.sum_congr rfl fun z _ => h3 z, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _),
      ite_eq_left (Finset.mem_univ _)]
  have hLHS : ∑ σ, (if fstS σ < sndS σ then m (fstS σ) * m (sndS σ) *
        (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * ∑ l, m l * NS σ.carrier l else 0) =
      ∑ σ : DoubleSurface B, (1 / m (fstS σ)) * (a σ * a σ * X (fstS σ) (rho hB σ) (rho hB σ)) +
      ∑ σ : DoubleSurface B, (if fstS σ < sndS σ then m (fstS σ) * m (sndS σ) *
        (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * ∑ z, (if z ≠ fstS σ ∧ z ≠ sndS σ then
          m z * ∑ T ∈ tcs σ.fst σ.snd z.1, (if T ⊆ σ.carrier then N T else 0) else 0)
        else 0) := by
    rw [sum_doubleSurface_eq_sum_lt_add_swap
      (fun σ => (1 / m (fstS σ)) * (a σ * a σ * X (fstS σ) (rho hB σ) (rho hB σ))),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h : fstS σ < sndS σ
    · by_cases ha0 : a σ = 0
      · have hsw0 : a σ.swap = 0 := by rw [ha σ, ha0, neg_zero]
        simp [ite_eq_left h, ha0, hsw0]
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, hLsplit σ ha0]
      have hsw : a σ.swap = -a σ := ha σ
      have hf := (hm (fstS σ)).ne'
      have hs := (hm (sndS σ)).ne'
      have key : ∀ A B' R : ℚ, m (fstS σ) * m (sndS σ) *
          (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * (m (sndS σ) * A + m (fstS σ) * B' + R) =
          1 / m (fstS σ) * (a σ * a σ * A) + 1 / m (sndS σ) * (a σ.swap * a σ.swap * B') +
            m (fstS σ) * m (sndS σ) * (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * R := by
        intro A B' R
        rw [hsw]
        field_simp
      exact key _ _ _
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, add_zero]
  rw [hLHS, hRHS1, sum_lhs_off a m N, sum_rhs_off a m N, sum_off_eq ha m hm N, add_assoc]

/-! ### The transversal terms: a divisor of a surface split over the triple curves -/

/-- A connected component of a subset of `Eᵢ ∩ Eⱼ` through a point of a double surface of
`(Eᵢ, Eⱼ)` lies in that double surface. -/
private theorem connectedComponentIn_subset_carrier {Z : Scheme.{0}} {B : Divisor Z}
    (σ : DoubleSurface B) {F : Set Z} (hF : F ⊆ σ.fst.support ∩ σ.snd.support) {x : Z}
    (hx : x ∈ F) (hxσ : x ∈ σ.carrier) : connectedComponentIn F x ⊆ σ.carrier := by
  rw [σ.carrier_eq_connectedComponentIn hxσ]
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans hF)

private theorem IsTripleCurve.isClosed {Z : Scheme.{0}} {E₁ E₂ E₃ : Mori.PrimeDivisor Z}
    {T : Set Z} (h : IsTripleCurve E₁ E₂ E₃ T) : IsClosed T := by
  obtain ⟨-, -, x, hx, rfl⟩ := h
  rw [connectedComponentIn_eq_image hx]
  exact ((E₁.idealSheaf.support.isClosed.inter E₂.idealSheaf.support.isClosed).inter
    E₃.idealSheaf.support.isClosed).isClosedEmbedding_subtypeVal.isClosedMap _
    isClosed_connectedComponent

private theorem IsTripleCurve.disjoint {Z : Scheme.{0}} {E₁ E₂ E₃ : Mori.PrimeDivisor Z}
    {T T' : Set Z} (h : IsTripleCurve E₁ E₂ E₃ T) (h' : IsTripleCurve E₁ E₂ E₃ T')
    (hne : T ≠ T') : Disjoint T T' := by
  obtain ⟨-, -, x, -, rfl⟩ := h
  obtain ⟨-, -, y, -, rfl⟩ := h'
  rw [Set.disjoint_iff]
  rintro z ⟨hz, hz'⟩
  exact hne ((connectedComponentIn_eq hz).trans (connectedComponentIn_eq hz').symm)

open Classical in
/-- `S ∩ E` is the union of the triple curves of `Eᵢ ∩ Eⱼ ∩ E` lying in the double surface `S`
of `(Eᵢ, Eⱼ)`. -/
private theorem carrier_inter_support_eq_biUnion {Z : Scheme.{0}} [NoetherianSpace Z]
    {B : Divisor Z} (σ : DoubleSurface B) (E : Mori.PrimeDivisor Z) :
    σ.carrier ∩ E.support = ⋃ T ∈ (tcs σ.fst σ.snd E).filter (· ⊆ σ.carrier), T := by
  classical
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_filter, mem_tcs, exists_prop]
  constructor
  · rintro ⟨hxσ, hxE⟩
    have hx : x ∈ σ.fst.support ∩ σ.snd.support ∩ E.support := ⟨σ.carrier_subset hxσ, hxE⟩
    exact ⟨_, ⟨⟨⟨x, mem_connectedComponentIn hx⟩, connectedComponentIn_subset _ _, x, hx, rfl⟩,
      connectedComponentIn_subset_carrier σ Set.inter_subset_left hx hxσ⟩,
      mem_connectedComponentIn hx⟩
  · rintro ⟨T, ⟨hT, hTσ⟩, hxT⟩
    exact ⟨hTσ hxT, (hT.2.1 hxT).2⟩

open Classical in
/-- `S_σ ∩ S_τ` is the union of the triple curves of `Eᵢ ∩ Eⱼ ∩ E_l` lying in both, for double
surfaces `σ` of `(Eᵢ, Eⱼ)` and `τ` of `(Eᵢ, E_l)`. -/
private theorem carrier_inter_carrier_eq_biUnion {Z : Scheme.{0}} [NoetherianSpace Z]
    {B : Divisor Z} {E : Mori.PrimeDivisor Z} (σ τ : DoubleSurface B) (h : σ.fst = E)
    (h' : τ.fst = E) :
    σ.carrier ∩ τ.carrier =
      ⋃ T ∈ (tcs E σ.snd τ.snd).filter (fun T => T ⊆ σ.carrier ∧ T ⊆ τ.carrier), T := by
  classical
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_filter, mem_tcs, exists_prop]
  constructor
  · rintro ⟨hxσ, hxτ⟩
    have hxE : x ∈ E.support := h ▸ (σ.carrier_subset hxσ).1
    have hx : x ∈ E.support ∩ σ.snd.support ∩ τ.snd.support :=
      ⟨⟨hxE, (σ.carrier_subset hxσ).2⟩, (τ.carrier_subset hxτ).2⟩
    refine ⟨_, ⟨⟨⟨x, mem_connectedComponentIn hx⟩, connectedComponentIn_subset _ _, x, hx, rfl⟩,
      connectedComponentIn_subset_carrier σ ?_ hx hxσ,
      connectedComponentIn_subset_carrier τ ?_ hx hxτ⟩, mem_connectedComponentIn hx⟩
    · rintro y ⟨⟨h1, h2⟩, -⟩
      exact ⟨h ▸ h1, h2⟩
    · rintro y ⟨⟨h1, -⟩, h3⟩
      exact ⟨h' ▸ h1, h3⟩
  · rintro ⟨T, ⟨-, hTσ, hTτ⟩, hxT⟩
    exact ⟨hTσ hxT, hTτ hxT⟩

/-- The dimension bound on a subset of a triple intersection, for three distinct components in
any order. -/
private theorem dim_le_one_of_ne {Z : Scheme.{0}} {B : Divisor Z} [LinearOrder B.support]
    (hT : ∀ i j l : B.support, i < j → j < l →
      ∀ T ⊆ i.1.support ∩ j.1.support ∩ l.1.support, topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ))
    {x y z : B.support} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {T : Set Z}
    (hTs : T ⊆ x.1.support ∩ y.1.support ∩ z.1.support) :
    topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ) := by
  have hm : ∀ t ∈ T, t ∈ x.1.support ∧ t ∈ y.1.support ∧ t ∈ z.1.support :=
    fun t ht => ⟨(hTs ht).1.1, (hTs ht).1.2, (hTs ht).2⟩
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact hT x y z h1 h3 T hTs
  · exact hT x z y h2 h3 T fun t ht => ⟨⟨(hm t ht).1, (hm t ht).2.2⟩, (hm t ht).2.1⟩
  · exact absurd (h1.trans h3) (lt_asymm h2)
  · exact hT z x y h2 h1 T fun t ht => ⟨⟨(hm t ht).2.2, (hm t ht).1⟩, (hm t ht).2.1⟩
  · exact hT y x z h1 h2 T fun t ht => ⟨⟨(hm t ht).2.1, (hm t ht).1⟩, (hm t ht).2.2⟩
  · exact absurd (h3.trans h1) (lt_asymm h2)
  · exact hT y z x h3 h2 T fun t ht => ⟨⟨(hm t ht).2.1, (hm t ht).2.2⟩, (hm t ht).1⟩
  · exact hT z y x h3 h1 T fun t ht => ⟨⟨(hm t ht).2.2, (hm t ht).2.1⟩, (hm t ht).1⟩

/-- At a point of `ρ(σ)`, the ideal of `ρ(σ)` is that of `Eⱼ ∩ Eᵢ` on `Eᵢ`. -/
private theorem stalk_rho {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) {x : σ.fst.idealSheaf.subscheme} (hx : x ∈ (rho hB σ).support) :
    IdealSheafData.stalk (rho hB σ).idealSheaf x =
      IdealSheafData.stalk (σ.snd.idealSheaf.comap σ.fst.idealSheaf.subschemeι) x := by
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  have := (isEffectiveCartierDivisor_comap_component hB hab).2
  have := (rho hB σ).integral
  obtain ⟨T', hST, hdisj⟩ := exists_closeds_sup_rho hB σ
  have hPV : (rho hB σ).idealSheaf =
      Scheme.IdealSheafData.vanishingIdeal (rho hB σ).idealSheaf.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ rfl
  rw [hPV]
  refine MMP.Mori.stalk_vanishingIdeal_eq_stalk_of_sup_eq _ _ T' hST fun hT => ?_
  have : x ∈ (((rho hB σ).idealSheaf.support ⊓ T' : Closeds _) : Set _) := ⟨hx, hT⟩
  rw [hdisj.eq_bot] at this
  exact this

private theorem stalk_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E)
    {x : E.idealSheaf.subscheme} (hx : x ∈ (rhoOf hB σ h).support) :
    IdealSheafData.stalk (rhoOf hB σ h).idealSheaf x =
      IdealSheafData.stalk (σ.snd.idealSheaf.comap E.idealSheaf.subschemeι) x := by
  subst h; exact stalk_rho hB σ hx

private theorem mem_support_comap_snd_of_mem_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E)
    {x : E.idealSheaf.subscheme} (hx : x ∈ (rhoOf hB σ h).support) :
    x ∈ (σ.snd.idealSheaf.comap E.idealSheaf.subschemeι).support := by
  have hxσ : E.idealSheaf.subschemeι x ∈ σ.carrier := by
    rw [← image_support_rhoOf hB σ h]; exact ⟨x, hx, rfl⟩
  change x ∈ ((σ.snd.idealSheaf.comap E.idealSheaf.subschemeι).support : Set _)
  rw [Scheme.IdealSheafData.support_comap]
  exact (σ.carrier_subset hxσ).2

/-- **`ρ(σ)` has snc with a divisor of `E_b` meeting it along another component.** If `G` is,
at each of its points, the trace on `E_b` of a component `E_g`, `g ≠ b`, then the
prime divisor `ρ(σ)` of `E_b` has simple normal crossings with `G`. -/
private theorem hasSNCWith_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (b : B.support)
    (σ : DoubleSurface B) (h : σ.fst = b.1) (G : b.1.idealSheaf.subscheme.IdealSheafData)
    (g : B.support) (hgb : g ≠ b)
    (hG : ∀ x ∈ G.support, x ∈ (g.1.idealSheaf.comap b.1.idealSheaf.subschemeι).support ∧
      IdealSheafData.stalk G x =
        IdealSheafData.stalk (g.1.idealSheaf.comap b.1.idealSheaf.subschemeι) x) :
    MMP.Resolution.HasSNCWith (fun _ : Unit => G) (rhoOf hB σ h).idealSheaf := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  intro x hx
  obtain ⟨m, w, c', hw, hc, -⟩ :=
    MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
      (hasSNCWith_component hB b) (not_component_subset b) x
  have hsb : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ b :=
    fun e => σ.fst_ne_snd (h.trans (congrArg Subtype.val e).symm)
  have hx' : x ∈ (rhoOf hB σ h).support := hx
  have hxs : x ∈ (σ.snd.idealSheaf.comap b.1.idealSheaf.subschemeι).support :=
    mem_support_comap_snd_of_mem_rhoOf hB σ h hx'
  have hst : IdealSheafData.stalk (rhoOf hB σ h).idealSheaf x =
      IdealSheafData.stalk (σ.snd.idealSheaf.comap b.1.idealSheaf.subschemeι) x :=
    stalk_rhoOf hB σ h hx'
  have hG' : ∀ u : {u : Unit // x ∈ G.support}, x ∈
      (g.1.idealSheaf.comap b.1.idealSheaf.subschemeι).support := fun u => (hG x u.2).1
  refine ⟨m, w, fun u => c' ⟨⟨g, hgb⟩, hG' u⟩, {c' ⟨⟨⟨σ.snd, σ.snd_mem⟩, hsb⟩, hxs⟩}, hw,
    ?_, ?_, ?_⟩
  · intro u
    exact (hG x u.2).2.trans (hc ⟨⟨g, hgb⟩, hG' u⟩)
  · intro u v _
    exact Subtype.ext rfl
  · rw [Finset.coe_singleton, Set.image_singleton, hst]
    exact hc ⟨⟨⟨σ.snd, σ.snd_mem⟩, hsb⟩, hxs⟩

/-- A divisor not containing the prime divisor `P` contains none of the irreducible components of
the support of `P`. -/
private theorem not_component_subset_of_not_support_subset {Y : Scheme.{0}}
    (P : Mori.PrimeDivisor Y) (G : Y.IdealSheafData)
    (h : ¬ (P.support : Set Y) ⊆ (G.support : Set Y)) :
    ∀ W ∈ MMP.Resolution.componentsOf (P.idealSheaf.support : Set Y),
      ¬ W ⊆ (G.support : Set Y) := by
  intro W hW hWG
  have hirr : IsIrreducible (P.idealSheaf.support : Set Y) := by
    change IsIrreducible (P.support : Set Y)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  exact h ((hW.2 ⟨hirr, le_rfl⟩ hW.1.2).trans hWG)

/-- **No third component contains a double surface.** At the generic point of `ρ(σ)`, of
coheight one on `Eᵢ`, two distinct members of a regular system of parameters would cut out
`Eⱼ` and `E_l`. -/
private theorem not_carrier_subset_support {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (σ : DoubleSurface B) (l : B.support) (hl₁ : l ≠ fstS σ) (hl₂ : l ≠ sndS σ) :
    ¬ σ.carrier ⊆ l.1.support := by
  intro hsub
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set b : B.support := ⟨σ.fst, σ.fst_mem⟩
  set ι := σ.fst.idealSheaf.subschemeι
  set η := (rho hB σ).genericPoint
  have hηS : ι η ∈ σ.carrier := by
    rw [← image_support_rho hB σ]
    refine ⟨η, ?_, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨m, w, c', hw, -, hinj⟩ :=
    MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith
      (hasSNCWith_component hB b) (not_component_subset b) η
  have hne1 : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ b :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  have hm1 : η ∈ ((σ.snd.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact (σ.carrier_subset hηS).2
  have hm2 : η ∈ ((l.1.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]; exact hsub hηS
  have hc : c' ⟨⟨_, hne1⟩, hm1⟩ ≠ c' ⟨⟨l, hl₁⟩, hm2⟩ := fun h =>
    hl₂ (congrArg (fun e => e.1.1) (hinj h)).symm
  have hdim := hw.2
  rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hdim
  have hm : m = 1 := by exact_mod_cast hdim.symm
  subst hm
  exact hc (Subsingleton.elim _ _)

end Core

/-! ### Reduced surfaces and transport to the prime divisors -/

section Defs

variable {k : Type} [Field k] {Z : Scheme.{0}}

/-- The reduced closed subscheme on the closure of `S`. -/
public noncomputable abbrev surfI (S : Set Z) : Z.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure S)

/-- Equal intersection numbers for equal structure morphisms. -/
private theorem sheafIntersectionNumber_congr_base {X Y : Scheme.{0}} {f f' : X ⟶ Spec (.of k)} (h : f = f')
    [IsProper f] [IsProper f'] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Y ≤ d) (L : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f' i d hd L := by
  subst h; rfl

private theorem ker_comp_eq_surfI {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (S : Set Z) (hS : E.idealSheaf.subschemeι '' P.support = S) :
    (surfI S).subschemeι.ker = (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι).ker := by
  have := P.integral
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  rw [← hS, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    P.idealSheaf.range_subschemeι]

/-- The isomorphism from the prime divisor `P` of `E` onto the reduced subscheme on its image. -/
private noncomputable def phi {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (S : Set Z) (hS : E.idealSheaf.subschemeι '' P.support = S) :
    P.idealSheaf.subscheme ⟶ (surfI S).subscheme :=
  IsClosedImmersion.lift (surfI S).subschemeι
    (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι) (ker_comp_eq_surfI P S hS).le

private theorem phi_fac {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (S : Set Z) (hS : E.idealSheaf.subschemeι '' P.support = S) :
    phi P S hS ≫ (surfI S).subschemeι = P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

private theorem isIso_phi {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (S : Set Z) (hS : E.idealSheaf.subschemeι '' P.support = S) : IsIso (phi P S hS) :=
  IsClosedImmersion.isIso_lift (surfI S).subschemeι _ (ker_comp_eq_surfI P S hS)

attribute [local instance] isIso_phi

private noncomputable def pullbackTensorIso' {P P' : Scheme.{0}} (q : P' ⟶ P) (K M : P.Modules) :
    (Scheme.Modules.pullback q).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf) (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj K).obj M) ≅
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨P'.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P'.presheaf) (forget₂ CommRingCat RingCat) (P'.ringCatSheaf.2)⟩).obj ((Scheme.Modules.pullback q).obj K)).obj ((Scheme.Modules.pullback q).obj M)) :=
  (Stacks.RingedSpace.comparisonBifunctorIso q.toLRSHom.toShHom).app (K, M)

private theorem isInvertible_vecCons2 {X : Scheme.{0}} (A B : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] (t : Fin 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, B] t) := by
  fin_cases t <;> assumption

attribute [local instance] isInvertible_vecCons2

private theorem sheafIntersectionNumber_congr_family {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsProper f] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    {L L' : Fin d → X.Modules} (h : L = L')
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L' j)] :
    sheafIntersectionNumber k f i d hd L = sheafIntersectionNumber k f i d hd L' := by
  subst h; rfl

/-- Additivity in the first of two slots. -/
private theorem sheafIntersectionNumber_two_tensor {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Y ⟶ X) [IsClosedImmersion i] (hd : topologicalKrullDim Y ≤ (2 : ℕ))
    (A M N H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H]
    (e : A ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.2)⟩).obj M).obj N)) :
    sheafIntersectionNumber k f i 2 hd ![A, H] =
      sheafIntersectionNumber k f i 2 hd ![M, H] + sheafIntersectionNumber k f i 2 hd ![N, H] := by
  have hM : Function.update ![A, H] 0 M = ![M, H] := by
    funext t; fin_cases t <;> rfl
  have hN : Function.update ![A, H] 0 N = ![N, H] := by
    funext t; fin_cases t <;> rfl
  have := isInvertible_update ![A, H] 0 M
  have := isInvertible_update ![A, H] 0 N
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_update_tensor k f i 2 hd 0 ![A, H] M N e,
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    sheafIntersectionNumber_congr_family f i 2 hd hM,
    sheafIntersectionNumber_congr_family f i 2 hd hN,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]

/-- Isomorphic first slots give equal numbers. -/
private theorem sheafIntersectionNumber_two_congr_iso {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k))
    [IsProper f] (i : Y ⟶ X) [IsClosedImmersion i] (hd : topologicalKrullDim Y ≤ (2 : ℕ))
    (A A' H : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A']
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 H] (e : A ≅ A') :
    sheafIntersectionNumber k f i 2 hd ![A, H] = sheafIntersectionNumber k f i 2 hd ![A', H] := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  refine intersectionNumber_eq_of_iso_at k f i 2 hd _ _ 0 ?_ e
  intro q hq
  fin_cases q
  · exact absurd rfl hq
  · rfl

/-- **Transport to the prime divisor.** -/
private theorem sheafIntersectionNumber_surfI_eq {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (S : Set Z)
    (hS : E.idealSheaf.subschemeι '' P.support = S) {d : ℕ}
    (hd : topologicalKrullDim (surfI S).subscheme ≤ d)
    (hd' : topologicalKrullDim P.idealSheaf.subscheme ≤ d)
    (L : Fin d → (surfI S).subscheme.Modules)
    [∀ t, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (L t)] :
    sheafIntersectionNumber k ((surfI S).subschemeι ≫ sZ) (𝟙 _) d hd L =
      sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) (𝟙 _) d
        hd' (fun t => (Scheme.Modules.pullback (phi P S hS)).obj (L t)) := by
  rw [sheafIntersectionNumber_eq_of_iso k ((surfI S).subschemeι ≫ sZ) (𝟙 _) (phi P S hS)
      (asIso (phi P S hS)).symm (by simp) d hd hd' L,
    sheafIntersectionNumber_congr_hom k _ (Category.id_comp (phi P S hS)).symm d hd' L,
    sheafIntersectionNumber_comp_eq_of_iso k _ (phi P S hS) (𝟙 _) d hd' L _
      (fun t => Iso.refl _)]
  exact sheafIntersectionNumber_congr_base (by rw [← Category.assoc, phi_fac, Category.assoc])
    _ _ _ _

private theorem range_comp_phi {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (S : Set Z)
    (hS : E.idealSheaf.subschemeι '' P.support = S) (T : Set Z) :
    phi P S hS '' (P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' T)) =
      (surfI S).subschemeι ⁻¹' T := by
  ext x
  obtain ⟨y, rfl⟩ := (Scheme.homeoOfIso (asIso (phi P S hS))).surjective x
  have hinj := (Scheme.homeoOfIso (asIso (phi P S hS))).injective
  change _ ↔ ((phi P S hS) ≫ (surfI S).subschemeι) y ∈ T
  rw [phi_fac]
  constructor
  · rintro ⟨y', hy', hyy⟩
    obtain rfl := hinj hyy
    exact hy'
  · exact fun hy => ⟨y, hy, rfl⟩

/-- **Transport of curve numbers to the prime divisor.** -/
private theorem curveNum_surfI_eq {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (S : Set Z)
    (hS : E.idealSheaf.subschemeι '' P.support = S) (T : Set Z) (hT : IsClosed T)
    (hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      ⟨(surfI S).subschemeι ⁻¹' T, hT.preimage (surfI S).subschemeι.continuous⟩).subscheme ≤
        (1 : ℕ))
    (hd' : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      ⟨P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' T),
        (hT.preimage E.idealSheaf.subschemeι.continuous).preimage
          P.idealSheaf.subschemeι.continuous⟩).subscheme ≤ (1 : ℕ))
    (M : (surfI S).subscheme.Modules)
    [SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 M] :
    sheafIntersectionNumber k ((surfI S).subschemeι ≫ sZ)
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨(surfI S).subschemeι ⁻¹' T, hT.preimage (surfI S).subschemeι.continuous⟩).subschemeι
        1 hd (fun _ => M) =
      sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ)
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' T),
            (hT.preimage E.idealSheaf.subschemeι.continuous).preimage
              P.idealSheaf.subschemeι.continuous⟩).subschemeι
        1 hd' (fun _ => (Scheme.Modules.pullback (phi P S hS)).obj M) := by
  rw [← sheafIntersectionNumber_congr_base
      (f := phi P S hS ≫ (surfI S).subschemeι ≫ sZ)
      (by rw [← Category.assoc, phi_fac, Category.assoc]),
    ← sheafIntersectionNumber_comp_eq_of_iso k ((surfI S).subschemeι ≫ sZ) (phi P S hS) _ 1 hd'
      (fun _ => M) _ (fun _ => Iso.refl _)]
  refine sheafIntersectionNumber_eq_of_ker_eq k _ _ _ ?_ 1 hd hd' _
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_closure, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change (surfI S).subschemeι ⁻¹' T = closure (phi P S hS ''
    (P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' T)))
  rw [range_comp_phi, (hT.preimage (surfI S).subschemeι.continuous).closure_eq]

end Defs

attribute [local instance] isIso_phi

/-! ### Cutting a prime divisor by an effective Cartier divisor -/

section Local

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z : Scheme.{0}}

/-- The closed subset of `P` over a subset `T` of `Z`, through its closure. -/
private noncomputable def curveCloseds {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (T : Set Z) : Closeds P.idealSheaf.subscheme :=
  ⟨P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' closure T),
    (isClosed_closure.preimage E.idealSheaf.subschemeι.continuous).preimage
      P.idealSheaf.subschemeι.continuous⟩

/-- The degree `(H · T)` of an invertible sheaf on `P` along `T`, read on `P`; zero when the
subscheme has dimension above one. -/
private noncomputable def curveNumP (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (H : P.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible P.idealSheaf.subscheme.presheaf
      P.idealSheaf.subscheme.ringCatSheaf.2 H] (T : Set Z) : ℚ := by
  classical
  exact if h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveCloseds P T)).subscheme ≤ (1 : ℕ) then
    (sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ)
      (Scheme.IdealSheafData.vanishingIdeal (curveCloseds P T)).subschemeι 1 h (fun _ => H) : ℚ)
  else 0

/-- **Cutting the prime divisor `P` by an effective Cartier divisor of `E` into curves.** -/
private theorem num_P_eq_sum_curveNumP (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ))
    (A : E.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible E.idealSheaf.subscheme.presheaf
      E.idealSheaf.subscheme.ringCatSheaf.2 A]
    (G : E.idealSheaf.subscheme.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor G]
    (e0 : A ≅ Stacks.Divisors.invertibleSheaf' G) (H : P.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible P.idealSheaf.subscheme.presheaf
      P.idealSheaf.subscheme.ringCatSheaf.2 H]
    (hG : ∀ y ∈ (G.comap P.idealSheaf.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → P.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (G.comap P.idealSheaf.subschemeι) y = Ideal.span {w j})
    (s : Finset (Set Z))
    (hsupp : ((G.comap P.idealSheaf.subschemeι).support : Set _) =
      P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' ⋃ a ∈ s, a))
    (hdisj : (s : Set (Set Z)).PairwiseDisjoint id) (hcl : ∀ a ∈ s, IsClosed a)
    (hdim : ∀ a ∈ s, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveCloseds P a)).subscheme ≤ (1 : ℕ)) :
    (sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2
        hP2 ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj A, H] : ℚ) =
      ∑ a ∈ s, curveNumP sZ P H a := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian E.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion E.idealSheaf.subschemeι
  have : IsLocallyNoetherian P.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion P.idealSheaf.subschemeι
  have : Stacks.Divisors.IsPullbackDefined P.idealSheaf.subschemeι G :=
    MMP.Resolution.isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ hG
  let T : {a // a ∈ s} → Closeds P.idealSheaf.subscheme := fun a => curveCloseds P a.1
  have hT' : ((G.comap P.idealSheaf.subschemeι).support : Set P.idealSheaf.subscheme) =
      ⋃ a ∈ (Finset.univ : Finset {a // a ∈ s}), (T a : Set P.idealSheaf.subscheme) := by
    rw [hsupp]
    ext y
    simp only [T, curveCloseds, Set.mem_preimage, Set.mem_iUnion, Finset.mem_univ, true_and,
      Closeds.coe_mk, exists_prop, Subtype.exists]
    refine exists_congr fun a => and_congr_right fun ha => ?_
    rw [(hcl a ha).closure_eq]
  have hdisj' : ((Finset.univ : Finset {a // a ∈ s}) : Set {a // a ∈ s}).PairwiseDisjoint
      fun a => (T a : Set P.idealSheaf.subscheme) := by
    intro a _ b _ hab
    change Disjoint (P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' closure a.1))
      (P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' closure b.1))
    rw [(hcl a.1 a.2).closure_eq, (hcl b.1 b.2).closure_eq]
    exact ((hdisj a.2 b.2 fun h => hab (Subtype.ext h)).preimage _).preimage _
  have h2 := MMP.Mori.sheafIntersectionNumber_eq_sum_of_support_eq_iUnion k
    (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) 1 hP2
    ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj A, H] (G.comap P.idealSheaf.subschemeι)
    hG ((Scheme.Modules.pullback P.idealSheaf.subschemeι).mapIso e0 ≪≫
      Stacks.Divisors.invertibleSheafPullbackIso P.idealSheaf.subschemeι G)
    Finset.univ T hT' hdisj' (fun a => hdim a.1 a.2)
  rw [h2]
  push_cast
  rw [← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [curveNumP, dif_pos (hdim a.1 a.2)]
  exact_mod_cast sheafIntersectionNumber_congr_family _ _ 1 _ (funext fun t => by fin_cases t; rfl)

private theorem ker_curveCloseds_eq {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (a : Set Z)
    (ha : a ⊆ E.idealSheaf.subschemeι '' P.support) :
    ((Scheme.IdealSheafData.vanishingIdeal (curveCloseds P a)).subschemeι ≫
        P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι).ker =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure a)).subschemeι.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure a)),
    Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_closure, Closeds.coe_closure, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
    Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hcl : IsClosed (E.idealSheaf.subschemeι '' P.support) :=
    E.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _ P.idealSheaf.support.isClosed
  have hsub : closure a ⊆ E.idealSheaf.subschemeι '' P.support := closure_minimal ha hcl
  change closure (E.idealSheaf.subschemeι '' (P.idealSheaf.subschemeι ''
    (P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' closure a)))) = closure a
  rw [Set.image_preimage_eq_inter_range, P.idealSheaf.range_subschemeι]
  refine (congrArg closure ?_).trans closure_closure
  ext z
  constructor
  · rintro ⟨y, ⟨hy, -⟩, rfl⟩
    exact hy
  · intro hz
    obtain ⟨y, hy, rfl⟩ := hsub hz
    exact ⟨y, ⟨hz, hy⟩, rfl⟩

private theorem dim_curveCloseds_le {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (a : Set Z)
    (ha : a ⊆ E.idealSheaf.subschemeι '' P.support)
    (h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure a)).subscheme ≤ (1 : ℕ)) :
    topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveCloseds P a)).subscheme ≤ (1 : ℕ) := by
  have hker := ker_curveCloseds_eq P a ha
  have := IsClosedImmersion.isIso_lift _ _ hker.symm
  rw [IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift _ _ hker.symm.le))).isHomeomorph]
  exact h

/-- **(L1) on `ρ(σ)`**: `(εⱼ|_{ρσ} · H) = (π_{ρσ}|_{ρσ} · H)`. -/
private theorem num_P_eps_snd (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (hvar : Mori.IsVariety k sZ)
    (hsm : IsSmoothScheme sZ) {B : Divisor Z} (hB : B.IsSNC sZ) (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (σ : DoubleSurface B)
    (hP2 : topologicalKrullDim (rho hB σ).idealSheaf.subscheme ≤ (2 : ℕ))
    (H : (rho hB σ).idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible (rho hB σ).idealSheaf.subscheme.presheaf
      (rho hB σ).idealSheaf.subscheme.ringCatSheaf.2 H] :
    sheafIntersectionNumber k
        ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2
        ![(Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).obj
          ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf (ε (sndS σ)))), H] =
      sheafIntersectionNumber k
        ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2
        ![(Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (π (fstS σ) (rho hB σ))), H] := by
  have := (rho hB σ).integral
  obtain ⟨R, hcomap, hPe, hRe, hRtop⟩ := exists_comap_eq_rho_mul hB σ
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  obtain ⟨eε⟩ := nonempty_pullback_eps_iso k sZ hvar hsm hB ε hε hab
  obtain ⟨hπe, hπsub⟩ := exists_isEffective_pi k sZ hB π hπ ⟨σ.fst, σ.fst_mem⟩ (rho hB σ)
  have eπ : MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ (rho hB σ)) ≅
      Stacks.Divisors.invertibleSheaf' (rho hB σ).idealSheaf :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf _ hπe ≪≫
      eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hπsub)
  have e : (Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf (ε ⟨σ.snd, σ.snd_mem⟩)) ≅
      Stacks.Divisors.sumSheaf (rho hB σ).idealSheaf R :=
    eε ≪≫ eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hcomap) ≪≫
      (Stacks.Divisors.invertibleSheafSumIso _ _).symm
  rw [sheafIntersectionNumber_two_tensor _ _ hP2 _
      ((Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' (rho hB σ).idealSheaf))
      ((Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' R)) H
      ((Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).mapIso e ≪≫
        pullbackTensorIso' (rho hB σ).idealSheaf.subschemeι _ _),
    sheafIntersectionNumber_eq_zero_of_iso_unit k _ (𝟙 _) 2 hP2
      ![(Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' R), H] 0
      (nonempty_pullback_invertibleSheaf_iso_unit (rho hB σ).idealSheaf.subschemeι R hRtop).some,
    add_zero]
  exact sheafIntersectionNumber_two_congr_iso _ _ hP2 _ _ H
    ((Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).mapIso eπ.symm)

/-- **(D0) on `P`**: a prime divisor of `E` disjoint from `P` restricts trivially. -/
private theorem num_P_pi_eq_zero_of_disjoint (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {B : Divisor Z}
    (hB : B.IsSNC sZ)
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (i : B.support) (P Q : Mori.PrimeDivisor i.1.idealSheaf.subscheme)
    (hPQ : Disjoint P.support Q.support)
    (hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ))
    (H : P.idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible P.idealSheaf.subscheme.presheaf
      P.idealSheaf.subscheme.ringCatSheaf.2 H] :
    sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2
        hP2 ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (π i Q)), H] = 0 := by
  obtain ⟨hQe, hQsub⟩ := exists_isEffective_pi k sZ hB π hπ i Q
  refine sheafIntersectionNumber_eq_zero_of_iso_unit k _ (𝟙 _) 2 hP2 _ 0
    (nonempty_pullback_cartierSheaf_iso_unit P.idealSheaf.subschemeι (π i Q) hQe ?_).some
  rw [P.idealSheaf.range_subschemeι, hQsub]
  exact hPQ

end Local

/-! ### The transversal local relations -/

section Local2

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z : Scheme.{0}}

open Classical in
/-- **(T1) on `ρ(σ)`**: `(E_l|_{ρσ} · H) = ∑_{T ⊆ S} (H · T)` for a third component `E_l`. -/
private theorem num_P_eps_transversal (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [NoetherianSpace Z]
    (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ) {B : Divisor Z}
    (hB : B.IsSNC sZ) [LinearOrder B.support] (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (hT : ∀ i j l : B.support, i < j → j < l →
      ∀ T ⊆ i.1.support ∩ j.1.support ∩ l.1.support, topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ))
    (σ : DoubleSurface B) (l : B.support) (hl₁ : l ≠ fstS σ) (hl₂ : l ≠ sndS σ)
    (hP2 : topologicalKrullDim (rho hB σ).idealSheaf.subscheme ≤ (2 : ℕ))
    (H : (rho hB σ).idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible (rho hB σ).idealSheaf.subscheme.presheaf
      (rho hB σ).idealSheaf.subscheme.ringCatSheaf.2 H] :
    (sheafIntersectionNumber k
        ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2
        ![(Scheme.Modules.pullback (rho hB σ).idealSheaf.subschemeι).obj
          ((Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf (ε l))), H] : ℚ) =
      ∑ T ∈ tcs σ.fst σ.snd l.1, if T ⊆ σ.carrier then curveNumP sZ (rho hB σ) H T else 0 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion σ.fst.idealSheaf.subschemeι
  have := (rho hB σ).integral
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι) :=
    (isEffectiveCartierDivisor_comap_component hB hl₁).1
  have hsnc : MMP.Resolution.HasSNCWith
      (fun _ : Unit => l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι)
      (rho hB σ).idealSheaf :=
    hasSNCWith_rhoOf hB (fstS σ) σ rfl _ l hl₁ fun x hx => ⟨hx, rfl⟩
  have hPl : ¬ ((rho hB σ).support : Set _) ⊆
      ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).support : Set _) := by
    intro hsub
    refine not_carrier_subset_support hB σ l hl₁ hl₂ ?_
    rw [← image_support_rho hB σ]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).support : Set _) := hsub hy
    rw [Scheme.IdealSheafData.support_comap] at hy'
    exact hy'
  have hG : ∀ y ∈ ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).comap
      (rho hB σ).idealSheaf.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → (rho hB σ).idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).comap
          (rho hB σ).idealSheaf.subschemeι) y = Ideal.span {w j} := by
    intro y hy
    obtain ⟨m, w, c', hw, hc, -⟩ :=
      MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hsnc
        (fun _ => not_component_subset_of_not_support_subset (rho hB σ) _ hPl) y
    exact ⟨m, w, c' ⟨(), hy⟩, hw, hc ⟨(), hy⟩⟩
  have hιP : ∀ y : (rho hB σ).idealSheaf.subscheme,
      σ.fst.idealSheaf.subschemeι ((rho hB σ).idealSheaf.subschemeι y) ∈ σ.carrier := by
    intro y
    rw [← image_support_rho hB σ]
    refine ⟨(rho hB σ).idealSheaf.subschemeι y, ?_, rfl⟩
    change (rho hB σ).idealSheaf.subschemeι y ∈ ((rho hB σ).idealSheaf.support : Set _)
    rw [← (rho hB σ).idealSheaf.range_subschemeι]
    exact ⟨y, rfl⟩
  rw [num_P_eq_sum_curveNumP sZ (rho hB σ) hP2 _ _
      (nonempty_pullback_eps_iso k sZ hvar hsm hB ε hε hl₁).some H hG
      ((tcs σ.fst σ.snd l.1).filter (· ⊆ σ.carrier)) ?_ ?_ ?_ ?_, Finset.sum_filter]
  · rw [← carrier_inter_support_eq_biUnion σ l.1]
    ext y
    simp only [Scheme.IdealSheafData.support_comap, Set.mem_preimage, Set.mem_inter_iff,
      SetLike.mem_coe]
    exact ⟨fun h => ⟨hιP y, h⟩, fun h => h.2⟩
  · intro a ha a' ha' hne
    exact IsTripleCurve.disjoint (mem_tcs.1 (Finset.mem_filter.1 ha).1)
      (mem_tcs.1 (Finset.mem_filter.1 ha').1) hne
  · exact fun a ha => (mem_tcs.1 (Finset.mem_filter.1 ha).1).isClosed
  · intro a ha
    refine dim_curveCloseds_le (rho hB σ) a ?_ ?_
    · rw [image_support_rho hB σ]
      exact (Finset.mem_filter.1 ha).2
    · exact dim_le_one_of_ne hT (fun e => σ.fst_ne_snd (congrArg Subtype.val e)) hl₁.symm
        hl₂.symm (mem_tcs.1 (Finset.mem_filter.1 ha).1).2.1

open Classical in
/-- **(T2) on `ρ(σ)`**: `(π_{ρτ}|_{ρσ} · H) = ∑_{T ⊆ S_σ ∩ S_τ} (H · T)` when `σ`, `τ` share
their first component but not their second. -/
private theorem num_P_pi_transversal (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [NoetherianSpace Z]
    {B : Divisor Z} (hB : B.IsSNC sZ) [LinearOrder B.support]
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hT : ∀ i j l : B.support, i < j → j < l →
      ∀ T ⊆ i.1.support ∩ j.1.support ∩ l.1.support, topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ))
    (i : B.support) (σ τ : DoubleSurface B) (h : σ.fst = i.1) (h' : τ.fst = i.1)
    (hne : σ.snd ≠ τ.snd)
    (hP2 : topologicalKrullDim (rhoOf hB σ h).idealSheaf.subscheme ≤ (2 : ℕ))
    (H : (rhoOf hB σ h).idealSheaf.subscheme.Modules)
    [SheafOfModules.IsInvertible (rhoOf hB σ h).idealSheaf.subscheme.presheaf
      (rhoOf hB σ h).idealSheaf.subscheme.ringCatSheaf.2 H] :
    (sheafIntersectionNumber k
        ((rhoOf hB σ h).idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2
        ![(Scheme.Modules.pullback (rhoOf hB σ h).idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (π i (rhoOf hB τ h'))), H] : ℚ) =
      ∑ T ∈ tcs i.1 σ.snd τ.snd,
        if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then curveNumP sZ (rhoOf hB σ h) H T else 0 := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian i.1.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion i.1.idealSheaf.subschemeι
  have := (rhoOf hB σ h).integral
  obtain ⟨hQe, hQsub⟩ := exists_isEffective_pi k sZ hB π hπ i (rhoOf hB τ h')
  have : Stacks.Divisors.IsEffectiveCartierDivisor (rhoOf hB τ h').idealSheaf :=
    hQsub ▸ MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hQe
  have hgb : (sndS τ) ≠ i := fun e => τ.fst_ne_snd (h'.trans (congrArg Subtype.val e).symm)
  have hsnc : MMP.Resolution.HasSNCWith (fun _ : Unit => (rhoOf hB τ h').idealSheaf)
      (rhoOf hB σ h).idealSheaf :=
    hasSNCWith_rhoOf hB i σ h (rhoOf hB τ h').idealSheaf (sndS τ) hgb fun x hx =>
      ⟨mem_support_comap_snd_of_mem_rhoOf hB τ h' hx, stalk_rhoOf hB τ h' hx⟩
  have hPQ : rhoOf hB σ h ≠ rhoOf hB τ h' := fun e =>
    hne (congrArg DoubleSurface.snd (rhoOf_injective hB h h' e))
  have hG : ∀ y ∈ ((rhoOf hB τ h').idealSheaf.comap (rhoOf hB σ h).idealSheaf.subschemeι).support,
      ∃ (m : ℕ) (w : Fin m → (rhoOf hB σ h).idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((rhoOf hB τ h').idealSheaf.comap
          (rhoOf hB σ h).idealSheaf.subschemeι) y = Ideal.span {w j} := by
    intro y hy
    obtain ⟨m, w, c', hw, hc, -⟩ :=
      MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hsnc
        (fun _ => not_component_subset_of_not_support_subset (rhoOf hB σ h)
          (rhoOf hB τ h').idealSheaf (not_support_subset_of_ne hPQ)) y
    exact ⟨m, w, c' ⟨(), hy⟩, hw, hc ⟨(), hy⟩⟩
  have hιP : ∀ y : (rhoOf hB σ h).idealSheaf.subscheme,
      i.1.idealSheaf.subschemeι ((rhoOf hB σ h).idealSheaf.subschemeι y) ∈ σ.carrier := by
    intro y
    rw [← image_support_rhoOf hB σ h]
    refine ⟨(rhoOf hB σ h).idealSheaf.subschemeι y, ?_, rfl⟩
    change (rhoOf hB σ h).idealSheaf.subschemeι y ∈ ((rhoOf hB σ h).idealSheaf.support : Set _)
    rw [← (rhoOf hB σ h).idealSheaf.range_subschemeι]
    exact ⟨y, rfl⟩
  have hQS : ((rhoOf hB τ h').support : Set _) = i.1.idealSheaf.subschemeι ⁻¹' τ.carrier := by
    rw [← image_support_rhoOf hB τ h', Set.preimage_image_eq _
      i.1.idealSheaf.subschemeι.isClosedEmbedding.injective]
  rw [num_P_eq_sum_curveNumP sZ (rhoOf hB σ h) hP2 _ (rhoOf hB τ h').idealSheaf
      (MMP.CartierDivisor.sheafIsoInvertibleSheaf (π i (rhoOf hB τ h')) hQe ≪≫
        eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hQsub)) H hG
      ((tcs i.1 σ.snd τ.snd).filter (fun T => T ⊆ σ.carrier ∧ T ⊆ τ.carrier)) ?_ ?_ ?_ ?_,
    Finset.sum_filter]
  · rw [← carrier_inter_carrier_eq_biUnion σ τ h h']
    ext y
    simp only [Scheme.IdealSheafData.support_comap, Set.mem_preimage, Set.mem_inter_iff,
      SetLike.mem_coe]
    change (rhoOf hB σ h).idealSheaf.subschemeι y ∈ ((rhoOf hB τ h').support : Set _) ↔ _
    rw [hQS]
    exact ⟨fun h => ⟨hιP y, h⟩, fun h => h.2⟩
  · intro a ha a' ha' hne
    exact IsTripleCurve.disjoint (mem_tcs.1 (Finset.mem_filter.1 ha).1)
      (mem_tcs.1 (Finset.mem_filter.1 ha').1) hne
  · exact fun a ha => (mem_tcs.1 (Finset.mem_filter.1 ha).1).isClosed
  · intro a ha
    refine dim_curveCloseds_le (rhoOf hB σ h) a ?_ ?_
    · rw [image_support_rhoOf hB σ h]
      exact (Finset.mem_filter.1 ha).2.1
    · exact dim_le_one_of_ne hT (y := sndS σ) (z := sndS τ)
        (fun e => σ.fst_ne_snd (h.trans (congrArg Subtype.val e)))
        (Ne.symm hgb) (fun e => hne (congrArg Subtype.val e))
        (mem_tcs.1 (Finset.mem_filter.1 ha).1).2.1

end Local2

/-! ### The weighted identity for a family of surface classes -/

section Identity

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z : Scheme.{0}}

/-- The closed subset of the reduced surface on `S` over a subset `T` of `Z`. -/
private noncomputable def curveClosedsS (S T : Set Z) : Closeds (surfI S).subscheme :=
  ⟨(surfI S).subschemeι ⁻¹' closure T, isClosed_closure.preimage (surfI S).subschemeι.continuous⟩

section Numbers

variable (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
  (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
    (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))

/-- `(e|_S · 𝓗_S)` on the reduced surface `S`. -/
private noncomputable def nsNum (S : Set Z) (e : Z.CartierDivisor) : ℚ := by
  classical
  haveI := h𝓗 S
  exact if h : topologicalKrullDim (surfI S).subscheme ≤ (2 : ℕ) then
    (sheafIntersectionNumber k ((surfI S).subschemeι ≫ sZ) (𝟙 _) 2 h
      ![(Scheme.Modules.pullback (surfI S).subschemeι).obj
        (MMP.CartierDivisor.sheaf e), 𝓗 S] : ℚ) else 0

/-- `(𝓗_S · T)` on the reduced surface `S`. -/
private noncomputable def cNum (S T : Set Z) : ℚ := by
  classical
  haveI := h𝓗 S
  exact if h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subscheme ≤ (1 : ℕ) then
    (sheafIntersectionNumber k ((surfI S).subschemeι ≫ sZ)
      (Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subschemeι 1 h
      (fun _ => 𝓗 S) : ℚ) else 0

/-- `(π_Q|_P · 𝓗_P)` on a prime divisor `P` of a component. -/
private noncomputable def fxNum {B : Divisor Z}
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (i : B.support) (P Q : Mori.PrimeDivisor i.1.idealSheaf.subscheme) : ℚ := by
  classical
  haveI := h𝓗 (i.1.idealSheaf.subschemeι '' P.support)
  exact if h : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ) then
    (sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) (𝟙 _)
      2 h ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (π i Q)),
        (Scheme.Modules.pullback (phi P _ rfl)).obj (𝓗 (i.1.idealSheaf.subschemeι '' P.support))] :
      ℚ) else 0

end Numbers

private theorem dim_P_eq {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (S : Set Z) (hS : E.idealSheaf.subschemeι '' P.support = S) :
    topologicalKrullDim P.idealSheaf.subscheme = topologicalKrullDim (surfI S).subscheme :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso (phi P S hS))).isHomeomorph

/-- `nsNum` read on a prime divisor `P` with image `S`. -/
private theorem nsNum_eq (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (S : Set Z)
    (hS : E.idealSheaf.subschemeι '' P.support = S)
    (hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ)) (e : Z.CartierDivisor) :
    haveI := h𝓗 S
    nsNum sZ 𝓗 h𝓗 S e =
      (sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2
        hP2 ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
          ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf e)),
          (Scheme.Modules.pullback (phi P S hS)).obj (𝓗 S)] : ℚ) := by
  haveI := h𝓗 S
  have hS2 : topologicalKrullDim (surfI S).subscheme ≤ (2 : ℕ) := dim_P_eq P S hS ▸ hP2
  have e' : (Scheme.Modules.pullback (phi P S hS)).obj ((Scheme.Modules.pullback
      (surfI S).subschemeι).obj (MMP.CartierDivisor.sheaf e)) ≅
      (Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf e)) :=
    (Scheme.Modules.pullbackComp (phi P S hS) (surfI S).subschemeι).app _ ≪≫
      eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj
        (MMP.CartierDivisor.sheaf e)) (phi_fac P S hS)) ≪≫
      ((Scheme.Modules.pullbackComp P.idealSheaf.subschemeι E.idealSheaf.subschemeι).app _).symm
  have h1 := sheafIntersectionNumber_congr_family (k := k)
    (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2
    (L := fun t => (Scheme.Modules.pullback (phi P S hS)).obj
      (![(Scheme.Modules.pullback (surfI S).subschemeι).obj
        (MMP.CartierDivisor.sheaf e), 𝓗 S] t))
    (L' := ![(Scheme.Modules.pullback (phi P S hS)).obj ((Scheme.Modules.pullback
        (surfI S).subschemeι).obj (MMP.CartierDivisor.sheaf e)),
      (Scheme.Modules.pullback (phi P S hS)).obj (𝓗 S)])
    (funext fun t => by fin_cases t <;> rfl)
  have h2 := sheafIntersectionNumber_two_congr_iso (k := k)
    (P.idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) (𝟙 _) hP2 _ _
    ((Scheme.Modules.pullback (phi P S hS)).obj (𝓗 S)) e'
  rw [nsNum, dif_pos hS2, sheafIntersectionNumber_surfI_eq sZ P S hS hS2 hP2, h1, h2]

/-- `fxNum` with the image set replaced by an equal one. -/
private theorem fxNum_eq (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S)) {B : Divisor Z}
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (i : B.support) (P Q : Mori.PrimeDivisor i.1.idealSheaf.subscheme) (S : Set Z)
    (hS : i.1.idealSheaf.subschemeι '' P.support = S)
    (hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ)) :
    haveI := h𝓗 S
    fxNum sZ 𝓗 h𝓗 π i P Q =
      (sheafIntersectionNumber k (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ)
        (𝟙 _) 2 hP2 ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf (π i Q)),
          (Scheme.Modules.pullback (phi P S hS)).obj (𝓗 S)] : ℚ) := by
  subst hS
  rw [fxNum, dif_pos hP2]

private theorem ker_curveClosedsS_eq (S T : Set Z) (hT : closure T ⊆ closure S) :
    ((Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subschemeι ≫
        (surfI S).subschemeι).ker =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)),
    Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  congr 1
  apply Closeds.ext
  rw [Closeds.coe_closure, Closeds.coe_closure, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change closure ((surfI S).subschemeι '' ((surfI S).subschemeι ⁻¹' closure T)) = closure T
  rw [Set.image_preimage_eq_inter_range, (surfI S).range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    Set.inter_eq_left.2 hT, closure_closure]

/-- `cNum` read on a prime divisor `P` with image `S`. -/
private theorem cNum_eq (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    {E : Mori.PrimeDivisor Z} (P : Mori.PrimeDivisor E.idealSheaf.subscheme) (S : Set Z)
    (hS : E.idealSheaf.subschemeι '' P.support = S) (T : Set Z) (hTS : T ⊆ S)
    (hT1 : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ)) :
    haveI := h𝓗 S
    cNum sZ 𝓗 h𝓗 S T = curveNumP sZ P ((Scheme.Modules.pullback (phi P S hS)).obj (𝓗 S)) T := by
  haveI := h𝓗 S
  have hScl : IsClosed S := hS ▸
    E.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _ P.idealSheaf.support.isClosed
  have hTS' : closure T ⊆ closure S := closure_mono hTS
  have hd : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subscheme ≤ (1 : ℕ) := by
    have hker := ker_curveClosedsS_eq S T hTS'
    have := IsClosedImmersion.isIso_lift _ _ hker.symm
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift _ _ hker.symm.le))).isHomeomorph]
    exact hT1
  have hd' := dim_curveCloseds_le P T (hS ▸ hTS) hT1
  rw [cNum, dif_pos hd, curveNumP, dif_pos hd']
  exact_mod_cast curveNum_surfI_eq sZ P S hS (closure T) isClosed_closure hd hd' (𝓗 S)

open Classical in
/-- **The weighted identity for a family of surface classes, and its sign consequence.** -/
private theorem sum_eq_zero_of_family (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (hvar : Mori.IsVariety k sZ)
    (hsm : IsSmoothScheme sZ) (hZ : topologicalKrullDim Z = 4) [NoetherianSpace Z]
    {B : Divisor Z} (hB : B.IsSNC sZ) [LinearOrder B.support] [Fintype (DoubleSurface B)]
    (a : DoubleSurface B → ℚ) (ha : a ∈ orientedSurfaceCoefficients B)
    (m : B.support → ℚ) (hm : ∀ i, 0 < m i)
    (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (N : Set Z → ℚ)
    (hN : ∀ σ : DoubleSurface B, a σ ≠ 0 → ∀ l : B.support, l ≠ fstS σ → l ≠ sndS σ →
      ∀ T ∈ tcs σ.fst σ.snd l.1, T ⊆ σ.carrier → cNum sZ 𝓗 h𝓗 σ.carrier T = N T)
    (hNpos : ∀ i j l : B.support, i < j → j < l → ∀ T ∈ tcs i.1 j.1 l.1, 0 ≤ N T)
    (hX0 : ∀ i : B.support, (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
      (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * fxNum sZ 𝓗 h𝓗 π i P Q) = 0)
    (hDS : ∀ σ : DoubleSurface B, a σ ≠ 0 → ∑ l, m l * nsNum sZ 𝓗 h𝓗 σ.carrier (ε l) ≤ 0) :
    ∀ σ : DoubleSurface B, a σ ≠ 0 → ∑ l, m l * nsNum sZ 𝓗 h𝓗 σ.carrier (ε l) = 0 := by
  have hS := topologicalKrullDim_doubleSurface_le k sZ hvar hZ hB
  have hT := topologicalKrullDim_tripleCurve_le k sZ hvar hZ hB
  have hP2 : ∀ σ : DoubleSurface B,
      topologicalKrullDim (rho hB σ).idealSheaf.subscheme ≤ (2 : ℕ) := fun σ =>
    (dim_P_eq (rho hB σ) σ.carrier (image_support_rho hB σ)).symm ▸ hS σ
  have hP2' : ∀ (i : B.support) (σ : DoubleSurface B) (h : σ.fst = i.1),
      topologicalKrullDim (rhoOf hB σ h).idealSheaf.subscheme ≤ (2 : ℕ) := fun i σ h =>
    (dim_P_eq (rhoOf hB σ h) σ.carrier (image_support_rhoOf hB σ h)).symm ▸ hS σ
  have hcN : ∀ σ : DoubleSurface B, a σ ≠ 0 → ∀ (E : Mori.PrimeDivisor Z) (h : σ.fst = E)
      (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
      (hP : E.idealSheaf.subschemeι '' P.support = σ.carrier) (l : B.support),
      l ≠ fstS σ → l ≠ sndS σ → ∀ T ∈ tcs σ.fst σ.snd l.1, T ⊆ σ.carrier →
      haveI := h𝓗 σ.carrier
      curveNumP sZ P ((Scheme.Modules.pullback (phi P σ.carrier hP)).obj (𝓗 σ.carrier)) T =
        N T := by
    intro σ ha0 E h P hP l hl₁ hl₂ T hTm hTS
    haveI := h𝓗 σ.carrier
    rw [← cNum_eq sZ 𝓗 h𝓗 P σ.carrier hP T hTS
      (dim_le_one_of_ne hT (fun e => σ.fst_ne_snd (congrArg Subtype.val e)) hl₁.symm hl₂.symm
        (mem_tcs.1 hTm).2.1)]
    exact hN σ ha0 l hl₁ hl₂ T hTm hTS
  have core := core_identity hB a ha m hm (fun S l => nsNum sZ 𝓗 h𝓗 S (ε l))
    (fxNum sZ 𝓗 h𝓗 π) N
    (fun σ ha0 => by
      haveI := h𝓗 σ.carrier
      rw [nsNum_eq sZ 𝓗 h𝓗 (rho hB σ) σ.carrier (image_support_rho hB σ) (hP2 σ),
        fxNum_eq sZ 𝓗 h𝓗 π (fstS σ) (rho hB σ) (rho hB σ) σ.carrier (image_support_rho hB σ)
          (hP2 σ)]
      exact_mod_cast num_P_eps_snd sZ hvar hsm hB ε hε π hπ σ (hP2 σ) _)
    (fun σ l ha0 hl₁ hl₂ => by
      haveI := h𝓗 σ.carrier
      rw [nsNum_eq sZ 𝓗 h𝓗 (rho hB σ) σ.carrier (image_support_rho hB σ) (hP2 σ),
        num_P_eps_transversal sZ hvar hsm hB ε hε hT σ l hl₁ hl₂ (hP2 σ)]
      refine Finset.sum_congr rfl fun T hTm => ?_
      split_ifs with hTS
      · exact hcN σ ha0 σ.fst rfl (rho hB σ) (image_support_rho hB σ) l hl₁ hl₂ T hTm hTS
      · rfl)
    (fun i σ τ h h' hsnd hne => by
      rw [fxNum_eq sZ 𝓗 h𝓗 π i (rhoOf hB σ h) (rhoOf hB τ h') σ.carrier
        (image_support_rhoOf hB σ h) (hP2' i σ h)]
      haveI := h𝓗 σ.carrier
      exact_mod_cast num_P_pi_eq_zero_of_disjoint sZ hB π hπ i _ _
        (disjoint_support_rhoOf hB h h' hsnd hne) (hP2' i σ h) _)
    (fun i σ τ h h' ha0 hne => by
      haveI := h𝓗 σ.carrier
      rw [fxNum_eq sZ 𝓗 h𝓗 π i (rhoOf hB σ h) (rhoOf hB τ h') σ.carrier
        (image_support_rhoOf hB σ h) (hP2' i σ h),
        num_P_pi_transversal sZ hB π hπ hT i σ τ h h' hne (hP2' i σ h)]
      refine Finset.sum_congr rfl fun T hTm => ?_
      split_ifs with hTS
      · have hτi : sndS τ ≠ fstS σ := fun e =>
          τ.fst_ne_snd (h'.trans (h.symm.trans (congrArg Subtype.val e).symm))
        have hτσ : sndS τ ≠ sndS σ := fun e => hne (congrArg Subtype.val e).symm
        have hTm' : T ∈ tcs σ.fst σ.snd τ.snd := h ▸ hTm
        exact hcN σ ha0 i.1 h (rhoOf hB σ h) (image_support_rhoOf hB σ h) (sndS τ) hτi hτσ T
          hTm' hTS.1
      · rfl)
  simp only [hX0, mul_zero, Finset.sum_const_zero, zero_add] at core
  have hRnn : 0 ≤ ∑ i, ∑ j, ∑ l, (if i < j ∧ j < l then ∑ T ∈ tcs i.1 j.1 l.1,
      m i * m j * m l * (coeffT a i j T / (m i * m j) - coeffT a i l T / (m i * m l) +
        coeffT a j l T / (m j * m l)) ^ 2 * N T else 0) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg
      fun l _ => ?_
    split_ifs with hh
    · refine Finset.sum_nonneg fun T hT' => mul_nonneg (mul_nonneg ?_ (sq_nonneg _))
        (hNpos i j l hh.1 hh.2 T hT')
      have := hm i; have := hm j; have := hm l; positivity
    · exact le_rfl
  have hterm : ∀ σ : DoubleSurface B, (if fstS σ < sndS σ then m (fstS σ) * m (sndS σ) *
      (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 * ∑ l, m l * nsNum sZ 𝓗 h𝓗 σ.carrier (ε l)
      else 0) ≤ 0 := by
    intro σ
    split_ifs
    · by_cases ha0 : a σ = 0
      · simp [ha0]
      · exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (mul_pos (hm _) (hm _)).le (sq_nonneg _)) (hDS σ ha0)
    · exact le_rfl
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos fun σ _ => hterm σ).1
    (le_antisymm (Finset.sum_nonpos fun σ _ => hterm σ) (core ▸ hRnn))
  have key : ∀ σ : DoubleSurface B, a σ ≠ 0 → fstS σ < sndS σ →
      ∑ l, m l * nsNum sZ 𝓗 h𝓗 σ.carrier (ε l) = 0 := by
    intro σ ha0 hlt
    have h0 := hzero σ (Finset.mem_univ _)
    rw [if_pos hlt] at h0
    have hpos : 0 < m (fstS σ) * m (sndS σ) * (a σ / (m (fstS σ) * m (sndS σ))) ^ 2 := by
      have := hm (fstS σ); have := hm (sndS σ)
      have : a σ / (m (fstS σ) * m (sndS σ)) ≠ 0 := div_ne_zero ha0 (by positivity)
      positivity
    exact (mul_eq_zero.1 h0).resolve_left hpos.ne'
  intro σ ha0
  rcases lt_or_gt_of_ne (fun e : fstS σ = sndS σ => σ.fst_ne_snd (congrArg Subtype.val e))
    with hlt | hgt
  · exact key σ ha0 hlt
  · have hsw : a σ.swap ≠ 0 := by rw [ha σ]; exact neg_ne_zero.2 ha0
    exact key σ.swap hsw hgt

end Identity

/-! ### Positivity of `-D` against a contracted cut -/

section Sign

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k]

/-- Two-slot intersection numbers are symmetric. -/
private theorem intersectionNumber_swap2 {X Y : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (i : Y ⟶ X) [IsClosedImmersion i] (hd : topologicalKrullDim Y ≤ ((2 : ℕ) : WithBot ℕ∞))
    (A B : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] :
    intersectionNumber k f i 2 hd ![A, B] = intersectionNumber k f i 2 hd ![B, A] := by
  have h := intersectionNumber_comp_perm k f i 2 hd ![B, A] (Equiv.swap 0 1)
  rw [← h]
  congr 1
  funext t
  fin_cases t <;> simp

/-- **A relatively ample sheaf has positive degree on a contracted integral curve.** -/
private theorem intersectionNumber_one_pos_of_contracted {Z Y : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] (g : Z ⟶ Y) (L : Z.Modules) [Stacks.Ample.IsInvertibleModule Z L]
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    (hamp : Mori.IsRelativelyAmple g L) {W : Scheme.{0}} (j : W ⟶ Z) [IsClosedImmersion j]
    [IsIntegral W] (hW : topologicalKrullDim W = (1 : ℕ)) (y : Y) (hy : ∀ w, g (j w) = y) :
    0 < intersectionNumber k sZ j 1 hW.le (fun _ => L) := by
  set x := j (genericPoint W)
  have hcl : closure ({x} : Set Z) = Set.range j := by
    rw [show ({x} : Set Z) = j '' {genericPoint W} from (Set.image_singleton).symm,
      j.isClosedEmbedding.closure_image_eq,
      show closure ({genericPoint W} : Set W) = Set.univ from genericPoint_spec W, Set.image_univ]
  have hker : j.ker = (curveSubschemeAtι x).ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, Scheme.IdealSheafData.ker_subschemeι]
    congr 1
    apply Closeds.ext
    rw [Closeds.coe_closure, Closeds.coe_closure, hcl, j.isClosedEmbedding.isClosed_range.closure_eq]
  have := IsClosedImmersion.isIso_lift (curveSubschemeAtι x) j hker.symm
  have hdimC : topologicalKrullDim (curveSubschemeAt x) = 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift (curveSubschemeAtι x) j
        hker.symm.le))).isHomeomorph]
    exact_mod_cast hW
  let C : ProperCurve sZ := ⟨x, isProperCurve_of_isProper sZ hdimC⟩
  have hC : C.IsContractedBy g := by
    intro x' hx'
    change x' ∈ closure ({x} : Set Z) at hx'
    rw [hcl] at hx'
    obtain ⟨w, rfl⟩ := hx'
    exact (hy w).trans (hy _).symm
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g L
    hamp C hC
  have h1 : intersectionNumber k sZ j 1 hW.le (fun _ => L) =
      intersectionNumber k sZ C.ι 1 (by exact_mod_cast C.dim_le) (fun _ => L) := by
    rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      ← Snapper.sheafIntersectionNumber_eq_intersectionNumber]
    exact sheafIntersectionNumber_eq_of_ker_eq k sZ j C.ι hker 1 hW.le _ _
  have h2 := intersectionNumber_one_eq_invertibleCurveDegree k sZ C.ι C.dim_le L
  rw [h1, h2]
  exact hpos

/-- **Cutting an integral surface by a positive power of `B` and positivity on the curves.** -/
private theorem intersectionNumber_two_pos_of_cut {X W : Scheme.{0}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (j : W ⟶ X) [IsClosedImmersion j] [IsIntegral W] (hW : topologicalKrullDim W = (2 : ℕ))
    (L B : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B]
    (n : ℕ) (hn : 1 ≤ n) (D : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Nonempty D.subscheme]
    (e : ((Scheme.Modules.pullback j).obj B).tensorPowerModules (n : ℤ) ≅
      Stacks.Divisors.invertibleSheaf D)
    (hL : ∀ V : X.IdealSheafData, IsIntegral V.subscheme →
      (V.support : Set X) ⊆ j '' (D.support : Set W) →
      ∀ hV : topologicalKrullDim V.subscheme = (1 : ℕ),
        0 < intersectionNumber k f V.subschemeι 1 hV.le (fun _ => L)) :
    0 < intersectionNumber k f j 2 hW.le ![L, B] := by
  classical
  have hDdim : topologicalKrullDim D.subscheme = ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k (j ≫ f) D inferInstance hW
  rw [intersectionNumber_swap2 f j hW.le L B]
  set N : Fin 2 → X.Modules :=
    Function.update ![B, L] 0
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 (![B, L] 0) (n : ℤ))
    with hN
  haveI : ∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (N q) :=
    isInvertible_update ![B, L] 0 _
  have hNiso : (Scheme.Modules.pullback j).obj (N 0) ≅
      (Stacks.Divisors.invertibleSheaf D : W.Modules) :=
    eqToIso (congrArg (Scheme.Modules.pullback j).obj
        (Function.update_self (0 : Fin 2) _ ![B, L])) ≪≫
      Scheme.Modules.pullbackTensorPowerIso j B n ≪≫ e
  have hNpos : 0 < intersectionNumber k f j 2 hW.le N := by
    rw [intersectionNumber_eq_of_isEffectiveCartierDivisor k f j 1 hW.le N D hDdim.le hNiso,
      intersectionNumber_congr_family k f _ 1 _
        (funext fun t => by fin_cases t; rfl : (fun t : Fin 1 => N t.succ) = fun _ => L)]
    refine intersectionNumber_pos_of_pos_topDimComponents k f (D.subschemeι ≫ j) 1 hDdim _
      (fun V => ?_)
    haveI : IsIntegral V.1.subscheme := V.2.1
    have hVdim : topologicalKrullDim V.1.subscheme = ((1 : ℕ) : WithBot ℕ∞) := by
      refine V.2.2.2.trans ?_
      rw [Stacks.Chow.supp_pushforwardStructureSheaf (D.subschemeι ≫ j),
        topologicalKrullDim_range_eq (D.subschemeι ≫ j)]
      exact hDdim
    have hVsub : (V.1.support : Set X) ⊆ j '' (D.support : Set W) := by
      intro x hx
      have h := V.2.2.1 hx
      rw [Stacks.Chow.supp_pushforwardStructureSheaf (D.subschemeι ≫ j), Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.range_comp, D.range_subschemeι] at h
      exact h
    exact hL V.1 inferInstance hVsub hVdim
  have hmul : intersectionNumber k f j 2 hW.le N = n * intersectionNumber k f j 2 hW.le ![B, L] :=
    intersectionNumber_update_tensorPower k f j 2 hW.le ![B, L] 0 n
  rw [hmul] at hNpos
  exact pos_of_mul_pos_right hNpos (by exact_mod_cast (Nat.zero_le n))

/-- `c ↦ (q^*𝒪(c) · H)` is additive. -/
private theorem num_pullback_sheaf_add {X' Z : Scheme.{0}} (f : X' ⟶ Spec (.of k)) [IsProper f]
    (hd : topologicalKrullDim X' ≤ (2 : ℕ)) (q : X' ⟶ Z) (H : X'.Modules)
    [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 H] (c c' : Z.CartierDivisor) :
    sheafIntersectionNumber k f (𝟙 _) 2 hd
        ![(Scheme.Modules.pullback q).obj (MMP.CartierDivisor.sheaf (c + c')), H] =
      sheafIntersectionNumber k f (𝟙 _) 2 hd
          ![(Scheme.Modules.pullback q).obj (MMP.CartierDivisor.sheaf c), H] +
        sheafIntersectionNumber k f (𝟙 _) 2 hd
          ![(Scheme.Modules.pullback q).obj (MMP.CartierDivisor.sheaf c'), H] :=
  sheafIntersectionNumber_two_tensor f (𝟙 _) hd _ _ _ H
    ((Scheme.Modules.pullback q).mapIso
        (MMP.CartierDivisorSheaf.sheafMulIso c c').symm ≪≫
      pullbackTensorIso' q _ _)

variable {Z : Scheme.{0}}

/-- `c ↦ (𝒪(c)|_S · 𝓗_S)` as an additive map. -/
private noncomputable def nsHom (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (S : Set Z) (hS2 : topologicalKrullDim (surfI S).subscheme ≤ (2 : ℕ)) :
    Z.CartierDivisor →+ ℤ :=
  haveI := h𝓗 S
  AddMonoidHom.mk' (fun c => sheafIntersectionNumber k ((surfI S).subschemeι ≫ sZ) (𝟙 _) 2 hS2
      ![(Scheme.Modules.pullback (surfI S).subschemeι).obj
        (MMP.CartierDivisor.sheaf c), 𝓗 S])
    (fun c c' => num_pullback_sheaf_add _ hS2 _ _ c c')

private theorem nsNum_eq_nsHom (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (S : Set Z) (hS2 : topologicalKrullDim (surfI S).subscheme ≤ (2 : ℕ)) (c : Z.CartierDivisor) :
    nsNum sZ 𝓗 h𝓗 S c = nsHom sZ 𝓗 h𝓗 S hS2 c := by
  rw [nsNum, dif_pos hS2]
  rfl

/-- `∑ₗ mₗ (εₗ · 𝓗)_S = -(-c · 𝓗)_S` for `c = ∑ₗ mₗ εₗ`. -/
private theorem sum_mul_nsNum_eq_neg (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (S : Set Z) (hS2 : topologicalKrullDim (surfI S).subscheme ≤ (2 : ℕ)) {ι : Type*}
    (s : Finset ι) (m : ι → ℤ) (ε : ι → Z.CartierDivisor) :
    ∑ l ∈ s, (m l : ℚ) * nsNum sZ 𝓗 h𝓗 S (ε l) =
      -nsNum sZ 𝓗 h𝓗 S (-∑ l ∈ s, m l • ε l) := by
  simp only [nsNum_eq_nsHom sZ 𝓗 h𝓗 S hS2, map_neg, map_sum, map_zsmul, Int.cast_neg,
    Int.cast_sum, smul_eq_mul, Int.cast_mul, neg_neg]

/-- **Positivity of `(-c · 𝓗)_S` against a contracted cut.** -/
private theorem nsNum_pos_of_cut (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {Y : Scheme.{0}} (g : Z ⟶ Y)
    (D : Divisor Z) (hDc : (-D).IsCartier) (hamp : (-D).IsRelativelyAmple g hDc)
    (c : Z.CartierDivisor) (hcw : MMP.Intersection.IsWeilDivisorOfCartier (-c) (-D))
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (S : Set Z) [IsIntegral (surfI S).subscheme]
    (hS : topologicalKrullDim (surfI S).subscheme = (2 : ℕ)) (n : ℕ) (hn : 1 ≤ n)
    (F : (surfI S).subscheme.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor F]
    [Nonempty F.subscheme]
    (e : ((Scheme.Modules.pullback (𝟙 _)).obj (𝓗 S)).tensorPowerModules (n : ℤ) ≅
      Stacks.Divisors.invertibleSheaf F)
    (hF : ∀ V : (surfI S).subscheme.IdealSheafData, IsIntegral V.subscheme →
      (V.support : Set (surfI S).subscheme) ⊆ (F.support : Set (surfI S).subscheme) →
        ∃ y, ∀ w, g ((V.subschemeι ≫ (surfI S).subschemeι) w) = y) :
    0 < nsNum sZ 𝓗 h𝓗 S (-c) := by
  haveI := h𝓗 S
  obtain ⟨eW⟩ := MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf hcw
  haveI := hDc.isInvertibleModule_divisorialSheaf
  haveI : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 (-D).divisorialSheaf :=
    hDc.isInvertibleModule_divisorialSheaf
  rw [nsNum, dif_pos hS.le, sheafIntersectionNumber_two_congr_iso _ _ _ _
    ((Scheme.Modules.pullback (surfI S).subschemeι).obj (-D).divisorialSheaf) _
    ((Scheme.Modules.pullback (surfI S).subschemeι).mapIso eW),
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hpos := intersectionNumber_two_pos_of_cut (k := k) ((surfI S).subschemeι ≫ sZ) (𝟙 _) hS
    ((Scheme.Modules.pullback (surfI S).subschemeι).obj (-D).divisorialSheaf) (𝓗 S) n hn F e
    (fun V hVi hVsub hV => by
      have hVsub' : (V.support : Set (surfI S).subscheme) ⊆
          (F.support : Set (surfI S).subscheme) := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := hVsub hx
        simpa using hy
      obtain ⟨y, hy⟩ := hF V hVi hVsub'
      rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
        ← sheafIntersectionNumber_comp_eq_of_iso k sZ (surfI S).subschemeι V.subschemeι 1 hV.le
          (fun _ => (-D).divisorialSheaf) _ (fun _ => Iso.refl _),
        Snapper.sheafIntersectionNumber_eq_intersectionNumber]
      exact intersectionNumber_one_pos_of_contracted sZ g (-D).divisorialSheaf hamp
        (V.subschemeι ≫ (surfI S).subschemeι) hV y hy)
  exact_mod_cast hpos

end Sign

/-! ### The `Zᵢ(a)`-term -/

section X0

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z : Scheme.{0}}

private theorem isWeilDivisorOfCartier_zero {X : Scheme.{0}} :
    MMP.Intersection.IsWeilDivisorOfCartier (0 : X.CartierDivisor) (0 : Divisor X) := fun P => by
  simpa using MMP.Intersection.isOrderAlong_zero (MMP.Intersection.primeDivisorSubvariety P)

private theorem isWeilDivisorOfCartier_add {X : Scheme.{0}} {A B : X.CartierDivisor} {v w : Divisor X}
    (hA : MMP.Intersection.IsWeilDivisorOfCartier A v)
    (hB : MMP.Intersection.IsWeilDivisorOfCartier B w) :
    MMP.Intersection.IsWeilDivisorOfCartier (A + B) (v + w) := fun P => by
  simpa [DivisorWithCoeffs.coeff] using (hA P).add (hB P)

private theorem isWeilDivisorOfCartier_neg {X : Scheme.{0}} {A : X.CartierDivisor}
    {w : Divisor X} (h : MMP.Intersection.IsWeilDivisorOfCartier A w) :
    MMP.Intersection.IsWeilDivisorOfCartier (-A) (-w) := by
  intro P
  obtain ⟨a, b, ha, hb, ⟨g, ⟨U, hxU, g', hg', hgg⟩, hbu, hbg⟩, la, lb, hla, hlb, hN⟩ := h P
  have hgu : IsUnit g := hgg ▸ g'.isUnit.map _
  refine ⟨b, a, hb, ha, ⟨_, ⟨U, hxU, g'⁻¹, hg'.inv, rfl⟩, ?_, ?_⟩, lb, la, hlb, hla, ?_⟩
  · rw [← hbg]; exact hbu.mul hgu
  · rw [← hbg, ← hgg, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rw [DivisorWithCoeffs.coeff_neg, hN]; ring

private theorem isWeilDivisorOfCartier_zsmul {X : Scheme.{0}} {A : X.CartierDivisor} {w : Divisor X}
    (h : MMP.Intersection.IsWeilDivisorOfCartier A w) (n : ℤ) :
    MMP.Intersection.IsWeilDivisorOfCartier (n • A) (n • w) := by
  induction n using Int.induction_on with
  | zero => simpa using isWeilDivisorOfCartier_zero
  | succ m ih => simpa [add_smul] using isWeilDivisorOfCartier_add ih h
  | pred m ih =>
    have := isWeilDivisorOfCartier_add ih (isWeilDivisorOfCartier_neg h)
    rwa [← neg_one_smul ℤ A, ← neg_one_smul ℤ w, ← add_smul, ← add_smul,
      ← sub_eq_add_neg] at this

private theorem isWeilDivisorOfCartier_sum {X : Scheme.{0}} {ι : Type*} (s : Finset ι) (n : ι → ℤ)
    (c : ι → X.CartierDivisor) (w : ι → Divisor X)
    (h : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (c i) (w i)) :
    MMP.Intersection.IsWeilDivisorOfCartier (∑ i ∈ s, n i • c i) (∑ i ∈ s, n i • w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWeilDivisorOfCartier_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isWeilDivisorOfCartier_add (isWeilDivisorOfCartier_zsmul (h a) _) ih

open Classical in
/-- **The `Zᵢ(a)`-term vanishes**: for a numerically trivial `ℚ`-divisor `F` on the component,
`∑_Q F_Q (π_Q|_P · 𝓗_P) = 0`. -/
private theorem sum_mul_fxNum_eq_zero (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {B : Divisor Z}
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S)) (i : B.support)
    [IsIntegral i.1.idealSheaf.subscheme] [IsLocallyNoetherian i.1.idealSheaf.subscheme]
    [IsNormal i.1.idealSheaf.subscheme] [CompactSpace i.1.idealSheaf.subscheme]
    (F : QDivisor i.1.idealSheaf.subscheme)
    (hNT : F.IsNumericallyTrivial k (i.1.idealSheaf.subschemeι ≫ sZ))
    (P : Mori.PrimeDivisor i.1.idealSheaf.subscheme) :
    F.sum (fun Q cQ => cQ * fxNum sZ 𝓗 h𝓗 π i P Q) = 0 := by
  by_cases hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ)
  swap
  · rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun Q _ => ?_
    rw [fxNum, dif_neg hP2, mul_zero]
  haveI := h𝓗 (i.1.idealSheaf.subschemeι '' P.support)
  let Φ : i.1.idealSheaf.subscheme.CartierDivisor →+ ℤ := AddMonoidHom.mk'
    (fun c => sheafIntersectionNumber k
      (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2
      ![(Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
        (MMP.CartierDivisor.sheaf c),
        (Scheme.Modules.pullback (phi P _ rfl)).obj
          (𝓗 (i.1.idealSheaf.subschemeι '' P.support))])
    (fun c c' => num_pullback_sheaf_add _ hP2 _ _ c c')
  have hfx : ∀ Q, fxNum sZ 𝓗 h𝓗 π i P Q = (Φ (π i Q) : ℚ) := fun Q => by
    rw [fxNum, dif_pos hP2]
    rfl
  obtain ⟨hQC, h0⟩ := (QDivisor.isNumericallyTrivial_iff F).1 hNT
  have hEC := QDivisor.isCartierDivisor_cartierIndex_smul hQC
  have hn : 0 < F.cartierIndex hQC := QDivisor.cartierIndex_pos hQC
  have hEq : Divisor.toQDivisor hEC.toDivisor = ((F.cartierIndex hQC : ℕ) : ℤ) • F :=
    hEC.toQDivisor_toDivisor
  have hcoeff : ∀ Q, ((hEC.toDivisor Q : ℤ) : ℚ) = (F.cartierIndex hQC : ℚ) * F Q := fun Q => by
    have := congrArg (fun G : QDivisor _ => G Q) hEq
    have h' := Divisor.coeff_toQDivisor hEC.toDivisor Q
    simp only [DivisorWithCoeffs.coeff] at h'
    simp only [Finsupp.smul_apply, h', zsmul_eq_mul] at this
    rw [this]
    push_cast
    ring
  have hcW : MMP.Intersection.IsWeilDivisorOfCartier
      (∑ Q ∈ hEC.toDivisor.support, hEC.toDivisor Q • π i Q) hEC.toDivisor := by
    have := isWeilDivisorOfCartier_sum hEC.toDivisor.support (fun Q => hEC.toDivisor Q) (π i)
      (fun Q => Finsupp.single Q 1) (hπ i)
    have hE : (∑ Q ∈ hEC.toDivisor.support, hEC.toDivisor Q • Finsupp.single Q (1 : ℤ)) =
        hEC.toDivisor := by
      conv_rhs => rw [← Finsupp.sum_single hEC.toDivisor]
      simp [Finsupp.sum, Finsupp.smul_single]
    rwa [hE] at this
  have hΦc : Φ (∑ Q ∈ hEC.toDivisor.support, hEC.toDivisor Q • π i Q) = 0 := by
    change sheafIntersectionNumber k
      (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 2 hP2 _ = 0
    refine sheafIntersectionNumber_eq_zero_of_degree_eq_zero k
      (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) (𝟙 _) 1 hP2 _ (fun C => ?_)
    have : IsIntegral C.scheme :=
      StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
        isIrreducible_singleton.closure
    obtain ⟨eW⟩ := MMP.Intersection.IsWeilDivisorOfCartier.nonempty_sheaf_iso_divisorialSheaf hcW
    have hEc := hEC.isCartier_toDivisor
    haveI := hEc.isInvertibleModule_divisorialSheaf
    haveI : SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
        i.1.idealSheaf.subscheme.ringCatSheaf.2 hEC.toDivisor.divisorialSheaf :=
      hEc.isInvertibleModule_divisorialSheaf
    have h1 := h0 C.scheme (C.ι ≫ P.idealSheaf.subschemeι) C.dim_eq
    rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k _ _ _ F hQC hEC.toDivisor hEc hEq,
      div_eq_zero_iff] at h1
    have h2 : hEC.toDivisor.degreeOn k (i.1.idealSheaf.subschemeι ≫ sZ)
        (C.ι ≫ P.idealSheaf.subschemeι) C.dim_le hEc = 0 := by
      rcases h1 with h1 | h1
      · exact_mod_cast h1
      · exact absurd h1 (by exact_mod_cast hn.ne')
    change degreeOn k (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ) C.ι C.dim_le
      ((Scheme.Modules.pullback P.idealSheaf.subschemeι).obj
        (MMP.CartierDivisor.sheaf _)) = 0
    rw [degreeOn_pullback_eq_degreeOn_comp
      (P.idealSheaf.subschemeι ≫ i.1.idealSheaf.subschemeι ≫ sZ)
      (i.1.idealSheaf.subschemeι ≫ sZ) P.idealSheaf.subschemeι C.ι rfl C.dim_le,
      degreeOn_eq_of_iso k _ _ C.dim_le eW]
    exact h2
  have hsupp : hEC.toDivisor.support = F.support := by
    ext Q
    simp only [Finsupp.mem_support_iff, ne_eq]
    have := hcoeff Q
    constructor
    · intro h hF
      rw [hF, mul_zero] at this
      exact h (by exact_mod_cast this)
    · intro hF h
      rw [h, Int.cast_zero] at this
      exact hF ((mul_eq_zero.1 this.symm).resolve_left (by exact_mod_cast hn.ne'))
  have hsum : (F.cartierIndex hQC : ℚ) * F.sum (fun Q cQ => cQ * fxNum sZ 𝓗 h𝓗 π i P Q) =
      (Φ (∑ Q ∈ hEC.toDivisor.support, hEC.toDivisor Q • π i Q) : ℚ) := by
    rw [map_sum, Int.cast_sum, Finsupp.sum, Finset.mul_sum, hsupp]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [map_zsmul, smul_eq_mul, Int.cast_mul, hcoeff, hfx]
    ring
  rw [hΦc, Int.cast_zero] at hsum
  exact (mul_eq_zero.1 hsum).resolve_left (by exact_mod_cast hn.ne')

end X0

/-! ### Surfaces contracted to points -/

section Step2

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z : Scheme.{0}}

open Classical in
/-- **The family identity forces `(-c_D · 𝓗)_S = 0` on every supported surface**, once that
number is nonnegative there. -/
private theorem nsNum_eq_zero_of_family (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ) (hZ : topologicalKrullDim Z = 4)
    [NoetherianSpace Z] {D : Divisor Z} (hB : D.IsSNC sZ) [LinearOrder D.support]
    [Fintype (DoubleSurface D)] (hDpos : ∀ P ∈ D.support, 0 < D.coeff P)
    (a : DoubleSurface D → ℚ) (ha : a ∈ orientedSurfaceCoefficients D)
    (ε : D.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : D.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (N : Set Z → ℚ)
    (hN : ∀ σ : DoubleSurface D, a σ ≠ 0 → ∀ l : D.support, l ≠ fstS σ → l ≠ sndS σ →
      ∀ T ∈ tcs σ.fst σ.snd l.1, T ⊆ σ.carrier → cNum sZ 𝓗 h𝓗 σ.carrier T = N T)
    (hNpos : ∀ i j l : D.support, i < j → j < l → ∀ T ∈ tcs i.1 j.1 l.1, 0 ≤ N T)
    (hX0 : ∀ i : D.support, (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
      (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * fxNum sZ 𝓗 h𝓗 π i P Q) = 0)
    (hDS : ∀ σ : DoubleSurface D, a σ ≠ 0 →
      0 ≤ nsNum sZ 𝓗 h𝓗 σ.carrier (-∑ l : D.support, D.coeff l.1 • ε l)) :
    ∀ σ : DoubleSurface D, a σ ≠ 0 →
      nsNum sZ 𝓗 h𝓗 σ.carrier (-∑ l : D.support, D.coeff l.1 • ε l) = 0 := by
  have hS := topologicalKrullDim_doubleSurface_le k sZ hvar hZ hB
  have hsum : ∀ σ : DoubleSurface D, ∑ l : D.support, ((D.coeff l.1 : ℤ) : ℚ) *
      nsNum sZ 𝓗 h𝓗 σ.carrier (ε l) =
      -nsNum sZ 𝓗 h𝓗 σ.carrier (-∑ l : D.support, D.coeff l.1 • ε l) := fun σ =>
    sum_mul_nsNum_eq_neg sZ 𝓗 h𝓗 σ.carrier (hS σ) Finset.univ (fun l => D.coeff l.1) ε
  have key := sum_eq_zero_of_family sZ hvar hsm hZ hB a ha (fun l => (D.coeff l.1 : ℚ))
    (fun l => by exact_mod_cast hDpos l.1 l.2) ε hε π hπ 𝓗 h𝓗 N hN hNpos hX0
    (fun σ h => by rw [hsum σ]; linarith [hDS σ h])
  intro σ h
  have := key σ h
  rw [hsum σ] at this
  linarith

/-- The reduced double surface is integral. -/
private theorem isIntegral_surfI {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {D : Divisor Z} (hB : D.IsSNC sZ)
    (σ : DoubleSurface D) : IsIntegral (surfI σ.carrier).subscheme := by
  have hirr : IsIrreducible σ.carrier := by
    rw [← image_support_rho hB σ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure.image _ σ.fst.idealSheaf.subschemeι.continuous.continuousOn
  exact StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hirr.closure

/-- The reduced double surface has dimension two. -/
public theorem dim_surfI_eq {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {D : Divisor Z} (hB : D.IsSNC sZ)
    (hE : ∀ i : D.support, topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ))
    (σ : DoubleSurface D) : topologicalKrullDim (surfI σ.carrier).subscheme = (2 : ℕ) := by
  rw [← dim_P_eq (rho hB σ) σ.carrier (image_support_rho hB σ)]
  have := σ.fst.integral
  obtain ⟨R, -, hPe, -, -⟩ := exists_comap_eq_rho_mul hB σ
  haveI : Nonempty (rho hB σ).idealSheaf.subscheme := by
    have hη : (rho hB σ).genericPoint ∈ Set.range (rho hB σ).idealSheaf.subschemeι := by
      rw [(rho hB σ).idealSheaf.range_subschemeι]
      change _ ∈ ((rho hB σ).support : Set _)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    exact ⟨hη.choose⟩
  exact topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k
    (σ.fst.idealSheaf.subschemeι ≫ sZ) (rho hB σ).idealSheaf hPe (hE (fstS σ))

/-- `(A · T)` on `Z`, zero above dimension one. -/
private noncomputable def zNum (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (A : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 A] (T : Set Z) : ℚ := by
  classical
  exact if h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ) then
    (sheafIntersectionNumber k sZ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι
      1 h (fun _ => A) : ℚ) else 0

private theorem cNum_pullback_eq_zNum (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (A : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 A] (S T : Set Z)
    (hTS : closure T ⊆ closure S)
    (hT1 : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ)) :
    cNum sZ (fun S => (Scheme.Modules.pullback (surfI S).subschemeι).obj A)
      (fun S => inferInstance) S T = zNum sZ A T := by
  have hker := ker_curveClosedsS_eq S T hTS
  have hd : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subscheme ≤ (1 : ℕ) := by
    have := IsClosedImmersion.isIso_lift _ _ hker.symm
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift _ _ hker.symm.le))).isHomeomorph]
    exact hT1
  rw [cNum, dif_pos hd, zNum, dif_pos hT1]
  congr 1
  rw [← sheafIntersectionNumber_comp_eq_of_iso k sZ (surfI S).subschemeι _ 1 hd (fun _ => A) _
      (fun _ => Iso.refl _)]
  exact sheafIntersectionNumber_eq_of_ker_eq k sZ _ _ hker 1 hd hT1 _

private theorem zNum_nonneg (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (A : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 A] (hA : Scheme.Modules.IsAmple Z A)
    (T : Set Z) : 0 ≤ zNum sZ A T := by
  unfold zNum
  split_ifs with h
  · have h0 : (0 : ℤ) ≤ sheafIntersectionNumber k sZ
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι 1 h (fun _ => A) := by
      rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
        intersectionNumber_eq_sum_dimComponents k sZ _ 1 h]
      refine finsum_nonneg fun W => mul_nonneg (Int.natCast_nonneg _) ?_
      have := W.2.1
      exact (intersectionNumber_pos k sZ W.1.subschemeι 1 (by exact_mod_cast W.2.2.2)
        (fun _ => A) (fun _ => hA)).le
    exact_mod_cast h0
  · exact le_rfl

/-- **`(-c_D · A)_S > 0` on a surface contracted to a point.** -/
private theorem nsNum_pullback_pos (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] {Y : Scheme.{0}} (g : Z ⟶ Y)
    (D : Divisor Z) (hDc : (-D).IsCartier) (hamp : (-D).IsRelativelyAmple g hDc)
    (c : Z.CartierDivisor) (hcw : MMP.Intersection.IsWeilDivisorOfCartier (-c) (-D))
    (A : Z.Modules) [Stacks.Ample.IsInvertibleModule Z A]
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 A] (hA : Stacks.Ample.IsAmple Z A)
    (S : Set Z) [IsIntegral (surfI S).subscheme]
    (hS : topologicalKrullDim (surfI S).subscheme = (2 : ℕ)) (y : Y)
    (hy : ∀ z ∈ closure S, g z = y) :
    0 < nsNum sZ (fun S => (Scheme.Modules.pullback (surfI S).subschemeι).obj A)
      (fun S => inferInstance) S (-c) := by
  have hposdim : 0 < topologicalKrullDim (surfI S).subscheme := by
    rw [hS]; exact_mod_cast Nat.succ_pos 1
  have hamp1 : Stacks.Ample.IsAmple (surfI S).subscheme
      ((Scheme.Modules.pullback (surfI S).subschemeι).obj A) :=
    Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
      (surfI S).subschemeι A hA (Or.inl ⟨inferInstance, inferInstance⟩)
  have hamp2 : Scheme.Modules.IsAmple (surfI S).subscheme ((Scheme.Modules.pullback (𝟙 _)).obj
      ((Scheme.Modules.pullback (surfI S).subschemeι).obj A)) :=
    Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _
      (Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
        (𝟙 _) _ hamp1 (Or.inl ⟨inferInstance, inferInstance⟩))
  obtain ⟨n, F, hn, hFc, hFne, ⟨e⟩⟩ :=
    exists_effectiveCartierDivisor_tensorPower_of_isAmple k ((surfI S).subschemeι ≫ sZ) hposdim
      _ hamp2
  haveI := hFc
  haveI := hFne
  refine nsNum_pos_of_cut sZ g D hDc hamp c hcw _ _ S hS n hn F e (fun V _ _ => ⟨y, fun w => ?_⟩)
  refine hy _ ?_
  have : (surfI S).subschemeι (V.subschemeι w) ∈ Set.range (surfI S).subschemeι := ⟨_, rfl⟩
  rw [(surfI S).range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Closeds.coe_closure] at this
  exact this

/-- **Step 2.** If every surface supporting `a` is contracted to a point, then `a = 0`. -/
private theorem eq_zero_of_forall_contracted (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ) (hZ : topologicalKrullDim Z = 4)
    [NoetherianSpace Z] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {D : Divisor Z} (hB : D.IsSNC sZ) [LinearOrder D.support]
    [Fintype (DoubleSurface D)] (hDpos : ∀ P ∈ D.support, 0 < D.coeff P)
    (a : DoubleSurface D → ℚ) (ha : a ∈ orientedSurfaceCoefficients D)
    (ε : D.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : D.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hE3 : ∀ i : D.support, topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ))
    (hX0 : ∀ (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
      (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
        (surfI S).subscheme.ringCatSheaf.2 (𝓗 S)) (i : D.support),
      (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * fxNum sZ 𝓗 h𝓗 π i P Q) = 0)
    {Y : Scheme.{0}} (g : Z ⟶ Y) (hDc : (-D).IsCartier) (hamp : (-D).IsRelativelyAmple g hDc)
    (hcw : MMP.Intersection.IsWeilDivisorOfCartier (-∑ l : D.support, D.coeff l.1 • ε l) (-D))
    (A : Z.Modules) [Stacks.Ample.IsInvertibleModule Z A]
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 A] (hA : Stacks.Ample.IsAmple Z A)
    (hpt : ∀ σ : DoubleSurface D, a σ ≠ 0 → ∃ y, ∀ z ∈ σ.carrier, g z = y) :
    a = 0 := by
  have hT := topologicalKrullDim_tripleCurve_le k sZ hvar hZ hB
  have hpos : ∀ σ : DoubleSurface D, a σ ≠ 0 →
      0 < nsNum sZ (fun S => (Scheme.Modules.pullback (surfI S).subschemeι).obj A)
        (fun S => inferInstance) σ.carrier (-∑ l : D.support, D.coeff l.1 • ε l) := by
    intro σ ha0
    obtain ⟨y, hy⟩ := hpt σ ha0
    haveI := isIntegral_surfI hB σ
    exact nsNum_pullback_pos sZ g D hDc hamp _ hcw A hA σ.carrier (dim_surfI_eq hB hE3 σ) y
      (fun z hz => hy z (by rwa [(isClosed_carrier σ).closure_eq] at hz))
  have hzero := nsNum_eq_zero_of_family sZ hvar hsm hZ hB hDpos a ha ε hε π hπ
    (fun S => (Scheme.Modules.pullback (surfI S).subschemeι).obj A) (fun S => inferInstance)
    (zNum sZ A)
    (fun σ _ l hl₁ hl₂ T hTm hTS => cNum_pullback_eq_zNum sZ A σ.carrier T (closure_mono hTS)
      (dim_le_one_of_ne hT (fun e => σ.fst_ne_snd (congrArg Subtype.val e)) hl₁.symm hl₂.symm
        (mem_tcs.1 hTm).2.1))
    (fun _ _ _ _ _ T _ =>
      zNum_nonneg sZ A (Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple _ _ hA) T)
    (hX0 _ _) (fun σ ha0 => (hpos σ ha0).le)
  funext σ
  by_contra h
  have h1 := hzero σ h
  have h2 := hpos σ h
  rw [h1] at h2
  exact lt_irrefl _ h2

end Step2

/-! ### The components and their divisors -/

section Glue

variable {k : Type} [Field k] {Z : Scheme.{0}}

/-- On a smooth integral scheme every Weil divisor is the Weil divisor of a Cartier divisor. -/
private theorem exists_isWeilDivisorOfCartier_of_isSmoothScheme {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme sX) (w : Divisor X) :
    ∃ A : X.CartierDivisor, MMP.Intersection.IsWeilDivisorOfCartier A w :=
  (MMP.Resolution.Bridges.uniqueFactorization_and_exists_isWeilDivisorOfCartier).2 X
    (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm) w

/-- The prime divisor `ρ(σ)` of a component is smooth. -/
private theorem isSmoothScheme_rho [PerfectField k] {sZ : Z ⟶ Spec (.of k)} [IsProper sZ]
    {D : Divisor Z} (hB : D.IsSNC sZ) (σ : DoubleSurface D) :
    IsSmoothScheme ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι ≫ sZ) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hab : (⟨σ.snd, σ.snd_mem⟩ : D.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter (σ.fst.idealSheaf.subschemeι ≫ sZ)
    (rho hB σ).idealSheaf fun y hy => ?_
  have hy' : y ∈ (rho hB σ).support := hy
  obtain ⟨m, w, j, hw, hst⟩ := stalk_comap_component hB hab y
    (mem_support_comap_snd_of_mem_rhoOf hB σ rfl hy')
  exact ⟨m, w, j, hw, (stalk_rho hB σ hy').trans hst⟩

private theorem isSmoothScheme_rhoOf [PerfectField k] {sZ : Z ⟶ Spec (.of k)} [IsProper sZ]
    {D : Divisor Z} (hB : D.IsSNC sZ) {E : Mori.PrimeDivisor Z} (σ : DoubleSurface D)
    (h : σ.fst = E) :
    IsSmoothScheme ((rhoOf hB σ h).idealSheaf.subschemeι ≫ E.idealSheaf.subschemeι ≫ sZ) := by
  subst h
  exact isSmoothScheme_rho hB σ

/-- The components of an snc divisor on a fourfold have dimension three. -/
private theorem dim_component_eq {sZ : Z ⟶ Spec (.of k)} (hvar : Mori.IsVariety k sZ)
    (hsm : IsSmoothScheme sZ) (hZ : topologicalKrullDim Z = 4) {D : Divisor Z}
    (ε : D.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (i : D.support) : topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ) := by
  have := hvar
  haveI : IsIntegral Z := hvar.toIsIntegral
  obtain ⟨he, hsub⟩ := exists_isEffective_eps k sZ hvar hsm ε hε i
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor i.1.idealSheaf :=
    hsub ▸ MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme he
  haveI : Nonempty i.1.idealSheaf.subscheme := by
    have hη : i.1.genericPoint ∈ Set.range i.1.idealSheaf.subschemeι := by
      rw [i.1.idealSheaf.range_subschemeι]
      change _ ∈ (i.1.support : Set _)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    exact ⟨hη.choose⟩
  exact topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k sZ i.1.idealSheaf hE
    (by rw [hZ]; rfl)

/-- Every prime divisor of a component with nonzero coefficient in `Zᵢ(a)` is a `ρ(σ)`. -/
private theorem exists_rhoOf_eq_of_mem_support {sZ : Z ⟶ Spec (.of k)} [IsProper sZ]
    [NoetherianSpace Z] {D : Divisor Z} (hB : D.IsSNC sZ) (a : DoubleSurface D → ℚ)
    (E : Mori.PrimeDivisor Z) (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : P ∈ (surfaceCoefficientDivisor a E).support) :
    ∃ (σ : DoubleSurface D) (h : σ.fst = E), rhoOf hB σ h = P := by
  by_contra hne
  push Not at hne
  apply Finsupp.mem_support_iff.1 hP
  have := coeff_surfaceCoefficientDivisor a E P
  simp only [DivisorWithCoeffs.coeff] at this
  rw [this]
  exact surfaceCoefficientCoeff_eq_zero hB a P hne

/-- **The divisors `Zᵢ(a)` are numerically trivial on the components.** -/
private theorem isNumericallyTrivial_surfaceCoefficientDivisor {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] [IsProper (Z ↘ Spec (.of ℂ))] [NoetherianSpace Z]
    (hvar : Mori.IsVariety ℂ (Z ↘ Spec (.of ℂ))) {D : Divisor Z}
    (hB : D.IsSNC (Z ↘ Spec (.of ℂ)))
    (π : ∀ i : D.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (A : Z.Modules) [Stacks.Ample.IsInvertibleModule Z A] (hA : Stacks.Ample.IsAmple Z A)
    (hE3 : ∀ i : D.support, topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ))
    (a : DoubleSurface D → ℚ) (i : D.support)
    [IsLocallyNoetherian i.1.idealSheaf.subscheme] [IsNormal i.1.idealSheaf.subscheme]
    [CompactSpace i.1.idealSheaf.subscheme]
    (h0 : MMP.Chow.divisorClass i.1.idealSheaf.subscheme (surfaceCoefficientDivisor a i.1) = 0) :
    (surfaceCoefficientDivisor a i.1).IsNumericallyTrivial ℂ
      (i.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))) := by
  have := hvar
  have := i.1.integral
  have hv : AlgebraicGeometry.IsVariety ℂ (i.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))) := ⟨⟩
  have hamp : Stacks.Ample.IsAmple i.1.idealSheaf.subscheme
      ((Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj A) :=
    Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
      i.1.idealSheaf.subschemeι A hA (Or.inl ⟨inferInstance, inferInstance⟩)
  have htf := isProjective_tfae_seven_of_exists_isAmple
    (i.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ)))
      ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  have h5 : IsProper (i.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))) ∧
      ∃ (L : i.1.idealSheaf.subscheme.Modules)
        (hL : Stacks.Ample.IsInvertibleModule i.1.idealSheaf.subscheme L),
        letI : Stacks.Ample.IsInvertibleModule i.1.idealSheaf.subscheme L := hL
        Stacks.Ample.IsAmple i.1.idealSheaf.subscheme L :=
    ⟨inferInstance, _, inferInstance, hamp⟩
  have hproj : IsProjectiveMorphism (i.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ))) :=
    (htf.out 5 2).mp h5
  have hpv : Mori.IsProjectiveVariety ℂ (i.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) :=
    { toIsVariety := hv, isProjective := hproj }
  refine MMP.Threefold.isNumericallyTrivial_of_divisorClass_eq_zero hpv (hB.1 i.1 i.2) (hE3 i) _
    (fun S hS => ?_) (fun S _ => MMP.Intersection.IsWeilDivisorOfCartier.isCartier (hπ i S)) h0
  obtain ⟨σ, h, rfl⟩ := exists_rhoOf_eq_of_mem_support hB a i.1 S hS
  exact isSmoothScheme_rhoOf hB σ h

end Glue

/-! ### Krull dimension of irreducible spaces -/

section Step1a

/-- In an irreducible quasi-sober `T₀` space of dimension at most one, a closed irreducible subset
is the whole space or a point. -/
private theorem eq_univ_or_eq_singleton_of_topologicalKrullDim_le_one {Y : Type*} [TopologicalSpace Y]
    [IrreducibleSpace Y] [QuasiSober Y] [T0Space Y] (hY : topologicalKrullDim Y ≤ 1)
    {T : Set Y} (hTi : IsIrreducible T) (hTc : IsClosed T) :
    T = Set.univ ∨ ∃ x, T = {x} := by
  by_cases hT : T = Set.univ
  · exact Or.inl hT
  right
  set η := hTi.genericPoint
  have hη : closure ({η} : Set Y) = T := by
    have := hTi.isGenericPoint_genericPoint_closure
    rwa [hTc.closure_eq] at this
  refine ⟨η, Set.eq_singleton_iff_unique_mem.2 ⟨hη ▸ subset_closure rfl, fun x hx => ?_⟩⟩
  by_contra hxη
  have hlt1 : closure ({x} : Set Y) ⊂ T := by
    refine HasSubset.Subset.ssubset_of_ne (closure_minimal (by simpa using hx) hTc) fun h => hxη ?_
    rw [← hη] at h
    exact (inseparable_iff_closure_eq.2 h).eq
  let s0 : IrreducibleCloseds Y := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let s1 : IrreducibleCloseds Y := ⟨T, hTi, hTc⟩
  let s2 : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  let p : LTSeries (IrreducibleCloseds Y) := ⟨2, ![s0, s1, s2], fun i => by
    fin_cases i
    exacts [hlt1, Set.ssubset_univ_iff.2 hT]⟩
  unfold topologicalKrullDim at hY
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim p).trans hY
  exact absurd h2 (by decide)

/-- In a space of dimension at most zero, no irreducible closed set strictly contains another. -/
private theorem not_lt_of_topologicalKrullDim_le_zero {Y : Type*} [TopologicalSpace Y]
    (hY : topologicalKrullDim Y ≤ 0) {s t : IrreducibleCloseds Y} : ¬ s < t :=
  (Order.krullDim_nonpos_iff_forall_isMin.1 hY t).not_lt

/-- An irreducible quasi-sober `T₀` space of dimension at most zero is a point. -/
private theorem subsingleton_of_topologicalKrullDim_le_zero {Y : Type*} [TopologicalSpace Y]
    [IrreducibleSpace Y] [QuasiSober Y] [T0Space Y] (hY : topologicalKrullDim Y ≤ 0) :
    Subsingleton Y := by
  set η := genericPoint Y
  suffices h : ∀ x : Y, x = η from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  by_contra hxη
  have hlt : closure ({x} : Set Y) ⊂ Set.univ := by
    refine Set.ssubset_univ_iff.2 fun h => hxη ?_
    rw [← (genericPoint_spec Y : closure ({η} : Set Y) = Set.univ)] at h
    exact (inseparable_iff_closure_eq.2 h).eq
  exact not_lt_of_topologicalKrullDim_le_zero hY
    (s := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (t := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩) hlt

end Step1a

/-! ### The pull-back of an ample sheaf from the image curve -/

section Step1b

variable {Z X : Scheme.{0}}

private theorem range_surfI_comp (f : Z ⟶ X) (S : Set Z) :
    Set.range ((surfI S).subschemeι ≫ f) = f.base '' closure S := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (surfI S).range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]

private theorem ker_le_gS (f : Z ⟶ X) (S : Set Z) :
    (surfI (f.base '' S)).subschemeι.ker ≤ ((surfI S).subschemeι ≫ f).ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 ?_
  change ((Closeds.closure _ : Closeds X) : Set X) ⊆ ((surfI (f.base '' S)).support : Set X)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, Closeds.coe_closure,
    range_surfI_comp]
  exact closure_minimal (image_closure_subset_closure_image f.continuous) isClosed_closure

/-- The map from the reduced surface on `S` onto the reduced image `f(S)`. -/
private noncomputable def gS (f : Z ⟶ X) (S : Set Z) :
    (surfI S).subscheme ⟶ (surfI (f.base '' S)).subscheme :=
  IsClosedImmersion.lift (surfI (f.base '' S)).subschemeι ((surfI S).subschemeι ≫ f)
    (ker_le_gS f S)

private theorem gS_fac (f : Z ⟶ X) (S : Set Z) :
    gS f S ≫ (surfI (f.base '' S)).subschemeι = (surfI S).subschemeι ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

private theorem surjective_gS (f : Z ⟶ X) (hf : IsClosedMap f.base) (S : Set Z) :
    Function.Surjective (gS f S).base := by
  intro c
  have hc : (surfI (f.base '' S)).subschemeι c ∈ closure (f.base '' S) := by
    have : (surfI (f.base '' S)).subschemeι c ∈ Set.range (surfI (f.base '' S)).subschemeι :=
      ⟨c, rfl⟩
    rwa [(surfI _).range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure] at this
  have hcl : closure (f.base '' S) ⊆ f.base '' closure S :=
    closure_minimal (Set.image_mono subset_closure) (hf _ isClosed_closure)
  obtain ⟨s, hs⟩ : (surfI (f.base '' S)).subschemeι c ∈ Set.range ((surfI S).subschemeι ≫ f) := by
    rw [range_surfI_comp]; exact hcl hc
  refine ⟨s, (surfI (f.base '' S)).subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← hs, ← Scheme.Hom.comp_apply, gS_fac]

/-- The reduced subscheme on the closure of `C` is a noetherian, separated, integral scheme of
dimension one. -/
private def IsCurveSet (C : Set X) : Prop :=
  IsNoetherian (surfI C).subscheme ∧ IsIntegral (surfI C).subscheme ∧
    (surfI C).subscheme.IsSeparated ∧ topologicalKrullDim (surfI C).subscheme = 1

/-- The ample invertible sheaf chosen on a set satisfying `IsCurveSet`. -/
private noncomputable def chosenAmpleSheaf (C : Set X) (h : IsCurveSet C) :
    (surfI C).subscheme.Modules :=
  haveI := h.1; haveI := h.2.1; haveI := h.2.2.1
  (Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one _ h.2.2.2).choose

/-- An ample invertible sheaf on the reduced image curve, and `𝒪` otherwise. -/
private noncomputable def curveAmpleSheaf (C : Set X) : (surfI C).subscheme.Modules :=
  haveI := Classical.propDecidable (IsCurveSet C)
  if h : IsCurveSet C then chosenAmpleSheaf C h else SheafOfModules.unit _

private theorem curveAmpleSheaf_of_isCurveSet (C : Set X) (h : IsCurveSet C) :
    curveAmpleSheaf C = chosenAmpleSheaf C h := by
  unfold curveAmpleSheaf; exact dif_pos h

private theorem curveAmpleSheaf_of_not_isCurveSet (C : Set X) (h : ¬ IsCurveSet C) :
    curveAmpleSheaf C = SheafOfModules.unit _ := by
  unfold curveAmpleSheaf; exact dif_neg h

private theorem exists_isAmple_chosenAmpleSheaf (C : Set X) (h : IsCurveSet C) :
    ∃ hL : SheafOfModules.IsInvertible (surfI C).subscheme.presheaf
        (surfI C).subscheme.ringCatSheaf.2 (chosenAmpleSheaf C h),
      @Scheme.Modules.IsAmple (surfI C).subscheme (chosenAmpleSheaf C h) hL := by
  haveI := h.1; haveI := h.2.1; haveI := h.2.2.1
  exact (Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one _ h.2.2.2).choose_spec

private theorem isInvertible_curveAmpleSheaf (C : Set X) :
    SheafOfModules.IsInvertible (surfI C).subscheme.presheaf (surfI C).subscheme.ringCatSheaf.2
      (curveAmpleSheaf C) := by
  by_cases h : IsCurveSet C
  · rw [curveAmpleSheaf_of_isCurveSet C h]; exact (exists_isAmple_chosenAmpleSheaf C h).choose
  · rw [curveAmpleSheaf_of_not_isCurveSet C h]; infer_instance

private theorem exists_isAmple_curveAmpleSheaf (C : Set X) (h : IsCurveSet C) :
    ∃ hL : SheafOfModules.IsInvertible (surfI C).subscheme.presheaf
        (surfI C).subscheme.ringCatSheaf.2 (curveAmpleSheaf C),
      @Scheme.Modules.IsAmple (surfI C).subscheme (curveAmpleSheaf C) hL := by
  rw [curveAmpleSheaf_of_isCurveSet C h]
  exact exists_isAmple_chosenAmpleSheaf C h

/-- The family `𝓗¹_S = g_S^* M_{f(S)}`. -/
private noncomputable def famH (f : Z ⟶ X) (S : Set Z) : (surfI S).subscheme.Modules :=
  (Scheme.Modules.pullback (gS f S)).obj (curveAmpleSheaf (f.base '' S))

private theorem isInvertible_famH (f : Z ⟶ X) (S : Set Z) :
    SheafOfModules.IsInvertible (surfI S).subscheme.presheaf (surfI S).subscheme.ringCatSheaf.2
      (famH f S) :=
  haveI := isInvertible_curveAmpleSheaf (f.base '' S)
  isInvertible_pullback_obj _ _

end Step1b

/-! ### Positivity against the image curve -/

section Step1c

attribute [local instance] isInvertible_vecCons2

variable {Z X : Scheme.{0}}

/-- In a `T₀` space of dimension at most zero every point is closed. -/
private theorem isClosed_singleton_of_topologicalKrullDim_le_zero {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] (hY : topologicalKrullDim Y ≤ 0) (x : Y) : IsClosed ({x} : Set Y) := by
  by_contra hx
  have hne : closure ({x} : Set Y) ≠ {x} := fun h => hx (h ▸ isClosed_closure)
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure ({x} : Set Y), y ≠ x := by
    by_contra h
    push Not at h
    exact hne (Set.eq_singleton_iff_unique_mem.2 ⟨subset_closure rfl, h⟩)
  have hlt : closure ({y} : Set Y) ⊂ closure {x} := by
    refine HasSubset.Subset.ssubset_of_ne (closure_minimal (by simpa using hy) isClosed_closure)
      fun h => hyx (inseparable_iff_closure_eq.2 h).eq
  exact not_lt_of_topologicalKrullDim_le_zero hY
    (s := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩)
    (t := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩) hlt

/-- `𝓗¹_S` is trivial when `f(S)` is not an integral curve. -/
private noncomputable def famHIsoUnit (f : Z ⟶ X) (S : Set Z) (h : ¬ IsCurveSet (f.base '' S)) :
    famH f S ≅ SheafOfModules.unit _ :=
  (Scheme.Modules.pullback (gS f S)).mapIso (eqToIso (curveAmpleSheaf_of_not_isCurveSet _ h)) ≪≫
    Stacks.PicardTrivialOpenUFD.pullbackUnitIso (gS f S)

variable {k : Type} [Field k]

/-- The reduced image of `S` is proper over `k`. -/
private theorem isProper_surfI_image (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] [LocallyOfFiniteType sX] (f : Z ⟶ X) (hfs : f ≫ sX = sZ)
    (hf : IsClosedMap f.base) (S : Set Z) :
    IsProper ((surfI (f.base '' S)).subschemeι ≫ sX) := by
  have heq : gS f S ≫ (surfI (f.base '' S)).subschemeι ≫ sX = (surfI S).subschemeι ≫ sZ := by
    rw [← Category.assoc, gS_fac, Category.assoc, hfs]
  haveI : UniversallyClosed (gS f S ≫ (surfI (f.base '' S)).subschemeι ≫ sX) := by
    rw [heq]; infer_instance
  haveI : Surjective (gS f S) := ⟨surjective_gS f hf S⟩
  haveI : UniversallyClosed ((surfI (f.base '' S)).subschemeι ≫ sX) :=
    UniversallyClosed.of_comp_surjective (gS f S) _
  exact ⟨⟩

/-- The pull-back along `gS f S` of a nonempty closed subscheme of the image curve is
nonempty. -/
private theorem nonempty_comap_gS_subscheme (f : Z ⟶ X) (hf : IsClosedMap f.base) (S : Set Z)
    (P : (surfI (f.base '' S)).subscheme.IdealSheafData) [hPne : Nonempty P.subscheme] :
    Nonempty (P.comap (gS f S)).subscheme := by
  obtain ⟨p⟩ := hPne
  obtain ⟨s, hs⟩ := surjective_gS f hf S (P.subschemeι p)
  have hsP : s ∈ (((P.comap (gS f S)).support : Closeds _) : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]
    change (gS f S) s ∈ (P.support : Set _)
    rw [hs, ← P.range_subschemeι]
    exact ⟨p, rfl⟩
  rw [← (P.comap (gS f S)).range_subschemeι] at hsP
  exact ⟨hsP.choose⟩

/-- An integral closed subscheme of `S` lying over a zero-dimensional closed subscheme of the image
curve is mapped by `f` to a single point. -/
private theorem exists_eq_of_support_le_comap_gS (f : Z ⟶ X) (S : Set Z)
    {P : (surfI (f.base '' S)).subscheme.IdealSheafData}
    (hPdim : topologicalKrullDim P.subscheme = ((0 : ℕ) : WithBot ℕ∞))
    (V : (surfI S).subscheme.IdealSheafData) (hVi : IsIntegral V.subscheme)
    (hVsub : (V.support : Set (surfI S).subscheme) ⊆ (P.comap (gS f S)).support) :
    ∃ y, ∀ w : V.subscheme, f ((V.subschemeι ≫ (surfI S).subschemeι) w) = y := by
  set I := (gS f S).base '' Set.range V.subschemeι with hI
  have hIirr : IsIrreducible I := by
    haveI := hVi
    have h1 : IsIrreducible (Set.range V.subschemeι) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ V.subschemeι.continuous.continuousOn
    exact h1.image _ (gS f S).continuous.continuousOn
  have hIP : I ⊆ (P.support : Set _) := by
    rintro _ ⟨v, ⟨w, rfl⟩, rfl⟩
    have hv : V.subschemeι w ∈ ((P.comap (gS f S)).support : Set _) := by
      apply hVsub
      rw [← V.range_subschemeι]
      exact ⟨w, rfl⟩
    rwa [Scheme.IdealSheafData.support_comap] at hv
  obtain ⟨η, hη⟩ := QuasiSober.sober hIirr.closure isClosed_closure
  have hηP : η ∈ (P.support : Set _) :=
    closure_minimal hIP P.support.isClosed (hη.mem)
  obtain ⟨p, rfl⟩ : η ∈ Set.range P.subschemeι := by rw [P.range_subschemeι]; exact hηP
  have hpcl : IsClosed ({P.subschemeι p} : Set _) := by
    rw [← Set.image_singleton]
    exact P.subschemeι.isClosedEmbedding.isClosedMap _
      (isClosed_singleton_of_topologicalKrullDim_le_zero (hPdim ▸ le_rfl) p)
  have hIsub : I ⊆ {P.subschemeι p} := by
    have := hη.def
    rw [hpcl.closure_eq] at this
    exact this ▸ subset_closure
  refine ⟨(surfI (f.base '' S)).subschemeι (P.subschemeι p), fun w => ?_⟩
  have hmem : (gS f S) (V.subschemeι w) ∈ I := ⟨_, ⟨w, rfl⟩, rfl⟩
  have h1 : (gS f S) (V.subschemeι w) = P.subschemeι p := hIsub hmem
  have h2 : (surfI (f.base '' S)).subschemeι ((gS f S) (V.subschemeι w)) =
      f ((surfI S).subschemeι (V.subschemeι w)) := by
    rw [← Scheme.Hom.comp_apply, gS_fac, Scheme.Hom.comp_apply]
  rw [Scheme.Hom.comp_apply, ← h2, h1]

/-- **`(-c_D · 𝓗¹)_S > 0` on a surface mapping onto a curve.** -/
private theorem nsNum_famH_pos (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] [LocallyOfFiniteType sX] (f : Z ⟶ X) (hfs : f ≫ sX = sZ)
    (hf : IsClosedMap f.base)
    (D : Divisor Z) (hDc : (-D).IsCartier) (hamp : (-D).IsRelativelyAmple f hDc)
    (c : Z.CartierDivisor) (hcw : MMP.Intersection.IsWeilDivisorOfCartier (-c) (-D))
    (S : Set Z) [IsIntegral (surfI S).subscheme]
    (hS : topologicalKrullDim (surfI S).subscheme = (2 : ℕ)) (hC : IsCurveSet (f.base '' S)) :
    0 < nsNum sZ (famH f) (isInvertible_famH f) S (-c) := by
  haveI := hC.2.1
  obtain ⟨hL, hampM⟩ := exists_isAmple_curveAmpleSheaf (f.base '' S) hC
  haveI := hL
  haveI := isProper_surfI_image sZ sX f hfs hf S
  have hposdim : 0 < topologicalKrullDim (surfI (f.base '' S)).subscheme := by
    rw [hC.2.2.2]; exact zero_lt_one
  obtain ⟨n, P, hn, hP, hPne, ⟨e₀⟩⟩ := exists_effectiveCartierDivisor_tensorPower_of_isAmple k
    ((surfI (f.base '' S)).subschemeι ≫ sX) hposdim (curveAmpleSheaf (f.base '' S)) hampM
  haveI := hPne
  haveI : IsDominant (gS f S) := ⟨(surjective_gS f hf S).denseRange⟩
  have hpd : Stacks.Divisors.IsPullbackDefined (gS f S) P :=
    Stacks.Divisors.isPullbackDefined_of_isDominant (gS f S) P hP
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (P.comap (gS f S)) := hpd
  haveI := nonempty_comap_gS_subscheme f hf S P
  haveI : SheafOfModules.IsInvertible (surfI S).subscheme.toRingedSpace.presheaf
      (structureSheafRing (surfI S).subscheme.toRingedSpace).property (famH f S) :=
    isInvertible_famH f S
  haveI : SheafOfModules.IsInvertible (surfI S).subscheme.toRingedSpace.presheaf
      (structureSheafRing (surfI S).subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback (𝟙 _)).obj (famH f S)) :=
    isInvertible_pullback_obj _ _
  haveI : SheafOfModules.IsInvertible (surfI (f.base '' S)).subscheme.toRingedSpace.presheaf
      (structureSheafRing (surfI (f.base '' S)).subscheme.toRingedSpace).property
      (curveAmpleSheaf (f.base '' S)) := hL
  let e : ((Scheme.Modules.pullback (𝟙 _)).obj (famH f S)).tensorPowerModules (n : ℤ) ≅
      Stacks.Divisors.invertibleSheaf (P.comap (gS f S)) :=
    (Scheme.Modules.pullbackTensorPowerIso (𝟙 _) (famH f S) n).symm ≪≫
      (Scheme.Modules.pullbackId _).app _ ≪≫
      (Scheme.Modules.pullbackTensorPowerIso (gS f S) (curveAmpleSheaf (f.base '' S)) n).symm ≪≫
      (Scheme.Modules.pullback (gS f S)).mapIso e₀ ≪≫
      Stacks.Divisors.invertibleSheafPullbackIso (gS f S) P
  refine nsNum_pos_of_cut sZ f D hDc hamp c hcw (famH f) (isInvertible_famH f) S hS n hn _ e
    (fun V hVi hVsub => ?_)
  exact exists_eq_of_support_le_comap_gS f S
    (topologicalKrullDim_subscheme_of_isEffectiveCartierDivisor k
      ((surfI (f.base '' S)).subschemeι ≫ sX) P hP (by rw [hC.2.2.2]; rfl)) V hVi hVsub

end Step1c

/-! ### Triple curves -/

section Step1d

attribute [local instance] isInvertible_vecCons2

private theorem isIrreducible_preimage_val {Y : Type*} [TopologicalSpace Y] {C T : Set Y}
    (hT : IsIrreducible T) (hTC : T ⊆ C) : IsIrreducible ((↑) ⁻¹' T : Set C) := by
  obtain ⟨x, hx⟩ := hT.nonempty
  refine ⟨⟨⟨x, hTC hx⟩, hx⟩, fun u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩ => ?_⟩
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hu
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hv
  obtain ⟨z, hzT, hzU, hzV⟩ := hT.2 U V hU hV ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨z, hTC hzT⟩, hzT, hzU, hzV⟩

/-- **A closed irreducible subset of an irreducible closed set of dimension at most one** is the
whole set or a point. -/
private theorem eq_or_eq_singleton_of_subset {Y : Type*} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    {C T : Set Y} (hC : IsIrreducible C) (hCc : IsClosed C) (hdim : topologicalKrullDim C ≤ 1)
    (hT : IsIrreducible T) (hTc : IsClosed T) (hTC : T ⊆ C) : T = C ∨ ∃ x, T = {x} := by
  haveI : IrreducibleSpace C := Subtype.irreducibleSpace hC
  haveI : QuasiSober C := hCc.isClosedEmbedding_subtypeVal.quasiSober
  rcases eq_univ_or_eq_singleton_of_topologicalKrullDim_le_one hdim
    (isIrreducible_preimage_val hT hTC) (hTc.preimage continuous_subtype_val) with h | ⟨x, hx⟩
  · left
    refine subset_antisymm hTC fun c hc => ?_
    have : (⟨c, hc⟩ : C) ∈ ((↑) ⁻¹' T : Set C) := h ▸ Set.mem_univ _
    exact this
  · right
    refine ⟨x.1, Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun y hy => ?_⟩⟩
    · have : x ∈ ((↑) ⁻¹' T : Set C) := hx ▸ rfl
      exact this
    · have : (⟨y, hTC hy⟩ : C) ∈ ((↑) ⁻¹' T : Set C) := hy
      rw [hx] at this
      exact congrArg Subtype.val this

variable {k : Type} [Field k] {Z : Scheme.{0}}

/-- On `ρ(σ)`, the trace of a third component is cut out by regular parameters. -/
private theorem stalk_param_eps_comap {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z}
    (hB : B.IsSNC sZ) (σ : DoubleSurface B) (l : B.support) (hl₁ : l ≠ fstS σ)
    (hl₂ : l ≠ sndS σ) :
    ∀ y ∈ ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).comap
      (rho hB σ).idealSheaf.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → (rho hB σ).idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).comap
          (rho hB σ).idealSheaf.subschemeι) y = Ideal.span {w j} := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion σ.fst.idealSheaf.subschemeι
  have := (rho hB σ).integral
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι) :=
    (isEffectiveCartierDivisor_comap_component hB hl₁).1
  have hsnc : MMP.Resolution.HasSNCWith
      (fun _ : Unit => l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι)
      (rho hB σ).idealSheaf :=
    hasSNCWith_rhoOf hB (fstS σ) σ rfl _ l hl₁ fun x hx => ⟨hx, rfl⟩
  have hPl : ¬ ((rho hB σ).support : Set _) ⊆
      ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).support : Set _) := by
    intro hsub
    refine not_carrier_subset_support hB σ l hl₁ hl₂ ?_
    rw [← image_support_rho hB σ]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ((l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).support : Set _) := hsub hy
    rw [Scheme.IdealSheafData.support_comap] at hy'
    exact hy'
  intro y hy
  obtain ⟨m, w, c', hw, hc, -⟩ :=
    MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hsnc
      (fun _ => not_component_subset_of_not_support_subset (rho hB σ) _ hPl) y
  exact ⟨m, w, c' ⟨(), hy⟩, hw, hc ⟨(), hy⟩⟩

/-- **Triple curves are irreducible.** -/
private theorem isIrreducible_of_mem_tcs {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] [NoetherianSpace Z]
    {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) (l : B.support) (hl₁ : l ≠ fstS σ)
    (hl₂ : l ≠ sndS σ) (T : Set Z) (hT : T ∈ tcs σ.fst σ.snd l.1) (hTS : T ⊆ σ.carrier) :
    IsIrreducible T := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion σ.fst.idealSheaf.subschemeι
  have : IsLocallyNoetherian (rho hB σ).idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (rho hB σ).idealSheaf.subschemeι
  have : NoetherianSpace (rho hB σ).idealSheaf.subscheme :=
    ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι).isClosedEmbedding.isEmbedding.noetherianSpace
  have hTt := mem_tcs.1 hT
  obtain ⟨-, hTsub, x, hx, hxT⟩ := hTt
  have hxT' : x ∈ T := hxT ▸ mem_connectedComponentIn hx
  set emb := (rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι
  have hrange : Set.range emb = σ.carrier := range_comp_rho hB σ
  obtain ⟨y, hy⟩ : x ∈ Set.range emb := hrange ▸ hTS hxT'
  set G := (l.1.idealSheaf.comap σ.fst.idealSheaf.subschemeι).comap
    (rho hB σ).idealSheaf.subschemeι
  have hGs : (G.support : Set _) = emb ⁻¹' l.1.support := by
    ext z
    simp only [G, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      SetLike.mem_coe]
    rfl
  have hyG : y ∈ (G.support : Set _) := by
    rw [hGs, Set.mem_preimage, hy]; exact hx.2
  have hirr := MMP.Mori.isIrreducible_connectedComponentIn_support_of_stalk_eq_span_parameter G
    (stalk_param_eps_comap hB σ l hl₁ hl₂) hyG
  have himg := MMP.Mori.image_connectedComponentIn_of_isEmbedding emb.isClosedEmbedding.isEmbedding
    hyG
  have hGimg : emb '' (G.support : Set _) = l.1.support ∩ σ.carrier := by
    rw [hGs, Set.image_preimage_eq_inter_range, hrange]
  rw [hGimg, hy] at himg
  have hTeq : connectedComponentIn (l.1.support ∩ σ.carrier) x = T := by
    apply subset_antisymm
    · rw [← hxT]
      refine connectedComponentIn_mono _ fun z hz => ?_
      exact ⟨σ.carrier_subset hz.2, hz.1⟩
    · exact (IsTripleCurve.isPreconnected (mem_tcs.1 hT)).subset_connectedComponentIn hxT'
        fun z hz => ⟨(hTsub hz).2, hTS hz⟩
  rw [← hTeq, ← himg]
  exact hirr.image _ emb.continuous.continuousOn

end Step1d

/-! ### Restriction of the family to the triple curves -/

section Step1e

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z X : Scheme.{0}}

/-- The degree of `𝓗¹_T` on the reduced curve `T`. -/
private noncomputable def oneNum (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (f : Z ⟶ X) (T : Set Z) : ℚ := by
  classical
  haveI := isInvertible_famH f T
  exact if h : topologicalKrullDim (surfI T).subscheme ≤ (1 : ℕ) then
    (sheafIntersectionNumber k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 h (fun _ => famH f T) : ℚ)
  else 0

private theorem ker_le_of_closure_subset {Y : Scheme.{0}} {S T : Set Y} (h : closure T ⊆ closure S) :
    (surfI S).subschemeι.ker ≤ (surfI T).subschemeι.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 ?_
  change ((Closeds.closure T : Closeds Y) : Set Y) ⊆ ((surfI S).support : Set Y)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, Closeds.coe_closure]
  exact h

/-- The inclusion of reduced subschemes `T ⊆ S`. -/
private noncomputable def incl {Y : Scheme.{0}} (S T : Set Y) (h : closure T ⊆ closure S) :
    (surfI T).subscheme ⟶ (surfI S).subscheme :=
  IsClosedImmersion.lift (surfI S).subschemeι (surfI T).subschemeι (ker_le_of_closure_subset h)

private theorem incl_fac {Y : Scheme.{0}} (S T : Set Y) (h : closure T ⊆ closure S) :
    incl S T h ≫ (surfI S).subschemeι = (surfI T).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

private theorem isClosedImmersion_incl {Y : Scheme.{0}} (S T : Set Y) (h : closure T ⊆ closure S) :
    IsClosedImmersion (incl S T h) := by
  have : IsClosedImmersion (incl S T h ≫ (surfI S).subschemeι) := by
    rw [incl_fac]; infer_instance
  exact IsClosedImmersion.of_comp _ (surfI S).subschemeι

/-- `cNum` read on the reduced curve itself. -/
private theorem cNum_eq_incl (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
    (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
      (surfI S).subscheme.ringCatSheaf.2 (𝓗 S))
    (S T : Set Z) (hTS : closure T ⊆ closure S)
    (hT1 : topologicalKrullDim (surfI T).subscheme ≤ (1 : ℕ)) :
    haveI := h𝓗 S
    cNum sZ 𝓗 h𝓗 S T = (sheafIntersectionNumber k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 hT1
      (fun _ => (Scheme.Modules.pullback (incl S T hTS)).obj (𝓗 S)) : ℚ) := by
  haveI := h𝓗 S
  haveI := isClosedImmersion_incl S T hTS
  have hker := ker_curveClosedsS_eq S T hTS
  have hd : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subscheme ≤ (1 : ℕ) := by
    have := IsClosedImmersion.isIso_lift _ _ hker.symm
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift _ _ hker.symm.le))).isHomeomorph]
    exact hT1
  haveI := IsClosedImmersion.isIso_lift (surfI T).subschemeι
    ((Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subschemeι ≫ (surfI S).subschemeι)
    hker.symm
  let e := asIso (IsClosedImmersion.lift (surfI T).subschemeι
    ((Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subschemeι ≫ (surfI S).subschemeι)
    hker.symm.le)
  have he : e.hom ≫ incl S T hTS =
      (Scheme.IdealSheafData.vanishingIdeal (curveClosedsS S T)).subschemeι := by
    rw [← cancel_mono (surfI S).subschemeι, Category.assoc, incl_fac]
    exact IsClosedImmersion.lift_fac _ _ _
  rw [cNum, dif_pos hd, sheafIntersectionNumber_eq_of_iso k _ _ (incl S T hTS) e he 1 hd hT1,
    sheafIntersectionNumber_congr_hom k _ (Category.id_comp (incl S T hTS)).symm 1 hT1,
    sheafIntersectionNumber_comp_eq_of_iso k _ (incl S T hTS) (𝟙 _) 1 hT1 _ _
      (fun _ => Iso.refl _)]
  congr 1
  exact sheafIntersectionNumber_congr_base (by rw [← Category.assoc, incl_fac]) _ _ _ _

/-- The inclusion of the reduced images. -/
private noncomputable def kap (f : Z ⟶ X) (S T : Set Z) (h : T ⊆ S) :
    (surfI (f.base '' T)).subscheme ⟶ (surfI (f.base '' S)).subscheme :=
  incl (f.base '' S) (f.base '' T) (closure_mono (Set.image_mono h))

private theorem incl_gS (f : Z ⟶ X) (S T : Set Z) (h : T ⊆ S) (hTS : closure T ⊆ closure S) :
    incl S T hTS ≫ gS f S = gS f T ≫ kap f S T h := by
  rw [← cancel_mono (surfI (f.base '' S)).subschemeι, Category.assoc, gS_fac, ← Category.assoc,
    incl_fac, Category.assoc, kap, incl_fac, gS_fac]

/-- `j_T^* 𝓗¹_S ≅ g_T^* κ^* M_{f(S)}`. -/
private noncomputable def inclFamHIso (f : Z ⟶ X) (S T : Set Z) (h : T ⊆ S)
    (hTS : closure T ⊆ closure S) :
    (Scheme.Modules.pullback (incl S T hTS)).obj (famH f S) ≅
      (Scheme.Modules.pullback (gS f T)).obj
        ((Scheme.Modules.pullback (kap f S T h)).obj (curveAmpleSheaf (f.base '' S))) :=
  (Scheme.Modules.pullbackComp (incl S T hTS) (gS f S)).app _ ≪≫
    eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj (curveAmpleSheaf (f.base '' S)))
      (incl_gS f S T h hTS)) ≪≫
    ((Scheme.Modules.pullbackComp (gS f T) (kap f S T h)).app _).symm

private theorem nonempty_pullback_curveAmpleSheaf_iso {Y : Scheme.{0}} (C₁ C₂ : Set Y) (h : C₁ = C₂)
    (κ : (surfI C₁).subscheme ⟶ (surfI C₂).subscheme)
    (hκ : κ ≫ (surfI C₂).subschemeι = (surfI C₁).subschemeι) :
    Nonempty ((Scheme.Modules.pullback κ).obj (curveAmpleSheaf C₂) ≅ curveAmpleSheaf C₁) := by
  subst h
  have : κ = 𝟙 _ := by rw [← cancel_mono (surfI C₁).subschemeι, hκ, Category.id_comp]
  subst this
  exact ⟨(Scheme.Modules.pullbackId _).app _⟩

private theorem subsingleton_surfI_singleton {Y : Scheme.{0}} (x : Y) (hx : IsClosed ({x} : Set Y)) :
    Subsingleton (surfI ({x} : Set Y)).subscheme := by
  refine ⟨fun a b => (surfI ({x} : Set Y)).subschemeι.isClosedEmbedding.injective ?_⟩
  have hmem : ∀ c : (surfI ({x} : Set Y)).subscheme, (surfI ({x} : Set Y)).subschemeι c = x := by
    intro c
    have : (surfI ({x} : Set Y)).subschemeι c ∈ Set.range (surfI ({x} : Set Y)).subschemeι :=
      ⟨c, rfl⟩
    rwa [(surfI _).range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure, hx.closure_eq] at this
  rw [hmem a, hmem b]

end Step1e

/-! ### Compatibility and signs of the curve numbers -/

section Step1f

attribute [local instance] isInvertible_vecCons2

variable {k : Type} [Field k] {Z X : Scheme.{0}}

/-- One-slot intersection numbers only see the isomorphism class. -/
private theorem sheafIntersectionNumber_one_congr_iso {Y W : Scheme.{0}} (g : Y ⟶ Spec (.of k))
    [IsProper g] (i : W ⟶ Y) [IsClosedImmersion i] (hd : topologicalKrullDim W ≤ (1 : ℕ))
    (A B : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 B] (e : A ≅ B) :
    sheafIntersectionNumber k g i 1 hd (fun _ => A) = sheafIntersectionNumber k g i 1 hd (fun _ => B) := by
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  exact intersectionNumber_eq_of_iso_at k g i 1 hd _ _ 0 (fun q hq => absurd (Subsingleton.elim q 0) hq) e

private theorem subsingleton_surfI_of_eq {Y : Scheme.{0}} (C : Set Y) (x : Y) (h : C = {x})
    (hx : IsClosed ({x} : Set Y)) : Subsingleton (surfI C).subscheme := by
  subst h
  exact subsingleton_surfI_singleton x hx

/-- **Consistency of the triple-curve numbers for `𝓗¹`.** -/
private theorem cNum_famH_eq_oneNum (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (f : Z ⟶ X)
    (hf : IsClosedMap f.base) (S T : Set Z) (hScl : IsClosed S) (hSirr : IsIrreducible S)
    (hTcl : IsClosed T) (hTirr : IsIrreducible T) (hTS : T ⊆ S)
    (hdimS : topologicalKrullDim (f.base '' S) ≤ 1)
    (hT1 : topologicalKrullDim (surfI T).subscheme ≤ (1 : ℕ)) :
    cNum sZ (famH f) (isInvertible_famH f) S T = oneNum sZ f T := by
  have hTS' : closure T ⊆ closure S := closure_mono hTS
  haveI := isInvertible_famH f S
  haveI := isInvertible_famH f T
  haveI := isInvertible_curveAmpleSheaf (f.base '' S)
  haveI := isInvertible_curveAmpleSheaf (f.base '' T)
  haveI : SheafOfModules.IsInvertible (surfI T).subscheme.presheaf
      (surfI T).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (incl S T hTS')).obj (famH f S)) :=
    isInvertible_pullback_obj _ _
  have key : sheafIntersectionNumber k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 hT1
      (fun _ => (Scheme.Modules.pullback (incl S T hTS')).obj (famH f S)) =
      sheafIntersectionNumber k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 hT1 (fun _ => famH f T) := by
    rcases eq_or_eq_singleton_of_subset (hSirr.image _ f.continuous.continuousOn) (hf _ hScl)
      hdimS (hTirr.image _ f.continuous.continuousOn) (hf _ hTcl) (Set.image_mono hTS) with
      h | ⟨x, hx⟩
    · obtain ⟨e1⟩ := nonempty_pullback_curveAmpleSheaf_iso (f.base '' T) (f.base '' S) h
        (kap f S T hTS) (incl_fac _ _ _)
      have e2 : (Scheme.Modules.pullback (incl S T hTS')).obj (famH f S) ≅ famH f T :=
        inclFamHIso f S T hTS hTS' ≪≫ (Scheme.Modules.pullback (gS f T)).mapIso e1
      exact sheafIntersectionNumber_one_congr_iso _ _ hT1 _ _ e2
    · have hxcl : IsClosed ({x} : Set X) := hx ▸ hf _ hTcl
      haveI := subsingleton_surfI_of_eq (f.base '' T) x hx hxcl
      obtain ⟨t⟩ : Nonempty (surfI T).subscheme := by
        obtain ⟨z, hz⟩ := hTirr.nonempty
        have : z ∈ Set.range (surfI T).subschemeι := by
          rw [(surfI T).range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
            Closeds.coe_closure]
          exact subset_closure hz
        exact ⟨this.choose⟩
      haveI : SheafOfModules.IsInvertible (surfI (f.base '' T)).subscheme.presheaf
          (surfI (f.base '' T)).subscheme.ringCatSheaf.2
          ((Scheme.Modules.pullback (kap f S T hTS)).obj (curveAmpleSheaf (f.base '' S))) :=
        isInvertible_pullback_obj _ _
      obtain ⟨u1⟩ := nonempty_iso_unit_of_subsingleton
        ((Scheme.Modules.pullback (kap f S T hTS)).obj (curveAmpleSheaf (f.base '' S))) (gS f T t)
      obtain ⟨u2⟩ := nonempty_iso_unit_of_subsingleton (curveAmpleSheaf (f.base '' T)) (gS f T t)
      have e3 : (Scheme.Modules.pullback (incl S T hTS')).obj (famH f S) ≅
          SheafOfModules.unit _ :=
        inclFamHIso f S T hTS hTS' ≪≫ (Scheme.Modules.pullback (gS f T)).mapIso u1 ≪≫
          Stacks.PicardTrivialOpenUFD.pullbackUnitIso (gS f T)
      have e4 : famH f T ≅ SheafOfModules.unit _ :=
        (Scheme.Modules.pullback (gS f T)).mapIso u2 ≪≫
          Stacks.PicardTrivialOpenUFD.pullbackUnitIso (gS f T)
      rw [sheafIntersectionNumber_eq_zero_of_iso_unit k _ (𝟙 _) 1 hT1 _ 0 e3,
        sheafIntersectionNumber_eq_zero_of_iso_unit k _ (𝟙 _) 1 hT1 _ 0 e4]
  rw [cNum_eq_incl sZ (famH f) (isInvertible_famH f) S T hTS' hT1, oneNum, dif_pos hT1, key]

/-- **The triple-curve numbers of `𝓗¹` are nonnegative.** -/
private theorem oneNum_nonneg (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (sX : X ⟶ Spec (.of k))
    [IsSeparated sX] [LocallyOfFiniteType sX] (f : Z ⟶ X) (hfs : f ≫ sX = sZ)
    (hf : IsClosedMap f.base) (T : Set Z) [IsIntegral (surfI T).subscheme] :
    0 ≤ oneNum sZ f T := by
  haveI := isInvertible_famH f T
  unfold oneNum
  split_ifs with h1
  swap
  · exact le_rfl
  by_cases hC : IsCurveSet (f.base '' T)
  swap
  · rw [sheafIntersectionNumber_eq_zero_of_iso_unit k _ (𝟙 _) 1 h1 _ 0 (famHIsoUnit f T hC)]
    simp
  haveI := hC.2.1
  obtain ⟨hL, hampM⟩ := exists_isAmple_curveAmpleSheaf (f.base '' T) hC
  haveI := hL
  haveI := isProper_surfI_image sZ sX f hfs hf T
  have hposdim : 0 < topologicalKrullDim (surfI (f.base '' T)).subscheme := by
    rw [hC.2.2.2]; exact zero_lt_one
  obtain ⟨n, P, hn, hP, hPne, ⟨e₀⟩⟩ := exists_effectiveCartierDivisor_tensorPower_of_isAmple k
    ((surfI (f.base '' T)).subschemeι ≫ sX) hposdim (curveAmpleSheaf (f.base '' T)) hampM
  haveI : IsDominant (gS f T) := ⟨(surjective_gS f hf T).denseRange⟩
  have hpd : Stacks.Divisors.IsPullbackDefined (gS f T) P :=
    Stacks.Divisors.isPullbackDefined_of_isDominant (gS f T) P hP
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (P.comap (gS f T)) := hpd
  haveI : SheafOfModules.IsInvertible (surfI (f.base '' T)).subscheme.toRingedSpace.presheaf
      (structureSheafRing (surfI (f.base '' T)).subscheme.toRingedSpace).property
      (curveAmpleSheaf (f.base '' T)) := hL
  haveI : SheafOfModules.IsInvertible (surfI T).subscheme.toRingedSpace.presheaf
      (structureSheafRing (surfI T).subscheme.toRingedSpace).property (famH f T) :=
    isInvertible_famH f T
  set L : Fin 1 → (surfI T).subscheme.Modules := fun _ => famH f T with hL'
  haveI : ∀ q, SheafOfModules.IsInvertible (surfI T).subscheme.presheaf
      (surfI T).subscheme.ringCatSheaf.2 (Function.update L 0
        (Stacks.SheafOfModules.Invertible.tensorPower (surfI T).subscheme.presheaf
          (surfI T).subscheme.ringCatSheaf.2 (L 0) (n : ℤ)) q) :=
    isInvertible_update L 0 _
  have hNiso : (Scheme.Modules.pullback (𝟙 _)).obj (Function.update L 0
      (Stacks.SheafOfModules.Invertible.tensorPower (surfI T).subscheme.presheaf
        (surfI T).subscheme.ringCatSheaf.2 (L 0) (n : ℤ)) 0) ≅
      Stacks.Divisors.invertibleSheaf (P.comap (gS f T)) :=
    (Scheme.Modules.pullbackId _).app _ ≪≫ eqToIso (Function.update_self (0 : Fin 1) _ L) ≪≫
      (Scheme.Modules.pullbackTensorPowerIso (gS f T) (curveAmpleSheaf (f.base '' T)) n).symm ≪≫
      (Scheme.Modules.pullback (gS f T)).mapIso e₀ ≪≫
      Stacks.Divisors.invertibleSheafPullbackIso (gS f T) P
  have hmul := intersectionNumber_update_tensorPower k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 h1 L 0 n
  rw [intersectionNumber_eq_of_isEffectiveCartierDivisor' k _ (𝟙 _) 0 h1 _ (P.comap (gS f T))
    hNiso, intersectionNumber_zero_eq_finrank_globalSections] at hmul
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber]
  have hnn : (0 : ℤ) ≤ (n : ℤ) * intersectionNumber k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 h1 L := by
    rw [← hmul]; exact Int.natCast_nonneg _
  have : (0 : ℤ) ≤ intersectionNumber k ((surfI T).subschemeι ≫ sZ) (𝟙 _) 1 h1 L :=
    nonneg_of_mul_nonneg_right hnn (by exact_mod_cast (show 0 < n by omega))
  exact_mod_cast this

/-- `(-c · 𝓗¹)_S = 0` when `f(S)` is not an integral curve. -/
private theorem nsNum_famH_eq_zero (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (f : Z ⟶ X) (S : Set Z)
    (c : Z.CartierDivisor) (hC : ¬ IsCurveSet (f.base '' S)) :
    nsNum sZ (famH f) (isInvertible_famH f) S c = 0 := by
  haveI := isInvertible_famH f S
  unfold nsNum
  split_ifs with h
  · rw [sheafIntersectionNumber_eq_zero_of_iso_unit k _ (𝟙 _) 2 h _ 1 (famHIsoUnit f S hC)]
    simp
  · rfl

end Step1f

/-! ### No supported surface maps onto a curve -/

section Step1g

variable {k : Type} [Field k] {Z X : Scheme.{0}}

private theorem le_zero_of_le_one_of_ne_one {d : WithBot ℕ∞} (h1 : d ≤ 1) (h2 : d ≠ 1) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe m =>
    have hm : m ≤ 1 := by exact_mod_cast h1
    have hm' : m ≠ 1 := fun h => h2 (by rw [h]; rfl)
    have : m = 0 := ENat.lt_one_iff_eq_zero.1 (lt_of_le_of_ne hm hm')
    rw [this]; rfl

public theorem isIrreducible_carrier {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {D : Divisor Z}
    (hB : D.IsSNC sZ) (σ : DoubleSurface D) : IsIrreducible σ.carrier := by
  rw [← image_support_rho hB σ, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isIrreducible_singleton.closure.image _ σ.fst.idealSheaf.subschemeι.continuous.continuousOn

/-- **Step 1.** Every surface supporting `a` is contracted to a point. -/
private theorem exists_eq_of_mem_vertical (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ) (hZ : topologicalKrullDim Z = 4)
    [NoetherianSpace Z] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {D : Divisor Z} (hB : D.IsSNC sZ) [LinearOrder D.support]
    [Fintype (DoubleSurface D)] (hDpos : ∀ P ∈ D.support, 0 < D.coeff P)
    (a : DoubleSurface D → ℚ) (ha : a ∈ orientedSurfaceCoefficients D)
    (ε : D.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : D.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hE3 : ∀ i : D.support, topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ))
    (hX0 : ∀ (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
      (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
        (surfI S).subscheme.ringCatSheaf.2 (𝓗 S)) (i : D.support),
      (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ => cP * cQ * fxNum sZ 𝓗 h𝓗 π i P Q) = 0)
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    (f : Z ⟶ X) (hfs : f ≫ sX = sZ) (hf : IsClosedMap f.base)
    (hDc : (-D).IsCartier) (hamp : (-D).IsRelativelyAmple f hDc)
    (hcw : MMP.Intersection.IsWeilDivisorOfCartier (-∑ l : D.support, D.coeff l.1 • ε l) (-D))
    (hvert : ∀ σ : DoubleSurface D, a σ ≠ 0 → topologicalKrullDim (f.base '' σ.carrier) ≤ 1) :
    ∀ σ : DoubleSurface D, a σ ≠ 0 → ∃ y, ∀ z ∈ σ.carrier, f z = y := by
  have hT := topologicalKrullDim_tripleCurve_le k sZ hvar hZ hB
  have hzero := nsNum_eq_zero_of_family sZ hvar hsm hZ hB hDpos a ha ε hε π hπ (famH f)
    (isInvertible_famH f) (oneNum sZ f)
    (fun σ ha0 l hl₁ hl₂ T hTm hTS => cNum_famH_eq_oneNum sZ f hf σ.carrier T (isClosed_carrier σ)
      (isIrreducible_carrier hB σ) (mem_tcs.1 hTm).isClosed
      (isIrreducible_of_mem_tcs hB σ l hl₁ hl₂ T hTm hTS) hTS (hvert σ ha0)
      (dim_le_one_of_ne hT (fun e => σ.fst_ne_snd (congrArg Subtype.val e)) hl₁.symm hl₂.symm
        (mem_tcs.1 hTm).2.1))
    (fun i j l hij hjl T hTm => by
      have hTt := mem_tcs.1 hTm
      have hne : i.1 ≠ j.1 := fun e => hij.ne (Subtype.ext e)
      have hTE : T ⊆ i.1.support ∩ j.1.support := fun z hz => (hTt.2.1 hz).1
      have hsub : T ⊆ (DoubleSurface.through i.2 j.2 hne hTt.1 hTE).carrier :=
        DoubleSurface.subset_through i.2 j.2 hne hTt.1 hTE hTt.isPreconnected
      have hirr := isIrreducible_of_mem_tcs hB (DoubleSurface.through i.2 j.2 hne hTt.1 hTE) l
        (hij.trans hjl).ne' hjl.ne' T hTm hsub
      haveI : IsIntegral (surfI T).subscheme :=
        StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible (Closeds.closure T)
          hirr.closure
      exact oneNum_nonneg sZ sX f hfs hf T)
    (hX0 _ _)
    (fun σ _ => by
      by_cases hC : IsCurveSet (f.base '' σ.carrier)
      · haveI := isIntegral_surfI hB σ
        exact (nsNum_famH_pos sZ sX f hfs hf D hDc hamp _ hcw σ.carrier (dim_surfI_eq hB hE3 σ)
          hC).le
      · rw [nsNum_famH_eq_zero sZ f σ.carrier _ hC])
  intro σ ha0
  have hnc : ¬ IsCurveSet (f.base '' σ.carrier) := fun hC => by
    haveI := isIntegral_surfI hB σ
    have := nsNum_famH_pos sZ sX f hfs hf D hDc hamp _ hcw σ.carrier (dim_surfI_eq hB hE3 σ) hC
    rw [hzero σ ha0] at this
    exact lt_irrefl _ this
  have hCcl : IsClosed (f.base '' σ.carrier) := hf _ (isClosed_carrier σ)
  have hCirr : IsIrreducible (f.base '' σ.carrier) :=
    (isIrreducible_carrier hB σ).image _ f.continuous.continuousOn
  haveI hCint : IsIntegral (surfI (f.base '' σ.carrier)).subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hCirr.closure
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsLocallyNoetherian (surfI (f.base '' σ.carrier)).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (surfI (f.base '' σ.carrier)).subschemeι
  haveI : CompactSpace (surfI (f.base '' σ.carrier)).subscheme :=
    (surfI (f.base '' σ.carrier)).subschemeι.isClosedEmbedding.compactSpace
  haveI hCnoeth : IsNoetherian (surfI (f.base '' σ.carrier)).subscheme := ⟨⟩
  haveI hCsep : (surfI (f.base '' σ.carrier)).subscheme.IsSeparated :=
    Scheme.IsSeparated.of_isSeparated ((surfI (f.base '' σ.carrier)).subschemeι ≫ sX)
  have hmemC : ∀ c, (surfI (f.base '' σ.carrier)).subschemeι c ∈ f.base '' σ.carrier := by
    intro c
    have : (surfI (f.base '' σ.carrier)).subschemeι c ∈
        Set.range (surfI (f.base '' σ.carrier)).subschemeι := ⟨c, rfl⟩
    rwa [(surfI _).range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure, hCcl.closure_eq] at this
  have hdle : topologicalKrullDim (surfI (f.base '' σ.carrier)).subscheme ≤ 1 :=
    ((surfI (f.base '' σ.carrier)).subschemeι.isClosedEmbedding.isInducing.codRestrict
      hmemC).topologicalKrullDim_le.trans (hvert σ ha0)
  have hd0 : topologicalKrullDim (surfI (f.base '' σ.carrier)).subscheme ≤ 0 :=
    le_zero_of_le_one_of_ne_one hdle fun h => hnc ⟨hCnoeth, hCint, hCsep, h⟩
  haveI : Subsingleton (surfI (f.base '' σ.carrier)).subscheme :=
    subsingleton_of_topologicalKrullDim_le_zero hd0
  obtain ⟨z0, hz0⟩ := σ.carrier_nonempty
  have hrange : ∀ z ∈ σ.carrier, f z ∈ Set.range (surfI (f.base '' σ.carrier)).subschemeι := by
    intro z hz
    rw [(surfI _).range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure]
    exact subset_closure ⟨z, hz, rfl⟩
  refine ⟨f z0, fun z hz => ?_⟩
  obtain ⟨c, hc⟩ := hrange z hz
  obtain ⟨c0, hc0⟩ := hrange z0 hz0
  rw [← hc, ← hc0, Subsingleton.elim c c0]

end Step1g

end MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity

@[expose] public section

namespace MMP.Fourfold

open MMP.Mori
open MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity

attribute [local instance] isIso_phi

/-- **Injectivity on contracted edges.** Let `f : Z ⟶ X` be a projective birational morphism
from a smooth projective complex fourfold to a normal variety, and `D` a divisor on `Z`,
positive on its support, whose support is snc and such that `-D` is Cartier and `f`-ample. An
oriented coefficient system `a` on the double surfaces of `D`, supported on surfaces whose image
in `X` has dimension at most one, with every class `[Zᵢ(a)]` zero in `H_4(Bᵢ, ℚ)`, is zero. -/
@[mmp "lem_mmp_conductor_contracted_edge_injectivity"]
public theorem eq_zero_of_mem_verticalSurfaceCoefficients_of_surfaceCoefficientClasses_eq_zero
    {Z X : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (f : Z ⟶ X)
    (hcomp : f ≫ sX = Z ↘ Spec (.of ℂ))
    (hf : MMP.Intersection.IsResolution sX f)
    (hZ : IsProjective (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
    (D : Divisor Z) (hsnc : DivisorWithCoeffs.IsSNC (Z ↘ Spec (.of ℂ)) D)
    (hDpos : ∀ P ∈ D.support, 0 < D.coeff P)
    (hA : ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple f h)
    {a : DoubleSurface D → ℚ} (ha : a ∈ verticalSurfaceCoefficients f D)
    (h0 : surfaceCoefficientClasses D a = 0) :
    a = 0 := by
  classical
  obtain ⟨hvarX, hvarZ, hsmZ, hprojf, hbir⟩ := hf
  rw [hcomp] at hvarZ hsmZ
  haveI : IsIntegral Z := hvarZ.toIsIntegral
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := hZ.isProper
  haveI : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  letI : LinearOrder D.support :=
    LinearOrder.lift' (Fintype.equivFin D.support) (Fintype.equivFin D.support).injective
  haveI : Finite (DoubleSurface D) := DoubleSurface.finite
  letI : Fintype (DoubleSurface D) := Fintype.ofFinite _
  choose ε hε using fun i : D.support =>
    exists_isWeilDivisorOfCartier_of_isSmoothScheme hsmZ (Finsupp.single i.1 (1 : ℤ))
  have hπex : ∀ (i : D.support) (P : Mori.PrimeDivisor i.1.idealSheaf.subscheme),
      ∃ c : i.1.idealSheaf.subscheme.CartierDivisor,
        MMP.Intersection.IsWeilDivisorOfCartier c (Finsupp.single P 1) := fun i P => by
    haveI := i.1.integral
    exact exists_isWeilDivisorOfCartier_of_isSmoothScheme (hsnc.1 i.1 i.2) _
  choose π hπ using hπex
  have htfZ := isProjective_tfae_seven_of_exists_isAmple (Z ↘ Spec (.of ℂ))
    ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  obtain ⟨-, A, hAi, hAamp⟩ := (htfZ.out 1 5).mp hZ
  haveI := hAi
  haveI : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 A := hAi
  have hE3 := dim_component_eq hvarZ hsmZ hdim ε hε
  have hX0 : ∀ (𝓗 : ∀ S : Set Z, (surfI S).subscheme.Modules)
      (h𝓗 : ∀ S, SheafOfModules.IsInvertible (surfI S).subscheme.presheaf
        (surfI S).subscheme.ringCatSheaf.2 (𝓗 S)) (i : D.support),
      (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ =>
          cP * cQ * fxNum (Z ↘ Spec (.of ℂ)) 𝓗 h𝓗 π i P Q) = 0 := by
    intro 𝓗 h𝓗 i
    haveI := i.1.integral
    haveI : IsLocallyNoetherian i.1.idealSheaf.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion i.1.idealSheaf.subschemeι
    haveI : IsNormal i.1.idealSheaf.subscheme := isNormal_of_isRegular _
      (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme (hsnc.1 i.1 i.2))
    haveI : CompactSpace i.1.idealSheaf.subscheme :=
      i.1.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
    have hNT := isNumericallyTrivial_surfaceCoefficientDivisor hvarZ hsnc π hπ A hAamp hE3 a i
      (by rw [← surfaceCoefficientClasses_apply, h0]; rfl)
    rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun P _ => ?_
    have := sum_mul_fxNum_eq_zero (Z ↘ Spec (.of ℂ)) π hπ 𝓗 h𝓗 i _ hNT P
    rw [Finsupp.sum] at this ⊢
    rw [show ∑ Q ∈ (surfaceCoefficientDivisor a i.1).support,
        (surfaceCoefficientDivisor a i.1) P * (surfaceCoefficientDivisor a i.1) Q *
          fxNum (Z ↘ Spec (.of ℂ)) 𝓗 h𝓗 π i P Q =
        (surfaceCoefficientDivisor a i.1) P * ∑ Q ∈ (surfaceCoefficientDivisor a i.1).support,
          (surfaceCoefficientDivisor a i.1) Q * fxNum (Z ↘ Spec (.of ℂ)) 𝓗 h𝓗 π i P Q by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun Q _ => by ring, this, mul_zero]
  have hDsum : D = ∑ l : D.support, D.coeff l.1 • Finsupp.single l.1 (1 : ℤ) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum, ← Finset.sum_coe_sort]
    simp [DivisorWithCoeffs.coeff, Finsupp.smul_single]
  have hcw : MMP.Intersection.IsWeilDivisorOfCartier (-∑ l : D.support, D.coeff l.1 • ε l)
      (-D) := by
    have := isWeilDivisorOfCartier_sum Finset.univ (fun l : D.support => D.coeff l.1) ε
      (fun l => Finsupp.single l.1 1) hε
    rw [← hDsum] at this
    exact isWeilDivisorOfCartier_neg this
  obtain ⟨hDc, hamp⟩ := hA
  obtain ⟨haor, hvert⟩ := (mem_verticalSurfaceCoefficients f D).1 ha
  haveI := hvarX
  haveI : IsProper (f ≫ sX) := by rw [hcomp]; infer_instance
  haveI : IsProper f := IsProper.of_comp f sX
  have hpt := exists_eq_of_mem_vertical (Z ↘ Spec (.of ℂ)) hvarZ hsmZ hdim hsnc hDpos a haor ε hε
    π hπ hE3 hX0 sX f hcomp f.isClosedMap hDc hamp hcw hvert
  exact eq_zero_of_forall_contracted (Z ↘ Spec (.of ℂ)) hvarZ hsmZ hdim hsnc hDpos a haor ε hε
    π hπ hE3 hX0 f hDc hamp hcw A hAamp hpt

end MMP.Fourfold
