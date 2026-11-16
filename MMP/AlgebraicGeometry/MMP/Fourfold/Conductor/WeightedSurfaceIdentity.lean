module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.Topology.Collar
import MMP.Analysis.Convex.ConvexCover
import MMP.Geometry.Manifold.Corners.ReachOfImmersion
import MMP.Geometry.Manifold.Corners.Rounding
import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# The weighted surface intersection identity; collars of manifolds with corners

Let `Z` be a smooth projective fourfold over a field `k`, `B = ∑ᵢ Eᵢ` a reduced snc divisor on
`Z`, `a` an oriented surface coefficient system on `B` (`MMP.Fourfold.orientedSurfaceCoefficients`)
with divisors `Zᵢ(a)` on the `Eᵢ` (`MMP.Fourfold.surfaceCoefficientDivisor`), and
`D = ∑ᵢ mᵢ Eᵢ` with all `mᵢ > 0`. Put `b_{ij,S} = a_{ij,S} / (mᵢ mⱼ)`. For every `ℚ`-Cartier
divisor `H` on `Z`,
`∑_{i<j} ∑_S mᵢ mⱼ b_{ij,S}² (D · S · H)
  = ∑ᵢ (Zᵢ(a)² · H|_{Eᵢ}) / mᵢ + ∑_{i<j<k} ∑_T mᵢ mⱼ mₖ (b_{ij,T} - b_{ik,T} + b_{jk,T})² (T · H)`,
where `S` runs over the connected components of `Eᵢ ∩ Eⱼ` and `T` over the connected components
of the triple intersection `Eᵢ ∩ Eⱼ ∩ Eₖ`.

Second, let `X = Σ i, M i` be a finite disjoint union of compact Hausdorff smooth real manifolds
with corners, `M i` modelled on the quadrant `[0, ∞)^(n i)`, the dimensions `n i` allowed to
differ, and let `∂X` be its boundary (the points of every depth, corners included). Then `X` and
`∂X` have the homotopy types of finite polyhedra, and `∂X` has a collar: an open embedding
`c : ∂X × [0, 1) → X` with `c (x, 0) = x`.

## Main results

* `MMP.Fourfold.sum_sq_mul_intersectionNumber_doubleSurface_eq`: the weighted surface identity.
* `MMP.exists_collar_and_homotopyEquiv_finite_simplicialComplex`: collars and finite homotopy
  models for compact manifolds with corners.

## Implementation notes

* All intersection numbers are those of Kollár–Mori, `MMP.Mori.sheafIntersectionNumber`, of the
  invertible sheaves `MMP.CartierDivisor.sheaf` of Cartier divisors, extended
  `ℚ`-multilinearly to `ℚ`-Cartier divisors (`MMP.Mori.KCartierDivisor ℚ`). A double surface `S`
  and a triple curve `T` are given their reduced induced closed subscheme structure. `D · S · H`
  is computed on `Z` against `S`, `Zᵢ(a)² · H|_{Eᵢ}` on the threefold `Eᵢ`, against `Eᵢ` itself,
  with `H|_{Eᵢ}` the pull-back of the sheaves of `H`, and `T · H` on `Z` against `T`.
* The divisors `Eᵢ` of `Z` and the prime divisors `P` of the `Eᵢ` enter through Cartier
  divisors `εᵢ`, `π_P` whose Weil divisors are `Eᵢ` and `P`
  (`MMP.Intersection.IsWeilDivisorOfCartier`).
  On the smooth `Z` and `Eᵢ` these exist, and they are unique, so the identity is about the
  divisors themselves. `D` enters as `∑ᵢ mᵢ εᵢ` and `Zᵢ(a)` as `∑_P Zᵢ(a)_P π_P`.
* The components are indexed by the support of `B`, with an arbitrary linear order playing the
  role of the labelling `i = 1, …, s`. The dimension bounds `dim Eᵢ ≤ 3`, `dim S ≤ 2` and
  `dim T ≤ 1` that the intersection numbers require are proved from the snc condition: a point on
  `r` components has a local ring of dimension at least `r`, so on the fourfold `Z` a closed set
  inside `r` components has dimension at most `4 - r`
  (`MMP.Fourfold.topologicalKrullDim_subscheme_le_of_isSNC`).
* A manifold with corners is a manifold over `modelWithCornersEuclideanQuadrant`, smooth of
  class `C^∞`; a disjoint union of components of different dimensions is a sigma type over a
  finite index type. A finite polyhedron is the underlying space
  `Geometry.SimplicialComplex.space` of a simplicial complex with finitely many faces in
  `EuclideanSpace ℝ (Fin N)`. The source also asks that the boundary hypersurfaces be embedded;
  the conclusion holds without it. The collar is topological, as `∂X` is not a smooth manifold.
* The homotopy type of `X` is found by embedding each `M i` in a Euclidean space (Whitney): the
  image has positive reach, so it is homotopy equivalent to a finite union of balls and hence to
  its nerve. Each `∂(M i)` is homotopy equivalent to a compact set of positive reach, treated the
  same way. The collar comes from Brown's collaring theorem applied to local collars.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP MMP.Mori

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

/-- No other component contains an irreducible component of `E_b`. -/
private theorem not_component_subset {Z : Scheme.{0}} {B : Divisor Z} (b : B.support)
    (c : {c : B.support // c ≠ b}) :
    ∀ W ∈ MMP.Resolution.componentsOf (b.1.idealSheaf.support : Set Z),
      ¬ W ⊆ (c.1.1.idealSheaf.support : Set Z) :=
  not_component_subset_of_not_support_subset b.1 c.1.1.idealSheaf
    (not_support_subset_of_ne fun e => c.2 (Subtype.ext e.symm))

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
  haveI := hvar
  obtain ⟨he, hsub⟩ := (hε a).isEffective_and_subscheme_eq_of_isSmoothScheme sZ hsm
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
    rw [Scheme.IdealSheafData.support_comap]
    exact hx.2
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

/-- The image of the support of a prime divisor of `E` is the closure of the image of its generic
point. -/
private theorem image_support_eq_closure {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    E.idealSheaf.subschemeι '' P.support = closure {E.idealSheaf.subschemeι P.genericPoint} := by
  rw [← Set.image_singleton, E.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]

/-- The first component of a double surface, as an element of the support. -/
private abbrev fstS {Z : Scheme.{0}} {B : Divisor Z} (σ : DoubleSurface B) : B.support :=
  ⟨σ.fst, σ.fst_mem⟩

/-- The second component of a double surface, as an element of the support. -/
private abbrev sndS {Z : Scheme.{0}} {B : Divisor Z} (σ : DoubleSurface B) : B.support :=
  ⟨σ.snd, σ.snd_mem⟩

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
    rw [Scheme.IdealSheafData.support_comap]
    exact (σ.carrier_subset hηS).2
  have hm2 : η ∈ ((l.1.idealSheaf.comap ι).support : Set _) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hsub hηS
  have hc : c' ⟨⟨_, hne1⟩, hm1⟩ ≠ c' ⟨⟨l, hl₁⟩, hm2⟩ := fun h =>
    hl₂ (congrArg (fun e => e.1.1) (hinj h)).symm
  have hdim := hw.2
  rw [ringKrullDim_stalk_eq_coheight, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hdim
  have hm : m = 1 := by exact_mod_cast hdim.symm
  subst hm
  exact hc (Subsingleton.elim _ _)

/-- **Double surfaces of a component are determined by their surface.** Two double surfaces with
the same first component and the same surface are equal: were their second components distinct,
the surface would lie in three components, and at its generic point, of coheight one on `Eᵢ`,
two distinct members of a regular system of parameters of `𝒪_{Eᵢ}` would cut out the other two. -/
private theorem eq_of_fst_eq_of_carrier_eq {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {σ τ : DoubleSurface B} (h₁ : σ.fst = τ.fst) (h₃ : σ.carrier = τ.carrier) : σ = τ := by
  by_cases h₂ : σ.snd = τ.snd
  · exact DoubleSurface.ext h₁ h₂ h₃
  exact (not_carrier_subset_support hB σ ⟨τ.snd, τ.snd_mem⟩
    (fun e => τ.fst_ne_snd (h₁ ▸ (congrArg Subtype.val e).symm))
    (fun e => h₂ (congrArg Subtype.val e).symm)
    (by rw [h₃]; exact fun _ hx => (τ.carrier_subset hx).2)).elim

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
  have hcl := (image_support_eq_closure (rho hB σ)).symm.trans (image_support_rho hB σ)
  refine (finsum_eq_single _ ⟨σ, rfl, hcl.symm⟩ fun τ hτ => absurd ?_ hτ).trans rfl
  exact Subtype.ext (eq_of_fst_eq_of_carrier_eq hB τ.2.1 (τ.2.2.trans hcl))

/-- The surface of a double surface `σ` of `(Eᵢ, Eⱼ)` is the image of `ρ(σ)` in `Z`. -/
private theorem range_comp_rho {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    Set.range ((rho hB σ).idealSheaf.subschemeι ≫ σ.fst.idealSheaf.subschemeι) = σ.carrier := by
  rw [← image_support_rho hB σ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  congr 1
  exact (rho hB σ).idealSheaf.range_subschemeι

/-- **(2b) `(εⱼ · c · S)_Z = (π_{ρ(σ)} · π_{ρ(σ)} · c|_{Eᵢ})_{Eᵢ}`** for a double surface `σ` of
`(Eᵢ, Eⱼ)`: `εⱼ|_{Eᵢ} = ρ(σ) + R` with `R` missing `ρ(σ)`. -/
private theorem sheafIntersectionNumber_eps_snd (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ)
    {B : Divisor Z} (hB : B.IsSNC sZ) (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (σ : DoubleSurface B)
    (hS2 : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subscheme ≤ (2 : ℕ))
    (hE3 : topologicalKrullDim σ.fst.idealSheaf.subscheme ≤ (3 : ℕ)) (c : Z.CartierDivisor) :
    sheafIntersectionNumber k sZ
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subschemeι 2 hS2
        (fun t => MMP.CartierDivisor.sheaf (![ε ⟨σ.snd, σ.snd_mem⟩, c] t)) =
      @sheafIntersectionNumber k _ _ _ (σ.fst.idealSheaf.subschemeι ≫ sZ) _ (𝟙 _) _ 3 hE3
        ![MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ (rho hB σ)),
          MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ (rho hB σ)),
          (Scheme.Modules.pullback σ.fst.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf c)]
        (fun t => by
          fin_cases t
          exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
            isInvertible_pullback_obj _ _]) := by
  set ι := σ.fst.idealSheaf.subschemeι
  set P := rho hB σ
  set ιP := P.idealSheaf.subschemeι
  have := P.integral
  obtain ⟨R, hcomap, hPe, hRe, hRtop⟩ := exists_comap_eq_rho_mul hB σ
  have hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ) :=
    topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k (ι ≫ sZ) (𝟙 _) 2
      hE3 P.idealSheaf
  have hker : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subschemeι.ker =
      (ιP ≫ ι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      range_comp_rho hB σ]
  rw [sheafIntersectionNumber_eq_of_ker_eq k sZ _ (ιP ≫ ι) hker 2 hS2 hP2,
    sheafIntersectionNumber_comp_eq_of_iso k sZ ι ιP 2 hP2 _
      (fun t => (Scheme.Modules.pullback ι).obj
        (MMP.CartierDivisor.sheaf (![ε ⟨σ.snd, σ.snd_mem⟩, c] t)))
      (fun t => Iso.refl _)]
  obtain ⟨hπe, hπsub⟩ := exists_isEffective_pi k sZ hB π hπ ⟨σ.fst, σ.fst_mem⟩ P
  have hab : (⟨σ.snd, σ.snd_mem⟩ : B.support) ≠ ⟨σ.fst, σ.fst_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h).symm
  obtain ⟨eε⟩ := nonempty_pullback_eps_iso k sZ hvar hsm hB ε hε hab
  have eπ : MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ P) ≅
      Stacks.Divisors.invertibleSheaf' P.idealSheaf :=
    MMP.CartierDivisor.sheafIsoInvertibleSheaf _ hπe ≪≫
      eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hπsub)
  have hL3 : ∀ t : Fin (2 + 1), SheafOfModules.IsInvertible σ.fst.idealSheaf.subscheme.presheaf
      σ.fst.idealSheaf.subscheme.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ P),
        MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ P),
        (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)] t) :=
    fun t => by
      fin_cases t
      exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
        isInvertible_pullback_obj _ _]
  rw [Snapper.sheafIntersectionNumber_eq_intersectionNumber k (ι ≫ sZ) (𝟙 _),
    intersectionNumber_eq_of_isEffectiveCartierDivisor' k (ι ≫ sZ) (𝟙 _) 2 hE3
      ![MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ P),
        MMP.CartierDivisor.sheaf (π ⟨σ.fst, σ.fst_mem⟩ P),
        (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)] P.idealSheaf
      ((Scheme.Modules.pullbackId _).app _ ≪≫ eπ),
    ← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    sheafIntersectionNumber_congr_hom k (ι ≫ sZ) (Category.comp_id ιP),
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    Snapper.sheafIntersectionNumber_eq_intersectionNumber,
    intersectionNumber_update_tensor k (ι ≫ sZ) ιP 2 hP2 0 _
      (Stacks.Divisors.invertibleSheaf' P.idealSheaf) (Stacks.Divisors.invertibleSheaf' R)
      (eε ≪≫ eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hcomap) ≪≫
        (Stacks.Divisors.invertibleSheafSumIso _ _).symm)]
  have := isInvertible_update (fun t => (Scheme.Modules.pullback ι).obj
    (MMP.CartierDivisor.sheaf (![ε ⟨σ.snd, σ.snd_mem⟩, c] t))) 0
    (Stacks.Divisors.invertibleSheaf' P.idealSheaf)
  have := isInvertible_update (fun t => (Scheme.Modules.pullback ι).obj
    (MMP.CartierDivisor.sheaf (![ε ⟨σ.snd, σ.snd_mem⟩, c] t))) 0
    (Stacks.Divisors.invertibleSheaf' R)
  refine (congrArg₂ (· + ·) (?_ : _ = _) (?_ : _ = (0 : ℤ))).trans (add_zero _)
  · refine intersectionNumber_eq_of_iso_at k (ι ≫ sZ) ιP 2 hP2 _ _ 0 ?_
      (eqToIso (Function.update_self _ _ _) ≪≫ eπ.symm)
    intro q hq
    fin_cases q
    · simp at hq
    · exact (Function.update_of_ne hq (Stacks.Divisors.invertibleSheaf' P.idealSheaf : _)
        (fun t => (Scheme.Modules.pullback ι).obj
          (MMP.CartierDivisor.sheaf (![ε ⟨σ.snd, σ.snd_mem⟩, c] t)))).symm
  · rw [← Snapper.sheafIntersectionNumber_eq_intersectionNumber,
      ← sheafIntersectionNumber_congr_hom k (ι ≫ sZ) (Category.id_comp ιP),
      sheafIntersectionNumber_comp_eq_of_iso k (ι ≫ sZ) ιP (𝟙 _) 2 hP2 _ _ (fun t => Iso.refl _)]
    exact @sheafIntersectionNumber_eq_zero_of_iso_unit k _ _ _ _ _ (𝟙 _) _ 2 hP2 _
      (fun t => isInvertible_pullback_obj _ _) 0
      ((Scheme.Modules.pullback ιP).mapIso (eqToIso (Function.update_self _ _ _)) ≪≫
        (nonempty_pullback_invertibleSheaf_iso_unit ιP R hRtop).some)

/-- `ρ(σ)` read on a component `E` equal to the first component of `σ`. -/
private noncomputable def rhoOf {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ) {E : Mori.PrimeDivisor Z}
    (σ : DoubleSurface B) (h : σ.fst = E) : Mori.PrimeDivisor E.idealSheaf.subscheme :=
  h ▸ rho hB σ

private theorem image_support_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E) :
    E.idealSheaf.subschemeι '' (rhoOf hB σ h).support = σ.carrier := by
  subst h
  exact image_support_rho hB σ

private theorem surfaceCoefficientCoeff_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (a : DoubleSurface B → ℚ) {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E) :
    surfaceCoefficientCoeff a E (rhoOf hB σ h) = a σ := by
  subst h
  exact surfaceCoefficientCoeff_rho hB a σ

/-- Prime divisors of `E` with the same image in `Z` are equal. -/
private theorem eq_of_image_support_eq {Z : Scheme.{0}} {E : Mori.PrimeDivisor Z}
    {P Q : Mori.PrimeDivisor E.idealSheaf.subscheme}
    (h : E.idealSheaf.subschemeι '' P.support = E.idealSheaf.subschemeι '' Q.support) : P = Q := by
  rw [image_support_eq_closure, image_support_eq_closure] at h
  have hQ : IsGenericPoint (E.idealSheaf.subschemeι Q.genericPoint)
      (closure {E.idealSheaf.subschemeι P.genericPoint}) := by
    rw [h]
    exact isGenericPoint_closure
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
private theorem sum_surfaceCoefficientDivisor {k : Type} [Field k] {Z : Scheme.{0}}
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

/-- **(4, disjoint case) `(π_P · π_Q · c|_{Eᵢ})_{Eᵢ} = 0`** for prime divisors `P`, `Q` of `Eᵢ`
with disjoint supports: cutting by `π_P`, the sheaf of `π_Q` is trivial on `P`. -/
private theorem sheafIntersectionNumber_pi_pi_eq_zero_of_disjoint (k : Type) [Field k]
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (i : B.support) (hE3 : topologicalKrullDim i.1.idealSheaf.subscheme ≤ (3 : ℕ))
    (P Q : Mori.PrimeDivisor i.1.idealSheaf.subscheme) (hPQ : Disjoint P.support Q.support)
    (c : Z.CartierDivisor) :
    @sheafIntersectionNumber k _ _ _ (i.1.idealSheaf.subschemeι ≫ sZ) _ (𝟙 _) _ 3 hE3
        ![MMP.CartierDivisor.sheaf (π i P),
          MMP.CartierDivisor.sheaf (π i Q),
          (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
            (MMP.CartierDivisor.sheaf c)]
        (fun t => by
          fin_cases t
          exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
            isInvertible_pullback_obj _ _]) = 0 := by
  have hL3 : ∀ t : Fin (2 + 1), SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf (π i P),
        MMP.CartierDivisor.sheaf (π i Q),
        (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf c)] t) :=
    fun t => by
      fin_cases t
      exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
        isInvertible_pullback_obj _ _]
  set ι := i.1.idealSheaf.subschemeι
  obtain ⟨hPe, hPsub⟩ := exists_isEffective_pi k sZ hB π hπ i P
  obtain ⟨hQe, hQsub⟩ := exists_isEffective_pi k sZ hB π hπ i Q
  set D := MMP.CartierDivisor.subscheme (π i P) hPe
  have hD2 := topologicalKrullDim_subscheme_le_of_isEffective k (ι ≫ sZ) (𝟙 _) 2 hE3 _ hPe
  rw [sheafIntersectionNumber_eq_of_isEffective k (ι ≫ sZ) (𝟙 _) 2 hE3 _ (π i P) hPe
      ((Scheme.Modules.pullbackId _).app _),
    sheafIntersectionNumber_congr_hom k (ι ≫ sZ)
      ((Category.comp_id D.subschemeι).trans (Category.id_comp D.subschemeι).symm),
    sheafIntersectionNumber_comp_eq_of_iso k (ι ≫ sZ) D.subschemeι (𝟙 _) 2 hD2 _ _
      (fun t => Iso.refl _)]
  have hdisj : Disjoint (Set.range D.subschemeι)
      (MMP.CartierDivisor.subscheme (π i Q) hQe).support := by
    rw [D.range_subschemeι, hQsub]
    change Disjoint (D.support : Set _) Q.support
    rw [show D = P.idealSheaf from hPsub]
    exact hPQ
  exact @sheafIntersectionNumber_eq_zero_of_iso_unit k _ _ _ _ _ (𝟙 _) _ 2 hD2 _
    (fun t => isInvertible_pullback_obj _ _) 0
    (nonempty_pullback_cartierSheaf_iso_unit D.subschemeι (π i Q) hQe hdisj).some

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

/-- `(e · c · S)` against the closed set `S` with its reduced structure, extended by zero when
`dim S > 2`. -/
private noncomputable def surfNum (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] (S : Set Z) (e c : Z.CartierDivisor) : ℚ := by
  classical
  exact if h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure S)).subscheme ≤ (2 : ℕ) then
    (sheafIntersectionNumber k sZ
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure S)).subschemeι 2 h
      (fun t => MMP.CartierDivisor.sheaf (![e, c] t)) : ℚ) else 0

private theorem surfNum_eq (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] (S : Set Z) (e c : Z.CartierDivisor) (h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure S)).subscheme ≤ (2 : ℕ)) :
    (sheafIntersectionNumber k sZ
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure S)).subschemeι 2 h
      (fun t => MMP.CartierDivisor.sheaf (![e, c] t)) : ℚ) = surfNum k sZ S e c := by
  rw [surfNum, dite_eq_left h]

/-- `(c · T)` against the closed set `T` with its reduced structure, extended by zero when
`dim T > 1`. -/
private noncomputable def curveNum (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] (T : Set Z) (c : Z.CartierDivisor) : ℚ := by
  classical
  exact if h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ) then
    (sheafIntersectionNumber k sZ
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι 1 h
      (fun _ => MMP.CartierDivisor.sheaf c) : ℚ) else 0

private theorem curveNum_eq (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] (T : Set Z) (c : Z.CartierDivisor) (h : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ)) :
    (sheafIntersectionNumber k sZ
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι 1 h
      (fun _ => MMP.CartierDivisor.sheaf c) : ℚ) = curveNum k sZ T c := by
  rw [curveNum, dite_eq_left h]

/-- `(π_P · π_Q · c|_{Eᵢ})` on the component `Eᵢ`, extended by zero when `dim Eᵢ > 3`. -/
private noncomputable def xNum (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] {B : Divisor Z}
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (i : B.support) (P Q : Mori.PrimeDivisor i.1.idealSheaf.subscheme) (c : Z.CartierDivisor) :
    ℚ := by
  classical
  exact if h : topologicalKrullDim i.1.idealSheaf.subscheme ≤ (3 : ℕ) then
    (@sheafIntersectionNumber k _ _ _ (i.1.idealSheaf.subschemeι ≫ sZ) _ (𝟙 _) _ 3 h
      ![MMP.CartierDivisor.sheaf (π i P),
        MMP.CartierDivisor.sheaf (π i Q),
        (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf c)]
      (fun t => by
        fin_cases t
        exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
          isInvertible_pullback_obj _ _]) : ℚ) else 0

private theorem xNum_eq (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k))
    [IsProper sZ] {B : Divisor Z}
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (i : B.support) (P Q : Mori.PrimeDivisor i.1.idealSheaf.subscheme) (c : Z.CartierDivisor)
    (h : topologicalKrullDim i.1.idealSheaf.subscheme ≤ (3 : ℕ)) :
    (@sheafIntersectionNumber k _ _ _ (i.1.idealSheaf.subschemeι ≫ sZ) _ (𝟙 _) _ 3 h
      ![MMP.CartierDivisor.sheaf (π i P),
        MMP.CartierDivisor.sheaf (π i Q),
        (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
          (MMP.CartierDivisor.sheaf c)]
      (fun t => by
        fin_cases t
        exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
          isInvertible_pullback_obj _ _]) : ℚ) = xNum k sZ π i P Q c := by
  rw [xNum, dite_eq_left h]

/-- `(εⱼ · c · S) = (π_{ρσ} · π_{ρσ} · c|)_{Eᵢ}`, in the extended numbers. -/
private theorem surfNum_eps_snd (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ)
    {B : Divisor Z} (hB : B.IsSNC sZ) (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hS : ∀ σ : DoubleSurface B, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subscheme ≤ (2 : ℕ))
    (hE : ∀ i : B.support, topologicalKrullDim i.1.idealSheaf.subscheme ≤ (3 : ℕ))
    (σ : DoubleSurface B) (c : Z.CartierDivisor) :
    surfNum k sZ σ.carrier (ε (sndS σ)) c = xNum k sZ π (fstS σ) (rho hB σ) (rho hB σ) c := by
  rw [← surfNum_eq k sZ _ _ _ (hS σ), ← xNum_eq k sZ π _ _ _ _ (hE (fstS σ))]
  exact_mod_cast sheafIntersectionNumber_eps_snd k sZ hvar hsm hB ε hε π hπ σ (hS σ)
    (hE (fstS σ)) c

/-- Distinct double surfaces of the same ordered pair: `(π_{ρσ} · π_{ρτ} · c|)_{Eᵢ} = 0`. -/
private theorem xNum_rhoOf_eq_zero (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (i : B.support) {σ τ : DoubleSurface B} (h : σ.fst = i.1) (h' : τ.fst = i.1)
    (h₂ : σ.snd = τ.snd) (hne : σ ≠ τ) (c : Z.CartierDivisor) :
    xNum k sZ π i (rhoOf hB σ h) (rhoOf hB τ h') c = 0 := by
  rw [xNum]
  split_ifs with hE3
  · exact_mod_cast sheafIntersectionNumber_pi_pi_eq_zero_of_disjoint k sZ hB π hπ i hE3 _ _
      (disjoint_support_rhoOf hB h h' h₂ hne) c
  · rfl

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
    · exact fun h => absurd (Finset.mem_univ _) h
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
    · exact fun h => absurd (Finset.mem_univ _) h
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
    (hL1 : ∀ σ : DoubleSurface B, NS σ.carrier (sndS σ) = X (fstS σ) (rho hB σ) (rho hB σ))
    (hT1 : ∀ (σ : DoubleSurface B) (l : B.support), l ≠ fstS σ → l ≠ sndS σ →
      NS σ.carrier l = ∑ T ∈ tcs σ.fst σ.snd l.1, if T ⊆ σ.carrier then N T else 0)
    (hD0 : ∀ (i : B.support) (σ τ : DoubleSurface B) (h : σ.fst = i.1) (h' : τ.fst = i.1),
      σ.snd = τ.snd → σ ≠ τ → X i (rhoOf hB σ h) (rhoOf hB τ h') = 0)
    (hT2 : ∀ (i : B.support) (σ τ : DoubleSurface B) (h : σ.fst = i.1) (h' : τ.fst = i.1),
      σ.snd ≠ τ.snd → X i (rhoOf hB σ h) (rhoOf hB τ h') =
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
        · rw [ite_eq_left h2, hT2 (fstS σ) σ τ.1 rfl τ.2 (Ne.symm h2)]
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
  have hLsplit : ∀ σ : DoubleSurface B, ∑ l, m l * NS σ.carrier l =
      m (sndS σ) * X (fstS σ) (rho hB σ) (rho hB σ) +
      m (fstS σ) * X (sndS σ) (rho hB σ.swap) (rho hB σ.swap) +
      ∑ z, (if z ≠ fstS σ ∧ z ≠ sndS σ then m z * ∑ T ∈ tcs σ.fst σ.snd z.1,
        (if T ⊆ σ.carrier then N T else 0) else 0) := by
    intro σ
    have hne : sndS σ ≠ fstS σ := fun e => σ.fst_ne_snd (congrArg Subtype.val e).symm
    have h3 : ∀ z, m z * NS σ.carrier z =
        (if z = sndS σ then m (sndS σ) * X (fstS σ) (rho hB σ) (rho hB σ) else 0) +
        (if z = fstS σ then m (fstS σ) * X (sndS σ) (rho hB σ.swap) (rho hB σ.swap) else 0) +
        (if z ≠ fstS σ ∧ z ≠ sndS σ then m z * ∑ T ∈ tcs σ.fst σ.snd z.1,
          (if T ⊆ σ.carrier then N T else 0) else 0) := by
      intro z
      by_cases h1 : z = sndS σ
      · subst h1
        rw [ite_eq_left rfl, ite_eq_right hne, ite_eq_right fun h => h.2 rfl, hL1, add_zero,
          add_zero]
      · by_cases h2 : z = fstS σ
        · subst h2
          rw [ite_eq_right h1, ite_eq_left rfl, ite_eq_right fun h => h.1 rfl, zero_add, add_zero]
          exact congrArg _ (hL1 σ.swap)
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left ⟨h2, h1⟩, zero_add, zero_add,
            hT1 σ z h2 h1]
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
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, hLsplit]
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

/-- The finite sum over the triple curves, as a `finsum` over the connected components. -/
private theorem finsum_isTripleCurve_eq_sum {Z : Scheme.{0}} [NoetherianSpace Z]
    (E₁ E₂ E₃ : Mori.PrimeDivisor Z) (g : Set Z → ℚ) :
    ∑ᶠ (T : Set Z) (_ : T.Nonempty ∧ T ⊆ E₁.support ∩ E₂.support ∩ E₃.support ∧
        ∃ x ∈ E₁.support ∩ E₂.support ∩ E₃.support,
          connectedComponentIn (E₁.support ∩ E₂.support ∩ E₃.support) x = T), g T =
      ∑ T ∈ tcs E₁ E₂ E₃, g T := by
  rw [tcs, ← finsum_mem_eq_finite_toFinset_sum]
  rfl

/-- Distributing the sum over the Cartier divisors of `H`, left side. -/
private theorem sum_ite_mul_sum_eq {D ι C : Type*} [Fintype D] [Fintype ι] (s : Finset C)
    (h : C → ℚ) (p : D → Prop) [DecidablePred p] (w : D → ℚ) (m : ι → ℚ)
    (F : D → ι → C → ℚ) :
    ∑ σ, (if p σ then w σ * ∑ l, m l * ∑ c ∈ s, h c * F σ l c else 0) =
      ∑ c ∈ s, h c * ∑ σ, (if p σ then w σ * ∑ l, m l * F σ l c else 0) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hp : p σ
  · simp only [ite_eq_left hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => by ring
  · simp only [ite_eq_right hp, Finset.sum_const_zero, mul_zero]

/-- Distributing the sum over the Cartier divisors of `H`, first term of the right side. -/
private theorem sum_finsupp_sum_mul_eq {ι C : Type*} [Fintype ι] (s : Finset C) (h : C → ℚ)
    (r : ι → ℚ) {P : ι → Type*} (f : ∀ i, P i →₀ ℚ) (X : ∀ i, P i → P i → C → ℚ) :
    ∑ i, r i * (f i).sum (fun P cP => (f i).sum fun Q cQ => ∑ c ∈ s, cP * cQ * h c * X i P Q c) =
      ∑ c ∈ s, h c * ∑ i, r i * (f i).sum (fun P cP =>
        (f i).sum fun Q cQ => cP * cQ * X i P Q c) := by
  simp only [Finsupp.sum, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun c _ => by ring

/-- Distributing the sum over the Cartier divisors of `H`, second term of the right side. -/
private theorem sum_ite_sum_mul_eq {ι C S : Type*} [Fintype ι] (s : Finset C) (h : C → ℚ)
    (p : ι → ι → ι → Prop) [∀ i j l, Decidable (p i j l)] (U : ι → ι → ι → Finset S)
    (K : ι → ι → ι → S → ℚ) (N : S → C → ℚ) :
    ∑ i, ∑ j, ∑ l, (if p i j l then ∑ T ∈ U i j l, K i j l T * ∑ c ∈ s, h c * N T c else 0) =
      ∑ c ∈ s, h c * ∑ i, ∑ j, ∑ l,
        (if p i j l then ∑ T ∈ U i j l, K i j l T * N T c else 0) := by
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hp : p i j l
  · simp only [ite_eq_left hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun c _ => by ring
  · simp only [ite_eq_right hp, mul_zero, Finset.sum_const_zero]

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
  subst h
  exact stalk_rho hB σ hx

private theorem mem_support_comap_snd_of_mem_rhoOf {k : Type} [Field k] {Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of k)} [IsProper sZ] {B : Divisor Z} (hB : B.IsSNC sZ)
    {E : Mori.PrimeDivisor Z} (σ : DoubleSurface B) (h : σ.fst = E)
    {x : E.idealSheaf.subscheme} (hx : x ∈ (rhoOf hB σ h).support) :
    x ∈ (σ.snd.idealSheaf.comap E.idealSheaf.subschemeι).support := by
  have hxσ : E.idealSheaf.subschemeι x ∈ σ.carrier := by
    rw [← image_support_rhoOf hB σ h]
    exact ⟨x, hx, rfl⟩
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

/-- **The intersection number on a prime divisor `P` of a component, split over curves.** Let
`P ⊆ E` be a prime divisor of a component `E`, `L₁, L₂` invertible sheaves on `E` with
`L₁ ≅ 𝒪_E(G)` for an effective Cartier divisor `G` and `L₂ ≅ c|_E`. If `G|_P` is cut out by
regular parameters and its support is the disjoint union of the closed sets `a ∈ s` of `Z`, then
`(L₁ · L₂ · P)_E = ∑_a (c · a)`. -/
private theorem sheafIntersectionNumber_eq_sum_curveNum (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] {E : Mori.PrimeDivisor Z}
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ))
    (L : Fin 2 → E.idealSheaf.subscheme.Modules)
    [∀ t, SheafOfModules.IsInvertible E.idealSheaf.subscheme.presheaf
      E.idealSheaf.subscheme.ringCatSheaf.2 (L t)]
    (G : E.idealSheaf.subscheme.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor G]
    (e0 : L 0 ≅ Stacks.Divisors.invertibleSheaf' G) (c : Z.CartierDivisor)
    (e1 : L 1 ≅ (Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
      (MMP.CartierDivisor.sheaf c))
    (hG : ∀ y ∈ (G.comap P.idealSheaf.subschemeι).support, ∃ (m : ℕ)
      (w : Fin m → P.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (G.comap P.idealSheaf.subschemeι) y = Ideal.span {w j})
    (s : Finset (Set Z))
    (hsupp : ((G.comap P.idealSheaf.subschemeι).support : Set _) =
      P.idealSheaf.subschemeι ⁻¹' (E.idealSheaf.subschemeι ⁻¹' ⋃ a ∈ s, a))
    (hdisj : (s : Set (Set Z)).PairwiseDisjoint id) (hcl : ∀ a ∈ s, IsClosed a)
    (hsub : ∀ a ∈ s, a ⊆ E.idealSheaf.subschemeι '' P.support)
    (hdim : ∀ a ∈ s, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure a)).subscheme ≤ (1 : ℕ)) :
    (sheafIntersectionNumber k (E.idealSheaf.subschemeι ≫ sZ) P.idealSheaf.subschemeι 2 hP2 L :
      ℚ) = ∑ a ∈ s, curveNum k sZ a c := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set ι := E.idealSheaf.subschemeι
  set ιP := P.idealSheaf.subschemeι
  have : IsLocallyNoetherian E.idealSheaf.subscheme := isLocallyNoetherian_of_isClosedImmersion ι
  have : IsLocallyNoetherian P.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ιP
  have : ∀ t, SheafOfModules.IsInvertible P.idealSheaf.subscheme.presheaf
      P.idealSheaf.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback ιP).obj (L t)) :=
    fun t => isInvertible_pullback_obj _ _
  have : Stacks.Divisors.IsPullbackDefined ιP G :=
    MMP.Resolution.isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ hG
  have : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (MMP.CartierDivisor.sheaf c) := isInvertible_cartierSheaf _
  have : SheafOfModules.IsInvertible E.idealSheaf.subscheme.presheaf
      E.idealSheaf.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)) :=
    isInvertible_pullback_obj _ _
  let T : {a // a ∈ s} → Closeds P.idealSheaf.subscheme := fun a =>
    ⟨ιP ⁻¹' (ι ⁻¹' a.1), ((hcl a.1 a.2).preimage ι.continuous).preimage ιP.continuous⟩
  have hrange : ∀ a : {a // a ∈ s}, Set.range
      (((Scheme.IdealSheafData.vanishingIdeal (T a)).subschemeι ≫ ιP) ≫ ι) = a.1 := by
    intro a
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hy
    · intro hz
      obtain ⟨y, hy, rfl⟩ := hsub a.1 a.2 hz
      obtain ⟨w, rfl⟩ : y ∈ Set.range ιP := by rwa [P.idealSheaf.range_subschemeι]
      exact ⟨_, ⟨w, hz, rfl⟩, rfl⟩
  have hker : ∀ a : {a // a ∈ s},
      (((Scheme.IdealSheafData.vanishingIdeal (T a)).subschemeι ≫ ιP) ≫ ι).ker =
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure a.1)).subschemeι.ker := by
    intro a
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      hrange]
  have hdT : ∀ a : {a // a ∈ s}, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (T a)).subscheme ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro a
    have := IsClosedImmersion.isIso_lift _ _ (hker a)
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift _ _ (hker a).le))).symm.isHomeomorph]
    exact hdim a.1 a.2
  have hT' : ((G.comap ιP).support : Set P.idealSheaf.subscheme) =
      ⋃ a ∈ (Finset.univ : Finset {a // a ∈ s}), (T a : Set P.idealSheaf.subscheme) := by
    rw [hsupp]
    ext y
    simp [T]
  have hdisj' : ((Finset.univ : Finset {a // a ∈ s}) : Set {a // a ∈ s}).PairwiseDisjoint
      fun a => (T a : Set P.idealSheaf.subscheme) := by
    intro a _ b _ hab
    exact ((hdisj a.2 b.2 fun h => hab (Subtype.ext h)).preimage _).preimage _
  have h2 := MMP.Mori.sheafIntersectionNumber_eq_sum_of_support_eq_iUnion k (ιP ≫ ι ≫ sZ) 1 hP2
    (fun t => (Scheme.Modules.pullback ιP).obj (L t)) (G.comap ιP) hG
    ((Scheme.Modules.pullback ιP).mapIso e0 ≪≫ Stacks.Divisors.invertibleSheafPullbackIso ιP G)
    Finset.univ T hT' hdisj' hdT
  rw [sheafIntersectionNumber_congr_hom k (ι ≫ sZ) (Category.id_comp ιP).symm,
    sheafIntersectionNumber_comp_eq_of_iso k (ι ≫ sZ) ιP (𝟙 _) 2 hP2 L
      (fun t => (Scheme.Modules.pullback ιP).obj (L t)) (fun t => Iso.refl _)]
  refine (congrArg (Int.cast : ℤ → ℚ) h2).trans ?_
  push_cast
  rw [← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun a _ => ?_
  have eL : ∀ t : Fin 1, L t.succ ≅
      (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c) := fun t =>
    eqToIso (congrArg L (by rw [Fin.fin_one_eq_zero t]; rfl)) ≪≫ e1
  rw [← sheafIntersectionNumber_comp_eq_of_iso k (ι ≫ sZ) ιP
      (Scheme.IdealSheafData.vanishingIdeal (T a)).subschemeι 1 (hdT a)
      (fun _ => (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c))
      (fun t => (Scheme.Modules.pullback ιP).obj (L t.succ))
      (fun t => (Scheme.Modules.pullback ιP).mapIso (eL t).symm),
    ← sheafIntersectionNumber_comp_eq_of_iso k sZ ι
      ((Scheme.IdealSheafData.vanishingIdeal (T a)).subschemeι ≫ ιP) 1 (hdT a)
      (fun _ => MMP.CartierDivisor.sheaf c) _ (fun _ => Iso.refl _),
    sheafIntersectionNumber_eq_of_ker_eq k sZ _ _ (hker a) 1 (hdT a) (hdim a.1 a.2),
    curveNum_eq]

open Classical in
/-- **(3, transversal case on a double surface) `(ε_l · c · S) = ∑_{T ⊆ S} (c · T)`** for a
double surface `σ` of `(Eᵢ, Eⱼ)` and a third component `E_l`: `E_l|_S` is a reduced effective
Cartier divisor on `S` whose support is the disjoint union of the triple curves `T ⊆ S` of
`Eᵢ ∩ Eⱼ ∩ E_l`. -/
private theorem surfNum_eps_transversal (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [NoetherianSpace Z] (hvar : Mori.IsVariety k sZ)
    (hsm : IsSmoothScheme sZ) {B : Divisor Z}
    (hB : B.IsSNC sZ) [LinearOrder B.support] (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (hS : ∀ σ : DoubleSurface B, topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subscheme ≤ (2 : ℕ))
    (hT : ∀ i j l : B.support, i < j → j < l →
      ∀ T ⊆ i.1.support ∩ j.1.support ∩ l.1.support, topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ))
    (σ : DoubleSurface B) (l : B.support) (hl₁ : l ≠ fstS σ) (hl₂ : l ≠ sndS σ)
    (c : Z.CartierDivisor) :
    surfNum k sZ σ.carrier (ε l) c =
      ∑ T ∈ tcs σ.fst σ.snd l.1, if T ⊆ σ.carrier then curveNum k sZ T c else 0 := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set b : B.support := fstS σ
  set ι := σ.fst.idealSheaf.subschemeι
  have : IsLocallyNoetherian σ.fst.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ι
  set P := rho hB σ
  set ιP := P.idealSheaf.subschemeι
  have := P.integral
  have hker : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subschemeι.ker =
      (ιP ≫ ι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      range_comp_rho hB σ]
  have hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ) := by
    have := IsClosedImmersion.isIso_lift _ _ hker
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (Scheme.homeoOfIso (asIso (IsClosedImmersion.lift _ _ hker.le))).isHomeomorph]
    exact hS σ
  have hL : ∀ t : Fin 2, SheafOfModules.IsInvertible σ.fst.idealSheaf.subscheme.presheaf
      σ.fst.idealSheaf.subscheme.ringCatSheaf.2
      (![(Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf (ε l)),
        (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)] t) :=
    fun t => by fin_cases t <;> exact isInvertible_pullback_obj _ _
  set G := l.1.idealSheaf.comap ι
  have : Stacks.Divisors.IsEffectiveCartierDivisor G :=
    (isEffectiveCartierDivisor_comap_component hB hl₁).1
  have hsnc : MMP.Resolution.HasSNCWith (fun _ : Unit => G) P.idealSheaf :=
    hasSNCWith_rhoOf hB b σ rfl G l hl₁ fun x hx => ⟨hx, rfl⟩
  have hPl : ¬ (P.support : Set _) ⊆ (G.support : Set _) := by
    intro hsub
    refine not_carrier_subset_support hB σ l hl₁ hl₂ ?_
    rw [← image_support_rho hB σ]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ((l.1.idealSheaf.comap ι).support : Set _) := hsub hy
    rw [Scheme.IdealSheafData.support_comap] at hy'
    exact hy'
  have hG : ∀ y ∈ (G.comap ιP).support, ∃ (m : ℕ)
      (w : Fin m → P.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (G.comap ιP) y = Ideal.span {w j} := by
    intro y hy
    obtain ⟨m, w, c', hw, hc, -⟩ :=
      MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hsnc
        (fun _ => not_component_subset_of_not_support_subset P G hPl) y
    exact ⟨m, w, c' ⟨(), hy⟩, hw, hc ⟨(), hy⟩⟩
  set s := (tcs σ.fst σ.snd l.1).filter (· ⊆ σ.carrier)
  have hιP : ∀ y : P.idealSheaf.subscheme, ι (ιP y) ∈ σ.carrier := by
    intro y
    rw [← image_support_rho hB σ]
    refine ⟨ιP y, ?_, rfl⟩
    change ιP y ∈ (P.idealSheaf.support : Set _)
    rw [← P.idealSheaf.range_subschemeι]
    exact ⟨y, rfl⟩
  rw [← surfNum_eq k sZ _ _ _ (hS σ),
    sheafIntersectionNumber_eq_of_ker_eq k sZ _ (ιP ≫ ι) hker 2 (hS σ) hP2,
    sheafIntersectionNumber_comp_eq_of_iso k sZ ι ιP 2 hP2 _
      ![(Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf (ε l)),
        (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)]
      (fun t => match t with | 0 => Iso.refl _ | 1 => Iso.refl _),
    sheafIntersectionNumber_eq_sum_curveNum k sZ P hP2 _ G
      (nonempty_pullback_eps_iso k sZ hvar hsm hB ε hε hl₁).some c (Iso.refl _) hG s ?_ ?_ ?_ ?_ ?_,
    Finset.sum_filter]
  · rw [← carrier_inter_support_eq_biUnion σ l.1]
    change ((l.1.idealSheaf.comap ι).comap ιP).support.1 = _
    ext y
    simp only [Scheme.IdealSheafData.support_comap, Set.mem_preimage, Set.mem_inter_iff]
    exact ⟨fun h => ⟨hιP y, h⟩, fun h => h.2⟩
  · intro a ha a' ha' hne
    exact IsTripleCurve.disjoint (mem_tcs.1 (Finset.mem_filter.1 ha).1)
      (mem_tcs.1 (Finset.mem_filter.1 ha').1) hne
  · exact fun a ha => (mem_tcs.1 (Finset.mem_filter.1 ha).1).isClosed
  · intro a ha
    rw [image_support_rho hB σ]
    exact (Finset.mem_filter.1 ha).2
  · intro a ha
    exact dim_le_one_of_ne hT (fun e => σ.fst_ne_snd (congrArg Subtype.val e)) hl₁.symm
      hl₂.symm (mem_tcs.1 (Finset.mem_filter.1 ha).1).2.1

open Classical in
/-- **(3, transversal case on a component)
`(π_{ρσ} · π_{ρτ} · c|)_{Eᵢ} = ∑_{T ⊆ S_σ ∩ S_τ} (c · T)`**
for double surfaces `σ` of `(Eᵢ, Eⱼ)` and `τ` of `(Eᵢ, E_l)`, `j ≠ l`: `π_{ρτ}|_{ρσ}` is a
reduced effective Cartier divisor on `ρσ` whose support is the disjoint union of the triple curves
`T ⊆ S_σ ∩ S_τ`. -/
private theorem xNum_rhoOf_transversal (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsProper sZ] [NoetherianSpace Z] {B : Divisor Z}
    (hB : B.IsSNC sZ) [LinearOrder B.support]
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1))
    (hE : ∀ i : B.support, topologicalKrullDim i.1.idealSheaf.subscheme ≤ (3 : ℕ))
    (hT : ∀ i j l : B.support, i < j → j < l →
      ∀ T ⊆ i.1.support ∩ j.1.support ∩ l.1.support, topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ))
    (i : B.support) (σ τ : DoubleSurface B) (h : σ.fst = i.1) (h' : τ.fst = i.1)
    (hne : σ.snd ≠ τ.snd) (c : Z.CartierDivisor) :
    xNum k sZ π i (rhoOf hB σ h) (rhoOf hB τ h') c =
      ∑ T ∈ tcs i.1 σ.snd τ.snd,
        if T ⊆ σ.carrier ∧ T ⊆ τ.carrier then curveNum k sZ T c else 0 := by
  classical
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set ι := i.1.idealSheaf.subschemeι
  have : IsLocallyNoetherian i.1.idealSheaf.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion ι
  set P := rhoOf hB σ h
  set Q := rhoOf hB τ h'
  set ιP := P.idealSheaf.subschemeι
  have := P.integral
  obtain ⟨hPe, hPsub⟩ := exists_isEffective_pi k sZ hB π hπ i P
  obtain ⟨hQe, hQsub⟩ := exists_isEffective_pi k sZ hB π hπ i Q
  set D := MMP.CartierDivisor.subscheme (π i P) hPe
  have hD2 := topologicalKrullDim_subscheme_le_of_isEffective k (ι ≫ sZ) (𝟙 _) 2 (hE i) _ hPe
  have : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    hPsub ▸ MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hPe
  have : Stacks.Divisors.IsEffectiveCartierDivisor Q.idealSheaf :=
    hQsub ▸ MMP.CartierDivisor.isEffectiveCartierDivisor_subscheme hQe
  have hP2 : topologicalKrullDim P.idealSheaf.subscheme ≤ (2 : ℕ) :=
    topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k (ι ≫ sZ) (𝟙 _) 2
      (hE i) P.idealSheaf
  have hL : ∀ t : Fin 2, SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf (π i P),
        MMP.CartierDivisor.sheaf (π i Q),
        (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)] t.succ) :=
    fun t => by
      fin_cases t
      exacts [isInvertible_cartierSheaf _, isInvertible_pullback_obj _ _]
  have hL3 : ∀ t : Fin (2 + 1), SheafOfModules.IsInvertible i.1.idealSheaf.subscheme.presheaf
      i.1.idealSheaf.subscheme.ringCatSheaf.2
      (![MMP.CartierDivisor.sheaf (π i P),
        MMP.CartierDivisor.sheaf (π i Q),
        (Scheme.Modules.pullback ι).obj (MMP.CartierDivisor.sheaf c)] t) :=
    fun t => by
      fin_cases t
      exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
        isInvertible_pullback_obj _ _]
  have hgb : (sndS τ) ≠ i := fun e => τ.fst_ne_snd (h'.trans (congrArg Subtype.val e).symm)
  have hsnc : MMP.Resolution.HasSNCWith (fun _ : Unit => Q.idealSheaf) P.idealSheaf :=
    hasSNCWith_rhoOf hB i σ h Q.idealSheaf (sndS τ) hgb fun x hx =>
      ⟨mem_support_comap_snd_of_mem_rhoOf hB τ h' hx, stalk_rhoOf hB τ h' hx⟩
  have hPQ : P ≠ Q := fun e => hne (congrArg DoubleSurface.snd (rhoOf_injective hB h h' e))
  have hG : ∀ y ∈ (Q.idealSheaf.comap ιP).support, ∃ (m : ℕ)
      (w : Fin m → P.idealSheaf.subscheme.presheaf.stalk y) (j : Fin m),
      Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (Q.idealSheaf.comap ιP) y = Ideal.span {w j} := by
    intro y hy
    obtain ⟨m, w, c', hw, hc, -⟩ :=
      MMP.Resolution.exists_coordinates_comap_subschemeι_of_hasSNCWith hsnc
        (fun _ => not_component_subset_of_not_support_subset P Q.idealSheaf
          (not_support_subset_of_ne hPQ)) y
    exact ⟨m, w, c' ⟨(), hy⟩, hw, hc ⟨(), hy⟩⟩
  set s := (tcs i.1 σ.snd τ.snd).filter (fun T => T ⊆ σ.carrier ∧ T ⊆ τ.carrier)
  have hιP : ∀ y : P.idealSheaf.subscheme, ι (ιP y) ∈ σ.carrier := by
    intro y
    rw [← image_support_rhoOf hB σ h]
    refine ⟨ιP y, ?_, rfl⟩
    change ιP y ∈ (P.idealSheaf.support : Set _)
    rw [← P.idealSheaf.range_subschemeι]
    exact ⟨y, rfl⟩
  have hQS : (Q.support : Set _) = ι ⁻¹' τ.carrier := by
    rw [← image_support_rhoOf hB τ h', Set.preimage_image_eq _ ι.isClosedEmbedding.injective]
  rw [← xNum_eq k sZ π i P Q c (hE i),
    sheafIntersectionNumber_eq_of_isEffective k (ι ≫ sZ) (𝟙 _) 2 (hE i) _ (π i P) hPe
      ((Scheme.Modules.pullbackId _).app _),
    sheafIntersectionNumber_eq_of_ker_eq k (ι ≫ sZ) (D.subschemeι ≫ 𝟙 _) ιP
      (by rw [Category.comp_id, Scheme.IdealSheafData.ker_subschemeι,
        Scheme.IdealSheafData.ker_subschemeι, hPsub]) 2 hD2 hP2,
    sheafIntersectionNumber_eq_sum_curveNum k sZ P hP2 _ Q.idealSheaf
      (MMP.CartierDivisor.sheafIsoInvertibleSheaf (π i Q) hQe ≪≫
        eqToIso (congrArg Stacks.Divisors.invertibleSheaf' hQsub)) c (Iso.refl _) hG s
      ?_ ?_ ?_ ?_ ?_,
    Finset.sum_filter]
  · rw [← carrier_inter_carrier_eq_biUnion σ τ h h']
    change (Q.idealSheaf.comap ιP).support.1 = _
    ext y
    simp only [Scheme.IdealSheafData.support_comap, Set.mem_preimage, Set.mem_inter_iff]
    change ιP y ∈ (Q.support : Set _) ↔ _
    rw [hQS]
    exact ⟨fun h => ⟨hιP y, h⟩, fun h => h.2⟩
  · intro a ha a' ha' hne
    exact IsTripleCurve.disjoint (mem_tcs.1 (Finset.mem_filter.1 ha).1)
      (mem_tcs.1 (Finset.mem_filter.1 ha').1) hne
  · exact fun a ha => (mem_tcs.1 (Finset.mem_filter.1 ha).1).isClosed
  · intro a ha
    rw [image_support_rhoOf hB σ h]
    exact (Finset.mem_filter.1 ha).2.1
  · intro a ha
    refine dim_le_one_of_ne hT (x := i) (y := sndS σ) (z := sndS τ)
      (fun e => σ.fst_ne_snd (h.trans (congrArg Subtype.val e))) (Ne.symm hgb)
      (fun e => hne (congrArg Subtype.val e)) (mem_tcs.1 (Finset.mem_filter.1 ha).1).2.1

/-! ### The dimensions of the strata of an snc divisor on a fourfold -/

/-- **A closed set of points of codimension at least `r`.** On an integral scheme `Y` of finite
type over a field, of dimension `n`, a closed set all of whose points have coheight at least `r`
has dimension at most `n - r`. -/
theorem topologicalKrullDim_le_sub_of_le_coheight (k : Type) [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {n r : ℕ}
    (hY : topologicalKrullDim Y = n) {C : Set Y} (hC : IsClosed C)
    (h : ∀ y ∈ C, (r : ℕ∞) ≤ Order.coheight y) :
    topologicalKrullDim C ≤ ((n - r : ℕ) : WithBot ℕ∞) := by
  refine topologicalKrullDim_le_of_forall_closure hC fun y hy => ?_
  let _ : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have hdc := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint y)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at hdc
  change topologicalKrullDim (closure {y} : Set Y) + Order.coheight y = topologicalKrullDim Y at hdc
  rw [hY] at hdc
  have hle : topologicalKrullDim (closure {y} : Set Y) ≤ n :=
    (topologicalKrullDim_subspace_le Y _).trans hY.le
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim (closure {y} : Set Y) = d := by
    induction h' : topologicalKrullDim (closure {y} : Set Y) using WithBot.recBotCoe with
    | bot => rw [h'] at hdc; simp at hdc
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => rw [h'] at hle; exact absurd (WithBot.coe_le_coe.1 hle) (by simp)
      | coe a => exact ⟨a, rfl⟩
  rw [hd] at hdc ⊢
  have hc := h y hy
  induction hco : Order.coheight y using ENat.recTopCoe with
  | top =>
    rw [hco] at hdc
    have : ((d : ℕ∞) + ⊤ : ℕ∞) = n := by exact_mod_cast hdc
    simp at this
  | coe c =>
    rw [hco] at hdc hc
    have : d + c = n := by exact_mod_cast hdc
    have : r ≤ c := by exact_mod_cast hc
    exact_mod_cast (by omega : d ≤ n - r)

/-- **A point on `r` components of an snc divisor has codimension at least `r`.** If `x` lies on
`r` distinct components of `B` (`f` injective), then `r ≤ coheight x`. -/
theorem le_coheight_of_isSNC {k : Type} [Field k] {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)}
    {B : Divisor Z} (hB : B.IsSNC sZ) {r : ℕ} (f : Fin r → B.support)
    (hf : Function.Injective f) {x : Z} (hx : ∀ t, x ∈ (f t).1.support) :
    (r : ℕ∞) ≤ Order.coheight x := by
  obtain ⟨n, z, j, hz, hj, -⟩ := hB.2 x
  let g : Fin r → Fin n := fun t => j ⟨(f t).1, (f t).2, hx t⟩
  have hg : Function.Injective g := fun a b hab => hf (Subtype.ext (by simpa using hj hab))
  have hrn : r ≤ n := by simpa using Fintype.card_le_of_injective g hg
  have h2 := hz.2
  rw [ringKrullDim_stalk_eq_coheight] at h2
  rw [show Order.coheight x = n by exact_mod_cast h2]
  exact_mod_cast hrn

/-- On a fourfold `Z` of finite type over `k` with an snc divisor `B`, a closed subscheme whose
support lies in `r` distinct components of `B` has dimension at most `4 - r`. -/
theorem topologicalKrullDim_subscheme_le_of_isSNC (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) [IsIntegral Z] [LocallyOfFiniteType sZ]
    (hZ : topologicalKrullDim Z = 4) {B : Divisor Z} (hB : B.IsSNC sZ) {r : ℕ}
    (f : Fin r → B.support) (hf : Function.Injective f) (I : Z.IdealSheafData)
    (hI : (I.support : Set Z) ⊆ ⋂ t, (f t).1.support) :
    topologicalKrullDim I.subscheme ≤ ((4 - r : ℕ) : WithBot ℕ∞) := by
  rw [I.subschemeι.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq,
    show Set.range I.subschemeι = (I.support : Set Z) from I.range_subschemeι]
  exact topologicalKrullDim_le_sub_of_le_coheight k sZ hZ I.support.isClosed fun y hy =>
    le_coheight_of_isSNC hB f hf fun t => Set.mem_iInter.1 (hI hy) t

/-- A component `Eᵢ` of an snc divisor on a fourfold variety has dimension at most `3`. -/
theorem topologicalKrullDim_component_le (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) (hvar : Mori.IsVariety k sZ) (hZ : topologicalKrullDim Z = 4)
    {B : Divisor Z} (hB : B.IsSNC sZ) (i : B.support) :
    topologicalKrullDim i.1.idealSheaf.subscheme ≤ (3 : ℕ) :=
  haveI := hvar
  topologicalKrullDim_subscheme_le_of_isSNC k sZ hZ hB (r := 1) (fun _ => i)
    (fun a b _ => Subsingleton.elim a b) _ fun _ hy => Set.mem_iInter.2 fun _ => hy

/-- A double surface `S ⊆ Eᵢ ∩ Eⱼ` of an snc divisor on a fourfold variety, with its reduced
structure, has dimension at most `2`. -/
theorem topologicalKrullDim_doubleSurface_le (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) (hvar : Mori.IsVariety k sZ) (hZ : topologicalKrullDim Z = 4)
    {B : Divisor Z} (hB : B.IsSNC sZ) (σ : DoubleSurface B) :
    topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subscheme ≤ (2 : ℕ) := by
  have := hvar
  have hne : (⟨σ.fst, σ.fst_mem⟩ : B.support) ≠ ⟨σ.snd, σ.snd_mem⟩ :=
    fun h => σ.fst_ne_snd (congrArg Subtype.val h)
  refine topologicalKrullDim_subscheme_le_of_isSNC k sZ hZ hB (r := 2)
    ![⟨σ.fst, σ.fst_mem⟩, ⟨σ.snd, σ.snd_mem⟩] ?_ _ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab hne | exact absurd hab.symm hne
  · rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    refine closure_minimal (fun y hy => ?_) (isClosed_iInter fun t => ?_)
    · have := σ.carrier_subset hy
      exact Set.mem_iInter.2 fun t => by fin_cases t; exacts [this.1, this.2]
    · exact (![(⟨σ.fst, σ.fst_mem⟩ : B.support), ⟨σ.snd, σ.snd_mem⟩] t).1.idealSheaf.support
        |>.isClosed

/-- A subset `T` of a triple intersection `Eᵢ ∩ Eⱼ ∩ Eₗ` (`i < j < l`) of an snc divisor on a
fourfold variety, its closure given the reduced structure, has dimension at most `1`. -/
theorem topologicalKrullDim_tripleCurve_le (k : Type) [Field k] {Z : Scheme.{0}}
    (sZ : Z ⟶ Spec (.of k)) (hvar : Mori.IsVariety k sZ) (hZ : topologicalKrullDim Z = 4)
    {B : Divisor Z} (hB : B.IsSNC sZ) [LinearOrder B.support] (i j l : B.support)
    (hij : i < j) (hjl : j < l) (T : Set Z) (hT : T ⊆ i.1.support ∩ j.1.support ∩ l.1.support) :
    topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subscheme ≤ (1 : ℕ) := by
  have := hvar
  refine topologicalKrullDim_subscheme_le_of_isSNC k sZ hZ hB (r := 3) ![i, j, l] ?_ _ ?_
  · intro a b hab
    have h1 := hij.ne; have h2 := (hij.trans hjl).ne; have h3 := hjl.ne
    fin_cases a <;> fin_cases b <;> simp_all
  · rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    refine closure_minimal (fun y hy => ?_) (isClosed_iInter fun t => ?_)
    · have := hT hy
      exact Set.mem_iInter.2 fun t => by fin_cases t; exacts [this.1.1, this.1.2, this.2]
    · exact (![i, j, l] t).1.idealSheaf.support.isClosed

/-- **The weighted surface intersection identity.** On a smooth projective fourfold `Z` with a
reduced snc divisor `B = ∑ᵢ Eᵢ`, an oriented surface coefficient system `a`, weights `mᵢ > 0`
with `D = ∑ᵢ mᵢ Eᵢ` and `b_{ij,S} = a_{ij,S} / (mᵢ mⱼ)`, and any `ℚ`-Cartier divisor `H`:
`∑_{i<j} ∑_S mᵢ mⱼ b_{ij,S}² (D · S · H)` equals
`∑ᵢ (Zᵢ(a)² · H|_{Eᵢ}) / mᵢ + ∑_{i<j<k} ∑_T mᵢ mⱼ mₖ (b_{ij,T} - b_{ik,T} + b_{jk,T})² (T · H)`,
`S` running over the connected components of `Eᵢ ∩ Eⱼ` and `T` over those of `Eᵢ ∩ Eⱼ ∩ Eₖ`.
Here `εᵢ` and `π_P` are the Cartier divisors of `Eᵢ` and of the prime divisors `P` of `Eᵢ`. -/
@[mmp "lem_mmp_conductor_weighted_surface_identity"]
public theorem sum_sq_mul_intersectionNumber_doubleSurface_eq
    (k : Type) [Field k] {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of k)) [IsProper sZ]
    (hvar : Mori.IsVariety k sZ) (hsm : IsSmoothScheme sZ) (hproj : IsProjectiveMorphism sZ)
    (hZ : topologicalKrullDim Z = 4)
    (B : Divisor Z) (hBred : ∀ E ∈ B.support, B E = 1) (hB : B.IsSNC sZ)
    [LinearOrder B.support]
    (a : DoubleSurface B → ℚ) (ha : a ∈ orientedSurfaceCoefficients B)
    (m : B.support → ℚ) (hm : ∀ i, 0 < m i)
    (H : KCartierDivisor ℚ Z)
    (ε : B.support → Z.CartierDivisor)
    (hε : ∀ i, MMP.Intersection.IsWeilDivisorOfCartier (ε i) (Finsupp.single i.1 1))
    (π : ∀ i : B.support, Mori.PrimeDivisor i.1.idealSheaf.subscheme →
      i.1.idealSheaf.subscheme.CartierDivisor)
    (hπ : ∀ i P, MMP.Intersection.IsWeilDivisorOfCartier (π i P) (Finsupp.single P 1)) :
    (∑ᶠ (σ : DoubleSurface B)
        (_ : (⟨σ.fst, σ.fst_mem⟩ : B.support) < ⟨σ.snd, σ.snd_mem⟩),
        m ⟨σ.fst, σ.fst_mem⟩ * m ⟨σ.snd, σ.snd_mem⟩ *
          (a σ / (m ⟨σ.fst, σ.fst_mem⟩ * m ⟨σ.snd, σ.snd_mem⟩)) ^ 2 *
          ∑ l : B.support, m l * H.sum fun c h => h *
            (sheafIntersectionNumber k sZ
              (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure σ.carrier)).subschemeι 2
              (topologicalKrullDim_doubleSurface_le k sZ hvar hZ hB σ)
              (fun t => MMP.CartierDivisor.sheaf (![ε l, c] t)) : ℚ)) =
      (∑ i : B.support, (1 / m i) *
        (surfaceCoefficientDivisor a i.1).sum fun P cP =>
          (surfaceCoefficientDivisor a i.1).sum fun Q cQ => H.sum fun c h => cP * cQ * h *
            (@sheafIntersectionNumber k _ _ _ (i.1.idealSheaf.subschemeι ≫ sZ) _ (𝟙 _) _ 3
              (topologicalKrullDim_component_le k sZ hvar hZ hB i)
              ![MMP.CartierDivisor.sheaf (π i P),
                MMP.CartierDivisor.sheaf (π i Q),
                (Scheme.Modules.pullback i.1.idealSheaf.subschemeι).obj
                  (MMP.CartierDivisor.sheaf c)]
              (fun t => by
                fin_cases t
                exacts [isInvertible_cartierSheaf _, isInvertible_cartierSheaf _,
                  isInvertible_pullback_obj _ _]) : ℚ)) +
      ∑ i : B.support, ∑ j : B.support, ∑ l : B.support,
        if hij : i < j then if hjl : j < l then
          ∑ᶠ (T : Set Z) (hT' : T.Nonempty ∧ T ⊆ i.1.support ∩ j.1.support ∩ l.1.support ∧
              ∃ x ∈ i.1.support ∩ j.1.support ∩ l.1.support,
                connectedComponentIn (i.1.support ∩ j.1.support ∩ l.1.support) x = T),
            m i * m j * m l *
              (coeffAlong a i.2 j.2 (fun h => hij.ne (Subtype.ext h)) hT'.1
                  (fun y hy => (hT'.2.1 hy).1) / (m i * m j) -
                coeffAlong a i.2 l.2 (fun h => (hij.trans hjl).ne (Subtype.ext h)) hT'.1
                  (fun y hy => ⟨(hT'.2.1 hy).1.1, (hT'.2.1 hy).2⟩) / (m i * m l) +
                coeffAlong a j.2 l.2 (fun h => hjl.ne (Subtype.ext h)) hT'.1
                  (fun y hy => ⟨(hT'.2.1 hy).1.2, (hT'.2.1 hy).2⟩) / (m j * m l)) ^ 2 *
              H.sum fun c h => h *
                (sheafIntersectionNumber k sZ
                  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure T)).subschemeι 1
                  (topologicalKrullDim_tripleCurve_le k sZ hvar hZ hB i j l hij hjl T hT'.2.1)
                  (fun _ => MMP.CartierDivisor.sheaf c) : ℚ)
        else 0 else 0 := by
  classical
  have hS := topologicalKrullDim_doubleSurface_le k sZ hvar hZ hB
  have hE := topologicalKrullDim_component_le k sZ hvar hZ hB
  have hT := topologicalKrullDim_tripleCurve_le k sZ hvar hZ hB
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have : IsNoetherian Z := ⟨⟩
  have := DoubleSurface.finite (B := B)
  let _ : Fintype (DoubleSurface B) := Fintype.ofFinite _
  have hcore := fun c : Z.CartierDivisor => core_identity hB a ha m hm
    (fun S l => surfNum k sZ S (ε l) c) (fun i P Q => xNum k sZ π i P Q c)
    (fun T => curveNum k sZ T c)
    (fun σ => surfNum_eps_snd k sZ hvar hsm hB ε hε π hπ hS hE σ c)
    (fun σ l h1 h2 => surfNum_eps_transversal k sZ hvar hsm hB ε hε hS hT σ l h1 h2 c)
    (fun i σ τ h h' h2 hne => xNum_rhoOf_eq_zero k sZ hB π hπ i h h' h2 hne c)
    (fun i σ τ h h' hne =>
      xNum_rhoOf_transversal k sZ hB π hπ hE hT i σ τ h h' hne c)
  have hH : ∀ g : Z.CartierDivisor → ℚ → ℚ, H.sum g = ∑ c ∈ H.support, g c (H c) := fun g => rfl
  rw [finsum_eq_sum_of_fintype]
  trans (∑ i : B.support, (1 / m i) * (surfaceCoefficientDivisor a i.1).sum (fun P cP =>
        (surfaceCoefficientDivisor a i.1).sum fun Q cQ => H.sum fun c h => cP * cQ * h *
          xNum k sZ π i P Q c)) +
      ∑ i : B.support, ∑ j : B.support, ∑ l : B.support, (if i < j ∧ j < l then
        ∑ T ∈ tcs i.1 j.1 l.1, m i * m j * m l *
          (coeffT a i j T / (m i * m j) - coeffT a i l T / (m i * m l) +
            coeffT a j l T / (m j * m l)) ^ 2 * H.sum (fun c h => h * curveNum k sZ T c) else 0)
  · simp only [finsum_eq_if, surfNum_eq, hH]
    rw [sum_ite_mul_sum_eq H.support (fun c => H c) (fun σ : DoubleSurface B => fstS σ < sndS σ)
        (fun σ => m (fstS σ) * m (sndS σ) * (a σ / (m (fstS σ) * m (sndS σ))) ^ 2) m
        (fun (σ : DoubleSurface B) l c => surfNum k sZ σ.carrier (ε l) c),
      sum_finsupp_sum_mul_eq H.support (fun c => H c) (fun i => 1 / m i)
        (fun i => surfaceCoefficientDivisor a i.1) (xNum k sZ π)]
    simp only [hcore, mul_add, Finset.sum_add_distrib]
    congr 1
    exact (sum_ite_sum_mul_eq H.support (fun c => H c) (fun i j l => i < j ∧ j < l)
      (fun i j l => tcs i.1 j.1 l.1) (fun i j l T => m i * m j * m l *
        (coeffT a i j T / (m i * m j) - coeffT a i l T / (m i * m l) +
          coeffT a j l T / (m j * m l)) ^ 2) (curveNum k sZ)).symm
  · congr 1
    · simp only [xNum_eq]
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => ?_
      by_cases hij : i < j
      · by_cases hjl : j < l
        · rw [dite_eq_left hij, dite_eq_left hjl, ite_eq_left ⟨hij, hjl⟩,
            ← finsum_isTripleCurve_eq_sum]
          refine finsum_congr fun T => finsum_congr fun hT' => ?_
          have e1 := coeffAlong_eq_coeffT a i j (fun h => hij.ne (Subtype.ext h)) hT'.1
            (fun y hy => (hT'.2.1 hy).1)
          have e2 := coeffAlong_eq_coeffT a i l (fun h => (hij.trans hjl).ne (Subtype.ext h)) hT'.1
            (fun y hy => ⟨(hT'.2.1 hy).1.1, (hT'.2.1 hy).2⟩)
          have e3 := coeffAlong_eq_coeffT a j l (fun h => hjl.ne (Subtype.ext h)) hT'.1
            (fun y hy => ⟨(hT'.2.1 hy).1.2, (hT'.2.1 hy).2⟩)
          simp only [e1, e2, e3, curveNum_eq]
        · rw [dite_eq_left hij, dite_eq_right hjl, ite_eq_right fun h => hjl h.2]
      · rw [dite_eq_right hij, ite_eq_right fun h => hij h.1]

end MMP.Fourfold

/-! ### Collars and finite homotopy models for compact manifolds with corners -/

namespace MMP

open Set
open scoped Manifold ContDiff

section Corners

variable {ι : Type*} [Finite ι] {n : ι → ℕ} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (EuclideanQuadrant (n i)) (M i)]
  [∀ i, IsManifold (modelWithCornersEuclideanQuadrant (n i)) ∞ (M i)]
  [∀ i, CompactSpace (M i)] [∀ i, T2Space (M i)]

include n in
/-- The finite disjoint union has the homotopy type of a finite polyhedron: a Whitney embedding
of each summand has an image of positive reach, which is homotopy equivalent to the nerve of a
finite cover by balls. -/
private theorem exists_homotopyEquiv_finite_simplicialComplex :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
        K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv (Σ i, M i) K.space) := by
  choose N e he hemb hinj using fun i ↦
    exists_embedding_euclidean_of_compact (I := modelWithCornersEuclideanQuadrant (n i)) (M := M i)
  refine MMP.Topology.exists_homotopyEquiv_simplicialComplex_sigma_of_nearestPoint
    (fun i ↦ range (e i)) (fun i ↦ ⟨(hemb i).isEmbedding.toHomeomorph.toHomotopyEquiv⟩)
    (fun i ↦ isCompact_range (hemb i).continuous) fun i ↦ ?_
  obtain ⟨τ, hτ, hu⟩ := MMP.Topology.exists_hasUniqueNearestPoints_range
    ((he i).of_le (by norm_cast)) (hemb i).isEmbedding (hinj i)
  exact ⟨τ, hτ, hu.exists_nearestPoint (hemb i).isClosed_range⟩

/-- The boundary has the homotopy type of a finite polyhedron: each summand's boundary is
homotopy equivalent to a compact set of positive reach, which is homotopy equivalent to the
nerve of a finite cover by balls. -/
private theorem exists_homotopyEquiv_boundary_finite_simplicialComplex :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
        K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv
          {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)}
          K.space) := by
  set g : (Σ i, (modelWithCornersEuclideanQuadrant (n i)).boundary (M i)) → Σ i, M i :=
    Sigma.map id fun _ x ↦ x.1 with hg
  have hge : Topology.IsEmbedding g :=
    (Topology.isEmbedding_sigmaMap Function.injective_id).2 fun _ ↦ Topology.IsEmbedding.subtypeVal
  have hrange : range g =
      {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} := by
    ext ⟨i, x⟩
    constructor
    · rintro ⟨⟨j, y⟩, hy⟩
      simp only [hg, Sigma.map, id] at hy
      obtain ⟨rfl, hy⟩ := Sigma.mk.inj_iff.1 hy
      obtain rfl := eq_of_heq hy
      exact y.2
    · exact fun hx => ⟨⟨i, x, hx⟩, rfl⟩
  have hhom := hge.toHomeomorph.trans (Homeomorph.setCongr hrange)
  choose N A hA hreach hX using fun i ↦
    MMP.Topology.exists_isCompact_hasUniqueNearestPoints_homotopyEquiv_boundary (n := n i)
      (M := M i)
  obtain ⟨Nn, K, hK, ⟨eK⟩⟩ :=
    MMP.Topology.exists_homotopyEquiv_simplicialComplex_sigma_of_nearestPoint A hX hA fun i ↦ by
      obtain ⟨τ, hτ, hu⟩ := hreach i
      exact ⟨τ, hτ, hu.exists_nearestPoint (hA i).isClosed⟩
  exact ⟨Nn, K, hK, ⟨hhom.symm.toHomotopyEquiv.trans eK⟩⟩

/-- The boundary has a collar, by Brown's collaring theorem applied to local collars. -/
private theorem exists_collar :
    ∃ c : {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} ×
        Set.Ico (0 : ℝ) 1 → Σ i, M i,
      Topology.IsOpenEmbedding c ∧ ∀ x (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x := by
  refine MMP.Topology.exists_collar_of_locallyCollared
    (isClosed_sigma_iff.2 fun i ↦ ModelWithCorners.isClosed_boundary
      (I := modelWithCornersEuclideanQuadrant (n i)) (M := M i) (n := ∞) (by simp)) ?_
  rintro ⟨i, x⟩ hx
  obtain ⟨Z, tZ, d, hd, hd0, hdB, ⟨q, hq⟩⟩ :=
    MMP.Topology.exists_localCollar_boundary (k := ∞) (by simp) hx
  exact ⟨Z, tZ, Sigma.mk i ∘ d, Topology.IsOpenEmbedding.sigmaMk.comp hd,
    fun z t ht ↦ hd0 z t ht, fun p hp ↦ hdB p hp, ⟨q, by simp [hq]⟩⟩

end Corners

/-- **Collars and finite homotopy models for compact manifolds with corners.** Let
`X = Σ i, M i` be a finite disjoint union of compact Hausdorff smooth manifolds with
corners, `M i` modelled on the quadrant of dimension `n i`, with boundary `∂X`. Then `X` and
`∂X` are each homotopy equivalent to the underlying space of a finite simplicial complex in a
Euclidean space, and there is an open embedding `c : ∂X × [0, 1) → X` with `c (x, 0) = x`. -/
@[mmp "lem_mmp_compact_corners_finite_homotopy"]
public theorem exists_collar_and_homotopyEquiv_finite_simplicialComplex
    {ι : Type*} [Finite ι] {n : ι → ℕ} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
    [∀ i, ChartedSpace (EuclideanQuadrant (n i)) (M i)]
    [∀ i, IsManifold (modelWithCornersEuclideanQuadrant (n i)) ∞ (M i)]
    [∀ i, CompactSpace (M i)] [∀ i, T2Space (M i)] :
    (∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
        K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv (Σ i, M i) K.space)) ∧
    (∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))),
        K.faces.Finite ∧ Nonempty (ContinuousMap.HomotopyEquiv
          {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)}
          K.space)) ∧
    ∃ c : {p : Σ i, M i | p.2 ∈ (modelWithCornersEuclideanQuadrant (n p.1)).boundary (M p.1)} ×
        Set.Ico (0 : ℝ) 1 → Σ i, M i,
      Topology.IsOpenEmbedding c ∧ ∀ x (t : Set.Ico (0 : ℝ) 1), (t : ℝ) = 0 → c (x, t) = x :=
  ⟨exists_homotopyEquiv_finite_simplicialComplex (n := n),
    exists_homotopyEquiv_boundary_finite_simplicialComplex, exists_collar⟩

end MMP
