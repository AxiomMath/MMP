module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ContractedEdgeInjectivity
import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.GlobalSections
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.FibreClassTransport
import MMP.AlgebraicGeometry.Analytic.NormalizationExcision
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ConductorKernel
import StacksFrontier.AlgebraicGeometry.Examples.NonEffectiveProjectiveDescent
import MMP.AlgebraicGeometry.ProjectiveSpace.LinearProjection
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Chow.CycleClassTopDegree
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenImmersionRange
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Removing a zero generic fibre class by double-surface edges

Let `r : Z ⟶ Y` be a curve-and-point exceptional model of a normal projective `ℚ`-factorial
terminal complex fourfold, with exceptional divisor `F = ∑ Fᵢ` and algebraic kernel `K(r)`.
Let `(Lᵢ)ᵢ` be `ℚ`-divisors on the components `Fᵢ` whose classes form an element of `K(r)`.
For a curve `T ⊆ Sing Y` and a general closed point `t ∈ T`, the `Lᵢ` cut on the surface fibre
`F_t = r⁻¹(t)` curves whose classes add up to `w_T(t) ∈ H_2(F_t, ℚ)`. If `w_T = 0` for every
`T`, then there is an oriented double-surface system `a`, supported on double surfaces mapping
onto curves of `Y`, such that the divisors `Lᵢ - Zᵢ(a)` still have classes in `K(r)` and each of
them has zero class on every component of a general surface fibre of `Fᵢ`.

## Main results

* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_mem_orientedSurfaceCoefficients_sub`.

## Implementation notes

* A general closed point of a curve `T` is a closed point of `U ∩ T` for an open `U ⊆ Y`
  meeting `T`; the open may depend on the divisors. The fibre `F_t` is the reduced closed
  subscheme of `Z` on `r⁻¹(t)`, which has the complex points of the scheme fibre.
* The curve cut on `F_t` (or on a component `G` of it) by a prime divisor `P` of `Fᵢ` is the sum
  of the irreducible components of `F_t ∩ P` (of `G ∩ P`), each with coefficient one. For `t`
  general the scheme-theoretic intersection is reduced, the ground field having characteristic
  zero, so this is the class of the restriction of `P`.
* For `t` general the components `G` of the fibre of `Fᵢ` over `t` are smooth projective
  surfaces, on which Poincaré duality identifies the rational Chern class
  `c₁(𝒪(Lᵢ)|_G) ∈ H²(G, ℚ)` with the class of the curve cut on `G` by `Lᵢ` in `H_2(G, ℚ)`. The
  vanishing of the Chern class is stated as the vanishing of that curve class.
* The double surfaces dominating the curves of `Y` are those whose image under `r` has
  dimension one.

* The proof works one general fibre at a time. Normalization excision for the union of the
  components `G` of `F_t` identifies the kernel of `⨁_G H_2(G, ℚ) → H_2(F_t, ℚ)` with the
  oriented coefficient vectors on the double curves. The double curves over `T` form a finite
  covering of a general open of `T`; averaging a solution over the monodromy of a connected
  component of the labellings makes it constant on the double surfaces dominating `T`, which
  gives the oriented system `a`. The classes of the divisors `Zᵢ(a)` of an oriented system lie
  in `K(r)`, their push-forwards to `Z` cancelling in pairs, so those of `Lᵢ - Zᵢ(a)` do too.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.Intersection.Scheme (Subvariety)
open MMP.Mori
open scoped MMP.SubschemeOver

namespace MMP.Fourfold

/-- The classes `([Zᵢ(a)])ᵢ` of an oriented double-surface system lie in `K(r)`: each is a
divisor class, and their push-forwards to `Z` cancel in pairs `(S ⊆ Eᵢ ∩ Eⱼ, S ⊆ Eⱼ ∩ Eᵢ)`. -/
private theorem surfaceCoefficientClasses_mem_algebraicKernel
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    {a : DoubleSurface F → ℚ} (ha : a ∈ orientedSurfaceCoefficients F) :
    surfaceCoefficientClasses F a ∈ algebraicKernel F := by
  have hres := hM.isResolution
  have : MMP.Mori.IsVariety ℂ sY := hres.1
  have hvar : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  have hdim : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  have : IsIntegral Z := hvar.toIsIntegral
  refine (mem_exceptionalKernel F).2 ⟨fun E => LinearMap.mem_range_self _ _, ?_⟩
  exact ConductorBlowup.sum_componentHomologyMap_divisorClass_eq_zero_of_topologicalKrullDim_eq_four
    hdim F a ha

/-- On a Noetherian scheme a divisor has finitely many double surfaces: finitely many ordered
pairs of components, and finitely many connected components of each double intersection. -/
private theorem finite_doubleSurface {X : Scheme.{0}} [NoetherianSpace X] (B : Divisor X) :
    Finite (DoubleSurface B) := by
  let 𝒮 : Set (Set X) := ⋃ p : B.support × B.support,
    {S | ∃ σ : DoubleSurface B, σ.fst = p.1.1 ∧ σ.snd = p.2.1 ∧ σ.carrier = S}
  have h𝒮 : 𝒮.Finite :=
    Set.finite_iUnion fun p => DoubleSurface.finite_setOf_carrier (B := B) p.1.1 p.2.1
  have := h𝒮.to_subtype
  refine Finite.of_injective (β := B.support × B.support × 𝒮)
    (fun σ => (⟨σ.fst, σ.fst_mem⟩, ⟨σ.snd, σ.snd_mem⟩,
      ⟨σ.carrier, Set.mem_iUnion.2 ⟨(⟨σ.fst, σ.fst_mem⟩, ⟨σ.snd, σ.snd_mem⟩),
        σ, rfl, rfl, rfl⟩⟩)) ?_
  intro σ τ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact DoubleSurface.ext h.1 h.2.1 h.2.2

/-! ### Edge labellings of the general fibres over a curve

For a curve `T ⊆ Sing Y` and a general closed point `y ∈ T`, the double curves of the fibre
`F_y` lying on a double surface `S ⊆ Eᵢ ∩ Eⱼ` dominating `T` are the irreducible components of
`S ∩ r⁻¹(y)`. An *edge index* is a finite set `I` of labels, each sent to a double surface
dominating `T` (every such surface being hit), with an involution `s` lifting `S ↦ S.swap`; an
*edge labelling* at `y` assigns to each label a double curve, bijectively over each double
surface, the labels `i` and `s i` getting the same curve. The labellings at the closed points of
`U ∩ T` carry the topology in which a labelling `(y, λ)` is close to `(y₀, λ₀)` when the fibre
over `y` and each curve `λ i` lie in given neighbourhoods of the fibre over `y₀` and of `λ₀ i`;
it is the topology of a finite covering of `(U ∩ T)(ℂ)`. -/

/-- The points of delta-dimension one of a scheme over `ℂ`: the generic points of its curves. -/
private abbrev CurvePt (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] : Type :=
  {x : X // Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
    (X ↘ Spec (.of ℂ)) x = (1 : ℕ)}

/-- The points of delta-dimension `k` of a scheme over `ℂ`. -/
private abbrev dimPts (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] (k : ℕ) : Set X :=
  {x | Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
    (X ↘ Spec (.of ℂ)) x = k}

/-- The class `∑ₓ β(x) cl_X(x) ∈ H_{2k}(X; ℚ)` of a rational combination of points. -/
private noncomputable abbrev pointsClass (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (k : ℕ) : (X →₀ ℚ) →ₗ[ℚ] RationalHomology X (2 * k) :=
  Finsupp.linearCombination ℚ (Chow.pointCycleClassOrZero ℚ k)

/-- The class of a single point of delta-dimension `k` is its cycle class. -/
private theorem pointsClass_single {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] {k : ℕ} (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = k) (a : ℚ) :
    pointsClass X k (Finsupp.single x a) = a • Chow.pointCycleClass ℚ x hx := by
  rw [Finsupp.linearCombination_single, Chow.pointCycleClassOrZero, dif_pos hx]

/-- A point of a scheme is determined by its closure. -/
private theorem eq_of_closure_eq {X : Scheme.{0}} {x y : X}
    (h : closure ({x} : Set X) = closure {y}) : x = y :=
  (inseparable_iff_closure_eq.mpr h).eq

/-- A closed immersion over `ℂ` preserves delta-dimensions. -/
private theorem relativeDimension_closedImmersion {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] (f : Y ⟶ X) [IsClosedImmersion f]
    [f.IsOver (Spec (.of ℂ))] (y : Y) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) y =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (f.base y) := by
  rw [← comp_over f (Spec (.of ℂ))]
  exact Stacks.Chow.relativeDimension_comp_closedImmersion _ f _ y

/-- **The class of points commutes with push-forward along a proper morphism which preserves
delta-dimensions and has residue degree one everywhere** (e.g. a closed immersion). -/
private theorem pushforward_pointsClass_of {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] (f : Y ⟶ X)
    [IsProper f] [f.IsOver (Spec (.of ℂ))]
    (hd : ∀ y, Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) y =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (f.base y))
    (hdeg : ∀ y, f.residueDegree y = 1) (k : ℕ) (β : Y →₀ ℚ) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map
      (K := ℂ) f)) (UnderlyingSpace.isProperMap_map (K := ℂ) f) (2 * k : ℕ)).hom
        (pointsClass Y k β) = pointsClass X k (Finsupp.mapDomain f.base β) := by
  classical
  rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun y _ ↦ ?_
  rw [map_smul, Function.comp_apply]
  congr 1
  by_cases hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) y = k
  · have h := Chow.pushforward_pointCycleClass ℚ f y hy
    simp only [hdeg, Nat.cast_one, one_smul] at h
    rw [Chow.pointCycleClassOrZero, dif_pos hy]
    exact h
  · have hx : ¬ Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (f.base y) = k := by
      rwa [← hd y]
    rw [Chow.pointCycleClassOrZero, dif_neg hy, Chow.pointCycleClassOrZero, dif_neg hx, map_zero]

/-- The class of points commutes with push-forward along a closed immersion. -/
private theorem pushforward_pointsClass {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] (f : Y ⟶ X)
    [IsClosedImmersion f] [f.IsOver (Spec (.of ℂ))] (k : ℕ) (β : Y →₀ ℚ) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (UnderlyingSpace.map
      (K := ℂ) f)) (UnderlyingSpace.isProperMap_map (K := ℂ) f) (2 * k : ℕ)).hom
        (pointsClass Y k β) = pointsClass X k (Finsupp.mapDomain f.base β) :=
  pushforward_pointsClass_of f (relativeDimension_closedImmersion f)
    (Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion f) k β

/-- Push-forward along a map preserving delta-dimensions keeps combinations of points of
delta-dimension `k` supported on such points. -/
private theorem mapDomain_mem_supported_of {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] (f : Y ⟶ X)
    (hd : ∀ y, Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) y =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) (f.base y))
    {k : ℕ} {β : Y →₀ ℚ} (hβ : β ∈ Finsupp.supported ℚ ℚ (dimPts Y k)) :
    Finsupp.mapDomain f.base β ∈ Finsupp.supported ℚ ℚ (dimPts X k) := by
  classical
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  change _ = _
  rw [← hd y]
  exact hβ hy

/-- The class in `H_2(G, ℚ)` of the curves cut on a surface `G ⊆ E` by a subset `S ⊆ Z`: the sum
of the cycle classes of the maximal irreducible subsets of `G ∩ S` which are curves, indexed by
their generic points. -/
private noncomputable def curveClassOn {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {E : MMP.Mori.PrimeDivisor Z}
    (G : {V : Subvariety E.idealSheaf.subscheme // V.HasDim 2}) (S : Set Z) :
    RationalHomology G.1.toScheme (2 * 1) :=
  ∑ᶠ (x : CurvePt G.1.toScheme)
    (_ : Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ (G.1.ι ≫ E.idealSheaf.subschemeι).base ⁻¹' S) (closure {x.1})),
    Chow.pointCycleClass ℚ x.1 x.2

/-- The class in `H_2(G, ℚ)` of the curve cut on a surface `G ⊆ E` by a `ℚ`-divisor `M` of
`E`. -/
private noncomputable def restrictionClass {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {E : MMP.Mori.PrimeDivisor Z}
    (G : {V : Subvariety E.idealSheaf.subscheme // V.HasDim 2}) (M : QDivisor E.idealSheaf.subscheme) :
    RationalHomology G.1.toScheme (2 * 1) :=
  M.sum fun P c ↦ c • ∑ᶠ (x : CurvePt G.1.toScheme)
    (_ : Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
    Chow.pointCycleClass ℚ x.1 x.2

/-- An edge index over the curve `T`: labels `I` sent onto the double surfaces dominating `T`,
with an involution `s` over `S ↦ S.swap`. -/
private structure IsEdgeIndex {Z Y : Scheme.{0}} (r : Z ⟶ Y) {F : Divisor Z}
    (T : IrreducibleCloseds Y) {I : Type} (π : I → DoubleSurface F) (s : I → I) : Prop where
  s_s : ∀ i, s (s i) = i
  π_s : ∀ i, π (s i) = (π i).swap
  image_eq : ∀ i, r.base '' (π i).carrier = (T : Set Y)
  exists_eq : ∀ σ : DoubleSurface F, r.base '' σ.carrier = (T : Set Y) → ∃ i, π i = σ

/-- An edge labelling at `y`: over each double surface `S`, the labels of `S` go bijectively to
the irreducible components of `S ∩ r⁻¹(y)`, and `i`, `s i` get the same curve. -/
private structure IsEdgeLabeling {Z Y : Scheme.{0}} (r : Z ⟶ Y) {F : Divisor Z} {I : Type}
    (π : I → DoubleSurface F) (s : I → I) (y : Y) (lab : I → Set Z) : Prop where
  lab_s : ∀ i, lab (s i) = lab i
  bijOn : ∀ σ : DoubleSurface F, Set.BijOn lab {i | π i = σ}
    {C | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) C}

open Classical in
/-- The edge equation at `y` for coefficients `b` on a labelling: on every component `G` of the
fibre of every `E` over `y`, the curve class of `L E` is `∑ b_i [λ i]`, over the labels of the
double surfaces `E ∩ E'`. -/
private def EdgeRelation {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    (r : Z ⟶ Y) {F : Divisor Z} (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    {I : Type} [Fintype I] (π : I → DoubleSurface F) (y : Y) (lab : I → Set Z) (b : I → ℚ) :
    Prop :=
  ∀ (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
    Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
    restrictionClass G (L E) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1), b i • curveClassOn G (lab i)

/-- The edge labellings at the closed points of `U ∩ T`. -/
private def edgePoints {Z Y : Scheme.{0}} (r : Z ⟶ Y) {F : Divisor Z} {I : Type}
    (π : I → DoubleSurface F) (s : I → I) (T : IrreducibleCloseds Y) (U : Y.Opens) :
    Set (Y × (I → Set Z)) :=
  {x | IsClosed {x.1} ∧ x.1 ∈ (U : Set Y) ∩ T ∧ IsEdgeLabeling r π s x.1 x.2}

/-- The covering topology on labellings: `(y, λ)` lies in the basic open of `(W₀, W)` when the
complex points of the fibre over `y` lie in `W₀` and those of each `λ i` in `W i`. -/
@[instance_reducible]
private def edgeTopology {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] (r : Z ⟶ Y) (I : Type) :
    TopologicalSpace (Y × (I → Set Z)) :=
  .generateFrom {M | ∃ (W₀ : Set (UnderlyingSpace ℂ Z)) (W : I → Set (UnderlyingSpace ℂ Z)),
    IsOpen W₀ ∧ (∀ i, IsOpen (W i)) ∧
    M = {x | UnderlyingSpace.pointsOver (K := ℂ) (r.base ⁻¹' {x.1}) ⊆ W₀ ∧
      ∀ i, UnderlyingSpace.pointsOver (K := ℂ) (x.2 i) ⊆ W i}}

/-- The connected component of a labelling `x₀` among the labellings over `U ∩ T`. -/
private def edgeComponent {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] (r : Z ⟶ Y)
    {F : Divisor Z} {I : Type} (π : I → DoubleSurface F) (s : I → I) (T : IrreducibleCloseds Y)
    (U : Y.Opens) (x₀ : Y × (I → Set Z)) : Set (Y × (I → Set Z)) :=
  @connectedComponentIn _ (edgeTopology r I) (edgePoints r π s T U) x₀

/-- The monodromy group of a set `X₀` of labellings: the permutations of the labels over the
double surfaces, commuting with `s`, under which `X₀` is stable. -/
private def edgeSubgroup {Z Y : Scheme.{0}} {F : Divisor Z} {I : Type}
    (π : I → DoubleSurface F) (s : I → I) (X₀ : Set (Y × (I → Set Z))) :
    Subgroup (Equiv.Perm I) where
  carrier := {g | (∀ i, π (g i) = π i) ∧ (∀ i, s (g i) = g (s i)) ∧
    ∀ x ∈ X₀, (x.1, x.2 ∘ g) ∈ X₀ ∧ (x.1, x.2 ∘ ⇑g⁻¹) ∈ X₀}
  one_mem' := ⟨fun _ ↦ rfl, fun _ ↦ rfl, fun x hx ↦ ⟨hx, hx⟩⟩
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂, hg₃⟩ ⟨hh₁, hh₂, hh₃⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun x hx ↦ ⟨?_, ?_⟩⟩
    · simp [Equiv.Perm.mul_apply, hg₁, hh₁]
    · simp [Equiv.Perm.mul_apply, hg₂, hh₂]
    · exact (hh₃ _ (hg₃ x hx).1).1
    · rw [mul_inv_rev, Equiv.Perm.coe_mul]
      exact (hg₃ _ (hh₃ x hx).2).2
  inv_mem' := by
    rintro g ⟨hg₁, hg₂, hg₃⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun x hx ↦ ⟨(hg₃ x hx).2, ?_⟩⟩
    · simpa using (hg₁ (g⁻¹ i)).symm
    · apply g.injective
      have := hg₂ (g⁻¹ i)
      simp only [show ∀ j, g (g⁻¹ j) = j from fun j ↦ (Equiv.eq_symm_apply g).mp rfl] at this ⊢
      exact this.symm
    · rw [inv_inv]; exact (hg₃ x hx).1

/-! ### Normalization excision for a finite union of closed subschemes -/

section Excision

open MMP.UnderlyingSpace MMP.Proof_lem_mmp_conductor_ordinary_normalization_excision
open CategoryTheory.Limits

/-- Push-forward along `f` then `g` is push-forward along `h` when `f ≫ g = h`. -/
private theorem pushforward_pushforward_of_comp_eq {X₁ X₂ X₃ : TopCat.{0}} (f : X₁ ⟶ X₂)
    (g : X₂ ⟶ X₃) (h : X₁ ⟶ X₃) (hf : IsProperMap f) (hg : IsProperMap g) (hh : IsProperMap h)
    (hfg : f ≫ g = h) (k : ℤ) (x) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) g hg k).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf k).hom x) =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) h hh k).hom x := by
  subst hfg
  rw [← ModuleCat.comp_apply, ← borelMooreHomology.pushforward_comp]

open MMP.UnderlyingSpace borelMooreHomology CategoryTheory.Limits in
/-- Classes on the summands of a finite coproduct of schemes whose push-forwards add up to `0`
vanish: restriction to the open and closed summands separates them. -/
private theorem eq_zero_of_sum_pushforward_sigmaι {J : Type} [Fintype J]
    (G : J → Scheme.{0}) [∀ j, (G j).Over (Spec (.of ℂ))] [(∐ G).Over (Spec (.of ℂ))]
    [IsComplexScheme (∐ G)] [∀ j, (Sigma.ι G j).IsOver (Spec (.of ℂ))]
    [∀ j, IsClosedImmersion (Sigma.ι G j)] (k : ℤ)
    (x : ∀ j, borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ (G j))) k)
    (h : ∑ j, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) (Sigma.ι G j)))
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (Sigma.ι G j)).isProperMap k).hom
        (x j) = 0) (j : J) : x j = 0 := by
  classical
  set M := ModuleCat.of ℚ ℚ
  set Y : TopCat := TopCat.of (UnderlyingSpace ℂ (∐ G))
  set V : J → TopologicalSpace.Opens Y := fun l ↦ opensRangeMap (Sigma.ι G l)
  have hmem : ∀ l (p : UnderlyingSpace ℂ (∐ G)),
      p ∈ V l ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∈ Set.range (Sigma.ι G l) := by
    intro l p
    change p ∈ Set.range (mapFun (K := ℂ) (Sigma.ι G l)) ↔ _
    rw [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, top_le_preimage_iff]
    rfl
  have hdisj : Pairwise (Function.onFun Disjoint fun l ↦ (V l : Set Y)) := by
    intro l m hlm
    refine Set.disjoint_left.2 fun p hl hm ↦ ?_
    rw [SetLike.mem_coe, hmem] at hl hm
    exact Set.disjoint_left.1 (Stacks.Chow.pairwise_disjoint_range_sigmaι G hlm) hl hm
  have hcover : ∀ p : Y, ∃ l, p ∈ V l := fun p ↦ by
    obtain ⟨l, hl⟩ := Stacks.Chow.exists_mem_range_sigmaι G (p.toHom (IsLocalRing.closedPoint ℂ))
    exact ⟨l, (hmem l p).2 hl⟩
  have hf := isProperMap_clopenInclusion V hdisj hcover
  let e : ∀ l, UnderlyingSpace ℂ (G l) ≃ₜ V l := fun l ↦ homeomorphOpensRangeMap (Sigma.ι G l)
  let res : ∀ l, borelMooreHomology ℚ M Y k →ₗ[ℚ]
      borelMooreHomology ℚ M (TopCat.of (UnderlyingSpace ℂ (G l))) k := fun l ↦
    (pushforward ℚ M (TopCat.ofHom ((e l).symm : C(V l, UnderlyingSpace ℂ (G l))))
      (e l).symm.isProperMap k).hom ∘ₗ (restrict ℚ M (V l) k).hom
  have hpush : ∀ l y, (pushforward ℚ M (TopCat.ofHom (map (K := ℂ) (Sigma.ι G l)))
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (Sigma.ι G l)).isProperMap k).hom y =
      (pushforward ℚ M (clopenInclusion (V l)) (hf l) k).hom
        ((pushforward ℚ M (TopCat.ofHom (e l : C(UnderlyingSpace ℂ (G l), V l)))
          (e l).isProperMap k).hom y) := by
    intro l y
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    rfl
  have hself : ∀ y, res j ((pushforward ℚ M (TopCat.ofHom (map (K := ℂ) (Sigma.ι G j)))
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (Sigma.ι G j)).isProperMap k).hom y)
      = y := by
    intro y
    change (pushforward ℚ M _ _ k).hom ((restrict ℚ M (V j) k).hom _) = y
    rw [hpush, ← ModuleCat.comp_apply (pushforward ℚ M (clopenInclusion (V j)) (hf j) k),
      pushforward_restrict_self ℚ M (V j) (isClopen_of_disjoint_cover V hdisj hcover j),
      ModuleCat.id_apply]
    exact borelMooreHomology.pushforward_symm_pushforward_homeomorph ℚ M (e j) k y
  have hne : ∀ l, l ≠ j → ∀ y, res j ((pushforward ℚ M
      (TopCat.ofHom (map (K := ℂ) (Sigma.ι G l)))
      (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (Sigma.ι G l)).isProperMap k).hom y)
      = 0 := by
    intro l hlj y
    change (pushforward ℚ M _ _ k).hom ((restrict ℚ M (V j) k).hom _) = 0
    rw [hpush, ← ModuleCat.comp_apply (pushforward ℚ M (clopenInclusion (V l)) (hf l) k),
      pushforward_restrict_of_disjoint ℚ M (V l) (V j)
        (isClopen_of_disjoint_cover V hdisj hcover j) (hdisj hlj)]
    simp
  have := congrArg (res j) h
  rw [map_sum, Finset.sum_eq_single j (fun l _ hl ↦ hne l hl _) (by simp), hself,
    map_zero] at this
  exact this

/-- **The excision sequence of a finite union of closed subschemes, in degree two.** Let a complex
scheme `R` be covered by closed subschemes `m j : G j ⟶ R`, let `A` be the set of points lying on
two of them, and suppose `A` and its traces on the `G j` have dimension at most one. If classes
`ρ j ∈ H_2(G j)` push forward to `0` in `H_2(R)`, then `ρ j = -[γ j]` for rational combinations
`γ j` of points of delta-dimension one (`1`-cycles), whose push-forwards to `R` cancel. -/
private theorem exists_cycles_of_sum_pushforward_eq_zero
    {R : Scheme.{0}} [R.Over (Spec (.of ℂ))] [IsComplexScheme R]
    {J : Type} [Fintype J] (G : J → Scheme.{0}) [∀ j, (G j).Over (Spec (.of ℂ))]
    [∀ j, IsComplexScheme (G j)]
    (m : ∀ j, G j ⟶ R) [∀ j, IsClosedImmersion (m j)] [∀ j, (m j).IsOver (Spec (.of ℂ))]
    (hcov : ∀ x : R, ∃ j, x ∈ Set.range (m j)) (A : Set R)
    (hA : A = ⋃ j, ⋃ k, ⋃ (_ : j ≠ k), Set.range (m j) ∩ Set.range (m k))
    (hAdim : topologicalKrullDim A ≤ 1)
    (hGdim : ∀ j, topologicalKrullDim ((m j).base ⁻¹' A) ≤ 1)
    (ρ : ∀ j, RationalHomology (G j) (2 * 1))
    (hρ : ∑ j, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) (m j))) (IsComplexScheme.isProperMap_map (m j))
      (2 * 1 : ℕ)).hom (ρ j) = 0) :
    ∃ γ : ∀ j, G j →₀ ℚ,
      (∀ j, γ j ∈ Finsupp.supported ℚ ℚ (dimPts (G j) 1)) ∧
      (∀ j, ρ j + pointsClass (G j) 1 (γ j) = 0) ∧
      ∑ j, Finsupp.mapDomain (m j).base (γ j) = 0 := by
  classical
  -- the disjoint union `N = ∐ G j` and `ν : N ⟶ R`
  let N : Scheme.{0} := ∐ G
  let ν : N ⟶ R := Sigma.desc m
  letI : N.Over (Spec (.of ℂ)) := ⟨ν ≫ R ↘ Spec (.of ℂ)⟩
  haveI : ν.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hιν : ∀ j, Sigma.ι G j ≫ ν = m j := fun j ↦ Sigma.ι_desc _ _
  haveI hιover : ∀ j, (Sigma.ι G j).IsOver (Spec (.of ℂ)) := fun j ↦ ⟨by
    change Sigma.ι G j ≫ ν ≫ R ↘ Spec (.of ℂ) = _
    rw [← Category.assoc, hιν, comp_over]⟩
  haveI : ∀ j, IsClosedImmersion (Sigma.ι G j) := Stacks.Chow.isClosedImmersion_sigmaι G
  haveI : IsProper ν := Stacks.Chow.isProper_sigmaDesc_of_locallyFinite G m
    (locallyFinite_of_finite _)
  haveI : IsZariskiLocalAtSource @LocallyQuasiFinite :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyQuasiFinite)
      (Q := RingHom.QuasiFinite)
  haveI : LocallyQuasiFinite ν :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite) fun _ ↦ inferInstance
  haveI : IsFinite ν := IsFinite.of_isProper_of_locallyQuasiFinite ν
  haveI : IsComplexScheme N := IsComplexScheme.of_isFinite ν
  -- the spaces
  have hAcl : IsClosed A := by
    rw [hA]
    exact isClosed_iUnion_of_finite fun j ↦ isClosed_iUnion_of_finite fun k ↦
      isClosed_iUnion_of_finite fun _ ↦
        (m j).isClosedEmbedding.isClosed_range.inter (m k).isClosedEmbedding.isClosed_range
  let Rt := TopCat.of (UnderlyingSpace ℂ R)
  let Nt := TopCat.of (UnderlyingSpace ℂ N)
  let νt : Nt ⟶ Rt := TopCat.ofHom (map (K := ℂ) ν)
  let Aan : Set Rt := pointsOver (K := ℂ) A
  have hAc : IsClosed Aan := isClosed_pointsOver hAcl
  have hFc : IsClosed (νt ⁻¹' Aan) := hAc.preimage νt.hom.continuous
  have hνp : IsProperMap νt := IsComplexScheme.isProperMap_map ν
  have hmapι : ∀ j q, map (K := ℂ) ν (map (K := ℂ) (Sigma.ι G j) q) = map (K := ℂ) (m j) q :=
    fun j q ↦ UnderlyingSpace.ext (by
      rw [toHom_map, toHom_map, toHom_map, Category.assoc, hιν])
  have hpiece : ∀ p : UnderlyingSpace ℂ N, ∃ j q, map (K := ℂ) (Sigma.ι G j) q = p := by
    intro p
    obtain ⟨j, hj⟩ := Stacks.Chow.exists_mem_range_sigmaι G (p.toHom (IsLocalRing.closedPoint ℂ))
    have hp : p ∈ Set.range (mapFun (K := ℂ) (Sigma.ι G j)) := by
      rw [range_mapFun_of_isOpenImmersion, Set.mem_setOf_eq, top_le_preimage_iff]
      exact hj
    obtain ⟨q, hq⟩ := hp
    exact ⟨j, q, hq⟩
  have hhom : IsHomeomorph (Aanᶜ.restrictPreimage (map (K := ℂ) ν)) := by
    rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
    refine ⟨(map (K := ℂ) ν).continuous.restrictPreimage, (hνp.restrictPreimage _).isClosedMap,
      ⟨fun p₁ p₂ h ↦ ?_, fun P ↦ ?_⟩⟩
    · obtain ⟨j₁, q₁, hq₁⟩ := hpiece p₁.1
      obtain ⟨j₂, q₂, hq₂⟩ := hpiece p₂.1
      have h' : map (K := ℂ) (m j₁) q₁ = map (K := ℂ) (m j₂) q₂ := by
        rw [← hmapι, ← hmapι, hq₁, hq₂]
        exact congrArg Subtype.val h
      by_cases hj : j₁ = j₂
      · subst hj
        refine Subtype.ext ?_
        rw [← hq₁, ← hq₂, mapFun_injective_of_mono (m j₁) h']
      · exfalso
        apply p₁.2
        change (map (K := ℂ) ν p₁.1).toHom (IsLocalRing.closedPoint ℂ) ∈ A
        rw [← hq₁, hmapι, hA]
        refine Set.mem_iUnion.2 ⟨j₁, Set.mem_iUnion.2 ⟨j₂, Set.mem_iUnion.2 ⟨hj, ?_, ?_⟩⟩⟩
        · exact ⟨_, rfl⟩
        · rw [h']
          exact ⟨_, rfl⟩
    · obtain ⟨j, hj⟩ := hcov (P.1.toHom (IsLocalRing.closedPoint ℂ))
      have hP : P.1 ∈ Set.range (map (K := ℂ) (m j)) := by
        rw [range_map_of_isClosedImmersion]
        exact hj
      obtain ⟨q, hq⟩ := hP
      refine ⟨⟨map (K := ℂ) (Sigma.ι G j) q, ?_⟩, Subtype.ext ?_⟩
      · change map (K := ℂ) ν _ ∈ Aanᶜ
        rw [hmapι, hq]
        exact P.2
      · change map (K := ℂ) ν _ = P.1
        rw [hmapι, hq]
  let gX : TopCat.of (νt ⁻¹' Aan) ⟶ TopCat.of Aan :=
    TopCat.ofHom ((map (K := ℂ) ν).restrictPreimage Aan)
  let gU : TopCat.of (borelMooreHomology.complOpens hFc) ⟶
      TopCat.of (borelMooreHomology.complOpens hAc) :=
    TopCat.ofHom ((map (K := ℂ) ν).restrictPreimage Aanᶜ)
  have hbijC : ∀ k : ℤ, Function.Bijective
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gU (hνp.restrictPreimage Aanᶜ) k).hom :=
    fun k ↦ bijective_pushforward_of_homeomorph gU (hνp.restrictPreimage Aanᶜ) hhom.homeomorph
      (fun _ ↦ rfl) k
  have hrelA := isRelativeQuasiIso_pointsOver R ⟨A, hAcl⟩ hAc
  have hrelF := isRelativeQuasiIso_pointsOver N ⟨ν.base ⁻¹' A, hAcl.preimage ν.continuous⟩ hFc
  obtain ⟨hex, -⟩ := homology_sequence νt hνp hAc hFc (Opens.ext rfl) gX
    (hνp.restrictPreimage Aan) (TopCat.ext fun _ ↦ rfl) gU (hνp.restrictPreimage Aanᶜ)
    (fun _ ↦ rfl) hrelA hrelF hbijC
  -- the class `n = ∑ ι_{j*} ρ j` on `N`
  let pι : ∀ j, RationalHomology (G j) (2 * 1) →ₗ[ℚ] RationalHomology N (2 * 1) := fun j ↦
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) (Sigma.ι G j))) (IsComplexScheme.isProperMap_map _)
      (2 * 1 : ℕ)).hom
  let n : RationalHomology N (2 * 1) := ∑ j, pι j (ρ j)
  have hn : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) νt hνp (2 * 1 : ℕ)).hom n = 0 := by
    rw [← hρ, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact pushforward_pushforward_of_comp_eq _ _ _ _ _ _
      (TopCat.ext fun q ↦ hmapι j q) _ _
  obtain ⟨c, hc⟩ := ((hex ((2 * 1 : ℕ) : ℤ)) (0, n)).1 (by
    simp only [LinearMap.coprod_apply, map_zero, zero_add]
    exact hn)
  have hc₁ : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) gX (hνp.restrictPreimage Aan)
      (2 * 1 : ℕ)).hom c = 0 := congrArg Prod.fst hc
  have hc₂ : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (subspaceInclusion Nt (νt ⁻¹' Aan)) (borelMooreHomology.isProperMap_subspaceInclusion hFc)
      (2 * 1 : ℕ)).hom c = -n := by
    have h : -(borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (subspaceInclusion Nt (νt ⁻¹' Aan)) (borelMooreHomology.isProperMap_subspaceInclusion hFc)
        (2 * 1 : ℕ)).hom c = n := congrArg Prod.snd hc
    rw [← h, neg_neg]
  -- the reduced schemes on `A` and on `ν⁻¹ A`
  let IA := Scheme.IdealSheafData.vanishingIdeal (⟨A, hAcl⟩ : Closeds R)
  let IF := Scheme.IdealSheafData.vanishingIdeal
    (⟨ν.base ⁻¹' A, hAcl.preimage ν.continuous⟩ : Closeds N)
  haveI : IsComplexScheme IA.subscheme := IsComplexScheme.of_isClosedImmersion IA.subschemeι
  haveI : IsComplexScheme IF.subscheme := IsComplexScheme.of_isClosedImmersion IF.subschemeι
  haveI : IsReduced IF.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hrA : Set.range (map (K := ℂ) IA.subschemeι) = Aan := by
    rw [range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrF : Set.range (map (K := ℂ) IF.subschemeι) = νt ⁻¹' Aan := by
    rw [range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let eA : UnderlyingSpace ℂ IA.subscheme ≃ₜ Aan :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
      IA.subschemeι).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrA)
  let eF : UnderlyingSpace ℂ IF.subscheme ≃ₜ (νt ⁻¹' Aan : Set Nt) :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
      IF.subschemeι).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrF)
  have hdimA : MMP.Intersection.Scheme.dimension IA.subscheme ≤ (1 : ℕ) := by
    refine le_trans ((IA.subschemeι.isClosedEmbedding.isInducing.codRestrict
      (s := A) fun z ↦ ?_).topologicalKrullDim_le) hAdim
    have : IA.subschemeι z ∈ Set.range IA.subschemeι := ⟨z, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  have hdimF : MMP.Intersection.Scheme.dimension IF.subscheme ≤ (1 : ℕ) := by
    have hcl : ∀ j, IsClosed ((Sigma.ι G j).base '' ((m j).base ⁻¹' A)) := fun j ↦
      (Sigma.ι G j).isClosedEmbedding.isClosedMap _ (hAcl.preimage (m j).continuous)
    have hdj : ∀ j ∈ (Finset.univ : Finset J),
        topologicalKrullDim ((Sigma.ι G j).base '' ((m j).base ⁻¹' A)) ≤ (1 : ℕ) := by
      intro j _
      refine le_of_eq_of_le ?_ (hGdim j)
      have hemb : Topology.IsEmbedding (fun s : ((m j).base ⁻¹' A : Set (G j)) ↦
          (Sigma.ι G j).base s.1) :=
        (Sigma.ι G j).isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
      have hrange : Set.range (fun s : ((m j).base ⁻¹' A : Set (G j)) ↦ (Sigma.ι G j).base s.1) =
          (Sigma.ι G j).base '' ((m j).base ⁻¹' A) := by
        rw [Set.range_comp' (Sigma.ι G j).base Subtype.val, Subtype.range_coe]
      exact ((hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph
        |>.topologicalKrullDim_eq).symm
    have hle := topologicalKrullDim_biUnion_le (Finset.univ : Finset J) hcl hdj
    have hsub : ν.base ⁻¹' A ⊆ ⋃ j ∈ (Finset.univ : Finset J),
        (Sigma.ι G j).base '' ((m j).base ⁻¹' A) := by
      intro x hx
      obtain ⟨j, z, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι G x
      refine Set.mem_biUnion (Finset.mem_univ j) ⟨z, ?_, rfl⟩
      change (Sigma.ι G j ≫ ν).base z ∈ A at hx
      rwa [hιν] at hx
    refine le_trans ((IF.subschemeι.isClosedEmbedding.isInducing.codRestrict
      (s := ν.base ⁻¹' A) fun z ↦ ?_).topologicalKrullDim_le)
      (le_trans (topologicalKrullDim_le_of_subset hsub) hle)
    have : IF.subschemeι z ∈ Set.range IF.subschemeι := ⟨z, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  -- the restriction `ψ : ν⁻¹ A ⟶ A` of `ν`
  have hkerψ : IA.subschemeι.ker ≤ (IF.subschemeι ≫ ν).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.2 ?_)
    rintro _ ⟨z, rfl⟩
    have : IF.subschemeι z ∈ Set.range IF.subschemeι := ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    exact this
  let ψ := IsClosedImmersion.lift IA.subschemeι (IF.subschemeι ≫ ν) hkerψ
  have hψ : ψ ≫ IA.subschemeι = IF.subschemeι ≫ ν := IsClosedImmersion.lift_fac _ _ _
  haveI : ψ.IsOver (Spec (.of ℂ)) := ⟨by
    change ψ ≫ IA.subschemeι ≫ R ↘ Spec (.of ℂ) = IF.subschemeι ≫ ν ≫ R ↘ Spec (.of ℂ)
    rw [← Category.assoc, hψ, Category.assoc]⟩
  haveI : IsProper (ψ ≫ IA.subschemeι) := by rw [hψ]; infer_instance
  haveI : IsProper ψ := IsProper.of_comp ψ IA.subschemeι
  -- delta-dimensions and residue degrees along `ν` and `ψ`
  have hdN : ∀ n : N,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (N ↘ Spec (.of ℂ)) n =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (R ↘ Spec (.of ℂ)) (ν.base n) := by
    intro n
    obtain ⟨j, g, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι G n
    rw [← relativeDimension_closedImmersion (Sigma.ι G j) g,
      relativeDimension_closedImmersion (m j) g]
    change _ = Stacks.Chow.relativeDimension _ _ ((Sigma.ι G j ≫ ν).base g)
    rw [hιν]
  have hdegN : ∀ n : N, ν.residueDegree n = 1 := by
    intro n
    obtain ⟨j, g, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι G n
    have h := AlgebraicGeometry.residueDegree_comp (Sigma.ι G j) ν g
    rw [hιν, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (m j),
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (Sigma.ι G j)] at h
    simpa using h.symm
  have hψb : ∀ x, IA.subschemeι.base (ψ.base x) = ν.base (IF.subschemeι.base x) := fun x ↦ by
    change (ψ ≫ IA.subschemeι).base x = (IF.subschemeι ≫ ν).base x
    rw [hψ]
  have hdψ : ∀ x : IF.subscheme,
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (IF.subscheme ↘ Spec (.of ℂ)) x =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (IA.subscheme ↘ Spec (.of ℂ)) (ψ.base x) := by
    intro x
    rw [relativeDimension_closedImmersion IF.subschemeι x, hdN,
      relativeDimension_closedImmersion IA.subschemeι (ψ.base x), hψb]
  have hdegψ : ∀ x : IF.subscheme, ψ.residueDegree x = 1 := by
    intro x
    have h := AlgebraicGeometry.residueDegree_comp ψ IA.subschemeι x
    rw [hψ, AlgebraicGeometry.residueDegree_comp, hdegN,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion IF.subschemeι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion IA.subschemeι] at h
    simpa using h.symm
  -- `c` is the class of a `1`-cycle `γ` on `ν⁻¹ A`
  let M := ModuleCat.of ℚ ℚ
  let c' := (borelMooreHomology.pushforward ℚ M
    (TopCat.ofHom (eF.symm : C(↥(νt ⁻¹' Aan), UnderlyingSpace ℂ IF.subscheme)))
    eF.symm.isProperMap (2 * 1 : ℕ)).hom c
  have hcc' : (borelMooreHomology.pushforward ℚ M
      (TopCat.ofHom (eF : C(UnderlyingSpace ℂ IF.subscheme, ↥(νt ⁻¹' Aan))))
      eF.isProperMap (2 * 1 : ℕ)).hom c' = c :=
    borelMooreHomology.pushforward_symm_pushforward_homeomorph ℚ M eF.symm _ c
  obtain ⟨γ, hγsupp, hγ⟩ := Chow.exists_mem_supported_linearCombination_eq (R := ℚ) hdimF c'
  have hγ' : pointsClass IF.subscheme 1 γ = c' := hγ
  set δ := Finsupp.mapDomain IF.subschemeι.base γ with hδ
  have hδsupp : δ ∈ Finsupp.supported ℚ ℚ (dimPts N 1) :=
    mapDomain_mem_supported_of IF.subschemeι (relativeDimension_closedImmersion IF.subschemeι)
      hγsupp
  have hpF : (borelMooreHomology.pushforward ℚ M (subspaceInclusion Nt (νt ⁻¹' Aan))
      (borelMooreHomology.isProperMap_subspaceInclusion hFc) (2 * 1 : ℕ)).hom c =
      pointsClass N 1 δ := by
    rw [← hcc', pushforward_pushforward_of_comp_eq _ _ (TopCat.ofHom (map (K := ℂ) IF.subschemeι))
      _ _ (IsComplexScheme.isProperMap_map _) (TopCat.ext fun _ ↦ rfl), ← hγ']
    exact pushforward_pointsClass IF.subschemeι 1 γ
  have hcomp : TopCat.ofHom (map (K := ℂ) ψ) ≫
      TopCat.ofHom (eA : C(UnderlyingSpace ℂ IA.subscheme, ↥Aan)) =
      TopCat.ofHom (eF : C(UnderlyingSpace ℂ IF.subscheme, ↥(νt ⁻¹' Aan))) ≫ gX :=
      TopCat.ext fun p ↦ Subtype.ext (by
    change map (K := ℂ) IA.subschemeι (map (K := ℂ) ψ p) =
      map (K := ℂ) ν (map (K := ℂ) IF.subschemeι p)
    refine UnderlyingSpace.ext ?_
    rw [toHom_map, toHom_map, toHom_map, toHom_map, Category.assoc, hψ, Category.assoc])
  have hψγ : Finsupp.mapDomain ψ.base γ = 0 := by
    refine Chow.eq_zero_of_linearCombination_pointCycleClassOrZero_eq_zero (R := ℚ) hdimA
      (mapDomain_mem_supported_of ψ hdψ hγsupp) ?_
    change pointsClass IA.subscheme 1 (Finsupp.mapDomain ψ.base γ) = 0
    have h1 : (borelMooreHomology.pushforward ℚ M
        (TopCat.ofHom (eA : C(UnderlyingSpace ℂ IA.subscheme, ↥Aan))) eA.isProperMap
        (2 * 1 : ℕ)).hom (pointsClass IA.subscheme 1 (Finsupp.mapDomain ψ.base γ)) = 0 := by
      rw [← pushforward_pointsClass_of ψ hdψ hdegψ 1 γ, hγ',
        pushforward_pushforward_of_comp_eq _ _ _ _ _ ((hνp.restrictPreimage Aan).comp
          eF.isProperMap) hcomp,
        ← pushforward_pushforward_of_comp_eq
          (TopCat.ofHom (eF : C(UnderlyingSpace ℂ IF.subscheme, ↥(νt ⁻¹' Aan)))) gX _
          eF.isProperMap (hνp.restrictPreimage Aan)
          ((hνp.restrictPreimage Aan).comp eF.isProperMap) rfl, hcc', hc₁]
    have h2 := congrArg (borelMooreHomology.pushforward ℚ M
      (TopCat.ofHom (eA.symm : C(↥Aan, UnderlyingSpace ℂ IA.subscheme))) eA.symm.isProperMap
      (2 * 1 : ℕ)).hom h1
    rwa [borelMooreHomology.pushforward_symm_pushforward_homeomorph, map_zero] at h2
  -- `ν_* δ = 0`
  have hδν : Finsupp.mapDomain ν.base δ = 0 := by
    rw [hδ, ← Finsupp.mapDomain_comp,
      show ⇑ν.base ∘ ⇑IF.subschemeι.base = ⇑IA.subschemeι.base ∘ ⇑ψ.base from
        funext fun x ↦ (hψb x).symm,
      Finsupp.mapDomain_comp, hψγ, Finsupp.mapDomain_zero]
  -- the summands of `δ`
  have hιinj : ∀ j, Function.Injective (Sigma.ι G j).base := fun j ↦
    (Sigma.ι G j).isClosedEmbedding.injective
  have hmν : ∀ j, ⇑(m j).base = ⇑ν.base ∘ ⇑(Sigma.ι G j).base := fun j ↦ funext fun g ↦ by
    change _ = (Sigma.ι G j ≫ ν).base g
    rw [hιν]
  let γj : ∀ j, G j →₀ ℚ := fun j ↦
    Finsupp.comapDomain (Sigma.ι G j).base δ (hιinj j).injOn
  have hδdec : δ = ∑ j, Finsupp.mapDomain (Sigma.ι G j).base (γj j) := by
    ext n
    rw [Finsupp.finset_sum_apply]
    obtain ⟨j, g, rfl⟩ := Stacks.Chow.exists_mem_range_sigmaι G n
    rw [Finset.sum_eq_single j]
    · rw [Finsupp.mapDomain_apply_of_injective (hιinj j)]
      rfl
    · intro k _ hk
      refine Finsupp.mapDomain_of_notMem_range _ _ fun hV ↦ ?_
      exact Set.disjoint_left.1 (Stacks.Chow.pairwise_disjoint_range_sigmaι G hk) hV ⟨g, rfl⟩
    · simp
  refine ⟨γj, fun j x hx ↦ ?_, fun j ↦ ?_, ?_⟩
  · have hx' : (Sigma.ι G j).base x ∈ δ.support := by
      simpa [γj] using hx
    have h := hδsupp hx'
    change _ = _ at h ⊢
    rwa [relativeDimension_closedImmersion (Sigma.ι G j) x]
  · have hsum : ∑ j, pι j (ρ j + pointsClass (G j) 1 (γj j)) = 0 := by
      simp only [map_add, Finset.sum_add_distrib]
      have : ∑ j, pι j (pointsClass (G j) 1 (γj j)) = pointsClass N 1 δ := by
        conv_rhs => rw [hδdec]
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ ↦ pushforward_pointsClass (Sigma.ι G j) 1 (γj j)
      rw [this, ← hpF, hc₂]
      exact add_neg_cancel n
    exact eq_zero_of_sum_pushforward_sigmaι G _ (fun j ↦ ρ j + pointsClass (G j) 1 (γj j))
      hsum j
  · calc ∑ j, Finsupp.mapDomain (m j).base (γj j)
        = ∑ j, Finsupp.mapDomain ν.base (Finsupp.mapDomain (Sigma.ι G j).base (γj j)) :=
          Finset.sum_congr rfl fun j _ ↦ by rw [← Finsupp.mapDomain_comp, hmν]
      _ = Finsupp.mapDomain ν.base δ := by rw [hδdec, Finsupp.mapDomain_finset_sum]
      _ = 0 := hδν

end Excision

/-- The preimage of an irreducible set lying in the image of an embedding is irreducible. -/
private theorem isIrreducible_preimage_of_isEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {φ : A → B} (hφ : Topology.IsEmbedding φ) {C : Set B}
    (hC : IsIrreducible C) (hCr : C ⊆ Set.range φ) : IsIrreducible (φ ⁻¹' C) := by
  refine ⟨?_, fun u v hu hv ⟨a, has, hau⟩ ⟨b, hbs, hbv⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hC.nonempty
    obtain ⟨a, rfl⟩ := hCr hc
    exact ⟨a, hc⟩
  · obtain ⟨u', hu', rfl⟩ := hφ.isInducing.isOpen_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := hφ.isInducing.isOpen_iff.1 hv
    obtain ⟨c, hcC, hcu, hcv⟩ := hC.2 u' v' hu' hv' ⟨φ a, has, hau⟩ ⟨φ b, hbs, hbv⟩
    obtain ⟨d, rfl⟩ := hCr hcC
    exact ⟨d, hcC, hcu, hcv⟩

/-- The maximal irreducible subsets of the preimage of `S` under an embedding are the preimages
of the maximal irreducible subsets of `S` lying in the image, when each of these lies in the
image or misses it. -/
private theorem maximal_preimage_iff {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {φ : A → B} (hφ : Topology.IsEmbedding φ) {S : Set B}
    (hsep : ∀ C, Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ S) C →
      C ⊆ Set.range φ ∨ Disjoint C (Set.range φ)) (A' : Set A) :
    Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ φ ⁻¹' S) A' ↔
      ∃ C, Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ S) C ∧ C ⊆ Set.range φ ∧ A' = φ ⁻¹' C := by
  constructor
  · rintro ⟨⟨hA, hAS⟩, hmax⟩
    obtain ⟨C, hAC, hC⟩ := exists_subset_maximal_of_isIrreducible
      (hA.image φ hφ.continuous.continuousOn) (Set.image_subset_iff.2 hAS)
    have hCr : C ⊆ Set.range φ := by
      refine (hsep C hC).resolve_right fun hd ↦ ?_
      obtain ⟨a, ha⟩ := hA.nonempty
      exact Set.disjoint_left.1 hd (hAC ⟨a, ha, rfl⟩) ⟨a, rfl⟩
    refine ⟨C, hC, hCr, le_antisymm (fun a ha ↦ hAC ⟨a, ha, rfl⟩) ?_⟩
    exact hmax ⟨isIrreducible_preimage_of_isEmbedding hφ hC.1.1 hCr,
      Set.preimage_mono hC.1.2⟩ fun a ha ↦ hAC ⟨a, ha, rfl⟩
  · rintro ⟨C, hC, hCr, rfl⟩
    refine ⟨⟨isIrreducible_preimage_of_isEmbedding hφ hC.1.1 hCr, Set.preimage_mono hC.1.2⟩, ?_⟩
    rintro X ⟨hX, hXS⟩ hCX
    have hle : C ⊆ φ '' X := by
      rw [← Set.image_preimage_eq_of_subset hCr]
      exact Set.image_mono hCX
    have := hC.2 ⟨hX.image φ hφ.continuous.continuousOn, Set.image_subset_iff.2 hXS⟩ hle
    exact fun a ha ↦ this ⟨a, ha, rfl⟩

/-- The maximal irreducible subsets of an irreducible set are the set itself. -/
private theorem maximal_subset_iff_of_isIrreducible {B : Type*} [TopologicalSpace B]
    {S C : Set B} (hS : IsIrreducible S) :
    Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ S) C ↔ C = S := by
  constructor
  · intro hC
    exact le_antisymm hC.1.2 (hC.2 ⟨hS, le_rfl⟩ hC.1.2)
  · rintro rfl
    exact ⟨⟨hS, le_rfl⟩, fun _ hX _ ↦ hX.2⟩

open MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity Classical in
/-- At a closed point `y` whose fibre components in `E` are disjoint, a system `a` on double
surfaces dominating `T` cuts on each component `G` the curve class `∑ a_S [C]` over the
labelled double curves `C ⊆ G`. -/
private theorem restrictionClass_surfaceCoefficientDivisor_eq_of_disjoint
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {sZ : Z ⟶ Spec (.of ℂ)} [IsProper sZ] {r : Z ⟶ Y} {F : Divisor Z} (hB : F.IsSNC sZ)
    (y : Y) {T : IrreducibleCloseds Y} {I : Type} [Fintype I] {π : I → DoubleSurface F}
    {s : I → I} (hI : IsEdgeIndex r T π s) {lab : I → Set Z} (hlab : IsEdgeLabeling r π s y lab)
    (a : DoubleSurface F → ℚ) (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2})
    (hG : Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _))
    (hdisj : ∀ A, Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A → A ≠ G.1.support →
        Disjoint A G.1.support) :
    restrictionClass G (surfaceCoefficientDivisor a E.1) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1), a (π i) • curveClassOn G (lab i) := by
  classical
  have := noetherianSpace_of_isComplexScheme (X := Z)
  have := finite_doubleSurface F
  letI : Fintype (DoubleSurface F) := Fintype.ofFinite _
  set ι := E.1.idealSheaf.subschemeι with hι
  set φ := (G.1.ι ≫ ι).base with hφdef
  have hφ : Topology.IsEmbedding φ := (G.1.ι ≫ ι).isClosedEmbedding.isEmbedding
  have hιemb : Topology.IsEmbedding ι.base := ι.isClosedEmbedding.isEmbedding
  have hrangeι : Set.range ι.base = (E.1.idealSheaf.support : Set Z) :=
    E.1.idealSheaf.range_subschemeι
  have hrange : Set.range φ = ι.base '' (G.1.support : Set _) := by
    rw [hφdef, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    congr 1
    exact G.1.ideal.range_subschemeι
  have hfib : ∀ x, r.base (φ x) = y := by
    intro x
    have hx : G.1.ι.base x ∈ (G.1.support : Set _) := by
      rw [Subvariety.support_eq, ← G.1.ideal.range_subschemeι]; exact ⟨x, rfl⟩
    exact hG.1.2 hx
  -- a curve of the fibre of `E` lies in `G` or misses it
  have hsep : ∀ C : Set Z, IsIrreducible C → C ⊆ (E.1.idealSheaf.support : Set Z) →
      C ⊆ r.base ⁻¹' {y} → C ⊆ Set.range φ ∨ Disjoint C (Set.range φ) := by
    intro C hC hCE hCy
    have hCr : C ⊆ Set.range ι.base := hrangeι ▸ hCE
    have hC' := isIrreducible_preimage_of_isEmbedding hιemb hC hCr
    have hC'y : ι.base ⁻¹' C ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y} := by
      intro x hx
      change r.base (ι.base x) ∈ ({y} : Set Y)
      exact hCy hx
    obtain ⟨G', hCG', hG'⟩ := exists_subset_maximal_of_isIrreducible hC' hC'y
    rw [hrange]
    by_cases hGG : G' = G.1.support
    · left
      intro c hc
      obtain ⟨x, rfl⟩ := hCr hc
      exact ⟨x, hGG ▸ hCG' hc, rfl⟩
    · right
      rw [Set.disjoint_left]
      rintro c hc ⟨g, hg, rfl⟩
      exact Set.disjoint_left.1 (hdisj G' hG' hGG) (hCG' hc) hg
  -- the labelled double curves of `σ` lie in `E` and over `y`
  have hlabE : ∀ σ : DoubleSurface F, σ.fst = E.1 → ∀ C,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) C →
      C ⊆ Set.range φ ∨ Disjoint C (Set.range φ) := by
    intro σ hσ C hC
    refine hsep C hC.1.1 (fun c hc ↦ ?_) fun c hc ↦ (hC.1.2 hc).2
    have := (σ.carrier_subset (hC.1.2 hc).1).1
    rw [hσ] at this
    exact this
  -- the curve class of a double surface is the sum over its labels
  have hσ : ∀ σ : DoubleSurface F, σ.fst = E.1 →
      ∑ᶠ (x : CurvePt G.1.toScheme)
        (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ φ ⁻¹' σ.carrier) (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2 =
      ∑ i ∈ Finset.univ.filter (fun i ↦ π i = σ), curveClassOn G (lab i) := by
    intro σ hσE
    let t : I → Set (CurvePt G.1.toScheme) := fun i ↦
      {x | lab i ⊆ Set.range φ ∧ closure {x.1} = φ ⁻¹' lab i}
    have hS : φ ⁻¹' σ.carrier = φ ⁻¹' (σ.carrier ∩ r.base ⁻¹' {y}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, hfib x, and_true]
    have hmem : ∀ C : CurvePt G.1.toScheme,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ φ ⁻¹' σ.carrier) (closure {C.1}) ↔
          C ∈ ⋃ i ∈ ((Finset.univ.filter (fun i ↦ π i = σ) : Finset I) : Set I), t i := by
      intro C
      rw [hS, maximal_preimage_iff hφ (hlabE σ hσE)]
      simp only [Set.mem_iUnion, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq, exists_prop, t]
      constructor
      · rintro ⟨C', hC', hC'r, hCC'⟩
        obtain ⟨i, hi, rfl⟩ := (hlab.bijOn σ).surjOn hC'
        exact ⟨i, hi, hC'r, hCC'⟩
      · rintro ⟨i, hi, hir, hCi⟩
        exact ⟨lab i, (hlab.bijOn σ).mapsTo hi, hir, hCi⟩
    have hcc : ∀ i, π i = σ → curveClassOn G (lab i) =
        ∑ᶠ (C : CurvePt G.1.toScheme) (_ : C ∈ t i),
          Chow.pointCycleClass ℚ C.1 C.2 := by
      intro i hi
      have hli := (hlab.bijOn σ).mapsTo hi
      have hirr : IsIrreducible (lab i) := hli.1.1
      unfold curveClassOn
      refine finsum_congr fun C ↦ ?_
      have hiff : Maximal (fun A ↦ IsIrreducible A ∧
          A ⊆ (G.1.ι ≫ E.1.idealSheaf.subschemeι).base ⁻¹' lab i) (closure {C.1}) ↔
          C ∈ t i := by
        change Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ φ ⁻¹' lab i) _ ↔ _
        rw [maximal_preimage_iff hφ fun C' hC' ↦ ?_]
        · simp only [maximal_subset_iff_of_isIrreducible hirr, t, Set.mem_setOf_eq]
          constructor
          · rintro ⟨C', rfl, h1, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨_, rfl, h1, h2⟩
        · rw [maximal_subset_iff_of_isIrreducible hirr] at hC'
          subst hC'
          exact hlabE σ hσE _ hli
      exact finsum_congr_Prop (propext hiff) fun _ ↦ rfl
    rw [show (∑ᶠ (C : CurvePt G.1.toScheme)
        (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ φ ⁻¹' σ.carrier) (closure {C.1})),
        Chow.pointCycleClass ℚ C.1 C.2) =
        ∑ᶠ (C : CurvePt G.1.toScheme)
          (_ : C ∈ ⋃ i ∈ ((Finset.univ.filter (fun i ↦ π i = σ) : Finset I) : Set I), t i),
          Chow.pointCycleClass ℚ C.1 C.2 from
        finsum_congr fun C ↦ finsum_congr_Prop (propext (hmem C)) fun _ ↦ rfl]
    rw [finsum_mem_biUnion, finsum_mem_coe_finset]
    · exact Finset.sum_congr rfl fun i hi ↦ (hcc i (Finset.mem_filter.1 hi).2).symm
    · intro i hi j hj hij
      refine Set.disjoint_left.2 fun C hCi hCj ↦ hij ?_
      have hi' : π i = σ := (Finset.mem_filter.1 hi).2
      have hj' : π j = σ := (Finset.mem_filter.1 hj).2
      refine (hlab.bijOn σ).injOn hi' hj' ?_
      rw [← Set.image_preimage_eq_of_subset hCi.1, ← Set.image_preimage_eq_of_subset hCj.1,
        ← hCi.2, ← hCj.2]
    · exact Finset.finite_toSet _
    · intro i _
      refine Set.Subsingleton.finite fun C hC C' hC' ↦ ?_
      exact Subtype.ext (eq_of_closure_eq (hC.2.trans hC'.2.symm))
  -- assemble
  have hP : ∀ σ : {σ : DoubleSurface F // σ.fst = E.1},
      G.1.ι.base ⁻¹' ((rhoOf hB σ.1 σ.2).support : Set _) = φ ⁻¹' σ.1.carrier := by
    intro σ
    rw [hφdef, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
      ← image_support_rhoOf hB σ.1 σ.2]
    congr 1
    exact (Set.preimage_image_eq _ ι.isClosedEmbedding.injective).symm
  rw [restrictionClass, sum_surfaceCoefficientDivisor hB a E.1]
  swap
  · intro P
    exact zero_smul _ _
  calc _ = ∑ σ : {σ : DoubleSurface F // σ.fst = E.1}, a σ.1 •
        ∑ i ∈ Finset.univ.filter (fun i ↦ π i = σ.1), curveClassOn G (lab i) := by
        refine Finset.sum_congr rfl fun σ _ ↦ ?_
        rw [hP σ, hσ σ.1 σ.2]
    _ = ∑ σ ∈ Finset.univ.filter (fun σ : DoubleSurface F ↦ σ.fst = E.1), a σ •
        ∑ i ∈ Finset.univ.filter (fun i ↦ π i = σ), curveClassOn G (lab i) :=
        (Finset.sum_subtype (Finset.univ.filter fun σ : DoubleSurface F ↦ σ.fst = E.1)
          (fun σ ↦ by simp) (fun σ ↦ a σ •
            ∑ i ∈ Finset.univ.filter (fun i ↦ π i = σ), curveClassOn G (lab i))).symm
    _ = ∑ σ ∈ Finset.univ.filter (fun σ : DoubleSurface F ↦ σ.fst = E.1),
        ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1) with π i = σ,
          a (π i) • curveClassOn G (lab i) := by
        refine Finset.sum_congr rfl fun σ hσ ↦ ?_
        rw [Finset.smul_sum, Finset.filter_filter]
        refine (Finset.sum_congr ?_ fun i hi ↦ ?_)
        · ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; exact ⟨h ▸ (Finset.mem_filter.1 hσ).2, h⟩
          · exact fun h ↦ h.2
        · rw [(Finset.mem_filter.1 hi).2.2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi ↦ by simpa using hi) _

/-- A closed set `K` either maps onto a set containing `T`, or misses the fibres over the closed
points of an open meeting `T`. -/
private theorem exists_open_imp_subset_image {Z Y : Scheme.{0}} (r : Z ⟶ Y)
    (hr : IsClosedMap r.base) (T : IrreducibleCloseds Y) {K : Set Z} (hK : IsClosed K) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      y ∈ r.base '' K → (T : Set Y) ⊆ r.base '' K := by
  by_cases h : (T : Set Y) ⊆ r.base '' K
  · obtain ⟨t, ht⟩ := T.isIrreducible.nonempty
    exact ⟨⊤, ⟨t, trivial, ht⟩, fun _ _ _ ↦ h⟩
  · obtain ⟨t, htT, htK⟩ := Set.not_subset.1 h
    exact ⟨⟨(r.base '' K)ᶜ, (hr K hK).isOpen_compl⟩, ⟨t, htK, htT⟩,
      fun y hy hyK ↦ absurd hyK hy.1⟩

/-- A curve `T` does not lie in a single point. -/
private theorem not_subset_singleton_of_topologicalKrullDim_eq_one {Y : Type*}
    [TopologicalSpace Y] {T : Set Y} (hT1 : topologicalKrullDim T = 1) (y : Y) :
    ¬ T ⊆ {y} := by
  intro h
  haveI : Subsingleton T := ⟨fun a b ↦ Subtype.ext ((h a.2).trans (h b.2).symm)⟩
  have := topologicalKrullDim_zero_of_discreteTopology T
  rw [hT1] at this
  exact absurd this (by decide)

/-- An element of `WithBot ℕ∞` below `2` is at most `1`. -/
private theorem le_one_of_lt_two {e : WithBot ℕ∞} (h : e < ((2 : ℕ) : WithBot ℕ∞)) :
    e ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe e =>
      have h' : ((e : ℕ∞) : WithBot ℕ∞) < (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have h'' : e < 2 := by exact_mod_cast WithBot.coe_lt_coe.1 h'
      have : e ≤ 1 := by omega
      exact WithBot.coe_le_coe.2 (by exact_mod_cast this)

/-- **Double surfaces over a general point.** Over a general open of `T`, a double surface
whose image contains a closed point of `T` maps onto `T`. -/
private theorem exists_open_doubleSurface_image_eq
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      ∀ σ : DoubleSurface F, y ∈ r.base '' σ.carrier → r.base '' σ.carrier = T := by
  classical
  have := noetherianSpace_of_isComplexScheme (X := Z)
  have := finite_doubleSurface F
  letI : Fintype (DoubleSurface F) := Fintype.ofFinite _
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  refine exists_forall_of_finite T (fun (σ : DoubleSurface F) y ↦ y ∈ r.base '' σ.carrier →
    r.base '' σ.carrier = T) fun σ ↦ ?_
  have hPcl : ∀ P : MMP.Mori.PrimeDivisor Z, IsClosed (P.support : Set Z) := fun P ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  have hσcl : IsClosed σ.carrier := by
    obtain ⟨x, -, hx⟩ := σ.isComponent
    rw [← hx]
    exact MMP.Fourfold.ConductorBlowup.isClosed_connectedComponentIn
      ((hPcl _).inter (hPcl _)) x
  have hσE : σ.carrier ⊆ (σ.fst.support : Set Z) := by
    obtain ⟨x, -, hx⟩ := σ.isComponent
    rw [← hx]
    exact (connectedComponentIn_subset _ _).trans Set.inter_subset_left
  obtain ⟨U, hU, hP⟩ := exists_open_imp_subset_image r r.isClosedMap T hσcl
  refine ⟨U, hU, fun y hy hyσ ↦ ?_⟩
  have hTσ := hP y hy hyσ
  set K : Set Y := r.base '' (σ.fst.support : Set Z)
  have hKirr : IsIrreducible K := by
    have : IsIrreducible (σ.fst.support : Set Z) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact isIrreducible_singleton.closure
    exact this.image _ r.continuous.continuousOn
  have hσK : r.base '' σ.carrier ⊆ K := Set.image_mono hσE
  have hKT : K = T := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hKirr T.isClosed
      (hTσ.trans hσK) (Ne.symm hne) (ne_top_of_le_ne_top (by decide)
        (hM.topologicalKrullDim_image_le σ.fst σ.fst_mem))
    rw [hT1] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le σ.fst σ.fst_mem)) (lt_irrefl _)
  exact le_antisymm (hKT ▸ hσK) hTσ

/-- **No vertical double surfaces over a general point.** Over a general open of `T`, an
irreducible closed set lying in two components of `F` and in the fibre over a closed point of `T`
has dimension at most one. -/
private theorem exists_open_topologicalKrullDim_inter_fibre_le
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      ∀ E E' : F.support, E ≠ E' → ∀ X : Set Z, IsIrreducible X → IsClosed X →
        X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} →
        topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  classical
  have := noetherianSpace_of_isComplexScheme (X := Z)
  have hres := hM.isResolution
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  haveI : IsIntegral Z := (inferInstance : MMP.Mori.IsVariety ℂ (r ≫ sY)).toIsIntegral
  haveI : LocallyOfFiniteType (r ≫ sY) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have hPcl : ∀ P : MMP.Mori.PrimeDivisor Z, IsClosed (P.support : Set Z) := fun P ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  -- the irreducible components of the double intersections
  have hS : ∀ p : F.support × F.support, ∃ 𝒦 : Set (Set Z), 𝒦.Finite ∧ (∀ K ∈ 𝒦, IsClosed K) ∧
      (∀ K ∈ 𝒦, IsIrreducible K) ∧ (p.1.1.support : Set Z) ∩ p.2.1.support = ⋃₀ 𝒦 :=
    fun p ↦ NoetherianSpace.exists_finite_set_isClosed_irreducible ((hPcl _).inter (hPcl _))
  choose 𝒦 h𝒦f h𝒦c h𝒦i h𝒦 using hS
  haveI : ∀ p, Finite (𝒦 p) := fun p ↦ (h𝒦f p).to_subtype
  letI : Fintype (Σ p : F.support × F.support, 𝒦 p) := Fintype.ofFinite _
  obtain ⟨U, hU, hP⟩ := exists_forall_of_finite T
    (fun (q : Σ p : F.support × F.support, 𝒦 p) y ↦ y ∈ r.base '' (q.2 : Set Z) →
      (T : Set Y) ⊆ r.base '' (q.2 : Set Z))
    fun q ↦ exists_open_imp_subset_image r r.isClosedMap T (h𝒦c q.1 q.2 q.2.2)
  refine ⟨U, hU, fun y hy E E' hEE' X hX hXc hXs ↦ ?_⟩
  -- `X` lies in a component `K` of `E ∩ E'`
  have hXK : ∃ K ∈ 𝒦 (E, E'), X ⊆ K := by
    obtain ⟨K, hK, hXK⟩ := (isIrreducible_iff_sUnion_isClosed.1 hX) (h𝒦f (E, E')).toFinset
      (fun K hK ↦ h𝒦c _ K ((h𝒦f (E, E')).mem_toFinset.1 hK))
      (by
        have h := h𝒦 (E, E')
        simp only at h
        rw [Set.Finite.coe_toFinset, ← h]
        exact fun x hx ↦ ⟨(hXs hx).1.1, (hXs hx).1.2⟩)
    exact ⟨K, (h𝒦f (E, E')).mem_toFinset.1 hK, hXK⟩
  obtain ⟨K, hK, hXK⟩ := hXK
  have hyK : y ∈ r.base '' K := by
    obtain ⟨x, hx⟩ := hX.nonempty
    exact ⟨x, hXK hx, (hXs hx).2⟩
  have hTK := hP y hy ⟨(E, E'), ⟨K, hK⟩⟩ hyK
  have hne : X ≠ K := by
    rintro rfl
    refine not_subset_singleton_of_topologicalKrullDim_eq_one hT1 y (hTK.trans ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact (hXs hx).2
  have hdimK : topologicalKrullDim K ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    have hsub : K ⊆ (E.1.support : Set Z) ∩ E'.1.support := by
      have h := h𝒦 (E, E')
      simp only at h
      rw [h]
      exact Set.subset_sUnion_of_mem hK
    refine le_trans (topologicalKrullDim_le_of_subset hsub) ?_
    have h := MMP.Fourfold.topologicalKrullDim_subscheme_le_of_isSNC ℂ (r ≫ sY) hdimZ hM.isSNC
      (f := ![E, E']) (Fin.cons_injective_iff.2 ⟨by simpa using hEE',
        Function.injective_of_subsingleton _⟩)
      (Scheme.IdealSheafData.vanishingIdeal
        ⟨(E.1.support : Set Z) ∩ E'.1.support, (hPcl _).inter (hPcl _)⟩)
      (by
        rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
        intro x hx
        simp only [Set.mem_iInter, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        exact ⟨hx.1, hx.2⟩)
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
    exact h
  have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne (h𝒦i _ K hK) hXc hXK hne
    (ne_top_of_le_ne_top (by decide) hdimK)
  exact le_one_of_lt_two (hlt.trans_le hdimK)

/-! ### The components of a general fibre -/

/-- The components of the fibre `r⁻¹(y)`: a component `E` of `F` and a surface `G ⊆ E` which is
a maximal irreducible subset of the fibre of `E` over `y`. -/
private abbrev FibreComponent {Z Y : Scheme.{0}} (r : Z ⟶ Y) (F : Divisor Z) (y : Y) : Type :=
  Σ E : F.support, {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
    Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
      (G.1.support : Set E.1.idealSheaf.subscheme)}

/-- The reduced fibre `r⁻¹(y)` over a closed point, as an ideal sheaf. -/
private noncomputable abbrev fibreIdeal {Z Y : Scheme.{0}} (r : Z ⟶ Y) {y : Y} (hy : IsClosed {y}) :
    Z.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩

/-- A fibre component, as a closed subscheme of `Z`. -/
private noncomputable abbrev FibreComponent.toZ {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (j : FibreComponent r F y) : j.2.1.1.toScheme ⟶ Z :=
  j.2.1.1.ι ≫ j.1.1.idealSheaf.subschemeι

private theorem FibreComponent.range_toZ {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (j : FibreComponent r F y) :
    Set.range j.toZ.base = j.1.1.idealSheaf.subschemeι.base '' (j.2.1.1.support : Set _) := by
  change Set.range ((j.2.1.1.ι).base ≫ (j.1.1.idealSheaf.subschemeι).base) = _
  rw [TopCat.coe_comp, Set.range_comp]
  congr 1
  exact j.2.1.1.ideal.range_subschemeι

private theorem FibreComponent.range_toZ_subset {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (j : FibreComponent r F y) : Set.range j.toZ.base ⊆ r.base ⁻¹' {y} := by
  rw [j.range_toZ]
  rintro _ ⟨x, hx, rfl⟩
  exact j.2.2.1.2 hx

private theorem FibreComponent.ker_le {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (hy : IsClosed {y}) (j : FibreComponent r F y) :
    (fibreIdeal r hy).subschemeι.ker ≤ j.toZ.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono (Closeds.closure_le.2 j.range_toZ_subset)

/-- A fibre component, as a closed subscheme of the reduced fibre. -/
private noncomputable def FibreComponent.toFibre {Z Y : Scheme.{0}} {r : Z ⟶ Y}
    {F : Divisor Z} {y : Y} (hy : IsClosed {y}) (j : FibreComponent r F y) :
    j.2.1.1.toScheme ⟶ (fibreIdeal r hy).subscheme :=
  IsClosedImmersion.lift _ j.toZ (j.ker_le hy)

private theorem FibreComponent.toFibre_comp {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (hy : IsClosed {y}) (j : FibreComponent r F y) :
    j.toFibre hy ≫ (fibreIdeal r hy).subschemeι = j.toZ :=
  IsClosedImmersion.lift_fac _ _ _

private instance FibreComponent.isClosedImmersion_toFibre {Z Y : Scheme.{0}} {r : Z ⟶ Y}
    {F : Divisor Z} {y : Y} (hy : IsClosed {y}) (j : FibreComponent r F y) :
    IsClosedImmersion (j.toFibre hy) := by
  haveI : IsClosedImmersion (j.toFibre hy ≫ (fibreIdeal r hy).subschemeι) := by
    rw [j.toFibre_comp]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (fibreIdeal r hy).subschemeι

private instance FibreComponent.isOver_toFibre {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    {r : Z ⟶ Y} {F : Divisor Z} {y : Y} (hy : IsClosed {y}) (j : FibreComponent r F y) :
    (j.toFibre hy).IsOver (Spec (.of ℂ)) := ⟨by
  change j.toFibre hy ≫ (fibreIdeal r hy).subschemeι ≫ Z ↘ Spec (.of ℂ) =
    j.toZ ≫ Z ↘ Spec (.of ℂ)
  rw [← Category.assoc, j.toFibre_comp]⟩

private theorem FibreComponent.range_toFibre {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (hy : IsClosed {y}) (j : FibreComponent r F y) :
    Set.range (j.toFibre hy).base =
      (fibreIdeal r hy).subschemeι.base ⁻¹' Set.range j.toZ.base := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by rw [← j.toFibre_comp hy]; rfl⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, (fibreIdeal r hy).subschemeι.isClosedEmbedding.injective ?_⟩
    change (j.toFibre hy ≫ (fibreIdeal r hy).subschemeι).base z = _
    rw [j.toFibre_comp hy, hz]

/-- The double locus of the fibre: the points on two fibre components. -/
private abbrev fibreDoubleLocus {Z Y : Scheme.{0}} (r : Z ⟶ Y) (F : Divisor Z) {y : Y}
    (hy : IsClosed {y}) : Set (fibreIdeal r hy).subscheme :=
  ⋃ j : FibreComponent r F y, ⋃ k : FibreComponent r F y, ⋃ (_ : j ≠ k),
    Set.range (j.toFibre hy).base ∩ Set.range (k.toFibre hy).base

private theorem finite_fibreComponent {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] (r : Z ⟶ Y) (F : Divisor Z) (y : Y) : Finite (FibreComponent r F y) := by
  haveI : ∀ E : F.support, Finite {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
        (G.1.support : Set _)} := fun E ↦ by
    have := noetherianSpace_of_isComplexScheme (X := E.1.idealSheaf.subscheme)
    have := (finite_setOf_maximal ((E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})).to_subtype
    refine Finite.of_injective (β := {A | Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A})
      (fun G ↦ ⟨(G.1.1.support : Set _), G.2⟩) fun G G' h ↦ ?_
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext (Subvariety.support_injective h))
  infer_instance

/-- Over a point where every fibre component of every `E` is a surface, every point of the fibre
of `E` lies on a fibre component. -/
private theorem exists_fibreComponent_mem {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (hy : IsClosed {y})
    (hdim2 : ∀ (E : F.support) (A : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (E : F.support) (z : E.1.idealSheaf.subscheme)
    (hz : (E.1.idealSheaf.subschemeι ≫ r).base z = y) :
    ∃ G : {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} // Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _)},
      z ∈ (G.1.1.support : Set _) := by
  have hcl : IsClosed ((E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) :=
    hy.preimage (E.1.idealSheaf.subschemeι ≫ r).continuous
  obtain ⟨A, hzA, hA⟩ := exists_subset_maximal_of_isIrreducible
    (S := (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) isIrreducible_singleton
    (Set.singleton_subset_iff.2 (show z ∈ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y} from hz))
  have hAcl : IsClosed A := by
    have h := hA.2 ⟨hA.1.1.closure, closure_minimal hA.1.2 hcl⟩ subset_closure
    exact closure_subset_iff_isClosed.1 h
  let G0 := Subvariety.ofIrreducibleCloseds (⟨A, hA.1.1, hAcl⟩ : IrreducibleCloseds _)
  have hG0 : (G0.support : Set _) = A := by
    rw [Subvariety.support_ofIrreducibleCloseds]
    rfl
  have hdim : G0.HasDim ((2 : ℕ) : ℤ) := by
    rw [Subvariety.HasDim, MMP.Intersection.hasDim_natCast_iff]
    change G0.dim = _
    rw [Subvariety.dim_eq_topologicalKrullDim_support, hG0]
    exact hdim2 E A hA
  exact ⟨⟨⟨G0, hdim⟩, by rw [hG0]; exact hA⟩, by rw [hG0]; exact hzA rfl⟩

/-- **The excision hypotheses on a general fibre.** The fibre components cover the reduced
fibre, and the double locus and its traces on the components have dimension at most one. -/
private theorem fibreComponent_excision_hyps
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) {y : Y} (hy : IsClosed {y})
    (hyS : y ∈ (singularLocus sY : Set Y))
    (hdim2 : ∀ (E : F.support) (A : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (hEE : ∀ E E' : F.support, E ≠ E' → ∀ X : Set Z, IsIrreducible X → IsClosed X →
      X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} →
      topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    (∀ x : (fibreIdeal r hy).subscheme, ∃ j : FibreComponent r F y,
      x ∈ Set.range (j.toFibre hy).base) ∧
    topologicalKrullDim (fibreDoubleLocus r F hy) ≤ 1 ∧
    ∀ j : FibreComponent r F y,
      topologicalKrullDim ((j.toFibre hy).base ⁻¹' fibreDoubleLocus r F hy) ≤ 1 := by
  classical
  have := finite_fibreComponent r F y
  letI : Fintype (FibreComponent r F y) := Fintype.ofFinite _
  set ιR := (fibreIdeal r hy).subschemeι with hιR
  have hrangeR : Set.range ιR.base = r.base ⁻¹' {y} := by
    rw [hιR, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hEinj : ∀ E : F.support, Function.Injective E.1.idealSheaf.subschemeι.base := fun E ↦
    E.1.idealSheaf.subschemeι.isClosedEmbedding.injective
  have hEr : ∀ E : F.support,
      Set.range E.1.idealSheaf.subschemeι.base = (E.1.support : Set Z) := fun E ↦
    E.1.idealSheaf.range_subschemeι
  have hcov : ∀ x : (fibreIdeal r hy).subscheme, ∃ j : FibreComponent r F y,
      x ∈ Set.range (j.toFibre hy).base := by
    intro x
    have hxy : ιR.base x ∈ r.base ⁻¹' {y} := hrangeR ▸ ⟨x, rfl⟩
    have hx : ιR.base x ∈ (F.supp : Set Z) := by
      rw [hM.supp_eq_preimage_singularLocus, Set.mem_preimage,
        show r.base (ιR.base x) = y from hxy]
      exact hyS
    rw [MMP.Mori.DivisorWithCoeffs.coe_supp] at hx
    obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨z, hz⟩ : ιR.base x ∈ Set.range (E.idealSheaf.subschemeι).base := by
      rw [E.idealSheaf.range_subschemeι]; exact hxE
    have hzy : (E.idealSheaf.subschemeι ≫ r).base z = y := by
      show r.base (E.idealSheaf.subschemeι.base z) = y
      rw [hz]
      exact hxy
    obtain ⟨G, hzG⟩ := exists_fibreComponent_mem hy hdim2 ⟨E, hE⟩ z hzy
    refine ⟨⟨⟨E, hE⟩, G⟩, ?_⟩
    rw [FibreComponent.range_toFibre, Set.mem_preimage, FibreComponent.range_toZ]
    exact ⟨z, hzG, hz⟩
  -- the components are irreducible surfaces, none inside another
  have hirr : ∀ j : FibreComponent r F y, IsIrreducible (Set.range (j.toFibre hy).base) :=
    fun j ↦ by
      rw [← Set.image_univ]
      exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) _
        (j.toFibre hy).continuous.continuousOn
  have hdimG : ∀ j : FibreComponent r F y,
      topologicalKrullDim j.2.1.1.toScheme = ((2 : ℕ) : WithBot ℕ∞) := fun j ↦
    (MMP.Intersection.hasDim_natCast_iff 2).1 j.2.1.2
  have hdim_mG : ∀ j : FibreComponent r F y,
      topologicalKrullDim (Set.range (j.toFibre hy).base) = ((2 : ℕ) : WithBot ℕ∞) := fun j ↦ by
    rw [← (j.toFibre hy).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
      |>.topologicalKrullDim_eq]
    exact hdimG j
  have hdim_gZ : ∀ j : FibreComponent r F y,
      topologicalKrullDim (Set.range j.toZ.base) = ((2 : ℕ) : WithBot ℕ∞) := fun j ↦ by
    rw [← j.toZ.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact hdimG j
  have hninc : ∀ j k : FibreComponent r F y, j ≠ k →
      ¬ Set.range (j.toFibre hy).base ⊆ Set.range (k.toFibre hy).base := by
    intro j k hjk hsub
    have hZsub : Set.range j.toZ.base ⊆ Set.range k.toZ.base := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨w, hw⟩ := hsub ⟨z, rfl⟩
      refine ⟨w, ?_⟩
      rw [← k.toFibre_comp hy, ← j.toFibre_comp hy]
      change ιR.base ((k.toFibre hy).base w) = ιR.base ((j.toFibre hy).base z)
      rw [hw]
    by_cases hE : j.1 = k.1
    · obtain ⟨E, G, hG⟩ := j
      obtain ⟨E', G', hG'⟩ := k
      simp only at hE
      subst hE
      have hsub' : (G.1.support : Set E.1.idealSheaf.subscheme) ⊆
          (G'.1.support : Set E.1.idealSheaf.subscheme) := by
        intro x hx
        have h := hZsub (by
          rw [FibreComponent.range_toZ]
          exact ⟨x, hx, rfl⟩)
        rw [FibreComponent.range_toZ] at h
        obtain ⟨x', hx', he⟩ := h
        exact hEinj E he ▸ hx'
      have heq : (G.1.support : Set E.1.idealSheaf.subscheme) =
          (G'.1.support : Set E.1.idealSheaf.subscheme) :=
        le_antisymm hsub' (hG.2 hG'.1 hsub')
      have : G = G' := Subtype.ext (Subvariety.support_injective heq)
      subst this
      exact hjk rfl
    · have hsubE : ∀ l : FibreComponent r F y, Set.range l.toZ.base ⊆ (l.1.1.support : Set Z) := by
        intro l
        rw [FibreComponent.range_toZ, ← hEr]
        exact Set.image_subset_range _ _
      have h := hEE j.1 k.1 hE (Set.range j.toZ.base) (by
          rw [← Set.image_univ]
          exact IsIrreducible.image (IrreducibleSpace.isIrreducible_univ _) _
            j.toZ.continuous.continuousOn)
        j.toZ.isClosedEmbedding.isClosed_range
        (fun x hx ↦ ⟨⟨hsubE j hx, hsubE k (hZsub hx)⟩, j.range_toZ_subset hx⟩)
      rw [hdim_gZ] at h
      exact absurd h (by decide)
  have hdim_inter : ∀ j k : FibreComponent r F y, j ≠ k →
      topologicalKrullDim ↥(Set.range (j.toFibre hy).base ∩ Set.range (k.toFibre hy).base) ≤
        ((1 : ℕ) : WithBot ℕ∞) := by
    intro j k hjk
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne (hirr j)
      ((j.toFibre hy).isClosedEmbedding.isClosed_range.inter
        (k.toFibre hy).isClosedEmbedding.isClosed_range)
      Set.inter_subset_left (fun h ↦ hninc j k hjk (h ▸ Set.inter_subset_right))
      (by rw [hdim_mG]; decide)
    rw [hdim_mG] at hlt
    exact le_one_of_lt_two hlt
  have hAdim : topologicalKrullDim (fibreDoubleLocus r F hy) ≤ 1 := by
    let B : FibreComponent r F y × FibreComponent r F y → Set (fibreIdeal r hy).subscheme :=
      fun p ↦ Set.range (p.1.toFibre hy).base ∩ Set.range (p.2.toFibre hy).base
    let t := Finset.univ.filter fun p : FibreComponent r F y × FibreComponent r F y ↦ p.1 ≠ p.2
    have hA' : fibreDoubleLocus r F hy = ⋃ p ∈ t, B p := by
      ext x
      simp only [fibreDoubleLocus, B, t, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
        true_and, exists_prop, Prod.exists]
    have key := topologicalKrullDim_biUnion_le (c := ((1 : ℕ) : WithBot ℕ∞)) t (A := B)
      (fun p ↦ (p.1.toFibre hy).isClosedEmbedding.isClosed_range.inter
        (p.2.toFibre hy).isClosedEmbedding.isClosed_range)
      (fun p hp ↦ hdim_inter p.1 p.2 (Finset.mem_filter.1 hp).2)
    rw [hA']
    exact key.trans (le_of_eq Nat.cast_one)
  refine ⟨hcov, hAdim, fun j ↦ ?_⟩
  have hind : Topology.IsInducing (fun x : ((j.toFibre hy).base ⁻¹' fibreDoubleLocus r F hy :
      Set j.2.1.1.toScheme) ↦ (⟨(j.toFibre hy).base x.1, x.2⟩ : fibreDoubleLocus r F hy)) :=
    ((j.toFibre hy).isClosedEmbedding.isInducing.comp Topology.IsInducing.subtypeVal).codRestrict _
  exact hind.topologicalKrullDim_le.trans hAdim

/-- The curves of a fibre component `G ⊆ E` on a divisor `P` of `E` are those of the reduced
fibre on `P`, read on `G`: pushed forward to the fibre, the curve classes of `P` on the
components `G` of the fibre of `E` add up to the curve class of `P` on the fibre. -/
private theorem sum_pushforward_curves_eq
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {r : Z ⟶ Y} {F : Divisor Z} {y : Y} (hy : IsClosed {y})
    (hdisj : ∀ (E : F.support) (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    (hdim2 : ∀ (E : F.support) (A : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (E : F.support) [Fintype {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
        (G.1.support : Set E.1.idealSheaf.subscheme)}]
    (P : MMP.Mori.PrimeDivisor E.1.idealSheaf.subscheme) :
    ∑ G : {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
        (G.1.support : Set E.1.idealSheaf.subscheme)},
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ)
          (FibreComponent.toFibre (F := F) hy ⟨E, G⟩)))
        (IsComplexScheme.isProperMap_map _) (2 * 1 : ℕ)).hom
        (∑ᶠ (x : CurvePt G.1.1.toScheme)
          (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ G.1.1.ι.base ⁻¹' (P.support : Set _))
            (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) =
    ∑ᶠ (x : CurvePt (fibreIdeal r hy).subscheme)
      (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (fibreIdeal r hy).subschemeι.base ⁻¹'
          (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
        (closure {x.1})),
      Chow.pointCycleClass ℚ x.1 x.2 := by
  classical
  let Sub := {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
    Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
      (G.1.support : Set E.1.idealSheaf.subscheme)}
  let mG : ∀ G : Sub, G.1.1.toScheme ⟶ (fibreIdeal r hy).subscheme := fun G ↦
    FibreComponent.toFibre (F := F) hy ⟨E, G⟩
  have hmG : ∀ G : Sub,
      mG G ≫ (fibreIdeal r hy).subschemeι = G.1.1.ι ≫ E.1.idealSheaf.subschemeι := fun G ↦
    FibreComponent.toFibre_comp (F := F) hy ⟨E, G⟩
  have hmGb : ∀ (G : Sub) x, (fibreIdeal r hy).subschemeι.base ((mG G).base x) =
      E.1.idealSheaf.subschemeι.base (G.1.1.ι.base x) := fun G x ↦ by
    change (mG G ≫ (fibreIdeal r hy).subschemeι).base x =
      (G.1.1.ι ≫ E.1.idealSheaf.subschemeι).base x
    rw [hmG]
  have hEinj : Function.Injective E.1.idealSheaf.subschemeι.base :=
    E.1.idealSheaf.subschemeι.isClosedEmbedding.injective
  have hrangeR : Set.range (fibreIdeal r hy).subschemeι.base = r.base ⁻¹' {y} := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let SR : Set (fibreIdeal r hy).subscheme := (fibreIdeal r hy).subschemeι.base ⁻¹'
    (E.1.idealSheaf.subschemeι.base '' (P.support : Set _))
  -- the trace of `SR` on a component `G`
  have hpre : ∀ G : Sub, (mG G).base ⁻¹' SR = G.1.1.ι.base ⁻¹' (P.support : Set _) := by
    intro G
    ext x
    change (fibreIdeal r hy).subschemeι.base ((mG G).base x) ∈
        E.1.idealSheaf.subschemeι.base '' (P.support : Set _) ↔
      G.1.1.ι.base x ∈ (P.support : Set _)
    rw [hmGb]
    exact hEinj.mem_set_image
  -- a maximal irreducible subset of `SR` lies in a component or misses it
  have hsep : ∀ (G : Sub) C₁, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ SR) C₁ →
      C₁ ⊆ Set.range (mG G).base ∨ Disjoint C₁ (Set.range (mG G).base) := by
    intro G C₁ hC₁
    have hirr : IsIrreducible ((fibreIdeal r hy).subschemeι.base '' C₁) :=
      hC₁.1.1.image _ (fibreIdeal r hy).subschemeι.continuous.continuousOn
    have hsubE : (fibreIdeal r hy).subschemeι.base '' C₁ ⊆
        Set.range E.1.idealSheaf.subschemeι.base := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨z, -, hz⟩ := hC₁.1.2 hx
      exact ⟨z, hz⟩
    have hirr' := isIrreducible_preimage_of_isEmbedding
      E.1.idealSheaf.subschemeι.isClosedEmbedding.isEmbedding hirr hsubE
    have hfib : E.1.idealSheaf.subschemeι.base ⁻¹' ((fibreIdeal r hy).subschemeι.base '' C₁) ⊆
        (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y} := by
      rintro z ⟨x, -, hx⟩
      change r.base (E.1.idealSheaf.subschemeι.base z) = y
      rw [← hx]
      exact (hrangeR ▸ ⟨x, rfl⟩ : (fibreIdeal r hy).subschemeι.base x ∈ r.base ⁻¹' {y})
    obtain ⟨A, hCA, hA⟩ := exists_subset_maximal_of_isIrreducible hirr' hfib
    have hrange : Set.range (mG G).base =
        (fibreIdeal r hy).subschemeι.base ⁻¹'
          (E.1.idealSheaf.subschemeι.base '' (G.1.1.support : Set _)) := by
      rw [show mG G = FibreComponent.toFibre (F := F) hy ⟨E, G⟩ from rfl,
        FibreComponent.range_toFibre, FibreComponent.range_toZ]
    by_cases hAG : A = G.1.1.support
    · left
      intro x hx
      rw [hrange]
      obtain ⟨z, hz⟩ := hsubE ⟨x, hx, rfl⟩
      exact ⟨z, hAG ▸ hCA (show E.1.idealSheaf.subschemeι.base z ∈
        (fibreIdeal r hy).subschemeι.base '' C₁ from hz ▸ ⟨x, hx, rfl⟩), hz⟩
    · right
      rw [Set.disjoint_left]
      intro x hx hxG
      rw [hrange] at hxG
      obtain ⟨z, hzG, hz⟩ := hxG
      exact Set.disjoint_left.1 (hdisj E A _ hA G.2 hAG) (hCA (show
        E.1.idealSheaf.subschemeι.base z ∈ (fibreIdeal r hy).subschemeι.base '' C₁
        from hz ▸ ⟨x, hx, rfl⟩)) hzG
  -- the curves of `SR` and of the traces
  have hdG : ∀ (G : Sub) (x : G.1.1.toScheme),
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (G.1.1.toScheme ↘ Spec (.of ℂ)) x =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        ((fibreIdeal r hy).subscheme ↘ Spec (.of ℂ)) ((mG G).base x) := fun G x ↦
    relativeDimension_closedImmersion (mG G) x
  let im : ∀ G : Sub, CurvePt G.1.1.toScheme → CurvePt (fibreIdeal r hy).subscheme :=
    fun G x ↦ ⟨(mG G).base x.1, (hdG G x.1).symm.trans x.2⟩
  have him : ∀ G (C : CurvePt G.1.1.toScheme), closure {(im G C).1} =
      (mG G).base '' closure {C.1} := fun G C ↦ by
    rw [← (mG G).isClosedEmbedding.closure_image_eq, Set.image_singleton]
  have himinj : ∀ G, Function.Injective (im G) := fun G C C' h ↦
    Subtype.ext ((mG G).isClosedEmbedding.injective (congrArg Subtype.val h))
  let MaxR : Set (CurvePt (fibreIdeal r hy).subscheme) :=
    {C | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ SR) (closure {C.1})}
  let MaxG : ∀ G : Sub, Set (CurvePt G.1.1.toScheme) := fun G ↦
    {C | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ G.1.1.ι.base ⁻¹' (P.support : Set _))
      (closure {C.1})}
  have hmax_iff : ∀ G C, C ∈ MaxG G ↔ im G C ∈ MaxR := by
    intro G C
    have hemb := (mG G).isClosedEmbedding.isEmbedding
    show Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ G.1.1.ι.base ⁻¹' (P.support : Set _))
        (closure {C.1}) ↔
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ SR) (closure {(im G C).1})
    rw [← hpre, maximal_preimage_iff hemb (hsep G), him]
    constructor
    · rintro ⟨C₁, hC₁, hC₁r, hCC⟩
      rwa [hCC, Set.image_preimage_eq_of_subset hC₁r]
    · intro h
      exact ⟨_, h, Set.image_subset_range _ _,
        (Set.preimage_image_eq _ (mG G).isClosedEmbedding.injective).symm⟩
  have hcover : ∀ C ∈ MaxR, ∃ G C', im G C' = C := by
    intro C hC
    have hx : C.1 ∈ closure ({C.1} : Set (fibreIdeal r hy).subscheme) := subset_closure rfl
    obtain ⟨z, hzP, hz⟩ := hC.1.2 hx
    have hzy : (E.1.idealSheaf.subschemeι ≫ r).base z = y := by
      change r.base (E.1.idealSheaf.subschemeι.base z) = y
      rw [hz]
      have h1 : (fibreIdeal r hy).subschemeι.base C.1 ∈
          Set.range (fibreIdeal r hy).subschemeι.base := ⟨C.1, rfl⟩
      rw [hrangeR] at h1
      exact h1
    obtain ⟨G, hzG⟩ := exists_fibreComponent_mem hy hdim2 E z hzy
    have hxG : C.1 ∈ Set.range (mG G).base := by
      rw [show mG G = FibreComponent.toFibre (F := F) hy ⟨E, G⟩ from rfl,
        FibreComponent.range_toFibre, FibreComponent.range_toZ]
      exact ⟨z, hzG, hz⟩
    obtain ⟨w, hw⟩ := hxG
    exact ⟨G, ⟨w, by rw [hdG G w, hw]; exact C.2⟩, Subtype.ext hw⟩
  have hdisj_im : ∀ G G' C C', im G C = im G' C' → G = G' := by
    intro G G' C C' h
    have hb : (mG G).base C.1 = (mG G').base C'.1 := congrArg Subtype.val h
    have hab : E.1.idealSheaf.subschemeι.base (G'.1.1.ι.base C'.1) =
        E.1.idealSheaf.subschemeι.base (G.1.1.ι.base C.1) := by
      rw [← hmGb, ← hmGb, hb]
    have hmem : G.1.1.ι.base C.1 ∈ (G'.1.1.support : Set _) := by
      rw [← hEinj hab, Subvariety.support_eq, ← G'.1.1.ideal.range_subschemeι]
      exact ⟨C'.1, rfl⟩
    have hmemG : G.1.1.ι.base C.1 ∈ (G.1.1.support : Set _) := by
      rw [Subvariety.support_eq, ← G.1.1.ideal.range_subschemeι]
      exact ⟨C.1, rfl⟩
    by_contra hne
    have hne' : (G.1.1.support : Set E.1.idealSheaf.subscheme) ≠ G'.1.1.support := fun h ↦
      hne (Subtype.ext (Subtype.ext (Subvariety.support_injective h)))
    exact Set.disjoint_left.1 (hdisj E _ _ G.2 G'.2 hne') hmemG hmem
  have hMaxR : MaxR = ⋃ G ∈ (Set.univ : Set Sub), im G '' MaxG G := by
    ext C
    simp only [Set.mem_iUnion, Set.mem_univ, true_and, Set.mem_image, exists_prop]
    constructor
    · intro hC
      obtain ⟨G, C', rfl⟩ := hcover C hC
      exact ⟨G, C', (hmax_iff G C').2 hC, rfl⟩
    · rintro ⟨G, C', hC', rfl⟩
      exact (hmax_iff G C').1 hC'
  have hfin : ∀ G : Sub, (MaxG G).Finite := by
    intro G
    have := noetherianSpace_of_isComplexScheme (X := G.1.1.toScheme)
    refine (finite_setOf_maximal (G.1.1.ι.base ⁻¹' (P.support : Set _))).preimage
      (f := fun C : CurvePt G.1.1.toScheme ↦ closure {C.1}) ?_
    intro C _ C' _ h
    exact Subtype.ext (eq_of_closure_eq h)
  -- compute
  have hpush : ∀ (G : Sub) (C : CurvePt G.1.1.toScheme),
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (mG G)))
        (IsComplexScheme.isProperMap_map _) (2 * 1 : ℕ)).hom
        (Chow.pointCycleClass ℚ C.1 C.2) =
      Chow.pointCycleClass ℚ (im G C).1 (im G C).2 := by
    intro G C
    have h := Chow.pushforward_pointCycleClass ℚ (mG G) C.1 C.2
    have hdeg : (mG G).residueDegree C.1 = 1 :=
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion (mG G) C.1
    simp only [hdeg, Nat.cast_one, one_smul] at h
    refine h.trans ?_
    rw [Chow.pointCycleClassOrZero, dif_pos (im G C).2]
  change ∑ G : Sub, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (mG G)))
      (IsComplexScheme.isProperMap_map _) (2 * 1 : ℕ)).hom
      (∑ᶠ C ∈ MaxG G, Chow.pointCycleClass ℚ C.1 C.2) =
    ∑ᶠ C ∈ MaxR, Chow.pointCycleClass ℚ C.1 C.2
  rw [hMaxR, finsum_mem_biUnion (fun G _ G' _ hGG' ↦ ?_) Set.finite_univ fun G _ ↦
      (hfin G).image _, finsum_mem_univ, finsum_eq_sum_of_fintype]
  · refine Finset.sum_congr rfl fun G _ ↦ ?_
    rw [finsum_mem_image (fun C _ C' _ h ↦ himinj G h)]
    refine (AddMonoidHom.map_finsum_mem (fun C : CurvePt G.1.1.toScheme ↦
        Chow.pointCycleClass ℚ C.1 C.2)
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (mG G)))
        (IsComplexScheme.isProperMap_map _) (2 * 1 : ℕ)).hom.toAddMonoidHom (hfin G)).trans ?_
    exact finsum_mem_congr rfl fun C _ ↦ hpush G C
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨C, -, rfl⟩ ⟨C', -, h⟩
    exact hGG' (hdisj_im G G' C C' h.symm)

/-- **The pushed-forward restriction classes are `w_T(y)`.** Over a point where the fibre
components of each `E` are disjoint surfaces, the classes `[L_E|_G]` of the fibre components,
pushed forward to the reduced fibre, add up to the class `w_T(y)` of the curves cut on the fibre
by the `L_E`. -/
private theorem sum_pushforward_restrictionClass_eq
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {r : Z ⟶ Y} {F : Divisor Z} {y : Y} (hy : IsClosed {y})
    (hdisj : ∀ (E : F.support) (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    (hdim2 : ∀ (E : F.support) (A : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    [∀ E : F.support, Fintype {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
        (G.1.support : Set E.1.idealSheaf.subscheme)}]
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme) :
    ∑ j : FibreComponent r F y, (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (j.toFibre hy)))
        (IsComplexScheme.isProperMap_map _) (2 * 1 : ℕ)).hom (restrictionClass j.2.1 (L j.1)) =
      ∑ E : F.support, (L E).sum fun P c ↦ c •
        ∑ᶠ (x : CurvePt (fibreIdeal r hy).subscheme)
          (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (fibreIdeal r hy).subschemeι.base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
            (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2 := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun E _ ↦ ?_
  simp only [restrictionClass, Finsupp.sum, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  exact Finset.smul_sum.symm.trans (congrArg _ (sum_pushforward_curves_eq hy hdisj hdim2 E P))

open Classical in
/-- **Each double curve carries one label per pair of components.** At a closed point `y` over
which the double surfaces meeting `r⁻¹(y)` dominate `T` and no surface lies in two components,
a closed irreducible curve `C ⊆ E ∩ r⁻¹(y)` carries exactly one label `i` with `π i ⊆ E ∩ E'`
and `λ i = C` when `C ⊆ E' ≠ E`, and none otherwise. -/
private theorem card_filter_label_eq
    {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z} {T : IrreducibleCloseds Y} {y : Y}
    (hy : IsClosed {y})
    (hσT : ∀ σ : DoubleSurface F, y ∈ r.base '' σ.carrier → r.base '' σ.carrier = T)
    (hEE : ∀ E E' : F.support, E ≠ E' → ∀ X : Set Z, IsIrreducible X → IsClosed X →
      X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} →
      topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    {I : Type} [Fintype I] {π : I → DoubleSurface F} {s : I → I} (hI : IsEdgeIndex r T π s)
    {lab : I → Set Z} (hlab : IsEdgeLabeling r π s y lab)
    (E E' : F.support) {C : Set Z} (hCirr : IsIrreducible C) (hCcl : IsClosed C)
    (hCdim : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞)) (hCy : C ⊆ r.base ⁻¹' {y})
    (hCE : C ⊆ (E.1.support : Set Z)) :
    (Finset.univ.filter fun i ↦ (π i).fst = E.1 ∧ (π i).snd = E'.1 ∧ lab i = C).card =
      if E' ≠ E ∧ C ⊆ (E'.1.support : Set Z) then 1 else 0 := by
  classical
  have hPcl : ∀ P : MMP.Mori.PrimeDivisor Z, IsClosed (P.support : Set Z) := fun P ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure
  -- the label of `C` over a double surface is contained in that surface
  have hlab_sub : ∀ i, lab i ⊆ (π i).carrier := fun i ↦ fun x hx ↦
    (((hlab.bijOn (π i)).mapsTo (show i ∈ {i' | π i' = π i} from rfl)).1.2 hx).1
  split_ifs with h
  · obtain ⟨hne, hCE'⟩ := h
    obtain ⟨x₀, hx₀⟩ := hCirr.nonempty
    let σ₀ : DoubleSurface F :=
      { fst := E.1, snd := E'.1, fst_mem := E.2, snd_mem := E'.2,
        fst_ne_snd := fun h ↦ hne (Subtype.ext h.symm),
        carrier := connectedComponentIn ((E.1.support : Set Z) ∩ E'.1.support) x₀,
        isComponent := ⟨x₀, ⟨hCE hx₀, hCE' hx₀⟩, rfl⟩ }
    have hCσ : C ⊆ σ₀.carrier :=
      hCirr.2.isPreconnected.subset_connectedComponentIn hx₀ fun x hx ↦ ⟨hCE hx, hCE' hx⟩
    have hσ₀T : r.base '' σ₀.carrier = T := hσT σ₀ ⟨x₀, hCσ hx₀, hCy hx₀⟩
    have hCmax : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ₀.carrier ∩ r.base ⁻¹' {y}) C := by
      refine ⟨⟨hCirr, fun x hx ↦ ⟨hCσ hx, hCy hx⟩⟩, fun X hX hCX ↦ ?_⟩
      have hXsub : closure X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} := by
        refine closure_minimal (fun x hx ↦ ?_)
          (((hPcl _).inter (hPcl _)).inter (hy.preimage r.continuous))
        have := hX.2 hx
        exact ⟨connectedComponentIn_subset _ _ this.1, this.2⟩
      have hle := hEE E E' (Ne.symm hne) _ hX.1.closure isClosed_closure hXsub
      by_contra hXC
      have hne' : C ≠ closure X := fun h ↦ hXC (h ▸ subset_closure)
      have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hX.1.closure hCcl
        (hCX.trans subset_closure) hne' (ne_top_of_le_ne_top (by decide) hle)
      rw [hCdim] at hlt
      exact absurd (hlt.trans_le hle) (lt_irrefl _)
    obtain ⟨i, hi, hlabi⟩ := (hlab.bijOn σ₀).surjOn hCmax
    rw [Finset.card_eq_one]
    refine ⟨i, Finset.ext fun i' ↦ ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hf, hs, hl⟩
      have hπ : π i' = σ₀ := by
        refine DoubleSurface.ext hf hs ?_
        obtain ⟨x', -, hx'⟩ := (π i').isComponent
        have hx₀' : x₀ ∈ (π i').carrier := hlab_sub i' (hl ▸ hx₀)
        rw [← hx'] at hx₀' ⊢
        rw [connectedComponentIn_eq hx₀', hf, hs]
      exact (hlab.bijOn σ₀).injOn hπ hi (hl.trans hlabi.symm)
    · rintro rfl
      exact ⟨by rw [hi], by rw [hi], hlabi⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i - ⟨hf, hs, hl⟩
    refine h ⟨fun h' ↦ (π i).fst_ne_snd (hf.trans (h' ▸ hs.symm)), fun x hx ↦ ?_⟩
    have := ((π i).carrier_subset (hlab_sub i (hl ▸ hx))).2
    rwa [hs] at this

open Classical in
/-- The curve class cut on a surface `G ⊆ E` by an irreducible set `S` lying in `G` or missing
it: the class of `S` when `S` is a curve of `G`, and `0` otherwise. -/
private theorem curveClassOn_eq_dite {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {E : MMP.Mori.PrimeDivisor Z} (G : {V : Subvariety E.idealSheaf.subscheme // V.HasDim 2}) {S : Set Z}
    (hS : IsIrreducible S)
    (hsep : S ⊆ Set.range (G.1.ι ≫ E.idealSheaf.subschemeι).base ∨
      Disjoint S (Set.range (G.1.ι ≫ E.idealSheaf.subschemeι).base)) :
    curveClassOn G S = if h : ∃ x : CurvePt G.1.toScheme,
        (G.1.ι ≫ E.idealSheaf.subschemeι).base '' closure {x.1} = S then
      Chow.pointCycleClass ℚ h.choose.1 h.choose.2 else 0 := by
  have hφ : Topology.IsEmbedding (G.1.ι ≫ E.idealSheaf.subschemeι).base :=
    (G.1.ι ≫ E.idealSheaf.subschemeι).isClosedEmbedding.isEmbedding
  have key : ∀ C : CurvePt G.1.toScheme,
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ (G.1.ι ≫ E.idealSheaf.subschemeι).base ⁻¹' S) (closure {C.1}) ↔
      (G.1.ι ≫ E.idealSheaf.subschemeι).base '' closure {C.1} = S := by
    intro C
    rcases hsep with hsub | hdis
    · rw [maximal_subset_iff_of_isIrreducible (isIrreducible_preimage_of_isEmbedding hφ hS hsub)]
      constructor
      · intro h
        rw [h, Set.image_preimage_eq_of_subset hsub]
      · intro h
        rw [← h, Set.preimage_image_eq _ hφ.injective]
    · constructor
      · intro h
        exfalso
        obtain ⟨x, hx⟩ := h.1.1.nonempty
        exact Set.disjoint_left.1 hdis (h.1.2 hx) ⟨x, rfl⟩
      · intro h
        exfalso
        obtain ⟨x, hx⟩ : (closure {C.1} : Set G.1.toScheme).Nonempty :=
          ⟨C.1, subset_closure rfl⟩
        exact Set.disjoint_left.1 hdis (h ▸ ⟨x, hx, rfl⟩) ⟨x, rfl⟩
  unfold curveClassOn
  rw [finsum_congr fun C ↦ finsum_congr_Prop (propext (key C)) fun _ ↦ rfl]
  split_ifs with h
  · rw [finsum_eq_single _ h.choose]
    · rw [finsum_eq_if, if_pos h.choose_spec]
    · intro C hC
      rw [finsum_eq_if, if_neg]
      intro hCS
      apply hC
      exact Subtype.ext (eq_of_closure_eq
        (hφ.injective.image_injective (hCS.trans h.choose_spec.symm)))
  · refine finsum_eq_zero_of_forall_eq_zero fun C ↦ ?_
    rw [finsum_eq_if, if_neg fun hC ↦ h ⟨C, hC⟩]

open Classical in
/-- The coefficient of a label in the edge solution built from coefficients `coef E C` of the
curves `C` on the components `E`: one component `E₀ ∋ C` is chosen, the label of `C` on
`E ∩ E₀` receives `-coef E C`, the one on `E₀ ∩ E` receives `coef E C`, the others `0`. -/
private noncomputable def edgeCoeff {Z : Scheme.{0}} {F : Divisor Z} {I : Type}
    (π : I → DoubleSurface F) (lab : I → Set Z) (coef : F.support → Set Z → ℚ) (i : I) : ℚ :=
  if h : ∃ E : F.support, lab i ⊆ (E.1.support : Set Z) then
    (if h.choose = ⟨(π i).snd, (π i).snd_mem⟩ then -coef ⟨(π i).fst, (π i).fst_mem⟩ (lab i)
      else 0) +
    (if h.choose = ⟨(π i).fst, (π i).fst_mem⟩ then coef ⟨(π i).snd, (π i).snd_mem⟩ (lab i)
      else 0)
  else 0

/-- The edge solution is oriented. -/
private theorem edgeCoeff_swap {Z : Scheme.{0}} {F : Divisor Z} {I : Type}
    {π : I → DoubleSurface F} {lab : I → Set Z} {s : I → I} (coef : F.support → Set Z → ℚ)
    (hπs : ∀ i, π (s i) = (π i).swap) (hlabs : ∀ i, lab (s i) = lab i) (i : I) :
    edgeCoeff π lab coef (s i) = -edgeCoeff π lab coef i := by
  classical
  unfold edgeCoeff
  have h1 : (⟨(π (s i)).fst, (π (s i)).fst_mem⟩ : F.support) = ⟨(π i).snd, (π i).snd_mem⟩ :=
    Subtype.ext (by rw [hπs]; rfl)
  have h2 : (⟨(π (s i)).snd, (π (s i)).snd_mem⟩ : F.support) = ⟨(π i).fst, (π i).fst_mem⟩ :=
    Subtype.ext (by rw [hπs]; rfl)
  simp only [h1, h2, hlabs]
  split_ifs <;> ring

open Classical in
/-- **The edge equation for one curve.** If the coefficients `coef E C` vanish unless `C ⊆ E`
and add up to `0` over `E`, the labels of a curve `C ⊆ E` on the double surfaces `E ∩ E'` carry
edge coefficients adding up to `-coef E C`. -/
private theorem sum_edgeCoeff_eq
    {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z} {T : IrreducibleCloseds Y} {y : Y}
    (hy : IsClosed {y})
    (hσT : ∀ σ : DoubleSurface F, y ∈ r.base '' σ.carrier → r.base '' σ.carrier = T)
    (hEE : ∀ E E' : F.support, E ≠ E' → ∀ X : Set Z, IsIrreducible X → IsClosed X →
      X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} →
      topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    {I : Type} [Fintype I] {π : I → DoubleSurface F} {s : I → I} (hI : IsEdgeIndex r T π s)
    {lab : I → Set Z} (hlab : IsEdgeLabeling r π s y lab)
    (coef : F.support → Set Z → ℚ) (E : F.support) {C : Set Z} (hCirr : IsIrreducible C)
    (hCcl : IsClosed C) (hCdim : topologicalKrullDim C = ((1 : ℕ) : WithBot ℕ∞))
    (hCy : C ⊆ r.base ⁻¹' {y}) (hCE : C ⊆ (E.1.support : Set Z))
    (hK3 : ∀ E', coef E' C ≠ 0 → C ⊆ (E'.1.support : Set Z)) (hK4 : ∑ E', coef E' C = 0) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1 ∧ lab i = C), edgeCoeff π lab coef i =
      -coef E C := by
  have hex : ∃ E' : F.support, C ⊆ (E'.1.support : Set Z) := ⟨E, hCE⟩
  set E₀ := hex.choose with hE₀
  have hE₀C : C ⊆ (E₀.1.support : Set Z) := hex.choose_spec
  let f : F.support → ℚ := fun E' ↦ (if E₀ = E' then -coef E C else 0) +
    (if E₀ = E then coef E' C else 0)
  let snd : I → F.support := fun i ↦ ⟨(π i).snd, (π i).snd_mem⟩
  have hb : ∀ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1 ∧ lab i = C),
      edgeCoeff π lab coef i = f (snd i) := by
    intro i hi
    obtain ⟨hf, hl⟩ := (Finset.mem_filter.1 hi).2
    have hfst : (⟨(π i).fst, (π i).fst_mem⟩ : F.support) = E := Subtype.ext hf
    unfold edgeCoeff
    have hex' : ∃ E' : F.support, lab i ⊆ (E'.1.support : Set Z) := hl ▸ hex
    rw [dif_pos hex']
    have hch : hex'.choose = E₀ := by
      rw [hE₀]
      congr 1
      exact hl ▸ rfl
    simp only [hch]
    simp only [hfst, hl, f, snd]
  rw [Finset.sum_congr rfl hb, ← Finset.sum_fiberwise_of_maps_to (g := snd) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  have hcard : ∀ E' : F.support,
      ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1 ∧ lab i = C) with snd i = E',
        f (snd i) = (if E' ≠ E ∧ C ⊆ (E'.1.support : Set Z) then 1 else 0) • f E' := by
    intro E'
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
      ← card_filter_label_eq hy hσT hEE hI hlab E E' hCirr hCcl hCdim hCy hCE,
      Finset.filter_filter]
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, snd]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, congrArg Subtype.val h3, h2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h3⟩, Subtype.ext h2⟩
  rw [Finset.sum_congr rfl fun E' _ ↦ hcard E']
  by_cases h0 : E₀ = E
  · -- the chosen component is `E`
    have : ∀ E' : F.support, (if E' ≠ E ∧ C ⊆ (E'.1.support : Set Z) then 1 else 0) • f E' =
        if E' = E then 0 else coef E' C := by
      intro E'
      by_cases hE' : E' = E
      · simp [hE']
      · by_cases hCE' : C ⊆ (E'.1.support : Set Z)
        · simp [hE', hCE', f, h0, Ne.symm hE']
        · have : coef E' C = 0 := by
            by_contra hne
            exact hCE' (hK3 E' hne)
          simp [hE', hCE', this]
    rw [Finset.sum_congr rfl fun E' _ ↦ this E',
      ← Finset.sum_erase_add _ _ (Finset.mem_univ E), if_pos rfl, add_zero,
      Finset.sum_congr rfl fun E' hE' ↦ if_neg (Finset.ne_of_mem_erase hE')]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ E)] at hK4
    linarith
  · -- the chosen component is another `E₀ ⊇ C`
    have : ∀ E' : F.support, (if E' ≠ E ∧ C ⊆ (E'.1.support : Set Z) then 1 else 0) • f E' =
        if E' = E₀ then -coef E C else 0 := by
      intro E'
      by_cases hE' : E' = E₀
      · subst hE'
        simp [h0, hE₀C, f]
      · simp [f, h0, Ne.symm hE', hE']
    rw [Finset.sum_congr rfl fun E' _ ↦ this E', Finset.sum_ite_eq' Finset.univ E₀]
    simp

open Classical in
/-- The coefficient of a curve `C ⊆ Z` in the `1`-cycles `γ_G` on the fibre components `G` of a
component `E`, a `1`-cycle being a rational combination of the generic points of its curves. -/
private noncomputable def fibreCoef {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z} {y : Y}
    [Fintype (FibreComponent r F y)]
    (γ : ∀ j : FibreComponent r F y, j.2.1.1.toScheme →₀ ℚ) (E : F.support)
    (C : Set Z) : ℚ :=
  ∑ j ∈ Finset.univ.filter (fun j : FibreComponent r F y ↦ j.1 = E),
    (γ j).sum fun x a ↦ if j.toZ.base '' closure {x} = C then a else 0

/-- A fibre component lies in its component of `F`. -/
private theorem FibreComponent.range_toZ_subset_support {Z Y : Scheme.{0}} {r : Z ⟶ Y}
    {F : Divisor Z} {y : Y} (j : FibreComponent r F y) :
    Set.range j.toZ.base ⊆ (j.1.1.support : Set Z) := by
  rw [j.range_toZ]
  rintro _ ⟨z, -, rfl⟩
  have : j.1.1.idealSheaf.subschemeι.base z ∈ Set.range j.1.1.idealSheaf.subschemeι.base :=
    ⟨z, rfl⟩
  rw [j.1.1.idealSheaf.range_subschemeι] at this
  exact this

/-- A curve of a fibre component, in `Z`: closed, irreducible, one-dimensional, in the fibre. -/
private theorem FibreComponent.curve_props {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} (j : FibreComponent r F y) (V : CurvePt j.2.1.1.toScheme) :
    IsIrreducible (j.toZ.base '' closure {V.1}) ∧
      IsClosed (j.toZ.base '' closure {V.1}) ∧
      topologicalKrullDim (j.toZ.base '' closure {V.1}) = ((1 : ℕ) : WithBot ℕ∞) ∧
      j.toZ.base '' closure {V.1} ⊆ r.base ⁻¹' {y} ∧
      j.toZ.base '' closure {V.1} ⊆ (j.1.1.support : Set Z) := by
  have hemb := j.toZ.isClosedEmbedding
  refine ⟨isIrreducible_singleton.closure.image _ j.toZ.continuous.continuousOn,
    hemb.isClosedMap _ isClosed_closure, ?_,
    (Set.image_subset_range _ _).trans j.range_toZ_subset,
    (Set.image_subset_range _ _).trans j.range_toZ_subset_support⟩
  have h1 : topologicalKrullDim (closure {V.1} : Set j.2.1.1.toScheme) =
      ((1 : ℕ) : WithBot ℕ∞) := by
    rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (j.2.1.1.toScheme ↘ Spec (.of ℂ)) V.1,
      V.2]
    rfl
  have hemb' : Topology.IsEmbedding (fun s : (closure {V.1} : Set j.2.1.1.toScheme) ↦
      j.toZ.base s.1) := hemb.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (fun s : (closure {V.1} : Set j.2.1.1.toScheme) ↦ j.toZ.base s.1) =
      j.toZ.base '' (closure {V.1} : Set j.2.1.1.toScheme) := by
    rw [Set.range_comp' j.toZ.base Subtype.val, Subtype.range_coe]
  rw [← h1]
  exact ((hemb'.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph
    |>.topologicalKrullDim_eq).symm

/-- A nonzero coefficient on `E` lives on a curve of `E`. -/
private theorem subset_of_fibreCoef_ne_zero {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z}
    {y : Y} [Fintype (FibreComponent r F y)]
    (γ : ∀ j : FibreComponent r F y, j.2.1.1.toScheme →₀ ℚ) (E : F.support)
    (C : Set Z) (h : fibreCoef γ E C ≠ 0) : C ⊆ (E.1.support : Set Z) := by
  classical
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨V, -, hV⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hVC : j.toZ.base '' closure {V} = C := by
    by_contra h'
    exact hV (if_neg h')
  rw [← hVC, ← (Finset.mem_filter.1 hj).2]
  exact (Set.image_subset_range _ _).trans j.range_toZ_subset_support

/-- The coefficient of the curve of `V` on its own component is the coefficient of `V`. -/
private theorem fibreCoef_self {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z} {y : Y}
    [Fintype (FibreComponent r F y)]
    (hdisj : ∀ (E : F.support) (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    (γ : ∀ j : FibreComponent r F y, j.2.1.1.toScheme →₀ ℚ)
    (j : FibreComponent r F y) (V : j.2.1.1.toScheme) :
    fibreCoef γ j.1 (j.toZ.base '' closure {V}) = γ j V := by
  classical
  have hinj : ∀ V' : j.2.1.1.toScheme,
      j.toZ.base '' closure {V'} = j.toZ.base '' closure {V} ↔ V' = V := by
    intro V'
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
    exact eq_of_closure_eq (j.toZ.isClosedEmbedding.injective.image_injective h)
  unfold fibreCoef
  rw [Finset.sum_eq_single j]
  · rw [Finsupp.sum]
    refine (Finset.sum_eq_single V ?_ ?_).trans (if_pos rfl)
    · intro V' _ hV'
      exact if_neg fun h ↦ hV' ((hinj V').1 h)
    · intro hV
      rw [if_pos rfl]
      exact Finsupp.notMem_support_iff.1 hV
  · intro k hk hkj
    refine Finset.sum_eq_zero fun V' _ ↦ if_neg fun h ↦ ?_
    obtain ⟨E, G, hG⟩ := j
    obtain ⟨E', G', hG'⟩ := k
    have hE : E' = E := (Finset.mem_filter.1 hk).2
    subst hE
    have hGG : G' ≠ G := fun h' ↦ hkj (by subst h'; rfl)
    have hne : (G'.1.support : Set E'.1.idealSheaf.subscheme) ≠
        (G.1.support : Set E'.1.idealSheaf.subscheme) := fun h' ↦
      hGG (Subtype.ext (Subvariety.support_injective h'))
    have hd := hdisj E' _ _ hG' hG hne
    have hmem : (FibreComponent.toZ (⟨E', G, hG⟩ : FibreComponent r F y)).base V ∈
        (FibreComponent.toZ (⟨E', G', hG'⟩ : FibreComponent r F y)).base ''
          (closure {V'} : Set G'.1.toScheme) := h ▸ ⟨V, subset_closure rfl, rfl⟩
    obtain ⟨x', -, hx'⟩ := hmem
    have h1 : G'.1.ι.base x' ∈ (G'.1.support : Set E'.1.idealSheaf.subscheme) := by
      rw [Subvariety.support_eq, ← G'.1.ideal.range_subschemeι]; exact ⟨x', rfl⟩
    have h2 : G.1.ι.base V ∈ (G.1.support : Set E'.1.idealSheaf.subscheme) := by
      rw [Subvariety.support_eq, ← G.1.ideal.range_subschemeι]; exact ⟨V, rfl⟩
    have heq : G'.1.ι.base x' = G.1.ι.base V :=
      E'.1.idealSheaf.subschemeι.isClosedEmbedding.injective hx'
    exact Set.disjoint_left.1 hd h1 (heq ▸ h2)
  · intro h
    simp at h

/-- The coefficients of the curve of `V` on all components add up to `0`: the push-forwards of
the `γ_G` to the reduced fibre cancel. -/
private theorem sum_fibreCoef_eq_zero {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z} {y : Y}
    (hy : IsClosed {y}) [Fintype (FibreComponent r F y)]
    (γ : ∀ j : FibreComponent r F y, j.2.1.1.toScheme →₀ ℚ)
    (hγ2 : ∑ j, Finsupp.mapDomain (j.toFibre hy).base (γ j) = 0)
    (j : FibreComponent r F y) (V : j.2.1.1.toScheme) :
    ∑ E : F.support, fibreCoef γ E (j.toZ.base '' closure {V}) = 0 := by
  classical
  unfold fibreCoef
  rw [Finset.sum_fiberwise_of_maps_to (g := Sigma.fst) (fun _ _ ↦ Finset.mem_univ _)]
  let CR := (j.toFibre hy).base V
  have hR : Function.Injective (fibreIdeal r hy).subschemeι.base :=
    (fibreIdeal r hy).subschemeι.isClosedEmbedding.injective
  have himg : ∀ (k : FibreComponent r F y) (W : k.2.1.1.toScheme),
      k.toZ.base '' closure {W} = (fibreIdeal r hy).subschemeι.base ''
        closure {(k.toFibre hy).base W} := by
    intro k W
    rw [show closure {(k.toFibre hy).base W} = (k.toFibre hy).base '' closure {W} by
      rw [← Set.image_singleton, (k.toFibre hy).isClosedEmbedding.closure_image_eq],
      Set.image_image, ← k.toFibre_comp hy]
    rfl
  have h0 := congrArg (fun c ↦ c CR) hγ2
  simp only [Finsupp.finset_sum_apply, Finsupp.coe_zero, Pi.zero_apply] at h0
  refine Eq.trans ?_ h0
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun W _ ↦ ?_
  rw [Finsupp.single_apply]
  refine if_congr ?_ rfl rfl
  rw [himg, himg j V]
  constructor
  · intro h
    exact eq_of_closure_eq (hR.image_injective h)
  · intro h
    rw [h]

/-- A label of a double surface of `E` lies in a fibre component `G ⊆ E` or misses it. -/
private theorem label_subset_or_disjoint {Z Y : Scheme.{0}} {r : Z ⟶ Y} {F : Divisor Z} {y : Y}
    (hdisj : ∀ (E : F.support) (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    {I : Type} {π : I → DoubleSurface F} {s : I → I} {lab : I → Set Z}
    (hlab : IsEdgeLabeling r π s y lab) (j : FibreComponent r F y) (i : I)
    (hi : (π i).fst = j.1.1) :
    IsIrreducible (lab i) ∧
      (lab i ⊆ Set.range j.toZ.base ∨ Disjoint (lab i) (Set.range j.toZ.base)) := by
  have hmax := (hlab.bijOn (π i)).mapsTo (show i ∈ {i' | π i' = π i} from rfl)
  have hC := hmax.1.1
  refine ⟨hC, ?_⟩
  set ι := j.1.1.idealSheaf.subschemeι
  have hιemb : Topology.IsEmbedding ι.base := ι.isClosedEmbedding.isEmbedding
  have hCr : lab i ⊆ Set.range ι.base := by
    intro c hc
    have h1 := ((π i).carrier_subset (hmax.1.2 hc).1).1
    rw [hi] at h1
    have : (j.1.1.idealSheaf.support : Set Z) = Set.range ι.base :=
      j.1.1.idealSheaf.range_subschemeι.symm
    exact this ▸ h1
  have hC' := isIrreducible_preimage_of_isEmbedding hιemb hC hCr
  have hC'y : ι.base ⁻¹' lab i ⊆ (ι ≫ r).base ⁻¹' {y} := fun x hx ↦ (hmax.1.2 hx).2
  obtain ⟨A, hCA, hA⟩ := exists_subset_maximal_of_isIrreducible hC' hC'y
  rw [j.range_toZ]
  by_cases hAG : A = j.2.1.1.support
  · left
    intro c hc
    obtain ⟨x, rfl⟩ := hCr hc
    exact ⟨x, hAG ▸ hCA hc, rfl⟩
  · right
    rw [Set.disjoint_left]
    rintro c hc ⟨g, hg, rfl⟩
    exact Set.disjoint_left.1 (hdisj j.1 A _ hA j.2.2 hAG) (hCA hc) hg

open Classical in
/-- **From cycles to edge coefficients.** If the classes `[L_E|_G]` are `-[γ_G]` for `1`-cycles
`γ_G` on the fibre components whose push-forwards to the fibre cancel, the edge solution built
from the coefficients of the `γ_G` is oriented and solves the edge equation. -/
private theorem exists_edgeRelation_of_cycles
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {r : Z ⟶ Y} {F : Divisor Z} {T : IrreducibleCloseds Y} {y : Y} (hy : IsClosed {y})
    (hdisj : ∀ (E : F.support) (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    (hσT : ∀ σ : DoubleSurface F, y ∈ r.base '' σ.carrier → r.base '' σ.carrier = T)
    (hEE : ∀ E E' : F.support, E ≠ E' → ∀ X : Set Z, IsIrreducible X → IsClosed X →
      X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} →
      topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme) [Fintype (FibreComponent r F y)]
    (γ : ∀ j : FibreComponent r F y, j.2.1.1.toScheme →₀ ℚ)
    (hγs : ∀ j : FibreComponent r F y, γ j ∈ Finsupp.supported ℚ ℚ (dimPts j.2.1.1.toScheme 1))
    (hγ1 : ∀ j : FibreComponent r F y,
      restrictionClass j.2.1 (L j.1) + pointsClass j.2.1.1.toScheme 1 (γ j) = 0)
    (hγ2 : ∑ j : FibreComponent r F y, Finsupp.mapDomain (j.toFibre hy).base (γ j) = 0)
    {I : Type} [Fintype I] {π : I → DoubleSurface F} {s : I → I} (hI : IsEdgeIndex r T π s)
    {lab : I → Set Z} (hlab : IsEdgeLabeling r π s y lab) :
    ∃ b : I → ℚ, (∀ i, b (s i) = -b i) ∧ EdgeRelation r L π y lab b := by
  refine ⟨edgeCoeff π lab (fibreCoef γ), fun i ↦ edgeCoeff_swap _ hI.π_s hlab.lab_s i, ?_⟩
  intro E G hG
  let j : FibreComponent r F y := ⟨E, G, hG⟩
  have hρ : restrictionClass G (L E) = -pointsClass G.1.toScheme 1 (γ j) :=
    eq_neg_of_add_eq_zero_left (hγ1 j)
  let cyc : I → G.1.toScheme →₀ ℚ := fun i ↦
    if h : ∃ x : CurvePt G.1.toScheme, j.toZ.base '' closure {x.1} = lab i then
      Finsupp.single h.choose.1 1 else 0
  have hcc : ∀ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
      curveClassOn G (lab i) = pointsClass _ 1 (cyc i) := by
    intro i hi
    obtain ⟨hirr, hsep⟩ := label_subset_or_disjoint hdisj hlab j i (Finset.mem_filter.1 hi).2
    rw [curveClassOn_eq_dite G hirr hsep]
    simp only [cyc]
    split_ifs with h
    · exact ((pointsClass_single _ h.choose.2 1).trans (one_smul _ _)).symm
    · exact (map_zero _).symm
  have hinj : ∀ V V' : CurvePt G.1.toScheme,
      j.toZ.base '' closure {V.1} = j.toZ.base '' closure {V'.1} → V = V' := fun V V' h ↦
    Subtype.ext (eq_of_closure_eq (j.toZ.isClosedEmbedding.injective.image_injective h))
  have hcyc : ∀ (i : I) (V : G.1.toScheme)
      (hV : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (G.1.toScheme ↘ Spec (.of ℂ)) V = (1 : ℕ)), cyc i V =
      if lab i = j.toZ.base '' closure {V} then 1 else 0 := by
    intro i V hV
    simp only [cyc]
    by_cases h : ∃ V' : CurvePt G.1.toScheme, j.toZ.base '' closure {V'.1} = lab i
    · rw [dif_pos h, Finsupp.single_apply]
      by_cases h' : lab i = j.toZ.base '' closure {V}
      · have e1 : h.choose = ⟨V, hV⟩ := hinj _ _ (h.choose_spec.trans h')
        exact (if_pos (congrArg Subtype.val e1)).trans (if_pos h').symm
      · have e1 : ¬ h.choose.1 = V := by
          intro e
          apply h'
          rw [← e]
          exact h.choose_spec.symm
        exact (if_neg e1).trans (if_neg h').symm
    · have e1 : ¬ lab i = j.toZ.base '' closure {V} := fun h' ↦ h ⟨⟨V, hV⟩, h'.symm⟩
      rw [dif_neg h]
      exact (if_neg e1).symm
  have hcyc0 : ∀ (i : I) (V : G.1.toScheme)
      (hV : ¬ Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (G.1.toScheme ↘ Spec (.of ℂ)) V = (1 : ℕ)), cyc i V = 0 := by
    intro i V hV
    simp only [cyc]
    split_ifs with h
    · rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hV h.choose.2
    · rfl
  change restrictionClass G (L E) =
    ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
      edgeCoeff π lab (fibreCoef γ) i • curveClassOn G (lab i)
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [hcc i hi], hρ, ← map_neg]
  rw [show (∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
      edgeCoeff π lab (fibreCoef γ) i • pointsClass _ 1 (cyc i)) =
      pointsClass _ 1 (∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
        edgeCoeff π lab (fibreCoef γ) i • cyc i) by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (map_smul _ _ _).symm]
  congr 1
  ext V
  by_cases hV : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (G.1.toScheme ↘ Spec (.of ℂ)) V = (1 : ℕ)
  · obtain ⟨hCirr, hCcl, hCdim, hCy, hCE⟩ := j.curve_props ⟨V, hV⟩
    have key := sum_edgeCoeff_eq hy hσT hEE hI hlab (fibreCoef γ) E hCirr hCcl hCdim hCy hCE
      (fun E' h ↦ subset_of_fibreCoef_ne_zero γ E' _ h) (sum_fibreCoef_eq_zero hy γ hγ2 j V)
    rw [fibreCoef_self hdisj γ j V] at key
    simp only [Finsupp.neg_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
      hcyc _ V hV, mul_ite, mul_one, mul_zero]
    rw [← key, ← Finset.sum_filter, Finset.filter_filter]
  · have hγV : γ j V = 0 := by
      by_contra hne
      exact hV (hγs j (Finsupp.mem_support_iff.2 hne))
    simp only [Finsupp.neg_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
      hcyc0 _ V hV, mul_zero, Finset.sum_const_zero, hγV, neg_zero]

/-- A curve-and-point exceptional model `r : Z ⟶ Y` makes `Z` proper over `ℂ`. -/
private theorem isProper_comp_of_isCurvePointExceptionalModel
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) : IsProper (r ≫ sY) := by
  haveI := (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
  haveI := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  infer_instance

open Classical in
/-- **Spreading edge coefficients.** At a general closed point `y` of `T`, a system `a` on the
double surfaces dominating `T` cuts on each fibre component `G ⊆ E` the curve class
`∑ a_S [C]` over the double curves `C ⊆ G` of the surfaces `S ⊆ E ∩ E'`. -/
private theorem restrictionClass_surfaceCoefficientDivisor_eq
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U₀ : Set Y) ∩ T, IsClosed {y} →
      ∀ (I : Type) [Fintype I] (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s →
      ∀ lab : I → Set Z, IsEdgeLabeling r π s y lab →
      ∀ a : DoubleSurface F → ℚ, (∀ σ, a σ ≠ 0 → r.base '' σ.carrier = (T : Set Y)) →
      ∀ (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
        Maximal (fun A ↦ IsIrreducible A ∧
          A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
        restrictionClass G (surfaceCoefficientDivisor a E.1) =
          ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1), a (π i) • curveClassOn G (lab i) := by
  obtain ⟨U, hU, hdisj⟩ := exists_disjoint_maximal_fibre hM T hT1
  haveI := isProper_comp_of_isCurvePointExceptionalModel hM
  refine ⟨U, hU, fun y hy _ I _ π s hI lab hlab a _ E G hG ↦ ?_⟩
  exact restrictionClass_surfaceCoefficientDivisor_eq_of_disjoint hM.isSNC y hI hlab a E G hG
    fun A hA hne ↦ hdisj y hy E A _ hA hG hne

/-- Relabelling by a permutation `g` over the double surfaces moves the coefficients by `g⁻¹`. -/
private theorem sum_filter_comp_perm {F : Type*} {Z : Scheme.{0}} {B : Divisor Z} {I : Type}
    [Fintype I] [AddCommGroup F] [Module ℚ F] (π : I → DoubleSurface B)
    (E : MMP.Mori.PrimeDivisor Z) (g : Equiv.Perm I) (hg : ∀ i, π (g i) = π i) (b : I → ℚ)
    (f : I → F) [DecidablePred fun i ↦ (π i).fst = E] :
    ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E), b i • f (g i) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E), b (g⁻¹ i) • f i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Fintype.sum_equiv g _ _ fun i ↦ by simp [hg i]

/-- **One general fibre.** At a closed point `y` over which the fibre components of each `Fᵢ`
are disjoint surfaces, the double surfaces meeting `r⁻¹(y)` dominate `T`, and no surface lies in
two components of `F`, the vanishing of `w_T(y)` gives, for every edge labelling, oriented
coefficients solving the edge equation: normalization excision for `⨆ G ⟶ r⁻¹(y)`. -/
private theorem exists_edgeRelation_of_fibre
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) {y : Y} (hy : IsClosed {y})
    (hyS : y ∈ (singularLocus sY : Set Y))
    (hdisj : ∀ (E : F.support) (A B : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
      A ≠ B → Disjoint A B)
    (hdim2 : ∀ (E : F.support) (A : Set E.1.idealSheaf.subscheme),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (hσT : ∀ σ : DoubleSurface F, y ∈ r.base '' σ.carrier → r.base '' σ.carrier = T)
    (hEE : ∀ E E' : F.support, E ≠ E' → ∀ X : Set Z, IsIrreducible X → IsClosed X →
      X ⊆ (E.1.support : Set Z) ∩ E'.1.support ∩ r.base ⁻¹' {y} →
      topologicalKrullDim X ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hw : (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
                ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                ((Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
                (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0)
    (I : Type) [Fintype I] (π : I → DoubleSurface F) (s : I → I) (hI : IsEdgeIndex r T π s)
    (lab : I → Set Z) (hlab : IsEdgeLabeling r π s y lab) :
    ∃ b : I → ℚ, (∀ i, b (s i) = -b i) ∧ EdgeRelation r L π y lab b := by
  haveI := finite_fibreComponent r F y
  haveI : ∀ E : F.support, Finite {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
        (G.1.support : Set E.1.idealSheaf.subscheme)} := fun E ↦
    Finite.of_injective (fun G ↦ (⟨E, G⟩ : FibreComponent r F y)) fun _ _ h ↦
      eq_of_heq (Sigma.mk.inj h).2
  letI : ∀ E : F.support, Fintype {G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2} //
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
        (G.1.support : Set E.1.idealSheaf.subscheme)} := fun E ↦ Fintype.ofFinite _
  obtain ⟨hcov, hAdim, hGdim⟩ := fibreComponent_excision_hyps hM hy hyS hdim2 hEE
  have hρ := (sum_pushforward_restrictionClass_eq hy hdisj hdim2 L).trans hw
  obtain ⟨γ, hγs, hγ1, hγ2⟩ := exists_cycles_of_sum_pushforward_eq_zero
    (fun j : FibreComponent r F y ↦ j.2.1.1.toScheme) (fun j ↦ j.toFibre hy) hcov
    (fibreDoubleLocus r F hy) rfl hAdim hGdim (fun j ↦ restrictionClass j.2.1 (L j.1)) hρ
  exact exists_edgeRelation_of_cycles hy hdisj hσT hEE L γ hγs hγ1 hγ2 hI hlab

/-- **Fibrewise normalization excision.** At a general closed point `y` of `T` with `w_T(y) = 0`,
for every edge labelling, there are oriented coefficients on the labels solving the edge
equation: the kernel of `⨁_G H_2(G) → H_2(F_y)` is spanned by the oriented double curves. -/
private theorem exists_edgeRelation_of_fibreClass_eq_zero
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, ∀ hy : IsClosed {y},
      (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
                ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                ((Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
                (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0 →
      ∀ (I : Type) [Fintype I] (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s →
      ∀ lab : I → Set Z, IsEdgeLabeling r π s y lab →
      ∃ b : I → ℚ, (∀ i, b (s i) = -b i) ∧ EdgeRelation r L π y lab b := by
  obtain ⟨U₁, hU₁, h₁⟩ := exists_forall_of_finite T _
    (exists_disjoint_maximal_fibre_of_mem hM T hT1)
  obtain ⟨U₂, hU₂, h₂⟩ := exists_open_doubleSurface_image_eq hM T hT1
  obtain ⟨U₃, hU₃, h₃⟩ := exists_open_topologicalKrullDim_inter_fibre_le hM T hT1
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, inter_inter_nonempty_of_irreducibleCloseds T
    (inter_inter_nonempty_of_irreducibleCloseds T hU₁ hU₂) hU₃, ?_⟩
  intro y hy hyc hw I _ π s hI lab hlab
  have hy₁ : y ∈ (U₁ : Set Y) ∩ T := ⟨hy.1.1.1, hy.2⟩
  have hy₂ : y ∈ (U₂ : Set Y) ∩ T := ⟨hy.1.1.2, hy.2⟩
  have hy₃ : y ∈ (U₃ : Set Y) ∩ T := ⟨hy.1.2, hy.2⟩
  exact exists_edgeRelation_of_fibre hM L T hyc (hTs hy.2) (fun E ↦ (h₁ y hy₁ E).1)
    (fun E ↦ (h₁ y hy₁ E).2) (h₂ y hy₂) (h₃ y hy₃) hw I π s hI lab hlab

/-! ### The covering of edge labellings

Over a general open `U₀` of `T`, the product germs `F_b × Δ ≃ₜ F_Δ` of the exceptional family
carry the double curves of `F_b` onto those of `F_t`, so every labelling at `b` spreads to a
*sheet* of labellings over `Δ`: these sheets are connected, open in the labellings over `U ∩ T`,
and the edge equation is constant along them. -/

section EdgeCovering

open MMP.UnderlyingSpace Topology
open ConductorBlowup (isClosed_carrier)

/-- A predicate locally constant on a preconnected set holds everywhere on it once it holds at one
point. -/
private theorem forall_of_isPreconnected_of_locally_iff {α : Type*} [TopologicalSpace α]
    {X : Set α} (hX : IsPreconnected X) (P : α → Prop)
    (hloc : ∀ a ∈ X, ∃ O, IsOpen O ∧ a ∈ O ∧ ∀ a' ∈ O ∩ X, (P a ↔ P a'))
    {a₀ : α} (ha₀ : a₀ ∈ X) (hP : P a₀) : ∀ a ∈ X, P a := by
  choose! O hO haO hOP using hloc
  set u := ⋃ a ∈ {a | a ∈ X ∧ P a}, O a
  set v := ⋃ a ∈ {a | a ∈ X ∧ ¬ P a}, O a
  have hu : IsOpen u := isOpen_biUnion fun a ha ↦ hO a ha.1
  have hv : IsOpen v := isOpen_biUnion fun a ha ↦ hO a ha.1
  have hcov : X ⊆ u ∪ v := fun a ha ↦ by
    by_cases h : P a
    · exact Or.inl (Set.mem_biUnion ⟨ha, h⟩ (haO a ha))
    · exact Or.inr (Set.mem_biUnion ⟨ha, h⟩ (haO a ha))
  have hdisj : X ∩ (u ∩ v) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ⟨ha, hau, hav⟩ ↦ ?_
    obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 hau
    obtain ⟨c, hc, hac⟩ := Set.mem_iUnion₂.1 hav
    exact hc.2 ((hOP c hc.1 a ⟨hac, ha⟩).2 ((hOP b hb.1 a ⟨hab, ha⟩).1 hb.2))
  intro a ha
  rcases isPreconnected_iff_subset_of_disjoint.1 hX u v hu hv hcov hdisj with h | h
  · obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (h ha)
    exact (hOP b hb.1 a ⟨hab, ha⟩).1 hb.2
  · obtain ⟨c, hc, hac⟩ := Set.mem_iUnion₂.1 (h ha₀)
    exact absurd ((hOP c hc.1 a₀ ⟨hac, ha₀⟩).2 hP) hc.2

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {r : Z ⟶ Y} [r.IsOver (Spec (.of ℂ))] {F D : Divisor Z}

/-- The `ℂ`-point of a closed point of a scheme locally of finite type over `ℂ`. -/
private theorem exists_toHom_eq {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {x : X} (hx : IsClosed {x}) :
    ∃ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) = x :=
  ⟨(equivClosedPoints (K := ℂ) X).symm ⟨x, hx⟩, by
    rw [← equivClosedPoints_apply, Equiv.apply_symm_apply]⟩

/-- A scheme point which is the point of a `ℂ`-point is closed. -/
private theorem isClosed_singleton_toHom {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (p : UnderlyingSpace ℂ X) :
    IsClosed {p.toHom (IsLocalRing.closedPoint ℂ)} := by
  have := ((equivClosedPoints (K := ℂ) X) p).2
  rwa [equivClosedPoints_apply] at this

/-- A nonempty closed subset of a quasi-compact scheme locally of finite type over `ℂ` has a
complex point. -/
private theorem nonempty_pointsOver_of_isClosed {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [CompactSpace X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {S : Set X} (hS : IsClosed S)
    (hne : S.Nonempty) : (pointsOver (K := ℂ) S).Nonempty := by
  obtain ⟨x, hx, hxc⟩ := hS.exists_closed_singleton hne
  obtain ⟨p, hp⟩ := exists_toHom_eq hxc
  exact ⟨p, by rw [mem_pointsOver, hp]; exact hx⟩

/-- **Disjoint double curves of one double surface.** -/
private theorem exists_disjoint_maximal_doubleCurve_of_mem
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1)
    (σ : DoubleSurface F) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      (∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) B → A ≠ B →
        Disjoint A B) ∧
      ∀ A : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) A →
        topologicalKrullDim A = ((1 : ℕ) : WithBot ℕ∞) := by
  classical
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hres.1
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI : MMP.Mori.IsVariety ℂ (r ≫ Y ↘ Spec (.of ℂ)) := hres.2.1
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (Y ↘ Spec (.of ℂ))
      (r ≫ Y ↘ Spec (.of ℂ)) hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have := noetherianSpace_of_isComplexScheme (X := Z)
  obtain ⟨U₄, hU₄, h₄⟩ := exists_open_doubleSurface_image_eq hM T hT1
  by_cases hσT : r.base '' σ.carrier = (T : Set Y)
  swap
  · -- `σ` misses the general fibres
    have hempty : ∀ y ∈ (U₄ : Set Y) ∩ T, ∀ A : Set Z,
        ¬ Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) A := by
      intro y hy A hA
      obtain ⟨x, hx⟩ := hA.1.1.nonempty
      exact hσT (h₄ y hy σ ⟨x, (hA.1.2 hx).1, (hA.1.2 hx).2⟩)
    exact ⟨U₄, hU₄, fun y hy ↦ ⟨fun A _ hA _ _ ↦ (hempty y hy A hA).elim,
      fun A hA ↦ (hempty y hy A hA).elim⟩⟩
  -- the smooth scheme `S = E₁ ∩ E₂`
  set E₁ := σ.fst
  set E₂ := σ.snd
  set K : Z.IdealSheafData := E₁.idealSheaf ⊔ E₂.idealSheaf with hKdef
  have hKsupp : (K.support : Set Z) = (E₁.support : Set Z) ∩ E₂.support := by
    rw [hKdef, Scheme.IdealSheafData.support_sup]; rfl
  have hsmK : MMP.Mori.IsSmoothScheme (K.subschemeι ≫ Z ↘ Spec (.of ℂ)) := by
    have hX : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hres.2.2.1
    refine MMP.Resolution.isSmoothScheme_subscheme_of_hasSNCWith (k := ℂ) _ hX
      (E := (Empty.elim : Empty → Z.IdealSheafData)) ⟨fun i ↦ i.elim, fun x ↦ ?_⟩ ?_
    · obtain ⟨n, z, j, hz, -, -⟩ := hM.isSNC.2 x
      exact ⟨n, z, fun i ↦ i.1.elim, hz, fun i ↦ i.1.elim, fun a ↦ a.1.elim⟩
    · intro x hx
      have hx' : x ∈ (E₁.support : Set Z) ∩ E₂.support := hKsupp ▸ hx
      obtain ⟨n, z, j, hz, -, hI⟩ := hM.isSNC.2 x
      refine ⟨n, z, fun i ↦ i.1.elim, {j ⟨E₁, σ.fst_mem, hx'.1⟩, j ⟨E₂, σ.snd_mem, hx'.2⟩},
        hz, fun i ↦ i.1.elim, fun a ↦ a.1.elim, ?_⟩
      have hsup : K = ⨆ b : Bool, cond b E₁.idealSheaf E₂.idealSheaf := by
        rw [iSup_bool_eq]; rfl
      rw [hsup, MMP.Resolution.stalk_iSup, iSup_bool_eq]
      simp only [cond_true, cond_false]
      rw [hI ⟨E₁, σ.fst_mem, hx'.1⟩, hI ⟨E₂, σ.snd_mem, hx'.2⟩, Finset.coe_insert,
        Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton, Ideal.span_insert]
  set ι := K.subschemeι with hι
  have hrangeι : Set.range ι.base = (E₁.support : Set Z) ∩ E₂.support := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι, hKsupp]
  have hsupp : ∀ E : MMP.Mori.PrimeDivisor Z, IsClosed (E.support : Set Z) := fun E ↦ by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hE₁₂ : IsClosed ((E₁.support : Set Z) ∩ E₂.support) := (hsupp _).inter (hsupp _)
  -- the open subscheme over `σ`
  obtain ⟨x₀, hx₀, hσx₀⟩ := σ.isComponent
  have hσopen : IsOpen (ι.base ⁻¹' (((E₁.support : Set Z) ∩ E₂.support) \ σ.carrier)ᶜ) := by
    refine (isOpen_compl_iff.2 ?_).preimage ι.base.hom.continuous
    rw [← hσx₀]; exact isClosed_diff_connectedComponentIn'' hE₁₂ x₀
  set V : K.subscheme.Opens := ⟨_, hσopen⟩ with hV
  set φ : V.toScheme ⟶ Z := V.ι ≫ ι with hφ
  have hrangeφ : Set.range φ.base = σ.carrier := by
    rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : ι.base u ∈ (E₁.support : Set Z) ∩ E₂.support := hrangeι ▸ ⟨u, rfl⟩
      by_contra h
      exact hu ⟨hu', h⟩
    · intro hw
      obtain ⟨u, rfl⟩ : w ∈ Set.range ι.base := hrangeι ▸ σ.carrier_subset hw
      exact ⟨u, fun h ↦ h.2 hw, rfl⟩
  have hφemb : Topology.IsEmbedding φ.base :=
    (ι.isClosedEmbedding.isEmbedding).comp V.ι.isOpenEmbedding.isEmbedding
  haveI : IsProper (Y ↘ Spec (.of ℂ)) :=
    (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
  haveI : IsProper (Z ↘ Spec (.of ℂ)) := by rw [← hM.comp_eq]; infer_instance
  have hσirr : IsIrreducible σ.carrier :=
    MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity.isIrreducible_carrier
      (sZ := Z ↘ Spec (.of ℂ)) (hM.comp_eq ▸ hM.isSNC) σ
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨φ ≫ Z ↘ Spec (.of ℂ)⟩
  haveI : Smooth (ι ≫ Z ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsmK
  haveI : Smooth (V.toScheme ↘ Spec (.of ℂ)) := by
    change Smooth ((V.ι ≫ ι) ≫ Z ↘ Spec (.of ℂ)); rw [Category.assoc]; infer_instance
  haveI : IsReduced K.subscheme := AlgebraicGeometry.isReduced_of_smooth (ι ≫ Z ↘ Spec (.of ℂ))
  haveI : IrreducibleSpace V.toScheme := by
    rw [irreducibleSpace_def]
    have h := isIrreducible_preimage_of_isEmbedding hφemb hσirr hrangeφ.symm.subset
    rwa [← hrangeφ, Set.preimage_range] at h
  haveI : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : CompactSpace K.subscheme := ι.isClosedEmbedding.compactSpace
  haveI : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType ((V.ι ≫ ι) ≫ Z ↘ Spec (.of ℂ)); infer_instance
  haveI : QuasiCompact (V.toScheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact ((V.ι ≫ ι) ≫ Z ↘ Spec (.of ℂ)); infer_instance
  -- `σ ⟶ T` and generic smoothness
  let Tc : Closeds Y := ⟨(T : Set Y), T.isClosed⟩
  set j := curveι T with hj
  have hrangej : Set.range j.base = (T : Set Y) := by
    rw [hj, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrangef : Set.range (φ ≫ r).base = (T : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrangeφ, hσT]
  have hker : j.ker ≤ (φ ≫ r).ker := by
    rw [hj, Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    rw [TopologicalSpace.Closeds.coe_closure, hrangef, T.isClosed.closure_eq]
    rfl
  let p := IsClosedImmersion.lift j (φ ≫ r) hker
  have hp : p ≫ j = φ ≫ r := IsClosedImmersion.lift_fac _ _ _
  letI : (curveScheme T).Over (Spec (.of ℂ)) := ⟨j ≫ Y ↘ Spec (.of ℂ)⟩
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal Tc T.isIrreducible
  haveI : p.IsOver (Spec (.of ℂ)) := ⟨by
    change p ≫ j ≫ Y ↘ Spec (.of ℂ) = φ ≫ Z ↘ Spec (.of ℂ)
    rw [← Category.assoc, hp, Category.assoc, hM.comp_eq]⟩
  haveI : LocallyOfFiniteType ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  haveI : QuasiCompact ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change QuasiCompact (j ≫ Y ↘ Spec (.of ℂ)); infer_instance
  obtain ⟨U', hU'd, -, -, hfib⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) p
  have hpsurj : Function.Surjective p.base := by
    intro t
    have htK : j.base t ∈ Set.range (φ ≫ r).base := by rw [hrangef, ← hrangej]; exact ⟨t, rfl⟩
    obtain ⟨x, hx⟩ := htK
    refine ⟨x, j.isClosedEmbedding.injective ?_⟩
    change (p ≫ j).base x = j.base t
    rw [hp]
    exact hx
  haveI : IsDominant p := ⟨hpsurj.denseRange⟩
  -- dimensions
  have hdσ : topologicalKrullDim σ.carrier = ((2 : ℕ) : WithBot ℕ∞) := by
    have hE3 : ∀ i : F.support, topologicalKrullDim i.1.idealSheaf.subscheme = (3 : ℕ) := by
      intro i
      rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
      exact ConductorBlowup.topologicalKrullDim_support_eq_three hdimZ i.1
    have h := MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity.dim_surfI_eq
      (sZ := Z ↘ Spec (.of ℂ)) (hM.comp_eq ▸ hM.isSNC) hE3 σ
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq] at h
    rw [MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity.surfI,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure,
      (isClosed_carrier σ).closure_eq] at h
    exact h
  have hdV : topologicalKrullDim V.toScheme = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [← hdσ]
    exact (hφemb.toHomeomorph.trans (Homeomorph.setCongr hrangeφ)).isHomeomorph
      |>.topologicalKrullDim_eq
  have hdT : topologicalKrullDim (curveScheme T) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [MMP.Mori.topologicalKrullDim_subscheme_eq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hT1
  obtain ⟨W, hW, hWU⟩ := j.isClosedEmbedding.isInducing.isOpen_iff.1 U'.2
  refine ⟨⟨W, hW⟩, ?_, fun y hy ↦ ?_⟩
  · obtain ⟨t, ht⟩ := hU'd.nonempty
    refine ⟨j.base t, ?_, hrangej ▸ ⟨t, rfl⟩⟩
    change j.base t ∈ W
    rw [← Set.mem_preimage, hWU]
    exact ht
  obtain ⟨t, rfl⟩ : y ∈ Set.range j.base := hrangej ▸ hy.2
  have ht : t ∈ U' := by
    have h1 : t ∈ j.base ⁻¹' W := hy.1
    rw [hWU] at h1
    exact h1
  have hsm := (hfib inferInstance t ht).1
  -- the fibre `p⁻¹(t)` embeds onto `σ ∩ r⁻¹(y)`
  set ψ : p.fiber t → Z := fun w ↦ φ.base ((p.fiberι t).base w) with hψ
  have hψemb : Topology.IsEmbedding ψ := hφemb.comp (p.fiberι t).isEmbedding
  have hψr : Set.range ψ = σ.carrier ∩ r.base ⁻¹' {j.base t} := by
    rw [hψ, Set.range_comp' φ.base (p.fiberι t).base, p.range_fiberι t]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨hrangeφ ▸ ⟨u, rfl⟩, ?_⟩
      change (φ ≫ r).base u = j.base t
      rw [← hp]; change j.base (p.base u) = j.base t; rw [show p.base u = t from hu]
    · rintro ⟨hwσ, hwy⟩
      obtain ⟨u, rfl⟩ : w ∈ Set.range φ.base := hrangeφ ▸ hwσ
      refine ⟨u, j.isClosedEmbedding.injective ?_, rfl⟩
      change (p ≫ j).base u = j.base t
      rw [hp]; exact hwy
  have hcomp : ∀ C, Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ σ.carrier ∩ r.base ⁻¹' {j.base t}) C →
      ψ ⁻¹' C ∈ irreducibleComponents (p.fiber t) := by
    intro C hC
    have hmax := (maximal_preimage_iff hψemb (S := σ.carrier ∩ r.base ⁻¹' {j.base t})
      (fun C' hC' ↦ Or.inl (hψr ▸ hC'.1.2)) (ψ ⁻¹' C)).2 ⟨C, hC, hψr ▸ hC.1.2, rfl⟩
    rw [← hψr, Set.preimage_range] at hmax
    exact ⟨hmax.1.1, fun X hX hle ↦ hmax.2 ⟨hX, Set.subset_univ _⟩ hle⟩
  refine ⟨fun A B hA hB hAB ↦ ?_, fun A hA ↦ ?_⟩
  · have hAr : A ⊆ Set.range ψ := hψr ▸ hA.1.2
    have hBr : B ⊆ Set.range ψ := hψr ▸ hB.1.2
    have hne : ψ ⁻¹' A ≠ ψ ⁻¹' B := fun h ↦ hAB (by
      rw [← Set.image_preimage_eq_of_subset hAr, h, Set.image_preimage_eq_of_subset hBr])
    have hd := @MMP.Flips.ResolutionInputs.disjoint_of_mem_irreducibleComponents_of_smooth _ _ _
      (p.fiberToSpecResidueField t) hsm _ _ (hcomp A hA) (hcomp B hB) hne
    rw [Set.disjoint_left]
    intro a haA haB
    obtain ⟨a', rfl⟩ := hAr haA
    exact Set.disjoint_left.1 hd haA haB
  · have hAr : A ⊆ Set.range ψ := hψr ▸ hA.1.2
    have hd := (hfib inferInstance t ht).2 _ (hcomp A hA)
    have hdA : topologicalKrullDim (ψ ⁻¹' A) = topologicalKrullDim A := by
      have hemb : Topology.IsEmbedding (fun s : (ψ ⁻¹' A : Set (p.fiber t)) ↦ ψ s.1) :=
        hψemb.comp Topology.IsEmbedding.subtypeVal
      have hrange : Set.range (fun s : (ψ ⁻¹' A : Set (p.fiber t)) ↦ ψ s.1) = A := by
        rw [Set.range_comp' ψ Subtype.val, Subtype.range_coe, Set.image_preimage_eq_of_subset hAr]
      exact (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)).isHomeomorph
        |>.topologicalKrullDim_eq
    rw [hdA, hdV, hdT] at hd
    revert hd
    generalize topologicalKrullDim A = e
    intro hd
    induction e using WithBot.recBotCoe with
    | bot => simp at hd
    | coe e =>
      have h' : e + 1 = 2 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact hd)
      induction e using ENat.recTopCoe with
      | top => simp at h'
      | coe e =>
        have : e + 1 = 2 := by exact_mod_cast h'
        rw [(by omega : e = 1)]
        rfl

/-- A complex point of `Z` whose scheme point lies over that of `y` lies over `y`. -/
private theorem mapFun_eq_of_base_eq [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    {p : UnderlyingSpace ℂ Z} {y : UnderlyingSpace ℂ Y}
    (h : r.base (p.toHom (IsLocalRing.closedPoint ℂ)) = y.toHom (IsLocalRing.closedPoint ℂ)) :
    mapFun r p = y := by
  apply (equivClosedPoints (K := ℂ) Y).injective
  apply Subtype.ext
  rw [equivClosedPoints_apply, equivClosedPoints_apply, toHom_mapFun]
  exact h

/-- Two closed subsets of a scheme locally of finite type over `ℂ` with the same complex points
are equal. -/
private theorem eq_of_pointsOver_eq {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h : pointsOver (K := ℂ) A = pointsOver (K := ℂ) B) : A = B := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  have key : ∀ {A B : Set X}, IsClosed A → IsClosed B →
      pointsOver (K := ℂ) A ⊆ pointsOver (K := ℂ) B → A ⊆ B := by
    intro A B hA hB h
    rw [← closure_inter_closedPoints hA]
    refine closure_minimal (fun a ⟨ha, hac⟩ ↦ ?_) hB
    obtain ⟨p, rfl⟩ := exists_toHom_eq (X := X) hac
    exact h ha
  exact (key hA hB h.subset).antisymm (key hB hA h.symm.subset)

/-- The complex points of a double curve over `y` lie in the fibre `F_y`. -/
private theorem pointsOver_subset_fibre_of_maximal [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (σ : DoubleSurface F) {y : UnderlyingSpace ℂ Y} {C : Set Z}
    (hC : Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ σ.carrier ∩ r.base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}) C) :
    pointsOver (K := ℂ) C ⊆ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y} := by
  intro p hp
  have h := hC.1.2 hp
  refine ⟨?_, mapFun_eq_of_base_eq h.2⟩
  change p.toHom (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z)
  rw [DivisorWithCoeffs.coe_supp]
  exact Set.mem_iUnion₂.2 ⟨σ.fst, σ.fst_mem, (σ.carrier_subset h.1).1⟩

/-- Over a point `y` whose double curves on `σ` are disjoint, the complex points of each of them
form a connected component of `σ(ℂ) ∩ F_y`. -/
private theorem connectedComponentIn_doubleCurve_eq [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] [NoetherianSpace Z]
    (σ : DoubleSurface F) {y : UnderlyingSpace ℂ Y}
    (hdisj : ∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B →
      Disjoint A B)
    {C : Set Z} (hC : Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ σ.carrier ∩ r.base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)}) C)
    (z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}))
    (hz : (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C) :
    connectedComponentIn {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier} z =
      {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C} := by
  classical
  set Fib : Set Z := σ.carrier ∩ r.base ⁻¹' {y.toHom (IsLocalRing.closedPoint ℂ)} with hFib
  set M : Set (Set Z) := {A | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Fib) A} with hM
  set Fy := pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {y} with hFy
  let Q : Set Z → Set Fy := fun A ↦ {w | (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) A}
  have hFibcl : IsClosed Fib :=
    (isClosed_carrier σ).inter ((isClosed_singleton_toHom y).preimage r.continuous)
  have hMcl : ∀ B ∈ M, IsClosed B := fun B hB ↦ isClosed_of_maximal hFibcl hB
  refine connectedComponentIn_eq_of_pairwiseDisjoint (Ps := Q '' M)
    ((finite_setOf_maximal Fib).image Q) ?_ ?_ ?_ ?_ ⟨C, hC, rfl⟩ hz
  · rintro _ ⟨B, hB, rfl⟩
    exact (isClosed_pointsOver (hMcl B hB)).preimage continuous_subtype_val
  · rintro _ ⟨B, hB, rfl⟩
    have hsub : pointsOver (K := ℂ) B ⊆ Fy := pointsOver_subset_fibre_of_maximal σ hB
    have hconn := isConnected_pointsOver_of_isIrreducible (Z := Z) (hMcl B hB) hB.1.1
    have himg : (Subtype.val : Fy → UnderlyingSpace ℂ Z) '' Q B = pointsOver (K := ℂ) B := by
      change Subtype.val '' (Subtype.val ⁻¹' _) = _
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
    exact hconn.isPreconnected
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩ hne
    have hBB' : B ≠ B' := fun h ↦ hne (by rw [h])
    exact Set.disjoint_left.2 fun w hw hw' ↦ Set.disjoint_left.1 (hdisj B B' hB hB' hBB') hw hw'
  · ext w
    simp only [Set.sUnion_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨B, hB, hwB⟩
      exact (hB.1.2 hwB).1
    · intro hw
      have hwFib : (w : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ) ∈ Fib := by
        refine ⟨hw, ?_⟩
        have h2 : mapFun r (w : UnderlyingSpace ℂ Z) = y := w.2.2
        change r.base _ = _
        rw [← h2, toHom_mapFun]
        rfl
      obtain ⟨B, hxB, hB⟩ := exists_subset_maximal_of_isIrreducible (S := Fib)
        isIrreducible_singleton (Set.singleton_subset_iff.2 hwFib)
      exact ⟨B, hB, hxB rfl⟩

/-- **Double curves are carried to double curves.** A homeomorphism `F_b ≃ₜ F_t` preserving a
double surface `S` carries the complex points of every component of `S ∩ r⁻¹(b)` onto those of a
component of `S ∩ r⁻¹(t)`, when the components over `b` and over `t` are disjoint. -/
private theorem exists_maximal_doubleCurve_transport [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] [NoetherianSpace Z]
    (σ : DoubleSurface F) {b t : UnderlyingSpace ℂ Y}
    (hb : ∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B →
      Disjoint A B)
    (ht : ∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B →
      Disjoint A B)
    (h : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {t}))
    (hh : ∀ z, (h z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier ↔
      (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier)
    {C : Set Z} (hC : Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C) :
    ∃ C', Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) C' ∧
      ∀ z : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}),
        (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
          (h z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C' := by
  have hCcl : IsClosed C := isClosed_of_maximal
    ((isClosed_carrier σ).inter ((isClosed_singleton_toHom b).preimage r.continuous)) hC
  obtain ⟨p, hpC⟩ := nonempty_pointsOver_of_isClosed (X := Z) hCcl hC.1.1.nonempty
  let z₀ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) :=
    ⟨p, pointsOver_subset_fibre_of_maximal σ hC hpC⟩
  have hz₀σ : (z₀ : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier := (hC.1.2 hpC).1
  have hhz₀ : (h z₀ : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier := (hh z₀).2 hz₀σ
  have hFib : (h z₀ : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ) ∈
      σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)} := by
    refine ⟨hhz₀, ?_⟩
    have h2 : mapFun r (h z₀ : UnderlyingSpace ℂ Z) = t := (h z₀).2.2
    have key : ∀ x : UnderlyingSpace ℂ Z, r.base (x.toHom (IsLocalRing.closedPoint ℂ)) =
        (mapFun r x).toHom (IsLocalRing.closedPoint ℂ) := fun x ↦ by rw [toHom_mapFun]; rfl
    change r.base _ = _
    rw [key, h2]
  obtain ⟨B, hxB, hB⟩ := exists_subset_maximal_of_isIrreducible
    (S := σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)})
    isIrreducible_singleton (Set.singleton_subset_iff.2 hFib)
  have hhz₀B : (h z₀ : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) B := hxB rfl
  have hccb := connectedComponentIn_doubleCurve_eq σ hb hC z₀ hpC
  have hcct := connectedComponentIn_doubleCurve_eq σ ht hB (h z₀) hhz₀B
  have hS : h '' {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier} =
      {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {t}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩; exact (hh z).2 hz
    · intro hw
      refine ⟨h.symm w, ?_, h.apply_symm_apply w⟩
      have := (hh (h.symm w)).1
      rw [h.apply_symm_apply] at this
      exact this hw
  have himg := h.image_connectedComponentIn
    (s := {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) |
      (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) σ.carrier}) (x := z₀) hz₀σ
  rw [hS, hccb, hcct] at himg
  refine ⟨B, hB, fun z ↦ ?_⟩
  have : z ∈ {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) |
      (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C} ↔
      h z ∈ {w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {t}) |
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) B} := by
    rw [← himg]; exact h.injective.mem_set_image.symm
  exact this

/-- **Disjoint double curves.** Over a general open of `T`, the irreducible components of
`S ∩ r⁻¹(y)` are, for every double surface `S`, pairwise disjoint curves: `S` is a smooth surface
(a stratum of the snc divisor `F`), smooth over a dense open of `T` when it dominates `T`
(generic smoothness), and it misses the general fibres otherwise. -/
private theorem exists_disjoint_maximal_doubleCurve
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, ∀ σ : DoubleSurface F,
      (∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) B → A ≠ B →
        Disjoint A B) ∧
      ∀ A : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) A →
        topologicalKrullDim A = ((1 : ℕ) : WithBot ℕ∞) := by
  have := noetherianSpace_of_isComplexScheme (X := Z)
  have := finite_doubleSurface F
  letI : Fintype (DoubleSurface F) := Fintype.ofFinite _
  exact exists_forall_of_finite T _ (exists_disjoint_maximal_doubleCurve_of_mem hM T hT1)

/-- The complex points of `U ∩ T` form a connected set for every open `U` meeting the curve `T`:
they are the image of the complex points of an irreducible closed subset of `Z` over `T`. -/
private theorem isConnected_pointsOver_inter
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D) (T : IrreducibleCloseds Y)
    (U : Y.Opens) (hU : ((U : Set Y) ∩ T).Nonempty) :
    IsConnected (pointsOver (K := ℂ) ((U : Set Y) ∩ T)) := by
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ (r ≫ Y ↘ Spec (.of ℂ)) := hM.isResolution.2.1
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hM.isResolution.2.2.2.2
  have hsurj : Function.Surjective r.base := by
    have h := r.denseRange.closure_range
    rw [r.isClosedMap.isClosed_range.closure_eq] at h
    exact Set.range_eq_univ.1 h
  obtain ⟨η, hη⟩ := QuasiSober.sober T.isIrreducible T.isClosed
  obtain ⟨z, hz⟩ := hsurj η
  set S : Set Z := closure {z} with hSdef
  have hcl : IsClosed S := isClosed_closure
  have hirr : IsIrreducible S := isIrreducible_singleton.closure
  have hST : r.base '' S = (T : Set Y) := by
    apply Set.Subset.antisymm
    · refine (image_closure_subset_closure_image r.continuous).trans ?_
      rw [Set.image_singleton, hz, hη.def]
    · rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.2 ⟨z, subset_closure rfl, hz⟩)
        (r.isClosedMap _ hcl)
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨S, hcl⟩ with hI
  haveI : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hirr
  have hrange : Set.range I.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  set Zc : Set I.subscheme := I.subschemeι.base ⁻¹' (r.base ⁻¹' (U : Set Y))ᶜ with hZc
  have hZcl : IsClosed Zc :=
    ((U.isOpen.preimage r.continuous).isClosed_compl).preimage I.subschemeι.continuous
  have hZne : Zc ≠ Set.univ := by
    obtain ⟨y, hyU, hyT⟩ := hU
    rw [← hST] at hyT
    obtain ⟨z', hz'S, rfl⟩ := hyT
    rw [← hrange] at hz'S
    obtain ⟨w, rfl⟩ := hz'S
    intro h
    have hw : w ∈ Zc := h ▸ Set.mem_univ w
    exact hw hyU
  have hconn := MMP.UnderlyingSpace.isConnected_regularPart_diff
    (X := I.subscheme) hZcl hZne
  have hdense := MMP.UnderlyingSpace.dense_regularPart_diff
    (X := I.subscheme) hZcl hZne
  set A : Set (UnderlyingSpace ℂ I.subscheme) :=
    {p | p.toHom (IsLocalRing.closedPoint ℂ) ∉ Zc} with hA
  have hAconn : IsConnected A :=
    hconn.subset_closure (fun p hp ↦ hp.2) (by rw [hdense.closure_eq]; exact Set.subset_univ _)
  have himage : mapFun (K := ℂ) r '' (map (K := ℂ) I.subschemeι '' A) =
      pointsOver (K := ℂ) ((U : Set Y) ∩ T) := by
    ext q
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have hpS : I.subschemeι.base (p.toHom (IsLocalRing.closedPoint ℂ)) ∈ S := by
        have h := Set.mem_range_self (f := I.subschemeι.base) (p.toHom (IsLocalRing.closedPoint ℂ))
        rwa [hrange] at h
      rw [mem_pointsOver, toHom_mapFun]
      refine ⟨?_, ?_⟩
      · by_contra h; exact hp h
      · rw [← hST]; exact ⟨_, hpS, rfl⟩
    · rintro ⟨hqU, hqT⟩
      rw [← hST] at hqT
      obtain ⟨w, hwS, hwq⟩ := hqT
      obtain ⟨p', hp'⟩ := nonempty_pointsOver_of_isClosed
        (hcl.inter ((isClosed_singleton_toHom q).preimage r.continuous))
        (⟨w, hwS, hwq⟩ : (S ∩ r.base ⁻¹' {q.toHom (IsLocalRing.closedPoint ℂ)}).Nonempty)
      have hp'r : p' ∈ Set.range (map (K := ℂ) I.subschemeι) := by
        rw [range_map_of_isClosedImmersion]
        change p'.toHom (IsLocalRing.closedPoint ℂ) ∈ Set.range I.subschemeι
        rw [hrange]; exact hp'.1
      obtain ⟨p, rfl⟩ := hp'r
      refine ⟨_, ⟨p, fun h ↦ h ?_, rfl⟩, ?_⟩
      · change r.base (I.subschemeι.base (p.toHom (IsLocalRing.closedPoint ℂ))) ∈ (U : Set Y)
        have h3 : r.base (I.subschemeι.base (p.toHom (IsLocalRing.closedPoint ℂ))) =
          q.toHom (IsLocalRing.closedPoint ℂ) := hp'.2
        exact h3 ▸ hqU
      · exact mapFun_eq_of_base_eq hp'.2
  rw [← himage]
  exact (hAconn.image _ (map (K := ℂ) I.subschemeι).continuous.continuousOn).image _
    (continuous_mapFun (K := ℂ) r).continuousOn

/-- A nonempty open part of an irreducible closed subset of a scheme locally of finite type over
`ℂ` has a closed point. -/
private theorem exists_isClosed_mem_inter [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (U : Y.Opens)
    (T : IrreducibleCloseds Y) (h : ((U : Set Y) ∩ T).Nonempty) :
    ∃ y ∈ (U : Set Y) ∩ T, IsClosed {y} := by
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (.of ℂ))
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints h ⟨_, _, U.isOpen, T.isClosed, rfl⟩
  exact ⟨y, hy, hyc⟩

/-- A closed subset of a scheme locally of finite type over `ℂ` whose complex points lie in a
closed subset lies in it. -/
private theorem subset_of_pointsOver_subset {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h : pointsOver (K := ℂ) A ⊆ pointsOver (K := ℂ) B) : A ⊆ B := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  rw [← closure_inter_closedPoints hA]
  refine closure_minimal (fun a ⟨ha, hac⟩ ↦ ?_) hB
  obtain ⟨p, rfl⟩ := exists_toHom_eq (X := X) hac
  exact h ha

/-- **Tube lemma.** For `K` compact, the points `y` with `f(K × {y}) ⊆ W` form an open set. -/
private theorem isOpen_setOf_forall_mem_of_isCompact {X Y' Z' : Type*} [TopologicalSpace X]
    [TopologicalSpace Y'] [TopologicalSpace Z'] {K : Set X} (hK : IsCompact K)
    {f : X × Y' → Z'} (hf : Continuous f) {W : Set Z'} (hW : IsOpen W) :
    IsOpen {y | ∀ x ∈ K, f (x, y) ∈ W} := by
  rw [isOpen_iff_eventually]
  intro y hy
  exact hK.eventually_forall_of_forall_eventually fun x hx ↦
    ((hf.comp continuous_swap).tendsto (y, x)).eventually (hW.eventually_mem (hy x hx))

/-- A closed irreducible subset of a scheme of dimension `n` is the support of an
`n`-dimensional subvariety. -/
private theorem exists_subvarietyOfDim_support_eq {G : Scheme.{0}} {B : Set G} (hB : IsClosed B)
    (hirr : IsIrreducible B) {n : ℕ} (hd : topologicalKrullDim B = (n : WithBot ℕ∞)) :
    ∃ V : {V : Subvariety G // V.HasDim n}, (V.1.support : Set G) = B := by
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨B, hB⟩ with hI
  have hsupp : (I.support : Set G) = B := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  refine ⟨⟨⟨I, StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ hirr⟩,
    ⟨n, rfl, ?_⟩⟩, hsupp⟩
  change topologicalKrullDim I.subscheme = _
  rw [MMP.Mori.topologicalKrullDim_subscheme_eq, hsupp]
  exact hd

/-- Over `ℂ`, a point whose closure has dimension `n` has relative dimension `n` (Stacks, Tag
02QO). -/
private theorem relativeDimension_eq_of_topologicalKrullDim_closure_eq {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p] (x : X) (n : ℕ)
    (h : topologicalKrullDim (closure ({x} : Set X)) = (n : WithBot ℕ∞)) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction p x =
      n := by
  have hnn := Stacks.Chow.relativeDimension_nonneg (Stacks.Chow.fieldChowSituation ℂ)
    (fun _ _ ↦ rfl) p x
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ p x] at h
  have h' : (Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      p x).toNat = n := by
    exact_mod_cast h
  omega

/-- A closed irreducible curve in the image of a closed immersion is the image of the closure of
a point of delta-dimension one. -/
private theorem exists_curvePt_image_eq {X G : Scheme.{0}} [G.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (G ↘ Spec (.of ℂ))] (f : G ⟶ X)
    [IsClosedImmersion f] {S : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hSf : S ⊆ Set.range f.base) (hd : topologicalKrullDim S = ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ x : CurvePt G, f.base '' closure {x.1} = S := by
  have hemb := f.isClosedEmbedding.isEmbedding
  have hrange : Set.range (fun s : (f.base ⁻¹' S : Set G) ↦ f.base s.1) = S := by
    rw [Set.range_comp' f.base Subtype.val, Subtype.range_coe, Set.image_preimage_eq_of_subset hSf]
  have hirr' := isIrreducible_preimage_of_isEmbedding hemb hirr hSf
  have hcl : closure ({hirr'.genericPoint} : Set G) = f.base ⁻¹' S := by
    have h := hirr'.isGenericPoint_genericPoint_closure
    rw [(hS.preimage f.continuous).closure_eq] at h
    exact h.def
  have hdB : topologicalKrullDim (f.base ⁻¹' S) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [← hd]
    exact ((hemb.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq
  refine ⟨⟨hirr'.genericPoint, relativeDimension_eq_of_topologicalKrullDim_closure_eq _ _ 1
    (by rw [hcl]; exact hdB)⟩, ?_⟩
  change f.base '' closure {hirr'.genericPoint} = S
  rw [hcl, Set.image_preimage_eq_of_subset hSf]

/-- The scheme point under `r` of a complex point is that of its image. -/
private theorem base_toHom_eq (x : UnderlyingSpace ℂ Z) :
    r.base (x.toHom (IsLocalRing.closedPoint ℂ)) =
      (mapFun r x).toHom (IsLocalRing.closedPoint ℂ) := by
  rw [toHom_mapFun]; rfl

/-- **The sheets of edge labellings.** Over a general open `U₀` of `T`, for every edge index,
every `U ≤ U₀` and every `b ∈ (U ∩ T)(ℂ)`, there are a neighbourhood `Δ` of `b`, relatively open
in `(U ∩ T)(ℂ)`, and a transport `ℓ` of the labellings at `b` to labellings over `Δ`: the sheet of
each labelling is connected, contains a neighbourhood of it among the labellings over `U ∩ T`,
the edge equation is constant along it, its curves sweep an open part of each double surface, the
transport matches labels as the labellings at `b` match them, and every labelling over `Δ` lies on
a sheet. -/
private theorem exists_edgeSheet
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ (I : Type) [Fintype I] (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s →
      ∀ U ≤ U₀, ∀ b ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T),
      ∃ Δ : Set (UnderlyingSpace ℂ Y), b ∈ Δ ∧
        (∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) ((U : Set Y) ∩ T)) ∧
        ∃ ℓ : (I → Set Z) → UnderlyingSpace ℂ Y → I → Set Z,
        (∀ lab, IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab →
          ℓ lab b = lab ∧
          (∀ t ∈ Δ, (t.toHom (IsLocalRing.closedPoint ℂ), ℓ lab t) ∈ edgePoints r π s T U) ∧
          @IsPreconnected _ (edgeTopology r I)
            ((fun t ↦ (t.toHom (IsLocalRing.closedPoint ℂ), ℓ lab t)) '' Δ) ∧
          (∃ M, @IsOpen _ (edgeTopology r I) M ∧
            (b.toHom (IsLocalRing.closedPoint ℂ), lab) ∈ M ∧
            M ∩ edgePoints r π s T U ⊆
              (fun t ↦ (t.toHom (IsLocalRing.closedPoint ℂ), ℓ lab t)) '' Δ) ∧
          (∀ t ∈ Δ, ∀ c, EdgeRelation r L π (b.toHom (IsLocalRing.closedPoint ℂ)) lab c ↔
            EdgeRelation r L π (t.toHom (IsLocalRing.closedPoint ℂ)) (ℓ lab t) c) ∧
          ∀ i, ∃ O', IsOpen O' ∧
            O' ∩ pointsOver (K := ℂ) ((π i).carrier ∩ r.base ⁻¹' (U : Set Y)) =
              {p | ∃ t ∈ Δ, p ∈ pointsOver (K := ℂ) (ℓ lab t i)}) ∧
        (∀ t ∈ Δ, ∀ lab₁ lab₂,
          IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab₁ →
          IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab₂ → ∀ i j,
          (pointsOver (K := ℂ) (ℓ lab₁ t i) = pointsOver (K := ℂ) (ℓ lab₂ t j) ↔
            pointsOver (K := ℂ) (lab₁ i) = pointsOver (K := ℂ) (lab₂ j))) ∧
        ∀ t ∈ Δ, ∀ lab', IsEdgeLabeling r π s (t.toHom (IsLocalRing.closedPoint ℂ)) lab' →
          ∃ lab, IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab ∧
            ℓ lab t = lab' := by
  classical
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ (r ≫ Y ↘ Spec (.of ℂ)) := hM.isResolution.2.1
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  have := noetherianSpace_of_isComplexScheme (X := Z)
  obtain ⟨U₁, hU₁, hH2⟩ := exists_transport_fibreClasses hM L T hTs hT1
  obtain ⟨U₂, hU₂, hD⟩ := exists_disjoint_maximal_doubleCurve hM T hT1
  obtain ⟨U₃, hU₃, hE⟩ :=
    exists_forall_of_finite T _ (exists_disjoint_maximal_fibre_of_mem hM T hT1)
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, inter_inter_nonempty_of_irreducibleCloseds T
    (inter_inter_nonempty_of_irreducibleCloseds T hU₁ hU₂) hU₃, ?_⟩
  intro I _ π s hI U hU b hb
  have hU1 : U ≤ U₁ := hU.trans (inf_le_left.trans inf_le_left)
  have hU2 : U ≤ U₂ := hU.trans (inf_le_left.trans inf_le_right)
  have hU3 : U ≤ U₃ := hU.trans inf_le_right
  obtain ⟨Δ, hΔN, ⟨O, hO, hΔO⟩, hΔc, hbΔ, Φ, hΦr, hΦb, hΦE, hcls⟩ :=
    hH2 b ⟨hU1 hb.1, hb.2⟩ (pointsOver (K := ℂ) (U : Set Y))
      ((isOpen_pointsOver_opens U).mem_nhds hb.1)
  let Fb := ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b})
  have hΔ : Δ = O ∩ pointsOver (K := ℂ) ((U : Set Y) ∩ T) := by
    ext t
    constructor
    · intro ht
      have h' := hΔO ▸ ht
      exact ⟨h'.1, hΔN ht, h'.2.2⟩
    · rintro ⟨htO, htU, htT⟩
      rw [hΔO]; exact ⟨htO, hU1 htU, htT⟩
  have hΔUT : ∀ t ∈ Δ, t.toHom (IsLocalRing.closedPoint ℂ) ∈ (U : Set Y) ∩ T :=
    fun t ht ↦ (hΔ ▸ ht).2
  have hΦσ : ∀ (σ : DoubleSurface F) p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier ↔
      (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier :=
    mem_pointsOver_carrier_iff_of_homeomorph hΔc hbΔ Φ hΦb hΦE
  have hDt : ∀ t ∈ Δ, ∀ σ : DoubleSurface F, ∀ A B : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) A →
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) B → A ≠ B →
      Disjoint A B :=
    fun t ht σ ↦ (hD _ ⟨hU2 (hΔUT t ht).1, (hΔUT t ht).2⟩ σ).1
  -- the slices of `Φ`
  let hsl : ∀ t : Δ, ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) ≃ₜ
      ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)}) :=
    fun t ↦ transportHomeomorph Φ hΦr t subset_rfl subset_rfl
      (fun z ↦ iff_of_true z.2 ⟨(Φ (z, t)).2.1, hΦr (z, t)⟩)
  have hsl_apply : ∀ t z, (hsl t z : UnderlyingSpace ℂ Z) = Φ (z, t) := fun _ _ ↦ rfl
  have hslσ : ∀ t (σ : DoubleSurface F) z, (hsl t z : UnderlyingSpace ℂ Z) ∈
      pointsOver σ.carrier ↔ (z : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier :=
    fun t σ z ↦ hΦσ σ (z, t)
  have hslσ' : ∀ t (σ : DoubleSurface F) w, ((hsl t).symm w : UnderlyingSpace ℂ Z) ∈
      pointsOver σ.carrier ↔ (w : UnderlyingSpace ℂ Z) ∈ pointsOver σ.carrier := fun t σ w ↦ by
    simpa only [(hsl t).apply_symm_apply] using (hslσ t σ ((hsl t).symm w)).symm
  -- the points of `F_t` are the images of `F_b`
  have hpre : ∀ (t : Δ) (w : UnderlyingSpace ℂ Z),
      w ∈ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {(t : UnderlyingSpace ℂ Y)} →
      ∃ z, (Φ (z, t) : UnderlyingSpace ℂ Z) = w := by
    intro t w hw
    refine ⟨(hsl t).symm ⟨w, hw⟩, ?_⟩
    rw [← hsl_apply, (hsl t).apply_symm_apply]
  -- characterization of a transported double curve
  have hchar : ∀ (σ : DoubleSurface F) (t : Δ) (C C' : Set Z),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩
        r.base ⁻¹' {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) C' →
      (∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
        (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C') →
      ∀ w, w ∈ pointsOver (K := ℂ) C' ↔
        ∃ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ∧
          (Φ (z, t) : UnderlyingSpace ℂ Z) = w := by
    intro σ t C C' hC' hiff w
    constructor
    · intro hw
      obtain ⟨z, rfl⟩ := hpre t w (pointsOver_subset_fibre_of_maximal σ hC' hw)
      exact ⟨z, (hiff z).2 hw, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact (hiff z).1 hz
  -- the transport of double curves
  let ℓ₀ : Set Z → Set Z → UnderlyingSpace ℂ Y → Set Z := fun S A t ↦
    if h : ∃ ht : t ∈ Δ, ∃ C', Maximal (fun B ↦ IsIrreducible B ∧
        B ⊆ S ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) C' ∧
        ∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) A ↔
          (Φ (z, ⟨t, ht⟩) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C'
    then h.2.choose else ∅
  have hℓ₀ : ∀ (σ : DoubleSurface F) (C : Set Z), Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C →
      ∀ (t : Δ), Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩
          r.base ⁻¹' {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)})
          (ℓ₀ σ.carrier C t) ∧
        ∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (ℓ₀ σ.carrier C t) := by
    intro σ C hC t
    have hex : ∃ ht : (t : UnderlyingSpace ℂ Y) ∈ Δ, ∃ C', Maximal (fun B ↦ IsIrreducible B ∧
        B ⊆ σ.carrier ∩ r.base ⁻¹' {((t : UnderlyingSpace ℂ Y).toHom
          (IsLocalRing.closedPoint ℂ))}) C' ∧
        ∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
          (Φ (z, ⟨t, ht⟩) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C' :=
      ⟨t.2, exists_maximal_doubleCurve_transport σ (hDt b hbΔ σ) (hDt t t.2 σ) (hsl t)
        (hslσ t σ) hC⟩
    have h1 : ℓ₀ σ.carrier C t = hex.2.choose := dif_pos hex
    rw [h1]
    exact hex.2.choose_spec
  -- uniqueness of the transported curve
  have huniq : ∀ (σ : DoubleSurface F) (C C' : Set Z), Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C →
      ∀ (t : Δ), Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩
          r.base ⁻¹' {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) C' →
      (∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C') →
      ℓ₀ σ.carrier C t = C' := by
    intro σ C C' hC t hC' hiff
    have hfib : IsClosed (σ.carrier ∩ r.base ⁻¹'
        {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) :=
      (isClosed_carrier σ).inter ((isClosed_singleton_toHom _).preimage r.continuous)
    obtain ⟨h1, h2⟩ := hℓ₀ σ C hC t
    refine eq_of_pointsOver_eq (isClosed_of_maximal hfib h1) (isClosed_of_maximal hfib hC') ?_
    ext w
    rw [hchar σ t C _ h1 h2, hchar σ t C C' hC' hiff]
  -- uniqueness of the curve over `b`
  have huniqb : ∀ (σ : DoubleSurface F) (C₁ C₂ C' : Set Z) (t : Δ),
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C₁ →
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C₂ →
      (∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C₁ ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C') →
      (∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C₂ ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C') → C₁ = C₂ := by
    intro σ C₁ C₂ C' t h₁ h₂ hi₁ hi₂
    have hfib : IsClosed (σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) :=
      (isClosed_carrier σ).inter ((isClosed_singleton_toHom _).preimage r.continuous)
    refine eq_of_pointsOver_eq (isClosed_of_maximal hfib h₁) (isClosed_of_maximal hfib h₂) ?_
    ext w
    constructor
    · intro hw
      have hz := pointsOver_subset_fibre_of_maximal σ h₁ hw
      exact (hi₂ ⟨w, hz⟩).2 ((hi₁ ⟨w, hz⟩).1 hw)
    · intro hw
      have hz := pointsOver_subset_fibre_of_maximal σ h₂ hw
      exact (hi₁ ⟨w, hz⟩).2 ((hi₂ ⟨w, hz⟩).1 hw)
  -- reverse transport
  have hrev : ∀ (σ : DoubleSurface F) (t : Δ) (C' : Set Z), Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹'
          {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) C' →
      ∃ C, Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ σ.carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C ∧
        ∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
          (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C' := by
    intro σ t C' hC'
    obtain ⟨C, hC, hiff⟩ := exists_maximal_doubleCurve_transport σ (hDt t t.2 σ) (hDt b hbΔ σ)
      (hsl t).symm (hslσ' t σ) hC'
    refine ⟨C, hC, fun z ↦ ?_⟩
    have := hiff (hsl t z)
    rw [(hsl t).symm_apply_apply] at this
    exact this.symm
  let ℓ : (I → Set Z) → UnderlyingSpace ℂ Y → I → Set Z := fun lab t i ↦
    ℓ₀ (π i).carrier (lab i) t
  have hmaxb : ∀ lab, IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab → ∀ i,
      Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ (π i).carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) (lab i) :=
    fun lab h i ↦ (h.bijOn (π i)).mapsTo (show π i = π i from rfl)
  -- the transported labelling is a labelling
  have hlabt : ∀ lab, IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab →
      ∀ t : Δ, IsEdgeLabeling r π s ((t : UnderlyingSpace ℂ Y).toHom
        (IsLocalRing.closedPoint ℂ)) (ℓ lab t) := by
    intro lab hlab t
    refine ⟨fun i ↦ ?_, fun σ ↦ ⟨fun i hi ↦ ?_, fun i hi j hj hij ↦ ?_, fun C' hC' ↦ ?_⟩⟩
    · change ℓ₀ (π (s i)).carrier (lab (s i)) t = ℓ₀ (π i).carrier (lab i) t
      rw [hI.π_s, hlab.lab_s]; rfl
    · change π i = σ at hi
      rw [← hi]; exact (hℓ₀ (π i) (lab i) (hmaxb lab hlab i) t).1
    · change π i = σ at hi; change π j = σ at hj
      refine (hlab.bijOn σ).injOn hi hj ?_
      have hfib : IsClosed ((π i).carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) :=
        (isClosed_carrier _).inter ((isClosed_singleton_toHom _).preimage r.continuous)
      have hmj := hmaxb lab hlab j
      rw [hj, ← hi] at hmj
      refine eq_of_pointsOver_eq (isClosed_of_maximal hfib (hmaxb lab hlab i))
        (isClosed_of_maximal hfib hmj) ?_
      have hi1 := (hℓ₀ (π i) (lab i) (hmaxb lab hlab i) t).2
      have hj1 := (hℓ₀ (π j) (lab j) (hmaxb lab hlab j) t).2
      change ℓ₀ (π i).carrier (lab i) t = ℓ₀ (π j).carrier (lab j) t at hij
      ext w
      constructor
      · intro hw
        have hz := pointsOver_subset_fibre_of_maximal _ (hmaxb lab hlab i) hw
        exact (hj1 ⟨w, hz⟩).2 (hij ▸ (hi1 ⟨w, hz⟩).1 hw)
      · intro hw
        have hz := pointsOver_subset_fibre_of_maximal _ (hmaxb lab hlab j) hw
        exact (hi1 ⟨w, hz⟩).2 (hij.symm ▸ (hj1 ⟨w, hz⟩).1 hw)
    · obtain ⟨C, hC, hiff⟩ := hrev σ t C' hC'
      obtain ⟨i, hi, rfl⟩ := (hlab.bijOn σ).surjOn hC
      change π i = σ at hi
      refine ⟨i, hi, ?_⟩
      change ℓ₀ (π i).carrier (lab i) t = C'
      rw [hi]
      exact huniq σ (lab i) C' hC t hC' hiff
  -- surjectivity of `r` and compactness of `F_b`
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hM.isResolution.2.2.2.2
  have hsurj : Function.Surjective r.base := by
    have h := r.denseRange.closure_range
    rw [r.isClosedMap.isClosed_range.closure_eq] at h
    exact Set.range_eq_univ.1 h
  haveI : CompactSpace Fb := isCompact_iff_compactSpace.1
    (((MMP.UnderlyingSpace.isProperMap_map (K := ℂ) r).isCompact_preimage
      isCompact_singleton).inter_left (isClosed_pointsOver F.supp.isClosed))
  have hcont : Continuous fun p : Fb × Δ ↦ (Φ p : UnderlyingSpace ℂ Z) :=
    continuous_subtype_val.comp Φ.continuous
  have hℓb : ∀ lab, IsEdgeLabeling r π s (b.toHom (IsLocalRing.closedPoint ℂ)) lab →
      ℓ lab b = lab := fun lab hlab ↦ funext fun i ↦
    huniq (π i) (lab i) (lab i) (hmaxb lab hlab i) ⟨b, hbΔ⟩ (hmaxb lab hlab i)
      (fun z ↦ by rw [hΦb])
  -- the points over `t ∈ Δ` are the slice of `Φ` at `t`
  have hfibt : ∀ (t : Δ) (w : UnderlyingSpace ℂ Z), w ∈ pointsOver (K := ℂ)
      (r.base ⁻¹' {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) →
      ∃ z : Fb, (Φ (z, t) : UnderlyingSpace ℂ Z) = w := by
    intro t w hw
    refine hpre t w ⟨?_, mapFun_eq_of_base_eq hw⟩
    change w.toHom (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z)
    rw [hM.supp_eq_preimage_singularLocus, Set.mem_preimage]
    have hw' : r.base (w.toHom (IsLocalRing.closedPoint ℂ)) =
        (t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ) := hw
    rw [hw']
    exact hTs (hΔUT t t.2).2
  have hΦfib : ∀ (z : Fb) (t : Δ), (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ)
      (r.base ⁻¹' {(t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ)}) := by
    intro z t
    have h2 : mapFun r (Φ (z, t) : UnderlyingSpace ℂ Z) = t := hΦr (z, t)
    have key : ∀ x : UnderlyingSpace ℂ Z, r.base (x.toHom (IsLocalRing.closedPoint ℂ)) =
        (mapFun r x).toHom (IsLocalRing.closedPoint ℂ) := fun x ↦ by rw [toHom_mapFun]; rfl
    change r.base _ = _
    rw [key, h2]
  refine ⟨Δ, hbΔ, ⟨O, hO, hΔ⟩, ℓ, fun lab hlab ↦ ?_, ?_, ?_⟩
  rotate_left
  · -- matching of labels
    intro t ht lab₁ lab₂ h₁ h₂ i j
    have m₁ := hℓ₀ (π i) (lab₁ i) (hmaxb lab₁ h₁ i) ⟨t, ht⟩
    have m₂ := hℓ₀ (π j) (lab₂ j) (hmaxb lab₂ h₂ j) ⟨t, ht⟩
    constructor
    · intro h
      ext w
      constructor
      · intro hw
        have hz := pointsOver_subset_fibre_of_maximal _ (hmaxb lab₁ h₁ i) hw
        have h3 := (m₁.2 ⟨w, hz⟩).1 hw
        change _ ∈ pointsOver (ℓ lab₁ t i) at h3
        rw [h] at h3
        obtain ⟨z', hz', he⟩ := (hchar _ ⟨t, ht⟩ _ _ m₂.1 m₂.2 _).1 h3
        have : z' = ⟨w, hz⟩ := congrArg Prod.fst (Φ.injective (Subtype.ext he))
        rwa [this] at hz'
      · intro hw
        have hz := pointsOver_subset_fibre_of_maximal _ (hmaxb lab₂ h₂ j) hw
        have h3 := (m₂.2 ⟨w, hz⟩).1 hw
        change _ ∈ pointsOver (ℓ lab₂ t j) at h3
        rw [← h] at h3
        obtain ⟨z', hz', he⟩ := (hchar _ ⟨t, ht⟩ _ _ m₁.1 m₁.2 _).1 h3
        have : z' = ⟨w, hz⟩ := congrArg Prod.fst (Φ.injective (Subtype.ext he))
        rwa [this] at hz'
    · intro h
      ext w
      change w ∈ pointsOver (ℓ₀ (π i).carrier (lab₁ i) t) ↔
        w ∈ pointsOver (ℓ₀ (π j).carrier (lab₂ j) t)
      rw [hchar _ ⟨t, ht⟩ _ _ m₁.1 m₁.2, hchar _ ⟨t, ht⟩ _ _ m₂.1 m₂.2, h]
  · -- every labelling over `Δ` lies on a sheet
    intro t ht lab' hlab'
    set t' : Δ := ⟨t, ht⟩
    have hmaxt : ∀ i, Maximal (fun A ↦ IsIrreducible A ∧
        A ⊆ (π i).carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)}) (lab' i) :=
      fun i ↦ (hlab'.bijOn (π i)).mapsTo (show π i = π i from rfl)
    let rev : Set Z → Set Z → Set Z := fun S A ↦
      if h : ∃ C, Maximal (fun B ↦ IsIrreducible B ∧
          B ⊆ S ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) C ∧
          ∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) C ↔
            (Φ (z, t') : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) A
      then h.choose else ∅
    let lab : I → Set Z := fun i ↦ rev (π i).carrier (lab' i)
    have hspec : ∀ i, Maximal (fun B ↦ IsIrreducible B ∧
          B ⊆ (π i).carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)}) (lab i) ∧
        ∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (lab i) ↔
          (Φ (z, t') : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (lab' i) := by
      intro i
      have hex := hrev (π i) t' (lab' i) (hmaxt i)
      have h1 : lab i = hex.choose := dif_pos hex
      rw [h1]; exact hex.choose_spec
    have hℓt : ℓ lab t = lab' := funext fun i ↦
      huniq (π i) (lab i) (lab' i) (hspec i).1 t' (hmaxt i) (hspec i).2
    refine ⟨lab, ⟨fun i ↦ ?_, fun σ ↦ ⟨fun i hi ↦ ?_, fun i hi j hj hij ↦ ?_, fun C hC ↦ ?_⟩⟩, hℓt⟩
    · change rev (π (s i)).carrier (lab' (s i)) = rev (π i).carrier (lab' i)
      rw [hI.π_s, hlab'.lab_s]; rfl
    · change π i = σ at hi
      rw [← hi]; exact (hspec i).1
    · change π i = σ at hi; change π j = σ at hj
      refine (hlab'.bijOn σ).injOn hi hj ?_
      rw [← congrFun hℓt i, ← congrFun hℓt j]
      change ℓ₀ (π i).carrier (lab i) t = ℓ₀ (π j).carrier (lab j) t
      rw [hi, hj, hij]
    · obtain ⟨m1, m2⟩ := hℓ₀ σ C hC t'
      obtain ⟨i, hi, hi'⟩ := (hlab'.bijOn σ).surjOn m1
      change π i = σ at hi
      refine ⟨i, hi, ?_⟩
      have h1 := (hspec i).1
      have h2 := (hspec i).2
      rw [hi] at h1
      rw [hi'] at h2
      exact huniqb σ (lab i) C _ t' h1 hC h2 m2
  -- the sheet of one labelling
  have hmb := hmaxb lab hlab
  -- `V i`: the points of `F_b` off the other curves of the double surface of `i`
  let V : I → Set Fb := fun i ↦ ⋂ j ∈ {j | π j = π i ∧ lab j ≠ lab i},
    ((Subtype.val : Fb → UnderlyingSpace ℂ Z) ⁻¹' pointsOver (K := ℂ) (lab j))ᶜ
  have hVo : ∀ i, IsOpen (V i) := fun i ↦
    (Set.toFinite _).isOpen_biInter fun j _ ↦ isOpen_compl_iff.2 ((isClosed_pointsOver
      (isClosed_of_maximal ((isClosed_carrier _).inter
        ((isClosed_singleton_toHom b).preimage r.continuous)) (hmb j))).preimage
      continuous_subtype_val)
  have hWex : ∀ i, ∃ W : Set (UnderlyingSpace ℂ Z), IsOpen W ∧
      (Subtype.val ⁻¹' W : Set ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)) =
        Φ '' (V i ×ˢ Set.univ) := fun i ↦
    isOpen_induced_iff.1 (Φ.isOpenMap _ ((hVo i).prod isOpen_univ))
  choose W hWo hWeq using hWex
  have hK4' : ∀ i (t : Δ) (p : UnderlyingSpace ℂ Z), p ∈ pointsOver (K := ℂ) (ℓ lab t i) →
      p ∈ W i := by
    intro i t p hp
    obtain ⟨z, hz, rfl⟩ := (hchar _ t _ _ (hℓ₀ (π i) (lab i) (hmb i) t).1
      (hℓ₀ (π i) (lab i) (hmb i) t).2 p).1 hp
    have hzV : z ∈ V i := by
      refine Set.mem_iInter₂.2 fun j hj hzj ↦ ?_
      have hmj := hmb j
      rw [hj.1] at hmj
      exact Set.disjoint_left.1 (hDt b hbΔ (π i) (lab j) (lab i) hmj (hmb i) hj.2) hzj hz
    have : Φ (z, t) ∈ Φ '' (V i ×ˢ Set.univ) := ⟨(z, t), ⟨hzV, trivial⟩, rfl⟩
    rw [← hWeq] at this
    exact this
  have hK4 : ∀ i (p : UnderlyingSpace ℂ Z), p ∈ W i → p ∈ pointsOver (K := ℂ) (π i).carrier →
      ∀ ht : mapFun r p ∈ Δ, p ∈ pointsOver (K := ℂ) (ℓ lab (mapFun r p) i) := by
    intro i p hpW hpσ ht
    have hpF : p ∈ pointsOver (K := ℂ) (F.supp : Set Z) := by
      change p.toHom (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z)
      rw [DivisorWithCoeffs.coe_supp]
      exact Set.mem_iUnion₂.2 ⟨(π i).fst, (π i).fst_mem, ((π i).carrier_subset hpσ).1⟩
    have hmem : (⟨p, hpF, ht⟩ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ)) ∈
        Subtype.val ⁻¹' W i := hpW
    rw [hWeq] at hmem
    obtain ⟨⟨z, t⟩, ⟨hzV, -⟩, hΦzt⟩ := hmem
    have hpe : (Φ (z, t) : UnderlyingSpace ℂ Z) = p := congrArg Subtype.val hΦzt
    have htp : t = ⟨mapFun r p, ht⟩ :=
      Subtype.ext ((hΦr (z, t)).symm.trans (congrArg (mapFun r) hpe))
    subst htp
    have hzσ : (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (π i).carrier :=
      (hΦσ (π i) (z, _)).1 (hpe ▸ hpσ)
    have hzb : (z : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ) ∈
        (π i).carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)} := by
      refine ⟨hzσ, ?_⟩
      have h2 : mapFun r (z : UnderlyingSpace ℂ Z) = b := z.2.2
      have key : ∀ x : UnderlyingSpace ℂ Z, r.base (x.toHom (IsLocalRing.closedPoint ℂ)) =
          (mapFun r x).toHom (IsLocalRing.closedPoint ℂ) := fun x ↦ by rw [toHom_mapFun]; rfl
      change r.base _ = _
      rw [key, h2]
    obtain ⟨C, hzC, hC⟩ := exists_subset_maximal_of_isIrreducible
      (S := (π i).carrier ∩ r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)})
      isIrreducible_singleton (Set.singleton_subset_iff.2 hzb)
    obtain ⟨j, hj, rfl⟩ := (hlab.bijOn (π i)).surjOn hC
    have hjl : lab j = lab i := by
      by_contra hne
      exact (Set.mem_iInter₂.1 hzV j ⟨hj, hne⟩) (hzC rfl)
    have := ((hℓ₀ (π i) (lab i) (hmb i) ⟨mapFun r p, ht⟩).2 z).1 (hjl ▸ hzC rfl)
    rw [hpe] at this
    exact this
  letI := edgeTopology r I
  refine ⟨hℓb lab hlab, fun t ht ↦ ⟨isClosed_singleton_toHom t, hΔUT t ht, hlabt lab hlab ⟨t, ht⟩⟩,
    ?_, ?_, ?_, fun i ↦ ?_⟩
  · -- the sheet is connected
    refine hΔc.image _ ?_
    rw [continuousOn_iff_continuous_restrict]
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨W₀, W', hW₀, hW', rfl⟩
    change IsOpen ((fun t : Δ ↦ ((t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ),
      ℓ lab t)) ⁻¹' _)
    have hset : (fun t : Δ ↦ ((t : UnderlyingSpace ℂ Y).toHom (IsLocalRing.closedPoint ℂ),
        ℓ lab t)) ⁻¹'
        {x | pointsOver (K := ℂ) (r.base ⁻¹' {x.1}) ⊆ W₀ ∧
          ∀ i, pointsOver (K := ℂ) (x.2 i) ⊆ W' i} =
        {t : Δ | ∀ z ∈ (Set.univ : Set Fb), (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ W₀} ∩
          ⋂ i, {t : Δ | ∀ z ∈ {z : Fb | (z : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (lab i)},
            (Φ (z, t) : UnderlyingSpace ℂ Z) ∈ W' i} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff,
        Set.mem_iInter, Set.mem_univ, true_implies]
      refine and_congr ⟨fun h z ↦ h (hΦfib z t), fun h w hw ↦ ?_⟩
        (forall_congr' fun i ↦ ⟨fun h z hz ↦ h ((hℓ₀ (π i) (lab i) (hmb i) t).2 z |>.1 hz),
          fun h w hw ↦ ?_⟩)
      · obtain ⟨z, rfl⟩ := hfibt t w hw
        exact h z
      · obtain ⟨z, hz, rfl⟩ := (hchar _ t _ _ (hℓ₀ (π i) (lab i) (hmb i) t).1
          (hℓ₀ (π i) (lab i) (hmb i) t).2 w).1 hw
        exact h z hz
    rw [hset]
    refine IsOpen.inter (isOpen_setOf_forall_mem_of_isCompact isCompact_univ hcont hW₀)
      (isOpen_iInter_of_finite fun i ↦ isOpen_setOf_forall_mem_of_isCompact
        ((isClosed_pointsOver (isClosed_of_maximal ((isClosed_carrier _).inter
          ((isClosed_singleton_toHom b).preimage r.continuous)) (hmb i))).preimage
          continuous_subtype_val).isCompact hcont (hW' i))
  · -- a neighbourhood of the labelling lies on its sheet
    refine ⟨{x | pointsOver (K := ℂ) (r.base ⁻¹' {x.1}) ⊆ mapFun r ⁻¹' O ∧
        ∀ i, pointsOver (K := ℂ) (x.2 i) ⊆ W i},
      isOpen_generateFrom_of_mem ⟨_, W, hO.preimage (continuous_mapFun (K := ℂ) r), hWo, rfl⟩,
      ⟨fun w hw ↦ ?_, fun i w hw ↦ ?_⟩, ?_⟩
    · rw [Set.mem_preimage, mapFun_eq_of_base_eq hw]; exact (hΔ ▸ hbΔ).1
    · have := hK4' i ⟨b, hbΔ⟩ w
      rw [hℓb lab hlab] at this
      exact this hw
    · rintro ⟨y', lab'⟩ ⟨⟨hW₀', hW'⟩, hy'c, hy'UT, hlab'⟩
      obtain ⟨t', rfl⟩ := exists_toHom_eq hy'c
      obtain ⟨z', hz'⟩ := hsurj (t'.toHom (IsLocalRing.closedPoint ℂ))
      obtain ⟨w, hw⟩ := nonempty_pointsOver_of_isClosed (X := Z)
        ((isClosed_singleton_toHom t').preimage r.continuous) ⟨z', hz'⟩
      have ht'O : t' ∈ O := by
        have := hW₀' hw
        rwa [Set.mem_preimage, mapFun_eq_of_base_eq hw] at this
      have ht'Δ : t' ∈ Δ := hΔ ▸ ⟨ht'O, hy'UT⟩
      refine ⟨t', ht'Δ, Prod.ext rfl (funext fun i ↦ ?_)⟩
      have hm' : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (π i).carrier ∩
          r.base ⁻¹' {t'.toHom (IsLocalRing.closedPoint ℂ)}) (lab' i) :=
        (hlab'.bijOn (π i)).mapsTo (show π i = π i from rfl)
      have hmℓ := (hℓ₀ (π i) (lab i) (hmb i) ⟨t', ht'Δ⟩).1
      refine (hm'.eq_of_subset hmℓ.1 (subset_of_pointsOver_subset
        (isClosed_of_maximal ((isClosed_carrier _).inter
          ((isClosed_singleton_toHom t').preimage r.continuous)) hm')
        (isClosed_of_maximal ((isClosed_carrier _).inter
          ((isClosed_singleton_toHom t').preimage r.continuous)) hmℓ) fun p hp ↦ ?_)).symm
      have hpt : mapFun r p = t' := mapFun_eq_of_base_eq (hm'.1.2 hp).2
      have := hK4 i p (hW' i hp) (hm'.1.2 hp).1 (hpt ▸ ht'Δ)
      rw [hpt] at this
      exact this
  · -- the edge equation is constant along the sheet
    intro t ht c
    set t' : Δ := ⟨t, ht⟩
    have hEb := hE _ ⟨hU3 hb.1, hb.2⟩
    have hEt := hE _ ⟨hU3 (hΔUT t ht).1, (hΔUT t ht).2⟩
    -- an irreducible set over `y` in `E` lies in a component of `E_y` or misses it
    have hsep : ∀ (y : Y) (E : F.support), (∀ A B : Set E.1.idealSheaf.subscheme,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) B →
        A ≠ B → Disjoint A B) →
        ∀ (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y})
          (G.1.support : Set _) →
        ∀ S : Set Z, IsIrreducible S → S ⊆ (E.1.support : Set Z) ∩ r.base ⁻¹' {y} →
        S ⊆ Set.range (G.1.ι ≫ E.1.idealSheaf.subschemeι).base ∨
          Disjoint S (Set.range (G.1.ι ≫ E.1.idealSheaf.subschemeι).base) := by
      intro y E hdisj G hG S hS hSy
      have hSr : S ⊆ Set.range E.1.idealSheaf.subschemeι.base := by
        rw [E.1.idealSheaf.range_subschemeι]; exact fun x hx ↦ (hSy hx).1
      have hS' := isIrreducible_preimage_of_isEmbedding
        E.1.idealSheaf.subschemeι.isClosedEmbedding.isEmbedding hS hSr
      obtain ⟨A, hSA, hA⟩ := exists_subset_maximal_of_isIrreducible
        (S := (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) hS' (fun x hx ↦ (hSy hx).2)
      have hR : Set.range (G.1.ι ≫ E.1.idealSheaf.subschemeι).base =
          E.1.idealSheaf.subschemeι.base '' (G.1.support : Set _) := range_ι_comp_subschemeι G.1
      rw [hR]
      by_cases hAG : A = G.1.support
      · left
        intro x hx
        obtain ⟨u, rfl⟩ := hSr hx
        exact ⟨u, hAG ▸ hSA hx, rfl⟩
      · right
        rw [Set.disjoint_left]
        rintro x hx ⟨u, hu, rfl⟩
        exact Set.disjoint_left.1 (hdisj A _ hA hG hAG) (hSA hx) hu
    have key : ∀ (E : F.support) (Gb : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _) →
        ∃ Gt : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2},
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
            {t.toHom (IsLocalRing.closedPoint ℂ)}) (Gt.1.support : Set _) ∧
          (∀ z : Fb, (z : UnderlyingSpace ℂ Z) ∈ pointsOver
              (E.1.idealSheaf.subschemeι.base '' (Gb.1.support : Set _)) ↔
            (Φ (z, t') : UnderlyingSpace ℂ Z) ∈ pointsOver
              (E.1.idealSheaf.subschemeι.base '' (Gt.1.support : Set _))) ∧
          (restrictionClass Gb (L E) = ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
              c i • curveClassOn Gb (lab i) ↔
            restrictionClass Gt (L E) = ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
              c i • curveClassOn Gt (ℓ lab t i)) := by
      intro E Gb hGb
      obtain ⟨Gt, hGt, hGbt, θ, hθ1, hθ2⟩ := hcls t' E Gb hGb
      refine ⟨Gt, hGt, hGbt, ?_⟩
      have hθR : θ (restrictionClass Gb (L E)) = restrictionClass Gt (L E) := hθ2
      have hRb := range_ι_comp_subschemeι Gb.1
      have hRt := range_ι_comp_subschemeι Gt.1
      have hθC : ∀ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
          θ (curveClassOn Gb (lab i)) = curveClassOn Gt (ℓ lab t i) := by
        intro i hi
        have hfst : (π i).fst = E.1 := (Finset.mem_filter.1 hi).2
        have hmi := hmb i
        obtain ⟨hmt, hiff⟩ := hℓ₀ (π i) (lab i) (hmb i) t'
        have hSb : lab i ⊆ (E.1.support : Set Z) ∩
            r.base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)} := fun x hx ↦
          ⟨hfst ▸ ((π i).carrier_subset (hmi.1.2 hx).1).1, (hmi.1.2 hx).2⟩
        have hSt : ℓ lab t i ⊆ (E.1.support : Set Z) ∩
            r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)} := fun x hx ↦
          ⟨hfst ▸ ((π i).carrier_subset (hmt.1.2 hx).1).1, (hmt.1.2 hx).2⟩
        have hclb : IsClosed (lab i) := isClosed_of_maximal ((isClosed_carrier _).inter
          ((isClosed_singleton_toHom b).preimage r.continuous)) hmi
        have hclt : IsClosed (ℓ lab t i) := isClosed_of_maximal ((isClosed_carrier _).inter
          ((isClosed_singleton_toHom t).preimage r.continuous)) hmt
        have hRbc : IsClosed (Set.range (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base) :=
          (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).isClosedEmbedding.isClosed_range
        have hRtc : IsClosed (Set.range (Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base) :=
          (Gt.1.ι ≫ E.1.idealSheaf.subschemeι).isClosedEmbedding.isClosed_range
        have hsubiff : lab i ⊆ Set.range (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base ↔
            ℓ lab t i ⊆ Set.range (Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base := by
          constructor
          · intro h
            refine subset_of_pointsOver_subset hclt hRtc fun w hw ↦ ?_
            obtain ⟨z, hz, rfl⟩ := (hchar _ t' _ _ hmt hiff w).1 hw
            have h1 := pointsOver_mono (K := ℂ) h hz
            rw [hRb] at h1
            rw [hRt]
            exact (hGbt z).1 h1
          · intro h
            refine subset_of_pointsOver_subset hclb hRbc fun w hw ↦ ?_
            have hz := pointsOver_subset_fibre_of_maximal _ hmi hw
            have h1 := pointsOver_mono (K := ℂ) h ((hiff ⟨w, hz⟩).1 hw)
            rw [hRt] at h1
            rw [hRb]
            exact (hGbt ⟨w, hz⟩).2 h1
        rw [curveClassOn_eq_dite Gb hmi.1.1 (hsep _ E (hEb E).1 Gb hGb _ hmi.1.1 hSb),
          curveClassOn_eq_dite Gt hmt.1.1 (hsep _ E (hEt E).1 Gt hGt _ hmt.1.1 hSt)]
        have hdb := (hD _ ⟨hU2 hb.1, hb.2⟩ (π i)).2 _ hmi
        have hdt := (hD _ ⟨hU2 (hΔUT t ht).1, (hΔUT t ht).2⟩ (π i)).2 _ hmt
        split_ifs with h1 h2 h2
        · have e1 : (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {h1.choose.1} =
              lab i := h1.choose_spec
          have e2 : (Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {h2.choose.1} =
              ℓ lab t i := h2.choose_spec
          refine hθ1 ⟨(π i).snd, (π i).snd_mem⟩
            (fun h ↦ (π i).fst_ne_snd (hfst.trans (congrArg Subtype.val h).symm))
            h1.choose h2.choose ?_ fun z ↦ ?_
          · rw [e1]
            exact fun x hx ↦ ((π i).carrier_subset (hmi.1.2 hx).1).2
          · rw [e1, e2]
            exact hiff z
        · exfalso
          have e1 : (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {h1.choose.1} =
              lab i := h1.choose_spec
          have hs : lab i ⊆ Set.range (Gb.1.ι ≫ E.1.idealSheaf.subschemeι).base :=
            e1 ▸ Set.image_subset_range _ _
          obtain ⟨V, hV⟩ := exists_curvePt_image_eq (Gt.1.ι ≫ E.1.idealSheaf.subschemeι)
            hclt hmt.1.1 (hsubiff.1 hs) hdt
          exact h2 ⟨V, hV⟩
        · exfalso
          have e2 : (Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base '' closure {h2.choose.1} =
              ℓ lab t i := h2.choose_spec
          have hs : ℓ lab t i ⊆ Set.range (Gt.1.ι ≫ E.1.idealSheaf.subschemeι).base :=
            e2 ▸ Set.image_subset_range _ _
          obtain ⟨V, hV⟩ := exists_curvePt_image_eq (Gb.1.ι ≫ E.1.idealSheaf.subschemeι)
            hclb hmi.1.1 (hsubiff.2 hs) hdb
          exact h1 ⟨V, hV⟩
        · exact map_zero θ
      have hsum : (∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
          c i • curveClassOn Gt (ℓ lab t i)) =
          θ (∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
            c i • curveClassOn Gb (lab i)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i hi ↦ by rw [map_smul, hθC i hi]
      rw [← hθR, hsum]
      exact θ.injective.eq_iff.symm
    constructor
    · intro hrel E Gt' hGt'
      haveI : CompactSpace E.1.idealSheaf.subscheme :=
        E.1.idealSheaf.subschemeι.isClosedEmbedding.compactSpace
      have hcl : IsClosed (E.1.idealSheaf.subschemeι.base '' (Gt'.1.support : Set _)) :=
        E.1.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap _ Gt'.1.ideal.support.isClosed
      obtain ⟨w, hw⟩ := nonempty_pointsOver_of_isClosed (X := Z) hcl
        ⟨_, ⟨Gt'.1.genericPoint, Gt'.1.isGenericPoint_genericPoint.mem, rfl⟩⟩
      have hwF := pointsOver_image_subset_fibre E.2 hGt'.1.2 hw
      obtain ⟨z, rfl⟩ := hpre t' w hwF
      have hwE : (Φ (z, t') : UnderlyingSpace ℂ Z) ∈ pointsOver (E.1.support : Set Z) := by
        obtain ⟨u, -, hu⟩ := hw
        change _ ∈ (E.1.idealSheaf.support : Set Z)
        rw [← hu, ← E.1.idealSheaf.range_subschemeι]
        exact ⟨u, rfl⟩
      have hzE := (hΦE E.1 E.2 (z, t')).1 hwE
      obtain ⟨x, hx⟩ : (z : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ) ∈
          Set.range E.1.idealSheaf.subschemeι.base := by
        rw [E.1.idealSheaf.range_subschemeι]; exact hzE
      have hxF : x ∈ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {b.toHom (IsLocalRing.closedPoint ℂ)} := by
        change r.base (E.1.idealSheaf.subschemeι.base x) = _
        rw [hx, base_toHom_eq, show mapFun r (z : UnderlyingSpace ℂ Z) = b from z.2.2]
      obtain ⟨A, hxA, hA⟩ := exists_subset_maximal_of_isIrreducible
        (S := (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {b.toHom (IsLocalRing.closedPoint ℂ)})
        isIrreducible_singleton (Set.singleton_subset_iff.2 hxF)
      obtain ⟨Gb, hGbA⟩ := exists_subvarietyOfDim_support_eq
        (isClosed_of_maximal ((isClosed_singleton_toHom b).preimage
          (E.1.idealSheaf.subschemeι ≫ r).continuous) hA) hA.1.1 ((hEb E).2 A hA)
      have hGb : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹'
          {b.toHom (IsLocalRing.closedPoint ℂ)}) (Gb.1.support : Set _) := hGbA ▸ hA
      obtain ⟨Gt, hGt, hGbt, hiffR⟩ := key E Gb hGb
      have hGtt : Gt = Gt' := by
        by_contra hne
        have hne' : (Gt.1.support : Set E.1.idealSheaf.subscheme) ≠
            (Gt'.1.support : Set E.1.idealSheaf.subscheme) := fun h ↦
          hne (Subtype.ext (Subvariety.support_injective h))
        have hd := (hEt E).1 _ _ hGt hGt' hne'
        obtain ⟨u, hu, hu'⟩ := (hGbt z).1 ⟨x, hGbA ▸ hxA rfl, hx⟩
        obtain ⟨u', hu2, hu2'⟩ := hw
        have : u = u' := E.1.idealSheaf.subschemeι.isClosedEmbedding.injective (hu'.trans hu2'.symm)
        exact Set.disjoint_left.1 hd hu (this ▸ hu2)
      subst hGtt
      exact hiffR.1 (hrel E Gb hGb)
    · intro hrel E Gb hGb
      obtain ⟨Gt, hGt, -, hiffR⟩ := key E Gb hGb
      exact hiffR.2 (hrel E Gt hGt)
  · -- the curves of the sheet sweep an open part of the double surface
    refine ⟨W i ∩ mapFun r ⁻¹' O, (hWo i).inter (hO.preimage (continuous_mapFun (K := ℂ) r)), ?_⟩
    ext p
    constructor
    · rintro ⟨⟨hpW, hpO⟩, hpσ, hpU⟩
      have htΔ : mapFun r p ∈ Δ := by
        rw [hΔ]
        refine ⟨hpO, ?_⟩
        rw [mem_pointsOver, toHom_mapFun]
        exact ⟨hpU, hI.image_eq i ▸ ⟨_, hpσ, rfl⟩⟩
      exact ⟨mapFun r p, htΔ, hK4 i p hpW hpσ htΔ⟩
    · rintro ⟨t, ht, hp⟩
      have hm := (hℓ₀ (π i) (lab i) (hmb i) ⟨t, ht⟩).1
      have hpt : mapFun r p = t := mapFun_eq_of_base_eq (hm.1.2 hp).2
      refine ⟨⟨hK4' i ⟨t, ht⟩ p hp, by rw [Set.mem_preimage, hpt]; exact (hΔ ▸ ht).1⟩,
        (hm.1.2 hp).1, ?_⟩
      change r.base _ ∈ (U : Set Y)
      rw [(hm.1.2 hp).2]
      exact (hΔUT t ht).1

/-- **Constancy of the edge equation along a component**, over a complex structure on `Y`. -/
private theorem edgeRelation_of_mem_edgeComponent_aux
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ (I : Type) [Fintype I] (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s →
      ∀ U ≤ U₀, ∀ x₀ ∈ edgePoints r π s T U, ∀ x ∈ edgeComponent r π s T U x₀, ∀ b : I → ℚ,
        EdgeRelation r L π x₀.1 x₀.2 b → EdgeRelation r L π x.1 x.2 b := by
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  obtain ⟨U₀, hU₀, hS⟩ := exists_edgeSheet hM L T hTs hT1
  refine ⟨U₀, hU₀, fun I _ π s hI U hU x₀ hx₀ x hx c hc ↦ ?_⟩
  letI := edgeTopology r I
  refine forall_of_isPreconnected_of_locally_iff isPreconnected_connectedComponentIn
    (fun y ↦ EdgeRelation r L π y.1 y.2 c) (fun y hy ↦ ?_) (mem_connectedComponentIn hx₀) hc x hx
  have hyP := connectedComponentIn_subset _ _ hy
  obtain ⟨y₁, lab⟩ := y
  obtain ⟨hyc, hyUT, hlab⟩ := hyP
  obtain ⟨b, rfl⟩ := exists_toHom_eq hyc
  obtain ⟨Δ, hbΔ, -, ℓ, hℓ, -, -⟩ := hS I π s hI U hU b hyUT
  obtain ⟨-, -, -, ⟨M, hMo, hxM, hMsub⟩, hrel, -⟩ := hℓ lab hlab
  refine ⟨M, hMo, hxM, fun y' hy' ↦ ?_⟩
  obtain ⟨t, ht, rfl⟩ := hMsub ⟨hy'.1, connectedComponentIn_subset _ _ hy'.2⟩
  exact hrel t ht c

/-- A preconnected set of labellings meeting the component of `x₀` lies in it. -/
private theorem subset_connectedComponentIn_of_mem {α : Type*} [TopologicalSpace α]
    {P S : Set α} {x₀ x : α} (hS : IsPreconnected S) (hSP : S ⊆ P) (hxS : x ∈ S)
    (hx : x ∈ connectedComponentIn P x₀) : S ⊆ connectedComponentIn P x₀ :=
  connectedComponentIn_eq hx ▸ hS.subset_connectedComponentIn hxS hSP

/-- Relabelling an edge labelling by a permutation of the labels over the double surfaces which
commutes with `s` gives an edge labelling. -/
private theorem IsEdgeLabeling.comp_perm {I : Type} {π : I → DoubleSurface F} {s : I → I}
    {y : Y} {lab : I → Set Z} (hlab : IsEdgeLabeling r π s y lab) (g : Equiv.Perm I)
    (hgπ : ∀ i, π (g i) = π i) (hgs : ∀ i, s (g i) = g (s i)) :
    IsEdgeLabeling r π s y (lab ∘ g) where
  lab_s i := by simp only [Function.comp_apply, ← hgs, hlab.lab_s]
  bijOn σ := by
    refine (hlab.bijOn σ).comp ⟨fun i hi ↦ by simpa [hgπ] using hi, g.injective.injOn,
      fun i hi ↦ ⟨g.symm i, ?_, g.apply_symm_apply i⟩⟩
    have := hgπ (g.symm i)
    rw [g.apply_symm_apply] at this
    change π (g.symm i) = σ
    rw [← this]; exact hi

/-- Two edge labellings at the same point differ by a permutation of the labels over the double
surfaces commuting with `s`. -/
private theorem exists_perm_of_isEdgeLabeling {T : IrreducibleCloseds Y} {I : Type} [Finite I]
    {π : I → DoubleSurface F} {s : I → I} (hI : IsEdgeIndex r T π s) {y : Y} {lab₁ lab₂ : I → Set Z}
    (h₁ : IsEdgeLabeling r π s y lab₁) (h₂ : IsEdgeLabeling r π s y lab₂) :
    ∃ g : Equiv.Perm I, (∀ i, π (g i) = π i) ∧ (∀ i, s (g i) = g (s i)) ∧ lab₂ = lab₁ ∘ g := by
  have hex : ∀ i, ∃ k, π k = π i ∧ lab₁ k = lab₂ i := fun i ↦
    (h₁.bijOn (π i)).surjOn ((h₂.bijOn (π i)).mapsTo (show π i = π i from rfl))
  choose f hfπ hflab using hex
  have hinj : Function.Injective f := by
    intro i j hij
    have hπ : π i = π j := by rw [← hfπ i, ← hfπ j, hij]
    refine (h₂.bijOn (π i)).injOn (show π i = π i from rfl) (show π j = π i from hπ.symm) ?_
    rw [← hflab, ← hflab, hij]
  set g := Equiv.ofBijective f ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hg : ∀ i, g i = f i := fun _ ↦ rfl
  refine ⟨g, fun i ↦ by rw [hg, hfπ], fun i ↦ ?_, funext fun i ↦ by simp [hg, hflab]⟩
  rw [hg, hg]
  refine (h₁.bijOn (π i).swap).injOn (show π (s (f i)) = (π i).swap by rw [hI.π_s, hfπ])
    (show π (f (s i)) = (π i).swap by rw [hfπ, hI.π_s]) ?_
  rw [h₁.lab_s, hflab, hflab, h₂.lab_s]

/-- A relabelling carrying `x₀` into its component lies in the monodromy group. -/
private theorem mem_edgeSubgroup_of_mem {I : Type} {π : I → DoubleSurface F} {s : I → I}
    {T : IrreducibleCloseds Y} {U : Y.Opens} {x₀ : Y × (I → Set Z)} (g : Equiv.Perm I)
    (hgπ : ∀ i, π (g i) = π i) (hgs : ∀ i, s (g i) = g (s i))
    (hg : (x₀.1, x₀.2 ∘ g) ∈ edgeComponent r π s T U x₀) :
    g ∈ edgeSubgroup π s (edgeComponent r π s T U x₀) := by
  letI := edgeTopology r I
  set P := edgePoints r π s T U
  have hx₀ : x₀ ∈ P := by
    by_contra h
    rw [edgeComponent, connectedComponentIn_eq_empty h] at hg
    exact hg
  have hρ : ∀ h : Equiv.Perm I, Continuous fun x : Y × (I → Set Z) ↦ (x.1, x.2 ∘ h) := by
    intro h
    refine continuous_generateFrom_iff.2 ?_
    rintro _ ⟨W₀, W, hW₀, hW, rfl⟩
    refine isOpen_generateFrom_of_mem ⟨W₀, fun i ↦ W (h.symm i), hW₀, fun i ↦ hW _, ?_⟩
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.comp_apply]
    refine and_congr Iff.rfl ⟨fun H i ↦ ?_, fun H i ↦ ?_⟩
    · simpa using H (h.symm i)
    · simpa using H (h i)
  have hgg : ∀ i, g (g⁻¹ i) = i := fun i ↦ g.apply_symm_apply i
  have hgi : ∀ i, π (g⁻¹ i) = π i := fun i ↦ by
    have := hgπ (g⁻¹ i); rw [hgg] at this; exact this.symm
  have hgis : ∀ i, s (g⁻¹ i) = g⁻¹ (s i) := fun i ↦ by
    apply g.injective
    rw [hgg, ← hgs, hgg]
  have hmapsP : ∀ h : Equiv.Perm I, (∀ i, π (h i) = π i) → (∀ i, s (h i) = h (s i)) →
      ∀ x ∈ P, (x.1, x.2 ∘ h) ∈ P := fun h hπ hs x hx ↦ ⟨hx.1, hx.2.1, hx.2.2.comp_perm h hπ hs⟩
  have himg : ∀ h : Equiv.Perm I, (∀ i, π (h i) = π i) → (∀ i, s (h i) = h (s i)) →
      ∀ x ∈ edgeComponent r π s T U x₀, (x.1, x.2 ∘ h) ∈ edgeComponent r π s T U x₀ →
      ∀ x' ∈ edgeComponent r π s T U x₀, (x'.1, x'.2 ∘ h) ∈ edgeComponent r π s T U x₀ := by
    intro h hπ hs x hx hxh x' hx'
    have hsub := subset_connectedComponentIn_of_mem
      (isPreconnected_connectedComponentIn.image _ (hρ h).continuousOn)
      (by rintro _ ⟨y, hy, rfl⟩; exact hmapsP h hπ hs y (connectedComponentIn_subset _ _ hy))
      ⟨x, hx, rfl⟩ hxh
    exact hsub ⟨x', hx', rfl⟩
  have h₀ := mem_connectedComponentIn hx₀
  refine ⟨hgπ, hgs, fun x hx ↦ ⟨himg g hgπ hgs x₀ h₀ hg x hx, ?_⟩⟩
  refine himg g⁻¹ hgi hgis _ hg ?_ x hx
  have hx₀' : ((x₀.1, x₀.2 ∘ g).1, (x₀.1, x₀.2 ∘ g).2 ∘ ⇑g⁻¹) = x₀ := by
    refine Prod.ext rfl (funext fun k ↦ ?_)
    simp only [Function.comp_apply, hgg]
  rw [hx₀']; exact h₀

/-- **Splitting the double curves**, over a complex structure on `Y`. -/
private theorem exists_edgeIndex_transitive_aux
    (hM : IsCurvePointExceptionalModel (Y ↘ Spec (.of ℂ)) r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus (Y ↘ Spec (.of ℂ)) : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ (I : Type) (_ : Fintype I) (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s ∧
      ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧ ∀ U ≤ U₀, ((U : Set Y) ∩ T).Nonempty →
        ∃ x₀ ∈ edgePoints r π s T U,
          (∀ y ∈ (U : Set Y) ∩ T, IsClosed {y} → ∃ x ∈ edgeComponent r π s T U x₀, x.1 = y) ∧
          ∀ i j, π i = π j → ∃ g ∈ edgeSubgroup π s (edgeComponent r π s T U x₀), g i = j := by
  classical
  haveI : MMP.Mori.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : MMP.Mori.IsVariety ℂ (r ≫ Y ↘ Spec (.of ℂ)) := hM.isResolution.2.1
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have := noetherianSpace_of_isComplexScheme (X := Z)
  have hfinσ := finite_doubleSurface F
  obtain ⟨U₁, hU₁, hS⟩ := exists_edgeSheet hM (fun _ ↦ 0) T hTs hT1
  obtain ⟨U₂, hU₂, hD⟩ := exists_disjoint_maximal_doubleCurve hM T hT1
  obtain ⟨U₃, hU₃, hC⟩ := isConnected_pointsOver_doubleSurface_inter hM T hTs hT1
  obtain ⟨U₄, hU₄, h₄⟩ := exists_open_doubleSurface_image_eq hM T hT1
  set U₀ : Y.Opens := U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄ with hU₀def
  have hU₀ : ((U₀ : Set Y) ∩ T).Nonempty :=
    inter_inter_nonempty_of_irreducibleCloseds T
      (inter_inter_nonempty_of_irreducibleCloseds T
        (inter_inter_nonempty_of_irreducibleCloseds T hU₁ hU₂) hU₃) hU₄
  have hU₀1 : U₀ ≤ U₁ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hU₀2 : U₀ ≤ U₂ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hU₀3 : U₀ ≤ U₃ := inf_le_left.trans inf_le_right
  have hU₀4 : U₀ ≤ U₄ := inf_le_right
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_isClosed_mem_inter U₀ T hU₀
  -- the edge index: the components of the double curves over `y₀`
  let I : Type := {p : DoubleSurface F × Set Z // r.base '' p.1.carrier = (T : Set Y) ∧
    Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ p.1.carrier ∩ r.base ⁻¹' {y₀}) p.2}
  have hIfin : Finite I := by
    have hS : (⋃ σ : DoubleSurface F,
        {A | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y₀}) A}).Finite :=
      Set.finite_iUnion fun σ ↦ finite_setOf_maximal _
    have := hS.to_subtype
    exact Finite.of_injective (β := DoubleSurface F × ↥(⋃ σ : DoubleSurface F,
        {A | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y₀}) A}))
      (fun p ↦ (p.1.1, ⟨p.1.2, Set.mem_iUnion.2 ⟨p.1.1, p.2.2⟩⟩))
      (fun p q h ↦ by
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext (Prod.ext h.1 h.2))
  letI : Fintype I := Fintype.ofFinite I
  let π : I → DoubleSurface F := fun p ↦ p.1.1
  let s : I → I := fun p ↦ ⟨(p.1.1.swap, p.1.2), p.2⟩
  have hI : IsEdgeIndex r T π s :=
    { s_s := fun p ↦ Subtype.ext (Prod.ext (DoubleSurface.swap_swap _) rfl)
      π_s := fun p ↦ rfl
      image_eq := fun p ↦ p.2.1
      exists_eq := fun σ hσ ↦ by
        obtain ⟨z, hz, hzy⟩ : y₀ ∈ r.base '' σ.carrier := hσ ▸ hy₀.2
        obtain ⟨A, -, hA⟩ := exists_subset_maximal_of_isIrreducible
          (S := σ.carrier ∩ r.base ⁻¹' {y₀}) (s := {z}) isIrreducible_singleton
          (Set.singleton_subset_iff.2 ⟨hz, hzy⟩)
        exact ⟨⟨(σ, A), hσ, hA⟩, rfl⟩ }
  -- every closed point of `U₀ ∩ T` carries an edge labelling
  have hlab₀ : IsEdgeLabeling r π s y₀ (fun p ↦ p.1.2) :=
    { lab_s := fun p ↦ rfl
      bijOn := fun σ ↦ by
        refine ⟨fun p hp ↦ ?_, fun p hp q hq h ↦ ?_, fun A hA ↦ ?_⟩
        · change π p = σ at hp
          rw [← hp]; exact p.2.2
        · change π p = σ at hp; change π q = σ at hq
          exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
        · obtain ⟨x, hx⟩ := hA.1.1.nonempty
          have hσT := h₄ y₀ ⟨hU₀4 hy₀.1, hy₀.2⟩ σ ⟨x, (hA.1.2 hx).1, (hA.1.2 hx).2⟩
          exact ⟨⟨(σ, A), hσT, hA⟩, rfl, rfl⟩ }
  have hconnT : ∀ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty →
      IsConnected (pointsOver (K := ℂ) ((U : Set Y) ∩ T)) := isConnected_pointsOver_inter hM T
  have hEX : ∀ t ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T),
      ∃ lab, IsEdgeLabeling r π s (t.toHom (IsLocalRing.closedPoint ℂ)) lab := by
    obtain ⟨b₀, hb₀⟩ := exists_toHom_eq hy₀c
    refine forall_of_isPreconnected_of_locally_iff (hconnT U₀ hU₀).isPreconnected
      (fun t ↦ ∃ lab, IsEdgeLabeling r π s (t.toHom (IsLocalRing.closedPoint ℂ)) lab)
      (fun t ht ↦ ?_) (show b₀ ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T) by
        rw [mem_pointsOver, hb₀]; exact hy₀) ⟨_, by rw [hb₀]; exact hlab₀⟩
    obtain ⟨Δ, htΔ, ⟨O, hO, hΔ⟩, ℓ, hℓ, -, hlast⟩ := hS I π s hI U₀ hU₀1 t ht
    refine ⟨O, hO, (hΔ ▸ htΔ).1, fun t' ht' ↦ ?_⟩
    have ht'Δ : t' ∈ Δ := hΔ ▸ ht'
    exact ⟨fun ⟨lab, hlab⟩ ↦ ⟨_, ((hℓ lab hlab).2.1 t' ht'Δ).2.2⟩,
      fun ⟨lab', hlab'⟩ ↦ (hlast t' ht'Δ lab' hlab').imp fun _ h ↦ h.1⟩
  -- two components of a double surface over a general point sharing a point are equal
  have hG : ∀ y ∈ (U₀ : Set Y) ∩ T, ∀ (σ : DoubleSurface F) (A B : Set Z) (z : Z),
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ σ.carrier ∩ r.base ⁻¹' {y}) B →
      z ∈ A → z ∈ B → A = B := by
    intro y hy σ A B z hA hB hzA hzB
    by_contra hne
    exact Set.disjoint_left.1 ((hD y ⟨hU₀2 hy.1, hy.2⟩ σ).1 A B hA hB hne) hzA hzB
  refine ⟨I, inferInstance, π, s, hI, U₀, hU₀, fun U hU hUT ↦ ?_⟩
  letI := edgeTopology r I
  obtain ⟨y, hyUT, hyc⟩ := exists_isClosed_mem_inter U T hUT
  obtain ⟨b, rfl⟩ := exists_toHom_eq hyc
  obtain ⟨lab, hlab⟩ := hEX b ⟨hU hyUT.1, hyUT.2⟩
  set P := edgePoints r π s T U with hP
  have hx₀ : (b.toHom (IsLocalRing.closedPoint ℂ), lab) ∈ P := ⟨hyc, hyUT, hlab⟩
  set X₀ := edgeComponent r π s T U (b.toHom (IsLocalRing.closedPoint ℂ), lab) with hX₀
  have hUU₁ : U ≤ U₁ := hU.trans hU₀1
  -- sheets through the component stay in it, and conversely
  have hsheet : ∀ t ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T), ∀ (Δ : Set (UnderlyingSpace ℂ Y))
      (ℓ : (I → Set Z) → UnderlyingSpace ℂ Y → I → Set Z) (lab₁ : I → Set Z),
      @IsPreconnected _ (edgeTopology r I)
        ((fun t ↦ (t.toHom (IsLocalRing.closedPoint ℂ), ℓ lab₁ t)) '' Δ) →
      (∀ t' ∈ Δ, (t'.toHom (IsLocalRing.closedPoint ℂ), ℓ lab₁ t') ∈ P) →
      ∀ t₁ ∈ Δ, (t₁.toHom (IsLocalRing.closedPoint ℂ), ℓ lab₁ t₁) ∈ X₀ →
      ∀ t₂ ∈ Δ, (t₂.toHom (IsLocalRing.closedPoint ℂ), ℓ lab₁ t₂) ∈ X₀ := by
    intro t _ Δ ℓ lab₁ hpre hP' t₁ ht₁ h₁ t₂ ht₂
    exact subset_connectedComponentIn_of_mem hpre (by rintro _ ⟨t', ht', rfl⟩; exact hP' t' ht')
      ⟨t₁, ht₁, rfl⟩ h₁ ⟨t₂, ht₂, rfl⟩
  refine ⟨_, hx₀, fun y' hy' hy'c ↦ ?_, fun i j hij ↦ ?_⟩
  · -- the component lies over every closed point of `U ∩ T`
    obtain ⟨t₀, rfl⟩ := exists_toHom_eq hy'c
    refine forall_of_isPreconnected_of_locally_iff (hconnT U hUT).isPreconnected
      (fun t ↦ ∃ x ∈ X₀, x.1 = t.toHom (IsLocalRing.closedPoint ℂ)) (fun t ht ↦ ?_)
      (show b ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T) from hyUT)
      ⟨_, mem_connectedComponentIn hx₀, rfl⟩ t₀ hy'
    obtain ⟨Δ, htΔ, ⟨O, hO, hΔ⟩, ℓ, hℓ, -, hlast⟩ := hS I π s hI U hUU₁ t ht
    refine ⟨O, hO, (hΔ ▸ htΔ).1, fun t' ht' ↦ ?_⟩
    have ht'Δ : t' ∈ Δ := hΔ ▸ ht'
    constructor
    · rintro ⟨⟨x1, lab₁⟩, hxX, rfl⟩
      have hlab₁ := (connectedComponentIn_subset _ _ hxX).2.2
      obtain ⟨hb1, hP', hpre, -⟩ := hℓ lab₁ hlab₁
      refine ⟨_, hsheet t ht Δ ℓ lab₁ hpre hP' t htΔ (by rw [hb1]; exact hxX) t' ht'Δ, rfl⟩
    · rintro ⟨⟨x1, lab'⟩, hxX, rfl⟩
      have hlab' := (connectedComponentIn_subset _ _ hxX).2.2
      obtain ⟨lab₂, hlab₂, hℓ₂⟩ := hlast t' ht'Δ lab' hlab'
      obtain ⟨hb2, hP', hpre, -⟩ := hℓ lab₂ hlab₂
      refine ⟨_, hsheet t ht Δ ℓ lab₂ hpre hP' t' ht'Δ (by rw [hℓ₂]; exact hxX) t htΔ, rfl⟩
  · -- transitivity on the labels of one double surface
    set σ := π i with hσ
    have hσT : r.base '' σ.carrier = (T : Set Y) := hI.image_eq i
    have hXc := hC σ hσT U (hU.trans hU₀3) hUT
    have hfib : ∀ (y : Y) (lab₁ : I → Set Z), IsEdgeLabeling r π s y lab₁ → ∀ k,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (π k).carrier ∩ r.base ⁻¹' {y}) (lab₁ k) :=
      fun y lab₁ h k ↦ (h.bijOn (π k)).mapsTo (show π k = π k from rfl)
    have hover : ∀ (y : Y) (lab₁ : I → Set Z), IsEdgeLabeling r π s y lab₁ → ∀ k,
        ∀ p ∈ pointsOver (K := ℂ) (lab₁ k), r.base (p.toHom (IsLocalRing.closedPoint ℂ)) = y :=
      fun y lab₁ h k p hp ↦ ((hfib y lab₁ h k).1.2 hp).2
    -- the points of `σ` over `U` reached by the label `i` along the component
    have hall : ∀ p ∈ pointsOver (K := ℂ) (σ.carrier ∩ r.base ⁻¹' (U : Set Y)),
        ∃ x ∈ X₀, p ∈ pointsOver (K := ℂ) (x.2 i) := by
      obtain ⟨p₀, hp₀⟩ := nonempty_pointsOver_of_isClosed
        (isClosed_of_maximal ((isClosed_carrier _).inter
          (hyc.preimage r.continuous)) (hfib _ lab hlab i))
        (hfib _ lab hlab i).1.1.nonempty
      refine forall_of_isPreconnected_of_locally_iff hXc.isPreconnected
        (fun p ↦ ∃ x ∈ X₀, p ∈ pointsOver (K := ℂ) (x.2 i)) (fun p hp ↦ ?_)
        (⟨((hfib _ lab hlab i).1.2 hp₀).1, by
          rw [Set.mem_preimage, hover _ lab hlab i p₀ hp₀]; exact hyUT.1⟩)
        ⟨_, mem_connectedComponentIn hx₀, hp₀⟩
      set t := mapFun r p with ht
      have htY : t.toHom (IsLocalRing.closedPoint ℂ) =
          r.base (p.toHom (IsLocalRing.closedPoint ℂ)) := by
        rw [ht, toHom_mapFun]; rfl
      have htUT : t ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T) := by
        rw [mem_pointsOver, htY]
        exact ⟨hp.2, hσT ▸ ⟨_, hp.1, rfl⟩⟩
      obtain ⟨Δ, htΔ, -, ℓ, hℓ, hinj, hlast⟩ := hS I π s hI U hUU₁ t htUT
      obtain ⟨lab₁, hlab₁⟩ := hEX t (pointsOver_mono (Set.inter_subset_inter_left _ hU) htUT)
      have hpσ : p.toHom (IsLocalRing.closedPoint ℂ) ∈
          σ.carrier ∩ r.base ⁻¹' {t.toHom (IsLocalRing.closedPoint ℂ)} := ⟨hp.1, htY.symm⟩
      obtain ⟨A, hpA, hA⟩ := exists_subset_maximal_of_isIrreducible isIrreducible_singleton
        (Set.singleton_subset_iff.2 hpσ)
      obtain ⟨k, hk, rfl⟩ := (hlab₁.bijOn σ).surjOn hA
      obtain ⟨hb1, hP₁, -, -, -, hO'⟩ := hℓ lab₁ hlab₁
      obtain ⟨O', hO'o, hO'eq⟩ := hO' k
      change π k = σ at hk
      have hkσ : (π k).carrier = σ.carrier := by rw [hk]
      have htUT₀ : t.toHom (IsLocalRing.closedPoint ℂ) ∈ (U₀ : Set Y) ∩ T :=
        ⟨hU htUT.1, htUT.2⟩
      -- both sides are: some labelling at `t` on the component has its label `i` at `lab₁ k`
      have key : ∀ p' ∈ O' ∩ pointsOver (K := ℂ) (σ.carrier ∩ r.base ⁻¹' (U : Set Y)),
          ∀ t' ∈ Δ, p' ∈ pointsOver (K := ℂ) (ℓ lab₁ t' k) →
          ((∃ x ∈ X₀, p' ∈ pointsOver (K := ℂ) (x.2 i)) ↔
            ∃ lab₂, IsEdgeLabeling r π s (t.toHom (IsLocalRing.closedPoint ℂ)) lab₂ ∧
              (t.toHom (IsLocalRing.closedPoint ℂ), lab₂) ∈ X₀ ∧
              pointsOver (K := ℂ) (lab₂ i) = pointsOver (K := ℂ) (lab₁ k)) := by
        intro p' _ t' ht' hp'
        have ht'P := hP₁ t' ht'
        have ht'UT₀ : t'.toHom (IsLocalRing.closedPoint ℂ) ∈ (U₀ : Set Y) ∩ T :=
          ⟨hU ht'P.2.1.1, ht'P.2.1.2⟩
        constructor
        · rintro ⟨⟨x1, lab'⟩, hxX, hp'x⟩
          have hxP := connectedComponentIn_subset _ _ hxX
          have hx1 : x1 = t'.toHom (IsLocalRing.closedPoint ℂ) :=
            (hover _ _ hxP.2.2 i p' hp'x).symm.trans (hover _ _ ht'P.2.2 k p' hp')
          subst hx1
          have heq : lab' i = ℓ lab₁ t' k := by
            refine hG _ ht'UT₀ σ _ _ _ (hfib _ _ hxP.2.2 i) ?_ hp'x hp'
            rw [← hkσ]; exact hfib _ _ ht'P.2.2 k
          obtain ⟨lab₂, hlab₂, hℓ₂⟩ := hlast t' ht' lab' hxP.2.2
          obtain ⟨hb2, hP₂, hpre₂, -⟩ := hℓ lab₂ hlab₂
          refine ⟨lab₂, hlab₂, ?_, ?_⟩
          · have := hsheet t htUT Δ ℓ lab₂ hpre₂ hP₂ t' ht' (by rw [hℓ₂]; exact hxX) t htΔ
            rwa [hb2] at this
          · rw [← hinj t' ht' lab₂ lab₁ hlab₂ hlab₁ i k, hℓ₂, heq]
        · rintro ⟨lab₂, hlab₂, hX₂, hpts⟩
          obtain ⟨hb2, hP₂, hpre₂, -⟩ := hℓ lab₂ hlab₂
          refine ⟨_, hsheet t htUT Δ ℓ lab₂ hpre₂ hP₂ t htΔ (by rw [hb2]; exact hX₂) t' ht', ?_⟩
          change p' ∈ pointsOver (K := ℂ) (ℓ lab₂ t' i)
          rw [(hinj t' ht' lab₂ lab₁ hlab₂ hlab₁ i k).2 hpts]; exact hp'
      have hpO' : p ∈ O' := by
        have : p ∈ O' ∩ pointsOver (K := ℂ) ((π k).carrier ∩ r.base ⁻¹' (U : Set Y)) := by
          rw [hO'eq]; exact ⟨t, htΔ, by rw [hb1]; exact hpA rfl⟩
        exact this.1
      refine ⟨O', hO'o, hpO', fun p' hp' ↦ ?_⟩
      have hp'2 : p' ∈ O' ∩ pointsOver (K := ℂ) ((π k).carrier ∩ r.base ⁻¹' (U : Set Y)) := by
        rw [hkσ]; exact hp'
      rw [hO'eq] at hp'2
      obtain ⟨t', ht', hp't'⟩ := hp'2
      rw [key p ⟨hpO', hp⟩ t htΔ (by rw [hb1]; exact hpA rfl), key p' hp' t' ht' hp't']
    -- the permutation carrying `i` to `j`
    obtain ⟨p₁, hp₁⟩ := nonempty_pointsOver_of_isClosed
      (isClosed_of_maximal ((isClosed_carrier _).inter
        (hyc.preimage r.continuous)) (hfib _ lab hlab j))
      (hfib _ lab hlab j).1.1.nonempty
    obtain ⟨⟨x1, lab'⟩, hxX, hp₁x⟩ := hall p₁ ⟨by
      have := ((hfib _ lab hlab j).1.2 hp₁).1; rwa [← hij] at this, by
        rw [Set.mem_preimage, hover _ lab hlab j p₁ hp₁]; exact hyUT.1⟩
    have hxP := connectedComponentIn_subset _ _ hxX
    have hx1 : x1 = b.toHom (IsLocalRing.closedPoint ℂ) :=
      (hover _ _ hxP.2.2 i p₁ hp₁x).symm.trans (hover _ _ hlab j p₁ hp₁)
    subst hx1
    have heq : lab' i = lab j := hG _ ⟨hU hyUT.1, hyUT.2⟩ σ _ _ _ (hfib _ _ hxP.2.2 i)
      (by rw [hij]; exact hfib _ _ hlab j) hp₁x hp₁
    obtain ⟨g, hgπ, hgs, hg⟩ := exists_perm_of_isEdgeLabeling hI hlab hxP.2.2
    refine ⟨g, mem_edgeSubgroup_of_mem g hgπ hgs (by rw [← hg]; exact hxX), ?_⟩
    exact (hlab.bijOn (π j)).injOn (show π (g i) = π j from (hgπ i).trans hij) rfl
      ((congrFun hg i).symm.trans heq)

end EdgeCovering

/-- **Splitting the double curves.** There is an edge index over `T` such that, over every
smaller open, some connected component of the labellings lies over every closed point of `U ∩ T`
and its monodromy group permutes the labels of each double surface transitively (the double
surfaces being irreducible, `S ∩ r⁻¹(U)` is connected). -/
private theorem exists_edgeIndex_transitive
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ (I : Type) (_ : Fintype I) (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s ∧
      ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧ ∀ U ≤ U₀, ((U : Set Y) ∩ T).Nonempty →
        ∃ x₀ ∈ edgePoints r π s T U,
          (∀ y ∈ (U : Set Y) ∩ T, IsClosed {y} → ∃ x ∈ edgeComponent r π s T U x₀, x.1 = y) ∧
          ∀ i j, π i = π j → ∃ g ∈ edgeSubgroup π s (edgeComponent r π s T U x₀), g i = j := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  exact exists_edgeIndex_transitive_aux hM T hTs hT1

/-- **Constancy of the fibre classes.** Over a general open of `T`, the edge equation for fixed
coefficients holds at all labellings of a connected component as soon as it holds at one: the
classes of the curves cut on the fibre components by global divisors are locally constant in
the smooth projective family of fibre components. -/
private theorem edgeRelation_of_mem_edgeComponent
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ (I : Type) [Fintype I] (π : I → DoubleSurface F) (s : I → I), IsEdgeIndex r T π s →
      ∀ U ≤ U₀, ∀ x₀ ∈ edgePoints r π s T U, ∀ x ∈ edgeComponent r π s T U x₀, ∀ b : I → ℚ,
        EdgeRelation r L π x₀.1 x₀.2 b → EdgeRelation r L π x.1 x.2 b := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  exact edgeRelation_of_mem_edgeComponent_aux hM L T hTs hT1

/-- The fibrewise edge argument over one curve `T ⊆ Sing Y`: if `w_T = 0`, an oriented system on
the double surfaces mapping onto `T` kills the restrictions of the `Lᵢ` to every component of a
general surface fibre over `T`. Fibrewise excision solves the edge equation at one labelling;
constancy spreads the solution over its connected component; averaging over the monodromy group
makes it constant on the labels of each double surface; the constant values are the system. -/
private theorem exists_orientedSurfaceCoefficients_generic_vanishing_of_curve
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (T : IrreducibleCloseds Y) (hTs : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hT1 : topologicalKrullDim (T : Set Y) = 1)
    (hwT : ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
        ∀ y ∈ (U : Set Y) ∩ T, ∀ hy : IsClosed {y},
        (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
                ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                ((Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
                (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F,
      (∀ σ, a σ ≠ 0 → r.base '' σ.carrier = T) ∧
      ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, IsClosed {y} →
        ∀ (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
          Maximal (fun A ↦ IsIrreducible A ∧
              A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
          (L E - surfaceCoefficientDivisor a E.1).sum (fun P c ↦ c •
            ∑ᶠ (x : {x : G.1.toScheme // Stacks.Chow.relativeDimension
                (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                (G.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A ↦ IsIrreducible A ∧
                  A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
              Chow.pointCycleClass ℚ x.1 x.2) = 0 := by
  classical
  obtain ⟨Uw, hUw, hw⟩ := hwT
  obtain ⟨U₁, hU₁, h₁⟩ := exists_edgeRelation_of_fibreClass_eq_zero hM L T hTs hT1
  obtain ⟨I, _, π, s, hI, U₂, hU₂, h₂⟩ := exists_edgeIndex_transitive hM T hTs hT1
  obtain ⟨U₃, hU₃, h₃⟩ := edgeRelation_of_mem_edgeComponent hM L T hTs hT1
  obtain ⟨U₄, hU₄, h₄⟩ := restrictionClass_surfaceCoefficientDivisor_eq hM T hT1
  let U : Y.Opens := Uw ⊓ U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄
  have hU : ((U : Set Y) ∩ T).Nonempty :=
    inter_inter_nonempty_of_irreducibleCloseds T
      (inter_inter_nonempty_of_irreducibleCloseds T
        (inter_inter_nonempty_of_irreducibleCloseds T
          (inter_inter_nonempty_of_irreducibleCloseds T hUw hU₁) hU₂) hU₃) hU₄
  have hUw' : ∀ y ∈ (U : Set Y), y ∈ (Uw : Set Y) := fun y hy ↦ hy.1.1.1.1
  have hU₁' : ∀ y ∈ (U : Set Y), y ∈ (U₁ : Set Y) := fun y hy ↦ hy.1.1.1.2
  have hU₂' : U ≤ U₂ := fun y hy ↦ hy.1.1.2
  have hU₃' : U ≤ U₃ := fun y hy ↦ hy.1.2
  have hU₄' : ∀ y ∈ (U : Set Y), y ∈ (U₄ : Set Y) := fun y hy ↦ hy.2
  obtain ⟨x₀, hx₀, hsurj, htrans⟩ := h₂ U hU₂' hU
  set X₀ := edgeComponent r π s T U x₀ with hX₀
  -- one solution at `x₀`, spread over the component
  obtain ⟨b₀, hb₀s, hb₀⟩ := h₁ x₀.1 ⟨hU₁' _ hx₀.2.1.1, hx₀.2.1.2⟩ hx₀.1
    (hw x₀.1 ⟨hUw' _ hx₀.2.1.1, hx₀.2.1.2⟩ hx₀.1) I π s hI x₀.2 hx₀.2.2
  have hall : ∀ x ∈ X₀, EdgeRelation r L π x.1 x.2 b₀ :=
    fun x hx ↦ h₃ I π s hI U hU₃' x₀ hx₀ x hx b₀ hb₀
  -- averaging over the monodromy group
  let Γ := edgeSubgroup π s X₀
  let bbar : I → ℚ := fun j ↦ (Fintype.card Γ : ℚ)⁻¹ * ∑ g : Γ, b₀ ((g : Equiv.Perm I)⁻¹ j)
  have hbar_inv : ∀ h : Γ, ∀ j, bbar ((h : Equiv.Perm I) j) = bbar j := by
    intro h j
    simp only [bbar]
    congr 1
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g ↦ ?_).symm
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  have hbar_s : ∀ j, bbar (s j) = -bbar j := by
    intro j
    simp only [bbar, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    have hgs := (g⁻¹ : Γ).2.2.1 j
    rw [Subgroup.coe_inv] at hgs
    rw [← hgs]
    exact hb₀s _
  have hbar_rel : ∀ x ∈ X₀, EdgeRelation r L π x.1 x.2 bbar := by
    intro x hx E G hG
    have hg : ∀ g : Γ, restrictionClass G (L E) =
        ∑ i ∈ Finset.univ.filter (fun i ↦ (π i).fst = E.1),
          b₀ ((g : Equiv.Perm I)⁻¹ i) • curveClassOn G (x.2 i) := by
      intro g
      rw [hall _ (g.2.2.2 x hx).1 E G hG]
      exact sum_filter_comp_perm π E.1 g g.2.1 b₀ (fun i ↦ curveClassOn G (x.2 i))
    have hcard : (Fintype.card Γ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [bbar, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    rw [Finset.sum_comm, ← Finset.univ.sum_congr rfl fun g _ ↦ hg g, Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  -- the averaged coefficients are constant on the labels of each double surface
  let a : DoubleSurface F → ℚ := fun σ ↦ if h : ∃ i, π i = σ then bbar h.choose else 0
  have ha_eq : ∀ i, a (π i) = bbar i := by
    intro i
    have h : ∃ j, π j = π i := ⟨i, rfl⟩
    simp only [a, dif_pos h]
    obtain ⟨g, hg, hgi⟩ := htrans _ _ h.choose_spec
    have hgc := hbar_inv ⟨g, hg⟩ h.choose
    change bbar (g h.choose) = bbar h.choose at hgc
    rw [hgi] at hgc
    exact hgc.symm
  have ha_zero : ∀ σ, (¬ ∃ i, π i = σ) → a σ = 0 := fun σ h ↦ dif_neg h
  refine ⟨a, ?_, ?_, U, hU, ?_⟩
  · rw [mem_orientedSurfaceCoefficients]
    intro σ
    by_cases h : ∃ i, π i = σ
    · obtain ⟨i, rfl⟩ := h
      rw [← hI.π_s, ha_eq, ha_eq, hbar_s]
    · have h' : ¬ ∃ i, π i = σ.swap := by
        rintro ⟨i, hi⟩
        exact h ⟨s i, by rw [hI.π_s, hi, DoubleSurface.swap_swap]⟩
      rw [ha_zero σ h, ha_zero _ h', neg_zero]
  · intro σ hσ
    by_cases h : ∃ i, π i = σ
    · obtain ⟨i, rfl⟩ := h
      exact hI.image_eq i
    · exact absurd (ha_zero σ h) hσ
  · intro y hy hyc E G hG
    obtain ⟨x, hx, rfl⟩ := hsurj y hy hyc
    have hxe : x ∈ edgePoints r π s T U :=
      @connectedComponentIn_subset _ (edgeTopology r I) _ x₀ x hx
    have hsupp : ∀ σ, a σ ≠ 0 → r.base '' σ.carrier = (T : Set Y) := by
      intro σ hσ
      by_cases h : ∃ i, π i = σ
      · obtain ⟨i, rfl⟩ := h
        exact hI.image_eq i
      · exact absurd (ha_zero σ h) hσ
    have h4 := h₄ x.1 ⟨hU₄' _ hy.1, hy.2⟩ hyc I π s hI x.2 hxe.2.2 a hsupp E G hG
    have hrel := hbar_rel x hx E G hG
    change restrictionClass G (L E - surfaceCoefficientDivisor a E.1) = 0
    rw [restrictionClass, Finsupp.sum_sub_index (fun _ _ _ ↦ sub_smul _ _ _)]
    change restrictionClass G (L E) - restrictionClass G (surfaceCoefficientDivisor a E.1) = 0
    rw [hrel, h4, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [ha_eq]

/-- A system supported on double surfaces whose images avoid `y` does not change the curve classes
cut on a component `G` of the fibre over `y`. -/
private theorem sum_surfaceCoefficientDivisor_eq_zero
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {r : Z ⟶ Y} {F : Divisor Z} (b : DoubleSurface F → ℚ) (y : Y)
    (hb : ∀ σ, b σ ≠ 0 → y ∉ r.base '' σ.carrier)
    (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2})
    (hG : (G.1.support : Set _) ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) :
    (surfaceCoefficientDivisor b E.1).sum (fun P c ↦ c •
      ∑ᶠ (x : {x : G.1.toScheme // Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (G.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
        (_ : Maximal (fun A ↦ IsIrreducible A ∧
            A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2) = 0 := by
  classical
  have := noetherianSpace_of_isComplexScheme (X := Z)
  refine Finset.sum_eq_zero fun P hP => ?_
  have hP' : surfaceCoefficientCoeff b E.1 P ≠ 0 := by
    rw [← coeff_surfaceCoefficientDivisor]; exact Finsupp.mem_support_iff.1 hP
  obtain ⟨⟨σ, hσE, hσP⟩, hσ⟩ : ∃ σ : {σ : DoubleSurface F // σ.fst = E.1 ∧
      σ.carrier = closure {E.1.idealSheaf.subschemeι P.genericPoint}}, b σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hP' (finsum_eq_zero_of_forall_eq_zero h)
  refine smul_eq_zero_of_right _ (finsum_eq_zero_of_forall_eq_zero fun C =>
    finsum_eq_if.trans (if_neg fun hC => ?_))
  have hxC : C.1 ∈ closure ({C.1} : Set G.1.toScheme) := subset_closure rfl
  have hxP : G.1.ι C.1 ∈ (P.support : Set _) := hC.prop.2 hxC
  have hxG : G.1.ι C.1 ∈ (G.1.support : Set _) :=
    (Scheme.IdealSheafData.range_subschemeι _).subset ⟨_, rfl⟩
  apply hb σ hσ
  refine ⟨E.1.idealSheaf.subschemeι (G.1.ι C.1), ?_, hG hxG⟩
  rw [hσP]
  have hcl : G.1.ι C.1 ∈ closure {P.genericPoint} := by
    rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have := image_closure_subset_closure_image (s := {P.genericPoint})
    E.1.idealSheaf.subschemeι.continuous ⟨_, hcl, rfl⟩
  rwa [Set.image_singleton] at this

/-- The fibrewise edge argument: a zero `w_T` is killed on every component of a general surface
fibre by an oriented system on the double surfaces dominating `T`. The systems for the different
curves `T` are put together: a double surface carries the coefficient of the system of the curve
it maps onto, and double surfaces mapping onto another curve `T'` miss the fibres over the points
of `T` outside `T ∩ T'`. -/
private theorem exists_orientedSurfaceCoefficients_generic_vanishing
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    -- `w_T = 0`: on a general fibre the curves cut by the `Lᵢ` add up to `0` in `H_2(F_t, ℚ)`
    (hw : ∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
      topologicalKrullDim (T : Set Y) = 1 →
      ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
        ∀ y ∈ (U : Set Y) ∩ T, ∀ hy : IsClosed {y},
        (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
                ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                ((Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
                (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F,
      (∀ σ, a σ ≠ 0 → topologicalKrullDim (r.base '' σ.carrier) = 1) ∧
      ∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
        topologicalKrullDim (T : Set Y) = 1 →
        ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, IsClosed {y} →
          ∀ (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
            Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
            (L E - surfaceCoefficientDivisor a E.1).sum (fun P c ↦ c •
              ∑ᶠ (x : {x : G.1.toScheme // Stacks.Chow.relativeDimension
                  (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                  (G.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                (_ : Maximal (fun A ↦ IsIrreducible A ∧
                    A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                Chow.pointCycleClass ℚ x.1 x.2) = 0  := by
  classical
  have := noetherianSpace_of_isComplexScheme (X := Z)
  have := finite_doubleSurface F
  let 𝒯 := {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
    topologicalKrullDim (T : Set Y) = 1}
  choose aT haT hsuppT hvanT using fun T : 𝒯 =>
    exists_orientedSurfaceCoefficients_generic_vanishing_of_curve hM L T.1 T.2.1 T.2.2
      (hw T.1 T.2.1 T.2.2)
  -- a double surface carries the coefficient of the system of the curve it maps onto
  let a : DoubleSurface F → ℚ := fun σ =>
    if h : ∃ T : 𝒯, (T.1 : Set Y) = r.base '' σ.carrier then aT h.choose σ else 0
  have ha_eq : ∀ (T : 𝒯) σ, (T.1 : Set Y) = r.base '' σ.carrier → a σ = aT T σ := by
    intro T σ hT
    have h : ∃ T : 𝒯, (T.1 : Set Y) = r.base '' σ.carrier := ⟨T, hT⟩
    have hc : h.choose = T := Subtype.ext (SetLike.coe_injective (h.choose_spec.trans hT.symm))
    simp only [a, dif_pos h, hc]
  have ha_zero : ∀ σ, (¬ ∃ T : 𝒯, (T.1 : Set Y) = r.base '' σ.carrier) → a σ = 0 :=
    fun σ h => dif_neg h
  have hne : ∀ σ, a σ ≠ 0 → ∃ T : 𝒯, (T.1 : Set Y) = r.base '' σ.carrier :=
    fun σ h => by_contra fun h' => h (ha_zero σ h')
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [mem_orientedSurfaceCoefficients]
    intro σ
    by_cases h : ∃ T : 𝒯, (T.1 : Set Y) = r.base '' σ.carrier
    · obtain ⟨T, hT⟩ := h
      rw [ha_eq T σ hT, ha_eq T σ.swap hT, (haT T) σ]
    · rw [ha_zero σ h, ha_zero σ.swap h, neg_zero]
  · intro σ h
    obtain ⟨T, hT⟩ := hne σ h
    rw [← hT]
    exact T.2.2
  · intro T hTs hT1
    let T₀ : 𝒯 := ⟨T, hTs, hT1⟩
    obtain ⟨U, hU, hvan⟩ := hvanT T₀
    -- the double surfaces where `a` differs from the system of `T` map onto other curves
    have hbad : ∀ σ, aT T₀ σ - a σ ≠ 0 →
        ∃ T' : 𝒯, (T'.1 : Set Y) = r.base '' σ.carrier ∧ T' ≠ T₀ := by
      intro σ hσ
      by_cases h0 : aT T₀ σ = 0
      · obtain ⟨T', hT'⟩ := hne σ (by rw [h0, zero_sub, neg_ne_zero] at hσ; exact hσ)
        refine ⟨T', hT', fun h => hσ ?_⟩
        rw [ha_eq T' σ hT', h, sub_self]
      · exact absurd (by rw [ha_eq T₀ σ (hsuppT T₀ σ h0).symm, sub_self]) hσ
    let K : Set Y := ⋃ σ ∈ {σ | aT T₀ σ - a σ ≠ 0}, r.base '' σ.carrier
    have hK : IsClosed K := by
      refine (Set.toFinite _).isClosed_biUnion fun σ hσ => ?_
      obtain ⟨T', hT', -⟩ := hbad σ hσ
      rw [← hT']
      exact T'.1.isClosed
    refine ⟨U ⊓ ⟨Kᶜ, hK.isOpen_compl⟩, ?_, ?_⟩
    · -- the generic point of `T` lies in `U` and in no other curve
      have hgen := T.isIrreducible.isGenericPoint_genericPoint_closure
      rw [T.isClosed.closure_eq] at hgen
      refine ⟨T.isIrreducible.genericPoint, ⟨(hgen.mem_open_set_iff U.2).2 ?_, ?_⟩,
        hgen.mem⟩
      · rwa [Set.inter_comm]
      · intro hη
        obtain ⟨σ, hσ, hη⟩ := Set.mem_iUnion₂.1 hη
        obtain ⟨T', hT', hne'⟩ := hbad σ hσ
        rw [← hT'] at hη
        have hsub : (T : Set Y) ⊆ T'.1 := by
          rw [← hgen.def]
          exact closure_minimal (Set.singleton_subset_iff.2 hη) T'.1.isClosed
        have hneq : (T : Set Y) ≠ T'.1 := fun h =>
          hne' (Subtype.ext (SetLike.coe_injective h.symm))
        have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne T'.1.isIrreducible
          T.isClosed hsub hneq (by rw [T'.2.2]; exact ne_of_beq_false rfl)
        rw [hT1, T'.2.2] at hlt
        exact lt_irrefl _ hlt
    · rintro y ⟨⟨hyU, hyK⟩, hyT⟩ hy E G hG
      have hdecomp : L E - surfaceCoefficientDivisor a E.1 =
          (L E - surfaceCoefficientDivisor (aT T₀) E.1) +
            surfaceCoefficientDivisor (aT T₀ - a) E.1 := by
        have := (surfaceCoefficientDivisorLinearMap F E.1).map_sub (aT T₀) a
        change surfaceCoefficientDivisor (aT T₀ - a) E.1 =
          surfaceCoefficientDivisor (aT T₀) E.1 - surfaceCoefficientDivisor a E.1 at this
        rw [this]
        abel
      rw [hdecomp, Finsupp.sum_add_index', hvan y ⟨hyU, hyT⟩ hy E G hG, zero_add]
      · refine sum_surfaceCoefficientDivisor_eq_zero _ y (fun σ hσ hyσ => hyK ?_) E G hG.prop.2
        exact Set.mem_biUnion (x := σ) hσ hyσ
      · intro _
        exact zero_smul _ _
      · intro _ _ _
        exact add_smul _ _ _

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Removing a zero generic fibre class by double-surface edges.** Let `r : Z ⟶ Y` be a
curve-and-point exceptional model with exceptional divisor `F`, and let `(Lᵢ)ᵢ` be
`ℚ`-divisors on the components `Fᵢ` of `F` whose classes lie in the algebraic kernel `K(r)`
(`MMP.Fourfold.algebraicKernel`). Suppose that for every curve `T ⊆ Sing Y` the classes of the
curves cut by the `Lᵢ` on a general fibre `F_t = r⁻¹(t)`, `t ∈ T`, add up to `0` in
`H_2(F_t, ℚ)`. Then there is an oriented double-surface system `a`
(`MMP.Fourfold.orientedSurfaceCoefficients`) supported on double surfaces mapping onto curves,
such that the classes of the divisors `Lᵢ - Zᵢ(a)` (`MMP.Fourfold.surfaceCoefficientDivisor`)
still lie in `K(r)`, and for every curve `T ⊆ Sing Y`, every general closed point `t ∈ T` and
every irreducible component `G` of the fibre of `Fᵢ` over `t`, the curve cut on `G` by
`Lᵢ - Zᵢ(a)` has class `0` in `H_2(G, ℚ)`. -/
@[mmp "lem_mmp_conductor_remove_generic_zero_by_edges"]
public theorem IsCurvePointExceptionalModel.exists_mem_orientedSurfaceCoefficients_sub
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (hL : (fun E ↦ Chow.divisorClass E.1.idealSheaf.subscheme (L E) : ComponentHomology F) ∈
      algebraicKernel F)
    -- `w_T = 0`: on a general fibre the curves cut by the `Lᵢ` add up to `0` in `H_2(F_t, ℚ)`
    (hw : ∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
      topologicalKrullDim (T : Set Y) = 1 →
      ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
        ∀ y ∈ (U : Set Y) ∩ T, ∀ hy : IsClosed {y},
        (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (x : {x : (Scheme.IdealSheafData.vanishingIdeal
                ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme //
              Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                ((Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subscheme ↘ Spec (.of ℂ)) x =
                (1 : ℕ)})
            (_ : Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (Scheme.IdealSheafData.vanishingIdeal
                  ⟨r.base ⁻¹' {y}, hy.preimage r.continuous⟩).subschemeι.base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {x.1})),
            Chow.pointCycleClass ℚ x.1 x.2) = 0) :
    ∃ a ∈ orientedSurfaceCoefficients F,
      (∀ σ, a σ ≠ 0 → topologicalKrullDim (r.base '' σ.carrier) = 1) ∧
      (fun E ↦ Chow.divisorClass E.1.idealSheaf.subscheme
        (L E - surfaceCoefficientDivisor a E.1) : ComponentHomology F) ∈ algebraicKernel F ∧
      ∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
        topologicalKrullDim (T : Set Y) = 1 →
        ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T, IsClosed {y} →
          ∀ (E : F.support) (G : {V : Subvariety E.1.idealSheaf.subscheme // V.HasDim 2}),
            Maximal (fun A ↦ IsIrreducible A ∧
                A ⊆ (E.1.idealSheaf.subschemeι ≫ r).base ⁻¹' {y}) (G.1.support : Set _) →
            (L E - surfaceCoefficientDivisor a E.1).sum (fun P c ↦ c •
              ∑ᶠ (x : {x : G.1.toScheme // Stacks.Chow.relativeDimension
                  (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
                  (G.1.toScheme ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                (_ : Maximal (fun A ↦ IsIrreducible A ∧
                    A ⊆ G.1.ι.base ⁻¹' (P.support : Set _)) (closure {x.1})),
                Chow.pointCycleClass ℚ x.1 x.2) = 0 := by
  obtain ⟨a, ha, hsupp, hvan⟩ := exists_orientedSurfaceCoefficients_generic_vanishing hM L hw
  refine ⟨a, ha, hsupp, ?_, hvan⟩
  convert (algebraicKernel F).sub_mem hL (surfaceCoefficientClasses_mem_algebraicKernel hM ha)
    using 1
  funext E
  simp [surfaceCoefficientClasses_apply, map_sub]

end MMP.Fourfold
