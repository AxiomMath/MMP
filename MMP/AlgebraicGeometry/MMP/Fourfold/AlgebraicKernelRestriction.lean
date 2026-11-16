module

import MMP.AlgebraicGeometry.Variety.ParameterPoint
import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Analytic.BorelMoore
public import MMP.AlgebraicTopology.CapProduct.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveLocalExactSequence
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ContractedEdgeInjectivity
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDense
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPointsUnderlyingSpace
import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
import MMP.AlgebraicGeometry.Resolution.SNCWithDivisorSmooth
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFamilyTriviality
import MMP.AlgebraicTopology.BorelMoore.FibreClassConstancy
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
import MMP.AlgebraicTopology.BorelMoore.FiniteChains
import MMP.AlgebraicTopology.PoincareDuality.PuncturedLow
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicTopology.CapProduct.SupportLemmas
import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
import MMP.AlgebraicTopology.PoincareDuality.AlexanderSquare
import MMP.AlgebraicTopology.CapProduct.Restriction
import MMP.AlgebraicTopology.PoincareDuality.DualClassSupport
import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCycle
import MMP.AlgebraicGeometry.CycleMap.Stacks.OpenRestriction
import MMP.AlgebraicGeometry.CycleMap.Stacks.PushforwardInjective
import MMP.AlgebraicGeometry.CycleMap.Stacks.FibreSpecialization
import MMP.AlgebraicGeometry.Chow.CycleClassPushforward
import MMP.AlgebraicGeometry.Chow.CycleClassTopDegree
import MMP.AlgebraicGeometry.Chow.RationalCycleClass
import StacksFrontier.AlgebraicGeometry.Intersection.ExteriorProductIntersection
import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Arrows
import StacksFrontier.AlgebraicGeometry.Curves.RegularSectionGeneration.Dimension
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import MMP.AlgebraicGeometry.Morphisms.HProjective
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.IdealSheafSubscheme
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Generic restrictions of the algebraic kernel

Let `r : Z ⟶ Y` be a curve-and-point exceptional model of a normal projective `ℚ`-factorial
terminal complex fourfold, with exceptional divisor `F = ∑ Fᵢ`, algebraic kernel `K(r)` and
algebraic defect `K(r)/B(r)`. For every curve `T ⊆ Sing Y`, a general fibre `F_t = r⁻¹(t)`,
`t ∈ T`, is a projective surface. A tuple `(Lᵢ)ᵢ` of `ℚ`-divisors on the components `Fᵢ` cuts on
`F_t` the curves `Lᵢ ∩ F_t`, and the sum of their fundamental classes is a class
`w_T(t) ∈ H_2(F_t, ℚ)`. Paired with the resolution local system `𝒲_t = H²(F_t, ℚ)`, it vanishes
on the kernel of the restriction map `r : 𝒲_t → 𝒱_{T,t}` when the classes of the `Lᵢ` lie in
`K(r)`, so it is a linear form on the punctured local system `𝒱_{T,t}`; it is monodromy
invariant, depends only on the classes `[Lᵢ]`, and vanishes on `B(r)`. This gives a linear map
`K(r)/B(r) → ⨁_T (𝒱_T^*)^{π₁(T)}`, whose target has dimension `∑_T b_T`.

## Main results

* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_linearMap_curveLocalSystemDual`.

## Implementation notes

* The space `(𝒱_T^*)^{π₁(T°)}` of monodromy invariant forms is the space of families
  `(w_t)_{t ∈ T°(ℂ)}` of linear forms `w_t` on the stalks `𝒱_{T,t}` that are flat: for every
  preconnected open `O ⊆ T°(ℂ)` and every section `s` of `𝒱_T` over `O`, `t ↦ w_t(s_t)` is
  constant on `O`. As `T°(ℂ)` is connected and locally connected, evaluation at a point `t` is
  an isomorphism of it onto the invariants of `π₁(T°, t)` in `𝒱_{T,t}^*`.
* The fundamental class of the curve cut on `F_t` by a prime divisor `P` of `Fᵢ` is the sum of
  the fundamental classes of the irreducible components of `F_t ∩ P` (as sets). For `t` general
  the scheme-theoretic fibre of `P` over `t` is reduced, as the ground field has characteristic
  zero, so this is the class of that fibre. Which `t` are general depends on the tuple `(Lᵢ)`:
  the identity is asserted for all but finitely many `t ∈ T°(ℂ)` (a Zariski-dense open of the
  curve `T°`), the finite exceptional set depending on `(Lᵢ)`. As the forms `Φ [x]` are flat and
  `T°(ℂ)` is connected and infinite, this still determines `Φ`.
* The pairing `⟨β, w⟩ ∈ ℚ` of `β ∈ H²(F_t, ℚ)` with `w ∈ H_2(F_t, ℚ)` is the coefficient of
  the class of a point in the cap product `β ∩ w ∈ H_0(F_t, ℚ)`; `F_t` is connected, so all
  points have the same class, which spans `H_0(F_t, ℚ)`. A germ in `𝒲_t` is represented by a
  class `α ∈ H²(r⁻¹(V), ℚ)` on a neighbourhood `V` of `t`, and is paired with `w` through its
  restriction `α|_{F_t}`.
* "After shrinking `T`": there are adapted opens `T₀ ⊆ T` such that the statement holds for all
  adapted opens `T° ⊆ T₀`, one for each curve `T`.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MMP
open MMP MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Fourfold
open scoped MMP.SubschemeOver
open Stacks.Chow (fieldChowSituation relativeDimension integralComponentAt
  componentMultiplicity cycleAssociatedToClosedSubscheme)

namespace Proof_lem_mmp_conductor_generic_kernel_restriction

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-! ### Auxiliary lemmas on families of curves -/

/-- The preimage of an irreducible set lying in the image of an embedding is irreducible. -/
private theorem isIrreducible_preimage_of_isEmbedding' {A B : Type*} [TopologicalSpace A]
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

/-- The `ℂ`-point of a closed point of a scheme locally of finite type over `ℂ`. -/
private theorem exists_toHom_eq' {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {x : X} (hx : IsClosed {x}) :
    ∃ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) = x :=
  ⟨(UnderlyingSpace.equivClosedPoints (K := ℂ) X).symm ⟨x, hx⟩, by
    rw [← UnderlyingSpace.equivClosedPoints_apply, Equiv.apply_symm_apply]⟩

private theorem topologicalKrullDim_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ B) :
    topologicalKrullDim A ≤ topologicalKrullDim B :=
  (Topology.IsInducing.of_comp (continuous_inclusion h) continuous_subtype_val
    Topology.IsInducing.subtypeVal).topologicalKrullDim_le

/-- **The fibres of a curve-dimensional closed set over a general point.** Let `p : X → C` be a
map from a Noetherian space to an irreducible space with more than one point, and `Z₀ ⊆ X` a
closed set whose irreducible components have dimension at most one. Over a nonempty open of
`C`, the fibres of `Z₀` over closed points contain no irreducible set of dimension `≥ 1`: the
components of `Z₀` contracted to points miss it, and the others meet every fibre in dimension
`0`. -/
private theorem exists_isOpen_forall_topologicalKrullDim_lt_one {X C : Type*} [TopologicalSpace X]
    [TopologicalSpace C] [TopologicalSpace.NoetherianSpace X] [IrreducibleSpace C] [Nontrivial C]
    (p : X → C) (hp : Continuous p) {Z₀ : Set X} (hZ₀ : IsClosed Z₀)
    (hdim : ∀ Zi, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Z₀) Zi → topologicalKrullDim Zi ≤ 1) :
    ∃ W : Set C, IsOpen W ∧ W.Nonempty ∧ ∀ y ∈ W, IsClosed ({y} : Set C) → ∀ A ⊆ Z₀,
      IsIrreducible A → A ⊆ p ⁻¹' {y} → topologicalKrullDim A < 1 := by
  classical
  set M := {Zi | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Z₀) Zi ∧ closure (p '' Zi) ≠ Set.univ}
    with hM
  have hMfin : M.Finite := (finite_setOf_maximal Z₀).subset fun Zi h ↦ h.1
  set Bad := ⋃ Zi ∈ M, closure (p '' Zi) with hBad
  have hBadcl : IsClosed Bad := hMfin.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hBadne : Bad ≠ Set.univ := by
    intro h
    have hfin := hMfin.image (fun Zi ↦ closure (p '' Zi))
    have hu : (Set.univ : Set C) ⊆ ⋃₀ (↑hfin.toFinset : Set (Set C)) := by
      rw [Set.Finite.coe_toFinset, Set.sUnion_image, ← hBad, h]
    obtain ⟨t, ht, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.1
      (IrreducibleSpace.isIrreducible_univ C)) hfin.toFinset
      (fun z hz ↦ by
        rw [Set.Finite.mem_toFinset] at hz
        obtain ⟨Zi, -, rfl⟩ := hz
        exact isClosed_closure) hu
    rw [Set.Finite.mem_toFinset] at ht
    obtain ⟨Zi, hZi, rfl⟩ := ht
    exact hZi.2 (Set.eq_univ_of_univ_subset hsub)
  refine ⟨Badᶜ, hBadcl.isOpen_compl, ?_, fun y hy hycl A hAZ hAirr hAy ↦ ?_⟩
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    exact hBadne h
  by_contra hA
  rw [not_lt] at hA
  obtain ⟨Zi, hAZi, hZi⟩ := exists_subset_maximal_of_isIrreducible hAirr hAZ
  have hZicl : IsClosed Zi := isClosed_of_maximal hZ₀ hZi
  have hcl : closure A = Zi := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hZi.1.1 isClosed_closure
      (closure_minimal hAZi hZicl) hne (ne_top_of_le_ne_top (by decide) (hdim Zi hZi))
    have h1 := topologicalKrullDim_mono (subset_closure : A ⊆ closure A)
    exact lt_irrefl _ (hA.trans_lt (h1.trans_lt (hlt.trans_le (hdim Zi hZi))))
  have h2 : p '' A ⊆ {y} := by rintro _ ⟨x, hx, rfl⟩; exact hAy hx
  have h3 : p '' closure A ⊆ {y} :=
    (image_closure_subset_closure_image hp).trans (closure_minimal h2 hycl)
  have himg : closure (p '' Zi) ⊆ {y} := by
    rw [← hcl]; exact closure_minimal h3 hycl
  have hZiM : Zi ∈ M := by
    refine ⟨hZi, fun h ↦ ?_⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne C
    have ha : a ∈ ({y} : Set C) := himg (h ▸ Set.mem_univ a)
    have hb : b ∈ ({y} : Set C) := himg (h ▸ Set.mem_univ b)
    exact hab (ha.trans hb.symm)
  obtain ⟨x, hx⟩ := hAirr.nonempty
  apply hy
  refine Set.mem_biUnion hZiM (subset_closure ⟨x, hAZi hx, ?_⟩)
  exact hAy hx

/-- In an integral scheme of finite type over `ℂ` of dimension `n + 1`, a prime divisor has
dimension `n`. -/
private theorem topologicalKrullDim_primeDivisor_support {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {n : ℕ}
    (hX : topologicalKrullDim X = ((n + 1 : ℕ) : WithBot ℕ∞)) (D : Mori.PrimeDivisor X) :
    topologicalKrullDim (D.support : Set X) = ((n : ℕ) : WithBot ℕ∞) := by
  have h := ConductorBlowup.topologicalKrullDim_closure_add_coheight D.genericPoint
  rw [D.coheight_genericPoint, hX] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  revert h
  generalize topologicalKrullDim (closure ({D.genericPoint} : Set X)) = e
  intro h
  induction e using WithBot.recBotCoe with
  | bot => exact (WithBot.bot_ne_coe (a := ((n + 1 : ℕ) : ℕ∞)) (by exact_mod_cast h)).elim
  | coe e =>
    have h' : e + 1 = ((n + 1 : ℕ) : ℕ∞) :=
      WithBot.coe_injective (by rw [WithBot.coe_add]; exact_mod_cast h)
    induction e using ENat.recTopCoe with
    | top => exact absurd h' (by rw [top_add]; exact ENat.top_ne_coe _)
    | coe e =>
      have : e + 1 = n + 1 := by exact_mod_cast h'
      rw [(by omega : e = n)]; rfl

/-- An immersion `ι ≫ j_G` restricted to a fibre of `f = ι ≫ g` is a closed immersion when its
image is the trace of a closed set over a closed point. -/
private theorem isClosedImmersion_fibreι_comp_of_range {V G B Z Y : Scheme.{0}} (f : V ⟶ B)
    (ι : V ⟶ G) (jG : G ⟶ Z) [IsPreimmersion (ι ≫ jG)] (jB : B ⟶ Y) (r : Z ⟶ Y)
    (hjB : Function.Injective jB.base) (comm : f ≫ jB = (ι ≫ jG) ≫ r) {S : Set Z}
    (hS : IsClosed S) (h1 : Set.range (ι ≫ jG).base ⊆ S)
    (h2 : S ∩ r.base ⁻¹' Set.range jB.base ⊆ Set.range (ι ≫ jG).base) (s : MMP.ParameterPoint B)
    (hpt : IsClosed {jB.base s.point}) :
    IsClosedImmersion (MMP.ParameterPoint.fibreι f s ≫ ι ≫ jG) := by
  have hrange : Set.range (MMP.ParameterPoint.fibreι f s ≫ ι ≫ jG).base =
      S ∩ r.base ⁻¹' {jB.base s.point} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨h1 ⟨_, rfl⟩, ?_⟩
      have hx : (MMP.ParameterPoint.fibreι f s).base x ∈ f.base ⁻¹' {s.point} := by
        rw [← MMP.ParameterPoint.range_fibreι]; exact ⟨x, rfl⟩
      change ((MMP.ParameterPoint.fibreι f s ≫ ι ≫ jG) ≫ r).base x = _
      rw [Category.assoc, Category.assoc, ← Category.assoc ι, ← comm]
      change jB.base (f.base ((MMP.ParameterPoint.fibreι f s).base x)) = _
      rw [show f.base ((MMP.ParameterPoint.fibreι f s).base x) = s.point from hx]
    · rintro ⟨hzS, hzr⟩
      obtain ⟨v, rfl⟩ := h2 ⟨hzS, by rw [Set.mem_preimage, hzr]; exact ⟨_, rfl⟩⟩
      have hv : f.base v = s.point := by
        apply hjB
        rw [← hzr]
        change (f ≫ jB).base v = ((ι ≫ jG) ≫ r).base v
        rw [comm]
      obtain ⟨w, hw⟩ : v ∈ Set.range (MMP.ParameterPoint.fibreι f s).base := by
        rw [MMP.ParameterPoint.range_fibreι]; exact hv
      refine ⟨w, ?_⟩
      change (ι ≫ jG).base ((MMP.ParameterPoint.fibreι f s).base w) = _
      rw [hw]
  exact .of_isPreimmersion _ (hrange ▸ hS.inter (hpt.preimage r.continuous))

/-! ### Flat families of forms -/

section Flat

variable {X : TopCat.{0}} (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X)

/-- The flat families of linear forms on the stalks of a sheaf `𝓛`: families `(w_t)_t` with
`t ↦ w_t (s_t)` constant on every preconnected open `O` and every section `s` over `O`. -/
private noncomputable def flatForms :
    Submodule ℚ (∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) :=
  ⨅ (O : Opens X) (_ : IsPreconnected (O : Set X))
    (s : ((TopCat.Sheaf.forget _ _).obj 𝓛).obj (op O))
    (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
    LinearMap.ker
      (LinearMap.applyₗ (R := ℚ)
          (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t ht s) ∘ₗ
          LinearMap.proj (R := ℚ)
            (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) t -
        LinearMap.applyₗ (R := ℚ)
          (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t' ht' s) ∘ₗ
          LinearMap.proj (R := ℚ)
            (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) t')

variable {𝓛} in
private theorem mem_flatForms
    {w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)} :
    w ∈ flatForms 𝓛 ↔ ∀ (O : Opens X), IsPreconnected (O : Set X) →
      ∀ (s : ((TopCat.Sheaf.forget _ _).obj 𝓛).obj (op O)) (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
        w t (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t ht s) =
          w t' (((TopCat.Sheaf.forget _ _).obj 𝓛).germ O t' ht' s) := by
  simp only [flatForms, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.applyₗ_apply_apply, sub_eq_zero]

end Flat

/-! ### Stalks of inverse images and of sheafifications -/

section Stalks

variable {A B : TopCat.{0}}

private lemma stalkPushforward_naturality' (f : A ⟶ B)
    {F G : TopCat.Presheaf (ModuleCat.{0} ℚ) A} (g : F ⟶ G) (x : A) :
    TopCat.Presheaf.stalkPushforward _ f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map g =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map g) ≫
        TopCat.Presheaf.stalkPushforward _ f G x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  rfl

private lemma stalkPushforward_comp_naturality' (f : A ⟶ B)
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) B} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) A}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : A) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [stalkPushforward_naturality' f v x, Functor.map_comp, Category.assoc]
  rfl

/-- The canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` is an isomorphism. -/
private lemma isIso_stalkToPullbackStalk (f : A ⟶ B) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) B)
    (x : A) : IsIso (stalkToPullbackStalk f F x) := by
  let ι := (TopCat.Sheaf.pullbackIso (ModuleCat.{0} ℚ) f).app F
  have hunit : (TopCat.Sheaf.forget _ B).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F ≫
      (TopCat.Sheaf.pushforward _ f).map ι.hom) =
      (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ B).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
    have := Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) (ModuleCat.{0} ℚ)
        _ _) F
    have h2 := (sheafToPresheaf _ _).congr_map this
    erw [h2]
    unfold Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    erw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Adjunction.comp_unit_app, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
      Category.comp_id]
    rfl
  have hst : stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map ι.hom) =
      TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ B).obj F) x ≫
        (TopCat.Presheaf.stalkFunctor _ x).map (toSheafify _ _) := by
    have hunit' : (TopCat.Sheaf.forget _ B).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ A).map ι.hom) =
        (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ B).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
      rw [← hunit, Functor.map_comp]
      rfl
    unfold stalkToPullbackStalk TopCat.Presheaf.stalkPullbackHom
    refine (stalkPushforward_comp_naturality' _ _ _ x).trans
      (Eq.trans ?_ (stalkPushforward_comp_naturality' _ _ _ x).symm)
    exact congrArg (fun g ↦ (TopCat.Presheaf.stalkFunctor _ (f x)).map g ≫
      TopCat.Presheaf.stalkPushforward _ f _ x) hunit'
  have h1 : IsIso (TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ B).obj F) x) :=
    (TopCat.Presheaf.stalkPullbackIso _ f ((TopCat.Sheaf.forget _ B).obj F) x).isIso_hom
  have h2 := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ)
    ((TopCat.Presheaf.pullback _ f).obj ((TopCat.Sheaf.forget _ B).obj F))
  have h3 : IsIso ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map ι.hom)) :=
    ((TopCat.Presheaf.stalkFunctor _ x).mapIso ((TopCat.Sheaf.forget _ A).mapIso ι)).isIso_hom
  have : IsIso (stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map ι.hom)) := by
    rw [hst]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h3 this

private theorem bijective_stalkToPullbackStalk (f : A ⟶ B)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) B) (x : A) :
    Function.Bijective (stalkToPullbackStalk f F x).hom :=
  have := isIso_stalkToPullbackStalk f F x
  ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk f F x)

/-- Every element of the stalk of `R^q f_* ℚ_X` at `y` is the germ of a class on `f⁻¹(V)` for
some open `V ∋ y`. -/
private theorem exists_higherDirectImageGerm_eq {X : TopCat.{0}} (f : X ⟶ B) (q : ℕ) (y : B)
    (w : ((TopCat.Sheaf.forget _ B).obj (higherDirectImage f q)).stalk y) :
    ∃ (V : Opens B) (hV : y ∈ V) (α : rationalCohomology (preimageSpace f V) q),
      (higherDirectImageGerm f q y hV).hom α = w := by
  have h2 := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y (ModuleCat.{0} ℚ)
    (directImagePresheaf f q)
  obtain ⟨w', rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor _ y).map (toSheafify _ (directImagePresheaf f q)))).2 w
  obtain ⟨V, hV, α, rfl⟩ := TopCat.Presheaf.germ_exist _ w'
  exact ⟨V, hV, α, rfl⟩

/-- Restriction of classes is compatible with the germs of the higher direct images. -/
private theorem higherDirectImageRestriction_germ {X' X'' Y' : TopCat.{0}} (p : X' ⟶ Y')
    (g' : X'' ⟶ X') {j' : X'' ⟶ Y'} (h : g' ≫ p = j') (q : ℕ) {V : Opens Y'} (y : Y')
    (hy : y ∈ V) (α : rationalCohomology (preimageSpace p V) q) :
    ((TopCat.Presheaf.stalkFunctor _ y).map
        ((TopCat.Sheaf.forget _ Y').map (higherDirectImageRestriction p g' h q))).hom
        ((higherDirectImageGerm p q y hy).hom α) =
      (higherDirectImageGerm j' q y hy).hom (((directImageRestriction p g' h q).app (op V)).hom α) := by
  have e1 : (higherDirectImageGerm p q y hy).hom α =
      ((TopCat.Sheaf.forget _ Y').obj (higherDirectImage p q)).germ V y hy
        (((toSheafify (Opens.grothendieckTopology Y') (directImagePresheaf p q)).app (op V)).hom α) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
      (toSheafify (Opens.grothendieckTopology Y') (directImagePresheaf p q)) α
  have e2 : (higherDirectImageGerm j' q y hy).hom (((directImageRestriction p g' h q).app (op V)).hom α) =
      ((TopCat.Sheaf.forget _ Y').obj (higherDirectImage j' q)).germ V y hy
        (((toSheafify (Opens.grothendieckTopology Y') (directImagePresheaf j' q)).app (op V)).hom
          (((directImageRestriction p g' h q).app (op V)).hom α)) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
      (toSheafify (Opens.grothendieckTopology Y') (directImagePresheaf j' q)) _
  erw [e1, e2, TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  have hn := congrArg (fun ψ ↦ (ψ.app (op V)).hom α)
    (toSheafify_naturality (Opens.grothendieckTopology Y') (directImageRestriction p g' h q))
  exact hn.symm

end Stalks

/-! ### Parallel transport in a local system -/

section Transport

variable {X : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X}

/-- The identification of stalks at equal points is a cast. -/
private lemma stalkCongr_of_eq_apply (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X)
    {x y : X} (h : x = y) (e : (ToType (F.stalk x)) = ToType (F.stalk y)) (w : F.stalk x) :
    (F.stalkCongr (.of_eq h)).hom.hom w = cast e w := by
  subst h
  change (F.stalkSpecializes (specializes_refl x)).hom w = w
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private lemma stalkCongr_germ (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X) {x y : X} (h : x = y)
    {U : Opens X} (hx : x ∈ U) (s : ToType (F.obj (op U))) :
    (F.stalkCongr (.of_eq h)).hom.hom (F.germ U x hx s) = F.germ U y (h ▸ hx) s := by
  subst h
  rw [stalkCongr_of_eq_apply F rfl rfl]
  rfl

/-- The germ of the image of a global section under a sheaf morphism is the image of its germ. -/
private lemma germ_map_hom {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (Ψ : P ⟶ Q)
    (x : X) (s : ToType (P.obj.obj (op ⊤))) :
    (((TopCat.Sheaf.forget _ X).obj Q).germ ⊤ x trivial).hom
        ((((TopCat.Sheaf.forget _ X).map Ψ).app (op ⊤)).hom s) =
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ)
        ((((TopCat.Sheaf.forget _ X).obj P).germ ⊤ x trivial).hom s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial _ s).symm

/-- On stalks, the inverse of a sheaf isomorphism undoes the isomorphism. -/
private lemma stalk_inv_hom_apply {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (Ψ : P ≅ Q) (x : X) (a : ((TopCat.Sheaf.forget _ X).obj P).stalk x) :
    (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ.inv)
      ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ.hom) a) = a :=
  ((TopCat.Presheaf.stalkFunctor _ x).mapIso
    ((TopCat.Sheaf.forget _ X).mapIso Ψ)).hom_inv_id_apply a

/-- The global section of the constant sheaf with value `e`. -/
private noncomputable def constSection {W : TopCat.{0}} (E : ModuleCat.{0} ℚ) (e : E) :
    ToType (((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology W)
    ((Functor.const (Opens W)ᵒᵖ).obj E)).app (op ⊤)).hom e

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem constantSheaf_exists_constSection_germ {W : TopCat.{0}} (E : ModuleCat.{0} ℚ)
    (p : W) (c : ToType (((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).germ
          ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) W := (Functor.const (Opens W)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K) e).symm

/-- A sheaf isomorphic to a constant sheaf has a global section with any prescribed germ. -/
private lemma exists_global_germ_eq {W : TopCat.{0}} {P : TopCat.Sheaf (ModuleCat.{0} ℚ) W}
    {E : ModuleCat.{0} ℚ}
    (φ : P ≅ (constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E) (x : W)
    (c : ((TopCat.Sheaf.forget _ W).obj P).stalk x) :
    ∃ s : ToType (P.obj.obj (op ⊤)),
      c = (((TopCat.Sheaf.forget _ W).obj P).germ ⊤ x trivial).hom s := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E x
    ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ W).map φ.hom) c)
  refine ⟨(((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e), ?_⟩
  refine Eq.trans ?_ (germ_map_hom φ.inv x _).symm
  exact (stalk_inv_hom_apply φ x c).symm.trans (congrArg _ he.symm)

/-- The stalks of a local system are finite-dimensional. -/
private theorem finiteDimensional_stalk (h𝓛 : IsLocalSystem 𝓛) (x : X) :
    FiniteDimensional ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk x) := by
  obtain ⟨V, hx, E, hE, ⟨φ⟩⟩ := h𝓛 x
  let p : (Opens.toTopCat X).obj V := ⟨x, hx⟩
  let C := (TopCat.Sheaf.forget _ _).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
      (ModuleCat.{0} ℚ)).obj E)
  let g : E →ₗ[ℚ] C.stalk p :=
    (C.germ ⊤ p (Opens.mem_top p)).hom ∘ₗ ((CategoryTheory.toSheafify
      (Opens.grothendieckTopology _) ((Functor.const (Opens _)ᵒᵖ).obj E)).app (op ⊤)).hom
  haveI := hE
  haveI : FiniteDimensional ℚ (C.stalk p) :=
    Module.Finite.of_surjective g fun c ↦ constantSheaf_exists_constSection_germ E p c
  let e₁ : ((TopCat.Sheaf.forget _ X).obj 𝓛).stalk x ≃ₗ[ℚ]
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        V.inclusion').obj 𝓛)).stalk p :=
    LinearEquiv.ofBijective (stalkToPullbackStalk V.inclusion' 𝓛 p).hom
      (bijective_stalkToPullbackStalk V.inclusion' 𝓛 p)
  let e₂ : _ ≃ₗ[ℚ] C.stalk p := ((TopCat.Presheaf.stalkFunctor _ p).mapIso
    ((TopCat.Sheaf.forget _ _).mapIso φ)).toLinearEquiv
  exact Module.Finite.equiv (e₁.trans e₂).symm

/-- `u` and `v` are the end germs of a global section of the inverse image of `𝓛` along the
path `γ`. -/
private def PathRel (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X) {x y : X} (γ : Path x y)
    (u : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk x)
    (v : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk y) : Prop :=
  ∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
      (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛).obj.obj (op ⊤)),
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
        𝓛 0).hom
      ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom u) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
          ⊤ 0 trivial).hom s ∧
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
        𝓛 1).hom
      ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
          ⊤ 1 trivial).hom s

/-- **Parallel transport.** The transport relation along a path is the graph of a linear
isomorphism, compatible with concatenation and reversal. -/
private lemma exists_transport [LocallyPathConnectedSpace X] (h𝓛 : IsLocalSystem 𝓛) :
    ∃ tr : ∀ {x y : X}, Path x y → (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk x ≃ₗ[ℚ]
        ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk y),
      (∀ {x y : X} (γ : Path x y) u v, PathRel 𝓛 γ u v ↔ tr γ u = v) ∧
      (∀ {x y z : X} (γ : Path x y) (δ : Path y z) u, tr (γ.trans δ) u = tr δ (tr γ u)) ∧
      (∀ {x y : X} (γ : Path x y) u, tr γ.symm (tr γ u) = u) := by
  have hinj : ∀ {a b : X} (h : a = b), Function.Injective
      (((TopCat.Sheaf.forget _ X).obj 𝓛).stalkCongr (.of_eq h)).hom.hom := fun h =>
    (ConcreteCategory.bijective_of_isIso (C := ModuleCat.{0} ℚ) _).1
  let tr : ∀ {x y : X}, Path x y → (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk x ≃ₗ[ℚ]
      ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk y) :=
    fun γ ↦ (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk γ)).toLinearEquiv
  have htrans : ∀ {x y z : X} (γ : Path x y) (δ : Path y z) u,
      tr (γ.trans δ) u = tr δ (tr γ u) := by
    intro x y z γ δ u
    change (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk (γ.trans δ))).hom u = _
    rw [Path.Homotopic.Quotient.mk_trans, h𝓛.parallelTransport_trans]
    rfl
  have hrefl : ∀ (x : X) u, tr (Path.refl x) u = u := by
    intro x u
    have h1 : Path.Homotopic.Quotient.mk ((Path.refl x).trans (Path.refl x)) =
        Path.Homotopic.Quotient.mk (Path.refl x) :=
      Quotient.sound ⟨Path.Homotopy.transRefl (Path.refl x)⟩
    have h2 : ∀ v, tr (Path.refl x) (tr (Path.refl x) v) = tr (Path.refl x) v := by
      intro v
      rw [← htrans]
      change (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk _)).hom v =
          (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk _)).hom v
      rw [h1]
    have := h2 ((tr (Path.refl x)).symm u)
    rwa [LinearEquiv.apply_symm_apply] at this
  refine ⟨tr, ?_, htrans, ?_⟩
  · intro x y γ u v
    constructor
    · rintro ⟨s, h0, h1⟩
      have key := h𝓛.parallelTransport_germ γ s u
        (by rwa [← stalkCongr_of_eq_apply _ γ.source.symm])
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at key
      exact hinj γ.target.symm ((bijective_stalkToPullbackStalk _ _ 1).1 (key.trans h1.symm))
    · rintro rfl
      obtain ⟨φ⟩ := h𝓛.nonempty_pullback_path_iso_constantSheaf γ
      obtain ⟨s, h0⟩ := exists_global_germ_eq φ 0
        ((stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 0).hom ((((TopCat.Sheaf.forget _ X).obj 𝓛).stalkCongr
            (.of_eq γ.source.symm)).hom.hom u))
      have h1 := h𝓛.parallelTransport_germ γ s u
        (by rwa [← stalkCongr_of_eq_apply _ γ.source.symm])
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at h1
      exact ⟨s, h0, h1⟩
  · intro x y γ u
    rw [← htrans]
    have h1 : Path.Homotopic.Quotient.mk (γ.trans γ.symm) =
        Path.Homotopic.Quotient.mk (Path.refl x) :=
      Quotient.sound ⟨(Path.Homotopy.reflTransSymm γ).symm⟩
    change (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk _)).hom u = u
    rw [h1]
    exact hrefl x u

/-- The section of `f^* 𝓛` over `f⁻¹(W)` attached to a section of `𝓛` over `W`. -/
private noncomputable def unitSec {A : TopCat.{0}} (f : A ⟶ X) {W : Opens X}
    (r : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ A).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj
      𝓛)).obj (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ X).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝓛)).app
      (op W)).hom r

private theorem stalkToPullbackStalk_germ {A : TopCat.{0}} (f : A ⟶ X) {W : Opens X}
    (r : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op W))) (x : A) (hx : f x ∈ W) :
    (stalkToPullbackStalk f 𝓛 x).hom (((TopCat.Sheaf.forget _ X).obj 𝓛).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ A).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ
        ((Opens.map f).obj W) x hx (unitSec f r) := by
  have h : ((TopCat.Sheaf.forget _ X).obj 𝓛).germ W (f x) hx ≫ stalkToPullbackStalk f 𝓛 x =
      ((TopCat.Sheaf.forget _ X).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝓛)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ A).obj
            ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ ((Opens.map f).obj W) x
              hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

/-- The image of a germ under a morphism of sheaves, read in the inverse images. -/
private theorem stalkToPullbackStalk_germ_map {A : TopCat.{0}} (f : A ⟶ X)
    {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (φ : P ⟶ Q) {W : Opens X}
    (s : ToType (((TopCat.Sheaf.forget _ X).obj P).obj (op W))) (x : A) (hx : f x ∈ W) :
    ((TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ A).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ))).hom
        ((stalkToPullbackStalk f P x).hom (((TopCat.Sheaf.forget _ X).obj P).germ W (f x) hx s)) =
      (stalkToPullbackStalk f Q x).hom (((TopCat.Sheaf.forget _ X).obj Q).germ W (f x) hx
        ((((TopCat.Sheaf.forget _ X).map φ).app (op W)).hom s)) := by
  rw [stalkToPullbackStalk_germ, stalkToPullbackStalk_germ]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  congr 1
  have hu := congrArg (fun ψ : P ⟶ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj Q) ↦
        (((TopCat.Sheaf.forget _ X).map ψ).app (op W)).hom s)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality φ)
  exact hu.symm

/-- Every section of `f^* 𝓛` is, near each point, the image of a section of `𝓛`. -/
private theorem exists_local_germ {A : TopCat.{0}} (f : A ⟶ X) {U : Opens A}
    (s : ToType (((TopCat.Sheaf.forget _ A).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).obj (op U))) (x₀ : A) (hx₀ : x₀ ∈ U) :
    ∃ (W : Opens X) (r : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op W))) (N : Opens A)
      (_ : x₀ ∈ N) (hNU : N ≤ U) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), ((TopCat.Sheaf.forget _ A).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ U x (hNU hx) s =
        (stalkToPullbackStalk f 𝓛 x).hom
          (((TopCat.Sheaf.forget _ X).obj 𝓛).germ W (f x) (hNW hx) r) := by
  obtain ⟨y, hy⟩ := (bijective_stalkToPullbackStalk f 𝓛 x₀).2
    (((TopCat.Sheaf.forget _ A).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ U x₀ hx₀ s)
  obtain ⟨W, hW, r, rfl⟩ := ((TopCat.Sheaf.forget _ X).obj 𝓛).exists_germ_eq y
  rw [stalkToPullbackStalk_germ] at hy
  obtain ⟨N, hN, iW, iU, e⟩ := ((TopCat.Sheaf.forget _ A).obj
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)).germ_eq x₀ _ _ _ _ hy
  refine ⟨W, r, N, hN, iU.le, iW.le, fun x hx => ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply _ iU x hx, ← e, TopCat.Presheaf.germ_res_apply]
  exact (stalkToPullbackStalk_germ f r x _).symm

/-- A form of a flat family is unchanged along the identification of stalks at equal points. -/
private lemma apply_stalkCongr
    (w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) {a b : X}
    (h : a = b) (u : ((TopCat.Sheaf.forget _ X).obj 𝓛).stalk a) :
    w b ((((TopCat.Sheaf.forget _ X).obj 𝓛).stalkCongr (.of_eq h)).hom.hom u) = w a u := by
  subst h
  rw [stalkCongr_of_eq_apply _ rfl rfl]
  rfl

/-- **Flat forms are invariant under transport.** -/
private theorem apply_eq_of_pathRel [LocallyPathConnectedSpace X]
    {w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)}
    (hw : w ∈ flatForms 𝓛) {x y : X} (γ : Path x y) {u v} (h : PathRel 𝓛 γ u v) :
    w x u = w y v := by
  obtain ⟨σ, h0, h1⟩ := h
  let f := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let e := fun a ↦ Equiv.ofBijective _ (bijective_stalkToPullbackStalk f 𝓛 a)
  let P := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)
  let g : unitInterval → ℚ := fun a ↦ w (f a) ((e a).symm ((P.germ ⊤ a trivial).hom σ))
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a₀
    obtain ⟨W, r, N, ha₀N, hNU, hNW, hloc⟩ := exists_local_germ f σ a₀ trivial
    have hfa₀W : f a₀ ∈ W := hNW ha₀N
    let O : Opens X := ⟨pathComponentIn (W : Set X) (f a₀), W.isOpen.pathComponentIn _⟩
    have hOW : O ≤ W := pathComponentIn_subset
    have hfa₀ : f a₀ ∈ O := mem_pathComponentIn_self hfa₀W
    have hOpre : IsPreconnected (O : Set X) :=
      (isPathConnected_pathComponentIn hfa₀W).isConnected.isPreconnected
    have key : ∀ c (hcN : c ∈ N) (hcO : f c ∈ O), g c =
        w (f c) (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O (f c) hcO
          ((((TopCat.Sheaf.forget _ X).obj 𝓛).map (homOfLE hOW).op).hom r)) := by
      intro c hcN hcO
      have hc := hloc c hcN
      change w (f c) ((e c).symm ((P.germ ⊤ c trivial).hom σ)) = _
      rw [show (P.germ ⊤ c trivial).hom σ = (P.germ ⊤ c (hNU hcN)).hom σ from rfl, hc]
      rw [show (e c).symm ((stalkToPullbackStalk f 𝓛 c).hom _) = _ from
        (e c).symm_apply_apply _, TopCat.Presheaf.germ_res_apply]
    filter_upwards [N.isOpen.mem_nhds ha₀N,
      (O.isOpen.preimage f.hom.continuous).mem_nhds hfa₀] with b hbN hbO
    rw [key b hbN hbO, key a₀ ha₀N hfa₀]
    exact (mem_flatForms.1 hw) O hOpre _ _ hbO _ hfa₀
  have hc := hg.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
    (Set.mem_univ 1)
  have hg0 : g 0 = w x u := by
    have h0' : (P.germ ⊤ 0 trivial).hom σ = (stalkToPullbackStalk f 𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom u) :=
      h0.symm
    change w (f 0) ((e 0).symm ((P.germ ⊤ 0 trivial).hom σ)) = w x u
    rw [h0', show (e 0).symm ((stalkToPullbackStalk f 𝓛 0).hom _) = _ from
      (e 0).symm_apply_apply _]
    exact apply_stalkCongr w γ.source.symm u
  have hg1 : g 1 = w y v := by
    have h1' : (P.germ ⊤ 1 trivial).hom σ = (stalkToPullbackStalk f 𝓛 1).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.target.symm)).hom.hom v) :=
      h1.symm
    change w (f 1) ((e 1).symm ((P.germ ⊤ 1 trivial).hom σ)) = w y v
    rw [h1', show (e 1).symm ((stalkToPullbackStalk f 𝓛 1).hom _) = _ from
      (e 1).symm_apply_apply _]
    exact apply_stalkCongr w γ.target.symm v
  rw [← hg0, ← hg1, hc]

/-- **A section transports to itself** along a path in its domain. -/
private theorem pathRel_germ {O : Opens X}
    (s : ToType (((TopCat.Sheaf.forget _ X).obj 𝓛).obj (op O))) {x y : X} (γ : Path x y)
    (hγ : ∀ a, γ a ∈ O) (hx : x ∈ O) (hy : y ∈ O) :
    PathRel 𝓛 γ (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O x hx s)
      (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O y hy s) := by
  let f := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let P := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝓛)
  have htop : (⊤ : Opens (TopCat.of unitInterval)) ≤ (Opens.map f).obj O := fun a _ ↦ hγ a
  have key : ∀ a : unitInterval, (stalkToPullbackStalk f 𝓛 a).hom
      (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O (f a) (hγ a) s) =
      (P.germ ⊤ a trivial).hom ((P.map (homOfLE htop).op).hom (unitSec f s)) := fun a ↦
    (stalkToPullbackStalk_germ f s a (hγ a)).trans
      (TopCat.Presheaf.germ_res_apply P (homOfLE htop) a trivial (unitSec f s)).symm
  refine ⟨(P.map (homOfLE htop).op).hom (unitSec f s), ?_, ?_⟩
  · rw [stalkCongr_germ _ γ.source.symm]
    exact key 0
  · rw [stalkCongr_germ _ γ.target.symm]
    exact key 1

end Transport

/-! ### Flat forms are the invariant forms -/

section FlatInvariant

variable {X : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X}

/-- The differences `w - v` of the end germs of global sections of `γ^* 𝓛` along loops `γ` at
`t`: they span the relations of the monodromy coinvariants of `𝓛_t`. -/
private def loopSet (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (t : X) :
    Set (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t) :=
  {u | ∃ (γ : Path t t)
      (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
          𝓛).obj.obj (op ⊤)))
      (w v : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t),
      (stalkToPullbackStalk
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr
          (.of_eq γ.source.symm)).hom.hom w) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            𝓛)).germ ⊤ 0 trivial).hom s ∧
      (stalkToPullbackStalk
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 1).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr
          (.of_eq γ.target.symm)).hom.hom v) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            𝓛)).germ ⊤ 1 trivial).hom s ∧
      u = w - v}

private theorem sub_mem_loopSet {t : X} {γ : Path t t} {w v} (h : PathRel 𝓛 γ w v) :
    w - v ∈ loopSet 𝓛 t := by
  obtain ⟨s, h0, h1⟩ := h
  exact ⟨γ, s, w, v, h0, h1, rfl⟩

private theorem pathRel_of_mem_loopSet {t : X} {u} (h : u ∈ loopSet 𝓛 t) :
    ∃ (γ : Path t t) (w v : ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t),
      PathRel 𝓛 γ w v ∧ u = w - v := by
  obtain ⟨γ, s, w, v, h0, h1, rfl⟩ := h
  exact ⟨γ, w, v, ⟨s, h0, h1⟩, rfl⟩

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X]

/-- **A flat family of forms vanishing at one point vanishes.** -/
private theorem eq_zero_of_mem_flatForms_of_isLocalSystem (h𝓛 : IsLocalSystem 𝓛)
    {w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)}
    (hw : w ∈ flatForms 𝓛) (t₀ : X) (h0 : w t₀ = 0) : w = 0 := by
  obtain ⟨tr, htr, -, -⟩ := exists_transport h𝓛
  funext t
  refine LinearMap.ext fun v ↦ ?_
  rw [apply_eq_of_pathRel hw (PathConnectedSpace.somePath t t₀) ((htr _ v _).2 rfl), h0]
  rfl

/-- **Evaluation at a point identifies the flat forms with the invariant forms**, the forms
vanishing on the relations of the monodromy coinvariants. -/
private theorem finite_and_finrank_flatForms (h𝓛 : IsLocalSystem 𝓛) (t₀ : X) :
    Module.Finite ℚ (flatForms 𝓛) ∧ Module.finrank ℚ (flatForms 𝓛) =
      Module.finrank ℚ (((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t₀ ⧸
        Submodule.span ℚ (loopSet 𝓛 t₀)) := by
  obtain ⟨tr, htr, htrans, hsymm⟩ := exists_transport h𝓛
  haveI := finiteDimensional_stalk h𝓛 t₀
  let V := ((TopCat.Sheaf.forget _ _).obj 𝓛).stalk t₀
  let S := Submodule.span ℚ (loopSet 𝓛 t₀)
  let ev : flatForms 𝓛 →ₗ[ℚ] Module.Dual ℚ V :=
    (LinearMap.proj (R := ℚ)
      (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t)) t₀).comp
      (flatForms 𝓛).subtype
  have hinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (eq_zero_of_mem_flatForms_of_isLocalSystem h𝓛 w.2 t₀ hw)
  -- the inverse transport is the transport along the reversed path
  have hinv : ∀ {x y : X} (γ : Path x y) v, (tr γ).symm v = tr γ.symm v := by
    intro x y γ v
    obtain ⟨u, rfl⟩ := (tr γ).surjective v
    rw [LinearEquiv.symm_apply_apply, hsymm]
  have hrange : LinearMap.range ev = S.dualAnnihilator := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      intro u hu
      refine (Submodule.span_le (p := LinearMap.ker (ev w))).2 ?_ hu
      intro u hu
      obtain ⟨γ, a, b, hab, rfl⟩ := pathRel_of_mem_loopSet hu
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact apply_eq_of_pathRel w.2 γ hab
    · intro φ hφ
      rw [Submodule.mem_dualAnnihilator] at hφ
      -- `φ` is invariant under the transport along loops
      have hinv' : ∀ (ℓ : Path t₀ t₀) z, φ (tr ℓ z) = φ z := by
        intro ℓ z
        have := hφ _ (Submodule.subset_span (sub_mem_loopSet ((htr ℓ z _).2 rfl)))
        rw [map_sub, sub_eq_zero] at this
        exact this.symm
      let γ : ∀ t : X, Path t₀ t := fun t ↦ PathConnectedSpace.somePath t₀ t
      let w : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓛).stalk t) :=
        fun t ↦ φ ∘ₗ (tr (γ t)).symm.toLinearMap
      have hw : w ∈ flatForms 𝓛 := by
        rw [mem_flatForms]
        intro O hO s t ht t' ht'
        have hpc : IsPathConnected (O : Set X) :=
          (O.isOpen.isConnected_iff_isPathConnected).1 ⟨⟨t, ht⟩, hO⟩
        have J := hpc.joinedIn t ht t' ht'
        have hδ := (htr _ _ _).1 (pathRel_germ s J.somePath J.somePath_mem ht ht')
        change φ ((tr (γ t)).symm _) = φ ((tr (γ t')).symm _)
        rw [← hδ]
        set z := (tr (γ t)).symm (((TopCat.Sheaf.forget _ X).obj 𝓛).germ O t ht s) with hz
        have hs : ((TopCat.Sheaf.forget _ X).obj 𝓛).germ O t ht s = tr (γ t) z := by
          rw [hz, LinearEquiv.apply_symm_apply]
        rw [hs, hinv, ← htrans, ← htrans, hinv']
      refine ⟨⟨w, hw⟩, ?_⟩
      refine LinearMap.ext fun z ↦ ?_
      change φ ((tr (γ t₀)).symm z) = φ z
      rw [← hinv' (γ t₀) ((tr (γ t₀)).symm z), LinearEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_injective ev hinj, ?_⟩
  rw [(LinearEquiv.ofInjective ev hinj).finrank_eq, (LinearEquiv.ofEq _ _ hrange).finrank_eq,
    ← (Submodule.dualQuotEquivDualAnnihilator S).finrank_eq, Subspace.dual_finrank_eq]

end FlatInvariant

/-! ### Descending flat forms along a surjection of sheaves -/

section FlatDescent

open Topology

variable {X : TopCat.{0}} {𝓦 𝓥 : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (ρ : 𝓦 ⟶ 𝓥)

/-- **Descent of forms along a surjection of sheaves.** Let `ρ : 𝓦 → 𝓥` be surjective on
stalks and `f_x` forms on the stalks `𝓦_x` killing the kernels of `ρ_x`, such that
`x ↦ f_x(s_x)` is locally constant for every local section `s` of `𝓦`. Then the forms `ψ_x` on
`𝓥_x` with `ψ_x ∘ ρ_x = f_x` form a flat family. -/
private theorem exists_mem_flatForms_comp_eq
    (hsurj : ∀ x, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ρ)).hom)
    (f : ∀ x, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj 𝓦).stalk x))
    (hker : ∀ x e, ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ρ)).hom e
      = 0 → f x e = 0)
    (hloc : ∀ (U : Opens X) (s : ToType (((TopCat.Sheaf.forget _ X).obj 𝓦).obj (op U))) (x₀ : X)
      (hx₀ : x₀ ∈ U), ∀ᶠ x in 𝓝 x₀, ∀ hx : x ∈ U,
        f x (((TopCat.Sheaf.forget _ X).obj 𝓦).germ U x hx s) =
          f x₀ (((TopCat.Sheaf.forget _ X).obj 𝓦).germ U x₀ hx₀ s)) :
    ∃ ψ ∈ flatForms 𝓥, ∀ x e, ψ x
      (((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ρ)).hom e) = f x e := by
  set ρs := fun x ↦ ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ρ)).hom
    with hρs
  choose g hg using fun x ↦ LinearMap.exists_rightInverse_of_surjective (ρs x)
    (LinearMap.range_eq_top.2 (hsurj x))
  have hψ : ∀ x e, f x (g x (ρs x e)) = f x e := fun x e ↦ by
    have h0 : ρs x (g x (ρs x e) - e) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hg x, LinearMap.id_apply, sub_self]
    have h1 := hker x _ h0
    have h2 := (f x).map_sub (g x (ρs x e)) e
    exact sub_eq_zero.1 (h2 ▸ h1)
  refine ⟨fun x ↦ (f x).comp (g x), ?_, fun x e ↦ hψ x e⟩
  rw [mem_flatForms]
  intro O hO s t ht t' ht'
  set φ : O → ℚ := fun x ↦ f x.1 (g x.1
    (((TopCat.Sheaf.forget _ X).obj 𝓥).germ O x.1 x.2 s)) with hφ
  have hlc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    obtain ⟨e, he⟩ := hsurj x₀.1 (((TopCat.Sheaf.forget _ X).obj 𝓥).germ O x₀.1 x₀.2 s)
    obtain ⟨U, hU, s', rfl⟩ := ((TopCat.Sheaf.forget _ X).obj 𝓦).germ_exist e
    have hgerm : ((TopCat.Sheaf.forget _ X).obj 𝓥).germ U x₀.1 hU
        ((((TopCat.Sheaf.forget _ X).map ρ).app (op U)).hom s') =
        ((TopCat.Sheaf.forget _ X).obj 𝓥).germ O x₀.1 x₀.2 s := by
      rw [← he]
      exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x₀.1 hU _ s').symm
    obtain ⟨W, hW, iU, iO, hres⟩ :=
      ((TopCat.Sheaf.forget _ X).obj 𝓥).germ_eq x₀.1 hU x₀.2 _ _ hgerm
    have hev := hloc U s' x₀ hU
    have hWn : (W : Set X) ∈ 𝓝 x₀.1 := W.isOpen.mem_nhds hW
    have hev' : ∀ᶠ x in 𝓝 x₀.1, x ∈ W ∧ ∀ hx : x ∈ U,
        f x (((TopCat.Sheaf.forget _ X).obj 𝓦).germ U x hx s') =
          f x₀ (((TopCat.Sheaf.forget _ X).obj 𝓦).germ U x₀ hU s') :=
      (show ∀ᶠ x in 𝓝 x₀.1, x ∈ W from hWn).and hev
    rw [nhds_subtype_eq_comap]
    refine Filter.eventually_comap.2 (hev'.mono fun x hx y hy ↦ ?_)
    subst hy
    obtain ⟨hxW, hxf⟩ := hx
    have hgx : ∀ z : O, ∀ hz : (z : X) ∈ W, ((TopCat.Sheaf.forget _ X).obj 𝓥).germ O z.1 z.2 s =
        ρs z.1 (((TopCat.Sheaf.forget _ X).obj 𝓦).germ U z.1 (iU.le hz) s') := by
      intro z hz
      rw [← TopCat.Presheaf.germ_res_apply _ iO z.1 hz s, ← hres, TopCat.Presheaf.germ_res_apply]
      exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U z.1 _ _ s').symm
    change f y.1 (g y.1 _) = f x₀.1 (g x₀.1 _)
    rw [hgx y hxW, hgx x₀ hW]
    exact (hψ _ _).trans ((hxf _).trans (hψ _ _).symm)
  haveI : PreconnectedSpace O := isPreconnected_iff_preconnectedSpace.1 hO
  exact hlc.apply_eq_of_preconnectedSpace (⟨t, ht⟩ : O) ⟨t', ht'⟩

end FlatDescent

/-! ### The complex points of a local-system open -/

section CurveTopology

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The complex realization of an integral scheme of finite type over `ℂ` is connected: its
regular points form a connected dense subset. -/
private theorem connectedSpace_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] [QuasiCompact sX] :
    ConnectedSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  haveI : QuasiCompact (X ↘ Spec (.of ℂ)) := ‹QuasiCompact sX›
  have hconn : IsConnected (MMP.UnderlyingSpace.regularPart ℂ X) := by
    simpa using MMP.UnderlyingSpace.isConnected_regularPart_diff (X := X)
      isClosed_empty (Set.empty_ne_univ (α := X))
  have huniv : IsConnected (Set.univ : Set (MMP.UnderlyingSpace ℂ X)) := by
    rw [← MMP.UnderlyingSpace.dense_regularPart.closure_eq]
    exact hconn.closure
  haveI : ConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    connectedSpace_iff_univ.mpr huniv
  exact (homeomorphUnderlyingSpace (X := X)).symm.surjective.connectedSpace
    (homeomorphUnderlyingSpace (X := X)).symm.continuous

/-- The complex realization of a scheme locally of finite type over `ℂ` is locally path
connected. -/
private theorem locallyPathConnectedSpace_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    LocallyPathConnectedSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have hb := MMP.UnderlyingSpace.hasOpenContractibleBasis X
  haveI : LocallyPathConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    LocallyPathConnectedSpace.of_bases hb fun x V hV => by
      show IsPathConnected V
      haveI : ContractibleSpace V := hV.2.2
      exact isPathConnected_iff_pathConnectedSpace.2 inferInstance
  exact (homeomorphUnderlyingSpace (X := X)).isOpenEmbedding.locallyPathConnectedSpace

variable {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}

/-- The curve `T` is the image of its closed immersion into `Y`. -/
private lemma range_curveι : Set.range (curveι T) = (T : Set Y) := by
  simp [Scheme.IdealSheafData.range_subschemeι]

/-- The curve `T` with its reduced structure is irreducible, Noetherian and of dimension one. -/
private lemma curveScheme_facts (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) :
    IrreducibleSpace (curveScheme T) ∧ topologicalKrullDim (curveScheme T) = 1 ∧
      IsNoetherian (curveScheme T) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  let e : curveScheme T ≃ₜ (T : Set Y) :=
    (curveι T).isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr range_curveι)
  haveI : IrreducibleSpace (T : Set Y) := Subtype.irreducibleSpace T.isIrreducible
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  refine ⟨e.symm.surjective.irreducibleSpace e.symm.continuous, ?_, ⟨⟩⟩
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans hT

/-- A local-system open is a smooth curve over `ℂ` with connected, locally path connected
complex realization. -/
private lemma isLocalSystemOpen_facts (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) {W : (curveScheme T).Opens}
    (hW : IsLocalSystemOpen sY W) :
    AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) ∧
      SmoothOfRelativeDimension 1 (W.ι ≫ curveι T ≫ sY) ∧
      ConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) ∧
      LocallyPathConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  obtain ⟨hirr, hdim, hnoeth⟩ := curveScheme_facts hY hT
  haveI := hnoeth
  haveI : Smooth (W.ι ≫ curveι T ≫ sY) := hW.smooth
  haveI : ConnectedSpace W := hW.connectedSpace
  haveI : IsIntegral W :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (W.ι ≫ curveι T ≫ sY)
  haveI hV : AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  haveI : Nonempty W := hW.connectedSpace.toNonempty
  obtain ⟨w⟩ := ‹Nonempty W›
  have hdimW : topologicalKrullDim W = 1 :=
    ((AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ (curveScheme T) (curveι T ≫ sY)
      (W : Set (curveScheme T)) W.isOpen ⟨w.1, w.2⟩).symm.trans hdim)
  exact ⟨hV, MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 1 hdimW,
    connectedSpace_analyticSpace _, locallyPathConnectedSpace_analyticSpace _⟩

end CurveTopology

/-! ### Points of complex schemes -/

section PointClass

/-- `Spec ℂ` is a complex scheme. -/
private theorem spec_isComplexScheme : IsComplexScheme (Spec (.of ℂ)) :=
  haveI : IsSmoothVariety ℂ (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    MMP.isSmoothVariety_of_eq_id (MMP.specOverSpec_over_self ℂ)
  IsComplexScheme.of_isSmoothVariety _

/-- The point of `Spec ℂ` has delta-dimension zero. -/
private theorem relativeDimension_spec (x : Spec (.of ℂ)) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (Spec (.of ℂ) ↘ Spec (.of ℂ)) x =
      ((0 : ℕ) : ℤ) := by
  refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ _ x 0 ?_
  have hcl : closure ({x} : Set (Spec (.of ℂ))) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)
  rw [hcl, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum ℂ) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- A point of delta-dimension zero is closed. -/
private theorem isClosed_singleton_of_relativeDimension_eq_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {x : X}
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((0 : ℕ) : ℤ)) : IsClosed ({x} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy ↦ ?_
  by_contra hne
  have hlt := Stacks.Chow.relativeDimension_lt_of_specializes (fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) (specializes_iff_mem_closure.mpr hy) (Ne.symm hne)
  have h0 : (0 : ℤ) ≤ relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) y :=
    Stacks.Chow.relativeDimension_nonneg (fieldChowSituation ℂ) (fun _ _ ↦ rfl)
      (X ↘ Spec (.of ℂ)) y
  have hx' : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = 0 := by exact_mod_cast hx
  omega

/-- A closed point has delta-dimension zero. -/
private theorem relativeDimension_eq_zero_of_isClosed {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((0 : ℕ) : ℤ) := by
  have h1 := Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ (X ↘ Spec (.of ℂ)) x
  rw [hx.closure_eq] at h1
  haveI : Subsingleton ({x} : Set X) := Set.subsingleton_singleton.coe_sort
  have h2 := @topologicalKrullDim_zero_of_discreteTopology ({x} : Set X) _
    Subsingleton.discreteTopology
  rw [h1] at h2
  have h3 : (relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x).toNat ≤ 0 := by exact_mod_cast h2
  have h0 : (0 : ℤ) ≤ relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x :=
    Stacks.Chow.relativeDimension_nonneg (fieldChowSituation ℂ) (fun _ _ ↦ rfl)
      (X ↘ Spec (.of ℂ)) x
  rw [Nat.cast_zero]
  omega

/-- At a closed point of a scheme locally of finite type over `ℂ`, the structure morphism has
residue degree one. -/
private theorem residueDegree_eq_one_of_isClosed {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) : p.residueDegree x = 1 := by
  haveI : Subsingleton (Spec (.of ℂ)) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  haveI := Stacks.Chow.isIso_Γevaluation_of_isIntegral_of_subsingleton (Y := Spec (.of ℂ)) (p x)
  have hf := ConcreteCategory.bijective_of_isIso (C := CommRingCat)
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (Spec (.of ℂ)).Γevaluation (p x))
  have hb := bijective_algebraMap_residueField_of_isClosed p x hx
  rw [RingHom.algebraMap_toAlgebra, ← Scheme.Γevaluation_naturality, ← Category.assoc,
    CommRingCat.hom_comp, RingHom.coe_comp] at hb
  let _ := (p.residueFieldMap x).hom.toAlgebra
  change Module.finrank ((Spec (.of ℂ)).residueField (p.base x)) (X.residueField x) = 1
  exact Module.finrank_of_bijective_algebraMap ((Function.Bijective.of_comp_iff _ hf).1 hb)

end PointClass

/-! ### Degrees of zero-cycle classes -/

section Degree

open Set MMP.borelMooreHomology MMP.SingularChain
  MMP.BorelMooreCross Finsupp in
/-- **Borel–Moore `H_0` of a compact path-connected space** is spanned by one class. -/
private theorem exists_forall_eq_smul_borelMooreHomology_zero {X : TopCat.{0}} [CompactSpace X]
    [PathConnectedSpace X] :
    ∃ v : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) X ((0 : ℕ) : ℤ),
      ∀ z, ∃ c : ℚ, z = c • v := by
  classical
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  have hcyc : ∀ c : (BM ℚ X).X 0, c ∈ Cyc (R := ℚ) X 0 := fun c ↦ by
    rw [mem_cyc_iff, show (0 : ℕ) - 1 = 0 from rfl, (BM ℚ X).shape 0 0 (by simp)]
    rfl
  refine ⟨(homologyEquiv ℚ X 0).symm (Submodule.Quotient.mk
    ⟨ofFinsupp (single (ContinuousMap.const _ x₀ : Simplex X 0) 1), hcyc _⟩), fun z ↦ ?_⟩
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv ℚ X 0 z)
  have hfin : (Function.support w.1.1).Finite := by
    have h := w.1.2.finite_inter_compact isCompact_univ
    refine h.subset fun σ hσ ↦ ⟨hσ, ?_⟩
    obtain ⟨y, hy⟩ := nonempty_singularSimplexImage σ
    exact ⟨y, hy, trivial⟩
  have hfw : ofFinsupp (toFinsupp w.1 hfin) = w.1 := ofFinsupp_toFinsupp _ _
  have hA : ∀ x ∈ (univ : Set X), ∀ y ∈ (univ : Set X), JoinedIn univ x y := fun x _ y _ ↦
    joinedIn_univ.2 (PathConnectedSpace.joined x y)
  obtain ⟨g, -, hg⟩ := reducedZeroVanishing_of_joinedIn (R := ℚ) hA
    (toFinsupp w.1 hfin - aug ℚ 0 (toFinsupp w.1 hfin) •
      single (ContinuousMap.const _ x₀ : Simplex X 0) 1) (by
      rw [inside, Finsupp.mem_supported]; intro σ _; exact fun _ _ ↦ trivial) (by
      rw [map_sub, map_smul, aug_single, smul_eq_mul, mul_one, sub_self])
  refine ⟨aug ℚ 0 (toFinsupp w.1 hfin), (homologyEquiv ℚ X 0).injective ?_⟩
  rw [LinearEquiv.map_smul]
  erw [LinearEquiv.apply_symm_apply]
  rw [← hw]
  change Submodule.Quotient.mk w = Submodule.Quotient.mk ((aug ℚ 0 (toFinsupp w.1 hfin)) •
    (⟨ofFinsupp (single (ContinuousMap.const _ x₀ : Simplex X 0) 1), hcyc _⟩ : Cyc (R := ℚ) X 0))
  refine (Submodule.Quotient.eq _).2 ?_
  refine mem_bdry_of _ (ofFinsupp g) ?_
  rw [d_ofFinsupp, hg, ofFinsupp_sub, hfw]
  rfl

open MMP.UnderlyingSpace MMP.borelMooreHomology

/-- The complex point of `Spec ℂ`. -/
private noncomputable def specComplexPoint : UnderlyingSpace ℂ (Spec (.of ℂ)) :=
  ⟨𝟙 _, by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩

/-- `Spec ℂ` has a single complex point. -/
private theorem subsingleton_underlyingSpace_spec :
    Subsingleton (UnderlyingSpace ℂ (Spec (.of ℂ))) := by
  refine ⟨fun p q ↦ UnderlyingSpace.ext ?_⟩
  have hp := p.toHom_comp_over
  have hq := q.toHom_comp_over
  rw [MMP.specOverSpec_over_self, Category.comp_id] at hp hq
  rw [hp, hq]

/-- The class of the point of `Spec ℂ` in `H_0(Spec ℂ, ℚ)`. -/
private noncomputable def specPointClass :
    MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))) ((2 * 0 : ℕ) : ℤ) :=
  haveI := spec_isComplexScheme
  Chow.pointCycleClass ℚ (IsLocalRing.closedPoint ℂ) (relativeDimension_spec _)

/-- A module with a basis indexed by a type with exactly one element `j₀` is free of rank one on
the basis vector. -/
private theorem bijective_smul_of_linearIndependent_of_span_eq_top {ι M : Type*} [AddCommGroup M]
    [Module ℚ M] (a : ι → M) (v : M) (hli : LinearIndependent ℚ a)
    (hsp : Submodule.span ℚ (Set.range a) = ⊤) (hsub : Subsingleton ι) (j₀ : ι)
    (ha : ∀ j, a j = v) : Function.Bijective fun c : ℚ ↦ c • v := by
  have : Unique ι := uniqueOfSubsingleton j₀
  have h0 : v ≠ 0 := ha default ▸ linearIndependent_unique_iff.1 hli
  refine ⟨smul_left_injective ℚ h0, fun y ↦ ?_⟩
  have hy : y ∈ Submodule.span ℚ (Set.range a) := hsp ▸ Submodule.mem_top
  rw [Set.range_unique, Submodule.mem_span_singleton] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨c, ?_⟩
  rw [← hc, ← ha default]

/-- `H_0(Spec ℂ, ℚ)` is free of rank one on the class of the point: the point is the generic
point of the only irreducible component of `Spec ℂ`, of delta-dimension zero
(`MMP.Chow.linearIndependent_and_span_eq_top_pointCycleClass`). -/
private theorem bijective_smul_specPointClass : Function.Bijective fun c : ℚ ↦ c • specPointClass := by
  haveI := spec_isComplexScheme
  obtain ⟨hli, hsp⟩ := Chow.linearIndependent_and_span_eq_top_pointCycleClass ℚ
    (X := Spec (.of ℂ)) (n := 0) (by
      change topologicalKrullDim (PrimeSpectrum ℂ) ≤ _
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
      simp)
  have hu : ∀ T : Set (Spec (.of ℂ)), T.Nonempty → T = Set.univ := fun T ⟨t, ht⟩ ↦
    Set.eq_univ_of_forall fun u ↦ (Subsingleton.elim u t) ▸ ht
  obtain ⟨u, hu', -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({IsLocalRing.closedPoint ℂ} : Set (Spec (.of ℂ))) isIrreducible_singleton
  refine bijective_smul_of_linearIndependent_of_span_eq_top _ _ hli hsp
    ⟨fun j j' ↦ Subtype.ext (Subtype.ext (by rw [hu _ j.1.2.1.nonempty, hu _ j'.1.2.1.nonempty]))⟩
    ⟨⟨u, hu'⟩, relativeDimension_spec _⟩ fun j ↦ ?_
  have hpt : ∀ (y : Spec (.of ℂ)) (hy : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (Spec (.of ℂ) ↘ Spec (.of ℂ)) y = ((0 : ℕ) : ℤ)),
      Chow.pointCycleClass ℚ y hy = specPointClass := by
    intro y hy
    have hy' : y = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hy'
    rfl
  exact hpt _ _

/-- The degree `H_0(Spec ℂ, ℚ) ≅ ℚ`, normalized on the class of the point. -/
private noncomputable def pointDegree :
    MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ)))) ((2 * 0 : ℕ) : ℤ) →ₗ[ℚ] ℚ :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℚ _ specPointClass)
    bijective_smul_specPointClass).symm.toLinearMap

private theorem pointDegree_specPointClass : pointDegree specPointClass = 1 := by
  change (LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℚ _ specPointClass)
    bijective_smul_specPointClass).symm specPointClass = 1
  rw [LinearEquiv.symm_apply_eq]
  exact (one_smul ℚ _).symm

/-- The map of a compact space to the point `Spec(ℂ)(ℂ)`. -/
private noncomputable def toPointSpace (W : TopCat.{0}) :
    W ⟶ TopCat.of (UnderlyingSpace ℂ (Spec (.of ℂ))) :=
  TopCat.ofHom ⟨fun _ ↦ specComplexPoint, continuous_const⟩

private theorem isProperMap_toPointSpace (W : TopCat.{0}) [CompactSpace W] :
    IsProperMap (toPointSpace W) :=
  (toPointSpace W).hom.continuous.isProperMap

/-- The degree of a `0`-dimensional class on a compact space: its push-forward to a point. -/
private noncomputable def compactDegree (W : TopCat.{0}) [CompactSpace W] :
    MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W ((2 * 0 : ℕ) : ℤ) →ₗ[ℚ] ℚ :=
  pointDegree ∘ₗ (MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
    (toPointSpace W) (isProperMap_toPointSpace W) ((2 * 0 : ℕ) : ℤ)).hom

/-- The degree is invariant under push-forward. -/
private theorem compactDegree_pushforward {W W' : TopCat.{0}} [CompactSpace W] [CompactSpace W']
    (f : W ⟶ W') (hf : IsProperMap f)
    (z : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W ((2 * 0 : ℕ) : ℤ)) :
    compactDegree W' ((MMP.borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf
      ((2 * 0 : ℕ) : ℤ)).hom z) = compactDegree W z := by
  change pointDegree _ = pointDegree _
  haveI := subsingleton_underlyingSpace_spec
  rw [← MMP.borelMooreHomology.pushforward_comp_apply']
  congr 1
  all_goals
    exact congrArg (fun φ ↦ (ModuleCat.Hom.hom φ) z)
      (MMP.borelMooreHomology.pushforward_congr_eq ℚ
        (by ext x : 1; exact Subsingleton.elim _ _) _ _ _)

/-- The complex points of a proper scheme over `ℂ` form a compact space. -/
private theorem compactSpace_analyticSpace_of_isProper {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProper (X ↘ Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    CompactSpace (analyticSpace (X ↘ Spec (.of ℂ))) := by
  have hover : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  haveI : CompactSpace (UnderlyingSpace ℂ X) := by
    refine ⟨?_⟩
    have := (isProperMap_map (K := ℂ) (X ↘ Spec (.of ℂ))).isCompact_preimage
      (isCompact_univ (X := UnderlyingSpace ℂ (Spec (.of ℂ))))
    simpa using this
  exact ComplexPoints.homeomorphUnderlyingSpace.symm.compactSpace

/-- **The degree of a point class is one.** -/
private theorem compactDegree_fundamentalClass {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [IsProper (X ↘ Spec (.of ℂ))]
    [CompactSpace (analyticSpace (X ↘ Spec (.of ℂ)))] (p : X)
    (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) p =
      ((0 : ℕ) : ℤ)) :
    compactDegree (analyticSpace (X ↘ Spec (.of ℂ))) (fundamentalClass p hp) = 1 := by
  have := spec_isComplexScheme
  haveI hover : (X ↘ Spec (.of ℂ)).IsOver (Spec (.of ℂ)) :=
    ⟨by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
  have h := Chow.pushforward_pointCycleClass ℚ (X ↘ Spec (.of ℂ)) p hp
  rw [residueDegree_eq_one_of_isClosed _ p (isClosed_singleton_of_relativeDimension_eq_zero hp),
    Nat.cast_one, one_smul, Chow.pointCycleClassOrZero,
    dif_pos (relativeDimension_spec _)] at h
  change pointDegree ((pushforward ℚ (ModuleCat.of ℚ ℚ) (toPointSpace _) _ _).hom
    ((pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩)
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap _).hom
      (Chow.pointCycleClass ℚ p hp))) = 1
  haveI := subsingleton_underlyingSpace_spec
  rw [← pushforward_comp_apply', pushforward_congr_eq ℚ (g := TopCat.ofHom (map (K := ℂ)
    (X ↘ Spec (.of ℂ)))) (by ext x : 1; exact Subsingleton.elim _ _) _ (isProperMap_map (K := ℂ) _)]
  erw [h]
  have e : (X ↘ Spec (.of ℂ)).base p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  convert pointDegree_specPointClass using 3
  rw [specPointClass]
  congr 1

/-- **A zero-cycle class on a compact path-connected fibre is its degree times a point class.** -/
private theorem eq_compactDegree_smul_fundamentalClass {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [IsProper (X ↘ Spec (.of ℂ))]
    [CompactSpace (analyticSpace (X ↘ Spec (.of ℂ)))]
    [PathConnectedSpace (analyticSpace (X ↘ Spec (.of ℂ)))] (p : X)
    (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) p =
      ((0 : ℕ) : ℤ))
    (z : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (X ↘ Spec (.of ℂ))) ((2 * 0 : ℕ) : ℤ)) :
    z = compactDegree (analyticSpace (X ↘ Spec (.of ℂ))) z • fundamentalClass p hp := by
  obtain ⟨v, hv⟩ := exists_forall_eq_smul_borelMooreHomology_zero
    (X := analyticSpace (X ↘ Spec (.of ℂ)))
  obtain ⟨c₀, hc₀⟩ := hv (fundamentalClass p hp)
  obtain ⟨c, hc⟩ := hv z
  have h1 := compactDegree_fundamentalClass p hp
  rw [hc₀, map_smul, smul_eq_mul] at h1
  rw [hc, map_smul, smul_eq_mul, hc₀]
  erw [smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (compactDegree _ v) c₀, h1, mul_one]

/-- **The class of a closed point of a proper complex scheme is non-zero**: its degree is one. -/
private theorem fundamentalClass_point_ne_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [IsProper (X ↘ Spec (.of ℂ))]
    [CompactSpace (analyticSpace (X ↘ Spec (.of ℂ)))] (p : X)
    (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) p =
      ((0 : ℕ) : ℤ)) :
    fundamentalClass p hp ≠ 0 := fun h ↦ by
  have h1 := compactDegree_fundamentalClass p hp
  erw [h, map_zero] at h1
  exact zero_ne_one h1

end Degree

/-! ### Proper neighbourhood deformations in open subspaces -/

section NeighbourhoodDeformations

open Topology Set

/-- Proper neighbourhood deformations pass to an open subspace containing the set. -/
private theorem hasProperNeighbourhoodDeformations_preimage_val {Y : Type*} [TopologicalSpace Y]
    {U : Set Y} (hU : IsOpen U) {X : Set Y} (hX : HasProperNeighbourhoodDeformations X)
    (hXU : X ⊆ U) : HasProperNeighbourhoodDeformations ((Subtype.val : U → Y) ⁻¹' X) := by
  intro M hM
  have hemb : IsOpenEmbedding (Subtype.val : U → Y) := hU.isOpenEmbedding_subtypeVal
  have hM' : Subtype.val '' M ∈ 𝓝ˢ X := by
    rw [mem_nhdsSet_iff_forall] at hM ⊢
    intro x hx
    have := hM ⟨x, hXU hx⟩ hx
    have h2 := hemb.map_nhds_eq ⟨x, hXU hx⟩
    change Subtype.val '' M ∈ 𝓝 ((⟨x, hXU hx⟩ : U) : Y)
    rw [← h2]
    exact Filter.image_mem_map this
  obtain ⟨N, hN, hXN, hNM, r, hr, hrX, G, hG, hG0, hG1, hGX, hGM⟩ := hX _ hM'
  have hNU : N ⊆ U := hNM.trans (by rintro _ ⟨y, -, rfl⟩; exact y.2)
  have hMU : ∀ q, G q ∈ U := fun q ↦ by obtain ⟨y, -, hy⟩ := hGM q; exact hy ▸ y.2
  set NU : Set U := Subtype.val ⁻¹' N with hNUdef
  -- `NU ≃ₜ N`
  have hNUe : ∀ y : NU, (y.1.1 : Y) ∈ N := fun y ↦ y.2
  let eN : NU ≃ₜ N :=
    { toFun := fun y ↦ ⟨y.1.1, y.2⟩
      invFun := fun y ↦ ⟨⟨y.1, hNU y.2⟩, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let eX : (Subtype.val ⁻¹' X : Set U) ≃ₜ X :=
    { toFun := fun y ↦ ⟨y.1.1, y.2⟩
      invFun := fun y ↦ ⟨⟨y.1, hXU y.2⟩, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨NU, hN.preimage continuous_subtype_val, ?_, ?_, ⟨eX.symm ∘ r ∘ eN, by fun_prop⟩, ?_, ?_,
    ⟨fun q ↦ ⟨G (eN q.1, q.2), hMU _⟩, by fun_prop⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact preimage_interior_subset_interior_preimage continuous_subtype_val (hXN hx)
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hNM hy
    rwa [Subtype.val_injective hzy] at hz
  · exact eX.symm.isProperMap.comp (hr.comp eN.isProperMap)
  · intro y hy
    exact Subtype.ext (hrX (eN y) hy)
  · refine isProperMap_of_comp_of_inj (g := (Subtype.val : U → Y)) (by fun_prop)
      continuous_subtype_val ?_ Subtype.val_injective
    exact hG.comp ((eN.prodCongr (Homeomorph.refl unitInterval)).isProperMap)
  · intro y; exact Subtype.ext (hG0 (eN y))
  · intro y; exact Subtype.ext (hG1 (eN y))
  · intro y t hy; exact Subtype.ext (hGX (eN y) t hy)
  · intro q
    obtain ⟨z, hz, hzq⟩ := hGM (eN q.1, q.2)
    have he : z = (⟨G (eN q.1, q.2), hMU _⟩ : U) := Subtype.ext hzq
    change (⟨G (eN q.1, q.2), hMU _⟩ : U) ∈ M
    rw [← he]
    exact hz

private theorem isProperMap_of_isEmpty' {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [IsEmpty A] (f : A → B) (hf : Continuous f) : IsProperMap f :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2 ⟨hf, fun s _ ↦ by
    rw [Set.eq_empty_of_isEmpty s, Set.image_empty]; exact isClosed_empty, fun y ↦ by
    rw [Set.eq_empty_of_isEmpty (f ⁻¹' {y})]; exact isCompact_empty⟩

/-- The empty set has arbitrarily small proper neighbourhood deformations. -/
private theorem hasProperNeighbourhoodDeformations_empty {Y : Type*} [TopologicalSpace Y] :
    HasProperNeighbourhoodDeformations (∅ : Set Y) := by
  intro M _
  refine ⟨∅, isClosed_empty, by simp, empty_subset _, ⟨fun y ↦ absurd y.2 (notMem_empty _),
    continuous_of_const fun y ↦ absurd y.2 (notMem_empty _)⟩, ?_, fun y ↦ absurd y.2 (notMem_empty _),
    ⟨fun q ↦ absurd q.1.2 (notMem_empty _), continuous_of_const fun q ↦ absurd q.1.2 (notMem_empty _)⟩,
    ?_, fun y ↦ absurd y.2 (notMem_empty _), fun y ↦ absurd y.2 (notMem_empty _),
    fun y ↦ absurd y.2 (notMem_empty _), fun q ↦ absurd q.1.2 (notMem_empty _)⟩
  · haveI : IsEmpty (∅ : Set Y) := Set.isEmpty_coe_sort.2 rfl
    exact isProperMap_of_isEmpty' _ (ContinuousMap.continuous _)
  · haveI : IsEmpty (∅ : Set Y) := Set.isEmpty_coe_sort.2 rfl
    haveI : IsEmpty ((∅ : Set Y) × unitInterval) := inferInstance
    exact isProperMap_of_isEmpty' _ (ContinuousMap.continuous _)

/-- The trace of a point on an open subspace has arbitrarily small proper neighbourhood
deformations, if the point has. -/
private theorem hasProperNeighbourhoodDeformations_inclHom_preimage_singleton {B : TopCat.{0}}
    (Q : TopologicalSpace.Opens B) {y : B} (hy : HasProperNeighbourhoodDeformations ({y} : Set B)) :
    HasProperNeighbourhoodDeformations
      ((MMP.borelMooreHomology.inclHom Q).hom ⁻¹' {y}) := by
  by_cases h : y ∈ Q
  · exact hasProperNeighbourhoodDeformations_preimage_val Q.isOpen hy
      (Set.singleton_subset_iff.2 h)
  · have he : (MMP.borelMooreHomology.inclHom Q).hom ⁻¹' {y} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ h (hx ▸ x.2)
    rw [he]
    exact hasProperNeighbourhoodDeformations_empty

/-- Bases of open contractible neighbourhoods pull back along open embeddings. -/
private theorem hasOpenContractibleBasis_of_isOpenEmbedding' {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : HasOpenContractibleBasis X) {e : Y → X} (he : IsOpenEmbedding e) :
    HasOpenContractibleBasis Y := by
  intro y
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨V, ⟨hV, hyV, _⟩, hVt⟩ ↦
    Filter.mem_of_superset (hV.mem_nhds hyV) hVt⟩⟩
  obtain ⟨V, ⟨hV, hyV, hc⟩, hVt⟩ := (h (e y)).mem_iff.1 (he.image_mem_nhds.2 ht)
  have hVr : V ⊆ range e := hVt.trans (image_subset_range _ _)
  refine ⟨e ⁻¹' V, ⟨hV.preimage he.continuous, hyV, ?_⟩, fun z hz ↦ ?_⟩
  · exact ((he.isEmbedding.homeomorphImage (e ⁻¹' V)).trans
      (Homeomorph.setCongr (image_preimage_eq_of_subset hVr))).contractibleSpace
  · obtain ⟨w, hw, hwz⟩ := hVt hz
    rwa [← he.injective hwz]

/-- An open subset of a space with a closed embedding into a Euclidean space has a closed
embedding into a Euclidean space: add the inverse distance to the complement as a coordinate. -/
private theorem exists_isClosedEmbedding_of_isOpen {Y : Type*} [TopologicalSpace Y] {N : ℕ}
    {F : Y → EuclideanSpace ℝ (Fin N)} (hF : IsClosedEmbedding F) {U : Set Y} (hU : IsOpen U) :
    ∃ G : U → EuclideanSpace ℝ (Fin (N + 1)), IsClosedEmbedding G := by
  let e : (EuclideanSpace ℝ (Fin N) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (N + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  suffices ∃ G : U → EuclideanSpace ℝ (Fin N) × ℝ, IsClosedEmbedding G by
    obtain ⟨G, hG⟩ := this
    exact ⟨e ∘ G, e.toHomeomorph.isClosedEmbedding.comp hG⟩
  set C : Set (EuclideanSpace ℝ (Fin N)) := F '' Uᶜ with hC
  have hCcl : IsClosed C := hF.isClosedMap _ hU.isClosed_compl
  have hFU : ∀ x : U, F x ∉ C := fun x ⟨y, hy, hyx⟩ ↦ hy (hF.injective hyx ▸ x.2)
  by_cases hne : C.Nonempty
  · have hd : ∀ x : U, Metric.infDist (F x) C ≠ 0 := fun x h ↦
      hFU x ((hCcl.mem_iff_infDist_zero hne).2 h)
    refine ⟨fun x ↦ (F x, (Metric.infDist (F x) C)⁻¹), ?_⟩
    have hcont : Continuous fun x : U ↦ (F x, (Metric.infDist (F x) C)⁻¹) :=
      (hF.continuous.comp continuous_subtype_val).prodMk
        (((Metric.continuous_infDist_pt C).comp
          (hF.continuous.comp continuous_subtype_val)).inv₀ hd)
    have hind : IsInducing fun x : U ↦ (F x, (Metric.infDist (F x) C)⁻¹) :=
      IsInducing.of_comp hcont continuous_fst (hF.isInducing.comp IsInducing.subtypeVal)
    refine ⟨⟨hind, fun x y h ↦ Subtype.ext (hF.injective (congrArg Prod.fst h))⟩, ?_⟩
    have hrange : Set.range (fun x : U ↦ (F x, (Metric.infDist (F x) C)⁻¹)) =
        {q | q.1 ∈ Set.range F ∧ q.2 * Metric.infDist q.1 C = 1} := by
      ext q
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨⟨x, rfl⟩, inv_mul_cancel₀ (hd x)⟩
      · rintro ⟨⟨y, hy⟩, hq⟩
        have hyd : Metric.infDist (F y) C ≠ 0 := by
          rw [hy]; intro h; rw [h, mul_zero] at hq; exact zero_ne_one hq
        have hyU : y ∈ U := by
          by_contra h'
          exact hyd ((Metric.infDist_zero_of_mem ⟨y, h', rfl⟩))
        refine ⟨⟨y, hyU⟩, Prod.ext hy ?_⟩
        change (Metric.infDist (F y) C)⁻¹ = q.2
        rw [hy] at hyd ⊢
        exact (eq_inv_of_mul_eq_one_left hq).symm
    rw [hrange]
    exact (hF.isClosed_range.preimage continuous_fst).inter
      (isClosed_eq (continuous_snd.mul ((Metric.continuous_infDist_pt C).comp continuous_fst))
        continuous_const)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hUu : U = Set.univ := by
      by_contra h
      obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem U).1 h
      exact (Set.eq_empty_iff_forall_notMem.1 hne) (F y) ⟨y, hy, rfl⟩
    refine ⟨fun x ↦ (F x, 1), ?_⟩
    have hcont : Continuous fun x : U ↦ (F x, (1 : ℝ)) :=
      (hF.continuous.comp continuous_subtype_val).prodMk continuous_const
    refine ⟨⟨IsInducing.of_comp hcont continuous_fst (hF.isInducing.comp IsInducing.subtypeVal),
      fun x y h ↦ Subtype.ext (hF.injective (congrArg Prod.fst h))⟩, ?_⟩
    have hrange : Set.range (fun x : U ↦ (F x, (1 : ℝ))) = Set.range F ×ˢ {1} := by
      ext q
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨⟨x, rfl⟩, rfl⟩
      · rintro ⟨⟨y, hy⟩, hq⟩
        exact ⟨⟨y, hUu ▸ Set.mem_univ y⟩, Prod.ext hy hq.symm⟩
    rw [hrange]
    exact hF.isClosed_range.prod isClosed_singleton

/-- **Proper neighbourhood deformations in an open subspace** (Fulton's setting, §19.1): for a
space `Y` with bases of open contractible neighbourhoods and a closed embedding into a Euclidean
space, an open `U ⊆ Y` and a closed `X ⊆ Y` with bases of open contractible neighbourhoods,
`X ∩ U` has arbitrarily small proper neighbourhood deformations in `U`. -/
private theorem hasProperNeighbourhoodDeformations_preimage_val_of_isOpen {Y : Type*}
    [TopologicalSpace Y] {N : ℕ} {F : Y → EuclideanSpace ℝ (Fin N)} (hF : IsClosedEmbedding F)
    (hYc : HasOpenContractibleBasis Y) {U : Set Y} (hU : IsOpen U) {X : Set Y} (hX : IsClosed X)
    (hXc : HasOpenContractibleBasis X) :
    HasProperNeighbourhoodDeformations ((Subtype.val : U → Y) ⁻¹' X) := by
  obtain ⟨G, hG⟩ := exists_isClosedEmbedding_of_isOpen hF hU
  refine hasProperNeighbourhoodDeformations_of_isClosedEmbedding hG
    (hX.preimage continuous_subtype_val) ?_
    (hasOpenContractibleBasis_of_isOpenEmbedding' hYc hU.isOpenEmbedding_subtypeVal)
  refine hasOpenContractibleBasis_of_isOpenEmbedding' hXc
    (e := fun x : ((Subtype.val : U → Y) ⁻¹' X) ↦ (⟨x.1.1, x.2⟩ : X)) ?_
  have hemb : IsEmbedding fun x : ((Subtype.val : U → Y) ⁻¹' X) ↦ (⟨x.1.1, x.2⟩ : X) :=
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict X fun x ↦ x.2
  refine ⟨hemb, ?_⟩
  have : Set.range (fun x : ((Subtype.val : U → Y) ⁻¹' X) ↦ (⟨x.1.1, x.2⟩ : X)) =
      Subtype.val ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.1.2
    · intro hx; exact ⟨⟨⟨x.1, hx⟩, x.2⟩, rfl⟩
  rw [this]
  exact hU.preimage continuous_subtype_val

end NeighbourhoodDeformations

/-! ### Local constancy of the degree of a specialization -/

section SpecializationDegree

open MMP.borelMooreHomology Topology

/-- A fibre of the inclusion of a subset is a subsingleton, hence compact. -/
private theorem compactSpace_preimage_singleton_inclHom {B : TopCat.{0}}
    (Q : TopologicalSpace.Opens B) (s : B) :
    CompactSpace ((inclHom Q).hom ⁻¹' {s}) := by
  have hsub : ((inclHom Q).hom ⁻¹' {s} : Set (TopCat.of Q)).Subsingleton := fun x hx y hy ↦
    Subtype.ext (hx.trans hy.symm)
  haveI : Finite ((inclHom Q).hom ⁻¹' {s}) := hsub.finite.to_subtype
  infer_instance

/-- **The degree of the specialization of a class on an open subset of an oriented manifold is
locally constant** (Fulton, Lemma 19.2(c), for the trivial family `Q → Q`). For an open subset
`Q` of an oriented manifold `B`, a class `ν ∈ H_n(Q)` and local orientation classes `u_s`,
the degree of `u_s ∩ ν ∈ H_0({s})` does not depend on `s` near a point of `Q`. -/
private theorem eventually_compactDegree_capProductSupportPullback_eq {B : TopCat.{0}}
    [T2Space B] [LocallyConnectedSpace B] [T5Space B] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H B] (hB : IsOrientedAtlas H B)
    {n : ℕ} (hn : 0 < n) (b : Module.Basis (Fin n) ℝ H) (Q : TopologicalSpace.Opens B)
    (hd : ∀ s : B, HasProperNeighbourhoodDeformations ((inclHom Q).hom ⁻¹' {s}))
    (ν : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of Q) n)
    {s₀ : B} (hs₀ : s₀ ∈ Q) (u₀ : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) B {s₀} n)
    (hu₀ : IsLocalOrientationClass ℚ b s₀ u₀) :
    ∀ᶠ s in 𝓝 s₀, ∀ u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) B {s} n,
      IsLocalOrientationClass ℚ b s u →
      @compactDegree (TopCat.of ((inclHom Q).hom ⁻¹' {s}))
          (compactSpace_preimage_singleton_inclHom Q s)
          (BorelMooreCross.congrDegree ℚ _ (by simp)
            (capProductSupportPullback ℚ (inclHom Q) isClosed_singleton (hd s) n n u ν)) =
        @compactDegree (TopCat.of ((inclHom Q).hom ⁻¹' {s₀}))
          (compactSpace_preimage_singleton_inclHom Q s₀)
          (BorelMooreCross.congrDegree ℚ _ (by simp)
            (capProductSupportPullback ℚ (inclHom Q) isClosed_singleton (hd s₀) n n u₀ ν)) := by
  set W := connectedComponentIn (Q : Set B) s₀ with hWdef
  have hWo : IsOpen W := Q.isOpen.connectedComponentIn
  have hs₀W : s₀ ∈ W := mem_connectedComponentIn hs₀
  have hWQ : W ⊆ Q := connectedComponentIn_subset _ _
  filter_upwards [hWo.mem_nhds hs₀W] with s hsW u hu
  set W' : TopologicalSpace.Opens B := ⟨W, hWo⟩
  haveI : ConnectedSpace W' :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponentIn_iff.2 hs₀)
  let ψ : TopCat.of PUnit.{1} × W' ≃ₜ MMP.Fourfold.preimageOpens (inclHom Q) W' :=
    { toFun := fun p ↦ ⟨⟨p.2.1, hWQ p.2.2⟩, p.2.2⟩
      invFun := fun q ↦ (PUnit.unit, ⟨q.1.1, q.2⟩)
      left_inv := fun p ↦ by rcases p with ⟨⟨⟩, w⟩; rfl
      right_inv := fun q ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hψ : ∀ p, (inclHom Q) (ψ p : TopCat.of Q) = (p.2 : B) := fun _ ↦ rfl
  have key := MMP.Fourfold.pushforward_fibreTransportHom_capProductSupportPullback_eq_of_isLocalOrientationClass
    (R := ℚ) (X := TopCat.of PUnit.{1}) (P := TopCat.of Q) (g := inclHom Q) (W := W') hB hn b ψ hψ
    hd n ν hsW hs₀W hu hu₀
  have hdeg := congrArg (fun z ↦ compactDegree (TopCat.of PUnit.{1})
    (BorelMooreCross.congrDegree ℚ _ (by simp : (n : ℤ) - n = ((2 * 0 : ℕ) : ℤ)) z)) key
  simp only at hdeg
  haveI := compactSpace_preimage_singleton_inclHom Q s
  haveI := compactSpace_preimage_singleton_inclHom Q s₀
  rw [← pushforward_congrDegree_comm, ← pushforward_congrDegree_comm, compactDegree_pushforward,
    compactDegree_pushforward] at hdeg
  exact hdeg

end SpecializationDegree

/-! ### The degree of a specialization against a cohomology class -/

section SpecializationCap

open MMP.borelMooreHomology Set

/-- Equal classes up to a transport of degrees have equal degrees. -/
private theorem compactDegree_congrDegree_congr {W : TopCat.{0}} [CompactSpace W] {d d' : ℤ}
    (h : d = ((2 * 0 : ℕ) : ℤ)) (h' : d' = ((2 * 0 : ℕ) : ℤ))
    (a : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W d)
    (b : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W d')
    (hab : a = BorelMooreCross.congrDegree ℚ W (h'.trans h.symm) b) :
    compactDegree W (BorelMooreCross.congrDegree ℚ W h a) =
      compactDegree W (BorelMooreCross.congrDegree ℚ W h' b) := by
  subst hab
  rw [congrDegree_congrDegree]

/-- The degree is invariant under push-forward, through a transport of degrees. -/
private theorem compactDegree_congrDegree_pushforward {W W' : TopCat.{0}} [CompactSpace W]
    [CompactSpace W'] (p : W ⟶ W') (hp : IsProperMap p) {d : ℤ} (h : d = ((2 * 0 : ℕ) : ℤ))
    (z : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W d) :
    compactDegree W' (BorelMooreCross.congrDegree ℚ W' h
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) p hp d).hom z)) =
      compactDegree W (BorelMooreCross.congrDegree ℚ W h z) := by
  rw [← pushforward_congrDegree_comm, compactDegree_pushforward]

/-- The pullback of absolute classes, `H^j(Y) → H^j(X)`. -/
private noncomputable abbrev absPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (j : ℤ) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j →ₗ[ℚ]
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X univ j :=
  (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ j).hom

private theorem absPullback_comp {X Y W : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (j : ℤ)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) W univ j) :
    absPullback (f ≫ g) j c = absPullback f j (absPullback g j c) := by
  simp only [absPullback, cohomologyWithSupports.pullback_comp]
  rfl

private theorem hasProperNeighbourhoodDeformations_of_eq_univ {W : Type*} [TopologicalSpace W]
    {A : Set W} (h : A = univ) : HasProperNeighbourhoodDeformations A :=
  h ▸ hasProperNeighbourhoodDeformations_univ W

/-- The projection formula for absolute classes. -/
private theorem pushforward_capProduct_absPullback {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : IsProperMap f) (j k : ℤ) (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y univ j)
    (a : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) X k) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) f hf (k - j)).hom
        (capProduct ℚ X univ j k (absPullback f j c) a) =
      capProduct ℚ Y univ j k c ((pushforward ℚ (ModuleCat.of ℚ ℚ) f hf k).hom a) :=
  pushforward_capProduct_pullback ℚ f hf isClosed_univ (hasProperNeighbourhoodDeformations_univ Y)
    (hasProperNeighbourhoodDeformations_of_eq_univ Set.preimage_univ) j k c a

/-- **Pairing a specialized class with a cohomology class, read on the base.** Let `g : P → B` be
proper, `Q ⊆ B` open, `y ∈ Q`, `O = g⁻¹(Q)` and `g_Q : O → Q` the restriction. For a class
`β ∈ H_4(P)`, a local class `u ∈ H^2(B, B - y)`, a proper map `f : g⁻¹(y) → F` to a compact space
and classes `γ_F ∈ H^2(F)`, `γ_O ∈ H^2(O)` with the same pullback to `g⁻¹(y)`, the degree of
`γ_F ∩ f_*(u ∩ β)` is the degree of `u ∩ g_{Q*}(γ_O ∩ β|_O)`: both are the degree of
`u ∩ (γ_O ∩ β|_O)` (Fulton, §19.1: projection formulas, restriction to `O`, and the exchange of
the two cap products). -/
private theorem compactDegree_capProduct_pushforward_eq {P Bb F : TopCat.{0}} [T5Space P]
    [T2Space Bb] [CompactSpace F] (g : P ⟶ Bb) (hg : IsProperMap g)
    (Q : TopologicalSpace.Opens Bb) {y : Bb} (hy : y ∈ Q) [CompactSpace (g ⁻¹' {y})]
    (hdP : HasProperNeighbourhoodDeformations (g ⁻¹' {y}))
    (hdO : HasProperNeighbourhoodDeformations
      ((inclHom (MMP.Fourfold.preimageOpens g Q)).hom ⁻¹' (g ⁻¹' {y})))
    (hdQ : HasProperNeighbourhoodDeformations ((inclHom Q).hom ⁻¹' {y}))
    (f : TopCat.of (g ⁻¹' {y}) ⟶ F) (hf : IsProperMap f)
    (γF : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) F univ 2)
    (γO : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (MMP.Fourfold.preimageOpens g Q)) univ 2)
    (hγ : (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f univ 2).hom γF =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨fun x : g ⁻¹' {y} ↦ (⟨x.1, show g x.1 ∈ Q from
          (Set.mem_singleton_iff.1 x.2).symm ▸ hy⟩ : MMP.Fourfold.preimageOpens g Q),
          by fun_prop⟩ : TopCat.of (g ⁻¹' {y}) ⟶ TopCat.of (MMP.Fourfold.preimageOpens g Q))
        univ 2).hom γO)
    (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Bb {y} 2)
    (β : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) P 4) :
    compactDegree F (BorelMooreCross.congrDegree ℚ F (by norm_num)
        (capProduct ℚ F univ 2 (4 - 2) γF ((pushforward ℚ (ModuleCat.of ℚ ℚ) f hf (4 - 2)).hom
            (capProductSupportPullback ℚ g isClosed_singleton hdP 2 4 u β)))) =
      @compactDegree (TopCat.of ((inclHom Q).hom ⁻¹' {y}))
        (compactSpace_preimage_singleton_inclHom Q y)
        (BorelMooreCross.congrDegree ℚ _ (by norm_num)
          (capProductSupportPullback ℚ (inclHom Q) isClosed_singleton hdQ 2 (4 - 2) u
            ((pushforward ℚ (ModuleCat.of ℚ ℚ) (restrictPreimage g Q)
              (isProperMap_restrictPreimage g Q hg) (4 - 2)).hom
              (capProduct ℚ _ univ 2 4 γO
                ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β))))) := by
  classical
  have hFibcl : IsClosed (g ⁻¹' {y}) := isClosed_singleton.preimage g.hom.continuous
  set e : TopCat.of (g ⁻¹' {y}) ⟶ TopCat.of (MMP.Fourfold.preimageOpens g Q) := TopCat.ofHom ⟨fun x : g ⁻¹' {y} ↦ (⟨x.1, show g x.1 ∈ Q from
    (Set.mem_singleton_iff.1 x.2).symm ▸ hy⟩ : MMP.Fourfold.preimageOpens g Q), by fun_prop⟩ with he
  set z := capProductSupportPullback ℚ g isClosed_singleton hdP 2 4 u β with hz
  -- Step A: the projection formula along `f`
  have hA := pushforward_capProduct_absPullback f hf 2 (4 - 2) γF z
  rw [← hA, compactDegree_congrDegree_pushforward]
  change compactDegree _ (BorelMooreCross.congrDegree ℚ _ _
    (capProduct ℚ _ univ 2 (4 - 2) (absPullback f 2 γF) z)) = _
  rw [show absPullback f 2 γF = absPullback e 2 γO from hγ]
  -- Step B: restrict to the open set `g⁻¹(y) ∩ O = g⁻¹(y)`
  set OI := opensInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}) with hOIdef
  have hOI : OI = ⊤ := eq_top_iff.2 fun x _ ↦
    show g x.1 ∈ Q from (Set.mem_singleton_iff.1 x.2).symm ▸ hy
  have hOIcl : IsClosed (OI : Set (TopCat.of (g ⁻¹' {y}))) := by
    rw [hOI, TopologicalSpace.Opens.coe_top]; exact isClosed_univ
  have hιTp : IsProperMap (inclHom OI) :=
    (Topology.IsClosedEmbedding.subtypeVal (by rw [hOI]; exact isClosed_univ)).isProperMap
  haveI : CompactSpace (TopCat.of OI) := isCompact_iff_compactSpace.1 hOIcl.isCompact
  have hzr := pushforward_inclHom_restrict_of_eq_top ℚ hOI hιTp (4 - 2) z
  have hB1 := pushforward_capProduct_absPullback (inclHom OI) hιTp 2 (4 - 2) (absPullback e 2 γO)
    ((restrict ℚ (ModuleCat.of ℚ ℚ) OI (4 - 2)).hom z)
  rw [hzr] at hB1
  rw [← hB1, compactDegree_congrDegree_pushforward, ← absPullback_comp]
  -- Step B': read the restricted class on `D = g⁻¹(y) ∩ O ⊆ O`
  have hm : inclHom OI ≫ e = opensInterMap (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}) ≫
      subsetInclusion (setInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y})) := by
    ext x; rfl
  rw [hm, absPullback_comp]
  have hDrange : (setInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}) :
      Set (TopCat.of (MMP.Fourfold.preimageOpens g Q))) = Set.range e := by
    ext x
    constructor
    · intro hx; exact ⟨⟨x.1, hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩; exact a.2
  haveI hDc : CompactSpace (TopCat.of (setInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}))) :=
    isCompact_iff_compactSpace.1 (hDrange ▸ isCompact_range e.hom.continuous)
  have hB2 := pushforward_capProduct_absPullback
    (opensInterMap (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}))
    (isProperMap_opensInterMap _ _) 2 (4 - 2)
    (absPullback (subsetInclusion (setInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}))) 2 γO)
    ((restrict ℚ (ModuleCat.of ℚ ℚ) OI (4 - 2)).hom z)
  rw [← compactDegree_congrDegree_pushforward
    (opensInterMap (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y})) (isProperMap_opensInterMap _ _),
    hB2]
  have hB := pushforward_opensInterMap_restrict_capProductSupport ℚ P
    (MMP.Fourfold.preimageOpens g Q) hFibcl hdP hdO 2 4
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g {y} 2).hom u) β
  rw [show z = capProductSupport ℚ P hFibcl hdP 2 4
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g {y} 2).hom u) β from rfl, hB]
  -- Step C: exchange the two cap products on `O`
  have hDcl : IsClosed ((inclHom (MMP.Fourfold.preimageOpens g Q)).hom ⁻¹' (g ⁻¹' {y})) :=
    hFibcl.preimage (inclHom _).hom.continuous
  have hs : (-1 : ℚˣ) ^ ((2 : ℤ) * 2) = 1 := (by decide : Even ((2 : ℤ) * 2)).neg_one_zpow
  have hC := capProductSupport_capProduct_eq ℚ (TopCat.of (MMP.Fourfold.preimageOpens g Q)) hDcl
    isClosed_univ hdO (hasProperNeighbourhoodDeformations_univ _)
    (by rw [Set.inter_univ]; exact hdO) (by rw [Set.univ_inter]; exact hdO)
    (HasProperNeighbourhoodDeformations.preimage_homeomorph hdO (Homeomorph.Set.univ _))
    (hasProperNeighbourhoodDeformations_of_eq_univ Set.preimage_univ) (n := 2) (j := 2) 4 hs
    ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (inclHom (MMP.Fourfold.preimageOpens g Q))
      (g ⁻¹' {y}) 2).hom ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g {y} 2).hom u))
    γO ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β)
  have hC' : capProduct ℚ (TopCat.of (setInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}))) univ
      2 (4 - 2)
      (absPullback (subsetInclusion (setInter (MMP.Fourfold.preimageOpens g Q) (g ⁻¹' {y}))) 2 γO)
      (capProductSupportPullback ℚ (inclHom (MMP.Fourfold.preimageOpens g Q)) hFibcl hdO 2 4
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g {y} 2).hom u)
        ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β)) =
      BorelMooreCross.congrDegree ℚ _ (by ring)
        (capProductSupport ℚ (TopCat.of (MMP.Fourfold.preimageOpens g Q)) hDcl hdO 2 (4 - 2)
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (inclHom (MMP.Fourfold.preimageOpens g Q)) (g ⁻¹' {y}) 2).hom
            ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g {y} 2).hom u))
          (capProduct ℚ _ univ 2 4 γO
            ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β))) := by
    rw [hC, congrDegree_congrDegree, BorelMooreCross.congrDegree_self]
    rfl
  rw [compactDegree_congrDegree_congr _ (by norm_num) _ _ hC']
  -- Step D: the projection formula along `g_Q`
  have hD1 : capProductSupport ℚ (TopCat.of (MMP.Fourfold.preimageOpens g Q)) hDcl hdO 2 (4 - 2)
      ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (inclHom (MMP.Fourfold.preimageOpens g Q)) (g ⁻¹' {y}) 2).hom
        ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) g {y} 2).hom u))
      (capProduct ℚ _ univ 2 4 γO
        ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β)) =
      capProductSupportPullback ℚ (restrictPreimage g Q ≫ inclHom Q) isClosed_singleton hdO 2 (4 - 2)
        u (capProduct ℚ _ univ 2 4 γO
          ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β)) := by
    change _ = capProductSupportPullback ℚ (inclHom (MMP.Fourfold.preimageOpens g Q) ≫ g)
      isClosed_singleton hdO 2 (4 - 2) u _
    rw [capProductSupportPullback_apply, cohomologyWithSupports.pullback_comp]
    rfl
  rw [hD1]
  have hD2 := MMP.Fourfold.pushforward_preimageRestrictHom_capProductSupportPullback (R := ℚ)
    (isProperMap_restrictPreimage g Q hg) (inclHom Q) (φ := restrictPreimage g Q ≫ inclHom Q) rfl
    isClosed_singleton hdQ hdO 2 (4 - 2) u
    (capProduct ℚ _ univ 2 4 γO
      ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β))
  haveI : CompactSpace (TopCat.of ((restrictPreimage g Q ≫ inclHom Q).hom ⁻¹' {y})) := hDc
  haveI := compactSpace_preimage_singleton_inclHom Q y
  have hfin := compactDegree_congrDegree_pushforward _
    (MMP.Fourfold.isProperMap_preimageRestrictHom (isProperMap_restrictPreimage g Q hg) (inclHom Q)
      (φ := restrictPreimage g Q ≫ inclHom Q) rfl {y}) (by norm_num : (4 : ℤ) - 2 - 2 = ((2 * 0 : ℕ) : ℤ))
    (capProductSupportPullback ℚ (restrictPreimage g Q ≫ inclHom Q) isClosed_singleton hdO 2 (4 - 2)
        u (capProduct ℚ _ univ 2 4 γO
          ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β)))
  rw [hD2] at hfin
  exact hfin.symm

/-- `compactDegree_capProduct_pushforward_eq`, for a map `g⁻¹(y) → F` factored as `h ∘ k` and
the degrees written as they arise from a curve. -/
private theorem compactDegree_capProduct_pushforward_pushforward_eq {P Bb F X' : TopCat.{0}}
    [T5Space P] [T2Space Bb] [CompactSpace F] (g : P ⟶ Bb) (hg : IsProperMap g)
    (Q : TopologicalSpace.Opens Bb) {y : Bb} (hy : y ∈ Q) [CompactSpace (g ⁻¹' {y})]
    (hdP : HasProperNeighbourhoodDeformations (g ⁻¹' {y}))
    (hdO : HasProperNeighbourhoodDeformations
      ((inclHom (MMP.Fourfold.preimageOpens g Q)).hom ⁻¹' (g ⁻¹' {y})))
    (hdQ : HasProperNeighbourhoodDeformations ((inclHom Q).hom ⁻¹' {y}))
    (k : TopCat.of (g ⁻¹' {y}) ⟶ X') (hk : IsProperMap k) (h : X' ⟶ F) (hh : IsProperMap h)
    (γF : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) F univ 2)
    (γO : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (MMP.Fourfold.preimageOpens g Q)) univ 2)
    (hγ : (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (k ≫ h) univ 2).hom γF =
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom ⟨fun x : g ⁻¹' {y} ↦ (⟨x.1, show g x.1 ∈ Q from
          (Set.mem_singleton_iff.1 x.2).symm ▸ hy⟩ : MMP.Fourfold.preimageOpens g Q),
          by fun_prop⟩ : TopCat.of (g ⁻¹' {y}) ⟶ TopCat.of (MMP.Fourfold.preimageOpens g Q))
        univ 2).hom γO)
    (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Bb {y} ((2 * 1 : ℕ) : ℤ))
    (β : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) P ((2 * (1 + 1) : ℕ) : ℤ)) :
    compactDegree F (BorelMooreCross.congrDegree ℚ F (by norm_num)
        (capProduct ℚ F univ 2 2 γF ((pushforward ℚ (ModuleCat.of ℚ ℚ) h hh (2 * 1 : ℕ)).hom
          ((pushforward ℚ (ModuleCat.of ℚ ℚ) k hk (2 * 1 : ℕ)).hom
            (BorelMooreCross.congrDegree ℚ _ (by norm_num)
              (capProductSupportPullback ℚ g isClosed_singleton hdP (2 * 1 : ℕ) (2 * (1 + 1) : ℕ)
                u β)))))) =
      @compactDegree (TopCat.of ((inclHom Q).hom ⁻¹' {y}))
        (compactSpace_preimage_singleton_inclHom Q y)
        (BorelMooreCross.congrDegree ℚ _ (by norm_num)
          (capProductSupportPullback ℚ (inclHom Q) isClosed_singleton hdQ 2 (4 - 2) u
            ((pushforward ℚ (ModuleCat.of ℚ ℚ) (restrictPreimage g Q)
              (isProperMap_restrictPreimage g Q hg) (4 - 2)).hom
              (capProduct ℚ _ univ 2 4 γO
                ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens g Q) 4).hom β))))) := by
  have key := compactDegree_capProduct_pushforward_eq g hg Q hy hdP hdO hdQ (k ≫ h) (hh.comp hk)
    γF γO hγ u β
  refine Eq.trans ?_ key
  rw [pushforward_congrDegree_comm, pushforward_congrDegree_comm,
    ← pushforward_comp_apply' ℚ k h hk hh, capProduct_congrDegree, congrDegree_congrDegree]
  rfl

end SpecializationCap

/-! ### Proper closed subsets of curves -/

section CurveFinite

/-- A proper closed subset of an irreducible set of dimension one in a Noetherian `T₀` space is
finite. -/
private theorem finite_of_isClosed_of_ne {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [T0Space X] {T K : Set X} (hT : IsIrreducible T)
    (hdim : topologicalKrullDim T = 1) (hK : IsClosed K) (hKT : K ⊆ T) (hne : K ≠ T) :
    K.Finite := by
  obtain ⟨S, hS, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hK
  refine Set.Finite.sUnion hS fun Z hZ ↦ ?_
  have hZT : Z ⊆ T := (Set.subset_sUnion_of_mem hZ).trans hKT
  have hZne : Z ≠ T := fun h ↦ hne (Set.Subset.antisymm hKT (h ▸ Set.subset_sUnion_of_mem hZ))
  have hZd := MMP.topologicalKrullDim_lt_of_subset_of_ne hT (hSc Z hZ) hZT hZne
    (by rw [hdim]; decide)
  rw [hdim] at hZd
  refine Set.Subsingleton.finite fun z hz z' hz' ↦ ?_
  have hcl : ∀ y ∈ Z, closure {y} = Z := by
    intro y hy
    by_contra hne'
    have h1 := MMP.topologicalKrullDim_lt_of_subset_of_ne (hSi Z hZ)
      isClosed_closure ((hSc Z hZ).closure_subset_iff.2 (Set.singleton_subset_iff.2 hy)) hne'
      (ne_top_of_lt hZd)
    haveI : Nonempty (IrreducibleCloseds (closure {y} : Set X)) :=
      ⟨⟨closure {⟨y, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have h0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDim (closure {y} : Set X) :=
      Order.krullDim_nonneg
    revert h1 h0
    generalize topologicalKrullDim (closure {y} : Set X) = a
    generalize topologicalKrullDim Z = b at hZd
    intro h1 h0
    induction a using WithBot.recBotCoe with
    | bot => exact absurd h0 (by decide)
    | coe a =>
      induction b using WithBot.recBotCoe with
      | bot => exact absurd h1 (by simp)
      | coe b =>
        have h1' : a < b := by exact_mod_cast h1
        have hb : b < 1 := by exact_mod_cast hZd
        have : b = 0 := by
          induction b using ENat.recTopCoe with
          | top => exact absurd hb (by decide)
          | coe n => norm_cast at hb ⊢; omega
        subst this
        exact absurd h1' (by simp)
  have e1 : IsGenericPoint z Z := hcl z hz
  have e2 : IsGenericPoint z' Z := hcl z' hz'
  exact e1.eq e2

/-- Only finitely many complex points of an open `T° ⊆ T` map into a finite subset of `Y`. -/
private theorem finite_setOf_image_mem {sY : Y ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsVariety ℂ sY)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens} {S : Set Y} (hS : S.Finite) :
    {t : analyticSpace (To.ι ≫ curveι T ≫ sY) |
      (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ S}.Finite := by
  letI : (To : Scheme.{0}).Over (Spec (.of ℂ)) := ⟨To.ι ≫ curveι T ≫ sY⟩
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI : LocallyOfFiniteType ((To : Scheme.{0}) ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (To.ι ≫ curveι T ≫ sY) from inferInstance
  have hinj : Function.Injective fun t : analyticSpace (To.ι ≫ curveι T ≫ sY) ↦
      (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) := by
    intro t t' h
    have h1 : t.hom.base (IsLocalRing.closedPoint ℂ) = t'.hom.base (IsLocalRing.closedPoint ℂ) := by
      have h' : (curveι T).base (To.ι.base (t.hom.base (IsLocalRing.closedPoint ℂ))) =
          (curveι T).base (To.ι.base (t'.hom.base (IsLocalRing.closedPoint ℂ))) := h
      exact To.ι.isOpenEmbedding.injective ((curveι T).isClosedEmbedding.injective h')
    apply (homeomorphUnderlyingSpace (X := (To : Scheme.{0}))).injective
    apply (MMP.UnderlyingSpace.equivClosedPoints (To : Scheme.{0})).injective
    exact Subtype.ext h1
  exact hS.preimage hinj.injOn

/-- All but finitely many complex points of an open `T° ⊆ T` lie in a given nonempty open of the
curve `T`. -/
private theorem eventually_mem_of_isOpen {sY : Y ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsVariety ℂ sY)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} {W : Set (curveScheme T)} (hW : IsOpen W) (hWne : W.Nonempty) :
    ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
      (t.hom ≫ To.ι).base (IsLocalRing.closedPoint ℂ) ∈ W := by
  obtain ⟨hirr, hdT, hnoeth⟩ := curveScheme_facts hY hdim
  haveI := hirr
  haveI := hnoeth
  have hfin : (Wᶜ : Set (curveScheme T)).Finite := by
    refine finite_of_isClosed_of_ne (IrreducibleSpace.isIrreducible_univ _) ?_ hW.isClosed_compl
      (Set.subset_univ _) ?_
    · rw [(Homeomorph.Set.univ (curveScheme T)).isHomeomorph.topologicalKrullDim_eq]
      exact hdT
    · intro h
      obtain ⟨w, hw⟩ := hWne
      exact (h ▸ Set.mem_univ w : w ∈ Wᶜ) hw
  refine Filter.eventually_cofinite.2 ((finite_setOf_image_mem hY (To := To)
    (hfin.image (curveι T).base)).subset fun t ht ↦ ?_)
  exact ⟨_, ht, rfl⟩

end CurveFinite

/-! ### Heights of points -/

section ClosedHeight

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)

include hf in
/-- A closed embedding of schemes preserves heights of points. -/
private theorem height_apply_of_isClosedEmbedding (y : X) :
    Order.height (f y) = Order.height y := by
  have hle : ∀ a b : X, f a ≤ f b ↔ a ≤ b := fun a b ↦ by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes]
    exact hf.isInducing.specializes_iff
  let g : Set.Iic y ↪o Set.Iic (f y) :=
    { toFun := fun z ↦ ⟨f z.1, (hle _ _).2 z.2⟩
      inj' := fun a b h ↦ Subtype.ext (hf.injective (congrArg Subtype.val h))
      map_rel_iff' := fun {a b} ↦ hle a.1 b.1 }
  have hsurj : Function.Surjective g := by
    rintro ⟨w, hw⟩
    have hsp : f y ⤳ w := Scheme.le_iff_specializes.1 hw
    have hmem : w ∈ Set.range f :=
      hsp.mem_closed hf.isClosed_range ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hmem
    exact ⟨⟨z, (hle _ _).1 hw⟩, rfl⟩
  have e := Order.krullDim_eq_of_orderIso (OrderIso.ofSurjective g hsurj)
  rw [← Order.height_eq_krullDim_Iic, ← Order.height_eq_krullDim_Iic] at e
  exact_mod_cast e.symm

end ClosedHeight

section ClosedHeight2

/-- The topological dimension of a scheme is the Krull dimension of its specialization order. -/
private theorem topologicalKrullDim_eq_krullDim' (X : Scheme.{0}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- The generic point of an integral scheme is maximal in the specialization order. -/
private theorem coheight_genericPoint_eq_zero (X : Scheme.{0}) [IsIntegral X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.2 fun _ _ ↦
    (Scheme.le_iff_specializes).2 ((genericPoint_spec X).specializes trivial)

end ClosedHeight2

/-! ### Specialization of curve classes along a family over a curve -/

section FamilySpecialization

open MMP.UnderlyingSpace MMP.borelMooreHomology

variable {X Z : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] [IsComplexScheme X]
  [IsComplexScheme Z]

omit [IsComplexScheme X] [IsComplexScheme Z] in
/-- A closed immersion over `ℂ` preserves delta-dimensions. -/
private theorem relativeDimension_closedImmersion (i : X ⟶ Z) [IsClosedImmersion i]
    [i.IsOver (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (x : X) :
    relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x =
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ))
        (i.base x) := by
  rw [← comp_over i (Spec (.of ℂ))]
  exact Stacks.Chow.relativeDimension_comp_closedImmersion _ i _ x

/-- **Cycle classes along closed immersions.** For a closed immersion `i : X → Z` over `ℂ`, the
push-forward of the cycle class of a point `x` of `X` is the cycle class of `i x`. -/
private theorem pushforward_pointCycleClass_of_isClosedImmersion (i : X ⟶ Z)
    [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))] {k : ℕ} (x : X)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) i)) (isProperMap_map (K := ℂ) i)
        (2 * k : ℕ)).hom (Chow.pointCycleClass ℚ x hx) =
      Chow.pointCycleClass ℚ (i.base x) ((relativeDimension_closedImmersion i x).symm.trans hx) := by
  have h := Chow.pushforward_pointCycleClass ℚ i x hx
  rw [Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul,
    Chow.pointCycleClassOrZero,
    dif_pos ((relativeDimension_closedImmersion i x).symm.trans hx)] at h
  exact h
/-- Along an embedding, the maximal irreducible subsets of `φ(K)` are the images of those of
`K`. -/
private theorem maximal_image_iff {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {φ : A → B}
    (hφ : Topology.IsEmbedding φ) (K S : Set A) :
    Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ φ '' K) (φ '' S) ↔
      Maximal (fun X ↦ IsIrreducible X ∧ X ⊆ K) S := by
  have hinj := hφ.injective
  have himg : ∀ X : Set A, IsIrreducible (φ '' X) ↔ IsIrreducible X := fun X ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ h.image φ hφ.continuous.continuousOn⟩
    have := isIrreducible_preimage_of_isEmbedding' hφ h (Set.image_subset_range _ _)
    rwa [Set.preimage_image_eq _ hinj] at this
  have hsub : ∀ X : Set A, φ '' X ⊆ φ '' K ↔ X ⊆ K := fun X ↦ Set.image_subset_image_iff hinj
  constructor
  · rintro ⟨⟨h1, h2⟩, hmax⟩
    refine ⟨⟨(himg S).1 h1, (hsub S).1 h2⟩, fun X ⟨hX1, hX2⟩ hSX ↦ ?_⟩
    have := hmax ⟨(himg X).2 hX1, (hsub X).2 hX2⟩ (Set.image_mono hSX)
    exact (Set.image_subset_image_iff hinj).1 this
  · rintro ⟨⟨h1, h2⟩, hmax⟩
    refine ⟨⟨(himg S).2 h1, (hsub S).2 h2⟩, fun X ⟨hX1, hX2⟩ hSX ↦ ?_⟩
    have hXr : X ⊆ Set.range φ := hX2.trans (Set.image_subset_range _ _)
    have hX' : X = φ '' (φ ⁻¹' X) := (Set.image_preimage_eq_of_subset hXr).symm
    rw [hX'] at hX1 hX2 hSX ⊢
    exact Set.image_mono (hmax ⟨(himg _).1 hX1, (hsub _).1 hX2⟩
      ((Set.image_subset_image_iff hinj).1 hSX))

/-- **Curves cut on a closed subscheme, read in the ambient scheme.** For a closed immersion
`i : X → Z` over `ℂ` and `K ⊆ X`, the push-forward along `i` of the sum of the cycle classes of
the `k`-dimensional maximal irreducible subsets `closure {x}` of `K` is the sum of the cycle
classes of those of `i(K)`. -/
private theorem pushforward_finsum_maximal (i : X ⟶ Z) [IsClosedImmersion i]
    [i.IsOver (Spec (.of ℂ))] (K : Set X) (k : ℕ) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) i)) (isProperMap_map (K := ℂ) i)
        (2 * k : ℕ)).hom
        (∑ᶠ (x : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
            (X ↘ Spec (.of ℂ)) x = k})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ K) (closure {x.1})),
          Chow.pointCycleClass ℚ x.1 x.2) =
      ∑ᶠ (z : {z : Z // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (Z ↘ Spec (.of ℂ)) z = k})
        (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ i.base '' K) (closure {z.1})),
        Chow.pointCycleClass ℚ z.1 z.2 := by
  classical
  haveI : NoetherianSpace X := noetherianSpace_of_isComplexScheme
  set s := {x : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
    (X ↘ Spec (.of ℂ)) x = k} | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ K) (closure {x.1})}
    with hs
  set t := {z : {z : Z // relativeDimension (fieldChowSituation ℂ).dimensionFunction
    (Z ↘ Spec (.of ℂ)) z = k} |
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ i.base '' K) (closure {z.1})} with ht
  have hsfin : s.Finite := by
    refine Set.Finite.of_finite_image (f := fun x : {x : X // relativeDimension
      (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k} ↦
        closure ({x.1} : Set X)) ((finite_setOf_maximal K).subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · intro x _ x' _ h
      exact Subtype.ext (inseparable_iff_closure_eq.mpr h).eq
  set e : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = k} → {z : Z // relativeDimension
        (fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) z = k} :=
    fun x ↦ ⟨i.base x.1, (relativeDimension_closedImmersion i x.1).symm.trans x.2⟩ with he
  have hemb := i.isClosedEmbedding.isEmbedding
  have hcl : ∀ x : X, closure ({i.base x} : Set Z) = i.base '' closure {x} := fun x ↦ by
    rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq]
  have hbij : Set.BijOn e s t := by
    refine ⟨fun x hx ↦ ?_, fun x _ x' _ h ↦ Subtype.ext (i.isClosedEmbedding.injective
      (congrArg Subtype.val h)), fun z hz ↦ ?_⟩
    · rw [ht, Set.mem_setOf_eq, he]
      dsimp only
      rw [hcl]
      exact (maximal_image_iff hemb K _).2 hx
    · have hzr : closure {z.1} ⊆ Set.range i.base :=
        hz.1.2.trans (Set.image_subset_range _ _)
      obtain ⟨x, hx⟩ := hzr (subset_closure rfl)
      have hxd : relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (X ↘ Spec (.of ℂ)) x = k := by
        rw [relativeDimension_closedImmersion i x, hx]; exact z.2
      refine ⟨⟨x, hxd⟩, ?_, Subtype.ext hx⟩
      rw [hs, Set.mem_setOf_eq]
      dsimp only
      rw [← maximal_image_iff hemb K, ← hcl, hx]
      exact hz
  set φ := (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) i))
    (isProperMap_map (K := ℂ) i) (2 * k : ℕ)).hom with hφ
  have h1 : φ (∑ᶠ x ∈ s, Chow.pointCycleClass ℚ x.1 x.2) =
      ∑ᶠ x ∈ s, φ (Chow.pointCycleClass ℚ x.1 x.2) :=
    AddMonoidHom.map_finsum_mem _ φ.toAddMonoidHom hsfin
  have h2 : ∑ᶠ x ∈ s, φ (Chow.pointCycleClass ℚ x.1 x.2) =
      ∑ᶠ z ∈ t, Chow.pointCycleClass ℚ z.1 z.2 :=
    finsum_mem_eq_of_bijOn e hbij fun x _ ↦
      pushforward_pointCycleClass_of_isClosedImmersion i x.1 x.2
  exact h1.trans h2

section Specialization

variable {B G : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]
  [G.Over (Spec (.of ℂ))] [IsComplexScheme G]

/-- **Specialization of the cycle class of a subvariety along a family over a curve** (Fulton,
Lemma 19.1.3, read in the ambient family). For `g : G → B` over a non-singular complex curve and
a subvariety `V = closure {x} ⊆ G` of dimension `n + 1` dominating `B`, the class of the
scheme-theoretic fibre `V_s`, pushed into `g⁻¹(s)`, is `g^* u_s ∩ cl_G(V)`. -/
private theorem pushforward_fibreAmbientPointsHom_cycleClass_eq_capProductSupportPullback
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ))) (g : G ⟶ B) [g.IsOver (Spec (.of ℂ))]
    {n : ℕ} (x : G)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (G ↘ Spec (.of ℂ)) x =
      ((n + 1 : ℕ) : ℤ))
    [IsDominant ((integralComponentAt x).subschemeι ≫ g)] (s : MMP.ParameterPoint B)
    (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ B))
      {s.complexPoint} (2 * 1 : ℕ))
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) ℚ
      curveOrientationBasis s.complexPoint u) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (fibreAmbientPointsHom (integralComponentAt x).subschemeι g rfl s)
        (isProperMap_fibreAmbientPointsHom (integralComponentAt x).subschemeι g rfl s)
        (2 * n : ℕ)).hom
        (Chow.cycleClass ℚ n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
          (MMP.ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ g) s ↘ Spec (.of ℂ))
          (𝟙 _) n)) =
      BorelMooreCross.congrDegree ℚ _ (by push_cast; ring)
        (capProductSupportPullback ℚ (TopCat.ofHom (map (K := ℂ) g)) isClosed_singleton
          (hasProperNeighbourhoodDeformations_preimage_singleton g _) (2 * 1 : ℕ)
          (2 * (n + 1) : ℕ) u (Chow.pointCycleClass ℚ x hx)) :=
  MMP.Chow.pushforward_cycleClass_fibre_eq_capProductSupportPullback_pointCycleClass ℚ hB g x hx s
    s.complexPoint (MMP.ParameterPoint.complexPoint_toHom_closedPoint s) _ _ (fun _ ↦ rfl) _ u hu

open Classical in
/-- **The class of a closed subscheme whose components have multiplicity one.** For a closed
immersion `j : W ⟶ X` whose `n`-dimensional components have multiplicity one, the class of the
`n`-dimensional part `[j(W)]_n` of the fundamental cycle of `W` (Stacks, Tag 02QU) is the sum of
the cycle classes `cl_X(x)` of the maximal irreducible subsets `closure {x}` of `j(W)`. -/
private theorem cycleClass_cycleAssociatedToClosedSubscheme_eq_finsum {X W : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (j : W ⟶ X) [IsClosedImmersion j] {n : ℕ}
    (hmult : ∀ ξ : genericPoints W, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (j.base ξ.1) = n → componentMultiplicity j ξ = 1) :
    Chow.cycleClass ℚ n (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ)
        (X ↘ Spec (.of ℂ)) j n) =
      ∑ᶠ (x : {x : X // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (X ↘ Spec (.of ℂ)) x = n})
        (_ : Maximal (fun A : Set X ↦ IsIrreducible A ∧ A ⊆ Set.range j.base) (closure {x.1})),
        Chow.pointCycleClass ℚ x.1 x.2 := by
  set α := cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) j (n : ℤ)
  have hS := Chow.finite_support_cycle α
  have hval : ∀ x : X, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = n →
      α.1 x = if ∃ ξ : genericPoints W, j.base ξ.1 = x then 1 else 0 := by
    intro x hx
    split_ifs with h
    · obtain ⟨ξ, rfl⟩ := h
      rw [Stacks.Chow.cycleAssociatedToClosedSubscheme_apply (fieldChowSituation ℂ) _ j _ ξ hx,
        hmult ξ hx]
    · exact Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ j _ x
        fun ⟨ξ, hξ, _⟩ ↦ h ⟨ξ, hξ⟩
  have hdim : ∀ x ∈ hS.toFinset, relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = n := fun x hx ↦
    (Stacks.Chow.mem_cyclesOfDimension_iff_forall_point (fieldChowSituation ℂ) _ _ α.1).mp α.2 x
      (hS.mem_toFinset.mp hx)
  rw [Chow.cycleClass_eq_sum,
    finsum_cond_eq_sum_of_cond_iff _ (t := hS.toFinset.subtype fun x ↦
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n)
      fun {x} _ ↦ by
        rw [MMP.Fourfold.maximal_closure_singleton_iff_exists_genericPoints, Finset.mem_subtype,
          hS.mem_toFinset, Function.mem_support, hval x.1 x.2]
        split_ifs with h
        · exact iff_of_true h one_ne_zero
        · exact iff_of_false h fun h' ↦ h' rfl]
  rw [show (∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n,
        Chow.pointCycleClass ℚ x.1 x.2) =
      ∑ x ∈ hS.toFinset.subtype fun x ↦
        relativeDimension (fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = n,
        Chow.pointCycleClassOrZero ℚ n x.1 from
      Finset.sum_congr rfl fun x _ ↦ by rw [Chow.pointCycleClassOrZero, dif_pos x.2],
    Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hdim]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hne : α.1 x ≠ 0 := hS.mem_toFinset.mp hx
  rw [hval x (hdim x hx)] at hne ⊢
  rw [if_pos (by by_contra h; exact hne (if_neg h)), one_smul]

/-- **The specialized class of a subvariety, read in an ambient scheme.** In the setting of
`pushforward_fibreAmbientPointsHom_cycleClass_eq_capProductSupportPullback`, let
`i : V_s → Zs` be a closed immersion over `ℂ` and `k : g⁻¹(s) → Zs(ℂ)` a proper map with
`k ∘ (V_s(ℂ) → g⁻¹(s)) = i`, and let the curve components of `V_s` have multiplicity one. Then
`g^* u_s ∩ cl_G(V)`, carried to `Zs` along `k`, is the sum of the classes of the curves of `Zs`
that are maximal irreducible in the image of `i`. -/
private theorem pushforward_capProductSupportPullback_eq_finsum
    (hB : SmoothOfRelativeDimension 1 (B ↘ Spec (.of ℂ)))
    (g : G ⟶ B) [g.IsOver (Spec (.of ℂ))] {Zs : Scheme.{0}} [Zs.Over (Spec (.of ℂ))]
    [IsComplexScheme Zs] (s : MMP.ParameterPoint B)
    (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ B))
      {s.complexPoint} (2 * 1 : ℕ))
    (hu : IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ B)) ℚ
      curveOrientationBasis s.complexPoint u)
    (x : G)
    (hx : relativeDimension (fieldChowSituation ℂ).dimensionFunction (G ↘ Spec (.of ℂ)) x =
      ((1 + 1 : ℕ) : ℤ))
    [IsDominant ((integralComponentAt x).subschemeι ≫ g)]
    (i : MMP.ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ g) s ⟶ Zs)
    [IsClosedImmersion i] [i.IsOver (Spec (.of ℂ))]
    (k : TopCat.of ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {s.complexPoint}) ⟶
      TopCat.of (UnderlyingSpace ℂ Zs)) (hk : IsProperMap k)
    (hki : fibreAmbientPointsHom (integralComponentAt x).subschemeι g rfl s ≫ k =
      TopCat.ofHom (map (K := ℂ) i))
    (hmult : ∀ ξ : genericPoints
        (MMP.ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ g) s),
      relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (MMP.ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ g) s ↘ Spec (.of ℂ))
        ξ.1 = (1 : ℕ) →
      componentMultiplicity (𝟙 _) ξ = 1) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) k hk (2 * 1 : ℕ)).hom
        (BorelMooreCross.congrDegree ℚ _ (by norm_num)
          (capProductSupportPullback ℚ (TopCat.ofHom (map (K := ℂ) g)) isClosed_singleton
            (hasProperNeighbourhoodDeformations_preimage_singleton g _) (2 * 1 : ℕ)
            (2 * (1 + 1) : ℕ) u (Chow.pointCycleClass ℚ x hx))) =
      ∑ᶠ (z : {z : Zs // relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (Zs ↘ Spec (.of ℂ)) z = (1 : ℕ)})
        (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Set.range i.base) (closure {z.1})),
        Chow.pointCycleClass ℚ z.1 z.2 := by
  rw [← pushforward_fibreAmbientPointsHom_cycleClass_eq_capProductSupportPullback hB g x hx s u
    hu, ← pushforward_comp_apply',
    pushforward_congr_eq ℚ hki _ (isProperMap_map (K := ℂ) _),
    cycleClass_cycleAssociatedToClosedSubscheme_eq_finsum (𝟙 _) (fun ξ hξ ↦ hmult ξ hξ)]
  rw [pushforward_finsum_maximal]
  have hK : i.base '' Set.range
      (𝟙 (MMP.ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ g) s) : _ ⟶ _) =
        Set.range i.base := by
    rw [show Set.range (𝟙 (MMP.ParameterPoint.fibre ((integralComponentAt x).subschemeι ≫ g) s) :
        _ ⟶ _) = Set.univ from Set.range_eq_univ.2 fun z ↦ ⟨z, rfl⟩, Set.image_univ]
  rw [hK]

end Specialization

section Multiplicity

/-- **Multiplicity one along a component meeting a smooth open.** If `f : V → B` is smooth on an
open `O ⊆ V`, every irreducible component of a fibre `V_s` whose generic point lies in `O` has
multiplicity one: the fibre of `O → B` is smooth, hence reduced, and is open in `V_s`. -/
private theorem componentMultiplicity_eq_one_of_genericPoint_mem {V B : Scheme.{0}} (f : V ⟶ B)
    (O : V.Opens) [Smooth (O.ι ≫ f)] (s : MMP.ParameterPoint B)
    [IsLocallyNoetherian (MMP.ParameterPoint.fibre f s)]
    (ξ : genericPoints (MMP.ParameterPoint.fibre f s))
    (hη : (MMP.ParameterPoint.fibreι f s).base ξ.1 ∈ O) :
    componentMultiplicity (𝟙 _) ξ = 1 := by
  haveI hm : IsOpenImmersion (MMP.ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (MMP.ParameterPoint.isPullback_fibreMap (q := f) O.ι rfl s).flip inferInstance
  have hr := Scheme.Pullback.range_map (O.ι ≫ f) s.ι f s.ι O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hrange : ξ.1 ∈
      Set.range (MMP.ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s).base := by
    have e : Set.range (MMP.ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s).base =
      Set.range (Limits.pullback.map (O.ι ≫ f) s.ι f s.ι O.ι (𝟙 _) (𝟙 _) (by simp)
        (by simp)).base := rfl
    rw [e, hr]
    refine ⟨?_, ?_⟩
    · change (MMP.ParameterPoint.fibreι f s).base _ ∈ Set.range O.ι.base
      rw [Scheme.Opens.range_ι]; exact hη
    · exact ⟨_, rfl⟩
  obtain ⟨η', hη'⟩ := hrange
  haveI : Smooth (MMP.ParameterPoint.fibreProj (O.ι ≫ f) s) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (MMP.ParameterPoint.isPullback_fibre (O.ι ≫ f) s) inferInstance
  haveI : IsReduced (MMP.ParameterPoint.fibre (O.ι ≫ f) s) :=
    AlgebraicGeometry.isReduced_of_smooth (MMP.ParameterPoint.fibreProj (O.ι ≫ f) s)
  have hred : _root_.IsReduced ((MMP.ParameterPoint.fibre f s).presheaf.stalk ξ.1) := by
    rw [← hη']
    have hiso : IsIso ((MMP.ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s).stalkMap
        η') := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ η'
    exact isReduced_of_injective
      ((MMP.ParameterPoint.fibreMap (p := O.ι ≫ f) (q := f) O.ι rfl s).stalkMap η').hom
      (ConcreteCategory.bijective_of_isIso _).1
  haveI := Stacks.RegularSectionGeneration.isArtinianRing_stalk_of_mem_genericPoints ξ.2
  exact Stacks.Chow.componentMultiplicity_eq_one_of_isField _ ξ
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing _)

/-- **Multiplicity one for the curve components of a fibre**, when the bad set of a smooth open
meets that fibre in points only. -/
private theorem componentMultiplicity_eq_one_of_smooth_open_of_mem {V B : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [B.Over (Spec (.of ℂ))] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]
    (f : V ⟶ B) [f.IsOver (Spec (.of ℂ))]
    (O : V.Opens) [Smooth (O.ι ≫ f)] (s : MMP.ParameterPoint B)
    (hbad : ∀ A : Set V, IsIrreducible A → A ⊆ (O : Set V)ᶜ →
      A ⊆ f.base ⁻¹' {s.point} → topologicalKrullDim A < 1)
    (ξ : genericPoints (MMP.ParameterPoint.fibre f s))
    (h1 : relativeDimension (fieldChowSituation ℂ).dimensionFunction
      (MMP.ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1 = (1 : ℕ)) :
    componentMultiplicity (𝟙 _) ξ = 1 := by
  haveI : LocallyOfFiniteType (MMP.ParameterPoint.fibre f s ↘ Spec (.of ℂ)) := by
    rw [← comp_over (MMP.ParameterPoint.fibreι f s) (Spec (.of ℂ))]; infer_instance
  haveI : IsLocallyNoetherian (MMP.ParameterPoint.fibre f s) :=
    LocallyOfFiniteType.isLocallyNoetherian (MMP.ParameterPoint.fibre f s ↘ Spec (.of ℂ))
  by_cases hη : (MMP.ParameterPoint.fibreι f s).base ξ.1 ∈ O
  · exact componentMultiplicity_eq_one_of_genericPoint_mem f O s ξ hη
  exfalso
  set i := MMP.ParameterPoint.fibreι f s with hi
  set A : Set (MMP.ParameterPoint.fibre f s) := closure {ξ.1} with hA
  have hsub : i.base '' A ⊆ (O : Set V)ᶜ := by
    refine (image_closure_subset_closure_image i.continuous).trans (closure_minimal ?_
      O.isOpen.isClosed_compl)
    rintro _ ⟨x, rfl, rfl⟩
    exact hη
  have hfib : i.base '' A ⊆ f.base ⁻¹' {s.point} := by
    rintro _ ⟨x, -, rfl⟩
    have : i.base x ∈ Set.range i.base := ⟨x, rfl⟩
    rw [hi, MMP.ParameterPoint.range_fibreι] at this
    exact this
  have hdimA : topologicalKrullDim A = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [hA, Stacks.Chow.topologicalKrullDim_closure_singleton_eq ℂ
      (MMP.ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1, h1, Int.toNat_natCast]
  have hdim' : topologicalKrullDim (i.base '' A) = ((1 : ℕ) : WithBot ℕ∞) := by
    rw [← hdimA]
    exact ((i.isClosedEmbedding.isEmbedding.homeomorphImage A).isHomeomorph
      |>.topologicalKrullDim_eq).symm
  have h := hbad _ (isIrreducible_singleton.closure.image _ i.continuous.continuousOn) hsub hfib
  rw [hdim'] at h
  exact lt_irrefl _ h

/-- **Generic multiplicity one.** For a dominant morphism `f : V → B` from an integral surface of
finite type over `ℂ` to a curve, over a nonempty open of `B` the curve components of the fibres
have multiplicity one (generic smoothness on the smooth locus of `V`). -/
private theorem exists_isOpen_forall_componentMultiplicity_eq_one {V B : Scheme.{0}}
    [V.Over (Spec (.of ℂ))] [B.Over (Spec (.of ℂ))] [IsIntegral V] [IsIntegral B]
    [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (B ↘ Spec (.of ℂ))] [QuasiCompact (B ↘ Spec (.of ℂ))] [Nontrivial B]
    (f : V ⟶ B) [f.IsOver (Spec (.of ℂ))] [IsDominant f]
    (hV : topologicalKrullDim V = ((2 : ℕ) : WithBot ℕ∞)) :
    ∃ W : Set B, IsOpen W ∧ W.Nonempty ∧ ∀ s : MMP.ParameterPoint B, s.point ∈ W →
      ∀ ξ : genericPoints (MMP.ParameterPoint.fibre f s),
        relativeDimension (fieldChowSituation ℂ).dimensionFunction
          (MMP.ParameterPoint.fibre f s ↘ Spec (.of ℂ)) ξ.1 = (1 : ℕ) →
        componentMultiplicity (𝟙 _) ξ = 1 := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of ℂ))
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V ↘ Spec (.of ℂ))
  haveI : AlgebraicGeometry.IsNoetherian V := ⟨⟩
  set Po := (V ↘ Spec (.of ℂ)).smoothLocus with hPo
  have hPone : genericPoint V ∈ Po := Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField _
  letI : Po.toScheme.Over (Spec (.of ℂ)) := ⟨Po.ι ≫ V ↘ Spec (.of ℂ)⟩
  haveI : Po.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType (Po.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (Po.ι ≫ _); infer_instance
  haveI : Smooth (Po.toScheme ↘ Spec (.of ℂ)) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff]
    change (Po.ι ≫ V ↘ Spec (.of ℂ)).smoothLocus = ⊤
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.2 fun x _ ↦ x.2
  haveI : Nonempty Po.toScheme := ⟨⟨_, hPone⟩⟩
  haveI : IsIntegral Po.toScheme := isIntegral_of_isOpenImmersion Po.ι
  haveI : QuasiCompact (Po.toScheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact (Po.ι ≫ _); infer_instance
  set po := Po.ι ≫ f with hpo
  haveI : po.IsOver (Spec (.of ℂ)) := by rw [hpo]; infer_instance
  obtain ⟨U₁, hU₁d, -, hU₁sm, -⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := ℂ) po
  set O : V.Opens := Po ⊓ f ⁻¹ᵁ U₁ with hO
  have hk : Set.range O.ι.base ⊆ Set.range ((po ⁻¹ᵁ U₁).ι ≫ Po.ι).base := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨⟨x.1, x.2.1⟩, x.2.2⟩, rfl⟩
  set k := IsOpenImmersion.lift ((po ⁻¹ᵁ U₁).ι ≫ Po.ι) O.ι hk with hkdef
  have hkf : k ≫ (po ⁻¹ᵁ U₁).ι ≫ Po.ι = O.ι := IsOpenImmersion.lift_fac _ _ _
  haveI : Smooth (O.ι ≫ f) := by
    haveI := hU₁sm
    have h : O.ι ≫ f = k ≫ (po ∣_ U₁) ≫ U₁.ι := by
      rw [morphismRestrict_ι, ← hkf]
      simp only [Category.assoc, hpo]
    rw [h]
    infer_instance
  have hηO : genericPoint V ∈ O := by
    refine ⟨hPone, ?_⟩
    change f.base (genericPoint V) ∈ U₁
    have h1 := (genericPoint_spec V).image (show Continuous f.base from f.continuous)
    rw [Set.image_univ, f.denseRange.closure_range] at h1
    rw [h1.eq (genericPoint_spec B)]
    change genericPoint B ∈ (U₁ : Set B)
    rw [(genericPoint_spec B).mem_open_set_iff U₁.isOpen, Set.univ_inter]
    exact hU₁d.nonempty
  have hZ₀ : IsClosed (O : Set V)ᶜ := O.isOpen.isClosed_compl
  have hdimZ₀ : ∀ Zi, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (O : Set V)ᶜ) Zi →
      topologicalKrullDim Zi ≤ 1 := by
    intro Zi hZi
    have hne : Zi ≠ Set.univ := fun h ↦ (hZi.1.2 (h ▸ Set.mem_univ _ :
      genericPoint V ∈ Zi)) hηO
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne
      (IrreducibleSpace.isIrreducible_univ _) (isClosed_of_maximal hZ₀ hZi) (Set.subset_univ _)
      hne (by
        rw [(Homeomorph.Set.univ V).isHomeomorph.topologicalKrullDim_eq, hV]
        decide)
    rw [(Homeomorph.Set.univ V).isHomeomorph.topologicalKrullDim_eq, hV] at hlt
    exact Order.le_of_lt_succ hlt
  obtain ⟨W₀, hW₀, hW₀ne, hW₀bad⟩ := exists_isOpen_forall_topologicalKrullDim_lt_one f.base
    f.continuous hZ₀ hdimZ₀
  refine ⟨W₀, hW₀, hW₀ne, fun s hs ξ h1 ↦
    componentMultiplicity_eq_one_of_smooth_open_of_mem f O s ?_ ξ h1⟩
  intro A' hA' hA'O hA'f
  exact hW₀bad _ hs s.isClosed_point A' hA'O hA' hA'f

end Multiplicity

section PointFibre

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
  {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}

/-- The point of `Y` under a `ℂ`-point of an open of a curve `T ⊆ Y`. -/
private noncomputable abbrev pointImage (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : Y :=
  (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ)

/-- A `ℂ`-point of `T°` is a closed immersion `Spec ℂ → Y`, when `Y` is separated over `ℂ`. -/
private theorem isClosedImmersion_point [IsSeparated sY] (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) := by
  haveI : IsClosedImmersion ((t.hom ≫ To.ι ≫ curveι T) ≫ sY) := by
    rw [Category.assoc, Category.assoc, t.hom_comp_structure]; infer_instance
  exact IsClosedImmersion.of_comp _ sY

/-- The image of a `ℂ`-point of `T°` in `Y` is the single point `pointImage t`. -/
private theorem range_point (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    Set.range (t.hom ≫ To.ι ≫ curveι T).base = {pointImage t} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact congrArg _ (Subsingleton.elim x _)
  · rintro rfl
    exact ⟨_, rfl⟩

/-- The image of a `ℂ`-point of `T°` is closed in `Y`, when `Y` is separated over `ℂ`. -/
private theorem isClosed_singleton_pointImage [IsSeparated sY]
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : IsClosed ({pointImage t} : Set Y) := by
  haveI := isClosedImmersion_point t
  exact range_point t ▸ (t.hom ≫ To.ι ≫ curveι T).isClosedEmbedding.isClosed_range

private theorem isClosedImmersion_pointFibreFst [IsSeparated sY]
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : IsClosedImmersion (pointFibreFst sY r To t) := by
  haveI := isClosedImmersion_point t
  unfold pointFibreFst pointFibre
  infer_instance

private theorem range_pointFibreFst (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    Set.range (pointFibreFst sY r To t).base = r.base ⁻¹' {pointImage t} := by
  unfold pointFibreFst pointFibre
  rw [Scheme.Pullback.range_fst]
  exact congrArg _ (range_point t)

private theorem pointFibreFst_base_mem (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (x : pointFibre sY r To t) :
    (pointFibreFst sY r To t).base x ∈ r.base ⁻¹' {pointImage t} := by
  rw [← range_pointFibreFst]
  exact ⟨x, rfl⟩

private theorem pointFibreFst_isOver (hM : r ≫ sY = Z ↘ Spec (.of ℂ))
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    (pointFibreFst sY r To t).IsOver (Spec (.of ℂ)) := ⟨by
  rw [← hM]
  exact pointFibreFst_comp_structure sY r To t⟩

/-- **The fibre of a family over a curve through `t`, inside `F_t`.** Let `b : B → Y` be a
morphism over `ℂ`, `g : G → B` and `jG : G → Z` with `g ≫ b = jG ≫ r`, `c : V → G` a morphism
and `s` a parameter point of `B` over the point of `t`. If `V_s → Z` is a closed immersion, then
it factors through a closed immersion `V_s → F_t` over `ℂ`. -/
private theorem exists_isClosedImmersion_fibre_pointFibre [IsSeparated sY]
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {B G : Scheme.{0}} [B.Over (Spec (.of ℂ))]
    [G.Over (Spec (.of ℂ))] (b : B ⟶ Y) (hb : b ≫ sY = B ↘ Spec (.of ℂ)) (g : G ⟶ B)
    [g.IsOver (Spec (.of ℂ))] (jG : G ⟶ Z) (hcomm : g ≫ b = jG ≫ r) {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] (c : W ⟶ G) [c.IsOver (Spec (.of ℂ))]
    (s : MMP.ParameterPoint B) (hst : b.base s.point = pointImage t)
    [IsClosedImmersion (MMP.ParameterPoint.fibreι (c ≫ g) s ≫ c ≫ jG)] :
    ∃ i : MMP.ParameterPoint.fibre (c ≫ g) s ⟶ pointFibre sY r To t,
      i ≫ pointFibreFst sY r To t = MMP.ParameterPoint.fibreι (c ≫ g) s ≫ c ≫ jG ∧
      IsClosedImmersion i ∧ i.IsOver (Spec (.of ℂ)) := by
  haveI := isClosedImmersion_point t
  set pt := t.hom ≫ To.ι ≫ curveι T with hpt
  -- the point `s` maps to `Spec ℂ`
  have hker : pt.ker ≤ (s.ι ≫ b).ker := by
    rw [(s.ι ≫ b).ker_eq_vanishingIdeal_closure_range,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    change closure (Set.range (s.ι ≫ b).base) ⊆ (pt.ker.support : Set Y)
    refine closure_minimal (fun _ hz ↦ pt.range_subset_ker_support ?_) pt.ker.support.isClosed
    obtain ⟨x, rfl⟩ := hz
    have hx : s.ι.base x = s.point := by
      have := MMP.ParameterPoint.range_ι s
      exact (this ▸ ⟨x, rfl⟩ : s.ι.base x ∈ ({s.point} : Set B))
    refine ⟨IsLocalRing.closedPoint ℂ, ?_⟩
    change pt.base _ = b.base (s.ι.base x)
    rw [hx, hst]
  set ℓ := IsClosedImmersion.lift pt (s.ι ≫ b) hker with hℓ
  have hℓf : ℓ ≫ pt = s.ι ≫ b := IsClosedImmersion.lift_fac _ _ _
  have hptS : pt ≫ sY = 𝟙 _ := by
    rw [hpt, Category.assoc, Category.assoc]
    exact t.hom_comp_structure
  have hw : (MMP.ParameterPoint.fibreι (c ≫ g) s ≫ c ≫ jG) ≫ r =
      (MMP.ParameterPoint.fibreProj (c ≫ g) s ≫ ℓ) ≫ pt := by
    rw [Category.assoc, Category.assoc, ← hcomm, Category.assoc, hℓf,
      ← Category.assoc (MMP.ParameterPoint.fibreProj (c ≫ g) s), ← MMP.ParameterPoint.fibreι_comp]
    simp only [Category.assoc]
  set i : MMP.ParameterPoint.fibre (c ≫ g) s ⟶ pointFibre sY r To t :=
    Limits.pullback.lift _ _ hw with hi
  have hi1 : i ≫ pointFibreFst sY r To t = MMP.ParameterPoint.fibreι (c ≫ g) s ≫ c ≫ jG :=
    Limits.pullback.lift_fst _ _ _
  have hi2 : i ≫ pointFibreSnd sY r To t = MMP.ParameterPoint.fibreProj (c ≫ g) s ≫ ℓ :=
    Limits.pullback.lift_snd _ _ _
  refine ⟨i, hi1, ?_, ⟨?_⟩⟩
  · haveI : IsClosedImmersion (i ≫ pointFibreFst sY r To t) := by rw [hi1]; infer_instance
    haveI := isClosedImmersion_pointFibreFst (r := r) t
    exact IsClosedImmersion.of_comp i (pointFibreFst sY r To t)
  · change i ≫ pointFibreSnd sY r To t = MMP.ParameterPoint.fibreι (c ≫ g) s ≫ W ↘ Spec (.of ℂ)
    rw [← comp_over c (Spec (.of ℂ)), hi2, ← Category.comp_id ℓ, ← hptS, ← Category.assoc ℓ, hℓf, ← comp_over g (Spec (.of ℂ)),
      ← hb]
    simp only [Category.assoc]
    rw [← Category.assoc (MMP.ParameterPoint.fibreProj (c ≫ g) s), ← MMP.ParameterPoint.fibreι_comp]
    simp only [Category.assoc]

/-- **The points of a family over `s`, read in `F_t`.** In the setting of
`exists_isClosedImmersion_fibre_pointFibre`, if `jG` is proper on the points of `G` over `s`,
these points map properly into `F_t(ℂ)`, compatibly with `jG`. -/
private theorem exists_isProperMap_fibrePoints_pointFibre (hM : r ≫ sY = Z ↘ Spec (.of ℂ))
    [IsSeparated sY] (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {B G : Scheme.{0}}
    [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))] [G.Over (Spec (.of ℂ))] (b : B ⟶ Y)
    (g : G ⟶ B)
    [g.IsOver (Spec (.of ℂ))] (jG : G ⟶ Z) [jG.IsOver (Spec (.of ℂ))] (hcomm : g ≫ b = jG ≫ r)
    (s : MMP.ParameterPoint B) (hst : b.base s.point = pointImage t)
    (hprop : IsProperMap fun x : ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {s.complexPoint}) ↦
      map (K := ℂ) jG x.1) :
    haveI := pointFibreFst_isOver hM t
    ∃ k : TopCat.of ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {s.complexPoint}) ⟶
        TopCat.of (UnderlyingSpace ℂ (pointFibre sY r To t)),
      IsProperMap k ∧ ∀ x, map (K := ℂ) (pointFibreFst sY r To t) (k x) = map (K := ℂ) jG x.1 := by
  haveI := pointFibreFst_isOver hM t
  haveI := isClosedImmersion_pointFibreFst (r := r) t
  set e := map (K := ℂ) (pointFibreFst sY r To t) with he
  have hemb : Topology.IsClosedEmbedding e := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) _
  have hmem : ∀ x : ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {s.complexPoint}),
      map (K := ℂ) jG x.1 ∈ Set.range e := by
    intro x
    rw [he, range_map_of_isClosedImmersion, range_pointFibreFst]
    change r.base (jG.base (x.1.toHom.base (IsLocalRing.closedPoint ℂ))) ∈ ({pointImage t} : Set Y)
    have hx : map (K := ℂ) g x.1 = s.complexPoint := x.2
    have hx' : g.base (x.1.toHom.base (IsLocalRing.closedPoint ℂ)) = s.point := by
      have := congrArg (fun q : UnderlyingSpace ℂ B ↦ q.toHom.base (IsLocalRing.closedPoint ℂ)) hx
      exact this.trans (MMP.ParameterPoint.complexPoint_toHom_closedPoint s)
    rw [Set.mem_singleton_iff, ← hst, ← hx']
    change (jG ≫ r).base _ = (g ≫ b).base _
    rw [hcomm]
  set Φ := hemb.isEmbedding.toHomeomorph with hΦ
  refine ⟨TopCat.ofHom ⟨fun x ↦ Φ.symm ⟨_, hmem x⟩, Φ.symm.continuous.comp
    (hprop.continuous.subtype_mk _)⟩, ?_, fun x ↦ ?_⟩
  · refine isProperMap_of_comp_of_inj (f := fun x ↦ Φ.symm ⟨_, hmem x⟩) (g := e)
      (Φ.symm.continuous.comp (hprop.continuous.subtype_mk _)) hemb.continuous ?_ hemb.injective
    convert hprop using 1
    funext x
    exact congrArg Subtype.val (Φ.apply_symm_apply ⟨_, hmem x⟩)
  · exact congrArg Subtype.val (Φ.apply_symm_apply ⟨_, hmem x⟩)

end PointFibre

end FamilySpecialization

/-! ### Pinned forms -/

section Pin

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- A family `ψ` of forms on the stalks of `𝒱_T` is *pinned* by a tuple `L` of `ℚ`-divisors on
the components of `F` if, at all but finitely many `t ∈ T°(ℂ)`, `ψ_t (r_t α)` is the pairing of
`α|_{F_t}` with the sum of the curve classes cut by `L` on `F_t`. -/
private def IsPinned (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (ψ : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      Module.Dual ℚ (curveLocalSystemFibre sY To t)) : Prop :=
  ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
    ∃ _ : IsComplexScheme (pointFibre sY r To t),
    ∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
      (p : pointFibre sY r To t)
      (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (pointFibre sY r To t ↘ Spec (.of ℂ)) p = (0 : ℕ)),
      borelMooreHomology.capProduct ℚ
          (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) Set.univ 2 2
          ((rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α)
          (∑ E : F.support, (L E).sum fun P c ↦ c •
            ∑ᶠ (C : {x : pointFibre sY r To t //
                relativeDimension (fieldChowSituation ℂ).dimensionFunction
                  (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
                A ⊆ (pointFibreFst sY r To t).base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                (closure {C.1})),
              fundamentalClass C.1 C.2) =
        ψ t ((localSystemRestrictionFibre sY hM.isBiregular To t).hom
            ((stalkToPullbackStalk (curveOpenInclusion sY To)
              (resolutionHigherDirectImage sY r 2) t).hom
              ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α))) •
          fundamentalClass p hp

variable (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
  {To : (curveScheme T).Opens}

private theorem sum_finsupp_sum_add {ι : Type*} [Fintype ι] {α : ι → Type*} {W : Type*}
    [AddCommGroup W] [Module ℚ W] (L L' : ∀ i, α i →₀ ℚ) (g : ∀ i, α i → W) :
    ∑ i, Finsupp.sum ((L + L') i) (fun P c ↦ c • g i P) =
      ∑ i, (L i).sum (fun P c ↦ c • g i P) + ∑ i, (L' i).sum (fun P c ↦ c • g i P) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦
    Finsupp.sum_add_index' (fun _ ↦ zero_smul _ _) (fun _ _ _ ↦ add_smul _ _ _)

private theorem sum_finsupp_sum_smul {ι : Type*} [Fintype ι] {α : ι → Type*} {W : Type*}
    [AddCommGroup W] [Module ℚ W] (c : ℚ) (L : ∀ i, α i →₀ ℚ) (g : ∀ i, α i → W) :
    ∑ i, Finsupp.sum ((c • L) i) (fun P c ↦ c • g i P) = c • ∑ i, (L i).sum (fun P c ↦ c • g i P) := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.smul_apply, Finsupp.sum_smul_index' (h := fun P c ↦ c • g i P) (fun _ ↦ zero_smul _ _),
    Finsupp.smul_sum]
  exact Finsupp.sum_congr fun _ _ ↦ mul_smul _ _ _

private theorem isPinned_add {L L' : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme}
    {ψ ψ' : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      Module.Dual ℚ (curveLocalSystemFibre sY To t)}
    (h : IsPinned hM To L ψ) (h' : IsPinned hM To L' ψ') :
    IsPinned hM To (L + L') (ψ + ψ') := by
  filter_upwards [h, h'] with t ht ht'
  obtain ⟨_, ht⟩ := ht
  obtain ⟨_, ht'⟩ := ht'
  refine ⟨‹_›, fun V hV α p hp ↦ ?_⟩
  rw [Pi.add_apply, LinearMap.add_apply, add_smul, ← ht V hV α p hp, ← ht' V hV α p hp]
  exact (congrArg _ (sum_finsupp_sum_add L L' _)).trans (map_add _ _ _)

private theorem isPinned_smul (c : ℚ) {L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme}
    {ψ : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      Module.Dual ℚ (curveLocalSystemFibre sY To t)}
    (h : IsPinned hM To L ψ) : IsPinned hM To (c • L) (c • ψ) := by
  filter_upwards [h] with t ht
  obtain ⟨_, ht⟩ := ht
  refine ⟨‹_›, fun V hV α p hp ↦ ?_⟩
  rw [Pi.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_smul, ← ht V hV α p hp]
  exact (congrArg _ (sum_finsupp_sum_smul c L _)).trans (map_smul _ _ _)

end Pin

/-! ### The geometric input and uniqueness -/

section Steps

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
  (hM : IsCurvePointExceptionalModel sY r F D)

/-! #### The complex points of `T°` -/

/-- `T°` as a scheme over `ℂ`, through `Y`. -/
private noncomputable abbrev curveOver (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) : To.toScheme.Over (Spec (.of ℂ)) :=
  ⟨To.ι ≫ curveι T ≫ sY⟩

/-- A local-system open `T°` of a curve `T` is a smooth curve over `ℂ`. -/
private theorem isSmoothVariety_curveOver (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y}
    (hdim : topologicalKrullDim (T : Set Y) = 1) {To : (curveScheme T).Opens}
    (hTo : IsLocalSystemOpen sY To) :
    letI := curveOver sY To
    IsSmoothVariety ℂ (To.toScheme ↘ Spec (.of ℂ)) ∧
      SmoothOfRelativeDimension 1 (To.toScheme ↘ Spec (.of ℂ)) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  have hY : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  obtain ⟨hirrT, hdT, hnoethT⟩ := curveScheme_facts hY hdim
  haveI := hirrT
  haveI := hnoethT
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  haveI : LocallyOfFiniteType ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (curveι T ≫ sY); infer_instance
  haveI : QuasiCompact ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change QuasiCompact (curveι T ≫ sY); infer_instance
  haveI : IsSeparated ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change IsSeparated (curveι T ≫ sY); infer_instance
  have hsm : To ≤ ((curveScheme T) ↘ Spec (.of ℂ)).smoothLocus := by
    intro x hx
    haveI : Smooth (To.ι ≫ (curveScheme T) ↘ Spec (.of ℂ)) := hTo.smooth
    have h1 : To.ι ⁻¹ᵁ ((curveScheme T) ↘ Spec (.of ℂ)).smoothLocus = ⊤ := by
      rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top_iff]
      infer_instance
    have h2 : (⟨x, hx⟩ : To) ∈ To.ι ⁻¹ᵁ ((curveScheme T) ↘ Spec (.of ℂ)).smoothLocus :=
      h1 ▸ trivial
    exact h2
  haveI : JacobsonSpace (curveScheme T) :=
    LocallyOfFiniteType.jacobsonSpace ((curveScheme T) ↘ Spec (.of ℂ))
  haveI : Nontrivial (curveScheme T) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := topologicalKrullDim_zero_of_discreteTopology (curveScheme T)
    rw [hdT] at h0
    exact absurd h0 (by decide)
  have hne : (To : Set (curveScheme T)).Nonempty := by
    haveI : Nonempty To := hTo.connectedSpace.toNonempty
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty To›
    exact ⟨x, hx⟩
  obtain ⟨d, hdB, hdcl⟩ := nonempty_inter_closedPoints hne To.isOpen.isLocallyClosed
  have hdη : d ≠ genericPoint (curveScheme T) := by
    intro h
    have hcl : IsClosed ({d} : Set (curveScheme T)) := hdcl
    have huniv := (genericPoint_spec (curveScheme T)).def
    rw [← h, hcl.closure_eq] at huniv
    obtain ⟨a, b, hab⟩ := exists_pair_ne (curveScheme T)
    have ha : a ∈ ({d} : Set (curveScheme T)) := huniv ▸ trivial
    have hb : b ∈ ({d} : Set (curveScheme T)) := huniv ▸ trivial
    exact hab (ha.trans hb.symm)
  exact MMP.Fourfold.isSmoothVariety_opens_of_le_smoothLocus ℂ hdT To hsm hdB hdη

/-- A local-system open `T°` of a curve has dimension one. -/
private theorem dim_curveOver (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y}
    (hdim : topologicalKrullDim (T : Set Y) = 1) {To : (curveScheme T).Opens}
    (hTo : IsLocalSystemOpen sY To) :
    letI := curveOver sY To
    SmoothOfRelativeDimension 1 (To.toScheme ↘ Spec (.of ℂ)) :=
  letI := curveOver sY To
  (isSmoothVariety_curveOver hM hdim hTo).2

/-- The inclusion `T°(ℂ) → Y(ℂ)`, on the underlying space of `T°`. -/
private noncomputable def curveBaseInclusion (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) :
    letI := curveOver sY To
    TopCat.of (UnderlyingSpace ℂ To.toScheme) ⟶ analyticSpace sY :=
  letI := curveOver sY To
  TopCat.ofHom ⟨fun x ↦ curveOpenInclusion sY To
      ((homeomorphUnderlyingSpace (X := To.toScheme)).symm x),
    (curveOpenInclusion sY To).hom.continuous.comp
      (homeomorphUnderlyingSpace (X := To.toScheme)).symm.continuous⟩

/-- The points of `T°(ℂ)` lying over an open `V ⊆ Y(ℂ)`. -/
private noncomputable abbrev curveBaseOpens (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (V : Opens (analyticSpace sY)) :
    letI := curveOver sY To
    Opens (TopCat.of (UnderlyingSpace ℂ To.toScheme)) :=
  letI := curveOver sY To
  Opens.comap (curveBaseInclusion sY To).hom V

/-- The complex points of the fibres `F_t` form compact spaces. -/
private theorem compactSpace_pointFibre (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    CompactSpace (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) := by
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsProper (pointFibre sY r To t ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd r (t.hom ≫ To.ι ≫ curveι T)))
  haveI : LocallyOfFiniteType (pointFibre sY r To t ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd r (t.hom ≫ To.ι ≫ curveι T)))
  exact compactSpace_analyticSpace_of_isProper

/-- The degree of the pairing of a class on `r⁻¹(V)` with a curve class on `F_t`, for
`t ∈ T°(ℂ)` over `V`. -/
private noncomputable def fibrePairing (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
    (w : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ)) : ℚ :=
  @compactDegree _ (compactSpace_pointFibre hM t) (BorelMooreCross.congrDegree ℚ _ (by norm_num)
    (borelMooreHomology.capProduct ℚ (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)))
      Set.univ 2 2 ((rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α) w))

/-- The scheme fibres `F_t` are complex schemes: they are projective over `ℂ`. -/
private theorem isComplexScheme_pointFibre (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : IsComplexScheme (pointFibre sY r To t) :=
  MMP.Analytic.isComplexScheme_of_isProjective _
    (hM.isResolution.2.2.2.1.baseChange (t.hom ≫ To.ι ≫ curveι T)).isProjective

/-- A nonempty closed subset of a scheme locally of finite type over `ℂ` has a complex point. -/
private theorem nonempty_pointsOver_of_isClosed' {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {S : Set X} (hS : IsClosed S) (hne : S.Nonempty) :
    (UnderlyingSpace.pointsOver (K := ℂ) S).Nonempty := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  have h := closure_inter_closedPoints hS
  obtain ⟨x, hxS, hxc⟩ : (S ∩ closedPoints X).Nonempty := by
    by_contra h'
    rw [Set.not_nonempty_iff_eq_empty] at h'
    rw [h', closure_empty] at h
    exact hne.ne_empty h.symm
  obtain ⟨p, hp⟩ := exists_toHom_eq' (X := X) hxc
  exact ⟨p, by rw [UnderlyingSpace.mem_pointsOver, hp]; exact hxS⟩

/-- **The complex points of a connected closed set are connected**: its irreducible pieces have
connected complex points, and two meeting pieces share a complex point. -/
private theorem isPreconnected_pointsOver_of_isPreconnected {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    {S : Set X} (hS : IsClosed S) (hc : _root_.IsPreconnected S) :
    _root_.IsPreconnected (UnderlyingSpace.pointsOver (K := ℂ) S) := by
  classical
  haveI := noetherianSpace_of_isComplexScheme (X := X)
  obtain ⟨𝒮, hfin, hcl, hirr, hSeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  have hsub : ∀ C ∈ 𝒮, C ⊆ S := fun C hC ↦ hSeq ▸ Set.subset_sUnion_of_mem hC
  have hmono : ∀ {A B : Set X}, A ⊆ B → UnderlyingSpace.pointsOver (K := ℂ) A ⊆
      UnderlyingSpace.pointsOver (K := ℂ) B := fun h p hp ↦ h hp
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hU hV hUV hdisj
  have hpiece : ∀ C ∈ 𝒮, UnderlyingSpace.pointsOver (K := ℂ) C ⊆ U ∨
      UnderlyingSpace.pointsOver (K := ℂ) C ⊆ V := fun C hC ↦
    isPreconnected_iff_subset_of_disjoint.1
      (MMP.Fourfold.isConnected_pointsOver_of_isIrreducible (hcl C hC) (hirr C hC)).isPreconnected
      U V hU hV ((hmono (hsub C hC)).trans hUV) (Set.eq_empty_of_subset_empty fun p hp ↦ by
        have hp' : p ∈ UnderlyingSpace.pointsOver (K := ℂ) S ∩ (U ∩ V) :=
          ⟨hmono (hsub C hC) hp.1, hp.2⟩
        rwa [hdisj] at hp')
  set tU := ⋃₀ {C ∈ 𝒮 | UnderlyingSpace.pointsOver (K := ℂ) C ⊆ U} with htU
  set tV := ⋃₀ {C ∈ 𝒮 | ¬ UnderlyingSpace.pointsOver (K := ℂ) C ⊆ U} with htV
  have htUcl : IsClosed tU := (hfin.subset fun C hC ↦ hC.1).isClosed_sUnion fun C hC ↦ hcl C hC.1
  have htVcl : IsClosed tV := (hfin.subset fun C hC ↦ hC.1).isClosed_sUnion fun C hC ↦ hcl C hC.1
  have hcover : S ⊆ tU ∪ tV := by
    intro x hx
    rw [hSeq] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    by_cases h : UnderlyingSpace.pointsOver (K := ℂ) C ⊆ U
    · exact Or.inl ⟨C, ⟨hC, h⟩, hxC⟩
    · exact Or.inr ⟨C, ⟨hC, h⟩, hxC⟩
  have hto : ∀ {t : Set X} (P : Set X → Prop), t = ⋃₀ {C ∈ 𝒮 | P C} → S ⊆ t →
      ∀ W : Set (UnderlyingSpace ℂ X), (∀ C ∈ 𝒮, P C → UnderlyingSpace.pointsOver (K := ℂ) C ⊆ W) →
        UnderlyingSpace.pointsOver (K := ℂ) S ⊆ W := by
    intro t P ht hSt W hW p hp
    obtain ⟨C, hC, hpC⟩ := (ht ▸ hSt) hp
    exact hW C hC.1 hC.2 hpC
  by_cases hB : (S ∩ tV).Nonempty
  · by_cases hA : (S ∩ tU).Nonempty
    · exfalso
      obtain ⟨x, -, hxU, hxV⟩ := isPreconnected_closed_iff.1 hc tU tV htUcl htVcl hcover hA hB
      obtain ⟨C, ⟨hC, hCU⟩, hxC⟩ := hxU
      obtain ⟨C', ⟨hC', hC'U⟩, hxC'⟩ := hxV
      obtain ⟨p, hpC, hpC'⟩ := nonempty_pointsOver_of_isClosed' ((hcl C hC).inter (hcl C' hC'))
        ⟨x, hxC, hxC'⟩
      have hpV : p ∈ V := ((hpiece C' hC').resolve_left hC'U) hpC'
      have : p ∈ UnderlyingSpace.pointsOver (K := ℂ) S ∩ (U ∩ V) :=
        ⟨hmono (hsub C hC) hpC, hCU hpC, hpV⟩
      rw [hdisj] at this
      exact this
    · rw [Set.not_nonempty_iff_eq_empty] at hA
      refine Or.inr (hto (fun C ↦ ¬ UnderlyingSpace.pointsOver (K := ℂ) C ⊆ U) htV ?_ V
        fun C hC hCU ↦ (hpiece C hC).resolve_left hCU)
      intro x hx
      rcases hcover hx with h | h
      · have hx' : x ∈ S ∩ tU := ⟨hx, h⟩
        rw [hA] at hx'
        exact absurd hx' (Set.notMem_empty x)
      · exact h
  · rw [Set.not_nonempty_iff_eq_empty] at hB
    refine Or.inl (hto (fun C ↦ UnderlyingSpace.pointsOver (K := ℂ) C ⊆ U) htU ?_ U
      fun C _ hCU ↦ hCU)
    intro x hx
    rcases hcover hx with h | h
    · exact h
    · have hx' : x ∈ S ∩ tV := ⟨hx, h⟩
      rw [hB] at hx'
      exact absurd hx' (Set.notMem_empty x)

/-- **The surface fibres are path connected.** `F_t(ℂ)` is the set of complex points of the fibre
`r⁻¹(t)`, which is connected by Zariski's main theorem (`Y` is normal and `r` birational). -/
private theorem pathConnectedSpace_pointFibre (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    PathConnectedSpace (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) := by
  have hres := hM.isResolution
  have hY : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  haveI := isComplexScheme_pointFibre hM t
  haveI : LocallyOfFiniteType (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (Limits.pullback.snd _ _); infer_instance
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; infer_instance
  haveI : (pointFibreFst sY r To t).IsOver (Spec (.of ℂ)) := pointFibreFst_isOver hM.comp_eq t
  haveI := isClosedImmersion_pointFibreFst (r := r) (To := To) t
  haveI := locallyPathConnectedSpace_analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))
  rw [pathConnectedSpace_iff_connectedSpace]
  have hconn : _root_.IsConnected (r.base ⁻¹' {pointImage t}) :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (r ≫ sY) sY
      hres.2.1 ⟨hY, ‹IsNormal Y›⟩ r hres.2.2.2.2).2 _
  have hcl : IsClosed (r.base ⁻¹' {pointImage t}) := by
    rw [← range_pointFibreFst]; exact (pointFibreFst sY r To t).isClosedEmbedding.isClosed_range
  have hpts := isPreconnected_pointsOver_of_isPreconnected hcl hconn.isPreconnected
  obtain ⟨p, hp⟩ := nonempty_pointsOver_of_isClosed' hcl hconn.nonempty
  rw [← range_pointFibreFst, ← UnderlyingSpace.range_map_of_isClosedImmersion] at hpts hp
  have hemb := UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
    (pointFibreFst sY r To t)
  obtain ⟨q, -⟩ := hp
  haveI : ConnectedSpace (UnderlyingSpace ℂ (pointFibre sY r To t)) := by
    refine connectedSpace_iff_univ.2 ⟨⟨q, trivial⟩, ?_⟩
    rw [hemb.isInducing.isPreconnected_image.symm, Set.image_univ]
    exact hpts
  exact homeomorphUnderlyingSpace.symm.surjective.connectedSpace
    homeomorphUnderlyingSpace.symm.continuous

/-- All but finitely many complex points of `T°` avoid the image of a component of `F` not
dominating `T`. -/
private theorem eventually_notMem_image_of_ne
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hdim : topologicalKrullDim (T : Set Y) = 1) (To : (curveScheme T).Opens) (E : F.support)
    (hE : r.base '' (E.1.support : Set Z) ≠ (T : Set Y)) :
    ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
      (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∉
        r.base '' (E.1.support : Set Z) := by
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsProper sY :=
    (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  have hEcl : IsClosed (r.base '' (E.1.support : Set Z)) := r.isClosedMap _ (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
  have hEirr : IsIrreducible (r.base '' (E.1.support : Set Z)) := by
    refine IsIrreducible.image ?_ _ r.continuous.continuousOn
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  let K : Set Y := (T : Set Y) ∩ r.base '' (E.1.support : Set Z)
  have hKne : K ≠ T := by
    intro h
    have hTK : (T : Set Y) ⊆ r.base '' (E.1.support : Set Z) := h ▸ Set.inter_subset_right
    apply hE
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hEirr T.isClosed
      hTK (Ne.symm hne) (ne_top_of_le_ne_top (by decide) (hM.topologicalKrullDim_image_le E.1 E.2))
    rw [hdim] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le E.1 E.2)) (lt_irrefl _)
  have hKfin : K.Finite := finite_of_isClosed_of_ne T.isIrreducible hdim (T.isClosed.inter hEcl)
    Set.inter_subset_left hKne
  refine Filter.eventually_cofinite.2
    ((finite_setOf_image_mem (To := To) hM.isResolution.1 hKfin).subset fun t ht ↦ ?_)
  refine ⟨?_, not_not.1 ht⟩
  rw [← range_curveι]
  exact ⟨_, rfl⟩

/-- **Components missing the general fibres.** A component `E` of `F` whose image is not `T`
meets only finitely many fibres `F_t`, so it cuts no curves on the others. -/
private theorem eventually_curveClass_eq_zero_of_image_ne
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hdim : topologicalKrullDim (T : Set Y) = 1) (To : (curveScheme T).Opens) (E : F.support)
    (hE : r.base '' (E.1.support : Set Z) ≠ (T : Set Y))
    (LE : QDivisor E.1.idealSheaf.subscheme) :
    ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
      ∀ _ : IsComplexScheme (pointFibre sY r To t),
      (LE.sum fun P c ↦ c •
        ∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
            A ⊆ (pointFibreFst sY r To t).base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
            (closure {C.1})),
          fundamentalClass C.1 C.2) = 0 := by
  classical
  filter_upwards [eventually_notMem_image_of_ne hM hdim To E hE] with t hyK _
  refine Finset.sum_eq_zero fun P _ ↦ ?_
  refine smul_eq_zero_of_right _ (finsum_eq_zero_of_forall_eq_zero fun C ↦
    finsum_eq_if.trans (if_neg fun hC ↦ ?_))
  obtain ⟨w, hw⟩ := hC.prop.1.nonempty
  obtain ⟨q, -, hq⟩ := hC.prop.2 hw
  apply hyK
  refine ⟨(pointFibreFst sY r To t).base w, ?_, ?_⟩
  · rw [← hq]
    have := (E.1.idealSheaf.range_subschemeι).subset ⟨q, rfl⟩
    exact this
  · have hc := congrArg (fun φ : pointFibre sY r To t ⟶ Y ↦ φ.base w) (pointFibreFst_comp sY r To t)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hc
    have hpt : (pointFibreSnd sY r To t).base w = IsLocalRing.closedPoint ℂ :=
      Subsingleton.elim _ _
    rw [hc, hpt]
    rfl

/-- The components of the exceptional divisor are smooth: `F` is snc. -/
private theorem isSmoothScheme_component (hM : IsCurvePointExceptionalModel sY r F D)
    (E : F.support) :
    MMP.Mori.IsSmoothScheme (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ)) := by
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have hX : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hres.2.2.1
  refine MMP.Resolution.isSmoothScheme_subscheme_of_hasSNCWith (k := ℂ) _ hX
    (E := (Empty.elim : Empty → Z.IdealSheafData)) ⟨fun i ↦ i.elim, fun x ↦ ?_⟩ ?_
  · obtain ⟨n, z, j, hz, -, -⟩ := hM.isSNC.2 x
    exact ⟨n, z, fun i ↦ i.1.elim, hz, fun i ↦ i.1.elim, fun a ↦ a.1.elim⟩
  · intro x hx
    obtain ⟨n, z, j, hz, -, hI⟩ := hM.isSNC.2 x
    refine ⟨n, z, fun i ↦ i.1.elim, {j ⟨E.1, E.2, hx⟩}, hz, fun i ↦ i.1.elim,
      fun a ↦ a.1.elim, ?_⟩
    rw [hI ⟨E.1, E.2, hx⟩]
    simp

/-- The components of the exceptional divisor are threefolds. -/
private theorem topologicalKrullDim_component (hM : IsCurvePointExceptionalModel sY r F D)
    (E : F.support) : topologicalKrullDim E.1.idealSheaf.subscheme = 3 := by
  have hres := hM.isResolution
  haveI : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hres.2.1
  have hdimZ : topologicalKrullDim Z = 4 := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hres.2.2.2.2]
    exact hM.topologicalKrullDim_eq
  haveI : IsIntegral Z := (show AlgebraicGeometry.IsVariety ℂ (r ≫ sY) from hres.2.1).toIsIntegral
  haveI : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI := E.1.integral
  haveI : LocallyOfFiniteType (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (E.1.idealSheaf.subschemeι ≫ Z ↘ Spec (.of ℂ))
    infer_instance
  have hform := MMP.height_add_coheight_eq_krullDim ℂ E.1.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, ← topologicalKrullDim_eq_krullDim',
    hdimZ] at hform
  have hh : Order.height E.1.genericPoint = 3 :=
    ENat.add_left_injective_of_ne_top ENat.one_ne_top
      ((WithBot.coe_injective hform : _ = (4 : ℕ∞)).trans (by norm_num))
  rw [topologicalKrullDim_eq_krullDim',
    ← MMP.height_add_coheight_eq_krullDim ℂ (genericPoint E.1.idealSheaf.subscheme),
    coheight_genericPoint_eq_zero, add_zero, ← height_apply_of_isClosedEmbedding
      E.1.idealSheaf.subschemeι E.1.idealSheaf.subschemeι.isClosedEmbedding]
  change ((Order.height E.1.genericPoint : ℕ∞) : WithBot ℕ∞) = 3
  rw [hh]
  rfl

/-- The map `E → T` of a component `E` of `F` mapping onto the curve `T`. -/
private theorem exists_lift_curveScheme {T : IrreducibleCloseds Y} (E : Mori.PrimeDivisor Z)
    (hE : r.base '' (E.support : Set Z) = (T : Set Y)) :
    ∃ pE : E.idealSheaf.subscheme ⟶ curveScheme T, pE ≫ curveι T = E.idealSheaf.subschemeι ≫ r := by
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  have hrangeE : Set.range (E.idealSheaf.subschemeι ≫ r).base = (T : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.IdealSheafData.range_subschemeι]
    exact hE
  have hker : (curveι T).ker ≤ (E.idealSheaf.subschemeι ≫ r).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg _ (TopologicalSpace.Closeds.ext ?_))
    rw [TopologicalSpace.Closeds.coe_closure, hrangeE, T.isClosed.closure_eq]
    rfl
  exact ⟨IsClosedImmersion.lift _ _ hker, IsClosedImmersion.lift_fac _ _ _⟩

/-- `fibrePairing` is linear in the cohomology class. -/
private noncomputable def fibrePairingₗ (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (w : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ)) :
    rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2 →ₗ[ℚ] ℚ where
  toFun α := fibrePairing hM t hV α w
  map_add' α α' := by
    simp only [fibrePairing, map_add, LinearMap.add_apply]
  map_smul' c α := by
    simp only [fibrePairing, map_smul, LinearMap.smul_apply, RingHom.id_apply]

private theorem fibrePairing_zero (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) :
    fibrePairing hM t hV α 0 = 0 := by
  simp only [fibrePairing, map_zero]

private theorem fibrePairing_sum (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) {ι : Type*}
    (S : Finset ι)
    (w : ι → MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ)) :
    fibrePairing hM t hV α (∑ i ∈ S, w i) = ∑ i ∈ S, fibrePairing hM t hV α (w i) := by
  simp only [fibrePairing, map_sum]

/-- `fibrePairing` does not change on shrinking the open set. -/
private theorem fibrePairing_restrict (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V V' : Opens (analyticSpace sY)} (h : V' ≤ V)
    (hV' : curveOpenInclusion sY To t ∈ V')
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
    (w : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ)) :
    fibrePairing hM t hV'
        ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) h) 2).hom α) w =
      fibrePairing hM t (h hV') α w := by
  unfold fibrePairing
  congr 3
  rw [← ConcreteCategory.comp_apply, ← rationalCohomologyMap_comp]
  rfl

/-- The cocone of the pairings with a curve class `w ∈ H_2(F_t)` over the neighbourhoods of `t`. -/
private noncomputable def fibrePairingCocone (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (w : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ)) :
    Limits.Cocone ((TopologicalSpace.OpenNhds.inclusion (curveOpenInclusion sY To t)).op ⋙
      directImagePresheaf (resolutionAnalyticMap sY r) 2) where
  pt := ModuleCat.of ℚ ℚ
  ι :=
    { app := fun U ↦ ModuleCat.ofHom (fibrePairingₗ hM t U.unop.2 w)
      naturality := fun U U' i ↦ by
        ext α
        change fibrePairing hM t U'.unop.2
          ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) i.unop.le) 2).hom
            α) w = fibrePairing hM t U.unop.2 α w
        exact fibrePairing_restrict hM t i.unop.le U'.unop.2 α w }

/-- The isomorphism of the stalk of `V ↦ H²(r⁻¹(V))` at `t` with the stalk `𝒲_t`. -/
private noncomputable def stalkPairingIso (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    (directImagePresheaf (resolutionAnalyticMap sY r) 2).stalk (curveOpenInclusion sY To t) ≅
      resolutionLocalSystemFibre sY r To t :=
  @asIso _ _ _ _ ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (curveOpenInclusion sY To t)).map
      (toSheafify (Opens.grothendieckTopology (analyticSpace sY))
        (directImagePresheaf (resolutionAnalyticMap sY r) 2)))
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (curveOpenInclusion sY To t)
        (ModuleCat.{0} ℚ) (directImagePresheaf (resolutionAnalyticMap sY r) 2)) ≪≫
    @asIso _ _ _ _ (stalkToPullbackStalk (curveOpenInclusion sY To)
      (higherDirectImage (resolutionAnalyticMap sY r) 2) t)
      (isIso_stalkToPullbackStalk (curveOpenInclusion sY To)
        (higherDirectImage (resolutionAnalyticMap sY r) 2) t)

/-- The pairing with a curve class `w ∈ H_2(F_t)`, on the stalk `𝒲_t` of `R²r_*ℚ`. -/
private noncomputable def stalkPairing (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (w : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ)) :
    resolutionLocalSystemFibre sY r To t →ₗ[ℚ] ℚ :=
  ((stalkPairingIso sY r t).inv ≫ Limits.colimit.desc _ (fibrePairingCocone hM t w)).hom

private theorem stalkPairing_apply (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (w : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) :
    stalkPairing hM t w ((stalkToPullbackStalk (curveOpenInclusion sY To)
        (resolutionHigherDirectImage sY r 2) t).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α)) =
      fibrePairing hM t hV α w := by
  have key : (directImagePresheaf (resolutionAnalyticMap sY r) 2).germ V _ hV ≫
      (stalkPairingIso sY r t).hom ≫ (stalkPairingIso sY r t).inv ≫
      (Limits.colimit.desc _ (fibrePairingCocone hM t w) :
        (directImagePresheaf (resolutionAnalyticMap sY r) 2).stalk (curveOpenInclusion sY To t) ⟶
          ModuleCat.of ℚ ℚ) =
        ModuleCat.ofHom (fibrePairingₗ hM t hV w) :=
    (congrArg (fun φ ↦ (directImagePresheaf (resolutionAnalyticMap sY r) 2).germ V _ hV ≫ φ)
      (Iso.hom_inv_id_assoc (stalkPairingIso sY r t)
        (Limits.colimit.desc _ (fibrePairingCocone hM t w)))).trans
      (Limits.colimit.ι_desc (fibrePairingCocone hM t w) (op ⟨V, hV⟩))
  exact congrArg (fun φ ↦ φ.hom α) key

/-- Restriction to equal open sets, followed by push-forwards along maps agreeing pointwise. -/
private theorem pushforward_restrict_congr {Y Y' : TopCat.{0}} [T2Space Y] {U U' : Opens Y}
    (hU : U = U') (f : TopCat.of U ⟶ Y') (f' : TopCat.of U' ⟶ Y') (hf : IsProperMap f)
    (hf' : IsProperMap f') (hff : ∀ x : U, f x = f' ⟨x.1, hU ▸ x.2⟩) (k : ℤ)
    (a : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) :
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f hf k).hom
        ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U k).hom a) =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) f' hf' k).hom
        ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ) U' k).hom a) := by
  subst hU
  have : f = f' := ConcreteCategory.hom_ext _ _ fun x ↦ hff x
  subst this
  rfl

/-- The complex points of `Z`, read in `Z^an = (r ≫ s_Y)(ℂ)`. -/
private noncomputable def toResolutionSpace (hM : IsCurvePointExceptionalModel sY r F D) :
    TopCat.of (UnderlyingSpace ℂ Z) ⟶ analyticSpace (r ≫ sY) :=
  TopCat.ofHom ((homeomorphUnderlyingSpace (X := Z)).symm : C(_, _)) ≫
    analyticMap (𝟙 Z) ((Category.id_comp _).trans hM.comp_eq)

private theorem toResolutionSpace_hom (hM : IsCurvePointExceptionalModel sY r F D)
    (z : UnderlyingSpace ℂ Z) : (toResolutionSpace hM z).hom = z.toHom := by
  change (ComplexPoints.realize (𝟙 Z) ((Category.id_comp _).trans hM.comp_eq)
    ((homeomorphUnderlyingSpace (X := Z)).symm z)).hom = _
  rw [ComplexPoints.realize_hom, Category.comp_id]
  rfl

private theorem curveBaseInclusion_hom (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) :
    letI := curveOver sY To
    ∀ x : UnderlyingSpace ℂ To.toScheme,
      (curveBaseInclusion sY To x).hom = x.toHom ≫ To.ι ≫ curveι T :=
  fun _ ↦ rfl

/-- The complex points of `Z`, as a homeomorphism `Z^an ≃ Z(ℂ)`. -/
private noncomputable def resolutionSpaceHomeomorph (hM : IsCurvePointExceptionalModel sY r F D) :
    analyticSpace (r ≫ sY) ≃ₜ UnderlyingSpace ℂ Z where
  toFun z := ⟨z.hom, by rw [← hM.comp_eq]; exact z.hom_comp_structure⟩
  invFun p := ⟨p.toHom, by rw [hM.comp_eq]; exact p.toHom_comp_over⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine ((homeomorphUnderlyingSpace (X := Z)).continuous.comp
      (ComplexPoints.continuous_realize (𝟙 Z) ((Category.id_comp _).trans hM.comp_eq.symm))).congr
      fun z ↦ UnderlyingSpace.ext ?_
    change (z.hom ≫ 𝟙 Z) = z.hom
    rw [Category.comp_id]
  continuous_invFun := by
    refine ((ComplexPoints.continuous_realize (𝟙 Z) ((Category.id_comp _).trans hM.comp_eq)).comp
      (homeomorphUnderlyingSpace (X := Z)).symm.continuous).congr fun p ↦ ComplexPoints.ext ?_
    change (p.toHom ≫ 𝟙 Z) = p.toHom
    rw [Category.comp_id]

private theorem toResolutionSpace_eq (hM : IsCurvePointExceptionalModel sY r F D) :
    toResolutionSpace hM = TopCat.ofHom ((resolutionSpaceHomeomorph hM).symm : C(_, _)) :=
  ConcreteCategory.hom_ext _ _ fun z ↦ ComplexPoints.ext (toResolutionSpace_hom hM z)

private theorem isProperMap_toResolutionSpace (hM : IsCurvePointExceptionalModel sY r F D) :
    IsProperMap (toResolutionSpace hM) := by
  rw [toResolutionSpace_eq]
  exact (resolutionSpaceHomeomorph hM).symm.isProperMap

/-- The complex points of `Y` lying on the curve `T`. -/
private def curvePoints (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y) :
    Set (analyticSpace sY) :=
  {y | y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (T : Set Y)}

private theorem isClosed_curvePoints (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y) :
    IsClosed (curvePoints sY T) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  exact (UnderlyingSpace.isClosed_pointsOver (K := ℂ) T.isClosed).preimage
    (homeomorphUnderlyingSpace (X := Y)).continuous

/-- The points of `r⁻¹(V)` over the curve `T`. -/
private def resolutionCurveSet (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (T : IrreducibleCloseds Y)
    (V : Opens (analyticSpace sY)) : Set (preimageSpace (resolutionAnalyticMap sY r) V) :=
  {z | resolutionAnalyticMap sY r z.1 ∈ curvePoints sY T}

private theorem isClosed_resolutionCurveSet (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y)
    (T : IrreducibleCloseds Y) (V : Opens (analyticSpace sY)) :
    IsClosed (resolutionCurveSet sY r T V) :=
  (isClosed_curvePoints sY T).preimage
    ((resolutionAnalyticMap sY r).hom.continuous.comp continuous_subtype_val)

/-- The points of `r⁻¹(V)` over `T` have arbitrarily small proper neighbourhood deformations in
`r⁻¹(V)`: they are the points of the algebraic subset `r⁻¹(T)` in an open subset of `Z(ℂ)`. -/
private theorem hasProperNeighbourhoodDeformations_resolutionCurveSet
    (hM : IsCurvePointExceptionalModel sY r F D) (T : IrreducibleCloseds Y)
    (V : Opens (analyticSpace sY)) :
    HasProperNeighbourhoodDeformations (resolutionCurveSet sY r T V) := by
  obtain ⟨hYc, N, Fe, hFe⟩ := UnderlyingSpace.hasBasis_contractible_and_exists_isClosedEmbedding Z
  set e := resolutionSpaceHomeomorph hM with he
  set U : Set (UnderlyingSpace ℂ Z) := e.symm ⁻¹' (resolutionAnalyticMap sY r ⁻¹' V) with hU
  have hUo : IsOpen U :=
    (V.isOpen.preimage (resolutionAnalyticMap sY r).hom.continuous).preimage e.symm.continuous
  have hrT : IsClosed (r.base ⁻¹' (T : Set Y)) := T.isClosed.preimage r.continuous
  have h := hasProperNeighbourhoodDeformations_preimage_val_of_isOpen hFe hYc hUo
    (UnderlyingSpace.isClosed_pointsOver (K := ℂ) hrT)
    (UnderlyingSpace.hasOpenContractibleBasis_pointsOver Z ⟨_, hrT⟩)
  let φ : preimageSpace (resolutionAnalyticMap sY r) V ≃ₜ U :=
    { toFun := fun z ↦ ⟨e z.1, show resolutionAnalyticMap sY r (e.symm (e z.1)) ∈ V by
        rw [e.symm_apply_apply]; exact z.2⟩
      invFun := fun p ↦ ⟨e.symm p.1, p.2⟩
      left_inv := fun z ↦ Subtype.ext (e.symm_apply_apply z.1)
      right_inv := fun p ↦ Subtype.ext (e.apply_symm_apply p.1)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
  convert HasProperNeighbourhoodDeformations.preimage_homeomorph h φ using 1
  ext z
  rfl

/-- The realization of the proper morphism `r` is proper. -/
private theorem isProperMap_resolutionAnalyticMap (hM : IsCurvePointExceptionalModel sY r F D) :
    IsProperMap (resolutionAnalyticMap sY r) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h : ⇑(resolutionAnalyticMap sY r) = (homeomorphUnderlyingSpace (X := Y)).symm ∘
      UnderlyingSpace.map (K := ℂ) r ∘ resolutionSpaceHomeomorph hM := by
    funext z
    exact ComplexPoints.ext rfl
  rw [h]
  exact (homeomorphUnderlyingSpace (X := Y)).symm.isProperMap.comp
    ((UnderlyingSpace.isProperMap_map (K := ℂ) r).comp (resolutionSpaceHomeomorph hM).isProperMap)

/-- The points of an open `V ⊆ Y(ℂ)` lying on `T`. -/
private abbrev curvePointsIn (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y)
    (V : Opens (analyticSpace sY)) : Set V :=
  Subtype.val ⁻¹' curvePoints sY T

/-- The restriction `r⁻¹(V) ∩ r⁻¹(T) → V ∩ T` of `r`. -/
private noncomputable def resolutionCurveMap (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (T : IrreducibleCloseds Y)
    (V : Opens (analyticSpace sY)) :
    TopCat.of (resolutionCurveSet sY r T V) ⟶ TopCat.of (curvePointsIn sY T V) :=
  TopCat.ofHom ⟨fun z ↦ ⟨⟨resolutionAnalyticMap sY r z.1.1, z.1.2⟩, z.2⟩,
    ((((resolutionAnalyticMap sY r).hom.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _)⟩

private theorem isProperMap_resolutionCurveMap (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (V : Opens (analyticSpace sY)) :
    IsProperMap (resolutionCurveMap sY r T V) := by
  refine isProperMap_of_comp_of_inj (g := (Subtype.val : curvePointsIn sY T V → V))
    (resolutionCurveMap sY r T V).hom.continuous continuous_subtype_val ?_ Subtype.val_injective
  have h1 := (borelMooreHomology.isProperMap_restrictPreimage (resolutionAnalyticMap sY r) V
    (isProperMap_resolutionAnalyticMap hM)).comp
    (Topology.IsClosedEmbedding.subtypeVal (isClosed_resolutionCurveSet sY r T V)).isProperMap
  exact h1

private theorem curveBaseInclusion_mem_curvePoints (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens) :
    letI := curveOver sY To
    ∀ x : UnderlyingSpace ℂ To.toScheme, curveBaseInclusion sY To x ∈ curvePoints sY T := by
  letI := curveOver sY To
  intro x
  change (curveBaseInclusion sY To x).hom.base (IsLocalRing.closedPoint ℂ) ∈ (T : Set Y)
  rw [curveBaseInclusion_hom, ← range_curveι (T := T)]
  exact ⟨_, rfl⟩

/-- The inclusion `T°(ℂ) ∩ V → V ∩ T`. -/
private noncomputable def curveBaseToPoints (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (V : Opens (analyticSpace sY)) :
    letI := curveOver sY To
    TopCat.of (curveBaseOpens sY To V) ⟶ TopCat.of (curvePointsIn sY T V) :=
  letI := curveOver sY To
  TopCat.ofHom ⟨fun b ↦ ⟨⟨curveBaseInclusion sY To b.1, b.2⟩,
      curveBaseInclusion_mem_curvePoints sY To b.1⟩,
    (((curveBaseInclusion sY To).hom.continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩

/-- The inclusion `T°(ℂ) → Y(ℂ)` is an embedding. -/
private theorem isEmbedding_curveBaseInclusion (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) : Topology.IsEmbedding (curveBaseInclusion sY To) := by
  letI := curveOver sY To
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : To.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : (curveι T).IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have h : ⇑(curveBaseInclusion sY To) = (homeomorphUnderlyingSpace (X := Y)).symm ∘
      UnderlyingSpace.map (K := ℂ) (curveι T) ∘ UnderlyingSpace.map (K := ℂ) To.ι := by
    funext x
    exact ComplexPoints.ext (by rw [curveBaseInclusion_hom]; rfl)
  rw [h]
  exact (homeomorphUnderlyingSpace (X := Y)).symm.isEmbedding.comp
    ((UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) (curveι T)).isEmbedding.comp
      (UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) To.ι).isEmbedding)

private theorem isClosedEmbedding_curveBaseToPoints (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens) (V : Opens (analyticSpace sY))
    (hVT : ∀ y ∈ V, y ∈ curvePoints sY T → y ∈ Set.range (curveBaseInclusion sY To)) :
    Topology.IsClosedEmbedding (curveBaseToPoints sY To V) ∧
      Function.Surjective (curveBaseToPoints sY To V) := by
  letI := curveOver sY To
  have hemb : Topology.IsEmbedding (curveBaseToPoints sY To V) := by
    have h1 := (isEmbedding_curveBaseInclusion sY To).comp
      (Topology.IsEmbedding.subtypeVal (p := (· ∈ (curveBaseOpens sY To V :
        Set (TopCat.of (UnderlyingSpace ℂ To.toScheme))))))
    have h2 : Topology.IsEmbedding (fun b : curveBaseOpens sY To V ↦
        (⟨curveBaseInclusion sY To b.1, b.2⟩ : V)) := h1.codRestrict _ _
    exact h2.codRestrict (curvePointsIn sY T V)
      (fun b ↦ curveBaseInclusion_mem_curvePoints sY To b.1)
  have hsurj : Function.Surjective (curveBaseToPoints sY To V) := by
    rintro ⟨⟨y, hyV⟩, hyT⟩
    obtain ⟨x, rfl⟩ := hVT y hyV hyT
    exact ⟨⟨x, hyV⟩, rfl⟩
  exact ⟨(hemb.toHomeomorphOfSurjective hsurj).isClosedEmbedding, hsurj⟩

/-- Over an open `V` all of whose points on `T` come from `T°`, the inclusion
`T°(ℂ) ∩ V → V ∩ T` is a homeomorphism; in particular push-forward along it is injective. -/
private theorem injective_pushforward_curveBaseToPoints (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens) (V : Opens (analyticSpace sY))
    (hVT : ∀ y ∈ V, y ∈ curvePoints sY T → y ∈ Set.range (curveBaseInclusion sY To)) (k : ℤ) :
    Function.Injective (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
      (curveBaseToPoints sY To V)
      (isClosedEmbedding_curveBaseToPoints sY To V hVT).1.isProperMap k).hom :=
  MMP.Chow.pushforward_injective_of_isClosedEmbedding _ _ (isClosedEmbedding_curveBaseToPoints sY To V hVT).1
    (isClosedEmbedding_curveBaseToPoints sY To V hVT).2 k

/-- The points of `T°(ℂ) ∩ V` have arbitrarily small proper neighbourhood deformations in
`T°(ℂ) ∩ V`. -/
private theorem hasProperNeighbourhoodDeformations_curveBaseOpens
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hdim : topologicalKrullDim (T : Set Y) = 1) {To : (curveScheme T).Opens}
    (hTo : IsLocalSystemOpen sY To) :
    letI := curveOver sY To
    ∀ (V : Opens (analyticSpace sY)) (z : UnderlyingSpace ℂ To.toScheme),
      HasProperNeighbourhoodDeformations
        ((borelMooreHomology.inclHom (curveBaseOpens sY To V)).hom ⁻¹' {z}) := by
  letI := curveOver sY To
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  intro V z
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective _ hM.isProjectiveVariety.isProjective.isProjective
  haveI : (curveι T).IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme (curveScheme T) := IsComplexScheme.of_isClosedImmersion (curveι T)
  haveI : To.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme To.toScheme := isComplexScheme_opens To
  haveI := (isSmoothVariety_curveOver hM hdim hTo).1
  haveI := (isSmoothVariety_curveOver hM hdim hTo).2
  have h := UnderlyingSpace.hasProperNeighbourhoodDeformations_preimage_singleton (𝟙 To.toScheme) z
  have he : (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (𝟙 To.toScheme))).hom ⁻¹' {z} = {z} := by
    ext x
    change UnderlyingSpace.map (K := ℂ) (𝟙 To.toScheme) x = z ↔ x = z
    rw [show UnderlyingSpace.map (K := ℂ) (𝟙 To.toScheme) x = x from
      UnderlyingSpace.ext (by rw [UnderlyingSpace.toHom_map, Category.comp_id])]
  rw [he] at h
  exact hasProperNeighbourhoodDeformations_inclHom_preimage_singleton _ h

/-- **The specialization of a class on `Z` against a class supported over `T`.** For an open
`V ⊆ Y(ℂ)` and `α' ∈ H²(r⁻¹(V), r⁻¹(V) - r⁻¹(T))`, the map
`H_4(Z) → H_2(V ∩ T)`, `μ ↦ r_*(α' ∩ μ|_{r⁻¹(V)})`. -/
private noncomputable def kernelSpecialization (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (V : Opens (analyticSpace sY))
    (α' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (preimageSpace (resolutionAnalyticMap sY r) V)
      (resolutionCurveSet sY r T V) 2) :
    MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Z)) 4
      →ₗ[ℚ] MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (curvePointsIn sY T V)) (4 - 2) := by
  haveI : T2Space (analyticSpace (r ≫ sY)) := (resolutionSpaceHomeomorph hM).isEmbedding.t2Space
  exact (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (resolutionCurveMap sY r T V)
      (isProperMap_resolutionCurveMap hM T V) (4 - 2)).hom ∘ₗ
    borelMooreHomology.capProductSupport ℚ (preimageSpace (resolutionAnalyticMap sY r) V)
      (isClosed_resolutionCurveSet sY r T V)
      (hasProperNeighbourhoodDeformations_resolutionCurveSet hM T V) 2 4 α' ∘ₗ
    (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
      (Opens.comap (resolutionAnalyticMap sY r).hom V) 4).hom ∘ₗ
    (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (toResolutionSpace hM)
      (isProperMap_toResolutionSpace hM) 4).hom

private theorem kernelSpecialization_apply (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (V : Opens (analyticSpace sY))
    (α' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (preimageSpace (resolutionAnalyticMap sY r) V)
      (resolutionCurveSet sY r T V) 2)
    (μ : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ Z)) 4) :
    haveI : T2Space (analyticSpace (r ≫ sY)) := (resolutionSpaceHomeomorph hM).isEmbedding.t2Space
    kernelSpecialization hM T V α' μ =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (resolutionCurveMap sY r T V)
        (isProperMap_resolutionCurveMap hM T V) (4 - 2)).hom
      (borelMooreHomology.capProductSupport ℚ (preimageSpace (resolutionAnalyticMap sY r) V)
        (isClosed_resolutionCurveSet sY r T V)
        (hasProperNeighbourhoodDeformations_resolutionCurveSet hM T V) 2 4 α'
        ((borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
          (Opens.comap (resolutionAnalyticMap sY r).hom V) 4).hom
          ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (toResolutionSpace hM)
            (isProperMap_toResolutionSpace hM) 4).hom μ))) :=
  rfl

/-- **Components away from `V` do not contribute.** If no complex point of a prime divisor `E`
of `Z` lies over `V`, then `kernelSpecialization` kills the classes pushed from `E`. -/
private theorem kernelSpecialization_componentHomologyMap_eq_zero
    (hM : IsCurvePointExceptionalModel sY r F D) (T : IrreducibleCloseds Y)
    (V : Opens (analyticSpace sY))
    (α' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (preimageSpace (resolutionAnalyticMap sY r) V)
      (resolutionCurveSet sY r T V) 2) (E : Mori.PrimeDivisor Z)
    (hE : ∀ z : analyticSpace (r ≫ sY), z.hom.base (IsLocalRing.closedPoint ℂ) ∈ E.support →
      resolutionAnalyticMap sY r z ∉ V)
    (x : RationalHomology E.idealSheaf.subscheme 4) :
    kernelSpecialization hM T V α' (componentHomologyMap E 4 x) = 0 := by
  haveI : T2Space (analyticSpace (r ≫ sY)) := (resolutionSpaceHomeomorph hM).isEmbedding.t2Space
  haveI : IsComplexScheme E.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion E.idealSheaf.subschemeι
  have hp := (isProperMap_toResolutionSpace hM).comp
    (UnderlyingSpace.isProperMap_map (K := ℂ) E.idealSheaf.subschemeι)
  have h2 : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (toResolutionSpace hM)
      (isProperMap_toResolutionSpace hM) 4).hom (componentHomologyMap E 4 x) =
      (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) E.idealSheaf.subschemeι) ≫
          toResolutionSpace hM) hp 4).hom x :=
    (borelMooreHomology.pushforward_comp_apply' ℚ _ _
      (UnderlyingSpace.isProperMap_map (K := ℂ) E.idealSheaf.subschemeι)
      (isProperMap_toResolutionSpace hM) 4 x).symm
  have hzero : (borelMooreHomology.restrict ℚ (ModuleCat.of ℚ ℚ)
      (Opens.comap (resolutionAnalyticMap sY r).hom V) 4).hom
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (toResolutionSpace hM)
        (isProperMap_toResolutionSpace hM) 4).hom (componentHomologyMap E 4 x)) = 0 := by
    rw [h2]
    refine borelMooreHomology.restrict_pushforward_eq_zero_of_disjoint ℚ (ModuleCat.of ℚ ℚ) _ _ _
      ?_ _ _
    rw [Set.disjoint_left]
    rintro z hzV ⟨p, rfl⟩
    refine hE _ ?_ hzV
    change ((toResolutionSpace hM) (UnderlyingSpace.map (K := ℂ) E.idealSheaf.subschemeι p)).hom.base
      (IsLocalRing.closedPoint ℂ) ∈ E.support
    rw [toResolutionSpace_hom, UnderlyingSpace.toHom_map]
    exact (E.idealSheaf.range_subschemeι).subset ⟨_, rfl⟩
  rw [kernelSpecialization_apply, hzero]
  exact (congrArg (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (resolutionCurveMap sY r T V)
    (isProperMap_resolutionCurveMap hM T V) (4 - 2)).hom
    ((borelMooreHomology.capProductSupport ℚ (preimageSpace (resolutionAnalyticMap sY r) V)
      (isClosed_resolutionCurveSet sY r T V)
      (hasProperNeighbourhoodDeformations_resolutionCurveSet hM T V) 2 4 α').map_zero)).trans
    (LinearMap.map_zero _)

/-- **The kernel of `r_t`.** A germ of a class `α` on `r⁻¹(V)` whose image under `r_t` vanishes
restricts to `0` on `j⁻¹(W)` for some neighbourhood `W ⊆ V` of `t`. -/
private theorem exists_le_directImageRestriction_eq_zero
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    {To : (curveScheme T).Opens} (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
    (h : (localSystemRestrictionFibre sY hM.isBiregular To t).hom
      ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2) t).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α)) = 0) :
    ∃ (W : Opens (analyticSpace sY)) (hWV : W ≤ V), curveOpenInclusion sY To t ∈ W ∧
      ((directImageRestriction (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) 2).app (op W)).hom
        (((directImagePresheaf (resolutionAnalyticMap sY r) 2).map (homOfLE hWV).op).hom α) = 0 := by
  set ψ := directImageRestriction (resolutionAnalyticMap sY r)
    (analyticMap (regularSection sY hM.isBiregular) (by rw [← Category.assoc, regularSection_comp]))
    (regularSection_analyticMap_comp sY hM.isBiregular) 2 with hψ
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply V (curveOpenInclusion sY To t) hV
    (toSheafify (Opens.grothendieckTopology (analyticSpace sY))
      (directImagePresheaf (resolutionAnalyticMap sY r) 2)) α
  have e1' : (higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α =
      ((TopCat.Sheaf.forget _ _).obj (higherDirectImage (resolutionAnalyticMap sY r) 2)).germ V _ hV
        (((toSheafify (Opens.grothendieckTopology (analyticSpace sY))
          (directImagePresheaf (resolutionAnalyticMap sY r) 2)).app (op V)).hom α) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V (curveOpenInclusion sY To t) hV
      (toSheafify (Opens.grothendieckTopology (analyticSpace sY))
        (directImagePresheaf (resolutionAnalyticMap sY r) 2)) α
  erw [e1'] at h
  unfold localSystemRestrictionFibre localSystemRestriction at h
  erw [stalkToPullbackStalk_germ_map] at h
  have h2 := (bijective_stalkToPullbackStalk (curveOpenInclusion sY To)
    (regularHigherDirectImage sY 2) t).1 (h.trans (map_zero _).symm)
  have h2' : ((TopCat.Presheaf.stalkFunctor _ _).map ((TopCat.Sheaf.forget _ _).map
      (resolutionRestriction sY hM.isBiregular 2))).hom
      ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α) = 0 := by
    rw [e1']
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact h2
  have h3 := higherDirectImageRestriction_germ (resolutionAnalyticMap sY r)
    (analyticMap (regularSection sY hM.isBiregular) (by rw [← Category.assoc, regularSection_comp]))
    (regularSection_analyticMap_comp sY hM.isBiregular) 2 _ hV α
  change ((TopCat.Presheaf.stalkFunctor _ _).map ((TopCat.Sheaf.forget _ _).map
    (resolutionRestriction sY hM.isBiregular 2))).hom _ = _ at h3
  rw [h3] at h2'
  -- the presheaf germ vanishes
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (curveOpenInclusion sY To t)
    (ModuleCat.{0} ℚ) (directImagePresheaf (regularInclusion sY) 2)
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (curveOpenInclusion sY To t)).map
      (toSheafify (Opens.grothendieckTopology (analyticSpace sY))
        (directImagePresheaf (regularInclusion sY) 2)))).1
  have h4 : (directImagePresheaf (regularInclusion sY) 2).germ V _ hV ((ψ.app (op V)).hom α) =
      (directImagePresheaf (regularInclusion sY) 2).germ V _ hV 0 := by
    apply hinj
    have e0 : ((directImagePresheaf (regularInclusion sY) 2).germ V _ hV) 0 = 0 := map_zero _
    have e0' : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ)
        (curveOpenInclusion sY To t)).map (toSheafify (Opens.grothendieckTopology (analyticSpace sY))
          (directImagePresheaf (regularInclusion sY) 2))))
        ((directImagePresheaf (regularInclusion sY) 2).germ V _ hV 0) = 0 := by
      rw [e0]; exact map_zero _
    exact h2'.trans e0'.symm
  obtain ⟨W, hW, iV, iV', hres⟩ := (directImagePresheaf (regularInclusion sY) 2).germ_eq _ hV hV _ _ h4
  refine ⟨W, iV.le, hW, ?_⟩
  rw [map_zero] at hres
  rw [← hres]
  have hnat := congrArg (fun φ ↦ φ.hom α) (ψ.naturality iV.op)
  exact hnat

/-- **Classes killed on the regular part vanish off `T`.** Over an open `W` of `Y(ℂ)` on which
the singular points lie on `T`, a class on `r⁻¹(W)` killed by the restriction to
`j⁻¹(W) ≅ r⁻¹(W ∩ Y_reg)` restricts to zero on `r⁻¹(W) - r⁻¹(T)`. -/
private theorem restrictCompl_eq_zero_of_directImageRestriction
    (hM : IsCurvePointExceptionalModel sY r F D) (T : IrreducibleCloseds Y)
    (W : Opens (analyticSpace sY))
    (hW : ∀ y ∈ W, y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (singularLocus sY : Set Y) →
      y ∈ curvePoints sY T)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) W) 2)
    (h : ((directImageRestriction (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) 2).app (op W)).hom α = 0) :
    (cohomologyWithSupports.restrictCompl ℚ (preimageSpace (resolutionAnalyticMap sY r) W)
      (resolutionCurveSet sY r T W) 2).hom α = 0 := by
  -- the regular points of `Y` over `W` off `T`
  have hreg : ∀ z : ↥(resolutionCurveSet sY r T W)ᶜ,
      resolutionAnalyticMap sY r z.1.1 ∈ Set.range (regularInclusion sY) := by
    intro z
    change _ ∈ Set.range (ComplexPoints.realize (sX := (smoothLocus sY).ι ≫ sY)
      (smoothLocus sY).ι rfl)
    rw [MMP.Analytic.ComplexPoints.range_realize_ι]
    by_contra hz
    refine z.2 (hW _ z.1.2 ?_)
    change (resolutionAnalyticMap sY r z.1.1).hom.base (IsLocalRing.closedPoint ℂ) ∉
      (smoothLocus sY : Set Y)
    rwa [show IsLocalRing.closedPoint ℂ = (default : Spec (.of ℂ)) from Subsingleton.elim _ _]
  set e := (MMP.Analytic.ComplexPoints.isOpenEmbedding_realize_ι (sX := sY)
    (smoothLocus sY)).isEmbedding.toHomeomorph with he
  have heq : ∀ y (hy : y ∈ Set.range (regularInclusion sY)),
      regularInclusion sY (e.symm ⟨y, hy⟩) = y := fun y hy ↦
    congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  have hmemW : ∀ z : ↥(resolutionCurveSet sY r T W)ᶜ,
      regularInclusion sY (e.symm ⟨_, hreg z⟩) ∈ W := fun z ↦ by
    rw [heq]; exact z.1.2
  have hc : Continuous fun z : ↥(resolutionCurveSet sY r T W)ᶜ ↦ e.symm ⟨_, hreg z⟩ :=
    e.symm.continuous.comp (Continuous.subtype_mk ((resolutionAnalyticMap sY r).hom.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)) fun z ↦ hreg z)
  let κ : TopCat.of ↥(resolutionCurveSet sY r T W)ᶜ ⟶ preimageSpace (regularInclusion sY) W :=
    TopCat.ofHom ⟨fun z ↦ ⟨e.symm ⟨_, hreg z⟩, hmemW z⟩, hc.subtype_mk hmemW⟩
  have hfac : subspaceInclusion (preimageSpace (resolutionAnalyticMap sY r) W)
      (resolutionCurveSet sY r T W)ᶜ = κ ≫ preimageRestrict (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) W := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ Subtype.ext (ComplexPoints.ext ?_)
    set x := e.symm ⟨_, hreg z⟩ with hxdef
    have hx : x.hom ≫ (smoothLocus sY).ι = z.1.1.hom ≫ r :=
      congrArg ComplexPoints.hom (heq _ (hreg z))
    have hrange : Set.range z.1.1.hom.base ⊆ Set.range (r ⁻¹ᵁ smoothLocus sY).ι.base := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have h2 : (x.hom ≫ (smoothLocus sY).ι).base p ∈ Set.range (smoothLocus sY).ι.base :=
        ⟨_, rfl⟩
      rw [hx, Scheme.Opens.range_ι] at h2
      exact h2
    set z' := IsOpenImmersion.lift (r ⁻¹ᵁ smoothLocus sY).ι z.1.1.hom hrange with hz'def
    have hz' : z' ≫ (r ⁻¹ᵁ smoothLocus sY).ι = z.1.1.hom := IsOpenImmersion.lift_fac _ _ _
    have hxz : x.hom = z' ≫ (r ∣_ smoothLocus sY) := by
      rw [← cancel_mono (smoothLocus sY).ι, hx, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, hz']
    change z.1.1.hom = x.hom ≫ regularSection sY hM.isBiregular
    rw [hxz, regularSection, Category.assoc, ← Category.assoc (r ∣_ smoothLocus sY),
      @IsIso.hom_inv_id _ _ _ _ _ hM.isBiregular, Category.id_comp, hz']
  change absPullback _ 2 α = 0
  rw [hfac, absPullback_comp]
  change absPullback κ 2 (((directImageRestriction (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) 2).app (op W)).hom α) = 0
  rw [h]
  exact (absPullback κ 2).map_zero

open MMP.borelMooreHomology Topology in
/-- `eventually_compactDegree_capProductSupportPullback_eq`, with the degrees of the cap product
given as integers `j = n` and `k = n`. -/
private theorem eventually_compactDegree_capProductSupportPullback_eq_of_eq {B : TopCat.{0}}
    [T2Space B] [LocallyConnectedSpace B] [T5Space B] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] [ChartedSpace H B] (hB : IsOrientedAtlas H B)
    {n : ℕ} (hn : 0 < n) (b : Module.Basis (Fin n) ℝ H) (Q : TopologicalSpace.Opens B)
    (hd : ∀ s : B, HasProperNeighbourhoodDeformations ((inclHom Q).hom ⁻¹' {s}))
    {j k : ℤ} (hj : j = n) (hk : k = n)
    (ν : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of Q) k)
    {s₀ : B} (hs₀ : s₀ ∈ Q) (u₀ : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) B {s₀} j)
    (hu₀ : IsLocalOrientationClass ℚ b s₀ (cast (by rw [hj]) u₀)) :
    ∀ᶠ s in 𝓝 s₀, ∀ u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) B {s} j,
      IsLocalOrientationClass ℚ b s (cast (by rw [hj]) u) →
      @compactDegree (TopCat.of ((inclHom Q).hom ⁻¹' {s}))
          (compactSpace_preimage_singleton_inclHom Q s)
          (BorelMooreCross.congrDegree ℚ _ (by rw [hj, hk]; simp)
            (capProductSupportPullback ℚ (inclHom Q) isClosed_singleton (hd s) j k u ν)) =
        @compactDegree (TopCat.of ((inclHom Q).hom ⁻¹' {s₀}))
          (compactSpace_preimage_singleton_inclHom Q s₀)
          (BorelMooreCross.congrDegree ℚ _ (by rw [hj, hk]; simp)
            (capProductSupportPullback ℚ (inclHom Q) isClosed_singleton (hd s₀) j k u₀ ν)) := by
  subst hj hk
  exact eventually_compactDegree_capProductSupportPullback_eq hB hn b Q hd ν hs₀ u₀ hu₀

open MMP.UnderlyingSpace MMP.borelMooreHomology in
/-- The map `W_V → V ∩ T` from the complex points of a prime divisor `E` of `Z` over `V`, for
`E` mapping into `T`, is proper. -/
private theorem isProperMap_componentCurveMap (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (V : Opens (analyticSpace sY)) (E : Mori.PrimeDivisor Z)
    (hET : ∀ x : UnderlyingSpace ℂ E.idealSheaf.subscheme,
      resolutionAnalyticMap sY r ((TopCat.ofHom (map (K := ℂ) E.idealSheaf.subschemeι) ≫
        toResolutionSpace hM) x) ∈ curvePoints sY T) :
    let jEan := TopCat.ofHom (map (K := ℂ) E.idealSheaf.subschemeι) ≫ toResolutionSpace hM
    let Wv : Opens (TopCat.of (UnderlyingSpace ℂ E.idealSheaf.subscheme)) :=
      Opens.comap jEan.hom (Opens.comap (resolutionAnalyticMap sY r).hom V)
    IsProperMap (TopCat.ofHom ⟨fun w ↦ ⟨⟨resolutionAnalyticMap sY r (jEan w.1), w.2⟩, hET w.1⟩,
        ((((resolutionAnalyticMap sY r).hom.continuous.comp
          (jEan.hom.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _)⟩ :
        TopCat.of Wv ⟶ TopCat.of (curvePointsIn sY T V)) := by
  intro jEan Wv
  haveI : T2Space (analyticSpace (r ≫ sY)) := (resolutionSpaceHomeomorph hM).isEmbedding.t2Space
  have hjEp : IsProperMap jEan :=
    (isProperMap_toResolutionSpace hM).comp (isProperMap_map (K := ℂ) E.idealSheaf.subschemeι)
  have hιEp := isProperMap_restrictPreimage jEan (Opens.comap (resolutionAnalyticMap sY r).hom V)
    hjEp
  exact isProperMap_of_comp_of_inj (g := (Subtype.val : curvePointsIn sY T V → V))
    (by fun_prop) continuous_subtype_val
    ((isProperMap_restrictPreimage (resolutionAnalyticMap sY r) V
      (isProperMap_resolutionAnalyticMap hM)).comp hιEp) Subtype.val_injective

open MMP.UnderlyingSpace MMP.borelMooreHomology in
/-- **The specialization of a class pushed from a prime divisor `E` lying over `T`**, read on the
complex points `W_V` of `E` over `V`: it is `q_*(α'|_{W_V} ∩ x|_{W_V})`, for
`q : W_V → V ∩ T`. -/
private theorem kernelSpecialization_componentHomologyMap_eq_pushforward
    (hM : IsCurvePointExceptionalModel sY r F D)
    (T : IrreducibleCloseds Y) (V : Opens (analyticSpace sY)) (E : Mori.PrimeDivisor Z)
    (hET : ∀ x : UnderlyingSpace ℂ E.idealSheaf.subscheme,
      resolutionAnalyticMap sY r ((TopCat.ofHom (map (K := ℂ) E.idealSheaf.subschemeι) ≫
        toResolutionSpace hM) x) ∈ curvePoints sY T)
    (α' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (preimageSpace (resolutionAnalyticMap sY r) V)
      (resolutionCurveSet sY r T V) 2)
    (x : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ E.idealSheaf.subscheme)) 4) :
    let jEan := TopCat.ofHom (map (K := ℂ) E.idealSheaf.subschemeι) ≫ toResolutionSpace hM
    let Wv : Opens (TopCat.of (UnderlyingSpace ℂ E.idealSheaf.subscheme)) :=
      Opens.comap jEan.hom (Opens.comap (resolutionAnalyticMap sY r).hom V)
    let q : TopCat.of Wv ⟶ TopCat.of (curvePointsIn sY T V) :=
      TopCat.ofHom ⟨fun w ↦ ⟨⟨resolutionAnalyticMap sY r (jEan w.1), w.2⟩, hET w.1⟩,
        ((((resolutionAnalyticMap sY r).hom.continuous.comp
          (jEan.hom.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _)⟩
    kernelSpecialization hM T V α' (componentHomologyMap E 4 x) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) q (isProperMap_componentCurveMap hM T V E hET)
        (4 - 2)).hom
      (borelMooreHomology.capProduct ℚ _ Set.univ 2 4
        (absPullback (restrictPreimage jEan (Opens.comap (resolutionAnalyticMap sY r).hom V)) 2
          ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α'))
        ((restrict ℚ (ModuleCat.of ℚ ℚ) Wv 4).hom x)) := by
  intro jEan Wv q
  haveI : T2Space (analyticSpace (r ≫ sY)) := (resolutionSpaceHomeomorph hM).isEmbedding.t2Space
  have hjEp : IsProperMap jEan :=
    (isProperMap_toResolutionSpace hM).comp (isProperMap_map (K := ℂ) E.idealSheaf.subschemeι)
  let ιE : TopCat.of Wv ⟶ preimageSpace (resolutionAnalyticMap sY r) V :=
    restrictPreimage jEan (Opens.comap (resolutionAnalyticMap sY r).hom V)
  have hιEp : IsProperMap ιE := isProperMap_restrictPreimage jEan _ hjEp
  have hqp : IsProperMap q := isProperMap_componentCurveMap hM T V E hET
  have hA'u : ιE ⁻¹' resolutionCurveSet sY r T V = Set.univ :=
    Set.eq_univ_of_forall fun w ↦ hET w.1
  rw [kernelSpecialization_apply]
  have h2 : (pushforward ℚ (ModuleCat.of ℚ ℚ) (toResolutionSpace hM)
      (isProperMap_toResolutionSpace hM) 4).hom (componentHomologyMap E 4 x) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) jEan hjEp 4).hom x :=
    (pushforward_comp_apply' ℚ _ _ (isProperMap_map (K := ℂ) E.idealSheaf.subschemeι)
      (isProperMap_toResolutionSpace hM) 4 _).symm
  rw [h2, restrict_pushforward_apply]
  have h3 := pushforward_restrictPreimage_capProductSupportPullback ℚ ιE hιEp
    (isClosed_resolutionCurveSet sY r T V)
    (hasProperNeighbourhoodDeformations_resolutionCurveSet hM T V)
    (hasProperNeighbourhoodDeformations_of_eq_univ hA'u) 2 4 α'
    ((restrict ℚ (ModuleCat.of ℚ ℚ) Wv 4).hom x)
  erw [← h3]
  erw [← pushforward_comp_apply']
  have hmapR : TopCat.ofHom (ιE.hom.restrictPreimage (resolutionCurveSet sY r T V)) ≫
      resolutionCurveMap sY r T V =
      subsetInclusion (ιE ⁻¹' resolutionCurveSet sY r T V) ≫ q :=
    ConcreteCategory.hom_ext _ _ fun z ↦ rfl
  rw [pushforward_apply_congr ℚ hmapR _
      (hqp.comp (isProperMap_subsetInclusion
        ((isClosed_resolutionCurveSet sY r T V).preimage ιE.hom.continuous))),
    pushforward_comp_apply' ℚ _ _ (isProperMap_subsetInclusion
      ((isClosed_resolutionCurveSet sY r T V).preimage ιE.hom.continuous)) hqp,
    capProductSupportPullback_apply,
    pushforward_subsetInclusion_capProductSupport]
  congr 1
  refine (capProduct_toCohomology _ _ 2 4 _ _).symm.trans ?_
  rw [cohomologyWithSupports.toCohomology_pullback_eq_map]
  rfl

open MMP.borelMooreHomology in
/-- Two factorizations of a specialization: if `g_Q ≫ b = h ≫ q`, `ι_O = h ≫ ι_E` and
`h_* β = x`, then `b_* g_{Q*}(ι_O^* c ∩ β) = q_*(ι_E^* c ∩ x)` (projection formula). -/
private theorem pushforward_pushforward_capProduct_absPullback_eq {O Qs Pts W Rr : TopCat.{0}}
    (gQ : O ⟶ Qs) (hgQ : IsProperMap gQ) (b : Qs ⟶ Pts) (hb : IsProperMap b)
    (h : O ⟶ W) (hh : IsProperMap h) (q : W ⟶ Pts) (hq : IsProperMap q)
    (ιO : O ⟶ Rr) (ιE : W ⟶ Rr) (hgq : gQ ≫ b = h ≫ q) (hιO : ιO = h ≫ ιE)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Rr Set.univ 2)
    (β : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) O 4)
    (x : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) W 4)
    (hx : (pushforward ℚ (ModuleCat.of ℚ ℚ) h hh 4).hom β = x) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) b hb (4 - 2)).hom
        ((pushforward ℚ (ModuleCat.of ℚ ℚ) gQ hgQ (4 - 2)).hom
          (capProduct ℚ O Set.univ 2 4 (absPullback ιO 2 c) β)) =
      (pushforward ℚ (ModuleCat.of ℚ ℚ) q hq (4 - 2)).hom
        (capProduct ℚ W Set.univ 2 4 (absPullback ιE 2 c) x) := by
  rw [← pushforward_comp_apply', pushforward_apply_congr ℚ hgq _ (hq.comp hh),
    pushforward_comp_apply' ℚ h q hh hq, hιO, absPullback_comp,
    pushforward_capProduct_absPullback h hh, hx]

open MMP.UnderlyingSpace MMP.borelMooreHomology in
/-- The restriction to an open `O` of a class `β` on `A`, pushed into an open `W_V` of `B` along
an open immersion `ι : A → B` with `ι(O(ℂ)) = W_V`, is the restriction to `W_V` of any class `x` on
`B` whose restriction to `ι(A(ℂ))` is `β`. -/
private theorem pushforward_restrict_eq_restrict_of_opensRangeMap {A B : Scheme.{0}}
    [A.Over (Spec (.of ℂ))] [B.Over (Spec (.of ℂ))] (ι : A ⟶ B) [IsOpenImmersion ι]
    [ι.IsOver (Spec (.of ℂ))] [T2Space (UnderlyingSpace ℂ A)] [T2Space (UnderlyingSpace ℂ B)]
    {k : ℤ} {β : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ A)) k}
    {x : MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ B)) k}
    (hβ : (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ((homeomorphOpensRangeMap ι : C(UnderlyingSpace ℂ A, opensRangeMap ι))))
      (homeomorphOpensRangeMap ι).isProperMap k).hom β =
      (restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ B))
        (opensRangeMap ι) k).hom x)
    {O : Opens (TopCat.of (UnderlyingSpace ℂ A))} {Wv : Opens (TopCat.of (UnderlyingSpace ℂ B))}
    (hWvR : Wv ≤ opensRangeMap ι)
    (hOO : O = Opens.comap (TopCat.ofHom ((homeomorphOpensRangeMap ι :
        C(UnderlyingSpace ℂ A, opensRangeMap ι)))).hom
      (subOpens (Y := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap ι) Wv))
    (h : TopCat.of O ⟶ TopCat.of Wv) (hh : IsProperMap h)
    (hhx : ∀ z : O, ((h z : Wv) : UnderlyingSpace ℂ B) = map (K := ℂ) ι z.1) :
    (pushforward ℚ (ModuleCat.of ℚ ℚ) h hh k).hom ((restrict ℚ (ModuleCat.of ℚ ℚ) O k).hom β) =
      (restrict ℚ (ModuleCat.of ℚ ℚ) Wv k).hom x := by
  have key1 := restrict_restrict_apply ℚ (ModuleCat.of ℚ ℚ)
    (Y := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap ι) hWvR k x
  rw [← hβ, restrict_pushforward_apply] at key1
  have hce := (subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap ι)
    hWvR).isClosedEmbedding
  apply MMP.Chow.pushforward_injective_of_isClosedEmbedding
    (subOpensMap (Y := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap ι) hWvR)
    (isProperMap_subOpensMap _ hWvR) hce
    (subOpensHomeo (Y := TopCat.of (UnderlyingSpace ℂ B)) (opensRangeMap ι) hWvR).surjective
  rw [← key1, ← pushforward_comp_apply']
  exact pushforward_restrict_congr hOO _ _ _ _ (fun z ↦ Subtype.ext (Subtype.ext (hhx z))) _ β

open MMP.UnderlyingSpace MMP.borelMooreHomology in
/-- **The curves cut by a divisor of a dominating component, as a specialized class.** For a
component `E` of `F` mapping onto `T` and a `ℚ`-divisor `L` on `E`, there are classes
`w_t ∈ H_2(F_t, ℚ)`, `t ∈ T°(ℂ)`, which at all but finitely many `t` are the sums of the classes of
the curves cut by `L` on `F_t`, and which vanish when `[L] = 0` in `H_4(E, ℚ)`: `w_t` is the
specialization `u_t ∩ [L]|_{E_{T°}}` along the family `E_{T°} → T°` (Fulton, Lemma 19.1.3, for each
component of `L` dominating `T`, the general fibres having multiplicity one; the other components
miss the general fibres). -/
private theorem exists_fibreClassFamily
    (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsLocalSystemOpen sY To) (E : F.support)
    (hE : r.base '' (E.1.support : Set Z) = (T : Set Y))
    (LE : QDivisor E.1.idealSheaf.subscheme) :
    letI := curveOver sY To
    haveI := (isSmoothVariety_curveOver hM hdim hTo).1
    haveI := (isSmoothVariety_curveOver hM hdim hTo).2
    ∀ (y : analyticSpace (To.ι ≫ curveι T ≫ sY) → UnderlyingSpace ℂ To.toScheme)
      (_ : ∀ t, (y t).toHom = t.hom)
      (u : ∀ t, cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (UnderlyingSpace ℂ To.toScheme)) {y t} ((2 * 1 : ℕ) : ℤ))
      (_ : ∀ t, IsLocalOrientationClass (T := TopCat.of (UnderlyingSpace ℂ To.toScheme)) ℚ
        curveOrientationBasis (y t) (u t))
      (hdQ : ∀ (V : Opens (analyticSpace sY)) (z : UnderlyingSpace ℂ To.toScheme),
        HasProperNeighbourhoodDeformations
          ((borelMooreHomology.inclHom (curveBaseOpens sY To V)).hom ⁻¹' {z})),
    ∃ w : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
        MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
          (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ),
      (∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
        ∀ _ : IsComplexScheme (pointFibre sY r To t),
        (LE.sum fun P c ↦ c •
          ∑ᶠ (C : {x : pointFibre sY r To t //
              relativeDimension (fieldChowSituation ℂ).dimensionFunction
                (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
            (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
              A ⊆ (pointFibreFst sY r To t).base ⁻¹'
                (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {C.1})),
            fundamentalClass C.1 C.2) = w t) ∧
      (Chow.divisorClass E.1.idealSheaf.subscheme LE = 0 → ∀ t, w t = 0) ∧
      (∀ (V : Opens (analyticSpace sY))
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
        (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
        ∀ᶠ t' in nhds t, ∀ hV' : curveOpenInclusion sY To t' ∈ V,
          fibrePairing hM t' hV' α (w t') = fibrePairing hM t hV α (w t)) ∧
      (∃ ν : ∀ V : Opens (analyticSpace sY),
          rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2 →
            MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
              (TopCat.of (curveBaseOpens sY To V)) (4 - 2),
        (∀ (V : Opens (analyticSpace sY))
          (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
          (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
          fibrePairing hM t hV α (w t) =
            @compactDegree (TopCat.of ((borelMooreHomology.inclHom
                (curveBaseOpens sY To V)).hom ⁻¹' {y t}))
              (compactSpace_preimage_singleton_inclHom _ _)
              (BorelMooreCross.congrDegree ℚ _ (by norm_num)
                (borelMooreHomology.capProductSupportPullback ℚ
                  (borelMooreHomology.inclHom (curveBaseOpens sY To V)) isClosed_singleton
                  (hdQ V (y t)) 2 (4 - 2) (u t) (ν V α)))) ∧
        (∀ (V : Opens (analyticSpace sY))
          (hVT : ∀ z ∈ V, z ∈ curvePoints sY T → z ∈ Set.range (curveBaseInclusion sY To))
          (α' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
            (preimageSpace (resolutionAnalyticMap sY r) V) (resolutionCurveSet sY r T V) 2),
          (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (curveBaseToPoints sY To V)
              (isClosedEmbedding_curveBaseToPoints sY To V hVT).1.isProperMap (4 - 2)).hom
            (ν V ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α')) =
          kernelSpecialization hM T V α'
            (componentHomologyMap E.1 4 (Chow.divisorClass E.1.idealSheaf.subscheme LE)))) := by
  classical
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  have hres := hM.isResolution
  have hY : MMP.Mori.IsVariety ℂ sY := hres.1
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hres.2.2.2.1).isProper
  obtain ⟨hirrT, hdT, hnoethT⟩ := curveScheme_facts hY hdim
  haveI := hirrT
  haveI := hnoethT
  haveI : IsIntegral (curveScheme T) :=
    MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨(T : Set Y), T.isClosed⟩ T.isIrreducible
  haveI : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  let jE := E.1.idealSheaf.subschemeι
  let j := curveι T
  choose pE hpE using exists_lift_curveScheme E.1 hE
  haveI : pE.IsOver (Spec (.of ℂ)) := ⟨by
    change pE ≫ j ≫ sY = jE ≫ Z ↘ Spec (.of ℂ)
    rw [← Category.assoc, hpE, Category.assoc, hM.comp_eq]⟩
  -- the components of `L` not dominating `T`, and their images
  let dom : Mori.PrimeDivisor E.1.idealSheaf.subscheme → Prop :=
    fun P ↦ pE.base '' (P.support : Set _) = Set.univ
  let Bad : Set (curveScheme T) :=
    ⋃ P ∈ LE.support.filter fun P ↦ ¬ dom P, pE.base '' (P.support : Set _)
  have hBad : Bad = (⋃ P ∈ LE.support.filter fun P ↦ ¬ dom P, pE.base '' (P.support : Set _) :
      Set (curveScheme T)) := rfl
  have hPcl : ∀ P : Mori.PrimeDivisor E.1.idealSheaf.subscheme,
      IsClosed (pE.base '' (P.support : Set _)) := fun P ↦ by
    have hc : IsClosed (j.base '' (pE.base '' (P.support : Set _))) := by
      rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hpE]
      exact (jE ≫ r).isClosedMap _ P.idealSheaf.support.isClosed
    exact (j.isClosedEmbedding.isClosed_iff_image_isClosed).2 hc
  have hBadcl : IsClosed Bad :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun P _ ↦ hPcl P
  letI : To.toScheme.Over (Spec (.of ℂ)) := curveOver sY To
  haveI : IsSmoothVariety ℂ (To.toScheme ↘ Spec (.of ℂ)) :=
    (isSmoothVariety_curveOver hM hdim hTo).1
  haveI := (isSmoothVariety_curveOver hM hdim hTo).2
  intro y hy
  have hpt0 : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      (t.hom ≫ To.ι).base (IsLocalRing.closedPoint ℂ) ∈ To := fun t ↦ by
    change To.ι.base (t.hom.base _) ∈ (To : Set (curveScheme T))
    rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
  have hycl := isClosed_singleton_pointImage (sY := sY) (To := To)
  have hsex : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY), ∃ s : MMP.ParameterPoint To.toScheme,
      s.point = ⟨_, hpt0 t⟩ := by
    intro t
    have ht0cl : IsClosed ({(⟨_, hpt0 t⟩ : To)} : Set To.toScheme) := by
      have : ({(⟨_, hpt0 t⟩ : To)} : Set To.toScheme) = (To.ι ≫ j).base ⁻¹' {pointImage t} := by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        constructor
        · rintro rfl; rfl
        · intro hx
          exact To.ι.isOpenEmbedding.injective (j.isClosedEmbedding.injective hx)
      rw [this]
      exact (hycl t).preimage (To.ι ≫ j).continuous
    exact ⟨MMP.ParameterPoint.ofIsClosed _ ht0cl
      (((show IsRegular To.toScheme ↔ IsLocallyNoetherian To.toScheme ∧
          ∀ y : To.toScheme, IsRegularLocalRing (To.toScheme.presheaf.stalk y)
          from (isRegular_tfae To.toScheme).out 1 2).mp
        (isRegular_of_smooth_over_field (To.toScheme ↘ Spec (.of ℂ)))).2 _),
      MMP.ParameterPoint.point_ofIsClosed _ _ _⟩
  choose s hspt using hsex
  have hst : ∀ t, (To.ι ≫ j).base (s t).point = pointImage t := fun t ↦ by rw [hspt]; rfl
  have hsy : ∀ t, (s t).complexPoint = y t := fun t ↦ by
    rw [UnderlyingSpace.eq_iff_toHom_closedPoint_eq,
      MMP.ParameterPoint.complexPoint_toHom_closedPoint, hspt t, hy t]
    rfl
  have hyfun : y = fun t ↦ (s t).complexPoint := funext fun t ↦ (hsy t).symm
  subst hyfun
  beta_reduce at hy ⊢
  intro u hu hdQ
  have h1 : SmoothOfRelativeDimension 1 (To.toScheme ↘ Spec (.of ℂ)) := dim_curveOver hM hdim hTo
  have hBadne : (Badᶜ : Set (curveScheme T)).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    obtain ⟨K, hK, hsub⟩ := isIrreducible_iff_sUnion_isClosed.1
      (IrreducibleSpace.isIrreducible_univ (curveScheme T))
      ((LE.support.filter fun P ↦ ¬ dom P).image fun P ↦ pE.base '' (P.support : Set _))
      (fun K hK ↦ by
        obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hK
        exact hPcl P) (by
        intro x _
        have hx : x ∈ Bad := h ▸ Set.mem_univ x
        rw [hBad, Set.mem_iUnion₂] at hx
        obtain ⟨P, hP, hxP⟩ := hx
        exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hP), hxP⟩)
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hK
    exact (Finset.mem_filter.1 hP).2 (Set.eq_univ_of_univ_subset hsub)
  have hB₀ne : (To : Set (curveScheme T)).Nonempty := by
    haveI : Nonempty To := hTo.connectedSpace.toNonempty
    obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty To›
    exact ⟨x, hx⟩
  -- `To` is a non-singular curve
  haveI : LocallyOfFiniteType ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (j ≫ sY); infer_instance
  haveI : QuasiCompact ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change QuasiCompact (j ≫ sY); infer_instance
  haveI : IsSeparated ((curveScheme T) ↘ Spec (.of ℂ)) := by
    change IsSeparated (j ≫ sY); infer_instance
  haveI : JacobsonSpace (curveScheme T) :=
    LocallyOfFiniteType.jacobsonSpace ((curveScheme T) ↘ Spec (.of ℂ))
  haveI : Nontrivial (curveScheme T) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := topologicalKrullDim_zero_of_discreteTopology (curveScheme T)
    rw [hdT] at h0
    exact absurd h0 (by decide)
  have hdex := nonempty_inter_closedPoints hB₀ne To.isOpen.isLocallyClosed
  let d := hdex.some
  have hdB := hdex.some_mem.1
  have hdcl := hdex.some_mem.2
  haveI : To.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hBdim : topologicalKrullDim To.toScheme = 1 := by
    haveI := (isSmoothVariety_curveOver hM hdim hTo).2
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (K := ℂ) 1
  have hB1 : SmoothOfRelativeDimension 1 (To.toScheme ↘ Spec (.of ℂ)) := h1
  -- the family `G = E ×_T To → To` of the fibres of `E`
  haveI : IsComplexScheme E.1.idealSheaf.subscheme := IsComplexScheme.of_isClosedImmersion jE
  let G : E.1.idealSheaf.subscheme.Opens := pE ⁻¹ᵁ To
  letI : G.toScheme.Over (Spec (.of ℂ)) := ⟨G.ι ≫ E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)⟩
  haveI : G.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme G.toScheme := isComplexScheme_opens G
  let g : G.toScheme ⟶ To.toScheme := pE ∣_ To
  have hg : g = (pE ∣_ To : G.toScheme ⟶ To.toScheme) := rfl
  have hgU : g ≫ To.ι = G.ι ≫ pE := morphismRestrict_ι pE To
  haveI : g.IsOver (Spec (.of ℂ)) := ⟨by
    change g ≫ To.ι ≫ ((curveScheme T) ↘ Spec (.of ℂ)) = G.ι ≫ _
    rw [← Category.assoc, hgU, Category.assoc, comp_over pE (Spec (.of ℂ))]⟩
  -- the components of `L` as surfaces of `E` and their parts over `To`
  haveI : LocallyOfFiniteType (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (jE ≫ Z ↘ Spec (.of ℂ)); infer_instance
  have hdimE : topologicalKrullDim E.1.idealSheaf.subscheme = ((2 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_component hM E]; rfl
  have hVSdim : ∀ P : Mori.PrimeDivisor E.1.idealSheaf.subscheme,
      relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = ((1 + 1 : ℕ) : ℤ) := fun P ↦ by
    refine Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
      ℂ _ _ (1 + 1) ?_
    rw [← P.support_eq_closure]
    exact topologicalKrullDim_primeDivisor_support hdimE P
  have hgpG : ∀ P : Mori.PrimeDivisor E.1.idealSheaf.subscheme, dom P → P.genericPoint ∈ G := by
    intro P hP
    obtain ⟨p, hp, hpd⟩ : d ∈ pE.base '' (P.support : Set _) := hP ▸ Set.mem_univ d
    have hpG : p ∈ G := show pE.base p ∈ To from hpd ▸ hdB
    rw [P.support_eq_closure] at hp
    exact (specializes_iff_mem_closure.mpr hp).mem_open G.isOpen hpG
  have hzdim : ∀ (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) (h : P.genericPoint ∈ G),
      relativeDimension (fieldChowSituation ℂ).dimensionFunction (G.toScheme ↘ Spec (.of ℂ))
        (⟨P.genericPoint, h⟩ : G.toScheme) = ((1 + 1 : ℕ) : ℤ) := fun P h ↦
    (Chow.relativeDimension_eq_of_isOver G.ι _).trans (hVSdim P)
  have hVGsupp : ∀ (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) (h : P.genericPoint ∈ G),
      Set.range (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι.base =
        G.ι.base ⁻¹' P.support := by
    intro P h
    erw [Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt,
      P.support_eq_closure, G.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
        G.ι.continuous]
    congr 1
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun hz ↦ by subst hz; rfl, fun hz ↦ G.ι.isOpenEmbedding.injective (hz.trans rfl)⟩
  have hVGsurj : ∀ P : Mori.PrimeDivisor E.1.idealSheaf.subscheme, dom P →
      ∀ h : P.genericPoint ∈ G,
        Function.Surjective
          ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g).base := by
    intro P hP h b
    obtain ⟨p, hp, hpb⟩ : b.1 ∈ pE.base '' (P.support : Set _) := hP ▸ Set.mem_univ _
    have hpG : pE.base p ∈ To := hpb ▸ b.2
    have hmem : (⟨p, hpG⟩ : G.toScheme) ∈
        Set.range (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι.base := by
      rw [hVGsupp]
      exact hp
    obtain ⟨v, hv⟩ := hmem
    refine ⟨v, To.ι.isOpenEmbedding.injective ?_⟩
    change (((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g) ≫ To.ι).base v =
      To.ι.base b
    rw [Category.assoc, hgU, ← Category.assoc, Scheme.Hom.comp_base, TopCat.comp_app,
      Scheme.Hom.comp_base, TopCat.comp_app, hv]
    exact hpb
  -- generic multiplicity one along each dominating component
  haveI : Nonempty To.toScheme := ⟨⟨d, hdB⟩⟩
  haveI : IsIntegral To.toScheme := isIntegral_of_isOpenImmersion To.ι
  haveI : LocallyOfFiniteType (To.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (To.ι ≫ _); infer_instance
  haveI : QuasiCompact (To.toScheme ↘ Spec (.of ℂ)) := by
    change QuasiCompact (To.ι ≫ _); infer_instance
  haveI : Nontrivial To.toScheme := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have h0 := topologicalKrullDim_zero_of_discreteTopology To.toScheme
    rw [hBdim] at h0
    exact absurd h0 (by decide)
  have hmultW : ∀ (P : Mori.PrimeDivisor E.1.idealSheaf.subscheme) (hP : dom P),
      ∃ W : Set To.toScheme, IsOpen W ∧ W.Nonempty ∧ ∀ s : MMP.ParameterPoint To.toScheme,
        s.point ∈ W → ∀ ξ : genericPoints (MMP.ParameterPoint.fibre
          ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩).subschemeι ≫ g) s),
          relativeDimension (fieldChowSituation ℂ).dimensionFunction
            (MMP.ParameterPoint.fibre
              ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩).subschemeι ≫ g) s ↘
                Spec (.of ℂ)) ξ.1 = (1 : ℕ) →
          componentMultiplicity (𝟙 _) ξ = 1 := by
    intro P hP
    haveI : IsDominant ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩).subschemeι ≫ g) :=
      ⟨(hVGsurj P hP (hgpG P hP)).denseRange⟩
    haveI := Stacks.Chow.isIntegral_integralComponentAt (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩
    have hdn : topologicalKrullDim (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩).subscheme =
        ((2 : ℕ) : WithBot ℕ∞) := by
      have h0 := Chow.dimension_integralComponentAt (Y := G.toScheme)
        (⟨P.genericPoint, hgpG P hP⟩ : G.toScheme)
      rw [hzdim P (hgpG P hP)] at h0
      exact h0
    exact exists_isOpen_forall_componentMultiplicity_eq_one _ hdn
  -- the classes of the components of `L` over `To`, and their vanishing combination
  let γ : Mori.PrimeDivisor E.1.idealSheaf.subscheme →
      MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (UnderlyingSpace ℂ G.toScheme)) (2 * (1 + 1) : ℕ) :=
    fun P ↦ if h : P.genericPoint ∈ G then
      Chow.pointCycleClass ℚ (X := G.toScheme) ⟨P.genericPoint, h⟩ (hzdim P h) else 0
  have hγ : γ = (fun P ↦ if h : P.genericPoint ∈ G then
      Chow.pointCycleClass ℚ (X := G.toScheme) ⟨P.genericPoint, h⟩ (hzdim P h) else 0 :
      Mori.PrimeDivisor E.1.idealSheaf.subscheme →
      MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (UnderlyingSpace ℂ G.toScheme)) (2 * (1 + 1) : ℕ)) := rfl
  have hHinj : Function.Injective (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ((homeomorphOpensRangeMap G.ι : C(UnderlyingSpace ℂ G.toScheme,
        opensRangeMap G.ι))))
      (homeomorphOpensRangeMap G.ι).isProperMap (2 * (1 + 1) : ℕ)).hom :=
    MMP.Chow.pushforward_injective_of_isClosedEmbedding _ _
      (homeomorphOpensRangeMap G.ι).isClosedEmbedding (homeomorphOpensRangeMap G.ι).surjective _
  have hβrel : (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ((homeomorphOpensRangeMap G.ι : C(UnderlyingSpace ℂ G.toScheme,
        opensRangeMap G.ι))))
      (homeomorphOpensRangeMap G.ι).isProperMap (2 * (1 + 1) : ℕ)).hom
        (LE.sum fun P c ↦ c • γ P) =
      restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme))
        (opensRangeMap G.ι) (2 * (1 + 1) : ℕ)
        (Chow.divisorClass E.1.idealSheaf.subscheme LE) := by
    have hP : ∀ P : Mori.PrimeDivisor E.1.idealSheaf.subscheme,
        (pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ((homeomorphOpensRangeMap G.ι : C(UnderlyingSpace ℂ G.toScheme,
            opensRangeMap G.ι))))
          (homeomorphOpensRangeMap G.ι).isProperMap (2 * (1 + 1) : ℕ)).hom (γ P) =
        restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme))
          (opensRangeMap G.ι) (2 * (1 + 1) : ℕ)
          (Chow.pointCycleClass ℚ P.genericPoint (hVSdim P)) := by
      intro P
      by_cases h : P.genericPoint ∈ G
      · simp only [hγ, dif_pos h]
        exact (Chow.restrict_pointCycleClass_eq_pushforward ℚ G.ι (⟨P.genericPoint, h⟩ : G.toScheme)
          (hVSdim P) (hzdim P h)).symm
      · simp only [hγ, dif_neg h, map_zero]
        refine (Chow.restrict_pointCycleClass_eq_zero_of_notMem ℚ G.ι _ (hVSdim P) ?_).symm
        rw [Scheme.Opens.range_ι]
        exact h
    have hdc : Chow.divisorClass E.1.idealSheaf.subscheme LE =
        LE.sum fun P c ↦ c • Chow.pointCycleClass ℚ P.genericPoint (hVSdim P) := by
      conv_lhs => rw [← Finsupp.sum_single LE]
      rw [map_finsuppSum]
      refine Finsupp.sum_congr fun P _ ↦ ?_
      rw [← Finsupp.smul_single_one, map_smul, Chow.divisorClass_single (hVSdim P)]
    rw [hdc, Finsupp.sum, map_sum, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun P _ ↦
      (map_smul _ _ _).trans ((congrArg _ (hP P)).trans (map_smul _ _ _).symm)
  -- the good points of `T°`
  choose W hWo hWne hWmult using hmultW
  have hev : ∀ P ∈ LE.support, ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
      ∀ hP : dom P, (t.hom ≫ To.ι).base (IsLocalRing.closedPoint ℂ) ∈ To.ι.base '' W P hP := by
    intro P _
    by_cases hP : dom P
    · filter_upwards [eventually_mem_of_isOpen (To := To) hY hdim
        (To.ι.isOpenEmbedding.isOpenMap _ (hWo P hP)) ((hWne P hP).image _)] with t ht _
      exact ht
    · exact Filter.Eventually.of_forall fun t hP' ↦ absurd hP' hP
  -- the per-point data: the parameter point, the orientation class and the map into `F_t`
  have hor := isOrientedAtlas_of_isManifold_complex
    (E := EuclideanSpace ℂ (Fin 1))
    (TopCat.of (UnderlyingSpace ℂ To.toScheme))
  let jG : G.toScheme ⟶ Z := G.ι ≫ jE
  have hjG : jG = (G.ι ≫ jE : G.toScheme ⟶ Z) := rfl
  have hcomm : g ≫ (To.ι ≫ j) = jG ≫ r := by
    rw [← Category.assoc, hgU, Category.assoc, hpE, hjG, Category.assoc]
  have hprop : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY), IsProperMap fun x :
      ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹' {(s t).complexPoint}) ↦ map (K := ℂ) jG x.1 := by
    intro t
    have hemb : Topology.IsEmbedding fun x : ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹'
        {(s t).complexPoint}) ↦ map (K := ℂ) G.ι x.1 :=
      (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) G.ι).isEmbedding.comp
        Topology.IsEmbedding.subtypeVal
    have hrange : Set.range (fun x : ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹'
        {(s t).complexPoint}) ↦ map (K := ℂ) G.ι x.1) =
        pointsOver (K := ℂ) (pE.base ⁻¹' {To.ι.base (s t).point}) := by
      have hgx : ∀ x : UnderlyingSpace ℂ G.toScheme, pE.base (G.ι.base (x.toHom.base
          (IsLocalRing.closedPoint ℂ))) = To.ι.base (g.base (x.toHom.base
            (IsLocalRing.closedPoint ℂ))) := fun x ↦ by
        change (G.ι ≫ pE).base _ = (g ≫ To.ι).base _
        rw [hgU]
      have hgs : ∀ x : UnderlyingSpace ℂ G.toScheme, map (K := ℂ) g x = (s t).complexPoint ↔
          g.base (x.toHom.base (IsLocalRing.closedPoint ℂ)) = (s t).point := fun x ↦ by
        rw [UnderlyingSpace.eq_iff_toHom_closedPoint_eq,
          MMP.ParameterPoint.complexPoint_toHom_closedPoint]
        rfl
      ext e
      constructor
      · rintro ⟨x, rfl⟩
        change pE.base (G.ι.base (x.1.toHom.base (IsLocalRing.closedPoint ℂ))) = _
        rw [hgx, (hgs x.1).1 x.2]
      · intro he
        have he' : pE.base (e.toHom.base (IsLocalRing.closedPoint ℂ)) = To.ι.base (s t).point := he
        have heG : e ∈ Set.range (mapFun (K := ℂ) G.ι) := by
          rw [range_mapFun_of_isOpenImmersion]
          refine (top_le_preimage_iff e _).2 ?_
          rw [Scheme.Opens.opensRange_ι]
          change pE.base (e.toHom.base (IsLocalRing.closedPoint ℂ)) ∈ To
          rw [he']
          exact (s t).point.2
        obtain ⟨x, rfl⟩ := heG
        refine ⟨⟨x, (hgs x).2 (To.ι.isOpenEmbedding.injective ?_)⟩, rfl⟩
        rw [← hgx]
        exact he'
    have ht₀cl : IsClosed ({To.ι.base (s t).point} : Set (curveScheme T)) := by
      have he : ({To.ι.base (s t).point} : Set (curveScheme T)) = j.base ⁻¹' {pointImage t} := by
        ext x
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        rw [← hst t]
        exact ⟨fun h ↦ h ▸ rfl, fun h ↦ j.isClosedEmbedding.injective h⟩
      rw [he]
      exact (hycl t).preimage j.continuous
    have hcl : IsClosed (pointsOver (K := ℂ) (pE.base ⁻¹' {To.ι.base (s t).point})) :=
      isClosed_pointsOver (ht₀cl.preimage pE.continuous)
    have hce : Topology.IsClosedEmbedding fun x : ((TopCat.ofHom (map (K := ℂ) g)).hom ⁻¹'
        {(s t).complexPoint}) ↦ map (K := ℂ) G.ι x.1 :=
      ⟨hemb, hrange ▸ hcl⟩
    have hjGm : ∀ x, map (K := ℂ) jG x = map (K := ℂ) jE (map (K := ℂ) G.ι x) := fun x ↦
      UnderlyingSpace.ext (by rw [toHom_map, toHom_map, toHom_map, hjG, Category.assoc])
    simp_rw [hjGm]
    exact (isProperMap_map (K := ℂ) jE).comp hce.isProperMap
  have hkex := fun t : analyticSpace (To.ι ≫ curveι T ≫ sY) ↦
    exists_isProperMap_fibrePoints_pointFibre hM.comp_eq t (To.ι ≫ j) g jG hcomm (s t)
      (hst t) (hprop t)
  choose k hk hkx using hkex
  have hjBinj : Function.Injective (To.ι ≫ j).base :=
    j.isClosedEmbedding.injective.comp To.ι.isOpenEmbedding.injective
  -- the specialization map at `t`
  let Φ := fun t : analyticSpace (To.ι ≫ curveι T ≫ sY) ↦
    (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩)
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap (2 * 1 : ℕ)).hom ∘ₗ
    (pushforward ℚ (ModuleCat.of ℚ ℚ) (k t) (hk t) (2 * 1 : ℕ)).hom ∘ₗ
    (BorelMooreCross.congrDegree ℚ _ (by norm_num)).toLinearMap ∘ₗ
    capProductSupportPullback ℚ (TopCat.ofHom (map (K := ℂ) g)) isClosed_singleton
      (hasProperNeighbourhoodDeformations_preimage_singleton g _) (2 * 1 : ℕ)
      (2 * (1 + 1) : ℕ) (u t)
  have hΦapp : ∀ t x, Φ t x = (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩)
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap (2 * 1 : ℕ)).hom
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (k t) (hk t) (2 * 1 : ℕ)).hom
        (BorelMooreCross.congrDegree ℚ _ (by norm_num)
          (capProductSupportPullback ℚ (TopCat.ofHom (map (K := ℂ) g)) isClosed_singleton
            (hasProperNeighbourhoodDeformations_preimage_singleton g _) (2 * 1 : ℕ)
            (2 * (1 + 1) : ℕ) (u t) x))) := fun _ _ ↦ rfl
  let β := LE.sum fun P c ↦ c • γ P
  have hβ : β = LE.sum fun P c ↦ c • γ P := rfl
  -- the classes read on the base
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective _ hM.isProjectiveVariety.isProjective.isProjective
  haveI : IsComplexScheme (curveScheme T) := IsComplexScheme.of_isClosedImmersion j
  haveI : IsComplexScheme To.toScheme := isComplexScheme_opens To
  haveI : IsProper (pE ≫ j) := by rw [hpE]; infer_instance
  haveI : IsProper pE := IsProper.of_comp pE j
  haveI : IsProper g := by rw [hg]; infer_instance
  have hgp : IsProperMap (TopCat.ofHom (map (K := ℂ) g)) := isProperMap_map (K := ℂ) g
  have hy' : ∀ t', (s t').complexPoint.toHom = t'.hom := hy
  have hsc : ∀ t', curveBaseInclusion sY To (s t').complexPoint = curveOpenInclusion sY To t' :=
    fun t' ↦ ComplexPoints.ext (by rw [curveBaseInclusion_hom, hy' t']; rfl)
  have hQmem : ∀ (V : Opens (analyticSpace sY)) t', curveOpenInclusion sY To t' ∈ V →
      (s t').complexPoint ∈ curveBaseOpens sY To V := fun V t' h ↦ by
    change curveBaseInclusion sY To (s t').complexPoint ∈ V
    rw [hsc]
    exact h
  -- the inclusion of `O = g⁻¹(Q)` into `r⁻¹(V)`
  have hOV : ∀ (V : Opens (analyticSpace sY))
      (x : MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) (curveBaseOpens sY To V)),
      resolutionAnalyticMap sY r (toResolutionSpace hM (map (K := ℂ) jG x.1)) ∈ V := by
    intro V x
    have hx : curveBaseInclusion sY To (map (K := ℂ) g x.1) ∈ V := x.2
    have heq : resolutionAnalyticMap sY r (toResolutionSpace hM (map (K := ℂ) jG x.1)) =
        curveBaseInclusion sY To (map (K := ℂ) g x.1) := ComplexPoints.ext (by
      change (toResolutionSpace hM _).hom ≫ r = _
      rw [toResolutionSpace_hom, curveBaseInclusion_hom, toHom_map, toHom_map, Category.assoc,
        ← hcomm]
      rfl)
    rw [heq]
    exact hx
  let ιO : ∀ V : Opens (analyticSpace sY),
      TopCat.of (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g))
        (curveBaseOpens sY To V)) ⟶
        preimageSpace (resolutionAnalyticMap sY r) V := fun V ↦
    TopCat.ofHom ⟨fun x ↦ ⟨toResolutionSpace hM (map (K := ℂ) jG x.1), hOV V x⟩,
      ((toResolutionSpace hM).hom.continuous.comp
        ((map (K := ℂ) jG).continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let ν : ∀ V : Opens (analyticSpace sY),
      rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2 →
        MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.of (curveBaseOpens sY To V)) (4 - 2) := fun V α ↦
    (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) (curveBaseOpens sY To V))
      (isProperMap_restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) _ hgp) (4 - 2)).hom
      (borelMooreHomology.capProduct ℚ _ Set.univ 2 4 (absPullback (ιO V) 2 α)
        ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g))
          (curveBaseOpens sY To V)) 4).hom β))
  have hν : ν = (fun V α ↦
    (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) (curveBaseOpens sY To V))
      (isProperMap_restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) _ hgp) (4 - 2)).hom
      (borelMooreHomology.capProduct ℚ _ Set.univ 2 4 (absPullback (ιO V) 2 α)
        ((restrict ℚ (ModuleCat.of ℚ ℚ) (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g))
          (curveBaseOpens sY To V)) 4).hom β)) : ∀ V : Opens (analyticSpace sY),
      rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2 →
        MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.of (curveBaseOpens sY To V)) (4 - 2)) := rfl
  -- the pairing at `t'`, read on `Q`
  have hCMP : ∀ (V : Opens (analyticSpace sY))
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) t'
      (hV' : curveOpenInclusion sY To t' ∈ V),
      fibrePairing hM t' hV' α (Φ t' β) =
        @compactDegree (TopCat.of ((inclHom (curveBaseOpens sY To V)).hom ⁻¹'
            {(s t').complexPoint}))
          (compactSpace_preimage_singleton_inclHom _ _)
          (BorelMooreCross.congrDegree ℚ _ (by norm_num)
            (capProductSupportPullback ℚ (inclHom (curveBaseOpens sY To V)) isClosed_singleton
              (hdQ V _) 2 (4 - 2) (u t') (ν V α))) := by
    intro V α t' hV'
    simp only [hν]
    let Q := curveBaseOpens sY To V
    have hQ : Q = curveBaseOpens sY To V := rfl
    have hyQ := hQmem V t' hV'
    haveI : CompactSpace ((TopCat.ofHom (map (K := ℂ) g)) ⁻¹' {(s t').complexPoint}) :=
      isCompact_iff_compactSpace.1 (hgp.isCompact_preimage isCompact_singleton)
    have hdP := hasProperNeighbourhoodDeformations_preimage_singleton g (s t').complexPoint
    have hdO : HasProperNeighbourhoodDeformations
        ((inclHom (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q)).hom ⁻¹'
          ((TopCat.ofHom (map (K := ℂ) g)) ⁻¹' {(s t').complexPoint})) :=
      hasProperNeighbourhoodDeformations_preimage_val
        (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q).isOpen
        hdP (fun x hx ↦ show (TopCat.ofHom (map (K := ℂ) g)) x ∈ Q from
          (Set.mem_singleton_iff.1 hx).symm ▸ hyQ)
    haveI := compactSpace_pointFibre hM t'
    let f : TopCat.of ((TopCat.ofHom (map (K := ℂ) g)) ⁻¹' {(s t').complexPoint}) ⟶
        analyticSpace (pointFibre sY r To t' ↘ Spec (.of ℂ)) :=
      k t' ≫ TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩
    have hγ : absPullback f 2
          ((rationalCohomologyMap (pointFibreInclusion sY r To t' hV') 2).hom α) =
        absPullback (TopCat.ofHom ⟨fun x : (TopCat.ofHom (map (K := ℂ) g)) ⁻¹'
            {(s t').complexPoint} ↦
          (⟨x.1, show (TopCat.ofHom (map (K := ℂ) g)) x.1 ∈ Q from
              (Set.mem_singleton_iff.1 x.2).symm ▸ hyQ⟩ :
            MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q), by fun_prop⟩ :
            TopCat.of ((TopCat.ofHom (map (K := ℂ) g)) ⁻¹' {(s t').complexPoint}) ⟶
              TopCat.of (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q))
          2 (absPullback (ιO V) 2 α) := by
      change absPullback f 2 (absPullback (pointFibreInclusion sY r To t' hV') 2 α) = _
      have hmap : f ≫ pointFibreInclusion sY r To t' hV' = (TopCat.ofHom ⟨fun x :
          (TopCat.ofHom (map (K := ℂ) g)) ⁻¹' {(s t').complexPoint} ↦
          (⟨x.1, show (TopCat.ofHom (map (K := ℂ) g)) x.1 ∈ Q from
            (Set.mem_singleton_iff.1 x.2).symm ▸ hyQ⟩ :
            MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q), by fun_prop⟩ :
            TopCat.of ((TopCat.ofHom (map (K := ℂ) g)) ⁻¹' {(s t').complexPoint}) ⟶
              TopCat.of (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q)) ≫ ιO V := by
        refine ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (ComplexPoints.ext ?_)
        change ((ComplexPoints.homeomorphUnderlyingSpace).symm (k t' x)).hom ≫
          pointFibreFst sY r To t' = (toResolutionSpace hM (map (K := ℂ) jG x.1)).hom
        rw [toResolutionSpace_hom, ← hkx t' x, toHom_map]
        rfl
      exact (absPullback_comp _ _ _ _).symm.trans
        ((congrArg (fun φ ↦ absPullback φ 2 α) hmap).trans (absPullback_comp _ _ _ _))
    refine (congrArg (fibrePairing hM t' hV' α) (hΦapp t' β)).trans ?_
    unfold fibrePairing
    have key := compactDegree_capProduct_pushforward_pushforward_eq _ hgp Q hyQ hdP hdO (hdQ V _)
      (k t') (hk t') (TopCat.ofHom ⟨_, ComplexPoints.homeomorphUnderlyingSpace.symm.continuous⟩)
      ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap _
      (absPullback (ιO V) 2 α) hγ (u t') β
    with_reducible exact key
  refine ⟨fun t ↦ Φ t β, ?_, fun hLE t ↦ ?_, ?_, ν, ?_, ?_⟩
  all_goals try beta_reduce
  rotate_left
  · have hβ0 : β = 0 := hHinj ((hβrel.trans (by rw [hLE, map_zero])).trans (map_zero _).symm)
    change Φ t β = 0
    rw [hβ0, map_zero]
  · intro V α t hV
    have hev := eventually_compactDegree_capProductSupportPullback_eq_of_eq hor (by norm_num)
      curveOrientationBasis (curveBaseOpens sY To V) (hdQ V) (j := 2) (k := 4 - 2)
      (by norm_num) (by norm_num) (ν V α) (hQmem V t hV) (u t) (hu t)
    have hcont : Filter.Tendsto (fun t' ↦ (s t').complexPoint) (nhds t)
        (nhds (s t).complexPoint) := by
      have hfun : (fun t' ↦ (s t').complexPoint) =
          fun t' ↦ homeomorphUnderlyingSpace (X := To.toScheme) t' :=
        funext fun t' ↦ UnderlyingSpace.ext (hy' t')
      rw [hfun, show (s t).complexPoint = homeomorphUnderlyingSpace (X := To.toScheme) t from
        UnderlyingSpace.ext (hy' t)]
      exact (homeomorphUnderlyingSpace (X := To.toScheme)).continuous.tendsto t
    filter_upwards [hcont.eventually hev] with t' ht' hV'
    have h3 := ht' (u t') (hu t')
    with_reducible exact (hCMP V α t' hV').trans (h3.trans (hCMP V α t hV).symm)
  · with_reducible exact hCMP
  · intro V hVT α'
    haveI : T2Space (analyticSpace (r ≫ sY)) := (resolutionSpaceHomeomorph hM).isEmbedding.t2Space
    let c := (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α'
    have hc : c = (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α' := rfl
    let Q := curveBaseOpens sY To V
    have hQ : Q = curveBaseOpens sY To V := rfl
    have hjEp : IsProperMap (TopCat.ofHom (map (K := ℂ) jE) ≫ toResolutionSpace hM) :=
      (isProperMap_toResolutionSpace hM).comp (isProperMap_map (K := ℂ) jE)
    let jEan := TopCat.ofHom (map (K := ℂ) jE) ≫ toResolutionSpace hM
    let Zv : Opens (analyticSpace (r ≫ sY)) := Opens.comap (resolutionAnalyticMap sY r).hom V
    let Wv : Opens (TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme)) :=
      Opens.comap jEan.hom Zv
    let ιE : TopCat.of Wv ⟶ preimageSpace (resolutionAnalyticMap sY r) V :=
      restrictPreimage jEan Zv
    -- the image of a point of `E`
    have hjEr : ∀ x : UnderlyingSpace ℂ E.1.idealSheaf.subscheme,
        (resolutionAnalyticMap sY r (jEan x)).hom = x.toHom ≫ jE ≫ r := fun x ↦ by
      change (toResolutionSpace hM (map (K := ℂ) jE x)).hom ≫ r = _
      rw [toResolutionSpace_hom, toHom_map, Category.assoc]
    have hET : ∀ x : UnderlyingSpace ℂ E.1.idealSheaf.subscheme,
        resolutionAnalyticMap sY r (jEan x) ∈ curvePoints sY T := fun x ↦ by
      change (resolutionAnalyticMap sY r (jEan x)).hom.base (IsLocalRing.closedPoint ℂ) ∈
        (T : Set Y)
      rw [hjEr, ← hE]
      refine ⟨jE.base (x.toHom.base (IsLocalRing.closedPoint ℂ)), ?_, rfl⟩
      exact (E.1.idealSheaf.range_subschemeι).subset ⟨_, rfl⟩
    -- `q : W_V → V ∩ T`
    let q : TopCat.of Wv ⟶ TopCat.of (curvePointsIn sY T V) :=
      TopCat.ofHom ⟨fun w ↦ ⟨⟨resolutionAnalyticMap sY r (jEan w.1), w.2⟩, hET w.1⟩,
        ((((resolutionAnalyticMap sY r).hom.continuous.comp
          (jEan.hom.continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _)⟩
    -- `h : O → W_V`
    have hhmem : ∀ x : MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q,
        map (K := ℂ) G.ι x.1 ∈ Wv := fun x ↦ by
      have hmap : jEan (map (K := ℂ) G.ι x.1) = toResolutionSpace hM (map (K := ℂ) jG x.1) :=
        ComplexPoints.ext (by
          change (toResolutionSpace hM (map (K := ℂ) jE (map (K := ℂ) G.ι x.1))).hom = _
          rw [toResolutionSpace_hom, toResolutionSpace_hom, toHom_map, toHom_map, toHom_map, hjG,
            Category.assoc])
      change resolutionAnalyticMap sY r (jEan (map (K := ℂ) G.ι x.1)) ∈ V
      rw [hmap]
      exact hOV V x
    let hmap' : TopCat.of (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q) ⟶
        TopCat.of Wv :=
      TopCat.ofHom ⟨fun x ↦ ⟨map (K := ℂ) G.ι x.1, hhmem x⟩,
        ((map (K := ℂ) G.ι).continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hbase : ∀ x : UnderlyingSpace ℂ G.toScheme,
        resolutionAnalyticMap sY r (jEan (map (K := ℂ) G.ι x)) =
          curveBaseInclusion sY To (map (K := ℂ) g x) := fun x ↦ ComplexPoints.ext (by
      rw [hjEr, curveBaseInclusion_hom, toHom_map, toHom_map, Category.assoc, ← Category.assoc G.ι,
        ← hjG, ← hcomm]
      rfl)
    -- `h` is a homeomorphism
    have hsurj' : Function.Surjective hmap' := by
      rintro ⟨w, hw⟩
      have hwV : resolutionAnalyticMap sY r (jEan w) ∈ V := hw
      obtain ⟨b, hb⟩ := hVT _ hwV (hET w)
      have hb' : b.toHom ≫ To.ι ≫ j = w.toHom ≫ pE ≫ j := by
        have := congrArg ComplexPoints.hom hb
        rw [curveBaseInclusion_hom, hjEr, ← hpE] at this
        exact this
      have hpt : pE.base (w.toHom.base (IsLocalRing.closedPoint ℂ)) ∈ To := by
        have h2 := congrArg (fun φ : Spec (.of ℂ) ⟶ Y ↦ φ.base (IsLocalRing.closedPoint ℂ)) hb'
        simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
        have h3 := j.isClosedEmbedding.injective h2
        have h4 : To.ι.base (b.toHom.base (IsLocalRing.closedPoint ℂ)) ∈ To :=
          (b.toHom.base (IsLocalRing.closedPoint ℂ)).2
        exact h3 ▸ h4
      have hwG : w ∈ Set.range (mapFun (K := ℂ) G.ι) := by
        rw [range_mapFun_of_isOpenImmersion]
        refine (top_le_preimage_iff w _).2 ?_
        rw [Scheme.Opens.opensRange_ι]
        exact hpt
      obtain ⟨x, rfl⟩ := hwG
      have hxO : (TopCat.ofHom (map (K := ℂ) g)) x ∈ Q := by
        change curveBaseInclusion sY To (map (K := ℂ) g x) ∈ V
        rw [← hbase]
        exact hwV
      exact ⟨⟨x, hxO⟩, rfl⟩
    have hemb' : Topology.IsEmbedding hmap' := by
      have h1 := (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) G.ι).isEmbedding.comp
        (Topology.IsEmbedding.subtypeVal (p := (· ∈ (MMP.Fourfold.preimageOpens
          (TopCat.ofHom (map (K := ℂ) g)) Q : Set (TopCat.of (UnderlyingSpace ℂ G.toScheme))))))
      exact h1.codRestrict (Wv : Set (TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme))) _
    have hhp : IsProperMap hmap' := (hemb'.toHomeomorphOfSurjective hsurj').isProperMap
    -- the restriction of `[L]` to `W_V` is read on `O`
    have hWvR : Wv ≤ (opensRangeMap G.ι :
        Opens (TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme))) := fun w hw ↦ by
      obtain ⟨⟨x, hx⟩, hxw⟩ := hsurj' ⟨w, hw⟩
      exact ⟨x, congrArg Subtype.val hxw⟩
    have hE3 : (pushforward ℚ (ModuleCat.of ℚ ℚ) hmap' hhp (2 * (1 + 1) : ℕ)).hom
        ((restrict ℚ (ModuleCat.of ℚ ℚ)
          (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q)
          (2 * (1 + 1) : ℕ)).hom β) =
        (restrict ℚ (ModuleCat.of ℚ ℚ) Wv (2 * (1 + 1) : ℕ)).hom
          (Chow.divisorClass E.1.idealSheaf.subscheme LE) := by
      refine pushforward_restrict_eq_restrict_of_opensRangeMap G.ι hβrel hWvR ?_ hmap' hhp
        fun z ↦ rfl
      ext x
      change curveBaseInclusion sY To (map (K := ℂ) g x) ∈ V ↔
        resolutionAnalyticMap sY r (jEan (map (K := ℂ) G.ι x)) ∈ V
      rw [hbase]
    -- the maps to `V ∩ T`
    have hιO' : ιO V = hmap' ≫ ιE :=
      ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (ComplexPoints.ext (by
        change (toResolutionSpace hM (map (K := ℂ) jG x.1)).hom =
          (toResolutionSpace hM (map (K := ℂ) jE (map (K := ℂ) G.ι x.1))).hom
        rw [toResolutionSpace_hom, toResolutionSpace_hom, toHom_map, toHom_map, toHom_map, hjG,
          Category.assoc]))
    have hgq : restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) Q ≫ curveBaseToPoints sY To V =
        hmap' ≫ q :=
      ConcreteCategory.hom_ext _ _ fun x ↦ Subtype.ext (Subtype.ext (hbase x.1).symm)
    have hqp : IsProperMap q := isProperMap_componentCurveMap hM T V E.1 hET
    let X := (pushforward ℚ (ModuleCat.of ℚ ℚ) q hqp (4 - 2)).hom
      (borelMooreHomology.capProduct ℚ _ Set.univ 2 4
        (absPullback ιE 2 c)
        ((restrict ℚ (ModuleCat.of ℚ ℚ) Wv 4).hom (Chow.divisorClass E.1.idealSheaf.subscheme LE)))
    have hE3' : (pushforward ℚ (ModuleCat.of ℚ ℚ) hmap' hhp 4).hom
        ((restrict ℚ (ModuleCat.of ℚ ℚ)
          (MMP.Fourfold.preimageOpens (TopCat.ofHom (map (K := ℂ) g)) Q)
          4).hom β) =
        (restrict ℚ (ModuleCat.of ℚ ℚ) Wv 4).hom (Chow.divisorClass E.1.idealSheaf.subscheme LE) := hE3
    have hL : (pushforward ℚ (ModuleCat.of ℚ ℚ) (curveBaseToPoints sY To V)
        (isClosedEmbedding_curveBaseToPoints sY To V hVT).1.isProperMap (4 - 2)).hom (ν V c) =
          X := by
      simp only [hν]
      have hL' := pushforward_pushforward_capProduct_absPullback_eq
        (restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) Q)
        (isProperMap_restrictPreimage (TopCat.ofHom (map (K := ℂ) g)) _ hgp)
        (curveBaseToPoints sY To V) (isClosedEmbedding_curveBaseToPoints sY To V hVT).1.isProperMap
        hmap' hhp q hqp (ιO V) ιE hgq hιO' c _ _ hE3'
      with_reducible exact hL'
    have hR : kernelSpecialization hM T V α'
        (componentHomologyMap E.1 4 (Chow.divisorClass E.1.idealSheaf.subscheme LE)) = X :=
      by
        have hR' := kernelSpecialization_componentHomologyMap_eq_pushforward hM T V E.1 hET α'
          (Chow.divisorClass E.1.idealSheaf.subscheme LE)
        exact hR'
    exact hL.trans hR.symm
  filter_upwards [eventually_mem_of_isOpen (To := To) hY hdim hBadcl.isOpen_compl hBadne,
    (Filter.eventually_all_finset LE.support).2 hev] with t htBad htW inst
  let t₀ := (t.hom ≫ To.ι).base (IsLocalRing.closedPoint ℂ)
  have hyt : j.base t₀ = pointImage t := rfl
  haveI := isClosedImmersion_point t
  haveI := pointFibreFst_isOver hM.comp_eq t
  haveI := isClosedImmersion_pointFibreFst (r := r) t
  have hXP : ∀ P ∈ LE.support,
      (∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
        (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
          A ⊆ (pointFibreFst sY r To t).base ⁻¹'
            (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
          (closure {C.1})),
        fundamentalClass C.1 C.2) = (Φ t) (γ P) := by
    intro P hPs
    have hPZcl : IsClosed (jE.base '' (P.support : Set _)) :=
      jE.isClosedMap _ P.idealSheaf.support.isClosed
    by_cases hP : dom P
    · have hγP : γ P = Chow.pointCycleClass ℚ (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩
          (hzdim P (hgpG P hP)) := by
        simp only [hγ, dif_pos (hgpG P hP)]
      have hsupp := hVGsupp P (hgpG P hP)
      have hsurj := hVGsurj P hP (hgpG P hP)
      have hmultP := hWmult P hP
      set ι := (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, hgpG P hP⟩).subschemeι with hιdef
      haveI : IsDominant (ι ≫ g) := ⟨hsurj.denseRange⟩
      have h1 : Set.range (ι ≫ jG).base ⊆ jE.base '' (P.support : Set _) := by
        rintro _ ⟨v, rfl⟩
        have hv : ι.base v ∈ Set.range ι.base := ⟨v, rfl⟩
        rw [hsupp] at hv
        exact ⟨_, hv, rfl⟩
      have h2 : jE.base '' (P.support : Set _) ∩ r.base ⁻¹' Set.range (To.ι ≫ j).base ⊆
          Set.range (ι ≫ jG).base := by
        rintro _ ⟨⟨p, hp, rfl⟩, ⟨b, hb⟩⟩
        have hpb : pE.base p = To.ι.base b := by
          apply j.isClosedEmbedding.injective
          change (pE ≫ j).base p = (To.ι ≫ j).base b
          rw [hb, hpE]; rfl
        have hpG : pE.base p ∈ To := hpb ▸ b.2
        have hmem : (⟨p, hpG⟩ : G.toScheme) ∈ Set.range ι.base := by
          rw [hsupp]
          exact hp
        obtain ⟨v, hv⟩ := hmem
        exact ⟨v, by change jE.base (G.ι.base (ι.base v)) = _; rw [hv]; rfl⟩
      have hptcl : IsClosed {(To.ι ≫ j).base (s t).point} := by rw [(hst t)]; exact (hycl t)
      haveI : IsPreimmersion (ι ≫ jG) := by rw [hjG]; infer_instance
      haveI : IsClosedImmersion (MMP.ParameterPoint.fibreι (ι ≫ g) (s t) ≫ ι ≫ jG) :=
        isClosedImmersion_fibreι_comp_of_range (ι ≫ g) ι jG (To.ι ≫ j) r hjBinj
          (by rw [Category.assoc, hcomm]; simp only [hjG, Category.assoc]) hPZcl h1 h2 (s t) hptcl
      obtain ⟨i, hi, hic, hio⟩ :=
        exists_isClosedImmersion_fibre_pointFibre t (To.ι ≫ j) rfl g jG hcomm ι (s t) (hst t)
      haveI := hic
      haveI := hio
      have hki : fibreAmbientPointsHom ι g rfl (s t) ≫ (k t) =
          TopCat.ofHom (map (K := ℂ) i) := by
        ext p : 1
        apply (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
          (pointFibreFst sY r To t)).injective
        rw [ConcreteCategory.comp_apply, (hkx t)]
        refine UnderlyingSpace.ext ?_
        change (map (K := ℂ) jG (map (K := ℂ) ι
          (map (K := ℂ) (MMP.ParameterPoint.fibreι (ι ≫ g) (s t)) p))).toHom =
          (map (K := ℂ) (pointFibreFst sY r To t) (map (K := ℂ) i p)).toHom
        rw [toHom_map, toHom_map, toHom_map, toHom_map, toHom_map]
        simp only [Category.assoc]
        exact congrArg (fun φ ↦ toHom p ≫ φ) hi.symm
      have hmult := hmultP (s t) (by
        obtain ⟨w, hw, hwt⟩ := htW P hPs hP
        have : w = (s t).point := by
          rw [(hspt t)]; exact To.ι.isOpenEmbedding.injective hwt
        exact this ▸ hw)
      have key := pushforward_capProductSupportPullback_eq_finsum hB1 g (s t) (u t) (hu t) _ (hzdim P (hgpG P hP)) i
        (k t) (hk t) hki hmult
      have hri : Set.range i.base =
          (pointFibreFst sY r To t).base ⁻¹' (jE.base '' (P.support : Set _)) := by
        ext x
        constructor
        · rintro ⟨w, rfl⟩
          have : (pointFibreFst sY r To t).base (i.base w) =
              (MMP.ParameterPoint.fibreι (ι ≫ g) (s t) ≫ ι ≫ jG).base w := by
            rw [← hi]; rfl
          rw [Set.mem_preimage, this]
          exact h1 ⟨_, rfl⟩
        · intro hx
          have hxr := pointFibreFst_base_mem t x
          obtain ⟨v, hv⟩ := h2 ⟨hx, ⟨(s t).point, (hst t).trans hxr.symm⟩⟩
          have hfv : (ι ≫ g).base v = (s t).point := by
            apply hjBinj
            change ((ι ≫ g) ≫ To.ι ≫ j).base v = _
            rw [Category.assoc, hcomm, ← Category.assoc, Scheme.Hom.comp_base, TopCat.comp_app,
              hv, (hst t)]
            exact hxr
          obtain ⟨w, hw⟩ : v ∈ Set.range (MMP.ParameterPoint.fibreι (ι ≫ g) (s t)).base := by
            rw [MMP.ParameterPoint.range_fibreι]; exact hfv
          refine ⟨w, (pointFibreFst sY r To t).isClosedEmbedding.injective ?_⟩
          change (i ≫ pointFibreFst sY r To t).base w = _
          rw [hi, Scheme.Hom.comp_base, TopCat.comp_app, hw]
          exact hv
      rw [hγP]
      refine Eq.trans ?_ (hΦapp t _).symm
      rw [key, hri]
      haveI : NoetherianSpace (pointFibre sY r To t) := noetherianSpace_of_isComplexScheme
      have hsfin : {C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)} |
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (pointFibreFst sY r To t).base ⁻¹'
            (jE.base '' (P.support : Set _))) (closure {C.1})}.Finite := by
        refine Set.Finite.of_finite_image (f := fun C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)} ↦
            closure ({C.1} : Set (pointFibre sY r To t)))
          ((finite_setOf_maximal ((pointFibreFst sY r To t).base ⁻¹'
            (jE.base '' (P.support : Set _)))).subset ?_) ?_
        · rintro _ ⟨C, hC, rfl⟩; exact hC
        · intro C _ C' _ h
          exact Subtype.ext (inseparable_iff_closure_eq.mpr h).eq
      set φ := (pushforward ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.ofHom ⟨_, (ComplexPoints.homeomorphUnderlyingSpace
            (X := pointFibre sY r To t)).symm.continuous⟩)
          (ComplexPoints.homeomorphUnderlyingSpace (X := pointFibre sY r To t)).symm.isProperMap
          (2 * 1 : ℕ)).hom with hφ
      have h1 : φ (∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (pointFibreFst sY r To t).base ⁻¹'
            (jE.base '' (P.support : Set _))) (closure {C.1})),
          Chow.pointCycleClass ℚ C.1 C.2) =
        ∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (pointFibreFst sY r To t).base ⁻¹'
            (jE.base '' (P.support : Set _))) (closure {C.1})),
          φ (Chow.pointCycleClass ℚ C.1 C.2) :=
        AddMonoidHom.map_finsum_mem _ φ.toAddMonoidHom hsfin
      rw [h1]
      rfl
    · have hBadP : pE.base '' (P.support : Set _) ⊆ Bad := by
        intro x hx
        rw [hBad, Set.mem_iUnion₂]
        exact ⟨P, Finset.mem_filter.2 ⟨hPs, hP⟩, hx⟩
      have hΦ0 : Φ t (γ P) = 0 := by
        by_cases h : P.genericPoint ∈ G
        · have hγP : γ P = Chow.pointCycleClass ℚ (X := G.toScheme) ⟨P.genericPoint, h⟩ (hzdim P h) := by
            simp only [hγ, dif_pos h]
          have hsupp := hVGsupp P h
          obtain ⟨μ, hμ⟩ : ∃ μ, (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι))
              (isProperMap_map (K := ℂ) (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι) (2 * (1 + 1) : ℕ)).hom μ =
              Chow.pointCycleClass ℚ (X := G.toScheme) ⟨P.genericPoint, h⟩ (hzdim P h) := ⟨_, rfl⟩
          haveI hemp : IsEmpty ((TopCat.ofHom (map (K := ℂ) ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g))).hom ⁻¹'
              {(s t).complexPoint}) := by
            refine ⟨fun ⟨v, hv⟩ ↦ ?_⟩
            have hv1 : map (K := ℂ) ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g) v = (s t).complexPoint := hv
            have hv' : ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g).base (v.toHom.base (IsLocalRing.closedPoint ℂ)) =
                (s t).point := by
              have := congrArg (fun q : UnderlyingSpace ℂ To.toScheme ↦
                q.toHom.base (IsLocalRing.closedPoint ℂ)) hv1
              exact this.trans (MMP.ParameterPoint.complexPoint_toHom_closedPoint _)
            have hmem : (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι.base (v.toHom.base (IsLocalRing.closedPoint ℂ)) ∈
                Set.range (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι.base := ⟨_, rfl⟩
            rw [hsupp] at hmem
            apply htBad
            refine hBadP ⟨_, hmem, ?_⟩
            change (G.ι ≫ pE).base _ = _
            rw [← hgU]
            change To.ι.base (((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g).base _) = _
            rw [hv', hspt t]
            rfl
          have hzero := ModuleCat.subsingleton_of_isZero (isZero_borelMooreHomology_of_isEmpty ℚ
            (ModuleCat.of ℚ ℚ) (TopCat.of ((TopCat.ofHom (map (K := ℂ) ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g))).hom ⁻¹'
              {(s t).complexPoint})) (((2 * (1 + 1) : ℕ) : ℤ) - ((2 * 1 : ℕ) : ℤ)))
          rw [hγP, ← hμ]
          refine (hΦapp t _).trans ?_
          rw [← pushforward_preimageRestrictHom_capProductSupportPullback
            (isProperMap_map (K := ℂ) (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι) _ (fibreAmbientPointsHom_aux (integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι g rfl)
            isClosed_singleton _ (hasProperNeighbourhoodDeformations_preimage_singleton
              ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g) _)]
          have h0 : capProductSupportPullback ℚ (TopCat.ofHom (map (K := ℂ) ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g)))
              isClosed_singleton (hasProperNeighbourhoodDeformations_preimage_singleton
                ((integralComponentAt (X := G.toScheme) ⟨P.genericPoint, h⟩).subschemeι ≫ g) _) (2 * 1 : ℕ) (2 * (1 + 1) : ℕ) (u t) μ = 0 :=
            @Subsingleton.elim _ hzero _ _
          rw [h0, map_zero, map_zero, map_zero, map_zero]
        · rw [hγ]
          dsimp only
          rw [dif_neg h]
          exact map_zero _
      rw [hΦ0]
      refine finsum_eq_zero_of_forall_eq_zero fun C ↦ finsum_eq_if.trans (if_neg fun hC ↦ ?_)
      obtain ⟨x, hx⟩ := hC.1.1.nonempty
      obtain ⟨p, hp, hpx⟩ := hC.1.2 hx
      have hxr := pointFibreFst_base_mem t x
      have hpt : pE.base p = t₀ := by
        apply j.isClosedEmbedding.injective
        change (pE ≫ j).base p = _
        rw [hpE, Scheme.Hom.comp_base, TopCat.comp_app, hpx, hyt]
        exact hxr
      have hB := hBadP ⟨p, hp, rfl⟩
      rw [hpt] at hB
      exact htBad hB
  rw [Finsupp.sum, Finset.sum_congr rfl fun P hP ↦ by rw [hXP P hP]]
  change _ = Φ t β
  rw [hβ, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun P _ ↦ (map_smul (Φ t) (LE P) (γ P)).symm

open MMP.UnderlyingSpace MMP.borelMooreHomology in
/-- **The curves cut by a homologically trivial divisor of a dominating component.** For a
component `E` of `F` mapping onto `T` and a `ℚ`-divisor `L` on `E` with `[L] = 0` in
`H_4(E, ℚ)`, at all but finitely many `t ∈ T°(ℂ)` the curves cut by `L` on `F_t` have classes
adding up to `0` in `H_2(F_t, ℚ)`: they add up to the specialization of `[L]` along `E_{T°} → T°`
(`exists_fibreClassFamily`). -/
private theorem eventually_curveClass_eq_zero_of_image_eq'
    (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsLocalSystemOpen sY To) (E : F.support)
    (hE : r.base '' (E.1.support : Set Z) = (T : Set Y))
    (LE : QDivisor E.1.idealSheaf.subscheme) (hLE : Chow.divisorClass E.1.idealSheaf.subscheme LE = 0) :
    ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
      ∀ _ : IsComplexScheme (pointFibre sY r To t),
      (LE.sum fun P c ↦ c •
        ∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
            A ⊆ (pointFibreFst sY r To t).base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
            (closure {C.1})),
          fundamentalClass C.1 C.2) = 0 := by
  letI := curveOver sY To
  haveI := (isSmoothVariety_curveOver hM hdim hTo).1
  haveI := (isSmoothVariety_curveOver hM hdim hTo).2
  have h1 : SmoothOfRelativeDimension 1 (To.toScheme ↘ Spec (.of ℂ)) := dim_curveOver hM hdim hTo
  have hor := isOrientedAtlas_of_isManifold_complex
    (E := EuclideanSpace ℂ (Fin 1))
    (TopCat.of (UnderlyingSpace ℂ To.toScheme))
  choose u hu using fun t : analyticSpace (To.ι ≫ curveι T ≫ sY) ↦
    exists_isLocalOrientationClass (R := ℚ) hor (by norm_num) curveOrientationBasis
      (homeomorphUnderlyingSpace (X := To.toScheme) t)
  obtain ⟨w, hP, hZ, -, -⟩ := exists_fibreClassFamily hM hdim hTo E hE LE
    (fun t ↦ homeomorphUnderlyingSpace (X := To.toScheme) t) (fun _ ↦ rfl) u hu
    (hasProperNeighbourhoodDeformations_curveBaseOpens hM hdim hTo)
  filter_upwards [hP] with t ht inst
  exact (ht inst).trans (hZ hLE t)

/-- The complex points of `Y` lying over a closed subset form a closed subset of `Y(ℂ)`. -/
private theorem isClosed_setOf_closedPoint_mem (sY : Y ⟶ Spec (.of ℂ)) {C : Set Y}
    (hC : IsClosed C) :
    IsClosed {y : analyticSpace sY | y.hom.base (IsLocalRing.closedPoint ℂ) ∈ C} := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  exact (UnderlyingSpace.isClosed_pointsOver (K := ℂ) hC).preimage
    (homeomorphUnderlyingSpace (X := Y)).continuous

/-- Near every point of `T°(ℂ)` there are points avoiding any finite set: `T°(ℂ)` is a Riemann
surface. -/
private theorem exists_and_of_eventually_of_cofinite (hY : MMP.Mori.IsVariety ℂ sY)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsLocalSystemOpen sY To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {p q : analyticSpace (To.ι ≫ curveι T ≫ sY) → Prop} (hp : ∀ᶠ t' in nhds t, p t')
    (hq : ∀ᶠ t' in Filter.cofinite, q t') : ∃ t', p t' ∧ q t' := by
  obtain ⟨-, hsm, -, -⟩ := isLocalSystemOpen_facts hY hdim hTo
  haveI := hsm
  set e := chartAt ℂ t
  have hN : {t' | p t'} ∩ e.source ∈ nhds t :=
    Filter.inter_mem hp (e.open_source.mem_nhds (mem_chart_source ℂ t))
  have himg : e '' ({t' | p t'} ∩ e.source) ∈ nhds (e t) :=
    e.image_mem_nhds (mem_chart_source ℂ t) hN
  have hinf : (e '' ({t' | p t'} ∩ e.source)).Infinite := infinite_of_mem_nhds (e t) himg
  have hinf' : ({t' | p t'} ∩ e.source).Infinite := fun hfin ↦ hinf (hfin.image _)
  obtain ⟨t', ht', hq'⟩ := (hinf'.diff (Filter.eventually_cofinite.1 hq)).nonempty
  exact ⟨t', ht'.1, not_not.1 hq'⟩

/-- A complex point of `Y` whose point lies in `T°` comes from `T°(ℂ)`. -/
private theorem mem_range_curveBaseInclusion (hY : MMP.Mori.IsVariety ℂ sY)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens} (y : analyticSpace sY)
    (hy : y.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range (To.ι ≫ curveι T).base) :
    y ∈ Set.range (curveBaseInclusion sY To) := by
  letI := curveOver sY To
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI : LocallyOfFiniteType (To.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (To.ι ≫ curveι T ≫ sY); infer_instance
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType sY)
  obtain ⟨x, hx⟩ := hy
  have hycl : IsClosed ({y.hom.base (IsLocalRing.closedPoint ℂ)} : Set Y) := by
    have := ((MMP.UnderlyingSpace.equivClosedPoints (K := ℂ) Y)
      (homeomorphUnderlyingSpace (X := Y) y)).2
    rwa [MMP.UnderlyingSpace.equivClosedPoints_apply] at this
  have hxcl : IsClosed ({x} : Set To.toScheme) := by
    have : ({x} : Set To.toScheme) = (To.ι ≫ curveι T).base ⁻¹'
        {y.hom.base (IsLocalRing.closedPoint ℂ)} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl; exact hx
      · intro hz
        exact ((curveι T).isClosedEmbedding.injective.comp To.ι.isOpenEmbedding.injective)
          (hz.trans hx.symm)
    rw [this]
    exact hycl.preimage (To.ι ≫ curveι T).continuous
  obtain ⟨b, hb⟩ := exists_toHom_eq' (X := To.toScheme) hxcl
  refine ⟨b, ?_⟩
  apply (homeomorphUnderlyingSpace (X := Y)).injective
  refine (MMP.UnderlyingSpace.equivClosedPoints (K := ℂ) Y).injective
    (Subtype.ext ?_)
  rw [MMP.UnderlyingSpace.equivClosedPoints_apply,
    MMP.UnderlyingSpace.equivClosedPoints_apply]
  change (To.ι ≫ curveι T).base (b.toHom.base (IsLocalRing.closedPoint ℂ)) =
    y.hom.base (IsLocalRing.closedPoint ℂ)
  exact (congrArg (To.ι ≫ curveι T).base hb).trans hx

open MMP.UnderlyingSpace MMP.borelMooreHomology in
/-- **The total curve class family of a divisor tuple in the algebraic kernel.** For a tuple
`L` of `ℚ`-divisors representing `x ∈ K(r)`, there are classes `w_t ∈ H_2(F_t)` which are, at all
but finitely many `t`, the sums of the curve classes cut by `L`, whose pairings with classes on
`r⁻¹(V)` are locally constant in `t`, and whose pairings vanish on the kernel of `r_t`. -/
private theorem exists_fibreClassTotal (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) {To : (curveScheme T).Opens}
    (hTo : IsAdaptedOpen sY r To) (x : algebraicKernel F)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (hL : ∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x.1 E) :
    ∃ w : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
        MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
          (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ),
      (∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
        ∀ _ : IsComplexScheme (pointFibre sY r To t),
          (∑ E : F.support, (L E).sum fun P c ↦ c •
            ∑ᶠ (C : {x : pointFibre sY r To t //
                relativeDimension (fieldChowSituation ℂ).dimensionFunction
                  (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
                A ⊆ (pointFibreFst sY r To t).base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                (closure {C.1})),
              fundamentalClass C.1 C.2) = w t) ∧
      (∀ (V : Opens (analyticSpace sY))
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
        (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
        ∀ᶠ t' in nhds t, ∀ hV' : curveOpenInclusion sY To t' ∈ V,
          fibrePairing hM t' hV' α (w t') = fibrePairing hM t hV α (w t)) ∧
      (∀ t e, (localSystemRestrictionFibre sY hM.isBiregular To t).hom e = 0 →
        stalkPairing hM t (w t) e = 0) := by
  classical
  letI := curveOver sY To
  haveI := (isSmoothVariety_curveOver hM hdim hTo.toIsLocalSystemOpen).1
  haveI := (isSmoothVariety_curveOver hM hdim hTo.toIsLocalSystemOpen).2
  have h1 : SmoothOfRelativeDimension 1 (To.toScheme ↘ Spec (.of ℂ)) :=
    dim_curveOver hM hdim hTo.toIsLocalSystemOpen
  have hor := isOrientedAtlas_of_isManifold_complex
    (E := EuclideanSpace ℂ (Fin 1))
    (TopCat.of (UnderlyingSpace ℂ To.toScheme))
  choose u hu using fun t : analyticSpace (To.ι ≫ curveι T ≫ sY) ↦
    exists_isLocalOrientationClass (R := ℚ) hor (by norm_num) curveOrientationBasis
      (homeomorphUnderlyingSpace (X := To.toScheme) t)
  have hdQ := hasProperNeighbourhoodDeformations_curveBaseOpens hM hdim hTo.toIsLocalSystemOpen
  -- the classes of the components
  have hfam : ∀ E : F.support, ∃ wE : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ),
      (∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
        ∀ _ : IsComplexScheme (pointFibre sY r To t),
          ((L E).sum fun P c ↦ c •
            ∑ᶠ (C : {x : pointFibre sY r To t //
                relativeDimension (fieldChowSituation ℂ).dimensionFunction
                  (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
              (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
                A ⊆ (pointFibreFst sY r To t).base ⁻¹'
                  (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                (closure {C.1})),
              fundamentalClass C.1 C.2) = wE t) ∧
      (∀ (V : Opens (analyticSpace sY))
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
        (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
        ∀ᶠ t' in nhds t, ∀ hV' : curveOpenInclusion sY To t' ∈ V,
          fibrePairing hM t' hV' α (wE t') = fibrePairing hM t hV α (wE t)) ∧
      (∃ ν : ∀ V : Opens (analyticSpace sY),
          rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2 →
            MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
              (TopCat.of (curveBaseOpens sY To V)) (4 - 2),
        (∀ (V : Opens (analyticSpace sY))
          (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
          (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
          fibrePairing hM t hV α (wE t) =
            @compactDegree (TopCat.of ((borelMooreHomology.inclHom
                (curveBaseOpens sY To V)).hom ⁻¹' {homeomorphUnderlyingSpace (X := To.toScheme) t}))
              (compactSpace_preimage_singleton_inclHom _ _)
              (BorelMooreCross.congrDegree ℚ _ (by norm_num)
                (borelMooreHomology.capProductSupportPullback ℚ
                  (borelMooreHomology.inclHom (curveBaseOpens sY To V)) isClosed_singleton
                  (hdQ V (homeomorphUnderlyingSpace (X := To.toScheme) t)) 2 (4 - 2) (u t)
                  (ν V α)))) ∧
        (∀ (V : Opens (analyticSpace sY))
          (hVT : ∀ z ∈ V, z ∈ curvePoints sY T → z ∈ Set.range (curveBaseInclusion sY To))
          (_ : r.base '' (E.1.support : Set Z) ≠ (T : Set Y) →
            ∀ z : analyticSpace (r ≫ sY), z.hom.base (IsLocalRing.closedPoint ℂ) ∈ E.1.support →
              resolutionAnalyticMap sY r z ∉ V)
          (α' : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
            (preimageSpace (resolutionAnalyticMap sY r) V) (resolutionCurveSet sY r T V) 2),
          (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) (curveBaseToPoints sY To V)
              (isClosedEmbedding_curveBaseToPoints sY To V hVT).1.isProperMap (4 - 2)).hom
            (ν V ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α')) =
          kernelSpecialization hM T V α' (componentHomologyMap E.1 4 (x.1 E)))) := by
    intro E
    by_cases hE : r.base '' (E.1.support : Set Z) = (T : Set Y)
    · obtain ⟨w, hP, -, hLC, ν, hCMP, hKV⟩ := exists_fibreClassFamily hM hdim
        hTo.toIsLocalSystemOpen E hE (L E) (fun t ↦ homeomorphUnderlyingSpace (X := To.toScheme) t)
        (fun _ ↦ rfl) u hu hdQ
      refine ⟨w, hP, hLC, ν, hCMP, fun V hVT _ α' ↦ ?_⟩
      rw [hKV V hVT α', hL E]
    · refine ⟨fun _ ↦ 0, ?_, ?_, fun _ _ ↦ 0, ?_, ?_⟩
      · filter_upwards [eventually_curveClass_eq_zero_of_image_ne hM hdim To E hE (L E)] with t ht
          inst
        exact ht inst
      · intro V α t hV
        filter_upwards with t' hV'
        rw [fibrePairing_zero, fibrePairing_zero]
      · intro V α t hV
        rw [fibrePairing_zero]
        simp only [map_zero]
      · intro V hVT hVE α'
        rw [kernelSpecialization_componentHomologyMap_eq_zero hM T V α' E.1 (hVE hE)]
        exact map_zero _
  choose wE hwP hwLC hν using hfam
  choose νE hνCMP hνKV using hν
  have hLCt : ∀ (V : Opens (analyticSpace sY))
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
      (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
      ∀ᶠ t' in nhds t, ∀ hV' : curveOpenInclusion sY To t' ∈ V,
        fibrePairing hM t' hV' α (∑ E, wE E t') = fibrePairing hM t hV α (∑ E, wE E t) := by
    intro V α t hV
    filter_upwards [Filter.eventually_all.2 fun E ↦ hwLC E V α t hV] with t' ht' hV'
    rw [fibrePairing_sum, fibrePairing_sum]
    exact Finset.sum_congr rfl fun E _ ↦ ht' E hV'
  have hY : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  -- the kernel vanishing on an open where the class dies on the regular part
  have hcore : ∀ (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (W : Opens (analyticSpace sY))
      (hW : curveOpenInclusion sY To t ∈ W)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) W) 2)
      (_ : ((directImageRestriction (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) 2).app (op W)).hom α = 0),
      fibrePairing hM t hW α (∑ E, wE E t) = 0 := by
    intro t W hW α hψ
    haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
    obtain ⟨U₀, hU₀ne, hU₀⟩ : ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
        (U : Set Y) ∩ (singularLocus sY : Set Y) = (U : Set Y) ∩ T := by
      letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
      haveI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
      haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
      exact MMP.Fourfold.exists_open_singularLocus_inter_eq hM T hT hdim
    -- the bad closed set
    set C : Set Y := ((U₀ : Set Y)ᶜ ∪ (curveι T).base '' (To : Set (curveScheme T))ᶜ) ∪
      ⋃ (E : F.support) (_ : r.base '' (E.1.support : Set Z) ≠ (T : Set Y)),
        r.base '' (E.1.support : Set Z) with hC
    have hCcl : IsClosed C := by
      refine (U₀.isOpen.isClosed_compl.union ((curveι T).isClosedEmbedding.isClosedMap _
        To.isOpen.isClosed_compl)).union
        (isClosed_iUnion_of_finite fun E ↦ isClosed_iUnion_of_finite fun _ ↦ ?_)
      exact r.isClosedMap _ (by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
    let V' : Opens (analyticSpace sY) := W ⊓
      ⟨{y | y.hom.base (IsLocalRing.closedPoint ℂ) ∉ C},
        (isClosed_setOf_closedPoint_mem sY hCcl).isOpen_compl⟩
    have hV'W : V' ≤ W := inf_le_left
    -- a good point near `t`
    have hp : ∀ᶠ t' in nhds t, curveOpenInclusion sY To t' ∈ W ∧
        ∀ hV' : curveOpenInclusion sY To t' ∈ W,
          fibrePairing hM t' hV' α (∑ E, wE E t') = fibrePairing hM t hW α (∑ E, wE E t) :=
      (show ∀ᶠ t' in nhds t, curveOpenInclusion sY To t' ∈ W from
        (curveOpenInclusion sY To).hom.continuous.continuousAt.preimage_mem_nhds
          (W.isOpen.mem_nhds hW)).and (hLCt W α t hW)
    have hU₀' : IsOpen ((curveι T).base ⁻¹' (U₀ : Set Y)) := U₀.isOpen.preimage (curveι T).continuous
    have hU₀ne' : ((curveι T).base ⁻¹' (U₀ : Set Y)).Nonempty := by
      obtain ⟨y, hyU, hyT⟩ := hU₀ne
      rw [← range_curveι] at hyT
      obtain ⟨c, rfl⟩ := hyT
      exact ⟨c, hyU⟩
    have hq : ∀ᶠ t' : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
        (t'.hom ≫ To.ι).base (IsLocalRing.closedPoint ℂ) ∈ (curveι T).base ⁻¹' (U₀ : Set Y) ∧
        ∀ E : F.support, r.base '' (E.1.support : Set Z) ≠ (T : Set Y) →
          (t'.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∉
            r.base '' (E.1.support : Set Z) := by
      refine (eventually_mem_of_isOpen hY hdim hU₀' hU₀ne').and
        (Filter.eventually_all.2 fun E ↦ ?_)
      by_cases hE : r.base '' (E.1.support : Set Z) = (T : Set Y)
      · exact Filter.Eventually.of_forall fun _ h ↦ (h hE).elim
      · exact (eventually_notMem_image_of_ne hM hdim To E hE).mono fun _ h _ ↦ h
    obtain ⟨t', ⟨htW, hLC'⟩, hU', hE'⟩ :=
      exists_and_of_eventually_of_cofinite hY hdim hTo.toIsLocalSystemOpen t hp hq
    have ht'V' : curveOpenInclusion sY To t' ∈ V' := by
      refine Opens.mem_inf.2 ⟨htW, fun hCt ↦ ?_⟩
      rcases hCt with (hU | ⟨c, hc, hceq⟩) | hR
      · exact hU hU'
      · have hmem : To.ι.base (t'.hom.base (IsLocalRing.closedPoint ℂ)) ∈ (To : Set _) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
        have hc' : c = To.ι.base (t'.hom.base (IsLocalRing.closedPoint ℂ)) :=
          (curveι T).isClosedEmbedding.injective hceq
        exact hc (hc' ▸ hmem)
      · obtain ⟨E, hE, hmem⟩ := Set.mem_iUnion₂.1 hR
        exact hE' E hE hmem
    -- the open `V'` meets the singular locus only along `T`, and misses the other components
    have hVT : ∀ z ∈ V', z ∈ curvePoints sY T → z ∈ Set.range (curveBaseInclusion sY To) := by
      intro z hz hzT
      apply mem_range_curveBaseInclusion hY z
      have hzT' : z.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range (curveι T).base := by
        rw [range_curveι]; exact hzT
      obtain ⟨c, hc⟩ := hzT'
      by_cases hcT : c ∈ (To : Set (curveScheme T))
      · obtain ⟨c', rfl⟩ : c ∈ Set.range To.ι.base := by rw [Scheme.Opens.range_ι]; exact hcT
        exact ⟨c', hc⟩
      · exact ((Opens.mem_inf.1 hz).2 (Or.inl (Or.inr ⟨c, hcT, hc⟩))).elim
    have hsing : ∀ y ∈ V', y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (singularLocus sY : Set Y) →
        y ∈ curvePoints sY T := by
      intro y hy hs
      have hU : y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (U₀ : Set Y) := by
        by_contra h
        exact (Opens.mem_inf.1 hy).2 (Or.inl (Or.inl h))
      have h' : y.hom.base (IsLocalRing.closedPoint ℂ) ∈
          (U₀ : Set Y) ∩ (singularLocus sY : Set Y) := ⟨hU, hs⟩
      rw [hU₀] at h'
      exact h'.2
    have hVE : ∀ E : F.support, r.base '' (E.1.support : Set Z) ≠ (T : Set Y) →
        ∀ z : analyticSpace (r ≫ sY), z.hom.base (IsLocalRing.closedPoint ℂ) ∈ E.1.support →
          resolutionAnalyticMap sY r z ∉ V' := by
      intro E hE z hz hzV
      exact (Opens.mem_inf.1 hzV).2 (Or.inr (Set.mem_iUnion₂.2 ⟨E, hE, ⟨_, hz, rfl⟩⟩))
    -- the restricted class comes from a class supported on `r⁻¹(T)`
    have hψV : ((directImageRestriction (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) 2).app (op V')).hom
        ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hV'W) 2).hom α) =
        0 := by
      have hnat := congrArg (fun φ ↦ φ.hom α) ((directImageRestriction (resolutionAnalyticMap sY r)
        (analyticMap (regularSection sY hM.isBiregular)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hM.isBiregular) 2).naturality (homOfLE hV'W).op)
      refine hnat.trans ?_
      exact (congrArg (ModuleCat.Hom.hom
        ((directImagePresheaf (regularInclusion sY) 2).map (homOfLE hV'W).op)) hψ).trans
          (map_zero _)
    have hcompl := restrictCompl_eq_zero_of_directImageRestriction hM T V' hsing _ hψV
    obtain ⟨α', hα'⟩ := (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ
      (preimageSpace (resolutionAnalyticMap sY r) V') (resolutionCurveSet sY r T V') 2 _).1 hcompl
    have hα'' : (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α' =
        (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hV'W) 2).hom α :=
      hα'
    -- the classes `ν` sum to zero
    have hsum : ∑ E, νE E V' ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom
        α') = 0 := by
      apply injective_pushforward_curveBaseToPoints sY To V' hVT (4 - 2)
      rw [map_sum, map_zero, Finset.sum_congr rfl fun E _ ↦ hνKV E V' hVT (hVE E) α', ← map_sum,
        ((mem_exceptionalKernel F).1 x.2).2, map_zero]
    rw [← hLC' htW, ← fibrePairing_restrict hM t' hV'W ht'V' α, ← hα'', fibrePairing_sum,
      Finset.sum_congr rfl fun E _ ↦ hνCMP E V'
        ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom α') t' ht'V', ← map_sum, ← map_sum, ← map_sum, hsum]
    simp only [map_zero]
  refine ⟨fun t ↦ ∑ E, wE E t, ?_, hLCt, ?_⟩
  · filter_upwards [Filter.eventually_all.2 hwP] with t ht inst
    exact Finset.sum_congr rfl fun E _ ↦ ht E inst
  · intro t e he
    obtain ⟨e₀, rfl⟩ := (bijective_stalkToPullbackStalk (curveOpenInclusion sY To)
      (resolutionHigherDirectImage sY r 2) t).2 e
    obtain ⟨V, hV, α, rfl⟩ := exists_higherDirectImageGerm_eq (resolutionAnalyticMap sY r) 2 _ e₀
    rw [stalkPairing_apply]
    obtain ⟨W, hWV, hW, hψ⟩ := exists_le_directImageRestriction_eq_zero hM t hV α he
    rw [← fibrePairing_restrict hM t hWV hW]
    exact hcore t W hW _ hψ

/-- **The pinned flat family attached to a family of curve classes.** Let `w_t ∈ H_2(F_t)` be
classes which are, at all but finitely many `t`, the sums of the curve classes cut by `L`, whose
pairings with classes on `r⁻¹(V)` are locally constant in `t`, and whose pairings vanish on the
kernel of `r_t : 𝒲_t → 𝒱_{T,t}`. Then the pairings descend to a flat pinned family on `𝒱_T`. -/
private theorem exists_mem_flatForms_isPinned_of_fibreClass
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    {To : (curveScheme T).Opens}
    (hsurj : ∀ t, Function.Surjective (localSystemRestrictionFibre sY hM.isBiregular To t).hom)
    (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (w : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      MMP.borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) ((2 * 1 : ℕ) : ℤ))
    (hpin : ∀ᶠ t : analyticSpace (To.ι ≫ curveι T ≫ sY) in Filter.cofinite,
      ∀ _ : IsComplexScheme (pointFibre sY r To t),
        (∑ E : F.support, (L E).sum fun P c ↦ c •
          ∑ᶠ (C : {x : pointFibre sY r To t //
              relativeDimension (fieldChowSituation ℂ).dimensionFunction
                (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
            (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
              A ⊆ (pointFibreFst sY r To t).base ⁻¹'
                (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
              (closure {C.1})),
            fundamentalClass C.1 C.2) = w t)
    (hLC : ∀ (V : Opens (analyticSpace sY))
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
      (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To t ∈ V),
      ∀ᶠ t' in nhds t, ∀ hV' : curveOpenInclusion sY To t' ∈ V,
        fibrePairing hM t' hV' α (w t') = fibrePairing hM t hV α (w t))
    (hKV : ∀ t e, (localSystemRestrictionFibre sY hM.isBiregular To t).hom e = 0 →
      stalkPairing hM t (w t) e = 0) :
    ∃ ψ ∈ flatForms (curveLocalSystem sY To), IsPinned hM To L ψ := by
  obtain ⟨ψ, hψ, hψρ⟩ := exists_mem_flatForms_comp_eq (localSystemRestriction sY hM.isBiregular To)
    (fun t ↦ hsurj t) (fun t ↦ stalkPairing hM t (w t)) (fun t e he ↦ hKV t e he) (by
      intro U s x₀ hx₀
      obtain ⟨W, ρW, N, hx₀N, hNU, hNW, hgerm⟩ :=
        exists_local_germ (𝓛 := resolutionHigherDirectImage sY r 2) (curveOpenInclusion sY To) s
          x₀ hx₀
      obtain ⟨V, hV, α, hα⟩ := exists_higherDirectImageGerm_eq (resolutionAnalyticMap sY r) 2
        (curveOpenInclusion sY To x₀)
        (((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY r 2)).germ W _ (hNW hx₀N) ρW)
      -- the section of `R²r_*ℚ` given by `α`
      set σ := ((toSheafify (Opens.grothendieckTopology (analyticSpace sY))
        (directImagePresheaf (resolutionAnalyticMap sY r) 2)).app (op V)).hom α with hσ
      have hσgerm : ∀ y (hy : y ∈ V),
          ((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY r 2)).germ V y hy σ =
            (higherDirectImageGerm (resolutionAnalyticMap sY r) 2 y hy).hom α := fun y hy ↦
        (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
          (toSheafify (Opens.grothendieckTopology (analyticSpace sY))
            (directImagePresheaf (resolutionAnalyticMap sY r) 2)) α).symm
      obtain ⟨W', hW', iW, iV, hres⟩ :=
        ((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY r 2)).germ_eq
          (curveOpenInclusion sY To x₀) (hNW hx₀N) hV ρW σ (by rw [hσgerm, hα])
      have hgy : ∀ y (hy : y ∈ W'),
          ((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY r 2)).germ W y (iW.le hy) ρW =
            (higherDirectImageGerm (resolutionAnalyticMap sY r) 2 y (iV.le hy)).hom α := by
        intro y hy
        refine (TopCat.Presheaf.germ_res_apply _ iW y hy ρW).symm.trans ?_
        rw [hres]
        exact (TopCat.Presheaf.germ_res_apply _ iV y hy σ).trans (hσgerm y _)
      have hpair : ∀ x (hx : x ∈ N) (hxW : curveOpenInclusion sY To x ∈ W'),
          stalkPairing hM x (w x) (((TopCat.Sheaf.forget _ _).obj
            (resolutionLocalSystem sY r To)).germ U x (hNU hx) s) =
            fibrePairing hM x (iV.le hxW) α (w x) := by
        intro x hx hxW
        refine (congrArg (stalkPairing hM x (w x)) (hgerm x hx)).trans ?_
        rw [hgy _ hxW]
        exact stalkPairing_apply hM x (w x) (iV.le hxW) α
      have hN' : ∀ᶠ x in nhds x₀, x ∈ N ∧ curveOpenInclusion sY To x ∈ W' :=
        (show ∀ᶠ x in nhds x₀, x ∈ N from N.isOpen.mem_nhds hx₀N).and
          (show ∀ᶠ x in nhds x₀, curveOpenInclusion sY To x ∈ W' from
            (W'.isOpen.preimage (curveOpenInclusion sY To).hom.continuous).mem_nhds hW')
      filter_upwards [hN', hLC V α x₀ hV] with x hx hxLC hxU
      rw [hpair x hx.1 hx.2, hpair x₀ hx₀N hW']
      exact hxLC _)
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [hpin] with t ht
  haveI := isComplexScheme_pointFibre hM t
  refine ⟨‹_›, fun V hV α p hp ↦ ?_⟩
  rw [show ψ t ((localSystemRestrictionFibre sY hM.isBiregular To t).hom
      ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2) t).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α))) =
      stalkPairing hM t (w t) ((stalkToPullbackStalk (curveOpenInclusion sY To)
        (resolutionHigherDirectImage sY r 2) t).hom
        ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α)) from hψρ t _,
    stalkPairing_apply]
  refine (congrArg (borelMooreHomology.capProduct ℚ
    (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) Set.univ 2 2
    ((rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α)) (ht ‹_›)).trans ?_
  haveI := compactSpace_pointFibre hM t
  haveI := pathConnectedSpace_pointFibre hM t
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsProper (pointFibre sY r To t ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd r (t.hom ≫ To.ι ≫ curveι T)))
  exact eq_compactDegree_smul_fundamentalClass p hp (BorelMooreCross.congrDegree ℚ _ (by norm_num)
    (borelMooreHomology.capProduct ℚ (analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)))
      Set.univ 2 2 ((rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α) (w t)))

/-- **Homologically trivial divisors pin the zero family.** A tuple `L` of `ℚ`-divisors on the
components `Fᵢ` with `[Lᵢ] = 0` in `H_4(Fᵢ, ℚ)` cuts on all but finitely many fibres `F_t`
curves whose classes add up to zero in `H_2(F_t, ℚ)`. -/
private theorem isPinned_zero {T : IrreducibleCloseds Y}
    (hdim : topologicalKrullDim (T : Set Y) = 1) {To : (curveScheme T).Opens}
    (hTo : IsAdaptedOpen sY r To) (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme)
    (hL : ∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = 0) : IsPinned hM To L 0 := by
  classical
  have hall := Filter.eventually_all.2 fun E : F.support ↦
    if hE : r.base '' (E.1.support : Set Z) = (T : Set Y) then
      eventually_curveClass_eq_zero_of_image_eq' hM hdim hTo.toIsLocalSystemOpen E hE (L E) (hL E)
    else eventually_curveClass_eq_zero_of_image_ne hM hdim To E hE (L E)
  filter_upwards [hall] with t ht
  haveI := isComplexScheme_pointFibre hM t
  refine ⟨inferInstance, fun V hV α p hp ↦ ?_⟩
  calc _ = borelMooreHomology.capProduct ℚ _ Set.univ 2 2
        ((rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α) 0 :=
        congrArg _ (Finset.sum_eq_zero fun E _ ↦ ht E inferInstance)
    _ = _ := by simp <;> rfl

/-- **The curve classes give flat pinned families.** For every `x ∈ K(r)` there is a flat family
of forms on `𝒱_T` pinned by every divisor representative of `x`. -/
private theorem exists_mem_flatForms_forall_isPinned {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y)) (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To)
    (hsurj : ∀ t, Function.Surjective (localSystemRestrictionFibre sY hM.isBiregular To t).hom)
    (x : algebraicKernel F) :
    ∃ ψ ∈ flatForms (curveLocalSystem sY To),
      ∀ L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme,
        (∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x.1 E) → IsPinned hM To L ψ := by
  -- a divisor representative of `x`
  have hx := ((mem_exceptionalKernel F).1 x.2).1
  choose L₀ hL₀ using fun E ↦ (hx E : x.1 E ∈ LinearMap.range _)
  obtain ⟨w, hpin, hLC, hKV⟩ := exists_fibreClassTotal hM hT hdim hTo x L₀ hL₀
  obtain ⟨ψ, hψ, hψpin⟩ := exists_mem_flatForms_isPinned_of_fibreClass hM hsurj L₀ w hpin hLC hKV
  refine ⟨ψ, hψ, fun L hL ↦ ?_⟩
  have := isPinned_add hM hψpin (isPinned_zero hM hdim hTo (L - L₀) fun E ↦ by
    rw [Pi.sub_apply, map_sub, hL, hL₀, sub_self])
  rwa [add_sub_cancel, add_zero] at this

/-- The complex points of an adapted open of a curve form an infinite set: they form a
Riemann surface. -/
private theorem infinite_analyticSpace (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To) :
    Infinite (analyticSpace (To.ι ≫ curveι T ≫ sY)) := by
  obtain ⟨-, hsm, hconn, -⟩ := isLocalSystemOpen_facts hM.isResolution.1 hdim
    hTo.toIsLocalSystemOpen
  haveI := hsm
  obtain ⟨x⟩ := hconn.toNonempty
  let e := chartAt ℂ x
  have htgt : e.target.Infinite := by
    intro hfin
    have hz : e x ∈ e.target := e.map_source (mem_chart_source ℂ x)
    have : IsOpen ({e x} : Set ℂ) := by
      have h1 : e.target \ (e.target \ {e x}) = {e x} := by
        ext w
        simp only [Set.mem_diff, Set.mem_singleton_iff, not_and, not_not]
        constructor
        · rintro ⟨h, h'⟩; exact h' h
        · rintro rfl; exact ⟨hz, fun _ ↦ rfl⟩
      rw [← h1]
      exact e.open_target.sdiff (hfin.subset Set.diff_subset).isClosed
    exact not_isOpen_singleton (e x) this
  have himg : (e.symm '' e.target).Infinite := htgt.image (by simpa using e.symm.injOn)
  exact Set.infinite_univ_iff.1 (himg.mono (Set.subset_univ _))

/-- A flat family of forms vanishing at one point vanishes. -/
private theorem eq_zero_of_mem_flatForms (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To)
    {w : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      Module.Dual ℚ (curveLocalSystemFibre sY To t)}
    (hw : w ∈ flatForms (curveLocalSystem sY To)) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (ht : w t = 0) : w = 0 := by
  obtain ⟨-, -, hconn, hlpc⟩ := isLocalSystemOpen_facts hM.isResolution.1 hdim
    hTo.toIsLocalSystemOpen
  haveI := hlpc
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 hconn
  exact eq_zero_of_mem_flatForms_of_isLocalSystem hTo.isLocalSystem hw t ht

/-- The point classes of a complex scheme fibre are nonzero. -/
private theorem exists_fundamentalClass_ne_zero (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) [IsComplexScheme (pointFibre sY r To t)] :
    ∃ (p : pointFibre sY r To t) (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction
        (pointFibre sY r To t ↘ Spec (.of ℂ)) p = (0 : ℕ)), fundamentalClass p hp ≠ 0 := by
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hM.isResolution.2.2.2.2
  have hsurj : Function.Surjective r.base := by
    have h := r.denseRange.closure_range
    rw [r.isClosedMap.isClosed_range.closure_eq] at h
    exact Set.range_eq_univ.1 h
  haveI : IsProper (pointFibre sY r To t ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsProper (Limits.pullback.snd r (t.hom ≫ To.ι ≫ curveι T)))
  -- the fibre is nonempty
  obtain ⟨z, hz⟩ := hsurj ((t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ))
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := r)
    (g := t.hom ≫ To.ι ≫ curveι T) z (IsLocalRing.closedPoint ℂ) hz
  haveI : CompactSpace (pointFibre sY r To t) :=
    QuasiCompact.compactSpace_of_compactSpace (pointFibre sY r To t ↘ Spec (.of ℂ))
  haveI := compactSpace_pointFibre hM t
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := pointFibre sY r To t) isClosed_univ
    ⟨w, Set.mem_univ _⟩
  exact ⟨x, relativeDimension_eq_zero_of_isClosed hx, fundamentalClass_point_ne_zero (X := pointFibre sY r To t) x _⟩

/-- Every element of `𝒱_{T,t}` is the restriction of the germ of a class on some `r⁻¹(V)`,
when `r_t` is onto. -/
private theorem exists_eq_localSystemRestrictionFibre {T : IrreducibleCloseds Y}
    {To : (curveScheme T).Opens} (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hsurj : Function.Surjective (localSystemRestrictionFibre sY hM.isBiregular To t).hom)
    (v : curveLocalSystemFibre sY To t) :
    ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
      (localSystemRestrictionFibre sY hM.isBiregular To t).hom
          ((stalkToPullbackStalk (curveOpenInclusion sY To)
            (resolutionHigherDirectImage sY r 2) t).hom
            ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α)) = v := by
  obtain ⟨w, rfl⟩ := hsurj v
  obtain ⟨w', rfl⟩ := (bijective_stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY r 2) t).2 w
  obtain ⟨V, hV, α, rfl⟩ := exists_higherDirectImageGerm_eq (resolutionAnalyticMap sY r) 2 _ w'
  exact ⟨V, hV, α, rfl⟩

/-- **Uniqueness of pinned flat families.** -/
private theorem eq_of_isPinned {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y)) (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To)
    (hsurj : ∀ t, Function.Surjective (localSystemRestrictionFibre sY hM.isBiregular To t).hom)
    {L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme}
    {ψ ψ' : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
      Module.Dual ℚ (curveLocalSystemFibre sY To t)}
    (hψ : ψ ∈ flatForms (curveLocalSystem sY To)) (hψ' : ψ' ∈ flatForms (curveLocalSystem sY To))
    (h : IsPinned hM To L ψ) (h' : IsPinned hM To L ψ') : ψ = ψ' := by
  haveI := infinite_analyticSpace hM hdim hTo
  obtain ⟨t, ⟨_, ht⟩, ⟨_, ht'⟩⟩ := (h.and h').exists
  obtain ⟨p, hp0, hp⟩ := exists_fundamentalClass_ne_zero hM t
  have hpt : ψ t = ψ' t := by
    ext v
    obtain ⟨V, hV, α, rfl⟩ := exists_eq_localSystemRestrictionFibre hM t (hsurj t) v
    have := (ht V hV α p hp0).symm.trans (ht' V hV α p hp0)
    exact smul_left_injective ℚ hp this
  have := eq_zero_of_mem_flatForms hM hdim hTo (sub_mem hψ hψ') t (by rw [Pi.sub_apply, hpt,
    sub_self])
  exact sub_eq_zero.1 this

open MMP.Fourfold.Conductor.ProofLemContractedEdgeInjectivity in
/-- **Oriented double-surface systems cut zero curve classes.** The curves cut by `Zᵢ(a)` and
`Zⱼ(a)` on a fibre along a double surface `S ⊆ Fᵢ ∩ Fⱼ` are the same, with opposite
coefficients. -/
private theorem sum_surfaceCoefficientDivisor_eq_zero (hM : IsCurvePointExceptionalModel sY r F D) {a : DoubleSurface F → ℚ}
    (ha : a ∈ orientedSurfaceCoefficients F) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    [IsComplexScheme (pointFibre sY r To t)] :
    (∑ E : F.support, (surfaceCoefficientDivisor a E.1).sum fun P c ↦ c •
        ∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
          (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
            A ⊆ (pointFibreFst sY r To t).base ⁻¹'
              (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
            (closure {C.1})),
          fundamentalClass C.1 C.2) = 0 := by
  classical
  have := noetherianSpace_of_isComplexScheme (X := Z)
  haveI : IsProper (r ≫ sY) := by
    haveI := (IsProjectiveMorphism.isProjective hM.isProjectiveVariety.isProjective).isProper
    haveI := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
    infer_instance
  haveI : Finite (DoubleSurface F) := DoubleSurface.finite
  letI := Fintype.ofFinite (DoubleSurface F)
  -- the curve class cut on `F_t` by a closed set `S ⊆ Z`
  set X : Set Z → _ := fun S ↦ ∑ᶠ (C : {x : pointFibre sY r To t //
            relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r To t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
    (_ : Maximal (fun A : Set (pointFibre sY r To t) ↦ IsIrreducible A ∧
      A ⊆ (pointFibreFst sY r To t).base ⁻¹' S) (closure {C.1})),
    fundamentalClass C.1 C.2 with hX
  have h1 : ∀ E : F.support, ((surfaceCoefficientDivisor a E.1).sum fun P c ↦
      c • X (E.1.idealSheaf.subschemeι.base '' (P.support : Set _))) =
      ∑ σ : {σ : DoubleSurface F // σ.fst = E.1}, a σ.1 • X σ.1.carrier := by
    intro E
    rw [sum_surfaceCoefficientDivisor hM.isSNC a E.1
      (fun P c ↦ c • X (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
      fun P ↦ zero_smul _ _]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [image_support_rhoOf]
  change ∑ E : F.support, ((surfaceCoefficientDivisor a E.1).sum fun P c ↦
      c • X (E.1.idealSheaf.subschemeι.base '' (P.support : Set _))) = 0
  simp_rw [h1]
  have h2 : ∑ E : F.support, ∑ σ : {σ : DoubleSurface F // σ.fst = E.1}, a σ.1 • X σ.1.carrier =
      ∑ σ : DoubleSurface F, a σ • X σ.carrier := by
    rw [← Fintype.sum_fiberwise (fun σ : DoubleSurface F ↦ (⟨σ.fst, σ.fst_mem⟩ : F.support))]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun σ ↦ by rw [Subtype.ext_iff])
      _ _ fun _ ↦ rfl
  rw [h2]
  have h3 : ∑ σ : DoubleSurface F, a σ • X σ.carrier =
      -∑ σ : DoubleSurface F, a σ • X σ.carrier := by
    let e : DoubleSurface F ≃ DoubleSurface F :=
      Function.Involutive.toPerm _ DoubleSurface.swap_swap
    refine (Equiv.sum_comp e _).symm.trans ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    change a σ.swap • X σ.swap.carrier = _
    rw [(mem_orientedSurfaceCoefficients F).1 ha σ, DoubleSurface.swap_carrier, neg_smul]
  have h4 : (2 : ℚ) • ∑ σ : DoubleSurface F, a σ • X σ.carrier = 0 := by
    rw [two_smul]
    nth_rw 2 [h3]
    exact add_neg_cancel _
  rcases smul_eq_zero.1 h4 with h | h
  · norm_num at h
  · exact h

/-- The curves `T ⊆ Sing Y` are finitely many: each is the image of a component of `F`. -/
private theorem finite_curves (hM : IsCurvePointExceptionalModel sY r F D) :
    Finite {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1} := by
  classical
  haveI : IsProper r := (IsProjectiveMorphism.isProjective hM.isResolution.2.2.2.1).isProper
  haveI : IsDominant r := MMP.Mori.IsBirationalMorphism.isDominant hM.isResolution.2.2.2.2
  have hsurj : Function.Surjective r.base := by
    have h := r.denseRange.closure_range
    rw [r.isClosedMap.isClosed_range.closure_eq] at h
    exact Set.range_eq_univ.1 h
  let K : Mori.PrimeDivisor Z → Set Y := fun E ↦ r.base '' (E.support : Set Z)
  have hKcl : ∀ E : Mori.PrimeDivisor Z, IsClosed (K E) := fun E ↦ r.isClosedMap _ (by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
  have hKirr : ∀ E : Mori.PrimeDivisor Z, IsIrreducible (K E) := fun E ↦ by
    refine IsIrreducible.image ?_ _ r.continuous.continuousOn
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure
  -- every singular curve is the image of a component of `F`
  have hmem : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1}, ∃ E ∈ F.support, K E = T.1 := by
    intro T
    have hsub : (T.1 : Set Y) ⊆ ⋃₀ ((F.support.image K : Finset (Set Y)) : Set (Set Y)) := by
      intro y hy
      obtain ⟨z, rfl⟩ := hsurj y
      have hz : z ∈ (F.supp : Set Z) := by
        rw [hM.supp_eq_preimage_singularLocus]; exact T.2.1 hy
      rw [DivisorWithCoeffs.coe_supp] at hz
      obtain ⟨E, hE, hzE⟩ := Set.mem_iUnion₂.1 hz
      exact Set.mem_sUnion.2 ⟨K E, Finset.mem_coe.2 (Finset.mem_image_of_mem K hE), z, hzE, rfl⟩
    obtain ⟨S, hS, hTS⟩ := (isIrreducible_iff_sUnion_isClosed.1 T.1.isIrreducible)
      (F.support.image K) (fun S hS ↦ by
        obtain ⟨E, -, rfl⟩ := Finset.mem_image.1 hS
        exact hKcl E) hsub
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 hS
    refine ⟨E, hE, ?_⟩
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne (hKirr E) T.1.isClosed
      hTS (Ne.symm hne) (ne_top_of_le_ne_top (by decide) (hM.topologicalKrullDim_image_le E hE))
    rw [T.2.2] at hlt
    exact absurd (hlt.trans_le (hM.topologicalKrullDim_image_le E hE)) (lt_irrefl _)
  choose e he he' using hmem
  refine Finite.of_injective (fun T ↦ (⟨e T, he T⟩ : F.support)) fun T T' h ↦ ?_
  have h' : e T = e T' := congrArg Subtype.val h
  exact Subtype.ext (SetLike.coe_injective ((he' T).symm.trans (h' ▸ he' T')))

/-- The flat families of forms on `𝒱_T` form a finite-dimensional space. -/
private theorem finite_flatForms (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To) :
    Module.Finite ℚ (flatForms (curveLocalSystem sY To)) := by
  obtain ⟨-, -, hconn, hlpc⟩ := isLocalSystemOpen_facts hM.isResolution.1 hdim
    hTo.toIsLocalSystemOpen
  haveI := hlpc
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 hconn
  obtain ⟨t₀⟩ := hconn.toNonempty
  exact (finite_and_finrank_flatForms hTo.isLocalSystem t₀).1

/-- **The dimension of the monodromy-invariant forms** is the rank `b_T`. -/
private theorem finrank_flatForms (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To) :
    Module.finrank ℚ (flatForms (curveLocalSystem sY To)) = curveLocalSystemRank sY To := by
  obtain ⟨-, -, hconn, hlpc⟩ := isLocalSystemOpen_facts hM.isResolution.1 hdim
    hTo.toIsLocalSystemOpen
  haveI := hlpc
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 hconn
  obtain ⟨t₀⟩ := hconn.toNonempty
  exact (finite_and_finrank_flatForms hTo.isLocalSystem t₀).2.trans
    ((IsLocalSystemOpen.curveLocalSystemRank_eq hM.isResolution.1 hM.topologicalKrullDim_eq
      hdim hT hTo.toIsLocalSystemOpen hTo.toIsLocalSystemOpen).2 t₀).symm

end Steps

/-! ### Assembly -/

private theorem solution
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) :
    ∃ T₀ : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
      (∀ T, IsAdaptedOpen sY r (T₀ T)) ∧
      ∀ To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
          topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
        (∀ T, To T ≤ T₀ T ∧ IsAdaptedOpen sY r (To T)) →
      -- the monodromy-invariant forms: flat families of forms on the stalks of `𝒱_T`
      let M : Submodule ℚ (∀ T, ∀ t : analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY),
          Module.Dual ℚ (curveLocalSystemFibre sY (To T) t)) :=
        Submodule.pi Set.univ fun T ↦
          ⨅ (O : Opens (analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY)))
            (_ : IsPreconnected (O : Set (analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY))))
            (s : ((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY (To T))).obj (op O))
            (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
            LinearMap.ker
              (LinearMap.applyₗ (R := ℚ)
                  (((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY (To T))).germ O t ht s) ∘ₗ
                  LinearMap.proj (R := ℚ)
                    (φ := fun t ↦ Module.Dual ℚ (curveLocalSystemFibre sY (To T) t)) t -
                LinearMap.applyₗ (R := ℚ)
                  (((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY (To T))).germ O t' ht' s) ∘ₗ
                  LinearMap.proj (R := ℚ)
                    (φ := fun t ↦ Module.Dual ℚ (curveLocalSystemFibre sY (To T) t)) t')
      ∃ Φ : AlgebraicDefect F →ₗ[ℚ] M,
        -- `Φ [x]` pairs `r_t α` with the sum of the curve classes of the `Lᵢ` on `F_t`
        (∀ T (x : algebraicKernel F) (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme),
            (∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x.1 E) →
          ∀ᶠ t : analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY) in Filter.cofinite,
          ∃ _ : IsComplexScheme (pointFibre sY r (To T) t),
          ∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY (To T) t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
            (p : pointFibre sY r (To T) t)
            (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r (To T) t ↘ Spec (.of ℂ)) p = (0 : ℕ)),
            borelMooreHomology.capProduct ℚ
                (analyticSpace (pointFibre sY r (To T) t ↘ Spec (.of ℂ))) Set.univ 2 2
                ((rationalCohomologyMap (pointFibreInclusion sY r (To T) t hV) 2).hom α)
                (∑ E : F.support, (L E).sum fun P c ↦ c •
                  ∑ᶠ (C : {x : pointFibre sY r (To T) t //
                      relativeDimension (fieldChowSituation ℂ).dimensionFunction
                        (pointFibre sY r (To T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                    (_ : Maximal (fun A : Set (pointFibre sY r (To T) t) ↦ IsIrreducible A ∧
                      A ⊆ (pointFibreFst sY r (To T) t).base ⁻¹'
                        (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                      (closure {C.1})),
                    fundamentalClass C.1 C.2) =
              (Φ (Submodule.Quotient.mk x)).1 T t
                  ((localSystemRestrictionFibre sY hM.isBiregular (To T) t).hom
                    ((stalkToPullbackStalk (curveOpenInclusion sY (To T))
                      (resolutionHigherDirectImage sY r 2) t).hom
                      ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α))) •
                fundamentalClass p hp) ∧
        Module.finrank ℚ M = ∑ᶠ T, curveLocalSystemRank sY (To T) := by
  classical
  -- the adapted opens of the exact sequence
  have hex := fun T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1} ↦
    hM.exists_exact_localSystemRestriction T.2.1 T.2.2
  choose T₀ hT₀ hT₀seq using hex
  refine ⟨T₀, hT₀, fun To hTo ↦ ?_⟩
  intro M
  have hsurj : ∀ T t, Function.Surjective
      (localSystemRestrictionFibre sY hM.isBiregular (To T) t).hom := fun T t ↦ by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hT₀seq T (To T) (hTo T).1 (hTo T).2
    exact h t
  -- the pinned flat family of each `x ∈ K(r)`
  choose ψ hψflat hψpin using fun T x ↦
    exists_mem_flatForms_forall_isPinned hM T.2.1 T.2.2 (hTo T).2 (hsurj T) x
  -- every `x ∈ K(r)` has divisor representatives
  have hrep : ∀ x : algebraicKernel F, ∃ L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme,
      ∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x.1 E := fun x ↦ by
    have hx := ((mem_exceptionalKernel F).1 x.2).1
    choose L hL using fun E ↦ (hx E : x.1 E ∈ LinearMap.range _)
    exact ⟨L, hL⟩
  choose Lx hLx using hrep
  -- `x ↦ ψ_x` is linear
  let Ψ : algebraicKernel F →ₗ[ℚ] M :=
    { toFun := fun x ↦ ⟨fun T ↦ ψ T x, fun T _ ↦ hψflat T x⟩
      map_add' := fun x y ↦ Subtype.ext <| funext fun T ↦
        eq_of_isPinned hM T.2.1 T.2.2 (hTo T).2 (hsurj T) (hψflat T (x + y)) (add_mem (hψflat T x) (hψflat T y))
          (hψpin T (x + y) (Lx x + Lx y) fun E ↦ by
            rw [Pi.add_apply, map_add, hLx, hLx]; rfl)
          (isPinned_add hM (hψpin T x _ (hLx x)) (hψpin T y _ (hLx y)))
      map_smul' := fun c x ↦ Subtype.ext <| funext fun T ↦
        eq_of_isPinned hM T.2.1 T.2.2 (hTo T).2 (hsurj T) (hψflat T (c • x)) (Submodule.smul_mem _ c (hψflat T x))
          (hψpin T (c • x) (c • Lx x) fun E ↦ by
            rw [Pi.smul_apply, map_smul, hLx]; rfl)
          (isPinned_smul hM c (hψpin T x _ (hLx x))) }
  -- it kills the classes of oriented double-surface systems
  have hB : (orientedSurfaceClasses F).comap (algebraicKernel F).subtype ≤ LinearMap.ker Ψ := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := (mem_orientedSurfaceClasses F).1 hx
    refine LinearMap.mem_ker.2 (Subtype.ext (funext fun T ↦ ?_))
    have hpin := hψpin T x (fun E ↦ surfaceCoefficientDivisor a E.1) fun E ↦ (hxa E).symm
    refine eq_of_isPinned hM T.2.1 T.2.2 (hTo T).2 (hsurj T) (hψflat T x) (zero_mem _) hpin ?_
    filter_upwards [hpin] with t ht
    obtain ⟨_, -⟩ := ht
    refine ⟨‹_›, fun V hV α p hp ↦ ?_⟩
    calc _ = borelMooreHomology.capProduct ℚ _ Set.univ 2 2
          ((rationalCohomologyMap (pointFibreInclusion sY r (To T) t hV) 2).hom α) 0 :=
          congrArg _ (sum_surfaceCoefficientDivisor_eq_zero hM ha _ t)
      _ = _ := by simp <;> rfl
  refine ⟨(Submodule.liftQ _ Ψ hB), fun T x L hL ↦ hψpin T x L hL, ?_⟩
  -- the dimension of the target
  haveI : Finite {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1} := finite_curves hM
  haveI := Fintype.ofFinite {T : IrreducibleCloseds Y //
    (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧ topologicalKrullDim (T : Set Y) = 1}
  let e : M ≃ₗ[ℚ] ∀ T, flatForms (curveLocalSystem sY (To T)) :=
    { toFun := fun w T ↦ ⟨w.1 T, w.2 T trivial⟩
      invFun := fun w ↦ ⟨fun T ↦ (w T).1, fun T _ ↦ (w T).2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  haveI := fun T : {T : IrreducibleCloseds Y //
      (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧ topologicalKrullDim (T : Set Y) = 1} ↦
    finite_flatForms hM T.2.2 (hTo T).2
  rw [e.finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun T _ ↦ finrank_flatForms hM T.2.1 T.2.2 (hTo T).2

end Proof_lem_mmp_conductor_generic_kernel_restriction

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MMP
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open scoped MMP.SubschemeOver
open Stacks.Chow (fieldChowSituation relativeDimension)

namespace MMP.Fourfold

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Generic restrictions of the algebraic kernel.** For a curve-and-point exceptional model
`r : Z ⟶ Y` with exceptional divisor `F`, there are adapted opens `T₀ ⊆ T` of the curves
`T ⊆ Sing Y` such that, for all adapted opens `T° ⊆ T₀`, there is a `ℚ`-linear map `Φ` from the
algebraic defect `K(r)/B(r)` (`MMP.Fourfold.AlgebraicDefect`) to the space `M` of families of
monodromy-invariant linear forms on the punctured local systems `𝒱_T` (`curveLocalSystem`), with
`dim M = ∑_T b_T` (`curveLocalSystemRank`), such that: for `x ∈ K(r)` represented by
`ℚ`-divisors `(Lᵢ)` on the components `Fᵢ`, all but finitely many points `t ∈ T°(ℂ)` (the
exceptional points depending on `(Lᵢ)`) and every germ `α` of `𝒲_t`, the
form `Φ [x]` at `t` takes on `r_t α` the value `⟨α|_{F_t}, w_T(t)⟩`, where `w_T(t)` is the sum of
the fundamental classes of the curves `Lᵢ ∩ F_t`. -/
@[mmp "lem_mmp_conductor_generic_kernel_restriction"]
public theorem IsCurvePointExceptionalModel.exists_linearMap_curveLocalSystemDual
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) :
    ∃ T₀ : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
      (∀ T, IsAdaptedOpen sY r (T₀ T)) ∧
      ∀ To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
          topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
        (∀ T, To T ≤ T₀ T ∧ IsAdaptedOpen sY r (To T)) →
      -- the monodromy-invariant forms: flat families of forms on the stalks of `𝒱_T`
      let M : Submodule ℚ (∀ T, ∀ t : analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY),
          Module.Dual ℚ (curveLocalSystemFibre sY (To T) t)) :=
        Submodule.pi Set.univ fun T ↦
          ⨅ (O : Opens (analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY)))
            (_ : IsPreconnected (O : Set (analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY))))
            (s : ((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY (To T))).obj (op O))
            (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
            LinearMap.ker
              (LinearMap.applyₗ (R := ℚ)
                  (((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY (To T))).germ O t ht s) ∘ₗ
                  LinearMap.proj (R := ℚ)
                    (φ := fun t ↦ Module.Dual ℚ (curveLocalSystemFibre sY (To T) t)) t -
                LinearMap.applyₗ (R := ℚ)
                  (((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY (To T))).germ O t' ht' s) ∘ₗ
                  LinearMap.proj (R := ℚ)
                    (φ := fun t ↦ Module.Dual ℚ (curveLocalSystemFibre sY (To T) t)) t')
      ∃ Φ : AlgebraicDefect F →ₗ[ℚ] M,
        -- `Φ [x]` pairs `r_t α` with the sum of the curve classes of the `Lᵢ` on `F_t`
        (∀ T (x : algebraicKernel F) (L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme),
            (∀ E, Chow.divisorClass E.1.idealSheaf.subscheme (L E) = x.1 E) →
          ∀ᶠ t : analyticSpace ((To T).ι ≫ curveι T.1 ≫ sY) in Filter.cofinite,
          ∃ _ : IsComplexScheme (pointFibre sY r (To T) t),
          ∀ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY (To T) t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
            (p : pointFibre sY r (To T) t)
            (hp : relativeDimension (fieldChowSituation ℂ).dimensionFunction
              (pointFibre sY r (To T) t ↘ Spec (.of ℂ)) p = (0 : ℕ)),
            borelMooreHomology.capProduct ℚ
                (analyticSpace (pointFibre sY r (To T) t ↘ Spec (.of ℂ))) Set.univ 2 2
                ((rationalCohomologyMap (pointFibreInclusion sY r (To T) t hV) 2).hom α)
                (∑ E : F.support, (L E).sum fun P c ↦ c •
                  ∑ᶠ (C : {x : pointFibre sY r (To T) t //
                      relativeDimension (fieldChowSituation ℂ).dimensionFunction
                        (pointFibre sY r (To T) t ↘ Spec (.of ℂ)) x = (1 : ℕ)})
                    (_ : Maximal (fun A : Set (pointFibre sY r (To T) t) ↦ IsIrreducible A ∧
                      A ⊆ (pointFibreFst sY r (To T) t).base ⁻¹'
                        (E.1.idealSheaf.subschemeι.base '' (P.support : Set _)))
                      (closure {C.1})),
                    fundamentalClass C.1 C.2) =
              (Φ (Submodule.Quotient.mk x)).1 T t
                  ((localSystemRestrictionFibre sY hM.isBiregular (To T) t).hom
                    ((stalkToPullbackStalk (curveOpenInclusion sY (To T))
                      (resolutionHigherDirectImage sY r 2) t).hom
                      ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α))) •
                fundamentalClass p hp) ∧
        Module.finrank ℚ M = ∑ᶠ T, curveLocalSystemRank sY (To T) :=
  Proof_lem_mmp_conductor_generic_kernel_restriction.solution hM

end MMP.Fourfold
