module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Intersection.Surface.IsotropicDivisorIndex
import MMP.AlgebraicGeometry.Intersection.ThreefoldIsotropicHodgeIndex
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.IsolatedPointAlgebraicKernel
import MMP.AlgebraicGeometry.Intersection.ThreefoldHodgeIndex
import MMP.AlgebraicGeometry.MMP.Fourfold.AlgebraicKernelRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.GenericRestrictionInjective
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.KernelStep
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreHomologyDetection
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.GenericDefect.FibreCycle
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.Analytic.Curve.TopCompactCohomology
import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.NormChernAverage
public import MMP.Topology.KrullDimensionProperClosed
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# The generic algebraic defect map is injective

Let `r : Z ⟶ Y` be a curve-and-point exceptional model of a normal projective `ℚ`-factorial
terminal complex fourfold `Y`, with exceptional divisor `F = ∑ Fᵢ`. A tuple `(Lᵢ)ᵢ` of
`ℚ`-divisors `Lᵢ` on the components `Fᵢ` defines, for each singular curve `T` of `Y` and each
`ℂ`-point `t` of `T`, the class
`w_T(t) = ∑ᵢ [Lᵢ|_{(Fᵢ)_t}] ∈ H_2(F_t, ℚ)`
of the sum of its fundamental curve classes on the surface fibre `F_t = r⁻¹(t)`. This gives the
map `K(r)/B(r) → ⨁_T (V_T^*)^{π₁(T)}` on the algebraic defect. The map is injective: if
`∑ᵢ (ιᵢ)_* [Lᵢ] = 0` in `H_4(Z, ℚ)` and `w_T(t) = 0` for the general point `t` of every singular
curve `T`, then `([Lᵢ])ᵢ` is the class tuple of an oriented double-surface system. In particular
`dim K(r)/B(r) ≤ ∑_T b_T`.

## Main results

* `MMP.Fourfold.IsCurvePointExceptionalModel.mem_orientedSurfaceClasses_and_finrank_le`: the
  injectivity of the generic algebraic defect map, and the bound `dim K(r)/B(r) ≤ ∑_T b_T`.

## Implementation notes

* The map is pinned by its value on a divisor tuple, and its injectivity is stated as the
  vanishing of its kernel: a tuple `(Lᵢ)ᵢ` with `∑ᵢ (ιᵢ)_* [Lᵢ] = 0` whose fibre classes vanish
  lies in `B(r)`. Every element of `K(r)` is the class tuple of a divisor tuple, so this is
  injectivity on `K(r)/B(r)`. The target `(V_T^*)^{π₁(T)}` is a subspace of `H_2(F_t, ℚ)` for
  `t ∈ T°`, so the value is zero exactly when `w_T(t) = 0` there.
* The restriction of a prime divisor `P` of `Fᵢ` to the fibre is the scheme `P ×_Y t`. Its
  curve cycle is the dimension-one part of its fundamental cycle, pushed forward to `F_t`. For
  general `t` this is the intersection of `P` with the fibre `(Fᵢ)_t`, with the right
  multiplicities. The hypothesis asks for the vanishing at every `ℂ`-point of a dense open of
  `T`. `w_T` is locally constant on `T°`, so this is the same as vanishing on `T°`.
* `b_T` is `MMP.Fourfold.curveLocalSystemRank` on a `r`-adapted open `T°` of `T`. It does not
  depend on that choice, and the bound is stated for every choice. The singular curves of `Y`
  are the irreducible closed subsets of `Sing Y` of dimension one.
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MMP
open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open scoped MMP.SubschemeOver

namespace Proof_thm_mmp_conductor_generic_defect_injective

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

noncomputable section LocalSystemGerms

open Opposite Limits

section Transport

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

private theorem bijective_stalkToPullbackStalk (x : X) :
    Function.Bijective (stalkToPullbackStalk f F x).hom := by
  rw [show stalkToPullbackStalk f F x = (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv
    from (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm]
  exact (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).symm.toLinearEquiv.bijective

end Transport

/-- The germ at `y` of the constant section with value `e`. -/
private noncomputable def constGerm {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ) (y : Y) :
    E →ₗ[ℚ] ToType (((TopCat.Sheaf.forget _ Y).obj (cSh Y E)).stalk y) :=
  (((TopCat.Sheaf.forget _ Y).obj (cSh Y E)).germ ⊤ y (Opens.mem_top y)).hom ∘ₗ
    ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).obj E)).app (op ⊤)).hom

private theorem constGerm_bijective {Y : TopCat.{0}} (E : ModuleCat.{0} ℚ) (y : Y) :
    Function.Bijective (constGerm E y) := by
  refine ⟨?_, fun c => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun e he => eq_zero_of_germ_constSection E y he
  · exact constantSheaf_exists_constSection_germ E y c

/-- The fibres of a local system are finite-dimensional. -/
private theorem finite_stalk_of_isLocalSystem {X : TopCat.{0}}
    {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (hL : IsLocalSystem L) (x : X) :
    Module.Finite ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk x) := by
  obtain ⟨V, hx, E, hE, ⟨φ⟩⟩ := hL x
  let y : (Opens.toTopCat X).obj V := ⟨x, hx⟩
  let e1 := LinearEquiv.ofBijective (stalkToPullbackStalk V.inclusion' L y).hom
    (bijective_stalkToPullbackStalk _ _ y)
  let e2 := ((TopCat.Presheaf.stalkFunctor _ y).mapIso
    ((TopCat.Sheaf.forget _ _).mapIso φ)).toLinearEquiv
  let e3 := (LinearEquiv.ofBijective _ (constGerm_bijective E y)).symm
  exact Module.Finite.equiv (e1.trans (e2.trans e3)).symm

end LocalSystemGerms

section FlatForms

open Opposite

variable {X : TopCat.{0}}

/-- The flat families of forms on the fibres of a sheaf `L`: families `φ_t ∈ L_t^*` such that
`φ_t (s_t) = φ_{t'} (s_{t'})` for every section `s` over a preconnected open containing `t, t'`. -/
private noncomputable def flatForms (L : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    Submodule ℚ (∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t)) :=
  ⨅ (O : Opens X) (_ : IsPreconnected (O : Set X))
    (s : ((TopCat.Sheaf.forget _ _).obj L).obj (op O)) (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
    LinearMap.ker
      (LinearMap.applyₗ (R := ℚ) (((TopCat.Sheaf.forget _ _).obj L).germ O t ht s) ∘ₗ
          LinearMap.proj (R := ℚ)
            (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t)) t -
        LinearMap.applyₗ (R := ℚ) (((TopCat.Sheaf.forget _ _).obj L).germ O t' ht' s) ∘ₗ
          LinearMap.proj (R := ℚ)
            (φ := fun t ↦ Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t)) t')

private theorem mem_flatForms {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {φ : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t)} :
    φ ∈ flatForms L ↔ ∀ (O : Opens X), IsPreconnected (O : Set X) →
      ∀ (s : ((TopCat.Sheaf.forget _ _).obj L).obj (op O)) (t) (ht : t ∈ O) (t') (ht' : t' ∈ O),
        φ t (((TopCat.Sheaf.forget _ _).obj L).germ O t ht s) =
          φ t' (((TopCat.Sheaf.forget _ _).obj L).germ O t' ht' s) := by
  simp only [flatForms, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.applyₗ_apply_apply, sub_eq_zero]

/-- Near every point, a flat family of forms takes, at any two nearby points, the same values on
suitable germs: any germ at one point is matched by a germ at the other. -/
private theorem exists_isOpen_forall_flatForms_apply_eq {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    [LocallyConnectedSpace X] (hL : IsLocalSystem L)
    {φ : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t)}
    (hφ : φ ∈ flatForms L) (z : X) :
    ∃ V : Set X, IsOpen V ∧ z ∈ V ∧ ∀ z' ∈ V, ∀ y' : ((TopCat.Sheaf.forget _ X).obj L).stalk z',
      ∀ z'' ∈ V, ∃ y'' : ((TopCat.Sheaf.forget _ X).obj L).stalk z'', φ z' y' = φ z'' y'' := by
  obtain ⟨V₀, hzV₀, hext⟩ := exists_germExtendable L hL z
  refine ⟨connectedComponentIn (V₀ : Set X) z, V₀.isOpen.connectedComponentIn,
    mem_connectedComponentIn hzV₀, ?_⟩
  intro z' hz' y' z'' hz''
  have hV₀ : connectedComponentIn (V₀ : Set X) z ⊆ V₀ := connectedComponentIn_subset _ _
  obtain ⟨Y, hY, hloc⟩ := hext z' (hV₀ hz') y'
  refine ⟨Y z'', ?_⟩
  rw [← hY]
  let g : connectedComponentIn (V₀ : Set X) z → ℚ := fun w => φ w.1 (Y w.1)
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    obtain ⟨W, r, N, hwN, hNW, hNloc⟩ := hloc w.1 (hV₀ w.2)
    let N' : Opens X := ⟨connectedComponentIn ((N : Set X) ∩ connectedComponentIn (V₀ : Set X) z)
      w.1, (N.isOpen.inter V₀.isOpen.connectedComponentIn).connectedComponentIn⟩
    have hwN' : w.1 ∈ N' := mem_connectedComponentIn ⟨hwN, w.2⟩
    have hN'N : N' ≤ N := fun x hx => (connectedComponentIn_subset _ _ hx).1
    have hN'W : N' ≤ W := hN'N.trans hNW
    have hN'pre : IsPreconnected (N' : Set X) := isPreconnected_connectedComponentIn
    let sres := ((TopCat.Sheaf.forget _ X).obj L).map (homOfLE hN'W).op r
    have hgerm : ∀ x (hx : x ∈ N'), ((TopCat.Sheaf.forget _ X).obj L).germ N' x hx sres = Y x :=
      fun x hx => by
        rw [TopCat.Presheaf.germ_res_apply, hNloc x (hN'N hx)]
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (N'.isOpen.mem_nhds hwN')] with w₂ hw₂
    change φ w₂.1 (Y w₂.1) = φ w.1 (Y w.1)
    rw [← hgerm w₂.1 hw₂, ← hgerm w.1 hwN']
    exact (mem_flatForms.1 hφ) N' hN'pre sres w₂.1 hw₂ w.1 hwN'
  haveI : PreconnectedSpace (connectedComponentIn (V₀ : Set X) z) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  exact hg.apply_eq_of_preconnectedSpace ⟨z', hz'⟩ ⟨z'', hz''⟩

/-- On a connected, locally connected space, a flat family of forms on the fibres of a local
system vanishing at one point vanishes. -/
private theorem eq_zero_of_mem_flatForms {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    [ConnectedSpace X] [LocallyConnectedSpace X] (hL : IsLocalSystem L)
    {φ : ∀ t : X, Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t)}
    (hφ : φ ∈ flatForms L) (t₀ : X) (h0 : φ t₀ = 0) : φ = 0 := by
  let S : Set X := {t | φ t = 0}
  have hopen : IsOpen S := isOpen_iff_forall_mem_open.2 fun z hz => by
    obtain ⟨V, hV, hzV, hVφ⟩ := exists_isOpen_forall_flatForms_apply_eq hL hφ z
    refine ⟨V, fun z₂ hz₂ => ?_, hV, hzV⟩
    refine LinearMap.ext fun y₂ => ?_
    obtain ⟨y, hy⟩ := hVφ z₂ hz₂ y₂ z hzV
    have hz' : φ z = 0 := hz
    rw [hy, hz']
    rfl
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hV, hzV, hVφ⟩ := exists_isOpen_forall_flatForms_apply_eq hL hφ z
    refine ⟨V, fun z₂ hz₂ h₂ => hz ?_, hV, hzV⟩
    refine LinearMap.ext fun y => ?_
    obtain ⟨y₂, hy⟩ := hVφ z hzV y z₂ hz₂
    have h₃ : φ z₂ = 0 := h₂
    rw [hy, h₃]
    rfl
  have huniv : S = Set.univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨t₀, h0⟩)
  funext t
  exact (huniv ▸ Set.mem_univ t : t ∈ S)

/-- On a connected, locally connected space, the flat families of forms on the fibres of a local
system form a finite-dimensional space. -/
private theorem finite_flatForms {L : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    [ConnectedSpace X] [LocallyConnectedSpace X] (hL : IsLocalSystem L) :
    Module.Finite ℚ (flatForms L) := by
  obtain ⟨t₀⟩ := (ConnectedSpace.toNonempty : Nonempty X)
  haveI := finite_stalk_of_isLocalSystem hL t₀
  let e : flatForms L →ₗ[ℚ] Module.Dual ℚ (((TopCat.Sheaf.forget _ X).obj L).stalk t₀) :=
    (LinearMap.proj t₀).comp (flatForms L).subtype
  refine Module.Finite.of_injective e fun a b hab => Subtype.ext ?_
  have h := eq_zero_of_mem_flatForms hL (sub_mem a.2 b.2) t₀ (by
    change a.1 t₀ - b.1 t₀ = 0
    exact sub_eq_zero.2 hab)
  exact sub_eq_zero.1 h

end FlatForms

section CurveRealization

/-- The complex realization of a local-system open of a curve of a complex variety is connected
and locally connected. -/
private theorem connectedSpace_and_locallyConnectedSpace_of_isLocalSystemOpen
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}
    (hY : MMP.Mori.IsVariety ℂ sY) {W : (curveScheme T).Opens} (hW : IsLocalSystemOpen sY W) :
    ConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) ∧
      LocallyConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : Smooth (W.ι ≫ curveι T ≫ sY) := hW.smooth
  haveI : ConnectedSpace W := hW.connectedSpace
  haveI : IsIntegral W :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (W.ι ≫ curveι T ≫ sY)
  haveI := locallyPathConnectedSpace_analyticSpace (W.ι ≫ curveι T ≫ sY)
  exact ⟨connectedSpace_analyticSpace _, inferInstance⟩

/-- A curve-and-point exceptional model has finitely many singular curves: each is the image of
a component of the exceptional divisor. -/
private theorem finite_singularCurves {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) :
    Finite {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1} := by
  classical
  obtain ⟨-, -, -, hproj, hbir⟩ := hr.isResolution
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hproj
  haveI : IsDominant r := hbir.isDominant
  have hsurj : Function.Surjective r.base := r.surjective
  have hcurve : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1}, ∃ P : F.support,
        (T.1 : Set Y) = r.base '' (P.1.support : Set Z) := by
    rintro ⟨T, hTsing, hTdim⟩
    have hsub : (T : Set Y) ⊆ ⋃₀ ((F.support.image fun P => r.base '' (P.support : Set Z) :
        Finset (Set Y)) : Set (Set Y)) := by
      intro y hy
      obtain ⟨z, rfl⟩ := hsurj y
      have hz : z ∈ (F.supp : Set Z) := by
        rw [hr.supp_eq_preimage_singularLocus]
        exact hTsing hy
      rw [MMP.Mori.DivisorWithCoeffs.coe_supp] at hz
      obtain ⟨P, hP, hzP⟩ := Set.mem_iUnion₂.1 hz
      exact ⟨_, Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP, rfl⟩), z, hzP, rfl⟩
    obtain ⟨C, hC, hTC⟩ := (isIrreducible_iff_sUnion_isClosed.1 T.isIrreducible) _
      (fun C hC => by
        obtain ⟨P, -, rfl⟩ := Finset.mem_image.1 hC
        exact r.isClosedMap _ P.idealSheaf.support.isClosed) hsub
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hC
    refine ⟨⟨P, hP⟩, ?_⟩
    by_contra hne
    have hirr : IsIrreducible (r.base '' (P.support : Set Z)) := by
      rw [show (P.support : Set Z) = closure {P.genericPoint} from
        AlgebraicGeometry.PrimeDivisor.support_eq_closure P]
      exact isIrreducible_singleton.closure.image _ r.continuous.continuousOn
    have hle := hr.topologicalKrullDim_image_le P hP
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hirr T.isClosed hTC hne
      (ne_top_of_le_ne_top (by decide) hle)
    rw [hTdim] at hlt
    exact absurd (hlt.trans_le hle) (lt_irrefl _)
  choose g hg using hcurve
  refine Finite.of_injective g fun T T' h => Subtype.ext (IrreducibleCloseds.ext ?_)
  rw [hg T, hg T', h]

end CurveRealization

/-- The dimension bound `dim K(r)/B(r) ≤ ∑_T b_T`, from the kernel step and the generic
restriction to the monodromy-invariant forms. -/
private theorem finrank_algebraicDefect_le
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsComplexScheme Z]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D)
    (To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (hTo : ∀ T, IsAdaptedOpen sY r (To T)) :
    Module.finrank ℚ (AlgebraicDefect F) ≤ ∑ᶠ T, curveLocalSystemRank sY (To T) := by
  obtain ⟨T₀, hT₀, hΦ⟩ := hr.exists_linearMap_curveLocalSystemDual
  have hY : MMP.Mori.IsVariety ℂ sY :=
    ((MMP.Mori.isProjectiveVariety_iff ℂ sY).1 hr.isProjectiveVariety).1
  have hrank : ∀ T, curveLocalSystemRank sY (T₀ T) = curveLocalSystemRank sY (To T) := fun T =>
    (IsLocalSystemOpen.curveLocalSystemRank_eq hY hr.topologicalKrullDim_eq T.2.2 T.2.1
      (hT₀ T).toIsLocalSystemOpen (hTo T).toIsLocalSystemOpen).1
  obtain ⟨Φ, hΦval, hfin⟩ := hΦ T₀ fun T => ⟨le_rfl, hT₀ T⟩
  have hinj : Function.Injective Φ :=
    hr.injective_curveLocalSystemDual T₀ _ Φ hΦval
      hr.mem_orientedSurfaceClasses_of_fibre_vanishing
      (hr.eq_zero_of_capProduct_restrict_eq_zero T₀)
      (hr.exists_dense_rationalCycleClass_fibreCycle_eq_zero T₀ hT₀)
  have hM : Module.Finite ℚ (type_of% (Φ 0)) := by
    haveI : Finite {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1} :=
      finite_singularCurves hr
    have hfin : ∀ T, Module.Finite ℚ (flatForms (curveLocalSystem sY (T₀ T))) := fun T => by
      have h := connectedSpace_and_locallyConnectedSpace_of_isLocalSystemOpen hY
        (hT₀ T).toIsLocalSystemOpen
      haveI := h.1
      haveI := h.2
      exact finite_flatForms (hT₀ T).isLocalSystem
    let e : type_of% (Φ 0) →ₗ[ℚ] ∀ T, flatForms (curveLocalSystem sY (T₀ T)) :=
      { toFun := fun x T => ⟨x.1 T, x.2 T (Set.mem_univ _)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Module.Finite.of_injective e fun a b hab => Subtype.ext (funext fun T => ?_)
    exact congrArg Subtype.val (congrFun hab T)
  calc Module.finrank ℚ (AlgebraicDefect F) ≤ Module.finrank ℚ (type_of% (Φ 0)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = ∑ᶠ T, curveLocalSystemRank sY (To T) := by
        rw [hfin]
        exact finsum_congr hrank

end Proof_thm_mmp_conductor_generic_defect_injective

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MMP

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic
open scoped MMP.SubschemeOver

/-- **The generic algebraic defect map is injective.** Let `r : Z ⟶ Y` be a curve-and-point
exceptional model with exceptional divisor `F`. Let `(L_E)_E` be `ℚ`-divisors on the components
`E` of `F` with `∑_E (ι_E)_* [L_E] = 0` in `H_4(Z, ℚ)`. Suppose that, for every singular curve `T`
of `Y`, the fibre class `∑_E ∑_P (L_E)_P [P ×_Y t] ∈ H_2(F_t, ℚ)` vanishes at every `ℂ`-point `t`
of a dense open of `T`. Then `([L_E])_E ∈ B(r)`. In particular, for any `r`-adapted opens `T°`
of the singular curves `T`, `dim_ℚ K(r)/B(r) ≤ ∑_T b_T`. -/
@[mmp "thm_mmp_conductor_generic_defect_injective"]
public theorem IsCurvePointExceptionalModel.mem_orientedSurfaceClasses_and_finrank_le
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsComplexScheme Z]
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hr : IsCurvePointExceptionalModel sY r F D) :
    (∀ L : ∀ E : F.support, QDivisor E.1.idealSheaf.subscheme,
      ∑ E : F.support, componentHomologyMap E.1 4 (MMP.Chow.divisorClass _ (L E)) = 0 →
      (∀ T : IrreducibleCloseds Y, (T : Set Y) ⊆ (singularLocus sY : Set Y) →
          topologicalKrullDim (T : Set Y) = 1 →
        ∃ U : (curveScheme T).Opens, Dense (U : Set (curveScheme T)) ∧
          ∀ (t : ComplexPoints (U.ι ≫ curveι T ≫ sY))
            [IsComplexScheme (pointFibre sY r U t)],
            Chow.rationalCycleClass (pointFibre sY r U t) 1
              (∑ E : F.support, ∑ P ∈ (L E).support, (L E) P •
                (1 : ℚ) ⊗ₜ[ℤ] @Stacks.Chow.cycleAssociatedToClosedSubscheme
                  (Stacks.Chow.fieldChowSituation ℂ) _ _ (pointFibre sY r U t ↘ Spec (.of ℂ)) _
                  (pullback.map (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι ≫ r)
                    (t.hom ≫ U.ι ≫ curveι T) r (t.hom ≫ U.ι ≫ curveι T)
                    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) (𝟙 _) (𝟙 _)
                    ((Category.comp_id _).trans (Category.assoc _ _ _).symm)
                    ((Category.comp_id _).trans (Category.id_comp _).symm))
                  (isClosedImmersion_pullback_map_of_comp_eq
                    (P.idealSheaf.subschemeι ≫ E.1.idealSheaf.subschemeι) r (Category.assoc _ _ _)
                    (t.hom ≫ U.ι ≫ curveι T)) ((1 : ℕ) : ℤ)) = 0) →
      (fun E => MMP.Chow.divisorClass E.1.idealSheaf.subscheme (L E) : ComponentHomology F) ∈
        orientedSurfaceClasses F) ∧
    ∀ To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
        topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
      (∀ T, IsAdaptedOpen sY r (To T)) →
      Module.finrank ℚ (AlgebraicDefect F) ≤ ∑ᶠ T, curveLocalSystemRank sY (To T) := by
  open Proof_thm_mmp_conductor_generic_defect_injective in
  exact ⟨hr.mem_orientedSurfaceClasses_of_fibre_vanishing, finrank_algebraicDefect_le hr⟩

end MMP.Fourfold
