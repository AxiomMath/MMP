module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Monomial
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CompletionStalkLimit
import MMP.AlgebraicGeometry.Singularities.Surface.ExceptionalCycleEuler
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Resolution.Surface.MinimalResolution
import MMP.AlgebraicGeometry.Cohomology.FormalFunctionsDegreeZero
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi

/-!
# Rational surface singularities and their exceptional cycles

Let `(X, P)` be a normal surface germ over an algebraically closed field `k` of arbitrary
characteristic and `f : Y ⟶ X` a resolution, with exceptional curves `E_1, …, E_n`. A cycle
`Z = ∑ nᵢ Eᵢ` is the closed subscheme of `Y` with ideal `𝒪_Y(-Z) = ∏ I_{Eᵢ}^{nᵢ}`. This file
proves two results on these cycles.

**Artin's rationality criterion.** If `f` is the minimal resolution and `Γ = Γ(f)` its weighted
dual graph, then `(X, P)` is a rational singularity, i.e. `(R¹f_*𝒪_Y)_P = 0`, if and only if `Γ`
is a rational weighted graph: for every nonzero `z ∈ ℤ_{≥ 0}^{V(Γ)}`,
`1 + ½ (zᵀ M(Γ) z + ∑_j z_j (2p_j - 2 + n_j)) ≤ 0`. By the cycle formula
`χ(𝒪_Z) = -½ (Z² + K_Y · Z)` this says `χ(𝒪_Z) ≥ 1` for every nonzero effective exceptional
cycle `Z`. Write `A = 𝒪_{X,P}`, `X' = Y ×_X Spec A` and `X_m = Y ×_X Spec (A/𝔪ᵐ)`. By flat base
change `(R¹f_*𝒪_Y)_P = H¹(X', 𝒪_{X'})`, and `X_m ⟶ Y` is a closed immersion into the fibre
`f⁻¹(P)`, of dimension at most one; on such a scheme `H¹` of the structure sheaf surjects onto
`H¹` of the structure sheaf of every closed subscheme.
* If `Γ` is rational, `H¹(𝒪_Z) = 0` for every exceptional cycle. Every `X_m` lies in a cycle
  `r ∑ Eᵢ`, since the fibre is the union of the `Eᵢ` (it is connected because `X` is normal), so
  `H¹(𝒪_{X_m}) = 0`, and the uniform bound of the theorem on formal functions with Nakayama gives
  `H¹(X', 𝒪_{X'}) = 0`.
* Conversely `H¹(X', 𝒪_{X'}) = 0` and `H²(X', 𝔪ᵐ 𝒪_{X'}) = 0` give `H¹(𝒪_{X_m}) = 0`; every
  cycle `Z` lies in some `X_m`, so `H¹(𝒪_Z) = 0` and `χ(𝒪_Z) = h⁰(𝒪_Z) ≥ 1`.
Minimal resolutions are isomorphic over `X`, which transports the vanishing between them.

**Degree-zero invertible sheaves on rational cycles.** If `χ(𝒪_{Z'}) > 0` for every nonzero
effective cycle `Z' ≤ Z` and `L` is an invertible sheaf on `Y` of degree `0` on every component
of `Z`, then `L|_Z ≅ 𝒪_Z`. Each component `E` has `χ(𝒪_E) = 1`, so genus zero, and a degree-zero
invertible sheaf on it has a nonzero global section, which vanishes nowhere by
[Stacks, Tag 0B40]. For `Z ≠ 0`, positivity of `χ(𝒪_Z)` and the cycle formula give a component
`E` with `((Z - E) · E) ≤ 1`. Put `W = Z - E`. If `E` meets `W`, the kernel of `L|_Z ⟶ L|_W` is
`L|_E ⊗ 𝒪_Y(-W)|_E`, of degree `≥ -1` on the genus zero curve `E`, hence without `H¹`, so a
nowhere vanishing section of `L|_W` lifts to one of `L|_Z`. If `E` and `W` are disjoint,
`𝒪_Z = 𝒪_W ⊕ 𝒪_E` [Stacks, Tag 0C4J] and the sections glue.

## Main results

* `MMP.Flips.IsWeightedDualGraph.isRationalSurfaceSingularity_iff_isRational`: `(X, P)` is a
  rational singularity if and only if `Γ(f)` is rational.
* `MMP.Flips.IsGermResolution.nonempty_pullback_divisorIdeal_iso_unit`: the triviality
  `L|_Z ≅ 𝒪_Z`.

## Implementation notes

The weighted dual graph `MMP.Flips.IsWeightedDualGraph` is formed for a surface germ with
boundary `(X, P; B)`; the rationality of `Γ` does not involve the boundary weights, so Artin's
criterion holds for every boundary `B`.

A cycle `Z = ∑ z_j E_j` is handled as the multiset of its components counted with
multiplicity, its subscheme being cut out by `∏_{E ∈ Z} I_E`. The cycle formula is made explicit
by the additivity `(D · Z) = ∑ z_j (D · E_j)` of intersection numbers (the degree on `W + E` is
the sum of the degrees on `W` and on `E`) and by adjunction `K_Y · E_j = 2p_j - 2 + n_j`. A
section of an invertible sheaf trivialises it exactly when its nonvanishing locus is everything,
and the nonvanishing locus of a restriction is the preimage of the nonvanishing locus.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.4, 3.4.1
* [M. Artin, *On isolated rational singularities of surfaces*][Artin1966]
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-- The tensor product of two modules on a scheme, as a module. -/
local notation3 (prettyPrint := false) "tens" X:max F:max G:max =>
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(X : Scheme).toRingedSpace.presheaf, (X : Scheme).toRingedSpace.IsSheaf⟩).obj F).obj G

/-! ### First cohomology along closed immersions into curves -/

section Descent

/-- **`H¹(G) ⟶ H¹(G / 𝓘ⁿ G)` is surjective when `H²(𝓘ⁿ G) = 0`**: the long exact sequence of
`0 ⟶ 𝓘ⁿ G ⟶ G ⟶ G / 𝓘ⁿ G ⟶ 0`. -/
private theorem surjective_rightDerived_one_map_cokernel_π {T : Scheme.{u}}
    (J : T.IdealSheafData) (n : ℕ) (G : T.Modules)
    (h : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived (1 + 1)).obj
      (Stacks.Algebraization.idealPowerMultiple J n G).toSheafOfModules)) :
    Function.Surjective (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).map
      (cokernel.π (Stacks.Algebraization.idealPowerMultiple J n G).ι)) := by
  let S : ShortComplex T.Modules :=
    ShortComplex.mk _ _ (cokernel.condition (Stacks.Algebraization.idealPowerMultiple J n G).ι)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; exact coequalizer.π_epi }
  exact (ModuleCat.epi_iff_surjective _).1
    (Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_map_g hS _ 1 h)

/-- **`H¹` descends along a closed immersion into a Noetherian scheme of dimension at most one.**
If `t : T ⟶ T'` is a closed immersion, `T'` is Noetherian of dimension at most one and `G` is
quasi-coherent on `T'` with `H¹(T', G) = 0`, then `H¹(T, t^* G) = 0`: the cokernel of
`H¹(T', G) ⟶ H¹(T', G / 𝓘 G)` lies in `H²(T', 𝓘 G) = 0`, and `G / 𝓘 G = t_* t^* G`. -/
private theorem subsingleton_rightDerived_one_pullback {T T' : Scheme.{u}} (t : T ⟶ T')
    [IsClosedImmersion t] [IsNoetherian T'] (hdim : topologicalKrullDim T' ≤ 1)
    (G : T'.Modules) [G.IsQuasicoherent]
    (h : Subsingleton
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections T').rightDerived 1).obj G)) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      ((Scheme.Modules.pullback t).obj G)) := by
  have h3 := (surjective_rightDerived_one_map_cokernel_π t.ker 1 G
    ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      T'.ringCatSheaf ⊤ 2 _).2
      (Stacks.AlgebraicGeometry.FibreDimension.isZero_hgroup_of_topologicalKrullDim_le _
        (d := 1) (by exact_mod_cast hdim) (by norm_num)))).subsingleton
  have e := ((Stacks.Cohomology.AffineBase.moduleGlobalSections T').rightDerived 1).mapIso
      (Stacks.Algebraization.idealQuotientPushforwardIso t.ker 1 G t (pow_one _).symm) ≪≫
    Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward t
      ((Scheme.Modules.pullback t).obj G) 1
  exact @Equiv.subsingleton _ _ e.toLinearEquiv.toEquiv.symm h3

end Descent

/-! ### First cohomology of structure sheaves -/

section StructureSheaf

/-- The structure sheaf pulls back to the structure sheaf. -/
private def pullbackObjUnitIso {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  Stacks.PullbackAlgebra.pullbackUnitIso i.toLRSHom.toShHom

/-- **`H¹(𝒪)` descends along a closed immersion into a Noetherian scheme of dimension at most
one.** -/
private theorem subsingleton_rightDerived_one_unit {T T' : Scheme.{u}} (t : T ⟶ T')
    [IsClosedImmersion t] [IsNoetherian T'] (hdim : topologicalKrullDim T' ≤ 1)
    (h : Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T').rightDerived 1).obj
      (SheafOfModules.unit T'.ringCatSheaf))) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      (SheafOfModules.unit T.ringCatSheaf)) := by
  have h' := subsingleton_rightDerived_one_pullback t hdim (SheafOfModules.unit T'.ringCatSheaf) h
  exact @Equiv.subsingleton _ _ (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived
    1).mapIso (pullbackObjUnitIso t)).toLinearEquiv.toEquiv.symm h'

/-- **`H¹(𝒪)` vanishes on a Noetherian scheme of dimension zero.** -/
private theorem subsingleton_rightDerived_one_unit_of_topologicalKrullDim_le_zero
    {T : Scheme.{u}} [IsNoetherian T] (hdim : topologicalKrullDim T ≤ 0) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      (SheafOfModules.unit T.ringCatSheaf)) :=
  ModuleCat.subsingleton_of_isZero
    ((Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      T.ringCatSheaf ⊤ 1 _).2
      (Stacks.AlgebraicGeometry.FibreDimension.isZero_hgroup_of_topologicalKrullDim_le _
        (d := 0) (by exact_mod_cast hdim) (by norm_num)))

end StructureSheaf

/-! ### The theorem on formal functions at the closed point -/

section FormalFunctions

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsProper f] [IsLocallyNoetherian X] (P : X)

omit [IsProper f] [IsLocallyNoetherian X] in
open Stacks.AlgebraicGeometry.FibreDimension in
/-- **The fibres of `Y ×_X Spec 𝒪_{X,P} ⟶ Spec 𝒪_{X,P}` are no bigger than those of `f`.** The
projection to `Y` is a base change of the preimmersion `Spec 𝒪_{X,P} ⟶ X`, hence an embedding,
and it carries the fibre over `s` into the fibre of `f` over the image of `s`. -/
private theorem topologicalKrullDim_fiber_stalkBaseChangeStructure_le {d : ℕ}
    (hfib : ∀ x : X, topologicalKrullDim (f ⁻¹' {x}) ≤ d) (s : Spec (X.presheaf.stalk P)) :
    topologicalKrullDim ((stalkBaseChangeStructure f P).fiber s) ≤ d := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    ((stalkBaseChangeStructure f P).fiberHomeo s).isHomeomorph]
  have hemb : Topology.IsEmbedding (stalkBaseChangeι f P) :=
    IsPreimmersion.isEmbedding (stalkBaseChangeι f P)
  have hind : Topology.IsInducing
      (fun z : ((stalkBaseChangeStructure f P) ⁻¹' {s}) => stalkBaseChangeι f P z.1) :=
    hemb.isInducing.comp Topology.IsInducing.subtypeVal
  refine (topologicalKrullDim_le_of_isInducing_of_range_subset
    hind (S := f ⁻¹' {X.fromSpecStalk P s}) ?_).trans (hfib _)
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  have hz' : stalkBaseChangeStructure f P z = s := hz
  change f (stalkBaseChangeι f P z) = X.fromSpecStalk P s
  rw [← hz', ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

/-- **`(R¹f_*𝒪_Y)_P` vanishes as soon as the first cohomology of every infinitesimal
neighbourhood of the fibre does.** By flat base change the stalk is `H¹(X', 𝒪_{X'})` over the
local ring `A = 𝒪_{X,P}`; the uniform bound of [Stacks, Tag 02OB] puts the kernel of
`H¹(X', 𝒪_{X'}) ⟶ H¹(X', 𝒪_{X'} / 𝔪^{c+1})` inside `𝔪 H¹(X', 𝒪_{X'})`, the target is
`H¹(X_{c+1}, 𝒪) = 0`, and Nakayama concludes, the module being finite. -/
private theorem subsingleton_stalk_of_forall_subsingleton_infinitesimalCohomology
    (hT : ∀ m, Subsingleton
      (infinitesimalCohomology f (SheafOfModules.unit Y.ringCatSheaf) P 1 m)) :
    Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨e⟩ := nonempty_higherDirectImageStalkLinearEquiv f
    (SheafOfModules.unit Y.ringCatSheaf) P 1
  refine @Equiv.subsingleton _ _ e.toEquiv ?_
  have hA : IsNoetherianRing ↥(X.presheaf.stalk P) := inferInstance
  have hg : IsProper (stalkBaseChangeStructure f P) := inferInstance
  have : (stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P).IsCoherent :=
    isCoherent_pullback _ _
  have hcoh : Stacks.SheafOfModules.IsCoherent
      (stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P) :=
    Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent inferInstance
  obtain ⟨c, hker, -, -⟩ := @exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8
    ↥(X.presheaf.stalk P) _ hA _ (stalkBaseChangeStructure f P) hg
    (IsLocalRing.maximalIdeal _) _ hcoh 1 isReesFinite_cohomologyIdealPowerSystem
  set A := X.presheaf.stalk P
  set g := stalkBaseChangeStructure f P
  set O' := stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P
  have hzero : Subsingleton (cohomologyOverBase A g 1 (Stacks.Algebraization.idealPowerQuotient
      (baseIdealSheaf A (IsLocalRing.maximalIdeal A) g) (c + 1) O')) :=
    @Equiv.subsingleton _ _ (infinitesimalCohomologyEquiv f _ P 1 (c + 1)).toEquiv (hT (c + 1))
  have htop := hker (c + 1) (Nat.le_succ c)
  rw [LinearMap.ker_eq_top.2 (Subsingleton.elim _ _), Nat.add_sub_cancel_left, pow_one] at htop
  have : Module.Finite A (cohomologyOverBase A g 1 O') :=
    @Stacks.Algebraization.moduleFinite_cohomologyOverBase A _ _ g hA hg O' _ 1
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ Module.Finite.fg_top htop
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  exact subsingleton_of_forall_eq 0 fun x => by
    simpa using (Submodule.eq_bot_iff _).1 hbot x Submodule.mem_top

open Stacks.AlgebraicGeometry.FibreDimension in
/-- **The first cohomology of every infinitesimal neighbourhood of the fibre vanishes when
`(R¹f_*𝒪_Y)_P` does**, provided all fibres of `f` have dimension at most one. The stalk is
`H¹(X', 𝒪_{X'})`, and `H¹(X', 𝒪_{X'}) ⟶ H¹(X', 𝒪_{X'} / 𝔪ᵐ)` is surjective because
`H²(X', 𝔪ᵐ 𝒪_{X'}) = 0` ([Stacks, Tag 02V7] over `Spec A`, all of whose fibres have dimension
at most one). -/
private theorem subsingleton_infinitesimalCohomology_of_subsingleton_stalk
    (hfib : ∀ x : X, topologicalKrullDim (f ⁻¹' {x}) ≤ 1)
    (h : Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P)) (m : ℕ) :
    Subsingleton (infinitesimalCohomology f (SheafOfModules.unit Y.ringCatSheaf) P 1 m) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨e⟩ := nonempty_higherDirectImageStalkLinearEquiv f
    (SheafOfModules.unit Y.ringCatSheaf) P 1
  have hH := @Equiv.subsingleton _ _ e.toEquiv.symm h
  refine @Equiv.subsingleton _ _ (infinitesimalCohomologyEquiv f _ P 1 m).toEquiv.symm ?_
  have hg : IsProper (stalkBaseChangeStructure f P) := inferInstance
  have : (stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P).IsCoherent :=
    isCoherent_pullback _ _
  have : IsLocallyNoetherian (Spec (X.presheaf.stalk P)) := inferInstance
  set O' := stalkBaseChangeModule f (SheafOfModules.unit Y.ringCatSheaf) P
  have : (Stacks.Algebraization.idealPowerMultiple (infinitesimalBaseIdealSheaf f P) m
      O').toSheafOfModules.IsCoherent := Stacks.Algebraization.isCoherent_idealPowerMultiple _ _ _
  exact @Function.Surjective.subsingleton _ _ _ hH
    (surjective_rightDerived_one_map_cokernel_π _ m O'
      (isZero_rightDerived_moduleGlobalSections_of_affine_base
        (stalkBaseChangeStructure f P) (d := 1)
        (topologicalKrullDim_fiber_stalkBaseChangeStructure_le f P hfib) _ (by norm_num)))

end FormalFunctions

/-! ### The thickenings of the closed point -/

section Thickening

open Stacks.FormalFunctions

variable {X : Scheme.{u}}

/-- A global section whose basic open is everything is a unit. -/
private theorem isUnit_of_basicOpen_eq_top {Z : Scheme.{u}} (f : Γ(Z, ⊤))
    (h : Z.basicOpen f = ⊤) : IsUnit f := by
  have hu := RingedSpace.isUnit_res_basicOpen Z.toRingedSpace f
  have e : Opposite.op (⊤ : Z.Opens) = Opposite.op (Z.toRingedSpace.basicOpen f) := by
    rw [show Z.toRingedSpace.basicOpen f = Z.basicOpen f from rfl, h]
  have : (homOfLE (RingedSpace.basicOpen_le Z.toRingedSpace f)).op = eqToHom e := rfl
  rw [this] at hu
  exact (isUnit_map_iff
    ((Z.toRingedSpace.presheaf.mapIso (eqToIso e)).commRingCatIsoToRingEquiv) f).1 hu

/-- `Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X` has image in `{P}`. -/
private theorem range_infinitesimalBase_subset (P : X) (m : ℕ) :
    Set.range (infinitesimalBase P m) ⊆ {P} := by
  rintro _ ⟨z, rfl⟩
  rw [infinitesimalBase, Scheme.Hom.comp_apply]
  have : (Spec.map (toStalkQuotient P m)) z = IsLocalRing.closedPoint (X.presheaf.stalk P) := by
    apply PrimeSpectrum.ext
    rw [IsLocalRing.closedPoint]
    refine ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
      (Ideal.IsPrime.ne_top inferInstance) ?_).symm
    have h1 : stalkMaximalIdeal P ^ m ≤ ((Spec.map (toStalkQuotient P m)) z).asIdeal := by
      intro a ha
      change (toStalkQuotient P m).hom a ∈ z.asIdeal
      have : (toStalkQuotient P m).hom a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      rw [this]
      exact z.asIdeal.zero_mem
    exact Ideal.IsPrime.le_of_pow_le h1
  rw [this, Scheme.fromSpecStalk_closedPoint]
  rfl

/-- **`Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X` is a closed immersion at a closed point**: it is a preimmersion
with closed image. -/
private theorem isClosedImmersion_infinitesimalBase {P : X} (hP : IsClosed ({P} : Set X))
    (m : ℕ) : IsClosedImmersion (infinitesimalBase P m) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rcases Set.subset_singleton_iff_eq.1 (range_infinitesimalBase_subset P m) with h | h <;>
    rw [h]
  · exact isClosed_empty
  · exact hP

/-- **A morphism from a quasi-compact scheme onto a closed point factors through a
thickening of the point.** If `h : Z ⟶ X` maps every point to the closed point `P` of the
locally Noetherian `X`, then `h` factors through `Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X` for some `m`: on an
affine neighbourhood `Spec R` of `P`, with `P` the prime `q`, elements outside `q` become units
on `Z` and elements of `q` nilpotent, so `R ⟶ Γ(Z, 𝒪_Z)` factors through `R_q / q^m R_q`. -/
private theorem exists_comp_infinitesimalBase_eq [IsLocallyNoetherian X] {P : X}
    {Z : Scheme.{u}} [CompactSpace Z] (h : Z ⟶ X) (hh : ∀ z, h z = P) :
    ∃ (m : ℕ) (L : Z ⟶ Spec (stalkQuotient P m)), L ≫ infinitesimalBase P m = h := by
  obtain ⟨U, hU, hPU, -⟩ := exists_isAffineOpen_mem_and_subset (x := P) (U := ⊤) trivial
  have hrange : Set.range h ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, hh z]
    exact hPU
  set h0 := IsOpenImmersion.lift U.ι h hrange
  have hh0 : h0 ≫ U.ι = h := IsOpenImmersion.lift_fac _ _ _
  set h1 := h0 ≫ hU.isoSpec.hom
  have hh1 : h1 ≫ hU.fromSpec = h := by
    rw [← hU.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc, hh0]
  set q := hU.primeIdealOf ⟨P, hPU⟩
  have hq : ∀ z, h1 z = q := fun z => hU.fromSpec.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hh1, hh z, hU.fromSpec_primeIdealOf])
  set φ : Γ(X, U) →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ h1.appTop).hom with hφ
  have hmem : ∀ a z, z ∈ Z.basicOpen (φ a) ↔ a ∉ q.asIdeal := by
    intro a z
    have hb : Z.basicOpen (φ a) = h1 ⁻¹ᵁ (Spec Γ(X, U)).basicOpen ((Scheme.ΓSpecIso _).inv a) :=
      (Scheme.preimage_basicOpen h1 _).symm
    rw [hb, basicOpen_eq_of_affine]
    change h1 z ∈ PrimeSpectrum.basicOpen a ↔ _
    rw [hq z]
    rfl
  have hnil : ∀ a ∈ q.asIdeal, IsNilpotent (φ a) := fun a ha =>
    (Scheme.isNilpotent_iff_basicOpen_eq_bot _).2
      (eq_bot_iff.2 fun z hz => ((hmem a z).1 hz ha).elim)
  have hunit : ∀ s ∉ q.asIdeal, IsUnit (φ s) := fun s hs =>
    isUnit_of_basicOpen_eq_top _ (eq_top_iff.2 fun z _ => (hmem s z).2 hs)
  let : Algebra Γ(X, U) (X.presheaf.stalk P) := (X.presheaf.germ U P hPU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk P) q.asIdeal :=
    hU.isLocalization_stalk ⟨P, hPU⟩
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ' : X.presheaf.stalk P →+* Γ(Z, ⊤) :=
    IsLocalization.lift (M := q.asIdeal.primeCompl) (g := φ) (fun y => hunit y.1 y.2)
  have hφ' : ∀ a, φ' (algebraMap _ _ a) = φ a := IsLocalization.lift_eq _
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (I := Ideal.map φ q.asIdeal)
    (J := ⊥) (Ideal.map_le_iff_le_comap.2 fun a ha => by
      obtain ⟨n, hn⟩ := hnil a ha
      exact Ideal.mem_comap.2 ⟨n, by rw [hn]; exact Ideal.zero_mem _⟩)
    (Ideal.FG.map (IsNoetherian.noetherian q.asIdeal) φ)
  have hker : ∀ a ∈ stalkMaximalIdeal P ^ e, φ' a = 0 := by
    intro a ha
    have h1 : stalkMaximalIdeal P ^ e =
        Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk P)) (q.asIdeal ^ e) := by
      rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
    rw [h1] at ha
    have h2 := Ideal.mem_map_of_mem φ' ha
    rw [Ideal.map_map, IsLocalization.lift_comp, Ideal.map_pow] at h2
    exact Ideal.mem_bot.1 (he h2)
  let ψ : stalkQuotient P e ⟶ Γ(Z, ⊤) := CommRingCat.ofHom (Ideal.Quotient.lift _ φ' hker)
  refine ⟨e, Z.toSpecΓ ≫ Spec.map ψ, ?_⟩
  have hcomp : X.presheaf.germ U P hPU ≫ toStalkQuotient P e ≫ ψ =
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫ h1.appTop := by
    ext a
    exact hφ' a
  have hSpec : Z.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ h1.appTop) = h1 := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [infinitesimalBase, ← hU.fromSpecStalk_eq_fromSpecStalk hPU, IsAffineOpen.fromSpecStalk,
    ← hh1, ← hSpec, ← hcomp, Spec.map_comp, Spec.map_comp]
  simp only [Category.assoc]

/-- The `m`-th thickening `X_m ⟶ Y` of the fibre over a closed point is a closed immersion, the
base change of `Spec (𝒪_{X,P}/𝔪ᵐ) ⟶ X`. -/
private theorem isClosedImmersion_infinitesimalι {Y : Scheme.{u}} (f : Y ⟶ X) {P : X}
    (hP : IsClosed ({P} : Set X)) (m : ℕ) : IsClosedImmersion (infinitesimalι f P m) := by
  have := isClosedImmersion_infinitesimalBase hP m
  exact inferInstanceAs (IsClosedImmersion (pullback.fst f (infinitesimalBase P m)))

/-- The thickening `X_m` lies over `P`. -/
private theorem range_infinitesimalι_subset {Y : Scheme.{u}} (f : Y ⟶ X) (P : X) (m : ℕ) :
    Set.range (infinitesimalι f P m) ⊆ f.base ⁻¹' {P} := by
  rintro _ ⟨z, rfl⟩
  change f (infinitesimalι f P m z) ∈ ({P} : Set X)
  rw [← Scheme.Hom.comp_apply, infinitesimalι_comp, Scheme.Hom.comp_apply]
  exact range_infinitesimalBase_subset P m ⟨_, rfl⟩

/-- **A closed subscheme lying over a closed point lies in a thickening of the fibre.** If
`t : T ⟶ Y` is a closed immersion from a quasi-compact scheme with `f ∘ t` constant `P`, then
`t` factors through a closed immersion `T ⟶ X_m` for some `m`. -/
private theorem exists_isClosedImmersion_comp_infinitesimalι_eq [IsLocallyNoetherian X]
    {Y : Scheme.{u}} (f : Y ⟶ X) {P : X} (hP : IsClosed ({P} : Set X)) {T : Scheme.{u}}
    [CompactSpace T] (t : T ⟶ Y) [IsClosedImmersion t] (ht : ∀ z, f (t z) = P) :
    ∃ (m : ℕ) (t' : T ⟶ infinitesimalNeighbourhood f P m),
      IsClosedImmersion t' ∧ t' ≫ infinitesimalι f P m = t := by
  obtain ⟨m, L, hL⟩ := exists_comp_infinitesimalBase_eq (t ≫ f) ht
  have hfac : pullback.lift t L hL.symm ≫ infinitesimalι f P m = t := pullback.lift_fst _ _ _
  refine ⟨m, pullback.lift t L hL.symm, ?_, hfac⟩
  have := isClosedImmersion_infinitesimalι f hP m
  have : IsClosedImmersion (pullback.lift t L hL.symm ≫ infinitesimalι f P m) := by
    rw [hfac]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (infinitesimalι f P m)

end Thickening

/-! ### Cycles of exceptional curves -/

section Cycles

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-! ### The ideal of a cycle given by a multiset of prime divisors -/

/-- The ideal sheaf `∏_{E ∈ m} I_E` of the cycle `∑_{E ∈ m} E`. -/
private def cycleIdeal (m : Multiset (MMP.Mori.PrimeDivisor Y)) : Y.IdealSheafData :=
  (m.map fun E => E.idealSheaf).prod

/-- The divisor `∑_{E ∈ m} E`. -/
private def cycleDivisor (m : Multiset (MMP.Mori.PrimeDivisor Y)) : Divisor Y :=
  (m.map fun E => Finsupp.single E (1 : ℤ)).sum

private theorem cycleIdeal_zero : cycleIdeal (0 : Multiset (MMP.Mori.PrimeDivisor Y)) = ⊤ := by
  simp [cycleIdeal, Scheme.IdealSheafData.one_eq_top]

private theorem cycleIdeal_cons (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleIdeal (E ::ₘ m) = E.idealSheaf * cycleIdeal m := by
  simp [cycleIdeal]

private theorem cycleDivisor_cons (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleDivisor (E ::ₘ m) = Finsupp.single E 1 + cycleDivisor m := by
  simp [cycleDivisor]

private theorem cycleIdeal_cons' (E : MMP.Mori.PrimeDivisor Y)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cycleIdeal (E ::ₘ m) = cycleIdeal m * E.idealSheaf := by
  rw [cycleIdeal_cons, mul_comm]

private theorem cycleDivisor_apply (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (C : MMP.Mori.PrimeDivisor Y) [DecidableEq (MMP.Mori.PrimeDivisor Y)] :
    cycleDivisor m C = m.count C := by
  induction m using Multiset.induction_on with
  | empty => simp [cycleDivisor]
  | cons E m ih =>
    rw [cycleDivisor_cons, Finsupp.add_apply, ih, Finsupp.single_apply, Multiset.count_cons]
    by_cases h : E = C
    · subst h
      simp [add_comm]
    · simp [h, Ne.symm h]

private theorem mem_support_cycleIdeal (m : Multiset (MMP.Mori.PrimeDivisor Y)) (x : Y) :
    x ∈ (cycleIdeal m).support ↔ ∃ E ∈ m, x ∈ E.idealSheaf.support := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [cycleIdeal_zero, Scheme.IdealSheafData.support_top, Multiset.notMem_zero,
      false_and, exists_false, iff_false]
    exact id
  | cons E m ih =>
    rw [cycleIdeal_cons, Scheme.IdealSheafData.support_mul, ← SetLike.mem_coe,
      TopologicalSpace.Closeds.coe_sup, Set.mem_union, SetLike.mem_coe, SetLike.mem_coe, ih]
    simp

private theorem isEffectiveCartierDivisor_cycleIdeal [IsLocallyNoetherian Y] [IsNormal Y]
    {s : Y ⟶ Spec (.of k)} (hsm : IsSmoothScheme s) (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (cycleIdeal m) := by
  induction m using Multiset.induction_on with
  | empty => rw [cycleIdeal_zero]; exact Stacks.Divisors.isEffectiveCartierDivisor_top
  | cons E m ih =>
    rw [cycleIdeal_cons]
    exact isEffectiveCartierDivisor_mul _ _
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E) ih

/-! ### Dimension and properness -/

private theorem topologicalKrullDim_cycleIdeal_le (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (hm : ∀ E ∈ m, topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    topologicalKrullDim (cycleIdeal m).subscheme ≤ 1 := by
  classical
  rw [topologicalKrullDim_subscheme]
  have : ((cycleIdeal m).support : Set Y) =
      ⋃ E ∈ m.toFinset, ((E.idealSheaf.support : TopologicalSpace.Closeds Y) : Set Y) := by
    ext x
    simp only [Set.mem_iUnion, Multiset.mem_toFinset, exists_prop]
    exact mem_support_cycleIdeal m x
  rw [this]
  exact topologicalKrullDim_biUnion_le _ (fun E => E.idealSheaf.support.isClosed)
    fun E hE => by
      rw [← topologicalKrullDim_subscheme]
      exact hm E (Multiset.mem_toFinset.mp hE)

/-- **A closed subscheme of the resolution lying over `P` is proper over `k`.** Its reduction
maps to the closed point `P` and is reduced, so it factors through `Spec κ(P)`, which is finite
over `k`; the subscheme itself is universally closed because its reduction surjects onto it. -/
private theorem isProper_of_support_subset {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {f : Y ⟶ X} (hf : IsGermResolution sX P f) (J : Y.IdealSheafData)
    (hJ : (J.support : Set Y) ⊆ f.base ⁻¹' {P}) :
    IsProper (J.subschemeι ≫ f ≫ sX) := by
  have : IsProper f := hf.isSmoothResolution.isProper
  have hX := hf.isSurfaceGerm.1.1
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsClosedImmersion (X.fromSpecResidueField P) :=
    isClosed_singleton_iff_isClosedImmersion.mp hf.isSurfaceGerm.2.2.1
  set R := J.radical with hR
  have hJR : J ≤ R := J.le_radical
  have : IsReduced R.subscheme := by
    rw [hR, ← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  set h := R.subschemeι ≫ f with hh
  have H : (X.fromSpecResidueField P).ker ≤ h.ker := by
    have h1 : h.ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure
          (h.base '' (⊤ : TopologicalSpace.Closeds R.subscheme))) := by
      rw [← Scheme.IdealSheafData.map_vanishingIdeal, Scheme.IdealSheafData.vanishingIdeal_top,
        Scheme.nilradical_eq_bot, Scheme.IdealSheafData.map_bot]
    rw [h1, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨z, -, rfl⟩
    refine (X.fromSpecResidueField P).range_subset_ker_support ?_
    rw [Scheme.range_fromSpecResidueField]
    have hz : R.subschemeι z ∈ (J.support : Set Y) := by
      rw [← Scheme.IdealSheafData.support_radical, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    exact hJ hz
  let l := IsClosedImmersion.lift (X.fromSpecResidueField P) h H
  have hl : l ≫ X.fromSpecResidueField P = h := IsClosedImmersion.lift_fac _ _ H
  have : IsProper (l ≫ X.fromSpecResidueField P) := hl ▸ inferInstance
  have : IsProper l := IsProper.of_comp l (X.fromSpecResidueField P)
  have : IsFinite (X.fromSpecResidueField P ≫ sX) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hRp : IsProper (R.subschemeι ≫ f ≫ sX) := by
    rw [← Category.assoc, ← hh, ← hl, Category.assoc]
    infer_instance
  have : IsSeparated sX := hX.toIsSeparated
  have hsurj : Surjective (Scheme.IdealSheafData.inclusion hJR) := by
    refine ⟨fun z => ?_⟩
    have hz : J.subschemeι z ∈ (R.support : Set Y) := by
      rw [Scheme.IdealSheafData.support_radical, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hz
    obtain ⟨r, hr⟩ := hz
    refine ⟨r, J.subschemeι.isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hr]
  have : UniversallyClosed (Scheme.IdealSheafData.inclusion hJR ≫ J.subschemeι ≫ f ≫ sX) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  have : UniversallyClosed (J.subschemeι ≫ f ≫ sX) :=
    UniversallyClosed.of_comp_surjective (Scheme.IdealSheafData.inclusion hJR) _
  exact ⟨⟩

/-! ### Intersection numbers with the curves of a cycle -/

section Intersection

variable (s : Y ⟶ Spec (.of k)) [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

open Classical in
/-- The intersection number `(D · E)` of a `ℚ`-divisor with a prime divisor, when defined. -/
private def ixn (D : QDivisor Y) (E : MMP.Mori.PrimeDivisor Y) : ℚ :=
  if h : ∃ x, IsIntersectionNumber s D E.idealSheaf x then h.choose else 0

variable {s}

private theorem isIntersectionNumber_ixn (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (hEp : IsProper (E.idealSheaf.subschemeι ≫ s))
    (hEd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) (D : QDivisor Y) :
    IsIntersectionNumber s D E.idealSheaf (ixn s D E) := by
  have h : ∃ x, IsIntersectionNumber s D E.idealSheaf x :=
    ⟨_, hEp, hEd, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm D, rfl⟩
  rw [ixn, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

private theorem ixn_eq_of_isIntersectionNumber {D : QDivisor Y} {E : MMP.Mori.PrimeDivisor Y}
    {x : ℚ} (h : IsIntersectionNumber s D E.idealSheaf x) : ixn s D E = x := by
  have h' : ∃ x, IsIntersectionNumber s D E.idealSheaf x := ⟨x, h⟩
  rw [ixn, dite_eq_left_of_eq_true (eq_true h')]
  exact h'.choose_spec.unique h

private theorem ixn_add (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (hEp : IsProper (E.idealSheaf.subschemeι ≫ s))
    (hEd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) (D D' : QDivisor Y) :
    ixn s (D + D') E = ixn s D E + ixn s D' E :=
  ixn_eq_of_isIntersectionNumber (isIntersectionNumber_add
    (isIntersectionNumber_ixn hsm hEp hEd D) (isIntersectionNumber_ixn hsm hEp hEd D'))

/-- The intersection number of `∑_{F ∈ m} F + D` with `E` is `∑_{F ∈ m} (F · E) + (D · E)`. -/
private theorem ixn_cycleDivisor_add (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (hEp : IsProper (E.idealSheaf.subschemeι ≫ s))
    (hEd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (D : QDivisor Y) :
    ixn s (Divisor.toQDivisor (cycleDivisor m) + D) E =
      (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum + ixn s D E := by
  induction m using Multiset.induction_on with
  | empty => simp [cycleDivisor]
  | cons F m ih =>
    rw [cycleDivisor_cons, map_add, add_assoc, ixn_add hsm hEp hEd, ih, Multiset.map_cons,
      Multiset.sum_cons, add_assoc]

/-- The reduced subscheme on the support of the divisor `E` of a prime divisor is `E`. -/
private theorem suppIdeal_single_one (E : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = E.idealSheaf := by
  rw [← vanishingIdeal_closure_genericPoint_eq_idealSheaf E, DivisorWithCoeffs.suppIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure E, DivisorWithCoeffs.coe_supp]
  rw [Finsupp.support_single _ one_ne_zero]
  simp

/-- **Adjunction on an integral curve of a smooth surface**: `((K + E) · E) = -2 χ(E, 𝒪_E)`. -/
private theorem ixn_canonical_add_single [IsAlgClosed k] (hY : MMP.Mori.IsVariety k s)
    (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2) {K : Divisor Y}
    (hK : K.IsCanonicalDivisor s 2) (E : MMP.Mori.PrimeDivisor Y)
    [hE : IsProper (E.idealSheaf.subschemeι ≫ s)] :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ s)
    ixn s (Divisor.toQDivisor (K + Finsupp.single E 1)) E =
      -2 * eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
        (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) := by
  have hI := suppIdeal_single_one E
  have hC : ∀ F ∈ (Finsupp.single E (1 : ℤ) : Divisor Y).support,
      (Finsupp.single E (1 : ℤ) : Divisor Y) F = 1 := by
    intro F hF
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hF
    rw [hF, Finsupp.single_eq_same]
  have hpr' : IsProper ((DivisorWithCoeffs.suppIdeal
      (Finsupp.single E (1 : ℤ) : Divisor Y)).subschemeι ≫ s) := by
    rwa [hI]
  have h := MMP.Threefold.isIntersectionNumber_canonical_add_eq_neg_two_mul_eulerCharacteristic
    hY hsm hd hK _ hC hpr'
  revert h hpr'
  generalize DivisorWithCoeffs.suppIdeal (Finsupp.single E (1 : ℤ) : Divisor Y) = I at hI ⊢
  subst hI
  intro _ h
  exact ixn_eq_of_isIntersectionNumber h

end Intersection

/-! ### Short exact sequences supported on a proper closed subscheme -/

section Sequence

variable {s : Y ⟶ Spec (.of k)}

private theorem isProper_of_le {J I : Y.IdealSheafData} (h : J ≤ I)
    [IsProper (J.subschemeι ≫ s)] : IsProper (I.subschemeι ≫ s) := by
  rw [← Scheme.IdealSheafData.inclusion_subschemeι h, Category.assoc]
  infer_instance

private theorem eulerCharacteristic_congr_hom {X : Scheme.{u}} {g g' : X ⟶ Spec (.of k)}
    (h : g = g') (hg : IsProper g) (hg' : IsProper g') (F : X.Modules) (hF : F.IsCoherent) :
    @eulerCharacteristic k _ _ g hg F hF = @eulerCharacteristic k _ _ g' hg' F hF := by
  subst h; rfl

/-- **A short exact sequence of `𝒪_Y`-modules pushed forward from closed subschemes of `J`
descends to `J`**: the direct image along the closed immersion `J ⟶ Y` is fully faithful and
exact. -/
private theorem exists_shortExact_inclusion (J : Y.IdealSheafData) {J₁ J₂ J₃ : Y.IdealSheafData}
    (h₁ : J ≤ J₁) (h₂ : J ≤ J₂) (h₃ : J ≤ J₃)
    {G₁ : J₁.subscheme.Modules} {G₂ : J₂.subscheme.Modules} {G₃ : J₃.subscheme.Modules}
    {T : ShortComplex Y.Modules} (hT : T.ShortExact)
    (e₁ : T.X₁ ≅ (Scheme.Modules.pushforward J₁.subschemeι).obj G₁)
    (e₂ : T.X₂ ≅ (Scheme.Modules.pushforward J₂.subschemeι).obj G₂)
    (e₃ : T.X₃ ≅ (Scheme.Modules.pushforward J₃.subschemeι).obj G₃) :
    ∃ (v : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₁)).obj G₁ ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₂)).obj G₂)
      (w : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₂)).obj G₂ ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h₃)).obj G₃)
      (hvw : v ≫ w = 0), (ShortComplex.mk v w hvw).ShortExact := by
  have iso : ∀ {I : Y.IdealSheafData} (h : J ≤ I) (G : I.subscheme.Modules),
      (Scheme.Modules.pushforward J.subschemeι).obj
          ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G) ≅
        (Scheme.Modules.pushforward I.subschemeι).obj G := fun h G =>
    (Scheme.Modules.pushforwardComp (Scheme.IdealSheafData.inclusion h) J.subschemeι).app G ≪≫
      (Scheme.Modules.pushforwardCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).app G
  have u₁ := e₁ ≪≫ (iso h₁ G₁).symm
  have u₂ := e₂ ≪≫ (iso h₂ G₂).symm
  have u₃ := e₃ ≪≫ (iso h₃ G₃).symm
  have hff := Stacks.ClosedImmersion.fullyFaithfulPushforward J.subschemeι
  have : (Scheme.Modules.pushforward J.subschemeι).Faithful := hff.faithful
  set v := hff.preimage (u₁.inv ≫ T.f ≫ u₂.hom)
  set w := hff.preimage (u₂.inv ≫ T.g ≫ u₃.hom)
  have hmapv : (Scheme.Modules.pushforward J.subschemeι).map v = u₁.inv ≫ T.f ≫ u₂.hom :=
    hff.map_preimage _
  have hmapw : (Scheme.Modules.pushforward J.subschemeι).map w = u₂.inv ≫ T.g ≫ u₃.hom :=
    hff.map_preimage _
  have hvw : v ≫ w = 0 := by
    apply hff.map_injective
    rw [Functor.map_comp, Functor.map_zero, hmapv, hmapw]
    simp
  refine ⟨v, w, hvw, ?_⟩
  refine ShortComplex.shortExact_of_shortExact_map (Scheme.Modules.pushforward J.subschemeι) ?_
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk u₁ u₂ u₃ ?_ ?_) hT
  · change u₁.hom ≫ (Scheme.Modules.pushforward J.subschemeι).map v = T.f ≫ u₂.hom
    rw [hmapv]
    simp
  · change u₂.hom ≫ (Scheme.Modules.pushforward J.subschemeι).map w = T.g ≫ u₃.hom
    rw [hmapw]
    simp

/-- The Euler characteristic on `J` of a module pushed forward from a closed subscheme `I ⊆ J`
is its Euler characteristic on `I`. -/
private theorem eulerCharacteristic_pushforward_inclusion {J I : Y.IdealSheafData} (h : J ≤ I)
    [hJ : IsProper (J.subschemeι ≫ s)] (G : I.subscheme.Modules) [hG : G.IsCoherent]
    (hc : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G).IsCoherent)
    (hI : IsProper (I.subschemeι ≫ s)) :
    @eulerCharacteristic k _ _ (J.subschemeι ≫ s) hJ _ hc =
      @eulerCharacteristic k _ _ (I.subschemeι ≫ s) hI G hG := by
  have : IsProper (Scheme.IdealSheafData.inclusion h ≫ J.subschemeι ≫ s) := by
    rwa [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  rw [eulerCharacteristic_pushforward_of_isClosedImmersion k _ _ G hG hc]
  exact eulerCharacteristic_congr_hom
    (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ G hG

/-- The Euler characteristic on `J` of `L|_J ⊗ G` for a module `G` pushed forward from a closed
subscheme `I ⊆ J` is the Euler characteristic of `G ⊗ L|_I` on `I` (the projection formula). -/
private theorem eulerCharacteristic_tensor_pushforward_inclusion {J I : Y.IdealSheafData}
    (h : J ≤ I) [hJ : IsProper (J.subschemeι ≫ s)] (G : I.subscheme.Modules) [hG : G.IsCoherent]
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hc₁ : (tens J.subscheme ((Scheme.Modules.pullback J.subschemeι).obj L)
      ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion h)).obj G)).IsCoherent)
    (hI : IsProper (I.subschemeι ≫ s))
    (hc₂ : (tens I.subscheme G ((Scheme.Modules.pullback I.subschemeι).obj L)).IsCoherent) :
    @eulerCharacteristic k _ _ (J.subschemeι ≫ s) hJ _ hc₁ =
      @eulerCharacteristic k _ _ (I.subschemeι ≫ s) hI _ hc₂ := by
  set i := Scheme.IdealSheafData.inclusion h
  have : IsLocallyNoetherian J.subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      (J.subschemeι ≫ s)
  have hiJ : IsProper (i ≫ J.subschemeι ≫ s) := by
    rwa [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  have : SheafOfModules.IsInvertible J.subscheme.presheaf J.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback J.subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj J.subschemeι L
  have hV : ((Scheme.Modules.pullback J.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (J.subschemeι ≫ s) _ 1
  have : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback J.subschemeι).obj L)) :=
    MMP.Mori.isInvertible_pullback_obj i _
  have hV' : ((Scheme.Modules.pullback i).obj
      ((Scheme.Modules.pullback J.subschemeι).obj L)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (i ≫ J.subschemeι ≫ s) _ 1
  have hpush : ((Scheme.Modules.pushforward i).obj G).IsCoherent := inferInstance
  have : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj I.subschemeι L
  have hL' : ((Scheme.Modules.pullback I.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s) _ 1
  have e : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback J.subschemeι).obj L) ≅
      (Scheme.Modules.pullback I.subschemeι).obj L :=
    (Scheme.Modules.pullbackComp i J.subschemeι).app L ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.IdealSheafData.inclusion_subschemeι h)).app L
  have h1 := eulerCharacteristic_tensorSheaf_comm k (J.subschemeι ≫ s)
    ((Scheme.Modules.pullback J.subschemeι).obj L) ((Scheme.Modules.pushforward i).obj G)
    (hF := hV) (hG := hpush)
  have h2 := eulerCharacteristic_tensorSheaf_pushforward_of_isClosedImmersion k i
    (J.subschemeι ≫ s) G ((Scheme.Modules.pullback J.subschemeι).obj L) hG hV hpush hV'
  have h3 := @eulerCharacteristic_eq_of_iso k _ _ (i ≫ J.subschemeι ≫ s) hiJ _ _
    (@SheafOfModules.tensorSheaf_isCoherent I.subscheme.toRingedSpace G _ hG hV')
    (@SheafOfModules.tensorSheaf_isCoherent I.subscheme.toRingedSpace G _ hG hL')
    (((Stacks.SheafOfModules.Tensor.sheafTensor _).obj G).mapIso e)
  refine h1.trans (h2.trans (h3.trans ?_))
  exact eulerCharacteristic_congr_hom
    (by rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]) _ _ _ _

/-- The restriction `𝒪_Y(-W)|_I` of the ideal sheaf of an effective Cartier divisor to a closed
subscheme is invertible. -/
private theorem isInvertible_pullback_negativeTwist (W I : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor W] :
    SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) :=
  Stacks.Models.isInvertible_restrict I _ (Stacks.Divisors.isTensorInvertible_negativeTwist W)

/-- The short exact sequence `0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0` of [Stacks, Tag 0C4T],
descended to the closed subscheme `W + I`. -/
private theorem exists_shortExact_mul (W I : Y.IdealSheafData)
    [hW : Stacks.Divisors.IsEffectiveCartierDivisor W]
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] :
    ∃ (v : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
          (Scheme.IdealSheafData.mul_le_right W I))).obj
          ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion (le_refl (W * I)))).obj
          (SheafOfModules.unit (W * I).subscheme.ringCatSheaf))
      (w : (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion (le_refl (W * I)))).obj
          (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) ⟶
        (Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
          (Scheme.IdealSheafData.mul_le_left W I))).obj
          (SheafOfModules.unit W.subscheme.ringCatSheaf))
      (hvw : v ≫ w = 0), (ShortComplex.mk v w hvw).ShortExact := by
  obtain ⟨f, zero, hex⟩ := Stacks.Divisors.addEffectiveCartierDivisor_shortExact W (W * I) I hW
    (Scheme.IdealSheafData.mul_le_left W I) rfl
  exact exists_shortExact_inclusion (W * I) _ _ _ hex (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- **`χ(𝒪_{W+I}) = χ(𝒪_W) + χ(𝒪_Y(-W)|_I)`** for effective Cartier divisors `W`, `I` whose
sum is proper over `k`: additivity of the Euler characteristic on `W + I` along the sequence
`0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0`. -/
private theorem eulerCharacteristic_unit_mul (W I : Y.IdealSheafData)
    [hW : Stacks.Divisors.IsEffectiveCartierDivisor W]
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    [hWI : IsProper ((W * I).subschemeι ≫ s)] :
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
    haveI := isInvertible_pullback_negativeTwist W I
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s)
      ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((W * I).subschemeι ≫ s)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
    eulerCharacteristic k ((W * I).subschemeι ≫ s)
        (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) =
      eulerCharacteristic k (W.subschemeι ≫ s) (SheafOfModules.unit W.subscheme.ringCatSheaf) +
        eulerCharacteristic k (I.subschemeι ≫ s)
          ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) := by
  have := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
  have := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
  have := isInvertible_pullback_negativeTwist W I
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
    (I.subschemeι ≫ s)
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W)) 1
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k ((W * I).subschemeι ≫ s)
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
  have : IsLocallyNoetherian (W * I).subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      ((W * I).subschemeι ≫ s)
  obtain ⟨v, w, hvw, hS⟩ := exists_shortExact_mul W I
  have key := eulerCharacteristic_add_of_shortExact k ((W * I).subschemeι ≫ s) hS
  have e₁ := eulerCharacteristic_pushforward_inclusion (s := s)
    (Scheme.IdealSheafData.mul_le_right W I)
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W))
    inferInstance inferInstance
  have e₂ := eulerCharacteristic_pushforward_inclusion (s := s) (le_refl (W * I))
    (SheafOfModules.unit (W * I).subscheme.ringCatSheaf) inferInstance inferInstance
  have e₃ := eulerCharacteristic_pushforward_inclusion (s := s)
    (Scheme.IdealSheafData.mul_le_left W I) (SheafOfModules.unit W.subscheme.ringCatSheaf)
    inferInstance inferInstance
  refine e₂.symm.trans (key.trans ?_)
  rw [add_comm]
  exact congrArg₂ (· + ·) e₃ e₁

/-- **The degree on `W + I` is the sum of the degrees on `W` and on `I`**, for effective Cartier
divisors `W`, `I` whose sum is a proper curve over `k`: the sequence
`0 ⟶ 𝒪_Y(-W)|_I ⟶ 𝒪_{W+I} ⟶ 𝒪_W ⟶ 0` twisted by an invertible sheaf `L`, against the untwisted
one, with the additivity of the degree on `I`. -/
private theorem degreeOn_mul (W I : Y.IdealSheafData)
    [hW : Stacks.Divisors.IsEffectiveCartierDivisor W]
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I]
    [hWI : IsProper ((W * I).subschemeι ≫ s)] (hd : topologicalKrullDim (W * I).subscheme ≤ 1)
    (hdW : topologicalKrullDim W.subscheme ≤ 1) (hdI : topologicalKrullDim I.subscheme ≤ 1)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
    MMP.Mori.degreeOn k s (W * I).subschemeι hd L =
      MMP.Mori.degreeOn k s W.subschemeι hdW L + MMP.Mori.degreeOn k s I.subschemeι hdI L := by
  have := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left W I)
  have := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_right W I)
  have := isInvertible_pullback_negativeTwist W I
  have : IsLocallyNoetherian (W * I).subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k
      ((W * I).subschemeι ≫ s)
  have : SheafOfModules.IsInvertible (W * I).subscheme.presheaf
      (W * I).subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback (W * I).subschemeι).obj L) :=
    MMP.Mori.isInvertible_pullback_obj _ L
  have : SheafOfModules.IsInvertible W.subscheme.presheaf W.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback W.subschemeι).obj L) := MMP.Mori.isInvertible_pullback_obj _ L
  have : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback I.subschemeι).obj L) := MMP.Mori.isInvertible_pullback_obj _ L
  have hN : ((Scheme.Modules.pullback I.subschemeι).obj
      (Stacks.Divisors.negativeTwist W)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s) _ 1
  have hLJ : ((Scheme.Modules.pullback (W * I).subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      ((W * I).subschemeι ≫ s) _ 1
  have hLW : ((Scheme.Modules.pullback W.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (W.subschemeι ≫ s) _ 1
  have hLI : ((Scheme.Modules.pullback I.subschemeι).obj L).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (I.subschemeι ≫ s) _ 1
  have hOJ := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    ((W * I).subschemeι ≫ s)
  have hOW := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (W.subschemeι ≫ s)
  have hOI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (I.subschemeι ≫ s)
  have : SheafOfModules.IsInvertible I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      (tens I.subscheme ((Scheme.Modules.pullback I.subschemeι).obj
        (Stacks.Divisors.negativeTwist W)) ((Scheme.Modules.pullback I.subschemeι).obj L)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible I.subscheme.presheaf
      I.subscheme.ringCatSheaf.2 _ _
  have hNL := @SheafOfModules.tensorSheaf_isCoherent I.subscheme.toRingedSpace _ _ hN hLI
  obtain ⟨v, w, hvw, hS⟩ := exists_shortExact_mul W I
  have hp₁ : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (Scheme.IdealSheafData.mul_le_right W I))).obj ((Scheme.Modules.pullback I.subschemeι).obj
        (Stacks.Divisors.negativeTwist W))).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hN
  have hp₂ : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (le_refl (W * I)))).obj (SheafOfModules.unit (W * I).subscheme.ringCatSheaf)).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hOJ
  have hp₃ : ((Scheme.Modules.pushforward (Scheme.IdealSheafData.inclusion
      (Scheme.IdealSheafData.mul_le_left W I))).obj
        (SheafOfModules.unit W.subscheme.ringCatSheaf)).IsCoherent :=
    @isCoherent_pushforward_of_isClosedImmersion _ _ _ _ _ _ hOW
  have key := eulerCharacteristic_tensorSheaf_add_of_shortExact_of_isProper k
    ((W * I).subschemeι ≫ s) ((Scheme.Modules.pullback (W * I).subschemeι).obj L) 1 _ hS
    hp₁ hp₂ hp₃
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₁)
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₂)
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₃)
  have t₁ := @eulerCharacteristic_tensor_pushforward_inclusion k _ Y s (W * I) I
    (Scheme.IdealSheafData.mul_le_right W I) _ _ hN L _
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₁) inferInstance hNL
  have t₂ := @eulerCharacteristic_tensor_pushforward_inclusion k _ Y s (W * I) (W * I)
    (le_refl (W * I)) _ _ hOJ L _
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₂) inferInstance
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hOJ hLJ)
  have t₃ := @eulerCharacteristic_tensor_pushforward_inclusion k _ Y s (W * I) W
    (Scheme.IdealSheafData.mul_le_left W I) _ _ hOW L _
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hLJ hp₃) inferInstance
    (@SheafOfModules.tensorSheaf_isCoherent _ _ _ hOW hLW)
  have u₂ := eulerCharacteristic_unit_tensorSheaf k ((W * I).subschemeι ≫ s) _ hLJ hOJ
  have u₃ := eulerCharacteristic_unit_tensorSheaf k (W.subschemeι ≫ s) _ hLW hOW
  have hA := u₂.symm.trans (t₂.symm.trans (key.trans (congrArg₂ (· + ·) t₁ (t₃.trans u₃))))
  have hB := eulerCharacteristic_unit_mul (s := s) W I
  have hC := invertibleCurveDegree_tensorSheaf_eq_add k (I.subschemeι ≫ s) hdI
    ((Scheme.Modules.pullback I.subschemeι).obj (Stacks.Divisors.negativeTwist W))
    ((Scheme.Modules.pullback I.subschemeι).obj L)
  have c₁ := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
    _ hNL hOI
  have c₂ := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
    _ hN hOI
  have c₃ := @invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
    _ hLI hOI
  have g₁ := (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s (W * I).subschemeι hd L).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ ((W * I).subschemeι ≫ s) _ hd _
      _ hLJ hOJ)
  have g₂ := (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s W.subschemeι hdW L).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (W.subschemeι ≫ s) _ hdW _
      _ hLW hOW)
  have g₃ := (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s I.subschemeι hdI L).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (I.subschemeι ≫ s) _ hdI _
      _ hLI hOI)
  rw [g₁, g₂, g₃]
  rw [c₁, c₂, c₃] at hC
  linarith

end Sequence

/-! ### Intersection numbers as degrees -/

section Curves

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- For a divisor `D` on a smooth `Y` and a closed subscheme `J` which is a proper curve,
`(D · J) = deg_J 𝒪_Y(D)`. -/
private theorem isIntersectionNumber_degreeOn (hsm : IsSmoothScheme s) {J : Y.IdealSheafData}
    [hp : IsProper (J.subschemeι ≫ s)] (hd : topologicalKrullDim J.subscheme ≤ 1)
    (D : Divisor Y) :
    IsIntersectionNumber s (Divisor.toQDivisor D) J
      (D.degreeOn k s J.subschemeι hd (MMP.Fourfold.isCartier_of_isSmoothScheme hsm D)) :=
  ⟨hp, hd, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _,
    QDivisor.intersectionNumber_toQDivisor k s _ hd D _ _⟩

end Curves

/-! ### Intersection numbers with a cycle -/

section CycleFormula

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Intersection numbers are additive in the cycle.** For a nonzero cycle `Z = ∑_{E ∈ m} E` of
proper curves on a smooth `Y` whose subcycles are proper over `k`,
`(D · Z) = ∑_{E ∈ m} (D · E)`: the degree on `W + E` is the sum of the degrees on `W` and `E`. -/
private theorem isIntersectionNumber_cycleIdeal (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (hm0 : m ≠ 0)
    (hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ s) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1)
    (hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ s)) (D : Divisor Y) :
    IsIntersectionNumber s (Divisor.toQDivisor D) (cycleIdeal m)
      (m.map fun F => ixn s (Divisor.toQDivisor D) F).sum := by
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm0
  | cons E m ih =>
    obtain ⟨hEp, hEd⟩ := hmE E (Multiset.mem_cons_self E m)
    have := hEp
    by_cases hm : m = 0
    · subst hm
      have hI : cycleIdeal (E ::ₘ 0) = E.idealSheaf := by
        rw [cycleIdeal_cons', cycleIdeal_zero, ← Scheme.IdealSheafData.one_eq_top, one_mul]
      rw [hI]
      simpa using isIntersectionNumber_ixn hsm hEp hEd (Divisor.toQDivisor D)
    · have hle : m ≤ E ::ₘ m := Multiset.le_cons_self m E
      have hmE' : ∀ F ∈ m, IsProper (F.idealSheaf.subschemeι ≫ s) ∧
          topologicalKrullDim F.idealSheaf.subscheme ≤ 1 :=
        fun F hF => hmE F (Multiset.mem_cons_of_mem hF)
      have ihc := ih hm hmE' fun m' hm' => hprop m' (hm'.trans hle)
      have hW := isEffectiveCartierDivisor_cycleIdeal hsm m
      have hIE :=
        MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E
      have hpJ : IsProper ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s) := by
        rw [← cycleIdeal_cons']; exact hprop _ le_rfl
      have hpW : IsProper ((cycleIdeal m).subschemeι ≫ s) := hprop m hle
      have hdW : topologicalKrullDim (cycleIdeal m).subscheme ≤ 1 :=
        topologicalKrullDim_cycleIdeal_le m fun F hF => (hmE' F hF).2
      have hdJ : topologicalKrullDim (cycleIdeal m * E.idealSheaf).subscheme ≤ 1 := by
        rw [← cycleIdeal_cons']
        exact topologicalKrullDim_cycleIdeal_le _ fun F hF => (hmE F hF).2
      rw [cycleIdeal_cons']
      have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
      have hcD := MMP.Fourfold.isCartier_of_isSmoothScheme hsm D
      have := hcD.isInvertibleModule_divisorialSheaf
      have h1 := isIntersectionNumber_degreeOn hsm hdJ D
      have h2 : D.degreeOn k s (cycleIdeal m * E.idealSheaf).subschemeι hdJ hcD =
          D.degreeOn k s (cycleIdeal m).subschemeι hdW hcD +
            D.degreeOn k s E.idealSheaf.subschemeι hEd hcD :=
        degreeOn_mul (s := s) (cycleIdeal m) E.idealSheaf hdJ hdW hEd D.divisorialSheaf
      have eW := ihc.unique (isIntersectionNumber_degreeOn hsm hdW D)
      have eE := ixn_eq_of_isIntersectionNumber (isIntersectionNumber_degreeOn hsm hEd D)
      convert h1 using 1
      rw [Multiset.map_cons, Multiset.sum_cons, eW, eE, h2]
      push_cast
      ring

end CycleFormula

/-! ### Cycles with given coefficients -/

/-- The ideal `∏ I_C^{n_C}` of the divisor `∑_{F ∈ m} F` is `∏_{F ∈ m} I_F`. -/
private theorem divisorIdeal_cycleDivisor (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    MMP.Resolution.divisorIdeal (fun C => (cycleDivisor m C).toNat) = cycleIdeal m := by
  classical
  rw [cycleIdeal, Finset.prod_multiset_map_count, MMP.Resolution.divisorIdeal]
  refine (finprod_eq_prod_of_mulSupport_subset _ fun C hC => ?_).trans
    (Finset.prod_congr rfl fun C _ => by rw [cycleDivisor_apply, Int.toNat_natCast])
  rw [Finset.mem_coe, Multiset.mem_toFinset, ← Multiset.count_pos]
  by_contra h0
  exact hC (by simp only [cycleDivisor_apply, Int.toNat_natCast, Nat.eq_zero_of_not_pos h0,
    pow_zero])

/-- The multiset `∑_j z_j [E_j]` of a coefficient vector `z`. -/
private def zMultiset {n : ℕ} (E : Fin n → MMP.Mori.PrimeDivisor Y)
    (z : Fin n → ℕ) : Multiset (MMP.Mori.PrimeDivisor Y) :=
  ∑ j, Multiset.replicate (z j) (E j)

private theorem sum_map_zMultiset {M : Type*} [AddCommMonoid M] {n : ℕ}
    (E : Fin n → MMP.Mori.PrimeDivisor Y) (z : Fin n → ℕ) (g : MMP.Mori.PrimeDivisor Y → M) :
    ((zMultiset E z).map g).sum = ∑ j, z j • g (E j) := by
  rw [zMultiset, ← Multiset.coe_mapAddMonoidHom, map_sum, ← Multiset.coe_sumAddMonoidHom,
    map_sum]
  simp [Multiset.map_replicate, Multiset.sum_replicate]

private theorem count_zMultiset [DecidableEq (MMP.Mori.PrimeDivisor Y)] {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} (hE : Function.Injective E) (z : Fin n → ℕ)
    (j : Fin n) : (zMultiset E z).count (E j) = z j := by
  rw [zMultiset, Multiset.count_sum']
  simp [Multiset.count_replicate, hE.eq_iff]

private theorem exists_eq_of_mem_zMultiset {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y}
    {z : Fin n → ℕ} {C : MMP.Mori.PrimeDivisor Y} (hC : C ∈ zMultiset E z) :
    ∃ j, E j = C := by
  rw [zMultiset, Multiset.mem_sum] at hC
  obtain ⟨j, -, hj⟩ := hC
  exact ⟨j, (Multiset.eq_of_mem_replicate hj).symm⟩

private theorem mem_zMultiset {n : ℕ} (E : Fin n → MMP.Mori.PrimeDivisor Y) {z : Fin n → ℕ}
    {j : Fin n} (hj : z j ≠ 0) : E j ∈ zMultiset E z := by
  rw [zMultiset, Multiset.mem_sum]
  exact ⟨j, Finset.mem_univ j, Multiset.mem_replicate.2 ⟨hj, rfl⟩⟩

private theorem cycleIdeal_zMultiset_const {n : ℕ} (E : Fin n → MMP.Mori.PrimeDivisor Y)
    (r : ℕ) : cycleIdeal (zMultiset E fun _ => r) = cycleIdeal (zMultiset E fun _ => 1) ^ r := by
  have h : (zMultiset E fun _ => r) = r • zMultiset E fun _ => 1 := by
    simp [zMultiset, Finset.smul_sum, Multiset.nsmul_singleton]
  rw [h, cycleIdeal, cycleIdeal, Multiset.map_nsmul, Multiset.prod_nsmul]

private theorem cycleDivisor_nonneg (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    0 ≤ cycleDivisor m := fun C => by
  classical
  rw [cycleDivisor_apply]
  exact Int.natCast_nonneg _

private theorem mem_of_mem_support_cycleDivisor {m : Multiset (MMP.Mori.PrimeDivisor Y)}
    {C : MMP.Mori.PrimeDivisor Y} (hC : C ∈ (cycleDivisor m).support) : C ∈ m := by
  classical
  rwa [Finsupp.mem_support_iff, cycleDivisor_apply, Nat.cast_ne_zero,
    Multiset.count_ne_zero] at hC

/-- An effective divisor `Z` is the cycle `∑_{C ∈ m} C` of the multiset `m` of its components
counted with multiplicity. -/
private theorem exists_eq_cycleDivisor (Z : Divisor Y) (hZ : 0 ≤ Z) :
    ∃ m : Multiset (MMP.Mori.PrimeDivisor Y), Z = cycleDivisor m ∧
      ∀ C, C ∈ m ↔ C ∈ Z.support := by
  classical
  refine ⟨Finsupp.toMultiset (Finsupp.mapRange Int.toNat Int.toNat_zero Z), ?_, fun C => ?_⟩
  · refine Finsupp.ext fun C => ?_
    rw [cycleDivisor_apply, Finsupp.count_toMultiset, Finsupp.mapRange_apply,
      Int.toNat_of_nonneg (hZ C)]
  · rw [Finsupp.mem_toMultiset, Finsupp.mem_support_iff, Finsupp.mapRange_apply,
      Finsupp.mem_support_iff, ne_eq, ne_eq, Int.toNat_eq_zero]
    exact ⟨fun h h0 => h h0.le, fun h h0 => h (le_antisymm h0 (hZ C))⟩

private theorem cycleDivisor_zMultiset_ne_zero {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y}
    (hE : Function.Injective E) {z : Fin n → ℕ} (hz : z ≠ 0) :
    cycleDivisor (zMultiset E z) ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
  intro h0
  have := cycleDivisor_apply (zMultiset E z) (E j)
  rw [h0, count_zMultiset hE] at this
  exact hj (by simpa using this.symm)

end Cycles

/-! ### `h⁰` and `h¹` on proper schemes of dimension at most one -/

section Cohomology

variable {k : Type u} [Field k]

/-- On a proper scheme of dimension at most one over `k`, `χ(ℱ) = h⁰(ℱ) - h¹(ℱ)`. -/
private theorem eulerCharacteristic_eq_finrank_sub {C : Scheme.{u}} (g : C ⟶ Spec (.of k))
    [IsProper g] (hdim : topologicalKrullDim C ≤ 1) (F : C.Modules) [F.IsCoherent] :
    eulerCharacteristic k g F = (Module.finrank k (cohomologyOverField k g F 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k g F 1) : ℤ) := by
  rw [eulerCharacteristic_eq_finsum]
  have hz : ∀ n : ℕ, 2 ≤ n → Module.finrank k (cohomologyOverField k g F n) = 0 := fun n hn =>
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_of_topologicalKrullDim_le k g F (d := 1) (i := n) hdim hn)
    Module.finrank_zero_of_subsingleton
  rw [finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m * (Module.finrank k (cohomologyOverField k g F m) : ℤ))
    (s := Finset.range 2) fun m hm => ?_]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- **A nonempty proper scheme over `k` has `h⁰(𝒪) ≥ 1`**: its ring of global functions is a
nonzero finite-dimensional `k`-vector space, containing the constant `1`. -/
private theorem one_le_finrank_cohomologyOverField_zero_unit {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [Nonempty C] :
    1 ≤ Module.finrank k (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 0) := by
  let : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  rw [finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
  have : Nontrivial Γ(C, ⊤) :=
    Stacks.EmptyLimitCounterexample.nontrivial_Γ_of_nonempty C (Classical.arbitrary C)
  have : Module.Finite k Γ(C, ⊤) := by
    have := forall_finiteDimensional_cohomologyOverField_unit k g 0
    exact Module.Finite.equiv (cohomologyOverFieldZeroIsoSections k g
      (SheafOfModules.unit C.ringCatSheaf)).toLinearEquiv
  exact Module.finrank_pos

end Cohomology

/-! ### Artin's criterion -/

section Main

open Stacks.FormalFunctions

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {P : X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The closed subscheme `∏ I_C^{Z_C}` cut out by an effective divisor `Z`. -/
private abbrev cyc (Z : Divisor Y) : Y.IdealSheafData :=
  MMP.Resolution.divisorIdeal fun C => (Z C).toNat

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem cyc_cycleDivisor (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    cyc (cycleDivisor m) = cycleIdeal m :=
  divisorIdeal_cycleDivisor m

omit [IsAlgClosed k] [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **An exceptional cycle lies over `P`, has dimension at most one and is nonempty.** -/
private theorem cyc_support_subset_and {Z : Divisor Y} (hZ : 0 ≤ Z) (hZ0 : Z ≠ 0)
    (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C) :
    ((cyc Z).support : Set Y) ⊆ f.base ⁻¹' {P} ∧
      topologicalKrullDim (cyc Z).subscheme ≤ 1 ∧ Nonempty (cyc Z).subscheme := by
  obtain ⟨m, hZm, hm⟩ := exists_eq_cycleDivisor Z hZ
  have hcyc : cyc Z = cycleIdeal m := hZm ▸ cyc_cycleDivisor m
  have hsub : ((cyc Z).support : Set Y) ⊆ f.base ⁻¹' {P} := by
    intro x hx
    rw [hcyc, SetLike.mem_coe, mem_support_cycleIdeal] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    exact (hZE C ((hm C).1 hC)).1.prop.2 hxC
  refine ⟨hsub, ?_, ?_⟩
  · rw [hcyc]
    exact topologicalKrullDim_cycleIdeal_le m fun C hC =>
      (hZE C ((hm C).1 hC)).2.2.le
  · obtain ⟨C, hC⟩ := Finset.nonempty_of_ne_empty fun h => hZ0 (Finsupp.support_eq_empty.1 h)
    have : IsIntegral C.idealSheaf.subscheme := (hZE C hC).2.1
    obtain ⟨w⟩ := (inferInstance : Nonempty C.idealSheaf.subscheme)
    have hx : C.idealSheaf.subschemeι w ∈ ((cyc Z).support : Set Y) := by
      rw [hcyc, SetLike.mem_coe, mem_support_cycleIdeal]
      refine ⟨C, (hm C).2 hC, ?_⟩
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    rw [← Scheme.IdealSheafData.range_subschemeι] at hx
    obtain ⟨v, -⟩ := hx
    exact ⟨v⟩

omit [IsAlgClosed k] [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A cycle of exceptional curves is proper over `k`. -/
private theorem isProper_cycleIdeal (hf : IsGermResolution sX P f)
    {m : Multiset (MMP.Mori.PrimeDivisor Y)} (hm : ∀ C ∈ m, IsGermExceptionalCurve f P C) :
    IsProper ((cycleIdeal m).subschemeι ≫ f ≫ sX) :=
  isProper_of_support_subset hf _ fun x hx => by
    obtain ⟨C, hC, hxC⟩ := (mem_support_cycleIdeal m x).1 hx
    exact (hm C hC).1.prop.2 hxC

omit [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem isGermExceptionalCurve_of_mem_zMultiset {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration f P E)
    {z : Fin n → ℕ} {C : MMP.Mori.PrimeDivisor Y} (hC : C ∈ zMultiset E z) :
    IsGermExceptionalCurve f P C := by
  obtain ⟨j, rfl⟩ := exists_eq_of_mem_zMultiset hC
  exact hE.isGermExceptionalCurve j

private theorem ixn_single_eq_matrix {B : QDivisor X} {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B f E Γ) (i j : Fin n) :
    ixn (f ≫ sX) (Divisor.toQDivisor (Finsupp.single (E i) 1)) (E j) = (Γ.matrix i j : ℚ) := by
  rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
  by_cases hij : i = j
  · subst hij
    rw [ixn_eq_of_isIntersectionNumber (hΓ.weight i)]
    simp [WeightedGraph.matrix]
  · rw [ixn_eq_of_isIntersectionNumber (hΓ.edgeWeight i j hij)]
    simp [WeightedGraph.matrix, hij]

private theorem ixn_cycleDivisor_zMultiset {B : QDivisor X} {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B f E Γ) (z : Fin n → ℕ) (j : Fin n) :
    ixn (f ≫ sX) (Divisor.toQDivisor (cycleDivisor (zMultiset E z))) (E j) =
      ∑ i, (z i : ℚ) * Γ.matrix i j := by
  have hf := hΓ.isGermResolution
  have hsm := hf.isSmoothResolution.isSmoothScheme
  obtain ⟨h1, hEp⟩ := (hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j).isProper sX hf
  have h := ixn_cycleDivisor_add hsm hEp h1.2.le (zMultiset E z) 0
  rw [add_zero, ixn_eq_of_isIntersectionNumber
    (isIntersectionNumber_zero (isIntersectionNumber_ixn hsm hEp h1.2.le 0)), add_zero,
    sum_map_zMultiset] at h
  rw [h]
  simp only [ixn_single_eq_matrix hΓ, nsmul_eq_mul]

private theorem ixn_canonical_eq_genus {B : QDivisor X} {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B f E Γ) {K : Divisor Y}
    (hK : K.IsCanonicalDivisor (f ≫ sX) 2) (j : Fin n) :
    ixn (f ≫ sX) (Divisor.toQDivisor K) (E j) = 2 * (Γ.genus j : ℚ) - 2 + Γ.weight j := by
  have hf := hΓ.isGermResolution
  have hsm := hf.isSmoothResolution.isSmoothScheme
  obtain ⟨h1, hEp⟩ := (hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j).isProper sX hf
  have hadj := ixn_canonical_add_single hf.isVariety hsm hf.topologicalKrullDim_eq hK (E j)
  rw [map_add, ixn_add hsm hEp h1.2.le, ixn_single_eq_matrix hΓ j j] at hadj
  obtain ⟨hp1, hc1, hg⟩ := hΓ.genus j
  rw [MMP.Mori.arithmeticGenus] at hg
  have hg' : ((Γ.genus j : ℤ) : ℚ) = 1 - (eulerCharacteristic k
      ((E j).idealSheaf.subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (E j).idealSheaf.subscheme.ringCatSheaf) : ℚ) := by
    exact_mod_cast hg
  rw [show Γ.matrix j j = -Γ.weight j by simp [WeightedGraph.matrix]] at hadj
  push_cast at hg' hadj
  linarith

/-- **The cycle formula in graph terms.** For a nonzero coefficient vector `z` and
`Z = ∑ z_j E_j`, `χ(𝒪_Z) = -½ (zᵀ M(Γ) z + ∑_j z_j (2p_j - 2 + n_j))`: this is
`χ(𝒪_Z) = -½ (Z² + K_Y · Z)` with `Z² = zᵀ M(Γ) z` by additivity of intersection numbers, and
`K_Y · E_j = 2p_j - 2 + n_j` by adjunction. -/
private theorem eulerCharacteristic_cyc_zMultiset_eq {B : QDivisor X} {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B f E Γ) (z : Fin n → ℕ) (hz : z ≠ 0)
    (hp : IsProper ((cyc (cycleDivisor (zMultiset E z))).subschemeι ≫ f ≫ sX)) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cyc (cycleDivisor (zMultiset E z))).subschemeι ≫ f ≫ sX)
    (eulerCharacteristic k ((cyc (cycleDivisor (zMultiset E z))).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (cyc (cycleDivisor (zMultiset E z))).subscheme.ringCatSheaf) : ℚ) =
      -((∑ j, ∑ l, (z j : ℚ) * Γ.matrix j l * z l) +
        ∑ j, (z j : ℚ) * (2 * Γ.genus j - 2 + Γ.weight j)) / 2 := by
  classical
  have hf := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  set m := zMultiset E z with hm
  set Z := cycleDivisor m with hZdef
  have hsm := hf.isSmoothResolution.isSmoothScheme
  have hY := hf.isVariety
  have : IsIntegral Y := hf.isIntegral sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm
    (n := 2) (by exact_mod_cast hf.topologicalKrullDim_eq)
  have hZ0 : Z ≠ 0 := cycleDivisor_zMultiset_ne_zero hE.injective hz
  have hm0 : m ≠ 0 := fun h0 => hZ0 (by simp [hZdef, h0, cycleDivisor])
  have hmE : ∀ C ∈ m, IsGermExceptionalCurve f P C := fun C hC =>
    isGermExceptionalCurve_of_mem_zMultiset hE hC
  have hmE' : ∀ C ∈ m, IsProper (C.idealSheaf.subschemeι ≫ f ≫ sX) ∧
      topologicalKrullDim C.idealSheaf.subscheme ≤ 1 := fun C hC =>
    have h := (hmE C hC).isProper sX hf
    ⟨h.2, h.1.2.le⟩
  have hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ f ≫ sX) := fun m' hm' =>
    isProper_cycleIdeal hf fun C hC => hmE C (Multiset.mem_of_le hm' hC)
  have hdiv : cyc Z = cycleIdeal m := cyc_cycleDivisor m
  obtain ⟨hp', a, b, ha, hb, hχ⟩ := hf.eulerCharacteristic_divisorIdeal_eq hK
    (cycleDivisor_nonneg m) hZ0 fun C hC => hmE C (mem_of_mem_support_cycleDivisor hC)
  have hA := isIntersectionNumber_cycleIdeal hsm m hm0 hmE' hprop Z
  have hB := isIntersectionNumber_cycleIdeal hsm m hm0 hmE' hprop K
  rw [← hdiv] at hA hB
  have ea := ha.unique hA
  have eb := hb.unique hB
  have hixnZ : ∀ j, ixn (f ≫ sX) (Divisor.toQDivisor Z) (E j) =
      ∑ i, (z i : ℚ) * Γ.matrix i j := ixn_cycleDivisor_zMultiset hΓ z
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    ((cyc Z).subschemeι ≫ f ≫ sX)
  have hχ' : (eulerCharacteristic k ((cyc Z).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) : ℚ) = -(a + b) / 2 := hχ
  rw [hχ', ea, eb, sum_map_zMultiset, sum_map_zMultiset]
  simp only [hixnZ, ixn_canonical_eq_genus hΓ hK, nsmul_eq_mul]
  congr 3
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### The fibre over `P` -/

omit [IsAlgClosed k] [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
private theorem isClosed_preimage_singleton (hf : IsGermResolution sX P f) :
    IsClosed (f.base ⁻¹' {P}) :=
  hf.isSurfaceGerm.2.2.1.preimage f.continuous

omit [IsAlgClosed k] [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] in
/-- The fibre over `P` is not all of `Y`: the generic point of `Y` maps to the generic point of
the surface `X`, which is not the closed point `P`. -/
private theorem preimage_singleton_ne_univ (hf : IsGermResolution sX P f) :
    f.base ⁻¹' {P} ≠ Set.univ := by
  intro h
  have : IsIntegral X := hf.isSurfaceGerm.1.1.toIsIntegral
  have : IsIntegral Y := hf.isIntegral sX
  have := hf.isSmoothResolution.isBirationalMorphism.isDominant
  have hη : f (genericPoint Y) = genericPoint X := map_genericPoint_of_isDominant f
  have hP : genericPoint X = P := by
    rw [← hη]
    exact (h ▸ Set.mem_univ (genericPoint Y) : genericPoint Y ∈ f.base ⁻¹' {P})
  have huniv : (Set.univ : Set X) = {P} := by
    rw [← hf.isSurfaceGerm.2.2.1.closure_eq, ← hP, (genericPoint_spec X).def]
  have : Subsingleton X := ⟨fun a b => by
    have ha : a ∈ ({P} : Set X) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({P} : Set X) := huniv ▸ Set.mem_univ b
    exact ha.trans hb.symm⟩
  have h2 := topologicalKrullDim_zero_of_discreteTopology X
  rw [hf.isSurfaceGerm.2.1] at h2
  exact absurd h2 (by decide)

omit [IsAlgClosed k] in
/-- **The fibres of a resolution of a surface germ have dimension at most one**: over a point
other than `P` the resolution is an isomorphism, and the fibre over `P` is a proper closed subset
of the irreducible surface `Y`. -/
private theorem topologicalKrullDim_preimage_le_one (hf : IsGermResolution sX P f) (x : X) :
    topologicalKrullDim (f ⁻¹' {x}) ≤ 1 := by
  by_cases hx : x = P
  · subst hx
    have : IsIntegral Y := hf.isIntegral sX
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
    have : IsNoetherian Y := {}
    exact MMP.Mori.topologicalKrullDim_le_one_of_ne_univ hf.topologicalKrullDim_eq.le
      (isClosed_preimage_singleton hf) (preimage_singleton_ne_univ hf)
  · obtain ⟨U, hU, hiso⟩ := hf.isIso_away
    have hxU : x ∈ (U : Set X) := by rwa [hU]
    have : Subsingleton (f.base ⁻¹' {x}) := ⟨fun a b => Subtype.ext
      (Stacks.Models.eq_of_isIso_morphismRestrict f U (by rw [show f a.1 = x from a.2]; exact hxU)
        ((show f a.1 = x from a.2).trans (show f b.1 = x from b.2).symm))⟩
    have : DiscreteTopology (f.base ⁻¹' {x}) := Subsingleton.discreteTopology
    exact (topologicalKrullDim_zero_of_discreteTopology (f.base ⁻¹' {x})).trans zero_le_one

omit [IsAlgClosed k] in
/-- **Every point of the fibre over `P` lies on an exceptional curve, unless the fibre is that
single point.** A non-closed point of the fibre specializing to `y` has a closure of dimension
one, so it has coheight one and is the generic point of an exceptional curve. Otherwise `y` is
closed and forms an irreducible component of the fibre by itself, hence an open and closed
point of it; the fibre is connected because `X` is normal, so it is `{y}`. -/
private theorem exists_isGermExceptionalCurve_mem_or (hf : IsGermResolution sX P f) {y : Y}
    (hy : f y = P) :
    (∃ C, IsGermExceptionalCurve f P C ∧ y ∈ C.support) ∨ f.base ⁻¹' {P} = {y} := by
  classical
  have : IsIntegral Y := hf.isIntegral sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  have hY := hf.isVariety
  have : LocallyOfFiniteType (f ≫ sX) := hY.toLocallyOfFiniteType
  have hYd := hf.topologicalKrullDim_eq
  have hFc : IsClosed (f.base ⁻¹' {P}) := isClosed_preimage_singleton hf
  have hFne : f.base ⁻¹' {P} ≠ Set.univ := preimage_singleton_ne_univ hf
  have hyF : y ∈ f.base ⁻¹' {P} := hy
  by_cases hcase : ∃ e ∈ f.base ⁻¹' {P}, ¬ IsClosed ({e} : Set Y) ∧ e ⤳ y
  · left
    obtain ⟨e, heF, hecl, hey⟩ := hcase
    obtain ⟨c, -, hec, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hecl
    have hW : closure ({e} : Set Y) ⊆ f.base ⁻¹' {P} :=
      closure_minimal (Set.singleton_subset_iff.2 heF) hFc
    have hWne : closure ({e} : Set Y) ≠ Set.univ := fun h =>
      hFne (Set.eq_univ_of_univ_subset (h ▸ hW))
    have hdim1 : topologicalKrullDim (closure ({e} : Set Y)) = 1 :=
      MMP.Mori.topologicalKrullDim_eq_one_of_ne_univ hYd.le isClosed_closure hWne
        (subset_closure rfl) (specializes_iff_mem_closure.1 hec) hec hne
    have hadd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (f ≫ sX) e
    rw [hdim1, hYd] at hadd
    have hcoh : Order.coheight e = 1 := by
      generalize Order.coheight e = d at hadd
      induction d using ENat.recTopCoe with
      | top =>
        have h2 : ((1 + ⊤ : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
          rwa [WithBot.coe_add]
        have h3 := WithBot.coe_injective h2
        simp at h3
      | coe d =>
        have h' : ((1 + d : ℕ) : WithBot ℕ∞) = ((2 : ℕ) : WithBot ℕ∞) := by
          push_cast; exact hadd
        have h'' : 1 + d = 2 := by exact_mod_cast h'
        obtain rfl : d = 1 := by omega
        rfl
    have hDsupp : ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne e hcoh).support : Set Y) =
        closure {e} := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne e hcoh,
      ⟨maximal_support_of_subset hFc hFne _ (hDsupp ▸ hW),
        isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hY hYd _⟩, ?_⟩
    show y ∈ ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne e hcoh).support : Set Y)
    rw [hDsupp]
    exact specializes_iff_mem_closure.1 hey
  · right
    have hycl : IsClosed ({y} : Set Y) := by
      by_contra h
      exact hcase ⟨y, hyF, h, specializes_rfl⟩
    have hgen : ∀ e ∈ f.base ⁻¹' {P}, e ⤳ y → e = y := by
      intro e he hey
      by_cases hecl : IsClosed ({e} : Set Y)
      · have h := specializes_iff_mem_closure.1 hey
        rw [hecl.closure_eq] at h
        exact h.symm
      · exact absurd ⟨e, he, hecl, hey⟩ hcase
    obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    set G := ⋃₀ {W ∈ Z | y ∉ W} with hG
    have hGc : IsClosed G :=
      (hZf.subset fun W hW => hW.1).isClosed_sUnion fun W hW => hZc W hW.1
    have hyG : y ∉ G := by
      rintro ⟨W, ⟨-, hyW⟩, hyW'⟩
      exact hyW hyW'
    have hFG : f.base ⁻¹' {P} ⊆ {y} ∪ G := by
      intro x hx
      rw [hZ] at hx
      obtain ⟨W, hW, hxW⟩ := hx
      by_cases hyW : y ∈ W
      · left
        obtain ⟨g, hg⟩ := QuasiSober.sober (hZirr W hW) (hZc W hW)
        have hgF : g ∈ f.base ⁻¹' {P} := by rw [hZ]; exact ⟨W, hW, hg.mem⟩
        have hgy : g = y := hgen g hgF (hg.specializes hyW)
        have hx' : x ∈ closure ({g} : Set Y) := by rwa [hg.def]
        rw [hgy, hycl.closure_eq] at hx'
        exact hx'
      · right
        exact ⟨W, ⟨hW, hyW⟩, hxW⟩
    have : IsProper f := hf.isSmoothResolution.isProper
    have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      (f ≫ sX) sX hY hf.isSurfaceGerm.1 f hf.isSmoothResolution.isBirationalMorphism).2 P
    rcases isPreconnected_iff_subset_of_disjoint_closed.1 hconn.isPreconnected {y} G hycl hGc
      hFG (by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨-, hx, hxG⟩
        rw [Set.mem_singleton_iff.1 hx] at hxG
        exact hyG hxG) with h | h
    · exact Set.Subset.antisymm h (Set.singleton_subset_iff.2 hyF)
    · exact absurd (h hyF) hyG

omit [IsAlgClosed k] in
/-- **`(R¹f_*𝒪_Y)_P = 0` kills `H¹(𝒪_T)` for every closed subscheme `T` over `P`.** By the
theorem on formal functions every thickening `X_m` of the fibre has `H¹(𝒪_{X_m}) = 0`; the
quasi-compact `T` lies in some `X_m`, a Noetherian scheme of dimension at most one, and `H¹`
descends along the closed immersion. -/
private theorem subsingleton_rightDerived_one_unit_of_subsingleton_stalk
    (hf : IsGermResolution sX P f)
    (h : Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P))
    {T : Scheme.{u}} [CompactSpace T] (t : T ⟶ Y) [IsClosedImmersion t] (ht : ∀ z, f (t z) = P) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections T).rightDerived 1).obj
      (SheafOfModules.unit T.ringCatSheaf)) := by
  have : IsProper f := hf.isSmoothResolution.isProper
  have hX := hf.isSurfaceGerm.1.1
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hP : IsClosed ({P} : Set X) := hf.isSurfaceGerm.2.2.1
  have hfib := topologicalKrullDim_preimage_le_one hf
  obtain ⟨m, t', ht', -⟩ := exists_isClosedImmersion_comp_infinitesimalι_eq f hP t ht
  have := ht'
  have := isClosedImmersion_infinitesimalι f hP m
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : CompactSpace (infinitesimalNeighbourhood f P m) :=
    (infinitesimalι f P m).isClosedEmbedding.compactSpace
  have : IsLocallyNoetherian (infinitesimalNeighbourhood f P m) :=
    LocallyOfFiniteType.isLocallyNoetherian (infinitesimalι f P m)
  have : IsNoetherian (infinitesimalNeighbourhood f P m) := {}
  have hdim : topologicalKrullDim (infinitesimalNeighbourhood f P m) ≤ 1 :=
    (Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
      (infinitesimalι f P m).isClosedEmbedding.isInducing
      (range_infinitesimalι_subset f P m)).trans (hfib P)
  have h1 := @Equiv.subsingleton _ _
    ((((Stacks.Cohomology.AffineBase.moduleGlobalSections _).rightDerived 1).mapIso
      (pullbackObjUnitIso (infinitesimalι f P m))).toLinearEquiv.toEquiv.symm)
    (subsingleton_infinitesimalCohomology_of_subsingleton_stalk f P hfib h m)
  exact subsingleton_rightDerived_one_unit t' hdim h1

/-- **Two minimal resolutions of a surface germ are isomorphic over `X`**: each dominates the
other, and the composites are the identities by uniqueness of the factorizations. -/
private theorem exists_isIso_comp_eq_of_isMinimalGermResolution {Y' : Scheme.{u}} {f' : Y' ⟶ X}
    [QuasiCompact (f' ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hf : IsMinimalGermResolution sX P f) (hf' : IsMinimalGermResolution sX P f') :
    ∃ b : Y ⟶ Y', IsIso b ∧ b ≫ f' = f := by
  have hX := hf.1.isSurfaceGerm
  have H := (MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq sX f hX.1 hX.2.1
    hf.isMinimalSurfaceResolution).1
  have H' := (MMP.Mori.IsMinimalSurfaceResolution.existsUnique_comp_eq sX f' hX.1 hX.2.1
    hf'.isMinimalSurfaceResolution).1
  obtain ⟨a, ha, -⟩ := H Y' f' hf'.1.isSmoothResolution
  obtain ⟨b, hb, -⟩ := H' Y f hf.1.isSmoothResolution
  have hba : b ≫ a = 𝟙 Y := (H Y f hf.1.isSmoothResolution).unique
    (by rw [Category.assoc, ha, hb]) (Category.id_comp f)
  have hab : a ≫ b = 𝟙 Y' := (H' Y' f' hf'.1.isSmoothResolution).unique
    (by rw [Category.assoc, hb, ha]) (Category.id_comp f')
  exact ⟨b, ⟨⟨a, hba, hab⟩⟩, hb⟩

omit [IsAlgClosed k] in
private theorem subsingleton_infinitesimal_of_forall_cycle (hf : IsGermResolution sX P f) {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration f P E) (m : ℕ)
    [IsClosedImmersion (infinitesimalι f P m)]
    (h : ∀ Z : Divisor Y, 0 ≤ Z → Z ≠ 0 → (∀ C ∈ Z.support, IsGermExceptionalCurve f P C) →
      Subsingleton (cohomologyOverField k ((cyc Z).subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) 1))
    (hn : ∃ C, IsGermExceptionalCurve f P C) :
    Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (infinitesimalNeighbourhood f P m)).rightDerived 1).obj
      (SheafOfModules.unit (infinitesimalNeighbourhood f P m).ringCatSheaf)) := by
  classical
  obtain ⟨C₀, hC₀⟩ := hn
  have : IsProper f := hf.isSmoothResolution.isProper
  have : LocallyOfFiniteType sX := hf.isSurfaceGerm.1.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  obtain ⟨j₀, -⟩ := hE.exists_eq C₀ hC₀
  have hcov : ∀ y ∈ f.base ⁻¹' {P}, ∃ j, y ∈ (E j).support := by
    intro y hy
    rcases exists_isGermExceptionalCurve_mem_or hf hy with ⟨C, hC, hyC⟩ | hF
    · obtain ⟨j, rfl⟩ := hE.exists_eq C hC
      exact ⟨j, hyC⟩
    · exact absurd ((Set.subsingleton_singleton).anti (hF ▸ hC₀.1.prop.2))
        hC₀.2.not_subsingleton
  have hJK : cycleIdeal (zMultiset E fun _ => 1) ≤ (infinitesimalι f P m).ker.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro y hy
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker,
      (infinitesimalι f P m).isClosedEmbedding.isClosed_range.closure_eq] at hy
    obtain ⟨j, hyj⟩ := hcov y (range_infinitesimalι_subset f P m hy)
    exact (mem_support_cycleIdeal _ y).2 ⟨E j, mem_zMultiset E one_ne_zero, hyj⟩
  obtain ⟨N, hN⟩ := Scheme.IdealSheafData.exists_pow_le_of_le_radical hJK
  set m' := zMultiset E fun _ => N + 1 with hm'
  have hJN : cycleIdeal m' ≤ (infinitesimalι f P m).ker := by
    rw [hm', cycleIdeal_zMultiset_const]
    exact (Scheme.IdealSheafData.pow_le_pow_of_le _ (Nat.le_succ N)).trans hN
  have hle : (cycleIdeal m').subschemeι.ker ≤ (infinitesimalι f P m).ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  set t' := IsClosedImmersion.lift (cycleIdeal m').subschemeι (infinitesimalι f P m) hle
  have ht' : t' ≫ (cycleIdeal m').subschemeι = infinitesimalι f P m :=
    IsClosedImmersion.lift_fac _ _ hle
  have : IsClosedImmersion (t' ≫ (cycleIdeal m').subschemeι) := ht' ▸ inferInstance
  have : IsClosedImmersion t' := IsClosedImmersion.of_comp_isClosedImmersion _
    (cycleIdeal m').subschemeι
  have hm'E : ∀ C ∈ m', IsGermExceptionalCurve f P C := fun C hC =>
    isGermExceptionalCurve_of_mem_zMultiset hE hC
  have hZ := h (cycleDivisor m') (cycleDivisor_nonneg m')
    (cycleDivisor_zMultiset_ne_zero hE.injective (Function.ne_iff.2 ⟨j₀, by simp⟩))
    fun C hC => hm'E C (mem_of_mem_support_cycleDivisor hC)
  rw [cyc_cycleDivisor] at hZ
  have : CompactSpace (cycleIdeal m').subscheme :=
    (cycleIdeal m').subschemeι.isClosedEmbedding.compactSpace
  have : IsLocallyNoetherian (cycleIdeal m').subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (cycleIdeal m').subschemeι
  have : IsNoetherian (cycleIdeal m').subscheme := {}
  exact subsingleton_rightDerived_one_unit t'
    (topologicalKrullDim_cycleIdeal_le m' fun C hC => (hm'E C hC).2.2.le) hZ

omit [IsAlgClosed k] in
/-- **`(R¹f_*𝒪_Y)_P = 0` if and only if `H¹(𝒪_Z) = 0` for every nonzero effective exceptional
cycle `Z`.** -/
private theorem subsingleton_stalk_iff_forall_cycle (hf : IsGermResolution sX P f) {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration f P E) :
    Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P) ↔
    ∀ Z : Divisor Y, 0 ≤ Z → Z ≠ 0 → (∀ C ∈ Z.support, IsGermExceptionalCurve f P C) →
      Subsingleton (cohomologyOverField k ((cyc Z).subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) 1) := by
  classical
  have : IsProper f := hf.isSmoothResolution.isProper
  have hX := hf.isSurfaceGerm.1.1
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hP : IsClosed ({P} : Set X) := hf.isSurfaceGerm.2.2.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have hfib := topologicalKrullDim_preimage_le_one hf
  have hXm : ∀ m, IsClosedImmersion (infinitesimalι f P m) := isClosedImmersion_infinitesimalι f hP
  have hXmN : ∀ m, IsNoetherian (infinitesimalNeighbourhood f P m) := fun m => by
    have := hXm m
    have : CompactSpace (infinitesimalNeighbourhood f P m) :=
      (infinitesimalι f P m).isClosedEmbedding.compactSpace
    have : IsLocallyNoetherian (infinitesimalNeighbourhood f P m) :=
      LocallyOfFiniteType.isLocallyNoetherian (infinitesimalι f P m)
    exact {}
  have hXmdim : ∀ m, topologicalKrullDim (infinitesimalNeighbourhood f P m) ≤
      topologicalKrullDim (f.base ⁻¹' {P}) := fun m =>
    haveI := hXm m
    Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
      (infinitesimalι f P m).isClosedEmbedding.isInducing (range_infinitesimalι_subset f P m)
  have hinf : ∀ m, Subsingleton (infinitesimalCohomology f (SheafOfModules.unit Y.ringCatSheaf)
      P 1 m) ↔ Subsingleton (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (infinitesimalNeighbourhood f P m)).rightDerived 1).obj
        (SheafOfModules.unit (infinitesimalNeighbourhood f P m).ringCatSheaf)) := fun m =>
    ((((Stacks.Cohomology.AffineBase.moduleGlobalSections _).rightDerived 1).mapIso
      (pullbackObjUnitIso (infinitesimalι f P m))).toLinearEquiv.toEquiv).subsingleton_congr
  constructor
  · intro h Z hZ hZ0 hZE
    obtain ⟨hsub, -, -⟩ := cyc_support_subset_and hZ hZ0 hZE
    have : CompactSpace (cyc Z).subscheme := (cyc Z).subschemeι.isClosedEmbedding.compactSpace
    exact subsingleton_rightDerived_one_unit_of_subsingleton_stalk hf h (cyc Z).subschemeι
      fun z => hsub (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
  · intro h
    refine subsingleton_stalk_of_forall_subsingleton_infinitesimalCohomology f P fun m =>
      (hinf m).2 ?_
    have := hXm m
    have := hXmN m
    by_cases hn : ∃ C, IsGermExceptionalCurve f P C
    · exact subsingleton_infinitesimal_of_forall_cycle hf hE m h hn
    · have hsub : (f.base ⁻¹' {P}).Subsingleton := fun a ha b hb => by
        rcases exists_isGermExceptionalCurve_mem_or hf ha with ⟨C, hC, -⟩ | hF
        · exact absurd ⟨C, hC⟩ hn
        · rw [hF] at hb
          exact hb.symm
      have := hsub.coe_sort
      have : DiscreteTopology (f.base ⁻¹' {P}) := Subsingleton.discreteTopology
      exact subsingleton_rightDerived_one_unit_of_topologicalKrullDim_le_zero
        ((hXmdim m).trans (topologicalKrullDim_zero_of_discreteTopology _))

omit [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **`H¹(𝒪_Z) = 0` for every exceptional cycle if and only if `χ(𝒪_Z) ≥ 1` for every one.** -/
private theorem forall_cycle_subsingleton_iff_one_le (hf : IsGermResolution sX P f) :
    (∀ Z : Divisor Y, 0 ≤ Z → Z ≠ 0 → (∀ C ∈ Z.support, IsGermExceptionalCurve f P C) →
      Subsingleton (cohomologyOverField k ((cyc Z).subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) 1)) ↔
    ∀ Z : Divisor Y, 0 ≤ Z → Z ≠ 0 → (∀ C ∈ Z.support, IsGermExceptionalCurve f P C) →
      ∀ _ : IsProper ((cyc Z).subschemeι ≫ f ≫ sX),
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          ((cyc Z).subschemeι ≫ f ≫ sX)
        1 ≤ eulerCharacteristic k ((cyc Z).subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) := by
  constructor
  · intro h Z hZ hZ0 hZE hp
    obtain ⟨-, hdim, hne⟩ := cyc_support_subset_and hZ hZ0 hZE
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cyc Z).subschemeι ≫ f ≫ sX)
    have := h Z hZ hZ0 hZE
    have h0 : Module.finrank k (cohomologyOverField k ((cyc Z).subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf) 1) = 0 :=
      Module.finrank_zero_of_subsingleton
    have h1 := one_le_finrank_cohomologyOverField_zero_unit (k := k)
      ((cyc Z).subschemeι ≫ f ≫ sX)
    have h2 := eulerCharacteristic_eq_finrank_sub ((cyc Z).subschemeι ≫ f ≫ sX) hdim
      (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf)
    rw [h0] at h2
    change 1 ≤ eulerCharacteristic k ((cyc Z).subschemeι ≫ f ≫ sX)
      (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf)
    omega
  · intro h Z hZ hZ0 hZE
    refine hf.subsingleton_cohomologyOverField_one_divisorIdeal hZ hZ0 hZE
      fun Z' hZ' hZ'Z hZ'0 hp => ?_
    have hZ'E : ∀ C ∈ Z'.support, IsGermExceptionalCurve f P C := fun C hC => hZE C (by
      rw [Finsupp.mem_support_iff] at hC ⊢
      exact fun h0 => hC (le_antisymm (h0 ▸ hZ'Z C) (hZ' C)))
    exact Int.lt_of_lt_of_le Int.zero_lt_one (h Z' hZ' hZ'0 hZ'E hp)

/-- **`χ(𝒪_Z) ≥ 1` for every exceptional cycle if and only if `Γ` is rational**, by the cycle
formula `χ(𝒪_Z) = -½ (Z² + K_Y · Z)`. -/
private theorem forall_one_le_iff_isRational {B : QDivisor X} {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B f E Γ) :
    (∀ Z : Divisor Y, 0 ≤ Z → Z ≠ 0 → (∀ C ∈ Z.support, IsGermExceptionalCurve f P C) →
      ∀ _ : IsProper ((cyc Z).subschemeι ≫ f ≫ sX),
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          ((cyc Z).subschemeι ≫ f ≫ sX)
        1 ≤ eulerCharacteristic k ((cyc Z).subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit (cyc Z).subscheme.ringCatSheaf)) ↔ Γ.IsRational := by
  classical
  have hf := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  constructor
  · intro hall z hz
    have hp : IsProper ((cyc (cycleDivisor (zMultiset E z))).subschemeι ≫ f ≫ sX) := by
      rw [cyc_cycleDivisor]
      exact isProper_cycleIdeal hf fun C hC => isGermExceptionalCurve_of_mem_zMultiset hE hC
    have h1 := hall _ (cycleDivisor_nonneg _) (cycleDivisor_zMultiset_ne_zero hE.injective hz)
      (fun C hC => isGermExceptionalCurve_of_mem_zMultiset hE
        (mem_of_mem_support_cycleDivisor hC)) hp
    have h := eulerCharacteristic_cyc_zMultiset_eq hΓ z hz hp
    have h1' := (Int.cast_le (R := ℚ)).2 h1
    rw [Int.cast_one, h] at h1'
    linarith
  · intro hrat Z hZ hZ0 hZE hp
    have hZeq : Z = cycleDivisor (zMultiset E fun j => (Z (E j)).toNat) := by
      refine Finsupp.ext fun C => ?_
      rw [cycleDivisor_apply]
      by_cases hC : ∃ j, E j = C
      · obtain ⟨j, rfl⟩ := hC
        rw [count_zMultiset hE.injective, Int.toNat_of_nonneg (hZ (E j))]
      · have h0 : Z C = 0 := by
          by_contra h0
          exact hC (hE.exists_eq C (hZE C (Finsupp.mem_support_iff.2 h0)))
        rw [h0, eq_comm, Nat.cast_eq_zero, Multiset.count_eq_zero]
        exact fun hmem => hC (exists_eq_of_mem_zMultiset hmem)
    obtain ⟨z, rfl⟩ : ∃ z, Z = cycleDivisor (zMultiset E z) := ⟨_, hZeq⟩
    have hz : z ≠ 0 := by
      rintro rfl
      apply hZ0
      simp [zMultiset, cycleDivisor]
    have h := eulerCharacteristic_cyc_zMultiset_eq hΓ z hz hp
    have h2 := hrat z hz
    have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cyc (cycleDivisor (zMultiset E z))).subschemeι ≫ f ≫ sX)
    have h1 : (1 : ℚ) ≤ (eulerCharacteristic k ((cyc (cycleDivisor (zMultiset E z))).subschemeι ≫
        f ≫ sX) (SheafOfModules.unit (cyc (cycleDivisor (zMultiset E z))).subscheme.ringCatSheaf) :
          ℚ) := by
      rw [h]
      linarith
    exact_mod_cast h1

/-- **Minimal resolutions have the same `(R¹f_*𝒪)_P`**: two minimal resolutions of `(X, P)`
are isomorphic over `X`. -/
private theorem subsingleton_stalk_of_isMinimalGermResolution {Y' : Scheme.{u}} {f' : Y' ⟶ X}
    [QuasiCompact (f' ≫ sX)] [IsLocallyNoetherian Y'] [IsNormal Y']
    (hf : IsMinimalGermResolution sX P f) (hf' : IsMinimalGermResolution sX P f') {n : ℕ}
    {E : Fin n → MMP.Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration f P E)
    (h : Subsingleton ((((Scheme.Modules.pushforward f').rightDerived 1).obj
      (SheafOfModules.unit Y'.ringCatSheaf)).presheaf.stalk P)) :
    Subsingleton ((((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit Y.ringCatSheaf)).presheaf.stalk P) := by
  obtain ⟨b, hb, hbf⟩ := exists_isIso_comp_eq_of_isMinimalGermResolution hf hf'
  refine (subsingleton_stalk_iff_forall_cycle hf.1 hE).2 fun Z hZ hZ0 hZE => ?_
  obtain ⟨hsub, -, -⟩ := cyc_support_subset_and hZ hZ0 hZE
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : CompactSpace (cyc Z).subscheme := (cyc Z).subschemeι.isClosedEmbedding.compactSpace
  exact subsingleton_rightDerived_one_unit_of_subsingleton_stalk hf'.1 h
    ((cyc Z).subschemeι ≫ b) fun z => by
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply b f', hbf]
      exact hsub (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)

end Main

/-- **Artin's rationality criterion.** Let `f : Y ⟶ X` be the minimal resolution of a surface
germ `(X, P)` over an algebraically closed field `k`, with exceptional curves `E_1, …, E_n`, and
let `Γ` be its weighted dual graph `Γ(f)`. Then `(X, P)` is a rational singularity if and only
if `Γ` is a rational weighted graph. -/
@[mmp "lem_mmp_foundation_fa3_artin_rationality_criterion"]
public theorem IsWeightedDualGraph.isRationalSurfaceSingularity_iff_isRational {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ) :
    IsRationalSurfaceSingularity sX P ↔ Γ.IsRational := by
  have key := ((subsingleton_stalk_iff_forall_cycle hf.1 hΓ.isExceptionalCurveEnumeration).trans
    (forall_cycle_subsingleton_iff_one_le hf.1)).trans (forall_one_le_iff_isRational hΓ)
  constructor
  · rintro ⟨Y', f', _, _, _, hf', hs⟩
    exact key.1 (subsingleton_stalk_of_isMinimalGermResolution hf hf'
      hΓ.isExceptionalCurveEnumeration hs)
  · intro h
    exact ⟨Y, f, inferInstance, inferInstance, inferInstance, hf, key.2 h⟩

/-! ### Degree-zero invertible sheaves on rational cycles -/

section LineBundle

variable {k : Type u} [Field k] {Y : Scheme.{u}}

/-! ### Symmetry of intersection numbers -/

section Intersection

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **Symmetry of the intersection numbers of two curves on a smooth surface.** -/
private theorem ixn_single_comm (hY : MMP.Mori.IsVariety k s) (hsm : IsSmoothScheme s)
    (hd : topologicalKrullDim Y = 2) {E F : MMP.Mori.PrimeDivisor Y}
    (hE : IsProper (E.idealSheaf.subschemeι ≫ s)) (hF : IsProper (F.idealSheaf.subschemeι ≫ s)) :
    ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E =
      ixn s (Divisor.toQDivisor (Finsupp.single E 1)) F := by
  by_cases hEF : E = F
  · subst hEF; rfl
  obtain ⟨-, h1, -⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne s hY hsm hd hEF hE
  obtain ⟨-, h2, -⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne s hY hsm hd
      (Ne.symm hEF) hF
  rw [MMP.Threefold.Resolution.toQDivisor_single, MMP.Threefold.Resolution.toQDivisor_single]
  push_cast
  rw [ixn_eq_of_isIntersectionNumber h1, ixn_eq_of_isIntersectionNumber h2, Set.inter_comm]
  congr 1
  funext z
  rw [MMP.Mori.localIntersectionNumber, MMP.Mori.localIntersectionNumber, sup_comm]

end Intersection

/-! ### Degrees of the invertible sheaves of divisors -/

section Degree

variable {s : Y ⟶ Spec (.of k)} {C : Scheme.{u}} (i : C ⟶ Y) [IsProper (i ≫ s)]
  (hdim : topologicalKrullDim C ≤ 1)

private theorem isInvertible_invertibleSheaf' (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (Stacks.Divisors.invertibleSheaf' D) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Divisors.isTensorInvertible_invertibleSheaf D)

private theorem isInvertible_negativeTwist' (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (Stacks.Divisors.negativeTwist' D) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Divisors.isTensorInvertible_negativeTwist D)

/-- The structure sheaf has degree zero. -/
private theorem degreeOn_unit
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 (SheafOfModules.unit Y.ringCatSheaf)] :
    MMP.Mori.degreeOn k s i hdim (SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  have := MMP.Mori.isInvertible_pullback_obj i (SheafOfModules.unit Y.ringCatSheaf)
  exact (MMP.Mori.degreeOn_eq_invertibleCurveDegree k s i hdim _).trans
    (invertibleCurveDegree_eq_zero_of_iso_unit k (i ≫ s) hdim _
      (Scheme.Modules.pullbackUnitIso i))

/-- `deg 𝒪_Y(-D) = -deg 𝒪_Y(D)` for an effective Cartier divisor `D`: the evaluation pairing
trivialises `𝒪_Y(D) ⊗ 𝒪_Y(-D)`. -/
private theorem degreeOn_negativeTwist' (D : Y.IdealSheafData)
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    haveI := isInvertible_negativeTwist' D
    haveI := isInvertible_invertibleSheaf' D
    MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.negativeTwist' D) =
      -MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' D) := by
  have := isInvertible_negativeTwist' D
  have := isInvertible_invertibleSheaf' D
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (tens Y (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.negativeTwist' D)) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Models.isTensorInvertible_invertibleSheafTensorNegativeTwist D hD)
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (SheafOfModules.unit Y.ringCatSheaf) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.Models.isTensorInvertible_unit Y)
  have h1 := MMP.Mori.degreeOn_tensorSheaf k s i hdim (Stacks.Divisors.invertibleSheaf' D)
    (Stacks.Divisors.negativeTwist' D)
  have h0 := (MMP.Mori.degreeOn_eq_of_iso k s i hdim
    (Stacks.Models.invertibleSheafTensorNegativeTwistIsoUnit D hD)).trans (degreeOn_unit i hdim)
  omega

private theorem degreeOn_invertibleSheaf'_congr {D D' : Y.IdealSheafData} (h : D = D')
    [Stacks.Divisors.IsEffectiveCartierDivisor D] [Stacks.Divisors.IsEffectiveCartierDivisor D'] :
    haveI := isInvertible_invertibleSheaf' D
    haveI := isInvertible_invertibleSheaf' D'
    MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' D) =
      MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' D') := by
  subst h; rfl

/-- **The degree of `𝒪_Y(∑_{F ∈ m} F)` is `∑_{F ∈ m} deg 𝒪_Y(F)`** on a smooth `Y`. -/
private theorem degreeOn_invertibleSheaf'_cycleIdeal [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme s) (m : Multiset (MMP.Mori.PrimeDivisor Y)) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isInvertible_invertibleSheaf' (cycleIdeal m)
    MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' (cycleIdeal m)) =
      (m.map fun F =>
        haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
          hsm F
        haveI := isInvertible_invertibleSheaf' F.idealSheaf
        MMP.Mori.degreeOn k s i hdim (Stacks.Divisors.invertibleSheaf' F.idealSheaf)).sum := by
  induction m using Multiset.induction_on with
  | empty =>
    have := isEffectiveCartierDivisor_cycleIdeal hsm (0 : Multiset (MMP.Mori.PrimeDivisor Y))
    have : Stacks.Divisors.IsEffectiveCartierDivisor (⊤ : Y.IdealSheafData) :=
      Stacks.Divisors.isEffectiveCartierDivisor_top
    have := isInvertible_invertibleSheaf' (⊤ : Y.IdealSheafData)
    have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (SheafOfModules.unit Y.ringCatSheaf) :=
      (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
        (Stacks.Models.isTensorInvertible_unit Y)
    refine (degreeOn_invertibleSheaf'_congr i hdim cycleIdeal_zero).trans
      ((MMP.Mori.degreeOn_eq_of_iso k s i hdim (L' := SheafOfModules.unit Y.ringCatSheaf)
        Stacks.Divisors.invertibleSheafTopIsoUnit).trans ?_)
    rw [degreeOn_unit i hdim]
    simp
  | cons F m ih =>
    have := isEffectiveCartierDivisor_cycleIdeal hsm m
    have := isEffectiveCartierDivisor_cycleIdeal hsm (F ::ₘ m)
    have := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
    have := isInvertible_invertibleSheaf' (F.idealSheaf * cycleIdeal m)
    have := isInvertible_invertibleSheaf' F.idealSheaf
    have := isInvertible_invertibleSheaf' (cycleIdeal m)
    have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        (Stacks.Divisors.sumSheaf F.idealSheaf (cycleIdeal m)) :=
      Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible Y.presheaf Y.ringCatSheaf.2 _ _
    rw [degreeOn_invertibleSheaf'_congr i hdim (cycleIdeal_cons F m),
      ← MMP.Mori.degreeOn_eq_of_iso k s i hdim
        (Stacks.Divisors.invertibleSheafSumIso F.idealSheaf (cycleIdeal m)),
      Multiset.map_cons, Multiset.sum_cons, ← ih]
    exact MMP.Mori.degreeOn_tensorSheaf k s i hdim _ _

end Degree

/-! ### Intersection numbers as degrees -/

section Curves

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `(F · E) = deg_E 𝒪_Y(F)` for prime divisors `E`, `F` on a smooth `Y`, with the invertible
sheaf of the effective Cartier divisor `F`. -/
private theorem ixn_single_eq_degreeOn (hsm : IsSmoothScheme s) {E : MMP.Mori.PrimeDivisor Y}
    (F : MMP.Mori.PrimeDivisor Y) [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
    haveI := isInvertible_invertibleSheaf' F.idealSheaf
    ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E =
      MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd
        (Stacks.Divisors.invertibleSheaf' F.idealSheaf) := by
  have hF := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm F
  have := isInvertible_invertibleSheaf' F.idealSheaf
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have hc := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm F
  obtain ⟨b⟩ :=
    MMP.Threefold.Resolution.nonempty_divisorialSheaf_single_iso_invertibleSheaf' F hF hc
  have := hc.isInvertibleModule_divisorialSheaf
  rw [ixn_eq_of_isIntersectionNumber (isIntersectionNumber_degreeOn hsm hd _)]
  congr 1
  exact MMP.Mori.degreeOn_eq_of_iso k s _ hd b

/-- **`χ(𝒪_Y(-W)|_E) = χ(𝒪_E) - (W · E)`** for `W = ∑_{F ∈ m} F` and a prime divisor `E` which
is a proper curve. -/
private theorem eulerCharacteristic_negativeTwist_cycleIdeal (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isInvertible_pullback_negativeTwist (cycleIdeal m) E.idealSheaf
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
      (E.idealSheaf.subschemeι ≫ s)
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m))) 1
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ s)
    (eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
          (Stacks.Divisors.negativeTwist (cycleIdeal m))) : ℚ) =
      eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) -
        (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  have := isEffectiveCartierDivisor_cycleIdeal hsm m
  have := isInvertible_pullback_negativeTwist (cycleIdeal m) E.idealSheaf
  have hN := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k
    (E.idealSheaf.subschemeι ≫ s)
    ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
      (Stacks.Divisors.negativeTwist (cycleIdeal m))) 1
  have hO := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
    (E.idealSheaf.subschemeι ≫ s)
  have := isInvertible_negativeTwist' (cycleIdeal m)
  have h1 := ((MMP.Mori.degreeOn_eq_invertibleCurveDegree k s E.idealSheaf.subschemeι hd
    (Stacks.Divisors.negativeTwist' (cycleIdeal m))).trans
    (@invertibleCurveDegree_eq_eulerCharacteristic_sub k _ _ (E.idealSheaf.subschemeι ≫ s) _ hd
      _ _ hN hO)).symm
  rw [degreeOn_negativeTwist', degreeOn_invertibleSheaf'_cycleIdeal _ hd hsm m] at h1
  have h2 : (((m.map fun F =>
        haveI := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme
          hsm F
        haveI := isInvertible_invertibleSheaf' F.idealSheaf
        MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd
          (Stacks.Divisors.invertibleSheaf' F.idealSheaf)).sum : ℤ) : ℚ) =
      (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
    rw [Int.cast_multiset_sum, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl fun F _ => (ixn_single_eq_degreeOn hsm F hd).symm)
  have h3 := congrArg (Int.cast : ℤ → ℚ) h1
  rw [Int.cast_sub, Int.cast_neg, h2] at h3
  linarith

/-- **The induction step for `χ`**: for `W = ∑_{F ∈ m} F` and a prime divisor `E` which is a
proper curve, `χ(𝒪_{W+E}) = χ(𝒪_W) + χ(𝒪_E) - ∑_{F ∈ m} (F · E)`. -/
private theorem eulerCharacteristic_cycleIdeal_mul (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1)
    [IsProper ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)] :
    haveI := isProper_of_le (s := s) (Scheme.IdealSheafData.mul_le_left (cycleIdeal m) E.idealSheaf)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((cycleIdeal m).subschemeι ≫ s)
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      (E.idealSheaf.subschemeι ≫ s)
    (eulerCharacteristic k ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s)
        (SheafOfModules.unit (cycleIdeal m * E.idealSheaf).subscheme.ringCatSheaf) : ℚ) =
      eulerCharacteristic k ((cycleIdeal m).subschemeι ≫ s)
          (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf) +
        eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) -
        (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  have := isEffectiveCartierDivisor_cycleIdeal hsm m
  have := MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hsm E
  have h := congrArg (Int.cast : ℤ → ℚ)
    (eulerCharacteristic_unit_mul (s := s) (cycleIdeal m) E.idealSheaf)
  push_cast at h
  rw [h, eulerCharacteristic_negativeTwist_cycleIdeal hsm m E hd]
  ring

end Curves

/-! ### The induction on the cycle -/

section Induction

variable [IsAlgClosed k] {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- **The cycle formula, by induction on the cycle.** For a nonzero cycle `Z = ∑_{E ∈ m} E` of
proper curves on a smooth surface whose subcycles are proper over `k`,
`χ(𝒪_Z) = -½ ∑_{E ∈ m} ((Z + K) · E)`. -/
private theorem eulerCharacteristic_cycleIdeal_eq
    (hY : MMP.Mori.IsVariety k s) (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor s 2)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (hm0 : m ≠ 0)
    (hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ s) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1)
    (hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ s)) :
    ∀ hp : IsProper ((cycleIdeal m).subschemeι ≫ s),
      haveI := hp
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((cycleIdeal m).subschemeι ≫ s)
      (eulerCharacteristic k ((cycleIdeal m).subschemeι ≫ s)
        (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf) : ℚ) =
        -(m.map fun F => ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F).sum / 2 := by
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm0
  | cons E m ih =>
    obtain ⟨hEp, hEd⟩ := hmE E (Multiset.mem_cons_self E m)
    have := hEp
    have hadj := ixn_canonical_add_single (s := s) hY hsm hd hK E
    by_cases hm : m = 0
    · subst hm
      have hc : cycleDivisor (E ::ₘ 0) + K = K + Finsupp.single E 1 := by
        rw [cycleDivisor_cons]
        simp [cycleDivisor, add_comm]
      rw [cycleIdeal_cons', cycleIdeal_zero, ← Scheme.IdealSheafData.one_eq_top, one_mul]
      intro _
      simp only [Multiset.map_cons, Multiset.map_zero, Multiset.sum_cons, Multiset.sum_zero,
        add_zero, hc, hadj]
      ring
    · have hle : m ≤ E ::ₘ m := Multiset.le_cons_self m E
      have hmE' : ∀ F ∈ m, IsProper (F.idealSheaf.subschemeι ≫ s) ∧
          topologicalKrullDim F.idealSheaf.subscheme ≤ 1 :=
        fun F hF => hmE F (Multiset.mem_cons_of_mem hF)
      have hih := ih hm hmE' (fun m' hm' => hprop m' (hm'.trans hle)) (hprop m hle)
      have hpJ : IsProper ((cycleIdeal m * E.idealSheaf).subschemeι ≫ s) := by
        rw [← cycleIdeal_cons']; exact hprop _ le_rfl
      rw [cycleIdeal_cons']
      intro _
      have hstep := eulerCharacteristic_cycleIdeal_mul hsm m E hEd
      have hlin : ∀ F ∈ E ::ₘ m, ixn s (Divisor.toQDivisor (cycleDivisor (E ::ₘ m) + K)) F =
          ixn s (Divisor.toQDivisor (Finsupp.single E 1)) F +
            ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F := by
        intro F hF
        rw [cycleDivisor_cons, add_assoc, map_add, ixn_add hsm (hmE F hF).1 (hmE F hF).2]
      have hsum : (m.map fun F =>
            ixn s (Divisor.toQDivisor (cycleDivisor (E ::ₘ m) + K)) F).sum =
          (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum +
            (m.map fun F => ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F).sum := by
        rw [← Multiset.sum_map_add]
        congr 1
        refine Multiset.map_congr rfl fun F hF => ?_
        rw [hlin F (Multiset.mem_cons_of_mem hF),
          ixn_single_comm hY hsm hd hEp (hmE' F hF).1]
      have hE : ixn s (Divisor.toQDivisor (cycleDivisor (E ::ₘ m) + K)) E =
          ixn s (Divisor.toQDivisor (Finsupp.single E 1)) E +
            (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum +
              ixn s (Divisor.toQDivisor K) E := by
        rw [hlin E (Multiset.mem_cons_self E m), map_add,
          ixn_cycleDivisor_add hsm hEp hEd m (Divisor.toQDivisor K)]
        ring
      rw [map_add, ixn_add hsm hEp hEd] at hadj
      rw [Multiset.map_cons, Multiset.sum_cons, hE, hsum]
      linarith

/-- **A component of genus zero meeting the rest of the cycle twice is not `K + Z`-negative.**
For a component `F` of `Z = ∑_{G ∈ m} G` with `χ(𝒪_F) = 1` and `((Z - F) · F) ≥ 2`, adjunction
`((K + F) · F) = -2` gives `((Z + K) · F) ≥ 0`. -/
private theorem ixn_cycleDivisor_add_canonical_nonneg [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    (hY : MMP.Mori.IsVariety k s)
    (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2) {K : Divisor Y}
    (hK : K.IsCanonicalDivisor s 2) {m : Multiset (MMP.Mori.PrimeDivisor Y)}
    {F : MMP.Mori.PrimeDivisor Y} (hF : F ∈ m) [hFp : IsProper (F.idealSheaf.subschemeι ≫ s)]
    (hFd : topologicalKrullDim F.idealSheaf.subscheme ≤ 1)
    (hχ : @eulerCharacteristic k _ _ (F.idealSheaf.subschemeι ≫ s) hFp
      (SheafOfModules.unit F.idealSheaf.subscheme.ringCatSheaf)
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (F.idealSheaf.subschemeι ≫ s)) = 1)
    (h2 : 2 ≤ ((m.erase F).map fun G => ixn s (Divisor.toQDivisor (Finsupp.single G 1)) F).sum) :
    0 ≤ ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F := by
  have hadj := ixn_canonical_add_single (s := s) hY hsm hd hK F
  rw [hχ, map_add, ixn_add hsm hFp hFd] at hadj
  rw [map_add, ixn_cycleDivisor_add hsm hFp hFd m (Divisor.toQDivisor K),
    ← Multiset.cons_erase hF, Multiset.map_cons, Multiset.sum_cons]
  push_cast at hadj
  linarith

/-- **A cycle with `χ(𝒪_Z) > 0` whose components have `χ(𝒪_E) = 1` has a component `E` with
`((Z - E) · E) ≤ 1`.** Otherwise every `((Z + K) · E)` is nonnegative by adjunction, and the cycle
formula `χ(𝒪_Z) = -½ ∑_{E ∈ Z} ((Z + K) · E)` makes `χ(𝒪_Z) ≤ 0`. -/
private theorem exists_mem_not_two_le_sum_ixn [DecidableEq (MMP.Mori.PrimeDivisor Y)]
    (hY : MMP.Mori.IsVariety k s) (hsm : IsSmoothScheme s) (hd : topologicalKrullDim Y = 2)
    {K : Divisor Y} (hK : K.IsCanonicalDivisor s 2)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (hm0 : m ≠ 0)
    (hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ s) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1)
    (hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ s))
    (hχE : ∀ E ∈ m, ∀ hp : IsProper (E.idealSheaf.subschemeι ≫ s),
      haveI := hp
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        (E.idealSheaf.subschemeι ≫ s)
      eulerCharacteristic k (E.idealSheaf.subschemeι ≫ s)
        (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) = 1)
    (hχ : haveI := hprop m le_rfl
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((cycleIdeal m).subschemeι ≫ s)
      0 < eulerCharacteristic k ((cycleIdeal m).subschemeι ≫ s)
        (SheafOfModules.unit (cycleIdeal m).subscheme.ringCatSheaf)) :
    ∃ E ∈ m, ¬ 2 ≤ ((m.erase E).map fun F =>
      ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  by_contra hcon
  push Not at hcon
  have hsum : 0 ≤ (m.map fun F => ixn s (Divisor.toQDivisor (cycleDivisor m + K)) F).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨F, hF, rfl⟩ := Multiset.mem_map.1 hx
      have := (hmE F hF).1
      exact ixn_cycleDivisor_add_canonical_nonneg hY hsm hd hK hF (hmE F hF).2
        (hχE F hF _) (hcon F hF)
  have hq := eulerCharacteristic_cycleIdeal_eq hY hsm hd hK m hm0 hmE hprop (hprop m le_rfl)
  have : (0 : ℚ) < _ := Int.cast_pos.2 hχ
  linarith

end Induction

/-! ### First cohomology on the components and on the cycles -/

section Cohomology

/-- On an integral proper curve over an algebraically closed field, `χ(𝒪) = 1 - h¹(𝒪)`: the
global functions are the constants. -/
private theorem eulerCharacteristic_unit_eq_one_sub [IsAlgClosed k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1) :
    haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
    eulerCharacteristic k g (SheafOfModules.unit C.ringCatSheaf) =
      1 - (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 1) : ℤ) := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  have h0 : Module.finrank k (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 0) = 1 :=
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k g).trans
      (finrank_globalSections_eq_one k g)
  refine (eulerCharacteristic_eq_finrank_sub g hdim _).trans ?_
  omega

/-- **On a curve of genus zero, an invertible sheaf with `H¹ ≠ 0` has degree at most `-2`**:
by [Stacks, Tag 0B90], `H¹(ℒ) = 0` as soon as `deg ℒ ≥ 2g - 1 = -1`. -/
private theorem invertibleCurveDegree_le_neg_two [IsAlgClosed k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [AlgebraicGeometry.IsCurve k g]
    (hg : Module.finrank k (cohomologyOverField k g (SheafOfModules.unit C.ringCatSheaf) 1) = 0)
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [hL : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L]
    (h : ¬ IsZero (cohomologyOverField k g L 1)) : invertibleCurveDegree k g hdim L ≤ -2 := by
  by_contra hlt
  apply h
  refine
    isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree k g L hL ?_
  have hgen : genus g = 0 := by
    rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k g 1).toLinearEquiv.finrank_eq, hg]
  rw [hgen]
  push_cast
  have : invertibleCurveDegree k g (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le L =
      invertibleCurveDegree k g hdim L := rfl
  omega

variable {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `deg_E 𝒪_Y(-W) = -∑_{F ∈ m} (F · E)` for `W = ∑_{F ∈ m} F` and a prime divisor `E` which is
a proper curve on a smooth `Y`. -/
private theorem degreeOn_negativeTwist'_cycleIdeal (hsm : IsSmoothScheme s)
    (m : Multiset (MMP.Mori.PrimeDivisor Y)) (E : MMP.Mori.PrimeDivisor Y)
    [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme ≤ 1) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    haveI := isInvertible_negativeTwist' (cycleIdeal m)
    (MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd
        (Stacks.Divisors.negativeTwist' (cycleIdeal m)) : ℚ) =
      -(m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum := by
  have := isEffectiveCartierDivisor_cycleIdeal hsm m
  have := isInvertible_negativeTwist' (cycleIdeal m)
  rw [degreeOn_negativeTwist', degreeOn_invertibleSheaf'_cycleIdeal _ hd hsm m, Int.cast_neg,
    Int.cast_multiset_sum, Multiset.map_map]
  exact congrArg _ (congrArg _ (Multiset.map_congr rfl fun F _ =>
    (ixn_single_eq_degreeOn hsm F hd).symm))

end Cohomology

/-! ### Restriction and gluing of sections -/

/-- Tensoring with a fixed module on the right, as an endofunctor of the modules on a scheme. -/
private abbrev tensorRight {X : Scheme.{u}} (L : X.Modules) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).flip.obj L

open Stacks.ProjectionFormula Stacks.RingedSpace RingedSpaceModuleAdjunction in
/-- `L ⊗ 𝒪_D` is the direct image of `L|_D`, compatibly with the maps from `L`. -/
private theorem exists_tensor_pushforward_iso {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (D : X.IdealSheafData) :
    ∃ φ : (tensorRight L).obj (Scheme.IdealSheafData.closedSubschemeStructureSheaf D) ≅
        (Scheme.Modules.pushforward D.subschemeι).obj
          ((Scheme.Modules.pullback D.subschemeι).obj L),
      (tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme D) ≫ φ.hom =
        (unitTensorIso X.toRingedSpace L).hom ≫
          (Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app L := by
  let F : SheafOfModules (structureSheafRing X.toRingedSpace) ⥤
      SheafOfModules (structureSheafRing X.toRingedSpace) :=
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).flip.obj L
  let f := D.subschemeι.toLRSHom.toShHom
  have hiso := isIso_projectionFormulaMap f
    (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace)) L
  have hcomp := tensorUnitToPushforward_comp_projectionFormulaMap' (f := f) L
  have hsc := isIso_structureComparison f L
  let ψi : ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨D.subscheme.toRingedSpace.presheaf, D.subscheme.toRingedSpace.IsSheaf⟩))).obj
        (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace),
          (pullbackFunctor f).obj L) ≅ (pullbackFunctor f).obj L :=
    (@asIso _ _ _ _ _ hsc).symm ≪≫ (pullbackFunctor f).mapIso (unitTensorIso X.toRingedSpace L)
  let φ₃ := (@asIso _ _ _ _ _ hiso) ≪≫ (pushforwardFunctor f).mapIso ψi
  refine ⟨φ₃, ?_⟩
  have h1 : F.map (Stacks.IdealSheafSequence.divisorQuotientMap D) ≫ projectionFormulaMap' f
      (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace)) L =
      (pullbackAdjunction f).unit.app
        (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩))).obj
          (SheafOfModules.unit (structureRingSheaf X.toRingedSpace), L)) ≫
      (pushforwardFunctor f).map (structureComparison f L) := by
    rw [← hcomp]
    simp only [F, unitHom_eq, Functor.uncurry_obj_map, Prod.mkHom]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have h2 := (pullbackAdjunction f).unit.naturality (unitTensorIso X.toRingedSpace L).hom
  have hφ : φ₃.hom = projectionFormulaMap' f
      (SheafOfModules.unit (structureRingSheaf D.subscheme.toRingedSpace)) L ≫
      (pushforwardFunctor f).map ((@asIso _ _ _ _ _ hsc).inv ≫
        (pullbackFunctor f).map (unitTensorIso X.toRingedSpace L).hom) := rfl
  change F.map (Stacks.IdealSheafSequence.divisorQuotientMap D) ≫ φ₃.hom = _
  rw [hφ]
  erw [← Category.assoc, h1, Category.assoc, ← CategoryTheory.Functor.map_comp]
  erw [asIso_inv, IsIso.hom_inv_id_assoc]
  exact h2.symm

/-- In a short exact sequence whose kernel has no `H¹`, global sections of the middle term surject
onto those of the cokernel. -/
private theorem surjective_app_top_of_subsingleton {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : Subsingleton (cohomologyOverField k f S.X₁ 1)) :
    Function.Surjective (S.g.app ⊤) := by
  obtain ⟨d, -, -, hgd, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  intro y
  obtain ⟨a, ha⟩ := (hgd 0 ((cohomologyOverFieldZeroEquivSections k f S.X₃).symm y)).1
    (Subsingleton.elim _ _)
  refine ⟨cohomologyOverFieldZeroEquivSections k f S.X₂ a, ?_⟩
  rw [← cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap, ha, Equiv.apply_symm_apply]

/-- `surjective_app_top_of_subsingleton` after applying an autoequivalence. -/
private theorem surjective_app_top_map_of_shortExact {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules ⥤ X.Modules) [F.IsEquivalence]
    [F.PreservesZeroMorphisms] {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C) (w : a ≫ b = 0)
    (hS : (ShortComplex.mk a b w).ShortExact)
    (h : Subsingleton (cohomologyOverField k f (F.obj A) 1)) :
    Function.Surjective ((F.map b).app ⊤) :=
  surjective_app_top_of_subsingleton f (hS.map_of_exact F) h

/-- The restriction of sections along a closed immersion, on global sections. -/
private theorem pushforwardSectionComparison_app_top' {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules)
    (z : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    (Stacks.Algebraization.pushforwardSectionComparison a b hw M).app ⊤ z =
      ((Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Scheme.Modules.pullbackCongr hw).hom.app M).app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          ((Scheme.Modules.pullback b).obj M)).app ⊤ z) := by
  simp only [Stacks.Algebraization.pushforwardSectionComparison, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  have h : ∀ {U : A.Opens} (i : U ⟶ U) (x : Γ((Scheme.Modules.pullback c).obj M, U)),
      ((Scheme.Modules.pullback c).obj M).presheaf.map i.op x = x := by
    intro U i x
    rw [Subsingleton.elim i (𝟙 U), op_id, CategoryTheory.Functor.map_id]
    rfl
  exact h _ _

/-- The nonvanishing locus of the restriction of a section is the preimage of its nonvanishing
locus. -/
private theorem nonvanishingLocus_pushforwardSectionComparison {A B C : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules)
    (z : Γ((Scheme.Modules.pullback b).obj M, ⊤)) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback c).obj M)
        ((Stacks.Algebraization.pushforwardSectionComparison a b hw M).app ⊤ z) =
      a.base ⁻¹' Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback b).obj M) z := by
  subst hw
  refine Eq.trans (congrArg (Stacks.Ample.nonvanishingLocus
    ((Scheme.Modules.pullback (a ≫ b)).obj M))
    (pushforwardSectionComparison_app_top' a b rfl M z)) ?_
  refine (Stacks.Ample.nonvanishingLocus_congr
    ((Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr rfl).app M)
    _).trans ?_
  exact (Stacks.NonvanishingPullback.preimage_nonvanishingLocus a _ z).symm

/-- The zero section vanishes everywhere. -/
private theorem notMem_nonvanishingLocus_zero {X : Scheme.{u}} (M : X.Modules) (x : X) :
    x ∉ Stacks.Ample.nonvanishingLocus M 0 := by
  rw [Stacks.Ample.mem_nonvanishingLocus_iff, not_not, map_zero]
  exact zero_mem _

/-- An invertible module with a nowhere vanishing global section is trivial. -/
private theorem nonempty_iso_unit_of_nonvanishingLocus_eq_univ {X : Scheme.{u}} (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] (t : Γ(M, ⊤))
    (ht : Stacks.Ample.nonvanishingLocus M t = Set.univ) :
    Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) := by
  have hLag' : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property M := ‹_›
  have hiso := AlgebraicGeometry.isIso_unitHomEquiv_symm_of_nonvanishingLocus_eq_univ M
    ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm t)
    ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X M t).trans ht)
  exact ⟨(asIso (M.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm
    t))).symm⟩

/-- Vanishing of cohomology transports along isomorphisms. -/
private theorem subsingleton_cohomologyOverField_of_iso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {F G : X.Modules} (e : F ≅ G) (n : ℕ)
    (h : Subsingleton (cohomologyOverField k f G n)) :
    Subsingleton (cohomologyOverField k f F n) := by
  let e' : cohomologyOverField k f F n ≅ cohomologyOverField k f G n :=
    (ModuleCat.restrictScalars _).mapIso
      (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).rightDerived
        n).mapIso e)
  exact e'.toLinearEquiv.toEquiv.subsingleton

/-- Tensoring with an invertible module is an equivalence. -/
private theorem isEquivalence_tensorRight {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : (tensorRight L).IsEquivalence :=
  (Stacks.SheafOfModules.Invertible.isInvertible_iff_tensorRightFunctor_isEquivalence
    X.presheaf X.ringCatSheaf.2 L).1 ‹_›

open Stacks.ProjectionFormula Stacks.RingedSpace RingedSpaceModuleAdjunction in
/-- Under `exists_tensor_pushforward_iso`, the restriction `L|_J ⟶ L|_D` is `L ⊗ (𝒪_J ⟶ 𝒪_D)`. -/
private theorem comp_pushforwardSectionComparison_eq {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {J D : X.IdealSheafData}
    (hsub : J ≤ D)
    (φJ : (tensorRight L).obj (Scheme.IdealSheafData.closedSubschemeStructureSheaf J) ≅
        (Scheme.Modules.pushforward J.subschemeι).obj
          ((Scheme.Modules.pullback J.subschemeι).obj L))
    (hφJ : (tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme J) ≫ φJ.hom =
        (unitTensorIso X.toRingedSpace L).hom ≫
          (Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app L)
    (φD : (tensorRight L).obj (Scheme.IdealSheafData.closedSubschemeStructureSheaf D) ≅
        (Scheme.Modules.pushforward D.subschemeι).obj
          ((Scheme.Modules.pullback D.subschemeι).obj L))
    (hφD : (tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme D) ≫ φD.hom =
        (unitTensorIso X.toRingedSpace L).hom ≫
          (Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app L) :
    φJ.hom ≫ Stacks.Algebraization.pushforwardSectionComparison
      (Scheme.IdealSheafData.inclusion hsub) J.subschemeι
      (Scheme.IdealSheafData.inclusion_subschemeι hsub) L =
      (tensorRight L).map (Scheme.IdealSheafData.closedSubschemeRestriction hsub) ≫ φD.hom := by
  have := isEquivalence_tensorRight L
  have : Epi ((tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme J)) := by
    have := Scheme.IdealSheafData.ambientToClosedSubscheme_epi J
    exact (tensorRight L).map_epi _
  refine (cancel_epi ((tensorRight L).map
    (Scheme.IdealSheafData.ambientToClosedSubscheme J))).1 ?_
  let lam : (tensorRight L).obj (Scheme.IdealSheafData.ambientStructureSheaf X) ⟶ L :=
    (unitTensorIso X.toRingedSpace L).hom
  calc (tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme J) ≫ φJ.hom ≫
        Stacks.Algebraization.pushforwardSectionComparison
          (Scheme.IdealSheafData.inclusion hsub) J.subschemeι
          (Scheme.IdealSheafData.inclusion_subschemeι hsub) L
      = ((tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme J) ≫ φJ.hom) ≫
        Stacks.Algebraization.pushforwardSectionComparison
          (Scheme.IdealSheafData.inclusion hsub) J.subschemeι
          (Scheme.IdealSheafData.inclusion_subschemeι hsub) L := (Category.assoc _ _ _).symm
    _ = lam ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction J.subschemeι).unit.app L ≫
          Stacks.Algebraization.pushforwardSectionComparison
            (Scheme.IdealSheafData.inclusion hsub) J.subschemeι
            (Scheme.IdealSheafData.inclusion_subschemeι hsub) L) :=
        (congrArg (· ≫ Stacks.Algebraization.pushforwardSectionComparison
          (Scheme.IdealSheafData.inclusion hsub) J.subschemeι
          (Scheme.IdealSheafData.inclusion_subschemeι hsub) L) hφJ).trans (Category.assoc _ _ _)
    _ = lam ≫ (Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app L :=
        congrArg (lam ≫ ·)
          (Stacks.Algebraization.unit_comp_pushforwardSectionComparison _ _ _ L)
    _ = (tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme D) ≫ φD.hom := hφD.symm
    _ = (tensorRight L).map (Scheme.IdealSheafData.ambientToClosedSubscheme J ≫
          Scheme.IdealSheafData.closedSubschemeRestriction hsub) ≫ φD.hom := by
        rw [Scheme.IdealSheafData.ambientToClosedSubscheme_comp_closedSubschemeRestriction]
    _ = _ := by rw [Functor.map_comp, Category.assoc]

/-- Surjectivity on global sections transports along a commutative square of isomorphisms. -/
private theorem surjective_app_top_of_comp_eq {X : Scheme.{u}} {A B A' B' : X.Modules} (g : A ⟶ B)
    (p : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B') (h : eA.hom ≫ p = g ≫ eB.hom)
    (hg : Function.Surjective (g.app ⊤)) : Function.Surjective (p.app ⊤) := by
  intro t
  obtain ⟨x, hx⟩ := hg ((eB.inv.app ⊤) t)
  refine ⟨eA.hom.app ⊤ x, ?_⟩
  have h1 : (p.app ⊤) ((eA.hom.app ⊤) x) = (eB.hom.app ⊤) ((g.app ⊤) x) :=
    congrArg (fun q => (q.app ⊤) x) h
  have h2 : (eB.hom.app ⊤) ((eB.inv.app ⊤) t) = t :=
    congrArg (fun q => (q.app ⊤) t) eB.inv_hom_id
  rw [h1, hx, h2]

open Stacks.ProjectionFormula Stacks.RingedSpace RingedSpaceModuleAdjunction in
/-- **Lifting sections.** For `J = C · D` with `D` an effective Cartier divisor, if
`H¹(C, 𝒪_X(-D)|_C ⊗ L|_C) = 0` then `Γ(J, L|_J) ⟶ Γ(D, L|_D)` is surjective. -/
private theorem surjective_restriction_of_subsingleton {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {J D C : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hJ : J = C * D) (hsub : J ≤ D)
    (hH : Subsingleton (cohomologyOverField k (C.subschemeι ≫ s)
      (tens C.subscheme ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Divisors.negativeTwist D)) ((Scheme.Modules.pullback C.subschemeι).obj L)) 1)) :
    Function.Surjective ((Stacks.Algebraization.pushforwardSectionComparison
      (Scheme.IdealSheafData.inclusion hsub) J.subschemeι
      (Scheme.IdealSheafData.inclusion_subschemeι hsub) L).app ⊤) := by
  subst hJ
  have : (tensorRight L).IsEquivalence := isEquivalence_tensorRight L
  have : (tensorRight L).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have hinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureRingSheaf X.toRingedSpace).property L := ‹_›
  have hK : Subsingleton (cohomologyOverField k s ((tensorRight L).obj
      ((Scheme.Modules.pushforward C.subschemeι).obj ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Divisors.negativeTwist D)))) 1) := by
    have hiso := isIso_projectionFormulaMap C.subschemeι.toLRSHom.toShHom
      ((Scheme.Modules.pullback C.subschemeι).obj (Stacks.Divisors.negativeTwist D)) L
    refine subsingleton_cohomologyOverField_of_iso s (@asIso _ _ _ _ _ hiso) 1 ?_
    exact @Equiv.subsingleton _ _
      ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k C.subschemeι s _ 1).symm
        |>.toLinearEquiv.toEquiv) hH
  have hsurj := surjective_app_top_map_of_shortExact s (tensorRight L) _ _ _
    (Stacks.Divisors.shortExact_sumKernelMap D C hD hsub) hK
  obtain ⟨φJ, hφJ⟩ := exists_tensor_pushforward_iso L (C * D)
  obtain ⟨φD, hφD⟩ := exists_tensor_pushforward_iso L D
  have hsq := comp_pushforwardSectionComparison_eq L hsub φJ hφJ φD hφD
  exact surjective_app_top_of_comp_eq _ _ φJ φD hsq hsurj

/-- **[Stacks, Tag 0B40] (4)**: a nonzero global section of an invertible module of degree `≤ 0`
on a proper integral curve vanishes nowhere. -/
private theorem nonvanishingLocus_eq_univ_of_ne_zero {k : Type u} [Field k] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C] (hdim : topologicalKrullDim C ≤ 1)
    (L : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k g hdim L ≤ 0) (t : Γ(L, ⊤)) (ht : t ≠ 0) :
    Stacks.Ample.nonvanishingLocus L t = Set.univ := by
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj
      C.ringCatSheaf.property L := ‹_›
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv C L).symm t
  have hs : s.eval (Opposite.op ⊤) ≠ 0 := by
    rwa [← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  rw [← Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq,
    AlgebraicGeometry.nonvanishingLocus_eq_compl_supportSet_zeroScheme L s hs,
    AlgebraicGeometry.supportSet_zeroScheme_eq_empty_of_invertibleCurveDegree_nonpos k g hdim L s
      hs hdeg, Set.compl_empty]

open Scheme.IdealSheafData in
/-- The structure sheaf of the empty closed subscheme is zero. -/
private theorem isZero_closedSubschemeStructureSheaf_top {X : Scheme.{u}} :
    IsZero (closedSubschemeStructureSheaf (⊤ : X.IdealSheafData)) := by
  rw [IsZero.iff_id_eq_zero]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  exact Subsingleton.elim (α := Γ((⊤ : X.IdealSheafData).subscheme,
    (⊤ : X.IdealSheafData).subschemeι ⁻¹ᵁ U)) _ _

open Scheme.IdealSheafData in
/-- The structure sheaf of a disjoint union is the direct sum of the two structure sheaves. -/
private theorem isIso_unionToBiprod {X : Scheme.{u}} (I J : X.IdealSheafData) (hIJ : I ⊔ J = ⊤) :
    IsIso (unionToBiprod I J) := by
  obtain ⟨hz, hS⟩ := unionIntersection_shortExact I J
  have : Mono (unionToBiprod I J) := unionToBiprod_mono I J
  have hZ : IsZero (closedSubschemeStructureSheaf (I ⊔ J)) := by
    rw [hIJ]; exact isZero_closedSubschemeStructureSheaf_top
  have : Epi (unionToBiprod I J) := hS.exact.epi_f (hZ.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi (unionToBiprod I J)

/-- For coprime ideal sheaves the intersection is contained in the product. -/
private theorem inf_le_mul_of_sup_eq_top {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I ⊔ J = ⊤) :
    I ⊓ J ≤ I * J := fun U => by
  have hU : I.ideal U ⊔ J.ideal U = ⊤ :=
    congrFun (congrArg Scheme.IdealSheafData.ideal h) U
  exact (Ideal.mul_eq_inf_of_coprime hU).ge

/-- Ideal sheaves with disjoint supports are coprime. -/
private theorem sup_eq_top_of_disjoint {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : Disjoint (I.support : Set X) J.support) : I ⊔ J = ⊤ := by
  refine (Scheme.IdealSheafData.support_eq_bot_iff _).1 (eq_bot_iff.2 fun x hx => ?_)
  exact (Set.disjoint_left.1 h (Scheme.IdealSheafData.support_antitone le_sup_left hx)
    (Scheme.IdealSheafData.support_antitone le_sup_right hx)).elim

/-- A point of `J` lying over the support of `I ≥ J` comes from the closed subscheme of `I`. -/
private theorem mem_range_inclusion {X : Scheme.{u}} {J I : X.IdealSheafData} (h : J ≤ I)
    (z : J.subscheme) (hz : J.subschemeι z ∈ (I.support : Set X)) :
    z ∈ Set.range (Scheme.IdealSheafData.inclusion h).base := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hz
  obtain ⟨r, hr⟩ := hz
  refine ⟨r, J.subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hr]

/-- A section of `L|_J` vanishes nowhere when its restrictions to two closed subschemes covering
`J` vanish nowhere. -/
private theorem nonvanishingLocus_eq_univ_of_cover {X : Scheme.{u}} (L : X.Modules)
    {J I₁ I₂ : X.IdealSheafData} (h₁ : J ≤ I₁) (h₂ : J ≤ I₂)
    (hJ : (J.support : Set X) ⊆ I₁.support ∪ I₂.support)
    (s : Γ((Scheme.Modules.pullback J.subschemeι).obj L, ⊤))
    (hs₁ : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback I₁.subschemeι).obj L)
      ((Stacks.Algebraization.pushforwardSectionComparison (Scheme.IdealSheafData.inclusion h₁)
        J.subschemeι (Scheme.IdealSheafData.inclusion_subschemeι h₁) L).app ⊤ s) = Set.univ)
    (hs₂ : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback I₂.subschemeι).obj L)
      ((Stacks.Algebraization.pushforwardSectionComparison (Scheme.IdealSheafData.inclusion h₂)
        J.subschemeι (Scheme.IdealSheafData.inclusion_subschemeι h₂) L).app ⊤ s) = Set.univ) :
    Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback J.subschemeι).obj L) s =
      Set.univ := by
  rw [nonvanishingLocus_pushforwardSectionComparison] at hs₁ hs₂
  refine Set.eq_univ_of_forall fun z => ?_
  have hz : J.subschemeι z ∈ (J.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
  rcases hJ hz with h | h
  · obtain ⟨r, rfl⟩ := mem_range_inclusion h₁ z h
    exact (Set.eq_univ_iff_forall.1 hs₁ r :)
  · obtain ⟨r, rfl⟩ := mem_range_inclusion h₂ z h
    exact (Set.eq_univ_iff_forall.1 hs₂ r :)

open Scheme.IdealSheafData in
/-- **Gluing on a disjoint union**: for coprime `I`, `J`, sections of `L|_I` and `L|_J` come from
one section of `L|_{I ⊓ J}`. -/
private theorem exists_pushforwardSectionComparison_eq_and_eq {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (I J : X.IdealSheafData)
    (hIJ : I ⊔ J = ⊤)
    (t₁ : Γ((Scheme.Modules.pullback I.subschemeι).obj L, ⊤))
    (t₂ : Γ((Scheme.Modules.pullback J.subschemeι).obj L, ⊤)) :
    ∃ s : Γ((Scheme.Modules.pullback (I ⊓ J).subschemeι).obj L, ⊤),
      (Stacks.Algebraization.pushforwardSectionComparison (inclusion (inf_le_left : I ⊓ J ≤ I))
        (I ⊓ J).subschemeι (inclusion_subschemeι _) L).app ⊤ s = t₁ ∧
      (Stacks.Algebraization.pushforwardSectionComparison (inclusion (inf_le_right : I ⊓ J ≤ J))
        (I ⊓ J).subschemeι (inclusion_subschemeι _) L).app ⊤ s = t₂ := by
  have : (tensorRight L).IsEquivalence := isEquivalence_tensorRight L
  have : (tensorRight L).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have hβ := isIso_unionToBiprod I J hIJ
  obtain ⟨φK, hφK⟩ := exists_tensor_pushforward_iso L (I ⊓ J)
  obtain ⟨φ₁, hφ₁⟩ := exists_tensor_pushforward_iso L I
  obtain ⟨φ₂, hφ₂⟩ := exists_tensor_pushforward_iso L J
  have hsq₁ := comp_pushforwardSectionComparison_eq L (inf_le_left : I ⊓ J ≤ I) φK hφK φ₁ hφ₁
  have hsq₂ := comp_pushforwardSectionComparison_eq L (inf_le_right : I ⊓ J ≤ J) φK hφK φ₂ hφ₂
  let e := (tensorRight L).mapIso (asIso (unionToBiprod I J))
  let y := ((tensorRight L).map biprod.inl).app ⊤ (φ₁.inv.app ⊤ t₁) +
    ((tensorRight L).map biprod.inr).app ⊤ (φ₂.inv.app ⊤ t₂)
  have hey : ((tensorRight L).map (unionToBiprod I J)).app ⊤ (e.inv.app ⊤ y) = y := by
    rw [← comp_app_apply]
    change (e.inv ≫ e.hom).app ⊤ y = y
    rw [e.inv_hom_id]
    rfl
  refine ⟨φK.hom.app ⊤ (e.inv.app ⊤ y), ?_, ?_⟩
  · rw [← comp_app_apply, hsq₁, comp_app_apply,
      show closedSubschemeRestriction (inf_le_left : I ⊓ J ≤ I) =
        unionToBiprod I J ≫ biprod.fst from (biprod.lift_fst _ _).symm,
      Functor.map_comp, comp_app_apply, hey, map_add, ← comp_app_apply, ← comp_app_apply,
      ← Functor.map_comp, ← Functor.map_comp, biprod.inl_fst, biprod.inr_fst,
      CategoryTheory.Functor.map_id,
      Functor.map_zero, app_apply_of_eq_zero rfl, add_zero, ← comp_app_apply]
    change ((φ₁.inv ≫ φ₁.hom)).app ⊤ t₁ = t₁
    rw [φ₁.inv_hom_id]
    rfl
  · rw [← comp_app_apply, hsq₂, comp_app_apply,
      show closedSubschemeRestriction (inf_le_right : I ⊓ J ≤ J) =
        unionToBiprod I J ≫ biprod.snd from (biprod.lift_snd _ _).symm,
      Functor.map_comp, comp_app_apply, hey, map_add, ← comp_app_apply, ← comp_app_apply,
      ← Functor.map_comp, ← Functor.map_comp, biprod.inl_snd, biprod.inr_snd,
      CategoryTheory.Functor.map_id,
      Functor.map_zero, app_apply_of_eq_zero rfl, zero_add, ← comp_app_apply]
    change ((φ₂.inv ≫ φ₂.hom)).app ⊤ t₂ = t₂
    rw [φ₂.inv_hom_id]
    rfl

/-! ### Nowhere vanishing sections on the components and on the cycles -/

/-- **A degree-zero invertible module on a proper integral curve with `χ(𝒪) = 1` has a nowhere
vanishing global section**: `h⁰(L) ≥ χ(L) = deg L + χ(𝒪) = 1`, and a nonzero global section of
an invertible module of degree zero vanishes nowhere. -/
private theorem exists_nonvanishingLocus_eq_univ_of_invertibleCurveDegree_eq_zero
    {C : Scheme.{u}} (g : C ⟶ Spec (.of k)) [IsProper g] [IsIntegral C]
    (hdim : topologicalKrullDim C ≤ 1)
    (hχ : @eulerCharacteristic k _ _ g _ (SheafOfModules.unit C.ringCatSheaf)
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g) = 1)
    (L : C.Modules) [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L]
    (hdeg : invertibleCurveDegree k g hdim L = 0) :
    ∃ t : Γ(L, ⊤), Stacks.Ample.nonvanishingLocus L t = Set.univ := by
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k g L 1
  have h1 := invertibleCurveDegree_eq_eulerCharacteristic_sub k g hdim L
  have h2 := eulerCharacteristic_eq_finrank_sub g hdim L
  have : Nontrivial (cohomologyOverField k g L 0) :=
    Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨a, ha⟩ := exists_ne (0 : cohomologyOverField k g L 0)
  refine ⟨cohomologyOverFieldZeroEquivSections k g L a,
    nonvanishingLocus_eq_univ_of_ne_zero g hdim L hdeg.le _ fun h0 => ha ?_⟩
  apply (cohomologyOverFieldZeroEquivSections k g L).injective
  rw [h0]
  have h := cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k g (0 : L ⟶ L)
    (0 : cohomologyOverField k g L 0)
  rw [map_zero] at h
  refine (h.trans ?_).symm
  rw [Scheme.Modules.Hom.zero_app]
  rfl

/-- **The kernel of `L|_{W+E} ⟶ L|_W` has no `H¹`** when `L` has degree zero on the genus zero
curve `E` and `(W · E) ≤ 1`, for `W = ∑_{F ∈ m} F`: the kernel is `𝒪_Y(-W)|_E ⊗ L|_E`, of degree
`-(W · E) ≥ -1`. -/
private theorem subsingleton_cohomologyOverField_one_tensor_negativeTwist [IsAlgClosed k]
    {s : Y ⟶ Spec (.of k)} [QuasiCompact s] [IsLocallyNoetherian Y] [IsNormal Y]
    (hsm : IsSmoothScheme s) (m : Multiset (MMP.Mori.PrimeDivisor Y))
    (E : MMP.Mori.PrimeDivisor Y) [IsProper (E.idealSheaf.subschemeι ≫ s)]
    (hd : topologicalKrullDim E.idealSheaf.subscheme = 1)
    (hgE : Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ s)
      (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 1) = 0)
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hLE : MMP.Mori.degreeOn k s E.idealSheaf.subschemeι hd.le L = 0)
    (hle : ¬ 2 ≤ (m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum) :
    haveI := isEffectiveCartierDivisor_cycleIdeal hsm m
    Subsingleton (cohomologyOverField k (E.idealSheaf.subschemeι ≫ s)
      (tens E.idealSheaf.subscheme ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m)))
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L)) 1) := by
  have := isEffectiveCartierDivisor_cycleIdeal hsm m
  have := isInvertible_pullback_negativeTwist (cycleIdeal m) E.idealSheaf
  have := isInvertible_negativeTwist' (cycleIdeal m)
  have := MMP.Mori.isInvertible_pullback_obj E.idealSheaf.subschemeι L
  have : SheafOfModules.IsInvertible E.idealSheaf.subscheme.presheaf
      E.idealSheaf.subscheme.ringCatSheaf.2
      (tens E.idealSheaf.subscheme ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m)))
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L)) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible _ _ _ _
  have : IsIntegral E.idealSheaf.subscheme := E.integral
  have : AlgebraicGeometry.IsCurve k (E.idealSheaf.subschemeι ≫ s) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hd }
  by_contra hns
  have hdeg := invertibleCurveDegree_le_neg_two (E.idealSheaf.subschemeι ≫ s) hgE hd.le _
    fun hz => hns (ModuleCat.subsingleton_of_isZero hz)
  have hC := invertibleCurveDegree_tensorSheaf_eq_add k (E.idealSheaf.subschemeι ≫ s) hd.le
    ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
      (Stacks.Divisors.negativeTwist (cycleIdeal m)))
    ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L)
  have e : (invertibleCurveDegree k (E.idealSheaf.subschemeι ≫ s) hd.le
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m))) : ℚ) =
      -(m.map fun F => ixn s (Divisor.toQDivisor (Finsupp.single F 1)) E).sum :=
    degreeOn_negativeTwist'_cycleIdeal hsm m E hd.le
  have hLE' : invertibleCurveDegree k (E.idealSheaf.subschemeι ≫ s) hd.le
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L) = 0 := hLE
  have h3 : invertibleCurveDegree k (E.idealSheaf.subschemeι ≫ s) hd.le
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m))) ≤ -2 := by
    linarith
  have h4 : (invertibleCurveDegree k (E.idealSheaf.subschemeι ≫ s) hd.le
      ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj
        (Stacks.Divisors.negativeTwist (cycleIdeal m))) : ℚ) ≤ -2 := by
    exact_mod_cast h3
  push Not at hle
  linarith

/-- **The induction step when `E` meets `W`.** Let `J = E · W` with `W` an effective Cartier
divisor, and suppose `H¹(E, 𝒪_X(-W)|_E ⊗ L|_E) = 0`, that `L|_W` has a nowhere vanishing section
and that every nonzero section of `L|_E` vanishes nowhere. If `E` and `W` meet, then `L|_J` has
a nowhere vanishing section: a lift of the section on `W` is nonzero on `E` at a common point. -/
private theorem exists_nonvanishingLocus_eq_univ_mul_of_mem {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (C D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hH : Subsingleton (cohomologyOverField k (C.subschemeι ≫ s)
      (tens C.subscheme ((Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Divisors.negativeTwist D)) ((Scheme.Modules.pullback C.subschemeι).obj L)) 1))
    (tD : Γ((Scheme.Modules.pullback D.subschemeι).obj L, ⊤))
    (htD : Stacks.Ample.nonvanishingLocus _ tD = Set.univ)
    (hC : ∀ t : Γ((Scheme.Modules.pullback C.subschemeι).obj L, ⊤), t ≠ 0 →
      Stacks.Ample.nonvanishingLocus _ t = Set.univ)
    {x : X} (hxC : x ∈ (C.support : Set X)) (hxD : x ∈ (D.support : Set X)) :
    ∃ t : Γ((Scheme.Modules.pullback (C * D).subschemeι).obj L, ⊤),
      Stacks.Ample.nonvanishingLocus _ t = Set.univ := by
  have hsubD : C * D ≤ D := Scheme.IdealSheafData.mul_le_right C D
  have hsubC : C * D ≤ C := Scheme.IdealSheafData.mul_le_left C D
  obtain ⟨t, ht⟩ := surjective_restriction_of_subsingleton s L hD rfl hsubD hH tD
  have hsD : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback D.subschemeι).obj L)
      ((Stacks.Algebraization.pushforwardSectionComparison (Scheme.IdealSheafData.inclusion hsubD)
        (C * D).subschemeι (Scheme.IdealSheafData.inclusion_subschemeι hsubD) L).app ⊤ t) =
        Set.univ := by
    rwa [ht]
  have hpre := (nonvanishingLocus_pushforwardSectionComparison
    (Scheme.IdealSheafData.inclusion hsubD) (C * D).subschemeι
    (Scheme.IdealSheafData.inclusion_subschemeι hsubD) L t).symm.trans hsD
  refine ⟨t, nonvanishingLocus_eq_univ_of_cover L hsubC hsubD ?_ t (hC _ ?_) hsD⟩
  · intro y hy
    rwa [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup] at hy
  · intro h0
    rw [← Scheme.IdealSheafData.range_subschemeι] at hxC
    obtain ⟨zC, hzC⟩ := hxC
    have hz : (C * D).subschemeι ((Scheme.IdealSheafData.inclusion hsubC).base zC) ∈
        (D.support : Set X) := by
      rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι, hzC]
      exact hxD
    obtain ⟨r, hr⟩ := mem_range_inclusion hsubD _ hz
    have h1 : (Scheme.IdealSheafData.inclusion hsubC).base zC ∈
        Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback (C * D).subschemeι).obj L) t := by
      rw [← hr]
      exact (Set.eq_univ_iff_forall.1 hpre r :)
    have h2 := nonvanishingLocus_pushforwardSectionComparison
      (Scheme.IdealSheafData.inclusion hsubC) (C * D).subschemeι
      (Scheme.IdealSheafData.inclusion_subschemeι hsubC) L t
    rw [h0] at h2
    have h3 : zC ∈ Stacks.Ample.nonvanishingLocus
        ((Scheme.Modules.pullback C.subschemeι).obj L) 0 := by
      rwa [h2]
    exact notMem_nonvanishingLocus_zero _ _ h3

/-- **The induction step when `E` and `W` are disjoint**: for coprime `C`, `D`, nowhere vanishing
sections of `L|_C` and `L|_D` glue to a nowhere vanishing section of `L|_{C ⊓ D}`. -/
private theorem exists_nonvanishingLocus_eq_univ_inf {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (C D : X.IdealSheafData)
    (hCD : C ⊔ D = ⊤) (tC : Γ((Scheme.Modules.pullback C.subschemeι).obj L, ⊤))
    (htC : Stacks.Ample.nonvanishingLocus _ tC = Set.univ)
    (tD : Γ((Scheme.Modules.pullback D.subschemeι).obj L, ⊤))
    (htD : Stacks.Ample.nonvanishingLocus _ tD = Set.univ) :
    ∃ t : Γ((Scheme.Modules.pullback (C ⊓ D).subschemeι).obj L, ⊤),
      Stacks.Ample.nonvanishingLocus _ t = Set.univ := by
  obtain ⟨t, h1, h2⟩ := exists_pushforwardSectionComparison_eq_and_eq L C D hCD tC tD
  refine ⟨t, nonvanishingLocus_eq_univ_of_cover L inf_le_left inf_le_right ?_ t
    (by rwa [h1]) (by rwa [h2])⟩
  intro y hy
  have := Scheme.IdealSheafData.support_antitone
    (le_inf (Scheme.IdealSheafData.mul_le_left C D) (Scheme.IdealSheafData.mul_le_right C D)) hy
  rw [Scheme.IdealSheafData.support_mul] at this
  exact this

/-- **Degree-zero invertible sheaves are trivial on rational exceptional cycles.** Let
`f : Y ⟶ X` resolve a normal surface germ `(X, P)` over an algebraically closed field `k`, and
let `Z = ∑ nᵢ Eᵢ` be an effective divisor supported on the exceptional curves of `f` such that
`χ(Z', 𝒪_{Z'}) > 0` for every nonzero effective divisor `Z' ≤ Z`. If `L` is an invertible sheaf
on `Y` of degree `0` on every component `Eᵢ` of `Z`, then the restriction of `L` to the closed
subscheme of `Y` with ideal `∏ I_{Eᵢ}^{nᵢ}` is isomorphic to its structure sheaf. -/
@[mmp "lem_mmp_foundation_rational_exceptional_cycle_line_bundle_trivial"]
public theorem IsGermResolution.nonempty_pullback_divisorIdeal_iso_unit {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {f : Y ⟶ X}
    (hf : IsGermResolution sX P f) {Z : Divisor Y} (hZ : 0 ≤ Z)
    (hZE : ∀ C ∈ Z.support, IsGermExceptionalCurve f P C)
    (hχ : ∀ Z' : Divisor Y, 0 ≤ Z' → Z' ≤ Z → Z' ≠ 0 →
      ∀ _ : IsProper ((MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subschemeι ≫ f ≫ sX),
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          ((MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subschemeι ≫ f ≫ sX)
        0 < eulerCharacteristic k
          ((MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit
            (MMP.Resolution.divisorIdeal fun C => (Z' C).toNat).subscheme.ringCatSheaf))
    (L : Y.Modules) [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : ∀ C ∈ Z.support, ∀ (_ : IsProper (C.idealSheaf.subschemeι ≫ f ≫ sX))
      (hdim : topologicalKrullDim C.idealSheaf.subscheme ≤ 1),
        degreeOn k (f ≫ sX) C.idealSheaf.subschemeι hdim L = 0) :
    Nonempty ((Scheme.Modules.pullback
        (MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subschemeι).obj L ≅
      SheafOfModules.unit
        (MMP.Resolution.divisorIdeal fun C => (Z C).toNat).subscheme.ringCatSheaf) := by
  classical
  have : QuasiCompact (f ≫ sX) := hf.quasiCompact_comp
  have : IsNormal Y := hf.isSmoothResolution.isNormal
  have hY : MMP.Mori.IsVariety k (f ≫ sX) := hf.isVariety
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY
  have : LocallyOfFiniteType (f ≫ sX) := hY.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsIntegral Y := hY.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have hsm := hf.isSmoothResolution.isSmoothScheme
  have hd := hf.topologicalKrullDim_eq
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm
    (n := 2) hd
  -- the cycle `Z` as a multiset of prime divisors
  obtain ⟨m, hZm, hmZ⟩ := exists_eq_cycleDivisor Z hZ
  have hmem : ∀ E ∈ m, E ∈ Z.support := fun E hE => (hmZ E).1 hE
  have hexc : ∀ E ∈ m, IsGermExceptionalCurve f P E := fun E hE => hZE E (hmem E hE)
  have hmE : ∀ E ∈ m, IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX) ∧
      topologicalKrullDim E.idealSheaf.subscheme ≤ 1 := fun E hE => by
    obtain ⟨h1, h2⟩ := (hexc E hE).isProper sX hf
    exact ⟨h2, h1.2.le⟩
  have hprop : ∀ m' ≤ m, IsProper ((cycleIdeal m').subschemeι ≫ f ≫ sX) := fun m' hm' =>
    isProper_cycleIdeal hf fun E hE => hexc E (Multiset.mem_of_le hm' hE)
  -- the positivity hypothesis for subcycles given as multisets
  have hχm : ∀ m' ≤ m, m' ≠ 0 → ∀ hp : IsProper ((cycleIdeal m').subschemeι ≫ f ≫ sX),
      haveI := hp
      haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
        ((cycleIdeal m').subschemeι ≫ f ≫ sX)
      0 < eulerCharacteristic k ((cycleIdeal m').subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit (cycleIdeal m').subscheme.ringCatSheaf) := by
    intro m' hm' hm0'
    have h := hχ (cycleDivisor m') (cycleDivisor_nonneg m')
      (fun C => by
        rw [hZm, cycleDivisor_apply, cycleDivisor_apply]
        exact_mod_cast Multiset.count_le_of_le C hm')
      (fun h0 => hm0' (Multiset.ext.2 fun C => by
        have := DFunLike.congr_fun h0 C
        rw [cycleDivisor_apply] at this
        simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_eq_zero] at this
        rw [this, Multiset.count_zero]))
    rw [divisorIdeal_cycleDivisor] at h
    exact h
  -- the components: `h¹(𝒪_E) = 0` and `χ(𝒪_E) = 1`
  have hcomp : ∀ E ∈ m,
      Module.finrank k (cohomologyOverField k (E.idealSheaf.subschemeι ≫ f ≫ sX)
        (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) 1) = 0 ∧
      ∀ hp : IsProper (E.idealSheaf.subschemeι ≫ f ≫ sX),
        haveI := hp
        haveI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
          (E.idealSheaf.subschemeι ≫ f ≫ sX)
        eulerCharacteristic k (E.idealSheaf.subschemeι ≫ f ≫ sX)
          (SheafOfModules.unit E.idealSheaf.subscheme.ringCatSheaf) = 1 := by
    intro E hE
    obtain ⟨hEp, hEd⟩ := hmE E hE
    have := hEp
    have : IsIntegral E.idealSheaf.subscheme := E.integral
    have h1 := hχm {E} (Multiset.singleton_le.2 hE) (Multiset.singleton_ne_zero E)
    rw [show cycleIdeal {E} = E.idealSheaf by simp [cycleIdeal]] at h1
    have h2 := h1 hEp
    have h3 := eulerCharacteristic_unit_eq_one_sub (E.idealSheaf.subschemeι ≫ f ≫ sX) hEd
    refine ⟨by omega, fun _ => by omega⟩
  -- the components: nowhere vanishing sections of `L|_E`
  have hcurve : ∀ E ∈ m,
      (∃ t : Γ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L, ⊤),
        Stacks.Ample.nonvanishingLocus _ t = Set.univ) ∧
      ∀ t : Γ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L, ⊤), t ≠ 0 →
        Stacks.Ample.nonvanishingLocus _ t = Set.univ := by
    intro E hE
    obtain ⟨hEp, hEd⟩ := hmE E hE
    have := hEp
    have : IsIntegral E.idealSheaf.subscheme := E.integral
    have := MMP.Mori.isInvertible_pullback_obj E.idealSheaf.subschemeι L
    have hdeg : invertibleCurveDegree k (E.idealSheaf.subschemeι ≫ f ≫ sX) hEd
        ((Scheme.Modules.pullback E.idealSheaf.subschemeι).obj L) = 0 :=
      hL E (hmem E hE) hEp hEd
    exact ⟨exists_nonvanishingLocus_eq_univ_of_invertibleCurveDegree_eq_zero _ hEd
      ((hcomp E hE).2 hEp) _ hdeg,
      fun t ht => nonvanishingLocus_eq_univ_of_ne_zero _ hEd _ hdeg.le t ht⟩
  -- the induction on the size of the cycle
  have key : ∀ n : ℕ, ∀ m' : Multiset (MMP.Mori.PrimeDivisor Y), m' ≤ m →
      Multiset.card m' = n → m' ≠ 0 →
      ∃ t : Γ((Scheme.Modules.pullback (cycleIdeal m').subschemeι).obj L, ⊤),
        Stacks.Ample.nonvanishingLocus _ t = Set.univ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro m' hm' hcard hm0'
    -- a component meeting the rest of the cycle at most once
    obtain ⟨E, hE, hle⟩ := exists_mem_not_two_le_sum_ixn hY hsm hd hK m' hm0'
      (fun E hE => hmE E (Multiset.mem_of_le hm' hE)) (fun m'' h => hprop m'' (h.trans hm'))
      (fun E hE => (hcomp E (Multiset.mem_of_le hm' hE)).2) (hχm m' hm' hm0' _)
    have hEm : E ∈ m := Multiset.mem_of_le hm' hE
    obtain ⟨hEp, hEd⟩ := hmE E hEm
    have := hEp
    have hm'eq : m' = E ::ₘ m'.erase E := (Multiset.cons_erase hE).symm
    rw [hm'eq, cycleIdeal_cons]
    by_cases hW : m'.erase E = 0
    · rw [hW, cycleIdeal_zero, Scheme.IdealSheafData.mul_top]
      exact (hcurve E hEm).1
    have hWcard : Multiset.card (m'.erase E) < n := by
      rw [← hcard, Multiset.card_erase_of_mem hE]
      exact Nat.pred_lt (Multiset.card_pos.2 hm0').ne'
    obtain ⟨tW, htW⟩ := ih _ hWcard (m'.erase E) ((Multiset.erase_le E m').trans hm') rfl hW
    by_cases hmeet : ∃ x, x ∈ (E.idealSheaf.support : Set Y) ∧
        x ∈ ((cycleIdeal (m'.erase E)).support : Set Y)
    · -- `E` meets `W`: lift the section on `W`
      obtain ⟨x, hxE, hxW⟩ := hmeet
      have hd1 : topologicalKrullDim E.idealSheaf.subscheme = 1 :=
        ((hexc E hEm).isProper sX hf).1.2
      exact exists_nonvanishingLocus_eq_univ_mul_of_mem (f ≫ sX) L E.idealSheaf
        (cycleIdeal (m'.erase E)) (isEffectiveCartierDivisor_cycleIdeal hsm (m'.erase E))
        (subsingleton_cohomologyOverField_one_tensor_negativeTwist hsm (m'.erase E) E hd1
          (hcomp E hEm).1 L (hL E (hmem E hEm) hEp hd1.le) hle)
        tW htW (hcurve E hEm).2 hxE hxW
    · -- `E` and `W` are disjoint: glue
      push Not at hmeet
      have hcop : E.idealSheaf ⊔ cycleIdeal (m'.erase E) = ⊤ :=
        sup_eq_top_of_disjoint (Set.disjoint_left.2 fun x hxE hxW => hmeet x hxE hxW)
      rw [show E.idealSheaf * cycleIdeal (m'.erase E) = E.idealSheaf ⊓ cycleIdeal (m'.erase E) from
        le_antisymm (le_inf (Scheme.IdealSheafData.mul_le_left _ _)
          (Scheme.IdealSheafData.mul_le_right _ _)) (inf_le_mul_of_sup_eq_top hcop)]
      obtain ⟨tE, htE⟩ := (hcurve E hEm).1
      exact exists_nonvanishingLocus_eq_univ_inf L _ _ hcop tE htE tW htW
  have hdiv : MMP.Resolution.divisorIdeal (fun C => (Z C).toNat) = cycleIdeal m := by
    rw [hZm]; exact divisorIdeal_cycleDivisor m
  rw [hdiv]
  have := MMP.Mori.isInvertible_pullback_obj (cycleIdeal m).subschemeι L
  by_cases hm0 : m = 0
  · -- the empty cycle: the subscheme is empty
    refine nonempty_iso_unit_of_nonvanishingLocus_eq_univ _ 0
      (Set.eq_univ_of_forall fun z => ?_)
    exfalso
    have hz : (cycleIdeal m).subschemeι z ∈ ((cycleIdeal m).support : Set Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    have h0 : ((cycleIdeal m).support : Set Y) = ∅ := by
      rw [hm0, cycleIdeal_zero, Scheme.IdealSheafData.support_top,
        TopologicalSpace.Closeds.coe_bot]
    rw [h0] at hz
    exact hz
  obtain ⟨t, ht⟩ := key _ m le_rfl rfl hm0
  exact nonempty_iso_unit_of_nonvanishingLocus_eq_univ _ t ht

end LineBundle

end MMP.Flips

end
