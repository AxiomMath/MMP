module

public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenModel
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# Reflexive powers on the locally free locus, and pull-back of Picard groups

Let `X` be a normal variety over a field `k` and `L` a coherent torsion-free sheaf of rank one
on `X`, with locally free locus `X⁰ = MMP.Mori.locallyFreeLocus L`. On `X⁰` the reflexive
powers `L^{[i]} = MMP.Mori.reflexivePow L i` are the ordinary integral tensor powers of the
invertible sheaf `L|_{X⁰}`: `L^{[i]}|_{X⁰} ≅ (L|_{X⁰})^{⊗ i}` for every `i ∈ ℤ`, a negative
power being the corresponding tensor power of the dual.

The proof: on `X⁰` the sheaf `L` is invertible, so every tensor power of `L|_{X⁰}` is
invertible, hence reflexive, and the canonical map `L^{⊗ n} → (L^{⊗ n})^{**}` restricts to an
isomorphism on `X⁰`. Since restriction to an open commutes with tensor products, this gives
`L^{[n]}|_{X⁰} ≅ (L|_{X⁰})^{⊗ n}` for `n ≥ 0`. For `n > 0`, restriction also commutes with the
dual, so `L^{[-n]}|_{X⁰}` is the dual of the invertible sheaf `(L|_{X⁰})^{⊗ n}`. That dual is a
tensor inverse of `(L|_{X⁰})^{⊗ n}`, and so is `((L|_{X⁰})^∨)^{⊗ n}`, and two tensor inverses
of an invertible sheaf are isomorphic. If `X⁰` is empty, any two modules on it are isomorphic.

## Main results

* `MMP.Mori.nonempty_restrict_reflexivePow_iso_tensorZPow`: `L^{[i]}|_{X⁰} ≅ (L|_{X⁰})^{⊗ i}`.

## Implementation notes

Restriction to `X⁰` is `AlgebraicGeometry.Scheme.Modules.restrictFunctor` along the open
immersion of `X⁰`, and the integral tensor power is
`MMP.Intersection.Scheme.Modules.tensorZPow`, which for `i < 0` is the `(-i)`-th tensor power
of the dual. Torsion-freeness is `Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree`
and rank one is the fibre rank `AlgebraicGeometry.Scheme.Modules.fiberRank` at the generic
point being `1`. The isomorphism is asserted to exist, as in the source.

Restriction to an open `V` commutes with the dual `𝓗om(-, 𝒪)`: passing through the slice-site
model of modules on `V` (`AlgebraicGeometry.Scheme.Modules.overEquiv`), this is
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafOverIso` followed by the transport of
internal Hom `Stacks.SheafOfModules.internalHomSchemeOpenIso`. That `L|_{X⁰}` is invertible
comes from its being locally free of finite type, with fibre rank locally constant, hence
constant on the irreducible scheme `X⁰`, equal to the generic rank `1`.

Injectivity of `g^* : Pic(Z) → Pic(X)` for a contraction (`lem_km3b_pic_pullback_injective`) is
the Stacks project's `AlgebraicGeometry.Scheme.Modules.injective_schemePullbackClass_of_isIso_c`;
it is not restated here.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.52, Cor. 3.17
-/

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace MMP.Mori

section ReflexivePow

variable {Y : Scheme.{u}}

local notation "TP" => Stacks.AlgebraicGeometry.ReflexivePowers.tensorPower

/-- The braiding of the sheaf tensor product. -/
private noncomputable def braid (A B : Y.Modules) : A ⊗ B ≅ B ⊗ A :=
  Stacks.SheafOfModules.Strict.braiding Y.presheaf _ A B

/-- The integral tensor power of the project agrees with the Stacks tensor power in degrees
`n ≥ 0`. -/
private noncomputable def tensorPowIsoTensorPower (F : Y.Modules) :
    ∀ n : ℕ, MMP.Intersection.Scheme.Modules.tensorPow F n ≅ TP F n
  | 0 => Iso.refl _
  | 1 => λ_ F
  | n + 2 => whiskerRightIso (tensorPowIsoTensorPower F (n + 1)) F ≪≫ braid _ F

/-- Restriction to an open commutes with the Stacks tensor powers. -/
private noncomputable def restrictTensorPowerIso (V : Y.Opens) (F : Y.Modules) :
    ∀ n : ℕ, (Scheme.Modules.restrictFunctor V.ι).obj (TP F n) ≅
      TP ((Scheme.Modules.restrictFunctor V.ι).obj F) n
  | 0 => Scheme.Modules.restrictUnitIso V.ι
  | 1 => Iso.refl _
  | n + 2 => Stacks.AlgebraicGeometry.ReflexivePowers.tensorSheafRestrictIso V F (TP F (n + 1)) ≪≫
      whiskerLeftIso ((Scheme.Modules.restrictFunctor V.ι).obj F)
        (restrictTensorPowerIso V F (n + 1))

/-- `D^{⊗ n} ⊗ F^{⊗ n} ≅ 𝒪` as soon as `D ⊗ F ≅ 𝒪`. -/
private noncomputable def tensorPowTensorIsoUnit {D F : Y.Modules} (e : D ⊗ F ≅ 𝟙_ Y.Modules) :
    ∀ n : ℕ, MMP.Intersection.Scheme.Modules.tensorPow D n ⊗
      MMP.Intersection.Scheme.Modules.tensorPow F n ≅ 𝟙_ Y.Modules
  | 0 => λ_ _
  | n + 1 =>
      let A := MMP.Intersection.Scheme.Modules.tensorPow D n
      let B := MMP.Intersection.Scheme.Modules.tensorPow F n
      show (A ⊗ D) ⊗ (B ⊗ F) ≅ 𝟙_ Y.Modules from
      α_ A D (B ⊗ F) ≪≫ whiskerLeftIso A ((α_ D B F).symm ≪≫
        whiskerRightIso (braid D B) F ≪≫ α_ B D F ≪≫ whiskerLeftIso B e ≪≫ ρ_ B) ≪≫
        tensorPowTensorIsoUnit e n

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- Restriction to an open commutes with the dual `𝓗om(-, 𝒪)`. -/
private noncomputable def restrictDualSheafIso (V : Y.Opens) (N : Y.Modules) :
    (Scheme.Modules.restrictFunctor V.ι).obj (dualSheaf N) ≅
      dualSheaf ((Scheme.Modules.restrictFunctor V.ι).obj N) :=
  ((Scheme.Modules.overFunctorEquiv V).app (dualSheaf N)).symm ≪≫
    (Scheme.Modules.overEquiv V).functor.mapIso (dualSheafOverIso Y V N) ≪≫
    Stacks.SheafOfModules.internalHomSchemeOpenIso V _ _ ≪≫
    (Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor _ V.toScheme.sheaf
      ((Scheme.Modules.overEquiv V).functor.obj (N.over V))).mapIso
      (Stacks.AlgebraicGeometry.CoherentFinite.overFunctorUnitIso V).symm ≪≫
    dualSheafIsoOfIso ((Scheme.Modules.overFunctorEquiv V).app N).symm

/-- A coherent sheaf of generic rank one which is locally free on an open `U` is finite locally
free of rank one there: its fibre rank is locally constant on the irreducible scheme `U`, so
equal to its value at the generic point. -/
private theorem isFiniteLocallyFreeOfRank_one_restrict [IsIntegral Y] [IsLocallyNoetherian Y]
    (U : Y.Opens) (L : Y.Modules) [_root_.SheafOfModules.IsCoherent L]
    (hU : Scheme.Modules.IsLocallyFree (L.restrict U.ι))
    (hrank : Scheme.Modules.fiberRank L (genericPoint Y) = 1) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (L.restrict U.ι) 1 := by
  haveI := Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_restrict U L
  have hfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (L.restrict U.ι) := by
    have key := (Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae
      (L.restrict U.ι)).out 3 4
    exact key.mp ⟨(Scheme.Modules.isLocallyFree_iff_pointwise _).mpr hU,
      _root_.SheafOfModules.IsCoherent.isFiniteType⟩
  haveI : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (L.restrict U.ι) :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).mpr hfl
  have hlc := Scheme.Modules.isLocallyConstant_fiberRank (L.restrict U.ι)
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq _ 1 fun x => ?_
  haveI : Nonempty U.toScheme := ⟨x⟩
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨x.1, Set.mem_univ _, x.2⟩
  let z : U.toScheme := ⟨genericPoint Y, hgen⟩
  rw [hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ z)]
  exact (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict U.ι L z).trans hrank

/-- A module is locally free on its locally free locus. -/
private theorem isLocallyFree_restrict_locallyFreeLocus (L : Y.Modules) :
    Scheme.Modules.IsLocallyFree (L.restrict (locallyFreeLocus L).ι) := by
  set V := locallyFreeLocus L
  intro z
  obtain ⟨U, hxU, hU⟩ := (mem_locallyFreeLocus_iff L z.1).mp z.2
  obtain ⟨W, hxW, I, ⟨e⟩⟩ := hU ⟨z.1, hxU⟩
  let e' : (Scheme.Modules.restrictFunctor (W.ι ≫ U.ι)).obj L ≅ SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctorComp W.ι U.ι).app L ≪≫ e
  let W' : V.toScheme.Opens := V.ι ⁻¹ᵁ (U.ι ''ᵁ W)
  have hrange : Set.range (W'.ι ≫ V.ι) ⊆ Set.range (W.ι ≫ U.ι) := by
    rintro _ ⟨y, rfl⟩
    have hy : V.ι y.1 ∈ U.ι ''ᵁ W := y.2
    rw [← SetLike.mem_coe, Scheme.Hom.coe_image] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    exact ⟨⟨w, hw⟩, hwy⟩
  obtain ⟨e''⟩ := Stacks.Modules.nonempty_restrictIsoFree_of_range_subset
    (W.ι ≫ U.ι) (W'.ι ≫ V.ι) L I hrange e'
  exact ⟨W', ⟨⟨z.1, hxU⟩, hxW, rfl⟩, I,
    ⟨((Scheme.Modules.restrictFunctorComp W'.ι V.ι).app L).symm ≪≫ e''⟩⟩

/-- On the locally free locus, a coherent sheaf of generic rank one is invertible. -/
private theorem isInvertible_restrict_locallyFreeLocus [IsIntegral Y] [IsLocallyNoetherian Y]
    (L : Y.Modules) [_root_.SheafOfModules.IsCoherent L]
    (hrank : Scheme.Modules.fiberRank L (genericPoint Y) = 1) :
    Stacks.SheafOfModules.IsInvertible (locallyFreeLocus L).toScheme.sheaf.obj
      (locallyFreeLocus L).toScheme.ringCatSheaf.property
      ((Scheme.Modules.restrictFunctor (locallyFreeLocus L).ι).obj L) :=
  haveI := isFiniteLocallyFreeOfRank_one_restrict _ L
    (isLocallyFree_restrict_locallyFreeLocus L) hrank
  Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one _ _

/-- The Stacks tensor powers of a coherent module on a locally Noetherian scheme are coherent. -/
private theorem isCoherent_tensorPower [IsLocallyNoetherian Y] (F : Y.Modules)
    [_root_.SheafOfModules.IsCoherent F] :
    ∀ n : ℕ, _root_.SheafOfModules.IsCoherent (TP F n)
  | 0 => inferInstanceAs (_root_.SheafOfModules.IsCoherent (SheafOfModules.unit Y.ringCatSheaf))
  | n + 1 => Stacks.AlgebraicGeometry.ReflexivePowers.isCoherent_tensorPower F inferInstance n

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On a nonempty open `V` where `F` is invertible, the restricted tensor powers of `F` are
reflexive. -/
private theorem isReflexive_restrict_tensorPower [IsIntegral Y] [IsLocallyNoetherian Y]
    (V : Y.Opens) [Nonempty V.toScheme] (F : Y.Modules) [_root_.SheafOfModules.IsCoherent F]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ) : IsReflexive ((Scheme.Modules.restrictFunctor V.ι).obj (TP F n)) := by
  haveI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hinv := Stacks.AlgebraicGeometry.ReflexivePowers.isInvertible_tensorPower _ hV n
  have hrefl := @AlgebraicGeometry.isReflexive_of_isInvertible V.toScheme _ _ _
    hinv.toAlgebraicGeometry
  haveI := isCoherent_tensorPower F n
  haveI := Stacks.AlgebraicGeometry.ReflexiveEquivalence.isCoherent_restrict V (TP F n)
  haveI := isCoherent_tensorPower ((Scheme.Modules.restrictFunctor V.ι).obj F) n
  exact Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_iso
    (restrictTensorPowerIso V F n).symm hrefl

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- The reflexive hull is invisible on an open where the module is reflexive. -/
private noncomputable def restrictReflexiveHullIso [IsLocallyNoetherian Y] (V : Y.Opens)
    (N : Y.Modules) [_root_.SheafOfModules.IsCoherent N]
    (hN : IsReflexive ((Scheme.Modules.restrictFunctor V.ι).obj N)) :
    (Scheme.Modules.restrictFunctor V.ι).obj (reflexiveHull N) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj N :=
  haveI := Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual V N hN
  (asIso ((Scheme.Modules.restrictFunctor V.ι).map (toDoubleDual N))).symm

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On a nonempty open `V` where `F` is invertible, the reflexive hull of `F^{⊗ n}` restricts to
`(F|_V)^{⊗ n}`. -/
private noncomputable def restrictReflexiveHullTensorPowerIso [IsIntegral Y]
    [IsLocallyNoetherian Y] (V : Y.Opens) [Nonempty V.toScheme] (F : Y.Modules)
    [_root_.SheafOfModules.IsCoherent F]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (n : ℕ) : (Scheme.Modules.restrictFunctor V.ι).obj (reflexiveHull (TP F n)) ≅
      TP ((Scheme.Modules.restrictFunctor V.ι).obj F) n :=
  haveI := isCoherent_tensorPower F n
  restrictReflexiveHullIso V _ (isReflexive_restrict_tensorPower V F hV n) ≪≫
    restrictTensorPowerIso V F n

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- The dual of the tensor power of an invertible sheaf is the tensor power of its dual: both
are tensor inverses of `F^{⊗ n}`. -/
private noncomputable def dualSheafTensorPowerIso (F : Y.Modules)
    (hF : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property F) (n : ℕ) :
    dualSheaf (TP F n) ≅ MMP.Intersection.Scheme.Modules.tensorPow (dualSheaf F) n :=
  haveI : Stacks.SheafOfModules.IsInvertible Y.presheaf _ (TP F n) :=
    Stacks.AlgebraicGeometry.ReflexivePowers.isInvertible_tensorPower _ hF n
  haveI : Stacks.SheafOfModules.IsInvertible Y.presheaf _ F := hF
  Stacks.SheafOfModules.isoOfTensorIsoUnit Y.presheaf _ (TP F n) _ _
    (Stacks.SheafOfModules.Scheme.evaluationIso _ _)
    (whiskerLeftIso _ (tensorPowIsoTensorPower F n).symm ≪≫
      tensorPowTensorIsoUnit (Stacks.SheafOfModules.Scheme.evaluationIso _ F) n)

/-- Any two modules on an empty scheme are isomorphic. -/
private theorem nonempty_iso_of_isEmpty [IsEmpty Y] (A B : Y.Modules) : Nonempty (A ≅ B) :=
  haveI : IsIso (0 : A ⟶ B) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isIso_of_bijective_stalkHom _ isEmptyElim
  ⟨asIso 0⟩

open Stacks.AlgebraicGeometry.ReflexiveModules in
/-- On the locally free locus `X⁰` of a coherent torsion-free sheaf `L` of rank one on a normal
variety, the reflexive power `L^{[i]}` restricts to the integral tensor power of `L|_{X⁰}`:
`L^{[i]}|_{X⁰} ≅ (L|_{X⁰})^{⊗ i}` for every `i : ℤ`. -/
@[mmp "lem_km2c_reflexive_power_restriction"]
public theorem nonempty_restrict_reflexivePow_iso_tensorZPow (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k f] [IsNormal X]
    (L : X.Modules) [SheafOfModules.IsCoherent L]
    (hL : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree L)
    (hrank : Scheme.Modules.fiberRank L (genericPoint X) = 1) (i : ℤ) :
    Nonempty ((Scheme.Modules.restrictFunctor (locallyFreeLocus L).ι).obj (reflexivePow L i) ≅
      MMP.Intersection.Scheme.Modules.tensorZPow
        ((Scheme.Modules.restrictFunctor (locallyFreeLocus L).ι).obj L) i) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set V := locallyFreeLocus L
  set F := (Scheme.Modules.restrictFunctor V.ι).obj L
  cases isEmpty_or_nonempty V.toScheme
  · exact nonempty_iso_of_isEmpty _ _
  have hinv := isInvertible_restrict_locallyFreeLocus L hrank
  rcases i with n | n
  · exact ⟨restrictReflexiveHullTensorPowerIso V L hinv n ≪≫ (tensorPowIsoTensorPower F n).symm⟩
  · exact ⟨restrictDualSheafIso V _ ≪≫
      dualSheafIsoOfIso (restrictReflexiveHullTensorPowerIso V L hinv (n + 1)).symm ≪≫
      dualSheafTensorPowerIso F hinv (n + 1)⟩

end ReflexivePow

end MMP.Mori
