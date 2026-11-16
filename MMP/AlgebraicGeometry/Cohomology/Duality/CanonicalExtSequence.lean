/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Group
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkFormula
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.RingTheory.Dualizing.GorensteinRegularElement
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistenceNagata
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomAdjunctionOnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# The codimension-one canonical `𝓔xt` sequence

Let `X` be of finite type over a field `k`, of pure dimension `d + 1`, with dualizing sheaf `ω_X`
and normalized dualizing complex `K_X`, and let `i : S ⟶ X` be a closed subscheme of pure
dimension `d` with dualizing sheaf `ω_S`. Then `i_* K_S ≅ R𝓗om(𝒪_S, K_X)`, and since `K_X` has
no cohomology below `-(d + 1)`, the truncation triangle `ω_X[d + 1] → K_X → τ_{≥ -d} K_X` gives an
exact sequence
`0 → 𝓔xt¹(𝒪_S, ω_X) → ω_S → 𝓗om(𝒪_S, H^{-d}(K_X)) → 𝓔xt²(𝒪_S, ω_X)`.
At a Cohen–Macaulay point of `X` the sheaf `H^{-d}(K_X)` vanishes, so for `X` Cohen–Macaulay
`ω_S ≅ 𝓔xt¹(𝒪_S, ω_X)`.

## Main results

* `MMP.Flips.exists_exact_homology_of_isGE`: for a triangulated functor `R` preserving `D^{≥ m}`
  and `K ≥ n - 1`, the exact sequence
  `0 → H^n(R(H^{n-1}(K)[1-n])) → H^n(R K) → H^n(R(H^n(K)[-n])) → H^{n+1}(R(H^{n-1}(K)[1-n]))`.
* `MMP.Flips.derivedSheafHomExactSupportNormalizedIso`: `R ℰom(𝒪_S, K_X) ≅ K_S`.
* `MMP.Flips.IsDualizingSheaf.exists_exact_ext`: the exact sequence, and the vanishing of
  `H^{-d}(K_X)` at Cohen–Macaulay points.
* `MMP.Flips.IsDualizingSheaf.nonempty_iso_ext`: `ω_S ≅ 𝓔xt¹(𝒪_S, ω_X)` for `X` Cohen–Macaulay.

## Implementation notes

Two models of `D(𝒪_X)` are in play: the locally small one, at which the normalized dualizing
complexes and the right adjoint `i^!` live, and `CategoryTheory.HasDerivedCategory.standard`, at
which the Ext sheaves `Stacks.Duality.extSheafOf` and the derived internal Hom are stated. The two
have the same objects; `MMP.Flips.homologyLsIsoStd`, `MMP.Flips.singleLsIsoStd` and
`MMP.Flips.rhomExactSupportModelIso` compare cohomology, single complexes and `R ℰom(𝒪_S, -)`
across them.

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite Limits
  Pretriangulated RingedSpaceModuleAdjunction

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

namespace MMP.Flips

open MMP.Mori

/-! ### The lowest-degree exact sequence of a triangulated functor -/

section LowestDegree

universe w v u'

variable {C : Type u'} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory in
/-- An object `≤ n` and `≥ n` of `D(C)` is its `n`-th cohomology placed in degree `n`. -/
lemma nonempty_iso_single_homology_of_isGE_of_isLE (A : DerivedCategory C) (n : ℤ)
    [A.IsGE n] [A.IsLE n] :
    Nonempty (A ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj A)) := by
  obtain ⟨Y, ⟨e⟩⟩ := A.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  exact ⟨e ≪≫ (singleFunctor C n).mapIso
    (((singleFunctorCompHomologyFunctorIso C n).app Y).symm ≪≫ (homologyFunctor C n).mapIso e.symm)⟩

open DerivedCategory in
/-- In a distinguished triangle `A → K → B → A[1]` with `B ≥ m + 1`, the map `A → K` is an
isomorphism on cohomology in degree `m`. -/
lemma isIso_homologyMap_mor₁_of_isGE (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (m n : ℤ) (hmn : m + 1 = n) (hB : T.obj₃.IsGE n) :
    IsIso ((homologyFunctor C m).map T.mor₁) := by
  have hm : Mono ((homologyFunctor C m).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (m - 1) m (by omega)).2
      ((isZero_of_isGE T.obj₃ n (m - 1) (by omega)).eq_of_src _ _)
  have he : Epi ((homologyFunctor C m).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT m).2
      ((isZero_of_isGE T.obj₃ n m (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

open DerivedCategory in
/-- In a distinguished triangle `A → K → B → A[1]` with `A ≤ m` and `B ≥ m + 1`, the cohomology
of `A` in degree `m` is that of `K`, that of `B` in degree `m + 1` is that of `K`, and `A ≥ m` if
`K ≥ m`. -/
lemma truncation_facts (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (m n : ℤ)
    (hmn : m + 1 = n) (hA : T.obj₁.IsLE m) (hB : T.obj₃.IsGE n) (hK : T.obj₂.IsGE m) :
    T.obj₁.IsGE m ∧ IsIso ((homologyFunctor C m).map T.mor₁) ∧
      IsIso ((homologyFunctor C n).map T.mor₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isGE_iff]
    intro i hi
    have hE := HomologySequence.exact₁ T hT (i - 1) i (by omega)
    exact hE.isZero_X₂ ((isZero_of_isGE T.obj₃ n (i - 1) (by omega)).eq_of_src _ _)
      ((isZero_of_isGE T.obj₂ m i hi).eq_of_tgt _ _)
  · exact isIso_homologyMap_mor₁_of_isGE T hT m n hmn hB
  · have hm : Mono ((homologyFunctor C n).map T.mor₂) :=
      (HomologySequence.mono_homologyMap_mor₂_iff T hT n).2
        ((isZero_of_isLE T.obj₁ m n (by omega)).eq_of_src _ _)
    have he : Epi ((homologyFunctor C n).map T.mor₂) :=
      (HomologySequence.epi_homologyMap_mor₂_iff T hT n (n + 1) (by omega)).2
        ((isZero_of_isLE T.obj₁ m (n + 1) (by omega)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

open DerivedCategory in
/-- An object `K ≥ m` sits in a distinguished triangle `A → K → B → A[1]` with `A` the `m`-th
cohomology of `K` placed in degree `m`, `B ≥ n = m + 1`, and `K → B` an isomorphism on `H^n`. -/
lemma exists_distTriang_single_homology_of_isGE (K : DerivedCategory C) (m n : ℤ)
    (hmn : m + 1 = n) (hK : K.IsGE m) :
    ∃ (A B : DerivedCategory C) (f : A ⟶ K) (g : K ⟶ B) (h : B ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ ∧ B.IsGE n ∧ IsIso ((homologyFunctor C n).map g) ∧
        Nonempty (A ≅ (singleFunctor C m).obj ((homologyFunctor C m).obj K)) := by
  obtain ⟨A, B, hA, hB, f, g, h, hT⟩ := TStructure.t.exists_triangle K m n (by omega)
  have hA' : A.IsLE m := ⟨hA⟩
  have hB' : B.IsGE n := ⟨hB⟩
  obtain ⟨hAge, hf, hg⟩ := truncation_facts _ hT m n hmn hA' hB' hK
  have : A.IsGE m := hAge
  have : IsIso ((homologyFunctor C m).map f) := hf
  obtain ⟨eA⟩ := nonempty_iso_single_homology_of_isGE_of_isLE A m
  exact ⟨A, B, f, g, h, hT, hB', hg,
    ⟨eA ≪≫ (singleFunctor C m).mapIso (asIso ((homologyFunctor C m).map f))⟩⟩

open DerivedCategory in
/-- **The lowest-degree exact sequence of a triangulated functor.** Let `R` be a triangulated
endofunctor of `D(C)` carrying `D^{≥ m}` into `D^{≥ m}` for every `m`, and let `K ≥ n - 1`. Then
there is an exact sequence
`0 → H^n(R(H^{n-1}(K)[1-n])) → H^n(R K) → H^n(R(H^n(K)[-n])) → H^{n+1}(R(H^{n-1}(K)[1-n]))`. -/
lemma exists_exact_homology_of_isGE (R : DerivedCategory C ⥤ DerivedCategory C)
    [R.CommShift ℤ] [R.IsTriangulated]
    (hR : ∀ (M : DerivedCategory C) (m : ℤ), M.IsGE m → (R.obj M).IsGE m)
    (K : DerivedCategory C) (n : ℤ) (hK : K.IsGE (n - 1)) :
    ∃ (a : (homologyFunctor C n).obj
          (R.obj ((singleFunctor C (n - 1)).obj ((homologyFunctor C (n - 1)).obj K))) ⟶
          (homologyFunctor C n).obj (R.obj K))
      (b : (homologyFunctor C n).obj (R.obj K) ⟶
          (homologyFunctor C n).obj (R.obj ((singleFunctor C n).obj ((homologyFunctor C n).obj K))))
      (c : (homologyFunctor C n).obj
          (R.obj ((singleFunctor C n).obj ((homologyFunctor C n).obj K))) ⟶
          (homologyFunctor C (n + 1)).obj
            (R.obj ((singleFunctor C (n - 1)).obj ((homologyFunctor C (n - 1)).obj K))))
      (hab : a ≫ b = 0) (hbc : b ≫ c = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact := by
  obtain ⟨A, B, f, g, h, hT, hB', hg, ⟨eA₁⟩⟩ :=
    exists_distTriang_single_homology_of_isGE K (n - 1) n (by omega) hK
  obtain ⟨A', B', f', g', h', hT', hB₂', -, ⟨eA'⟩⟩ :=
    exists_distTriang_single_homology_of_isGE B n (n + 1) rfl hB'
  have : IsIso ((homologyFunctor C n).map g) := hg
  let eA'₁ : A' ≅ (singleFunctor C n).obj ((homologyFunctor C n).obj K) :=
    eA' ≪≫ (singleFunctor C n).mapIso (asIso ((homologyFunctor C n).map g)).symm
  have hRT := R.map_distinguished _ hT
  have hRT' := R.map_distinguished _ hT'
  have hRB : (R.obj B).IsGE n := hR B n hB'
  have : IsIso ((homologyFunctor C n).map (R.map f')) :=
    isIso_homologyMap_mor₁_of_isGE _ hRT' n (n + 1) rfl (hR B' (n + 1) hB₂')
  let φ := asIso ((homologyFunctor C n).map (R.map f'))
  let ψA := (homologyFunctor C n).mapIso (R.mapIso eA₁)
  let ψA₁ := (homologyFunctor C (n + 1)).mapIso (R.mapIso eA₁)
  let ψA' := (homologyFunctor C n).mapIso (R.mapIso eA'₁)
  let δ := HomologySequence.δ (R.mapTriangle.obj (Triangle.mk f g h)) n (n + 1) rfl
  refine ⟨ψA.inv ≫ (homologyFunctor C n).map (R.map f),
    (homologyFunctor C n).map (R.map g) ≫ φ.inv ≫ ψA'.hom,
    ψA'.inv ≫ φ.hom ≫ δ ≫ ψA₁.hom, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Category.assoc]
    have hfg : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [← Category.assoc ((homologyFunctor C n).map (R.map f)), ← Functor.map_comp,
      ← Functor.map_comp, hfg]
    simp
  · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    have h0 : (homologyFunctor C n).map (R.map g) ≫ δ = 0 :=
      HomologySequence.comp_δ _ hRT n (n + 1) rfl
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψA₁.hom) h0).trans zero_comp)
  · have hm : Mono ((homologyFunctor C n).map (R.map f)) :=
      (HomologySequence.exact₁ _ hRT (n - 1) n (by omega)).mono_g
        ((isZero_of_isGE (R.obj B) n (n - 1) (by omega)).eq_of_src _ _)
    infer_instance
  · refine (ShortComplex.exact_iff_of_iso ?_).1 (HomologySequence.exact₂ _ hRT n)
    exact ShortComplex.isoMk ψA (Iso.refl _) (φ.symm ≪≫ ψA')
      ((Iso.hom_inv_id_assoc _ _).trans (Category.comp_id _).symm)
      (Category.id_comp _)
  · refine (ShortComplex.exact_iff_of_iso ?_).1 (HomologySequence.exact₃ _ hRT n (n + 1) rfl)
    exact ShortComplex.isoMk (Iso.refl _) (φ.symm ≪≫ ψA') ψA₁
      (Category.id_comp _)
      (by
        change (φ.inv ≫ ψA'.hom) ≫ ψA'.inv ≫ φ.hom ≫ δ ≫ ψA₁.hom = δ ≫ ψA₁.hom
        simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc])

open DerivedCategory in
/-- For a functor commuting with shifts, `H^j(R(W[-a])) ≅ H^{j-a}(R(W))`. -/
noncomputable def homologyObjSingleIso (R : DerivedCategory C ⥤ DerivedCategory C)
    [R.CommShift ℤ] (W : C) (a j k : ℤ) (h : j - a = k) :
    (homologyFunctor C j).obj (R.obj ((singleFunctor C a).obj W)) ≅
      (homologyFunctor C k).obj (R.obj ((singleFunctor C 0).obj W)) :=
  (homologyFunctor C j).mapIso
      (R.mapIso (((singleFunctors C).shiftIso (-a) a 0 (by omega)).app W).symm ≪≫
        (R.commShiftIso (-a)).app ((singleFunctor C 0).obj W)) ≪≫
    ((homologyFunctor C 0).shiftIso (-a) j k (by omega)).app _

end LowestDegree

/-! ### Comparison of the two models of `D(𝒪_X)`, and `R𝓗om(i_* 𝒪_S, -)` -/

section Models

variable {X S : Scheme.{u}}

/-- Cohomology of an object of `D(𝒪_X)` does not depend on the model. -/
def homologyLsIsoStd (Y : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (n : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules n).obj Y ≅
      (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).obj Y :=
  let Qs := @DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard _)
  let e : Qs.obj (Qs.objPreimage Y) ≅ Y := Qs.objObjPreimageIso Y
  (DerivedCategory.homologyFunctor X.Modules n).mapIso
      ((Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).functor.mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors X.Modules n).app (Qs.objPreimage Y) ≪≫
    ((@DerivedCategory.homologyFunctorFactors X.Modules _ _ (HasDerivedCategory.standard _)
      n).app (Qs.objPreimage Y)).symm ≪≫
    (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).mapIso e

/-- An isomorphism in the locally small model is one in the standard model. -/
def isoStdOfIsoLs {A B : DerivedCategory X.Modules} (e : A ≅ B) :
    @Iso (@DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) _ A B :=
  (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).inverse.mapIso e

/-- The two models place a module in degree `n` at isomorphic objects. -/
def singleLsIsoStd (M : X.Modules) (n : ℤ) :
    @Iso (@DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) _
      ((DerivedCategory.singleFunctor X.Modules n).obj M)
      ((@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) n).obj M) :=
  isoStdOfIsoLs ((DerivedCategory.singleFunctorIsoCompQ X.Modules n).app M) ≪≫
    ((@DerivedCategory.singleFunctorIsoCompQ X.Modules _ _ (HasDerivedCategory.standard _)
      n).app M).symm

section Std

attribute [local instance 10000] HasDerivedCategory.standard

/-- `R𝓗om(F, -)` as an endofunctor of the standard `D(𝒪_X)`. -/
abbrev rhomFrom (F : X.Modules) : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
    (op ((DerivedCategory.singleFunctor X.Modules 0).obj F))

/-- The shift structure on `- ⊗ᴸ F`. -/
instance (F : X.Modules) :
    (Stacks.SheafOfModules.derivedTensorRight X.sheaf
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).CommShift ℤ :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).commShift_left _

/-- The functor `- ⊗ᴸ F` is triangulated. -/
instance (F : X.Modules) :
    (Stacks.SheafOfModules.derivedTensorRight X.sheaf
      ((DerivedCategory.singleFunctor X.Modules 0).obj F)).IsTriangulated :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (Stacks.SheafOfModules.ringedSite X.sheaf)).exact_left _

/-- The shift structure on `R𝓗om(F, -)`, from its left adjoint `- ⊗ᴸ F`. -/
@[instance_reducible] def rhomFromCommShift (F : X.Modules) : (rhomFrom F).CommShift ℤ :=
  (Stacks.SheafOfModules.derivedSheafHomTensorAdjunction X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)).rightAdjointCommShift ℤ

/-- `R𝓗om(F, -)` is triangulated, being right adjoint to `- ⊗ᴸ F`. -/
lemma rhomFrom_isTriangulated (F : X.Modules) :
    letI := rhomFromCommShift F
    (rhomFrom F).IsTriangulated := by
  let := rhomFromCommShift F
  let : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
      (op ((DerivedCategory.singleFunctor X.Modules 0).obj F))).CommShift ℤ := rhomFromCommShift F
  have : (Stacks.SheafOfModules.derivedSheafHomTensorAdjunction X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)).CommShift ℤ :=
    Adjunction.commShift_of_leftAdjoint _ ℤ
  exact (Stacks.SheafOfModules.derivedSheafHomTensorAdjunction X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)).isTriangulated_rightAdjoint

/-- `R𝓗om(F, -)` carries `D^{≥ m}` into `D^{≥ m}` for a module `F`. -/
lemma rhomFrom_isGE (F : X.Modules) (M : DerivedCategory X.Modules) (m : ℤ) (hM : M.IsGE m) :
    ((rhomFrom F).obj M).IsGE m := by
  have := Stacks.SheafOfModules.isGE_derivedSheafHom X.sheaf
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) M 0 m
    (inferInstance : ((DerivedCategory.singleFunctor X.Modules 0).obj F).IsLE 0) hM
  rwa [sub_zero] at this

variable (i : S ⟶ X) [IsClosedImmersion i]

/-- `i_* 𝒪_S` in degree zero is the derived pushforward of `𝒪_S`. -/
def pushforwardUnitSingleIso :
    (modulePushforward (Stacks.Duality.closedQuotient i).i).mapDerivedCategory.obj
        (RingedSite.derivedStructureSheaf
          (Stacks.SheafOfModules.ringedSite (Stacks.Duality.closedQuotient i).Z.sheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf)) :=
  ((modulePushforward (Stacks.Duality.closedQuotient i).i).mapDerivedCategorySingleFunctor 0).app
    (SheafOfModules.unit _)

/-- **[Stacks, Tag 0A77]** in the form used here: `R𝓗om(i_* 𝒪_S, -) ≅ Ri_* R𝓗om(𝒪_S, -)`. -/
def rhomFromPushforwardIso :
    rhomFrom ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf)) ≅
      (Stacks.Duality.closedQuotient i).derivedSheafHomExactSupport ⋙
        (modulePushforward (Stacks.Duality.closedQuotient i).i).mapDerivedCategory :=
  (Stacks.SheafOfModules.derivedSheafHom X.sheaf).mapIso (pushforwardUnitSingleIso i).op ≪≫
    (Stacks.Duality.closedQuotient i).derivedSheafHomExactSupportPushforwardNatIso.symm

/-- **`R ℰom(𝒪_S, -)` read at the two models**, as in
`Stacks.Duality.ClosedImmersionDualizing.rhomModelIso`: both are total right derived functors of
sheaf Hom with exact support. -/
def rhomExactSupportModelIso :
    (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport ⋙
      (Stacks.Injectives.grothendieckModelEquiv.{u}
        (SheafOfModules.{u} (structureSheafRing
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z))).functor ≅
      (Stacks.Injectives.grothendieckModelEquiv.{u}
        (SheafOfModules.{u} (structureSheafRing
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X))).functor ⋙
        Stacks.Duality.LocallySmall.derivedSheafHomExactSupport i :=
  StacksDraft.DerivedModel.rightDerivedModelIso
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) (ComplexShape.up ℤ))
    (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).derivedSheafHomExactSupportComparison
    (Stacks.Duality.LocallySmall.derivedSheafHomExactSupportComparison i)
    (StacksDraft.DerivedModel.shrinkComparisonQhIso _).symm
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (StacksDraft.DerivedModel.shrinkComparisonQhIso _).symm)

/-- **The cohomology of `R𝓗om(i_* 𝒪_S, K)`** is the pushforward of the cohomology of any
object `T` of the locally small `D(𝒪_S)` isomorphic to `R ℰom(𝒪_S, K)`. -/
def homologyRhomFromIso (K : @DerivedCategory X.Modules _ _ (Scheme.Modules.hasDerivedCategory X))
    (T : @DerivedCategory S.Modules _ _ (Scheme.Modules.hasDerivedCategory S))
    (eT : (Stacks.Duality.LocallySmall.derivedSheafHomExactSupport i).obj K ≅ T) (n : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules n).obj
        ((rhomFrom ((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit S.ringCatSheaf))).obj K) ≅
      (Scheme.Modules.pushforward i).obj
        ((@DerivedCategory.homologyFunctor S.Modules _ _
          (Scheme.Modules.hasDerivedCategory S) n).obj T) :=
  (DerivedCategory.homologyFunctor X.Modules n).mapIso ((rhomFromPushforwardIso i).app K) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (modulePushforward (Stacks.Duality.closedQuotient i).i) n).app _ ≪≫
    (modulePushforward (Stacks.Duality.closedQuotient i).i).mapIso
      ((homologyLsIsoStd (X := S) _ n).symm ≪≫
        (@DerivedCategory.homologyFunctor S.Modules _ _
          (Scheme.Modules.hasDerivedCategory S) n).mapIso
          ((rhomExactSupportModelIso i).app K ≪≫ eT))

end Std

end Models

/-! ### Cohen–Macaulay local rings -/

section CohenMacaulayRing

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The normalized dualizing complex of a Cohen–Macaulay local ring of dimension `h` has no
cohomology outside degree `-h`** ([Stacks, Tag 0AWS]). -/
lemma isZero_homology_of_isCohenMacaulayLocalRing {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hCM : IsCohenMacaulayLocalRing A)
    (D : DerivedCategory (ModuleCat.{u} A))
    (hD : Dualizing.IsNormalizedDualizingComplex.{u, u} D) (h : ℕ)
    (hh : ringKrullDim A = (h : WithBot ℕ∞)) (j : ℤ) (hj : j ≠ -(h : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj D) := by
  obtain ⟨e⟩ := ((Dualizing.isCohenMacaulay_tfae_dualizingComplex D
    (isNormalizedDualizingComplex_ulift_zero hD)).out 1 3).mp hCM
  have hdim : Dualizing.localRingDimension A = h := by
    have h1 : ((IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) = h := by
      rwa [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    have h2 : (IsLocalRing.maximalIdeal A).height = h := by exact_mod_cast h1
    simp [Dualizing.localRingDimension, h2]
  rw [hdim] at e
  rcases lt_or_gt_of_ne hj with hlt | hgt
  · exact (DerivedCategory.isZero_of_isGE _ (-(h : ℤ)) j hlt).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).mapIso e)
  · exact (DerivedCategory.isZero_of_isLE _ (-(h : ℤ)) j hgt).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).mapIso e)

end CohenMacaulayRing

/-! ### The codimension-one canonical `𝓔xt` sequence -/

section Ext

variable {k : Type u} [Field k] {X S : Scheme.{u}}

/-- `𝓔xt^j_{𝒪_X}(𝒪_S, F)` for a closed immersion `i : S ⟶ X`. -/
abbrev extStructureSheaf (i : S ⟶ X) (F : X.Modules) (j : ℕ) : X.Modules :=
  Stacks.Duality.extSheafOf
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf))
    ((DerivedCategory.singleFunctor X.Modules 0).obj F) (-(j : ℤ))

/-- `𝓔xt^j_{𝒪_X}(𝒪_S, M)` is the `j`-th cohomology of `R𝓗om(i_* 𝒪_S, M)`. -/
lemma extStructureSheaf_eq (i : S ⟶ X) (M : X.Modules) (j : ℕ) :
    extStructureSheaf i M j =
      (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) j).obj
        ((rhomFrom ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf))).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)) := by
  simp only [extStructureSheaf, Stacks.Duality.extSheafOf, neg_neg]
  rfl

/-- **The normalized dualizing complex of a closed subscheme is `R ℰom(𝒪_S, K_X)`.** For a
closed immersion `i : S ⟶ X` of Noetherian schemes of finite type over `k`,
`R ℰom(𝒪_S, K_X) ≅ i^! K_X ≅ K_S` ([Stacks, Tags 0A9X and 0AUD]). -/
def derivedSheafHomExactSupportNormalizedIso [IsNoetherian X] {π : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType π] (i : S ⟶ X) [IsClosedImmersion i] [IsNoetherian S] :
    (Stacks.Duality.LocallySmall.derivedSheafHomExactSupport i).obj
        (normalizedDualizingComplexOverField π).complex.obj.obj ≅
      (normalizedDualizingComplexOverField (i ≫ π)).complex.obj.obj := by
  let e := Stacks.Duality.NormalizedOnOpens.twistedInverseImageObjIso
    Stacks.Duality.nagataCompactification (f := i) (q := π) rfl
    (Stacks.Duality.isDualizingComplex_derivedStructureSheafPlus_of_field k)
    (normalizedDualizingComplexOverField (i ≫ π)) (normalizedDualizingComplexOverField π)
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have := Stacks.Duality.LocallySmall.isIso_rightAdjointToDerivedSheafHom_app i _ _
    (Stacks.Duality.twistedInverseImageAdjunction i
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs i))
    ((pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance)
    (normalizedDualizingComplexOverField π).complex
  exact (asIso ((Stacks.Duality.LocallySmall.rightAdjointToDerivedSheafHom i _ _
    (Stacks.Duality.twistedInverseImageAdjunction i
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs i))).app
        (normalizedDualizingComplexOverField π).complex.obj)).symm ≪≫ (ObjectProperty.ι _).mapIso e

/-- **At a Cohen–Macaulay point, `H^{-d}(K_X)` vanishes** when `X` has pure dimension `d + 1`:
its stalk is `H^{1-h}` of the normalized dualizing complex of `𝒪_{X,x}`, `h = dim 𝒪_{X,x}`, which
is concentrated in degree `-h` ([Stacks, Tag 0AWS]). -/
lemma subsingleton_stalk_homology_of_isCohenMacaulayLocalRing [IsLocallyNoetherian X]
    [CompactSpace X] {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x : X) (hx : IsCohenMacaulayLocalRing (X.presheaf.stalk x)) :
    letI : IsNoetherian X := {}
    Subsingleton (Stacks.Duality.moduleStalkAtPoint
      ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
        (normalizedDualizingComplexOverField π).complex.obj.obj) x) := by
  let : IsNoetherian X := {}
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨-, hloc⟩ := hK3 (d + 1) hd
  obtain ⟨D, e, h, hD, -, hh, hed, hiso, -⟩ := hloc x
  obtain ⟨E⟩ := hiso (-(d : ℤ))
  have : Subsingleton (Stacks.Duality.standardHomology D (-(d : ℤ) + e)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (isZero_homology_of_isCohenMacaulayLocalRing hx D hD h hh (-(d : ℤ) + e) (by omega))
  exact E.toEquiv.subsingleton

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The data of three isomorphic objects transport an exact sequence starting with a
monomorphism. -/
lemma exists_exact_of_iso {C : Type*} [Category C] [Abelian C] {P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : C}
    (e₁ : P₁ ≅ Q₁) (e₂ : P₂ ≅ Q₂) (e₃ : P₃ ≅ Q₃) (e₄ : P₄ ≅ Q₄)
    (h : ∃ (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (c : P₃ ⟶ P₄) (hab : a ≫ b = 0) (hbc : b ≫ c = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact) :
    ∃ (a : Q₁ ⟶ Q₂) (b : Q₂ ⟶ Q₃) (c : Q₃ ⟶ Q₄) (hab : a ≫ b = 0) (hbc : b ≫ c = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact := by
  obtain ⟨a, b, c, hab, hbc, h₁, h₂, h₃⟩ := h
  refine ⟨e₁.inv ≫ a ≫ e₂.hom, e₂.inv ≫ b ≫ e₃.hom, e₃.inv ≫ c ≫ e₄.hom,
    by simp [reassoc_of% hab], by simp [reassoc_of% hbc], inferInstance, ?_, ?_⟩
  · refine (ShortComplex.exact_iff_of_iso ?_).1 h₂
    exact ShortComplex.isoMk e₁ e₂ e₃ (by simp) (by simp)
  · refine (ShortComplex.exact_iff_of_iso ?_).1 h₃
    exact ShortComplex.isoMk e₂ e₃ e₄ (by simp) (by simp)

/-- **The `𝓔xt` sequence of a closed immersion, from the lowest two cohomology sheaves.** Let
`K` be an object of `D(𝒪_X)` with `H^j(K) = 0` for `j < n - 1`, `ω ≅ H^{n-1}(K)`, and let `T`
be an object of `D(𝒪_S)` with `R ℰom(𝒪_S, K) ≅ T` and `ω_S ≅ H^n(T)`. Then there is an exact
sequence `0 → 𝓔xt¹(𝒪_S, ω) → i_* ω_S → 𝓗om(𝒪_S, H^n(K)) → 𝓔xt²(𝒪_S, ω)`. -/
lemma exists_exact_extStructureSheaf (i : S ⟶ X) [IsClosedImmersion i]
    (K : @DerivedCategory X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)) (n : ℤ)
    (hK : ∀ j < n - 1, IsZero
      ((@DerivedCategory.homologyFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) j).obj K))
    (ω : X.Modules)
    (eω : ω ≅ (@DerivedCategory.homologyFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
      (n - 1)).obj K)
    (T : @DerivedCategory S.Modules _ _ (Scheme.Modules.hasDerivedCategory S))
    (eT : (Stacks.Duality.LocallySmall.derivedSheafHomExactSupport i).obj K ≅ T) (ωS : S.Modules)
    (eS : ωS ≅ (@DerivedCategory.homologyFunctor S.Modules _ _ (Scheme.Modules.hasDerivedCategory S)
      n).obj T) :
    ∃ (a : extStructureSheaf i ω 1 ⟶ (Scheme.Modules.pushforward i).obj ωS)
        (b : (Scheme.Modules.pushforward i).obj ωS ⟶ extStructureSheaf i
          ((@DerivedCategory.homologyFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
            n).obj K) 0)
        (c : extStructureSheaf i
          ((@DerivedCategory.homologyFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
            n).obj K) 0 ⟶ extStructureSheaf i ω 2)
        (hab : a ≫ b = 0) (hbc : b ≫ c = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact := by
  let F := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit S.ringCatSheaf)
  let R := rhomFrom F
  let := rhomFromCommShift F
  have := rhomFrom_isTriangulated F
  have hKge : @DerivedCategory.IsGE X.Modules _ _ (HasDerivedCategory.standard _) K (n - 1) :=
    (@DerivedCategory.isGE_iff X.Modules _ _ (HasDerivedCategory.standard _) K (n - 1)).2
      fun j hj => (hK j hj).of_iso (homologyLsIsoStd K j).symm
  have h := exists_exact_homology_of_isGE R (rhomFrom_isGE F) K n hKge
  let W := (DerivedCategory.homologyFunctor X.Modules (n - 1)).obj K
  let eW : W ≅ ω := (homologyLsIsoStd K (n - 1)).symm ≪≫ eω.symm
  let eW₀ : (DerivedCategory.singleFunctor X.Modules 0).obj W ≅
      (@DerivedCategory.singleFunctor X.Modules _ _
        (Scheme.Modules.hasDerivedCategory X) 0).obj ω :=
    (DerivedCategory.singleFunctor X.Modules 0).mapIso eW ≪≫ (singleLsIsoStd ω 0).symm
  let W' := (DerivedCategory.homologyFunctor X.Modules n).obj K
  let eW'₀ : (DerivedCategory.singleFunctor X.Modules 0).obj W' ≅
      (@DerivedCategory.singleFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X) 0).obj
        ((@DerivedCategory.homologyFunctor X.Modules _ _ (Scheme.Modules.hasDerivedCategory X)
          n).obj K) :=
    (DerivedCategory.singleFunctor X.Modules 0).mapIso (homologyLsIsoStd K n).symm ≪≫
      (singleLsIsoStd _ 0).symm
  refine exists_exact_of_iso ?_ ?_ ?_ ?_ h
  · exact homologyObjSingleIso R W (n - 1) n ((1 : ℕ) : ℤ) (by simp) ≪≫
      (DerivedCategory.homologyFunctor X.Modules ((1 : ℕ) : ℤ)).mapIso (R.mapIso eW₀) ≪≫
      eqToIso (extStructureSheaf_eq i ω 1).symm
  · exact homologyRhomFromIso i K T eT n ≪≫ (Scheme.Modules.pushforward i).mapIso eS.symm
  · exact homologyObjSingleIso R W' n n ((0 : ℕ) : ℤ) (by simp) ≪≫
      (DerivedCategory.homologyFunctor X.Modules ((0 : ℕ) : ℤ)).mapIso (R.mapIso eW'₀) ≪≫
      eqToIso (extStructureSheaf_eq i _ 0).symm
  · exact homologyObjSingleIso R W (n - 1) (n + 1) ((2 : ℕ) : ℤ) (by push_cast; omega) ≪≫
      (DerivedCategory.homologyFunctor X.Modules ((2 : ℕ) : ℤ)).mapIso (R.mapIso eW₀) ≪≫
      eqToIso (extStructureSheaf_eq i ω 2).symm

end

/-- **The codimension-one canonical `𝓔xt` sequence, including the non-Cohen–Macaulay
correction.** Let `X` be of finite type over `k` and of pure dimension `d + 1`, with dualizing
sheaf `ω_X` and normalized dualizing complex `ω_X^•`, and `i : S ⟶ X` a closed subscheme of pure
dimension `d` with dualizing sheaf `ω_S`. Then there is an exact sequence
`0 → 𝓔xt¹(𝒪_S, ω_X) → ω_S → 𝓗om(𝒪_S, H^{-d}(ω_X^•)) → 𝓔xt²(𝒪_S, ω_X)`, and
`H^{-d}(ω_X^•)` vanishes at the Cohen–Macaulay points of `X`. -/
@[mmp "lem_mmp_foundation_fa16_dualizing_codimension_one_ext"]
theorem IsDualizingSheaf.exists_exact_ext [IsLocallyNoetherian X] [CompactSpace X]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ} {ωX : X.Modules}
    (hX : IsDualizingSheaf π (d + 1) ωX)
    (i : S ⟶ X) [IsClosedImmersion i] {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS) :
    letI : IsNoetherian X := {}
    (∃ (a : extStructureSheaf i ωX 1 ⟶ (Scheme.Modules.pushforward i).obj ωS)
        (b : (Scheme.Modules.pushforward i).obj ωS ⟶
          extStructureSheaf i ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
            (normalizedDualizingComplexOverField π).complex.obj.obj) 0)
        (c : extStructureSheaf i ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
            (normalizedDualizingComplexOverField π).complex.obj.obj) 0 ⟶ extStructureSheaf i ωX 2)
        (hab : a ≫ b = 0) (hbc : b ≫ c = 0),
      Mono a ∧ (ShortComplex.mk a b hab).Exact ∧ (ShortComplex.mk b c hbc).Exact) ∧
    ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x) →
      Subsingleton (Stacks.Duality.moduleStalkAtPoint
        ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
          (normalizedDualizingComplexOverField π).complex.obj.obj) x) := by
  let : IsNoetherian X := {}
  obtain ⟨hNS, -⟩ := isNoetherian_and_locallyOfFiniteType_of_isDualizingSheaf hS
  have := hNS
  refine ⟨?_, fun x hx => subsingleton_stalk_homology_of_isCohenMacaulayLocalRing hX.1 x hx⟩
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨hvan, -⟩ := hK3 (d + 1) hX.1
  obtain ⟨eX⟩ := hX.nonempty_iso_homology
  obtain ⟨eS⟩ := hS.nonempty_iso_homology
  rw [show (-((d + 1 : ℕ) : ℤ)) = -(d : ℤ) - 1 by omega] at eX
  exact exists_exact_extStructureSheaf i _ (-(d : ℤ))
    (fun j hj => hvan j (Or.inl (by push_cast; omega))) ωX eX _
    (derivedSheafHomExactSupportNormalizedIso i) ωS eS

/-- **The codimension-one canonical `𝓔xt` sequence**, Cohen–Macaulay case. Let `X` be
Cohen–Macaulay of finite type over `k` and of pure dimension `d + 1` with dualizing sheaf `ω_X`,
and `i : S ⟶ X` a closed subscheme of pure codimension one with dualizing sheaf `ω_S`. Then
`ω_S ≅ 𝓔xt¹_{𝒪_X}(𝒪_S, ω_X)`. -/
@[mmp "lem_mmp_foundation_fa16_dualizing_codimension_one_ext"]
theorem IsDualizingSheaf.nonempty_iso_ext [IsLocallyNoetherian X] [CompactSpace X]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ} {ωX : X.Modules}
    (hX : IsDualizingSheaf π (d + 1) ωX)
    (hCM : ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x))
    (i : S ⟶ X) [IsClosedImmersion i] {ωS : S.Modules} (hS : IsDualizingSheaf (i ≫ π) d ωS) :
    Nonempty ((Scheme.Modules.pushforward i).obj ωS ≅ extStructureSheaf i ωX 1) := by
  let : IsNoetherian X := {}
  obtain ⟨⟨a, b, c, hab, hbc, hm, h₂, -⟩, hv⟩ := hX.exists_exact_ext i hS
  have hH : IsZero ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) :=
    (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj
      X.ringCatSheaf _).mpr fun y => ModuleCat.isZero_iff_subsingleton.mpr (hv y (hCM y))
  have hE : IsZero (extStructureSheaf i ((DerivedCategory.homologyFunctor X.Modules
      (-(d : ℤ))).obj (normalizedDualizingComplexOverField π).complex.obj.obj) 0) := by
    rw [extStructureSheaf_eq]
    have hZ := (Functor.map_isZero
      (@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0) hH).of_iso
        (singleLsIsoStd _ 0)
    have hge := (@DerivedCategory.isGE_iff X.Modules _ _ (HasDerivedCategory.standard _) _ 1).2
      fun j _ => Functor.map_isZero
        (@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard _) j) hZ
    exact @DerivedCategory.isZero_of_isGE X.Modules _ _ (HasDerivedCategory.standard _) _ 1 _
      (by simp) (rhomFrom_isGE _ _ 1 hge)
  have he : Epi a := h₂.epi_f (hE.eq_of_tgt _ _)
  exact ⟨(@asIso _ _ _ _ a (isIso_of_mono_of_epi a)).symm⟩

end Ext

end MMP.Flips
