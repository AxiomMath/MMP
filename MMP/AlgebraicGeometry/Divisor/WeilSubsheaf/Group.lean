/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Modules.TotalQuotientSheaf
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.RingTheory.CohenMacaulay.Witnesses
public import StacksFrontier.RingTheory.Dualizing.NormalizedShiftSelfUniverse
public import StacksFrontier.RingTheory.Dualizing.QuotientExtConcentration

/-!
# The group of Weil divisorial subsheaves (FA 16.1–16.4)

The structure of `WSh(X)` for a reduced, pure-dimensional scheme `X` of finite type over a field
`k` (the standing setting of FA 16):

* `MMP.Flips.IsDualizingSheaf.isCohenMacaulayLocalRing_and_isGorenstein_iff`: at a point `η` of
  codimension `≤ 1`, `𝒪_{X,η}` is Cohen–Macaulay, and Gorenstein iff `(ω_X)_η ≅ 𝒪_{X,η}`.
* `MMP.Flips.IsDualizingSheaf.exists_weilDivisorialSubsheaf_iff`: `φ(ω_X) ⊆ K(X)` is a Weil
  divisorial subsheaf iff `X` is Gorenstein in codimension one (FA 16.3.3).
* `MMP.Flips.RationalFunctionsSubmodule.isCoherent_saturation`: the saturation of a coherent
  submodule of `K(X)` is coherent.
* `MMP.Flips.RationalFunctionsSubmodule.unitSmul_saturation`,
  `MMP.Flips.WeilDivisorialSubsheaf.isUnit_of_free`: multiplication by a unit commutes with
  saturation, and a local generator of a Weil divisorial subsheaf is a unit.
* `MMP.Flips.exists_isWShGroup`, `MMP.Flips.WeilDivisorialSubsheaf.stalkSet_mul_inv_unit`:
  `WSh(X)` is an abelian group under `·`, with neutral element `sat(𝒪_X)` and inverse `𝓛⁻¹`
  (FA 16.1.2), with the stalk formulas in codimension `≤ 1`.
* `MMP.Flips.WeilDivisorialSubsheaf.bijective_mulLocalHom_inv`,
  `MMP.Flips.WeilDivisorialSubsheaf.bijective_mulLocalHom`: `𝓛⁻¹ ≅ 𝓗om(𝓛, sat(𝒪_X))` and
  `𝓛⁻¹ · 𝓜 ≅ 𝓗om(𝓛, 𝓜)` by `x ↦ (l ↦ xl)`.
* `MMP.Flips.WeilDivisorialSubsheaf.exists_isIso_tensor_mul`: for `𝓛` locally free,
  `𝓛 ⊗ 𝓛' → 𝓛 · 𝓛'` is an isomorphism.

## Implementation notes

*Local homomorphisms.* `𝓗om_{𝒪_X}(𝓕, 𝓖)(V) = Hom_{𝒪_V}(𝓕|_V, 𝓖|_V)`; for submodules
`𝓕, 𝓖 ⊆ K(X)` such a morphism is a family of `Γ(X, W)`-linear maps `𝓕(W) → 𝓖(W)`, `W ⊆ V`,
compatible with restriction (`MMP.Flips.RationalFunctionsSubmodule.LocalHom`). The isomorphism
of sheaves `x ↦ (l ↦ xl)` is stated as the bijectivity of its map on sections over every open
`V`; it commutes with restriction by construction.

*Submodules over an open.* An `𝒪_V`-submodule of `K(X)|_V` is a submodule of `K(V)` for the open
subscheme `V` (the irreducible components of `V` are the traces of those of `X` meeting `V`), so
the statement on multiplication by a unit is made on an arbitrary scheme `Y` in place of `V`.

*Natural map from the tensor product.* `𝓛 ⊗ 𝓛'` is the sheafified tensor product
(`Stacks.SheafOfModules.OnSpace.monoidal`); the natural map `𝓛 ⊗ 𝓛' → 𝓛 · 𝓛'` is the morphism
sending `a ⊗ b` to `ab` on local sections, which determines it.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

namespace MMP.Flips

open MMP.Mori

/-! ### Local rings of codimension at most one -/

section WshRing

open IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

private lemma wshC_exists_nzd {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsReduced R] (h : ¬ (maximalIdeal R).height = 0) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular R x := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆ ⋃ p ∈ minimalPrimes R, (p : Set R) := by
    intro x hx
    have hx' := hne x hx
    by_contra hxn
    simp only [Set.mem_iUnion, not_exists] at hxn
    apply hx'
    intro a b hab
    simp only [smul_eq_mul] at hab
    have : a - b ∈ sInf (minimalPrimes R) := by
      rw [Submodule.mem_sInf]
      intro p hp
      have hmul : x * (a - b) ∈ p := by rw [mul_sub, hab, sub_self]; exact zero_mem _
      exact (hp.1.1.mem_or_mem hmul).resolve_left (hxn p hp)
    have h0 : sInf (minimalPrimes R) = (⊥ : Ideal R).radical := Ideal.sInf_minimalPrimes
    rw [h0, Ideal.radical_bot_of_isReduced] at this
    exact sub_eq_zero.mp this
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite hfin (⊥ : Ideal R) ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal hp.1.1.ne_top
  have : maximalIdeal R = p := le_antisymm hle hpm
  exact h ((Ideal.height_eq_zero_iff (I := maximalIdeal R)).mpr (this ▸ hp))

private lemma wshC_isCohenMacaulayLocalRing_of_reduced {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsReduced R] (h : ringKrullDim R ≤ 1) : IsCohenMacaulayLocalRing R := by
  have hmax : IsMaxCM R R := by
    by_cases h0 : (maximalIdeal R).height = 0
    · refine ⟨[], by simp, ?_, ?_⟩
      · rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simp)]
        exact RingTheory.Sequence.IsWeaklyRegular.nil R R
      · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0]
        simp
    · obtain ⟨x, hx, hreg⟩ := wshC_exists_nzd h0
      refine ⟨[x], by simpa using hx, ?_, ?_⟩
      · rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hx),
          RingTheory.Sequence.isWeaklyRegular_singleton_iff]
        exact hreg
      · have h1 : (1 : ℕ∞) ≤ (maximalIdeal R).height := Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0)
        have h2 : ((maximalIdeal R).height : WithBot ℕ∞) ≤ 1 := by
          rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
          exact h
        have h3 : (maximalIdeal R).height ≤ 1 := by exact_mod_cast h2
        have h4 : (maximalIdeal R).height = 1 := le_antisymm h3 h1
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h4]
        simp
  have := isMaxCM_iff_depth_eq_ringKrullDim.mp hmax
  show Module.depthSup R (maximalIdeal R) R = Module.supportDim R R
  rw [Module.supportDim_self_eq_ringKrullDim]
  exact this

private noncomputable def wshC_homologyShiftIso {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (i n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (K⟦n⟧)) ≅
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + n)).obj K) := by
  rw [← DerivedCategory.shift_homologyFunctor (ModuleCat.{u} R) i,
    ← DerivedCategory.shift_homologyFunctor (ModuleCat.{u} R) (i + n)]
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso n i (i + n) (by omega)).app K

/-- A normalized dualizing complex over a Noetherian local ring, with residue field lifted to
universe `u`, is also normalized with respect to the residue field in universe `0`. -/
lemma isNormalizedDualizingComplex_ulift_zero {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {ω : DerivedCategory (ModuleCat.{u} A)}
    (h : Dualizing.IsNormalizedDualizingComplex.{u, u} ω) :
    Dualizing.IsNormalizedDualizingComplex.{u, 0} ω :=
  let eU : ULift.{u} (IsLocalRing.ResidueField A) ≃ₗ[IsLocalRing.ResidueField A]
      ULift.{0} (IsLocalRing.ResidueField A) := ULift.moduleEquiv.trans ULift.moduleEquiv.symm
  ⟨h.1, h.2.map fun e => e.trans
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (IsLocalRing.ResidueField A)) 0).mapIso
      (LinearEquiv.toModuleIso eU))⟩

private lemma wshC_isGorensteinLocalRing_iff {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (hCM : IsCohenMacaulayLocalRing R)
    (D : DerivedCategory (ModuleCat.{u} R))
    (hD : Dualizing.IsNormalizedDualizingComplex.{u, u} D) (h : ℕ)
    (hh : ringKrullDim R = (h : WithBot ℕ∞)) :
    Dualizing.IsGorensteinLocalRing R ↔
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(h : ℤ))).obj D ≃ₗ[R] R) := by
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  constructor
  · intro hG
    have hS := Dualizing.LocalDuality.isNormalizedDualizingComplex_single_shift_of_isGorensteinLocalRing_self _ hG h hh
    obtain ⟨e⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hD hS
    have e1 := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(h : ℤ))).mapIso e ≪≫
      wshC_homologyShiftIso S (-(h : ℤ)) (h : ℤ)
    have h0 : (-(h : ℤ)) + (h : ℤ) = 0 := by omega
    rw [h0] at e1
    exact ⟨(e1 ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
      (ModuleCat.of R R)).toLinearEquiv⟩
  · rintro ⟨E⟩
    have hD' := isNormalizedDualizingComplex_ulift_zero hD
    obtain ⟨e⟩ := ((Dualizing.isCohenMacaulay_tfae_dualizingComplex D hD').out 1 3).mp hCM
    have hdim : Dualizing.localRingDimension R = h := by
      have h1 : ((maximalIdeal R).height : WithBot ℕ∞) = h := by
        rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
        exact hh
      have h2 : (maximalIdeal R).height = h := by exact_mod_cast h1
      simp [Dualizing.localRingDimension, h2]
    simp only [Dualizing.dualizingModule, hdim] at e
    let e2 : (DerivedCategory.singleFunctor (ModuleCat.{u} R) (-(h : ℤ))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(h : ℤ))).obj D) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) (-(h : ℤ))).obj (ModuleCat.of R R) :=
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (-(h : ℤ))).mapIso E.toModuleIso
    let e3 : S⟦(h : ℤ)⟧ ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) (-(h : ℤ))).obj
        (ModuleCat.of R R) :=
      ((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso (h : ℤ) (-(h : ℤ)) 0
        (by omega)).app (ModuleCat.of R R)
    have h1 : Dualizing.IsDualizingComplex (S⟦(h : ℤ)⟧) :=
      (Dualizing.isDualizingComplex_iff_of_iso (e ≪≫ e2 ≪≫ e3.symm)).mp hD.1
    have h2 := Dualizing.isDualizingComplex_shift _ h1 (-(h : ℤ))
    exact (Dualizing.isDualizingComplex_iff_of_iso
      ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R)) (h : ℤ) (-(h : ℤ))
        (by omega)).app S)).mp h2

end WshRing

section Gorenstein

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A scheme with a compactification over a field is Noetherian and of finite type over the
field. -/
private lemma wshC_isNoetherian_and_locallyOfFiniteType {π : X ⟶ Spec (.of k)}
    {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) :
    IsNoetherian X ∧ LocallyOfFiniteType π := by
  obtain ⟨-, Xbar, j, hj, πbar, hp, hjp, -⟩ := h
  subst hjp
  have : IsLocallyNoetherian (Spec (.of k)) := by infer_instance
  have : IsLocallyNoetherian Xbar := LocallyOfFiniteType.isLocallyNoetherian πbar
  have : CompactSpace Xbar := QuasiCompact.compactSpace_of_compactSpace πbar
  have : IsNoetherian Xbar := {}
  exact ⟨Stacks.Coherent.isNoetherian_of_isOpenImmersion j, inferInstance⟩

/-- `j^* H^{-d}(π̄^× k) ≅ H^{-d}(K_X)` for the dualizing complex `K_X` of `X` normalized relative
to `k[0]`: `K_X = π^! k = j^* π̄^× k` (Stacks, Tags 0AWJ and 0A9Y), and `j^*` is exact. -/
private lemma wshC_nonempty_restrict_dualizingModuleOverField_iso {π : X ⟶ Spec (.of k)}
    {Xbar : Scheme.{u}} (j : X ⟶ Xbar) [IsOpenImmersion j] (πbar : Xbar ⟶ Spec (.of k))
    [IsProper πbar] (hjp : j ≫ πbar = π) [IsNoetherian X] [LocallyOfFiniteType π] (d : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor j).obj (Stacks.Duality.dualizingModuleOverField πbar d) ≅
      (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
        (normalizedDualizingComplexOverField π).complex.obj.obj) := by
  subst hjp
  have : IsSeparated (j ≫ πbar) := inferInstance
  have : QuasiCompact (j ≫ πbar) := inferInstance
  let hps := Stacks.Duality.isShriekable_of_field (j ≫ πbar)
  let c : CompactificationOf (Over.mk (j ≫ πbar)) :=
    ⟨StructuredArrow.mk (Y := Over.mk πbar) (Over.homMk j rfl),
      ⟨(inferInstance : IsOpenImmersion j), (inferInstance : IsProper πbar)⟩⟩
  let e1 := Stacks.Duality.NormalizedOnOpens.isoUpperShriekPlusNagata
    (hp := isFiniteTypeOverNoetherian_of_field (j ≫ πbar))
    (Stacks.Duality.isDualizingComplex_derivedStructureSheafPlus_of_field k) hps
    (Stacks.Duality.normalizedDualizingComplex (isFiniteTypeOverNoetherian_of_field (j ≫ πbar)) _
      (Stacks.Duality.isDualizingComplex_derivedStructureSheafPlus_of_field k)) c
  let e1' := (ObjectProperty.ι _).mapIso ((ObjectProperty.ι _).mapIso e1)
  let e2 : (Stacks.Duality.quasiCoherentDerivedPullback' j).obj
      (Stacks.Duality.dualizingComplexOverField πbar) ≅ _ :=
    ((Stacks.Duality.restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback j).app _).symm
  let e3 := (ObjectProperty.ι _).mapIso e2
  have e4 := (Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso (-(d : ℤ))
  exact ⟨((e4.app (Stacks.Duality.dualizingComplexOverField πbar).obj).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).mapIso (e3.symm ≪≫ e1'.symm))⟩

/-- `ω ≅ H^{-d}(K_X)` for a dualizing sheaf `ω`, `K_X` normalized relative to `k[0]`. -/
private lemma wshC_nonempty_iso_homology {π : X ⟶ Spec (.of k)}
    {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) [IsNoetherian X]
    [LocallyOfFiniteType π] :
    Nonempty (ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) := by
  obtain ⟨-, Xbar, j, hj, πbar, hp, hjp, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := wshC_nonempty_restrict_dualizingModuleOverField_iso j πbar hjp d
  exact ⟨e ≪≫ e'⟩

private noncomputable def wshC_stalkEquivOfIso (x : X) {F G : X.Modules} (e : F ≅ G) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
    (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
  letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val x
  let f := AlgebraicGeometry.stalkMapLinear F.val G.val e.hom.val x
  let g := AlgebraicGeometry.stalkMapLinear G.val F.val e.inv.val x
  have hf : ∀ (U : X.Opens) (hx : x ∈ U) (s : F.val.obj (op U)),
      f (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx s) =
        TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf U x hx ((e.hom.val.app (op U)).hom s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
      ((PresheafOfModules.toPresheaf _).map e.hom.val) s
  have hg : ∀ (U : X.Opens) (hx : x ∈ U) (s : G.val.obj (op U)),
      g (TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf U x hx s) =
        TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hx ((e.inv.val.app (op U)).hom s) :=
    fun U hx s => TopCat.Presheaf.stalkFunctor_map_germ_apply' U x hx
      ((PresheafOfModules.toPresheaf _).map e.inv.val) s
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · refine LinearMap.ext fun m => ?_
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) G.val.presheaf m
    refine (congrArg f (hg U hx s)).trans ((hf U hx _).trans ?_)
    have h2 : (e.hom.val.app (op U)).hom ((e.inv.val.app (op U)).hom s) = s :=
      congrArg (fun t => (t.val.app (op U)).hom s) e.inv_hom_id
    rw [h2]
    rfl
  · refine LinearMap.ext fun m => ?_
    obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.val.presheaf m
    refine (congrArg g (hf U hx s)).trans ((hg U hx _).trans ?_)
    have h2 : (e.inv.val.app (op U)).hom ((e.hom.val.app (op U)).hom s) = s :=
      congrArg (fun t => (t.val.app (op U)).hom s) e.hom_inv_id
    rw [h2]
    rfl

/-- **In codimension at most one, Gorenstein is equivalent to a free rank-one canonical stalk.**
Let `X` be reduced and of pure dimension `d` over `k` with dualizing sheaf `ω_X`, and `η ∈ X` a
point of codimension `≤ 1`. Then `𝒪_{X,η}` is Cohen–Macaulay, and it is Gorenstein if and only if
`(ω_X)_η` is a free `𝒪_{X,η}`-module of rank one. -/
@[mmp "lem_mmp_foundation_fa16_codimension_one_gorenstein_canonical"]
theorem IsDualizingSheaf.isCohenMacaulayLocalRing_and_isGorenstein_iff [IsReduced X]
    {π : X ⟶ Spec (.of k)} {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) (η : X)
    (hη : Order.coheight η ≤ 1) :
    ∃ _ : IsNoetherianRing (X.presheaf.stalk η),
      IsCohenMacaulayLocalRing (X.presheaf.stalk η) ∧
        (Dualizing.IsGorensteinLocalRing (X.presheaf.stalk η) ↔
          Nonempty (Stacks.Duality.moduleStalkAtPoint ω η ≃ₗ[X.presheaf.stalk η]
            X.presheaf.stalk η)) := by
  obtain ⟨hN, hL⟩ := wshC_isNoetherian_and_locallyOfFiniteType h
  have := hN
  have := hL
  have hl : IsLocallyNoetherian X := hN.toIsLocallyNoetherian
  have hR : IsNoetherianRing (X.presheaf.stalk η) := inferInstance
  obtain ⟨e⟩ := wshC_nonempty_iso_homology h
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨-, hx⟩ := hK3 d h.1
  obtain ⟨D, e', h', hD, -, hh, hed, hiso, -⟩ := hx η
  refine ⟨hR, ?_⟩
  have hh1 : ringKrullDim (X.presheaf.stalk η) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hη
  have hCM := wshC_isCohenMacaulayLocalRing_of_reduced hh1
  refine ⟨hCM, ?_⟩
  obtain ⟨E1⟩ := hiso (-(d : ℤ))
  have hdeg : -(d : ℤ) + (e' : ℤ) = -(h' : ℤ) := by omega
  rw [hdeg] at E1
  rw [wshC_isGorensteinLocalRing_iff hCM D hD h' hh]
  have hh2 := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X)
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val η
  rw [hh2] at E1
  have hω2 := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X) ω.val η
  rw [hω2]
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val η
  let F := (wshC_stalkEquivOfIso η e).trans E1
  constructor
  · rintro ⟨f⟩
    exact ⟨F.trans f⟩
  · rintro ⟨f⟩
    exact ⟨F.symm.trans f⟩

/-- Restriction of `φ` commutes with restriction of sections. -/
lemma rationalFunctionsModule_naturality_apply {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    {U V : X.Opens} (j : V ⟶ U) (g : ω.val.obj (op U)) :
    ((φ.val.app (op V)) ((ω.val.map j.op) g)).1 =
      (rationalFunctionsPresheaf X).map j.op ((φ.val.app (op U) g).1) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (φ.val.naturality j.op) g)

/-- `φ` is linear for sections of the structure sheaf. -/
lemma rationalFunctionsModule_map_smul_apply {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    {W : X.Opens} (r : X.ringCatSheaf.obj.obj (op W)) (g : ω.val.obj (op W)) :
    ((φ.val.app (op W)) (r • g)).1 = (show Γ(X, W) from r) • (φ.val.app (op W) g).1 := by
  have := (φ.val.app (op W)).hom.map_smul r g
  exact congrArg Subtype.val this

/-- On a reduced, locally Noetherian, quasi-compact scheme, the map from the stalk of the
structure sheaf at `η` to the stalk of the sheaf of rational functions is injective. -/
lemma wshC_structure_stalk_injective [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (η : X) :
    Function.Injective (structureStalkToRationalFunctionsStalk X η).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨V, hη, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  have h1 : (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ V η hη r) =
      (rationalFunctionsPresheaf X).germ V η hη ((toRationalFunctionsPresheaf X).app (op V) r) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V η hη (toRationalFunctionsPresheaf X) r
  rw [h1] at ha
  have h0 : (rationalFunctionsPresheaf X).germ V η hη 0 = 0 := map_zero _
  obtain ⟨W, hηW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq (rationalFunctionsPresheaf X) η hη hη _ 0
    (ha.trans h0.symm)
  rw [map_zero] at hW
  have hW' : (toRationalFunctionsPresheaf X).app (op W) (X.presheaf.map iU.op r) = 0 := by
    rw [toRationalFunctionsPresheaf_app_map]; exact hW
  obtain ⟨e, he1, -, he3⟩ := exists_totalQuotientSheaf_ringEquiv_pi_residueField (X := X)
  have hz : toPiResidueField W (X.presheaf.map iU.op r) = 0 := by
    funext ⟨ξ, hξg, hξW⟩
    obtain ⟨Z, hZ⟩ : ∃ Z : irreducibleComponents X, componentGenericPoint X Z = ξ :=
      ⟨genericPoints.component ⟨ξ, hξg⟩, (isGenericPoint_componentGenericPoint X _).eq
        (genericPoints.isGenericPoint ⟨ξ, hξg⟩)⟩
    subst hZ
    have h2 := congrFun hW' ⟨Z, hξW⟩
    have h3 : X.presheaf.germ W (componentGenericPoint X Z) hξW (X.presheaf.map iU.op r) = 0 := h2
    change (X.residue (componentGenericPoint X Z)).hom
      (X.presheaf.germ W (componentGenericPoint X Z) hξW (X.presheaf.map iU.op r)) = 0
    rw [h3, map_zero]
  have hz2 : (X.toTotalQuotientSheaf.hom.app (op W)).hom (X.presheaf.map iU.op r) = 0 := by
    apply (e W).injective
    rw [he1 W, hz, map_zero]
  have hz3 := he3 W (hz2.trans (map_zero _).symm)
  have hr0 : X.presheaf.map iU.op r = 0 := hz3
  rw [← X.presheaf.germ_res_apply iU η hηW r, hr0, map_zero]

/-- Elements of the span of the images of `φ` over `W` are images. -/
private lemma wshC_exists_eq_of_mem_span_image {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (W : X.Opens) {u : ToType ((rationalFunctionsPresheaf X).obj (op W))}
    (hu : u ∈ Submodule.span Γ(X, W)
      {t | ∃ f : ω.val.obj (op W), ((φ.val.app (op W)) f).1 = t}) :
    ∃ f : ω.val.obj (op W), ((φ.val.app (op W)) f).1 = u := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨g, rfl⟩ := hy
    exact ⟨f + g, by rw [map_add]; rfl⟩
  | smul r x _ hx =>
    obtain ⟨f, rfl⟩ := hx
    let r' : X.ringCatSheaf.obj.obj (op W) := r
    exact ⟨r' • f, by
      have := (φ.val.app (op W)).hom.map_smul r' f
      exact congrArg Subtype.val this⟩

/-- A section of `K(X)` over `O` lying in the image sheaf of an injective `φ` is the image of a
section of `ω` over `O`. -/
private lemma wshC_exists_preimage_of_mem_imageSubmodule {ω : X.Modules}
    (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) {O : X.Opens}
    {s : ToType ((rationalFunctionsPresheaf X).obj (op O))}
    (hs : s ∈ (imageSubmodule φ).sections O) :
    ∃ t : ω.val.obj (op O), ((φ.val.app (op O)) t).1 = s := by
  rw [imageSubmodule, RationalFunctionsSubmodule.mem_localClosure_iff] at hs
  choose W i hyW hP using hs
  choose f hf using fun y hy => wshC_exists_eq_of_mem_span_image φ (W y hy) (hP y hy)
  let ι := {y : X // y ∈ O}
  let U : ι → X.Opens := fun y => W y.1 y.2
  let sf : ∀ y : ι, ω.presheaf.obj (op (U y)) := fun y => f y.1 y.2
  have hcompat : TopCat.Presheaf.IsCompatible ω.presheaf U sf := by
    intro a b
    refine hφ (U a ⊓ U b) (Subtype.ext ?_)
    have e1 := rationalFunctionsModule_naturality_apply φ
      (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)) (sf a)
    have e2 := rationalFunctionsModule_naturality_apply φ
      (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)) (sf b)
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [show ((φ.val.app (op (U a))) (sf a)).1 = _ from hf a.1 a.2,
      show ((φ.val.app (op (U b))) (sf b)).1 = _ from hf b.1 b.2]
    rfl
  obtain ⟨t0, ht0, -⟩ :=
    (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing ω.presheaf).mp ω.isSheaf U sf hcompat
  have hle : O ≤ iSup U := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyW y hy⟩
  refine ⟨(ω.val.map (homOfLE hle).op) t0, funext fun Z => ?_⟩
  let y : ι := ⟨componentGenericPoint X Z.1, Z.2⟩
  have hsy : (ω.val.map (i y.1 y.2).op) ((ω.val.map (homOfLE hle).op) t0) = sf y := by
    have := ht0 y
    rw [← this]
    change ω.presheaf.map _ (ω.presheaf.map _ t0) = ω.presheaf.map _ t0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have h1 := rationalFunctionsModule_naturality_apply φ (i y.1 y.2) ((ω.val.map (homOfLE hle).op) t0)
  rw [hsy, show ((φ.val.app (op (U y))) (sf y)).1 = _ from hf y.1 y.2] at h1
  exact (congrFun h1 ⟨Z.1, hyW y.1 y.2⟩).symm

/-- The image under `φ` of a section of `ω` over `V` is a section of `imageSubmodule φ` over
`V`. -/
lemma val_app_mem_imageSubmodule {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    {V : X.Opens} (γ : ω.val.obj (op V)) : (φ.val.app (op V) γ).1 ∈ (imageSubmodule φ).sections V := by
  rw [imageSubmodule, RationalFunctionsSubmodule.mem_localClosure_iff]
  intro x hx
  refine ⟨V, 𝟙 V, hx, ?_⟩
  rw [rationalFunctionsPresheaf_map_id_apply]
  exact Submodule.subset_span ⟨γ, rfl⟩

private lemma wshC_germ_eq_iff {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) {η : X} {V V' : X.Opens}
    (hV : η ∈ V) (hV' : η ∈ V') (γ : ω.val.obj (op V)) (γ' : ω.val.obj (op V')) :
    TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V η hV γ =
        TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V' η hV' γ' ↔
      (rationalFunctionsPresheaf X).germ V η hV (φ.val.app (op V) γ).1 =
        (rationalFunctionsPresheaf X).germ V' η hV' (φ.val.app (op V') γ').1 := by
  constructor
  · intro h
    obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (C := Ab.{u}) ω.val.presheaf η hV hV' γ γ' h
    rw [← TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) iU η hW,
      ← TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) iV η hW,
      ← rationalFunctionsModule_naturality_apply φ iU γ,
      ← rationalFunctionsModule_naturality_apply φ iV γ']
    exact congrArg _ (congrArg (fun z => (φ.val.app (op W) z).1) e)
  · intro h
    obtain ⟨W, hW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (rationalFunctionsPresheaf X) η hV hV' _ _ h
    rw [← rationalFunctionsModule_naturality_apply φ iU γ,
      ← rationalFunctionsModule_naturality_apply φ iV γ'] at e
    have e2 : ω.val.map iU.op γ = ω.val.map iV.op γ' := hφ W (Subtype.ext e)
    have h1 := TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf iU η hW γ
    have h2 := TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf iV η hW γ'
    exact h1.symm.trans ((congrArg (fun z => (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W η hW) z) e2).trans h2)

private lemma wshC_germ_smul_K {W : X.Opens} {η : X} (hW : η ∈ W) (b : Γ(X, W))
    (t : ToType ((rationalFunctionsPresheaf X).obj (op W))) :
    (rationalFunctionsPresheaf X).germ W η hW (b • t) =
      (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ W η hW b) *
        (rationalFunctionsPresheaf X).germ W η hW t := by
  have h1 : (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ W η hW b) =
      (rationalFunctionsPresheaf X).germ W η hW ((toRationalFunctionsPresheaf X).app (op W) b) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply W η hW (toRationalFunctionsPresheaf X) b
  rw [h1, ← map_mul]
  congr 1

private lemma wshC_smul_germ {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X) (η : X)
    {V : X.Opens} (hV : η ∈ V) (γ : ω.val.obj (op V)) (a : X.presheaf.stalk η) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
    ∃ (W : X.Opens) (hW : η ∈ W) (δ : ω.val.obj (op W)),
      a • TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V η hV γ =
        TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W η hW δ ∧
      (rationalFunctionsPresheaf X).germ W η hW (φ.val.app (op W) δ).1 =
        (structureStalkToRationalFunctionsStalk X η).hom a *
          (rationalFunctionsPresheaf X).germ V η hV (φ.val.app (op V) γ).1 := by
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
  obtain ⟨V₁, h1, β, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  let W := V₁ ⊓ V
  have hW : η ∈ W := ⟨h1, hV⟩
  let iβ : W ⟶ V₁ := homOfLE inf_le_left
  let iγ : W ⟶ V := homOfLE inf_le_right
  let γ' : ω.val.obj (op W) := ω.val.map iγ.op γ
  let β' : X.ringCatSheaf.obj.obj (op W) := X.presheaf.map iβ.op β
  refine ⟨W, hW, β' • γ', ?_, ?_⟩
  · have e1 := X.presheaf.germ_res_apply iβ η hW β
    have e2 := TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf iγ η hW γ
    have e3 := PresheafOfModules.germ_smul (R := X.presheaf) ω.val η W hW β' γ'
    refine Eq.trans ?_ e3.symm
    exact congrArg₂ (fun x y => x • y) e1.symm e2.symm
  · have e4 := rationalFunctionsModule_map_smul_apply φ β' γ'
    have e5 := rationalFunctionsModule_naturality_apply φ iγ γ
    have e6 := wshC_germ_smul_K hW (show Γ(X, W) from β') (φ.val.app (op W) γ').1
    have e7 := TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) iγ η hW (φ.val.app (op V) γ).1
    have e8 := X.presheaf.germ_res_apply iβ η hW β
    rw [e4, e6]
    exact congrArg₂ (fun x y => x * y) (congrArg _ e8) ((congrArg _ e5).trans e7)

private lemma wshC_nonempty_linearEquiv_of_principal [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) (η : X)
    (f : ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hf : (imageSubmodule φ).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (f : (rationalFunctionsPresheaf X).stalk η) *
        (structureStalkToRationalFunctionsStalk X η).hom a) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
    Nonempty (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf η ≃ₗ[X.presheaf.stalk η]
      X.presheaf.stalk η) := by
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
  have hfmem : (f : (rationalFunctionsPresheaf X).stalk η) ∈ (imageSubmodule φ).stalkSet η := by
    rw [hf]; exact ⟨1, by simp⟩
  obtain ⟨V, hηV, t, ht, hgerm⟩ := hfmem
  obtain ⟨γ, hγ⟩ := wshC_exists_preimage_of_mem_imageSubmodule φ hφ ht
  let g := TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V η hηV γ
  have hfg : (rationalFunctionsPresheaf X).germ V η hηV (φ.val.app (op V) γ).1 =
      (f : (rationalFunctionsPresheaf X).stalk η) := by rw [hγ]; exact hgerm
  let Λ : X.presheaf.stalk η →ₗ[X.presheaf.stalk η]
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf η) :=
    LinearMap.toSpanSingleton _ _ g
  have hΛ : Function.Bijective Λ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨W, hW, δ, h1, h2⟩ := wshC_smul_germ φ η hηV γ a
      have ha' : a • g = 0 := ha
      have h3 : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W η hW δ =
          TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W η hW 0 := by
        rw [← h1, map_zero]; exact ha'
      have h4 := (wshC_germ_eq_iff φ hφ hW hW δ 0).mp h3
      have h5 : (φ.val.app (op W) 0).1 = 0 := by rw [map_zero]; rfl
      rw [h5, map_zero, h2, hfg] at h4
      have h6 : (structureStalkToRationalFunctionsStalk X η).hom a = 0 := by
        have := (Units.isUnit f).mul_right_eq_zero.mp (by rw [mul_comm]; exact h4)
        exact this
      exact wshC_structure_stalk_injective η (h6.trans (map_zero _).symm)
    · intro m
      obtain ⟨V', hV', γ', rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) ω.val.presheaf m
      have hmem : (rationalFunctionsPresheaf X).germ V' η hV' (φ.val.app (op V') γ').1 ∈
          (imageSubmodule φ).stalkSet η :=
        ⟨V', hV', _, val_app_mem_imageSubmodule φ γ', rfl⟩
      rw [hf] at hmem
      obtain ⟨a, ha⟩ := hmem
      refine ⟨a, ?_⟩
      obtain ⟨W, hW, δ, h1, h2⟩ := wshC_smul_germ φ η hηV γ a
      show a • g = _
      refine h1.trans ((wshC_germ_eq_iff φ hφ hW hV' δ γ').mpr ?_)
      rw [h2, hfg, ← ha]
      exact mul_comm _ _
  exact ⟨(LinearEquiv.ofBijective Λ hΛ).symm⟩

/-- The `Γ(X, U)`-linear map `ω(U) → φ(ω)(U)`. -/
noncomputable def toImageSubmoduleSections {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (U : X.Opens) :
    ω.val.obj (op U) →ₗ[X.ringCatSheaf.obj.obj (op U)] ((imageSubmodule φ).presheafAb.obj (op U)) where
  toFun γ := ⟨(φ.val.app (op U) γ).1, val_app_mem_imageSubmodule φ γ⟩
  map_add' a b := Subtype.ext (by
    have := congrArg Subtype.val (map_add (φ.val.app (op U)).hom a b)
    exact this)
  map_smul' r γ := Subtype.ext (rationalFunctionsModule_map_smul_apply φ r γ)

/-- If `φ` is injective on sections, then `toImageSubmoduleSections φ U` is bijective. -/
lemma bijective_toImageSubmoduleSections {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) (U : X.Opens) :
    Function.Bijective (toImageSubmoduleSections φ U) := by
  constructor
  · intro a b hab
    have h1 := congrArg Subtype.val hab
    exact hφ U (Subtype.ext h1)
  · rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := wshC_exists_preimage_of_mem_imageSubmodule φ hφ hs
    exact ⟨t, Subtype.ext ht⟩

/-- If `φ : ω ⟶ K(X)` is injective on sections, then `ω` is isomorphic to its image
`imageSubmodule φ`. -/
noncomputable def isoImageSubmodule {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) :
    ω ≅ (imageSubmodule φ).toModules :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (LinearEquiv.ofBijective (toImageSubmoduleSections φ V.unop)
        (bijective_toImageSubmoduleSections φ hφ V.unop)).toModuleIso)
      (fun V W i => by
        ext γ
        exact Subtype.ext (rationalFunctionsModule_naturality_apply φ i.unop γ)))

/-- Distinct components through `η` give incomparable primes of `𝒪_{X,η}`. -/
private lemma wshC_comap_not_le [IsReduced X] {η : X} {Z Z₀ : irreducibleComponents X}
    (hZ : η ∈ Z.1) (hZ₀ : η ∈ Z₀.1)
    (hle : Ideal.comap (stalkToRationalFunctions X hZ).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z))) ≤
      Ideal.comap (stalkToRationalFunctions X hZ₀).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z₀)))) : Z = Z₀ := by
  let q : ∀ {Z : irreducibleComponents X}, η ∈ Z.1 → Spec (X.presheaf.stalk η) :=
    fun {Z} hZ => (Spec.map (stalkToRationalFunctions X hZ)) (IsLocalRing.closedPoint _)
  have hq : ∀ {Z : irreducibleComponents X} (hZ : η ∈ Z.1),
      X.fromSpecStalk η (q hZ) = componentGenericPoint X Z := by
    intro Z hZ
    have h1 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      ((isGenericPoint_componentGenericPoint X Z).specializes hZ)
    have h2 := congrArg (fun f => f (IsLocalRing.closedPoint (X.presheaf.stalk (componentGenericPoint X Z)))) h1
    simp only [Scheme.fromSpecStalk_closedPoint] at h2
    exact h2
  have hqle : (q hZ) ⤳ (q hZ₀) :=
    (PrimeSpectrum.le_iff_specializes (R := X.presheaf.stalk η) (q hZ) (q hZ₀)).mp hle
  have hξ : componentGenericPoint X Z ⤳ componentGenericPoint X Z₀ := by
    rw [← hq hZ, ← hq hZ₀]
    exact hqle.map (X.fromSpecStalk η).continuous
  have h1 : componentGenericPoint X Z₀ ∈ Z.1 := by
    rw [← (isGenericPoint_componentGenericPoint X Z).def]
    exact hξ.mem_closure
  have h2 : Z₀.1 ⊆ Z.1 := by
    rw [← (isGenericPoint_componentGenericPoint X Z₀).def]
    exact closure_minimal (by simpa using h1) (isClosed_of_mem_irreducibleComponents _ Z.2)
  exact Subtype.ext (le_antisymm (Z₀.2.2 Z.2.1 h2) h2)

private lemma wshC_exists_elem_vanishing_others [IsReduced X] [AlgebraicGeometry.IsNoetherian X]
    (η : X) (Z₀ : irreducibleComponents X) (hZ₀ : η ∈ Z₀.1) :
    ∃ a : X.presheaf.stalk η, (stalkToRationalFunctions X hZ₀).hom a ≠ 0 ∧
      ∀ (Z : irreducibleComponents X) (hZ : η ∈ Z.1), Z ≠ Z₀ →
        (stalkToRationalFunctions X hZ).hom a = 0 := by
  classical
  have hfin : (irreducibleComponents X).Finite := finite_irreducibleComponents_of_isNoetherian
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  let T := {Z : irreducibleComponents X // η ∈ Z.1}
  have : Fintype T := Fintype.ofFinite T
  let P : T → Ideal (X.presheaf.stalk η) := fun t =>
    Ideal.comap (stalkToRationalFunctions X t.2).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X t.1)))
  have hPprime : ∀ t, (P t).IsPrime := fun t =>
    Ideal.IsPrime.comap _
  let t₀ : T := ⟨Z₀, hZ₀⟩
  have hnot : ¬ (Finset.univ.erase t₀).prod P ≤ P t₀ := by
    rw [(hPprime t₀).prod_le]
    rintro ⟨t, ht, hle⟩
    exact (Finset.mem_erase.mp ht).1 (Subtype.ext (wshC_comap_not_le t.2 hZ₀ hle))
  obtain ⟨a, ha, ha0⟩ := SetLike.not_le_iff_exists.mp hnot
  have hm : ∀ Z : irreducibleComponents X,
      IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z)) = ⊥ := fun Z =>
    (IsLocalRing.isField_iff_maximalIdeal_eq).mp (RationalFunctions.isField_stalk X Z)
  refine ⟨a, ?_, ?_⟩
  · intro h
    apply ha0
    show _ ∈ IsLocalRing.maximalIdeal _
    rw [h]
    exact zero_mem _
  · intro Z hZ hne
    have h1 : a ∈ P ⟨Z, hZ⟩ :=
      (Finset.inf_le (Finset.mem_erase.mpr ⟨fun h => hne (congrArg Subtype.val h),
        Finset.mem_univ _⟩) : (Finset.univ.erase t₀).inf P ≤ P ⟨Z, hZ⟩)
        (Ideal.prod_le_inf (s := Finset.univ.erase t₀) (f := P) ha)
    have h3 : (stalkToRationalFunctions X hZ).hom a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z)) := h1
    rw [hm Z] at h3
    exact h3

private lemma wshC_stalkSet_eq_range_of_linearEquiv {ω : X.Modules}
    (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) (η : X)
    (e : letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf η ≃ₗ[X.presheaf.stalk η]
        X.presheaf.stalk η))
    {V : X.Opens} (hV : η ∈ V) (γ : ω.val.obj (op V))
    (hg : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V η hV γ = e.symm 1) :
    (imageSubmodule φ).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (rationalFunctionsPresheaf X).germ V η hV (φ.val.app (op V) γ).1 *
        (structureStalkToRationalFunctionsStalk X η).hom a := by
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
  ext y
  constructor
  · rintro ⟨U, hU, t, ht, rfl⟩
    obtain ⟨γ', hγ'⟩ := wshC_exists_preimage_of_mem_imageSubmodule φ hφ ht
    let m := TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U η hU γ'
    let b := e m
    have hm : m = b • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
      exact (e.symm_apply_apply m).symm
    obtain ⟨W, hW, δ, h1, h2⟩ := wshC_smul_germ φ η hV γ b
    have h3 : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U η hU γ' =
        TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W η hW δ := by
      refine hm.trans ?_
      rw [← hg]
      exact h1
    have h4 := (wshC_germ_eq_iff φ hφ hU hW γ' δ).mp h3
    refine ⟨b, ?_⟩
    show (rationalFunctionsPresheaf X).germ V η hV (φ.val.app (op V) γ).1 * _ = _
    rw [mul_comm, ← h2, ← h4, hγ']
  · rintro ⟨b, rfl⟩
    obtain ⟨W, hW, δ, h1, h2⟩ := wshC_smul_germ φ η hV γ b
    refine ⟨W, hW, _, val_app_mem_imageSubmodule φ δ, ?_⟩
    rw [h2, mul_comm]

private lemma wshC_ne_zero_of_linearEquiv [IsReduced X] [AlgebraicGeometry.IsNoetherian X]
    {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) (η : X)
    (e : letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf η ≃ₗ[X.presheaf.stalk η]
        X.presheaf.stalk η))
    {V : X.Opens} (hV : η ∈ V) (γ : ω.val.obj (op V))
    (hg : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V η hV γ = e.symm 1)
    {Y : X.Opens} (hηY : η ∈ Y)
    (hηZ : ∀ Z' : irreducibleComponents X, componentGenericPoint X Z' ∈ Y → η ∈ Z'.1)
    (Z : irreducibleComponents X) (hZ : η ∈ Z.1) (hZV : componentGenericPoint X Z ∈ V) :
    (φ.val.app (op V) γ).1 ⟨Z, hZV⟩ ≠ 0 := by
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
  intro h0
  obtain ⟨a, ha1, ha2⟩ := wshC_exists_elem_vanishing_others η Z hZ
  obtain ⟨V₁, h1, β, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
  let W : X.Opens := V₁ ⊓ V ⊓ Y
  have hW : η ∈ W := ⟨⟨h1, hV⟩, hηY⟩
  let iβ : W ⟶ V₁ := homOfLE (inf_le_left.trans inf_le_left)
  let iV : W ⟶ V := homOfLE (inf_le_left.trans inf_le_right)
  let β' : Γ(X, W) := X.presheaf.map iβ.op β
  have hu : β' • (rationalFunctionsPresheaf X).map iV.op (φ.val.app (op V) γ).1 = 0 := by
    funext ⟨Z', hZ'⟩
    show X.presheaf.germ W _ hZ' β' * (φ.val.app (op V) γ).1 ⟨Z', iV.le hZ'⟩ = 0
    have hZ'η := hηZ Z' hZ'.2
    by_cases hne : Z' = Z
    · subst hne
      rw [h0, mul_zero]
    · have h5 := ha2 Z' hZ'η hne
      have h6 : X.presheaf.germ W _ hZ' β' = 0 := by
        have h7 := X.presheaf.germ_res_apply iβ _ hZ' β
        have h8 := X.presheaf.germ_stalkSpecializes_apply (U := V₁) h1
          ((isGenericPoint_componentGenericPoint X Z').specializes hZ'η) β
        have h9 : (stalkToRationalFunctions X hZ'η).hom (X.presheaf.germ V₁ η h1 β) =
            X.presheaf.germ V₁ (componentGenericPoint X Z') (iβ.le hZ') β := h8
        show X.presheaf.germ W _ hZ' (X.presheaf.map iβ.op β) = 0
        rw [h7]
        exact h9.symm.trans h5
      rw [h6, zero_mul]
  have hsf : (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ V₁ η h1 β) *
      (rationalFunctionsPresheaf X).germ V η hV (φ.val.app (op V) γ).1 = 0 := by
    have h10 := wshC_germ_smul_K hW β'
      ((rationalFunctionsPresheaf X).map iV.op (φ.val.app (op V) γ).1)
    rw [hu, map_zero] at h10
    have h11 := TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) iV η hW
      (φ.val.app (op V) γ).1
    have h12 := X.presheaf.germ_res_apply iβ η hW β
    rw [h11, h12] at h10
    exact h10.symm
  obtain ⟨W₂, hW₂, δ, h13, h14⟩ := wshC_smul_germ φ η hV γ (X.presheaf.germ V₁ η h1 β)
  have h15 : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W₂ η hW₂ δ =
      TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf W₂ η hW₂ 0 := by
    refine (wshC_germ_eq_iff φ hφ hW₂ hW₂ δ 0).mpr ?_
    have h5 : (φ.val.app (op W₂) 0).1 = 0 := by
      rw [map_zero]
      rfl
    rw [h5, map_zero, h14]
    exact hsf
  have h16 : (X.presheaf.germ V₁ η h1 β) • e.symm 1 = 0 := by
    rw [← hg, h13, h15, map_zero]
  have h17 : e.symm (X.presheaf.germ V₁ η h1 β) = 0 := by
    have : e.symm (X.presheaf.germ V₁ η h1 β) = (X.presheaf.germ V₁ η h1 β) • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    exact this.trans h16
  apply ha1
  rw [e.symm.map_eq_zero_iff.mp h17, map_zero]

private lemma wshC_exists_unit_of_linearEquiv [IsReduced X] [AlgebraicGeometry.IsNoetherian X]
    {ω : X.Modules} (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) (η : X)
    (e : letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf η ≃ₗ[X.presheaf.stalk η]
        X.presheaf.stalk η)) :
    ∃ f : ((rationalFunctionsPresheaf X).stalk η)ˣ,
      (imageSubmodule φ).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        (f : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a := by
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val η
  obtain ⟨V, hV, γ, hg⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) ω.val.presheaf (e.symm 1)
  let s₀ := (φ.val.app (op V) γ).1
  have hfin : (irreducibleComponents X).Finite := finite_irreducibleComponents_of_isNoetherian
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  let S : Set (irreducibleComponents X) := {Z' | η ∉ Z'.1}
  let C : Set X := ⋃ Z' ∈ S, Z'.1
  have hC : IsClosed C :=
    (Set.toFinite S).isClosed_biUnion fun Z' _ => isClosed_of_mem_irreducibleComponents _ Z'.2
  let Y : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  have hηY : η ∈ Y := by
    intro hmem
    obtain ⟨Z', hZ', hη⟩ := Set.mem_iUnion₂.mp hmem
    exact hZ' hη
  have hηZ : ∀ Z' : irreducibleComponents X, componentGenericPoint X Z' ∈ Y → η ∈ Z'.1 := by
    intro Z' hZ'
    by_contra hη
    exact hZ' (Set.mem_iUnion₂.mpr ⟨Z', hη, (isGenericPoint_componentGenericPoint X Z').mem⟩)
  have hunit : IsUnit ((rationalFunctionsPresheaf X).germ V η hV s₀) := by
    let U' : X.Opens := V ⊓ Y
    have hU' : η ∈ U' := ⟨hV, hηY⟩
    let iU : U' ⟶ V := homOfLE inf_le_left
    let s' : ToType ((rationalFunctionsPresheaf X).obj (op U')) := fun Z' =>
      Ring.inverse (s₀ ⟨Z'.1, iU.le Z'.2⟩)
    have hmul : (rationalFunctionsPresheaf X).map iU.op s₀ * s' = 1 := by
      funext Z'
      show s₀ ⟨Z'.1, iU.le Z'.2⟩ * Ring.inverse (s₀ ⟨Z'.1, iU.le Z'.2⟩) = 1
      refine Ring.mul_inverse_cancel _ ?_
      have hne := wshC_ne_zero_of_linearEquiv φ hφ η e hV γ hg hηY hηZ Z'.1
        (hηZ Z'.1 Z'.2.2) (iU.le Z'.2)
      let := (RationalFunctions.isField_stalk X Z'.1).toField
      exact Ne.isUnit hne
    refine isUnit_iff_exists_inv.mpr ⟨(rationalFunctionsPresheaf X).germ U' η hU' s', ?_⟩
    have h11 := TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) iU η hU' s₀
    show (rationalFunctionsPresheaf X).germ V η hV s₀ * _ = 1
    rw [← h11, ← map_mul, hmul, map_one]
  exact ⟨hunit.unit, wshC_stalkSet_eq_range_of_linearEquiv φ hφ η e hV γ hg⟩

private lemma wshC_isCoherent_image [IsReduced X] {π : X ⟶ Spec (.of k)} {d : ℕ}
    {ω : X.Modules} (h : IsDualizingSheaf π d ω) (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) :
    SheafOfModules.IsCoherent (imageSubmodule φ).toModules := by
  obtain ⟨hN, hL⟩ := wshC_isNoetherian_and_locallyOfFiniteType h
  have := hN
  have := hL
  obtain ⟨e⟩ := wshC_nonempty_iso_homology h
  have hcoh : _root_.SheafOfModules.IsCoherent ω :=
    AlgebraicGeometry.isCoherent_of_moduleIso e.symm
      ((normalizedDualizingComplexOverField_spec π).2.1 (-(d : ℤ)))
  exact AlgebraicGeometry.isCoherent_of_moduleIso (isoImageSubmodule φ hφ) hcoh

/-- **FA 16.3.3.** Let `X` be reduced and of pure dimension `d` over `k` and `φ : ω_X → K(X)`
injective and `𝒪_X`-linear. Then `φ(ω_X)` is a Weil divisorial subsheaf if and only if `𝒪_{X,η}`
is Gorenstein for every point `η ∈ X` of codimension `≤ 1`. -/
@[mmp "lem_fa16a_dualizing_divisorial_iff_gorenstein_codim_one"]
theorem IsDualizingSheaf.exists_weilDivisorialSubsheaf_iff [IsReduced X] {π : X ⟶ Spec (.of k)}
    {d : ℕ} {ω : X.Modules} (h : IsDualizingSheaf π d ω) (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) :
    (∃ L : WeilDivisorialSubsheaf X, L.toRationalFunctionsSubmodule = imageSubmodule φ) ↔
      ∀ η : X, Order.coheight η ≤ 1 → ∃ _ : IsNoetherianRing (X.presheaf.stalk η),
        Dualizing.IsGorensteinLocalRing (X.presheaf.stalk η) := by
  obtain ⟨hN, hL⟩ := wshC_isNoetherian_and_locallyOfFiniteType h
  have := hN
  have := hL
  have hl : IsLocallyNoetherian X := hN.toIsLocallyNoetherian
  have hG : ∀ η : X, Order.coheight η ≤ 1 → ∃ _ : IsNoetherianRing (X.presheaf.stalk η),
      (Dualizing.IsGorensteinLocalRing (X.presheaf.stalk η) ↔
        letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          ω.val η
        Nonempty (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf η ≃ₗ[X.presheaf.stalk η]
          X.presheaf.stalk η)) := by
    intro η hη
    obtain ⟨hR, -, hiff⟩ := h.isCohenMacaulayLocalRing_and_isGorenstein_iff η hη
    refine ⟨hR, ?_⟩
    have hω2 := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X) ω.val η
    rw [hiff, hω2]
    exact Iff.rfl
  constructor
  · rintro ⟨L, hL⟩ η hη
    obtain ⟨hR, hiff'⟩ := hG η hη
    refine ⟨hR, hiff'.mpr ?_⟩
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    rw [hL] at hf
    exact wshC_nonempty_linearEquiv_of_principal φ hφ η f hf
  · intro hall
    refine ⟨{ toRationalFunctionsSubmodule := imageSubmodule φ
              isCoherent := wshC_isCoherent_image h φ hφ
              principal_codim_one := ?_
              isSaturated := h.isSaturated_image φ hφ }, rfl⟩
    intro η hη
    obtain ⟨hR, hiff'⟩ := hG η hη
    obtain ⟨hR', hGor⟩ := hall η hη
    exact wshC_exists_unit_of_linearEquiv φ hφ η (hiff'.mp hGor).some

end Gorenstein

section WShB1Infra

variable {X : Scheme.{u}}

section QCCriterion

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable [IsReduced X]

private theorem wshB_germ_eq_zero_of_notMem_basicOpen {U : X.Opens} (a : Γ(X, U))
    {Z : irreducibleComponents X} (hZ : componentGenericPoint X Z ∈ U)
    (ha : componentGenericPoint X Z ∉ X.basicOpen a) :
    X.presheaf.germ U _ hZ a = 0 := by
  by_contra h
  refine ha ((Scheme.mem_basicOpen X a _ hZ).mpr ?_)
  obtain ⟨g, hg⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel h
  exact ⟨⟨_, g, hg, by rw [mul_comm]; exact hg⟩, rfl⟩

/-- **Quasi-coherence criterion for submodules of `K(X)`.** -/
private theorem wshB_isQuasicoherent (F : RationalFunctionsSubmodule X)
    (H : ∀ (U : X.Opens), IsAffineOpen U → ∀ (a : Γ(X, U)) (t : ToType ((rationalFunctionsPresheaf X).obj
        (op (X.basicOpen a)))), t ∈ F.sections (X.basicOpen a) →
      ∃ (n : ℕ) (s : ToType ((rationalFunctionsPresheaf X).obj (op U))), s ∈ F.sections U ∧
        (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op s =
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) ^ n • t) :
    F.toModules.IsQuasicoherent := by
  refine Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ
    _ fun U hU a => ?_
  let := moduleOfLE F.toModules (X.basicOpen_le a)
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · have hVU : X.basicOpen a ≤ U := X.basicOpen_le a
    have hu : IsUnit (X.presheaf.map (homOfLE hVU).op a) :=
      X.toRingedSpace.isUnit_res_basicOpen a
    have ha : ∀ ψ : Γ(F.toModules, X.basicOpen a),
        a • ψ = (X.presheaf.map (homOfLE hVU).op a) • ψ := fun _ => rfl
    refine (Module.End.isUnit_iff _).mpr ⟨fun ψ₁ ψ₂ h => ?_, fun ψ => ?_⟩
    · simp only [Module.algebraMap_end_apply, ha] at h
      exact (hu.smul_left_cancel).mp h
    · refine ⟨((hu.unit⁻¹ : (Γ(X, X.basicOpen a))ˣ) : Γ(X, X.basicOpen a)) • ψ, ?_⟩
      simp only [Module.algebraMap_end_apply, ha]
      change (hu.unit : Γ(X, X.basicOpen a)) • ((hu.unit⁻¹ : (Γ(X, X.basicOpen a))ˣ) :
        Γ(X, X.basicOpen a)) • ψ = ψ
      rw [smul_smul, hu.unit.mul_inv, one_smul]
  · intro ψ
    obtain ⟨n, s, hs, hs'⟩ := H U hU a ψ.1 ψ.2
    refine ⟨n, (⟨s, hs⟩ : F.sections U), Subtype.ext ?_⟩
    show (X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ n)) • ψ.1 =
      (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op s
    rw [map_pow]
    exact hs'.symm
  · intro φ hφ
    refine ⟨1, Subtype.ext ?_⟩
    show a ^ 1 • φ.1 = 0
    rw [pow_one]
    funext Z
    show X.presheaf.germ U _ Z.2 a * φ.1 Z = 0
    by_cases hZ : componentGenericPoint X Z.1 ∈ X.basicOpen a
    · have := congrFun (congrArg Subtype.val hφ) ⟨Z.1, hZ⟩
      have h0 : φ.1 Z = 0 := this
      rw [h0, mul_zero]
    · rw [wshB_germ_eq_zero_of_notMem_basicOpen a Z.2 hZ, zero_mul]

end QCCriterion

section CoherentCriterion

/-- **A quasi-coherent module with finite sections over every affine open is coherent.** -/
private theorem wshB_isCoherent_of_finite [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsQuasicoherent]
    (h : ∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)) :
    SheafOfModules.IsCoherent F := by
  have hft : F.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn F
      (fun V : X.affineOpens => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V => V.2)
      fun V => Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
        F V (h V.1 V.2)
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType F

end CoherentCriterion

section InjRF

/-- On a reduced Noetherian scheme `𝒪_X(V) → K(X)(V)` is injective. -/
theorem injective_toRationalFunctionsPresheaf_app [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (V : X.Opens) :
    Function.Injective ((toRationalFunctionsPresheaf X).app (op V)) := by
  obtain ⟨e, he1, -, he3⟩ := exists_totalQuotientSheaf_ringEquiv_pi_residueField (X := X)
  have h1 : Function.Injective (toPiResidueField V) := by
    intro a b hab
    apply he3 V
    apply (e V).injective
    rw [he1, he1]
    exact hab
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply h1
  rw [map_zero]
  funext η
  obtain ⟨η, hη1, hη2⟩ := η
  let Z : irreducibleComponents X := ⟨closure {η}, hη1⟩
  have hcg : componentGenericPoint X Z = η :=
    (isGenericPoint_componentGenericPoint X Z).eq (isGenericPoint_closure (x := η))
  have hZ : componentGenericPoint X Z ∈ V := hcg ▸ hη2
  have hz : X.presheaf.germ V _ hZ s = 0 := congrFun hs ⟨Z, hZ⟩
  have key : ∀ (x y : X) (h : x = y) (hx : x ∈ V) (hy : y ∈ V),
      X.presheaf.germ V x hx s = 0 → X.presheaf.germ V y hy s = 0 := by
    rintro x y rfl hx hy; exact id
  have := key _ _ hcg hZ hη2 hz
  show (X.presheaf.germ V η hη2 ≫ X.residue η).hom s = 0
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  have h2 : (X.presheaf.germ V η hη2).hom s = 0 := this
  rw [h2, map_zero]

end InjRF

section UnitSections

/-- A section of `𝒪_X ⊆ K(X)` over `V` is the image of a section of `𝒪_X` over `V`. -/
theorem exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] {V : X.Opens} {t : ToType ((rationalFunctionsPresheaf X).obj (op V))}
    (ht : t ∈ (RationalFunctionsSubmodule.unit X).sections V) :
    ∃ r : Γ(X, V), (toRationalFunctionsPresheaf X).app (op V) r = t := by
  choose W i hxW hW using fun x : V => ht x.1 x.2
  have hr : ∀ x : V, ∃ r : Γ(X, W x), (toRationalFunctionsPresheaf X).app (op (W x)) r =
      (rationalFunctionsPresheaf X).map (i x).op t := fun x => by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hW x)
    exact ⟨r, hr⟩
  choose r hr using hr
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W r := by
    intro x y
    apply injective_toRationalFunctionsPresheaf_app
    show (toRationalFunctionsPresheaf X).app (op (W x ⊓ W y))
        (X.presheaf.map (Opens.infLELeft (W x) (W y)).op (r x)) =
      (toRationalFunctionsPresheaf X).app (op (W x ⊓ W y))
        (X.presheaf.map (Opens.infLERight (W x) (W y)).op (r y))
    rw [toRationalFunctionsPresheaf_app_map, toRationalFunctionsPresheaf_app_map, hr x, hr y,
      rationalFunctionsPresheaf_map_map _ _ (Opens.infLELeft (W x) (W y) ≫ i x),
      rationalFunctionsPresheaf_map_map _ _ (Opens.infLELeft (W x) (W y) ≫ i x)]
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V i
    (fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩) r hcompat
  refine ⟨g, ?_⟩
  funext Z
  have hZ : componentGenericPoint X Z.1 ∈ V := Z.2
  have hx := hg ⟨_, hZ⟩
  have h2 : (rationalFunctionsPresheaf X).map (i ⟨_, hZ⟩).op
      ((toRationalFunctionsPresheaf X).app (op V) g) =
      (rationalFunctionsPresheaf X).map (i ⟨_, hZ⟩).op t := by
    rw [← toRationalFunctionsPresheaf_app_map (i ⟨_, hZ⟩) g]
    exact (congrArg _ hx).trans (hr _)
  exact congrFun h2 ⟨Z.1, hxW ⟨_, hZ⟩⟩

end UnitSections

/-- The structure sheaf `𝒪_X ⊆ K(X)` of a reduced Noetherian scheme is coherent. -/
theorem RationalFunctionsSubmodule.isCoherent_toModules_unit [IsReduced X] [IsNoetherian X] :
    SheafOfModules.IsCoherent (RationalFunctionsSubmodule.unit X).toModules := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have hqc : (RationalFunctionsSubmodule.unit X).toModules.IsQuasicoherent := by
    refine wshB_isQuasicoherent _ ?_
    intro U hU a t ht
    obtain ⟨r, rfl⟩ := exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit ht
    let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.algebraOfLE X (X.basicOpen_le a)
    have : IsLocalization.Away a Γ(X, X.basicOpen a) := hU.isLocalization_basicOpen a
    obtain ⟨⟨x, ⟨-, n, rfl⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers a) r
    refine ⟨n, (toRationalFunctionsPresheaf X).app (op U) x, ?_, ?_⟩
    · intro y hy
      exact ⟨U, 𝟙 U, hy, Submodule.mem_one.mpr ⟨x, rfl⟩⟩
    · rw [← toRationalFunctionsPresheaf_app_map (homOfLE (X.basicOpen_le a)) x]
      have h : X.presheaf.map (homOfLE (X.basicOpen_le a)).op x =
          r * (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) ^ n := by
        rw [← map_pow]
        exact hx.symm
      rw [h, Algebra.smul_def, map_mul, mul_comm]
      rfl
  refine wshB_isCoherent_of_finite _ ?_
  intro U hU
  let e : (RationalFunctionsSubmodule.unit X).sections U :=
    ⟨1, fun y hy => ⟨U, 𝟙 U, hy, Submodule.mem_one.mpr ⟨1, map_one _⟩⟩⟩
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton Γ(X, U)
      ((RationalFunctionsSubmodule.unit X).sections U) e) := by
    rintro ⟨t, ht⟩
    obtain ⟨r, rfl⟩ := exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit ht
    refine ⟨r, Subtype.ext ?_⟩
    show r • (1 : ToType ((rationalFunctionsPresheaf X).obj (op U))) = _
    rw [Algebra.smul_def, mul_one]
    rfl
  exact Module.Finite.of_surjective _ hsurj

/-! ### Extension and cover lemmas for submodules of `K(X)` on affine opens -/

/-- The extension property of `𝓕 ⊆ K(X)` on an open `U`: a section of `𝓕` over `X_a` becomes,
after multiplication by a power of `a`, the restriction of a section of `𝓕` over `U`. -/
private def wshB1_HasExt (F : RationalFunctionsSubmodule X) (U : X.Opens) : Prop :=
  ∀ (a : Γ(X, U)) (t : ToType ((rationalFunctionsPresheaf X).obj (op (X.basicOpen a)))),
    t ∈ F.sections (X.basicOpen a) →
    ∃ (n : ℕ) (s : ToType ((rationalFunctionsPresheaf X).obj (op U))), s ∈ F.sections U ∧
      (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op s =
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) ^ n • t

/-- Two sections of `K(X)` over `U` agreeing on `X_a` agree after multiplication by `a`. -/
private theorem wshB1_smul_eq_of_res_eq [IsReduced X] {U : X.Opens} (a : Γ(X, U))
    {s s' : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (h : (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op s =
      (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op s') :
    a • s = a • s' := by
  funext Z
  rw [rationalFunctions_smul_apply, rationalFunctions_smul_apply]
  by_cases hZ : componentGenericPoint X Z.1 ∈ X.basicOpen a
  · have := congrFun h ⟨Z.1, hZ⟩
    exact congrArg _ this
  · rw [wshB_germ_eq_zero_of_notMem_basicOpen a Z.2 hZ, zero_mul, zero_mul]

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange in
/-- A quasi-coherent submodule of `K(X)` has the extension property on every affine open. -/
private theorem wshB1_hasExt_of_isQuasicoherent (F : RationalFunctionsSubmodule X)
    [F.toModules.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) : wshB1_HasExt F U := by
  intro a t ht
  let := moduleOfLE F.toModules (X.basicOpen_le a)
  have hl := isLocalizedModule_restrictₗ F.toModules hU a rfl (X.basicOpen_le a)
  obtain ⟨⟨x, ⟨-, n, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers a)
    (restrictₗ F.toModules (X.basicOpen_le a)) (show Γ(F.toModules, X.basicOpen a) from ⟨t, ht⟩)
  have hx' := congrArg Subtype.val hx
  refine ⟨n, x.1, x.2, ?_⟩
  rw [← map_pow]
  exact hx'.symm

/-- If the restriction of `s ∈ K(X)(U)` to `X_b` is a section of `𝓕`, then some `bⁿ s` is. -/
private theorem wshB1_pow_smul_mem_of_res [IsReduced X] {F : RationalFunctionsSubmodule X}
    {U : X.Opens} (hF : wshB1_HasExt F U) (b : Γ(X, U))
    (s : ToType ((rationalFunctionsPresheaf X).obj (op U)))
    (hs : (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le b)).op s ∈
      F.sections (X.basicOpen b)) : ∃ n : ℕ, b ^ n • s ∈ F.sections U := by
  obtain ⟨n, s', hs', he⟩ := hF b _ hs
  refine ⟨n + 1, ?_⟩
  have : b • s' = b • (b ^ n • s) := wshB1_smul_eq_of_res_eq b (by
    rw [he, rationalFunctionsPresheaf_map_smul, map_pow])
  rw [pow_succ', mul_smul, ← this]
  exact Submodule.smul_mem _ _ hs'

/-- On an affine open, `s ∈ K(X)(U)` lies in a submodule `N ⊆ K(X)(U)` as soon as every point
has a basic open neighbourhood `X_b` with `bⁿ s ∈ N` for some `n`. -/
private theorem wshB1_mem_of_cover {U : X.Opens} (hU : IsAffineOpen U)
    (N : Submodule Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)))
    (s : ToType ((rationalFunctionsPresheaf X).obj (op U)))
    (h : ∀ x ∈ U, ∃ b : Γ(X, U), x ∈ X.basicOpen b ∧ ∃ n : ℕ, b ^ n • s ∈ N) :
    s ∈ N := by
  let I : Ideal Γ(X, U) := N.comap (LinearMap.toSpanSingleton Γ(X, U) _ s)
  have hI : I = ⊤ := by
    rw [← Ideal.span_eq I, ← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨b, hxb, n, hn⟩ := h x hx
    rw [Opens.mem_iSup]
    refine ⟨⟨b ^ (n + 1), ?_⟩, ?_⟩
    · show b ^ (n + 1) • s ∈ N
      rw [pow_succ', mul_smul]
      exact Submodule.smul_mem _ _ hn
    · rw [Scheme.basicOpen_pow X b (Nat.succ_pos n)]
      exact hxb
  have h1 : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
  have h2 : (1 : Γ(X, U)) • s ∈ N := h1
  rwa [one_smul] at h2

/-- Products of sections are stable under restriction. -/
private theorem wshB1_map_mem_mul (L L' : RationalFunctionsSubmodule X) {U V : X.Opens}
    (i : V ⟶ U) {s : ToType ((rationalFunctionsPresheaf X).obj (op U))}
    (hs : s ∈ L.sections U * L'.sections U) :
    (rationalFunctionsPresheaf X).map i.op s ∈ L.sections V * L'.sections V := by
  refine Submodule.mul_induction_on hs (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul]
    exact Submodule.mul_mem_mul (L.map_mem i ha) (L'.map_mem i hb)
  · rw [map_add]
    exact add_mem ha hb

/-- The extension property for the products `𝓛(U)𝓛'(U)`. -/
private theorem wshB1_hasExt_mul {L L' : RationalFunctionsSubmodule X} {U : X.Opens}
    (hL : wshB1_HasExt L U) (hL' : wshB1_HasExt L' U) (a : Γ(X, U))
    (t : ToType ((rationalFunctionsPresheaf X).obj (op (X.basicOpen a))))
    (ht : t ∈ L.sections (X.basicOpen a) * L'.sections (X.basicOpen a)) :
    ∃ (n : ℕ) (s : ToType ((rationalFunctionsPresheaf X).obj (op U))),
      s ∈ L.sections U * L'.sections U ∧
      (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op s =
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) ^ n • t := by
  refine Submodule.mul_induction_on ht (fun l hl l' hl' => ?_) (fun t₁ t₂ h₁ h₂ => ?_)
  · obtain ⟨n, s, hs, he⟩ := hL a l hl
    obtain ⟨n', s', hs', he'⟩ := hL' a l' hl'
    refine ⟨n + n', s * s', Submodule.mul_mem_mul hs hs', ?_⟩
    rw [map_mul, he, he', smul_mul_smul_comm, pow_add]
  · obtain ⟨n₁, s₁, hs₁, he₁⟩ := h₁
    obtain ⟨n₂, s₂, hs₂, he₂⟩ := h₂
    refine ⟨n₁ + n₂, a ^ n₂ • s₁ + a ^ n₁ • s₂,
      add_mem (Submodule.smul_mem _ _ hs₁) (Submodule.smul_mem _ _ hs₂), ?_⟩
    rw [map_add, rationalFunctionsPresheaf_map_smul, rationalFunctionsPresheaf_map_smul, he₁, he₂,
      map_pow, map_pow, smul_smul, smul_smul, ← pow_add, ← pow_add, smul_add, add_comm n₂ n₁]

/-- On an affine open, the sections of `𝓛𝓛'` are the products `𝓛(U)𝓛'(U)`. -/
private theorem wshB1_mulImage_sections_eq [IsReduced X] {L L' : RationalFunctionsSubmodule X}
    {U : X.Opens} (hU : IsAffineOpen U) (hL : wshB1_HasExt L U) (hL' : wshB1_HasExt L' U) :
    (RationalFunctionsSubmodule.mulImage L L').sections U = L.sections U * L'.sections U := by
  ext t
  constructor
  · intro ht
    refine wshB1_mem_of_cover hU _ t fun x hx => ?_
    obtain ⟨W, i, hxW, hW⟩ := ht x hx
    obtain ⟨b, hbW, hxb⟩ := hU.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
    have hb : (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le b)).op t ∈
        L.sections (X.basicOpen b) * L'.sections (X.basicOpen b) := by
      rw [← rationalFunctionsPresheaf_map_map i (homOfLE hbW)]
      exact wshB1_map_mem_mul L L' _ hW
    obtain ⟨n, s, hs, he⟩ := wshB1_hasExt_mul hL hL' b _ hb
    refine ⟨b, hxb, n + 1, ?_⟩
    have : b • s = b • (b ^ n • t) := wshB1_smul_eq_of_res_eq b (by
      rw [he, rationalFunctionsPresheaf_map_smul, map_pow])
    rw [pow_succ', mul_smul, ← this]
    exact Submodule.smul_mem _ _ hs
  · intro ht x hx
    exact ⟨U, 𝟙 U, hx, ht⟩

/-! ### Helpers for `𝓛⁻¹` -/

/-- The generic point of an irreducible component has codimension zero. -/
private theorem wshB1_coheight_componentGenericPoint (Z : irreducibleComponents X) :
    Order.coheight (componentGenericPoint X Z) = 0 := by
  rw [Order.coheight_eq_zero]
  intro b hb
  have hb' : b ⤳ componentGenericPoint X Z := hb
  have hZ := isGenericPoint_componentGenericPoint X Z
  have h1 : Z.1 ⊆ closure {b} := by
    rw [← hZ.def]
    exact hb'.closure_subset
  have h2 : closure {b} ⊆ Z.1 := Z.2.2 isIrreducible_singleton.closure h1
  have h3 : b ∈ closure {componentGenericPoint X Z} := by
    rw [hZ.def]
    exact h2 (subset_closure rfl)
  exact specializes_iff_mem_closure.mpr h3

/-- A section of `K(X)` whose germ at the generic point `η_Z` is a unit has a nonzero
`Z`-component. -/
private theorem wshB1_component_ne_zero_of_isUnit_germ [IsReduced X] {V : X.Opens}
    (Z : irreducibleComponents X) (hZ : componentGenericPoint X Z ∈ V)
    (l : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hl : IsUnit ((rationalFunctionsPresheaf X).germ V _ hZ l)) : l ⟨Z, hZ⟩ ≠ 0 := by
  obtain ⟨g, hg⟩ := hl.exists_right_inv
  obtain ⟨V', hV'V, hZ', l', rfl⟩ := TopCat.Presheaf.exists_le_germ_eq _ g hZ
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hV'V) _ hZ' l, ← map_mul,
    ← map_one ((rationalFunctionsPresheaf X).germ V' _ hZ').hom] at hg
  obtain ⟨W, hZW, i1, i2, he⟩ := TopCat.Presheaf.germ_eq _ _ hZ' hZ' _ _ hg
  have h1 := congrFun he ⟨Z, hZW⟩
  rw [map_mul, map_one] at h1
  have h2 : l ⟨Z, hZ⟩ * l' ⟨Z, hZ'⟩ = 1 := h1
  intro h0
  rw [h0, zero_mul] at h2
  have := (RationalFunctions.isField_stalk X Z).nontrivial
  exact zero_ne_one h2

/-- For every generic point `η_Z ∈ U`, a Weil divisorial subsheaf has a section over the affine
open `U` with nonzero `Z`-component. -/
private theorem wshB1_exists_mem_ne_zero [IsReduced X] (L : WeilDivisorialSubsheaf X)
    {U : X.Opens} (hU : IsAffineOpen U) (hL : wshB1_HasExt L.toRationalFunctionsSubmodule U)
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    ∃ u ∈ L.sections U, u Z ≠ 0 := by
  have hc : Order.coheight (componentGenericPoint X Z.1) ≤ 1 := by
    rw [wshB1_coheight_componentGenericPoint]
    exact zero_le_one
  obtain ⟨f, hf⟩ := L.principal_codim_one _ hc
  have hfmem : (f : (rationalFunctionsPresheaf X).stalk (componentGenericPoint X Z.1)) ∈
      L.stalkSet (componentGenericPoint X Z.1) := by
    rw [hf]
    exact ⟨1, by beta_reduce; rw [map_one, mul_one]⟩
  obtain ⟨V, hζV, l, hl, hgerm⟩ := hfmem
  have hl0 : l ⟨Z.1, hζV⟩ ≠ 0 :=
    wshB1_component_ne_zero_of_isUnit_germ Z.1 hζV l (hgerm ▸ f.isUnit)
  obtain ⟨b, hbV, hζb⟩ := hU.exists_basicOpen_le (⟨_, hζV⟩ : V) Z.2
  obtain ⟨n, s, hs, he⟩ := hL b _ (L.map_mem (homOfLE hbV) hl)
  refine ⟨s, hs, ?_⟩
  have h1 := congrFun he ⟨Z.1, hζb⟩
  change s ⟨Z.1, _⟩ = X.presheaf.germ (X.basicOpen b) _ hζb
    ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op b) ^ n) * l ⟨Z.1, _⟩ at h1
  rw [← map_pow, TopCat.Presheaf.germ_res_apply, map_pow] at h1
  have hu : IsUnit (X.presheaf.germ U _ Z.2 b) := (Scheme.mem_basicOpen X b _ Z.2).mp hζb
  intro h0
  have h0' : s ⟨Z.1, Z.2⟩ = 0 := h0
  rw [h1] at h0'
  exact hl0 (((hu.pow n).mul_right_eq_zero).mp h0')

/-- On an affine open of a Noetherian space, every generic point `η_Z ∈ U` lies in a basic open
containing no other generic point. -/
private theorem wshB1_exists_basicOpen_sep [NoetherianSpace X] {U : X.Opens}
    (hU : IsAffineOpen U) (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    ∃ e : Γ(X, U), componentGenericPoint X Z.1 ∈ X.basicOpen e ∧
      ∀ Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}, Z' ≠ Z →
        componentGenericPoint X Z'.1 ∉ X.basicOpen e := by
  have : Finite (irreducibleComponents X) :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  let C : Set X := ⋃ Z' ∈ {Z' : irreducibleComponents X | Z' ≠ Z.1}, Z'.1
  have hC : IsClosed C := Set.Finite.isClosed_biUnion (Set.toFinite _)
    fun Z' _ => isClosed_of_mem_irreducibleComponents _ Z'.2
  have hζC : componentGenericPoint X Z.1 ∉ C := by
    simp only [C, Set.mem_iUnion]
    rintro ⟨Z', hZ', hmem⟩
    apply hZ'
    have h1 : Z.1.1 ⊆ Z'.1 := by
      rw [← (isGenericPoint_componentGenericPoint X Z.1).def]
      exact (isClosed_of_mem_irreducibleComponents _ Z'.2).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hmem)
    exact Subtype.ext (le_antisymm h1 (Z.1.2.2 Z'.2.1 h1)).symm
  let W : X.Opens := U ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
  obtain ⟨e, heW, hζe⟩ := hU.exists_basicOpen_le
    (⟨_, ⟨Z.2, hζC⟩⟩ : W) Z.2
  refine ⟨e, hζe, fun Z' hZ' hmem => ?_⟩
  apply (heW hmem).2
  simp only [C, Set.mem_iUnion]
  exact ⟨Z'.1, fun h => hZ' (Subtype.ext h), (isGenericPoint_componentGenericPoint X Z'.1).mem⟩

/-- A submodule of `K(X)(U)`, `U` affine, with, for every generic point of `U`, an element nonzero
there, has an element nonzero at all generic points of `U`. -/
private theorem wshB1_exists_forall_ne_zero [IsReduced X] [NoetherianSpace X] {U : X.Opens}
    (hU : IsAffineOpen U) (N : Submodule Γ(X, U) ((rationalFunctionsPresheaf X).obj (op U)))
    (hN : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      ∃ g ∈ N, g Z ≠ 0) :
    ∃ u ∈ N, ∀ Z, u Z ≠ 0 := by
  classical
  choose e he1 he2 using wshB1_exists_basicOpen_sep (X := X) hU
  choose u hu1 hu2 using hN
  have : Finite (irreducibleComponents X) :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  have : Fintype {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U} :=
    Fintype.ofFinite _
  refine ⟨∑ Z, e Z • u Z, Submodule.sum_mem _ fun Z _ => Submodule.smul_mem _ _ (hu1 Z),
    fun Z0 => ?_⟩
  have hev : (∑ Z, e Z • u Z) Z0 = ∑ Z, (e Z • u Z) Z0 := Finset.sum_apply _ _ _
  rw [hev, Finset.sum_eq_single Z0]
  · rw [rationalFunctions_smul_apply]
    intro h
    exact hu2 Z0
      (((Scheme.mem_basicOpen X (e Z0) _ Z0.2).mp (he1 Z0)).mul_right_eq_zero.mp h)
  · intro Z _ hZ
    rw [rationalFunctions_smul_apply,
      wshB_germ_eq_zero_of_notMem_basicOpen (e Z) Z0.2 (he2 Z Z0 (Ne.symm hZ)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A Weil divisorial subsheaf has a section over an affine open with all components nonzero. -/
private theorem wshB1_exists_mem_forall_ne_zero [IsReduced X] [NoetherianSpace X]
    (L : WeilDivisorialSubsheaf X) {U : X.Opens} (hU : IsAffineOpen U)
    (hL : wshB1_HasExt L.toRationalFunctionsSubmodule U) :
    ∃ u ∈ L.sections U, ∀ Z, u Z ≠ 0 :=
  wshB1_exists_forall_ne_zero hU _ (wshB1_exists_mem_ne_zero L hU hL)

/-- On an affine open, `x ∈ K(X)(U)` lies in `𝓛⁻¹(U)` as soon as `x 𝓛(U) ⊆ sat(𝒪_X)(U)`. -/
private theorem wshB1_mem_inv_of_forall [IsReduced X] {L : RationalFunctionsSubmodule X}
    {U : X.Opens} (hU : IsAffineOpen U) (hL : wshB1_HasExt L U)
    (x : ToType ((rationalFunctionsPresheaf X).obj (op U)))
    (hx : ∀ m ∈ L.sections U,
      x * m ∈ (RationalFunctionsSubmodule.unit X).saturation.sections U) :
    x ∈ L.inv.sections U := by
  intro W i l hl
  refine (RationalFunctionsSubmodule.unit X).saturation.mem_of_locally fun w hw => ?_
  obtain ⟨b, hbW, hwb⟩ := hU.exists_basicOpen_le (⟨w, hw⟩ : W) (i.le hw)
  refine ⟨X.basicOpen b, homOfLE hbW, hwb, ?_⟩
  obtain ⟨n, s, hs, he⟩ := hL b _ (L.map_mem (homOfLE hbW) hl)
  have h1 := (RationalFunctionsSubmodule.unit X).saturation.map_mem
    (homOfLE (X.basicOpen_le b)) (hx s hs)
  rw [map_mul, he, mul_smul_comm] at h1
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le b)).op b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  rw [Submodule.smul_mem_iff_of_isUnit _ (hu.pow n)] at h1
  rw [map_mul]
  exact h1

/-! ### Quasi-coherence of the saturation -/

/-- **Germ criterion on an affine open.** For `𝓕 ⊆ K(X)` with the extension property on the affine
open `U`, the germ of `s ∈ K(X)(U)` at `η ∈ U` lies in `𝓕_η` iff `r s ∈ 𝓕(U)` for some
`r ∈ Γ(X, U)` not vanishing at `η`. -/
private theorem wshB1_germ_mem_stalkSet_iff [IsReduced X] {F : RationalFunctionsSubmodule X}
    {U : X.Opens} (hU : IsAffineOpen U) (hF : wshB1_HasExt F U)
    (s : ToType ((rationalFunctionsPresheaf X).obj (op U))) {η : X} (hη : η ∈ U) :
    (rationalFunctionsPresheaf X).germ U η hη s ∈ F.stalkSet η ↔
      ∃ r : Γ(X, U), η ∈ X.basicOpen r ∧ r • s ∈ F.sections U := by
  rw [F.germ_mem_stalkSet_iff hη s]
  constructor
  · rintro ⟨W, i, hηW, hW⟩
    obtain ⟨b, hbW, hηb⟩ := hU.exists_basicOpen_le (⟨η, hηW⟩ : W) hη
    have hb : (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le b)).op s ∈
        F.sections (X.basicOpen b) := by
      rw [← rationalFunctionsPresheaf_map_map i (homOfLE hbW)]
      exact F.map_mem _ hW
    obtain ⟨n, hn⟩ := wshB1_pow_smul_mem_of_res hF b s hb
    refine ⟨b ^ (n + 1), ?_, ?_⟩
    · rw [Scheme.basicOpen_pow X b (Nat.succ_pos n)]
      exact hηb
    · rw [pow_succ', mul_smul]
      exact Submodule.smul_mem _ _ hn
  · rintro ⟨r, hηr, hr⟩
    refine ⟨X.basicOpen r, homOfLE (X.basicOpen_le r), hηr, ?_⟩
    have h1 := F.map_mem (homOfLE (X.basicOpen_le r)) hr
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) :=
      X.toRingedSpace.isUnit_res_basicOpen r
    rw [rationalFunctionsPresheaf_map_smul, Submodule.smul_mem_iff_of_isUnit _ hu] at h1
    exact h1

/-- **Extension property of the saturation.** If `𝓕 ⊆ K(X)` has the extension property on every
affine open of the locally Noetherian reduced scheme `X`, so does `sat(𝓕)`. -/
private theorem wshB1_hasExt_saturation [IsReduced X] [IsLocallyNoetherian X]
    {F : RationalFunctionsSubmodule X} {U : X.Opens} (hU : IsAffineOpen U)
    (hF : wshB1_HasExt F U) : wshB1_HasExt F.saturation U := by
  intro a t ht
  classical
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let x : ToType ((rationalFunctionsPresheaf X).obj (op U)) := fun Z =>
    if h : componentGenericPoint X Z.1 ∈ X.basicOpen a then t ⟨Z.1, h⟩ else 0
  have hxt : (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op x = t := by
    funext Z
    exact dite_eq_left_of_eq_true (eq_true Z.2)
  let J : ℕ → Ideal Γ(X, U) := fun k =>
    (F.sections U).comap (LinearMap.toSpanSingleton Γ(X, U) _ (a ^ k • x))
  have hJmem : ∀ k r, r ∈ J k ↔ r • a ^ k • x ∈ F.sections U := fun _ _ => Iff.rfl
  have hJmono : Monotone J := by
    refine monotone_nat_of_le_succ fun k r hr => ?_
    rw [hJmem] at hr ⊢
    rw [pow_succ', mul_smul, smul_comm r a]
    exact Submodule.smul_mem _ _ hr
  obtain ⟨n, hn⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) ⟨J, hJmono⟩
  have hn' : ∀ m, n ≤ m → J n = J m := hn
  refine ⟨n, a ^ n • x, ?_, by rw [rationalFunctionsPresheaf_map_smul, hxt, map_pow]⟩
  intro η hηU hc
  rw [wshB1_germ_mem_stalkSet_iff hU hF _ hηU]
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  obtain ⟨p, hp⟩ : η ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hηU
  have hmemD : ∀ (q : PrimeSpectrum Γ(X, U)) (r : Γ(X, U)),
      hU.fromSpec q ∈ X.basicOpen r ↔ r ∉ q.asIdeal := by
    intro q r
    change q ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    exact PrimeSpectrum.mem_basicOpen _ _
  let S : Submonoid Γ(X, U) := p.asIdeal.primeCompl ⊔ Submonoid.powers a
  have hdisj : Disjoint (J 0 : Set Γ(X, U)) S := by
    rw [Set.disjoint_left]
    intro y hyJ hyS
    obtain ⟨s, hs, z, ⟨k, rfl⟩, rfl⟩ := Submonoid.mem_sup.mp hyS
    have hsk : s ∈ J k := by
      have h0 : (s * a ^ k) • a ^ 0 • x ∈ F.sections U := hyJ
      rw [pow_zero, one_smul, mul_smul] at h0
      exact h0
    have hsn : s ∈ J n := by
      rcases le_total k n with h | h
      · exact hJmono h hsk
      · rw [hn' k h]
        exact hsk
    exact hcon s (hp ▸ (hmemD p s).mpr hs) hsn
  obtain ⟨P, hP, hJP, hPS⟩ := Ideal.exists_le_prime_disjoint (I := J 0) S hdisj
  let q : PrimeSpectrum Γ(X, U) := ⟨P, hP⟩
  have hqp : q ≤ p := by
    intro y hy
    by_contra hyp
    exact Set.disjoint_left.mp hPS hy (Submonoid.mem_sup_left hyp)
  have haq : a ∉ P := fun h =>
    Set.disjoint_left.mp hPS h (Submonoid.mem_sup_right (Submonoid.mem_powers a))
  have hη'a : hU.fromSpec q ∈ X.basicOpen a := (hmemD q a).mpr haq
  have hη'U : hU.fromSpec q ∈ U := X.basicOpen_le a hη'a
  have hspec : hU.fromSpec q ⤳ η :=
    hp ▸ ((PrimeSpectrum.le_iff_specializes q p).mp hqp).map hU.fromSpec.continuous
  have hc' : Order.coheight (hU.fromSpec q) ≤ 1 := (Order.coheight_anti (show η ≤ hU.fromSpec q from hspec)).trans hc
  have hgerm := ht _ hη'a hc'
  rw [← hxt, TopCat.Presheaf.germ_res_apply] at hgerm
  obtain ⟨r, hr1, hr2⟩ := (wshB1_germ_mem_stalkSet_iff hU hF x hη'U).mp hgerm
  have hrJ : r ∈ J 0 := by
    rw [hJmem, pow_zero, one_smul]
    exact hr2
  exact (hmemD q r).mp hr1 (hJP hrJ)

/-! ### Clearing denominators in `K(X)` over an affine open -/

/-- The `Z`-component of `m ∈ K(X)(U)`, `U` affine, is a fraction `c / bⁿ` of sections over `U`,
with `b` invertible at `η_Z` and vanishing at every other generic point of `U`. -/
private theorem wshB1_exists_local_denominator [IsReduced X] [NoetherianSpace X] {U : X.Opens}
    (hU : IsAffineOpen U) (m : ToType ((rationalFunctionsPresheaf X).obj (op U)))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}) :
    ∃ (b c : Γ(X, U)) (n : ℕ), componentGenericPoint X Z.1 ∈ X.basicOpen b ∧
      (∀ Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}, Z' ≠ Z →
        componentGenericPoint X Z'.1 ∉ X.basicOpen b) ∧
      m Z * X.presheaf.germ U _ Z.2 b ^ n = X.presheaf.germ U _ Z.2 c := by
  obtain ⟨V, hζV, g, hg⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (m Z)
  obtain ⟨e, hζe, he⟩ := wshB1_exists_basicOpen_sep hU Z
  obtain ⟨b, hbW, hζb⟩ := hU.exists_basicOpen_le
    (⟨_, ⟨hζV, hζe⟩⟩ : (V ⊓ X.basicOpen e : X.Opens)) Z.2
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.algebraOfLE X (X.basicOpen_le b)
  have : IsLocalization.Away b Γ(X, X.basicOpen b) := hU.isLocalization_basicOpen b
  obtain ⟨⟨c, ⟨-, n, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers b)
    (X.presheaf.map (homOfLE (hbW.trans inf_le_left)).op g)
  refine ⟨b, c, n, hζb, fun Z' hZ' hmem => he Z' hZ' ((hbW hmem).2), ?_⟩
  have h1 := congrArg (X.presheaf.germ (X.basicOpen b) _ hζb).hom hc
  change X.presheaf.germ (X.basicOpen b) _ hζb
      (X.presheaf.map (homOfLE (hbW.trans inf_le_left)).op g *
        X.presheaf.map (homOfLE (X.basicOpen_le b)).op (b ^ n)) =
    X.presheaf.germ (X.basicOpen b) _ hζb (X.presheaf.map (homOfLE (X.basicOpen_le b)).op c) at h1
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
    TopCat.Presheaf.germ_res_apply, hg, map_pow] at h1
  exact h1

/-- **Clearing denominators.** Every `m ∈ K(X)(U)`, `U` affine, has a denominator `t ∈ Γ(X, U)`
nonvanishing at every generic point of `U`: `t m` is the image of a section of `𝒪_X`. -/
private theorem wshB1_exists_denominator [IsReduced X] [NoetherianSpace X] {U : X.Opens}
    (hU : IsAffineOpen U) (m : ToType ((rationalFunctionsPresheaf X).obj (op U))) :
    ∃ t : Γ(X, U), (∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      X.presheaf.germ U _ Z.2 t ≠ 0) ∧ ∃ c : Γ(X, U), t • m = (toRationalFunctionsPresheaf X).app (op U) c := by
  classical
  choose b c n hb1 hb2 hb3 using wshB1_exists_local_denominator hU m
  have : Finite (irreducibleComponents X) :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  have : Fintype {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U} :=
    Fintype.ofFinite _
  have hzero : ∀ Z Z0 : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U}, Z ≠ Z0 →
      X.presheaf.germ U _ Z0.2 (b Z) = 0 := fun Z Z0 h =>
    wshB_germ_eq_zero_of_notMem_basicOpen (b Z) Z0.2 (hb2 Z Z0 (Ne.symm h))
  have hunit : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      IsUnit (X.presheaf.germ U _ Z.2 (b Z)) := fun Z =>
    (Scheme.mem_basicOpen X (b Z) _ Z.2).mp (hb1 Z)
  have hgt : ∀ Z0 : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      X.presheaf.germ U _ Z0.2 (∑ Z, b Z ^ (n Z + 1)) =
        X.presheaf.germ U _ Z0.2 (b Z0) ^ (n Z0 + 1) := by
    intro Z0
    rw [map_sum, Finset.sum_eq_single Z0]
    · rw [map_pow]
    · intro Z _ hZ
      rw [map_pow, hzero Z Z0 hZ, zero_pow (Nat.succ_ne_zero _)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine ⟨∑ Z, b Z ^ (n Z + 1), fun Z0 => ?_, ∑ Z, b Z * c Z, ?_⟩
  · rw [hgt]
    have := (RationalFunctions.isField_stalk X Z0.1).nontrivial
    exact ((hunit Z0).pow _).ne_zero
  · funext Z0
    rw [rationalFunctions_smul_apply, hgt]
    change _ = X.presheaf.germ U _ Z0.2 (∑ Z, b Z * c Z)
    rw [map_sum, Finset.sum_eq_single Z0]
    · rw [map_mul, ← hb3 Z0, pow_succ]
      ring
    · intro Z _ hZ
      rw [map_mul, hzero Z Z0 hZ, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-! ### Finiteness of the saturation, reduced to `sat(𝒪_X)` -/

/-- The finiteness of `sat(𝓕)(U)` over an affine open reduces to that of `sat(𝒪_X)(U)`: clearing
the denominators of finitely many generators of `𝓕(U)` gives `τ ∈ Γ(X, U)`, nonvanishing at every
generic point, with `τ sat(𝓕)(U) ⊆ sat(𝒪_X)(U)`. -/
private theorem wshB1_finite_saturation [IsReduced X] [IsNoetherian X]
    {F : RationalFunctionsSubmodule X} [F.toModules.IsQuasicoherent] [F.toModules.IsFiniteType]
    {U : X.Opens} (hU : IsAffineOpen U)
    (hone : Module.Finite Γ(X, U) ((RationalFunctionsSubmodule.unit X).saturation.sections U)) :
    Module.Finite Γ(X, U) (F.saturation.sections U) := by
  classical
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hFU := wshB1_hasExt_of_isQuasicoherent F hU
  have := RationalFunctionsSubmodule.isCoherent_toModules_unit (X := X)
  have : (RationalFunctionsSubmodule.unit X).toModules.IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  have h1U := wshB1_hasExt_of_isQuasicoherent (RationalFunctionsSubmodule.unit X) hU
  obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp
    (Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F.toModules hU))
  choose t ht0 c hc using fun m => wshB1_exists_denominator (X := X) hU m
  let τ : Γ(X, U) := ∏ m ∈ hTfin.toFinset, t m
  have hτ0 : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      X.presheaf.germ U _ Z.2 τ ≠ 0 := by
    intro Z
    have := (RationalFunctions.isField_stalk X Z.1).isDomain
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => ht0 m Z
  have hunitmem : ∀ c : Γ(X, U), (toRationalFunctionsPresheaf X).app (op U) c ∈
      (RationalFunctionsSubmodule.unit X).sections U :=
    fun c y hy => ⟨U, 𝟙 U, hy, Submodule.mem_one.mpr ⟨c, rfl⟩⟩
  have hτF : ∀ m ∈ F.sections U, τ • m ∈ (RationalFunctionsSubmodule.unit X).sections U := by
    intro m hm
    rw [← hTspan] at hm
    induction hm using Submodule.span_induction with
    | mem m hmT =>
      have : τ = (∏ m' ∈ hTfin.toFinset.erase m, t m') * t m :=
        (Finset.prod_erase_mul _ _ (hTfin.mem_toFinset.mpr hmT)).symm
      rw [this, mul_smul, hc m]
      exact Submodule.smul_mem _ _ (hunitmem _)
    | zero => rw [smul_zero]; exact zero_mem _
    | add _ _ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
    | smul r m _ h => rw [smul_smul, mul_comm, ← smul_smul]; exact Submodule.smul_mem _ _ h
  have hτS : ∀ s ∈ F.saturation.sections U,
      τ • s ∈ (RationalFunctionsSubmodule.unit X).saturation.sections U := by
    intro s hs η hη hc'
    rw [wshB1_germ_mem_stalkSet_iff hU h1U _ hη]
    obtain ⟨r, hr1, hr2⟩ := (wshB1_germ_mem_stalkSet_iff hU hFU s hη).mp (hs η hη hc')
    exact ⟨r, hr1, by rw [smul_smul, mul_comm, ← smul_smul]; exact hτF _ hr2⟩
  let φ : F.saturation.sections U →ₗ[Γ(X, U)]
      (RationalFunctionsSubmodule.unit X).saturation.sections U :=
    { toFun := fun s => ⟨τ • s.1, hτS s.1 s.2⟩
      map_add' := fun s s' => Subtype.ext (smul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (by
        show τ • r • s.1 = r • τ • s.1
        rw [smul_smul, mul_comm, ← smul_smul]) }
  have hφ : Function.Injective φ := by
    intro s s' h
    have h' := congrArg Subtype.val h
    apply Subtype.ext
    funext Z
    have hZ : X.presheaf.germ U _ Z.2 τ * s.1 Z = X.presheaf.germ U _ Z.2 τ * s'.1 Z :=
      congrFun h' Z
    obtain ⟨v, hv⟩ := (RationalFunctions.isField_stalk X Z.1).mul_inv_cancel (hτ0 Z)
    calc s.1 Z = v * X.presheaf.germ U _ Z.2 τ * s.1 Z := by rw [mul_comm v, hv, one_mul]
      _ = v * X.presheaf.germ U _ Z.2 τ * s'.1 Z := by rw [mul_assoc, hZ, ← mul_assoc]
      _ = s'.1 Z := by rw [mul_comm v, hv, one_mul]
  have := hone
  have : _root_.IsNoetherian Γ(X, U)
      ((RationalFunctionsSubmodule.unit X).saturation.sections U) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective φ hφ

end WShB1Infra

/-! ### The normalized canonical module inside `K(X)`

For `ω = H^{-d}(K_X)`, there is an injective `𝒪_X`-linear `φ : ω → K(X)` with saturated image. -/

section WShB1Dualizing

variable {k : Type u} [Field k] {X : Scheme.{u}}

section InjectiveHelpers

/-- Depth bound at every point, for `ω ≅ H^{-d}(K_X)`. -/
private lemma wshB1_exists_depth_le_of_iso [IsNoetherian X] {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π]
    {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) (x : X) :
    ∃ h : ℕ, ringKrullDim (X.presheaf.stalk x) = h ∧
      letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
      min (h : ℕ∞) 2 ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf x) := by
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨-, hx⟩ := hK3 d hd
  obtain ⟨D, e', h, -, -, hh, -, -, hdepth⟩ := hx x
  refine ⟨h, hh, ?_⟩
  have hinst := Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  have h2 := Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (wshC_stalkEquivOfIso x e)
  rw [h2]
  have hh := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X)
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  rw [hh] at hdepth
  exact hdepth

/-- At a point where the local ring is a field, `ω_x` is one-dimensional: `ω_x ≃ 𝒪_{X,x}`. -/
private lemma wshB1_nonempty_stalk_linearEquiv_of_isField [IsNoetherian X] {π : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj) (x : X)
    (hx : IsField (X.presheaf.stalk x)) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
    Nonempty ((TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf x) ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x) := by
  obtain ⟨-, -, hK3⟩ := normalizedDualizingComplexOverField_spec π
  obtain ⟨-, hx'⟩ := hK3 d hd
  obtain ⟨D, e', h, hD, -, hh, hed, hiso, -⟩ := hx' x
  have h0 : h = 0 := by
    have := ringKrullDim_eq_zero_of_isField hx
    rw [this] at hh
    exact_mod_cast hh.symm
  have he0 : e' = d := by omega
  obtain ⟨E1⟩ := hiso (-(d : ℤ))
  have hdeg : (-(d : ℤ)) + (e' : ℤ) = 0 := by omega
  rw [hdeg] at E1
  have hl : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  have : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  have hsingle : Dualizing.IsNormalizedDualizingComplex.{u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))) :=
    Dualizing.isNormalizedDualizingComplex_single_self_of_isField hx
  obtain ⟨E2⟩ := Dualizing.IsNormalizedDualizingComplex.nonempty_iso hD hsingle
  have hh := AlgebraicGeometry.TildeTensor.stalkModule_eq_presheafModule (X := X)
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  rw [hh] at E1
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val x
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    ((DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj).val x
  let E3 : (Stacks.Duality.standardHomology D 0) ≅ ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
    (@DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) _ _
      (HasDerivedCategory.standard _) 0).mapIso E2 ≪≫
      (@DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} (X.presheaf.stalk x)) _ _
        (HasDerivedCategory.standard _) 0).app _
  exact ⟨(wshC_stalkEquivOfIso x e).trans (E1.trans E3.toLinearEquiv)⟩

/-- Build a morphism `ω ⟶ K(X)` from linear identifications of the generic stalks. -/
private noncomputable def wshB1_homToRationalFunctions (ω : X.Modules)
    (b : ∀ Z : irreducibleComponents X,
      letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val
        (componentGenericPoint X Z)
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf (componentGenericPoint X Z)) ≃ₗ[X.presheaf.stalk (componentGenericPoint X Z)]
        X.presheaf.stalk (componentGenericPoint X Z)) :
    ω ⟶ rationalFunctionsModule X := by
  let Φ : ∀ U : X.Opens, ω.val.obj (op U) →+ ToType ((rationalFunctionsPresheaf X).obj (op U)) :=
    fun U =>
      { toFun := fun s Z => b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2 s)
        map_zero' := by
          funext Z
          exact (congrArg (b Z.1) (map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2)))).trans (map_zero _)
        map_add' := by
          intro s t; funext Z
          exact (congrArg (b Z.1) (map_add (ConcreteCategory.hom (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2)) s t)).trans (map_add _ _ _) }
  have hΦres : ∀ {U V : X.Opens} (i : V ⟶ U) (s : ω.val.obj (op U)),
      Φ V ((ω.val.presheaf.map i.op).hom s) = (rationalFunctionsPresheaf X).map i.op (Φ U s) := by
    intro U V i s
    funext Z
    show b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V _ Z.2 _) =
      b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ (i.le Z.2) s)
    exact congrArg (b Z.1) (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf i _ _ s)
  let φab : ω.val.presheaf ⟶ (RationalFunctionsSubmodule.top X).presheafAb :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => ⟨Φ U.unop s, Submodule.mem_top⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun s t => Subtype.ext (map_add _ s t) }
      naturality := by
        intro U V i
        ext s
        exact Subtype.ext (hΦres i.unop s) }
  have hφ : ∀ (U : X.Opensᵒᵖ) (r : X.ringCatSheaf.obj.obj U) (m : ω.val.obj U),
      φab.app U (r • m) = r • φab.app U m := by
    intro U r m
    refine Subtype.ext (funext fun Z => ?_)
    show b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U.unop _ Z.2 (r • m)) =
      X.presheaf.germ U.unop _ Z.2 r * b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U.unop _ Z.2 m)
    have h1 := PresheafOfModules.germ_smul (R := X.presheaf) ω.val (componentGenericPoint X Z.1)
      U.unop Z.2 r m
    exact (congrArg (b Z.1) h1).trans ((map_smul (b Z.1) _ _).trans rfl)
  exact ⟨PresheafOfModules.homMk φab hφ⟩

open Stacks.AlgebraicGeometry.AssociatedPointsMono in
/-- Variant of Stacks 0AVL (`injective_app_of_isAffineOpen`) with no hypothesis on the target. -/
private lemma wshB1_injective_app_of_isAffineOpen' [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ y ∈ Stacks.Divisors.associatedPoints F, ∀ (U : X.Opens) (hy : y ∈ U) (s : Γ(F, U)),
      f.app U s = 0 → F.presheaf.germ U y hy s = 0)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (f.app U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : Γ(F, U) →ₗ[Γ(X, U)] Γ(G, U) :=
    { toFun := f.app U
      map_add' := map_add _
      map_smul' := fun r x => f.app_smul r x }
  have hker : LinearMap.ker φ = ⊥ := by
    by_contra hne
    have : Nontrivial (LinearMap.ker φ) := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨q, hq⟩ := associatedPrimes.nonempty Γ(X, U) (LinearMap.ker φ)
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hq
    obtain ⟨hqp, k, hkq⟩ := hq
    have hcol : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {(k : Γ(F, U))}) = q := by
      rw [Submodule.colon_span]
      ext r
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hkq,
        Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    set u : U := hU.isoSpec.inv ⟨q, hqp⟩ with hu
    have hpq : hU.primeIdealOf u = ⟨q, hqp⟩ := primeIdealOf_isoSpec_inv hU _
    have hcol' : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {(k : Γ(F, U))})
          = (hU.primeIdealOf ⟨(u : X), u.2⟩).asIdeal := by
      rw [hcol]
      exact congrArg PrimeSpectrum.asIdeal hpq.symm
    let : Module (X.presheaf.stalk (u : X)) (F.presheaf.stalk (u : X)) :=
      stalkModule F (u : X)
    have hann := colon_germ_eq F hU (u : X) u.2 (k : Γ(F, U)) hcol'
    have hassoc : (u : X) ∈ Stacks.Divisors.associatedPoints F := ⟨inferInstance, _, hann⟩
    have hgz : F.presheaf.germ U (u : X) u.2 (k : Γ(F, U)) ≠ 0 := by
      intro h
      have h1 : (1 : X.presheaf.stalk (u : X)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk (u : X)) := by
        rw [← hann, Submodule.colon_span, Submodule.mem_colon_singleton, h, smul_zero]
        exact Submodule.zero_mem _
      exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk (u : X))).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact hgz (hf (u : X) hassoc U u.2 (k : Γ(F, U)) k.2)
  have key : ∀ t : Γ(F, U), f.app U t = 0 → t = 0 := by
    intro t ht
    have htk : t ∈ LinearMap.ker φ := ht
    rw [hker, Submodule.mem_bot] at htk
    exact htk
  intro a b hab
  exact sub_eq_zero.mp (key (a - b) (by rw [map_sub, hab, sub_self]))

/-- General opens: injectivity of `f.app U` from the germ condition at associated points. -/
private lemma wshB1_injective_app_of_germ_zero [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsQuasicoherent] (f : F ⟶ G)
    (hf : ∀ y ∈ Stacks.Divisors.associatedPoints F, ∀ (U : X.Opens) (hy : y ∈ U) (s : Γ(F, U)),
      f.app U s = 0 → F.presheaf.germ U y hy s = 0) (U : X.Opens) :
    Function.Injective (f.app U) := by
  have key : ∀ s : Γ(F, U), f.app U s = 0 → s = 0 := by
    intro s hs
    refine TopCat.Presheaf.section_ext (C := Ab.{u}) ⟨F.presheaf, F.isSheaf⟩ U s 0 fun x hx => ?_
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU'⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    have hVU : (V : X.Opens) ≤ U := hVU'
    have hnat : f.app (V : X.Opens) (F.presheaf.map (homOfLE hVU).op s)
        = G.presheaf.map (homOfLE hVU).op (f.app U s) := by
      have hn := congr($(f.mapPresheaf.naturality (homOfLE hVU).op) s)
      simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hn
      exact hn
    have hs0 : F.presheaf.map (homOfLE hVU).op s = 0 := by
      refine wshB1_injective_app_of_isAffineOpen' f hf hV ?_
      rw [hnat, hs, map_zero, map_zero]
    rw [← F.presheaf.germ_res_apply (homOfLE hVU) x hxV s, hs0, map_zero, map_zero]
  intro a b hab
  exact sub_eq_zero.mp (key (a - b) (by rw [map_sub, hab, sub_self]))

private lemma wshB1_mem_genericPoints_of_ringKrullDim_stalk_eq_zero (y : X)
    (h : ringKrullDim (X.presheaf.stalk y) = 0) : y ∈ genericPoints X := by
  rw [ringKrullDim_stalk_eq_coheight] at h
  have hmax : IsMax y := by
    have : Order.coheight y = 0 := by exact_mod_cast h
    exact Order.coheight_eq_zero.mp this
  have key : ∀ b : X, b ⤳ y → b = y := by
    intro b hb
    have h1 : y ≤ b := Scheme.le_iff_specializes.mpr hb
    have h2 : b ≤ y := hmax h1
    exact (hb.antisymm (Scheme.le_iff_specializes.mp h2)).eq
  show closure ({y} : Set X) ∈ irreducibleComponents X
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro T hT hle
  have hspec : IsGenericPoint (IsIrreducible.genericPoint hT) (closure T) :=
    IsIrreducible.isGenericPoint_genericPoint_closure hT
  have hy : y ∈ closure T := subset_closure (hle (subset_closure rfl))
  have hgy : IsIrreducible.genericPoint hT ⤳ y := hspec.specializes hy
  have hg := key _ hgy
  intro t ht
  have : t ∈ closure ({IsIrreducible.genericPoint hT} : Set X) := by
    rw [hspec.def]; exact subset_closure ht
  rwa [hg] at this

end InjectiveHelpers

/-- **Core, injectivity.** For `X` reduced and pure of dimension `d` and `ω ≅ H^{-d}(K_X)`, the
`𝒪_X`-linear map `ω ⟶ K(X)` built from any identifications `ω_η ≅ 𝒪_{X,η}` at the generic points is
injective on all sections. Proof sketch: the stalks of
`ω` at `x` have depth `≥ min (dim 𝒪_{X,x}) 2` (`normalizedDualizingComplexOverField_spec`), so
every associated point of `ω` is generic, whence `ω(U) → ∏_{η ∈ U} ω_η` is injective; each `ω_η`
is a `1`-dimensional `𝒪_{X,η}`-vector space (normalized dualizing complex over a field), and
choosing bases gives `ω_η ≅ 𝒪_{X,η}`. -/
private lemma wshB1_injective_homToRationalFunctions [IsReduced X] [IsNoetherian X]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj)
    (b : ∀ Z : irreducibleComponents X,
      letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier ω.val
        (componentGenericPoint X Z)
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf (componentGenericPoint X Z)) ≃ₗ[X.presheaf.stalk (componentGenericPoint X Z)]
        X.presheaf.stalk (componentGenericPoint X Z)) (U : X.Opens) :
    Function.Injective ((wshB1_homToRationalFunctions ω b).val.app (op U)) := by
  have hl : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  have hcoh : _root_.SheafOfModules.IsCoherent ω :=
    AlgebraicGeometry.isCoherent_of_moduleIso e.symm
      ((normalizedDualizingComplexOverField_spec π).2.1 (-(d : ℤ)))
  have hqc : ω.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent ω).1
  refine wshB1_injective_app_of_germ_zero (wshB1_homToRationalFunctions ω b) ?_ U
  intro y hy V hyV s hs
  obtain ⟨h, hh, hdep⟩ := wshB1_exists_depth_le_of_iso hd e y
  have hdep0 : Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal _)
      (TopCat.Presheaf.stalk (C := Ab.{u}) ω.val.presheaf y) = 0 := by
    by_contra hne
    exact Stacks.Divisors.notMem_associatedPoints_of_one_le_depth ω y
      (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 hne)) hy
  have hh0 : ringKrullDim (X.presheaf.stalk y) = 0 := by
    rw [hh]
    rw [hdep0] at hdep
    have : min (h : ℕ∞) 2 = 0 := le_antisymm hdep bot_le
    have : h = 0 := by
      by_contra hne
      have h1 : (1 : ℕ∞) ≤ h := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
      have : (1 : ℕ∞) ≤ min (h : ℕ∞) 2 := le_min h1 (by norm_num)
      rw [‹min (h : ℕ∞) 2 = 0›] at this
      exact absurd this (by norm_num)
    subst this; rfl
  have hyg : y ∈ genericPoints X := wshB1_mem_genericPoints_of_ringKrullDim_stalk_eq_zero y hh0
  obtain ⟨Z, rfl⟩ : ∃ Z : irreducibleComponents X, componentGenericPoint X Z = y :=
    ⟨genericPoints.component ⟨y, hyg⟩, (isGenericPoint_componentGenericPoint X _).eq
      (genericPoints.isGenericPoint ⟨y, hyg⟩)⟩
  have h2 := congrFun (congrArg Subtype.val
    (show (wshB1_homToRationalFunctions ω b).val.app (op V) s = 0 from hs)) ⟨Z, hyV⟩
  have h3 : b Z (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf V _ hyV s) = 0 := h2
  exact (b Z).injective (h3.trans (map_zero _).symm)

open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.SheafOfModules.SheafHomStalk in
private lemma wshB1_two_le_depth_stalk_restrict {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (F : X.Modules) (w : W)
    (h : letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val (j w)
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk (j w)) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (j w))) :
    letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((Scheme.Modules.restrictFunctor j).obj F).val w
    (2 : ℕ∞) ≤ Module.depth (W.presheaf.stalk w) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) ((Scheme.Modules.restrictFunctor j).obj F).val.presheaf w) := by
  have : IsLocalRing (ringStalk W.sheaf w) := inferInstanceAs (IsLocalRing (W.presheaf.stalk w))
  have : IsLocalRing (ringStalk X.sheaf (j w)) :=
    inferInstanceAs (IsLocalRing (X.presheaf.stalk (j w)))
  have key := Module.depth_eq_of_semilinearEquiv (restrictStalkRingEquiv j w)
    (IsLocalRing.maximalIdeal (ringStalk W.sheaf w))
    (restrictStalkAddEquiv j F w) (fun r m => restrictStalkHom_smul j F w r m)
  erw [IsLocalRing.map_ringEquiv_maximalIdeal (restrictStalkRingEquiv j w)] at key
  exact key ▸ h

private lemma wshB1_bijective_map_congr (F : X.Modules) {A A' B B' : X.Opens} (hA : A = A') (hB : B = B')
    (h : B ≤ A) (h' : B' ≤ A') (hb : Function.Bijective (F.presheaf.map (homOfLE h).op)) :
    Function.Bijective (F.presheaf.map (homOfLE h').op) := by
  subst hA; subst hB; exact hb

/-- **Hartogs, local form.** If `O ⊆ V` are open and the stalks of the coherent module `F` have
depth `≥ 2` at every point of `V` outside `O`, then restriction `F(V) → F(O)` is bijective
(Stacks, Tag 0E9I, applied to the open subscheme `V`). -/
private lemma wshB1_restriction_bijective_of_depth_ge_two_of_le [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] {O V : X.Opens} (hOV : O ≤ V)
    (hdepth : ∀ x : X, x ∈ V → x ∉ O →
      letI := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier F.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) :
    Function.Bijective (F.presheaf.map (homOfLE hOV).op) := by
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isOpenImmersion V.ι
  have hc : ((Scheme.Modules.restrictFunctor V.ι).obj F).IsCoherent :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion V.ι F ‹_›
  have hb := restriction_bijective_of_depth_ge_two V.toScheme
    ((Scheme.Modules.restrictFunctor V.ι).obj F) (V.ι ⁻¹ᵁ O) (fun x' hx' => by
      refine wshB1_two_le_depth_stalk_restrict V.ι F x' ?_
      exact hdepth (V.ι x') x'.2 hx')
  have hb' : Function.Bijective (F.presheaf.map (homOfLE (show V.ι ''ᵁ (V.ι ⁻¹ᵁ O) ≤ V.ι ''ᵁ ⊤ from
      Set.image_mono (fun _ _ => trivial))).op) := hb
  have hA : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  have hB : V.ι ''ᵁ (V.ι ⁻¹ᵁ O) = O := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hOV hy⟩, hy, rfl⟩
  exact wshB1_bijective_map_congr F (A := V.ι ''ᵁ ⊤) (A' := V) (B := V.ι ''ᵁ (V.ι ⁻¹ᵁ O)) (B' := O)
    hA hB _ hOV hb'

/-- **Core, saturation.** Same hypotheses: every injective `φ : ω ⟶ K(X)` has saturated image.
Proof sketch: `ω` is coherent with depth `≥ 2` at points with `dim 𝒪 ≥ 2`; a section
`s` of `sat(φ(ω))` over an affine `U` lies in `φ(ω)` off a closed set of codimension `≥ 2`, so by
`AlgebraicGeometry.restriction_bijective_of_depth_ge_two` it extends to a section of `ω(U)` that
agrees with `s` at the generic points, hence `s ∈ φ(ω)`. -/
private lemma wshB1_isSaturated_image_of_iso_homology [IsReduced X] [IsNoetherian X]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] {d : ℕ} {ω : X.Modules}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj)
    (φ : ω ⟶ rationalFunctionsModule X)
    (hφ : ∀ U : X.Opens, Function.Injective (φ.val.app (op U))) :
    (imageSubmodule φ).IsSaturated := by
  have hl : IsLocallyNoetherian X := ‹AlgebraicGeometry.IsNoetherian X›.toIsLocallyNoetherian
  have hcoh : _root_.SheafOfModules.IsCoherent ω :=
    AlgebraicGeometry.isCoherent_of_moduleIso e.symm
      ((normalizedDualizingComplexOverField_spec π).2.1 (-(d : ℤ)))
  have hfield : ∀ Z : irreducibleComponents X,
      IsField (X.presheaf.stalk (componentGenericPoint X Z)) := fun Z =>
    isField_stalk_of_closure_mem_irreducibleComponents X _ (by
      rw [(isGenericPoint_componentGenericPoint X Z).def]; exact Z.2)
  refine RationalFunctionsSubmodule.ext fun U => ?_
  refine le_antisymm ?_ ?_
  · intro s hs η hη _
    exact ⟨U, hη, s, hs, rfl⟩
  · intro s hs
    have hnat : ∀ {U V : X.Opens} (j : V ⟶ U) (g : ω.val.obj (op U)),
        ((φ.val.app (op V)) ((ω.val.map j.op) g)).1 =
          (rationalFunctionsPresheaf X).map j.op ((φ.val.app (op U) g).1) := fun j g =>
      congrArg Subtype.val (ConcreteCategory.congr_hom (φ.val.naturality j.op) g)
    let O : X.Opens := ⨆ W : {W : X.Opens // ∃ h : W ≤ U,
      (rationalFunctionsPresheaf X).map (homOfLE h).op s ∈ (imageSubmodule φ).sections W}, W.1
    have hOU : O ≤ U := iSup_le fun W => W.2.1
    have hsO : (rationalFunctionsPresheaf X).map (homOfLE hOU).op s ∈
        (imageSubmodule φ).sections O := by
      refine (imageSubmodule φ).mem_of_locally fun x hx => ?_
      obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp hx
      exact ⟨W.1, homOfLE (le_iSup (fun W : {W : X.Opens // ∃ h : W ≤ U,
        (rationalFunctionsPresheaf X).map (homOfLE h).op s ∈ (imageSubmodule φ).sections W} =>
          W.1) W), hxW, W.2.2⟩
    have hbad : ∀ y : X, y ∈ U → y ∉ O → (2 : ℕ∞) ≤ Order.coheight y := by
      intro y hy hyO
      by_contra hc
      have hc1 : Order.coheight y ≤ 1 := by
        by_contra h1
        refine hc ?_
        have h1' : 1 < Order.coheight y := not_le.mp h1
        generalize Order.coheight y = c at h1'
        induction c using ENat.recTopCoe with
        | top => exact le_top
        | coe n =>
          have : 1 < n := by exact_mod_cast h1'
          exact_mod_cast this
      obtain ⟨W, i, hyW, hmem⟩ := ((imageSubmodule φ).germ_mem_stalkSet_iff hy s).mp (hs y hy hc1)
      exact hyO (Opens.mem_iSup.mpr ⟨⟨W, i.le, hmem⟩, hyW⟩)
    obtain ⟨t, ht⟩ := wshC_exists_preimage_of_mem_imageSubmodule φ hφ hsO
    have hbij := wshB1_restriction_bijective_of_depth_ge_two_of_le ω hOU (fun y hy hyO => by
      obtain ⟨h, hh, hdep⟩ := wshB1_exists_depth_le_of_iso hd e y
      have h2 : (2 : ℕ∞) ≤ Order.coheight y := hbad y hy hyO
      rw [ringKrullDim_stalk_eq_coheight] at hh
      have h3 : (2 : ℕ∞) ≤ h := by
        have : Order.coheight y = (h : ℕ∞) := by exact_mod_cast hh
        rwa [this] at h2
      rwa [min_eq_right h3] at hdep)
    obtain ⟨t', ht'⟩ := hbij.2 t
    have hgen : ∀ Z : irreducibleComponents X, componentGenericPoint X Z ∈ U →
        componentGenericPoint X Z ∈ O := by
      intro Z hZ
      by_contra hZO
      have h2 := hbad _ hZ hZO
      have h0 := ringKrullDim_eq_zero_of_isField (hfield Z)
      rw [ringKrullDim_stalk_eq_coheight] at h0
      have : Order.coheight (componentGenericPoint X Z) = 0 := by exact_mod_cast h0
      rw [this] at h2
      exact absurd h2 (by norm_num)
    have hφt : ((φ.val.app (op U)) t').1 = s := by
      funext Z
      have h1 := hnat (homOfLE hOU) t'
      have h2 : (rationalFunctionsPresheaf X).map (homOfLE hOU).op ((φ.val.app (op U) t').1) =
          (rationalFunctionsPresheaf X).map (homOfLE hOU).op s := by
        refine h1.symm.trans (Eq.trans ?_ ht)
        have : (ω.val.map (homOfLE hOU).op) t' = t := ht'
        rw [this]
      exact congrFun h2 ⟨Z.1, hgen Z.1 Z.2⟩
    rw [imageSubmodule, RationalFunctionsSubmodule.mem_localClosure_iff]
    intro x hx
    refine ⟨U, 𝟙 U, hx, ?_⟩
    rw [rationalFunctionsPresheaf_map_id_apply]
    exact Submodule.subset_span ⟨t', hφt⟩

end WShB1Dualizing

/-! ### Saturation -/

namespace RationalFunctionsSubmodule

section Coherent

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Finiteness of `sat(𝒪_X)` over an affine open.** Let `X` be reduced, of finite type over a
field and of pure dimension `d`, and `U ⊆ X` an affine open. Then `sat(𝒪_X)(U)` is a finite
`Γ(X, U)`-module. The canonical module `ω = H^{-d}(K_X)` embeds into `K(X)` by some `φ` with
saturated image; a section `u ∈ φ(ω)(U)` nonzero at every generic point of `U` gives an injective
`Γ(X, U)`-linear map `s ↦ u s` from `sat(𝒪_X)(U)` into the finite module `φ(ω(U))`. -/
private theorem wshB1_finite_saturation_unit [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) ((RationalFunctionsSubmodule.unit X).saturation.sections U) := by
  classical
  have hl : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let ω : X.Modules := (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
    (normalizedDualizingComplexOverField π).complex.obj.obj
  let e : ω ≅ (DerivedCategory.homologyFunctor X.Modules (-(d : ℤ))).obj
      (normalizedDualizingComplexOverField π).complex.obj.obj := Iso.refl _
  have hcoh : _root_.SheafOfModules.IsCoherent ω :=
    AlgebraicGeometry.isCoherent_of_moduleIso e.symm
      ((normalizedDualizingComplexOverField_spec π).2.1 (-(d : ℤ)))
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent ω
  have hfield : ∀ Z : irreducibleComponents X,
      IsField (X.presheaf.stalk (componentGenericPoint X Z)) := fun Z =>
    RationalFunctions.isField_stalk X Z
  let b := fun Z : irreducibleComponents X =>
    (wshB1_nonempty_stalk_linearEquiv_of_isField hd e _ (hfield Z)).some
  let φ := wshB1_homToRationalFunctions ω b
  have hφ : ∀ V : X.Opens, Function.Injective (φ.val.app (op V)) :=
    wshB1_injective_homToRationalFunctions hd e b
  have hsat : imageSubmodule φ = (imageSubmodule φ).saturation :=
    wshB1_isSaturated_image_of_iso_homology hd e φ hφ
  have hmemG : ∀ t : ω.val.obj (op U), ((φ.val.app (op U)) t).1 ∈ (imageSubmodule φ).sections U := by
    intro t
    rw [imageSubmodule, RationalFunctionsSubmodule.mem_localClosure_iff]
    intro x hx
    exact ⟨U, 𝟙 U, hx, Submodule.subset_span ⟨t, rfl⟩⟩
  have hN : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U},
      ∃ g ∈ (imageSubmodule φ).sections U, g Z ≠ 0 := by
    intro Z
    have := (hfield Z.1).nontrivial
    let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ω.val (componentGenericPoint X Z.1)
    obtain ⟨V, hζV, s0, hs0⟩ :=
      TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) ω.val.presheaf ((b Z.1).symm 1)
    obtain ⟨c, hcV, hζc0⟩ := hU.exists_basicOpen_le (⟨_, hζV⟩ : V) Z.2
    have hζc : componentGenericPoint X Z.1 ∈ X.basicOpen c := hζc0
    let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE ω (X.basicOpen_le c)
    have hloc := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ
      ω hU c rfl (X.basicOpen_le c)
    let y : Γ(ω, X.basicOpen c) := ω.val.map (homOfLE hcV).op s0
    obtain ⟨⟨s1, ⟨-, n, rfl⟩⟩, hs1⟩ := IsLocalizedModule.surj (Submonoid.powers c)
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ ω (X.basicOpen_le c)) y
    refine ⟨_, hmemG s1, ?_⟩
    have hval : ((φ.val.app (op U)) s1).1 Z =
        b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2 s1) := rfl
    rw [hval]
    have hg1 : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf U _ Z.2 s1 =
        TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf (X.basicOpen c) _ hζc
          (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ ω (X.basicOpen_le c) s1) :=
      (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf
        (homOfLE (X.basicOpen_le c)) _ hζc s1).symm
    rw [hg1, ← hs1]
    have h1 := PresheafOfModules.germ_smul (R := X.presheaf) ω.val (componentGenericPoint X Z.1)
      (X.basicOpen c) hζc (X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ n)) y
    have h2 : TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf (X.basicOpen c) _ hζc y =
        (b Z.1).symm 1 := by
      rw [← hs0]
      exact TopCat.Presheaf.germ_res_apply (C := Ab.{u}) ω.val.presheaf (homOfLE hcV) _ hζc s0
    have h3 : b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf (X.basicOpen c) _ hζc
        ((⟨c ^ n, n, rfl⟩ : Submonoid.powers c) • y)) =
        X.presheaf.germ U _ Z.2 c ^ n := by
      have h4 : b Z.1 (TopCat.Presheaf.germ (C := Ab.{u}) ω.val.presheaf (X.basicOpen c) _ hζc y) =
          1 := by
        rw [h2]
        exact LinearEquiv.apply_symm_apply _ _
      refine (congrArg (b Z.1) h1).trans ((map_smul (b Z.1) _ _).trans ?_)
      erw [h4]
      rw [smul_eq_mul, mul_one, TopCat.Presheaf.germ_res_apply, map_pow]
    rw [h3]
    have hu : IsUnit (X.presheaf.germ U _ Z.2 c) := (Scheme.mem_basicOpen X c _ Z.2).mp hζc
    exact (hu.pow n).ne_zero
  obtain ⟨u, huG, hu0⟩ := wshB1_exists_forall_ne_zero hU _ hN
  have huS : ∀ s ∈ (RationalFunctionsSubmodule.unit X).saturation.sections U,
      u * s ∈ (imageSubmodule φ).sections U := by
    intro s hs
    have h1 : u * s ∈ (imageSubmodule φ).saturation.sections U := by
      intro η hη hc
      obtain ⟨W, i, hηW, hW⟩ :=
        ((RationalFunctionsSubmodule.unit X).germ_mem_stalkSet_iff hη s).mp (hs η hη hc)
      obtain ⟨r, hr⟩ := exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit hW
      refine ((imageSubmodule φ).germ_mem_stalkSet_iff hη _).mpr ⟨W, i, hηW, ?_⟩
      rw [map_mul, ← hr]
      have : (rationalFunctionsPresheaf X).map i.op u * (toRationalFunctionsPresheaf X).app (op W) r =
          r • (rationalFunctionsPresheaf X).map i.op u := by
        rw [Algebra.smul_def, mul_comm]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ ((imageSubmodule φ).map_mem i huG)
    rwa [← hsat] at h1
  let Lφ0 : Γ(ω, U) →ₗ[Γ(X, U)] (RationalFunctionsSubmodule.top X).sections U :=
    (φ.val.app (op U)).hom
  let Lφ : Γ(ω, U) →ₗ[Γ(X, U)] ToType ((rationalFunctionsPresheaf X).obj (op U)) :=
    ((RationalFunctionsSubmodule.top X).sections U).subtype ∘ₗ Lφ0
  have : Module.Finite Γ(X, U) Γ(ω, U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections ω hU
  let ψ : (RationalFunctionsSubmodule.unit X).saturation.sections U →ₗ[Γ(X, U)]
      LinearMap.range Lφ :=
    { toFun := fun s => ⟨u * s.1, by
        obtain ⟨t, ht⟩ := wshC_exists_preimage_of_mem_imageSubmodule φ hφ (huS s.1 s.2)
        exact show ∃ y, Lφ y = u * s.1 from ⟨t, ht⟩⟩
      map_add' := fun s s' => Subtype.ext (mul_add _ _ _)
      map_smul' := fun r s => Subtype.ext (mul_smul_comm _ _ _) }
  have hψ : Function.Injective ψ := by
    intro s s' h
    have h' := congrArg Subtype.val h
    apply Subtype.ext
    funext Z
    have hZ : u Z * s.1 Z = u Z * s'.1 Z := congrFun h' Z
    obtain ⟨v, hv⟩ := (RationalFunctions.isField_stalk X Z.1).mul_inv_cancel (hu0 Z)
    calc s.1 Z = v * u Z * s.1 Z := by rw [mul_comm v, hv, one_mul]
      _ = v * u Z * s'.1 Z := by rw [mul_assoc, hZ, ← mul_assoc]
      _ = s'.1 Z := by rw [mul_comm v, hv, one_mul]
  have : _root_.IsNoetherian Γ(X, U) (LinearMap.range Lφ) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective ψ hψ

/-- **Coherence of codimension-one saturation in the total quotient sheaf.** Let `X` be a reduced
scheme of finite type over a field, of pure dimension, and `𝓕 ⊆ K(X)` a coherent
`𝒪_X`-submodule. Then `sat(𝓕)` is a coherent `𝒪_X`-module. -/
@[mmp "lem_mmp_foundation_codimension_one_saturation_coherent"]
theorem isCoherent_saturation [IsReduced X] [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ} (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    {F : RationalFunctionsSubmodule X} (hF : SheafOfModules.IsCoherent F.toModules) :
    SheafOfModules.IsCoherent F.saturation.toModules := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have := hF
  have : F.toModules.IsFiniteType := hF.isFiniteType
  have : F.toModules.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  have : F.saturation.toModules.IsQuasicoherent :=
    wshB_isQuasicoherent _ fun U hU a t ht =>
      wshB1_hasExt_saturation hU (wshB1_hasExt_of_isQuasicoherent F hU) a t ht
  exact wshB_isCoherent_of_finite _ fun U hU =>
    wshB1_finite_saturation hU (wshB1_finite_saturation_unit π hd hU)

end Coherent

section UnitSmul

variable {Y : Scheme.{u}}

private lemma wshA_unit_mul_inv (f : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ)
    (W : Y.Opens) :
    (rationalFunctionsPresheaf Y).map (homOfLE (le_top : W ≤ ⊤)).op
        ((f⁻¹ : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ) :
          ToType ((rationalFunctionsPresheaf Y).obj (op ⊤))) *
      (rationalFunctionsPresheaf Y).map (homOfLE (le_top : W ≤ ⊤)).op
        (f : ToType ((rationalFunctionsPresheaf Y).obj (op ⊤))) = 1 := by
  rw [← map_mul]; simp

/-- The submodule `f · 𝓖 ⊆ K(Y)` for a unit `f` of `K(Y)(Y)`: its sections over `W` are the
`f|_W g` with `g ∈ 𝓖(W)`. -/
def unitSmul (f : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ)
    (G : RationalFunctionsSubmodule Y) : RationalFunctionsSubmodule Y where
  sections W := Submodule.map
    (LinearMap.mulLeft Γ(Y, W) ((rationalFunctionsPresheaf Y).map (homOfLE le_top).op
      (f : ToType ((rationalFunctionsPresheaf Y).obj (op ⊤))))) (G.sections W)
  map_mem := by
    rintro U V i _ ⟨g, hg, rfl⟩
    refine ⟨(rationalFunctionsPresheaf Y).map i.op g, G.map_mem i hg, ?_⟩
    simp only [LinearMap.mulLeft_apply, map_mul]
    rfl
  mem_of_locally := by
    intro U s hs
    refine ⟨(rationalFunctionsPresheaf Y).map (homOfLE (le_top : U ≤ ⊤)).op
      ((f⁻¹ : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ) :
        ToType ((rationalFunctionsPresheaf Y).obj (op ⊤))) * s, ?_, ?_⟩
    · refine G.mem_of_locally fun x hx => ?_
      obtain ⟨W, i, hxW, g, hg, hgs⟩ := hs x hx
      refine ⟨W, i, hxW, ?_⟩
      simp only [LinearMap.mulLeft_apply] at hgs
      rw [map_mul, ← hgs, ← mul_assoc]
      have := wshA_unit_mul_inv f W
      have h1 : (rationalFunctionsPresheaf Y).map i.op
          ((rationalFunctionsPresheaf Y).map (homOfLE (le_top : U ≤ ⊤)).op
            ((f⁻¹ : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ) :
              ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))) =
          (rationalFunctionsPresheaf Y).map (homOfLE (le_top : W ≤ ⊤)).op
            ((f⁻¹ : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ) :
              ToType ((rationalFunctionsPresheaf Y).obj (op ⊤))) := rfl
      rw [h1, this, one_mul]; exact hg
    · simp only [LinearMap.mulLeft_apply]
      rw [← mul_assoc]
      have := wshA_unit_mul_inv f U
      rw [mul_comm _ (_ : ToType ((rationalFunctionsPresheaf Y).obj (op U)))] at this
      rw [this, one_mul]

private lemma wshA_mem_unitSmul_iff (f : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ)
    (G : RationalFunctionsSubmodule Y) (W : Y.Opens)
    (s : ToType ((rationalFunctionsPresheaf Y).obj (op W))) :
    s ∈ (unitSmul f G).sections W ↔
      (rationalFunctionsPresheaf Y).map (homOfLE (le_top : W ≤ ⊤)).op
        ((f⁻¹ : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ) :
          ToType ((rationalFunctionsPresheaf Y).obj (op ⊤))) * s ∈ G.sections W := by
  have h1 := wshA_unit_mul_inv f W
  have h2 := h1
  rw [mul_comm] at h2
  constructor
  · rintro ⟨g, hg, rfl⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← mul_assoc, h1, one_mul]; exact hg
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← mul_assoc, h2, one_mul]

/-- **FA Def. 16.1.2, multiplication by a unit and saturation** (a). If `f` is a unit of
`K(Y)(Y)`, then `f · sat(𝓖) = sat(f · 𝓖)` for every `𝒪_Y`-submodule `𝓖 ⊆ K(Y)`. Applied to an open
subscheme `V ⊆ X` this is the statement for a unit `f ∈ K(X)(V)` and an `𝒪_V`-submodule of
`K(X)|_V`. -/
@[mmp "lem_fa16a_unit_multiplication_saturation"]
theorem unitSmul_saturation (f : (ToType ((rationalFunctionsPresheaf Y).obj (op ⊤)))ˣ)
    (G : RationalFunctionsSubmodule Y) :
    unitSmul f G.saturation = (unitSmul f G).saturation := by
  ext V s
  rw [wshA_mem_unitSmul_iff, mem_saturation_iff, mem_saturation_iff]
  refine forall_congr' fun η => forall_congr' fun hη => imp_congr_right fun _ => ?_
  rw [germ_mem_stalkSet_iff, germ_mem_stalkSet_iff]
  refine exists_congr fun W => exists_congr fun i => and_congr_right fun _ => ?_
  rw [wshA_mem_unitSmul_iff, map_mul]
  rfl

end UnitSmul

end RationalFunctionsSubmodule

namespace WeilDivisorialSubsheaf

variable {X : Scheme.{u}}

/-- The generic point of an irreducible component has coheight at most one. -/
lemma _root_.MMP.Flips.coheight_componentGenericPoint_le_one (Z : irreducibleComponents X) :
    Order.coheight (componentGenericPoint X Z) ≤ 1 :=
  (wshB1_coheight_componentGenericPoint Z).trans_le zero_le_one

/-- At the generic point of a component, a Weil divisorial subsheaf has a local generator `l₀`
that is nonzero at the generic point, and every section is locally an `𝒪`-multiple of it. -/
private lemma wshA_exists_generator (L : WeilDivisorialSubsheaf X) (Z : irreducibleComponents X) :
    ∃ (W0 : X.Opens) (hz0 : componentGenericPoint X Z ∈ W0)
      (l0 : ToType ((rationalFunctionsPresheaf X).obj (op W0))),
      l0 ∈ L.sections W0 ∧ l0 ⟨Z, hz0⟩ ≠ 0 ∧
      ∀ (W : X.Opens) (_ : componentGenericPoint X Z ∈ W)
        (l : ToType ((rationalFunctionsPresheaf X).obj (op W))), l ∈ L.sections W →
        ∃ (W1 : X.Opens) (i1 : W1 ⟶ W) (i0 : W1 ⟶ W0) (_ : componentGenericPoint X Z ∈ W1)
          (a : Γ(X, W1)), (rationalFunctionsPresheaf X).map i1.op l =
            a • (rationalFunctionsPresheaf X).map i0.op l0 := by
  set z := componentGenericPoint X Z with hzdef
  obtain ⟨g, hg⟩ := L.principal_codim_one z (coheight_componentGenericPoint_le_one Z)
  have hgmem : (g : (rationalFunctionsPresheaf X).stalk z) ∈ L.stalkSet z := by
    rw [hg]; exact ⟨1, by simp⟩
  obtain ⟨V0, hxV0, s0, hs0, hgerm0⟩ := hgmem
  obtain ⟨V1, hxV1, s1, hs1⟩ := TopCat.Presheaf.exists_germ_eq (rationalFunctionsPresheaf X)
    (x := z) ((g⁻¹ : ((rationalFunctionsPresheaf X).stalk z)ˣ) :
      (rationalFunctionsPresheaf X).stalk z)
  have hxm : z ∈ V0 ⊓ V1 := ⟨hxV0, hxV1⟩
  have hprod : (rationalFunctionsPresheaf X).germ (V0 ⊓ V1) z hxm
      ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op s0 *
        (rationalFunctionsPresheaf X).map (homOfLE inf_le_right).op s1) =
      (rationalFunctionsPresheaf X).germ (V0 ⊓ V1) z hxm 1 := by
    rw [map_mul, map_one, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      hgerm0, hs1]
    simp
  obtain ⟨W2, hz2, iU, iV, hW2⟩ := TopCat.Presheaf.germ_eq _ z _ _ _ _ hprod
  rw [map_one, map_mul] at hW2
  have hW2' := congrFun hW2 ⟨Z, hz2⟩
  refine ⟨W2, hz2, (rationalFunctionsPresheaf X).map (iU ≫ homOfLE inf_le_left).op s0,
    L.map_mem _ hs0, ?_, ?_⟩
  · intro h0
    have h3 : ((rationalFunctionsPresheaf X).map (iU ≫ homOfLE inf_le_left).op s0 ⟨Z, hz2⟩) *
        ((rationalFunctionsPresheaf X).map (iU ≫ homOfLE inf_le_right).op s1 ⟨Z, hz2⟩) = 1 :=
      hW2'
    rw [h0, zero_mul] at h3
    exact zero_ne_one h3
  · intro W hzW l hl
    have hmem : (rationalFunctionsPresheaf X).germ W z hzW l ∈ L.stalkSet z :=
      ⟨W, hzW, l, hl, rfl⟩
    rw [hg] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨W3, hz3, a0, ha0⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (x := z) b
    have hstruct : (structureStalkToRationalFunctionsStalk X z).hom b =
        (rationalFunctionsPresheaf X).germ W3 z hz3
          ((toRationalFunctionsPresheaf X).app (op W3) a0) := by
      rw [← ha0]
      have := ConcreteCategory.congr_hom (TopCat.Presheaf.stalkFunctor_map_germ
        (F := X.presheaf) (G := rationalFunctionsPresheaf X) W3 z hz3
        (toRationalFunctionsPresheaf X)) a0
      simp [structureStalkToRationalFunctionsStalk] at this ⊢
    have hxm3 : z ∈ W2 ⊓ W3 := ⟨hz2, hz3⟩
    have key : (rationalFunctionsPresheaf X).germ (W2 ⊓ W3) z hxm3
        ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op
          ((rationalFunctionsPresheaf X).map (iU ≫ homOfLE inf_le_left).op s0) *
         (rationalFunctionsPresheaf X).map (homOfLE inf_le_right).op
          ((toRationalFunctionsPresheaf X).app (op W3) a0)) =
        (rationalFunctionsPresheaf X).germ W z hzW l := by
      simp only [map_mul, TopCat.Presheaf.germ_res_apply]
      rw [hgerm0, ← hstruct]
      exact hb
    obtain ⟨W1, hz1, jU, jV, hj⟩ := TopCat.Presheaf.germ_eq _ z _ _ _ _ key
    rw [map_mul] at hj
    refine ⟨W1, jV, jU ≫ homOfLE inf_le_left, hz1,
      X.presheaf.map (jU ≫ homOfLE inf_le_right).op a0, ?_⟩
    rw [← hj, Algebra.smul_def]
    change _ = ((toRationalFunctionsPresheaf X).app (op W1) (X.presheaf.map _ a0)) * _
    rw [toRationalFunctionsPresheaf_app_map, mul_comm]
    rfl

/-- **FA Def. 16.1.2, multiplication by a unit and saturation** (b). Let `X` be reduced.
If `𝓛` is a Weil divisorial subsheaf and `𝓛|_V = f 𝒪_V` is free with generator
`f ∈ K(X)(V)` (every section of `𝓛` over `W ⊆ V` is `a f|_W` for a unique `a ∈ Γ(X, W)`), then `f`
is a unit of `K(X)(V)`. -/
@[mmp "lem_fa16a_unit_multiplication_saturation"]
theorem isUnit_of_free [IsReduced X] (L : WeilDivisorialSubsheaf X) {V : X.Opens}
    (f : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hf : ∀ (W : X.Opens) (i : W ⟶ V) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      l ∈ L.sections W ↔ ∃ a : Γ(X, W), l = a • (rationalFunctionsPresheaf X).map i.op f)
    (hinj : ∀ (W : X.Opens) (i : W ⟶ V) (a : Γ(X, W)),
      a • (rationalFunctionsPresheaf X).map i.op f = 0 → a = 0) :
    IsUnit f := by
  refine (Pi.isUnit_iff (x := (f : ∀ Z : {Z : irreducibleComponents X //
      componentGenericPoint X Z ∈ V}, X.presheaf.stalk (componentGenericPoint X Z.1)))).mpr ?_
  rintro ⟨Z, hZ⟩
  obtain ⟨W0, hz0, l0, hl0, hne, -⟩ := WeilDivisorialSubsheaf.wshA_exists_generator L Z
  obtain ⟨a, ha⟩ := (hf (W0 ⊓ V) (homOfLE inf_le_right)
    ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op l0)).mp (L.map_mem _ hl0)
  have h1 := congrFun ha ⟨Z, ⟨hz0, hZ⟩⟩
  have h2 : l0 ⟨Z, hz0⟩ = X.presheaf.germ (W0 ⊓ V) _ ⟨hz0, hZ⟩ a * f ⟨Z, hZ⟩ := h1
  let _ := (RationalFunctions.isField_stalk X Z).toField
  refine IsUnit.mk0 _ fun h0 => hne ?_
  rw [h2, h0, mul_zero]

/-! ### The group `WSh(X)` -/

/-- A Weil divisorial subsheaf is determined by its underlying submodule of `K(X)`. -/
theorem ext' {L L' : WeilDivisorialSubsheaf X}
    (h : L.toRationalFunctionsSubmodule = L'.toRationalFunctionsSubmodule) : L = L' := by
  cases L
  cases L'
  cases h
  rfl

end WeilDivisorialSubsheaf

section Group

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- `G` is a commutative group structure on `WSh(X)` whose product, neutral element and inverse
are `𝓛 · 𝓛'`, `sat(𝒪_X)` and `𝓛⁻¹`. -/
structure IsWShGroup (G : CommGroup (WeilDivisorialSubsheaf X)) : Prop where
  mul_eq : ∀ L L' : WeilDivisorialSubsheaf X,
    (G.mul L L').toRationalFunctionsSubmodule = L.mul L'
  one_eq : (G.one : WeilDivisorialSubsheaf X).toRationalFunctionsSubmodule =
    (RationalFunctionsSubmodule.unit X).saturation
  inv_eq : ∀ L : WeilDivisorialSubsheaf X, (G.inv L).toRationalFunctionsSubmodule = L.inv

private lemma wshA_struct_germ {W : X.Opens} {η : X} (hx : η ∈ W) (a : Γ(X, W)) :
    (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ W η hx a) =
      (rationalFunctionsPresheaf X).germ W η hx
        ((toRationalFunctionsPresheaf X).app (op W) a) := by
  have := ConcreteCategory.congr_hom (TopCat.Presheaf.stalkFunctor_map_germ
    (F := X.presheaf) (G := rationalFunctionsPresheaf X) W η hx
    (toRationalFunctionsPresheaf X)) a
  simp [structureStalkToRationalFunctionsStalk] at this ⊢

private lemma wshA_germ_smul {W : X.Opens} {η : X} (hx : η ∈ W) (a : Γ(X, W))
    (s : ToType ((rationalFunctionsPresheaf X).obj (op W))) :
    (rationalFunctionsPresheaf X).germ W η hx (a • s) =
      (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ W η hx a) *
        (rationalFunctionsPresheaf X).germ W η hx s := by
  rw [wshA_struct_germ, Algebra.smul_def, map_mul]
  rfl

private lemma wshA_stalkSet_saturation (F : RationalFunctionsSubmodule X) (η : X)
    (hη : Order.coheight η ≤ 1) : F.saturation.stalkSet η = F.stalkSet η := by
  ext y
  constructor
  · rintro ⟨V, hx, s, hs, rfl⟩
    exact hs η hx hη
  · rintro ⟨V, hx, s, hs, rfl⟩
    refine ⟨V, hx, s, fun η' hη' _ => ⟨V, hη', s, hs, rfl⟩, rfl⟩

private lemma wshA_stalkSet_unit (η : X) :
    (RationalFunctionsSubmodule.unit X).stalkSet η =
      Set.range (structureStalkToRationalFunctionsStalk X η).hom := by
  ext y
  constructor
  · rintro ⟨V, hx, s, hs, rfl⟩
    obtain ⟨W, i, hxW, hmem⟩ := hs η hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hmem
    refine ⟨X.presheaf.germ W η hxW r, ?_⟩
    rw [wshA_struct_germ, ← TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) i η hxW s,
      ← hr]
    rfl
  · rintro ⟨b, rfl⟩
    obtain ⟨W, hW, a0, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (x := η) b
    refine ⟨W, hW, (toRationalFunctionsPresheaf X).app (op W) a0, ?_, (wshA_struct_germ hW a0).symm⟩
    intro x hx
    exact ⟨W, 𝟙 W, hx, Submodule.mem_one.mpr ⟨a0, rfl⟩⟩

private lemma wshA_stalkSet_mulImage (L L' : RationalFunctionsSubmodule X) (η : X)
    (f g : ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hf : L.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (f : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a)
    (hg : L'.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (g : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a) :
    (RationalFunctionsSubmodule.mulImage L L').stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        ((f * g : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a := by
  ext y
  constructor
  · rintro ⟨V, hxV, s, hs, rfl⟩
    obtain ⟨W, i, hxW, hW⟩ := hs η hxV
    rw [← TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) i η hxW s]
    generalize (rationalFunctionsPresheaf X).map i.op s = t at hW
    refine Submodule.mul_induction_on hW (fun a ha b hb => ?_) (fun a b ⟨α, hα⟩ ⟨β, hβ⟩ => ?_)
    · have ha' : (rationalFunctionsPresheaf X).germ W η hxW a ∈ L.stalkSet η :=
        ⟨W, hxW, a, ha, rfl⟩
      have hb' : (rationalFunctionsPresheaf X).germ W η hxW b ∈ L'.stalkSet η :=
        ⟨W, hxW, b, hb, rfl⟩
      rw [hf] at ha'
      rw [hg] at hb'
      obtain ⟨α, hα⟩ := ha'
      obtain ⟨β, hβ⟩ := hb'
      refine ⟨α * β, ?_⟩
      simp only [Units.val_mul, map_mul]
      have hα' : (f : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom α =
          (rationalFunctionsPresheaf X).germ W η hxW a := hα
      have hβ' : (g : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom β =
          (rationalFunctionsPresheaf X).germ W η hxW b := hβ
      rw [← hα', ← hβ']
      ring
    · refine ⟨α + β, ?_⟩
      simp only [map_add, mul_add]
      exact congrArg₂ (· + ·) hα hβ
  · rintro ⟨c, rfl⟩
    have hf1 : (f : (rationalFunctionsPresheaf X).stalk η) ∈ L.stalkSet η := by
      rw [hf]; exact ⟨1, by simp⟩
    have hg1 : (g : (rationalFunctionsPresheaf X).stalk η) ∈ L'.stalkSet η := by
      rw [hg]; exact ⟨1, by simp⟩
    obtain ⟨V1, h1, s1, hs1, e1⟩ := hf1
    obtain ⟨V2, h2, s2, hs2, e2⟩ := hg1
    obtain ⟨W3, h3, a0, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (x := η) c
    have hxW : η ∈ (V1 ⊓ V2) ⊓ W3 := ⟨⟨h1, h2⟩, h3⟩
    set W := (V1 ⊓ V2) ⊓ W3 with hWdef
    let a0W : Γ(X, W) := X.presheaf.map (homOfLE (inf_le_right : W ≤ W3)).op a0
    let s1W := (rationalFunctionsPresheaf X).map
      (homOfLE ((inf_le_left : W ≤ V1 ⊓ V2).trans inf_le_left)).op s1
    let s2W := (rationalFunctionsPresheaf X).map
      (homOfLE ((inf_le_left : W ≤ V1 ⊓ V2).trans inf_le_right)).op s2
    have ht : (a0W • s1W) * s2W ∈ L.sections W * L'.sections W :=
      Submodule.mul_mem_mul (Submodule.smul_mem _ _ (L.map_mem _ hs1)) (L'.map_mem _ hs2)
    refine ⟨W, hxW, (a0W • s1W) * s2W, fun x hx => ⟨W, 𝟙 W, hx, ht⟩, ?_⟩
    rw [map_mul, wshA_germ_smul]
    have e1' : (rationalFunctionsPresheaf X).germ W η hxW s1W = f := by
      rw [← e1]; exact TopCat.Presheaf.germ_res_apply _ _ η _ s1
    have e2' : (rationalFunctionsPresheaf X).germ W η hxW s2W = g := by
      rw [← e2]; exact TopCat.Presheaf.germ_res_apply _ _ η _ s2
    have e3 : X.presheaf.germ W η hxW a0W = X.presheaf.germ W3 η h3 a0 :=
      TopCat.Presheaf.germ_res_apply _ _ η _ a0
    rw [e1', e2', e3, Units.val_mul]
    ring

private lemma wshA_stalkSet_inv_subset (L : RationalFunctionsSubmodule X) (η : X)
    (hη : Order.coheight η ≤ 1) (f : ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hf : L.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (f : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a) :
    L.inv.stalkSet η ⊆ Set.range fun a : X.presheaf.stalk η =>
        ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a := by
  rintro _ ⟨V, hxV, x, hx, rfl⟩
  have hf1 : (f : (rationalFunctionsPresheaf X).stalk η) ∈ L.stalkSet η := by
    rw [hf]; exact ⟨1, by simp⟩
  obtain ⟨V1, h1, s1, hs1, e1⟩ := hf1
  have hxm : η ∈ V ⊓ V1 := ⟨hxV, h1⟩
  have hmem := hx (V ⊓ V1) (homOfLE inf_le_left)
    ((rationalFunctionsPresheaf X).map (homOfLE inf_le_right).op s1) (L.map_mem _ hs1)
  have hg := hmem η hxm hη
  rw [wshA_stalkSet_unit] at hg
  obtain ⟨b, hb⟩ := hg
  refine ⟨b, ?_⟩
  have hb' : (structureStalkToRationalFunctionsStalk X η).hom b =
      (rationalFunctionsPresheaf X).germ V η hxV x * f := by
    rw [hb, map_mul]
    congr 1
    · exact TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : V ⊓ V1 ≤ V)) η hxm x
    · rw [← e1]; exact TopCat.Presheaf.germ_res_apply _ _ η _ s1
  show ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
    (structureStalkToRationalFunctionsStalk X η).hom b = _
  rw [hb', mul_comm _ (f : (rationalFunctionsPresheaf X).stalk η), ← mul_assoc, Units.inv_mul,
    one_mul]

private lemma wshA_stalkSet_inv_supset (L : WeilDivisorialSubsheaf X) (η : X)
    (_hη : Order.coheight η ≤ 1) (f : ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hf : L.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (f : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a) :
    (Set.range fun a : X.presheaf.stalk η =>
        ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a) ⊆ L.inv.stalkSet η := by
  rintro _ ⟨c, rfl⟩
  obtain ⟨V, hηV, J, hJ, t, ht⟩ := Stacks.SheafOfModules.LocallySurjective.exists_local_generators
    (X := X.toRingedSpace) (F := L.toModules)
    L.isCoherent.isFiniteType η
  obtain ⟨V2, h2, x0, hx0⟩ := TopCat.Presheaf.exists_germ_eq (rationalFunctionsPresheaf X) (x := η)
    (((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
      (structureStalkToRationalFunctionsStalk X η).hom c)
  have hη12 : η ∈ V ⊓ V2 := ⟨hηV, h2⟩
  have hj : ∀ j : J, ∃ (Wj : X.Opens) (ij : Wj ⟶ V ⊓ V2), η ∈ Wj ∧
      (rationalFunctionsPresheaf X).map ij.op
        ((rationalFunctionsPresheaf X).map (homOfLE (inf_le_right : V ⊓ V2 ≤ V2)).op x0 *
          (rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : V ⊓ V2 ≤ V)).op
            (t j : L.sections V).1) ∈ (RationalFunctionsSubmodule.unit X).sections Wj := by
    intro j
    have hgj : (rationalFunctionsPresheaf X).germ V η hηV (t j : L.sections V).1 ∈
        L.stalkSet η := ⟨V, hηV, _, (t j : L.sections V).2, rfl⟩
    rw [hf] at hgj
    obtain ⟨b, hb⟩ := hgj
    have hb' : (f : (rationalFunctionsPresheaf X).stalk η) *
        (structureStalkToRationalFunctionsStalk X η).hom b =
        (rationalFunctionsPresheaf X).germ V η hηV (t j : L.sections V).1 := hb
    have hP : (rationalFunctionsPresheaf X).germ (V ⊓ V2) η hη12
        ((rationalFunctionsPresheaf X).map (homOfLE (inf_le_right : V ⊓ V2 ≤ V2)).op x0 *
          (rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : V ⊓ V2 ≤ V)).op
            (t j : L.sections V).1) ∈ (RationalFunctionsSubmodule.unit X).stalkSet η := by
      rw [wshA_stalkSet_unit]
      refine ⟨c * b, ?_⟩
      simp only [map_mul, TopCat.Presheaf.germ_res_apply]
      rw [hx0, ← hb']
      symm
      calc _ = ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
              (rationalFunctionsPresheaf X).stalk η) * (f : (rationalFunctionsPresheaf X).stalk η) *
            ((structureStalkToRationalFunctionsStalk X η).hom c *
              (structureStalkToRationalFunctionsStalk X η).hom b) := by ring
        _ = _ := by rw [Units.inv_mul, one_mul]
    obtain ⟨W, i, hηW, hW⟩ := (RationalFunctionsSubmodule.germ_mem_stalkSet_iff _ hη12 _).mp hP
    exact ⟨W, i, hηW, hW⟩
  choose W hWi hηW hWj using hj
  have hηZ : η ∈ (V ⊓ V2) ⊓ ⨅ j, W j := by
    refine ⟨hη12, ?_⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηW
  set Z := (V ⊓ V2) ⊓ ⨅ j, W j with hZdef
  have hZ12 : Z ≤ V ⊓ V2 := inf_le_left
  have hZV : Z ≤ V := hZ12.trans inf_le_left
  have hZ2 : Z ≤ V2 := hZ12.trans inf_le_right
  have hZW : ∀ j, Z ≤ W j := fun j => inf_le_right.trans (iInf_le W j)
  have hmem : (rationalFunctionsPresheaf X).map (homOfLE hZ2).op x0 ∈ L.inv.sections Z := by
    intro W' i l hl
    refine (RationalFunctionsSubmodule.unit X).saturation.mem_of_locally fun y' hy' => ?_
    obtain ⟨V', hV'W, hy'V', a, hsum⟩ := ht W' (i.le.trans hZV) ⟨l, hl⟩ y' hy'
    refine ⟨V', homOfLE hV'W, hy'V', ?_⟩
    let a' : J → Γ(X, V') := fun j => a j
    have hsumv : (rationalFunctionsPresheaf X).map (homOfLE hV'W).op l =
        ∑ j, a' j • (rationalFunctionsPresheaf X).map
          (homOfLE (hV'W.trans (i.le.trans hZV))).op (t j : L.sections V).1 := by
      have hsum2 : L.restrictHom (homOfLE hV'W) ⟨l, hl⟩ = ∑ j, a' j •
          L.restrictHom (homOfLE (hV'W.trans (i.le.trans hZV))) (t j : L.sections V) := hsum
      have := congrArg Subtype.val hsum2
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this
    have hu : (rationalFunctionsPresheaf X).map (homOfLE hV'W).op
        ((rationalFunctionsPresheaf X).map i.op
          ((rationalFunctionsPresheaf X).map (homOfLE hZ2).op x0) * l) ∈
        (RationalFunctionsSubmodule.unit X).sections V' := by
      rw [map_mul, hsumv, Finset.mul_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hj' := (RationalFunctionsSubmodule.unit X).map_mem
        (homOfLE ((hV'W.trans i.le).trans (hZW j))) (hWj j)
      rw [map_mul] at hj'
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ hj'
    intro η' hη' _
    exact ⟨V', hη', _, hu, rfl⟩
  refine ⟨Z, hηZ, _, hmem, ?_⟩
  rw [TopCat.Presheaf.germ_res_apply, hx0]

/-- **FA Def. 16.1.2, the stalks in codimension one.** At a point `η` of codimension `≤ 1` with
`𝓛_η = f 𝒪_{X,η}` and `𝓛'_η = g 𝒪_{X,η}` (`f`, `g` units of `K(X)_η`):
`(𝓛 · 𝓛')_η = fg 𝒪_{X,η}`, `(𝓛⁻¹)_η = f⁻¹ 𝒪_{X,η}` and `sat(𝒪_X)_η = 𝒪_{X,η}`. -/
@[mmp "lem_fa16a_wsh_group"]
theorem WeilDivisorialSubsheaf.stalkSet_mul_inv_unit [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (L L' : WeilDivisorialSubsheaf X) (η : X) (hη : Order.coheight η ≤ 1)
    (f g : ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hf : L.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (f : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a)
    (hg : L'.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (g : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a) :
    (L.mul L').stalkSet η = (Set.range fun a : X.presheaf.stalk η =>
        ((f * g : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a) ∧
      L.inv.stalkSet η = (Set.range fun a : X.presheaf.stalk η =>
        ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a) ∧
      (RationalFunctionsSubmodule.unit X).saturation.stalkSet η =
        Set.range (structureStalkToRationalFunctionsStalk X η).hom := by
  refine ⟨?_, Set.Subset.antisymm (wshA_stalkSet_inv_subset _ η hη f hf)
    (wshA_stalkSet_inv_supset L η hη f hf), ?_⟩
  · show (RationalFunctionsSubmodule.mulImage _ _).saturation.stalkSet η = _
    rw [wshA_stalkSet_saturation _ η hη]
    exact wshA_stalkSet_mulImage _ _ η f g hf hg
  · rw [wshA_stalkSet_saturation _ η hη, wshA_stalkSet_unit]

/-- **FA Def. 16.1.2, uniqueness.** Two saturated submodules of `K(X)` with the same stalks at all
points of codimension `≤ 1` are equal. -/
@[mmp "lem_fa16a_wsh_group"]
theorem RationalFunctionsSubmodule.eq_of_stalkSet_eq {F G : RationalFunctionsSubmodule X}
    (hF : F.IsSaturated) (hG : G.IsSaturated)
    (h : ∀ η : X, Order.coheight η ≤ 1 → F.stalkSet η = G.stalkSet η) : F = G := by
  have hF' : F = F.saturation := hF
  have hG' : G = G.saturation := hG
  have : F.saturation = G.saturation := by
    ext V s
    rw [mem_saturation_iff, mem_saturation_iff]
    exact forall_congr' fun η => forall_congr' fun hη => imp_congr_right fun hc => by
      rw [h η hc]
  rw [hF', hG', this]

omit [Field k] in
private theorem wshB_isSaturated_saturation (F : RationalFunctionsSubmodule X) :
    F.saturation.IsSaturated := by
  apply RationalFunctionsSubmodule.ext
  intro V
  ext s
  constructor
  · intro hs η hη hc
    exact ⟨V, hη, s, hs, rfl⟩
  · intro hs η hη hc
    have := hs η hη hc
    rwa [wshA_stalkSet_saturation F η hc] at this

omit [Field k] in
private theorem wshB_germ_mul {V W : X.Opens} (i : W ⟶ V) {η : X} (hη : η ∈ W)
    (x : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (l : ToType ((rationalFunctionsPresheaf X).obj (op W))) :
    (rationalFunctionsPresheaf X).germ W η hη ((rationalFunctionsPresheaf X).map i.op x * l) =
      (rationalFunctionsPresheaf X).germ V η (i.le hη) x *
        (rationalFunctionsPresheaf X).germ W η hη l := by
  rw [map_mul, TopCat.Presheaf.germ_res_apply]

section WShGroupBuild

variable [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]

omit [Field k] in
private theorem wshB_stalkSet_inv_mul_le (L : WeilDivisorialSubsheaf X) (η : X)
    (hη : Order.coheight η ≤ 1) {V W : X.Opens} (i : W ⟶ V) (hηW : η ∈ W)
    (s : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hs : (rationalFunctionsPresheaf X).germ V η (i.le hηW) s ∈ L.inv.stalkSet η)
    (l : ToType ((rationalFunctionsPresheaf X).obj (op W))) (hl : l ∈ L.sections W) :
    (rationalFunctionsPresheaf X).germ W η hηW ((rationalFunctionsPresheaf X).map i.op s * l) ∈
      (RationalFunctionsSubmodule.unit X).stalkSet η := by
  obtain ⟨f, hf⟩ := L.principal_codim_one η hη
  have h1 := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L η hη f f hf hf).2.1
  rw [h1] at hs
  obtain ⟨a, ha⟩ := hs
  have hlη : (rationalFunctionsPresheaf X).germ W η hηW l ∈ L.stalkSet η := ⟨W, hηW, l, hl, rfl⟩
  rw [hf] at hlη
  obtain ⟨b, hb⟩ := hlη
  rw [wshB_germ_mul i hηW s l, ← ha, ← hb, wshA_stalkSet_unit]
  refine ⟨a * b, ?_⟩
  simp only [map_mul]
  have hu : ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
      (rationalFunctionsPresheaf X).stalk η) * f = 1 := by simp
  calc _ = (((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
      (rationalFunctionsPresheaf X).stalk η) * f) *
      ((structureStalkToRationalFunctionsStalk X η).hom a *
        (structureStalkToRationalFunctionsStalk X η).hom b) := by rw [hu, one_mul]
    _ = _ := by ring

private theorem wshB_isSaturated_inv (L : WeilDivisorialSubsheaf X) : L.inv.IsSaturated := by
  apply RationalFunctionsSubmodule.ext
  intro V
  ext s
  constructor
  · intro hs η hη hc
    exact ⟨V, hη, s, hs, rfl⟩
  · intro hs W i l hl η hηW hc
    exact wshB_stalkSet_inv_mul_le L η hc i hηW s (hs η (i.le hηW) hc) l hl

variable (hmul : ∀ L L' : WeilDivisorialSubsheaf X, SheafOfModules.IsCoherent (L.mul L').toModules)
  (hone : SheafOfModules.IsCoherent (RationalFunctionsSubmodule.unit X).saturation.toModules)
  (hinv : ∀ L : WeilDivisorialSubsheaf X, SheafOfModules.IsCoherent L.inv.toModules)

include hmul in
private def wshB_mulW (L L' : WeilDivisorialSubsheaf X) : WeilDivisorialSubsheaf X where
  toRationalFunctionsSubmodule := L.mul L'
  isCoherent := hmul L L'
  principal_codim_one := fun η hη => by
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    obtain ⟨g, hg⟩ := L'.principal_codim_one η hη
    exact ⟨f * g, (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L' η hη f g hf hg).1⟩
  isSaturated := wshB_isSaturated_saturation _

include hone in
private def wshB_oneW : WeilDivisorialSubsheaf X where
  toRationalFunctionsSubmodule := (RationalFunctionsSubmodule.unit X).saturation
  isCoherent := hone
  principal_codim_one := fun η hη => by
    refine ⟨1, ?_⟩
    rw [wshA_stalkSet_saturation _ η hη, wshA_stalkSet_unit]
    simp
  isSaturated := wshB_isSaturated_saturation _

include hinv in
private def wshB_invW (L : WeilDivisorialSubsheaf X) : WeilDivisorialSubsheaf X where
  toRationalFunctionsSubmodule := L.inv
  isCoherent := hinv L
  principal_codim_one := fun η hη => by
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    exact ⟨f⁻¹, (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L η hη f f hf hf).2.1⟩
  isSaturated := wshB_isSaturated_inv L

omit [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X] in
private theorem wshB_ext {L L' : WeilDivisorialSubsheaf X}
    (h : ∀ η : X, Order.coheight η ≤ 1 → L.stalkSet η = L'.stalkSet η) : L = L' :=
  WeilDivisorialSubsheaf.ext'
    (RationalFunctionsSubmodule.eq_of_stalkSet_eq L.isSaturated L'.isSaturated h)

include hmul hone hinv in
private theorem wshB_exists_group : ∃ G : CommGroup (WeilDivisorialSubsheaf X), IsWShGroup G := by
  have hstalk : ∀ (L L' : WeilDivisorialSubsheaf X) (η : X) (hη : Order.coheight η ≤ 1)
      (f g : ((rationalFunctionsPresheaf X).stalk η)ˣ)
      (hf : L.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        (f : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a)
      (hg : L'.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        (g : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a),
      (wshB_mulW hmul L L').stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        ((f * g : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
          (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a :=
    fun L L' η hη f g hf hg =>
      (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L' η hη f g hf hg).1
  have hone_stalk : ∀ (η : X) (hη : Order.coheight η ≤ 1),
      (wshB_oneW hone : WeilDivisorialSubsheaf X).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        (((1 : ((rationalFunctionsPresheaf X).stalk η)ˣ)) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a := by
    intro η hη
    show (RationalFunctionsSubmodule.unit X).saturation.stalkSet η = _
    rw [wshA_stalkSet_saturation _ η hη, wshA_stalkSet_unit]
    simp
  refine ⟨{ mul := wshB_mulW hmul
            one := wshB_oneW hone
            inv := wshB_invW hinv
            mul_assoc := ?_
            one_mul := ?_
            mul_one := ?_
            inv_mul_cancel := ?_
            mul_comm := ?_ }, ?_, ?_, ?_⟩
  · intro L L' L''
    apply wshB_ext
    intro η hη
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    obtain ⟨g, hg⟩ := L'.principal_codim_one η hη
    obtain ⟨h, hh⟩ := L''.principal_codim_one η hη
    show (wshB_mulW hmul (wshB_mulW hmul L L') L'').stalkSet η =
      (wshB_mulW hmul L (wshB_mulW hmul L' L'')).stalkSet η
    rw [hstalk _ _ η hη (f * g) h (hstalk L L' η hη f g hf hg) hh,
      hstalk _ _ η hη f (g * h) hf (hstalk L' L'' η hη g h hg hh), mul_assoc]
  · intro L
    apply wshB_ext
    intro η hη
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    show (wshB_mulW hmul (wshB_oneW hone) L).stalkSet η = L.stalkSet η
    rw [hstalk _ _ η hη 1 f (hone_stalk η hη) hf, one_mul, hf]
  · intro L
    apply wshB_ext
    intro η hη
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    show (wshB_mulW hmul L (wshB_oneW hone)).stalkSet η = L.stalkSet η
    rw [hstalk _ _ η hη f 1 hf (hone_stalk η hη), mul_one, hf]
  · intro L
    apply wshB_ext
    intro η hη
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    have hi : (wshB_invW hinv L).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a :=
      (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L η hη f f hf hf).2.1
    show (wshB_mulW hmul (wshB_invW hinv L) L).stalkSet η = (wshB_oneW hone).stalkSet η
    rw [hstalk _ _ η hη f⁻¹ f hi hf, hone_stalk η hη, inv_mul_cancel]
  · intro L L'
    apply wshB_ext
    intro η hη
    obtain ⟨f, hf⟩ := L.principal_codim_one η hη
    obtain ⟨g, hg⟩ := L'.principal_codim_one η hη
    show (wshB_mulW hmul L L').stalkSet η = (wshB_mulW hmul L' L).stalkSet η
    rw [hstalk _ _ η hη f g hf hg, hstalk _ _ η hη g f hg hf, mul_comm]
  · exact fun L L' => rfl
  · rfl
  · exact fun L => rfl

end WShGroupBuild

/-- The image `𝓛𝓛' ⊆ K(X)` of two Weil divisorial subsheaves is coherent: on an affine open its
sections are the products `𝓛(U)𝓛'(U)`. -/
private theorem wshB_isCoherent_mulImage [IsReduced X] [IsNoetherian X]
    (L L' : WeilDivisorialSubsheaf X) :
    SheafOfModules.IsCoherent
      (RationalFunctionsSubmodule.mulImage L.toRationalFunctionsSubmodule
        L'.toRationalFunctionsSubmodule).toModules := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have := L.isCoherent
  have := L'.isCoherent
  have : L.toRationalFunctionsSubmodule.toModules.IsFiniteType := L.isCoherent.isFiniteType
  have : L'.toRationalFunctionsSubmodule.toModules.IsFiniteType := L'.isCoherent.isFiniteType
  have : L.toRationalFunctionsSubmodule.toModules.IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  have : L'.toRationalFunctionsSubmodule.toModules.IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  have hqc : (RationalFunctionsSubmodule.mulImage L.toRationalFunctionsSubmodule
      L'.toRationalFunctionsSubmodule).toModules.IsQuasicoherent := by
    refine wshB_isQuasicoherent _ ?_
    intro U hU a t ht
    rw [wshB1_mulImage_sections_eq (hU.basicOpen a)
      (wshB1_hasExt_of_isQuasicoherent _ (hU.basicOpen a))
      (wshB1_hasExt_of_isQuasicoherent _ (hU.basicOpen a))] at ht
    obtain ⟨n, s, hs, he⟩ := wshB1_hasExt_mul (wshB1_hasExt_of_isQuasicoherent _ hU)
      (wshB1_hasExt_of_isQuasicoherent _ hU) a t ht
    exact ⟨n, s, fun x hx => ⟨U, 𝟙 U, hx, hs⟩, he⟩
  refine wshB_isCoherent_of_finite _ ?_
  intro U hU
  have h1 : (L.sections U).FG := Module.Finite.iff_fg.mp
    (Stacks.AlgebraicGeometry.CoherentFinite.finite_sections L.toRationalFunctionsSubmodule.toModules hU)
  have h2 : (L'.sections U).FG := Module.Finite.iff_fg.mp
    (Stacks.AlgebraicGeometry.CoherentFinite.finite_sections L'.toRationalFunctionsSubmodule.toModules hU)
  have h3 : ((RationalFunctionsSubmodule.mulImage L.toRationalFunctionsSubmodule
      L'.toRationalFunctionsSubmodule).sections U).FG := by
    rw [wshB1_mulImage_sections_eq hU (wshB1_hasExt_of_isQuasicoherent _ hU)
      (wshB1_hasExt_of_isQuasicoherent _ hU)]
    exact h1.mul h2
  exact Module.Finite.iff_fg.mpr h3

/-- The inverse `𝓛⁻¹ ⊆ K(X)` of a Weil divisorial subsheaf is coherent when `sat(𝒪_X)` is: on an
affine open `𝓛⁻¹(U)` embeds into `sat(𝒪_X)(U)` by multiplication by a section of `𝓛` nonzero at
every generic point. -/
private theorem wshB_isCoherent_inv [IsReduced X] [IsNoetherian X]
    (hone : SheafOfModules.IsCoherent (RationalFunctionsSubmodule.unit X).saturation.toModules)
    (L : WeilDivisorialSubsheaf X) : SheafOfModules.IsCoherent L.inv.toModules := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have := L.isCoherent
  have : L.toRationalFunctionsSubmodule.toModules.IsFiniteType := L.isCoherent.isFiniteType
  have : L.toRationalFunctionsSubmodule.toModules.IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  have := hone
  have : (RationalFunctionsSubmodule.unit X).saturation.toModules.IsFiniteType :=
    hone.isFiniteType
  have : (RationalFunctionsSubmodule.unit X).saturation.toModules.IsQuasicoherent :=
    _root_.isQuasicoherent_of_isCoherent _
  have hqc : L.inv.toModules.IsQuasicoherent := by
    refine wshB_isQuasicoherent _ ?_
    intro U hU a t ht
    classical
    let x : ToType ((rationalFunctionsPresheaf X).obj (op U)) := fun Z =>
      if h : componentGenericPoint X Z.1 ∈ X.basicOpen a then t ⟨Z.1, h⟩ else 0
    have hxt : (rationalFunctionsPresheaf X).map (homOfLE (X.basicOpen_le a)).op x = t := by
      funext Z
      exact dite_eq_left_of_eq_true (eq_true Z.2)
    obtain ⟨T, hTfin, hTspan⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp
      (Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
        L.toRationalFunctionsSubmodule.toModules hU))
    have hm : ∀ m ∈ T, ∃ n : ℕ,
        a ^ n • (x * m) ∈ (RationalFunctionsSubmodule.unit X).saturation.sections U := by
      intro m hmT
      have hmL : m ∈ L.sections U := hTspan ▸ Submodule.subset_span hmT
      refine wshB1_pow_smul_mem_of_res (wshB1_hasExt_of_isQuasicoherent _ hU) a _ ?_
      rw [map_mul, hxt]
      exact ht _ (𝟙 _) _ (L.map_mem _ hmL)
    choose! n hn using hm
    let N := ∑ m ∈ hTfin.toFinset, n m
    have hN : ∀ m ∈ T,
        a ^ N • (x * m) ∈ (RationalFunctionsSubmodule.unit X).saturation.sections U := by
      intro m hmT
      have hle : n m ≤ N :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hTfin.mem_toFinset.mpr hmT)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
      exact Submodule.smul_mem _ _ (hn m hmT)
    refine ⟨N, a ^ N • x,
      wshB1_mem_inv_of_forall hU (wshB1_hasExt_of_isQuasicoherent _ hU) _ ?_, ?_⟩
    · intro m hm
      rw [← hTspan] at hm
      induction hm using Submodule.span_induction with
      | mem m hmT => rw [smul_mul_assoc]; exact hN m hmT
      | zero => rw [mul_zero]; exact zero_mem _
      | add m₁ m₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
      | smul r m _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
    · rw [rationalFunctionsPresheaf_map_smul, hxt, map_pow]
  refine wshB_isCoherent_of_finite _ ?_
  intro U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨u, hu, hu0⟩ := wshB1_exists_mem_forall_ne_zero L hU
    (wshB1_hasExt_of_isQuasicoherent _ hU)
  have : Module.Finite Γ(X, U) ((RationalFunctionsSubmodule.unit X).saturation.sections U) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
      (RationalFunctionsSubmodule.unit X).saturation.toModules hU
  let φ : L.inv.sections U →ₗ[Γ(X, U)]
      (RationalFunctionsSubmodule.unit X).saturation.sections U :=
    { toFun := fun x => ⟨x.1 * u, x.2 U (𝟙 U) u hu⟩
      map_add' := fun x y => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r x => Subtype.ext (smul_mul_assoc _ _ _) }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext
    funext Z
    have hZ : x.1 Z * u Z = y.1 Z * u Z := congrFun h Z
    obtain ⟨v, hv⟩ := (RationalFunctions.isField_stalk X Z.1).mul_inv_cancel (hu0 Z)
    calc x.1 Z = x.1 Z * u Z * v := by rw [mul_assoc, hv, mul_one]
      _ = y.1 Z * u Z * v := by rw [hZ]
      _ = y.1 Z := by rw [mul_assoc, hv, mul_one]
  have : _root_.IsNoetherian Γ(X, U)
      ((RationalFunctionsSubmodule.unit X).saturation.sections U) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  exact Module.Finite.of_injective φ hφ

/-- **FA Def. 16.1.2, corrected: `WSh(X)` is a group.** Let `X` be a reduced scheme of finite type
over `k`, of pure dimension. Then `WSh(X)`, with the product `𝓛 · 𝓛' = sat(𝓛𝓛')`, is an abelian
group with neutral element `sat(𝒪_X)`, the inverse of `𝓛` being `𝓛⁻¹`. -/
@[mmp "lem_fa16a_wsh_group"]
theorem exists_isWShGroup [IsReduced X] [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) :
    ∃ G : CommGroup (WeilDivisorialSubsheaf X), IsWShGroup G := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  exact wshB_exists_group
    (fun L L' => RationalFunctionsSubmodule.isCoherent_saturation π hd (wshB_isCoherent_mulImage L L'))
    (RationalFunctionsSubmodule.isCoherent_saturation π hd
      RationalFunctionsSubmodule.isCoherent_toModules_unit)
    (fun L => wshB_isCoherent_inv
      (RationalFunctionsSubmodule.isCoherent_saturation π hd
        RationalFunctionsSubmodule.isCoherent_toModules_unit) L)

end Group

/-! ### `𝓗om` of Weil divisorial subsheaves -/

namespace RationalFunctionsSubmodule

variable {X : Scheme.{u}}

/-- A morphism `𝓕|_V ⟶ 𝓖|_V` of `𝒪_V`-modules between submodules of `K(X)`, i.e. a section of
`𝓗om_{𝒪_X}(𝓕, 𝓖)` over `V`: `Γ(X, W)`-linear maps `𝓕(W) → 𝓖(W)` for the opens `W ⊆ V`,
compatible with restriction. -/
structure LocalHom (F G : RationalFunctionsSubmodule X) (V : X.Opens) where
  /-- The map on sections over `W ⊆ V`. -/
  app (W : X.Opens) (hW : W ≤ V) : F.sections W →ₗ[Γ(X, W)] G.sections W
  /-- Compatibility with restriction. -/
  naturality (W W' : X.Opens) (hW : W ≤ V) (i : W' ⟶ W) (s : F.sections W) :
    ((app W' (i.le.trans hW)) (F.restrictHom i s) : ToType ((rationalFunctionsPresheaf X).obj (op W'))) =
      G.restrictHom i (app W hW s)

/-- The section `l ↦ x l` of `𝓗om(𝓕, 𝓖)` over `V` defined by `x ∈ K(X)(V)` with `x 𝓕|_V ⊆ 𝓖|_V`. -/
def mulLocalHom (F G : RationalFunctionsSubmodule X) (V : X.Opens)
    (x : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hx : ∀ (W : X.Opens) (i : W ⟶ V) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      l ∈ F.sections W → (rationalFunctionsPresheaf X).map i.op x * l ∈ G.sections W) :
    LocalHom F G V where
  app W hW :=
    { toFun := fun l => ⟨(rationalFunctionsPresheaf X).map (homOfLE hW).op x * l.1,
        hx W (homOfLE hW) l.1 l.2⟩
      map_add' := by
        intro a b
        exact Subtype.ext (mul_add _ _ _)
      map_smul' := by
        intro r l
        exact Subtype.ext (mul_smul_comm _ _ _) }
  naturality := by
    intro W W' hW i l
    change (rationalFunctionsPresheaf X).map (homOfLE (i.le.trans hW)).op x *
        (rationalFunctionsPresheaf X).map i.op l.1 =
      (rationalFunctionsPresheaf X).map i.op
        ((rationalFunctionsPresheaf X).map (homOfLE hW).op x * l.1)
    rw [map_mul]
    rfl

end RationalFunctionsSubmodule

namespace WeilDivisorialSubsheaf

variable {X : Scheme.{u}} [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]

omit [IsLocallyNoetherian X] [CompactSpace X] in
private lemma wshA_exists_ratio (L : WeilDivisorialSubsheaf X) (Z : irreducibleComponents X)
    (V : X.Opens) (hZ : componentGenericPoint X Z ∈ V)
    (φ : RationalFunctionsSubmodule.LocalHom L.toRationalFunctionsSubmodule
      (RationalFunctionsSubmodule.unit X).saturation V) :
    ∃ c : X.presheaf.stalk (componentGenericPoint X Z),
      ∀ (W : X.Opens) (hzW : componentGenericPoint X Z ∈ W) (hW : W ≤ V)
        (l : ToType ((rationalFunctionsPresheaf X).obj (op W))) (hl : l ∈ L.sections W),
        (φ.app W hW ⟨l, hl⟩).1 ⟨Z, hzW⟩ = c * l ⟨Z, hzW⟩ := by
  obtain ⟨W0, hz0, l0, hl0, hne, hall⟩ := WeilDivisorialSubsheaf.wshA_exists_generator L Z
  let _ := (RationalFunctions.isField_stalk X Z).toField
  have hl1 : (rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op l0 ∈
      L.sections (W0 ⊓ V) := L.map_mem _ hl0
  refine ⟨(φ.app (W0 ⊓ V) inf_le_right ⟨_, hl1⟩).1 ⟨Z, ⟨hz0, hZ⟩⟩ / l0 ⟨Z, hz0⟩, ?_⟩
  intro W hzW hW l hl
  obtain ⟨W1, i1, i0, hz1, a, ha⟩ := hall W hzW l hl
  have hW1 : W1 ≤ V := i1.le.trans hW
  have n1 := φ.naturality W W1 hW i1 ⟨l, hl⟩
  have n2 := φ.naturality (W0 ⊓ V) W1 inf_le_right (homOfLE (le_inf i0.le hW1)) ⟨_, hl1⟩
  have e1 : (L.restrictHom i1 ⟨l, hl⟩ : ToType ((rationalFunctionsPresheaf X).obj (op W1))) =
      a • (L.restrictHom (homOfLE (le_inf i0.le hW1)) ⟨_, hl1⟩ :
        ToType ((rationalFunctionsPresheaf X).obj (op W1))) := ha
  have e2 : L.restrictHom i1 ⟨l, hl⟩ =
      a • L.restrictHom (homOfLE (le_inf i0.le hW1)) ⟨_, hl1⟩ := Subtype.ext e1
  rw [e2, map_smul] at n1
  set P := (φ.app (W0 ⊓ V) inf_le_right ⟨_, hl1⟩).1 with hP
  have h1 := congrFun n1 ⟨Z, hz1⟩
  have h2 := congrFun n2 ⟨Z, hz1⟩
  have h3 := congrFun ha ⟨Z, hz1⟩
  have h1' : X.presheaf.germ W1 _ hz1 a * (φ.app W1 hW1 (L.restrictHom
      (homOfLE (le_inf i0.le hW1)) ⟨_, hl1⟩)).1 ⟨Z, hz1⟩ =
      (φ.app W hW ⟨l, hl⟩).1 ⟨Z, hzW⟩ := h1
  have h2' : (φ.app W1 hW1 (L.restrictHom
      (homOfLE (le_inf i0.le hW1)) ⟨_, hl1⟩)).1 ⟨Z, hz1⟩ = P ⟨Z, ⟨i0.le hz1, hW1 hz1⟩⟩ := h2
  have h3' : l ⟨Z, i1.le hz1⟩ = X.presheaf.germ W1 _ hz1 a * l0 ⟨Z, i0.le hz1⟩ := h3
  rw [← h1', h2']
  have h4 : (P ⟨Z, ⟨i0.le hz1, hW1 hz1⟩⟩ / l0 ⟨Z, hz0⟩) * l ⟨Z, hzW⟩ =
      X.presheaf.germ W1 _ hz1 a * P ⟨Z, ⟨i0.le hz1, hW1 hz1⟩⟩ := by
    rw [show l ⟨Z, hzW⟩ = l ⟨Z, i1.le hz1⟩ from rfl, h3']
    field_simp
  exact h4.symm

omit [IsLocallyNoetherian X] [CompactSpace X] in
/-- **FA Def. 16.1.2, `𝓛^* = 𝓗om(𝓛, 𝒪_X) = 𝓛⁻¹`, general form.** For a Weil divisorial subsheaf
`𝓛`, `x ↦ (l ↦ xl)` is an isomorphism `𝓛⁻¹ ≅ 𝓗om_{𝒪_X}(𝓛, sat(𝒪_X))`: on every open `V` it is a
bijection from `𝓛⁻¹(V)` onto the morphisms `𝓛|_V → sat(𝒪_X)|_V`. -/
@[mmp "lem_fa16a_inverse_iso_hom_sat"]
theorem bijective_mulLocalHom_inv (L : WeilDivisorialSubsheaf X) (V : X.Opens) :
    Function.Bijective fun x : L.inv.sections V =>
      RationalFunctionsSubmodule.mulLocalHom L.toRationalFunctionsSubmodule
        (RationalFunctionsSubmodule.unit X).saturation V x.1 x.2 := by
  constructor
  · intro x y hxy
    refine Subtype.ext (funext fun ⟨Z, hZ⟩ => ?_)
    obtain ⟨W0, hz0, l0, hl0, hne, -⟩ := WeilDivisorialSubsheaf.wshA_exists_generator L Z
    let _ := (RationalFunctions.isField_stalk X Z).toField
    have hl1 : (rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op l0 ∈
        L.sections (W0 ⊓ V) := L.map_mem _ hl0
    have h := congrArg (fun ψ => (ψ.app (W0 ⊓ V) inf_le_right ⟨_, hl1⟩).1 ⟨Z, ⟨hz0, hZ⟩⟩) hxy
    have h' : x.1 ⟨Z, hZ⟩ * l0 ⟨Z, hz0⟩ = y.1 ⟨Z, hZ⟩ * l0 ⟨Z, hz0⟩ := h
    obtain ⟨u, hu⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel hne
    calc x.1 ⟨Z, hZ⟩ = x.1 ⟨Z, hZ⟩ * (l0 ⟨Z, hz0⟩ * u) := by rw [hu, mul_one]
      _ = (x.1 ⟨Z, hZ⟩ * l0 ⟨Z, hz0⟩) * u := by rw [mul_assoc]
      _ = (y.1 ⟨Z, hZ⟩ * l0 ⟨Z, hz0⟩) * u := by rw [h']
      _ = y.1 ⟨Z, hZ⟩ := by rw [mul_assoc, hu, mul_one]
  · intro φ
    have hc : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V},
        ∃ c : X.presheaf.stalk (componentGenericPoint X Z.1),
        ∀ (W : X.Opens) (hzW : componentGenericPoint X Z.1 ∈ W) (hW : W ≤ V)
          (l : ToType ((rationalFunctionsPresheaf X).obj (op W))) (hl : l ∈ L.sections W),
          (φ.app W hW ⟨l, hl⟩).1 ⟨Z.1, hzW⟩ = c * l ⟨Z.1, hzW⟩ :=
      fun Z => wshA_exists_ratio L Z.1 V Z.2 φ
    choose x hx using hc
    have hxe : ∀ (W : X.Opens) (hW : W ≤ V) (l : ToType ((rationalFunctionsPresheaf X).obj (op W)))
        (hl : l ∈ L.sections W),
        (rationalFunctionsPresheaf X).map (homOfLE hW).op x * l = (φ.app W hW ⟨l, hl⟩).1 := by
      intro W hW l hl
      funext ⟨Z, hzW⟩
      exact (hx ⟨Z, hW hzW⟩ W hzW hW l hl).symm
    have hmem : (x : ToType ((rationalFunctionsPresheaf X).obj (op V))) ∈ L.inv.sections V := by
      intro W i l hl
      have key : (rationalFunctionsPresheaf X).map i.op
          (x : ToType ((rationalFunctionsPresheaf X).obj (op V))) * l =
          (φ.app W i.le ⟨l, hl⟩).1 := hxe W i.le l hl
      rw [key]
      exact (φ.app W i.le ⟨l, hl⟩).2
    refine ⟨⟨x, hmem⟩, ?_⟩
    have hext : ∀ ψ₁ ψ₂ : RationalFunctionsSubmodule.LocalHom L.toRationalFunctionsSubmodule
        (RationalFunctionsSubmodule.unit X).saturation V,
        (∀ W hW l, (ψ₁.app W hW l).1 = (ψ₂.app W hW l).1) → ψ₁ = ψ₂ := by
      rintro ⟨a1, n1⟩ ⟨a2, n2⟩ h
      have : a1 = a2 := by
        funext W hW
        refine LinearMap.ext fun l => Subtype.ext ?_
        exact h W hW l
      subst this
      rfl
    refine hext _ _ fun W hW l => ?_
    exact hxe W hW l.1 l.2

omit [IsLocallyNoetherian X] [CompactSpace X] [IsReduced X] in
/-- The stalk formula `(𝓛⁻¹ · 𝓜)_η = f⁻¹ g 𝒪_{X,η}` in codimension `≤ 1`. -/
private theorem wshB2_stalkSet_inv_mul {k : Type u} [Field k] [IsReduced X]
    [IsLocallyNoetherian X] [CompactSpace X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (L M : WeilDivisorialSubsheaf X) (η : X) (hc : Order.coheight η ≤ 1)
    (f g : ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hf : L.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (f : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a)
    (hg : M.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      (g : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a) :
    (L.inv.mul M.toRationalFunctionsSubmodule).stalkSet η =
      Set.range fun a : X.presheaf.stalk η =>
        ((f⁻¹ * g : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
          (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a := by
  have : IsNoetherian X := {}
  obtain ⟨G, hG⟩ := exists_isWShGroup π hd
  have h2 : (G.inv L).toRationalFunctionsSubmodule = L.inv := hG.inv_eq L
  have hinv : (G.inv L).stalkSet η = Set.range fun a : X.presheaf.stalk η =>
        ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a := by
    have : (G.inv L).stalkSet η = L.inv.stalkSet η := by
      show (G.inv L).toRationalFunctionsSubmodule.stalkSet η = _
      rw [h2]
    rw [this]
    exact (stalkSet_mul_inv_unit L M η hc f g hf hg).2.1
  have : ((G.inv L).mul M).stalkSet η = (L.inv.mul M.toRationalFunctionsSubmodule).stalkSet η := by
    show ((G.inv L).toRationalFunctionsSubmodule.mul M.toRationalFunctionsSubmodule).stalkSet η = _
    rw [h2]
  rw [← this]
  exact (stalkSet_mul_inv_unit (G.inv L) M η hc f⁻¹ g hinv hg).1

/-- Multiplication by an element of `𝓛⁻¹ · 𝓜` maps `𝓛` into `𝓜`. -/
private theorem wshB_mul_inv_mem {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (L M : WeilDivisorialSubsheaf X) (V : X.Opens) :
    ∀ x ∈ (L.inv.mul M.toRationalFunctionsSubmodule).sections V,
        ∀ (W : X.Opens) (i : W ⟶ V) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
          l ∈ L.sections W → (rationalFunctionsPresheaf X).map i.op x * l ∈ M.sections W := by
  intro x hx W i l hl
  have hMs : M.toRationalFunctionsSubmodule = M.toRationalFunctionsSubmodule.saturation :=
    M.isSaturated
  rw [hMs]
  intro η hηW hc
  obtain ⟨f, hf⟩ := L.principal_codim_one η hc
  obtain ⟨g, hg⟩ := M.principal_codim_one η hc
  have hmul' := wshB2_stalkSet_inv_mul π hd L M η hc f g hf hg
  have hxη : (rationalFunctionsPresheaf X).germ V η (i.le hηW) x ∈
      (L.inv.mul M.toRationalFunctionsSubmodule).stalkSet η :=
    ⟨V, i.le hηW, x, hx, rfl⟩
  rw [hmul'] at hxη
  obtain ⟨a, ha⟩ := hxη
  have hlη : (rationalFunctionsPresheaf X).germ W η hηW l ∈ L.stalkSet η :=
    ⟨W, hηW, l, hl, rfl⟩
  rw [hf] at hlη
  obtain ⟨b, hb⟩ := hlη
  rw [wshB_germ_mul i hηW x l, ← ha, ← hb]
  have : (M.toRationalFunctionsSubmodule).stalkSet η = _ := hg
  rw [this]
  refine ⟨a * b, ?_⟩
  simp only [map_mul, Units.val_mul]
  have hu : ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
      (rationalFunctionsPresheaf X).stalk η) * f = 1 := by simp
  calc _ = (g : (rationalFunctionsPresheaf X).stalk η) * (((f⁻¹ : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
      (rationalFunctionsPresheaf X).stalk η) * f) *
      ((structureStalkToRationalFunctionsStalk X η).hom a *
        (structureStalkToRationalFunctionsStalk X η).hom b) := by rw [hu, mul_one]
    _ = _ := by ring

omit [IsLocallyNoetherian X] [CompactSpace X] [IsReduced X] in
/-- The generic point of an irreducible component lies on no other irreducible component. -/
private theorem wshB2_componentGenericPoint_mem {Z Z' : irreducibleComponents X}
    (h : componentGenericPoint X Z ∈ Z'.1) : Z = Z' := by
  have hg := isGenericPoint_componentGenericPoint X Z
  have hsub : Z.1 ⊆ Z'.1 := by
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr h)
      (isClosed_of_mem_irreducibleComponents _ Z'.2)
  exact Subtype.ext ((Z.2.2 Z'.2.1 hsub).antisymm hsub).symm

private theorem wshB2_exists_isolating (Z : irreducibleComponents X) :
    ∃ U : X.Opens, componentGenericPoint X Z ∈ U ∧
      ∀ Z' : irreducibleComponents X, componentGenericPoint X Z' ∈ U → Z' = Z := by
  have : IsNoetherian X := {}
  have : Finite (irreducibleComponents X) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  have hcl : IsClosed (⋃ Z' : {Z' : irreducibleComponents X // Z' ≠ Z}, Z'.1.1) :=
    isClosed_iUnion_of_finite fun Z' => isClosed_of_mem_irreducibleComponents _ Z'.1.2
  refine ⟨⟨_, hcl.isOpen_compl⟩, ?_, ?_⟩
  · intro hmem
    obtain ⟨Z', hZ'⟩ := Set.mem_iUnion.mp hmem
    exact Z'.2 (wshB2_componentGenericPoint_mem hZ').symm
  · intro Z' hZ'
    by_contra hne
    exact hZ' (Set.mem_iUnion.mpr ⟨⟨Z', hne⟩, (isGenericPoint_componentGenericPoint X Z').mem⟩)

private theorem wshB2_exists_section_ne_zero (L : WeilDivisorialSubsheaf X)
    (Z : irreducibleComponents X) (N : X.Opens) (hN : componentGenericPoint X Z ∈ N) :
    ∃ (W : X.Opens) (_ : W ≤ N) (hZ : componentGenericPoint X Z ∈ W)
      (l : ToType ((rationalFunctionsPresheaf X).obj (op W))), l ∈ L.sections W ∧ l ⟨Z, hZ⟩ ≠ 0 := by
  have hc : Order.coheight (componentGenericPoint X Z) ≤ 1 := by
    rw [wshB1_coheight_componentGenericPoint]
    exact zero_le_one
  obtain ⟨f, hf⟩ := L.principal_codim_one _ hc
  have hfm : (f : (rationalFunctionsPresheaf X).stalk _) ∈ L.stalkSet (componentGenericPoint X Z) := by
    rw [hf]; exact ⟨1, by simp⟩
  obtain ⟨W₁, h₁, s, hs, hsf⟩ := hfm
  obtain ⟨W₂, h₂, t, ht⟩ := TopCat.Presheaf.exists_germ_eq (rationalFunctionsPresheaf X)
    ((f⁻¹ : ((rationalFunctionsPresheaf X).stalk (componentGenericPoint X Z))ˣ) :
      (rationalFunctionsPresheaf X).stalk (componentGenericPoint X Z))
  have h12 : componentGenericPoint X Z ∈ W₁ ⊓ W₂ := ⟨h₁, h₂⟩
  have hg : (rationalFunctionsPresheaf X).germ (W₁ ⊓ W₂) _ h12
      ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op s *
        (rationalFunctionsPresheaf X).map (homOfLE inf_le_right).op t) =
      (rationalFunctionsPresheaf X).germ (W₁ ⊓ W₂) _ h12 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hsf, ht, map_one]
    simp
  obtain ⟨W₃, h₃, iU, iV, he⟩ := TopCat.Presheaf.germ_eq _ _ h12 h12 _ _ hg
  have hZ := congrFun he ⟨Z, h₃⟩
  change s ⟨Z, h₁⟩ * t ⟨Z, h₂⟩ = 1 at hZ
  refine ⟨W₁ ⊓ N, inf_le_right, ⟨h₁, hN⟩,
    (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op s, L.map_mem _ hs, ?_⟩
  change s ⟨Z, h₁⟩ ≠ 0
  intro h0
  rw [h0, zero_mul] at hZ
  exact zero_ne_one hZ

private theorem wshB2_localHom_cross (L M : WeilDivisorialSubsheaf X) {V : X.Opens}
    (φ : RationalFunctionsSubmodule.LocalHom L.toRationalFunctionsSubmodule
      M.toRationalFunctionsSubmodule V)
    (Z : irreducibleComponents X) {U : X.Opens} (hU : U ≤ V) (hZ : componentGenericPoint X Z ∈ U)
    (hiso : ∀ Z' : irreducibleComponents X, componentGenericPoint X Z' ∈ U → Z' = Z)
    (l l' : ToType ((rationalFunctionsPresheaf X).obj (op U))) (hl : l ∈ L.sections U)
    (hl' : l' ∈ L.sections U) :
    (φ.app U hU ⟨l, hl⟩).1 ⟨Z, hZ⟩ * l' ⟨Z, hZ⟩ = (φ.app U hU ⟨l', hl'⟩).1 ⟨Z, hZ⟩ * l ⟨Z, hZ⟩ := by
  -- sections over `U` are determined by their `Z`-component
  have hext : ∀ {U' : X.Opens} (_ : U' ≤ U) (hZ' : componentGenericPoint X Z ∈ U')
      (a b : ToType ((rationalFunctionsPresheaf X).obj (op U'))), a ⟨Z, hZ'⟩ = b ⟨Z, hZ'⟩ → a = b := by
    intro U' hU' hZ' a b hab
    funext ⟨Z', hZ''⟩
    obtain rfl := hiso Z' (hU' hZ'')
    exact hab
  by_cases h0 : l ⟨Z, hZ⟩ = 0
  · have hl0 : (⟨l, hl⟩ : L.sections U) = 0 :=
      Subtype.ext (hext le_rfl hZ l 0 (by rw [h0]; rfl))
    rw [hl0, map_zero, h0, mul_zero]
    exact zero_mul _
  obtain ⟨b, hb⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel h0
  obtain ⟨W₀, hW₀, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (l' ⟨Z, hZ⟩ * b)
  let j : W₀ ⊓ U ⟶ U := homOfLE inf_le_right
  have hZ₀ : componentGenericPoint X Z ∈ W₀ ⊓ U := ⟨hW₀, hZ⟩
  let a' : Γ(X, W₀ ⊓ U) := X.presheaf.map (homOfLE inf_le_left).op a
  have ha' : X.presheaf.germ (W₀ ⊓ U) _ hZ₀ a' = l' ⟨Z, hZ⟩ * b := by
    rw [TopCat.Presheaf.germ_res_apply, ha]
  have hres : L.restrictHom j ⟨l', hl'⟩ = a' • L.restrictHom j ⟨l, hl⟩ := by
    apply Subtype.ext
    apply hext inf_le_right hZ₀
    change l' ⟨Z, hZ⟩ = X.presheaf.germ (W₀ ⊓ U) _ hZ₀ a' * l ⟨Z, hZ⟩
    rw [ha', mul_assoc, mul_comm b, hb, mul_one]
  have n1 := congrFun (φ.naturality U (W₀ ⊓ U) hU j ⟨l', hl'⟩) ⟨Z, hZ₀⟩
  have n2 := congrFun (φ.naturality U (W₀ ⊓ U) hU j ⟨l, hl⟩) ⟨Z, hZ₀⟩
  rw [hres, map_smul] at n1
  change X.presheaf.germ (W₀ ⊓ U) _ hZ₀ a' *
      (φ.app (W₀ ⊓ U) (j.le.trans hU) (L.restrictHom j ⟨l, hl⟩)).1 ⟨Z, hZ₀⟩ =
    (φ.app U hU ⟨l', hl'⟩).1 ⟨Z, hZ⟩ at n1
  change (φ.app (W₀ ⊓ U) (j.le.trans hU) (L.restrictHom j ⟨l, hl⟩)).1 ⟨Z, hZ₀⟩ =
    (φ.app U hU ⟨l, hl⟩).1 ⟨Z, hZ⟩ at n2
  rw [n2, ha'] at n1
  rw [← n1]
  linear_combination (-((φ.app U hU ⟨l, hl⟩).1 ⟨Z, hZ⟩ * l' ⟨Z, hZ⟩)) * hb

/-- **FA proof of 16.4, `𝓗om` of Weil divisorial sheaves.** Let `X` be a reduced scheme of finite
type over `k`, of pure dimension, and `𝓛, 𝓜 ∈ WSh(X)`. Then `x ↦ (l ↦ xl)` is an isomorphism
`𝓛⁻¹ · 𝓜 ≅ 𝓗om_{𝒪_X}(𝓛, 𝓜)`: on every open `V` every `x ∈ (𝓛⁻¹ · 𝓜)(V)` satisfies `x 𝓛|_V ⊆ 𝓜|_V`,
and `x ↦ (l ↦ xl)` is a bijection from `(𝓛⁻¹ · 𝓜)(V)` onto the morphisms `𝓛|_V → 𝓜|_V`. -/
@[mmp "lem_fa16a_hom_wsh_product"]
theorem bijective_mulLocalHom {k : Type u} [Field k] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (L M : WeilDivisorialSubsheaf X) (V : X.Opens) :
    ∃ hmul : ∀ x ∈ (L.inv.mul M.toRationalFunctionsSubmodule).sections V,
        ∀ (W : X.Opens) (i : W ⟶ V) (l : ToType ((rationalFunctionsPresheaf X).obj (op W))),
          l ∈ L.sections W → (rationalFunctionsPresheaf X).map i.op x * l ∈ M.sections W,
      Function.Bijective fun x : (L.inv.mul M.toRationalFunctionsSubmodule).sections V =>
        RationalFunctionsSubmodule.mulLocalHom L.toRationalFunctionsSubmodule
          M.toRationalFunctionsSubmodule V x.1 (hmul x.1 x.2) := by
  refine ⟨wshB_mul_inv_mem π hd L M V, ?_⟩
  constructor
  · -- injectivity: compare components at a generic point against a nonvanishing local section
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    apply Subtype.ext
    funext ⟨Z, hZV⟩
    obtain ⟨W, hWV, hZ, l, hl, hne⟩ := wshB2_exists_section_ne_zero L Z V hZV
    have h := congrArg (fun φ : RationalFunctionsSubmodule.LocalHom L.toRationalFunctionsSubmodule
      M.toRationalFunctionsSubmodule V => (φ.app W hWV ⟨l, hl⟩).1 ⟨Z, hZ⟩) hxy
    change x ⟨Z, hZV⟩ * l ⟨Z, hZ⟩ = y ⟨Z, hZV⟩ * l ⟨Z, hZ⟩ at h
    obtain ⟨b, hb⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel hne
    linear_combination b * h - (x ⟨Z, hZV⟩ - y ⟨Z, hZV⟩) * hb
  · -- surjectivity: `x_Z = φ(l_Z)_Z / (l_Z)_Z` for a nonvanishing local section `l_Z`
    intro φ
    have hsec : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V},
        ∃ (W : X.Opens) (_ : W ≤ V) (hZ : componentGenericPoint X Z.1 ∈ W)
          (_ : ∀ Z' : irreducibleComponents X, componentGenericPoint X Z' ∈ W → Z' = Z.1)
          (l : ToType ((rationalFunctionsPresheaf X).obj (op W))) (hl : l ∈ L.sections W)
          (b : X.presheaf.stalk (componentGenericPoint X Z.1)), l ⟨Z.1, hZ⟩ * b = 1 := by
      intro Z
      obtain ⟨I, hI, hiso⟩ := wshB2_exists_isolating Z.1
      obtain ⟨W, hWN, hZ, l, hl, hne⟩ := wshB2_exists_section_ne_zero L Z.1 (V ⊓ I) ⟨Z.2, hI⟩
      obtain ⟨b, hb⟩ := (RationalFunctions.isField_stalk X Z.1).mul_inv_cancel hne
      exact ⟨W, hWN.trans inf_le_left, hZ, fun Z' hZ' => hiso Z' (hWN hZ').2,
        l, hl, b, hb⟩
    choose W hWV hZW hiso l hl b hb using hsec
    let x : ToType ((rationalFunctionsPresheaf X).obj (op V)) := fun Z =>
      (φ.app (W Z) (hWV Z) ⟨l Z, hl Z⟩).1 ⟨Z.1, hZW Z⟩ * b Z
    have key : ∀ (W' : X.Opens) (hW' : W' ≤ V) (l' : ToType ((rationalFunctionsPresheaf X).obj
        (op W'))) (hl' : l' ∈ L.sections W'),
        (φ.app W' hW' ⟨l', hl'⟩).1 = (rationalFunctionsPresheaf X).map (homOfLE hW').op x * l' := by
      intro W' hW' l' hl'
      funext ⟨Z, hZ⟩
      let Zv : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ V} := ⟨Z, hW' hZ⟩
      let U := W' ⊓ W Zv
      have hZU : componentGenericPoint X Z ∈ U := ⟨hZ, hZW Zv⟩
      have hUV : U ≤ V := inf_le_left.trans hW'
      let i₁ : U ⟶ W' := homOfLE inf_le_left
      let i₂ : U ⟶ W Zv := homOfLE inf_le_right
      have hc := wshB2_localHom_cross L M φ Z hUV hZU
        (fun Z' hZ' => hiso Zv Z' (inf_le_right (b := W Zv) hZ'))
        _ _ (L.map_mem i₁ hl') (L.map_mem i₂ (hl Zv))
      have n1 := congrFun (φ.naturality W' U hW' i₁ ⟨l', hl'⟩) ⟨Z, hZU⟩
      have n2 := congrFun (φ.naturality (W Zv) U (hWV Zv) i₂ ⟨l Zv, hl Zv⟩) ⟨Z, hZU⟩
      change (φ.app U _ (L.restrictHom i₁ ⟨l', hl'⟩)).1 ⟨Z, hZU⟩ =
        (φ.app W' hW' ⟨l', hl'⟩).1 ⟨Z, hZ⟩ at n1
      change (φ.app U _ (L.restrictHom i₂ ⟨l Zv, hl Zv⟩)).1 ⟨Z, hZU⟩ =
        (φ.app (W Zv) (hWV Zv) ⟨l Zv, hl Zv⟩).1 ⟨Z, hZW Zv⟩ at n2
      change (φ.app U hUV (L.restrictHom i₁ ⟨l', hl'⟩)).1 ⟨Z, hZU⟩ * l Zv ⟨Z, hZW Zv⟩ =
        (φ.app U hUV (L.restrictHom i₂ ⟨l Zv, hl Zv⟩)).1 ⟨Z, hZU⟩ * l' ⟨Z, hZ⟩ at hc
      rw [n1, n2] at hc
      change (φ.app W' hW' ⟨l', hl'⟩).1 ⟨Z, hZ⟩ =
        (φ.app (W Zv) (hWV Zv) ⟨l Zv, hl Zv⟩).1 ⟨Z, hZW Zv⟩ * b Zv * l' ⟨Z, hZ⟩
      linear_combination b Zv * hc - (φ.app W' hW' ⟨l', hl'⟩).1 ⟨Z, hZ⟩ * hb Zv
    have hxmem : x ∈ (L.inv.mul M.toRationalFunctionsSubmodule).sections V := by
      intro η hη hc
      rw [← wshA_stalkSet_saturation _ η hc]
      change (rationalFunctionsPresheaf X).germ V η hη x ∈
        (L.inv.mul M.toRationalFunctionsSubmodule).stalkSet η
      obtain ⟨f, hf⟩ := L.principal_codim_one η hc
      obtain ⟨g, hg⟩ := M.principal_codim_one η hc
      rw [wshB2_stalkSet_inv_mul π hd L M η hc f g hf hg]
      have hfm : (f : (rationalFunctionsPresheaf X).stalk η) ∈ L.stalkSet η := by
        rw [hf]; exact ⟨1, by simp⟩
      obtain ⟨W₁, h₁, s, hs, hsf⟩ := hfm
      let i : W₁ ⊓ V ⟶ W₁ := homOfLE inf_le_left
      have hηW : η ∈ W₁ ⊓ V := ⟨h₁, hη⟩
      have hs' := L.map_mem i hs
      have hk := key (W₁ ⊓ V) inf_le_right _ hs'
      have hm : (rationalFunctionsPresheaf X).germ (W₁ ⊓ V) η hηW
          (φ.app (W₁ ⊓ V) inf_le_right ⟨_, hs'⟩).1 ∈ M.stalkSet η :=
        ⟨_, hηW, _, (φ.app (W₁ ⊓ V) inf_le_right ⟨_, hs'⟩).2, rfl⟩
      rw [hk, wshB_germ_mul, TopCat.Presheaf.germ_res_apply, hsf, hg] at hm
      obtain ⟨a, ha⟩ := hm
      simp only at ha
      refine ⟨a, ?_⟩
      change ((f⁻¹ * g : ((rationalFunctionsPresheaf X).stalk η)ˣ) :
        (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a =
        (rationalFunctionsPresheaf X).germ V η hη x
      rw [Units.val_mul, mul_assoc, ha, mul_comm, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨⟨x, hxmem⟩, ?_⟩
    obtain ⟨app, nat⟩ := φ
    simp only [RationalFunctionsSubmodule.mulLocalHom]
    congr 1
    funext W' hW'
    apply LinearMap.ext
    rintro ⟨l', hl'⟩
    apply Subtype.ext
    exact (key W' hW' l' hl').symm

end WeilDivisorialSubsheaf

/-! ### The product of a locally free and a Weil divisorial subsheaf -/

section Tensor

variable {X : Scheme.{u}}

/-- The sheaves of modules on a scheme with the sheafified tensor product of [Stacks, Tag 01CA]. -/
local instance modulesMonoidalWSh (Y : Scheme.{u}) : MonoidalCategory Y.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal Y.toRingedSpace

/-- Two sections of `𝓕 ⊆ K(X)` with the same germ in `K(X)` have the same germ in `𝓕`. -/
private lemma wshA2_germ_eq_of_germ_eq (F : RationalFunctionsSubmodule X) {U : X.Opens} {η : X}
    (hη : η ∈ U) (s t : F.sections U)
    (h : (rationalFunctionsPresheaf X).germ U η hη s.1 =
      (rationalFunctionsPresheaf X).germ U η hη t.1) :
    TopCat.Presheaf.germ F.toModules.val.presheaf U η hη s =
      TopCat.Presheaf.germ F.toModules.val.presheaf U η hη t := by
  obtain ⟨W, hηW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq _ η hη hη s.1 t.1 h
  refine TopCat.Presheaf.germ_ext _ W hηW iU iU ?_
  have hi : iV = iU := Subsingleton.elim _ _
  subst hi
  exact Subtype.ext e

/-- At a point of codimension `≤ 1` the stalk of a Weil divisorial subsheaf has rank at most one:
a basis of it has at most one element. -/
private lemma wshA2_subsingleton_of_basis (L : WeilDivisorialSubsheaf X) (η : X)
    (hη : Order.coheight η ≤ 1) {I : Type u}
    (b : Module.Basis I (ToType (X.presheaf.stalk η))
      (ToType (TopCat.Presheaf.stalk L.toRationalFunctionsSubmodule.toModules.val.presheaf η))) :
    Subsingleton I := by
  obtain ⟨u, hu⟩ := L.principal_codim_one η hη
  -- any two germs are dependent, with a nonzero coefficient on the second when the first is not 0
  have hdep : ∀ m₁ m₂ : ToType (TopCat.Presheaf.stalk
      L.toRationalFunctionsSubmodule.toModules.val.presheaf η),
      ∃ a₁ a₂ : X.presheaf.stalk η, a₂ • m₁ = a₁ • m₂ ∧ (a₁ = 0 → m₁ = 0) := by
    intro m₁ m₂
    obtain ⟨V₁, hη₁, s₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      L.toRationalFunctionsSubmodule.toModules.val.presheaf m₁
    obtain ⟨V, hVV₁, hηV, s₂, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
      L.toRationalFunctionsSubmodule.toModules.val.presheaf m₂ hη₁
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVV₁) η hηV s₁]
    generalize L.toRationalFunctionsSubmodule.toModules.val.presheaf.map (homOfLE hVV₁).op s₁ = t₁
    have hk : ∀ t : L.sections V, ∃ a : X.presheaf.stalk η,
        (u : (rationalFunctionsPresheaf X).stalk η) *
          (structureStalkToRationalFunctionsStalk X η).hom a =
        (rationalFunctionsPresheaf X).germ V η hηV t.1 := by
      intro t
      have hmem : (rationalFunctionsPresheaf X).germ V η hηV t.1 ∈ L.stalkSet η :=
        ⟨V, hηV, t.1, t.2, rfl⟩
      rw [hu] at hmem
      exact hmem
    obtain ⟨a₁, ha₁⟩ := hk t₁
    obtain ⟨a₂, ha₂⟩ := hk s₂
    refine ⟨a₁, a₂, ?_, ?_⟩
    · obtain ⟨U₁, hU₁V, hηU₁, r₁, hr₁⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a₁ hηV
      obtain ⟨U, hUU₁, hηU, r₂, hr₂⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a₂ hηU₁
      have hρ₁ : X.presheaf.germ U η hηU (X.presheaf.map (homOfLE hUU₁).op r₁) = a₁ :=
        (TopCat.Presheaf.germ_res_apply _ _ η hηU r₁).trans hr₁
      let iUV : U ⟶ V := homOfLE (hUU₁.trans hU₁V)
      have g₁ := TopCat.Presheaf.germ_res_apply
        L.toRationalFunctionsSubmodule.toModules.val.presheaf iUV η hηU t₁
      have g₂ := TopCat.Presheaf.germ_res_apply
        L.toRationalFunctionsSubmodule.toModules.val.presheaf iUV η hηU s₂
      rw [← g₁, ← g₂, ← hρ₁, ← hr₂]
      refine (PresheafOfModules.germ_smul (R := X.presheaf)
        L.toRationalFunctionsSubmodule.toModules.val η U hηU r₂ _).symm.trans
        (Eq.trans ?_ (PresheafOfModules.germ_smul (R := X.presheaf)
          L.toRationalFunctionsSubmodule.toModules.val η U hηU _ _))
      refine wshA2_germ_eq_of_germ_eq L.toRationalFunctionsSubmodule hηU _ _ ?_
      change (rationalFunctionsPresheaf X).germ U η hηU
          (r₂ • (rationalFunctionsPresheaf X).map iUV.op t₁.1) =
        (rationalFunctionsPresheaf X).germ U η hηU
          (X.presheaf.map (homOfLE hUU₁).op r₁ • (rationalFunctionsPresheaf X).map iUV.op s₂.1)
      have k₁ : (rationalFunctionsPresheaf X).germ U η hηU
          ((rationalFunctionsPresheaf X).map iUV.op t₁.1) =
          (rationalFunctionsPresheaf X).germ V η hηV t₁.1 :=
        TopCat.Presheaf.germ_res_apply _ iUV η hηU _
      have k₂ : (rationalFunctionsPresheaf X).germ U η hηU
          ((rationalFunctionsPresheaf X).map iUV.op s₂.1) =
          (rationalFunctionsPresheaf X).germ V η hηV s₂.1 :=
        TopCat.Presheaf.germ_res_apply _ iUV η hηU _
      rw [wshA_germ_smul, wshA_germ_smul, k₁, k₂, hρ₁, hr₂, ← ha₁, ← ha₂]
      ring
    · intro h0
      rw [← map_zero (TopCat.Presheaf.germ
        L.toRationalFunctionsSubmodule.toModules.val.presheaf V η hηV).hom]
      refine wshA2_germ_eq_of_germ_eq L.toRationalFunctionsSubmodule hηV t₁ 0 ?_
      rw [← ha₁, h0, map_zero, mul_zero]
      exact (map_zero _).symm
  refine ⟨fun i j => ?_⟩
  by_contra hij
  obtain ⟨a₁, a₂, h, h0⟩ := hdep (b i) (b j)
  have hr := congrArg (fun m => b.repr m j) h
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, mul_one] at hr
  rw [Finsupp.single_eq_of_ne (Ne.symm hij), mul_zero] at hr
  exact b.ne_zero i (h0 hr.symm)

/-- A module with a basis indexed by a subsingleton is generated by the basis vector. -/
private lemma wshA2_eq_repr_smul {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Subsingleton ι] (i₀ : ι) (b : Module.Basis ι R M) (m : M) : m = b.repr m i₀ • b i₀ := by
  conv_lhs => rw [← b.repr.symm_apply_apply m]
  rw [← b.repr_symm_single]
  congr 1
  ext j
  rw [Subsingleton.elim j i₀, Finsupp.single_eq_same]

/-- A locally free Weil divisorial subsheaf is, near every point, generated by a single section
`f` which is a unit of `K(X)`. -/
private lemma wshA2_exists_unit_generator [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]
    (L : WeilDivisorialSubsheaf X)
    (hL : SheafOfModules.IsLocallyFree L.toRationalFunctionsSubmodule.toModules) (x : X) :
    ∃ (W : X.Opens) (_ : x ∈ W) (f : ToType ((rationalFunctionsPresheaf X).obj (op W))),
      f ∈ L.sections W ∧ IsUnit f ∧
      ∀ (W' : X.Opens) (i : W' ⟶ W) (s : ToType ((rationalFunctionsPresheaf X).obj (op W'))),
        s ∈ L.sections W' → ∀ y ∈ W', ∃ (V' : X.Opens) (j : V' ⟶ W'), y ∈ V' ∧
          ∃ a : Γ(X, V'), (rationalFunctionsPresheaf X).map j.op s =
            a • (rationalFunctionsPresheaf X).map (j ≫ i).op f := by
  -- a chart of `L` around `x`, and the generic point of a component through `x`
  obtain ⟨q, hq⟩ := hL.exists_isLocallyFreeData
  obtain ⟨k, hk⟩ : ∃ k, x ∈ q.X k := by
    have h : IsOpenCover q.X := (Opens.coversTop_iff ((X : TopCat.{u}) : Type u) q.X).1 q.coversTop
    have hx : x ∈ (⨆ i, q.X i) := by rw [h.iSup_eq_top]; exact Opens.mem_top x
    simpa using hx
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hxZ : x ∈ closure {componentGenericPoint X Z} := by
    rw [(isGenericPoint_componentGenericPoint X Z).def]
    exact mem_irreducibleComponent
  have hηk : componentGenericPoint X Z ∈ q.X k :=
    (specializes_iff_mem_closure.mpr hxZ).mem_open (q.X k).isOpen hk
  obtain ⟨bη⟩ := Stacks.StalkFreeBridge.nonempty_stalkBasis_of_isLocallyFreeData
    L.toRationalFunctionsSubmodule.toModules q k hηk
  have hsub := wshA2_subsingleton_of_basis L _ (coheight_componentGenericPoint_le_one Z) bη
  obtain ⟨i₀⟩ : Nonempty (q.generators k).I := by
    by_contra hI
    rw [not_nonempty_iff] at hI
    obtain ⟨W0, hz0, l0, hl0, hne, -⟩ := WeilDivisorialSubsheaf.wshA_exists_generator L Z
    have hm : TopCat.Presheaf.germ L.toRationalFunctionsSubmodule.toModules.val.presheaf W0 _ hz0
        (⟨l0, hl0⟩ : L.sections W0) = 0 :=
      bη.ext_elem isEmptyElim
    rw [← map_zero (TopCat.Presheaf.germ
      L.toRationalFunctionsSubmodule.toModules.val.presheaf W0 _ hz0).hom] at hm
    obtain ⟨W', hzW', i₁, i₂, h⟩ := TopCat.Presheaf.germ_eq _ _ hz0 hz0 _ _ hm
    have h' := congrFun (congrArg Subtype.val h) ⟨Z, hzW'⟩
    exact hne (h'.trans (congrFun (map_zero
      ((rationalFunctionsPresheaf X).map i₂.op).hom) ⟨Z, hzW'⟩))
  -- the stalk at `x` is free of rank one, generated by the germ of a section `f₀`
  obtain ⟨bx⟩ := Stacks.StalkFreeBridge.nonempty_stalkBasis_of_isLocallyFreeData
    L.toRationalFunctionsSubmodule.toModules q k hk
  obtain ⟨W, hxW, f₀, hf₀⟩ := TopCat.Presheaf.exists_germ_eq
    L.toRationalFunctionsSubmodule.toModules.val.presheaf (bx i₀)
  have hgen := wshA2_eq_repr_smul i₀ bx
  have G1 : ∀ (W' : X.Opens) (_ : x ∈ W') (s : ToType ((rationalFunctionsPresheaf X).obj (op W'))),
      s ∈ L.sections W' → ∃ (W'' : X.Opens) (_ : x ∈ W'') (i : W'' ⟶ W') (i' : W'' ⟶ W)
        (a : Γ(X, W'')), (rationalFunctionsPresheaf X).map i.op s =
          a • (rationalFunctionsPresheaf X).map i'.op f₀.1 := by
    intro W' hxW' s hs
    obtain ⟨U, hU, hxU, r, hr⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf
      (bx.repr (TopCat.Presheaf.germ L.toRationalFunctionsSubmodule.toModules.val.presheaf W' x hxW'
        (⟨s, hs⟩ : L.sections W')) i₀) (show x ∈ W ⊓ W' from ⟨hxW, hxW'⟩)
    have h1 := hgen (TopCat.Presheaf.germ L.toRationalFunctionsSubmodule.toModules.val.presheaf
      W' x hxW' (⟨s, hs⟩ : L.sections W'))
    rw [← hr, ← hf₀, ← TopCat.Presheaf.germ_res_apply _ (homOfLE (hU.trans inf_le_left)) x hxU f₀]
      at h1
    have h0 := TopCat.Presheaf.germ_res_apply L.toRationalFunctionsSubmodule.toModules.val.presheaf
      (homOfLE (hU.trans inf_le_right)) x hxU (⟨s, hs⟩ : L.sections W')
    have h2 := h0.trans (h1.trans (PresheafOfModules.germ_smul (R := X.presheaf)
      L.toRationalFunctionsSubmodule.toModules.val x U hxU r _).symm)
    obtain ⟨W'', hxW'', i₁, i₂, h3⟩ := TopCat.Presheaf.germ_eq _ x hxU hxU _ _ h2
    have hi : i₂ = i₁ := Subsingleton.elim _ _
    subst hi
    refine ⟨W'', hxW'', i₂ ≫ homOfLE (hU.trans inf_le_right),
      i₂ ≫ homOfLE (hU.trans inf_le_left), X.presheaf.map i₂.op r, ?_⟩
    have h4 := congrArg Subtype.val h3
    change (rationalFunctionsPresheaf X).map i₂.op
        ((rationalFunctionsPresheaf X).map (homOfLE (hU.trans inf_le_right)).op s) =
      (rationalFunctionsPresheaf X).map i₂.op
        (r • (rationalFunctionsPresheaf X).map (homOfLE (hU.trans inf_le_left)).op f₀.1) at h4
    rw [rationalFunctionsPresheaf_map_smul] at h4
    exact h4
  -- finitely many local generators of `L` near `x`, each a multiple of `f₀` near `x`
  obtain ⟨V, hxV, J, hJ, t, ht⟩ := Stacks.SheafOfModules.LocallySurjective.exists_local_generators
    (X := X.toRingedSpace) (F := L.toRationalFunctionsSubmodule.toModules)
    L.isCoherent.isFiniteType x
  have hG := fun j => G1 V hxV (t j).1 (t j).2
  choose Wj hxWj ij ij' aj hj using hG
  obtain ⟨W1, hxW1, hW1V, hW1W, hW1j⟩ : ∃ W1 : X.Opens, x ∈ W1 ∧ W1 ≤ V ∧ W1 ≤ W ∧
      ∀ j, W1 ≤ Wj j := by
    refine ⟨(V ⊓ W) ⊓ ⨅ j, Wj j, ⟨⟨hxV, hxW⟩, ?_⟩, inf_le_left.trans inf_le_left,
      inf_le_left.trans inf_le_right, fun j => inf_le_right.trans (iInf_le Wj j)⟩
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxWj
  have hloc : ∀ (W' : X.Opens) (i : W' ⟶ W1)
      (s : ToType ((rationalFunctionsPresheaf X).obj (op W'))),
      s ∈ L.sections W' → ∀ y ∈ W', ∃ (V' : X.Opens) (j : V' ⟶ W'), y ∈ V' ∧
        ∃ a : Γ(X, V'), (rationalFunctionsPresheaf X).map j.op s =
          a • (rationalFunctionsPresheaf X).map (j ≫ i).op
            ((rationalFunctionsPresheaf X).map (homOfLE hW1W).op f₀.1) := by
    intro W' i s hs y hy
    obtain ⟨V', hV'W', hyV', c, hc⟩ := ht W' (i.le.trans hW1V) ⟨s, hs⟩ y hy
    let c' : J → Γ(X, V') := fun j => c j
    refine ⟨V', homOfLE hV'W', hyV', ∑ j, c' j * X.presheaf.map
      (homOfLE (hV'W'.trans (i.le.trans (hW1j j)))).op (aj j), ?_⟩
    have hc2 : (⟨(rationalFunctionsPresheaf X).map (homOfLE hV'W').op s,
        L.map_mem _ hs⟩ : L.sections V') = ∑ j, c' j •
          (⟨(rationalFunctionsPresheaf X).map (homOfLE (hV'W'.trans (i.le.trans hW1V))).op
            (t j).1, L.map_mem _ (t j).2⟩ : L.sections V') := hc
    have hc3 := congrArg Subtype.val hc2
    rw [Submodule.coe_sum] at hc3
    simp only [Submodule.coe_smul] at hc3
    refine hc3.trans ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : (rationalFunctionsPresheaf X).map (homOfLE (hV'W'.trans (i.le.trans hW1V))).op
        (t j).1 = (rationalFunctionsPresheaf X).map
          (homOfLE (hV'W'.trans (i.le.trans (hW1j j)))).op
          ((rationalFunctionsPresheaf X).map (ij j).op (t j).1) := rfl
    rw [e1, hj j, rationalFunctionsPresheaf_map_smul, smul_smul]
    rfl
  refine ⟨W1, hxW1, (rationalFunctionsPresheaf X).map (homOfLE hW1W).op f₀.1,
    L.map_mem _ f₀.2, ?_, hloc⟩
  refine (Pi.isUnit_iff (x := ((rationalFunctionsPresheaf X).map (homOfLE hW1W).op f₀.1 :
    ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W1},
      X.presheaf.stalk (componentGenericPoint X Z.1)))).mpr ?_
  rintro ⟨Z', hZ'⟩
  obtain ⟨W0, hz0, l0, hl0, hne, -⟩ := WeilDivisorialSubsheaf.wshA_exists_generator L Z'
  obtain ⟨V', j, hzV', a, ha⟩ := hloc (W0 ⊓ W1) (homOfLE inf_le_right)
    ((rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op l0) (L.map_mem _ hl0) _ ⟨hz0, hZ'⟩
  have h1 := congrFun ha ⟨Z', hzV'⟩
  have h2 : l0 ⟨Z', hz0⟩ = X.presheaf.germ V' _ hzV' a *
      (rationalFunctionsPresheaf X).map (homOfLE hW1W).op f₀.1 ⟨Z', hZ'⟩ := h1
  let _ := (RationalFunctions.isField_stalk X Z').toField
  refine IsUnit.mk0 _ fun h0 => hne ?_
  rw [h2, h0, mul_zero]

/-- Near a point where `𝓛` is generated by a unit `f` of `K(X)`, `f⁻¹ (𝓛 · 𝓛') ⊆ 𝓛'`. -/
private lemma wshA2_inv_mul_mem (L L' : WeilDivisorialSubsheaf X) {W : X.Opens}
    (f g : ToType ((rationalFunctionsPresheaf X).obj (op W))) (hg : g * f = 1)
    (hloc : ∀ (W' : X.Opens) (i : W' ⟶ W) (s : ToType ((rationalFunctionsPresheaf X).obj (op W'))),
        s ∈ L.sections W' → ∀ y ∈ W', ∃ (V' : X.Opens) (j : V' ⟶ W'), y ∈ V' ∧
          ∃ a : Γ(X, V'), (rationalFunctionsPresheaf X).map j.op s =
            a • (rationalFunctionsPresheaf X).map (j ≫ i).op f)
    {V : X.Opens} (i : V ⟶ W) (c : ToType ((rationalFunctionsPresheaf X).obj (op V)))
    (hc : c ∈ (L.mul L').sections V) :
    (rationalFunctionsPresheaf X).map i.op g * c ∈ L'.sections V := by
  refine (congrArg (fun F : RationalFunctionsSubmodule X =>
    (rationalFunctionsPresheaf X).map i.op g * c ∈ F.sections V) L'.isSaturated).mpr ?_
  intro η hη hη1
  obtain ⟨W3, i3, hη3, h3⟩ := (RationalFunctionsSubmodule.germ_mem_stalkSet_iff _ hη c).mp
    (hc η hη hη1)
  obtain ⟨W4, i4, hη4, h4⟩ := h3 η hη3
  have key : ∀ t ∈ L.sections W4 * L'.sections W4, ∃ (W5 : X.Opens) (j : W5 ⟶ W4), η ∈ W5 ∧
      (rationalFunctionsPresheaf X).map j.op
        ((rationalFunctionsPresheaf X).map (i4 ≫ i3 ≫ i).op g * t) ∈ L'.sections W5 := by
    intro t ht
    refine Submodule.mul_induction_on ht (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨V', j, hηV', a', ha'⟩ := hloc W4 (i4 ≫ i3 ≫ i) a ha η hη4
      refine ⟨V', j, hηV', ?_⟩
      have hGF : (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op g *
          (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op f = 1 := by
        rw [← map_mul, hg, map_one]
      have e1 : (rationalFunctionsPresheaf X).map j.op
          ((rationalFunctionsPresheaf X).map (i4 ≫ i3 ≫ i).op g * (a * b)) =
          (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op g *
            ((rationalFunctionsPresheaf X).map j.op a * (rationalFunctionsPresheaf X).map j.op b) := by
        rw [map_mul, map_mul]; rfl
      rw [e1, ha', Algebra.smul_def]
      have e2 : (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op g *
          (algebraMap Γ(X, V') _ a' * (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op f *
            (rationalFunctionsPresheaf X).map j.op b) =
          algebraMap Γ(X, V') _ a' * ((rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op g *
            (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3 ≫ i).op f) *
            (rationalFunctionsPresheaf X).map j.op b := by ring
      rw [e2, hGF, mul_one, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (L'.map_mem j hb)
    · obtain ⟨W₁, j₁, h₁, m₁⟩ := ha
      obtain ⟨W₂, j₂, h₂, m₂⟩ := hb
      refine ⟨W₁ ⊓ W₂, homOfLE (inf_le_left.trans j₁.le), ⟨h₁, h₂⟩, ?_⟩
      rw [mul_add, map_add]
      exact add_mem (L'.map_mem (homOfLE inf_le_left) m₁) (L'.map_mem (homOfLE inf_le_right) m₂)
  obtain ⟨W5, j, hη5, h5⟩ := key _ h4
  refine (RationalFunctionsSubmodule.germ_mem_stalkSet_iff _ hη _).mpr
    ⟨W5, j ≫ i4 ≫ i3, hη5, ?_⟩
  have e3 : (rationalFunctionsPresheaf X).map (j ≫ i4 ≫ i3).op
      ((rationalFunctionsPresheaf X).map i.op g * c) =
      (rationalFunctionsPresheaf X).map j.op
        ((rationalFunctionsPresheaf X).map (i4 ≫ i3 ≫ i).op g *
          (rationalFunctionsPresheaf X).map i4.op ((rationalFunctionsPresheaf X).map i3.op c)) := by
    rw [map_mul, map_mul]; rfl
  rw [e3]
  exact h5

/-- **FA Def. 16.1.2: `𝓛 ⊗ 𝓛' ≅ 𝓛 · 𝓛'` for `𝓛` locally free.** Let `X` be reduced and Noetherian
and `𝓛, 𝓛'` Weil divisorial subsheaves with `𝓛` locally free. Then the natural map
`𝓛 ⊗ 𝓛' → 𝓛 · 𝓛'`, the morphism sending `a ⊗ b` to `ab` on local sections, is an isomorphism. -/
@[mmp "lem_fa16a_product_iso_tensor_locally_free"]
theorem WeilDivisorialSubsheaf.exists_isIso_tensor_mul [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (L L' : WeilDivisorialSubsheaf X)
    (hL : SheafOfModules.IsLocallyFree L.toRationalFunctionsSubmodule.toModules) :
    ∃ μ : L.toRationalFunctionsSubmodule.toModules ⊗ L'.toRationalFunctionsSubmodule.toModules ⟶
        (L.mul L').toModules,
      (∀ (U : X.Opensᵒᵖ) (a : L.sections U.unop) (b : L'.sections U.unop),
        (show (L.mul L').sections U.unop from
          (μ.val.app U).hom (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            X.toRingedSpace _ _ U (a ⊗ₜ b))).1 = a.1 * b.1) ∧ IsIso μ := by
  have hmulmem : ∀ (U : X.Opens) (x : L.sections U) (y : L'.sections U),
      x.1 * y.1 ∈ (L.mul L').sections U := by
    intro U x y η hη _
    refine ⟨U, hη, x.1 * y.1, fun z hz => ⟨U, 𝟙 U, hz, ?_⟩, rfl⟩
    exact Submodule.mul_mem_mul x.2 y.2
  let β : Stacks.BilinearMap L.toRationalFunctionsSubmodule.toModules.val
      L'.toRationalFunctionsSubmodule.toModules.val (L.mul L').toModules.val :=
    { app := fun U => AddMonoidHom.mk'
        (fun x => AddMonoidHom.mk' (fun y => (⟨x.1 * y.1, hmulmem U.unop x y⟩ : (L.mul L').sections U.unop))
          (fun y y' => Subtype.ext (mul_add _ _ _)))
        (fun x x' => AddMonoidHom.ext fun y => Subtype.ext (add_mul _ _ _))
      map_smul_left := fun U r x y => Subtype.ext (smul_mul_assoc _ _ _)
      map_smul_right := fun U r x y => Subtype.ext (mul_smul_comm _ _ _)
      naturality := fun {U V} i x y => Subtype.ext
        (map_mul ((rationalFunctionsPresheaf X).map i.unop.op).hom x.1 y.1) }
  let μ : L.toRationalFunctionsSubmodule.toModules ⊗ L'.toRationalFunctionsSubmodule.toModules ⟶
      (L.mul L').toModules :=
    PresheafOfModules.tensorSheafDesc (Osharp := ⟨X.presheaf, X.IsSheaf⟩)
      (F := L.toRationalFunctionsSubmodule.toModules) (G := L'.toRationalFunctionsSubmodule.toModules)
      (Q := (L.mul L').toModules) (PresheafOfModules.ofBilinear β)
  have hsec : ∀ (U : X.Opensᵒᵖ) (a : L.sections U.unop) (b : L'.sections U.unop),
      (show (L.mul L').sections U.unop from
        (μ.val.app U).hom (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          X.toRingedSpace _ _ U (a ⊗ₜ b))).1 = a.1 * b.1 := by
    intro U a b
    exact congrArg Subtype.val (PresheafOfModules.tensorSheafDesc_unit (Osharp := ⟨X.presheaf, X.IsSheaf⟩)
      (F := L.toRationalFunctionsSubmodule.toModules) (G := L'.toRationalFunctionsSubmodule.toModules)
      (Q := (L.mul L').toModules) (PresheafOfModules.ofBilinear β) U a b |>.trans
        (PresheafOfModules.ofBilinear_tmul _ _ _ _))
  refine ⟨μ, hsec, ?_⟩
  refine ExtensionByZeroModules.isIso_of_stalk_isIso X.ringCatSheaf μ fun x => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  let T := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x
    L.toRationalFunctionsSubmodule.toModules L'.toRationalFunctionsSubmodule.toModules
  have hform : ∀ (V : X.Opens) (hxV : x ∈ V) (a : L.sections V) (b : L'.sections V),
      ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((ExtensionByZeroModules.toAb X.ringCatSheaf).map μ))
        (T.symm (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
          L.toRationalFunctionsSubmodule.toModules.val x V hxV a ⊗ₜ
          Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
          L'.toRationalFunctionsSubmodule.toModules.val x V hxV b)) =
      TopCat.Presheaf.germ ((ExtensionByZeroModules.toAb X.ringCatSheaf).obj (L.mul L').toModules)
        V x hxV (⟨a.1 * b.1, hmulmem V a b⟩ : (L.mul L').sections V) := by
    intro V hxV a b
    have h1 := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_germ X.toRingedSpace x
      L.toRationalFunctionsSubmodule.toModules L'.toRationalFunctionsSubmodule.toModules V hxV a b
    rw [← h1, LinearEquiv.symm_apply_apply]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    congr 1
    exact Subtype.ext (hsec (op V) a b)
  obtain ⟨W, hxW, f, hfL, hfu, hloc⟩ := wshA2_exists_unit_generator L hL x
  obtain ⟨g, hg⟩ : ∃ g, g * f = 1 := ⟨(hfu.unit⁻¹ : _), hfu.unit.inv_mul⟩
  let e := Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
    L.toRationalFunctionsSubmodule.toModules.val x W hxW (⟨f, hfL⟩ : L.sections W)
  -- `e` is the germ of the restriction of `f` to any smaller neighbourhood
  have he : ∀ (V : X.Opens) (hxV : x ∈ V) (i : V ⟶ W),
      e = Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
        L.toRationalFunctionsSubmodule.toModules.val x V hxV
          (⟨(rationalFunctionsPresheaf X).map i.op f, L.map_mem i hfL⟩ : L.sections V) :=
    fun V hxV i => (TopCat.Presheaf.germ_res_apply
      L.toRationalFunctionsSubmodule.toModules.val.presheaf i x hxV _).symm
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    L.toRationalFunctionsSubmodule.toModules.val x
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace
    L'.toRationalFunctionsSubmodule.toModules.val x
  have hall : ∀ t : TensorProduct (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk
        X.toRingedSpace x) (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace
        L.toRationalFunctionsSubmodule.toModules.val x)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk X.toRingedSpace
        L'.toRationalFunctionsSubmodule.toModules.val x), ∃ n, t = e ⊗ₜ n := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    | tmul m n =>
      obtain ⟨V, hVW, hxV, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
        L.toRationalFunctionsSubmodule.toModules.val.presheaf m hxW
      obtain ⟨V', j, hxV', a, ha⟩ := hloc V (homOfLE hVW) s.1 s.2 x hxV
      have hm : (TopCat.Presheaf.germ L.toRationalFunctionsSubmodule.toModules.val.presheaf V x hxV) s =
          Stacks.SheafOfModules.TensorStalkRingedSpace.ringGerm X.toRingedSpace x V' hxV' a • e := by
        rw [he V' hxV' (j ≫ homOfLE hVW)]
        refine (TopCat.Presheaf.germ_res_apply _ j x hxV' s).symm.trans ?_
        refine Eq.trans ?_ (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul
          X.toRingedSpace L.toRationalFunctionsSubmodule.toModules.val x V' hxV' a _)
        exact congrArg (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
          L.toRationalFunctionsSubmodule.toModules.val x V' hxV') (Subtype.ext ha)
      refine ⟨Stacks.SheafOfModules.TensorStalkRingedSpace.ringGerm X.toRingedSpace x V' hxV' a • n, ?_⟩
      rw [hm, TensorProduct.smul_tmul]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨n₁, rfl⟩ := h₁
      obtain ⟨n₂, rfl⟩ := h₂
      exact ⟨n₁ + n₂, (TensorProduct.tmul_add _ _ _).symm⟩
  let Ψ := ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((ExtensionByZeroModules.toAb X.ringCatSheaf).map μ))
  have hΦ : ∀ (V : X.Opens) (hVW : V ≤ W) (hxV : x ∈ V) (b : L'.sections V),
      Ψ (T.symm (e ⊗ₜ Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
          L'.toRationalFunctionsSubmodule.toModules.val x V hxV b)) =
        TopCat.Presheaf.germ ((ExtensionByZeroModules.toAb X.ringCatSheaf).obj (L.mul L').toModules)
          V x hxV (⟨(rationalFunctionsPresheaf X).map (homOfLE hVW).op f * b.1,
            hmulmem V ⟨_, L.map_mem (homOfLE hVW) hfL⟩ b⟩ : (L.mul L').sections V) := by
    intro V hVW hxV b
    rw [he V hxV (homOfLE hVW)]
    exact hform V hxV _ b
  let φ := Ψ.comp T.symm.toLinearMap.toAddMonoidHom
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨n, rfl⟩ := hall t
      obtain ⟨V, hVW, hxV, b, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
        L'.toRationalFunctionsSubmodule.toModules.val.presheaf n hxW
      have h0 := (hΦ V hVW hxV b).symm.trans ht
      have h0' := h0.trans (map_zero (TopCat.Presheaf.germ ((ExtensionByZeroModules.toAb
        X.ringCatSheaf).obj (L.mul L').toModules) V x hxV).hom).symm
      obtain ⟨V', hxV', i₁, i₂, h1⟩ := TopCat.Presheaf.germ_eq _ x hxV hxV _ _ h0'
      have h2 : (rationalFunctionsPresheaf X).map i₁.op
          ((rationalFunctionsPresheaf X).map (homOfLE hVW).op f * b.1) = 0 := by
        have := congrArg Subtype.val h1
        exact this.trans (map_zero ((rationalFunctionsPresheaf X).map i₂.op).hom)
      have h3 : (rationalFunctionsPresheaf X).map i₁.op b.1 = 0 := by
        have hgf : (rationalFunctionsPresheaf X).map (i₁ ≫ homOfLE hVW).op g *
            (rationalFunctionsPresheaf X).map (i₁ ≫ homOfLE hVW).op f = 1 := by
          rw [← map_mul, hg, map_one]
        rw [map_mul] at h2
        calc (rationalFunctionsPresheaf X).map i₁.op b.1
            = ((rationalFunctionsPresheaf X).map (i₁ ≫ homOfLE hVW).op g *
                (rationalFunctionsPresheaf X).map (i₁ ≫ homOfLE hVW).op f) *
              (rationalFunctionsPresheaf X).map i₁.op b.1 := by rw [hgf, one_mul]
          _ = (rationalFunctionsPresheaf X).map (i₁ ≫ homOfLE hVW).op g *
              ((rationalFunctionsPresheaf X).map i₁.op
                ((rationalFunctionsPresheaf X).map (homOfLE hVW).op f) *
              (rationalFunctionsPresheaf X).map i₁.op b.1) := by rw [mul_assoc]; rfl
          _ = 0 := by rw [h2, mul_zero]
      have h4 : (TopCat.Presheaf.germ L'.toRationalFunctionsSubmodule.toModules.val.presheaf
          V x hxV) b = 0 := by
        rw [← TopCat.Presheaf.germ_res_apply _ i₁ x hxV' b]
        have h5 : L'.toRationalFunctionsSubmodule.toModules.val.presheaf.map i₁.op b = 0 :=
          Subtype.ext h3
        rw [h5, map_zero]
      rw [h4]
      exact TensorProduct.tmul_zero _ _
    · intro c
      obtain ⟨V, hVW, hxV, c', rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
        ((ExtensionByZeroModules.toAb X.ringCatSheaf).obj (L.mul L').toModules) c hxW
      let b : L'.sections V := ⟨(rationalFunctionsPresheaf X).map (homOfLE hVW).op g * c'.1,
        wshA2_inv_mul_mem L L' f g hg hloc (homOfLE hVW) c'.1 c'.2⟩
      refine ⟨e ⊗ₜ Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace
          L'.toRationalFunctionsSubmodule.toModules.val x V hxV b, ?_⟩
      refine (hΦ V hVW hxV b).trans ?_
      congr 1
      refine Subtype.ext ?_
      change (rationalFunctionsPresheaf X).map (homOfLE hVW).op f *
        ((rationalFunctionsPresheaf X).map (homOfLE hVW).op g * c'.1) = c'.1
      rw [← mul_assoc, ← map_mul, mul_comm f g, hg, map_one, one_mul]
  have key : ∀ z, Ψ z = φ (T z) := fun z => congrArg Ψ (T.symm_apply_apply z).symm
  constructor
  · intro z₁ z₂ h
    exact T.injective (hφ.1 ((key z₁).symm.trans (h.trans (key z₂))))
  · intro c
    obtain ⟨t, rfl⟩ := hφ.2 c
    exact ⟨T.symm t, (key _).trans (congrArg φ (T.apply_symm_apply t))⟩

end Tensor

end MMP.Flips
