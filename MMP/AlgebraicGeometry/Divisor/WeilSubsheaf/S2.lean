/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.Group
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkFormula
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocusOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth
public import StacksFrontier.RingTheory.CohenMacaulay.Localization
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.GorensteinRegularElement
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# `S₂`, the structure sheaf and `𝒪(D)` as Weil divisorial subsheaves (FA 16.2–16.3)

This file proves the following facts about Weil divisorial subsheaves of the sheaf `K(X)` of
rational functions on a reduced Noetherian scheme `X`, together with two commutative-algebra
inputs used alongside them.

## Main results

* `MMP.Flips.satisfiesS2_iff_bijective_restrict`: a reduced locally Noetherian scheme is `S₂` if
  and only if restriction `𝒪_X(V) → 𝒪_X(W)` is bijective whenever every point of `V ∖ W` has a
  local ring of dimension `≥ 2` (Hartogs extension across codimension two).
* `MMP.Flips.exists_weilDivisorialSubsheaf_unit_iff_satisfiesS2` (FA 16.3.2): `𝒪_X ⊆ K(X)` is a
  Weil divisorial subsheaf if and only if `X` is `S₂`.
* `MMP.Flips.WeilDivisor.exists_weilDivisorialSubsheaf_sheaf` (FA 16.2.2): on a reduced,
  pure-dimensional scheme of finite type over a field, `𝒪(D)` is a Weil divisorial subsheaf for
  every Weil divisor `D`.
* `MMP.Flips.WeilDivisor.exists_injective_hom` (FA 16.2.2): `D ↦ 𝒪(D)` is an injective group
  homomorphism `WDiv(X) → WSh(X)`.
* `MMP.Flips.isGorensteinLocalRing_quotient_ofList`: the quotient of a regular local ring by a
  regular sequence is a Gorenstein, hence Cohen–Macaulay and `S₂`, local ring.
* `MMP.Flips.isClosed_setOf_not_isCohenMacaulayLocalRing`: the non-Cohen–Macaulay locus of a
  scheme of finite type over a field is closed.

## Main definitions

* `MMP.Flips.RationalFunctionsSubmodule.IsGeneratedAt`: `𝓕_η = c 𝒪_{X,η}` for a unit `c`.
* `MMP.Flips.WeilDivisorPrime.uniformizer`: a uniformizer of `𝒪_{X,Γ}`.
* `MMP.Flips.WeilDivisorPrime.localGenerator`: the local generator of `𝓘_Γ` at a point.
* `MMP.Flips.vanishingIdealImage`: the ideal sheaf of a closed subset, inside `K(X)`.

## Implementation notes

For a prime divisor `Γ` the ideal sheaf `𝓘_Γ ⊆ 𝒪_X` of the reduced closed subscheme on `Γ̄` has
coherent image in `K(X)`, with stalk `t_Γ 𝒪_{X,Γ}` at `Γ` for a uniformizer `t_Γ` and the local
ring at every other point of codimension `≤ 1`. So `𝓜_Γ = sat(𝓘_Γ)` is a Weil divisorial
subsheaf, and the product `∏_Γ 𝓜_Γ^{[-n_Γ]}` in the group `WSh(X)` has the stalks of `𝒪(D)` in
codimension `≤ 1`; both are saturated, hence equal. The stalk condition defining `𝒪(D)` at `Γ` is
imposed for every uniformizer of `𝒪_{X,Γ}`; any two differ by a unit, so it is the condition for
the one uniformizer `MMP.Flips.WeilDivisorPrime.uniformizer`
(`MMP.Flips.WeilDivisor.stalkCondition_genericPoint_iff`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.2–16.3
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite Limits

namespace MMP.Flips

open MMP.Mori

/-! ### `S₂` and extension across codimension two -/

section S2

variable {X : Scheme.{u}}

/-- `S₂` in terms of `Module.depth`. -/
theorem satisfiesS2_iff_forall_min_le_depth :
    SatisfiesS2 X ↔ ∀ x : X, min 2 (ringKrullDim (X.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) : WithBot ℕ∞) := by
  refine forall_congr' fun x => ?_
  set R := X.presheaf.stalk x
  rw [depth_eq_depthSup_of_isLocalRing]
  constructor
  · rintro ⟨s, hs, hreg, hlen⟩
    exact hlen.trans (WithBot.coe_le_coe.mpr (Module.le_depthSup hs hreg))
  · intro h
    have key : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) R →
        ∃ s : List R, (∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R) ∧
          RingTheory.Sequence.IsRegular R s ∧ k < s.length := by
      intro k hk
      rw [Module.depthSup_eq_iSup] at hk
      have hlt : ((k : ℕ) : ℕ∞) < _ := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hk
      obtain ⟨rs, hlt'⟩ := lt_iSup_iff.mp hlt
      obtain ⟨⟨hmem, hreg⟩, hlt''⟩ := lt_iSup_iff.mp hlt'
      exact ⟨rs, hmem, hreg, by exact_mod_cast hlt''⟩
    by_cases h2 : ((1 + 1 : ℕ) : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) R
    · obtain ⟨s, hs, hreg, hlen⟩ := key 1 h2
      exact ⟨s, hs, hreg, (min_le_left _ _).trans (by exact_mod_cast hlen)⟩
    by_cases h1 : ((0 + 1 : ℕ) : ℕ∞) ≤ Module.depthSup R (IsLocalRing.maximalIdeal R) R
    · obtain ⟨s, hs, hreg, hlen⟩ := key 0 h1
      refine ⟨s, hs, hreg, h.trans ?_⟩
      have : Module.depthSup R (IsLocalRing.maximalIdeal R) R ≤ 1 := by
        simpa using not_le.mp h2
      exact WithBot.coe_le_coe.mpr (this.trans (by exact_mod_cast hlen))
    · refine ⟨[], by simp, RingTheory.Sequence.IsRegular.nil _ _, h.trans ?_⟩
      have : Module.depthSup R (IsLocalRing.maximalIdeal R) R = 0 := by
        simpa using not_le.mp h1
      simp only [List.length_nil, CharP.cast_eq_zero]
      exact WithBot.coe_le_coe.mpr this.le

/-- **`S₂` gives extension across codimension two.** -/
theorem bijective_presheaf_map_of_satisfiesS2 [IsLocallyNoetherian X] (hX : SatisfiesS2 X)
    {V W : X.Opens} (h : W ≤ V)
    (hcodim : ∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z)) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  refine restriction_bijective_of_depth_ge_two_of_le (SheafOfModules.unit X.ringCatSheaf) h
    fun z hz hzW => ?_
  have h2 := satisfiesS2_iff_forall_min_le_depth.mp hX z
  rw [min_eq_left (hcodim z hz hzW)] at h2
  have h2' : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk z)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z) :=
    WithBot.coe_le_coe.mp h2
  exact h2'.trans_eq
    (Module.depth_eq_depth_of_linearEquiv _ (Stacks.UnitStalk.unitStalkLinearEquiv X z))

/-- **Extension across codimension two gives depth two.** If restriction of functions is
bijective across every closed subset all of whose points have local rings of dimension `≥ 2`,
then every local ring of dimension `≥ 2` has depth `≥ 2`. -/
theorem two_le_depth_stalk_of_bijective_presheaf_map [IsLocallyNoetherian X]
    (H : ∀ (V W : X.Opens) (h : W ≤ V),
      (∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z)) →
        Function.Bijective (X.presheaf.map (homOfLE h).op))
    (x : X) (hx : 2 ≤ ringKrullDim (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) := by
  let U : X.Opens := ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hxU : x ∉ (U : Set X) := fun h => h (subset_closure rfl)
  have hres : ∀ W : X.Opens, Function.Bijective
      (X.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op) := by
    intro W
    refine H W _ (U.ι.image_preimage_le W) fun z hzW hz => ?_
    have hzU : z ∉ (U : Set X) := by
      intro hzU
      apply hz
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact ⟨hzU, hzW⟩
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr (not_not.mp hzU)
    refine hx.trans ?_
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
    exact WithBot.coe_le_coe.mpr (Order.coheight_anti (show z ≤ x from hxz))
  have hL : IsIso ((Scheme.Modules.restrictAdjunction U.ι).unit.app F) := by
    have : IsIso ((Scheme.Modules.toPresheaf X).map
        ((Scheme.Modules.restrictAdjunction U.ι).unit.app F)) := by
      refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W => ?_
      induction W using Opposite.rec with | op W => ?_
      exact (ConcreteCategory.isIso_iff_bijective _).mpr (hres W)
    exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf X)
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F) := by
    have hcomp : (Scheme.Modules.restrictAdjunction U.ι).unit.app F ≫
        (Scheme.Modules.pushforward U.ι).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app F) =
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app F :=
      Adjunction.unit_leftAdjointUniq_hom_app _ _ F
    rw [← hcomp]
    infer_instance
  have : F.IsFiniteType := Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_unit
  exact (Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem
    U F hunit x hxU).trans_eq
    (Module.depth_eq_depth_of_linearEquiv _ (Stacks.UnitStalk.unitStalkLinearEquiv X x)).symm

/-- **Serre `S₂` is equivalent to extension across codimension two.** Let `X` be a reduced
locally Noetherian scheme. Then `X` is `S₂` iff for every open `V ⊆ X` and every closed
`Z ⊆ V` with `codim_V Z ≥ 2` (every point of `Z` has local-ring dimension `≥ 2`), the restriction
`𝒪_X(V) → 𝒪_X(V ∖ Z)` is bijective. -/
@[mmp "lem_mmp_foundation_s2_hartogs_equivalence"]
theorem satisfiesS2_iff_bijective_restrict [IsReduced X] [IsLocallyNoetherian X] :
    SatisfiesS2 X ↔ ∀ (V W : X.Opens) (h : W ≤ V),
      (∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z)) →
        Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  refine ⟨fun hX V W h hcodim => bijective_presheaf_map_of_satisfiesS2 hX h hcodim,
    fun H => satisfiesS2_iff_forall_min_le_depth.mpr fun x => ?_⟩
  by_cases hx : 2 ≤ ringKrullDim (X.presheaf.stalk x)
  · rw [min_eq_left hx]
    exact WithBot.coe_le_coe.mpr (two_le_depth_stalk_of_bijective_presheaf_map H x hx)
  · have hS1 := ((isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero X).mp ‹_›).1 x
    have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
      obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (X.presheaf.stalk x) = d :=
        WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot) |>.imp fun _ h => h.symm
      rw [hd] at hx ⊢
      have hd2 : d < 1 + 1 := by
        rw [one_add_one_eq_two]
        exact WithBot.coe_lt_coe.mp (not_le.mp hx)
      exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one hd2)
    rw [min_eq_right (not_le.mp hx).le]
    exact (le_min (by simpa using hle) le_rfl).trans hS1

end S2

/-! ### Stalks of submodules of `K(X)` -/

section StalkSet

variable {X : Scheme.{u}}

namespace RationalFunctionsSubmodule

/-- `𝓕_η = c · 𝒪_{X,η}` for a unit `c` of `K(X)_η`. -/
def IsGeneratedAt (F : RationalFunctionsSubmodule X) (η : X)
    (c : ((rationalFunctionsPresheaf X).stalk η)ˣ) : Prop :=
  F.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
    (c : (rationalFunctionsPresheaf X).stalk η) * (structureStalkToRationalFunctionsStalk X η).hom a

/-- At a point of codimension at most one, the stalk of the saturation of `F` is the stalk of `F`.
-/
theorem stalkSet_saturation {F : RationalFunctionsSubmodule X} {η : X}
    (hη : Order.coheight η ≤ 1) : F.saturation.stalkSet η = F.stalkSet η := by
  ext g
  rw [← mem_stalk, ← mem_stalk, stalk_saturation F hη]

/-- The saturation of a submodule of `K(X)` is saturated. -/
theorem isSaturated_saturation (F : RationalFunctionsSubmodule X) : F.saturation.IsSaturated :=
  saturation_eq_of_stalk fun _ hη => (stalk_saturation F hη).symm

/-- The stalk of `𝒪_X ⊆ K(X)` at `η` is the image of `𝒪_{X,η}` in `K(X)_η`. -/
theorem stalkSet_unit (η : X) :
    (unit X).stalkSet η = Set.range (structureStalkToRationalFunctionsStalk X η).hom := by
  refine (unit_stalkSet_subset η).antisymm ?_
  rintro _ ⟨b, rfl⟩
  obtain ⟨V, hV, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf b
  refine ⟨V, hV, (toRationalFunctionsPresheaf X).app (op V) r, ?_, ?_⟩
  · exact fun y hy => ⟨V, 𝟙 V, hy, Submodule.mem_one.mpr ⟨r, by
      rw [rationalFunctionsPresheaf_map_id_apply]; rfl⟩⟩
  · exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V η hV
      (toRationalFunctionsPresheaf X) r).symm

end RationalFunctionsSubmodule

end StalkSet

/-! ### The structure sheaf as a Weil divisorial subsheaf (FA 16.3.2) -/

section StructureSheaf

variable {X : Scheme.{u}}

/-- A point of coheight `≤ 1` does not have a local ring of dimension `≥ 2`. -/
private lemma not_two_le_ringKrullDim_of_coheight_le_one {η : X} (hη : Order.coheight η ≤ 1) :
    ¬ 2 ≤ ringKrullDim (X.presheaf.stalk η) := by
  rw [ringKrullDim_stalk_eq_coheight]
  intro h
  have h' : (2 : ℕ∞) ≤ Order.coheight η := WithBot.coe_le_coe.mp h
  exact absurd (h'.trans hη) (by decide)

/-- If every point of `V ∖ W` has a local ring of dimension `≥ 2`, then every generic point of
an irreducible component lying in `V` lies in `W`. -/
private lemma mem_of_two_le_ringKrullDim {V W : X.Opens}
    (hZ : ∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z))
    (Z : irreducibleComponents X) (hZV : componentGenericPoint X Z ∈ V) :
    componentGenericPoint X Z ∈ W := by
  by_contra hn
  exact not_two_le_ringKrullDim_of_coheight_le_one (coheight_componentGenericPoint_le_one Z)
    (hZ _ hZV hn)

/-- If `𝒪_X ⊆ K(X)` is saturated, then restriction of functions is bijective across every
closed subset all of whose points have local rings of dimension `≥ 2`. -/
theorem bijective_presheaf_map_of_isSaturated_unit [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (hsat : (RationalFunctionsSubmodule.unit X).IsSaturated) {V W : X.Opens}
    (h : W ≤ V) (hZ : ∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z)) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  have : IsNoetherian X := {}
  have hgen := fun Z hZV => mem_of_two_le_ringKrullDim (V := V) (W := W) hZ Z hZV
  refine ⟨fun a b hab => ?_, fun g => ?_⟩
  · apply injective_toRationalFunctionsPresheaf_app V
    funext Z
    have := congrArg ((toRationalFunctionsPresheaf X).app (op W)) hab
    rw [toRationalFunctionsPresheaf_app_map, toRationalFunctionsPresheaf_app_map] at this
    exact congrFun this ⟨Z.1, hgen Z.1 Z.2⟩
  · let s : ToType ((rationalFunctionsPresheaf X).obj (op V)) := fun Z =>
      (toRationalFunctionsPresheaf X).app (op W) g ⟨Z.1, hgen Z.1 Z.2⟩
    have hs : (rationalFunctionsPresheaf X).map (homOfLE h).op s =
        (toRationalFunctionsPresheaf X).app (op W) g := rfl
    have hmem : s ∈ (RationalFunctionsSubmodule.unit X).saturation.sections V := by
      intro η hη hc
      have hηW : η ∈ W := by
        by_contra hn
        exact not_two_le_ringKrullDim_of_coheight_le_one hc (hZ η hη hn)
      rw [← TopCat.Presheaf.germ_res_apply (rationalFunctionsPresheaf X) (homOfLE h) η hηW s, hs]
      exact ⟨W, hηW, _, fun x hx => ⟨W, 𝟙 W, hx, Submodule.mem_one.mpr ⟨g, rfl⟩⟩, rfl⟩
    rw [← hsat] at hmem
    obtain ⟨r, hr⟩ := exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit hmem
    refine ⟨r, injective_toRationalFunctionsPresheaf_app W ?_⟩
    rw [toRationalFunctionsPresheaf_app_map, hr, hs]

/-- If restriction of functions is bijective across every closed subset all of whose points
have local rings of dimension `≥ 2`, then `𝒪_X ⊆ K(X)` is saturated. -/
theorem isSaturated_unit_of_bijective_presheaf_map [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X]
    (H : ∀ (V W : X.Opens) (h : W ≤ V),
      (∀ z ∈ V, z ∉ W → 2 ≤ ringKrullDim (X.presheaf.stalk z)) →
        Function.Bijective (X.presheaf.map (homOfLE h).op)) :
    (RationalFunctionsSubmodule.unit X).IsSaturated := by
  have : IsNoetherian X := {}
  refine RationalFunctionsSubmodule.ext fun V => le_antisymm
    ((RationalFunctionsSubmodule.unit X).sections_le_saturation V) fun s hs => ?_
  let U : X.Opens := ⨆ (W : X.Opens) (i : W ⟶ V)
    (_ : (rationalFunctionsPresheaf X).map i.op s ∈
      (RationalFunctionsSubmodule.unit X).sections W), W
  have hUV : U ≤ V := iSup₂_le fun W i => iSup_le fun _ => i.le
  have hsU : (rationalFunctionsPresheaf X).map (homOfLE hUV).op s ∈
      (RationalFunctionsSubmodule.unit X).sections U := by
    refine (RationalFunctionsSubmodule.unit X).mem_of_locally fun x hx => ?_
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hW
    obtain ⟨hm, hxW⟩ := Opens.mem_iSup.mp hi
    exact ⟨W, homOfLE (le_iSup₂_of_le W i (le_iSup (fun _ => W) hm)), hxW, hm⟩
  have hcod : ∀ z ∈ V, z ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk z) := by
    intro z hzV hzU
    rw [ringKrullDim_stalk_eq_coheight]
    by_contra hlt
    have hc : Order.coheight z ≤ 1 := by
      by_contra h1
      exact hlt (WithBot.coe_le_coe.mpr (Order.add_one_le_of_lt (not_le.mp h1) : (2 : ℕ∞) ≤ _))
    obtain ⟨W, i, hzW, hm⟩ :=
      ((RationalFunctionsSubmodule.unit X).germ_mem_stalkSet_iff hzV s).mp (hs z hzV hc)
    exact hzU (Opens.mem_iSup.mpr ⟨W, Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hm, hzW⟩⟩⟩)
  obtain ⟨g, hg⟩ := exists_toRationalFunctionsPresheaf_app_eq_of_mem_unit hsU
  obtain ⟨t, rfl⟩ := (H V U hUV hcod).2 g
  have hgen := fun Z hZV => mem_of_two_le_ringKrullDim (V := V) (W := U) hcod Z hZV
  have hts : (toRationalFunctionsPresheaf X).app (op V) t = s := by
    funext Z
    have := congrFun hg ⟨Z.1, hgen Z.1 Z.2⟩
    rwa [toRationalFunctionsPresheaf_app_map] at this
  rw [← hts]
  exact fun x hx => ⟨V, 𝟙 V, hx, Submodule.mem_one.mpr ⟨t, rfl⟩⟩

/-- **FA 16.3.2.** Let `X` be a reduced Noetherian scheme. Then
`𝒪_X ⊆ K(X)` is a Weil divisorial subsheaf if and only if `X` is `S₂`. -/
@[mmp "lem_fa16a_structure_sheaf_divisorial_iff_s2"]
theorem exists_weilDivisorialSubsheaf_unit_iff_satisfiesS2 [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] :
    (∃ L : WeilDivisorialSubsheaf X,
        L.toRationalFunctionsSubmodule = RationalFunctionsSubmodule.unit X) ↔ SatisfiesS2 X := by
  have : IsNoetherian X := {}
  rw [satisfiesS2_iff_bijective_restrict]
  refine ⟨fun ⟨L, hL⟩ V W h hZ =>
    bijective_presheaf_map_of_isSaturated_unit (hL ▸ L.isSaturated) h hZ, fun H => ?_⟩
  refine ⟨{ toRationalFunctionsSubmodule := RationalFunctionsSubmodule.unit X
            isCoherent := RationalFunctionsSubmodule.isCoherent_toModules_unit
            principal_codim_one := fun η _ =>
              ⟨1, by rw [RationalFunctionsSubmodule.stalkSet_unit]; simp⟩
            isSaturated := isSaturated_unit_of_bijective_presheaf_map H }, rfl⟩

end StructureSheaf

/-! ### `𝒪(D)` is a Weil divisorial subsheaf (FA 16.2.2) -/

section Construction

variable {X : Scheme.{u}}

open RationalFunctionsSubmodule

section Group

variable [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X]
  [G : CommGroup (WeilDivisorialSubsheaf X)] (hG : IsWShGroup G)

include hG

omit [IsReduced X] [IsLocallyNoetherian X] [CompactSpace X] in
/-- At a point of codimension at most one, the identity of `WSh(X)` is generated by `1`. -/
theorem IsWShGroup.isGeneratedAt_one {η : X} (hη : Order.coheight η ≤ 1) :
    (1 : WeilDivisorialSubsheaf X).IsGeneratedAt η 1 := by
  have h1 : (1 : WeilDivisorialSubsheaf X).toRationalFunctionsSubmodule = (unit X).saturation :=
    hG.one_eq
  rw [IsGeneratedAt, h1, stalkSet_saturation hη, stalkSet_unit]
  simp

/-- If `L` and `L'` are generated at `η` by `c` and `c'`, then `L * L'` is generated at `η`
by `c * c'`. -/
theorem IsWShGroup.isGeneratedAt_mul {L L' : WeilDivisorialSubsheaf X} {η : X}
    (hη : Order.coheight η ≤ 1) {c c' : ((rationalFunctionsPresheaf X).stalk η)ˣ}
    (hL : L.IsGeneratedAt η c) (hL' : L'.IsGeneratedAt η c') :
    (L * L').IsGeneratedAt η (c * c') := by
  have h1 : (L * L').toRationalFunctionsSubmodule = L.mul L' := hG.mul_eq L L'
  rw [IsGeneratedAt, h1]
  exact (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L' η hη c c' hL hL').1

/-- If `L` is generated at `η` by `c`, then `L⁻¹` is generated at `η` by `c⁻¹`. -/
theorem IsWShGroup.isGeneratedAt_inv {L : WeilDivisorialSubsheaf X} {η : X}
    (hη : Order.coheight η ≤ 1) {c : ((rationalFunctionsPresheaf X).stalk η)ˣ}
    (hL : L.IsGeneratedAt η c) : L⁻¹.IsGeneratedAt η c⁻¹ := by
  have h1 : (L⁻¹).toRationalFunctionsSubmodule = L.inv := hG.inv_eq L
  rw [IsGeneratedAt, h1]
  exact (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L η hη c c hL hL).2.1

/-- If `L` is generated at `η` by `c`, then `L ^ n` is generated at `η` by `c ^ n` for every
`n : ℕ`. -/
theorem IsWShGroup.isGeneratedAt_pow {L : WeilDivisorialSubsheaf X} {η : X}
    (hη : Order.coheight η ≤ 1) {c : ((rationalFunctionsPresheaf X).stalk η)ˣ}
    (hL : L.IsGeneratedAt η c) (n : ℕ) : (L ^ n).IsGeneratedAt η (c ^ n) := by
  induction n with
  | zero => simpa using hG.isGeneratedAt_one hη
  | succ n ih => simpa [pow_succ] using hG.isGeneratedAt_mul hη ih hL

/-- If `L` is generated at `η` by `c`, then `L ^ n` is generated at `η` by `c ^ n` for every
`n : ℤ`. -/
theorem IsWShGroup.isGeneratedAt_zpow {L : WeilDivisorialSubsheaf X} {η : X}
    (hη : Order.coheight η ≤ 1) {c : ((rationalFunctionsPresheaf X).stalk η)ˣ}
    (hL : L.IsGeneratedAt η c) (n : ℤ) : (L ^ n).IsGeneratedAt η (c ^ n) := by
  cases n with
  | ofNat n => simpa using hG.isGeneratedAt_pow hη hL n
  | negSucc n => simpa using hG.isGeneratedAt_inv hη (hG.isGeneratedAt_pow hη hL (n + 1))

/-- If each `L i` is generated at `η` by `c i`, then `∏ i ∈ s, L i` is generated at `η` by
`∏ i ∈ s, c i`. -/
theorem IsWShGroup.isGeneratedAt_prod {ι : Type*} (s : Finset ι) (L : ι → WeilDivisorialSubsheaf X)
    {η : X} (hη : Order.coheight η ≤ 1) (c : ι → ((rationalFunctionsPresheaf X).stalk η)ˣ)
    (hL : ∀ i ∈ s, (L i).IsGeneratedAt η (c i)) :
    (∏ i ∈ s, L i).IsGeneratedAt η (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hG.isGeneratedAt_one hη
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact hG.isGeneratedAt_mul hη (hL i (Finset.mem_insert_self i s))
      (ih fun j hj => hL j (Finset.mem_insert_of_mem hj))

end Group

/-- On a reduced Noetherian scheme, if `𝒪_{X,η}` is a domain then every nonzero `a ∈ 𝒪_{X,η}`
becomes a unit in `K(X)_η`. -/
theorem isUnit_structureStalkToRationalFunctionsStalk [IsReduced X] [IsNoetherian X] {η : X}
    [IsDomain (X.presheaf.stalk η)] {a : X.presheaf.stalk η} (ha : a ≠ 0) :
    IsUnit ((structureStalkToRationalFunctionsStalk X η).hom a) := by
  classical
  obtain ⟨V, hV, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf a
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
  let W : X.Opens := V ⊓ Y
  have hW : η ∈ W := ⟨hV, hηY⟩
  let iV : W ⟶ V := homOfLE inf_le_left
  let s₀ : ToType ((rationalFunctionsPresheaf X).obj (op W)) :=
    (toRationalFunctionsPresheaf X).app (op W) (X.presheaf.map iV.op r)
  have hne : ∀ Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ W}, s₀ Z ≠ 0 := by
    rintro ⟨Z, hZ⟩
    have hsp := (isGenericPoint_componentGenericPoint X Z).specializes (hηZ Z hZ.2)
    change X.presheaf.germ W _ hZ (X.presheaf.map iV.op r) ≠ 0
    rw [X.presheaf.germ_res_apply, ← X.presheaf.germ_stalkSpecializes_apply hV hsp]
    let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hsp
    have hinj := IsLocalization.injective (X.presheaf.stalk (componentGenericPoint X Z))
      (Ideal.primeCompl_le_nonZeroDivisors
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk (componentGenericPoint X Z))).under
          (X.presheaf.stalk η)))
    intro h0
    exact ha (hinj (h0.trans (map_zero _).symm))
  let s' : ToType ((rationalFunctionsPresheaf X).obj (op W)) := fun Z => Ring.inverse (s₀ Z)
  have hmul : s₀ * s' = 1 := by
    funext Z
    change s₀ Z * Ring.inverse (s₀ Z) = 1
    refine Ring.mul_inverse_cancel _ ?_
    let := (RationalFunctions.isField_stalk X Z.1).toField
    exact Ne.isUnit (hne Z)
  have e : (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ V η hV r) =
      (rationalFunctionsPresheaf X).germ W η hW s₀ := by
    rw [← X.presheaf.germ_res_apply iV η hW r]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply W η hW _ _
  rw [e]
  exact IsUnit.of_mul_eq_one ((rationalFunctionsPresheaf X).germ W η hW s')
    (by rw [← map_mul, hmul, map_one])

/-! ### Uniformizers -/

namespace WeilDivisorPrime

/-- The local ring `𝒪_{X,Γ}` of a prime divisor `Γ` is a domain. -/
instance isDomain_localRing (Γ : WeilDivisorPrime X) : IsDomain Γ.1.localRing := Γ.2.choose

/-- The local ring `𝒪_{X,Γ}` of a prime divisor `Γ` is a discrete valuation ring. -/
instance isDiscreteValuationRing_localRing (Γ : WeilDivisorPrime X) :
    IsDiscreteValuationRing Γ.1.localRing :=
  Γ.2.choose_spec

/-- A uniformizer of the discrete valuation ring `𝒪_{X,Γ}`. -/
def uniformizer (Γ : WeilDivisorPrime X) : Γ.1.localRing :=
  (IsDiscreteValuationRing.exists_irreducible Γ.1.localRing).choose

/-- The uniformizer of `𝒪_{X,Γ}` is irreducible. -/
theorem irreducible_uniformizer (Γ : WeilDivisorPrime X) : Irreducible Γ.uniformizer :=
  (IsDiscreteValuationRing.exists_irreducible Γ.1.localRing).choose_spec

/-- The image in `K(X)_Γ` of the uniformizer of `𝒪_{X,Γ}` is a unit. -/
theorem isUnit_uniformizer [IsReduced X] [IsNoetherian X] (Γ : WeilDivisorPrime X) :
    IsUnit ((structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom Γ.uniformizer) :=
  isUnit_structureStalkToRationalFunctionsStalk Γ.irreducible_uniformizer.ne_zero

/-- The image in `K(X)_Γ` of the uniformizer of `𝒪_{X,Γ}`, a unit. -/
def uniformizerUnit [IsReduced X] [IsNoetherian X] (Γ : WeilDivisorPrime X) :
    ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ :=
  Γ.isUnit_uniformizer.unit

/-- The value of `Γ.uniformizerUnit` is the image in `K(X)_Γ` of the uniformizer of `𝒪_{X,Γ}`. -/
theorem val_uniformizerUnit [IsReduced X] [IsNoetherian X] (Γ : WeilDivisorPrime X) :
    (Γ.uniformizerUnit : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) =
      (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom Γ.uniformizer :=
  rfl

open scoped Classical in
/-- The local generator of `𝒪(-Γ)` at `η`: the image of the uniformizer at `η = Γ`, and `1`
elsewhere. -/
def localGenerator [IsReduced X] [IsNoetherian X] (Γ : WeilDivisorPrime X) (η : X) :
    ((rationalFunctionsPresheaf X).stalk η)ˣ :=
  if h : Γ.1.genericPoint = η then h ▸ Γ.uniformizerUnit else 1

/-- At the generic point of `Γ`, the local generator is the image of the uniformizer. -/
theorem localGenerator_self [IsReduced X] [IsNoetherian X] (Γ : WeilDivisorPrime X) :
    Γ.localGenerator Γ.1.genericPoint = Γ.uniformizerUnit := by
  simp [localGenerator]

/-- At a point other than the generic point of `Γ`, the local generator is `1`. -/
theorem localGenerator_of_ne [IsReduced X] [IsNoetherian X] (Γ : WeilDivisorPrime X) {η : X}
    (h : Γ.1.genericPoint ≠ η) : Γ.localGenerator η = 1 := by
  rw [localGenerator, dif_neg h]

/-- A prime divisor is determined by its generic point. -/
theorem genericPoint_injective :
    Function.Injective fun Γ : WeilDivisorPrime X => Γ.1.genericPoint :=
  fun _ _ h => Subtype.ext (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h)

end WeilDivisorPrime

/-! ### The stalk condition of `𝒪(D)` -/

namespace WeilDivisor

/-- At a point of codimension at least two, every germ satisfies the stalk condition of `𝒪(D)`. -/
theorem stalkCondition_of_not_coheight_le_one (D : WeilDivisor X) {x : X}
    (hx : ¬ Order.coheight x ≤ 1) (g : (rationalFunctionsPresheaf X).stalk x) :
    D.StalkCondition x g := by
  refine ⟨fun Γ h _ _ => ?_, fun h => absurd h hx⟩
  subst h
  exact absurd (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le hx

/-- At the generic point of a prime divisor `Γ`, a germ satisfies the stalk condition of `𝒪(D)` if
and only if it lies in `t_Γ^{-D(Γ)} 𝒪_{X,Γ}`, for `t_Γ` the uniformizer of `𝒪_{X,Γ}`. -/
theorem stalkCondition_genericPoint_iff [IsReduced X] [IsNoetherian X] (D : WeilDivisor X)
    (Γ : WeilDivisorPrime X) (g : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) :
    D.StalkCondition Γ.1.genericPoint g ↔ g ∈ Set.range fun a : X.presheaf.stalk Γ.1.genericPoint =>
      ((Γ.uniformizerUnit ^ (-D Γ) : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
        (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
        (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom a := by
  set φ := (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom
  set τ := Γ.uniformizerUnit
  have hτ : (τ : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) = φ Γ.uniformizer := rfl
  set p := (D Γ).toNat with hp
  set q := (-D Γ).toNat with hq
  have hpq : (p : ℤ) - q = D Γ := Int.toNat_sub_toNat_neg (D Γ)
  set T := (τ : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)
  set Ti := ((τ⁻¹ : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
    (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)
  have hTT : T * Ti = 1 := Units.mul_inv τ
  have hz : ((τ ^ (-D Γ) : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
      (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) = T ^ q * Ti ^ p := by
    rw [show -D Γ = (q : ℤ) - p by omega, zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul,
      Units.val_pow_eq_pow_val, ← inv_pow, Units.val_pow_eq_pow_val]
  have key : ∀ t : Γ.1.localRing, Irreducible t → ((∃ a, φ t ^ p * g = φ t ^ q * φ a) ↔
      ∃ a, g = T ^ q * Ti ^ p * φ a) := by
    intro t ht
    obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible _
      Γ.irreducible_uniformizer ht
    set V := φ u
    set Vi := φ ↑u⁻¹
    have hVV : V * Vi = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have e1 : φ (Γ.uniformizer * u) = T * V := by rw [map_mul, hτ]
    rw [e1]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨↑u⁻¹ ^ p * ↑u ^ q * a, ?_⟩
      rw [map_mul, map_mul, map_pow, map_pow]
      calc g = (T * Ti) ^ p * (V * Vi) ^ p * g := by rw [hTT, hVV]; simp
        _ = Ti ^ p * Vi ^ p * ((T * V) ^ p * g) := by ring
        _ = Ti ^ p * Vi ^ p * ((T * V) ^ q * φ a) := by rw [ha]
        _ = _ := by ring
    · rintro ⟨a, rfl⟩
      refine ⟨↑u ^ p * ↑u⁻¹ ^ q * a, ?_⟩
      rw [map_mul, map_mul, map_pow, map_pow]
      calc (T * V) ^ p * (T ^ q * Ti ^ p * φ a) = (T * Ti) ^ p * (T ^ q * V ^ p * φ a) := by ring
        _ = (V * Vi) ^ q * (T ^ q * V ^ p * φ a) := by rw [hTT, hVV]; simp
        _ = _ := by ring
  rw [hz]
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (key _ Γ.irreducible_uniformizer).mp
      (h.1 Γ rfl Γ.uniformizer Γ.irreducible_uniformizer)
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨fun Γ' h t ht => ?_, fun _ h => absurd rfl (h Γ)⟩
    obtain rfl := WeilDivisorPrime.genericPoint_injective h
    exact (key t ht).mpr ⟨a, rfl⟩

/-- At a point `η` of codimension at most one that is not the generic point of a prime divisor, a
germ satisfies the stalk condition of `𝒪(D)` if and only if it lies in the image of `𝒪_{X,η}`. -/
theorem stalkCondition_iff_of_forall_ne (D : WeilDivisor X) {η : X} (hη : Order.coheight η ≤ 1)
    (hΓ : ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint ≠ η)
    (g : (rationalFunctionsPresheaf X).stalk η) :
    D.StalkCondition η g ↔ g ∈ Set.range (structureStalkToRationalFunctionsStalk X η).hom :=
  ⟨fun h => h.2 hη hΓ, fun h => ⟨fun Γ h' => absurd h' (hΓ Γ), fun _ _ => h⟩⟩

end WeilDivisor

/-! ### Ideal sheaves of closed subsets inside `K(X)` -/

/-- The composite `𝓝 ⊆ 𝒪_X ⟶ K(X)` for a subsheaf `𝓝 ⊆ 𝒪_X`. -/
def submoduleToRationalFunctions (N : (SheafOfModules.unit X.ringCatSheaf).Submodule) :
    N.toSheafOfModules ⟶ rationalFunctionsModule X where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun n => (⟨(toRationalFunctionsPresheaf X).app U n.1, Submodule.mem_top⟩ :
            (RationalFunctionsSubmodule.top X).sections U.unop)
          map_add' := fun a b =>
            Subtype.ext (map_add ((toRationalFunctionsPresheaf X).app U).hom a.1 b.1)
          map_smul' := fun r a => Subtype.ext (by
            change (toRationalFunctionsPresheaf X).app U
              ((show Γ(X, U.unop) from r) * (show Γ(X, U.unop) from a.1)) = _
            rw [map_mul]
            rfl) }
      naturality := fun {U V} i => by
        ext n
        apply Subtype.ext
        exact (ConcreteCategory.congr_hom ((toRationalFunctionsPresheaf X).naturality i) n.1) }

/-- The map `𝓝 ⟶ K(X)` sends a section `n` of `𝓝` to the image of `n` in `K(X)`. -/
theorem submoduleToRationalFunctions_app (N : (SheafOfModules.unit X.ringCatSheaf).Submodule)
    (U : X.Opens) (n : N.toSheafOfModules.val.obj (op U)) :
    ((submoduleToRationalFunctions N).val.app (op U) n).1 =
      (toRationalFunctionsPresheaf X).app (op U) n.1 := rfl

/-- The ideal sheaf `𝓘 ⊆ 𝒪_X` of a quasi-coherent ideal on a locally Noetherian scheme is
coherent. -/
theorem isCoherent_idealModule [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    SheafOfModules.IsCoherent (Stacks.Algebraization.idealModule I) := by
  have h : ∀ U : X.Opens, IsAffineOpen U →
      Module.Finite Γ(X, U) Γ(Stacks.Algebraization.idealModule I, U) := by
    intro U hU
    have : IsNoetherianRing (X.ringCatSheaf.obj.obj (op U)) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : IsNoetherian (X.ringCatSheaf.obj.obj (op U))
        ((SheafOfModules.unit X.ringCatSheaf).val.obj (op U)) :=
      (inferInstance : IsNoetherian (X.ringCatSheaf.obj.obj (op U)) (X.ringCatSheaf.obj.obj (op U)))
    have : IsNoetherian (X.ringCatSheaf.obj.obj (op U)) ((Stacks.Algebraization.idealPowerMultiple
        I 1 (SheafOfModules.unit X.ringCatSheaf)).obj (op U)) := isNoetherian_submodule' _
    exact (inferInstance : Module.Finite (X.ringCatSheaf.obj.obj (op U))
      ((Stacks.Algebraization.idealPowerMultiple I 1 (SheafOfModules.unit X.ringCatSheaf)).obj
        (op U)))
  have hft : (Stacks.Algebraization.idealModule I).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn _
      (fun V : X.affineOpens => (V : X.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top X))
      (fun V => V.2)
      fun V =>
        Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isFiniteTildeOn_of_moduleFinite_sections
          _ V (h V.1 V.2)
  exact
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- On an affine open `U`, `a ∈ 𝓘_Z(U)` iff `a` vanishes at every point of `Z ∩ U`. -/
theorem mem_vanishingIdeal_ideal_iff (Z : Closeds X) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Γ(X, U)) :
    a ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨U, hU⟩ ↔
      ∀ x ∈ U, x ∈ Z → x ∉ X.basicOpen a := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  have hb : ∀ p, hU.fromSpec p ∈ X.basicOpen a ↔ p ∈ PrimeSpectrum.basicOpen a := fun p => by
    rw [← hU.fromSpec_preimage_basicOpen]; rfl
  constructor
  · intro h x hx hxZ hxa
    obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
    exact ((hb p).mp hxa) (h p hxZ)
  · intro h p hp
    by_contra hpa
    have hpU : hU.fromSpec p ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact Set.mem_range_self p
    exact h _ hpU hp ((hb p).mpr hpa)

/-- The ideal sheaf `𝓘_Z ⊆ 𝒪_X` of the reduced closed subscheme on `Z`, as a subsheaf. -/
abbrev vanishingIdealSubmodule (Z : Closeds X) : (SheafOfModules.unit X.ringCatSheaf).Submodule :=
  Stacks.Algebraization.idealPowerMultiple (Scheme.IdealSheafData.vanishingIdeal Z) 1
    (SheafOfModules.unit X.ringCatSheaf)

/-- The ideal sheaf `𝓘_Z` of a closed subset `Z`, as a submodule of `K(X)`. -/
def vanishingIdealImage (Z : Closeds X) : RationalFunctionsSubmodule X :=
  imageSubmodule (submoduleToRationalFunctions (vanishingIdealSubmodule Z))

/-- On a reduced, locally Noetherian, quasi-compact scheme, `𝓝 ⟶ K(X)` is injective on sections. -/
theorem injective_submoduleToRationalFunctions_app [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (N : (SheafOfModules.unit X.ringCatSheaf).Submodule) (U : X.Opens) :
    Function.Injective ((submoduleToRationalFunctions N).val.app (op U)) := by
  intro a b h
  have h1 := congrArg Subtype.val h
  rw [submoduleToRationalFunctions_app, submoduleToRationalFunctions_app] at h1
  exact Subtype.ext (injective_toRationalFunctionsPresheaf_app U h1)

/-- On a reduced Noetherian scheme, the ideal sheaf `𝓘_Z` of a closed subset, inside `K(X)`, is
coherent. -/
theorem isCoherent_vanishingIdealImage [IsReduced X] [IsNoetherian X] (Z : Closeds X) :
    SheafOfModules.IsCoherent (vanishingIdealImage Z).toModules := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  exact isCoherent_of_moduleIso
    (isoImageSubmodule _ (injective_submoduleToRationalFunctions_app _))
    (isCoherent_idealModule _)

/-- The stalks of `𝓘_Z ⊆ K(X)`: the images of the germs of functions on affine opens vanishing
along `Z`. -/
theorem mem_stalkSet_vanishingIdealImage_iff [IsReduced X] [IsLocallyNoetherian X]
    [CompactSpace X] (Z : Closeds X) {η : X} (g : (rationalFunctionsPresheaf X).stalk η) :
    g ∈ (vanishingIdealImage Z).stalkSet η ↔ ∃ (U : X.Opens) (_ : IsAffineOpen U) (hη : η ∈ U)
      (a : Γ(X, U)), (∀ x ∈ U, x ∈ Z → x ∉ X.basicOpen a) ∧
        g = (structureStalkToRationalFunctionsStalk X η).hom (X.presheaf.germ U η hη a) := by
  set φ := submoduleToRationalFunctions (vanishingIdealSubmodule Z)
  constructor
  · rintro ⟨V, hV, s, hs, rfl⟩
    obtain ⟨t, ht⟩ := exists_preimage_of_mem_imageSubmodule φ
      (injective_submoduleToRationalFunctions_app _) hs
    obtain ⟨U, hUa, hηU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hV
    let i : U ⟶ V := homOfLE hUV
    let t' := (vanishingIdealSubmodule Z).toSheafOfModules.val.map i.op t
    have ht' : t'.1 ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨U, hUa⟩ := by
      rw [← Stacks.Algebraization.idealModule_obj_affine]
      exact t'.2
    refine ⟨U, hUa, hηU, t'.1, (mem_vanishingIdeal_ideal_iff Z hUa _).mp ht', ?_⟩
    rw [← TopCat.Presheaf.germ_res_apply _ i η hηU, ← ht,
      ← rationalFunctionsModule_naturality_apply φ i t]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U η hηU _ _).symm
  · rintro ⟨U, hUa, hηU, a, ha, rfl⟩
    have ha' : a ∈ (vanishingIdealSubmodule Z).obj (op U) := by
      rw [Stacks.Algebraization.idealModule_obj_affine _ ⟨U, hUa⟩]
      exact (mem_vanishingIdeal_ideal_iff Z hUa a).mpr ha
    refine ⟨U, hηU, _, val_app_mem_imageSubmodule φ (⟨a, ha'⟩ :
      (vanishingIdealSubmodule Z).toSheafOfModules.val.obj (op U)), ?_⟩
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U η hηU _ _).symm

namespace WeilDivisorPrime

/-- The support `Γ̄`, the closure of the generic point, of a prime divisor `Γ`. -/
def closure (Γ : WeilDivisorPrime X) : Closeds X :=
  ⟨_root_.closure {Γ.1.genericPoint}, isClosed_closure⟩

/-- A point of codimension at most one other than the generic point of `Γ` does not lie in `Γ̄`. -/
theorem notMem_closure_of_coheight_le_one (Γ : WeilDivisorPrime X) {η : X}
    (hη : Order.coheight η ≤ 1) (h : Γ.1.genericPoint ≠ η) : η ∉ Γ.closure := by
  intro hηZ
  have hle : η ≤ Γ.1.genericPoint := specializes_iff_mem_closure.mpr hηZ
  have hlt : η < Γ.1.genericPoint := hle.lt_of_not_ge fun hge =>
    h ((specializes_iff_mem_closure.mpr hηZ).antisymm hge).eq
  have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1
  have := Order.coheight_strictAnti hlt (by rw [h1]; exact ENat.natCast_lt_top 1)
  rw [h1] at this
  exact absurd (this.trans_le hη) (lt_irrefl _)

/-- The stalk of `𝓘_Γ ⊆ K(X)` at the generic point of `Γ` is `t_Γ 𝒪_{X,Γ}`, for `t_Γ` the
uniformizer. -/
theorem isGeneratedAt_vanishingIdealImage_self [IsReduced X] [IsNoetherian X]
    (Γ : WeilDivisorPrime X) :
    (vanishingIdealImage Γ.closure).IsGeneratedAt Γ.1.genericPoint Γ.uniformizerUnit := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  ext g
  rw [mem_stalkSet_vanishingIdealImage_iff]
  constructor
  · rintro ⟨U, hU, hη, a, ha, rfl⟩
    have hna : ¬ IsUnit (X.presheaf.germ U _ hη a) := by
      rw [← X.mem_basicOpen a _ hη]
      exact ha _ hη (subset_closure rfl)
    have hm : X.presheaf.germ U _ hη a ∈ IsLocalRing.maximalIdeal Γ.1.localRing := hna
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp Γ.irreducible_uniformizer,
      Ideal.mem_span_singleton'] at hm
    obtain ⟨b, hb⟩ := hm
    refine ⟨b, ?_⟩
    change (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom Γ.uniformizer * _ = _
    rw [← map_mul, mul_comm, hb]
  · rintro ⟨b, rfl⟩
    obtain ⟨V, hV, r, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf (Γ.uniformizer * b)
    obtain ⟨U, hUa, hηU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hV
    let i : U ⟶ V := homOfLE hUV
    have hgerm : X.presheaf.germ U _ hηU (X.presheaf.map i.op r) = Γ.uniformizer * b := by
      rwa [X.presheaf.germ_res_apply]
    refine ⟨U, hUa, hηU, X.presheaf.map i.op r, fun x hx hxZ hxa => ?_, ?_⟩
    · have hsp : Γ.1.genericPoint ⤳ x := specializes_iff_mem_closure.mpr hxZ
      have h1 : Γ.1.genericPoint ∈ X.basicOpen (X.presheaf.map i.op r) :=
        hsp.mem_open (X.basicOpen _).isOpen hxa
      rw [X.mem_basicOpen _ _ hηU, hgerm] at h1
      exact Γ.irreducible_uniformizer.not_isUnit (isUnit_of_mul_isUnit_left h1)
    · rw [hgerm, map_mul]
      rfl

/-- At a point `η` of codimension at most one other than the generic point of `Γ`, the stalk of
`𝓘_Γ ⊆ K(X)` is `𝒪_{X,η}`. -/
theorem isGeneratedAt_vanishingIdealImage_of_ne [IsReduced X] [IsNoetherian X]
    (Γ : WeilDivisorPrime X) {η : X} (hη : Order.coheight η ≤ 1) (h : Γ.1.genericPoint ≠ η) :
    (vanishingIdealImage Γ.closure).IsGeneratedAt η 1 := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have hηZ := Γ.notMem_closure_of_coheight_le_one hη h
  ext g
  rw [mem_stalkSet_vanishingIdealImage_iff]
  constructor
  · rintro ⟨U, hU, hηU, a, ha, rfl⟩
    exact ⟨X.presheaf.germ U η hηU a, one_mul _⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨V, hV, r, hr⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf b
    let Y : X.Opens := ⟨(Γ.closure : Set X)ᶜ, Γ.closure.isClosed.isOpen_compl⟩
    obtain ⟨U, hUa, hηU, hUV⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show η ∈ V ⊓ Y from ⟨hV, hηZ⟩)
    let i : U ⟶ V := homOfLE (hUV.trans inf_le_left)
    refine ⟨U, hUa, hηU, X.presheaf.map i.op r, fun x hx hxZ _ => (hUV hx).2 hxZ, ?_⟩
    beta_reduce
    rw [Units.val_one, one_mul, X.presheaf.germ_res_apply, hr]

end WeilDivisorPrime

/-- On a reduced, pure-dimensional scheme of finite type over a field, every prime divisor `Γ` has
a Weil divisorial subsheaf whose stalk at each point `η` of codimension at most one is generated by
`Γ.localGenerator η`. -/
theorem WeilDivisorPrime.exists_weilDivisorialSubsheaf_isGeneratedAt {k : Type u} [Field k]
    [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (Γ : WeilDivisorPrime X) :
    ∃ M : WeilDivisorialSubsheaf X, ∀ η : X, Order.coheight η ≤ 1 →
      M.IsGeneratedAt η (Γ.localGenerator η) := by
  set J := vanishingIdealImage Γ.closure
  have hJ : ∀ η : X, Order.coheight η ≤ 1 → J.IsGeneratedAt η (Γ.localGenerator η) := by
    intro η hη
    by_cases h : Γ.1.genericPoint = η
    · subst h
      rw [Γ.localGenerator_self]
      exact Γ.isGeneratedAt_vanishingIdealImage_self
    · rw [Γ.localGenerator_of_ne h]
      exact Γ.isGeneratedAt_vanishingIdealImage_of_ne hη h
  exact ⟨⟨J.saturation,
    RationalFunctionsSubmodule.isCoherent_saturation π hd (isCoherent_vanishingIdealImage _),
    fun η hη => ⟨_, (stalkSet_saturation hη).trans (hJ η hη)⟩, isSaturated_saturation J⟩,
    fun η hη => (stalkSet_saturation hη).trans (hJ η hη)⟩

end Construction

open RationalFunctionsSubmodule

section WeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **FA Def. 16.2.2, `𝒪(D) ∈ WSh(X)`.** Let `X` be a reduced, pure-dimensional scheme of finite
type over `k`. For every Weil divisor `D ∈ WDiv(X)`, `𝒪(D)` is a Weil divisorial subsheaf. -/
@[mmp "lem_fa16a_sheaf_of_weil_divisor_divisorial"]
theorem WeilDivisor.exists_weilDivisorialSubsheaf_sheaf [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (D : WeilDivisor X) :
    ∃ L : WeilDivisorialSubsheaf X, L.toRationalFunctionsSubmodule = D.sheaf := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  obtain ⟨G, hG⟩ := exists_isWShGroup π hd
  choose M hM using fun Γ => WeilDivisorPrime.exists_weilDivisorialSubsheaf_isGeneratedAt π hd Γ
  refine ⟨∏ Γ ∈ D.support, M Γ ^ (-D Γ), ?_⟩
  set N := ∏ Γ ∈ D.support, M Γ ^ (-D Γ)
  have hN : ∀ η : X, Order.coheight η ≤ 1 →
      N.IsGeneratedAt η (∏ Γ ∈ D.support, Γ.localGenerator η ^ (-D Γ)) :=
    fun η hη => hG.isGeneratedAt_prod _ _ hη _ fun Γ _ => hG.isGeneratedAt_zpow hη (hM Γ η hη) _
  have hcond : ∀ η : X, Order.coheight η ≤ 1 → ∀ g, D.StalkCondition η g ↔ g ∈ N.stalkSet η := by
    intro η hη g
    rw [hN η hη]
    by_cases h : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
    · obtain ⟨Γ, rfl⟩ := h
      rw [D.stalkCondition_genericPoint_iff Γ, Finset.prod_eq_single Γ
        (fun Γ' _ hne => by
          rw [Γ'.localGenerator_of_ne fun e => hne (WeilDivisorPrime.genericPoint_injective e),
            one_zpow])
        (fun hΓ => by rw [Finsupp.notMem_support_iff.mp hΓ]; simp), Γ.localGenerator_self]
    · push Not at h
      rw [D.stalkCondition_iff_of_forall_ne hη h, Finset.prod_eq_one fun Γ _ => by
        rw [Γ.localGenerator_of_ne (h Γ), one_zpow]]
      simp
  have hsat : N.toRationalFunctionsSubmodule = N.saturation := N.isSaturated
  rw [hsat]
  ext V s
  rw [mem_saturation_iff]
  change _ ↔ ∀ (x : X) (hx : x ∈ V), D.StalkCondition x _
  constructor
  · intro h x hx
    by_cases hc : Order.coheight x ≤ 1
    · exact (hcond x hc _).mpr (h x hx hc)
    · exact D.stalkCondition_of_not_coheight_le_one hc _
  · intro h η hη hc
    exact (hcond η hc _).mp (h η hη)

/-! ### Stalks of `𝒪(D)` at points of codimension at most one -/

namespace WeilDivisor

/-- At a point where every coefficient of `D` vanishes, the germs of `𝒪_X` satisfy the stalk
condition of `𝒪(D)`. -/
private theorem stalkCondition_of_mem_range (D : WeilDivisor X) {x : X}
    (hD : ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint = x → D Γ = 0)
    {g : (rationalFunctionsPresheaf X).stalk x}
    (hg : g ∈ Set.range (structureStalkToRationalFunctionsStalk X x).hom) :
    D.StalkCondition x g := by
  obtain ⟨a, rfl⟩ := hg
  exact ⟨fun Γ h t _ => ⟨a, by rw [hD Γ h]; simp⟩, fun _ _ => ⟨a, rfl⟩⟩

/-- At a point of codimension `≤ 1` where every coefficient of `D` vanishes, the stalk condition
of `𝒪(D)` says that the germ lies in `𝒪_{X,x}`. -/
private theorem mem_range_of_stalkCondition (D : WeilDivisor X) {x : X}
    (hx : Order.coheight x ≤ 1)
    (hD : ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint = x → D Γ = 0)
    {g : (rationalFunctionsPresheaf X).stalk x} (h : D.StalkCondition x g) :
    g ∈ Set.range (structureStalkToRationalFunctionsStalk X x).hom := by
  by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = x
  · obtain ⟨Γ, rfl⟩ := hΓ
    obtain ⟨a, ha⟩ := h.1 Γ rfl Γ.uniformizer Γ.irreducible_uniformizer
    refine ⟨a, ?_⟩
    rw [hD Γ rfl] at ha
    simpa using ha.symm
  · simp only [not_exists] at hΓ
    exact h.2 hx hΓ

/-- A point `η` of codimension `≤ 1` has an open neighbourhood containing the generic point of no
prime divisor `Γ ≠ η` in the support of `D`. -/
private theorem exists_nhds_coeff_eq_zero (D : WeilDivisor X) {η : X}
    (hη : Order.coheight η ≤ 1) :
    ∃ W : X.Opens, η ∈ W ∧ ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint ∈ W →
      Γ.1.genericPoint ≠ η → D Γ = 0 := by
  classical
  let S := D.support.filter fun Γ => Γ.1.genericPoint ≠ η
  let C : Set X := ⋃ Γ ∈ S, closure {Γ.1.genericPoint}
  have hC : IsClosed C := isClosed_biUnion_finset fun _ _ => isClosed_closure
  refine ⟨⟨Cᶜ, hC.isOpen_compl⟩, ?_, ?_⟩
  · intro hmem
    obtain ⟨Γ, hΓ, hηΓ⟩ := Set.mem_iUnion₂.mp hmem
    have hne : Γ.1.genericPoint ≠ η := (Finset.mem_filter.mp hΓ).2
    have hsp : Γ.1.genericPoint ⤳ η := specializes_iff_mem_closure.mpr hηΓ
    have hlt : η < Γ.1.genericPoint := lt_iff_le_not_ge.mpr
      ⟨Scheme.le_iff_specializes.mpr hsp,
        fun h => hne (hsp.antisymm (Scheme.le_iff_specializes.mp h)).eq⟩
    have h1 := MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1
    have h2 := Order.coheight_strictAnti hlt (by rw [h1]; exact ENat.natCast_lt_top 1)
    rw [h1] at h2
    exact absurd hη (not_le.mpr h2)
  · intro Γ hΓ hne
    by_contra h0
    exact hΓ (Set.mem_iUnion₂.mpr ⟨Γ, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h0, hne⟩,
      subset_closure rfl⟩)

/-- A germ of `𝒪_{X,η}` satisfying the stalk condition of `𝒪(D)` at a point `η` of codimension
`≤ 1` lies in the stalk `𝒪(D)_η`. -/
private theorem mem_stalkSet_sheaf_of_stalkCondition (D : WeilDivisor X) {η : X}
    (hη : Order.coheight η ≤ 1) (r : X.presheaf.stalk η)
    (hr : D.StalkCondition η ((structureStalkToRationalFunctionsStalk X η).hom r)) :
    (structureStalkToRationalFunctionsStalk X η).hom r ∈ D.sheaf.stalkSet η := by
  obtain ⟨V, hV, ρ, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨W, hW, hD⟩ := exists_nhds_coeff_eq_zero D hη
  let U := V ⊓ W
  have hU : η ∈ U := ⟨hV, hW⟩
  let ρU : Γ(X, U) := X.presheaf.map (homOfLE inf_le_left : U ⟶ V).op ρ
  have hgerm : ∀ (x : X) (hx : x ∈ U), (rationalFunctionsPresheaf X).germ U x hx
      ((toRationalFunctionsPresheaf X).app (op U) ρU) =
      (structureStalkToRationalFunctionsStalk X x).hom (X.presheaf.germ U x hx ρU) :=
    fun x hx =>
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (toRationalFunctionsPresheaf X) ρU).symm
  have hηr : X.presheaf.germ U η hU ρU = X.presheaf.germ V η hV ρ :=
    X.presheaf.germ_res_apply _ η hU ρ
  refine ⟨U, hU, (toRationalFunctionsPresheaf X).app (op U) ρU, fun x hx => ?_, by
    rw [hgerm, hηr]⟩
  rw [hgerm]
  by_cases hxη : x = η
  · subst hxη
    rw [hηr]
    exact hr
  · refine stalkCondition_of_mem_range D (fun Γ hΓ => hD Γ ?_ ?_) ⟨_, rfl⟩
    · rw [hΓ]; exact hx.2
    · rw [hΓ]; exact hxη

/-- If an `𝒪_X`-submodule of `K(X)` has stalk `u 𝒪_{X,η}` at `η`, contained in `c 𝒪_{X,η}` and
containing `c`, then its stalk is `c 𝒪_{X,η}`. -/
private theorem stalkSet_eq_range_of_mem {F : RationalFunctionsSubmodule X} {η : X}
    {u c : (rationalFunctionsPresheaf X).stalk η}
    (hu : F.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      u * (structureStalkToRationalFunctionsStalk X η).hom a)
    (hsub : F.stalkSet η ⊆ Set.range fun a : X.presheaf.stalk η =>
      c * (structureStalkToRationalFunctionsStalk X η).hom a)
    (hc : c ∈ F.stalkSet η) :
    F.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      c * (structureStalkToRationalFunctionsStalk X η).hom a := by
  refine hsub.antisymm ?_
  rintro _ ⟨a, rfl⟩
  rw [hu] at hc ⊢
  obtain ⟨b, rfl⟩ := hc
  exact ⟨b * a, by simp only [map_mul, mul_assoc]⟩

/-- At a point `η` of codimension `≤ 1` where every coefficient of `D` vanishes,
`𝒪(D)_η = 𝒪_{X,η}`. -/
theorem stalkSet_sheaf_of_coeff_eq_zero {L : WeilDivisorialSubsheaf X} {D : WeilDivisor X}
    (hL : L.toRationalFunctionsSubmodule = D.sheaf) {η : X} (hη : Order.coheight η ≤ 1)
    (hD : ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η → D Γ = 0) :
    D.sheaf.stalkSet η = Set.range fun a : X.presheaf.stalk η =>
      ((1 : ((rationalFunctionsPresheaf X).stalk η)ˣ) : (rationalFunctionsPresheaf X).stalk η) *
        (structureStalkToRationalFunctionsStalk X η).hom a := by
  obtain ⟨f, hf⟩ := L.principal_codim_one η hη
  rw [hL] at hf
  refine stalkSet_eq_range_of_mem hf ?_ ?_
  · rintro _ ⟨V, hV, s, hs, rfl⟩
    obtain ⟨a, ha⟩ := mem_range_of_stalkCondition D hη hD (hs η hV)
    exact ⟨a, by simpa using ha⟩
  · simpa using mem_stalkSet_sheaf_of_stalkCondition D hη 1
      (stalkCondition_of_mem_range D hD ⟨1, rfl⟩)

/-- `𝒪(D)_Γ = t_Γ^{-n_Γ} 𝒪_{X,Γ}` when `n_Γ ≤ 0`. -/
private theorem stalkSet_sheaf_genericPoint_of_nonpos [IsReduced X] [IsNoetherian X]
    {L : WeilDivisorialSubsheaf X} {D : WeilDivisor X}
    (hL : L.toRationalFunctionsSubmodule = D.sheaf)
    (Γ : WeilDivisorPrime X) (hn : D Γ ≤ 0) :
    D.sheaf.stalkSet Γ.1.genericPoint = Set.range fun a : X.presheaf.stalk Γ.1.genericPoint =>
      ((Γ.uniformizerUnit ^ (-D Γ) : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
        (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
        (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom a := by
  have hη := (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le
  obtain ⟨f, hf⟩ := L.principal_codim_one _ hη
  rw [hL] at hf
  refine stalkSet_eq_range_of_mem hf ?_ ?_
  · rintro _ ⟨V, hV, s, hs, rfl⟩
    exact (stalkCondition_genericPoint_iff D Γ _).mp (hs _ hV)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -D Γ = m := ⟨(-D Γ).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hval : ((Γ.uniformizerUnit ^ (-D Γ) :
        ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
          (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) =
        (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom (Γ.uniformizer ^ m) := by
      rw [hm, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, Γ.val_uniformizerUnit]
    rw [hval]
    refine mem_stalkSet_sheaf_of_stalkCondition D hη _ ?_
    rw [stalkCondition_genericPoint_iff, ← hval]
    exact ⟨1, by simp⟩

/-- `𝒪(D)_Γ = t_Γ^{-n_Γ} 𝒪_{X,Γ}` when `n_Γ > 0`. -/
private theorem stalkSet_sheaf_genericPoint_of_pos [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    {L : WeilDivisorialSubsheaf X} {D : WeilDivisor X}
    (hL : L.toRationalFunctionsSubmodule = D.sheaf) (Γ : WeilDivisorPrime X) (hn : 0 < D Γ) :
    D.sheaf.stalkSet Γ.1.genericPoint = Set.range fun a : X.presheaf.stalk Γ.1.genericPoint =>
      ((Γ.uniformizerUnit ^ (-D Γ) : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
        (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
        (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom a := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have hη := (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le
  obtain ⟨f, hf⟩ := L.principal_codim_one _ hη
  rw [hL] at hf
  refine stalkSet_eq_range_of_mem hf ?_ ?_
  · rintro _ ⟨V, hV, s, hs, rfl⟩
    exact (stalkCondition_genericPoint_iff D Γ _).mp (hs _ hV)
  obtain ⟨L', hL'⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf π hd (-D)
  have hΓ' := stalkSet_sheaf_genericPoint_of_nonpos hL' Γ (by simp only [Finsupp.neg_apply]; omega)
  rw [← hL'] at hΓ'
  have hinv := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L' L' _ hη _ _ hΓ' hΓ').2.1
  rw [← zpow_neg, Finsupp.neg_apply, neg_neg] at hinv
  have hmem : ((Γ.uniformizerUnit ^ (-D Γ) :
      ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
        (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) ∈
        L'.inv.stalkSet Γ.1.genericPoint := by
    rw [hinv]; exact ⟨1, by simp⟩
  obtain ⟨V, hV, x, hx, hxg⟩ := hmem
  obtain ⟨W, hW, hD⟩ := exists_nhds_coeff_eq_zero D hη
  let U := V ⊓ W
  have hU : Γ.1.genericPoint ∈ U := ⟨hV, hW⟩
  let i : U ⟶ V := homOfLE inf_le_left
  have hxU : (rationalFunctionsPresheaf X).map i.op x ∈ L'.inv.sections U := L'.inv.map_mem i hx
  refine ⟨U, hU, _, fun z hz => ?_, by rw [TopCat.Presheaf.germ_res_apply _ i _ hU x, hxg]⟩
  have hzS : (rationalFunctionsPresheaf X).germ U z hz ((rationalFunctionsPresheaf X).map i.op x) ∈
      L'.inv.stalkSet z := ⟨U, hz, _, hxU, rfl⟩
  by_cases hzη : z = Γ.1.genericPoint
  · subst hzη
    rw [hinv] at hzS
    exact (stalkCondition_genericPoint_iff D Γ _).mpr hzS
  by_cases hc : Order.coheight z ≤ 1
  · have hD0 : ∀ Γ' : WeilDivisorPrime X, Γ'.1.genericPoint = z → D Γ' = 0 := fun Γ' h =>
      hD Γ' (by rw [h]; exact hz.2) (by rw [h]; exact hzη)
    have h1 := stalkSet_sheaf_of_coeff_eq_zero hL' hc fun Γ' h => by
      rw [Finsupp.neg_apply, hD0 Γ' h, neg_zero]
    rw [← hL'] at h1
    have hinv' := (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L' L' z hc 1 1 h1 h1).2.1
    rw [hinv'] at hzS
    refine stalkCondition_of_mem_range D hD0 ?_
    obtain ⟨a, ha⟩ := hzS
    exact ⟨a, by simpa using ha⟩
  · exact stalkCondition_of_not_coheight_le_one D hc _

/-- **The stalk of `𝒪(D)` at a prime divisor.** `𝒪(D)_Γ = t_Γ^{-n_Γ} 𝒪_{X,Γ}`. -/
theorem stalkSet_sheaf_genericPoint [IsReduced X] [IsNoetherian X]
    (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (D : WeilDivisor X)
    (Γ : WeilDivisorPrime X) :
    D.sheaf.stalkSet Γ.1.genericPoint = Set.range fun a : X.presheaf.stalk Γ.1.genericPoint =>
      ((Γ.uniformizerUnit ^ (-D Γ) : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
        (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
        (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom a := by
  obtain ⟨L, hL⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf π hd D
  rcases le_or_gt (D Γ) 0 with hn | hn
  · exact stalkSet_sheaf_genericPoint_of_nonpos hL Γ hn
  · exact stalkSet_sheaf_genericPoint_of_pos π hd hL Γ hn

end WeilDivisor

/-! ### `D ↦ 𝒪(D)` is an injective group homomorphism (FA 16.2.2) -/

/-- In a group structure on `WSh(X)`, `𝒪(D + D') = 𝒪(D) · 𝒪(D')`. -/
theorem WeilDivisorialSubsheaf.eq_mul_of_eq_sheaf_add
    [IsReduced X] [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (G : CommGroup (WeilDivisorialSubsheaf X)) (hG : IsWShGroup G)
    {L L' L'' : WeilDivisorialSubsheaf X} {D D' : WeilDivisor X}
    (hL : L.toRationalFunctionsSubmodule = D.sheaf)
    (hL' : L'.toRationalFunctionsSubmodule = D'.sheaf)
    (hL'' : L''.toRationalFunctionsSubmodule = (D + D').sheaf) :
    letI := G
    L'' = L * L' := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  let := G
  apply WeilDivisorialSubsheaf.ext'
  rw [show (L * L').toRationalFunctionsSubmodule = L.mul L' from hG.mul_eq _ _]
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq L''.isSaturated
    (isSaturated_saturation _) fun η hη => ?_
  rw [hL'']
  by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
  · obtain ⟨Γ, rfl⟩ := hΓ
    have h1 := WeilDivisor.stalkSet_sheaf_genericPoint π hd D Γ
    have h2 := WeilDivisor.stalkSet_sheaf_genericPoint π hd D' Γ
    rw [← hL] at h1
    rw [← hL'] at h2
    rw [WeilDivisor.stalkSet_sheaf_genericPoint π hd (D + D') Γ,
      (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L' _ hη _ _ h1 h2).1,
      ← zpow_add, Finsupp.add_apply, neg_add]
  · simp only [not_exists] at hΓ
    have h0 : ∀ E : WeilDivisor X, ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η → E Γ = 0 :=
      fun E Γ h => absurd h (hΓ Γ)
    have h1 := WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL hη (h0 D)
    have h2 := WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL' hη (h0 D')
    rw [← hL] at h1
    rw [← hL'] at h2
    rw [WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL'' hη (h0 _),
      (WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L' _ hη _ _ h1 h2).1, mul_one]

/-- If `𝒪(D)` is the unit of `WSh(X)`, then `D = 0`. -/
theorem WeilDivisor.eq_zero_of_sheaf_eq_saturation_unit
    [IsReduced X] [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    {L : WeilDivisorialSubsheaf X} {D : WeilDivisor X}
    (hL : L.toRationalFunctionsSubmodule = D.sheaf)
    (h1 : L.toRationalFunctionsSubmodule = (RationalFunctionsSubmodule.unit X).saturation) :
    D = 0 := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  ext Γ
  have hη := (MMP.Mori.PrimeDivisor.coheight_genericPoint Γ.1).le
  have hS := WeilDivisor.stalkSet_sheaf_genericPoint π hd D Γ
  rw [← hL, h1] at hS
  obtain ⟨f0, hf0⟩ := L.principal_codim_one _ hη
  rw [(WeilDivisorialSubsheaf.stalkSet_mul_inv_unit L L _ hη f0 f0 hf0 hf0).2.2] at hS
  set c := Γ.uniformizerUnit ^ (-D Γ) with hc
  have hinj := wshC_structure_stalk_injective (X := X) Γ.1.genericPoint
  have hcmem : (c : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) ∈
      Set.range (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom := by
    rw [hS]; exact ⟨1, by simp⟩
  have h1mem : (1 : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) ∈
      Set.range fun a : X.presheaf.stalk Γ.1.genericPoint =>
        (c : (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) *
          (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom a := by
    rw [← hS]; exact ⟨1, map_one _⟩
  obtain ⟨p, hp⟩ := hcmem
  obtain ⟨q, hq⟩ := h1mem
  have hq' : (c * (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom q :
      (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) = 1 := hq
  have hpq : p * q = 1 := hinj (by rw [map_mul, hp, hq', map_one])
  rw [Finsupp.zero_apply]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -D Γ = m := ⟨(-D Γ).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hpm : Γ.uniformizer ^ m = p := hinj (by
      rw [hp, hc, hm, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, Γ.val_uniformizerUnit])
    have hu : IsUnit (Γ.uniformizer ^ m) := hpm ▸ IsUnit.of_mul_eq_one q hpq
    exact Γ.irreducible_uniformizer.not_isUnit ((isUnit_pow_iff (by omega)).mp hu)
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, D Γ = m := ⟨(D Γ).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hqm : Γ.uniformizer ^ m = q := hinj (by
      have e : (structureStalkToRationalFunctionsStalk X Γ.1.genericPoint).hom q =
          ((c⁻¹ : ((rationalFunctionsPresheaf X).stalk Γ.1.genericPoint)ˣ) :
            (rationalFunctionsPresheaf X).stalk Γ.1.genericPoint) := by
        rw [← Units.inv_mul_cancel_left c ((structureStalkToRationalFunctionsStalk X
          Γ.1.genericPoint).hom q), hq', mul_one]
      rw [e, hc, ← zpow_neg, neg_neg, hm, zpow_natCast, Units.val_pow_eq_pow_val, map_pow,
        Γ.val_uniformizerUnit])
    have hu : IsUnit (Γ.uniformizer ^ m) :=
      hqm ▸ IsUnit.of_mul_eq_one p (by rw [mul_comm]; exact hpq)
    exact Γ.irreducible_uniformizer.not_isUnit ((isUnit_pow_iff (by omega)).mp hu)

/-- **FA Def. 16.2.2, "a natural injective group homomorphism".** Let `X` be a reduced,
pure-dimensional scheme of finite type over `k`, and `G` the group structure of `WSh(X)`
(`MMP.Flips.exists_isWShGroup`). Then `D ↦ 𝒪(D)` is an injective group homomorphism
`WDiv(X) → WSh(X)`. -/
@[mmp "lem_fa16a_weil_divisor_to_wsh_injective_hom"]
theorem WeilDivisor.exists_injective_hom [IsReduced X] [IsNoetherian X] (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (G : CommGroup (WeilDivisorialSubsheaf X)) (hG : IsWShGroup G) :
    letI := G
    ∃ f : Multiplicative (WeilDivisor X) →* WeilDivisorialSubsheaf X, Function.Injective f ∧
      ∀ D : WeilDivisor X, (f (Multiplicative.ofAdd D)).toRationalFunctionsSubmodule = D.sheaf := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  let := G
  choose F hF using fun D : WeilDivisor X => WeilDivisor.exists_weilDivisorialSubsheaf_sheaf π hd D
  have hmul : ∀ D D' : WeilDivisor X, F (D + D') = F D * F D' := fun D D' =>
    WeilDivisorialSubsheaf.eq_mul_of_eq_sheaf_add π hd G hG (hF D) (hF D') (hF (D + D'))
  let f : Multiplicative (WeilDivisor X) →* WeilDivisorialSubsheaf X :=
    MonoidHom.mk' (fun D => F (Multiplicative.toAdd D)) fun a b => by
      rw [toAdd_mul]; exact hmul _ _
  refine ⟨f, (injective_iff_map_eq_one f).mpr fun a ha => ?_, hF⟩
  set D := Multiplicative.toAdd a with hDa
  have ha' : F D = 1 := ha
  have h1 : (F D).toRationalFunctionsSubmodule =
      (RationalFunctionsSubmodule.unit X).saturation := by
    rw [ha']; exact hG.one_eq
  suffices hD : D = 0 by
    rw [← ofAdd_toAdd a, ← hDa, hD, ofAdd_zero]
  exact WeilDivisor.eq_zero_of_sheaf_eq_saturation_unit π hd (hF D) h1

end WeilDivisor

/-! ### Regular-sequence quotients of regular local rings -/

section RegularSequence

open RingTheory.Sequence Pointwise IsLocalRing

/-- If `l` is a regular sequence on `R/aR` viewed as an `R`-module, its image in `R ⧸ (a)` is a
regular sequence on the ring `R ⧸ (a)`. -/
theorem isRegular_quotient_span_singleton_map {R : Type u} [CommRing R] (a : R) (l : List R)
    (h : IsRegular (QuotSMulTop a R) l) :
    IsRegular (R ⧸ Ideal.span {a}) (l.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
  have hs : a • (⊤ : Submodule R R) = Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e := (Submodule.quotEquivOfEq _ _ hs).toAddEquiv
  refine (e.isRegular_congr (List.forall₂_map_right_iff.mpr <|
    List.forall₂_same.mpr fun r _ x => ?_)).mp h
  change Submodule.quotEquivOfEq _ _ hs (r • x) = _
  rw [LinearEquiv.map_smul, Algebra.smul_def]
  rfl

/-- The quotient of a local ring by a proper ideal is local. -/
theorem isLocalRing_quotient_of_ne_top {R : Type u} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (hI : I ≠ ⊤) : IsLocalRing (R ⧸ I) :=
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- The quotient of a Noetherian Gorenstein local ring by a regular sequence of length `n` is a
Gorenstein local ring. -/
theorem exists_isLocalRing_isGorensteinLocalRing_quotient_ofList (n : ℕ) :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Dualizing.IsGorensteinLocalRing R → ∀ (g : List R), g.length = n → IsRegular R g →
    ∃ _ : IsLocalRing (R ⧸ Ideal.ofList g),
      Dualizing.IsGorensteinLocalRing (R ⧸ Ideal.ofList g) := by
  induction n with
  | zero =>
    intro R _ _ _ hR g hn hg
    have hne : Ideal.ofList g ≠ ⊤ := fun h => hg.top_ne_smul (by simp [h])
    have := isLocalRing_quotient_of_ne_top _ hne
    refine ⟨this, ?_⟩
    obtain rfl := List.length_eq_zero_iff.mp hn
    have e : R ⧸ Ideal.ofList ([] : List R) ≃+* R :=
      (Ideal.quotEquivOfEq Ideal.ofList_nil).trans (RingEquiv.quotientBot R)
    exact (Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff e).mpr hR
  | succ n ih =>
    intro R _ _ _ hR g hn hg
    have hne : Ideal.ofList g ≠ ⊤ := fun h => hg.top_ne_smul (by simp [h])
    have := isLocalRing_quotient_of_ne_top _ hne
    refine ⟨this, ?_⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_length_eq_add_one hn
    rw [isRegular_cons_iff] at hg
    obtain ⟨ha, hl⟩ := hg
    have ham : a ∈ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hne (Ideal.subset_span (List.mem_cons_self ..))
    have hspan : Ideal.span {a} ≠ ⊤ := fun h =>
      (mem_maximalIdeal a).mp ham (Ideal.span_singleton_eq_top.mp h)
    have := isLocalRing_quotient_of_ne_top _ hspan
    have hR' : Dualizing.IsGorensteinLocalRing (R ⧸ Ideal.span {a}) :=
      (Dualizing.isGorensteinLocalRing_quotient_span_singleton_iff R a ham
        (mem_nonZeroDivisors_iff_right.mpr fun x hx =>
          ha (by simpa [smul_eq_mul, mul_comm] using hx))).mp hR
    obtain ⟨_, hG⟩ := ih hR' (l.map (Ideal.Quotient.mk _)) (by simpa using hn)
      (isRegular_quotient_span_singleton_map a l hl)
    have e : (R ⧸ Ideal.span {a}) ⧸ Ideal.ofList (l.map (Ideal.Quotient.mk (Ideal.span {a}))) ≃+*
        R ⧸ Ideal.ofList (a :: l) :=
      (Ideal.quotEquivOfEq (Ideal.map_ofList _ l).symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans
          (Ideal.quotEquivOfEq (Ideal.ofList_cons a l).symm))
    exact (Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff e).mp hG

/-- The spectrum of a Noetherian Cohen–Macaulay local ring satisfies `S₂` (see Stacks 00NB). -/
theorem satisfiesS2_spec_of_isCohenMacaulayLocalRing {B : CommRingCat.{u}}
    [IsNoetherianRing B] [IsLocalRing B] (hB : IsCohenMacaulayLocalRing B) :
    SatisfiesS2 (Spec B) := by
  intro x
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B x
  have : IsNoetherianRing ((Spec B).presheaf.stalk x) :=
    IsLocalization.isNoetherianRing x.asIdeal.primeCompl _ inferInstance
  have hS : IsCohenMacaulayLocalRing ((Spec B).presheaf.stalk x) :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mpr
      (((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B).mp hB).of_isLocalization_atPrime
        x.asIdeal _)
  obtain ⟨ss, hmem, hreg, hlen⟩ := exists_isRegular_length_eq_depth_of_cohenMacaulay hS
  refine ⟨ss, hmem, hreg, min_le_of_right_le (le_of_eq ?_)⟩
  have hsd := Module.supportDim_self_eq_ringKrullDim ((Spec B).presheaf.stalk x)
  rw [Module.supportDim] at hsd
  unfold IsCohenMacaulayLocalRing IsCohenMacaulayModule at hS
  rw [← hsd, ← hS, ← hlen]
  rfl

/-- **A regular-sequence quotient of a regular local ring is Gorenstein.** Let `R` be a regular
local ring and `g₁, …, g_c ∈ R` a regular sequence. Then `R/(g₁, …, g_c)` is a Gorenstein (in
particular Cohen–Macaulay, hence `S₂`) local ring. -/
@[mmp "lem_mmp_foundation_regular_sequence_quotient_gorenstein"]
theorem isGorensteinLocalRing_quotient_ofList {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (g : List R) (hg : RingTheory.Sequence.IsRegular R g) :
    ∃ (_ : IsLocalRing (R ⧸ Ideal.ofList g)) (_ : IsNoetherianRing (R ⧸ Ideal.ofList g)),
      Dualizing.IsGorensteinLocalRing (R ⧸ Ideal.ofList g) ∧
        IsCohenMacaulayLocalRing (R ⧸ Ideal.ofList g) ∧
        SatisfiesS2 (Spec (.of (R ⧸ Ideal.ofList g))) := by
  obtain ⟨hloc, hG⟩ := exists_isLocalRing_isGorensteinLocalRing_quotient_ofList g.length
    (Dualizing.IsRegularLocalRing.isGorensteinLocalRing R) g rfl hg
  have hCM := Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing _ hG
  exact ⟨hloc, inferInstance, hG, hCM,
    satisfiesS2_spec_of_isCohenMacaulayLocalRing (B := .of (R ⧸ Ideal.ofList g)) hCM⟩

end RegularSequence

/-! ### The Cohen–Macaulay locus -/

/-- **The Cohen–Macaulay locus of a finite-type scheme over a field is open.** Let `X` be a
scheme of finite type over a field. Then the set of points `x` with `𝒪_{X,x}` not
Cohen–Macaulay is closed in `X`. -/
@[mmp "lem_mmp_foundation_finite_type_cohen_macaulay_locus_open"]
theorem isClosed_setOf_not_isCohenMacaulayLocalRing {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] :
    IsClosed {x : X | ¬ IsCohenMacaulayLocalRing (X.presheaf.stalk x)} := by
  have hset : {x : X | ¬ IsCohenMacaulayLocalRing (X.presheaf.stalk x)} =
      {x : X | Scheme.Hom.IsCohenMacaulayAt π (fun y =>
        isLocallyNoetherian_fiber_of_locallyOfFinitePresentation π y) x}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Scheme.Hom.IsCohenMacaulayAt]
    have := isIso_fiberι_of_isIso_fromSpecResidueField π (π x)
      (isIso_fromSpecResidueField_of_field k (π x))
    have hcm := localCM_iff_of_isIso_stalkMap (π.fiberι (π x)) (π.asFiber x)
      (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation π (π x)) inferInstance
    rw [Scheme.Hom.fiberι_asFiber] at hcm
    rw [hcm]
    exact ⟨fun h h' => h h'.2, fun h h' => h ⟨Flat.stalkMap π x, h'⟩⟩
  rw [hset]
  exact (isOpen_setOf_isCohenMacaulayAt π).isClosed_compl

end MMP.Flips
