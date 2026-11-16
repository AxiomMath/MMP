/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.ChangeOfField
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Divisor.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Connected
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialize.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.TensorPower

/-!
# Serre duality on proper Cohen--Macaulay schemes, and two connectedness consequences

Let `X` be a proper Cohen--Macaulay scheme of pure dimension `d` over a field `k`, with structure
morphism `f : X ⟶ Spec k` and dualizing sheaf `ω_X = H^{-d}(f^× 𝒪_{Spec k})`. Serre duality says
that for every quasi-coherent (in particular every coherent) `𝒪_X`-module `𝒢` and every integer
`i` there is a `k`-linear isomorphism `Ext^i_X(𝒢, ω_X) ≅ H^{d-i}(X, 𝒢)^∨`. It is [Stacks, Tag
0FVZ], part (3), for `K = 𝒢[0]` in degree `i - d`, read through `ω_X[d][i - d] = ω_X[i]`.

Two geometric statements whose proofs rest on it are stated here:

* the support of an effective ample Cartier divisor on a connected projective Cohen--Macaulay
  scheme of pure dimension at least two is connected;
* for a proper birational morphism `h : X → X'` of normal surfaces with `h_* 𝒪_X = 𝒪_{X'}`, a
  section `s` of a line bundle `L` some power of which is pulled back from `X'` vanishes at one
  closed point of a fibre of `h` only if it vanishes at all of them (Kollár et al., FA 8.6).

## Main results

* `MMP.Mori.nonempty_zExt_dualizingModule_linearEquiv_dual`: Serre duality
  `Ext^i_X(𝒢, ω_X) ≅ H^{d-i}(X, 𝒢)^∨`, for every `i : ℤ`.
* `MMP.Mori.nonempty_zExt_linearEquiv_of_equidimensional`: the same, for `X` equidimensional of
  dimension `d` and `𝒢` quasi-coherent.
* `MMP.Mori.isConnected_support_of_two_le_depth`: on a connected scheme proper over `k` with
  depth at least two at closed points, `Supp A` is connected for `A` effective and ample.
* `MMP.Mori.isConnected_support_of_isAmple_divisorSheaf`: the support of an effective ample
  Cartier divisor on a connected projective Cohen--Macaulay scheme of pure dimension `≥ 2` is
  connected.
* `MMP.Mori.mem_nonvanishingLocus_of_map_eq`: `s(c) ≠ 0` and `h(x) = h(c)` imply `s(x) ≠ 0`.

## Implementation notes

* `Ext^i_X(𝒢, ω_X)` is `CategoryTheory.Abelian.zExt 𝒢 ω_X i`, the `ℤ`-graded Ext of the derived
  category, and `H^j(X, 𝒢)` for `j : ℤ` is the hypercohomology
  `Stacks.Duality.derivedCohomologyOverField f 𝒢[0] j`. With integer indices the statement
  covers `i > d`, where `H^{d-i}(X, 𝒢) = 0`, and `i < 0`, where `Ext^i = 0`.
* The dualizing sheaf of the proper scheme `X` is `H^{-d}(f^× 𝒪_{Spec k})`
  (`Stacks.Duality.dualizingModuleOverField f d`); `ω` is any module isomorphic to it.
* *Pure dimension `d`* is: every irreducible component has dimension `d`. On the empty scheme
  both sides of the duality vanish.
* An effective Cartier divisor is an ideal sheaf `A` with
  `Stacks.Divisors.IsEffectiveCartierDivisor A`; it is ample when `𝒪_X(A)`
  (`Stacks.Divisors.divisorSheaf A`) is, and `Supp A` is the zero locus `A.support`.
  *Projective over `k`* is `AlgebraicGeometry.IsProjective f`.
* The value `s(x) ∈ L ⊗ κ(x)` is nonzero exactly when the germ of `s` at `x` is not in
  `𝔪_x L_x`, which is membership of `x` in `Stacks.Ample.nonvanishingLocus L s`. `L^{⊗j}` is
  `Stacks.SheafOfModules.Invertible.tensorPower L j`, and `h_* 𝒪_X = 𝒪_{X'}` is that `h^♯` is an
  isomorphism on every open of `X'`.

## References

* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 8.6
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

-- The Stacks results used here are stated at the locally small models of `D(R)`, `D(𝒪_X)` and
-- `D(SheafOfModules R)`, which Stacks scopes
-- (`StacksFrontier.Homology.DerivedCategory.LocallySmall`).
open scoped Stacks.SmallDerivedModel

universe u

namespace MMP.Mori

/-- A nonempty space all of whose irreducible components have dimension `d` is equidimensional
of dimension `d`. -/
theorem equidimensional_and_topologicalKrullDim_eq_of_irreducibleComponents {T : Type*}
    [TopologicalSpace T] [Nonempty T] {d : ℕ}
    (hpure : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = d) :
    TopologicalSpace.Equidimensional T ∧ topologicalKrullDim T = d := by
  refine ⟨fun Z hZ W hW => (hpure Z hZ).trans (hpure W hW).symm, ?_⟩
  obtain ⟨x⟩ := ‹Nonempty T›
  obtain ⟨Z, hZ, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible ({x} : Set T)
    isIrreducible_singleton
  rw [AlgebraicGeometry.topologicalKrullDim_eq_iSup_irreducibleComponents T]
  exact le_antisymm (iSup₂_le fun W hW => (hpure W hW).le) (le_iSup₂_of_le Z hZ (hpure Z hZ).ge)

section SerreDuality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **Serre duality on an equidimensional proper Cohen--Macaulay scheme.** If `X` is proper over
`k`, Cohen--Macaulay and equidimensional of dimension `d`, and `ω ≅ H^{-d}(f^× 𝒪_{Spec k})`, then
for every quasi-coherent `𝒢` and every `i : ℤ`, `Ext^i_X(𝒢, ω) ≅ H^{d-i}(X, 𝒢)^∨` over `k`. -/
theorem nonempty_zExt_linearEquiv_of_equidimensional (hCM : IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (ω : X.Modules)
    (hω : Nonempty (ω ≅ Stacks.Duality.dualizingModuleOverField f d))
    (G : X.Modules) [G.IsQuasicoherent] (i : ℤ) :
    letI := Scheme.linearOver f
    Nonempty (Abelian.zExt G ω i ≃ₗ[k]
      (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) (d - i) →ₗ[k] k)) := by
  let := Scheme.linearOver f
  obtain ⟨e⟩ := hω
  have hM : Stacks.Duality.dualizingModuleOverField f d =
      Stacks.Duality.relativeDualizingModule f
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k))) := by
    unfold Stacks.Duality.dualizingModuleOverField Stacks.Duality.relativeDualizingModule
    rw [Stacks.Duality.neg_toNat_getD_topologicalKrullDim_eq hd]
    rfl
  let e' := (DerivedCategory.singleFunctor X.Modules 0).mapIso (e ≪≫ eqToIso hM)
  rw [show (d : ℤ) - i = -(i - d) by omega]
  refine ⟨StacksDraft.DerivedHom.HomModuleBaseChange.postcompLinearEquiv k _
      ((shiftFunctor (DerivedCategory X.Modules) i).mapIso e' ≪≫
        (shiftFunctorAdd' (DerivedCategory X.Modules) (d : ℤ) (i - d) i (by omega)).app _) ≪≫ₗ
    Stacks.Duality.dualityEquivShiftOfIsProper f hCM hequi d hd
      (Stacks.Duality.singleQuasiCoherentDegreeZero G) (i - d)⟩

/-- **Serre duality on a proper Cohen--Macaulay scheme.** Let `X` be a proper Cohen--Macaulay
scheme of pure dimension `d` over a field `k`, with dualizing sheaf `ω ≅ H^{-d}(f^× 𝒪_{Spec k})`,
and `𝒢` a coherent `𝒪_X`-module. For every `i` there is an isomorphism of `k`-vector spaces
`Ext^i_X(𝒢, ω) ≅ H^{d-i}(X, 𝒢)^∨`. -/
@[mmp "lem_mmp_foundation_proper_cohen_macaulay_serre_duality"]
theorem nonempty_zExt_dualizingModule_linearEquiv_dual (hCM : IsCohenMacaulay X) (d : ℕ)
    (hpure : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d) (ω : X.Modules)
    (hω : Nonempty (ω ≅ Stacks.Duality.dualizingModuleOverField f d))
    (G : X.Modules) [G.IsCoherent] (i : ℤ) :
    letI := Scheme.linearOver f
    Nonempty (Abelian.zExt G ω i ≃ₗ[k]
      (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) (d - i) →ₗ[k] k)) := by
  let := Scheme.linearOver f
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  rcases isEmpty_or_nonempty X with hX | hX
  · have h0 := Stacks.Duality.ProperOverField.isZero_derivedCategory_of_isEmpty
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)
    have : Subsingleton (Abelian.zExt G ω i) := ⟨fun a b => h0.eq_of_src a b⟩
    have : Subsingleton (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) (d - i)) :=
      ModuleCat.subsingleton_of_isZero (Functor.map_isZero _ (Functor.map_isZero _ h0))
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · obtain ⟨hequi, hd⟩ :=
      equidimensional_and_topologicalKrullDim_eq_of_irreducibleComponents hpure
    exact nonempty_zExt_linearEquiv_of_equidimensional f hCM hequi d hd ω hω G i

end SerreDuality

section AmpleDivisor

variable {k : Type u} [Field k] {F : Scheme.{u}} (f : F ⟶ Spec (.of k))

/-- On a Cohen--Macaulay scheme the depth of every local ring along its maximal ideal is at least
its Krull dimension. -/
theorem ringKrullDim_stalk_le_depth_of_isCohenMacaulay {X : Scheme.{u}}
    (hCM : IsCohenMacaulay X) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ (Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) : WithBot ℕ∞) := by
  obtain ⟨-, hst⟩ := ((isCohenMacaulay_tfae_stalk X).out 1 2).1 hCM
  obtain ⟨_, hR⟩ := hst x
  have h1 : Module.depthSup (X.presheaf.stalk x) (IsLocalRing.maximalIdeal _)
      (X.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk x) := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact hR
  rw [← h1]
  refine WithBot.coe_le_coe.2 ?_
  rw [Module.depth, Module.depthSup_eq_iSup]
  split_ifs
  · exact le_top
  · exact le_rfl

/-- **An ample divisor is connected once closed points have depth at least two.** Let `X` be a
connected scheme proper over a field `k` whose local rings at closed points all have depth at
least two, and `A` an effective Cartier divisor on `X` with `𝒪_X(A)` ample. Then `Supp A` is
connected. -/
theorem isConnected_support_of_two_le_depth {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (A : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor A]
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf A
      Stacks.Ample.IsAmple X (Stacks.Divisors.divisorSheaf A)) :
    _root_.IsConnected (A.support : Set X) := by
  have hconn := Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple k f
    (Stacks.Divisors.divisorSheaf A)
    ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).2 hA)
    (Stacks.Divisors.canonicalSection' A) (Stacks.Divisors.canonicalSection_isRegular A) hdepth
  rw [Stacks.Divisors.zeroScheme_canonicalSection A] at hconn
  rw [← A.range_subschemeι]
  exact isConnected_range A.subschemeι.continuous

/-- **An ample Cartier divisor on a connected projective Cohen--Macaulay scheme is connected.**
Let `F` be a connected projective Cohen--Macaulay scheme over a field `k`, of pure dimension
`d ≥ 2`, and `A` an effective Cartier divisor on `F` with `𝒪_F(A)` ample. Then `Supp A` is
connected (in particular nonempty). -/
@[mmp "lem_fourfold_cm_ample_divisor_connected"]
theorem isConnected_support_of_isAmple_divisorSheaf (hproj : IsProjective f) [ConnectedSpace F]
    (hCM : IsCohenMacaulay F) {d : ℕ} (hd : 2 ≤ d)
    (hpure : ∀ Z ∈ irreducibleComponents F, topologicalKrullDim Z = d)
    (A : F.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor A]
    (hA : haveI := Stacks.Divisors.isInvertible_divisorSheaf A
      Stacks.Ample.IsAmple F (Stacks.Divisors.divisorSheaf A)) :
    _root_.IsConnected (A.support : Set F) := by
  have : IsProper f := hproj.isProper
  have : Nonempty F := ConnectedSpace.toNonempty
  obtain ⟨hequi, hdim⟩ :=
    equidimensional_and_topologicalKrullDim_eq_of_irreducibleComponents hpure
  refine isConnected_support_of_two_le_depth f (fun x hx => ?_) A hA
  have h := ringKrullDim_stalk_le_depth_of_isCohenMacaulay hCM x
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k F f x hx,
    topologicalKrullDimAt_eq_of_equidimensional k F f hequi hdim x] at h
  exact WithBot.coe_le_coe.1 ((show ((2 : ℕ∞) : WithBot ℕ∞) ≤ d by exact_mod_cast hd).trans h)

end AmpleDivisor

section SurfaceFibre

open Stacks.NonvanishingLocusRestrict Stacks.NonvanishingSpelling in
/-- An invertible module has, around every point, a section over an open on which it vanishes
nowhere: the basis section of a local trivialization. -/
theorem exists_opens_nonvanishingLocusOn_of_isInvertibleModule {X : Scheme.{u}} (A : X.Modules)
    [Stacks.Ample.IsInvertibleModule X A] (p : X) :
    ∃ W : X.Opens, p ∈ W ∧ ∃ b : Γ(A, W), (W : Set X) ⊆ nonvanishingLocusOn A W b := by
  obtain ⟨V, hV, hτ⟩ := Stacks.NonvanishingTrivialize.exists_cover_trivialization
    X.toRingedSpace (toSheafOfModules X A)
  obtain ⟨z, hz⟩ : ∃ z : X, p ∈ V z :=
    TopologicalSpace.Opens.mem_iSup.mp (hV ▸ TopologicalSpace.Opens.mem_top p)
  obtain ⟨τ⟩ := hτ z
  exact ⟨V z, hz, Stacks.NonvanishingTrivialize.basis τ, fun y hy =>
    ⟨hy, Stacks.NonvanishingTrivialize.notMem_maximalSmul_germ_basis τ hy⟩⟩

/-- A global section `s` of an invertible module `L` has, in every positive tensor power
`L^{⊗ j}`, a section (its `j`-th power) with the same nonvanishing locus. -/
theorem exists_tensorPower_nonvanishingLocus_eq {X : Scheme.{u}} (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (j : ℕ) (hj : 0 < j) :
    ∃ t : Γ(Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.property L
        (j : ℤ), ⊤),
      Stacks.Ample.nonvanishingLocus _ t = Stacks.Ample.nonvanishingLocus L s := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L := ‹Stacks.Ample.IsInvertibleModule X L›
  let s0 : L.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s
  let e1 := Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L
  let s1 := SheafOfModules.sectionsMap e1.inv s0
  obtain ⟨t0, ht0⟩ := AlgebraicGeometry.exists_section_power_nonvanishingOpen_eq L 1 s1 j hj
  let e2 : Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L ((1 * j : ℕ) : ℤ) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (j : ℤ) := eqToIso (by rw [one_mul])
  refine ⟨(SheafOfModules.sectionsMap e2.hom t0).eval (op ⊤), ?_⟩
  ext y
  have h1 := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq X
    (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (j : ℤ))
    (SheafOfModules.sectionsMap e2.hom t0)
  have h2 := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X L s
  have h3 : y ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ t0 ↔
      y ∈ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ s1 :=
    Iff.of_eq (congrArg (fun W => y ∈ W) ht0)
  have h4 := AlgebraicGeometry.nonvanishingLocus_iso e2 t0 y
  have h5 := AlgebraicGeometry.nonvanishingLocus_iso e1.symm s0 y
  exact (Iff.of_eq (congrArg (fun W => y ∈ W) h1)).symm.trans
    (h4.trans (h3.trans (h5.trans (Iff.of_eq (congrArg (fun W => y ∈ W) h2)))))

open Stacks.NonvanishingLocusRestrict in
/-- If a section `b'` of an invertible module `P` vanishes nowhere on an open `U`, then on `U` the
nonvanishing locus of a global section `t` is the basic open of a function on `U`. -/
theorem exists_basicOpen_iff_mem_nonvanishingLocus_of_subset_nonvanishingLocusOn
    {X : Scheme.{u}} (P : X.Modules) [Stacks.Ample.IsInvertibleModule X P] (U : X.Opens)
    (b' : Γ(P, U)) (hb' : (U : Set X) ⊆ nonvanishingLocusOn P U b') (t : Γ(P, ⊤)) :
    ∃ r : Γ(X, U), ∀ y ∈ U, y ∈ Stacks.Ample.nonvanishingLocus P t ↔ y ∈ X.basicOpen r := by
  let Q := Stacks.AmpleLocallyClosed.pullbackModule U.ι P
  have : Stacks.Ample.IsInvertibleModule U.toScheme Q :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback U.ι P
  let β := restrictSection U P b'
  have hβ : Stacks.Ample.nonvanishingLocus Q β = Set.univ := by
    rw [nonvanishingLocus_restrictSection]
    ext y
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact hb' y.2
  let τ := restrictSection U P (P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
  have hτ : ∀ y : U.toScheme, y ∈ Stacks.Ample.nonvanishingLocus Q τ ↔
      U.ι y ∈ Stacks.Ample.nonvanishingLocus P t := by
    intro y
    rw [mem_nonvanishingLocus_restrictSection_iff,
      mem_nonvanishingLocusOn_iff P U (show U.ι y ∈ U from y.2),
      Stacks.Ample.mem_nonvanishingLocus_iff]
    erw [TopCat.Presheaf.germ_res_apply]
    rfl
  have hW : (⊤ : U.toScheme.Opens) ≤ Stacks.NonvanishingOpen.nonvanishingOpen U.toScheme Q β := by
    intro y _
    change y ∈ Stacks.Ample.nonvanishingLocus Q β
    rw [hβ]
    trivial
  obtain ⟨a, ha⟩ := (Stacks.NonvanishingSpelling.bijective_smul U.toScheme Q β hW).2 τ
  have hid : Q.presheaf.map (homOfLE (le_top : (⊤ : U.toScheme.Opens) ≤ ⊤)).op β = β := by
    rw [show homOfLE (le_top : (⊤ : U.toScheme.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id,
      Q.presheaf.map_id]
    rfl
  have key : ∀ y : U.toScheme, U.ι y ∈ Stacks.Ample.nonvanishingLocus P t ↔
      U.ι y ∈ X.basicOpen a := by
    intro y
    rw [← hτ y]
    have ha' : a • Q.presheaf.map (homOfLE (le_top : (⊤ : U.toScheme.Opens) ≤ ⊤)).op β = τ := ha
    rw [← ha', hid, Stacks.Ample.nonvanishingLocus_smul, hβ, Set.inter_univ]
    exact Scheme.Opens.mem_basicOpen_toScheme (U := U) (V := ⊤) (r := a) (x := y)
  let r : Γ(X, U) := X.presheaf.map (eqToHom U.ι_image_top.symm).op a
  have hr : X.basicOpen r = X.basicOpen a := X.basicOpen_res_eq _ _
  refine ⟨r, fun y hy => ?_⟩
  rw [hr]
  exact key ⟨y, hy⟩

open Stacks.NonvanishingLocusRestrict in
/-- **A section of a pullback does not vanish at one point of a fibre only.** Let `h : X ⟶ X'`
satisfy `h_* 𝒪_X = 𝒪_{X'}` (every `h^♯` on an open is an isomorphism), `A` an invertible
`𝒪_{X'}`-module and `t` a global section of `h^* A`. If `h x = h c` and `t(c) ≠ 0`, then
`t(x) ≠ 0`. -/
theorem mem_nonvanishingLocus_pullback_of_map_eq {X X' : Scheme.{u}} (h : X ⟶ X')
    (hpush : ∀ U : X'.Opens, IsIso (h.app U)) (A : X'.Modules)
    [Stacks.Ample.IsInvertibleModule X' A]
    (t : Γ((Scheme.Modules.pullback h).obj A, ⊤)) {x c : X} (hxc : h x = h c)
    (hc : c ∈ Stacks.Ample.nonvanishingLocus _ t) :
    x ∈ Stacks.Ample.nonvanishingLocus _ t := by
  obtain ⟨W, hcW, b, hb⟩ := exists_opens_nonvanishingLocusOn_of_isInvertibleModule A (h c)
  let P := (Scheme.Modules.pullback h).obj A
  let U : X.Opens := h ⁻¹ᵁ W
  let b' : Γ(P, U) := Stacks.RingedSpace.pullbackUnit h.toLRSHom.toShHom A (op W) b
  have hb' : (U : Set X) ⊆ nonvanishingLocusOn P U b' := by
    intro y hy
    have := preimage_nonvanishingLocusOn h A b
    change _ = nonvanishingLocusOn P U b' at this
    rw [← this]
    exact hb hy
  have hxU : x ∈ U := by
    change h x ∈ W
    rwa [hxc]
  obtain ⟨r, hr⟩ :=
    exists_basicOpen_iff_mem_nonvanishingLocus_of_subset_nonvanishingLocusOn P U b' hb' t
  obtain ⟨σ, hσ⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 (hpush W)).2 r
  have hσ' : h ⁻¹ᵁ X'.basicOpen σ = X.basicOpen r := by
    rw [Scheme.preimage_basicOpen, hσ]
  have key : ∀ y ∈ U, y ∈ Stacks.Ample.nonvanishingLocus P t ↔ h y ∈ X'.basicOpen σ := by
    intro y hy
    rw [hr y hy, ← hσ']
    rfl
  exact (key x hxU).2 (hxc ▸ (key c hcW).1 hc)

variable {k : Type u} [Field k] {X X' : Scheme.{u}}

/-- **Sections pulled back from the base do not vanish at one point of a fibre only.** Let
`h : X → X'` be a proper birational morphism of normal surfaces over `k` with
`h_* 𝒪_X = 𝒪_{X'}`, `L` a line bundle on `X` with `L^{⊗j} ≅ h^* A` for some `j > 0` and some line
bundle `A` on `X'`, and `s ∈ H⁰(X, L)`. If `x, c` are points of `X` with `h(x) = h(c)` and
`s(c) ≠ 0`, then `s(x) ≠ 0`. The source states it for closed points; it holds for all points. -/
@[mmp "lem_fa8_lc_surface_section_nonvanishing_on_fibre"]
theorem mem_nonvanishingLocus_of_map_eq (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    (_hX : IsNormalVariety k sX) (_hX2 : topologicalKrullDim X = 2)
    (_hX' : IsNormalVariety k sX') (_hX'2 : topologicalKrullDim X' = 2)
    (h : X ⟶ X') [IsProper h] (_hh : h ≫ sX' = sX) (_hbir : IsBirationalMorphism h)
    (hpush : ∀ U : X'.Opens, IsIso (h.app U))
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (j : ℕ) (hj : 0 < j)
    (A : X'.Modules) [Stacks.Ample.IsInvertibleModule X' A]
    (hLA : Nonempty (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
      X.ringCatSheaf.property L (j : ℤ) ≅ (Scheme.Modules.pullback h).obj A))
    (s : Γ(L, ⊤)) {x c : X} (hxc : h x = h c) (hsc : c ∈ Stacks.Ample.nonvanishingLocus L s) :
    x ∈ Stacks.Ample.nonvanishingLocus L s := by
  obtain ⟨t, ht⟩ := exists_tensorPower_nonvanishingLocus_eq L s j hj
  obtain ⟨e⟩ := hLA
  let M : X.Modules := Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
    X.ringCatSheaf.property L (j : ℤ)
  let e' : M ≅ (Scheme.Modules.pullback h).obj A := e
  rw [← ht, ← Stacks.Ample.nonvanishingLocus_congr e' t] at hsc ⊢
  exact mem_nonvanishingLocus_pullback_of_map_eq h hpush A (e'.hom.app ⊤ t) hxc hsc

end SurfaceFibre

end MMP.Mori
