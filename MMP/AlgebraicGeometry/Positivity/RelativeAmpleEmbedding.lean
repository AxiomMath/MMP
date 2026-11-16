module
public import MMP.AlgebraicGeometry.SpreadingOut.FilteredColimitStages
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Resolution.Surface.TopFormDivisors
public import MMP.AlgebraicGeometry.MMP.Steps
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional

/-!
# Relative very ampleness, descent of invertible sheaves, and weighted orders

Four independent foundational results.

Let `h : V ⟶ Z` be a proper morphism of varieties and `A` an `h`-ample Cartier divisor on `V`.
For all sufficiently large `m`, the divisor `mA` is `h`-free, i.e. the evaluation map
`h^* h_* 𝒪_V(mA) ⟶ 𝒪_V(mA)` is surjective, and the morphism `V ⟶ ℙ_Z(h_* 𝒪_V(mA))` that this
quotient defines is a closed immersion. Moreover `V ≅ Proj_Z ⨁_{n ≥ 0} h_* 𝒪_V(nA)` over `Z`.

Invertible sheaves, and isomorphisms between them, descend along a filtered colimit of
algebras `B = colim R_j` from `Z ×_A Spec B` to some `Z ×_A Spec R_j`. A proper birational
morphism of varieties onto a normal variety is an isomorphism off a closed set of codimension at
least two. On a two-dimensional regular local ring the weighted order with weights `(1, w)` is
a valuation, and extends uniquely to the fraction field.

## Main results

* `MMP.Flips.IsRelativelyAmpleCartier.eventually_isClosedImmersion_projectiveBundle`
* `MMP.exists_isInvertible_pullback_iso_of_isColimit_under`
* `MMP.Mori.exists_isIso_morphismRestrict_two_le_closedsCodimension`
* `MMP.Resolution.exists_addValuation_monomialValuation`

## Implementation notes

For the first result, the morphism `V ⟶ ℙ_Z(E)`, `E = h_* 𝒪_V(mA)`, is
`MMP.Flips.relativeEvaluationMorphism`, defined for any `h`-free invertible sheaf
(`MMP.Flips.IsRelativelyFreeModule`) as the morphism to `Proj_Z Sym(E)` induced by
`Sym(E) ⟶ h_* ⨁ 𝒪_V(mA)^{⊗ n}`. It lies over `Z`, and through the isomorphism
`MMP.Flips.relativeEvaluationTwistIso : i^* 𝒪_{ℙ(E)}(1) ≅ 𝒪_V(mA)` the pullback of the
tautological quotient `π^* E ⟶ 𝒪_{ℙ(E)}(1)` is the counit `h^* h_* 𝒪_V(mA) ⟶ 𝒪_V(mA)` of
`h^* ⊣ h_*` (`MMP.Flips.tautologicalMap_relativeEvaluationTwistIso`); so it is the morphism the
universal property of `ℙ(E)` attaches to that quotient.

The relative `Proj` is that of `Stacks.RelativeAmple.directImageAlgebra h 𝒪_V(A)`, whose degree
`n` piece is `h_*` of the `n`-th tensor power of `𝒪_V(A)`, which is `h_* 𝒪_V(nA)`; the
statement asserts an isomorphism of `V` with it over `Z`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.22
* [Stacks Project, Tag 0C6J](https://stacks.math.columbia.edu/tag/0C6J)
* [EGA II, 4.6]
* [Stacks Project, Tag 0B8W]
* [Stacks Project, Tag 01ZR]
* [J. Kollár and S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  Notation 0.4(7)
* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], 1.10
-/

section

universe u

open CategoryTheory AlgebraicGeometry Opposite Filter
open MMP.Mori MMP.Intersection.Scheme.Modules
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.RelativeProjDegreeOne (unitSection app_homEquiv_symm)
open Stacks.Chow.GenuineChern Stacks.Tag01VMVeryAmple

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Proofs.lem_mmp_foundation_fa2_ample_powers_complete_relative_embedding

/-- A morphism out of an inverse image is determined by its values on pulled-back sections. -/
private theorem hom_ext_unitSection {X Y : Scheme.{u}} (r : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    {φ ψ : (Scheme.Modules.pullback r).obj M ⟶ N}
    (h : ∀ (O : Y.Opens) (s : Γ(M, O)),
      φ.val.app (op (r ⁻¹ᵁ O)) (unitSection r M O s) =
        ψ.val.app (op (r ⁻¹ᵁ O)) (unitSection r M O s)) :
    φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv M N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact Scheme.Modules.hom_ext _ _ fun O => ConcreteCategory.hom_ext _ _ (h O)

private theorem counit_unitSection {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) (W : S.Opens)
    (s : Γ((Scheme.Modules.pushforward f).obj L, W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L).val.app (op (f ⁻¹ᵁ W))
      (unitSection f _ W s) = s := by
  have := app_homEquiv_symm f (𝟙 ((Scheme.Modules.pushforward f).obj L)) W s
  rw [Stacks.Tag01VMVeryAmple.homEquiv_symm_id] at this
  exact this

/-- A morphism `r^* π^* f_* L ⟶ L` built from `τ` and `φ` equals the counit if it agrees with it
on pulled-back sections. -/
private theorem eq_counit_of_sections {X S P : Scheme.{u}} (f : X ⟶ S) (r : X ⟶ P) (π : P ⟶ S)
    (hr : r ≫ π = f) (L : X.Modules) (O : P.Modules)
    (τ : (Scheme.Modules.pullback π).obj ((Scheme.Modules.pushforward f).obj L) ⟶ O)
    (φ : (Scheme.Modules.pullback r).obj O ⟶ L)
    (H : ∀ (W : S.Opens) (s : Γ((Scheme.Modules.pushforward f).obj L, W)),
      φ.val.app (op (r ⁻¹ᵁ (π ⁻¹ᵁ W)))
          (unitSection r O (π ⁻¹ᵁ W) (τ.val.app (op (π ⁻¹ᵁ W))
            (unitSection π _ W s))) =
        L.val.map (homOfLE (by rw [← hr]; rfl : r ⁻¹ᵁ (π ⁻¹ᵁ W) ≤ f ⁻¹ᵁ W)).op s) :
    (Scheme.Modules.pullbackCongr hr).inv.app _ ≫
        (Scheme.Modules.pullbackComp r π).inv.app _ ≫
        (Scheme.Modules.pullback r).map τ ≫ φ =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L := by
  subst hr
  refine hom_ext_unitSection (r ≫ π) fun W s => ?_
  rw [counit_unitSection]
  refine Eq.trans ?_ ((H W s).trans (PresheafOfModules.map_id_apply L.val _ s))
  exact congrArg (φ.val.app (op (r ⁻¹ᵁ (π ⁻¹ᵁ W))))
    ((congrArg (((Scheme.Modules.pullback r).map τ).val.app (op (r ⁻¹ᵁ (π ⁻¹ᵁ W))))
      (Stacks.Chow.GenuineChern.pullbackComp_inv_unitSection r π _ W s)).trans
      (Stacks.Chow.GenuineChern.unitSection_pullback_map r τ (π ⁻¹ᵁ W) _))

/-- Restricting a section along a section `j` of an open immersion `U.ι` and transporting it back
through the canonical isomorphisms recovers its restriction. -/
private theorem unitSection_comp_ι_eq_id {X : Scheme.{u}} (U : X.Opens) (j : X ⟶ U.toScheme)
    (hj : j ≫ U.ι = 𝟙 X)
    (T : X.Modules) (Ws : X.Opens) (u : Γ(T, Ws)) (V' : U.toScheme.Opens)
    (hV' : V' ≤ U.ι ⁻¹ᵁ Ws) :
    ((Scheme.Modules.pullbackId X).hom.app T).val.app (op (j ⁻¹ᵁ V'))
      (((Scheme.Modules.pullbackCongr hj).hom.app T).val.app (op (j ⁻¹ᵁ V'))
        (((Scheme.Modules.pullbackComp j U.ι).hom.app T).val.app (op (j ⁻¹ᵁ V'))
          (unitSection j ((Scheme.Modules.pullback U.ι).obj T) V'
            (((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app T).val.app (op V')
              (((Scheme.Modules.restrictFunctor U.ι).obj T).val.map (homOfLE hV').op
                (T.val.map (homOfLE (U.ι.image_preimage_le Ws)).op u)))))) =
      T.val.map (homOfLE (by
        intro x hx
        have := hV' hx
        have h2 : (j ≫ U.ι) x ∈ Ws := this
        rw [hj] at h2
        exact h2 : j ⁻¹ᵁ V' ≤ Ws)).op u := by
  have hjle : j ⁻¹ᵁ (U.ι ⁻¹ᵁ Ws) ≤ Ws := by
    intro x hx
    have h2 : (j ≫ U.ι) x ∈ Ws := hx
    rw [hj] at h2
    exact h2
  have s1 := PresheafOfModules.naturality_apply
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app T).val (homOfLE hV').op
    (T.val.map (homOfLE (U.ι.image_preimage_le Ws)).op u)
  rw [restrictFunctorIsoPullback_hom_res] at s1
  have s2 := unitSection_restrict j ((Scheme.Modules.pullback U.ι).obj T) hV'
    (unitSection U.ι T Ws u)
  have e4 : ((Scheme.Modules.pullbackComp j U.ι).hom.app T).val.app (op (j ⁻¹ᵁ (U.ι ⁻¹ᵁ Ws)))
      (unitSection j ((Scheme.Modules.pullback U.ι).obj T) (U.ι ⁻¹ᵁ Ws)
        (unitSection U.ι T Ws u)) = unitSection (j ≫ U.ι) T Ws u :=
    pullbackComp_hom_unitSection j U.ι T Ws u
  have e6 : ((Scheme.Modules.pullbackCongr hj).hom.app T).val.app (op (j ⁻¹ᵁ (U.ι ⁻¹ᵁ Ws)))
      (unitSection (j ≫ U.ι) T Ws u) =
      ((Scheme.Modules.pullback (𝟙 X)).obj T).val.map (homOfLE hjle).op
        (unitSection (𝟙 X) T Ws u) :=
    pullbackCongr_hom_unitSection_eq hj T Ws u hjle
  have e8 : ((Scheme.Modules.pullbackId X).hom.app T).val.app (op Ws)
      (unitSection (𝟙 X) T Ws u) = u :=
    pullbackId_hom_unitSection X T Ws u
  have n3 : ((Scheme.Modules.pullbackComp j U.ι).hom.app T).val.app (op (j ⁻¹ᵁ V'))
      (((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback U.ι).obj T)).val.map
        (homOfLE (j.preimage_mono hV')).op
        (unitSection j ((Scheme.Modules.pullback U.ι).obj T) (U.ι ⁻¹ᵁ Ws)
          (unitSection U.ι T Ws u))) =
      ((Scheme.Modules.pullback (j ≫ U.ι)).obj T).val.map (homOfLE (j.preimage_mono hV')).op
        (((Scheme.Modules.pullbackComp j U.ι).hom.app T).val.app (op (j ⁻¹ᵁ (U.ι ⁻¹ᵁ Ws)))
          (unitSection j ((Scheme.Modules.pullback U.ι).obj T) (U.ι ⁻¹ᵁ Ws)
            (unitSection U.ι T Ws u))) :=
    PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackComp j U.ι).hom.app T).val (homOfLE (j.preimage_mono hV')).op _
  have n5 : ((Scheme.Modules.pullbackCongr hj).hom.app T).val.app (op (j ⁻¹ᵁ V'))
      (((Scheme.Modules.pullback (j ≫ U.ι)).obj T).val.map (homOfLE (j.preimage_mono hV')).op
        (unitSection (j ≫ U.ι) T Ws u)) =
      ((Scheme.Modules.pullback (𝟙 X)).obj T).val.map (homOfLE (j.preimage_mono hV')).op
        (((Scheme.Modules.pullbackCongr hj).hom.app T).val.app (op (j ⁻¹ᵁ (U.ι ⁻¹ᵁ Ws)))
          (unitSection (j ≫ U.ι) T Ws u)) :=
    PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackCongr hj).hom.app T).val (homOfLE (j.preimage_mono hV')).op _
  have n7 : ((Scheme.Modules.pullbackId X).hom.app T).val.app (op (j ⁻¹ᵁ V'))
      (((Scheme.Modules.pullback (𝟙 X)).obj T).val.map
        (homOfLE ((j.preimage_mono hV').trans hjle)).op (unitSection (𝟙 X) T Ws u)) =
      T.val.map (homOfLE ((j.preimage_mono hV').trans hjle)).op
        (((Scheme.Modules.pullbackId X).hom.app T).val.app (op Ws)
          (unitSection (𝟙 X) T Ws u)) :=
    PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackId X).hom.app T).val
      (homOfLE ((j.preimage_mono hV').trans hjle)).op _
  rw [s1, s2, n3, e4, n5, e6]
  refine (congrArg (((Scheme.Modules.pullbackId X).hom.app T).val.app (op (j ⁻¹ᵁ V')))
    (map_map_homOfLE ((Scheme.Modules.pullback (𝟙 X)).obj T) (j.preimage_mono hV') hjle
      (unitSection (𝟙 X) T Ws u))).trans ?_
  rw [n7, e8]

private theorem presheaf_map_eqToHom_symm {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens}
    (e : A = B) (x : Γ(M, B)) :
    M.presheaf.map (eqToHom e.symm).op (M.presheaf.map (eqToHom e).op x) = x := by
  subst e
  simp

private theorem iso_inv_hom_apply {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (V : Y.Opens)
    (x : Γ(M, V)) : e.inv.val.app (op V) (e.hom.val.app (op V) x) = x := by
  change (e.hom ≫ e.inv).val.app (op V) x = x
  rw [e.hom_inv_id]
  rfl

section D

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hepi : Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L))

private theorem jcomp_ι :
    (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L hepi)).inv) ≫
      (directImageSymPowerMap f L).coveringOpen.ι = 𝟙 X := by
  simp only [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]

/-- `θ₁` with its source and target spelled as inverse image and restriction. -/
private noncomputable def thetaOne :
    (Scheme.Modules.pullback ((directImageSymPowerMap f L).globalMorphism (relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))))).obj
        (twistOne ((Scheme.Modules.pushforward f).obj L)) ⟶
      (Scheme.Modules.restrictFunctor (directImageSymPowerMap f L).coveringOpen.ι).obj
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) :=
  (directImageSymPowerMap f L).theta.app 1

omit [QuasiCompact f] [QuasiSeparated f] in
/-- `L^{⊗ 1} ⟶ L`. -/
private noncomputable def powOneToSelf :
    (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) ⟶ L :=
  (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).inv ≫
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom

omit [QuasiCompact f] [QuasiSeparated f] in
private theorem powOneToSelf_apply {V V' : X.Opens} (i : V' ≤ V) (s : Γ(L, V)) :
    (powOneToSelf L).val.app (op V')
      ((Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)).val.map (homOfLE i).op
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app V
        ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app V s))) =
      L.val.map (homOfLE i).op s := by
  refine (PresheafOfModules.naturality_apply (powOneToSelf L).val (homOfLE i).op _).trans ?_
  congr 1
  have h1 := iso_inv_hom_apply (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1) V
    ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app V s)
  have h2 := iso_inv_hom_apply
    (Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).symm V s
  exact (congrArg ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).hom.val.app
    (op V)) h1).trans h2

/-- The comparison `r^* 𝒪(1) ⟶ L` through `θ₁`. -/
private noncomputable def phi0 :
    (Scheme.Modules.pullback ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
        hepi)).inv) ≫ ((directImageSymPowerMap f L).globalMorphism (relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))))).obj
        (twistOne ((Scheme.Modules.pushforward f).obj L)) ⟶ L :=
  (Scheme.Modules.pullbackComp (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
      hepi)).inv) ((directImageSymPowerMap f L).globalMorphism (relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
      L))))).inv.app (twistOne ((Scheme.Modules.pushforward f).obj L)) ≫
  (Scheme.Modules.pullback (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
      hepi)).inv)).map (thetaOne f L) ≫
  (Scheme.Modules.pullback (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
      hepi)).inv)).map
            ((Scheme.Modules.restrictFunctorIsoPullback
              (directImageSymPowerMap f L).coveringOpen.ι).hom.app
                  (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ))) ≫
  (Scheme.Modules.pullbackComp (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
      hepi)).inv) (directImageSymPowerMap f L).coveringOpen.ι).hom.app
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) ≫
  (Scheme.Modules.pullbackCongr (jcomp_ι f L hepi)).hom.app
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) ≫
  (Scheme.Modules.pullbackId X).hom.app (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1
      : ℕ) : ℤ)) ≫
  powOneToSelf L

private theorem phi0_unitSection (W : S.Opens) (s : Γ((Scheme.Modules.pushforward f).obj L, W)) :
    (phi0 f L hepi).val.app (op (((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f
        L hepi)).inv) ≫ ((directImageSymPowerMap f L).globalMorphism (relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))))) ⁻¹ᵁ
        ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
        f).obj L))).toBase ⁻¹ᵁ W))) (unitSection ((X.topIso.inv ≫ (X.isoOfEq
        (coveringOpen_directImageSymPowerMap f L hepi)).inv) ≫ ((directImageSymPowerMap f
        L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
        ((Scheme.Modules.pushforward f).obj L))))) (twistOne ((Scheme.Modules.pushforward f).obj
        L)) ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
        f).obj L))).toBase ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData
        ((Scheme.Modules.pushforward f).obj L)
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
        ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op
        W) s))) =
      L.val.map (homOfLE (show ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
          hepi)).inv) ≫ ((directImageSymPowerMap f L).globalMorphism (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))))
          ⁻¹ᵁ ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          ((Scheme.Modules.pushforward f).obj L))).toBase ⁻¹ᵁ W) ≤ f ⁻¹ᵁ W from
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, toRelativeProj_comp_toBase]) :
          toRelativeProj (directImageSymPowerMap f L)
            (coveringOpen_directImageSymPowerMap f L hepi) ⁻¹ᵁ ((relativeProj
                (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
                L))).toBase ⁻¹ᵁ W) ≤ f ⁻¹ᵁ W))).op s := by
  have hcl := (directImageSymPowerMap f L).theta_clauseOne W 1
    (Scheme.Modules.Hom.app (Scheme.Modules.symmetricAlgebraGen S
      ((Scheme.Modules.pushforward f).obj L)) W s)
  rw [directImageSymPowerMap_value_gen] at hcl
  have hV' : ((directImageSymPowerMap f L).globalMorphism (relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ
      ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
      f).obj L))).toBase ⁻¹ᵁ W) ≤ (directImageSymPowerMap f L).coveringOpen.ι ⁻¹ᵁ (f ⁻¹ᵁ W) :=
    ((directImageSymPowerMap f L).toBase_preimage_eq W).symm.le
  have ht : (thetaOne f L).val.app (op (((directImageSymPowerMap f L).globalMorphism (relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ
      ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
      f).obj L))).toBase ⁻¹ᵁ W))) (unitSection ((directImageSymPowerMap f L).globalMorphism
      (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
      L)))) (twistOne ((Scheme.Modules.pushforward f).obj L)) ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData ((Scheme.Modules.pushforward f).obj L)
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
      ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op W)
      s))) =
      ((Scheme.Modules.restrictFunctor (directImageSymPowerMap f L).coveringOpen.ι).obj
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ))).val.map (homOfLE
          hV').op
        ((Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)).val.map (homOfLE
            ((directImageSymPowerMap f L).coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ W))).op
            ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app (f ⁻¹ᵁ W)
            ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ W) s)))
            := by
    have := congrArg (((directImageSymPowerMap f L).powK ((1 : ℕ) : ℤ)).presheaf.map
      (eqToHom ((directImageSymPowerMap f L).toBase_preimage_eq W).symm).op) hcl
    exact (presheaf_map_eqToHom_symm _ ((directImageSymPowerMap f L).toBase_preimage_eq W)
        _).symm.trans this
  have e1 := pullbackComp_inv_unitSection (X.topIso.inv ≫ (X.isoOfEq
      (coveringOpen_directImageSymPowerMap f L hepi)).inv) ((directImageSymPowerMap f
      L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
      ((Scheme.Modules.pushforward f).obj L)))) (twistOne ((Scheme.Modules.pushforward f).obj L))
      ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
      f).obj L))).toBase ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData
      ((Scheme.Modules.pushforward f).obj L)
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
      ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op W)
      s))
  have e2 := unitSection_pullback_map (X.topIso.inv ≫ (X.isoOfEq
      (coveringOpen_directImageSymPowerMap f L hepi)).inv) (thetaOne f L) (((directImageSymPowerMap
      f L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
      ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W)) (unitSection ((directImageSymPowerMap f L).globalMorphism (relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))))
      (twistOne ((Scheme.Modules.pushforward f).obj L)) ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData ((Scheme.Modules.pushforward f).obj L)
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
      ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op W)
      s)))
  rw [ht] at e2
  have e3 := unitSection_pullback_map (X.topIso.inv ≫ (X.isoOfEq
      (coveringOpen_directImageSymPowerMap f L hepi)).inv)
    ((Scheme.Modules.restrictFunctorIsoPullback (directImageSymPowerMap f
        L).coveringOpen.ι).hom.app (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ)
        : ℤ))) (((directImageSymPowerMap f L).globalMorphism (relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ
        ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
        f).obj L))).toBase ⁻¹ᵁ W))
    (((Scheme.Modules.restrictFunctor (directImageSymPowerMap f L).coveringOpen.ι).obj
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ))).val.map (homOfLE
        hV').op
        ((Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)).val.map (homOfLE
            ((directImageSymPowerMap f L).coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ W))).op
            ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app (f ⁻¹ᵁ W)
            ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ W) s))))
  have hC := unitSection_comp_ι_eq_id (directImageSymPowerMap f L).coveringOpen
      (X.topIso.inv ≫ (X.isoOfEq
      (coveringOpen_directImageSymPowerMap f L hepi)).inv) (jcomp_ι f L hepi)
      (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) (f ⁻¹ᵁ W)
      ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app (f ⁻¹ᵁ W)
      ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ W) s)) _ hV'
  have hchain : (powOneToSelf L).val.app (op ((X.topIso.inv ≫ (X.isoOfEq
      (coveringOpen_directImageSymPowerMap f L hepi)).inv) ⁻¹ᵁ (((directImageSymPowerMap f
      L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
      ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W))))
      (((Scheme.Modules.pullbackId X).hom.app (Stacks.AmpleProjectiveImmersion.tensorPowerModule X
          L ((1 : ℕ) : ℤ))).val.app (op ((X.topIso.inv ≫ (X.isoOfEq
          (coveringOpen_directImageSymPowerMap f L hepi)).inv) ⁻¹ᵁ (((directImageSymPowerMap f
          L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ ((relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
          L))).toBase ⁻¹ᵁ W))))
      (((Scheme.Modules.pullbackCongr (jcomp_ι f L hepi)).hom.app
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ))).val.app (op
          ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L hepi)).inv) ⁻¹ᵁ
          (((directImageSymPowerMap f L).globalMorphism (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ
          ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
          f).obj L))).toBase ⁻¹ᵁ W))))
      (((Scheme.Modules.pullbackComp (X.topIso.inv ≫ (X.isoOfEq
          (coveringOpen_directImageSymPowerMap f L hepi)).inv) (directImageSymPowerMap f
          L).coveringOpen.ι).hom.app (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 :
          ℕ) : ℤ))).val.app (op ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f
          L hepi)).inv) ⁻¹ᵁ (((directImageSymPowerMap f L).globalMorphism (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ
          ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
          f).obj L))).toBase ⁻¹ᵁ W))))
      (((Scheme.Modules.pullback (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f
          L hepi)).inv)).map ((Scheme.Modules.restrictFunctorIsoPullback
              (directImageSymPowerMap f L).coveringOpen.ι).hom.app
                  (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)))).val.app
                  (op ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
                  hepi)).inv) ⁻¹ᵁ (((directImageSymPowerMap f L).globalMorphism (relativeProj
                  (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
                  L)))) ⁻¹ᵁ ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
                  ((Scheme.Modules.pushforward f).obj L))).toBase ⁻¹ᵁ W))))
      (((Scheme.Modules.pullback (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f
          L hepi)).inv)).map (thetaOne f L)).val.app (op ((X.topIso.inv ≫ (X.isoOfEq
          (coveringOpen_directImageSymPowerMap f L hepi)).inv) ⁻¹ᵁ (((directImageSymPowerMap f
          L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ ((relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
          L))).toBase ⁻¹ᵁ W))))
      (((Scheme.Modules.pullbackComp (X.topIso.inv ≫ (X.isoOfEq
          (coveringOpen_directImageSymPowerMap f L hepi)).inv) ((directImageSymPowerMap f
          L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          ((Scheme.Modules.pushforward f).obj L))))).inv.app (twistOne ((Scheme.Modules.pushforward
          f).obj L))).val.app (op (((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap
          f L hepi)).inv) ≫ ((directImageSymPowerMap f L).globalMorphism (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))))
          ⁻¹ᵁ ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          ((Scheme.Modules.pushforward f).obj L))).toBase ⁻¹ᵁ W)))
        (unitSection ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
            hepi)).inv) ≫ ((directImageSymPowerMap f L).globalMorphism (relativeProj
            (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))))
            (twistOne ((Scheme.Modules.pushforward f).obj L)) ((relativeProj
            (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
            L))).toBase ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData
            ((Scheme.Modules.pushforward f).obj L)
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
            ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app
            (op W) s))))))))) =
      (powOneToSelf L).val.app (op ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap
          f L hepi)).inv) ⁻¹ᵁ (((directImageSymPowerMap f L).globalMorphism (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))) ⁻¹ᵁ
          ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward
          f).obj L))).toBase ⁻¹ᵁ W)))) ((Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1
          : ℕ) : ℤ)).val.map (homOfLE (((X.topIso.inv ≫ (X.isoOfEq
          (coveringOpen_directImageSymPowerMap f L hepi)).inv).preimage_mono hV').trans
        (by
          intro x hx
          have h2 : ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
              hepi)).inv) ≫ (directImageSymPowerMap f L).coveringOpen.ι) x ∈ f ⁻¹ᵁ W := hx
          rw [jcomp_ι f L hepi] at h2
          exact h2))).op
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).hom.app (f ⁻¹ᵁ W)
          ((Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L).inv.app (f ⁻¹ᵁ W) s))) :=
              by
    rw [e1, e2, e3, hC]
  exact hchain.trans (powOneToSelf_apply L _ s)

private theorem toRelativeProj_eq_comp : (toRelativeProj (directImageSymPowerMap f L)
    (coveringOpen_directImageSymPowerMap f L hepi)) = (X.topIso.inv ≫ (X.isoOfEq
    (coveringOpen_directImageSymPowerMap f L hepi)).inv) ≫ ((directImageSymPowerMap f
    L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
    ((Scheme.Modules.pushforward f).obj L)))) := by
  rw [toRelativeProj, Category.assoc]

private theorem pullbackCongr_comp_phi0_unitSection (W : S.Opens)
    (s : Γ((Scheme.Modules.pushforward f).obj L, W)) :
    (((Scheme.Modules.pullbackCongr (toRelativeProj_eq_comp f L hepi)).hom.app (twistOne
        ((Scheme.Modules.pushforward f).obj L))) ≫
      phi0 f L hepi).val.app (op ((toRelativeProj (directImageSymPowerMap f L)
          (coveringOpen_directImageSymPowerMap f L hepi)) ⁻¹ᵁ ((relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
          L))).toBase ⁻¹ᵁ W))) (unitSection (toRelativeProj (directImageSymPowerMap f L)
          (coveringOpen_directImageSymPowerMap f L hepi)) (twistOne ((Scheme.Modules.pushforward
          f).obj L)) ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          ((Scheme.Modules.pushforward f).obj L))).toBase ⁻¹ᵁ W)
          (((Stacks.SymGraded.projectiveBundleTwistData ((Scheme.Modules.pushforward f).obj L)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
          ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app
          (op W) s))) =
      L.val.map (homOfLE
          (le_of_eq (by rw [← Scheme.Hom.comp_preimage, toRelativeProj_comp_toBase]) :
          (toRelativeProj (directImageSymPowerMap f L) (coveringOpen_directImageSymPowerMap f L
              hepi)) ⁻¹ᵁ ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
              ((Scheme.Modules.pushforward f).obj L))).toBase ⁻¹ᵁ W) ≤ f ⁻¹ᵁ W)).op s := by
  have hle : (toRelativeProj (directImageSymPowerMap f L) (coveringOpen_directImageSymPowerMap f L
      hepi)) ⁻¹ᵁ ((relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
      ((Scheme.Modules.pushforward f).obj L))).toBase ⁻¹ᵁ W) ≤ ((X.topIso.inv ≫ (X.isoOfEq
      (coveringOpen_directImageSymPowerMap f L hepi)).inv) ≫ ((directImageSymPowerMap f
      L).globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
      ((Scheme.Modules.pushforward f).obj L))))) ⁻¹ᵁ ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W) := by rw [toRelativeProj_eq_comp f L hepi]
  have c1 := pullbackCongr_hom_unitSection_eq (toRelativeProj_eq_comp f L hepi) (twistOne
      ((Scheme.Modules.pushforward f).obj L)) ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData ((Scheme.Modules.pushforward f).obj L)
      (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
      ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op W)
      s)) hle
  have c2 := PresheafOfModules.naturality_apply (phi0 f L hepi).val (homOfLE hle).op
    (unitSection ((X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L hepi)).inv) ≫
        ((directImageSymPowerMap f L).globalMorphism (relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L)))))
        (twistOne ((Scheme.Modules.pushforward f).obj L)) ((relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
        ⁻¹ᵁ W) (((Stacks.SymGraded.projectiveBundleTwistData ((Scheme.Modules.pushforward f).obj L)
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
        ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op
        W) s)))
  rw [phi0_unitSection] at c2
  have c3 := congrArg ((phi0 f L hepi).val.app _) c1
  have c4 := c2.trans (map_map_homOfLE L _ _ s)
  have c5 := c3.trans c4
  exact (comp_app_apply _ _ _ _).trans c5

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The tautological quotient, with its target spelled as `twistOne`. -/
private noncomputable def tautMap (E : S.Modules) [E.IsQuasicoherent] :
    (Scheme.Modules.pullback (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
        E)).toBase).obj E ⟶
      twistOne E :=
  Stacks.ProjectiveBundleSplitting.tautologicalMap E
    (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)

private theorem tautologicalMap_comp_eq_counit :
    (Scheme.Modules.pullbackCongr (toRelativeProj_comp_toBase (directImageSymPowerMap f L)
        (coveringOpen_directImageSymPowerMap f L hepi))).inv.app ((Scheme.Modules.pushforward
            f).obj L) ≫
      (Scheme.Modules.pullbackComp (toRelativeProj (directImageSymPowerMap f L)
          (coveringOpen_directImageSymPowerMap f L hepi)) (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
          L))).toBase).inv.app ((Scheme.Modules.pushforward f).obj L) ≫
      (Scheme.Modules.pullback (toRelativeProj (directImageSymPowerMap f L)
          (coveringOpen_directImageSymPowerMap f L hepi))).map (tautMap
          ((Scheme.Modules.pushforward f).obj L)) ≫
      ((Scheme.Modules.pullbackCongr (toRelativeProj_eq_comp f L hepi)).hom.app (twistOne
          ((Scheme.Modules.pushforward f).obj L)) ≫
        phi0 f L hepi) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L := by
  refine eq_counit_of_sections f _ _ (toRelativeProj_comp_toBase _ _) L _ _ _ fun W s => ?_
  have t1 : (tautMap ((Scheme.Modules.pushforward f).obj L)).val.app (op ((relativeProj
      (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj L))).toBase
      ⁻¹ᵁ W)) (unitSection (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
      ((Scheme.Modules.pushforward f).obj L))).toBase ((Scheme.Modules.pushforward f).obj L) W s) =
      ((Stacks.SymGraded.projectiveBundleTwistData ((Scheme.Modules.pushforward f).obj L)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)).ψ 1).val.app (op W)
        ((Scheme.Modules.symmetricAlgebraGen S ((Scheme.Modules.pushforward f).obj L)).val.app (op
            W) s) :=
    tautologicalMap_unitSection ((Scheme.Modules.pushforward f).obj L)
        (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _) W s
  rw [t1]
  exact pullbackCongr_comp_phi0_unitSection f L hepi W s

/-- **Clause (1) of Tag 01O9.** The isomorphism `r^* 𝒪_{ℙ(f_* L)}(1) ≅ L`, for `r : X ⟶ ℙ(f_* L)`
the morphism defined by the quotient `f^* f_* L ⟶ L`. -/
private noncomputable def tautologicalTwistIso :
    (Scheme.Modules.pullback (toRelativeProj (directImageSymPowerMap f L)
          (coveringOpen_directImageSymPowerMap f L hepi))).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist
          ((Scheme.Modules.pushforward f).obj L)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)) ≅ L :=
  haveI : IsIso (thetaOne f L) := Stacks.VeryAmpleGlue.isIso_theta_one _ fun x => by
    obtain ⟨W, -, a, hx⟩ := exists_mem_nonvanishingOpenAt_directImageSymPowerMap f _ hepi
      ((directImageSymPowerMap f L).coveringOpen.ι x)
    exact ⟨W, a, hx⟩
  (Scheme.Modules.pullbackCongr (toRelativeProj_eq_comp f L hepi)).app _ ≪≫
    (Scheme.Modules.pullbackComp (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f
        L hepi)).inv) ((directImageSymPowerMap f L).globalMorphism (relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra ((Scheme.Modules.pushforward f).obj
        L))))).symm.app (twistOne ((Scheme.Modules.pushforward f).obj L)) ≪≫
    (Scheme.Modules.pullback (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
        hepi)).inv)).mapIso (asIso (thetaOne f L)) ≪≫
    (Scheme.Modules.pullback (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f L
        hepi)).inv)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (directImageSymPowerMap f L).coveringOpen.ι).app
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ))) ≪≫
    (Scheme.Modules.pullbackComp (X.topIso.inv ≫ (X.isoOfEq (coveringOpen_directImageSymPowerMap f
        L hepi)).inv) (directImageSymPowerMap f L).coveringOpen.ι).app
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) ≪≫
    (Scheme.Modules.pullbackCongr (jcomp_ι f L hepi)).app
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 : ℕ) : ℤ)) ≪≫
    (Scheme.Modules.pullbackId X).app (Stacks.AmpleProjectiveImmersion.tensorPowerModule X L ((1 :
        ℕ) : ℤ)) ≪≫
    (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L 1).symm ≪≫
    Stacks.AlgebraicGeometry.MorphismToProjUniversal.unitorPow L

end D

private noncomputable def nsmulIso {V : Scheme.{u}} [IsLocallyNoetherian V] [IsNormal V]
    [CompactSpace V] {A : Divisor V} (hA : A.IsCartier) (m : ℕ) :
    haveI := hA.isInvertibleModule_divisorialSheaf
    (m • A).divisorialSheaf ≅ Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  induction m with
  | zero =>
    exact eqToIso (by rw [zero_smul]) ≪≫ Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.Ample.tensorPowModuleZeroIso V A.divisorialSheaf).symm
  | succ n ih =>
    exact eqToIso (by rw [succ_nsmul]) ≪≫
      ((hA.nsmul n).divisorialSheafTensorIso hA).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso ih).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso V A.divisorialSheaf).symm ≪≫
      Stacks.Ample.tensorPowModuleAddIso V A.divisorialSheaf (n : ℤ) 1 ≪≫
      eqToIso (by push_cast; rfl)

end MMP.Proofs.lem_mmp_foundation_fa2_ample_powers_complete_relative_embedding

namespace MMP.Flips

section RelativeEvaluation

open MMP.Proofs.lem_mmp_foundation_fa2_ample_powers_complete_relative_embedding

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- An `𝒪_X`-module `L` is *`f`-free* (relatively globally generated) for `f : X ⟶ S` if the
evaluation map `f^* f_* L ⟶ L`, the counit of `f^* ⊣ f_*`, is an epimorphism. -/
@[expose] public def IsRelativelyFreeModule (L : X.Modules) : Prop :=
  Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L)

public theorem isRelativelyFreeModule_iff (L : X.Modules) :
    IsRelativelyFreeModule f L ↔
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L) :=
  Iff.rfl

variable [QuasiCompact f] [QuasiSeparated f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : IsRelativelyFreeModule f L)

/-- The morphism `X ⟶ ℙ_S(f_* L)` defined by the quotient `f^* f_* L ⟶ L` of an `f`-free
invertible sheaf `L`: the morphism to the relative `Proj` of `Sym(f_* L)` induced by the graded
map `Sym(f_* L) ⟶ f_* ⨁ L^{⊗ n}`. -/
public noncomputable def relativeEvaluationMorphism :
    X ⟶ projectiveBundle ((Scheme.Modules.pushforward f).obj L) :=
  toRelativeProj (directImageSymPowerMap f L) (coveringOpen_directImageSymPowerMap f L hL)

/-- `relativeEvaluationMorphism` lies over `S`. -/
@[reassoc (attr := simp)]
public theorem relativeEvaluationMorphism_comp_toBase :
    relativeEvaluationMorphism f L hL ≫
        projectiveBundleToBase ((Scheme.Modules.pushforward f).obj L) = f :=
  toRelativeProj_comp_toBase _ _

/-- The isomorphism `i^* 𝒪_{ℙ(f_* L)}(1) ≅ L` for `i = relativeEvaluationMorphism f L hL`. -/
public noncomputable def relativeEvaluationTwistIso :
    (Scheme.Modules.pullback (relativeEvaluationMorphism f L hL)).obj
        (Stacks.ProjectiveBundleSplitting.tautologicalTwist
          ((Scheme.Modules.pushforward f).obj L)
          (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)) ≅ L :=
  tautologicalTwistIso f L hL

/-- Under `relativeEvaluationTwistIso`, the pullback along `relativeEvaluationMorphism` of the
tautological quotient `π^* f_* L ⟶ 𝒪_{ℙ(f_* L)}(1)` is the evaluation map `f^* f_* L ⟶ L`. -/
public theorem tautologicalMap_relativeEvaluationTwistIso :
    (Scheme.Modules.pullbackCongr (relativeEvaluationMorphism_comp_toBase f L hL)).inv.app _ ≫
        (Scheme.Modules.pullbackComp (relativeEvaluationMorphism f L hL)
          (projectiveBundleToBase _)).inv.app _ ≫
        (Scheme.Modules.pullback (relativeEvaluationMorphism f L hL)).map
          (Stacks.ProjectiveBundleSplitting.tautologicalMap
            ((Scheme.Modules.pushforward f).obj L)
            (Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent _)) ≫
        (relativeEvaluationTwistIso f L hL).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app L :=
  tautologicalMap_comp_eq_counit f L hL

end RelativeEvaluation

open MMP.Proofs.lem_mmp_foundation_fa2_ample_powers_complete_relative_embedding in
/-- Let `h : V ⟶ Z` be a proper morphism of varieties over `k` and `A` an `h`-ample Cartier
divisor on `V`. For all sufficiently large `m`, the evaluation map `h^* h_* 𝒪_V(mA) ⟶ 𝒪_V(mA)`
is an epimorphism (`mA` is `h`-free), and the morphism
`relativeEvaluationMorphism : V ⟶ ℙ_Z(h_* 𝒪_V(mA))` over `Z` that it defines is a closed
immersion. Moreover `V ≅ Proj_Z ⨁_{n ≥ 0} h_* 𝒪_V(nA)` over `Z`. -/
@[mmp "lem_mmp_foundation_fa2_ample_powers_complete_relative_embedding"]
public theorem IsRelativelyAmpleCartier.eventually_isClosedImmersion_projectiveBundle
    {k : Type u} [Field k] {V Z : Scheme.{u}} (sV : V ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsIntegral V] [IsIntegral Z] [IsSeparated sV] [IsSeparated sZ]
    [LocallyOfFiniteType sV] [LocallyOfFiniteType sZ] [QuasiCompact sV] [QuasiCompact sZ]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (h : V ⟶ Z) [IsProper h] (hh : h ≫ sZ = sV) {A : Divisor V}
    (hA : IsRelativelyAmpleCartier h A) :
    (∀ᶠ m : ℕ in atTop,
      haveI := (hA.choose.nsmul m).isInvertibleModule_divisorialSheaf
      ∃ hfree : IsRelativelyFreeModule h (m • A).divisorialSheaf,
        IsClosedImmersion (relativeEvaluationMorphism h (m • A).divisorialSheaf hfree)) ∧
    haveI := hA.choose.isInvertibleModule_divisorialSheaf
    ∃ e : V ≅ (relativeProj (Stacks.RelativeAmple.directImageAlgebra h A.divisorialSheaf)).scheme,
      e.hom ≫ (relativeProj (Stacks.RelativeAmple.directImageAlgebra h A.divisorialSheaf)).toBase =
        h := by
  obtain ⟨hC, hAmp⟩ := hA
  haveI := hC.isInvertibleModule_divisorialSheaf
  have hL : Stacks.RelativeAmple.IsRelativelyAmple h A.divisorialSheaf :=
    ⟨inferInstance, hAmp⟩
  haveI : CompactSpace Z := (quasiCompact_iff_compactSpace sZ).mp inferInstance
  refine ⟨?_, ?_⟩
  · obtain ⟨d₀, -, hd⟩ :=
      Stacks.VeryAmplePowersQuasiCompactBase.eventuallyVeryAmplePower_of_isRelativelyAmple h _ hL
    filter_upwards [eventually_ge_atTop d₀] with m hm
    haveI := (hC.nsmul m).isInvertibleModule_divisorialSheaf
    have hva : IsRelativelyVeryAmple h (m • A).divisorialSheaf := by
      have := isRelativelyVeryAmple_of_isIso (𝟙 V) h
        (Stacks.Ample.tensorPowModule V A.divisorialSheaf (m : ℤ)) (m • A).divisorialSheaf
        (nsmulIso hC m ≪≫ ((Scheme.Modules.pullbackId V).app _).symm) (hd m hm)
      rwa [Category.id_comp] at this
    obtain ⟨_, hepi, himm⟩ :=
      ((tfae_isRelativelyVeryAmple h (m • A).divisorialSheaf).out 1 4).mp hva
    refine ⟨hepi, ?_⟩
    unfold relativeEvaluationMorphism
    have : IsSeparated (projectiveBundleToBase
        ((Scheme.Modules.pushforward h).obj (m • A).divisorialSheaf)) :=
      Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase _ _
    have : UniversallyClosed (toRelativeProj (directImageSymPowerMap h (m • A).divisorialSheaf)
          (coveringOpen_directImageSymPowerMap h _ hepi) ≫ projectiveBundleToBase
        ((Scheme.Modules.pushforward h).obj (m • A).divisorialSheaf)) := by
      rw [toRelativeProj_comp_toBase]; infer_instance
    have := UniversallyClosed.of_comp_of_isSeparated (toRelativeProj (directImageSymPowerMap h
        (m • A).divisorialSheaf) (coveringOpen_directImageSymPowerMap h _ hepi))
      (projectiveBundleToBase
        ((Scheme.Modules.pushforward h).obj (m • A).divisorialSheaf))
    exact IsClosedImmersion.of_isPreimmersion _ (Scheme.Hom.isClosedMap _).isClosed_range
  · haveI := Stacks.RelativeAmple.isIso_relativeAmpleProjHom h A.divisorialSheaf hL
    exact ⟨asIso (Stacks.RelativeAmple.relativeAmpleProjHom h A.divisorialSheaf hL),
      Stacks.RelativeAmple.relativeAmpleProjHom_toBase h A.divisorialSheaf hL⟩

end MMP.Flips

end

/-!
### Invertible sheaves and their isomorphisms descend along filtered colimits of algebras

Let `f : Z ⟶ Spec A` be quasi-compact and quasi-separated (for instance of finite presentation),
and let `B = colim_j R_j` be a filtered colimit of `A`-algebras. Write `Z_j = Z ×_A Spec R_j` and
`Z_B = Z ×_A Spec B`, so that `Z_B` is the cofiltered limit of the `Z_j` along affine transition
morphisms. Then every invertible sheaf on `Z_B` is, up to isomorphism, the pullback of an
invertible sheaf on some `Z_j`; and an isomorphism between the pullbacks to `Z_B` of two
invertible sheaves on a stage `Z_j` is, under the canonical identifications of iterated pullbacks,
the pullback of an isomorphism defined over a further stage `Z_k`.
-/

section

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (IsInvertible)
open Stacks.AlgebraicGeometry.ModuleLimits

namespace MMP.Proofs.lem_mmp_foundation_invertible_sheaf_filtered_descent

variable {A : CommRingCat.{u}} {Z : Scheme.{u}} (f : Z ⟶ Spec A)
    {J : Type u} [Category.{v} J] (R : J ⥤ Under A) (c : Cocone R)

/-- The base changes `Z ×_A Spec R_j`, as a diagram indexed by `Jᵒᵖ`. -/
private noncomputable abbrev stage : Jᵒᵖ ⥤ Scheme.{u} where
  obj j := pullback f (Spec.map (R.obj j.unop).hom)
  map g := pullback.map f _ f _ (𝟙 Z) (Spec.map (R.map g.unop).right) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp, Under.w])
  map_id j := by
    apply pullback.hom_ext <;> simp
  map_comp g h := by
    apply pullback.hom_ext <;>
      simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id, ← Spec.map_comp, ← Under.comp_right,
        unop_comp, Functor.map_comp]

/-- The base change `Z ×_A Spec B` as a cone over `stage`. -/
private noncomputable abbrev stageCone : Cone (stage f R) where
  pt := pullback f (Spec.map c.pt.hom)
  π :=
  { app j := pullback.map f _ f _ (𝟙 Z) (Spec.map (c.ι.app j.unop).right) (𝟙 _) (by simp)
      (by rw [Category.comp_id, ← Spec.map_comp, Under.w]; rfl)
    naturality j k g := by
      apply pullback.hom_ext <;>
        simp only [stage, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_snd_assoc, Category.comp_id, ← Spec.map_comp, ← Under.comp_right, c.w,
          Functor.const_obj_map] <;>
        exact Category.id_comp _ }

private lemma stage_map_fst {j k : Jᵒᵖ} (g : j ⟶ k) :
    (stage f R).map g ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private lemma stage_map_snd {j k : Jᵒᵖ} (g : j ⟶ k) :
    (stage f R).map g ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (R.map g.unop).right :=
  pullback.lift_snd _ _ _

private lemma stageCone_π_fst (j : Jᵒᵖ) :
    (stageCone f R c).π.app j ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private lemma stageCone_π_snd (j : Jᵒᵖ) :
    (stageCone f R c).π.app j ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (c.ι.app j.unop).right :=
  pullback.lift_snd _ _ _

/-- The first projections of a cone over `stage` to `Z` all agree. -/
private lemma cone_π_fst_eq [IsFiltered J] (s : Cone (stage f R)) (j k : Jᵒᵖ) :
    s.π.app j ≫ pullback.fst _ _ = s.π.app k ≫ pullback.fst _ _ := by
  obtain ⟨m, a, b, -⟩ := IsFilteredOrEmpty.cocone_objs j.unop k.unop
  rw [← s.w a.op, ← s.w b.op, Category.assoc, Category.assoc, stage_map_fst, stage_map_fst]

/-- The cone over the spectra of the `R_j` given by the second projections of a cone over
`stage`. -/
private noncomputable def specCone (s : Cone (stage f R)) :
    Cone ((R ⋙ Under.forget A).op ⋙ Scheme.Spec) where
  pt := s.pt
  π :=
  { app j := s.π.app j ≫ pullback.snd _ _
    naturality j k g := by
      have h := s.w g
      have h' := stage_map_snd f R g
      dsimp at h h' ⊢
      rw [Category.id_comp, ← h, Category.assoc, h']
      rfl }

/-- `Z ×_A Spec B` is the limit of the `Z ×_A Spec R_j`. -/
private noncomputable def isLimitStageCone [IsFiltered J] (hc : IsColimit c) :
    IsLimit (stageCone f R c) := by
  have hS : IsLimit (Scheme.Spec.mapCone ((Under.forget A).mapCocone c).op) :=
    isLimitOfPreserves _ (isColimitOfPreserves (Under.forget A) hc).op
  let j₀ : Jᵒᵖ := .op (IsFiltered.nonempty (C := J)).some
  let ℓ : ∀ s : Cone (stage f R), s.pt ⟶ Spec c.pt.right := fun s => hS.lift (specCone f R s)
  have hℓ : ∀ (s : Cone (stage f R)) (j : Jᵒᵖ),
      ℓ s ≫ Spec.map (c.ι.app j.unop).right = s.π.app j ≫ pullback.snd _ _ :=
    fun s j => hS.fac (specCone f R s) j
  have hlift : ∀ s : Cone (stage f R), ℓ s ≫ Spec.map c.pt.hom =
      s.π.app j₀ ≫ pullback.fst _ _ ≫ f := fun s => by
    have hw : Spec.map c.pt.hom =
        Spec.map (c.ι.app j₀.unop).right ≫ Spec.map (R.obj j₀.unop).hom :=
      (congrArg Spec.map (Under.w (c.ι.app j₀.unop))).symm.trans (Spec.map_comp _ _)
    rw [hw, ← Category.assoc, hℓ, Category.assoc, ← pullback.condition]
  exact
  { lift s := pullback.lift (s.π.app j₀ ≫ pullback.fst _ _) (ℓ s)
      (by rw [hlift, Category.assoc])
    fac s j := by
      apply pullback.hom_ext
      · rw [Category.assoc, stageCone_π_fst, pullback.lift_fst]
        exact cone_π_fst_eq f R s j₀ j
      · rw [Category.assoc, stageCone_π_snd, pullback.lift_snd_assoc]
        exact hℓ s j
    uniq s m hm := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, ← hm j₀, Category.assoc, stageCone_π_fst]
      · rw [pullback.lift_snd]
        refine hS.uniq (specCone f R s) _ (fun j => ?_)
        show (m ≫ pullback.snd _ _) ≫ Spec.map (c.ι.app j.unop).right =
          s.π.app j ≫ pullback.snd _ _
        rw [← hm j, Category.assoc, Category.assoc, stageCone_π_snd] }

variable {f R} in
/-- The transition morphisms of `stage` are base changes of morphisms of affine schemes. -/
private lemma isPullback_stage_map {j k : Jᵒᵖ} (g : j ⟶ k) :
    IsPullback (pullback.snd _ _) ((stage f R).map g) (Spec.map (R.map g.unop).right)
      (pullback.snd _ _) := by
  refine IsPullback.flip (IsPullback.of_right (h₁₂ := pullback.fst f _) (v₁₃ := f)
    (h₂₂ := Spec.map (R.obj k.unop).hom) ?_ (stage_map_snd f R g)
    (IsPullback.of_hasPullback f _))
  rw [stage_map_fst, ← Spec.map_comp, Under.w]
  exact IsPullback.of_hasPullback f _

private lemma isAffineHom_stage_map {j k : Jᵒᵖ} (g : j ⟶ k) : IsAffineHom ((stage f R).map g) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_stage_map g) inferInstance

private lemma compactSpace_stage_obj [QuasiCompact f] (j : Jᵒᵖ) :
    CompactSpace ((stage f R).obj j) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (Spec.map (R.obj j.unop).hom))

private lemma quasiSeparatedSpace_stage_obj [QuasiSeparated f] (j : Jᵒᵖ) :
    QuasiSeparatedSpace ((stage f R).obj j) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (Spec.map (R.obj j.unop).hom))

/-- An isomorphism between the pullbacks to the limit of two modules of finite presentation on a
stage descends, compatibly with the canonical identifications, to a further stage. -/
private lemma exists_iso_pullback_canonical {I : Type u} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (cc : Cone D)
    (hlim : IsLimit cc) (i : I) (L M : (D.obj i).Modules)
    [L.IsFinitePresentation] [M.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (cc.π.app i)).obj L ≅
      (Scheme.Modules.pullback (cc.π.app i)).obj M) :
    ∃ (n : I) (g : n ⟶ i)
      (ψ : (Scheme.Modules.pullback (D.map g)).obj L ≅ (Scheme.Modules.pullback (D.map g)).obj M),
      ∀ hp : cc.π.app n ≫ D.map g = cc.π.app i,
      (Scheme.Modules.pullback (cc.π.app n)).map ψ.hom ≫
          (Scheme.Modules.pullbackComp _ _).hom.app M ≫
            (Scheme.Modules.pullbackCongr hp).hom.app M =
        (Scheme.Modules.pullbackComp _ _).hom.app L ≫
          (Scheme.Modules.pullbackCongr hp).hom.app L ≫ φ.hom := by
  obtain ⟨m, e, φm, hφm⟩ := exists_map_of_pullback_canonical_of_isLimit' D cc hlim i L M φ.hom
  have hφmiso : IsIso ((Scheme.Modules.pullback (cc.π.app m)).map φm) := by
    have : IsIso ((Scheme.Modules.pullback (cc.π.app m)).map φm ≫
        canHom (cc.π.app m) (D.map e) (cc.π.app i) (cc.w e) M) := by
      rw [hφm]; infer_instance
    exact IsIso.of_isIso_comp_right _ (canHom (cc.π.app m) (D.map e) (cc.π.app i) (cc.w e) M)
  obtain ⟨n, g', hiso⟩ := exists_isIso_pullback_of_isLimit D cc hlim m _ _
    (isFinitePresentation_pullback (D.map e) L) (isFinitePresentation_pullback (D.map e) M)
    φm hφmiso
  let N := canNatIso (D.map g') (D.map e) (D.map (g' ≫ e)) (D.map_comp g' e).symm
  refine ⟨n, g' ≫ e,
    (N.app L).symm ≪≫ asIso ((Scheme.Modules.pullback (D.map g')).map φm) ≪≫ N.app M,
    fun hp => ?_⟩
  have key : (Scheme.Modules.pullback (cc.π.app n)).map
      (N.inv.app L ≫ (Scheme.Modules.pullback (D.map g')).map φm ≫ N.hom.app M) ≫
        canHom (cc.π.app n) (D.map (g' ≫ e)) (cc.π.app i) hp M =
      canHom (cc.π.app n) (D.map (g' ≫ e)) (cc.π.app i) hp L ≫ φ.hom := by
    have hnat := (canNatIso (cc.π.app n) (D.map g') (cc.π.app m) (cc.w g')).hom.naturality φm
    dsimp only [Functor.comp_map] at hnat
    rw [canNatIso_hom_app, canNatIso_hom_app] at hnat
    have hp' := fun F => canHom_comp (cc.π.app n) (D.map g') (D.map e) (cc.π.app m) (cc.w g')
      (D.map (g' ≫ e)) (D.map_comp g' e).symm (cc.π.app i) (cc.w e) hp F
    simp only [N, Functor.map_comp, Category.assoc, hp' M]
    rw [reassoc_of% hnat, hφm, ← reassoc_of% (hp' L), ← Category.assoc, ← Functor.map_comp]
    simp
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, asIso_hom]
  unfold canHom at key
  rw [Category.assoc] at key
  exact key

/-- `exists_iso_pullback_canonical` with the limit, the stages and the morphisms between them
replaced by any schemes and morphisms equal to them. -/
private lemma exists_iso_pullback_canonical_of_eq {I : Type u} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (cc : Cone D)
    (hlim : IsLimit cc) (i : I) {X W : Scheme.{u}} (hX : cc.pt = X) (hW : D.obj i = W)
    (L M : W.Modules) [L.IsFinitePresentation] [M.IsFinitePresentation] (P : X ⟶ W)
    (φ : (Scheme.Modules.pullback P).obj L ≅ (Scheme.Modules.pullback P).obj M)
    (hP : HEq (cc.π.app i) P) :
    ∃ (n : I) (g : n ⟶ i), ∀ (Y : Scheme.{u}) (_ : D.obj n = Y) (G : Y ⟶ W) (_ : HEq (D.map g) G)
      (Q : X ⟶ Y) (_ : HEq (cc.π.app n) Q) (hp : Q ≫ G = P),
      ∃ ψ : (Scheme.Modules.pullback G).obj L ≅ (Scheme.Modules.pullback G).obj M,
      (Scheme.Modules.pullback Q).map ψ.hom ≫
          (Scheme.Modules.pullbackComp _ _).hom.app M ≫
            (Scheme.Modules.pullbackCongr hp).hom.app M =
        (Scheme.Modules.pullbackComp _ _).hom.app L ≫
          (Scheme.Modules.pullbackCongr hp).hom.app L ≫ φ.hom := by
  subst hX hW
  obtain rfl := eq_of_heq hP
  obtain ⟨n, g, ψ, h⟩ := exists_iso_pullback_canonical D cc hlim i L M φ
  refine ⟨n, g, fun Y hY G hG Q hQ => ?_⟩
  subst hY
  obtain rfl := eq_of_heq hG
  obtain rfl := eq_of_heq hQ
  exact fun hp => ⟨ψ, h hp⟩

/-- The projection from `Z ×_A Spec B` to the stage at `j`, written out. -/
private lemma stageCone_π_app_op (j : J) :
    (stageCone f R c).π.app (.op j) =
      pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
        (Spec.map (c.ι.app j).right) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, Under.w]; rfl) := rfl

/-- The transition morphism of `stage` along `g`, written out. -/
private lemma stage_map_op {j k : J} (g : j ⟶ k) :
    (stage f R).map g.op =
      pullback.map f (Spec.map (R.obj k).hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
        (Spec.map (R.map g).right) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, Under.w]) := rfl

end MMP.Proofs.lem_mmp_foundation_invertible_sheaf_filtered_descent

namespace MMP

open MMP.Proofs.lem_mmp_foundation_invertible_sheaf_filtered_descent in
/-- Let `f : Z ⟶ Spec A` be quasi-compact and quasi-separated and let `c` be a colimit cocone of a
filtered diagram `R` of `A`-algebras, with point `B`. Every invertible sheaf on `Z ×_A Spec B` is
isomorphic to the pullback of an invertible sheaf on some `Z ×_A Spec R_j`, and every isomorphism
`φ` between the pullbacks to `Z ×_A Spec B` of two invertible sheaves on `Z ×_A Spec R_j` is, after
the canonical identifications, the pullback of an isomorphism over `Z ×_A Spec R_k` for some
`g : j ⟶ k`. -/
@[mmp "lem_mmp_foundation_invertible_sheaf_filtered_descent"]
public theorem exists_isInvertible_pullback_iso_of_isColimit_under
    {A : CommRingCat.{u}} {Z : Scheme.{u}} (f : Z ⟶ Spec A) [QuasiCompact f] [QuasiSeparated f]
    {J : Type u} [Category.{v} J] [IsFiltered J] (R : J ⥤ Under A) (c : Cocone R)
    (hc : IsColimit c) :
    (∀ L : (pullback f (Spec.map c.pt.hom)).Modules,
      IsInvertible (pullback f (Spec.map c.pt.hom)).sheaf.obj
        (pullback f (Spec.map c.pt.hom)).ringCatSheaf.property L →
      ∃ (j : J) (Lj : (pullback f (Spec.map (R.obj j).hom)).Modules),
        IsInvertible (pullback f (Spec.map (R.obj j).hom)).sheaf.obj
          (pullback f (Spec.map (R.obj j).hom)).ringCatSheaf.property Lj ∧
        Nonempty (L ≅ (Scheme.Modules.pullback
          (pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
            (Spec.map (c.ι.app j).right) (𝟙 _)
            ((Category.comp_id f).trans (Category.id_comp f).symm)
            ((Category.comp_id _).trans
              ((congrArg Spec.map (Under.w (c.ι.app j))).symm.trans (Spec.map_comp _ _))))).obj
            Lj)) ∧
    (∀ (j : J) (L₀ M₀ : (pullback f (Spec.map (R.obj j).hom)).Modules),
      IsInvertible (pullback f (Spec.map (R.obj j).hom)).sheaf.obj
        (pullback f (Spec.map (R.obj j).hom)).ringCatSheaf.property L₀ →
      IsInvertible (pullback f (Spec.map (R.obj j).hom)).sheaf.obj
        (pullback f (Spec.map (R.obj j).hom)).ringCatSheaf.property M₀ →
      ∀ φ : (Scheme.Modules.pullback
          (pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
            (Spec.map (c.ι.app j).right) (𝟙 _)
            ((Category.comp_id f).trans (Category.id_comp f).symm)
            ((Category.comp_id _).trans
              ((congrArg Spec.map (Under.w (c.ι.app j))).symm.trans (Spec.map_comp _ _))))).obj L₀ ≅
          (Scheme.Modules.pullback
          (pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
            (Spec.map (c.ι.app j).right) (𝟙 _)
            ((Category.comp_id f).trans (Category.id_comp f).symm)
            ((Category.comp_id _).trans
              ((congrArg Spec.map (Under.w (c.ι.app j))).symm.trans (Spec.map_comp _ _))))).obj M₀,
      ∃ (k : J) (g : j ⟶ k)
        (ψ : (Scheme.Modules.pullback
            (pullback.map f (Spec.map (R.obj k).hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
              (Spec.map (R.map g).right) (𝟙 _)
              ((Category.comp_id f).trans (Category.id_comp f).symm)
              ((Category.comp_id _).trans
                ((congrArg Spec.map (Under.w (R.map g))).symm.trans (Spec.map_comp _ _))))).obj L₀ ≅
          (Scheme.Modules.pullback
            (pullback.map f (Spec.map (R.obj k).hom) f (Spec.map (R.obj j).hom) (𝟙 Z)
              (Spec.map (R.map g).right) (𝟙 _)
              ((Category.comp_id f).trans (Category.id_comp f).symm)
              ((Category.comp_id _).trans
                ((congrArg Spec.map (Under.w (R.map g))).symm.trans (Spec.map_comp _ _))))).obj
            M₀),
        (Scheme.Modules.pullback
            (pullback.map f (Spec.map c.pt.hom) f (Spec.map (R.obj k).hom) (𝟙 Z)
              (Spec.map (c.ι.app k).right) (𝟙 _)
              ((Category.comp_id f).trans (Category.id_comp f).symm)
              ((Category.comp_id _).trans
                ((congrArg Spec.map (Under.w (c.ι.app k))).symm.trans (Spec.map_comp _ _))))).map
            ψ.hom ≫
          (Scheme.Modules.pullbackComp _ _).hom.app M₀ ≫
          (Scheme.Modules.pullbackCongr (pullbackMap_cocone_comp_transition f R c g)).hom.app M₀ =
        (Scheme.Modules.pullbackComp _ _).hom.app L₀ ≫
          (Scheme.Modules.pullbackCongr (pullbackMap_cocone_comp_transition f R c g)).hom.app L₀ ≫
            φ.hom) := by
  have : ∀ {j k : Jᵒᵖ} (g : j ⟶ k), IsAffineHom ((stage f R).map g) :=
    isAffineHom_stage_map f R
  have := compactSpace_stage_obj f R
  have := quasiSeparatedSpace_stage_obj f R
  have hlim := isLimitStageCone f R c hc
  refine ⟨fun L hL => ?_, fun j L₀ M₀ hL hM φ => ?_⟩
  · obtain ⟨⟨i⟩, Li, hLi, e⟩ :=
      exists_isInvertible_pullback_iso_of_isLimit (stage f R) (stageCone f R c) hlim L hL
    exact ⟨i, Li, hLi, e⟩
  have := @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ L₀ hL
  have := @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible _ M₀ hM
  obtain ⟨n, g, H⟩ := exists_iso_pullback_canonical_of_eq (stage f R) (stageCone f R c) hlim
    (.op j) (X := pullback f (Spec.map c.pt.hom)) (W := pullback f (Spec.map (R.obj j).hom))
    rfl rfl L₀ M₀ _ φ (heq_of_eq (stageCone_π_app_op f R c j))
  obtain ⟨k, rfl⟩ : ∃ k : J, n = .op k := ⟨n.unop, rfl⟩
  obtain ⟨g, rfl⟩ : ∃ g' : j ⟶ k, g = g'.op := ⟨g.unop, rfl⟩
  refine ⟨k, g, ?_⟩
  refine H (pullback f (Spec.map (R.obj k).hom)) rfl _ ?_ _ ?_ _
  · exact heq_of_eq (stage_map_op f R g)
  · exact heq_of_eq (stageCone_π_app_op f R c k)

end MMP

end

/-!
### A proper birational morphism to a normal variety is an isomorphism off codimension two

Let `f : Y ⟶ X` be a proper birational morphism of varieties over a field `k`, with `X` normal.
Then there is an open `V ⊆ X` whose closed complement has codimension at least two such that
`f` restricts to an isomorphism `f⁻¹(V) ⟶ V`.
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Mori

/-- A proper birational `k`-morphism `f : Y ⟶ X` of varieties with `X` normal is an isomorphism
over an open `V ⊆ X` whose complement has codimension at least two. -/
@[mmp "lem_mmp_foundation_km3a_birational_codimension_two"]
public theorem exists_isIso_morphismRestrict_two_le_closedsCodimension (k : Type u) [Field k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hY : IsVariety k sY) (f : Y ⟶ X) (hf : f ≫ sX = sY)
    [IsProper f] (hbir : IsBirationalMorphism f) :
    ∃ V : X.Opens, 2 ≤ closedsCodimension V.compl ∧ IsIso (f ∣_ V) := by
  haveI : IsNormal X := hX.2
  haveI : IsVariety k sX := hX.1
  haveI : IsVariety k (f ≫ sX) := hf ▸ hY
  exact ⟨biregularLocus f, two_le_closedsCodimension_compl_biregularLocus sX f hbir,
    isBiregular_biregularLocus f⟩

end MMP.Mori

end

/-!
### The weighted monomial order of a two-dimensional regular local ring

Let `(R, 𝔪)` be a two-dimensional regular local ring with regular system of parameters
`(x, y)`, and let `w ≥ 1`. Let `I_ν` be the ideal generated by the monomials `x^i y^j` with
`i + w j ≥ ν`, and `v(s) = sup {ν : s ∈ I_ν} ∈ ℕ ∪ {∞}` the weighted order
(`MMP.Resolution.monomialValuation x y w`). Then `v` is finite on nonzero elements, additive on
products, satisfies `v(s + t) ≥ min (v s) (v t)`, and extends uniquely to an additive valuation
of the fraction field `K` of `R`.
-/

section

open MvPolynomial IsLocalRing

namespace MMP.Proofs.lem_mmp_resolution_weighted_monomial_valuation

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private theorem span_pair_eq {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) :
    Ideal.span {x, y} = maximalIdeal R := by
  rw [← hxy.1, Matrix.range_cons_cons_empty]

/-- A polynomial vanishes modulo `I` exactly when all of its coefficients lie in `I`. -/
private theorem map_mk_eq_zero_iff {σ : Type*} {I : Ideal R} {P : MvPolynomial σ R} :
    P.map (Ideal.Quotient.mk I) = 0 ↔ ∀ e, P.coeff e ∈ I := by
  simp [MvPolynomial.ext_iff, coeff_map, Ideal.Quotient.eq_zero_iff_mem]

/-- Degree-`d` forms in a regular system of parameters `(x, y)` with value in `𝔪^(d+1)` have all
coefficients in `𝔪`. -/
private theorem coeff_mem_of_isHomogeneous {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {d : ℕ}
    {P : MvPolynomial (Fin 2) R} (hP : P.IsHomogeneous d)
    (hev : aeval ![x, y] P ∈ maximalIdeal R ^ (d + 1)) (e : Fin 2 →₀ ℕ) :
    P.coeff e ∈ maximalIdeal R := by
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hxy
  have hxs : Ideal.ofList [x, y] = maximalIdeal R := by
    rw [← span_pair_eq hxy, Ideal.ofList]
    congr 1
    ext
    simp
  have hmin : [x, y].length = (maximalIdeal R).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hxy.2] at h
    simp only [List.length_cons, List.length_nil]
    exact_mod_cast h.symm
  have hv : (fun i : Fin [x, y].length => [x, y][i]) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  have hx : ∀ i : Fin [x, y].length, [x, y][i] ∈ maximalIdeal R := fun i => by
    rw [← hxs]
    exact Ideal.subset_span (List.getElem_mem _)
  have hinj := (IsRegularLocalRing.gradedRingEquivMvPolynomial [x, y] hxs hmin hx).injective
  have hmap := AssociatedGraded.polyGradedHom_map (maximalIdeal R)
    (fun i : Fin [x, y].length => [x, y][i]) hx (P := P) hP
  refine map_mk_eq_zero_iff.mp ?_ e
  apply hinj
  rw [map_zero]
  change AssociatedGraded.polyGradedHom _ _ hx _ = 0
  rw [hmap, MMP.Flips.associatedGraded_classOfPow_eq_zero_iff]
  change eval (fun i : Fin [x, y].length => [x, y][i]) P ∈ _
  rw [hv, ← MvPolynomial.coe_aeval_eq_eval]
  exact hev

private theorem weight_eq (w : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.weight ![1, w] e = e 0 + w * e 1 := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, mul_comm]

private theorem degree_eq (e : Fin 2 →₀ ℕ) : e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem aeval_monomial_eq (x y : R) (e : Fin 2 →₀ ℕ) (c : R) :
    aeval ![x, y] (monomial e c) = c * (x ^ e 0 * y ^ e 1) := by
  simp [MvPolynomial.aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two]

private theorem aeval_eq_sum (x y : R) (P : MvPolynomial (Fin 2) R) :
    aeval ![x, y] P = ∑ e ∈ P.support, P.coeff e * (x ^ e 0 * y ^ e 1) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  simp only [aeval_monomial_eq]

/-- Membership in `I_ν` is being the value of a polynomial all of whose monomials have weight
at least `ν`. -/
private theorem mem_monomialIdeal_iff {x y : R} {w ν : ℕ} {r : R} :
    r ∈ MMP.Resolution.monomialIdeal x y w ν ↔
      ∃ P : MvPolynomial (Fin 2) R, (∀ e ∈ P.support, ν ≤ Finsupp.weight ![1, w] e) ∧
        aeval ![x, y] P = r := by
  constructor
  · intro hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨i, j, hij, rfl⟩ := hr
      refine ⟨monomial (Finsupp.single 0 i + Finsupp.single 1 j) 1, fun e he => ?_, ?_⟩
      · rw [Finset.mem_singleton.mp (support_monomial_subset he), weight_eq]
        simpa using hij
      · simp [aeval_monomial_eq]
    | zero => exact ⟨0, by simp, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨P, hP, rfl⟩ := ha
      obtain ⟨Q, hQ, rfl⟩ := hb
      refine ⟨P + Q, fun e he => ?_, map_add _ _ _⟩
      rcases Finset.mem_union.mp (support_add he) with h | h
      exacts [hP e h, hQ e h]
    | smul a b _ hb =>
      obtain ⟨P, hP, rfl⟩ := hb
      exact ⟨a • P, fun e he => hP e (support_smul he), map_smul _ _ _⟩
  · rintro ⟨P, hP, rfl⟩
    rw [aeval_eq_sum]
    refine Ideal.sum_mem _ fun e he => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    exact ⟨e 0, e 1, (weight_eq w e) ▸ hP e he, rfl⟩

private theorem aeval_mem_pow {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y])
    {n : ℕ} {P : MvPolynomial (Fin 2) R} (hP : ∀ e ∈ P.support, n ≤ e.degree) :
    aeval ![x, y] P ∈ maximalIdeal R ^ n := by
  have hx : x ∈ maximalIdeal R := hxy.1 ▸ Ideal.subset_span ⟨0, rfl⟩
  have hy : y ∈ maximalIdeal R := hxy.1 ▸ Ideal.subset_span ⟨1, rfl⟩
  rw [aeval_eq_sum]
  refine Ideal.sum_mem _ fun e he => Ideal.mul_mem_left _ _ ?_
  have := hP e he
  rw [degree_eq] at this
  refine Ideal.pow_le_pow_right this ?_
  rw [pow_add]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)

/-- A polynomial with coefficients in `(x, y)` has the same value as one whose monomials are
those of the original multiplied by a variable. -/
private theorem exists_shift {x y : R} {P : MvPolynomial (Fin 2) R}
    (hP : ∀ e, P.coeff e ∈ Ideal.span {x, y}) :
    ∃ Q : MvPolynomial (Fin 2) R,
      (∀ e' ∈ Q.support, ∃ e ∈ P.support, ∃ i, e' = e + Finsupp.single i 1) ∧
        aeval ![x, y] Q = aeval ![x, y] P := by
  classical
  choose α β hαβ using fun e => Ideal.mem_span_pair.mp (hP e)
  refine ⟨∑ e ∈ P.support, (monomial (e + Finsupp.single 0 1) (α e) +
    monomial (e + Finsupp.single 1 1) (β e)), ?_, ?_⟩
  · intro e' he'
    obtain ⟨e, he, h⟩ := Finset.mem_biUnion.mp (support_sum he')
    rcases Finset.mem_union.mp (support_add h) with h | h
    · exact ⟨e, he, 0, Finset.mem_singleton.mp (support_monomial_subset h)⟩
    · exact ⟨e, he, 1, Finset.mem_singleton.mp (support_monomial_subset h)⟩
  · rw [aeval_eq_sum x y P, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_add, aeval_monomial_eq, aeval_monomial_eq, ← hαβ e]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_true, if_false, add_zero]
    ring

private theorem aeval_sub_homogeneousComponent_mem {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {n : ℕ} {D : MvPolynomial (Fin 2) R}
    (hD : ∀ e ∈ D.support, n ≤ e.degree) :
    aeval ![x, y] (D - homogeneousComponent n D) ∈ maximalIdeal R ^ (n + 1) := by
  refine aeval_mem_pow hxy fun e he => ?_
  rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at he
  split_ifs at he with h
  · simp at he
  · have := hD e (mem_support_iff.mpr (by simpa using he)); omega

/-- For an upward-closed set `M` of monomials, an element of `(x^e : e ∈ M) ∩ 𝔪^d` lies in the
ideal generated by the monomials of `M` of degree at least `d`. -/
private theorem exists_degree_le_of_mem_pow {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {M : Set (Fin 2 →₀ ℕ)}
    (hM : ∀ e ∈ M, ∀ i, e + Finsupp.single i 1 ∈ M) {P : MvPolynomial (Fin 2) R}
    (hP : ∀ e ∈ P.support, e ∈ M) (d : ℕ) (hd : aeval ![x, y] P ∈ maximalIdeal R ^ d) :
    ∃ Q : MvPolynomial (Fin 2) R, (∀ e ∈ Q.support, e ∈ M ∧ d ≤ e.degree) ∧
      aeval ![x, y] Q = aeval ![x, y] P := by
  induction d with
  | zero => exact ⟨P, fun e he => ⟨hP e he, Nat.zero_le _⟩, rfl⟩
  | succ d ih =>
    obtain ⟨Q, hQ, hQP⟩ := ih (Ideal.pow_le_pow_right (Nat.le_succ d) hd)
    have hlow := aeval_sub_homogeneousComponent_mem hxy (fun e he => (hQ e he).2)
    have hH : aeval ![x, y] (homogeneousComponent d Q) ∈ maximalIdeal R ^ (d + 1) := by
      have : aeval ![x, y] (homogeneousComponent d Q) =
          aeval ![x, y] Q - aeval ![x, y] (Q - homogeneousComponent d Q) := by
        rw [map_sub]; ring
      rw [this, hQP]; exact Ideal.sub_mem _ hd hlow
    have hc := coeff_mem_of_isHomogeneous hxy (homogeneousComponent_isHomogeneous d Q) hH
    obtain ⟨H', hH', hH'H⟩ := exists_shift (fun e => (span_pair_eq hxy) ▸ hc e)
    refine ⟨H' + (Q - homogeneousComponent d Q), fun e he => ?_, ?_⟩
    · rcases Finset.mem_union.mp (support_add he) with h | h
      · obtain ⟨e₀, he₀, i, rfl⟩ := hH' e h
        rw [mem_support_iff, coeff_homogeneousComponent] at he₀
        split_ifs at he₀ with hdeg
        · refine ⟨hM _ (hQ e₀ (mem_support_iff.mpr he₀)).1 i, ?_⟩
          rw [degree_eq] at hdeg ⊢
          fin_cases i <;> simp <;> omega
        · exact absurd rfl he₀
      · rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at h
        split_ifs at h with hdeg
        · simp at h
        · have := hQ e (mem_support_iff.mpr (by simpa using h)); exact ⟨this.1, by omega⟩
    · rw [map_add, hH'H, map_sub, hQP]; ring

/-- A polynomial with coefficients in `𝔪` whose monomials have weight at least `a` has value in
`I_(a+1)`. -/
private theorem aeval_mem_monomialIdeal_succ {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) {a : ℕ}
    {P : MvPolynomial (Fin 2) R} (hP : ∀ e ∈ P.support, a ≤ Finsupp.weight ![1, w] e)
    (hc : ∀ e, P.coeff e ∈ maximalIdeal R) :
    aeval ![x, y] P ∈ MMP.Resolution.monomialIdeal x y w (a + 1) := by
  obtain ⟨Q, hQ, hQP⟩ := exists_shift (fun e => (span_pair_eq hxy).symm ▸ hc e)
  rw [← hQP]
  refine mem_monomialIdeal_iff.mpr ⟨Q, fun e' he' => ?_, rfl⟩
  obtain ⟨e, he, i, rfl⟩ := hQ e' he'
  have := hP e he
  rw [weight_eq] at this ⊢
  fin_cases i <;> simp <;> nlinarith

/-- **Weighted initial forms.** A weighted-homogeneous form of weight `a` whose value lies in
`I_(a+1)` has all its coefficients in `𝔪`. -/
private theorem coeff_mem_of_isWeightedHomogeneous {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) {a : ℕ}
    {P : MvPolynomial (Fin 2) R} (hP : P.IsWeightedHomogeneous ![1, w] a)
    (hev : aeval ![x, y] P ∈ MMP.Resolution.monomialIdeal x y w (a + 1)) (e : Fin 2 →₀ ℕ) :
    P.coeff e ∈ maximalIdeal R := by
  classical
  suffices h : ∀ n, ∀ e : Fin 2 →₀ ℕ, e.degree = n → P.coeff e ∈ maximalIdeal R from h _ e rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro e he
  set Plow := ∑ k ∈ Finset.range n, homogeneousComponent k P with hPlow
  have hcl : ∀ f, Plow.coeff f = if f.degree < n then P.coeff f else 0 := by
    intro f
    simp only [Plow, coeff_sum, coeff_homogeneousComponent, Finset.sum_ite_eq, Finset.mem_range]
  have hlowI : aeval ![x, y] Plow ∈ MMP.Resolution.monomialIdeal x y w (a + 1) := by
    refine aeval_mem_monomialIdeal_succ hxy hw (fun f hf => ?_) (fun f => ?_)
    · rw [mem_support_iff, hcl] at hf
      split_ifs at hf with h
      · exact (hP hf).symm.le
      · exact absurd rfl hf
    · rw [hcl]; split_ifs with h
      · exact ih _ h f rfl
      · exact zero_mem _
  set P' := P - Plow
  have hP'I : aeval ![x, y] P' ∈ MMP.Resolution.monomialIdeal x y w (a + 1) := by
    simp only [P', map_sub]; exact Ideal.sub_mem _ hev hlowI
  have hP'deg : ∀ f ∈ P'.support, n ≤ f.degree := by
    intro f hf
    rw [mem_support_iff, coeff_sub, hcl] at hf
    split_ifs at hf with h
    · simp at hf
    · omega
  obtain ⟨T, hT, hTP⟩ := mem_monomialIdeal_iff.mp hP'I
  obtain ⟨Q, hQ, hQT⟩ := exists_degree_le_of_mem_pow hxy
    (M := {f | a + 1 ≤ Finsupp.weight ![1, w] f})
    (fun f hf i => by
      simp only [Set.mem_setOf_eq, map_add] at hf ⊢; omega)
    hT n (hTP ▸ aeval_mem_pow hxy hP'deg)
  set D := P' - Q
  have hD0 : aeval ![x, y] D = 0 := by simp only [D, map_sub, hQT, hTP, sub_self]
  have hDdeg : ∀ f ∈ D.support, n ≤ f.degree := by
    intro f hf
    rw [mem_support_iff, coeff_sub] at hf
    by_cases h : P'.coeff f = 0
    · rw [h, zero_sub, neg_ne_zero] at hf; exact (hQ f (mem_support_iff.mpr hf)).2
    · exact hP'deg f (mem_support_iff.mpr h)
  have hHD : aeval ![x, y] (homogeneousComponent n D) ∈ maximalIdeal R ^ (n + 1) := by
    have h := aeval_sub_homogeneousComponent_mem hxy hDdeg
    rw [map_sub, hD0, zero_sub, neg_mem_iff] at h
    exact h
  have hc := coeff_mem_of_isHomogeneous hxy (homogeneousComponent_isHomogeneous n D) hHD e
  rw [coeff_homogeneousComponent, if_pos he] at hc
  by_cases hPe : P.coeff e = 0
  · rw [hPe]; exact zero_mem _
  have hQe : Q.coeff e = 0 := by
    by_contra h
    have h1 := (hQ e (mem_support_iff.mpr h)).1
    have h2 := hP hPe
    simp only [Set.mem_setOf_eq] at h1
    omega
  simpa [D, P', coeff_sub, hcl, he, hQe] using hc

private theorem mul_mem_monomialIdeal {x y : R} {w m n : ℕ} {r s : R}
    (hr : r ∈ MMP.Resolution.monomialIdeal x y w m)
    (hs : s ∈ MMP.Resolution.monomialIdeal x y w n) :
    r * s ∈ MMP.Resolution.monomialIdeal x y w (m + n) := by
  classical
  obtain ⟨P, hP, rfl⟩ := mem_monomialIdeal_iff.mp hr
  obtain ⟨Q, hQ, rfl⟩ := mem_monomialIdeal_iff.mp hs
  refine mem_monomialIdeal_iff.mpr ⟨P * Q, fun e he => ?_, map_mul _ _ _⟩
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Finset.mem_add.mp (support_mul P Q he)
  rw [map_add]
  exact add_le_add (hP e₁ he₁) (hQ e₂ he₂)

/-- An element `s ∈ I_a ∖ I_(a+1)` has a weighted initial form of weight `a`: a
weighted-homogeneous `Pa` of weight `a`, not all of whose coefficients lie in `𝔪`, with
`s - Pa(x, y) ∈ I_(a+1)`. -/
private theorem exists_initialForm {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) {a : ℕ} {s : R}
    (hs : s ∈ MMP.Resolution.monomialIdeal x y w a)
    (hs' : s ∉ MMP.Resolution.monomialIdeal x y w (a + 1)) :
    ∃ Pa : MvPolynomial (Fin 2) R, Pa.IsWeightedHomogeneous ![1, w] a ∧
      (∃ e, Pa.coeff e ∉ maximalIdeal R) ∧
      s - aeval ![x, y] Pa ∈ MMP.Resolution.monomialIdeal x y w (a + 1) := by
  classical
  obtain ⟨P, hP, rfl⟩ := mem_monomialIdeal_iff.mp hs
  set Pa := weightedHomogeneousComponent ![1, w] a P
  have hPa := weightedHomogeneousComponent_isWeightedHomogeneous (R := R) (w := ![1, w]) a P
  have hrest :
      aeval ![x, y] P - aeval ![x, y] Pa ∈ MMP.Resolution.monomialIdeal x y w (a + 1) := by
    rw [← map_sub]
    refine mem_monomialIdeal_iff.mpr ⟨P - Pa, fun e he => ?_, rfl⟩
    rw [mem_support_iff, coeff_sub, coeff_weightedHomogeneousComponent] at he
    split_ifs at he with h
    · simp at he
    · have := hP e (mem_support_iff.mpr (by simpa using he)); omega
  refine ⟨Pa, hPa, ?_, hrest⟩
  by_contra hc
  simp only [not_exists, not_not] at hc
  refine hs' ?_
  have h := aeval_mem_monomialIdeal_succ hxy hw (P := Pa) (a := a)
    (fun e he => (hPa (mem_support_iff.mp he)).symm.le) hc
  simpa using Ideal.add_mem _ hrest h

/-- **Multiplicativity of weighted initial forms**: if `s ∈ I_a ∖ I_(a+1)` and
`t ∈ I_b ∖ I_(b+1)`, then `st ∉ I_(a+b+1)`, since the initial forms have nonzero product in the
polynomial domain `κ[X, Y]`. -/
private theorem mul_notMem_monomialIdeal {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) {a b : ℕ}
    {s t : R} (hs : s ∈ MMP.Resolution.monomialIdeal x y w a)
    (hs' : s ∉ MMP.Resolution.monomialIdeal x y w (a + 1))
    (ht : t ∈ MMP.Resolution.monomialIdeal x y w b)
    (ht' : t ∉ MMP.Resolution.monomialIdeal x y w (b + 1)) :
    s * t ∉ MMP.Resolution.monomialIdeal x y w (a + b + 1) := by
  intro hst
  obtain ⟨P, hP, ⟨e, he⟩, hsP⟩ := exists_initialForm hxy hw hs hs'
  obtain ⟨Q, hQ, ⟨f, hf⟩, htQ⟩ := exists_initialForm hxy hw ht ht'
  have hPI : aeval ![x, y] P ∈ MMP.Resolution.monomialIdeal x y w a :=
    mem_monomialIdeal_iff.mpr ⟨P, fun e he => (hP (mem_support_iff.mp he)).symm.le, rfl⟩
  have hPQ : aeval ![x, y] (P * Q) ∈ MMP.Resolution.monomialIdeal x y w (a + b + 1) := by
    have h1 := mul_mem_monomialIdeal hsP ht
    have h2 := mul_mem_monomialIdeal hPI htQ
    rw [show a + 1 + b = a + b + 1 by omega] at h1
    rw [show a + (b + 1) = a + b + 1 by omega] at h2
    have : aeval ![x, y] (P * Q) =
        s * t - (s - aeval ![x, y] P) * t - aeval ![x, y] P * (t - aeval ![x, y] Q) := by
      rw [map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hst h1) h2
  have h0 := map_mk_eq_zero_iff.mpr (coeff_mem_of_isWeightedHomogeneous hxy hw (hP.mul hQ) hPQ)
  rw [map_mul, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  exacts [he (map_mk_eq_zero_iff.mp h0 e), hf (map_mk_eq_zero_iff.mp h0 f)]

/-! ### The weighted order -/

private theorem monomialIdeal_antitone {x y : R} {w ν ν' : ℕ} (h : ν ≤ ν') :
    MMP.Resolution.monomialIdeal x y w ν' ≤ MMP.Resolution.monomialIdeal x y w ν :=
  Ideal.span_mono fun _ ⟨i, j, hij, hr⟩ => ⟨i, j, h.trans hij, hr⟩

private theorem one_mem_monomialIdeal_zero (x y : R) (w : ℕ) :
    (1 : R) ∈ MMP.Resolution.monomialIdeal x y w 0 :=
  Ideal.subset_span ⟨0, 0, le_rfl, by simp⟩

private theorem monomialIdeal_le_pow {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w ν d : ℕ}
    (h : ∀ e : Fin 2 →₀ ℕ, ν ≤ Finsupp.weight ![1, w] e → d ≤ e.degree) :
    MMP.Resolution.monomialIdeal x y w ν ≤ maximalIdeal R ^ d := fun r hr => by
  obtain ⟨P, hP, rfl⟩ := mem_monomialIdeal_iff.mp hr
  exact aeval_mem_pow hxy fun e he => h e (hP e he)

private theorem monomialValuation_zero (x y : R) (w : ℕ) :
    MMP.Resolution.monomialValuation x y w 0 = ⊤ :=
  top_le_iff.mp <| ENat.forall_natCast_le_iff_le.mp fun n _ =>
    le_iSup₂_of_le (f := fun ν (_ : (0 : R) ∈ MMP.Resolution.monomialIdeal x y w ν) => (ν : ℕ∞))
      n (zero_mem _) le_rfl

private theorem monomialValuation_eq {x y : R} {w a : ℕ} {s : R}
    (hs : s ∈ MMP.Resolution.monomialIdeal x y w a)
    (hs' : s ∉ MMP.Resolution.monomialIdeal x y w (a + 1)) :
    MMP.Resolution.monomialValuation x y w s = a := by
  refine le_antisymm (iSup₂_le fun ν hν => ?_)
    (le_iSup₂ (f := fun ν (_ : s ∈ MMP.Resolution.monomialIdeal x y w ν) => (ν : ℕ∞)) a hs)
  by_contra h
  exact hs' (monomialIdeal_antitone (by exact_mod_cast not_le.mp h) hν)

private theorem exists_mem_notMem {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) {s : R}
    (hs : s ≠ 0) :
    ∃ a, s ∈ MMP.Resolution.monomialIdeal x y w a ∧
      s ∉ MMP.Resolution.monomialIdeal x y w (a + 1) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, s ∉ maximalIdeal R ^ n := by
    by_contra h
    push Not at h
    apply hs
    rwa [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
      (maximalIdeal.isMaximal R).ne_top, Submodule.mem_iInf]
  have hex : ∃ ν, s ∉ MMP.Resolution.monomialIdeal x y w ν := by
    refine ⟨w * n, fun h => hn (monomialIdeal_le_pow hxy (fun e he => ?_) h)⟩
    rw [weight_eq] at he
    rw [degree_eq]
    nlinarith
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this (by simpa using Ideal.mul_mem_left _ s (one_mem_monomialIdeal_zero x y w))
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    simpa using this
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    exact Nat.find_spec hex

private theorem natCast_le_monomialValuation_iff {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) {ν : ℕ} {s : R} :
    (ν : ℕ∞) ≤ MMP.Resolution.monomialValuation x y w s ↔
      s ∈ MMP.Resolution.monomialIdeal x y w ν := by
  refine ⟨fun h => ?_, fun h =>
    le_iSup₂ (f := fun ν (_ : s ∈ MMP.Resolution.monomialIdeal x y w ν) => (ν : ℕ∞)) ν h⟩
  by_cases hs : s = 0
  · rw [hs]; exact zero_mem _
  obtain ⟨a, ha, ha'⟩ := exists_mem_notMem hxy hw hs
  rw [monomialValuation_eq ha ha'] at h
  exact monomialIdeal_antitone (by exact_mod_cast h) ha

/-- The weighted order is additive on products: the content of `mul_notMem_monomialIdeal`. -/
private theorem monomialValuation_mul {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) (s t : R) :
    MMP.Resolution.monomialValuation x y w (s * t) =
      MMP.Resolution.monomialValuation x y w s + MMP.Resolution.monomialValuation x y w t := by
  by_cases hs : s = 0
  · simp [hs, monomialValuation_zero]
  by_cases ht : t = 0
  · simp [ht, monomialValuation_zero]
  obtain ⟨a, ha, ha'⟩ := exists_mem_notMem hxy hw hs
  obtain ⟨b, hb, hb'⟩ := exists_mem_notMem hxy hw ht
  rw [monomialValuation_eq ha ha', monomialValuation_eq hb hb',
    monomialValuation_eq (mul_mem_monomialIdeal ha hb)
      (mul_notMem_monomialIdeal hxy hw ha ha' hb hb')]
  push_cast; rfl

private theorem min_le_monomialValuation_add {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) (s t : R) :
    min (MMP.Resolution.monomialValuation x y w s) (MMP.Resolution.monomialValuation x y w t) ≤
      MMP.Resolution.monomialValuation x y w (s + t) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_min_iff, natCast_le_monomialValuation_iff hxy hw,
    natCast_le_monomialValuation_iff hxy hw] at hn
  exact (natCast_le_monomialValuation_iff hxy hw).mpr (Ideal.add_mem _ hn.1 hn.2)

private theorem monomialValuation_ne_top {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) (s : R)
    (hs : s ≠ 0) : MMP.Resolution.monomialValuation x y w s ≠ ⊤ := by
  obtain ⟨a, ha, ha'⟩ := exists_mem_notMem hxy hw hs
  rw [monomialValuation_eq ha ha']; exact ENat.coe_ne_top a

private theorem monomialValuation_one {x y : R}
    (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} :
    MMP.Resolution.monomialValuation x y w 1 = 0 := by
  refine monomialValuation_eq (one_mem_monomialIdeal_zero x y w) fun h =>
    (maximalIdeal.isMaximal R).ne_top <| (Ideal.eq_top_iff_one _).mpr <|
      pow_one (maximalIdeal R) ▸ monomialIdeal_le_pow hxy (fun e he => ?_) h
  rw [weight_eq] at he; rw [degree_eq]
  rcases Nat.eq_zero_or_pos (e 1) with h | h
  · rw [h] at he; omega
  · omega

/-- An additive valuation of `S` that is finite on nonzero elements extends uniquely to the
fraction field. -/
private theorem existsUnique_extend {S : Type*} [CommRing S] [Nontrivial S] (K : Type*) [Field K]
    [Algebra S K] [IsFractionRing S K] (V₀ : AddValuation S (WithTop ℤ))
    (hV₀ : ∀ s, s ≠ 0 → V₀ s ≠ ⊤) :
    ∃! V : AddValuation K (WithTop ℤ), ∀ s : S, V (algebraMap S K s) = V₀ s := by
  let V₁ : Valuation S (Multiplicative (WithTop ℤ)ᵒᵈ) := V₀
  have hS : nonZeroDivisors S ≤ V₁.supp.primeCompl := fun s hs h =>
    hV₀ s (nonZeroDivisors.coe_ne_zero ⟨s, hs⟩) ((AddValuation.mem_supp_iff V₀ s).mp h)
  let V : AddValuation K (WithTop ℤ) := Valuation.extendToLocalization V₁ hS K
  have hV : ∀ s, V (algebraMap S K s) = V₀ s :=
    Valuation.extendToLocalization_apply_map_apply V₁ hS K
  refine ⟨V, hV, fun V' hV' => AddValuation.ext fun z => ?_⟩
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors S) z
  refine WithTop.add_right_cancel (hV₀ b (nonZeroDivisors.coe_ne_zero b)) ?_
  have h1 := congrArg V' h
  have h2 := congrArg V h
  rw [AddValuation.map_mul, hV'] at h1
  rw [AddValuation.map_mul, hV] at h2
  rw [h1, h2, hV', hV]

end Local

end MMP.Proofs.lem_mmp_resolution_weighted_monomial_valuation

namespace MMP.Resolution

open MMP.Proofs.lem_mmp_resolution_weighted_monomial_valuation in
/-- Let `(x, y)` be a regular system of parameters of a two-dimensional regular local ring `R`
with fraction field `K`, and `w ≥ 1`. The weighted order `v = monomialValuation x y w` is finite on
nonzero elements, satisfies `v (s * t) = v s + v t` and `min (v s) (v t) ≤ v (s + t)`, and there is
a unique additive valuation of `K` with values in `WithTop ℤ` restricting to `v` on `R`. -/
@[mmp "lem_mmp_resolution_weighted_monomial_valuation"]
public theorem exists_addValuation_monomialValuation
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {x y : R} (hxy : MMP.Mori.IsRegularSystemOfParameters ![x, y]) {w : ℕ} (hw : 1 ≤ w) :
    (∀ s : R, s ≠ 0 → monomialValuation x y w s ≠ ⊤) ∧
      (∀ s t : R, monomialValuation x y w (s * t) =
        monomialValuation x y w s + monomialValuation x y w t) ∧
      (∀ s t : R, min (monomialValuation x y w s) (monomialValuation x y w t) ≤
        monomialValuation x y w (s + t)) ∧
      ∃! V : AddValuation K (WithTop ℤ), ∀ s : R,
        V (algebraMap R K s) = (monomialValuation x y w s).map (Nat.cast : ℕ → ℤ) := by
  have hfin := monomialValuation_ne_top hxy hw
  have hmul := monomialValuation_mul hxy hw
  have hadd := min_le_monomialValuation_add hxy hw
  refine ⟨hfin, hmul, hadd, ?_⟩
  have hmono : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) := WithTop.monotone_map_iff.mpr Nat.mono_cast
  let f : R → WithTop ℤ := fun s => (MMP.Resolution.monomialValuation x y w s).map Nat.cast
  let V₀ : AddValuation R (WithTop ℤ) := AddValuation.of f
    (by simp [f, monomialValuation_zero]) (by simp [f, monomialValuation_one hxy])
    (fun s t => (hmono.map_min).symm.trans_le (hmono (hadd s t)))
    (fun s t => by simp only [f, hmul]; exact WithTop.map_add (Nat.castAddMonoidHom ℤ) _ _)
  exact existsUnique_extend K V₀ fun s hs => by simpa [V₀, f] using hfin s hs

end MMP.Resolution

end
