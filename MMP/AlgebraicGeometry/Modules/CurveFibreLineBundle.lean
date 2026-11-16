module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Modules.SquareZeroInvertibleLift
public import MMP.RingTheory.Henselian.ArtinApproximation
public import MMP.AlgebraicGeometry.Morphisms.Etale.HenselizationColimit
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GrothendieckAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeMorphism
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnionGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.LimitDescent.BaseChangeLimit
public import StacksFrontier.AlgebraicGeometry.Limits.IntegralFamily
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.ExcellentStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalk.ElementaryFiber
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.FibreNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreFirstCohomology
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SectionLifting

/-!
# Extending an invertible sheaf from a fibre of dimension at most one

Let `f : X ⟶ S` be a projective morphism, with `S` locally of finite type over a field, and let
`s ∈ S` be a point whose scheme fibre `F = X_s` has dimension at most one. Every invertible sheaf
`L₀` on `F` is the restriction of an invertible sheaf on `X ×_S S'` for some elementary
(pointed, with trivial residue field extension) étale neighbourhood `(S', s') ⟶ (S, s)`.

Write `R = 𝒪_{S,s}`, `R̂` for its completion and `Rʰ` for its henselization. The proof has four
steps.

* The fibres `X ×_S Spec (R̂ / 𝔪̂ⁿ⁺¹)` are nilpotent thickenings of `F`, of dimension at most one,
  so `L₀` lifts along them ([Stacks, Tag 09NY]); Grothendieck existence on the projective
  `X ×_S Spec R̂` ([Stacks, Tag 088F]) algebraizes the tower, and the algebraization is invertible.
* `R̂` is the filtered colimit of its finite type `R`-subalgebras, so the invertible sheaf descends
  to `X ×_S Spec B` for one of them ([Stacks, Tag 0B8W]).
* Artin approximation gives an `R`-algebra map `B ⟶ Rʰ` agreeing with `B ⟶ R̂` modulo `𝔪`; the
  pull-back along it restricts to `L₀` on the closed fibre.
* `Rʰ` is the filtered colimit of the rings of the affine elementary étale neighbourhoods of
  `(S, s)`, so the sheaf on `X ×_S Spec Rʰ` descends to one of them, again by [Stacks, Tag 0B8W].

For the second assertion, let `C` be an irreducible component of `F`, `Y` the union of the other
components and `H` an ample invertible sheaf on `F`. The sheaf given on `C_red` and `H^{⊗ n}` on
`Y_red` glue on the scheme-theoretic union of `C_red` and `Y_red`, whose two members meet in
finitely many points ([Stacks, Tag 09NE]); the glued sheaf lifts to `F` ([Stacks, Tag 09NY]) and
then to `X ×_S S'` by the first assertion. On a one-dimensional component `D ≠ C` its degree is
`n · deg(H|_D)`, and `deg(H|_D) > 0` since `H|_D` is ample.

Auxiliary results also lift invertible sheaves along nilpotent closed immersions into a scheme of
dimension at most one by first-order steps with vanishing `H²`.

## Main definitions

* `MMP.Fourfold.LiftsInvertible`: every invertible sheaf on the source is a pullback of an
  invertible sheaf on the target.
* `MMP.Fourfold.invertibleTower`: the successive lifts of an invertible sheaf along a tower of
  surjective closed immersions over a scheme of dimension at most one.

## Main results

* `MMP.Fourfold.liftsInvertible_of_ker_pow_eq_bot`: lifting along a nilpotent closed immersion
  into a Noetherian space of dimension at most one.
* `MMP.Fourfold.exists_isInvertibleModule_pullback_adicBaseChange_zero`: algebraization of an
  invertible sheaf on the closed member of the adic tower of a projective scheme over a complete
  Noetherian ring, when that member has dimension at most one.
* `MMP.Fourfold.exists_isInvertibleModule_pullback_bcπ`: descent of an invertible sheaf on a base
  change of a cofiltered limit of affine schemes.
* `MMP.Fourfold.exists_small_cofiltered_initial_affineElementaryEtaleNeighborhood`: the affine
  elementary étale neighbourhoods receive an initial functor from a small cofiltered category.
* `MMP.Fourfold.exists_elementaryEtaleNeighborhood_extension`: extension of an invertible sheaf
  from the fibre to `X ×_S S'` for an elementary étale neighbourhood `(S', s')`.
* `MMP.Fourfold.exists_elementaryEtaleNeighborhood_extension_of_component`: an invertible sheaf
  given on one irreducible component `C` of the fibre extends, with arbitrarily large degrees on
  the other one-dimensional components.

## Implementation notes

* Both assertions carry the tag of the source; they are
  `MMP.Fourfold.exists_elementaryEtaleNeighborhood_extension` and
  `MMP.Fourfold.exists_elementaryEtaleNeighborhood_extension_of_component`.
* An integral component `C` of `F_red` is the reduced closed subscheme
  `(Scheme.IdealSheafData.vanishingIdeal C).subscheme` on an irreducible component `C` of `F`, and
  a component is one-dimensional when that subscheme is. "Arbitrarily large positive degrees" is:
  for every `n`, degree at least `n` on every other one-dimensional component.
* The base field is arbitrary; the source works over `ℂ`. Only `S ⟶ Spec k` locally of finite
  type is used (so that `𝒪_{S,s}` is essentially of finite type over `k`, as Artin approximation
  needs), and `f` is H-projective (`AlgebraicGeometry.IsProjectiveMorphism`). The point `s` need
  not be closed.
* The fibre is `MMP.Fourfold.pointSettingFibre f s = X ×_S Spec κ(s)` and its map to
  `X ×_S S'` is `MMP.Fourfold.localEtaleFibreMap`, as in
  `MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum`.
* The category of affine elementary étale neighbourhoods has objects in `Type 1`, while the
  descent theorem for invertible sheaves through limits is stated for index categories in the
  universe of the schemes; the limit is therefore taken over a small cofiltered category with an
  initial functor to it, which exists because the elementary étale neighbourhoods admit a small
  weakly initial family.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite

universe u

namespace MMP.Fourfold

section Nilpotent

attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] Stacks.Thickenings.hasExtAbelianSheaf

/-- H² of any abelian sheaf on a scheme with Noetherian underlying space of dimension ≤ 1
vanishes. -/
theorem h2_eq_zero_of_noetherianSpace_of_dim_le_one {Y : Scheme.{u}} [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ ((1 : ℕ) : WithBot ℕ∞))
    (F : TopCat.Sheaf AddCommGrpCat.{u} Y) (x : Sheaf.H.{u} F 2) : x = 0 := by
  have := Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
    hdim (by norm_num : 1 < 2) F
  exact Subsingleton.elim _ _

/-- A morphism `i : X ⟶ Y` such that every invertible sheaf on `X` is the pullback of an
invertible sheaf on `Y`. -/
def LiftsInvertible {X Y : Scheme.{u}} (i : X ⟶ Y) : Prop :=
  ∀ (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L],
    ∃ (M : Y.Modules) (_ : Stacks.Ample.IsInvertibleModule Y M),
      Nonempty ((Scheme.Modules.pullback i).obj M ≅ L)

/-- The pullback of an invertible module is invertible. -/
theorem isInvertibleModule_pullback {X Y : Scheme.{u}} (i : X ⟶ Y) (M : Y.Modules)
    [hM : Stacks.Ample.IsInvertibleModule Y M] :
    Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback i).obj M) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (Stacks.RingedSpace.modulePullback_isInvertible_of i.toLRSHom.toShHom _
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr hM))

/-- Lifting invertible modules is stable under composition. -/
theorem LiftsInvertible.comp {X Y Z : Scheme.{u}} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : LiftsInvertible i) (hj : LiftsInvertible j) : LiftsInvertible (i ≫ j) := by
  intro L _
  obtain ⟨M, hM, ⟨eM⟩⟩ := hi L
  obtain ⟨N, hN, ⟨eN⟩⟩ := hj M
  exact ⟨N, hN, ⟨((Scheme.Modules.pullbackComp i j).app N).symm ≪≫
    (Scheme.Modules.pullback i).mapIso eN ≪≫ eM⟩⟩

/-- An isomorphism lifts invertible modules. -/
theorem LiftsInvertible.of_isIso {X Y : Scheme.{u}} (i : X ⟶ Y) [IsIso i] : LiftsInvertible i := by
  intro L hL
  exact ⟨(Scheme.Modules.pullback (inv i)).obj L, isInvertibleModule_pullback _ _,
    ⟨(Scheme.Modules.pullbackComp i (inv i)).app L ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id i)).app L ≪≫
      (Scheme.Modules.pullbackId X).app L⟩⟩

open Scheme.IdealSheafData in
/-- First-order step: lifting along the inclusion `V(K^(m+1)) ⟶ V(K^(m+2))`. -/
theorem liftsInvertible_inclusion_pow_succ {Y : Scheme.{u}} [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ ((1 : ℕ) : WithBot ℕ∞)) (K : Y.IdealSheafData) (m : ℕ) :
    LiftsInvertible (inclusion (I := K ^ (m + 2)) (J := K ^ (m + 1))
      (Stacks.Thickenings.idealSheaf_pow_le_pow_right (Nat.le_succ (m + 1)))) := by
  have hle : K ^ (m + 2) ≤ K ^ (m + 1) :=
    Stacks.Thickenings.idealSheaf_pow_le_pow_right (Nat.le_succ (m + 1))
  have hth := Stacks.Thickenings.isFirstOrderThickening_inclusion_of_sq_le hle (by
    rw [← pow_mul]
    exact Stacks.Thickenings.idealSheaf_pow_le_pow_right (by omega))
  have hemb : Topology.IsClosedEmbedding (K ^ (m + 2)).subschemeι :=
    (K ^ (m + 2)).subschemeι.isClosedEmbedding
  haveI : NoetherianSpace (K ^ (m + 2)).subscheme := hemb.isInducing.noetherianSpace
  have hdim' : topologicalKrullDim (K ^ (m + 2)).subscheme ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    hemb.isInducing.topologicalKrullDim_le.trans hdim
  intro L _
  exact MMP.Resolution.Bridges.exists_isInvertibleModule_pullback_iso_of_ker_sq_eq_bot _
    (by simpa [Stacks.Thickenings.IsFirstOrderThickening, Stacks.Thickenings.IsNthOrderThickening]
      using hth.2) (fun x => h2_eq_zero_of_noetherianSpace_of_dim_le_one hdim' _ x) L

open Scheme.IdealSheafData in
/-- The inclusion `V(I) ⟶ V(J)` lifts invertible modules when `I = J`. -/
theorem liftsInvertible_inclusion_of_eq {Y : Scheme.{u}} {I J : Y.IdealSheafData} (h : I ≤ J)
    (he : I = J) : LiftsInvertible (inclusion h) := by
  subst he
  rw [show inclusion h = inclusion (le_refl I) from rfl, inclusion_id]
  exact LiftsInvertible.of_isIso _

open Scheme.IdealSheafData in
/-- Lifting along `V(K) ⟶ V(K^(m+1))`. -/
theorem liftsInvertible_inclusion_pow {Y : Scheme.{u}} [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ ((1 : ℕ) : WithBot ℕ∞)) (K : Y.IdealSheafData) (m : ℕ) :
    LiftsInvertible (inclusion (I := K ^ (m + 1)) (J := K)
      ((Stacks.Thickenings.idealSheaf_pow_le_pow_right (Nat.le_add_left 1 m)).trans_eq
        (pow_one K))) := by
  induction m with
  | zero => exact liftsInvertible_inclusion_of_eq _ (pow_one K)
  | succ m ih =>
    have := ih.comp (liftsInvertible_inclusion_pow_succ hdim K m)
    rwa [inclusion_comp] at this

open Scheme.IdealSheafData in
/-- **Lifting invertible sheaves along a nilpotent closed immersion in dimension at most one.**
Let `i : X ⟶ Y` be a closed immersion into a scheme with Noetherian underlying space of
topological dimension at most one, whose ideal sheaf is nilpotent. Then every invertible sheaf
on `X` is isomorphic to the pullback of an invertible sheaf on `Y`. -/
theorem liftsInvertible_of_ker_pow_eq_bot {X Y : Scheme.{u}} [NoetherianSpace Y]
    (hdim : topologicalKrullDim Y ≤ ((1 : ℕ) : WithBot ℕ∞)) (i : X ⟶ Y) [IsClosedImmersion i]
    {n : ℕ} (hn : i.ker ^ n = ⊥) : LiftsInvertible i := by
  have : IsIso (i.ker ^ (n + 1)).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 (by rw [pow_succ, hn, bot_mul])
  have h3 := ((LiftsInvertible.of_isIso i.toImage).comp
    (liftsInvertible_inclusion_pow hdim i.ker n)).comp
    (LiftsInvertible.of_isIso (i.ker ^ (n + 1)).subschemeι)
  have heq : i.toImage ≫ inclusion
      ((Stacks.Thickenings.idealSheaf_pow_le_pow_right (Nat.le_add_left 1 n)).trans_eq
        (pow_one i.ker)) ≫ (i.ker ^ (n + 1)).subschemeι = i := by
    rw [inclusion_subschemeι]
    exact Scheme.Hom.toImage_imageι i
  rwa [Category.assoc, heq] at h3

end Nilpotent

section Tower

variable (A : Type) [CommRing A] (I : Ideal A) {X : Scheme.{0}} (fX : X ⟶ Spec (.of A))

/-- A member of a tower `Xₙ` of schemes carrying an invertible module. -/
structure InvertibleTowerStage (Xn : ℕ → Scheme.{0}) (n : ℕ) where
  /-- The module. -/
  obj : (Xn n).Modules
  /-- The module is invertible. -/
  isInvertible : Stacks.Ample.IsInvertibleModule _ obj

attribute [instance] InvertibleTowerStage.isInvertible

variable {Xn : ℕ → Scheme.{0}} (i : ∀ n, Xn n ⟶ Xn (n + 1)) [∀ n, IsClosedImmersion (i n)]
  (hi : ∀ n, Function.Surjective (i n))

include hi in
/-- The members of a tower of surjective closed immersions over a Noetherian space are
Noetherian. -/
theorem noetherianSpace_tower [NoetherianSpace (Xn 0)] (n : ℕ) : NoetherianSpace (Xn n) := by
  induction n with
  | zero => infer_instance
  | succ n ih => exact noetherianSpace_of_surjective _ (i n).continuous (hi n)

include hi in
/-- The members of a tower of surjective closed immersions are homeomorphic to the closed member,
so they have its dimension. -/
theorem topologicalKrullDim_tower (n : ℕ) :
    topologicalKrullDim (Xn n) = topologicalKrullDim (Xn 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← ih]
    exact ((isHomeomorph_iff_continuous_isClosedMap_bijective.2
      ⟨(i n).continuous, (i n).isClosedEmbedding.isClosedMap,
        (i n).isClosedEmbedding.injective, hi n⟩).topologicalKrullDim_eq _).symm

include hi in
/-- One step of the tower: an invertible module on `Xₙ` lifts to `Xₙ₊₁`, by [Stacks, Tag 09NY]. -/
theorem exists_lift_invertibleTowerStage [NoetherianSpace (Xn 0)]
    (hdim : topologicalKrullDim (Xn 0) ≤ 1) (n : ℕ) (L : InvertibleTowerStage Xn n) :
    ∃ M : InvertibleTowerStage Xn (n + 1),
      Nonempty ((Scheme.Modules.pullback (i n)).obj M.obj ≅ L.obj) := by
  haveI := noetherianSpace_tower i hi (n + 1)
  obtain ⟨M, hM, e⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one _ _
      (i n) ((topologicalKrullDim_tower i hi (n + 1)).trans_le hdim) L.obj
  exact ⟨⟨M, hM⟩, e⟩

/-- The tower of successive lifts of an invertible module on the closed member. -/
def invertibleTower [NoetherianSpace (Xn 0)] (hdim : topologicalKrullDim (Xn 0) ≤ 1)
    (L₀ : InvertibleTowerStage Xn 0) : (n : ℕ) → InvertibleTowerStage Xn n
  | 0 => L₀
  | n + 1 => (exists_lift_invertibleTowerStage i hi hdim n (invertibleTower hdim L₀ n)).choose

@[simp]
theorem invertibleTower_zero [NoetherianSpace (Xn 0)] (hdim : topologicalKrullDim (Xn 0) ≤ 1)
    (L₀ : InvertibleTowerStage Xn 0) : invertibleTower i hi hdim L₀ 0 = L₀ := rfl

/-- The members of `MMP.Fourfold.invertibleTower` restrict to each other. -/
theorem nonempty_invertibleTower_iso [NoetherianSpace (Xn 0)]
    (hdim : topologicalKrullDim (Xn 0) ≤ 1) (L₀ : InvertibleTowerStage Xn 0) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (i n)).obj (invertibleTower i hi hdim L₀ (n + 1)).obj ≅
      (invertibleTower i hi hdim L₀ n).obj) :=
  (exists_lift_invertibleTowerStage i hi hdim n (invertibleTower i hi hdim L₀ n)).choose_spec

include hi in
/-- **Algebraization of an invertible module from the closed member of an adic tower of
dimension at most one.** Given a tower `Xₙ` cartesian over the adic thickenings of a complete
Noetherian ring `A`, with compatible cartesian maps to a projective `X` over `A`, every invertible
module on `X₀` is the pullback of an invertible module on `X`. -/
theorem exists_isInvertibleModule_pullback_of_tower [IsNoetherianRing A] [IsAdicComplete I A]
    (hfX : IsProjectiveMorphism fX) (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (k : ∀ n, Xn n ⟶ X) (hk : ∀ n, i n ≫ k (n + 1) = k n)
    (hkcart : ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n))
    [NoetherianSpace (Xn 0)] (hdim : topologicalKrullDim (Xn 0) ≤ 1)
    (L : (Xn 0).Modules) [hL : Stacks.Ample.IsInvertibleModule _ L] :
    ∃ (M : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X M),
      Nonempty ((Scheme.Modules.pullback (k 0)).obj M ≅ L) := by
  haveI := isProper_of_isProjectiveMorphism fX hfX
  let T := invertibleTower i hi hdim ⟨L, hL⟩
  obtain ⟨M, hcoh, e, -⟩ :=
    Stacks.AmpleFormalSystemLineBundle.exists_coherent_of_restriction_isEquivalence A I fX
      q i k hk hkcart (fun n => (T n).obj) (fun n => (T n).isInvertible)
      (fun n => (nonempty_invertibleTower_iso i hi hdim ⟨L, hL⟩ n).some)
      (Stacks.AmpleFormalSystemTheorem.adicTowerModuleAlgebraization_of_canonicalTower A I q i
        hcart (Stacks.AdicTowerRestriction.adicCanonicalTowerModuleAlgebraization A I)
        fX hfX k hk hkcart)
  exact ⟨M, Stacks.AdicTowerInvert.adicTowerInvertibility A I q fX hfX k hkcart M hcoh
    (fun n => Stacks.AmpleFormalSystemLineBundle.isInvertibleModule_of_iso (e n)
      (T n).isInvertible), ⟨(e 0).symm⟩⟩

/-- **Algebraization on the canonical adic tower.** If the closed member `adicBaseChange A I fX 0`
of the adic tower of a projective `fX` over a complete Noetherian ring has dimension at most one,
every invertible module on it is the pullback of an invertible module on `X`. -/
theorem exists_isInvertibleModule_pullback_adicBaseChange_zero [IsNoetherianRing A]
    [IsAdicComplete I A] (hfX : IsProjectiveMorphism fX)
    [NoetherianSpace (adicBaseChange A I fX 0)]
    (hdim : topologicalKrullDim (adicBaseChange A I fX 0) ≤ 1)
    (L : (adicBaseChange A I fX 0).Modules) [Stacks.Ample.IsInvertibleModule _ L] :
    ∃ (M : X.Modules) (_ : Stacks.Ample.IsInvertibleModule X M),
      Nonempty ((Scheme.Modules.pullback (pullback.fst fX (adicThickeningι A I 0))).obj M ≅ L) :=
  exists_isInvertibleModule_pullback_of_tower A I fX (adicBaseChangeSucc A I fX)
    (fun n => (bijective_base_adicBaseChangeSucc A I fX n).2) hfX
    (fun n => pullback.snd fX (adicThickeningι A I n)) (isPullback_adicBaseChangeSucc A I fX)
    (fun n => pullback.fst fX (adicThickeningι A I n)) (adicBaseChangeSucc_fst A I fX)
    (fun n => IsPullback.of_hasPullback fX (adicThickeningι A I n)) hdim L

end Tower

/-- **Descent of an invertible module on a base change of a cofiltered limit.** Every invertible
module on `Y ×_{D i} c.pt` is, up to isomorphism, the pullback along `LimitDescent.bcπ` of an
invertible module on `Y ×_{D i} D j` for some `j ⟶ i`. -/
theorem exists_isInvertibleModule_pullback_bcπ {I : Type} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{0}) [∀ {j k : I} (g : j ⟶ k), IsAffineHom (D.map g)] (c : Cone D)
    (hc : IsLimit c) (i : I) (Y : Over (D.obj i)) [CompactSpace Y.left]
    [QuasiSeparatedSpace Y.left] (M : (pullback Y.hom (c.π.app i)).Modules)
    [hM : Stacks.Ample.IsInvertibleModule _ M] :
    ∃ (j : Over i) (N : (pullback Y.hom (D.map j.hom)).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ N),
      Nonempty (M ≅ (Scheme.Modules.pullback (LimitDescent.bcπ D c i Y j)).obj N) := by
  haveI := LimitDescent.compactSpace_bcDiagram_obj D i Y
  haveI := LimitDescent.quasiSeparatedSpace_bcDiagram_obj D i Y
  haveI : ∀ {j k : Over i} (g : j ⟶ k), IsAffineHom ((LimitDescent.bcDiagram D i Y).map g) :=
    fun g => LimitDescent.isAffineHom_bcMap D i Y g
  obtain ⟨j, N, hN, e⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      (LimitDescent.bcDiagram D i Y) (LimitDescent.bcCone D c i Y)
      (LimitDescent.isLimitBcCone D c i Y hc) M hM
  exact ⟨j, N, hN, e⟩

/-- The descent morphism `LimitDescent.bcπ` is the base change of the cone leg. -/
theorem bcπ_eq_lift {I : Type} [Category I] (D : I ⥤ Scheme.{0}) (c : Cone D) (i : I)
    (Y : Over (D.obj i)) (j : Over i) :
    LimitDescent.bcπ D c i Y j = pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ c.π.app j.left) (by rw [pullback.condition, Category.assoc, c.w j.hom]) :=
  pullback.hom_ext ((LimitDescent.bcπ_fst D c i Y j).trans (pullback.lift_fst _ _ _).symm)
    ((LimitDescent.bcπ_snd D c i Y j).trans (pullback.lift_snd _ _ _).symm)

section Hens

/-- On an affine scheme, `Spec 𝒪_{Y,y} ⟶ Y` is the germ map followed by `Spec Γ(Y) ≅ Y`. -/
@[reassoc]
theorem fromSpecStalk_eq_of_isAffine {Y : Scheme.{0}} [IsAffine Y] (y : Y) :
    Y.fromSpecStalk y = Spec.map (Y.presheaf.germ ⊤ y (Set.mem_univ _)) ≫ Y.isoSpec.inv := by
  rw [← (isAffineOpen_top Y).fromSpecStalk_eq_fromSpecStalk (x := y) (Set.mem_univ _),
    ← IsAffineOpen.fromSpec_top]
  rfl

/-- Transport of `Spec 𝒪_{Y,x} ⟶ Y` along an equality of points. -/
@[reassoc]
theorem SpecMap_stalkCongr_fromSpecStalk {Y : Scheme.{0}} {x y : Y} (h : x = y) :
    Spec.map (Y.presheaf.stalkCongr (.of_eq h)).hom ≫ Y.fromSpecStalk x = Y.fromSpecStalk y := by
  subst h
  simp

variable {S : Scheme.{0}} {s : S} {Rh : Type} [CommRing Rh] [IsLocalRing Rh]
  [Algebra (S.presheaf.stalk s) Rh]

/-- The legs of the henselization over an affine elementary étale neighbourhood lie over the
canonical morphism `Spec 𝒪_{S,s}ʰ ⟶ Spec 𝒪_{S,s} ⟶ S`. -/
theorem SpecMap_comp_isoSpec_inv_toBase_of_isOverStalk (U : ElementaryEtaleNeighborhood S s)
    [IsAffine U.obj.scheme] (φ : Γ(U.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (hφ : IsOverStalk S s Rh U φ.hom) :
    Spec.map φ ≫ U.obj.scheme.isoSpec.inv ≫ U.obj.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) ≫ S.fromSpecStalk s := by
  obtain ⟨g, -, hg, hφg⟩ := hφ
  let gH : U.obj.scheme.presheaf.stalk U.obj.point ⟶ CommRingCat.of Rh := CommRingCat.ofHom g
  have h1 : φ = U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _) ≫ gH := by
    ext x
    exact congrArg (fun h : _ →+* Rh => h x) hφg
  have h2 : CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh) =
      (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom ≫
        U.obj.toBase.stalkMap U.obj.point ≫ gH := by
    ext x
    exact (congrArg (fun h : _ →+* Rh => h x) hg).symm
  rw [h1, h2, Spec.map_comp, Category.assoc, ← fromSpecStalk_eq_of_isAffine_assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc, SpecMap_stalkCongr_fromSpecStalk U.obj.map_point.symm]

omit [IsLocalRing Rh] [Algebra (S.presheaf.stalk s) Rh] in
/-- Every element of the local ring at the point of an elementary étale neighbourhood is congruent,
modulo the maximal ideal, to the image of an element of `𝒪_{S,s}`. -/
theorem exists_sub_stalkMap_mem_maximalIdeal (U : ElementaryEtaleNeighborhood S s)
    (y : U.obj.scheme.presheaf.stalk U.obj.point) :
    ∃ r : S.presheaf.stalk s,
      y - stalkMap S s U r ∈
        IsLocalRing.maximalIdeal (U.obj.scheme.presheaf.stalk U.obj.point) := by
  haveI : IsIso U.obj.residueFieldMap := U.property
  have hiso : IsIso (U.obj.toBase.residueFieldMap U.obj.point) := by
    have h : U.obj.toBase.residueFieldMap U.obj.point =
        (S.residueFieldCongr U.obj.map_point).hom ≫ U.obj.residueFieldMap := by
      rw [EtaleNeighborhood.residueFieldMap_def, Iso.hom_inv_id_assoc]
    rw [h]
    infer_instance
  obtain ⟨z, hz⟩ := ((ConcreteCategory.bijective_of_isIso
    (U.obj.toBase.residueFieldMap U.obj.point)).2) (U.obj.scheme.residue U.obj.point y)
  obtain ⟨t, rfl⟩ := S.residue_surjective _ z
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso
    (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom).2 t
  refine ⟨r, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  have h := congrArg (fun φ => φ.hom t) (Scheme.residue_residueFieldMap U.obj.toBase U.obj.point)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  change (U.obj.scheme.residue U.obj.point).hom y = (U.obj.scheme.residue U.obj.point).hom
    ((U.obj.toBase.stalkMap U.obj.point).hom ((S.presheaf.stalkCongr _).hom.hom r))
  rw [← hz]
  change _ = (U.obj.scheme.residue U.obj.point).hom
    ((U.obj.toBase.stalkMap U.obj.point).hom
      (ConcreteCategory.hom (S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom r))
  rw [hr]
  exact h

omit [IsLocalRing Rh] [Algebra (S.presheaf.stalk s) Rh] in
/-- The residue of the image of `r ∈ 𝒪_{S,s}` in the local ring of an elementary étale
neighbourhood is the image of the residue of `r` under `κ(s) ≅ κ(u)`. -/
theorem residue_stalkMap (U : ElementaryEtaleNeighborhood S s) (r : S.presheaf.stalk s) :
    (U.obj.scheme.residue U.obj.point).hom (stalkMap S s U r) =
      U.obj.residueFieldMap.hom ((S.residue s).hom r) := by
  have h1 := congrArg
    (fun φ => φ.hom ((S.presheaf.stalkCongr (.of_eq U.obj.map_point.symm)).hom.hom r))
    (Scheme.residue_residueFieldMap U.obj.toBase U.obj.point)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  change _ = U.obj.residueFieldMap.hom _
  rw [EtaleNeighborhood.residueFieldMap_def]
  change (U.obj.scheme.residue U.obj.point).hom ((U.obj.toBase.stalkMap U.obj.point).hom
    ((S.presheaf.stalkCongr _).hom.hom r)) = _
  rw [← h1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.residue_residueFieldCongr S U.obj.map_point.symm)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [← h2, Scheme.residueFieldCongr_inv]

/-- The section through the distinguished point of an affine elementary étale neighbourhood,
read on global sections, is the leg of the henselization followed by a residue map. -/
theorem SpecMap_comp_section_comp_isoSpec_hom (U : ElementaryEtaleNeighborhood S s)
    [IsAffine U.obj.scheme] (φ : Γ(U.obj.scheme, ⊤) ⟶ CommRingCat.of Rh)
    (hφ : IsOverStalk S s Rh U φ.hom) {K : Type} [CommRing K] (χ : Rh →+* K)
    (hχ : ∀ x ∈ IsLocalRing.maximalIdeal Rh, χ x = 0)
    (e : S.residueField s ⟶ CommRingCat.of K)
    (he : ∀ r, e.hom ((S.residue s).hom r) = χ (algebraMap (S.presheaf.stalk s) Rh r)) :
    Spec.map e ≫ elementaryNeighborhoodSection U ≫ U.obj.scheme.isoSpec.hom =
      Spec.map (φ ≫ CommRingCat.ofHom χ) := by
  haveI : IsIso U.obj.residueFieldMap := U.property
  obtain ⟨g, hgl, hg, hφg⟩ := hφ
  rw [elementaryNeighborhoodSection, Scheme.fromSpecResidueField, fromSpecStalk_eq_of_isAffine,
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [hφg, RingHom.comp_apply]
  set y := (U.obj.scheme.presheaf.germ ⊤ U.obj.point (Set.mem_univ _)).hom x
  obtain ⟨r, hr⟩ := exists_sub_stalkMap_mem_maximalIdeal U y
  have h1 : (U.obj.scheme.residue U.obj.point).hom y =
      (U.obj.scheme.residue U.obj.point).hom (stalkMap S s U r) := by
    change IsLocalRing.residue _ y = IsLocalRing.residue _ _
    rwa [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have h2 : χ (g y) = χ (g (stalkMap S s U r)) := by
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    exact hχ _ (map_nonunit g _ hr)
  rw [h1, h2, residue_stalkMap]
  have h3 : (inv U.obj.residueFieldMap).hom (U.obj.residueFieldMap.hom ((S.residue s).hom r)) =
      (S.residue s).hom r := by
    rw [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
  rw [h3, he, ← hg, RingHom.comp_apply]

/-- Every elementary étale neighbourhood is refined by an affine one. -/
theorem exists_affineElementaryEtaleNeighborhood_hom (U : ElementaryEtaleNeighborhood S s) :
    ∃ W : MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s, Nonempty (W.obj ⟶ U) := by
  obtain ⟨O, hO, hu, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.obj.scheme) (x := U.obj.point)
      (U := ⊤) (by simp)
  let W : EtaleNeighborhood S s :=
    { scheme := O
      point := ⟨U.obj.point, hu⟩
      toBase := O.ι ≫ U.obj.toBase
      map_point := U.obj.map_point }
  have hW : W.IsElementary := by
    change IsIso ((S.residueFieldCongr W.map_point).inv ≫
      W.toBase.residueFieldMap W.point)
    rw [Scheme.residueFieldMap_comp]
    change IsIso (((S.residueFieldCongr U.obj.map_point).inv ≫
      U.obj.toBase.residueFieldMap U.obj.point) ≫ O.ι.residueFieldMap W.point)
    exact IsIso.comp_isIso' U.property (inferInstance : IsIso (O.ι.residueFieldMap W.point))
  exact ⟨⟨⟨W, hW⟩, hO⟩, ⟨⟨⟨O.ι, rfl, rfl⟩⟩⟩⟩

/-- The affine elementary étale neighbourhoods of `(S, s)` receive an initial functor from a
small cofiltered category. -/
theorem exists_small_cofiltered_initial_affineElementaryEtaleNeighborhood (S : Scheme.{0})
    (s : S) : ∃ (K : Type) (_ : SmallCategory K) (_ : IsCofiltered K)
      (Φ : K ⥤ MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s), Φ.Initial := by
  obtain ⟨Rh, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField (S.presheaf.stalk s)
  haveI : IsCofiltered (MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s) :=
    @isCofiltered_of_isFiltered_op _ _
      (MMP.Resolution.Bridges.isFiltered_affineElementaryEtaleNeighborhood_and_isColimit
        S s Rh).1
  obtain ⟨T, hT, hTinit⟩ :=
    InitiallySmall.exists_small_weakly_initial_set.{0} (ElementaryEtaleNeighborhood S s)
  choose W hW using fun U : ElementaryEtaleNeighborhood S s =>
    exists_affineElementaryEtaleNeighborhood_hom U
  let T' : Set (MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s) := W '' T
  haveI : Small.{0} T' := small_image _ _
  let P : ObjectProperty (MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s) :=
    fun V => V ∈ T'
  have hinit : ∀ V : MMP.Resolution.Bridges.AffineElementaryEtaleNeighborhood S s,
      ∃ c : P.FullSubcategory,
        Nonempty ((ObjectProperty.ι P).obj c ⟶ V) := by
    intro V
    obtain ⟨U, hU, ⟨g⟩⟩ := hTinit V.obj
    obtain ⟨h⟩ := hW U
    exact ⟨⟨W U, ⟨U, hU, rfl⟩⟩, ⟨⟨h ≫ g⟩⟩⟩
  haveI : IsCofiltered P.FullSubcategory :=
    IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (ObjectProperty.ι P) hinit
  haveI : (ObjectProperty.ι P).Initial :=
    Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ hinit
  let K0 := P.FullSubcategory
  haveI : IsCofiltered (SmallModel.{0} K0) := IsCofiltered.of_equivalence (equivSmallModel K0)
  exact ⟨SmallModel.{0} K0, inferInstance, inferInstance,
    (equivSmallModel K0).inverse ⋙ ObjectProperty.ι P, Functor.initial_comp _ _⟩

end Hens

section Modules

/-- The isomorphism `a^* (b^* M) ≅ c^* M` induced by an equality `a ≫ b = c`. -/
def pullbackCompIso {X Y Z : Scheme.{0}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z} (h : a ≫ b = c)
    (M : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback c).obj M :=
  (Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

/-- Pulling back along an isomorphism reflects isomorphism of modules. -/
theorem nonempty_iso_of_isIso_pullback {X Y : Scheme.{0}} (θ : X ⟶ Y) [IsIso θ] {A B : Y.Modules}
    (e : (Scheme.Modules.pullback θ).obj A ≅ (Scheme.Modules.pullback θ).obj B) :
    Nonempty (A ≅ B) := by
  have hid : inv θ ≫ θ = 𝟙 Y := IsIso.inv_hom_id θ
  exact ⟨((Scheme.Modules.pullbackId Y).app A).symm ≪≫ (pullbackCompIso hid A).symm ≪≫
    (Scheme.Modules.pullback (inv θ)).mapIso e ≪≫ pullbackCompIso hid B ≪≫
    (Scheme.Modules.pullbackId Y).app B⟩

/-- The source of a proper morphism to a quasi-compact scheme is quasi-compact. -/
theorem compactSpace_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g] [CompactSpace Y] :
    CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace g

/-- The source of a proper morphism to a quasi-separated scheme is quasi-separated. -/
theorem quasiSeparatedSpace_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g]
    [QuasiSeparatedSpace Y] : QuasiSeparatedSpace X :=
  haveI : QuasiSeparated g := IsSeparated.instQuasiSeparated g
  quasiSeparatedSpace_of_quasiSeparated g

end Modules

section Main

/-- **Extending an invertible sheaf from a fibre of dimension at most one.** Let `f : X ⟶ S` be
projective, with `S` locally of finite type over a field, and let `s ∈ S` be a point whose scheme
fibre `F = X ×_S Spec κ(s)` has dimension at most one. Every invertible sheaf `L₀` on `F` is the
restriction, along `F ≅ (X ×_S S') ×_{S'} Spec κ(s') ⟶ X ×_S S'`, of an invertible sheaf on
`X ×_S S'` for some elementary étale neighbourhood `(S', s')` of `(S, s)`, i.e. a pointed étale
neighbourhood with `κ(s) ≅ κ(s')`. -/
@[mmp "lem_fourfold_curve_fibre_line_bundle_etale_extension"]
theorem exists_elementaryEtaleNeighborhood_extension {k : Type} [Field k] {S X : Scheme.{0}}
    (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS] (f : X ⟶ S) (hf : IsProjectiveMorphism f)
    (s : S) (hdim : topologicalKrullDim (pointSettingFibre f s) ≤ 1)
    (L₀ : (pointSettingFibre f s).Modules) [Stacks.Ample.IsInvertibleModule _ L₀] :
    ∃ (U : ElementaryEtaleNeighborhood S s) (M : (pullback f U.obj.toBase).Modules)
      (_ : Stacks.Ample.IsInvertibleModule _ M),
      Nonempty ((Scheme.Modules.pullback (localEtaleFibreMap f U)).obj M ≅ L₀) := by
  classical
  -- the local ring, its completion and its henselization
  let R := S.presheaf.stalk s
  letI : Algebra k R := (((sS.stalkMap s).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sS.base s) (by simp)).hom)).toAlgebra
  haveI : Algebra.EssFiniteType k R := essFiniteType_stalkStructureMap sS s
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing k R
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  haveI : IsLocalRing A :=
    AdicCompletion.isLocalRing_of_fg (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  haveI := isAdicComplete_maximalIdeal_adicCompletion R
  obtain ⟨Rh, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField R
  let emb := IsLocalRing.henselizationToAdicCompletion R Rh
  -- the completion as a cofiltered limit of finite type `R`-algebras
  let F1 : Finset A ⥤ CommRingCat.{0} := Algebra.adjoinFinsetDiagram R A
  let D1 : (Finset A)ᵒᵖ ⥤ Scheme.{0} := F1.op ⋙ Scheme.Spec
  let c1 : Cone D1 := Scheme.Spec.mapCone (Algebra.adjoinFinsetCocone R A).op
  have hc1 : IsLimit c1 :=
    isLimitOfPreserves Scheme.Spec (Algebra.isColimitAdjoinFinsetCocone R A).op
  haveI : ∀ {i j : (Finset A)ᵒᵖ} (g : i ⟶ j), IsAffineHom (D1.map g) := by
    intro i j g
    dsimp [D1, F1, Algebra.adjoinFinsetDiagram]
    infer_instance
  let i1 : (Finset A)ᵒᵖ := op ∅
  let B0 := Algebra.adjoin R ((∅ : Finset A) : Set A)
  let πA : Spec (.of A) ⟶ Spec (.of B0) := Spec.map (CommRingCat.ofHom B0.val.toRingHom)
  let g1 : Spec (.of B0) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R B0)) ≫ S.fromSpecStalk s
  have hY1 : IsProjectiveMorphism (pullback.snd f g1) := hf.baseChange g1
  haveI : IsProper (pullback.snd f g1) := isProper_of_isProjectiveMorphism _ hY1
  haveI : CompactSpace ↥(pullback f g1) := compactSpace_of_isProper (pullback.snd f g1)
  haveI : QuasiSeparatedSpace ↥(pullback f g1) :=
    quasiSeparatedSpace_of_isProper (pullback.snd f g1)
  let fX : pullback (pullback.snd f g1) πA ⟶ Spec (.of A) := pullback.snd (pullback.snd f g1) πA
  have hfX : IsProjectiveMorphism fX := hY1.baseChange _
  -- the closed member of the adic tower is the fibre
  let Im := IsLocalRing.maximalIdeal A
  let X0 := adicBaseChange A Im fX 0
  let bX0 : X0 ⟶ adicThickening A Im 0 := pullback.snd fX (adicThickeningι A Im 0)
  let pX0 : X0 ⟶ X := pullback.fst fX (adicThickeningι A Im 0) ≫
    pullback.fst (pullback.snd f g1) πA ≫ pullback.fst f g1
  have hc1g1 : πA ≫ g1 = Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ S.fromSpecStalk s := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hpX0 : pX0 ≫ f = bX0 ≫ adicThickeningι A Im 0 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ S.fromSpecStalk s := by
    rw [← hc1g1]
    simp only [pX0, bX0, fX, Category.assoc, pullback.condition, pullback.condition_assoc]
  have hIm : IsLocalRing.maximalIdeal A = Im ^ (0 + 1) := by rw [zero_add, pow_one]
  let eR : IsLocalRing.ResidueField R →+* A ⧸ Im ^ (0 + 1) :=
    (Ideal.quotEquivOfEq hIm : IsLocalRing.ResidueField A ≃+* A ⧸ Im ^ (0 + 1)).toRingHom.comp
      (IsLocalRing.ResidueField.map (algebraMap R A))
  let e : S.residueField s ⟶ CommRingCat.of (A ⧸ Im ^ (0 + 1)) := CommRingCat.ofHom eR
  have he : ∀ r : R, eR (IsLocalRing.residue R r) = Ideal.Quotient.mk _ (algebraMap R A r) := by
    intro r
    simp only [eR, RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  haveI : IsIso e := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (Ideal.quotEquivOfEq hIm).bijective.comp (AdicCompletion.residueField_map_bijective R)
  have hres : S.residue s ≫ e = CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (Im ^ (0 + 1))) := by
    ext r
    exact he r
  have hθc : pX0 ≫ f = (bX0 ≫ Spec.map e) ≫ S.fromSpecResidueField s := by
    rw [hpX0, Scheme.fromSpecResidueField, Category.assoc, ← Spec.map_comp_assoc, hres,
      Spec.map_comp, Category.assoc]
    rfl
  let θ : X0 ⟶ pointSettingFibre f s := pullback.lift pX0 (bX0 ≫ Spec.map e) hθc
  haveI : IsIso θ := by
    have h1 := ((IsPullback.of_hasPullback fX (adicThickeningι A Im 0)).paste_horiz
      (IsPullback.of_hasPullback (pullback.snd f g1) πA)).paste_horiz
        (IsPullback.of_hasPullback f g1)
    have h2 : IsPullback (θ ≫ pullback.fst f (S.fromSpecResidueField s)) bX0 f
        (Spec.map e ≫ S.fromSpecResidueField s) := by
      have e1 : θ ≫ pullback.fst f (S.fromSpecResidueField s) =
          (pullback.fst fX (adicThickeningι A Im 0) ≫ pullback.fst (pullback.snd f g1) πA) ≫
            pullback.fst f g1 := by
        rw [Category.assoc]
        exact pullback.lift_fst _ _ _
      have e2 : Spec.map e ≫ S.fromSpecResidueField s = (adicThickeningι A Im 0 ≫ πA) ≫ g1 := by
        rw [Category.assoc, hc1g1, Scheme.fromSpecResidueField, ← Spec.map_comp_assoc, hres,
          Spec.map_comp, Category.assoc]
        rfl
      rw [e1, e2]
      exact h1
    exact (h2.of_right (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s))).isIso_fst_of_isIso
  haveI : IsProper bX0 := isProper_of_isProjectiveMorphism _ (hfX.baseChange _)
  haveI : CompactSpace X0 := compactSpace_of_isProper bX0
  haveI : LocallyOfFiniteType bX0 := IsProper.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X0 := LocallyOfFiniteType.isLocallyNoetherian bX0
  haveI : IsNoetherian X0 := {}
  have hdim0 : topologicalKrullDim X0 ≤ 1 := by
    rwa [(θ.homeomorph.isHomeomorph).topologicalKrullDim_eq]
  -- algebraization over the completion
  obtain ⟨Mh, hMh, ⟨eMh⟩⟩ := exists_isInvertibleModule_pullback_adicBaseChange_zero A Im fX hfX
    hdim0 ((Scheme.Modules.pullback θ).obj L₀)
  -- descent to a finite type `R`-subalgebra of the completion
  haveI : IsAffine (D1.obj i1) := by
    dsimp [D1]
    infer_instance
  let Y1 : Over (D1.obj i1) := Over.mk (pullback.snd f g1)
  haveI : CompactSpace Y1.left := (inferInstance : CompactSpace ↥(pullback f g1))
  haveI : QuasiSeparatedSpace Y1.left := (inferInstance : QuasiSeparatedSpace ↥(pullback f g1))
  obtain ⟨j1, N1, hN1, ⟨eN1⟩⟩ := exists_isInvertibleModule_pullback_bcπ D1 c1 hc1 i1 Y1 Mh
    (hM := hMh)
  -- Artin approximation of the finite stage in the henselization
  let B := Algebra.adjoin R ((j1.left.unop : Finset A) : Set A)
  haveI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp
    ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _))
  obtain ⟨ψ, hψ⟩ := MMP.Resolution.Bridges.exists_algHom_henselization_approx (k := k) Rh B.val 1
  have hKA : (Ideal.Quotient.mk (Im ^ (0 + 1))).comp (emb.toRingHom.comp ψ.toRingHom) =
      (Ideal.Quotient.mk (Im ^ (0 + 1))).comp B.val.toRingHom := by
    haveI := AdicCompletion.algebraMap_isLocalHom_of_fg
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    have hle : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R ^ 1) ≤ Im ^ (0 + 1) := by
      rw [pow_one, zero_add, pow_one, Ideal.map_le_iff_le_comap]
      intro r hr
      exact map_nonunit (algebraMap R A) r hr
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    exact (Ideal.Quotient.eq.mpr (hle (hψ x))).symm
  let ιB : Spec (.of B) ⟶ Spec (.of B0) := D1.map j1.hom
  let ψS : Spec (.of Rh) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hψg1 : ψS ≫ ιB ≫ g1 =
      Spec.map (CommRingCat.ofHom (algebraMap R Rh)) ≫ S.fromSpecStalk s := by
    have hring : (CommRingCat.ofHom (algebraMap R B0) ≫ CommRingCat.ofHom (Subalgebra.inclusion
        (Algebra.adjoin_mono (Finset.coe_subset.mpr (Finset.empty_subset _)))).toRingHom) ≫
        CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap R Rh) := by
      ext r
      exact ψ.commutes r
    rw [← hring, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
    rfl
  -- the henselization as a cofiltered limit over a small index category
  obtain ⟨-, ι, hover, ⟨hιc⟩⟩ :=
    MMP.Resolution.Bridges.isFiltered_affineElementaryEtaleNeighborhood_and_isColimit S s Rh
  obtain ⟨K, _, _, Φ, _⟩ := exists_small_cofiltered_initial_affineElementaryEtaleNeighborhood S s
  haveI := Functor.final_op_of_initial Φ
  let G2 : Kᵒᵖ ⥤ CommRingCat.{0} := Φ.op ⋙ MMP.Resolution.Bridges.affineGlobalSections S s
  let cc : Cocone G2 := (Cocone.mk _ ι).whisker Φ.op
  have hcc : IsColimit cc := (Functor.Final.isColimitWhiskerEquiv Φ.op _).symm hιc
  let D2 : K ⥤ Scheme.{0} := G2.rightOp ⋙ Scheme.Spec
  let c2 : Cone D2 := Scheme.Spec.mapCone (coneRightOpOfCocone cc)
  have hc2 : IsLimit c2 := isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hcc)
  haveI : ∀ {i j : K} (g : i ⟶ j), IsAffineHom (D2.map g) := by
    intro i j g
    dsimp [D2]
    infer_instance
  let i2 : K := (IsCofiltered.nonempty (C := K)).some
  let U0 := (Φ.obj i2).obj
  haveI : IsAffine U0.obj.scheme := (Φ.obj i2).property
  let g2 : Spec Γ(U0.obj.scheme, ⊤) ⟶ S := U0.obj.scheme.isoSpec.inv ≫ U0.obj.toBase
  let πh : Spec (.of Rh) ⟶ Spec Γ(U0.obj.scheme, ⊤) := c2.π.app i2
  have hπh : πh ≫ g2 =
      Spec.map (CommRingCat.ofHom (algebraMap R Rh)) ≫ S.fromSpecStalk s :=
    SpecMap_comp_isoSpec_inv_toBase_of_isOverStalk U0 (ι.app (op (Φ.obj i2)))
      (hover (op (Φ.obj i2)))
  have hY2 : IsProjectiveMorphism (pullback.snd f g2) := hf.baseChange g2
  haveI : IsProper (pullback.snd f g2) := isProper_of_isProjectiveMorphism _ hY2
  haveI : IsAffine (D2.obj i2) := by
    dsimp [D2]
    infer_instance
  let Y2 : Over (D2.obj i2) := Over.mk (pullback.snd f g2)
  haveI : CompactSpace Y2.left := compactSpace_of_isProper (pullback.snd f g2)
  haveI : QuasiSeparatedSpace Y2.left := quasiSeparatedSpace_of_isProper (pullback.snd f g2)
  -- the stage of the completion, pulled back to the henselization
  let ρ : pullback (pullback.snd f g2) πh ⟶ pullback (pullback.snd f g1) ιB :=
    pullback.lift (pullback.lift (pullback.fst _ πh ≫ pullback.fst f g2)
      (pullback.snd _ πh ≫ ψS ≫ ιB) (by
        simp only [Category.assoc]
        rw [pullback.condition (f := f) (g := g2), ← Category.assoc,
          pullback.condition (f := pullback.snd f g2) (g := πh), Category.assoc, hπh, hψg1]))
      (pullback.snd _ πh ≫ ψS) (by rw [pullback.lift_snd, Category.assoc])
  let Mh2 := (Scheme.Modules.pullback ρ).obj N1
  haveI hMh2 : Stacks.Ample.IsInvertibleModule _ Mh2 := @isInvertibleModule_pullback _ _ ρ N1 hN1
  obtain ⟨j2, N2, hN2, ⟨eN2⟩⟩ := exists_isInvertibleModule_pullback_bcπ D2 c2 hc2 i2 Y2 Mh2
    (hM := hMh2)
  -- the étale neighbourhood and the extension
  let U := (Φ.obj j2.left).obj
  haveI : IsAffine U.obj.scheme := (Φ.obj j2.left).property
  let hU : U.obj.scheme ⟶ U0.obj.scheme := (Φ.map j2.hom).hom.hom.hom
  have hUover : hU ≫ U0.obj.toBase = U.obj.toBase := (Φ.map j2.hom).hom.hom.over
  let δ : Spec Γ(U.obj.scheme, ⊤) ⟶ Spec Γ(U0.obj.scheme, ⊤) := Spec.map hU.appTop
  have hτ : pullback.fst f U.obj.toBase ≫ f =
      (pullback.snd f U.obj.toBase ≫ U.obj.scheme.isoSpec.hom ≫ δ) ≫ g2 := by
    simp only [δ, g2, Category.assoc]
    rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id_assoc, hUover, pullback.condition]
  let τ : pullback f U.obj.toBase ⟶ pullback (pullback.snd f g2) δ :=
    pullback.lift (pullback.lift (pullback.fst f U.obj.toBase)
      (pullback.snd f U.obj.toBase ≫ U.obj.scheme.isoSpec.hom ≫ δ) hτ)
      (pullback.snd f U.obj.toBase ≫ U.obj.scheme.isoSpec.hom)
      (by rw [pullback.lift_snd, Category.assoc])
  refine ⟨U, (Scheme.Modules.pullback τ).obj N2, @isInvertibleModule_pullback _ _ τ N2 hN2, ?_⟩
  -- the closed fibre inside the base change to the henselization
  let bX0' : X0 ⟶ Spec (.of Rh) :=
    bX0 ≫ adicThickeningι A Im 0 ≫ Spec.map (CommRingCat.ofHom emb.toRingHom)
  have hσ : pX0 ≫ f = (bX0' ≫ πh) ≫ g2 := by
    have hemb : CommRingCat.ofHom (algebraMap R Rh) ≫ CommRingCat.ofHom emb.toRingHom =
        CommRingCat.ofHom (algebraMap R A) :=
      CommRingCat.hom_ext (RingHom.ext emb.commutes)
    rw [hpX0, Category.assoc, hπh, ← hemb, Spec.map_comp]
    simp only [bX0', Category.assoc]
  let σ : X0 ⟶ pullback (pullback.snd f g2) πh :=
    pullback.lift (pullback.lift pX0 (bX0' ≫ πh) hσ) bX0' (by rw [pullback.lift_snd])
  let πB : Spec (.of A) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom B.val.toRingHom)
  have hKA' : adicThickeningι A Im 0 ≫ Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ ψS =
      adicThickeningι A Im 0 ≫ πB := by
    have h := CommRingCat.hom_ext (f := CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom emb.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Im ^ (0 + 1))))
      (g := CommRingCat.ofHom B.val.toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (Im ^ (0 + 1))))
      hKA
    have h2 := congrArg Spec.map h
    simp only [Spec.map_comp, Category.assoc] at h2
    exact h2
  have hπAB : πB ≫ ιB = πA := c1.w j1.hom
  let β1 : pullback (pullback.snd f g1) πA ⟶ pullback (pullback.snd f g1) ιB :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ πB)
      (by rw [pullback.condition, Category.assoc, hπAB])
  have hβ1 : LimitDescent.bcπ D1 c1 i1 Y1 j1 = β1 := bcπ_eq_lift D1 c1 i1 Y1 j1
  have hb : bX0' ≫ ψS = pullback.fst fX (adicThickeningι A Im 0) ≫
      pullback.snd (pullback.snd f g1) πA ≫ πB := by
    rw [← Category.assoc, pullback.condition]
    simp only [bX0', bX0, Category.assoc, hKA']
  have hE1 : σ ≫ ρ = pullback.fst fX (adicThickeningι A Im 0) ≫ β1 := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [σ, ρ, β1, pX0, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [σ, ρ, β1, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd, pullback.lift_snd_assoc]
        rw [← Category.assoc bX0', hb, pullback.condition (f := pullback.snd f g1) (g := πA)]
        simp only [Category.assoc, hπAB]
    · simp only [σ, ρ, β1, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hb
  let πU : Spec (.of Rh) ⟶ Spec Γ(U.obj.scheme, ⊤) := c2.π.app j2.left
  have hπUδ : πU ≫ δ = πh := c2.w j2.hom
  let β2 : pullback (pullback.snd f g2) πh ⟶ pullback (pullback.snd f g2) δ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ πU)
      (by rw [pullback.condition, Category.assoc, hπUδ])
  have hβ2 : LimitDescent.bcπ D2 c2 i2 Y2 j2 = β2 := bcπ_eq_lift D2 c2 i2 Y2 j2
  haveI := IsLocalRing.isLocalHom_henselizationToAdicCompletion R Rh
  let χ : Rh →+* A ⧸ Im ^ (0 + 1) := (Ideal.Quotient.mk (Im ^ (0 + 1))).comp emb.toRingHom
  have hχ : ∀ x ∈ IsLocalRing.maximalIdeal Rh, χ x = 0 := by
    intro x hx
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [← hIm]
    exact map_nonunit emb.toRingHom x hx
  have he' : ∀ r, e.hom ((S.residue s).hom r) = χ (algebraMap R Rh r) := by
    intro r
    change eR (IsLocalRing.residue R r) = _
    rw [he]
    exact congrArg (Ideal.Quotient.mk _) (emb.commutes r).symm
  let legU : Γ(U.obj.scheme, ⊤) ⟶ CommRingCat.of Rh := ι.app (op (Φ.obj j2.left))
  have hχs : CommRingCat.ofHom χ = CommRingCat.ofHom emb.toRingHom ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (Im ^ (0 + 1))) := rfl
  have hlegU : Spec.map (legU ≫ CommRingCat.ofHom χ) = adicThickeningι A Im 0 ≫
      Spec.map (CommRingCat.ofHom emb.toRingHom) ≫ πU := by
    rw [hχs, ← Category.assoc, Spec.map_comp, Spec.map_comp]
    rfl
  have hKB : bX0 ≫ Spec.map e ≫ elementaryNeighborhoodSection U ≫ U.obj.scheme.isoSpec.hom =
      bX0' ≫ πU := by
    rw [SpecMap_comp_section_comp_isoSpec_hom U legU (hover _) χ hχ e he', hlegU]
    simp only [bX0', Category.assoc]
  have hθ1 : θ ≫ pullback.fst f (S.fromSpecResidueField s) = pX0 := pullback.lift_fst _ _ _
  have hθ2 : θ ≫ pullback.snd f (S.fromSpecResidueField s) = bX0 ≫ Spec.map e :=
    pullback.lift_snd _ _ _
  have hE2 : θ ≫ localEtaleFibreMap f U ≫ τ = σ ≫ β2 := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [τ, β2, σ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          localEtaleFibreMap_fst_assoc, localEtaleFibreMap_fst]
        exact hθ1
      · simp only [τ, β2, σ, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          pullback.lift_snd, pullback.lift_snd_assoc, localEtaleFibreMap_snd_assoc]
        rw [reassoc_of% hθ2, ← hπUδ, ← Category.assoc bX0', ← hKB]
        simp only [Category.assoc]
    · simp only [τ, β2, σ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        localEtaleFibreMap_snd_assoc]
      rw [reassoc_of% hθ2]
      exact hKB
  -- the chain of isomorphisms
  refine nonempty_iso_of_isIso_pullback θ ?_
  exact pullbackCompIso rfl _ ≪≫ pullbackCompIso rfl _ ≪≫
    (Scheme.Modules.pullbackCongr (by rwa [Category.assoc])).app N2 ≪≫
    (pullbackCompIso rfl N2).symm ≪≫
    (Scheme.Modules.pullback σ).mapIso (eN2 ≪≫ (Scheme.Modules.pullbackCongr hβ2).app N2).symm ≪≫
    pullbackCompIso hE1 N1 ≪≫ (pullbackCompIso rfl N1).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (eN1 ≪≫ (Scheme.Modules.pullbackCongr hβ1).app N1).symm ≪≫
    eMh

end Main

section Components

/-- `deg(L^{⊗ m}) = m · deg(L)` for an invertible module on a proper scheme of dimension at most
one over a field. -/
theorem invertibleCurveDegree_tensorPowModule_natCast {k : Type} [Field k] {D : Scheme.{0}}
    (g : D ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim D ≤ 1) (L : D.Modules)
    [Stacks.Ample.IsInvertibleModule D L] (m : ℕ) :
    invertibleCurveDegree k g hdim (Stacks.Ample.tensorPowModule D L (m : ℤ)) =
      (m : ℤ) * invertibleCurveDegree k g hdim L := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact invertibleCurveDegree_eq_zero_of_iso_unit k g _ _
      (Stacks.Ample.tensorPowModuleZeroIso D L)
  | succ m ih =>
    have e := Stacks.Ample.tensorPowModuleAddIso D L (m : ℤ) 1
    have h1 := invertibleCurveDegree_eq_of_iso k g hdim e
    have h2 := invertibleCurveDegree_tensorSheaf_eq_add k g hdim
      (Stacks.Ample.tensorPowModule D L (m : ℤ)) (Stacks.Ample.tensorPowModule D L 1)
    have h3 := invertibleCurveDegree_eq_of_iso k g hdim (Stacks.Ample.tensorPowModuleOneIso D L)
    push_cast
    rw [← h1, h2, ih, h3]
    ring

/-- The reduced closed subscheme on an irreducible closed subset is integral. -/
theorem isIntegral_subscheme_vanishingIdeal {Y : Scheme.{0}} (Z : Closeds Y)
    (hZ : IsIrreducible (Z : Set Y)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible Z hZ

variable {S X : Scheme.{0}}

/-- The scheme fibre of a projective morphism is proper over the residue field. -/
theorem isProper_pointSettingFibre (f : X ⟶ S) (hf : IsProjectiveMorphism f) (s : S) :
    IsProper (pullback.snd f (S.fromSpecResidueField s)) :=
  isProper_of_isProjectiveMorphism _ (hf.baseChange _)

/-- The scheme fibre of a projective morphism carries an ample invertible module. -/
theorem exists_isAmple_pointSettingFibre (f : X ⟶ S) (hf : IsProjectiveMorphism f) (s : S) :
    ∃ (H : (pointSettingFibre f s).Modules) (_ : Stacks.Ample.IsInvertibleModule _ H),
      Scheme.Modules.IsAmple _ H := by
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (S.residueField s))
  obtain ⟨H, hH, hHa⟩ := AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism
    (pullback.snd f (S.fromSpecResidueField s)) M hMa (hf.baseChange _)
  exact ⟨H, hH, (Stacks.AmpleBridge.isAmple_iff_isAmple _ H).mp hHa⟩

/-- The reduced closed subscheme on a closed subset of the fibre is proper over the residue
field. -/
theorem isProper_subschemeι_comp_pointSettingFibre (f : X ⟶ S) (hf : IsProjectiveMorphism f)
    (s : S) (D : Closeds (pointSettingFibre f s)) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫
      pullback.snd f (S.fromSpecResidueField s)) :=
  haveI := isProper_pointSettingFibre f hf s
  inferInstance

/-- **Extension from one component of the fibre with large degrees on the others.**
Let `C` be an irreducible component of the fibre `F`, with its reduced (integral)
closed subscheme `C_red`, and let `L` be an invertible sheaf on `C_red`. For every `n` there are an
elementary étale neighbourhood `(S', s')` and an invertible sheaf on `X ×_S S'` restricting to `L`
on `C_red` and of degree at least `n` on every other one-dimensional component of `F`.

The degree is `AlgebraicGeometry.invertibleCurveDegree` over `κ(s)` of the restriction to the
reduced closed subscheme on the component; that subscheme is proper over `κ(s)`
(`MMP.Fourfold.isProper_subschemeι_comp_pointSettingFibre`). -/
@[mmp "lem_fourfold_curve_fibre_line_bundle_etale_extension"]
theorem exists_elementaryEtaleNeighborhood_extension_of_component {k : Type} [Field k]
    (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS] (f : X ⟶ S) (hf : IsProjectiveMorphism f)
    (s : S) (hdim : topologicalKrullDim (pointSettingFibre f s) ≤ 1)
    (C : Closeds (pointSettingFibre f s))
    (hC : (C : Set (pointSettingFibre f s)) ∈ irreducibleComponents (pointSettingFibre f s))
    (L : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Modules)
    [Stacks.Ample.IsInvertibleModule _ L] (n : ℕ) :
    ∃ (U : ElementaryEtaleNeighborhood S s) (M : (pullback f U.obj.toBase).Modules)
      (hM : Stacks.Ample.IsInvertibleModule _ M),
      Nonempty ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫
        localEtaleFibreMap f U)).obj M ≅ L) ∧
      ∀ (D : Closeds (pointSettingFibre f s)),
        (D : Set (pointSettingFibre f s)) ∈ irreducibleComponents (pointSettingFibre f s) →
        D ≠ C →
        ∀ hD1 : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal D).subscheme = 1,
          haveI := isProper_subschemeι_comp_pointSettingFibre f hf s D
          haveI := @isInvertibleModule_pullback _ _
            ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫ localEtaleFibreMap f U) M hM
          (n : ℤ) ≤ invertibleCurveDegree (S.residueField s)
            ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫
              pullback.snd f (S.fromSpecResidueField s)) hD1.le
            ((Scheme.Modules.pullback ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫
              localEtaleFibreMap f U)).obj M) := by
  classical
  haveI := isProper_pointSettingFibre f hf s
  haveI : LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)) :=
    IsProper.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (pointSettingFibre f s) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (S.fromSpecResidueField s))
  haveI : CompactSpace (pointSettingFibre f s) :=
    compactSpace_of_isProper (pullback.snd f (S.fromSpecResidueField s))
  haveI : IsNoetherian (pointSettingFibre f s) := {}
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  obtain ⟨H, hH, hHa⟩ := exists_isAmple_pointSettingFibre f hf s
  let Hm := Stacks.Ample.tensorPowModule _ H (n : ℤ)
  -- glue `L` on `C` with `H^{⊗ n}` on the other components, on their scheme-theoretic union
  let L' : ∀ b, (Stacks.LiftInvertible.coverScheme i b).Modules := fun b =>
    match b with
    | true => L
    | false => (Scheme.Modules.pullback (Stacks.LiftInvertible.coverMap i false)).obj Hm
  haveI hL' : ∀ b, Stacks.Ample.IsInvertibleModule _ (L' b) := by
    intro b
    cases b with
    | true =>
      change Stacks.Ample.IsInvertibleModule _ L
      infer_instance
    | false => exact isInvertibleModule_pullback _ _
  obtain ⟨MW, hMW, hMWres⟩ :=
    Stacks.ClosedCoverKer.exists_invertible_of_closed_cover_discrete_intersections_of_iInf_ker _
      (Stacks.LiftInvertible.coverScheme i) (Stacks.LiftInvertible.coverLift i)
      (Stacks.LiftInvertible.exists_coverLift_eq i)
      (Stacks.LiftInvertible.discreteTopology_range_coverLift_inter i hdim)
      (Stacks.LiftInvertible.iInf_ker_coverLift i) L'
  -- lift from the union to the fibre
  obtain ⟨MF, hMF, ⟨eF⟩⟩ :=
    Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one _ _
      (Stacks.LiftInvertible.closedUnionIdeal i).subschemeι hdim MW
  -- extend to an elementary étale neighbourhood
  obtain ⟨U, M, hM, ⟨eM⟩⟩ := @exists_elementaryEtaleNeighborhood_extension k _ S X sS _ f hf s
    hdim MF hMF
  refine ⟨U, M, hM, ⟨?_⟩, ?_⟩
  · exact (pullbackCompIso rfl M).symm ≪≫ (Scheme.Modules.pullback i).mapIso eM ≪≫
      (pullbackCompIso (Stacks.LiftInvertible.coverLift_subschemeι i true) MF).symm ≪≫
      (Scheme.Modules.pullback _).mapIso eF ≪≫ (hMWres true).some
  · intro D hD hDC hD1
    -- `D` is one of the components that `C` misses
    have hsub : D ≤ Stacks.LiftInvertible.complementaryClosed i := by
      intro x hx
      refine ⟨D, ⟨hD, fun hDsub => hDC ?_⟩, hx⟩
      have hDC' : (D : Set (pointSettingFibre f s)) ⊆ C := by
        rwa [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal] at hDsub
      exact SetLike.coe_injective (subset_antisymm hDC' (hD.2 hC.1 hDC'))
    let ιD := (Scheme.IdealSheafData.vanishingIdeal D).subschemeι
    let jD : (Scheme.IdealSheafData.vanishingIdeal D).subscheme ⟶
        Stacks.LiftInvertible.coverScheme i false :=
      Scheme.IdealSheafData.inclusion (Scheme.IdealSheafData.vanishingIdeal_antimono hsub)
    have hjD : jD ≫ Stacks.LiftInvertible.coverMap i false = ιD :=
      Scheme.IdealSheafData.inclusion_subschemeι _
    have hW : (jD ≫ Stacks.LiftInvertible.coverLift i false) ≫
        (Stacks.LiftInvertible.closedUnionIdeal i).subschemeι = ιD := by
      rw [Category.assoc, Stacks.LiftInvertible.coverLift_subschemeι, hjD]
    haveI := isProper_subschemeι_comp_pointSettingFibre f hf s D
    haveI := @isInvertibleModule_pullback _ _ (ιD ≫ localEtaleFibreMap f U) M hM
    haveI : Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback ιD).obj H) :=
      isInvertibleModule_pullback _ _
    let eD : (Scheme.Modules.pullback (ιD ≫ localEtaleFibreMap f U)).obj M ≅
        Stacks.Ample.tensorPowModule _ ((Scheme.Modules.pullback ιD).obj H) (n : ℤ) :=
      (pullbackCompIso rfl M).symm ≪≫ (Scheme.Modules.pullback ιD).mapIso eM ≪≫
        (pullbackCompIso hW MF).symm ≪≫ (Scheme.Modules.pullback _).mapIso eF ≪≫
        (pullbackCompIso rfl MW).symm ≪≫ (Scheme.Modules.pullback jD).mapIso (hMWres false).some ≪≫
        pullbackCompIso hjD Hm ≪≫ Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso ιD H n
    rw [invertibleCurveDegree_eq_of_iso _ _ hD1.le eD,
      invertibleCurveDegree_tensorPowModule_natCast]
    haveI := isIntegral_subscheme_vanishingIdeal D hD.1
    have hpos := invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom (S.residueField s)
      (ιD ≫ pullback.snd f (S.fromSpecResidueField s)) hD1 ιD H hHa
    nlinarith

end Components

end MMP.Fourfold
