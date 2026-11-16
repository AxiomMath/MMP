module

public import MMP.AlgebraicGeometry.Morphisms.GenericSmoothness
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowup
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy

/-!
# Elliptic fibrations in the proof of abundance (FA 15)

Two steps of the proof of FA 15.9, about a log elliptic fiber space `f_U : U ⟶ Z` on an open
`U` of a variety `X` satisfying the assumptions of FA 15.4.

The first is the conservation of the generic degree along a curve fibration. Let `k` be an
algebraically closed field of characteristic zero, `g : V ⟶ W` a proper surjective morphism of
`k`-varieties with `V` normal and `dim V = dim W + 1`, and `L` a `ℚ`-Cartier `ℚ`-divisor on `V`.
There is a dense open `W⁰ ⊆ W` over which the fibres are smooth, and for every closed point
`w ∈ W⁰` the fibre `V_w` is a proper curve with irreducible components `C₁, …, C_r`, each of
multiplicity one in `[V_w]`, such that `deg_{k(W)} L|_{V_η} = ∑ⱼ (L · Cⱼ)`.

The proof has two steps. The local rings of `V` at the points over the generic point of `W` are
regular, so the image of the singular locus of `V`, closed since `g` is proper, is a proper closed
subset; away from it generic smoothness makes `g` smooth, and the fibres are curves over a dense
open. With `E = m L` Cartier, the Euler characteristics of `𝒪_V(E)` and `𝒪_V` on the fibres are
locally constant over that open, hence constant, and their difference is the degree of `𝒪_V(E)`
on the fibre. On the regular generic fibre `V_η` this degree is `∑ E_P [κ(P) : κ(η)]` by
Riemann–Roch in divisor form, which is `m · deg_{k(W)} L|_{V_η}`; on a smooth closed fibre over
`κ(w) = k` it is the sum of the degrees on its components, each of multiplicity one, which is
`m · ∑_C (L · C)`.

The second: a `(K_X + Δ_X)`-trivially connected prime divisor `D` has `f_U(D ∩ U)` not dense in
`Z`. Write `L = K_X + Δ_X`. By (15.4.2) some multiple `M = mL` is Cartier with
`h⁰(X, 𝒪_X(M)) ≥ 2`, so the divisor of zeros `B` of a suitable section is an effective member of
`|M|` through a closed point `x ∈ D`. As `B ∼ mL`, `B` is trivial on `L`-trivial curves, so
`D ⊆ Supp B` by trivial connectedness. If `f_U(Supp B ∩ U)` were dense it would be all of `Z`
(`f_U` is proper). Over the dense open `Z⁰` above, the fibre over a closed point is a connected
proper curve whose components have nonnegative `L`-degrees summing to `L · E_{f_U} = 0`; meeting
`Supp B`, it lies in `Supp B`. Every closed point of the nonempty open `f_U⁻¹(Z⁰)` then lies in
`Supp B`, hence so does the generic point of `X`, which is impossible.

## Main results

* `MMP.Flips.exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber`: the conservation
  of the generic degree.
* `MMP.Flips.not_dense_image_of_isTriviallyConnected`: `f_U(D ∩ U)` is not dense in `Z`.
* `MMP.Flips.intersectionNumber_restrictOpen`: for a dense open `U ⊆ X` and a curve
  `i : C ⟶ U` proper over `k`, `(L|_U · C) = (L · C)`, the latter along `C ⟶ U ⟶ X`.
* `MMP.Flips.exists_properCurve_of_opens`: a proper curve of `U` is a proper curve of `X`.

## Implementation notes

The source works over `ℂ`; the statements are made over any algebraically closed field `k` of
characteristic zero. Algebraic closedness makes the residue field of a closed point equal to `k`,
so that intersection numbers over `k` are degrees over the residue fields of the fibres.

The irreducible components of the fibre `g⁻¹(w)` are recorded by their generic points, the points
of `g⁻¹(w)` with no proper generalization inside `g⁻¹(w)`; each is the generic point of a proper
curve `MMP.Mori.ProperCurve` of `V`. Since the fibre is smooth over `κ(w)`, it is reduced, so all
multiplicities in its fundamental cycle equal one. The degree on the generic fibre is
`MMP.Flips.genericFiberDegree`, computed on the pull-back of a Cartier multiple of `L` to `V_η`,
whose prime divisors are the prime divisors of `V` dominating `W`.

The prime divisor `D` is the divisor `1 · D` (`Finsupp.single D 1`), and `D ∩ U` is the preimage
of the support of `D` under the inclusion `U ⟶ X`. Intersection numbers on `U` are compared with
those on `X`: along `U ⟶ X` the restriction of a divisor by local lengths
(`MMP.Mori.DivisorWithCoeffs.restrict`) is the restriction by coefficients
(`MMP.Mori.DivisorWithCoeffs.restrictOpen`), which for a Cartier divisor is its pull-back, and a
proper curve of `U` is a proper curve of `X` isomorphic to it over `X`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 15,
  proof of 15.9
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Flips

section GenericFibreDegree

open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open Stacks.AlgebraicGeometry.ComponentDegrees

/-- The fibre of `p` over a point `t` of an open `U` is the fibre of `p ∣_ U` over `t`. -/
private theorem exists_isPullback_fiber_restrict {V T : Scheme.{u}}
    (p : V ⟶ T) (U : T.Opens) (t : T) (ht : t ∈ U) :
    ∃ (a : p.fiber t ⟶ p ⁻¹ᵁ U) (g' : Spec (T.residueField t) ⟶ U),
      a ≫ (p ⁻¹ᵁ U).ι = p.fiberι t ∧ g' ≫ U.ι = T.fromSpecResidueField t ∧
      IsPullback a (p.fiberToSpecResidueField t) (p ∣_ U) g' := by
  have hr : Set.range (T.fromSpecResidueField t) ⊆ Set.range U.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using ht
  let g' := IsOpenImmersion.lift U.ι (T.fromSpecResidueField t) hr
  have hg : g' ≫ U.ι = T.fromSpecResidueField t := IsOpenImmersion.lift_fac _ _ _
  have hR := (isPullback_morphismRestrict p U).flip
  have hF : IsPullback (p.fiberι t) (p.fiberToSpecResidueField t) p (T.fromSpecResidueField t) :=
    IsPullback.of_hasPullback _ _
  let a := hR.lift (p.fiberι t) (p.fiberToSpecResidueField t ≫ g')
    (by simpa only [Category.assoc, hg] using hF.w)
  have h1 : a ≫ (p ⁻¹ᵁ U).ι = p.fiberι t := hR.lift_fst _ _ _
  have h2 : a ≫ p ∣_ U = p.fiberToSpecResidueField t ≫ g' := hR.lift_snd _ _ _
  refine ⟨a, g', h1, hg, ?_⟩
  refine IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ U).ι) (h₂₂ := U.ι) ?_ h2 hR
  rwa [h1, hg]

/-- An invertible module on a scheme flat over `S` is flat over `S`. -/
private theorem isFlatOver_of_isInvertibleModule {X S : Scheme.{u}} (π : X ⟶ S) [Flat π]
    (F : X.Modules) [Stacks.Ample.IsInvertibleModule X F] :
    IsFlatOver π.toLRSHom.toShHom F := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      X.presheaf _ _).mp ‹_›
  have : F.IsQuasicoherent := Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule F
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry F).mp
      (@Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ F h0)
  obtain ⟨-, hfree⟩ :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae F).out 4 2).mp hflf
  intro x
  letI := (π.stalkMap x).hom.toAlgebra
  have : Module.Flat (S.presheaf.stalk (π x)) (X.presheaf.stalk x) := Flat.stalkMap π x
  have := hfree x
  letI : Module (S.presheaf.stalk (π x)) (F.presheaf.stalk x) :=
    Module.compHom _ (π.stalkMap x).hom
  have : IsScalarTower (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := Module.Flat.of_free
  exact Module.Flat.trans (S.presheaf.stalk (π x)) (X.presheaf.stalk x) (F.presheaf.stalk x)

/-- Over a preconnected open `U` on which a proper `p` is smooth, the fibrewise Euler
characteristic of an invertible module is constant. -/
private theorem fibreEulerCharacteristic_eq_of_smooth_restrict {V T : Scheme.{u}}
    (p : V ⟶ T) [IsProper p] (U : T.Opens) [Smooth (p ∣_ U)]
    (hU : _root_.IsPreconnected (U : Set T)) (F : V.Modules) [Stacks.Ample.IsInvertibleModule V F]
    {t t' : T} (ht : t ∈ U) (ht' : t' ∈ U) :
    fibreEulerCharacteristic p F t = fibreEulerCharacteristic p F t' := by
  let F' := (Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj F
  have : LocallyOfFinitePresentation (p ∣_ U) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth (f := p ∣_ U)
  have hfp : FinitePresentation (p ∣_ U) :=
    ⟨inferInstance, inferInstanceAs (QuasiCompact (p ∣_ U)),
      @IsSeparated.instQuasiSeparated _ _ (p ∣_ U) IsProper.toIsSeparated⟩
  have hF'fp : F'.IsFinitePresentation :=
    @Stacks.Divisors.isFinitePresentation_of_isInvertible _ F'
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mp (inferInstance : Stacks.Ample.IsInvertibleModule _ F'))
  have hflat := isFlatOver_of_isInvertibleModule (p ∣_ U) F'
  have key : ∀ s (_ : s ∈ U), ∃ u, fibreEulerCharacteristic p F s =
      fibreEulerCharacteristic (p ∣_ U) F' u := by
    intro s hs
    obtain ⟨a, g', h1, -, hsq⟩ := exists_isPullback_fiber_restrict p U s hs
    have h := chiDerivedFibre_eq_eulerSum (p ∣_ U) hfp F' hF'fp hflat _ g' a _ hsq
      (IsLocalRing.closedPoint _)
    rw [← fibreEulerCharacteristic_eq_chiDerivedFibre (p ∣_ U) hfp F' hF'fp hflat] at h
    have e : (Scheme.Modules.pullback (p.fiberι s)).obj F ≅ (Scheme.Modules.pullback a).obj F' :=
      (eqToIso (by rw [h1])).trans ((Scheme.Modules.pullbackComp a (p ⁻¹ᵁ U).ι).app F).symm
    exact ⟨_, (eulerSum_congr _ (p.fiberToSpecResidueField s) e).trans h.symm⟩
  have hlc := isLocallyConstant_fibreEulerCharacteristic (p ∣_ U) hfp F' hF'fp hflat
  obtain ⟨u, hu⟩ := key t ht
  obtain ⟨u', hu'⟩ := key t' ht'
  rw [hu, hu']
  have : PreconnectedSpace U := Subtype.preconnectedSpace hU
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ trivial trivial

/-- The fibre of `p` over a point of an open over which `p` is smooth is smooth over the
residue field. -/
private theorem smooth_fiberToSpecResidueField_of_smooth_restrict {V T : Scheme.{u}}
    (p : V ⟶ T) (U : T.Opens) [Smooth (p ∣_ U)] (t : T) (ht : t ∈ U) :
    Smooth (p.fiberToSpecResidueField t) := by
  obtain ⟨a, g', -, -, hsq⟩ := exists_isPullback_fiber_restrict p U t ht
  exact MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance

/-- Cancellation in `WithBot ℕ∞` against a finite summand: `a + d = d + 1` forces `a = 1`. -/
private theorem eq_one_of_add_eq_add_one {a d : WithBot ℕ∞} (hb : d ≠ ⊥) (ht : d ≠ ⊤)
    (h : a + d = d + 1) : a = 1 := by
  lift d to ℕ∞ using hb
  lift d to ℕ using (by simpa using ht)
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h (by norm_cast)
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => norm_cast at h
    | coe a => norm_cast at h ⊢; omega

/-- There is a dense open of `W` over which `g` is smooth, with smooth fibres all of whose
irreducible components are curves. -/
private theorem exists_dense_open_smooth_restrict
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1) :
    ∃ U : W.Opens, Dense (U : Set W) ∧ Smooth (g ∣_ U) ∧
      ∀ w ∈ U, Smooth (g.fiberToSpecResidueField w) ∧
        ∀ Z ∈ irreducibleComponents (g.fiber w), topologicalKrullDim Z = 1 := by
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have : AlgebraicGeometry.IsVariety k sV := AlgebraicGeometry.IsVariety.mk
  have : AlgebraicGeometry.IsVariety k sW := AlgebraicGeometry.IsVariety.mk
  obtain ⟨V', hV'd, hV'⟩ := (MMP.topologicalKrullDim_fiber_of_isDominant k sV sW g hg).2.1
  have hbot : topologicalKrullDim W ≠ ⊥ := Order.krullDim_ne_bot_iff.mpr
    ⟨⟨closure {genericPoint W}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hdimZ : ∀ w ∈ V', ∀ Z ∈ irreducibleComponents (g.fiber w), topologicalKrullDim Z = 1 :=
    fun w hw Z hZ => eq_one_of_add_eq_add_one hbot
      (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sW) ((hV' w hw Z hZ).trans hdim)
  let Z : Set V := (sV.smoothLocus : Set V)ᶜ
  have hZ : IsClosed Z := sV.smoothLocus.isOpen.isClosed_compl
  have hgZ : IsClosed (g '' Z) := g.isClosedMap Z hZ
  have hη : genericPoint W ∉ g '' Z := by
    rintro ⟨z, hz, hgz⟩
    exact hz (((MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField sV).1 z).2
      (isRegularLocalRing_stalk_of_mem_genericFiber sV sW g hg hdim hgz))
  let U₀ : W.Opens := ⟨(g '' Z)ᶜ, hgZ.isOpen_compl⟩ ⊓ V'
  have hηU₀ : genericPoint W ∈ U₀ :=
    ⟨hη, (genericPoint_spec W).mem_open_set_iff V'.isOpen |>.mpr
      (by obtain ⟨u, hu⟩ := hV'd.nonempty; exact ⟨u, trivial, hu⟩)⟩
  obtain ⟨v, hv⟩ := g.surjective (genericPoint W)
  have hvU₀ : v ∈ g ⁻¹ᵁ U₀ := by simpa [hv] using hηU₀
  have : Nonempty U₀ := ⟨⟨_, hηU₀⟩⟩
  have : Nonempty (g ⁻¹ᵁ U₀) := ⟨⟨_, hvU₀⟩⟩
  let : (g ⁻¹ᵁ U₀).toScheme.Over (Spec (.of k)) := ⟨(g ⁻¹ᵁ U₀).ι ≫ sV⟩
  let : U₀.toScheme.Over (Spec (.of k)) := ⟨U₀.ι ≫ sW⟩
  have : (g ∣_ U₀).IsOver (Spec (.of k)) := ⟨by
    change g ∣_ U₀ ≫ U₀.ι ≫ sW = (g ⁻¹ᵁ U₀).ι ≫ sV
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hg]⟩
  have : Smooth ((g ⁻¹ᵁ U₀).toScheme ↘ Spec (.of k)) := by
    change Smooth ((g ⁻¹ᵁ U₀).ι ≫ sV)
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
      eq_top_iff]
    rintro x -
    by_contra hx
    exact x.2.1 ⟨x.1, hx, rfl⟩
  have : LocallyOfFiniteType ((g ⁻¹ᵁ U₀).toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType ((g ⁻¹ᵁ U₀).ι ≫ sV))
  have : QuasiCompact ((g ⁻¹ᵁ U₀).toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact ((g ⁻¹ᵁ U₀).ι ≫ sV))
  have : LocallyOfFiniteType (U₀.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (U₀.ι ≫ sW))
  have : QuasiCompact (U₀.toScheme ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (U₀.ι ≫ sW))
  obtain ⟨U, hUd, -, hsm, -⟩ := MMP.exists_dense_smooth_restrict_of_smooth (K := k) (g ∣_ U₀)
  have hsm' : Smooth (g ∣_ U₀.ι ''ᵁ U) := by
    let e := morphismRestrictRestrict g U₀ U
    have hw : g ∣_ U₀.ι ''ᵁ U = inv e.hom.left ≫ (g ∣_ U₀ ∣_ U) ≫ e.hom.right := by
      rw [IsIso.eq_inv_comp]
      exact e.hom.w
    rw [hw]
    infer_instance
  refine ⟨U₀.ι ''ᵁ U, ?_, hsm', fun w hw => ?_⟩
  · obtain ⟨u, hu⟩ := hUd.nonempty
    exact (U₀.ι ''ᵁ U).isOpen.dense ⟨_, ⟨u, hu, rfl⟩⟩
  · refine ⟨smooth_fiberToSpecResidueField_of_smooth_restrict g _ w hw, hdimZ w ?_⟩
    obtain ⟨u, -, rfl⟩ := hw
    exact u.2.2

open MMP.Mori in
/-- On an integral scheme of dimension at most one, the generic point of a prime divisor is a
closed point. -/
private theorem isClosed_singleton_genericPoint_of_dim_le_one {Y : Scheme.{u}} [IsIntegral Y]
    (hdim : topologicalKrullDim Y ≤ 1) (P : Mori.PrimeDivisor Y) :
    IsClosed ({P.genericPoint} : Set Y) := by
  have hne : P.genericPoint ≠ genericPoint Y := by
    intro h
    have h1 := P.coheight_genericPoint
    rw [h] at h1
    have : IsMax (genericPoint Y) := fun b _ =>
      (Scheme.le_iff_specializes.mpr (genericPoint_specializes b))
    rw [Order.coheight_eq_zero.2 this] at h1
    exact zero_ne_one h1
  refine Stacks.Topology.Dimension.isClosed_singleton_of_mem_of_ne_univ hdim
    (T := closure ({P.genericPoint} : Set Y)) isClosed_closure (fun h => hne ?_)
    (subset_closure (Set.mem_singleton _))
  exact (isGenericPoint_def.mpr h).eq (genericPoint_spec Y)

open MMP.Mori DivisorWithCoeffs in
/-- **The degree of a closed point on a curve.** On an integral scheme `C` of dimension at most
one, proper over a field `K`, with factorial local rings, the divisorial sheaf of a prime divisor
`P` has degree `[κ(P) : K]`. -/
private theorem invertibleCurveDegree_divisorialSheaf_single {K : Type u} [Field K]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of K)) [IsProper sC] [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] (hdim : topologicalKrullDim C ≤ 1)
    (hUFD : ∀ x : C, UniqueFactorizationMonoid (C.presheaf.stalk x)) (P : Mori.PrimeDivisor C)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C))] :
    invertibleCurveDegree K sC hdim (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C)) =
      sC.residueDegree P.genericPoint := by
  classical
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have hD0 : 0 ≤ (Finsupp.single P 1 : Divisor C) := Finsupp.single_nonneg.2 zero_le_one
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C)) := hL
  haveI := P.integral
  have hcart : Stacks.Divisors.IsEffectiveCartierDivisor P.idealSheaf :=
    isEffectiveCartierDivisor_of_codimension_one_of_uniqueFactorizationMonoid P.idealSheaf
      P.codimension_one (fun x _ => hUFD x)
  have hZ : AlgebraicGeometry.zeroScheme C
      (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C))
      ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)) = P.idealSheaf := by
    have hloc : ∀ x : C, ∃ V : C.affineOpens, x ∈ (V : C.Opens) ∧
        (AlgebraicGeometry.zeroScheme C
          (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C))
          ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤))).ideal V =
          P.idealSheaf.ideal V := by
      intro x
      obtain ⟨W, hxW, f, φ, hspan, hlocW, hφ⟩ :=
        MMP.Threefold.Resolution.exists_localEquation_of_isEffectiveCartierDivisor P hcart x
      obtain ⟨V, hxV, hVW, ⟨b⟩⟩ := AlgebraicGeometry.exists_affineOpen_dualBasisOne_of_isInvertible
        (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C)) x hxW
      refine ⟨V, hxV, ?_⟩
      rw [AlgebraicGeometry.zeroScheme_ideal_eq_span_evalAt
        (Divisor.divisorialSheaf (Finsupp.single P 1 : Divisor C))
        ((Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤)) V b,
        ← P.idealSheaf.map_ideal hVW, hspan, Ideal.map_span, Set.image_singleton]
      exact MMP.Threefold.Resolution.span_evalAt_eq_span_of_isLocalEquation P hD0 (V : C.Opens) b
        (C.presheaf.map (homOfLE hVW).op f) φ (hlocW.mono hVW) fun Z hZ => by
          rw [hφ Z (hVW hZ)]
          exact (TopCat.Presheaf.germ_res_apply C.presheaf (homOfLE hVW) _ hZ f).symm
    choose U hxU hU using hloc
    exact Scheme.IdealSheafData.ext_of_iSup_eq_top U
      (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩) hU
  have hs : (Divisor.divisorialSheafOneSection hD0).eval (Opposite.op ⊤) ≠ 0 := by
    intro h
    obtain ⟨y⟩ := (inferInstance : Nonempty C)
    let Z : irreducibleComponents C :=
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
    have h1 := congrArg (fun m : Γ(Divisor.divisorialSheaf
      (Finsupp.single P 1 : Divisor C), ⊤) =>
        m.1 (⟨Z, trivial⟩ :
          {Z : irreducibleComponents C // componentGenericPoint C Z ∈ (⊤ : C.Opens)})) h
    change (1 : C.presheaf.stalk (componentGenericPoint C Z)) = 0 at h1
    exact one_ne_zero h1
  rw [invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one K sC hdim _
    (Divisor.divisorialSheafOneSection hD0) hs _ hZ]
  -- the reduced point `P` is a one-point integral scheme
  have hcl := isClosed_singleton_genericPoint_of_dim_le_one hdim P
  have hrange : Set.range P.idealSheaf.subschemeι = {P.genericPoint} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change (P.support : Set C) = _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hcl.closure_eq]
  have : Subsingleton P.idealSheaf.subscheme := ⟨fun a b =>
    P.idealSheaf.subschemeι.isEmbedding.injective (by
      have ha : P.idealSheaf.subschemeι a ∈ Set.range P.idealSheaf.subschemeι := ⟨a, rfl⟩
      have hb : P.idealSheaf.subschemeι b ∈ Set.range P.idealSheaf.subschemeι := ⟨b, rfl⟩
      rw [hrange] at ha hb
      exact ha.trans hb.symm)⟩
  obtain ⟨p, hp⟩ : P.genericPoint ∈ Set.range P.idealSheaf.subschemeι := hrange ▸ rfl
  have h1 := Stacks.Chow.residueDegree_eq_finrank_globalSections K
    (P.idealSheaf.subschemeι ≫ sC) p
  rw [← h1, Stacks.Chow.residueDegree_comp,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion P.idealSheaf.subschemeι, mul_one, hp]

open MMP.Mori DivisorWithCoeffs in
/-- **Riemann–Roch on a curve, in divisor form.** On an integral scheme `C` of dimension at most
one, proper over a field `K`, with factorial local rings, a divisor `D` with invertible
divisorial sheaf has `deg 𝒪_C(D) = ∑_P D_P [κ(P) : K]`. -/
private theorem invertibleCurveDegree_divisorialSheaf_eq_sum {K : Type u} [Field K]
    {C : Scheme.{u}} (sC : C ⟶ Spec (.of K)) [IsProper sC] [IsIntegral C]
    [IsLocallyNoetherian C] [IsNormal C] (hdim : topologicalKrullDim C ≤ 1)
    (hUFD : ∀ x : C, UniqueFactorizationMonoid (C.presheaf.stalk x)) (D : Divisor C)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      D.divisorialSheaf] :
    invertibleCurveDegree K sC hdim D.divisorialSheaf =
      ∑ P ∈ D.support, D P * (sC.residueDegree P.genericPoint : ℤ) := by
  classical
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace sC
  have hcar : ∀ E : Divisor C, E.IsCartier := fun E => by
    rw [← Finsupp.sum_single E]
    induction E using Finsupp.induction_linear with
    | zero => simpa using Divisor.isCartier_zero
    | add f g hf hg =>
      rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by rw [Finsupp.single_add])]
      exact hf.add hg
    | single P n =>
      rw [Finsupp.sum_single_index (by simp), ← Finsupp.smul_single_one]
      exact (MMP.Threefold.Mori.isCartier_single_of_forall_uniqueFactorizationMonoid hUFD P).zsmul n
  have hid : ∀ (E : Divisor C) (hE : E.IsCartier) [AlgebraicGeometry.SheafOfModules.IsInvertible
      C.presheaf C.ringCatSheaf.2 E.divisorialSheaf],
      E.degreeOn K sC (𝟙 C) hdim hE = invertibleCurveDegree K sC hdim E.divisorialSheaf := by
    intro E hE _
    exact invertibleCurveDegree_pullback_of_isIso (𝟙 C) sC hdim hdim _
  let F : Divisor C →+ ℤ :=
    { toFun := fun E => E.degreeOn K sC (𝟙 C) hdim (hcar E)
      map_zero' := Divisor.degreeOn_zero' K sC (𝟙 C) hdim
      map_add' := fun E E' => Divisor.degreeOn_add K sC (𝟙 C) hdim E E' _ _ }
  have hpt : ∀ P : Mori.PrimeDivisor C,
      F (Finsupp.single P 1) = sC.residueDegree P.genericPoint := by
    intro P
    have hc := hcar (Finsupp.single P 1 : Divisor C)
    haveI := hc.isInvertibleModule_divisorialSheaf
    change Divisor.degreeOn K sC (𝟙 C) hdim _ (hcar _) = _
    rw [hid _ hc]
    exact invertibleCurveDegree_divisorialSheaf_single sC hdim hUFD P
  rw [← hid D (hcar D)]
  change F D = _
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [← Finsupp.smul_single_one, map_zsmul, hpt, smul_eq_mul]

/-- A preimmersion is bijective on residue fields. -/
private theorem bijective_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨Y.residue (f x) c, by
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]⟩

/-- A morphism inducing an isomorphism on the stalk at `q` preserves the coheight of `q`. -/
private theorem coheight_eq_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (q : X)
    [IsIso (f.stalkMap q)] : Order.coheight (f q) = Order.coheight q := by
  have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap q)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- At a point of the fibre with iso stalk map, the residue degree of the projection to
`Spec κ(η)` is the residue degree of `g` at its image. -/
private theorem residueDegree_fiberToSpecResidueField {V W : Scheme.{u}} (g : V ⟶ W) (η : W)
    (q : g.fiber η) (hq : IsIso ((g.fiberι η).stalkMap q)) :
    (g.fiberToSpecResidueField η).residueDegree q = g.residueDegree (g.fiberι η q) := by
  have h1 := Stacks.Chow.residueDegree_comp (g.fiberι η) g q
  have h2 : (g.fiberι η).residueDegree q = 1 :=
    MMP.Flips.residueFieldDegree_eq_one_of_isIso_stalkMap _ q hq
  have h3 : (g.fiberι η ≫ g).residueDegree q =
      (g.fiberToSpecResidueField η).residueDegree q := by
    rw [show g.fiberι η ≫ g = g.fiberToSpecResidueField η ≫ W.fromSpecResidueField η from
      Scheme.Hom.fiber_fac g η]
    exact Stacks.Chow.residueDegree_comp_of_bijective_residueFieldMap _ _ q
      (bijective_residueFieldMap_of_isPreimmersion _ _)
  rw [← h3, h1, h2, mul_one]

/-- The degree on the generic fibre: for a Cartier divisor `E` on `V`, the difference
`χ(V_η, 𝒪_V(E)|_{V_η}) - χ(V_η, 𝒪_{V_η})` is `∑ eᵢ [κ(ξᵢ) : κ(η)]`, the sum over the prime
divisors of `E` dominating `W`. -/
private theorem fibreEulerCharacteristic_sub_unit_genericPoint_eq_sum
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1)
    (E : Mori.Divisor V) (hE : E.IsCartier) [CompactSpace V]
    [Stacks.Ample.IsInvertibleModule V E.divisorialSheaf] :
    fibreEulerCharacteristic g E.divisorialSheaf (genericPoint W) -
        fibreEulerCharacteristic g (SheafOfModules.unit V.ringCatSheaf) (genericPoint W) =
      ∑ P ∈ E.support, E P * (genericFiberPointDegree g P : ℤ) := by
  classical
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hs : Function.Surjective g := g.surjective
  have hη := genericPoint_map_of_surjective g hs
  have hdim1 : topologicalKrullDim (g.fiber (g (genericPoint V))) = 1 := by
    rw [hη]; exact topologicalKrullDim_genericFiber_eq_one sV sW g hg hs hdim
  have hgfpd : ∀ R : Mori.PrimeDivisor V, genericFiberPointDegree g R =
      if g R.genericPoint = genericPoint W then g.residueDegree R.genericPoint else 0 := by
    intro R
    unfold genericFiberPointDegree
    split_ifs <;> rfl
  -- move to the point `η = g(ξ_V)`
  simp only [hgfpd, ← hη]
  set η := g (genericPoint V)
  set ι := g.fiberι η
  set π := g.fiberToSpecResidueField η
  haveI : IsIntegral (g.fiber η) := isIntegral_fiber_genericPoint g
  haveI : IsNormal (g.fiber η) := isNormal_fiber_genericPoint g
  haveI hπ : IsProper π :=
    inferInstanceAs (IsProper (Limits.pullback.snd g (W.fromSpecResidueField η)))
  haveI : IsLocallyNoetherian (g.fiber η) := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : CompactSpace (g.fiber η) := QuasiCompact.compactSpace_of_compactSpace π
  have hX : topologicalKrullDim (g.fiber η) ≤ 1 := hdim1.le
  have hiso : ∀ p, IsIso (ι.stalkMap p) := fun p => isIso_stalkMap_fiberι_genericPoint g p
  have hUFD : ∀ p : g.fiber η, UniqueFactorizationMonoid ((g.fiber η).presheaf.stalk p) := by
    intro p
    have hp : g (ι p) = genericPoint W := by
      rw [← hη]
      exact (Set.ext_iff.mp (g.range_fiberι η) (ι p)).mp ⟨p, rfl⟩
    haveI := isRegularLocalRing_stalk_of_mem_genericFiber sV sW g hg hdim hp
    haveI := IsRegularLocalRing.uniqueFactorizationMonoid (V.presheaf.stalk (ι p))
    exact MulEquiv.uniqueFactorizationMonoid
      (asIso (ι.stalkMap p)).commRingCatIsoToRingEquiv.toMulEquiv inferInstance
  -- the pull-back of `E` to the generic fibre
  have hgen : ι (genericPoint (g.fiber η)) = genericPoint V := by
    have h1 : g.asFiber (genericPoint V) = genericPoint (g.fiber η) :=
      (isGenericPoint_asFiber_genericPoint g).eq (genericPoint_spec _)
    rw [← h1]
    exact Scheme.Hom.fiberι_asFiber g _
  have hB : ∀ Z : irreducibleComponents (g.fiber η),
      ι (Mori.componentGenericPoint (g.fiber η) Z) ∉ E.supp := by
    intro Z
    have hZ : (Z : Set (g.fiber η)) = Set.univ := Set.mem_singleton_iff.mp
      (irreducibleComponents_eq_singleton (X := g.fiber η) ▸ Z.2 :
        (Z : Set (g.fiber η)) ∈ ({Set.univ} : Set (Set (g.fiber η))))
    have : Mori.componentGenericPoint (g.fiber η) Z = genericPoint (g.fiber η) :=
      (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)).eq
        (by rw [hZ]; exact genericPoint_spec _)
    rw [this, hgen]
    exact MMP.Fourfold.genericPoint_notMem_supp E
  set E' := E.pullback hE hB
  have hE' : E.IsPullback ι hB E' := Mori.Divisor.isPullback_pullback hE hB
  have hE'c : E'.IsCartier := hE'.isCartier hE
  haveI := hE'c.isInvertibleModule_divisorialSheaf
  have hLHS : fibreEulerCharacteristic g E.divisorialSheaf η -
      fibreEulerCharacteristic g (SheafOfModules.unit V.ringCatSheaf) η =
      invertibleCurveDegree (W.residueField η) π hX E'.divisorialSheaf := by
    rw [@invertibleCurveDegree_eq_of_iso (W.residueField η) _ _ π hπ hX _ _ _ _
      (hE'.divisorialSheafIso (hBc := hE)),
      show fibreEulerCharacteristic g (SheafOfModules.unit V.ringCatSheaf) η =
        eulerSum (W.residueField η) π (SheafOfModules.unit (g.fiber η).ringCatSheaf) from
      eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso ι)]
    rfl
  rw [hLHS, @invertibleCurveDegree_divisorialSheaf_eq_sum (W.residueField η) _ _ π hπ _ _ _ hX
    hUFD E' _]
  -- the prime divisors of `V_η` are the horizontal prime divisors of `V`
  have hco : ∀ q : g.fiber η, Order.coheight (ι q) = Order.coheight q := fun q =>
    haveI := hiso q
    coheight_eq_of_isIso_stalkMap ι q
  let P : Mori.PrimeDivisor (g.fiber η) → Mori.PrimeDivisor V := fun Q =>
    AlgebraicGeometry.PrimeDivisor.ofCoheightOne (ι Q.genericPoint)
      (by rw [hco]; exact Q.coheight_genericPoint)
  have hPgen : ∀ Q, (P Q).genericPoint = ι Q.genericPoint := fun Q =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hcoef : ∀ Q, E' Q = E (P Q) := fun Q => by
    haveI := hiso Q.genericPoint
    exact MMP.Positivity.coeff_eq_of_isPullback Q (P Q) (hPgen Q).symm hE hE'
  have hrange : ∀ x : V, g x = η ↔ x ∈ Set.range ι := fun x => by
    rw [Scheme.Hom.range_fiberι]; rfl
  have hdeg : ∀ q : g.fiber η, π.residueDegree q =
      if g (ι q) = η then g.residueDegree (ι q) else 0 := by
    intro q
    rw [if_pos ((hrange _).mpr ⟨q, rfl⟩)]
    exact residueDegree_fiberToSpecResidueField g η q (hiso q)
  refine Finset.sum_bij_ne_zero (fun Q _ _ => P Q) ?_ ?_ ?_ ?_
  · intro Q hQ _
    rw [Finsupp.mem_support_iff, ← hcoef]
    exact Finsupp.mem_support_iff.mp hQ
  · intro Q₁ _ _ Q₂ _ _ h
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (ι.isEmbedding.injective (by rw [← hPgen, ← hPgen, h]))
  · intro R hR hne
    have hη' : g R.genericPoint = η := by
      by_contra h
      exact hne (by rw [if_neg h]; simp)
    obtain ⟨q, hq⟩ := (hrange _).mp hη'
    have hq1 : Order.coheight q = 1 := by rw [← hco, hq]; exact R.coheight_genericPoint
    let Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne q hq1
    have hQgen : Q.genericPoint = q := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hPQ : P Q = R := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((hPgen Q).trans ((congrArg ι (show Mori.PrimeDivisor.genericPoint Q = q from hQgen)).trans
        hq))
    refine ⟨Q, ?_, ?_, hPQ⟩
    · rw [Finsupp.mem_support_iff, hcoef, hPQ]
      exact Finsupp.mem_support_iff.mp hR
    · rw [hcoef, hdeg, ← hPgen, hPQ]
      exact hne
  · intro Q _ _
    rw [hcoef, hdeg, ← hPgen]

/-- In a quasi-sober `T₀` space, the generic points of the irreducible components are exactly the
points without proper generalization. -/
private theorem mem_genericPoints_iff_forall_specializes {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] {x : α} :
    x ∈ genericPoints α ↔ ∀ y, y ⤳ x → y = x := by
  constructor
  · intro hx y hyx
    have hsub : closure {x} ⊆ closure {y} := specializes_iff_closure_subset.mp hyx
    have heq : closure {y} = closure {x} :=
      (hx.2 isIrreducible_singleton.closure hsub).antisymm hsub
    exact (inseparable_iff_closure_eq.mpr heq).eq
  · intro h
    obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure {x}) isIrreducible_singleton.closure
    have hgen := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
    have hxZ : x ∈ Z := hsub (subset_closure rfl)
    have hzx : hZ.1.genericPoint ⤳ x := by
      rwa [specializes_iff_mem_closure, hgen.def]
    have := h _ hzx
    change closure {x} ∈ irreducibleComponents α
    rwa [← this, hgen.def]

/-- For an embedding `φ` with image `f ⁻¹' {w}`, a point is a generic point of an irreducible
component iff its image has no proper generalization in `f ⁻¹' {w}`. -/
private theorem mem_genericPoints_iff_of_isEmbedding {α β γ : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] [TopologicalSpace β] {φ : α → β} (hφ : Topology.IsEmbedding φ)
    (f : β → γ) {w : γ} (hrange : Set.range φ = f ⁻¹' {w}) (x : α) :
    x ∈ genericPoints α ↔ ∀ y, f y = w → y ⤳ φ x → y = φ x := by
  rw [mem_genericPoints_iff_forall_specializes]
  refine ⟨fun h y hy hyx => ?_, fun h y hyx =>
    hφ.injective (h _ (hrange.subset ⟨y, rfl⟩) (hyx.map hφ.continuous))⟩
  obtain ⟨y, rfl⟩ : y ∈ Set.range φ := hrange ▸ hy
  rw [h y (hφ.isInducing.specializes_iff.mp hyx)]

/-- The image of a proper curve under an injective morphism of `k`-schemes, to a separated
`k`-scheme locally of finite type, is a proper curve. -/
private theorem isProperCurve_comp_of_injective {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] (φ : X ⟶ Y)
    (hφ : Function.Injective φ) (C : Mori.ProperCurve (φ ≫ sY)) :
    Mori.IsProperCurve sY (φ C.point) := by
  have hφsY : (C.ι ≫ φ) ≫ sY = C.ι ≫ (φ ≫ sY) := Category.assoc _ _ _
  haveI : AlgebraicGeometry.IsCurve k ((C.ι ≫ φ) ≫ sY) := hφsY ▸ C.isCurve
  haveI : IsProper ((C.ι ≫ φ) ≫ sY) := by rw [hφsY]; infer_instance
  have hinj : Function.Injective (C.ι ≫ φ) := fun a b h =>
    C.ι.isEmbedding.injective (hφ (by rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h))
  have hnc : ¬ ∃ z, Set.range (C.ι ≫ φ) = {z} := by
    rintro ⟨z, hz⟩
    have : Subsingleton C.scheme := ⟨fun a b => hinj (by
      have ha : (C.ι ≫ φ) a ∈ ({z} : Set Y) := hz ▸ ⟨a, rfl⟩
      have hb : (C.ι ≫ φ) b ∈ ({z} : Set Y) := hz ▸ ⟨b, rfl⟩
      exact ha.trans hb.symm)⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  have hcurve := MMP.Mori.isCurve_imageι_comp sY (C.ι ≫ φ) hnc
  have hker := C.ker_comp φ
  refine ⟨?_, ?_⟩
  · have h1 := hcurve.topologicalKrullDim_eq_one
    change topologicalKrullDim (C.ι ≫ φ).ker.subscheme = 1 at h1
    rwa [hker] at h1
  · have h1 : IsProper ((C.ι ≫ φ).imageι ≫ sY) := isProper_imageι_comp _ sY
    change IsProper ((C.ι ≫ φ).ker.subschemeι ≫ sY) at h1
    rwa [hker] at h1

/-- Along a closed immersion `φ : X ⟶ Y` of `k`-schemes, the degree of `φ^* L` on a
one-dimensional component of `X` is the degree of `L` on its image, a proper curve of `Y`. -/
private theorem componentDegree_pullback_eq_degree {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] (φ : X ⟶ Y)
    [IsClosedImmersion φ] [IsProper (φ ≫ sY)] (hX : topologicalKrullDim X ≤ 1)
    (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L] (ξ : genericPointsOne X) :
    haveI : Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback φ).obj L) :=
      inferInstance
    haveI := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X
      ((Scheme.Modules.pullback φ).obj L)
    componentDegree k (φ ≫ sY) hX ((Scheme.Modules.pullback φ).obj L) 1 ξ =
      Mori.ProperCurve.degree k
        (⟨φ ξ.1, isProperCurve_comp_of_injective φ φ.isEmbedding.injective
          ⟨ξ.1, Mori.isProperCurve_of_isProper (φ ≫ sY)
            ((MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq ξ.1).trans
              (mem_genericPointsOne_iff.mp ξ.2).2)⟩⟩ : Mori.ProperCurve sY) L := by
  set C : Mori.ProperCurve (φ ≫ sY) := ⟨ξ.1, Mori.isProperCurve_of_isProper (φ ≫ sY)
    ((MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq ξ.1).trans
      (mem_genericPointsOne_iff.mp ξ.2).2)⟩
  have hd : componentDegree k (φ ≫ sY) hX ((Scheme.Modules.pullback φ).obj L) 1 ξ =
      C.degree k ((Scheme.Modules.pullback φ).obj L) := by
    unfold componentDegree Mori.ProperCurve.degree Mori.degreeOn
    exact (AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree k _ _ _).symm
  rw [hd, ← MMP.Chow.degree_cyclePushforwardOfPoint_eq φ rfl C L]
  have h1 : Mori.residueFieldDegree φ C.point = 1 :=
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ C.point
  simp only [Mori.cyclePushforwardOfPoint, dif_pos (isProperCurve_comp_of_injective φ
    φ.isEmbedding.injective C), Mori.OneCycle.degree, Finsupp.linearCombination_single,
    smul_eq_mul, h1, Nat.cast_one, one_mul]
  rfl

/-- A scheme proper and smooth over a perfect field is reduced along its components: every
one-dimensional component has multiplicity one. -/
private theorem componentMultiplicity_eq_one_of_smooth {K : Type u} [Field K] [PerfectField K]
    {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [Smooth π] [IsProper π] (ξ : genericPointsOne X) :
    componentMultiplicity X ξ = 1 := by
  have : IsNoetherian X := isNoetherian_of_isProper_over_field K π
  let R := X.presheaf.stalk ξ.1
  have hreg : IsRegularLocalRing R :=
    (MMP.mem_smoothLocus_iff_isRegularLocalRing_of_perfectField π).2.1 inferInstance ξ.1
  have hdim : ringKrullDim R = 0 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    have hcoheight : Order.coheight ξ.1 = 0 :=
      Order.coheight_eq_zero.mpr
        (isMax_of_mem_genericPoints ξ.1 (mem_genericPointsOne_iff.mp ξ.2).1)
    simpa only [WithBot.coe_zero] using congrArg (fun d : ℕ∞ => (d : WithBot ℕ∞)) hcoheight
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  have hfield : IsField R := Ring.KrullDimLE.isField_of_isDomain
  letI := hfield.toField
  have : IsSimpleModule R R := inferInstance
  unfold componentMultiplicity
  rw [Module.length_eq_one_iff.mpr this]
  rfl

/-- The degree on a smooth closed fibre: over a closed point `w` with smooth fibre, the
irreducible components of `g⁻¹(w)` are proper curves `C`, and
`χ(V_w, 𝒪_V(E)|_{V_w}) - χ(V_w, 𝒪_{V_w}) = ∑_C deg_C 𝒪_V(E)`. -/
private theorem exists_finset_properCurve_fibreEulerCharacteristic_sub_unit_eq_sum
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (w : W) (hsm : Smooth (g.fiberToSpecResidueField w))
    (hcomp : ∀ Z ∈ irreducibleComponents (g.fiber w), topologicalKrullDim Z = 1)
    (hcl : IsClosed ({w} : Set W))
    (E : Mori.Divisor V) (hE : E.IsCartier) [CompactSpace V]
    [Stacks.Ample.IsInvertibleModule V E.divisorialSheaf] :
    ∃ S : Finset (Mori.ProperCurve sV),
      Mori.ProperCurve.point '' (S : Set (Mori.ProperCurve sV)) =
        {x : V | g x = w ∧ ∀ y : V, g y = w → y ⤳ x → y = x} ∧
      fibreEulerCharacteristic g E.divisorialSheaf w -
          fibreEulerCharacteristic g (SheafOfModules.unit V.ringCatSheaf) w =
        ∑ C ∈ S, E.degreeOn k sV C.ι C.dim_le hE := by
  classical
  have : IsClosedImmersion (W.fromSpecResidueField w) :=
    isClosed_singleton_iff_isClosedImmersion.mp hcl
  have : IsClosedImmersion (g.fiberι w) :=
    inferInstanceAs (IsClosedImmersion (Limits.pullback.fst _ _))
  set θ := (residueFieldIsoBase sW w hcl).inv
  have hθ : Function.Bijective θ := ConcreteCategory.bijective_of_isIso θ
  have hθe := SpecMap_residueFieldIsoBase_inv sW w hcl
  have hsX : g.fiberι w ≫ sV = g.fiberToSpecResidueField w ≫ Spec.map θ := by
    rw [hθe, ← hg, ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc]
  have hπ : IsProper (g.fiberToSpecResidueField w) :=
    inferInstanceAs (IsProper (Limits.pullback.snd g (W.fromSpecResidueField w)))
  have : IsProper (g.fiberToSpecResidueField w :
      g.fiber w ⟶ Spec (.of (W.residueField w))) := hπ
  have : IsProper (g.fiberι w ≫ sV) := by rw [hsX]; infer_instance
  have hX : topologicalKrullDim (g.fiber w) ≤ 1 :=
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun Z hZ =>
      (hcomp Z hZ).le
  letI := θ.hom.toAlgebra
  have : CharZero (W.residueField w) := charZero_of_injective_algebraMap (R := k) hθ.1
  set φ := g.fiberι w
  set F := E.divisorialSheaf
  -- the fibre degree as a degree over `k`
  have hLHS : fibreEulerCharacteristic g F w -
      fibreEulerCharacteristic g (SheafOfModules.unit V.ringCatSheaf) w =
      invertibleCurveDegree k (φ ≫ sV) hX ((Scheme.Modules.pullback φ).obj F) := by
    have hk := @MMP.Threefold.Resolution.invertibleCurveDegree_comp_specMap
        (W.residueField w) _ k _ (g.fiber w) (g.fiberToSpecResidueField w) hπ θ
        (by rw [← hsX]; infer_instance) hθ hX ((Scheme.Modules.pullback φ).obj F) _
    rw [MMP.Mori.invertibleCurveDegree_congr_structure hsX, hk,
      show fibreEulerCharacteristic g (SheafOfModules.unit V.ringCatSheaf) w =
        eulerSum (W.residueField w) (g.fiberToSpecResidueField w)
          (SheafOfModules.unit (g.fiber w).ringCatSheaf) from
      eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso φ)]
    rfl
  haveI : Stacks.Ample.IsInvertibleModule (g.fiber w) ((Scheme.Modules.pullback φ).obj F) :=
    inferInstance
  haveI := Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme (g.fiber w)
    ((Scheme.Modules.pullback φ).obj F)
  have hsum := curveDegree_eq_finsum_componentDegree_of_isProper k (φ ≫ sV) hX
    ((Scheme.Modules.pullback φ).obj F) 1
  rw [← invertibleCurveDegree_eq_curveDegree] at hsum
  have hmult := @componentMultiplicity_eq_one_of_smooth (W.residueField w) _ inferInstance
    (g.fiber w) (g.fiberToSpecResidueField w) hsm hπ
  let push : genericPointsOne (g.fiber w) → Mori.ProperCurve sV := fun ξ =>
    ⟨φ ξ.1, isProperCurve_comp_of_injective φ φ.isEmbedding.injective
      ⟨ξ.1, Mori.isProperCurve_of_isProper (φ ≫ sV)
        ((MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq ξ.1).trans
          (mem_genericPointsOne_iff.mp ξ.2).2)⟩⟩
  have hdeg : ∀ ξ, componentDegree k (φ ≫ sV) hX ((Scheme.Modules.pullback φ).obj F) 1 ξ =
      (push ξ).degree k F := fun ξ => componentDegree_pullback_eq_degree φ hX F ξ
  have hinj : Function.Injective push := fun a b h =>
    Subtype.ext (φ.isEmbedding.injective (congrArg Mori.ProperCurve.point h))
  haveI : Fintype (genericPointsOne (g.fiber w)) :=
    (finite_genericPointsOne_of_isProper k (φ ≫ sV)).fintype
  -- a point of the fibre is a generic point of a component iff it has no proper generalization
  -- in `g⁻¹(w)`
  have hrange : Set.range φ = g ⁻¹' {w} := Scheme.Hom.range_fiberι g w
  have htrans : ∀ x' : g.fiber w, x' ∈ genericPoints (g.fiber w) ↔
      ∀ y : V, g y = w → y ⤳ φ x' → y = φ x' :=
    mem_genericPoints_iff_of_isEmbedding φ.isEmbedding g hrange
  refine ⟨Finset.univ.image push, ?_, ?_⟩
  · ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨ξ, rfl⟩, rfl⟩
      refine ⟨hrange.subset ⟨ξ.1, rfl⟩, (htrans ξ.1).mp (mem_genericPointsOne_iff.mp ξ.2).1⟩
    · rintro ⟨hgx, hmin⟩
      obtain ⟨x', rfl⟩ : x ∈ Set.range φ := hrange ▸ hgx
      have hx' := (htrans x').mpr hmin
      exact ⟨push ⟨x', mem_genericPointsOne_iff.mpr ⟨hx', hcomp _ hx'⟩⟩, ⟨_, rfl⟩, rfl⟩
  · rw [hLHS, hsum, finsum_eq_sum_of_fintype, Finset.sum_image (fun a _ b _ h => hinj h)]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [hmult ξ, hdeg ξ, Nat.cast_one, one_mul]
    rfl

/-- Over an open on which `g` is smooth, the generic degree is conserved at every closed
point. -/
private theorem genericFiberDegree_eq_sum_of_smooth_restrict
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1)
    (L : Mori.QDivisor V) (hL : L.IsQCartier)
    (U : W.Opens) (hU : (U : Set W).Nonempty) (hsm : Smooth (g ∣_ U))
    (w : W) (hw : w ∈ U) (hsmw : Smooth (g.fiberToSpecResidueField w))
    (hcomp : ∀ Z ∈ irreducibleComponents (g.fiber w), topologicalKrullDim Z = 1)
    (hcl : IsClosed ({w} : Set W)) :
    ∃ S : Finset (Mori.ProperCurve sV),
      Mori.ProperCurve.point '' (S : Set (Mori.ProperCurve sV)) =
        {x : V | g x = w ∧ ∀ y : V, g y = w → y ⤳ x → y = x} ∧
      genericFiberDegree g L = ∑ C ∈ S, L.intersectionNumber k sV C.ι C.dim_le hL := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have hEc := Mori.QDivisor.isCartierDivisor_cartierIndex_smul hL
  set m := L.cartierIndex hL
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Mori.QDivisor.cartierIndex_pos hL).ne'
  set E := hEc.toDivisor
  have hE : E.IsCartier := hEc.isCartier_toDivisor
  have hEL : Mori.Divisor.toQDivisor E = ((m : ℕ) : ℤ) • L := hEc.toQDivisor_toDivisor
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨S, hS, hdegw⟩ :=
    exists_finset_properCurve_fibreEulerCharacteristic_sub_unit_eq_sum sV sW g hg w hsmw hcomp hcl
      E hE
  refine ⟨S, hS, ?_⟩
  have hUpre : _root_.IsPreconnected (U : Set W) :=
    ((IrreducibleSpace.isIrreducible_univ W).isPreirreducible.open_subset U.isOpen
      (Set.subset_univ _)).isPreconnected
  have hη : genericPoint W ∈ U := by
    obtain ⟨u, hu⟩ := hU
    exact (genericPoint_spec W).mem_open_set_iff U.isOpen |>.mpr ⟨u, trivial, hu⟩
  have h1 := fibreEulerCharacteristic_eq_of_smooth_restrict g U hUpre E.divisorialSheaf hη hw
  have h2 := fibreEulerCharacteristic_eq_of_smooth_restrict g U hUpre
    (SheafOfModules.unit V.ringCatSheaf) hη hw
  have hgen := fibreEulerCharacteristic_sub_unit_genericPoint_eq_sum sV sW g hg hdim E hE
  rw [h1, h2, hdegw] at hgen
  have hcoef : ∀ P, (E P : ℚ) = m * L P := fun P => by
    have := congrArg (fun D : Mori.QDivisor V => D P) hEL
    simp only [Mori.Divisor.toQDivisor, Mori.DivisorWithCoeffs.mapCoeffsAddMonoidHom] at this
    simpa [Mori.DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_apply] using this
  have hsupp : E.support = L.support := by
    ext P
    simp only [Finsupp.mem_support_iff, ne_eq]
    rw [← Int.cast_eq_zero (α := ℚ), hcoef P, mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨hm0, h⟩⟩
  simp only [Mori.QDivisor.intersectionNumber, ← Finset.sum_div]
  rw [eq_div_iff hm0]
  have hgen' := congrArg (fun z : ℤ => (z : ℚ)) hgen
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at hgen'
  change _ = ∑ C ∈ S, ((E.degreeOn k sV C.ι C.dim_le hE : ℤ) : ℚ)
  rw [hgen', genericFiberDegree, hsupp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [hcoef P, Mori.DivisorWithCoeffs.coeff_apply]
  ring

/-- **Conservation of the generic degree.** Let `g : V ⟶ W` be a proper surjective morphism of
varieties over an algebraically closed field `k` of characteristic zero, with `V` normal and
`dim V = dim W + 1`, and `L` a `ℚ`-Cartier `ℚ`-divisor on `V`. There is a dense open `W⁰ ⊆ W`
over which every fibre of `g` is smooth, and such that for each closed point `w ∈ W⁰` the
irreducible components of `g⁻¹(w)` are proper curves `C ∈ S` (recorded by their generic points)
with `deg_{k(W)} L|_{V_η} = ∑_{C ∈ S} (L · C)`. -/
@[mmp "lem_mmp_fa15_generic_fibre_degree"]
theorem exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k))
    [IsIntegral V] [IsNormal V] [IsLocallyNoetherian V]
    [IsSeparated sV] [LocallyOfFiniteType sV] [QuasiCompact sV]
    [IsIntegral W] [IsSeparated sW] [LocallyOfFiniteType sW] [QuasiCompact sW]
    (g : V ⟶ W) (hg : g ≫ sW = sV) [IsProper g] [Surjective g]
    (hdim : topologicalKrullDim V = topologicalKrullDim W + 1)
    (L : Mori.QDivisor V) (hL : L.IsQCartier) :
    ∃ U : W.Opens, Dense (U : Set W) ∧ ∀ w ∈ U,
      Smooth (g.fiberToSpecResidueField w) ∧
      (IsClosed ({w} : Set W) → ∃ S : Finset (Mori.ProperCurve sV),
        Mori.ProperCurve.point '' (S : Set (Mori.ProperCurve sV)) =
          {x : V | g x = w ∧ ∀ y : V, g y = w → y ⤳ x → y = x} ∧
        genericFiberDegree g L = ∑ C ∈ S, L.intersectionNumber k sV C.ι C.dim_le hL) := by
  obtain ⟨U, hUd, hsm, hfib⟩ := exists_dense_open_smooth_restrict sV sW g hg hdim
  exact ⟨U, hUd, fun w hw => ⟨(hfib w hw).1, fun hcl =>
    genericFiberDegree_eq_sum_of_smooth_restrict sV sW g hg hdim L hL U hUd.nonempty hsm w hw
      (hfib w hw).1 (hfib w hw).2 hcl⟩⟩

end GenericFibreDegree

section TriviallyConnected

open MMP.Mori

section Member

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- At a closed point `x` of a scheme locally of finite type over an algebraically closed field
`k`, every element of `𝒪_{X,x}` is congruent to a constant modulo the maximal ideal:
`κ(x) = k`. -/
private theorem exists_sub_germ_mem_maximalIdeal [IsAlgClosed k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {x : X} (hx : IsClosed {x}) (a : X.presheaf.stalk x) :
    ∃ c : k, a - (X.presheaf.germ ⊤ x trivial).hom (scalarsToGlobalSections k sX c) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  have h : (X.residue x).hom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
      (scalarsToGlobalSections k sX)) = (residueFieldIsoBase sX x hx).inv.hom := by
    have : Spec.map (CommRingCat.ofHom ((X.residue x).hom.comp
        ((X.presheaf.germ ⊤ x trivial).hom.comp (scalarsToGlobalSections k sX)))) =
        X.fromSpecResidueField x ≫ sX := by
      simp only [scalarsToGlobalSections, Scheme.fromSpecResidueField, CommRingCat.ofHom_comp,
        CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
      congr 1
      rw [← Scheme.fromSpecStalk_toSpecΓ_assoc]
      congr 1
      rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [← SpecMap_residueFieldIsoBase_inv sX x hx] at this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (residueFieldIsoBase sX x hx).inv).2
    ((X.residue x).hom a)
  refine ⟨c, ?_⟩
  have hc' : ((X.residue x).hom.comp ((X.presheaf.germ ⊤ x trivial).hom.comp
      (scalarsToGlobalSections k sX))) c = (X.residue x).hom a := by rwa [h]
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact hc'.symm

variable [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral X]

/-- The divisor of zeros of a nonzero section `σ` of `𝒪_X(M)` has the local equation `σ ψ` on
an open `W` on which `ψ` is a local equation of `M`. -/
private theorem isLocalEquation_zeroDivisor {M : Divisor X} {W : X.Opens}
    {ψ : (RationalFunctions X)ˣ} (hψ : M.IsLocalEquation W ψ) (σ : M.divisorialSubmodule ⊤)
    (hσ : σ ≠ 0) :
    (M.zeroDivisor σ hσ).IsLocalEquation W
      ((Divisor.isUnit_sectionToRationalFunctions hσ).unit * ψ) := by
  rw [Divisor.zeroDivisor_eq]
  exact (Divisor.isLocalEquation_principalDivisor _ W).add hψ

/-- The local value `σ ψ` at `x` of a nonzero section `σ` of `𝒪_X(M)`, for a local equation
`ψ` of `M` near `x`, is regular at `x`. -/
private theorem exists_stalk_eq_mul {M : Divisor X} {W : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : M.IsLocalEquation W ψ) {x : X} (hxW : x ∈ W) {Z : irreducibleComponents X}
    (hxZ : x ∈ Z.1) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) :
    ∃ a : X.presheaf.stalk x, (stalkToRationalFunctions X hxZ).hom a =
      Divisor.sectionToRationalFunctions σ Z * (ψ : RationalFunctions X) Z := by
  obtain ⟨a, ha⟩ := exists_stalk_eq_of_forall_zero_le_ord hxZ _ fun E hE => by
    rw [← isLocalEquation_zeroDivisor hψ σ hσ E ⟨x, hE, hxW⟩]
    exact Divisor.zeroDivisor_nonneg M σ hσ E
  refine ⟨a, ha.trans ?_⟩
  simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec]

/-- If the local value `σ ψ` of a nonzero section `σ` vanishes at `x`, then `x` lies on the
divisor of zeros of `σ`. -/
private theorem mem_supp_zeroDivisor {M : Divisor X} {W : X.Opens} {ψ : (RationalFunctions X)ˣ}
    (hψ : M.IsLocalEquation W ψ) {x : X} (hxW : x ∈ W) {Z : irreducibleComponents X}
    (hxZ : x ∈ Z.1) (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (a : X.presheaf.stalk x)
    (ha : (stalkToRationalFunctions X hxZ).hom a =
      Divisor.sectionToRationalFunctions σ Z * (ψ : RationalFunctions X) Z)
    (hm : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    x ∈ (M.zeroDivisor σ hσ).supp := by
  by_contra hxs
  obtain ⟨b, hb⟩ := (isLocalEquation_zeroDivisor hψ σ hσ).exists_unit_stalk hxW hxs hxZ
  have hab : (b : X.presheaf.stalk x) = a := stalkToRationalFunctions_injective hxZ (by
    rw [hb, ha]
    simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec])
  exact (IsLocalRing.mem_maximalIdeal a).mp hm (hab ▸ b.isUnit)

/-- **A member of `|M|` through a closed point** (FA 15.9, via (15.4.2)). If `M` is Cartier with
`h⁰(X, 𝒪_X(M)) ≥ 2` on a normal integral scheme locally of finite type over an algebraically
closed field, then every closed point `x` lies on the divisor of zeros of a nonzero section of
`𝒪_X(M)`: the sections vanishing at `x` form a hyperplane of `H⁰(X, 𝒪_X(M))`. -/
private theorem exists_mem_supp_zeroDivisor [IsAlgClosed k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {M : Divisor X} (hM : M.IsCartier) (h2 : 2 ≤ M.h0 k sX) {x : X}
    (hx : IsClosed {x}) :
    ∃ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0), x ∈ (M.zeroDivisor σ hσ).supp := by
  classical
  obtain ⟨W, hxW, ψ, hψ⟩ := hM x
  set Z := pointComponent x
  have hxZ : x ∈ Z.1 := mem_pointComponent x
  letI : Module k (M.divisorialSubmodule ⊤) := Module.compHom _ (scalarsToGlobalSections k sX)
  have h2' : 2 ≤ Module.finrank k (M.divisorialSubmodule ⊤) := h2
  have : Module.Finite k (M.divisorialSubmodule ⊤) := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasis k (M.divisorialSubmodule ⊤)
  let i₀ : Fin (Module.finrank k (M.divisorialSubmodule ⊤)) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank k (M.divisorialSubmodule ⊤)) := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hσ₁ : b i₀ ≠ 0 := b.ne_zero i₀
  have hσ₂ : b i₁ ≠ 0 := b.ne_zero i₁
  obtain ⟨a₁, ha₁⟩ := exists_stalk_eq_mul hψ hxW hxZ (b i₀) hσ₁
  by_cases hm₁ : a₁ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  · exact ⟨b i₀, hσ₁, mem_supp_zeroDivisor hψ hxW hxZ (b i₀) hσ₁ a₁ ha₁ hm₁⟩
  obtain ⟨a₂, ha₂⟩ := exists_stalk_eq_mul hψ hxW hxZ (b i₁) hσ₂
  have hu : IsUnit a₁ := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm₁
  obtain ⟨c, hc⟩ := exists_sub_germ_mem_maximalIdeal sX hx (a₂ * ↑hu.unit⁻¹)
  set g := (X.presheaf.germ ⊤ x trivial).hom (scalarsToGlobalSections k sX c) with hg
  have hσ : b i₁ - c • b i₀ ≠ 0 := by
    intro h0
    have := congrArg (fun v => b.repr v i₁) h0
    simp [b.repr_self, Finsupp.single_apply, hne] at this
  refine ⟨_, hσ, mem_supp_zeroDivisor hψ hxW hxZ _ hσ (a₂ - g * a₁) ?_ ?_⟩
  · have hs : (stalkToRationalFunctions X hxZ).hom g =
        (X.presheaf.germ ⊤ (componentGenericPoint X Z) trivial).hom
          (scalarsToGlobalSections k sX c) := by
      rw [hg, stalkToRationalFunctions]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _
    rw [map_sub, map_mul, ha₁, ha₂, hs]
    change _ = ((b i₁).1 ⟨Z, trivial⟩ -
      (scalarsToGlobalSections k sX c • (b i₀).1) ⟨Z, trivial⟩) * _
    rw [rationalFunctions_smul_apply]
    simp only [Divisor.sectionToRationalFunctions_apply]
    ring
  · have : a₂ - g * a₁ = (a₂ * ↑hu.unit⁻¹ - g) * a₁ := by
      rw [sub_mul, mul_assoc, Units.inv_mul_of_eq hu.unit_spec, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hc

end Member

section Restrict

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (U : X.Opens)

/-- At the generic point of a prime divisor `E`, the stalk of the ideal of `E` is the maximal
ideal of the local ring. -/
private theorem stalkIdeal_idealSheaf_eq_maximalIdeal (E : Mori.PrimeDivisor X) {y : X}
    (hy : y = E.genericPoint) :
    E.idealSheaf.stalkIdeal y = IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  subst hy
  rw [← MMP.Mori.vanishingIdeal_closure_genericPoint_eq_idealSheaf]
  have := Stacks.Chow.stalkIdeal_vanishingIdeal_closure_fromSpecStalk E.genericPoint
    (IsLocalRing.closedPoint _)
  rw [Scheme.fromSpecStalk_closedPoint] at this
  exact this

open Classical in
/-- Along an open immersion, the local intersection length of a prime divisor `E` of `X` along a
prime divisor `P` of `U` is `1` if `E` is the closure of `P` and `0` otherwise. -/
theorem intersectionLength_ι (E : Mori.PrimeDivisor X) (P : Mori.PrimeDivisor U) :
    E.intersectionLength U.ι P =
      if E = OpenWeilRestriction.primeDivisorMap U.ι P then 1 else 0 := by
  split_ifs with hE
  · have hy : U.ι P.genericPoint = E.genericPoint := by
      rw [hE]; exact (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm
    have hiso : IsIso (U.ι.stalkMap P.genericPoint) :=
      inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
    rw [PrimeDivisor.intersectionLength, stalkIdeal_idealSheaf_eq_maximalIdeal E hy,
      IsLocalRing.map_maximalIdeal_of_surjective _
        (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap P.genericPoint)).2]
    have : IsSimpleModule (U.toScheme.presheaf.stalk P.genericPoint)
        (U.toScheme.presheaf.stalk P.genericPoint ⧸
          IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk P.genericPoint)) :=
      isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal _).out
    rw [Module.length_eq_one]
    rfl
  · refine PrimeDivisor.intersectionLength_eq_zero_of_notMem U.ι E fun hmem => hE ?_
    have hco : Order.coheight (U.ι P.genericPoint) = 1 := by
      rw [show U.ι P.genericPoint = Mori.PrimeDivisor.genericPoint
        (OpenWeilRestriction.primeDivisorMap U.ι P) from
          (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm]
      exact Mori.PrimeDivisor.coheight_genericPoint _
    have h1 := PrimeDivisor.eq_genericPoint_of_mem_support E hmem hco
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (h1.symm.trans (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm)

/-- Along an open immersion `U ⟶ X`, the restriction of a divisor (`DivisorWithCoeffs.restrict`)
is its restriction by coefficients (`DivisorWithCoeffs.restrictOpen`). -/
theorem restrict_ι_eq_restrictOpen {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : D.restrict U.ι = D.restrictOpen U := by
  classical
  have hc : ∀ P, DivisorWithCoeffs.restrictCoeff U.ι D P =
      D.coeff (OpenWeilRestriction.primeDivisorMap U.ι P) := by
    intro P
    simp only [DivisorWithCoeffs.restrictCoeff, intersectionLength_ι, ite_smul, one_smul,
      zero_smul, Finsupp.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  have hfin : (Function.support (DivisorWithCoeffs.restrictCoeff U.ι D)).Finite := by
    refine (D.support.finite_toSet.preimage
      (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn).subset fun P hP => ?_
    rw [Function.mem_support, hc] at hP
    exact Finsupp.mem_support_iff.mpr hP
  ext P
  change (D.restrict U.ι).coeff P = (D.restrictOpen U).coeff P
  rw [DivisorWithCoeffs.coeff_restrict U.ι hfin, DivisorWithCoeffs.coeff_restrictOpen]
  exact hc P

end Restrict

/-- A proper curve `C` of an open `U ⊆ X`, `X` separated over `k`, is a proper curve `Γ` of `X`,
with the same generic point and isomorphic to `C` over `X`. -/
theorem exists_properCurve_of_opens {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) [IsSeparated sX] (C : ProperCurve (U.ι ≫ sX)) :
    ∃ (Γ : ProperCurve sX) (e : C.scheme ≅ Γ.scheme),
      Γ.point = U.ι C.point ∧ e.hom ≫ Γ.ι = C.ι ≫ U.ι := by
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have : IsProper (C.ι ≫ U.ι) := IsProper.of_comp (C.ι ≫ U.ι) sX
  have hrange : Set.range (C.ι ≫ U.ι) = U.ι '' closure {C.point} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    congr 1
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set U))).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hcl : closure ({U.ι C.point} : Set X) ⊆ Set.range U.ι := by
    refine (closure_minimal ?_ (C.ι ≫ U.ι).isClosedMap.isClosed_range).trans ?_
    · rw [Set.singleton_subset_iff, hrange]; exact ⟨C.point, subset_closure rfl, rfl⟩
    · rw [hrange]; exact Set.image_subset_range _ _
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι C.point rfl hcl
  refine ⟨⟨U.ι C.point, ⟨?_, ?_⟩⟩, e, rfl, he⟩
  · rw [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C.dim_eq
  · have : curveSubschemeAtι (U.ι C.point) ≫ sX = e.inv ≫ (C.ι ≫ U.ι) ≫ sX := by
      rw [← he, Category.assoc, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance

section Compare

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (U : X.Opens) [IsIntegral U]
  [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [IsDominant U.ι]

/-- The restriction to a dense open `U` of a Cartier divisor is its pull-back along `U ⟶ X`. -/
theorem isPullback_restrictOpen {N : Divisor X} (hN : N.IsCartier) :
    N.IsPullback U.ι (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
      (N.restrictOpen U) := by
  obtain ⟨N', hN'⟩ := hN.exists_isPullback (f := U.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
  have hiso : ∀ P : Mori.PrimeDivisor U, IsIso (U.ι.stalkMap P.genericPoint) := fun P =>
    inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
  have : N' = N.restrictOpen U := by
    ext P
    change N'.coeff P = (N.restrictOpen U).coeff P
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact MMP.Positivity.coeff_eq_of_isPullback P _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm hN hN'
  exact this ▸ hN'

variable [QuasiCompact sX] [QuasiCompact (U.ι ≫ sX)]

/-- **Intersection numbers can be computed on a dense open.** For a `ℚ`-Cartier `ℚ`-divisor `L`
on `X` and a curve `i : C ⟶ U`, proper over `k`, `(L|_U · C) = (L · C)`, the right-hand side
computed along `i ≫ (U ⟶ X)`. -/
theorem intersectionNumber_restrictOpen (L : QDivisor X) (hL : L.IsQCartier)
    (hLU : QDivisor.IsQCartier (L.restrictOpen U)) {C : Scheme.{u}} (i : C ⟶ U)
    [IsProper (i ≫ U.ι ≫ sX)] (hdim : topologicalKrullDim C ≤ 1) :
    haveI : IsProper ((i ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    QDivisor.intersectionNumber k (U.ι ≫ sX) i hdim (L.restrictOpen U) hLU =
      L.intersectionNumber k sX (i ≫ U.ι) hdim hL := by
  have : IsProper ((i ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have hm := QDivisor.cartierIndex_pos hL
  obtain ⟨N, hN, hNc⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hL
  have hp := isPullback_restrictOpen U hNc
  have hNUc : Divisor.IsCartier (N.restrictOpen U) := Divisor.IsPullback.isCartier hp hNc
  have hNU : Divisor.toQDivisor (N.restrictOpen U) =
      ((L.cartierIndex hL : ℕ) : ℤ) • L.restrictOpen U := by
    ext P
    exact congrArg (fun G : QDivisor X => G (OpenWeilRestriction.primeDivisorMap U.ι P)) hN
  rw [QDivisor.intersectionNumber_eq_of_smul k (U.ι ≫ sX) i hdim _ hLU hm _ hNUc hNU,
    QDivisor.intersectionNumber_eq_of_smul k sX (i ≫ U.ι) hdim _ hL hm _ hNc hN]
  congr 2
  have := hNc.isInvertibleModule_divisorialSheaf
  have := hNUc.isInvertibleModule_divisorialSheaf
  change Mori.degreeOn k (U.ι ≫ sX) i hdim (Divisor.divisorialSheaf (N.restrictOpen U)) =
    Mori.degreeOn k sX (i ≫ U.ι) hdim N.divisorialSheaf
  rw [degreeOn_eq_of_iso k (U.ι ≫ sX) i hdim
      (Divisor.IsPullback.divisorialSheafIso (hBc := hNc) hp),
    degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι i rfl]

/-- The intersection number of `L|_U` with a proper curve `C` of an open `U` is that of `L` with
the proper curve `Γ` of `X` isomorphic to `C` over `X` (`exists_properCurve_of_opens`). -/
theorem intersectionNumber_restrictOpen_of_iso (L : QDivisor X) (hL : L.IsQCartier)
    (hLU : QDivisor.IsQCartier (L.restrictOpen U)) (C : ProperCurve (U.ι ≫ sX)) (Γ : ProperCurve sX)
    (e : C.scheme ≅ Γ.scheme) (he : e.hom ≫ Γ.ι = C.ι ≫ U.ι) :
    QDivisor.intersectionNumber k (U.ι ≫ sX) C.ι C.dim_le (L.restrictOpen U) hLU =
      L.intersectionNumber k sX Γ.ι Γ.dim_le hL := by
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [intersectionNumber_restrictOpen sX U L hL hLU C.ι C.dim_le]
  simp only [QDivisor.intersectionNumber, Divisor.degreeOn]
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX (C.ι ≫ U.ι) Γ.ι C.dim_le
    Γ.dim_le e he]

end Compare

/-- If the generic fibre of a surjective morphism `g : V ⟶ W` of integral schemes locally of finite
type over `k` is a curve, then `dim V = dim W + 1`. -/
private theorem topologicalKrullDim_eq_add_one {k : Type u} [Field k] {V W : Scheme.{u}}
    (sV : V ⟶ Spec (.of k)) (sW : W ⟶ Spec (.of k)) [IsIntegral V] [IsIntegral W]
    [LocallyOfFiniteType sV] [LocallyOfFiniteType sW] [CompactSpace W] (g : V ⟶ W)
    (hg : g ≫ sW = sV) (hs : Function.Surjective g)
    (h1 : topologicalKrullDim (g.base ⁻¹' {genericPoint W}) = 1) :
    topologicalKrullDim V = topologicalKrullDim W + 1 := by
  have := locallyOfFiniteType_of_comp_eq sV sW g hg
  have hθ := genericPoint_map_of_surjective g hs
  rw [← (g.fiberHomeo (genericPoint W)).isHomeomorph.topologicalKrullDim_eq] at h1
  have dF := toENat_trdeg_eq_topologicalKrullDim_fiber g (genericPoint V)
    (isGenericPoint_asFiber_genericPoint g)
  have dV := topologicalKrullDim_eq_trdeg_residueField k V sV (genericPoint V)
    (genericPoint_spec V)
  have dW := topologicalKrullDim_eq_trdeg_residueField k W sW (g (genericPoint V))
    (hθ ▸ genericPoint_spec W)
  have ht := congrArg Cardinal.toENat (trdeg_residueField_add sV sW g hg (genericPoint V))
  rw [map_add] at ht
  rw [← hθ, ← dF] at h1
  rw [dV, dW, ← ht, ← h1]
  rfl

/-- In a quasi-sober `T₀` space, every point `p` of a closed set `F` is a specialization of a
point `q ∈ F` with no proper generalization in `F`: the generic point of an irreducible component
of `F` containing `p`. -/
private theorem exists_maximal_generalization {T : Type*} [TopologicalSpace T] [QuasiSober T]
    [T0Space T] {F : Set T} (hF : IsClosed F) {p : T} (hp : p ∈ F) :
    ∃ q ∈ F, q ⤳ p ∧ ∀ y ∈ F, y ⤳ q → y = q := by
  have : QuasiSober F := hF.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨Y, hY, hpY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({⟨p, hp⟩} : Set F)) isIrreducible_singleton.closure
  have hYc := isClosed_of_mem_irreducibleComponents Y hY
  have hgen := hY.1.isGenericPoint_genericPoint_closure
  rw [hYc.closure_eq] at hgen
  set q' := hY.1.genericPoint
  have hind : Topology.IsInducing ((↑) : F → T) := Topology.IsInducing.subtypeVal
  refine ⟨q'.1, q'.2, ?_, fun y hy hyq => ?_⟩
  · have : q' ⤳ ⟨p, hp⟩ := hgen.specializes (hpY (subset_closure rfl))
    exact this.map continuous_subtype_val
  · have hyq' : (⟨y, hy⟩ : F) ⤳ q' := hind.specializes_iff.mp hyq
    have hsub : Y ⊆ closure ({⟨y, hy⟩} : Set F) := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyq'))
        isClosed_closure
    have hle := hY.2 isIrreducible_singleton.closure hsub
    have hqy : q' ⤳ ⟨y, hy⟩ := hgen.specializes (hle (subset_closure rfl))
    exact congrArg Subtype.val (hyq'.antisymm hqy).eq

open Classical in
/-- **The components of a connected fibre form a connected curve.** Let `f : U ⟶ Z` have a
closed connected fibre `F = f⁻¹(w)`, and let `S` be curves of the open `U ⊆ X` whose generic
points are the maximal points of `F`. If each `C ∈ S` is the proper curve `Γ C` of `X`, then
`⋃_{C ∈ S} Γ C` contains `F` and is connected. -/
private theorem isConnected_curveUnion_of_fiber {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (U : X.Opens) {Z : Scheme.{u}} (f : U.toScheme ⟶ Z) {w : Z}
    (hFc : _root_.IsConnected (f ⁻¹' {w})) (hFcl : IsClosed (f ⁻¹' {w}))
    (S : Finset (ProperCurve (U.ι ≫ sX)))
    (hS : Mori.ProperCurve.point '' (S : Set (ProperCurve (U.ι ≫ sX))) =
      {x | f x = w ∧ ∀ y, f y = w → y ⤳ x → y = x})
    (Γ : ProperCurve (U.ι ≫ sX) → ProperCurve sX) (hΓ : ∀ C, (Γ C).point = U.ι C.point) :
    U.ι '' (f ⁻¹' {w}) ⊆ curveUnion sX (S.image Γ) ∧
      _root_.IsConnected (curveUnion sX (S.image Γ)) := by
  have hA : U.ι '' (f ⁻¹' {w}) ⊆ curveUnion sX (S.image Γ) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hqF, hqp, hqmax⟩ := exists_maximal_generalization hFcl hp
    obtain ⟨C, hCS, rfl⟩ : q ∈ Mori.ProperCurve.point '' (S : Set (ProperCurve (U.ι ≫ sX))) := by
      rw [hS]; exact ⟨hqF, hqmax⟩
    refine Set.mem_biUnion (Finset.mem_image_of_mem Γ hCS) ?_
    rw [hΓ]
    exact specializes_iff_mem_closure.mp (hqp.map U.ι.continuous)
  have hcl : curveUnion sX (S.image Γ) ⊆ closure (U.ι '' (f ⁻¹' {w})) := by
    refine Set.iUnion₂_subset fun Γ' hΓ' => ?_
    obtain ⟨C, hCS, rfl⟩ := Finset.mem_image.mp hΓ'
    have hC : C.point ∈ Mori.ProperCurve.point '' (S : Set (ProperCurve (U.ι ≫ sX))) :=
      ⟨C, hCS, rfl⟩
    rw [hS] at hC
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨C.point, hC.1, (hΓ C).symm⟩)
  exact ⟨hA, (hFc.image _ U.ι.continuous.continuousOn).subset_closure hA hcl⟩

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}

/-- A principal divisor has degree zero on every proper curve. -/
private theorem degreeOn_principalDivisor (Γ : ProperCurve sX) (φ : (RationalFunctions X)ˣ) :
    (principalDivisor φ).degreeOn k sX Γ.ι Γ.dim_le (Divisor.isCartier_principalDivisor φ) =
      0 := by
  have hdc := Divisor.isCartier_principalDivisor φ
  have hiso := (Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso
  have := hdc.isInvertibleModule_divisorialSheaf
  have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
  have h1 : (principalDivisor φ).degreeOn k sX Γ.ι Γ.dim_le hdc =
      (0 : Divisor X).degreeOn k sX Γ.ι Γ.dim_le Divisor.isCartier_zero :=
    degreeOn_eq_of_iso k sX Γ.ι Γ.dim_le hiso
  rw [h1, Divisor.degreeOn_zero' k sX Γ.ι Γ.dim_le]

/-- Under the assumptions of FA 15.4, every prime divisor `D` meets the support of an effective
`ℚ`-Cartier divisor `B` that is trivial on every `(K_X + Δ_X)`-trivial proper curve: a member
of `|m(K_X + Δ_X)|` through a closed point of `D`. -/
private theorem exists_member_meets
    (h : SatisfiesAbundanceAssumptions k sX K Δ) (D : Mori.PrimeDivisor X) :
    ∃ B : QDivisor X, ∃ hB : B.IsQCartier, 0 ≤ B ∧
      (∀ Γ : ProperCurve sX,
        (Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ.ι Γ.dim_le h.isQCartier = 0 →
          B.intersectionNumber k sX Γ.ι Γ.dim_le hB = 0) ∧
      ((DivisorWithCoeffs.supp (Finsupp.single D 1 : Divisor X) : Set X) ∩
        (B.supp : Set X)).Nonempty := by
  obtain ⟨m, hm, M, hMeq, hMc, h2⟩ := h.exists_two_le_h0
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hDne : (D.support : Set X).Nonempty :=
    ⟨D.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  have hDc : IsClosed (D.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  obtain ⟨x, hxD, hx⟩ := nonempty_inter_closedPoints hDne hDc.isLocallyClosed
  obtain ⟨σ, hσ, hxσ⟩ := exists_mem_supp_zeroDivisor sX hMc h2 hx
  have hZc : (M.zeroDivisor σ hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]; exact (Divisor.isCartier_principalDivisor _).add hMc
  refine ⟨Divisor.toQDivisor (M.zeroDivisor σ hσ), QDivisor.isQCartier_toQDivisor hZc,
    fun E => ?_, fun Γ hΓ => ?_, ⟨x, ?_, ?_⟩⟩
  · have := Divisor.zeroDivisor_nonneg M σ hσ E
    change (0 : ℚ) ≤ ((M.zeroDivisor σ hσ E : ℤ) : ℚ)
    exact_mod_cast this
  · rw [QDivisor.intersectionNumber_toQDivisor k sX Γ.ι Γ.dim_le _ hZc,
      Divisor.degreeOn_congr (Divisor.zeroDivisor_eq M σ hσ) hZc
        ((Divisor.isCartier_principalDivisor _).add hMc),
      Divisor.degreeOn_add k sX Γ.ι Γ.dim_le _ _ (Divisor.isCartier_principalDivisor _) hMc,
      degreeOn_principalDivisor, zero_add,
      ← QDivisor.intersectionNumber_toQDivisor k sX Γ.ι Γ.dim_le _ hMc
        (QDivisor.isQCartier_toQDivisor hMc)]
    have e : (m : ℚ) • (Divisor.toQDivisor K + Δ) = Divisor.toQDivisor M := by
      rw [hMeq, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
    have hmL : ((m : ℚ) • (Divisor.toQDivisor K + Δ)).IsQCartier :=
      e ▸ QDivisor.isQCartier_toQDivisor hMc
    rw [Fourfold.intersectionNumber_congr sX Γ.ι Γ.dim_le _ hmL e.symm,
      Fourfold.intersectionNumber_smul sX Γ.ι Γ.dim_le _ h.isQCartier _ hmL, hΓ, mul_zero]
  · exact DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_apply]) hxD
  · rwa [Divisor.supp_toQDivisor]

/-- The support of an effective `ℚ`-Cartier divisor `B` which is trivial on every
`(K_X + Δ_X)`-trivial proper curve does not dominate the log elliptic fibration (FA, proof of
15.9). -/
private theorem not_dense_image_supp
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU)
    (B : QDivisor X) (hB : B.IsQCartier) (h0 : 0 ≤ B)
    (hBL : ∀ Γ : ProperCurve sX,
      (Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ.ι Γ.dim_le h.isQCartier = 0 →
        B.intersectionNumber k sX Γ.ι Γ.dim_le hB = 0) :
    ¬ Dense (fU '' (U.ι ⁻¹' (B.supp : Set X))) := by
  classical
  intro hd
  set L := Divisor.toQDivisor K + Δ
  have hc := hfU.isContraction
  have hUv : Mori.IsVariety k (U.ι ≫ sX) := hc.isVariety_source
  have hZv : Mori.IsVariety k sZ := hc.isVariety_target
  have hXv : Mori.IsVariety k sX := h.isProjectiveVariety.toIsVariety
  haveI : IsSeparated sX := hXv.toIsSeparated
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX h.isProjectiveVariety.isProjective
  haveI : IsIntegral U.toScheme := hUv.toIsIntegral
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsSeparated (U.ι ≫ sX) := hUv.toIsSeparated
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := hUv.toLocallyOfFiniteType
  haveI : QuasiCompact (U.ι ≫ sX) := hUv.toQuasiCompact
  haveI : IsSeparated sZ := hZv.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZv.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sX)
  haveI : IsProper fU := hc.isProper
  haveI hsurj : Surjective fU := fU.surjective_of_isIso_app hc.isIso_app
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hU)
  have hdim : topologicalKrullDim U.toScheme = topologicalKrullDim Z + 1 :=
    topologicalKrullDim_eq_add_one (U.ι ≫ sX) sZ fU hc.comp_eq hsurj.surj hfU.dim_genericFiber
  set LU := Divisor.toQDivisor (DivisorWithCoeffs.restrict U.ι K) +
    DivisorWithCoeffs.restrict U.ι Δ with hLUdef
  have hLU_eq : LU = L.restrictOpen U := by
    rw [hLUdef, restrict_ι_eq_restrictOpen, restrict_ι_eq_restrictOpen]
    ext P
    rfl
  have hLUq : QDivisor.IsQCartier (L.restrictOpen U) := hLU_eq ▸ hfU.isQCartier
  obtain ⟨Z₀, hZ₀d, hZ₀⟩ := exists_dense_open_genericFiberDegree_eq_sum_intersectionNumber
    (U.ι ≫ sX) sZ fU hc.comp_eq hdim LU hfU.isQCartier
  have himg : fU '' (U.ι ⁻¹' (B.supp : Set X)) = Set.univ := by
    have hcl : IsClosed (fU '' (U.ι ⁻¹' (B.supp : Set X))) :=
      fU.isClosedMap _ (B.supp.isClosed.preimage U.ι.continuous)
    rw [← hcl.closure_eq, hd.closure_eq]
  -- the closed points of `U` over `Z₀` lie in `Supp B`
  have key : ∀ y : U.toScheme, IsClosed ({y} : Set U.toScheme) → fU y ∈ Z₀ →
      U.ι y ∈ (B.supp : Set X) := by
    intro y hy hyZ₀
    have hw : IsClosed ({fU y} : Set Z) := by
      simpa using fU.isClosedMap _ hy
    obtain ⟨S, hSpts, hdeg⟩ := (hZ₀ (fU y) hyZ₀).2 hw
    choose Γ e hΓpt hΓe using fun C : ProperCurve (U.ι ≫ sX) =>
      exists_properCurve_of_opens sX U C
    have hcmp : ∀ C : ProperCurve (U.ι ≫ sX),
        LU.intersectionNumber k (U.ι ≫ sX) C.ι C.dim_le hfU.isQCartier =
          L.intersectionNumber k sX (Γ C).ι (Γ C).dim_le h.isQCartier := fun C => by
      rw [Fourfold.intersectionNumber_congr (U.ι ≫ sX) C.ι C.dim_le _ hLUq hLU_eq]
      exact intersectionNumber_restrictOpen_of_iso sX U L h.isQCartier hLUq C (Γ C) (e C) (hΓe C)
    -- the components of the fibre have nonnegative degrees summing to `L · E_{f_U} = 0`
    have hzero : ∀ C ∈ S, L.intersectionNumber k sX (Γ C).ι (Γ C).dim_le h.isQCartier = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun C _ =>
        h.isNef.2 (Γ C).scheme (Γ C).ι (Γ C).dim_eq).mp ?_
      rw [← Finset.sum_congr rfl fun C _ => hcmp C, ← hdeg]
      exact hfU.genericFiberDegree_eq_zero
    obtain ⟨hA, hconn⟩ := isConnected_curveUnion_of_fiber sX U fU
      (fU.isConnected_preimage_singleton_of_isIso_app hc.isIso_app (fU y))
      (hw.preimage fU.continuous) S hSpts Γ hΓpt
    have hmeet : (curveUnion sX (S.image Γ) ∩ (B.supp : Set X)).Nonempty := by
      obtain ⟨p, hp, hpw⟩ : fU y ∈ fU '' (U.ι ⁻¹' (B.supp : Set X)) := himg ▸ Set.mem_univ _
      exact ⟨U.ι p, hA ⟨p, hpw, rfl⟩, hp⟩
    exact curveUnion_subset_supp_of_intersectionNumber_eq_zero sX hXv L h.isQCartier B hB h0 hBL
      (S.image Γ) hconn (Finset.forall_mem_image.mpr hzero) hmeet (hA ⟨y, rfl, rfl⟩)
  -- hence the generic point of `X` lies in `Supp B`
  haveI : JacobsonSpace U.toScheme := LocallyOfFiniteType.jacobsonSpace (U.ι ≫ sX)
  haveI : Nonempty Z := ⟨fU ⟨_, hU.some_mem⟩⟩
  have hOne : ((fU ⁻¹ᵁ Z₀ : U.toScheme.Opens) : Set U.toScheme).Nonempty := by
    obtain ⟨z, hz⟩ := hZ₀d.nonempty
    obtain ⟨y, rfl⟩ := hsurj.surj z
    exact ⟨y, hz⟩
  obtain ⟨q, hqO, hq⟩ : genericPoint X ∈ U.ι '' (fU ⁻¹ᵁ Z₀ : U.toScheme.Opens) :=
    ((genericPoint_spec X).mem_open_set_iff (U.ι.isOpenMap _ (fU ⁻¹ᵁ Z₀).isOpen)).mpr
      (by simpa using hOne.image U.ι)
  have hqB : U.ι q ∈ (B.supp : Set X) := by
    by_contra hqB
    have hO' : IsOpen (((fU ⁻¹ᵁ Z₀ : U.toScheme.Opens) : Set U.toScheme) ∩
        (U.ι ⁻¹' (B.supp : Set X))ᶜ) :=
      (fU ⁻¹ᵁ Z₀).isOpen.inter (B.supp.isClosed.preimage U.ι.continuous).isOpen_compl
    obtain ⟨y, ⟨hyO, hyB⟩, hyc⟩ := nonempty_inter_closedPoints
      (show (((fU ⁻¹ᵁ Z₀ : U.toScheme.Opens) : Set U.toScheme) ∩
        (U.ι ⁻¹' (B.supp : Set X))ᶜ).Nonempty from ⟨q, hqO, hqB⟩) hO'.isLocallyClosed
    exact hyB (key y hyc hyO)
  rw [hq] at hqB
  exact Fourfold.genericPoint_notMem_supp B hqB

/-- **A trivially connected prime divisor is vertical** (FA, proof of 15.9). Let `(X, Δ_X)`,
with `K_X` a canonical divisor, satisfy the assumptions of 15.4
(`MMP.Flips.SatisfiesAbundanceAssumptions`) over an algebraically closed field of characteristic
zero, let `f_U : U ⟶ Z` be a log elliptic fiber space on a nonempty open `U ⊆ X` as in (15.4.3),
and let `D` be a prime divisor of `X` which is `(K_X + Δ_X)`-trivially connected
(`MMP.Flips.IsTriviallyConnected`). Then `f_U(D ∩ U)` is not dense in `Z`. -/
@[mmp "lem_fa15_general_fiber_misses_trivially_connected"]
theorem not_dense_image_of_isTriviallyConnected
    (h : SatisfiesAbundanceAssumptions k sX K Δ)
    (U : X.Opens) (hU : (U : Set X).Nonempty) {Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (fU : U.toScheme ⟶ Z)
    (hfU : IsLogEllipticFiberSpace k (U.ι ≫ sX) sZ 3 (DivisorWithCoeffs.restrict U.ι K)
      (DivisorWithCoeffs.restrict U.ι Δ) fU)
    (D : Mori.PrimeDivisor X)
    (hD : IsTriviallyConnected k sX 3 K Δ (Finsupp.single D 1)) :
    ¬ Dense (fU '' (U.ι ⁻¹' (D.support : Set X))) := by
  obtain ⟨B, hB, h0, hBL, hmeet⟩ := exists_member_meets sX h D
  have hDB := supp_subset_supp_of_isTriviallyConnected sX 3 K Δ D hD h.isQCartier B hB h0 hBL hmeet
  have hsub : (D.support : Set X) ⊆ B.supp := fun x hx =>
    hDB (DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff_apply]) hx)
  exact fun hd => not_dense_image_supp sX h U hU sZ fU hfU B hB h0 hBL
    (hd.mono (Set.image_mono (Set.preimage_mono hsub)))

end TriviallyConnected

end MMP.Flips
