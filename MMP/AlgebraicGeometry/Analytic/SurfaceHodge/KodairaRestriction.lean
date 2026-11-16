module

public import MMP.AlgebraicGeometry.Divisor.SmoothDivisorRestriction
public import MMP.AlgebraicGeometry.Vanishing.KodairaCharZero
public import MMP.AlgebraicGeometry.CohenMacaulay.SerreDuality
public import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
public import MMP.AlgebraicGeometry.Positivity.VeryAmpleMultiple
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafSections

/-!
# Kodaira restriction of `H¹(𝒪)` to a smooth ample curve

Let `X` be a smooth projective variety of dimension `n ≥ 2` over an algebraically closed field
`k` of characteristic zero, `L` an ample invertible sheaf on `X` and `s` a regular global section
of `L`, with zero scheme `Z = Z(s)` and inclusion `i : Z ⟶ X`. The ideal sequence
`0 ⟶ ℐ_Z ⟶ 𝒪_X ⟶ i_* 𝒪_Z ⟶ 0` has `ℐ_Z ≅ L^∨`, and Kodaira vanishing gives
`H¹(X, L^∨) = 0` since `1 < n`. The long exact cohomology sequence therefore makes the restriction
`H¹(X, 𝒪_X) ⟶ H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)` injective, so `h¹(𝒪_X) ≤ h¹(𝒪_Z)`.

For a very ample Cartier divisor `A` Bertini's theorem gives a nonzero section of `𝒪_X(A)` with
smooth zero scheme `Z`; the Enriques–Severi–Zariski theorem makes `Z` connected, hence integral,
and `Z` is an effective Cartier divisor, hence of dimension `n - 1`. So `Z` is a smooth
projective connected subvariety of dimension `n - 1` (a curve when `X` is a surface) on which the
restriction of `H¹(𝒪)` is injective. Every projective variety has a very ample Cartier divisor,
and every sufficiently high multiple of an ample one is very ample
(`MMP.Resolution.Bridges.eventually_isVeryAmpleDivisor_nsmul`), so `Z` may be taken in `|mA|`
for any ample `A` and `m ≫ 0`.

## Main results

* `MMP.Analytic.SurfaceHodge.injective_cohomologyOverFieldMap_divisorQuotientMap_zeroScheme`:
  the restriction `H¹(X, 𝒪_X) ⟶ H¹(Z, 𝒪_Z)` to the zero scheme of a regular section of an ample
  invertible sheaf is injective.
* `MMP.Analytic.SurfaceHodge.finrank_cohomologyOverField_unit_one_le_zeroScheme`:
  `h¹(X, 𝒪_X) ≤ h¹(Z, 𝒪_Z)`.
* `MMP.Analytic.SurfaceHodge.exists_smooth_connected_zeroScheme_of_isVeryAmpleDivisor`: a very
  ample divisor has a member that is smooth of relative dimension `n - 1`, connected, integral
  and projective, on which the restriction of `H¹(𝒪)` is injective.
* `MMP.Analytic.SurfaceHodge.exists_isVeryAmpleDivisor_of_isProjectiveVariety`: a projective
  variety carries a very ample Cartier divisor.

## Implementation notes

The curve is the zero scheme `AlgebraicGeometry.zeroScheme` of a section of `𝒪_X(A)`, a closed
subscheme with its closed immersion, rather than a prime divisor: this is the form Bertini's
theorem produces and the form the Jacobian of a curve is stated for. The restriction map is
`H¹` of `Stacks.IdealSheafSequence.divisorQuotientMap`, the map `𝒪_X ⟶ i_* 𝒪_Z`, followed by the
identification `cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 2.47.
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MMP.Intersection

namespace MMP.Analytic.SurfaceHodge

universe u

/-- **Kodaira restriction to the zero scheme of an ample section.** Let `X` be a smooth projective
variety of dimension `n ≥ 2` over an algebraically closed field `k` of characteristic zero, `L`
an ample invertible sheaf and `s` a regular global section of `L`, with zero scheme `Z`. Then the
restriction `H¹(X, 𝒪_X) ⟶ H¹(X, i_* 𝒪_Z) ≅ H¹(Z, 𝒪_Z)` is injective. -/
theorem injective_cohomologyOverFieldMap_divisorQuotientMap_zeroScheme
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : MMP.Mori.IsSmoothScheme f)
    {n : ℕ} (hn : topologicalKrullDim X = n) (h2 : 2 ≤ n) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    (hs : ∀ U : X.Opens, Function.Injective fun r : Γ(X, U) =>
      r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) :
    Function.Injective (cohomologyOverFieldMap k f
        (Stacks.IdealSheafSequence.divisorQuotientMap (zeroScheme X L s)) 1 ≫
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k (zeroScheme X L s).subschemeι f
        (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1).inv).hom := by
  obtain ⟨_, hS⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact (zeroScheme X L s)
  obtain ⟨-, -, hfg, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  have := isIso_zeroSchemeIdealHom L s hs
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := ‹_›
  have hK := MMP.Mori.subsingleton_derivedCohomologyOverField_dualSheaf_of_isAmple f hsm n hn L
    hL 1 (by omega)
  let e₀ := asIso (zeroSchemeIdealHom L s)
  let e : (dualModule L : X.Modules) ≅
      (Stacks.Divisors.idealSheafOfModules (zeroScheme X L s) : X.Modules) :=
    { hom := e₀.hom, inv := e₀.inv, hom_inv_id := e₀.hom_inv_id, inv_hom_id := e₀.inv_hom_id }
  have h1 : Subsingleton (cohomologyOverField k f
      (Stacks.ClosedImmersion.idealSheaf (zeroScheme X L s).subschemeι.toLRSHom.toShHom) 1) :=
    ((cohomologyOverFieldIso k f e 1).toLinearEquiv.toEquiv.symm.trans
      (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k f _ 1).toEquiv
      ).subsingleton
  have hg : Function.Injective (cohomologyOverFieldMap k f
      (Stacks.IdealSheafSequence.divisorQuotientMap (zeroScheme X L s)) 1).hom := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hfg 1 x).1 hx
    rw [Subsingleton.elim y 0, map_zero]
  exact fun a b h => hg ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k
    (zeroScheme X L s).subschemeι f
    (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1).toLinearEquiv.symm.injective
      h)

/-- **`h¹(𝒪_X) ≤ h¹(𝒪_Z)` for the zero scheme of an ample section.** Under the hypotheses of
`injective_cohomologyOverFieldMap_divisorQuotientMap_zeroScheme`, the dimension of `H¹(X, 𝒪_X)`
is at most that of `H¹(Z, 𝒪_Z)`, the latter being finite since `Z` is proper over `k`. -/
theorem finrank_cohomologyOverField_unit_one_le_zeroScheme
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : MMP.Mori.IsSmoothScheme f)
    {n : ℕ} (hn : topologicalKrullDim X = n) (h2 : 2 ≤ n) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    (hs : ∀ U : X.Opens, Function.Injective fun r : Γ(X, U) =>
      r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ≤
      Module.finrank k (cohomologyOverField k ((zeroScheme X L s).subschemeι ≫ f)
        (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1) := by
  have : IsProper f := inferInstance
  have : IsLocallyNoetherian (zeroScheme X L s).subscheme :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ ((zeroScheme X L s).subschemeι ≫ f)
      inferInstance (isLocallyNoetherian_Spec.mpr inferInstance)
  have := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit (zeroScheme X L s).subscheme
  have := finiteDimensional_cohomologyOverField_of_isProper k
    ((zeroScheme X L s).subschemeι ≫ f)
    (SheafOfModules.unit (zeroScheme X L s).subscheme.ringCatSheaf) 1
  exact LinearMap.finrank_le_finrank_of_injective
    (injective_cohomologyOverFieldMap_divisorQuotientMap_zeroScheme f hsm hn h2 L hL s hs)

/-- On a normal scheme, irreducible and locally of finite type over a field, of dimension at
least two, the local ring at every closed point has depth at least two. -/
private theorem two_le_depth_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IrreducibleSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (hdim : 2 ≤ topologicalKrullDim X)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) := by
  have h := (hasPropertySk_iff X 2).mp (hasPropertySk_two_of_isNormal X) x
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX x hx,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k X sX
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) x, Nat.cast_ofNat,
    min_eq_left hdim] at h
  exact WithBot.coe_le_coe.1 h

/-- In `WithBot ℕ∞`, `d + 1 = m + 1` for a natural number `m` forces `d = m`. -/
private theorem eq_natCast_of_add_one_eq_natCast_succ {d : WithBot ℕ∞} {m : ℕ}
    (h : d + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : d = m := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd ((WithBot.bot_add 1).symm.trans h) WithBot.bot_ne_coe
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => norm_cast at h
    | coe d =>
      norm_cast at h ⊢
      omega

/-- The zero scheme of a nonzero section of an invertible sheaf on a projective variety of
dimension `n ≥ 1`, when integral and smooth over `k`, is smooth of relative dimension `n - 1`. -/
theorem smoothOfRelativeDimension_pred_zeroScheme_of_ne_zero
    {k : Type} [Field k] {X : Scheme.{0}} [X.Over (Spec (.of k))]
    [IsProjectiveVariety k (X ↘ Spec (.of k))] {n : ℕ} (hdimX : topologicalKrullDim X = n)
    (hn : 1 ≤ n) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    (hs0 : s ≠ 0) [IsIntegral (zeroScheme X L s).subscheme]
    [Smooth ((zeroScheme X L s).subschemeι ≫ X ↘ Spec (.of k))] :
    SmoothOfRelativeDimension (n - 1) ((zeroScheme X L s).subschemeι ≫ X ↘ Spec (.of k)) := by
  set f := X ↘ Spec (.of k)
  set Z := zeroScheme X L s
  set ι := Z.subschemeι
  have : IsIntegral X := (inferInstance : IsVariety k f).toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcart := isEffectiveCartierDivisor_zeroScheme_of_ne_zero L s hs0
  set ξ := genericPoint Z.subscheme
  have hξ : closure ({ξ} : Set Z.subscheme) = Set.univ := genericPoint_spec Z.subscheme
  have hdim1 := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor Z hcart ξ
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩, hξ⟩
  rw [ringKrullDim_stalk_eq_coheight] at hdim1
  have hco : Order.coheight (ι ξ) = 1 := by exact_mod_cast hdim1
  have hformula := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f (ι ξ)
  rw [hco, hdimX] at hformula
  have he := IsClosedImmersion.isClosedEmbedding ι
  have hclos : closure ({ι ξ} : Set X) = Set.range ι := by
    rw [← Set.image_singleton, he.isClosedMap.closure_image_eq_of_continuous he.continuous, hξ,
      Set.image_univ]
  have hdimZ : topologicalKrullDim Z.subscheme = topologicalKrullDim (Set.range ι) :=
    IsHomeomorph.topologicalKrullDim_eq _ he.isEmbedding.toHomeomorph.isHomeomorph
  rw [hclos, ← hdimZ] at hformula
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hdZ : topologicalKrullDim Z.subscheme = ((m + 1 - 1 : ℕ) : WithBot ℕ∞) := by
    rw [Nat.add_sub_cancel]
    exact eq_natCast_of_add_one_eq_natCast_succ (by exact_mod_cast hformula)
  have : IsVariety k (ι ≫ f) := {}
  exact smoothOfRelativeDimension_of_isVariety (ι ≫ f) (m + 1 - 1) hdZ

/-- **A smooth connected member of a very ample system, with Kodaira restriction.** Let `X` be a
smooth projective variety of dimension `n ≥ 2` over an algebraically closed field `k` of
characteristic zero and `A` a very ample Cartier divisor. Then there is a nonzero section `s` of
`𝒪_X(A)` whose zero scheme `Z` is connected, integral, smooth of relative dimension `n - 1` and
projective over `k`, such that the restriction `H¹(X, 𝒪_X) ⟶ H¹(Z, 𝒪_Z)` is injective; in
particular `h¹(𝒪_X) ≤ h¹(𝒪_Z)`. -/
theorem exists_smooth_connected_zeroScheme_of_isVeryAmpleDivisor
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [X.Over (Spec (.of k))]
    [IsProjectiveVariety k (X ↘ Spec (.of k))] {n : ℕ}
    [SmoothOfRelativeDimension n (X ↘ Spec (.of k))] (hn : 2 ≤ n)
    (A : X.CartierDivisor) (hA : IsVeryAmpleDivisor k A) :
    ∃ s : Γ(MMP.CartierDivisor.sheaf A, ⊤), s ≠ 0 ∧
      ConnectedSpace
        (@zeroScheme X (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.isInvertibleModule_sheaf A)
            s).subscheme ∧
      IsIntegral (@zeroScheme X (MMP.CartierDivisor.sheaf A)
          (MMP.CartierDivisor.isInvertibleModule_sheaf A) s).subscheme ∧
      SmoothOfRelativeDimension (n - 1)
        ((@zeroScheme X (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.isInvertibleModule_sheaf A)
            s).subschemeι ≫
          X ↘ Spec (.of k)) ∧
      IsProjectiveMorphism
        ((@zeroScheme X (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.isInvertibleModule_sheaf A)
            s).subschemeι ≫
          X ↘ Spec (.of k)) ∧
      Function.Injective (cohomologyOverFieldMap k (X ↘ Spec (.of k))
          (Stacks.IdealSheafSequence.divisorQuotientMap
            (@zeroScheme X (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.isInvertibleModule_sheaf
                A) s)) 1 ≫
        (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k
          (@zeroScheme X (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.isInvertibleModule_sheaf
              A) s).subschemeι
          (X ↘ Spec (.of k)) (SheafOfModules.unit (@zeroScheme X (MMP.CartierDivisor.sheaf A)
            (MMP.CartierDivisor.isInvertibleModule_sheaf A) s).subscheme.ringCatSheaf) 1).inv).hom ∧
      Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
          (SheafOfModules.unit X.ringCatSheaf) 1) ≤
        Module.finrank k (cohomologyOverField k
          ((@zeroScheme X (MMP.CartierDivisor.sheaf A) (MMP.CartierDivisor.isInvertibleModule_sheaf
              A) s).subschemeι ≫
            X ↘ Spec (.of k))
          (SheafOfModules.unit (@zeroScheme X (MMP.CartierDivisor.sheaf A)
            (MMP.CartierDivisor.isInvertibleModule_sheaf A) s).subscheme.ringCatSheaf) 1) := by
  set f := X ↘ Spec (.of k)
  have hV : IsVariety k f := inferInstance
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsSmoothVariety k f := (isSmoothVariety_iff k f).2 ⟨hV, inferInstance⟩
  have : IsIntegral X := hV.toIsIntegral
  have : IsProper f := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNormal X := isNormal_of_smooth_over_field f
  have hdimX : topologicalKrullDim X = n := topologicalKrullDim_eq_of_smoothOfRelativeDimension f n
  set L := MMP.CartierDivisor.sheaf A
  have hLi : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    MMP.CartierDivisor.isInvertibleModule_sheaf A
  obtain ⟨s, hs0, hsm⟩ := exists_ne_zero_smooth_zeroScheme_of_isVeryAmpleDivisor k A hA
  refine ⟨s, hs0, ?_⟩
  set Z := zeroScheme X L s
  set ι := Z.subschemeι
  have : Stacks.Ample.IsInvertibleModule X L := MMP.CartierDivisor.isInvertibleModule_sheaf A
  have hamp : Stacks.Ample.IsAmple X L := by
    have htfae := Stacks.AmpleRelativeFiniteType.tfae_six f L
    have h5 : ∃ d : ℕ, 1 ≤ d ∧ Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver f
        (Stacks.Ample.tensorPowModule X L (d : ℤ)) :=
      ⟨1, le_rfl, MMP.Resolution.Bridges.hasImmersionTwistOver_of_isVeryAmple k L _ hA
        (Stacks.Ample.tensorPowModuleOneIso _ _)⟩
    exact (htfae.out 5 1).1 h5
  set t := Stacks.Divisors.sectionsOfTop L s
  have hte : t.eval (op ⊤) = s := Stacks.Divisors.sectionsOfTop_eval_top _ _
  have hreg := isRegularSection_of_eval_top_ne_zero L t (hte ▸ hs0)
  have : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L := hLi
  have hconn : ConnectedSpace Z.subscheme := by
    have := Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple k f L
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X _).2 hamp) t hreg
      (two_le_depth_stalk f (by rw [hdimX]; exact_mod_cast hn))
    rwa [hte] at this
  have : Smooth (ι ≫ f) := hsm
  have hZi : IsIntegral Z.subscheme := isIntegral_of_smooth_of_connectedSpace (ι ≫ f)
  have hs' : ∀ U : X.Opens, Function.Injective fun r : Γ(X, U) =>
      r • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
    have := injective_smul_res_of_isRegularSection L t hreg
    rwa [hte] at this
  have hsmX : MMP.Mori.IsSmoothScheme f := MMP.Flips.isSmoothScheme_of_smooth f
  refine ⟨hconn, hZi, ?_, isProjectiveMorphism_isClosedImmersion_comp ι f
    IsProjectiveVariety.isProjective,
    injective_cohomologyOverFieldMap_divisorQuotientMap_zeroScheme f hsmX hdimX hn L hamp s hs',
    finrank_cohomologyOverField_unit_one_le_zeroScheme f hsmX hdimX hn L hamp s hs'⟩
  exact smoothOfRelativeDimension_pred_zeroScheme_of_ne_zero hdimX (by omega) L s hs0

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A very ample line bundle is generated by finitely many global sections: the pullbacks of the
homogeneous coordinates along the embedding into projective space. -/
private theorem exists_sections_cover_of_isVeryAmple {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {L : X.Modules} (hL : IsVeryAmple k L) :
    ∃ (N : ℕ) (σ : Fin (N + 1) → Γ(L, ⊤)),
      ∀ x : X, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus L (σ j) := by
  obtain ⟨N, ι, -, -, ⟨e⟩⟩ := hL
  set 𝒮 := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k
  have hwhere : Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible 𝒮 1 = ⊤ :=
    (Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus 𝒮 1).trans
      (Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_adjoin_degree_one 𝒮
        (Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule _ k) 1)
  let t := fun j : Fin (N + 1) => ProjectiveSpectrum.Proj.degreeSection 𝒮 (1 * 1)
      ⟨MvPolynomial.X (ULift.up j), Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one _⟩
  refine ⟨N, fun j => e.inv.app ⊤ (pullbackGlobalSections ι (ProjSpace.twistOne k _) (t j)),
    fun x => ?_⟩
  have hx : ι.base x ∈ (⨆ i : ULift.{u} (Fin (N + 1)),
      Proj.basicOpen 𝒮 (MvPolynomial.X i)) := by
    rw [Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top]; trivial
  obtain ⟨⟨j⟩, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have h := (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒮 1 1 ⟨MvPolynomial.X (ULift.up j), Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one _⟩
    (x := ι.base x) (by rw [hwhere]; trivial)).mpr hj
  exact ⟨j, Stacks.Ample.nonvanishingLocus_congr e.symm
    (pullbackGlobalSections ι (ProjSpace.twistOne k _) (t j)) ▸
      Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections ι _ _ h⟩

/-- **A projective variety carries a very ample Cartier divisor.** The pullback of `𝒪(1)` along
a projective embedding is very ample; it has a nonzero global section, whose divisor `D` has
`𝒪_X(D)` isomorphic to it. -/
theorem exists_isVeryAmpleDivisor_of_isProjectiveVariety {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsProjectiveVariety k (X ↘ Spec (.of k))] :
    ∃ A : X.CartierDivisor, IsVeryAmpleDivisor k A := by
  have : IsIntegral X := (inferInstance : IsVariety k (X ↘ Spec (.of k))).toIsIntegral
  obtain ⟨n, i, hi, hover⟩ :=
    (IsProjectiveVariety.isProjective : IsProjectiveMorphism (X ↘ Spec (.of k)))
  let A₀ := (Scheme.Modules.pullback i).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k)))
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A₀ := inferInstance
  have : Stacks.Ample.IsInvertibleModule X A₀ := inferInstance
  have hva₀ : IsVeryAmple k A₀ :=
    MMP.Resolution.Bridges.isVeryAmple_of_isClosedImmersion k A₀ A₀ (Iso.refl _) n i hover
      (Iso.refl _)
  obtain ⟨N, σ, hσ⟩ := exists_sections_cover_of_isVeryAmple hva₀
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨j, hj⟩ := hσ x
  have hne : σ j ≠ 0 := fun h => by
    rw [h, Stacks.Ample.nonvanishingLocus_zero] at hj
    exact hj
  obtain ⟨D, hD⟩ := exists_isDivisorOfSection A₀ (σ j) hne
  obtain ⟨φ, -⟩ := MMP.CartierDivisor.exists_sheaf_iso_of_isDivisorOfSection A₀ hD
  exact ⟨D, MMP.Resolution.Bridges.isVeryAmple_of_isClosedImmersion k
    (MMP.CartierDivisor.sheaf D) A₀ φ n i hover (Iso.refl _)⟩

end MMP.Analytic.SurfaceHodge
