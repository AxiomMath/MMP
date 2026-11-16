module

public import MMP.AlgebraicGeometry.Divisor.ReflexivePowerLocallyFree
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
public import MMP.AlgebraicGeometry.Positivity.AmpleTwistRealPerturbation
public import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
public import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra
public import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# Exceptional divisors and loci, finite covers, reflexive powers and an snc criterion

Auxiliary results of Kollár–Mori §2.5–2.6 on birational morphisms and divisors.

* **Exceptional divisors.** Let `f : Y → X` be a projective birational morphism of normal
  varieties over a field `k`, with `X` `ℚ`-factorial. There is an effective `f`-ample Cartier
  divisor `H` on `Y` with no `f`-exceptional component, and then `F := f^*(f_*H) - H` is an
  effective `ℚ`-divisor all of whose components are `f`-exceptional. `H` is the zero divisor of a
  general section of `𝒪_Y(m)` for an embedding `Y ⊆ ℙᴺ × X` over `X`; a non-exceptional prime
  divisor of `Y` has the valuation of its image, so it does not occur in `F`. For `e > 0` with
  `e f_*H` Cartier, `eF = f^*(e f_*H) - eH` is Cartier and `-eF = eH + f^*(-e f_*H)` is `f`-ample.
* **The exceptional set over a `ℚ`-factorial base.** For `f : Y → X` projective birational with
  `X` `ℚ`-factorial, `Ex(f)` is empty or of pure codimension one. When `Y` is normal, `Ex(f)` is
  the support of the anti-ample exceptional `D = eF` above: off `Supp D`, one section of a power
  of `𝒪_Y(-D)` is `f^*h` (as `f_*𝒪_Y = 𝒪_X`), and `D(h)` is an affine neighbourhood of `f(y)`
  with affine preimage, so the fibre through `y` is finite. In general one passes to the
  normalization `ν : Yᵛ → Y`: `Ex(f) = ν(Ex(f ∘ ν))`, and the finite surjective `ν` preserves
  the codimension of points.
* **Finite covers.** For a finite surjective `π : Y → X` of varieties in characteristic zero with
  `X` normal and `ℱ` quasi-coherent, `H^i(X, ℱ)` is a direct summand of `H^i(Y, π^*ℱ)`: the
  normalised trace splits `𝒪_X → π_*𝒪_Y`, so `ℱ` is a summand of `π_*π^*ℱ ≅ ℱ ⊗ π_*𝒪_Y`, and `π`
  is affine.
* **Reflexive powers.** For a coherent torsion-free rank-one sheaf `L` on a normal variety, every
  reflexive power `L^{[i]}` is the dual of a coherent sheaf, hence coherent and reflexive; and it
  is the unique reflexive coherent sheaf restricting to `L^{⊗ i}` on the locally free locus `X⁰`,
  because `X \ X⁰` has codimension at least two [Stacks, Tag 0EBJ].
* **An snc criterion.** Effective Cartier divisors `G₁, …, G_s` on a smooth `n`-dimensional
  variety, every non-empty intersection `G_J` of which is empty or smooth of pure dimension
  `n - |J|`, add up to a reduced snc divisor: at each point their local equations are part of a
  regular system of parameters.

## Main results

* `MMP.Mori.exists_isRelativelyAmple_isPullback_transformDivisor_eq_add`: `H` and `F` with
  `f^*(f_*H) = H + F`.
* `MMP.Mori.exists_isRelativelyAmple_neg_smul_of_isExceptional`: an effective exceptional `F`
  and `e > 0` with `-eF` Cartier and `f`-ample.
* `MMP.Mori.isPureCodimOne_exceptionalSet_of_isQFactorial`: `Ex(f)` is of pure codimension one.
* `MMP.Mori.nonempty_retract_cohomologyOverField_pullback_of_isFinite`: `H^i(X, ℱ)` is a retract
  of `H^i(Y, π^* ℱ)` in `ModuleCat k`.
* `MMP.Mori.isCoherent_reflexivePow_and_isReflexive`: `L^{[i]}` is coherent and reflexive.
* `MMP.Mori.nonempty_iso_reflexivePow_of_isReflexive`: `𝒢 ≅ L^{[i]}`.
* `MMP.Mori.DivisorWithCoeffs.isSNC_of_forall_smooth_iSup`: the snc criterion.

## Implementation notes

The push-forward `f_*H` is `MMP.Mori.RationalMap.transformDivisor` along `f.toRationalMap`, and
`f^*(f_*H) = H + F` is stated through `MMP.Mori.QDivisor.IsPullback`, which determines the
pull-back of a `ℚ`-Cartier divisor uniquely. The integral divisor `eF` is a `MMP.Mori.Divisor`
`D` with `Divisor.toQDivisor D = e • F`. "Isomorphic to a direct summand" is
`CategoryTheory.Retract` in `ModuleCat k`; the vanishing `H^i(Y, π^*ℱ) = 0 → H^i(X, ℱ) = 0`
follows. The `i`-th power of `L|_{X⁰}` is `MMP.Intersection.Scheme.Modules.tensorZPow`. In the
snc criterion the divisors are indexed by a finite type `ι`, their intersection is the supremum
of their ideal sheaves, `G₁ + ⋯ + G_s` is the divisor `D` with coefficient
`∑ⱼ length(𝒪_{Y,P} / (G_j)_P)` at `P`, and pure dimension `n - |J|` is `dim C + |J| = n` for
every irreducible component `C`.

The construction of `H` and `F` is carried out for a proper `f` factoring through a finite
morphism to some `ℙⁿ_X`, rather than a closed immersion: the composite of a projective morphism
with the normalization of its source is of this form, but need not be projective in the sense of
`AlgebraicGeometry.IsProjectiveMorphism` when `X` carries no ample invertible sheaf. In the
divisoriality of `Ex(f)`, the source's argument through relative global generation of `𝒪_Y(reH)`
and degrees on contracted curves is replaced by the anti-ample divisor `-eF`. Kollár–Mori state
that result for `Y` projective; only projectivity of `f` is used. "Empty or of pure codimension
one" is `MMP.Mori.IsPureCodimOne`, which holds vacuously for the empty set.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.52, 2.62,
  2.63, proof of 2.64 (Step 1), proof of 2.67
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Proof_lem_km2c_exceptional_divisor_witness

open MMP.Mori

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- `𝒪_Y(nL) ≅ 𝒪_Y(L)^{⊗ n}` for a Cartier divisor `L` and `n ≥ 1`. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {L : Divisor Y} (hL : L.IsCartier) (n : ℕ)
    (hn : 1 ≤ n) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    Nonempty ((n • L).divisorialSheaf ≅
      Stacks.Ample.tensorPowModule Y L.divisorialSheaf (n : ℤ)) := by
  have := hL.isInvertibleModule_divisorialSheaf
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨eqToIso (congrArg Divisor.divisorialSheaf (one_nsmul L)) ≪≫
      (Stacks.Ample.tensorPowModuleOneIso Y _).symm⟩
  | succ n hn ih =>
    obtain ⟨e⟩ := ih
    refine ⟨eqToIso (congrArg Divisor.divisorialSheaf (succ_nsmul L n)) ≪≫
      ((hL.nsmul n).divisorialSheafTensorIso hL).symm ≪≫ ?_ ≪≫
      Stacks.Ample.tensorPowModuleAddIso Y _ (n : ℤ) 1 ≪≫
      Stacks.RelativeVeryAmple.tensorPowModuleCongr Y _ (by push_cast; rfl)⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso Y _).symm

open Opposite RingedSpaceModuleAdjunction Stacks.Ample in
/-- **The zero divisor of a section.** On an integral scheme `Z`, a global section `s` of an
invertible module `M` which does not vanish at some point is a regular section; its zero scheme is
an effective Cartier divisor `I` with `M ≅ 𝒪_Z(I)`, whose support misses the nonvanishing locus
of `s`. -/
private theorem exists_isEffectiveCartierDivisor_of_mem_nonvanishingLocus {Z : Scheme.{u}}
    [IsIntegral Z] (M : Z.Modules) [IsInvertibleModule Z M] (s : Γ(M, ⊤)) {z₀ : Z}
    (hz₀ : z₀ ∈ nonvanishingLocus M s) :
    ∃ I : Z.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor I ∧
      (∀ z ∈ nonvanishingLocus M s, z ∉ I.support) ∧
        Nonempty (M ≅ (Stacks.Divisors.invertibleSheaf' I : Z.Modules)) := by
  have : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M :=
    InvertibleSheafGeneral.isInvertible_of_isInvertibleModule _
  have hne0 : s ≠ 0 := by
    intro h
    rw [h, mem_nonvanishingLocus_iff] at hz₀
    exact hz₀ (by simp)
  have hevaltop : (Stacks.SheafOfModules.sectionsOfTop M s).eval (op ⊤) = s :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ s
  have hne0' : (Stacks.SheafOfModules.sectionsOfTop M s).eval (op ⊤) ≠ 0 := by
    rwa [hevaltop]
  have hreg : IsRegularSection Z.sheaf.obj Z.ringCatSheaf.property
      (Stacks.SheafOfModules.sectionsOfTop M s) :=
    isRegularSection_of_eval_top_ne_zero _ _ hne0'
  have hZc : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroScheme Z M ((Stacks.SheafOfModules.sectionsOfTop M s).eval (op ⊤))) :=
    (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Z _ _).2 hreg
  have hcompl := nonvanishingLocus_eq_compl_supportSet_zeroScheme M _ hne0'
  have hnv : nonvanishingLocus M s =
      (zeroScheme Z M ((Stacks.SheafOfModules.sectionsOfTop M s).eval (op ⊤))).supportSetᶜ := by
    rw [← hcompl]
    conv_lhs => rw [← hevaltop]
    rw [← Stacks.AmplePredicateBridge.coe_nonvanishingOpen_eval Z _
        (Stacks.SheafOfModules.sectionsOfTop M s)]
    rfl
  refine ⟨_, hZc, fun z hz hz' => ?_, ⟨invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg⟩⟩
  rw [hnv] at hz
  exact hz hz'

open RingedSpaceModuleAdjunction Stacks.Ample in
/-- **A section of `𝒪_Y(m)` avoiding finitely many points.** Let `f : Y → S` factor through a
finite `i : Y → ℙⁿ_S`, and let `g : Y → ℙⁿ_ℤ` be the composite with the projection to the
integral model. Since `𝒪(1)` is ample on `ℙⁿ_ℤ`, for a finite set `T ⊆ Y` some section of
`𝒪(m)` (`m ≥ 1`) does not vanish on `g(T)`; its pull-back is a section of `g^*𝒪(m)` not
vanishing on `T`. Over an affine open `V` of `S`, the composite `f⁻¹(V) → ℙⁿ_ℤ` is affine (finite
over `ℙⁿ_V`, which is affine over `ℙⁿ_ℤ`), so `g^*𝒪(m)` is ample on `f⁻¹(V)`:
it is `f`-ample. -/
private theorem exists_isRelativelyAmple_forall_mem_nonvanishingLocus {S W : Scheme.{u}}
    (f : W ⟶ S) (hfg : ∃ (n : ℕ) (i : W ⟶ projectiveSpaceOver n S), IsFinite i ∧
      i ≫ (projectiveSpaceOver n S ↘ S) = f) {T : Set W} (hT : T.Finite) :
    ∃ (M : W.Modules) (_ : IsInvertibleModule W M) (s : Γ(M, ⊤)),
      (∀ y ∈ T, y ∈ nonvanishingLocus M s) ∧ MMP.Mori.IsRelativelyAmple f M := by
  obtain ⟨n, i, hi, rfl⟩ := hfg
  set g := i ≫ projectiveSpaceOver.toIntegralAtUniverse n S with hg
  set L0 := Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n
  have hL0 := Stacks.HProjective.isAmple_twistingSheafAtUniverse n
  obtain ⟨m, hm, s, -, hsE, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L0 hL0
      (hT.image g) ⊤ (by simp)
  have hL1 : IsAmple _ (tensorPowModule _ L0 (m : ℤ)) :=
    Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L0 m hm hL0
  refine ⟨(modulePullback g.toLRSHom.toShHom).obj (tensorPowModule _ L0 (m : ℤ)),
    Stacks.InvertiblePullback.isInvertibleModule_pullback g (tensorPowModule _ L0 (m : ℤ)),
    Stacks.NonvanishingPullback.pullbackGlobalSection g (tensorPowModule _ L0 (m : ℤ)) s,
    fun y hy => ?_, fun x => ?_⟩
  · rw [Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff]
    have := hsE ⟨y, hy, rfl⟩
    rwa [Stacks.AmpleTheory.coe_powNonvanishingOpen] at this
  · obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show x ∈ (⊤ : S.Opens) from trivial)
    refine ⟨V, hV, hxV, ?_⟩
    have := Stacks.HProjective.isAffineHom_preimage_ι_comp_toIntegralAtUniverse n V hV
    have h1 : IsAffineHom ((i ∣_ ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V)) ≫
        ((projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V).ι ≫ projectiveSpaceOver.toIntegralAtUniverse n S) :=
      inferInstance
    rw [morphismRestrict_ι_assoc] at h1
    have h1' : IsAffineHom (((i ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ V).ι ≫ g) := by
      rwa [hg]
    have h2 : IsAmple _ ((modulePullback ((((i ≫ (projectiveSpaceOver n S ↘ S)) ⁻¹ᵁ V).ι ≫
        g)).toLRSHom.toShHom).obj (tensorPowModule _ L0 (m : ℤ))) :=
      Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom _ _ hL1
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Stacks.RelativeVeryAmple.modulePullbackPairIso _ _ _)).mpr h2

open RingedSpaceModuleAdjunction in
/-- **A general section of `𝒪_Y(m)`.** For `f : Y → X` factoring through a finite `Y → ℙᴺ_X`,
every finite set `T` of points of `Y` is avoided by the zero divisor of some section of a
positive power of `𝒪_Y(1)`: an effective `f`-ample Cartier divisor `H` whose support contains
no point of `T` that is the generic point of a prime divisor. -/
private theorem exists_isRelativelyAmple_forall_genericPoint_mem
    (sY : Y ⟶ Spec (.of k)) (hY : IsNormalVariety k sY) (f : Y ⟶ X)
    (hfg : ∃ (n : ℕ) (g : Y ⟶ projectiveSpaceOver n X), IsFinite g ∧
      g ≫ (projectiveSpaceOver n X ↘ X) = f) (T : Set Y) (hT : T.Finite) :
    ∃ (H : Divisor Y) (hH : H.IsCartier), 0 ≤ H ∧ H.IsRelativelyAmple f hH ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, E.genericPoint ∈ T → H E = 0 := by
  have : IsIntegral Y := hY.1.toIsIntegral
  obtain ⟨M, hM, s, hsT, hamp⟩ :=
    exists_isRelativelyAmple_forall_mem_nonvanishingLocus f hfg (hT.insert (genericPoint Y))
  obtain ⟨I, hI, hIs, ⟨eM⟩⟩ := exists_isEffectiveCartierDivisor_of_mem_nonvanishingLocus M s
    (hsT _ (Set.mem_insert _ _))
  obtain ⟨H, hH0, hHc, ⟨eH⟩, hHsupp⟩ :=
    MMP.Threefold.Resolution.exists_divisor_of_isEffectiveCartierDivisor I hI
  refine ⟨H, hHc, hH0, ?_, fun E hE => ?_⟩
  · have := hHc.isInvertibleModule_divisorialSheaf
    rw [Divisor.isRelativelyAmple_iff]
    intro x
    obtain ⟨V, hV, hxV, hVamp⟩ := hamp x
    refine ⟨V, hV, hxV, ?_⟩
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso (eH ≪≫ eM.symm))).mpr hVamp
  · refine le_antisymm (not_lt.mp fun hpos => ?_) (hH0 E)
    exact hIs _ (hsT _ (Set.mem_insert_of_mem _ hE)) (hHsupp E hpos)

/-- The generic point of `Y` lies outside the exceptional set of a proper birational morphism
`f : Y → X`: the fibre of `f` over `η_X` is `{η_Y}`, so `η_X` lies in the finite-fibre locus, over
which `f` is an isomorphism. -/
private theorem genericPoint_notMem_exceptionalSet [IsIntegral Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfP : IsProper f) (hfb : IsBirationalMorphism f) :
    genericPoint Y ∉ (exceptionalSet f : Set Y) := by
  have : IsIntegral X := hX.1.1.toIsIntegral
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sX) := hfs ▸ hY.1.toLocallyOfFiniteType
    exact locallyOfFiniteType_of_comp f sX
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
  have hpre := preimage_genericPoint f hb
  obtain ⟨hU, hiso⟩ :=
    (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1 inferInstance
  have hfη : f (genericPoint Y) = genericPoint X := by
    have : genericPoint Y ∈ f ⁻¹' {genericPoint X} := by rw [hpre]; rfl
    exact this
  intro h
  refine h (le_biregularLocus (V := ⟨_, hU⟩) hiso ?_)
  change (f ⁻¹' {f (genericPoint Y)}).Finite
  rw [hfη, hpre]
  exact Set.finite_singleton _

/-- **The `f`-exceptional prime divisors are finitely many.** Each lies in the proper closed subset
`Ex(f)` and, having codimension one, is an irreducible component of it. -/
private theorem finite_setOf_genericPoint_isExceptional
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfP : IsProper f) (hfb : IsBirationalMorphism f) :
    {y : Y | ∃ E : MMP.Mori.PrimeDivisor Y,
      RationalMap.IsExceptional (X := Y) f.toRationalMap E ∧ E.genericPoint = y}.Finite := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsNoetherian Y := {}
  have hηY := genericPoint_notMem_exceptionalSet sX sY hX hY f hfs hfP hfb
  obtain ⟨S, hirr, hZ⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible
    (exceptionalSet f)
  refine (S.finite_toSet.biUnion fun s _ =>
    (show ({y : Y | IsGenericPoint y (s : Set Y)}).Subsingleton from
      fun a ha b hb => ha.eq hb).finite).subset ?_
  rintro _ ⟨E, hE, rfl⟩
  have hηE : E.genericPoint ∈ (exceptionalSet f : Set Y) :=
    MMP.Positivity.support_subset_exceptionalSet E hE
      (MMP.Flips.primeDivisor_genericPoint_mem_support E)
  rw [hZ, TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at hηE
  simp only [Function.comp_apply, id_eq, Set.iSup_eq_iUnion, Set.mem_iUnion] at hηE
  obtain ⟨s, hs, hηs⟩ := hηE
  have hsZ : (s : Set Y) ⊆ (exceptionalSet f : Set Y) := by
    rw [hZ]
    exact (Finset.le_sup (f := id) hs : s ≤ S.sup id)
  obtain ⟨t, ht⟩ := QuasiSober.sober (hirr ⟨s, hs⟩) s.isClosed
  have hte : t = E.genericPoint := by
    by_contra hne
    have h1 : E.genericPoint < t :=
      lt_of_le_of_ne (ht.specializes hηs) fun h => hne (Inseparable.eq h)
    have h2 : t < genericPoint Y :=
      lt_of_le_of_ne (genericPoint_specializes t)
        fun h => hηY (Inseparable.eq h ▸ hsZ ht.mem)
    have h3 := (Order.coheight_add_one_le h1).trans_eq E.coheight_genericPoint
    have h4 : 1 ≤ Order.coheight t := le_add_self.trans (Order.coheight_add_one_le h2)
    exact absurd ((add_le_add_left h4 1).trans h3) (by decide)
  subst hte
  exact Set.mem_biUnion hs ht

/-- A `ℚ`-factorial variety over `k` is separated over `Spec ℤ`. -/
private theorem isSeparated_terminal (sX : X ⟶ Spec (.of k)) (hX : MMP.Fourfold.IsQFactorial sX) :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  have := hX.1.1
  infer_instance

/-- A point of coheight zero of an integral scheme is its generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {Z : Scheme.{u}} [IsIntegral Z] {x : Z}
    (h : Order.coheight x = 0) : x = genericPoint Z := by
  rw [Order.coheight_eq_zero] at h
  have h2 := h (show x ≤ genericPoint Z from genericPoint_specializes x)
  exact ((genericPoint_specializes x).antisymm h2).eq.symm

/-- **The transform of a non-exceptional prime divisor.** For a birational morphism `f : Y → X` of
normal varieties, a prime divisor `E ⊆ Y` which is not `f`-exceptional is mapped onto a prime
divisor: `f(η_E) = η_P` for some prime divisor `P ⊆ X`. -/
private theorem exists_map_genericPoint_eq_of_not_isExceptional
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfb : IsBirationalMorphism f) [LocallyOfFiniteType f]
    (E : MMP.Mori.PrimeDivisor Y)
    (hE : ¬ RationalMap.IsExceptional (X := Y) f.toRationalMap E) :
    ∃ P : MMP.Mori.PrimeDivisor X, f E.genericPoint = P.genericPoint := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsIntegral X := hX.1.1.toIsIntegral
  have := isSeparated_terminal sX hX
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight] at hE
  push Not at hE
  obtain ⟨x, hx, hlt⟩ := hE
  have hηx : f E.genericPoint ⤳ x := by
    have hsub : (TopologicalSpace.Closeds.closure (f '' (E.idealSheaf.support : Set Y)) : Set X) ⊆
        closure {f E.genericPoint} := by
      rw [TopologicalSpace.Closeds.coe_closure]
      refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨y, hy, rfl⟩
      have hsp : E.genericPoint ⤳ y := specializes_iff_mem_closure.mpr (by
        rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
      exact (hsp.map f.continuous).mem_closure
    exact specializes_iff_mem_closure.mpr (hsub hx)
  have hle : Order.coheight (f E.genericPoint) ≤ 1 := by
    have h1 : Order.coheight x ≤ 1 := by
      rw [← one_add_one_eq_two] at hlt
      exact Order.le_of_lt_add_one hlt
    exact (Order.coheight_anti (α := X) (show x ≤ f E.genericPoint from hηx)).trans h1
  have hco : Order.coheight (f E.genericPoint) = 1 := by
    refine le_antisymm hle (Order.one_le_iff_ne_zero.mpr fun h0 => ?_)
    have h2 : E.genericPoint ∈ f ⁻¹' {genericPoint X} := eq_genericPoint_of_coheight_eq_zero h0
    rw [preimage_genericPoint f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)] at h2
    have h3 := E.coheight_genericPoint
    rw [show E.genericPoint = genericPoint Y from h2,
      Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z] at h3
    exact zero_ne_one h3
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective. -/
private theorem nonneg_of_isPullback {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) : 0 ≤ B := by
  have hm := QDivisor.cartierIndex_pos hAq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hAq
  obtain ⟨D', hD', hp⟩ := h _ hm D₀ hD₀ hD₀c
  have hmq : (0 : ℚ) < (A.cartierIndex hAq : ℚ) := by exact_mod_cast hm
  have hD₀n : ∀ P : MMP.Mori.PrimeDivisor X, (P.support ∩ (⊤ : X.Opens)).Nonempty →
      0 ≤ D₀.coeff P := by
    intro P _
    have h2 : (D₀ P : ℚ) = A.cartierIndex hAq * A P :=
      (by simpa using congrArg (· P) hD₀ :
        Divisor.toQDivisor D₀ P = A.cartierIndex hAq * A P)
    exact_mod_cast h2 ▸ mul_nonneg hmq.le (hA P)
  intro E
  have hE : (E.support ∩ f ⁻¹ᵁ (⊤ : X.Opens)).Nonempty :=
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  have h0 := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c hD₀n hp E hE
  have h1 : (D' E : ℚ) = A.cartierIndex hAq * B E :=
    (by simpa using congrArg (· E) hD' :
      Divisor.toQDivisor D' E = A.cartierIndex hAq * B E)
  have h0' : (0 : ℚ) ≤ (D' E : ℚ) := by exact_mod_cast h0
  exact nonneg_of_mul_nonneg_right (h1 ▸ h0') hmq

/-- **The defect `F`.** If `H ≥ 0` has no `f`-exceptional component, then `f^*(f_*H) - H` is
effective and supported on `f`-exceptional divisors: a non-exceptional prime `P` has the valuation
of `f_*P`, and on an exceptional `E` the pull-back of the effective `f_*H` is `≥ 0`. -/
private theorem nonneg_sub_and_isExceptional_of_isPullback
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfP : IsProper f) (hfb : IsBirationalMorphism f)
    (H : Divisor Y) (hH0 : 0 ≤ H)
    (hHE : ∀ E : MMP.Mori.PrimeDivisor Y,
      RationalMap.IsExceptional (X := Y) f.toRationalMap E → H E = 0)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
      (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)).supp)
    (B' : QDivisor Y)
    (hB' : (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)).IsPullback
      f hB B') :
    0 ≤ B' - Divisor.toQDivisor H ∧
      ∀ E : MMP.Mori.PrimeDivisor Y, (B' - Divisor.toQDivisor H) E ≠ 0 →
        RationalMap.IsExceptional (X := Y) f.toRationalMap E := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have hY': IsNormalVariety k (f ≫ sX) := hfs ▸ hY
  set B := Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)
  have hBq : B.IsQCartier := MMP.Fourfold.isQCartier_of_isQFactorial sX hX B
  have htr := MMP.Positivity.transformDivisor_of_isPullback hX.1 hY' hfb hBq hB hB'
  -- the coefficient of a non-exceptional `E` in `f^*(f_*H)` is that of `E` in `H`
  have key : ∀ E : MMP.Mori.PrimeDivisor Y,
      ¬ RationalMap.IsExceptional (X := Y) f.toRationalMap E → B' E = (H E : ℚ) := by
    intro E hE
    obtain ⟨P, hP⟩ :=
      exists_map_genericPoint_eq_of_not_isExceptional sX sY hX hY f hfb E hE
    obtain ⟨E', -, -, hE'⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX.1 hY' hfb P
    have := isSeparated_terminal sX hX
    have hEP := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E P).mpr hP
    have hEE' : E' = E := by
      by_contra hne
      have h1 := hE' (Finsupp.single E (1 : ℤ))
      rw [RationalMap.transformDivisor_single_of_eq_some hEP] at h1
      simp [Ne.symm hne] at h1
    subst hEE'
    have h1 : RationalMap.transformDivisor (X := Y) f.toRationalMap B' P = B P := by rw [htr]
    rw [hE' B'] at h1
    rw [h1]
    change ((RationalMap.transformDivisor (X := Y) f.toRationalMap H) P : ℚ) = _
    rw [hE' H]
  refine ⟨fun E => ?_, fun E hE => ?_⟩
  · by_cases hEx : RationalMap.IsExceptional (X := Y) f.toRationalMap E
    · have hB0 : 0 ≤ B := by
        intro P
        obtain ⟨E', -, -, hE'⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hX.1 hY' hfb P
        change (0 : ℚ) ≤ ((RationalMap.transformDivisor (X := Y) f.toRationalMap H) P : ℚ)
        rw [hE' H]
        exact_mod_cast hH0 E'
      have := nonneg_of_isPullback hB0 hBq hB'
      rw [Finsupp.sub_apply, show (Divisor.toQDivisor H) E = (H E : ℚ) from rfl, hHE E hEx]
      simpa using this E
    · rw [Finsupp.sub_apply, key E hEx]
      exact le_of_eq (sub_self _).symm
  · by_contra hEx
    exact hE (by rw [Finsupp.sub_apply, key E hEx]; exact sub_self _)

/-- **An `f`-ample divisor without exceptional components** (Kollár–Mori, proof of 2.62), for
`f` proper and finite over some `ℙⁿ_X`
(`MMP.Mori.exists_isRelativelyAmple_isPullback_transformDivisor_eq_add` is the projective
case, and the composite of a projective morphism with a normalization is of this form). -/
private theorem exists_isRelativelyAmple_isPullback_of_isFinite
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY) (hfP : IsProper f)
    (hfg : ∃ (n : ℕ) (g : Y ⟶ projectiveSpaceOver n X), IsFinite g ∧
      g ≫ (projectiveSpaceOver n X ↘ X) = f) (hfb : IsBirationalMorphism f) :
    ∃ (H : Divisor Y) (hH : H.IsCartier) (F : QDivisor Y),
      0 ≤ H ∧ H.IsRelativelyAmple f hH ∧
      (∀ E : MMP.Mori.PrimeDivisor Y,
        RationalMap.IsExceptional (X := Y) f.toRationalMap E → H E = 0) ∧
      0 ≤ F ∧
      (∀ E : MMP.Mori.PrimeDivisor Y, F E ≠ 0 →
        RationalMap.IsExceptional (X := Y) f.toRationalMap E) ∧
      ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)).supp,
        (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)).IsPullback
          f hB (Divisor.toQDivisor H + F) := by
  obtain ⟨H, hH, hH0, hHamp, hHT⟩ := exists_isRelativelyAmple_forall_genericPoint_mem sY hY f hfg _
    (finite_setOf_genericPoint_isExceptional sX sY hX hY f hfs hfP hfb)
  have hHE : ∀ E : MMP.Mori.PrimeDivisor Y,
      RationalMap.IsExceptional (X := Y) f.toRationalMap E → H E = 0 :=
    fun E hE => hHT E ⟨E, hE, rfl⟩
  set B := Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)
  have : IsIntegral Y := hY.1.toIsIntegral
  have := hfb.isDominant
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f B
  obtain ⟨B', hB'⟩ :=
    ((MMP.Fourfold.isQCartier_of_isQFactorial sX hX B).existsUnique_isPullback hB).exists
  obtain ⟨hF0, hFE⟩ :=
    nonneg_sub_and_isExceptional_of_isPullback sX sY hX hY f hfs hfP hfb H hH0 hHE hB B' hB'
  refine ⟨H, hH, B' - Divisor.toQDivisor H, hH0, hHamp, hHE, hF0, hFE, hB, ?_⟩
  rwa [add_sub_cancel]

open RingedSpaceModuleAdjunction in
/-- A positive multiple of an `f`-ample Cartier divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Y} {L : Divisor X} (hL : L.IsCartier)
    (h : L.IsRelativelyAmple f hL) (n : ℕ) (hn : 0 < n) :
    (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  have := hL.isInvertibleModule_divisorialSheaf
  have := (hL.nsmul n).isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, hA⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  obtain ⟨e0⟩ := nonempty_divisorialSheaf_nsmul_iso hL n hn
  have := Stacks.Ample.isInvertibleModule_tensorPowModule (f ⁻¹ᵁ V).toScheme
    ((modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L.divisorialSheaf) (n : ℤ)
  let e := (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e0 ≪≫
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι _ n
  rw [Stacks.RelativeVeryAmple.isAmple_congr _ _ e]
  exact (Stacks.AmplePositivePower.isAmple_iff_isAmple_tensorPowModule _ n hn).1 hA

/-- **An effective exceptional divisor whose negative is relatively ample** (Kollár–Mori 2.62),
for `f` proper and finite over some `ℙⁿ_X`
(`MMP.Mori.exists_isRelativelyAmple_neg_smul_of_isExceptional` is the projective case). -/
private theorem exists_isRelativelyAmple_neg_of_isFinite
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY) (hfP : IsProper f)
    (hfg : ∃ (n : ℕ) (g : Y ⟶ projectiveSpaceOver n X), IsFinite g ∧
      g ≫ (projectiveSpaceOver n X ↘ X) = f) (hfb : IsBirationalMorphism f) :
    ∃ (F : QDivisor Y) (e : ℕ), 0 < e ∧ 0 ≤ F ∧
      (∀ E : MMP.Mori.PrimeDivisor Y, F E ≠ 0 →
        RationalMap.IsExceptional (X := Y) f.toRationalMap E) ∧
      ∃ (D : Divisor Y) (hD : D.IsCartier),
        Divisor.toQDivisor D = (e : ℚ) • F ∧ (-D).IsRelativelyAmple f hD.neg := by
  obtain ⟨H, hH, F, -, hHamp, -, hF0, hFexc, hB, hpb⟩ :=
    exists_isRelativelyAmple_isPullback_of_isFinite sX sY hX hY f hfs hfP hfg hfb
  obtain ⟨e, he, D₀, hD₀, hD₀c⟩ :=
    (MMP.Fourfold.isQCartier_of_isQFactorial sX hX
      (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H))).exists_pos
  obtain ⟨D', hD', hD'pb⟩ := hpb e he D₀ hD₀ hD₀c
  have hD'c : D'.IsCartier := hD'pb.isCartier hD₀c
  refine ⟨F, e, he, hF0, hFexc, D' - e • H, hD'c.sub (hH.nsmul e), ?_, ?_⟩
  · rw [map_sub, map_nsmul, hD', smul_add, natCast_zsmul, natCast_zsmul, add_sub_cancel_left,
      Nat.cast_smul_eq_nsmul]
  · have hneg := hD'pb.zsmul hD₀c (-1) (fun Z hZ => hB Z (by
      rwa [← Divisor.supp_toQDivisor, map_zsmul, QDivisor.supp_zsmul (by norm_num),
        Divisor.supp_toQDivisor,
        QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast he.ne') hD₀] at hZ))
    have := MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback f (hH.nsmul e)
      (isRelativelyAmple_nsmul hH hHamp e he) (hD₀c.zsmul (-1)) hneg (hD'c.zsmul (-1))
    convert this using 1
    simp only [neg_smul, one_smul]
    abel

/-- A projective morphism factors through a finite morphism to some `ℙⁿ`: its closed
immersion. -/
private theorem exists_isFinite_of_isProjectiveMorphism {S W : Scheme.{u}} {f : W ⟶ S}
    (hf : IsProjectiveMorphism f) : ∃ (n : ℕ) (i : W ⟶ projectiveSpaceOver n S), IsFinite i ∧
      i ≫ (projectiveSpaceOver n S ↘ S) = f := by
  obtain ⟨n, i, hi, hif⟩ := hf
  exact ⟨n, i, inferInstance, hif⟩

end Proof_lem_km2c_exceptional_divisor_witness

namespace MMP.Mori

open Proof_lem_km2c_exceptional_divisor_witness in
/-- **An `f`-ample divisor without exceptional components** (Kollár–Mori, proof of 2.62).
Let `f : Y ⟶ X` be a projective birational morphism of normal varieties over `k`, with `X`
`ℚ`-factorial. There are an effective Cartier divisor `H` on `Y` with `𝒪_Y(H)` `f`-ample and no
`f`-exceptional component, and an effective `ℚ`-divisor `F` on `Y` whose components are all
`f`-exceptional, such that `f^*(f_*H) = H + F`. -/
@[mmp "lem_km2c_exceptional_divisor_witness"]
public theorem exists_isRelativelyAmple_isPullback_transformDivisor_eq_add
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) :
    ∃ (H : Divisor Y) (hH : H.IsCartier) (F : QDivisor Y),
      0 ≤ H ∧ H.IsRelativelyAmple f hH ∧
      (∀ E : PrimeDivisor Y, RationalMap.IsExceptional (X := Y) f.toRationalMap E → H E = 0) ∧
      0 ≤ F ∧
      (∀ E : PrimeDivisor Y, F E ≠ 0 → RationalMap.IsExceptional (X := Y) f.toRationalMap E) ∧
      ∃ hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉
          (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)).supp,
        (Divisor.toQDivisor (RationalMap.transformDivisor (X := Y) f.toRationalMap H)).IsPullback
          f hB (Divisor.toQDivisor H + F) :=
  exists_isRelativelyAmple_isPullback_of_isFinite sX sY hX hY f hfs
    (isProper_of_isProjectiveMorphism f hfp) (exists_isFinite_of_isProjectiveMorphism hfp) hfb

open Proof_lem_km2c_exceptional_divisor_witness in
/-- **An effective exceptional divisor whose negative is relatively ample** (Kollár–Mori 2.62).
Let `f : Y ⟶ X` be a projective birational morphism of normal varieties over `k`, with `X`
`ℚ`-factorial. There are an effective `ℚ`-divisor `F` on `Y` whose components are all
`f`-exceptional, and `e > 0`, such that `eF` is a Cartier divisor `D` and `𝒪_Y(-D)` is
`f`-ample. -/
@[mmp "lem_km2c_exists_antiample_exceptional"]
public theorem exists_isRelativelyAmple_neg_smul_of_isExceptional
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) :
    ∃ (F : QDivisor Y) (e : ℕ), 0 < e ∧ 0 ≤ F ∧
      (∀ E : PrimeDivisor Y, F E ≠ 0 → RationalMap.IsExceptional (X := Y) f.toRationalMap E) ∧
      ∃ (D : Divisor Y) (hD : D.IsCartier),
        Divisor.toQDivisor D = (e : ℚ) • F ∧ (-D).IsRelativelyAmple f hD.neg :=
  exists_isRelativelyAmple_neg_of_isFinite sX sY hX hY f hfs
    (isProper_of_isProjectiveMorphism f hfp) (exists_isFinite_of_isProjectiveMorphism hfp) hfb

end MMP.Mori

namespace Proof_lem_km2c_finite_cover_cohomology_summand

open MonoidalCategory

/-- For a finite surjective `π : Y ⟶ X` of varieties in characteristic zero with `X` normal,
a quasi-coherent `F` is a retract of `π_* π^* F`, through the unit of the adjunction. -/
private theorem nonempty_retract_pushforward_pullback
    (k : Type u) [Field k] [CharZero k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsVariety k f] [IsVariety k g] [IsNormal X]
    (π : Y ⟶ X) [IsFinite π] [Surjective π] (hπ : π ≫ f = g)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (Retract F
      ((Scheme.Modules.pushforward π).obj ((Scheme.Modules.pullback π).obj F))) := by
  letI : MonoidalCategory X.Modules := Stacks.SheafOfModules.Strict.monoidalCategory
    X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
  obtain ⟨τ, hτ⟩ := MMP.Mori.exists_unitToPushforwardObjUnit_comp_eq_id f g π hπ
  obtain ⟨e, -⟩ := MMP.Modules.exists_pushforward_pullback_iso_tensor_unit π F
  let W : Retract (F ⊗ 𝟙_ X.Modules)
      (F ⊗ (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
    { i := F ◁ SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom
      r := F ◁ τ
      retract := (MonoidalCategory.whiskerLeft_comp F _ τ).symm.trans
        ((congrArg (F ◁ ·) hτ).trans (MonoidalCategory.whiskerLeft_id F _)) }
  exact ⟨((ρ_ F).symm.retract.trans W).trans e.retract⟩

end Proof_lem_km2c_finite_cover_cohomology_summand

namespace MMP.Mori

open Proof_lem_km2c_finite_cover_cohomology_summand in
/-- Let `π : Y ⟶ X` be a finite surjective morphism of varieties over a field `k` of
characteristic zero, with `X` normal, and let `ℱ` be a quasi-coherent sheaf on `X`. Then
`H^i(X, ℱ)` is a retract of `H^i(Y, π^* ℱ)` as a `k`-vector space for every `i`. In particular
`H^i(Y, π^* ℱ) = 0` implies `H^i(X, ℱ) = 0`. -/
@[mmp "lem_km2c_finite_cover_cohomology_summand"]
public theorem nonempty_retract_cohomologyOverField_pullback_of_isFinite
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsVariety k f] [IsVariety k g] [IsNormal X]
    (π : Y ⟶ X) [IsFinite π] [Surjective π] (hπ : π ≫ f = g)
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    Nonempty (Retract (cohomologyOverField k f F i)
      (cohomologyOverField k g ((Scheme.Modules.pullback π).obj F) i)) := by
  obtain ⟨R⟩ := nonempty_retract_pushforward_pullback k f g π hπ F
  subst hπ
  exact ⟨(R.map (cohomologyOverFieldFunctor k f i)).trans
    (cohomologyOverFieldPushforwardIsoOfIsAffineHom k π f _ i).symm.retract⟩

end MMP.Mori

namespace Proof_lem_km2c_reflexive_power_reflexive

open Stacks.AlgebraicGeometry

/-- Every tensor power `L^{⊗ n}`, `n ≥ 0`, of a coherent module is coherent. -/
private lemma isCoherent_tensorPower {X : Scheme.{u}} [IsLocallyNoetherian X] (L : X.Modules)
    [SheafOfModules.IsCoherent L] :
    ∀ n : ℕ, SheafOfModules.IsCoherent (ReflexivePowers.tensorPower L n)
  | 0 => CoherentTFAE.isCoherent_unit X
  | n + 1 => ReflexivePowers.isCoherent_tensorPower L inferInstance n

end Proof_lem_km2c_reflexive_power_reflexive

namespace MMP.Mori

open Stacks.AlgebraicGeometry.ReflexiveModules Proof_lem_km2c_reflexive_power_reflexive in
/-- For a coherent torsion-free sheaf `L` of rank one on a normal variety, every reflexive power
`L^{[i]}`, `i : ℤ`, is a reflexive coherent sheaf. -/
@[mmp "lem_km2c_reflexive_power_reflexive"]
public theorem isCoherent_reflexivePow_and_isReflexive (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k f] [IsNormal X]
    (L : X.Modules) [SheafOfModules.IsCoherent L] (hL : IsTorsionFree L)
    (hrank : Scheme.Modules.fiberRank L (genericPoint X) = 1) (i : ℤ) :
    SheafOfModules.IsCoherent (reflexivePow L i) ∧ IsReflexive (reflexivePow L i) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdual := Stacks.AlgebraicGeometry.InternalHomLocalKernel.isCoherent_dualSheaf (X := X)
  have H :=
    Stacks.AlgebraicGeometry.ReflexiveStalkCriterion.isCoherent_and_isReflexive_dualSheaf hdual
  cases i with
  | ofNat n => exact H _ (hdual _ (isCoherent_tensorPower L n))
  | negSucc n => exact H _ (hdual _ (hdual _ (isCoherent_tensorPower L (n + 1))))

end MMP.Mori

namespace Proof_lem_km2c_reflexive_power_unique

open MMP.Mori Stacks.AlgebraicGeometry.ReflexiveModules

/-- **Reflexive Hartogs, objectwise.** If the complement of an open `U` of an integral locally
noetherian scheme has structure-sheaf depth at least two, two coherent reflexive modules whose
restrictions to `U` are isomorphic are isomorphic. -/
private lemma nonempty_iso_of_restrict_iso {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    {F G : X.Modules} (hF : F.IsCoherent ∧ IsReflexive F) (hG : G.IsCoherent ∧ IsReflexive G)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj F ≅
      (Scheme.Modules.restrictFunctor U.ι).obj G) :
    Nonempty (F ≅ G) := by
  obtain ⟨E, φ, -⟩ := reflexiveCoherentEquivalence X U hdepth
  let F' : ReflexiveCoherentModules X := ⟨F, hF⟩
  let G' : ReflexiveCoherentModules X := ⟨G, hG⟩
  let ρ := Scheme.Modules.restrictFunctorIsoPullback U.ι
  let β : (E.functor.obj F').obj ≅ (E.functor.obj G').obj :=
    φ.app F' ≪≫ (ρ.app F).symm ≪≫ e ≪≫ ρ.app G ≪≫ (φ.app G').symm
  exact ⟨(ObjectProperty.ι _).mapIso
    (E.fullyFaithfulFunctor.preimageIso ((ObjectProperty.fullyFaithfulι _).preimageIso β))⟩

end Proof_lem_km2c_reflexive_power_unique

namespace MMP.Mori

open Stacks.AlgebraicGeometry.ReflexiveModules Proof_lem_km2c_reflexive_power_unique in
/-- On a normal variety, a reflexive coherent sheaf `𝒢` whose restriction to the locally free
locus `X⁰` of a coherent torsion-free rank-one sheaf `L` is isomorphic to `(L|_{X⁰})^{⊗ i}` is
isomorphic to the reflexive power `L^{[i]}`. -/
@[mmp "lem_km2c_reflexive_power_unique"]
public theorem nonempty_iso_reflexivePow_of_isReflexive (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k f] [IsNormal X]
    (L : X.Modules) [SheafOfModules.IsCoherent L] (hL : IsTorsionFree L)
    (hrank : Scheme.Modules.fiberRank L (genericPoint X) = 1)
    (G : X.Modules) [SheafOfModules.IsCoherent G] (hG : IsReflexive G) (i : ℤ)
    (e : (Scheme.Modules.restrictFunctor (locallyFreeLocus L).ι).obj G ≅
      MMP.Intersection.Scheme.Modules.tensorZPow
        ((Scheme.Modules.restrictFunctor (locallyFreeLocus L).ι).obj L) i) :
    Nonempty (G ≅ reflexivePow L i) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨α⟩ := nonempty_restrict_reflexivePow_iso_tensorZPow k f L hL hrank i
  exact nonempty_iso_of_restrict_iso _
    (fun x hx => two_le_depth_stalk_of_two_le_coheight x
      (two_le_coheight_of_notMem_locallyFreeLocus ⟨‹_›, ‹_›⟩ L
        (Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent ‹_›) hL hrank hx))
    ⟨‹_›, hG⟩
    (isCoherent_reflexivePow_and_isReflexive k f L hL hrank i) (e ≪≫ α.symm)

end MMP.Mori

namespace Proof_lem_km2c_snc_criterion

open Order

/-- A closed immersion preserves heights in the specialization order. -/
private lemma height_eq_height_base {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (x : X) : height x = height (f.base x) := by
  have hemb := f.isClosedEmbedding
  have hle : ∀ a b : X, f.base a ≤ f.base b ↔ a ≤ b := fun a b => by
    rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes, hemb.isInducing.specializes_iff]
  have hmono : StrictMono f.base := fun a b hab =>
    lt_of_le_not_ge ((hle a b).2 hab.le) fun h => hab.not_ge ((hle b a).1 h)
  refine height_eq_of_strictMono _ hmono (fun a b hb => ?_) x
  obtain ⟨a', rfl⟩ : b ∈ Set.range f.base := by
    have hb' : b ∈ closure {f.base a} :=
      specializes_iff_mem_closure.mp (Scheme.le_iff_specializes.mp hb.le)
    exact closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_range_self a))
      hemb.isClosed_range hb'
  exact ⟨a', lt_of_le_not_ge ((hle a' a).1 hb.le) fun h => hb.not_ge ((hle a a').2 h), rfl⟩

private lemma eq_natCast_sub_and_le_of_add_eq {d : WithBot ℕ∞} {r n : ℕ} (h : d + r = n) :
    d = ((n - r : ℕ) : WithBot ℕ∞) ∧ r ≤ n := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have : ((⊤ : ℕ∞) + r : ℕ∞) = n := by exact_mod_cast h
      simp at this
    | coe e =>
      have : e + r = n := by exact_mod_cast h
      refine ⟨?_, by omega⟩
      rw [show e = n - r by omega]; rfl

private lemma add_le_of_add_le_sub {a b r n : ℕ} {c : ℕ∞}
    (h : ((a : ℕ∞) : WithBot ℕ∞) + (c : WithBot ℕ∞) ≤ ((n - r : ℕ) : WithBot ℕ∞))
    (hab : a + b = n) (hrn : r ≤ n) : (c : WithBot ℕ∞) + r ≤ ((b : ℕ∞) : WithBot ℕ∞) := by
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by norm_cast)
  | coe c =>
    have h2 : (((a + c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((n - r : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      push_cast; exact h
    have : a + c ≤ n - r := Nat.cast_le.mp (WithBot.coe_le_coe.mp h2)
    have h4 : (((c + r : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((b : ℕ) : ℕ∞) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr (Nat.cast_le.mpr (by omega))
    exact_mod_cast h4

/-- If height and coheight add up to `n` at every point of `Y`, and every irreducible component of
`X` has dimension `n - r`, then a closed immersion `X → Y` raises coheights by at least `r`. -/
private lemma coheight_add_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] {n r : ℕ}
    (hY : ∀ y : Y, height y + coheight y = n)
    (hX : ∀ C ∈ irreducibleComponents (Set.univ : Set X), topologicalKrullDim C + r = n)
    (x : X) : (coheight x : WithBot ℕ∞) + r ≤ coheight (f.base x) := by
  have hrn : r ≤ n := by
    obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      ({⟨x, trivial⟩} : Set (Set.univ : Set X)) isIrreducible_singleton
    exact (eq_natCast_sub_and_le_of_add_eq (hX C hC)).2
  have hdimX : topologicalKrullDim X ≤ ((n - r : ℕ) : WithBot ℕ∞) := by
    rw [← (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq]
    exact MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
      fun C hC => (eq_natCast_sub_and_le_of_add_eq (hX C hC)).1.le
  have h1 := height_add_coheight_le_krullDim x
  rw [(krullDim_eq_of_orderIso irreducibleSetEquivPoints).symm, height_eq_height_base f x] at h1
  have h2 := hY (f.base x)
  have hfin : height (f.base x) ≠ ⊤ := fun ht => by simp [ht] at h2
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin
  have hc : coheight (f.base x) ≠ ⊤ := fun ht => by simp [ht] at h2
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hc
  rw [← ha, ← hb] at h2
  rw [← ha] at h1
  rw [← hb]
  exact add_le_of_add_le_sub (h1.trans hdimX) (by exact_mod_cast h2) hrn

/-- An effective Cartier divisor has a local equation at every point. -/
private lemma exists_stalk_eq_span_singleton {Y : Scheme.{u}} (I : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor I] (y : Y) :
    ∃ g : Y.presheaf.stalk y, IdealSheafData.stalk I y = Ideal.span {g} := by
  obtain ⟨V, hyV, f, -, hf⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpen_isRegular I inferInstance y
  refine ⟨Y.presheaf.germ V y hyV f, ?_⟩
  rw [IdealSheafData.stalk_eq_map_germ _ y V hyV, hf, Ideal.map_span, Set.image_singleton]

/-- Off the support of `I`, the length of `𝒪_{Y,x} / I_x` vanishes. -/
private lemma length_stalk_quotient_eq_zero {Y : Scheme.{u}} (I : Y.IdealSheafData) {x : Y}
    (hx : x ∉ I.support) :
    ((Module.length (Y.presheaf.stalk x)
      (Y.presheaf.stalk x ⧸ IdealSheafData.stalk I x)).toNat : ℤ) = 0 := by
  rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mpr hx]
  have : Subsingleton (Y.presheaf.stalk x ⧸ (⊤ : Ideal (Y.presheaf.stalk x))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Module.length_eq_zero]; rfl

/-- Let `g j` be local equations at `y` of the divisors `G j` through `y`. If every non-empty
intersection `⋂_{j ∈ J} G_j` is smooth of pure codimension `|J|`, then `𝒪_{Y,y} / (g j)` is regular
of dimension `dim 𝒪_{Y,y} - #{j | y ∈ G_j}`. -/
private lemma isRegularLocalRing_quotient_and_add_eq (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) [Smooth sY] (n : ℕ)
    (hdim : topologicalKrullDim Y = n) {ι : Type*} [Finite ι] (G : ι → Y.IdealSheafData)
    (hG : ∀ J : Finset ι, J.Nonempty →
      IsEmpty (⨆ j ∈ J, G j).subscheme ∨
        (Smooth ((⨆ j ∈ J, G j).subschemeι ≫ sY) ∧
          ∀ C ∈ irreducibleComponents (Set.univ : Set (⨆ j ∈ J, G j).subscheme),
            topologicalKrullDim C + J.card = n))
    (y : Y) (g : {j : ι // y ∈ (G j).support} → Y.presheaf.stalk y)
    (hg : ∀ j, IdealSheafData.stalk (G j.1) y = Ideal.span {g j}) :
    IsRegularLocalRing (Y.presheaf.stalk y ⧸ Ideal.span (Set.range g)) ∧
      ringKrullDim (Y.presheaf.stalk y ⧸ Ideal.span (Set.range g)) +
          Nat.card {j : ι // y ∈ (G j).support} = ringKrullDim (Y.presheaf.stalk y) := by
  have := Fintype.ofFinite ι
  classical
  rw [Nat.card_eq_fintype_card]
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := isRegularLocalRing_stalk_of_smooth_over_field sY y
  have hspan_le : Ideal.span (Set.range g) ≤ IsLocalRing.maximalIdeal _ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hne : IdealSheafData.stalk (G j.1) y ≠ ⊤ := fun htop =>
      ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mp htop) j.2
    exact IsLocalRing.le_maximalIdeal hne ((hg j).ge (Ideal.mem_span_singleton_self _))
  have hge : ringKrullDim (Y.presheaf.stalk y) ≤
      ringKrullDim (Y.presheaf.stalk y ⧸ Ideal.span (Set.range g)) +
        Fintype.card {j : ι // y ∈ (G j).support} := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range g) ?_).trans ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact Ideal.span_le.mp hspan_le
    · gcongr
      rw [← Set.image_univ]
      exact_mod_cast (Set.encard_image_le g Set.univ).trans (by simp)
  by_cases hT : IsEmpty {j : ι // y ∈ (G j).support}
  · rw [Ideal.span_eq_bot.mpr (by rintro _ ⟨j, -⟩; exact (hT.false j).elim), Fintype.card_eq_zero]
    exact ⟨.of_ringEquiv (RingEquiv.quotientBot _).symm, by
      rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), Nat.cast_zero, add_zero]⟩
  rw [not_isEmpty_iff] at hT
  set J := Finset.univ.filter fun j => y ∈ (G j).support
  have hmemJ : ∀ j, j ∈ J ↔ y ∈ (G j).support := fun j => by simp [J]
  have hJ : J.Nonempty := let ⟨j⟩ := hT; ⟨j.1, (hmemJ _).mpr j.2⟩
  set F := ⨆ j ∈ J, G j with hFdef
  have hFy : IdealSheafData.stalk F y = Ideal.span (Set.range g) := by
    rw [hFdef, iSup_subtype', MMP.Resolution.stalk_iSup]
    refine le_antisymm (iSup_le fun j => ?_) (Ideal.span_le.mpr ?_)
    · rw [hg ⟨j.1, (hmemJ j.1).mp j.2⟩, Ideal.span_singleton_le_iff_mem]
      exact Ideal.subset_span (Set.mem_range_self _)
    · rintro _ ⟨j, rfl⟩
      refine Ideal.mem_iSup_of_mem ⟨j.1, (hmemJ _).mpr j.2⟩ ?_
      rw [hg j]
      exact Ideal.mem_span_singleton_self _
  have hyF : y ∈ F.support := by
    by_contra hn
    have htop := (Stacks.Divisors.stalk_eq_top_iff_notMem_support F y).mpr hn
    rw [hFy] at htop
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ hspan_le))
  obtain ⟨w, hw⟩ : y ∈ Set.range F.subschemeι := by rwa [F.range_subschemeι]
  obtain ⟨hsm, hcomp⟩ := (hG J hJ).resolve_left fun h0 => h0.false w
  have : LocallyOfFinitePresentation (F.subschemeι ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := F.subschemeι ≫ sY)).mpr
      inferInstance
  have hreg := MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_stalk sY F
    ((MMP.Mori.isSmoothScheme_iff _).2 hsm) hyF
  rw [hFy] at hreg
  refine ⟨hreg, le_antisymm ?_ hge⟩
  -- the dimension bound comes from the purity of `⋂_{j ∈ J} G_j`
  rw [show J.card = Fintype.card {j : ι // y ∈ (G j).support} by
    simp [J, Fintype.card_subtype]] at hcomp
  generalize Fintype.card {j : ι // y ∈ (G j).support} = r at hcomp ⊢
  let : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : IsIntegral Y := hY.toIsIntegral
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have hpure : MMP.Intersection.IsPureDimensional Y n := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rwa [(Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq]
  rw [← hFy, ← hw, ringKrullDim_eq_of_ringEquiv
    (MMP.Flips.ResolutionInputs.stalkQuotientEquiv F w), ringKrullDim_stalk_eq_coheight,
    ringKrullDim_stalk_eq_coheight]
  exact coheight_add_le F.subschemeι
    (MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure) hcomp w

/-- The local equations at `y` of the divisors `G j` through `y` are distinct members of a regular
system of parameters of `𝒪_{Y,y}`. -/
private lemma exists_isRegularSystemOfParameters (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) [Smooth sY] (n : ℕ)
    (hdim : topologicalKrullDim Y = n) {ι : Type*} [Finite ι] (G : ι → Y.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (G j)]
    (hG : ∀ J : Finset ι, J.Nonempty →
      IsEmpty (⨆ j ∈ J, G j).subscheme ∨
        (Smooth ((⨆ j ∈ J, G j).subschemeι ≫ sY) ∧
          ∀ C ∈ irreducibleComponents (Set.univ : Set (⨆ j ∈ J, G j).subscheme),
            topologicalKrullDim C + J.card = n))
    (y : Y) : ∃ (m : ℕ) (z : Fin m → Y.presheaf.stalk y)
      (ι' : {j : ι // y ∈ (G j).support} → Fin m),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective ι' ∧
        ∀ j, IdealSheafData.stalk (G j.1) y = Ideal.span {z (ι' j)} := by
  have := Fintype.ofFinite ι
  classical
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have := isRegularLocalRing_stalk_of_smooth_over_field sY y
  choose g hg using fun j : {j : ι // y ∈ (G j).support} => exists_stalk_eq_span_singleton (G j.1) y
  set e := Fintype.equivFin {j : ι // y ∈ (G j).support}
  have hreg := isRegularLocalRing_quotient_and_add_eq k sY hY n hdim G hG y g hg
  rw [← e.symm.surjective.range_comp g, Nat.card_eq_fintype_card] at hreg
  obtain ⟨mt, t, ht⟩ :=
    (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff (g ∘ e.symm)).mp hreg
  refine ⟨_, Fin.append (g ∘ e.symm) t, fun j => Fin.castAdd mt (e j), ht,
    fun j j' hjj' => e.injective (Fin.castAdd_injective _ _ hjj'), fun j => ?_⟩
  rw [Fin.append_left, hg j]
  simp

/-- A prime divisor `E` in the support of `D = ∑ G_j` is, at each of its points `y`, one of the
`G j` through `y`. -/
private lemma exists_stalk_idealSheaf_eq (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : MMP.Mori.IsVariety k sY) [Smooth sY] (n : ℕ)
    (hdim : topologicalKrullDim Y = n) {ι : Type*} [Fintype ι] (G : ι → Y.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (G j)]
    (hG : ∀ J : Finset ι, J.Nonempty →
      IsEmpty (⨆ j ∈ J, G j).subscheme ∨
        (Smooth ((⨆ j ∈ J, G j).subschemeι ≫ sY) ∧
          ∀ C ∈ irreducibleComponents (Set.univ : Set (⨆ j ∈ J, G j).subscheme),
            topologicalKrullDim C + J.card = n))
    (D : MMP.Mori.Divisor Y)
    (hD : ∀ P : MMP.Mori.PrimeDivisor Y, D.coeff P = ∑ j, ((Module.length
      (Y.presheaf.stalk P.genericPoint) (Y.presheaf.stalk P.genericPoint ⧸
        IdealSheafData.stalk (G j) P.genericPoint)).toNat : ℤ))
    {E : MMP.Mori.PrimeDivisor Y} (hE : E ∈ D.support) {y : Y} (hy : y ∈ E.support) :
    ∃ j : ι, y ∈ (G j).support ∧
      IdealSheafData.stalk E.idealSheaf y = IdealSheafData.stalk (G j) y := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨j, hj⟩ : ∃ j, E.genericPoint ∈ (G j).support := by
    by_contra! h
    exact Finsupp.mem_support_iff.mp hE <| (hD E).trans <|
      Finset.sum_eq_zero fun j _ => length_stalk_quotient_eq_zero _ (h j)
  have hEG : E.support ⊆ (G j).support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hj) (G j).support.isClosed
  have hyG : y ∈ (G j).support := hEG hy
  refine ⟨j, hyG, ?_⟩
  obtain ⟨m, z, ι', hz, -, hG'⟩ := exists_isRegularSystemOfParameters k sY hY n hdim G hG y
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  obtain ⟨q, -, hqE, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hy
  have hle : IdealSheafData.stalk (G j) y ≤ IdealSheafData.stalk E.idealSheaf y := by
    refine MMP.Resolution.stalk_le_stalk_of_le ?_ y
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf E,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact hEG
  have hprime := MMP.Intersection.prime_of_isRegularSystemOfParameters hz (ι' ⟨j, hyG⟩)
  rw [hG' ⟨j, hyG⟩, hqE] at hle ⊢
  have : (Ideal.span {z (ι' ⟨j, hyG⟩)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  -- `(z i) ⊆ q` are primes, of height `1` for `q`, and `(z i) ≠ 0` in the domain `𝒪_{Y,y}`
  refine (eq_of_le_of_not_lt hle fun hlt => hprime.ne_zero ?_).symm
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hq1] at h1
  rw [← Ideal.span_singleton_eq_bot, ← Ideal.height_eq_zero_iff_eq_bot]
  exact nonpos_iff_eq_zero.mp
    ((ENat.add_le_add_iff_right ENat.one_ne_top).mp (by simpa using h1))

end Proof_lem_km2c_snc_criterion

namespace MMP.Mori

namespace DivisorWithCoeffs

open Proof_lem_km2c_snc_criterion in
/-- **Snc criterion.** Let `sY : Y ⟶ Spec k` be a smooth variety of dimension `n` and `G j`,
`j ∈ ι`, finitely many effective Cartier divisors on `Y` such that for every non-empty `J` the
scheme-theoretic intersection `⨆ j ∈ J, G j` is empty or smooth over `k` with every irreducible
component of dimension `n - |J|`. Then the divisor `D = ∑ⱼ G j` is snc and all of its nonzero
coefficients are `1`. -/
@[mmp "lem_km2c_snc_criterion"]
public theorem isSNC_of_forall_smooth_iSup (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (hY : IsVariety k sY) [Smooth sY] (n : ℕ)
    (hdim : topologicalKrullDim Y = n) {ι : Type*} [Fintype ι] (G : ι → Y.IdealSheafData)
    [∀ j, Stacks.Divisors.IsEffectiveCartierDivisor (G j)]
    (hG : ∀ J : Finset ι, J.Nonempty →
      IsEmpty (⨆ j ∈ J, G j).subscheme ∨
        (Smooth ((⨆ j ∈ J, G j).subschemeι ≫ sY) ∧
          ∀ C ∈ irreducibleComponents (Set.univ : Set (⨆ j ∈ J, G j).subscheme),
            topologicalKrullDim C + J.card = n))
    (D : Divisor Y)
    (hD : ∀ P : PrimeDivisor Y, D.coeff P = ∑ j, ((Module.length (Y.presheaf.stalk P.genericPoint)
      (Y.presheaf.stalk P.genericPoint ⧸ IdealSheafData.stalk (G j) P.genericPoint)).toNat : ℤ)) :
    D.IsSNC sY ∧ ∀ P ∈ D.support, D.coeff P = 1 := by
  classical
  have local_parameters : ∀ x : Y, ∃ (m : ℕ) (z : Fin m → Y.presheaf.stalk x)
      (j : {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ x ∈ E.support} → Fin m),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (j E)} := by
    intro x
    obtain ⟨m, z, ι', hz, hι', hG'⟩ :=
      Proof_lem_km2c_snc_criterion.exists_isRegularSystemOfParameters k sY hY n hdim G hG x
    choose c hc using fun E : {E : MMP.Mori.PrimeDivisor Y // E ∈ D.support ∧ x ∈ E.support} =>
      exists_stalk_idealSheaf_eq k sY hY n hdim G hG D hD E.2.1 E.2.2
    refine ⟨m, z, fun E => ι' ⟨c E, (hc E).1⟩, hz, fun E E' h => ?_, fun E => ?_⟩
    · refine Subtype.ext (MMP.Intersection.eq_of_stalk_idealSheaf_eq E.2.2 E'.2.2 ?_)
      rw [(hc E).2, (hc E').2, Subtype.mk.inj (hι' h)]
    · rw [(hc E).2]
      exact hG' ⟨c E, (hc E).1⟩
  refine ⟨⟨fun E hE => ?_, local_parameters⟩, fun P hP => ?_⟩
  · refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter sY _ fun y hy => ?_
    obtain ⟨m, z, j, hz, -, hI⟩ := local_parameters y
    exact ⟨m, z, j ⟨E, hE, hy⟩, hz, hI ⟨E, hE, hy⟩⟩
  -- at the generic point `η` of `P`, `𝒪_{Y,η}` is a DVR, so at most one `G j` passes through `η`,
  -- and there `𝒪_{Y,η} / (G j)_η` is the residue field
  set η := P.genericPoint
  obtain ⟨m, z, ι', hz, hι', hG'⟩ :=
      Proof_lem_km2c_snc_criterion.exists_isRegularSystemOfParameters k sY hY n hdim G hG η
  obtain rfl : m = 1 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, P.coheight_genericPoint] at h
    exact_mod_cast h.symm
  have hterm : ∀ j, ((Module.length (Y.presheaf.stalk η)
      (Y.presheaf.stalk η ⧸ IdealSheafData.stalk (G j) η)).toNat : ℤ) =
        if η ∈ (G j).support then 1 else 0 := by
    intro j
    split_ifs with hj
    · rw [hG' ⟨j, hj⟩, Subsingleton.elim (ι' ⟨j, hj⟩) default, ← Set.range_unique, hz.1]
      have : IsSimpleModule (Y.presheaf.stalk η)
          (Y.presheaf.stalk η ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk η)) :=
        isSimpleModule_iff_isCoatom.mpr
          (Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _))
      rw [Module.length_eq_one]; rfl
    · exact length_stalk_quotient_eq_zero _ hj
  have hsum := hD P
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_boole] at hsum
  have hle : (Finset.univ.filter fun j => η ∈ (G j).support).card ≤ 1 := by
    simpa [Fintype.card_subtype] using Fintype.card_le_of_injective ι' hι'
  have hne : (Finset.univ.filter fun j => η ∈ (G j).support).card ≠ 0 := fun h0 =>
    Finsupp.mem_support_iff.mp hP (hsum.trans (by rw [h0]; rfl))
  rw [hsum, show (Finset.univ.filter fun j => η ∈ (G j).support).card = 1 by omega]
  rfl

end DivisorWithCoeffs

end MMP.Mori

namespace Proof_lem_km2c_exceptional_set_pure_codim_one

open TopologicalSpace MMP.Mori Proof_lem_km2c_exceptional_divisor_witness

/-- A closed set which is a finite union of irreducible closed sets of codimension one is of
pure codimension one. -/
private theorem isPureCodimOne_of_eq_iUnion {T : Type*} [TopologicalSpace T] (S : Closeds T)
    (s : Finset (IrreducibleCloseds T)) (hs : ∀ Z ∈ s, codimension Z = 1)
    (hS : (S : Set T) = ⋃ Z ∈ s, (Z : Set T)) : IsPureCodimOne S := by
  intro W hW
  have hsub : (W : Set T) ⊆ ⋃₀ ↑(s.image (fun Z : IrreducibleCloseds T ↦ (Z : Set T))) := by
    rw [Finset.coe_image, Set.sUnion_image]
    simpa only [Finset.mem_coe, ← hS] using hW.prop
  obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible _
    (by simp only [Finset.mem_image]; rintro _ ⟨Z, -, rfl⟩; exact Z.isClosed) hsub
  obtain ⟨Z, hZs, rfl⟩ := Finset.mem_image.mp hz
  have hZS : (Z : Set T) ⊆ S :=
    hS ▸ Set.subset_biUnion_of_mem (u := fun Z : IrreducibleCloseds T ↦ (Z : Set T)) hZs
  have hWZ : W = Z := le_antisymm hWz (hW.2 hZS hWz)
  subst hWZ
  exact hs W hZs

/-! ### The fibres through points off an anti-ample exceptional divisor -/

section Core

open Opposite Stacks.Ample Stacks.ModuleStalk Stacks.NonvanishingLocusRestrict
  RingedSpaceModuleAdjunction

/-- A morphism of `𝒪_Y`-modules can only shrink the nonvanishing locus of a section. -/
private theorem nonvanishingLocusOn_app_subset {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (s : Γ(M, V)) :
    nonvanishingLocusOn N V (φ.app V s) ⊆ nonvanishingLocusOn M V s := by
  rintro y ⟨hy, h⟩
  refine ⟨hy, fun hm => h ?_⟩
  rw [← mapFun_germ]
  have h1 : map φ y ((M.presheaf.germ V y hy).hom s) ∈ (maximalSmul M y).map (map φ y) :=
    Submodule.mem_map_of_mem hm
  have h2 : (maximalSmul M y).map (map φ y) ≤ maximalSmul N y := by
    rw [maximalSmul, maximalSmul, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact h2 h1

/-- Where `D` has no component, `1` is a section of `𝒪_Y(D)`. -/
private theorem isDivisorialSection_one_of_coeff_eq_zero {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] (D : Divisor Y) (W : Y.Opens)
    (hW : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ W).Nonempty → D.coeff E = 0) :
    D.IsDivisorialSection W 1 := by
  intro E hE
  refine Or.inr ?_
  change WithZero.exp _ ≤ E.valuation 1
  rw [map_one, hW E hE, neg_zero, WithZero.exp_zero]

/-- For `E ≤ 0`, a section of `𝒪_Y(E)` read as a regular function through
`𝒪_Y(E) ⊆ 𝒪_Y(0) ≅ 𝒪_Y` is the rational function it is. -/
private theorem toRationalFunctionsPresheaf_app_inclusion {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] {E : Divisor Y} (h : E ≤ 0) (U : Y.Opens) (σ : Γ(E.divisorialSheaf, U)) :
    (toRationalFunctionsPresheaf Y).app (op U)
      (show Γ(Y, U) from (Divisor.divisorialSheafInclusion h ≫
        (Divisor.divisorialSheafZeroIso (X := Y)).hom).app U σ) = σ.1 := by
  set ψ := Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor Y))
  have hc : (Divisor.divisorialSheafZeroIso (X := Y)).hom ≫ ψ = 𝟙 _ :=
    (asIso ψ).inv_hom_id
  have key := ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U) hc)
    ((Divisor.divisorialSheafInclusion h).app U σ)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at key
  rw [← Divisor.coe_structureSheafToDivisorialSheaf_app (le_refl (0 : Divisor Y)) U,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  exact congrArg Subtype.val key

/-- **Step (b) of the source, at one point.** Let `f : Y ⟶ X` satisfy `f_* 𝒪_Y = 𝒪_X`, and let
`D ≥ 0` be a Cartier divisor on the normal scheme `Y` with `𝒪_Y(-D)` `f`-ample. If `y ∉ Supp D`,
then `f y` has an affine neighbourhood `B` whose preimage is affine and misses `Supp D`.

A section `σ` of `𝒪_Y(-nD)` over `f⁻¹V` with affine nonvanishing locus through `y` is a regular
function `t`, which is `f^*h` for some `h` on `V`; then `B = D(h)`: `t` is a unit at `y`, a unit
of `𝒪_{Y,z}` only off `Supp D` (it vanishes along every component of `D`), and wherever `t` is a
unit, `σ` does not vanish. -/
private theorem exists_isAffineOpen_preimage_of_notMem_supp {X Y : Scheme.{u}} [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) (hΓ : ∀ V : X.Opens, IsIso (f.app V))
    {D : Divisor Y} (hD0 : 0 ≤ D) (hD : D.IsCartier) (hamp : (-D).IsRelativelyAmple f hD.neg)
    {y : Y} (hy : y ∉ D.supp) :
    ∃ B : X.Opens, IsAffineOpen B ∧ IsAffineOpen (f ⁻¹ᵁ B) ∧ f y ∈ B ∧
      ∀ z ∈ f ⁻¹ᵁ B, z ∉ D.supp := by
  have := hD.neg.isInvertibleModule_divisorialSheaf
  obtain ⟨V, hV, hyV, hA⟩ := hamp (f y)
  obtain ⟨n, hn, s, U₀, hU₀, hyU₀, hU₀a⟩ :=
    IsAmpleForPowers.exists_affine_nonvanishingLocus hA (⟨y, hyV⟩ : (f ⁻¹ᵁ V).toScheme)
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_nsmul_iso hD.neg n hn
  let e := (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι
      (-D).divisorialSheaf n).symm ≪≫
    (modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e₀.symm
  let σ := Stacks.AmplePullbackPart1.sectionOfRestrictGlobalSection (f ⁻¹ᵁ V)
    (n • -D).divisorialSheaf (Scheme.Modules.Hom.app e.hom ⊤ s)
  have hNV : ∀ z : (f ⁻¹ᵁ V).toScheme, z ∈ (U₀ : Set (f ⁻¹ᵁ V).toScheme) ↔
      (f ⁻¹ᵁ V).ι z ∈ nonvanishingLocusOn _ (f ⁻¹ᵁ V) σ := by
    intro z
    rw [hU₀, ← nonvanishingLocus_congr e s]
    exact mem_nonvanishingLocus_iff_of_sectionOfRestrictGlobalSection (f ⁻¹ᵁ V) _ _ z
  have hle : (n • -D) ≤ 0 := by
    intro E
    simp only [Finsupp.coe_smul, Finsupp.coe_neg, Pi.smul_apply, Pi.neg_apply, Finsupp.coe_zero,
      Pi.zero_apply]
    exact nsmul_nonpos (neg_nonpos.mpr (hD0 E)) n
  let φ := Divisor.divisorialSheafInclusion hle ≫ (Divisor.divisorialSheafZeroIso (X := Y)).hom
  let t : Γ(Y, f ⁻¹ᵁ V) := φ.app (f ⁻¹ᵁ V) σ
  have ht : (toRationalFunctionsPresheaf Y).app (op (f ⁻¹ᵁ V)) t = σ.1 :=
    toRationalFunctionsPresheaf_app_inclusion hle (f ⁻¹ᵁ V) σ
  obtain ⟨h, hh⟩ := ((ConcreteCategory.isIso_iff_bijective (f.app V)).mp (hΓ V)).2 t
  have hpre : f ⁻¹ᵁ X.basicOpen h = Y.basicOpen t := by rw [Scheme.preimage_basicOpen, hh]
  -- `t` is a unit only off `Supp D`
  have hK4 : ∀ z ∈ Y.basicOpen t, z ∉ D.supp := by
    intro z hz hzD
    have hzZ : z ∈ f ⁻¹ᵁ V := Y.basicOpen_le t hz
    have hu : IsUnit ((Y.presheaf.germ (f ⁻¹ᵁ V) z hzZ).hom t) := (Y.mem_basicOpen t z hzZ).mp hz
    obtain ⟨E, hE, hzE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hzD
    have hEZ : (E.support ∩ f ⁻¹ᵁ V).Nonempty := ⟨z, hzE, hzZ⟩
    have hηZ := E.genericPoint_mem_of_nonempty hEZ
    have hsp : E.genericPoint ⤳ z := specializes_iff_mem_closure.mpr (by
      rwa [← AlgebraicGeometry.PrimeDivisor.support_eq_closure])
    have ha : IsUnit ((Y.presheaf.germ (f ⁻¹ᵁ V) E.genericPoint hηZ).hom t) := by
      have := hu.map (Y.presheaf.stalkSpecializes hsp).hom
      rwa [TopCat.Presheaf.germ_stalkSpecializes_apply] at this
    have hval := E.valuation_toComponent_of_isUnit ha
    have hcomp : E.toComponent.hom ((Y.presheaf.germ (f ⁻¹ᵁ V) E.genericPoint hηZ).hom t) =
        σ.1 ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEZ⟩ := by
      rw [← ht, toRationalFunctionsPresheaf_app_apply]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf _ _ _
    have hord := σ.2 E hEZ
    rw [← hcomp] at hord
    rcases hord with h0 | hle'
    · exact (ha.map E.toComponent.hom).ne_zero h0
    · rw [hval, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle'
      apply hE
      have h1 : (n • -D).coeff E = -((n : ℤ) * D.coeff E) := by
        simp [DivisorWithCoeffs.coeff_apply]
      rw [h1, neg_neg] at hle'
      have h2 : 0 ≤ D.coeff E := hD0 E
      have h3 : (0 : ℤ) < n := by exact_mod_cast hn
      nlinarith
  -- `t` is a unit at `y`
  have hyNV : y ∈ nonvanishingLocusOn _ (f ⁻¹ᵁ V) σ := (hNV ⟨y, hyV⟩).mp hyU₀
  let W : Y.Opens := f ⁻¹ᵁ V ⊓ ⟨(D.supp : Set Y)ᶜ, D.supp.isClosed.isOpen_compl⟩
  have hyW : y ∈ W := ⟨hyV, hy⟩
  have hW0 : ∀ E : MMP.Mori.PrimeDivisor Y, (E.support ∩ W).Nonempty →
      (n • -D).coeff E = 0 := by
    rintro E ⟨x, hxE, hxW⟩
    have : D.coeff E = 0 := by
      by_contra hne
      exact hxW.2 (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hne, hxE⟩)
    simp only [DivisorWithCoeffs.coeff_apply] at this ⊢
    simp [this]
  let one : Γ((n • -D).divisorialSheaf, W) := ⟨1, isDivisorialSection_one_of_coeff_eq_zero _ W hW0⟩
  let iW : W ⟶ f ⁻¹ᵁ V := homOfLE inf_le_left
  have hres : (n • -D).divisorialSheaf.presheaf.map iW.op σ = Y.presheaf.map iW.op t • one := by
    apply Subtype.ext
    funext Zc
    change σ.1 ⟨Zc.1, _⟩ = Y.presheaf.germ W _ Zc.2 (Y.presheaf.map iW.op t) * 1
    rw [mul_one, TopCat.Presheaf.germ_res_apply, ← ht, toRationalFunctionsPresheaf_app_apply]
  have hu : IsUnit ((Y.presheaf.germ (f ⁻¹ᵁ V) y hyV).hom t) := by
    by_contra hnu
    apply hyNV.2
    have hm := smul_mem_maximalSmul_of_mem_maximalIdeal (M := (n • -D).divisorialSheaf)
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      (((n • -D).divisorialSheaf.presheaf.germ W y hyW).hom one)
    rw [← TopCat.Presheaf.germ_res_apply Y.presheaf iW y hyW, ← germ_smul, ← hres,
      TopCat.Presheaf.germ_res_apply] at hm
    exact hm
  have hyB : y ∈ Y.basicOpen t := (Y.mem_basicOpen t y hyV).mpr hu
  -- wherever `t` is a unit, `σ` does not vanish
  have hUle : (f ⁻¹ᵁ V).ι ''ᵁ U₀ ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hBU : Y.basicOpen t ≤ (f ⁻¹ᵁ V).ι ''ᵁ U₀ := by
    intro z hz
    have hzZ : z ∈ f ⁻¹ᵁ V := Y.basicOpen_le t hz
    have hzNV : z ∈ nonvanishingLocusOn _ (f ⁻¹ᵁ V) σ := by
      refine nonvanishingLocusOn_app_subset φ (f ⁻¹ᵁ V) σ ⟨hzZ, fun hm => ?_⟩
      have := mem_maximalIdeal_of_mem_maximalSmul Y z hm
      rw [unitStalkFun_germ] at this
      exact (IsLocalRing.notMem_maximalIdeal.mpr ((Y.mem_basicOpen t z hzZ).mp hz)) this
    exact ⟨⟨z, hzZ⟩, (hNV ⟨z, hzZ⟩).mpr hzNV, rfl⟩
  have hUa : IsAffineOpen ((f ⁻¹ᵁ V).ι ''ᵁ U₀) := hU₀a.image_of_isOpenImmersion (f ⁻¹ᵁ V).ι
  refine ⟨X.basicOpen h, hV.basicOpen h, ?_, ?_, ?_⟩
  · have hb := hUa.basicOpen (Y.presheaf.map (homOfLE hUle).op t)
    rw [Scheme.basicOpen_res, inf_eq_right.mpr hBU] at hb
    rwa [hpre]
  · change y ∈ f ⁻¹ᵁ X.basicOpen h
    rw [hpre]
    exact hyB
  · exact fun z hz => hK4 z (by rwa [hpre] at hz)

/-- **Finite fibres over an affine open with affine preimage.** If `f` is proper and `B ∋ x` is
an affine open with `f⁻¹(B)` affine, then `f` is finite over `B` and the fibre over `x` is
finite. -/
private theorem finite_preimage_singleton_of_isAffineOpen {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsProper f] {B : X.Opens} (hB : IsAffineOpen B) (hfB : IsAffineOpen (f ⁻¹ᵁ B)) {x : X}
    (hx : x ∈ B) : (f ⁻¹' {x}).Finite := by
  have : IsAffine B.toScheme := hB
  have : IsAffine (f ⁻¹ᵁ B).toScheme := hfB
  have : IsFinite (f ∣_ B) := by
    rw [IsFinite.iff_isProper_and_isAffineHom]
    exact ⟨inferInstance, inferInstance⟩
  refine (((f ∣_ B).finite_preimage_singleton ⟨x, hx⟩).image (f ⁻¹ᵁ B).ι).subset ?_
  intro z hz
  have hzB : z ∈ f ⁻¹ᵁ B := by
    change f z ∈ B
    rw [Set.mem_singleton_iff.mp hz]
    exact hx
  refine ⟨⟨z, hzB⟩, ?_, rfl⟩
  apply Subtype.ext
  have := congrArg (fun g => g.base ⟨z, hzB⟩) (morphismRestrict_ι f B)
  simp only [Scheme.Hom.comp_base] at this
  exact this.trans (Set.mem_singleton_iff.mp hz)

end Core

/-! ### The normal case -/

/-- On a proper birational morphism of varieties onto a normal variety, a point of the target is
in the biregular locus exactly when its fibre is finite. -/
private theorem mem_biregularLocus_iff_finite (k : Type u) [Field k] {U R : Scheme.{u}}
    {sU : U ⟶ Spec (.of k)} {sR : R ⟶ Spec (.of k)} (hU : AlgebraicGeometry.IsVariety k sU)
    (hR : AlgebraicGeometry.IsVariety k sR) [IsNormal R] (h : U ⟶ R) (hh : h ≫ sR = sU)
    [IsProper h] (hb : IsBirational h) (x : R) :
    x ∈ biregularLocus h ↔ (h ⁻¹' {x}).Finite := by
  obtain ⟨⟨hO, hiso⟩, hEx, -⟩ :=
    MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hU hR h hh hb
  refine ⟨fun hx => ?_, fun hx => le_biregularLocus (V := ⟨_, hO⟩) hiso hx⟩
  have : LocallyOfFiniteType sU := hU.toLocallyOfFiniteType
  have : LocallyOfFiniteType h := by
    subst hh
    exact locallyOfFiniteType_of_comp h sR
  rcases (h ⁻¹' {x}).eq_empty_or_nonempty with h0 | ⟨u, hu⟩
  · rw [h0]
    exact Set.finite_empty
  · have hux : h u = x := hu
    have hnot : u ∉ (exceptionalSet h : Set U) := fun hu' =>
      hu' (show h u ∈ biregularLocus h by rwa [hux])
    rw [hEx, Set.mem_ofPred_eq, not_lt, hux] at hnot
    exact MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le h x hnot

/-- **Normal case** (the source's steps (a)–(c)). Let `f : Y ⟶ X` be a proper birational morphism
of varieties, `X` normal and `ℚ`-factorial, `Y` normal, with `f` finite over some `ℙⁿ_X`. Then
`Ex(f)` is the union of finitely many prime divisors: the components of an effective
exceptional `D` with `𝒪_Y(-D)` `f`-ample. Off `Supp D` the fibres of `f` are finite. -/
private theorem exists_finset_exceptionalSet_eq_of_isNormal {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsNormalVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY) (hfP : IsProper f)
    (hfg : ∃ (n : ℕ) (g : Y ⟶ projectiveSpaceOver n X), IsFinite g ∧
      g ≫ (projectiveSpaceOver n X ↘ X) = f)
    (hfb : IsBirationalMorphism f) :
    ∃ s : Finset (MMP.Mori.PrimeDivisor Y), (exceptionalSet f : Set Y) = ⋃ E ∈ s, E.support := by
  obtain ⟨F, e, he, hF0, hFE, D, hD, hDF, hamp⟩ :=
    exists_isRelativelyAmple_neg_of_isFinite sX sY hX hY f hfs hfP hfg hfb
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1.1
  have hYv : AlgebraicGeometry.IsVariety k sY := hY.1
  have := hXv.toIsIntegral
  have := hYv.toIsIntegral
  have hDcoeff : ∀ E, (D E : ℚ) = e * F E := fun E =>
    (by simpa using congrArg (· E) hDF : Divisor.toQDivisor D E = e * F E)
  have heq : (0 : ℚ) < e := by exact_mod_cast he
  have hD0 : 0 ≤ D := fun E => by
    exact_mod_cast (hDcoeff E ▸ mul_nonneg heq.le (hF0 E) : (0 : ℚ) ≤ D E)
  refine ⟨F.support, subset_antisymm ?_ ?_⟩
  · intro y hy
    by_contra hyS
    have hyD : y ∉ D.supp := by
      rw [DivisorWithCoeffs.mem_supp_iff]
      rintro ⟨E, hE, hyE⟩
      refine hyS (Set.mem_biUnion (x := E) (Finsupp.mem_support_iff.mpr fun hF => hE ?_) hyE)
      rw [DivisorWithCoeffs.coeff_apply]
      have : (D E : ℚ) = 0 := by rw [hDcoeff, hF, mul_zero]
      exact_mod_cast this
    have hΓ := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sY sX
      hYv ⟨hXv, inferInstance⟩ f hfb).1
    obtain ⟨B, hB, hfB, hyB, -⟩ :=
      exists_isAffineOpen_preimage_of_notMem_supp f hΓ hD0 hD hamp hyD
    have hfin := finite_preimage_singleton_of_isAffineOpen f hB hfB hyB
    exact hy ((mem_biregularLocus_iff_finite k hYv hXv f hfs
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb) (f y)).mpr hfin)
  · simp only [Set.iUnion_subset_iff]
    intro E hE
    exact MMP.Positivity.support_subset_exceptionalSet E (hFE E (Finsupp.mem_support_iff.mp hE))

/-! ### The general case, through the normalization -/

/-- A locally quasi-finite morphism is strictly monotone for the specialization orders: two
points of one fibre are never specializations of each other. -/
private theorem strictMono_of_locallyQuasiFinite {Y' Y : Scheme.{u}} (ν : Y' ⟶ Y)
    [LocallyQuasiFinite ν] : StrictMono (ν : Y' → Y) := by
  intro a b hab
  have hsp : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
  have hle : ν a ≤ ν b := Scheme.le_iff_specializes.mpr (hsp.map ν.continuous)
  refine lt_of_le_not_ge hle fun hge => ?_
  have heq : ν b = ν a := ((hsp.map ν.continuous).antisymm (Scheme.le_iff_specializes.mp hge)).eq
  have hab' : b = a := (ν.isDiscrete_preimage_singleton (ν a)).eq_of_specializes hsp heq rfl
  exact lt_irrefl a (hab' ▸ hab)

/-- A closed map lifts strict specializations: for `b < ν a` there is `a' < a` over `b`. -/
private theorem exists_lt_of_lt_of_isClosedMap {Y' Y : Scheme.{u}} (ν : Y' ⟶ Y)
    (hν : IsClosedMap ν) {a : Y'} {b : Y} (hb : b < ν a) : ∃ a' < a, ν a' = b := by
  obtain ⟨a', ha', rfl⟩ := hν.specializingMap (Scheme.le_iff_specializes.mp hb.le)
  refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun h => ?_, rfl⟩
  exact hb.not_ge (Scheme.le_iff_specializes.mpr
    ((Scheme.le_iff_specializes.mp h).map ν.continuous))

/-- **Codimension is preserved by a finite surjective morphism of integral schemes of finite type
over a field**: heights are preserved (finite morphisms are closed and quasi-finite), so the
dimension and, by the dimension formula, the coheights are. -/
private theorem coheight_apply_eq_of_isFinite {k : Type u} [Field k] {Y' Y : Scheme.{u}}
    [IsIntegral Y'] [IsIntegral Y] (ν : Y' ⟶ Y) [IsFinite ν] (hsurj : Function.Surjective ν)
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (z : Y') :
    Order.coheight (ν z) = Order.coheight z := by
  let : Y.Over (Spec (.of k)) := ⟨sY⟩
  let : Y'.Over (Spec (.of k)) := ⟨ν ≫ sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have : LocallyOfFiniteType (Y' ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (ν ≫ sY))
  have hh : ∀ a : Y', Order.height (ν a) = Order.height a := fun a =>
    (Order.height_eq_of_strictMono ν (strictMono_of_locallyQuasiFinite ν)
      (fun a b hb => exists_lt_of_lt_of_isClosedMap ν ν.isClosedMap hb) a).symm
  have hdim : Order.krullDim Y = Order.krullDim Y' := by
    rw [Order.krullDim_eq_iSup_height, Order.krullDim_eq_iSup_height]
    refine le_antisymm (iSup_le fun b => ?_) (iSup_le fun a => ?_)
    · obtain ⟨a, rfl⟩ := hsurj b
      rw [hh]
      exact le_iSup (fun a : Y' => (Order.height a : WithBot ℕ∞)) a
    · rw [← hh]
      exact le_iSup (fun b : Y => (Order.height b : WithBot ℕ∞)) (ν a)
  have h1 := MMP.height_add_coheight_eq_krullDim k (ν z)
  have h2 := MMP.height_add_coheight_eq_krullDim k z
  have hlt := MMP.krullDim_lt_top_of_isIntegral k Y'
  rw [hdim, ← h2, hh] at h1
  have h3 : Order.height z + Order.coheight (ν z) = Order.height z + Order.coheight z :=
    WithBot.coe_injective h1
  have hfin : Order.height z ≠ ⊤ := by
    intro htop
    rw [← h2, htop, top_add] at hlt
    exact lt_irrefl _ hlt
  exact WithTop.add_left_cancel hfin h3

/-- **General case, reduction to the normalization** (the source's last paragraph). For a
projective birational `f : Y ⟶ X` of varieties with `X` `ℚ`-factorial, `Ex(f)` is a finite union of
irreducible closed subsets of codimension one: with `ν : Yᵛ ⟶ Y` the normalization, `f ∘ ν` is
finite over `ℙⁿ_X`, birational, and has the same fibres up to the finite surjective `ν`, so `Ex(f ∘ ν) = ν⁻¹(Ex f)` and `Ex(f) = ν(Ex(f ∘ ν))`;
`ν` maps each prime divisor onto an irreducible closed subset of codimension one. -/
private theorem exists_finset_exceptionalSet_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : MMP.Mori.IsVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) :
    ∃ s : Finset (IrreducibleCloseds Y), (∀ Z ∈ s, codimension Z = 1) ∧
      (exceptionalSet f : Set Y) = ⋃ Z ∈ s, (Z : Set Y) := by
  classical
  have hXv : AlgebraicGeometry.IsVariety k sX := hX.1.1
  have : AlgebraicGeometry.IsVariety k sY := hY
  have := hXv.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsProper f := isProper_of_isProjectiveMorphism f hfp
  obtain ⟨⟨hvar, hnorm, hfin, hsurj, hbir⟩, -, -, -, -⟩ := MMP.Threefold.normalization_spec sY
  set hfc := MMP.finite_irreducibleComponents_of_isIntegral Y
  set Yn := Y.normalizationScheme hfc
  set ν : Yn ⟶ Y := Y.normalization hfc
  have := hvar.toIsIntegral
  have : LocallyOfFiniteType (ν ≫ sY) := hvar.toLocallyOfFiniteType
  have : CompactSpace Yn := QuasiCompact.compactSpace_of_compactSpace (ν ≫ sY)
  have : IsLocallyNoetherian Yn := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ sY)
  have : IsNormal Yn := hnorm
  have : IsFinite ν := hfin
  -- the composite is proper, finite over `ℙⁿ_X` and birational
  have hfP : IsProper (ν ≫ f) := inferInstance
  have hfg : ∃ (n : ℕ) (g : Yn ⟶ projectiveSpaceOver n X), IsFinite g ∧
      g ≫ (projectiveSpaceOver n X ↘ X) = ν ≫ f := by
    obtain ⟨n, i, hi, hif⟩ := hfp
    exact ⟨n, ν ≫ i, inferInstance, by rw [Category.assoc, hif]⟩
  have hbν := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbir
  have hbf := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
  have hb : IsBirational (ν ≫ f) := hbν.comp hbf
  have hfs' : (ν ≫ f) ≫ sX = ν ≫ sY := by rw [Category.assoc, hfs]
  have hbm : IsBirationalMorphism (ν ≫ f) := by
    obtain ⟨⟨hO, hiso⟩, -, -⟩ :=
      MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hvar hXv (ν ≫ f)
        hfs' hb
    have : LocallyOfFiniteType (ν ≫ f) := by
      have : LocallyOfFiniteType ((ν ≫ f) ≫ sX) := hfs' ▸ inferInstance
      exact locallyOfFiniteType_of_comp (ν ≫ f) sX
    have hpre := preimage_genericPoint (ν ≫ f) hb
    have hηX : genericPoint X ∈ MMP.Resolution.Bridges.finiteFibreLocus (ν ≫ f) := by
      change ((ν ≫ f) ⁻¹' {genericPoint X}).Finite
      rw [hpre]
      exact Set.finite_singleton _
    have hηY : genericPoint Yn ∈ (ν ≫ f) ⁻¹ᵁ ⟨_, hO⟩ := by
      change (ν ≫ f) (genericPoint Yn) ∈ MMP.Resolution.Bridges.finiteFibreLocus (ν ≫ f)
      rw [IsBirational.genericPoint_eq _ hb]
      exact hηX
    exact MMP.Flips.isBirationalMorphism_of_isIso_resLE (ν ≫ f) ((ν ≫ f) ⁻¹ᵁ ⟨_, hO⟩) ⟨_, hO⟩
      ⟨_, hηY⟩ ⟨_, hηX⟩ le_rfl
      (by simp only [Scheme.Hom.resLE, Scheme.homOfLE_rfl, Category.id_comp]; exact hiso)
  obtain ⟨s, hs⟩ := exists_finset_exceptionalSet_eq_of_isNormal sX (ν ≫ sY) hX ⟨hvar, hnorm⟩
    (ν ≫ f) hfs' hfP hfg hbm
  -- `Ex(f ∘ ν) = ν⁻¹(Ex f)`
  have hsurj' : Function.Surjective ν := hsurj.surj
  have hiff : ∀ u : Yn, u ∈ (exceptionalSet (ν ≫ f) : Set Yn) ↔
      ν u ∈ (exceptionalSet f : Set Y) := by
    intro u
    rw [SetLike.mem_coe, SetLike.mem_coe, mem_exceptionalSet, mem_exceptionalSet,
      mem_biregularLocus_iff_finite k hvar hXv (ν ≫ f) hfs' hb,
      mem_biregularLocus_iff_finite k hY hXv f hfs hbf, Scheme.Hom.comp_apply]
    have hpre : (ν ≫ f) ⁻¹' {f (ν u)} = ν ⁻¹' (f ⁻¹' {f (ν u)}) := by
      ext v
      simp
    rw [hpre]
    refine not_congr ⟨fun h => ?_, ν.finite_preimage⟩
    rw [← Set.image_preimage_eq (f ⁻¹' {f (ν u)}) hsurj']
    exact h.image ν
  have hEx : (exceptionalSet f : Set Y) = ν '' (exceptionalSet (ν ≫ f) : Set Yn) := by
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · obtain ⟨u, rfl⟩ := hsurj' y
      exact ⟨u, (hiff u).mpr hy, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hiff u).mp hu
  have himg : ∀ E : MMP.Mori.PrimeDivisor Yn,
      ν '' E.support = (IrreducibleCloseds.closureSingleton (ν E.genericPoint) : Set Y) := by
    intro E
    rw [IrreducibleCloseds.coe_closureSingleton, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ν.isClosedMap.closure_image_eq_of_continuous ν.continuous, Set.image_singleton]
  refine ⟨s.image fun E => IrreducibleCloseds.closureSingleton (ν E.genericPoint), ?_, ?_⟩
  · simp only [Finset.mem_image]
    rintro _ ⟨E, -, rfl⟩
    rw [Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight,
      coheight_apply_eq_of_isFinite ν hsurj' sY,
      ← Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
    exact E.codimension_closure_genericPoint
  · rw [hEx, hs, Set.image_iUnion₂, Finset.set_biUnion_finset_image]
    exact Set.iUnion₂_congr fun E _ => himg E

end Proof_lem_km2c_exceptional_set_pure_codim_one

namespace MMP.Mori

open Proof_lem_km2c_exceptional_set_pure_codim_one in
/-- **The exceptional set of a projective birational morphism to a `ℚ`-factorial variety is
divisorial** (Kollár–Mori 2.63). If `f : Y ⟶ X` is a projective birational morphism of varieties
over `k` and `X` is `ℚ`-factorial, then `exceptionalSet f` is empty or of pure codimension one. -/
@[mmp "lem_km2c_exceptional_set_pure_codim_one"]
public theorem isPureCodimOne_exceptionalSet_of_isQFactorial
    {k : Type u} [Field k] {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : MMP.Fourfold.IsQFactorial sX) (hY : IsVariety k sY)
    (f : Y ⟶ X) (hfs : f ≫ sX = sY)
    (hfp : IsProjectiveMorphism f) (hfb : IsBirationalMorphism f) :
    IsPureCodimOne (exceptionalSet f) := by
  obtain ⟨s, hs, hS⟩ := exists_finset_exceptionalSet_eq sX sY hX hY f hfs hfp hfb
  exact isPureCodimOne_of_eq_iUnion _ s hs hS

end MMP.Mori
