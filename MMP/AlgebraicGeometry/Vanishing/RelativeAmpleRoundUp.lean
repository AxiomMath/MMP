module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.Untwisting
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveSchemes
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
public import MMP.AlgebraicGeometry.Intersection.Nef
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
public import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
public import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
public import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
public import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup

/-!
# Vanishing of higher direct images for a relatively ample `ℚ`-divisor

Let `f : Y ⟶ Z` be a projective morphism of varieties over an algebraically closed field `k` of
characteristic zero, with `Y` smooth, `K` a canonical divisor of `Y`, and `B` an `f`-ample
`ℚ`-divisor on `Y` whose fractional part `{B}` has simple normal crossing support. Then
`R^i f_* 𝒪_Y(K + ⌈B⌉) = 0` for every `i > 0`.

The proof compactifies `f` over a projective closure of an affine chart of `Z`, resolves the
compactification keeping `Y` as an snc open subset, and reduces to the projective round-up
vanishing
`MMP.Mori.subsingleton_derivedCohomologyOverField_exteriorPower_tensor_divisorialSheaf_roundUp`
for `B + n f^*H`, `H` the hyperplane at infinity, by writing the pushforward from `Y` as the
colimit of twists by `n f^*H`.

## Main results

* `MMP.Fourfold.isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp`: the
  vanishing above.

## Implementation notes

* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, the setting of the projective vanishing theorem it rests on.
* `f`-ampleness of the `ℚ`-divisor `B` is `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`: some
  positive multiple of `B` is a Cartier divisor whose invertible sheaf is `f`-ample.
* "`{B}` has snc support" is `MMP.Mori.DivisorWithCoeffs.IsSNC` of
  `MMP.Mori.DivisorWithCoeffs.fract B`, and `⌈B⌉` is `MMP.Mori.DivisorWithCoeffs.roundUp B`.
* `K_Y` is a divisor `K` with `MMP.Mori.Divisor.IsCanonicalDivisor`, and `R^i f_*` is the
  `i`-th right derived functor of `AlgebraicGeometry.Scheme.Modules.pushforward f`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Thm. 2.64,
  Cor. 2.68
-/

@[expose] public section

section

/-!
## Proof: Relative ample vanishing from projective vanishing

Let `f : Y ⟶ Z` be a projective morphism of varieties over an algebraically closed field of
characteristic zero, with `Y` smooth, `K` a canonical divisor of `Y` and `B` a `ℚ`-divisor with a
relatively ample multiple whose fractional part has simple normal crossing support. Then
`Rⁱf_* 𝒪_Y(K + ⌈B⌉) = 0` for `i > 0`.

Higher direct images vanish once the cohomology of every preimage `W = f⁻¹(V)` of an affine open
`V ⊆ Z` does. A multiple of `B` embeds `W` into `ℙᴹ_V ⊆ ℙᴹ × ℙʳ`; its closure `Y₀` is a
projective variety carrying an ample family `A_a = A_0 ⊗ H^{⊗ a}` with `H` cutting out the boundary
`Y₀ ∖ W`. A log resolution of `Y₀` which is an isomorphism over `W` and makes the boundary snc
compactifies `W` to a smooth projective `X` on which `L + mE + Δ` is nef and big for large `m`.
Kawamata–Viehweg vanishing for round-ups on `X`, and the fact that `H^i(W, -)` is the colimit of
`H^i(X, - ⊗ 𝒪(mE))` (Stacks, Tag 09MR), give the vanishing over `W`.

## Main results

* `MMP.FourfoldProofs.FourfoldRelativeAmpleVanishingProof.isZero_hgroup_preimage`: the vanishing of
  `Hⁱ(f⁻¹(V), 𝒪_Y(K + ⌈B⌉))` for every affine open `V` of `Z`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

namespace MMP.FourfoldProofs.FourfoldRelativeAmpleVanishingProof

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule

section Endgame

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- **Cohomology of the nonvanishing open from vanishing of all twists.** Let `X` be a
quasi-compact quasi-separated scheme, `ℒ` an invertible module, `s ∈ Γ(X, ℒ)` and `𝒢` a
quasi-coherent module with `Hⁿ(X, 𝒢 ⊗ ℒ^{⊗ k}) = 0` for every `k ≥ 0`. Then `Hⁿ(X_s, 𝒢) = 0`:
a class `η` on `X_s` has some `sᵏ η` extending to `X` ([Stacks, Tag 09MR]), hence `sᵏ η = 0`,
and multiplication by `sᵏ` is injective on the cohomology of `X_s`. -/
private theorem isZero_hgroup_nonvanishingOpen {X : Scheme.{0}} [QuasiSeparatedSpace X]
    [CompactSpace X]
    (L : SheafOfModules.{0} (structureSheafRing X.toRingedSpace))
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (G : X.Modules) [G.IsQuasicoherent] (n : ℕ)
    (h : ∀ k : ℕ, IsZero (Hgroup X.ringCatSheaf ⊤ n (twist X L G (k : ℤ)))) :
    IsZero (Hgroup X.ringCatSheaf (nonvanishingOpen L s) n G) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun η η' => ?_⟩
  suffices hz : ∀ η : Hgroup X.ringCatSheaf (nonvanishingOpen L s) n G, η = 0 by
    rw [hz η, hz η']
  intro η
  obtain ⟨-, hext⟩ := SectionPowerAnnihilation.annihilates_and_extends_of_isCompact s ⊤
    isCompact_univ n
  obtain ⟨k, ξ, hξ⟩ := hext (nonvanishingOpen L s) le_top (top_inf_eq _).symm G inferInstance η
  have hξ0 : ξ = 0 := by
    have := AddCommGrpCat.isZero_iff_subsingleton.mp (h k)
    exact Subsingleton.elim _ _
  rw [hξ0, map_zero] at hξ
  have hiso := Untwisting.isIso_hfunctor_map_sectionPowerAction X L s G k
    (nonvanishingOpen L s) le_rfl n
  have hinj : Function.Injective (ConcreteCategory.hom ((Hfunctor X.ringCatSheaf
      (nonvanishingOpen L s) n).map (SectionPowerComposition.mul X L s G k))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (hξ.symm.trans (map_zero _).symm)

end Endgame

section Main

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

private theorem roundUp_toQDivisor_add {X : Scheme.{0}} (D : Divisor X) (Δ : QDivisor X) :
    (Divisor.toQDivisor D + Δ).roundUp = D + Δ.roundUp := by
  ext E
  change (Divisor.toQDivisor D + Δ).roundUp.coeff E = D.coeff E + Δ.roundUp.coeff E
  rw [DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundUp,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, Int.ceil_intCast_add]

/-- The prime divisor of `X` whose generic point is the image of the generic point of a prime
divisor of `W`, for an open immersion `u : W ⟶ X`. -/
private def openPrimeDivisor {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) :
    MMP.Mori.PrimeDivisor X :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (u P.genericPoint)
    ((coheight_eq_of_isOpenImmersion u).trans P.coheight_genericPoint)

private theorem genericPoint_openPrimeDivisor {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) : (openPrimeDivisor u P).genericPoint = u P.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- On a smooth variety a canonical divisor `K` of dimension `n` has `𝒪_X(K) ≅ ⋀ⁿ Ω_{X/k}`:
the defining isomorphism lives on the smooth locus, which is all of `X`. -/
private theorem nonempty_divisorialSheaf_iso_exteriorPower {k : Type} [Field k] {X : Scheme.{0}}
    {f : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) :=
  MMP.Flips.nonempty_iso_of_restrict_iso hsm (hK.iso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus f).ι).app _ ≪≫
      Scheme.Modules.exteriorPowerPullbackIso (smoothLocus f).ι _ n ≪≫
      (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
        (Scheme.Hom.etaleRelativeDifferentialsIso (smoothLocus f).ι f _ rfl)).symm)

/-- The pull-back of a canonical divisor of a smooth variety along an open immersion `ι` has
divisorial sheaf `⋀ⁿ Ω_{W/k}`. -/
private theorem nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback {k : Type} [Field k]
    {W X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (ι : W ⟶ X) [IsOpenImmersion ι] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n)
    {hB : ∀ Z : irreducibleComponents W, ι (componentGenericPoint W Z) ∉ K.supp}
    {K' : Divisor W} (h : K.IsPullback ι hB K') :
    Nonempty (K'.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (ι ≫ sX)) n) := by
  have hKc : K.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm K
  obtain ⟨e⟩ := nonempty_divisorialSheaf_iso_exteriorPower hsm hK
  exact ⟨(Divisor.IsPullback.divisorialSheafIso (hBc := hKc) h) ≪≫
    (Scheme.Modules.pullback ι).mapIso e ≪≫
    Scheme.Modules.exteriorPowerPullbackIso ι _ n ≪≫
    (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
      (Scheme.Hom.etaleRelativeDifferentialsIso ι sX _ rfl)⟩

/-- The coefficients of the pull-back of a Cartier divisor along an open immersion are those of
the corresponding prime divisors. -/
private theorem coeff_of_isPullback_of_isOpenImmersion {W X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian W] [IsNormal W] (ι : W ⟶ X) [IsOpenImmersion ι]
    {D : Divisor X} (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents W, ι (componentGenericPoint W Z) ∉ D.supp}
    {D' : Divisor W} (h : D.IsPullback ι hB D') (P : MMP.Mori.PrimeDivisor W) :
    D'.coeff P = D.coeff (openPrimeDivisor ι P) :=
  MMP.Positivity.coeff_eq_of_isPullback P _ (genericPoint_openPrimeDivisor ι P).symm hDc h

private theorem openPrimeDivisor_injective {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u] :
    Function.Injective (openPrimeDivisor u) := fun P Q h =>
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective (u.isOpenEmbedding.injective (by
    rw [← genericPoint_openPrimeDivisor, h, genericPoint_openPrimeDivisor]))

private theorem openPrimeDivisor_eq_primeDivisorMap {W X : Scheme.{0}} (u : W ⟶ X)
    [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) :
    openPrimeDivisor u P = OpenWeilRestriction.primeDivisorMap u P :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((genericPoint_openPrimeDivisor u P).trans
    (OpenWeilRestriction.genericPoint_primeDivisorMap u P).symm)

/-- **Prime divisors through the complement of a support.** If an open immersion `ι : W ⟶ X` has
image `X ∖ Supp E`, then `E` has coefficient zero along the closure of every prime divisor of
`W`. -/
private theorem coeff_openPrimeDivisor_eq_zero {W X : Scheme.{0}} (ι : W ⟶ X) [IsOpenImmersion ι]
    {E : Divisor X} (h : Set.range ι = (E.supp : Set X)ᶜ) (P : MMP.Mori.PrimeDivisor W) :
    E.coeff (openPrimeDivisor ι P) = 0 := by
  by_contra hne
  have hmem : (openPrimeDivisor ι P).genericPoint ∈ (E.supp : Set X) :=
    DivisorWithCoeffs.support_subset_supp hne (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
  rw [genericPoint_openPrimeDivisor, ← Set.notMem_compl_iff, ← h] at hmem
  exact hmem ⟨_, rfl⟩

/-- **Comparison of divisorial sheaves along two open immersions.** Let `ι : W ⟶ X` and
`j : W ⟶ X'` be open immersions into smooth varieties over `k` compatible with the structure
morphisms, `K`, `K'` canonical divisors and `D`, `D'` divisors with the same coefficient along
corresponding prime divisors. Then `ι^* 𝒪_X(K + D) ≅ j^* 𝒪_{X'}(K' + D')`. -/
private theorem nonempty_restrict_divisorialSheaf_iso {k : Type} [Field k]
    {W X X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X'] [CompactSpace X] [CompactSpace X']
    [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hsm : IsSmoothScheme sX) (hsm' : IsSmoothScheme sX')
    (ι : W ⟶ X) [IsOpenImmersion ι] (j : W ⟶ X') [IsOpenImmersion j]
    (hιj : ι ≫ sX = j ≫ sX') {n : ℕ} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX n) (hK' : K'.IsCanonicalDivisor sX' n)
    (D : Divisor X) (D' : Divisor X')
    (hD : ∀ P : MMP.Mori.PrimeDivisor W,
      D.coeff (openPrimeDivisor ι P) = D'.coeff (openPrimeDivisor j P)) :
    Nonempty ((K + D).divisorialSheaf.restrict ι ≅ (K' + D').divisorialSheaf.restrict j) := by
  haveI : IsDominant ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ι
  haveI : IsDominant j := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion j
  have hc : ∀ G : Divisor X, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  have hc' : ∀ G : Divisor X', G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm'
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant ι
  have hB' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant j
  obtain ⟨Kι, hKι⟩ := (hc K).exists_isPullback (hB K)
  obtain ⟨Dι, hDι⟩ := (hc D).exists_isPullback (hB D)
  obtain ⟨Kj, hKj⟩ := (hc' K').exists_isPullback (hB' K')
  obtain ⟨Dj, hDj⟩ := (hc' D').exists_isPullback (hB' D')
  have hDD : Dι = Dj := by
    ext P
    change Dι.coeff P = Dj.coeff P
    rw [coeff_of_isPullback_of_isOpenImmersion ι (hc D) hDι,
      coeff_of_isPullback_of_isOpenImmersion j (hc' D') hDj, hD P]
  subst hDD
  have hsum := Divisor.IsPullback.add (hc K) (hc D) (hB (K + D)) hKι hDι
  have hsum' := Divisor.IsPullback.add (hc' K') (hc' D') (hB' (K' + D')) hKj hDj
  have hKιc : Kι.IsCartier := hKι.isCartier (hc K)
  have hKjc : Kj.IsCartier := hKj.isCartier (hc' K')
  have hDc : Dι.IsCartier := hDι.isCartier (hc D)
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback hsm ι hK hKι
  obtain ⟨eK'⟩ := nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback hsm' j hK' hKj
  rw [hιj] at eK
  have e₁ : (K + D).divisorialSheaf.restrict ι ≅ (Kι + Dι).divisorialSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback ι).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hc (K + D)) hsum).symm
  have e₂ : (K' + D').divisorialSheaf.restrict j ≅ (Kj + Dι).divisorialSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hc' (K' + D')) hsum').symm
  exact ⟨e₁ ≪≫ (hKιc.divisorialSheafTensorIso hDc).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso (eK ≪≫ eK'.symm)).app _ ≪≫
    hKjc.divisorialSheafTensorIso hDc ≪≫ e₂.symm⟩

/-- The tensor powers of `𝒪_X(E)` for a Cartier divisor `E`: `𝒪_X(E)^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPower_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.SheafOfModules.TensorPower.tensorPower
      (Stacks.SheafOfModules.sectionSiteRing X) (Stacks.SheafOfModules.sectionSiteSheaf X)
      E.divisorialSheaf (k : ℤ) ≅ (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨eqToIso (Stacks.SheafOfModules.TensorPower.tensorPower_zero _ _ _) ≪≫
      Divisor.divisorialSheafZeroIso.symm ≪≫ eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso _ _ _ (k : ℤ)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app E.divisorialSheaf ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- The tensor powers of `𝒪_X(E)` for a Cartier divisor `E`, in the spelling of
`Stacks.Ample.tensorPowModule`: `𝒪_X(E)^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPowModule_divisorialSheaf_iso {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {E : Divisor X} (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.Ample.tensorPowModule X E.divisorialSheaf (k : ℤ) ≅
      (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨Stacks.Ample.tensorPowModuleZeroIso X _ ≪≫ Divisor.divisorialSheafZeroIso.symm ≪≫
      eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ (k : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e
        (Stacks.Ample.tensorPowModuleOneIso X _) ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- **The twists of a divisorial sheaf by `𝒪(E)` are divisorial.** For Cartier divisors `D`,
`E` on a Noetherian normal scheme, `𝒪_X(D) ⊗ 𝒪_X(E)^{⊗ k} ≅ 𝒪_X(D + kE)`. -/
private theorem nonempty_twist_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {D E : Divisor X} (hD : D.IsCartier) (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (twist X E.divisorialSheaf D.divisorialSheaf (k : ℤ) ≅
      (D + k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_tensorPower_divisorialSheaf_iso hE k
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor _).obj D.divisorialSheaf).mapIso e ≪≫
    hD.divisorialSheafTensorIso (hE.nsmul k)⟩

/-- The nonvanishing open of the canonical section `1` of `𝒪_X(E)`, for `E ≥ 0` Cartier, is the
complement of the support of `E`. -/
private theorem nonvanishingOpen_divisorialSheafOneSection {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (hE0 : 0 ≤ E) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    ((Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) E.divisorialSheaf
      (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) E.divisorialSheaf
        (MMP.Threefold.Mori.oneSection hE0)) : X.Opens) : Set X) = (E.supp : Set X)ᶜ :=
  (Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop _ _).trans
    (MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 hE)

/-- **EGA-projective over an H-projective variety is H-projective.** Over a field every scheme
has an ample invertible sheaf on the base, so the two notions of projectivity agree there
(Stacks, Tag 0B45); a projective morphism `g` to an H-projective `Y` is therefore H-projective,
and so is `g ≫ s_Y`. -/
private theorem isProjectiveMorphism_of_isProjective {k : Type} [Field k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y) (hg : IsProjective g) :
    IsProjectiveMorphism (g ≫ sY) ∧ IsProjectiveMorphism g := by
  have hS : HasAmpleInvertibleSheaf (Spec (.of k)) :=
    (hasAmpleInvertibleSheaf_iff _).mpr (Stacks.HProjective.exists_isAmple_of_isAffine _)
  have hsY : IsProjective sY :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf sY hS).mpr hY
  have hc : IsProjective (g ≫ sY) := isProjective_comp_of_hasAmpleInvertibleSheaf g sY hS hsY hg
  have hcm := (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf _ hS).mp hc
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hY
  exact ⟨hcm, IsProjectiveMorphism.of_comp g sY hcm⟩

/-- The preimage of a quasi-compact open under a quasi-compact morphism is quasi-compact. -/
private theorem compactSpace_preimage {Y Z : Scheme.{0}} (f : Y ⟶ Z) [QuasiCompact f]
    {V : Z.Opens} (hV : IsCompact (V : Set Z)) : CompactSpace (f ⁻¹ᵁ V) :=
  isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV)

/-- The `i`-th coordinate section of `𝒪(1)` on `ℙⁿ_A` does not vanish exactly on the `i`-th
standard chart `D₊(Tᵢ)`. -/
private theorem mem_nonvanishingLocus_coordSectionTop_iff {A : Type} [CommRing A] (n : ℕ)
    (i : Fin (n + 1)) (z : projectiveSpaceOver n (Spec (.of A))) :
    z ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of A)))
        (MMP.Fourfold.coordSectionTop (A := A) n i) ↔
      z ∈ projectiveSpaceOver.standardChart n (Spec (.of A)) i :=
  MMP.Fourfold.mem_nonvanishingLocus_pullbackCoordSection_iff
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of A))) i z

/-- The data of a projective closure of an open `W ⊆ Y` adapted to a `ℚ`-divisor `B` on `Y`, in
continuation-passing style: a projective variety `Y₀ ⊇ W`, an invertible sheaf `H` on `Y₀` with a
section `t` whose nonvanishing locus is `W`, and a sequence `A_a ≅ A_0 ⊗ H^{⊗ a}` of invertible
sheaves on `Y₀`, ample for large `a`, with `A_0|_W ≅ 𝒪_Y(cB)|_W` for some `c > 0`. -/
private abbrev ProjectiveClosureData {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (W : Y.Opens) (B : QDivisor Y) (C : Prop) : Prop :=
  ∀ (c : ℕ) (_ : 0 < c) (Lc : Divisor Y) (_ : Divisor.toQDivisor Lc = (c : ℚ) • B)
    (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k s₀)
    (j : W.toScheme ⟶ Y₀) (_ : IsOpenImmersion j) (_ : j ≫ s₀ = W.ι ≫ sY)
    (Hb : Y₀.Modules) (_ : Stacks.Ample.IsInvertibleModule Y₀ Hb) (t : Γ(Hb, ⊤))
    (_ : Set.range j = Stacks.Ample.nonvanishingLocus Hb t)
    (A : ℕ → Y₀.Modules) (_ : ∀ a, Stacks.Ample.IsInvertibleModule Y₀ (A a)) (a₀ : ℕ)
    (_ : ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple Y₀ (A a))
    (_ : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y₀.toRingedSpace.sheaf).obj (A a)).obj Hb))
    (_ : Nonempty ((Scheme.Modules.pullback j).obj (A 0) ≅ Lc.divisorialSheaf.restrict W.ι)), C

/-- The conclusion of the compactification step, in continuation-passing style: a smooth
projective variety `X ⊇ W` whose boundary is the support of an effective divisor `E`, and a
decomposition `L + Δ` with `Δ` snc extending `B`, such that `L + mE + Δ` is nef and big for all
large `m`. -/
private abbrev CompactificationData {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (W : Y.Opens) (B : QDivisor Y) (C : Prop) : Prop :=
  ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (_ : IsSmoothScheme sX)
    (ι : W.toScheme ⟶ X) [IsOpenImmersion ι] (_ : ι ≫ sX = W.ι ≫ sY)
    (E L : Divisor X) (Δ : QDivisor X) (n₀ : ℕ) (_ : 0 ≤ E)
    (_ : Set.range ι = (E.supp : Set X)ᶜ) (_ : Δ.IsSNC sX)
    (_ : ∀ m : ℕ, n₀ ≤ m → (Divisor.toQDivisor (L + m • E) + Δ).IsNef k sX ∧
      (Divisor.toQDivisor (L + m • E) + Δ).IsBig k sX)
    (_ : ∀ P : MMP.Mori.PrimeDivisor W, (L + Δ.roundUp).coeff (openPrimeDivisor ι P) =
      B.roundUp.coeff (openPrimeDivisor W.ι P)), C

/-- **Projective closure of the preimage of an affine open.** For `f : Y ⟶ Z` projective, `B`
`f`-ample and `V ⊆ Z` affine with `W = f⁻¹(V)` nonempty, a high multiple `cB` of `B` is very
ample over `V`; the embedding `W ⟶ ℙᴹ_V ⊆ ℙᴹ × ℙʳ` by its sections, followed by the closure,
gives the data of `ProjectiveClosureData`. -/
private theorem exists_projectiveClosure
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f)
    (V : Z.Opens) (hV : IsAffineOpen V) (hW : Nonempty (f ⁻¹ᵁ V)) (C : Prop)
    (H : ProjectiveClosureData sY (f ⁻¹ᵁ V) B C) : C := by
  classical
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : IsAffine V.toScheme := hV
  -- Step 1: a multiple `L₀ = mB` that is ample on `W = f⁻¹(V)`
  obtain ⟨m, hm, L₀, hL₀c, hL₀B, hL₀amp⟩ := hB
  haveI := hL₀c.isInvertibleModule_divisorialSheaf
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple f L₀.divisorialSheaf :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _ inferInstance
      hL₀amp
  set LW := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L₀.divisorialSheaf with hLW
  haveI : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V) LW :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  have hampW : Stacks.Ample.IsAmple (f ⁻¹ᵁ V) LW := hrel.2 V hV
  -- Step 2: a power of `LW` embeds `W` into `ℙᴹ_V` over `V`
  have hT := Stacks.AmpleRelativeFiniteType.tfae_six (f ∣_ V) LW
  obtain ⟨N₀, hN₀, himm⟩ := (hT.out 1 6).mp hampW
  obtain ⟨M, i, hi, hif, ⟨eL⟩⟩ := himm N₀ le_rfl
  -- Step 3: `V` is a closed subscheme of the standard chart `𝔸ʳ ⊆ ℙʳ_k`
  obtain ⟨r, c₀, hc₀, hc₀s⟩ := exists_isClosedImmersion_affineSpace (V.ι ≫ sZ)
  set Pr := projectiveSpaceOver r (Spec (.of k)) with hPr
  set ach : 𝔸(ULift.{0} (Fin r); Spec (.of k)) ⟶ Pr := projectiveSpaceOver.affineChart r 0
    (Equiv.ulift.{0}.trans (finSuccAboveEquiv (0 : Fin (r + 1)))) (Spec (.of k)) with hach
  set φ : V.toScheme ⟶ Pr := c₀ ≫ ach with hφ
  -- Step 4: `W ⟶ ℙᴹ_V ⟶ ℙᴹ_{ℙʳ}` and its scheme-theoretic image `Y₀`
  set P := projectiveSpaceOver M Pr with hP
  set πP : P ⟶ Pr := pullback.fst (terminal.from Pr) (terminal.from (projectiveSpaceAtUniverse M))
    with hπP
  set πPr : Pr ⟶ Spec (.of k) := pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse r)) with hπPr
  set b : projectiveSpaceOver M V.toScheme ⟶ P := projectiveSpaceOverMap M φ with hb
  set e : (f ⁻¹ᵁ V).toScheme ⟶ P := i ≫ b with he
  haveI := hi
  haveI := hc₀
  haveI : IsOpenImmersion ach := by rw [hach]; infer_instance
  haveI : IsImmersion φ := by rw [hφ]; infer_instance
  haveI : IsImmersion b :=
    MorphismProperty.of_isPullback (P := @IsImmersion) (isPullback_projectiveSpaceOverMap M φ).flip
      ‹IsImmersion φ›
  haveI : IsImmersion e := inferInstance
  haveI := compactSpace_preimage f hV.isCompact
  haveI : IsProper πPr := isProper_projectiveSpaceOver r (Spec (.of k))
  haveI : IsProper πP := isProper_projectiveSpaceOver M Pr
  haveI : QuasiCompact e := quasiCompact_of_compactSpace e
  set Y₀ := e.image with hY₀
  set j : (f ⁻¹ᵁ V).toScheme ⟶ Y₀ := e.toImage with hj
  set ι' : Y₀ ⟶ P := e.imageι with hι'
  set q : Y₀ ⟶ Pr := ι' ≫ πP with hq
  set s₀ : Y₀ ⟶ Spec (.of k) := q ≫ πPr with hs₀
  have hPP : IsProjectiveMorphism (πP ≫ πPr) :=
    IsProjectiveMorphism.comp ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩
      ⟨r, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hs₀' : s₀ = ι' ≫ πP ≫ πPr := by rw [hs₀, hq, Category.assoc]
  obtain ⟨hs₀p, -⟩ := isProjectiveMorphism_of_isProjective (πP ≫ πPr) hPP ι'
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite ι')
  have hY₀ : MMP.Mori.IsProjectiveVariety k s₀ := by
    rw [hs₀']
    haveI : IsProper (ι' ≫ πP ≫ πPr) := isProper_of_isProjectiveMorphism _ hs₀p
    haveI : IsIntegral (f ⁻¹ᵁ V).toScheme := inferInstance
    exact (MMP.Mori.isProjectiveVariety_iff k _).2
      ⟨@AlgebraicGeometry.IsVariety.mk k _ _ _ inferInstance inferInstance inferInstance
        inferInstance, hs₀p⟩
  have heπ : e ≫ πP = (f ∣_ V) ≫ φ := by
    rw [he, Category.assoc, hb, hπP, projectiveSpaceOverMap_fst, ← Category.assoc, hif]
  have hφπ : φ ≫ πPr = V.ι ≫ sZ := by
    rw [hφ, Category.assoc, hπPr]
    erw [projectiveSpaceOver.affineChart_over]
    exact hc₀s
  have hjs : j ≫ s₀ = (f ⁻¹ᵁ V).ι ≫ sY := by
    rw [hs₀, hq, ← Category.assoc, ← Category.assoc, hj, hι', Scheme.Hom.toImage_imageι,
      heπ, Category.assoc, hφπ, ← Category.assoc, morphismRestrict_ι, Category.assoc, hfs]
  -- the boundary section `t = q^* x₀`
  set Hb : Y₀.Modules := (Scheme.Modules.pullback q).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) with hHb
  haveI hHbi : Stacks.Ample.IsInvertibleModule Y₀ Hb :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  set t : Γ(Hb, ⊤) := pullbackGlobalSections q _ (MMP.Fourfold.coordSectionTop (A := k) r 0)
    with ht
  have hrange : Set.range j = Stacks.Ample.nonvanishingLocus Hb t := by
    have hNV : Stacks.Ample.nonvanishingLocus Hb t = q.base ⁻¹' Set.range ach.base := by
      ext y
      rw [Set.mem_preimage, ht, MMP.Fourfold.mem_nonvanishingLocus_pullbackGlobalSections_iff,
        mem_nonvanishingLocus_coordSectionTop_iff, hach, projectiveSpaceOver.range_affineChart]
      rfl
    rw [hNV]
    have hje : j ≫ ι' = e := by rw [hj, hι']; exact Scheme.Hom.toImage_imageι e
    have hjq : j ≫ q = ((f ∣_ V) ≫ c₀) ≫ ach := by
      rw [hq, ← Category.assoc, hje, heπ, hφ, Category.assoc]
    set U₀ : Pr.Opens := ach.opensRange with hU₀
    set Q : Y₀.Opens := q ⁻¹ᵁ U₀ with hQ
    have hjQ : Set.range j.base ⊆ Set.range Q.ι.base := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      change q.base (j.base w) ∈ Set.range ach.base
      rw [← Scheme.Hom.comp_apply, hjq, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    set j' := IsOpenImmersion.lift Q.ι j hjQ with hj'
    have hj'f : j' ≫ Q.ι = j := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion j' := by
      haveI : IsOpenImmersion (j' ≫ Q.ι) := by rw [hj'f]; infer_instance
      exact IsOpenImmersion.of_comp j' Q.ι
    have hcomp : j' ≫ (q ∣_ U₀) = ((f ∣_ V) ≫ c₀) ≫ ach.isoOpensRange.hom := by
      rw [← cancel_mono U₀.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'f,
        Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hjq]
    haveI : IsSeparated q := by rw [hq]; infer_instance
    haveI : IsProper (j' ≫ (q ∣_ U₀)) := by rw [hcomp]; infer_instance
    haveI : IsProper j' := IsProper.of_comp j' (q ∣_ U₀)
    haveI : IsIntegral Y₀ := hY₀.toIsVariety.toIsIntegral
    obtain ⟨w⟩ := hW
    haveI : Nonempty Q := ⟨j' w⟩
    have hcl : IsClopen (Set.range j'.base) :=
      ⟨j'.isClosedMap.isClosed_range, j'.isOpenEmbedding.isOpen_range⟩
    have huniv : Set.range j'.base = Set.univ := by
      rcases isClopen_iff.mp hcl with h | h
      · exact absurd h (Set.Nonempty.ne_empty ⟨_, w, rfl⟩)
      · exact h
    rw [← hj'f, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, huniv, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  -- the ample family `A_a = 𝒪(1) ⊗ q^* 𝒪(a)` restricted to `Y₀`
  set A : ℕ → Y₀.Modules := fun a => (Scheme.Modules.pullback ι').obj
    (Stacks.AmplePullbackPart1.tensorPullbackPowModule πP
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) a) with hA
  have hAi : ∀ a, Stacks.Ample.IsInvertibleModule Y₀ (A a) := fun a =>
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  obtain ⟨a₀, hamp⟩ : ∃ a₀ : ℕ, ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple Y₀ (A a) := by
    obtain ⟨a₀, ha₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isAmple πP _ _
      (Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf M Pr)
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf (n := r) (S := Spec (.of k)))
    refine ⟨a₀, fun a ha => ?_⟩
    exact Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding ι' _
      (ha₀ a ha) (Or.inl ⟨inferInstance, inferInstance⟩)
  have eA : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y₀.toRingedSpace.sheaf).obj (A a)).obj Hb) := by
    intro a
    set O1M := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr
    set O1r := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))
    have e1 : Stacks.Ample.tensorPowModule Pr O1r ((a + 1 : ℕ) : ℤ) ≅
        Stacks.RelativeVeryAmple.tensorModules Pr (Stacks.Ample.tensorPowModule Pr O1r (a : ℤ))
          O1r :=
      eqToIso (by push_cast; rfl) ≪≫ (Stacks.Ample.tensorPowModuleAddIso Pr O1r a 1).symm ≪≫
        Stacks.RelativeVeryAmple.tensorModulesMapIso Pr (Iso.refl _)
          (Stacks.Ample.tensorPowModuleOneIso Pr O1r)
    have e2 := (Scheme.Modules.pullback πP).mapIso e1 ≪≫
      Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso πP _ _
    have e3 := Stacks.RelativeVeryAmple.tensorModulesMapIso P (Iso.refl O1M) e2 ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesAssociator P _ _ _).symm
    have e4 := (Scheme.Modules.pullback ι').mapIso e3 ≪≫
      Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso ι' _ _
    exact ⟨e4 ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso Y₀ (Iso.refl _)
      ((Scheme.Modules.pullbackComp ι' πP).app O1r)⟩
  have eA0 : Nonempty ((Scheme.Modules.pullback j).obj (A 0) ≅
      (N₀ • L₀).divisorialSheaf.restrict (f ⁻¹ᵁ V).ι) := by
    obtain ⟨eP⟩ := nonempty_tensorPowModule_divisorialSheaf_iso hL₀c N₀
    set O1M := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr
    set O1r := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))
    have hje : j ≫ ι' = e := by rw [hj, hι']; exact Scheme.Hom.toImage_imageι e
    have hbs : b ≫ projectiveSpaceOver.toIntegralAtUniverse M Pr =
        projectiveSpaceOver.toIntegralAtUniverse M V.toScheme := projectiveSpaceOverMap_snd M φ
    have eT : Stacks.RelativeVeryAmple.tensorModules P O1M ((Scheme.Modules.pullback πP).obj
        (Stacks.Ample.tensorPowModule Pr O1r ((0 : ℕ) : ℤ))) ≅ O1M :=
      Stacks.RelativeVeryAmple.tensorModulesMapIso P (Iso.refl _)
        ((Scheme.Modules.pullback πP).mapIso (Stacks.Ample.tensorPowModuleZeroIso Pr O1r) ≪≫
          Stacks.PullbackAlgebra.pullbackUnitIso πP.toLRSHom.toShHom) ≪≫
        Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor P O1M
    have eb : (Scheme.Modules.pullback b).obj O1M ≅
        Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M V.toScheme :=
      (Scheme.Modules.pullbackComp b (projectiveSpaceOver.toIntegralAtUniverse M Pr)).app _ ≪≫
        eqToIso (by rw [hbs])
    exact ⟨(Scheme.Modules.pullbackComp j ι').app _ ≪≫ eqToIso (by rw [hje]; rfl) ≪≫
      (Scheme.Modules.pullback e).mapIso eT ≪≫ eqToIso (by rw [he]) ≪≫
      ((Scheme.Modules.pullbackComp i b).app O1M).symm ≪≫
      (Scheme.Modules.pullback i).mapIso eb ≪≫ eL.symm ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι
        L₀.divisorialSheaf N₀).symm ≪≫
      (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).mapIso eP ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _).symm⟩
  refine H (N₀ * m) (Nat.mul_pos (by omega) hm) (N₀ • L₀) ?_ Y₀ s₀ hY₀ j inferInstance hjs Hb hHbi
    t hrange A hAi a₀ hamp eA eA0
  rw [map_nsmul, hL₀B]
  ext P
  change (N₀ • ((m : ℚ) • B)) P = (((N₀ * m : ℕ) : ℚ) • B) P
  simp only [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  ring

/-- **Lifting an open immersion along a morphism that is an isomorphism over an open.** If
`g : X' ⟶ X` restricts to an isomorphism over `U` and `j : W ⟶ X` is an open immersion with image
in `U`, then `j` lifts to an open immersion `ι : W ⟶ X'` with image `g⁻¹(j(W))`. -/
private theorem exists_isOpenImmersion_lift {W X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens)
    [IsIso (g ∣_ U)] (j : W ⟶ X) [IsOpenImmersion j] (hj : Set.range j ⊆ U) :
    ∃ ι : W ⟶ X', IsOpenImmersion ι ∧ ι ≫ g = j ∧ Set.range ι = g ⁻¹' Set.range j := by
  have hjU : Set.range j ⊆ Set.range U.ι := by simpa using hj
  set j' : W ⟶ U.toScheme := IsOpenImmersion.lift U.ι j hjU
  have hj' : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion j' := by
    have : IsOpenImmersion (j' ≫ U.ι) := by rw [hj']; infer_instance
    exact IsOpenImmersion.of_comp j' U.ι
  have hfac : inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι ≫ g = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  refine ⟨j' ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hfac, hj']
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hfac, hj']
    · rintro ⟨w, hw⟩
      have hxU : x ∈ g ⁻¹ᵁ U := by
        change g x ∈ U
        rw [← hw]
        exact hj ⟨w, rfl⟩
      let y : (g ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have hy : (g ⁻¹ᵁ U).ι y = x := rfl
      have h1 : (g ∣_ U) y = j' w := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hy,
          ← Scheme.Hom.comp_apply, hj']
        exact hw.symm
      have h2 : inv (g ∣_ U) (j' w) = y := by
        rw [← h1, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
        rfl
      refine ⟨w, ?_⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2, hy]

/-- **The effective divisor of a section.** On an integral Noetherian normal scheme on which every
divisor is Cartier, a section `t` of an invertible sheaf `L` that does not vanish identically is
the canonical section `1` of `𝒪_X(E)` for an effective divisor `E` with `𝒪_X(E) ≅ L`; the
complement of `Supp E` is the nonvanishing locus of `t`. -/
private theorem exists_divisor_of_section {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (t : Γ(L, ⊤))
    (ht : (Stacks.Ample.nonvanishingLocus L t).Nonempty) :
    ∃ E : Divisor X, 0 ≤ E ∧ Nonempty (E.divisorialSheaf ≅ L) ∧
      (E.supp : Set X)ᶜ = Stacks.Ample.nonvanishingLocus L t := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  obtain ⟨D, ⟨e⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible L
  set sΓ : Γ(D.divisorialSheaf, ⊤) := e.inv.app ⊤ t with hsΓ
  have hts : e.hom.app ⊤ sΓ = t := by
    rw [hsΓ, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  have hsne : sΓ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := ht
    rw [← hts, h, map_zero, Stacks.Ample.nonvanishingLocus_zero] at hx
    exact hx
  set σ : D.divisorialSubmodule ⊤ := sΓ
  let ψ₀ : RationalFunctions X := fun Z => σ.1 ⟨Z, trivial⟩
  have hsub : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hψ₀ : ∀ Z, ψ₀ Z ≠ 0 := by
    intro Z hZ
    apply hsne
    change σ = 0
    apply Subtype.ext
    funext Z'
    obtain rfl : Z' = ⟨Z, trivial⟩ := Subtype.ext (Subsingleton.elim _ _)
    exact hZ
  have hunit : IsUnit ψ₀ := by
    rw [Pi.isUnit_iff]
    intro Z
    obtain ⟨b, hb⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel (hψ₀ Z)
    exact IsUnit.of_mul_eq_one _ hb
  set ψ := hunit.unit
  set E : Divisor X := D + principalDivisor ψ with hE
  have hEc : ∀ P : MMP.Mori.PrimeDivisor X, E.coeff P = D.coeff P + P.ord ψ := fun P => by
    rw [hE, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hE0 : 0 ≤ E := by
    intro P
    change 0 ≤ E.coeff P
    rw [hEc]
    have h := σ.2 P ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl, trivial⟩
    rcases h with h | h
    · exact absurd h (hψ₀ _)
    · have h' : WithZero.exp (-D.coeff P) ≤ WithZero.exp (P.ord ψ) := by
        rwa [← P.valuation_component ψ]
      rw [WithZero.exp_le_exp] at h'
      linarith
  let eM : E.divisorialSheaf ≅ D.divisorialSheaf := Divisor.divisorialSheafMulIso ψ hEc
  have h1 : eM.hom.app ⊤ (MMP.Threefold.Mori.oneSection hE0) = sΓ := by
    change (⟨_, _⟩ : D.divisorialSubmodule ⊤) = σ
    apply Subtype.ext
    funext Z
    change (ψ : RationalFunctions X) Z.1 *
      ((Divisor.structureSheafToDivisorialSheaf hE0).app ⊤ (1 : Γ(X, ⊤))).1 Z = σ.1 Z
    rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
    change (ψ : RationalFunctions X) Z.1 * 1 = σ.1 Z
    rw [mul_one]
    rfl
  refine ⟨E, hE0, ⟨eM ≪≫ e⟩, ?_⟩
  rw [← MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 (hcart E),
    ← Stacks.Ample.nonvanishingLocus_congr (eM ≪≫ e) (MMP.Threefold.Mori.oneSection hE0)]
  congr 1
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h1, hts]

/-- **Rational functions lift along an open immersion.** For an open immersion `ι : W ⟶ X` of
integral schemes, every unit of `K(W)` is the pull-back of a unit of `K(X)`: the stalk map of `ι`
at the generic point of `W` is an isomorphism. -/
private theorem exists_pullbackRationalFunction_eq {W X : Scheme.{0}} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (ι : W ⟶ X) [IsOpenImmersion ι]
    (hφ' : ∀ (φ : (RationalFunctions X)ˣ) (Z : irreducibleComponents W),
      ι (componentGenericPoint W Z) ∉ (principalDivisor φ).supp)
    (ψ : (RationalFunctions W)ˣ) :
    ∃ φ : (RationalFunctions X)ˣ, pullbackRationalFunction ι φ (hφ' φ) = ψ := by
  have hsubW : Subsingleton (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  set η := componentGenericPoint W Z₀ with hη
  have hmem : ∀ W' : irreducibleComponents X, ι η ∈ W'.1 := fun W' => by
    have h : W'.1 ∈ ({Set.univ} : Set (Set X)) := by
      rw [← irreducibleComponents_eq_singleton]; exact W'.2
    rw [Set.mem_singleton_iff] at h
    rw [h]; trivial
  set a : (X.presheaf.stalk (ι η))ˣ :=
    Units.map (inv (ι.stalkMap η)).hom.toMonoidHom ((RationalFunctions.unitsEquiv W ψ) Z₀)
  refine ⟨(RationalFunctions.unitsEquiv X).symm
    (fun W' => Units.map (stalkToRationalFunctions X (hmem W')).hom.toMonoidHom a), ?_⟩
  apply (RationalFunctions.unitsEquiv W).injective
  funext Z
  obtain rfl : Z = Z₀ := Subsingleton.elim _ _
  obtain ⟨W₀⟩ : Nonempty (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  simp only [pullbackRationalFunction, MulEquiv.apply_symm_apply]
  rw [pullbackComponent_eq (hφ' _) (Divisor.isLocalEquation_principalDivisor _ ⊤) trivial
    (hmem W₀) a rfl]
  apply Units.ext
  change (ι.stalkMap η).hom ((inv (ι.stalkMap η)).hom _) = _
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
  rfl

/-- **Extending a divisor from an open subscheme up to linear equivalence.** Let `ι : W ⟶ X` be
an open immersion of integral Noetherian normal schemes and `G` a Cartier divisor on `X` whose
pull-back to `W` has divisorial sheaf isomorphic to `𝒪_W(T)`. Then some `G' ∼ G` has coefficient
`T(P)` along the prime divisor of `X` through every prime divisor `P` of `W`. -/
private theorem exists_linearlyEquivalent_coeff_eq {W X : Scheme.{0}} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] (ι : W ⟶ X) [IsOpenImmersion ι] {G : Divisor X} (hG : G.IsCartier)
    (T : Divisor W) (e : Nonempty ((Scheme.Modules.pullback ι).obj G.divisorialSheaf ≅
      T.divisorialSheaf)) :
    ∃ G' : Divisor X, Nonempty (G'.divisorialSheaf ≅ G.divisorialSheaf) ∧
      ∀ P : MMP.Mori.PrimeDivisor W, G'.coeff (openPrimeDivisor ι P) = T.coeff P := by
  haveI : IsDominant ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ι
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant ι
  obtain ⟨Gι, hGι⟩ := hG.exists_isPullback (hB G)
  obtain ⟨e⟩ := e
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    ((Divisor.IsPullback.divisorialSheafIso (hBc := hG) hGι) ≪≫ e)
  obtain ⟨φ, hφ⟩ := exists_pullbackRationalFunction_eq ι (fun φ => hB _) ψ
  refine ⟨G - principalDivisor φ, ⟨Divisor.LinearlyEquivalent.divisorialSheafIso
    ⟨φ⁻¹, by rw [MMP.Mori.principalDivisor_inv]; abel⟩⟩, fun P => ?_⟩
  have hpr := Divisor.isPullback_principalDivisor (f := ι) φ (hB _)
  rw [hφ] at hpr
  rw [DivisorWithCoeffs.coeff_sub, ← coeff_of_isPullback_of_isOpenImmersion ι hG hGι,
    ← coeff_of_isPullback_of_isOpenImmersion ι (Divisor.isCartier_principalDivisor φ) hpr]
  have := congrArg (DivisorWithCoeffs.coeff · P) hψ
  simp only [DivisorWithCoeffs.coeff_sub] at this
  rw [← this]
  ring

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData}
    (hF : MMP.Resolution.IsSNCFamily s F)
    {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X)
    (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A prime divisor contained in a closed set of pure codimension one is one of its irreducible
components. -/
private theorem mem_componentsOf_of_support_subset {X : Scheme.{0}} {S : Set X} (hS : IsClosed S)
    (hpure : MMP.Mori.IsPureCodimOne (⟨S, hS⟩ : TopologicalSpace.Closeds X))
    (P : MMP.Mori.PrimeDivisor X) (hP : (P.support : Set X) ⊆ S) :
    (P.support : Set X) ∈ MMP.Resolution.componentsOf S := by
  have hηS : P.genericPoint ∈ S :=
    hP (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  obtain ⟨W, hW, hηW⟩ := MMP.Resolution.exists_mem_componentsOf hηS
  have hWcl : IsClosed W := MMP.Resolution.isClosed_of_mem_componentsOf hS hW
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hWcl
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X => (W' : Set X) ⊆ S)
      ⟨W, hW.1.1, hWcl⟩ :=
    ⟨hW.1.2, fun W' hW' hle => hW.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hcod := hpure _ hmax
  have hξc : Order.coheight ξ = 1 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    convert hcod using 2
    ext1
    exact hξ.def
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξc with hQ
  have hQs : (Q.support : Set X) = W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hξ.def
  have hPQ : (P.support : Set X) ⊆ Q.support := by
    rw [hQs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηW) hWcl
  have hPQe := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ
  rw [hPQe, hQs]
  exact hW

/-- A divisor all of whose components lie in an snc closed subset is snc. -/
private theorem isSNC_of_isSNCClosedSubset {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] {S : Set X} (hS : MMP.Resolution.IsSNCClosedSubset sX S)
    {R : Type*} [Zero R] (Δ : MMP.Mori.DivisorWithCoeffs R X)
    (hΔ : ∀ P ∈ Δ.support, (P.support : Set X) ⊆ S) : Δ.IsSNC sX := by
  obtain ⟨hScl, hS0 | ⟨hpure, -, hfam⟩⟩ := hS
  · have hempty : ∀ P ∈ Δ.support, False := fun P hP => by
      have := hΔ P hP (show P.genericPoint ∈ P.support by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
      rw [hS0] at this
      exact this
    refine ⟨fun P hP => (hempty P hP).elim, fun x => ?_⟩
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
    exact ⟨n, z, fun P => (hempty P.1 P.2.1).elim, hz, fun P => (hempty P.1 P.2.1).elim,
      fun P => (hempty P.1 P.2.1).elim⟩
  · exact isSNC_of_isSNCFamily hfam Δ fun P hP =>
      ⟨⟨_, mem_componentsOf_of_support_subset hScl hpure P (hΔ P hP)⟩,
        MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf _ P rfl⟩

/-- The local snc condition at a point only depends on the support of the divisor. -/
private theorem sncStalk_of_forall_ne_zero_iff {R R' : Type*} [Zero R] [Zero R'] {W : Scheme.{0}}
    (D : MMP.Mori.DivisorWithCoeffs R W) (D' : MMP.Mori.DivisorWithCoeffs R' W)
    (h : ∀ P, D P ≠ 0 ↔ D' P ≠ 0) (w : W)
    (hD : ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk w)
      (jj : {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ w ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, AlgebraicGeometry.IdealSheafData.stalk E.1.idealSheaf w = Ideal.span {z (jj E)}) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk w)
      (jj : {E : MMP.Mori.PrimeDivisor W // E ∈ D'.support ∧ w ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, AlgebraicGeometry.IdealSheafData.stalk E.1.idealSheaf w = Ideal.span {z (jj E)} := by
  have hs : D.support = D'.support := Finset.ext fun P => by
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]; exact h P
  rw [← hs]
  exact hD

/-- **Transport of the snc condition to the image of an open immersion.** Let `ι : W ⟶ X` and
`j : W ⟶ Y` be open immersions over `k`, `F` an snc divisor on `Y` and `D` a finite set of prime
divisors of `X` whose members through `ι(W)` are exactly the closures of the components of
`F|_W`. Then `D` restricted to `ι(W)` is an snc closed subset. -/
private theorem isSNCClosedSubset_opensRange {k : Type} [Field k] {W X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (ι : W ⟶ X) [IsOpenImmersion ι] (jY : W ⟶ Y) [IsOpenImmersion jY]
    (h : ι ≫ sX = jY ≫ sY) {R : Type*} [Zero R] (F : MMP.Mori.DivisorWithCoeffs R Y)
    (hF : F.IsSNC sY) (D : Finset (MMP.Mori.PrimeDivisor X))
    (hD : ∀ Q : MMP.Mori.PrimeDivisor W,
      openPrimeDivisor ι Q ∈ D ↔ F.coeff (openPrimeDivisor jY Q) ≠ 0) :
    MMP.Resolution.IsSNCClosedSubset (ι.opensRange.ι ≫ sX)
      (ι.opensRange.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  set U := ι.opensRange with hU
  set Rd : Divisor X := ∑ E ∈ D, Finsupp.single E (1 : ℤ) with hRd
  have hRd' : ∀ P, Rd P ≠ 0 ↔ P ∈ D := fun P => by
    rw [hRd, Finset.sum_apply']; simp [Finsupp.single_apply]
  set T : Divisor U := Rd.restrictOpen U with hT
  have hTc : ∀ Fc, T Fc = Rd (OpenWeilRestriction.primeDivisorMap U.ι Fc) := fun _ => rfl
  have hrangeU : Set.range U.ι = Set.range ι := by rw [Scheme.Opens.range_ι]; rfl
  have hlofp : ∀ {Z : Scheme.{0}} (I : Z.IdealSheafData) (s : Z ⟶ Spec (.of k))
      [LocallyOfFiniteType s], LocallyOfFinitePresentation (I.subschemeι ≫ s) := fun I s _ =>
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := I.subschemeι ≫ s)).mpr
      inferInstance
  have hTQ : ∀ Fc : MMP.Mori.PrimeDivisor U, Fc ∈ T.support →
      ∃ Q : MMP.Mori.PrimeDivisor W,
        OpenWeilRestriction.primeDivisorMap U.ι Fc = openPrimeDivisor ι Q ∧
          openPrimeDivisor ι Q ∈ D := by
    intro Fc hFc
    have hPD : OpenWeilRestriction.primeDivisorMap U.ι Fc ∈ D :=
      (hRd' _).1 (by rw [← hTc]; exact Finsupp.mem_support_iff.mp hFc)
    obtain ⟨w, hw⟩ : U.ι Fc.genericPoint ∈ Set.range ι := by
      rw [← hrangeU]; exact ⟨_, rfl⟩
    have hmem : ι w ∈ (OpenWeilRestriction.primeDivisorMap U.ι Fc).support := by
      rw [hw, MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      ι _ w hmem
    refine ⟨Q, by rw [openPrimeDivisor_eq_primeDivisorMap, hQ], ?_⟩
    rw [openPrimeDivisor_eq_primeDivisorMap, hQ]
    exact hPD
  have hTsnc : T.IsSNC (U.ι ≫ sX) := by
    refine ⟨fun Fc hFc => ?_, fun x => ?_⟩
    · obtain ⟨Q, hPQ, hQD⟩ := hTQ Fc hFc
      have hFQ : F.coeff (openPrimeDivisor jY Q) ≠ 0 := (hD Q).1 hQD
      have hsmY := hF.1 (openPrimeDivisor jY Q) (Finsupp.mem_support_iff.mpr hFQ)
      haveI := hlofp (openPrimeDivisor jY Q).idealSheaf sY
      haveI := hlofp (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf sX
      have h1 : MMP.Mori.IsSmoothScheme (Q.idealSheaf.subschemeι ≫ jY ≫ sY) := by
        refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff jY sY
          (openPrimeDivisor jY Q).idealSheaf Q.idealSheaf (by
            rw [openPrimeDivisor_eq_primeDivisorMap]
            exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap jY Q)).2
          fun z _ => ?_
        rw [← MMP.Mori.smoothLocus_eq_smoothLocus, hsmY]; trivial
      rw [← h] at h1
      have h2 := (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff ι sX
        (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf Q.idealSheaf (by
          rw [hPQ, openPrimeDivisor_eq_primeDivisorMap]
          exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap ι Q)).1 h1
      exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sX
        (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf Fc.idealSheaf
        (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι Fc)).2
        fun z hz => h2 z (by rw [← hrangeU]; exact hz)
    · obtain ⟨w, hw⟩ := x.2
      have hx : U.ι x = ι w := hw.symm
      refine (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι Rd x).2 ?_
      rw [hx]
      refine (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff ι Rd w).1 ?_
      have hY := (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff jY F w).2
        (hF.2 (jY w))
      refine sncStalk_of_forall_ne_zero_iff _ _ (fun Q => ?_) w hY
      rw [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply,
        ← openPrimeDivisor_eq_primeDivisorMap, ← openPrimeDivisor_eq_primeDivisorMap, hRd', hD Q]
      rfl
  have hset : U.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) =
      ⋃ Fc ∈ T.support, (Fc.support : Set U) := by
    ext x
    simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨P, hP, hx⟩
      obtain ⟨Fc, hFc⟩ :=
        MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support U.ι P x hx
      refine ⟨Fc, ?_, ?_⟩
      · rw [Finsupp.mem_support_iff, hTc, hFc]
        exact (hRd' P).2 hP
      · rwa [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι, hFc]
    · rintro ⟨Fc, hFc, hx⟩
      exact ⟨_, (hRd' _).1 (by rw [← hTc]; exact Finsupp.mem_support_iff.mp hFc),
        (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι Fc x).2 hx⟩
  rw [hset]
  exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hTsnc

/-- A morphism `g` restricting, along open immersions `ι` and `j` from a nonempty scheme with
`ι ≫ g = j`, to an isomorphism `ι(W) ≅ j(W)` is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {W X Y : Scheme.{0}} [Nonempty W]
    [IrreducibleSpace X] [IrreducibleSpace Y] (ι : W ⟶ X) [IsOpenImmersion ι] (j : W ⟶ Y)
    [IsOpenImmersion j] (g : X ⟶ Y) (hιg : ι ≫ g = j) : IsBirationalMorphism g := by
  have hle : ι.opensRange ≤ g ⁻¹ᵁ j.opensRange := by
    rintro _ ⟨w, rfl⟩
    exact ⟨w, by rw [← Scheme.Hom.comp_apply, hιg]⟩
  have hcomp : ι.isoOpensRange.hom ≫ g.resLE j.opensRange ι.opensRange hle =
      j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, hιg, Scheme.Hom.isoOpensRange_hom_ι]
  have hres : g.resLE j.opensRange ι.opensRange hle =
      inv ι.isoOpensRange.hom ≫ j.isoOpensRange.hom := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  have : IsIso (g.resLE j.opensRange ι.opensRange hle) := by
    rw [hres]
    infer_instance
  obtain ⟨w⟩ : Nonempty W := inferInstance
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (show ((ι.opensRange : X.Opens) : Set X).Nonempty from ⟨ι w, w, rfl⟩)
    (show ((j.opensRange : Y.Opens) : Set Y).Nonempty from ⟨j w, w, rfl⟩) hle this

/-- For `B̄ = G / c`, the divisor `G + (c m) E` is `c` times `⌊B̄⌋ + m E + {B̄}`. -/
private theorem toQDivisor_add_mul_nsmul {X : Scheme.{0}} (G E : Divisor X) {c : ℕ}
    (hc : (c : ℚ) ≠ 0) (m : ℕ) {Bb : QDivisor X} (hBb : Bb = (c : ℚ)⁻¹ • Divisor.toQDivisor G)
    (hdecomp : Divisor.toQDivisor Bb.roundDown + Bb.fract = Bb) :
    Divisor.toQDivisor (G + (c * m) • E) =
      (c : ℚ) • (Divisor.toQDivisor (Bb.roundDown + m • E) + Bb.fract) := by
  ext P
  have h : ((Bb.roundDown P : ℤ) : ℚ) + Bb.fract P = Bb P :=
    congrArg (fun D : QDivisor X => D P) hdecomp
  have hb : Bb P = (c : ℚ)⁻¹ * (G P : ℚ) := by
    subst hBb
    rfl
  change (((G + (c * m) • E) P : ℤ) : ℚ) =
    (c : ℚ) * ((((Bb.roundDown + m • E) P : ℤ) : ℚ) + Bb.fract P)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
    Int.cast_natCast]
  rw [add_right_comm, h, hb]
  field_simp
  push_cast
  ring

/-- **Resolution of a projective closure.** From the data of `ProjectiveClosureData`, a strong
resolution of `Y₀` followed by a log resolution of the closures of the components of `{B}` and
of the boundary, both isomorphisms over `W`, gives the data of `CompactificationData`. -/
private theorem exists_compactification_of_projectiveClosure
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (W : Y.Opens) [Nonempty W] [CompactSpace W]
    (B : QDivisor Y) (hBf : B.fract.IsSNC sY) (C : Prop)
    (H : CompactificationData sY W B C) : ProjectiveClosureData sY W B C := by
  classical
  intro c hc Lc hLc Y₀ s₀ hY₀ j hjo hj Hb hHb t ht A hA a₀ hamp eA eA0
  haveI := hjo
  haveI := hHb
  haveI := hY₀
  have hY₀v : AlgebraicGeometry.IsVariety k s₀ := hY₀.toIsVariety
  haveI := hY₀v
  haveI : IsIntegral Y₀ := hY₀v.toIsIntegral
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  -- the image of `W` lies in the smooth locus of `Y₀`
  have hsY : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).1 hsm
  have hWsm : Set.range j ⊆ (smoothLocus s₀ : Set Y₀) := by
    have hU : Smooth (j.opensRange.ι ≫ s₀) := by
      rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, hj]
      infer_instance
    exact fun _ hx => (le_sSup hU : j.opensRange ≤ smoothLocus s₀) hx
  -- Step 1: a strong resolution `g₁ : X₁ ⟶ Y₀`, an isomorphism over the smooth locus
  obtain ⟨X₁, g₁, hX₁v, hg₁p, hg₁b, hX₁sm, hg₁iso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution s₀ hY₀v
  haveI := hg₁iso
  obtain ⟨ι₁, hι₁o, hι₁, hι₁r⟩ := exists_isOpenImmersion_lift g₁ (smoothLocus s₀) j hWsm
  haveI := hι₁o
  haveI := hX₁v
  haveI : IsIntegral X₁ := hX₁v.toIsIntegral
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ s₀)
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ s₀)
  haveI : Smooth (g₁ ≫ s₀) := (MMP.Mori.isSmoothScheme_iff _).1 hX₁sm
  haveI : IsNormal X₁ := isNormal_of_smooth_over_field (g₁ ≫ s₀)
  have hcart₁ : ∀ D : Divisor X₁, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hX₁sm
  -- the boundary divisor `E₁` on `X₁`, with `X₁ ∖ Supp E₁ = ι₁(W)`
  haveI : Stacks.Ample.IsInvertibleModule X₁ ((Scheme.Modules.pullback g₁).obj Hb) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g₁ Hb
  have hrange₁ : Set.range ι₁ = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback g₁).obj Hb) (pullbackGlobalSections g₁ Hb t) := by
    rw [hι₁r, ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ht]
  obtain ⟨E₁, hE₁0, -, hE₁r⟩ := exists_divisor_of_section hcart₁ _
    (pullbackGlobalSections g₁ Hb t) (by rw [← hrange₁]; exact Set.range_nonempty _)
  -- the closures in `X₁` of the components of `{B}` meeting `W`
  have hinjW : Function.Injective (openPrimeDivisor W.ι) := openPrimeDivisor_injective W.ι
  set S : Set (MMP.Mori.PrimeDivisor W) := {Q | B.fract.coeff (openPrimeDivisor W.ι Q) ≠ 0}
  have hS : S.Finite := (B.fract.support.finite_toSet.preimage hinjW.injOn).subset
    fun Q hQ => Finsupp.mem_support_iff.mpr hQ
  set D : Finset (MMP.Mori.PrimeDivisor X₁) := hS.toFinset.image (openPrimeDivisor ι₁) ∪ E₁.support
  -- Step 2: a log resolution of `(X₁, D)`, an isomorphism over `ι₁(W)`
  have hX₁n : MMP.Mori.IsNormalVariety k (g₁ ≫ s₀) := ⟨hX₁v, inferInstance⟩
  obtain ⟨Yb, f₂, hres, -, hsnc, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (g₁ ≫ s₀) hX₁n D
  have hU : IsIso (f₂ ∣_ ι₁.opensRange) := hiso _ ((MMP.Mori.isSmoothScheme_iff _).2 inferInstance)
    (isSNCClosedSubset_opensRange (g₁ ≫ s₀) sY ι₁ W.ι (by rw [← Category.assoc, hι₁, hj]) B.fract
      hBf D fun Q => ⟨fun hQ => by
        rcases Finset.mem_union.mp hQ with hQ | hQ
        · obtain ⟨Q', hQ', hQQ'⟩ := Finset.mem_image.mp hQ
          rw [← openPrimeDivisor_injective ι₁ hQQ']
          exact hS.mem_toFinset.mp hQ'
        · exact absurd (coeff_openPrimeDivisor_eq_zero ι₁ (hrange₁.trans hE₁r.symm) Q)
            (Finsupp.mem_support_iff.mp hQ),
        fun hQ => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Q, hS.mem_toFinset.mpr hQ, rfl⟩)⟩)
  obtain ⟨ι, hιo, hι, hιr⟩ := exists_isOpenImmersion_lift f₂ ι₁.opensRange ι₁ (by simp)
  haveI := hιo
  set g : Yb ⟶ Y₀ := f₂ ≫ g₁ with hg
  have hιg : ι ≫ g = j := by rw [hg, ← Category.assoc, hι, hι₁]
  have hιgr : Set.range ι = g ⁻¹' Set.range j := by
    rw [hιr, hι₁r]
    rfl
  -- the resolution `Yb` is a smooth projective variety
  have hgproj : IsProjective g := hres.isProjective.comp hg₁p
  obtain ⟨hYbpm, hgpm⟩ := isProjectiveMorphism_of_isProjective s₀
    ((MMP.Mori.isProjectiveVariety_iff k s₀).1 hY₀).2 g hgproj
  set sYb : Yb ⟶ Spec (.of k) := g ≫ s₀ with hsYb
  have hsYb' : sYb = f₂ ≫ g₁ ≫ s₀ := by rw [hsYb, hg, Category.assoc]
  have hYbv : AlgebraicGeometry.IsVariety k sYb := by rw [hsYb']; exact hres.isVariety_source
  haveI := hYbv
  haveI : MMP.Mori.IsProjectiveVariety k sYb :=
    (MMP.Mori.isProjectiveVariety_iff k sYb).2 ⟨hYbv, hYbpm⟩
  have hYbsm : IsSmoothScheme sYb := by rw [hsYb']; exact hres.isSmoothScheme
  haveI : IsIntegral Yb := hYbv.toIsIntegral
  haveI : IsLocallyNoetherian Yb := LocallyOfFiniteType.isLocallyNoetherian sYb
  haveI : CompactSpace Yb := QuasiCompact.compactSpace_of_compactSpace sYb
  haveI : Smooth sYb := (MMP.Mori.isSmoothScheme_iff _).1 hYbsm
  haveI : IsNormal Yb := isNormal_of_smooth_over_field sYb
  have hcart : ∀ D : Divisor Yb, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hYbsm
  -- the boundary divisor `E` on `Yb`, with `Yb ∖ Supp E = ι(W)`
  haveI : Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback g).obj Hb) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g Hb
  have hrange : Set.range ι = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback g).obj Hb) (pullbackGlobalSections g Hb t) := by
    rw [hιgr, ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ht]
  obtain ⟨E, hE0, ⟨eE⟩, hEr⟩ := exists_divisor_of_section hcart _
    (pullbackGlobalSections g Hb t) (by rw [← hrange]; exact Set.range_nonempty _)
  -- the extension `G'` of `cB|_W` with `𝒪(G') ≅ g^* A₀`
  haveI : Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback g).obj (A 0)) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g (A 0)
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Yb.sheaf.obj Yb.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj (A 0)) :=
    ‹Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback g).obj (A 0))›
  obtain ⟨G, ⟨eG⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    ((Scheme.Modules.pullback g).obj (A 0))
  haveI : IsDominant W.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion W.ι
  have hcartY : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨T, hT⟩ := (hcartY Lc).exists_isPullback
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant W.ι Lc)
  have eT : Nonempty ((Scheme.Modules.pullback ι).obj G.divisorialSheaf ≅ T.divisorialSheaf) := by
    obtain ⟨e0⟩ := eA0
    exact ⟨(Scheme.Modules.pullback ι).mapIso eG ≪≫
      (Scheme.Modules.pullbackComp ι g).app _ ≪≫ (Scheme.Modules.pullbackCongr hιg).app _ ≪≫ e0 ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hcartY Lc) hT).symm⟩
  obtain ⟨G', ⟨eG'⟩, hG'⟩ := exists_linearlyEquivalent_coeff_eq ι (hcart G) T eT
  -- `𝒪(G' + aE) ≅ g^* A_a`
  have hGa : ∀ a : ℕ, Nonempty ((G' + a • E).divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (A a)) := by
    intro a
    induction a with
    | zero => exact ⟨eqToIso (by rw [zero_nsmul, add_zero]) ≪≫ eG' ≪≫ eG⟩
    | succ a ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨ea⟩ := eA a
      exact ⟨eqToIso (by rw [succ_nsmul, add_assoc]) ≪≫
        ((hcart _).divisorialSheafTensorIso (hcart E)).symm ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso eE ≪≫
        (Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso g (A a) Hb).symm ≪≫
        (Scheme.Modules.pullback g).mapIso ea.symm⟩
  have hgb : IsBirationalMorphism g := isBirationalMorphism_of_isOpenImmersion_comp ι j g hιg
  -- the `ℚ`-divisor `B̄ = G'/c` extending `B`
  set Bb : QDivisor Yb := ((c : ℚ)⁻¹) • Divisor.toQDivisor G'
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hBbc : ∀ P, Bb.coeff P = (c : ℚ)⁻¹ * G'.coeff P := fun P => rfl
  have hdecomp : Divisor.toQDivisor Bb.roundDown + Bb.fract = Bb := by
    ext P
    change (Bb.roundDown.coeff P : ℚ) + Bb.fract.coeff P = Bb.coeff P
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_fract, Int.floor_add_fract]
  have hBbW : ∀ Q : MMP.Mori.PrimeDivisor W,
      Bb.coeff (openPrimeDivisor ι Q) = B.coeff (openPrimeDivisor W.ι Q) := by
    intro Q
    rw [hBbc, hG' Q, coeff_of_isPullback_of_isOpenImmersion W.ι (hcartY Lc) hT Q]
    have := congrArg (DivisorWithCoeffs.coeff · (openPrimeDivisor W.ι Q)) hLc
    simp only [Divisor.coeff_toQDivisor] at this
    rw [this]
    change (c : ℚ)⁻¹ * ((c : ℚ) * B.coeff _) = B.coeff _
    rw [← mul_assoc, inv_mul_cancel₀ hcq, one_mul]
  refine H Yb sYb hYbsm ι ?_ E Bb.roundDown Bb.fract a₀ hE0 ?_ ?_ ?_ ?_
  · rw [hsYb, ← Category.assoc, hιg, hj]
  · rw [hrange, ← hEr]
  · have hsnc' : MMP.Resolution.IsSNCClosedSubset sYb
        ((exceptionalSet f₂ : Set Yb) ∪ f₂ ⁻¹' (D.sup fun E => E.idealSheaf.support)) := by
      rw [hsYb']; exact hsnc
    refine isSNC_of_isSNCClosedSubset sYb hsnc' Bb.fract fun P hP => ?_
    by_cases hPW : ∃ w, ι w ∈ P.support
    · obtain ⟨w, hw⟩ := hPW
      obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
        ι P w hw
      rw [← openPrimeDivisor_eq_primeDivisorMap] at hQ
      subst hQ
      have hfr : B.fract.coeff (openPrimeDivisor W.ι Q) ≠ 0 := by
        have h := Finsupp.mem_support_iff.mp hP
        change Int.fract (Bb.coeff (openPrimeDivisor ι Q)) ≠ 0 at h
        rw [hBbW] at h
        rwa [DivisorWithCoeffs.coeff_fract]
      have hD : openPrimeDivisor ι₁ Q ∈ D :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Q, hS.mem_toFinset.mpr hfr, rfl⟩)
      have hcl : IsClosed (f₂ ⁻¹' ((openPrimeDivisor ι₁ Q).support : Set X₁)) :=
        (openPrimeDivisor ι₁ Q).idealSheaf.support.isClosed.preimage f₂.continuous
      intro y hy
      refine Or.inr ?_
      have hy' : y ∈ f₂ ⁻¹' ((openPrimeDivisor ι₁ Q).support : Set X₁) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
        refine closure_minimal ?_ hcl hy
        have hgp : AlgebraicGeometry.PrimeDivisor.genericPoint (openPrimeDivisor ι Q) =
            ι Q.genericPoint := genericPoint_openPrimeDivisor ι Q
        have hgp₁ : AlgebraicGeometry.PrimeDivisor.genericPoint (openPrimeDivisor ι₁ Q) =
            ι₁ Q.genericPoint := genericPoint_openPrimeDivisor ι₁ Q
        rw [Set.singleton_subset_iff, hgp]
        change f₂ (ι Q.genericPoint) ∈ ((openPrimeDivisor ι₁ Q).support : Set X₁)
        rw [← Scheme.Hom.comp_apply, hι, AlgebraicGeometry.PrimeDivisor.support_eq_closure, hgp₁]
        exact subset_closure rfl
      exact (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X₁ =>
        (E.idealSheaf.support : Set X₁)) hD) hy'
    · intro y hy
      refine Or.inr ?_
      have hyι : y ∉ Set.range ι := fun ⟨w, hw⟩ => hPW ⟨w, hw ▸ hy⟩
      rw [hιr, Set.mem_preimage, hrange₁, ← hE₁r, Set.notMem_compl_iff] at hyι
      obtain ⟨F, hF, hyF⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyι
      have hD : F ∈ D := Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hF)
      exact (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X₁ =>
        (E.idealSheaf.support : Set X₁)) hD) hyF
  · intro m hm
    have hB' := toQDivisor_add_mul_nsmul G' E hcq m (Bb := Bb) rfl hdecomp
    obtain ⟨e⟩ := hGa (c * m)
    haveI := hA (c * m)
    exact QDivisor.isNef_and_isBig_of_isBirationalMorphism sYb s₀ hYbv hYbpm hY₀v
      ((MMP.Mori.isProjectiveVariety_iff k s₀).1 hY₀).2 g rfl hgpm hgb (A (c * m))
      (hamp _ (hm.trans (Nat.le_mul_of_pos_left m hc))) c hc _ (hcart _) e _ hB'
  · intro P
    have h1 : Bb.roundDown + Bb.fract.roundUp = Bb.roundUp := by
      rw [← roundUp_toQDivisor_add, hdecomp]
    rw [h1, DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundUp, hBbW P]

/-- **The good compactification of the preimage of an affine open.** This is the geometric heart
of the proof: compactify `f⁻¹(V) ⟶ V` inside a smooth projective variety `X̄` whose boundary is
the support of an effective Cartier divisor `E`, and extend `B` to `L + Δ` with `Δ` snc, such that
`L + mE + Δ` is nef and big for all large `m`. -/
private theorem exists_compactification
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f) (hBf : B.fract.IsSNC sY)
    (V : Z.Opens) (hV : IsAffineOpen V) (hW : Nonempty (f ⁻¹ᵁ V)) (C : Prop)
    (H : CompactificationData sY (f ⁻¹ᵁ V) B C) : C := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI := compactSpace_preimage f hV.isCompact
  exact exists_projectiveClosure sY sZ f hfs hf B hB V hV hW C
    (exists_compactification_of_projectiveClosure sY hsm (f ⁻¹ᵁ V) B hBf C H)

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type} [Field k] {W X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] (u : W ⟶ X) [IsOpenImmersion u]
    [Nonempty W] : topologicalKrullDim W = topologicalKrullDim X := by
  haveI : Nonempty u.opensRange := ⟨⟨u (Classical.arbitrary W), ⟨_, rfl⟩⟩⟩
  rw [← Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sX u.opensRange]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso u.isoOpensRange).isHomeomorph

/-- **Projective round-up vanishing, in the `Hgroup` spelling.** -/
private theorem isZero_hgroup_top_canonical_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] (hsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (L : Divisor X) (Δ : QDivisor X) (hΔ : Δ.IsSNC sX)
    (hnef : (Divisor.toQDivisor L + Δ).IsNef k sX) (hbig : (Divisor.toQDivisor L + Δ).IsBig k sX)
    (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i
      (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf) := by
  set F := (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf
  haveI := MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    sX hsm hK L Δ hΔ hnef hbig (i : ℤ) (by exact_mod_cast hi)
  haveI : Subsingleton (cohomologyOverField k sX F i) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k sX F
      i).toEquiv.subsingleton
  haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ i F) :=
    (AlgebraicGeometry.cohomologyOverFieldAddEquivHgroup k sX F i).symm.toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The vanishing over the preimage of one affine open of the base. -/
private theorem isZero_hgroup_preimage
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f) (hBf : B.fract.IsSNC sY)
    (i : ℕ) (hi : 0 < i) (V : Z.Opens) (hV : IsAffineOpen V) :
    IsZero (Hgroup Y.ringCatSheaf (f ⁻¹ᵁ V) i (K + B.roundUp).divisorialSheaf) := by
  classical
  by_cases hW : Nonempty (f ⁻¹ᵁ V)
  swap
  · have hbot : f ⁻¹ᵁ V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    rw [hbot]
    exact isZero_Hgroup_bot _ i
  refine exists_compactification sY sZ hsm f hfs hf B hB hBf V hV hW _ ?_
  intro X sX _ _ _ _ _ hsmX ι _ hιs E L Δ n₀ hE0 hrange hΔ hnb hcoeff
  have hdimX : topologicalKrullDim X = n := by
    rw [← hK.topologicalKrullDim_eq, ← topologicalKrullDim_eq_of_isOpenImmersion sX ι,
      topologicalKrullDim_eq_of_isOpenImmersion sY (f ⁻¹ᵁ V).ι]
  obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsmX hdimX
  have hEc : E.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmX E
  set D : Divisor X := K' + (Divisor.toQDivisor (L + n₀ • E) + Δ).roundUp with hD
  haveI := hEc.isInvertibleModule_divisorialSheaf
  have hT : ι ''ᵁ ⊤ = Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
      E.divisorialSheaf (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace)
        E.divisorialSheaf (MMP.Threefold.Mori.oneSection hE0)) := by
    apply TopologicalSpace.Opens.ext
    rw [nonvanishingOpen_divisorialSheafOneSection hEc hE0, ← hrange]
    simp
  have hG : IsZero (Hgroup X.ringCatSheaf (ι ''ᵁ ⊤) i D.divisorialSheaf) := by
    rw [hT]
    refine isZero_hgroup_nonvanishingOpen (X := X) E.divisorialSheaf _ D.divisorialSheaf i
      fun k => ?_
    obtain ⟨e⟩ := nonempty_twist_divisorialSheaf_iso
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsmX D) hEc k
    refine IsZero.of_iso ?_ ((Hfunctor X.ringCatSheaf ⊤ i).mapIso e)
    have hDk : D + k • E = K' + (Divisor.toQDivisor (L + (n₀ + k) • E) + Δ).roundUp := by
      rw [hD, roundUp_toQDivisor_add, roundUp_toQDivisor_add, add_smul]
      abel
    rw [hDk]
    obtain ⟨h1, h2⟩ := hnb (n₀ + k) (Nat.le_add_right _ _)
    exact isZero_hgroup_top_canonical_add_roundUp sX hsmX hK' _ Δ hΔ h1 h2 i hi
  have hcoeff' : ∀ P : MMP.Mori.PrimeDivisor (f ⁻¹ᵁ V),
      ((Divisor.toQDivisor (L + n₀ • E) + Δ).roundUp).coeff (openPrimeDivisor ι P) =
        B.roundUp.coeff (openPrimeDivisor (f ⁻¹ᵁ V).ι P) := by
    intro P
    have hE : (n₀ • E).coeff (openPrimeDivisor ι P) = 0 := by
      change n₀ • E.coeff (openPrimeDivisor ι P) = 0
      rw [coeff_openPrimeDivisor_eq_zero ι hrange, smul_zero]
    rw [roundUp_toQDivisor_add, ← hcoeff P, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hE, add_zero]
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI := compactSpace_preimage f hV.isCompact
  obtain ⟨e3⟩ := nonempty_restrict_divisorialSheaf_iso sX sY hsmX hsm ι (f ⁻¹ᵁ V).ι hιs hK' hK
    _ _ hcoeff'
  have e1 := (AlgebraicGeometry.CohomologyScalars.hfunctorOpenImmersionIso ι i).app
    D.divisorialSheaf
  have e2 := (AlgebraicGeometry.CohomologyScalars.hfunctorOpenImmersionIso (f ⁻¹ᵁ V).ι i).app
    (K + B.roundUp).divisorialSheaf
  have hW' : f ⁻¹ᵁ V = (f ⁻¹ᵁ V).ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top _).symm
  rw [hW']
  exact ((hG.of_iso e1.symm).of_iso ((Hfunctor _ ⊤ i).mapIso e3).symm).of_iso e2

end Main

end

end MMP.FourfoldProofs.FourfoldRelativeAmpleVanishingProof

end

section

public section

open CategoryTheory AlgebraicGeometry MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-- **Vanishing for a relatively ample round-up.** Let `f : Y ⟶ Z` be a projective morphism of
varieties over an algebraically closed field `k` of characteristic zero, with `Y` smooth, `K` a
canonical divisor of `Y`, and `B` an `f`-ample `ℚ`-divisor on `Y` whose fractional part has
simple normal crossing support. Then `R^i f_* 𝒪_Y(K + ⌈B⌉) = 0` for every `i > 0`. -/
@[mmp "lem_fourfold_relative_ample_vanishing"]
public theorem isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f) (hBf : B.fract.IsSNC sY)
    (i : ℕ) (hi : 0 < i) :
    Limits.IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      (K + B.roundUp).divisorialSheaf) := by
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard Z.Modules
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward f)
    (rfl : (i : ℤ) = (i : ℤ)) _).1 ?_
  exact Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage
    f _ i Z.isBasis_affineOpens fun V hV =>
      MMP.FourfoldProofs.FourfoldRelativeAmpleVanishingProof.isZero_hgroup_preimage sY sZ hsm f hfs hf
        hK B hB hBf i hi V hV

end MMP.Fourfold

end

end
