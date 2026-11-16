module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Divisor.Cycles
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Log minimal models of fourfold pairs: comparison of adjoints and the floor-supported identity

Two comparisons between a pair `(X/Z, B)` and a log minimal model `φ : X ⤏ M` of it, both
computed on a common resolution `p : W ⟶ X`, `q : W ⟶ M` of `φ`.

For an effective lc pair with rational boundary, `X` and `Z` normal projective, one has
`p^*(K_X + B) = q^*(K_M + B_M) + F` with `F` effective and exceptional over `M`: `F` has
positive coefficient along the strict transforms of the primes contracted by `φ` and coefficient
zero along those retained, so `p_* F ≥ 0`, and the negativity lemma (the comparison of generic
pull-backs) makes `F` effective; along a prime of `M` exceptional over `X` the boundary has
coefficient one, which forces the coefficient of `F` there to vanish.

If moreover `α (K_X + B) ≡_Z C + N` with `N ≥ 0` supported in `⌊B⌋` and `(Y, B_Y + t C_Y)` is a
log minimal model of `(X, B + t C)`, `0 < t ≤ 1`, then `α (K_Y + B_Y) ≡_Z C_Y + N_Y` with
`N_Y = q_* p^* N + (1 + α t) (q_* p^* C - C_Y)` effective and supported in `⌊B_Y⌋`, rational when
the data are: the numerically trivial divisor `α (K_X + B) - C - N` has numerically trivial full
trace on `Y`.

## Main results

* `MMP.Fourfold.IsLogMinimalModel.nonneg_sub_and_isExceptionalPrimeDivisor`: on a common
  resolution, `p^*(K_X + B) - q^*(K_M + B_M)` is effective and exceptional over `M`.
* `MMP.Fourfold.exists_isNumericallyEquivalentOver_logCanonicalDivisor_of_isRealLogMinimalModel`:
  a floor-supported numerical identity `α (K_X + B) ≡_Z C + N` survives a log minimal model.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result; some helpers (strict transforms on a common resolution) appear in
both namespaces. The canonical divisors are chosen compatibly through a canonical divisor `K_W`
of the resolution, so the identities hold as equalities of divisors. Pull-backs are the
`ℝ`-divisors pinned by `MMP.Flips.IsRCartierPullback`, numerical equivalence over `Z` is
`MMP.Flips.IsNumericallyEquivalentOver`, and the comparison of generic pull-backs is
`MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub`.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC], Section 2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace Proof_lem_fourfold_projective_lc_log_model_comparison

open MMP.Mori MMP.Fourfold

/-! ### Strict transforms on a common resolution -/

section StrictTransform

private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- At a point of coheight at most one of a normal integral scheme the local ring is a valuation
ring. -/
private theorem valuationRing_stalk_of_coheight_le_one {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} (hy : Order.coheight y ≤ 1) :
    ValuationRing (Y.presheaf.stalk y) := by
  rcases lt_or_eq_of_le hy with h | h
  · have hmax : IsMax y := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
    have hy' : y ⤳ genericPoint Y := hmax (show y ≤ genericPoint Y from hgen)
    obtain rfl : genericPoint Y = y := (hgen.antisymm hy').eq
    change ValuationRing Y.functionField
    infer_instance
  · have hdim : ringKrullDim (Y.presheaf.stalk y) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]
      rfl
    have h5 : IsNoetherianRing (Y.presheaf.stalk y) ∧ IsLocalRing (Y.presheaf.stalk y) ∧
        IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) ∧
        ringKrullDim (Y.presheaf.stalk y) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal y, hdim⟩
    obtain ⟨_, _⟩ := ((isDiscreteValuationRing_tfae (Y.presheaf.stalk y)).out 5 1).mp h5
    infer_instance

/-- **Divisorial images.** Let `f : W ⟶ Y` be a dominant morphism of normal integral schemes
inducing an isomorphism of function fields, and `P` a prime divisor of `W` whose image point has
coheight at most one. Then `f(η_P)` is the generic point of a prime divisor `Q` of `Y`, and `f`
induces an isomorphism `𝒪_{Y,Q} ≅ 𝒪_{W,P}`. -/
private theorem exists_primeDivisor_of_coheight_le_one {W Y : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : W ⟶ Y) [IsDominant f] (hf : Function.Bijective (functionFieldMap f))
    (P : MMP.Mori.PrimeDivisor W) (hP : Order.coheight (f P.genericPoint) ≤ 1) :
    ∃ Q : MMP.Mori.PrimeDivisor Y, f P.genericPoint = Q.genericPoint ∧
      IsIso (f.stalkMap P.genericPoint) := by
  have := valuationRing_stalk_of_coheight_le_one hP
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf P.genericPoint
  have hco : Order.coheight (f P.genericPoint) = 1 := by
    have h1 : ringKrullDim (W.presheaf.stalk P.genericPoint) =
        ringKrullDim (Y.presheaf.stalk (f P.genericPoint)) :=
      (ringKrullDim_eq_of_ringEquiv
        (asIso (f.stalkMap P.genericPoint)).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      P.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco, ?_, hiso⟩
  exact (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm

/-- Two prime divisors of `W` over the generic point of the same prime divisor of `Y` agree, for
a separated dominant morphism `f : W ⟶ Y` of normal integral schemes inducing an isomorphism of
function fields. -/
private theorem eq_of_apply_genericPoint_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : W ⟶ Y) [IsDominant f] [IsSeparated f] (hf : Function.Bijective (functionFieldMap f))
    {P P' : MMP.Mori.PrimeDivisor W} {Q : MMP.Mori.PrimeDivisor Y}
    (hP : f P.genericPoint = Q.genericPoint) (hP' : f P'.genericPoint = Q.genericPoint) :
    P = P' := by
  have hQ : Order.coheight Q.genericPoint ≤ 1 := Q.coheight_genericPoint.le
  have : ValuationRing (Y.presheaf.stalk (f P.genericPoint)) := by
    rw [hP]; exact valuationRing_stalk_of_coheight_le_one hQ
  have : ValuationRing (Y.presheaf.stalk (f P'.genericPoint)) := by
    rw [hP']; exact valuationRing_stalk_of_coheight_le_one hQ
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf P.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf P'.genericPoint
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.eq_of_isIso_stalkMap f hf (hP'.trans hP.symm))

/-- **The strict transform on a resolution.** Let `p : W ⟶ X` be a proper birational morphism
of normal varieties with inverse `h`, and `P` a prime divisor of `X`. Then `h` is defined at the
codimension-one point `η_P` by some `h'`, and `h'(η_P)` is the generic point of a prime divisor
`E` of `W` with `p(η_E) = η_P`, along which `p` induces an isomorphism of local rings. -/
private theorem exists_strictTransform {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hX : IsNormalVariety k sX) (p : W ⟶ X)
    (h : X.RationalMap W) [IsProper p] (hWnp : IsNormalVariety k (p ≫ sX))
    (hpb : IsBirationalMorphism p) (hinv : RationalMap.IsInverse p.toRationalMap h)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ (E : MMP.Mori.PrimeDivisor W) (h' : X.PartialMap W) (hP : P.genericPoint ∈ h'.domain),
      h'.toRationalMap = h ∧ E.genericPoint = h'.hom ⟨P.genericPoint, hP⟩ ∧
      p E.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap E.genericPoint) := by
  have := hX.1
  have := hWnp.1
  have : IsDominant p := hpb.isDominant
  have := isSeparated_toTerminal sX
  have : IsSeparated p := IsSeparated.of_comp p sX
  obtain ⟨E, heq, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hWnp hpb P
  obtain ⟨e, he1, he2⟩ := id hinv
  have hhp : h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
    rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]
  obtain ⟨h', hh'P, hh'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 X) p h hhp
      P.coheight_genericPoint.le)
  have hpw : p (h'.hom ⟨P.genericPoint, hh'P⟩) = P.genericPoint :=
    apply_hom_eq_of_isInverse p e he1 h' (hh'.trans he2.symm) hh'P
  haveI : ValuationRing (X.presheaf.stalk P.genericPoint) := by
    haveI := P.isDiscreteValuationRing_localRing
    exact inferInstanceAs (ValuationRing P.localRing)
  haveI : ValuationRing (X.presheaf.stalk (p E.genericPoint)) := by rw [heq]; infer_instance
  haveI : ValuationRing (X.presheaf.stalk (p (h'.hom ⟨P.genericPoint, hh'P⟩))) := by
    rw [hpw]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing p hpb.functionFieldMap_bijective
    (h'.hom ⟨P.genericPoint, hh'P⟩)
  exact ⟨E, h', hh'P, hh', MMP.Positivity.eq_of_isIso_stalkMap p hpb.functionFieldMap_bijective
    (hpw.trans heq.symm), heq, hiso⟩

/-- Along a prime divisor `E` of `Y` with `f(η_E) = η_P` at which `f` induces an isomorphism of
local rings, the valuation `ord_E ∘ f^*` is `ord_P`. -/
private theorem divisorialValuation_comap_functionFieldMap_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (f : Y ⟶ X) [IsDominant f] (E : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] :
    E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq t]

end StrictTransform

/-! ### Orders of forms along isomorphisms of local rings -/

section FormOrders

open TopologicalSpace

/-- A specialization between equal points induces an isomorphism of stalks. -/
private theorem isIso_stalkSpecializes {X : Scheme.{u}} {x y : X} (hsp : x ⤳ y)
    (h : x = y) : IsIso (X.presheaf.stalkSpecializes hsp) := by
  subst h
  simp only [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

/-- A bijective algebra map is a localization at the trivial submonoid. -/
private theorem isLocalization_bot_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    IsLocalization (⊥ : Submonoid R) S :=
  IsLocalization.of_le_isUnit_of_bijective (by simp [Algebra.algebraMapSubmonoid]) h

section

variable {k : Type*} [CommRing k] {K L : Type*} [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- Along a bijective map of fields over `k`, `Ω^d_{K/k} ⟶ Ω^d_{L/k}` is injective: the inverse
map is a left inverse. -/
private theorem topFormsMap_injective_of_bijective (h : Function.Bijective (algebraMap K L))
    (d : ℕ) :
    Function.Injective (topFormsMap k K L d) := by
  let e := RingEquiv.ofBijective (algebraMap K L) h
  let : Algebra L K := e.symm.toRingHom.toAlgebra
  have : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k K c = e.symm (algebraMap k L c)
    rw [IsScalarTower.algebraMap_apply k K L]
    exact (e.symm_apply_apply _).symm
  have : IsScalarTower K L K := IsScalarTower.of_algebraMap_eq fun c =>
    (e.symm_apply_apply c).symm
  intro x y hxy
  have h1 := congrArg (topFormsMap k L K d) hxy
  rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
    MMP.Threefold.Mori.Helpers.topFormsMap_comp] at h1
  have hid := topFormsMap_eq_self (k := k) (RingHom.id K) (fun _ => rfl) (d := d)
  rwa [hid, hid] at h1

end

section

variable {k : Type*} [CommRing k] {d : ℕ}
variable {A B K L : Type*} [CommRing A] [CommRing B] [Field K] [Field L] [Algebra k A]
  [Algebra k B] [Algebra k K] [Algebra k L] [Algebra A K] [Algebra B L] [Algebra A B]
  [Algebra K L] [Algebra A L] [IsScalarTower k A K] [IsScalarTower k B L] [IsScalarTower k A B]
  [IsScalarTower k K L] [IsScalarTower k A L] [IsScalarTower A B L] [IsScalarTower A K L]

/-- A generator of `Ω^d_{A/k}` with nonzero image in `Ω^d_{K/k}` is carried, along bijective
maps `A ⟶ B` and `K ⟶ L`, to a generator of `Ω^d_{B/k}` with nonzero image in `Ω^d_{L/k}`. -/
private theorem exists_generator_of_bijective (hAB : Function.Bijective (algebraMap A B))
    (hKL : Function.Bijective (algebraMap K L))
    (h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0) :
    ∃ σ : ⋀[B]^d Ω[B⁄k], Submodule.span B {σ} = ⊤ ∧ topFormsMap k B L d σ ≠ 0 := by
  obtain ⟨σ, hσ, h0⟩ := h
  have := isLocalization_bot_of_bijective hAB
  refine ⟨topFormsMap k A B d σ, span_singleton_topFormsMap ⊥ hσ, ?_⟩
  rw [MMP.Threefold.Mori.Helpers.topFormsMap_comp,
    ← MMP.Threefold.Mori.Helpers.topFormsMap_comp (B := K) (C := L)]
  exact fun h1 => h0 (topFormsMap_injective_of_bijective hKL d (h1.trans (map_zero _).symm))

end

section

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}
variable {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
  [IsScalarTower k K K']
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K] [Algebra A' K'] [IsScalarTower k A' K']
  [IsFractionRing A' K'] [Algebra A A'] [IsScalarTower k A A'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower k A K']

/-- The order of a form is invariant under bijective maps `A ⟶ A'`, `K ⟶ K'` compatible with the
valuations, with no hypothesis on `k`: if `Ω^d_{A/k}` has a generator the orders are computed
from it and its image; otherwise neither side has one and both orders are `0`. -/
private theorem ordAt_pullbackForms_eq_of_bijective (hbij : Function.Bijective (algebraMap A A'))
    (hbijK : Function.Bijective (algebraMap K K'))
    {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hvv : ∀ x, v' (algebraMap K K' x) = v x) (τ : PluriForms k K d m) :
    ordAt A' v' (pullbackForms (K' := K') m τ) = ordAt A v τ := by
  classical
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    have := isLocalization_bot_of_bijective hbijK
    have hK := span_singleton_topFormsMap (K := K) (nonZeroDivisors A) hσ
    have hω : IsPullbackGenerator K' (topFormsMap k A K d σ) :=
      ⟨hK, span_singleton_topFormsMap ⊥ hK, fun h1 =>
        h0 (topFormsMap_injective_of_bijective hbijK d (h1.trans (map_zero _).symm))⟩
    exact MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq hbij hmul hunit hmul' hunit' hvv
      hσ hω τ
  · have h' : ¬ ∃ σ : ⋀[A']^d Ω[A'⁄k], Submodule.span A' {σ} = ⊤ ∧
        topFormsMap k A' K' d σ ≠ 0 := by
      intro h'
      apply h
      let eA := RingEquiv.ofBijective (algebraMap A A') hbij
      let eK := RingEquiv.ofBijective (algebraMap K K') hbijK
      let : Algebra A' A := eA.symm.toRingHom.toAlgebra
      let : Algebra K' K := eK.symm.toRingHom.toAlgebra
      let : Algebra A' K := ((algebraMap A K).comp (algebraMap A' A)).toAlgebra
      have hA : ∀ c : k, algebraMap k A c = eA.symm (algebraMap k A' c) := fun c => by
        rw [IsScalarTower.algebraMap_apply k A A']
        exact (eA.symm_apply_apply _).symm
      have hKc : ∀ c : k, algebraMap k K c = eK.symm (algebraMap k K' c) := fun c => by
        rw [IsScalarTower.algebraMap_apply k K K']
        exact (eK.symm_apply_apply _).symm
      have : IsScalarTower k A' A := IsScalarTower.of_algebraMap_eq hA
      have : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq hKc
      have : IsScalarTower A' A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : IsScalarTower k A' K := IsScalarTower.of_algebraMap_eq fun c => by
        change _ = algebraMap A K (eA.symm (algebraMap k A' c))
        rw [← hA, ← IsScalarTower.algebraMap_apply]
      have : IsScalarTower A' K' K := IsScalarTower.of_algebraMap_eq fun a => by
        change algebraMap A K (eA.symm a) = eK.symm (algebraMap A' K' a)
        apply eK.injective
        rw [RingEquiv.apply_symm_apply]
        change algebraMap K K' (algebraMap A K (eA.symm a)) = _
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A A' K']
        congr 1
        exact eA.apply_symm_apply a
      exact exists_generator_of_bijective (A := A') (B := A) (K := K') (L := K)
        eA.symm.bijective eK.symm.bijective h'
    simp only [ordAt, h, h', dite_false]

end

/-- The order of a rational pluricanonical form is unchanged by pulling back along a prime
divisor `F` of `Y` dominating a prime divisor `P` of `X`: `ord_F(f^*τ) = ord_P(τ)` when
`f(η_F) = η_P` and `f^♯ : 𝒪_{X,P} ⟶ 𝒪_{Y,F}` is an isomorphism, `f^* : k(X) → k(Y)` being an
isomorphism. The isomorphisms carry a generator of `Ω^d_{𝒪_{X,P}/k}` to one of `Ω^d_{𝒪_{Y,F}/k}`
and back, so both sides are computed from the same generator, or both vanish. -/
private theorem ordForm_pullbackRationalPluriForms_of_isIso {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal X] [IsNormal Y] {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X)
    [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ} (F : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor X) (heq : f F.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap F.genericPoint)] {m : ℤ} (τ : RationalPluriForms sX d m) :
    F.ordForm (pullbackRationalPluriForms sX f τ) = P.ordForm τ := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := stalkAlgebra sX P.genericPoint
  have := isScalarTower_stalk_functionField sX P.genericPoint
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  have hsp : f F.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ Y.presheaf.stalk F.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap F.genericPoint
  have := isIso_stalkSpecializes hsp heq
  have hφ : IsIso φ := by infer_instance
  let : Algebra P.localRing F.localRing := φ.hom.toAlgebra
  let : Algebra P.localRing Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap P.localRing X.functionField)).toAlgebra
  have : IsScalarTower P.localRing X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hφK : ∀ r : P.localRing, algebraMap P.localRing Y.functionField r =
      algebraMap F.localRing Y.functionField (φ.hom r) := fun r => by
    change functionFieldMap f _ = algebraMap _ Y.functionField ((f.stalkMap F.genericPoint).hom
        ((X.presheaf.stalkSpecializes hsp).hom r))
    rw [← functionFieldMap_algebraMap_stalk, algebraMap_stalkSpecializes]
  have : IsScalarTower P.localRing F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq hφK
  have : IsScalarTower k P.localRing F.localRing := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
          Y.presheaf.germ ⊤ F.genericPoint (Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ P.genericPoint (Opens.mem_top _)) ≫ φ := by
      simp only [φ, Scheme.Hom.comp_appTop, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  have : IsScalarTower k P.localRing Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
      IsScalarTower.algebraMap_apply k P.localRing X.functionField]
    rfl
  have hbijA : Function.Bijective (algebraMap P.localRing F.localRing) :=
    (ConcreteCategory.isIso_iff_bijective φ).mp hφ
  exact ordAt_pullbackForms_eq_of_bijective (k := k) hbijA hbij
    P.ord_mul_of_ne_zero (fun _ ha => P.ord_algebraMap_of_isUnit ha)
    F.ord_mul_of_ne_zero (fun _ ha => F.ord_algebraMap_of_isUnit ha)
    (fun x => MMP.Positivity.ord_functionFieldMap_of_isIso f F P heq x) τ

end FormOrders

/-! ### Smoothness in codimension one and compatible forms -/

section CompatibleForms

open TopologicalSpace

/-- **Smoothness transfers along isomorphisms of local rings.** If `f : W ⟶ X` induces an
isomorphism `𝒪_{X,P} ≅ 𝒪_{W,E}` with `f(η_E) = η_P` and `W` is smooth over `k`, then `η_P` is a
smooth point of `X`. -/
private theorem genericPoint_mem_smoothLocus_of_isIso {k : Type u} [Field k] {X W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral W]
    [IsLocallyNoetherian W] [LocallyOfFiniteType sX] (f : W ⟶ X)
    [LocallyOfFiniteType (f ≫ sX)] (hW : IsSmoothScheme (f ≫ sX)) (E : MMP.Mori.PrimeDivisor W)
    (P : MMP.Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] : P.genericPoint ∈ smoothLocus sX := by
  rw [MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus_iff]
  have hE : E.genericPoint ∈ smoothLocus (f ≫ sX) := by
    rw [show smoothLocus (f ≫ sX) = ⊤ from hW]; trivial
  rw [MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus_iff] at hE
  let := stalkAlgebra sX P.genericPoint
  let := stalkAlgebra (f ≫ sX) E.genericPoint
  have hsp : f E.genericPoint ⤳ P.genericPoint := heq ▸ specializes_rfl
  let φ : X.presheaf.stalk P.genericPoint ⟶ W.presheaf.stalk E.genericPoint :=
    X.presheaf.stalkSpecializes hsp ≫ f.stalkMap E.genericPoint
  have := isIso_stalkSpecializes hsp heq
  have hφ : IsIso φ := by infer_instance
  have hcomm : ∀ c : k, φ.hom (algebraMap k P.localRing c) = algebraMap k E.localRing c := by
    intro c
    have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
          W.presheaf.germ ⊤ E.genericPoint (Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
          X.presheaf.germ ⊤ P.genericPoint (Opens.mem_top _)) ≫ φ := by
      simp only [φ, Scheme.Hom.comp_appTop, Category.assoc,
        TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
      rfl
    exact (congrArg (fun g => g.hom c) h).symm
  let e : P.localRing ≃ₐ[k] E.localRing :=
    { (asIso φ).commRingCatIsoToRingEquiv with commutes' := hcomm }
  exact Algebra.FormallySmooth.of_equiv e.symm

/-- On a normal variety with a canonical divisor whose prime divisors have smooth generic points,
`ord_Γ(c • τ) = v_Γ(c) + ord_Γ(τ)` for `c ≠ 0` and `τ ≠ 0`. -/
private theorem ordForm_smul_of_forall_mem_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (hX : IsNormalVariety k sX)
    (hsm : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ smoothLocus sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (Γ : MMP.Mori.PrimeDivisor X)
    {c : X.functionField} (hc : c ≠ 0) {τ : RationalPluriForms sX n 1} (hτ : τ ≠ 0) :
    Γ.ordForm (c • τ) = X.ord c Γ.genericPoint + Γ.ordForm τ := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have h1 := MMP.Positivity.finrank_topForms_functionField_eq_one hX hsm hK.topologicalKrullDim_eq
  have : Nontrivial (⋀[X.functionField]^n Ω[X.functionField⁄k]) :=
    Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨V, ψ, hΓV, hψ⟩ := MMP.Positivity.Divisor.exists_isLocalEquation K Γ
  have hσ := MMP.Positivity.span_formsGerm_invSection_eq_top hK hψ Γ (hsm Γ) hΓV
  exact ordAt_smul (k := k) Γ.ord_mul_of_ne_zero (fun _ ha => Γ.ord_algebraMap_of_isUnit ha)
    ⟨_, hσ, topFormsMap_ne_zero_of_span_eq_top hσ⟩ hc hτ

/-- **Compatible forms over an arbitrary field.** Let `f : W ⟶ Y` be a proper birational morphism
from a smooth variety to a normal variety with a canonical divisor `K₀`, `K_W` a canonical divisor
of `W` and `K_Y = f_* K_W`. Then `K_Y` is a canonical divisor, and a nonzero rational top form `ω`
on `Y` has `div_Y(ω) = K_Y` and `div_W(f^*ω) = K_W`. -/
private theorem exists_form_of_transformDivisor_eq {k : Type u} [Field k] {Y W : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [LocallyOfFiniteType sY] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hY : IsNormalVariety k sY) (f : W ⟶ Y) [IsProper f] [IsDominant f]
    (hWn : IsNormalVariety k (f ≫ sY)) (hf : IsBirationalMorphism f)
    (hWs : IsSmoothScheme (f ≫ sY)) {n : ℕ} {K₀ : Divisor Y}
    (hK₀ : K₀.IsCanonicalDivisor sY n) {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (f ≫ sY) n)
    {KY : Divisor Y} (hpush : RationalMap.transformDivisor (X := W) f.toRationalMap KW = KY) :
    ∃ ω : RationalPluriForms sY n 1, ω ≠ 0 ∧
      (∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.ordForm ω = KY.coeff Γ) ∧
      (∀ P : MMP.Mori.PrimeDivisor W,
        P.ordForm (pullbackRationalPluriForms sY f ω) = KW.coeff P) ∧
      KY.IsCanonicalDivisor sY n := by
  classical
  have : LocallyOfFiniteType (f ≫ sY) := hWn.1.toLocallyOfFiniteType
  have hbij := hf.functionFieldMap_bijective
  have hsmW : ∀ P : MMP.Mori.PrimeDivisor W, P.genericPoint ∈ smoothLocus (f ≫ sY) := fun P => by
    rw [show smoothLocus (f ≫ sY) = ⊤ from hWs]; trivial
  have hsmY : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.genericPoint ∈ smoothLocus sY := fun Γ => by
    obtain ⟨E, heq, hiso, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hWn hf Γ
    exact genericPoint_mem_smoothLocus_of_isIso f hWs E Γ heq
  obtain ⟨ω₀, hω₀0, hω₀⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hY hsmY hK₀
  obtain ⟨ω₁, hω₁0, hω₁⟩ :=
    MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq_of_forall_mem_smoothLocus hWn hsmW hKW
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (f ≫ sY)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sY f
  have h1 := MMP.Positivity.finrank_topForms_functionField_eq_one hY hsmY
    hK₀.topologicalKrullDim_eq
  let b := Module.basisUnique Unit h1
  have hspan : Submodule.span Y.functionField {b ()} = ⊤ := by
    simpa only [Set.range_unique] using b.span_eq
  have : IsLocalization (⊥ : Submonoid Y.functionField) W.functionField :=
    isLocalization_bot_of_bijective hbij
  have hω : IsPullbackGenerator W.functionField (b ()) :=
    ⟨hspan, span_singleton_topFormsMap ⊥ hspan, fun h0 =>
      b.ne_zero () (topFormsMap_injective_of_bijective hbij n (h0.trans (map_zero _).symm))⟩
  have hpb : ∀ τ : RationalPluriForms sY n 1,
      pullbackRationalPluriForms sY f τ = pullbackFormsAlong hω 1 τ := fun τ => by
    change pullbackForms (K := Y.functionField) (K' := W.functionField) 1 τ = _
    exact pullbackForms_eq hω 1 τ
  set BY := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1
  set BW := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) 1
  have hrepr : ∀ τ : RationalPluriForms sY n 1,
      pullbackRationalPluriForms sY f τ = algebraMap _ _ (BY.repr τ ()) • BW () := fun τ =>
    hpb τ
  set a := BY.repr ω₀ ()
  have ha0 : a ≠ 0 := by
    intro h0
    apply hω₀0
    have h2 : BY.repr ω₀ = 0 := Finsupp.ext fun i => by cases i; exact h0
    exact BY.repr.injective (h2.trans BY.repr.map_zero.symm)
  set c : W.functionField := BW.repr ω₁ () / algebraMap Y.functionField W.functionField a with hc
  have hc0 : c ≠ 0 := by
    refine div_ne_zero (fun h0 => hω₁0 ?_) ((map_ne_zero _).mpr ha0)
    have h2 : BW.repr ω₁ = 0 := Finsupp.ext fun i => by cases i; exact h0
    exact BW.repr.injective (h2.trans BW.repr.map_zero.symm)
  obtain ⟨c', hc'⟩ := hbij.2 c
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [← hc', map_zero])
  have hc'' : algebraMap Y.functionField W.functionField c' = c := hc'
  set ω : RationalPluriForms sY n 1 := c' • ω₀ with hωdef
  have hrepω : BY.repr ω () = c' * a := congrArg (· ()) (BY.repr.map_smul c' ω₀)
  have hpull : pullbackRationalPluriForms sY f ω = ω₁ := by
    rw [hrepr, hrepω, map_mul, hc'', hc, div_mul_cancel₀ _ ((map_ne_zero _).mpr ha0)]
    have := BW.sum_repr ω₁
    rwa [Fintype.sum_unique] at this
  have hω0 : ω ≠ 0 := smul_ne_zero hc'0 hω₀0
  have hordY : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.ordForm ω = KY.coeff Γ := by
    intro Γ
    obtain ⟨E, heq, hiso, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hY hWn hf Γ
    rw [← ordForm_pullbackRationalPluriForms_of_isIso f hbij E Γ heq ω, hpull, hω₁, ← hpush]
    exact (htr KW).symm
  refine ⟨ω, hω0, hordY, fun P => by rw [hpull, hω₁], ?_⟩
  refine hK₀.of_linearlyEquivalent ?_
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hc'0
  refine ⟨φ, ?_⟩
  ext Γ
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, ← hordY Γ, ← hω₀ Γ, hωdef,
    ordForm_smul_of_forall_mem_smoothLocus hY hsmY hK₀ Γ hc'0 hω₀0]
  ring

end CompatibleForms

/-! ### Relative nefness of a `ℚ`-divisor as an `ℝ`-divisor -/

section Nef

open MMP.Flips

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem ProperCurve.not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem ProperCurve.isCurve_comp (C : ProperCurve sX) {C' : Scheme} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine ProperCurve.not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem ProperCurve.isCurve_ι (C : ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := ProperCurve.isCurve_comp C hν hdim
  have hc2 := ProperCurve.isCurve_ι C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (ProperCurve.not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn_of_isCartierIntersectionNumber [QuasiCompact sX]
    [IsLocallyNoetherian X] [IsNormal X] {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- **`ℚ`-nefness is `ℝ`-nefness.** If `K + B` (with `K` a divisor and `B` a `ℚ`-divisor) is
nef over `Y` as a `ℚ`-Cartier `ℚ`-divisor, then `K + B` is nef over `Y` as an `ℝ`-divisor. -/
private theorem isRelativelyNef_logCanonicalDivisor [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {Y : Scheme.{u}} {f : X ⟶ Y} {K : Divisor X} {B : QDivisor X}
    (h : QDivisor.IsRelativelyNef sX f (Divisor.toQDivisor K + B)) :
    MMP.Flips.IsRelativelyNef k sX f (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) := by
  obtain ⟨hD, hh⟩ := h
  set D := Divisor.toQDivisor K + B with hDdef
  set N := D.cartierIndex hD
  have hNpos : (0 : ℚ) < N := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set L : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hLc : L.IsCartier := (D.cartierIndexSMul hD).2
  have hLD : ∀ P, (L.coeff P : ℚ) = N * D.coeff P := fun P => by
    simpa [zsmul_eq_mul] using
      congrArg (fun G : QDivisor X => G.coeff P) (QDivisor.toQDivisor_cartierIndexSMul D hD)
  refine ⟨1, fun _ => ((1 / N : ℚ) : ℝ), fun _ => L, fun _ => hLc, ?_, fun C hC x hx => ?_⟩
  · ext P
    simp only [MMP.Flips.logCanonicalDivisor, Fin.sum_univ_one]
    change (Divisor.toRDivisor K + QDivisor.toRDivisor B).coeff P =
      (((1 / N : ℚ) : ℝ) • Divisor.toRDivisor L).coeff P
    rw [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, smul_eq_mul]
    have h2 : ((L.coeff P : ℚ) : ℝ) = ((N * D.coeff P : ℚ) : ℝ) := by rw [hLD P]
    have h3 : D.coeff P = (K.coeff P : ℚ) + B.coeff P := by
      rw [hDdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    push_cast at h2
    rw [h3] at h2
    push_cast at h2
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    rw [h2]
    push_cast
    field_simp
  · obtain ⟨hL', d, -, hd, rfl⟩ := hx
    have key := hh C hC
    rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
      Finsupp.sum_single_index (by simp)] at key
    simp only [smul_eq_mul, mul_one] at key
    have hd0 := eq_degreeOn_of_isCartierIntersectionNumber (hd 0)
    simp only [Fin.sum_univ_one]
    rw [hd0]
    exact_mod_cast key

end Nef

/-! ### Log discrepancies computed by forms -/

section LogDiscrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The log discrepancy of a prime divisor `E` on a resolution `f : W ⟶ X` is
`1 + ord_E(f^*ω) - coeff_E(f^*(K + B))`, for a rational top form `ω` with `div_X(ω) = K`
canonical. -/
private theorem isLogDiscrepancy_of_ordForm {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hXn : IsNormalVariety k sX) (f : W ⟶ X) [IsProper f]
    [IsDominant f] (hWn : IsNormalVariety k (f ≫ sX)) (hfb : IsBirationalMorphism f) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (ω : RationalPluriForms sX n 1) (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) {G : RDivisor W}
    (hG : MMP.Flips.IsRCartierPullback f (MMP.Flips.logCanonicalDivisor K B) G)
    (E : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sX n B ⟨W, f, hWn, hfb, E⟩
      (1 + (E.ordForm (pullbackRationalPluriForms sX f ω) : ℝ) - G.coeff E) := by
  obtain ⟨m, r, L, L', hLc, hD, hpbL, rfl⟩ := hG
  refine ⟨hXn, inferInstanceAs (IsProper f), ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, m, r, L, L',
    hLc, fun Γ => ?_, hpbL, ?_⟩
  · have := congrArg (fun D : RDivisor X => D.coeff Γ) hD
    simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, hωK]
  · rw [MMP.Flips.coeff_sum_smul_toRDivisor]
    rfl

/-- The log discrepancy of a prime divisor `Γ` of `X` itself is `1 - coeff_Γ B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor_of_ordForm [CompactSpace X]
    (hXn : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : RDivisor X} (ω : RationalPluriForms sX n 1) (hω0 : ω ≠ 0)
    (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hD : MMP.Flips.logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (Γ : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor k hXn Γ)
      (1 - B.coeff Γ) := by
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hLc j)
  have hcoeff : ∀ j, (L' j).coeff Γ = (L j).coeff Γ := fun j =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) Γ Γ rfl (hLc j) (hL' j)
  have hbij : Function.Bijective (functionFieldMap (𝟙 X)) := by
    refine ⟨fun a b hab => ?_, fun a => ⟨a, MMP.Mori.functionFieldMap_id_apply a⟩⟩
    rwa [MMP.Mori.functionFieldMap_id_apply, MMP.Mori.functionFieldMap_id_apply] at hab
  have hord : (DivisorOver.ofPrimeDivisor k hXn Γ).ordPullback ω = K.coeff Γ := by
    change Γ.ordForm (pullbackRationalPluriForms sX (𝟙 X) ω) = _
    rw [ordForm_pullbackRationalPluriForms_of_isIso (𝟙 X) hbij Γ Γ rfl ω, hωK]
  have hΓ := congrArg (fun D : RDivisor X => D.coeff Γ) hD
  simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at hΓ
  refine ⟨hXn, inferInstanceAs (IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hωK Γ).symm⟩, m, r, L,
    L', hLc, fun Γ' => ?_, fun j => ⟨_, hL' j⟩, ?_⟩
  · have := congrArg (fun D : RDivisor X => D.coeff Γ') hD
    simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, hωK]
  · rw [hord]
    change 1 - B.coeff Γ = 1 + (K.coeff Γ : ℝ) - ∑ i, r i * ((L' i).coeff Γ : ℝ)
    simp only [hcoeff]
    rw [← hΓ]
    ring

/-- Along a prime divisor `P` of a resolution `f : W ⟶ X` over a prime divisor `Γ` of `X`, the
pull-back of `K_X + B` has coefficient `coeff_P K_W + coeff_Γ B`, where `K_X = f_* K_W`. -/
private theorem coeff_isRCartierPullback_logCanonicalDivisor {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hXn : IsNormalVariety k sX) (f : W ⟶ X) [IsProper f]
    (hWn : IsNormalVariety k (f ≫ sX)) (hfb : IsBirationalMorphism f) {KW : Divisor W}
    {K : Divisor X} (hK : RationalMap.transformDivisor (X := W) f.toRationalMap KW = K)
    {B : QDivisor X} {G : RDivisor W}
    (hG : MMP.Flips.IsRCartierPullback f
      (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) G)
    {P : MMP.Mori.PrimeDivisor W} {Γ : MMP.Mori.PrimeDivisor X}
    (hPΓ : f P.genericPoint = Γ.genericPoint) :
    G.coeff P = KW.coeff P + B.coeff Γ := by
  have : IsDominant f := hfb.isDominant
  have := hXn.1
  have : IsSeparated f := IsSeparated.of_comp f sX
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWn hfb Γ
  obtain rfl := eq_of_apply_genericPoint_eq f hfb.functionFieldMap_bijective heq hPΓ
  rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback E Γ heq hG, MMP.Flips.logCanonicalDivisor,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, ← hK,
    DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply, htr KW]
  rfl

end LogDiscrepancy

/-! ### Function fields on a common resolution -/

section FunctionField

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of `φ : X ⤏ Y` (with `h` inverse to `p`
and `q = φ ∘ h`), `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Y W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y)
    (h : X.RationalMap W) [IsDominant p] (hinv : RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨e, he1, he2⟩ := hinv
  rw [← hcomp, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm p e he1]

/-- A ring map `θ : k(Y) → k(X)` inducing `m : Spec k(X) ⟶ Y` at the generic point satisfies
`p^* ∘ θ = q^*` for every pair `p : A ⟶ X`, `q : A ⟶ Y` along which `m` is `q`. -/
private theorem functionFieldMap_comp_eq_of_specMap {X Y A : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral A] (m : Spec X.functionField ⟶ Y)
    (θ : Y.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m)
    (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p] [IsDominant q]
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    (functionFieldMap p).comp θ = functionFieldMap q := by
  have key : Spec.map (CommRingCat.ofHom ((functionFieldMap p).comp θ)) ≫
      Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hθ, hA,
      functionFieldMap_fromSpecStalk q]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).mp key))

/-- A ring map inducing `m : Spec k(X) ⟶ Y`, read off a pair `p : A ⟶ X`, `q : A ⟶ Y` of
morphisms inducing isomorphisms of function fields along which `m` is `q`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] (m : Spec X.functionField ⟶ Y) (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hq : Function.Bijective (functionFieldMap q))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, Function.Bijective θ ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q :=
    RingHom.ext fun s => ep.apply_symm_apply _
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  refine ⟨θ, ep.symm.bijective.comp hq, ?_⟩
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
  exact functionFieldMap_fromSpecStalk q

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if they
agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U)
    {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have heqv : P₁.equiv P₂ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp heqv
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

/-- Two morphisms from an integral scheme to a separated scheme agree if they agree on
`Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalk_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {f g : W ⟶ Y}
    (H : W.fromSpecStalk (genericPoint W) ≫ f = W.fromSpecStalk (genericPoint W) ≫ g) :
    f = g := by
  have h := hom_eq_of_fromSpecStalkOfMem_eq (⊤ : W.Opens) (show genericPoint W ∈ (⊤ : W.Opens)
    from trivial) (f := (⊤ : W.Opens).ι ≫ f) (g := (⊤ : W.Opens).ι ≫ g) (by
      rw [← Category.assoc, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, H])
  rw [← Scheme.topIso_hom] at h
  exact (cancel_epi _).mp h

/-- If `θ` induces `φ` at the generic points and `ψ` is inverse to `φ`, then
`Spec k(X) ⟶ Spec k(M) ⟶ X` along `θ` and `ψ` is the canonical map. -/
private theorem specMap_comp_fromFunctionField_of_isInverse {X M : Scheme.{u}} [IsIntegral X]
    [IsIntegral M] {φ : X.RationalMap M} {ψ : M.RationalMap X}
    (hinv : MMP.Mori.RationalMap.IsInverse φ ψ) (θ : M.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ M.fromSpecStalk (genericPoint M) =
      φ.fromFunctionField) :
    Spec.map (CommRingCat.ofHom θ) ≫ ψ.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hy : genericPoint M ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have hφ : φ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ : ψ.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint M) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c1 : Spec.map (CommRingCat.ofHom θ) ≫ e.target.fromSpecStalkOfMem (genericPoint M) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ, hφ,
      Category.assoc]
  rw [hψ, ← Category.assoc, c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- **Realizing a contracted divisor on the resolution.** On a common resolution
`p : W ⟶ X`, `q : W ⟶ M` of `φ`, with `ψ` inverse to `φ`, the strict transform `P` on `W` of a
prime divisor `Γ` of `X`, regarded as a divisor over `M`, realizes `Γ` through `ψ`. -/
private theorem isRealizedOver_of_apply_eq {k : Type u} [Field k] {X M W : Scheme.{u}}
    {sM : M ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral M]
    [IsLocallyNoetherian M] [IsNormal M] [CompactSpace M] [LocallyOfFiniteType sM]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsSeparated sM]
    [IsSeparated (X ↘ ⊤_ Scheme)]
    (p : W ⟶ X) (q : W ⟶ M) (h : X.RationalMap W) [IsDominant p] [IsDominant q] [IsProper q]
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : RationalMap.IsInverse p.toRationalMap h) {φ : X.RationalMap M}
    (hcomp : h.compHom q = φ) {ψ : M.RationalMap X} (hψ : RationalMap.IsInverse φ ψ)
    (hWnq : IsNormalVariety k (q ≫ sM)) (Γ : MMP.Mori.PrimeDivisor X)
    (P : MMP.Mori.PrimeDivisor W) (heq : p P.genericPoint = Γ.genericPoint)
    [IsIso (p.stalkMap P.genericPoint)] :
    MMP.Flips.IsRealizedOver sM ψ Γ
      (⟨⟨W, q, hWnq, hqb, P⟩, ‹IsProper q›⟩ : MMP.Flips.ProperDivisorOver k sM) := by
  have hA := specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp
  obtain ⟨θ, -, hθ⟩ := exists_ringHom_of_specMap _ p q hpb.functionFieldMap_bijective
    hqb.functionFieldMap_bijective hA
  have hθp := functionFieldMap_comp_eq_of_specMap _ θ hθ p q hA
  have hψθ := specMap_comp_fromFunctionField_of_isInverse hψ θ hθ
  obtain ⟨e, he1, he2⟩ := id hψ
  refine ⟨e.symm.toPartialMap, p, hpb, he2, ?_, ?_⟩
  · set g := e.symm.toPartialMap
    have hx : genericPoint M ∈ g.domain :=
      (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
    have hA : genericPoint W ∈ q ⁻¹ᵁ g.domain := by
      change q (genericPoint W) ∈ g.domain
      rw [map_genericPoint_of_isDominant]
      exact hx
    refine hom_eq_of_fromSpecStalkOfMem_eq _ hA ?_
    have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫
        g.domain.fromSpecStalkOfMem (genericPoint M) hx =
        (q ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint W) hA ≫ (q ∣_ g.domain) := by
      rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
        Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact functionFieldMap_fromSpecStalk q
    rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc, ← c1,
      Category.assoc, ← partialMap_fromFunctionField_eq g hx,
      ← Scheme.RationalMap.fromFunctionField_toRationalMap,
      show g.toRationalMap = ψ from he2, ← hθp,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψθ]
    exact (functionFieldMap_fromSpecStalk p).symm
  · exact divisorialValuation_comap_functionFieldMap_eq p P Γ heq

end FunctionField

/-! ### Exceptional divisors over the target -/

section Exceptional

open MMP.Flips

private theorem topologicalKrullDim_closure_singleton_add_coheight {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (x : Y) :
    topologicalKrullDim (closure {x} : Set Y) + Order.coheight x = topologicalKrullDim Y := by
  let _ : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint x)
  rwa [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at h

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + c = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_add, top_add]
      rw [this] at h
      exact ENat.top_ne_natCast n (WithBot.coe_injective h)
    | coe d =>
      induction c using ENat.recTopCoe with
      | top =>
        exfalso
        have : ((d : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
          rw [← WithBot.coe_add, add_top]
        rw [this] at h
        exact ENat.top_ne_natCast n (WithBot.coe_injective h)
      | coe c =>
        have h' : d + c = n := by exact_mod_cast h
        have e1 : (((d : ℕ∞) : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞)) ↔ d + 2 ≤ n := by
          rw [show ((d : ℕ∞) : WithBot ℕ∞) + 2 = (((d + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) from rfl,
            show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe,
            Nat.cast_le]
        rw [e1]
        constructor
        · intro h2
          exact_mod_cast (show 2 ≤ c by omega)
        · intro h2
          have : 2 ≤ c := by exact_mod_cast h2
          omega

private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

private theorem two_le_of_not_le_one {c : ℕ∞} (h : ¬ c ≤ 1) : 2 ≤ c := by
  simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h)

/-- **Strict transforms and the induced map.** Let `p : W ⟶ X` be a proper birational morphism
of normal varieties with inverse `h`, and `q : W ⟶ M` with `h ≫ q = φ`. The strict transform `E`
on `W` of a prime divisor `Γ` of `X` satisfies `p(η_E) = η_Γ`; `φ` sends `Γ` to `Q` exactly when
`q(η_E) = η_Q`, and `Γ` is `φ`-exceptional when `q(η_E)` has coheight at least two. -/
private theorem exists_strictTransform_comp {k : Type u} [Field k] {X M W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [IsSeparated (M ↘ ⊤_ Scheme)]
    (hX : IsNormalVariety k sX) (p : W ⟶ X) (q : W ⟶ M) (h : X.RationalMap W) [IsProper p]
    (hWnp : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hinv : RationalMap.IsInverse p.toRationalMap h) {φ : X.RationalMap M}
    (hφ : h.compHom q = φ) (Γ : MMP.Mori.PrimeDivisor X) :
    ∃ E : MMP.Mori.PrimeDivisor W, p E.genericPoint = Γ.genericPoint ∧
      (∀ Q : MMP.Mori.PrimeDivisor M, RationalMap.transformPrimeDivisor φ Γ = some Q ↔
        q E.genericPoint = Q.genericPoint) ∧
      (2 ≤ Order.coheight (q E.genericPoint) → RationalMap.IsExceptional φ Γ) := by
  obtain ⟨E, h', hP', hh', hE, hpE, -⟩ := exists_strictTransform hX p h hWnp hpb hinv Γ
  have hg : (h'.compHom q).toRationalMap = φ := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hh', hφ]
  have hgE : (h'.compHom q).hom ⟨Γ.genericPoint, hP'⟩ = q E.genericPoint := by
    rw [hE]
    rfl
  refine ⟨E, hpE, fun Q => ⟨fun hQ => ?_, fun hQ => ?_⟩, fun h2 => ?_⟩
  · exact ((genericPoint_eq_of_transformPrimeDivisor_eq_some hQ (h'.compHom q) hg hP').trans
      hgE).symm
  · exact transformPrimeDivisor_eq_some_of_genericPoint_eq (h'.compHom q) hg hP'
      (by rw [hgE, hQ])
  · refine Or.inr ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨_, hP', hg⟩, ?_⟩
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
    intro x hx
    have hx' : x ∈ (MMP.Mori.RationalMap.transform φ Γ.idealSheaf.support : Set M) := hx
    rw [coe_transform_eq_closure_singleton (h'.compHom q) hg Γ hP', hgE] at hx'
    exact h2.trans (Order.coheight_anti
      (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hx')))

end Exceptional

end Proof_lem_fourfold_projective_lc_log_model_comparison

namespace MMP.Fourfold

open Proof_lem_fourfold_projective_lc_log_model_comparison

open MMP.Mori

open Classical in
/-- **Comparison for a projective lc log minimal model.** Let `(X/Z, B)` be an effective lc pair
with rational boundary, `X` and `Z` normal projective, and let `(M/Z, B_M)` with `φ : X ⤏ M` be
a log minimal model of `(X/Z, B)`. Let `p : W ⟶ X`, `q : W ⟶ M` be a common resolution:
`W` a smooth variety, `p` and `q` projective birational, `q ∘ p⁻¹ = φ`, with a canonical divisor
`K_W` of `W` such that `p_* K_W = K_X` and `q_* K_W = K_M`. If `G_X = p^*(K_X + B)` and
`G_M = q^*(K_M + B_M)`, then `F = G_X - G_M` is effective and every prime divisor of `W` in its
support is exceptional over `M`. -/
@[mmp "lem_fourfold_projective_lc_log_model_comparison"]
public theorem IsLogMinimalModel.nonneg_sub_and_isExceptionalPrimeDivisor
    {k : Type u} [Field k] {X Z M W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sM : M ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M] [LocallyOfFiniteType sM]
    [QuasiCompact sM]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsNormal Z]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    {π : X ⟶ Z} {πM : M ⟶ Z} {B : QDivisor X} {KX : Divisor X} {KM : Divisor M}
    {BM : QDivisor M} {φ : X.RationalMap M}
    (hM : IsLogMinimalModel sX sZ sM π πM B KM BM φ)
    {sW : W ⟶ Spec (.of k)} (hW : MMP.Mori.IsVariety k sW) (hWs : MMP.Mori.IsSmoothScheme sW)
    {p : W ⟶ X} {q : W ⟶ M} (hpX : p ≫ sX = sW) (hqM : q ≫ sM = sW)
    (hp : IsProjectiveMorphism p) (hq : IsProjectiveMorphism q)
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    {h : X.RationalMap W} (hh : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hφ : h.compHom q = φ)
    (hKW : ∃ (n : ℕ) (KW : Divisor W), KW.IsCanonicalDivisor sW n ∧
      MMP.Mori.RationalMap.transformDivisor p.toRationalMap KW = KX ∧
      MMP.Mori.RationalMap.transformDivisor q.toRationalMap KW = KM)
    {GX GM : RDivisor W}
    (hGX : MMP.Flips.IsRCartierPullback p
      (MMP.Flips.logCanonicalDivisor KX (QDivisor.toRDivisor B)) GX)
    (hGM : MMP.Flips.IsRCartierPullback q
      (MMP.Flips.logCanonicalDivisor KM (QDivisor.toRDivisor BM)) GM) :
    0 ≤ GX - GM ∧
      ∀ P, (GX - GM).coeff P ≠ 0 → MMP.Flips.IsExceptionalPrimeDivisor sM q P := by
  classical
  subst hpX
  -- the varieties and morphisms
  have hXn : IsNormalVariety k sX := hM.isNormalVariety
  have hWn : IsNormalVariety k (p ≫ sX) := ⟨hW, inferInstance⟩
  have hWnq : IsNormalVariety k (q ≫ sM) := by rwa [hqM]
  have hZv := (MMP.Mori.isProjectiveVariety_iff k sZ).mp hZp
  have hXv := (MMP.Mori.isProjectiveVariety_iff k sX).mp hXp
  have hsMp : IsProjectiveMorphism sM := by
    rw [← hM.comp_eq_model]
    exact IsProjectiveMorphism.comp hM.isProjectiveMorphism_model hZv.2
  have : IsProper sM := isProper_of_isProjectiveMorphism sM hsMp
  have hMv : MMP.Mori.IsVariety k sM :=
    (MMP.Mori.isVariety_iff k sM).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hMn : IsNormalVariety k sM := ⟨hMv, inferInstance⟩
  have hMp : MMP.Mori.IsProjectiveVariety k sM :=
    (MMP.Mori.isProjectiveVariety_iff k sM).mpr ⟨hMv, hsMp⟩
  have hWp : MMP.Mori.IsProjectiveVariety k (p ≫ sX) :=
    (MMP.Mori.isProjectiveVariety_iff k _).mpr ⟨hW, IsProjectiveMorphism.comp hp hXv.2⟩
  have := hXv.1
  have := hZv.1
  have := hW
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have := isSeparated_toTerminal sX
  have := isSeparated_toTerminal sM
  have := isSeparated_toTerminal sZ
  have hpbij := hpb.functionFieldMap_bijective
  have hqbij := hqb.functionFieldMap_bijective
  have hWsq : IsSmoothScheme (q ≫ sM) := by rwa [hqM]
  -- canonical divisors and compatible forms
  obtain ⟨n, KW, hKWc, hKWX, hKWM⟩ := hKW
  have hKWq : KW.IsCanonicalDivisor (q ≫ sM) n := by rwa [hqM]
  obtain ⟨⟨-, n₀, K₀, hK₀, -⟩, -, hlc⟩ := hM.isLogCanonicalPair
  obtain ⟨n₁, hKM⟩ := hM.isCanonicalDivisor
  have : MMP.Mori.IsVariety k (q ≫ sM) := hWnq.1
  obtain rfl : n₀ = n := by
    exact_mod_cast hK₀.topologicalKrullDim_eq.symm.trans
      ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).trans
        hKWc.topologicalKrullDim_eq)
  obtain rfl : n₁ = n₀ := by
    exact_mod_cast hKM.topologicalKrullDim_eq.symm.trans
      ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sM (q ≫ sM) hqb).trans
        hKWc.topologicalKrullDim_eq)
  obtain ⟨ωX, hωX0, hωX, hωXW, hKXc⟩ :=
    exists_form_of_transformDivisor_eq hXn p hWn hpb hWs hK₀ hKWc hKWX
  obtain ⟨ωM, hωM0, hωM, hωMW, -⟩ :=
    exists_form_of_transformDivisor_eq hMn q hWnq hqb hWsq hKM hKWq hKWM
  -- log discrepancies on `W`
  have hlogX : ∀ P : MMP.Mori.PrimeDivisor W, MMP.Intersection.IsLogDiscrepancy sX n₁
      (QDivisor.toRDivisor B) ⟨W, p, hWn, hpb, P⟩ (1 + (KW.coeff P : ℝ) - GX.coeff P) := by
    intro P
    have := isLogDiscrepancy_of_ordForm hXn p hWn hpb hKXc ωX hωX0 hωX hGX P
    rwa [hωXW P] at this
  have hlogM : ∀ P : MMP.Mori.PrimeDivisor W, MMP.Intersection.IsLogDiscrepancy sM n₁
      (QDivisor.toRDivisor BM) ⟨W, q, hWnq, hqb, P⟩ (1 + (KW.coeff P : ℝ) - GM.coeff P) := by
    intro P
    have := isLogDiscrepancy_of_ordForm hMn q hWnq hqb hKM ωM hωM0 hωM hGM P
    rwa [hωMW P] at this
  -- strict transforms of the prime divisors of `X`
  have hstrict := exists_strictTransform_comp hXn p q h hWn hpb hh hφ
  -- the comparison vanishes along strict transforms of retained prime divisors
  have hret : ∀ (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor X)
      (Q : MMP.Mori.PrimeDivisor M), p P.genericPoint = Γ.genericPoint →
      q P.genericPoint = Q.genericPoint → (GX - GM).coeff P = 0 := by
    intro P Γ Q hPΓ hPQ
    obtain ⟨E, hpE, hiff, -⟩ := hstrict Γ
    obtain rfl := eq_of_apply_genericPoint_eq p hpbij hpE hPΓ
    have hΓQ := (hiff Q).mpr hPQ
    have huniq : ∀ Γ', RationalMap.transformPrimeDivisor φ Γ' = some Q → Γ' = Γ := by
      intro Γ' hΓ'
      obtain ⟨E', hpE', hiff', -⟩ := hstrict Γ'
      obtain rfl := eq_of_apply_genericPoint_eq q hqbij ((hiff' Q).mp hΓ') hPQ
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hpE'.symm.trans hpE)
    have hBM : BM.coeff Q = B.coeff Γ := by
      have hnot : ¬ MMP.Flips.RationalMap.IsInverseExceptional φ Q := fun hQ => hQ Γ hΓQ
      rw [hM.coeff_boundary Q, if_neg hnot, add_zero]
      exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hΓQ huniq B
    rw [DivisorWithCoeffs.coeff_sub,
      coeff_isRCartierPullback_logCanonicalDivisor hXn p hWn hpb hKWX hGX hpE,
      coeff_isRCartierPullback_logCanonicalDivisor hMn q hWnq hqb hKWM hGM hPQ, hBM]
    ring
  -- the comparison is positive along strict transforms of contracted prime divisors
  obtain ⟨m, r, L, L', hLc, hD, -, -⟩ := id hGX
  have hcon : ∀ (P : MMP.Mori.PrimeDivisor W) (Γ : MMP.Mori.PrimeDivisor X),
      p P.genericPoint = Γ.genericPoint → 2 ≤ Order.coheight (q P.genericPoint) →
      0 < (GX - GM).coeff P := by
    intro P Γ hPΓ h2
    obtain ⟨E, hpE, -, hexc⟩ := hstrict Γ
    obtain rfl := eq_of_apply_genericPoint_eq p hpbij hpE hPΓ
    have : ValuationRing (X.presheaf.stalk (p E.genericPoint)) := by
      rw [hpE]; exact valuationRing_stalk_of_coheight_le_one Γ.coheight_genericPoint.le
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing p hpbij E.genericPoint
    have hψ := hM.isBirational.isInverse_inverse
    have hE := isRealizedOver_of_apply_eq p q h hpb hqb hh hφ hψ hWnq Γ E hpE
    have ha := isLogDiscrepancy_ofPrimeDivisor_of_ordForm hXn hKXc ωX hωX0 hωX hLc hD Γ
    have hlt := hM.logDiscrepancy_lt Γ (hexc h2) _ hψ _ hE n₁ _ _ ha (hlogM E)
    rw [DivisorWithCoeffs.coeff_sub,
      coeff_isRCartierPullback_logCanonicalDivisor hXn p hWn hpb hKWX hGX hpE]
    rw [QDivisor.coeff_toRDivisor] at hlt
    linarith
  -- the push-forward of the comparison to `X` is effective
  have hpush : 0 ≤ RationalMap.transformDivisor (X := W) p.toRationalMap (GX - GM) := by
    refine Finsupp.le_def.mpr fun Γ => ?_
    obtain ⟨E, heq, -, htr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn hWn hpb Γ
    rw [htr]
    by_cases hc : Order.coheight (q E.genericPoint) ≤ 1
    · obtain ⟨Q, hEQ, -⟩ := exists_primeDivisor_of_coheight_le_one q hqbij E hc
      exact (hret E Γ Q heq hEQ).ge
    · exact (hcon E Γ heq (two_le_of_not_le_one hc)).le
  -- the base
  have hpq : p ≫ π = q ≫ πM := by
    refine hom_eq_of_fromSpecStalk_eq ?_
    have h1 := specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hh hφ
    rw [← Category.assoc, ← functionFieldMap_fromSpecStalk p, Category.assoc,
      ← MMP.Flips.RationalMap.fromFunctionField_hom, ← hM.isOver,
      MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc, h1, Category.assoc]
  -- the comparison is effective
  have hL : MMP.Flips.IsCartierCombination
      (MMP.Flips.logCanonicalDivisor KX (QDivisor.toRDivisor B)) :=
    ⟨m, r, L, hLc, by rw [hD]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hnonneg : 0 ≤ GX - GM :=
    MMP.Fourfold.nonneg_sub_of_nonneg_transformDivisor_sub (p ≫ sX) sX sM hWn hWp hXn hXp hMn hMp
      π πM p q rfl hqM hpq hp hpb hq hqb hL
      (isRelativelyNef_logCanonicalDivisor hM.isRelativelyNef) hGX hGM hpush
  refine ⟨hnonneg, fun P hP => ?_⟩
  -- the comparison is exceptional over `M`
  refine ⟨hWnq, hqb, inferInstance, ?_⟩
  rw [isExceptional_iff_two_le_coheight hKM.topologicalKrullDim_eq]
  by_contra hlt
  have hle := not_imp_comm.mp two_le_of_not_le_one hlt
  obtain ⟨Q, hPQ, -⟩ := exists_primeDivisor_of_coheight_le_one q hqbij P hle
  by_cases hpc : Order.coheight (p P.genericPoint) ≤ 1
  · obtain ⟨Γ, hPΓ, -⟩ := exists_primeDivisor_of_coheight_le_one p hpbij P hpc
    exact hP (hret P Γ Q hPΓ hPQ)
  · have hQ : MMP.Flips.RationalMap.IsInverseExceptional φ Q := by
      intro Γ hΓ
      obtain ⟨E, hpE, hiff, -⟩ := hstrict Γ
      obtain rfl := eq_of_apply_genericPoint_eq q hqbij ((hiff Q).mp hΓ) hPQ
      rw [hpE] at hpc
      exact hpc Γ.coheight_genericPoint.le
    have hBM : BM.coeff Q = 1 := by
      rw [hM.coeff_boundary Q, if_pos hQ, show (RationalMap.transformDivisor φ B).coeff Q = 0 from
        MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne hQ B, zero_add]
    have ha := hlc n₁ _ _ (hlogX P)
    have h0 : 0 ≤ (GX - GM).coeff P := Finsupp.le_def.mp hnonneg P
    have hF : (GX - GM).coeff P = GX.coeff P - KW.coeff P - 1 := by
      rw [DivisorWithCoeffs.coeff_sub,
        coeff_isRCartierPullback_logCanonicalDivisor hMn q hWnq hqb hKWM hGM hPQ, hBM]
      push_cast
      ring
    exact hP (le_antisymm (by linarith) h0)

end MMP.Fourfold

namespace Proof_lem_fourfold_theta_identity_on_model

open Proof_lem_fourfold_projective_lc_log_model_comparison (isSeparated_toTerminal
  partialMap_fromFunctionField_eq specMap_functionFieldMap_fromFunctionField_of_isInverse
  withBot_add_two_le_iff)

open MMP.Mori MMP.Flips

/-! ### Numerical equivalence -/

section Numerical

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The empty presentation of `0` computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber k sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every value of `0 · C` is zero. -/
private theorem eq_zero_of_isRIntersectionNumber_zero (C : ProperCurve sX) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX 0 r L C x) : x = 0 :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ x 0 h (isRIntersectionNumber_zero C)

/-- A real combination `a D₁ + b D₂` of `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_smul_add_smul {D₁ D₂ : RDivisor X}
    (h₁ : IsCartierCombination D₁) (h₂ : IsCartierCombination D₂) (a b : ℝ) :
    IsCartierCombination (a • D₁ + b • D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append (a • r₁) (b • r₂), Fin.append L₁ L₂, fun j => ?_, ?_⟩
  · refine Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier) (fun i => ?_)
      (fun i => ?_) j
    · simpa using hL₁ i
    · simpa using hL₂ i
  · simp [Fin.sum_univ_add, Finset.smul_sum, smul_smul]

/-- An `ℝ`-Cartier combination `D` has an intersection number with a curve `C` as soon as some
Cartier divisor has one with `C` (computed on a normalization of `C`). -/
private theorem exists_isRIntersectionNumber (C : ProperCurve sX) {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d)
    {D : RDivisor X} (hD : IsCartierCombination D) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L' : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX D r L' C x := by
  obtain ⟨C', ν, hν, hdim, -⟩ := h
  obtain ⟨m, r, L', hL', hD⟩ := hD
  exact ⟨m, r, L', _, hL', fun j => _, by simpa only [toRDivisor_eq_mapCoeffs] using hD,
    fun j => ⟨C', ν, hν, hdim, rfl⟩, rfl⟩

/-- If `N₁ ≡_f N₂` then `N₁ - N₂ ≡_f 0`. -/
private theorem isNumericallyTrivialOver_sub {f : X ⟶ Y} {N₁ N₂ : RDivisor X}
    (h : IsNumericallyEquivalentOver k sX f N₁ N₂) :
    IsNumericallyTrivialOver k sX f (N₁ - N₂) := by
  obtain ⟨h₁, h₂, h⟩ := h
  refine ⟨by simpa [sub_eq_add_neg] using isCartierCombination_smul_add_smul h₁ h₂ 1 (-1),
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m r L x m' r' L' x' hx hx' => ?_⟩
  rw [eq_zero_of_isRIntersectionNumber_zero C hx']
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨hL, d, hD, -, rfl⟩ := hx
    simp
  · obtain ⟨hL, d, -, hd, -⟩ := id hx
    obtain ⟨m₁, r₁, L₁, x₁, hx₁⟩ := exists_isRIntersectionNumber C (hd ⟨0, hm⟩) h₁
    obtain ⟨m₂, r₂, L₂, x₂, hx₂⟩ := exists_isRIntersectionNumber C (hd ⟨0, hm⟩) h₂
    have he := h C hC _ _ _ _ _ _ _ _ hx₁ hx₂
    have hl := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ r₁ L₁ r₂ L₂ x₁ x₂ 1 (-1)
      hx₁ hx₂
    rw [show (1 : ℝ) • N₁ + (-1 : ℝ) • N₂ = N₁ - N₂ by module] at hl
    rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx hl, he]
    ring

/-- Adding a numerically trivial divisor does not change the numerical class. -/
private theorem isNumericallyEquivalentOver_add_of_isNumericallyTrivialOver {f : X ⟶ Y}
    {A T : RDivisor X} (hA : IsCartierCombination A) (hT : IsNumericallyTrivialOver k sX f T) :
    IsNumericallyEquivalentOver k sX f (A + T) A := by
  refine ⟨by simpa using isCartierCombination_smul_add_smul hA hT.1 1 1, hA,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have hl := (IsRIntersectionNumber.eq_and_linear k sX C).2 _ _ r₁ L₁ r₂ L₂ x₁ x₂ 1 (-1) h₁ h₂
  rw [show (1 : ℝ) • (A + T) + (-1 : ℝ) • A = T by module] at hl
  have := hT.2.2 C hC _ _ _ _ _ _ _ _ hl (isRIntersectionNumber_zero C)
  linarith

end Numerical

/-! ### Presentations and pull-backs on a `ℚ`-factorial variety -/

section QFactorial

/-- On a `ℚ`-factorial variety every `ℝ`-divisor `D` is a real combination of Cartier divisors,
with rational coefficients when `D` is rational. -/
private theorem exists_presentation_of_isQFactorial {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Fourfold.IsQFactorial sX) (D : RDivisor X) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
      (MMP.Intersection.WeilRDivisor.IsRational D → ∀ j, ∃ a : ℚ, r j = a) := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor X => hX.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine ⟨_, fun j => D (e.symm j) / m (e.symm j),
    fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor X) 1,
    fun j => hc _, ?_, fun hD j => ?_⟩
  · have hterm : ∀ P : MMP.Mori.PrimeDivisor X, (D P / m P) •
        Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor X)) =
          Finsupp.single P (D P) := by
      intro P
      ext Q
      have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
      simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
      by_cases hQ : P = Q
      · subst hQ
        simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
      · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
    rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
        Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor X) 1 :
          Divisor X)))]
    rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
        Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor X)))]
    simp_rw [hterm]
    exact (Finsupp.sum_single D).symm
  · obtain ⟨a, ha⟩ := hD (e.symm j)
    exact ⟨a / m (e.symm j), by
      change D _ / _ = _
      rw [← DivisorWithCoeffs.coeff_apply, ha]; push_cast; rfl⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Fourfold.IsQFactorial sX) (D : RDivisor X) : IsCartierCombination D := by
  obtain ⟨m, r, L, hL, hD, -⟩ := exists_presentation_of_isQFactorial hX D
  exact ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hD⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor has a pull-back along a dominant morphism; it is
effective when `D` is, and rational when `D` is. -/
private theorem exists_isRCartierPullback_of_isQFactorial {k : Type u} [Field k]
    {T X : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Fourfold.IsQFactorial sX) (f : T ⟶ X) [IsDominant f] (D : RDivisor X) :
    ∃ G : RDivisor T, IsRCartierPullback f D G ∧ ((∀ P, 0 ≤ D.coeff P) → ∀ E, 0 ≤ G.coeff E) ∧
      (MMP.Intersection.WeilRDivisor.IsRational D →
        MMP.Intersection.WeilRDivisor.IsRational G) := by
  obtain ⟨m, r, L, hL, hD, hr⟩ := exists_presentation_of_isQFactorial hX D
  have hp := fun j => Divisor.isPullback_pullback (f := f) (hL j)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f (L j))
  have hG : IsRCartierPullback f D (∑ j, r j • Divisor.toRDivisor ((L j).pullback (hL j)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f (L j)))) :=
    ⟨m, r, L, _, hL, hD, fun j => ⟨_, hp j⟩, rfl⟩
  refine ⟨_, hG, fun hD0 => ?_, fun hDr E => ?_⟩
  · have hRC : MMP.Fourfold.RDivisor.IsRCartier D := ⟨m, r, L, hL, fun Γ => by
      rw [hD, MMP.Fourfold.coeff_sum_smul_toRDivisor]⟩
    have h0 : (0 : RDivisor X) ≤ D := Finsupp.le_def.mpr hD0
    have := (MMP.Fourfold.isEffective_of_isRCartierPullback f hRC h0).2 _ hG
    exact fun E => Finsupp.le_def.mp this E
  · choose a ha using hr hDr
    refine ⟨∑ j, a j * (((L j).pullback (hL j)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f (L j))).coeff E : ℚ),
      ?_⟩
    rw [MMP.Fourfold.coeff_sum_smul_toRDivisor]
    push_cast
    simp only [ha]

/-- If `D` pulls back to `G` and `D'` to `G'`, then `D - D'` pulls back to `G - G'`. -/
private theorem isRCartierPullback_sub {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D D' : RDivisor X} {G G' : RDivisor Y}
    (h : IsRCartierPullback f D G) (h' : IsRCartierPullback f D' G') :
    IsRCartierPullback f (D - D') (G - G') := by
  have := MMP.Fourfold.isRCartierPullback_add h (MMP.Fourfold.isRCartierPullback_smul (-1) h')
  simpa only [neg_one_smul, ← sub_eq_add_neg] using this

end QFactorial

/-! ### Strict transforms on a common resolution -/

section StrictTransform

/-- The image of a prime divisor under a proper morphism sending its generic point to the
generic point of a prime divisor `P` is the support of `P`. -/
private theorem image_support_eq_of_map_genericPoint {W Y : Scheme.{u}} (q : W ⟶ Y) [IsProper q]
    (E : MMP.Mori.PrimeDivisor W) (P : MMP.Mori.PrimeDivisor Y)
    (h : q E.genericPoint = P.genericPoint) :
    q '' E.support = closure {P.genericPoint} := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
  apply le_antisymm
  · refine (image_closure_subset_closure_image q.continuous).trans ?_
    rw [Set.image_singleton, h]
  · have hc : IsClosed (q '' closure {E.genericPoint}) := q.isClosedMap _ isClosed_closure
    refine closure_minimal ?_ hc
    rw [Set.singleton_subset_iff, ← h]
    exact Set.mem_image_of_mem _ (subset_closure rfl)

/-- A strict transform is not exceptional. -/
private theorem not_isExceptionalPrimeDivisor_of_map_genericPoint {k : Type u} [Field k]
    {W Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {nY : ℕ}
    (hdim : topologicalKrullDim Y = nY) (q : W ⟶ Y) [IsProper q]
    (FW : MMP.Mori.PrimeDivisor W) (F : MMP.Mori.PrimeDivisor Y)
    (hFWeq : q FW.genericPoint = F.genericPoint) :
    ¬ IsExceptionalPrimeDivisor sY q FW := by
  intro hex
  obtain ⟨hY', hf', hp', hexc⟩ := hex
  change topologicalKrullDim (q '' FW.support : Set Y) + 2 ≤ topologicalKrullDim Y at hexc
  rw [image_support_eq_of_map_genericPoint q FW F hFWeq] at hexc
  have h1 := topologicalKrullDim_closure_singleton_add_coheight sY F.genericPoint
  rw [F.coheight_genericPoint, hdim] at h1
  rw [hdim] at hexc
  exact absurd ((withBot_add_two_le_iff h1).mp hexc) (by norm_num)

/-- Two morphisms from a reduced scheme to a separated scheme with the same rational map are
equal. -/
private theorem eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (f g : X ⟶ Y) (h : f.toRationalMap = g.toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  change X.topIso.hom ≫ f = (⊤ : X.Opens).ι ≫ g at this
  rwa [← Scheme.topIso_hom, cancel_epi] at this

/-- Let `p : W ⟶ X`, `q : W ⟶ Y` be a common resolution of `φ = q ∘ p⁻¹`, and `φ_* P = F`. The
prime divisor `F_W` of `W` over `F` lies over `P`, and `p` is a local isomorphism at its generic
point. -/
private theorem map_genericPoint_eq_of_transformPrimeDivisor_eq_some {k : Type u} [Field k]
    {W X Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (hY : IsNormalVariety k sY) {p : W ⟶ X} {q : W ⟶ Y} (hWp : IsNormalVariety k (p ≫ sX))
    [IsProper p] [IsProper q] (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    {h : X.RationalMap W} (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    {φ : X.RationalMap Y} (hφ : h.compHom q = φ) {P : MMP.Mori.PrimeDivisor X}
    {F : MMP.Mori.PrimeDivisor Y}
    (hPF : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F)
    (FW : MMP.Mori.PrimeDivisor W) (hFW : q FW.genericPoint = F.genericPoint)
    [IsIso (q.stalkMap FW.genericPoint)] :
    p FW.genericPoint = P.genericPoint ∧ IsIso (p.stalkMap FW.genericPoint) := by
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_toTerminal sY
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  -- the strict transform `P_W` of `P`
  obtain ⟨PW, hPWeq, hPWiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hX hWp hpb P
  -- a representative of `φ` defined at the generic point of `P`
  obtain ⟨hdef, -⟩ := MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hPF
  obtain ⟨g', hPg, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  have hFg := genericPoint_eq_of_transformPrimeDivisor_eq_some hPF g' hg' hPg
  have hPWdom : p PW.genericPoint ∈ g'.domain := by rw [hPWeq]; exact hPg
  -- `φ ∘ p` on `p⁻¹(dom g')` represents `q`
  let χ : W.PartialMap Y :=
    { domain := p ⁻¹ᵁ g'.domain
      dense_domain := (p ⁻¹ᵁ g'.domain).2.dense ⟨PW.genericPoint, hPWdom⟩
      hom := (p ∣_ g'.domain) ≫ g'.hom }
  have hX' : genericPoint X ∈ g'.domain := (genericPoint_specializes _).mem_open g'.domain.2 hPg
  have hgen : genericPoint W ∈ χ.domain := by
    change p (genericPoint W) ∈ g'.domain
    rw [map_genericPoint_of_isDominant]
    exact hX'
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
      g'.domain.fromSpecStalkOfMem (genericPoint X) hX' =
      (p ⁻¹ᵁ g'.domain).fromSpecStalkOfMem (genericPoint W) hgen ≫ (p ∣_ g'.domain) := by
    rw [← cancel_mono g'.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk p
  have hχ : χ.toRationalMap = q.toPartialMap.toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [show q.toPartialMap.toRationalMap = q.toRationalMap from rfl,
      MMP.Flips.RationalMap.fromFunctionField_hom q,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq χ hgen]
    change (p ⁻¹ᵁ g'.domain).fromSpecStalkOfMem _ hgen ≫ (p ∣_ g'.domain) ≫ g'.hom = _
    rw [← Category.assoc, ← c1, Category.assoc, ← partialMap_fromFunctionField_eq g' hX',
      ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg',
      specMap_functionFieldMap_fromFunctionField_of_isInverse _ _ _ _ hinv hφ]
  -- hence `q(P_W) = F`
  have e1 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hχ
    (show PW.genericPoint ∈ χ.domain from hPWdom)
    (show PW.genericPoint ∈ q.toPartialMap.domain from trivial)
  have hqPW : q PW.genericPoint = F.genericPoint := by
    have l : χ.hom ⟨PW.genericPoint, hPWdom⟩ = g'.hom ⟨P.genericPoint, hPg⟩ := by
      change g'.hom ((p ∣_ g'.domain) ⟨PW.genericPoint,
        (hPWdom : PW.genericPoint ∈ p ⁻¹ᵁ g'.domain)⟩) = _
      congr 1
      exact Subtype.ext ((morphismRestrict_base_coe p g'.domain _).trans hPWeq)
    have r : q.toPartialMap.hom ⟨PW.genericPoint, trivial⟩ = q PW.genericPoint := rfl
    rw [hFg, ← l, ← r]
    exact e1.symm
  -- so `P_W = F_W`
  have := F.isDiscreteValuationRing_localRing
  have hbij := hqb.functionFieldMap_bijective
  have : ValuationRing (Y.presheaf.stalk (q FW.genericPoint)) := by rw [hFW]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (q PW.genericPoint)) := by rw [hqPW]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij PW.genericPoint
  have hEE : FW.genericPoint = PW.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap q hbij (hqPW.trans hFW.symm)
  rw [hEE]
  exact ⟨hPWeq, hPWiso⟩

/-- A common resolution of a birational map over `Z` commutes over `Z`. -/
private theorem comp_eq_comp_of_isOver {W X Y Z : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {p : W ⟶ X} {q : W ⟶ Y} [IsDominant p]
    {h : X.RationalMap W} (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    {φ : X.RationalMap Y} (hφ : h.compHom q = φ) {π : X ⟶ Z} {πY : Y ⟶ Z}
    (hover : MMP.Flips.RationalMap.IsOver π πY φ) : p ≫ π = q ≫ πY := by
  refine eq_of_toRationalMap_eq _ _ (Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_)
  rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom,
    ← Category.assoc, ← functionFieldMap_fromSpecStalk p, Category.assoc,
    ← MMP.Flips.RationalMap.fromFunctionField_hom π,
    ← hover, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_of_isInverse _ _ _ _ hinv hφ, Category.assoc]

end StrictTransform

/-! ### The lc condition along a prime exceptional over `X` -/

section LogDiscrepancy

/-- Let `p : W ⟶ X`, `q : W ⟶ Y` be a common resolution comparing `K_X + B + t C` with an
adjoint on `Y`, and let `F_W` be a prime divisor of `W` over a prime `F` of `Y` along which
`p^*(K_X + B + t C)` has coefficient `ord_F K_Y + 1`. Then the log discrepancy of `F_W` with
respect to `(X, B + C)` is `-(1 - t) ord_{F_W} p^* C`; so if `(X, B + C)` is lc, `C ≥ 0` and
`t < 1`, the pull-back `p^* C` vanishes along `F_W`. -/
private theorem coeff_eq_zero_of_isRealLcPair {k : Type u} [Field k] [PerfectField k]
    {X Y W : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {φ : X.RationalMap Y} {KX : Divisor X} {KY : Divisor Y} {B C : RDivisor X} {BY : RDivisor Y}
    {t : ℝ} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W} {GX GY Cw : RDivisor W} {n₀ : ℕ}
    (hR : MMP.Fourfold.IsLogComparisonResolution sX sY sW φ KX (B + t • C) KY BY p q h GX GY)
    (hlc : MMP.Fourfold.IsRealLcPair sX (B + C)) (hKX : KX.IsCanonicalDivisor sX n₀)
    (hCw : IsRCartierPullback p C Cw) (hCw0 : ∀ E, 0 ≤ Cw.coeff E) (ht1 : t < 1)
    {F : MMP.Mori.PrimeDivisor Y} {FW : MMP.Mori.PrimeDivisor W}
    (htrq : ∀ D' : Divisor W,
      (MMP.Mori.RationalMap.transformDivisor q.toRationalMap D').coeff F = D'.coeff FW)
    (hGX : GX.coeff FW = KY.coeff F + 1) :
    Cw.coeff FW = 0 := by
  have hXn : IsNormalVariety k sX := hlc.1
  have hWnp : IsNormalVariety k (p ≫ sX) := by
    rw [hR.comp_eq_left]; exact ⟨hR.isVariety, inferInstance⟩
  have hpb := hR.isBirationalMorphism_left
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have : IsDominant p := hpb.isDominant
  have := hR.isVariety
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  -- compatible canonical divisors and forms
  obtain ⟨nW, KW, hKW, hKWX, hKWY⟩ := hR.exists_canonicalDivisor
  have hKY : KY.coeff F = KW.coeff FW := by rw [← hKWY]; exact htrq KW
  obtain rfl : nW = n₀ := by
    have := hXn.1
    have := hWnp.1
    have hdimW := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb
    exact_mod_cast hKW.topologicalKrullDim_eq.symm.trans
      (hdimW.symm.trans hKX.topologicalKrullDim_eq)
  have hKW' : KW.IsCanonicalDivisor (p ≫ sX) nW := by rw [hR.comp_eq_left]; exact hKW
  obtain ⟨ω, hω0, hωX, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXn hWnp hpb hKX hKW' hKWX
  -- a presentation of `K_X + B + C = (K_X + B + t C) + (1 - t) C` and its pull-back
  obtain ⟨m, r, L, L', hLc, hL, hLpb, hG⟩ := MMP.Fourfold.isRCartierPullback_add
    hR.isRCartierPullback_left (MMP.Fourfold.isRCartierPullback_smul (1 - t) hCw)
  let DWd : MMP.Mori.DivisorOver k sX := ⟨W, p, hWnp, hpb, FW⟩
  have hDW : MMP.Intersection.IsLogDiscrepancy sX nW (B + C) DWd
      (-((1 - t) * Cw.coeff FW)) := by
    refine ⟨hXn, inferInstanceAs (IsProper p), ω, hω0, ⟨KX, hKX, fun Γ => ?_⟩, m, r, L, L',
      hLc, fun Γ => ?_, hLpb, ?_⟩
    · rw [← hωX]; rfl
    · have := congrArg (fun D : MMP.Mori.RDivisor X => D Γ) hL
      simp only [MMP.Flips.logCanonicalDivisor, Finsupp.add_apply, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul] at this
      rw [← hωX] at this
      refine Eq.trans ?_ this
      have h1 : (Divisor.toRDivisor (divisorOfForm ω)) Γ = (Γ.ordForm ω : ℝ) := rfl
      rw [h1, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply]
      ring
    · have hord : DWd.ordPullback ω = KW.coeff FW := by
        rw [← hωW]; rfl
      have hG' : (GX + (1 - t) • Cw).coeff FW = ∑ i, r i * ((L' i).coeff FW : ℝ) := by
        rw [hG, MMP.Fourfold.coeff_sum_smul_toRDivisor]
      change _ = 1 + (DWd.ordPullback ω : ℝ) - ∑ i, r i * ((L' i).coeff FW : ℝ)
      rw [← hG', hord, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
        hGX, hKY]
      ring
  have h0 := hlc.2.2.2 nW DWd _ hDW
  have hc := hCw0 FW
  nlinarith [sub_pos.mpr ht1]

end LogDiscrepancy

end Proof_lem_fourfold_theta_identity_on_model

namespace MMP.Fourfold

open Proof_lem_fourfold_theta_identity_on_model MMP.Flips

open MMP.Mori

open Classical in
/-- **A floor-supported numerical identity survives a log minimal model.** Let `(X, B + C)` be
an lc pair with real boundary over `Z`, with `X` `ℚ`-factorial projective, `B, C ≥ 0`, and no
component of `C` in `⌊B⌋`. Suppose `α (K_X + B) ≡_Z C + N` with `α > 0`, `N ≥ 0` and `N`
supported in `⌊B⌋`. Let `0 < t ≤ 1`, and let `φ : X ⤏ Y` be a log minimal model of
`(X/Z, B + t C)` with boundary `B_Y + t C_Y`. Here `C_Y = φ_* C`, and `B_Y` is `φ_* B` plus
every prime divisor of `Y` exceptional over `X` with coefficient one. Then there is an effective
`ℝ`-divisor `N_Y` on `Y`, supported in `⌊B_Y⌋`, with `α (K_Y + B_Y) ≡_Z C_Y + N_Y`. If `B`,
`C`, `N` and `α` are rational, then `N_Y` can be chosen rational, and `B_Y` and `C_Y` are
rational. -/
@[mmp "lem_fourfold_theta_identity_on_model"]
public theorem exists_isNumericallyEquivalentOver_logCanonicalDivisor_of_isRealLogMinimalModel
    {k : Type u} [Field k] [CharZero k] {X Y Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX]
    [QuasiCompact sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hZp : MMP.Mori.IsProjectiveVariety k sZ)
    {π : X ⟶ Z} {πY : Y ⟶ Z} {KX : Divisor X} {KY : Divisor Y}
    {B C N : RDivisor X} {α t : ℝ}
    (hlc : IsRealLcPair sX (B + C)) (hQ : IsQFactorial sX)
    (hB : ∀ P, 0 ≤ B.coeff P) (hC : ∀ P, 0 ≤ C.coeff P)
    (hCB : ∀ P, C.coeff P ≠ 0 → B.coeff P < 1)
    (hα : 0 < α) (hN : ∀ P, 0 ≤ N.coeff P) (hNB : ∀ P, N.coeff P ≠ 0 → 1 ≤ B.coeff P)
    (hnum : MMP.Flips.IsNumericallyEquivalentOver k sX π
      (α • MMP.Flips.logCanonicalDivisor KX B) (C + N))
    (ht : 0 < t) (ht₁ : t ≤ 1)
    {φ : X.RationalMap Y} {BY : RDivisor Y}
    (hBY : ∀ F : MMP.Mori.PrimeDivisor Y,
      BY.coeff F = (MMP.Mori.RationalMap.transformDivisor φ B).coeff F +
        if MMP.Flips.RationalMap.IsInverseExceptional φ F then 1 else 0)
    (hY : IsRealLogMinimalModel sX sY sZ π πY KX (B + t • C) KY
      (BY + t • MMP.Mori.RationalMap.transformDivisor φ C) φ) :
    ∃ NY : RDivisor Y, (∀ F, 0 ≤ NY.coeff F) ∧ (∀ F, NY.coeff F ≠ 0 → 1 ≤ BY.coeff F) ∧
      MMP.Flips.IsNumericallyEquivalentOver k sY πY
        (α • MMP.Flips.logCanonicalDivisor KY BY)
        (MMP.Mori.RationalMap.transformDivisor φ C + NY) ∧
      (MMP.Intersection.WeilRDivisor.IsRational B → MMP.Intersection.WeilRDivisor.IsRational C →
        MMP.Intersection.WeilRDivisor.IsRational N → (∃ a : ℚ, α = a) →
        MMP.Intersection.WeilRDivisor.IsRational BY ∧
          MMP.Intersection.WeilRDivisor.IsRational
            (MMP.Mori.RationalMap.transformDivisor φ C) ∧
          MMP.Intersection.WeilRDivisor.IsRational NY) := by
  classical
  set CY := MMP.Mori.RationalMap.transformDivisor φ C
  obtain ⟨W, _, _, _, sW, p, q, h, GX, GY, hR⟩ := hY.exists_resolution
  -- the varieties and morphisms
  have hXn : IsNormalVariety k sX := hlc.1
  have hYn : IsNormalVariety k sY := hY.isNormalVariety_model
  have hWn : IsNormalVariety k sW := ⟨hR.isVariety, inferInstance⟩
  have hWnp : IsNormalVariety k (p ≫ sX) := by rwa [hR.comp_eq_left]
  have hWnq : IsNormalVariety k (q ≫ sY) := by rwa [hR.comp_eq_right]
  have := isProper_of_isProjectiveMorphism p hR.isProjectiveMorphism_left
  have := isProper_of_isProjectiveMorphism q hR.isProjectiveMorphism_right
  have hpb := hR.isBirationalMorphism_left
  have hqb := hR.isBirationalMorphism_right
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have := hR.isVariety
  have : LocallyOfFiniteType sW := hR.isVariety.toLocallyOfFiniteType
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
  obtain ⟨nY, hKYc⟩ := hY.isCanonicalDivisor_model
  have hdimY : topologicalKrullDim Y = nY := hKYc.topologicalKrullDim_eq
  -- pull-backs of `C` and `N` to `W`
  obtain ⟨Cw, hCw, hCw0, hCwr⟩ := exists_isRCartierPullback_of_isQFactorial hQ p C
  obtain ⟨Nw, hNw, hNw0, hNwr⟩ := exists_isRCartierPullback_of_isQFactorial hQ p N
  -- the numerically trivial divisor `D = α (K_X + B) - (C + N)` and its pull-back
  set D : RDivisor X := α • logCanonicalDivisor KX B - (C + N) with hDdef
  have hD : IsNumericallyTrivialOver k sX π D := isNumericallyTrivialOver_sub hnum
  set DW : RDivisor W := α • GX - (1 + α * t) • Cw - Nw with hDWdef
  have hDW : IsRCartierPullback p D DW := by
    convert isRCartierPullback_sub (isRCartierPullback_sub
      (MMP.Fourfold.isRCartierPullback_smul α hR.isRCartierPullback_left)
      (MMP.Fourfold.isRCartierPullback_smul (1 + α * t) hCw)) hNw using 1
    simp only [hDdef, logCanonicalDivisor]
    module
  have hpq : p ≫ π = q ≫ πY := by
    have : IsSeparated sZ := hZp.toIsSeparated
    have := Proof_lem_fourfold_projective_lc_log_model_comparison.isSeparated_toTerminal sZ
    exact comp_eq_comp_of_isOver hR.isInverse hR.compHom_eq hY.isOver
  have hWp : MMP.Mori.IsProjectiveVariety k sW := by
    have hpr : IsProjectiveMorphism (p ≫ sX) :=
      hR.isProjectiveMorphism_left.comp hXp.isProjective
    rw [hR.comp_eq_left] at hpr
    exact { toIsVariety := hR.isVariety, isProjective := hpr }
  obtain ⟨hT, -⟩ := MMP.Fourfold.isNumericallyTrivialOver_transformDivisor_and_isRCartierPullback
    sW sX sY sZ hWn hWp hXn hXp hY.isQFactorial hY.isProjectiveVariety_model hZp π πY hY.comp_eq
    hY.comp_eq_model p q hR.comp_eq_left hR.comp_eq_right hpq hR.isProjectiveMorphism_left hpb
    hR.isProjectiveMorphism_right hqb hD hDW
  set T := MMP.Mori.RationalMap.transformDivisor q.toRationalMap DW
  set NY : RDivisor Y := α • logCanonicalDivisor KY BY - T - CY with hNYdef
  have hnumY : IsNumericallyEquivalentOver k sY πY (α • logCanonicalDivisor KY BY) (CY + NY) := by
    have e : α • logCanonicalDivisor KY BY = (CY + NY) + T := by
      simp only [hNYdef]
      abel
    rw [e]
    exact isNumericallyEquivalentOver_add_of_isNumericallyTrivialOver
      (isCartierCombination_of_isQFactorial hY.isQFactorial _) hT
  -- the coefficients of `N_Y`
  have key : ∀ F : MMP.Mori.PrimeDivisor Y, ∃ FW : MMP.Mori.PrimeDivisor W,
      q FW.genericPoint = F.genericPoint ∧ IsIso (q.stalkMap FW.genericPoint) ∧
      NY.coeff F = (1 + α * t) * (Cw.coeff FW - CY.coeff F) + Nw.coeff FW ∧
      GX.coeff FW = KY.coeff F + BY.coeff F + t * CY.coeff F ∧
      (∀ D' : Divisor W, (MMP.Mori.RationalMap.transformDivisor q.toRationalMap D').coeff F =
        D'.coeff FW) := by
    intro F
    obtain ⟨FW, hFWeq, hFWiso, hFWtr⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hYn hWnq hqb F
    have hnexc := not_isExceptionalPrimeDivisor_of_map_genericPoint sY hdimY q FW F hFWeq
    have hGXY : GX.coeff FW = GY.coeff FW := by
      by_contra hne
      exact hnexc (hR.isExceptional FW (by
        rw [DivisorWithCoeffs.coeff_sub]; exact sub_ne_zero.mpr hne))
    have hGY : GY.coeff FW = (logCanonicalDivisor KY (BY + t • CY)).coeff F :=
      MMP.Fourfold.coeff_eq_of_isRCartierPullback FW F hFWeq hR.isRCartierPullback_right
    have hTF : T.coeff F = DW.coeff FW := hFWtr DW
    have hGX : GX.coeff FW = KY.coeff F + BY.coeff F + t * CY.coeff F := by
      rw [hGXY, hGY]
      simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
        Divisor.coeff_toRDivisor, smul_eq_mul]
      ring
    refine ⟨FW, hFWeq, hFWiso, ?_, hGX, hFWtr⟩
    have hNYF : NY.coeff F = α * (KY.coeff F + BY.coeff F) - T.coeff F - CY.coeff F := by
      simp only [hNYdef, logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
        DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
        smul_eq_mul]
    have hDWF : DW.coeff FW = α * GX.coeff FW - (1 + α * t) * Cw.coeff FW - Nw.coeff FW := by
      simp only [hDWdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    rw [hNYF, hTF, hDWF, hGX]
    ring
  -- the coefficients along a strict transform
  have hstrict : ∀ F : MMP.Mori.PrimeDivisor Y,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F → ∃ P : MMP.Mori.PrimeDivisor X,
      NY.coeff F = N.coeff P ∧ CY.coeff F = C.coeff P ∧ BY.coeff F = B.coeff P := by
    intro F hF
    obtain ⟨P, hP⟩ : ∃ P, MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F := by
      simpa [MMP.Flips.RationalMap.IsInverseExceptional] using hF
    obtain ⟨FW, hFWeq, _, hNYF, -, -⟩ := key F
    obtain ⟨hpFW, _⟩ := map_genericPoint_eq_of_transformPrimeDivisor_eq_some hXn hYn hWnp hpb
      hqb hR.isInverse hR.compHom_eq hP FW hFWeq
    have huniq : ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor φ P' = some F → P' = P :=
      fun P' hP' => by
        obtain ⟨h', -⟩ := map_genericPoint_eq_of_transformPrimeDivisor_eq_some hXn hYn hWnp hpb
          hqb hR.isInverse hR.compHom_eq hP' FW hFWeq
        exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h'.symm.trans hpFW)
    have htr : ∀ D' : RDivisor X,
        (MMP.Mori.RationalMap.transformDivisor φ D').coeff F = D'.coeff P := fun D' =>
      MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hP huniq D'
    refine ⟨P, ?_, htr C, by rw [hBY F, if_neg hF, htr B, add_zero]⟩
    rw [hNYF, MMP.Fourfold.coeff_eq_of_isRCartierPullback FW P hpFW hCw,
      MMP.Fourfold.coeff_eq_of_isRCartierPullback FW P hpFW hNw, htr C]
    ring
  -- the coefficients along a prime divisor exceptional over `X`
  have hexc : ∀ F : MMP.Mori.PrimeDivisor Y, MMP.Flips.RationalMap.IsInverseExceptional φ F →
      CY.coeff F = 0 ∧ BY.coeff F = 1 := fun F hF =>
    ⟨mapPrimeDivisors_apply_eq_zero_of_forall_ne hF C, by
      rw [hBY F, if_pos hF, show (MMP.Mori.RationalMap.transformDivisor φ B).coeff F = 0 from
        mapPrimeDivisors_apply_eq_zero_of_forall_ne hF B, zero_add]⟩
  have hpos : 0 < 1 + α * t := by positivity
  refine ⟨NY, fun F => ?_, fun F hF => ?_, hnumY, fun hBr hCr hNr ⟨a, ha⟩ => ⟨fun F => ?_,
    fun F => ?_, fun F => ?_⟩⟩
  · by_cases hF : MMP.Flips.RationalMap.IsInverseExceptional φ F
    · obtain ⟨FW, -, -, hNYF, -, -⟩ := key F
      rw [hNYF, (hexc F hF).1, sub_zero]
      exact add_nonneg (mul_nonneg hpos.le (hCw0 hC FW)) (hNw0 hN FW)
    · obtain ⟨P, h1, -, -⟩ := hstrict F hF
      exact h1 ▸ hN P
  · by_cases hF' : MMP.Flips.RationalMap.IsInverseExceptional φ F
    · rw [(hexc F hF').2]
    · obtain ⟨P, h1, -, h3⟩ := hstrict F hF'
      exact h3 ▸ hNB P (h1 ▸ hF)
  · by_cases hF : MMP.Flips.RationalMap.IsInverseExceptional φ F
    · exact ⟨1, by rw [(hexc F hF).2]; simp⟩
    · obtain ⟨P, -, -, h3⟩ := hstrict F hF
      exact h3 ▸ hBr P
  · by_cases hF : MMP.Flips.RationalMap.IsInverseExceptional φ F
    · exact ⟨0, by rw [(hexc F hF).1]; simp⟩
    · obtain ⟨P, -, h2, -⟩ := hstrict F hF
      exact h2 ▸ hCr P
  · by_cases hF : MMP.Flips.RationalMap.IsInverseExceptional φ F
    · obtain ⟨FW, -, -, hNYF, hGXF, htrq⟩ := key F
      obtain ⟨hCYF, hBYF⟩ := hexc F hF
      rw [hNYF, hCYF, sub_zero]
      obtain ⟨c, hc⟩ := hCwr hCr FW
      obtain ⟨n, hn⟩ := hNwr hNr FW
      rcases ht₁.lt_or_eq with ht1 | rfl
      · obtain ⟨n₀, hKX⟩ := hY.isCanonicalDivisor
        rw [coeff_eq_zero_of_isRealLcPair hR hlc hKX hCw (hCw0 hC) ht1 htrq
          (by rw [hGXF, hCYF, hBYF, mul_zero, add_zero]), hn]
        exact ⟨n, by push_cast; ring⟩
      · rw [hc, hn, ha]
        exact ⟨(1 + a * 1) * c + n, by push_cast; ring⟩
    · obtain ⟨P, h1, -, -⟩ := hstrict F hF
      exact h1 ▸ hNr P

end MMP.Fourfold
