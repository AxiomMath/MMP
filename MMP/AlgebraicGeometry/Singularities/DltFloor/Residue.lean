module

public import MMP.AlgebraicGeometry.Singularities.DltFloor.LocalAlgebra
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
public import MMP.AlgebraicGeometry.Singularities.DltDivisorialCohenMacaulay
public import MMP.AlgebraicGeometry.MMP.Fourfold.SdltAdjointPair
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
public import MMP.RingTheory.DiscreteValuationRing.Integrality
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
public import MMP.AlgebraicGeometry.Divisor.SmoothRDivisors
public import MMP.AlgebraicGeometry.Resolution.DivisorTupleRestrictionLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExteriorPowerEigenvalue
import MMP.AlgebraicGeometry.Variety.Subvariety
import MMP.AlgebraicGeometry.Singularities.DltStrataSncLocus
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentExistence

/-!
# Residues along the floor of a dlt pair

Let `(X, B)` be a dlt pair and `P` a prime component of `⌊B⌋`. This file collects the local
statements about Poincaré residues along `P` used to identify the adjoint sheaf of the floor:
the residue of a local generator of `𝒪_X(m(K_X + B))` can be lifted at each codimension-one point
of `P`, adjunction steps along the components of the floor are transported through open
restrictions, a component of the double locus of two floor components is a prime divisor of each,
and at a smooth point the residue of a logarithmic frame is the frame of the residue. It also
contains the combinatorics of the floor: its prime components have coefficient one, each is the
image of one adjunction step, and the disjoint union of the components is the normalization.

## Main results

* `MMP.Fourfold.SdltFloor.exists_primeDivisor_of_isAdjunctionStep`
* `MMP.Fourfold.SdltFloor.exists_isUnit_eq_smul_tprod`
* `MMP.Fourfold.SdltFloor.exists_isAdjunctionStep_of_mem_roundDown_support`
* `MMP.Fourfold.SdltFloor.exists_iso_normalizationScheme`

## References

* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Sections 4.1 and 5.1
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.SdltFloor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

section ResidueLift

/-- An element of the local ring at a prime divisor has nonnegative order. -/
private theorem ord_algebraMap_nonneg {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y]
    (P : MMP.Mori.PrimeDivisor Y) (a : Y.presheaf.stalk P.genericPoint) :
    0 ≤ Y.ord (algebraMap _ Y.functionField a) P.genericPoint := by
  by_cases ha : algebraMap _ Y.functionField a = 0
  · rw [ha, Scheme.ord_zero]; rfl
  have h := (P.divisorialValuation_le_one_iff _).mpr ⟨a, rfl⟩
  rw [P.divisorialValuation_eq_exp_neg_ord ha, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- A unit of the local ring at a prime divisor has order zero. -/
public theorem ord_algebraMap_eq_zero_of_isUnit {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (P : MMP.Mori.PrimeDivisor Y) {x : Y} (hx : x = P.genericPoint) {b : Y.presheaf.stalk x}
    (hb : IsUnit b) : Y.ord (algebraMap _ Y.functionField b) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hb

/-! ### Poincaré residues along a prime divisor -/

/-- **The residue lift at a codimension-one point.** For `Q` a prime divisor of `T`, there is a
`b` in the local ring along `P`, a unit there, such that `b τ` has no pole along any other prime
divisor through `j(η_Q)` and its residue `b̄ ρ` has no zero at `Q`. -/
private theorem exists_residue_lift
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (Q : MMP.Mori.PrimeDivisor T) :
    ∃ b : X.presheaf.stalk (j (componentGenericPoint T Q.component)), IsUnit b ∧
      (∀ E : MMP.Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ P →
        0 ≤ X.ord (algebraMap _ X.functionField b) E.genericPoint + E.ordForm τ) ∧
      T.ord ((MMP.Positivity.componentToFunctionField Q.component).hom
        ((j.stalkMap (componentGenericPoint T Q.component)).hom b)) Q.genericPoint +
        Q.ordForm ρ ≤ 0 := by
  classical
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg k X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg k T.functionField).toNat = n := by
    have := trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  -- the top forms on `X` and on `T` are lines
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sX) (d := n + 1) (by rw [hdim]; norm_cast)
  have hrank : Module.finrank X.functionField (RationalPluriForms sX (n + 1) 1) = 1 := by
    let bb : Module.Basis Unit X.functionField (RationalPluriForms sX (n + 1) 1) :=
      ZTensorPower.basis b₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  have hrankT : Module.finrank T.functionField (RationalPluriForms (j ≫ sX) n 1) = 1 := by
    have := essFiniteType_functionField (sX := j ≫ sX)
    have hK : Module.finrank T.functionField Ω[T.functionField⁄k] = n :=
      (finrank_kaehlerDifferential_eq_trdeg k T.functionField).trans hdT
    have : FiniteDimensional T.functionField Ω[T.functionField⁄k] :=
      (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k T.functionField).1
    have h1 : Module.finrank T.functionField (⋀[T.functionField]^n Ω[T.functionField⁄k]) = 1 := by
      rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
    let c₀ := (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique (Fin 1) Unit)
    let bb : Module.Basis Unit T.functionField (RationalPluriForms (j ≫ sX) n 1) :=
      ZTensorPower.basis c₀ 1
    rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]
  -- a local generator `ρ₁` of `ω_{T,Q}`
  have : Nontrivial (RationalPluriForms (j ≫ sX) n 1) :=
    Module.nontrivial_of_finrank_pos (R := T.functionField) (by omega)
  obtain ⟨ρ₀, hρ₀⟩ := exists_ne (0 : RationalPluriForms (j ≫ sX) n 1)
  obtain ⟨g, hg0, hg⟩ := MMP.CyclicChartDifferent.Aux.exists_ord_eq Q (-Q.ordForm ρ₀)
  set ρ₁ := g • ρ₀ with hρ₁def
  have hρ₁0 : ρ₁ ≠ 0 := smul_ne_zero hg0 hρ₀
  have hρ₁Q : Q.ordForm ρ₁ = 0 := by
    rw [hρ₁def, Q.ordForm_smul (sX := j ≫ sX) hdT hg0 hρ₀, hg]
    ring
  -- its lift `σ = f τ`
  obtain ⟨σ, hσP, hσE, hσres⟩ :=
    exists_isPoincareResidue_of_le_ordForm_of_charZero sX hX hdim j hT P hP Q ρ₁ hρ₁Q.ge
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' τ hτ0).mp hrank σ
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  -- `f` is regular along `P`
  obtain ⟨a, haf⟩ : ∃ a : X.presheaf.stalk P.genericPoint,
      algebraMap _ X.functionField a = f := by
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [map_zero, hf0]⟩
    refine MMP.Fourfold.exists_algebraMap_eq_of_ord_nonneg P hf0 ?_
    have := P.ordForm_smul (sX := sX) hd hf0 hτ0
    rw [hf, hτ] at this
    omega
  set b₁ := X.presheaf.stalkSpecializes hspP a with hb₁
  have hb₁f : algebraMap _ X.functionField b₁ = f := by
    rw [hb₁, MMP.Fourfold.algebraMap_stalkSpecializes', haf]
  -- the residue of `σ` is `b̄₁ ρ`
  have hres := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ b₁
  rw [hb₁f, hf] at hres
  have hρσeq := IsPoincareResidue.unique_of_isClosedImmersion (sY := sX) P hjT hσres hres
  obtain ⟨hb0, hρ0⟩ := smul_ne_zero_iff.mp (hρσeq ▸ hρ₁0 :
    (j.stalkMap (genericPoint T)).hom b₁ • ρ ≠ 0)
  have hb₁u : IsUnit b₁ :=
    isUnit_of_map_unit (j.stalkMap (genericPoint T)).hom b₁
      ((isUnit_iff_ne_zero (G₀ := T.functionField)).mpr hb0)
  have hf0 : f ≠ 0 := by
    rw [← hb₁f]; exact (hb₁u.map _).ne_zero
  -- the stalk at the component generic point
  have hcg := MMP.Fourfold.componentGenericPoint_eq_genericPoint Q.component
  have h' : componentGenericPoint T Q.component ⤳ genericPoint T := specializes_of_eq hcg
  refine ⟨X.presheaf.stalkSpecializes (j.base.hom.map_specializes h') b₁, hb₁u.map _,
    fun E hE hEP => ?_, ?_⟩
  · rw [MMP.Fourfold.algebraMap_stalkSpecializes', hb₁f, ← E.ordForm_smul (sX := sX) hd hf0 hτ0, hf]
    exact hσE E hE hEP
  · rw [Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h',
      MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes T _ h',
      MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint T]
    have := Q.ordForm_smul (sX := j ≫ sX) hdT hb0 hρ0
    rw [← hρσeq, hρ₁Q] at this
    rw [← this]

end ResidueLift

section Step

/-! ### Pull-backs and dimensions -/

/-- The pull-back predicate depends only on the divisors, not on the proof of `(∗)`. -/
public theorem isPullback_congr {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D D' : QDivisor Y}
    {hD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp} {R R' : QDivisor X}
    (h : D.IsPullback f hD R) (e : D = D') (e' : R = R') : D'.IsPullback f (e ▸ hD) R' := by
  subst e e'
  exact h

/-- A scheme carrying a prime divisor, locally of finite type over a field, has dimension at least
one: a prime divisor of an `n`-dimensional variety has dimension `n - 1`. -/
public theorem exists_eq_add_one_of_primeDivisor {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {N : ℕ}
    (hN : topologicalKrullDim X = N) (P : MMP.Mori.PrimeDivisor X) : ∃ n, N = n + 1 := by
  have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX P.genericPoint
  rw [P.coheight_genericPoint, hN] at hPP
  rcases N with _ | n
  · exfalso
    revert hPP
    generalize topologicalKrullDim (closure {P.genericPoint} : Set X) = e
    induction e using WithBot.recBotCoe with
    | bot => simp
    | coe m =>
      induction m using ENat.recTopCoe with
      | top => norm_cast
      | coe m => norm_cast
  · exact ⟨n, rfl⟩

end Step

section Step2

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y}

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
public theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (MMP.Mori.isIso_ι_restrict_self U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

/-- The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
image. -/
public theorem ker_eq_vanishingIdeal {A B : Scheme.{0}} (g : A ⟶ B) [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range g.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  simp only [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- A closed immersion from a reduced scheme onto a prime divisor `P` has kernel the ideal
of `P`. -/
public theorem ker_eq_idealSheaf {T Y : Scheme.{0}} [IsLocallyNoetherian Y] (j : T ⟶ Y)
    [IsClosedImmersion j] [IsReduced T] (P : MMP.Mori.PrimeDivisor Y)
    (hP : Set.range j.base = (P.support : Set Y)) : j.ker = P.idealSheaf := by
  rw [ker_eq_vanishingIdeal, ← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure, hP]
  exact P.idealSheaf.support.isClosed.closure_eq

/-- **Local coordinates on a hypersurface adapted to a restricted boundary**, pointwise. Let
`ι : S ⟶ W` be a closed immersion and `y ∈ S` such that, at `ι y`, a regular system of
parameters `z` has `ker ι = (z_{i₀})` and the ideals `E_i` through `ι y` are `(z_{c(i)})` with
`c` injective and avoiding `i₀`. Then at `y` the ideals `ι⁻¹E_i` through `y` are distinct
members of a regular system of parameters of `𝒪_{S,y}`. -/
private theorem exists_coordinates_comap_of_stalk {S W : Scheme.{0}} [IsLocallyNoetherian W]
    (ι : S ⟶ W) [IsClosedImmersion ι] {Λ : Type*} (E : Λ → W.IdealSheafData) (y : S) {n : ℕ}
    {z : Fin n → W.presheaf.stalk (ι y)} (hz : IsRegularSystemOfParameters z) (i₀ : Fin n)
    (hker : IdealSheafData.stalk ι.ker (ι y) = Ideal.span {z i₀})
    (c : {i // ι y ∈ (E i).support} → Fin n) (hc : Function.Injective c)
    (hc0 : ∀ i, c i ≠ i₀) (hE : ∀ i, IdealSheafData.stalk (E i.1) (ι y) = Ideal.span {z (c i)}) :
    ∃ (m : ℕ) (w : Fin m → S.presheaf.stalk y)
      (c' : {i // y ∈ ((E i).comap ι).support} → Fin m),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((E i.1).comap ι) y = Ideal.span {w (c' i)}) ∧
        Function.Injective c' := by
  classical
  set J : Finset (Fin n) := {i₀} with hJdef
  have hZx : IdealSheafData.stalk ι.ker (ι y) = Ideal.span (z '' (J : Set (Fin n))) := by
    rwa [hJdef, Finset.coe_singleton, Set.image_singleton]
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hq⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  let e : (W.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J : Set (Fin n)))) ≃+*
      S.presheaf.stalk y :=
    (Ideal.quotEquivOfEq (hZx.symm.trans
      (MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker ι y).symm)).trans
      (RingHom.quotientKerEquivOfSurjective (ι.stalkMap_surjective y))
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = (ι.stalkMap y).hom a := fun a => rfl
  have hmem : ∀ i : {i // y ∈ ((E i).comap ι).support}, ι y ∈ (E i.1).support :=
    fun i => (MMP.Resolution.mem_support_comap_iff _ _ y).1 i.2
  have hnot : ∀ i : {i // y ∈ ((E i).comap ι).support}, c ⟨i.1, hmem i⟩ ∈ Jᶜ := by
    intro i
    rw [Finset.mem_compl, hJdef, Finset.mem_singleton]
    exact hc0 _
  let o := Jᶜ.orderIsoOfFin rfl
  refine ⟨Jᶜ.card, fun j => e (Ideal.Quotient.mk _ (z (Jᶜ.orderEmbOfFin rfl j))),
    fun i => o.symm ⟨c ⟨i.1, hmem i⟩, hnot i⟩, hq.map_ringEquiv e, fun i => ?_, ?_⟩
  · dsimp only
    rw [IdealSheafData.stalk_comap, hE ⟨i.1, hmem i⟩, Ideal.map_span,
      Set.image_singleton, he, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · exact fun i j hij => Subtype.ext
      (Subtype.mk.inj (hc (congrArg Subtype.val (o.symm.injective hij))))

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private lemma eq_of_le_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hq]; simp))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

/-- **A lower bound for the different along a second boundary component.** In the setting of the
effectivity of the different, let `Q` be a prime divisor of `T` and `Γ ≠ P` a prime divisor with
`coeff_Γ B ≥ 1` cut out near `x = j(η_Q)` by `t ∈ 𝒪_{X,x}` (order one along `Γ`, a unit along
every other prime divisor through `x`), whose restriction to `T` vanishes along `Q`. Then
`coeff_Q (D|_T - div ρ) ≥ 1`: the regular function `b^m φ / t^m` restricts to `T`. -/
private theorem one_le_coeff_isPullback_sub_divisorOfForm
    {k : Type} [Field k] [CharZero k] {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety k sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety k (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (B : QDivisor X) (hB : B.IsEffective) (hBP : B.coeff P = 0)
    (τ : RationalPluriForms sX (n + 1) 1) (hτ0 : τ ≠ 0) (hτ : P.ordForm τ = -1)
    (ρ : RationalPluriForms (j ≫ sX) n 1) (hρ : IsPoincareResidue sX j n 1 τ ρ)
    (hD : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsQCartier)
    (hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).supp)
    (R₀ : QDivisor T)
    (hR₀ : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B).IsPullback j hgen R₀)
    (Q : MMP.Mori.PrimeDivisor T) (Γ : MMP.Mori.PrimeDivisor X) (hΓP : Γ ≠ P)
    (hΓ : 1 ≤ B.coeff Γ) (t : X.presheaf.stalk (j Q.genericPoint))
    (ht0 : algebraMap _ X.functionField t ≠ 0)
    (htΓ : X.ord (algebraMap _ X.functionField t) Γ.genericPoint = 1)
    (htE : ∀ E : MMP.Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support → E ≠ Γ →
      X.ord (algebraMap _ X.functionField t) E.genericPoint = 0)
    (htQ : 1 ≤ T.ord (algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom t))
      Q.genericPoint) :
    1 + Q.ordForm ρ ≤ R₀.coeff Q := by
  classical
  obtain ⟨m, hm, Dm, hDm, hDmc⟩ := hD.exists_pos
  obtain ⟨Dm', hDm', hp⟩ := hR₀ m hm Dm hDm hDmc
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hR₀Q : ((Dm'.coeff Q : ℤ) : ℚ) = (m : ℚ) * R₀.coeff Q := by
    have := congrArg (fun G : QDivisor T => G.coeff Q) hDm'
    simpa [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor] using this
  -- a local equation of `m D` near `x = j(η_Q)`
  set η := componentGenericPoint T Q.component with hηdef
  have hηQ : η ⤳ Q.genericPoint := Q.specializes_genericPoint
  have hsp : j η ⤳ j Q.genericPoint := j.base.hom.map_specializes hηQ
  obtain ⟨U, hxU, φ, hφ⟩ := hDmc (j Q.genericPoint)
  have hQU : (Q.support ∩ j ⁻¹ᵁ U).Nonempty := (Q.genericPoint_mem_iff _).mp hxU
  have hjηU : j η ∈ U := hsp.mem_open U.isOpen hxU
  have hm' : ((m : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hgenm : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ Dm.supp :=
    fun Z hZ => hgen Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq hm' hDm] at hZ)
  rw [hp U φ hφ Q hQU] at hR₀Q
  set W := pointComponent (j η) with hWdef
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hjηU (hgenm Q.component) (mem_pointComponent _)
  rw [pullbackComponent_eq _ hφ _ (mem_pointComponent _) a ha,
    MMP.CyclicChartDifferent.Aux.ordUnit_eq_ord] at hR₀Q
  obtain ⟨b, hb, hbE, hbQ⟩ := exists_residue_lift sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
  have hmemZ : ∀ Z : irreducibleComponents X, j η ∈ Z.1 := fun Z => by
    rw [(MMP.Fourfold.subsingleton_irreducibleComponents (X := X)).elim Z W]
    exact mem_pointComponent _
  let Gu : (RationalFunctions X)ˣ := (RationalFunctions.unitsEquiv X).symm fun Z =>
    Units.map (stalkToRationalFunctions X (hmemZ Z)).hom.toMonoidHom hb.unit
  have hGW : ((Gu : RationalFunctions X) W) =
      (stalkToRationalFunctions X (mem_pointComponent (j η))).hom b := rfl
  have hGord : ∀ E : MMP.Mori.PrimeDivisor X,
      E.ord Gu = X.ord (algebraMap _ X.functionField b) E.genericPoint := by
    intro E
    rw [MMP.Positivity.ord_eq_ord_componentToFunctionField]
    change X.ord ((MMP.Positivity.componentToFunctionField E.component).hom
      ((stalkToRationalFunctions X (hmemZ E.component)).hom b)) _ = _
    rw [MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkToRationalFunctions]
  -- the unit `Tu` of `K(X)` given by `t`
  obtain ⟨Tu, hTu⟩ := MMP.Fourfold.exists_units_componentToFunctionField_eq ht0
  have hTord : ∀ E : MMP.Mori.PrimeDivisor X,
      E.ord Tu = X.ord (algebraMap _ X.functionField t) E.genericPoint := by
    intro E
    rw [MMP.Positivity.ord_eq_ord_componentToFunctionField, hTu]
  have hxW : j Q.genericPoint ∈ W.1 :=
    hsp.mem_closed (isClosed_of_mem_irreducibleComponents _ W.2) (mem_pointComponent _)
  -- `b^m φ / t^m` is regular at `x`
  have hψ : ∀ E : MMP.Mori.PrimeDivisor X, j Q.genericPoint ∈ E.support →
      0 ≤ E.ord (Gu ^ m * φ * Tu⁻¹ ^ m) := by
    intro E hE
    rw [PrimeDivisor.ord_mul, PrimeDivisor.ord_mul, PrimeDivisor.ord_pow, PrimeDivisor.ord_pow,
      PrimeDivisor.ord_inv, hGord, hTord, ← hφ E ⟨_, hE, hxU⟩]
    have hc := congrArg (fun G : QDivisor X => G.coeff E) hDm
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      coeff_divisorOfForm, zsmul_eq_mul] at hc
    have hBE := hB E
    by_cases hEP : E = P
    · subst hEP
      have h0 : X.ord (algebraMap _ X.functionField b) E.genericPoint = 0 :=
        ord_algebraMap_eq_zero_of_isUnit E (by
          rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
          exact MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j E hP) hb
      have ht : X.ord (algebraMap _ X.functionField t) E.genericPoint = 0 :=
        htE E hE (Ne.symm hΓP)
      rw [h0, ht, hτ, DivisorWithCoeffs.coeff_single_self, hBP] at *
      have : (Dm.coeff E : ℚ) = 0 := by rw [hc]; push_cast; ring
      have : Dm.coeff E = 0 := by exact_mod_cast this
      rw [this]; simp
    · have h1 := hbE E hE hEP
      rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hEP)] at hc
      have hb1 : (0 : ℚ) ≤
          (X.ord (algebraMap _ X.functionField b) E.genericPoint : ℚ) + E.ordForm τ := by
        exact_mod_cast h1
      have key : (0 : ℚ) ≤ (m : ℚ) * X.ord (algebraMap _ X.functionField b) E.genericPoint +
          Dm.coeff E - m * X.ord (algebraMap _ X.functionField t) E.genericPoint := by
        rw [hc]
        by_cases hEΓ : E = Γ
        · subst hEΓ
          rw [htΓ]
          have : (1 : ℚ) ≤ B.coeff E := hΓ
          push_cast
          nlinarith
        · rw [htE E hE hEΓ]
          have : (0 : ℚ) ≤ B.coeff E := hBE
          push_cast
          nlinarith
      rw [nsmul_eq_mul, nsmul_eq_mul, mul_neg]
      have : (0 : ℤ) ≤ (m : ℤ) * X.ord (algebraMap _ X.functionField b) E.genericPoint +
          Dm.coeff E - m * X.ord (algebraMap _ X.functionField t) E.genericPoint := by
        exact_mod_cast key
      push_cast
      linarith
  obtain ⟨c, hc⟩ := exists_stalk_eq_of_forall_zero_le_ord hxW (Gu ^ m * φ * Tu⁻¹ ^ m) hψ
  -- the germ relation `c t^m = b^m a` at the generic point of `P`
  have hcompF : ∀ s : X.presheaf.stalk (j Q.genericPoint),
      (stalkToRationalFunctions X (mem_pointComponent (j η))).hom
        (X.presheaf.stalkSpecializes hsp s) = (stalkToRationalFunctions X hxW).hom s := by
    intro s
    change (X.presheaf.stalkSpecializes hsp ≫ X.presheaf.stalkSpecializes _).hom s = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hTW : (Tu : RationalFunctions X) W = (stalkToRationalFunctions X hxW).hom t := by
    letI := (RationalFunctions.isField_stalk X W).toField
    apply RingHom.injective (MMP.Positivity.componentToFunctionField W).hom
    rw [hTu, MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkToRationalFunctions]
  have hunits : Gu ^ m * φ * Tu⁻¹ ^ m * Tu ^ m = Gu ^ m * φ := by
    rw [mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]
  have hspc : X.presheaf.stalkSpecializes hsp c * (X.presheaf.stalkSpecializes hsp t) ^ m =
      b ^ m * a.val := by
    apply stalkToRationalFunctions_injective (mem_pointComponent (j η))
    rw [map_mul, map_pow, map_mul, map_pow, ← hGW, ha, hcompF, hcompF, hc, ← hTW]
    have := congrArg (fun u : (RationalFunctions X)ˣ => (u : RationalFunctions X) W) hunits
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply, Pi.pow_apply] at this
    simpa [Units.val_mul, Units.val_pow_eq_pow_val, Pi.mul_apply, Pi.pow_apply] using this
  -- restriction to `T`
  set ψT := (MMP.Positivity.componentToFunctionField Q.component).hom
  have hres : ∀ s : X.presheaf.stalk (j Q.genericPoint),
      ψT ((j.stalkMap η).hom (X.presheaf.stalkSpecializes hsp s)) =
        algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom s) := by
    intro s
    rw [Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hηQ s,
      MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes T Q.component hηQ]
  have heq := congrArg (fun r => ψT ((j.stalkMap η).hom r)) hspc
  simp only [map_mul, map_pow, hres] at heq
  have hb0 : ψT ((j.stalkMap η).hom b) ≠ 0 := ((hb.map _).map _).ne_zero
  have ha0 : ψT ((j.stalkMap η).hom a.val) ≠ 0 := ((a.isUnit.map _).map _).ne_zero
  have ht0' : algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom t) ≠ 0 := by
    intro h0
    rw [h0] at htQ
    simp at htQ
  have hc0 : algebraMap _ T.functionField ((j.stalkMap Q.genericPoint).hom c) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at heq
    exact mul_ne_zero (pow_ne_zero _ hb0) ha0 heq.symm
  have hord := congrArg (fun r => T.ord r Q.genericPoint) heq
  rw [Scheme.ord_mul hc0 (pow_ne_zero _ ht0'), MMP.Fourfold.ord_pow' ht0',
    Scheme.ord_mul (pow_ne_zero _ hb0) ha0, MMP.Fourfold.ord_pow' hb0] at hord
  have key := ord_algebraMap_nonneg Q ((j.stalkMap Q.genericPoint).hom c)
  rw [Units.coe_map] at hR₀Q
  change ((T.ord (ψT ((j.stalkMap η).hom a.val)) Q.genericPoint : ℤ) : ℚ) = _ at hR₀Q
  have hmb : (m : ℤ) * (T.ord (ψT ((j.stalkMap η).hom b)) Q.genericPoint + Q.ordForm ρ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hbQ
  have hmt : (m : ℤ) * 1 ≤ (m : ℤ) * T.ord (algebraMap _ T.functionField
      ((j.stalkMap Q.genericPoint).hom t)) Q.genericPoint :=
    mul_le_mul_of_nonneg_left htQ (by positivity)
  refine le_of_mul_le_mul_left ?_ hmQ
  rw [← hR₀Q]
  have : (m : ℤ) * (1 + Q.ordForm ρ) ≤ T.ord (ψT ((j.stalkMap η).hom a.val)) Q.genericPoint := by
    rw [mul_add] at hmb ⊢
    rw [mul_one] at hmt ⊢
    linarith
  exact_mod_cast this

open Classical in
/-- **The orders of a local equation of a prime divisor.** If `Γ ∋ y` is cut out at `y` by a
member `t` of a regular system of parameters of `𝒪_{Y,y}`, then `t` has order one along `Γ` and
order zero along every other prime divisor through `y`. -/
public theorem ord_algebraMap_eq_ite_of_stalk_eq_span {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {y : Y} {n : ℕ} {z : Fin n → Y.presheaf.stalk y}
    (hz : IsRegularSystemOfParameters z) (i : Fin n) (Γ : MMP.Mori.PrimeDivisor Y)
    (hΓy : y ∈ Γ.support) (hΓ : IdealSheafData.stalk Γ.idealSheaf y = Ideal.span {z i})
    (E : MMP.Mori.PrimeDivisor Y) (hE : y ∈ E.support) :
    Y.ord (algebraMap _ Y.functionField (z i)) E.genericPoint = if E = Γ then 1 else 0 := by
  classical
  have hsp : E.genericPoint ⤳ y := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hE
  set tE := Y.presheaf.stalkSpecializes hsp (z i) with htE
  have halg : algebraMap _ Y.functionField tE = algebraMap _ Y.functionField (z i) :=
    MMP.Fourfold.algebraMap_stalkSpecializes' Y hsp _
  have hmax : IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint) =
      Ideal.map (Y.presheaf.stalkSpecializes hsp).hom (IdealSheafData.stalk E.idealSheaf y) := by
    rw [← MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes,
      MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hz0 : z i ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz i
  split_ifs with hEΓ
  · subst hEΓ
    rw [hΓ, Ideal.map_span, Set.image_singleton] at hmax
    haveI : IsDiscreteValuationRing (Y.presheaf.stalk E.genericPoint) :=
      E.isDiscreteValuationRing_localRing
    have htE0 : tE ≠ 0 := by
      intro h0
      have : algebraMap _ Y.functionField (z i) = 0 := by rw [← halg, h0, map_zero]
      exact hz0 (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
        (this.trans (map_zero _).symm))
    rw [← halg]
    exact MMP.Fourfold.ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint
      (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal tE htE0 hmax)
  · have hnot : z i ∉ MMP.Intersection.primeOfSpecializes hsp := by
      intro hmem
      obtain ⟨q, hqE, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hE
      obtain ⟨qΓ, -, hqΓ, hqΓh⟩ :=
        MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Γ hΓy
      have hpq : MMP.Intersection.primeOfSpecializes hsp = q.asIdeal := by
        have hsp' : Y.fromSpecStalk y q ⤳ y := hqE ▸ hsp
        rw [MMP.Resolution.primeOfSpecializes_congr hqE.symm hsp hsp']
        exact MMP.Resolution.primeOfSpecializes_fromSpecStalk y q hsp'
      have hle : IdealSheafData.stalk Γ.idealSheaf y ≤ q.asIdeal := by
        rw [hΓ, Ideal.span_le, Set.singleton_subset_iff, ← hpq]; exact hmem
      haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
      haveI : (IdealSheafData.stalk Γ.idealSheaf y).IsPrime := by rw [hqΓ]; exact qΓ.2
      have heq : IdealSheafData.stalk Γ.idealSheaf y = q.asIdeal := by
        refine eq_of_le_of_height_eq_one ?_ hle hqh
        rw [hΓ, Ne, Ideal.span_singleton_eq_bot]; exact hz0
      exact hEΓ (MMP.Intersection.eq_of_stalk_idealSheaf_eq hE hΓy (hq.trans heq.symm))
    have hu : IsUnit tE := by
      by_contra hnu
      exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    rw [← halg]
    exact ord_algebraMap_eq_zero_of_isUnit E rfl hu

/-- A member of a regular system of parameters of `𝒪_{Y,y}` cuts out a prime divisor through
`y`: the closure of the generization of `y` at the prime it generates. -/
private theorem exists_primeDivisor_stalk_eq_span {Y : Scheme.{0}} {y : Y}
    [IsRegularLocalRing (Y.presheaf.stalk y)] {n : ℕ} {z : Fin n → Y.presheaf.stalk y}
    (hz : IsRegularSystemOfParameters z) (m : Fin n) :
    ∃ E : MMP.Mori.PrimeDivisor Y, y ∈ E.support ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {z m} := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  have hP := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz m
  set q : PrimeSpectrum (Y.presheaf.stalk y) := ⟨Ideal.span {z m}, hP⟩
  have hz0 : z m ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz m
  have hzu : ¬ IsUnit (z m) := fun hu => hP.ne_top (Ideal.span_singleton_eq_top.2 hu)
  have h1 : Order.coheight (Y.fromSpecStalk y q) = 1 := by
    refine (Stacks.Chow.coheight_fromSpecStalk_eq_height (W := Y) y q).trans ?_
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0) hzu
  set E := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1
  have hsupp : (E.support : Set Y) = closure {Y.fromSpecStalk y q} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  refine ⟨E, ?_, ?_⟩
  · rw [hsupp]
    exact specializes_iff_mem_closure.1 (MMP.Resolution.specializes_fromSpecStalk y q)
  · have hcl : E.idealSheaf.support = TopologicalSpace.Closeds.closure {Y.fromSpecStalk y q} :=
      TopologicalSpace.Closeds.ext (by rw [TopologicalSpace.Closeds.coe_closure]; exact hsupp)
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf E, hcl]
    exact Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y q

/-- **The reduced different meets the other floor components.** For one adjunction step from a
dlt pair onto `P` and a second prime component `Q` of `⌊B_Y⌋`, every irreducible subset of
`j⁻¹(Q)` lies in a prime divisor `Q'` of `T` with `Q' ⊆ j⁻¹(Q)` and coefficient one in `B_T`. -/
public theorem exists_primeDivisor_of_isAdjunctionStep (hB : MMP.Intersection.IsDltPair sY BY)
    {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {P : MMP.Mori.PrimeDivisor Y} (hP : Set.range j.base = (P.support : Set Y))
    {Q : MMP.Mori.PrimeDivisor Y} (hQP : Q ≠ P) (hQ : 1 ≤ BY.coeff Q)
    {W : Set T} (hW : IsIrreducible W) (hWQ : W ⊆ j.base ⁻¹' (Q.support : Set Y)) :
    ∃ Q' : MMP.Mori.PrimeDivisor T, W ⊆ (Q'.support : Set T) ∧
      (Q'.support : Set T) ⊆ j.base ⁻¹' (Q.support : Set Y) ∧ 1 ≤ BT.coeff Q' := by
  classical
  obtain ⟨⟨hpair, hB0, -⟩, hB1, Z, -, hsnc, hpos⟩ := id hB
  obtain ⟨hTv, P', hP'1, hP', hci, -⟩ := id h
  have hPP : P' = P := by
    have hmem : P.genericPoint ∈ (P'.support : Set Y) := by
      rw [← hP', hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    exact MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem
  subst hPP
  rw [inverseTransformDivisor_ι_eq_restrictOpen] at hsnc
  have hXv : IsNormalVariety k sY := hpair.1
  haveI : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  haveI : CompactSpace Y := haveI := hXv.1; QuasiCompact.compactSpace_of_compactSpace sY
  haveI : LocallyOfFiniteType (j ≫ sY) := hTv.1.toLocallyOfFiniteType
  haveI : CompactSpace T := haveI := hTv.1; QuasiCompact.compactSpace_of_compactSpace (j ≫ sY)
  set U : Y.Opens := Z.compl
  -- a stratum point `c ∈ U` above `W`
  have hWim : IsIrreducible (j.base '' W) := hW.image _ j.base.hom.continuous.continuousOn
  have hWPQ : j.base '' W ⊆ (P'.support : Set Y) ∩ Q.support := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hP ▸ ⟨w, rfl⟩, hWQ hw⟩
  obtain ⟨c, hcZ, hWc, hcPQ⟩ :=
    exists_notMem_closure_of_isDltPair hB hpos (Ne.symm hQP) hP'1 hQ hWim hWPQ
  have hcU : c ∈ U := hcZ
  have hcP : c ∈ Set.range j.base := hP ▸ (hcPQ (subset_closure rfl)).1
  obtain ⟨x, rfl⟩ := hcP
  -- coordinates on `T` at `x`
  obtain ⟨N, z, jjY, hz, hjY, hIY⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι BY ⟨_, hcU⟩).mp
      (hsnc.2 ⟨_, hcU⟩)
  have hsupp : ∀ G : MMP.Mori.PrimeDivisor Y, 1 ≤ BY.coeff G → G ∈ BY.support := fun G hG => by
    rw [Finsupp.mem_support_iff]
    exact (lt_of_lt_of_le one_pos hG).ne'
  have hPs := hsupp P' hP'1
  have hQs := hsupp Q hQ
  have hyP : j x ∈ P'.support := hP ▸ ⟨x, rfl⟩
  have hyQ : j x ∈ Q.support := (hcPQ (subset_closure rfl)).2
  set i₀ := jjY ⟨P', hPs, hyP⟩
  have hker : IdealSheafData.stalk j.ker (j x) = Ideal.span {z i₀} := by
    rw [ker_eq_idealSheaf j P' hP]
    exact hIY ⟨P', hPs, hyP⟩
  let E : {Γ : MMP.Mori.PrimeDivisor Y // Γ ∈ BY.support ∧ Γ ≠ P'} → Y.IdealSheafData :=
    fun Γ => Γ.1.idealSheaf
  let cc : {Γ // j x ∈ (E Γ).support} → Fin N := fun Γ => jjY ⟨Γ.1.1, Γ.1.2.1, Γ.2⟩
  have hc : Function.Injective cc := fun a b hab =>
    Subtype.ext (Subtype.ext (Subtype.mk.inj (hjY hab)))
  have hc0 : ∀ Γ, cc Γ ≠ i₀ := fun Γ hΓ => Γ.1.2.2 (Subtype.mk.inj (hjY hΓ))
  obtain ⟨m, w, c', hw, hc', -⟩ := exists_coordinates_comap_of_stalk j E x hz i₀ hker cc hc hc0
    (fun Γ => hIY ⟨Γ.1.1, Γ.1.2.1, Γ.2⟩)
  set QL : {Γ : MMP.Mori.PrimeDivisor Y // Γ ∈ BY.support ∧ Γ ≠ P'} := ⟨Q, hQs, hQP⟩
  have hxQ : x ∈ ((E QL).comap j).support := (MMP.Resolution.mem_support_comap_iff _ _ x).2 hyQ
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hw
  obtain ⟨Q', hxQ', hQ'st⟩ := exists_primeDivisor_stalk_eq_span hw (c' ⟨QL, hxQ⟩)
  have hst : IdealSheafData.stalk Q'.idealSheaf x = IdealSheafData.stalk (Q.idealSheaf.comap j) x :=
    hQ'st.trans (hc' ⟨QL, hxQ⟩).symm
  have hspx : Q'.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hxQ'
  have hgpQ : Q'.genericPoint ∈ (Q.idealSheaf.comap j).support := by
    rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hspx, ← hst,
      ← MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hspx]
    change Q'.genericPoint ∈ (Q'.support : Set T)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hQ'sub : (Q'.support : Set T) ⊆ j.base ⁻¹' (Q.support : Set Y) := by
    intro t ht
    have hsp : Q'.genericPoint ⤳ t := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact ht
    exact (MMP.Resolution.mem_support_comap_iff _ _ t).1
      (hsp.mem_closed (Q.idealSheaf.comap j).support.isClosed hgpQ)
  have hWQ' : W ⊆ (Q'.support : Set T) := by
    intro w hw
    have h1 : j x ⤳ j w := specializes_iff_mem_closure.mpr (hWc ⟨w, hw, rfl⟩)
    have h2 : x ⤳ w := (j.isClosedEmbedding.isInducing.specializes_iff).mp h1
    exact h2.mem_closed Q'.idealSheaf.support.isClosed hxQ'
  refine ⟨Q', hWQ', hQ'sub, ?_⟩
  -- a local equation `t` of `Q` at `y' = j(η_{Q'})`
  have hy'U : j Q'.genericPoint ∈ U := (hspx.map j.base.hom.continuous).mem_open U.isOpen hcU
  have hgpmem : Q'.genericPoint ∈ (Q'.support : Set T) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hy'Q : j Q'.genericPoint ∈ Q.support := hQ'sub hgpmem
  have hy'P : j Q'.genericPoint ∈ P'.support := by rw [← hP]; exact ⟨_, rfl⟩
  obtain ⟨N2, z2, jj2, hz2, -, hI2⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι BY ⟨_, hy'U⟩).mp
      (hsnc.2 ⟨_, hy'U⟩)
  let z2' : Fin N2 → Y.presheaf.stalk (j Q'.genericPoint) := z2
  have hz2' : IsRegularSystemOfParameters z2' := hz2
  set t : Y.presheaf.stalk (j Q'.genericPoint) := z2' (jj2 ⟨Q, hQs, hy'Q⟩) with htdef
  have htQ : IdealSheafData.stalk Q.idealSheaf (j Q'.genericPoint) = Ideal.span {t} :=
    hI2 ⟨Q, hQs, hy'Q⟩
  have hord : ∀ G : MMP.Mori.PrimeDivisor Y, j Q'.genericPoint ∈ G.support →
      Y.ord (algebraMap _ Y.functionField t) G.genericPoint = if G = Q then 1 else 0 :=
    fun G hG => ord_algebraMap_eq_ite_of_stalk_eq_span hz2' _ Q hy'Q htQ G hG
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz2'
  have ht0' : t ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz2' _
  have ht0 : algebraMap _ Y.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ht0'
  -- `t|_T` vanishes along `Q'` and is nonzero
  set tb := (j.stalkMap Q'.genericPoint).hom t with htb
  have htb_mem : tb ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk Q'.genericPoint) := by
    have h1 : tb ∈ IdealSheafData.stalk (Q.idealSheaf.comap j) Q'.genericPoint := by
      rw [IdealSheafData.stalk_comap, htQ]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self t)
    exact (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support _ _).mpr hgpQ h1
  have htb0 : tb ≠ 0 := by
    intro h0
    have hmem : t ∈ RingHom.ker (j.stalkMap Q'.genericPoint).hom := h0
    rw [MMP.Resolution.Internal.TupleRestrictionLift.ker_stalkMap_eq_stalk_ker,
      ker_eq_idealSheaf j P' hP] at hmem
    obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P' hy'P
    obtain ⟨qQ, -, hqQ, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Q hy'Q
    haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk (j Q'.genericPoint))
    haveI : (IdealSheafData.stalk Q.idealSheaf (j Q'.genericPoint)).IsPrime := by
      rw [hqQ]; exact qQ.2
    have hle : IdealSheafData.stalk Q.idealSheaf (j Q'.genericPoint) ≤ q.asIdeal := by
      rw [htQ, Ideal.span_le, Set.singleton_subset_iff, ← hq]; exact hmem
    have heq : IdealSheafData.stalk Q.idealSheaf (j Q'.genericPoint) = q.asIdeal := by
      refine eq_of_le_of_height_eq_one ?_ hle hqh
      rw [htQ, Ne, Ideal.span_singleton_eq_bot]; exact ht0'
    exact hQP (MMP.Intersection.eq_of_stalk_idealSheaf_eq hy'Q hy'P (heq.trans hq.symm))
  have htQ' : 1 ≤ T.ord (algebraMap _ T.functionField tb) Q'.genericPoint := by
    have hK : algebraMap _ T.functionField tb ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr htb0
    have h1 := (MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff Q' tb).mpr htb_mem
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord Q' hK, ← WithZero.exp_zero,
      WithZero.exp_lt_exp, neg_lt_zero] at h1
    omega
  -- the residue identity and the lower bound
  obtain ⟨Nd, K, hK, hQc⟩ := hpair.2
  obtain ⟨n, rfl⟩ := exists_eq_add_one_of_primeDivisor sY hK.topologicalKrullDim_eq P'
  have hdim : topologicalKrullDim Y = n + 1 := by rw [hK.topologicalKrullDim_eq]; push_cast; rfl
  have hBP : BY.coeff P' = 1 := le_antisymm (hB1 P') hP'1
  set B : QDivisor Y := BY - Finsupp.single P' 1 with hBdef
  have hBY : BY = Finsupp.single P' 1 + B := by rw [hBdef]; abel
  have hBP0 : B.coeff P' = 0 := by
    rw [hBdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
  have hBc : ∀ G, G ≠ P' → B.coeff G = BY.coeff G := fun G hG => by
    rw [hBdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hG),
      sub_zero]
  have hBnn : 0 ≤ B := fun G => by
    rcases eq_or_ne G P' with rfl | hGP
    · exact hBP0.ge
    · show (0 : ℚ) ≤ B.coeff G
      rw [hBc G hGP]; exact hB0 G
  obtain ⟨τ, hτ0, hτP, ρ, hρ, -⟩ := exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero sY hdim j P' hP
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK hτ0
  rw [one_smul] at hlin
  have hDq : (Divisor.toQDivisor (divisorOfForm τ) + BY).IsQCartier :=
    hQc.add_of_linearlyEquivalent hlin.symm
  obtain ⟨hgen₁, hpb₁⟩ :=
    h.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P' hP τ hτ0 hτP ρ hρ hDq
  have hDq' : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P' 1 + B).IsQCartier := by
    rwa [add_assoc, ← hBY]
  have hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
      (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P' 1 + B).supp := by
    rw [add_assoc, ← hBY]; exact hgen₁
  have hpb : (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P' 1 + B).IsPullback j hgen
      (Divisor.toQDivisor (divisorOfForm ρ) + BT) :=
    isPullback_congr hpb₁ (by rw [add_assoc, ← hBY]) rfl
  have hlow := one_le_coeff_isPullback_sub_divisorOfForm sY hXv hdim j hTv P' hP B
    (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hBnn) hBP0 τ hτ0 hτP ρ hρ hDq' hgen _ hpb Q' Q
    hQP (by rw [hBc Q hQP]; exact hQ) t ht0 (by rw [hord Q hy'Q, if_pos rfl])
    (fun G hG hGQ => by rw [hord G hG, if_neg hGQ]) htQ'
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at hlow
  linarith

end Step2

/-- The stalk map of a closed immersion into a reduced scheme is injective at a point whose image
has a neighbourhood contained in the image. -/
public theorem stalkMap_injective_of_subset_range {A Y : Scheme.{0}} [IsReduced Y] (f : A ⟶ Y)
    [IsClosedImmersion f] (t : A) (V : Y.Opens) (htV : f.base t ∈ V)
    (hV : (V : Set Y) ⊆ Set.range f.base) : Function.Injective (f.stalkMap t).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨W, hxW, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf a
  rw [Scheme.Hom.germ_stalkMap_apply,
    ← map_zero (ConcreteCategory.hom (A.presheaf.germ (f ⁻¹ᵁ W) t hxW))] at ha
  obtain ⟨V', htV', iV, iV', hV'⟩ := TopCat.Presheaf.germ_eq A.presheaf t hxW hxW _ 0 ha
  rw [map_zero] at hV'
  obtain ⟨W₁, hW₁, hW₁V⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp V'.isOpen
  let W₂ : Y.Opens := W ⊓ ⟨W₁, hW₁⟩ ⊓ V
  have hxW₂ : f.base t ∈ W₂ := ⟨⟨hxW, show t ∈ f.base ⁻¹' W₁ by rw [hW₁V]; exact htV'⟩, htV⟩
  let r₂ := (ConcreteCategory.hom (Y.presheaf.map
    (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W).op)) r
  have hle : f ⁻¹ᵁ W₂ ≤ V' := fun z hz => by
    have : z ∈ f.base ⁻¹' W₁ := hz.1.2
    rwa [hW₁V] at this
  have hz : (ConcreteCategory.hom (f.app W₂)) r₂ = 0 := by
    change (ConcreteCategory.hom (Y.presheaf.map
      (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W).op ≫ f.app W₂)) r = 0
    rw [Scheme.Hom.naturality, ConcreteCategory.comp_apply]
    have : ((Opens.map f.base).map
        (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W).op.unop).op =
        iV.op ≫ (homOfLE hle).op :=
      congrArg Quiver.Hom.op (Subsingleton.elim _ _)
    rw [this, Functor.map_comp, ConcreteCategory.comp_apply, hV', map_zero]
  have hr₂ : r₂ = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨a', rfl⟩ := hV (Y.basicOpen_le r₂ hy).2
    have : a' ∈ f ⁻¹ᵁ Y.basicOpen r₂ := hy
    rw [Scheme.Hom.preimage_basicOpen, hz, Scheme.basicOpen_zero] at this
    exact this
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf
    (homOfLE (inf_le_left.trans inf_le_left) : W₂ ⟶ W) (f.base t) hxW₂ r]
  change (ConcreteCategory.hom (Y.presheaf.germ W₂ (f.base t) hxW₂)) r₂ = 0
  rw [hr₂, map_zero]

/-- If the local ring at `y` is a domain, the generic points of two irreducible components
through `y` coincide. -/
public theorem eq_of_isDomain_stalk {Y : Scheme.{0}} {y : Y} [IsDomain (Y.presheaf.stalk y)]
    {a b : Y} (ha : closure {a} ∈ irreducibleComponents Y)
    (hb : closure {b} ∈ irreducibleComponents Y) (hay : a ⤳ y) (hby : b ⤳ y) : a = b := by
  let ξ := Y.fromSpecStalk y ⟨⊥, Ideal.isPrime_bot⟩
  have key : ∀ c : Y, closure {c} ∈ irreducibleComponents Y → c ⤳ y → c = ξ := by
    intro c hc hcy
    obtain ⟨q, rfl⟩ : c ∈ Set.range (Y.fromSpecStalk y) := by
      rwa [Scheme.range_fromSpecStalk]
    have hsp : ξ ⤳ Y.fromSpecStalk y q :=
      ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le).map (Y.fromSpecStalk y).continuous
    have hsub : closure {Y.fromSpecStalk y q} ⊆ closure {ξ} :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hsp))
        isClosed_closure
    have heq := hc.2 isIrreducible_singleton.closure hsub
    exact ((show IsGenericPoint (Y.fromSpecStalk y q) (closure {ξ}) from
      (hsub.antisymm heq)).eq isGenericPoint_closure)
  exact (key a ha hay).trans (key b hb hby).symm

/-- A Cartier multiple `m(K + Δ)` stays Cartier when `K` is replaced by a linearly equivalent
divisor. -/
public theorem isCartierDivisor_smul_add_of_linearlyEquivalent {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {K K' : Divisor X} {Δ : QDivisor X}
    {m : ℤ} (h : (m • (Divisor.toQDivisor K + Δ)).IsCartierDivisor)
    (hK : K.LinearlyEquivalent K') : (m • (Divisor.toQDivisor K' + Δ)).IsCartierDivisor := by
  obtain ⟨D, hD, hC⟩ := h
  obtain ⟨φ, hφ⟩ := hK
  refine ⟨D - m • principalDivisor φ, ?_, hC.sub ((Divisor.isCartier_principalDivisor φ).zsmul m)⟩
  rw [map_sub, map_zsmul, hD, ← hφ, map_sub, smul_add, smul_add, smul_sub]
  abel

/-- **A differential frame at a smooth point.** Let `y` be a point of a normal integral variety
`X` of dimension `n + 1` over a perfect field, with regular local ring of dimension two and regular
system of parameters `x, y'`. There are `w₁, …, w_{n-1} ∈ 𝒪_{X,y}` whose residues have linearly
independent differentials, such that `dx, dy', dw` is a basis of `Ω_{𝒪_{X,y}/k}`. -/
public theorem exists_basis_D_cons {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType sX]
    {n : ℕ} (hdim : topologicalKrullDim X = (n + 1 : ℕ)) (y : X)
    {x y' : X.presheaf.stalk y} (hz : IsRegularSystemOfParameters ![x, y']) :
    letI := stalkAlgebra sX y
    1 ≤ n ∧ ∃ w : Fin (n - 1) → X.presheaf.stalk y,
      LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y))
        (fun l => KaehlerDifferential.D k (IsLocalRing.ResidueField (X.presheaf.stalk y))
          (IsLocalRing.residue _ (w l))) ∧
      ∃ b : Module.Basis (Fin 2 ⊕ Fin (n - 1)) (X.presheaf.stalk y)
          Ω[X.presheaf.stalk y⁄k],
        ⇑b = Sum.elim (fun i => KaehlerDifferential.D k _ (![x, y'] i))
          (fun l => KaehlerDifferential.D k _ (w l)) := by
  classical
  let := stalkAlgebra sX y
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hfs, hef⟩ := formallySmooth_stalk (sX := sX) y inferInstance
  haveI := hfs
  haveI := hef
  haveI := formallySmooth_residueField_stalk (sX := sX) y hef
  set κ := IsLocalRing.ResidueField (X.presheaf.stalk y)
  -- dimensions
  have hd2 : ringKrullDim (X.presheaf.stalk y) = (2 : ℕ) := hz.2
  obtain ⟨htr, hle⟩ := trdeg_residueField_stalk sX hdim y hd2
  refine ⟨by omega, ?_⟩
  have : Algebra.EssFiniteType (X.presheaf.stalk y) κ :=
    (RingHom.essFiniteType_algebraMap).mp
      (RingHom.FiniteType.of_surjective (algebraMap (X.presheaf.stalk y) κ)
        IsLocalRing.residue_surjective).essFiniteType
  have : Algebra.EssFiniteType k κ := .comp _ (X.presheaf.stalk y) _
  have hfinκ : Module.finrank κ Ω[κ⁄k] = n - 1 := by
    rw [finrank_kaehlerDifferential_eq_trdeg, htr]
    simp
  have : FiniteDimensional κ Ω[κ⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k κ).1
  obtain ⟨bs, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent κ (Set.range (KaehlerDifferential.D k κ))
  have hbtop : Submodule.span κ (Set.range ((↑) : bs → Ω[κ⁄k])) = ⊤ := by
    rw [Subtype.range_coe, hbspan, KaehlerDifferential.span_range_derivation]
  let bb := Module.Basis.mk hbli hbtop.ge
  have : Finite bs := Module.Finite.finite_basis bb
  letI : Fintype bs := Fintype.ofFinite bs
  have hcard : Fintype.card bs = n - 1 := by rw [← Module.finrank_eq_card_basis bb, hfinκ]
  let e : Fin (n - 1) ≃ bs := (Fintype.equivFinOfCardEq hcard).symm
  choose wb hwb using fun l : Fin (n - 1) => hbsub (e l).2
  choose w hw using fun l => IsLocalRing.residue_surjective (R := X.presheaf.stalk y) (wb l)
  have hli : LinearIndependent κ
      (fun l => KaehlerDifferential.D k κ (IsLocalRing.residue _ (w l))) := by
    have h := hbli.comp e e.injective
    convert h using 1
    funext l
    simp only [Function.comp_apply, hw, hwb]
  refine ⟨w, hli, ?_⟩
  -- `Ω_{𝒪_{X,y}/k}` has rank `n + 1`
  have : Module.Finite (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k] :=
    KaehlerDifferential.finite k _
  have : Module.Projective (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k] :=
    ((Algebra.formallySmooth_iff k _).mp inferInstance).1
  have : Module.Free (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k] :=
    Module.free_of_flat_of_isLocalRing
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX y
  have := essFiniteType_functionField (sX := sX)
  have hrank : Module.finrank (X.presheaf.stalk y) Ω[X.presheaf.stalk y⁄k] = 2 + (n - 1) := by
    rw [← finrank_kaehlerDifferential_eq_of_isFractionRing (K := X.functionField),
      finrank_kaehlerDifferential_eq_trdeg,
      toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdim]
    omega
  exact exists_basis_D_sumElim hrank hz hli

/-- A basis `v₀, v₁, v` of `M`, ordered as `Fin.cons v₀ (Fin.cons v₁ v)`, has top exterior power
spanned by its wedge. -/
public theorem span_ιMulti_cons_eq_top {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {n' : ℕ}
    (b : Module.Basis (Fin 2 ⊕ Fin n') A M) (v0 v1 : M) (v : Fin n' → M)
    (hb : ⇑b = Sum.elim ![v0, v1] v) :
    Submodule.span A {exteriorPower.ιMulti A (n' + 2) (Fin.cons v0 (Fin.cons v1 v))} = ⊤ := by
  let e : Fin 2 ⊕ Fin n' ≃ Fin (n' + 2) :=
    finSumFinEquiv.trans (finCongr (by omega))
  let b' := b.reindex e
  have hb' : ⇑b' = Fin.cons v0 (Fin.cons v1 v) := by
    funext l
    rw [Module.Basis.coe_reindex, Function.comp_apply, hb]
    refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun l => ?_) l) l
    · rfl
    · rfl
    · have he : e (Sum.inr l) = l.succ.succ := by
        ext; simp [e]
      rw [show e.symm l.succ.succ = Sum.inr l by rw [← he, Equiv.symm_apply_apply]]
      rfl
  have h := (MMP.Intersection.bijective_smul_ιMulti_basis b').2
  rw [hb'] at h
  refine eq_top_iff.mpr fun σ _ => ?_
  obtain ⟨r, rfl⟩ := h σ
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **Writing a pluriform in a frame at a point.** Let `y` be a point of a normal integral
variety of dimension `d` over a perfect field, `σ = dz₁ ∧ ⋯ ∧ dz_d` a generator of the top forms
of `𝒪_{X,y}` and `x, y' ∈ 𝒪_{X,y}` nonzero. If `ord_Γ τ = -m(ord_Γ x + ord_Γ y')` along every
prime divisor `Γ` through `y`, then `τ = u (x⁻¹ y'⁻¹ σ)^{⊗m}` for a unit `u` of `𝒪_{X,y}`. -/
public theorem exists_isUnit_eq_smul_tprod {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] {d : ℕ} (hdim : topologicalKrullDim X = d) (y : X)
    (z : Fin d → X.presheaf.stalk y) (x y' : X.presheaf.stalk y)
    (hσ : letI := stalkAlgebra sX y
      Submodule.span (X.presheaf.stalk y)
        {exteriorPower.ιMulti (X.presheaf.stalk y) d
          (fun l => KaehlerDifferential.D k (X.presheaf.stalk y) (z l))} = ⊤)
    {m : ℕ} (τ : RationalPluriForms sX d m) (hτ0 : τ ≠ 0)
    (hx0 : algebraMap (X.presheaf.stalk y) X.functionField x ≠ 0)
    (hy0 : algebraMap (X.presheaf.stalk y) X.functionField y' ≠ 0)
    (hord : ∀ Γ : MMP.Mori.PrimeDivisor X, y ∈ Γ.support →
      Γ.ordForm τ = -(m : ℤ) * (X.ord (algebraMap _ X.functionField x) Γ.genericPoint +
        X.ord (algebraMap _ X.functionField y') Γ.genericPoint)) :
    letI := functionFieldAlgebra sX
    ∃ u : X.presheaf.stalk y, IsUnit u ∧
      τ = (algebraMap _ X.functionField u • PiTensorProduct.tprod X.functionField
        (fun _ : Fin m => (algebraMap _ X.functionField x)⁻¹ • (algebraMap _ X.functionField y')⁻¹ •
          exteriorPower.ιMulti X.functionField d (fun l => KaehlerDifferential.D k X.functionField
            (algebraMap _ X.functionField (z l)))) :
        RationalPluriForms sX d m) := by
  classical
  let := stalkAlgebra sX y
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX y
  have := essFiniteType_functionField (sX := sX)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  have hfin : Module.finrank X.functionField Ω[X.functionField⁄k] = d := by
    rw [finrank_kaehlerDifferential_eq_trdeg,
      toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdim]
  haveI := nontrivial_exteriorPower_of_finrank_eq k X.functionField hfin
  have h0 := topFormsMap_ne_zero_of_span_eq_top (k := k) (K := X.functionField) hσ
  have hF : topFormsMap k (X.presheaf.stalk y) X.functionField d
      (exteriorPower.ιMulti (X.presheaf.stalk y) d
        (fun l => KaehlerDifferential.D k (X.presheaf.stalk y) (z l))) =
      exteriorPower.ιMulti X.functionField d (fun l => KaehlerDifferential.D k X.functionField
        (algebraMap _ X.functionField (z l))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext l
    rw [KaehlerDifferential.map_D]
  set c := formCoeff (k := k) (m := (m : ℤ)) (X.presheaf.stalk y) hσ h0 τ with hcdef
  have hc := formCoeff_smul_basis (m := (m : ℤ)) hσ h0 τ
  have hb : (ZTensorPower.basis (topFormsBasis (X.presheaf.stalk y) hσ h0) (m : ℤ) () :
      RationalPluriForms sX d m) = PiTensorProduct.tprod X.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti X.functionField d (fun l => KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (z l)))) := by
    rw [← hF]
    exact (ZTensorPower.basis_ofNat _ m).trans (by rw [topFormsBasis_apply])
  have hc0 : c ≠ 0 := fun h => hτ0 ((formCoeff_eq_zero_iff (m := (m : ℤ)) hσ h0 τ).mp h)
  set u' : X.functionField := c * (algebraMap _ X.functionField x *
    algebraMap _ X.functionField y') ^ m with hu'
  have hxy0 : algebraMap _ X.functionField x * algebraMap _ X.functionField y' ≠ 0 :=
    mul_ne_zero hx0 hy0
  have hu'0 : u' ≠ 0 := mul_ne_zero hc0 (pow_ne_zero _ hxy0)
  have hordu : ∀ Γ : MMP.Mori.PrimeDivisor X, y ∈ Γ.support → X.ord u' Γ.genericPoint = 0 := by
    intro Γ hΓ
    have h1 : Γ.ordForm τ = X.ord c Γ.genericPoint :=
      MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX y Γ hΓ hσ h0 τ
    have h2 := hord Γ hΓ
    rw [hu', Scheme.ord_mul hc0 (pow_ne_zero _ hxy0), ← zpow_natCast,
      MMP.Mori.ord_zpow _ hxy0, Scheme.ord_mul hx0 hy0, ← h1, h2]
    push_cast
    ring
  obtain ⟨u, hu, hu''⟩ :=
    MMP.Mori.exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero y hu'0 hordu
  refine ⟨u, hu, ?_⟩
  set F := exteriorPower.ιMulti X.functionField d (fun l => KaehlerDifferential.D k X.functionField
    (algebraMap _ X.functionField (z l))) with hFdef
  set a := algebraMap (X.presheaf.stalk y) X.functionField x
  set b := algebraMap (X.presheaf.stalk y) X.functionField y'
  have e1 : (PiTensorProduct.tprod X.functionField (fun _ : Fin m => a⁻¹ • b⁻¹ • F) :
      RationalPluriForms sX d m) =
      (a⁻¹ * b⁻¹) ^ m • (PiTensorProduct.tprod X.functionField (fun _ : Fin m => F) :
        RationalPluriForms sX d m) := by
    rw [← MMP.Mori.tprod_const_smul]
    congr 1
    funext _
    rw [smul_smul]
  rw [e1, hu'', smul_smul, ← hb, ← hc]
  congr 1
  rw [hu', mul_assoc, ← mul_pow, show a * b * (a⁻¹ * b⁻¹) = 1 by field_simp, one_pow, mul_one]

/-- **The residue of a form written in a frame.** Let `j : S ⟶ X` be a closed immersion onto a
prime divisor `P` of `X` passing through `y`, with `I(P)_y = (t)`, and let `s ∈ 𝒪_{X,y}` be
a unit at the generic point of `P`. If `τ = u (t⁻¹ s⁻¹ dt ∧ ds ∧ dw)^{⊗m}`, then the residue of
`τ` along `S` is `ū s̄^{-m} (ds̄ ∧ dw̄)^{⊗m}`. -/
public theorem isPoincareResidue_of_eq_frame {k : Type} [Field k] {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral S]
    (j : S ⟶ X) {n' m : ℕ} {y : X} (hsp : j (genericPoint S) ⤳ y)
    (t s : X.presheaf.stalk y) (w : Fin n' → X.presheaf.stalk y) (u : X.presheaf.stalk y)
    (ht : X.ord (algebraMap _ X.functionField t) (j (genericPoint S)) = 1)
    (hs : IsUnit ((X.presheaf.stalkSpecializes hsp).hom s))
    (τ : RationalPluriForms sX (n' + 2) m)
    (hτ : letI := functionFieldAlgebra sX
      τ = (algebraMap _ X.functionField u • PiTensorProduct.tprod X.functionField
        (fun _ : Fin m => (algebraMap _ X.functionField t)⁻¹ •
          (algebraMap _ X.functionField s)⁻¹ •
          exteriorPower.ιMulti X.functionField (n' + 2) (Fin.cons
            (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField t))
            (Fin.cons (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField s))
              fun l => KaehlerDifferential.D k X.functionField
                (algebraMap _ X.functionField (w l))))) :
        RationalPluriForms sX (n' + 2) m)) :
    letI := functionFieldAlgebra (j ≫ sX)
    IsPoincareResidue sX j (n' + 1) m τ
      ((j.stalkMap (genericPoint S)).hom ((X.presheaf.stalkSpecializes hsp).hom u *
          (((hs.unit⁻¹ : (X.presheaf.stalk (j (genericPoint S)))ˣ) :
            X.presheaf.stalk (j (genericPoint S))) ^ m)) •
        PiTensorProduct.tprod S.functionField (fun _ : Fin m =>
          exteriorPower.ιMulti S.functionField (n' + 1) fun i =>
            KaehlerDifferential.D k S.functionField ((j.stalkMap (genericPoint S)).hom
              ((X.presheaf.stalkSpecializes hsp).hom
                ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk y) i))))) := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (j ≫ sX)
  set sp := (X.presheaf.stalkSpecializes hsp).hom
  have hsp_alg : ∀ a, algebraMap _ X.functionField (sp a) = algebraMap _ X.functionField a :=
    fun a => MMP.Mori.algebraMap_stalkSpecializes hsp a
  refine ⟨sp t, sp u * (((hs.unit⁻¹ : (X.presheaf.stalk _)ˣ) : _) ^ m),
    fun i => sp ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk y) i),
    by rw [hsp_alg]; exact ht, ?_, rfl⟩
  rw [hτ]
  have hcons : (fun i => KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField
      (sp ((Fin.cons s w : Fin (n' + 1) → X.presheaf.stalk y) i)))) =
      Fin.cons (KaehlerDifferential.D k X.functionField (algebraMap _ X.functionField s))
        (fun l => KaehlerDifferential.D k X.functionField
          (algebraMap _ X.functionField (w l))) := by
    funext i
    refine Fin.cases ?_ (fun l => ?_) i
    · simp only [Fin.cons_zero, hsp_alg]
    · simp only [Fin.cons_succ, hsp_alg]
  have hs0 : algebraMap _ X.functionField s ≠ 0 := by
    rw [← hsp_alg]; exact (hs.map _).ne_zero
  have hinv : algebraMap (X.presheaf.stalk (j (genericPoint S))) X.functionField
      ((hs.unit⁻¹ : (X.presheaf.stalk (j (genericPoint S)))ˣ) :
        X.presheaf.stalk (j (genericPoint S))) = (algebraMap _ X.functionField s)⁻¹ := by
    rw [← hsp_alg s]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    have : ((hs.unit⁻¹ : (X.presheaf.stalk _)ˣ) : X.presheaf.stalk (j (genericPoint S))) *
        sp s = 1 :=
      hs.unit.inv_mul
    rw [this, map_one]
  rw [map_mul, map_pow, hinv, hsp_alg, hsp_alg, hcons, mul_smul]
  congr 1
  rw [← MMP.Mori.tprod_const_smul]
  congr 1
  funext _
  rw [smul_comm]

/-- Exchanging the first two vectors of a wedge changes its sign. -/
public theorem ιMulti_cons_cons_swap {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {n' : ℕ}
    (a b : M) (v : Fin n' → M) :
    exteriorPower.ιMulti K (n' + 2) (Fin.cons a (Fin.cons b v)) =
      -exteriorPower.ιMulti K (n' + 2) (Fin.cons b (Fin.cons a v)) := by
  have h := (exteriorPower.ιMulti K (n' + 2) (M := M)).map_swap
    (Fin.cons b (Fin.cons a v) : Fin (n' + 2) → M) (i := 0) (j := 1) (by simp [Fin.ext_iff])
  rw [← h]
  congr 1
  funext l
  refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun l => ?_) l) l
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
      (by simp [Fin.ext_iff])]
    rfl

/-- Linear independence descends along a semilinear additive map over a field homomorphism. -/
private theorem linearIndependent_of_comp_ringHom {ι K L M M' : Type*} [Field K] [Field L]
    [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module L M'] (φ : K →+* L) (j : M →+ M')
    (hc : ∀ (r : K) (m : M), j (r • m) = φ r • j m) {v : ι → M}
    (hv : LinearIndependent L (j ∘ v)) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  have h := congrArg j hg
  rw [map_sum, map_zero] at h
  simp only [hc] at h
  exact (map_eq_zero φ).mp (hv s (fun i => φ (g i)) h i hi)

/-- **The restriction of a coordinate is a uniformizer.** Let `f : S ⟶ Y` be a closed immersion
from a normal integral scheme and `Q` a prime divisor of `S`. If `x, y'` is a regular system of
parameters of `𝒪_{Y,f(η_Q)}` and the kernel of `𝒪_{Y,f(η_Q)} → 𝒪_{S,η_Q}` is `(x)`, then the
restriction of `y'` has order one along `Q`. -/
public theorem ord_stalkMap_eq_one {Y S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] (f : S ⟶ Y) [IsClosedImmersion f] (Q : MMP.Mori.PrimeDivisor S)
    {x y' : Y.presheaf.stalk (f Q.genericPoint)} (hz : IsRegularSystemOfParameters ![x, y'])
    (hker : RingHom.ker (f.stalkMap Q.genericPoint).hom = Ideal.span {x}) :
    S.ord (algebraMap _ S.functionField ((f.stalkMap Q.genericPoint).hom y')) Q.genericPoint =
      1 := by
  classical
  set φ := (f.stalkMap Q.genericPoint).hom
  have hsurj : Function.Surjective φ := f.stalkMap_surjective Q.genericPoint
  haveI : IsLocalHom φ := inferInstance
  have hy'm : y' ∈ IsLocalRing.maximalIdeal _ := hz.1 ▸ Ideal.subset_span ⟨1, rfl⟩
  have hφx : φ x = 0 := (RingHom.mem_ker).mp (hker ▸ Ideal.mem_span_singleton_self x)
  -- the maximal ideal of `𝒪_{S,η_Q}` is generated by the image of `y'`
  have hmB : IsLocalRing.maximalIdeal (S.presheaf.stalk Q.genericPoint) = Ideal.span {φ y'} := by
    apply le_antisymm
    · intro b hb
      obtain ⟨a, rfl⟩ := hsurj b
      have ha : a ∈ IsLocalRing.maximalIdeal _ := by
        by_contra h
        exact (IsLocalRing.mem_maximalIdeal _).mp hb
          ((IsLocalRing.notMem_maximalIdeal.mp h).map φ)
      rw [← hz.1, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Ideal.mem_span_pair] at ha
      obtain ⟨c, d, rfl⟩ := ha
      rw [map_add, map_mul, map_mul, hφx, mul_zero, zero_add]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
        (IsLocalRing.mem_maximalIdeal _).mp hy'm (isUnit_of_map_unit φ _ h)
  have hdim : ringKrullDim (S.presheaf.stalk Q.genericPoint) = (1 : ℕ) := by
    rw [ringKrullDim_stalk_eq_coheight, Q.coheight_genericPoint]; rfl
  have hreg : IsRegularSystemOfParameters ![φ y'] := by
    refine ⟨?_, hdim⟩
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty, hmB]
  have hmem : Q.genericPoint ∈ Q.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  obtain ⟨q, -, hq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Q hmem
  have hqm : q.asIdeal = IsLocalRing.maximalIdeal _ := by
    haveI := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing (X := S) Q
    have hne : q.asIdeal ≠ ⊥ := by
      intro h
      rw [h, Ideal.height_bot] at hq1
      exact zero_ne_one hq1
    exact IsLocalRing.eq_maximalIdeal (q.isPrime.isMaximal hne)
  have hQ : AlgebraicGeometry.IdealSheafData.stalk Q.idealSheaf Q.genericPoint =
      Ideal.span {(![φ y'] : Fin 1 → _) 0} := by
    rw [hq, hqm, hmB]; rfl
  exact (ord_algebraMap_eq_ite_of_stalk_eq_span hreg 0 Q hmem hQ Q hmem).trans (if_pos rfl)

/-- Linear independence of differentials is transported along a `k`-compatible isomorphism of
fields. -/
public theorem linearIndependent_D_ringEquiv {k K L ι' : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (e : K ≃+* L)
    (he : ∀ c : k, e (algebraMap k K c) = algebraMap k L c) {v : ι' → K}
    (hv : LinearIndependent K fun i => KaehlerDifferential.D k K (v i)) :
    LinearIndependent L fun i => KaehlerDifferential.D k L (e (v i)) := by
  letI : Algebra L K := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k K c = e.symm (algebraMap k L c)
    rw [← he, RingEquiv.symm_apply_apply]
  refine linearIndependent_of_comp_ringHom e.symm.toRingHom
    (KaehlerDifferential.map k k L K).toAddMonoidHom (fun r m => ?_) ?_
  · exact (KaehlerDifferential.map k k L K).map_smul r m
  · convert hv using 1
    funext i
    simp only [Function.comp_apply, LinearMap.toAddMonoidHom_coe, KaehlerDifferential.map_D]
    congr 1
    exact e.symm_apply_apply (v i)

/-- **Residue fields along a closed immersion.** For a closed immersion `f : S ⟶ Y` of schemes over
`k`, the residue field map at `q ∈ S` is a `k`-compatible isomorphism `κ(f q) ≅ κ(q)`. -/
public theorem exists_residueField_ringEquiv {k : Type} [Field k] {Y S : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (f : S ⟶ Y) [IsClosedImmersion f] (q : S) (g : S ⟶ Spec (.of k))
    (hg : g = f ≫ sY) :
    letI := stalkAlgebra sY (f q)
    letI : Algebra k (S.residueField q) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ S.Γevaluation q).hom.toAlgebra
    ∃ e : IsLocalRing.ResidueField (Y.presheaf.stalk (f q)) ≃+* S.residueField q,
      (∀ a, e (IsLocalRing.residue _ a) = S.residue q ((f.stalkMap q).hom a)) ∧
      ∀ c : k, e (algebraMap k _ c) = algebraMap k (S.residueField q) c := by
  subst hg
  letI := stalkAlgebra sY (f q)
  letI : Algebra k (S.residueField q) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sY).appTop ≫ S.Γevaluation q).hom.toAlgebra
  set φ := (f.residueFieldMap q).hom
  have hres : ∀ a, φ (IsLocalRing.residue _ a) = S.residue q ((f.stalkMap q).hom a) :=
    fun a => rfl
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨c, rfl⟩ := S.residue_surjective q b
    obtain ⟨a, rfl⟩ := f.stalkMap_surjective q c
    exact ⟨_, hres a⟩
  refine ⟨RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩, hres, fun c => ?_⟩
  change φ ((Y.Γevaluation (f q)).hom (sY.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom c))) = _
  rw [Scheme.Γevaluation_naturality_apply]
  rfl

section Floor

/-- A prime component of the round down of a boundary with coefficients in `[0, 1]` has
coefficient one. -/
public theorem coeff_eq_one_of_mem_roundDown_support {X : Scheme.{0}} {B : QDivisor X}
    (h0 : ∀ P, 0 ≤ B.coeff P) (h1 : ∀ P, B.coeff P ≤ 1) {P : MMP.Mori.PrimeDivisor X}
    (hP : P ∈ B.roundDown.support) : B.coeff P = 1 := by
  have hP' : B.roundDown.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
  rw [DivisorWithCoeffs.coeff_roundDown] at hP'
  refine le_antisymm (h1 P) ?_
  by_contra hlt
  push Not at hlt
  exact hP' (Int.floor_eq_zero_iff.mpr ⟨h0 P, hlt⟩)

/-- A prime divisor of coefficient at least one is a component of the round down. -/
public theorem mem_roundDown_support_of_one_le_coeff {X : Scheme.{0}} {B : QDivisor X}
    {P : MMP.Mori.PrimeDivisor X} (hP : 1 ≤ B.coeff P) : P ∈ B.roundDown.support := by
  rw [Finsupp.mem_support_iff]
  change B.roundDown.coeff P ≠ 0
  rw [DivisorWithCoeffs.coeff_roundDown]
  have h1 : (1 : ℤ) ≤ ⌊B.coeff P⌋ := Int.le_floor.mpr (by exact_mod_cast hP)
  omega

/-- The support of a prime component of the floor of a dlt pair is a boundary stratum. -/
public theorem isDltStratum_support {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    (hB : MMP.Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ B.roundDown.support) :
    IsDltStratum sX B (P.support : Set X) := by
  have hP1 := coeff_eq_one_of_mem_roundDown_support hB.nonneg hdlt.2.1 hP
  refine ⟨hdlt, {P}, Finset.singleton_nonempty P, by simp [hP1], ?_, ?_⟩
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    exact ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    refine ⟨⟨?_, le_rfl⟩, fun S hS _ => hS.2⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure

/-- `d + 1 = n + 1` in `WithBot ℕ∞` forces `d = n`. -/
public theorem eq_natCast_of_add_one_eq_natCast_succ {d : WithBot ℕ∞} {n : ℕ}
    (h : d + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : d = (n : ℕ) := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
      exact ENat.top_ne_coe (n + 1) (by simpa using WithBot.coe_injective this)
    | coe e =>
      have : ((e + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [← h]; norm_cast
      have : e + 1 = n + 1 := by exact_mod_cast this
      norm_cast; omega

/-- On an integral scheme locally of finite type over a field, a prime divisor has codimension
one: its dimension plus one is the dimension of the scheme. -/
public theorem topologicalKrullDim_support_add_one {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (P.support : Set X) + 1 = topologicalKrullDim X := by
  let _ : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact_mod_cast h

/-- **Adjunction to a floor component.** A prime component `P` of the floor of a dlt pair is the
image of a closed immersion carrying one adjunction step `(X, B) ⇝ (P, Diff_P(B - P))`. -/
public theorem exists_isAdjunctionStep_of_mem_roundDown_support {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} (hdim : topologicalKrullDim X = (n + 1 : ℕ)) {B : QDivisor X}
    (hB : MMP.Fourfold.IsPair sX B) (hdlt : MMP.Intersection.IsDltPair sX B)
    {P : MMP.Mori.PrimeDivisor X} (hP : P ∈ B.roundDown.support) :
    ∃ (S : Scheme.{0}) (j : S ⟶ X) (BS : QDivisor S),
      Set.range j.base = (P.support : Set X) ∧ IsAdjunctionStep sX B j BS := by
  haveI := hB.isAlgClosed
  haveI := hB.charZero
  obtain ⟨S, j, BS, hj, ⟨F⟩⟩ :=
    (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
      (isDltStratum_support hB hdlt hP)).1.1
  have hlft : LocallyOfFiniteType sX := hB.isPair.1.1.toLocallyOfFiniteType
  have hdimS : topologicalKrullDim S = (n : ℕ) := by
    haveI := F.isClosedImmersion
    rw [j.isClosedEmbedding.toIsEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
    have h1 := topologicalKrullDim_support_add_one sX P
    rw [hdim, ← hj] at h1
    exact eq_natCast_of_add_one_eq_natCast_succ h1
  have hlen := F.dim_add_length hdim hdimS
  cases F with
  | refl h => simp [StratumAdjunctionData.length] at hlen
  | @step S₀ T₀ ι₀ BS₀ F₀ j₀ BT₀ h₀ =>
    cases F₀ with
    | refl h => exact ⟨_, _, _, hj, by simpa using h₀⟩
    | step F₁ _ _ _ => simp [StratumAdjunctionData.length] at hlen

/-- A morphism from a reduced scheme whose image lies in the image of a morphism from a reduced
scheme kills the kernel of the latter. -/
public theorem ker_le_ker_of_range_subset {T S X : Scheme.{0}} [IsReduced T] [IsReduced S]
    (ι : T ⟶ X) (j : S ⟶ X) (h : Set.range j ⊆ Set.range ι) : ι.ker ≤ j.ker := by
  rw [ker_eq_vanishingIdeal, ker_eq_vanishingIdeal]
  exact Scheme.IdealSheafData.vanishingIdeal_antimono fun x hx => closure_mono h hx

/-- A locally Noetherian scheme has finitely many irreducible components on each quasi-compact
open. -/
public theorem finite_irreducibleComponents_of_isLocallyNoetherian (T : Scheme.{0})
    [IsLocallyNoetherian T] :
    ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite := by
  intro U hU
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : IsNoetherian U.toScheme := { }
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- A finite coproduct of normal schemes is normal. -/
private theorem isNormal_sigmaObj {I : Type} (S : I → Scheme.{0}) [hS : ∀ i, IsNormal (S i)] :
    IsNormal (∐ S) := by
  rw [isNormal_iff_stalk_normal]
  intro x
  obtain ⟨i, y, rfl⟩ := (sigmaOpenCover S).exists_eq x
  let ε := (asIso (((sigmaOpenCover S).f i).stalkMap y)).commRingCatIsoToRingEquiv
  have : IsNormal ((sigmaOpenCover S).X i) := hS i
  have : IsIntegrallyClosed (((sigmaOpenCover S).X i).presheaf.stalk y) := IsNormal.stalk_normal y
  have : IsDomain (((sigmaOpenCover S).X i).presheaf.stalk y) := IsNormal.stalk_isDomain y
  exact ⟨ε.injective.isDomain ε.toRingHom, IsIntegrallyClosed.of_equiv ε.symm⟩

/-- The coproduct of closed immersions of integral schemes onto the distinct irreducible
components of a reduced scheme is birational. -/
private theorem isBirational_sigmaDesc {T : Scheme.{0}} [IsReduced T]
    {I : Type} (S : I → Scheme.{0}) [∀ i, IsIntegral (S i)]
    (n : ∀ i, S i ⟶ T) [∀ i, IsClosedImmersion (n i)]
    (hrange : ∀ i, Set.range (n i) ∈ irreducibleComponents T)
    (hcomp : ∀ Z ∈ irreducibleComponents T, ∃! i, Set.range (n i) = Z) :
    IsBirational (Limits.Sigma.desc n) := by
  classical
  have hfι : ∀ i y, (Limits.Sigma.desc n) (Limits.Sigma.ι S i y) = n i y := fun i y => by
    rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]
  have hηcl : ∀ i, closure {genericPoint (S i)} = (Set.univ : Set (S i)) := fun i =>
    (genericPoint_spec (S i)).def
  -- the range of `nᵢ` is the closure of the image of the generic point
  have hcl : ∀ i, closure {n i (genericPoint (S i))} = Set.range (n i) := fun i => by
    rw [← Set.image_singleton, (n i).isClosedEmbedding.closure_image_eq, hηcl i,
      Set.image_univ]
  -- the range of a coprojection is clopen
  have hclopen : ∀ i, IsClopen (Set.range (Limits.Sigma.ι S i)) := fun i => by
    have : Set.range (Limits.Sigma.ι S i) = sigmaMk S '' Set.range (Sigma.mk i) := by
      ext x; constructor
      · rintro ⟨y, rfl⟩; exact ⟨⟨i, y⟩, ⟨y, rfl⟩, sigmaMk_mk S i y⟩
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, (sigmaMk_mk S i y).symm⟩
    rw [this]
    exact ⟨(sigmaMk S).isClosedMap _ isClopen_range_sigmaMk.1,
      (sigmaMk S).isOpenMap _ isClopen_range_sigmaMk.2⟩
  have hgenS : ∀ i, Limits.Sigma.ι S i (genericPoint (S i)) ∈ genericPoints (∐ S : Scheme.{0}) :=
      fun i => by
    refine ⟨isIrreducible_singleton.closure, fun Z hZ hsub => ?_⟩
    have hZC : Z ⊆ Set.range (Limits.Sigma.ι S i) :=
      (show IsIrreducible Z from hZ).2.isPreconnected.subset_isClopen (hclopen i)
        ⟨_, hsub (subset_closure rfl), _, rfl⟩
    refine hZC.trans ?_
    rw [← Set.image_univ, ← hηcl i, ← Set.image_singleton]
    exact image_closure_subset_closure_image (Limits.Sigma.ι S i).continuous
  have hgenS' : ∀ x ∈ genericPoints (∐ S : Scheme.{0}),
      ∃ i, x = Limits.Sigma.ι S i (genericPoint (S i)) := by
    intro x hx
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk S).surjective x
    rw [sigmaMk_mk] at hx ⊢
    refine ⟨i, congrArg _ ?_⟩
    have hemb := (Limits.Sigma.ι S i).isOpenEmbedding
    have hpre := preimage_mem_irreducibleComponents hx hemb
      ⟨_, subset_closure rfl, y, rfl⟩
    have hy : closure {y} = (Set.univ : Set (S i)) := by
      rw [hemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
      exact ((hpre.2 (IrreducibleSpace.isIrreducible_univ (S i)) (Set.subset_univ _)).antisymm
        (Set.subset_univ _)).symm
    exact (IsGenericPoint.eq (show IsGenericPoint y ⊤ from hy) (genericPoint_spec (S i)))
  have hmaps : ∀ i, closure {(Limits.Sigma.desc n) (Limits.Sigma.ι S i (genericPoint (S i)))} ∈
      irreducibleComponents T := fun i => by
    rw [hfι, hcl]
    exact hrange i
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := hgenS' x hx
    exact hmaps i
  · intro x hx x' hx' hxx'
    obtain ⟨i, rfl⟩ := hgenS' x hx
    obtain ⟨i', rfl⟩ := hgenS' x' hx'
    rw [hfι, hfι] at hxx'
    have : Set.range (n i) = Set.range (n i') := by rw [← hcl, ← hcl, hxx']
    obtain ⟨j, -, hj⟩ := hcomp _ (hrange i)
    rw [hj i rfl, hj i' this.symm]
  · intro t ht
    obtain ⟨i, hi, -⟩ := hcomp _ ht
    refine ⟨_, hgenS i, ?_⟩
    rw [hfι]
    refine (IsGenericPoint.eq (show IsGenericPoint _ (closure {t}) from ?_) rfl)
    change closure _ = _
    rw [hcl, hi]
  · intro x hx
    obtain ⟨i, rfl⟩ := hgenS' x hx
    letI := (isField_stalk_of_closure_mem_irreducibleComponents (hx := hmaps i)).toField
    have hsurj : Function.Surjective ((Limits.Sigma.desc n).stalkMap
        (Limits.Sigma.ι S i (genericPoint (S i)))) := by
      have key : ∀ g : S i ⟶ T, g = n i →
          Function.Surjective (g.stalkMap (genericPoint (S i))) := by
        rintro _ rfl; exact (n i).stalkMap_surjective _
      have h := key _ (Limits.Sigma.ι_desc n i)
      rw [Scheme.Hom.stalkMap_comp] at h
      have hbij := ConcreteCategory.bijective_of_isIso
        ((Limits.Sigma.ι S i).stalkMap (genericPoint (S i)))
      intro z
      obtain ⟨w, hw⟩ := h ((Limits.Sigma.ι S i).stalkMap _ z)
      exact ⟨w, hbij.1 hw⟩
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨((Limits.Sigma.desc n).stalkMap _).hom.injective, hsurj⟩

/-- **The normalization of a scheme with normal components.** Let `T` be a reduced scheme whose
irreducible components are the images of finitely many closed immersions `nᵢ : Sᵢ ⟶ T` of normal
integral schemes, each component being the image of exactly one `nᵢ`. Then `⨿ᵢ Sᵢ ⟶ T` is the
normalization of `T`. -/
public theorem exists_iso_normalizationScheme {T : Scheme.{0}} [IsReduced T]
    (hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite)
    {I : Type} [Finite I] (S : I → Scheme.{0}) [∀ i, IsIntegral (S i)] [∀ i, IsNormal (S i)]
    (n : ∀ i, S i ⟶ T) [∀ i, IsClosedImmersion (n i)]
    (hS : ∀ V : (∐ S : Scheme.{0}).Opens, IsCompact V.1 → (irreducibleComponents V).Finite)
    (hrange : ∀ i, Set.range (n i) ∈ irreducibleComponents T)
    (hcomp : ∀ Z ∈ irreducibleComponents T, ∃! i, Set.range (n i) = Z) :
    ∃ φ : (∐ S) ≅ Stacks.AlgebraicGeometry.Normalization.normalizationScheme T hfin,
      φ.hom ≫ slcCurveNormalization T hfin = Limits.Sigma.desc n := by
  haveI : IsIntegralHom (Limits.Sigma.desc n) := isIntegralHom_sigmaDesc_of_finite n
  haveI : IsNormal (∐ S) := isNormal_sigmaObj S
  have hbir := isBirational_sigmaDesc S n hrange hcomp
  obtain ⟨hX', g, e, hg, he⟩ := exists_normalizationFactorization_of_integral_of_birational hfin
    (Limits.Sigma.desc n)
    (fun U hU => hS _ ((Limits.Sigma.desc n).isCompact_preimage hU))
    (fun U _ => hbir.morphismRestrict U)
  haveI := Scheme.isIso_normalization_of_isNormal (∐ S) hX'
  haveI : IsIso g := by rw [← he]; infer_instance
  refine ⟨(asIso g).symm, ?_⟩
  change inv g ≫ Scheme.normalization T hfin = _
  rw [← hg, IsIso.inv_hom_id_assoc]

/-- A prime divisor is determined by its support. -/
public theorem primeDivisor_eq_of_support_eq {X : Scheme.{0}} {P Q : MMP.Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.mpr h).eq

/-- Each `n i` has an irreducible component of `T` as its range, and every irreducible component
of `T` is the range of exactly one `n i`. -/
public theorem range_mem_irreducibleComponents_of_floor {X T : Scheme.{0}} (ι : T ⟶ X)
    [IsClosedImmersion ι] {B : QDivisor X}
    (hT : Set.range ι.base = ⋃ P ∈ B.roundDown.support, (P.support : Set X))
    {I : Type} (S : I → Scheme.{0}) (n : ∀ i, S i ⟶ T) (P : I → MMP.Mori.PrimeDivisor X)
    (hP : ∀ i, P i ∈ B.roundDown.support) (hPinj : Function.Injective P)
    (hPsurj : ∀ Q ∈ B.roundDown.support, ∃ i, P i = Q)
    (hn : ∀ i, Set.range (n i ≫ ι) = ((P i).support : Set X)) :
    (∀ i, Set.range (n i) ∈ irreducibleComponents T) ∧
      ∀ Z ∈ irreducibleComponents T, ∃! i, Set.range (n i) = Z := by
  have hinj : Function.Injective ι.base := ι.isClosedEmbedding.injective
  have himg : ∀ i, ι.base '' Set.range (n i) = ((P i).support : Set X) := fun i => by
    rw [← hn i, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hsub : ∀ Z : Set T, IsIrreducible Z → ∃ i, ι.base '' Z ⊆ ((P i).support : Set X) := by
    intro Z hZ
    have hZ' : IsIrreducible (ι.base '' Z) := hZ.image _ ι.base.hom.continuous.continuousOn
    have hcl := isIrreducible_iff_sUnion_isClosed.mp hZ'
    obtain ⟨W, hW, hZW⟩ := hcl (B.roundDown.support.image fun Q => (Q.support : Set X))
      (by
        intro W hW
        obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hW
        exact Q.idealSheaf.support.isClosed)
      (by
        rintro _ ⟨z, -, rfl⟩
        have : ι.base z ∈ Set.range ι.base := ⟨z, rfl⟩
        rw [hT] at this
        obtain ⟨_, ⟨Q, rfl⟩, hz⟩ := this
        obtain ⟨hQ, hz⟩ := Set.mem_iUnion.mp hz
        exact ⟨_, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩, hz⟩)
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨i, rfl⟩ := hPsurj Q hQ
    exact ⟨i, hZW⟩
  have hirr : ∀ i, IsIrreducible (Set.range (n i)) := fun i => by
    have hgen : (P i).genericPoint ∈ ι.base '' Set.range (n i) := by
      rw [himg i, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨η, -, hη⟩ := hgen
    have : Set.range (n i) = closure {η} := by
      apply (Set.image_injective.mpr hinj)
      rw [himg i, ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hη,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [this]
    exact isIrreducible_singleton.closure
  have hmax : ∀ i, Set.range (n i) ∈ irreducibleComponents T := fun i => by
    refine ⟨hirr i, fun Z hZ hiZ => ?_⟩
    obtain ⟨j, hj⟩ := hsub Z hZ
    have hij : ((P i).support : Set X) ⊆ (P j).support := by
      rw [← himg i]
      exact (Set.image_mono hiZ).trans hj
    have hgen : (P i).genericPoint ∈ ((P j).support : Set X) := by
      apply hij
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have hji := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hgen
    rw [hji, ← himg i] at hj
    exact (Set.image_subset_image_iff hinj).mp hj
  refine ⟨hmax, fun Z hZ => ?_⟩
  obtain ⟨i, hi⟩ := hsub Z hZ.1
  rw [← himg i] at hi
  have hZi : Z = Set.range (n i) :=
    ((Set.image_subset_image_iff hinj).mp hi).antisymm
      (hZ.2 (hirr i) ((Set.image_subset_image_iff hinj).mp hi))
  refine ⟨i, hZi.symm, fun i' hi' => hPinj ?_⟩
  apply primeDivisor_eq_of_support_eq
  rw [← himg i, ← himg i', hi', hZi]

end Floor

end MMP.Fourfold.SdltFloor
