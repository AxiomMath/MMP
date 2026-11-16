module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.DltStrataSncLocus
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStep
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC

/-!
# Adjunction to a stratum of a dlt pair

Let `(X, B)` be a rational dlt pair and `S` a boundary stratum, an irreducible component of a
nonempty intersection of distinct prime components of `⌊B⌋`. Then `S` is the final stratum of a
flag `X = S₀ ⊃ S₁ ⊃ ⋯ ⊃ S_k = S` along which iterated adjunction is defined, and for every such
flag the adjunction pair `(S, B_S)` on the final stratum, with `K_S + B_S = (K_X + B)|_S`, is
again a dlt pair. Finally the generic point `η` of `S` lies in the snc locus of `(X, B)`: it lies
outside every closed set `Z` witnessing that `(X, B)` is dlt (Kollár–Mori 2.37, 5.50), and `S` has
the expected codimension, `codim S = r` whenever `S` is an irreducible component of an
intersection of `r` distinct components of `⌊B⌋`.

The proof reduces to three facts about one adjunction step `(Y, B_Y) ⇝ (T, B_T)` from a dlt pair
onto a prime component `P` of `⌊B_Y⌋`: the pair `(T, B_T)` is dlt; the closed set witnessing
dltness of `(Y, B_Y)` restricts to one for `(T, B_T)`; and every irreducible subset of `T ∩ Q`, for
a second component `Q` of `⌊B_Y⌋`, lies in a prime divisor of `T` contained in `Q` and of
coefficient one in `B_T`. Dltness of the final pair of every flag is then an induction along the
flag, and the existence of a flag ending at `S`, as well as `η ∉ Z`, an induction on the number of
components cutting out `S`: the stratum `S ⊆ P` is again a stratum of `(T, B_T)`, cut out by fewer
components. The codimension count is read off a regular system of parameters at `η`.

## Main results

* `MMP.Fourfold.IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair`.

## Implementation notes

The identity `K_S + B_S = (K_X + B)|_S` is part of the data: each step of
`MMP.Fourfold.StratumAdjunctionData` requires `B_j` to be the different
`Diff_{S_j}(B_{j-1} - S_j)` (`MMP.Flips.IsDifferentDivisor`), which is the residue identity
`K_{S_j} + B_j = (K_{S_{j-1}} + B_{j-1})|_{S_j}`. The stratum `S ⊆ X` is identified with the
final scheme `T` of the flag through the image of the closed immersion `ι : T ⟶ X`. The
codimension of `S` is the coheight `Order.coheight η` of its generic point in the specialization
order, and "the generic point of `S` is in the snc locus" is stated against every witness `Z` of
the definition of dlt (`MMP.Intersection.IsDltPair`), so it does not depend on a choice of `Z`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori1998],
  2.37, 4.16, 5.50, 5.52
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

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
private theorem ord_algebraMap_eq_zero_of_isUnit {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (P : MMP.Mori.PrimeDivisor Y) {x : Y} (hx : x = P.genericPoint) {b : Y.presheaf.stalk x}
    (hb : IsUnit b) : Y.ord (algebraMap _ Y.functionField b) P.genericPoint = 0 := by
  subst hx
  exact P.ord_algebraMap_of_isUnit hb

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
    refine exists_algebraMap_eq_of_ord_nonneg P hf0 ?_
    have := P.ordForm_smul (sX := sX) hd hf0 hτ0
    rw [hf, hτ] at this
    omega
  set b₁ := X.presheaf.stalkSpecializes hspP a with hb₁
  have hb₁f : algebraMap _ X.functionField b₁ = f := by
    rw [hb₁, algebraMap_stalkSpecializes', haf]
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
  have hcg := componentGenericPoint_eq_genericPoint Q.component
  have h' : componentGenericPoint T Q.component ⤳ genericPoint T := specializes_of_eq hcg
  refine ⟨X.presheaf.stalkSpecializes (j.base.hom.map_specializes h') b₁, hb₁u.map _,
    fun E hE hEP => ?_, ?_⟩
  · rw [algebraMap_stalkSpecializes', hb₁f, ← E.ordForm_smul (sX := sX) hd hf0 hτ0, hf]
    exact hσE E hE hEP
  · rw [Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ h',
      MMP.CyclicChartDifferent.Aux.componentToFunctionField_stalkSpecializes T _ h',
      MMP.CyclicChartDifferent.Aux.algebraMap_stalk_genericPoint T]
    have := Q.ordForm_smul (sX := j ≫ sX) hdT hb0 hρ0
    rw [← hρσeq, hρ₁Q] at this
    rw [← this]

end ResidueLift

section Step

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}}
  {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {BY : QDivisor Y}

/-! ### A rational top form with a simple pole along a normal prime divisor -/

/-- The top exterior power of a linearly independent family is nonzero. -/
private theorem ιMulti_ne_zero_of_linearIndependent {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {n : ℕ} {v : Fin n → W} (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  classical
  let b := Module.Basis.span hv
  have hb : (fun i => ((b i : Submodule.span K (Set.range v)) : W)) = v := by
    funext i; simp [b, Module.Basis.span_apply]
  have hmap : exteriorPower.map n (Submodule.span K (Set.range v)).subtype
      (exteriorPower.ιMulti K n b) = exteriorPower.ιMulti K n v := by
    rw [exteriorPower.map_apply_ιMulti]
    exact congrArg _ hb
  intro h0
  have h1 : exteriorPower.ιMulti K n b = 0 := by
    apply exteriorPower.map_injective_field (n := n) (Submodule.injective_subtype _)
    rw [hmap, h0, map_zero]
  have h2 := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) h1
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero, b.det_self] at h2
  exact one_ne_zero h2

/-- A nonzero element of the maximal ideal of the local ring at the generic point of a prime
divisor. -/
private theorem exists_mem_maximalIdeal_ne_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X) (y : X)
    (hy : y = P.genericPoint) :
    ∃ t : X.presheaf.stalk y, t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ∧
      algebraMap (X.presheaf.stalk y) X.functionField t ≠ 0 := by
  subst hy
  have := P.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible P.localRing
  exact ⟨ϖ, hϖ.not_isUnit, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero⟩

/-- A normal prime divisor `S` of a normal variety `M` in characteristic zero carries a rational
top form `τ` with a simple pole along `S` and a nonzero Poincaré residue. -/
private theorem exists_isPoincareResidue_ne_zero {k : Type} [Field k] [CharZero k]
    {M S : Scheme.{0}} (sM : M ⟶ Spec (.of k))
    [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M] [CompactSpace M]
    [LocallyOfFiniteType sM] {n : ℕ}
    (hdim : topologicalKrullDim M = n + 1) (j : S ⟶ M) [IsClosedImmersion j] [IsIntegral S]
    [IsNormal S] [IsLocallyNoetherian S] [CompactSpace S] (hT : IsNormalVariety k (j ≫ sM))
    (P : MMP.Mori.PrimeDivisor M) (hP : Set.range j.base = (P.support : Set M)) :
    ∃ τ : RationalPluriForms sM (n + 1) 1, τ ≠ 0 ∧ P.ordForm τ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sM) n 1, IsPoincareResidue sM j n 1 τ ρ ∧ ρ ≠ 0 := by
  classical
  have : LocallyOfFiniteType (j ≫ sM) := hT.1.toLocallyOfFiniteType
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  let := functionFieldAlgebra sM
  let := functionFieldAlgebra (j ≫ sM)
  have hd : (Algebra.trdeg k M.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) (by rw [hdim]; norm_cast)
  have hdimT := topologicalKrullDim_eq_of_range_eq_support sM hdim j P hP
  -- coordinates on `S` with independent differentials
  have := essFiniteType_functionField (sX := j ≫ sM)
  have hfin : Module.finrank S.functionField Ω[S.functionField⁄k] = n :=
    (finrank_kaehlerDifferential_eq_trdeg k S.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdimT)
  have : FiniteDimensional S.functionField Ω[S.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k S.functionField).1
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent S.functionField (Set.range (KaehlerDifferential.D k S.functionField))
  have hbtop : Submodule.span S.functionField (Set.range ((↑) : b → Ω[S.functionField⁄k])) = ⊤ := by
    rw [Subtype.range_coe, hbspan, KaehlerDifferential.span_range_derivation]
  let bb := Module.Basis.mk hbli hbtop.ge
  have : Finite b := Module.Finite.finite_basis bb
  let : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by rw [← Module.finrank_eq_card_basis bb, hfin]
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose xb hxb using fun i : Fin n => hbsub (e i).2
  obtain ⟨x, hx⟩ : ∃ x : Fin n → M.presheaf.stalk (j (genericPoint S)),
      ∀ i, (j.stalkMap (genericPoint S)).hom (x i) = xb i :=
    ⟨fun i => (SurjectiveOnStalks.stalkMap_surjective j (genericPoint S) (xb i)).choose,
      fun i => (SurjectiveOnStalks.stalkMap_surjective j (genericPoint S) (xb i)).choose_spec⟩
  have hli : LinearIndependent S.functionField
      (fun i => KaehlerDifferential.D k S.functionField
        ((j.stalkMap (genericPoint S)).hom (x i))) := by
    have h := hbli.comp e e.injective
    convert h using 1
    funext i
    simp only [Function.comp_apply, hx, hxb]
  -- a uniformizing element along `S`
  obtain ⟨t, htm, ht0⟩ := exists_mem_maximalIdeal_ne_zero P (j (genericPoint S)) hjT
  let := stalkAlgebra sM (j (genericPoint S))
  let ν : MvPolynomial (Fin (n + 1)) k →ₐ[k] M.presheaf.stalk (j (genericPoint S)) :=
    MvPolynomial.aeval (Fin.cons t x)
  have hν0 : ν (MvPolynomial.X 0) = t := by simp [ν]
  have hνs : ∀ i : Fin n, ν (MvPolynomial.X i.succ) = x i := fun i => by simp [ν]
  have hF : (algebraMap _ M.functionField t)⁻¹ *
      algebraMap _ M.functionField (ν (MvPolynomial.X 0)) =
      algebraMap _ M.functionField (1 : M.presheaf.stalk (j (genericPoint S))) := by
    rw [hν0, inv_mul_cancel₀ ht0, map_one]
  obtain ⟨c, hc, hres, hord⟩ := exists_isPoincareResidue_smul_tprod_ιMulti sM hd j P hjT ν
    (by rw [hν0]; exact htm) (fun h => ht0 (by rw [← hν0, h, map_zero]))
    (by simpa only [hνs] using hli) hF
  refine ⟨_, fun h0 => ?_, hord isUnit_one, _, hres, ?_⟩
  · have := hord isUnit_one
    rw [h0, PrimeDivisor.ordForm_zero] at this
    exact absurd this (by norm_num)
  · rw [map_one, mul_one]
    have : CharZero S.functionField :=
      charZero_of_injective_algebraMap (algebraMap k S.functionField).injective
    refine smul_ne_zero (Nat.cast_ne_zero.mpr hc.ne') ?_
    intro h0
    have h1 := congrArg (PiTensorProduct.subsingletonEquiv (R := S.functionField)
      (s := fun _ : Fin 1 => ⋀[S.functionField]^n Ω[S.functionField⁄k]) 0) h0
    rw [PiTensorProduct.subsingletonEquiv_apply_tprod] at h1
    exact ιMulti_ne_zero_of_linearIndependent (by simpa only [hνs] using hli)
      (h1.trans (LinearEquiv.map_zero _))

/-! ### Log canonicity by forward adjunction -/

/-- A scheme carrying a prime divisor, locally of finite type over a field, has dimension at least
one: a prime divisor of an `n`-dimensional variety has dimension `n - 1`. -/
private theorem exists_eq_add_one_of_primeDivisor {k : Type} [Field k] {X : Scheme.{0}}
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

/-- The pull-back predicate depends only on the divisors, not on the proof of `(∗)`. -/
private theorem isPullback_congr {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} {D D' : QDivisor Y}
    {hD : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ D.supp} {R R' : QDivisor X}
    (h : D.IsPullback f hD R) (e : D = D') (e' : R = R') : D'.IsPullback f (e ▸ hD) R' := by
  subst e e'
  exact h

/-- Removing a component `P` of coefficient one from an effective boundary leaves an effective
boundary. -/
private theorem sub_single_nonneg {Y : Scheme.{0}} {BY : QDivisor Y} (hB0 : 0 ≤ BY)
    {P : MMP.Mori.PrimeDivisor Y} (hBP : BY.coeff P = 1) : 0 ≤ BY - Finsupp.single P 1 :=
  fun Q => by
    rcases eq_or_ne P Q with rfl | hQP
    · change (0 : ℚ) ≤ (BY - Finsupp.single P 1).coeff P
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
    · simpa [Finsupp.single_apply, hQP] using hB0 Q

/-- **The adjunction formula along a residue.** For one adjunction step `(Y, B_Y) ⇝ (T, B_T)`
onto `P`, there is a rational top form `τ` on `Y` with a simple pole along `P` and a nonzero
Poincaré residue `ρ` such that `div τ + B_Y`, written `div τ + P + (B_Y - P)`, is `ℚ`-Cartier and
restricts to `T` as `div ρ + B_T`. -/
private theorem exists_isPoincareResidue_isPullback {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T}
    (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace Y] [CompactSpace T] [LocallyOfFiniteType sY] [LocallyOfFiniteType (j ≫ sY)]
    (hXv : IsNormalVariety k sY) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY (n + 1))
    (hQ : (Divisor.toQDivisor K + BY).IsQCartier) {P : MMP.Mori.PrimeDivisor Y}
    (hP : Set.range j.base = (P.support : Set Y)) :
    ∃ τ : RationalPluriForms sY (n + 1) 1, τ ≠ 0 ∧ P.ordForm τ = -1 ∧
      ∃ ρ : RationalPluriForms (j ≫ sY) n 1, IsPoincareResidue sY j n 1 τ ρ ∧ ρ ≠ 0 ∧
        (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
          (BY - Finsupp.single P 1)).IsQCartier ∧
        ∃ hgen : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉
            (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
              (BY - Finsupp.single P 1)).supp,
          (Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 +
            (BY - Finsupp.single P 1)).IsPullback j hgen
            (Divisor.toQDivisor (divisorOfForm ρ) + BT) := by
  obtain ⟨hTv, -, -, -, hci, -⟩ := id h
  have hdim : topologicalKrullDim Y = n + 1 := by rw [hK.topologicalKrullDim_eq]; push_cast; rfl
  obtain ⟨τ, hτ0, hτP, ρ, hρ, hρ0⟩ := exists_isPoincareResidue_ne_zero sY hdim j hTv P hP
  have hlin := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hXv hK hτ0
  rw [one_smul] at hlin
  have hDq : (Divisor.toQDivisor (divisorOfForm τ) + BY).IsQCartier :=
    hQ.add_of_linearlyEquivalent hlin.symm
  obtain ⟨hgen, hpb⟩ :=
    h.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hP τ hτ0 hτP ρ hρ hDq
  have e : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + (BY - Finsupp.single P 1) =
      Divisor.toQDivisor (divisorOfForm τ) + BY := by abel
  exact ⟨τ, hτ0, hτP, ρ, hρ, hρ0, by rw [e]; exact hDq, by rw [e]; exact hgen,
    isPullback_congr hpb e.symm rfl⟩

/-- **Forward adjunction for one adjunction step.** For one adjunction step `(Y, B_Y) ⇝ (T, B_T)`
from a pair with `0 ≤ B_Y ≤ 1` onto a prime divisor `P`, `(T, B_T)` is a pair, and every divisor
`F` over `T` has an exceptional divisor `E` over `Y` with the same centre and the same
discrepancy: `a(F, T, B_T) = a(E, Y, B_Y)`. -/
private theorem isPair_and_forall_exists_isExceptional {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hY : MMP.Mori.IsPair sY BY) (hB0 : 0 ≤ BY)
    (hB1 : ∀ P, BY.coeff P ≤ 1) {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T}
    (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] :
    MMP.Mori.IsPair (j ≫ sY) BT ∧ (∀ Q, 0 ≤ BT.coeff Q) ∧
      ∃ (n : ℕ) (K : Divisor Y) (KT : Divisor T), K.IsCanonicalDivisor sY (n + 1) ∧
        KT.IsCanonicalDivisor (j ≫ sY) n ∧ (Divisor.toQDivisor K + BY).IsQCartier ∧
        (Divisor.toQDivisor KT + BT).IsQCartier ∧
        ∀ F : DivisorOver k (j ≫ sY), ∃ E : DivisorOver k sY, E.IsExceptional ∧
          j.base (F.f.base F.E.genericPoint) = E.f.base E.E.genericPoint ∧
          ∀ a : ℚ, IsDiscrepancy (j ≫ sY) n KT BT F a ↔ IsDiscrepancy sY (n + 1) K BY E a := by
  classical
  obtain ⟨hTv, P, hP1, hP, hci, -⟩ := id h
  have hXv : IsNormalVariety k sY := hY.1
  have : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  have : CompactSpace Y := haveI := hXv.1; QuasiCompact.compactSpace_of_compactSpace sY
  have : LocallyOfFiniteType (j ≫ sY) := hTv.1.toLocallyOfFiniteType
  have : CompactSpace T := haveI := hTv.1; QuasiCompact.compactSpace_of_compactSpace (j ≫ sY)
  obtain ⟨N, K, hK, hQ⟩ := hY.2
  obtain ⟨n, rfl⟩ := exists_eq_add_one_of_primeDivisor sY hK.topologicalKrullDim_eq P
  have hdim : topologicalKrullDim Y = n + 1 := by rw [hK.topologicalKrullDim_eq]; push_cast; rfl
  have hdimT := topologicalKrullDim_eq_of_range_eq_support sY hdim j P hP
  have hBP : BY.coeff P = 1 := le_antisymm (hB1 P) hP1
  -- a form with a simple pole along `P` and its residue
  obtain ⟨τ, hτ0, hτP, ρ, hρ, hρ0, hDq', hgen, hpb⟩ :=
    exists_isPoincareResidue_isPullback h hXv hK hQ hP
  -- `B_Y = P + B` with `B ≥ 0` not containing `P`
  set B : QDivisor Y := BY - Finsupp.single P 1 with hBdef
  have hBY : BY = Finsupp.single P 1 + B := by rw [hBdef]; abel
  have hBP0 : B.coeff P = 0 := by
    rw [hBdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
  have hB : 0 ≤ B := sub_single_nonneg hB0 hBP
  -- local generators of a Cartier multiple and their residues
  obtain ⟨M₀, hM₀, DM, hDM, hDMc⟩ := hDq'.exists_pos
  obtain ⟨M', rfl⟩ : ∃ M', M₀ = M' + 1 := ⟨M₀ - 1, by omega⟩
  have hgens := MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sY hdim j hTv
    hdimT P hP B τ hτ0 ρ hρ hρ0 BT hgen hpb M' DM hDM hDMc
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor (j ≫ sY) hTv hdimT
  have hCart : (((M' + 1 : ℕ) : ℤ) • (Divisor.toQDivisor KT + BT)).IsCartierDivisor :=
    isCartierDivisor_of_forall_generatesOn hTv hKT fun w => by
      obtain ⟨U, hU, -, -, ρ', -, hρ'⟩ := hgens w
      exact ⟨j ⁻¹ᵁ U, hU, ρ', hρ'⟩
  have hBT0 : ∀ Q, 0 ≤ BT.coeff Q := fun Q =>
    coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero sY hXv hdim j hTv P hP
      B (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hB) hBP0 τ hτ0 hτP ρ hρ hDq' BT hgen hpb Q
  refine ⟨⟨hTv, n, KT, hKT, ⟨((M' + 1 : ℕ) : ℤ), by positivity, hCart⟩⟩, hBT0, n, K, KT, hK,
    hKT, hQ, ⟨((M' + 1 : ℕ) : ℤ), by positivity, hCart⟩, fun F => ?_⟩
  have hDK : ∃ m : ℕ, 0 < m ∧
      ((m : ℤ) • (Divisor.toQDivisor K + (Finsupp.single P 1 + B))).IsCartierDivisor := by
    rw [← hBY]; exact hQ.exists_pos
  obtain ⟨E, hE, hc, hiff⟩ := exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue sY hXv n
    K hK P j hTv hP KT hKT B hB hBP0 hDK BT ⟨M' + 1, by omega, hgens⟩ F
  exact ⟨E, hE, hc, fun a => by rw [hiff a, ← hBY]⟩

/-- A prime divisor `P` of a pair `(X, B)`, regarded as a divisor over `X`, has discrepancy
`-coeff_P B`. -/
private theorem isDiscrepancy_ofPrimeDivisor {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hQ : (Divisor.toQDivisor K + B).IsQCartier)
    (P : MMP.Mori.PrimeDivisor X) :
    IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hX P) (-B.coeff P) := by
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
  rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
  have hPV : (P.support ∩ (V : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hV⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  linear_combination -hτ.2 P hPV

/-- A prime divisor `P` of a pair `(X, B)`, regarded as a divisor over `X`, has log discrepancy
`1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} (hQ : (Divisor.toQDivisor K + B).IsQCartier)
    (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B)
      (DivisorOver.ofPrimeDivisor k hX P) (1 - B.coeff P) := by
  have := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy
    (isDiscrepancy_ofPrimeDivisor hX hK hQ P) (show IsProper (𝟙 X) from inferInstance)
  push_cast at this
  rwa [← sub_eq_add_neg] at this

/-- On a log canonical pair every coefficient of the boundary is at most one: the log
discrepancy of a prime divisor `P` is `1 - coeff_P`. -/
private theorem coeff_le_one_of_isLogCanonicalPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ≤ 1 := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, -, hlc⟩ := hB
  have h0 := hlc n _ _ (isLogDiscrepancy_ofPrimeDivisor hX hK hQ P)
  exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) ≤ 1)

/-- On a log canonical pair every discrepancy, of a divisor over `X` on any model, is `≥ -1`:
a proper model with the same valuation has log discrepancy `1 + a ≥ 0`. -/
private theorem neg_one_le_of_isLogCanonicalPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Δ : QDivisor X} (hlc : MMP.Intersection.IsLogCanonicalPair sX Δ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  have hX := hlc.1.1
  have : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.1 hK E.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hE
  have h1 := hlc.2.2 _ _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')

/-- On a dlt pair with bad set `Z`, every discrepancy of a divisor over `X` whose centre lies in
`Z` is `> -1`: a proper model with the same valuation has the same centre and log discrepancy
`1 + a > 0`. -/
private theorem neg_one_lt_of_isDltPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Δ : QDivisor X} (hP : MMP.Mori.IsPair sX Δ) {Z : TopologicalSpace.Closeds X}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (MMP.Mori.QDivisor.toRDivisor Δ) D a →
        0 < a)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {D : DivisorOver k sX} {a : ℚ}
    (hDZ : D.f D.E.genericPoint ∈ (Z : Set X)) (ha : IsDiscrepancy sX n K Δ D a) : -1 < a := by
  have hX := hP.1
  have : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hE
  have hEZ : (E.toDivisorOver.center : Set X) ⊆ Z := by
    rw [DivisorOver.center_eq_closure_genericPoint]
    refine (Z.isClosed.closure_subset_iff).mpr ?_
    rw [Set.singleton_subset_iff]
    exact hc ▸ hDZ
  have h1 := hpos n _ hEZ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) < a')

/-- The restriction to an open `U` of an exceptional divisor over `X` whose center meets `U` is
exceptional over `U`. -/
private theorem isExceptional_restrict {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {U : X.Opens} [Nonempty U] (D : DivisorOver k sX)
    (hD : D.IsExceptional) (hU : IsNormalVariety k (U.ι ≫ sX))
    (hY : IsNormalVariety k ((D.f ∣_ U) ≫ U.ι ≫ sX)) (hf : IsBirationalMorphism (D.f ∣_ U))
    (E' : MMP.Mori.PrimeDivisor (D.f ⁻¹ᵁ U).toScheme)
    (hE' : OpenWeilRestriction.primeDivisorMap (D.f ⁻¹ᵁ U).ι E' = D.E) :
    (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)).IsExceptional := by
  rw [DivisorOver.isExceptional_iff_two_le_coheight hU]
  rw [DivisorOver.isExceptional_iff_two_le_coheight hX] at hD
  change 2 ≤ Order.coheight ((D.f ∣_ U) E'.genericPoint)
  rw [← coheight_eq_of_isOpenImmersion U.ι]
  have : U.ι ((D.f ∣_ U) E'.genericPoint) = D.f D.E.genericPoint := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE']
    exact congrArg D.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm
  rwa [this]

/-- **The different vanishes off the other floor components on the snc locus.** For one adjunction
step `(Y, B_Y) ⇝ (T, B_T)` onto `P` and a smooth open `U ⊆ Y` on which `B_Y` is snc, a prime
divisor `Q` of `T` with `j(η_Q) ∈ U` lying on no component of `B_Y` other than `P` has
`coeff_Q B_T = 0`: forward adjunction gives an exceptional `E` over `Y` centred at `j(η_Q)` with
`a(E, Y, B_Y) = -coeff_Q B_T`, and near `j(η_Q)` the pair is `(U, P)`, whose discrepancy is `0`. -/
private theorem coeff_eq_zero_of_forall_mem_support {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hY : MMP.Mori.IsPair sY BY) (hB0 : 0 ≤ BY)
    (hB1 : ∀ P, BY.coeff P ≤ 1) {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T}
    (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {U : Y.Opens} (hU : MMP.Mori.IsSmoothScheme (U.ι ≫ sY))
    (hsnc : (BY.restrictOpen U).IsSNC (U.ι ≫ sY))
    (Q : MMP.Mori.PrimeDivisor T) (hQU : j Q.genericPoint ∈ U)
    (hQ : ∀ Γ : MMP.Mori.PrimeDivisor Y, BY.coeff Γ ≠ 0 → j Q.genericPoint ∈ Γ.support →
      Set.range j.base = (Γ.support : Set Y)) :
    BT.coeff Q = 0 := by
  classical
  obtain ⟨hTv, P, hP1, hP, hci, -⟩ := id h
  obtain ⟨hPT, hBT0, n, K, KT, hK, hKT, hKQ, hKTQ, hfw⟩ :=
    isPair_and_forall_exists_isExceptional hY hB0 hB1 h
  have hXv : IsNormalVariety k sY := hY.1
  have : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (j ≫ sY) := hTv.1.toLocallyOfFiniteType
  obtain ⟨n', rfl⟩ := exists_eq_add_one_of_primeDivisor (j ≫ sY) hKT.topologicalKrullDim_eq Q
  have hBP : BY.coeff P = 1 := le_antisymm (hB1 P) hP1
  refine le_antisymm ?_ (hBT0 Q)
  -- forward adjunction for the prime divisor `Q` of `T`
  obtain ⟨E, hE, hcen, hiff⟩ := hfw (DivisorOver.ofPrimeDivisor k hTv Q)
  have hEd := (hiff _).mp (isDiscrepancy_ofPrimeDivisor hTv hKT hKTQ Q)
  have hcenE : E.f E.E.genericPoint = j Q.genericPoint := hcen.symm
  -- an open `V ∋ j(η_Q)` inside `U` meeting no component of `B_Y - P`
  set V : Y.Opens := U ⊓ (BY - Finsupp.single P 1).supp.compl with hVdef
  have hyV : j Q.genericPoint ∈ V := by
    refine ⟨hQU, ?_⟩
    intro hmem
    obtain ⟨Γ, hΓ, hyΓ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    by_cases hΓP : Γ = P
    · subst hΓP
      apply hΓ
      rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
    · have hc : BY.coeff Γ ≠ 0 := by
        intro h0
        apply hΓ
        rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hΓP), h0,
          sub_zero]
      have h1 := hQ Γ hc hyΓ
      rw [hP] at h1
      have hmem : P.genericPoint ∈ (Γ.support : Set Y) := by
        rw [← h1, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
      exact hΓP (MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hmem)
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  have hYpw : IsPairWith sY (n' + 1 + 1) K BY := ⟨hXv, hK, hKQ⟩
  have hEV : ((E.center : Set Y) ∩ V).Nonempty := by
    refine ⟨j Q.genericPoint, ?_, hyV⟩
    rw [DivisorOver.center_eq_closure_genericPoint, hcenE]
    exact subset_closure rfl
  obtain ⟨hY', hf, E', hE', -, hiff'⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hYpw E V hEV
  have hpV := hYpw.restrictOpen V
  have hEx' := isExceptional_restrict hXv E hE hpV.1 hY' hf E' hE'
  have ha' := (hiff' _).mp hEd
  -- the pair `(V, B_Y|_V) = (V, P|_V)` has discrepancy `0`
  have : ∀ G : MMP.Mori.PrimeDivisor Y,
      LocallyOfFinitePresentation (G.idealSheaf.subschemeι ≫ sY) :=
    fun G => (LocallyOfFinitePresentation.iff_locallyOfFiniteType
      (f := G.idealSheaf.subschemeι ≫ sY)).mpr inferInstance
  have hVU : V ≤ U := inf_le_left
  have hsmV : MMP.Mori.IsSmoothScheme (V.ι ≫ sY) :=
    MMP.Mori.isSmoothScheme_ι_of_le_smoothLocus
      (hVU.trans (MMP.Mori.le_smoothLocus_of_isSmoothScheme_ι hU))
  have hsncV : (BY.restrictOpen V).IsSNC (V.ι ≫ sY) :=
    MMP.Threefold.Mori.OpenRestriction.isSNC_restrictOpen_of_cover sY (fun _ : Unit => U) V
      (fun x hx => ⟨(), hVU hx⟩) BY (fun _ => hsnc)
  set S := (BY.restrictOpen V).support with hSdef
  have hSP : ∀ G ∈ S, OpenWeilRestriction.primeDivisorMap V.ι G = P := by
    intro G hG
    by_contra hGP
    have hc : BY.coeff (OpenWeilRestriction.primeDivisorMap V.ι G) ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hG; exact this
    have hc' : (BY - Finsupp.single P 1).coeff (OpenWeilRestriction.primeDivisorMap V.ι G) ≠ 0 := by
      rwa [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hGP),
        sub_zero]
    have hmem : V.ι G.genericPoint ∈ ((BY - Finsupp.single P 1).supp : Set Y) := by
      refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨_, hc', ?_⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        OpenWeilRestriction.genericPoint_primeDivisorMap]
      exact subset_closure rfl
    have hGV := G.genericPoint.2
    exact hGV.2 hmem
  have hdisc := MMP.Mori.discrep_eq_of_isSNC (V.ι ≫ sY) hpV.1 hsmV (by omega) hpV.2.1 S le_rfl
    (hsncV.of_support_subset <| Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
      fun E hE => Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE))
    (fun G _ => hB1 _)
  have h0 : (0 : EReal) ≤ MMP.Mori.discrep (V.ι ≫ sY) (n' + 1 + 1) (K.restrictOpen V)
      (BY.restrictOpen V) := by
    rw [hdisc]
    refine le_inf (le_inf ?_ ?_) (by norm_num)
    · refine le_iInf₂ fun G hG => le_iInf₂ fun F hF => le_iInf₂ fun hGF _ => ?_
      exact absurd (OpenWeilRestriction.primeDivisorMap_injective V.ι
        ((hSP G hG).trans (hSP F hF).symm)) hGF
    · refine le_iInf₂ fun G _ => ?_
      have : (0 : ℚ) ≤ 1 - (BY.restrictOpen V).coeff G := sub_nonneg.mpr (hB1 _)
      exact_mod_cast (show ((0 : ℝ) : EReal) ≤ (((1 - (BY.restrictOpen V).coeff G : ℚ) : ℝ) :
        EReal) from EReal.coe_le_coe_iff.mpr (by exact_mod_cast this))
  have h1 := h0.trans (MMP.Mori.discrep_le hEx' ha')
  have h2 : (0 : ℝ) ≤ ((-BT.coeff Q : ℚ) : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℚ) ≤ -BT.coeff Q := by exact_mod_cast h2
  linarith
/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{0}} {R : Type*}
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
private theorem ker_eq_vanishingIdeal {A B : Scheme.{0}} (g : A ⟶ B) [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range g.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  simp only [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- A closed immersion from a reduced scheme onto a prime divisor `P` has kernel the ideal
of `P`. -/
private theorem ker_eq_idealSheaf {T Y : Scheme.{0}} [IsLocallyNoetherian Y] (j : T ⟶ Y)
    [IsClosedImmersion j] [IsReduced T] (P : MMP.Mori.PrimeDivisor Y)
    (hP : Set.range j.base = (P.support : Set Y)) : j.ker = P.idealSheaf := by
  rw [ker_eq_vanishingIdeal, ← MMP.Intersection.vanishingIdeal_support_idealSheaf P]
  congr 1
  apply TopologicalSpace.Closeds.ext
  rw [TopologicalSpace.Closeds.coe_closure, hP]
  exact P.idealSheaf.support.isClosed.closure_eq

/-- The kernel of the stalk map of a closed immersion at `y` is the stalk at `ι y` of its
kernel. -/
private theorem ker_stalkMap_eq_stalk_ker {S W : Scheme.{0}} (ι : S ⟶ W) [IsClosedImmersion ι]
    (y : S) : RingHom.ker (ι.stalkMap y).hom = IdealSheafData.stalk ι.ker (ι y) := by
  have key : ∀ (K : W.IdealSheafData) (t : S ⟶ K.subscheme) [IsIso t],
      RingHom.ker ((t ≫ K.subschemeι).stalkMap y).hom =
        IdealSheafData.stalk K ((t ≫ K.subschemeι) y) := by
    intro K t _
    have : IsIso (t.stalkMap y) :=
      (IsOpenImmersion.iff_isIso_stalkMap.1 (IsOpenImmersion.of_isIso t)).2 y
    rw [Scheme.Hom.stalkMap_comp]
    change RingHom.ker ((t.stalkMap y).hom.comp (K.subschemeι.stalkMap (t y)).hom) =
      IdealSheafData.stalk K (K.subschemeι (t y))
    rw [RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso (t.stalkMap y)).1]
    exact Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk K (t y)
  have e : ι.toImage ≫ ι.ker.subschemeι = ι := ι.toImage_imageι
  have := key ι.ker ι.toImage
  rwa [e] at this

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
    rw [hJdef, Finset.coe_singleton, Set.image_singleton]
    exact hker
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hq⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  let e : (W.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J : Set (Fin n)))) ≃+*
      S.presheaf.stalk y :=
    (Ideal.quotEquivOfEq (hZx.symm.trans (ker_stalkMap_eq_stalk_ker ι y).symm)).trans
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
  · intro i j hij
    have h2 := hc (congrArg Subtype.val (o.symm.injective hij))
    exact Subtype.ext (congrArg (fun t : {i // ι y ∈ (E i).support} => t.1) h2)

/-- In a domain, a nonzero prime contained in a prime of height one is equal to it. -/
private lemma eq_of_le_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] {I q : Ideal A}
    [I.IsPrime] [q.IsPrime] (hI : I ≠ ⊥) (hle : I ≤ q) (hq : q.height = 1) : I = q := by
  by_contra hne
  have : q.FiniteHeight := Ideal.finiteHeight_iff_lt.mpr (Or.inr (by rw [hq]; simp))
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle hne)
  rw [hq, Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hI h1

/-- Let `J` be an ideal sheaf contained in the ideal of a prime divisor `P`, and `y ∈ P` a point
at which `J` is cut out by a member of a regular system of parameters. Then `P` and `J` have the
same ideal at `y`: the generated ideal is a nonzero prime inside the height-one prime of `P`. -/
private lemma stalk_idealSheaf_eq_of_le {X : Scheme.{0}} [IsLocallyNoetherian X]
    (P : MMP.Mori.PrimeDivisor X) {J : X.IdealSheafData} (hle : J ≤ P.idealSheaf) {y : X}
    (hy : y ∈ P.support) {m : ℕ} {w : Fin m → X.presheaf.stalk y}
    (hw : IsRegularSystemOfParameters w) (j0 : Fin m)
    (hst : AlgebraicGeometry.IdealSheafData.stalk J y = Ideal.span {w j0}) :
    AlgebraicGeometry.IdealSheafData.stalk P.idealSheaf y =
      AlgebraicGeometry.IdealSheafData.stalk J y := by
  obtain ⟨q, -, hPq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P hy
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk y)
  have := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw j0
  rw [hPq, hst]
  refine (eq_of_le_of_height_eq_one ?_ ?_ hq1).symm
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hw j0
  · rw [← hst, ← hPq]
    exact MMP.Resolution.stalk_le_stalk_of_le hle y

/-- **The snc condition for the different at a point of the snc locus.** For one adjunction step
from a dlt-type pair whose boundary is snc on a smooth open `U`, at every point `x` of `T` with
`j x ∈ U` the components of `B_T` through `x` are distinct coordinate hyperplanes of `𝒪_{T,x}`:
each lies in some `Γ ∩ T`, `Γ ≠ P` a component of `B_Y` (`coeff_eq_zero_of_forall_mem_support`),
and `Γ ∩ T` is a coordinate hyperplane at `x` (`exists_coordinates_comap_of_stalk`). -/
private theorem sncStalk_of_isAdjunctionStep {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hY : MMP.Mori.IsPair sY BY) (hB0 : 0 ≤ BY)
    (hB1 : ∀ P, BY.coeff P ≤ 1) {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T}
    (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {U : Y.Opens} (hU : MMP.Mori.IsSmoothScheme (U.ι ≫ sY))
    (hsnc : (BY.restrictOpen U).IsSNC (U.ι ≫ sY)) (x : T) (hx : j x ∈ U) :
    MMP.Threefold.Mori.OpenRestriction.SNCStalk BT x := by
  classical
  obtain ⟨hTv, P, hP1, hP, hci, -⟩ := id h
  set y := j x with hydef
  obtain ⟨N, z, jjY, hz, hjY, hIY⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι BY ⟨y, hx⟩).mp (hsnc.2 ⟨y, hx⟩)
  have hPs : P ∈ BY.support := Finsupp.mem_support_iff.mpr (lt_of_lt_of_le one_pos hP1).ne'
  have hyP : y ∈ P.support := by rw [← hP]; exact ⟨x, rfl⟩
  set i₀ := jjY ⟨P, hPs, hyP⟩
  have hker : IdealSheafData.stalk j.ker (j x) = Ideal.span {z i₀} := by
    rw [ker_eq_idealSheaf j P hP]; exact hIY ⟨P, hPs, hyP⟩
  let E : {Γ : MMP.Mori.PrimeDivisor Y // Γ ∈ BY.support ∧ Γ ≠ P} → Y.IdealSheafData :=
    fun Γ => Γ.1.idealSheaf
  let c : {Γ // j x ∈ (E Γ).support} → Fin N := fun Γ => jjY ⟨Γ.1.1, Γ.1.2.1, Γ.2⟩
  have hc : Function.Injective c := fun _ _ hab =>
    have := congrArg Subtype.val (hjY hab)
    Subtype.ext (Subtype.ext this)
  have hc0 : ∀ Γ, c Γ ≠ i₀ := fun Γ hΓ => Γ.1.2.2 (congrArg Subtype.val (hjY hΓ))
  obtain ⟨m, w, c', hw, hc', hinj⟩ := exists_coordinates_comap_of_stalk j E x hz i₀ hker c hc hc0
    (fun Γ => hIY ⟨Γ.1.1, Γ.1.2.1, Γ.2⟩)
  -- every component of `B_T` through `x` lies in some `Γ ∩ T`
  have hex : ∀ Q : {Q : MMP.Mori.PrimeDivisor T // Q ∈ BT.support ∧ x ∈ Q.support},
      ∃ Γ : {Γ : MMP.Mori.PrimeDivisor Y // Γ ∈ BY.support ∧ Γ ≠ P},
        j Q.1.genericPoint ∈ Γ.1.support := by
    intro Q
    by_contra hne
    push Not at hne
    have hsp : Q.1.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact Q.2.2
    have hQU : j Q.1.genericPoint ∈ U :=
      (hsp.map j.base.hom.continuous).mem_open U.isOpen hx
    have h0 := coeff_eq_zero_of_forall_mem_support hY hB0 hB1 h hU hsnc Q.1 hQU
      (fun Γ hΓ hqΓ => by
        by_cases hΓP : Γ = P
        · rw [hΓP]; exact hP
        · exact absurd hqΓ (hne ⟨Γ, Finsupp.mem_support_iff.mpr hΓ, hΓP⟩))
    exact Finsupp.mem_support_iff.mp Q.2.1 h0
  choose Γf hΓf using hex
  have hmemc : ∀ Q : {Q : MMP.Mori.PrimeDivisor T // Q ∈ BT.support ∧ x ∈ Q.support},
      ∀ t ∈ Q.1.support, t ∈ ((E (Γf Q)).comap j).support := by
    intro Q t ht
    have hsp : Q.1.genericPoint ⤳ t := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact ht
    refine (MMP.Resolution.mem_support_comap_iff _ _ t).2 ?_
    exact (hsp.map j.base.hom.continuous).mem_closed (E (Γf Q)).support.isClosed (hΓf Q)
  have hkey : ∀ Q : {Q : MMP.Mori.PrimeDivisor T // Q ∈ BT.support ∧ x ∈ Q.support},
      IdealSheafData.stalk Q.1.idealSheaf x = Ideal.span {w (c' ⟨Γf Q, hmemc Q x Q.2.2⟩)} := by
    intro Q
    rw [← hc' ⟨Γf Q, hmemc Q x Q.2.2⟩]
    refine stalk_idealSheaf_eq_of_le Q.1 ?_ Q.2.2 hw (c' ⟨Γf Q, hmemc Q x Q.2.2⟩)
      (hc' ⟨Γf Q, hmemc Q x Q.2.2⟩)
    rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf Q.1]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun t ht => hmemc Q t ht
  refine ⟨m, w, fun Q => c' ⟨Γf Q, hmemc Q x Q.2.2⟩, hw, fun Q Q' hQQ => ?_, hkey⟩
  apply Subtype.ext
  apply MMP.Intersection.eq_of_stalk_idealSheaf_eq Q.2.2 Q'.2.2
  rw [hkey Q, hkey Q']
  exact congrArg (fun i => Ideal.span {w i}) hQQ

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
  -- the residue lift
  obtain ⟨b, hb, hbE, hbQ⟩ := exists_residue_lift sX hX hdim j hT P hP τ hτ0 hτ ρ hρ Q
  have hmemZ : ∀ Z : irreducibleComponents X, j η ∈ Z.1 := fun Z => by
    rw [(subsingleton_irreducibleComponents (X := X)).elim Z W]; exact mem_pointComponent _
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
  obtain ⟨Tu, hTu⟩ := exists_units_componentToFunctionField_eq ht0
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
          rw [componentGenericPoint_eq_genericPoint]
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
    let := (RationalFunctions.isField_stalk X W).toField
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
  rw [Scheme.ord_mul hc0 (pow_ne_zero _ ht0'), ord_pow' ht0',
    Scheme.ord_mul (pow_ne_zero _ hb0) ha0, ord_pow' hb0] at hord
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
private theorem ord_algebraMap_eq_ite_of_stalk_eq_span {Y : Scheme.{0}} [IsIntegral Y]
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
    algebraMap_stalkSpecializes' Y hsp _
  have hmax : IsLocalRing.maximalIdeal (Y.presheaf.stalk E.genericPoint) =
      Ideal.map (Y.presheaf.stalkSpecializes hsp).hom (IdealSheafData.stalk E.idealSheaf y) := by
    rw [← MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes,
      MMP.Resolution.Aux.stalk_idealSheaf_genericPoint]
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hz0 : z i ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz i
  split_ifs with hEΓ
  · subst hEΓ
    rw [hΓ, Ideal.map_span, Set.image_singleton] at hmax
    have : IsDiscreteValuationRing (Y.presheaf.stalk E.genericPoint) :=
      E.isDiscreteValuationRing_localRing
    have htE0 : tE ≠ 0 := by
      intro h0
      have : algebraMap _ Y.functionField (z i) = 0 := by rw [← halg, h0, map_zero]
      exact hz0 (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
        (this.trans (map_zero _).symm))
    rw [← halg]
    exact ord_algebraMap_eq_one_of_irreducible E.coheight_genericPoint
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
      have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
      have : (IdealSheafData.stalk Γ.idealSheaf y).IsPrime := by rw [hqΓ]; exact qΓ.2
      have heq : IdealSheafData.stalk Γ.idealSheaf y = q.asIdeal := by
        refine eq_of_le_of_height_eq_one ?_ hle hqh
        rw [hΓ, Ne, Ideal.span_singleton_eq_bot]; exact hz0
      exact hEΓ (MMP.Intersection.eq_of_stalk_idealSheaf_eq hE hΓy (hq.trans heq.symm))
    have hu : IsUnit tE := by
      by_contra hnu
      exact hnot ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    rw [← halg]
    exact ord_algebraMap_eq_zero_of_isUnit E rfl hu

/-- **The different on the snc locus.** For one adjunction step from a dlt pair with bad set `Z`,
`T ∖ j⁻¹(Z)` is smooth and `B_T` has simple normal crossing support there. -/
private theorem isSmoothScheme_and_isSNC_of_isAdjunctionStep {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {BY : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY BY)
    {Z : TopologicalSpace.Closeds Y}
    (hsm : MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY))
    (hsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : Y.Opens)) BY))
    {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T}
    (h : IsAdjunctionStep sY BY j BT) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] :
    MMP.Mori.IsSmoothScheme
        (Scheme.Opens.ι ((Z.preimage j.continuous).compl : T.Opens) ≫ j ≫ sY) ∧
      DivisorWithCoeffs.IsSNC
        (Scheme.Opens.ι ((Z.preimage j.continuous).compl : T.Opens) ≫ j ≫ sY)
        (MMP.Mori.inverseTransformDivisor
          (Scheme.Opens.ι ((Z.preimage j.continuous).compl : T.Opens)) BT) := by
  classical
  obtain ⟨⟨hpair, hB0, -⟩, hB1, -⟩ := id hB
  have hTv : IsNormalVariety k (j ≫ sY) := h.1
  have : LocallyOfFiniteType (j ≫ sY) := hTv.1.toLocallyOfFiniteType
  set U : Y.Opens := Z.compl
  set V : T.Opens := (Z.preimage j.continuous).compl
  rw [inverseTransformDivisor_ι_eq_restrictOpen] at hsnc ⊢
  have hVU : ∀ v : V.toScheme, j (V.ι v) ∈ U := fun v => v.2
  have hst : ∀ v : V.toScheme, MMP.Threefold.Mori.OpenRestriction.SNCStalk
      (BT.restrictOpen V) v := fun v =>
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff V.ι BT v).mpr
      (sncStalk_of_isAdjunctionStep hpair hB0 hB1 h hsm hsnc (V.ι v) (hVU v))
  have : LocallyOfFiniteType (V.ι ≫ j ≫ sY) := inferInstance
  have : LocallyOfFinitePresentation (V.ι ≫ j ≫ sY) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := V.ι ≫ j ≫ sY)).mpr inferInstance
  refine ⟨?_, ?_, hst⟩
  · rw [isSmoothScheme_iff, MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
    intro v
    obtain ⟨n, z, -, hz, -⟩ := hst v
    exact isRegularLocalRing_of_isRegularSystemOfParameters hz
  · intro E' hE'
    refine MMP.Resolution.isSmoothScheme_subscheme_of_stalk_eq_span_parameter (V.ι ≫ j ≫ sY)
      E'.idealSheaf fun v hv => ?_
    obtain ⟨n, z, jj, hz, -, hI⟩ := hst v
    exact ⟨n, z, jj ⟨E', hE', hv⟩, hz, hI ⟨E', hE', hv⟩⟩

/-- **The bad set of a dlt pair restricts along an adjunction step.** For one adjunction step
`(Y, B_Y) ⇝ (T, B_T)` from a dlt pair and any closed `Z ⊆ Y` witnessing that `(Y, B_Y)` is dlt,
the preimage `j⁻¹(Z)` witnesses that `(T, B_T)` is dlt. -/
private theorem isDltWitness_preimage (hB : MMP.Intersection.IsDltPair sY BY)
    {Z : TopologicalSpace.Closeds Y}
    (hsm : MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY))
    (hsnc : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : Y.Opens)) BY))
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sY), (D.center : Set Y) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sY n (MMP.Mori.QDivisor.toRDivisor BY) D a →
        0 < a)
    {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] :
    MMP.Mori.IsSmoothScheme
        (Scheme.Opens.ι ((Z.preimage j.continuous).compl : T.Opens) ≫ j ≫ sY) ∧
      DivisorWithCoeffs.IsSNC
        (Scheme.Opens.ι ((Z.preimage j.continuous).compl : T.Opens) ≫ j ≫ sY)
        (MMP.Mori.inverseTransformDivisor
          (Scheme.Opens.ι ((Z.preimage j.continuous).compl : T.Opens)) BT) ∧
      ∀ (n : ℕ) (F : DivisorOver k (j ≫ sY)), (F.center : Set T) ⊆ Z.preimage j.continuous →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy (j ≫ sY) n
          (MMP.Mori.QDivisor.toRDivisor BT) F a → 0 < a := by
  obtain ⟨⟨hpair, hB0, -⟩, hB1, -⟩ := id hB
  obtain ⟨hPT, -, n, K, KT, hK, hKT, -, -, hfw⟩ :=
    isPair_and_forall_exists_isExceptional hpair hB0 hB1 h
  obtain ⟨hsmT, hsncT⟩ := isSmoothScheme_and_isSNC_of_isAdjunctionStep hB hsm hsnc h
  refine ⟨hsmT, hsncT, fun n' F hFZ a ha => ?_⟩
  obtain ⟨c, hc, rfl⟩ := MMP.Threefold.Bridges.exists_isDiscrepancy_of_isLogDiscrepancy hPT hKT ha
  obtain ⟨E, -, hcen, hiff⟩ := hfw F
  have hFmem : F.f F.E.genericPoint ∈ (F.center : Set T) := by
    rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl
  have hEZ : E.f E.E.genericPoint ∈ (Z : Set Y) := by
    rw [← hcen]; exact hFZ hFmem
  have h1 := neg_one_lt_of_isDltPair hpair hpos hK hEZ ((hiff c).mp hc)
  have h2 : (-1 : ℝ) < c := by exact_mod_cast h1
  linarith

/-- **Dlt adjunction to a floor component.** One adjunction step from a dlt pair gives a dlt
pair. -/
private theorem isDltPair_of_isAdjunctionStep (hB : MMP.Intersection.IsDltPair sY BY)
    {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] :
    MMP.Intersection.IsDltPair (j ≫ sY) BT := by
  obtain ⟨⟨hpair, hB0, hlc⟩, hB1, Z, hsm, hsnc, hpos⟩ := id hB
  obtain ⟨hPT, hBT0, n, K, KT, hK, hKT, -, -, hfw⟩ :=
    isPair_and_forall_exists_isExceptional hpair hB0 hB1 h
  have hlcT : MMP.Intersection.IsLogCanonicalPair (j ≫ sY) BT := by
    refine ⟨hPT, hBT0, fun n' F a ha => ?_⟩
    obtain ⟨c, hc, rfl⟩ := MMP.Threefold.Bridges.exists_isDiscrepancy_of_isLogDiscrepancy hPT hKT ha
    obtain ⟨E, -, -, hiff⟩ := hfw F
    have h1 := neg_one_le_of_isLogCanonicalPair ⟨hpair, hB0, hlc⟩ hK ((hiff c).mp hc)
    have h2 : (-1 : ℝ) ≤ c := by exact_mod_cast h1
    linarith
  obtain ⟨hsmT, hsncT, hposT⟩ := isDltWitness_preimage hB hsm hsnc hpos h
  exact ⟨hlcT, coeff_le_one_of_isLogCanonicalPair hlcT, Z.preimage j.continuous, hsmT, hsncT,
    hposT⟩

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
private theorem exists_primeDivisor_of_isAdjunctionStep (hB : MMP.Intersection.IsDltPair sY BY)
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
  have : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  have : CompactSpace Y := haveI := hXv.1; QuasiCompact.compactSpace_of_compactSpace sY
  have : LocallyOfFiniteType (j ≫ sY) := hTv.1.toLocallyOfFiniteType
  have : CompactSpace T := haveI := hTv.1; QuasiCompact.compactSpace_of_compactSpace (j ≫ sY)
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
  have hsupp : ∀ G : MMP.Mori.PrimeDivisor Y, 1 ≤ BY.coeff G → G ∈ BY.support := fun G hG =>
    Finsupp.mem_support_iff.mpr (lt_of_lt_of_le one_pos hG).ne'
  have hPs := hsupp P' hP'1
  have hQs := hsupp Q hQ
  have hyP : j x ∈ P'.support := by rw [← hP]; exact ⟨x, rfl⟩
  have hyQ : j x ∈ Q.support := (hcPQ (subset_closure rfl)).2
  set i₀ := jjY ⟨P', hPs, hyP⟩
  have hker : IdealSheafData.stalk j.ker (j x) = Ideal.span {z i₀} := by
    rw [ker_eq_idealSheaf j P' hP]; exact hIY ⟨P', hPs, hyP⟩
  let E : {Γ : MMP.Mori.PrimeDivisor Y // Γ ∈ BY.support ∧ Γ ≠ P'} → Y.IdealSheafData :=
    fun Γ => Γ.1.idealSheaf
  let cc : {Γ // j x ∈ (E Γ).support} → Fin N := fun Γ => jjY ⟨Γ.1.1, Γ.1.2.1, Γ.2⟩
  have hc : Function.Injective cc := fun _ _ hab =>
    have := congrArg Subtype.val (hjY hab)
    Subtype.ext (Subtype.ext this)
  have hc0 : ∀ Γ, cc Γ ≠ i₀ := fun Γ hΓ => Γ.1.2.2 (congrArg Subtype.val (hjY hΓ))
  obtain ⟨m, w, c', hw, hc', -⟩ := exists_coordinates_comap_of_stalk j E x hz i₀ hker cc hc hc0
    (fun Γ => hIY ⟨Γ.1.1, Γ.1.2.1, Γ.2⟩)
  set QL : {Γ : MMP.Mori.PrimeDivisor Y // Γ ∈ BY.support ∧ Γ ≠ P'} := ⟨Q, hQs, hQP⟩
  have hxQ : x ∈ ((E QL).comap j).support := (MMP.Resolution.mem_support_comap_iff _ _ x).2 hyQ
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
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
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz2'
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
    rw [ker_stalkMap_eq_stalk_ker, ker_eq_idealSheaf j P' hP] at hmem
    obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support P' hy'P
    obtain ⟨qQ, -, hqQ, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support Q hy'Q
    have := IsRegularLocalRing.isDomain (Y.presheaf.stalk (j Q'.genericPoint))
    have : (IdealSheafData.stalk Q.idealSheaf (j Q'.genericPoint)).IsPrime := by
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
  obtain ⟨τ, hτ0, hτP, ρ, hρ, -, hDq', hgen, hpb⟩ :=
    exists_isPoincareResidue_isPullback h hXv hK hQc hP
  set B : QDivisor Y := BY - Finsupp.single P' 1 with hBdef
  have hBP0 : B.coeff P' = 0 := by
    rw [hBdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, hBP, sub_self]
  have hBQ : B.coeff Q = BY.coeff Q := by
    rw [hBdef, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQP),
      sub_zero]
  have hlow := one_le_coeff_isPullback_sub_divisorOfForm sY hXv hdim j hTv P' hP B
    (DivisorWithCoeffs.isEffective_iff_nonneg.mpr (sub_single_nonneg hB0 hBP)) hBP0 τ hτ0 hτP ρ hρ
    hDq' hgen _ hpb Q' Q hQP (hBQ ▸ hQ) t ht0 (by simp [hord Q hy'Q])
    (fun G hG hGQ => by simp [hord G hG, hGQ]) htQ'
  rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at hlow
  linarith

open Classical in
/-- **A stratum of a dlt pair is a stratum of an adjunction step.** Let `S` be an irreducible
component of `⋂_{Q ∈ J} Q` for floor components `Q` of a dlt pair `(Y, B_Y)`, and `P ∈ J` with an
adjunction step `(Y, B_Y) ⇝ (T, B_T)` onto `P`. If `J ≠ {P}`, then `j⁻¹(S)` is an irreducible
component of `⋂_{Q' ∈ J'} Q'` for a nonempty set `J'` of fewer floor components of `(T, B_T)`. -/
private theorem exists_finset_maximal_preimage (hB : MMP.Intersection.IsDltPair sY BY)
    {T : Scheme.{0}} {j : T ⟶ Y} {BT : QDivisor T} (hj : IsAdjunctionStep sY BY j BT)
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {P : MMP.Mori.PrimeDivisor Y} (hjP : Set.range j.base = (P.support : Set Y))
    {J : Finset (MMP.Mori.PrimeDivisor Y)} (hPJ : P ∈ J) (h1 : ∀ P ∈ J, 1 ≤ BY.coeff P)
    (hJP : ¬ J.erase P = ∅) {S : Set Y}
    (hS : Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ ⋂ P ∈ J, (P.support : Set Y)) S) :
    ∃ J' : Finset (MMP.Mori.PrimeDivisor T), J'.card < J.card ∧ J'.Nonempty ∧
      (∀ Q' ∈ J', 1 ≤ BT.coeff Q') ∧
      Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ ⋂ Q' ∈ J', (Q'.support : Set T))
        (j.base ⁻¹' S) := by
  classical
  obtain ⟨-, -, -, -, hci, -⟩ := id hj
  have hemb := j.isClosedEmbedding
  have hSP : S ⊆ (P.support : Set Y) :=
    hS.1.2.trans (Set.biInter_subset_of_mem hPJ)
  have hSj : S ⊆ Set.range j.base := hjP ▸ hSP
  have himS : j.base '' (j.base ⁻¹' S) = S := Set.image_preimage_eq_of_subset hSj
  have hirr : IsIrreducible (j.base ⁻¹' S) :=
    MMP.Flips.isIrreducible_of_isInducing_image hemb.isInducing (by rw [himS]; exact hS.1.1)
  -- choose, for every other component `Q`, a component of `T ∩ Q` containing `S`
  have hQ' : ∀ Q ∈ J.erase P, ∃ Q' : MMP.Mori.PrimeDivisor T,
      j.base ⁻¹' S ⊆ (Q'.support : Set T) ∧
      (Q'.support : Set T) ⊆ j.base ⁻¹' (Q.support : Set Y) ∧ 1 ≤ BT.coeff Q' := by
    intro Q hQ
    obtain ⟨hQP, hQJ⟩ := Finset.mem_erase.mp hQ
    refine exists_primeDivisor_of_isAdjunctionStep hB hj hjP hQP (h1 Q hQJ) hirr ?_
    exact Set.preimage_mono (hS.1.2.trans (Set.biInter_subset_of_mem hQJ))
  choose f hf using hQ'
  set J' := (J.erase P).attach.image fun Q => f Q.1 Q.2
  have hJ'ne : J'.Nonempty := by
    rw [Finset.image_nonempty, Finset.attach_nonempty_iff, Finset.nonempty_iff_ne_empty]
    exact hJP
  have hJ'1 : ∀ Q' ∈ J', 1 ≤ BT.coeff Q' := by
    intro Q' hQ'
    obtain ⟨⟨Q, hQ⟩, -, rfl⟩ := Finset.mem_image.mp hQ'
    exact (hf Q hQ).2.2
  have hS'sub : j.base ⁻¹' S ⊆ ⋂ Q' ∈ J', (Q'.support : Set T) := by
    refine Set.subset_iInter₂ fun Q' hQ' => ?_
    obtain ⟨⟨Q, hQ⟩, -, rfl⟩ := Finset.mem_image.mp hQ'
    exact (hf Q hQ).1
  have hS' : Maximal (fun W : Set T => IsIrreducible W ∧
      W ⊆ ⋂ Q' ∈ J', (Q'.support : Set T)) (j.base ⁻¹' S) := by
    refine ⟨⟨hirr, hS'sub⟩, fun W ⟨hW, hWJ⟩ hSW => ?_⟩
    have himW : j.base '' W ⊆ ⋂ Q ∈ J, (Q.support : Set Y) := by
      refine Set.subset_iInter₂ fun Q hQ => ?_
      by_cases hQP : Q = P
      · subst hQP
        rw [← hjP]; exact Set.image_subset_range _ _
      · have hQe : Q ∈ J.erase P := Finset.mem_erase.mpr ⟨hQP, hQ⟩
        have := hWJ.trans (Set.biInter_subset_of_mem
          (Finset.mem_image_of_mem (fun Q => f Q.1 Q.2) (Finset.mem_attach _ ⟨Q, hQe⟩)))
        rintro _ ⟨x, hx, rfl⟩
        exact (hf Q hQe).2.1 (this hx)
    have hSW' : S ≤ j.base '' W := by
      rw [← himS]; exact Set.image_mono hSW
    have := hS.2 ⟨hW.image _ hemb.continuous.continuousOn, himW⟩ hSW'
    intro x hx
    exact this ⟨x, hx, rfl⟩
  exact ⟨J', by
    have := Finset.card_erase_of_mem hPJ
    have := Finset.card_pos.mpr ⟨P, hPJ⟩
    have h1' : J'.card ≤ (J.erase P).card :=
      Finset.card_image_le.trans (Finset.card_attach).le
    omega, hJ'ne, hJ'1, hS'⟩

end Step

section Flag

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

section

variable {X : Scheme.{0}}
  {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}

/-- The final pair of every flag of iterated adjunction from a dlt pair is dlt. -/
private theorem isDltPair_of_stratumAdjunctionData (hB : MMP.Intersection.IsDltPair sX B)
    {T : Scheme.{0}} {ι : T ⟶ X} {BT : QDivisor T} (F : StratumAdjunctionData sX B ι BT) :
    haveI : IsIntegral T := F.isNormalVariety.1.toIsIntegral
    haveI : IsNormal T := F.isNormalVariety.2
    haveI : IsLocallyNoetherian T := by
      have := F.isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
    MMP.Intersection.IsDltPair (ι ≫ sX) BT := by
  induction F with
  | refl h =>
    simp only [Category.id_comp]
    exact hB
  | step F j BT h ih =>
    rename_i S T ι BS
    have : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    have : IsNormal S := F.isNormalVariety.2
    have : IsLocallyNoetherian S := by
      have := F.isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
    have : IsIntegral T := (F.step j BT h).isNormalVariety.1.toIsIntegral
    have : IsNormal T := (F.step j BT h).isNormalVariety.2
    have : IsLocallyNoetherian T := by
      have := (F.step j BT h).isNormalVariety.1
      exact LocallyOfFiniteType.isLocallyNoetherian ((j ≫ ι) ≫ sX)
    have := isDltPair_of_isAdjunctionStep ih h
    simp only [Category.assoc]
    exact this

end

omit [IsAlgClosed k] [CharZero k] in
/-- Prefixing a flag of iterated adjunction from `(T, B_T)` by one adjunction step
`(Y, B_Y) ⇝ (T, B_T)` gives a flag from `(Y, B_Y)`. -/
private theorem isStratumAdjunctionPair_comp {Y T : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian T] [IsNormal T] {BY : QDivisor Y}
    (hY : MMP.Mori.IsPair sY BY) {j : T ⟶ Y} {BT : QDivisor T} (h : IsAdjunctionStep sY BY j BT)
    {S : Scheme.{0}} {ι : S ⟶ T} {BS : QDivisor S} (F : StratumAdjunctionData (j ≫ sY) BT ι BS) :
    IsStratumAdjunctionPair sY BY (ι ≫ j) BS := by
  induction F with
  | refl _ =>
    have h' : IsAdjunctionStep (𝟙 Y ≫ sY) BY j BT := by rwa [Category.id_comp]
    have := IsStratumAdjunctionPair.step sY (isStratumAdjunctionPair_refl sY hY) j h'
    rwa [Category.comp_id, ← Category.id_comp j] at this
  | @step S₁ T₁ ι₁ BS₁ F j' BS' h' ih =>
    have h'' : IsAdjunctionStep ((ι₁ ≫ j) ≫ sY) BS₁ j' BS' := by rwa [Category.assoc]
    have := IsStratumAdjunctionPair.step sY ih j' h''
    rwa [← Category.assoc] at this

open Classical in
/-- A set maximal among the irreducible subsets of a single prime divisor `P` is `P` itself. -/
private theorem eq_support_of_maximal_of_erase_eq_empty {Y : Scheme.{0}}
    {J : Finset (MMP.Mori.PrimeDivisor Y)} {P : MMP.Mori.PrimeDivisor Y} (hPJ : P ∈ J)
    (hJP : J.erase P = ∅) {S : Set Y}
    (hS : Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ ⋂ P ∈ J, (P.support : Set Y)) S) :
    S = (P.support : Set Y) := by
  obtain rfl : J = {P} := by rw [← Finset.insert_erase hPJ, hJP]; rfl
  have hSP : S ⊆ (P.support : Set Y) := by simpa using hS.1.2
  refine le_antisymm hSP (hS.2 ⟨?_, by simp⟩ hSP)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isIrreducible_singleton.closure

/-- **Existence of a flag ending at a stratum**, by induction on the number of floor components
cutting out the stratum. -/
private theorem exists_isStratumAdjunctionPair_of_card_le (n : ℕ) :
    ∀ {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
      [IsNormal Y] {BY : QDivisor Y}, MMP.Intersection.IsDltPair sY BY →
      ∀ J : Finset (MMP.Mori.PrimeDivisor Y), J.card ≤ n → J.Nonempty →
      (∀ P ∈ J, 1 ≤ BY.coeff P) → ∀ S : Set Y,
      Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ ⋂ P ∈ J, (P.support : Set Y)) S →
      ∃ (T : Scheme.{0}) (ι : T ⟶ Y) (BT : QDivisor T),
        Set.range ι.base = S ∧ IsStratumAdjunctionPair sY BY ι BT := by
  classical
  induction n with
  | zero =>
    intro Y sY _ _ _ BY _ J hJ hne
    exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ n ih =>
    intro Y sY _ _ _ BY hB J hJ hne h1 S hS
    obtain ⟨P, hPJ⟩ := hne
    obtain ⟨T, j, BT, hjP, hj⟩ := exists_isAdjunctionStep_of_isDltPair hB P (h1 P hPJ)
    obtain ⟨hTv, -, -, -, hci, -⟩ := id hj
    have : IsIntegral T := hTv.1.toIsIntegral
    have : IsNormal T := hTv.2
    have : IsLocallyNoetherian T := by
      have := hTv.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ sY)
    have hTB := isDltPair_of_isAdjunctionStep hB hj
    by_cases hJP : J.erase P = ∅
    · -- `S` is the component `P` itself
      refine ⟨T, j, BT, hjP.trans (eq_support_of_maximal_of_erase_eq_empty hPJ hJP hS).symm, ?_⟩
      have := isStratumAdjunctionPair_comp hB.1.1 hj (.refl hTB.1.1)
      rwa [Category.id_comp] at this
    · obtain ⟨J', hJ'card, hJ'ne, hJ'1, hS'⟩ :=
        exists_finset_maximal_preimage hB hj hjP hPJ h1 hJP hS
      obtain ⟨T', ι', BT', hι', F⟩ := ih hTB J' (by omega) hJ'ne hJ'1 _ hS'
      refine ⟨T', ι' ≫ j, BT', ?_, isStratumAdjunctionPair_comp hB.1.1 hj F.some⟩
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hι',
        Set.image_preimage_eq_of_subset (hjP ▸ hS.1.2.trans (Set.biInter_subset_of_mem hPJ))]

/-- A set maximal among the irreducible subsets of an intersection of prime divisors is
closed. -/
private theorem isClosed_of_maximal {Y : Scheme.{0}} [IsLocallyNoetherian Y]
    {J : Finset (MMP.Mori.PrimeDivisor Y)} {S : Set Y}
    (hS : Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ ⋂ P ∈ J, (P.support : Set Y)) S) :
    IsClosed S := by
  have hcl : IsClosed (⋂ P ∈ J, (P.support : Set Y)) :=
    isClosed_biInter fun P _ => P.idealSheaf.support.isClosed
  exact closure_subset_iff_isClosed.mp
    (hS.2 ⟨hS.1.1.closure, closure_minimal hS.1.2 hcl⟩ subset_closure)

/-- **The strata of a dlt pair meet the snc locus.** The generic point of a stratum of a dlt pair
lies outside every closed set witnessing dltness; by induction on the number of floor components
cutting out the stratum, through one adjunction step, along which witnesses restrict. -/
private theorem notMem_of_isGenericPoint_of_card_le (n : ℕ) :
    ∀ {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
      [IsNormal Y] {BY : QDivisor Y}, MMP.Intersection.IsDltPair sY BY →
      ∀ J : Finset (MMP.Mori.PrimeDivisor Y), J.card ≤ n → J.Nonempty →
      (∀ P ∈ J, 1 ≤ BY.coeff P) → ∀ S : Set Y,
      Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ ⋂ P ∈ J, (P.support : Set Y)) S →
      ∀ η : Y, IsGenericPoint η S → ∀ Z : TopologicalSpace.Closeds Y,
        MMP.Mori.IsSmoothScheme (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY) →
        DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY)
          (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι (Z.compl : Y.Opens)) BY) →
        (∀ (n : ℕ) (D : DivisorOver k sY), (D.center : Set Y) ⊆ Z →
          ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sY n (MMP.Mori.QDivisor.toRDivisor BY) D a →
            0 < a) →
        η ∉ (Z : Set Y) := by
  classical
  induction n with
  | zero =>
    intro Y sY _ _ _ BY _ J hJ hne
    exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ n ih =>
    intro Y sY _ _ _ BY hB J hJ hne h1 S hS η hη Z hsm hsnc hpos hηZ
    obtain ⟨P, hPJ⟩ := hne
    have hSP : S ⊆ (P.support : Set Y) :=
      hS.1.2.trans (Set.biInter_subset_of_mem hPJ)
    by_cases hJP : J.erase P = ∅
    · -- `S` is the component `P`, of log discrepancy `0`
      have hSeq := eq_support_of_maximal_of_erase_eq_empty hPJ hJP hS
      have hηP : η = P.genericPoint := by
        refine hη.eq ?_
        rw [hSeq, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isGenericPoint_closure
      have hXv : IsNormalVariety k sY := hB.1.1.1
      obtain ⟨N, K, hK, hQc⟩ := hB.1.1.2
      have hcen : ((DivisorOver.ofPrimeDivisor k hXv P).center : Set Y) ⊆ Z := by
        rw [DivisorOver.center_eq_closure_genericPoint]
        refine closure_minimal ?_ Z.isClosed
        rw [Set.singleton_subset_iff]
        change P.genericPoint ∈ (Z : Set Y)
        rw [← hηP]; exact hηZ
      have h0 := hpos N _ hcen _ (isLogDiscrepancy_ofPrimeDivisor hXv hK hQc P)
      have hP1 : BY.coeff P = 1 := le_antisymm (hB.2.1 P) (h1 P hPJ)
      rw [hP1] at h0
      norm_num at h0
    · obtain ⟨T, j, BT, hjP, hj⟩ := exists_isAdjunctionStep_of_isDltPair hB P (h1 P hPJ)
      obtain ⟨hTv, -, -, -, hci, -⟩ := id hj
      have : IsIntegral T := hTv.1.toIsIntegral
      have : IsNormal T := hTv.2
      have : IsLocallyNoetherian T := by
        have := hTv.1
        exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ sY)
      obtain ⟨J', hJ'card, hJ'ne, hJ'1, hS'⟩ :=
        exists_finset_maximal_preimage hB hj hjP hPJ h1 hJP hS
      obtain ⟨hsmT, hsncT, hposT⟩ := isDltWitness_preimage hB hsm hsnc hpos hj
      have hTB := isDltPair_of_isAdjunctionStep hB hj
      have hη' : IsGenericPoint hS'.1.1.genericPoint (j.base ⁻¹' S) := by
        have := hS'.1.1.isGenericPoint_genericPoint_closure
        rwa [(isClosed_of_maximal hS').closure_eq] at this
      have hjη : j.base hS'.1.1.genericPoint = η := by
        have h2 := hη'.image j.base.hom.continuous
        rw [Set.image_preimage_eq_of_subset (hjP ▸ hSP), (isClosed_of_maximal hS).closure_eq] at h2
        exact h2.eq hη
      refine ih hTB J' (by omega) hJ'ne hJ'1 _ hS' _ hη' _ hsmT hsncT hposT ?_
      change j.base hS'.1.1.genericPoint ∈ (Z : Set Y)
      rw [hjη]; exact hηZ

/-- **The codimension of a stratum at the snc locus.** If the generic point `η` of an irreducible
component `S` of `⋂_{P ∈ J} P`, for prime divisors `P` with coefficient at least one, is a point
at which the boundary is snc, then `codim S = |J|`: the components `P ∈ J` are distinct coordinate
hyperplanes at `η`, and a coordinate missing from them would cut out a generization of `η` lying on
every `P ∈ J`, contradicting maximality of `S`. -/
private theorem coheight_eq_card_of_notMem {k : Type} [Field k] {Y : Scheme.{0}}
    [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of k)} {BY : QDivisor Y}
    {Z : TopologicalSpace.Closeds Y}
    (hsnc : (BY.restrictOpen (Z.compl : Y.Opens)).IsSNC (Scheme.Opens.ι (Z.compl : Y.Opens) ≫ sY))
    {J : Finset (MMP.Mori.PrimeDivisor Y)} (h1 : ∀ P ∈ J, 1 ≤ BY.coeff P) {S : Set Y}
    (hS : Maximal (fun W : Set Y => IsIrreducible W ∧ W ⊆ ⋂ P ∈ J, (P.support : Set Y)) S)
    {η : Y} (hη : IsGenericPoint η S) (hηZ : η ∉ (Z : Set Y)) :
    Order.coheight η = J.card := by
  classical
  set U : Y.Opens := Z.compl
  obtain ⟨N, z, jjY, hz, hjY, hIY⟩ :=
    (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι BY ⟨η, hηZ⟩).mp
      (hsnc.2 ⟨η, hηZ⟩)
  let z' : Fin N → Y.presheaf.stalk η := z
  have hz' : IsRegularSystemOfParameters z' := hz
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz'
  have hηS : η ∈ S := hη.mem
  have hcl : IsClosed (⋂ P ∈ J, (P.support : Set Y)) :=
    isClosed_biInter fun P _ => P.idealSheaf.support.isClosed
  have hmem : ∀ P ∈ J, P ∈ BY.support ∧ η ∈ P.support := fun P hP =>
    ⟨Finsupp.mem_support_iff.mpr (lt_of_lt_of_le one_pos (h1 P hP)).ne',
      Set.mem_iInter₂.mp (hS.1.2 hηS) P hP⟩
  let c : J → Fin N := fun P => jjY ⟨P.1, hmem P.1 P.2⟩
  have hc : Function.Injective c := by
    intro a b hab
    exact Subtype.ext (Subtype.mk_eq_mk.mp (hjY hab))
  set Jf : Finset (Fin N) := Finset.univ.image c with hJf
  have hJfcard : Jf.card = J.card := by
    rw [hJf, Finset.card_image_of_injective _ hc, Finset.card_univ, Fintype.card_coe]
  have hJfuniv : Jf = Finset.univ := by
    by_contra hne
    have hlt : Jf.card < N := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hne)
    obtain ⟨hreg, -, hq⟩ :=
      MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz' Jf
    set I := Ideal.span (z' '' (Jf : Set (Fin N))) with hIdef
    have := IsRegularLocalRing.isDomain (Y.presheaf.stalk η ⧸ I)
    have hI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
    let q : PrimeSpectrum (Y.presheaf.stalk η) := ⟨I, hI⟩
    have hsp : Y.fromSpecStalk η q ⤳ η := MMP.Resolution.specializes_fromSpecStalk η q
    have hy'J : closure {Y.fromSpecStalk η q} ⊆ ⋂ P ∈ J, (P.support : Set Y) := by
      refine closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_iInter₂.mpr fun P hP => ?_)) hcl
      change Y.fromSpecStalk η q ∈ P.idealSheaf.support
      rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hsp,
        MMP.Resolution.primeOfSpecializes_fromSpecStalk]
      have := hIY ⟨P, hmem P hP⟩
      change IdealSheafData.stalk P.idealSheaf η = Ideal.span {z' (c ⟨P, hP⟩)} at this
      rw [this, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨c ⟨P, hP⟩, by simp [hJf], rfl⟩
    have hSsub : S ⊆ closure {Y.fromSpecStalk η q} := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hsp))
        isClosed_closure
    have hle := hS.2 ⟨isIrreducible_singleton.closure, hy'J⟩ hSsub
    have hsp' : η ⤳ Y.fromSpecStalk η q := by
      rw [specializes_iff_mem_closure, hη.def]
      exact hle (subset_closure rfl)
    have heq : Y.fromSpecStalk η q = Y.fromSpecStalk η (IsLocalRing.closedPoint _) := by
      rw [Scheme.fromSpecStalk_closedPoint]; exact (hsp.antisymm hsp').eq
    have hqc := (Y.fromSpecStalk η).isEmbedding.injective heq
    have hImax : I = IsLocalRing.maximalIdeal _ := congrArg PrimeSpectrum.asIdeal hqc
    have hpos : 0 < Jfᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]; omega
    apply MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hq ⟨0, hpos⟩
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hIdef, hImax, ← hz'.1]
    exact Ideal.subset_span ⟨_, rfl⟩
  have hN : N = J.card := by
    rw [← hJfcard, hJfuniv, Finset.card_univ, Fintype.card_fin]
  have h := (ringKrullDim_stalk_eq_coheight η).symm.trans hz'.2
  rw [hN] at h
  exact_mod_cast h

end Flag

/-- **Adjunction to a dlt stratum.** Let `(X, B)` be a rational dlt pair over an
algebraically closed field `k` of characteristic zero and `S` a boundary stratum
(`MMP.Fourfold.IsDltStratum`). Then iterated adjunction is defined along some flag ending at
`S`: there is an adjunction pair `(T, B_T)` (`MMP.Fourfold.IsStratumAdjunctionPair`)
whose closed immersion `ι : T ⟶ X` has image `S`. Moreover, for every flag of iterated
adjunction data ending at `S`, the final pair `(T, B_T)`, with `K_T + B_T = (K_X + B)|_T`, is a
dlt pair (`MMP.Intersection.IsDltPair`) for the structure morphism `ι ≫ s_X`. Finally, the
generic point `η` of `S` lies outside every closed `Z ⊆ X` witnessing that `(X, B)` is dlt, and
`S` has the expected codimension: `codim S = |J|` for every finite set `J` of prime divisors with
coefficient one in `B` of which `S` is an irreducible component of the intersection. -/
@[mmp "lem_mmp_dlt_stratum_adjunction"]
public theorem IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {S : Set X}
    (hS : IsDltStratum sX B S) :
    ((∃ (T : Scheme.{0}) (ι : T ⟶ X) (BT : QDivisor T),
        Set.range ι.base = S ∧ IsStratumAdjunctionPair sX B ι BT) ∧
      ∀ {T : Scheme.{0}} {ι : T ⟶ X} {BT : QDivisor T}
        (F : StratumAdjunctionData sX B ι BT), Set.range ι.base = S →
        haveI : IsIntegral T := F.isNormalVariety.1.toIsIntegral
        haveI : IsNormal T := F.isNormalVariety.2
        haveI : IsLocallyNoetherian T := by
          have := F.isNormalVariety.1
          exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
        MMP.Intersection.IsDltPair (ι ≫ sX) BT) ∧
      ∀ η : X, IsGenericPoint η S →
        (∀ Z : TopologicalSpace.Closeds X,
          IsSmoothScheme (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX) →
          DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX)
            (inverseTransformDivisor (Scheme.Opens.ι (Z.compl : X.Opens)) B) →
          (∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
            ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a →
              0 < a) →
          η ∉ (Z : Set X)) ∧
        ∀ J : Finset (MMP.Mori.PrimeDivisor X), (∀ P ∈ J, 1 ≤ B.coeff P) →
          Maximal (fun T : Set X => IsIrreducible T ∧ T ⊆ ⋂ P ∈ J, (P.support : Set X)) S →
          Order.coheight η = J.card := by
  obtain ⟨hB, J, hne, h1, -, hmax⟩ := hS
  have hnot : ∀ η : X, IsGenericPoint η S → ∀ Z : TopologicalSpace.Closeds X,
      IsSmoothScheme (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX) →
      DivisorWithCoeffs.IsSNC (Scheme.Opens.ι (Z.compl : X.Opens) ≫ sX)
        (inverseTransformDivisor (Scheme.Opens.ι (Z.compl : X.Opens)) B) →
      (∀ (n : ℕ) (D : DivisorOver k sX), (D.center : Set X) ⊆ Z →
        ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a → 0 < a) →
      η ∉ (Z : Set X) := fun η hη =>
    notMem_of_isGenericPoint_of_card_le J.card hB J le_rfl hne h1 S hmax η hη
  refine ⟨⟨exists_isStratumAdjunctionPair_of_card_le J.card hB J le_rfl hne h1 S hmax,
    fun F _ => isDltPair_of_stratumAdjunctionData hB F⟩, fun η hη => ⟨hnot η hη, ?_⟩⟩
  intro J' h1' hmax'
  obtain ⟨-, -, Z, hsm, hsnc, hpos⟩ := hB
  have hηZ := hnot η hη Z hsm hsnc hpos
  rw [inverseTransformDivisor_ι_eq_restrictOpen] at hsnc
  exact coheight_eq_card_of_notMem hsnc h1' hmax' hη hηZ

end MMP.Fourfold
