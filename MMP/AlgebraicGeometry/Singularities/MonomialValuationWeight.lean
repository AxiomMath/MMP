module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.Resolution.SNCWeight.PrimitiveWeightModification
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal

/-!
# Monomial valuations of primitive weight

Let `W` be a smooth variety over a field `k` of characteristic zero, `T = ∑ⱼ Tⱼ` a reduced
simple normal crossing divisor on `W`, `J` a nonempty set of components of `T` and `Z_J` an
irreducible component of `⋂_{j ∈ J} Tⱼ` with generic point `η`, and `α ∈ ℤ_{>0}^J` a primitive
weight.

There is a normalized divisorial valuation of `k(W)` that is monomial of weight `α` at `Z_J`,
for every choice of local equations `zⱼ ∈ 𝒪_{W,η}` of the `Tⱼ`: it is `ord_{E_α}` for the
exceptional component `E_α` of the toroidal modification
`MMP.Fourfold.exists_snc_modification_primitive_weight`, attached to a regular subdivision of
the orthant `ℝ_{≥0}^J` containing the ray of `α`.

Such a valuation `ξ` has vanishing reduced snc discrepancy, `e_T(ξ) = 0`. A valuation monomial
of weight `α` at `Z_J` is determined by its values on `𝒪_{W,η}`, whose fraction field is `k(W)`,
so `ξ = ord_{E_α}`. The modification `g : W' ⟶ U`, over an affine neighbourhood `U` of `η`, is
log crepant, `K_{W'} + T' = g^*(K_U + T|_U)`, with `T'` reduced, so the log discrepancy of `E_α`
over `(U, T|_U)` is `1 - coeff_{E_α} T' = 0`. Log discrepancies are local on the base, so the log
discrepancy of `ξ` over `(W, T)`, and then over `(W°_ξ, T|_{W°_ξ})`, is `0` as well; and
`T|_{W°_ξ}` is the restriction of `∑_{j ∈ J(ξ)} Tⱼ`, since every component of `T` meeting `W°_ξ`
contains the centre of `ξ`.

## Main results

* `MMP.Fourfold.exists_isMonomialValuationOfWeight`: monomial valuations of primitive weight
  exist.
* `MMP.Fourfold.isReducedSNCDiscrepancy_zero_of_isMonomialValuationOfWeight`: they have reduced
  snc discrepancy `0`.

## Implementation notes

* The valuation is produced independently of the local equations: one `ξ` serves for every
  family `z` of generators of the stalks at `η` of the ideal sheaves of the `Tⱼ`, the ideals
  `𝔞_{α,m}` not depending on that choice (`MMP.Fourfold.weightedMonomialIdeal_eq_of_span_eq`).
* Primitivity of `α` is `∀ d, (∀ j, d ∣ αⱼ) → d = 1`; it is needed, since for `α = d α'` the
  monomial valuation of weight `α` is `d` times a normalized one.
* The reduced snc discrepancy is the predicate `MMP.Fourfold.IsReducedSNCDiscrepancy` on its
  value, so `e_T(ξ) = 0` reads `IsReducedSNCDiscrepancy sW T ξ 0`.
* The modification is constructed over an affine neighbourhood `U` of `η` rather than over
  `W°_ξ`; the passage from `U` to `W°_ξ` goes through the pair `(W, T)` (on a smooth variety
  `K_W + T` is Cartier) and the locality of log discrepancies on the base.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-- A valuation of the function field of an integral scheme is determined by its values on any
stalk, whose fraction field the function field is. -/
private theorem valuation_ext_of_stalk {X : Scheme.{u}} [IsIntegral X] (x : X)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {v w : Valuation X.functionField Γ}
    (h : ∀ f : X.presheaf.stalk x, v (algebraMap _ X.functionField f) =
      w (algebraMap _ X.functionField f)) : v = w := by
  ext t
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk x) t
  rw [map_div₀, map_div₀, h, h]

/-- A valuation monomial of weight `α` at `Z` is unique. -/
private theorem eq_of_isMonomialValuationOfWeight {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] {T : Divisor W} {J : Finset (MMP.Mori.PrimeDivisor W)}
    {Z : IrreducibleCloseds W} {z : J → W.presheaf.stalk Z.isIrreducible.genericPoint}
    {α : J → ℕ} {ξ ξ' : Valuation W.functionField ℤᵐ⁰}
    (hξ : IsMonomialValuationOfWeight sW T J Z z α ξ)
    (hξ' : IsMonomialValuationOfWeight sW T J Z z α ξ') : ξ = ξ' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := hξ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h'⟩ := hξ'
  refine valuation_ext_of_stalk Z.isIrreducible.genericPoint fun f => ?_
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨M, hM, hξM⟩ := h f hf
  obtain ⟨M', hM', hξM'⟩ := h' f hf
  rw [hξM, hξM', hM.unique hM']

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem valuation_comap_injective {L L' : Type*} [Field L] [Field L'] (f : L →+* L')
    (hf : Function.Surjective f) :
    Function.Injective (fun v : Valuation L' ℤᵐ⁰ => v.comap f) := by
  intro v w h
  ext g
  obtain ⟨g, rfl⟩ := hf g
  exact congrArg (fun u : Valuation L ℤᵐ⁰ => u g) h

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_opens_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (hX : MMP.Mori.IsVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- **Log discrepancies over an open subscheme.** For a pair `(X, B)`, a proper divisor `D` over
`X` whose centre meets `U` and a proper divisor `D'` over `U` with the same valuation have the same
log discrepancies, for `B` and `B|_U` respectively. -/
private theorem isLogDiscrepancy_open_iff {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} (hB : MMP.Mori.IsPair sX B) {n : ℕ} (hn : topologicalKrullDim X = n)
    (U : X.Opens) [Nonempty U]
    (D : DivisorOver k sX) (hDp : IsProper D.f) (hDU : D.f D.E.genericPoint ∈ U)
    (D' : DivisorOver k (U.ι ≫ sX)) (hD'p : IsProper D'.f)
    (hv : D.valuation = D'.valuation.comap (functionFieldMap U.ι)) (a : ℝ) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a ↔
      MMP.Intersection.IsLogDiscrepancy (U.ι ≫ sX) n
        (QDivisor.toRDivisor (MMP.Mori.inverseTransformDivisor U.ι B)) D' a := by
  classical
  haveI := isDominant_ι_of_nonempty U
  obtain ⟨hXv, n0, K, hK, hQ⟩ := hB
  obtain rfl : n0 = n := by exact_mod_cast hK.topologicalKrullDim_eq.symm.trans hn
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy ⟨hXv, n0, K, hK, hQ⟩ hK D
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hDU⟩
  obtain ⟨hY, hf, E', -, hval, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff ⟨hXv, hK, hQ⟩ D U hcen
  have hcU := (hiff c).1 hc
  haveI : IsProper (D.f ∣_ U) := by haveI := hDp; infer_instance
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcU.isPair hcU.2.1 D'
  have hDUv : DivisorOver.valuation (⟨_, D.f ∣_ U, hY, hf, E'⟩ : DivisorOver k (U.ι ≫ sX)) =
      D'.valuation :=
    valuation_comap_injective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U).2
      (hval.symm.trans hv)
  have hcc : (c' : ℝ) = c := by
    have := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq
      ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc' (1 + c')).2 ⟨hD'p, rfl⟩)
      ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcU (1 + c)).2
        ⟨inferInstance, rfl⟩) hDUv.symm
    linarith
  rw [MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc,
    inverseTransformDivisor_ι_eq_restrictOpen,
    MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hc', hcc]
  exact ⟨fun h => ⟨hD'p, h.2⟩, fun h => ⟨hDp, h.2⟩⟩

/-- `(W, T)` is a pair for any divisor `T` on a smooth variety: `K_W` exists and every Weil
divisor is Cartier. -/
private theorem isPair_toQDivisor_of_isSmoothScheme {k : Type u} [Field k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW) {n : ℕ}
    (hdim : topologicalKrullDim W = n) (T : Divisor W) :
    MMP.Mori.IsPair sW (Divisor.toQDivisor T) := by
  haveI := hW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sW hWs hdim
  exact ⟨⟨hW, inferInstance⟩, n, KW, hKW, isQCartier_of_isSmoothScheme hWs _⟩

/-- Membership in `W ∖ ⋃_{Z ⊄ Tⱼ} Tⱼ`. -/
private theorem mem_sncComplement {W : Scheme.{u}} {T : Divisor W} {Z : Set W} {x : W} :
    x ∈ sncComplement T Z ↔ ∀ E ∈ T.support, ¬ Z ⊆ E.support → x ∉ E.support := by
  simp [← SetLike.mem_coe, sncComplement]

/-- A generic point of `Z` lies in `W ∖ ⋃_{Z ⊄ Tⱼ} Tⱼ`. -/
private theorem mem_sncComplement_of_isGenericPoint {W : Scheme.{u}} {T : Divisor W} {Z : Set W}
    {x : W} (hx : IsGenericPoint x Z) : x ∈ sncComplement T Z :=
  mem_sncComplement.2 fun E _ hZE hxE => hZE <| by
    rw [← hx.def]
    exact (E.idealSheaf.support).isClosed.closure_subset_iff.2 (by simpa using hxE)

/-- On `W ∖ ⋃_{Z ⊄ Tⱼ} Tⱼ` a reduced divisor `T` restricts to `∑_{Z ⊆ Tⱼ} Tⱼ`. -/
private theorem restrictOpen_sncComplement {W : Scheme.{u}} {T : Divisor W}
    (hT : MMP.Intersection.IsReducedEffective T) (Z : Set W) :
    T.restrictOpen (sncComplement T Z) =
      (MMP.Intersection.reducedDivisorOf (sncIndexSet T Z)).restrictOpen (sncComplement T Z) := by
  classical
  refine DivisorWithCoeffs.ext' fun E' => ?_
  rw [DivisorWithCoeffs.coeff_restrictOpen, DivisorWithCoeffs.coeff_restrictOpen,
    MMP.Intersection.coeff_reducedDivisorOf]
  set P := OpenWeilRestriction.primeDivisorMap (sncComplement T Z).ι E'
  rcases hT P with h0 | h1
  · rw [h0, if_neg]
    intro hP
    simp only [sncIndexSet, Finset.mem_filter, Finsupp.mem_support_iff] at hP
    exact hP.1 h0
  · have hsupp : P ∈ T.support :=
      Finsupp.mem_support_iff.mpr (by rw [← DivisorWithCoeffs.coeff_apply, h1]; simp)
    rw [h1, if_pos]
    refine Finset.mem_filter.2 ⟨hsupp, by_contra fun hZP => mem_sncComplement.1 ?_ _ hsupp hZP
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)⟩
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
    exact E'.genericPoint.2

/-- **The reduced snc discrepancy is the log discrepancy over `(W, T)`.** On a smooth variety
with a reduced snc divisor `T`, a divisor `D` over `W` with log discrepancy `e` over `(W, T)` has
`e_T(ord_D) = e`. -/
private theorem isReducedSNCDiscrepancy_of_isLogDiscrepancy {k : Type u} [Field k]
    [PerfectField k] {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] (hW : MMP.Mori.IsVariety k sW)
    (hWs : IsSmoothScheme sW) {T : Divisor W} (hT : MMP.Intersection.IsReducedEffective T)
    (hTs : T.IsSNC sW) {n : ℕ} (hdim : topologicalKrullDim W = n) {D : DivisorOver k sW}
    (hDp : IsProper D.f) {e : ℝ}
    (he : MMP.Intersection.IsLogDiscrepancy sW n
      (QDivisor.toRDivisor (Divisor.toQDivisor T)) D e) :
    IsReducedSNCDiscrepancy sW T D.valuation e := by
  set V := sncComplement T (D.center : Set W)
  have hηV : D.f D.E.genericPoint ∈ V := mem_sncComplement_of_isGenericPoint <| by
    rw [D.center_eq_closure_genericPoint]
    exact isGenericPoint_closure
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  obtain ⟨hWn, n', KW, hKW, hQ⟩ := isPair_toQDivisor_of_isSmoothScheme hW hWs hdim T
  obtain ⟨hY1, hf1, E1, -, hval1, -⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff ⟨hWn, hKW, hQ⟩ D V
      ⟨_, by rw [D.center_eq_closure_genericPoint]; exact subset_closure rfl, hηV⟩
  have hD1p : IsProper (D.f ∣_ V) := by
    haveI := hDp
    infer_instance
  refine ⟨hW, hWs, hT, hTs, D.center, ⟨D, hDp, rfl, rfl⟩, this, n, ⟨_, D.f ∣_ V, hY1, hf1, E1⟩,
    hD1p, hval1, ?_⟩
  rw [inverseTransformDivisor_ι_eq_restrictOpen, ← restrictOpen_sncComplement hT,
    ← inverseTransformDivisor_ι_eq_restrictOpen, ← QDivisor.toRDivisor_toQDivisor,
    ← MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]
  exact (isLogDiscrepancy_open_iff sW ⟨hWn, n', KW, hKW, hQ⟩ hdim V D hDp hηV _ hD1p hval1 e).1 he

/-- **A monomial valuation of primitive weight has log discrepancy `0` over `(W, T)`.** It is
`ord_{E_α}` for the boundary component `E_α` of the log crepant toroidal modification
`exists_snc_modification_primitive_weight` over a neighbourhood `U` of `η`, whose log
discrepancy over `(U, T|_U)` is `1 - coeff_{E_α} T' = 0`. -/
private theorem isLogDiscrepancy_zero_of_isMonomialValuationOfWeight {k : Type u} [Field k]
    [CharZero k] {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] {T : Divisor W} {J : Finset (MMP.Mori.PrimeDivisor W)}
    {Z : IrreducibleCloseds W} {z : J → W.presheaf.stalk Z.isIrreducible.genericPoint}
    {α : J → ℕ} {ξ : Valuation W.functionField ℤᵐ⁰}
    (hξ : IsMonomialValuationOfWeight sW T J Z z α ξ) (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1)
    {D : DivisorOver k sW} (hDp : IsProper D.f) (hξD : ξ = D.valuation) (hZD : Z = D.center) :
    ∃ n : ℕ, topologicalKrullDim W = n ∧ MMP.Intersection.IsLogDiscrepancy sW n
      (QDivisor.toRDivisor (Divisor.toQDivisor T)) D 0 := by
  obtain ⟨hW, hWs, hT, hTs, hJ, hJT, hZ, hz, hα, -, -⟩ := id hξ
  have hη : D.f D.E.genericPoint = Z.isIrreducible.genericPoint := by
    refine IsGenericPoint.eq ?_ (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)
    rw [hZD, D.center_eq_closure_genericPoint]
    exact isGenericPoint_closure
  obtain ⟨U, hηU, -, -, W', _, _, _, g, hg, _, hW', T', hproj, -, -, hT'r, -, -, -,
      ⟨n, K, hK, hcrep⟩, E, hE, hmono, -⟩ :=
    exists_snc_modification_primitive_weight sW hW hWs T hT hTs J hJ hJT Z hZ α hα hαp
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := isDominant_ι_of_nonempty U
  have hdim : topologicalKrullDim W = n :=
    (topologicalKrullDim_opens_eq hW U).symm.trans hK.topologicalKrullDim_eq
  have hgp : IsProper g := isProper_of_isProjectiveMorphism g hproj
  haveI : IsDominant g := hg.isDominant
  let Dg : DivisorOver k (U.ι ≫ sW) := ⟨W', g, hW', hg, E⟩
  have hvU : D.valuation = Dg.valuation.comap (functionFieldMap U.ι) := by
    rw [← hξD, eq_of_isMonomialValuationOfWeight hξ (hmono z hz)]
    ext t
    exact congrArg E.divisorialValuation
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g U.ι t).symm
  refine ⟨n, hdim, ?_⟩
  rw [isLogDiscrepancy_open_iff sW (isPair_toQDivisor_of_isSmoothScheme hW hWs hdim T) hdim U D
      hDp (hη ▸ hηU) Dg hgp hvU,
    MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]
  convert MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (D := Dg)
    (hcrep E) hgp using 1
  simp [Divisor.coeff_toQDivisor, (hT'r E).resolve_left (Finsupp.mem_support_iff.mp hE)]

variable {k : Type u} [Field k] {W : Scheme.{u}} (sW : W ⟶ Spec (.of k)) [IsIntegral W]

/-- **Monomial valuations exist.** Let `W` be a smooth variety over a field `k` of characteristic
zero, `T` a reduced snc divisor on `W`, `J ⊆ Supp T` a nonempty set of components and `Z` an
irreducible component of `⋂_{j ∈ J} Tⱼ`. For every primitive `α ∈ ℤ_{>0}^J` there is a
normalized divisorial valuation `ξ` of `k(W)` that is monomial of weight `α` at `Z`
(`MMP.Fourfold.IsMonomialValuationOfWeight`) with respect to every family of local equations
`zⱼ ∈ 𝒪_{W,η}` of the `Tⱼ`. -/
@[mmp "lem_oai4_c1_monomial_divisorial"]
public theorem exists_isMonomialValuationOfWeight [CharZero k]
    (hW : MMP.Mori.IsVariety k sW) (hWs : IsSmoothScheme sW) (T : Divisor W)
    (hT : MMP.Intersection.IsReducedEffective T) (hTs : T.IsSNC sW)
    (J : Finset (MMP.Mori.PrimeDivisor W)) (hJ : J.Nonempty) (hJT : J ⊆ T.support)
    (Z : IrreducibleCloseds W)
    (hZ : Maximal (fun S : Set W => IsIrreducible S ∧ S ⊆ ⋂ E ∈ J, E.support) (Z : Set W))
    (α : J → ℕ) (hα : ∀ j, 0 < α j) (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1) :
    ∃ ξ : Valuation W.functionField ℤᵐ⁰,
      ∀ z : J → W.presheaf.stalk Z.isIrreducible.genericPoint,
        (∀ j : J, IdealSheafData.stalk j.1.idealSheaf Z.isIrreducible.genericPoint =
          Ideal.span {z j}) →
        IsMonomialValuationOfWeight sW T J Z z α ξ := by
  obtain ⟨_, _⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, E, -, hE, -⟩ :=
    exists_snc_modification_primitive_weight sW hW hWs T hT hTs J hJ hJT Z hZ α hα hαp
  exact ⟨_, hE⟩

variable [IsLocallyNoetherian W] [IsNormal W] in
/-- **Monomial valuations have zero error.** Let `W` be a smooth variety over a field `k` of
characteristic zero, `T` a reduced snc divisor, `J` a nonempty set of components of `T` and `Z`
an irreducible component of `⋂_{j ∈ J} Tⱼ`. If `α ∈ ℤ_{>0}^J` is primitive and `ξ` is monomial
of weight `α` at `Z` (`MMP.Fourfold.IsMonomialValuationOfWeight`), then the reduced snc
discrepancy `e_T(ξ)` is `0` (`MMP.Fourfold.IsReducedSNCDiscrepancy`). -/
@[mmp "lem_oai4_c1_monomial_zero_error"]
public theorem isReducedSNCDiscrepancy_zero_of_isMonomialValuationOfWeight [CharZero k]
    {T : Divisor W} {J : Finset (MMP.Mori.PrimeDivisor W)} {Z : IrreducibleCloseds W}
    {z : J → W.presheaf.stalk Z.isIrreducible.genericPoint} {α : J → ℕ}
    {ξ : Valuation W.functionField ℤᵐ⁰}
    (hξ : IsMonomialValuationOfWeight sW T J Z z α ξ)
    (hαp : ∀ d : ℕ, (∀ j, d ∣ α j) → d = 1) :
    IsReducedSNCDiscrepancy sW T ξ 0 := by
  obtain ⟨hW, hWs, hT, hTs, -, -, -, -, -, ⟨D, hDp, hξD, hZD⟩, -⟩ := id hξ
  obtain ⟨n, hdim, hlog⟩ :=
    isLogDiscrepancy_zero_of_isMonomialValuationOfWeight hξ hαp hDp hξD hZD
  exact hξD ▸ isReducedSNCDiscrepancy_of_isLogDiscrepancy hW hWs hT hTs hdim hDp hlog

end MMP.Fourfold

end
