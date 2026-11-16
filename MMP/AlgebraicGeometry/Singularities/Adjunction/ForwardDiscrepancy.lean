module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.CyclicCover.IndexOneCover
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.StrongResolution.Functorial
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import MMP.AlgebraicGeometry.Resolution.Blowup.ProjectiveBirationalIsBlowup
import MMP.AlgebraicGeometry.Resolution.Blowup.CoherentIdealBlowup
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo

/-!
# Forward discrepancy adjunction on a normal prime divisor

Let `X` be a normal variety of dimension `n + 1` over an algebraically closed field `k` of
characteristic zero, `S ⊆ X` a normal prime divisor, `B ≥ 0` a `ℚ`-divisor without component `S`
with `K_X + S + B` `ℚ`-Cartier, and `B_S` the adjunction boundary on `S`, defined by Poincaré
residues of local generators of `𝒪_X(m(K_X + S + B))`. Every divisor `F` over `S` is realised by
an exceptional divisor `E` over `X` with the same center and `a(F, S, B_S) = a(E, X, S + B)`.
In particular a lower bound for the discrepancies of the exceptional divisors over `X` with
center in a closed subset `Z ⊆ S` bounds the discrepancies of all divisors over `(S, B_S)` with
center in `Z`.

The proof follows Kollár et al. On a log resolution `f : Y ⟶ X` of `(X, S + B)` whose strict
transform `S'` of `S` meets no prime divisor over `Supp B ∖ S`, and on which an ideal realising
`F` becomes invertible, `F` is a prime divisor `F'` of `S'`; its generic point `y` has codimension
two in `Y`, and `E` is the exceptional divisor of the blow-up of `Y` along the closure of `y`, with
`a(E, X, S + B) = ∑ a(Eᵢ, X, S + B)` over the `f`-exceptional `Eᵢ` through `y`. At `y` the snc
divisor has at most one component `E₀` besides `S'`. Writing `f^*τ = g (ds/s ∧ dx)^{⊗m}` with
`s` a local equation of `S'` and `e` one of `E₀`, the residue of `f^*τ` along `S'` has order
`ord_{E₀}(f^*τ) = m · a(E₀, X, S + B)` along `F'`. Residues commute with pull-back to the strict
transform, so this residue is `f_S^*ρ` for the residue `ρ` of `τ` along `S`, a local generator of
`𝒪_S(m(K_S + B_S))`, and `m · a(F, S, B_S) = ord_{F'}(f_S^*ρ)`.

## Main results

* `MMP.Fourfold.exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue`: the forward
  discrepancy adjunction.
* `MMP.Fourfold.isPoincareResidue_pullback`: Poincaré residues of `m`-fold forms commute with
  pull-back along a birational morphism to the strict transform.

## Implementation notes

Discrepancies are predicates `MMP.Mori.IsDiscrepancy`; a discrepancy is computed by any local
generator of `𝒪_X(m'(K_X + Δ))` near the center, for any `m'`
(`mul_eq_ordPullback_of_isDiscrepancy`), which lets the exponent `m` of the residue
identification differ from the Cartier index of `K_X + S + B`. That `m(K_S + B_S)` is Cartier
follows from the existence of local generators of it at every point of `S`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 17.2
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.46, 5.47
-/

open CategoryTheory TopologicalSpace MMP.Mori
open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero

universe u

namespace MMP.Fourfold

/-! ### Realising a divisor over `S` on a log resolution of `(X, S + B)` -/

section

/-! ### Exceptional divisors -/

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- The generic point of an irreducible scheme has coheight zero. -/
private theorem coheight_genericPoint (X : Scheme.{u}) [IrreducibleSpace X] :
    Order.coheight (genericPoint X) = 0 :=
  Order.coheight_eq_zero.2 fun b hb => by
    rw [Scheme.le_iff_specializes] at hb ⊢
    exact genericPoint_specializes _

/-! ### Auxiliary facts on log resolutions -/

/-- A proper specialization of the generic point of a prime divisor has codimension at least
two. -/
private theorem two_le_coheight_of_specializes {X : Scheme.{u}} (P : PrimeDivisor X) {x : X}
    (hx : P.genericPoint ⤳ x) (hne : x ≠ P.genericPoint) : 2 ≤ Order.coheight x := by
  have hlt : x < P.genericPoint := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hx) fun h =>
    hne (inseparable_iff_specializes_and.2 ⟨Scheme.le_iff_specializes.1 h, hx⟩).eq
  have := Order.coheight_add_one_le hlt
  rwa [P.coheight_genericPoint, one_add_one_eq_two] at this

/-- The exceptional prime divisors of a log resolution form a finite set. -/
private theorem exists_finset_isExceptional {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} {D : RDivisor X}
    {Y : Scheme.{u}} {f : Y ⟶ X} (hf : Mori.IsLogResolution sX D f)
    (hY : IsNormalVariety k (f ≫ sX)) :
    ∃ Ex : Finset (PrimeDivisor Y), ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E := by
  classical
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  have hcoh : ∀ s ∈ (exceptionalSet f : Set Y), Order.coheight s ≠ 0 := by
    intro s hs
    have hs' : s ∈ ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) :=
      Or.inl hs
    rcases hf.isSNCSubset with h | ⟨t, ht, -⟩
    · rw [h] at hs'
      exact hs'.elim
    · rw [← ht] at hs'
      obtain ⟨E, -, hsE⟩ := Set.mem_iUnion₂.1 hs'
      have hle : s ≤ E.genericPoint := by
        rw [Scheme.le_iff_specializes]
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hsE
        exact specializes_iff_mem_closure.2 hsE
      have h1 := Order.coheight_anti hle
      rw [E.coheight_genericPoint] at h1
      intro h0
      rw [h0] at h1
      exact absurd h1 (by norm_num)
  have hfin := finite_setOf_genericPoint_mem (exceptionalSet f).isClosed hcoh
  refine ⟨hfin.toFinset.filter fun E => RationalMap.IsExceptional f.toRationalMap E, fun E => ?_⟩
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨MMP.Positivity.support_subset_exceptionalSet E h
    (MMP.Flips.primeDivisor_genericPoint_mem_support E), h⟩⟩

/-- The stalk ideal of an ideal sheaf at a point is the stalk of the ideal sheaf there. -/
private theorem stalkIdeal_eq_stalk {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x = AlgebraicGeometry.IdealSheafData.stalk I x :=
  le_antisymm
    (iSup_le fun U => le_iSup_of_le U.1 (le_iSup_of_le U.2 le_rfl))
    (iSup_le fun U => iSup_le fun hx => le_iSup_of_le ⟨U, hx⟩ le_rfl)

/-- On an irreducible scheme, a point of coheight zero is the generic point. -/
private theorem eq_genericPoint_of_coheight_eq_zero {X : Scheme.{u}} [IrreducibleSpace X] {s : X}
    (h : Order.coheight s = 0) : s = genericPoint X := by
  have hmax := Order.coheight_eq_zero.1 h
  have h1 : s ≤ genericPoint X := by
    rw [Scheme.le_iff_specializes]; exact genericPoint_specializes s
  have h2 := hmax h1
  rw [Scheme.le_iff_specializes] at h1 h2
  exact (inseparable_iff_specializes_and.2 ⟨h1, h2⟩).eq.symm

/-- In `WithBot ℕ∞`, if `d + 1 = n` and `d + c = n + 1`, then `c = 2`. -/
private theorem eq_two_of_add_one_eq_of_add_eq {d : WithBot ℕ∞} {n : ℕ} {c : ℕ∞}
    (h1 : d + 1 = (n : WithBot ℕ∞)) (h2 : d + (c : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    c = 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => norm_cast at h1
    | coe m =>
      induction c using ENat.recTopCoe with
      | top => norm_cast at h2
      | coe c => norm_cast at h1 h2 ⊢; omega

/-- In `WithBot ℕ∞`, `e + 1 = n + 1` forces `e = n`. -/
private theorem eq_of_add_one_eq_add_one {e : WithBot ℕ∞} {n : ℕ}
    (h : e + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : e = (n : WithBot ℕ∞) := by
  induction e using WithBot.recBotCoe with
  | bot => simp at h; exact absurd h WithBot.bot_ne_coe
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => norm_cast at h
    | coe m => norm_cast at h ⊢; omega

/-- If `ι : T ⟶ X` is a closed immersion onto a prime divisor of a variety `X` of dimension
`n + 1`, then `T` has dimension `n`. -/
public theorem topologicalKrullDim_eq_of_range_eq_support
    {k : Type u} [Field k] {X T : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
    [LocallyOfFiniteType sX]
    {n : ℕ} (hdim : topologicalKrullDim X = n + 1) (ι : T ⟶ X) [IsClosedImmersion ι]
    (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X)) :
    topologicalKrullDim T = n := by
  have hPP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX P.genericPoint
  rw [P.coheight_genericPoint, hdim] at hPP
  have hT : topologicalKrullDim T = topologicalKrullDim (closure {P.genericPoint} : Set X) := by
    have e : (closure {P.genericPoint} : Set X) = Set.range ι.base := by
      rw [hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.toHomeomorph ι.isEmbedding).isHomeomorph)
  rw [hT, eq_of_add_one_eq_add_one
    (e := topologicalKrullDim (closure {P.genericPoint} : Set X)) (n := n)
    (by simpa using hPP)]

/-- The image in a variety `Y` of dimension `m + 1` of the generic point of a prime divisor of a
prime divisor `S'` of `Y` has codimension two. -/
private theorem coheight_subschemeι_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    {m : ℕ} (hdim : topologicalKrullDim Y = m + 1)
    (S' : PrimeDivisor Y) (F' : PrimeDivisor S'.idealSheaf.subscheme) :
    Order.coheight (S'.idealSheaf.subschemeι F'.genericPoint) = 2 := by
  haveI : IsIntegral S'.idealSheaf.subscheme := S'.integral
  set ι := S'.idealSheaf.subschemeι
  have hP : Set.range ι.base = (S'.support : Set Y) := Scheme.IdealSheafData.range_subschemeι _
  have hQ := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sY) F'.genericPoint
  rw [F'.coheight_genericPoint] at hQ
  have hx := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY (ι F'.genericPoint)
  have hcl : topologicalKrullDim (closure {ι F'.genericPoint} : Set Y) =
      topologicalKrullDim (closure {F'.genericPoint} : Set S'.idealSheaf.subscheme) := by
    have e : (closure {ι F'.genericPoint} : Set Y) = ι.base '' closure {F'.genericPoint} := by
      rw [← Set.image_singleton, ← ι.isClosedEmbedding.closure_image_eq]
    rw [e]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (Topology.IsEmbedding.homeomorphImage ι.isEmbedding _).isHomeomorph).symm
  rw [topologicalKrullDim_eq_of_range_eq_support sY hdim ι S' hP] at hQ
  rw [hcl, hdim] at hx
  exact eq_two_of_add_one_eq_of_add_eq (by simpa using hQ) hx

/-- The stalk of an ideal sheaf at a generization `y` of `x` is generated by the image of its
stalk at `x`. -/
private theorem stalk_map_stalkSpecializes {X : Scheme.{u}} (I : X.IdealSheafData) {x y : X}
    (h : y ⤳ x) :
    (IdealSheafData.stalk I x).map (X.presheaf.stalkSpecializes h).hom =
      IdealSheafData.stalk I y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.isOpen hxU
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I y ⟨U, hU⟩ hyU, Ideal.map_map, ← CommRingCat.hom_comp,
    TopCat.Presheaf.germ_stalkSpecializes]

/-- The pull-back of an effective Cartier divisor `J` along a morphism from an integral scheme
whose generic point avoids the support of `J` is an effective Cartier divisor: a local generator
of `J` restricts to a nonzero element of each local ring. -/
private theorem isEffectiveCartierDivisor_comap_of_genericPoint_notMem {Y Z : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsIntegral Z] [IsLocallyNoetherian Z] (J : Y.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (g : Z ⟶ Y)
    (hη : g (genericPoint Z) ∉ J.support) :
    Stacks.Divisors.IsEffectiveCartierDivisor (J.comap g) := by
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun t _ => ?_
  obtain ⟨h, -, hgen⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor J hJ (g t)
  have hst : IdealSheafData.stalk (J.comap g) t = Ideal.span {(g.stalkMap t).hom h} := by
    rw [AlgebraicGeometry.stalk_comap, hgen, Ideal.map_span, Set.image_singleton]
  refine ⟨(g.stalkMap t).hom h, IsRegular.of_ne_zero ?_, hst⟩
  intro h0
  have hsp : genericPoint Z ⤳ t := genericPoint_specializes t
  have hη' : genericPoint Z ∉ (J.comap g).support := by
    intro hm
    have h' : genericPoint Z ∈ ((J.comap g).support : Set Z) := hm
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage] at h'
    exact hη h'
  rw [← Stacks.Divisors.stalk_eq_top_iff_notMem_support, ← stalk_map_stalkSpecializes _ hsp, hst,
    h0, Ideal.span_singleton_eq_bot.2 rfl, Ideal.map_bot] at hη'
  exact bot_ne_top hη'

/-! ### The divisor `G` -/

/-- A morphism is injective over its biregular locus. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {X Y : Scheme.{u}} {f : X ⟶ Y} {x y : X}
    (h : f x = f y) (hx : f x ∈ biregularLocus f) : x = y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let px : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let py : (f ⁻¹ᵁ V).toScheme := ⟨y, show f y ∈ V from h ▸ hx⟩
  have hpx : V.ι ((f ∣_ V) px) = f x := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have hpy : V.ι ((f ∣_ V) py) = f y := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have h1 : (f ∣_ V) px = (f ∣_ V) py := V.ι.isOpenEmbedding.injective (by rw [hpx, hpy, h])
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective h1)

/-- A prime divisor whose ideal at `η_Z` is generated by a member of a regular system of
parameters has multiplicity `1` along `Z`. -/
private theorem multiplicityAlong_eq_one {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Q : PrimeDivisor X) (Z : IrreducibleCloseds X) {m : ℕ}
    {z : Fin m → X.presheaf.stalk Z.isIrreducible.genericPoint}
    (hz : IsRegularSystemOfParameters z) (i : Fin m)
    (hQ : IdealSheafData.stalk Q.idealSheaf Z.isIrreducible.genericPoint = Ideal.span {z i}) :
    Q.multiplicityAlong Z = 1 := by
  have hmem : ∀ j, z j ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) :=
    fun j => by
      rw [← hz.1]
      exact Ideal.subset_span ⟨j, rfl⟩
  have hli := linearIndependent_toCotangent_of_isRegularSystemOfParameters hz hmem
  have hsq :
      z i ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk Z.isIrreducible.genericPoint) ^ 2 :=
    fun h => hli.ne_zero i ((Ideal.toCotangent_eq_zero _ _).2 h)
  rw [PrimeDivisor.multiplicityAlong_eq_of_stalkIdeal_eq_span Q Z
    (by rwa [stalkIdeal_eq_stalk])]
  refine le_antisymm (iSup₂_le fun s hs => ?_) (le_iSup₂_of_le 1 (by simpa using hmem i) le_rfl)
  by_contra hlt
  push Not at hlt
  have : 2 ≤ s := by exact_mod_cast (ENat.add_one_le_iff (by simp)).2 hlt
  exact hsq (Ideal.pow_le_pow_right this hs)

/-- A prime divisor not passing through `η_Z` has multiplicity `0` along `Z`. -/
private theorem multiplicityAlong_eq_zero {X : Scheme.{u}} (Q : PrimeDivisor X)
    (Z : IrreducibleCloseds X) (h : Z.isIrreducible.genericPoint ∉ Q.support) :
    Q.multiplicityAlong Z = 0 := by
  unfold MMP.Mori.PrimeDivisor.multiplicityAlong
  rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ h]
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  · exact absurd (top_le_iff.1 (hs.trans (Ideal.pow_le_self hs0.ne')))
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
private noncomputable def compDivisorOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by
      rw [Category.assoc]
      exact E.isNormalVariety
    isBirationalMorphism := IsPair.isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

/-- The valuation of `(W, f ∘ g, F)` is that of `(W, g, F)`, read on `k(X)` through `f^*`. -/
private theorem valuation_compDivisorOver {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (E : DivisorOver k (f ≫ sX)) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have := E.isIntegral
  have := E.isDominant
  have := E.isNormal
  have := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The components of the snc divisor `Ex(f) ∪ f⁻¹(Supp D)` of a log resolution: a finite set of
prime divisors, which are exactly those with generic point in that set, whose reduced sum is
snc. -/
private theorem exists_finset_isSNC_of_isLogResolution {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {D : RDivisor X} {Y : Scheme.{u}} {f : Y ⟶ X}
    [LocallyOfFiniteType (f ≫ sX)] (hf : Mori.IsLogResolution sX D f) :
    ∃ t : Finset (PrimeDivisor Y),
      (∀ P : PrimeDivisor Y,
        P.genericPoint ∈ (exceptionalSet f : Set Y) ∨ f P.genericPoint ∈ D.supp ↔ P ∈ t) ∧
      DivisorWithCoeffs.IsSNC (f ≫ sX) (∑ P ∈ t, Finsupp.single P (1 : ℤ)) := by
  rcases hf.isSNCSubset with h | ⟨t, ht, htsnc⟩
  · refine ⟨∅, fun P => ?_, ?_⟩
    · simp only [Finset.notMem_empty, iff_false]
      intro hP
      have : P.genericPoint ∈
          ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) := hP
      rw [h] at this
      exact this
    · rw [Finset.sum_empty]
      haveI := MMP.Resolution.Aux.smooth_of_isSmoothScheme' (f ≫ sX) hf.isSmoothScheme
      exact DivisorWithCoeffs.isSNC_zero _
  · refine ⟨t, fun P => ⟨fun hP => ?_, fun hP => ?_⟩, htsnc⟩
    · have : P.genericPoint ∈
          ((exceptionalSet f ⊔ D.supp.preimage f.continuous : Closeds Y) : Set Y) := hP
      rw [← ht] at this
      obtain ⟨P', hP', hPP'⟩ := Set.mem_iUnion₂.1 this
      rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPP'] at hP'
    · have : P.genericPoint ∈ ⋃ E ∈ t, (E.support : Set Y) :=
        Set.mem_iUnion₂.2 ⟨P, hP, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
      rw [ht] at this
      exact this

open Classical in
/-- **The divisor `G` over `X`.** On a log resolution `f : Y ⟶ X` of `(X, S + B)` such that the
strict transform `S'` of `S` meets no prime divisor lying over a point of `Supp B ∖ S`, and for
a point `y ∈ S'` of codimension two in `Y`, the exceptional divisor `G` of the blow-up of `Y`
along the closure of `y` is exceptional over `X`, has center the closure of `f(y)`, and
`a(G, X, S + B) = ∑_{y ∈ E} a(E, X, S + B)`, the sum over the `f`-exceptional prime divisors
`E` through `y`. -/
private theorem exists_divisorOver_isDiscrepancy {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : PrimeDivisor X) {B : QDivisor X} (hB : B.coeff S = 0)
    (hKSB : (Divisor.toQDivisor K + Finsupp.single S 1 + B).IsQCartier)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Mori.IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (S' : PrimeDivisor Y) (hS' : inverseTransformPrimeDivisor f S = some S')
    (hdisj : ∀ Γ : PrimeDivisor Y, f Γ.genericPoint ∈ B.supp → f Γ.genericPoint ∉ S.support →
      Disjoint (S'.support : Set Y) Γ.support)
    (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E)
    (e : PrimeDivisor Y → ℚ)
    (he : ∀ E ∈ Ex, IsDiscrepancy sX (n + 1) K
      (Divisor.toQDivisor (Finsupp.single S 1) + B)
      ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ (e E))
    (y : Y) (hyS : y ∈ S'.support) (hy : Order.coheight y = 2) :
    ∃ G : DivisorOver k sX, G.IsExceptional ∧ G.f G.E.genericPoint = f y ∧
      IsDiscrepancy sX (n + 1) K (Finsupp.single S 1 + B) G
        (∑ E ∈ Ex, if y ∈ E.support then e E else 0) := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hY.1.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  haveI : IsProper f := hf.isProper
  have hfb : IsBirationalMorphism f := hf.isBirationalMorphism
  have hsm : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  haveI : Smooth (f ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hsm
  have hS1 : Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) = Finsupp.single S (1 : ℚ) := by
    rw [MMP.Threefold.Resolution.toQDivisor_single]; simp
  set Δ : QDivisor X := Finsupp.single S 1 + B with hΔ
  have hPW : IsPairWith sX (n + 1) K Δ := ⟨hX, hK, by rw [hΔ, ← add_assoc]; exact hKSB⟩
  obtain ⟨t, ht, htsnc⟩ := exists_finset_isSNC_of_isLogResolution hf
  rw [QDivisor.supp_toRDivisor, hS1] at ht
  choose a ha using fun Γ : PrimeDivisor Y =>
    MMP.Positivity.IsPair.exists_isDiscrepancy hPW.isPair hK ⟨Y, f, hY, hfb, Γ⟩
  have hfS := MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hS'
  have hbir := two_le_closedsCodimension_compl_biregularLocus (hY := hX.1) (hX := hY.1) sX f hfb
  -- non-exceptional prime divisors of `Y` lie over prime divisors of `X`, biregularly
  have hnex : ∀ Γ : PrimeDivisor Y, ¬ RationalMap.IsExceptional f.toRationalMap Γ →
      ∃ P : PrimeDivisor X, f Γ.genericPoint = P.genericPoint ∧
        f Γ.genericPoint ∈ biregularLocus f ∧ a Γ = -Δ.coeff P := by
    intro Γ hΓ
    obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPW
      (⟨Y, f, hY, hfb, Γ⟩ : DivisorOver k sX) hΓ
    have hη : f Γ.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hfb, Γ⟩ : DivisorOver k sX), hc,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine ⟨P, hη, ?_, (ha Γ).eq hd⟩
    by_contra hV
    have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hbir) _ hV
    rw [hη, P.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  have hS'nex : ¬ RationalMap.IsExceptional f.toRationalMap S' := by
    intro hE
    have h2 := (isExceptional_iff_two_le_coheight hX
      (⟨Y, f, hY, hfb, S'⟩ : DivisorOver k sX)).mp hE
    change 2 ≤ Order.coheight (f S'.genericPoint) at h2
    rw [hfS.1, S.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  have hΔS : Δ.coeff S = 1 := by
    rw [hΔ, DivisorWithCoeffs.coeff_add, hB, add_zero, DivisorWithCoeffs.coeff_single_self]
  have haS' : a S' = -1 := by
    obtain ⟨P, hP, -, hPa⟩ := hnex S' hS'nex
    have : P = S := AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hP.symm.trans hfS.1)
    rw [hPa, this, hΔS]
  have hS't : S' ∈ t := by
    refine (ht S').1 (Or.inr ?_)
    rw [hfS.1, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨S, by rw [hΔS]; norm_num, MMP.Flips.primeDivisor_genericPoint_mem_support S⟩
  have hExt : ∀ E ∈ Ex, E ∈ t := fun E hE => (ht E).1 (Or.inl
    (MMP.Positivity.support_subset_exceptionalSet E ((hEx E).1 hE)
      (MMP.Flips.primeDivisor_genericPoint_mem_support E)))
  -- the crepant boundary of `(X, S + B)` on `Y`
  set ΔY : QDivisor Y := ∑ Γ ∈ t, (-a Γ) • Finsupp.single Γ (1 : ℚ) with hΔY
  have hΔYc : ∀ Γ, ΔY.coeff Γ = if Γ ∈ t then -a Γ else 0 := by
    intro Γ
    rw [hΔY, ← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
    simp only [DivisorWithCoeffs.coeffAddMonoidHom_apply, DivisorWithCoeffs.coeff_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq']
  have hcrep : IsCrepantBoundary sX (n + 1) K Δ f hY hfb ΔY := by
    intro Γ
    rw [hΔYc]
    split_ifs with hΓ
    · rw [neg_neg]; exact ha Γ
    · have hΓex : ¬ RationalMap.IsExceptional f.toRationalMap Γ := fun hE =>
        hΓ ((ht Γ).1 (Or.inl (MMP.Positivity.support_subset_exceptionalSet Γ hE
          (MMP.Flips.primeDivisor_genericPoint_mem_support Γ))))
      obtain ⟨P, hP, -, hPa⟩ := hnex Γ hΓex
      have h0 : Δ.coeff P = 0 := by
        by_contra h0
        refine hΓ ((ht Γ).1 (Or.inr ?_))
        rw [hP, DivisorWithCoeffs.mem_supp_iff]
        exact ⟨P, h0, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
      rw [neg_zero, ← neg_zero, ← h0, ← hPa]
      exact ha Γ
  -- the canonical divisor of `Y`
  have hdimY : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hK.topologicalKrullDim_eq]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb).symm
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hsm hdimY
  obtain ⟨-, hiff⟩ := IsPair.isDiscrepancy_iff_of_crepant hPW.isPair f hY hfb hK hKY
    (Or.inl hcrep)
  -- the blow-up of `Y` along the closure of `y`
  set W := IrreducibleCloseds.closureSingleton y with hWdef
  have hWy : W.isIrreducible.genericPoint = y :=
    AlgebraicGeometry.AlgebraicCycle.genericPoint_closureSingleton y
  have hWc : codimension W = 2 := by rw [MMP.Flips.codimension_closureSingleton, hy]
  have hreg : IsRegularLocalRing (Y.presheaf.stalk W.isIrreducible.genericPoint) :=
    isRegularLocalRing_stalk_of_smooth_over_field (f ≫ sX) _
  obtain ⟨⟨D, j, hjo, hj, hE⟩, -⟩ :=
    MMP.Flips.valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp (f ≫ sX) hY W
      (by rw [hWc]) hreg
  haveI := hjo
  obtain ⟨-, hDd⟩ := isDiscrepancy_blowUp (f ≫ sX) hY.1 hKY ΔY W (c := 2) (by rw [hWc]; rfl)
    le_rfl D j hj hE
  rw [hWy] at hE
  have hGd := (hiff D (compDivisorOver f hY hfb D)
    (valuation_compDivisorOver f hY hfb D) _).mp hDd
  -- `f y` is a point of `S` other than its generic point
  have hsp : S'.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyS
    exact specializes_iff_mem_closure.2 hyS
  have hfy : 2 ≤ Order.coheight (f y) := by
    have h2 : f y ≠ S.genericPoint := by
      intro h
      have := eq_of_map_eq_of_mem_biregularLocus (h.trans hfS.1.symm) (h ▸ hfS.1 ▸ hfS.2)
      rw [this, S'.coheight_genericPoint] at hy
      exact absurd hy (by norm_num)
    exact two_le_coheight_of_specializes S (hfS.1 ▸ hsp.map f.continuous) h2
  refine ⟨compDivisorOver f hY hfb D, ?_, ?_, ?_⟩
  · rw [isExceptional_iff_two_le_coheight hX]
    change 2 ≤ Order.coheight ((D.f ≫ f) D.E.genericPoint)
    rw [Scheme.Hom.comp_apply, hE]
    exact hfy
  · change (D.f ≫ f) D.E.genericPoint = _
    rw [Scheme.Hom.comp_apply, hE]
  · convert hGd using 1
    have hmemt : ∀ Γ ∈ t, Γ ∈ (∑ P ∈ t, Finsupp.single P (1 : ℤ)).support := fun Γ hΓ => by
      rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
        Finset.sum_eq_single_of_mem Γ hΓ fun Q _ hQΓ => Finsupp.single_eq_of_ne hQΓ.symm,
        Finsupp.single_eq_same]
      exact one_ne_zero
    have hsum : (ΔY.sum fun Γ c => c * ((Γ.multiplicityAlong W).toNat : ℚ)) =
        ∑ Γ ∈ t, -a Γ * (if y ∈ Γ.support then 1 else 0) := by
      rw [hΔY, ← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun Γ hΓ => ?_
      rw [Finsupp.smul_single, Finsupp.sum_single_index (zero_mul _), smul_eq_mul, mul_one]
      congr 1
      split_ifs with hyΓ
      · obtain ⟨_, z, j, hz, -, hI⟩ := htsnc.2 W.isIrreducible.genericPoint
        have hΓW : W.isIrreducible.genericPoint ∈ Γ.support := hWy ▸ hyΓ
        rw [multiplicityAlong_eq_one Γ _ hz (j ⟨Γ, hmemt Γ hΓ, hΓW⟩) (hI ⟨Γ, hmemt Γ hΓ, hΓW⟩)]
        rfl
      · rw [multiplicityAlong_eq_zero Γ W (hWy ▸ hyΓ)]
        rfl
    -- the components of the snc divisor through `y`
    have hterm : ∀ Γ ∈ t, (if y ∈ Γ.support then a Γ else 0) =
        (if Γ = S' then a Γ else 0) +
          (if Γ ∈ Ex then (if y ∈ Γ.support then a Γ else 0) else 0) := by
      intro Γ hΓ
      by_cases hΓS : Γ = S'
      · subst hΓS
        have : Γ ∉ Ex := fun h => hS'nex ((hEx Γ).1 h)
        simp [hyS, this]
      by_cases hΓE : Γ ∈ Ex
      · simp [hΓS, hΓE]
      · simp only [hΓS, hΓE, if_false, zero_add]
        split_ifs with hyΓ
        · exfalso
          have hΓex : ¬ RationalMap.IsExceptional f.toRationalMap Γ := fun h => hΓE ((hEx Γ).2 h)
          obtain ⟨P, hP, hPV, -⟩ := hnex Γ hΓex
          rcases (ht Γ).2 hΓ with hΓX | hΓD
          · exact hΓX hPV
          · rw [hP, DivisorWithCoeffs.mem_supp_iff] at hΓD
            obtain ⟨Q, hQ, hPQ⟩ := hΓD
            have hQP := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hPQ
            subst hQP
            by_cases hQS : Q = S
            · subst hQS
              exact hΓS (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
                (eq_of_map_eq_of_mem_biregularLocus (hP.trans hfS.1.symm) (hP ▸ hPV)))
            · have hBQ : B.coeff Q ≠ 0 := by
                rwa [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_of_ne
                  (Ne.symm hQS), zero_add] at hQ
              refine Set.disjoint_left.1 (hdisj Γ ?_ ?_) hyS hyΓ
              · rw [hP, DivisorWithCoeffs.mem_supp_iff]
                exact ⟨Q, hBQ, MMP.Flips.primeDivisor_genericPoint_mem_support Q⟩
              · rw [hP]
                intro hm
                exact hQS (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hm).symm
        · rfl
    have hkey : (∑ Γ ∈ t, if y ∈ Γ.support then a Γ else 0) =
        -1 + ∑ E ∈ Ex, if y ∈ E.support then e E else 0 := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq' t S' a,
        if_pos hS't, haS', ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.2 hExt]
      congr 1
      refine Finset.sum_congr rfl fun E hE => ?_
      rw [(ha E).eq (by simpa only [hS1] using he E hE)]
    rw [hsum]
    have h2 : (∑ Γ ∈ t, -a Γ * (if y ∈ Γ.support then (1 : ℚ) else 0)) =
        -∑ Γ ∈ t, if y ∈ Γ.support then a Γ else 0 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun Γ _ => ?_
      split_ifs <;> ring
    rw [h2, hkey]
    push_cast
    ring

/-! ### The ideal `Ĵ` through which `F` is realised -/

/-- **Divisors over `X` lift to a proper birational model.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, every divisor `D` over `X` has the valuation of a divisor `E`
over `Y`, read on `k(X)` through `f^*`: by the valuative criterion the valuation ring of `ord_D`
dominates the local ring of a point of `Y`. -/
private theorem exists_divisorOver_comap_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    [IsProper f] (D : DivisorOver k sX) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    ∃ E : DivisorOver k (f ≫ sX), D.valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    change D.valuation (e.symm (functionFieldMap f t)) = D.valuation t
    exact congrArg D.valuation (e.symm_apply_apply t)
  -- `ξ` dominates the local ring of a point of `Y` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : Y, (∀ a : Y.presheaf.stalk x,
      ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
    set z := D.f D.E.genericPoint
    have hw : ∀ b : X.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
          D.valuation (algebraMap _ X.functionField b) := by
      intro b
      simpa only [Valuation.comap_apply] using
        congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
    let R := ξ.valuationSubring
    let φ : X.presheaf.stalk z →+* R :=
      ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
    have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hex : ValuativeCriterion.Existence f := by
      have h : @IsProper _ _ f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq f :=
      { R := R
        K := Y.functionField
        i₁ := Y.fromSpecStalk (genericPoint Y)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk f,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
        Y.fromSpecStalk (genericPoint Y) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
        Y.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (Y.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : Y.presheaf.stalk x,
        algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]
      exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(Y)`: `ord_E` on `D.Y`, along `k(Y) ≅ k(X) ≅ k(D.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  refine ⟨D'.toDivisorOver, ?_⟩
  change D.valuation = D'.valuation.comap (functionFieldMap f)
  rw [hv, hξ]

/-- A morphism of irreducible schemes sending the generic point to the generic point is
dominant. -/
private theorem isDominant_of_map_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  refine Set.eq_univ_of_univ_subset ?_
  have hc : closure ({genericPoint Y} : Set Y) = Set.univ := genericPoint_spec Y
  rw [← hc]
  exact closure_mono (Set.singleton_subset_iff.2 ⟨_, h⟩)

/-- **Realising a divisor over `T` on a proper birational model `W`.** Let `F` be a divisor over
a normal variety `T`, `G₀` a divisor over `T` with the same valuation whose model maps only its
generic point to the generic point of `T`, and `g : W ⟶ T` a proper birational morphism from a
normal variety such that, on an open `V ⊆ W` containing every point of `W` over the center of
`F`, `g` factors through the model of `G₀`. Then `F` is a prime divisor of `W`: the center of
`F` on `W` has local ring dominating, hence equal to, the discrete valuation ring of `G₀`. -/
private theorem exists_primeDivisor_valuation_eq_of_lift {k : Type u} [Field k]
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    {sT : T ⟶ Spec (.of k)} (hT : IsNormalVariety k sT)
    (F G0 : DivisorOver k sT) (hG0 : G0.valuation = F.valuation)
    (hgen : ∀ z : G0.Y, G0.f z = genericPoint T →
      z = (haveI := G0.isIntegral; genericPoint G0.Y))
    {W : Scheme.{u}} (g : W ⟶ T) (hW : IsNormalVariety k (g ≫ sT))
    (hg : IsBirationalMorphism g) [IsProper g] (V : W.Opens) (ψ : V.toScheme ⟶ G0.Y)
    (hψ : ψ ≫ G0.f = V.ι ≫ g) (hV : ∀ w : W, g w = F.f F.E.genericPoint → w ∈ V) :
    ∃ F' : PrimeDivisor W, (⟨W, g, hW, hg, F'⟩ : DivisorOver k sT).valuation = F.valuation := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (g ≫ sT) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sT)
  haveI : IsDominant g := hg.isDominant
  haveI := G0.isIntegral
  haveI := G0.isNormal
  haveI := G0.isLocallyNoetherian
  haveI := G0.isDominant
  haveI : IsSeparated (G0.f ≫ sT) := G0.isNormalVariety.1.toIsSeparated
  -- the divisor `F` on `W`
  obtain ⟨Fh, hFh⟩ := exists_divisorOver_comap_eq hW hg F
  haveI := Fh.isIntegral
  haveI := Fh.isNormal
  haveI := Fh.isLocallyNoetherian
  haveI := Fh.isDominant
  set c := Fh.f Fh.E.genericPoint with hc
  have hgc : g c = F.f F.E.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hT.1
      (D := compDivisorOver g hW hg Fh) (D' := F) (by rw [valuation_compDivisorOver, ← hFh])
  have hcV : c ∈ V := hV c hgc
  set c' : V.toScheme := ⟨c, hcV⟩ with hc'
  haveI : Nonempty V.toScheme := ⟨c'⟩
  haveI : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨c, hcV⟩)
  -- `ψ` is dominant
  have hψη : ψ (genericPoint V.toScheme) = genericPoint G0.Y := hgen _ (by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply, map_genericPoint_of_isDominant V.ι,
      map_genericPoint_of_isDominant g])
  haveI : IsDominant ψ := isDominant_of_map_genericPoint ψ hψη
  have key : ∀ (m : V.toScheme ⟶ T) [IsDominant m], m = ψ ≫ G0.f → ∀ t,
      functionFieldMap m t = functionFieldMap ψ (functionFieldMap G0.f t) := by
    intro m _ hm t
    subst hm
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply ψ G0.f t).symm
  have hff : ∀ t, functionFieldMap ψ (functionFieldMap G0.f t) =
      functionFieldMap V.ι (functionFieldMap g t) := by
    intro t
    rw [← key (V.ι ≫ g) hψ.symm t,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have hbG := G0.isBirationalMorphism.functionFieldMap_bijective
  have hbg := hg.functionFieldMap_bijective
  have hbV : Function.Bijective (functionFieldMap V.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨c', trivial⟩
  set w0 := G0.E.divisorialValuation with hw0def
  have hw0 : ∀ t, w0 (functionFieldMap G0.f t) = F.valuation t := fun t => by rw [← hG0]; rfl
  have hvW : ∀ t, Fh.valuation (functionFieldMap g t) = F.valuation t := fun t => by
    rw [hFh]; rfl
  -- the local homomorphism `𝒪_{G₀, ψ(c)} ⟶ 𝒪_{W, c}`
  haveI : IsIso (V.ι.stalkMap c') := inferInstance
  let φ : G0.Y.presheaf.stalk (ψ c') →+* W.presheaf.stalk c :=
    (inv (V.ι.stalkMap c')).hom.comp (ψ.stalkMap c').hom
  have hφ : ∀ a t, algebraMap _ G0.Y.functionField a = functionFieldMap G0.f t →
      algebraMap _ W.functionField (φ a) = functionFieldMap g t := by
    intro a t ha
    apply hbV.1
    have h1 : functionFieldMap V.ι (algebraMap _ W.functionField (φ a)) =
        algebraMap _ V.toScheme.functionField ((V.ι.stalkMap c').hom (φ a)) :=
      functionFieldMap_algebraMap_stalk V.ι c' (φ a)
    have h2 : (V.ι.stalkMap c').hom (φ a) = (ψ.stalkMap c').hom a := by
      change ((V.ι.stalkMap c').hom ((inv (V.ι.stalkMap c')).hom ((ψ.stalkMap c').hom a))) = _
      rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]
    rw [h1, h2, ← functionFieldMap_algebraMap_stalk ψ c' a, ha, hff]
  -- `ψ(c)` is the generic point of the divisor of `G₀`
  have hdom : ∀ a : G0.Y.presheaf.stalk (ψ c'), w0 (algebraMap _ _ a) ≤ 1 ∧
      (a ∈ IsLocalRing.maximalIdeal _ → w0 (algebraMap _ _ a) < 1) := by
    intro a
    obtain ⟨t, ht⟩ := hbG.2 (algebraMap _ G0.Y.functionField a)
    have hb := hφ a t ht.symm
    rw [← ht, hw0, ← hvW, ← hb]
    refine ⟨MMP.Positivity.DivisorOver.valuation_algebraMap_le_one Fh c rfl (φ a), fun ha => ?_⟩
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one Fh c rfl (φ a) ?_
    haveI : IsLocalHom φ := by
      change IsLocalHom ((inv (V.ι.stalkMap c')).hom.comp (ψ.stalkMap c').hom)
      infer_instance
    exact map_nonunit φ a ha
  have hψc : ψ c' = G0.E.genericPoint := by
    refine MMP.Positivity.DivisorOver.eq_of_dominates (G0.f ≫ sT) w0 (fun a => (hdom a).1)
      (fun a ha => (hdom a).2 ha) (fun a => ?_) (fun a ha => ?_)
    · exact (PrimeDivisor.divisorialValuation_le_one_iff G0.E _).2 ⟨a, rfl⟩
    · exact (PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff G0.E a).2 ha
  -- `φ` is an isomorphism
  have hrange : ∀ z : G0.Y, z = G0.E.genericPoint → ∀ s, w0 s ≤ 1 →
      s ∈ (algebraMap (G0.Y.presheaf.stalk z) G0.Y.functionField).range := by
    rintro z rfl s hs
    exact (PrimeDivisor.divisorialValuation_le_one_iff G0.E s).1 hs
  have hφb : Function.Bijective φ := by
    constructor
    · intro a a' haa
      obtain ⟨t, ht⟩ := hbG.2 (algebraMap _ G0.Y.functionField a)
      obtain ⟨t', ht'⟩ := hbG.2 (algebraMap _ G0.Y.functionField a')
      have h1 := hφ a t ht.symm
      have h2 := hφ a' t' ht'.symm
      rw [haa, h2] at h1
      have : t = t' := hbg.1 h1.symm
      subst this
      exact IsFractionRing.injective (G0.Y.presheaf.stalk (ψ c')) G0.Y.functionField
        (ht.symm.trans ht')
    · intro b
      obtain ⟨t, ht⟩ := hbg.2 (algebraMap _ W.functionField b)
      have hle : w0 (functionFieldMap G0.f t) ≤ 1 := by
        rw [hw0, ← hvW, ht]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one Fh c rfl b
      obtain ⟨a, ha⟩ := hrange (ψ c') hψc _ hle
      refine ⟨a, IsFractionRing.injective (W.presheaf.stalk c) W.functionField ?_⟩
      rw [hφ a t ha, ht]
  have hcoh : Order.coheight c = 1 := by
    have h1 := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective φ hφb)
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hψc,
      G0.E.coheight_genericPoint] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh, ?_⟩
  have hv := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hW Fh
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne c hcoh)
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne c hcoh).symm
  ext t
  rw [← hvW, hv]
  change _ = PrimeDivisor.divisorialValuation _
    (functionFieldMap (𝟙 W) (functionFieldMap g t))
  rw [functionFieldMap_id_apply]
  rfl

/-- An affine variety is quasi-projective: `𝒪_X` is ample relative to the quasi-affine structure
morphism. -/
private theorem isQuasiProjectiveVariety_of_isAffine {k : Type u} [Field k] {U : Scheme.{u}}
    [IsAffine U] (s : U ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k s] :
    IsQuasiProjectiveVariety k s := by
  rw [isQuasiProjectiveVariety_iff_isQuasiProjective,
    isQuasiProjective_iff_hProjectiveIsQuasiProjective]
  exact ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule U, inferInstance,
    Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule s _ (Iso.refl _)⟩

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- The pull-back of an effective Cartier divisor along an open immersion of integral schemes is
an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_comap_of_isOpenImmersion {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsIntegral X] (J : Y.IdealSheafData)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (j : X ⟶ Y) [IsOpenImmersion j] :
    Stacks.Divisors.IsEffectiveCartierDivisor (J.comap j) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian j
  refine isEffectiveCartierDivisor_of_stalk_regular_principal _ fun t _ => ?_
  obtain ⟨g, hg, hgen⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor J hJ (j t)
  refine ⟨(j.stalkMap t).hom g, IsRegular.of_ne_zero ?_, by
    rw [AlgebraicGeometry.stalk_comap, hgen, Ideal.map_span, Set.image_singleton]⟩
  haveI : IsIso (j.stalkMap t) := @IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _ _ ‹_› t
  have hinj : Function.Injective (j.stalkMap t).hom :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap t)).1
  intro h0
  have : g = 0 := hinj (by rw [h0, map_zero])
  exact hg.ne_zero this

/-- A closed immersion of an integral scheme onto a prime divisor `P` maps the generic point to
the generic point of `P`. -/
private theorem map_genericPoint_eq {X T : Scheme.{u}} [IsIntegral T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X)) :
    ι (genericPoint T) = P.genericPoint := by
  have h1 : IsGenericPoint (ι (genericPoint T)) (closure (ι.base '' Set.univ)) :=
    (genericPoint_spec T).image ι.continuous
  rw [Set.image_univ, ι.isClosedEmbedding.isClosed_range.closure_eq, hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact h1.eq (isGenericPoint_closure)

/-- **Realising a divisor over `T` on the models of `T`.** Let `T ⊆ X` be a normal closed
subvariety, image of a prime divisor `P` of `X`, with a canonical divisor, and `F` a divisor over
`T` whose center is not all of `T`. There is an ideal sheaf `J ⊆ 𝒪_X` whose support has
codimension at least two in `X` such that `F` is a prime divisor of every proper birational
model `W ⟶ T` from a normal variety on which `J` pulls back to an effective Cartier divisor:
near the center of `F`, `F` is a prime divisor of a projective model `Bl_{J₀} U₀` of an affine
open `U₀ ⊆ T`, and `J` is the ideal of the closure of `V(J₀)`. -/
private theorem exists_idealSheaf_realising {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (hT : IsNormalVariety k (ι ≫ sX)) (P : PrimeDivisor X)
    (hP : Set.range ι = (P.support : Set X))
    {n : ℕ} {KS : Divisor T} (hKS : KS.IsCanonicalDivisor (ι ≫ sX) n)
    (F : DivisorOver k (ι ≫ sX)) (hFη : F.f F.E.genericPoint ≠ genericPoint T) :
    ∃ J : X.IdealSheafData, (∀ x ∈ J.support, 2 ≤ Order.coheight x) ∧
      ∀ (W : Scheme.{u}) (g : W ⟶ T) (hW : IsNormalVariety k (g ≫ ι ≫ sX))
        (hg : IsBirationalMorphism g), IsProper g →
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (g ≫ ι)) →
        ∃ F' : PrimeDivisor W,
          (⟨W, g, hW, hg, F'⟩ : DivisorOver k (ι ≫ sX)).valuation = F.valuation := by
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ sX) := hT.1
  set x0 := F.f F.E.genericPoint with hx0
  -- an affine open `U₀ ⊆ T` through the center of `F`
  obtain ⟨_, ⟨V, hVa, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ι x0)) isOpen_univ
  set U0 : T.Opens := ι ⁻¹ᵁ V with hU0
  have hx0U : x0 ∈ U0 := hxV
  haveI : IsAffine U0 := (hVa.preimage ι : IsAffineOpen U0)
  haveI : Nonempty U0 := ⟨⟨x0, hx0U⟩⟩
  haveI : IsDominant U0.ι := Opens.isDominant_ι (U0.isOpen.dense ⟨x0, hx0U⟩)
  have hU0v : IsNormalVariety k (U0.ι ≫ ι ≫ sX) := MMP.Mori.isNormalVariety_ι hT U0
  haveI : AlgebraicGeometry.IsVariety k (U0.ι ≫ ι ≫ sX) := hU0v.1
  haveI : IsQuasiProjectiveVariety k (U0.ι ≫ ι ≫ sX) := isQuasiProjectiveVariety_of_isAffine _
  have hU0b : IsBirationalMorphism U0.ι := by
    haveI : IsOpenImmersion ((⊤ : U0.toScheme.Opens).ι ≫ U0.ι) := inferInstance
    exact isBirationalMorphism_of_isOpenImmersion U0.ι ⊤ (by simp)
  -- `F` restricted to `U₀`
  have hPW0 : IsPairWith (ι ≫ sX) n KS (-Divisor.toQDivisor KS) :=
    ⟨hT, hKS, by rw [add_neg_cancel]; exact QDivisor.isQCartier_zero⟩
  have hFc : ((F.center : Set T) ∩ U0).Nonempty :=
    ⟨x0, by rw [F.center_eq_closure_genericPoint]; exact subset_closure rfl, hx0U⟩
  obtain ⟨hY0, hf0, E0, -, hv0, -⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPW0 F U0 hFc
  set F0 : DivisorOver k (U0.ι ≫ ι ≫ sX) := ⟨_, F.f ∣_ U0, hY0, hf0, E0⟩ with hF0
  haveI := F0.isIntegral
  haveI := F0.isNormal
  haveI := F0.isLocallyNoetherian
  haveI := F0.isDominant
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (U0.ι ≫ ι ≫ sX) F0.valuation := by
    refine ⟨F0.Y, F0.f ≫ U0.ι ≫ ι ≫ sX, F0.isNormalVariety, F0.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra (U0.ι ≫ ι ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (F0.f ≫ U0.ι ≫ ι ≫ sX)
    refine ⟨MMP.Mori.functionFieldAlgEquiv (U0.ι ≫ ι ≫ sX) F0.f
      F0.isBirationalMorphism.functionFieldMap_bijective, ?_⟩
    ext t
    rfl
  -- a projective model of `U₀` on which `F` is a prime divisor, and its blow-up presentation
  obtain ⟨D0, hD0p, hD0v, -⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates
    (U0.ι ≫ ι ≫ sX) hdiv (F0.f F0.E.genericPoint)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one F0 _ rfl)
    (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one F0 _ rfl)
  haveI := D0.toDivisorOver.isIntegral
  haveI := D0.toDivisorOver.isDominant
  obtain ⟨J0, hJ0, hJ0ft, e, he⟩ := MMP.exists_blowUp_iso_of_isProjective_of_isBirational
    (U0.ι ≫ ι ≫ sX) D0.f hD0p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D0.isBirationalMorphism)
  obtain ⟨-, -, hisoU, -, hlift, -⟩ :=
    MMP.Blowup.isBirational_blowUpToBase_and_exists_iso_blowUp (U0.ι ≫ ι ≫ sX) J0 hJ0 hJ0ft
  -- the ideals `J' ⊆ 𝒪_T` and `J ⊆ 𝒪_X`
  set J' : T.IdealSheafData := (J0.subschemeι ≫ U0.ι).ker with hJ'
  have hJ'U : J'.comap U0.ι = J0 := AlgebraicGeometry.ker_comap_eq_of_isOpenImmersion U0 J0
  set J : X.IdealSheafData := (J'.subschemeι ≫ ι).ker with hJdef
  have hJT : J.comap ι = J' := by
    rw [hJdef, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : Limits.pullback.fst ι (J'.subschemeι ≫ ι) =
        Limits.pullback.snd ι (J'.subschemeι ≫ ι) ≫ J'.subschemeι := by
      rw [← cancel_mono ι, Category.assoc, Limits.pullback.condition]
    rw [h, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]
  -- the generic point of `U₀` is not in `V(J₀)`
  have hηJ0 : genericPoint U0.toScheme ∉ J0.support := by
    intro h
    refine hJ0 (Scheme.IdealSheafData.support_eq_top_iff.1 ?_)
    refine top_le_iff.1 fun z _ => ?_
    have hz : genericPoint U0.toScheme ⤳ z := genericPoint_specializes z
    exact hz.mem_closed J0.support.isClosed h
  refine ⟨J, ?_, ?_⟩
  · -- the support of `J` lies in `P` and misses its generic point
    intro x hx
    have h1 : (J.support : Set X) = closure (Set.range (J'.subschemeι ≫ ι)) :=
      Scheme.Hom.support_ker _
    have hxr : x ∈ Set.range ι := by
      have hx' : x ∈ closure (Set.range (J'.subschemeι ≫ ι)) := h1 ▸ hx
      refine closure_minimal ?_ ι.isClosedEmbedding.isClosed_range hx'
      rintro _ ⟨z, rfl⟩
      exact ⟨J'.subschemeι z, rfl⟩
    obtain ⟨t, rfl⟩ := hxr
    have hPsp : ∀ t' : T, P.genericPoint ⤳ ι t' := fun t' => by
      have : ι t' ∈ (P.support : Set X) := hP ▸ ⟨t', rfl⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.2 this
    have hgP := map_genericPoint_eq ι P hP
    have ht : t ≠ genericPoint T := by
      rintro rfl
      have h2 : genericPoint T ∈ ((J.comap ι).support : Set T) := by
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage]
        exact hx
      rw [hJT] at h2
      have h4 : genericPoint U0.toScheme ∈ ((J'.comap U0.ι).support : Set _) := by
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
          map_genericPoint_of_isDominant]
        exact h2
      rw [hJ'U] at h4
      exact hηJ0 h4
    exact two_le_coheight_of_specializes P (hPsp t)
      fun h => ht (ι.isClosedEmbedding.injective (h.trans hgP.symm))
  · intro W g hW hg hgp hJW
    haveI := hgp
    haveI : IsIntegral W := hW.1.toIsIntegral
    haveI : LocallyOfFiniteType (g ≫ ι ≫ sX) := hW.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (g ≫ ι ≫ sX)
    rw [Scheme.IdealSheafData.comap_comp, hJT] at hJW
    set Vg : W.Opens := g ⁻¹ᵁ U0 with hVg
    haveI : IsDominant g := hg.isDominant
    haveI : Nonempty Vg := ⟨⟨genericPoint W, show g (genericPoint W) ∈ U0 by
      rw [map_genericPoint_of_isDominant]
      exact ((genericPoint_spec T).mem_open_set_iff U0.isOpen).2 ⟨x0, trivial, hx0U⟩⟩⟩
    have hJ0V : Stacks.Divisors.IsEffectiveCartierDivisor (J0.comap (g ∣_ U0)) := by
      rw [← hJ'U, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι,
        Scheme.IdealSheafData.comap_comp]
      exact isEffectiveCartierDivisor_comap_of_isOpenImmersion _ hJW Vg.ι
    obtain ⟨φ, hφ, -⟩ := hlift (g ∣_ U0) hJ0V
    have hψ0 : (φ ≫ e.inv) ≫ D0.f = g ∣_ U0 := by
      rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hφ]
    set G0 : DivisorOver k (ι ≫ sX) := compDivisorOver U0.ι hU0v hU0b D0.toDivisorOver with hG0d
    have hG0 : G0.valuation = F.valuation := by
      rw [hG0d, valuation_compDivisorOver, hv0]
      exact congrArg (Valuation.comap (functionFieldMap U0.ι)) hD0v
    have hgen' : ∀ z : D0.Y, U0.ι (D0.f z) = genericPoint T → z = genericPoint D0.Y := by
      intro z hz2
      have hz' : D0.f z = genericPoint U0.toScheme := by
        apply U0.ι.isOpenEmbedding.injective
        rw [hz2, map_genericPoint_of_isDominant U0.ι]
      have hbir : genericPoint U0.toScheme ∈ biregularLocus (blowUpToBase J0) :=
        le_biregularLocus hisoU hηJ0
      have h7 : blowUpToBase J0 (e.hom z) = genericPoint U0.toScheme := by
        rw [← Scheme.Hom.comp_apply, he, hz']
      have h8 : blowUpToBase J0 (e.hom (genericPoint D0.Y)) = genericPoint U0.toScheme := by
        rw [← Scheme.Hom.comp_apply, he, map_genericPoint_of_isDominant D0.f]
      have h9 := eq_of_map_eq_of_mem_biregularLocus (h7.trans h8.symm) (h7 ▸ hbir)
      exact e.hom.isOpenEmbedding.injective h9
    have hgen : ∀ z : G0.Y, G0.f z = genericPoint T →
        z = (haveI := G0.isIntegral; genericPoint G0.Y) := fun z hz => hgen' z hz
    refine exists_primeDivisor_valuation_eq_of_lift hT F G0 hG0 hgen g hW hg Vg (φ ≫ e.inv)
      ?_ fun w hw => ?_
    · change (φ ≫ e.inv) ≫ D0.f ≫ U0.ι = Vg.ι ≫ g
      rw [← Category.assoc, hψ0, morphismRestrict_ι]
    · show g w ∈ U0
      rw [hw]
      exact hx0U

/-! ### A log resolution principalizing `Ĵ` -/

/-- A variety is a disjoint union of varieties, with one component. -/
private theorem isDisjointUnionOfVarieties_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k sX) :
    MMP.Resolution.IsDisjointUnionOfVarieties sX := by
  haveI := hX
  haveI : IsIntegral X := hX.toIsIntegral
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro C hC C' hC' hne
  rw [irreducibleComponents_eq_singleton] at hC hC'
  exact absurd (hC.trans hC'.symm) hne

/-- If the end result of a blow-up sequence of a variety is nonempty, it is a variety. -/
private theorem isVariety_toBase {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : MMP.Resolution.ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)),
      AlgebraicGeometry.IsVariety k sX → Nonempty B.target →
        AlgebraicGeometry.IsVariety k (B.toBase ≫ sX)
  | X, .nil _, sX, hX, _ => by
    change AlgebraicGeometry.IsVariety k (𝟙 X ≫ sX)
    rwa [Category.id_comp]
  | X, .cons Z B, sX, hX, hne => by
    haveI := hX
    have hZ : Z ≠ ⊥ := by
      rintro rfl
      haveI := AlgebraicGeometry.isEmpty_blowUp_bot X
      obtain ⟨y⟩ := hne
      exact isEmptyElim (B.toBase y)
    have h := (MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      sX Z hZ).1
    have := isVariety_toBase B _ h hne
    change AlgebraicGeometry.IsVariety k ((B.toBase ≫ blowUpToBase Z) ≫ sX)
    rwa [Category.assoc]

/-- A morphism which is an isomorphism over a nonempty open has points over it. -/
private theorem nonempty_preimage_of_isIso_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (V : X.Opens)
    [IsIso (g ∣_ V)] (hV : (V : Set X).Nonempty) : ((g ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨(inv (g ∣_ V) ⟨x, hx⟩).1, (inv (g ∣_ V) ⟨x, hx⟩).2⟩

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (g : Y ⟶ X) (V : X.Opens) [IsIso (g ∣_ V)]
    (hV : (V : Set X).Nonempty) : IsBirationalMorphism g := by
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
    (nonempty_preimage_of_isIso_restrict g V hV) hV le_rfl ?_
  rwa [Scheme.Hom.resLE_eq_morphismRestrict]

/-- An open of `X` which is smooth over `k` lies in the smooth locus. -/
private theorem le_smoothLocus_of_isSmoothScheme {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {U : X.Opens}
    (hU : IsSmoothScheme (U.ι ≫ sX)) : U ≤ smoothLocus sX := by
  have : LocallyOfFinitePresentation (U.ι ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := U.ι ≫ sX)).mpr inferInstance
  exact le_smoothLocus _ ((isSmoothScheme_iff _).1 hU)

/-- An open in the smooth locus is smooth over `k`. -/
private theorem isSmoothScheme_of_le_smoothLocus {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) {U : X.Opens} (hU : U ≤ smoothLocus sX) :
    IsSmoothScheme (U.ι ≫ sX) := by
  refine top_le_iff.1 fun x' _ => ?_
  obtain ⟨V, hxV, hV⟩ := mem_smoothLocus_iff.1 (hU x'.2)
  refine mem_smoothLocus_iff.2 ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  haveI := hV
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι U.ι (le_refl (U.ι ⁻¹ᵁ V)), Category.assoc]
  infer_instance

/-- A point of the support of an ideal sheaf with principal stalks which has no proper
generization in the support has coheight at most one. -/
private theorem coheight_le_one_of_principal {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    {η : Y} (hη : η ∈ I.support) (hmax : ∀ η' ∈ I.support, η' ⤳ η → η ⤳ η') :
    Order.coheight η ≤ 1 := by
  obtain ⟨h, hh⟩ := hI η
  have hmin : IsLocalRing.maximalIdeal _ ∈ (Ideal.span {h}).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun P hP _ => ?_⟩
    · rw [← hh]
      exact IsLocalRing.le_maximalIdeal
        ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).not.2 (not_not.2 hη))
    · obtain ⟨hPp, hPh⟩ := hP
      let p : PrimeSpectrum (Y.presheaf.stalk η) := ⟨P, hPp⟩
      have hp1 : Y.fromSpecStalk η p ∈ I.support := by
        have : p ∈ Y.fromSpecStalk η ⁻¹' (I.support : Set Y) := by
          rw [MMP.Resolution.preimage_fromSpecStalk_support, hh]
          exact (PrimeSpectrum.mem_zeroLocus _ _).2 fun x hx => hPh hx
        exact this
      have hp2 := MMP.Resolution.fromSpecStalk_specializes_self η p
      have heq : Y.fromSpecStalk η p = η := (hp2.antisymm (hmax _ hp1 hp2)).eq
      have hpc : p = IsLocalRing.closedPoint _ := (Y.fromSpecStalk η).isEmbedding.injective
        (heq.trans Scheme.fromSpecStalk_closedPoint.symm)
      change IsLocalRing.maximalIdeal _ ≤ p.asIdeal
      rw [hpc]
      exact le_rfl
  haveI : (Ideal.span {h}).IsPrincipal := ⟨⟨h, rfl⟩⟩
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing _ hmin
  have h2 : (Order.coheight η : WithBot ℕ∞) ≤ 1 := by
    rw [← ringKrullDim_stalk_eq_coheight, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast h1
  exact_mod_cast h2

/-- In a Noetherian space every point of a closed set specializes from a maximal point of it. -/
private theorem exists_maximal_generization {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y]
    [QuasiSober Y] (S : Closeds Y) {y : Y} (hy : y ∈ S) :
    ∃ η ∈ S, η ⤳ y ∧ ∀ η' ∈ S, η' ⤳ η → η ⤳ η' := by
  obtain ⟨-, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf S.isClosed
  obtain ⟨W, hW, hyW⟩ := Set.mem_sUnion.1 (hcov hy)
  have hWc : IsClosed W := MMP.Resolution.Aux.isClosed_of_mem_componentsOf S.isClosed hW
  have hgen := hW.1.1.isGenericPoint_genericPoint_closure
  rw [hWc.closure_eq] at hgen
  refine ⟨hW.1.1.genericPoint, hW.1.2 hgen.mem, hgen.specializes hyW, fun η' hη' hsp => ?_⟩
  have h1 : W ⊆ closure {η'} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
      isClosed_closure
  have h2 := hW.2 ⟨isIrreducible_singleton.closure, closure_minimal
    (Set.singleton_subset_iff.2 hη') S.isClosed⟩ h1
  rw [specializes_iff_mem_closure, hgen.def]
  exact h2 (subset_closure rfl)

/-- The stalks of an effective Cartier divisor are principal. -/
private theorem stalk_principal_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (I : Y.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h} := by
  intro y
  obtain ⟨h, -, hh⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor I hI y
  exact ⟨h, hh⟩

/-- **A resolution principalizing an ideal of codimension two.** Let `X` be a normal variety in
characteristic zero and `I ⊆ 𝒪_X` an ideal whose support has codimension at least two and
contains the singular locus. The strong resolution of the blow-up of `I` is a resolution
`p : X₀ ⟶ X` on which `I 𝒪_{X₀}` is an effective Cartier divisor, and its exceptional set is
`p⁻¹(V(I))`: `p` is an isomorphism over `X ∖ V(I)`, and over `V(I)` by Krull's principal ideal
theorem. -/
private theorem exists_resolution_principalizing {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (I : X.IdealSheafData)
    (hI : ∀ x ∈ I.support, 2 ≤ Order.coheight x)
    (hsing : (singularLocus sX : Set X) ⊆ I.support) :
    ∃ (X0 : Scheme.{u}) (p0 : X0 ⟶ X), MMP.Resolution.IsResolutionOfVariety sX p0 ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p0) ∧
      (exceptionalSet p0 : Set X0) = p0 ⁻¹' (I.support : Set X) := by
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  have hηI : genericPoint X ∉ I.support := fun h => by
    have := hI _ h
    rw [coheight_genericPoint] at this
    exact absurd this (by norm_num)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact hηI (by simp; exact Set.mem_univ _)
  obtain ⟨hBv, hπp, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX I hI0
  haveI := hBv
  haveI : IsIntegral (blowUp I) := hBv.toIsIntegral
  haveI : LocallyOfFiniteType (blowUpToBase I ≫ sX) := hBv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I ≫ sX)
  haveI : QuasiCompact (blowUpToBase I ≫ sX) := hBv.toQuasiCompact
  haveI : CompactSpace (blowUp I) :=
    QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian (blowUp I) := {}
  haveI hπi : IsIso (blowUpToBase I ∣_ I.support.compl) :=
    isIso_blowUpToBase_restrict_compl_support I
  -- the strong resolution of the blow-up
  obtain ⟨BR, hBR, -⟩ := MMP.Resolution.exists_strongResolution_blowupSequenceFunctor.{u}
  have hDU := isDisjointUnionOfVarieties_of_isVariety (blowUpToBase I ≫ sX) hBv
  obtain ⟨hsm₁, hiso₁, -⟩ := hBR (blowUpToBase I ≫ sX) hDU
  set B₁ := BR (blowUpToBase I ≫ sX) hDU with hB₁
  haveI := hiso₁
  set W : X.Opens := I.support.compl with hW
  have hWne : (W : Set X).Nonempty := ⟨genericPoint X, hηI⟩
  -- the blow-up is smooth over `W`
  have hWsm : W ≤ smoothLocus sX := fun x hx => by
    by_contra h
    exact hx (hsing h)
  have hπW : blowUpToBase I ⁻¹ᵁ W ≤ smoothLocus (blowUpToBase I ≫ sX) := by
    apply le_smoothLocus_of_isSmoothScheme
    have hWs : IsSmoothScheme (W.ι ≫ sX) := isSmoothScheme_of_le_smoothLocus sX hWsm
    haveI : Smooth (W.ι ≫ sX) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hWs
    have : LocallyOfFinitePresentation ((blowUpToBase I ⁻¹ᵁ W).ι ≫ blowUpToBase I ≫ sX) :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
    refine (isSmoothScheme_iff _).2 ?_
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  haveI : IsIso (B₁.toBase ∣_ blowUpToBase I ⁻¹ᵁ W) :=
    MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le B₁.toBase hπW
  haveI hp0W : IsIso ((B₁.toBase ≫ blowUpToBase I) ∣_ W) := by
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›
  set p0 := B₁.toBase ≫ blowUpToBase I with hp0
  -- `X₀` is a smooth variety
  have hX0ne : Nonempty B₁.target :=
    let ⟨y, _⟩ := nonempty_preimage_of_isIso_restrict p0 W hWne; ⟨y⟩
  have hX0v : AlgebraicGeometry.IsVariety k (p0 ≫ sX) := by
    rw [hp0, Category.assoc]
    exact isVariety_toBase B₁ _ hBv hX0ne
  haveI := hX0v
  haveI : IsIntegral B₁.target := hX0v.toIsIntegral
  haveI : LocallyOfFiniteType (p0 ≫ sX) := hX0v.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian B₁.target := LocallyOfFiniteType.isLocallyNoetherian (p0 ≫ sX)
  haveI : QuasiCompact (p0 ≫ sX) := hX0v.toQuasiCompact
  haveI : CompactSpace B₁.target := QuasiCompact.compactSpace_of_compactSpace (p0 ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian B₁.target := {}
  have hp0b : IsBirationalMorphism p0 := isBirationalMorphism_of_isIso_restrict p0 W hWne
  haveI : IsDominant p0 := hp0b.isDominant
  have hp0p : IsProjective p0 :=
    (MMP.Resolution.ClosedBlowupSequence.isProjective_toBase B₁).comp hπp
  -- `I 𝒪_{X₀}` is an effective Cartier divisor
  have hL : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap p0) := by
    rw [hp0, Scheme.IdealSheafData.comap_comp]
    refine isEffectiveCartierDivisor_comap_of_genericPoint_notMem _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) B₁.toBase ?_
    intro h
    have h' : B₁.toBase (genericPoint B₁.target) ∈
        ((I.comap (blowUpToBase I)).support : Set (blowUp I)) := h
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, ← hp0, map_genericPoint_of_isDominant] at h'
    exact hηI h'
  -- the exceptional set
  have hWV : W ≤ biregularLocus p0 := le_biregularLocus hp0W
  have hEx : (exceptionalSet p0 : Set B₁.target) = p0 ⁻¹' (I.support : Set X) := by
    apply Set.Subset.antisymm
    · intro y hy
      by_contra hyI
      exact hy (hWV hyI)
    · intro y hy hyV
      have hyL : y ∈ (I.comap p0).support := by
        change y ∈ ((I.comap p0).support : Set B₁.target)
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
        exact hy
      obtain ⟨η, hηL, hηy, hηmax⟩ := exists_maximal_generization (I.comap p0).support hyL
      have h1 := coheight_le_one_of_principal (I.comap p0)
        (stalk_principal_of_isEffectiveCartierDivisor _ hL) hηL hηmax
      have hηV : p0 η ∈ biregularLocus p0 :=
        (hηy.map p0.continuous).mem_open (biregularLocus p0).isOpen hyV
      have h2 := MMP.Positivity.coheight_map_of_mem_biregularLocus p0 hηV
      have hηI' : p0 η ∈ I.support := by
        have : η ∈ ((I.comap p0).support : Set B₁.target) := hηL
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at this
        exact this
      have h3 := hI _ hηI'
      rw [h2] at h3
      exact absurd (h3.trans h1) (by norm_num)
  refine ⟨B₁.target, p0, ⟨hXv, hX0v, hp0p, hp0b, ?_⟩, hL, hEx⟩
  rw [hp0, Category.assoc]
  exact hsm₁

/-- If `a ≫ b` is an isomorphism, `a` is dominant, the source of `b` is reduced and `b` is
separated, then `b` is an isomorphism. -/
private theorem isIso_of_isIso_comp {A B V : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ V) [IsIso (a ≫ b)]
    [IsDominant a] [IsReduced B] [IsSeparated b] : IsIso b := by
  refine ⟨⟨inv (a ≫ b) ≫ a, ?_, by simp⟩⟩
  refine ext_of_isDominant_of_isSeparated b ?_ a ?_
  · simp
  · rw [← Category.assoc, IsIso.hom_inv_id_assoc, Category.comp_id]

/-- If `h ≫ g` is an isomorphism over `V`, with `h` dominant, `X'` reduced and `g` separated,
then `g` is an isomorphism over `V` and `h` over `g⁻¹(V)`. -/
private theorem isBiregular_of_isBiregular_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] {V : X.Opens}
    (hV : IsBiregular (h ≫ g) V) : IsBiregular g V ∧ IsBiregular h (g ⁻¹ᵁ V) := by
  unfold IsBiregular at hV ⊢
  rw [morphismRestrict_comp] at hV
  have : IsDominant (h ∣_ g ⁻¹ᵁ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant h› _
  have : IsSeparated (g ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsSeparated g› _
  have := @isIso_of_isIso_comp _ _ _ (h ∣_ g ⁻¹ᵁ V) (g ∣_ V) hV _ _ _
  exact ⟨this, @IsIso.of_isIso_comp_right _ _ _ _ _ _ (g ∣_ V) this hV⟩

/-- The exceptional set of a composite. -/
private theorem exceptionalSet_comp {Y X' X : Scheme.{u}} (h : Y ⟶ X') (g : X' ⟶ X)
    [IsDominant h] [IsReduced X'] [IsSeparated g] [UniversallyClosed g] :
    exceptionalSet (h ≫ g) = exceptionalSet h ⊔ (exceptionalSet g).preimage h.continuous := by
  apply SetLike.coe_injective
  ext y
  change y ∈ exceptionalSet (h ≫ g) ↔ y ∈ exceptionalSet h ∨ h y ∈ exceptionalSet g
  simp only [mem_exceptionalSet]
  constructor
  · intro hy
    by_contra hne
    push Not at hne
    obtain ⟨hyh, hyg⟩ := hne
    apply hy
    have hcl : IsClosed (g '' (biregularLocus h : Set X')ᶜ) :=
      g.isClosedMap _ (biregularLocus h).isOpen.isClosed_compl
    let W : X.Opens := biregularLocus g ⊓ ⟨_, hcl.isOpen_compl⟩
    have hWg : IsBiregular g W :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have hWh : IsBiregular h (g ⁻¹ᵁ W) := by
      refine isBiregular_iff_le_biregularLocus.mpr ?_
      intro x hx
      by_contra hxU
      exact hx.2 ⟨x, hxU, rfl⟩
    have hiso : IsBiregular (h ≫ g) W := by
      unfold IsBiregular at *
      rw [morphismRestrict_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hWh hWg
    refine le_biregularLocus hiso ⟨hyg, ?_⟩
    rintro ⟨x, hx, hxy⟩
    have hxy' : g x = g (h y) := hxy.trans (Scheme.Hom.comp_apply h g y)
    have hx' : g x ∈ biregularLocus g := hxy' ▸ hyg
    exact hx (eq_of_map_eq_of_mem_biregularLocus hxy' hx' ▸ hyh)
  · intro hy hmem
    have hb := isBiregular_of_isBiregular_comp h g (isBiregular_biregularLocus (h ≫ g))
    rcases hy with hy | hy
    · exact hy (le_biregularLocus hb.2 hmem)
    · exact hy (le_biregularLocus hb.1 hmem)

open MMP.Resolution in
/-- A member of an snc family with irreducible support is a prime divisor. -/
private theorem exists_primeDivisor_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (i : ι) (hirr : IsIrreducible ((F i).support : Set X)) :
    ∃ P : PrimeDivisor X, P.idealSheaf = F i := by
  have hint := isIntegral_subscheme_of_isIrreducible s (F i) (hF.1 i).2.2 hirr
  refine ⟨⟨F i, hint, ?_⟩, rfl⟩
  have hcl := closure_subschemeι_genericPoint (F i)
  refine (hF.1 i).2.1 _ ⟨show closure _ ⊆ _ from hcl.le, fun V hV _ => ?_⟩
  exact show (V : Set X) ⊆ closure _ from hcl ▸ hV

open MMP.Resolution in
/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData} (hF : IsSNCFamily s F)
    (D : DivisorWithCoeffs ℤ X) (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

open MMP.Resolution in
/-- A divisor with simple normal crossings in the sense of `IsSNCClosedSubset` is one in the
sense of `MMP.Mori.IsSNCSubset`. -/
private theorem isSNCSubset_of_isSNCClosedSubset {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [NoetherianSpace X] {S : Closeds X}
    (hS : IsSNCClosedSubset sX (S : Set X)) : IsSNCSubset sX S := by
  classical
  obtain ⟨-, h | ⟨-, hfin, hfam⟩⟩ := hS
  · exact Or.inl (Closeds.ext (by rw [h]; rfl))
  · right
    have : Fintype (componentsOf (S : Set X)) := hfin.fintype
    have hP : ∀ W : componentsOf (S : Set X), ∃ P : PrimeDivisor X,
        P.idealSheaf = componentsFamily (S : Set X) W := fun W =>
      exists_primeDivisor_of_isSNCFamily hfam W (by
        rw [coe_support_componentsFamily S.isClosed W]; exact W.2.1.1)
    choose P hP using hP
    have hPs : ∀ W, (P W).support = (W : Set X) := fun W => by
      change ((P W).idealSheaf.support : Set X) = _
      rw [hP, coe_support_componentsFamily S.isClosed W]
    refine ⟨Finset.univ.image P, ?_, ?_⟩
    · apply Set.Subset.antisymm
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.iUnion_exists,
          Set.iUnion_iUnion_eq', Set.iUnion_subset_iff]
        intro W
        rw [hPs]
        exact W.2.1.2
      · intro x hx
        obtain ⟨-, hcov⟩ := Aux.finite_and_cover_componentsOf S.isClosed
        obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
        refine Set.mem_biUnion (x := P ⟨W, hW⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_
        rw [hPs]
        exact hxW
    · refine isSNC_of_isSNCFamily hfam _ fun Q hQ => ?_
      obtain ⟨E, hE, hQE⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hQ)
      have hQ' : Q = E := Finset.mem_singleton.1 (Finsupp.support_single_subset hQE)
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hE
      exact ⟨W, by rw [hQ', hP]⟩

/-- The support of an ideal sheaf with principal stalks on an integral locally Noetherian scheme
which misses the generic point is of pure codimension one. -/
private theorem isPureCodimOne_support_of_principal {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [NoetherianSpace Y] (I : Y.IdealSheafData)
    (hI : ∀ y, ∃ h, IdealSheafData.stalk I y = Ideal.span {h})
    (hgen : genericPoint Y ∉ I.support) : IsPureCodimOne I.support := by
  intro W hW
  set e := irreducibleSetEquivPoints (α := Y)
  have hWη : (W : Set Y) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have hηW : e W ∈ (W : Set Y) := by rw [hWη]; exact subset_closure rfl
  have hηI : e W ∈ I.support := hW.1 hηW
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  have hle := coheight_le_one_of_principal I hI hηI fun η' hη' hsp => by
    let W' : IrreducibleCloseds Y :=
      ⟨closure {η'}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hWW' : W ≤ W' := by
      change (W : Set Y) ⊆ closure {η'}
      rw [hWη]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp))
        isClosed_closure
    have h2 := hW.2 (y := W') (closure_minimal (Set.singleton_subset_iff.2 hη') I.support.isClosed)
      hWW'
    rw [specializes_iff_mem_closure, ← hWη]
    exact h2 (subset_closure rfl)
  have hne : Order.coheight (e W) ≠ 0 := by
    intro h0
    have : e W = genericPoint Y := eq_genericPoint_of_coheight_eq_zero h0
    exact hgen (this ▸ hηI)
  exact le_antisymm hle (ENat.one_le_iff_ne_zero.2 hne)

/-- A union of two closed subsets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_sup {T : Type*} [TopologicalSpace T] {A B : Closeds T}
    (hA : IsPureCodimOne A) (hB : IsPureCodimOne B) : IsPureCodimOne (A ⊔ B) := by
  intro W hW
  have hWsub : (W : Set T) ⊆ (A : Set T) ∪ B := hW.1
  classical
  have key : (W : Set T) ⊆ A ∨ (W : Set T) ⊆ B := by
    obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp W.isIrreducible
      {(A : Set T), (B : Set T)} (by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact A.isClosed
        · exact B.isClosed) (by
        intro x hx
        rcases hWsub hx with h | h
        · exact ⟨A, by simp, h⟩
        · exact ⟨B, by simp, h⟩)
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hWz
    · exact Or.inr hWz
  rcases key with h | h
  · exact hA W ⟨h, fun W' hW' hle => hW.2 (hW'.trans Set.subset_union_left) hle⟩
  · exact hB W ⟨h, fun W' hW' hle => hW.2 (hW'.trans Set.subset_union_right) hle⟩

/-- The stalk of a sum of ideal sheaves is the sum of the stalks. -/
private theorem stalk_sup {X : Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU,
    IdealSheafData.stalk_eq_map_germ J x ⟨U, hU⟩ hxU, ← Ideal.map_sup]
  rfl

/-- If `ξ ⤳ y`, the stalk of `J` at `y` is contained in that of `I`, and `ξ` lies in the support
of `I`, then `ξ` lies in the support of `J`. -/
private theorem mem_support_of_specializes_of_stalk_le {Y : Scheme.{u}} {I J : Y.IdealSheafData}
    {ξ y : Y} (h : ξ ⤳ y) (hle : IdealSheafData.stalk J y ≤ IdealSheafData.stalk I y)
    (hI : ξ ∈ I.support) : ξ ∈ J.support := by
  by_contra hJ
  have h1 := Ideal.map_mono (f := (Y.presheaf.stalkSpecializes h).hom) hle
  rw [stalk_map_stalkSpecializes, stalk_map_stalkSpecializes,
    (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).2 hJ] at h1
  exact (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).1 (top_le_iff.1 h1) hI

/-- In a local ring, if `a + b` is generated by a non-zero-divisor `m`, then `a = (m)` or
`b = (m)`. -/
private theorem eq_span_or_eq_span_of_sup_eq_span {R : Type*} [CommRing R] [IsLocalRing R]
    {a b : Ideal R} {m : R} (hm : IsRegular m) (h : a ⊔ b = Ideal.span {m}) :
    a = Ideal.span {m} ∨ b = Ideal.span {m} := by
  have hma : m ∈ a ⊔ b := h ▸ Ideal.mem_span_singleton_self m
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hma
  have hx' : x ∈ Ideal.span {m} := h ▸ Ideal.mem_sup_left hx
  have hy' : y ∈ Ideal.span {m} := h ▸ Ideal.mem_sup_right hy
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hx'
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hy'
  have hrt : r + t = 1 := by
    apply hm.2
    change (r + t) * m = 1 * m
    rw [add_mul, hr, ht, one_mul, hxy]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hrt with hu | hu
  · left
    refine le_antisymm (h ▸ le_sup_left) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := hu
    have : m = ↑u⁻¹ * x := by rw [← hr, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact a.mul_mem_left _ hx
  · right
    refine le_antisymm (h ▸ le_sup_right) ?_
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := hu
    have : m = ↑u⁻¹ * y := by rw [← ht, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact b.mul_mem_left _ hy

/-- **A log resolution of `(X, S + B)` principalizing an ideal.** Let `X` be a normal variety in
characteristic zero, `S` a prime divisor, `B` a `ℚ`-divisor without component `S` and `J` an
ideal sheaf whose support has codimension at least two. There is a log resolution
`f : Y ⟶ X` of `(X, S + B)` such that the strict transform `S'` of `S` meets no prime divisor
lying over a point of `Supp B ∖ S`, and `J 𝒪_Y` is an effective Cartier divisor. -/
private theorem exists_isLogResolution_disjoint_isEffectiveCartierDivisor {k : Type u} [Field k]
    [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (S : PrimeDivisor X) {B : QDivisor X} (hB : B.coeff S = 0)
    (J : X.IdealSheafData) (hJ : ∀ x ∈ J.support, 2 ≤ Order.coheight x) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      Mori.IsLogResolution sX
        (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f ∧
      IsNormalVariety k (f ≫ sX) ∧
      ∃ S' : PrimeDivisor Y, inverseTransformPrimeDivisor f S = some S' ∧
        (∀ Γ : PrimeDivisor Y, f Γ.genericPoint ∈ B.supp → f Γ.genericPoint ∉ S.support →
          Disjoint (S'.support : Set Y) Γ.support) ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (J.comap f) := by
  classical
  haveI hXv : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : AlgebraicGeometry.IsNoetherian X := {}
  have hS1 : Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) = Finsupp.single S (1 : ℚ) := by
    rw [MMP.Threefold.Resolution.toQDivisor_single]; simp
  set Δ : QDivisor X := Finsupp.single S 1 + B with hΔ
  set IB : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal B.supp with hIB
  set ISg : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (singularLocus sX) with hISg
  set I : X.IdealSheafData := J * (S.idealSheaf ⊔ IB) * ISg with hIdef
  have hSB : S.genericPoint ∉ (B.supp : Set X) := by
    intro h
    obtain ⟨P, hP, hSP⟩ := DivisorWithCoeffs.mem_supp_iff.1 h
    rw [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hSP] at hP
    exact hP hB
  have hmemI : ∀ x, x ∈ (I.support : Set X) ↔ (x ∈ (J.support : Set X) ∨
      (x ∈ (S.support : Set X) ∧ x ∈ (B.supp : Set X))) ∨ x ∈ (singularLocus sX : Set X) := by
    intro x
    simp only [hIdef, Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_sup, hIB,
      hISg, Closeds.coe_sup, Closeds.coe_inf, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Set.mem_union, Set.mem_inter_iff]
  have hI2 : ∀ x ∈ I.support, 2 ≤ Order.coheight x := by
    intro x hx
    rcases (hmemI x).1 hx with (hxJ | ⟨hxS, hxB⟩) | hxs
    · exact hJ x hxJ
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxS
      exact two_le_coheight_of_specializes S (specializes_iff_mem_closure.2 hxS)
        (fun h => hSB (h ▸ hxB))
    · have h0 : Order.coheight x ≠ 0 := fun h => by
        have := eq_genericPoint_of_coheight_eq_zero h
        exact hxs (this ▸ MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus')
      have h1 : Order.coheight x ≠ 1 := fun h => by
        have := MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h)
        have hg : MMP.Mori.PrimeDivisor.genericPoint
            (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h) = x :=
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h
        rw [hg] at this
        exact hxs this
      generalize Order.coheight x = c at h0 h1 ⊢
      induction c using ENat.recTopCoe with
      | top => exact le_top
      | coe c =>
        norm_cast at h0 h1 ⊢
        omega
  have hsing : (singularLocus sX : Set X) ⊆ I.support := fun x hx => (hmemI x).2 (Or.inr hx)
  obtain ⟨X0, p0, hres, hL, hEx0⟩ := exists_resolution_principalizing hX I hI2 hsing
  -- the smooth model `X₀`
  have hX0v : AlgebraicGeometry.IsVariety k (p0 ≫ sX) := hres.isVariety_source
  haveI := hX0v
  haveI : IsIntegral X0 := hX0v.toIsIntegral
  haveI : LocallyOfFiniteType (p0 ≫ sX) := hX0v.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X0 := LocallyOfFiniteType.isLocallyNoetherian (p0 ≫ sX)
  haveI : QuasiCompact (p0 ≫ sX) := hX0v.toQuasiCompact
  haveI : CompactSpace X0 := QuasiCompact.compactSpace_of_compactSpace (p0 ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian X0 := {}
  have hX0n : IsNormal X0 :=
    isNormal_of_isRegular X0
      (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hres.isSmoothScheme)
  haveI := hX0n
  have hX0 : IsNormalVariety k (p0 ≫ sX) := ⟨hX0v, hX0n⟩
  haveI : IsProper p0 := hres.isProjective.isProper
  have hp0b := hres.isBirationalMorphism
  haveI : IsDominant p0 := hp0b.isDominant
  -- the prime divisors of `X₀` over `V(I) ∪ Supp Δ`
  set C : Set X0 := p0 ⁻¹' ((I.support : Set X) ∪ (Δ.supp : Set X)) with hC
  have hCc : IsClosed C := (I.support.isClosed.union Δ.supp.isClosed).preimage p0.continuous
  have hηX : genericPoint X ∉ (I.support : Set X) ∪ (Δ.supp : Set X) := by
    rintro (h | h)
    · have := hI2 _ h
      rw [coheight_genericPoint] at this
      exact absurd this (by norm_num)
    · obtain ⟨P, -, hP⟩ := DivisorWithCoeffs.mem_supp_iff.1 h
      exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support P hP
  have hCcoh : ∀ s ∈ C, Order.coheight s ≠ 0 := by
    intro s hs h0
    rw [eq_genericPoint_of_coheight_eq_zero h0] at hs
    exact hηX (by rw [← map_genericPoint_of_isDominant p0]; exact hs)
  have hfinD := finite_setOf_genericPoint_mem hCc hCcoh
  set D0 := hfinD.toFinset with hD0
  have hmemD0 : ∀ P : PrimeDivisor X0, P ∈ D0 ↔ P.genericPoint ∈ C := fun P => by
    rw [hD0, Set.Finite.mem_toFinset]; rfl
  have hcov : ∀ x ∈ C, ∃ P ∈ D0, x ∈ P.support := by
    intro x hx
    by_cases hxI : p0 x ∈ (I.support : Set X)
    · have hxL : x ∈ (I.comap p0).support := by
        change x ∈ ((I.comap p0).support : Set X0)
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
        exact hxI
      obtain ⟨η, hηL, hηx, hηmax⟩ := exists_maximal_generization (I.comap p0).support hxL
      have hηC : η ∈ C := by
        have : η ∈ ((I.comap p0).support : Set X0) := hηL
        rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at this
        exact Or.inl this
      have h1 := coheight_le_one_of_principal (I.comap p0)
        (stalk_principal_of_isEffectiveCartierDivisor _ hL) hηL hηmax
      have hcoh : Order.coheight η = 1 :=
        le_antisymm h1 (ENat.one_le_iff_ne_zero.2 (hCcoh η hηC))
      have hg : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh) = η :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne η hcoh
      refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh, ?_, ?_⟩
      · rw [hmemD0, hg]
        exact hηC
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        change x ∈ closure {(MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hcoh))}
        rw [hg]
        exact specializes_iff_mem_closure.1 hηx
    · have hxD : p0 x ∈ (Δ.supp : Set X) := hx.resolve_left hxI
      obtain ⟨Q, hQ, hxQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hxD
      have hxV : p0 x ∈ biregularLocus p0 := by
        by_contra h
        have : x ∈ (exceptionalSet p0 : Set X0) := h
        rw [hEx0] at this
        exact hxI this
      have hQsp : Q.genericPoint ⤳ p0 x := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxQ
        exact specializes_iff_mem_closure.2 hxQ
      have hηQ : Q.genericPoint ∈ biregularLocus p0 :=
        hQsp.mem_open (biregularLocus p0).isOpen hxV
      obtain ⟨Q', -, hQ'⟩ :=
        MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := p0) Q hηQ
      refine ⟨Q', ?_, ?_⟩
      · rw [hmemD0, hC, Set.mem_preimage, hQ']
        exact Or.inr (DivisorWithCoeffs.mem_supp_iff.2
          ⟨Q, hQ, MMP.Flips.primeDivisor_genericPoint_mem_support Q⟩)
      · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        refine specializes_iff_mem_closure.1 ?_
        set V0 := biregularLocus p0 with hV0
        haveI : IsIso (p0 ∣_ V0) := isBiregular_biregularLocus p0
        let a : (p0 ⁻¹ᵁ V0).toScheme :=
          ⟨Q'.genericPoint, show p0 Q'.genericPoint ∈ V0 from hQ' ▸ hηQ⟩
        let b : (p0 ⁻¹ᵁ V0).toScheme := ⟨x, hxV⟩
        have hab : (p0 ∣_ V0) a ⤳ (p0 ∣_ V0) b := by
          rw [← V0.ι.isOpenEmbedding.isInducing.specializes_iff, ← Scheme.Hom.comp_apply,
            ← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
            Scheme.Hom.comp_apply]
          change p0 Q'.genericPoint ⤳ p0 x
          rw [hQ']
          exact hQsp
        have hab' : a ⤳ b := (p0 ∣_ V0).isOpenEmbedding.isInducing.specializes_iff.1 hab
        exact (p0 ⁻¹ᵁ V0).ι.isOpenEmbedding.isInducing.specializes_iff.2 hab'
  have hsuppD0 : ∀ P ∈ D0, (P.support : Set X0) ⊆ C := by
    intro P hP x hx
    rw [hmemD0] at hP
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hx
    exact closure_minimal (Set.singleton_subset_iff.2 hP) hCc hx
  -- the snc-preserving log resolution of `(X₀, D₀)`
  obtain ⟨Y, f1, hres1, hpure1, hsnc1, -⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (p0 ≫ sX) hX0 D0
  set f := f1 ≫ p0 with hfdef
  have hYv : AlgebraicGeometry.IsVariety k (f ≫ sX) := by
    rw [hfdef, Category.assoc]
    exact hres1.isVariety_source
  haveI := hYv
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hYv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : QuasiCompact (f ≫ sX) := hYv.toQuasiCompact
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI : IsProper f1 := hres1.isProjective.isProper
  have hf1b := hres1.isBirationalMorphism
  haveI : IsDominant f1 := hf1b.isDominant
  have hfb : IsBirationalMorphism f := IsPair.isBirationalMorphism_comp hf1b hp0b
  haveI : IsProper f := by
    rw [hfdef]
    infer_instance
  haveI : IsDominant f := hfb.isDominant
  have hsmY : IsSmoothScheme (f ≫ sX) := by
    rw [hfdef, Category.assoc]
    exact hres1.isSmoothScheme
  have hYn : IsNormal Y :=
    isNormal_of_isRegular Y (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsmY)
  have hY : IsNormalVariety k (f ≫ sX) := ⟨hYv, hYn⟩
  -- `I 𝒪_Y` and the exceptional set of `f`
  have hgenI : genericPoint Y ∉ (I.comap f).support := by
    intro h
    have h' : genericPoint Y ∈ ((I.comap f).support : Set Y) := h
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      map_genericPoint_of_isDominant] at h'
    exact hηX (Or.inl h')
  have hLf : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap f) := by
    rw [hfdef, Scheme.IdealSheafData.comap_comp]
    refine isEffectiveCartierDivisor_comap_of_genericPoint_notMem _ hL f1 ?_
    intro h
    have h' : f1 (genericPoint Y) ∈ ((I.comap p0).support : Set X0) := h
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      map_genericPoint_of_isDominant, map_genericPoint_of_isDominant] at h'
    exact hηX (Or.inl h')
  have hExf : (exceptionalSet f : Set Y) =
      (exceptionalSet f1 : Set Y) ∪ f1 ⁻¹' (exceptionalSet p0 : Set X0) := by
    rw [hfdef, exceptionalSet_comp]
    rfl
  have hExfC : exceptionalSet f = exceptionalSet f1 ⊔ (I.comap f).support := by
    apply SetLike.coe_injective
    rw [hExf, Closeds.coe_sup, hEx0, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage]
    rfl
  have hpure : IsPureCodimOne (exceptionalSet f) := by
    rw [hExfC]
    exact isPureCodimOne_sup hpure1 (isPureCodimOne_support_of_principal _
      (stalk_principal_of_isEffectiveCartierDivisor _ hLf) hgenI)
  -- simple normal crossings
  have hSig : ((exceptionalSet f ⊔ (QDivisor.toRDivisor (Divisor.toQDivisor
      (Finsupp.single S 1) + B)).supp.preimage f.continuous : Closeds Y) : Set Y) =
      (exceptionalSet f1 : Set Y) ∪ f1 ⁻¹' D0.sup fun E => (E.idealSheaf.support : Set X0) := by
    rw [Closeds.coe_sup, Closeds.coe_preimage, QDivisor.supp_toRDivisor, hS1, hExf, hEx0,
      Finset.sup_set_eq_biUnion]
    ext y
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · obtain ⟨P, hP, hyP⟩ := hcov (f1 y) (Or.inl h)
        exact Or.inr ⟨P, hP, hyP⟩
      · obtain ⟨P, hP, hyP⟩ := hcov (f1 y) (Or.inr h)
        exact Or.inr ⟨P, hP, hyP⟩
    · rintro (h | ⟨P, hP, hyP⟩)
      · exact Or.inl (Or.inl h)
      · rcases hsuppD0 P hP hyP with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  have hlog : Mori.IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f := by
    refine ⟨⟨inferInstance, hfb, hsmY⟩, hpure, isSNCSubset_of_isSNCClosedSubset (f ≫ sX) ?_⟩
    rw [hSig, hfdef, Category.assoc]
    exact hsnc1
  -- the strict transform of `S`
  have hbir := two_le_closedsCodimension_compl_biregularLocus (hY := hX.1) (hX := hYv) sX f hfb
  have hηS : S.genericPoint ∈ biregularLocus f := by
    by_contra h
    have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 hbir) _ h
    rw [S.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨S', hS', hfS'⟩ :=
    MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some (g := f) S hηS
  -- `J 𝒪_Y` and `(I_S + I_B) 𝒪_Y` are effective Cartier divisors
  have hprod := hLf
  rw [hIdef, AlgebraicGeometry.comap_mul, AlgebraicGeometry.comap_mul] at hprod
  have hprod' := AlgebraicGeometry.isEffectiveCartierDivisor_left_of_mul _ _ hprod
  have hJf := AlgebraicGeometry.isEffectiveCartierDivisor_left_of_mul _ _ hprod'
  have hMf := AlgebraicGeometry.isEffectiveCartierDivisor_right_of_mul _ _ hprod'
  refine ⟨Y, f, hlog, hY, S', hS', fun Γ hΓB hΓS => ?_, hJf⟩
  -- disjointness from the principalization of `I_S + I_B`
  refine Set.disjoint_left.2 fun y hyS hyΓ => ?_
  obtain ⟨m, hm, hgen⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hMf y
  rw [Scheme.IdealSheafData.comap_sup, stalk_sup] at hgen
  have hspS : S'.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyS
    exact specializes_iff_mem_closure.2 hyS
  have hspΓ : Γ.genericPoint ⤳ y := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyΓ
    exact specializes_iff_mem_closure.2 hyΓ
  have hsuppc : ∀ (K : X.IdealSheafData) (z : Y),
      z ∈ ((K.comap f).support : Set Y) ↔ f z ∈ (K.support : Set X) := fun K z => by
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage]
  have hIBs : (IB.support : Set X) = B.supp := by
    rw [hIB, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hS'S : S'.genericPoint ∈ (S.idealSheaf.comap f).support :=
    (hsuppc _ _).2 (hfS' ▸ MMP.Flips.primeDivisor_genericPoint_mem_support S)
  have hS'B : S'.genericPoint ∉ (IB.comap f).support := fun h =>
    hSB (hIBs ▸ hfS' ▸ (hsuppc _ _).1 h)
  have hΓS' : Γ.genericPoint ∉ (S.idealSheaf.comap f).support := fun h =>
    hΓS ((hsuppc _ _).1 h)
  have hΓB' : Γ.genericPoint ∈ (IB.comap f).support :=
    (hsuppc _ _).2 (hIBs ▸ hΓB)
  rcases eq_span_or_eq_span_of_sup_eq_span hm hgen with ha | hb
  · exact hS'B (mem_support_of_specializes_of_stalk_le hspS
      (le_sup_right.trans (hgen.trans ha.symm).le) hS'S)
  · exact hΓS' (mem_support_of_specializes_of_stalk_le hspΓ
      (le_sup_left.trans (hgen.trans hb.symm).le) hΓB')

end

/-! ### Poincaré residues of `m`-fold forms along a smooth divisor -/

section

open CategoryTheory.Limits

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y]

/-! ### Cartier divisors from local generators -/

/-- If `𝒪_W(m(K + Δ))` has a local generator around every point of a normal variety `W` over a
perfect field, then `m(K + Δ)` is a Cartier divisor. -/
public theorem isCartierDivisor_of_forall_generatesOn [PerfectField k] {W : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (hW : IsNormalVariety k sW) {n : ℕ} {K : Divisor W} (hK : K.IsCanonicalDivisor sW n)
    {Δ : QDivisor W} {m : ℕ}
    (h : ∀ w : W, ∃ U : W.Opens, w ∈ U ∧ ∃ τ : RationalPluriForms sW n m, GeneratesOn Δ m U τ) :
    ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor := by
  classical
  have hn := hK.topologicalKrullDim_eq
  let := functionFieldAlgebra sW
  have : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hW hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hW hK
  choose U hU τ hτ using h
  have hcoef : ∀ (w : W) (Γ : PrimeDivisor W), (Γ.support ∩ U w).Nonempty →
      ((m : ℤ) • (Divisor.toQDivisor K + Δ)).coeff Γ =
        (((m : ℤ) * Γ.ordForm ω - Γ.ordForm (τ w) : ℤ) : ℚ) := by
    intro w Γ hΓ
    have e := (hτ w).2 Γ hΓ
    rw [hω Γ] at *
    change (m : ℤ) • ((K.coeff Γ : ℚ) + Δ.coeff Γ) = _
    push_cast
    rw [zsmul_eq_mul]
    push_cast
    linarith
  obtain ⟨C, hC⟩ := (QDivisor.mem_range_toQDivisor_iff _).mpr fun Γ =>
    ⟨_, hcoef Γ.genericPoint Γ
      ⟨Γ.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ, hU _⟩⟩
  refine ⟨C, hC, fun w => ⟨U w, hU w, ?_⟩⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set c' := (ZTensorPower.basis b m).repr (τ w) () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b (hτ w).1
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero
    (mul_ne_zero (zpow_ne_zero (m : ℤ) hc) (zpow_ne_zero (-1 : ℤ) hc'))
  refine ⟨φ, fun Γ hΓ => ?_⟩
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω0
  have e2 := hN m (τ w) (hτ w).1
  rw [← hc_def] at e1
  rw [← hc'_def] at e2
  have hCΓ : (C.coeff Γ : ℚ) = (((m : ℤ) * Γ.ordForm ω - Γ.ordForm (τ w) : ℤ) : ℚ) := by
    rw [← Divisor.coeff_toQDivisor, hC]
    exact hcoef w Γ hΓ
  have hCΓ' : C.coeff Γ = (m : ℤ) * Γ.ordForm ω - Γ.ordForm (τ w) := by exact_mod_cast hCΓ
  rw [hCΓ', hφ Γ, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
    ord_zpow _ hc', e1, e2]
  ring

section Frames

open IsLocalRing in
/-- **A frame of differentials through `dh`.** If `Ω_{A/k}` is free of rank `e + 1` over a local
ring `A` and `dh` has a retraction `r(dh) = 1`, then `dh, dx₁, …, dxₑ` span `Ω_{A/k}` for some
`x₁, …, xₑ ∈ A`. -/
public theorem exists_span_cons_D_eq_top {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]] {e : ℕ}
    (hrank : Module.finrank A Ω[A⁄k] = e + 1) {h : A} {r : Ω[A⁄k] →ₗ[A] A}
    (hr : r (KaehlerDifferential.D k A h) = 1) :
    ∃ x : Fin e → A, Submodule.span A (Set.range (Fin.cons (KaehlerDifferential.D k A h)
      fun i => KaehlerDifferential.D k A (x i) : Fin (e + 1) → Ω[A⁄k])) = ⊤ := by
  classical
  have := Module.finitePresentation_of_projective A Ω[A⁄k]
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
    (KaehlerDifferential.D k A) (KaehlerDifferential.span_range_derivation k A)
  have : Finite κ := Module.Finite.finite_basis b
  let := Fintype.ofFinite κ
  have hcard : Fintype.card κ = e + 1 := by rw [← Module.finrank_eq_card_basis b, hrank]
  set c := b.repr (KaehlerDifferential.D k A h) with hc
  have hsum : ∑ i, c i • b i = KaehlerDifferential.D k A h := b.sum_repr _
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, IsUnit (c i₀) := by
    by_contra hno
    push Not at hno
    have hmem : r (KaehlerDifferential.D k A h) ∈ maximalIdeal A := by
      rw [← hsum, map_sum]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr (hno i))
    rw [hr] at hmem
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  set s := Finset.univ.erase i₀ with hs_def
  have hs : s.card = e := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]; rfl
  let σ : Fin e ≃ s := (s.equivFinOfCardEq hs).symm
  refine ⟨fun j => a (σ j), ?_⟩
  set N := Submodule.span A (Set.range (Fin.cons (KaehlerDifferential.D k A h)
      fun j => KaehlerDifferential.D k A (a (σ j)) : Fin (e + 1) → Ω[A⁄k])) with hN
  have hmem : ∀ i, i ≠ i₀ → b i ∈ N := by
    intro i hi
    refine Submodule.subset_span ⟨(σ.symm ⟨i, by simp [s, hi]⟩).succ, ?_⟩
    simp [hb]
  have hdh : KaehlerDifferential.D k A h ∈ N := Submodule.subset_span ⟨0, rfl⟩
  rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = i₀
  · subst hi
    have h1 : c i • b i = KaehlerDifferential.D k A h - ∑ j ∈ s, c j • b j := by
      rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      abel
    have h2 : b i = (↑hi₀.unit⁻¹ : A) • (c i • b i) := by
      rw [smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [SetLike.mem_coe, h2, h1]
    exact N.smul_mem _ (N.sub_mem hdh (N.sum_mem fun j hj =>
      N.smul_mem _ (hmem j (Finset.ne_of_mem_erase hj))))
  · exact hmem i hi

/-- The top exterior power of a module spanned by `n` vectors is spanned by their wedge. -/
public theorem span_singleton_ιMulti_eq_top {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {n : ℕ} (v : Fin n → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    Submodule.span R {exteriorPower.ιMulti R n v} = ⊤ := by
  have hid : ∀ g : Fin n ↪o Fin n, (g : Fin n → Fin n) = id := by
    intro g
    have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
    rw [Finset.orderEmbOfFin_unique hc (f := g) (fun _ => Finset.mem_univ _) g.strictMono,
      ← Finset.orderEmbOfFin_unique hc (f := id) (fun _ => Finset.mem_univ _) strictMono_id]
  have h := exteriorPower.ιMulti_family_span_of_span R (n := n) hv
  rw [← h]
  congr 1
  ext w
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    refine ⟨Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin n)).toOrderEmbedding, ?_⟩
    simp only [exteriorPower.ιMulti_family, hid, Function.comp_id]
  · rintro ⟨y, rfl⟩
    simp only [exteriorPower.ιMulti_family, hid, Function.comp_id]

/-- If `dh, dx₁, …, dxₑ` span `Ω_{A/k}` and `A → B` is surjective with `h ↦ 0`, the images
`dx̄₁, …, dx̄ₑ` span `Ω_{B/k}`. -/
public theorem span_range_D_algebraMap_eq_top {k A B : Type*} [CommRing k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (hπ : Function.Surjective (algebraMap A B)) {e : ℕ} {h : A} (hh : algebraMap A B h = 0)
    {x : Fin e → A}
    (hx : Submodule.span A (Set.range (Fin.cons (KaehlerDifferential.D k A h)
      fun i => KaehlerDifferential.D k A (x i) : Fin (e + 1) → Ω[A⁄k])) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D k B (algebraMap A B (x i))) =
      ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation k B, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := hπ b
  have ha : KaehlerDifferential.D k A a ∈ Submodule.span A (Set.range (Fin.cons
      (KaehlerDifferential.D k A h) fun i => KaehlerDifferential.D k A (x i) :
        Fin (e + 1) → Ω[A⁄k])) :=
    hx ▸ Submodule.mem_top
  have hm := Submodule.mem_map_of_mem (f := (KaehlerDifferential.map k k A B).restrictScalars A) ha
  rw [Submodule.map_span] at hm
  simp only [LinearMap.coe_restrictScalars, KaehlerDifferential.map_D] at hm
  have hsub : ⇑(KaehlerDifferential.map k k A B) '' Set.range (Fin.cons
      (KaehlerDifferential.D k A h) fun i => KaehlerDifferential.D k A (x i) :
        Fin (e + 1) → Ω[A⁄k]) ⊆
      insert 0 (Set.range fun i => KaehlerDifferential.D k B (algebraMap A B (x i))) := by
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [KaehlerDifferential.map_D, hh]
    · exact Or.inr ⟨i, by simp [KaehlerDifferential.map_D]⟩
  have hm' := Submodule.span_mono hsub hm
  rw [Submodule.span_insert_zero] at hm'
  exact Submodule.span_le_restrictScalars A B _ hm'

end Frames

section Residue

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- Along an integral closed subscheme `T` of `Y` whose generic point is that of a prime divisor,
the local ring `𝒪_{Y,T}` is a discrete valuation ring, formally smooth over `k`, with free
differentials of finite type and of rank `trdeg_k k(Y)`, and `j(η_T)` has codimension one. -/
public theorem stalk_facts [PerfectField k] [LocallyOfFiniteType sY] {Γ : PrimeDivisor Y}
    (hΓ : j (genericPoint T) = Γ.genericPoint) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra sY
    IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T))) ∧
      Module.Free (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] ∧
      Module.Finite (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] ∧
      Algebra.FormallySmooth k (Y.presheaf.stalk (j (genericPoint T))) ∧
      Order.coheight (j (genericPoint T)) = 1 ∧
      Module.finrank (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] =
          (Algebra.trdeg k Y.functionField).toNat :=
  stalk_facts_of_eq_genericPoint _ hΓ

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The restriction `𝒪_{Y,T} → k(T)` along a closed immersion is a surjective `k`-algebra
map. -/
public theorem stalkMap_facts [IsClosedImmersion j] :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j (genericPoint T))) T.functionField ∧
      Function.Surjective (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) :=
  stalkMap_facts_of_isClosedImmersion

/-- **Uniformizers along `T`**: if `j` sends `η_T` to the generic point of a prime divisor `Γ`,
there is a uniformizer `ϖ` of `𝒪_{Y,T}` with a retraction `r(dϖ) = 1`, and every element of order
one is a unit multiple of `ϖ`. -/
public theorem exists_uniformizer [PerfectField k] [LocallyOfFiniteType sY] [IsClosedImmersion j]
    {Γ : PrimeDivisor Y} (hΓ : j (genericPoint T) = Γ.genericPoint) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    ∃ (ϖ : Y.presheaf.stalk (j (genericPoint T)))
      (r : Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] →ₗ[Y.presheaf.stalk (j (genericPoint T))]
        Y.presheaf.stalk (j (genericPoint T))),
      algebraMap _ T.functionField ϖ = 0 ∧ r (KaehlerDifferential.D k _ ϖ) = 1 ∧
      RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
        Ideal.span {ϖ} ∧
      ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ^ 2 ∧
      ∀ t : Y.presheaf.stalk (j (genericPoint T)),
        Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 →
          ∃ u, IsUnit u ∧ t = u * ϖ :=
  exists_uniformizer_of_eq_genericPoint _ hΓ

/-- **Uniqueness of the Poincaré residue** along an integral closed subscheme `T ⊆ Y` whose generic
point is that of a prime divisor of the normal variety `Y`, over a perfect field. -/
public theorem isPoincareResidue_unique [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] {Γ : PrimeDivisor Y}
    (hΓ : j (genericPoint T) = Γ.genericPoint) {n m : ℕ}
    {τ : RationalPluriForms sY (n + 1) m} {ρ ρ' : RationalPluriForms (j ≫ sY) n m}
    (h : MMP.Fourfold.IsPoincareResidue sY j n m τ ρ)
    (h' : MMP.Fourfold.IsPoincareResidue sY j n m τ ρ') : ρ = ρ' :=
  IsPoincareResidue.unique_of_isClosedImmersion _ hΓ h h'

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The local rings of a smooth variety over a perfect field are essentially of finite type and
formally smooth, with free differentials of rank `trdeg_k k(Y)`. -/
private theorem stalk_facts_of_isSmoothScheme [PerfectField k] [LocallyOfFiniteType sY]
    (hsm : IsSmoothScheme sY) (y : Y) :
    letI := stalkAlgebra sY y
    letI := functionFieldAlgebra sY
    Algebra.FormallySmooth k (Y.presheaf.stalk y) ∧ Algebra.EssFiniteType k (Y.presheaf.stalk y) ∧
      Module.Free (Y.presheaf.stalk y) Ω[(Y.presheaf.stalk y)⁄k] ∧
      Module.Finite (Y.presheaf.stalk y) Ω[(Y.presheaf.stalk y)⁄k] ∧
      Module.finrank (Y.presheaf.stalk y) Ω[(Y.presheaf.stalk y)⁄k] =
        (Algebra.trdeg k Y.functionField).toNat := by
  let := stalkAlgebra sY y
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY y
  obtain ⟨hln, hreg⟩ := (isRegular_iff_regular_stalks Y).1
    (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x : U := ⟨y, hxU⟩
  let := sectionAlgebra sY U
  have := finiteType_sectionAlgebra sY hU'
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) := TopCat.Presheaf.algebra_section_stalk Y.presheaf x
  have := isScalarTower_section_stalk sY U x
  have := hU'.isLocalization_stalk x
  have := hreg y
  set q := (hU'.primeIdealOf x).asIdeal
  have := Algebra.isSeparableExtension_of_perfectField k q.ResidueField
  have hs : Algebra.IsSmoothAt k q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q (Y.presheaf.stalk y)).mpr inferInstance
  have : Algebra.EssFiniteType Γ(Y, U) (Y.presheaf.stalk y) := .of_isLocalization _ q.primeCompl
  have hfs : Algebra.FormallySmooth k (Y.presheaf.stalk y) := Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (Y.presheaf.stalk y)).restrictScalars k)
  have hess : Algebra.EssFiniteType k (Y.presheaf.stalk y) := .comp k Γ(Y, U) _
  have hfree : Module.Free (Y.presheaf.stalk y) Ω[(Y.presheaf.stalk y)⁄k] :=
    Module.free_of_flat_of_isLocalRing
  have hfin : Module.Finite (Y.presheaf.stalk y) Ω[(Y.presheaf.stalk y)⁄k] := inferInstance
  have := essFiniteType_functionField (sX := sY)
  refine ⟨hfs, hess, hfree, hfin, ?_⟩
  rw [← finrank_kaehlerDifferential_eq_of_isFractionRing (K := Y.functionField),
    finrank_kaehlerDifferential_eq_trdeg]

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The specialization map `𝒪_{Y,y} → 𝒪_{Y,ξ}` is `k`-linear. -/
public theorem isScalarTower_stalkSpecializes {ξ y : Y} (h : ξ ⤳ y) :
    letI := stalkAlgebra sY y
    letI := stalkAlgebra sY ξ
    letI : Algebra (Y.presheaf.stalk y) (Y.presheaf.stalk ξ) :=
      (Y.presheaf.stalkSpecializes h).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk y) (Y.presheaf.stalk ξ) := by
  let := stalkAlgebra sY y
  let := stalkAlgebra sY ξ
  let : Algebra (Y.presheaf.stalk y) (Y.presheaf.stalk ξ) :=
    (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have e : (Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ ξ (Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (Opens.mem_top _)) ≫
        Y.presheaf.stalkSpecializes h := by
    simp
  exact congrArg CommRingCat.Hom.hom e

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] in
/-- The stalk map of `j : T ⟶ Y` at `w` is `k`-linear, for the structure `j ≫ s_Y` of `T`. -/
public theorem isScalarTower_stalkMap (w : T) :
    letI := stalkAlgebra sY (j w)
    letI := stalkAlgebra (j ≫ sY) w
    letI : Algebra (Y.presheaf.stalk (j w)) (T.presheaf.stalk w) := (j.stalkMap w).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j w)) (T.presheaf.stalk w) := by
  let := stalkAlgebra sY (j w)
  let := stalkAlgebra (j ≫ sY) w
  let : Algebra (Y.presheaf.stalk (j w)) (T.presheaf.stalk w) := (j.stalkMap w).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  have e : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
        T.presheaf.germ ⊤ w (Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (j w) (Opens.mem_top _)) ≫ j.stalkMap w := by
    simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
    rfl
  exact congrArg CommRingCat.Hom.hom e

open scoped TensorProduct in
/-- Rewriting `c • b^{⊗m}` as `a • (d • b)^{⊗m}` when `a dᵐ = c`. -/
private theorem eq_smul_tprod_of_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis Unit K V) (m : ℕ) {c a d : K} {θ : ZTensorPower K V (m : ℤ)}
    (hθ : c • ZTensorPower.basis b (m : ℤ) () = θ) (had : a * d ^ m = c) :
    θ = (a • PiTensorProduct.tprod K (fun _ : Fin m => d • b ()) : TensorPower K m V) := by
  have hb : ZTensorPower.basis b (m : ℤ) () =
      (PiTensorProduct.tprod K (fun _ : Fin m => b ()) : TensorPower K m V) :=
    ZTensorPower.basis_ofNat b m
  have key : (a • PiTensorProduct.tprod K (fun _ : Fin m => d • b ()) : TensorPower K m V) =
      (c • PiTensorProduct.tprod K (fun _ : Fin m => b ()) : TensorPower K m V) := by
    rw [tprod_const_smul, smul_smul, had]
  rw [key, ← hθ]
  exact congrArg (fun t => c • t) hb

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
open scoped TensorProduct in
/-- **Forms on `T` along a frame from `Y`.** If `dh, dx₁, …, dxₑ` span `Ω_{𝒪_{Y,j(w)}/k}` and `h`
generates the kernel of `𝒪_{Y,j(w)} → 𝒪_{T,w}`, then for `a ∈ 𝒪_{T,w}` the form
`a · (dx̄₁ ∧ ⋯ ∧ dx̄ₑ)^{⊗m}` on `T` is nonzero when `a` is, and has order `ord_w(a)` along the
prime divisor of `T` with generic point `w`. -/
private theorem ordForm_smul_tprod_frame [IsClosedImmersion j] [IsLocallyNoetherian T]
    [LocallyOfFiniteType (j ≫ sY)] {e : ℕ}
    (hTrank : Module.finrank T.functionField
      (letI := functionFieldAlgebra (j ≫ sY); Ω[T.functionField⁄k]) = e)
    (w : T) {h : Y.presheaf.stalk (j w)} (hker : RingHom.ker (j.stalkMap w).hom = Ideal.span {h})
    {x : Fin e → Y.presheaf.stalk (j w)}
    (hx : letI := stalkAlgebra sY (j w)
      Submodule.span (Y.presheaf.stalk (j w)) (Set.range (Fin.cons (KaehlerDifferential.D k _ h)
        fun i => KaehlerDifferential.D k _ (x i) : Fin (e + 1) → Ω[(Y.presheaf.stalk (j w))⁄k])) =
          ⊤)
    (m : ℕ) (a : T.functionField) (ρ : RationalPluriForms (j ≫ sY) e m)
    (hρ : letI := functionFieldAlgebra (j ≫ sY)
      ρ = (a • PiTensorProduct.tprod T.functionField
        (fun _ : Fin m => exteriorPower.ιMulti T.functionField e fun i =>
          KaehlerDifferential.D k T.functionField
            (algebraMap _ T.functionField ((j.stalkMap w).hom (x i)))) :
        TensorPower T.functionField m (⋀[T.functionField]^e Ω[T.functionField⁄k]))) :
    (a ≠ 0 → ρ ≠ 0) ∧ ∀ G : PrimeDivisor T, G.genericPoint = w →
      G.ordForm ρ = T.ord a w := by
  let := functionFieldAlgebra (j ≫ sY)
  let := stalkAlgebra sY (j w)
  let := stalkAlgebra (j ≫ sY) w
  let : Algebra (Y.presheaf.stalk (j w)) (T.presheaf.stalk w) := (j.stalkMap w).hom.toAlgebra
  have := isScalarTower_stalkMap (sY := sY) (j := j) w
  have := isScalarTower_stalk_functionField (j ≫ sY) w
  have : FiniteDimensional T.functionField Ω[T.functionField⁄k] := by
    have := essFiniteType_functionField (sX := j ≫ sY)
    exact (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k T.functionField).1
  have hnt := nontrivial_exteriorPower_of_finrank_eq k T.functionField hTrank
  have hhker : algebraMap (Y.presheaf.stalk (j w)) (T.presheaf.stalk w) h = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self h)
  have hspanT := span_range_D_algebraMap_eq_top (k := k) (A := Y.presheaf.stalk (j w))
    (B := T.presheaf.stalk w) (j.stalkMap_surjective w) hhker hx
  have hσT := span_singleton_ιMulti_eq_top _ hspanT
  have h0T := topFormsMap_ne_zero_of_span_eq_top (K := T.functionField) hσT
  have hWT : topFormsMap k (T.presheaf.stalk w) T.functionField e
      (exteriorPower.ιMulti _ e fun i => KaehlerDifferential.D k (T.presheaf.stalk w)
        (algebraMap (Y.presheaf.stalk (j w)) (T.presheaf.stalk w) (x i))) =
      exteriorPower.ιMulti T.functionField e fun i => KaehlerDifferential.D k T.functionField
        (algebraMap _ T.functionField ((j.stalkMap w).hom (x i))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    simp only [KaehlerDifferential.map_D]
    rfl
  have hρ' : ρ = a •
      ZTensorPower.basis (topFormsBasis (T.presheaf.stalk w) hσT h0T) (m : ℤ) () := by
    rw [hρ]
    refine ((eq_smul_tprod_of_eq (K := T.functionField) _ m (θ := (a •
        ZTensorPower.basis (topFormsBasis (T.presheaf.stalk w) hσT h0T) (m : ℤ) ())) rfl
      (by rw [one_pow, mul_one])).trans ?_).symm
    rw [topFormsBasis_apply, hWT, one_smul]
  have hρc : formCoeff (k := k) (m := (m : ℤ)) (T.presheaf.stalk w) hσT h0T
      (a •
        ZTensorPower.basis (topFormsBasis (T.presheaf.stalk w) hσT h0T) (m : ℤ) ()) =
      a := by
    rw [formCoeff_smul]
    simp [formCoeff]
  have hρc' : formCoeff (k := k) (m := (m : ℤ)) (T.presheaf.stalk w) hσT h0T
      (ρ : PluriForms k T.functionField e m) = a :=
    (congrArg (formCoeff (k := k) (m := (m : ℤ)) (T.presheaf.stalk w) hσT h0T) hρ').trans hρc
  refine ⟨fun ha hρ0 => ?_, ?_⟩
  · have hc := (formCoeff_eq_zero_iff (k := k) (m := (m : ℤ)) hσT h0T
      (ρ : PluriForms k T.functionField e m)).mpr hρ0
    rw [hρc'] at hc
    exact ha hc
  · rintro G rfl
    rw [PrimeDivisor.ordForm_eq G ρ hσT h0T, hρc']

open scoped TensorProduct in
/-- **The residue of a form and its order at a point.** Let `T ⊆ Y` be an integral closed
subscheme of a smooth variety, whose generic point is that of a prime divisor `Γ`, `w ∈ T` with
`y = j(w)`, `h ∈ 𝒪_{Y,y}` cutting out `T` at `y` with `ord_Γ(h) = 1` and `h ∉ 𝔪_y²`, `π ∈ 𝒪_{Y,y}`
a unit along `T`, and `θ` a nonzero rational `m`-canonical form with
`ord_D(θ) = β ord_D(π) - m ord_D(h)` along every prime divisor `D ∋ y`. Then `θ` has a nonzero
Poincaré residue `ρ` along `T`, and `ord_G(ρ) = β ord_w(π̄)` for the prime divisor `G` of `T` with
generic point `w`. -/
private theorem exists_isPoincareResidue_ordForm [PerfectField k] [LocallyOfFiniteType sY]
    (hsmY : IsSmoothScheme sY) [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ sY)]
    [IsLocallyNoetherian T]
    {Γ : PrimeDivisor Y} (hΓ : j (genericPoint T) = Γ.genericPoint) {e m : ℕ}
    (he : (letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat) = e + 1)
    (θ : RationalPluriForms sY (e + 1) m) (hθ0 : θ ≠ 0) (w : T) {h π : Y.presheaf.stalk (j w)}
    (β : ℤ) (hker : RingHom.ker (j.stalkMap w).hom = Ideal.span {h})
    (hh2 : h ∉ IsLocalRing.maximalIdeal (Y.presheaf.stalk (j w)) ^ 2)
    (hhΓ : Y.ord (algebraMap _ Y.functionField h) Γ.genericPoint = 1)
    (hπ : ∀ hζ : j (genericPoint T) ⤳ j w, IsUnit ((Y.presheaf.stalkSpecializes hζ).hom π))
    (hD : ∀ D : PrimeDivisor Y, j w ∈ D.support →
      D.ordForm θ = β * Y.ord (algebraMap _ Y.functionField π) D.genericPoint -
        m * Y.ord (algebraMap _ Y.functionField h) D.genericPoint) :
    ∃ ρ : RationalPluriForms (j ≫ sY) e m, MMP.Fourfold.IsPoincareResidue sY j e m θ ρ ∧
      ρ ≠ 0 ∧ ∀ G : PrimeDivisor T, G.genericPoint = w →
        G.ordForm ρ = β * T.ord (algebraMap _ T.functionField ((j.stalkMap w).hom π)) w := by
  classical
  let := stalkAlgebra sY (j w)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (j w)
  obtain ⟨hfs, hess, hfree, hfin, hrank⟩ := stalk_facts_of_isSmoothScheme hsmY (j w)
  rw [he] at hrank
  have hsurj : Function.Surjective (j.stalkMap w).hom := j.stalkMap_surjective w
  have hhm : h ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (j w)) := by
    have : h ∈ RingHom.ker (j.stalkMap w).hom := hker ▸ Ideal.mem_span_singleton_self h
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have h1 := RingHom.mem_ker.mp this
    exact (hu.map (j.stalkMap w).hom).ne_zero h1
  -- a retraction of `dh` and a frame `dh, dx₁, …, dxₑ` at `y`
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (Y.presheaf.stalk (j w))) :=
    Algebra.EssFiniteType.of_surjective (IsScalarTower.toAlgHom k (Y.presheaf.stalk (j w)) _)
      IsLocalRing.residue_surjective
  have hkerκ : RingHom.ker (algebraMap (Y.presheaf.stalk (j w))
      (IsLocalRing.ResidueField (Y.presheaf.stalk (j w)))) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (j w)) := IsLocalRing.ker_residue
  obtain ⟨r, hr⟩ := MMP.Fourfold.exists_retraction_D (k := k)
    (L := IsLocalRing.ResidueField (Y.presheaf.stalk (j w))) IsLocalRing.residue_surjective
    (by rwa [hkerκ]) (by rwa [hkerκ])
  obtain ⟨x, hx⟩ := exists_span_cons_D_eq_top hrank hr
  set vA : Fin (e + 1) → Ω[(Y.presheaf.stalk (j w))⁄k] :=
    Fin.cons (KaehlerDifferential.D k _ h) fun i => KaehlerDifferential.D k _ (x i) with hvA
  have hσA := span_singleton_ιMulti_eq_top vA hx
  have := essFiniteType_functionField (sX := sY)
  have hKrank : Module.finrank Y.functionField Ω[Y.functionField⁄k] = e + 1 :=
    (finrank_kaehlerDifferential_eq_trdeg k Y.functionField).trans he
  have : FiniteDimensional Y.functionField Ω[Y.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k Y.functionField).1
  have := nontrivial_exteriorPower_of_finrank_eq k Y.functionField hKrank
  have h0A := topFormsMap_ne_zero_of_span_eq_top (K := Y.functionField) hσA
  set c := formCoeff (k := k) (m := (m : ℤ)) (Y.presheaf.stalk (j w)) hσA h0A θ with hc_def
  have hθ := formCoeff_smul_basis (k := k) (m := (m : ℤ)) hσA h0A
    (θ : PluriForms k Y.functionField (e + 1) m)
  rw [← hc_def] at hθ
  -- the order of `θ` along a prime divisor through `y` is the order of `c`
  have hbasis : ∀ {B : Type u} [CommRing B] [Algebra k B] [Algebra B Y.functionField]
      [IsScalarTower k B Y.functionField] [IsFractionRing B Y.functionField]
      {σ : ⋀[B]^(e + 1) Ω[B⁄k]} (hσ : Submodule.span B {σ} = ⊤)
      (h0 : topFormsMap k B Y.functionField (e + 1) σ ≠ 0),
      topFormsMap k B Y.functionField (e + 1) σ =
        topFormsMap k (Y.presheaf.stalk (j w)) Y.functionField (e + 1)
          (exteriorPower.ιMulti _ (e + 1) vA) →
      formCoeff (k := k) (m := (m : ℤ)) B hσ h0 θ = c := by
    intro B _ _ _ _ _ σ hσ h0 hσσ
    have hb : ZTensorPower.basis (topFormsBasis B hσ h0) (m : ℤ) () =
        ZTensorPower.basis (topFormsBasis (Y.presheaf.stalk (j w)) hσA h0A) (m : ℤ) () := by
      refine (ZTensorPower.basis_ofNat _ m).trans (Eq.trans ?_ (ZTensorPower.basis_ofNat _ m).symm)
      rw [topFormsBasis_apply, topFormsBasis_apply, hσσ]
    conv_lhs => rw [← hθ]
    rw [formCoeff_smul, ← hb]
    simp [formCoeff]
  have hordc : ∀ D : PrimeDivisor Y, j w ∈ D.support → D.ordForm θ = Y.ord c D.genericPoint := by
    intro D hDy
    have hsp : D.genericPoint ⤳ j w := by
      rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hDy
    let := stalkAlgebra sY D.genericPoint
    have := isScalarTower_stalk_functionField sY D.genericPoint
    let : Algebra (Y.presheaf.stalk (j w)) (Y.presheaf.stalk D.genericPoint) :=
      (Y.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := isScalarTower_stalkSpecializes (sY := sY) hsp
    have hloc := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have hσD := span_singleton_topFormsMap (k := k) (K := Y.presheaf.stalk D.genericPoint)
      (d := e + 1) ((IsLocalRing.maximalIdeal (Y.presheaf.stalk D.genericPoint)).comap
        (Y.presheaf.stalkSpecializes hsp).hom).primeCompl hσA
    have hσDK : topFormsMap k (Y.presheaf.stalk D.genericPoint) Y.functionField (e + 1)
        (topFormsMap k (Y.presheaf.stalk (j w)) (Y.presheaf.stalk D.genericPoint) (e + 1)
          (exteriorPower.ιMulti _ (e + 1) vA)) =
        topFormsMap k (Y.presheaf.stalk (j w)) Y.functionField (e + 1)
          (exteriorPower.ιMulti _ (e + 1) vA) := by
      simp only [topFormsMap_ιMulti]
      congr 1
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [vA, Fin.cons_zero, KaehlerDifferential.map_D]
        congr 1
        exact MMP.Mori.algebraMap_stalkSpecializes hsp h
      · simp only [vA, Fin.cons_succ, KaehlerDifferential.map_D]
        congr 1
        exact MMP.Mori.algebraMap_stalkSpecializes hsp (x i)
    have h0D : topFormsMap k (Y.presheaf.stalk D.genericPoint) Y.functionField (e + 1)
        (topFormsMap k (Y.presheaf.stalk (j w)) (Y.presheaf.stalk D.genericPoint) (e + 1)
          (exteriorPower.ιMulti _ (e + 1) vA)) ≠ 0 := by
      rw [hσDK]; exact h0A
    rw [PrimeDivisor.ordForm_eq D θ hσD h0D]
    exact congrArg (fun a => Y.ord a D.genericPoint) (hbasis hσD h0D hσDK)
  -- `c · h^m` is a unit multiple of `π^β` (algebraic Hartogs)
  have hTw : genericPoint T ⤳ w := (genericPoint_spec T).specializes trivial
  have hζ : j (genericPoint T) ⤳ j w := hTw.map j.continuous
  have hsp : ∀ a, algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes hζ).hom a) =
      algebraMap _ Y.functionField a :=
    fun a => MMP.Mori.algebraMap_stalkSpecializes hζ a
  have hπu := hπ hζ
  have hπK : algebraMap _ Y.functionField π ≠ 0 := by
    rw [← hsp]
    exact (hπu.map _).ne_zero
  have hhK : algebraMap _ Y.functionField h ≠ 0 := by
    intro h0
    rw [h0] at hhΓ
    have := congrFun Scheme.ord_zero Γ.genericPoint
    simp only [Pi.zero_apply] at this
    omega
  have hc0 : c ≠ 0 :=
    (formCoeff_eq_zero_iff (k := k) (m := (m : ℤ)) hσA h0A
      (θ : PluriForms k Y.functionField (e + 1) m)).not.mpr
      hθ0
  have hq0 : c * algebraMap _ Y.functionField h ^ (m : ℤ) *
      algebraMap _ Y.functionField π ^ (-β) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc0 (zpow_ne_zero _ hhK)) (zpow_ne_zero _ hπK)
  obtain ⟨u, hu, huq⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero (j w) hq0
    fun D hDy => by
      rw [Scheme.ord_mul (mul_ne_zero hc0 (zpow_ne_zero _ hhK)) (zpow_ne_zero _ hπK),
        Scheme.ord_mul hc0 (zpow_ne_zero _ hhK), ord_zpow _ hhK, ord_zpow _ hπK, ← hordc D hDy,
        hD D hDy]
      ring
  -- the coefficient `g = u π^β`, a unit of `𝒪_{Y,T}`
  obtain ⟨g, hg_def⟩ : ∃ g : Y.presheaf.stalk (j (genericPoint T)),
      g = (Y.presheaf.stalkSpecializes hζ).hom u * ((hπu.unit ^ β : (Y.presheaf.stalk _)ˣ) :
        Y.presheaf.stalk (j (genericPoint T))) := ⟨_, rfl⟩
  have hunits : ∀ (R : CommRingCat.{u}) (S : Type u) [CommRing S] (φ : R →+* S) (v : Rˣ) (n : ℤ),
      φ ((v ^ n : Rˣ) : R) = ((Units.map φ.toMonoidHom v ^ n : Sˣ) : S) := by
    intro R S _ φ v n
    rw [← map_zpow, Units.coe_map]
    rfl
  have hgK : algebraMap _ Y.functionField g = c * algebraMap _ Y.functionField h ^ (m : ℤ) := by
    rw [hg_def, map_mul, hunits, hsp, Units.val_zpow_eq_zpow_val, Units.coe_map]
    change algebraMap _ Y.functionField u *
      (algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes hζ).hom π)) ^ β = _
    rw [hsp, huq, mul_assoc, ← zpow_add₀ hπK, neg_add_cancel, zpow_zero, mul_one]
  have hgu : IsUnit g := by
    rw [hg_def]
    exact (hu.map _).mul (Units.isUnit _)
  -- the representation at the generic point of `T`
  let := functionFieldAlgebra (j ≫ sY)
  have hW : topFormsMap k (Y.presheaf.stalk (j w)) Y.functionField (e + 1)
      (exteriorPower.ιMulti _ (e + 1) vA) =
      exteriorPower.ιMulti Y.functionField (e + 1)
        (Fin.cons (KaehlerDifferential.D k Y.functionField (algebraMap _ Y.functionField h))
          fun i => KaehlerDifferential.D k Y.functionField
            (algebraMap _ Y.functionField (x i))) := by
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [vA, Fin.cons_zero, KaehlerDifferential.map_D]
    · simp only [vA, Fin.cons_succ, KaehlerDifferential.map_D]
  have hrep : θ = (algebraMap _ Y.functionField g • PiTensorProduct.tprod Y.functionField
      (fun _ : Fin m => (algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes hζ).hom h))⁻¹ •
        exteriorPower.ιMulti Y.functionField (e + 1)
          (Fin.cons (KaehlerDifferential.D k Y.functionField
              (algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes hζ).hom h)))
            fun i => KaehlerDifferential.D k Y.functionField
              (algebraMap _ Y.functionField ((Y.presheaf.stalkSpecializes hζ).hom (x i))))) :
        TensorPower Y.functionField m
          (⋀[Y.functionField]^(e + 1) Ω[Y.functionField⁄k])) := by
    simp only [hsp]
    rw [← hW, ← topFormsBasis_apply (A := Y.presheaf.stalk (j w)) hσA h0A ()]
    refine eq_smul_tprod_of_eq _ m hθ ?_
    rw [hgK, inv_pow, ← zpow_natCast, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hhK), mul_one]
  -- the dimension of `k(T)`
  have hTrank : Module.finrank T.functionField Ω[T.functionField⁄k] = e := by
    let := stalkAlgebra sY (j (genericPoint T))
    let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    obtain ⟨hdvr, hfree', hfin', hsm', -, hrank'⟩ := stalk_facts (sY := sY) hΓ
    obtain ⟨htow, hsurjT⟩ := stalkMap_facts (sY := sY) (j := j)
    obtain ⟨ϖ, -, -, -, hkerϖ, hϖ2, -⟩ := exists_uniformizer (sY := sY) hΓ
    have := essFiniteType_functionField (sX := j ≫ sY)
    have h1 := MMP.Fourfold.finrank_kaehlerDifferential_add_one (k := k) hsurjT hkerϖ hϖ2
    rw [hrank', he] at h1
    omega
  have hspT : ∀ a : Y.presheaf.stalk (j w), (j.stalkMap (genericPoint T)).hom
      ((Y.presheaf.stalkSpecializes hζ).hom a) =
        algebraMap (T.presheaf.stalk w) T.functionField ((j.stalkMap w).hom a) := fun a =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint T) w hTw a
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : RationalPluriForms (j ≫ sY) e m, ρ =
      ((j.stalkMap (genericPoint T)).hom g •
        PiTensorProduct.tprod T.functionField (fun _ : Fin m => exteriorPower.ιMulti
          T.functionField e fun i => KaehlerDifferential.D k T.functionField
            ((j.stalkMap (genericPoint T)).hom ((Y.presheaf.stalkSpecializes hζ).hom (x i)))) :
        TensorPower T.functionField m (⋀[T.functionField]^e Ω[T.functionField⁄k])) := ⟨_, rfl⟩
  have hρ : ρ = ((j.stalkMap (genericPoint T)).hom g •
      PiTensorProduct.tprod T.functionField
        (fun _ : Fin m => exteriorPower.ιMulti T.functionField e fun i =>
          KaehlerDifferential.D k T.functionField
            (algebraMap _ T.functionField ((j.stalkMap w).hom (x i)))) :
        TensorPower T.functionField m (⋀[T.functionField]^e Ω[T.functionField⁄k])) := by
    rw [hρ_def]
    simp only [hspT]
    rfl
  obtain ⟨hne, hord⟩ := ordForm_smul_tprod_frame (sY := sY) hTrank w hker hx m _ ρ hρ
  have hga : (j.stalkMap (genericPoint T)).hom g =
      (j.stalkMap (genericPoint T)).hom ((Y.presheaf.stalkSpecializes hζ).hom u) *
        ((j.stalkMap (genericPoint T)).hom ((Y.presheaf.stalkSpecializes hζ).hom π)) ^ β := by
    rw [hg_def, map_mul, hunits, Units.val_zpow_eq_zpow_val, Units.coe_map]
    rfl
  have hju : IsUnit ((j.stalkMap (genericPoint T)).hom
      ((Y.presheaf.stalkSpecializes hζ).hom u)) := (hu.map _).map _
  have hjπ : IsUnit ((j.stalkMap (genericPoint T)).hom
      ((Y.presheaf.stalkSpecializes hζ).hom π)) := hπu.map _
  refine ⟨ρ, ⟨(Y.presheaf.stalkSpecializes hζ).hom h, g,
    fun i => (Y.presheaf.stalkSpecializes hζ).hom (x i), ?_, hrep, hρ_def⟩,
    hne (hgu.map _).ne_zero, ?_⟩
  · rw [hsp, hΓ]; exact hhΓ
  · rintro G rfl
    rw [hord G rfl, hga, Scheme.ord_mul hju.ne_zero (zpow_ne_zero _ hjπ.ne_zero),
      ord_zpow _ hjπ.ne_zero, hspT π]
    have h0 : T.ord ((j.stalkMap (genericPoint T)).hom
        ((Y.presheaf.stalkSpecializes hζ).hom u)) G.genericPoint = 0 := by
      rw [hspT u]
      exact G.ord_algebraMap_of_isUnit (hu.map _)
    rw [h0, zero_add]

end Residue

section BaseChange

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The images of the other members of a regular system of parameters form one in the quotient by
one member. -/
private theorem exists_isRegularSystemOfParameters_of_surjective {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] (ψ : A →+* B)
    (hψ : Function.Surjective ψ) {n : ℕ} {z : Fin n → A} (hz : IsRegularSystemOfParameters z)
    {m : Fin n} (hker : RingHom.ker ψ = Ideal.span {z m}) :
    ∃ (n' : ℕ) (z' : Fin n' → B) (σ : {i : Fin n // i ≠ m} → Fin n'),
      IsRegularSystemOfParameters z' ∧ Function.Injective σ ∧ ∀ i, z' (σ i) = ψ (z i.1) := by
  classical
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hsop⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {m}
  have hs : Ideal.span (z '' (({m} : Finset (Fin n)) : Set (Fin n))) = RingHom.ker ψ := by
    rw [hker]
    simp
  let e : (A ⧸ Ideal.span (z '' (({m} : Finset (Fin n)) : Set (Fin n)))) ≃+* B :=
    (Ideal.quotEquivOfEq hs).trans (RingHom.quotientKerEquivOfSurjective hψ)
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = ψ a := fun a => rfl
  set emb := (({m} : Finset (Fin n))ᶜ).orderEmbOfFin rfl
  have hrange : ∀ i : {i : Fin n // i ≠ m}, ∃ k, emb k = i.1 := by
    intro i
    have hr := Finset.range_orderEmbOfFin (({m} : Finset (Fin n))ᶜ) rfl
    rw [← Set.mem_range, hr]
    simpa using i.2
  refine ⟨_, e ∘ fun j => Ideal.Quotient.mk _ (z (emb j)), fun i => (hrange i).choose,
    IsRegularSystemOfParameters.map_ringEquiv e hsop, ?_, ?_⟩
  · intro i i' h
    apply Subtype.ext
    rw [← (hrange i).choose_spec, ← (hrange i').choose_spec]
    exact congrArg emb h
  · intro i
    simp only [Function.comp_apply, he]
    rw [(hrange i).choose_spec]

/-- The inverse transform of a component of `Δ` meeting the biregular locus is a component of the
inverse transform of `Δ`. -/
private theorem mem_support_inverseTransformDivisor {A B : Scheme.{u}} (h : A ⟶ B) {R : Type*}
    [AddCommMonoid R] (Δ : DivisorWithCoeffs R B) {E : PrimeDivisor B} (hE : E ∈ Δ.support)
    {F : PrimeDivisor A} (hF : inverseTransformPrimeDivisor h E = some F) :
    F ∈ (inverseTransformDivisor h Δ).support := by
  classical
  have hEg :=
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hF).1
  rw [Finsupp.mem_support_iff]
  change (DivisorWithCoeffs.mapPrimeDivisors (inverseTransformPrimeDivisor h) Δ) F ≠ 0
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finset.sum_eq_single E]
  · rw [hF]
    simpa using Finsupp.mem_support_iff.mp hE
  · intro D _ hDE
    cases hD : inverseTransformPrimeDivisor h D with
    | none => simp
    | some F' =>
      simp only [Option.elim_some, Finsupp.singleAddHom_apply]
      rw [Finsupp.single_apply, ite_eq_right]
      rintro rfl
      have hDg :=
        (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1
      apply hDE
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hDg.symm.trans hEg)
  · exact fun hE' => absurd hE hE'

/-- A member of a regular system of parameters does not lie in `𝔪²`. -/
private theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {N : ℕ} {z : Fin N → R} (hz : IsRegularSystemOfParameters z) (i : Fin N) :
    z i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  obtain ⟨hmem, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  intro h
  exact hli.ne_zero i ((Ideal.toCotangent_eq_zero _ _).mpr h)

/-- The length of a regular system of parameters of `𝒪_{X,y}` is the codimension of `y`. -/
private theorem coheight_eq_of_isRegularSystemOfParameters {X : Scheme.{u}} {y : X} {N : ℕ}
    {z : Fin N → X.presheaf.stalk y} (hz : IsRegularSystemOfParameters z) :
    Order.coheight y = N := by
  have h := hz.2
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- On a scheme with discrete valuation rings at points of codimension one, the order of an element
of the local ring at such a point is its length order. -/
private theorem ord_algebraMap_eq_ringOrd {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {y : Y} (h1 : Order.coheight y = 1) {b : Y.presheaf.stalk y} (hb : b ≠ 0) :
    Y.ord (algebraMap _ Y.functionField b) y = ((Ring.ord (Y.presheaf.stalk y) b).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le h1.le
  have hnz : b ∈ nonZeroDivisors (Y.presheaf.stalk y) := mem_nonZeroDivisors_of_ne_zero hb
  have hfin : Ring.ord (Y.presheaf.stalk y) b ≠ ⊤ := Ring.ord_ne_top hnz
  have hne : algebraMap _ Y.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb
  rw [Scheme.ord_eq_iff h1 hne]
  change Ring.ordFrac (Y.presheaf.stalk y) (algebraMap _ _ b) = _
  rw [Ring.ordFrac_eq_ord _ hb,
    Ring.ordMonoidWithZeroHom_eq_coe _ hnz (ENat.natCast_toNat hfin).symm]

omit [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X] [IsNormal Y] in
open Classical in
/-- **Orders of a local equation of a prime divisor.** At a point `y` of a prime divisor `E` of a
smooth scheme, a generator `π` of the ideal of `E` has order one along `E` and order zero along
every other prime divisor through `y`, and it is a unit at every generization of `y` off `E`. -/
private theorem ord_algebraMap_of_stalk_idealSheaf_eq_span [IsIntegral Y] {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType sY] (hsmY : IsSmoothScheme sY) {E : PrimeDivisor Y} {y : Y}
    (hyE : y ∈ E.support) {π : Y.presheaf.stalk y}
    (hπ : IdealSheafData.stalk E.idealSheaf y = Ideal.span {π}) :
    (∀ D : PrimeDivisor Y, y ∈ D.support →
      Y.ord (algebraMap _ Y.functionField π) D.genericPoint = if D = E then 1 else 0) ∧
    ∀ (ξ : Y) (h : ξ ⤳ y), ξ ∉ E.support → IsUnit ((Y.presheaf.stalkSpecializes h).hom π) := by
  have hηE := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE
  have hprime : MMP.Intersection.primeOfSpecializes hηE = Ideal.span {π} :=
    (MMP.Resolution.Aux.primeOfSpecializes_genericPoint sY hsmY E hyE).trans hπ
  -- a generization at which `π` vanishes lies on `E`
  have hnot : ∀ (ξ : Y) (h : ξ ⤳ y), π ∈ MMP.Intersection.primeOfSpecializes h →
      ξ ∈ E.support := by
    intro ξ h hmem
    have hle : MMP.Intersection.primeOfSpecializes hηE ≤ MMP.Intersection.primeOfSpecializes h := by
      rwa [hprime, Ideal.span_singleton_le_iff_mem]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact MMP.Intersection.specializes_of_primeOfSpecializes_le hηE h hle
  have hunit : ∀ (ξ : Y) (h : ξ ⤳ y), ξ ∉ E.support →
      IsUnit ((Y.presheaf.stalkSpecializes h).hom π) := by
    intro ξ h hξ
    by_contra hnu
    exact hξ (hnot ξ h ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  refine ⟨fun D hyD => ?_, hunit⟩
  have hηD := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD
  rw [← MMP.Mori.algebraMap_stalkSpecializes hηD π]
  split_ifs with hDE
  · subst hDE
    have h1 := MMP.Intersection.ord_stalkSpecializes_eq_one hηD hprime
    have hπ0 : π ≠ 0 := by
      rintro rfl
      have hgen : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes trivial
      have hmem := hnot _ hgen (zero_mem _)
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure] at hmem
      have heq : D.genericPoint = genericPoint Y :=
        (hmem.antisymm (genericPoint_specializes _)).eq
      have h0 := coheight_genericPoint Y
      rw [← heq, D.coheight_genericPoint] at h0
      exact one_ne_zero h0
    have hne : (Y.presheaf.stalkSpecializes hηD).hom π ≠ 0 := fun h0 =>
      hπ0 (MMP.Intersection.stalkSpecializes_injective hηD (h0.trans (map_zero _).symm))
    rw [ord_algebraMap_eq_ringOrd D.coheight_genericPoint hne, h1]
    rfl
  · have hDE' : D.genericPoint ∉ E.support := by
      intro hmem
      exact hDE (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem).symm
    exact D.ord_algebraMap_of_isUnit (hunit _ hηD hDE')

omit [CompactSpace X] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **Non-exceptional prime divisors of a log resolution.** A prime divisor `D` of `Y` that is not
`f`-exceptional maps onto a prime divisor `P` of `X`, the order along `D` of a pulled-back form is
its order along `P`, and `D` is a component of `f⁻¹_*Δ` as soon as `P` is a component of `Δ`. -/
private theorem exists_primeDivisor_of_not_isExceptional {Δ : QDivisor X}
    (hX : IsNormalVariety k sX)
    {f : Y ⟶ X} (hf : Mori.IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hY : IsNormalVariety k (f ≫ sX)) {D : PrimeDivisor Y}
    (hD : ¬ RationalMap.IsExceptional f.toRationalMap D) :
    ∃ P : PrimeDivisor X, f D.genericPoint = P.genericPoint ∧
      (∀ {n : ℕ} {m : ℤ} (τ : RationalPluriForms sX n m),
        (⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, D⟩ :
          DivisorOver k sX).ordPullback τ = P.ordForm τ) ∧
      (P ∈ Δ.support → D ∈ (inverseTransformDivisor f Δ).support) := by
  have := hf.isProper
  have : IsIntegral Y := hY.1.toIsIntegral
  set DD : DivisorOver k sX := ⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, D⟩
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX DD hD
  have hfP : f D.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hv' : ∀ g, DD.valuation g = P.divisorialValuation g := fun g => by
    rw [hv]
    change P.divisorialValuation (functionFieldMap (𝟙 X) g) = _
    rw [MMP.Mori.functionFieldMap_id_apply]
  refine ⟨P, hfP, fun τ => DD.ordPullback_eq_ordForm_of_valuation_eq P hv' τ, fun hP => ?_⟩
  have hbir : P.genericPoint ∈ biregularLocus f :=
    MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX f hY.1
      hf.toIsSmoothResolution.isBirationalMorphism
      (by
        rw [ringKrullDim_stalk_eq_coheight, P.coheight_genericPoint]
        rfl)
  obtain ⟨F, hF, hFg⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P hbir
  have hFD : F = D := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_map_eq_of_mem_biregularLocus (hFg.trans hfP.symm) (hFg ▸ hbir))
  rw [← hFD]
  exact mem_support_inverseTransformDivisor f Δ hP hF

omit [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X] in
/-- **The snc condition at a codimension-one point of `T`.** Let `T` be a component of an snc
divisor on `Y`, `j : P ⟶ Y` a closed immersion of a normal integral scheme cut out at `j(w)` by
the ideal of `T`, with `w` of codimension one. Then at most one other component of the snc divisor
in `B` passes through `j(w)`, and the local equation of such a component restricts to a
uniformizer at `w`. -/
private theorem snc_at_codim_one {R : Type*} [Zero R] {Y P S : Scheme.{u}}
    [IsLocallyNoetherian Y] {s : Y ⟶ S} {D' : DivisorWithCoeffs R Y} (hsnc : D'.IsSNC s)
    {B : Finset (PrimeDivisor Y)} (hBD : ∀ D ∈ B, D ∈ D'.support) {T : PrimeDivisor Y}
    (hT : T ∈ D'.support) (hTB : T ∉ B) {j : P ⟶ Y} [IsClosedImmersion j] [IsIntegral P]
    [IsLocallyNoetherian P] [IsNormal P] (w : P) (hw : Order.coheight w = 1)
    (hyT : j w ∈ T.support)
    (hker : RingHom.ker (j.stalkMap w).hom = IdealSheafData.stalk T.idealSheaf (j w)) :
    (∀ D₁ ∈ B, ∀ D₂ ∈ B, j w ∈ D₁.support → j w ∈ D₂.support → D₁ = D₂) ∧
      ∀ D₀ ∈ B, j w ∈ D₀.support → ∃ π : Y.presheaf.stalk (j w),
        IdealSheafData.stalk D₀.idealSheaf (j w) = Ideal.span {π} ∧
          P.ord (algebraMap _ P.functionField ((j.stalkMap w).hom π)) w = 1 := by
  obtain ⟨N, z, jj, hz, hjj, hI⟩ := hsnc.2 (j w)
  have hker' : RingHom.ker (j.stalkMap w).hom = Ideal.span {z (jj ⟨T, hT, hyT⟩)} :=
    hker.trans (hI ⟨T, hT, hyT⟩)
  obtain ⟨N', z', σ, hz', hσ, hσz⟩ :=
    exists_isRegularSystemOfParameters_of_surjective _ (j.stalkMap_surjective w) hz hker'
  have hN' : N' = 1 := by
    have := coheight_eq_of_isRegularSystemOfParameters hz'
    rw [hw] at this
    exact_mod_cast this.symm
  subst hN'
  have hne : ∀ D (hD : D ∈ B) (hyD : j w ∈ D.support),
      jj ⟨D, hBD D hD, hyD⟩ ≠ jj ⟨T, hT, hyT⟩ := fun D hD hyD h => by
    have hDT : D = T := congrArg Subtype.val (hjj h)
    exact hTB (hDT ▸ hD)
  refine ⟨fun D₁ hD₁ D₂ hD₂ hy₁ hy₂ => ?_, fun D₀ hD₀ hy₀ => ?_⟩
  · have h0 : σ ⟨_, hne D₁ hD₁ hy₁⟩ = σ ⟨_, hne D₂ hD₂ hy₂⟩ := Fin.subsingleton_one.elim _ _
    exact congrArg Subtype.val (hjj (congrArg Subtype.val (hσ h0)))
  · refine ⟨z (jj ⟨D₀, hBD D₀ hD₀, hy₀⟩), hI ⟨D₀, hBD D₀ hD₀, hy₀⟩, ?_⟩
    have hzw := hσz ⟨_, hne D₀ hD₀ hy₀⟩
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, ϖ = z' (σ ⟨_, hne D₀ hD₀ hy₀⟩) := ⟨_, rfl⟩
    rw [← hϖ] at hzw
    have : IsDiscreteValuationRing (P.presheaf.stalk w) := by
      have h := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hw)
      change IsDiscreteValuationRing
        (P.presheaf.stalk (AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hw).genericPoint) at h
      rwa [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne] at h
    have hmax : IsLocalRing.maximalIdeal (P.presheaf.stalk w) = Ideal.span {ϖ} := by
      rw [← hz'.1]
      congr 1
      ext a
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        rw [hϖ, Fin.subsingleton_one.elim i (σ ⟨_, hne D₀ hD₀ hy₀⟩)]
      · rintro rfl
        exact ⟨_, hϖ.symm⟩
    have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
    have hne0 : algebraMap _ P.functionField ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    rw [← hzw]
    change P.ord (algebraMap _ P.functionField ϖ) w = 1
    have : Ring.KrullDimLE 1 (P.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
    rw [Scheme.ord_eq_iff hw hne0]
    exact Ring.ordFrac_irreducible hirr

end BaseChange

section PullbackForms

section Field

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}

/-- Along an isomorphism of fields with a pull-back generator, the pull-back of forms is
bijective. -/
private theorem pullbackForms_bijective (hK : Function.Bijective (algebraMap K K'))
    {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Bijective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  have hrepr : ∀ τ : PluriForms k K d m,
      b'.repr (pullbackForms (K' := K') m τ) () = algebraMap K K' (b.repr τ ()) := by
    intro τ
    rw [pullbackForms_eq hω]
    unfold pullbackFormsAlong
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_apply, ite_eq_left rfl, mul_one]
  refine ⟨fun τ₁ τ₂ h => ?_, fun ρ => ?_⟩
  · have h1 := congrArg (fun ρ => b'.repr ρ ()) h
    simp only [hrepr] at h1
    have h2 := hK.1 h1
    exact b.ext_elem fun i => by cases i; exact h2
  · obtain ⟨c, hc⟩ := hK.2 (b'.repr ρ ())
    refine ⟨c • b (), b'.ext_elem fun i => ?_⟩
    cases i
    rw [hrepr, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self,
      Finsupp.single_apply, ite_eq_left rfl, mul_one, hc]

end Field

variable {W : Scheme.{u}} {sW : W ⟶ Spec (.of k)} [IsIntegral W] {V : Scheme.{u}} [IsIntegral V]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The pull-back of rational forms is `k(W)`-semilinear along `g^* : k(W) → k(V)`. -/
private theorem pullbackRationalPluriForms_smul (g : V ⟶ W) [IsDominant g] {d : ℕ} {m : ℤ}
    (a : W.functionField) (τ : RationalPluriForms sW d m) :
    pullbackRationalPluriForms sW g (a • τ) =
      functionFieldMap g a • pullbackRationalPluriForms sW g τ := by
  let := functionFieldAlgebra sW
  let := functionFieldAlgebra (g ≫ sW)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sW g
  exact pullbackForms_smul (K := W.functionField) (K' := V.functionField) (m := m) a τ

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] in
/-- Along a birational morphism over a perfect field the pull-back of rational forms is
bijective. -/
private theorem pullbackRationalPluriForms_bijective [PerfectField k] [LocallyOfFiniteType sW]
    (g : V ⟶ W) [IsDominant g] (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sW; (Algebra.trdeg k W.functionField).toNat = d) (m : ℤ) :
    Function.Bijective (pullbackRationalPluriForms (d := d) (m := m) sW g) := by
  let := functionFieldAlgebra sW
  let := functionFieldAlgebra (g ≫ sW)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sW g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sW g hg hd
  exact pullbackForms_bijective (K := W.functionField) (K' := V.functionField) hg hω m

end PullbackForms

end

/-! ### The strict transform of `S` and pull-back of residues -/

section

/-! ## Adjunction on a log resolution -/

/-- The image under `f` of the strict transform `S' = f⁻¹_* S` lies in `S`. -/
private theorem map_mem_support {X Y : Scheme.{u}} (f : Y ⟶ X) (P : PrimeDivisor X)
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P') :
    ∀ y ∈ (P'.support : Set Y), f y ∈ (P.support : Set X) := by
  intro y ht
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at ht ⊢
  have hg :=
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP').1
  have h2 := image_closure_subset_closure_image f.continuous ⟨_, ht, rfl⟩
  rw [Set.image_singleton, hg] at h2
  exact h2

/-- The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
image. -/
private theorem ker_eq_vanishingIdeal {A B : Scheme.{u}} (g : A ⟶ B) [IsReduced A] :
    g.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range g.base)) := by
  rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
    ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
  simp only [TopologicalSpace.Closeds.coe_top, Set.image_univ]

/-- The restriction `f_S` exists: `ι' ≫ f` factors through the closed immersion `ι`, since `T'`
is reduced and `f` maps `S' = f⁻¹_* S` into `S`. -/
private theorem exists_comp_eq {X Y T T' : Scheme.{u}} (f : Y ⟶ X) (ι : T ⟶ X)
    [IsClosedImmersion ι] (P : PrimeDivisor X) (hP : Set.range ι.base = (P.support : Set X))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsReduced T']
    (hι' : Set.range ι'.base = (P'.support : Set Y)) :
    ∃ fS : T' ⟶ T, fS ≫ ι = ι' ≫ f := by
  have hsub : Set.range (ι' ≫ f).base ⊆ (P.support : Set X) := by
    rintro _ ⟨t, rfl⟩
    exact map_mem_support f P P' hP' _ (hι' ▸ ⟨t, rfl⟩)
  have H : ι.ker ≤ (ι' ≫ f).ker := by
    rw [ker_eq_vanishingIdeal (ι' ≫ f), ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
      TopologicalSpace.Closeds.closure_le]
    refine hsub.trans ?_
    rw [← hP]
    exact Scheme.Hom.range_subset_ker_support _
  exact ⟨IsClosedImmersion.lift ι (ι' ≫ f) H, IsClosedImmersion.lift_fac _ _ _⟩

/-- `S'` is smooth: it is a component of the snc divisor `Ex(f) ∪ f⁻¹ Supp(S + B)`, whose
components are smooth, and `T'` is that component with its reduced structure. -/
private theorem isSmoothScheme_aux
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    {T : Scheme.{u}} (ι : T ⟶ X) (P : PrimeDivisor X) (B : QDivisor X) (hB : B.coeff P = 0)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Mori.IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    {T' : Scheme.{u}} (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsIntegral T']
    (hι' : Set.range ι'.base = (P'.support : Set Y))
    (fS : T' ⟶ T) (hfS : fS ≫ ι = ι' ≫ f) : IsSmoothScheme (fS ≫ ι ≫ sX) := by
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  have hg := (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
    hP').1
  -- the generic point of `S'` lies in `f⁻¹ Supp(S + B)`
  have hmem : (P'.genericPoint : Y) ∈ ((exceptionalSet f ⊔
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)).supp.preimage
        f.continuous : TopologicalSpace.Closeds Y) : Set Y) := by
    refine Or.inr ?_
    show f P'.genericPoint ∈
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single P 1) + B)).supp
    rw [hg, DivisorWithCoeffs.mem_supp_iff]
    refine ⟨P, ?_, ?_⟩
    · simp [DivisorWithCoeffs.coeff_single_self, hB]
    · exact MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P
  rcases hf.isSNCSubset with h0 | ⟨s, hs, hsnc⟩
  · rw [h0] at hmem
    exact hmem.elim
  rw [← hs] at hmem
  obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hmem
  have hEP : E = P' := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E P' hPE
  subst hEP
  have hsupp : E ∈ (∑ E ∈ s, Finsupp.single E (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
      Finset.sum_eq_single_of_mem E hE (fun b _ hb => Finsupp.single_eq_of_ne' hb)]
    simp
  have hsm := hsnc.1 E hsupp
  -- `T'` is the reduced closed subscheme `E`
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  have hker : ι'.ker = E.idealSheaf.subschemeι.ker := by
    rw [ker_eq_vanishingIdeal ι', ker_eq_vanishingIdeal E.idealSheaf.subschemeι, hι',
      Scheme.IdealSheafData.range_subschemeι]
  set g := IsClosedImmersion.lift E.idealSheaf.subschemeι ι' hker.symm.le
  haveI : IsIso g := IsClosedImmersion.isIso_lift E.idealSheaf.subschemeι ι' hker.symm
  have hfac : g ≫ E.idealSheaf.subschemeι = ι' := IsClosedImmersion.lift_fac _ _ _
  have heq : fS ≫ ι ≫ sX = g ≫ E.idealSheaf.subschemeι ≫ f ≫ sX := by
    rw [reassoc_of% hfS, reassoc_of% hfac]
  rw [heq]
  haveI : LocallyOfFiniteType (E.idealSheaf.subschemeι ≫ f ≫ sX) := inferInstance
  haveI : Smooth (E.idealSheaf.subschemeι ≫ f ≫ sX) := (isSmoothScheme_iff _).1 hsm
  haveI : LocallyOfFiniteType (g ≫ E.idealSheaf.subschemeι ≫ f ≫ sX) := inferInstance
  exact (isSmoothScheme_iff _).2 inferInstance

/-- `f_S : S' ⟶ S` is birational: over the biregular locus `W` of `f`, both `S ∩ W` and
`f(S' ∩ f⁻¹ W)` are the reduced closed subscheme of `W` with support the closure of `η_S`. -/
private theorem isBirationalMorphism_aux {X Y T T' : Scheme.{u}} (f : Y ⟶ X) (ι : T ⟶ X)
    [IsClosedImmersion ι] [IsIntegral T] (P : PrimeDivisor X)
    (hP : Set.range ι.base = (P.support : Set X))
    (P' : PrimeDivisor Y) (hP' : inverseTransformPrimeDivisor f P = some P')
    (ι' : T' ⟶ Y) [IsClosedImmersion ι'] [IsIntegral T']
    (hι' : Set.range ι'.base = (P'.support : Set Y))
    (fS : T' ⟶ T) (hfS : fS ≫ ι = ι' ≫ f) : IsBirationalMorphism fS := by
  have hW : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  obtain ⟨hg, hgW⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP'
  have hUV : ι' ⁻¹ᵁ (f ⁻¹ᵁ biregularLocus f) ≤ fS ⁻¹ᵁ (ι ⁻¹ᵁ biregularLocus f) := by
    intro t ht
    have : (fS ≫ ι).base t = (ι' ≫ f).base t := by rw [hfS]
    change (fS ≫ ι).base t ∈ biregularLocus f
    rw [this]
    exact ht
  obtain ⟨t0, ht0⟩ : (P'.genericPoint : Y) ∈ Set.range ι'.base :=
    hι' ▸ MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P'
  obtain ⟨s0, hs0⟩ : (P.genericPoint : X) ∈ Set.range ι.base :=
    hP ▸ MMP.Positivity.PrimeDivisor.genericPoint_mem_support' P
  have ht0U : t0 ∈ ι' ⁻¹ᵁ (f ⁻¹ᵁ biregularLocus f) := by
    change f.base (ι'.base t0) ∈ biregularLocus f
    rw [ht0]; exact hgW
  have hs0V : s0 ∈ ι ⁻¹ᵁ biregularLocus f := by
    change ι.base s0 ∈ biregularLocus f
    rw [hs0, ← hg]; exact hgW
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE fS _ _ ⟨t0, ht0U⟩ ⟨s0, hs0V⟩ hUV ?_
  haveI : IsClosedImmersion (ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hcomp : fS.resLE _ _ hUV ≫ (ι ∣_ biregularLocus f) =
      ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f) := by
    rw [← cancel_mono (biregularLocus f).ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, hfS]
  haveI hci : IsClosedImmersion
      (ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f)) := inferInstance
  refine IsClosedImmersion.isIso_of_ker_eq _ _ _ hcomp ?_
  rw [ker_eq_vanishingIdeal, ker_eq_vanishingIdeal]
  congr 1
  have hfac : ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f) ≫
      (biregularLocus f).ι = (ι' ⁻¹ᵁ (f ⁻¹ᵁ biregularLocus f)).ι ≫ ι' ≫ f := by
    simp only [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
  have hfac' : (ι ∣_ biregularLocus f) ≫ (biregularLocus f).ι =
      (ι ⁻¹ᵁ biregularLocus f).ι ≫ ι := morphismRestrict_ι _ _
  apply le_antisymm
  · rw [TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨t, rfl⟩
    apply subset_closure
    have h1 : ((ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫ (f ∣_ biregularLocus f)).base t).1
        = f.base (ι'.base t.1) := congrArg (fun g => g.base t) hfac
    obtain ⟨a, ha⟩ : ((ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫
        (f ∣_ biregularLocus f)).base t).1 ∈ Set.range ι.base := by
      rw [hP, h1]; exact map_mem_support f P P' hP' _ (hι' ▸ ⟨t.1, rfl⟩)
    have haV : a ∈ ι ⁻¹ᵁ biregularLocus f := by
      change ι.base a ∈ biregularLocus f
      rw [ha]; exact Subtype.property _
    refine ⟨⟨a, haV⟩, Subtype.ext ?_⟩
    exact (congrArg (fun g => g.base ⟨a, haV⟩) hfac').trans ha
  · rw [TopologicalSpace.Closeds.closure_le]
    rintro _ ⟨a, rfl⟩
    have e1 : (biregularLocus f).ι.base ((ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫
        (f ∣_ biregularLocus f)).base ⟨t0, ht0U⟩) = P.genericPoint := by
      refine (congrArg (fun g => g.base ⟨t0, ht0U⟩) hfac).trans ?_
      change f.base (ι'.base t0) = _
      rw [ht0, hg]
    have e2 : (biregularLocus f).ι.base ((ι ∣_ biregularLocus f).base a) = ι.base a.1 :=
      congrArg (fun g => g.base a) hfac'
    have hη : (ι'.resLE (f ⁻¹ᵁ biregularLocus f) _ le_rfl ≫
        (f ∣_ biregularLocus f)).base ⟨t0, ht0U⟩ ⤳ (ι ∣_ biregularLocus f).base a := by
      rw [← (biregularLocus f).ι.isOpenEmbedding.isInducing.specializes_iff, e1, e2,
        specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hP]
      exact ⟨a.1, rfl⟩
    exact hη.mem_closed (TopologicalSpace.Closeds.isClosed _) (subset_closure ⟨_, rfl⟩)

section ResiduePullback

open KaehlerDifferential

/-- `u^*(a ω^{⊗m}) = u(a) (u^*ω)^{⊗m}` for every top form `ω`, once the line of top forms has a
pull-back generator `ω₀`. -/
private theorem pullbackForms_smul_formPow' {k : Type u} [Field k] {K K' : Type u} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    {ω₀ : ⋀[K]^d Ω[K⁄k]} (hω₀ : IsPullbackGenerator K' ω₀) (m : ℕ) (a : K)
    (ω : ⋀[K]^d Ω[K⁄k]) :
    pullbackForms (K' := K') (m : ℤ) (a • MMP.Fourfold.formPow ω m) =
      algebraMap K K' a • MMP.Fourfold.formPow (topFormsMap k K K' d ω) m := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hω₀.1 ▸ Submodule.mem_top (x := ω))
  rw [MMP.Fourfold.formPow_smul, smul_smul, MMP.Fourfold.pullbackForms_smul_formPow hω₀,
    LinearMap.map_smul, ← algebraMap_smul K' c (topFormsMap k K K' d ω₀),
    MMP.Fourfold.formPow_smul, smul_smul, map_mul, map_pow]

/-- The pull-back of a logarithmic form `g (t⁻¹ dt ∧ dx₁ ∧ ⋯ ∧ dxₙ)^{⊗m}` along an extension of
fields `u` is `u(g) (u(t)⁻¹ du(t) ∧ du(x₁) ∧ ⋯ ∧ du(xₙ))^{⊗m}`. -/
private theorem pullbackForms_logForm {k : Type u} [Field k] {K K' : Type u} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {n : ℕ}
    {ω₀ : ⋀[K]^(n + 1) Ω[K⁄k]} (hω₀ : IsPullbackGenerator K' ω₀) (m : ℕ) (g t : K)
    (x : Fin n → K) :
    pullbackForms (K' := K') (m : ℤ) ((g • PiTensorProduct.tprod K (fun _ : Fin m => t⁻¹ •
      exteriorPower.ιMulti K (n + 1) (Fin.cons (D k K t) fun i => D k K (x i))) :
        TensorPower K m (⋀[K]^(n + 1) Ω[K⁄k]))) =
      (algebraMap K K' g • PiTensorProduct.tprod K' (fun _ : Fin m => (algebraMap K K' t)⁻¹ •
        exteriorPower.ιMulti K' (n + 1) (Fin.cons (D k K' (algebraMap K K' t))
          fun i => D k K' (algebraMap K K' (x i)))) :
        TensorPower K' m (⋀[K']^(n + 1) Ω[K'⁄k])) := by
  have hv : (fun i => map k k K K' ((Fin.cons (D k K t) fun i => D k K (x i) :
      Fin (n + 1) → Ω[K⁄k]) i)) =
      (Fin.cons (D k K' (algebraMap K K' t)) fun i => D k K' (algebraMap K K' (x i)) :
        Fin (n + 1) → Ω[K'⁄k]) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [KaehlerDifferential.map_D]
  refine (pullbackForms_smul_formPow' hω₀ m g _).trans ?_
  rw [LinearMap.map_smul, MMP.Mori.topFormsMap_ιMulti, ← algebraMap_smul K' t⁻¹, map_inv₀, hv]
  rfl

/-- The pull-back of a form `g (dx₁ ∧ ⋯ ∧ dxₙ)^{⊗m}` along an extension of fields `u` is
`u(g) (du(x₁) ∧ ⋯ ∧ du(xₙ))^{⊗m}`. -/
private theorem pullbackForms_form {k : Type u} [Field k] {K K' : Type u} [Field K]
    [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {n : ℕ}
    {ω₀ : ⋀[K]^n Ω[K⁄k]} (hω₀ : IsPullbackGenerator K' ω₀) (m : ℕ) (g : K)
    (x : Fin n → K) :
    pullbackForms (K' := K') (m : ℤ) ((g • PiTensorProduct.tprod K (fun _ : Fin m =>
      exteriorPower.ιMulti K n fun i => D k K (x i)) :
        TensorPower K m (⋀[K]^n Ω[K⁄k]))) =
      (algebraMap K K' g • PiTensorProduct.tprod K' (fun _ : Fin m =>
        exteriorPower.ιMulti K' n fun i => D k K' (algebraMap K K' (x i))) :
        TensorPower K' m (⋀[K']^n Ω[K'⁄k])) := by
  refine (pullbackForms_smul_formPow' hω₀ m g _).trans ?_
  rw [MMP.Mori.topFormsMap_ιMulti]
  simp only [KaehlerDifferential.map_D]
  rfl

/-- Transport of a form `c (dv₁ ∧ ⋯ ∧ dvₙ)^{⊗m}` along an equality of structure morphisms. -/
private theorem cast_eq_smul_tprod {k : Type u} [Field k] {T₁ : Scheme.{u}} [IsIntegral T₁]
    {n m : ℕ} {s s' : T₁ ⟶ Spec (.of k)} (e : s = s')
    (H : RationalPluriForms s n m = RationalPluriForms s' n m) (X : RationalPluriForms s n m)
    (c : T₁.functionField) (v : Fin n → T₁.functionField)
    (hX : letI := functionFieldAlgebra s
      X = (c • PiTensorProduct.tprod T₁.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti T₁.functionField n (fun i => D k T₁.functionField (v i))) :
        TensorPower T₁.functionField m (⋀[T₁.functionField]^n Ω[T₁.functionField⁄k]))) :
    letI := functionFieldAlgebra s'
    cast H X = (c • PiTensorProduct.tprod T₁.functionField (fun _ : Fin m =>
        exteriorPower.ιMulti T₁.functionField n (fun i => D k T₁.functionField (v i))) :
        TensorPower T₁.functionField m (⋀[T₁.functionField]^n Ω[T₁.functionField⁄k])) := by
  subst e
  exact hX

variable {Y Y₁ T T₁ : Scheme.{u}} (g : Y₁ ⟶ Y) (j : T ⟶ Y) (j₁ : T₁ ⟶ Y₁) (h : T₁ ⟶ T)
  [IsIntegral T] [IsIntegral T₁] [IsIntegral Y] [IsIntegral Y₁] [IsDominant h] [IsDominant g]

private theorem map_genericPoint_eq_of_comp_eq (hh : h ≫ j = j₁ ≫ g) :
    g (j₁ (genericPoint T₁)) = j (genericPoint T) := by
  have := congrArg (fun f : T₁ ⟶ Y => f (genericPoint T₁)) hh
  simp only [Scheme.Hom.comp_apply] at this
  rw [← this, map_genericPoint_of_isDominant]

/-- The stalk map `𝒪_{Y, j(η_T)} → 𝒪_{Y₁, j₁(η_{T₁})}` of `g`. -/
private noncomputable def stalkMapAt (hh : h ≫ j = j₁ ≫ g) :
    Y.presheaf.stalk (j (genericPoint T)) ⟶ Y₁.presheaf.stalk (j₁ (genericPoint T₁)) :=
  (Y.presheaf.stalkCongr (.of_eq (map_genericPoint_eq_of_comp_eq g j j₁ h hh).symm)).hom ≫
    g.stalkMap (j₁ (genericPoint T₁))

private theorem stalkMapAt_functionField (hh : h ≫ j = j₁ ≫ g)
    (a : Y.presheaf.stalk (j (genericPoint T))) :
    algebraMap (Y₁.presheaf.stalk (j₁ (genericPoint T₁))) Y₁.functionField
        ((stalkMapAt g j j₁ h hh).hom a) =
      functionFieldMap g (algebraMap _ Y.functionField a) := by
  have key : stalkMapAt g j j₁ h hh ≫
        Y₁.presheaf.stalkSpecializes ((genericPoint_spec Y₁).specializes trivial) =
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
        (Y.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant g).symm)).hom ≫
          g.stalkMap (genericPoint Y₁) := by
    simp only [stalkMapAt, TopCat.Presheaf.stalkCongr_hom, Category.assoc]
    rw [← Scheme.Hom.stalkSpecializes_stalkMap, ← Category.assoc, ← Category.assoc]
    congr 1
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes]
  exact congrArg (fun f => f.hom a) key

private theorem stalkMapAt_stalkMap (hh : h ≫ j = j₁ ≫ g)
    (a : Y.presheaf.stalk (j (genericPoint T))) :
    (j₁.stalkMap (genericPoint T₁)).hom ((stalkMapAt g j j₁ h hh).hom a) =
      functionFieldMap h ((j.stalkMap (genericPoint T)).hom a) := by
  have key : stalkMapAt g j j₁ h hh ≫ j₁.stalkMap (genericPoint T₁) =
      j.stalkMap (genericPoint T) ≫
        (T.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant h).symm)).hom ≫
          h.stalkMap (genericPoint T₁) := by
    simp only [stalkMapAt, Category.assoc, ← Scheme.Hom.stalkMap_comp]
    rw [Scheme.Hom.stalkMap_congr_point_assoc j _ _ (map_genericPoint_of_isDominant h).symm,
      ← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom (h ≫ j) (j₁ ≫ g) hh]
    simp only [TopCat.Presheaf.stalkCongr_hom]
    apply TopCat.Presheaf.stalk_hom_ext
    intro V hV
    erw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc]
    rfl
  exact congrArg (fun f => f.hom a) key

/-- **Residues of `m`-fold forms commute with pull-back to the strict transform.** Let
`g : Y₁ ⟶ Y` be a birational morphism of normal varieties over a perfect field, `j : T ⟶ Y` an
integral closed subscheme onto the prime divisor `P`, `j₁ : T₁ ⟶ Y₁` one onto `P₁` with
`g(η_{P₁}) = η_P`, `g` an isomorphism of local rings at `η_{P₁}`, and `h : T₁ ⟶ T` birational with
`h ≫ j = j₁ ≫ g`. If `ρ = Res_T τ`, then `h^*ρ = Res_{T₁}(g^*τ)`. -/
public theorem isPoincareResidue_pullback {k : Type u} [Field k] [PerfectField k]
    (sY : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsNormal Y] [LocallyOfFiniteType sY]
    [IsLocallyNoetherian Y₁] [IsNormal Y₁] [LocallyOfFiniteType (j ≫ sY)]
    (hgb : Function.Bijective (functionFieldMap g)) (hhb : Function.Bijective (functionFieldMap h))
    (hh : h ≫ j = j₁ ≫ g) (P : PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    (P₁ : PrimeDivisor Y₁) (hP₁ : j₁ (genericPoint T₁) = P₁.genericPoint)
    [IsIso (g.stalkMap P₁.genericPoint)] {n m : ℕ}
    (hdY : letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat = n + 1)
    (hdT : letI := functionFieldAlgebra (j ≫ sY); (Algebra.trdeg k T.functionField).toNat = n)
    {τ : RationalPluriForms sY (n + 1) m} {ρ : RationalPluriForms (j ≫ sY) n m}
    (hρ : MMP.Fourfold.IsPoincareResidue sY j n m τ ρ) :
    MMP.Fourfold.IsPoincareResidue (g ≫ sY) j₁ n m (pullbackRationalPluriForms sY g τ)
      (cast (by rw [← Category.assoc, hh, Category.assoc])
        (pullbackRationalPluriForms (j ≫ sY) h ρ)) := by
  classical
  obtain ⟨t, a0, x0, ht, hτE, hρE⟩ := hρ
  set ψ := stalkMapAt g j j₁ h hh with hψdef
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (g ≫ sY)
  refine ⟨ψ.hom t, ψ.hom a0, fun i => ψ.hom (x0 i), ?_, ?_, ?_⟩
  · rw [hψdef, stalkMapAt_functionField g j j₁ h hh, hP₁,
      MMP.Positivity.ord_functionFieldMap_of_isIso g P₁ P (by
        rw [← hP₁, map_genericPoint_eq_of_comp_eq g j j₁ h hh, hP])]
    rw [← hP]
    exact ht
  · let := functionFieldMapAlgebra g
    have := isScalarTower_functionFieldMap sY g
    have hΦ : ∀ a, algebraMap Y.functionField Y₁.functionField (algebraMap _ Y.functionField a) =
        algebraMap _ Y₁.functionField (ψ.hom a) :=
      fun a => (stalkMapAt_functionField g j j₁ h hh a).symm
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sY g hgb hdY
    change pullbackForms (K' := Y₁.functionField) (m : ℤ) τ = _
    rw [hτE, pullbackForms_logForm hω]
    simp only [hΦ]
    rfl
  · let := functionFieldAlgebra (j ≫ sY)
    let := functionFieldAlgebra (h ≫ j ≫ sY)
    let := functionFieldMapAlgebra h
    have := isScalarTower_functionFieldMap (j ≫ sY) h
    have hΦ : ∀ a, algebraMap T.functionField T₁.functionField ((j.stalkMap
        (genericPoint T)).hom a) =
        (j₁.stalkMap (genericPoint T₁)).hom (ψ.hom a) :=
      fun a => (stalkMapAt_stalkMap g j j₁ h hh a).symm
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective (j ≫ sY) h hhb hdT
    refine cast_eq_smul_tprod (k := k) (by rw [← Category.assoc, hh, Category.assoc]) _ _ _ _ ?_
    change pullbackForms (K' := T₁.functionField) (m : ℤ) ρ = _
    rw [hρE, pullbackForms_form hω]
    simp only [hΦ]
    rfl

end ResiduePullback

end

/-! ### The forward adjunction -/

section Main

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Any local generator computes the discrepancy.** If `a = a(E, X, Δ)` and `τ'` generates
`𝒪_X(m'(K + Δ))` on an open set containing `f(η_E)`, then `m' · a = ord_E(f^*τ')`. -/
private theorem mul_eq_ordPullback_of_isDiscrepancy {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) {m' : ℕ}
    {U' : X.Opens} (hU' : D.f D.E.genericPoint ∈ U') {τ' : RationalPluriForms sX n m'}
    (hτ' : GeneratesOn Δ m' U' τ') : (m' : ℚ) * a = D.ordPullback τ' := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set g : X.functionField := c ^ (m' : ℤ) * c' ^ (-(m : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      X.ord g Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hτ.2 Γ ⟨_, hΓ, hU⟩
    have e2 := hτ'.2 Γ ⟨_, hΓ, hU'⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'.1
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have : ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) = 0 := by
      linear_combination (m' : ℚ) * e1 - (m : ℚ) * e2 - (m' : ℚ) * f1 + (m : ℚ) * f2
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg hord
  have hY0 : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact D.E.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) = 0 := by
    exact_mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'.1
  have key : (m : ℚ) * ((m' : ℚ) * a - D.ordPullback τ') = 0 := by
    linear_combination (m' : ℚ) * hτa + (m' : ℚ) * h1 - (m : ℚ) * h2 + hY0'
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hm0)

/-- The order of a form along a prime divisor does not change under transport along an equality
of structure morphisms. -/
private theorem ordForm_cast' {k : Type u} [Field k] {W : Scheme.{u}} [IsIntegral W]
    [IsLocallyNoetherian W] {s₁ s₂ : W ⟶ Spec (.of k)} (h : s₁ = s₂) {d : ℕ} {m : ℤ}
    (H : RationalPluriForms s₁ d m = RationalPluriForms s₂ d m) (ρ : RationalPluriForms s₁ d m)
    (G : MMP.Mori.PrimeDivisor W) : G.ordForm (cast H ρ) = G.ordForm ρ := by
  subst h
  rfl

open Classical in
/-- **The residue along `S'` at a point of codimension two.** Let `f : Y ⟶ X` be a log
resolution of `(X, S + B)` whose strict transform `S'` of `S` meets no prime divisor lying over a
point of `Supp B ∖ S`, let `τ` generate `𝒪_X(m(K_X + S + B))` near the image of a point `y` of
codimension two of `S'`, and let `ρ` be the residue of `f^*τ` along `S'`. Then the order of `ρ`
along the prime divisor of `S'` with generic point `y` is `m · ∑ a(E, X, S + B)`, the sum over
the `f`-exceptional prime divisors `E` through `y`. -/
private theorem ordForm_eq_mul_sum_of_isPoincareResidue {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX (n + 1))
    (S : MMP.Mori.PrimeDivisor X) {B : QDivisor X} (hB : B.coeff S = 0)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Mori.IsLogResolution sX
      (QDivisor.toRDivisor (Divisor.toQDivisor (Finsupp.single S 1) + B)) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (S' : MMP.Mori.PrimeDivisor Y) (hS' : inverseTransformPrimeDivisor f S = some S')
    (hdisj : ∀ Γ : MMP.Mori.PrimeDivisor Y, f Γ.genericPoint ∈ B.supp →
      f Γ.genericPoint ∉ S.support → Disjoint (S'.support : Set Y) Γ.support)
    (Ex : Finset (MMP.Mori.PrimeDivisor Y))
    (hEx : ∀ E, E ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap E)
    (e : MMP.Mori.PrimeDivisor Y → ℚ)
    (he : ∀ E ∈ Ex, IsDiscrepancy sX (n + 1) K
      (Divisor.toQDivisor (Finsupp.single S 1) + B)
      ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ (e E))
    {m : ℕ} {U : X.Opens} {τ : RationalPluriForms sX (n + 1) m}
    (hτ : GeneratesOn (Divisor.toQDivisor (Finsupp.single S 1) + B) m U τ)
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsDominant f] [IsIntegral S'.idealSheaf.subscheme]
    [IsLocallyNoetherian S'.idealSheaf.subscheme] [IsNormal S'.idealSheaf.subscheme]
    (F' : MMP.Mori.PrimeDivisor S'.idealSheaf.subscheme)
    (hFU : f (S'.idealSheaf.subschemeι F'.genericPoint) ∈ U)
    (ρ : RationalPluriForms (S'.idealSheaf.subschemeι ≫ f ≫ sX) n m)
    (hρ : MMP.Fourfold.IsPoincareResidue (f ≫ sX) S'.idealSheaf.subschemeι n m
      (pullbackRationalPluriForms sX f τ) ρ) :
    (F'.ordForm ρ : ℚ) = m * ∑ E ∈ Ex,
      if S'.idealSheaf.subschemeι F'.genericPoint ∈ E.support then e E else 0 := by
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hfb : IsBirationalMorphism f := hf.isBirationalMorphism
  have hsmY : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  set y := S'.idealSheaf.subschemeι F'.genericPoint with hy
  set w := F'.genericPoint with hw
  have hw1 : Order.coheight w = 1 := F'.coheight_genericPoint
  have hrange' : Set.range S'.idealSheaf.subschemeι.base = (S'.support : Set Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  have hyS : y ∈ (S'.support : Set Y) := hrange' ▸ ⟨_, rfl⟩
  have hΓ : S'.idealSheaf.subschemeι (genericPoint S'.idealSheaf.subscheme) = S'.genericPoint :=
    map_genericPoint_eq S'.idealSheaf.subschemeι S' hrange'
  -- dimensions
  have hdimY : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    haveI := hX.1
    haveI := hY.1
    rw [← hK.topologicalKrullDim_eq]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb).symm
  have he' : (letI := functionFieldAlgebra (f ≫ sX); (Algebra.trdeg k Y.functionField).toNat) =
      n + 1 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := f ≫ sX) hdimY
  have hdX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  -- the strict transform `S'`
  have hS1 : Divisor.toQDivisor (Finsupp.single S (1 : ℤ)) = Finsupp.single S (1 : ℚ) := by
    rw [MMP.Threefold.Resolution.toQDivisor_single]; simp
  have hfS := MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hS'
  have hS'nex : ¬ RationalMap.IsExceptional f.toRationalMap S' := by
    intro hE
    have h2 := (isExceptional_iff_two_le_coheight hX
      (⟨Y, f, hY, hfb, S'⟩ : DivisorOver k sX)).mp hE
    change 2 ≤ Order.coheight (f S'.genericPoint) at h2
    rw [hfS.1, S.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)
  have hS'Ex : S' ∉ Ex := fun h => hS'nex ((hEx S').1 h)
  set Δ : QDivisor X := Divisor.toQDivisor (Finsupp.single S 1) + B with hΔ
  have hΔS : Δ.coeff S = 1 := by
    rw [hΔ, hS1, DivisorWithCoeffs.coeff_add, hB, add_zero, DivisorWithCoeffs.coeff_single_self]
  -- the snc divisor
  obtain ⟨t, ht, htsnc⟩ := exists_finset_isSNC_of_isLogResolution hf
  rw [QDivisor.supp_toRDivisor] at ht
  have hmemt : ∀ Γ ∈ t, Γ ∈ (∑ P ∈ t, Finsupp.single P (1 : ℤ)).support := fun Γ hΓ => by
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply,
      Finset.sum_eq_single_of_mem Γ hΓ fun Q _ hQΓ => Finsupp.single_eq_of_ne hQΓ.symm,
      Finsupp.single_eq_same]
    exact one_ne_zero
  have hS't : S' ∈ t := by
    refine (ht S').1 (Or.inr ?_)
    rw [hfS.1, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨S, by rw [hΔS]; norm_num, MMP.Flips.primeDivisor_genericPoint_mem_support S⟩
  have hExt : ∀ E ∈ Ex, E ∈ t := fun E hE => (ht E).1 (Or.inl
    (MMP.Positivity.support_subset_exceptionalSet E ((hEx E).1 hE)
      (MMP.Flips.primeDivisor_genericPoint_mem_support E)))
  have hker : RingHom.ker (S'.idealSheaf.subschemeι.stalkMap w).hom =
      IdealSheafData.stalk S'.idealSheaf (S'.idealSheaf.subschemeι w) :=
    IdealSheafData.ker_stalkMap_subschemeι _ _
  obtain ⟨hcnt1, hcnt2⟩ := snc_at_codim_one htsnc (B := Ex)
    (fun D hD => hmemt D (hExt D hD)) (hmemt S' hS't) hS'Ex w hw1 hyS hker
  -- a local equation `h` of `S'` at `y`
  obtain ⟨N, z, jj, hz, -, hI⟩ := htsnc.2 y
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hz
  set h := z (jj ⟨S', hmemt S' hS't, hyS⟩) with hhdef
  have hIh : IdealSheafData.stalk S'.idealSheaf y = Ideal.span {h} := hI ⟨S', hmemt S' hS't, hyS⟩
  have hkerh : RingHom.ker (S'.idealSheaf.subschemeι.stalkMap w).hom = Ideal.span {h} :=
    hker.trans hIh
  have hh2 : h ∉ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ 2 :=
    notMem_maximalIdeal_sq hz _
  have hordh := ord_algebraMap_of_stalk_idealSheaf_eq_span hsmY hyS hIh
  have hhΓ : Y.ord (algebraMap _ Y.functionField h) S'.genericPoint = 1 := by
    have := hordh.1 S' hyS
    rwa [if_pos rfl] at this
  -- the form `θ = f^*τ`
  set θ := pullbackRationalPluriForms sX f τ with hθdef
  have hpb0 : pullbackRationalPluriForms sX f (0 : RationalPluriForms sX (n + 1) m) = 0 := by
    have := pullbackRationalPluriForms_smul (sW := sX) f (0 : X.functionField)
      (0 : RationalPluriForms sX (n + 1) m)
    rwa [zero_smul, map_zero, zero_smul] at this
  have hpbinj := (pullbackRationalPluriForms_bijective (sW := sX) f
    hfb.functionFieldMap_bijective hdX (m : ℤ)).1
  have hθ0 : θ ≠ 0 := fun h0 => hτ.1 (hpbinj (h0.trans hpb0.symm))
  -- the orders of `θ` along the prime divisors through `y`
  have hθord : ∀ D : MMP.Mori.PrimeDivisor Y, y ∈ D.support →
      (D.ordForm θ : ℚ) = if D = S' then -(m : ℚ) else if D ∈ Ex then m * e D else 0 := by
    intro D hyD
    have hDU : f D.genericPoint ∈ U :=
      ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD).map
        f.continuous).mem_open U.isOpen hFU
    by_cases hDEx : D ∈ Ex
    · have hDS : D ≠ S' := fun h => hS'Ex (h ▸ hDEx)
      rw [if_neg hDS, if_pos hDEx]
      exact (mul_eq_ordPullback_of_isDiscrepancy (he D hDEx) hDU hτ).symm
    · have hDex : ¬ RationalMap.IsExceptional f.toRationalMap D := fun h => hDEx ((hEx D).2 h)
      obtain ⟨PX, hPX, hord, -⟩ := exists_primeDivisor_of_not_isExceptional (Δ := Δ) hX hf hY
        hDex
      have hc := hτ.2 PX
        ⟨PX.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' PX, hPX ▸ hDU⟩
      have hθD : D.ordForm θ = PX.ordForm τ := hord τ
      rw [if_neg hDEx, hθD]
      by_cases hPS : PX = S
      · subst hPS
        have hDS : D = S' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
          (eq_of_map_eq_of_mem_biregularLocus (hPX.trans hfS.1.symm) (hPX ▸ hfS.1 ▸ hfS.2))
        rw [if_pos hDS]
        rw [hΔS] at hc
        linarith
      · have hDS : D ≠ S' := by
          rintro rfl
          exact hPS (AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hPX.symm.trans hfS.1))
        rw [if_neg hDS]
        have hB0 : Δ.coeff PX = 0 := by
          rw [hΔ, hS1, DivisorWithCoeffs.coeff_add,
            DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hPS), zero_add]
          by_contra hBP
          refine Set.disjoint_left.1 (hdisj D ?_ ?_) hyS hyD
          · rw [hPX, DivisorWithCoeffs.mem_supp_iff]
            exact ⟨PX, hBP, MMP.Flips.primeDivisor_genericPoint_mem_support PX⟩
          · rw [hPX]
            intro hm
            exact hPS (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hm).symm
        rw [hB0, mul_zero, add_zero] at hc
        exact hc
  -- the residue, computed with a local equation of the other boundary component through `y`
  by_cases hE0 : ∃ E₀ ∈ Ex, y ∈ E₀.support
  · obtain ⟨E₀, hE₀, hyE₀⟩ := hE0
    have hE₀S : E₀ ≠ S' := fun h => hS'Ex (h ▸ hE₀)
    obtain ⟨π, hπI, hπord⟩ := hcnt2 E₀ hE₀ hyE₀
    have ordπ := ord_algebraMap_of_stalk_idealSheaf_eq_span hsmY hyE₀ hπI
    have hθE₀ := hθord E₀ hyE₀
    rw [if_neg hE₀S, if_pos hE₀] at hθE₀
    obtain ⟨ρ', hρ'res, -, hρ'ord⟩ := exists_isPoincareResidue_ordForm (sY := f ≫ sX)
      (j := S'.idealSheaf.subschemeι) hsmY hΓ he' θ hθ0 w (E₀.ordForm θ) hkerh hh2 hhΓ
      (fun hζ => ordπ.2 _ hζ (by
        rw [hΓ]
        intro hmem
        exact hE₀S (MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hmem)))
      (fun D hyD => by
        have h1 := hθord D hyD
        rw [ordπ.1 D hyD, hordh.1 D hyD]
        by_cases hDS : D = S'
        · subst hDS
          rw [if_pos rfl] at h1
          rw [if_neg (Ne.symm hE₀S), if_pos rfl]
          push_cast
          have : (D.ordForm θ : ℚ) = -(m : ℚ) := h1
          have h2 : D.ordForm θ = -(m : ℤ) := by exact_mod_cast this
          rw [h2]; ring
        · rw [if_neg hDS]
          by_cases hDE : D = E₀
          · subst hDE; simp
          · rw [if_neg hDE, if_neg hDS] at *
            have hDEx : D ∉ Ex := fun hD => hDE (hcnt1 D hD E₀ hE₀ hyD hyE₀)
            rw [if_neg hDEx] at h1
            have h2 : D.ordForm θ = 0 := by exact_mod_cast h1
            rw [h2]; ring)
    have hρeq :=
      isPoincareResidue_unique (sY := f ≫ sX) (j := S'.idealSheaf.subschemeι) hΓ hρ hρ'res
    rw [hρeq, hρ'ord F' rfl, hπord, mul_one, hθE₀]
    congr 1
    rw [Finset.sum_eq_single E₀]
    · rw [if_pos hyE₀]
    · intro E hE hEE₀
      rw [if_neg]
      intro hyE
      exact hEE₀ (hcnt1 E hE E₀ hE₀ hyE hyE₀)
    · intro h; exact absurd hE₀ h
  · push Not at hE0
    obtain ⟨ρ', hρ'res, -, hρ'ord⟩ := exists_isPoincareResidue_ordForm (sY := f ≫ sX)
      (j := S'.idealSheaf.subschemeι) hsmY hΓ he' θ hθ0 w (π := 1) 0 hkerh hh2 hhΓ
      (fun hζ => by rw [map_one]; exact isUnit_one)
      (fun D hyD => by
        have h1 := hθord D hyD
        rw [hordh.1 D hyD, zero_mul, zero_sub]
        by_cases hDS : D = S'
        · rw [if_pos hDS] at h1
          rw [if_pos hDS]
          have h2 : D.ordForm θ = -(m : ℤ) := by exact_mod_cast h1
          rw [h2]; ring
        · rw [if_neg hDS, if_neg (fun hD => hE0 D hD hyD)] at h1
          rw [if_neg hDS]
          have h2 : D.ordForm θ = 0 := by exact_mod_cast h1
          rw [h2]; ring)
    have hρeq :=
      isPoincareResidue_unique (sY := f ≫ sX) (j := S'.idealSheaf.subschemeι) hΓ hρ hρ'res
    rw [hρeq, hρ'ord F' rfl, zero_mul, Finset.sum_eq_zero]
    · simp
    · intro E hE
      rw [if_neg (hE0 E hE)]

/-- **Forward discrepancy adjunction on a normal prime divisor.** Let `X` be a normal variety of
dimension `n + 1` with canonical divisor `K`, `ι : S ⟶ X` a closed immersion onto a prime
divisor `P` with `S` a normal variety with canonical divisor `K_S`, and `B ≥ 0` a `ℚ`-divisor with
`coeff_P B = 0` and `K + P + B` `ℚ`-Cartier. Let `B_S` be the adjunction boundary on `S`: for some
`m > 0`, each point of `S` has a neighbourhood `U` in `X` and a form `τ` generating
`𝒪_X(m(K_X + P + B))` on `U` whose Poincaré residue `ρ` along `S` generates `𝒪_S(m(K_S + B_S))`
on `ι⁻¹ U`. Then every divisor `F` over `S` has a divisor `E` over `X`, exceptional over `X`, with
`ι(c_S(F)) = c_X(E)` (as generic points) and `a(F, S, B_S) = a(E, X, P + B)`. -/
@[mmp "lem_fourfold_normal_prime_forward_adjunction"]
public theorem exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (n : ℕ) (K : Divisor X) (hK : K.IsCanonicalDivisor sX (n + 1))
    (P : Mori.PrimeDivisor X) {S : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (hS : IsNormalVariety k (ι ≫ sX)) (hι : Set.range ι.base = (P.support : Set X))
    (KS : Divisor S) (hKS : KS.IsCanonicalDivisor (ι ≫ sX) n)
    (B : QDivisor X) (hB : 0 ≤ B) (hBP : B.coeff P = 0)
    (hD : ∃ m : ℕ, 0 < m ∧
      ((m : ℤ) • (Divisor.toQDivisor K + (Finsupp.single P 1 + B))).IsCartierDivisor)
    (BS : QDivisor S)
    (hBS : ∃ m : ℕ, 0 < m ∧ ∀ x : S, ∃ U : X.Opens, ι.base x ∈ U ∧
      ∃ τ : RationalPluriForms sX (n + 1) m, GeneratesOn (Finsupp.single P 1 + B) m U τ ∧
        ∃ ρ : RationalPluriForms (ι ≫ sX) n m,
          IsPoincareResidue sX ι n m τ ρ ∧ GeneratesOn BS m (ι ⁻¹ᵁ U) ρ)
    (F : DivisorOver k (ι ≫ sX)) :
    ∃ E : DivisorOver k sX, E.IsExceptional ∧
      ι.base (F.f.base F.E.genericPoint) = E.f.base E.E.genericPoint ∧
      ∀ a : ℚ, IsDiscrepancy (ι ≫ sX) n KS BS F a ↔
        IsDiscrepancy sX (n + 1) K (Finsupp.single P 1 + B) E a := by
  classical
  obtain ⟨m, hm, hloc⟩ := hBS
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType (ι ≫ sX) := hS.1.toLocallyOfFiniteType
  have hS1 : Divisor.toQDivisor (Finsupp.single P (1 : ℤ)) = Finsupp.single P (1 : ℚ) := by
    rw [MMP.Threefold.Resolution.toQDivisor_single]; simp
  -- the adjunction pair `(S, B_S)`
  have hCartS : ((m : ℤ) • (Divisor.toQDivisor KS + BS)).IsCartierDivisor :=
    isCartierDivisor_of_forall_generatesOn hS hKS fun x => by
      obtain ⟨U, hxU, τ, -, ρ, -, hρ⟩ := hloc x
      exact ⟨ι ⁻¹ᵁ U, hxU, ρ, hρ⟩
  have hPWS : IsPairWith (ι ≫ sX) n KS BS := ⟨hS, hKS, m, by exact_mod_cast hm.ne', hCartS⟩
  -- the pair `(X, S + B)`
  have hKSB : (Divisor.toQDivisor K + Finsupp.single P 1 + B).IsQCartier := by
    obtain ⟨m₀, hm₀, hC⟩ := hD
    exact ⟨m₀, by exact_mod_cast hm₀.ne', by rwa [add_assoc]⟩
  have hPX : Mori.IsPair sX (Divisor.toQDivisor (Finsupp.single P 1) + B) :=
    ⟨hX, n + 1, K, hK, by rw [hS1, ← add_assoc]; exact hKSB⟩
  -- the center of `F` is not the generic point of `S`
  have hFη : F.f F.E.genericPoint ≠ genericPoint S := by
    intro h
    by_cases hex : F.IsExceptional
    · have h2 := (isExceptional_iff_two_le_coheight hS F).mp hex
      rw [h, coheight_genericPoint] at h2
      exact absurd h2 (by norm_num)
    · obtain ⟨Q, hv⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hS F hex
      have hx := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hS.1 hv
      have h0 : Order.coheight (genericPoint S) = 0 := coheight_genericPoint S
      rw [← h, hx] at h0
      change Order.coheight Q.genericPoint = 0 at h0
      rw [Q.coheight_genericPoint] at h0
      exact one_ne_zero h0
  -- a local generator `τ` near the center, with residue `ρ`
  obtain ⟨U, hxU, τ, hτ, ρ, hres, hρ⟩ := hloc (F.f F.E.genericPoint)
  have hτ' : GeneratesOn (Divisor.toQDivisor (Finsupp.single P 1) + B) m U τ := by rwa [hS1]
  -- a log resolution on which `F` is a prime divisor of the strict transform of `S`
  obtain ⟨J, hJ, hreal⟩ := exists_idealSheaf_realising ι hS P hι hKS F hFη
  obtain ⟨Y, f, hf, hY, S', hS', hdisjP, hJY⟩ :=
    exists_isLogResolution_disjoint_isEffectiveCartierDivisor hX P hBP J hJ
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI := hf.isProper
  have hfb : IsBirationalMorphism f := hf.isBirationalMorphism
  haveI : IsDominant f := hfb.isDominant
  haveI : IsIntegral S'.idealSheaf.subscheme := S'.integral
  have hrange' : Set.range S'.idealSheaf.subschemeι.base = (S'.support : Set Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  -- the restriction `f_S : S' ⟶ S`
  obtain ⟨fS, hfS⟩ := exists_comp_eq f ι P hι S' hS' S'.idealSheaf.subschemeι hrange'
  have hsm := isSmoothScheme_aux sX ι P B hBP f hf hY S' hS' S'.idealSheaf.subschemeι hrange'
    fS hfS
  have hT' : IsNormalVariety k (fS ≫ ι ≫ sX) := by
    refine ⟨?_, isNormal_of_isRegular _
      (MMP.Threefold.Resolution.isRegular_of_isSmoothScheme hsm)⟩
    haveI := hY.1
    have heq : fS ≫ ι ≫ sX = S'.idealSheaf.subschemeι ≫ f ≫ sX := by rw [reassoc_of% hfS]
    rw [heq]
    exact AlgebraicGeometry.IsVariety.mk
  have hbir := isBirationalMorphism_aux f ι P hι S' hS' S'.idealSheaf.subschemeι hrange' fS hfS
  haveI : IsProper (fS ≫ ι) := hfS ▸ inferInstance
  have hprop : IsProper fS := IsProper.of_comp fS ι
  haveI : IsNormal S'.idealSheaf.subscheme := hT'.2
  haveI : LocallyOfFiniteType (fS ≫ ι ≫ sX) := hT'.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian S'.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (fS ≫ ι ≫ sX)
  haveI : IsDominant fS := hbir.isDominant
  have hJT' : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap (fS ≫ ι)) := by
    rw [hfS, Scheme.IdealSheafData.comap_comp]
    refine isEffectiveCartierDivisor_comap_of_genericPoint_notMem _ hJY _ ?_
    intro hmem
    have hmem' : S'.genericPoint ∈ ((J.comap f).support : Set Y) := hmem
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hS').1] at hmem'
    have := hJ _ hmem'
    rw [P.coheight_genericPoint] at this
    exact absurd this (by norm_num)
  obtain ⟨F', hF'⟩ := hreal _ fS hT' hbir hprop hJT'
  have hx0 := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hS.1 hF'
  change fS F'.genericPoint = F.f F.E.genericPoint at hx0
  have hfy : f (S'.idealSheaf.subschemeι F'.genericPoint) = ι (F.f F.E.genericPoint) := by
    rw [← hx0, ← Scheme.Hom.comp_apply, ← hfS, Scheme.Hom.comp_apply]
  -- the exceptional divisor `G` over `X`
  obtain ⟨Ex, hEx⟩ := exists_finset_isExceptional hf hY
  choose e he using fun E : MMP.Mori.PrimeDivisor Y =>
    MMP.Positivity.IsPair.exists_isDiscrepancy hPX hK ⟨Y, f, hY, hf.isBirationalMorphism, E⟩
  have hdim : topologicalKrullDim X = (n : WithBot ℕ∞) + 1 := by
    rw [hK.topologicalKrullDim_eq]; rfl
  have hdimY : topologicalKrullDim Y = (n : WithBot ℕ∞) + 1 := by
    haveI := hX.1
    haveI := hY.1
    rw [← hdim]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX)
      hf.isBirationalMorphism).symm
  have hyS : S'.idealSheaf.subschemeι F'.genericPoint ∈ (S'.support : Set Y) :=
    hrange' ▸ ⟨_, rfl⟩
  have hy2 : Order.coheight (S'.idealSheaf.subschemeι F'.genericPoint) = 2 :=
    coheight_subschemeι_genericPoint (f ≫ sX) hdimY S' F'
  obtain ⟨G, hGex, hGpt, hGd⟩ := exists_divisorOver_isDiscrepancy hX hK P hBP hKSB f hf hY S'
    hS' hdisjP Ex hEx e (fun E _ => he E) _ hyS hy2
  -- the residue of `f^*τ` along `S'` is `f_S^*ρ`
  have hdX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  have hdS := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι ≫ sX)
    hKS.topologicalKrullDim_eq
  obtain ⟨-, hgW⟩ :=
    MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hS'
  haveI : IsIso (f.stalkMap S'.genericPoint) :=
    MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hgW
  have hR := isPoincareResidue_pullback f ι S'.idealSheaf.subschemeι fS sX
    hfb.functionFieldMap_bijective hbir.functionFieldMap_bijective hfS P
    (map_genericPoint_eq ι P hι) S' (map_genericPoint_eq _ S' hrange') hdX hdS hres
  have hFU : f (S'.idealSheaf.subschemeι F'.genericPoint) ∈ U := by rwa [hfy]
  have hord := ordForm_eq_mul_sum_of_isPoincareResidue hX hK P hBP f hf hY S' hS' hdisjP Ex hEx e
    (fun E _ => he E) hτ' F' hFU _ hR
  rw [ordForm_cast' (by rw [← Category.assoc, hfS, Category.assoc])] at hord
  -- the discrepancy of `F` over `(S, B_S)`
  set aval : ℚ := ∑ E ∈ Ex,
    if S'.idealSheaf.subschemeι F'.genericPoint ∈ E.support then e E else 0 with haval
  have hd'' : IsDiscrepancy (ι ≫ sX) n KS BS
      ⟨S'.idealSheaf.subscheme, fS, hT', hbir, F'⟩ aval := by
    refine ⟨hS, hKS, m, hm, hCartS, ι ⁻¹ᵁ U, ?_, ρ, hρ, ?_⟩
    · change ι (fS F'.genericPoint) ∈ U
      rwa [hx0]
    · change (m : ℚ) * aval = (F'.ordForm (pullbackRationalPluriForms (ι ≫ sX) fS ρ) : ℚ)
      rw [hord]
  have hFa : ∀ a : ℚ, IsDiscrepancy (ι ≫ sX) n KS BS F a ↔ a = aval := by
    refine fun a =>
      ⟨fun ha => (MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPWS hF' hd'' ha).symm, ?_⟩
    rintro rfl
    obtain ⟨a1, ha1⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPWS.isPair hKS F
    have := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPWS hF' hd'' ha1
    rwa [← this] at ha1
  refine ⟨G, hGex, ?_, fun a => ?_⟩
  · change ι (F.f F.E.genericPoint) = G.f G.E.genericPoint
    rw [hGpt, hfy]
  · rw [hFa]
    exact ⟨fun ha => ha ▸ hGd, fun ha => (hGd.eq ha).symm⟩

end Main

end MMP.Fourfold
