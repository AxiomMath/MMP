module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.Flip.FlipPreservesCanonical
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence

/-!
# Szabó's sets of small log discrepancy shrink under flips

Let `X` be a normal threefold with canonical divisor `K`, `D` a `ℚ`-divisor with `K_X + D`
`ℚ`-Cartier, `φ : X ⟶ Z` a small contraction with `-(K_X + D)` `φ`-ample, and `φ⁺ : X⁺ ⟶ Z` with
`g : X ⤏ X⁺` a flip of `φ` with respect to `K_X + D`. Let `B ⊆ X` be the union of finitely many
prime divisors `P`, and `B⁺ ⊆ X⁺` the union of their transforms `g_*P`. If no flipping curve of `φ`
lies in `B`, then `𝒮_t(X⁺, g_*D; B⁺) ⊆ 𝒮_t(X, D; B)` for every `t ∈ ℚ`, where the function fields
`k(X)` and `k(X⁺)` are identified over `k(Z)`.

A valuation `ν` of `𝒮_t(X⁺, g_*D; B⁺)` lies in `𝒮_t(X, D)` since sets of small log discrepancy
shrink under flips. Suppose its center `W` on `X` is a curve contained in `B`. Then `W` is not
contained in `Ex(φ)`, for it would be a flipping curve; so its generic point `ξ` lies off `Ex(φ)`
and `φ(ξ)` lies off the closed set `φ(Ex φ)` (otherwise `φ(ξ)` is a closed point and `ξ`,
isolated in its fibre, is closed on the Jacobson scheme `X`). Over `U = Z ∖ φ(Ex φ)` the flip
`φ⁺` is an isomorphism. The centers of `ν` on `X` and on `X⁺` lie over the same point of the
separated scheme `Z`, so the generic point `ξ⁺` of the center on `X⁺` lies over `U`: it has the
same codimension as `ξ`, and it is a specialization of the generic point of `g_*P` for the
component `P ∋ ξ` of `B`. Hence the center on `X⁺` is a curve in `B⁺`, a contradiction.

## Main results

* `MMP.Flips.smallLogDiscrepancySetOff_subset_of_isFlip`

## Implementation notes

The valuations in the two sets live on the different fields `k(X⁺)` and `k(X)`. A valuation `ν⁺`
of `k(X⁺)` is identified with the valuation `ν` of `k(X)` satisfying `ν ∘ φ^* = ν⁺ ∘ φ⁺^*` on
`k(Z)`; such a `ν` exists, and the inclusion is stated for every such `ν`. The canonical divisor
of `X⁺` is `g_*K`, so that `K_{X⁺} + D⁺ = g_*(K_X + D)`; that it is a canonical divisor and that
`g_*K + g_*D` is `ℚ`-Cartier is `MMP.Flips.smallLogDiscrepancySet_subset_of_isFlip`, and the
sets `𝒮_t(X⁺, D⁺; B⁺)` are formed with any proofs of these facts.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.14
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

section Center

/-- If the valuation ring of `w` dominates the local ring of `X` at `x`, the valuation ring of
`w ∘ φ^*` dominates the local ring of `Z` at `φ(x)`, for a dominant `φ : X ⟶ Z`. -/
private theorem dominates_map {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] (φ : X ⟶ Z)
    [IsDominant φ] (w : Valuation X.functionField ℤᵐ⁰) {x : X}
    (h1 : ∀ a : X.presheaf.stalk x, w (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      w (algebraMap _ X.functionField a) < 1) :
    (∀ a : Z.presheaf.stalk (φ x),
      w.comap (functionFieldMap φ) (algebraMap _ Z.functionField a) ≤ 1) ∧
    ∀ a ∈ IsLocalRing.maximalIdeal (Z.presheaf.stalk (φ x)),
      w.comap (functionFieldMap φ) (algebraMap _ Z.functionField a) < 1 := by
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h1 _
  · rw [Valuation.comap_apply, functionFieldMap_algebraMap_stalk]
    exact h2 _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu =>
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))

/-- Let `φ : X ⟶ Z` and `φ' : X' ⟶ Z` be dominant, with `Z` separated over `k`, and `v`, `v'`
valuations of `k(X)`, `k(X')` agreeing on `k(Z)`. If `v` dominates the local ring at `x` and `v'`
the local ring at `x'`, then `φ(x) = φ'(x')`. -/
private theorem map_eq_of_comap_eq {k : Type u} [Field k] {X X' Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral Z] (sZ : Z ⟶ Spec (.of k)) [IsSeparated sZ] (φ : X ⟶ Z)
    (φ' : X' ⟶ Z) [IsDominant φ] [IsDominant φ'] {v : Valuation X.functionField ℤᵐ⁰}
    {v' : Valuation X'.functionField ℤᵐ⁰}
    (hv : v.comap (functionFieldMap φ) = v'.comap (functionFieldMap φ')) {x : X} {x' : X'}
    (h1 : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1)
    (h1' : ∀ a : X'.presheaf.stalk x', v' (algebraMap _ X'.functionField a) ≤ 1)
    (h2' : ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x'),
      v' (algebraMap _ X'.functionField a) < 1) :
    φ x = φ' x' := by
  obtain ⟨d1, d2⟩ := dominates_map φ v h1 h2
  obtain ⟨d1', d2'⟩ := dominates_map φ' v' h1' h2'
  rw [← hv] at d1' d2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sZ _ d1 d2 d1' d2'

end Center

section Topology

/-- If `φ` is an open immersion over an open `U`, then `φ` reflects specializations
`φ a ⤳ φ b` with `φ b ∈ U`. -/
private theorem specializes_of_map_specializes {X Z : Scheme.{u}} {φ : X ⟶ Z} {U : Z.Opens}
    (hU : IsOpenImmersion ((φ ⁻¹ᵁ U).ι ≫ φ)) {a b : X} (hb : φ b ∈ U) (h : φ a ⤳ φ b) :
    a ⤳ b :=
  ((((φ ⁻¹ᵁ U).ι ≫ φ).isOpenEmbedding.isInducing.specializes_iff
    (x := ⟨a, h.mem_open U.isOpen hb⟩) (y := ⟨b, hb⟩)).1 h).map continuous_subtype_val

end Topology

section SmallContraction

/-- On a variety of dimension `3`, there is no chain `a ⤳ b ⤳ c` of distinct points with
`coheight a ≥ 2`. -/
private theorem false_of_two_le_coheight_of_specializes {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX) (hdim : topologicalKrullDim X = 3)
    {a b c : X} (ha : 2 ≤ Order.coheight a) (hab : a ⤳ b) (hbc : b ⤳ c) (hab' : a ≠ b)
    (hbc' : b ≠ c) : False := by
  have := hX.toIsIntegral
  have := hX.toLocallyOfFiniteType
  have h := topologicalKrullDim_closure_singleton_add_coheight sX a
  have h2 := two_le_topologicalKrullDim_of_specializes (S := closure {a}) (subset_closure rfl)
    hab.mem_closure (hab.trans hbc).mem_closure hab hbc hab' hbc'
  rw [hdim] at h
  have h4 : (2 : WithBot ℕ∞) + 2 ≤ 3 := h ▸ add_le_add h2 (WithBot.coe_le_coe.mpr ha)
  exact absurd h4 (by decide)

/-- A morphism which is an open immersion on an open `O` is injective on `O`. -/
private theorem eq_of_isOpenImmersion {X Z : Scheme.{u}} {φ : X ⟶ Z} {O : X.Opens}
    (hO : IsOpenImmersion (O.ι ≫ φ)) {a b : X} (ha : a ∈ O) (hb : b ∈ O) (h : φ a = φ b) :
    a = b :=
  congrArg Subtype.val ((O.ι ≫ φ).isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h)

/-- A small contraction of a threefold is an open immersion off a closed set `V` from
which no chain `a ⤳ b ⤳ c` of distinct points starts. -/
private theorem exists_closeds_of_isSmall {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ)
    (hX : topologicalKrullDim X = 3) :
    ∃ V : Closeds X, (∀ a ∈ V, ∀ b c : X, a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False) ∧
      IsOpenImmersion ((show X.Opens from V.compl).ι ≫ φ) := by
  obtain ⟨V, W', hV, -, hle, hiso⟩ := hφ.exists_isIso
  rw [le_closedsCodimension_iff_le_coheight] at hV
  have hVc : IsOpenImmersion ((show X.Opens from V.compl).ι ≫ φ) := by
    rw [← Scheme.Hom.resLE_comp_ι φ hle]; infer_instance
  exact ⟨V, fun a ha _ _ =>
    false_of_two_le_coheight_of_specializes sX hφ.isVariety_source hX (hV a ha), hVc⟩

/-- In a Noetherian space, let `V` be a closed set from which no chain `a ⤳ b ⤳ c` of distinct
points starts. Then only finitely many non-closed points lie in `V`: each is the generic point of
an irreducible component of `V`. -/
private theorem finite_inter_of_forall_exists_specializes {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] [T0Space X] {V F : Set X} (hV : IsClosed V)
    (hchain : ∀ a ∈ V, ∀ b c : X, a ⤳ b → b ⤳ c → a ≠ b → b ≠ c → False)
    (hF : ∀ y ∈ F, ∃ y', y ⤳ y' ∧ y ≠ y') : (F ∩ V).Finite := by
  obtain ⟨S, hSfin, hScl, hSirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hV
  refine (hSfin.biUnion fun t _ => Set.Subsingleton.finite
    (s := {y | IsGenericPoint y t}) fun a ha b hb => ha.eq hb).subset ?_
  rintro y ⟨hyF, t, htS, hyt⟩
  have hg := (hSirr t htS).isGenericPoint_genericPoint_closure
  rw [(hScl t htS).closure_eq] at hg
  obtain ⟨y', hyy', hne⟩ := hF y hyF
  refine Set.mem_biUnion htS (by_contra fun hgy => ?_)
  exact hchain _ ⟨t, htS, hg.mem⟩ y y' (hg.specializes hyt) hyy' (fun h => hgy (h ▸ hg)) hne

/-- A contraction is a local isomorphism at every point whose fibre is finite. -/
private theorem notMem_exceptionalSet_of_finite_preimage {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z}
    (hφ : IsContraction k sZ sX φ) {x : X} (hfin : (φ ⁻¹' {φ x}).Finite) :
    x ∉ exceptionalSet φ := by
  have : IsProper φ := hφ.isProper
  obtain ⟨U, hzU, hfinU⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton φ (φ x) hfin
  obtain ⟨Va, hVa, hzVa, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := U.toScheme) (x := ⟨φ x, hzU⟩) (U := ⊤) trivial
  have hiso : IsIso ((φ ∣_ U).app Va) := by
    rw [morphismRestrict_app]
    exact IsIso.comp_isIso' (hφ.isIso_app _) (by
      rw [eqToHom_op, eqToHom_map]; exact CategoryTheory.instIsIsoEqToHom _)
  have : IsIso (φ ∣_ (U.ι ''ᵁ Va)) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict φ U Va)).mp ((isIso_morphismRestrict_iff_isIso_app _ hVa).mpr hiso)
  refine fun hx => hx ⟨φ ⁻¹ᵁ (U.ι ''ᵁ Va), ⟨⟨φ x, hzU⟩, hzVa, rfl⟩, ?_⟩
  rw [← morphismRestrict_ι]; infer_instance

/-- A small contraction of a threefold maps every point of its exceptional set to a closed
point. -/
private theorem isClosed_singleton_map_of_mem_exceptionalSet {k : Type u} [Field k]
    {X Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z}
    (hφ : IsSmall k sZ sX φ) (hX : topologicalKrullDim X = 3) {x : X}
    (hx : x ∈ exceptionalSet φ) : IsClosed ({φ x} : Set Z) := by
  have := hφ.isVariety_source.toLocallyOfFiniteType
  have := hφ.isVariety_source.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsNoetherian X := ⟨⟩
  have : IsProper φ := hφ.isProper
  obtain ⟨V, hchain, hVc⟩ := exists_closeds_of_isSmall hφ hX
  by_contra hzc
  refine notMem_exceptionalSet_of_finite_preimage hφ.toIsContraction ?_ hx
  have hnc : ∀ y ∈ φ ⁻¹' {φ x}, ∃ y', y ⤳ y' ∧ y ≠ y' := by
    intro y (hy : φ y = φ x)
    by_contra! h
    have hy' : IsClosed ({y} : Set X) := closure_subset_iff_isClosed.mp fun t ht =>
      (h t (specializes_iff_mem_closure.mpr ht)).symm
    have := φ.isClosedMap _ hy'
    rw [Set.image_singleton, hy] at this
    exact hzc this
  rw [← Set.inter_union_diff (φ ⁻¹' {φ x}) V]
  exact (finite_inter_of_forall_exists_specializes V.isClosed hchain hnc).union
    (Set.Subsingleton.finite fun a ha b hb =>
      eq_of_isOpenImmersion hVc ha.2 hb.2 (ha.1.trans hb.1.symm))

/-- On a Jacobson scheme, a point `s` off the exceptional set of `φ` whose specializations all
lie in its fibre is closed. -/
private theorem isClosed_singleton_of_notMem_exceptionalSet {X Z : Scheme.{u}} [JacobsonSpace X]
    {φ : X ⟶ Z} {s : X} (hs : s ∉ exceptionalSet φ) (hfib : ∀ t, s ⤳ t → φ t = φ s) :
    IsClosed ({s} : Set X) := by
  obtain ⟨O, hsO, hO⟩ := exists_isOpenImmersion_of_notMem_exceptionalSet hs
  refine isClosed_singleton_of_isLocallyClosed_singleton
    ⟨O, closure {s}, O.isOpen, isClosed_closure, Set.ext fun t => ⟨?_, ?_⟩⟩
  · rintro rfl
    exact ⟨hsO, subset_closure rfl⟩
  · rintro ⟨htO, ht⟩
    exact eq_of_isOpenImmersion hO htO hsO (hfib t (specializes_iff_mem_closure.mpr ht))

/-- A dimension `d` with `d + 2 = 3` is `1`. -/
private theorem eq_one_of_add_two_eq_three {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 3) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have h3 : ((3 : ℕ∞) : WithBot ℕ∞) = 3 := rfl
      rw [← h3, ← WithBot.coe_add, WithBot.coe_inj] at h
      have : n + 2 = 3 := by exact_mod_cast h
      obtain rfl : n = 1 := by omega
      rfl

/-- For a small contraction `φ` of a threefold, a point `ξ ∉ Ex(φ)` whose closure is a curve
maps off `φ(Ex φ)`. -/
private theorem map_notMem_image_exceptionalSet {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φ : X ⟶ Z} (hφ : IsSmall k sZ sX φ)
    (hX : topologicalKrullDim X = 3) {ξ : X} (hξ : ξ ∉ exceptionalSet φ)
    (hdim : topologicalKrullDim (closure {ξ} : Set X) = 1) :
    φ ξ ∉ φ '' exceptionalSet φ := by
  rintro ⟨e, he, hee⟩
  have := hφ.isVariety_source.toLocallyOfFiniteType
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hz := hee ▸ isClosed_singleton_map_of_mem_exceptionalSet hφ hX he
  have hcl := isClosed_singleton_of_notMem_exceptionalSet hξ fun t ht => by
    simpa [hz.closure_eq] using (ht.map φ.continuous).mem_closure
  rw [hcl.closure_eq] at hdim
  have h0 := hdim ▸ topologicalKrullDim_zero_of_discreteTopology ({ξ} : Set X)
  exact absurd h0 (by decide)

end SmallContraction

section DivisorCenter

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}

/-- The center of a proper divisor over `X` is the closure of the point `f(η_E)`. -/
private theorem coe_center_eq_closure (E : ProperDivisorOver k sX) :
    (E.center : Set X) = closure {E.f E.E.genericPoint} := by
  rw [E.center_eq_toDivisorOver_center]
  exact E.toDivisorOver.center_eq_closure_genericPoint

/-- The codimension of the center of a proper divisor over `X` is the coheight of `f(η_E)`. -/
private theorem codimension_center (E : ProperDivisorOver k sX) :
    codimension E.center = Order.coheight (E.f E.E.genericPoint) := by
  rw [E.center_eq_toDivisorOver_center, MMP.Positivity.DivisorOver.codimension_center]

end DivisorCenter

/-- **Szabó's sets of small log discrepancy shrink under flips** (FA 4.14). Let `X` be a normal
threefold with canonical divisor `K`, `D` a `ℚ`-divisor with `K_X + D` `ℚ`-Cartier, and
`φ⁺ : X⁺ ⟶ Z` with `g : X ⤏ X⁺` a flip of the small contraction `φ : X ⟶ Z` with respect to
`K_X + D` (`MMP.Flips.IsFlip`). Let `B = ⋃_{P ∈ Ps} P` for a finite set `Ps` of prime divisors of
`X`, and `B⁺ = ⋃_{P ∈ Ps} g_*P`. If no flipping curve of `φ` (`MMP.Flips.IsFlippingCurve`) is
contained in `B`, then `g_*K` is a canonical divisor of `X⁺`, `g_*K + g_*D` is `ℚ`-Cartier, and
for every `t ∈ ℚ`, each `ν⁺ ∈ 𝒮_t(X⁺, g_*D; B⁺)` corresponds to a valuation
`ν` of `k(X)` (with `ν ∘ φ^* = ν⁺ ∘ φ⁺^*`), and every such `ν` lies in `𝒮_t(X, D; B)`
(`MMP.Flips.smallLogDiscrepancySetOff`). -/
@[mmp "lem_fa4_szabo_set_shrinks_under_flip"]
public theorem smallLogDiscrepancySetOff_subset_of_isFlip {k : Type u} [Field k]
    {X Z X' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsIntegral Z]
    {K : Divisor X} {D : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ]
    [IsDominant φp] {g : X.RationalMap X'}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX 3)
    (hD : (Divisor.toQDivisor K + D).IsQCartier)
    (hflip : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g)
    (Ps : Finset (Mori.PrimeDivisor X)) (B : Closeds X) (B' : Closeds X')
    (hB : (B : Set X) = ⋃ P ∈ Ps, P.support)
    (hB' : (B' : Set X') = ⋃ P ∈ Ps, ⋃ (P' : Mori.PrimeDivisor X')
      (_ : Mori.RationalMap.transformPrimeDivisor g P = some P'), P'.support)
    (hcurve : ∀ C : Set X, IsFlippingCurve k sX sZ φ C → ¬ C ⊆ B) :
    ∃ (hK' : Divisor.IsCanonicalDivisor sX' 3 (Mori.RationalMap.transformDivisor g K))
      (hD' : (Divisor.toQDivisor (Mori.RationalMap.transformDivisor g K) +
        Mori.RationalMap.transformDivisor g D).IsQCartier),
      ∀ (t : ℚ) (ν' : Valuation X'.functionField ℤᵐ⁰),
        ν' ∈ smallLogDiscrepancySetOff sX' 3 (Mori.RationalMap.transformDivisor g K)
          (Mori.RationalMap.transformDivisor g D) hflip.isNormalVariety_flip hK' hD' B' t →
        (∃ ν : Valuation X.functionField ℤᵐ⁰,
          ν.comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp)) ∧
        ∀ ν : Valuation X.functionField ℤᵐ⁰,
          ν.comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp) →
          ν ∈ smallLogDiscrepancySetOff sX 3 K D hX hK hD B t := by
  obtain ⟨hK', hD', hmain⟩ := smallLogDiscrepancySet_subset_of_isFlip hX hK hD hflip
  refine ⟨hK', hD', fun t ν' hν' => ?_⟩
  obtain ⟨hex, hall⟩ := hmain t ν' hν'.1
  refine ⟨hex, fun ν hν => ⟨hall ν hν, fun E hEν ⟨hcod, hsub⟩ => ?_⟩⟩
  obtain ⟨E', -, hE'ν⟩ := hν'.1.2.1
  haveI : IsSeparated sZ := hflip.isNormalVariety_target.1.toIsSeparated
  haveI : IsProper φ := hflip.isContraction.isProper
  have hφs : IsSmall k sZ sX φ := hflip.isSmall_source
  have hdim : topologicalKrullDim X = 3 := by exact_mod_cast hK.topologicalKrullDim_eq
  haveI := E.toDivisorOver.isIntegral
  haveI := E'.toDivisorOver.isIntegral
  -- `ξ`, `ξ'`: the generic points of the centers of `ν` on `X` and on `X⁺`
  set ξ := E.f E.E.genericPoint
  set ξ' := E'.f E'.E.genericPoint
  have hξξ' : φ ξ = φp ξ' :=
    map_eq_of_comap_eq sZ φ φp (v := E.valuation) (v' := E'.valuation)
      (by rw [hEν, hE'ν]; exact hν)
      (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E.toDivisorOver _ rfl)
      (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E.toDivisorOver _ rfl)
      (MMP.Positivity.DivisorOver.valuation_algebraMap_le_one E'.toDivisorOver _ rfl)
      (MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one E'.toDivisorOver _ rfl)
  have hcoh : Order.coheight ξ = 2 := codimension_center E ▸ hcod
  have hdimW : topologicalKrullDim (closure {ξ} : Set X) = 1 := eq_one_of_add_two_eq_three <| by
    simpa [hcoh, hdim] using topologicalKrullDim_closure_singleton_add_coheight sX ξ
  have hWB : closure {ξ} ⊆ (B : Set X) := coe_center_eq_closure E ▸ hsub
  -- `ξ ∉ Ex(φ)`: otherwise the center would be a flipping curve in `B`
  have hξEx : ξ ∉ exceptionalSet φ := fun h =>
    hcurve _ (isFlippingCurve_of_subset_exceptionalSet hφs hdim
      isIrreducible_singleton.closure isClosed_closure hdimW
      ((isClosed_exceptionalSet φ).closure_subset_iff.2 (Set.singleton_subset_iff.2 h))) hWB
  -- `φ⁺` is an isomorphism over `U = Z ∖ φ(Ex φ)`, which contains `φ⁺(ξ') = φ(ξ)`
  let U : Z.Opens := ⟨(φ '' exceptionalSet φ)ᶜ,
    (φ.isClosedMap _ (isClosed_exceptionalSet φ)).isOpen_compl⟩
  have hflip' : IsFlip k sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + D)) φ φp g := by
    rwa [map_add, QDivisor.toRDivisor_toQDivisor]
  haveI : IsIso (φp ∣_ U) :=
    hflip'.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hD U disjoint_compl_left
  have hO' : IsOpenImmersion ((φp ⁻¹ᵁ U).ι ≫ φp) := by
    rw [← morphismRestrict_ι]; infer_instance
  have hξ'U : φp ξ' ∈ U := hξξ' ▸ map_notMem_image_exceptionalSet hφs hdim hξEx hdimW
  have hξ'Ex : ξ' ∉ exceptionalSet φp := fun h => h ⟨_, hξ'U, hO'⟩
  refine hν'.2 E' hE'ν ⟨?_, ?_⟩
  · -- the center on `X⁺` has codimension `2`
    rw [codimension_center, ← coheight_map_of_notMem_exceptionalSet hξ'Ex, ← hξξ',
      coheight_map_of_notMem_exceptionalSet hξEx, hcoh]
  · -- the center on `X⁺` lies in `B⁺`: it is a specialization of `g_*P` for a component `P ∋ ξ`
    rw [coe_center_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.2 ?_) B'.isClosed
    have hξB := hWB (subset_closure rfl)
    rw [hB] at hξB
    obtain ⟨P, hP, hξP⟩ := Set.mem_iUnion₂.1 hξB
    have he := (exceptional_hasNonemptyCenter_iff_of_isSmall sX sX' sZ φ φp hφs
      hflip.isSmall).2 g hflip.isModificationOf
    set e := primeDivisorEquivOfModification hφs hflip.isSmall hflip.isModificationOf
    obtain ⟨hPt, hPv⟩ := he P
    have hηη : φ P.genericPoint = φp (e P).genericPoint :=
      map_eq_of_comap_eq sZ φ φp hPv.symm
        (fun a => (P.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩)
        (fun a ha => (P.divisorialValuation_algebraMap_lt_one_iff a).2 ha)
        (fun a => ((e P).divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩)
        (fun a ha => ((e P).divisorialValuation_algebraMap_lt_one_iff a).2 ha)
    have hPξ : P.genericPoint ⤳ ξ := by
      rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hsp := specializes_of_map_specializes hO' hξ'U (hηη ▸ hξξ' ▸ hPξ.map φ.continuous)
    rw [hB']
    refine Set.mem_iUnion₂.2 ⟨P, hP, Set.mem_iUnion₂.2 ⟨e P, hPt, ?_⟩⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.1 hsp

end MMP.Flips

end
