module

public import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback
public import MMP.AlgebraicGeometry.MMP.Abundance.TriviallyConnectedDivisor

/-!
# Trivially connected divisors across a projective numerically trivial small modification

Let `φ : X ⟶ T` and `ψ : Y ⟶ T` be proper birational morphisms of normal projective complex
threefolds, both isomorphisms in codimension one, let `(X, Δ)` be a klt pair with `K_X + Δ` nef and
numerically `φ`-trivial, and let `K_Y`, `Δ_Y` be the birational transforms of `K_X`, `Δ` on `Y`.
If a prime divisor `E` on `X` is `(K_X + Δ)`-trivially connected, then so is its strict transform
`E⁺` on `Y` with respect to `K_Y + Δ_Y`.

There are `r > 0` and a Cartier divisor `M` on `T` with `φ^* M = r (K_X + Δ)` and
`ψ^* M = r (K_Y + Δ_Y)`. For a proper curve `C ⊆ E⁺`, the projection formula gives
`deg_C ψ^* 𝒪_T(M) = deg 𝒪_T(M)` on `ψ_*[C]`. This vanishes when `ψ(C)` is a point. Otherwise
`ψ(C)` is a curve in `φ(E)`, dominated by a proper curve `Γ ⊆ E` that `φ` does not contract.
Since `(K_X + Δ) · Γ = 0`, the degree of `𝒪_T(M)` on `ψ(C)` vanishes. So every curve of `E⁺` is
`(K_Y + Δ_Y)`-trivial. Two closed points of `E⁺` lie on the image of the support of an
effective ample divisor on the normalization of `E⁺`, which is a connected union of curves
of `E⁺`.

## Main results

* `MMP.Flips.IsTriviallyConnected.transform_of_isIsoInCodimOne`

## Implementation notes

The statement is over `ℂ`, the base field over which numerical triviality of curves in a
trivially connected divisor is available.

The strict transform of `E` and the divisors `K_Y`, `Δ_Y` are the birational transforms through
`T`: first `MMP.Mori.RationalMap.transformDivisor` along `φ` (resp. `MMP.Flips.flopBaseDivisor`),
then `MMP.Mori.inverseTransformDivisor` along `ψ`, exactly as in
`MMP.Flips.IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.6, 15.9
-/

section

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips

namespace MMP.FourfoldProofs.FourfoldFa15ProjectiveFlopTrivialConnectedPreservedProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- On a normal scheme, irreducible and locally of finite type over a field, of dimension at
least two, the local ring at every closed point has depth at least two. -/
private theorem two_le_depth_stalk {k : Type} [Field k] {N : Scheme.{0}}
    (sN : N ⟶ Spec (.of k)) [LocallyOfFiniteType sN] [IrreducibleSpace N]
    [IsLocallyNoetherian N] [IsNormal N] (hdim : 2 ≤ topologicalKrullDim N)
    (x : N) (hx : IsClosed ({x} : Set N)) :
    (2 : ℕ∞) ≤ Module.depth (N.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (N.presheaf.stalk x)) (N.presheaf.stalk x) := by
  have h := (hasPropertySk_iff N 2).mp (hasPropertySk_two_of_isNormal N) x
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k N sN x hx,
    topologicalKrullDimAt_eq_topologicalKrullDim_of_equidimensional k N sN
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace N) x, Nat.cast_ofNat,
    min_eq_left hdim] at h
  exact WithBot.coe_le_coe.1 h

/-- **A connected ample support through a closed set.** On a normal projective variety `N` of
dimension at least two over `k`, every closed subset `T` not containing the generic point lies in
a closed connected subset not containing the generic point: the support of an effective ample
Cartier divisor containing `T`. -/
private theorem exists_isConnected_of_isNormal {k : Type} [Field k] {N : Scheme.{0}}
    (sN : N ⟶ Spec (.of k)) [IsIntegral N] [IsNormal N] [IsLocallyNoetherian N]
    [LocallyOfFiniteType sN] (hN : Mori.IsProjectiveVariety k sN)
    (hd : 2 ≤ topologicalKrullDim N) {T : Set N} (hT : IsClosed T) (hη : genericPoint N ∉ T) :
    ∃ A : Set N, IsClosed A ∧ _root_.IsConnected A ∧ T ⊆ A ∧ genericPoint N ∉ A := by
  haveI := hN
  haveI : IsProper sN := inferInstance
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ :=
    AlgebraicGeometry.exists_isAmple_of_isProjectiveMorphism sN M hMa hN.isProjective
  obtain ⟨I, hI, hTI, hηI, n, hn, ⟨e⟩⟩ :=
    MMP.Threefold.Resolution.exists_isEffectiveCartierDivisor_of_isAmple L hLa hT hη
  haveI := hI
  haveI := Stacks.Divisors.isInvertible_divisorSheaf I
  have hIa : Stacks.Ample.IsAmple N (Stacks.Divisors.divisorSheaf I) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
      (Stacks.AmplePositivePower.isAmple_tensorPowModule_of_isAmple L n hn hLa)
  exact ⟨I.support, I.support.isClosed,
    MMP.Mori.isConnected_support_of_two_le_depth sN (two_le_depth_stalk sN hd) I hIa, hTI, hηI⟩

/-- In the specialization order on a scheme, `x ≤ y` and `x ≠ y` give `x < y`. -/
private theorem lt_of_le_of_ne_of_specializes {X : Scheme.{0}} {x y : X} (h : x ≤ y)
    (hne : x ≠ y) : x < y :=
  lt_of_le_not_ge h fun h' => hne (Specializes.antisymm (h' : x ⤳ y) (h : y ⤳ x)).eq

/-- The dimension of the reduced closed subscheme on the closure of `x` is the height
of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt {X : Scheme.{0}} (x : X) :
    topologicalKrullDim (curveSubschemeAt x) = Order.height x := by
  have h := MMP.Intersection.subvarietyDim_eq_height (MMP.Intersection.associatedSubvariety x)
  rw [MMP.Intersection.genericPoint_associatedSubvariety] at h
  exact h

/-- On an integral `k`-scheme of dimension three, the generic point of a prime divisor has
height two. -/
private theorem height_genericPoint_eq_two {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 3) (P : Mori.PrimeDivisor Y) :
    Order.height P.genericPoint = 2 := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := ‹LocallyOfFiniteType sY›
  have hpure : MMP.Intersection.IsPureDimensional Y 3 := by
    intro Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [(Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq, hdim]
    rfl
  have h := MMP.Intersection.height_add_coheight_eq_of_isPureDimensional k hpure P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P] at h
  have h3 : ((3 : ℕ) : ℕ∞) = 2 + 1 := rfl
  rw [h3] at h
  exact WithTop.add_right_cancel ENat.one_ne_top h

/-- A point strictly specializing a point of height two has height at most one. -/
private theorem height_le_one_of_lt {α : Type*} [Preorder α] {x y : α} (hy : Order.height y = 2)
    (h : x < y) : Order.height x ≤ 1 := by
  have h' := Order.height_add_one_le h
  rw [hy, show (2 : ℕ∞) = 1 + 1 from rfl] at h'
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

/-- A point of height zero is closed. -/
private theorem isClosed_singleton_of_height_eq_zero {X : Scheme.{0}} {x : X}
    (h : Order.height x = 0) : IsClosed ({x} : Set X) := by
  rw [Order.height_eq_zero] at h
  refine isClosed_of_closure_subset fun y hy => ?_
  have h1 : x ⤳ y := specializes_iff_mem_closure.2 hy
  have h2 : y ⤳ x := h (show y ≤ x from h1)
  exact Set.mem_singleton_iff.2 (h2.antisymm h1).eq

open Order in
/-- **A connected closed set of curves is a union of proper curves.** Let `Y` be proper over `k`
and noetherian, `η` a point of height two, and `W ⊆ {η}⁻` a closed connected subset not
containing `η` but containing a point of height one. Then `W` is the union of the finitely many
proper curves it contains. -/
private theorem exists_curveUnion_eq {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsProper sY] [IsLocallyNoetherian Y] [CompactSpace Y]
    {η : Y} (hη : height η = 2) {W : Set Y} (hW : IsClosed W) (hWc : _root_.IsConnected W)
    (hWη : W ⊆ closure {η}) (hηW : η ∉ W) {c : Y} (hcW : c ∈ W) (hc : height c = 1) :
    ∃ S : Finset (ProperCurve sY), curveUnion sY S = W := by
  classical
  haveI : IsNoetherian Y := ⟨⟩
  have hle : ∀ w ∈ W, height w ≤ 1 := fun w hw =>
    height_le_one_of_lt hη (lt_of_le_of_ne_of_specializes
      (specializes_iff_mem_closure.2 (hWη hw) : η ⤳ w) fun h => hηW (h ▸ hw))
  obtain ⟨S0, hS0f, hS0c, hS0i, hWS0⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hW
  let gen : S0 → Y := fun t => (hS0i t.1 t.2).genericPoint
  have hgen : ∀ t : S0, closure {gen t} = (t : Set Y) := fun t => by
    have := (hS0i t.1 t.2).isGenericPoint_genericPoint_closure
    rwa [(hS0c t.1 t.2).closure_eq] at this
  have hgenW : ∀ t : S0, gen t ∈ W := fun t => by
    rw [hWS0]
    exact Set.mem_sUnion_of_mem (hgen t ▸ subset_closure rfl) t.2
  have hsub : ∀ w ∈ W, ∃ t : S0, w ∈ (t : Set Y) := fun w hw => by
    rw [hWS0] at hw
    obtain ⟨t, ht, hwt⟩ := hw
    exact ⟨⟨t, ht⟩, hwt⟩
  set G : Set Y := {w | w ∈ W ∧ height w = 1} with hG
  have hGsub : G ⊆ Set.range gen := by
    rintro w ⟨hw, hw1⟩
    have hirr : IsIrreducible (closure ({w} : Set Y)) := isIrreducible_singleton.closure
    have hcov : closure ({w} : Set Y) ⊆ ⋃₀ ↑(hS0f.toFinset) := by
      rw [Set.Finite.coe_toFinset, ← hWS0]
      exact hW.closure_subset_iff.2 (Set.singleton_subset_iff.2 hw)
    obtain ⟨t, ht, hwt⟩ := (isIrreducible_iff_sUnion_isClosed.1 hirr) hS0f.toFinset
      (fun z hz => hS0c z (hS0f.mem_toFinset.1 hz)) hcov
    rw [Set.Finite.mem_toFinset] at ht
    refine ⟨⟨t, ht⟩, ?_⟩
    have hwg : w ≤ gen ⟨t, ht⟩ := (specializes_iff_mem_closure.2
      ((hgen ⟨t, ht⟩).symm ▸ hwt (subset_closure rfl)) : gen ⟨t, ht⟩ ⤳ w)
    have hg1 : height (gen ⟨t, ht⟩) = 1 :=
      le_antisymm (hle _ (hgenW _)) (hw1 ▸ Order.height_mono hwg)
    by_contra hne
    have hlt : w < gen ⟨t, ht⟩ := lt_of_le_of_ne_of_specializes hwg (Ne.symm hne)
    have := Order.height_strictMono hlt (by rw [hw1]; exact ENat.one_lt_top)
    rw [hw1, hg1] at this
    exact lt_irrefl _ this
  haveI : Finite S0 := hS0f.to_subtype
  have hGf : G.Finite := (Set.finite_range gen).subset hGsub
  have hcurve : ∀ w ∈ G, IsProperCurve sY w := by
    rintro w ⟨-, hw1⟩
    exact isProperCurve_of_isProper sY
      ((topologicalKrullDim_curveSubschemeAt w).trans (by rw [hw1]; rfl))
  have hinj : Function.Injective (fun C : ProperCurve sY => C.point) := fun _ _ =>
    ProperCurve.ext
  have hSf : {C : ProperCurve sY | C.point ∈ G}.Finite :=
    hGf.preimage hinj.injOn
  refine ⟨hSf.toFinset, ?_⟩
  apply subset_antisymm
  · refine Set.iUnion₂_subset fun C hC => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hC
    exact hW.closure_subset_iff.2 (Set.singleton_subset_iff.2 hC.1)
  · intro x hx
    by_contra hxU
    have hmemU : ∀ w ∈ G, x ∉ closure ({w} : Set Y) := fun w hw hxw => hxU
      (Set.mem_biUnion (x := ⟨w, hcurve w hw⟩)
        (by
          simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
          exact hw) hxw)
    obtain ⟨t, hxt⟩ := hsub x hx
    have hg0 : ∀ t : S0, x ∈ (t : Set Y) → height (gen t) = 0 ∧ (t : Set Y) = {x} := by
      intro t hxt
      have hg1 : height (gen t) ≠ 1 := fun h1 =>
        hmemU (gen t) ⟨hgenW t, h1⟩ ((hgen t).symm ▸ hxt)
      have hg0 : height (gen t) = 0 :=
        (ENat.le_one_iff_eq_zero_or_eq_one.1 (hle _ (hgenW t))).resolve_right hg1
      refine ⟨hg0, ?_⟩
      rw [← hgen t, (isClosed_singleton_of_height_eq_zero hg0).closure_eq] at hxt ⊢
      rw [Set.mem_singleton_iff.1 hxt]
    obtain ⟨hgt0, htx⟩ := hg0 t hxt
    have hxc : IsClosed ({x} : Set Y) := htx ▸ hS0c t.1 t.2
    set U : Set Y := ⋃₀ {t' | t' ∈ S0 ∧ x ∉ t'} with hU
    have hUc : IsClosed U := Set.Finite.isClosed_sUnion (hS0f.subset fun t' ht' => ht'.1)
      fun t' ht' => hS0c t' ht'.1
    have hxU' : x ∉ U := fun ⟨t', ht', hxt'⟩ => ht'.2 hxt'
    have hWsplit : W ⊆ {x} ∪ U := by
      intro y hy
      obtain ⟨t', hyt'⟩ := hsub y hy
      by_cases hxt' : x ∈ (t' : Set Y)
      · obtain ⟨-, h⟩ := hg0 t' hxt'
        rw [h] at hyt'
        exact Or.inl hyt'
      · exact Or.inr ⟨t', ⟨t'.2, hxt'⟩, hyt'⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hWc.isPreconnected) {x} U
        hxc hUc hWsplit (by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          rintro - rfl hy
          exact hxU' hy) with h | h
    · have hcx := Set.mem_singleton_iff.1 (h hcW)
      have hgx : gen t = x := by
        have := hgen t ▸ (subset_closure rfl : gen t ∈ closure {gen t})
        rwa [htx] at this
      rw [hcx, ← hgx, hgt0] at hc
      exact zero_ne_one hc
    · exact hxU' (h hx)

/-- **Two closed points of a surface in a projective threefold lie on a connected curve.** Let
`Y` be a projective variety over `k` and `P` a prime divisor of `Y`, with `dim Y = 3`. Any two
closed points of `P` lie on a connected union of finitely many proper irreducible curves
contained in `P`. -/
private theorem exists_isConnected_curveUnion {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType sY] (hY : Mori.IsProjectiveVariety k sY)
    (hdim : topologicalKrullDim Y = 3) (P : Mori.PrimeDivisor Y) {x₁ x₂ : Y}
    (hx₁ : x₁ ∈ P.support) (hx₂ : x₂ ∈ P.support) (hc₁ : IsClosed {x₁}) (hc₂ : IsClosed {x₂}) :
    ∃ S : Finset (ProperCurve sY), _root_.IsConnected (curveUnion sY S) ∧
      curveUnion sY S ⊆ P.support ∧ x₁ ∈ curveUnion sY S ∧ x₂ ∈ curveUnion sY S := by
  classical
  haveI := hY
  haveI : IsProper sY := inferInstance
  haveI : AlgebraicGeometry.IsVariety k sY := hY.toIsVariety
  set η := P.genericPoint with hηdef
  have hsupp : (P.support : Set Y) = closure {η} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  rw [hsupp] at hx₁ hx₂ ⊢
  have hη2 : Order.height η = 2 := height_genericPoint_eq_two sY hdim P
  obtain ⟨c, hcη, hc1⟩ := (Order.coe_lt_height_iff (n := 1) (x := η)
    (by rw [hη2]; exact ENat.coe_lt_top 2)).1 (by rw [hη2]; exact Nat.one_lt_ofNat)
  have hcη' : c ∈ closure ({η} : Set Y) := specializes_iff_mem_closure.1 (hcη.le : η ⤳ c)
  set Z := curveSubschemeAt η
  set ι := curveSubschemeAtι η
  haveI : IsIntegral Z :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  haveI : AlgebraicGeometry.IsVariety k (ι ≫ sY) := { }
  have hrange : Set.range ι = closure {η} := range_curveSubschemeAtι η
  have hZd : topologicalKrullDim Z = 2 :=
    (topologicalKrullDim_curveSubschemeAt η).trans (by rw [hη2]; rfl)
  have hZp : AlgebraicGeometry.IsProjectiveVariety k (ι ≫ sY) := by
    obtain ⟨n, i, hi, hi'⟩ := hY.isProjective
    exact { isProjective := ⟨n, ι ≫ i, inferInstance, by rw [Category.assoc, hi']⟩ }
  obtain ⟨⟨hνv, hνn, hνf, hνs, hνb⟩, ⟨U, hU, hUiso⟩, -, -, hνp⟩ :=
    MMP.Threefold.normalization_spec (ι ≫ sY)
  set hfin := MMP.finite_irreducibleComponents_of_isIntegral Z
  set N := Z.normalizationScheme hfin
  set ν := Z.normalization hfin
  haveI := hνv
  haveI := hνn
  haveI := hνf
  haveI : IsIntegral N := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := ν ≫ ι ≫ sY)
  haveI : LocallyOfFiniteType (ν ≫ ι ≫ sY) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (ν ≫ ι ≫ sY)
  have hNd : topologicalKrullDim N = 2 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι ≫ sY) (ν ≫ ι ≫ sY)
      hνb).symm.trans hZd
  have hNp : Mori.IsProjectiveVariety k (ν ≫ ι ≫ sY) := hνp hZp
  have hνgen : ν (genericPoint N) = genericPoint Z := by
    refine ((isGenericPoint_iff_specializes).2 fun z =>
      ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩).eq (genericPoint_spec Z)
    obtain ⟨y, rfl⟩ := hνs.surj z
    exact ((genericPoint_spec N).specializes (Set.mem_univ y)).map ν.continuous
  have hιgen : ι (genericPoint Z) = η := by
    have h1 : ι (genericPoint Z) ∈ closure ({η} : Set Y) := hrange ▸ Set.mem_range_self _
    obtain ⟨z, hz⟩ : η ∈ Set.range ι := hrange ▸ subset_closure rfl
    have h2 : ι (genericPoint Z) ⤳ η :=
      (congrArg (fun y => ι (genericPoint Z) ⤳ y) hz).mp
        (((genericPoint_spec Z).specializes (Set.mem_univ z)).map ι.continuous)
    exact (h2.antisymm (specializes_iff_mem_closure.2 h1)).eq
  have hfib : ∀ a : N, ν a = genericPoint Z → a = genericPoint N := by
    intro a ha
    have hgU : genericPoint Z ∈ U := by
      rw [← SetLike.mem_coe, hU]
      exact Field.instIsIntegrallyClosed Z.functionField
    have haU : a ∈ ν ⁻¹ᵁ U := by rwa [Scheme.Hom.mem_preimage, ha]
    have hgNU : genericPoint N ∈ ν ⁻¹ᵁ U := by rwa [Scheme.Hom.mem_preimage, hνgen]
    have hinj : Function.Injective (ν ∣_ U) := (Scheme.Hom.homeomorph (ν ∣_ U)).injective
    have := @hinj (⟨a, haU⟩ : (ν ⁻¹ᵁ U).toScheme) (⟨genericPoint N, hgNU⟩ : (ν ⁻¹ᵁ U).toScheme)
      (Subtype.ext <| (morphismRestrict_base_coe ν U _).trans
        ((ha.trans hνgen.symm).trans (morphismRestrict_base_coe ν U
          (⟨genericPoint N, hgNU⟩ : (ν ⁻¹ᵁ U).toScheme)).symm))
    exact congrArg Subtype.val this
  set f : N ⟶ Y := ν ≫ ι
  have hfrange : Set.range f = closure {η} := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨ν a, (Scheme.Hom.comp_apply ν ι a).symm⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := hνs.surj z
      exact ⟨a, Scheme.Hom.comp_apply ν ι a⟩
  set T : Set N := f ⁻¹' ({x₁, x₂} ∪ closure {c})
  have hTc : IsClosed T :=
    ((hc₁.union hc₂).union isClosed_closure).preimage f.continuous
  have hfgen : f (genericPoint N) = η := by
    rw [Scheme.Hom.comp_apply, hνgen, hιgen]
  have hηne : ∀ x : Y, IsClosed {x} → η ≠ x := by
    rintro x hx rfl
    have := (Order.height_eq_zero.2 fun y hy => ?_ : Order.height η = 0)
    · rw [hη2] at this
      exact absurd this (by decide)
    · have : y ∈ closure ({η} : Set Y) := specializes_iff_mem_closure.1 hy
      rw [hx.closure_eq, Set.mem_singleton_iff] at this
      exact this ▸ le_rfl
  have hηT : genericPoint N ∉ T := by
    intro h
    simp only [T, Set.mem_preimage] at h
    rw [hfgen] at h
    rcases h with (h | h) | h
    · exact hηne _ hc₁ h
    · exact hηne _ hc₂ h
    · have hle : η ≤ c := (specializes_iff_mem_closure.2 h : c ⤳ η)
      exact (lt_irrefl _ (hcη.trans_le hle))
  obtain ⟨A, hAc, hAconn, hTA, hηA⟩ :=
    exists_isConnected_of_isNormal (ν ≫ ι ≫ sY) hNp (by rw [hNd]) hTc hηT
  set W : Set Y := f '' A
  have hWc : IsClosed W := f.isClosedMap _ hAc
  have hWconn : _root_.IsConnected W := hAconn.image _ f.continuous.continuousOn
  have hWη : W ⊆ closure {η} := (Set.image_subset_range _ _).trans hfrange.subset
  have hηW : η ∉ W := by
    rintro ⟨a, ha, hfa⟩
    have : ν a = genericPoint Z := by
      apply ι.isClosedEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hfa, hιgen]
    exact hηA (hfib a this ▸ ha)
  have hmemW : ∀ y ∈ ({x₁, x₂} ∪ closure {c} : Set Y), y ∈ W := by
    intro y hy
    have hyr : y ∈ Set.range f := by
      rw [hfrange]
      rcases hy with (h | h) | h
      · exact h ▸ hx₁
      · exact (Set.mem_singleton_iff.1 h) ▸ hx₂
      · exact closure_minimal (Set.singleton_subset_iff.2 hcη') isClosed_closure h
    obtain ⟨a, rfl⟩ := hyr
    exact ⟨a, hTA hy, rfl⟩
  obtain ⟨S, hS⟩ := exists_curveUnion_eq sY hη2 hWc hWconn hWη hηW
    (hmemW c (Or.inr (subset_closure rfl))) hc1
  refine ⟨S, hS ▸ hWconn, hS ▸ hWη, hS ▸ hmemW _ (Or.inl (Or.inl rfl)),
    hS ▸ hmemW _ (Or.inl (Or.inr rfl))⟩

private theorem degreeOn_isPullback_eq {k : Type} [Field k]
    {V W : Scheme.{0}} {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [QuasiCompact sV]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [IsSeparated sW] [LocallyOfFiniteType sW]
    {u : V ⟶ W} (hu : u ≫ sW = sV) {B : Divisor W} (hBc : B.IsCartier)
    {hB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ B.supp}
    {B' : Divisor V} (h : B.IsPullback u hB B') (C : ProperCurve sV) :
    haveI := hBc.isInvertibleModule_divisorialSheaf
    ((B'.degreeOn k sV C.ι C.dim_le (h.isCartier hBc) : ℤ) : ℝ) =
      OneCycle.degree ℝ sW B.divisorialSheaf (cyclePushforwardOfPoint ℝ sW u C.point) := by
  haveI := hBc.isInvertibleModule_divisorialSheaf
  haveI := QuasiCompact.compactSpace_of_compactSpace sV
  haveI := (h.isCartier hBc).isInvertibleModule_divisorialSheaf
  rw [ProperCurve.degree_pushforward_eq_degree_pullback u hu C]
  congr 1
  exact degreeOn_eq_of_iso k sV C.ι C.dim_le (h.divisorialSheafIso (hBc := hBc))

/-- `(L · C) = 0` iff `deg_C 𝒪(B) = 0` for a Cartier multiple `B = r L`. -/
private theorem intersectionNumber_eq_zero_iff {k : Type} [Field k] {V : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} [QuasiCompact sV] [IsLocallyNoetherian V] [IsNormal V]
    (C : ProperCurve sV) {L : QDivisor V} (hL : L.IsQCartier) {r : ℕ} (hr : 0 < r)
    {B : Divisor V} (hB : B.IsCartier) (h : Divisor.toQDivisor B = (r : ℤ) • L) :
    L.intersectionNumber k sV C.ι C.dim_le hL = 0 ↔ B.degreeOn k sV C.ι C.dim_le hB = 0 := by
  rw [QDivisor.intersectionNumber_eq_of_smul k sV C.ι C.dim_le L hL hr B hB h]
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [div_eq_zero_iff]
  simp [this]

/-- Push-forwards of two points with the same image. -/
private theorem degree_cyclePushforwardOfPoint_eq_zero {k : Type} [Field k] {X Y T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) (L : T.Modules)
    [SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]
    (φ : X ⟶ T) (ψ : Y ⟶ T) {x : X} {y : Y} (hxy : φ x = ψ y)
    (hx : residueFieldDegree φ x ≠ 0)
    (h : OneCycle.degree ℝ sT L (cyclePushforwardOfPoint ℝ sT φ x) = 0) :
    OneCycle.degree ℝ sT L (cyclePushforwardOfPoint ℝ sT ψ y) = 0 := by
  unfold cyclePushforwardOfPoint at h ⊢
  by_cases hC : IsProperCurve sT (ψ y)
  · have hC' : IsProperCurve sT (φ x) := hxy ▸ hC
    rw [dif_pos hC'] at h
    rw [dif_pos hC]
    have he : (⟨φ x, hC'⟩ : ProperCurve sT) = ⟨ψ y, hC⟩ := ProperCurve.ext hxy
    rw [he] at h
    simp only [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul] at h ⊢
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd (by exact_mod_cast h') hx
    · rw [h', mul_zero]
  · rw [dif_neg hC, map_zero]

/-- The generic point of a proper curve is not a closed point. -/
private theorem not_isClosed_singleton_of_isProperCurve {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)} {t : T} (h : IsProperCurve sT t) : ¬ IsClosed ({t} : Set T) := by
  intro ht
  have hr : ∀ a, curveSubschemeAtι t a = t := fun a => by
    have : curveSubschemeAtι t a ∈ closure ({t} : Set T) :=
      range_curveSubschemeAtι t ▸ ⟨a, rfl⟩
    rwa [ht.closure_eq] at this
  have : Subsingleton (curveSubschemeAt t) :=
    ⟨fun a b => (curveSubschemeAtι t).isEmbedding.injective ((hr a).trans (hr b).symm)⟩
  have h0 : topologicalKrullDim (curveSubschemeAt t) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  rw [h.dim_eq] at h0
  norm_num at h0

/-- A closed map sends the closure of a point onto the closure of its image. -/
private theorem image_closure_singleton {S X : Scheme.{0}} (μ : S ⟶ X) [UniversallyClosed μ]
    (x : S) : μ '' closure {x} = closure {μ x} := by
  rw [← Set.image_singleton, μ.isClosedMap.closure_image_eq_of_continuous μ.continuous]

/-- **A curve of a prime divisor over a curve of the target.** Let `φ : X ⟶ T` be proper, `X`
proper over `k` of dimension three, `E` a prime divisor of `X` and `t` the generic point of a
proper curve of `T` lying in `φ(E)` but different from the image of the generic point of `E`.
Then some proper curve `Γ ⊆ E` not contracted by `φ` has generic point over `t`. -/
private theorem exists_properCurve_map_eq {k : Type} [Field k] {X T : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sT : T ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    [IsProper sX] (φ : X ⟶ T) [IsProper φ] (hdim : topologicalKrullDim X = 3)
    (E : Mori.PrimeDivisor X) {t : T} (hC : IsProperCurve sT t)
    (ht : t ∈ closure {φ E.genericPoint}) (htE : t ≠ φ E.genericPoint) :
    ∃ Γ : ProperCurve sX, closure {Γ.point} ⊆ (E.support : Set X) ∧ φ Γ.point = t ∧
      ¬ Γ.IsContractedBy φ := by
  rw [← image_closure_singleton φ] at ht
  obtain ⟨x, hxE, rfl⟩ := ht
  have hxle : x ≤ E.genericPoint := (specializes_iff_mem_closure.2 hxE : E.genericPoint ⤳ x)
  have hxlt : x < E.genericPoint :=
    lt_of_le_of_ne_of_specializes hxle (fun h => htE (by rw [h]))
  have hE2 := height_genericPoint_eq_two sX hdim E
  have hle1 : Order.height x ≤ 1 := height_le_one_of_lt hE2 hxlt
  have hxc : ¬ IsClosed ({x} : Set X) := by
    intro hx
    apply not_isClosed_singleton_of_isProperCurve hC
    have h := image_closure_singleton φ x
    rw [hx.closure_eq, Set.image_singleton] at h
    rw [h]
    exact isClosed_closure
  have hne0 : Order.height x ≠ 0 := fun h => hxc (isClosed_singleton_of_height_eq_zero h)
  have h1 : Order.height x = 1 :=
    (ENat.le_one_iff_eq_zero_or_eq_one.1 hle1).resolve_left hne0
  have hΓ : IsProperCurve sX x :=
    isProperCurve_of_isProper sX ((topologicalKrullDim_curveSubschemeAt x).trans (by rw [h1]; rfl))
  refine ⟨⟨x, hΓ⟩, ?_, rfl, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.2 hxE) isClosed_closure
  · intro hcon
    apply not_isClosed_singleton_of_isProperCurve hC
    have h := image_closure_singleton φ x
    have hsub : φ '' closure {x} = {φ x} := by
      apply subset_antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact hcon z hz
      · exact Set.singleton_subset_iff.2 ⟨x, subset_closure rfl, rfl⟩
    rw [← hsub, h]
    exact isClosed_closure

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_terminal_from {k : Type} [Field k] {T : Scheme.{0}}
    (sT : T ⟶ Spec (.of k)) [IsSeparated sT] : IsSeparated (T ↘ ⊤_ Scheme) := by
  rw [show (T ↘ ⊤_ Scheme) = sT ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- The birational transform of a prime divisor through `T` is a prime divisor or zero. -/
private theorem transform_single_eq {X Y T : Scheme.{0}} [IsIntegral X] [IsIntegral T]
    [IsIntegral Y] (φ : X ⟶ T) (ψ : Y ⟶ T) (E : Mori.PrimeDivisor X) :
    inverseTransformDivisor ψ
        (RationalMap.transformDivisor φ.toRationalMap (Finsupp.single E 1 : Divisor X)) = 0 ∨
      ∃ P : Mori.PrimeDivisor Y, inverseTransformDivisor ψ
        (RationalMap.transformDivisor φ.toRationalMap (Finsupp.single E 1 : Divisor X)) =
          Finsupp.single P 1 := by
  simp only [inverseTransformDivisor, RationalMap.transformDivisor,
    DivisorWithCoeffs.mapPrimeDivisors_single]
  rcases (RationalMap.transformPrimeDivisor φ.toRationalMap E) with _ | E'
  · simp
  · simp only [Option.elim_some, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases inverseTransformPrimeDivisor ψ E' with _ | E''
    · simp
    · exact Or.inr ⟨E'', rfl⟩

/-- The support of a prime divisor, as a divisor, is the prime divisor itself. -/
private theorem supp_single_one {X : Scheme.{0}} (P : Mori.PrimeDivisor X) :
    ((DivisorWithCoeffs.supp (Finsupp.single P 1 : Divisor X)) : Set X) = P.support := by
  apply subset_antisymm
  · rw [AlgebraicGeometry.PrimeDivisor.support]
    exact DivisorWithCoeffs.supp_single_le P 1
  · exact DivisorWithCoeffs.support_subset_supp (by simp [DivisorWithCoeffs.coeff])

/-- On a curve `C` inside the strict transform `P` of a trivially connected prime divisor `E`,
any `L` with `ψ^* M = r L` for the common Cartier adjoint `M` on `T` is numerically trivial. -/
private theorem intersectionNumber_eq_zero_of_subset_support {X Y T : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    [QuasiCompact sX] [QuasiCompact sY]
    (hX : Mori.IsProjectiveVariety ℂ sX) (hY : Mori.IsProjectiveVariety ℂ sY)
    (hT : Mori.IsProjectiveVariety ℂ sT)
    {φ : X ⟶ T} {ψ : Y ⟶ T} (hφT : φ ≫ sT = sX) (hψT : ψ ≫ sT = sY) [IsProper φ] [IsProper ψ]
    (hψ : IsBirationalMorphism ψ)
    (hdimX : topologicalKrullDim X = 3) (hdimY : topologicalKrullDim Y = 3)
    {K : Divisor X} {Δ : QDivisor X} (hnef : (Divisor.toQDivisor K + Δ).IsNef ℂ sX)
    {E : Mori.PrimeDivisor X} (hE : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single E 1))
    {E' : Mori.PrimeDivisor T} {P : Mori.PrimeDivisor Y}
    (hE' : RationalMap.transformPrimeDivisor φ.toRationalMap E = some E')
    (hP : inverseTransformPrimeDivisor ψ E' = some P)
    {r : ℕ} (hr : 0 < r) {M : Divisor T} (hMc : M.IsCartier)
    {MX : Divisor X} {hBX : ∀ Z : irreducibleComponents X, φ (componentGenericPoint X Z) ∉ M.supp}
    (hMX : Divisor.toQDivisor MX = (r : ℤ) • (Divisor.toQDivisor K + Δ))
    (hpbX : M.IsPullback φ hBX MX)
    {MY : Divisor Y} {hBY : ∀ Z : irreducibleComponents Y, ψ (componentGenericPoint Y Z) ∉ M.supp}
    {L : QDivisor Y} (hLY : L.IsQCartier) (hMY : Divisor.toQDivisor MY = (r : ℤ) • L)
    (hpbY : M.IsPullback ψ hBY MY) (C : ProperCurve sY)
    (hCsub : closure {C.point} ⊆ (P.support : Set Y)) :
    L.intersectionNumber ℂ sY C.ι C.dim_le hLY = 0 := by
  haveI := hT
  haveI := hX
  haveI : IsProper sT := inferInstance
  haveI : IsProper sX := inferInstance
  haveI : IsSeparated (T ↘ ⊤_ Scheme) := isSeparated_terminal_from sT
  have hdimT : topologicalKrullDim T = 3 := by
    haveI : MMP.Mori.IsVariety ℂ sT := hT.toIsVariety
    haveI : MMP.Mori.IsVariety ℂ sY := hY.toIsVariety
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sT sY hψ]
    exact hdimY
  have hφE : φ E.genericPoint = E'.genericPoint :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff φ E E').1 hE'
  have hψP : ψ P.genericPoint = E'.genericPoint :=
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1
  have htE : ψ C.point ∈ closure {φ E.genericPoint} := by
    rw [hφE, ← hψP]
    have hsp : P.genericPoint ⤳ C.point := specializes_iff_mem_closure.2 (by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hCsub (subset_closure rfl))
    exact specializes_iff_mem_closure.1 (hsp.map ψ.continuous)
  have hMYc : MY.IsCartier := hpbY.isCartier hMc
  haveI := hMc.isInvertibleModule_divisorialSheaf
  refine (intersectionNumber_eq_zero_iff C hLY hr hMYc hMY).2 ?_
  have key := degreeOn_isPullback_eq hψT hMc hpbY C
  suffices h : OneCycle.degree ℝ sT M.divisorialSheaf
      (cyclePushforwardOfPoint ℝ sT ψ C.point) = 0 by
    rw [h] at key
    exact_mod_cast key
  by_cases hCt : IsProperCurve sT (ψ C.point)
  · have hne : ψ C.point ≠ φ E.genericPoint := by
      intro h
      have h1 : Order.height (ψ C.point) = 1 := by
        have := (topologicalKrullDim_curveSubschemeAt (ψ C.point)).symm.trans hCt.dim_eq
        exact_mod_cast this
      rw [h, hφE, height_genericPoint_eq_two sT hdimT E'] at h1
      norm_num at h1
    obtain ⟨Γ, hΓE, hΓt, hΓc⟩ := exists_properCurve_map_eq (sX := sX) φ hdimX E hCt htE hne
    have hres :=
      (MMP.ProgramBaseChange.residueFieldDegree_pos_of_not_isContractedBy φ hφT Γ hΓc).ne'
    haveI : Uncountable ℂ := ⟨fun h => not_countable_complex (Set.countable_univ_iff.2 h)⟩
    have hΓ0 := intersectionNumber_eq_zero_of_isTriviallyConnected sX hdimX K Δ hnef E hE Γ
      (by rwa [supp_single_one])
    have hMXc : MX.IsCartier := hpbX.isCartier hMc
    rw [intersectionNumber_eq_zero_iff Γ hnef.fst hr hMXc hMX] at hΓ0
    have keyX := degreeOn_isPullback_eq hφT hMc hpbX Γ
    rw [hΓ0, Int.cast_zero] at keyX
    exact degree_cyclePushforwardOfPoint_eq_zero sT _ φ ψ hΓt hres keyX.symm
  · simp only [cyclePushforwardOfPoint, dif_neg hCt, map_zero]

end MMP.FourfoldProofs.FourfoldFa15ProjectiveFlopTrivialConnectedPreservedProof

end

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori

open MMP.FourfoldProofs.FourfoldFa15ProjectiveFlopTrivialConnectedPreservedProof in
/-- **Trivially connected divisors survive projective numerically trivial small modifications**
(FA 15.9). Let `φ : X ⟶ T` and `ψ : Y ⟶ T` be proper birational morphisms of normal
projective complex varieties, isomorphisms in codimension one (`MMP.Flips.IsIsoInCodimOne`). Let
`(X, Δ)` be a klt threefold (`MMP.Flips.IsKawamataLogTerminal` with canonical divisor `K` of
dimension `3`), with `K + Δ` nef and numerically `φ`-trivial. Put `K_Y = ψ⁻¹_* φ_* K` and
`Δ_Y = ψ⁻¹_* φ_* Δ`. If a prime divisor `E` on `X` is `(K + Δ)`-trivially connected
(`MMP.Flips.IsTriviallyConnected`), then its strict transform `E⁺ = ψ⁻¹_* φ_* E` is
`(K_Y + Δ_Y)`-trivially connected. -/
@[mmp "lem_fourfold_fa15_projective_flop_trivial_connected_preserved"]
public theorem IsTriviallyConnected.transform_of_isIsoInCodimOne {X Y T : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [LocallyOfFiniteType sT]
    [QuasiCompact sX] [QuasiCompact sY]
    (hX : Mori.IsProjectiveVariety ℂ sX) (hY : Mori.IsProjectiveVariety ℂ sY)
    (hT : Mori.IsProjectiveVariety ℂ sT)
    {φ : X ⟶ T} {ψ : Y ⟶ T} (hφT : φ ≫ sT = sX) (hψT : ψ ≫ sT = sY)
    [IsProper φ] [IsProper ψ] (hφ : IsBirationalMorphism φ) (hψ : IsBirationalMorphism ψ)
    (hφs : IsIsoInCodimOne φ) (hψs : IsIsoInCodimOne ψ)
    {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor Δ))
    (htriv : IsNumericallyTrivialOver ℂ sX φ (QDivisor.toRDivisor (Divisor.toQDivisor K + Δ)))
    (hnef : (Divisor.toQDivisor K + Δ).IsNef ℂ sX)
    {E : Mori.PrimeDivisor X}
    (hE : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single E 1)) :
    let KY : Divisor Y :=
      inverseTransformDivisor ψ (RationalMap.transformDivisor φ.toRationalMap K)
    let ΔY : QDivisor Y := inverseTransformDivisor ψ (flopBaseDivisor φ Δ)
    let Eplus : Divisor Y := inverseTransformDivisor ψ
      (RationalMap.transformDivisor φ.toRationalMap (Finsupp.single E 1 : Divisor X))
    IsTriviallyConnected ℂ sY 3 KY ΔY Eplus := by
  intro KY ΔY Eplus
  obtain ⟨hKT, ⟨r, hr, M, hM, hMc, ⟨MX, hBX, hMX, hpbX⟩, ⟨MY, hBY, hMY, hpbY⟩⟩, hkltY, -, -, -⟩ :=
    IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne hX hY hT hφT hψT hφ hψ hφs hψs
      hklt htriv
  haveI := hY
  have hLY : (Divisor.toQDivisor KY + ΔY).IsQCartier :=
    ⟨r, by exact_mod_cast hr.ne', MY, hMY, Divisor.IsPullback.isCartier hpbY hMc⟩
  refine ⟨hkltY.1.isNormalVariety, inferInstance, hkltY.2.1, hLY, ?_, ?_⟩
  · intro P
    rcases transform_single_eq φ ψ E with h | ⟨P', h⟩ <;> simp only [Eplus, h]
    · exact le_rfl
    · exact Finsupp.single_nonneg.mpr zero_le_one P
  · have hnull : ∀ C : ProperCurve sY, closure {C.point} ⊆ (Eplus.supp : Set Y) →
        (Divisor.toQDivisor KY + ΔY).intersectionNumber ℂ sY C.ι C.dim_le hLY = 0 := by
      intro C hCsub
      have hCmem : C.point ∈ (Eplus.supp : Set Y) := hCsub (subset_closure rfl)
      rcases hE' : RationalMap.transformPrimeDivisor φ.toRationalMap E with _ | E'
      · exfalso
        simp only [Eplus, inverseTransformDivisor, RationalMap.transformDivisor,
          DivisorWithCoeffs.mapPrimeDivisors_single, hE', Option.elim_none, map_zero,
          DivisorWithCoeffs.supp_zero] at hCmem
        exact hCmem
      rcases hP : inverseTransformPrimeDivisor ψ E' with _ | P
      · exfalso
        simp only [Eplus, inverseTransformDivisor, RationalMap.transformDivisor,
          DivisorWithCoeffs.mapPrimeDivisors_single, hE', hP, Option.elim_none,
          Option.elim_some, map_zero, DivisorWithCoeffs.supp_zero] at hCmem
        exact hCmem
      have hEP : Eplus = Finsupp.single P 1 := by
        simp only [Eplus, inverseTransformDivisor, RationalMap.transformDivisor,
          DivisorWithCoeffs.mapPrimeDivisors_single, hE', hP, Option.elim_some]
      rw [hEP, supp_single_one] at hCsub
      exact intersectionNumber_eq_zero_of_subset_support hX hY hT hφT hψT hψ hklt.2.1.1
        hkltY.2.1.1 hnef hE hE' hP hr hMc hMX hpbX hLY hMY hpbY C hCsub
    intro x₁ hx₁ x₂ hx₂ hc₁ hc₂
    rcases transform_single_eq φ ψ E with h0 | ⟨P, hP⟩
    · exfalso
      change x₁ ∈ (DivisorWithCoeffs.supp Eplus : Set Y) at hx₁
      simp only [Eplus, h0, DivisorWithCoeffs.supp_zero] at hx₁
      exact hx₁
    · have hsupp : ((DivisorWithCoeffs.supp Eplus) : Set Y) = P.support := by
        simpa only [Eplus, hP] using supp_single_one P
      rw [hsupp] at hx₁ hx₂
      obtain ⟨S, hconn, hsub, h₁, h₂⟩ := exists_isConnected_curveUnion hY hkltY.2.1.1 P hx₁ hx₂
        hc₁ hc₂
      refine ⟨S, hconn, hsupp ▸ hsub, h₁, h₂, fun C hC => hnull C ?_⟩
      exact (Set.subset_biUnion_of_mem (u := fun C : ProperCurve sY => closure {C.point})
        hC).trans (hsupp ▸ hsub)

end MMP.Flips

end
