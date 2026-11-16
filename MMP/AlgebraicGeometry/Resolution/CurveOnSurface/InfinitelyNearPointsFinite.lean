module

public import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.MultiplicityOneBlowup
import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions

/-!
# Finiteness of the tree of infinitely near singular points

Let `S` be a two-dimensional regular Noetherian scheme, `C ⊆ S` a reduced curve and `p ∈ C` a
closed point. The infinitely near singular points of `C` over `p` form a rooted tree: the root is
`(S, C, p)` and the children of a vertex `t` are the elements of
`MMP.Resolution.firstInfinitelyNearSingularities t`, the singular points of the birational
transform on the exceptional curve of the blow-up of `t`. Each vertex has finitely many
children and multiplicities do not increase along an edge, so by König's lemma an infinite tree
would contain an infinite path of eventually constant multiplicity `μ ≥ 2`, that is, an infinite
blow-up sequence of multiplicity `μ`. Hence, if no such sequence starts at any vertex, the tree
is finite.

## Main results

* `MMP.Resolution.finite_isChain_firstInfinitelyNearSingularities_of_length_ne_top`: if no
  infinite blow-up sequence of multiplicity `μ ≥ 2` starts at any infinitely near singular point
  of `C` over `p` (including `p`), then there are only finitely many of them.

## Implementation notes

If `𝒪_{S,p}` has dimension at most one, the root has no children at all: `p` is then an
isolated point of `C`, so the birational transform of `C` misses the exceptional curve.

A vertex of the tree is recorded by its chain of ancestors: a list `[t₀, t₁, …, t_k]` of
`MMP.Resolution.PointedSubscheme`s with `t₀ = (S, C, p)` and
`t_{j+1} ∈ MMP.Resolution.firstInfinitelyNearSingularities t_j`. Counting chains rather than
their end triples makes distinct blow-up paths distinct vertices; the finiteness of the chains
implies that of the set `⋃ n, MMP.Resolution.infinitelyNearSingularities (S, C, p) n` of end
triples. The reduced curve is a reduced effective Cartier divisor `C : S.IdealSheafData`. A
blow-up sequence of multiplicity `μ` starting at a vertex `t` is a
`MMP.Resolution.PointBlowupSequence t.S` satisfying
`MMP.Resolution.PointBlowupSequence.IsConstantMultiplicity t.C μ` whose first centre is `t.q`
through `zeroIso`; it is infinite when its length is `⊤`.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], proof of Theorem 1.67
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing MMP.Resolution.Kr1c

namespace MMP.Resolution

-- The structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions match every goal and send instance search through `Submodule ?R ?R`.
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-! ### Preliminaries -/

/-- The multiplicity of a nonzero element of a Noetherian local ring is finite (Krull's
intersection theorem). -/
private theorem mult_ne_top_of_ne_zero {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {f : R} (hf : f ≠ 0) : mult f ≠ ⊤ := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  obtain ⟨j, hj⟩ : ∃ j : ℕ, f ∉ maximalIdeal R ^ j := by
    by_contra h
    push Not at h
    apply hf
    have : f ∈ ⨅ i : ℕ, maximalIdeal R ^ i := Ideal.mem_iInf.mpr h
    rwa [hK] at this
  refine ne_top_of_le_ne_top (ENat.coe_ne_top j) (iSup₂_le fun i hi => ?_)
  by_contra hlt
  push Not at hlt
  exact hj (Ideal.pow_le_pow_right (by exact_mod_cast hlt.le)
    (hi (Ideal.mem_span_singleton_self f)))

/-- The multiplicity of an effective Cartier divisor at a point with regular local ring is
finite. -/
private theorem multAt_ne_top {X : Scheme.{u}} {C : X.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) {x : X}
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) : multAt C x ≠ ⊤ := by
  have : IsNoetherianRing (X.presheaf.stalk x) := hreg.toIsNoetherian
  obtain ⟨f, hfnz, hf⟩ := hasPrincipalStalks_of_isEffectiveCartierDivisor hC x
  rw [multAt, hf]
  exact mult_ne_top_of_ne_zero (nonZeroDivisors.ne_zero hfnz)

/-! ### The birational transform of an effective Cartier divisor -/

/-- The birational transform of an effective Cartier divisor in the blow-up of a closed point
with two-dimensional regular local ring is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_birationalTransform {S : Scheme.{u}} [IsNoetherian S]
    {p : S} (hp : IsClosed ({p} : Set S)) (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) {C : S.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) :
    Stacks.Divisors.IsEffectiveCartierDivisor (birationalTransform p hp C) := by
  have : IsLocallyNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    (Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _).toIsLocallyNoetherian
  exact Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun w _ => hasPrincipalStalks_birationalTransform hp hreg hdim
      (hasPrincipalStalks_of_isEffectiveCartierDivisor hC) (multAt_ne_top hC hreg) w

/-! ### Points with a local ring of dimension at most one -/

section DimensionOne

/-- In a local ring of dimension zero, a non-zero-divisor is a unit. -/
private theorem isUnit_of_mem_nonZeroDivisors_of_ringKrullDim_le_zero {R : Type*} [CommRing R]
    [IsLocalRing R] (hR : ringKrullDim R ≤ 0) {f : R} (hf : f ∈ nonZeroDivisors R) : IsUnit f := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hR
  by_contra hfu
  obtain ⟨n, hn⟩ := Ring.KrullDimLE.isNilpotent_iff_mem_nonunits.mpr hfu
  exact nonZeroDivisors.ne_zero (pow_mem hf n) hn

/-- No point of an effective Cartier divisor other than `p` specializes to a point `p` whose
local ring has dimension at most one. -/
private theorem eq_of_specializes_of_mem_support {X : Scheme.{u}} {C : X.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) {p x : X}
    (hdim : ringKrullDim (X.presheaf.stalk p) ≤ 1) (hx : x ∈ C.support) (hxp : x ⤳ p) :
    x = p := by
  by_contra hne
  have hlt : p < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxp)
    fun h' => hne (hxp.antisymm (Scheme.le_iff_specializes.mp h')).eq
  have h0 : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hdim ⊢
    have hle := Order.coheight_add_one_le hlt
    have hp1 : Order.coheight p ≤ 1 := by exact_mod_cast hdim
    have hx0 : Order.coheight x = 0 := by
      have := hle.trans hp1
      by_contra h
      have h1 : 1 ≤ Order.coheight x := ENat.one_le_iff_ne_zero.mpr h
      have h2 : (1 : ℕ∞) + 1 ≤ Order.coheight x + 1 := by gcongr
      have := h2.trans this
      norm_num at this
    rw [hx0]
    rfl
  obtain ⟨f, hfnz, hf⟩ := hasPrincipalStalks_of_isEffectiveCartierDivisor hC x
  refine (IdealSheafData.stalk_eq_top_iff_notMem_support C x).1 ?_ hx
  rw [hf, Ideal.span_singleton_eq_top]
  exact isUnit_of_mem_nonZeroDivisors_of_ringKrullDim_le_zero h0 hfnz

/-- A point `p` whose local ring has dimension at most one is isolated in an effective Cartier
divisor of a Noetherian scheme. -/
private theorem exists_isOpen_forall_mem_support_eq {X : Scheme.{u}} [IsNoetherian X]
    {C : X.IdealSheafData} (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) {p : X}
    (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) ≤ 1) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ ∀ x ∈ V, x ∈ C.support → x = p := by
  set Z : Set X := (C.support : Set X)
  set T := closure (Z \ {p})
  have hTZ : T ⊆ Z := closure_minimal Set.diff_subset C.support.isClosed
  obtain ⟨Ps, hPfin, hPcl, hPirr, hP⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_closure : IsClosed T)
  have hpiece : ∀ t ∈ Ps, p ∈ t → t = {p} := by
    intro t ht hpt
    obtain ⟨η, hη⟩ := QuasiSober.sober (hPirr t ht) (hPcl t ht)
    have hηt : η ∈ t := hη.mem
    have hηZ : η ∈ Z :=
      hTZ (show η ∈ closure (Z \ {p}) from hP ▸ Set.mem_sUnion_of_mem hηt ht)
    have hηp : η ⤳ p := hη.specializes hpt
    obtain rfl := eq_of_specializes_of_mem_support hC hdim hηZ hηp
    rw [← hη.def, hp.closure_eq]
  set Ps' := {t ∈ Ps | p ∉ t}
  have hcl : IsClosed (⋃₀ Ps') :=
    (hPfin.subset fun t ht => ht.1).isClosed_sUnion fun t ht => hPcl t ht.1
  have hsub : Z \ {p} ⊆ ⋃₀ Ps' := by
    rintro z ⟨hzZ, hzp⟩
    have hzT : z ∈ ⋃₀ Ps := hP ▸ subset_closure ⟨hzZ, hzp⟩
    obtain ⟨t, ht, hzt⟩ := hzT
    refine ⟨t, ⟨ht, fun hpt => ?_⟩, hzt⟩
    rw [hpiece t ht hpt] at hzt
    exact hzp hzt
  have hpT : p ∉ T := fun hpT => by
    obtain ⟨t, ht, hpt⟩ := closure_minimal hsub hcl hpT
    exact ht.2 hpt
  refine ⟨Tᶜ, isClosed_closure.isOpen_compl, hpT, fun x hxT hxZ => ?_⟩
  by_contra hxp
  exact hxT (subset_closure ⟨hxZ, hxp⟩)

/-- At a point whose local ring has dimension at most one, the birational transform of an
effective Cartier divisor misses the exceptional curve. -/
private theorem notMem_support_birationalTransform_of_ringKrullDim_le_one {S : Scheme.{u}}
    [IsNoetherian S] {p : S} (hp : IsClosed ({p} : Set S))
    (hdim : ringKrullDim (S.presheaf.stalk p) ≤ 1) {C : S.IdealSheafData}
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hq : q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support) :
    q ∉ (birationalTransform p hp C).support := by
  have : IsNoetherian (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  obtain ⟨V, hVo, hpV, hV⟩ := exists_isOpen_forall_mem_support_eq hC hp hdim
  set g := Limits.pullback.snd C.subschemeι
    (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
  set W := g ⁻¹ᵁ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support.compl
  have : IsNoetherian (Limits.pullback C.subschemeι
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))) :=
    isNoetherian_of_isClosedImmersion g
  have : QuasiCompact (W.ι ≫ g) := inferInstance
  intro hqC
  change q ∈ ((W.ι ≫ g).ker.support : Set _) at hqC
  rw [Scheme.Hom.support_ker] at hqC
  have hqV : q ∈ (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base ⁻¹' V := by
    rw [Set.mem_preimage, (mem_support_exceptionalIdeal_iff _ hp q).1 hq]
    exact hpV
  have hcont := (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).base.hom.continuous
  obtain ⟨_, hzV, y, rfl⟩ := mem_closure_iff.1 hqC _ (hVo.preimage hcont) hqV
  have hyE : (W.ι ≫ g).base y ∉
      (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support :=
    y.2
  have hyC : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ((W.ι ≫ g).base y) ∈
      C.support := by
    change _ ∈ (C.support : Set S)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    refine ⟨Limits.pullback.fst C.subschemeι
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
      (W.ι y), ?_⟩
    rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply]
    rfl
  exact hyE ((mem_support_exceptionalIdeal_iff _ hp _).2 (hV _ hzV hyC))

end DimensionOne

/-! ### The vertices of the tree -/

/-- The standing hypotheses at a vertex `t` of the tree: `t.S` is Noetherian, `t.q` is a closed
point with two-dimensional regular local ring, and `t.C` is an effective Cartier divisor. -/
private structure IsGoodVertex (t : PointedSubscheme.{u}) : Prop where
  noeth : IsNoetherian t.S
  closed : IsClosed ({t.q} : Set t.S)
  reg : IsRegularLocalRing (t.S.presheaf.stalk t.q)
  dim : ringKrullDim (t.S.presheaf.stalk t.q) = 2
  cart : Stacks.Divisors.IsEffectiveCartierDivisor t.C

/-- When `t.q` is closed, the children of `t` are the closed singular points of the birational
transform of `t.C` that lie on the exceptional curve. -/
private theorem mem_firstInfinitelyNearSingularities_iff {t t' : PointedSubscheme.{u}}
    (h : IsClosed ({t.q} : Set t.S)) :
    t' ∈ firstInfinitelyNearSingularities t ↔
      ∃ q : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩),
        IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩))) ∧
        q ∈ (birationalTransform t.q h t.C).support ∧
        q ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩)).support ∧
        ¬ IsRegularLocalRing
          ((blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩)).presheaf.stalk q ⧸
            IdealSheafData.stalk (birationalTransform t.q h t.C) q) ∧
        t' = ⟨_, birationalTransform t.q h t.C, q⟩ := by
  rw [firstInfinitelyNearSingularities, dif_pos h]
  rfl

/-- A closed point whose local ring has dimension at most one has no infinitely near singular
points. -/
private theorem firstInfinitelyNearSingularities_eq_empty_of_ringKrullDim_le_one {S : Scheme.{u}}
    [IsNoetherian S] {C : S.IdealSheafData} (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    {p : S} (hp : IsClosed ({p} : Set S)) (hdim : ringKrullDim (S.presheaf.stalk p) ≤ 1) :
    firstInfinitelyNearSingularities (⟨S, C, p⟩ : PointedSubscheme.{u}) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ht' => by
    obtain ⟨q, -, hqC, hqE, -, -⟩ := (mem_firstInfinitelyNearSingularities_iff hp).1 ht'
    exact notMem_support_birationalTransform_of_ringKrullDim_le_one hp hdim hC q hqE hqC

/-- A vertex has finitely many children. -/
private theorem finite_firstInfinitelyNearSingularities {t : PointedSubscheme.{u}}
    (ht : IsGoodVertex t) :
    (firstInfinitelyNearSingularities t).Finite := by
  have := ht.noeth
  have := ht.noeth.toIsLocallyNoetherian
  obtain ⟨hfin, -⟩ := sum_residueDegree_mul_multAt_birationalTransform_le_multAt ht.closed ht.reg
    ht.dim t.C (isEffectiveCartierSubscheme_of_hasPrincipalStalks
      (hasPrincipalStalks_of_isEffectiveCartierDivisor ht.cart))
  refine (hfin.toFinset.finite_toSet.image fun q =>
    (⟨_, birationalTransform t.q ht.closed t.C, q⟩ : PointedSubscheme.{u})).subset ?_
  intro t' ht'
  obtain ⟨q, -, hqC, hqE, -, rfl⟩ := (mem_firstInfinitelyNearSingularities_iff ht.closed).1 ht'
  exact ⟨q, (mem_toFinset_support_sup_iff hfin).2 ⟨hqC, hqE⟩, rfl⟩

/-- A child of a vertex satisfies the standing hypotheses, is singular of multiplicity at least
two, and has multiplicity at most that of its parent. -/
private theorem good_and_multAt_of_mem {t t' : PointedSubscheme.{u}} (ht : IsGoodVertex t)
    (h : t' ∈ firstInfinitelyNearSingularities t) :
    IsGoodVertex t' ∧ 2 ≤ multAt t'.C t'.q ∧ multAt t'.C t'.q ≤ multAt t.C t.q := by
  have := ht.noeth
  have := ht.noeth.toIsLocallyNoetherian
  obtain ⟨q, hqcl, hqC, hqE, hsing, rfl⟩ := (mem_firstInfinitelyNearSingularities_iff ht.closed).1 h
  obtain ⟨hregq, hdimq, -⟩ := isRegularLocalRing_stalk_blowUp_of_mem_support_exceptionalIdeal t.q
    ht.closed ht.reg ht.dim q hqE
  have hcart := isEffectiveCartierDivisor_birationalTransform ht.closed ht.reg ht.dim ht.cart
  refine ⟨⟨Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _, hqcl, hregq, hdimq hqcl, hcart⟩,
    ?_, ?_⟩
  · have := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp
      (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, ht.closed⟩)
    obtain ⟨g, hgnz, hg⟩ := hasPrincipalStalks_of_isEffectiveCartierDivisor hcart q
    have hiff := Kollar.isRegularLocalRing_stalk_quotient_iff_multAt_eq_one hqcl hregq
      (hdimq hqcl) _ hqC g hg (nonZeroDivisors.ne_zero hgnz)
    have h1 := one_le_multAt_of_mem_support hqC
    have hne : multAt (birationalTransform t.q ht.closed t.C) q ≠ 1 := fun h => hsing (hiff.2 h)
    exact Order.add_one_le_of_lt (lt_of_le_of_ne h1 hne.symm)
  · obtain ⟨hfin, hsum⟩ := sum_residueDegree_mul_multAt_birationalTransform_le_multAt ht.closed
      ht.reg ht.dim t.C (isEffectiveCartierSubscheme_of_hasPrincipalStalks
      (hasPrincipalStalks_of_isEffectiveCartierDivisor ht.cart))
    exact (le_sum_mul (fun i _ => one_le_toENat_rank _)
      ((mem_toFinset_support_sup_iff hfin).2 ⟨hqC, hqE⟩)).trans hsum

/-- A child of a vertex is a singular point of the transform lying over the vertex. -/
private theorem exists_eq_blowUp_of_mem {t t' : PointedSubscheme.{u}}
    (h : IsClosed ({t.q} : Set t.S)) (ht' : t' ∈ firstInfinitelyNearSingularities t) :
    ∃ hS : t'.S = blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, h⟩),
      (birationalTransform t.q h t.C).comap (eqToHom hS) = t'.C ∧
      (blowUpToBase _).base ((eqToHom hS).base t'.q) = t.q ∧
      t'.q ∈ t'.C.support ∧
      ¬ IsRegularLocalRing (t'.S.presheaf.stalk t'.q ⧸ IdealSheafData.stalk t'.C t'.q) := by
  obtain ⟨q, -, hqC, hqE, hsing, rfl⟩ := (mem_firstInfinitelyNearSingularities_iff h).1 ht'
  refine ⟨rfl, ?_, ?_, hqC, hsing⟩
  · simp only [eqToHom_refl]
    exact Scheme.IdealSheafData.comap_id _
  · simp only [eqToHom_refl, Scheme.Hom.id_base, TopCat.id_app]
    exact (mem_support_exceptionalIdeal_iff _ h q).1 hqE

/-- A child of the same multiplicity `m ≥ 2` as its parent is the only point of the transform
over the parent. -/
private theorem eq_of_multAt_eq {t t' : PointedSubscheme.{u}} (ht : IsGoodVertex t)
    (h : t' ∈ firstInfinitelyNearSingularities t) (hm2 : 2 ≤ multAt t.C t.q)
    (hm : multAt t'.C t'.q = multAt t.C t.q)
    (hS : t'.S = blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, ht.closed⟩))
    (x : t'.S) (hx : x ∈ t'.C.support) (hxt : (blowUpToBase _).base ((eqToHom hS).base x) = t.q) :
    x = t'.q := by
  have := ht.noeth
  have := ht.noeth.toIsLocallyNoetherian
  obtain ⟨q, -, hqC, hqE, -, rfl⟩ := (mem_firstInfinitelyNearSingularities_iff ht.closed).1 h
  simp only [eqToHom_refl, Scheme.Hom.id_base, TopCat.id_app] at hxt
  obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.mp (multAt_ne_top ht.cart ht.reg)
  have hm2' : 2 ≤ m := by
    rw [← hm'] at hm2
    exact_mod_cast hm2
  have key := (birationalTransform_fibre_eq_singleton_or_multAt_lt ht.closed ht.reg ht.dim t.C
    (isEffectiveCartierSubscheme_of_hasPrincipalStalks
      (hasPrincipalStalks_of_isEffectiveCartierDivisor ht.cart)) m hm'.symm hm2').1
    q hqC hqE (hm.trans hm'.symm)
  have hx' : x ∈ {q' | q' ∈ (birationalTransform t.q ht.closed t.C).support ∧
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{t.q}, ht.closed⟩)).base q' = t.q} :=
    ⟨hx, hxt⟩
  rwa [key.1] at hx'

/-! ### König's lemma -/

/-- The chains of the tree starting at `t`. -/
private def chains (t : PointedSubscheme.{u}) : Set (List PointedSubscheme.{u}) :=
  {l | l.head? = some t ∧ List.IsChain (fun t t' => t' ∈ firstInfinitelyNearSingularities t) l}

/-- If a vertex has finitely many children and infinitely many chains, one of its children has
infinitely many chains. -/
private theorem exists_infinite_chains_of_infinite {t : PointedSubscheme.{u}}
    (hfin : (firstInfinitelyNearSingularities t).Finite) (hinf : (chains t).Infinite) :
    ∃ t' ∈ firstInfinitelyNearSingularities t, (chains t').Infinite := by
  by_contra h
  push Not at h
  refine hinf ((((hfin.biUnion fun t' ht' => (h t' ht').image (List.cons t))).insert [t]).subset ?_)
  rintro l ⟨hl, hc⟩
  match l, hl, hc with
  | [a], hl, _ =>
    obtain rfl : a = t := by simpa using hl
    exact Set.mem_insert _ _
  | a :: b :: l, hl, hc =>
    obtain rfl : a = t := by simpa using hl
    rw [List.isChain_cons_cons] at hc
    exact Set.mem_insert_of_mem _ (Set.mem_biUnion hc.1 ⟨b :: l, ⟨rfl, hc.2⟩, rfl⟩)

/-- König's lemma for the tree of good vertices: infinitely many chains give an infinite path. -/
private theorem exists_seq_mem_firstInfinitelyNearSingularities {t₀ : PointedSubscheme.{u}}
    (h₀ : IsGoodVertex t₀) (hinf : (chains t₀).Infinite) :
    ∃ x : ℕ → PointedSubscheme.{u}, x 0 = t₀ ∧
      ∀ n, IsGoodVertex (x n) ∧ x (n + 1) ∈ firstInfinitelyNearSingularities (x n) := by
  have step : ∀ t : PointedSubscheme.{u}, IsGoodVertex t ∧ (chains t).Infinite →
      ∃ t' ∈ firstInfinitelyNearSingularities t, IsGoodVertex t' ∧ (chains t').Infinite := by
    rintro t ⟨hg, hi⟩
    obtain ⟨t', ht', hi'⟩ :=
      exists_infinite_chains_of_infinite (finite_firstInfinitelyNearSingularities hg) hi
    exact ⟨t', ht', (good_and_multAt_of_mem hg ht').1, hi'⟩
  choose! next hnext hPnext using step
  have hP : ∀ n, IsGoodVertex (next^[n] t₀) ∧ (chains (next^[n] t₀)).Infinite := by
    intro n
    induction n with
    | zero => exact ⟨h₀, hinf⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hPnext _ ih
  refine ⟨fun n => next^[n] t₀, rfl, fun n => ⟨(hP n).1, ?_⟩⟩
  simp only [Function.iterate_succ_apply']
  exact hnext _ (hP n)

/-- Along an infinite path of good vertices the multiplicities are eventually constant, equal to
some `μ ≥ 2`: they do not increase along an edge, and every vertex but the root is singular. -/
private theorem exists_forall_multAt_eq {x : ℕ → PointedSubscheme.{u}}
    (hx : ∀ n, IsGoodVertex (x n) ∧ x (n + 1) ∈ firstInfinitelyNearSingularities (x n)) :
    ∃ N μ : ℕ, 2 ≤ μ ∧ ∀ n, multAt (x (N + n)).C (x (N + n)).q = μ := by
  have hfin n := multAt_ne_top (hx n).1.cart (hx n).1.reg
  have hchild n := good_and_multAt_of_mem (hx n).1 (hx n).2
  set m : ℕ → ℕ := fun n => (multAt (x (n + 1)).C (x (n + 1)).q).toNat
  have hanti : Antitone m := antitone_nat_of_succ_le fun n =>
    ENat.toNat_le_toNat (hchild (n + 1)).2.2 (hfin _)
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨N + 1, m N, ?_, fun n => ?_⟩
  · simpa using ENat.toNat_le_toNat (hchild N).2.1 (hfin _)
  · rw [Nat.add_right_comm, hN (N + n) (Nat.le_add_right N n)]
    exact (ENat.coe_toNat (hfin _)).symm

/-! ### Infinite paths of constant multiplicity -/

/-- The tail of an infinite path of good vertices of constant multiplicity `μ ≥ 2` is an infinite
blow-up sequence of multiplicity `μ`. -/
private theorem exists_pointBlowupSequence (x : ℕ → PointedSubscheme.{u})
    (hx : ∀ n, x (n + 1) ∈ firstInfinitelyNearSingularities (x n)) (hgood : ∀ n, IsGoodVertex (x n))
    (μ : ℕ) (hμ : 2 ≤ μ) (hm : ∀ n, multAt (x n).C (x n).q = μ) :
    ∃ s : PointBlowupSequence (x 0).S, s.zeroIso.hom.base (s.p 0) = (x 0).q ∧
      s.IsConstantMultiplicity (x 0).C μ ∧ s.length = ⊤ := by
  have hS : ∀ n, (x (n + 1)).S =
      blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{(x n).q}, (hgood n).closed⟩) := fun n =>
    (exists_eq_blowUp_of_mem (hgood n).closed (hx n)).1
  let s : PointBlowupSequence (x 0).S :=
    { length := ⊤
      S := fun n => (x n).S
      zeroIso := Iso.refl _
      p := fun n => (x n).q
      isClosed_p := fun n _ => (hgood n).closed
      blowupIso := fun n _ => eqToIso (hS n) }
  have hlt : ∀ i : ℕ, (i : ℕ∞) < s.length := ENat.coe_lt_top
  have hC : ∀ i, s.transformedSubscheme (x 0).C i = (x i).C := by
    intro i
    induction i with
    | zero => exact Scheme.IdealSheafData.comap_id _
    | succ i ih =>
      rw [PointBlowupSequence.transformedSubscheme, dif_pos (hlt i), ih]
      exact (exists_eq_blowUp_of_mem (hgood i).closed (hx i)).2.1
  refine ⟨s, rfl, ⟨fun i _ => by rw [hC]; exact hm i, fun i hi => ⟨?_, ?_, ?_⟩⟩, rfl⟩
  · simp only [PointBlowupSequence.σ, Scheme.Hom.comp_apply, eqToIso.hom]
    exact (exists_eq_blowUp_of_mem (hgood i).closed (hx i)).2.2.1
  · rw [PointBlowupSequence.IsSingularPointOfTransform, hC]
    exact (exists_eq_blowUp_of_mem (hgood i).closed (hx i)).2.2.2
  · intro q _ hq hsing
    simp only [PointBlowupSequence.σ, Scheme.Hom.comp_apply, eqToIso.hom] at hq
    rw [PointBlowupSequence.IsSingularPointOfTransform, hC] at hsing
    have hm2 : 2 ≤ multAt (x i).C (x i).q := by rw [hm]; exact_mod_cast hμ
    exact eq_of_multAt_eq (hgood i) (hx i) hm2 (by rw [hm, hm]) (hS i) q hsing.1 hq

/-- **Finiteness of the tree of infinitely near singularities** (Kollár, proof of 1.67). Let `S`
be a two-dimensional regular Noetherian scheme, `C ⊆ S` a reduced effective Cartier divisor and
`p ∈ C` a closed point. Suppose that for every infinitely near singular point `t` of `C` over
`p` (including `(S, C, p)` itself) and every `μ ≥ 2`, every blow-up sequence of multiplicity `μ`
for `t.C` starting at `t.q` has finite length. Then the set of chains
`[(S, C, p), t₁, …, t_k]` with `t_{j+1} ∈ firstInfinitelyNearSingularities t_j` is finite (in
particular, only finitely many infinitely near singular points of `C` lie over `p`). -/
@[mmp "lem_kr1c_multiplicity_tree_koenig"]
public theorem finite_isChain_firstInfinitelyNearSingularities_of_length_ne_top
    {S : Scheme.{u}} [IsNoetherian S]
    (hreg : ∀ q : S, IsRegularLocalRing (S.presheaf.stalk q))
    (hdim : topologicalKrullDim S = 2)
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    [IsReduced C.subscheme] {p : S} (hpc : IsClosed ({p} : Set S)) (hpC : p ∈ C.support)
    (hinf : ∀ (n : ℕ), ∀ t ∈ infinitelyNearSingularities ⟨S, C, p⟩ n, ∀ μ : ℕ, 2 ≤ μ →
      ∀ s : PointBlowupSequence t.S, s.zeroIso.hom.base (s.p 0) = t.q →
        s.IsConstantMultiplicity t.C μ → s.length ≠ ⊤) :
    {l : List PointedSubscheme.{u} | l.head? = some ⟨S, C, p⟩ ∧
      List.IsChain (fun t t' => t' ∈ firstInfinitelyNearSingularities t) l}.Finite := by
  change (chains ⟨S, C, p⟩).Finite
  by_contra hinfin
  -- The root has a two-dimensional local ring: otherwise it has no children.
  have hdim2 : ringKrullDim (S.presheaf.stalk p) = 2 := by
    by_contra hne
    have h2 : ringKrullDim (S.presheaf.stalk p) ≤ 2 :=
      hdim ▸ ringKrullDim_stalk_le_topologicalKrullDim p
    have hempty := firstInfinitelyNearSingularities_eq_empty_of_ringKrullDim_le_one hC hpc
      (Order.le_of_lt_succ (h2.lt_of_ne hne))
    obtain ⟨t', ht', -⟩ := exists_infinite_chains_of_infinite
      (by rw [hempty]; exact Set.finite_empty) hinfin
    rwa [hempty] at ht'
  obtain ⟨x, hx0, hx⟩ := exists_seq_mem_firstInfinitelyNearSingularities (t₀ := ⟨S, C, p⟩)
    ⟨‹_›, hpc, hreg p, hdim2, hC⟩ hinfin
  obtain ⟨N, μ, hμ, hN⟩ := exists_forall_multAt_eq hx
  -- The vertices of the path are infinitely near singular points.
  have hmem : ∀ n, x n ∈ infinitelyNearSingularities ⟨S, C, p⟩ n := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ih => exact Set.mem_biUnion ih (hx n).2
  obtain ⟨s, hs0, hs, hlen⟩ := exists_pointBlowupSequence (fun n => x (N + n))
    (fun n => (hx (N + n)).2) (fun n => (hx _).1) μ hμ hN
  exact hinf N _ (hmem _) _ hμ s hs0 hs hlen

end MMP.Resolution

end
