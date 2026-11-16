module
public import MMP.AlgebraicGeometry.Singularities.Bertini.GeneralMemberLogResolution
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
import MMP.AlgebraicGeometry.Divisor.GeneralMemberAdjunction
import MMP.AlgebraicGeometry.Divisor.RationalFunctionsProduct

/-!
# Discrepancies on a general member of a free linear system

Let `(X, Δ = ∑ aⱼ Dⱼ)` be a pair over an algebraically closed field `k` of characteristic zero
with `dim X ≥ 2`, `|V|` a free linear system on `X` spanned by sections `sᵢ` of `𝒪_X(H)`, and
`f : X' ⟶ X` a log resolution of `(X, Δ)` with `f`-exceptional prime divisors `E₁, …, E_s` such
that `∑ⱼ f⁻¹_* Dⱼ` is smooth. For a general member `H_g` of `|V|`, a connected component `H⁰` of
`H_g` and the restriction `f⁰ : H'⁰ = f⁻¹(H⁰) ⟶ H⁰`, which is a log resolution of
`(H⁰, Δ|_{H⁰})`
(`MMP.Mori.IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent`),
every irreducible component `F` of `Eᵢ ∩ H'⁰` has the discrepancy of `Eᵢ`:
`a(F, H⁰, Δ|_{H⁰}) = a(Eᵢ, X, Δ)`. This is the adjunction step of the proof of
Kollár–Mori 5.17(1).

## Main results

* `MMP.Mori.IsLogResolution.exists_polynomial_isDiscrepancy_restrict_connectedComponent_iff`:
  the statement above.

## Implementation notes

The setting is that of
`MMP.Mori.IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent`:
"general" means `Q(c) ≠ 0` for a nonzero polynomial `Q` in the coefficients of
`σ = ∑ cᵢ sᵢ`, `H⁰` is a connected component `Z` of `Supp (σ)₀` with its reduced structure,
`H'⁰` is the base change `X' ×_X H⁰` and `f⁰` its second projection.

A discrepancy is a predicate `MMP.Mori.IsDiscrepancy` on a rational number. The equality
`a(F, H⁰, Δ|_{H⁰}) = a(Eᵢ, X, Δ)` is stated as: a rational `a` is the discrepancy of `Eᵢ` over
`(X, Δ)` if and only if it is the discrepancy of `F` over `(H⁰, Δ|_{H⁰})`, for every choice of
canonical divisors of `X` and `H⁰`. That `X'` and `H⁰` are normal varieties and `f⁰` is
birational, which the divisors over `X` and over `H⁰` require, are part of the conclusion.

The proof is the adjunction formula, made explicit with forms. Near a point `z` of `H⁰`, let `τ`
be a local generator of `𝒪_X(m(K_X + Δ))` and `t` a local equation of `H`. The rational
`m`-canonical form `θ = f^*(t^{-m} τ)` on `Y` has a pole of order `m` along the component `T` of
`f^*H` that cuts out `H'⁰`. Its Poincaré residue `ρ` along `T`, computed in local frames
`dh ∧ dx₁ ∧ ⋯ ∧ dxₙ` with `h` a local equation of `T`, is an `m`-canonical form on `H'⁰`. Since
`f⁰` is birational, `ρ = (f⁰)^*τ'` for a unique form `τ'` on `H⁰`. Then:

* At a codimension-one point of `H'⁰`, the snc condition gives a local coordinate for the unique
  other boundary component through it. It follows that `ord_F ρ = ord_E(f^*τ)` whenever `F` lies
  on the boundary component `E`.
* At codimension-one points of the normal `H⁰`, `f` is biregular, so the same computation shows
  that `τ'` generates `𝒪_{H⁰}(m(K_{H⁰} + Δ|_{H⁰}))` near `z`.

Comparing orders gives `m · a(F, H⁰, Δ|_{H⁰}) = ord_F((f⁰)^*τ') = ord_E(f^*τ) = m · a(E, X, Δ)`.

The source proof compares line bundles: the crepant boundary, adjunction on `Y`, and the
isomorphism `𝒪_X(m(K_X + Δ + H))|_{H⁰} ≅ 𝒪_{H⁰}(m(K_{H⁰} + Δ|_{H⁰}))`. Here the same comparison
is made on local generators, through the Poincaré residue of rational pluricanonical forms. The
discrepancy is then read off from orders of forms along prime divisors, using its uniqueness.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of 5.17
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry hiding PrimeDivisor

universe u

namespace MMP.Mori

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y]

/-! ### Varieties -/

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The source of a log resolution of a normal variety is a normal variety. -/
private theorem isNormalVariety_of_isLogResolution {W T : Scheme.{u}} {sT : T ⟶ Spec (.of k)}
    (hT : IsNormalVariety k sT) {D : RDivisor T} {g : W ⟶ T} (hg : IsLogResolution sT D g) :
    IsNormalVariety k (g ≫ sT) := by
  have := hT.1.toIsIntegral
  have := hT.1.toIsSeparated
  have := hT.1.toLocallyOfFiniteType
  have := hT.1.toQuasiCompact
  have := hg.isProper
  have : IsIntegral W := hg.toIsSmoothResolution.isIntegral
  exact ⟨(isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    hg.toIsSmoothResolution.isNormal⟩

/-! ### The general member is Cartier -/

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A divisor `H` admitting finitely many sections of `𝒪_X(H)` without common zero is Cartier:
off `Supp (sᵢ)₀ = Supp (div uᵢ + H)` the divisor `H` has the local equation `uᵢ⁻¹`. -/
private theorem isCartier_of_forall_exists_notMem_supp {H : Divisor X} {ι : Type*}
    (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    H.IsCartier := by
  intro x
  obtain ⟨i, hi, hx⟩ := hs x
  refine ⟨(H.zeroDivisor (s i) hi).supp.compl, hx, ?_⟩
  set u := (Divisor.isUnit_sectionToRationalFunctions hi).unit
  refine ⟨u⁻¹, fun E ⟨y, hyE, hyU⟩ => ?_⟩
  have h0 : (H.zeroDivisor (s i) hi).coeff E = 0 := by
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  rw [Divisor.zeroDivisor_eq, DivisorWithCoeffs.coeff_add, coeff_principalDivisor] at h0
  rw [PrimeDivisor.ord_inv]
  exact eq_neg_of_add_eq_zero_right h0

attribute [local instance] isInvertible_of_isInvertibleModule

/-! ### The zero scheme of a section of a divisorial sheaf -/

section ZeroScheme

/-- The support of the zero scheme of `t` is the support of the divisor of zeros `(t)₀`. -/
private theorem mem_supportSet_zeroScheme_iff {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (D : Divisor Y) (hD : D.IsCartier)
    [Stacks.Ample.IsInvertibleModule Y D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0) (y : Y) :
    y ∈ (zeroScheme Y D.divisorialSheaf t).supportSet ↔ y ∈ (D.zeroDivisor t ht).supp := by
  obtain ⟨V, hyV, a, ha, hI, hc⟩ := exists_affine_zeroScheme_ideal_eq_span D hD t ht y
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem hyV, hI, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe, Y.mem_basicOpen a y hyV]
  constructor
  · intro hna
    by_contra hy
    apply hna
    obtain ⟨c, hc'⟩ := exists_unit_stalk_of_forall_ord_eq_zero (mem_pointComponent y)
      (MMP.Threefold.Resolution.sectionUnit a ha) fun E hE => by
        have hEV : E.genericPoint ∈ (V : Y.Opens) := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
          exact (specializes_iff_mem_closure.mpr hE).mem_open (V : Y.Opens).isOpen hyV
        rw [← hc E hEV]
        by_contra hne
        exact hy (DivisorWithCoeffs.support_subset_supp hne hE)
    have hZ : componentGenericPoint Y (pointComponent y) ∈ (V : Y.Opens) :=
      ((isGenericPoint_componentGenericPoint Y _).specializes
        (mem_pointComponent y)).mem_open (V : Y.Opens).isOpen hyV
    have heq : (Y.presheaf.germ V y hyV).hom a = c := by
      apply stalkToRationalFunctions_injective (mem_pointComponent y)
      rw [hc', MMP.Threefold.Resolution.sectionUnit_apply a ha _ hZ]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [heq]
    exact c.isUnit
  · intro hy hu
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    have hηE := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE
    have hEV : E.genericPoint ∈ (V : Y.Opens) := hηE.mem_open (V : Y.Opens).isOpen hyV
    have hyB : y ∈ Y.basicOpen a := (Y.mem_basicOpen a y hyV).mpr hu
    have hEB : E.genericPoint ∈ Y.basicOpen a := hηE.mem_open (Y.basicOpen a).isOpen hyB
    exact hE ((hc E hEV).trans (MMP.Threefold.Resolution.ord_sectionUnit_eq_zero a ha E hEV
      ((Y.mem_basicOpen a _ hEV).mp hEB)))

end ZeroScheme

/-! ### Normality of a connected component -/

/-- The points of `Supp D` off a connected component `Z` of it form a closed set. -/
private theorem isClosed_supp_diff_connectedComponentIn {Y : Scheme.{u}} (D : Divisor Y)
    {Z : Closeds Y} {x₀ : Y} (hZ : connectedComponentIn (D.supp : Set Y) x₀ = (Z : Set Y)) :
    IsClosed ((D.supp : Set Y) \ Z) := by
  classical
  have heq : (D.supp : Set Y) \ Z =
      ⋃ E ∈ D.support.filter (fun E => Disjoint E.support (Z : Set Y)), E.support := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨hy, hyZ⟩
      obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
      refine ⟨E, ⟨Finsupp.mem_support_iff.mpr hE, ?_⟩, hyE⟩
      rw [Set.disjoint_left]
      intro y' hy'E hy'Z
      have hirr : _root_.IsPreconnected E.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isPreconnected_singleton.closure
      have hsub : E.support ⊆ (D.supp : Set Y) := fun z hz =>
        DivisorWithCoeffs.support_subset_supp hE hz
      have hcc : connectedComponentIn (D.supp : Set Y) y' = Z := by
        rw [← hZ]; exact (connectedComponentIn_eq (hZ ▸ hy'Z)).symm
      exact hyZ (hcc ▸ hirr.subset_connectedComponentIn hy'E hsub hyE)
    · rintro ⟨E, ⟨hE, hdisj⟩, hyE⟩
      exact ⟨DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.mp hE) hyE,
        Set.disjoint_left.mp hdisj hyE⟩
  rw [heq]
  exact (Finset.finite_toSet _).isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **A connected component of a normal member is a normal variety.** If the zero scheme of a
nonzero section `t` of `𝒪_X(D)` is normal, every connected component `Z` of `Supp (t)₀`, with its
reduced structure, is a normal variety. -/
private theorem isNormalVariety_of_isNormal_zeroScheme (hX : IsNormalVariety k sX)
    (D : Divisor X) (hD : D.IsCartier) [Stacks.Ample.IsInvertibleModule X D.divisorialSheaf]
    (t : D.divisorialSubmodule ⊤) (ht : t ≠ 0)
    [IsNormal (zeroScheme X D.divisorialSheaf t).subscheme]
    (Z : Closeds X) (x₀ : X) (hx₀ : x₀ ∈ (D.zeroDivisor t ht).supp)
    (hZ : connectedComponentIn ((D.zeroDivisor t ht).supp : Set X) x₀ = (Z : Set X)) :
    IsNormalVariety k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) := by
  classical
  set zs := zeroScheme X D.divisorialSheaf t with hzs_def
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hI_def
  have := hX.1.toIsSeparated
  have := hX.1.toLocallyOfFiniteType
  have := hX.1.toQuasiCompact
  have : IsReduced zs.subscheme := isReduced_of_isNormal _
  have hsupp : zs.support = (D.zeroDivisor t ht).supp := by
    ext y
    exact mem_supportSet_zeroScheme_iff D hD t ht y
  have hzs : zs = Scheme.IdealSheafData.vanishingIdeal (D.zeroDivisor t ht).supp :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme zs _ hsupp
  have hZD : (Z : Set X) ⊆ (D.zeroDivisor t ht).supp := hZ ▸ connectedComponentIn_subset _ _
  have hcl := isClosed_supp_diff_connectedComponentIn (D.zeroDivisor t ht) hZ
  -- the two ideals agree near `Z`
  have hstalk : ∀ x ∈ (Z : Set X), IdealSheafData.stalk zs x = IdealSheafData.stalk I x := by
    intro x hx
    rw [hzs]
    refine MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _
      (U := ⟨_, hcl.isOpen_compl⟩) (fun h => h.2 hx) ?_
    ext y
    simp only [Set.mem_inter_iff, Opens.coe_mk, Set.mem_compl_iff, Set.mem_sdiff, not_and,
      not_not]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hZD h1, h2⟩⟩
  have hrange : Set.range I.subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hrange' : Set.range zs.subschemeι = (D.zeroDivisor t ht).supp := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
  -- the stalks of `I.subscheme` are the stalks of the zero scheme
  have hiso : ∀ z : I.subscheme, ∃ z' : zs.subscheme,
      Nonempty (I.subscheme.presheaf.stalk z ≃+* zs.subscheme.presheaf.stalk z') := by
    intro z
    have hxZ : I.subschemeι z ∈ (Z : Set X) := hrange ▸ ⟨z, rfl⟩
    obtain ⟨z', hz'⟩ : I.subschemeι z ∈ Set.range zs.subschemeι := hrange' ▸ hZD hxZ
    refine ⟨z', ⟨?_⟩⟩
    have h1 := IdealSheafData.ker_stalkMap_subschemeι I z
    have h2 := IdealSheafData.ker_stalkMap_subschemeι zs z'
    have e₁ := RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective z)
    have e₂ := RingHom.quotientKerEquivOfSurjective (zs.subschemeι.stalkMap_surjective z')
    have key : ∀ (x' : X) (_ : x' = I.subschemeι z),
        Nonempty (X.presheaf.stalk (I.subschemeι z) ⧸ IdealSheafData.stalk I (I.subschemeι z) ≃+*
          X.presheaf.stalk x' ⧸ IdealSheafData.stalk zs x') := by
      rintro x' rfl
      exact ⟨Ideal.quotEquivOfEq (hstalk _ hxZ).symm⟩
    exact e₁.symm.trans ((Ideal.quotEquivOfEq h1).trans ((key _ hz').some.trans
      ((Ideal.quotEquivOfEq h2.symm).trans e₂)))
  have : IsNormal I.subscheme := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · obtain ⟨z', ⟨e⟩⟩ := hiso z
      exact e.injective.isDomain
    · obtain ⟨z', ⟨e⟩⟩ := hiso z
      exact IsIntegrallyClosed.of_equiv e.symm
  -- irreducibility
  have : IsLocallyNoetherian I.subscheme := isLocallyNoetherian_of_isClosedImmersion I.subschemeι
  have : CompactSpace I.subscheme := I.subschemeι.isClosedEmbedding.compactSpace
  have hne : Nonempty I.subscheme := by
    obtain ⟨z, -⟩ : x₀ ∈ Set.range I.subschemeι := by
      rw [hrange, ← hZ]; exact mem_connectedComponentIn hx₀
    exact ⟨z⟩
  have : ConnectedSpace I.subscheme := by
    have hpc : _root_.IsPreconnected (Set.univ : Set I.subscheme) := by
      rw [← I.subschemeι.isClosedEmbedding.isInducing.isPreconnected_image, Set.image_univ,
        hrange, ← hZ]
      exact isPreconnected_connectedComponentIn
    have : PreconnectedSpace I.subscheme := ⟨hpc⟩
    exact { toNonempty := hne }
  have : IrreducibleSpace I.subscheme := by
    obtain ⟨z⟩ := hne
    have h := MMP.Mori.connectedComponent_eq_irreducibleComponent z
    have hu : connectedComponent z = Set.univ := Set.eq_univ_of_univ_subset
      (isPreconnected_univ.subset_connectedComponent (Set.mem_univ z))
    rw [hu] at h
    have : IsIrreducible (Set.univ : Set I.subscheme) := h ▸ isIrreducible_irreducibleComponent
    exact (irreducibleSpace_def _).mpr this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨(isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    inferInstance⟩

/-! ### Bertini -/

section Bertini

attribute [local instance]
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **The general member is normal.** For a general member `(σ)₀` of a free linear system on a
normal variety of dimension at least two over an algebraically closed field of characteristic
zero, every connected component of `Supp (σ)₀`, with its reduced structure, is a normal variety. -/
private theorem exists_polynomial_isNormalVariety [IsAlgClosed k] [CharZero k]
    (hdim : 2 ≤ topologicalKrullDim X) (hX : IsNormalVariety k sX)
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∀ hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0, ∀ (Z : Closeds X),
        ∀ x ∈ (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp,
          connectedComponentIn
            ((H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp : Set X) x =
            (Z : Set X) →
          IsNormalVariety k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) := by
  classical
  let : X.Over (Spec (.of k)) := ⟨sX⟩
  have : AlgebraicGeometry.IsVariety k (X ↘ Spec (.of k)) := hX.1
  have hHc := isCartier_of_forall_exists_notMem_supp s hs
  have hL := hHc.isInvertibleModule_divisorialSheaf
  obtain ⟨i₀, -, -⟩ := hs (Nonempty.some inferInstance)
  set N := Fintype.card ι - 1
  have hcard : Fintype.card ι = N + 1 := by
    have := Fintype.card_pos_iff.mpr ⟨i₀⟩
    omega
  let e : ι ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  let s' : Fin (N + 1) → Γ(H.divisorialSheaf, ⊤) := fun j => s (e.symm j)
  have hsys : ∀ c : ι → k, MMP.Threefold.Bridges.systemSection (k := k) s' (c ∘ e.symm) =
      ∑ i, scalarsToGlobalSections k sX (c i) • s i := by
    intro c
    rw [MMP.Threefold.Bridges.systemSection_apply]
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  have hs' : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen X H.divisorialSheaf
      (MMP.Threefold.Bridges.systemSection s' c) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨i, hi, hy⟩ := hs y
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single (e i) 1, ?_⟩
    have h1 : MMP.Threefold.Bridges.systemSection (k := k) s' (Pi.single (e i) 1) = s i := by
      rw [MMP.Threefold.Bridges.systemSection_apply,
        Finset.sum_eq_single (e i) (fun j _ hj => by simp [hj]) (by simp)]
      simp only [s', Equiv.symm_apply_apply, Pi.single_eq_same]
      exact one_smul k _
    rw [h1]
    exact mem_nonvanishingOpen_of_notMem_supp H hHc (s i) hi y hy
  obtain ⟨U, hU, hUc⟩ :=
    MMP.Threefold.Bridges.exists_dense_open_isNormal_zeroScheme_of_two_le_topologicalKrullDim
      hdim s' hs'
  obtain ⟨Q', hQ'0, hQ'⟩ := exists_polynomial_dualPoint_mem U hU
  refine ⟨MvPolynomial.rename e.symm Q', fun h => hQ'0
    (MvPolynomial.rename_injective _ e.symm.injective (h.trans (map_zero _).symm)),
    fun c hc hσ Z x hx hZ => ?_⟩
  rw [MvPolynomial.eval_rename] at hc
  have hc0 : c ∘ e.symm ≠ 0 := by
    intro h0
    apply hσ
    rw [← hsys, h0, map_zero]
    rfl
  have hnorm := hUc (c ∘ e.symm) hc0 (hQ' _ hc0 hc)
  rw [hsys] at hnorm
  exact isNormalVariety_of_isNormal_zeroScheme hX H hHc _ hσ Z x hx hZ

end Bertini

/-! ### Cartier divisors from local generators -/

/-- If `𝒪_W(m(K + Δ))` has a local generator around every point of a normal variety `W` over a
perfect field, then `m(K + Δ)` is a Cartier divisor. -/
private theorem isCartierDivisor_of_forall_generatesOn [PerfectField k] {W : Scheme.{u}}
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

/-! ### Frames of differentials -/

section Frames

open IsLocalRing in
/-- **A frame of differentials through `dh`.** If `Ω_{A/k}` is free of rank `e + 1` over a local
ring `A` and `dh` has a retraction `r(dh) = 1`, then `dh, dx₁, …, dxₑ` span `Ω_{A/k}` for some
`x₁, …, xₑ ∈ A`: a basis of `Ω_{A/k}` made of differentials contains one whose coefficient in `dh`
is a unit, and it can be exchanged for `dh`. -/
private theorem exists_span_cons_D_eq_top {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
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
  letI := Fintype.ofFinite κ
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
private theorem span_singleton_ιMulti_eq_top {R M : Type*} [CommRing R] [AddCommGroup M]
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
private theorem span_range_D_algebraMap_eq_top {k A B : Type*} [CommRing k] [CommRing A]
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

/-! ### Poincaré residues along a closed subscheme over a prime divisor -/

section Residue

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- Along an integral closed subscheme `T` of `Y` whose generic point is that of a prime divisor,
the local ring `𝒪_{Y,T}` is a discrete valuation ring, formally smooth over `k`, with free
differentials of rank `trdeg_k k(Y)`. -/
private theorem stalk_facts [PerfectField k] [LocallyOfFiniteType sY] {Γ : PrimeDivisor Y}
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
          (Algebra.trdeg k Y.functionField).toNat := by
  rw [hΓ]
  exact ⟨Γ.isDiscreteValuationRing_localRing, (Γ.free_kaehlerDifferential_localRing (sX := sY)).1,
    (Γ.free_kaehlerDifferential_localRing (sX := sY)).2, (Γ.formallySmooth_localRing (sX := sY)).1,
    Γ.coheight_genericPoint, Γ.finrank_kaehlerDifferential_localRing (sX := sY)⟩

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The restriction `𝒪_{Y,T} → k(T)` along a closed immersion is a surjective `k`-algebra
map. -/
private theorem stalkMap_facts [IsClosedImmersion j] :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j (genericPoint T))) T.functionField ∧
      Function.Surjective (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  refine ⟨IsScalarTower.of_algebraMap_eq' ?_, ?_⟩
  · have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
          T.presheaf.germ ⊤ (genericPoint T) (TopologicalSpace.Opens.mem_top _) =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
          Y.presheaf.germ ⊤ (j (genericPoint T)) (TopologicalSpace.Opens.mem_top _)) ≫
          j.stalkMap (genericPoint T) := by
      simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
      rfl
    exact congrArg CommRingCat.Hom.hom h
  · exact SurjectiveOnStalks.stalkMap_surjective j (genericPoint T)

/-- **Uniformizers along `T`**: a uniformizer `ϖ` of `𝒪_{Y,T}` with a retraction `r(dϖ) = 1`;
every element of order one is a unit multiple of `ϖ`. -/
private theorem exists_uniformizer [PerfectField k] [LocallyOfFiniteType sY] [IsClosedImmersion j]
    [LocallyOfFiniteType (j ≫ sY)] {Γ : PrimeDivisor Y} (hΓ : j (genericPoint T) = Γ.genericPoint) :
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
          ∃ u, IsUnit u ∧ t = u * ϖ := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨hdvr, hfree, hfin, hsm, hcoh, -⟩ := stalk_facts (sY := sY) hΓ
  obtain ⟨htow, hsurj⟩ := stalkMap_facts (sY := sY) (j := j)
  have := essFiniteType_functionField (sX := j ≫ sY)
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (j (genericPoint T)))
  have hmax : RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk (j (genericPoint T))) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  have hker : RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
      Ideal.span {ϖ} :=
    hmax.trans ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ)
  have hϖ0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField ϖ = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self ϖ)
  have hϖ2 :
      ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ^ 2 := by
    rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : ϖ * 1 = ϖ * (ϖ * c) := by rwa [mul_one, ← mul_assoc, ← pow_two]
    have h2 := mul_left_cancel₀ hϖ.ne_zero h1
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one c h2.symm)
  obtain ⟨r, hr⟩ := MMP.Fourfold.exists_retraction_D (k := k) hsurj
    (hker ▸ Ideal.mem_span_singleton_self ϖ) hϖ2
  refine ⟨ϖ, r, hϖ0, hr, hker, hϖ2, fun t ht => ?_⟩
  have ht0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField t ≠ 0 := by
    intro h
    rw [h] at ht
    have := congrFun Scheme.ord_zero (j (genericPoint T))
    simp only [Pi.zero_apply] at this
    omega
  have h1 := (Scheme.ord_eq_iff hcoh ht0).mp ht
  have h2 : Ring.ordFrac (Y.presheaf.stalk (j (genericPoint T)))
      (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ) = WithZero.exp 1 :=
    Ring.ordFrac_irreducible hϖ
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := (Y.presheaf.stalk (j (genericPoint T))))
    (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ)
    (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField t) (h2.trans h1.symm)
  refine ⟨u, u.isUnit,
    IsFractionRing.injective (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ?_⟩
  rw [← hu, map_mul, Units.smul_def, Algebra.smul_def]

/-- **Uniqueness of the Poincaré residue** along an integral closed subscheme `T ⊆ Y` whose generic
point is that of a prime divisor of the normal variety `Y`, over a perfect field. -/
private theorem isPoincareResidue_unique [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] [LocallyOfFiniteType (j ≫ sY)] {Γ : PrimeDivisor Y}
    (hΓ : j (genericPoint T) = Γ.genericPoint) {n m : ℕ}
    {τ : RationalPluriForms sY (n + 1) m} {ρ ρ' : RationalPluriForms (j ≫ sY) n m}
    (h : MMP.Fourfold.IsPoincareResidue sY j n m τ ρ)
    (h' : MMP.Fourfold.IsPoincareResidue sY j n m τ ρ') : ρ = ρ' := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := stalk_facts (sY := sY) hΓ
  obtain ⟨htow, hsurj⟩ := stalkMap_facts (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, -, -, hunif⟩ := exists_uniformizer (sY := sY) hΓ
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h'
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  exact MMP.Fourfold.logPluriResidue_eq_of_logPluriForm_eq hsurj hϖ0 hr hu₁ hu₂ x₁ x₂
    (hτ₁.symm.trans hτ₂)

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The local rings of a smooth variety over a perfect field are essentially of finite type and
formally smooth, with free differentials of rank `trdeg_k k(Y)`. -/
private theorem stalk_facts_of_isSmoothScheme [PerfectField k] [LocallyOfFiniteType sY]
    (hsm : IsSmoothScheme sY)
    (y : Y) :
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

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The specialization map `𝒪_{Y,y} → 𝒪_{Y,ξ}` is `k`-linear. -/
private theorem isScalarTower_stalkSpecializes {ξ y : Y} (h : ξ ⤳ y) :
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
private theorem isScalarTower_stalkMap (w : T) :
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

omit [IsLocallyNoetherian Y] [IsNormal Y] in
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
      rwa [hσDK]
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
  · rwa [hsp, hΓ]
  · rintro G rfl
    rw [hord G rfl, hga, Scheme.ord_mul hju.ne_zero (zpow_ne_zero _ hjπ.ne_zero),
      ord_zpow _ hjπ.ne_zero, hspT π]
    have h0 : T.ord ((j.stalkMap (genericPoint T)).hom
        ((Y.presheaf.stalkSpecializes hζ).hom u)) G.genericPoint = 0 := by
      rw [hspT u]
      exact G.ord_algebraMap_of_isUnit (hu.map _)
    rw [h0, zero_add]

end Residue

/-! ### Local equations and the base change to a component of the general member -/

section BaseChange

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

private theorem mem_primeOfSpecializes_of_mem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X]
    {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    {x : X} (hxU : x ∈ U) {W : irreducibleComponents X} (hxW : x ∈ W.1)
    {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    {x' : X} (h : x' ⤳ x) (hx' : x' ∈ D.supp) :
    a ∈ MMP.Intersection.primeOfSpecializes h := by
  obtain ⟨C, hC, hx'C⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx'
  have hηC : C.genericPoint ⤳ x' := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx'C
  have hxC : x ∈ C.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact hηC.trans h
  have hord : C.ord φ ≠ 0 := by
    rwa [← hφ C ⟨x', hx'C, h.mem_open U.isOpen hxU⟩]
  have hW : W = C.component :=
    eq_of_mem_irreducibleComponents hxW (C.support_subset_component hxC)
  subst hW
  refine MMP.Resolution.primeOfSpecializes_trans_le hηC h ?_
  change X.presheaf.stalkSpecializes (hηC.trans h) a ∈ IsLocalRing.maximalIdeal _
  by_contra hna
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hna
  apply hord
  refine C.ord_eq_zero_of_isUnit hna ?_
  rw [C.toComponent_stalkSpecializes (hηC.trans h) hxW]
  exact ha

/-- On the discrete valuation ring `𝒪_{X,D}`, the order `v_D` of the image of `c ≠ 0` is its length
order. -/
private theorem ordUnit_eq_ord {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (D : PrimeDivisor X)
    {c : D.localRing} (hc : c ≠ 0)
    {u : (X.presheaf.stalk (componentGenericPoint X D.component))ˣ}
    (hu : D.toComponent.hom c = u) : D.ordUnit u = ((Ring.ord D.localRing c).toNat : ℤ) := by
  let := D.toComponent.hom.toAlgebra
  have := isFractionRing_stalkToRationalFunctions D.genericPoint_mem_component
  have : Ring.KrullDimLE 1 D.localRing := krullDimLE_of_coheight_le D.coheight_genericPoint.le
  have := D.isDiscreteValuationRing_localRing
  have hnz : c ∈ nonZeroDivisors D.localRing := mem_nonZeroDivisors_of_ne_zero hc
  have hfin : Ring.ord D.localRing c ≠ ⊤ := Ring.ord_ne_top hnz
  have h := D.valuation_eq_exp_ordUnit u
  have h2 : D.valuation (D.toComponent.hom c) =
      WithZero.exp ((Ring.ord D.localRing c).toNat : ℤ) := by
    change Ring.ordFrac D.localRing (IsLocalization.algEquiv (nonZeroDivisors D.localRing) _
      (FractionRing D.localRing) (algebraMap D.localRing _ c)) = _
    rw [AlgEquiv.commutes, Ring.ordFrac_eq_ord _ hc,
      Ring.ordMonoidWithZeroHom_eq_coe _ hnz (ENat.coe_toNat hfin).symm]
    rfl
  rw [hu, h] at h2
  exact WithZero.exp_injective h2

/-- The coefficient of the pull-back `f^*D` at a prime divisor `E` through `y` is the order along
`E` of the pulled-back germ of a local equation of `D`. -/
private theorem coeff_eq_ord_stalkMap {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {D : Divisor X}
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {y : Y} (hyU : f y ∈ U) {W : irreducibleComponents X}
    (hW : f y ∈ W.1) {a : X.presheaf.stalk (f y)}
    (ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) W)
    {y'' : Y} (h : y'' ⤳ y) (h1 : Order.coheight y'' = 1) :
    Y.presheaf.stalkSpecializes h (f.stalkMap y a) ≠ 0 ∧
    H'.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1) =
      ((Ring.ord (Y.presheaf.stalk y'') (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat
        : ℤ) := by
  set E : PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1 with hEdef
  have hEg : AlgebraicGeometry.PrimeDivisor.genericPoint E = y'' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y'' h1
  have hηy : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳ y := by rwa [hEg]
  have hyE : y ∈ E.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact hηy
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := ⟨y, hyE, hyU⟩
  have hc := hpb U φ hφ E hE
  set Z := E.component
  set cgp := componentGenericPoint Y Z
  have hZ : f cgp ∈ U := E.map_componentGenericPoint_mem f hE
  have hcgpy : cgp ⤳ y := E.specializes_genericPoint.trans hηy
  have hx0 : f cgp ⤳ f y := f.base.hom.map_specializes hcgpy
  set W' := pointComponent (f cgp)
  have hfyW' : f y ∈ W'.1 := hx0.mem_closed (isClosed_of_mem_irreducibleComponents _ W'.2)
    (mem_pointComponent _)
  have hWW' : W' = W := eq_of_mem_irreducibleComponents hfyW' hW
  have hx0W : f cgp ∈ W.1 := hWW' ▸ mem_pointComponent _
  obtain ⟨a1, ha1⟩ := hφ.exists_unit_stalk hZ (hB Z) hx0W
  have ha0 : X.presheaf.stalkSpecializes hx0 a = (a1 : X.presheaf.stalk (f cgp)) := by
    apply stalkToRationalFunctions_injective hx0W
    rw [ha1, ← ha]
    change (X.presheaf.stalkSpecializes hx0 ≫ X.presheaf.stalkSpecializes _).hom a = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  rw [pullbackComponent_eq hB hφ hZ hx0W a1 ha1] at hc
  have hcu : E.toComponent.hom (Y.presheaf.stalkSpecializes hηy (f.stalkMap y a)) =
      ((Units.map (f.stalkMap cgp).hom.toMonoidHom a1 : (Y.presheaf.stalk cgp)ˣ) :
        Y.presheaf.stalk cgp) := by
    change (Y.presheaf.stalkSpecializes _ ≫ Y.presheaf.stalkSpecializes _).hom
      (f.stalkMap y a) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [Units.coe_map, ← ha0]
    exact (Scheme.Hom.stalkSpecializes_stalkMap_apply f cgp y hcgpy a).symm
  have hne : Y.presheaf.stalkSpecializes hηy (f.stalkMap y a) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcu
    exact (Units.ne_zero _) hcu.symm
  rw [hc, ordUnit_eq_ord E hne hcu]
  clear_value E
  subst hEg
  exact ⟨hne, rfl⟩

/-- A local equation of an effective divisor on a normal scheme is regular at each point of its
open. -/
private theorem exists_germ_eq_of_isLocalEquation {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X]
    {D : Divisor X} (hD : 0 ≤ D) {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {x : X} (hxU : x ∈ U) :
    ∃ a : X.presheaf.stalk x, (stalkToRationalFunctions X (mem_pointComponent x)).hom a =
      (φ : RationalFunctions X) (pointComponent x) :=
  exists_stalk_eq_of_forall_zero_le_ord _ φ fun E hE => by
    rw [← hφ E ⟨x, hE, hxU⟩]; exact hD E

/-- Off `Supp D`, the germ of a local equation of `D` is a unit. -/
private theorem isUnit_of_isLocalEquation_of_notMem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {x : X} (hxU : x ∈ U) {W : irreducibleComponents X}
    (hxW : x ∈ W.1) {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    (hx : x ∉ D.supp) : IsUnit a := by
  obtain ⟨a1, ha1⟩ := hφ.exists_unit_stalk hxU hx hxW
  rw [stalkToRationalFunctions_injective hxW (ha.trans ha1.symm)]
  exact a1.isUnit

/-- On `Supp D`, the germ of a local equation of `D` is not a unit. -/
private theorem not_isUnit_of_isLocalEquation_of_mem_supp {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {x : X} (hxU : x ∈ U) {W : irreducibleComponents X}
    (hxW : x ∈ W.1) {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    (hx : x ∈ D.supp) : ¬ IsUnit a := by
  have h := mem_primeOfSpecializes_of_mem_supp hφ hxU hxW ha (specializes_refl x) hx
  change X.presheaf.stalkSpecializes (specializes_refl x) a ∈ IsLocalRing.maximalIdeal _ at h
  rw [TopCat.Presheaf.stalkSpecializes_refl] at h
  exact (IsLocalRing.mem_maximalIdeal _).mp h

/-- The pull-back to an integral `Y` of the germ of a local equation is nonzero. -/
private theorem stalkMap_ne_zero_of_isLocalEquation {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] {f : Y ⟶ X} {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {y : Y} (hyU : f y ∈ U) {W : irreducibleComponents X}
    (hW : f y ∈ W.1) {a : X.presheaf.stalk (f y)}
    (ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) W) :
    f.stalkMap y a ≠ 0 := by
  set Z := pointComponent y
  set cgp := componentGenericPoint Y Z
  have hcgpy : cgp ⤳ y := (isGenericPoint_componentGenericPoint Y Z).specializes
    (mem_pointComponent y)
  have hx0 : f cgp ⤳ f y := f.base.hom.map_specializes hcgpy
  have hZ : f cgp ∈ U := hx0.mem_open U.isOpen hyU
  set W' := pointComponent (f cgp)
  have hfyW' : f y ∈ W'.1 := hx0.mem_closed (isClosed_of_mem_irreducibleComponents _ W'.2)
    (mem_pointComponent _)
  have hWW' : W' = W := eq_of_mem_irreducibleComponents hfyW' hW
  have hx0W : f cgp ∈ W.1 := hWW' ▸ mem_pointComponent _
  have hu : IsUnit (X.presheaf.stalkSpecializes hx0 a) := by
    refine isUnit_of_isLocalEquation_of_notMem_supp hφ hZ hx0W ?_ (hB Z)
    rw [← ha]
    change (X.presheaf.stalkSpecializes hx0 ≫ X.presheaf.stalkSpecializes _).hom a = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  intro h0
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply f cgp y hcgpy a
  rw [h0, map_zero] at h1
  exact (hu.map (f.stalkMap cgp).hom).ne_zero h1

/-- At a generic point of an integral scheme every nonzero germ is a unit. -/
private theorem isUnit_of_coheight_eq_zero {Y : Scheme.{u}} [IsIntegral Y]
    {y : Y} (h0 : Order.coheight y = 0) {c : Y.presheaf.stalk y} (hc : c ≠ 0) : IsUnit c := by
  have : Ring.KrullDimLE 0 (Y.presheaf.stalk y) := krullDimLE_of_coheight_le (by rw [h0]; rfl)
  letI := (Ring.KrullDimLE.isField_of_isDomain (R := Y.presheaf.stalk y)).toField
  exact isUnit_iff_ne_zero.mpr hc

/-- Set-theoretically, `Supp f^*D = f⁻¹(Supp D)` for an effective Cartier divisor `D` and a
factorial `Y`. -/
private theorem mem_supp_iff_mem_supp_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) {f : Y ⟶ X}
    {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') (y : Y) :
    f y ∈ D.supp ↔ y ∈ H'.supp := by
  obtain ⟨U, hxU, φ, hφ⟩ := hDc (f y)
  obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
  have hb0 := stalkMap_ne_zero_of_isLocalEquation hB hφ hxU _ ha
  constructor
  · intro hx
    have hna := not_isUnit_of_isLocalEquation_of_mem_supp hφ hxU _ ha hx
    have hnb : ¬ IsUnit (f.stalkMap y a) := fun hu =>
      hna ((isUnit_map_iff (f.stalkMap y).hom a).mp hu)
    by_contra hy
    apply hnb
    have := hUFD y
    have hass : Associated (f.stalkMap y a) 1 := by
      refine MMP.Intersection.associated_of_forall_ord_stalkSpecializes_eq y hb0 one_ne_zero
        fun y'' h hle => ?_
      rw [map_one, Ring.ord_one]
      have hne : Y.presheaf.stalkSpecializes h (f.stalkMap y a) ≠ 0 := fun h0 =>
        hb0 (MMP.Intersection.stalkSpecializes_injective h (h0.trans (map_zero _).symm))
      rcases ENat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
      · exact Ring.ord_of_isUnit (isUnit_of_coheight_eq_zero h0 hne)
      · obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hxU _ ha h h1
        have hyE : y ∈ (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1).support := by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
            AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
            ← specializes_iff_mem_closure]
          exact h
        have hc0 : H'.coeff (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1) = 0 := by
          by_contra hne'
          exact hy (DivisorWithCoeffs.mem_supp_iff.mpr ⟨_, hne', hyE⟩)
        rw [hc0] at hc
        have hfin : Ring.ord (Y.presheaf.stalk y'')
            (Y.presheaf.stalkSpecializes h (f.stalkMap y a)) ≠ ⊤ := by
          have : Ring.KrullDimLE 1 (Y.presheaf.stalk y'') :=
            krullDimLE_of_coheight_le (by rw [h1]; rfl)
          exact Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hne)
        have h0' : (Ring.ord (Y.presheaf.stalk y'')
            (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat = 0 := by exact_mod_cast hc.symm
        rw [← ENat.coe_toNat hfin, h0']
        rfl
    exact hass.isUnit_iff.mpr isUnit_one
  · intro hy
    obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hy
    by_contra hx
    have hau := isUnit_of_isLocalEquation_of_notMem_supp hφ hxU _ ha hx
    have hη := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE
    have h1 :=AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
    obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hxU _ ha hη h1
    have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1 = E :=
      ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mpr rfl).symm
    rw [hEq, Ring.ord_of_isUnit ((hau.map (f.stalkMap y).hom).map _)] at hc
    exact hE hc

/-- Where `f^*D` is the prime divisor `E` with multiplicity one, the pulled-back local equation
generates the ideal of `E`. -/
private theorem associated_stalkMap_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hsmY : IsSmoothScheme sY)
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) {f : Y ⟶ X}
    {D : Divisor X}
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) {y : Y} (hyU : f y ∈ U) {W : irreducibleComponents X}
    (hW : f y ∈ W.1) {a : X.presheaf.stalk (f y)}
    (ha : (stalkToRationalFunctions X hW).hom a = (φ : RationalFunctions X) W)
    {E : PrimeDivisor Y} (hyE : y ∈ E.support) (hE1 : H'.coeff E = 1)
    (hE0 : ∀ E' : PrimeDivisor Y, y ∈ E'.support → E' ≠ E → H'.coeff E' = 0)
    {π : Y.presheaf.stalk y} (hπ : IdealSheafData.stalk E.idealSheaf y = Ideal.span {π})
    (hπ0 : π ≠ 0) : Associated (f.stalkMap y a) π := by
  have hb0 := stalkMap_ne_zero_of_isLocalEquation hB hφ hyU hW ha
  have := hUFD y
  have hprime := MMP.Resolution.Aux.primeOfSpecializes_genericPoint sY hsmY E hyE
  have hηE := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hyE
  refine MMP.Intersection.associated_of_forall_ord_stalkSpecializes_eq y hb0 hπ0
    fun y'' h hle => ?_
  have hne : Y.presheaf.stalkSpecializes h (f.stalkMap y a) ≠ 0 := fun h0 =>
    hb0 (MMP.Intersection.stalkSpecializes_injective h (h0.trans (map_zero _).symm))
  have hneπ : Y.presheaf.stalkSpecializes h π ≠ 0 := fun h0 =>
    hπ0 (MMP.Intersection.stalkSpecializes_injective h (h0.trans (map_zero _).symm))
  rcases ENat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [Ring.ord_of_isUnit (isUnit_of_coheight_eq_zero h0 hne),
      Ring.ord_of_isUnit (isUnit_of_coheight_eq_zero h0 hneπ)]
  · obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hyU hW ha h h1
    have : Ring.KrullDimLE 1 (Y.presheaf.stalk y'') :=
      krullDimLE_of_coheight_le (by rw [h1]; rfl)
    have hfin : Ring.ord (Y.presheaf.stalk y'')
        (Y.presheaf.stalkSpecializes h (f.stalkMap y a)) ≠ ⊤ :=
      Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hne)
    rw [← ENat.coe_toNat hfin]
    by_cases hyη : y'' = AlgebraicGeometry.PrimeDivisor.genericPoint E
    · have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1 = E :=
        ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mpr hyη).symm
      rw [hEq, hE1] at hc
      have h1' : (Ring.ord (Y.presheaf.stalk y'')
          (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat = 1 := by exact_mod_cast hc.symm
      rw [h1']
      refine (MMP.Intersection.ord_stalkSpecializes_eq_one h ?_).symm
      rw [MMP.Resolution.primeOfSpecializes_congr hyη h hηE, hprime, hπ]
    · have hyE' : y ∈ (AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1).support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne,
          ← specializes_iff_mem_closure]
        exact h
      have hEne : AlgebraicGeometry.PrimeDivisor.ofCoheightOne y'' h1 ≠ E := fun hEq =>
        hyη ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mp hEq.symm)
      rw [hE0 _ hyE' hEne] at hc
      have h0' : (Ring.ord (Y.presheaf.stalk y'')
          (Y.presheaf.stalkSpecializes h (f.stalkMap y a))).toNat = 0 := by exact_mod_cast hc.symm
      rw [h0']
      refine (MMP.Intersection.ord_stalkSpecializes_of_notMem h fun hπy => hyη ?_).symm
      have hle' : MMP.Intersection.primeOfSpecializes hηE ≤
          MMP.Intersection.primeOfSpecializes h := by
        rwa [hprime, hπ, Ideal.span_singleton_le_iff_mem]
      have hsp : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳ y'' :=
        MMP.Intersection.specializes_of_primeOfSpecializes_le hηE h hle'
      by_contra hne'
      have hlt := Order.coheight_strictAnti (MMP.Intersection.lt_of_specializes_of_ne hsp hne')
      rw [h1, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at hlt
      exact lt_irrefl _ (hlt (by decide))

/-- The germ of a local equation of `D` vanishes on every closed set contained in `Supp D`. -/
private theorem germ_mem_stalk_vanishingIdeal {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    {x : X} (hxU : x ∈ U) {W : irreducibleComponents X} (hxW : x ∈ W.1)
    {a : X.presheaf.stalk x}
    (ha : (stalkToRationalFunctions X hxW).hom a = (φ : RationalFunctions X) W)
    {Z : Closeds X} (hZ : (Z : Set X) ⊆ D.supp) :
    a ∈ IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal Z) x := by
  rw [MMP.Resolution.stalk_vanishingIdeal_eq, PrimeSpectrum.mem_vanishingIdeal]
  intro p hp
  have h := MMP.Intersection.fromSpecStalk_specializes x p
  rw [← MMP.Intersection.comap_maximalIdeal_stalkSpecializes_fromSpecStalk x p]
  exact mem_primeOfSpecializes_of_mem_supp hφ hxU hxW ha h (hZ hp)

/-- Over a connected component `Z` of `Supp D`, the inverse image of the reduced ideal of `Z` is,
at each point, the ideal of the component of `f^*D` through it. -/
private theorem exists_stalk_comap_vanishingIdeal_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hsmY : IsSmoothScheme sY)
    (hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) {f : Y ⟶ X}
    {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H')
    (hH'1 : ∀ E ∈ H'.support, H'.coeff E = 1)
    (hdisj : ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support)
    (hgen : ∀ E ∈ H'.support, ∀ y ∈ E.support, ∃ π : Y.presheaf.stalk y, π ≠ 0 ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {π})
    {Z : Closeds X} {x₀ : X} (hZ : connectedComponentIn (D.supp : Set X) x₀ = Z)
    {y : Y} (hy : f y ∈ Z) :
    ∃ E ∈ H'.support, y ∈ E.support ∧ E.support ⊆ f ⁻¹' Z ∧
      IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal Z).comap f) y =
        IdealSheafData.stalk E.idealSheaf y := by
  classical
  have hZD : (Z : Set X) ⊆ D.supp := hZ ▸ connectedComponentIn_subset _ _
  have hK1 := mem_supp_iff_mem_supp_of_isPullback hUFD hD hDc hpb
  obtain ⟨E, hE, hyE⟩ := DivisorWithCoeffs.mem_supp_iff.mp ((hK1 y).mp (hZD hy))
  have hEs : E ∈ H'.support := Finsupp.mem_support_iff.mpr hE
  have hEZ : E.support ⊆ f ⁻¹' Z := by
    have hirr : _root_.IsPreconnected (f '' E.support) := by
      have : IsIrreducible E.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact isIrreducible_singleton.closure
      have h2 : IsIrreducible (f '' E.support) := this.image _ f.continuous.continuousOn
      exact (IsIrreducible.isConnected h2).isPreconnected
    have hsub : f '' E.support ⊆ D.supp := by
      rintro _ ⟨y', hy', rfl⟩
      exact (hK1 y').mpr (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, hy'⟩)
    have hcc : connectedComponentIn (D.supp : Set X) (f y) = Z := by
      rw [← hZ]; exact (connectedComponentIn_eq (hZ ▸ hy)).symm
    intro y' hy'
    have := hirr.subset_connectedComponentIn ⟨y, hyE, rfl⟩ hsub ⟨y', hy', rfl⟩
    rwa [hcc] at this
  refine ⟨E, hEs, hyE, hEZ, le_antisymm ?_ ?_⟩
  · -- upper bound: through the radical
    refine (MMP.Resolution.stalk_le_stalk_of_le
      (Scheme.IdealSheafData.le_radical _) y).trans (le_of_eq ?_)
    rw [← Scheme.IdealSheafData.vanishingIdeal_support,
      ← MMP.Intersection.vanishingIdeal_support_idealSheaf]
    set T : Closeds Y := ⟨⋃ E' ∈ H'.support.erase E, E'.support,
      (H'.support.erase E).finite_toSet.isClosed_biUnion fun E' _ => E'.idealSheaf.support.isClosed⟩
    have hT : ∀ y', y' ∈ (T : Set Y) ↔ ∃ E' ∈ H'.support, E' ≠ E ∧ y' ∈ E'.support := by
      intro y'
      simp only [T, Closeds.coe_mk, Set.mem_iUnion, Finset.mem_erase, exists_prop]
      exact ⟨fun ⟨E', ⟨h1, h2⟩, h3⟩ => ⟨E', h2, h1, h3⟩, fun ⟨E', h2, h1, h3⟩ => ⟨E', ⟨h1, h2⟩, h3⟩⟩
    have hyT : y ∉ (T : Set Y) := by
      rw [hT]
      rintro ⟨E', hE', hne, hyE'⟩
      exact Set.disjoint_left.mp (hdisj E hEs E' hE' hne.symm) hyE hyE'
    refine MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _
      (U := ⟨(T : Set Y)ᶜ, T.isClosed.isOpen_compl⟩) hyT ?_
    ext y'
    simp only [Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Set.mem_inter_iff, Opens.coe_mk, Set.mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      obtain ⟨E', hE', hy'E'⟩ := DivisorWithCoeffs.mem_supp_iff.mp ((hK1 y').mp (hZD h1))
      by_cases hEE : E' = E
      · subst hEE; exact hy'E'
      · exact absurd ((hT y').mpr ⟨E', Finsupp.mem_support_iff.mpr hE', hEE, hy'E'⟩) h2
    · rintro ⟨h1, h2⟩
      exact ⟨hEZ h1, h2⟩
  · -- lower bound: the pulled back local equation generates
    obtain ⟨U, hxU, φ, hφ⟩ := hDc (f y)
    obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
    obtain ⟨π, hπ0, hπ⟩ := hgen E hEs y hyE
    have hass := associated_stalkMap_of_isPullback sY hsmY hUFD hpb hφ hxU _ ha hyE
      (hH'1 E hEs) (fun E' hyE' hne => by
        by_contra hc
        exact Set.disjoint_left.mp (hdisj E hEs E' (Finsupp.mem_support_iff.mpr hc)
          (Ne.symm hne)) hyE hyE') hπ hπ0
    rw [hπ, ← Ideal.span_singleton_eq_span_singleton.mpr hass, Ideal.span_le,
      Set.singleton_subset_iff, AlgebraicGeometry.IdealSheafData.stalk_comap]
    exact Ideal.mem_map_of_mem _
      (germ_mem_stalk_vanishingIdeal hφ hxU _ ha hZD)

/-- The pull-back of an effective Cartier divisor is effective. -/
private theorem coeff_nonneg_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X}
    {D : Divisor X} (hD : 0 ≤ D) (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') (E : PrimeDivisor Y) : 0 ≤ H'.coeff E := by
  obtain ⟨U, hxU, φ, hφ⟩ := hDc (f (AlgebraicGeometry.PrimeDivisor.genericPoint E))
  obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD hφ hxU
  have h1 := AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E
  obtain ⟨-, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hxU _ ha (specializes_refl _) h1
  have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1 = E :=
    ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E h1).mpr rfl).symm
  rw [hEq] at hc
  rw [hc]
  exact Nat.cast_nonneg _

open Classical in
/-- If `H' + ∑_{F ∈ S} F` is reduced, each component of `H'` has coefficient one and is not in
`S`. -/
private theorem coeff_eq_one_and_notMem_of_mem_support {Y : Scheme.{u}} {H' : Divisor Y}
    (hH' : ∀ E, 0 ≤ H'.coeff E) (S : Finset (PrimeDivisor Y))
    (h01 : ∀ F : PrimeDivisor Y,
      (H' + ∑ F ∈ S, Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ S, Finsupp.single F (1 : ℤ)).coeff F = 1)
    {E : PrimeDivisor Y} (hE : E ∈ H'.support) : H'.coeff E = 1 ∧ E ∉ S := by
  have hcS : DivisorWithCoeffs.coeff (∑ F ∈ S, Finsupp.single F (1 : ℤ) : Divisor Y) E =
      if E ∈ S then 1 else 0 := by
    change (∑ F ∈ S, Finsupp.single F (1 : ℤ)) E = _
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  have hpos : H'.coeff E ≠ 0 := Finsupp.mem_support_iff.mp hE
  have hnn := hH' E
  have h' := h01 E
  rw [DivisorWithCoeffs.coeff_add, hcS] at h'
  by_cases hS : E ∈ S
  · rw [if_pos hS] at h'
    exfalso
    rcases h' with h | h <;> omega
  · rw [if_neg hS] at h'
    refine ⟨?_, hS⟩
    rcases h' with h | h <;> omega

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
    rw [hker]; simp
  let e : (A ⧸ Ideal.span (z '' (({m} : Finset (Fin n)) : Set (Fin n)))) ≃+* B :=
    (Ideal.quotEquivOfEq hs).trans (RingHom.quotientKerEquivOfSurjective hψ)
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = ψ a := fun a => rfl
  set emb := (({m} : Finset (Fin n))ᶜ).orderEmbOfFin rfl
  have hrange : ∀ i : {i : Fin n // i ≠ m}, ∃ k, emb k = i.1 := by
    intro i
    have hr := Finset.range_orderEmbOfFin (({m} : Finset (Fin n))ᶜ) rfl
    have : i.1 ∈ Set.range emb := by
      rw [hr]; simpa using i.2
    exact this
  refine ⟨_, e ∘ fun j => Ideal.Quotient.mk _ (z (emb j)), fun i => (hrange i).choose,
    IsRegularSystemOfParameters.map_ringEquiv e hsop, ?_, ?_⟩
  · intro i i' h
    apply Subtype.ext
    rw [← (hrange i).choose_spec, ← (hrange i').choose_spec]
    exact congrArg emb h
  · intro i
    simp only [Function.comp_apply, he]
    rw [(hrange i).choose_spec]

/-- The kernel of the stalk map of a closed subscheme composed with an isomorphism is the stalk of
its ideal. -/
private theorem ker_stalkMap_comp_subschemeι {W Y : Scheme.{u}} (J : Y.IdealSheafData)
    (e : W ⟶ J.subscheme) [IsIso e] (w : W) :
    RingHom.ker ((e ≫ J.subschemeι).stalkMap w).hom =
      IdealSheafData.stalk J ((e ≫ J.subschemeι) w) := by
  have : IsIso (e.stalkMap w) := IsOpenImmersion.instIsIsoCommRingCatStalkMap e w
  have hinj : Function.Injective (e.stalkMap w).hom :=
    (asIso (e.stalkMap w)).commRingCatIsoToRingEquiv.injective
  have key : ∀ a, ((e ≫ J.subschemeι).stalkMap w).hom a =
      (e.stalkMap w).hom ((J.subschemeι.stalkMap (e w)).hom a) := fun a => by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  ext a
  rw [RingHom.mem_ker, key, map_eq_zero_iff _ hinj]
  have h2 := IdealSheafData.ker_stalkMap_subschemeι J (e w)
  exact (SetLike.ext_iff.mp h2 a : _)

/-- The kernel of the stalk map of `X' ×_X Z ⟶ X'` is the stalk of the inverse image of the ideal
of `Z`. -/
private theorem ker_stalkMap_pullback_fst {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X)
    (w : ↥(pullback f I.subschemeι)) :
    RingHom.ker ((pullback.fst f I.subschemeι).stalkMap w).hom =
      IdealSheafData.stalk (I.comap f) (pullback.fst f I.subschemeι w) := by
  have h := Scheme.IdealSheafData.comapIso_inv_subschemeι I f
  have key : ∀ q : pullback f I.subschemeι ⟶ Y, (I.comapIso f).inv ≫ (I.comap f).subschemeι = q →
      RingHom.ker (q.stalkMap w).hom = IdealSheafData.stalk (I.comap f) (q w) := by
    rintro q rfl
    exact ker_stalkMap_comp_subschemeι _ _ w
  exact key _ h

/-- Over a point outside the biregular locus of a proper birational morphism onto a normal variety,
the fibre has more than one point. -/
private theorem not_subsingleton_fiber_of_notMem_biregularLocus {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {x : X}
    (hx : x ∉ biregularLocus f) : ¬ (f ⁻¹' {x}).Subsingleton := by
  have := hX.2
  have := hY.toIsIntegral
  have := hX.1.toIsIntegral
  have := hf.isDominant
  obtain ⟨u, rfl⟩ := f.surjective x
  have hu : u ∈ exceptionalSet f := hx
  have key := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hY hX.1 f
    rfl (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)).2.1
  have hu' : u ∈ (exceptionalSet f : Set Y) := hu
  rw [key] at hu'
  intro hsub
  have : Subsingleton (f ⁻¹' {f u}) := hsub.coe_sort
  have : DiscreteTopology (f ⁻¹' {f u}) := ⟨Subsingleton.elim _ _⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology (f ⁻¹' {f u})
  have hu'' : 0 < topologicalKrullDim (f ⁻¹' {f u}) := hu'
  exact (hu''.trans_le h0).false

/-- Being an isomorphism over an open is stable under base change. -/
private theorem isIso_pullback_snd_morphismRestrict {X Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (V : X.Opens) [IsIso (f ∣_ V)] :
    IsIso (pullback.snd f ι ∣_ (ι ⁻¹ᵁ V)) := by
  have hC := (isPullback_morphismRestrict (pullback.snd f ι) (ι ⁻¹ᵁ V)).flip
  have hB := IsPullback.of_hasPullback f ι
  have hs := hC.paste_horiz hB
  rw [← morphismRestrict_ι ι V] at hs
  have hD := IsPullback.of_right' hs (isPullback_morphismRestrict f V).flip
  exact hD.isIso_snd_of_isIso

/-- A morphism is injective over its biregular locus. -/
private theorem injOn_preimage_biregularLocus {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Set.InjOn f.base (f ⁻¹ᵁ biregularLocus f : Set X) := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hinj : Function.Injective ((f ⁻¹ᵁ biregularLocus f).ι ≫ f).base := by
    rw [← morphismRestrict_ι]
    exact ((f ∣_ biregularLocus f) ≫ (biregularLocus f).ι).isOpenEmbedding.injective
  exact fun a ha b hb hab ↦ congrArg Subtype.val (@hinj ⟨a, ha⟩ ⟨b, hb⟩ hab)

/-- The biregular locus of the base change is the preimage of the biregular locus of `f`, when the
fibres of `f` over the other points have several points. -/
private theorem mem_biregularLocus_pullback_snd_iff {X Y Z : Scheme.{u}} (f : Y ⟶ X) (ι : Z ⟶ X)
    (hA : ∀ x, x ∉ biregularLocus f → ¬ (f ⁻¹' {x}).Subsingleton) (z : Z) :
    z ∈ biregularLocus (pullback.snd f ι) ↔ ι z ∈ biregularLocus f := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine ⟨fun hz => ?_, fun hz =>
    le_biregularLocus (isIso_pullback_snd_morphismRestrict f ι (biregularLocus f)) hz⟩
  by_contra hx
  apply hA _ hx
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨w₁, hw₁, hw₁'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) y₁ z hy₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ι) y₂ z hy₂
  have h12 : w₁ = w₂ := injOn_preimage_biregularLocus (pullback.snd f ι)
    (show pullback.snd f ι w₁ ∈ biregularLocus (pullback.snd f ι) by rwa [hw₁'])
    (show pullback.snd f ι w₂ ∈ biregularLocus (pullback.snd f ι) by rwa [hw₂'])
    (hw₁'.trans hw₂'.symm)
  rw [← hw₁, ← hw₂, h12]

/-- Over the biregular locus, specializations lift along the morphism. -/
private theorem specializes_of_mem_biregularLocus {A B : Scheme.{u}} (h : A ⟶ B) {a b : A}
    (hb : h b ∈ biregularLocus h) (hab : h a ⤳ h b) : a ⤳ b := by
  have : IsIso (h ∣_ biregularLocus h) := isBiregular_biregularLocus h
  have hφ : ∀ x : (h ⁻¹ᵁ biregularLocus h).toScheme,
      ((h ∣_ biregularLocus h).homeomorph x).1 = h x.1 := fun x =>
    morphismRestrict_base_coe h _ x
  have ha : h a ∈ biregularLocus h := hab.mem_open (biregularLocus h).isOpen hb
  have hsp : (⟨h a, ha⟩ : biregularLocus h) ⤳ ⟨h b, hb⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  have hsp' := hsp.map (h ∣_ biregularLocus h).homeomorph.symm.continuous
  have h1 : (h ∣_ biregularLocus h).homeomorph.symm ⟨h a, ha⟩ = ⟨a, ha⟩ :=
    (h ∣_ biregularLocus h).homeomorph.symm_apply_eq.mpr (Subtype.ext (hφ ⟨a, ha⟩).symm)
  have h2 : (h ∣_ biregularLocus h).homeomorph.symm ⟨h b, hb⟩ = ⟨b, hb⟩ :=
    (h ∣_ biregularLocus h).homeomorph.symm_apply_eq.mpr (Subtype.ext (hφ ⟨b, hb⟩).symm)
  rw [h1, h2] at hsp'
  exact hsp'.map continuous_subtype_val

/-- A prime divisor whose generic point lies on a prime divisor `E` is `E`. -/
private theorem eq_of_genericPoint_mem_support {Y : Scheme.{u}} {E F : PrimeDivisor Y}
    (hF : AlgebraicGeometry.PrimeDivisor.genericPoint F ∈ E.support) : F = E := by
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hF
  have h1 : AlgebraicGeometry.PrimeDivisor.genericPoint E ⤳
      AlgebraicGeometry.PrimeDivisor.genericPoint F := specializes_iff_mem_closure.mpr hF
  by_contra hne
  have := Order.coheight_strictAnti (MMP.Intersection.lt_of_specializes_of_ne h1 hne)
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at this
  exact lt_irrefl _ (this (by decide))

/-- A prime divisor meeting the biregular locus has a prime inverse transform, whose generic point
maps to its generic point. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus {A B : Scheme.{u}}
    (h : A ⟶ B) (D : PrimeDivisor B)
    (hD : AlgebraicGeometry.PrimeDivisor.genericPoint D ∈ biregularLocus h) :
    ∃ F : PrimeDivisor A, inverseTransformPrimeDivisor h D = some F ∧
      h (AlgebraicGeometry.PrimeDivisor.genericPoint F) =
        AlgebraicGeometry.PrimeDivisor.genericPoint D := by
  set V := biregularLocus h
  have : IsIso (h ∣_ V) := isBiregular_biregularLocus h
  set φ := (h ∣_ V).homeomorph
  set a' := φ.symm ⟨AlgebraicGeometry.PrimeDivisor.genericPoint D, hD⟩
  set a : A := a'.1
  have hφ : ∀ x : (h ⁻¹ᵁ V).toScheme, (φ x).1 = h x.1 := fun x =>
    (morphismRestrict_base_coe h V x)
  have ha : h a = AlgebraicGeometry.PrimeDivisor.genericPoint D := by
    have h1 := hφ a'
    have h2 : φ a' = ⟨AlgebraicGeometry.PrimeDivisor.genericPoint D, hD⟩ := φ.apply_symm_apply _
    rw [h2] at h1
    exact h1.symm
  have haV : h a ∈ V := ha ▸ hD
  have hcoh : Order.coheight a = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus h haV, ha,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set F := AlgebraicGeometry.PrimeDivisor.ofCoheightOne a hcoh
  have hFg : AlgebraicGeometry.PrimeDivisor.genericPoint F = a :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne a hcoh
  refine ⟨F, ?_, by rw [hFg, ha]⟩
  rw [inverseTransformPrimeDivisor_eq_some_iff]
  refine ⟨⟨_, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' D, hD⟩, ?_⟩
  rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf, inverseTransformIdeal]
  congr 1
  apply Closeds.ext
  change F.support = closure (h ⁻¹' ((D.support : Set B) ∩ V))
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hFg]
  apply le_antisymm
  · exact closure_mono (Set.singleton_subset_iff.mpr
      ⟨ha ▸ MMP.Positivity.PrimeDivisor.genericPoint_mem_support' D, haV⟩)
  · refine closure_minimal ?_ isClosed_closure
    rintro y ⟨hyD, hyV⟩
    have hsp : (⟨AlgebraicGeometry.PrimeDivisor.genericPoint D, hD⟩ : V) ⤳ ⟨h y, hyV⟩ := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      exact MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD
    have hsp' := hsp.map φ.symm.continuous
    have hy' : φ.symm ⟨h y, hyV⟩ = ⟨y, hyV⟩ :=
      φ.symm_apply_eq.mpr (Subtype.ext (hφ ⟨y, hyV⟩).symm)
    rw [hy'] at hsp'
    exact specializes_iff_mem_closure.mp (hsp'.map continuous_subtype_val)

/-- If the inverse transform of `D` is the prime divisor `F`, the generic point of `D` is biregular
and is the image of that of `F`. -/
private theorem genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some
    {A B : Scheme.{u}}
    {h : A ⟶ B} {D : PrimeDivisor B} {F : PrimeDivisor A}
    (hF : inverseTransformPrimeDivisor h D = some F) :
    AlgebraicGeometry.PrimeDivisor.genericPoint D ∈ biregularLocus h ∧
      h (AlgebraicGeometry.PrimeDivisor.genericPoint F) =
        AlgebraicGeometry.PrimeDivisor.genericPoint D := by
  obtain ⟨⟨x, hxD, hxV⟩, -⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hF
  have hη : AlgebraicGeometry.PrimeDivisor.genericPoint D ∈ biregularLocus h :=
    (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hxD).mem_open
      (biregularLocus h).isOpen hxV
  obtain ⟨F', hF', hF'g⟩ := inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus h D hη
  rw [hF] at hF'
  cases hF'
  exact ⟨hη, hF'g⟩

/-- The inverse transform of a component of `Δ` meeting the biregular locus is a component of the
inverse transform of `Δ`. -/
private theorem mem_support_inverseTransformDivisor {A B : Scheme.{u}} (h : A ⟶ B) {R : Type*}
    [AddCommMonoid R] (Δ : DivisorWithCoeffs R B) {E : PrimeDivisor B} (hE : E ∈ Δ.support)
    {F : PrimeDivisor A} (hF : inverseTransformPrimeDivisor h E = some F) :
    F ∈ (inverseTransformDivisor h Δ).support := by
  classical
  have hEg := (genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some hF).2
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
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      have hDg := (genericPoint_mem_biregularLocus_of_inverseTransformPrimeDivisor_eq_some hD).2
      apply hDE
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [← hDg, ← hEg]
  · exact fun hE' => absurd hE hE'

/-- A member of a regular system of parameters does not lie in `𝔪²`. -/
private theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {N : ℕ} {z : Fin N → R} (hz : IsRegularSystemOfParameters z) (i : Fin N) :
    z i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  have := isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hmem, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  exact fun h => hli.ne_zero i ((Ideal.toCotangent_eq_zero _ _).mpr h)

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
  rw [Ring.ordFrac_eq_ord _ hb, Ring.ordMonoidWithZeroHom_eq_coe _ hnz (ENat.coe_toNat hfin).symm]

open Classical in
/-- **The base change to a component of the general member.** For a connected component `Z` of
`Supp D`, the base change `Y ×_X Z` is cut out in `Y` by a single component `T` of `f^*D`: its
image is `T`, the generic point of `Y ×_X Z` maps to that of `T`, and the kernel of each stalk map
of `Y ×_X Z → Y` is the ideal of `T`. -/
private theorem exists_primeDivisor_pullback_fst [IsAlgClosed k] [CharZero k]
    {Δ : QDivisor X} {f : Y ⟶ X} (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (Ex : Finset (PrimeDivisor Y))
    {D : Divisor X} (hD0 : 0 ≤ D) (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    (H' : Divisor Y) (hpb : D.IsPullback f hB H')
    (h01 : ∀ F : PrimeDivisor Y,
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 1)
    (hsnc : DivisorWithCoeffs.IsSNC (f ≫ sX)
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)))
    (hdisj : ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support)
    (Z : Closeds X) (x₀ : X)
    (hZ : connectedComponentIn (D.supp : Set X) x₀ = (Z : Set X))
    (hY : IsNormalVariety k (f ≫ sX))
    (hY' : IsNormalVariety k
      (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)) :
    have := hY'.1.toIsIntegral
    ∃ T : PrimeDivisor Y, T ∈ H'.support ∧ H'.coeff T = 1 ∧
      T ∉ (inverseTransformDivisor f Δ).support ∪ Ex ∧
      pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
        (genericPoint
          (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι : Scheme.{u})) =
          T.genericPoint ∧
      T.support = Set.range (pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) ∧
      ∀ w, RingHom.ker
        ((pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).stalkMap w).hom =
        IdealSheafData.stalk T.idealSheaf
          (pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι w) := by
  set I := Scheme.IdealSheafData.vanishingIdeal Z with hIdef
  set 𝔅 := (inverseTransformDivisor f Δ).support ∪ Ex with h𝔅
  set D' : Divisor Y := H' + ∑ F ∈ 𝔅, Finsupp.single F (1 : ℤ) with hD'def
  have : IsIntegral Y := hY.1.toIsIntegral
  have := hY'.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  have hUFD : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) := fun y => by
    have : Smooth (f ≫ sX) := hsmY.smooth
    have := isRegularLocalRing_stalk_of_smooth_over_field (f ≫ sX) y
    exact IsRegularLocalRing.uniqueFactorizationMonoid _
  have hH'nn : ∀ E, 0 ≤ H'.coeff E := coeff_nonneg_of_isPullback hD0 hDc hpb
  have hH'1 : ∀ E ∈ H'.support, H'.coeff E = 1 ∧ E ∉ 𝔅 := fun E hE =>
    coeff_eq_one_and_notMem_of_mem_support hH'nn 𝔅 h01 hE
  have hD'mem : ∀ E ∈ H'.support, E ∈ D'.support := by
    intro E hE
    rw [Finsupp.mem_support_iff]
    change DivisorWithCoeffs.coeff D' E ≠ 0
    have hc : DivisorWithCoeffs.coeff (∑ F ∈ 𝔅, Finsupp.single F (1 : ℤ) : Divisor Y) E = 0 := by
      change (∑ F ∈ 𝔅, Finsupp.single F (1 : ℤ)) E = 0
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun F hF => ?_
      rw [Finsupp.single_apply, if_neg]
      exact fun hFE => (hH'1 E hE).2 (hFE ▸ hF)
    rw [hD'def, DivisorWithCoeffs.coeff_add, hc, add_zero, (hH'1 E hE).1]
    exact one_ne_zero
  have hgen : ∀ E ∈ H'.support, ∀ y ∈ E.support, ∃ π : Y.presheaf.stalk y, π ≠ 0 ∧
      IdealSheafData.stalk E.idealSheaf y = Ideal.span {π} := by
    intro E hE y hy
    obtain ⟨n, z, j, hz, -, hI⟩ := hsnc.2 y
    have := isRegularLocalRing_of_isRegularSystemOfParameters hz
    exact ⟨z (j ⟨E, hD'mem E hE, hy⟩), MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz _,
      hI ⟨E, hD'mem E hE, hy⟩⟩
  have hK : ∀ y : Y, f y ∈ (Z : Set X) → ∃ E ∈ H'.support, y ∈ E.support ∧
      E.support ⊆ f ⁻¹' Z ∧ IdealSheafData.stalk (I.comap f) y =
        IdealSheafData.stalk E.idealSheaf y := fun y hy =>
    exists_stalk_comap_vanishingIdeal_eq (f ≫ sX) hsmY hUFD hD0 hDc hpb
      (fun E hE => (hH'1 E hE).1) hdisj hgen hZ hy
  have hιrange : Set.range I.subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hrange : Set.range (pullback.fst f I.subschemeι) = f ⁻¹' (Z : Set X) := by
    rw [Scheme.Pullback.range_fst, hιrange]
  have hclosed : IsClosed (Set.range (pullback.fst f I.subschemeι)) :=
    (pullback.fst f I.subschemeι).isClosedEmbedding.isClosed_range
  set ζ := pullback.fst f I.subschemeι (genericPoint (pullback f I.subschemeι : Scheme.{u}))
    with hζ
  have hζZ : f ζ ∈ (Z : Set X) := by
    rw [← Set.mem_preimage, ← hrange]
    exact ⟨_, rfl⟩
  have hcl : closure {ζ} = Set.range (pullback.fst f I.subschemeι) := by
    apply le_antisymm
    · exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
    · rintro _ ⟨w, rfl⟩
      exact specializes_iff_mem_closure.mp
        (((genericPoint_spec (pullback f I.subschemeι : Scheme.{u})).specializes trivial).map
          (pullback.fst f I.subschemeι).continuous)
  obtain ⟨T, hT, hζT, hTZ, -⟩ := hK ζ hζZ
  have hTsupp : T.support = Set.range (pullback.fst f I.subschemeι) := by
    refine le_antisymm (fun y hy => hrange ▸ hTZ hy) ?_
    rw [← hcl]
    exact closure_minimal (Set.singleton_subset_iff.mpr hζT) T.idealSheaf.support.isClosed
  have hTgen : ζ = T.genericPoint := by
    have h1 : IsGenericPoint ζ T.support := by rw [hTsupp, ← hcl]; exact isGenericPoint_closure
    have h2 : IsGenericPoint T.genericPoint T.support := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isGenericPoint_closure
    exact h1.eq h2
  refine ⟨T, hT, (hH'1 T hT).1, (hH'1 T hT).2, hTgen, hTsupp, fun w => ?_⟩
  have hwZ : f (pullback.fst f I.subschemeι w) ∈ (Z : Set X) := by
    rw [← Set.mem_preimage, ← hrange]
    exact ⟨_, rfl⟩
  obtain ⟨E, hE, hwE, hEZ, hst⟩ := hK _ hwZ
  have hET : E = T := by
    apply eq_of_genericPoint_mem_support
    rw [hTsupp, hrange]
    exact hEZ (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E)
  rw [ker_stalkMap_pullback_fst, hst, hET]

omit [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X] [CompactSpace X] in
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
    have := MMP.Intersection.specializes_of_primeOfSpecializes_le hηE h hle
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
    exact this
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
      have hmax : IsMax (genericPoint Y) := fun z _ ↦ genericPoint_specializes z
      have h0 := Order.coheight_eq_zero.mpr hmax
      rw [← heq, D.coheight_genericPoint] at h0
      exact one_ne_zero h0
    have hne : (Y.presheaf.stalkSpecializes hηD).hom π ≠ 0 := fun h0 =>
      hπ0 (MMP.Intersection.stalkSpecializes_injective hηD (h0.trans (map_zero _).symm))
    rw [ord_algebraMap_eq_ringOrd D.coheight_genericPoint hne, h1]
    rfl
  · have hDE' : D.genericPoint ∉ E.support := fun hmem =>
      hDE (eq_of_genericPoint_mem_support hmem)
    exact D.ord_algebraMap_of_isUnit (hunit _ hηD hDE')

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **The pulled-back local equation.** A local equation `φ` of an effective divisor `D` on `V`
is a rational function `t` on `X` whose pull-back has order `coeff_E(f^*D)` along every prime
divisor `E` of `Y` with `f(η_E) ∈ V`. -/
private theorem exists_ord_functionFieldMap_eq_coeff [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y] {f : Y ⟶ X} [IsDominant f] {D : Divisor X} (hD0 : 0 ≤ D)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp}
    {H' : Divisor Y} (hpb : D.IsPullback f hB H') {V : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation V φ) :
    ∃ t : X.functionField, t ≠ 0 ∧ ∀ E : PrimeDivisor Y, f E.genericPoint ∈ V →
      Y.ord (functionFieldMap f t) E.genericPoint = H'.coeff E := by
  have hsub : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]; infer_instance
  obtain ⟨x⟩ : Nonempty X := inferInstance
  set W₀ := pointComponent x
  have hη : genericPoint X ⤳ componentGenericPoint X W₀ := genericPoint_specializes _
  refine ⟨(X.presheaf.stalkSpecializes hη).hom ((φ : RationalFunctions X) W₀), ?_, fun E hE => ?_⟩
  · exact (((Pi.isUnit_iff.mp φ.isUnit) W₀).map _).ne_zero
  obtain ⟨a, ha⟩ := exists_germ_eq_of_isLocalEquation hD0 hφ hE
  have hW : pointComponent (f E.genericPoint) = W₀ := Subsingleton.elim _ _
  have hta : algebraMap _ X.functionField a =
      (X.presheaf.stalkSpecializes hη).hom ((φ : RationalFunctions X) W₀) := by
    have e1 : algebraMap (X.presheaf.stalk (f E.genericPoint)) X.functionField a =
        (X.presheaf.stalkSpecializes (genericPoint_specializes
          (componentGenericPoint X (pointComponent (f E.genericPoint))))).hom
          ((stalkToRationalFunctions X (mem_pointComponent (f E.genericPoint))).hom a) := by
      change (X.presheaf.stalkSpecializes _).hom a =
        (X.presheaf.stalkSpecializes _ ≫ X.presheaf.stalkSpecializes _).hom a
      rw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [e1, ha]
    clear e1 ha
    revert hη
    rw [← hW]
    intro hη
    rfl
  obtain ⟨hne, hc⟩ := coeff_eq_ord_stalkMap hpb hφ hE (mem_pointComponent _) ha
    (specializes_refl _) E.coheight_genericPoint
  have hEq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ E.coheight_genericPoint = E :=
    ((MMP.Mori.PrimeDivisor.eq_ofCoheightOne_iff E E.coheight_genericPoint).mpr rfl).symm
  rw [hEq] at hc
  rw [TopCat.Presheaf.stalkSpecializes_refl] at hne hc
  rw [← hta, functionFieldMap_algebraMap_stalk, hc]
  exact ord_algebraMap_eq_ringOrd E.coheight_genericPoint hne

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- **Non-exceptional prime divisors of a log resolution.** A prime divisor `D` of `Y` that is not
`f`-exceptional maps onto a prime divisor `P` of `X`, the order along `D` of a pulled-back form is
its order along `P`, and `D` is a component of `f⁻¹_*Δ` as soon as `P` is a component of `Δ`. -/
private theorem exists_primeDivisor_of_not_isExceptional {Δ : QDivisor X}
    (hX : IsNormalVariety k sX)
    {f : Y ⟶ X} (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
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
      (by rw [ringKrullDim_stalk_eq_coheight, P.coheight_genericPoint]; rfl)
  obtain ⟨F, hF, hFg⟩ := inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus f P hbir
  have hFD : F = D :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <| injOn_preimage_biregularLocus f
      (show f F.genericPoint ∈ biregularLocus f by rwa [hFg])
      (show f D.genericPoint ∈ biregularLocus f by rwa [hfP]) (hFg.trans hfP.symm)
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
    have h1 : jj ⟨D₁, hBD D₁ hD₁, hy₁⟩ = jj ⟨D₂, hBD D₂ hD₂, hy₂⟩ :=
      congrArg Subtype.val (hσ h0)
    exact congrArg Subtype.val (hjj h1)
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
      · rintro ⟨i, rfl⟩; rw [hϖ, Fin.subsingleton_one.elim i (σ ⟨_, hne D₀ hD₀ hy₀⟩)]
      · rintro rfl; exact ⟨_, hϖ.symm⟩
    have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hmax
    have hne0 : algebraMap _ P.functionField ϖ ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hirr.ne_zero
    rw [← hzw]
    change P.ord (algebraMap _ P.functionField ϖ) w = 1
    have : Ring.KrullDimLE 1 (P.presheaf.stalk w) := krullDimLE_of_coheight_le hw.le
    rw [Scheme.ord_eq_iff hw hne0]
    exact Ring.ordFrac_irreducible hirr

end BaseChange

/-! ### Pull-backs of forms along birational morphisms -/

section PullbackForms

section Field

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}

/-- The pull-back of forms along an extension of fields is semilinear. -/
private theorem pullbackForms_smul (m : ℤ) (a : K) (τ : PluriForms k K d m) :
    pullbackForms (K' := K') m (a • τ) = algebraMap K K' a • pullbackForms (K' := K') m τ := by
  classical
  by_cases hω : ∃ ω : ⋀[K]^d Ω[K⁄k], IsPullbackGenerator K' ω
  · obtain ⟨ω, hω⟩ := hω
    rw [pullbackForms_eq hω, pullbackForms_eq hω]
    unfold pullbackFormsAlong
    rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul]
  · unfold pullbackForms
    rw [dif_neg hω, dif_neg hω, smul_zero]

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
      Finsupp.single_apply, if_pos rfl, mul_one]
  refine ⟨fun τ₁ τ₂ h => ?_, fun ρ => ?_⟩
  · have h1 := congrArg (fun ρ => b'.repr ρ ()) h
    simp only [hrepr] at h1
    have h2 := hK.1 h1
    exact b.ext_elem fun i => by cases i; exact h2
  · obtain ⟨c, hc⟩ := hK.2 (b'.repr ρ ())
    refine ⟨c • b (), b'.ext_elem fun i => ?_⟩
    cases i
    rw [hrepr, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self,
      Finsupp.single_apply, if_pos rfl, mul_one, hc]

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
  exact pullbackForms_smul (K := W.functionField) (K' := V.functionField) m a τ

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

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- Orders of forms do not see a rewriting of the structure morphism. -/
private theorem ordForm_cast {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
    {s₁ s₂ : W ⟶ Spec (.of k)} (h : s₁ = s₂) {d : ℕ} {m : ℤ} (ρ : RationalPluriForms s₁ d m)
    (G : PrimeDivisor W) : G.ordForm (h ▸ ρ : RationalPluriForms s₂ d m) = G.ordForm ρ := by
  subst h; rfl

omit [IsLocallyNoetherian Y] [IsNormal Y] in
/-- A rewriting of the structure morphism does not make a form vanish. -/
private theorem cast_ne_zero {W : Scheme.{u}} [IsIntegral W] {s₁ s₂ : W ⟶ Spec (.of k)}
    (h : s₁ = s₂) {d : ℕ} {m : ℤ} {ρ : RationalPluriForms s₁ d m} (hρ : ρ ≠ 0) :
    (h ▸ ρ : RationalPluriForms s₂ d m) ≠ 0 := by
  subst h; exact hρ

end PullbackForms

/-! ### The local comparison -/

open Classical in
/-- **The local adjunction step.** Around every point `z` of the connected component `H⁰ = Z` of
a general member `D`, a local generator `τ` of `𝒪_X(m(K_X + Δ))` near `z` and a local generator
`τ'` of `𝒪_{H⁰}(m(K_{H⁰} + Δ|_{H⁰}))` near `z` can be chosen so that, for every component `F` of
`E ∩ H'⁰` over the neighbourhood, `ord_E(f^*τ) = ord_F(f⁰^*τ')`. -/
private theorem exists_generatesOn_ordPullback_eq [IsAlgClosed k] [CharZero k]
    {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    {D : Divisor X} (hD0 : 0 ≤ D) (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    (H' : Divisor Y) (hpb : D.IsPullback f hB H')
    (h01 : ∀ F : PrimeDivisor Y,
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 0 ∨
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).coeff F = 1)
    (hsnc : DivisorWithCoeffs.IsSNC (f ≫ sX)
      (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)))
    (hdisj : ∀ E ∈ H'.support, ∀ E' ∈ H'.support, E ≠ E' → Disjoint E.support E'.support)
    (Z : Closeds X) (x₀ : X)
    (hZ : connectedComponentIn (D.supp : Set X) x₀ = (Z : Set X))
    (hY : IsNormalVariety k (f ≫ sX))
    (hH : IsNormalVariety k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX))
    (hY' : IsNormalVariety k
      (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX))
    (hlog : IsLogResolution ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
      (QDivisor.toRDivisor (Δ.restrictComponents
        (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι))
      (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι))
    {m n n' : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hn' : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = n')
    (hmC : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor)
    (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :
    haveI := hH.1.toIsIntegral
    haveI := hH.2
    haveI := hH.1.toLocallyOfFiniteType
    haveI := LocallyOfFiniteType.isLocallyNoetherian
      ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
    ∃ U : X.Opens, (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι z ∈ U ∧
      ∃ τ : RationalPluriForms sX n m, GeneratesOn Δ m U τ ∧
      ∃ U' : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens, z ∈ U' ∧
      ∃ τ' : RationalPluriForms ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) n' m,
        GeneratesOn (Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
          m U' τ' ∧
        ∀ E ∈ Ex,
        ∀ F : PrimeDivisor (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
          Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
            pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹'
              E.support) F.support →
          pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι F.genericPoint ∈ U' →
          (⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, E⟩ :
              DivisorOver k sX).ordPullback τ =
            (⟨_, pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι, hY',
              hlog.isBirationalMorphism, F⟩ :
              DivisorOver k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)).ordPullback
              τ' := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let P := pullback f I.subschemeι
  let p₁ := pullback.fst f I.subschemeι
  let p₂ := pullback.snd f I.subschemeι
  have hX : IsNormalVariety k sX := hΔ.isNormalVariety
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have hsmY : IsSmoothScheme (f ≫ sX) := hf.isSmoothScheme
  have := hf.isProper
  have hbirf := hf.toIsSmoothResolution.isBirationalMorphism
  have : IsDominant f := hbirf.isDominant
  have := hH.1.toIsIntegral
  have := hH.2
  have := hH.1.toLocallyOfFiniteType
  have := LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ sX)
  have := hY'.1.toIsIntegral
  have := hY'.2
  have := hY'.1.toLocallyOfFiniteType
  have := LocallyOfFiniteType.isLocallyNoetherian (p₂ ≫ I.subschemeι ≫ sX)
  have hbirg := hlog.isBirationalMorphism
  have : IsDominant (p₂) := hbirg.isDominant
  have := hlog.isProper
  have hcond : p₁ ≫ f ≫ sX = p₂ ≫ I.subschemeι ≫ sX := pullback.condition_assoc _
  have : LocallyOfFiniteType (p₁ ≫ f ≫ sX) := by rw [hcond]; infer_instance
  -- the component `T` of `f^*D` cutting out the base change
  obtain ⟨T, hTH', hT1, hTB, hTgen, hTsupp, hker⟩ := exists_primeDivisor_pullback_fst hf Ex hD0
    hDc hB H' hpb h01 hsnc hdisj Z x₀ hZ hY hY'
  -- dimensions
  have he : (letI := functionFieldAlgebra (f ≫ sX); (Algebra.trdeg k Y.functionField).toNat) =
      n' + 1 := by
    have hgbij := hbirg.functionFieldMap_bijective
    have hfbij := hbirf.functionFieldMap_bijective
    have hP1 := trdeg_functionField_eq_of_bijective (I.subschemeι ≫ sX) (p₂) hgbij
    have hH1 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := I.subschemeι ≫ sX) hn'
    -- the residue field of `𝒪_{Y,T}`
    let := stalkAlgebra (f ≫ sX) (p₁ (genericPoint P))
    let := functionFieldAlgebra (p₁ ≫ f ≫ sX)
    let : Algebra (Y.presheaf.stalk (p₁ (genericPoint P))) P.functionField :=
      ((p₁).stalkMap (genericPoint P)).hom.toAlgebra
    obtain ⟨hdvr, hfree', hfin', hsm', -, hrank'⟩ := stalk_facts (sY := f ≫ sX) hTgen
    obtain ⟨htow, hsurjT⟩ := stalkMap_facts (sY := f ≫ sX) (j := p₁)
    obtain ⟨ϖ, -, -, -, hkerϖ, hϖ2, -⟩ := exists_uniformizer (sY := f ≫ sX) hTgen
    have := essFiniteType_functionField (sX := p₁ ≫ f ≫ sX)
    have h1 := MMP.Fourfold.finrank_kaehlerDifferential_add_one (k := k) hsurjT hkerϖ hϖ2
    rw [hrank', finrank_kaehlerDifferential_eq_trdeg] at h1
    rw [← h1]
    congr 1
    revert hP1
    rw [← hcond]
    intro hP1
    rw [← hP1, hH1]
  have hn : n = n' + 1 := by
    have hX1 := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
      hK.topologicalKrullDim_eq
    have hXY := trdeg_functionField_eq_of_bijective sX f hbirf.functionFieldMap_bijective
    rw [← hX1, ← he, hXY]
  subst hn
  have hdX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  -- a local generator `τ` and a local equation `t` of `D` at `x = ι z`
  obtain ⟨-, U₁, hxU₁, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hΔ hK hmC (I.subschemeι z)
  obtain ⟨V, hxV, φ, hφ⟩ := hDc (I.subschemeι z)
  obtain ⟨t, ht0, ht⟩ := exists_ord_functionFieldMap_eq_coeff hD0 hpb hφ
  -- the form `θ = f^*(t^{-m} τ)` on `Y`
  have hpb0 : pullbackRationalPluriForms sX f (0 : RationalPluriForms sX (n' + 1) m) = 0 := by
    have := pullbackRationalPluriForms_smul (sW := sX) f (0 : X.functionField)
      (0 : RationalPluriForms sX (n' + 1) m)
    rwa [zero_smul, map_zero, zero_smul] at this
  have hpbinj := (pullbackRationalPluriForms_bijective (sW := sX) f
    hbirf.functionFieldMap_bijective hdX (m : ℤ)).1
  have htK : functionFieldMap f t ≠ 0 := (map_ne_zero _).mpr ht0
  obtain ⟨θ, hθ_def⟩ : ∃ θ : RationalPluriForms (f ≫ sX) (n' + 1) m,
      θ = pullbackRationalPluriForms sX f (t ^ (-(m : ℤ)) • τ) := ⟨_, rfl⟩
  have hfτ0 : pullbackRationalPluriForms sX f τ ≠ 0 := fun h0 =>
    hτ.1 (hpbinj (h0.trans hpb0.symm))
  have hθ0 : θ ≠ 0 := by
    rw [hθ_def, pullbackRationalPluriForms_smul, map_zpow₀]
    exact smul_ne_zero (zpow_ne_zero _ htK) hfτ0
  have hθord : ∀ D : PrimeDivisor Y, f D.genericPoint ∈ V →
      D.ordForm θ = (⟨Y, f, hY, hbirf, D⟩ : DivisorOver k sX).ordPullback τ -
        m * H'.coeff D := by
    intro D hDV
    rw [hθ_def, pullbackRationalPluriForms_smul, map_zpow₀,
      D.ordForm_smul he (zpow_ne_zero _ htK) hfτ0, ord_zpow _ htK, ht D hDV]
    change _ = D.ordForm (pullbackRationalPluriForms sX f τ) - _
    ring
  -- the boundary `B` and the snc divisor `H' + B`
  have hTD' : T ∈ (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
      Finsupp.single F (1 : ℤ)).support := by
    rw [Finsupp.mem_support_iff]
    change DivisorWithCoeffs.coeff (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
      Finsupp.single F (1 : ℤ)) T ≠ 0
    have hc : DivisorWithCoeffs.coeff (∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ) : Divisor Y) T = 0 := by
      change (∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)) T = 0
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun F hF => ?_
      rw [Finsupp.single_apply, if_neg]
      exact fun hFT => hTB (hFT ▸ hF)
    rw [DivisorWithCoeffs.coeff_add, hc, add_zero, hT1]
    exact one_ne_zero
  have hBD' : ∀ D ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
      D ∈ (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ)).support := by
    intro E hE
    rw [Finsupp.mem_support_iff]
    change DivisorWithCoeffs.coeff (H' + ∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
      Finsupp.single F (1 : ℤ)) E ≠ 0
    have hc : DivisorWithCoeffs.coeff (∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
        Finsupp.single F (1 : ℤ) : Divisor Y) E = 1 := by
      change (∑ F ∈ (inverseTransformDivisor f Δ).support ∪ Ex, Finsupp.single F (1 : ℤ)) E = 1
      rw [Finsupp.finsetSum_apply, Finset.sum_eq_single E]
      · simp
      · intro F _ hFE; rw [Finsupp.single_apply, if_neg hFE]
      · exact fun h => absurd hE h
    have hH'nn : ∀ E, 0 ≤ H'.coeff E := coeff_nonneg_of_isPullback hD0 hDc hpb
    have h0 : H'.coeff E = 0 := by
      by_contra hne
      exact (coeff_eq_one_and_notMem_of_mem_support hH'nn _ h01
        (Finsupp.mem_support_iff.mpr hne)).2 hE
    rw [DivisorWithCoeffs.coeff_add, hc, h0]
    exact one_ne_zero
  -- the coefficients of `f^*D` along the prime divisors through a point of `T`
  have hH'coeff : ∀ (y : Y) (D : PrimeDivisor Y), y ∈ T.support → y ∈ D.support →
      H'.coeff D = if D = T then 1 else 0 := by
    intro y D hyT hyD
    split_ifs with hDT
    · rw [hDT, hT1]
    · by_contra hne
      exact Set.disjoint_left.mp (hdisj D (Finsupp.mem_support_iff.mpr hne) T hTH' hDT) hyD hyT
  -- the order of `f^*τ` along a prime divisor off the boundary vanishes
  have hτ0 : ∀ D : PrimeDivisor Y, f D.genericPoint ∈ U₁ →
      D ∉ (inverseTransformDivisor f Δ).support ∪ Ex →
      (⟨Y, f, hY, hbirf, D⟩ : DivisorOver k sX).ordPullback τ = 0 := by
    intro D hDU hDB
    have hDex : ¬ RationalMap.IsExceptional f.toRationalMap D := fun h =>
      hDB (Finset.mem_union_right _ ((hEx D).mpr h))
    obtain ⟨PX, hPX, hord, hsupp⟩ := exists_primeDivisor_of_not_isExceptional hX hf hY hDex
    rw [hord]
    have hPXΔ : PX ∉ Δ.support := fun h => hDB (Finset.mem_union_left _ (hsupp h))
    have hc := hτ.2 PX
      ⟨PX.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' PX, hPX ▸ hDU⟩
    have h0 : DivisorWithCoeffs.coeff Δ PX = 0 := Finsupp.notMem_support_iff.mp hPXΔ
    rw [h0, mul_zero, add_zero] at hc
    exact_mod_cast hc
  -- a local equation of `T` at each point of the base change
  have hframe : ∀ w : P, ∃ h : Y.presheaf.stalk (p₁ w),
      RingHom.ker ((p₁).stalkMap w).hom = Ideal.span {h} ∧
      h ∉ IsLocalRing.maximalIdeal (Y.presheaf.stalk (p₁ w)) ^ 2 ∧
      IdealSheafData.stalk T.idealSheaf (p₁ w) = Ideal.span {h} := by
    intro w
    have hyT : p₁ w ∈ T.support := hTsupp ▸ ⟨w, rfl⟩
    obtain ⟨N, z, jj, hz, -, hI⟩ := hsnc.2 (p₁ w)
    exact ⟨z (jj ⟨T, hTD', hyT⟩), (hker w).trans (hI ⟨T, hTD', hyT⟩),
      notMem_maximalIdeal_sq hz _, hI ⟨T, hTD', hyT⟩⟩
  -- the residue of `θ` at a point of the base change over `U₁ ∩ V`
  have hres : ∀ w : P, f (p₁ w) ∈ U₁ → f (p₁ w) ∈ V →
      ∀ (π : Y.presheaf.stalk (p₁ w)) (β : ℤ),
      (∀ hζ : p₁ (genericPoint P) ⤳ p₁ w,
        IsUnit ((Y.presheaf.stalkSpecializes hζ).hom π)) →
      (∀ D : PrimeDivisor Y, p₁ w ∈ D.support →
        (⟨Y, f, hY, hbirf, D⟩ : DivisorOver k sX).ordPullback τ =
          β * Y.ord (algebraMap _ Y.functionField π) D.genericPoint) →
      ∃ ρ : RationalPluriForms (p₁ ≫ f ≫ sX) n' m,
        MMP.Fourfold.IsPoincareResidue (f ≫ sX) (p₁) n' m θ ρ ∧ ρ ≠ 0 ∧
        ∀ G : PrimeDivisor P,
          G.genericPoint = w →
          G.ordForm ρ = β * P.ord
            (algebraMap _ P.functionField (((p₁).stalkMap w).hom π)) w := by
    intro w hwU hwV π β hπ hβ
    have hyT : p₁ w ∈ T.support := hTsupp ▸ ⟨w, rfl⟩
    obtain ⟨h, hkerh, hh2, hIh⟩ := hframe w
    have hordh := (ord_algebraMap_of_stalk_idealSheaf_eq_span hsmY hyT hIh).1
    refine exists_isPoincareResidue_ordForm (sY := f ≫ sX) (j := p₁) hsmY hTgen he θ hθ0 w β
      hkerh hh2 ?_ hπ fun D hyD => ?_
    · have := hordh T hyT
      rw [if_pos rfl] at this
      exact this
    · have hηD : D.genericPoint ⤳ p₁ w :=
        MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD
      have hDV : f D.genericPoint ∈ V := (hηD.map f.continuous).mem_open V.isOpen hwV
      rw [hθord D hDV, hβ D hyD, hH'coeff _ D hyT hyD, hordh D hyD]
  -- a point of the base change over `z`
  have := hbirg.isDominant
  obtain ⟨wz, hwz⟩ := p₂.surjective z
  have hfwz : f (p₁ wz) = I.subschemeι z := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hwz]
  have hTwz : T.genericPoint ⤳ p₁ wz := by
    rw [← hTgen]
    exact ((genericPoint_spec P).specializes trivial).map (p₁).continuous
  have hfTU : f T.genericPoint ∈ U₁ := (hTwz.map f.continuous).mem_open U₁.isOpen (hfwz ▸ hxU₁)
  have hfTV : f T.genericPoint ∈ V := (hTwz.map f.continuous).mem_open V.isOpen (hfwz ▸ hxV)
  -- the residue `ρ` of `θ` along the base change, computed at its generic point
  obtain ⟨ρ, hρres, hρ0, -⟩ := hres (genericPoint P) (hTgen ▸ hfTU)
    (hTgen ▸ hfTV) 1 0 (fun _ => by simp) fun D hyD => by
      have hyD' := hyD
      rw [hTgen] at hyD'
      have hDT : T = D := eq_of_genericPoint_mem_support hyD'
      subst hDT
      rw [hτ0 _ hfTU hTB, zero_mul]
  have hρuniq : ∀ ρ' : RationalPluriForms (p₁ ≫ f ≫ sX) n' m,
      MMP.Fourfold.IsPoincareResidue (f ≫ sX) (p₁) n' m θ ρ' → ρ' = ρ := fun ρ' h' =>
    isPoincareResidue_unique (sY := f ≫ sX) (j := p₁) hTgen h' hρres
  -- the form `τ'` on `H⁰` pulling back to `ρ`
  have hdH := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := I.subschemeι ≫ sX) hn'
  obtain ⟨τ', hτ'⟩ := (pullbackRationalPluriForms_bijective (sW := I.subschemeι ≫ sX)
    (p₂)
    hbirg.functionFieldMap_bijective hdH (m : ℤ)).2 (hcond ▸ ρ)
  have hyT : ∀ w : P, p₁ w ∈ T.support := fun w => hTsupp ▸ ⟨w, rfl⟩
  have hfJ : ∀ w : P, f (p₁ w) = I.subschemeι (p₂ w) := fun w => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hηT : ∀ E : PrimeDivisor Y, E ∈ (inverseTransformDivisor f Δ).support ∪ Ex →
      p₁ (genericPoint P) ∉ E.support := fun E hE hmem => by
    rw [hTgen] at hmem
    exact hTB (eq_of_genericPoint_mem_support hmem ▸ hE)
  -- the order of `θ` near a component through a codimension-one point of the base change
  have hord1 : ∀ w : P, Order.coheight w = 1 → f (p₁ w) ∈ U₁ → f (p₁ w) ∈ V →
      ∀ D₀ ∈ (inverseTransformDivisor f Δ).support ∪ Ex, p₁ w ∈ D₀.support →
      ∀ G' : PrimeDivisor P, G'.genericPoint = w →
        G'.ordForm ρ = (⟨Y, f, hY, hbirf, D₀⟩ : DivisorOver k sX).ordPullback τ := by
    intro w hw hwU hwV D₀ hD₀ hyD₀ G' hG'
    obtain ⟨hcnt1, hcnt2⟩ := snc_at_codim_one hsnc hBD' hTD' hTB w hw (hyT w) (hker w)
    obtain ⟨π, hπI, hπord⟩ := hcnt2 D₀ hD₀ hyD₀
    have ordπ := ord_algebraMap_of_stalk_idealSheaf_eq_span hsmY hyD₀ hπI
    obtain ⟨ρw, hρwres, -, hρword⟩ := hres w hwU hwV π
      ((⟨Y, f, hY, hbirf, D₀⟩ : DivisorOver k sX).ordPullback τ)
      (fun hζ => ordπ.2 _ hζ (hηT D₀ hD₀)) fun D hyD => by
        rw [ordπ.1 D hyD]
        split_ifs with hDD₀
        · rw [hDD₀, mul_one]
        · rw [mul_zero]
          refine hτ0 D ?_ fun hDB => hDD₀ (hcnt1 D hDB D₀ hD₀ hyD hyD₀)
          exact ((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD).map
            f.continuous).mem_open U₁.isOpen hwU
    rw [hρuniq ρw hρwres] at hρword
    rw [hρword G' hG', hπord, mul_one]
  -- the generic point of `H⁰` lies on no component of `Δ`
  have hgη : (p₂) (genericPoint P) = genericPoint I.subscheme := by
    obtain ⟨w0, hw0⟩ := p₂.surjective (genericPoint I.subscheme)
    have h1 := (genericPoint_specializes w0).map (p₂).continuous
    rw [hw0] at h1
    exact (h1.antisymm (genericPoint_specializes _)).eq
  have hgenΔ : ∀ E ∈ Δ.support, I.subschemeι (genericPoint I.subscheme) ∉ E.support := by
    intro E hE hmem
    have hTex : ¬ RationalMap.IsExceptional f.toRationalMap T := fun h =>
      hTB (Finset.mem_union_right _ ((hEx T).2 h))
    obtain ⟨P, hfP, -, hPinv⟩ := exists_primeDivisor_of_not_isExceptional hX hf hY hTex
    have h1 : I.subschemeι (genericPoint I.subscheme) = P.genericPoint := by
      rw [← hgη, ← hfJ, hTgen, hfP]
    rw [h1] at hmem
    refine hTB (Finset.mem_union_left _ (hPinv ?_))
    rw [eq_of_genericPoint_mem_support hmem]; exact hE
  have : CompactSpace I.subscheme := I.subschemeι.isClosedEmbedding.compactSpace
  have : IsNoetherian I.subscheme := {}
  have hfin :
      (Function.support (DivisorWithCoeffs.restrictComponentsCoeff I.subschemeι Δ)).Finite :=
    DivisorWithCoeffs.finite_support_restrictComponentsCoeff I.subschemeι Δ fun E hE s hs => by
      have hs' : s = genericPoint I.subscheme := by
        rw [Order.coheight_eq_zero] at hs
        have h2 := hs (show s ≤ genericPoint I.subscheme from genericPoint_specializes s)
        exact ((genericPoint_specializes s).antisymm h2).eq.symm
      rw [hs']; exact hgenΔ E hE
  have hA := fun x (hx : x ∉ biregularLocus f) =>
    not_subsingleton_fiber_of_notMem_biregularLocus hX f hY.1 hbirf hx
  -- components of `Δ` through a biregular image of a point of the base change lift to `Y`
  have hlift : ∀ w : P, f (p₁ w) ∈ biregularLocus f → ∀ E ∈ Δ.support, f (p₁ w) ∈ E.support →
      ∃ DE ∈ (inverseTransformDivisor f Δ).support ∪ Ex, p₁ w ∈ DE.support ∧
        f DE.genericPoint = E.genericPoint := by
    intro w hw E hE hwE
    have hbirE : E.genericPoint ∈ biregularLocus f :=
      MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hX f hY.1 hbirf
        (by rw [ringKrullDim_stalk_eq_coheight, E.coheight_genericPoint]; rfl)
    obtain ⟨DE, hDE, hDEg⟩ := inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus f E hbirE
    refine ⟨DE, Finset.mem_union_left _ (mem_support_inverseTransformDivisor f Δ hE hDE), ?_, hDEg⟩
    have hsp := specializes_of_mem_biregularLocus f hw (a := DE.genericPoint) (by
      rw [hDEg]; exact MMP.Resolution.Aux.genericPoint_specializes_of_mem_support E hwE)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hsp
  -- orders of `τ'` are orders of the residue
  have hordτ' : ∀ (Γ' : PrimeDivisor P) (Γ : PrimeDivisor I.subscheme),
      (p₂) Γ'.genericPoint = Γ.genericPoint → Γ.ordForm τ' = Γ'.ordForm ρ := by
    intro Γ' Γ hΓ
    have hv := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hH
      ⟨_, (p₂), hY', hbirg, Γ'⟩ Γ hΓ
    rw [← DivisorOver.ordPullback_eq_ordForm_of_valuation_eq ⟨_, (p₂), hY', hbirg, Γ'⟩ Γ
      (fun g => by
        rw [hv]
        change Γ.divisorialValuation (functionFieldMap (𝟙 _) g) = _
        rw [MMP.Mori.functionFieldMap_id_apply]) τ']
    change Γ'.ordForm (pullbackRationalPluriForms _ (p₂) τ') = _
    rw [hτ', ordForm_cast]
  refine ⟨U₁ ⊓ V, ⟨hxU₁, hxV⟩, τ, hτ.mono inf_le_left, I.subschemeι ⁻¹ᵁ (U₁ ⊓ V), ⟨hxU₁, hxV⟩, τ',
    ⟨?_, ?_⟩, ?_⟩
  · intro h0
    apply cast_ne_zero hcond hρ0
    rw [← hτ', h0]
    have := pullbackRationalPluriForms_smul (sW := I.subschemeι ≫ sX) p₂
      (0 : I.subscheme.functionField)
      (0 : RationalPluriForms (I.subschemeι ≫ sX) n' m)
    rwa [zero_smul, map_zero, zero_smul] at this
  · rintro Γ ⟨p, hpΓ, hpU⟩
    have hηU : Γ.genericPoint ∈ I.subschemeι ⁻¹ᵁ (U₁ ⊓ V) :=
      (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hpΓ).mem_open
        (I.subschemeι ⁻¹ᵁ (U₁ ⊓ V)).isOpen hpU
    have hbg : Γ.genericPoint ∈ biregularLocus (p₂) :=
      MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one hH (p₂) hY'.1 hbirg
        (by rw [ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint]; rfl)
    obtain ⟨Γ', -, hΓ'⟩ := inverseTransformPrimeDivisor_eq_some_of_mem_biregularLocus (p₂) Γ hbg
    have hx : f (p₁ Γ'.genericPoint) = I.subschemeι Γ.genericPoint := by rw [hfJ, hΓ']
    have hxbir : f (p₁ Γ'.genericPoint) ∈ biregularLocus f :=
      hx ▸ (mem_biregularLocus_pullback_snd_iff f I.subschemeι hA _).1 hbg
    have hxU : f (p₁ Γ'.genericPoint) ∈ U₁ ⊓ V := hx ▸ hηU
    have hw1 : Order.coheight Γ'.genericPoint = 1 := Γ'.coheight_genericPoint
    rw [hordτ' Γ' Γ hΓ', DivisorWithCoeffs.coeff_restrictComponents I.subschemeι hfin Γ,
      Finsupp.sum]
    by_cases hex : ∃ D₀ ∈ (inverseTransformDivisor f Δ).support ∪ Ex,
      p₁ Γ'.genericPoint ∈ D₀.support
    · obtain ⟨D₀, hD₀, hyD₀⟩ := hex
      have hD₀Ex : D₀ ∉ Ex := fun hD₀Ex =>
        MMP.Positivity.support_subset_exceptionalSet D₀ ((hEx D₀).1 hD₀Ex) hyD₀ hxbir
      have hD₀ne : ¬ RationalMap.IsExceptional f.toRationalMap D₀ := fun h => hD₀Ex ((hEx D₀).2 h)
      obtain ⟨P, hfP, hPord, -⟩ := exists_primeDivisor_of_not_isExceptional hX hf hY hD₀ne
      have hxP : f (p₁ Γ'.genericPoint) ∈ P.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure]
        convert (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D₀ hyD₀).map
          f.continuous using 1
        exact hfP.symm
      have hτP := hτ.2 P ⟨_, hxP, hxU.1⟩
      rw [hord1 Γ'.genericPoint hw1 hxU.1 hxU.2 D₀ hD₀ hyD₀ Γ' rfl, hPord]
      obtain ⟨hcnt1, -⟩ := snc_at_codim_one hsnc hBD' hTD' hTB Γ'.genericPoint hw1 (hyT _)
        (hker _)
      rw [Finset.sum_eq_single P]
      · rwa [if_pos (hx ▸ hxP)]
      · intro E hE hEP
        rw [if_neg]
        intro hxE
        obtain ⟨DE, hDE, hyDE, hDEg⟩ := hlift _ hxbir E hE (hx ▸ hxE)
        exact hEP <| AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
          hDEg.symm.trans ((congrArg (fun D : PrimeDivisor Y => f D.genericPoint)
            (hcnt1 DE hDE D₀ hD₀ hyDE hyD₀)).trans hfP)
      · intro hP
        rw [if_pos (hx ▸ hxP), Finsupp.notMem_support_iff.mp hP]
    · push Not at hex
      obtain ⟨ρw, hρwres, -, hρword⟩ := hres Γ'.genericPoint hxU.1 hxU.2 1 0
        (fun _ => by simp) fun D hyD => by
          rw [zero_mul]
          exact hτ0 D (((MMP.Resolution.Aux.genericPoint_specializes_of_mem_support D hyD).map
            f.continuous).mem_open U₁.isOpen hxU.1) fun hDB => hex D hDB hyD
      rw [hρuniq ρw hρwres] at hρword
      rw [hρword Γ' rfl, zero_mul, Finset.sum_eq_zero]
      · simp
      · intro E hE
        rw [if_neg]
        intro hxE
        obtain ⟨DE, hDE, hyDE, -⟩ := hlift _ hxbir E hE (hx ▸ hxE)
        exact hex DE hDE hyDE
  · intro E hE F hF hFU
    have hyE : p₁ F.genericPoint ∈ E.support :=
      hF.prop.2 (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' F)
    have hxU : f (p₁ F.genericPoint) ∈ U₁ ⊓ V := (hfJ _) ▸ hFU
    rw [← hord1 F.genericPoint F.coheight_genericPoint hxU.1 hxU.2 E
      (Finset.mem_union_right _ hE) hyE F rfl]
    change F.ordForm ρ = F.ordForm (pullbackRationalPluriForms _ (p₂) τ')
    rw [hτ', ordForm_cast]

open Classical in
/-- **Discrepancies on a general member** (Kollár–Mori, proof of 5.17(1)). Let `(X, Δ)` be a pair
over an algebraically closed field `k` of characteristic zero with `dim X ≥ 2`,
`s : ι → H⁰(X, 𝒪_X(H))` finitely many sections without common zero, and `f : Y ⟶ X` a log
resolution of `(X, Δ)` whose `f`-exceptional prime divisors form the finite set `Ex` and such that
the reduced divisor on the components of `f⁻¹_* Δ` is smooth. Then `Y` is a normal variety and
there is a nonzero polynomial `Q` such that for every `c` with `Q(c) ≠ 0` the section
`σ = ∑ cᵢ sᵢ` is nonzero and, for every connected component `Z` of `Supp (σ)₀` with its reduced
structure `ι_Z : H⁰ ⟶ X` and `f⁰ : Y ×_X H⁰ ⟶ H⁰` the base change: `H⁰` and `Y ×_X H⁰` are
normal varieties, `f⁰` is birational, and for every `E ∈ Ex`, every prime divisor `F` of
`Y ×_X H⁰` whose support is an irreducible component of the preimage of `E`, all canonical
divisors `K` of `X` and `K'` of `H⁰` and every rational `a`, `a` is the discrepancy
`a(E, X, Δ)` if and only if it is the discrepancy `a(F, H⁰, Δ|_{H⁰})`. -/
@[mmp "lem_km5d_general_member_restricted_discrepancy"]
public theorem IsLogResolution.exists_polynomial_isDiscrepancy_restrict_connectedComponent_iff
    [IsAlgClosed k] [CharZero k] (hdim : 2 ≤ topologicalKrullDim X)
    {Δ : QDivisor X} (hΔ : IsPair sX Δ) {f : Y ⟶ X}
    (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f) (Ex : Finset (PrimeDivisor Y))
    (hEx : ∀ F : PrimeDivisor Y, F ∈ Ex ↔ RationalMap.IsExceptional f.toRationalMap F)
    (hsm : IsSmoothScheme
      ((⨅ F ∈ (inverseTransformDivisor f Δ).support, F.idealSheaf).subschemeι ≫ f ≫ sX))
    {H : Divisor X} {ι : Type*} [Fintype ι] (s : ι → H.divisorialSubmodule ⊤)
    (hs : ∀ x : X, ∃ (i : ι) (hi : s i ≠ 0), x ∉ (H.zeroDivisor (s i) hi).supp) :
    ∃ hY : IsNormalVariety k (f ≫ sX),
    ∃ Q : MvPolynomial ι k, Q ≠ 0 ∧ ∀ c : ι → k, MvPolynomial.eval c Q ≠ 0 →
      ∃ hσ : (∑ i, scalarsToGlobalSections k sX (c i) • s i) ≠ 0,
        ∀ (Z : Closeds X),
          ∀ x ∈ (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp,
          connectedComponentIn
            ((H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).supp : Set X) x =
            (Z : Set X) →
          ∃ hH : IsNormalVariety k ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX),
          ∃ hY' : IsNormalVariety k
            (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
              (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX),
          ∃ hbir : IsBirationalMorphism
            (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
            haveI := hH.1.toIsIntegral
            haveI := hH.2
            haveI := hH.1.toLocallyOfFiniteType
            haveI := LocallyOfFiniteType.isLocallyNoetherian
              ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
            ∀ E ∈ Ex,
            ∀ F : PrimeDivisor (pullback f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι),
              Maximal (fun T ↦ IsIrreducible T ∧ T ⊆
                pullback.fst f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ⁻¹'
                  E.support) F.support →
            ∀ (n n' : ℕ) (K : Divisor X)
              (K' : Divisor (Scheme.IdealSheafData.vanishingIdeal Z).subscheme),
              K.IsCanonicalDivisor sX n →
              K'.IsCanonicalDivisor ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
                n' →
            ∀ a : ℚ,
              IsDiscrepancy sX n K Δ
                  ⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, E⟩ a ↔
                IsDiscrepancy ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) n' K'
                  (Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
                  ⟨_, pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι,
                    hY', hbir, F⟩ a := by
  have hX : IsNormalVariety k sX := hΔ.isNormalVariety
  have hY : IsNormalVariety k (f ≫ sX) := isNormalVariety_of_isLogResolution hX hf
  obtain ⟨Q₁, hQ₁, h₁⟩ :=
    IsLogResolution.exists_polynomial_isSNC_pullback_zeroDivisor_add hΔ hf Ex hEx hsm s hs
  obtain ⟨Q₂, hQ₂, h₂⟩ :=
    IsLogResolution.exists_polynomial_isLogResolution_restrict_connectedComponent hdim hΔ hf Ex
      hEx hsm s hs
  obtain ⟨Q₃, hQ₃, h₃⟩ := exists_polynomial_isNormalVariety hdim hX s hs
  refine ⟨hY, Q₁ * Q₂ * Q₃, mul_ne_zero (mul_ne_zero hQ₁ hQ₂) hQ₃, fun c hc => ?_⟩
  rw [map_mul, map_mul] at hc
  have hc₁ := left_ne_zero_of_mul (left_ne_zero_of_mul hc)
  have hc₂ := right_ne_zero_of_mul (left_ne_zero_of_mul hc)
  have hc₃ := right_ne_zero_of_mul hc
  obtain ⟨hσ, hB, H', hpb, h01, hsnc, hdisj⟩ := h₁ c hc₁
  obtain ⟨hσ₂, h₂c⟩ := h₂ c hc₂
  refine ⟨hσ, fun Z x hx hZ => ?_⟩
  obtain ⟨hlog, -, -, -⟩ := h₂c Z x hx hZ
  have hH := h₃ c hc₃ hσ Z x hx hZ
  have hY' := isNormalVariety_of_isLogResolution hH hlog
  refine ⟨hH, hY', hlog.isBirationalMorphism, ?_⟩
  intro E hE F hF n n' K K' hK hK' a
  have := hH.1.toIsIntegral
  have := hH.2
  have := hH.1.toLocallyOfFiniteType
  have := LocallyOfFiniteType.isLocallyNoetherian
    ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX)
  have hD0 := Divisor.zeroDivisor_nonneg H _ hσ
  have hDc : (H.zeroDivisor (∑ i, scalarsToGlobalSections k sX (c i) • s i) hσ).IsCartier := by
    rw [Divisor.zeroDivisor_eq]
    exact (Divisor.isCartier_principalDivisor _).add (isCartier_of_forall_exists_notMem_supp s hs)
  have hKL := fun {m : ℕ} (hmC : ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor) z =>
    exists_generatesOn_ordPullback_eq hΔ hf Ex hEx hD0 hDc hB H' hpb h01 hsnc hdisj Z x hZ hY
      hH hY' hlog hK hK'.topologicalKrullDim_eq hmC z
  -- the center of `E` lies over the neighbourhood of `f⁰(η_F)`
  have hηE : f E.genericPoint ⤳ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
      (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι F.genericPoint) := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    refine Specializes.map ?_ f.continuous
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hF.1.2 (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' F)
  -- `m(K' + Δ|_{H⁰})` is Cartier as soon as `m(K + Δ)` is
  have hCart : ∀ {m : ℕ},
      ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor →
      QDivisor.IsCartierDivisor ((m : ℤ) • (Divisor.toQDivisor K' +
        Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)) :=
    fun hmC => isCartierDivisor_of_forall_generatesOn hH hK' fun z => by
      obtain ⟨-, -, -, -, U', hzU', τ', hτ', -⟩ := hKL hmC z
      exact ⟨U', hzU', τ', hτ'⟩
  -- the comparison, for a given `m`
  have key : ∀ {m : ℕ} (hm : 0 < m),
      ((m : ℤ) • (Divisor.toQDivisor K + Δ)).IsCartierDivisor →
      ∃ a₀ : ℚ, IsDiscrepancy sX n K Δ
          ⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, E⟩ a₀ ∧
        IsDiscrepancy ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ sX) n' K'
          (Δ.restrictComponents (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)
          ⟨_, pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι, hY',
            hlog.isBirationalMorphism, F⟩ a₀ := by
    intro m hm hmC
    obtain ⟨U, hzU, τ, hτ, U', hzU', τ', hτ', hord⟩ :=
      hKL hmC (pullback.snd f (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι F.genericPoint)
    have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    refine ⟨((⟨Y, f, hY, hf.toIsSmoothResolution.isBirationalMorphism, E⟩ :
      DivisorOver k sX).ordPullback τ : ℚ) / m, ⟨hX, hK, m, hm, hmC, U, hηE.mem_open U.isOpen hzU,
        τ, hτ, by field_simp⟩, ⟨hH, hK', m, hm, hCart hmC, U', hzU', τ', hτ', ?_⟩⟩
    rw [hord E hE F hF hzU']
    field_simp
  constructor
  · intro ha
    obtain ⟨-, -, m, hm, hmC, -⟩ := id ha
    obtain ⟨a₀, ha₀, ha₀'⟩ := key hm hmC
    rwa [ha.eq ha₀]
  · intro ha
    obtain ⟨-, n₀, K₀, hK₀, hQ⟩ := hΔ
    have hQ' := hQ.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK₀ hK)
    obtain ⟨m, hm, hmC⟩ := hQ'.exists_pos
    obtain ⟨a₀, ha₀, ha₀'⟩ := key hm hmC
    rwa [ha.eq ha₀']

end MMP.Mori

end
