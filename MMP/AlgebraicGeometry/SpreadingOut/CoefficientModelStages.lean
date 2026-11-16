module

public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModels
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict

/-!
# The stages of a coefficient model

Let `k₀ ⊆ K` be fields and let `X` be a finite diagram of `K`-schemes with finitely many
invertible sheaves on its vertices. A *model* of `X` over a finitely generated `k₀`-subalgebra
`R ⊆ K` is a diagram `Y` of projective `R`-schemes whose base change to `K` is `X`, with models
of the invertible sheaves. Its *stages* are its base changes to the finitely generated
subalgebras `S ⊇ R`, and a property of the stages holds *eventually* when it holds at all stages
beyond some stage. Finitely many eventual properties hold together, since the finitely generated
subalgebras of `K` form a directed set.

The file first proves a criterion for simple normal crossings through scheme-theoretic
intersections of prime divisors, then sets up the stages, their comparison morphisms and the
fibres of a stage over a field-valued point, and proves that the properties of morphisms and of
sections which hold over `K` hold eventually.

## Main definitions

* `MMP.Spreading.Model`: a model of a finite diagram over a finitely generated subalgebra.
* `MMP.Spreading.Model.stage`: the model at a later stage.
* `MMP.Spreading.Model.Eventually`: a property of the stages that holds beyond some stage.
* `MMP.Spreading.Model.stageCmp`, `MMP.Spreading.Model.cmp`, `MMP.Spreading.Model.fibreMap`:
  the comparison morphisms between stages, from `X`, and from the fibres.

## Main results

* `MMP.Spreading.isSNC_of_interIdeal`: the simple normal crossings criterion.
* `MMP.Spreading.Model.isCartesian_stage`: every stage is cartesian over the first one.
* `MMP.Spreading.Model.eventually_isRelativelyAmple`: relative ampleness holds eventually.

## References

* [EGA IV, 8.10, 9.7, 12.2]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace MMP.Spreading

noncomputable section

/-! ### Simple normal crossings through scheme-theoretic intersections -/

section SNCCriterion

/-- Along a strictly monotone map, the coheight of the image of `a` is at least the coheight of
`a` plus a lower bound for the coheights of the images of all generizations of `a`. -/
private lemma coheight_add_le_coheight_map {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : StrictMono f) (a : α) (n : ℕ) (h : ∀ b, a ≤ b → (n : ℕ∞) ≤ Order.coheight (f b)) :
    Order.coheight a + n ≤ Order.coheight (f a) := by
  have key : ∀ r : ℕ, (r : ℕ∞) ≤ Order.coheight a →
      ((r + n : ℕ) : ℕ∞) ≤ Order.coheight (f a) := by
    intro r hr
    obtain ⟨p, hp, hpl⟩ := Order.exists_series_of_le_coheight a hr
    have hab : a ≤ p.last := hp ▸ p.head_le_last
    obtain ⟨q, hq, hql⟩ := Order.exists_series_of_le_coheight (f p.last) (h _ hab)
    let p' := p.map f hf
    have hlast : p'.last = q.head := by
      rw [hq]
      rfl
    have := Order.length_le_coheight (p := RelSeries.smash p' q hlast) (x := f a)
      (by simp [RelSeries.head_smash, p', hp])
    simpa [RelSeries.smash_length, p', hpl, hql] using this
  induction h' : Order.coheight a using ENat.recTopCoe with
  | top =>
    rw [top_add]
    refine (ENat.eq_top_iff_forall_ge.mpr fun r => ?_).ge
    exact (key r (by rw [h']; exact le_top)).trans' (by exact_mod_cast Nat.le_add_right r n)
  | coe r =>
    exact_mod_cast key r (by rw [h'])

variable {k : Type u} [Field k] {V : Scheme.{u}}

/-- The ideal sheaf of the scheme-theoretic intersection of finitely many prime divisors. -/
public abbrev interIdeal (J : Finset (Mori.PrimeDivisor V)) : V.IdealSheafData :=
  J.sup fun F => F.idealSheaf

/-- The stalk of the zero ideal sheaf is the zero ideal. -/
public lemma stalk_bot (x : V) : IdealSheafData.stalk (⊥ : V.IdealSheafData) x = ⊥ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply, Ideal.map_bot]

private lemma stalk_interIdeal (J : Finset (Mori.PrimeDivisor V)) (x : V) :
    IdealSheafData.stalk (interIdeal J) x = J.sup fun F => IdealSheafData.stalk F.idealSheaf x := by
  classical
  induction J using Finset.induction_on with
  | empty => exact stalk_bot x
  | insert F J _ ih =>
    rw [interIdeal, Finset.sup_insert, IdealSheafData.stalk_sup]
    erw [ih]
    rw [Finset.sup_insert]

private lemma mem_support_interIdeal {J : Finset (Mori.PrimeDivisor V)} {x : V} :
    x ∈ (interIdeal J).support ↔ ∀ F ∈ J, x ∈ F.support := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    simp only [interIdeal, Finset.sup_empty, Scheme.IdealSheafData.support_bot,
      Finset.notMem_empty, IsEmpty.forall_iff, implies_true, iff_true]
    trivial
  | insert F J _ ih =>
    rw [interIdeal, Finset.sup_insert, Scheme.IdealSheafData.support_sup, ← SetLike.mem_coe,
      TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe]
    erw [ih]
    rw [Finset.forall_mem_insert]
    rfl

private lemma mem_support_sum_single_one (𝓕 : Finset (Mori.PrimeDivisor V))
    {F : Mori.PrimeDivisor V}
    (hF : F ∈ 𝓕) : F ∈ (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq' 𝓕 F (fun _ => (1 : ℤ)), if_pos hF]
  exact one_ne_zero

private lemma support_sum_single_one (𝓕 : Finset (Mori.PrimeDivisor V)) :
    (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ)).support = 𝓕 := by
  classical
  ext F
  refine ⟨fun hF => ?_, mem_support_sum_single_one 𝓕⟩
  by_contra hF'
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply] at hF
  simp only [Finsupp.single_apply] at hF
  rw [Finset.sum_ite_eq' 𝓕 F (fun _ => (1 : ℤ)), if_neg hF'] at hF
  exact hF rfl

/-- Over a perfect field, a closed subscheme of a scheme locally of finite type is smooth exactly
when its local rings, the quotients of the local rings of the ambient scheme by the stalks of the
ideal sheaf, are regular. -/
public lemma isSmoothScheme_subscheme_iff [PerfectField k] (sV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType sV] (I : V.IdealSheafData) :
    Mori.IsSmoothScheme (I.subschemeι ≫ sV) ↔ ∀ x ∈ (I.support : Set V),
      IsRegularLocalRing (V.presheaf.stalk x ⧸ IdealSheafData.stalk I x) := by
  have : LocallyOfFinitePresentation (I.subschemeι ≫ sV) :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  rw [Mori.isSmoothScheme_iff,
    MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  refine ⟨fun h x hx => ?_, fun h w => ?_⟩
  · obtain ⟨w, rfl⟩ : x ∈ Set.range I.subschemeι.base := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    exact IsRegularLocalRing.of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv I w).symm
  · have hw : I.subschemeι w ∈ (I.support : Set V) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    have := h _ hw
    exact IsRegularLocalRing.of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv I w)

/-- **A simple normal crossing divisor has smooth intersections of the expected codimension**:
every scheme-theoretic intersection of `r` of its components is smooth, and its points have
coheight at least `r`. -/
public lemma interIdeal_of_isSNC [PerfectField k] (sV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType sV] (𝓕 : Finset (Mori.PrimeDivisor V))
    (h : Mori.DivisorWithCoeffs.IsSNC sV (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ)))
    {J : Finset (Mori.PrimeDivisor V)} (hJ : J ⊆ 𝓕) :
    Mori.IsSmoothScheme ((interIdeal J).subschemeι ≫ sV) ∧
      ∀ x ∈ ((interIdeal J).support : Set V), (J.card : ℕ∞) ≤ Order.coheight x := by
  classical
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have key : ∀ x ∈ ((interIdeal J).support : Set V),
      IsRegularLocalRing (V.presheaf.stalk x ⧸ IdealSheafData.stalk (interIdeal J) x) ∧
        (J.card : ℕ∞) ≤ Order.coheight x := by
    intro x hx
    obtain ⟨n, z, c, hz, hc, hst⟩ := h.2 x
    have hmem : ∀ F ∈ J, F ∈ (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ)).support ∧ x ∈ F.support :=
      fun F hF => ⟨mem_support_sum_single_one 𝓕 (hJ hF), mem_support_interIdeal.mp hx F hF⟩
    let s : Finset (Fin n) := J.attach.image fun F => c ⟨F.1, hmem F.1 F.2⟩
    have hs : s.card = J.card := by
      rw [Finset.card_image_of_injective _ (fun F F' e => Subtype.ext (by
        have := congrArg Subtype.val (hc e)
        exact this)), Finset.card_attach]
    have hstalk : IdealSheafData.stalk (interIdeal J) x = Ideal.span (z '' s) := by
      rw [stalk_interIdeal]
      apply le_antisymm
      · refine Finset.sup_le fun F hF => ?_
        rw [hst ⟨F, hmem F hF⟩]
        refine Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨c ⟨F, hmem F hF⟩, ?_, rfl⟩)
        exact Finset.mem_image.mpr ⟨⟨F, hF⟩, Finset.mem_attach _ _, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨i, hi, rfl⟩
        obtain ⟨⟨F, hF⟩, -, rfl⟩ := Finset.mem_image.mp hi
        refine Finset.le_sup (f := fun F => IdealSheafData.stalk F.idealSheaf x) hF ?_
        rw [hst ⟨F, hmem F hF⟩]
        exact Ideal.subset_span rfl
    haveI : IsRegularLocalRing (V.presheaf.stalk x) :=
      Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
    obtain ⟨hreg, -, -⟩ :=
      MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz s
    refine ⟨hstalk ▸ hreg, ?_⟩
    have hdim := hz.2
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    have hsn : s.card ≤ n := (Finset.card_le_univ s).trans (by simp)
    have : Order.coheight x = n := by exact_mod_cast hdim
    rw [this, ← hs]
    exact_mod_cast hsn
  exact ⟨(isSmoothScheme_subscheme_iff sV _).mpr fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

/-- **The smooth-intersection criterion for simple normal crossings.** On a smooth integral
scheme over a perfect field, finitely many prime divisors form a simple normal crossing divisor as
soon as every scheme-theoretic intersection of `r` of them is smooth and its points have coheight
at least `r`. -/
public lemma isSNC_of_interIdeal [PerfectField k] (sV : V ⟶ Spec (.of k))
    [LocallyOfFiniteType sV] (hV : Smooth sV) (𝓕 : Finset (Mori.PrimeDivisor V))
    (H : ∀ J ⊆ 𝓕, Mori.IsSmoothScheme ((interIdeal J).subschemeι ≫ sV) ∧
      ∀ x ∈ ((interIdeal J).support : Set V), (J.card : ℕ∞) ≤ Order.coheight x) :
    Mori.DivisorWithCoeffs.IsSNC sV (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ)) := by
  classical
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  refine ⟨fun E hE => ?_, fun x => ?_⟩
  · rw [support_sum_single_one] at hE
    have := (H {E} (Finset.singleton_subset_iff.mpr hE)).1
    rwa [interIdeal, Finset.sup_singleton] at this
  have hreg : IsRegularLocalRing (V.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sV).mp hV x
  let I := 𝓕.filter fun F => x ∈ F.support
  -- local equations of the components through `x`
  have hgen : ∀ F ∈ I, ∃ g : V.presheaf.stalk x,
      IdealSheafData.stalk F.idealSheaf x = Ideal.span {g} := by
    intro F hF
    obtain ⟨q, -, hq, hqh⟩ :=
      MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support F (Finset.mem_filter.mp hF).2
    have := IsRegularLocalRing.uniqueFactorizationMonoid (V.presheaf.stalk x)
    have := IsRegularLocalRing.isDomain (V.presheaf.stalk x)
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      (p := q.asIdeal) hqh).principal
    exact ⟨g, hq.trans (hg.trans (Ideal.submodule_span_eq).symm)⟩
  choose g hg using hgen
  let e := I.equivFin
  let h : Fin I.card → V.presheaf.stalk x := fun i => g (e.symm i).1 (e.symm i).2
  have hspan : Ideal.span (Set.range h) = IdealSheafData.stalk (interIdeal I) x := by
    rw [stalk_interIdeal]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Finset.le_sup (f := fun F => IdealSheafData.stalk F.idealSheaf x) (e.symm i).2 ?_
      rw [hg _ (e.symm i).2]
      exact Ideal.subset_span rfl
    · refine Finset.sup_le fun F hF => ?_
      rw [hg F hF]
      refine Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨e ⟨F, hF⟩, ?_⟩)
      simp [h]
  have hxI : x ∈ ((interIdeal I).support : Set V) :=
    mem_support_interIdeal.mpr fun F hF => (Finset.mem_filter.mp hF).2
  have hregq : IsRegularLocalRing (V.presheaf.stalk x ⧸ Ideal.span (Set.range h)) := by
    rw [hspan]
    exact ((isSmoothScheme_subscheme_iff sV _).mp (H I (Finset.filter_subset _ _)).1) x hxI
  -- the quotient has the complementary dimension
  have hdim : ringKrullDim (V.presheaf.stalk x ⧸ Ideal.span (Set.range h)) + I.card =
      ringKrullDim (V.presheaf.stalk x) := by
    apply le_antisymm
    · obtain ⟨w, hw⟩ : x ∈ Set.range (interIdeal I).subschemeι.base := by
        rwa [Scheme.IdealSheafData.range_subschemeι]
      have hemb := (interIdeal I).subschemeι.isClosedEmbedding.isInducing
      have hle : ∀ a b, (interIdeal I).subschemeι.base a ≤ (interIdeal I).subschemeι.base b ↔
          a ≤ b := fun a b => by
        rw [Scheme.le_iff_specializes, Scheme.le_iff_specializes, hemb.specializes_iff]
      have hmono : StrictMono (interIdeal I).subschemeι.base := fun a b hab =>
        lt_iff_le_not_ge.mpr ⟨(hle a b).mpr hab.le, fun h => hab.not_ge ((hle b a).mp h)⟩
      have hc := coheight_add_le_coheight_map _ hmono w I.card fun b _ =>
        (H I (Finset.filter_subset _ _)).2 _ (by
          rw [← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨b, rfl⟩)
      rw [hspan, ← hw,
        ringKrullDim_eq_of_ringEquiv (MMP.Flips.ResolutionInputs.stalkQuotientEquiv _ w),
        ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
      exact_mod_cast hc
    · refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank
        (Ideal.span (Set.range h)) ?_).trans ?_
      · rw [IsLocalRing.ringJacobson_eq_maximalIdeal, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        have hne : IdealSheafData.stalk (e.symm i).1.idealSheaf x ≠ ⊤ := fun htop =>
          (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ x).mp htop
            (Finset.mem_filter.mp (e.symm i).2).2
        rw [hg _ (e.symm i).2] at hne
        exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
          hne (Ideal.span_singleton_eq_top.mpr hu)
      · gcongr
        have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := V.presheaf.stalk x)
          (Set.finite_range h)
        have h2 : (Set.range h).ncard ≤ I.card := by
          rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image, Set.ncard_coe_finset]
          exact Finset.card_image_le.trans (by simp)
        exact_mod_cast h1.trans h2
  obtain ⟨m, tt, hz⟩ :=
    (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff h).mp ⟨hregq, hdim⟩
  have hI : ∀ E : {E : Mori.PrimeDivisor V //
      E ∈ (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ)).support ∧ x ∈ E.support}, E.1 ∈ I := fun E =>
    Finset.mem_filter.mpr ⟨(Finset.ext_iff.mp (support_sum_single_one 𝓕) E.1).mp E.2.1, E.2.2⟩
  refine ⟨I.card + m, Fin.append h tt, fun E => Fin.castAdd m (e ⟨E.1, hI E⟩), hz, ?_, ?_⟩
  · intro E E' hEE'
    exact Subtype.ext (congrArg (fun y : I => (y : Mori.PrimeDivisor V))
      (e.injective (Fin.castAdd_injective _ _ hEE')))
  · intro E
    rw [Fin.append_left]
    simpa only [h, Equiv.symm_apply_apply] using hg _ _

/-- An irreducible set covered by two closed sets lies in one of them. -/
public lemma subset_or_subset_of_isIrreducible {X : Type*} [TopologicalSpace X] {s z₁ z₂ : Set X}
    (hs : IsIrreducible s) (h₁ : IsClosed z₁) (h₂ : IsClosed z₂) (h : s ⊆ z₁ ∪ z₂) :
    s ⊆ z₁ ∨ s ⊆ z₂ :=
  isPreirreducible_iff_isClosed_union_isClosed.mp hs.isPreirreducible _ _ h₁ h₂ h

/-- The support of a prime divisor, as an irreducible closed subset. -/
public abbrev primeIrreducibleCloseds {V : Scheme.{u}} (F : Mori.PrimeDivisor V) :
    TopologicalSpace.IrreducibleCloseds V :=
  TopologicalSpace.IrreducibleCloseds.closureSingleton F.genericPoint

/-- The irreducible closed subset of a prime divisor is its support. -/
public lemma coe_primeIrreducibleCloseds {V : Scheme.{u}} (F : Mori.PrimeDivisor V) :
    (primeIrreducibleCloseds F : Set V) = F.support :=
  (AlgebraicGeometry.PrimeDivisor.support_eq_closure F).symm

private lemma codimension_primeIrreducibleCloseds {V : Scheme.{u}} (F : Mori.PrimeDivisor V) :
    codimension (primeIrreducibleCloseds F) = 1 := by
  rw [Flips.codimension_closureSingleton, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]

private lemma le_primeIrreducibleCloseds {V : Scheme.{u}}
    {W : TopologicalSpace.IrreducibleCloseds V} {F : Mori.PrimeDivisor V}
    (hWF : (W : Set V) ⊆ F.support) : W ≤ primeIrreducibleCloseds F := by
  change (W : Set V) ⊆ (primeIrreducibleCloseds F : Set V)
  rwa [coe_primeIrreducibleCloseds]

/-- An irreducible set inside a finite union of supports of prime divisors lies in one of them. -/
private lemma exists_mem_subset_support_of_isIrreducible {V : Scheme.{u}}
    {s : Finset (Mori.PrimeDivisor V)} {W : Set V} (hW : IsIrreducible W)
    (h : W ⊆ ⋃ F ∈ s, F.support) : ∃ F ∈ s, W ⊆ F.support := by
  classical
  obtain ⟨t, ht, hWt⟩ := isIrreducible_iff_sUnion_isClosed.mp hW (s.image fun F => F.support)
    (fun t ht => by
      obtain ⟨F, -, rfl⟩ := Finset.mem_image.mp ht
      rw [← coe_primeIrreducibleCloseds]
      exact (primeIrreducibleCloseds F).isClosed)
    (fun x hx => by
      obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.mp (h hx)
      exact Set.mem_sUnion.mpr ⟨F.support, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hF), hxF⟩)
  obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨F, hF, hWt⟩

/-- An irreducible closed subset of codimension one contained in a prime divisor is its
support. -/
private lemma eq_primeIrreducibleCloseds {V : Scheme.{u}}
    {W : TopologicalSpace.IrreducibleCloseds V}
    (hW : codimension W = 1) (F : Mori.PrimeDivisor V) (hWF : (W : Set V) ⊆ F.support) :
    W = primeIrreducibleCloseds F := by
  have hle := le_primeIrreducibleCloseds hWF
  by_contra hne
  have hlt := lt_of_le_of_ne hle hne
  have := Order.coheight_add_one_le hlt
  rw [← codimension_eq_coheight, ← codimension_eq_coheight,
    codimension_primeIrreducibleCloseds, hW] at this
  exact absurd this (by norm_num)

/-- A finite union of supports of prime divisors is of pure codimension one. -/
private lemma isPureCodimOne_of_eq_biUnion {V : Scheme.{u}} {T : TopologicalSpace.Closeds V}
    (s : Finset (Mori.PrimeDivisor V)) (hT : (T : Set V) = ⋃ F ∈ s, F.support) :
    Mori.IsPureCodimOne T := by
  classical
  intro W hW
  obtain ⟨F, hFs, hWF⟩ := exists_mem_subset_support_of_isIrreducible W.isIrreducible
    (hT ▸ hW.prop : (W : Set V) ⊆ ⋃ F ∈ s, F.support)
  have hFT : ((primeIrreducibleCloseds F : TopologicalSpace.IrreducibleCloseds V) : Set V) ⊆ T := by
    rw [coe_primeIrreducibleCloseds, hT]
    exact Set.subset_biUnion_of_mem (u := fun F => F.support) hFs
  have hle := le_primeIrreducibleCloseds hWF
  rw [← hW.eq_of_ge hFT hle]
  exact codimension_primeIrreducibleCloseds F

open Classical in
/-- A closed subset of pure codimension one contained in a finite union of supports of prime
divisors is the union of those contained in it. -/
public lemma subset_biUnion_of_isPureCodimOne {V : Scheme.{u}} [QuasiSober V]
    {T : TopologicalSpace.Closeds V} (hT : Mori.IsPureCodimOne T)
    (s : Finset (Mori.PrimeDivisor V)) (hTs : (T : Set V) ⊆ ⋃ F ∈ s, F.support) :
    (T : Set V) ⊆ ⋃ F ∈ s.filter (fun F => F.support ⊆ (T : Set V)), F.support := by
  classical
  intro x hx
  obtain ⟨W₀, hW₀, hxW₀⟩ := MMP.Resolution.exists_mem_componentsOf hx
  have hW₀' : Maximal (fun W' : Set V => IsIrreducible W' ∧ W' ⊆ T) W₀ := hW₀
  have hcl : closure W₀ = W₀ := by
    refine hW₀'.eq_of_ge ⟨hW₀'.prop.1.closure, ?_⟩ subset_closure
    exact closure_minimal hW₀'.prop.2 T.isClosed
  let W : TopologicalSpace.IrreducibleCloseds V :=
    ⟨W₀, hW₀'.prop.1, hcl ▸ isClosed_closure⟩
  have hWmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds V => (W' : Set V) ⊆ T) W :=
    ⟨hW₀'.prop.2, fun W' hW' hle => hW₀'.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hcodim := hT W hWmax
  obtain ⟨F, hFs, hWF⟩ :=
    exists_mem_subset_support_of_isIrreducible W.isIrreducible (hWmax.prop.trans hTs)
  have hWeq := eq_primeIrreducibleCloseds hcodim F hWF
  have hFT : F.support ⊆ T := by
    rw [← coe_primeIrreducibleCloseds, ← hWeq]
    exact hWmax.prop
  refine Set.mem_iUnion₂.mpr ⟨F, Finset.mem_filter.mpr ⟨hFs, hFT⟩, ?_⟩
  rw [← coe_primeIrreducibleCloseds, ← hWeq]
  exact hxW₀

/-- **A log resolution from its exceptional components.** A proper birational projective morphism
`f : W ⟶ Z` from a smooth scheme is a log resolution along a closed subset `C` of `Z` as soon as
its exceptional set is the union of finitely many prime divisors and `Ex(f) ∪ f⁻¹(C)` is the
union of the components of a simple normal crossing divisor. -/
public lemma isLogResolutionAlong_of_cover {k : Type u} [Field k] {W Z : Scheme.{u}}
    (sZ : Z ⟶ Spec (.of k)) (C : TopologicalSpace.Closeds Z) (f : W ⟶ Z) [IsProper f]
    (hbir : Mori.IsBirationalMorphism f) (hsm : Smooth (f ≫ sZ))
    (hproj : IsProjectiveMorphism f) (𝓕 𝓕ex : Finset (Mori.PrimeDivisor W))
    (hex : (Mori.exceptionalSet f : Set W) = ⋃ F ∈ 𝓕ex, F.support)
    (hcov : (Mori.exceptionalSet f : Set W) ∪ f.base ⁻¹' C = ⋃ F ∈ 𝓕, F.support)
    (hsnc : Mori.DivisorWithCoeffs.IsSNC (f ≫ sZ) (∑ F ∈ 𝓕, Finsupp.single F (1 : ℤ))) :
    IsLogResolutionAlong sZ C f := by
  have : LocallyOfFinitePresentation (f ≫ sZ) := @instLocallyOfFinitePresentationOfSmooth _ _ _ hsm
  refine ⟨⟨inferInstance, hbir, (Mori.isSmoothScheme_iff _).mpr hsm⟩,
    isPureCodimOne_of_eq_biUnion 𝓕ex hex, Or.inr ⟨𝓕, ?_, hsnc⟩, hproj⟩
  rw [← hcov]
  rfl

end SNCCriterion

/-! ### Models and stages -/

section Stages

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]

/-- The point `Spec K ⟶ Spec R` of a subalgebra `R ⊆ K`. -/
public abbrev κ (R : Subalgebra k₀ K) : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The transition morphism `Spec S ⟶ Spec R` for subalgebras `R ≤ S`. -/
public abbrev π {R S : Subalgebra k₀ K} (h : R ≤ S) : Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

/-- The point `Spec K ⟶ Spec R` factors through the transition morphism from a larger
subalgebra. -/
public lemma κ_π {R S : Subalgebra k₀ K} (h : R ≤ S) : κ S ≫ π h = κ R := by
  rw [← Spec.map_comp]
  rfl

/-- The transition morphisms between the spectra of subalgebras compose. -/
public lemma π_π {R S T : Subalgebra k₀ K} (h : R ≤ S) (h' : S ≤ T) :
    π h' ≫ π h = π (h.trans h') := by
  rw [← Spec.map_comp]
  rfl

/-- **Open immersions descend to a stage** (Stacks 0EUU): a morphism over a stage `S₀` whose base
change to `K` is an open immersion has open immersions as base changes to all late stages. -/
public lemma exists_stage_isOpenImmersion (S₀ : CoefficientModels.FGSub k₀ K)
    {A B : Over (Spec (.of S₀.1))} (f : A ⟶ B) [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] [LocallyOfFinitePresentation f.left]
    (hf : IsOpenImmersion ((Over.pullback (κ S₀.1)).map f).left) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₁ ≤ S), IsOpenImmersion
        ((Over.pullback (π (show S₀.1 ≤ S.1 from h₁.trans h))).map f).left := by
  obtain ⟨i, g, hg⟩ := @exists_isOpenImmersion_pullback _ _ _ (CoefficientModels.specDiagram k₀ K)
    (CoefficientModels.specCone k₀ K) (CoefficientModels.isLimitSpecCone k₀ K) _
    (Opposite.op S₀) _ _ A B ‹_› ‹_› ‹_› ‹_› f ‹_› hf
  refine ⟨i.unop, leOfHom g.unop, fun S h => ?_⟩
  have := overPullback_map_comp (@IsOpenImmersion) (π (show S₀.1 ≤ i.unop.1 from leOfHom g.unop))
    (π (show i.unop.1 ≤ S.1 from h)) f hg
  rwa [π_π] at this

/-- **Isomorphisms descend to a stage**: a morphism over a stage `S₀` whose base change to `K` is
an isomorphism has isomorphisms as base changes to all late stages. -/
public lemma exists_stage_isIso (S₀ : CoefficientModels.FGSub k₀ K)
    {A B : Over (Spec (.of S₀.1))} (f : A ⟶ B) [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] [LocallyOfFinitePresentation f.left]
    (hf : IsIso ((Over.pullback (κ S₀.1)).map f).left) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₁ ≤ S), IsIso
        ((Over.pullback (π (show S₀.1 ≤ S.1 from h₁.trans h))).map f).left := by
  obtain ⟨i, g, hg⟩ := @exists_isIso_baseChange_of_isIso_limitBaseChange _ _ _ _
    (CoefficientModels.specDiagram k₀ K) _ (CoefficientModels.specCone k₀ K)
    (CoefficientModels.isLimitSpecCone k₀ K) (Opposite.op S₀) A B f _ _ ‹_› ‹_› ‹_› ‹_› ‹_› hf
  refine ⟨i.unop, leOfHom g.unop, fun S h => ?_⟩
  have := overPullback_map_comp (MorphismProperty.isomorphisms Scheme.{u})
    (π (show S₀.1 ≤ i.unop.1 from leOfHom g.unop)) (π (show i.unop.1 ≤ S.1 from h)) f hg
  rwa [π_π] at this

/-- The fields of the field-valued points of a stage have characteristic zero. -/
public lemma charZero_of_point [CharZero k₀] {S : CoefficientModels.FGSub k₀ K} {L : Type u}
    [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) : CharZero L :=
  charZero_of_injective_ringHom
    ((Spec.preimage t).hom.comp (algebraMap k₀ S.1)).injective

/-- **Inverting one nonzero element**: past the stage `S₀[1/r]`, every point of a stage lies
over a point of `Spec S₀` outside the zero set of `r`. -/
public lemma exists_le_forall_notMem_asIdeal (S₀ : CoefficientModels.FGSub k₀ K) (r : S₀.1)
    (hr : r ≠ 0) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (y : Spec (.of S.1)),
      r ∉ ((π (show S₀.1 ≤ S.1 from h₂.trans h)).base y).asIdeal := by
  have hr0 : (r : K) ≠ 0 := fun h0 => hr (Subtype.ext h0)
  let S₂ : CoefficientModels.FGSub k₀ K := ⟨S₀.1 ⊔ Algebra.adjoin k₀ {(r : K)⁻¹},
    S₀.2.sup (by simpa using Subalgebra.fg_adjoin_finset (R := k₀) {(r : K)⁻¹})⟩
  refine ⟨S₂, le_sup_left (a := S₀.1), fun S h y hmem => ?_⟩
  have hunit : IsUnit (Subalgebra.inclusion (show S₀.1 ≤ S.1 from
      (le_sup_left (a := S₀.1)).trans h) r) := by
    refine IsUnit.of_mul_eq_one (b := ⟨(r : K)⁻¹, (le_sup_right (b := Algebra.adjoin k₀
      {(r : K)⁻¹})).trans (show S₂.1 ≤ S.1 from h) (Algebra.subset_adjoin rfl)⟩) ?_
    apply Subtype.ext
    simp [hr0]
  exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)

/-- `exists_le_forall_notMem_asIdeal` for the field-valued points of the stages. -/
public lemma exists_le_forall_notMem (S₀ : CoefficientModels.FGSub k₀ K) (r : S₀.1)
    (hr : r ≠ 0) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      r ∉ ((t ≫ π (show S₀.1 ≤ S.1 from h₂.trans h)).base
        (IsLocalRing.closedPoint L)).asIdeal := by
  obtain ⟨S₂, h₂, H⟩ := exists_le_forall_notMem_asIdeal S₀ r hr
  exact ⟨S₂, h₂, fun S h L _ t => H S h _⟩

variable {J : Type u} [SmallCategory J]

/-- A model of the diagram `X` and of the sheaves `𝓛` over a finitely generated subalgebra. -/
public structure Model (k₀ : Type u) [Field k₀] [Algebra k₀ K] (X : J ⥤ Over (Spec (.of K)))
    {ι : Type u} (v : ι → J)
    (𝓛 : ∀ i, (X.obj (v i)).left.Modules) where
  /-- The finitely generated subalgebra `R ⊆ K` over which the model is defined. -/
  R : CoefficientModels.FGSub k₀ K
  /-- The diagram of schemes over `Spec R`. -/
  Y : J ⥤ Over (Spec (.of R.1))
  /-- The comparison morphisms from `X` to the model. -/
  p : ∀ j, (X.obj j).left ⟶ (Y.obj j).left
  /-- The diagram `X` is the base change of `Y` along `Spec K ⟶ Spec R`. -/
  cart : IsCartesian (κ R.1) X Y p
  /-- The model sheaves on the schemes of `Y`. -/
  N : ∀ i, (Y.obj (v i)).left.Modules
  /-- The pullback of each model sheaf is isomorphic to the corresponding sheaf of `𝓛`. -/
  θ : ∀ i, (Scheme.Modules.pullback (p (v i))).obj (N i) ≅ 𝓛 i
  /-- Each model sheaf is invertible. -/
  invertible : ∀ i, Stacks.Ample.IsInvertibleModule _ (N i)
  /-- Each scheme of `Y` is of finite presentation over `Spec R`. -/
  fp : ∀ j, FinitePresentation (Y.obj j).hom
  /-- Each scheme of `Y` is projective over `Spec R`. -/
  hproj : ∀ j, IsProjectiveMorphism (Y.obj j).hom

variable {X : J ⥤ Over (Spec (.of K))} {ι : Type u} {v : ι → J}
  {𝓛 : ∀ i, (X.obj (v i)).left.Modules} (M : Model k₀ X v 𝓛)

/-- The model at a later stage `S`, the base change of the model at `M.R`. -/
public abbrev Model.stage {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) :
    J ⥤ Over (Spec (.of S.1)) :=
  M.Y ⋙ Over.pullback (π (show M.R.1 ≤ S.1 from h))

/-- The model sheaves at a later stage. -/
public abbrev Model.stageN {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) (i : ι) :
    ((M.stage h).obj (v i)).left.Modules :=
  (Scheme.Modules.pullback (pullback.fst (M.Y.obj (v i)).hom
    (π (show M.R.1 ≤ S.1 from h)))).obj (M.N i)

/-- The model of a specified sheaf at a later stage is invertible. -/
public lemma Model.stageN_invertible {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) (i : ι) :
    Stacks.Ample.IsInvertibleModule _ (M.stageN h i) :=
  haveI := M.invertible i
  MMP.Fourfold.isInvertibleModule_pullback _ _

/-- A property of the stages holds from some stage on. -/
@[expose] public def Model.Eventually (P : ∀ S : CoefficientModels.FGSub k₀ K, M.R ≤ S → Prop) :
    Prop :=
  ∃ S₀ : CoefficientModels.FGSub k₀ K, ∃ h₀ : M.R ≤ S₀, ∀ S (h : S₀ ≤ S), P S (h₀.trans h)

variable {M} in
/-- Two properties that hold eventually hold together eventually. -/
public lemma Model.Eventually.and {P Q : ∀ S : CoefficientModels.FGSub k₀ K, M.R ≤ S → Prop}
    (hP : M.Eventually P) (hQ : M.Eventually Q) :
    M.Eventually (fun S h => P S h ∧ Q S h) := by
  obtain ⟨S₁, h₁, H₁⟩ := hP
  obtain ⟨S₂, h₂, H₂⟩ := hQ
  refine ⟨⟨S₁.1 ⊔ S₂.1, S₁.2.sup S₂.2⟩, h₁.trans (le_sup_left (a := S₁.1)), fun S h => ?_⟩
  exact ⟨H₁ S ((le_sup_left (a := S₁.1)).trans h),
    H₂ S ((le_sup_right (b := S₂.1)).trans h)⟩

variable {M} in
/-- Finitely many properties of the stages, each holding from some stage on, hold together from
some stage on. -/
public lemma Model.Eventually.forall {α : Type*} [Finite α]
    {P : α → ∀ S : CoefficientModels.FGSub k₀ K, M.R ≤ S → Prop}
    (hP : ∀ a, M.Eventually (P a)) : M.Eventually fun S h => ∀ a, P a S h := by
  classical
  have : Fintype α := Fintype.ofFinite α
  choose S₀ h₀ H using hP
  obtain ⟨T, hT⟩ := Finset.exists_le (insert M.R (Finset.univ.image S₀))
  refine ⟨T, hT _ (Finset.mem_insert_self _ _), fun S h a => ?_⟩
  exact H a S ((hT _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ a)))).trans h)

variable {M} in
/-- A property implied by one that holds eventually holds eventually. -/
public lemma Model.Eventually.mono {P Q : ∀ S : CoefficientModels.FGSub k₀ K, M.R ≤ S → Prop}
    (hP : M.Eventually P) (hPQ : ∀ S h, P S h → Q S h) : M.Eventually Q := by
  obtain ⟨S₀, h₀, H⟩ := hP
  exact ⟨S₀, h₀, fun S h => hPQ _ _ (H S h)⟩

/-- The true property holds eventually. -/
public lemma Model.eventually_true : M.Eventually fun _ _ => True :=
    ⟨M.R, le_rfl, fun _ _ => trivial⟩

/-- A property of morphisms stable under base change, holding at one stage, holds at every later
stage. -/
public lemma Model.eventually_of_exists (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {A B : Over (Spec (.of M.R.1))} (f : A ⟶ B)
    (h : ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      P ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left) :
    M.Eventually fun S h => P ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left := by
  obtain ⟨S₀, h₀, H⟩ := h
  refine ⟨S₀, h₀, fun S h => ?_⟩
  have := overPullback_map_comp P (π (show M.R.1 ≤ S₀.1 from h₀))
    (π (show S₀.1 ≤ S.1 from h)) f H
  rwa [π_π] at this

/-- The limit form of a stage: a stage of the cofiltered system of spectra is a subalgebra
containing `M.R`. -/
private lemma Model.exists_of_limit {Q : ∀ S : CoefficientModels.FGSub k₀ K, M.R ≤ S → Prop}
    (h : ∃ (i : (CoefficientModels.FGSub k₀ K)ᵒᵖ) (g : i ⟶ Opposite.op M.R),
      Q i.unop (leOfHom g.unop)) :
    ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S), Q S h := by
  obtain ⟨i, g, hg⟩ := h
  exact ⟨i.unop, leOfHom g.unop, hg⟩

/-- A property of morphisms respecting isomorphisms holds for `X.map g` if and only if it holds
for the base change to `K` of the model morphism `M.Y.map g`. -/
private lemma Model.prop_map_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {j j' : J}
    (g : j ⟶ j') :
    P (X.map g).left ↔ P ((Over.pullback (κ M.R.1)).map (M.Y.map g)).left :=
  MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk ((Over.forget _).mapIso (M.cart.iso.app j))
    ((Over.forget _).mapIso (M.cart.iso.app j')) (by
      have := congrArg (fun z => z.left) (M.cart.iso.hom.naturality g)
      simp only [Over.comp_left] at this
      exact this.symm))

/-- The structure morphism of an object of an overcategory, as a morphism to the terminal
object. -/
public abbrev toTerminal {S : Scheme.{u}} (Z : Over S) : Z ⟶ Over.mk (𝟙 S) := Over.homMk Z.hom

/-- A property of morphisms holds for the base change of the map to the terminal object over `S` if
and only if it holds for the structure morphism of the base change. -/
public lemma prop_overPullback_toTerminal_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {S T : Scheme.{u}} (b : T ⟶ S) (Z : Over S) :
    P ((Over.pullback b).map (toTerminal Z)).left ↔ P ((Over.pullback b).obj Z).hom := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (P := P) _ (pullback.snd (𝟙 S) b)]
  simp only [Over.pullback_map_left, Over.pullback_obj_hom, Over.homMk_left,
    Over.mk_hom, pullback.lift_snd]

/-- **Smoothness descends to a stage**: a scheme over a stage `S₀` whose base change to `K` is
smooth has smooth base changes to all late stages. -/
public lemma exists_stage_smooth (S₀ : CoefficientModels.FGSub k₀ K) (A : Over (Spec (.of S₀.1)))
    [CompactSpace A.left] [QuasiSeparatedSpace A.left] [LocallyOfFinitePresentation A.hom]
    (hA : Smooth ((Over.pullback (κ S₀.1)).obj A).hom) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₁ ≤ S), Smooth ((Over.pullback (π (show S₀.1 ≤ S.1 from h₁.trans h))).obj A).hom := by
  have : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let B : Over (Spec (.of S₀.1)) := Over.mk (𝟙 (Spec (.of S₀.1)))
  have : CompactSpace B.left := inferInstanceAs (CompactSpace (Spec _))
  have : QuasiSeparatedSpace B.left := inferInstanceAs (QuasiSeparatedSpace (Spec _))
  have : LocallyOfFinitePresentation (toTerminal A).left :=
    inferInstanceAs (LocallyOfFinitePresentation A.hom)
  have hf : Smooth ((Over.pullback (κ S₀.1)).map (toTerminal A)).left :=
    (prop_overPullback_toTerminal_iff @Smooth _ A).mpr hA
  obtain ⟨i, g, hg⟩ := @exists_smooth_baseChange_of_smooth_limitBaseChange _ _
    (CoefficientModels.specDiagram k₀ K) (CoefficientModels.specCone k₀ K) (Opposite.op S₀) A B
    (toTerminal A) _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› (CoefficientModels.isLimitSpecCone k₀ K) hf
  refine ⟨i.unop, leOfHom g.unop, fun S h => ?_⟩
  have := overPullback_map_comp @Smooth (π (show S₀.1 ≤ i.unop.1 from leOfHom g.unop))
    (π (show i.unop.1 ≤ S.1 from h)) (toTerminal A) hg
  rw [π_π] at this
  exact (prop_overPullback_toTerminal_iff @Smooth _ A).mp this

/-- A property of morphisms respecting isomorphisms holds for the structure morphism of `X.obj j`
if and only if it holds for the base change to `K` of the model vertex's map to the terminal
object. -/
public lemma Model.prop_obj_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (j : J) :
    P (X.obj j).hom ↔ P ((Over.pullback (κ M.R.1)).map (toTerminal (M.Y.obj j))).left := by
  refine Iff.trans ?_ (prop_overPullback_toTerminal_iff P _ _).symm
  exact MorphismProperty.arrow_mk_iso_iff P (Arrow.isoMk ((Over.forget _).mapIso
    (M.cart.iso.app j)) (Iso.refl _) (by
      simpa using Over.w (M.cart.iso.hom.app j)))

/-! #### Finiteness of the model -/

/-- Every vertex of the model is quasi-compact. -/
public lemma Model.compactSpace (j : J) : CompactSpace (M.Y.obj j).left :=
  have := (M.fp j).2.1
  QuasiCompact.compactSpace_of_compactSpace (M.Y.obj j).hom

/-- Every vertex of the model is quasi-separated. -/
public lemma Model.quasiSeparatedSpace (j : J) : QuasiSeparatedSpace (M.Y.obj j).left :=
  have := (M.fp j).2.2
  (quasiSeparated_iff_quasiSeparatedSpace (M.Y.obj j).hom).mp inferInstance

/-- Every vertex of the model is locally Noetherian. -/
public lemma Model.isLocallyNoetherian (j : J) : IsLocallyNoetherian (M.Y.obj j).left :=
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K M.R
  have := (M.fp j).1
  LocallyOfFiniteType.isLocallyNoetherian (M.Y.obj j).hom

/-- Every morphism of the model diagram is locally of finite presentation. -/
public lemma Model.locallyOfFinitePresentation_map {j j' : J} (g : j ⟶ j') :
    LocallyOfFinitePresentation (M.Y.map g).left :=
  have := M.isLocallyNoetherian j'
  have := (M.fp j).1
  have : LocallyOfFiniteType ((M.Y.map g).left ≫ (M.Y.obj j').hom) := by
    rw [Over.w]; infer_instance
  LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr
    (LocallyOfFiniteType.of_comp (f := (M.Y.map g).left) (g := (M.Y.obj j').hom) this)

/-- The structure morphism of every vertex of the model is locally of finite presentation. -/
public lemma Model.locallyOfFinitePresentation_toTerminal (j : J) :
    LocallyOfFinitePresentation (toTerminal (M.Y.obj j)).left :=
  (M.fp j).1

include M in
/-- The vertices over `K` are locally of finite type. -/
public lemma Model.locallyOfFiniteType_obj (j : J) : LocallyOfFiniteType (X.obj j).hom :=
  have := (M.fp j).1
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (M.cart.isPullback j) inferInstance

/-! #### Limit descent of properties of morphisms to a stage -/

section LimitDescent

variable {A B : Over (Spec (.of M.R.1))} (f : A ⟶ B) [CompactSpace A.left]
  [QuasiSeparatedSpace A.left] [CompactSpace B.left] [QuasiSeparatedSpace B.left]

/-- A morphism of the model that is smooth over `K` is smooth at some stage. -/
public lemma Model.exists_smooth [LocallyOfFinitePresentation f.left]
    (hf : Smooth ((Over.pullback (κ M.R.1)).map f).left) :
    ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      Smooth ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left :=
  M.exists_of_limit (Q := fun S h => Smooth ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map
    f).left) (@exists_smooth_baseChange_of_smooth_limitBaseChange _ _
    (CoefficientModels.specDiagram k₀ K) (CoefficientModels.specCone k₀ K) (Opposite.op M.R) A B f
    _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› (CoefficientModels.isLimitSpecCone k₀ K) hf)

/-- A morphism of the model that is flat over `K` is flat at some stage. -/
public lemma Model.exists_flat [LocallyOfFinitePresentation f.left]
    (hf : Flat ((Over.pullback (κ M.R.1)).map f).left) :
    ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      Flat ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left :=
  M.exists_of_limit (Q := fun S h => Flat ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map
    f).left) (@exists_flat_baseChange_of_limitBaseChange _ _ _
    (CoefficientModels.specDiagram k₀ K) (CoefficientModels.specCone k₀ K) (Opposite.op M.R) A B f
    _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› (CoefficientModels.isLimitSpecCone k₀ K) hf)

/-- A morphism of the model that is an isomorphism over `K` is an isomorphism at some stage. -/
public lemma Model.exists_isIso [LocallyOfFinitePresentation f.left]
    (hf : IsIso ((Over.pullback (κ M.R.1)).map f).left) :
    ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      IsIso ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left :=
  M.exists_of_limit (Q := fun S h => IsIso ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map
    f).left) (@exists_isIso_baseChange_of_isIso_limitBaseChange _ _ _ _
    (CoefficientModels.specDiagram k₀ K) _ (CoefficientModels.specCone k₀ K)
    (CoefficientModels.isLimitSpecCone k₀ K) (Opposite.op M.R) A B f
    _ _ ‹_› ‹_› ‹_› ‹_› ‹_› hf)

/-- A morphism of the model that is surjective over `K` is surjective at some stage. -/
public lemma Model.exists_surjective [LocallyOfFinitePresentation f.left]
    (hf : Surjective ((Over.pullback (κ M.R.1)).map f).left) :
    ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      Surjective ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left :=
  M.exists_of_limit (Q := fun S h => Surjective ((Over.pullback (π (show M.R.1 ≤ S.1 from
    h))).map f).left) (@exists_surjective_baseChange_of_surjective_limitBaseChange _ _ _
    (CoefficientModels.specDiagram k₀ K) _ (CoefficientModels.specCone k₀ K)
    (CoefficientModels.isLimitSpecCone k₀ K) (Opposite.op M.R) A B f
    _ _ ‹_› ‹_› ‹_› ‹_› ‹_› hf)

/-- A morphism of the model that is a closed immersion over `K` is a closed immersion at some
stage. -/
public lemma Model.exists_isClosedImmersion [LocallyOfFiniteType f.left]
    (hf : IsClosedImmersion ((Over.pullback (κ M.R.1)).map f).left) :
    ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      IsClosedImmersion ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map f).left :=
  M.exists_of_limit (Q := fun S h => IsClosedImmersion ((Over.pullback (π (show M.R.1 ≤ S.1
    from h))).map f).left) (@exists_isClosedImmersion_baseChange_of_isLimit _ _ _ _
    (CoefficientModels.specDiagram k₀ K) _ (CoefficientModels.specCone k₀ K)
    (CoefficientModels.isLimitSpecCone k₀ K) (Opposite.op M.R) A B f
    _ _ ‹_› ‹_› ‹_› ‹_› ‹_› hf)

end LimitDescent

/-- A property of a morphism over `K`, stable under base change and descending to a stage, holds
for its model from some stage on. -/
public lemma Model.eventually_map (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {j j' : J} (g : j ⟶ j')
    (hex : P ((Over.pullback (κ M.R.1)).map (M.Y.map g)).left →
      ∃ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
        P ((Over.pullback (π (show M.R.1 ≤ S.1 from h))).map (M.Y.map g)).left) :
    M.Eventually fun S h => P (X.map g).left → P ((M.stage h).map g).left := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  by_cases hg : P (X.map g).left
  · exact (M.eventually_of_exists P (M.Y.map g) (hex ((M.prop_map_iff P g).mp hg))).mono
      fun _ _ h _ => h
  · exact M.eventually_true.mono fun _ _ _ h => absurd h hg

/-- The model of every specified sheaf is of finite presentation. -/
public lemma Model.isFinitePresentation_N (i : ι) : (M.N i).IsFinitePresentation :=
  have := M.isLocallyNoetherian (v i)
  have := M.invertible i
  have := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ (M.N i)
  isFinitePresentation_of_isCoherent (M.N i)

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- An isomorphism over `K` between the pullbacks of two modules of finite presentation on a
vertex of the model gives isomorphisms between their pullbacks to all late stages. -/
public lemma Model.eventually_iso (j : J) (A B : (M.Y.obj j).left.Modules)
    [A.IsFinitePresentation] [B.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (M.p j)).obj A ≅ (Scheme.Modules.pullback (M.p j)).obj B) :
    M.Eventually fun S h =>
      Nonempty ((Scheme.Modules.pullback (pullback.fst (M.Y.obj j).hom
          (π (show M.R.1 ≤ S.1 from h)))).obj A ≅
        (Scheme.Modules.pullback (pullback.fst (M.Y.obj j).hom
          (π (show M.R.1 ≤ S.1 from h)))).obj B) := by
  let D := CoefficientModels.specDiagram k₀ K
  let W : Over (D.obj (Opposite.op M.R)) := M.Y.obj j
  have hpb : IsPullback (M.p j) (X.obj j).hom W.hom
      ((CoefficientModels.specCone k₀ K).π.app (Opposite.op M.R)) := M.cart.isPullback j
  have hW : FinitePresentation W.hom := M.fp j
  have : ∀ {a b : Over (Opposite.op M.R)} (f : a ⟶ b),
      IsAffineHom ((CoefficientModels.stageDiagram D W).map f) := fun f =>
    CoefficientModels.isAffineHom_stageMap D W f
  have : ∀ a, CompactSpace ((CoefficientModels.stageDiagram D W).obj a) := fun a =>
    CoefficientModels.compactSpace_stageObj D W hW a
  have : ∀ a, QuasiSeparatedSpace ((CoefficientModels.stageDiagram D W).obj a) := fun a =>
    CoefficientModels.quasiSeparatedSpace_stageObj D W hW a
  let i : Over (Opposite.op M.R) := Over.mk (𝟙 _)
  let s := pullback.snd (D.map i.hom) W.hom
  have hsA := isFinitePresentation_pullback s A
  have hsB := isFinitePresentation_pullback s B
  let c' := CoefficientModels.legCone D W (CoefficientModels.specCone k₀ K) (X.obj j) (M.p j) hpb
  have hl : c'.π.app i ≫ s = M.p j := CoefficientModels.leg_snd D W _ _ _ hpb i
  obtain ⟨k, e, ⟨ψ⟩⟩ := exists_iso_of_isLimit (CoefficientModels.stageDiagram D W) c'
    (CoefficientModels.isLimitLegCone D W _ _ _ hpb (CoefficientModels.isLimitSpecCone k₀ K)) i
    ((Scheme.Modules.pullback s).obj A) ((Scheme.Modules.pullback s).obj B) hsA hsB
    (canIso _ s _ hl A ≪≫ φ ≪≫ (canIso _ s _ hl B).symm)
  have hk : M.R ≤ k.left.unop := leOfHom k.hom.unop
  refine ⟨k.left.unop, hk, fun S h => ?_⟩
  let m : Over (Opposite.op M.R) := Over.mk (homOfLE (hk.trans h)).op
  let b : m ⟶ k := Over.homMk (homOfLE h).op (Subsingleton.elim _ _)
  let σ : pullback (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from hk.trans h)) ≅
      CoefficientModels.stageObj D W m := pullbackSymmetry _ _
  have hσ : σ.hom ≫ pullback.snd (D.map m.hom) W.hom = pullback.fst _ _ :=
    pullbackSymmetry_hom_comp_snd _ _
  have hs : CoefficientModels.stageMap D W (b ≫ e) ≫ s = pullback.snd (D.map m.hom) W.hom :=
    CoefficientModels.stageMap_snd D W (b ≫ e)
  have hbe : CoefficientModels.stageMap D W b ≫ CoefficientModels.stageMap D W e =
      CoefficientModels.stageMap D W (b ≫ e) := (CoefficientModels.stageMap_comp D W b e).symm
  let ψ' : (Scheme.Modules.pullback (CoefficientModels.stageMap D W (b ≫ e))).obj
        ((Scheme.Modules.pullback s).obj A) ≅
      (Scheme.Modules.pullback (CoefficientModels.stageMap D W (b ≫ e))).obj
        ((Scheme.Modules.pullback s).obj B) :=
    (canIso _ _ _ hbe _).symm ≪≫
      (Scheme.Modules.pullback (CoefficientModels.stageMap D W b)).mapIso ψ ≪≫ canIso _ _ _ hbe _
  exact ⟨(canIso σ.hom _ _ hσ A).symm ≪≫ (Scheme.Modules.pullback σ.hom).mapIso
    ((canIso _ s _ hs A).symm ≪≫ ψ' ≪≫ canIso _ s _ hs B) ≪≫ canIso σ.hom _ _ hσ B⟩

/-- A later stage of the model is affine over every stage `k` of the system of base changes of
`W` that it lies over, compatibly with both projections. -/
private lemma Model.exists_stage_τ
    (W : Over ((CoefficientModels.specDiagram k₀ K).obj (Opposite.op M.R)))
    (k : Over (Opposite.op M.R)) (S : CoefficientModels.FGSub k₀ K) (h : k.left.unop ≤ S) :
    ∃ τ : pullback W.hom (π (show M.R.1 ≤ S.1 from (leOfHom k.hom.unop).trans h)) ⟶
        CoefficientModels.stageObj (CoefficientModels.specDiagram k₀ K) W k,
      IsAffineHom τ ∧ τ ≫ pullback.snd _ _ = pullback.fst _ _ ∧
        τ ≫ pullback.fst _ _ = pullback.snd _ _ ≫ π (show k.left.unop.1 ≤ S.1 from h) := by
  let D := CoefficientModels.specDiagram k₀ K
  let m : Over (Opposite.op M.R) := Over.mk (homOfLE ((leOfHom k.hom.unop).trans h)).op
  let b : m ⟶ k := Over.homMk (homOfLE h).op (Subsingleton.elim _ _)
  let σ : pullback W.hom (π (show M.R.1 ≤ S.1 from (leOfHom k.hom.unop).trans h)) ≅
      CoefficientModels.stageObj D W m := pullbackSymmetry _ _
  have : IsAffineHom (CoefficientModels.stageMap D W b) :=
    CoefficientModels.isAffineHom_stageMap D W b
  refine ⟨σ.hom ≫ CoefficientModels.stageMap D W b, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, CoefficientModels.stageMap_snd]
    exact pullbackSymmetry_hom_comp_snd _ _
  · have hσ : σ.hom ≫ pullback.fst (D.map m.hom) W.hom = pullback.snd _ _ :=
      pullbackSymmetry_hom_comp_fst _ _
    rw [Category.assoc, CoefficientModels.stageMap_fst, ← Category.assoc, hσ]
    rfl

open Stacks.AlgebraicGeometry.ModuleLimits in
/-- **Ampleness descends to a stage** (Stacks 09MT): for a scheme `W` of finite presentation over
the first stage whose base change to `K` is `Xw`, an invertible module on `W` whose pullback to
`Xw` is ample has ample pullbacks to all late stages. -/
private lemma Model.eventually_isAmple
    (W : Over ((CoefficientModels.specDiagram k₀ K).obj (Opposite.op M.R)))
    (hW : FinitePresentation W.hom) (Xw : Over (Spec (.of K))) (gw : Xw.left ⟶ W.left)
    (hpb : IsPullback gw Xw.hom W.hom (κ M.R.1)) (N : W.left.Modules)
    [Stacks.Ample.IsInvertibleModule _ N]
    (hX : Stacks.Ample.IsAmple Xw.left ((Scheme.Modules.pullback gw).obj N)) :
    M.Eventually fun S h =>
      Stacks.Ample.IsAmple (pullback W.hom (π (show M.R.1 ≤ S.1 from h)))
        ((Scheme.Modules.pullback (pullback.fst W.hom (π (show M.R.1 ≤ S.1 from h)))).obj N) := by
  let D := CoefficientModels.specDiagram k₀ K
  have hpb' : IsPullback gw Xw.hom W.hom
      ((CoefficientModels.specCone k₀ K).π.app (Opposite.op M.R)) := hpb
  have : ∀ {a b : Over (Opposite.op M.R)} (f : a ⟶ b),
      IsAffineHom ((CoefficientModels.stageDiagram D W).map f) := fun f =>
    CoefficientModels.isAffineHom_stageMap D W f
  have : ∀ a, CompactSpace ((CoefficientModels.stageDiagram D W).obj a) := fun a =>
    CoefficientModels.compactSpace_stageObj D W hW a
  have : ∀ a, QuasiSeparatedSpace ((CoefficientModels.stageDiagram D W).obj a) := fun a =>
    CoefficientModels.quasiSeparatedSpace_stageObj D W hW a
  let i : Over (Opposite.op M.R) := Over.mk (𝟙 _)
  let s : (CoefficientModels.stageDiagram D W).obj i ⟶ W.left := pullback.snd (D.map i.hom) W.hom
  let c' := CoefficientModels.legCone D W (CoefficientModels.specCone k₀ K) Xw gw hpb'
  have hl : c'.π.app i ≫ s = gw := CoefficientModels.leg_snd D W _ _ _ hpb' i
  have hsN : Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback s).obj N) :=
    MMP.Fourfold.isInvertibleModule_pullback _ _
  have := Stacks.RelativeVeryAmple.stacksIsInvertible _ ((Scheme.Modules.pullback s).obj N)
  have h1 := MMP.Fourfold.isInvertibleModule_pullback (c'.π.app i)
    ((Scheme.Modules.pullback s).obj N)
  have := Stacks.RelativeVeryAmple.stacksIsInvertible _
    ((Scheme.Modules.pullback (c'.π.app i)).obj ((Scheme.Modules.pullback s).obj N))
  have h2 := MMP.Fourfold.isInvertibleModule_pullback gw N
  have hlim : Scheme.Modules.IsAmple c'.pt
      ((Scheme.Modules.pullback (c'.π.app i)).obj ((Scheme.Modules.pullback s).obj N)) := by
    rw [← Stacks.AmpleBridge.isAmple_iff_isAmple]
    exact (@Stacks.RelativeVeryAmple.isAmple_congr Xw.left _ _ h1 h2 (canIso _ s _ hl N)).mpr hX
  obtain ⟨k, e, hkA⟩ :=
      Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs
    (CoefficientModels.stageDiagram D W) c'
    (CoefficientModels.isLimitLegCone D W _ _ _ hpb' (CoefficientModels.isLimitSpecCone k₀ K)) i
    _ hlim
  have hk : M.R ≤ k.left.unop := leOfHom k.hom.unop
  refine ⟨k.left.unop, hk, fun S h => ?_⟩
  obtain ⟨τ, hτ, hτs, -⟩ := M.exists_stage_τ W k S h
  let sk : CoefficientModels.stageObj D W k ⟶ W.left := pullback.snd (D.map k.hom) W.hom
  have hes : (CoefficientModels.stageDiagram D W).map e ≫ s = sk :=
    CoefficientModels.stageMap_snd D W e
  have h3 := MMP.Fourfold.isInvertibleModule_pullback ((CoefficientModels.stageDiagram D W).map e)
    ((Scheme.Modules.pullback s).obj N)
  have i3 := Stacks.RelativeVeryAmple.stacksIsInvertible _
    ((Scheme.Modules.pullback ((CoefficientModels.stageDiagram D W).map e)).obj
      ((Scheme.Modules.pullback s).obj N))
  have h4 := MMP.Fourfold.isInvertibleModule_pullback sk N
  have i4 := Stacks.RelativeVeryAmple.stacksIsInvertible _ ((Scheme.Modules.pullback sk).obj N)
  have hk' : Scheme.Modules.IsAmple _ ((Scheme.Modules.pullback sk).obj N) :=
    @Scheme.Modules.isAmple_of_iso _ _ _ i3 i4 (canIso _ s _ hes N) hkA
  have h5 := MMP.Fourfold.isInvertibleModule_pullback τ ((Scheme.Modules.pullback sk).obj N)
  have := Stacks.RelativeVeryAmple.stacksIsInvertible _
    ((Scheme.Modules.pullback τ).obj ((Scheme.Modules.pullback sk).obj N))
  have : QuasiCompact (pullback.snd W.hom (π (show M.R.1 ≤ S.1 from hk.trans h))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback W.hom _)
      hW.2.1
  have : CompactSpace (Limits.pullback (C := Scheme.{u}) W.hom
      (π (show M.R.1 ≤ S.1 from hk.trans h))) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd W.hom _)
  have hτA := Scheme.Modules.isAmple_pullback_of_isAffineHom τ _ hk'
  have h6 := MMP.Fourfold.isInvertibleModule_pullback
    (pullback.fst W.hom (π (show M.R.1 ≤ S.1 from hk.trans h))) N
  rw [← Stacks.AmpleBridge.isAmple_iff_isAmple] at hτA
  exact (@Stacks.RelativeVeryAmple.isAmple_congr _ _ _ h5 h6 (canIso τ sk _ hτs N)).mp hτA

open Stacks.AlgebraicGeometry.ModuleLimits RingedSpaceModuleAdjunction in
/-- **Ampleness on a quasi-compact open of a vertex descends to a stage**: if the restriction of
the pullback of an invertible module `N` on a vertex of the model to the preimage over `K` of a
quasi-compact open `W₀` is ample, then so is its restriction to the preimage of `W₀` at every
late stage. -/
private lemma Model.eventually_isAmple_open (j : J) (W₀ : (M.Y.obj j).left.Opens)
    (hW₀ : IsCompact (W₀ : Set (M.Y.obj j).left)) (N : (M.Y.obj j).left.Modules)
    [Stacks.Ample.IsInvertibleModule _ N]
    (hK : haveI := MMP.Fourfold.isInvertibleModule_pullback (M.p j) N
      Stacks.Ample.IsAmple (M.p j ⁻¹ᵁ W₀).toScheme
        ((modulePullback (M.p j ⁻¹ᵁ W₀).ι.toLRSHom.toShHom).obj
          ((Scheme.Modules.pullback (M.p j)).obj N))) :
    M.Eventually fun S h =>
      haveI := MMP.Fourfold.isInvertibleModule_pullback
        (pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h))) N
      Stacks.Ample.IsAmple (pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h)) ⁻¹ᵁ W₀)
        ((modulePullback (pullback.fst (M.Y.obj j).hom
          (π (show M.R.1 ≤ S.1 from h)) ⁻¹ᵁ W₀).ι.toLRSHom.toShHom).obj
          ((Scheme.Modules.pullback (pullback.fst (M.Y.obj j).hom
            (π (show M.R.1 ≤ S.1 from h)))).obj N)) := by
  have := M.quasiSeparatedSpace j
  have hc : CompactSpace W₀ := isCompact_iff_compactSpace.mp hW₀
  let W : Over ((CoefficientModels.specDiagram k₀ K).obj (Opposite.op M.R)) :=
    Over.mk (W₀.ι ≫ (M.Y.obj j).hom)
  have hW : FinitePresentation W.hom := by
    have hl := (M.fp j).1
    have hqs : QuasiSeparatedSpace W₀ :=
      (isQuasiSeparated_iff_quasiSeparatedSpace (W₀ : Set (M.Y.obj j).left) W₀.isOpen).mp
        (IsQuasiSeparated.of_quasiSeparatedSpace _)
    refine ⟨?_, (quasiCompact_iff_compactSpace (W₀.ι ≫ (M.Y.obj j).hom)).mpr hc,
      (quasiSeparated_iff_quasiSeparatedSpace (W₀.ι ≫ (M.Y.obj j).hom)).mpr hqs⟩
    show LocallyOfFinitePresentation (W₀.ι ≫ (M.Y.obj j).hom)
    infer_instance
  let Xw : Over (Spec (.of K)) := Over.mk ((M.p j ⁻¹ᵁ W₀).ι ≫ (X.obj j).hom)
  have hpb : IsPullback (M.p j ∣_ W₀) Xw.hom W.hom (κ M.R.1) :=
    (isPullback_morphismRestrict (M.p j) W₀).paste_vert (M.cart.isPullback j)
  have hN' : Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback W₀.ι).obj N) :=
    MMP.Fourfold.isInvertibleModule_pullback _ _
  have hX : Stacks.Ample.IsAmple Xw.left
      ((Scheme.Modules.pullback (M.p j ∣_ W₀)).obj ((Scheme.Modules.pullback W₀.ι).obj N)) := by
    have := MMP.Fourfold.isInvertibleModule_pullback (M.p j) N
    have h1 := MMP.Fourfold.isInvertibleModule_pullback (M.p j ∣_ W₀)
      ((Scheme.Modules.pullback W₀.ι).obj N)
    have h2 := Stacks.InvertiblePullback.isInvertibleModule_restrict (M.p j ⁻¹ᵁ W₀)
      ((Scheme.Modules.pullback (M.p j)).obj N)
    exact (@Stacks.RelativeVeryAmple.isAmple_congr _ _ _ h1 h2
      (canIso _ _ _ (morphismRestrict_ι (M.p j) W₀) N ≪≫
        (canIso _ _ _ rfl N).symm)).mpr hK
  refine (M.eventually_isAmple W hW Xw (M.p j ∣_ W₀) hpb _ hX).mono fun S h hS => ?_
  let F := pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h))
  have hP : IsPullback (F ∣_ W₀) ((F ⁻¹ᵁ W₀).ι ≫ pullback.snd (M.Y.obj j).hom
      (π (show M.R.1 ≤ S.1 from h))) W.hom (π (show M.R.1 ≤ S.1 from h)) :=
    (isPullback_morphismRestrict F W₀).paste_vert (IsPullback.of_hasPullback _ _)
  let φ := hP.isoPullback
  have hφ : φ.hom ≫ pullback.fst W.hom (π (show M.R.1 ≤ S.1 from h)) = F ∣_ W₀ :=
    hP.isoPullback_hom_fst
  have h1 := Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom φ.hom _ hS
  have i1 : Stacks.Ample.IsInvertibleModule _ (Stacks.AmpleLocallyClosed.pullbackModule φ.hom
      ((Scheme.Modules.pullback (pullback.fst W.hom (π (show M.R.1 ≤ S.1 from h)))).obj
        ((Scheme.Modules.pullback W₀.ι).obj N))) :=
    MMP.Fourfold.isInvertibleModule_pullback _ _
  have := MMP.Fourfold.isInvertibleModule_pullback F N
  have i2 := Stacks.InvertiblePullback.isInvertibleModule_restrict (F ⁻¹ᵁ W₀)
    ((Scheme.Modules.pullback F).obj N)
  exact (@Stacks.RelativeVeryAmple.isAmple_congr _ _ _ i1 i2
    (canIso φ.hom _ _ hφ _ ≪≫ canIso (F ∣_ W₀) W₀.ι _ (morphismRestrict_ι F W₀) N ≪≫
      (canIso _ F _ rfl N).symm)).mp h1

open RingedSpaceModuleAdjunction in
private lemma isAmple_restrict_of_eq {Z : Scheme.{u}} {U U' : Z.Opens} (h : U = U')
    (L : Z.Modules) [Stacks.Ample.IsInvertibleModule Z L]
    (hU : Stacks.Ample.IsAmple U ((modulePullback U.ι.toLRSHom.toShHom).obj L)) :
    Stacks.Ample.IsAmple U' ((modulePullback U'.ι.toLRSHom.toShHom).obj L) := by
  subst h
  exact hU

open RingedSpaceModuleAdjunction in
/-- **Relative ampleness descends to a stage.** Let `f₀` be a quasi-compact morphism from a
vertex of the model to a quasi-compact scheme `T`, with base change `fK` over `K` along an affine
`pT`, and with base changes `fS` at the later stages along affine morphisms `qT`. If the pullback
`L` of an invertible module `N` is `fK`-ample, then the pullback of `N` to every late stage is
`fS`-ample. -/
public lemma Model.eventually_isRelativelyAmple (j : J) (N : (M.Y.obj j).left.Modules)
    [Stacks.Ample.IsInvertibleModule _ N] {T : Scheme.{u}} [CompactSpace T]
    (f₀ : (M.Y.obj j).left ⟶ T) [QuasiCompact f₀] {TK : Scheme.{u}} (pT : TK ⟶ T)
    [IsAffineHom pT] (fK : (X.obj j).left ⟶ TK) [QuasiCompact fK] (hK : M.p j ≫ f₀ = fK ≫ pT)
    (L : (X.obj j).left.Modules) [Stacks.Ample.IsInvertibleModule _ L]
    (θ : (Scheme.Modules.pullback (M.p j)).obj N ≅ L)
    (TS : ∀ S : CoefficientModels.FGSub k₀ K, M.R ≤ S → Scheme.{u})
    (qT : ∀ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S), TS S h ⟶ T)
    (hqT : ∀ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S), IsAffineHom (qT S h))
    (fS : ∀ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S),
      pullback (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h)) ⟶ TS S h)
    (hS : ∀ (S : CoefficientModels.FGSub k₀ K) (h : M.R ≤ S), fS S h ≫ qT S h =
      pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h)) ≫ f₀)
    (hamp : Mori.IsRelativelyAmple fK L) :
    M.Eventually fun S h =>
      haveI := MMP.Fourfold.isInvertibleModule_pullback
        (pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h))) N
      Mori.IsRelativelyAmple (fS S h) ((Scheme.Modules.pullback
        (pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h)))).obj N) := by
  classical
  have hst : Stacks.RelativeAmple.IsRelativelyAmple fK L :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple fK L ‹_› hamp
  choose V hV hmem _ using fun t : T => exists_isAffineOpen_mem_and_subset (U := ⊤)
    (Set.mem_univ t)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t => (V t : Set T))
    (fun t => (V t).isOpen) (fun t _ => Set.mem_iUnion.mpr ⟨t, hmem t⟩)
  have key : ∀ t : s, M.Eventually fun S h =>
      haveI := MMP.Fourfold.isInvertibleModule_pullback
        (pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h))) N
      Stacks.Ample.IsAmple (pullback.fst (M.Y.obj j).hom (π (show M.R.1 ≤ S.1 from h)) ⁻¹ᵁ
          (f₀ ⁻¹ᵁ V t))
        ((modulePullback (pullback.fst (M.Y.obj j).hom
          (π (show M.R.1 ≤ S.1 from h)) ⁻¹ᵁ (f₀ ⁻¹ᵁ V t)).ι.toLRSHom.toShHom).obj
          ((Scheme.Modules.pullback (pullback.fst (M.Y.obj j).hom
            (π (show M.R.1 ≤ S.1 from h)))).obj N)) := fun t => by
    refine M.eventually_isAmple_open j (f₀ ⁻¹ᵁ V t) (f₀.isCompact_preimage (hV t).isCompact) N ?_
    have h1 := hst.isAmple_preimage fK L (pT ⁻¹ᵁ V t) ((hV t).preimage pT)
    have heq : fK ⁻¹ᵁ (pT ⁻¹ᵁ V t) = M.p j ⁻¹ᵁ (f₀ ⁻¹ᵁ V t) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hK]
    have h2 := isAmple_restrict_of_eq heq L h1
    have := MMP.Fourfold.isInvertibleModule_pullback (M.p j) N
    exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
      ((modulePullback (M.p j ⁻¹ᵁ (f₀ ⁻¹ᵁ V t)).ι.toLRSHom.toShHom).mapIso θ)).mpr h2
  refine (Model.Eventually.forall key).mono fun S h H => ?_
  intro y
  obtain ⟨t, ht, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ (qT S h y)))
  have := hqT S h
  refine ⟨qT S h ⁻¹ᵁ V t, (hV t).preimage _, hy, ?_⟩
  refine isAmple_restrict_of_eq ?_ _ (H ⟨t, ht⟩)
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hS]

/-- The comparison of a later stage of the model with an earlier one. -/
@[expose] public noncomputable def Model.stageCmp {S₀ S : CoefficientModels.FGSub k₀ K}
    (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) (j : J) : ((M.stage (h₀.trans h)).obj j).left ⟶ ((M.stage h₀).obj j).left :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ π (show S₀.1 ≤ S.1 from h))
    (by rw [pullback.condition, Category.assoc, π_π])

/-- A later stage of the model is the base change of an earlier one. -/
public lemma Model.isCartesian_stageCmp {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) : IsCartesian (π (show S₀.1 ≤ S.1 from h)) (M.stage (h₀.trans h)) (M.stage h₀)
      (M.stageCmp h₀ h) where
  w {j j'} g := by
    apply pullback.hom_ext
    · simp only [Model.stageCmp, Category.assoc, Functor.comp_map, pullback.lift_fst,
        pullback.lift_fst_assoc, overPullback_map_left_fst]
    · simp only [Model.stageCmp, Category.assoc, Functor.comp_map, pullback.lift_snd,
        pullback.lift_snd_assoc, overPullback_map_left_snd, overPullback_map_left_snd_assoc]
  isPullback j := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [Model.stageCmp, pullback.lift_fst, π_π]
    exact IsPullback.of_hasPullback _ _

/-- The comparison of the fibre of a later stage `S` over `t` with the vertex at an earlier stage
`S₀`. -/
public noncomputable abbrev Model.fibreMap {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) {L : Type u} [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) (j : J) :
    ((M.stage (h₀.trans h) ⋙ Over.pullback t).obj j).left ⟶ ((M.stage h₀).obj j).left :=
  pullback.fst _ t ≫ M.stageCmp h₀ h j

/-- The fibre of a later stage over `t` is the fibre of the earlier stage over `t ≫ π`. -/
public lemma Model.isPullback_fibreMap {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) {L : Type u} [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) (j : J) :
    IsPullback (M.fibreMap h₀ h t j) (pullback.snd _ t) ((M.stage h₀).obj j).hom
      (t ≫ π (show S₀.1 ≤ S.1 from h)) :=
  (IsPullback.of_hasPullback ((M.stage (h₀.trans h)).obj j).hom t).paste_horiz
    ((M.isCartesian_stageCmp h₀ h).isPullback j)

/-- The comparison of the diagram over `K` with a stage of the model. -/
@[expose] public noncomputable def Model.cmp {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S)
    (j : J) :
    (X.obj j).left ⟶ ((M.stage h).obj j).left :=
  pullback.lift (M.p j) ((X.obj j).hom ≫ κ S.1) (by
    rw [Category.assoc, κ_π]; exact (M.cart.isPullback j).w)

/-- The diagram `X` is cartesian over every stage of the model, along `Spec K ⟶ Spec S`. -/
public lemma Model.isCartesian_cmp {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) :
    IsCartesian (κ S.1) X (M.stage h) (M.cmp h) where
  w {j j'} g := by
    apply pullback.hom_ext
    · simp only [Model.cmp, Category.assoc, Functor.comp_map, pullback.lift_fst,
        pullback.lift_fst_assoc, overPullback_map_left_fst]
      exact M.cart.w g
    · simp only [Model.cmp, Category.assoc, Functor.comp_map, pullback.lift_snd,
        pullback.lift_snd_assoc, overPullback_map_left_snd]
      rw [← Over.w (X.map g), Category.assoc]
  isPullback j := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [Model.cmp, pullback.lift_fst, κ_π]
    exact M.cart.isPullback j

/-- The comparison of the base change of `X` with the model at a later stage. -/
public lemma Model.isCartesian_stage {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) :
    ∃ q : ∀ j, (X.obj j).left ⟶ ((M.stage h).obj j).left,
      IsCartesian (κ S.1) X (M.stage h) q ∧ ∀ j, q j ≫ pullback.fst _ _ = M.p j :=
  ⟨M.cmp h, M.isCartesian_cmp h, fun _ => pullback.lift_fst _ _ _⟩

/-- Stage comparisons compose. -/
public lemma Model.stageCmp_comp {S₀ S₁ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h₁ : S₀ ≤ S₁) (h₂ : S₁ ≤ S) (j : J) :
    M.stageCmp (h₀.trans h₁) h₂ j ≫ M.stageCmp h₀ h₁ j = M.stageCmp h₀ (h₁.trans h₂) j := by
  apply pullback.hom_ext
  · simp only [Model.stageCmp, Category.assoc, pullback.lift_fst]
  · simp only [Model.stageCmp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, π_π]

/-- The comparison of the diagram over `K` with a later stage, followed by the stage comparison,
is the comparison with the earlier stage. -/
public lemma Model.cmp_stageCmp {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) (j : J) : M.cmp (h₀.trans h) j ≫ M.stageCmp h₀ h j = M.cmp h₀ j := by
  apply pullback.hom_ext
  · simp only [Model.cmp, Model.stageCmp, Category.assoc, pullback.lift_fst]
  · simp only [Model.cmp, Model.stageCmp, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, κ_π]

/-- Fibre comparisons factor through later stages. -/
public lemma Model.fibreMap_comp {S₀ S₁ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h₁ : S₀ ≤ S₁) (h₂ : S₁ ≤ S) {L : Type u} [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1))
    (j : J) :
    M.fibreMap (h₀.trans h₁) h₂ t j ≫ M.stageCmp h₀ h₁ j = M.fibreMap h₀ (h₁.trans h₂) t j := by
  simp only [Model.fibreMap, Category.assoc, M.stageCmp_comp]

/-- **Quasi-compact opens descend to a stage** (Stacks 01Z4): a quasi-compact open of a vertex over
`K` is the preimage of a quasi-compact open of the vertex at every late stage. -/
public lemma Model.exists_open (j : J) (U : (X.obj j).left.Opens)
    (hU : IsCompact (U : Set (X.obj j).left)) :
    ∃ (S₀ : CoefficientModels.FGSub k₀ K) (h₀ : M.R ≤ S₀), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₀ ≤ S), ∃ V : ((M.stage (h₀.trans h)).obj j).left.Opens,
        IsCompact (V : Set ((M.stage (h₀.trans h)).obj j).left) ∧
          M.cmp (h₀.trans h) j ⁻¹ᵁ V = U := by
  let D := CoefficientModels.specDiagram k₀ K
  let W : Over (D.obj (Opposite.op M.R)) := M.Y.obj j
  have hpb : IsPullback (M.p j) (X.obj j).hom W.hom
      ((CoefficientModels.specCone k₀ K).π.app (Opposite.op M.R)) := M.cart.isPullback j
  have : ∀ {a b : Over (Opposite.op M.R)} (f : a ⟶ b),
      IsAffineHom ((CoefficientModels.stageDiagram D W).map f) := fun f =>
    CoefficientModels.isAffineHom_stageMap D W f
  obtain ⟨i, V, hV, hVU⟩ := exists_preimage_eq (CoefficientModels.stageDiagram D W)
    (CoefficientModels.legCone D W (CoefficientModels.specCone k₀ K) (X.obj j) (M.p j) hpb)
    (CoefficientModels.isLimitLegCone D W _ _ _ hpb (CoefficientModels.isLimitSpecCone k₀ K))
    U hU
  refine ⟨i.left.unop, leOfHom i.hom.unop, fun S h => ?_⟩
  obtain ⟨τ, hτ, hτs, hτf⟩ := M.exists_stage_τ W i S h
  have hcτ : M.cmp ((leOfHom i.hom.unop).trans h) j ≫ τ =
      CoefficientModels.leg D W (CoefficientModels.specCone k₀ K) (X.obj j) (M.p j) hpb i := by
    apply pullback.hom_ext
    · erw [Category.assoc, hτf, CoefficientModels.leg_fst, Model.cmp, pullback.lift_snd_assoc,
        Category.assoc, κ_π]
      rfl
    · erw [Category.assoc, hτs, CoefficientModels.leg_snd, Model.cmp, pullback.lift_fst]
  refine ⟨τ ⁻¹ᵁ V, τ.isCompact_preimage hV, ?_⟩
  erw [← Scheme.Hom.comp_preimage, hcτ]
  exact hVU

/-- **Closed subschemes descend to a stage** (Stacks 01ZM, 01ZP): a closed subscheme of a vertex
over `K` is the base change of a closed subscheme of the vertex at some stage. -/
public lemma Model.exists_closedSubscheme (j : J) {E : Scheme.{u}} (iE : E ⟶ (X.obj j).left)
    [IsClosedImmersion iE] :
    ∃ (S₀ : CoefficientModels.FGSub k₀ K) (h₀ : M.R ≤ S₀) (E₀ : Scheme.{u})
      (e₀ : E₀ ⟶ ((M.stage h₀).obj j).left) (q₀ : E ⟶ E₀),
      IsClosedImmersion e₀ ∧ IsPullback q₀ iE e₀ (M.cmp h₀ j) := by
  let D := CoefficientModels.specDiagram k₀ K
  let W : Over (D.obj (Opposite.op M.R)) := M.Y.obj j
  have hpb : IsPullback (M.p j) (X.obj j).hom W.hom
      ((CoefficientModels.specCone k₀ K).π.app (Opposite.op M.R)) := M.cart.isPullback j
  have : ∀ {a b : Over (Opposite.op M.R)} (f : a ⟶ b),
      IsAffineHom ((CoefficientModels.stageDiagram D W).map f) := fun f =>
    CoefficientModels.isAffineHom_stageMap D W f
  have hW : FinitePresentation W.hom := M.fp j
  have : ∀ a, CompactSpace ((CoefficientModels.stageDiagram D W).obj a) := fun a =>
    CoefficientModels.compactSpace_stageObj D W hW a
  have : ∀ a, QuasiSeparatedSpace ((CoefficientModels.stageDiagram D W).obj a) := fun a =>
    CoefficientModels.quasiSeparatedSpace_stageObj D W hW a
  have := M.locallyOfFiniteType_obj j
  have : IsLocallyNoetherian (X.obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian (X.obj j).hom
  have hfp : FinitePresentation iE :=
    ⟨instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType iE, inferInstance,
      instQuasiSeparatedOfMonoScheme iE⟩
  obtain ⟨i, Y, hY, ⟨e⟩⟩ := @exists_isClosedImmersion_model_of_isLimit _ _ _ _
    (CoefficientModels.stageDiagram D W)
    (CoefficientModels.legCone D W (CoefficientModels.specCone k₀ K) (X.obj j) (M.p j) hpb)
    (CoefficientModels.isLimitLegCone D W _ _ _ hpb (CoefficientModels.isLimitSpecCone k₀ K))
    _ _ _ (Over.mk iE) ‹IsClosedImmersion iE› hfp
  refine ⟨i.left.unop, leOfHom i.hom.unop, ?_⟩
  obtain ⟨τ, -, hτs, hτf⟩ := M.exists_stage_τ W i i.left.unop le_rfl
  let leg := CoefficientModels.leg D W (CoefficientModels.specCone k₀ K) (X.obj j) (M.p j) hpb i
  have hcτ : M.cmp ((leOfHom i.hom.unop).trans le_rfl) j ≫ τ = leg := by
    apply pullback.hom_ext
    · erw [Category.assoc, hτf, CoefficientModels.leg_fst, Model.cmp, pullback.lift_snd_assoc,
        Category.assoc, κ_π]
      rfl
    · erw [Category.assoc, hτs, CoefficientModels.leg_snd, Model.cmp, pullback.lift_fst]
  have hY' : IsClosedImmersion Y.hom := hY
  let a : pullback Y.hom leg ⟶ pullback Y.hom τ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ M.cmp (leOfHom i.hom.unop) j)
      ((pullback.condition).trans ((congrArg (pullback.snd Y.hom leg ≫ ·) hcτ).symm.trans
        (Category.assoc _ _ _).symm))
  have hR : IsPullback (pullback.fst Y.hom τ) (pullback.snd Y.hom τ) Y.hom τ :=
    IsPullback.of_hasPullback _ _
  have hL : IsPullback a (pullback.snd Y.hom leg) (pullback.snd Y.hom τ)
      (M.cmp ((leOfHom i.hom.unop).trans le_rfl) j) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hR
    have ha : a ≫ pullback.fst Y.hom τ = pullback.fst Y.hom leg := pullback.lift_fst _ _ _
    have hO : IsPullback (pullback.fst Y.hom leg) (pullback.snd Y.hom leg) Y.hom
        (M.cmp (leOfHom i.hom.unop) j ≫ τ) := hcτ ▸ IsPullback.of_hasPullback Y.hom leg
    rwa [ha]
  have hE : IsPullback e.hom.left iE (pullback.snd Y.hom leg) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w e.hom⟩
  refine ⟨pullback Y.hom τ, pullback.snd Y.hom τ, e.hom.left ≫ a,
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (IsPullback.of_hasPullback Y.hom τ)
      hY, ?_⟩
  exact Category.id_comp (M.cmp (leOfHom i.hom.unop) j) ▸ hE.paste_horiz hL

/-- The point of `Spec K` lies over the generic point of every stage. -/
public lemma κ_apply_eq_bot (R : Subalgebra k₀ K) (x : Spec (.of K)) :
    (κ R).base x = (⊥ : PrimeSpectrum R) := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  change PrimeSpectrum.comap (algebraMap R K) (IsLocalRing.closedPoint K) = ⊥
  ext r
  change algebraMap R K r ∈ IsLocalRing.maximalIdeal K ↔ r ∈ (⊥ : Ideal R)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not,
    Ideal.mem_bot, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R K)]

/-- **Open subsets meeting the generic fibre meet every late field-valued fibre**: if a vertex at
a stage is flat, an open of it whose preimage over `K` is nonempty has nonempty preimage in the
fibre over every field-valued point of every late stage. -/
public lemma Model.exists_nonempty_fibre (j : J) {S₀ : CoefficientModels.FGSub k₀ K}
    (h₀ : M.R ≤ S₀) [Flat ((M.stage h₀).obj j).hom]
    [LocallyOfFinitePresentation ((M.stage h₀).obj j).hom]
    (V : ((M.stage h₀).obj j).left.Opens) (hV : (M.cmp h₀ j ⁻¹ᵁ V : Set (X.obj j).left).Nonempty) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      Set.Nonempty (SetLike.coe (pullback.fst ((M.stage (h₀.trans (h₂.trans h))).obj j).hom t ⁻¹ᵁ
        (M.stageCmp h₀ (h₂.trans h) j ⁻¹ᵁ V))) := by
  classical
  let f := V.ι ≫ ((M.stage h₀).obj j).hom
  have hO : IsOpen (Set.range f.base) := f.isOpenMap.isOpen_range
  obtain ⟨x, hx⟩ := hV
  have hbot : (⊥ : PrimeSpectrum S₀.1) ∈ Set.range f.base := by
    refine ⟨⟨M.cmp h₀ j x, hx⟩, ?_⟩
    change ((M.cmp h₀ j) ≫ ((M.stage h₀).obj j).hom).base x = (⊥ : PrimeSpectrum S₀.1)
    rw [(M.isCartesian_cmp h₀).isPullback j |>.w, Scheme.Hom.comp_apply]
    exact κ_apply_eq_bot _ _
  obtain ⟨_, ⟨r, rfl⟩, hr, hrO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hbot hO
  obtain ⟨S₂, h₂, H₂⟩ := exists_le_forall_notMem S₀ r (fun h0 => hr (h0 ▸ Ideal.zero_mem _))
  refine ⟨S₂, h₂, fun S h L _ t => ?_⟩
  -- the image of the fibre point in the stage `S₀`
  let y := (t ≫ π (show S₀.1 ≤ S.1 from h₂.trans h)).base (IsLocalRing.closedPoint L)
  have hy : y ∈ Set.range f.base := hrO (show y ∈ PrimeSpectrum.basicOpen r from H₂ S h L t)
  obtain ⟨v, hv⟩ := hy
  -- the fibre is the base change of the stage `S₀` along `t ≫ π`
  have hP := (IsPullback.of_hasPullback ((M.stage (h₀.trans (h₂.trans h))).obj j).hom t).paste_horiz
    ((M.isCartesian_stageCmp h₀ (h₂.trans h)).isPullback j)
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := ((M.stage h₀).obj j).hom) (g := t ≫ π (show S₀.1 ≤ S.1 from h₂.trans h))
    (V.ι.base v) (IsLocalRing.closedPoint L) (by rw [← Scheme.Hom.comp_apply]; exact hv)
  refine ⟨hP.isoPullback.inv z, ?_⟩
  change (pullback.fst _ _ ≫ M.stageCmp h₀ (h₂.trans h) j).base (hP.isoPullback.inv z) ∈ V
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz₁]
  exact v.2

/-- Every vertex of a stage of the model is of finite presentation. -/
public lemma Model.finitePresentation_stage {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S)
    (j : J) : FinitePresentation ((M.stage h).obj j).hom :=
  ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) (M.fp j).1,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) (M.fp j).2.1,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) (M.fp j).2.2⟩

/-- The field-valued fibres of the stages are locally of finite type. -/
public lemma Model.locallyOfFiniteType_fibre {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S)
    {L : Type u} [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) (j : J) :
    LocallyOfFiniteType ((M.stage h ⋙ Over.pullback t).obj j).hom :=
  have := (M.finitePresentation_stage h j).1
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback _ t)
    inferInstance

/-- Every vertex of a stage of the model is quasi-compact. -/
public lemma Model.compactSpace_stage {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) (j : J) :
    CompactSpace ((M.stage h).obj j).left :=
  have := (M.finitePresentation_stage h j).2.1
  QuasiCompact.compactSpace_of_compactSpace ((M.stage h).obj j).hom

/-- Every vertex of a stage of the model is quasi-separated. -/
public lemma Model.quasiSeparatedSpace_stage {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S)
    (j : J) : QuasiSeparatedSpace ((M.stage h).obj j).left :=
  have := (M.finitePresentation_stage h j).2.2
  (quasiSeparated_iff_quasiSeparatedSpace ((M.stage h).obj j).hom).mp inferInstance

/-- Every morphism of a stage of the model is locally of finite presentation. -/
public lemma Model.locallyOfFinitePresentation_stage_map {S : CoefficientModels.FGSub k₀ K}
    (h : M.R ≤ S) {j j' : J} (g : j ⟶ j') : LocallyOfFinitePresentation ((M.stage h).map g).left :=
  MorphismProperty.of_isPullback (overPullback_isPullback _ _ _ _)
    (M.locallyOfFinitePresentation_map g)

/-- The fibre of a later stage over `t` is a base change of an earlier stage. -/
public lemma Model.isCartesian_fibre {S₀ S : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (h : S₀ ≤ S) {L : Type u} [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)) :
    IsCartesian (t ≫ π (show S₀.1 ≤ S.1 from h)) (M.stage (h₀.trans h) ⋙ Over.pullback t)
      (M.stage h₀) (fun j => M.fibreMap h₀ h t j) :=
  (isCartesian_pullback t (M.stage (h₀.trans h))).comp (M.isCartesian_stageCmp h₀ h)

/-- The morphisms of the stages are proper. -/
public lemma Model.isProper_stage_map {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S)
    {j j' : J} (g : j ⟶ j') : IsProper ((M.stage h).map g).left := by
  have hP : ∀ i, IsProper ((M.stage h).obj i).hom := fun i =>
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback _ _)
      (isProper_of_isProjectiveMorphism _ (M.hproj i))
  have := hP j
  have := hP j'
  have : IsProper (((M.stage h).map g).left ≫ ((M.stage h).obj j').hom) := by
    rw [Over.w]; infer_instance
  exact IsProper.of_comp _ ((M.stage h).obj j').hom

/-- The image of a morphism of a stage, a closed subset. -/
@[expose] public def Model.rangeClosed {S : CoefficientModels.FGSub k₀ K} (h : M.R ≤ S) {j j' : J}
    (g : j ⟶ j') : TopologicalSpace.Closeds ((M.stage h).obj j').left :=
  ⟨Set.range ((M.stage h).map g).left.base,
    have := M.isProper_stage_map h g
    ((M.stage h).map g).left.isClosedMap.isClosed_range⟩

/-- A property of the field-valued fibres of a vertex at a stage `S₀` that holds outside the zero
set of a nonzero element holds on the fibres of all late stages. -/
private lemma Model.exists_of_ne_zero {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (Q : ∀ {F : Scheme.{u}}, (F ⟶ ((M.stage h₀).obj j).left) → Prop)
    (H : ∃ r : S₀.1, r ≠ 0 ∧ ∀ (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S₀.1)),
      r ∉ (t.base (IsLocalRing.closedPoint L)).asIdeal → ∀ {F : Scheme.{u}}
        (fst : F ⟶ ((M.stage h₀).obj j).left) (snd : F ⟶ Spec (.of L)),
        IsPullback fst snd ((M.stage h₀).obj j).hom t → Q fst) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      Q (M.fibreMap h₀ (h₂.trans h) t j) := by
  obtain ⟨r, hr, H⟩ := H
  obtain ⟨S₂, h₂, H₂⟩ := exists_le_forall_notMem S₀ r hr
  exact ⟨S₂, h₂, fun S h L _ t => H L _ (H₂ S h L t) _ _
      (M.isPullback_fibreMap h₀ (h₂.trans h) t j)⟩

/-- **Inclusions of closed subsets of a stage spread to the fibres of late stages.** -/
public lemma Model.exists_preimage_subset {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (j : J) (C₁ C₂ : TopologicalSpace.Closeds ((M.stage h₀).obj j).left)
    (hC : M.cmp h₀ j ⁻¹' C₁ ⊆ M.cmp h₀ j ⁻¹' C₂) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap h₀ (h₂.trans h) t j ⁻¹' C₁ ⊆ M.fibreMap h₀ (h₂.trans h) t j ⁻¹' C₂ :=
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K S₀
  M.exists_of_ne_zero h₀ j (fun fst => fst ⁻¹' C₁ ⊆ fst ⁻¹' C₂)
    (exists_forall_preimage_subset (K := K) _ (M.finitePresentation_stage h₀ j) _ _
      ((M.isCartesian_cmp h₀).isPullback j) C₁ C₂ hC)

/-- **Emptiness of closed subsets of a stage spreads to the fibres of late stages.** -/
public lemma Model.exists_preimage_eq_empty {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀)
    (j : J) (C : TopologicalSpace.Closeds ((M.stage h₀).obj j).left)
    (hC : M.cmp h₀ j ⁻¹' C = ∅) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      M.fibreMap h₀ (h₂.trans h) t j ⁻¹' C = ∅ :=
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K S₀
  M.exists_of_ne_zero h₀ j (fun fst => fst ⁻¹' C = ∅)
    (exists_forall_preimage_eq_empty (K := K) _ (M.finitePresentation_stage h₀ j) _ _
      ((M.isCartesian_cmp h₀).isPullback j) C hC)

/-- **Dimension bounds on closed subsets of a stage spread to the fibres of late stages.** -/
public lemma Model.exists_topologicalKrullDim_preimage_le {S₀ : CoefficientModels.FGSub k₀ K}
    (h₀ : M.R ≤ S₀) (j : J) (C : TopologicalSpace.Closeds ((M.stage h₀).obj j).left) (e : ℕ)
    (hC : topologicalKrullDim (M.cmp h₀ j ⁻¹' C) ≤ e) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      topologicalKrullDim (M.fibreMap h₀ (h₂.trans h) t j ⁻¹' C) ≤ e :=
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K S₀
  M.exists_of_ne_zero h₀ j (fun fst => topologicalKrullDim (fst ⁻¹' C) ≤ e)
    (exists_forall_topologicalKrullDim_preimage_le (K := K) _ (M.finitePresentation_stage h₀ j) _ _
      ((M.isCartesian_cmp h₀).isPullback j) C e hC)

/-- **Smoothness of closed subschemes spreads to the fibres.** If the inverse image over `K` of an
ideal sheaf of a vertex at a stage cuts out a smooth subscheme, so does its inverse image in every
field-valued fibre of every late stage. -/
public lemma Model.exists_isSmoothScheme_comap {S₀ : CoefficientModels.FGSub k₀ K}
    (h₀ : M.R ≤ S₀) (j : J) (I₀ : ((M.stage h₀).obj j).left.IdealSheafData)
    (hK : Mori.IsSmoothScheme ((I₀.comap (M.cmp h₀ j)).subschemeι ≫ (X.obj j).hom)) :
    ∃ (S₂ : CoefficientModels.FGSub k₀ K) (h₂ : S₀ ≤ S₂), ∀ (S : CoefficientModels.FGSub k₀ K)
      (h : S₂ ≤ S) (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of S.1)),
      Mori.IsSmoothScheme ((I₀.comap (M.fibreMap h₀ (h₂.trans h) t j)).subschemeι ≫
        ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).hom) := by
  have : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K S₀
  have := (M.finitePresentation_stage h₀ j).1
  have := M.compactSpace_stage h₀ j
  have := M.quasiSeparatedSpace_stage h₀ j
  have : IsLocallyNoetherian ((M.stage h₀).obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((M.stage h₀).obj j).hom
  let A : Over (Spec (.of S₀.1)) := Over.mk (I₀.subschemeι ≫ ((M.stage h₀).obj j).hom)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace I₀.subschemeι
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated I₀.subschemeι
  have : LocallyOfFinitePresentation I₀.subschemeι :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  have : LocallyOfFinitePresentation A.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (I₀.subschemeι ≫ ((M.stage h₀).obj j).hom))
  -- the base change to `K`
  have hlftK := M.locallyOfFiniteType_obj j
  have : LocallyOfFinitePresentation ((I₀.comap (M.cmp h₀ j)).subschemeι ≫ (X.obj j).hom) :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  have hsq := (isPullback_comap I₀ (M.cmp h₀ j)).flip.paste_vert
    ((M.isCartesian_cmp h₀).isPullback j)
  have hA : Smooth ((Over.pullback (κ S₀.1)).obj A).hom :=
    prop_snd_of_isPullback @Smooth hsq (IsPullback.of_hasPullback A.hom (κ S₀.1))
      ((Mori.isSmoothScheme_iff _).mp hK)
  obtain ⟨S₂, h₂, H⟩ := exists_stage_smooth S₀ A hA
  refine ⟨S₂, h₂, fun S h L _ t => ?_⟩
  -- the base change to the fibre
  have hsm : Smooth (pullback.snd A.hom (t ≫ π (show S₀.1 ≤ S.1 from h₂.trans h))) := by
    have h1 := (IsPullback.of_hasPullback (pullback.snd A.hom
      (π (show S₀.1 ≤ S.1 from h₂.trans h))) t).paste_horiz
      (IsPullback.of_hasPullback A.hom (π (show S₀.1 ≤ S.1 from h₂.trans h)))
    have h2 : Smooth (pullback.snd (pullback.snd A.hom (π (show S₀.1 ≤ S.1 from h₂.trans h))) t) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ t) (H S h)
    exact prop_snd_of_isPullback @Smooth h1 (IsPullback.of_hasPullback _ _) h2
  have hsq' := (isPullback_comap I₀ (M.fibreMap h₀ (h₂.trans h) t j)).flip.paste_vert
    (M.isPullback_fibreMap h₀ (h₂.trans h) t j)
  have := M.locallyOfFiniteType_fibre (h₀.trans (h₂.trans h)) t j
  have : LocallyOfFinitePresentation ((I₀.comap (M.fibreMap h₀ (h₂.trans h) t j)).subschemeι ≫
      ((M.stage (h₀.trans (h₂.trans h)) ⋙ Over.pullback t).obj j).hom) :=
    instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType _
  exact (Mori.isSmoothScheme_iff _).mpr
    (prop_snd_of_isPullback @Smooth (IsPullback.of_hasPullback _ _) hsq' hsm)

/-- **Sections descend to a stage** (Stacks 01ZR for the structure sheaf): a section over `K` on
the preimage of a quasi-compact open `V` of a vertex at a stage `S₀` is the pullback of a section
on the preimage of `V` at a later stage. -/
public lemma Model.exists_section {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (V : ((M.stage h₀).obj j).left.Opens) (hV : IsCompact (V : Set ((M.stage h₀).obj j).left))
    (a : Γ((M.cmp h₀ j ⁻¹ᵁ V).toScheme, ⊤)) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁)
      (a₁ : Γ((M.stageCmp h₀ h₁ j ⁻¹ᵁ V).toScheme, ⊤)),
      ((M.cmp (h₀.trans h₁) j).resLE (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) (M.cmp h₀ j ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp])).appTop a₁ = a := by
  let D := CoefficientModels.specDiagram k₀ K
  let W' : Over (D.obj (Opposite.op S₀)) := Over.mk (V.ι ≫ ((M.stage h₀).obj j).hom)
  let Xo : Over (CoefficientModels.specCone k₀ K).pt :=
    Over.mk ((M.cmp h₀ j ⁻¹ᵁ V).ι ≫ (X.obj j).hom)
  have hpb : IsPullback (M.cmp h₀ j ∣_ V) Xo.hom W'.hom
      ((CoefficientModels.specCone k₀ K).π.app (Opposite.op S₀)) :=
    (AlgebraicGeometry.isPullback_morphismRestrict (M.cmp h₀ j) V).paste_vert
      ((M.isCartesian_cmp h₀).isPullback j)
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K S₀
  have := (M.finitePresentation_stage h₀ j).1
  have := (M.finitePresentation_stage h₀ j).2.1
  have := (M.finitePresentation_stage h₀ j).2.2
  have := M.compactSpace_stage h₀ j
  have : IsLocallyNoetherian ((M.stage h₀).obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((M.stage h₀).obj j).hom
  have : IsNoetherian ((M.stage h₀).obj j).left := ⟨⟩
  have hW : FinitePresentation W'.hom :=
    show FinitePresentation (V.ι ≫ ((M.stage h₀).obj j).hom) from
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : ∀ {a b : Over (Opposite.op S₀)} (f : a ⟶ b),
      IsAffineHom ((CoefficientModels.stageDiagram D W').map f) := fun f =>
    CoefficientModels.isAffineHom_stageMap D W' f
  have : ∀ a, CompactSpace ((CoefficientModels.stageDiagram D W').obj a) := fun a =>
    CoefficientModels.compactSpace_stageObj D W' hW a
  have : ∀ a, QuasiSeparatedSpace ((CoefficientModels.stageDiagram D W').obj a) := fun a =>
    CoefficientModels.quasiSeparatedSpace_stageObj D W' hW a
  obtain ⟨hcol⟩ := nonempty_isColimit_Γ_mapCocone (CoefficientModels.stageDiagram D W')
    (CoefficientModels.legCone D W' (CoefficientModels.specCone k₀ K) Xo _ hpb)
    (CoefficientModels.isLimitLegCone D W' _ _ _ hpb (CoefficientModels.isLimitSpecCone k₀ K))
  obtain ⟨m, a', ha'⟩ := Limits.Concrete.isColimit_exists_rep _ hcol a
  have h₁ : S₀ ≤ m.unop.left.unop := leOfHom m.unop.hom.unop
  let ψ : (M.stageCmp h₀ h₁ j ⁻¹ᵁ V).toScheme ⟶ CoefficientModels.stageObj D W' m.unop :=
    pullback.lift ((M.stageCmp h₀ h₁ j ⁻¹ᵁ V).ι ≫ ((M.stage (h₀.trans h₁)).obj j).hom)
      (M.stageCmp h₀ h₁ j ∣_ V) (by
        change _ = _ ≫ V.ι ≫ ((M.stage h₀).obj j).hom
        rw [morphismRestrict_ι_assoc, ((M.isCartesian_stageCmp h₀ h₁).isPullback j).w]
        exact Category.assoc _ _ _)
  have hlegψ : (M.cmp (h₀.trans h₁) j).resLE (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) (M.cmp h₀ j ⁻¹ᵁ V)
      (by rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]) ≫ ψ =
      CoefficientModels.leg D W' (CoefficientModels.specCone k₀ K) Xo _ hpb m.unop := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, CoefficientModels.leg_fst]
      erw [Scheme.Hom.resLE_comp_ι_assoc]
      exact (congrArg ((M.cmp h₀ j ⁻¹ᵁ V).ι ≫ ·)
        ((M.isCartesian_cmp (h₀.trans h₁)).isPullback j).w).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, CoefficientModels.leg_snd, ← cancel_mono V.ι,
        Category.assoc, morphismRestrict_ι, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc,
        M.cmp_stageCmp]
  refine ⟨m.unop.left.unop, h₁, ψ.appTop a', ?_⟩
  calc _ = ((M.cmp (h₀.trans h₁) j).resLE (M.stageCmp h₀ h₁ j ⁻¹ᵁ V) (M.cmp h₀ j ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, M.cmp_stageCmp]) ≫ ψ).appTop a' := by
          rw [Scheme.Hom.comp_appTop]; rfl
    _ = (CoefficientModels.leg D W' (CoefficientModels.specCone k₀ K) Xo _ hpb m.unop).appTop
          a' := by rw [hlegψ]
    _ = a := ha'

/-- Equal pullbacks along `s` give equal pullbacks along `ψ ≫ s`. -/
private lemma appTop_eq_of_comp_eq {A B C : Scheme.{u}} (ψ : A ⟶ B) (s : B ⟶ C) (w : A ⟶ C)
    (h : ψ ≫ s = w) (a b : Γ(C, ⊤)) (hab : s.appTop a = s.appTop b) :
    w.appTop a = w.appTop b := by
  subst h
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply, hab]

/-- Sections over an open `U` restricted along `f ∣_ U`. -/
private lemma topIso_inv_appTop_morphismRestrict_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (z : Γ(Y, U)) :
    (f ∣_ U).appTop (U.topIso.inv z) = (f ⁻¹ᵁ U).topIso.inv (f.app U z) := by
  have : U.topIso.inv ≫ (f ∣_ U).appTop = f.app U ≫ (f ⁻¹ᵁ U).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Iso.inv_hom_id_assoc, Scheme.Hom.appLE]
    simp
  exact congrArg (fun φ => φ.hom z) this

/-- **Equalities of sections descend to a stage**: two sections of a vertex at a stage `S₀` over a
quasi-compact open `V` with the same pullback over `K` have the same pullback at a later stage. -/
public lemma Model.exists_section_eq {S₀ : CoefficientModels.FGSub k₀ K} (h₀ : M.R ≤ S₀) (j : J)
    (V : ((M.stage h₀).obj j).left.Opens) (hV : IsCompact (V : Set ((M.stage h₀).obj j).left))
    (x y : Γ(((M.stage h₀).obj j).left, V))
    (hxy : (M.cmp h₀ j).app V x = (M.cmp h₀ j).app V y) :
    ∃ (S₁ : CoefficientModels.FGSub k₀ K) (h₁ : S₀ ≤ S₁),
      (M.stageCmp h₀ h₁ j).app V x = (M.stageCmp h₀ h₁ j).app V y := by
  let D := CoefficientModels.specDiagram k₀ K
  let W' : Over (D.obj (Opposite.op S₀)) := Over.mk (V.ι ≫ ((M.stage h₀).obj j).hom)
  let Xo : Over (CoefficientModels.specCone k₀ K).pt :=
    Over.mk ((M.cmp h₀ j ⁻¹ᵁ V).ι ≫ (X.obj j).hom)
  have hpb : IsPullback (M.cmp h₀ j ∣_ V) Xo.hom W'.hom
      ((CoefficientModels.specCone k₀ K).π.app (Opposite.op S₀)) :=
    (AlgebraicGeometry.isPullback_morphismRestrict (M.cmp h₀ j) V).paste_vert
      ((M.isCartesian_cmp h₀).isPullback j)
  have := CoefficientModels.isNoetherianRing_of_fg k₀ K S₀
  have := (M.finitePresentation_stage h₀ j).1
  have := (M.finitePresentation_stage h₀ j).2.1
  have := (M.finitePresentation_stage h₀ j).2.2
  have := M.compactSpace_stage h₀ j
  have : IsLocallyNoetherian ((M.stage h₀).obj j).left :=
    LocallyOfFiniteType.isLocallyNoetherian ((M.stage h₀).obj j).hom
  have : IsNoetherian ((M.stage h₀).obj j).left := ⟨⟩
  have hW : FinitePresentation W'.hom :=
    show FinitePresentation (V.ι ≫ ((M.stage h₀).obj j).hom) from
      ⟨inferInstance, inferInstance, inferInstance⟩
  have : ∀ {a b : Over (Opposite.op S₀)} (f : a ⟶ b),
      IsAffineHom ((CoefficientModels.stageDiagram D W').map f) := fun f =>
    CoefficientModels.isAffineHom_stageMap D W' f
  have : ∀ a, CompactSpace ((CoefficientModels.stageDiagram D W').obj a) := fun a =>
    CoefficientModels.compactSpace_stageObj D W' hW a
  have : ∀ a, QuasiSeparatedSpace ((CoefficientModels.stageDiagram D W').obj a) := fun a =>
    CoefficientModels.quasiSeparatedSpace_stageObj D W' hW a
  obtain ⟨hcol⟩ := nonempty_isColimit_Γ_mapCocone (CoefficientModels.stageDiagram D W')
    (CoefficientModels.legCone D W' (CoefficientModels.specCone k₀ K) Xo _ hpb)
    (CoefficientModels.isLimitLegCone D W' _ _ _ hpb (CoefficientModels.isLimitSpecCone k₀ K))
  let m₀ : (Over (Opposite.op S₀))ᵒᵖ := Opposite.op (Over.mk (𝟙 _))
  let sec : Γ(((M.stage h₀).obj j).left, V) →
      ToType (((CoefficientModels.stageDiagram D W').op ⋙ Scheme.Γ).obj m₀) := fun z =>
    ((pullback.snd _ _ : CoefficientModels.stageObj D W' m₀.unop ⟶ W'.left)).appTop (V.topIso.inv z)
  have hsec : ∀ z, (Scheme.Γ.mapCocone (CoefficientModels.legCone D W'
      (CoefficientModels.specCone k₀ K) Xo _ hpb).op).ι.app m₀ (sec z) =
      (M.cmp h₀ j ⁻¹ᵁ V).topIso.inv ((M.cmp h₀ j).app V z) := by
    intro z
    rw [← topIso_inv_appTop_morphismRestrict_apply]
    change (CoefficientModels.leg D W' _ Xo _ hpb m₀.unop).appTop
      (((pullback.snd _ _ : CoefficientModels.stageObj D W' m₀.unop ⟶ W'.left)).appTop _) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun φ => (Scheme.Hom.appTop φ).hom (V.topIso.inv z))
      (CoefficientModels.leg_snd D W' _ Xo _ hpb m₀.unop)
  obtain ⟨k, f, g, hfg⟩ := Limits.Concrete.isColimit_exists_of_rep_eq _ hcol (sec x) (sec y) (by
    rw [hsec, hsec, hxy])
  have hmap : ∀ (e : m₀ ⟶ k) (z : Γ(((M.stage h₀).obj j).left, V)),
      ((CoefficientModels.stageDiagram D W').op ⋙ Scheme.Γ).map e (sec z) =
        ((pullback.snd _ _ : CoefficientModels.stageObj D W' k.unop ⟶ W'.left)).appTop
            (V.topIso.inv z) := by
    intro e z
    change (CoefficientModels.stageMap D W' e.unop).appTop
      (((pullback.snd _ _ : CoefficientModels.stageObj D W' m₀.unop ⟶ W'.left)).appTop _) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun φ => (Scheme.Hom.appTop φ).hom (V.topIso.inv z))
      (CoefficientModels.stageMap_snd D W' e.unop)
  have key : ((pullback.snd _ _ : CoefficientModels.stageObj D W' k.unop ⟶ W'.left)).appTop
      (V.topIso.inv x) =
      ((pullback.snd _ _ : CoefficientModels.stageObj D W' k.unop ⟶ W'.left)).appTop
          (V.topIso.inv y) :=
    (hmap f x).symm.trans (hfg.trans (hmap g y))
  have h₁ : S₀ ≤ k.unop.left.unop := leOfHom k.unop.hom.unop
  let ψ : (M.stageCmp h₀ h₁ j ⁻¹ᵁ V).toScheme ⟶ CoefficientModels.stageObj D W' k.unop :=
    pullback.lift ((M.stageCmp h₀ h₁ j ⁻¹ᵁ V).ι ≫ ((M.stage (h₀.trans h₁)).obj j).hom)
      (M.stageCmp h₀ h₁ j ∣_ V) (by
        change _ = _ ≫ V.ι ≫ ((M.stage h₀).obj j).hom
        rw [morphismRestrict_ι_assoc, ((M.isCartesian_stageCmp h₀ h₁).isPullback j).w]
        exact Category.assoc _ _ _)
  refine ⟨k.unop.left.unop, h₁, ?_⟩
  have e : (M.stageCmp h₀ h₁ j ∣_ V).appTop (V.topIso.inv x) =
      (M.stageCmp h₀ h₁ j ∣_ V).appTop (V.topIso.inv y) := by
    have hψ : ψ ≫ (pullback.snd _ _ : CoefficientModels.stageObj D W' k.unop ⟶ W'.left) =
        M.stageCmp h₀ h₁ j ∣_ V := by
      simp only [ψ, pullback.lift_snd]
    exact appTop_eq_of_comp_eq ψ _ _ hψ _ _ key
  rw [topIso_inv_appTop_morphismRestrict_apply, topIso_inv_appTop_morphismRestrict_apply] at e
  simpa only [← CommRingCat.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (M.stageCmp h₀ h₁ j ⁻¹ᵁ V).topIso.hom.hom e

end Stages

/-! ### Module systems over a discrete index -/

section Discrete

variable {K : Type u} [Field K] {J : Type u} [SmallCategory J] (X : J ⥤ Over (Spec (.of K)))
  {ι : Type u} (v : ι → J) (𝓛 : ∀ i, (X.obj (v i)).left.Modules)

/-- The identity maps of a family of modules indexed by a discrete category. -/
@[expose] public def discreteμ : ∀ {e e' : Discrete ι} (φ : e ⟶ e'),
    𝓛 e.as ⟶ (Scheme.Modules.pullback (X.map ((Discrete.functor v).map φ)).left).obj (𝓛 e'.as)
  | ⟨_⟩, ⟨_⟩, ⟨rfl⟩ => (Scheme.Modules.pullbackId _).inv.app _ ≫
      (Scheme.Modules.pullbackCongr (by simp)).hom.app _

private lemma pullbackCongr_coherence {Z : Scheme.{u}} (f g h : Z ⟶ Z) (hf : 𝟙 Z = f)
    (hg : 𝟙 Z = g) (hh : 𝟙 Z = h) (hfg : f ≫ g = h) (M : Z.Modules) :
    (Scheme.Modules.pullbackId Z).inv.app M ≫ (Scheme.Modules.pullbackCongr hh).hom.app M =
      ((Scheme.Modules.pullbackId Z).inv.app M ≫ (Scheme.Modules.pullbackCongr hf).hom.app M) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Z).inv.app M ≫
          (Scheme.Modules.pullbackCongr hg).hom.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M ≫
          (Scheme.Modules.pullbackCongr hfg).hom.app M := by
  subst hf hg hh
  have h := Scheme.Modules.pseudofunctor_left_unitality (𝟙 Z)
  rw [Iso.inv_comp_eq] at h
  have h' := congrArg (fun φ => φ.app M) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at h'
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app, eqToHom_refl,
    Category.comp_id, Category.assoc]
  rw [← h']
  erw [NatTrans.id_app, Category.comp_id, Category.id_comp, Category.comp_id,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The identity maps of a discrete family of modules at an identity morphism. -/
public lemma discreteμ_id (e : Discrete ι) :
    discreteμ X v 𝓛 (𝟙 e) = (Scheme.Modules.pullbackId _).inv.app (𝓛 e.as) ≫
      (Scheme.Modules.pullbackCongr (by simp)).hom.app (𝓛 e.as) := by
  rcases e with ⟨i⟩
  rfl

/-- The identity maps of a discrete family of modules are compatible with composition. -/
public lemma discreteμ_comp {e e' e'' : Discrete ι} (φ : e ⟶ e') (ψ : e' ⟶ e'') :
    discreteμ X v 𝓛 (φ ≫ ψ) =
      discreteμ X v 𝓛 φ ≫ (Scheme.Modules.pullback (X.map ((Discrete.functor v).map φ)).left).map
        (discreteμ X v 𝓛 ψ) ≫ (Scheme.Modules.pullbackComp _ _).hom.app (𝓛 e''.as) ≫
        (Scheme.Modules.pullbackCongr (by simp)).hom.app (𝓛 e''.as) := by
  rcases e with ⟨i⟩
  rcases e' with ⟨i'⟩
  rcases e'' with ⟨i''⟩
  rcases φ with ⟨h⟩
  rcases ψ with ⟨h'⟩
  dsimp at h h'
  subst h h'
  exact pullbackCongr_coherence _ _ _ (by simp) (by simp) (by simp) (by simp) _

end Discrete

end

end MMP.Spreading
