module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction
public import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
public import MMP.AlgebraicGeometry.Resolution.SNCPullback
public import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
public import MMP.AlgebraicGeometry.Resolution.TransformRestriction
public import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientIdeal
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
public import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
public import MMP.AlgebraicGeometry.Resolution.SNCHypersurfaceCentres
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Cosupport
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.TuningOfIdeals
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealOrder
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.GoingUpUniqueness
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import MMP.AlgebraicGeometry.Resolution.MaximalContact.AlongBlowupSequence
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaxOrderControlledTransform
public import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion

/-!
# The order-reduction step `𝓑𝓓_{n,m,j}`: order, restriction and change of fields

Fix `N ≥ 1`, a marked order-reduction family `𝓜` on dimensions `0, …, N - 1`, `m ≥ 1` and an
index `j`. For a triple `(X, I, E)` of dimension `n` with `1 ≤ n ≤ N` and `maxord I ≤ m`,
`𝓑𝓓_{n,m,j}(X, I, E)` is empty if `maxord I < m`; otherwise, with `μ = m!` and `W = W_μ(I)`,
it is the (trivial) blow-up `π` of `Z_{-1} = Z_{-1}(W, μ, E^j)` followed by the push-forward
`τ_*𝐁_S` of `𝐁_S = 𝓜_{n-1,μ}(S, W_0𝒪_S, μ, E_S)` along the inclusion `τ` of `S = π⁻¹E^j`,
with empty blow-ups deleted.

This file proves three properties of this construction (Kollár, Lemma 3.102 and its proof).
`𝓑𝓓_{n,m,j}(X, I, E)` is a smooth blow-up sequence of order `m` starting with `(X, I, E)`,
and so is `π` followed by `τ_*𝐁_S` before deleting empty blow-ups: the first blow-up is of order
`μ` for `W`, the push-forward is of order `μ` by going up, and tuning brings the order back
to `m`. The restriction of `τ_*𝐁_S` to `S` is `𝐁_S`, and the formal transforms of `W_0` along
it restrict to the marked transforms of `(W_0𝒪_S, μ)`. Finally `𝓑𝓓` commutes with change of
fields: the projection `X_L → X` is flat and surjective with regular fibres, so it preserves
orders, maximal coefficient ideals and `Z_{-1}`, blowing up commutes with it, and (2b) of `𝓜`
compares the two values of `𝓜`.

## Main results

* `MMP.Resolution.bdFunctor_isOrderMTripleSeq`: `𝓑𝓓_{n,m,j}` is of order `m`.
* `MMP.Resolution.bdFunctor_formalTransform_restrict_eq`: restriction to `S` commutes with the
  transforms.
* `MMP.Resolution.commutesWithFieldChangeOn_bdFunctor`: `𝓑𝓓_{n,m,j}` commutes with change of
  fields.

## References

* [J. Kollár, *Lectures on resolution of singularities*][kollar2007], Lemma 3.102 and its proof
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Resolution

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local instance] Bridges.isClosedImmersion_canonicalLift

namespace BDFunctor

open MMP.Mori

/-- The kernel of the stalk map of a closed immersion at `y` is the stalk at `ι y` of its
kernel. -/
private theorem ker_stalkMap_eq_stalk_ker {S W : Scheme.{u}} (ι : S ⟶ W) [IsClosedImmersion ι]
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

/-- **Local coordinates on a smooth hypersurface `H = ι(S)` adapted to the restricted boundary.**
If `H + ∑ᵢ E^i` is an snc family, `H` the image of a closed immersion `ι : S → W`, then at every
point of `S` the inverse images `ι⁻¹E^i` through it are distinct coordinate hyperplanes. -/
private theorem exists_coordinates_comap_of_isSNCFamily {k : Type u} [Field k] {S W : Scheme.{u}}
    [IsLocallyNoetherian W] (ι : S ⟶ W) [IsClosedImmersion ι] (s : W ⟶ Spec (.of k))
    {n₀ : ℕ} (E : Fin n₀ → W.IdealSheafData)
    (hHE : IsSNCFamily s fun o : Option (Fin n₀) => o.elim ι.ker E) (y : S) :
    ∃ (m : ℕ) (w : Fin m → S.presheaf.stalk y)
      (c' : {i // y ∈ ((E i).comap ι).support} → Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk ((E i.1).comap ι) y = Ideal.span {w (c' i)}) ∧
        Function.Injective c' := by
  classical
  have hxH : ι y ∈ ((Option.elim none ι.ker E : W.IdealSheafData).support : Set W) :=
    ι.range_subset_ker_support ⟨y, rfl⟩
  obtain ⟨n, z, c, hz, hE, hc⟩ := hHE.2 (ι y)
  set J : Finset (Fin n) := {c ⟨none, hxH⟩} with hJdef
  have hZx : IdealSheafData.stalk ι.ker (ι y) = Ideal.span (z '' (J : Set (Fin n))) := by
    rw [hJdef, Finset.coe_singleton, Set.image_singleton]
    exact hE ⟨none, hxH⟩
  have := MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  obtain ⟨hreg, -, hq⟩ := MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz J
  let e : (W.presheaf.stalk (ι y) ⧸ Ideal.span (z '' (J : Set (Fin n)))) ≃+*
      S.presheaf.stalk y :=
    (Ideal.quotEquivOfEq (hZx.symm.trans (ker_stalkMap_eq_stalk_ker ι y).symm)).trans
      (RingHom.quotientKerEquivOfSurjective (ι.stalkMap_surjective y))
  have he : ∀ a, e (Ideal.Quotient.mk _ a) = (ι.stalkMap y).hom a := fun a => rfl
  have hmem : ∀ i : {i // y ∈ ((E i).comap ι).support},
      ι y ∈ ((Option.elim (some i.1) ι.ker E : W.IdealSheafData).support : Set W) :=
    fun i => (mem_support_comap_iff _ _ y).1 i.2
  have hnot : ∀ i : {i // y ∈ ((E i).comap ι).support}, c ⟨some i.1, hmem i⟩ ∈ Jᶜ := by
    intro i
    rw [Finset.mem_compl, hJdef, Finset.mem_singleton]
    intro h
    exact Option.some_ne_none _ (congrArg Subtype.val (hc h))
  let o := Jᶜ.orderIsoOfFin rfl
  refine ⟨Jᶜ.card, fun j => e (Ideal.Quotient.mk _ (z (Jᶜ.orderEmbOfFin rfl j))),
    fun i => o.symm ⟨c ⟨some i.1, hmem i⟩, hnot i⟩, hq.map_ringEquiv e, fun i => ?_, ?_⟩
  · dsimp only
    rw [IdealSheafData.stalk_comap, show IdealSheafData.stalk (E i.1) (ι y) =
        Ideal.span {z (c ⟨some i.1, hmem i⟩)} from hE ⟨some i.1, hmem i⟩, Ideal.map_span,
      Set.image_singleton, he, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · intro i j hij
    have h1 := congrArg Subtype.val (o.symm.injective hij)
    have h2 := hc h1
    exact Subtype.ext (Option.some_injective _ (congrArg Subtype.val h2))

/-- The total transform of a closed subset `A` under a blow-up is the inverse image of `A ∪ Z`. -/
private theorem totalTransformStep_eq {X : Scheme.{u}} (Z : X.IdealSheafData) {A : Set X}
    (hA : IsClosed A) :
    ClosedBlowupSequence.totalTransformStep Z A = blowUpToBase Z ⁻¹' (A ∪ Z.support) := by
  apply subset_antisymm
  · rintro y (hy | hy)
    · exact Or.inl (closure_minimal (fun y hy => hy.1) (hA.preimage (blowUpToBase Z).continuous) hy)
    · exact Or.inr hy
  · rintro y (hy | hy)
    · by_cases hyZ : blowUpToBase Z y ∈ (Z.support : Set X)
      · exact Or.inr hyZ
      · exact Or.inl (subset_closure ⟨hy, hyZ⟩)
    · exact Or.inr hy

private theorem support_comap_orderedDivisor {X Y : Scheme.{u}} (E : OrderedDivisor X)
    (f : Y ⟶ X) : (E.comap f).support = f ⁻¹' E.support := by
  ext y
  simp [OrderedDivisor.support, OrderedDivisor.comap, Scheme.IdealSheafData.support_comap]

/-- **Exchanging coordinates.** Let `A` and `B` be families of ideal sheaves with the same union
of supports, and `y` a point at which the members of `A` through `y` are distinct coordinate
hyperplanes for some regular system of parameters `v`, and the members of `B` through `y` are
coordinate hyperplanes for a regular system of parameters `w`. Then the members of `A` through
`y` are distinct coordinate hyperplanes for `w`. -/
private theorem exists_coordinates_of_iUnion_support_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ΛA ΛB : Type*} {A : ΛA → X.IdealSheafData} {B : ΛB → X.IdealSheafData}
    (hAB : (⋃ i, ((A i).support : Set X)) = ⋃ j, ((B j).support : Set X)) (y : X)
    {n : ℕ} {v : Fin n → X.presheaf.stalk y} (hv : MMP.Mori.IsRegularSystemOfParameters v)
    (d : {i // y ∈ (A i).support} → Fin n)
    (hd : ∀ i, IdealSheafData.stalk (A i.1) y = Ideal.span {v (d i)}) (hdinj : Function.Injective d)
    {m : ℕ} {w : Fin m → X.presheaf.stalk y} (hw : MMP.Mori.IsRegularSystemOfParameters w)
    (c : {j // y ∈ (B j).support} → Fin m)
    (hc : ∀ j, IdealSheafData.stalk (B j.1) y = Ideal.span {w (c j)}) :
    ∃ c' : {i // y ∈ (A i).support} → Fin m,
      (∀ i, IdealSheafData.stalk (A i.1) y = Ideal.span {w (c' i)}) ∧ Function.Injective c' := by
  have key : ∀ i : {i // y ∈ (A i).support}, ∃ j : {j // y ∈ (B j).support},
      IdealSheafData.stalk (A i.1) y = Ideal.span {w (c j)} := by
    intro i
    let P : PrimeSpectrum (X.presheaf.stalk y) :=
      ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hv (d i)⟩
    have hP : X.fromSpecStalk y P ∈ ⋃ j, ((B j).support : Set X) := by
      rw [← hAB]
      exact Set.mem_iUnion.2 ⟨i.1, (fromSpecStalk_mem_support_iff_stalk_le _ y P).2 (hd i).le⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hP
    have hyj : y ∈ (B j).support :=
      (fromSpecStalk_specializes_self y P).mem_closed (B j).support.isClosed hj
    have hjP := (fromSpecStalk_mem_support_iff_stalk_le _ y P).1 hj
    rw [hc ⟨j, hyj⟩] at hjP
    let Q : PrimeSpectrum (X.presheaf.stalk y) :=
      ⟨_, span_singleton_isPrime_of_isRegularSystemOfParameters hw (c ⟨j, hyj⟩)⟩
    have hQ : X.fromSpecStalk y Q ∈ ⋃ i, ((A i).support : Set X) := by
      rw [hAB]
      exact Set.mem_iUnion.2 ⟨j, (fromSpecStalk_mem_support_iff_stalk_le _ y Q).2
        (hc ⟨j, hyj⟩).le⟩
    obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hQ
    have hyl : y ∈ (A l).support :=
      (fromSpecStalk_specializes_self y Q).mem_closed (A l).support.isClosed hl
    have hlQ := (fromSpecStalk_mem_support_iff_stalk_le _ y Q).1 hl
    rw [hd ⟨l, hyl⟩] at hlQ
    have hdl : d ⟨l, hyl⟩ = d i := by
      by_contra hne
      exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hv (Ne.symm hne)
        (hjP (hlQ (Ideal.subset_span rfl)))
    refine ⟨⟨j, hyj⟩, ?_⟩
    rw [hd i]
    refine le_antisymm ?_ hjP
    rw [← hdl]
    exact hlQ
  choose j hj using key
  refine ⟨fun i => c (j i), hj, fun i₁ i₂ h => ?_⟩
  have h1 : Ideal.span {v (d i₁)} = Ideal.span {v (d i₂)} := by
    rw [← hd, ← hd, hj, hj]
    exact congrArg (fun a => Ideal.span {w a}) h
  apply hdinj
  by_contra hne
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hv hne
    (by rw [h1]; exact Ideal.subset_span rfl)

/-- **Snc inside the image of a closed immersion lifts** (the argument of
`MMP.Resolution.Kollar.hasSNCWith_cons_of_hasSNCWith_comap`, for a closed immersion
`ι : S → X` with image `H`). If `H + ∑ᵢ E^i` is an snc family, `Z ⊆ X` a closed subscheme
contained in `H` (that is, `ker ι ≤ Z`) and `ι⁻¹Z` has simple normal crossings with `ι⁻¹E`,
then `Z` has simple normal crossings with `E`. -/
private theorem hasSNCWith_of_hasSNCWith_comap {k : Type u} [Field k] {S X : Scheme.{u}}
    [IsLocallyNoetherian X] (ι : S ⟶ X) [IsClosedImmersion ι] (sX : X ⟶ Spec (.of k))
    {n₀ : ℕ} (E : Fin n₀ → X.IdealSheafData)
    (hHE : IsSNCFamily sX fun o : Option (Fin n₀) => o.elim ι.ker E)
    (Z : X.IdealSheafData) (hZH : ι.ker ≤ Z)
    (hZ : HasSNCWith (fun i => (E i).comap ι) (Z.comap ι)) :
    HasSNCWith E Z := by
  intro x hx
  have hxH : x ∈ (ι.ker.support : Set X) := Scheme.IdealSheafData.support_antitone hZH hx
  have hr : (ι.ker.support : Set X) = Set.range ι :=
    Stacks.AffineClosedUnion.support_ker_eq_range ι
  obtain ⟨y, rfl⟩ : x ∈ Set.range ι := hr ▸ hxH
  have hyZ : y ∈ ((Z.comap ι).support : Set S) := (mem_support_comap_iff _ _ y).2 hx
  obtain ⟨n, w, c', J', hw, hwE, hwinj, hwZ⟩ := hZ y hyZ
  obtain ⟨n₁, z₀, c₀, hz₀, hz₀E, hz₀inj⟩ := hHE.2 (ι y)
  have hx0 : ι y ∈ ((Option.elim none ι.ker E : X.IdealSheafData).support : Set X) := hxH
  set φ := (ι.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := ι.stalkMap_surjective y
  have hker : RingHom.ker φ = Ideal.span {z₀ (c₀ ⟨none, hx0⟩)} := by
    rw [hφdef, ker_stalkMap_eq_stalk_ker]
    exact hz₀E ⟨none, hx0⟩
  have hsupp : ∀ i, y ∈ ((E i).comap ι).support ↔ ι y ∈ (E i).support :=
    fun i => mem_support_comap_iff _ _ y
  have hxs : ∀ i : {i : Fin n₀ // y ∈ ((E i).comap ι).support},
      ι y ∈ ((Option.elim (some i.1) ι.ker E : X.IdealSheafData).support : Set X) :=
    fun i => (hsupp i.1).1 i.2
  have hE : ∀ i ∈ (Set.univ : Set {i : Fin n₀ // y ∈ ((E i).comap ι).support}),
      Ideal.span {w (c' i)} = (Ideal.span {z₀ (c₀ ⟨some i.1, hxs i⟩)}).map φ := by
    intro i _
    rw [← hwE i]
    show IdealSheafData.stalk ((E i.1).comap ι) y = _
    rw [IdealSheafData.stalk_comap]
    exact congrArg (Ideal.map φ) (hz₀E ⟨some i.1, hxs i⟩)
  have hinj : ∀ i ∈ (Set.univ : Set {i : Fin n₀ // y ∈ ((E i).comap ι).support}),
      ∀ i' ∈ (Set.univ : Set {i : Fin n₀ // y ∈ ((E i).comap ι).support}),
      c' i = c' i' → i = i' :=
    fun i _ i' _ h => hwinj h
  obtain ⟨t, ht, ht0, htφ, htE⟩ := MMP.Mori.exists_lift_isRegularSystemOfParameters φ hφ hz₀
    (c₀ ⟨none, hx0⟩) hker hw c' (fun i => z₀ (c₀ ⟨some i.1, hxs i⟩)) _ hE hinj
  refine ⟨n + 1, t, fun i => (c' ⟨i.1, (hsupp i.1).2 i.2⟩).succ,
    insert 0 (J'.image Fin.succ), ht, ?_, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    rw [htE ⟨i, (hsupp i).2 hi⟩ trivial]
    exact hz₀E ⟨some i, hi⟩
  · rintro ⟨i, hi⟩ ⟨i', hi'⟩ h
    have := congrArg Subtype.val (hwinj (Fin.succ_injective _ h))
    exact Subtype.ext this
  · have h1 : IdealSheafData.stalk Z (ι y) =
        Ideal.comap φ (Ideal.span (w '' (J' : Set (Fin n)))) := by
      rw [← hwZ, IdealSheafData.stalk_comap, Ideal.comap_map_of_surjective φ hφ]
      have h3 : IdealSheafData.stalk ι.ker (ι y) ≤ IdealSheafData.stalk Z (ι y) :=
        stalk_le_stalk_of_le hZH _
      have h4 : Ideal.comap φ ⊥ = IdealSheafData.stalk ι.ker (ι y) := by
        rw [← ker_stalkMap_eq_stalk_ker]; rfl
      rw [h4]
      exact (sup_eq_left.mpr h3).symm
    rw [h1]
    have h5 : w '' (J' : Set (Fin n)) = φ '' ((fun k => t k.succ) '' (J' : Set (Fin n))) := by
      rw [Set.image_image]
      simp only [htφ]
    have hk : Ideal.comap φ ⊥ = Ideal.span {z₀ (c₀ ⟨none, hx0⟩)} := hker
    rw [h5, ← Ideal.map_span, Ideal.comap_map_of_surjective φ hφ, hk, ← ht0, ← Ideal.span_union]
    congr 1
    ext a
    simp only [Finset.coe_insert, Finset.coe_image, Set.image_insert_eq, Set.image_image,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto

private theorem closure_preimage_compl_support_eq_univ {X : Scheme.{u}} (Z : X.IdealSheafData) :
    closure (blowUpToBase Z ⁻¹' (Z.support : Set X)ᶜ) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨Y, hY, hxY⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
    isIrreducible_singleton
  have hYc : IsClosed Y := isClosed_of_mem_irreducibleComponents Y hY
  have hgen := (hY.1 : IsIrreducible Y).isGenericPoint_genericPoint_closure
  rw [hYc.closure_eq] at hgen
  set η := (hY.1 : IsIrreducible Y).genericPoint
  have hη : η ∈ genericPoints (blowUp Z) := by
    show closure {η} ∈ irreducibleComponents (blowUp Z)
    rw [hgen.def]
    exact hY
  obtain ⟨-, hZ⟩ := (bijOn_genericPoints_blowUpToBase Z).1 hη
  have hηV : η ∈ blowUpToBase Z ⁻¹' (Z.support : Set X)ᶜ := fun h =>
    hZ (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2 h)
  have hxη : x ∈ closure {η} := by rw [hgen.def]; exact hxY rfl
  exact closure_mono (Set.singleton_subset_iff.2 hηV) hxη

/-- **The image of the strict transform.** For a closed immersion `j : S → X` and a closed
subscheme `Z ⊆ X`, the image of the canonical lift `B_{j⁻¹Z}S → B_ZX` is the closure of
`π⁻¹(j(S) ∖ Z)`. -/
private theorem range_canonicalLift_eq_closure {S X : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] (Z : X.IdealSheafData) :
    Set.range (canonicalLift j Z) =
      closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X))) := by
  set f := canonicalLift j Z with hf
  set T : Set (blowUp Z) := blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)) with hT
  have hsq : ∀ v, blowUpToBase Z (f v) = j (blowUpToBase (Z.comap j) v) := fun v ↦ by
    rw [← Scheme.Hom.comp_apply, hf, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  have : IsClosedImmersion f := Bridges.isClosedImmersion_canonicalLift j Z
  set V : Set (blowUp (Z.comap j)) :=
    blowUpToBase (Z.comap j) ⁻¹' ((Z.comap j).support : Set S)ᶜ with hV
  have hVdense : closure V = Set.univ := closure_preimage_compl_support_eq_univ (Z.comap j)
  have himage : f '' V = T := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨_, (hsq v).symm⟩, ?_⟩
      rw [hsq v]
      simpa [hV] using hv
    · rintro ⟨⟨s, hs⟩, hyZ⟩
      have hs' : s ∉ ((Z.comap j).support : Set S) := by
        simpa [hs] using hyZ
      obtain ⟨v, hv⟩ := exists_blowUpToBase_eq_of_notMem_support (Z.comap j) hs'
      refine ⟨v, by simpa [hV, hv] using hs', ?_⟩
      have hfv : blowUpToBase Z (f v) = blowUpToBase Z y := by rw [hsq v, hv, hs]
      exact blowUpToBase_injective_of_notMem_support Z (by rwa [hfv]) hfv
  apply subset_antisymm
  · rw [← Set.image_univ, ← hVdense, ← himage]
    exact image_closure_subset_closure_image f.continuous
  · rw [← himage]
    exact closure_minimal (Set.image_subset_range _ _) f.isClosedEmbedding.isClosed_range

/-- For a closed immersion `j : S → X` of a reduced scheme, the kernel of the canonical lift is the
reduced ideal of the closure of `π⁻¹(j(S) ∖ Z)`. -/
private theorem ker_canonicalLift_eq_vanishingIdeal {S X : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] [IsReduced S] (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = Scheme.IdealSheafData.vanishingIdeal
      (.closure (blowUpToBase Z ⁻¹' (Set.range j \ (Z.support : Set X)))) := by
  have : IsReduced (blowUp (Z.comap j)) := isReduced_blowUp (Z.comap j)
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range, range_canonicalLift_eq_closure]
  congr 1
  exact TopologicalSpace.Closeds.ext (by
    rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure,
      closure_closure])

/-- A centre having snc with the restricted boundary pushes forward to a centre having snc with
the ambient boundary. -/
private theorem hasSNCWith_map {k : Type u} [Field k] {S W : Scheme.{u}} (ι : S ⟶ W)
    [IsClosedImmersion ι] (s : W ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (E' : OrderedDivisor W)
    (hfam : IsSNCFamily s fun o : Option (Fin E'.s) => o.elim ι.ker E'.E)
    {ES : OrderedDivisor S} (hES : ES.support = (E'.comap ι).support) {Z : S.IdealSheafData}
    (hZ : HasSNCWith ES.E Z) :
    HasSNCWith E'.E (Z.map ι) := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian ι
  have hZ' : HasSNCWith (fun i => (E'.E i).comap ι) Z := by
    intro y hy
    obtain ⟨n, w, c', J, hw, hwE, -, hwZ⟩ := hZ y hy
    obtain ⟨m, v, d, hv, hvE, hd⟩ :=
      exists_coordinates_comap_of_isSNCFamily ι s E'.E hfam y
    obtain ⟨c'', hc'', hinj⟩ := exists_coordinates_of_iUnion_support_eq
      (A := fun i => (E'.E i).comap ι) (B := ES.E) hES.symm y hv d hvE hd hw c' hwE
    exact ⟨n, w, c'', J, hw, hc'', hinj, hwZ⟩
  have h := Z.comap_map_of_isClosedImmersion ι
  exact hasSNCWith_of_hasSNCWith_comap ι s E'.E hfam (Z.map ι)
    (Scheme.Hom.le_ker_comp Z.subschemeι ι) (h.symm ▸ hZ')

/-- Let `H` be a closed subset of pure codimension one of a noetherian scheme and `Z ⊆ H` a closed
subset no irreducible component of which is an irreducible component of `H`. Then every
irreducible component of `Z` has codimension at least two. -/
private theorem two_le_codimension_of_mem_componentsOf {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    {H Z : TopologicalSpace.Closeds X} (hH1 : MMP.Mori.IsPureCodimOne H) (hZH : (Z : Set X) ⊆ H)
    (hcomp : ∀ W ∈ componentsOf (Z : Set X), W ∉ componentsOf (H : Set X)) {W : Set X}
    (hW : W ∈ componentsOf (Z : Set X)) : 2 ≤ codimension (irreducibleClosure hW.1.1) := by
  classical
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf Z.isClosed hW
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf H.isClosed
  obtain ⟨H', hH'mem, hWH'⟩ : ∃ H' ∈ componentsOf (H : Set X), W ⊆ H' := by
    obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1 hfin.toFinset
      (fun z hz => Aux.isClosed_of_mem_componentsOf H.isClosed (hfin.mem_toFinset.mp hz))
      (by rw [hfin.coe_toFinset]; exact hW.1.2.trans (hZH.trans hcov))
    exact ⟨z, hfin.mem_toFinset.mp hz, hWz⟩
  have hne : W ≠ H' := fun h => hcomp W hW (h ▸ hH'mem)
  have hH'c : IsClosed H' := Aux.isClosed_of_mem_componentsOf H.isClosed hH'mem
  let C' : TopologicalSpace.IrreducibleCloseds X := ⟨H', hH'mem.1.1, hH'c⟩
  have hC' : codimension C' = 1 :=
    hH1 C' ⟨hH'mem.1.2, fun W' hW' hle => hH'mem.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hlt : irreducibleClosure hW.1.1 < C' := by
    refine lt_of_le_of_ne ?_ ?_
    · show closure W ⊆ H'
      rw [hWc.closure_eq]
      exact hWH'
    · intro h
      apply hne
      have := congrArg (fun C : TopologicalSpace.IrreducibleCloseds X => (C : Set X)) h
      simpa [irreducibleClosure, hWc.closure_eq, C'] using this
  have := Order.coheight_add_one_le hlt
  rw [codimension_eq_coheight] at hC' ⊢
  rw [hC'] at this
  exact le_trans (by norm_num) this

/-- If every irreducible component of `Z` has codimension at least two, then the union of the
components of codimension at least two is `Z` itself. -/
private theorem componentsOfCodimAtLeastTwo_eq_self {X : Scheme.{u}} {Z : Set X}
    (h2 : ∀ W (hW : W ∈ componentsOf Z), 2 ≤ codimension (irreducibleClosure hW.1.1)) :
    componentsOfCodimAtLeastTwo Z = Z := by
  ext x
  rw [mem_componentsOfCodimAtLeastTwo]
  refine ⟨fun ⟨_, hW, _, hx⟩ => hW.1.2 hx, fun hx => ?_⟩
  obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hx
  exact ⟨W, hW, h2 W hW, hxW⟩

/-- The reindexing `Fin (n + 1) → Fin n ⊕ Unit` sending the last index to the exceptional
entry and `castSucc i` to the `i`-th transform. -/
private abbrev lastToInr (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  finSuccEquivLast.trans (Equiv.optionEquivSumPUnit _)

/-- When every irreducible component of the centre `Z ⊆ ι(S)` has codimension at least two, the
family `(B_Z(ι S), π⁻¹_tot(E))` is the family of transforms of the members of `ι(S) + ∑ᵢ E^i`
followed by the exceptional divisor, reindexed. -/
private theorem cons_ker_canonicalLift_totalTransform_eq {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsReduced S] (E : OrderedDivisor X)
    (Z : X.IdealSheafData)
    [IsReduced (Z.comap (blowUpToBase Z)).subscheme]
    (hEpure : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support)
    (h2 : ∀ W (hW : W ∈ componentsOf (Z.support : Set X)),
      2 ≤ codimension (irreducibleClosure hW.1.1)) :
    ∀ i : Fin (E.s + 1 + 1), Fin.cons (α := fun _ => (blowUp Z).IdealSheafData)
        (canonicalLift ι Z).ker (E.totalTransform Z).E i =
      blowUpTransformFamily (Fin.cons (α := fun _ => X.IdealSheafData) ι.ker E.E) Z
        (lastToInr _ i) := by
  have hunion : (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
      (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W) =
      blowUpToBase Z ⁻¹' (Z.support : Set X) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
    refine ⟨fun ⟨_, hW, _, hy⟩ => hW.1.2 hy, fun hy => ?_⟩
    obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hy
    exact ⟨W, hW, fun hWE =>
      OrderedDivisor.not_two_le_codimension_of_mem_componentsOf E hEpure hWE (h2 W hW), hxW⟩
  intro i
  induction i using Fin.lastCases with
  | last =>
    have hcl : TopologicalSpace.Closeds.closure (blowUpToBase Z ⁻¹' (Z.support : Set X)) =
        (Z.comap (blowUpToBase Z)).support :=
      TopologicalSpace.Closeds.ext (by
        rw [TopologicalSpace.Closeds.coe_closure, Scheme.IdealSheafData.support_comap]
        exact (Z.support.isClosed.preimage (blowUpToBase Z).continuous).closure_eq)
    rw [Equiv.trans_apply, finSuccEquivLast_last, Equiv.optionEquivSumPUnit_none]
    show (E.totalTransform Z).E (Fin.last E.s) = _
    simp only [OrderedDivisor.totalTransform, Fin.snoc_last, hunion, hcl,
      MMP.Mori.vanishingIdeal_support_eq_self, blowUpTransformFamily, Sum.elim_inr]
  | cast j =>
    rw [Equiv.trans_apply, finSuccEquivLast_castSucc, Equiv.optionEquivSumPUnit_some]
    induction j using Fin.cases with
    | zero =>
      simp only [blowUpTransformFamily, Sum.elim_inl, Fin.castSucc_zero, Fin.cons_zero,
        ker_canonicalLift_eq_vanishingIdeal]
      rw [Stacks.AffineClosedUnion.support_ker_eq_range ι]
      rfl
    | succ m =>
      simp only [blowUpTransformFamily, Sum.elim_inl, Fin.cons_succ, ← Fin.succ_castSucc]
      show (E.totalTransform Z).E (Fin.castSucc m) = _
      simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc,
        componentsOfCodimAtLeastTwo_eq_self h2]

/-- The `Fin.cons` form of an snc family indexed by `Option`. -/
private theorem isSNCFamily_cons_of_option {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (H : X.IdealSheafData) (E : OrderedDivisor X)
    (h : IsSNCFamily s fun o : Option (Fin E.s) => o.elim H E.E) :
    IsSNCFamily s (Fin.cons (α := fun _ => X.IdealSheafData) H E.E) := by
  have := h.comp (finSuccEquiv E.s) (finSuccEquiv E.s).injective
  convert this using 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- **The transform of `ι(S) + ∑ᵢ E^i` stays snc** under the blow-up of a centre `Z ⊆ ι(S)` having
snc with `E`, no component of which is a component of `ι(S)`. -/
private theorem isSNCFamily_transform {k : Type u} [Field k] [CharZero k] {S X : Scheme.{u}}
    (ι : S ⟶ X) [IsClosedImmersion ι] [IsReduced S] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] (E' : OrderedDivisor X)
    (hfam : IsSNCFamily sX fun o : Option (Fin E'.s) => o.elim ι.ker E'.E)
    (Z : X.IdealSheafData) (hZH : ι.ker ≤ Z) (hZ : HasSNCWith E'.E Z)
    (hZcomp : ∀ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf (ι.ker.support : Set X)) :
    IsSNCFamily (blowUpToBase Z ≫ sX) fun o : Option (Fin (E'.totalTransform Z).s) =>
      o.elim (canonicalLift ι Z).ker (E'.totalTransform Z).E := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  have hcons := isSNCFamily_cons_of_option ι.ker E' hfam
  have hZcons := Kollar.hasSNCWith_cons_of_hasSNCWith sX E' ι.ker hcons Z hZH hZ
  have h := isSNCFamily_blowUpTransformFamily sX hcons hZcons
  have hred : IsReduced (Z.comap (blowUpToBase Z)).subscheme := (h.1 (Sum.inr ())).1
  have h2 : ∀ W (hW : W ∈ componentsOf (Z.support : Set X)),
      2 ≤ codimension (irreducibleClosure hW.1.1) := fun W hW =>
    two_le_codimension_of_mem_componentsOf (H := ι.ker.support) (Z := Z.support)
      (hfam.1 none).2.1 (Scheme.IdealSheafData.support_antitone hZH) hZcomp hW
  have hEpure : ∀ i, MMP.Mori.IsPureCodimOne (E'.E i).support := fun i => (hfam.1 (some i)).2.1
  have hfun := cons_ker_canonicalLift_totalTransform_eq ι E' Z hEpure h2
  have h3 := h.comp (fun o : Option (Fin (E'.s + 1)) =>
    lastToInr _ ((finSuccEquiv _).symm o))
    fun _ _ hab => (finSuccEquiv _).symm.injective ((lastToInr _).injective hab)
  have hfeq : (fun o : Option (Fin (E'.totalTransform Z).s) =>
      o.elim (canonicalLift ι Z).ker (E'.totalTransform Z).E) =
      blowUpTransformFamily (Fin.cons (α := fun _ => X.IdealSheafData) ι.ker E'.E) Z ∘
        (fun o : Option (Fin (E'.s + 1)) => lastToInr _ ((finSuccEquiv _).symm o)) := by
    funext o
    cases o with
    | none => exact hfun 0
    | some i => exact hfun i.succ
  exact hfeq ▸ h3

/-- The unit ideal sheaf is nonzero at the generic points. -/
private theorem isNonzeroAtGenericPoints_top {X : Scheme.{u}} :
    IsNonzeroAtGenericPoints (⊤ : X.IdealSheafData) := by
  intro η _ h
  have : IdealSheafData.stalk (⊤ : X.IdealSheafData) η = ⊤ := by
    rw [IdealSheafData.stalk_eq_top_iff_notMem_support]
    intro h
    exact Set.notMem_empty η (by simpa using (show η ∈ ((⊥ : TopologicalSpace.Closeds X) : Set X)
        from h))
  rw [h] at this
  exact bot_ne_top this

/-- The support of the total transform of `E`, split along a closed immersion `ι` with
`ι(S) ⊆ Supp E`. -/
private theorem support_totalTransform_split {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] [IsReduced S] (E E' : OrderedDivisor X)
    (hEpure : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support)
    (hE'pure : ∀ i, MMP.Mori.IsPureCodimOne (E'.E i).support)
    (hsupp : E.support = (ι.ker.support : Set X) ∪ E'.support) (Z : X.IdealSheafData) :
    (E.totalTransform Z).support =
      ((canonicalLift ι Z).ker.support : Set (blowUp Z)) ∪ (E'.totalTransform Z).support := by
  have hEc : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
  have hE'c : IsClosed E'.support := isClosed_iUnion_of_finite fun i => (E'.E i).support.isClosed
  have hker : (ι.ker.support : Set X) = Set.range ι :=
    Stacks.AffineClosedUnion.support_ker_eq_range ι
  have hker1 : ((canonicalLift ι Z).ker.support : Set (blowUp Z)) =
      closure (blowUpToBase Z ⁻¹' (Set.range ι \ (Z.support : Set X))) := by
    rw [Scheme.Hom.support_ker, (canonicalLift ι Z).isClosedEmbedding.isClosed_range.closure_eq,
      range_canonicalLift_eq_closure]
  rw [OrderedDivisor.support_totalTransform E hEpure, OrderedDivisor.support_totalTransform E'
      hE'pure,
    totalTransformStep_eq _ hEc, totalTransformStep_eq _ hE'c, hker1, hsupp, hker]
  have hAc : IsClosed (Set.range ι) := ι.isClosedEmbedding.isClosed_range
  ext x
  simp only [Set.mem_preimage, Set.mem_union]
  constructor
  · rintro ((h | h) | h)
    · by_cases hz : blowUpToBase Z x ∈ (Z.support : Set X)
      · exact Or.inr (Or.inr hz)
      · exact Or.inl (subset_closure ⟨h, hz⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl
        (closure_minimal (fun y hy => hy.1) (hAc.preimage (blowUpToBase Z).continuous) h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- A component of the image of the centre is not a component of the closed subscheme, when the
centre has components of positive codimension in the subscheme. -/
private theorem notMem_componentsOf_map {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (Z : S.IdealSheafData) (hZ : HasComponentsOfPositiveCodim (Z.support : Set S)) :
    ∀ W ∈ componentsOf ((Z.map ι).support : Set X), W ∉ componentsOf (ι.ker.support : Set X) := by
  intro W hW hWH
  have hsupp : ((Z.map ι).support : Set X) = ι '' Z.support := by
    rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure,
      (ι.isClosedEmbedding.isClosedMap _ Z.support.isClosed).closure_eq]
  have hker : (ι.ker.support : Set X) = Set.range ι :=
    Stacks.AffineClosedUnion.support_ker_eq_range ι
  have hWsub : W ⊆ Set.range ι := hker ▸ hWH.1.2
  have himg : ι '' (ι ⁻¹' W) = W := Set.image_preimage_eq_of_subset hWsub
  have hirr : IsIrreducible (ι ⁻¹' W) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hW.1.1.nonempty
      obtain ⟨s, rfl⟩ := hWsub hx
      exact ⟨s, hx⟩
    · intro u v hu hv ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨U, hU, rfl⟩ := ι.isEmbedding.isInducing.isOpen_iff.1 hu
      obtain ⟨V, hV, rfl⟩ := ι.isEmbedding.isInducing.isOpen_iff.1 hv
      obtain ⟨z, hzW, hzU, hzV⟩ := hW.1.1.isPreirreducible U V hU hV ⟨ι a, ha.1, ha.2⟩
        ⟨ι b, hb.1, hb.2⟩
      obtain ⟨s, rfl⟩ := hWsub hzW
      exact ⟨s, hzW, hzU, hzV⟩
  have hcomp : ι ⁻¹' W ∈ componentsOf (Z.support : Set S) := by
    refine ⟨⟨hirr, fun s hs => ?_⟩, fun V hV hle => ?_⟩
    · have : ι s ∈ ((Z.map ι).support : Set X) := hW.1.2 hs
      rw [hsupp] at this
      obtain ⟨t, ht, hts⟩ := this
      exact (ι.isEmbedding.injective hts) ▸ ht
    · intro s hs
      have hV' : IsIrreducible (ι '' V) := hV.1.image ι ι.continuous.continuousOn
      have h1 : ι '' V ⊆ ((Z.map ι).support : Set X) := by
        rw [hsupp]; exact Set.image_mono hV.2
      have h2 : W ⊆ ι '' V := by
        rw [← himg]; exact Set.image_mono hle
      exact hW.2 ⟨hV', h1⟩ h2 ⟨s, hs, rfl⟩
  have hpos := hZ _ hcomp
  have hmax : codimension (irreducibleClosure hcomp.1.1) = 0 := by
    rw [codimension, Order.coheight_eq_zero]
    intro V hV
    show (V : Set S) ⊆ closure (ι ⁻¹' W)
    intro s hs
    have hV' : IsIrreducible (ι '' (V : Set S)) := V.isIrreducible.image ι ι.continuous.continuousOn
    have h1 : ι '' (V : Set S) ⊆ ((ι.ker.support : Set X)) := by
      rw [hker]; exact (Set.image_subset_range _ _)
    have h2 : W ⊆ ι '' (V : Set S) := by
      rw [← himg]
      refine Set.image_mono ?_
      exact (subset_closure.trans hV)
    have h3 := hWH.2 ⟨hV', h1⟩ h2 ⟨s, hs, rfl⟩
    exact subset_closure h3
  rw [hmax] at hpos
  exact absurd hpos (by decide)

/-- Along a blow-up sequence, every centre has simple normal crossings with the total transform of
the divisor. -/
private def CentersHaveSNCWithDivisor {k : Type u} [Field k] :
    ∀ {Y : Scheme.{u}}, (Y ⟶ Spec (.of k)) → OrderedDivisor Y → ClosedBlowupSequence Y → Prop
  | _, _, _, .nil _ => True
  | _, s, E, .cons Z B =>
    HasSNCWith E.E Z ∧ CentersHaveSNCWithDivisor (blowUpToBase Z ≫ s) (E.totalTransform Z) B

private theorem iUnion_support_cons_eq {X : Scheme.{u}} (H : X.IdealSheafData)
    (E' : OrderedDivisor X) :
    (⋃ i, ((Fin.cons (α := fun _ => X.IdealSheafData) H E'.E i).support : Set X)) =
      (H.support : Set X) ∪ E'.support := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union, OrderedDivisor.support]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero => exact Or.inl hi
    | succ i => exact Or.inr ⟨i, hi⟩
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, h⟩
    · exact ⟨i.succ, hi⟩

private theorem centersHaveSNCWithDivisor_of_isPushforward {k : Type u} [Field k] [CharZero k]
    {S : Scheme.{u}}
    (BS : ClosedBlowupSequence S) :
    ∀ {Y : Scheme.{u}} (ι : S ⟶ Y) [IsClosedImmersion ι] (BY : ClosedBlowupSequence Y),
      ClosedBlowupSequence.IsPushforward ι BS BY →
      ∀ (sY : Y ⟶ Spec (.of k)) (J : Y.IdealSheafData) (E E' : OrderedDivisor Y),
        IsTriple sY J E →
        IsSNCFamily sY (fun o : Option (Fin E'.s) => o.elim ι.ker E'.E) →
        E.support = (ι.ker.support : Set Y) ∪ E'.support →
        ∀ (a : MarkedIdeal S) (ES : OrderedDivisor S), ES.support = (E'.comap ι).support →
        BS.IsOrderGeMarkedTripleSeq (ι ≫ sY) a ES → CentersHaveSNCWithDivisor sY E BY := by
  induction BS with
  | nil S =>
    intro Y ι _ BY hP sY J E E' hT hfam hsupp a ES hES hBS
    cases BY with
    | nil => trivial
    | cons ZX BX => exact hP.elim
  | cons ZS BS ih =>
    intro Y ι _ BY hP sY J E E' hT hfam hsupp a ES hES hBS
    cases BY with
    | nil => exact hP.elim
    | cons ZX BX =>
      obtain ⟨hc, hm, hP'⟩ := hP
      subst hc
      obtain ⟨hTS, hZSsm, hZSpos, hZSsnc, -, hBS'⟩ := hBS
      have hT' := hT
      obtain ⟨hchar, hsm, hlft, hqc, hequi, hJ, hEsnc⟩ := hT
      obtain ⟨-, -, -, -, -, -, hESsnc⟩ := hTS
      haveI := hchar
      haveI := hlft
      haveI := hqc
      haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      haveI : IsReduced ι.ker.subscheme := (hfam.1 none).1
      haveI := isReduced_of_isOpenImmersion ι.toImage
      have h1 : HasSNCWith E'.E ZX := by
        have := hasSNCWith_map ι sY E' hfam hES hZSsnc
        rwa [← hm] at this
      have hZH : ι.ker ≤ ZX := by
        conv_rhs => rw [hm]
        exact Scheme.Hom.le_ker_comp _ ι
      have hcons := isSNCFamily_cons_of_option ι.ker E' hfam
      have h2 : HasSNCWith E.E ZX := by
        have hZc := Kollar.hasSNCWith_cons_of_hasSNCWith sY E' ι.ker hcons ZX hZH h1
        have hAB : (⋃ i, ((E.E i).support : Set Y)) =
            ⋃ i, ((Fin.cons (α := fun _ => Y.IdealSheafData) ι.ker E'.E i).support : Set Y) := by
          rw [iUnion_support_cons_eq]; exact hsupp
        intro x hx
        obtain ⟨n, w, c, J', hw, hc, hinj, hJ'⟩ := hZc x hx
        obtain ⟨n₁, z, cE, hz, hzE, hzinj⟩ := hEsnc.2.2 x
        obtain ⟨c'', hc'', hinj''⟩ := exists_coordinates_of_iUnion_support_eq hAB x hz cE hzE
          hzinj hw c hc
        exact ⟨n, w, c'', J', hw, hc'', hinj'', hJ'⟩
      have hZcomp : ∀ W ∈ componentsOf (ZX.support : Set Y),
          W ∉ componentsOf (ι.ker.support : Set Y) := by
        have := notMem_componentsOf_map ι (ZX.comap ι) hZSpos
        rwa [← hm] at this
      simp only [eqToHom_refl, Category.id_comp] at hP'
      have hT₁ : IsTriple (blowUpToBase ZX ≫ sY) (⊤ : (blowUp ZX).IdealSheafData)
          (E.totalTransform ZX) :=
        isTriple_blowUp_totalTransform hT' h2 isNonzeroAtGenericPoints_top
      have hfam₁ := isSNCFamily_transform ι sY E' hfam ZX hZH h1 hZcomp
      have hEpure : ∀ i, MMP.Mori.IsPureCodimOne (E.E i).support := fun i => (hEsnc.2.1 i).2.1
      have hE'pure : ∀ i, MMP.Mori.IsPureCodimOne (E'.E i).support :=
        fun i => (hfam.1 (some i)).2.1
      have hESpure : ∀ i, MMP.Mori.IsPureCodimOne (ES.E i).support := fun i => (hESsnc.2.1 i).2.1
      have hsupp₁ := support_totalTransform_split ι E E' hEpure hE'pure hsupp ZX
      have hE'c : IsClosed E'.support :=
        isClosed_iUnion_of_finite fun i => (E'.E i).support.isClosed
      have hESc : IsClosed ES.support :=
        isClosed_iUnion_of_finite fun i => (ES.E i).support.isClosed
      have hES₁ : (ES.totalTransform (ZX.comap ι)).support =
          ((E'.totalTransform ZX).comap (canonicalLift ι ZX)).support := by
        rw [OrderedDivisor.support_totalTransform ES hESpure, support_comap_orderedDivisor,
          OrderedDivisor.support_totalTransform E' hE'pure, totalTransformStep_eq _ hESc,
          totalTransformStep_eq _ hE'c, hES]
        ext y
        simp only [Set.mem_preimage, Set.mem_union, TopologicalSpace.Closeds.coe_preimage,
          support_comap_orderedDivisor, Scheme.IdealSheafData.support_comap]
        have hh : blowUpToBase ZX (canonicalLift ι ZX y) = ι (blowUpToBase (ZX.comap ι) y) := by
          rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
        rw [hh]
      refine ⟨h2, ?_⟩
      have e : canonicalLift ι ZX ≫ blowUpToBase ZX ≫ sY =
          blowUpToBase (ZX.comap ι) ≫ ι ≫ sY := by
        rw [← Category.assoc, canonicalLift_comp_blowUpToBase, Category.assoc]
      exact ih (canonicalLift ι ZX) BX hP' (blowUpToBase ZX ≫ sY) ⊤ (E.totalTransform ZX)
        (E'.totalTransform ZX) hT₁ hfam₁ hsupp₁ (a.birationalTransform (ZX.comap ι))
        (ES.totalTransform (ZX.comap ι)) hES₁ (by rw [e]; exact hBS')

/-- On a smooth scheme over a field of characteristic zero all of whose irreducible components
have positive dimension, an ideal `K` with `(D^i K)^μ ⊆ K^(μ-i)` for `i < μ` has
`cosupp K = cosupp (K, μ)`. -/
private theorem support_eq_cosupport_of_higherDerivativeIdeal_pow_le' {k : Type u} [Field k]
    [CharZero k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (hcomp : ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) {μ : ℕ} (hμ : 1 ≤ μ)
    {K : X.IdealSheafData} (hK : ∀ i < μ, higherDerivativeIdeal sX K i ^ μ ≤ K ^ (μ - i)) :
    (K.support : Set X) = (⟨K, μ⟩ : MarkedIdeal X).cosupport := by
  have hsub : ∀ r < μ, (K.support : Set X) ⊆ (higherDerivativeIdeal sX K r).support := by
    intro r hr x hx
    have hK' := hK (μ - 1) (by omega)
    rw [Nat.sub_sub_self hμ, pow_one] at hK'
    have h1 := Scheme.IdealSheafData.support_antitone hK' hx
    rw [Scheme.IdealSheafData.support_pow _ _ (by omega)] at h1
    exact Scheme.IdealSheafData.support_antitone
      ((monotone_nat_of_le_succ fun n => by
        rw [higherDerivativeIdeal_succ]; exact le_derivativeIdeal sX hcomp _ :
          Monotone (higherDerivativeIdeal sX K)) (by omega : r ≤ μ - 1)) h1
  ext x
  refine ⟨fun hx => ?_,
    fun hx => mem_support_of_one_le_multAt K ((Nat.one_le_cast.2 hμ).trans hx)⟩
  show (μ : ℕ∞) ≤ multAt K x
  by_contra! hlt
  have hfin : multAt K x ≠ ⊤ := hlt.ne_top
  have hrx : multAt K x = (multAt K x).toNat := (ENat.coe_toNat hfin).symm
  have hr := hsub (multAt K x).toNat (by exact_mod_cast hrx ▸ hlt) hx
  have hne : IdealSheafData.stalk (higherDerivativeIdeal sX K (multAt K x).toNat) x ≠ ⊤ :=
    fun ht => (IdealSheafData.stalk_eq_top_iff_notMem_support _ x).1 ht hr
  have h1 : ((1 : ℕ) : ℕ∞) ≤ multAt (higherDerivativeIdeal sX K (multAt K x).toNat) x := by
    rw [multAt, natCast_le_idealOrder_iff', pow_one]
    exact IsLocalRing.le_maximalIdeal hne
  rw [multAt_higherDerivativeIdeal sX hcomp K _ x, ← hrx, tsub_self] at h1
  exact absurd h1 (by decide)

/-- A smooth blow-up sequence of order `≥ m` for a triple is a plain one. -/
private theorem isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k] :
    ∀ {Y : Scheme.{u}} (B : ClosedBlowupSequence Y) (s : Y ⟶ Spec (.of k)) (a : MarkedIdeal Y)
      (E : OrderedDivisor Y), B.IsOrderGeMarkedTripleSeq s a E → B.IsOrderGePlainSeq s a
  | _, .nil _, _, _, _, h => ⟨h.2.1, h.2.2.2.2.2.1⟩
  | _, .cons Z B, s, a, E, h =>
    ⟨h.1.2.1, h.1.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.1,
      isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq B _ _ _ h.2.2.2.2.2⟩

/-- Plain order `m`, a triple and snc of the centres give a smooth blow-up sequence of order `m`
starting with the triple. -/
private theorem isOrderMTripleSeq_of_plain {k : Type u} [Field k] :
    ∀ {Y : Scheme.{u}} (B : ClosedBlowupSequence Y) (s : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData)
      (E : OrderedDivisor Y) (m : ℕ), IsTriple s I E → B.IsOrderMPlainSeq s I m →
      CentersHaveSNCWithDivisor s E B → B.IsOrderMTripleSeq s I E m
  | _, .nil _, _, _, _, _, hT, _, _ => hT
  | _, .cons Z B, s, I, E, m, hT, hp, ha =>
    ⟨hT, hp.2.2.1, hp.2.2.2.1, ha.1, hp.2.2.2.2.1,
      isOrderMTripleSeq_of_plain B _ _ _ m (isTriple_controlledTransform_totalTransform hT ha.1)
        hp.2.2.2.2.2 ha.2⟩

/-- **Going up, with divisor** (the argument of Kollár 3.102, "Going up"). Let `(Y, I, E)` be a
triple, `H ⊆ Y` a smooth hypersurface with `H + E'` snc, `E = H + E'` as divisors, and `I` an
ideal with `(D^i I)^μ ⊆ I^(μ-i)`, `maxord I ≤ μ`, no component of `H` in `cosupp (I, μ)`. A
push-forward along `H ↪ Y` of a smooth blow-up sequence of order `≥ μ` starting with
`(H, I|_H, μ, E'|_H)` and without empty blow-ups is a smooth blow-up sequence of order `≥ μ`
starting with `(Y, I, μ, E)`. -/
private theorem isOrderGeMarkedTripleSeq_of_isPushforward {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) (I : Y.IdealSheafData) (Edv E' : OrderedDivisor Y)
    (H : Y.IdealSheafData) (hT : IsTriple sY I Edv)
    (hfam : IsSNCFamily sY fun o : Option (Fin E'.s) => o.elim H E'.E)
    (hsupp : Edv.support = (H.support : Set Y) ∪ E'.support)
    (hpos : ∀ C ∈ irreducibleComponents Y, 0 < topologicalKrullDim C)
    {μ : ℕ} (hμ : 1 ≤ μ) (hmax : maxOrder I ≤ μ)
    (hbal : ∀ i < μ, higherDerivativeIdeal sY I i ^ μ ≤ I ^ (μ - i))
    (hSI : ∀ W ∈ componentsOf (H.support : Set Y), ¬ W ⊆ (⟨I, μ⟩ : MarkedIdeal Y).cosupport)
    (BS : ClosedBlowupSequence H.subscheme) (BY : ClosedBlowupSequence Y)
    (hP : ClosedBlowupSequence.IsPushforward H.subschemeι BS BY) (hne : BS.HasNoEmptyBlowups)
    (ES : OrderedDivisor H.subscheme) (hES : ES.support = (E'.comap H.subschemeι).support)
    (hBS : BS.IsOrderGeMarkedTripleSeq (H.subschemeι ≫ sY) ⟨I.comap H.subschemeι, μ⟩ ES) :
    BY.IsOrderGeMarkedTripleSeq sY ⟨I, μ⟩ Edv := by
  have hT' := hT
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hEsnc⟩ := hT
  haveI := hlft
  haveI := hqc
  haveI : Smooth sY := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  have hfam' : IsSNCFamily sY fun o : Option (Fin E'.s) => o.elim H.subschemeι.ker E'.E := by
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hfam
  have hsupp' : Edv.support = (H.subschemeι.ker.support : Set Y) ∪ E'.support := by
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using hsupp
  have hSNC : CentersHaveSNCWithDivisor sY Edv BY :=
    centersHaveSNCWithDivisor_of_isPushforward BS H.subschemeι BY hP sY I Edv E' hT' hfam' hsupp'
      ⟨I.comap H.subschemeι, μ⟩ ES hES hBS
  by_cases hμeq : maxOrder I = μ
  · have hnat : (maxOrder I).toNat = μ := by rw [hμeq]; rfl
    have hD : IsDBalanced sY I := by
      intro i hi
      rw [hnat] at hi ⊢
      exact hbal i hi
    have hplain : BY.IsOrderMPlainSeq sY I μ :=
      ClosedBlowupSequence.IsPushforward.isOrderMPlainSeq_of_isDBalanced sY hsm hequi hpos hD hI
        hμeq hμ ⟨(hfam.1 none).2.2, (hfam.1 none).2.1⟩ hSI
        (isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq _ _ _ _ hBS) hP
    exact (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq sY I Edv hT' μ hμeq
        BY).1.2
      (isOrderMTripleSeq_of_plain BY sY I Edv μ hT' hplain hSNC)
  · have hlt : maxOrder I < μ := lt_of_le_of_ne hmax hμeq
    have hdich := support_eq_cosupport_of_higherDerivativeIdeal_pow_le' sY hpos hμ hbal
    have hI0 : I = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      refine eq_bot_iff.2 fun x hx => ?_
      have hx' : x ∈ (⟨I, μ⟩ : MarkedIdeal Y).cosupport := hdich ▸ hx
      have h1 : (μ : ℕ∞) ≤ multAt I x := hx'
      have h2 : multAt I x ≤ maxOrder I :=
        le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _ (Set.mem_univ _)
      exact absurd (lt_of_le_of_lt (h1.trans h2) hlt) (lt_irrefl _)
    cases BS with
    | nil =>
      cases BY with
      | nil => exact hT'
      | cons Z B => exact hP.elim
    | cons ZS BS' =>
      exfalso
      obtain ⟨-, -, -, -, hord, -⟩ := hBS
      have hZS : ZS ≠ ⊤ := hne.1
      have hsne : (ZS.support : Set H.subscheme).Nonempty := by
        by_contra h
        apply hZS
        rw [← Scheme.IdealSheafData.support_eq_bot_iff]
        refine eq_bot_iff.2 fun x hx => h ⟨x, hx⟩
      obtain ⟨x, hx⟩ := hsne
      obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hx
      have h1 := hord W hW
      have h2 : 1 ≤ orderAlong (I.comap H.subschemeι) hW.1.1 := by
        refine le_trans ?_ h1
        exact_mod_cast hμ
      have h3 := mem_support_of_one_le_multAt _ h2
      rw [hI0, Scheme.IdealSheafData.comap_top] at h3
      simp at h3

/-- On an equidimensional space of positive dimension, every irreducible component has positive
dimension. -/
private theorem pos_topologicalKrullDim_of_mem_irreducibleComponents {X : Type*}
    [TopologicalSpace X] (he : Equidimensional X) (hX : 0 < topologicalKrullDim X) :
    ∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C := by
  intro C hC
  by_contra! h
  exact hX.not_ge <| MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
    fun D hD => (he D hD C hC).le.trans h

/-- An ideal of finite maximal order is nonzero at the generic points: at a point where the stalk
vanishes the order is `∞`. -/
private theorem isNonzeroAtGenericPoints_of_maxOrder_eq {X : Scheme.{u}} {I : X.IdealSheafData}
    {μ : ℕ} (h : maxOrder I = μ) : IsNonzeroAtGenericPoints I := by
  intro η _ hbot
  have h1 : multAt I η = ⊤ := by
    unfold multAt; rw [hbot]
    refine top_le_iff.mp ((ENat.forall_natCast_le_iff_le).1 fun n _ => ?_)
    rw [natCast_le_idealOrder_iff']; exact bot_le
  have h2 : multAt I η ≤ maxOrder I :=
    le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _ (Set.mem_univ _)
  rw [h1, h] at h2
  exact ENat.coe_ne_top μ (top_le_iff.mp h2)

/-- Let `S` be a set of components of a smooth divisor `D`, and `Z` the reduced ideal of their
union. At a point `x` of a component `W ∈ S`, the ideal of `Z` agrees with that of `D`: the
components of `D` are disjoint, so near `x` the union of `S` is all of `D`. -/
private theorem stalk_vanishingIdeal_sUnion_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) {S : Set (Set X)}
    (hS : S ⊆ componentsOf (D.support : Set X)) {W : Set X} (hWS : W ∈ S) {x : X} (hxW : x ∈ W) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (⋃₀ S))) x =
      IdealSheafData.stalk D x := by
  haveI := Aux.isReduced_subscheme_of_isSmoothScheme sX D hD
  have hU : IsClosed (⋃₀ S) := Aux.isClosed_sUnion_of_subset_componentsOf sX D S hS
  set R : Set X := ⋃₀ (componentsOf (D.support : Set X) \ S)
  have hR : IsClosed R := Aux.isClosed_sUnion_of_subset_componentsOf sX D _ Set.diff_subset
  have hxR : x ∉ R := by
    rintro ⟨W', hW', hxW'⟩
    exact hW'.2 (Aux.eq_of_mem_componentsOf_of_isSmoothScheme sX D hD hW'.1 (hS hWS) hxW' hxW ▸
      hWS)
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D D.support rfl]
  refine IdealSheafData.stalk_vanishingIdeal_congr (V := ⟨Rᶜ, hR.isOpen_compl⟩) hxR ?_
  ext z
  simp only [Closeds.coe_closure, hU.closure_eq, Set.mem_inter_iff, Opens.coe_mk,
    Set.mem_compl_iff]
  constructor
  · rintro ⟨⟨W', hW', hzW'⟩, hzR⟩
    exact ⟨(hS hW').1.2 hzW', hzR⟩
  · rintro ⟨hzD, hzR⟩
    obtain ⟨W', hW', hzW'⟩ := exists_mem_componentsOf hzD
    by_cases h : W' ∈ S
    · exact ⟨⟨W', h, hzW'⟩, hzR⟩
    · exact absurd ⟨W', ⟨hW', h⟩, hzW'⟩ hzR

/-- `Z_{-1}(K, μ, E^j)`, a union of connected components of the entry `E^j` of the snc divisor
of a triple, has simple normal crossings with `E`: near a point of `E^j = (z_{c(j)} = 0)` it is
`(z_{c(j)} = 0)`. -/
private theorem hasSNCWith_divisorComponentCentre (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (K : MarkedIdeal t.X) (j : Fin t.E.s) :
    HasSNCWith t.E.E (divisorComponentCentre K (t.E.E j)) := by
  obtain ⟨-, -, hlft, hqc, -, -, hE⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  obtain ⟨-, -, hEsm⟩ := hE.2.1 j
  set S : Set (Set t.X) :=
    {W | W ∈ componentsOf ((t.E.E j).support : Set t.X) ∧ W ⊆ K.cosupport} with hSdef
  have hS : S ⊆ componentsOf ((t.E.E j).support : Set t.X) := fun W hW => hW.1
  have hU := Aux.isClosed_sUnion_of_subset_componentsOf t.sX _ S hS
  intro x hx
  have hx' : x ∈ ⋃₀ S := by simpa [divisorComponentCentre, hSdef, hU.closure_eq] using hx
  obtain ⟨W, hWS, hxW⟩ := hx'
  have hxD : x ∈ ((t.E.E j).support : Set t.X) := (hS hWS).1.2 hxW
  obtain ⟨n, z, c, hz, hzE, hinj⟩ := hE.2.2 x
  refine ⟨n, z, c, {c ⟨j, hxD⟩}, hz, hzE, hinj, ?_⟩
  change IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure (⋃₀ S))) x = _
  rw [stalk_vanishingIdeal_sUnion_eq t.sX _ hEsm hS hWS hxW, hzE ⟨j, hxD⟩]
  simp

/-- The irreducible components of `Z_{-1}(K, μ, E^j)` are components of the divisor `E^j`, so of
codimension `1`. -/
private theorem hasComponentsOfPositiveCodim_divisorComponentCentre (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (K : MarkedIdeal t.X) (j : Fin t.E.s) :
    HasComponentsOfPositiveCodim ((divisorComponentCentre K (t.E.E j)).support : Set t.X) := by
  obtain ⟨-, -, hlft, hqc, -, -, hE⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  obtain ⟨-, hpure, hEsm⟩ := hE.2.1 j
  have hZ := (divisorComponentCentre_spec t.sX K (t.E.E j) hEsm hpure).2.1
  intro C hC
  have hCc : IsClosed C :=
    isClosed_of_mem_componentsOf (divisorComponentCentre K (t.E.E j)).support.isClosed hC
  refine (hZ (irreducibleClosure hC.1.1) ⟨?_, fun W' hW' hle => ?_⟩).ge
  · change closure C ⊆ _
    rw [hCc.closure_eq]; exact hC.1.2
  · have h1 : (W' : Set t.X) ⊆ C := hC.2 ⟨W'.isIrreducible, hW'⟩
      (by
        simp only [irreducibleClosure, hCc.closure_eq] at hle
        exact hle)
    change (W' : Set t.X) ⊆ closure C
    exact h1.trans subset_closure

/-- Every irreducible component of `Z_{-1}(K, μ, E^j)` lies in `cosupp(K, μ)`, so `K` has order
`≥ μ` along it. -/
private theorem orderAlongGE_divisorComponentCentre (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (K : MarkedIdeal t.X) (j : Fin t.E.s) :
    OrderAlongGE K.I ((divisorComponentCentre K (t.E.E j)).support : Set t.X) K.m := by
  obtain ⟨-, -, hlft, hqc, -⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  set S : Set (Set t.X) :=
    {W | W ∈ componentsOf ((t.E.E j).support : Set t.X) ∧ W ⊆ K.cosupport} with hS
  have hU : IsClosed (⋃₀ S) :=
    Aux.isClosed_sUnion_of_subset_componentsOf t.sX _ S fun W hW => hW.1
  have hsup : ((divisorComponentCentre K (t.E.E j)).support : Set t.X) = ⋃₀ S := by
    simp [divisorComponentCentre, hS, hU.closure_eq]
  intro C hC
  have hCc : IsClosed C :=
    isClosed_of_mem_componentsOf (divisorComponentCentre K (t.E.E j)).support.isClosed hC
  have hg : hC.1.1.genericPoint ∈ C := by
    have := hC.1.1.isGenericPoint_genericPoint_closure.mem
    rwa [hCc.closure_eq] at this
  obtain ⟨W, hW, hgW⟩ : hC.1.1.genericPoint ∈ ⋃₀ S := hsup ▸ hC.1.2 hg
  exact hW.2 hgW

/-- At a point of `Z_{-1}(K, μ, E^j)` its stalk ideal is generated by one member of a regular
system of parameters. -/
private theorem exists_stalk_centre (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (K : MarkedIdeal t.X) (j : Fin t.E.s) :
    ∀ y ∈ (divisorComponentCentre K (t.E.E j)).support, ∃ (m : ℕ)
      (w : Fin m → t.X.presheaf.stalk y) (i : Fin m), MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (divisorComponentCentre K (t.E.E j)) y = Ideal.span {w i} := by
  obtain ⟨-, -, hlft, hqc, -, -, hE⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  obtain ⟨-, -, hEsm⟩ := hE.2.1 j
  set S : Set (Set t.X) :=
    {W | W ∈ componentsOf ((t.E.E j).support : Set t.X) ∧ W ⊆ K.cosupport} with hSdef
  have hS : S ⊆ componentsOf ((t.E.E j).support : Set t.X) := fun W hW => hW.1
  have hU := Aux.isClosed_sUnion_of_subset_componentsOf t.sX _ S hS
  intro x hx
  have hx' : x ∈ ⋃₀ S := by
    simpa [divisorComponentCentre, hSdef, hU.closure_eq,
      Stacks.AffineClosedUnion.support_vanishingIdeal] using hx
  obtain ⟨W, hWS, hxW⟩ := hx'
  have hxD : x ∈ ((t.E.E j).support : Set t.X) := (hS hWS).1.2 hxW
  obtain ⟨n, z, c, hz, hzE, hinj⟩ := hE.2.2 x
  refine ⟨n, z, c ⟨j, hxD⟩, hz, ?_⟩
  change IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure (⋃₀ S))) x = _
  rw [stalk_vanishingIdeal_sUnion_eq t.sX _ hEsm hS hWS hxW, hzE ⟨j, hxD⟩]

/-- The blow-up of `Z_{-1}(K, μ, E^j)` is an isomorphism, the centre being an effective Cartier
divisor. -/
private theorem isIso_blowUpToBase_centre (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (K : MarkedIdeal t.X) (j : Fin t.E.s) :
    IsIso (blowUpToBase (divisorComponentCentre K (t.E.E j))) := by
  haveI : LocallyOfFiniteType t.sX := ht.2.2.1
  haveI : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  exact Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (exists_stalk_centre t ht K j))

/-- The inverse image of the divisor of a triple under a smooth, quasi-compact morphism is an
ordered snc divisor. -/
private theorem comap_isOrderedSNC (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) {Y : Scheme.{u}}
    (h : Y ⟶ t.X) [Smooth h] [QuasiCompact (h ≫ t.sX)] :
    (t.E.comap h).IsOrderedSNC (h ≫ t.sX) :=
  (pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) h).2.2.2.2.2

/-- Deleting the `j`-th entry of an snc family and putting it first gives an snc family. -/
private theorem isSNCFamily_option_deleteIndex {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} (E : OrderedDivisor X) (hE : IsSNCFamily s E.E) (j : ℕ)
    (hj : j < E.s) :
    IsSNCFamily s (fun o : Option (Fin (E.deleteIndex j).s) =>
      o.elim (E.E ⟨j, hj⟩) (E.deleteIndex j).E) := by
  set L := (List.finRange E.s).filter fun i : Fin E.s => i.val ≠ j with hL
  have hLinj : Function.Injective L.get :=
    List.Nodup.injective_get ((List.nodup_finRange _).filter _)
  have hLne : ∀ i, L.get i ≠ ⟨j, hj⟩ := fun i h => by
    have := List.of_mem_filter (L.get_mem i)
    simp only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at this
    exact this (congrArg Fin.val h :)
  let g : Option (Fin L.length) → Fin E.s := fun o => o.elim ⟨j, hj⟩ L.get
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact absurd hab.symm (hLne b)
    | some a =>
      cases b with
      | none => exact absurd hab (hLne a)
      | some b => exact congrArg some (hLinj hab)
  have e : (fun o : Option (Fin (E.deleteIndex j).s) =>
      o.elim (E.E ⟨j, hj⟩) (E.deleteIndex j).E) = E.E ∘ g := by
    funext o
    cases o with
    | none => rfl
    | some a => rfl
  rw [e]
  exact hE.comp g hg

/-- The support of a divisor is the union of the supports of its `j`-th entry and of the others. -/
private theorem support_eq_union_deleteIndex {X : Scheme.{u}} (E : OrderedDivisor X) (j : ℕ)
    (hj : j < E.s) :
    E.support = ((E.E ⟨j, hj⟩).support : Set X) ∪ (E.deleteIndex j).support := by
  set L := (List.finRange E.s).filter fun i : Fin E.s => i.val ≠ j with hL
  ext x
  simp only [OrderedDivisor.support, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hij : i.val = j
    · left
      have : i = ⟨j, hj⟩ := Fin.ext hij
      exact this ▸ hi
    · right
      have hmem : i ∈ L := by
        rw [hL, List.mem_filter]; exact ⟨List.mem_finRange i, by simpa using hij⟩
      obtain ⟨a, ha⟩ := List.mem_iff_get.1 hmem
      exact ⟨a, by
        show x ∈ ((E.E (L.get a)).support : Set X)
        rw [ha]; exact hi⟩
  · rintro (h | ⟨a, ha⟩)
    · exact ⟨_, h⟩
    · exact ⟨L.get a, ha⟩

/-- With `maxord I = m ≥ 1` on a triple of dimension `n ≥ 1`, the maximal coefficient ideal
`W_{m!}(I)` has maximal order `m!`. -/
private theorem maxOrder_maximalCoefficientIdeal_factorial {m n : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) :
    maxOrder (maximalCoefficientIdeal t.sX t.I (m.factorial : ℤ)) = m.factorial := by
  obtain ⟨hchar, hsm, hlft, hqc, hequi, -⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  exact Kollar.maxOrder_maximalCoefficientIdeal t.sX hsm hequi (by rw [hdim]; exact_mod_cast hn)
    t.I (by rw [hmax]; simpa using hm) (Nat.factorial_pos m)

/-- `(X, W_{m!}(I), E)` is a triple when `(X, I, E)` is one with `maxord I = m ≥ 1`. -/
private theorem isTriple_maximalCoefficientIdeal_factorial {m n : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) :
    IsTriple t.sX (maximalCoefficientIdeal t.sX t.I (m.factorial : ℤ)) t.E := by
  have hW := maxOrder_maximalCoefficientIdeal_factorial t ht hdim hn hm hmax
  obtain ⟨hchar, hsm, hlft, hqc, heq, -, hE⟩ := ht
  exact ⟨hchar, hsm, hlft, hqc, heq, isNonzeroAtGenericPoints_of_maxOrder_eq hW, hE⟩

section DeleteEmptyAux

variable {X : Scheme.{u}}

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem injective_flatIdx_get (E : OrderedDivisor X) :
    Function.Injective (flatIdx E).get :=
  List.nodup_iff_injective_get.1 ((List.nodup_finRange _).filter _)

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

section Reindex

variable {X : Scheme.{u}} {Λ Λ' : Type*} (E : Λ → X.IdealSheafData) (g : Λ' → Λ)

/-- A property of all entries may be checked on the nonempty ones. -/
private theorem forall_iff_forall_comp (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i)
    (R : X.IdealSheafData → Prop) (hR : R ⊤) :
    (∀ i, R (E i)) ↔ ∀ j, R (E (g j)) := by
  refine ⟨fun h j => h _, fun h i => ?_⟩
  by_cases hi : E i = ⊤
  · rw [hi]; exact hR
  · obtain ⟨j, rfl⟩ := hg i hi
    exact h j

/-- The coordinate assignment of an snc family at a point may be taken over the nonempty
entries. -/
private theorem exists_coord_iff (hginj : Function.Injective g)
    (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x) :
    (∃ c : {i // x ∈ (E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c) ↔
      ∃ c : {j // x ∈ (E (g j)).support} → Fin n,
        (∀ j, IdealSheafData.stalk (E (g j.1)) x = Ideal.span {z (c j)}) ∧
          Function.Injective c := by
  let φ : {j // x ∈ (E (g j)).support} → {i // x ∈ (E i).support} := fun j => ⟨g j.1, j.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨j, hj⟩ := hg i.1 fun h => by
      have := i.2
      rw [h, Scheme.IdealSheafData.support_top] at this
      exact this
    exact ⟨⟨j, hj ▸ i.2⟩, Subtype.ext hj⟩
  let e := Equiv.ofBijective φ hφ
  constructor
  · rintro ⟨c, hc, hinj⟩
    exact ⟨c ∘ φ, fun j => hc (φ j), hinj.comp hφ.1⟩
  · rintro ⟨c, hc, hinj⟩
    refine ⟨c ∘ e.symm, fun i => ?_, hinj.comp e.symm.injective⟩
    have hi : g (e.symm i).1 = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
    rw [← hi]
    exact hc (e.symm i)

private theorem isSNCFamily_iff_comp {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hginj : Function.Injective g) (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) :
    IsSNCFamily sX E ↔ IsSNCFamily sX (E ∘ g) := by
  refine and_congr (forall_iff_forall_comp E g hg (fun D => IsReduced D.subscheme ∧
      MMP.Mori.IsPureCodimOne D.support ∧ MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
      ⟨?_, ?_, ?_⟩)
    (forall_congr' fun x => exists_congr fun n => exists_congr fun z => ?_)
  · exact isReduced_of_isAffine_isReduced _
  · intro W hW
    have h := hW.prop
    rw [Scheme.IdealSheafData.support_top] at h
    obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
    exact (h hw).elim
  · unfold MMP.Mori.IsSmoothScheme
    ext x
    exact isEmptyElim x
  · have key := exists_coord_iff E g hginj hg x z
    constructor
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.1 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.2 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩

end Reindex

section DeleteEmpty

variable {X : Scheme.{u}} (E : OrderedDivisor X)

private theorem isOrderedSNC_deleteEmpty_iff {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) :
    E.IsOrderedSNC sX ↔ E.deleteEmpty.IsOrderedSNC sX :=
  and_congr
    (forall_iff_forall_comp E.E _ (exists_flatIdx_get E)
      (fun D => IsReduced D.subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor D)
      ⟨isReduced_of_isAffine_isReduced _, Stacks.Divisors.isEffectiveCartierDivisor_top⟩)
    (isSNCFamily_iff_comp E.E _ sX (injective_flatIdx_get E) (exists_flatIdx_get E))

end DeleteEmpty

end DeleteEmptyAux

/-- Inserting empty entries into an ordered snc divisor keeps it an ordered snc divisor. -/
private theorem mem_markedTriples_of_deleteEmpty (T : MarkedTriple.{u})
    (h : T.deleteEmpty ∈ markedTriples) : T ∈ markedTriples := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d, e, f, (isOrderedSNC_deleteEmpty_iff T.E T.sX).2 g⟩

/-- The marked triple `(S, W_0𝒪_S, μ, E_S)` fed to `𝓜` by `𝓑𝓓` has dimension `n - 1` when
`S ≠ ∅`. -/
private theorem tS_mem {m n j : ℕ} (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) (hn : 1 ≤ n)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    (S.support : Set (blowUp Z)).Nonempty → tS ∈ markedTriplesOfDim {n - 1} μ := by
  intro μ W Z π S τ tS hne
  have h := bdFunctor_input_mem_markedTriplesOfDim t ht hm hmax hj hn hdim hne
  exact ⟨mem_markedTriples_of_deleteEmpty _ h.1, h.2⟩

/-- Derivative ideals commute with smooth pull-back (iterated). -/
private theorem higherDerivativeIdeal_comap {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [Smooth sX] (f : Y ⟶ X) [Smooth f]
    (hf : f ≫ sX = sY) (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z)
    (I : X.IdealSheafData) (i : ℕ) :
    higherDerivativeIdeal sY (I.comap f) i = (higherDerivativeIdeal sX I i).comap f := by
  induction i with
  | zero => simp [higherDerivativeIdeal_zero]
  | succ i ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih]
    exact derivativeIdeal_comap_of_smooth sX sY f hf hdim _

/-- Ideal sheaves with the same stalks on an open set have the same derivative ideals there. -/
private theorem stalk_higherDerivativeIdeal_congr {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [Smooth sY]
    (hdim : ∀ Z ∈ irreducibleComponents Y, 0 < topologicalKrullDim Z)
    {A B : Y.IdealSheafData} (U : Y.Opens)
    (h : ∀ u ∈ U, IdealSheafData.stalk A u = IdealSheafData.stalk B u) (i : ℕ) :
    ∀ u ∈ U, IdealSheafData.stalk (higherDerivativeIdeal sY A i) u =
      IdealSheafData.stalk (higherDerivativeIdeal sY B i) u := by
  have hAB : A.comap U.ι = B.comap U.ι := by
    refine le_antisymm ?_ ?_ <;>
    · refine IdealSheafData.le_of_stalk_le _ _ fun v => ?_
      rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_comap, h (U.ι v) v.2]
  have hD : (higherDerivativeIdeal sY A i).comap U.ι =
      (higherDerivativeIdeal sY B i).comap U.ι := by
    rw [← higherDerivativeIdeal_comap sY (U.ι ≫ sY) U.ι rfl hdim A i,
      ← higherDerivativeIdeal_comap sY (U.ι ≫ sY) U.ι rfl hdim B i, hAB]
  intro u hu
  let v : U.toScheme := ⟨u, hu⟩
  have this : IdealSheafData.stalk ((higherDerivativeIdeal sY A i).comap U.ι) v =
      IdealSheafData.stalk ((higherDerivativeIdeal sY B i).comap U.ι) v := by rw [hD]
  rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_comap] at this
  have hb := ConcreteCategory.bijective_of_isIso (U.ι.stalkMap v)
  have h1 := congrArg (Ideal.comap (U.ι.stalkMap v).hom) this
  rwa [Ideal.comap_map_of_bijective _ hb, Ideal.comap_map_of_bijective _ hb] at h1

/-- A scheme smooth over a field is locally noetherian with regular local rings. -/
private theorem regular_stalks_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [Smooth s] :
    IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
  ((isRegular_tfae X).out 1 2).mp (isRegular_of_smooth_over_field s)

/-- `ord_y h^*I = ord_{h(y)} I` for smooth `h` (on a scheme smooth over a field). -/
private theorem multAt_comap_of_smooth_general {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (h : Y ⟶ X) [Smooth h] (I : X.IdealSheafData) (y : Y) :
    multAt (I.comap h) y = multAt I (h y) := by
  obtain ⟨hXn, hX⟩ := regular_stalks_of_smooth sX
  obtain ⟨hYn, hY⟩ := regular_stalks_of_smooth (h ≫ sX)
  exact MMP.Flips.ResolutionInputs.multAt_comap_eq h hX hY
    (fun y => AlgebraicGeometry.isRegularLocalRing_closedFibre_of_smooth h y) I y

/-- The stalks of the twist `W_0 = (π^*W : I_F^μ)` of `W = W_μ(I)` along `π : B_ZX → X`,
`Z = Z_{-1}(W, μ, E^j)`, `F = π⁻¹Z`: `W_0` is `π^*W` off `F` and the unit ideal on `F`. -/
private theorem twist_facts {m n j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    maxOrder W.I = μ ∧ W.I.comap π ≤ (W.birationalTransform Z).I ∧
      (∀ y, y ∉ ((Z.comap π).support : Set (blowUp Z)) →
        IdealSheafData.stalk (W.birationalTransform Z).I y =
          IdealSheafData.stalk (W.I.comap π) y) ∧
      (∀ y ∈ ((Z.comap π).support : Set (blowUp Z)),
        IdealSheafData.stalk (W.birationalTransform Z).I y = ⊤) := by
  intro μ W Z π
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hE⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso π := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  have hWmax : maxOrder W.I = μ :=
    maxOrder_maximalCoefficientIdeal_factorial t ht' hdim hn hm hmax
  obtain ⟨-, hEpure, hEsm⟩ := hE.2.1 ⟨j, hj⟩
  have hZsm := (divisorComponentCentre_spec t.sX W (t.E.E ⟨j, hj⟩) hEsm hEpure).1
  have hmul : (W.birationalTransform Z).I * Z.comap π ^ μ = W.I.comap π :=
    MarkedIdeal.birationalTransform_mul_eq t.sX hsm Z hZsm
      (hasComponentsOfPositiveCodim_divisorComponentCentre t ht' W ⟨j, hj⟩) W
      (orderAlongGE_divisorComponentCentre t ht' W ⟨j, hj⟩)
  have hst : ∀ y, IdealSheafData.stalk (W.birationalTransform Z).I y *
      IdealSheafData.stalk (Z.comap π) y ^ μ = IdealSheafData.stalk (W.I.comap π) y := fun y => by
    rw [← IdealSheafData.stalk_pow, ← IdealSheafData.stalk_mul]
    exact congrArg (fun J => IdealSheafData.stalk J y) hmul
  refine ⟨hWmax, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
    calc IdealSheafData.stalk (W.I.comap π) y
        = IdealSheafData.stalk (W.birationalTransform Z).I y *
            IdealSheafData.stalk (Z.comap π) y ^ μ := (hst y).symm
      _ ≤ IdealSheafData.stalk (W.birationalTransform Z).I y := Ideal.mul_le_left
  · have : IdealSheafData.stalk (Z.comap π) y = ⊤ :=
      (IdealSheafData.stalk_eq_top_iff_notMem_support _ y).2 hy
    rw [← hst y, this, Ideal.top_pow, Ideal.mul_top]
  · by_contra hne
    have h1 := IsLocalRing.le_maximalIdeal hne
    have h2 := IsLocalRing.le_maximalIdeal
      (fun h => (IdealSheafData.stalk_eq_top_iff_notMem_support _ y).1 h hy)
    have h3 : IdealSheafData.stalk (W.I.comap π) y ≤
        IsLocalRing.maximalIdeal ((blowUp Z).presheaf.stalk y) ^ (μ + 1) := by
      rw [← hst y, pow_succ']
      exact Ideal.mul_mono h1 (Ideal.pow_right_mono h2 μ)
    have h4 : ((μ + 1 : ℕ) : ℕ∞) ≤ multAt (W.I.comap π) y :=
      (natCast_le_idealOrder_iff' _ _).2 h3
    rw [multAt_comap_of_smooth_general t.sX π W.I y] at h4
    have h5 : multAt W.I (π y) ≤ maxOrder W.I :=
      le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt W.I z) _ (Set.mem_univ _)
    rw [hWmax] at h5
    have := h4.trans h5
    norm_cast at this
    omega

/-- On a scheme of dimension `n ≥ 1` with equidimensional components, all irreducible components
have positive dimension. -/
private theorem pos_dim_blowup {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (Z : X.IdealSheafData) [IsIso (blowUpToBase Z)] {n : ℕ} (hn : 1 ≤ n)
    (hdim : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) (hequi : Equidimensional X) :
    (∀ C ∈ irreducibleComponents X, 0 < topologicalKrullDim C) ∧
      topologicalKrullDim (blowUp Z) = ((n : ℕ∞) : WithBot ℕ∞) ∧
      (∀ C ∈ irreducibleComponents (blowUp Z), 0 < topologicalKrullDim C) := by
  have hX : 0 < topologicalKrullDim X := by
    rw [hdim]; exact_mod_cast hn
  have hdY : topologicalKrullDim (blowUp Z) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdim]
    exact IsHomeomorph.topologicalKrullDim_eq _ (blowUpToBase Z).homeomorph.isHomeomorph
  refine ⟨pos_topologicalKrullDim_of_mem_irreducibleComponents hequi hX, hdY,
    pos_topologicalKrullDim_of_mem_irreducibleComponents (equidimensional_blowUp sX Z hequi) ?_⟩
  rw [hdY]; exact_mod_cast hn

/-- **`W_0` is `D`-balanced** (Kollár, proof of 3.102: `(D^iW_0)^μ ⊂ W_0^{μ-i}` for `i < μ`). -/
private theorem hbal_twist {m n j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    ∀ i < μ, higherDerivativeIdeal (π ≫ t.sX) (W.birationalTransform Z).I i ^ μ ≤
      (W.birationalTransform Z).I ^ (μ - i) := by
  intro μ W Z π
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hE⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso π := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  obtain ⟨hposX, -, hposY⟩ := pos_dim_blowup t.sX Z hn hdim hequi
  obtain ⟨hWmax, -, h1, h2⟩ := twist_facts t ht' hdim hn hm hmax hj
  have hdim1 : 1 ≤ topologicalKrullDim t.X := by rw [hdim]; exact_mod_cast hn
  have hm' : 1 ≤ (maxOrder t.I).toNat := by rw [hmax]; simpa using hm
  have hbal := Kollar.isDBalanced_maximalCoefficientIdeal_factorial t.sX hequi hdim1 t.I hm'
  have htoNat : (maxOrder t.I).toNat = m := by rw [hmax]; rfl
  rw [htoNat] at hbal
  have hK : ∀ i < μ, higherDerivativeIdeal t.sX W.I i ^ μ ≤ W.I ^ (μ - i) := by
    have h := hbal
    unfold IsDBalanced at h
    rw [show maxOrder (maximalCoefficientIdeal t.sX t.I (m.factorial : ℤ)) = μ from hWmax] at h
    exact h
  intro i hi
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  rw [IdealSheafData.stalk_pow, IdealSheafData.stalk_pow]
  by_cases hy : y ∈ ((Z.comap π).support : Set (blowUp Z))
  · rw [h2 y hy, Ideal.top_pow]; exact le_top
  · haveI : Smooth (π ≫ t.sX) := inferInstance
    have hcongr := stalk_higherDerivativeIdeal_congr (π ≫ t.sX) hposY
      (A := (W.birationalTransform Z).I) (B := W.I.comap π) (Z.comap π).support.compl
      (fun u hu => h1 u hu) i y hy
    rw [hcongr, higherDerivativeIdeal_comap t.sX (π ≫ t.sX) π rfl hposX W.I i, h1 y hy]
    have h3 := stalk_le_stalk_of_le (Scheme.IdealSheafData.comap_mono π (hK i hi)) y
    simp only [Stacks.IdealSheaf.comap_pow, IdealSheafData.stalk_pow] at h3
    exact h3

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- A closed subset `C` in the image of an open embedding `f` is an irreducible component of
`D` exactly when `f⁻¹C` is an irreducible component of `f⁻¹D`. -/
private theorem mem_componentsOf_iff_preimage (hf : Topology.IsOpenEmbedding f) {D C : Set α}
    (hC : IsClosed C) (hCf : C ⊆ Set.range f) :
    C ∈ componentsOf D ↔ f ⁻¹' C ∈ componentsOf (f ⁻¹' D) := by
  constructor
  · rintro ⟨⟨hirr, hCD⟩, hmax⟩
    have hne : (f ⁻¹' C).Nonempty := by
      obtain ⟨c, hc⟩ := hirr.nonempty
      obtain ⟨b, rfl⟩ := hCf hc
      exact ⟨b, hc⟩
    refine ⟨⟨⟨hne, hirr.isPreirreducible.preimage hf⟩, Set.preimage_mono hCD⟩, ?_⟩
    rintro T ⟨hT, hTD⟩ hle
    have hCT : C ⊆ f '' T := by
      intro c hc
      obtain ⟨b, rfl⟩ := hCf hc
      exact ⟨b, hle hc, rfl⟩
    have := hmax ⟨hT.image f hf.continuous.continuousOn,
      (Set.image_mono hTD).trans (Set.image_preimage_subset f D)⟩ hCT
    intro b hb
    exact this ⟨b, hb, rfl⟩
  · rintro ⟨⟨hirr, hCD⟩, hmax⟩
    have hCeq : f '' (f ⁻¹' C) = C := Set.image_preimage_eq_of_subset hCf
    refine ⟨⟨hCeq ▸ hirr.image f hf.continuous.continuousOn, ?_⟩, ?_⟩
    · rw [← hCeq]
      exact (Set.image_mono hCD).trans (Set.image_preimage_subset f D)
    · rintro S ⟨hS, hSD⟩ hle
      have hSne : (f ⁻¹' S).Nonempty := hirr.nonempty.mono (Set.preimage_mono hle)
      have h1 := hmax ⟨⟨hSne, hS.isPreirreducible.preimage hf⟩, Set.preimage_mono hSD⟩
        (Set.preimage_mono hle)
      have hSU : (S ∩ Set.range f).Nonempty := by
        obtain ⟨b, hb⟩ := hSne
        exact ⟨f b, hb, b, rfl⟩
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen hS.isPreirreducible
        hf.isOpen_range hSU).trans (hC.closure_subset_iff.2 ?_)
      rintro _ ⟨hx, b, rfl⟩
      exact h1 hx

end Topology

/-- The maximal order of `W_0` is at most `μ`. -/
private theorem maxOrder_twist_le {m n j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    maxOrder (W.birationalTransform Z).I ≤ μ := by
  intro μ W Z
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hE⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso (blowUpToBase Z) := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  obtain ⟨hWmax, hle, -, -⟩ := twist_facts t ht' hdim hn hm hmax hj
  refine iSup₂_le fun y _ => ?_
  calc multAt (W.birationalTransform Z).I y ≤ multAt (W.I.comap (blowUpToBase Z)) y :=
        Kollar.multAt_antitone hle y
    _ = multAt W.I (blowUpToBase Z y) :=
        multAt_comap_of_smooth_general t.sX (blowUpToBase Z) W.I y
    _ ≤ maxOrder W.I :=
        le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt W.I z) _ (Set.mem_univ _)
    _ = μ := hWmax

/-- No component of `E^j` pulled back to `B_ZX` lies in `cosupp (W_0, μ)`. -/
private theorem hSI_twist {m n j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    ∀ C ∈ componentsOf ((((t.E.E ⟨j, hj⟩).comap π).support : Set (blowUp Z))),
      ¬ C ⊆ (⟨(W.birationalTransform Z).I, μ⟩ : MarkedIdeal (blowUp Z)).cosupport := by
  intro μ W Z π C hC hsub
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hE⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso π := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  obtain ⟨hWmax, hle, -, h2⟩ := twist_facts t ht' hdim hn hm hmax hj
  have hμ : 1 ≤ μ := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
  obtain ⟨y, hy⟩ := hC.1.1.nonempty
  have hCc : IsClosed C := Aux.isClosed_of_mem_componentsOf
    (((t.E.E ⟨j, hj⟩).comap π).support).isClosed hC
  have hC'c : IsClosed (π '' C) := π.isClosedEmbedding.isClosedMap _ hCc
  have hsupp : (((t.E.E ⟨j, hj⟩).comap π).support : Set (blowUp Z)) =
      π ⁻¹' ((t.E.E ⟨j, hj⟩).support : Set t.X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hC' : π '' C ∈ componentsOf ((t.E.E ⟨j, hj⟩).support : Set t.X) := by
    rw [mem_componentsOf_iff_preimage π.isOpenEmbedding hC'c (Set.image_subset_range _ _),
      Set.preimage_image_eq _ π.injective, ← hsupp]
    exact hC
  have hsubW : π '' C ⊆ W.cosupport := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : (μ : ℕ∞) ≤ multAt (W.birationalTransform Z).I u := hsub hu
    have h2 := Kollar.multAt_antitone hle u
    rw [multAt_comap_of_smooth_general t.sX π W.I u] at h2
    exact h1.trans h2
  have hZ : (Z.support : Set t.X) = ⋃₀ {W' | W' ∈ componentsOf ((t.E.E ⟨j, hj⟩).support : Set t.X) ∧
      W' ⊆ W.cosupport} := by
    obtain ⟨-, hEpure, hEsm⟩ := hE.2.1 ⟨j, hj⟩
    have hS : {W' | W' ∈ componentsOf ((t.E.E ⟨j, hj⟩).support : Set t.X) ∧
        W' ⊆ W.cosupport} ⊆ componentsOf ((t.E.E ⟨j, hj⟩).support : Set t.X) := fun W hW => hW.1
    have hU := Aux.isClosed_sUnion_of_subset_componentsOf t.sX _ _ hS
    simp [Z, divisorComponentCentre, hU.closure_eq]
  have hyZ : π y ∈ (Z.support : Set t.X) := by
    rw [hZ]; exact ⟨π '' C, ⟨hC', hsubW⟩, y, hy, rfl⟩
  have hyF : y ∈ ((Z.comap π).support : Set (blowUp Z)) := by
    rw [Scheme.IdealSheafData.support_comap]; exact hyZ
  have h1 : (μ : ℕ∞) ≤ multAt (W.birationalTransform Z).I y := hsub hy
  have h3 : multAt (W.birationalTransform Z).I y = 0 := by
    unfold multAt
    rw [h2 y hyF]
    have hn1 : ¬ ((1 : ℕ) : ℕ∞) ≤ idealOrder (⊤ : Ideal ((blowUp Z).presheaf.stalk y)) := by
      rw [natCast_le_idealOrder_iff', pow_one]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 h)
    exact nonpos_iff_eq_zero.1 (not_lt.1 fun h => hn1 (by exact_mod_cast Order.one_le_iff_pos.2 h))
  rw [h3] at h1
  have : μ ≤ 0 := by exact_mod_cast h1
  omega

/-- The push-forward of the empty sequence is empty. -/
private theorem pushforward_nil {S X : Scheme.{u}} (j : S ⟶ X) :
    (ClosedBlowupSequence.nil S).pushforward j = ClosedBlowupSequence.nil X := by
  unfold ClosedBlowupSequence.pushforward
  split_ifs with h
  · have := h.choose_spec
    generalize h.choose = B' at this
    cases B' with
    | nil => rfl
    | cons Z B => exact this.elim
  · rfl

/-- A member of a marked order reduction family on `[0, N - 1]`, evaluated at a marked triple
of dimension `k ≤ N - 1`, is the value of an order reduction functor there. -/
private theorem exists_toFun_eq_of_isMarkedOrderReductionFamily {N k μ : ℕ}
    (M : MarkedFamily.{u}) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hμ : 1 ≤ μ)
    (hk : k ≤ N - 1) {tS : MarkedTriple.{u}} (htS : tS ∈ markedTriplesOfDim {k} μ) :
    ∃ (F : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim (Set.Icc 0 (N - 1)) μ))
      (h : tS ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) μ), F.toFun tS h = M k μ tS := by
  obtain ⟨F, hF1, -⟩ := hM μ hμ
  obtain ⟨h1, h2, k', hk', hk2⟩ := htS
  rw [Set.mem_singleton_iff] at hk'
  subst hk'
  have hdim : dimNat tS.X = k' := by
    show ((topologicalKrullDim tS.X).unbotD 0).toNat = k'
    rw [hk2, WithBot.unbotD_coe, ENat.toNat_coe]
  have h : tS ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) μ :=
    ⟨h1, h2, k', ⟨Nat.zero_le _, hk⟩, hk2⟩
  exact ⟨F, h, by rw [hF1 tS h, hdim]⟩

/-- **Kollár 3.102, "The sequence on `S`" and "Going up"**, for any divisor `Edv` on `B_ZX`
which is a triple with the ideal `W_0` and has the support of `π⁻¹E`. -/
private theorem pushforward_core {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    ∀ (Edv : OrderedDivisor (blowUp Z)),
      IsTriple (π ≫ t.sX) (W.birationalTransform Z).I Edv →
      Edv.support = (t.E.comap π).support →
      ∀ BS : ClosedBlowupSequence S.subscheme,
        (BS = .nil _ ∨ ((S.support : Set (blowUp Z)).Nonempty ∧ BS = M (n - 1) μ tS)) →
        (BS.pushforward τ).IsOrderGeMarkedTripleSeq (π ≫ t.sX) (W.birationalTransform Z) Edv := by
  intro μ W Z π S τ tS Edv hEdv hsupp BS hBS
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, hE⟩ := ht
  haveI := hchar
  haveI := hlft
  haveI := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso π := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  obtain ⟨-, hdY, hposY⟩ := pos_dim_blowup t.sX Z hn hdim hequi
  have hμ : 1 ≤ μ := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
  rcases hBS with rfl | ⟨hne, rfl⟩
  · rw [pushforward_nil]
    exact hEdv
  · by_cases hex : ∃ B', ClosedBlowupSequence.IsPushforward τ (M (n - 1) μ tS) B'
    · have hpf : (M (n - 1) μ tS).pushforward τ = hex.choose := by
        unfold ClosedBlowupSequence.pushforward; rw [dif_pos hex]
      rw [hpf]
      have hP := hex.choose_spec
      -- the input of `M` is a marked triple of dimension `n - 1`
      have htS : tS ∈ markedTriplesOfDim {n - 1} μ := tS_mem t ht' hm hmax hj hn hdim hne
      obtain ⟨F, htS', hFM⟩ := exists_toFun_eq_of_isMarkedOrderReductionFamily M hM hμ
        (by omega : n - 1 ≤ N - 1) htS
      have hBS := F.isOrderGeMarkedTripleSeq tS htS'
      have hNE := F.hasNoEmptyBlowups tS htS'
      rw [hFM] at hBS hNE
      have hE0 : (t.E.comap π).IsOrderedSNC (π ≫ t.sX) := comap_isOrderedSNC t ht' π
      have hfam := isSNCFamily_option_deleteIndex (t.E.comap π) hE0.2 j hj
      refine isOrderGeMarkedTripleSeq_of_isPushforward (π ≫ t.sX) (W.birationalTransform Z).I Edv
        ((t.E.comap π).deleteIndex j) S hEdv hfam ?_ hposY hμ
        (maxOrder_twist_le t ht' hdim hn hm hmax hj) (hbal_twist t ht' hdim hn hm hmax hj)
        (hSI_twist t ht' hdim hn hm hmax hj) (M (n - 1) μ tS) hex.choose hP hNE
        tS.E rfl hBS
      rw [hsupp]
      exact support_eq_union_deleteIndex (t.E.comap π) j hj
    · have hpf : (M (n - 1) μ tS).pushforward τ = .nil _ := by
        unfold ClosedBlowupSequence.pushforward; rw [dif_neg hex]
      rw [hpf]
      exact hEdv

/-- A push-forward of a sequence without empty blow-ups has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_of_isPushforward {S : Scheme.{u}} (BS : ClosedBlowupSequence S) :
    ∀ {X : Scheme.{u}} (ι : S ⟶ X) (BX : ClosedBlowupSequence X),
      ClosedBlowupSequence.IsPushforward ι BS BX → BS.HasNoEmptyBlowups →
        BX.HasNoEmptyBlowups := by
  induction BS with
  | nil S =>
    intro X ι BX hP _
    cases BX with
    | nil => trivial
    | cons Z B => exact hP.elim
  | cons ZS BS ih =>
    intro X ι BX hP hne
    cases BX with
    | nil => exact hP.elim
    | cons ZX BX =>
      obtain ⟨hc, -, hP'⟩ := hP
      subst hc
      refine ⟨fun h => hne.1 ?_, ?_⟩
      · rw [h]; exact Scheme.IdealSheafData.comap_top ι
      · rw [eqToHom_refl, Category.id_comp] at hP'
        exact ih _ BX hP' hne.2

/-- The ideal of `Z_{-1}`'s twist, when `Z_{-1}` is empty, is the pull-back of `W`. -/
private theorem twist_eq_of_top {m n j : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    Z = ⊤ → (W.birationalTransform Z).I = W.I.comap π := by
  intro μ W Z π hZ
  obtain ⟨-, hle, h1, -⟩ := twist_facts t ht hdim hn hm hmax hj
  refine le_antisymm ?_ hle
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  rw [h1 y]
  have hs : (Z.support : Set t.X) = ∅ := by rw [hZ]; simp
  have : ((Z.comap π).support : Set (blowUp Z)) = ∅ := by
    rw [Scheme.IdealSheafData.support_comap]
    change π ⁻¹' (Z.support : Set t.X) = ∅
    rw [hs]; rfl
  rw [this]; exact Set.notMem_empty y

private theorem map_eq_comap_inv' {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (g : X ⟶ Y) [IsIso g] : I.map g = I.comap (inv g) := by
  have hfst : Limits.pullback.fst (inv g) I.subschemeι =
      Limits.pullback.snd (inv g) I.subschemeι ≫ I.subschemeι ≫ g := by
    rw [← Limits.pullback.condition_assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.IdealSheafData.comap, hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.ker_subschemeι]

private theorem pullbackReduced_heq_extendByClosure {Y : Scheme.{u}} (B : ClosedBlowupSequence Y)
    (hB : B.HasNoEmptyBlowups) :
    ∀ {X₁ X₂ : Scheme.{u}} (ψ : Y ⟶ X₁) [IsIso ψ] (g : X₂ ⟶ Y) (e : X₂ = X₁),
      g ≫ ψ = eqToHom e → B.pullbackReduced g ≍ B.extendByClosure ψ := by
  induction B with
  | nil Y => intro X₁ X₂ ψ _ g e _; subst e; rfl
  | cons Z B ih =>
    intro X₁ X₂ ψ _ g e hgψ
    subst e
    have hg : g = inv ψ := by
      calc g = (g ≫ ψ) ≫ inv ψ := by simp
        _ = inv ψ := by rw [hgψ]; simp
    subst hg
    have hmap : Z.comap (inv ψ) = Z.map ψ := (map_eq_comap_inv' Z ψ).symm
    have hcm : (Z.map ψ).comap ψ = Z := ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion ψ Z
    have hne : Z.comap (inv ψ) ≠ ⊤ := by
      intro h
      rw [hmap] at h
      apply hB.1
      rw [← hcm, h]; simp
    have h1 : ClosedBlowupSequence.pullbackReduced (ClosedBlowupSequence.cons Z B) (inv ψ) =
        ClosedBlowupSequence.cons (Z.comap (inv ψ)) (B.pullbackReduced (canonicalLift (inv ψ) Z))
            := by
      simp only [ClosedBlowupSequence.pullbackReduced, hne, dite_false]
    have h2 : ClosedBlowupSequence.extendByClosure (ClosedBlowupSequence.cons Z B) ψ =
        ClosedBlowupSequence.cons (Z.map ψ) (ClosedBlowupSequence.extendByClosure B
          (eqToHom (congrArg blowUp hcm.symm) ≫ canonicalLift ψ (Z.map ψ))) := by
      rw [ClosedBlowupSequence.extendByClosure, dif_pos hcm]
    rw [h1, h2]
    have hiso := Kollar.isIso_canonicalLift ψ (Z.map ψ)
    haveI : IsIso (eqToHom (congrArg blowUp hcm.symm) ≫ canonicalLift ψ (Z.map ψ)) := inferInstance
    have hc : Stacks.Blowup.IsCartierOver (Z.map ψ) (Over.mk (blowUpToBase (Z.comap (inv ψ)))) := by
      rw [← hmap]; exact Kollar.isCartierOver_blowUpToBase _
    have hfin : canonicalLift (inv ψ) Z ≫ (eqToHom (congrArg blowUp hcm.symm) ≫
        canonicalLift ψ (Z.map ψ)) = eqToHom (congrArg blowUp hmap) := by
      refine Kollar.blowUpLift_ext hc ?_ ?_
      · rw [Category.assoc, Category.assoc, canonicalLift_comp_blowUpToBase ψ (Z.map ψ),
          ← Category.assoc (eqToHom _), Kollar.eqToHom_blowUpToBase hcm.symm, ← Category.assoc,
          canonicalLift_comp_blowUpToBase, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      · exact Kollar.eqToHom_blowUpToBase hmap
    refine heq_of_eq (ClosedBlowupSequence.cons_eq_cons_iff.2 ⟨hmap, ?_⟩)
    exact ih hB.2 (eqToHom (congrArg blowUp hcm.symm) ≫ canonicalLift ψ (Z.map ψ))
      (canonicalLift (inv ψ) Z) (congrArg blowUp hmap) hfin

/-- **Deleting the first (empty) blow-up.** If the first centre of a sequence is empty and the
rest has no empty blow-ups, the reduction is the rest, pulled back along the inverse of
`B_∅X ≅ X`, and it is of order `≥ μ` as soon as the rest is. -/
private theorem reduction_cons_top {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) (Z : X.IdealSheafData)
    (ht : IsTriple s a.I E) (hm : 1 ≤ a.m)
    (hZ : Z = ⊤) (B : ClosedBlowupSequence (blowUp Z)) (hB : B.HasNoEmptyBlowups)
    (hGe : B.IsOrderGeMarkedTripleSeq (blowUpToBase Z ≫ s) ⟨a.I.comap (blowUpToBase Z), a.m⟩
      (E.comap (blowUpToBase Z))) :
    (ClosedBlowupSequence.cons Z B).reduction.IsOrderGeMarkedTripleSeq s a E := by
  subst hZ
  have hred : (ClosedBlowupSequence.cons (⊤ : X.IdealSheafData) B).reduction =
      B.extendByClosure (blowUpToBase (⊤ : X.IdealSheafData)) := by
    have hc : (⊤ : X.IdealSheafData).comap (𝟙 X) = ⊤ := by simp
    have := ClosedBlowupSequence.isIso_blowUpToBase_top X
    unfold ClosedBlowupSequence.reduction
    rw [Kollar.pullbackReduced_cons_of_eq_top _ _ _ hc]
    exact eq_of_heq (pullbackReduced_heq_extendByClosure B hB (blowUpToBase ⊤) _ rfl
      (by rw [blowUpLift_comp]; rfl))
  rw [hred]
  haveI := ClosedBlowupSequence.isIso_blowUpToBase_top X
  exact ClosedBlowupSequence.isOrderGeMarkedTripleSeq_extendByClosure_of_cosupport_subset B
    (blowUpToBase ⊤) s a E hm ht
    (fun x _ => Surjective.surj (f := blowUpToBase (⊤ : X.IdealSheafData)) x) hGe

/-- **Back to `I`.** A smooth blow-up sequence of order `≥ m!` for `(X, W_{m!}(I), m!, E)` is one
of order `m` for `(X, I, E)` when `maxord I = m`. -/
private theorem back_of_ge {n m : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmax : maxOrder t.I = m) (B : ClosedBlowupSequence t.X)
    (hB : B.IsOrderGeMarkedTripleSeq t.sX ⟨maximalCoefficientIdeal t.sX t.I (m.factorial : ℤ),
        m.factorial⟩ t.E) : B.IsOrderMTripleSeq t.sX t.I t.E m := by
  have hm' : (maxOrder t.I).toNat = m := by rw [hmax]; rfl
  have hcomp := pos_topologicalKrullDim_of_mem_irreducibleComponents ht.2.2.2.2.1
      (by rw [hdim]; exact_mod_cast hn)
  have hsm := (ClosedBlowupSequence.IsOrderGeMarkedTripleSeq.isSmooth_and_centersHaveSNCWith _ _ _
      B hB).1
  have := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_maximalCoefficientIdeal_of_dvd
    t.sX t.I t.E ht hcomp (by omega) m.factorial (Nat.factorial_pos m)
    (hm' ▸ Nat.dvd_factorial (by omega) le_rfl) B hsm).2 hB
  rw [hm'] at this
  exact ((ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E ht
    m hmax B).1.1 this)

/-- The sequence `𝓜_{n-1,μ}(S, W_0𝒪_S, μ, E_S)` has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_M {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    (S.support : Set (blowUp Z)).Nonempty → (M (n - 1) μ tS).HasNoEmptyBlowups := by
  intro μ W Z π S τ tS hne
  have htS : tS ∈ markedTriplesOfDim {n - 1} μ := tS_mem t ht hm hmax hj hn hdim hne
  have hμ : 1 ≤ μ := Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
  obtain ⟨F, htS', hFM⟩ := exists_toFun_eq_of_isMarkedOrderReductionFamily M hM hμ
    (by omega : n - 1 ≤ N - 1) htS
  exact hFM ▸ F.hasNoEmptyBlowups tS htS'

/-- **Kollár 3.102, up to "Back to `I`"**: `π_{-1}` followed by `τ_*𝐁_S` is of order `≥ μ` for
`(X, W_μ(I), μ, E)`. -/
private theorem bd_seq_ge {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    ∀ BS : ClosedBlowupSequence S.subscheme,
      (BS = .nil _ ∨ ((S.support : Set (blowUp Z)).Nonempty ∧ BS = M (n - 1) μ tS)) →
      (ClosedBlowupSequence.cons Z (BS.pushforward τ)).IsOrderGeMarkedTripleSeq t.sX W t.E := by
  intro μ W Z π S τ tS BS hBS
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, heq, -, hE⟩ := ht
  haveI : CharZero t.k := hchar
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso π := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  have hsnc := hasSNCWith_divisorComponentCentre t ht' W ⟨j, hj⟩
  have hTW := isTriple_maximalCoefficientIdeal_factorial t ht' hdim hn hm hmax
  have hEdv : IsTriple (π ≫ t.sX) (W.birationalTransform Z).I (t.E.totalTransform Z) :=
    isTriple_birationalTransform_totalTransform W hTW hsnc
  have hEpure : ∀ i, MMP.Mori.IsPureCodimOne (t.E.E i).support := fun i => (hE.2.1 i).2.1
  have hEc : IsClosed t.E.support := isClosed_iUnion_of_finite fun i => (t.E.E i).support.isClosed
  have hsupp : (t.E.totalTransform Z).support = (t.E.comap π).support := by
    rw [OrderedDivisor.support_totalTransform t.E hEpure Z, totalTransformStep_eq _ hEc,
      support_comap_orderedDivisor]
    have hZE : (Z.support : Set t.X) ⊆ t.E.support := by
      obtain ⟨-, hEpure', hEsm⟩ := hE.2.1 ⟨j, hj⟩
      intro x hx
      have := (divisorComponentCentre_spec t.sX W (t.E.E ⟨j, hj⟩) hEsm hEpure').2.2.1 hx
      exact Set.mem_iUnion.2 ⟨⟨j, hj⟩, this⟩
    rw [Set.union_eq_left.2 hZE]
  exact ⟨hTW, isSmoothScheme_of_hasSNCWith t ht' Z hsnc,
    hasComponentsOfPositiveCodim_divisorComponentCentre t ht' W ⟨j, hj⟩, hsnc,
    orderAlongGE_divisorComponentCentre t ht' W ⟨j, hj⟩,
    pushforward_core M hN hM t ht' hdim hn hnN hm hmax hj (t.E.totalTransform Z) hEdv hsupp BS hBS⟩

/-- The same, for the divisor `π⁻¹E` instead of the total transform (used when `Z_{-1}` is
empty). -/
private theorem bd_seq_ge_comap {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    ∀ BS : ClosedBlowupSequence S.subscheme,
      (BS = .nil _ ∨ ((S.support : Set (blowUp Z)).Nonempty ∧ BS = M (n - 1) μ tS)) →
      (BS.pushforward τ).IsOrderGeMarkedTripleSeq (π ≫ t.sX) (W.birationalTransform Z)
        (t.E.comap π) := by
  intro μ W Z π S τ tS BS hBS
  have ht' := ht
  obtain ⟨hchar, hsm, hlft, hqc, heq, -, hE⟩ := ht
  haveI : CharZero t.k := hchar
  haveI : LocallyOfFiniteType t.sX := hlft
  haveI : QuasiCompact t.sX := hqc
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI hiso : IsIso π := isIso_blowUpToBase_centre t ht' W ⟨j, hj⟩
  have hsnc := hasSNCWith_divisorComponentCentre t ht' W ⟨j, hj⟩
  have hTW := isTriple_maximalCoefficientIdeal_factorial t ht' hdim hn hm hmax
  have hEdv : IsTriple (π ≫ t.sX) (W.birationalTransform Z).I (t.E.totalTransform Z) :=
    isTriple_birationalTransform_totalTransform W hTW hsnc
  have hEdv2 : IsTriple (π ≫ t.sX) (W.birationalTransform Z).I (t.E.comap π) :=
    ⟨hEdv.1, hEdv.2.1, hEdv.2.2.1, hEdv.2.2.2.1, hEdv.2.2.2.2.1, hEdv.2.2.2.2.2.1,
      comap_isOrderedSNC t ht' π⟩
  exact pushforward_core M hN hM t ht' hdim hn hnN hm hmax hj (t.E.comap π) hEdv2 rfl BS hBS

/-- **Kollár 3.102**: the sequence `(π_{-1}, τ_*𝐁_S)` with empty blow-ups deleted is of order
`≥ μ` for `(X, W_μ(I), μ, E)`. -/
private theorem bd_seq_reduced {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
        ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    ∀ BS : ClosedBlowupSequence S.subscheme,
      (BS = .nil _ ∨ ((S.support : Set (blowUp Z)).Nonempty ∧ BS = M (n - 1) μ tS)) →
      ((ClosedBlowupSequence.cons Z (BS.pushforward τ)).reduction).IsOrderGeMarkedTripleSeq
        t.sX W t.E := by
  intro μ W Z π S τ tS BS hBS
  have hnoempty : (BS.pushforward τ).HasNoEmptyBlowups := by
    rcases hBS with h | ⟨hne, h⟩
    · subst h; rw [pushforward_nil]; trivial
    · subst h
      unfold ClosedBlowupSequence.pushforward
      split_ifs with hh
      · exact hasNoEmptyBlowups_of_isPushforward _ τ _ hh.choose_spec
          (hasNoEmptyBlowups_M M hN hM t ht hdim hn hnN hm hmax hj hne)
      · trivial
  by_cases hZ : Z = ⊤
  · have hGe := bd_seq_ge_comap M hN hM t ht hdim hn hnN hm hmax hj BS hBS
    have hm1 : 1 ≤ W.m := Nat.factorial_pos m
    have hW0 : W.birationalTransform Z = ⟨W.I.comap π, W.m⟩ := by
      have := twist_eq_of_top t ht hdim hn hm hmax hj hZ
      show (⟨(W.birationalTransform Z).I, (W.birationalTransform Z).m⟩ : MarkedIdeal _) = _
      rw [this]; rfl
    rw [hW0] at hGe
    exact reduction_cons_top t.sX W t.E Z
      (isTriple_maximalCoefficientIdeal_factorial t ht hdim hn hm hmax) hm1 hZ (BS.pushforward τ)
          hnoempty hGe
  · have hne : (ClosedBlowupSequence.cons Z (BS.pushforward τ)).HasNoEmptyBlowups :=
      ⟨hZ, hnoempty⟩
    rw [ClosedBlowupSequence.reduction_eq_self hne]
    exact bd_seq_ge M hN hM t ht hdim hn hnN hm hmax hj BS hBS

end BDFunctor

open BDFunctor in
/-- **Kollár, Lemma 3.102 (opening clause).** Let `𝓜` be a marked order-reduction family on
dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, I, E)` a triple of dimension `n`
with `1 ≤ n ≤ N`, `E^j` an entry of `E` (`0`-based index `j`) and `m ≥ 1` with `maxord I ≤ m`.
Then `bdFunctor M n m j (X, I, E)` is a smooth blow-up sequence of order `m` starting with
`(X, I, E)` (`ClosedBlowupSequence.IsOrderMTripleSeq`).

Moreover, if `maxord I = m`, then with `μ = m!`, `W = W_μ(I)`, `π` the blow-up of
`Z = Z_{-1}(W, μ, E^j)`, `S = π⁻¹E^j` with inclusion `τ` and
`𝐁_S = M (n - 1) μ (S, W_0𝒪_S, μ, E_S)`, if `S ≠ ∅` then the sequence before deleting empty
blow-ups, `π` followed by `τ_*𝐁_S`, is already of order `m` for `(X, I, E)`. -/
@[mmp "lem_kr3e_bd_is_sequence_of_order_m"]
public theorem bdFunctor_isOrderMTripleSeq {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) (hj : j < t.E.s) :
    (bdFunctor M n m j t).IsOrderMTripleSeq t.sX t.I t.E m ∧
      (maxOrder t.I = m →
        let μ := m.factorial
        let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
        let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
        let π := blowUpToBase Z
        let S := (t.E.E ⟨j, hj⟩).comap π
        let τ := S.subschemeι
        let tS : MarkedTriple.{u} :=
          ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap τ,
            ((t.E.comap π).deleteIndex j).comap τ⟩, t.k, τ ≫ π ≫ t.sX⟩, μ⟩
        let BS : ClosedBlowupSequence S.subscheme := M (n - 1) μ tS
        (S.support : Set (blowUp Z)).Nonempty →
          (ClosedBlowupSequence.cons Z (BS.pushforward τ)).IsOrderMTripleSeq
            t.sX t.I t.E m) := by
  refine ⟨?_, fun hmax' => ?_⟩
  · rw [bdFunctor]
    split_ifs with h
    · exact back_of_ge t ht hdim hn hm h.1 _
        (bd_seq_reduced M hN hM t ht hdim hn hnN hm h.1 hj _
          (by split_ifs with h' <;> simp_all))
    · exact ht
  · intro μ W Z π S τ tS BS hS
    exact back_of_ge t ht hdim hn hm hmax' _
      (bd_seq_ge M hN hM t ht hdim hn hnN hm hmax' hj BS (Or.inr ⟨hS, rfl⟩))

namespace BDFunctor

/-- Every blow-up sequence on `S` has a push-forward along a closed immersion `j : S → X`
(Kollár 3.30.3). -/
private theorem exists_isPushforward {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : ClosedBlowupSequence S) : ∃ BX, ClosedBlowupSequence.IsPushforward j BS BX := by
  induction BS generalizing X with
  | nil S => exact ⟨.nil X, trivial⟩
  | cons ZS BS ih =>
    have h : (ZS.map j).comap j = ZS :=
      ZS.comap_map_of_isClosedImmersion j
    obtain ⟨BX, hBX⟩ := ih (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j (ZS.map j))
    exact ⟨.cons (ZS.map j) BX, h, rfl, hBX⟩

/-- The chosen push-forward along a closed immersion is a push-forward. -/
private theorem isPushforward_pushforward {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : ClosedBlowupSequence S) :
    ClosedBlowupSequence.IsPushforward j BS (BS.pushforward j) := by
  have h := exists_isPushforward j BS
  rw [ClosedBlowupSequence.pushforward, dif_pos h]
  exact h.choose_spec

/-- The truncations of a smooth blow-up sequence of order `≥ m` are such sequences. -/
private theorem isOrderGePlainSeq_truncate {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (i : ℕ), B.IsOrderGePlainSeq s a → (B.truncate i).IsOrderGePlainSeq s a
  | _, .nil _, _, _, _, h => h
  | _, .cons Z B, _, _, 0, h => ⟨h.1, h.2.1⟩
  | _, .cons Z B, _, _, i + 1, h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      isOrderGePlainSeq_truncate B _ _ i h.2.2.2.2.2⟩

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, K, m)`, the formal
transform `N_r·D_r⁻¹` of `N = K·D` has `N_r = K_r·D_r`, `K_r` the iterated marked transform. -/
private theorem formalTransformAux_num_eq {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (D : X.IdealSheafData), B.IsOrderGePlainSeq s a →
      (B.formalTransformAux (a.I * D) D a.m).num =
        (B.markedTransform a).I * (B.formalTransformAux (a.I * D) D a.m).den
  | _, .nil _, _, _, _, _ => rfl
  | _, .cons Z B, s, a, D, h => by
    have hmul := MarkedIdeal.birationalTransform_mul_eq s h.1 Z h.2.2.1 h.2.2.2.1 a h.2.2.2.2.1
    have key : (a.I * D).comap (blowUpToBase Z) =
        (a.birationalTransform Z).I * (D.comap (blowUpToBase Z) * Z.comap (blowUpToBase Z) ^ a.m)
            := by
      rw [Stacks.IdealSheaf.comap_mul, ← hmul]; ring
    change (B.formalTransformAux ((a.I * D).comap (blowUpToBase Z))
        (D.comap (blowUpToBase Z) * Z.comap (blowUpToBase Z) ^ a.m) a.m).num =
      (B.markedTransform (a.birationalTransform Z)).I * (B.formalTransformAux
        ((a.I * D).comap (blowUpToBase Z))
        (D.comap (blowUpToBase Z) * Z.comap (blowUpToBase Z) ^ a.m) a.m).den
    rw [key]
    exact formalTransformAux_num_eq B _ (a.birationalTransform Z) _ h.2.2.2.2.2

/-- The first marked ideal of a smooth blow-up sequence of order `≥ m` starting with a marked
triple is a triple. -/
private theorem isTriple_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k] {X : Scheme.{u}}
    {B : ClosedBlowupSequence X} {s : X ⟶ Spec (.of k)} {a : MarkedIdeal X} {E : OrderedDivisor X}
    (h : B.IsOrderGeMarkedTripleSeq s a E) : IsTriple s a.I E := by
  cases B with
  | nil => exact h
  | cons Z B => exact h.1

/-- The centres of a push-forward along a closed immersion `j : S → X` lie in the images of the
blown-up `S_i`. -/
private theorem support_subset_range_pullbackHom_of_isPushforward {X : Scheme.{u}}
    (B' : ClosedBlowupSequence X) : ∀ {S : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
      {BS : ClosedBlowupSequence S} (Z : B'.target.IdealSheafData)
      (C : ClosedBlowupSequence (blowUp Z)),
      ClosedBlowupSequence.IsPushforward j BS (B'.append (.cons Z C)) →
        (Z.support : Set B'.target) ⊆ Set.range (B'.pullbackHom j) := by
  induction B' with
  | nil X =>
    intro S j _ BS Z C hP
    cases BS with
    | nil => exact hP.elim
    | cons ZS BS =>
      obtain ⟨-, rfl, -⟩ := hP
      have hle : j.ker ≤ ZS.map j := by
        rw [← Scheme.IdealSheafData.map_bot]
        exact Scheme.IdealSheafData.map_mono j bot_le
      have h : ((ZS.map j).support : Set X) ⊆ (j.ker.support : Set X) :=
        Scheme.IdealSheafData.support_antitone hle
      rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq] at h
      exact h
  | cons Z' B' ih =>
    intro S j _ BS Z C hP
    cases BS with
    | nil => exact hP.elim
    | cons ZS BS =>
      obtain ⟨hc, -, hP⟩ := hP
      subst hc
      rw [eqToHom_refl, Category.id_comp] at hP
      exact ih (canonicalLift j Z') Z C hP

/-- In the setting of `𝓑𝓓_{n,m,j}`, the pull-back `S = π⁻¹E^j` of the entry `E^j` to
`X_0 = B_{Z_{-1}}X` is a smooth hypersurface. -/
private theorem isSmoothHypersurface_comap_blowUpToBase (t : FieldBlowupTriple.{u})
    (ht : t ∈ triples) (K : MarkedIdeal t.X) (j : ℕ) (hj : j < t.E.s) :
    IsSmoothHypersurface (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩)) ≫ t.sX)
      ((t.E.E ⟨j, hj⟩).comap (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩)))) := by
  obtain ⟨-, hsm, hlft, hqc, -, -, -, hEsnc⟩ := id ht
  haveI := hlft
  haveI := hqc
  have hDj := hEsnc.1 ⟨j, hj⟩
  haveI : IsIso (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩))) :=
    isIso_blowUpToBase_divisorComponentCentre t.sX hsm K _ hDj.2.2 hDj.2.1
  obtain ⟨-, -, -, -, -, -, hE0⟩ := pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht)
    (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩)))
  replace hE0 : IsSNCFamily (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩)) ≫ t.sX)
    (fun i => (t.E.E i).comap (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩)))) := hE0
  exact ⟨(hE0.1 ⟨j, hj⟩).2.2, (hE0.1 ⟨j, hj⟩).2.1⟩

/-- In the setting of `𝓑𝓓_{n,m,j}`, every irreducible component of `X_0 = B_{Z_{-1}}X` has
dimension `n ≥ 1`: the blow-up of the Cartier divisor `Z_{-1}` is an isomorphism. -/
private theorem exists_dim_blowUp (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) {n : ℕ}
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n)
    (K : MarkedIdeal t.X) (j : ℕ) (hj : j < t.E.s) :
    ∃ d : ℕ, 0 < d ∧ ∀ C ∈ irreducibleComponents (blowUp (divisorComponentCentre K (t.E.E ⟨j,
        hj⟩))),
      topologicalKrullDim C = d := by
  obtain ⟨-, hsm, hlft, -, hequi, -, -, hEsnc⟩ := id ht
  haveI := hlft
  have hDj := hEsnc.1 ⟨j, hj⟩
  haveI : IsIso (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩))) :=
    isIso_blowUpToBase_divisorComponentCentre t.sX hsm K _ hDj.2.2 hDj.2.1
  have hdY : topologicalKrullDim (blowUp (divisorComponentCentre K (t.E.E ⟨j, hj⟩))) =
      ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdim]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (blowUpToBase (divisorComponentCentre K (t.E.E ⟨j, hj⟩))).homeomorph.isHomeomorph
  have hequi0 := equidimensional_blowUp t.sX (divisorComponentCentre K (t.E.E ⟨j, hj⟩)) hequi
  replace hdY : topologicalKrullDim (blowUp (divisorComponentCentre K (t.E.E ⟨j, hj⟩))) =
      (n : WithBot ℕ∞) := by rw [hdY]; norm_cast
  refine ⟨n, hn, fun C hC => le_antisymm ?_ ?_⟩
  · rw [← hdY]
    exact topologicalKrullDim_subspace_le _ C
  · rw [← hdY, topologicalKrullDim, Order.krullDim_eq_iSup_height]
    refine iSup_le fun Z' => ?_
    obtain ⟨W', hW', hZW⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible
        (Z' : Set (blowUp (divisorComponentCentre K (t.E.E ⟨j, hj⟩)))) Z'.isIrreducible
    rw [← hequi0 W' hW' C hC]
    calc (Order.height Z' : WithBot ℕ∞) ≤
          (Order.height (⟨W', hW'.1, isClosed_of_mem_irreducibleComponents W' hW'⟩ :
            IrreducibleCloseds _) : WithBot ℕ∞) := by
          exact_mod_cast Order.height_mono (show Z' ≤ _ from hZW)
      _ ≤ topologicalKrullDim W' := AlgebraicGeometry.height_le_topologicalKrullDim _

end BDFunctor

open BDFunctor in
/-- **Restriction commutes with the transforms in `𝓑𝓓` (Kollár, proof of Lemma 3.102).** Let
`M` be a marked order-reduction family on dimensions `0, …, N - 1`, `(X, I, E)` a triple of
dimension `n` with `1 ≤ n ≤ N`, `maxord I = m ≥ 1`, and `j < s`. With `μ = m!`,
`W = W_μ(I)`, `π` the blow-up of `Z = Z_{-1}(W, μ, E^j)`, `S = π⁻¹E^j` with inclusion `τ`,
`𝐁_S = M (n - 1) μ (S, W_0𝒪_S, μ, E_S)` and `P = τ_*𝐁_S`, suppose `S ≠ ∅`. Then for every `i`
the restriction of the `i`-th truncation of `P` to `S` is the `i`-th truncation of `𝐁_S`, and
the formal transform `T_i(W_0, μ) = N_i·D_i⁻¹` along `P` satisfies
`N_i|_{S_i} = J_i·D_i|_{S_i}`, where `J_i` is the `i`-th marked transform of `(W_0𝒪_S, μ)`. -/
@[mmp "lem_kr3e_bd_restriction_transform"]
public theorem bdFunctor_formalTransform_restrict_eq {N n m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) :
    let μ := m.factorial
    let W : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩
    let Z := divisorComponentCentre W (t.E.E ⟨j, hj⟩)
    let π := blowUpToBase Z
    let S := (t.E.E ⟨j, hj⟩).comap π
    let τ := S.subschemeι
    let W₀ := (W.birationalTransform Z).I
    let tS : MarkedTriple.{u} :=
      ⟨⟨⟨S.subscheme, W₀.comap τ, ((t.E.comap π).deleteIndex j).comap τ⟩,
        t.k, τ ≫ π ≫ t.sX⟩, μ⟩
    let BS : ClosedBlowupSequence S.subscheme := M (n - 1) μ tS
    let P := BS.pushforward τ
    (S.support : Set (blowUp Z)).Nonempty →
      ∀ i : ℕ, (P.truncate i).restrict S = BS.truncate i ∧
        (P.formalTransform W₀ μ i).num.comap ((P.truncate i).restrictHom S) =
          (((P.truncate i).restrict S).markedTransform ⟨W₀.comap τ, μ⟩).I *
            (P.formalTransform W₀ μ i).den.comap ((P.truncate i).restrictHom S) := by
  intro μ W Z π S τ W₀ tS BS P hS i
  have hP : ClosedBlowupSequence.IsPushforward τ BS P := isPushforward_pushforward τ BS
  have hres : P.restrict S = BS := Kollar.restrict_eq_of_isPushforward S hP
  refine ⟨?_, ?_⟩
  · change (P.truncate i).pullback S.subschemeι = _
    rw [← Kollar.pullback_truncate]
    exact congrArg (·.truncate i) hres
  · have hseq : (ClosedBlowupSequence.cons Z P).IsOrderMTripleSeq t.sX t.I t.E m :=
      (bdFunctor_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le hj).2 hmax hS
    have hmt : (ClosedBlowupSequence.cons Z P).IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E :=
      (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E ht m
        hmax _).1.2 hseq
    have hm' : (maxOrder t.I).toNat = m := by rw [hmax]; rfl
    have hcomp := pos_topologicalKrullDim_of_mem_irreducibleComponents ht.2.2.2.2.1
      (by rw [hdim]; exact_mod_cast hn)
    have hsm := (ClosedBlowupSequence.IsOrderGeMarkedTripleSeq.isSmooth_and_centersHaveSNCWith
      _ _ _ _ hmt).1
    have hW : (ClosedBlowupSequence.cons Z P).IsOrderGeMarkedTripleSeq t.sX W t.E :=
      (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_maximalCoefficientIdeal_of_dvd
        t.sX t.I t.E ht hcomp (by omega) μ (Nat.factorial_pos m)
        (hm' ▸ Nat.dvd_factorial (by omega) le_rfl) _ hsm).1 (by rw [hm']; exact hmt)
    have hP0 : P.IsOrderGeMarkedTripleSeq (π ≫ t.sX) (W.birationalTransform Z)
        (t.E.totalTransform Z) := hW.2.2.2.2.2
    have hB : P.IsOrderGePlainSeq (π ≫ t.sX) ⟨W₀, μ⟩ :=
      isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq P _ _ _ hP0
    obtain ⟨hchar, hsm0, -, hqc0, -, hnz0, -⟩ := isTriple_of_isOrderGeMarkedTripleSeq hP0
    haveI : CharZero t.k := hchar
    haveI : QuasiCompact (π ≫ t.sX) := hqc0
    haveI : Smooth (π ≫ t.sX) := MMP.Mori.IsSmoothScheme.smooth hsm0
    have hJS : IsNonzeroAtGenericPoints (W₀.comap τ) :=
      (bdFunctor_input_mem_markedTriplesOfDim t ht hm hmax hj hn hdim hS).1.2.2.2.2.2.1
    obtain ⟨-, hkr⟩ := ClosedBlowupSequence.IsOrderGePlainSeq.restrict (π ≫ t.sX)
      (exists_dim_blowUp t ht hdim hn W j hj) (isSmoothHypersurface_comap_blowUpToBase t ht W j hj)
      (Nat.factorial_pos m) hnz0 hJS hB (fun B' Z C h =>
          support_subset_range_pullbackHom_of_isPushforward B' τ Z C (h ▸ hP))
    rw [hkr i]
    change _ = ((P.truncate i).markedTransform ⟨W₀, μ⟩).I.comap _ * _
    rw [← Stacks.IdealSheaf.comap_mul]
    congr 1
    have e : W₀ * ⊤ = W₀ := by rw [← Scheme.IdealSheafData.one_eq_top, mul_one]
    have := formalTransformAux_num_eq (P.truncate i) _ ⟨W₀, μ⟩ ⊤
      (isOrderGePlainSeq_truncate P _ _ i hB)
    simp only [e] at this
    exact this

namespace BDFunctor

open CategoryTheory.Limits ClosedBlowupSequence MMP.Resolution.Aux

section PartI

private theorem isPushforward_unique : ∀ {S X : Scheme.{u}} (j : S ⟶ X) (BS : ClosedBlowupSequence
    S)
    (B1 B2 : ClosedBlowupSequence X), IsPushforward j BS B1 → IsPushforward j BS B2 → B1 = B2
  | _, _, _, .nil _, .nil _, .nil _, _, _ => rfl
  | _, _, _, .nil _, .nil _, .cons _ _, _, h => h.elim
  | _, _, _, .nil _, .cons _ _, _, h, _ => h.elim
  | _, _, j, .cons ZS BS, .cons Z1 B1, .cons Z2 B2, hP1, hP2 => by
    obtain ⟨h1, e1, p1⟩ := hP1
    obtain ⟨h2, e2, p2⟩ := hP2
    obtain rfl : Z1 = Z2 := e1.trans e2.symm
    rw [isPushforward_unique _ BS B1 B2 p1 p2]
  | _, _, _, .cons _ _, .nil _, _, h, _ => h.elim
  | _, _, _, .cons _ _, .cons _ _, .nil _, _, h => h.elim

private theorem comap_map_eq_map_comap_of_isPullback {S X S' X' : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j] (g : X' ⟶ X) (gS : S' ⟶ S) (j' : S' ⟶ X')
    (sq : IsPullback gS j' j g) (ZS : S.IdealSheafData) :
    (ZS.map j).comap g = (ZS.comap gS).map j' := by
  have sq1 : IsPullback (ZS.comap gS).subschemeι
      ((ZS.comapIso gS).hom ≫ pullback.snd gS ZS.subschemeι) gS ZS.subschemeι := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (ZS.comapIso gS) ?_ ?_
    · simp [pullback.condition]
    · simp
    · simp
  have sq3 := sq1.paste_horiz sq.flip
  have : IsClosedImmersion (ZS.subschemeι ≫ j) := inferInstance
  rw [Scheme.IdealSheafData.map, Scheme.IdealSheafData.map,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion (ZS.subschemeι ≫ j) g]
  rw [← sq3.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

private theorem isPullback_canonicalLift_square {S X S' X' : Scheme.{u}} (j : S ⟶ X) (g : X' ⟶ X)
    [Flat g]
    (gS : S' ⟶ S) [Flat gS] (j' : S' ⟶ X') (sq : IsPullback gS j' j g) (ZX : X.IdealSheafData)
    (j'₁ : blowUp ((ZX.comap j).comap gS) ⟶ blowUp (ZX.comap g))
    (hj : j'₁ ≫ blowUpToBase (ZX.comap g) = blowUpToBase ((ZX.comap j).comap gS) ≫ j') :
    IsPullback (canonicalLift gS (ZX.comap j)) j'₁ (canonicalLift j ZX) (canonicalLift g ZX) := by
  have α := Kollar.isPullback_canonicalLift_of_flat gS (ZX.comap j)
  have β := Kollar.isPullback_canonicalLift_of_flat g ZX
  have hcart : Stacks.Blowup.IsCartierOver ZX
      (Over.mk (blowUpToBase ((ZX.comap j).comap gS) ≫ gS ≫ j)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (ZX.comap (blowUpToBase ((ZX.comap j).comap
        gS) ≫ gS ≫ j))
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  have w : canonicalLift gS (ZX.comap j) ≫ canonicalLift j ZX = j'₁ ≫ canonicalLift g ZX := by
    refine (blowUpLift_unique ZX _ hcart _ ?_).trans (blowUpLift_unique ZX _ hcart _ ?_).symm
    · rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
        canonicalLift_comp_blowUpToBase, Category.assoc]
    · rw [Category.assoc, canonicalLift_comp_blowUpToBase, reassoc_of% hj, ← sq.w]
  have outer : IsPullback (canonicalLift gS (ZX.comap j)) (j'₁ ≫ blowUpToBase (ZX.comap g))
      (canonicalLift j ZX ≫ blowUpToBase ZX) g := by
    have := (α.paste_horiz sq.flip).flip
    rwa [hj, canonicalLift_comp_blowUpToBase]
  exact outer.of_bot w β.flip

private theorem blowUpLift_eq_inv_comp {X X' : Scheme.{u}} (Z : X.IdealSheafData) (g : X' ⟶ X)
    (hZ : Z.comap g = ⊤) [IsIso (blowUpToBase (Z.comap g))] :
    blowUpLift Z g (ClosedBlowupSequence.isCartierOver_of_comap_eq_top g Z hZ) =
      inv (blowUpToBase (Z.comap g)) ≫ canonicalLift g Z := by
  refine (blowUpLift_unique Z g _ _ ?_).symm
  rw [Category.assoc, canonicalLift_comp_blowUpToBase]
  simp

private theorem isPushforward_pullbackReduced : ∀ {S X : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j]
    (BS : ClosedBlowupSequence S) (BX : ClosedBlowupSequence X), IsPushforward j BS BX →
    ∀ {S' X' : Scheme.{u}} (g : X' ⟶ X) [Flat g] (gS : S' ⟶ S) (j' : S' ⟶ X'),
      IsPullback gS j' j g →
      IsPushforward j' (BS.pullbackReduced gS) (BX.pullbackReduced g)
  | _, _, _, _, .nil _, .nil _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, .nil _, .cons _ _, hP, _, _, _, _, _, _, _ => hP.elim
  | _, _, _, _, .cons _ _, .nil _, hP, _, _, _, _, _, _, _ => hP.elim
  | _, _, j, _, .cons ZS BS, .cons ZX BX, hP, S', X', g, _, gS, j', sq => by
    obtain ⟨hc, hm, hP'⟩ := hP
    subst hc
    haveI : Flat gS := MorphismProperty.of_isPullback (P := @Flat) sq.flip inferInstance
    have hcomm : (ZX.comap j).comap gS = (ZX.comap g).comap j' := by
      rw [← Scheme.IdealSheafData.comap_comp, sq.w, Scheme.IdealSheafData.comap_comp]
    have hL1 : ZX.comap g = ((ZX.comap j).comap gS).map j' := by
      calc ZX.comap g = ((ZX.comap j).map j).comap g := by rw [← hm]
        _ = _ := comap_map_eq_map_comap_of_isPullback j g gS j' sq _
    have hiff : (ZX.comap g = ⊤) ↔ ((ZX.comap j).comap gS = ⊤) := by
      constructor
      · intro h
        rw [hcomm, h]
        simp
      · intro h
        rw [hL1, h]
        simp
    haveI : IsClosedImmersion (eqToHom (congrArg blowUp rfl) ≫ canonicalLift j ZX) := by
      rw [eqToHom_refl, Category.id_comp]; infer_instance
    simp only [eqToHom_refl, Category.id_comp] at hP'
    by_cases hZ : ZX.comap g = ⊤
    · have hZS := hiff.1 hZ
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, hZS, dite_true]
      haveI hiX := Kollar.isIso_blowUpToBase_of_eq_top hZ
      haveI hiS := Kollar.isIso_blowUpToBase_of_eq_top hZS
      rw [blowUpLift_eq_inv_comp ZX g hZ, blowUpLift_eq_inv_comp (ZX.comap j) gS hZS]
      haveI : Flat (canonicalLift g ZX) := Kollar.flat_canonicalLift g ZX
      haveI : Flat (inv (blowUpToBase (ZX.comap g)) ≫ canonicalLift g ZX) := inferInstance
      have hj : (blowUpToBase ((ZX.comap j).comap gS) ≫ j' ≫ inv (blowUpToBase (ZX.comap g))) ≫
          blowUpToBase (ZX.comap g) = blowUpToBase ((ZX.comap j).comap gS) ≫ j' := by simp
      have Q := isPullback_canonicalLift_square j g gS j' sq ZX _ hj
      refine isPushforward_pullbackReduced (canonicalLift j ZX) BS BX hP' _ _ j' ?_
      refine Q.of_iso (asIso (blowUpToBase ((ZX.comap j).comap gS))) (Iso.refl _)
        (asIso (blowUpToBase (ZX.comap g))) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
    · have hZS : ¬ ((ZX.comap j).comap gS = ⊤) := fun h => hZ (hiff.2 h)
      simp only [ClosedBlowupSequence.pullbackReduced, hZ, hZS, dite_false]
      refine ⟨hcomm.symm, hL1, ?_⟩
      haveI : Flat (canonicalLift g ZX) := Kollar.flat_canonicalLift g ZX
      haveI : Flat (canonicalLift gS (ZX.comap j)) := Kollar.flat_canonicalLift gS (ZX.comap j)
      have hj : (eqToHom (congrArg blowUp hcomm) ≫
          canonicalLift j' (ZX.comap g)) ≫ blowUpToBase (ZX.comap g) =
          blowUpToBase ((ZX.comap j).comap gS) ≫ j' := by
        rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
          ClosedBlowupSequence.eqToHom_comp_blowUpToBase hcomm]
      have Q := isPullback_canonicalLift_square j g gS j' sq ZX _ hj
      exact isPushforward_pullbackReduced (canonicalLift j ZX) BS BX hP' _ _ _ Q

private theorem pushforward_eq_of_isPushforward {S X : Scheme.{u}} (j : S ⟶ X) {B :
    ClosedBlowupSequence S}
    {B' : ClosedBlowupSequence X} (h : IsPushforward j B B') : B.pushforward j = B' := by
  have hex : ∃ B'', IsPushforward j B B'' := ⟨B', h⟩
  unfold ClosedBlowupSequence.pushforward
  rw [dif_pos hex]
  exact isPushforward_unique j B _ _ hex.choose_spec h

private theorem pushforward_pullbackReduced {S X S' X' : Scheme.{u}} (j : S ⟶ X)
    [IsClosedImmersion j]
    (g : X' ⟶ X) [Flat g] (gS : S' ⟶ S) (j' : S' ⟶ X') (sq : IsPullback gS j' j g)
    (BS : ClosedBlowupSequence S) :
    (BS.pullbackReduced gS).pushforward j' = (BS.pushforward j).pullbackReduced g := by
  obtain ⟨B, hB⟩ := exists_isPushforward j BS
  rw [pushforward_eq_of_isPushforward j hB]
  exact pushforward_eq_of_isPushforward j' (isPushforward_pullbackReduced j BS B hB g gS j' sq)

end PartI

section PartIII

/-- The marked triple `(S, W_0𝒪_S, μ, E_S)` fed to `𝓜` by `𝓑𝓓`, for a given `S ⊆ B_ZX`. -/
private noncomputable def bdTS (m j : ℕ) (t : FieldBlowupTriple.{u}) (W : MarkedIdeal t.X)
    (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData) : MarkedTriple.{u} :=
  ⟨⟨⟨S.subscheme, (W.birationalTransform Z).I.comap S.subschemeι,
    ((t.E.comap (blowUpToBase Z)).deleteIndex j).comap S.subschemeι⟩, t.k,
    S.subschemeι ≫ blowUpToBase Z ≫ t.sX⟩, m.factorial⟩

open Classical in
/-- The blow-up sequence `𝐁_S = 𝓜_{n-1,μ}(S, W_0𝒪_S, μ, E_S)` of `𝓑𝓓` (empty if `S = ∅` or the
input is not a marked triple). -/
private noncomputable def bdBS (M : MarkedFamily.{u}) (n m j : ℕ) (t : FieldBlowupTriple.{u})
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData) :
    ClosedBlowupSequence S.subscheme :=
  if (S.support : Set (blowUp Z)).Nonempty ∧ bdTS m j t W Z S ∈ markedTriples
    then M (n - 1) m.factorial (bdTS m j t W Z S) else .nil _

/-- The body of `𝓑𝓓`, with the centre `Z` and the divisor `S = π⁻¹E^j` as parameters. -/
private noncomputable def bdBody (M : MarkedFamily.{u}) (n m j : ℕ) (t : FieldBlowupTriple.{u})
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData) :
    ClosedBlowupSequence t.X :=
  (ClosedBlowupSequence.cons Z ((bdBS M n m j t W Z S).pushforward S.subschemeι)).reduction

private theorem bdFunctor_eq_bdBody (M : MarkedFamily.{u}) (n m j : ℕ) (t : FieldBlowupTriple.{u})
    (h : maxOrder t.I = m ∧ j < t.E.s) :
    bdFunctor M n m j t = bdBody M n m j t
      ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩
      (divisorComponentCentre ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩
        (t.E.E ⟨j, h.2⟩))
      ((t.E.E ⟨j, h.2⟩).comap (blowUpToBase (divisorComponentCentre
        ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩ (t.E.E ⟨j, h.2⟩)))) := by
  unfold bdFunctor
  rw [dif_pos h]
  rfl

private theorem reduction_cons_pullbackReduced {X Y : Scheme.{u}} (Z : X.IdealSheafData)
    (B : ClosedBlowupSequence (blowUp Z)) (h : Y ⟶ X) :
    (ClosedBlowupSequence.cons (Z.comap h) (B.pullbackReduced (canonicalLift h Z))).reduction =
      ((ClosedBlowupSequence.cons Z B).pullback h).reduction := by
  change _ = (ClosedBlowupSequence.cons (Z.comap h) (B.pullback (canonicalLift h Z))).reduction
  rw [← reduction_pullback]
  exact reduction_append_congr (ClosedBlowupSequence.cons (Z.comap h) (.nil _))
    (reduction_reduction _)

/-- A blow-up sequence pulled back (with deletion of empty blow-ups) along a morphism from an
empty scheme is empty. -/
private theorem pullbackReduced_eq_nil_of_isEmpty : ∀ {X Y : Scheme.{u}} [IsEmpty Y]
    (B : ClosedBlowupSequence X) (g : Y ⟶ X), B.pullbackReduced g = .nil Y
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons Z B, g => by
    have hZ : Z.comap g = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      refine eq_bot_iff.2 fun y => (IsEmpty.false y).elim
    simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
    exact pullbackReduced_eq_nil_of_isEmpty B _

/-- The induced morphism `f⁻¹S → S` of closed subschemes. -/
private noncomputable def subschemeComapMap {X' X : Scheme.{u}} (S : X.IdealSheafData)
    (f : X' ⟶ X) : (S.comap f).subscheme ⟶ S.subscheme :=
  (S.comapIso f).hom ≫ pullback.snd f S.subschemeι

private theorem isPullback_subschemeComapMap {X' X : Scheme.{u}} (S : X.IdealSheafData)
    (f : X' ⟶ X) :
    IsPullback (subschemeComapMap S f) (S.comap f).subschemeι S.subschemeι f := by
  refine (IsPullback.of_iso_pullback (fst := (S.comap f).subschemeι)
    (snd := subschemeComapMap S f) ⟨?_⟩ (S.comapIso f) ?_ ?_).flip
  · simp [subschemeComapMap, pullback.condition]
  · simp
  · simp [subschemeComapMap]

private theorem orderedDivisor_comap_comap {X Y W : Scheme.{u}} (E : OrderedDivisor X)
    (f : Y ⟶ X) (g : W ⟶ Y) : (E.comap f).comap g = E.comap (g ≫ f) := by
  unfold OrderedDivisor.comap
  simp only [← Scheme.IdealSheafData.comap_comp]

private theorem orderedDivisor_deleteIndex_comap {X Y : Scheme.{u}} (E : OrderedDivisor X)
    (f : Y ⟶ X) (j : ℕ) : (E.comap f).deleteIndex j = (E.deleteIndex j).comap f := rfl

private theorem markedTriple_ext {k : Type u} [Field k] {X : Scheme.{u}} {I₁ I₂ : X.IdealSheafData}
    {E₁ E₂ : OrderedDivisor X} {s₁ s₂ : X ⟶ Spec (.of k)} {m : ℕ} (hI : I₁ = I₂) (hE : E₁ = E₂)
    (hs : s₁ = s₂) :
    (⟨⟨⟨X, I₁, E₁⟩, k, s₁⟩, m⟩ : MarkedTriple.{u}) = ⟨⟨⟨X, I₂, E₂⟩, k, s₂⟩, m⟩ := by
  subst hI hE hs; rfl

private theorem isEmpty_subscheme_of_support_eq_empty {X : Scheme.{u}} (S : X.IdealSheafData)
    (h : ¬ (S.support : Set X).Nonempty) : IsEmpty S.subscheme := by
  refine ⟨fun x => h ⟨S.subschemeι x, ?_⟩⟩
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Set.mem_range_self x

private theorem support_comap_nonempty {X' X : Scheme.{u}} (S : X.IdealSheafData) (f : X' ⟶ X)
    (h : ((S.comap f).support : Set X').Nonempty) : (S.support : Set X).Nonempty := by
  obtain ⟨x, hx⟩ := h
  rw [Scheme.IdealSheafData.support_comap] at hx
  exact ⟨f x, hx⟩

section Centre

/-- Under a flat morphism, the closure of the image of the generic point of an irreducible
component of `h⁻¹T` is an irreducible component of `T`. -/
private theorem closure_image_genericPoint_mem_componentsOf {X Y : Scheme.{u}} (h : Y ⟶ X)
    [Flat h] {T : Set X} (hT : IsClosed T) {C' : Set Y} (hC' : C' ∈ componentsOf (h ⁻¹' T)) :
    closure {h hC'.1.1.genericPoint} ∈ componentsOf T := by
  have hirr := hC'.1.1
  have hTY : IsClosed (h ⁻¹' T) := hT.preimage h.continuous
  have hCclosed : IsClosed C' := Aux.isClosed_of_mem_componentsOf hTY hC'
  have hgen : IsGenericPoint hirr.genericPoint C' := by
    simpa [hCclosed.closure_eq] using hirr.isGenericPoint_genericPoint_closure
  have hηC : hirr.genericPoint ∈ C' := hgen.mem
  refine ⟨⟨isIrreducible_singleton.closure, closure_minimal
    (Set.singleton_subset_iff.2 (hC'.1.2 hηC)) hT⟩, ?_⟩
  rintro W' ⟨hW'irr, hW'T⟩ hle
  have hσ := hW'irr.isGenericPoint_genericPoint_closure
  have hξσ : hW'irr.genericPoint ⤳ h hirr.genericPoint := by
    rw [specializes_iff_mem_closure, hσ.def]
    exact subset_closure (hle (subset_closure (Set.mem_singleton _)))
  obtain ⟨η'', hη''spec, hη''eq⟩ := Flat.generalizingMap h hξσ
  have hσT : hW'irr.genericPoint ∈ T := closure_minimal hW'T hT hσ.mem
  have hη''T : η'' ∈ h ⁻¹' T := by
    show h η'' ∈ T
    rw [hη''eq]; exact hσT
  have hsub : C' ⊆ closure {η''} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hη''spec))
      isClosed_closure
  have h2 := hC'.2 ⟨isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.2 hη''T) hTY⟩ hsub
  have hη''C : η'' ∈ C' := h2 (subset_closure (Set.mem_singleton _))
  have hs : hirr.genericPoint ⤳ η'' := by
    rw [specializes_iff_mem_closure, hgen.def]; exact hη''C
  have hs2 : h hirr.genericPoint ⤳ h η'' := hs.map h.continuous
  have hσmem : hW'irr.genericPoint ∈ closure {h hirr.genericPoint} := by
    rw [← hη''eq]; exact specializes_iff_mem_closure.1 hs2
  calc W' ⊆ closure W' := subset_closure
    _ = closure {hW'irr.genericPoint} := hσ.def.symm
    _ ⊆ closure {h hirr.genericPoint} :=
      closure_minimal (Set.singleton_subset_iff.2 hσmem) isClosed_closure

/-- Membership in the support of `Z_{-1}(K, D)`: the point lies on an irreducible component of
`D` contained in `cosupp K`. -/
private theorem mem_support_divisorComponentCentre {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] (K : MarkedIdeal X)
    (D : X.IdealSheafData) (x : X) :
    x ∈ ((divisorComponentCentre K D).support : Set X) ↔
      ∃ C ∈ componentsOf (D.support : Set X), C ⊆ K.cosupport ∧ x ∈ C := by
  set S : Set (Set X) := {W | W ∈ componentsOf (D.support : Set X) ∧ W ⊆ K.cosupport} with hSdef
  have hS : S ⊆ componentsOf (D.support : Set X) := fun W hW => hW.1
  have hU := isClosed_sUnion_of_subset_componentsOf sX D S hS
  have hsupC : (divisorComponentCentre K D).support = Closeds.closure (⋃₀ S) := by
    ext x; simp [divisorComponentCentre, hSdef]
  have hT : ((Closeds.closure (⋃₀ S) : Closeds X) : Set X) = ⋃₀ S := by
    simp [hU.closure_eq]
  rw [hsupC, hT]
  simp only [hSdef, Set.mem_sUnion, Set.mem_setOf_eq, and_assoc]

/-- Orders at the points of `Y` are those of the image, for the pull-back of the marked ideal;
then `Z_{-1}` of the pull-back has support `h⁻¹` of that of `Z_{-1}`. -/
private theorem mem_support_divisorComponentCentre_comap_gen {k K : Type u} [Field k] [CharZero k]
    [Field K] [CharZero K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] (sY : Y ⟶ Spec (.of K)) [Smooth sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] (h : Y ⟶ X) [Flat h]
    (Km : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hmult : ∀ y, multAt (Km.I.comap h) y = multAt Km.I (h y)) (y : Y) :
    y ∈ ((divisorComponentCentre (⟨Km.I.comap h, Km.m⟩ : MarkedIdeal Y) (D.comap h)).support :
        Set Y) ↔ h y ∈ ((divisorComponentCentre Km D).support : Set X) := by
  rw [mem_support_divisorComponentCentre sY, mem_support_divisorComponentCentre sX]
  have hTc : IsClosed (D.support : Set X) := D.support.isClosed
  have hsupp : ((D.comap h).support : Set Y) = h ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcosY : ∀ z : Y, z ∈ (⟨Km.I.comap h, Km.m⟩ : MarkedIdeal Y).cosupport ↔
      h z ∈ Km.cosupport := fun z => by
    change (Km.m : ℕ∞) ≤ multAt (Km.I.comap h) z ↔ (Km.m : ℕ∞) ≤ multAt Km.I (h z)
    rw [hmult]
  have hclK : IsClosed Km.cosupport := isClosed_setOf_le_multAt sX Km.I Km.m
  have hclKY : IsClosed (⟨Km.I.comap h, Km.m⟩ : MarkedIdeal Y).cosupport :=
    isClosed_setOf_le_multAt sY _ _
  simp only [hsupp]
  have hTY : IsClosed (h ⁻¹' (D.support : Set X)) := hTc.preimage h.continuous
  constructor
  · rintro ⟨C', hC', hsub, hyC'⟩
    have hgenC := closure_image_genericPoint_mem_componentsOf h hTc hC'
    have hirr := hC'.1.1
    have hCclosed : IsClosed C' := Aux.isClosed_of_mem_componentsOf hTY hC'
    have hgen : IsGenericPoint hirr.genericPoint C' := by
      simpa [hCclosed.closure_eq] using hirr.isGenericPoint_genericPoint_closure
    have hηC : hirr.genericPoint ∈ C' := hgen.mem
    refine ⟨_, hgenC, closure_minimal (Set.singleton_subset_iff.2
      ((hcosY _).1 (hsub hηC))) hclK, ?_⟩
    have : hirr.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hgen.def]; exact hyC'
    exact (this.map h.continuous).mem_closure
  · rintro ⟨C, hC, hsub, hyC⟩
    have hyT : y ∈ h ⁻¹' (D.support : Set X) := hC.1.2 hyC
    haveI : NoetherianSpace Y := noetherianSpace_of_finiteType sY
    obtain ⟨C', hC', hyC'⟩ := (finite_and_cover_componentsOf hTY).2 hyT
    have hgenC := closure_image_genericPoint_mem_componentsOf h hTc hC'
    have hirr := hC'.1.1
    have hCclosed : IsClosed C' := Aux.isClosed_of_mem_componentsOf hTY hC'
    have hgen : IsGenericPoint hirr.genericPoint C' := by
      simpa [hCclosed.closure_eq] using hirr.isGenericPoint_genericPoint_closure
    have hηC : hirr.genericPoint ∈ C' := hgen.mem
    have hyc : h y ∈ closure {h hirr.genericPoint} := by
      have : hirr.genericPoint ⤳ y := by
        rw [specializes_iff_mem_closure, hgen.def]; exact hyC'
      exact (this.map h.continuous).mem_closure
    have hCeq := eq_of_mem_componentsOf_of_isSmoothScheme sX D hD hC hgenC hyC hyc
    have hξ : h hirr.genericPoint ∈ Km.cosupport :=
      hsub (hCeq ▸ subset_closure (Set.mem_singleton _))
    refine ⟨C', hC', ?_, hyC'⟩
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 ((hcosY _).2 hξ)) hclKY

/-- `π^*W ⊆ (π^*I_Z)^μ` for the centre `Z_{-1}`: the order of `W` along `Z_{-1}` is `≥ μ`. -/
private theorem comap_le_comap_pow_divisorComponentCentre {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (hX : MMP.Mori.IsSmoothScheme sX) (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX)) (hD' : MMP.Mori.IsPureCodimOne D.support) :
    K.I.comap (blowUpToBase (divisorComponentCentre K D)) ≤
      (divisorComponentCentre K D).comap (blowUpToBase (divisorComponentCentre K D)) ^ K.m := by
  refine comap_le_comap_pow_of_stalk_le _ _ _ _ fun x => ?_
  refine stalk_le_pow_of_orderAlongGE sX hX _ (divisorComponentCentre_spec sX K D hD hD').1
    K.I K.m ?_ x
  intro W hW
  have hcl : IsClosed W := Aux.isClosed_of_mem_componentsOf
    (divisorComponentCentre K D).support.isClosed hW
  have hgen : IsGenericPoint hW.1.1.genericPoint W := by
    simpa [hcl.closure_eq] using hW.1.1.isGenericPoint_genericPoint_closure
  have hmem : hW.1.1.genericPoint ∈ ((divisorComponentCentre K D).support : Set X) :=
    hW.1.2 hgen.mem
  obtain ⟨C, -, hsub, hxC⟩ := (mem_support_divisorComponentCentre sX K D _).1 hmem
  exact hsub hxC

end Centre

section CentreFC

/-- `Z_{-1}` commutes with the change of the ground field. -/
private theorem divisorComponentCentre_comap_fc {k L : Type u} [Field k] [CharZero k] [Field L]
    (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    [LocallyOfFiniteType sX] [QuasiCompact sX] (K : MarkedIdeal X) (D : X.IdealSheafData)
    (hD : MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
    (hmult : ∀ y, multAt (K.I.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) y =
      multAt K.I (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)) y)) :
    divisorComponentCentre
        (⟨K.I.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))), K.m⟩ :
          MarkedIdeal (Limits.pullback sX (Spec.map (CommRingCat.ofHom σ))))
        (D.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) =
      (divisorComponentCentre K D).comap
        (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  haveI : CharZero L := charZero_of_injective_ringHom σ.injective
  haveI : PerfectField k := PerfectField.ofCharZero
  have hp := IsReducedFlatBaseChange.fieldChange sX σ
  haveI : Flat (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := hp.flat
  have sqb := IsPullback.of_hasPullback sX (Spec.map (CommRingCat.ofHom σ))
  haveI : Smooth (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ))) :=
    MorphismProperty.of_isPullback (P := @Smooth) sqb inferInstance
  haveI : LocallyOfFiniteType (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ))) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqb inferInstance
  haveI : QuasiCompact (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ))) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sqb inferInstance
  set p := Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)) with hpdef
  refine (hp.comap_vanishingIdeal _ _ ?_).symm
  ext y
  have := mem_support_divisorComponentCentre_comap_gen sX
    (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ))) p K D hD hmult y
  change y ∈ ((divisorComponentCentre (⟨K.I.comap p, K.m⟩ : MarkedIdeal _) (D.comap p)).support :
      Set _) ↔ p y ∈ ((divisorComponentCentre K D).support : Set X) at this
  simpa [divisorComponentCentre, Scheme.IdealSheafData.coe_support_vanishingIdeal] using this

end CentreFC

section FieldChangeTS

/-- The flatness of `Spec L → Spec k`. -/
private theorem flat_specMap_fc {k L : Type u} [Field k] [Field L] (σ : k →+* L) :
    Flat (Spec.map (CommRingCat.ofHom σ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  letI : Algebra k L := σ.toAlgebra
  exact (inferInstance : Module.Flat k L)

private theorem flat_fieldChangeProj_gen {k L : Type u} [Field k] [Field L] (σ : k →+* L)
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) :
    Flat (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  haveI := flat_specMap_fc σ
  exact MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback sX _).flip
    inferInstance

private theorem flat_fieldChangeProj (t : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    (σ : t.k →+* L) : Flat (t.fieldChangeProj σ) :=
  flat_fieldChangeProj_gen σ t.sX

/-- The rectangle exhibiting `S_L = S ×_k L`. -/
private theorem isPullback_bdTS_fieldChange {k L : Type u} [Field k] [Field L] (σ : k →+* L)
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (Z : X.IdealSheafData)
    (S : (blowUp Z).IdealSheafData)
    [Flat (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))] :
    IsPullback (subschemeComapMap S (canonicalLift (pullback.fst sX (Spec.map (CommRingCat.ofHom
        σ))) Z))
      ((S.comap (canonicalLift (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) Z)).subschemeι ≫
        blowUpToBase (Z.comap (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) ≫
          pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
      (S.subschemeι ≫ blowUpToBase Z ≫ sX) (Spec.map (CommRingCat.ofHom σ)) := by
  have sq := isPullback_subschemeComapMap S
    (canonicalLift (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) Z)
  have α := Kollar.isPullback_canonicalLift_of_flat (pullback.fst sX (Spec.map (CommRingCat.ofHom
      σ))) Z
  have sqb := IsPullback.of_hasPullback sX (Spec.map (CommRingCat.ofHom σ))
  have := (sq.flip.paste_horiz α).paste_horiz sqb.flip
  simpa using this.flip

end FieldChangeTS

section FieldChangeTS2

/-- The marked triple fed to `𝓜` on `X_L` is the pull-back, along the isomorphism
`S_L ≅ S ×_k L`, of the field change of the one on `X`. -/
private theorem bdTS_fieldChange (m j : ℕ) (t : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    (σ : t.k →+* L) [Flat (t.fieldChangeProj σ)] (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData)
    (S : (blowUp Z).IdealSheafData)
    (hbt : ((⟨W.I.comap (t.fieldChangeProj σ), W.m⟩ : MarkedIdeal (t.fieldChangeScheme
        σ)).birationalTransform
        (Z.comap (t.fieldChangeProj σ))).I =
      (W.birationalTransform Z).I.comap (canonicalLift (t.fieldChangeProj σ) Z)) :
    bdTS m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
        (Z.comap (t.fieldChangeProj σ)) (S.comap (canonicalLift (t.fieldChangeProj σ) Z)) =
      ((bdTS m j t W Z S).fieldChange σ).pullback
        (isPullback_bdTS_fieldChange σ t.sX Z S).isoPullback.hom := by
  have hrect := isPullback_bdTS_fieldChange σ t.sX Z S
  have ef : hrect.isoPullback.hom ≫
      FieldBlowupTriple.fieldChangeProj (bdTS m j t W Z S).toFieldBlowupTriple σ =
      subschemeComapMap S (canonicalLift (t.fieldChangeProj σ) Z) := hrect.isoPullback_hom_fst
  have es : hrect.isoPullback.hom ≫ (((bdTS m j t W Z S).fieldChange σ).sX) =
      (S.comap (canonicalLift (t.fieldChangeProj σ) Z)).subschemeι ≫
        blowUpToBase (Z.comap (t.fieldChangeProj σ)) ≫ (t.fieldChange σ).sX :=
    hrect.isoPullback_hom_snd
  have w1 := (isPullback_subschemeComapMap S (canonicalLift (t.fieldChangeProj σ) Z)).w
  have w2 := canonicalLift_comp_blowUpToBase (t.fieldChangeProj σ) Z
  have eq1 : (S.comap (canonicalLift (t.fieldChangeProj σ) Z)).subschemeι ≫
      canonicalLift (t.fieldChangeProj σ) Z = hrect.isoPullback.hom ≫
        (FieldBlowupTriple.fieldChangeProj (bdTS m j t W Z S).toFieldBlowupTriple σ ≫
          S.subschemeι) := by
    refine w1.symm.trans ?_
    exact (congrArg (· ≫ S.subschemeι) ef.symm).trans (Category.assoc _ _ _)
  have eq2 : (S.comap (canonicalLift (t.fieldChangeProj σ) Z)).subschemeι ≫
      blowUpToBase (Z.comap (t.fieldChangeProj σ)) ≫ t.fieldChangeProj σ =
      hrect.isoPullback.hom ≫
        (FieldBlowupTriple.fieldChangeProj (bdTS m j t W Z S).toFieldBlowupTriple σ ≫
          (S.subschemeι ≫ blowUpToBase Z)) := by
    rw [← w2, ← Category.assoc, eq1]
    exact (Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))
  unfold bdTS MarkedTriple.pullback FieldBlowupTriple.pullback MarkedTriple.fieldChange
    FieldBlowupTriple.fieldChange
  refine markedTriple_ext ?_ ?_ ?_
  · change ((⟨W.I.comap (t.fieldChangeProj σ), W.m⟩ : MarkedIdeal (t.fieldChangeScheme
      σ)).birationalTransform
        (Z.comap (t.fieldChangeProj σ))).I.comap _ = _
    rw [hbt]
    dsimp only
    simp only [← Scheme.IdealSheafData.comap_comp]
    exact congrArg (fun f => (MarkedIdeal.birationalTransform Z W).I.comap f) eq1
  · dsimp only
    simp only [orderedDivisor_comap_comap, orderedDivisor_deleteIndex_comap]
    exact congrArg (fun f => (t.E.deleteIndex j).comap f) eq2
  · exact es.symm

end FieldChangeTS2

section FieldChangeBody

/-- The key comparison of the two branches of `𝓑𝓓` for a change of fields. -/
private theorem bdBody_fieldChange {N m j : ℕ} (M : MarkedFamily.{u})
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (nX nY : ℕ)
    (t : FieldBlowupTriple.{u}) {L : Type u} [Field L] (σ : t.k →+* L)
    (W : MarkedIdeal t.X) (Z : t.X.IdealSheafData) (S : (blowUp Z).IdealSheafData)
    (hbt : ((⟨W.I.comap (t.fieldChangeProj σ), W.m⟩ :
        MarkedIdeal (t.fieldChangeScheme σ)).birationalTransform
          (Z.comap (t.fieldChangeProj σ))).I =
      (W.birationalTransform Z).I.comap (canonicalLift (t.fieldChangeProj σ) Z))
    (hX : (S.support : Set (blowUp Z)).Nonempty → bdTS m j t W Z S ∈ markedTriples ∧
      HasDimensionIn S.subscheme {nX - 1} ∧ nX - 1 ≤ N - 1)
    (hY : ((S.comap (canonicalLift (t.fieldChangeProj σ) Z)).support :
        Set (blowUp (Z.comap (t.fieldChangeProj σ)))).Nonempty →
      bdTS m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
        (Z.comap (t.fieldChangeProj σ)) (S.comap (canonicalLift (t.fieldChangeProj σ) Z)) ∈
          markedTriples ∧
        HasDimensionIn (S.comap (canonicalLift (t.fieldChangeProj σ) Z)).subscheme {nY - 1} ∧
        nY - 1 ≤ N - 1) :
    bdBody M nY m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
        (Z.comap (t.fieldChangeProj σ)) (S.comap (canonicalLift (t.fieldChangeProj σ) Z)) =
      ((bdBody M nX m j t W Z S).pullback (t.fieldChangeProj σ)).reduction := by
  classical
  haveI := flat_fieldChangeProj t σ
  haveI : Flat (canonicalLift (t.fieldChangeProj σ) Z) :=
    Kollar.flat_canonicalLift (t.fieldChangeProj σ) Z
  set ĥ := canonicalLift (t.fieldChangeProj σ) Z with hĥ
  have sq := isPullback_subschemeComapMap S ĥ
  haveI : Flat (subschemeComapMap S ĥ) :=
    MorphismProperty.of_isPullback (P := @Flat) sq.flip inferInstance
  have hrect := isPullback_bdTS_fieldChange σ t.sX Z S
  have hTS := bdTS_fieldChange m j t σ W Z S hbt
  have ef : hrect.isoPullback.hom ≫
      FieldBlowupTriple.fieldChangeProj (bdTS m j t W Z S).toFieldBlowupTriple σ =
      subschemeComapMap S ĥ := hrect.isoPullback_hom_fst
  have C1 : bdBS M nY m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
      (Z.comap (t.fieldChangeProj σ)) (S.comap ĥ) =
      (bdBS M nX m j t W Z S).pullbackReduced (subschemeComapMap S ĥ) := by
    by_cases hSY : ((S.comap ĥ).support : Set (blowUp (Z.comap (t.fieldChangeProj σ)))).Nonempty
    · have hS := support_comap_nonempty S ĥ hSY
      obtain ⟨hXm, hXd, hXN⟩ := hX hS
      have hBS : bdBS M nX m j t W Z S = M (nX - 1) m.factorial (bdTS m j t W Z S) := by
        unfold bdBS; exact if_pos ⟨hS, hXm⟩
      obtain ⟨hYm, hYd, hYN⟩ := hY hSY
      have hBSY : bdBS M nY m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
          (Z.comap (t.fieldChangeProj σ)) (S.comap ĥ) =
          M (nY - 1) m.factorial (bdTS m j (t.fieldChange σ)
            ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩ (Z.comap (t.fieldChangeProj σ))
            (S.comap ĥ)) := by
        unfold bdBS; exact if_pos ⟨hSY, hYm⟩
      have hμ : 1 ≤ m.factorial := Nat.succ_le_of_lt (Nat.factorial_pos m)
      obtain ⟨F, hF, hFc⟩ := hM m.factorial hμ
      have hdimIcc : ∀ (n : ℕ) (X' : Scheme.{u}), HasDimensionIn X' {n - 1} → n - 1 ≤ N - 1 →
          HasDimensionIn X' (Set.Icc 0 (N - 1)) := by
        rintro n X' ⟨d, hd, hdd⟩ hn
        rw [Set.mem_singleton_iff] at hd
        subst hd
        exact ⟨n - 1, ⟨Nat.zero_le _, hn⟩, hdd⟩
      set T := bdTS m j t W Z S with hTdef
      set T' := bdTS m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
        (Z.comap (t.fieldChangeProj σ)) (S.comap ĥ) with hT'def
      set e := hrect.isoPullback with hedef
      have hmtX : T ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial :=
        ⟨hXm, rfl, hdimIcc nX _ hXd hXN⟩
      have hmtY : T' ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial :=
        ⟨hYm, rfl, hdimIcc nY _ hYd hYN⟩
      have hTfc : T.fieldChange σ ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial := by
        refine ⟨?_, rfl, ?_⟩
        · exact mem_triples_iff.2 ⟨fieldChange_mem_sncTriples
            (mem_sncTriples_of_mem_triples hXm) σ,
            Equidimensional.of_homeomorph e.inv.homeomorph (mem_triples_iff.1 hYm).2⟩
        · obtain ⟨d, hd, hdd⟩ := hmtY.2.2
          refine ⟨d, hd, ?_⟩
          have h2 : topologicalKrullDim (T.fieldChange σ).X =
              topologicalKrullDim (S.comap ĥ).subscheme :=
            IsHomeomorph.topologicalKrullDim_eq e.inv e.inv.homeomorph.isHomeomorph
          exact h2.trans hdd
      have hmtY' : (T.fieldChange σ).pullback e.hom ∈
          markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial := hTS ▸ hmtY
      obtain ⟨-, -, hlft, hqc, -⟩ := hmtY'.1
      haveI : IsIso (show (S.comap ĥ).subscheme ⟶ (T.fieldChange σ).X from e.hom) :=
        Iso.isIso_hom e
      have hsm : Smooth (show (S.comap ĥ).subscheme ⟶ (T.fieldChange σ).X from e.hom) :=
        inferInstance
      have hsurj : Surjective (show (S.comap ĥ).subscheme ⟶ (T.fieldChange σ).X from e.hom) :=
        inferInstance
      have key1 := hFc.2.1.1 (T.fieldChange σ) hTfc (S.comap ĥ).subscheme e.hom hsm hsurj
        hlft hqc hmtY'
      have key2 := hFc.2.2 T hmtX L σ hTfc
      rw [key2] at key1
      have key3 : F.toFun ((T.fieldChange σ).pullback e.hom) hmtY' =
          (F.toFun T hmtX).pullback (subschemeComapMap S ĥ) := by
        refine key1.trans (eq_of_heq ?_)
        refine ClosedBlowupSequence.pullback_pullback_heq _ _ e.hom (subschemeComapMap S ĥ) rfl ?_
        rw [eqToHom_refl, Category.id_comp]
        exact ef.symm
      have step : ∀ (A B : MarkedTriple.{u}) (hAB : A = B)
          (hA : A ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial)
          (hB : B ∈ markedTriplesOfDim (Set.Icc 0 (N - 1)) m.factorial),
          HEq (F.toFun A hA) (F.toFun B hB) := by
        intro A B hAB hA hB; subst hAB; exact HEq.rfl
      have key4 : F.toFun T' hmtY = (F.toFun T hmtX).pullback (subschemeComapMap S ĥ) :=
        (eq_of_heq (step T' _ hTS hmtY hmtY')).trans key3
      obtain ⟨dX, hdX, hdXe⟩ := hXd
      obtain ⟨dY, hdY, hdYe⟩ := hYd
      rw [Set.mem_singleton_iff] at hdX hdY
      have hnX : dimNat S.subscheme = nX - 1 := by rw [← hdX]; simp [dimNat, hdXe]
      have hnY : dimNat (S.comap ĥ).subscheme = nY - 1 := by rw [← hdY]; simp [dimNat, hdYe]
      have hFT : F.toFun T hmtX = M (nX - 1) m.factorial T := by
        rw [hF T hmtX]
        exact congrArg (fun n => M n m.factorial T) hnX
      have hFT' : F.toFun T' hmtY = M (nY - 1) m.factorial T' := by
        rw [hF T' hmtY]
        exact congrArg (fun n => M n m.factorial T') hnY
      rw [hBS, hBSY, ← hFT, ← hFT']
      have hne : ((F.toFun T hmtX).pullback (subschemeComapMap S ĥ)).HasNoEmptyBlowups :=
        key4 ▸ F.hasNoEmptyBlowups T' hmtY
      exact key4.trans ((reduction_eq_self hne).symm.trans (reduction_pullback _ _))
    · have hBSY : bdBS M nY m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
          (Z.comap (t.fieldChangeProj σ)) (S.comap ĥ) = .nil _ := by
        unfold bdBS; exact if_neg (fun hh => hSY hh.1)
      have : IsEmpty (S.comap ĥ).subscheme :=
        isEmpty_subscheme_of_support_eq_empty (S.comap ĥ) hSY
      rw [hBSY]
      exact (@pullbackReduced_eq_nil_of_isEmpty _ _ this _ _).symm
  have e1 := pushforward_pullbackReduced S.subschemeι ĥ (subschemeComapMap S ĥ)
    (S.comap ĥ).subschemeι sq (bdBS M nX m j t W Z S)
  have e2 : bdBody M nY m j (t.fieldChange σ) ⟨W.I.comap (t.fieldChangeProj σ), W.m⟩
      (Z.comap (t.fieldChangeProj σ)) (S.comap ĥ) =
      (ClosedBlowupSequence.cons (Z.comap (t.fieldChangeProj σ))
        (((bdBS M nX m j t W Z S).pushforward S.subschemeι).pullbackReduced ĥ)).reduction := by
    unfold bdBody
    exact congrArg (fun B => (ClosedBlowupSequence.cons (Z.comap (t.fieldChangeProj σ))
        B).reduction)
      ((congrArg (fun B => B.pushforward (S.comap ĥ).subschemeι) C1).trans e1)
  refine e2.trans ?_
  rw [reduction_cons_pullbackReduced]
  exact (reduction_pullback_reduction _ (t.fieldChangeProj σ)).symm

end FieldChangeBody

/-- The input of `𝓜` in `𝓑𝓓`: marked triple of dimension `n - 1` when `S ≠ ∅`. -/
private theorem bd_input_facts {m j n : ℕ} (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (hj : j < t.E.s) (hn : 1 ≤ n)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞))
    (W : MarkedIdeal t.X)
    (hW : W = ⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩)
    (Z : t.X.IdealSheafData) (hZ : Z = divisorComponentCentre W (t.E.E ⟨j, hj⟩))
    (S : (blowUp Z).IdealSheafData) (hS : S = (t.E.E ⟨j, hj⟩).comap (blowUpToBase Z)) :
    (S.support : Set (blowUp Z)).Nonempty →
      bdTS m j t W Z S ∈ markedTriples ∧ HasDimensionIn S.subscheme {n - 1} := by
  subst hW hZ hS
  intro hne
  have h2 := bdFunctor_input_mem_markedTriplesOfDim (m := m) (n := n) (j := j) t ht hm hmax hj hn
      hdim hne
  exact ⟨mem_markedTriples_of_deleteEmpty _ h2.1, h2.2.2⟩

private theorem bdBody_congr (M : MarkedFamily.{u}) (n m j : ℕ) (tY : FieldBlowupTriple.{u})
    (W₁ W₂ : MarkedIdeal tY.X) (hW : W₁ = W₂) (Z₁ Z₂ : tY.X.IdealSheafData) (hZ : Z₁ = Z₂)
    (S₁ : (blowUp Z₁).IdealSheafData) (S₂ : (blowUp Z₂).IdealSheafData) (hS : HEq S₁ S₂) :
    bdBody M n m j tY W₁ Z₁ S₁ = bdBody M n m j tY W₂ Z₂ S₂ := by
  subst hW hZ
  obtain rfl := eq_of_heq hS
  rfl

private theorem heq_comap_blowUpToBase {X : Scheme.{u}} (D : X.IdealSheafData)
    {Z₁ Z₂ : X.IdealSheafData} (hZ : Z₁ = Z₂) :
    HEq (D.comap (blowUpToBase Z₁)) (D.comap (blowUpToBase Z₂)) := by
  subst hZ; rfl

section CoeffFC

/-- The higher derivative ideals commute with the pull-back along `X_L ⟶ X`. -/
private theorem higherDerivativeIdeal_comap_pullback_fst' {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (I : X.IdealSheafData) (r : ℕ) :
    higherDerivativeIdeal (pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
        (I.comap (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) r =
      (higherDerivativeIdeal sX I r).comap
        (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  letI := σ.toAlgebra
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih]
    exact (derivativeIdeal_comap_pullback_fst (L := L) sX).2 _

/-- The order is invariant under the change of the ground field. -/
private theorem multAt_comap_fc {k L : Type u} [Field k] [CharZero k] [Field L] (σ : k →+* L)
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (I : X.IdealSheafData)
    (y : (pullback sX (Spec.map (CommRingCat.ofHom σ)) : Scheme.{u})) :
    multAt (I.comap (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) y =
      multAt I (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)) y) := by
  haveI : CharZero L := charZero_of_injective_ringHom σ.injective
  have sqb := IsPullback.of_hasPullback sX (Spec.map (CommRingCat.ofHom σ))
  haveI : Smooth (pullback.snd sX (Spec.map (CommRingCat.ofHom σ))) :=
    MorphismProperty.of_isPullback (P := @Smooth) sqb inferInstance
  haveI := flat_fieldChangeProj_gen σ sX
  obtain ⟨hXn, hX⟩ := regular_stalks_of_smooth sX
  obtain ⟨hYn, hY⟩ := regular_stalks_of_smooth
    (pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
  exact MMP.Flips.ResolutionInputs.multAt_comap_eq (pullback.fst sX (Spec.map (CommRingCat.ofHom
      σ)))
    hX hY (fun y => isRegularLocalRing_closedFibre_of_isRegular_fiber _ y
      (isRegular_fiber_pullback_fst sX σ _)) I y

/-- The maximal order is invariant under the change of the ground field, since the projection
`X_L ⟶ X` preserves orders pointwise and is surjective. -/
private theorem maxOrder_comap_fc {k L : Type u} [Field k] [CharZero k] [Field L] (σ : k →+* L)
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (I : X.IdealSheafData) :
    maxOrder (I.comap (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) = maxOrder I := by
  simp only [maxOrder, maxOrderAlong, Set.mem_univ, iSup_pos, multAt_comap_fc σ sX I]
  exact (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))).surjective.iSup_comp (multAt I)

/-- `W_s(p^*I) = p^*W_s(I)` for the projection `p : X_L ⟶ X`. -/
private theorem maximalCoefficientIdeal_comap_fc {k L : Type u} [Field k] [CharZero k] [Field L]
    (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (I : X.IdealSheafData) (s : ℤ) :
    maximalCoefficientIdeal (pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
        (I.comap (pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) s =
      (maximalCoefficientIdeal sX I s).comap
        (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  rw [maximalCoefficientIdeal, maximalCoefficientIdeal, maxOrder_comap_fc σ sX I]
  simp only [(Scheme.IdealSheafData.map_gc _).l_iSup, Stacks.IdealSheaf.comap_finset_prod,
    Stacks.IdealSheaf.comap_pow, higherDerivativeIdeal_comap_pullback_fst' σ sX I]

end CoeffFC

/-- The maximal order of a triple's ideal is invariant under change of the ground field. -/
private theorem maxOrder_fieldChange (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    maxOrder (t.fieldChange σ).I = maxOrder t.I := by
  obtain ⟨hchar, hsm, hlft0, -⟩ := ht
  haveI : LocallyOfFiniteType t.sX := hlft0
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr hlft0
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  exact maxOrder_comap_fc σ t.sX t.I

/-- The case `maxord I = m`: the comparison through the blow-up of `Z_{-1}` and (2b) of the
marked family. -/
private theorem bdFunctor_fieldChange_of_maxOrder_eq {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    (t : FieldBlowupTriple.{u})
    (ht : t ∈ {t : FieldBlowupTriple.{u} | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s})
    (L : Type u) [Field L] (σ : t.k →+* L)
    (hL : t.fieldChange σ ∈
      {t : FieldBlowupTriple.{u} | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s})
    (hmax : maxOrder t.I = m) :
    bdFunctor M (dimNat (t.fieldChange σ).X) m j (t.fieldChange σ) =
      (bdFunctor M (dimNat t.X) m j t).pullback (t.fieldChangeProj σ) := by
  classical
  have htr : t ∈ triples := ht.1.1
  obtain ⟨hchar, hsm, hlft0, hqc0, he, hnz, hOD, hSNC⟩ := id htr
  haveI : CharZero t.k := hchar
  haveI : LocallyOfFiniteType t.sX := hlft0
  haveI : QuasiCompact t.sX := hqc0
  haveI : LocallyOfFinitePresentation t.sX :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := t.sX)).mpr hlft0
  haveI : Smooth t.sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : CharZero L := charZero_of_injective_ringHom σ.injective
  haveI := flat_fieldChangeProj t σ
  haveI : Surjective (t.fieldChangeProj σ) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback t.sX _).flip
      inferInstance
  have hYm : maxOrder (t.fieldChange σ).I = m := (maxOrder_fieldChange t htr σ).trans hmax
  obtain ⟨nX, hnX, hdX⟩ := ht.1.2.1
  obtain ⟨nY, hnY, hdY⟩ := hL.1.2.1
  have hdimX : dimNat t.X = nX := by simp [dimNat, hdX]
  have hdimY : dimNat (t.fieldChange σ).X = nY := by
    have : topologicalKrullDim (t.fieldChange σ).X = ((nY : ℕ∞) : WithBot ℕ∞) := hdY
    simp [dimNat, this]
  rw [bdFunctor_eq_bdBody M (dimNat (t.fieldChange σ).X) m j (t.fieldChange σ) ⟨hYm, hL.2⟩,
    bdFunctor_eq_bdBody M (dimNat t.X) m j t ⟨hmax, ht.2⟩, hdimX, hdimY]
  set μ := m.factorial with hμ
  set WX : MarkedIdeal t.X := ⟨maximalCoefficientIdeal t.sX t.I μ, μ⟩ with hWXdef
  set DX := t.E.E ⟨j, ht.2⟩ with hDX
  have hDsm : MMP.Mori.IsSmoothScheme (DX.subschemeι ≫ t.sX) := (hSNC.1 ⟨j, ht.2⟩).2.2
  have hDcod : MMP.Mori.IsPureCodimOne DX.support := (hSNC.1 ⟨j, ht.2⟩).2.1
  have hWY : (⟨maximalCoefficientIdeal (t.fieldChange σ).sX (t.fieldChange σ).I μ, μ⟩ :
      MarkedIdeal (t.fieldChange σ).X) = ⟨WX.I.comap (t.fieldChangeProj σ), WX.m⟩ := by
    congr 1
    exact maximalCoefficientIdeal_comap_fc σ t.sX t.I μ
  have hmult : ∀ y, multAt (WX.I.comap (t.fieldChangeProj σ)) y =
      multAt WX.I (t.fieldChangeProj σ y) := multAt_comap_fc σ t.sX WX.I
  have hZY2 : divisorComponentCentre (⟨WX.I.comap (t.fieldChangeProj σ), WX.m⟩ :
      MarkedIdeal (t.fieldChange σ).X) ((t.fieldChange σ).E.E ⟨j, hL.2⟩) =
      (divisorComponentCentre WX DX).comap (t.fieldChangeProj σ) :=
    divisorComponentCentre_comap_fc σ t.sX WX DX hDsm hmult
  have hZY : divisorComponentCentre (⟨maximalCoefficientIdeal (t.fieldChange σ).sX
      (t.fieldChange σ).I μ, μ⟩ : MarkedIdeal (t.fieldChange σ).X)
      ((t.fieldChange σ).E.E ⟨j, hL.2⟩) =
      (divisorComponentCentre WX DX).comap (t.fieldChangeProj σ) := by
    rw [hWY]; exact hZY2
  set ZX := divisorComponentCentre WX DX with hZXdef
  set SX := DX.comap (blowUpToBase ZX) with hSXdef
  have hbt : ((⟨WX.I.comap (t.fieldChangeProj σ), WX.m⟩ :
      MarkedIdeal (t.fieldChangeScheme σ)).birationalTransform
        (ZX.comap (t.fieldChangeProj σ))).I =
      (WX.birationalTransform ZX).I.comap (canonicalLift (t.fieldChangeProj σ) ZX) :=
    congrArg MarkedIdeal.I (MMP.Resolution.Kollar.birationalTransform_comap_eq_comap_canonicalLift
      (t.fieldChangeProj σ) ZX WX
      (comap_le_comap_pow_divisorComponentCentre t.sX hsm WX DX hDsm hDcod))
  have hSeq : ((t.fieldChange σ).E.E ⟨j, hL.2⟩).comap
      (blowUpToBase (ZX.comap (t.fieldChangeProj σ))) =
      SX.comap (canonicalLift (t.fieldChangeProj σ) ZX) := by
    change (DX.comap (t.fieldChangeProj σ)).comap
      (blowUpToBase (ZX.comap (t.fieldChangeProj σ))) = _
    rw [hSXdef, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      canonicalLift_comp_blowUpToBase]
  have hX' : (SX.support : Set (blowUp ZX)).Nonempty → bdTS m j t WX ZX SX ∈ markedTriples ∧
      HasDimensionIn SX.subscheme {nX - 1} ∧ nX - 1 ≤ N - 1 := by
    intro hne
    obtain ⟨h1, h2⟩ := bd_input_facts t htr hm hmax ht.2 hnX.1 hdX WX rfl ZX rfl SX rfl hne
    exact ⟨h1, h2, by have := hnX.2; omega⟩
  have hY' : ((SX.comap (canonicalLift (t.fieldChangeProj σ) ZX)).support :
      Set (blowUp (ZX.comap (t.fieldChangeProj σ)))).Nonempty →
      bdTS m j (t.fieldChange σ) ⟨WX.I.comap (t.fieldChangeProj σ), WX.m⟩
        (ZX.comap (t.fieldChangeProj σ)) (SX.comap (canonicalLift (t.fieldChangeProj σ) ZX)) ∈
        markedTriples ∧
        HasDimensionIn (SX.comap (canonicalLift (t.fieldChangeProj σ) ZX)).subscheme {nY - 1} ∧
        nY - 1 ≤ N - 1 := by
    intro hne
    obtain ⟨h1, h2⟩ := bd_input_facts (m := m) (j := j) (n := nY) (t.fieldChange σ) hL.1.1 hm hYm
      hL.2 hnY.1 hdY ⟨WX.I.comap (t.fieldChangeProj σ), WX.m⟩ hWY.symm
      (ZX.comap (t.fieldChangeProj σ)) hZY2.symm
      (SX.comap (canonicalLift (t.fieldChangeProj σ) ZX)) hSeq.symm hne
    exact ⟨h1, h2, by have := hnY.2; omega⟩
  have key := bdBody_fieldChange (m := m) (j := j) M hM nX nY t σ WX ZX SX hbt hX' hY'
  have hnb : (bdBody M nX m j t WX ZX SX).HasNoEmptyBlowups :=
    ClosedBlowupSequence.hasNoEmptyBlowups_reduction _
  refine (bdBody_congr M nY m j (t.fieldChange σ) _ _ hWY _ _ hZY _ _ ?_).trans
    (key.trans (ClosedBlowupSequence.reduction_eq_self
      (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _ hnb (t.fieldChangeProj σ))))
  exact (heq_comap_blowUpToBase _ hZY).trans (heq_of_eq hSeq)

end PartIII

end BDFunctor

open BDFunctor in
/-- **Kollár, Lemma 3.102 (2), change of fields.** Let `N ≥ 1`, let `𝓜` be a marked
order-reduction family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `m ≥ 1`
and `j` a (`0`-based) index. On the class of triples `(X, I, E)` with `1 ≤ dim X ≤ N`,
`maxord I ≤ m` and `j < s` (`E = (E^0, …, E^{s-1})`), the functor
`(X, I, E) ↦ bdFunctor M (dim X) m j (X, I, E)` commutes with change of fields
(`CommutesWithFieldChangeOn`). -/
@[mmp "lem_kr3e_bd_commutes_field_change"]
public theorem commutesWithFieldChangeOn_bdFunctor {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m) :
    CommutesWithFieldChangeOn {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s}
      (fun t _ => bdFunctor M (dimNat t.X) m j t) := by
  intro t ht L _ σ hL
  by_cases hmax : maxOrder t.I = m
  · exact bdFunctor_fieldChange_of_maxOrder_eq M hN hM hm t ht L σ hL hmax
  · have hmax' : ¬ (maxOrder (t.fieldChange σ).I = m ∧ j < (t.fieldChange σ).E.s) := by
      rw [maxOrder_fieldChange t ht.1.1]; exact fun h => hmax h.1
    simp only [bdFunctor, dif_neg hmax', dif_neg (fun h : _ ∧ _ => hmax h.1)]
    rfl

end MMP.Resolution
