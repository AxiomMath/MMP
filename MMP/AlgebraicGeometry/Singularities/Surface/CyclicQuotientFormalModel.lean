module

public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.CoordinateBlowupChart
public import MMP.AlgebraicGeometry.Resolution.LinearBlowupCharts
public import MMP.AlgebraicGeometry.Resolution.CyclicQuotient.MarkedChainContraction
public import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
public import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice

/-!
# Formal cyclic-quotient models of germs of types (3) and (9)

Let `(Y, y; C)` be a surface germ over an algebraically closed field `K` of characteristic `0`
whose boundary `C` is reduced. If it is of type (3) of FA Fig. 3 (`MMP.Flips.IsFig3Type3`), the
pair `(Spec 𝒪̂_{Y,y}, C)` is isomorphic over `K` to `(T_{m,q}, C^{(1)}_{m,q})` for some `m ≥ 1`
and `q` prime to `m`; if it is of type (9) (`MMP.Flips.IsFig3Type9`), it is isomorphic to
`(T_{m,q}, C^{(2)}_{m,q})`. Here `T_{m,q} = Spec K[[x, y]]^{μ_m}`
(`MMP.Flips.cyclicQuotientModel`) and `C^{(1)}_{m,q}`, `C^{(2)}_{m,q}` are the reduced images of
`(x = 0)` and `(xy = 0)` (`MMP.Flips.cyclicQuotientCurveOne`,
`MMP.Flips.cyclicQuotientCurveTwo`).

## Main results

* `MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isFig3Type3_or_isFig3Type9`

## Implementation notes

An isomorphism of pairs of affine schemes over `K` is recorded as a ring isomorphism
`φ : K[[x, y]]^{μ_m} ≃+* 𝒪̂_{Y,y}` of the rings of global sections, compatible with the
embeddings of `K` (the constants of `K[[x, y]]` and the composite `K → 𝒪_{Y,y} → 𝒪̂_{Y,y}`),
which carries the ideal of global sections of the ideal sheaf of `C^{(i)}_{m,q}` (that is, of
`MMP.Flips.cyclicQuotientImage` of `x`, resp. `xy`, through `Γ(Spec R, ⊤) ≅ R`) onto the
extension `I_{C,y} 𝒪̂_{Y,y}` of the stalk at `y` of the ideal sheaf of `C`. The ideal sheaf of
the reduced boundary `C = ∑ Cᵢ` is the infimum of the ideal sheaves of its components.

When the minimal resolution has no exceptional curve the germ is smooth, `m = 1`, and the model
comes from coordinates on `K[[x, y]]`, for a node by the formal Morse lemma. Otherwise the
exceptional curve is a negative chain of smooth rational curves, marked at its ends by the
boundary, and the model is that of
`MMP.Flips.exists_ringEquiv_cyclicInvariants_of_isSNCChain_fibre`, read through the theorem on
formal functions.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 16.6.1.2,
  16.6.3, Fig. 3
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace MMP.Flips

open MMP.Mori

/-- The completion `𝒪̂` of a local ring at its maximal ideal. -/
local notation "𝒪̂(" R ")" => AdicCompletion (maximalIdeal R) R

/-! ### The model side -/

private theorem X_dvd_iff_rescale_eq_zero {K : Type v} [Field K] (i : Fin 2)
    (φ : MvPowerSeries (Fin 2) K) :
    MvPowerSeries.X i ∣ φ ↔ MvPowerSeries.rescale (Function.update 1 i 0) φ = 0 := by
  rw [MvPowerSeries.X_dvd_iff]
  constructor
  · intro h
    ext e
    rw [MvPowerSeries.coeff_rescale, map_zero]
    by_cases he : e i = 0
    · rw [h e he, mul_zero]
    · rw [Finsupp.prod, Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.mpr he)
        (by simp [he]), zero_mul]
  · intro h e he
    have := congrArg (MvPowerSeries.coeff e) h
    rw [MvPowerSeries.coeff_rescale, map_zero] at this
    have hp : e.prod (fun j n => (Function.update (1 : Fin 2 → K) i 0) j ^ n) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have : j ≠ i := fun hji => (Finsupp.mem_support_iff.mp hj) (hji ▸ he)
      simp [this]
    rwa [hp, one_mul] at this

private theorem prime_X {K : Type v} [Field K] (i : Fin 2) :
    Prime (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
  refine ⟨fun h => by simpa using congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h,
    fun hu => ?_, fun a b hab => ?_⟩
  · simpa using MvPowerSeries.isUnit_iff_constantCoeff.mp hu
  · simp only [X_dvd_iff_rescale_eq_zero, map_mul] at hab ⊢
    exact mul_eq_zero.mp hab

private theorem radical_span_X {K : Type v} [Field K] (i : Fin 2) :
    (Ideal.span {MvPowerSeries.X i} : Ideal (MvPowerSeries (Fin 2) K)).radical =
      Ideal.span {MvPowerSeries.X i} :=
  ((Ideal.span_singleton_prime (prime_X i).ne_zero).mpr (prime_X i)).radical

private theorem radical_span_X_mul_X {K : Type v} [Field K] :
    (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Ideal (MvPowerSeries (Fin 2) K)).radical =
      Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1} := by
  have h0 := (Ideal.span_singleton_prime (prime_X (K := K) 0).ne_zero).mpr
    (prime_X (K := K) 0)
  have h1 := (Ideal.span_singleton_prime (prime_X (K := K) 1).ne_zero).mpr
    (prime_X (K := K) 1)
  apply le_antisymm
  · rw [← h0.radical, ← h1.radical, ← Ideal.radical_inf]
    refine Ideal.radical_mono (le_inf ?_ ?_) <;>
      rw [Ideal.span_singleton_le_span_singleton]
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro f hf
    refine ⟨2, ?_⟩
    rw [Ideal.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hf
    rw [Ideal.mem_span_singleton, pow_two]
    exact mul_dvd_mul hf.1 hf.2

private theorem span_X_inf_span_X {K : Type v} [Field K] :
    (Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1} :
        Ideal (MvPowerSeries (Fin 2) K)) =
      Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} := by
  refine le_antisymm (fun f hf => ?_) (le_inf ?_ ?_)
  · rw [Ideal.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hf
    obtain ⟨a, rfl⟩ := hf.1
    rw [Ideal.mem_span_singleton]
    refine mul_dvd_mul_left _ (((prime_X 1).dvd_or_dvd hf.2).resolve_left fun h => ?_)
    simpa using MvPowerSeries.X_dvd_iff.mp h (Finsupp.single 0 1) (by simp)
  · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

/-- The global sections of the vanishing ideal of a closed subset `Z` of `Spec R`, read in `R`
through `Γ(Spec R, ⊤) ≅ R`, form the vanishing ideal of `Z`. -/
private theorem comap_ΓSpecIso_vanishingIdeal (R : CommRingCat.{v})
    (Z : TopologicalSpace.Closeds (Spec R)) :
    Ideal.comap (Scheme.ΓSpecIso R).inv.hom
      ((Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨⊤, isAffineOpen_top (Spec R)⟩) =
      PrimeSpectrum.vanishingIdeal (R := R) (Z : Set (Spec R)) := by
  ext x
  refine Iff.trans ?_ (PrimeSpectrum.mem_vanishingIdeal _ _).symm
  rw [Ideal.mem_comap, Scheme.IdealSheafData.vanishingIdeal_ideal,
    PrimeSpectrum.mem_vanishingIdeal]
  simp only [Set.mem_preimage]
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  constructor
  · intro h (p : Spec R) hp
    have hp' : Spec.map (Scheme.ΓSpecIso R).inv (Spec.map (Scheme.ΓSpecIso R).hom p) = p := by
      rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
      rfl
    have hmem : Spec.map (Scheme.ΓSpecIso R).inv (Spec.map (Scheme.ΓSpecIso R).hom p) ∈
        (Z : Set (Spec R)) := by rwa [hp']
    have := h (Spec.map (Scheme.ΓSpecIso R).hom p) hmem
    change (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom x) ∈ p.asIdeal at this
    simpa using this
  · intro h p hp
    exact h _ hp

/-- The vanishing ideal of the image of a set under `Spec` of a ring map is the preimage of its
vanishing ideal. -/
private theorem vanishingIdeal_image_comap {A B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (S : Set (PrimeSpectrum B)) :
    PrimeSpectrum.vanishingIdeal (PrimeSpectrum.comap f '' S) =
      Ideal.comap f (PrimeSpectrum.vanishingIdeal S) := by
  ext a
  simp only [PrimeSpectrum.mem_vanishingIdeal, Set.forall_mem_image, Ideal.mem_comap]
  rfl

/-- The ideal of global sections of the reduced image of `(g = 0)` in `T_{m,q}`, read in
`K[[x, y]]^{μ_m}`, consists of the invariants in the radical of `(g)`. -/
private theorem comap_vanishingIdeal_cyclicQuotientImage {K : Type v} [Field K] {m : ℕ} {q : ℤ}
    (h : IsCyclicQuotientSetting K m q) (g : MvPowerSeries (Fin 2) K) :
    Ideal.comap (Scheme.ΓSpecIso (.of (cyclicInvariants K m q))).inv.hom
        ((Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h g)).ideal
          ⟨⊤, isAffineOpen_top _⟩) =
      Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g}).radical := by
  rw [comap_ΓSpecIso_vanishingIdeal]
  exact (PrimeSpectrum.vanishingIdeal_closure (R := cyclicInvariants K m q) _).trans <|
    (vanishingIdeal_image_comap (cyclicInvariants K m q).subtype _).trans <| by
      rw [← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

/-- For `m = 1` the group `μ_1` is trivial, so every power series is invariant. -/
private theorem cyclicInvariants_one_eq_top (K : Type v) [Field K] (q : ℤ) :
    cyclicInvariants K 1 q = ⊤ := by
  ext f
  simp only [Subring.mem_top, iff_true]
  intro ζ
  change MvPowerSeries.rescale (cyclicWeights K 1 q ζ) f = f
  rw [Subsingleton.elim ζ 1, map_one, MvPowerSeries.rescale_one, RingHom.id_apply]

/-- **The trivial-group model.** A ring isomorphism `K[[x, y]] ≃ R̂` over `K` carrying `(g)` onto
`I R̂`, for `(g)` radical, is the model `T_{1,1}` with the reduced image of `(g = 0)`. -/
private theorem exists_of_ringEquiv_mvPowerSeries {K : Type v} [Field K] [IsAlgClosed K]
    [CharZero K] {R Rh : Type v} [CommRing R] [CommRing Rh] [Algebra K R] [Algebra R Rh]
    (g : MvPowerSeries (Fin 2) K) (hg : (Ideal.span {g}).radical = Ideal.span {g})
    (I : Ideal R) (Φ : MvPowerSeries (Fin 2) K ≃+* Rh)
    (hc : ∀ c : K, Φ (MvPowerSeries.C c) = algebraMap R Rh (algebraMap K R c))
    (hI : Ideal.map Φ (Ideal.span {g}) = Ideal.map (algebraMap R Rh) I) :
    ∃ (m : ℕ) (q : ℤ) (_ : IsCyclicQuotientSetting K m q) (φ : cyclicInvariants K m q ≃+* Rh),
      (∀ c : K, ((φ.symm (algebraMap R Rh (algebraMap K R c)) : cyclicInvariants K m q) :
          MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g}).radical) =
        Ideal.map (algebraMap R Rh) I := by
  have htop : ∀ f, f ∈ cyclicInvariants K 1 1 := fun f => by
    rw [cyclicInvariants_one_eq_top]; trivial
  let φ : cyclicInvariants K 1 1 ≃+* Rh :=
    { toFun := fun x => Φ x.1
      invFun := fun z => ⟨Φ.symm z, htop _⟩
      left_inv := fun x => Subtype.ext (Φ.symm_apply_apply x.1)
      right_inv := Φ.apply_symm_apply
      map_mul' := fun x y => map_mul Φ x.1 y.1
      map_add' := fun x y => map_add Φ x.1 y.1 }
  refine ⟨1, 1, ⟨inferInstance, inferInstance, le_rfl, by simp⟩, φ, fun c => ?_, ?_⟩
  · change Φ.symm _ = _
    rw [← hc, RingEquiv.symm_apply_apply]
  · rw [hg, ← hI]
    ext z
    rw [Ideal.mem_map_of_equiv, Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, htop x⟩, hx, rfl⟩

/-! ### The smooth case: the germ, its completion and a smooth boundary -/

private theorem coheight_ne_zero {Y : Scheme.{v}} [IrreducibleSpace Y] {x : Y}
    (hx : closure ({x} : Set Y) ≠ Set.univ) : Order.coheight x ≠ 0 := by
  intro h0
  have hgx : genericPoint Y ≤ x :=
    Order.coheight_eq_zero.mp h0 ((genericPoint_spec Y).specializes (Set.mem_univ x))
  refine hx (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec Y).def]
  exact isClosed_closure.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hgx))

private theorem coheight_eq_one_of_not_isClosed {k : Type v} [Field k] {Y : Scheme.{v}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hYd : topologicalKrullDim Y = 2) {x : Y} (hx : ¬ IsClosed ({x} : Set Y))
    (hx' : closure ({x} : Set Y) ≠ Set.univ) : Order.coheight x = 1 := by
  obtain ⟨z, hz, hzx⟩ : ∃ z ∈ closure ({x} : Set Y), z ≠ x := by
    by_contra! h
    exact hx (isClosed_of_closure_subset h)
  have hz2 : Order.coheight z ≤ 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY z
    rw [hYd] at h
    generalize topologicalKrullDim (closure ({z} : Set Y)) = d at h
    induction d using WithBot.recBotCoe with
    | bot => simp at h
    | coe d => exact le_add_self.trans_eq (WithBot.coe_inj.mp (by push_cast; exact h))
  have h := (Order.coheight_add_one_le (lt_of_le_not_ge (α := Y)
    (specializes_iff_mem_closure.mpr hz) fun h' =>
      hzx ((specializes_iff_mem_closure.mpr hz).antisymm h').eq.symm)).trans hz2
  rw [← one_add_one_eq_two, ENat.add_le_add_iff_right ENat.one_ne_top] at h
  exact h.antisymm (Order.one_le_iff_ne_zero.mpr (coheight_ne_zero hx'))

private theorem eq_of_specializes_of_coheight_eq_one {Y : Scheme.{v}} [IrreducibleSpace Y]
    {ξ η : Y} (hη : Order.coheight η = 1) (h : ξ ⤳ η)
    (hξ : closure ({ξ} : Set Y) ≠ Set.univ) : ξ = η := by
  by_contra hne
  have h1 := Order.coheight_add_one_le (lt_of_le_not_ge (α := Y) h fun h' =>
    hne (h.antisymm h').eq)
  rw [hη] at h1
  exact coheight_ne_zero hξ
    (nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right ENat.one_ne_top).mp (by simpa using h1)))

/-- A non-closed point of the fibre of a resolution over the point lies on an exceptional curve.
-/
private theorem exists_mem_support_of_not_isClosed {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g) {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E) {η : Y}
    (hηF : η ∈ g.base ⁻¹' {P}) (hη : ¬ IsClosed ({η} : Set Y)) : ∃ j, η ∈ (E j).support := by
  have hYv := hg.isVariety
  have : IsIntegral Y := hYv.toIsIntegral
  have : LocallyOfFiniteType (g ≫ sX) := hYv.toLocallyOfFiniteType
  have hYd := hg.topologicalKrullDim_eq
  obtain ⟨hFcl, hFne⟩ := hg.isClosed_preimage_and_ne_univ
  have hne : closure ({η} : Set Y) ≠ Set.univ := fun h =>
    hFne (Set.eq_univ_of_univ_subset
      (h ▸ hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηF)))
  have hη1 := coheight_eq_one_of_not_isClosed (g ≫ sX) hYd hη hne
  set D := AlgebraicGeometry.PrimeDivisor.ofCoheightOne η hη1
  have hsupp : D.support = closure {η} := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  have hD : IsGermExceptionalCurve g P D := by
    refine ⟨⟨⟨?_, ?_⟩, fun Z ⟨hZirr, hZF⟩ hle => ?_⟩,
      isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hYd _⟩
    · rw [hsupp]; exact isIrreducible_singleton.closure
    · rw [hsupp]; exact hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηF)
    · rw [hsupp] at hle ⊢
      have hgen := hZirr.isGenericPoint_genericPoint_closure
      have hξF : hZirr.genericPoint ∈ g.base ⁻¹' {P} :=
        hFcl.closure_subset_iff.mpr hZF hgen.mem
      have hξ := eq_of_specializes_of_coheight_eq_one hη1
        (hgen.specializes (subset_closure (hle (subset_closure rfl))))
        (fun h => hFne (Set.eq_univ_of_univ_subset
          (h ▸ hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξF))))
      rw [← hξ, hgen.def]
      exact subset_closure
  obtain ⟨j, hj⟩ := hE.exists_eq D hD
  refine ⟨j, ?_⟩
  rw [hj, hsupp]
  exact subset_closure rfl

/-- A resolution of a surface germ without exceptional curves has finite fibre over the point. -/
private theorem finite_preimage_of_isExceptionalCurveEnumeration_zero {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g)
    {E : Fin 0 → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E) :
    (g.base ⁻¹' {P}).Finite := by
  have : IsIntegral Y := hg.isVariety.toIsIntegral
  obtain ⟨hFcl, -⟩ := hg.isClosed_preimage_and_ne_univ
  have hcl : ∀ η ∈ g.base ⁻¹' {P}, IsClosed ({η} : Set Y) := fun η hηF => by
    by_contra hη
    exact (exists_mem_support_of_not_isClosed hg hE hηF hη).choose.elim0
  -- a closed subset of a Noetherian space all of whose points are closed is finite
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨S, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨g.base ⁻¹' {P}, hFcl⟩
  have hS' : g.base ⁻¹' {P} = ⋃ (K : TopologicalSpace.Closeds Y) (_ : K ∈ S), (K : Set Y) := by
    have := congrArg (fun K : TopologicalSpace.Closeds Y => (K : Set Y)) hS
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
    simpa [Set.iSup_eq_iUnion] using this
  rw [hS']
  refine Set.Finite.biUnion S.finite_toSet fun K hK => ?_
  have hKirr : IsIrreducible (K : Set Y) := hSirr ⟨K, hK⟩
  have hgen := hKirr.isGenericPoint_genericPoint_closure
  rw [K.isClosed.closure_eq] at hgen
  have hKF : (K : Set Y) ⊆ g.base ⁻¹' {P} := by
    rw [hS']; exact Set.subset_biUnion_of_mem (u := fun K : TopologicalSpace.Closeds Y =>
      (K : Set Y)) hK
  have := hcl _ (hKF hgen.mem)
  rw [← hgen.def, this.closure_eq]
  exact Set.finite_singleton _

/-- The stalk maps of an isomorphism of schemes are isomorphisms. -/
private theorem isIso_stalkMap_of_isIso {X Y : Scheme.{v}} (f : X ⟶ Y) [IsIso f] (x : X) :
    IsIso (f.stalkMap x) := by
  have : IsOpenImmersion f := IsOpenImmersion.of_isIso f
  exact inferInstanceAs <| IsIso (f.toLRSHom.stalkMap x)

/-- A resolution of a surface germ without exceptional curves is an isomorphism near the point,
so the germ is regular there. -/
private theorem isRegularLocalRing_stalk_of_isExceptionalCurveEnumeration_zero {k : Type v}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g)
    {E : Fin 0 → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E) :
    IsRegularLocalRing (X.presheaf.stalk P) := by
  have hXv : IsNormalVariety k sX := hg.isSurfaceGerm.1
  have : IsIntegral X := hXv.1.toIsIntegral
  have : IsNormal X := hXv.2
  have : IsIntegral Y := hg.isIntegral sX
  have : IsProper g := hg.isSmoothResolution.isProper
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hg.isSmoothResolution.isBirationalMorphism
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso g hb).1 this
  set U : X.Opens := ⟨_, hU⟩
  have hPU : P ∈ U := finite_preimage_of_isExceptionalCurveEnumeration_zero hg hE
  obtain ⟨y', hy'⟩ := (g ∣_ U).surjective ⟨P, hPU⟩
  have hgy : g y'.1 = P := by
    rw [← morphismRestrict_base_coe g U y', hy']
  have hst : IsIso (g.stalkMap y'.1) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap g U y') |>.mp
      (isIso_stalkMap_of_isIso (g ∣_ U) y')
  have hreg := ((isRegular_iff_regular_stalks Y).1
    (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme (g ≫ sX)
      hg.isSmoothResolution.isSmoothScheme)).2 y'.1
  subst hgy
  exact IsRegularLocalRing.of_ringEquiv (asIso (g.stalkMap y'.1)).commRingCatIsoToRingEquiv.symm

/-- **The completed local ring at a closed point is `K[[x, y]]` over `K`.** -/
private theorem exists_ringEquiv_mvPowerSeries_of_isRegularSystemOfParameters {K : Type v}
    [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType sX] [IsLocallyNoetherian X] (p : X) (hp : IsClosed ({p} : Set X))
    {n : ℕ} {x : Fin n → X.presheaf.stalk p} (hx : IsRegularSystemOfParameters x) :
    letI := Mori.stalkAlgebra sX p
    ∃ Φ : MvPowerSeries (Fin n) K ≃+*
        𝒪̂(X.presheaf.stalk p),
      (∀ c : K, Φ (MvPowerSeries.C c) = algebraMap (X.presheaf.stalk p)
        (𝒪̂(X.presheaf.stalk p))
          (algebraMap K (X.presheaf.stalk p) c)) ∧
      ∀ i, Φ (MvPowerSeries.X i) = algebraMap (X.presheaf.stalk p)
        (𝒪̂(X.presheaf.stalk p)) (x i) := by
  letI := Mori.stalkAlgebra sX p
  obtain ⟨K', ⟨hk, hK'⟩, -⟩ :=
    MMP.Flips.ResolutionInputs.existsUnique_isFieldOfRepresentatives_completion sX p hp
  obtain ⟨F, ⟨hFX, hFbij⟩, -⟩ :=
    MMP.Flips.ResolutionInputs.existsUnique_algHom_X_eq_bijective_stalk p hx K' hK'
  have hk' : ∀ c : K, algebraMap K (𝒪̂(X.presheaf.stalk p)) c =
      algebraMap (X.presheaf.stalk p) (𝒪̂(X.presheaf.stalk p))
        (algebraMap K (X.presheaf.stalk p) c) := fun c =>
    IsScalarTower.algebraMap_apply K (X.presheaf.stalk p) _ c
  let ι : K →+* K' :=
    (algebraMap K (𝒪̂(X.presheaf.stalk p))).codRestrict K' (fun c => hk ⟨c, rfl⟩)
  have hι : Function.Bijective ι := by
    refine ⟨ι.injective, fun z => ?_⟩
    obtain ⟨r, hr⟩ := AdicCompletion.residueField_map_bijective (X.presheaf.stalk p) |>.2
      (residue (𝒪̂(X.presheaf.stalk p)) (z : 𝒪̂(X.presheaf.stalk p)))
    obtain ⟨r, rfl⟩ := residue_surjective r
    obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective sX p hp r
    refine ⟨c, hK'.2.1 ?_⟩
    change residue (𝒪̂(X.presheaf.stalk p)) (algebraMap K (𝒪̂(X.presheaf.stalk p)) c) =
      residue (𝒪̂(X.presheaf.stalk p)) z
    rw [← hr, ResidueField.map_residue, hk']
    rw [← ResidueField.map_residue]
    exact congrArg _ hc
  let e : K ≃+* K' := RingEquiv.ofBijective ι hι
  have hmapbij : Function.Bijective (MvPowerSeries.map (σ := Fin n) e.toRingHom) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨MvPowerSeries.map e.symm.toRingHom, fun f => ?_, fun f => ?_⟩ <;>
    · ext d
      simp
  refine ⟨RingEquiv.ofBijective (F.toRingHom.comp (MvPowerSeries.map e.toRingHom))
    (hFbij.comp hmapbij), fun c => ?_, fun i => ?_⟩
  · change F (MvPowerSeries.map _ (MvPowerSeries.C c)) = _
    rw [MvPowerSeries.map_C, ← hk']
    have h1 : MvPowerSeries.C (e.toRingHom c) =
        algebraMap K' (MvPowerSeries (Fin n) K') (e.toRingHom c) := rfl
    rw [h1, F.commutes]
    rfl
  · change F (MvPowerSeries.map _ (MvPowerSeries.X i)) = _
    rw [MvPowerSeries.map_X, hFX]

/-- In a two-dimensional regular local ring, an ideal `I ≠ 0, 𝔪` with regular quotient is
generated by the first entry of a regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_span_eq {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) (I : Ideal R)
    (hI : IsRegularLocalRing (R ⧸ I)) (h0 : I ≠ ⊥) (hm : I ≠ maximalIdeal R) :
    ∃ x : Fin 2 → R, MMP.Mori.IsRegularSystemOfParameters x ∧ I = Ideal.span {x 0} := by
  obtain ⟨xs, hgen, hlen, c, hc, hIc, -⟩ :=
    IsRegularLocalRing.exists_ofList_eq_maximalIdeal_length_eq_spanFinrank_and_ofList_take_eq I hI
  have h2 : xs.length = 2 := by
    have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at this
    rw [hlen]
    exact_mod_cast this
  match xs, h2, c, hc with
  | [a, b], _, 0, _ =>
    exact absurd (by simpa [Ideal.ofList] using hIc.symm) h0
  | [a, b], _, 2, _ =>
    exact absurd (hIc.symm.trans (by simpa using hgen)) hm
  | [a, b], _, 1, _ =>
    refine ⟨![a, b], ⟨?_, hdim⟩, ?_⟩
    · rw [← hgen]
      congr 1
      ext z
      simp [Fin.exists_fin_two, eq_comm, or_comm]
    · rw [← hIc]
      simp [Ideal.ofList]

/-- At a closed point `y` of a prime divisor `C` of a surface, the ideal of `C` in `𝒪_{Y,y}` is
neither `0` nor the maximal ideal. -/
private theorem stalk_idealSheaf_ne_bot_and_ne_maximalIdeal {k : Type v} [Field k]
    {Y : Scheme.{v}} {sY : Y ⟶ Spec (.of k)} (hY : Mori.IsVariety k sY)
    (hYd : topologicalKrullDim Y = 2) (C : Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ C.support)
    (hycl : IsClosed ({y} : Set Y)) :
    IdealSheafData.stalk C.idealSheaf y ≠ ⊥ ∧
      IdealSheafData.stalk C.idealSheaf y ≠ maximalIdeal (Y.presheaf.stalk y) := by
  have : IsIntegral Y := hY.toIsIntegral
  have hC := isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hY hYd C
  have hdimC : topologicalKrullDim (C.support : Set Y) = 1 := by
    rw [← topologicalKrullDim_subscheme]; exact hC.2
  have hsupp := MMP.Resolution.Aux.support_eq_closure_genericPoint C
  constructor
  · intro h0
    have hξ : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
    have hmem : genericPoint Y ∈ C.support :=
      (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes C.idealSheaf hξ).2
        (by rw [h0]; exact bot_le)
    have huniv : (C.support : Set Y) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (genericPoint_spec Y).def]
      exact C.idealSheaf.support.isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hmem)
    rw [huniv, (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq, hYd] at hdimC
    exact absurd hdimC (by decide)
  · intro hm
    have hη : AlgebraicGeometry.PrimeDivisor.genericPoint C ⤳ y := by
      rwa [specializes_iff_mem_closure, ← hsupp]
    have hle := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes C.idealSheaf hη).1
      (by
        change _ ∈ (C.support : Set Y)
        rw [hsupp]; exact subset_closure rfl)
    have hrefl : MMP.Intersection.primeOfSpecializes (specializes_refl y) ≤
        MMP.Intersection.primeOfSpecializes hη := by
      intro a ha
      apply hle
      rw [hm]
      change (Y.presheaf.stalkSpecializes (specializes_refl y)).hom a ∈ maximalIdeal _ at ha
      rwa [TopCat.Presheaf.stalkSpecializes_refl] at ha
    have hyη := MMP.Intersection.specializes_of_primeOfSpecializes_le _ _ hrefl
    have hηy : AlgebraicGeometry.PrimeDivisor.genericPoint C = y := by
      have := hyη.mem_closure
      rw [hycl.closure_eq] at this
      exact this
    have hsub : (C.support : Set Y) = {y} := by rw [hsupp, hηy, hycl.closure_eq]
    rw [hsub] at hdimC
    have : DiscreteTopology ({y} : Set Y) := Subsingleton.discreteTopology
    have h0 := topologicalKrullDim_zero_of_discreteTopology ({y} : Set Y)
    rw [hdimC] at h0
    exact absurd h0 (by decide)

/-! ### The completed local ring at a closed point -/

/-- **The completed local ring at a closed point is `K[[x₁, …, xₙ]]` over `K`**, the variables
going to any generators `z₁, …, zₙ` of the maximal ideal, `n = dim 𝒪_{X,p}`. -/
private theorem exists_ringEquiv_mvPowerSeries_of_span_eq {K : Type v}
    [Field K] [IsAlgClosed K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType sX] [IsLocallyNoetherian X] (p : X) (hp : IsClosed ({p} : Set X))
    {n : ℕ} (hdim : ringKrullDim (X.presheaf.stalk p) = n)
    {z : Fin n → 𝒪̂(X.presheaf.stalk p)}
    (hz : Ideal.span (Set.range z) =
      maximalIdeal (𝒪̂(X.presheaf.stalk p))) :
    letI := Mori.stalkAlgebra sX p
    ∃ Φ : MvPowerSeries (Fin n) K ≃+*
        𝒪̂(X.presheaf.stalk p),
      (∀ c : K, Φ (MvPowerSeries.C c) = algebraMap (X.presheaf.stalk p)
        (𝒪̂(X.presheaf.stalk p))
          (algebraMap K (X.presheaf.stalk p) c)) ∧
      ∀ i, Φ (MvPowerSeries.X i) = z i := by
  letI := Mori.stalkAlgebra sX p
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (maximalIdeal
      (𝒪̂(X.presheaf.stalk p)))).comp
        ((algebraMap (X.presheaf.stalk p) _).comp (algebraMap K (X.presheaf.stalk p)))) := by
    intro w
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨r, hr⟩ := AdicCompletion.residueField_map_bijective (X.presheaf.stalk p) |>.2
      (residue _ w)
    obtain ⟨r, rfl⟩ := residue_surjective r
    obtain ⟨c, hc⟩ := MMP.Mori.SurfaceAux.residue_surjective sX p hp r
    refine ⟨c, ?_⟩
    change residue _ (algebraMap (X.presheaf.stalk p) _ (algebraMap K (X.presheaf.stalk p) c)) =
      residue _ w
    rw [← hr, ← ResidueField.map_residue]
    exact congrArg _ hc
  obtain ⟨F, hFs, hFX, hFC⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom (maximalIdeal
      (𝒪̂(X.presheaf.stalk p))) z hz _ hsurj
  have hinj := MMP.Flips.ResolutionInputs.injective_of_surjective_of_ringKrullDim_le F hFs
    (MvPowerSeries.ringKrullDim_le K n)
    (by rw [IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal, hdim])
  exact ⟨RingEquiv.ofBijective F ⟨hinj, hFs⟩, hFC, hFX⟩

/-! ### The formal Morse lemma for a node -/

section Morse

variable {R : Type*} [CommRing R] {M : Ideal R}

/-- Two elements congruent to generators of a finitely generated ideal `M ⊆ rad R` modulo `M²`
generate `M`. -/
private theorem span_pair_add_eq (hfg : M.FG) (hjac : M ≤ (⊥ : Ideal R).jacobson)
    {u v a b : R} (huv : Ideal.span {u, v} = M) (ha : a ∈ M ^ 2) (hb : b ∈ M ^ 2) :
    Ideal.span {u + a, v + b} = M := by
  have hu : u ∈ M := huv ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hv : v ∈ M := huv ▸ Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have ha' : a ∈ M := Ideal.pow_le_self two_ne_zero ha
  have hb' : b ∈ M := Ideal.pow_le_self two_ne_zero hb
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨M.add_mem hu ha', M.add_mem hv hb'⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac ?_
  have h2 : M ^ 2 ≤ M • M := by rw [pow_two]; rfl
  conv_lhs => rw [← huv]
  rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · have := Submodule.sub_mem _
      (Submodule.mem_sup_left (Ideal.subset_span (Set.mem_insert (u + a) {v + b})))
      (Submodule.mem_sup_right (h2 ha))
    simpa using this
  · have := Submodule.sub_mem _
      (Submodule.mem_sup_left (Ideal.subset_span
        (Set.mem_insert_of_mem (u + a) (Set.mem_singleton (v + b)))))
      (Submodule.mem_sup_right (h2 hb))
    simpa using this

/-- An element of `M^(n+1)`, for `M = (u, v)`, is `u P + v Q` with `P, Q ∈ M^n`. -/
private theorem exists_eq_add_of_mem_pow_succ {u v e : R} (huv : Ideal.span {u, v} = M) {n : ℕ}
    (he : e ∈ M ^ (n + 1)) : ∃ P Q, P ∈ M ^ n ∧ Q ∈ M ^ n ∧ e = u * P + v * Q := by
  have he' : e ∈ Ideal.span {u, v} * M ^ n := by rwa [huv, ← pow_succ']
  rw [Ideal.span_insert, Ideal.sup_mul, Submodule.mem_sup] at he'
  obtain ⟨y, hy, z, hz, rfl⟩ := he'
  obtain ⟨P, hP, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  obtain ⟨Q, hQ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
  exact ⟨P, Q, hP, hQ, rfl⟩

/-- One step of the approximation. -/
private theorem exists_step (hfg : M.FG) (hjac : M ≤ (⊥ : Ideal R).jacobson) {u v g : R}
    (huv : Ideal.span {u, v} = M) (n : ℕ) (a b : R) (ha : a ∈ M ^ 2) (hb : b ∈ M ^ 2)
    (he : g - (u + a) * (v + b) ∈ M ^ (n + 3)) :
    ∃ a' b', a' ∈ M ^ 2 ∧ b' ∈ M ^ 2 ∧ g - (u + a') * (v + b') ∈ M ^ (n + 4) ∧
      a' - a ∈ M ^ (n + 2) ∧ b' - b ∈ M ^ (n + 2) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_eq_add_of_mem_pow_succ
    (span_pair_add_eq hfg hjac huv ha hb) he
  have hle : M ^ (n + 2) ≤ M ^ 2 := Ideal.pow_le_pow_right (by omega)
  refine ⟨a + Q, b + P, (M ^ 2).add_mem ha (hle hQ),
    (M ^ 2).add_mem hb (hle hP), ?_, by simpa using hQ, by simpa using hP⟩
  · have : g - (u + (a + Q)) * (v + (b + P)) = -(P * Q) := by
      linear_combination hPQ
    rw [this]
    refine (M ^ (n + 4)).neg_mem ?_
    have : P * Q ∈ M ^ (n + 2 + (n + 2)) := by
      rw [pow_add]; exact Ideal.mul_mem_mul hP hQ
    exact Ideal.pow_le_pow_right (by omega) this

private theorem mem_pow_smul_top {x : R} {n : ℕ} :
    x ∈ (M ^ n • ⊤ : Submodule R R) ↔ x ∈ M ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/-- **The formal Morse lemma for a node.** In a ring complete for a finitely generated ideal
`M = (u, v)`, an element `g ≡ uv` modulo `M³` factors as `g = (u + a)(v + b)` with
`a, b ∈ M²`. -/
private theorem exists_eq_mul_of_sub_mul_mem_pow_three [IsAdicComplete M R] (hfg : M.FG)
    {u v g : R} (huv : Ideal.span {u, v} = M) (hg : g - u * v ∈ M ^ 3) :
    ∃ a b, a ∈ M ^ 2 ∧ b ∈ M ^ 2 ∧ g = (u + a) * (v + b) := by
  have hjac : M ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot M
  let P : ℕ → R × R → Prop := fun n p =>
    p.1 ∈ M ^ 2 ∧ p.2 ∈ M ^ 2 ∧ g - (u + p.1) * (v + p.2) ∈ M ^ (n + 3)
  have hstep : ∀ n p, P n p → ∃ p', P (n + 1) p' ∧ p'.1 - p.1 ∈ M ^ (n + 2) ∧
      p'.2 - p.2 ∈ M ^ (n + 2) := by
    rintro n ⟨a, b⟩ ⟨ha, hb, he⟩
    obtain ⟨a', b', ha', hb', he', hda, hdb⟩ := exists_step hfg hjac huv n a b ha hb he
    exact ⟨(a', b'), ⟨ha', hb', he'⟩, hda, hdb⟩
  choose! step hstep' using hstep
  let seq : ℕ → R × R := fun n => Nat.rec (0, 0) (fun n p => step n p) n
  have hseq : ∀ n, P n (seq n) := by
    intro n
    induction n with
    | zero =>
      have h0 : seq 0 = (0, 0) := rfl
      refine ⟨?_, ?_, ?_⟩ <;> rw [h0]
      · exact (M ^ 2).zero_mem
      · exact (M ^ 2).zero_mem
      · simpa using hg
    | succ n ih => exact (hstep' n _ ih).1
  have hsucc : ∀ n, seq (n + 1) = step n (seq n) := fun n => rfl
  have hcauchy : ∀ (i : Fin 2) {m n : ℕ}, m ≤ n →
      (if i = 0 then (seq n).1 else (seq n).2) - (if i = 0 then (seq m).1 else (seq m).2) ∈
        M ^ (m + 2) := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h := hstep' n _ (hseq n)
      have hle : M ^ (n + 2) ≤ M ^ (m + 2) := Ideal.pow_le_pow_right (by omega)
      fin_cases i
      · have := (M ^ (m + 2)).add_mem ih (hle h.2.1)
        simp only [Fin.zero_eta, Fin.isValue, if_true, hsucc] at this ⊢
        convert this using 1; ring
      · have := (M ^ (m + 2)).add_mem ih (hle h.2.2)
        simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false, hsucc] at this ⊢
        convert this using 1; ring
  have hcauchy' : ∀ i : Fin 2, ∀ {m n : ℕ}, m ≤ n →
      (if i = 0 then (seq m).1 else (seq m).2) ≡ (if i = 0 then (seq n).1 else (seq n).2)
        [SMOD (M ^ m • ⊤ : Submodule R R)] := by
    intro i m n hmn
    rw [SModEq.sub_mem, mem_pow_smul_top, ← neg_sub]
    exact (M ^ m).neg_mem (Ideal.pow_le_pow_right (by omega) (hcauchy i hmn))
  obtain ⟨a, ha⟩ := IsAdicComplete.toIsPrecomplete.prec (hcauchy' 0)
  obtain ⟨b, hb⟩ := IsAdicComplete.toIsPrecomplete.prec (hcauchy' 1)
  simp only [if_true, Fin.isValue, one_ne_zero, if_false] at ha hb
  have ha' : ∀ n, (seq n).1 - a ∈ M ^ n := fun n => mem_pow_smul_top.mp (SModEq.sub_mem.mp (ha n))
  have hb' : ∀ n, (seq n).2 - b ∈ M ^ n := fun n => mem_pow_smul_top.mp (SModEq.sub_mem.mp (hb n))
  have hu : u ∈ M := huv ▸ Ideal.subset_span (Set.mem_insert _ _)
  refine ⟨a, b, ?_, ?_, ?_⟩
  · simpa using (M ^ 2).sub_mem (hseq 2).1 (ha' 2)
  · simpa using (M ^ 2).sub_mem (hseq 2).2.1 (hb' 2)
  · rw [← sub_eq_zero]
    refine (IsAdicComplete.toIsHausdorff (I := M) (M := R)).haus' _ fun n => ?_
    rw [SModEq.sub_mem, sub_zero, mem_pow_smul_top]
    have h1 := Ideal.pow_le_pow_right (I := M) (show n ≤ n + 3 by omega) (hseq n).2.2
    have h2 : (u + (seq n).1) * (v + (seq n).2) - (u + a) * (v + b) ∈ M ^ n := by
      have : (u + (seq n).1) * (v + (seq n).2) - (u + a) * (v + b) =
          ((seq n).1 - a) * (v + (seq n).2) + (u + a) * ((seq n).2 - b) := by ring
      rw [this]
      exact (M ^ n).add_mem (Ideal.mul_mem_right _ _ (ha' n)) (Ideal.mul_mem_left _ _ (hb' n))
    have := (M ^ n).add_mem h1 h2
    convert this using 1; ring

end Morse

/-! ### Birational transforms and the local equation of a reduced boundary -/

section Mono

open CategoryTheory.Limits

/-- The birational transform is monotone: a larger closed subscheme has a larger transform. -/
private theorem birationalTransform_mono {S : Scheme} (p : S) (hp : IsClosed ({p} : Set S))
    {C D : S.IdealSheafData} (h : D ≤ C) :
    MMP.Resolution.birationalTransform p hp D ≤ MMP.Resolution.birationalTransform p hp C := by
  unfold MMP.Resolution.birationalTransform
  set π := blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  set W := (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support.compl
  let φ : pullback C.subschemeι π ⟶ pullback D.subschemeι π :=
    pullback.map _ _ _ _ (Scheme.IdealSheafData.inclusion h) (𝟙 _) (𝟙 _)
      (by rw [Scheme.IdealSheafData.inclusion_subschemeι, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])
  have hφ : φ ≫ pullback.snd D.subschemeι π = pullback.snd C.subschemeι π := by
    rw [pullback.lift_snd, Category.comp_id]
  have hle : pullback.snd C.subschemeι π ⁻¹ᵁ W ≤ φ ⁻¹ᵁ (pullback.snd D.subschemeι π ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hφ]
  have key : φ.resLE _ _ hle ≫ (pullback.snd D.subschemeι π ⁻¹ᵁ W).ι ≫
      pullback.snd D.subschemeι π = (pullback.snd C.subschemeι π ⁻¹ᵁ W).ι ≫
        pullback.snd C.subschemeι π := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hφ]
  rw [← key]
  exact Scheme.Hom.le_ker_comp _ _

end Mono

/-- In a two-dimensional regular local ring a prime ideal other than `0` and `𝔪` is generated by
a prime element. -/
private theorem exists_prime_eq_span_of_ne {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) (P : Ideal R) [hP : P.IsPrime] (h0 : P ≠ ⊥)
    (hm : P ≠ maximalIdeal R) : ∃ π : R, Prime π ∧ P = Ideal.span {π} := by
  have : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid R
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have hbot : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h0)
  have hlt : P < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal hP.ne_top) hm
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hm2 : (maximalIdeal R).height = 2 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at h
    exact WithBot.coe_injective (h.trans rfl)
  have hP1 : P.height = 1 := by
    rw [hm2] at h2
    have h1' : (1 : ℕ∞) ≤ P.height := le_trans le_add_self h1
    generalize P.height = h at h1' h2 ⊢
    induction h using ENat.recTopCoe with
    | top => simp at h2
    | coe n =>
      have h1'' : 1 ≤ n := by exact_mod_cast h1'
      have h2' : n + 1 ≤ 2 := by exact_mod_cast h2
      have : n = 1 := by omega
      rw [this]; rfl
  obtain ⟨π, hπP, hπ⟩ := hP.exists_mem_prime_of_ne_bot h0
  exact ⟨π, hπ, Ideal.eq_span_singleton_of_height_eq_one hP1 hπP hπ⟩

/-- The ideal of a prime divisor in a local ring at a point of its support is prime. -/
private theorem isPrime_stalk_idealSheaf {Y : Scheme} (C : Mori.PrimeDivisor Y) {y : Y}
    (hy : y ∈ C.support) : (IdealSheafData.stalk C.idealSheaf y).IsPrime := by
  obtain ⟨y', rfl⟩ : y ∈ Set.range C.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have := C.integral
  rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
  exact RingHom.ker_isPrime _

/-- Two prime divisors through `y` with the same ideal in `𝒪_{Y,y}` are equal. -/
private theorem eq_of_stalk_idealSheaf_eq {Y : Scheme} {C C' : Mori.PrimeDivisor Y} {y : Y}
    (hy : y ∈ C.support) (h : IdealSheafData.stalk C.idealSheaf y =
      IdealSheafData.stalk C'.idealSheaf y) : C = C' := by
  have hsupp := MMP.Resolution.Aux.support_eq_closure_genericPoint C
  have hη : AlgebraicGeometry.PrimeDivisor.genericPoint C ⤳ y := by
    rwa [specializes_iff_mem_closure, ← hsupp]
  have hle := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes C.idealSheaf hη).1
    (by change _ ∈ (C.support : Set Y); rw [hsupp]; exact subset_closure rfl)
  rw [h] at hle
  exact (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support
    ((MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes C'.idealSheaf hη).2 hle))

private theorem iInf_fin_two' {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    ⨅ j, f j = f 0 ⊓ f 1 := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · exact le_iInf fun j => by fin_cases j; exacts [inf_le_left, inf_le_right]

private theorem stalk_inf {X : Scheme} [IsLocallyNoetherian X] (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊓ J) x = IdealSheafData.stalk I x ⊓ IdealSheafData.stalk J x := by
  have h := IdealSheafData.stalk_iInf_fin ![I, J] x
  rwa [iInf_fin_two', iInf_fin_two' (fun j => IdealSheafData.stalk (![I, J] j) x)] at h

private theorem span_inf_span_eq_span_mul {R : Type*} [CommRing R] {a b : R}
    (ha : Prime a) (hab : ¬ a ∣ b) :
    Ideal.span {a} ⊓ Ideal.span {b} = Ideal.span {a * b} := by
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ ?_)
  · rw [Ideal.mem_inf, Ideal.mem_span_singleton, Ideal.mem_span_singleton] at hx
    obtain ⟨v, rfl⟩ := hx.2
    rw [Ideal.mem_span_singleton, mul_comm a b]
    exact mul_dvd_mul_left _ ((ha.dvd_or_dvd hx.1).resolve_left hab)
  · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right _ _)
  · exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)

private theorem idealOrder_eq_of_mem_of_notMem {R : Type*} [CommRing R] [IsLocalRing R] {f : R}
    {n : ℕ} (h1 : f ∈ maximalIdeal R ^ n) (h2 : f ∉ maximalIdeal R ^ (n + 1)) :
    MMP.Resolution.mult f = n := by
  unfold MMP.Resolution.mult
  refine le_antisymm (not_lt.mp fun h => h2 ?_) ((MMP.Resolution.natCast_le_idealOrder_iff' _ n).2
    (by rwa [Ideal.span_singleton_le_iff_mem]))
  have := (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {f}) (n + 1)).1
    (by exact_mod_cast Order.add_one_le_of_lt h)
  exact (Ideal.span_singleton_le_iff_mem _).mp this

/-- **The local equation of a reduced boundary at a smooth point.** At a closed point `y` of a
surface with `𝒪_{Y,y}` regular, the ideal of a finite union of prime divisors through `y` is
generated by the product of their local equations, of multiplicity the sum of theirs. -/
private theorem exists_stalk_iInf_eq_span {K : Type*} [Field K] [IsAlgClosed K] {Y : Scheme}
    {sY : Y ⟶ Spec (.of K)} (hY : Mori.IsVariety K sY) (hYd : topologicalKrullDim Y = 2)
    [IsLocallyNoetherian Y] {y : Y} (hycl : IsClosed ({y} : Set Y))
    [IsRegularLocalRing (Y.presheaf.stalk y)] (S : Finset (Mori.PrimeDivisor Y))
    (hS : ∀ C ∈ S, y ∈ C.support) (mu : Mori.PrimeDivisor Y → ℕ)
    (hmu : ∀ C ∈ S, MMP.Resolution.multAt C.idealSheaf y = mu C) :
    ∃ φ : Y.presheaf.stalk y,
      IdealSheafData.stalk (⨅ C ∈ S, C.idealSheaf) y = Ideal.span {φ} ∧
        MMP.Resolution.mult φ = ∑ C ∈ S, mu C := by
  classical
  have hdim := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hY hYd y hycl
  have : IsDomain (Y.presheaf.stalk y) := IsRegularLocalRing.isDomain _
  have hπ : ∀ C, ∃ π : Y.presheaf.stalk y, C ∈ S →
      Prime π ∧ IdealSheafData.stalk C.idealSheaf y = Ideal.span {π} := by
    intro C
    by_cases hC : C ∈ S
    · have := isPrime_stalk_idealSheaf C (hS C hC)
      obtain ⟨h0, hm⟩ := stalk_idealSheaf_ne_bot_and_ne_maximalIdeal hY hYd C (hS C hC) hycl
      obtain ⟨π, hπ, he⟩ := exists_prime_eq_span_of_ne hdim _ h0 hm
      exact ⟨π, fun _ => ⟨hπ, he⟩⟩
    · exact ⟨1, fun h => absurd h hC⟩
  choose π hπ using hπ
  refine ⟨∏ C ∈ S, π C, ?_, ?_⟩
  · have key : ∀ s ⊆ S, IdealSheafData.stalk (⨅ C ∈ s, C.idealSheaf) y =
        Ideal.span {∏ C ∈ s, π C} := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.notMem_empty, iInf_of_empty, iInf_top, Finset.prod_empty,
          Ideal.span_singleton_one]
        exact MMP.Resolution.Aux.stalk_top y
      | insert a s ha ih =>
        intro hsub
        have haS := hsub (Finset.mem_insert_self a s)
        rw [Finset.iInf_insert, stalk_inf, ih ((Finset.subset_insert a s).trans hsub),
          (hπ a haS).2, Finset.prod_insert ha]
        refine span_inf_span_eq_span_mul (hπ a haS).1 fun hdvd => ?_
        obtain ⟨c, hc, hac⟩ := ((hπ a haS).1.dvd_finset_prod_iff _).mp hdvd
        have hcS := hsub (Finset.mem_insert_of_mem hc)
        have hassoc := (hπ a haS).1.associated_of_dvd (hπ c hcS).1 hac
        have heq := eq_of_stalk_idealSheaf_eq (C' := c) (hS a haS) (by
          rw [(hπ a haS).2, (hπ c hcS).2]
          exact Ideal.span_singleton_eq_span_singleton.mpr hassoc)
        exact ha (by rwa [heq])
    exact key S subset_rfl
  · have hd : (maximalIdeal (Y.presheaf.stalk y)).spanFinrank = 2 := by
      have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Y.presheaf.stalk y)
      rw [hdim] at this
      exact_mod_cast this
    have hord : ∀ C ∈ S, π C ∈ maximalIdeal (Y.presheaf.stalk y) ^ mu C ∧
        π C ∉ maximalIdeal (Y.presheaf.stalk y) ^ (mu C + 1) := by
      intro C hC
      have h := hmu C hC
      rw [MMP.Resolution.multAt, (hπ C hC).2] at h
      constructor
      · have := (MMP.Resolution.natCast_le_idealOrder_iff' _ (mu C)).1 h.ge
        exact (Ideal.span_singleton_le_iff_mem _).mp this
      · intro hmem
        have := (MMP.Resolution.natCast_le_idealOrder_iff' (Ideal.span {π C}) (mu C + 1)).2
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
        rw [h] at this
        exact absurd this (by norm_cast; omega)
    have := MMP.Mori.SurfaceAux.order_prod hd S π (fun _ => 1) mu
      (fun C hC => by simpa using hord C hC)
    simp only [pow_one, one_mul] at this
    exact_mod_cast idealOrder_eq_of_mem_of_notMem this.1 this.2

section BlowupCharts

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Resolution

section Poly

open Polynomial

variable {κ : Type*} [Field κ]

private theorem aeval_eq_sum (F : MvPolynomial (Fin 2) κ) (v : Fin 2 → Polynomial κ) :
    MvPolynomial.aeval v F =
      ∑ d ∈ F.support, C (F.coeff d) * (v 0 ^ d 0 * v 1 ^ d 1) := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two]
  rfl

private theorem add_eq_of_mem_support {R : Type*} [CommSemiring R] {F : MvPolynomial (Fin 2) R}
    {m : ℕ}
    (hF : F.IsHomogeneous m) {d : Fin 2 →₀ ℕ} (hd : d ∈ F.support) : d 0 + d 1 = m := by
  have := hF (MvPolynomial.mem_support_iff.mp hd)
  rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fin.sum_univ_two]
  simp

/-- The coefficients of `F(X, 1)` are those of `F(1, Y)` read backwards. -/
private theorem coeff_aeval_X_one {F : MvPolynomial (Fin 2) κ} {m : ℕ} (hF : F.IsHomogeneous m)
    (i : ℕ) : (MvPolynomial.aeval ![(Polynomial.X : Polynomial κ), 1] F).coeff i =
      if i ≤ m then (MvPolynomial.aeval ![(1 : Polynomial κ), Polynomial.X] F).coeff (m - i)
      else 0 := by
  rw [aeval_eq_sum, aeval_eq_sum, finset_sum_coeff, finset_sum_coeff]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun d hd => ?_
    have h := add_eq_of_mem_support hF hd
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow,
      mul_one, one_mul, coeff_C_mul_X_pow]
    congr 1
    apply propext
    omega
  · refine Finset.sum_eq_zero fun d hd => ?_
    have h := add_eq_of_mem_support hF hd
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow,
      mul_one, coeff_C_mul_X_pow]
    rw [if_neg (by omega)]

private theorem coeff_aeval_one_X_eq_zero {F : MvPolynomial (Fin 2) κ} {m : ℕ}
    (hF : F.IsHomogeneous m) {j : ℕ} (hj : m < j) :
    (MvPolynomial.aeval ![(1 : Polynomial κ), Polynomial.X] F).coeff j = 0 := by
  rw [aeval_eq_sum, finset_sum_coeff]
  refine Finset.sum_eq_zero fun d hd => ?_
  have h := add_eq_of_mem_support hF hd
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow,
    one_mul, coeff_C_mul_X_pow]
  rw [if_neg (by omega)]

end Poly

/-! ### The blow-up of a point in coordinates -/

/-- The only point of `Spec Γ(S, U)` lying over `p` is `primeIdealOf p`. -/
private theorem preimage_fromSpec_singleton {S : Scheme.{v}} {p : S}
    (c : CoordinateNeighbourhood S p) :
    c.isAffineOpen.fromSpec ⁻¹' ({p} : Set S) = {c.isAffineOpen.primeIdealOf ⟨p, c.mem⟩} := by
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun hq => c.isAffineOpen.fromSpec.isOpenEmbedding.injective ?_, ?_⟩
  · rw [hq, c.isAffineOpen.fromSpec_primeIdealOf]
  · rintro rfl
    exact c.isAffineOpen.fromSpec_primeIdealOf _

/-- On a coordinate neighbourhood, the ideal of the reduced point is `(x, y)`. -/
private theorem ideal_vanishingIdeal_eq_span {S : Scheme.{v}} {p : S}
    (hp : IsClosed ({p} : Set S)) (c : CoordinateNeighbourhood S p) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩ =
      Ideal.span {c.x, c.y} := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, c.span_eq]
  convert PrimeSpectrum.vanishingIdeal_singleton (c.isAffineOpen.primeIdealOf ⟨p, c.mem⟩)
    using 2
  exact preimage_fromSpec_singleton c

/-- A nonzero form `F` of degree `m` has `F(1, Y) ≠ 0`. -/
private theorem aeval_one_X_ne_zero {K : Type*} [CommRing K] {F : MvPolynomial (Fin 2) K}
    {m : ℕ} (hF : F.IsHomogeneous m) (h0 : F ≠ 0) :
    MvPolynomial.aeval (![1, Polynomial.X] : Fin 2 → Polynomial K) F ≠ 0 := by
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h0
  intro h
  apply hd
  have hprod : ∀ v : Fin 2 →₀ ℕ,
      (v.prod fun i k => (![1, Polynomial.X] : Fin 2 → Polynomial K) i ^ k) =
        Polynomial.X ^ (v 1) := by
    intro v
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [F.as_sum, map_sum] at h
  simp only [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, hprod] at h
  have h2 := congrArg (fun P : Polynomial K => P.coeff (d 1)) h
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h2
  rw [Finset.sum_eq_single d] at h2
  · simpa using h2
  · intro v hv hvd
    rw [if_neg]
    intro h1
    apply hvd
    have hv' := add_eq_of_mem_support hF hv
    have hd' := add_eq_of_mem_support hF (MvPolynomial.mem_support_iff.mpr hd)
    ext i
    fin_cases i
    · simp; omega
    · simpa using h1.symm
  · intro hdn
    exact absurd (MvPolynomial.notMem_support_iff.mp hdn) hd

/-- The kernel ideal sheaf of `Spec B ⟶ Spec A` induced by `g : A →+* B` is the ideal sheaf
attached to `ker g`. -/
private theorem ker_specMap {A B : Type v} [CommRing A] [CommRing B] (g : A →+* B) :
    (Spec.map (CommRingCat.ofHom g)).ker =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (RingHom.ker g)) := by
  rw [Scheme.ker_of_isAffine]
  congr 1
  have h : (Spec.map (CommRingCat.ofHom g)).appTop =
      (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso (.of B)).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).mpr (Scheme.ΓSpecIso_naturality _)
  have hinj : Function.Injective (Scheme.ΓSpecIso (.of B)).inv.hom :=
    (Scheme.ΓSpecIso (.of B)).symm.commRingCatIsoToRingEquiv.injective
  rw [h]
  change RingHom.ker (((Scheme.ΓSpecIso (.of B)).inv.hom.comp g).comp
    (Scheme.ΓSpecIso (.of A)).hom.hom) = _
  rw [RingHom.comp_assoc, RingHom.ker_comp_of_injective _ hinj, ← RingHom.comap_ker]
  exact Stacks.Blowup.comap_inv_eq_map_hom (Scheme.ΓSpecIso (.of A)).symm _

/-- The ideal of `ker (Spec B ⟶ Spec A)` on the top affine open. -/
private theorem ideal_ker_specMap_top {A B : Type v} [CommRing A] [CommRing B] (g : A →+* B) :
    (Spec.map (CommRingCat.ofHom g)).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom (RingHom.ker g) := by
  rw [ker_specMap]
  exact Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply _

/-- **Sections of a closed subscheme over a chart.** If an ideal sheaf `K` pulls back along an
open immersion `j : Spec B ⟶ X` with image `W` to the kernel of `Spec` of a surjection
`q : B → T`, then the sections of the closed subscheme of `K` over the preimage of `W` are `T`. -/
private theorem exists_ringEquiv_of_comap_eq {X : Scheme.{v}} (K : X.IdealSheafData)
    {B : CommRingCat.{v}} {T : Type v} [CommRing T] (j : Spec B ⟶ X) [IsOpenImmersion j]
    (W : X.affineOpens) (hW : j ''ᵁ ⊤ = W.1) (hle : ⊤ ≤ j ⁻¹ᵁ W.1) (q : B →+* T)
    (hq : Function.Surjective q)
    (hK : K.comap j = (Spec.map (CommRingCat.ofHom q)).ker) :
    ∃ ε : Γ(K.subscheme, K.subschemeι ⁻¹ᵁ W.1) ≃+* T,
      ∀ s, ε ((K.subschemeι.app W.1).hom s) =
        q ((Scheme.ΓSpecIso B).hom.hom ((j.appLE W.1 ⊤ hle).hom s)) := by
  obtain ⟨W, hWa⟩ := W
  subst hW
  set ψ : Γ(X, j ''ᵁ ⊤) →+* T := q.comp ((Scheme.ΓSpecIso B).hom.hom.comp
    (j.appIso ⊤).hom.hom) with hψ
  have hψs : Function.Surjective ψ := by
    refine hq.comp ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).hom).2.comp
      (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).hom).2)
  have hker : RingHom.ker ψ = K.ideal ⟨j ''ᵁ ⊤, hWa⟩ := by
    have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion K j ⟨⊤, isAffineOpen_top _⟩
    rw [hK, ideal_ker_specMap_top] at h1
    ext s
    rw [RingHom.mem_ker]
    have h2 : s ∈ K.ideal ⟨j ''ᵁ ⊤, hWa⟩ ↔ (j.appIso ⊤).hom.hom s ∈
        Ideal.map (Scheme.ΓSpecIso (.of B)).inv.hom (RingHom.ker q) := by
      rw [h1, Ideal.mem_comap, ← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    have h3 : Ideal.map (Scheme.ΓSpecIso (.of B)).inv.hom (RingHom.ker q) =
        (RingHom.ker q).comap (Scheme.ΓSpecIso (.of B)).hom.hom :=
      (Stacks.Blowup.comap_inv_eq_map_hom (Scheme.ΓSpecIso (.of B)).symm _).symm
    rw [h2, h3, Ideal.mem_comap, RingHom.mem_ker]
    rfl
  have hι := K.subschemeι_app_surjective ⟨j ''ᵁ ⊤, hWa⟩
  have hιk := K.ker_subschemeι_app ⟨j ''ᵁ ⊤, hWa⟩
  refine ⟨(RingHom.quotientKerEquivOfSurjective hι).symm.trans
    ((Ideal.quotEquivOfEq (hιk.trans hker.symm)).trans
      (RingHom.quotientKerEquivOfSurjective hψs)), fun s => ?_⟩
  have : (RingHom.quotientKerEquivOfSurjective hι).symm ((K.subschemeι.app (j ''ᵁ ⊤)).hom s) =
      Ideal.Quotient.mk _ s := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, this, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, hψ, Scheme.Hom.appIso_hom']
  rfl

/-- Exchanging the coordinates of a coordinate neighbourhood. -/
private def swapCoordinates {S : Scheme.{v}} {p : S}
    (c : CoordinateNeighbourhood S p) : CoordinateNeighbourhood S p where
  U := c.U
  isAffineOpen := c.isAffineOpen
  mem := c.mem
  isDomain := c.isDomain
  x := c.y
  y := c.x
  span_eq := by rw [Set.pair_comm]; exact c.span_eq

/-- A leading term with respect to `y, x` is obtained by exchanging the variables. -/
private theorem isLeadingTerm_swap {A : Type*} [CommRing A] [IsLocalRing A] {x y f : A}
    {F : MvPolynomial (Fin 2) (IsLocalRing.ResidueField A)} (hF : IsLeadingTerm x y f F) :
    IsLeadingTerm y x f (MvPolynomial.rename (Equiv.swap 0 1) F) := by
  obtain ⟨m, hm, hFm, G, hG, hGF, hfG⟩ := hF
  refine ⟨m, hm, hFm.rename_isHomogeneous, MvPolynomial.rename (Equiv.swap 0 1) G,
    hG.rename_isHomogeneous, ?_, ?_⟩
  · rw [MvPolynomial.map_rename, hGF]
  · convert hfG using 2
    rw [MvPolynomial.eval_rename, show (![y, x] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![x, y] from by
      funext i; fin_cases i <;> rfl]

/-- The evaluation at a closed point of an affine open is surjective. -/
private theorem evaluation_surjective {S : Scheme.{v}} {p : S} (hp : IsClosed ({p} : Set S))
    {U : S.Opens} (hU : IsAffineOpen U) (hpU : p ∈ U) :
    Function.Surjective (S.evaluation U p hpU).hom := by
  let := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨p, hpU⟩ : U)
  have := hU.isLocalization_stalk ⟨p, hpU⟩
  have := hU.primeIdealOf_isMaximal_of_isClosed ⟨p, hpU⟩ hp
  intro k
  obtain ⟨r', hr⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal
    (hU.primeIdealOf ⟨p, hpU⟩).asIdeal (S.presheaf.stalk p)).surjective k
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
  refine ⟨r, ?_⟩
  rw [← hr]
  rfl
/-- **Sections of `C₁ ∩ E` over the chart `D₊(xt)`**: they are `κ[Y]/(F(1, Y))`, by an
isomorphism sending the image of `r ∈ R` to its residue and `y/x` to `Y`. -/
private theorem exists_ringEquiv_chart {S : Scheme.{v}} [IsNoetherian S] {p : S}
    (hp : IsClosed ({p} : Set S)) (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) (c : CoordinateNeighbourhood S p)
    (f : Γ(S, c.U)) (m : ℕ) (hm : mult ((S.presheaf.germ c.U p c.mem).hom f) = m)
    (F : MvPolynomial (Fin 2) (S.residueField p))
    (hF : IsLeadingTerm ((S.presheaf.germ c.U p c.mem).hom c.x)
      ((S.presheaf.germ c.U p c.mem).hom c.y) ((S.presheaf.germ c.U p c.mem).hom f) F)
    (C : S.IdealSheafData) (hC : C.ideal ⟨c.U, c.isAffineOpen⟩ = Ideal.span {f})
    (hx : c.x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩) :
    ∃ ε : Γ((birationalTransform p hp C ⊔
          exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subscheme,
        (birationalTransform p hp C ⊔
          exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subschemeι ⁻¹ᵁ
            (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
              ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1) ≃+*
        Polynomial (S.residueField p) ⧸
          Ideal.span {MvPolynomial.aeval ![(1 : Polynomial (S.residueField p)), Polynomial.X] F},
      (∀ r, ε (((birationalTransform p hp C ⊔
          exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subschemeι.app
            (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
              ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1).hom
          ((blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
              ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).hom r)) =
          Ideal.Quotient.mk _ (Polynomial.C ((S.evaluation c.U p c.mem).hom r))) ∧
      ∀ w, (blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
              ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).hom c.x * w =
            (blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
              ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).hom c.y →
        ε (((birationalTransform p hp C ⊔
          exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subschemeι.app
            (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
              ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1).hom w) =
          Ideal.Quotient.mk _ (Polynomial.X : Polynomial (S.residueField p)) := by
  obtain ⟨hx', e, he⟩ := CoordinateNeighbourhood.exists_iso_spec_adjoin_div hp hreg hdim c
  obtain ⟨-, hφC, hφX⟩ :=
    CoordinateNeighbourhood.comap_exceptionalIdeal_eq_ker_and_exceptionalChartPolynomialEquiv
      hp hreg hdim c hx e he
  let φ := CoordinateNeighbourhood.exceptionalChartPolynomialEquiv hp hreg hdim c
  have hK := CoordinateNeighbourhood.comap_birationalTransform_sup_exceptionalIdeal_eq_ker hp hreg
    hdim c f m hm F hF C hC hx e he φ hφC hφX
  have hjW : (e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι) ''ᵁ ⊤ =
      (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso,
      Scheme.Opens.opensRange_ι]
  have hle : ⊤ ≤ (e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι) ⁻¹ᵁ
      (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1 :=
    fun z _ => (e.inv z).2
  have hqs : Function.Surjective ((Ideal.Quotient.mk (Ideal.span
      {MvPolynomial.aeval ![1, Polynomial.X] F})).comp
      (φ.symm.toRingHom.comp (Ideal.Quotient.mk _))) :=
    Ideal.Quotient.mk_surjective.comp (φ.symm.surjective.comp Ideal.Quotient.mk_surjective)
  obtain ⟨ε, hε⟩ := exists_ringEquiv_of_comap_eq _
      (e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι)
      (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩) hjW hle _ hqs hK
  have hjπ : (e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι) ≫
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, c.U) _)) ≫
      (⟨c.U, c.isAffineOpen⟩ : S.affineOpens).2.fromSpec := by
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]
  have key : blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩
        ⟨c.x, hx⟩ ≫ (e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι).appLE
      (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1 ⊤ hle ≫ (Scheme.ΓSpecIso _).hom =
      CommRingCat.ofHom (algebraMap Γ(S, c.U) _) := by
    have h2 := Stacks.Blowup.appLE_top_of_eq_specMap_fromSpec
      (⟨c.U, c.isAffineOpen⟩ : S.affineOpens) (CommRingCat.ofHom (algebraMap Γ(S, c.U) _)) hjπ
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE, h2, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hR : ∀ r, (Scheme.ΓSpecIso _).hom.hom
      (((e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι).appLE
      (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1 ⊤ hle).hom
      ((blowUpChartMap (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩
        ⟨c.x, hx⟩).hom r)) = algebraMap Γ(S, c.U) _ r := fun r => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]
    rfl
  refine ⟨ε, fun r => ?_, fun w hw => ?_⟩
  · refine (hε _).trans ?_
    refine (congrArg (fun t => (Ideal.Quotient.mk (Ideal.span
      {MvPolynomial.aeval ![1, Polynomial.X] F})) (φ.symm (Ideal.Quotient.mk _ t))) (hR r)).trans ?_
    exact congrArg _ ((RingEquiv.symm_apply_eq φ).mpr (hφC r).symm)
  · refine (hε _).trans ?_
    have hz := congrArg (fun t => (Scheme.ΓSpecIso _).hom.hom
      (((e.inv ≫ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1.ι).appLE
        (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1 ⊤ hle).hom t)) hw
    simp only [map_mul, hR] at hz
    exact congrArg _ ((RingEquiv.symm_apply_eq φ).mpr (hφX _ hz).symm)

/-- The germ of a section `f^♯ r` pulled back along `f` is the image of the germ of `r`. -/
private theorem germ_appLE {X Y : Scheme.{v}} (f : X ⟶ Y) {U : Y.Opens} {W : X.Opens}
    (e : W ≤ f ⁻¹ᵁ U) {z : X} (hz : z ∈ W) (r : Γ(Y, U)) :
    (X.presheaf.germ W z hz).hom ((f.appLE U W e).hom r) =
      f.stalkMap z ((Y.presheaf.germ U (f z) (e hz)).hom r) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  exact (Scheme.Hom.germ_stalkMap_apply f U z (e hz) r).symm

open Stacks.BlowUpChartCover in
/-- **The charts of the blow-up meet.** A point of the standard chart at `a` lies on the
standard chart at `b` as soon as the fraction `b / a` of the affine blow-up algebra avoids its
prime. -/
private theorem mem_chartOpen_chart_of_notMem {X : Scheme.{v}} (I : X.IdealSheafData)
    (V : X.affineOpens) (a b : I.ideal V) (q : PrimeSpectrum (chartRing I V a))
    (hq : affineBlowupAlgebra.fraction (S := Localization.Away (a : Γ(X, V.1)))
        (I.ideal V) (a : Γ(X, V.1)) 1
        ⟨(b : Γ(X, V.1)), by simp⟩ ∉ q.asIdeal) :
    chart I V a q ∈ (chartOpen I V b).1 := by
  let := (reesSituation I).sectionRingGradedRing V.1
  let := (reesSituation I).sectionRingGradingGradedRing V.1
  set z : Spec (.of (HomogeneousLocalization.Away
      ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V a).1)) :=
    Spec.map (CommRingCat.ofHom (reesToAffineBlowupEquiv I V a).toRingHom) q with hzdef
  have hpt : chart I V a q =
      Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V
        (Proj.awayι ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V a).1
          (reesDegreeOne I V a).2 Nat.one_pos z) := by
    conv_lhs => rw [Stacks.Blowup.chart_eq_specMap_awayι I V a]
    rfl
  rw [hpt]
  change Proj.awayι ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V a).1
      (reesDegreeOne I V a).2 Nat.one_pos z ∈
    (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) V ⁻¹ᵁ
      (chartOpen I V b).1)
  rw [preimage_relativeProjChart_chartOpen I V b]
  change z ∈ (Proj.awayι ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V a).1
      (reesDegreeOne I V a).2 Nat.one_pos ⁻¹ᵁ
    Proj.basicOpen ((reesSituation I).sectionRingGrading V.1) (reesDegreeOne I V b).1)
  rw [Proj.awayι_preimage_basicOpen ((reesSituation I).sectionRingGrading V.1)
    (reesDegreeOne I V a).2 Nat.one_pos (reesDegreeOne I V b).2 Nat.one_pos]
  have hlog : HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := (reesSituation I).sectionRingGrading V.1)
        (reesDegreeOne I V a).2 (reesDegreeOne I V b).2 =
      HomogeneousLocalization.Away.mk ((reesSituation I).sectionRingGrading V.1)
        (reesDegreeOne I V a).2 1 (reesDegreeOne I V b).1
          (by simp) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.Away.val_mk, pow_one]
  have heval : reesToAffineBlowupEquiv I V a
      (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := (reesSituation I).sectionRingGrading V.1)
        (reesDegreeOne I V a).2 (reesDegreeOne I V b).2) =
      affineBlowupAlgebra.fraction (S := Localization.Away (a : Γ(X, V.1)))
        (I.ideal V) (a : Γ(X, V.1)) 1 ⟨(b : Γ(X, V.1)), by simp⟩ := by
    rw [hlog, Stacks.Blowup.reesToAffineBlowupEquiv_awayMk I V a 1 (reesDegreeOne I V b).1
      (reesDegreeOne I V b).2]
    exact congrArg (affineBlowupAlgebra.fraction (S := Localization.Away (a : Γ(X, V.1)))
      (I.ideal V) (a : Γ(X, V.1)) 1) (Subtype.ext (reesToBase_degreeOne I V b))
  intro hmem
  exact hq (heval ▸ hmem)

/-- **The overlap of two charts of a blow-up**, read on the chart of `b`: it is the locus where
the transition section `a/b` is invertible. -/
private theorem basicOpen_eq_inf {X : Scheme.{v}} (I : X.IdealSheafData) (V : X.affineOpens)
    (a b : I.ideal V) (w : Γ(blowUp I, (blowUpChartOpen I V b).1))
    (hw : (blowUpChartMap I V b).hom b * w = (blowUpChartMap I V b).hom a) :
    (blowUp I).basicOpen w = (blowUpChartOpen I V a).1 ⊓ (blowUpChartOpen I V b).1 := by
  refine le_antisymm (le_inf ?_ (Scheme.basicOpen_le _ _)) ?_
  · -- the chart of `b` meets the chart of `a` where `a/b` is invertible
    intro z hz
    have hzb : z ∈ (blowUpChartOpen I V b).1 := Scheme.basicOpen_le _ _ hz
    obtain ⟨q, -, rfl⟩ := hzb
    have hq : q ∈ blowUpAffineChart I V b ⁻¹ᵁ (blowUp I).basicOpen w := hz
    have hle : (⊤ : (Spec (CommRingCat.of (blowUpAffineChartRing I V b))).Opens) ≤
        blowUpAffineChart I V b ⁻¹ᵁ (blowUpChartOpen I V b).1 :=
      ((blowUpAffineChart I V b).preimage_image_eq ⊤).ge
    set ρ := (Scheme.ΓSpecIso (CommRingCat.of (blowUpAffineChartRing I V b))).hom.hom
      ((blowUpAffineChart I V b).appLE (blowUpChartOpen I V b).1 ⊤ hle w) with hρ
    have hρ' : (blowUpAffineChart I V b).appLE (blowUpChartOpen I V b).1 ⊤ hle w =
        (Scheme.ΓSpecIso (CommRingCat.of (blowUpAffineChartRing I V b))).inv.hom ρ :=
      ((Scheme.ΓSpecIso (CommRingCat.of (blowUpAffineChartRing I V b))).hom_inv_id_apply _).symm
    have h9 : q ∈ (Spec (CommRingCat.of (blowUpAffineChartRing I V b))).basicOpen
        ((blowUpAffineChart I V b).appLE (blowUpChartOpen I V b).1 ⊤ hle w) := by
      rw [Scheme.basicOpen_appLE]; exact ⟨trivial, hq⟩
    rw [hρ', basicOpen_eq_of_affine] at h9
    have hq' : q ∈ PrimeSpectrum.basicOpen ρ := h9
    have hcomp : blowUpChartMap I V b ≫ (blowUpAffineChart I V b).appLE
        (blowUpChartOpen I V b).1 ⊤ hle ≫ (Scheme.ΓSpecIso _).hom =
        CommRingCat.ofHom (algebraMap Γ(X, V.1) (blowUpAffineChartRing I V b)) := by
      have h2 := Stacks.Blowup.appLE_top_of_eq_specMap_fromSpec
        (f := blowUpAffineChart I V b ≫ blowUpToBase I) V
        (CommRingCat.ofHom (algebraMap Γ(X, V.1) (blowUpAffineChartRing I V b)))
        (by rw [blowUpAffineChart_comp_blowUpToBase, V.2.isoSpec_inv_ι])
      rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE, h2, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    have hfrac : ρ =
        affineBlowupAlgebra.fraction (S := Localization.Away (b : Γ(X, V.1)))
          (I.ideal V) (b : Γ(X, V.1)) 1 ⟨(a : Γ(X, V.1)), by simp⟩ := by
      have hreg := affineBlowup_isRegular (I.ideal V) (b : Γ(X, V.1))
      have hmap : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (blowUpAffineChartRing I V b))).hom.hom
          ((blowUpAffineChart I V b).appLE (blowUpChartOpen I V b).1 ⊤ hle
            ((blowUpChartMap I V b).hom r)) =
          algebraMap Γ(X, V.1) (blowUpAffineChartRing I V b) r := fun r => by
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hcomp]; rfl
      have h1 := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of
        (blowUpAffineChartRing I V b))).hom.hom
          ((blowUpAffineChart I V b).appLE (blowUpChartOpen I V b).1 ⊤ hle t)) hw
      simp only [map_mul, hmap] at h1
      have h2 := affineBlowupAlgebra.algebraMap_pow_mul_fraction
        (S := Localization.Away (b : Γ(X, V.1))) (I.ideal V) (b : Γ(X, V.1)) 1
        ⟨(a : Γ(X, V.1)), by simp⟩
      rw [pow_one] at h2
      exact hreg.1 (h1.trans h2.symm)
    rw [hfrac] at hq'
    have h6 := mem_chartOpen_chart_of_notMem I V b a q hq'
    have h7 : (Stacks.BlowUpChartCover.chartOpen I V a).1 = (blowUpChartOpen I V a).1 :=
      (Scheme.Hom.image_top_eq_opensRange (blowUpAffineChart I V a)).symm
    rw [h7] at h6
    exact h6
  · -- on the overlap, `a` and `b` generate the same ideal of the local ring
    rintro z ⟨hza, hzb⟩
    rw [Scheme.mem_basicOpen _ _ _ hzb]
    set α := (blowUpToBase I).stalkMap z
      ((X.presheaf.germ V.1 (blowUpToBase I z) (blowUpChartOpen_le I V a hza)).hom a)
    set β := (blowUpToBase I).stalkMap z
      ((X.presheaf.germ V.1 (blowUpToBase I z) (blowUpChartOpen_le I V b hzb)).hom b)
    have hαa : ((blowUp I).presheaf.germ _ z hza).hom ((blowUpChartMap I V a).hom a) = α :=
      germ_appLE _ _ _ _
    have hαb : ((blowUp I).presheaf.germ _ z hzb).hom ((blowUpChartMap I V b).hom a) = α :=
      germ_appLE _ _ _ _
    have hβ : ((blowUp I).presheaf.germ _ z hzb).hom ((blowUpChartMap I V b).hom b) = β :=
      germ_appLE _ _ _ _
    have hspan : Ideal.span {α} = Ideal.span {β} := by
      have h1 := IdealSheafData.stalk_eq_map_germ (exceptionalIdeal I) z (blowUpChartOpen I V a)
        hza
      have h2 := IdealSheafData.stalk_eq_map_germ (exceptionalIdeal I) z (blowUpChartOpen I V b)
        hzb
      rw [ideal_exceptionalIdeal_blowUpChartOpen, Ideal.map_span, Set.image_singleton, hαa]
        at h1
      rw [ideal_exceptionalIdeal_blowUpChartOpen, Ideal.map_span, Set.image_singleton, hβ] at h2
      exact h1.symm.trans h2
    have hα0 : α ∈ nonZeroDivisors ((blowUp I).presheaf.stalk z) := by
      letI : Algebra Γ(blowUp I, (blowUpChartOpen I V a).1) ((blowUp I).presheaf.stalk z) :=
        ((blowUp I).presheaf.germ _ z hza).hom.toAlgebra
      haveI := (blowUpChartOpen I V a).2.isLocalization_stalk ⟨z, hza⟩
      rw [← hαa]
      exact IsLocalization.map_nonZeroDivisors_le
        ((blowUpChartOpen I V a).2.primeIdealOf ⟨z, hza⟩).asIdeal.primeCompl _
        ⟨_, blowUpChartMap_self_mem_nonZeroDivisors I V a, rfl⟩
    have hαβ : β * ((blowUp I).presheaf.germ _ z hzb).hom w = α := by
      rw [← hβ, ← map_mul, hw, hαb]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan.ge (Ideal.mem_span_singleton_self β))
    refine isUnit_iff_exists_inv'.mpr ⟨c, ?_⟩
    have h3 : α * (c * ((blowUp I).presheaf.germ _ z hzb).hom w) = α * 1 := by
      rw [mul_one, ← mul_assoc, mul_comm α, hc, hαβ]
    exact (mul_cancel_left_mem_nonZeroDivisors hα0).mp h3

/-- **The exceptional curve lies in the two charts of a coordinate neighbourhood.** -/
private theorem mem_or_mem_of_mem_support {S : Scheme.{v}} {p : S} (hp : IsClosed ({p} : Set S))
    (c : CoordinateNeighbourhood S p)
    (hx : c.x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩)
    (hy : c.y ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩)
    (z : blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))
    (hz : z ∈ (exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support) :
    z ∈ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩
        ⟨c.x, hx⟩).1 ∨
      z ∈ (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
        ⟨c.U, c.isAffineOpen⟩ ⟨c.y, hy⟩).1 := by
  have hzp : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) z = p := by
    have h1 : z ∈ ((Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩))).support := hz
    rw [Scheme.IdealSheafData.support_comap] at h1
    have h2 : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) z ∈
        ((Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).support : Set S) := h1
    have h3 : ((Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).support : Set S) = {p} := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
    rw [h3] at h2
    exact h2
  have hspan : ((Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩ :
      Ideal Γ(S, c.U)) ≤ Ideal.span (Set.range ![c.x, c.y]) := by
    rw [ideal_vanishingIdeal_eq_span hp c]
    exact Ideal.span_mono (by
      rintro w (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)
  obtain ⟨j, w, hw⟩ := exists_mem_range_blowupChartι
    (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩ ![c.x, c.y]
    (fun j => by fin_cases j; exacts [hx, hy]) hspan z (by rw [hzp]; exact c.mem)
  fin_cases j
  · exact Or.inl ⟨w, trivial, hw⟩
  · exact Or.inr ⟨w, trivial, hw⟩

/-- The ring `κ[Y]/(a (Y - r)²)` has exactly one prime ideal. -/
private theorem subsingleton_primeSpectrum_quotient_sq {κ : Type*} [Field κ] {a r : κ}
    (ha : a ≠ 0) :
    Subsingleton (PrimeSpectrum (Polynomial κ ⧸
      Ideal.span {Polynomial.C a * (Polynomial.X - Polynomial.C r) ^ 2})) := by
  set J := Ideal.span {Polynomial.C a * (Polynomial.X - Polynomial.C r) ^ 2}
  have key : ∀ q : PrimeSpectrum (Polynomial κ ⧸ J), ∀ P : Polynomial κ,
      Ideal.Quotient.mk J P ∈ q.asIdeal ↔ P.eval r = 0 := by
    intro q P
    have hY : Ideal.Quotient.mk J (Polynomial.X - Polynomial.C r) ∈ q.asIdeal := by
      have h0 : Ideal.Quotient.mk J (Polynomial.C a * (Polynomial.X - Polynomial.C r) ^ 2) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      have hmem : Ideal.Quotient.mk J (Polynomial.C a) *
          Ideal.Quotient.mk J (Polynomial.X - Polynomial.C r) ^ 2 ∈ q.asIdeal := by
        rw [← map_pow, ← map_mul, h0]; exact q.asIdeal.zero_mem
      rcases q.isPrime.mem_or_mem hmem with h | h
      · exfalso
        apply q.isPrime.ne_top
        rw [Ideal.eq_top_iff_one]
        have : Ideal.Quotient.mk J (Polynomial.C a⁻¹) * Ideal.Quotient.mk J (Polynomial.C a) =
            1 := by
          rw [← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1, map_one]
        rw [← this]
        exact q.asIdeal.mul_mem_left _ h
      · exact q.isPrime.mem_of_pow_mem 2 h
    constructor
    · intro hP
      by_contra hr
      apply q.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      -- `P = P(r) + (Y - r) Q`
      obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := r) (p := P)
      have h1 : Ideal.Quotient.mk J (Polynomial.C (P.eval r)) ∈ q.asIdeal := by
        have : Polynomial.C (P.eval r) = P - (Polynomial.X - Polynomial.C r) * Q := by
          rw [← hQ]; ring
        rw [this, map_sub, map_mul]
        exact q.asIdeal.sub_mem hP (q.asIdeal.mul_mem_right _ hY)
      have : Ideal.Quotient.mk J (Polynomial.C (P.eval r)⁻¹) *
          Ideal.Quotient.mk J (Polynomial.C (P.eval r)) = 1 := by
        rw [← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hr, Polynomial.C_1, map_one]
      rw [← this]
      exact q.asIdeal.mul_mem_left _ h1
    · intro hP
      obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hP
      rw [hQ, map_mul]
      exact q.asIdeal.mul_mem_right _ hY
  refine ⟨fun q₁ q₂ => PrimeSpectrum.ext (Ideal.ext fun z => ?_)⟩
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [key, key]

/-- In `κ[Y]/(P)` with `P(0) ≠ 0`, the class of `Y` is a unit. -/
private theorem isUnit_mk_X_of_coeff_zero_ne_zero {κ : Type*} [Field κ] {P : Polynomial κ}
    (hP : P.coeff 0 ≠ 0) : IsUnit (Ideal.Quotient.mk (Ideal.span {P}) Polynomial.X) := by
  obtain ⟨Q, hQ⟩ : Polynomial.X ∣ P - Polynomial.C (P.coeff 0) := by
    rw [Polynomial.X_dvd_iff]; simp
  refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ (-Polynomial.C (P.coeff 0)⁻¹ * Q)) ?_
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {P})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton]
  refine ⟨-Polynomial.C (P.coeff 0)⁻¹, ?_⟩
  have : Polynomial.X * Q = P - Polynomial.C (P.coeff 0) := hQ.symm
  calc Polynomial.X * (-Polynomial.C (P.coeff 0)⁻¹ * Q) - 1
      = -Polynomial.C (P.coeff 0)⁻¹ * (Polynomial.X * Q) - 1 := by ring
    _ = -Polynomial.C (P.coeff 0)⁻¹ * (P - Polynomial.C (P.coeff 0)) - 1 := by rw [this]
    _ = P * -Polynomial.C (P.coeff 0)⁻¹ + (Polynomial.C ((P.coeff 0)⁻¹ * P.coeff 0) - 1) := by
        rw [Polynomial.C_mul]; ring
    _ = P * -Polynomial.C (P.coeff 0)⁻¹ := by rw [inv_mul_cancel₀ hP, Polynomial.C_1, sub_self,
        add_zero]

/-- An affine open whose ring of sections has a single prime ideal has at most one point. -/
private theorem subsingleton_of_isAffineOpen {Z : Scheme} {U : Z.Opens} (hU : IsAffineOpen U)
    {T : Type*} [CommRing T] (e : Γ(Z, U) ≃+* T) [Subsingleton (PrimeSpectrum T)] :
    (U : Set Z).Subsingleton := by
  intro z₁ hz₁ z₂ hz₂
  have h1 := hU.fromSpec_primeIdealOf ⟨z₁, hz₁⟩
  have h2 := hU.fromSpec_primeIdealOf ⟨z₂, hz₂⟩
  have : hU.primeIdealOf ⟨z₁, hz₁⟩ = hU.primeIdealOf ⟨z₂, hz₂⟩ := by
    have hs : Subsingleton (PrimeSpectrum Γ(Z, U)) := by
      refine ⟨fun p q => ?_⟩
      have := Subsingleton.elim (PrimeSpectrum.comap e.symm.toRingHom p)
        (PrimeSpectrum.comap e.symm.toRingHom q)
      exact PrimeSpectrum.comap_injective_of_surjective _ e.symm.surjective this
    exact Subsingleton.elim _ _
  have := congrArg hU.fromSpec this
  rw [h1, h2] at this
  exact this

/-- **`C₁ ∩ E` for a tangent cone `a (Y - r)²`.** If the leading form `F` of `f` at `p` has
`F(0, 1) ≠ 0` and `F(1, Y) = a (Y - r)²`, the birational transform of `V(f)` meets the exceptional
curve in at most one point. -/
private theorem subsingleton_support_of_aeval_eq_sq {S : Scheme.{v}} [IsNoetherian S] {p : S}
    (hp : IsClosed ({p} : Set S)) (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) (c : CoordinateNeighbourhood S p)
    (f : Γ(S, c.U)) (m : ℕ) (hm : mult ((S.presheaf.germ c.U p c.mem).hom f) = m)
    (F : MvPolynomial (Fin 2) (S.residueField p))
    (hF : IsLeadingTerm ((S.presheaf.germ c.U p c.mem).hom c.x)
      ((S.presheaf.germ c.U p c.mem).hom c.y) ((S.presheaf.germ c.U p c.mem).hom f) F)
    (C : S.IdealSheafData) (hC : C.ideal ⟨c.U, c.isAffineOpen⟩ = Ideal.span {f})
    (h01 : (MvPolynomial.aeval ![(Polynomial.X : Polynomial (S.residueField p)), 1] F).coeff 0 ≠ 0)
    {a r : S.residueField p} (ha : a ≠ 0)
    (hsq : MvPolynomial.aeval ![(1 : Polynomial (S.residueField p)), Polynomial.X] F =
      Polynomial.C a * (Polynomial.X - Polynomial.C r) ^ 2) :
    (SetLike.coe (birationalTransform p hp C ⊔
      exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support).Subsingleton := by
  have hJ := ideal_vanishingIdeal_eq_span hp c
  have hx : c.x ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩ :=
    hJ ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hy : c.y ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).ideal ⟨c.U, c.isAffineOpen⟩ :=
    hJ ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  obtain ⟨ε₁, -, -⟩ := exists_ringEquiv_chart hp hreg hdim c f m hm F hF C hC hx
  obtain ⟨ε₂, -, hε₂X⟩ := exists_ringEquiv_chart hp hreg hdim (swapCoordinates c) f m hm _
    (isLeadingTerm_swap hF) C hC hy
  obtain ⟨w, hw⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow
    (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩ ⟨c.y, hy⟩ (n := 1)
    (x := c.x) (by rwa [pow_one])
  rw [pow_one] at hw
  have hover := basicOpen_eq_inf (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
    ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩ ⟨c.y, hy⟩ w hw.symm
  have hren : MvPolynomial.aeval ![(1 : Polynomial (S.residueField p)), Polynomial.X]
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) F) =
      MvPolynomial.aeval ![(Polynomial.X : Polynomial (S.residueField p)), 1] F := by
    rw [MvPolynomial.aeval_rename, show (![(1 : Polynomial (S.residueField p)), Polynomial.X] ∘
      ⇑(Equiv.swap (0 : Fin 2) 1)) = ![Polynomial.X, 1] from by funext i; fin_cases i <;> rfl]
  have h1 := hε₂X w hw.symm
  have hunit0 : IsUnit (ε₂ (((birationalTransform p hp C ⊔
      exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).subschemeι.app
        (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
          ⟨(swapCoordinates c).U, c.isAffineOpen⟩ ⟨(swapCoordinates c).x, hy⟩).1).hom w)) := by
    rw [h1]
    refine isUnit_mk_X_of_coeff_zero_ne_zero ?_
    convert h01 using 2
    exact congrArg Polynomial.coeff hren
  have hunit := (isUnit_map_iff ε₂ _).mp hunit0
  set Zi := birationalTransform p hp C ⊔
    exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) with hZi
  have hall : ∀ z : Zi.subscheme, z ∈ Zi.subschemeι ⁻¹ᵁ (blowUpChartOpen
      (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1 := by
    intro z
    rcases mem_or_mem_of_mem_support hp c hx hy (Zi.subschemeι z)
      (Scheme.IdealSheafData.support_antitone le_sup_right
        ((Scheme.IdealSheafData.range_subschemeι _).le ⟨z, rfl⟩)) with h | h
    · exact h
    · have hz := (Scheme.basicOpen_of_isUnit _ hunit).ge h
      have hz' : Zi.subschemeι z ∈
          (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).basicOpen w :=
        (Scheme.preimage_basicOpen Zi.subschemeι w).ge hz
      rw [hover] at hz'
      exact hz'.1
  have haff : IsAffineOpen (Zi.subschemeι ⁻¹ᵁ (blowUpChartOpen
      (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩ ⟨c.x, hx⟩).1) :=
    (blowUpChartOpen (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ⟨c.U, c.isAffineOpen⟩
      ⟨c.x, hx⟩).2.preimage _
  have := subsingleton_primeSpectrum_quotient_sq (κ := S.residueField p) (r := r) ha
  have hsub := subsingleton_of_isAffineOpen haff (ε₁.trans (Ideal.quotEquivOfEq
    (show Ideal.span {MvPolynomial.aeval ![(1 : Polynomial (S.residueField p)), Polynomial.X] F} =
      Ideal.span {Polynomial.C a * (Polynomial.X - Polynomial.C r) ^ 2} by rw [hsq])))
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rintro _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩
  exact congrArg _ (hsub (hall z₁) (hall z₂))

section Shear

open IsLocalRing MvPolynomial

/-- **Leading terms under a shear of coordinates.** If `F` is the leading form of `f` with
respect to `x, y`, then `F(X + c̄ Y, Y)` is its leading form with respect to `x - c y, y`. -/
private theorem isLeadingTerm_sub_mul {A : Type*} [CommRing A] [IsLocalRing A] {x y f : A}
    {F : MvPolynomial (Fin 2) (ResidueField A)} (hF : MMP.Resolution.IsLeadingTerm x y f F)
    (c : A) :
    MMP.Resolution.IsLeadingTerm (x - c * y) y f
      (bind₁ ![X 0 + C (residue A c) * X 1, X 1] F) := by
  obtain ⟨m, hm, hFm, G, hG, hGF, hfG⟩ := hF
  have hlin : ∀ (R : Type _) [CommRing R] (d : R) (i : Fin 2),
      (![X 0 + C d * X 1, X 1] i : MvPolynomial (Fin 2) R).IsHomogeneous 1 := by
    intro R _ d i
    fin_cases i
    · exact (isHomogeneous_X R 0).add ((isHomogeneous_C_mul_X d 1))
    · exact isHomogeneous_X R 1
  refine ⟨m, hm, ?_, bind₁ ![X 0 + C c * X 1, X 1] G, ?_, ?_, ?_⟩
  · simpa using hFm.aeval _ (hlin _ (residue A c))
  · simpa using hG.aeval _ (hlin _ c)
  · rw [map_bind₁, ← hGF]
    congr 2
    funext i
    fin_cases i <;> simp
  · have : MvPolynomial.eval ![x - c * y, y] (bind₁ ![X 0 + C c * X 1, X 1] G) =
        MvPolynomial.eval ![x, y] G := by
      rw [MvPolynomial.eval, eval₂Hom_bind₁]
      congr 2
      funext i
      fin_cases i <;> simp
    rw [this]
    exact hfG

/-- `F(X + λ Y, Y)` at `(0, 1)` is `F(λ, 1)`. -/
private theorem eval_aeval_bind₁ {κ : Type*} [Field κ] (F : MvPolynomial (Fin 2) κ) (l : κ) :
    (aeval ![(Polynomial.X : Polynomial κ), 1] (bind₁ ![X 0 + C l * X 1, X 1] F)).coeff 0 =
      MvPolynomial.eval ![l, 1] F := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have : (Polynomial.evalRingHom (0 : κ)).comp
      ((aeval ![(Polynomial.X : Polynomial κ), 1]).toRingHom.comp
        (bind₁ ![X 0 + C l * X 1, X 1]).toRingHom) = MvPolynomial.eval ![l, 1] := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun i => ?_)
    fin_cases i <;> simp
  exact congrArg (fun φ => φ F) this

/-- `F(X, 1) = F(λ, 1)` evaluated at `λ`. -/
private theorem eval_aeval_X_one {κ : Type*} [Field κ] (F : MvPolynomial (Fin 2) κ) (l : κ) :
    (aeval ![(Polynomial.X : Polynomial κ), 1] F).eval l = MvPolynomial.eval ![l, 1] F := by
  have : (Polynomial.evalRingHom l).comp (aeval ![(Polynomial.X : Polynomial κ), 1]).toRingHom =
      MvPolynomial.eval ![l, 1] := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun i => ?_)
    fin_cases i <;> simp
  exact congrArg (fun φ => φ F) this

end Shear

/-- A homogeneous form of degree `d` with coefficients in `𝔪`, evaluated at a point of `𝔪`,
lies in `𝔪^(d+1)`. -/
private theorem eval_mem_pow_succ_of_coeff_mem {A : Type*} [CommRing A] {M : Ideal A}
    {P : MvPolynomial (Fin 2) A} {d : ℕ} (hP : P.IsHomogeneous d)
    (hc : ∀ e, P.coeff e ∈ M) {v : Fin 2 → A} (hv : ∀ i, v i ∈ M) :
    MvPolynomial.eval v P ∈ M ^ (d + 1) := by
  rw [MvPolynomial.eval_eq']
  refine Ideal.sum_mem _ fun e he => ?_
  have hdeg : ∑ i, e i = d := by
    have := hP (MvPolynomial.mem_support_iff.mp he)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    simp
  rw [pow_succ', ← hdeg]
  refine Ideal.mul_mem_mul (hc e) ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hv i) _

/-- `(x - c y, y)` generates the same ideal as `(x, y)`. -/
private theorem span_sub_mul_eq {A : Type*} [CommRing A] (x y c : A) :
    Ideal.span {x - c * y, y} = Ideal.span {x, y} := by
  refine le_antisymm ?_ ?_ <;> rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  · exact ⟨Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert _ _))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))),
      Ideal.subset_span (Set.mem_insert_of_mem _ rfl)⟩
  · refine ⟨?_, Ideal.subset_span (Set.mem_insert_of_mem _ rfl)⟩
    have := Ideal.add_mem _ (Ideal.subset_span (Set.mem_insert (x - c * y) {y}))
      (Ideal.mul_mem_left (Ideal.span {x - c * y, y}) c
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
    rwa [sub_add_cancel] at this

/-- `(γ (y - r₁ x), y - r₂ x)` generates `(x, y)` when `γ` and `r₁ - r₂` are units. -/
private theorem span_mul_sub_eq {A : Type*} [CommRing A] {x y γ r₁ r₂ : A} (hγ : IsUnit γ)
    (hr : IsUnit (r₁ - r₂)) :
    Ideal.span {γ * (y - r₁ * x), y - r₂ * x} = Ideal.span {x, y} := by
  obtain ⟨γ', hγ'⟩ := hγ.exists_left_inv
  obtain ⟨δ, hδ⟩ := hr.exists_left_inv
  refine le_antisymm ?_ ?_ <;> rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  · have hx : x ∈ Ideal.span {x, y} := Ideal.subset_span (Set.mem_insert _ _)
    have hy : y ∈ Ideal.span {x, y} := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    exact ⟨Ideal.mul_mem_left _ _ (Ideal.sub_mem _ hy (Ideal.mul_mem_left _ _ hx)),
      Ideal.sub_mem _ hy (Ideal.mul_mem_left _ _ hx)⟩
  · set J := Ideal.span {γ * (y - r₁ * x), y - r₂ * x}
    have h1 : y - r₁ * x ∈ J := by
      have := Ideal.mul_mem_left J γ' (Ideal.subset_span (Set.mem_insert (γ * (y - r₁ * x)) _))
      rwa [← mul_assoc, hγ', one_mul] at this
    have h2 : y - r₂ * x ∈ J := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hx : x ∈ J := by
      have := Ideal.mul_mem_left J δ (Ideal.sub_mem _ h2 h1)
      have e : δ * ((y - r₂ * x) - (y - r₁ * x)) = x := by
        have : (y - r₂ * x) - (y - r₁ * x) = (r₁ - r₂) * x := by ring
        rw [this, ← mul_assoc, hδ, one_mul]
      rwa [e] at this
    refine ⟨hx, ?_⟩
    have := Ideal.add_mem _ h2 (Ideal.mul_mem_left _ r₂ hx)
    rwa [sub_add_cancel] at this

/-- A quadratic polynomial over an algebraically closed field is a product of linear factors. -/
private theorem exists_eq_C_mul_mul_of_natDegree_eq_two {κ : Type*} [Field κ] [IsAlgClosed κ]
    (P : Polynomial κ) (h : P.natDegree = 2) :
    ∃ γ r₁ r₂ : κ, γ ≠ 0 ∧ P = Polynomial.C γ * ((Polynomial.X - Polynomial.C r₁) *
      (Polynomial.X - Polynomial.C r₂)) := by
  have hroots : P.roots.card = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hP := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [h] at hroots
  obtain ⟨r₁, r₂, hr⟩ := Multiset.card_eq_two.mp hroots
  refine ⟨P.leadingCoeff, r₁, r₂, ?_, ?_⟩
  · intro h0; rw [Polynomial.leadingCoeff_eq_zero] at h0; rw [h0] at h; simp at h
  · rw [← hP, hr]; simp

/-- **The tangent cone of a curve whose birational transform meets `E` twice.** Let `p` be a
closed point of a Noetherian scheme with `𝒪_{S,p}` regular of dimension `2` and algebraically
closed residue field, and `D` a closed subscheme with `I_{D,p} = (φ)`, `mult φ = 2`. If the
birational transform of `D` meets the exceptional curve of the blow-up of `p` in more than one
point, then `φ` is, up to a unit, `u v` modulo `𝔪³` for generators `u, v` of `𝔪`. -/
private theorem exists_span_eq_and_unit_mul_sub_mul_mem_pow_three {S : Scheme.{v}}
    [IsNoetherian S] {p : S} (hp : IsClosed ({p} : Set S))
    (hreg : IsRegularLocalRing (S.presheaf.stalk p))
    (hdim : ringKrullDim (S.presheaf.stalk p) = 2) [IsAlgClosed (S.residueField p)]
    (D : S.IdealSheafData) {φ : S.presheaf.stalk p}
    (hD : IdealSheafData.stalk D p = Ideal.span {φ}) (hφ : mult φ = 2)
    (hns : ¬ (SetLike.coe (birationalTransform p hp D ⊔
      exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).support).Subsingleton) :
    ∃ u v : S.presheaf.stalk p, Ideal.span {u, v} = IsLocalRing.maximalIdeal _ ∧
      ∃ ε : (S.presheaf.stalk p)ˣ, ↑ε * φ - u * v ∈ IsLocalRing.maximalIdeal _ ^ 3 := by
  haveI := hreg
  haveI : IsLocallyNoetherian S := ‹IsNoetherian S›.toIsLocallyNoetherian
  have : IsDomain (S.presheaf.stalk p) := IsRegularLocalRing.isDomain _
  -- `D` is principal on an affine neighbourhood
  obtain ⟨U, hpU, s, hs⟩ : ∃ U : S.affineOpens, p ∈ (U : Set S) ∧
      ∃ s, D.ideal U = Ideal.span {s} := by
    obtain ⟨U, hpU, ⟨s, hs⟩⟩ :=
      Stacks.Divisors.exists_affineOpens_isPrincipal_of_stalk_isPrincipal D p ⟨φ, hD⟩
    exact ⟨U, hpU, s, hs⟩
  have hgs : Ideal.span {(S.presheaf.germ U.1 p hpU).hom s} = Ideal.span {φ} := by
    rw [← hD, IdealSheafData.stalk_eq_map_germ D p U hpU, hs, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨ε₀, hε₀⟩ := Ideal.span_singleton_eq_span_singleton.mp hgs
  have hmults : mult ((S.presheaf.germ U.1 p hpU).hom s) = 2 := by
    unfold mult; rwa [hgs]
  -- a regular system of parameters given by sections over `U`
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (S.presheaf.stalk p)
  have hn : n = 2 := by
    have h := hz.2.symm.trans hdim
    exact_mod_cast h
  subst hn
  letI : Algebra Γ(S, U.1) (S.presheaf.stalk p) := (S.presheaf.germ U.1 p hpU).hom.toAlgebra
  haveI := U.2.isLocalization_stalk ⟨p, hpU⟩
  obtain ⟨⟨a, t⟩, ha⟩ := IsLocalization.mk'_surjective
    (U.2.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl (z 0)
  obtain ⟨⟨b, t'⟩, hb⟩ := IsLocalization.mk'_surjective
    (U.2.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl (z 1)
  have ha' : (S.presheaf.germ U.1 p hpU).hom a =
      z 0 * algebraMap Γ(S, U.1) (S.presheaf.stalk p) t := by
    rw [← ha, IsLocalization.mk'_spec]; rfl
  have hb' : (S.presheaf.germ U.1 p hpU).hom b =
      z 1 * algebraMap Γ(S, U.1) (S.presheaf.stalk p) t' := by
    rw [← hb, IsLocalization.mk'_spec]; rfl
  have hrange : ∀ (w : Fin 2 → S.presheaf.stalk p), Set.range w = {w 0, w 1} := fun w => by
    ext g; simp [Fin.exists_fin_two, eq_comm]
  have hab : Ideal.span {(S.presheaf.germ U.1 p hpU).hom a, (S.presheaf.germ U.1 p hpU).hom b} =
      IsLocalRing.maximalIdeal _ := by
    rw [← hz.1, hrange, ha', hb', Ideal.span_insert, Ideal.span_insert,
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ t),
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ t')]
  -- the leading form with respect to `a, b`
  obtain ⟨⟨F₀, hF₀, -⟩, hF0⟩ := MMP.Resolution.Kollar.existsUnique_isLeadingTerm hdim hab.symm
    (f := (S.presheaf.germ U.1 p hpU).hom s) (by rw [hmults]; exact ENat.coe_ne_top 2)
  have hF₀ne := hF0 F₀ hF₀
  have hF₀h : F₀.IsHomogeneous 2 := by
    obtain ⟨m', hm', hFh, -⟩ := hF₀
    have : (m' : ℕ∞) = 2 := hm'.symm.trans hmults
    rwa [show m' = 2 by exact_mod_cast this] at hFh
  -- a shear making the coefficient of `Y²` nonzero
  have hP : MvPolynomial.aeval
      ![(Polynomial.X : Polynomial (ResidueField (S.presheaf.stalk p))), 1] F₀ ≠ 0 := by
    have hren : MvPolynomial.aeval ![(1 : Polynomial (ResidueField (S.presheaf.stalk p))),
        Polynomial.X] (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) F₀) =
        MvPolynomial.aeval ![(Polynomial.X : Polynomial (ResidueField (S.presheaf.stalk p))), 1]
          F₀ := by
      rw [MvPolynomial.aeval_rename, show (![(1 : Polynomial (ResidueField (S.presheaf.stalk p))),
        Polynomial.X] ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![Polynomial.X, 1] from by
          funext i; fin_cases i <;> rfl]
    rw [← hren]
    refine aeval_one_X_ne_zero hF₀h.rename_isHomogeneous fun h0 => hF₀ne ?_
    exact MvPolynomial.rename_injective _ (Equiv.injective _) (h0.trans (map_zero _).symm)
  haveI : IsAlgClosed (IsLocalRing.ResidueField (S.presheaf.stalk p)) :=
    ‹IsAlgClosed (S.residueField p)›
  have : Infinite (IsLocalRing.ResidueField (S.presheaf.stalk p)) := inferInstance
  obtain ⟨l, hl⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ hP
    (Cardinal.natCast_lt_aleph0.trans_le (Cardinal.aleph0_le_mk _))
  obtain ⟨t₀, ht₀⟩ := evaluation_surjective hp U.2 hpU l
  have hres : IsLocalRing.residue _ ((S.presheaf.germ U.1 p hpU).hom t₀) = l := ht₀
  have hxy : MMP.Mori.IsRegularSystemOfParameters
      ![(S.presheaf.germ U.1 p hpU).hom (a - t₀ * b), (S.presheaf.germ U.1 p hpU).hom b] := by
    refine ⟨?_, by rw [hdim]; rfl⟩
    rw [hrange]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_sub,
      map_mul]
    rw [span_sub_mul_eq, hab]
  obtain ⟨c, hcU, hcx, hcy⟩ :=
    MMP.Resolution.CoordinateNeighbourhood.exists_of_isRegularSystemOfParameters hp hreg hdim hpU
      (a - t₀ * b) b hxy
  have hcU' : (⟨c.U, c.isAffineOpen⟩ : S.affineOpens) ≤ U := hcU
  set f := (S.presheaf.map (homOfLE hcU).op).hom s with hfdef
  have hC : D.ideal ⟨c.U, c.isAffineOpen⟩ = Ideal.span {f} := by
    rw [← D.map_ideal hcU', hs, Ideal.map_span, Set.image_singleton]
    rfl
  have hgerm : ∀ r : Γ(S, U.1), (S.presheaf.germ c.U p c.mem).hom
      ((S.presheaf.map (homOfLE hcU).op).hom r) = (S.presheaf.germ U.1 p hpU).hom r :=
    fun r => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgf : (S.presheaf.germ c.U p c.mem).hom f = (S.presheaf.germ U.1 p hpU).hom s := hgerm s
  have hgx : (S.presheaf.germ c.U p c.mem).hom c.x =
      (S.presheaf.germ U.1 p hpU).hom a - (S.presheaf.germ U.1 p hpU).hom t₀ *
        (S.presheaf.germ U.1 p hpU).hom b := by
    rw [hcx, hgerm, map_sub, map_mul]
  have hgy : (S.presheaf.germ c.U p c.mem).hom c.y = (S.presheaf.germ U.1 p hpU).hom b := by
    rw [hcy, hgerm]
  set F := MvPolynomial.bind₁ (![MvPolynomial.X 0 + MvPolynomial.C
    (IsLocalRing.residue _ ((S.presheaf.germ U.1 p hpU).hom t₀)) * MvPolynomial.X 1,
      MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) _) F₀ with hFdef
  have hF : IsLeadingTerm ((S.presheaf.germ c.U p c.mem).hom c.x)
      ((S.presheaf.germ c.U p c.mem).hom c.y) ((S.presheaf.germ c.U p c.mem).hom f) F := by
    rw [hgx, hgy, hgf]
    exact isLeadingTerm_sub_mul hF₀ _
  have hmultf : mult ((S.presheaf.germ c.U p c.mem).hom f) = (2 : ℕ) := by
    rw [hgf, hmults]; rfl
  have h01 : (MvPolynomial.aeval ![(Polynomial.X : Polynomial
      (IsLocalRing.ResidueField (S.presheaf.stalk p))), 1] F).coeff 0 ≠ 0 := by
    rw [hFdef, eval_aeval_bind₁, hres, ← eval_aeval_X_one]
    exact hl
  -- `F(1, Y)` is a quadratic polynomial with two distinct roots
  obtain ⟨m', hm', hFh, G, hG, hGF, hfG⟩ := hF
  have hm'2 : m' = 2 := by
    have : (m' : ℕ∞) = (2 : ℕ) := hm'.symm.trans hmultf
    exact_mod_cast this
  subst hm'2
  have hdeg : (MvPolynomial.aeval ![(1 : Polynomial
      (IsLocalRing.ResidueField (S.presheaf.stalk p))), Polynomial.X] F).natDegree = 2 := by
    have h2 := coeff_aeval_X_one hFh 0
    rw [if_pos (Nat.zero_le _), Nat.sub_zero] at h2
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ (h2 ▸ h01)
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj =>
      coeff_aeval_one_X_eq_zero hFh (by exact_mod_cast hj)
  obtain ⟨γ, r₁, r₂, hγ, hfac⟩ := exists_eq_C_mul_mul_of_natDegree_eq_two _ hdeg
  have hr : r₁ ≠ r₂ := by
    rintro rfl
    let F' : MvPolynomial (Fin 2) (S.residueField p) := F
    let γ' : S.residueField p := γ
    let r' : S.residueField p := r₁
    have hsq : MvPolynomial.aeval ![(1 : Polynomial (S.residueField p)), Polynomial.X] F' =
        Polynomial.C γ' * (Polynomial.X - Polynomial.C r') ^ 2 := by
      rwa [sq]
    exact hns (subsingleton_support_of_aeval_eq_sq hp hreg hdim c f 2 hmultf F'
      ⟨2, hm', hFh, G, hG, hGF, hfG⟩ D hC h01 hγ hsq)
  -- `F = γ (Y - r₁ X)(Y - r₂ X)`
  set F' : MvPolynomial (Fin 2) (IsLocalRing.ResidueField (S.presheaf.stalk p)) :=
    MvPolynomial.C γ * ((MvPolynomial.X 1 - MvPolynomial.C r₁ * MvPolynomial.X 0) *
      (MvPolynomial.X 1 - MvPolynomial.C r₂ * MvPolynomial.X 0)) with hF'def
  have hlin : ∀ (R : Type _) [CommRing R] (r : R),
      (MvPolynomial.X 1 - MvPolynomial.C r * MvPolynomial.X 0 :
        MvPolynomial (Fin 2) R).IsHomogeneous 1 := fun R _ r =>
    (MvPolynomial.isHomogeneous_X R 1).sub (MvPolynomial.isHomogeneous_C_mul_X r 0)
  have hF'h : F'.IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C _ γ).mul ((hlin _ r₁).mul (hlin _ r₂))
  have hF'eq : MvPolynomial.aeval ![(1 : Polynomial
      (IsLocalRing.ResidueField (S.presheaf.stalk p))), Polynomial.X] F' =
      Polynomial.C γ * ((Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)) := by
    simp [hF'def, Polynomial.C_mul, Polynomial.algebraMap_eq]
  have hFF' : F = F' := by
    by_contra hne
    have := aeval_one_X_ne_zero (hFh.sub hF'h) (sub_ne_zero.mpr hne)
    rw [map_sub, hfac, hF'eq, sub_self] at this
    exact this rfl
  -- lifting to the local ring
  obtain ⟨γt, hγt⟩ := IsLocalRing.residue_surjective γ
  obtain ⟨r₁t, hr₁t⟩ := IsLocalRing.residue_surjective r₁
  obtain ⟨r₂t, hr₂t⟩ := IsLocalRing.residue_surjective r₂
  set H : MvPolynomial (Fin 2) (S.presheaf.stalk p) :=
    MvPolynomial.C γt * ((MvPolynomial.X 1 - MvPolynomial.C r₁t * MvPolynomial.X 0) *
      (MvPolynomial.X 1 - MvPolynomial.C r₂t * MvPolynomial.X 0)) with hHdef
  have hHh : H.IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C _ γt).mul ((hlin _ r₁t).mul (hlin _ r₂t))
  have hHmap : MvPolynomial.map (IsLocalRing.residue _) H = F' := by
    simp [hHdef, hF'def, hγt, hr₁t, hr₂t]
  set gx := (S.presheaf.germ c.U p c.mem).hom c.x
  set gy := (S.presheaf.germ c.U p c.mem).hom c.y
  have hspan : Ideal.span {gx, gy} = IsLocalRing.maximalIdeal (S.presheaf.stalk p) := by
    rw [hgx, hgy, span_sub_mul_eq, hab]
  have hgxm : gx ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk p) :=
    hspan ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hgym : gy ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk p) :=
    hspan ▸ Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hGH : MvPolynomial.eval ![gx, gy] (G - H) ∈
      IsLocalRing.maximalIdeal (S.presheaf.stalk p) ^ (2 + 1) := by
    refine eval_mem_pow_succ_of_coeff_mem (hG.sub hHh) (fun e => ?_) (fun i => ?_)
    · rw [← IsLocalRing.residue_eq_zero_iff, ← MvPolynomial.coeff_map (IsLocalRing.residue _),
        map_sub, hGF, hHmap, hFF', sub_self, MvPolynomial.coeff_zero, Finsupp.zero_apply]
    · fin_cases i
      · exact hgxm
      · exact hgym
  have hevH : MvPolynomial.eval ![gx, gy] H = γt * ((gy - r₁t * gx) * (gy - r₂t * gx)) := by
    simp [hHdef]
  have hunitγ : IsUnit γt := by
    by_contra h
    apply hγ
    rw [← hγt]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hunitr : IsUnit (r₁t - r₂t) := by
    by_contra h
    apply hr
    rw [← hr₁t, ← hr₂t, ← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine ⟨γt * (gy - r₁t * gx), gy - r₂t * gx, ?_, ε₀⁻¹, ?_⟩
  · rw [span_mul_sub_eq hunitγ hunitr, hspan]
  · have he : (↑ε₀⁻¹ : S.presheaf.stalk p) * φ = (S.presheaf.germ c.U p c.mem).hom f := by
      rw [hgf, ← hε₀, mul_comm, mul_assoc, Units.mul_inv, mul_one]
    rw [he]
    have := (IsLocalRing.maximalIdeal (S.presheaf.stalk p) ^ (2 + 1)).add_mem hfG hGH
    rw [map_sub, hevH] at this
    convert this using 1
    ring

end BlowupCharts

/-! ### Curvilinear markings at a point -/

section Markings

open CategoryTheory AlgebraicGeometry

section

open Polynomial

section MarkAlg

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {M : Ideal R} {h w : R}

private theorem span_pair_pow_le (h w : R) (j : ℕ) :
    Ideal.span {h, w} ^ j ≤ Ideal.span {h} ⊔ Ideal.span {w ^ j} := by
  induction j with
  | zero => simp
  | succ j ihj =>
    rw [pow_succ]
    calc Ideal.span {h, w} ^ j * Ideal.span {h, w}
        ≤ (Ideal.span {h} ⊔ Ideal.span {w ^ j}) * Ideal.span {h, w} :=
          Ideal.mul_mono_left ihj
      _ ≤ Ideal.span {h} ⊔ Ideal.span {w ^ (j + 1)} := by
          rw [Ideal.sup_mul, Ideal.span_insert, Ideal.mul_sup, Ideal.mul_sup]
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · exact le_sup_of_le_left Ideal.mul_le_right
          · exact le_sup_of_le_left Ideal.mul_le_left
          · exact le_sup_of_le_left Ideal.mul_le_right
          · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]
            exact le_sup_right

/-- Modulo `(h) + 𝔪 ^ j`, every element is a polynomial in `w`, for `𝔪 = (h, w)` with residue
field `K`. -/
private theorem exists_sub_aeval_mem (hM : Ideal.span {h, w} = M)
    (hres : ∀ g : R, ∃ c : K, g - algebraMap K R c ∈ M) (j : ℕ) (g : R) :
    ∃ P : K[X], g - aeval w P ∈ Ideal.span {h} ⊔ M ^ j := by
  induction j generalizing g with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨P, hP⟩ := ih g
    obtain ⟨a, ha, r, hr, hra⟩ := Submodule.mem_sup.mp hP
    rw [← hM] at hr
    obtain ⟨a', ha', r', hr', hr'a⟩ := Submodule.mem_sup.mp (span_pair_pow_le h w j hr)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hr'
    obtain ⟨c, hc⟩ := hres b
    refine ⟨P + Polynomial.C c * Polynomial.X ^ j, ?_⟩
    have : g - aeval w (P + Polynomial.C c * Polynomial.X ^ j) =
        (a + a') + (b - algebraMap K R c) * w ^ j := by
      rw [map_add, map_mul, aeval_C, map_pow, aeval_X]
      linear_combination -hra - hr'a
    rw [this]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.add_mem _ ha ha')) ?_
    refine Submodule.mem_sup_right ?_
    rw [pow_succ']
    have hw : w ∈ M := by rw [← hM]; exact Ideal.subset_span (by simp)
    exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hw j)

/-- Elements of `(X₀, X₁ ^ (n + 1))` have no monomials `X₁ ^ j`, `j ≤ n`. -/
private theorem coeff_single_one_eq_zero_of_mem {n : ℕ} {f : MvPowerSeries (Fin 2) K}
    (hf : f ∈ Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 1 ^ (n + 1)}) {j : ℕ}
    (hj : j ≤ n) : MvPowerSeries.coeff (Finsupp.single 1 j) f = 0 := by
  rw [Ideal.mem_span_pair] at hf
  obtain ⟨a, b, rfl⟩ := hf
  rw [map_add, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [MvPowerSeries.coeff_X_pow]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg (fun e => e 1) hp
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, h] at this
    omega
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [MvPowerSeries.coeff_X]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg (fun e => e 0) hp
    simp [h] at this

variable (K) in
/-- Evaluation of a polynomial at `X₁`. -/
private theorem coeff_eval₂_X_one (P : K[X]) (j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) j)
      (P.eval₂ MvPowerSeries.C (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = P.coeff j := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.coeff_add]
  | monomial d c =>
    rw [Polynomial.eval₂_monomial, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow,
      Polynomial.coeff_monomial]
    by_cases hd : d = j
    · subst hd; simp
    · rw [if_neg (fun h => hd (Finsupp.single_injective 1 h).symm), if_neg hd,
        mul_zero]

/-- **The kernel of `K[X] → R/(h, w ^ (n + 1))`**, read off a coordinate system
`R → K[[x₀, x₁]]` with `h ↦ x₀`, `w ↦ x₁`. -/
private theorem X_pow_dvd_of_aeval_mem (Q : R →+* MvPowerSeries (Fin 2) K)
    (hQc : ∀ c : K, Q (algebraMap K R c) = MvPowerSeries.C c)
    (hQh : Q h = MvPowerSeries.X 0) (hQw : Q w = MvPowerSeries.X 1) {n : ℕ} {P : K[X]}
    (hP : aeval w P ∈ Ideal.span {h, w ^ (n + 1)}) : Polynomial.X ^ (n + 1) ∣ P := by
  have hmem : Q (aeval w P) ∈ Ideal.span {MvPowerSeries.X 0, MvPowerSeries.X 1 ^ (n + 1)} := by
    have := Ideal.mem_map_of_mem Q hP
    rwa [Ideal.map_span, Set.image_pair, map_pow, hQh, hQw] at this
  have hQP : Q (aeval w P) = P.eval₂ MvPowerSeries.C (MvPowerSeries.X 1) := by
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hQw]
    congr 1
    ext c : 1
    exact hQc c
  rw [Polynomial.X_pow_dvd_iff]
  intro j hj
  rw [hQP] at hmem
  rw [← coeff_eval₂_X_one K P j]
  exact coeff_single_one_eq_zero_of_mem (n := n) (j := j) hmem (by omega)

/-- **A curvilinear quotient.** For `𝔪 = (h, w)` with residue field `K`, and a coordinate system
`h ↦ x₀`, `w ↦ x₁`, the quotient `R/(h, w ^ (n + 1))` is `K[X]/(X ^ (n + 1))`, `w ↦ X`. -/
private theorem exists_ringHom_ker_eq (hM : Ideal.span {h, w} = M)
    (hres : ∀ g : R, ∃ c : K, g - algebraMap K R c ∈ M) (Q : R →+* MvPowerSeries (Fin 2) K)
    (hQc : ∀ c : K, Q (algebraMap K R c) = MvPowerSeries.C c)
    (hQh : Q h = MvPowerSeries.X 0) (hQw : Q w = MvPowerSeries.X 1) (n : ℕ) :
    ∃ φ : R →+* K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}, Function.Surjective φ ∧
      RingHom.ker φ = Ideal.span {h, w ^ (n + 1)} ∧
      (∀ c : K, φ (algebraMap K R c) = algebraMap K _ c) ∧
      φ w = Ideal.Quotient.mk _ Polynomial.X := by
  set 𝔞 := Ideal.span {h, w ^ (n + 1)}
  let ψ : K[X] →+* R ⧸ 𝔞 := (Ideal.Quotient.mk 𝔞).comp (aeval w).toRingHom
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P, hP⟩ := exists_sub_aeval_mem hM hres (n + 1) g
    refine ⟨P, ?_⟩
    change Ideal.Quotient.mk 𝔞 (aeval w P) = _
    rw [Ideal.Quotient.eq]
    have hle : Ideal.span {h} ⊔ M ^ (n + 1) ≤ 𝔞 := by
      rw [← hM]
      refine sup_le ?_ ((span_pair_pow_le h w (n + 1)).trans ?_)
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact Ideal.subset_span (by simp)
      · refine sup_le ?_ ?_ <;> rw [Ideal.span_le, Set.singleton_subset_iff] <;>
          exact Ideal.subset_span (by simp)
    rw [← neg_sub]
    exact neg_mem (hle hP)
  have hker : RingHom.ker ψ = Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)} := by
    ext P
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    change Ideal.Quotient.mk 𝔞 (aeval w P) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · exact X_pow_dvd_of_aeval_mem Q hQc hQh hQw
    · rintro ⟨P', rfl⟩
      rw [map_mul, map_pow, aeval_X]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  let e : (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) ≃+* R ⧸ 𝔞 :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ P : K[X], e (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk 𝔞 (aeval w P) := fun P => rfl
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔞), ?_, ?_, ?_, ?_⟩
  · exact e.symm.surjective.comp Ideal.Quotient.mk_surjective
  · ext g
    simp only [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq, IsScalarTower.algebraMap_apply K K[X] (K[X] ⧸ _) c,
      Ideal.Quotient.algebraMap_eq, ← Polynomial.C_eq_algebraMap, he, aeval_C]
  · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [RingEquiv.symm_apply_eq, he, aeval_X]

end MarkAlg

end

section PointImmersion

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{v}} (p : X) {A : CommRingCat.{v}} [IsLocalRing A]
  (φ : X.presheaf.stalk p ⟶ A) [IsLocalHom φ.hom]

private theorem pointι_closedPoint :
    (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint A) = p := by
  rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

private theorem range_pointι (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A) :
    Set.range (Spec.map φ ≫ X.fromSpecStalk p) = {p} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    rw [hA z, pointι_closedPoint]
    rfl
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨_, pointι_closedPoint x φ⟩

private theorem isClosedImmersion_pointι (hp : IsClosed ({p} : Set X)) (hφ : Function.Surjective φ)
    (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A) :
    IsClosedImmersion (Spec.map φ ≫ X.fromSpecStalk p) := by
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective _ hφ
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [range_pointι p φ hA]
  exact hp

private theorem ker_pointι_ideal (U : X.affineOpens) (hU : p ∈ U.1)
    [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] :
    (Spec.map φ ≫ X.fromSpecStalk p).ker.ideal U =
      Ideal.comap (X.presheaf.germ U.1 p hU).hom (RingHom.ker φ.hom) := by
  rw [Scheme.Hom.ker_apply]
  have hU' : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint A) ∈ U.1 := by
    rwa [pointι_closedPoint]
  have key := Scheme.germ_stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk p) U.1 hU'
  rw [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk] at key
  ext s
  rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.mem_ker]
  have := congrArg (fun g => g.hom s) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [this]
  exact (map_eq_zero_iff _ (ConcreteCategory.injective_of_mono_of_preservesPullback _)).symm

private theorem stalk_ker_pointι [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] :
    IdealSheafData.stalk (Spec.map φ ≫ X.fromSpecStalk p).ker p = RingHom.ker φ.hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  rw [IdealSheafData.stalk_eq_map_germ _ p ⟨U, hU⟩ hpU, ker_pointι_ideal p φ ⟨U, hU⟩ hpU]
  letI := X.presheaf.algebra_section_stalk ⟨p, hpU⟩
  haveI := hU.isLocalization_stalk ⟨p, hpU⟩
  exact IsLocalization.map_comap (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl _ _

private theorem support_ker_pointι (hp : IsClosed ({p} : Set X))
    (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A)
    [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] :
    ((Spec.map φ ≫ X.fromSpecStalk p).ker.support : Set X) = {p} := by
  rw [Scheme.Hom.support_ker, range_pointι p φ hA, hp.closure_eq]

private theorem stalk_ker_pointι_of_ne (hp : IsClosed ({p} : Set X))
    (hA : ∀ z : Spec A, z = IsLocalRing.closedPoint A)
    [QuasiCompact (Spec.map φ ≫ X.fromSpecStalk p)] {x : X} (hx : x ≠ p) :
    IdealSheafData.stalk (Spec.map φ ≫ X.fromSpecStalk p).ker x = ⊤ := by
  rw [Stacks.Divisors.stalk_eq_top_iff_notMem_support]
  intro h
  have : x ∈ ((Spec.map φ ≫ X.fromSpecStalk p).ker.support : Set X) := h
  rw [support_ker_pointι p φ hp hA] at this
  exact hx this

private theorem fromSpecStalk_comp_eq {K : Type v} [Field K] (sX : X ⟶ Spec (.of K)) :
    X.fromSpecStalk p ≫ sX = Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)) := by
  have h1 : sX = X.toSpecΓ ≫ Spec.map sX.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [h1]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp,
    Category.assoc]

private theorem exists_iso_subscheme_ker_pointι {K : Type v} [Field K] (sX : X ⟶ Spec (.of K))
    [Algebra K A] (hφK : ∀ c : K, φ.hom (((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c) = algebraMap K A c)
    [IsClosedImmersion (Spec.map φ ≫ X.fromSpecStalk p)] :
    ∃ e : (Spec.map φ ≫ X.fromSpecStalk p).ker.subscheme ≅ Spec A,
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        (Spec.map φ ≫ X.fromSpecStalk p).ker.subschemeι ≫ sX := by
  set ι := Spec.map φ ≫ X.fromSpecStalk p
  refine ⟨(asIso ι.toImage).symm, ?_⟩
  have h1 : (asIso ι.toImage).symm.hom ≫ ι = ι.ker.subschemeι := by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  have h2 : ι ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap K A)) := by
    change Spec.map φ ≫ X.fromSpecStalk p ≫ sX = _
    rw [fromSpecStalk_comp_eq, ← Spec.map_comp]
    congr 1
    ext c
    exact hφK c
  rw [← h2, ← Category.assoc, h1]

end PointImmersion

section Marking

open Polynomial

set_option backward.isDefEq.respectTransparency false

private theorem eq_closedPoint_of_finite {K : Type v} [Field K] {A : CommRingCat.{v}}
    [IsLocalRing A] [Algebra K A] [Module.Finite K A] (z : Spec A) :
    z = IsLocalRing.closedPoint A := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hz : z.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime z.asIdeal
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hz)

/-- **Curvilinear point markings.** At a closed point `p` with `𝔪_p = (h, w)`, residue field
`K` and a coordinate system `h ↦ x₀`, `w ↦ x₁`, the ideal sheaves `Zₙ` with stalk
`(h, w ^ (n + 1))` at `p` and trivial elsewhere exist, and `Zₙ ≅ Spec K[X]/(X ^ (n + 1))` over
`K`. -/
private theorem exists_marking {K : Type v} [Field K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K))
    (p : X) (hp : IsClosed ({p} : Set X)) {h w : X.presheaf.stalk p}
    (hhw : Ideal.span {h, w} = IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (hres : ∀ g : X.presheaf.stalk p, ∃ c : K, g - ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (Q : X.presheaf.stalk p →+* MvPowerSeries (Fin 2) K)
    (hQc : ∀ c : K, Q (((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c) = MvPowerSeries.C c)
    (hQh : Q h = MvPowerSeries.X 0) (hQw : Q w = MvPowerSeries.X 1) :
    ∃ Z : ℕ → X.IdealSheafData,
      (∀ n, ((Z n).support : Set X) = {p}) ∧
      (∀ n, IdealSheafData.stalk (Z n) p = Ideal.span {h, w ^ (n + 1)}) ∧
      (∀ n x, x ≠ p → IdealSheafData.stalk (Z n) x = ⊤) ∧
      (∀ n, ∃ e : (Z n).subscheme ≅
        Spec (.of (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (Z n).subschemeι ≫ sX) := by
  letI : Algebra K (X.presheaf.stalk p) := ((Scheme.ΓSpecIso (.of K)).inv ≫ sX.appTop ≫
      X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom.toAlgebra
  have hφ : ∀ n : ℕ,
      ∃ φ : X.presheaf.stalk p →+* K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)},
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span {h, w ^ (n + 1)} ∧
      (∀ c : K, φ (algebraMap K _ c) = algebraMap K _ c) ∧
      φ w = Ideal.Quotient.mk _ Polynomial.X :=
    fun n => exists_ringHom_ker_eq hhw hres Q hQc hQh hQw n
  choose φ hsurj hker hK hφw using hφ
  refine ⟨fun n => (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p).ker, ?_⟩
  have hfin : ∀ n : ℕ, Module.Finite K (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) :=
    fun n => (AdjoinRoot.powerBasis' (monic_X_pow (R := K) (n + 1))).finite
  have hloc : ∀ n : ℕ,
      IsLocalRing (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) :=
    fun n => by
      haveI : Nontrivial (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by
          rw [Ne, Ideal.span_singleton_eq_top]
          exact (isUnit_pow_iff (Nat.succ_ne_zero n)).not.mpr Polynomial.not_isUnit_X)
      exact IsLocalRing.of_surjective' (φ n) (hsurj n)
  have hlh : ∀ n, IsLocalHom (φ n) := fun n => IsLocalHom.of_surjective _ (hsurj n)
  have hA : ∀ n (z : Spec (.of (K[X] ⧸ Ideal.span {(Polynomial.X : K[X]) ^ (n + 1)}))),
      z = IsLocalRing.closedPoint _ := fun n z => by
    haveI := hfin n; haveI := hloc n
    exact eq_closedPoint_of_finite (K := K) (A := .of (K[X] ⧸ _)) z
  have hci : ∀ n, IsClosedImmersion (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p) :=
    fun n => by
      haveI := hloc n; haveI := hlh n
      exact isClosedImmersion_pointι p (CommRingCat.ofHom (φ n)) hp (hsurj n) (hA n)
  have hqc : ∀ n, QuasiCompact (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p) :=
    fun n => by
      haveI := hci n
      haveI := IsClosedImmersion.instIsAffineHom
        (Spec.map (CommRingCat.ofHom (φ n)) ≫ X.fromSpecStalk p)
      exact instQuasiCompactOfIsAffineHom _
  refine ⟨fun n => ?_, fun n => ?_, fun n x hx => ?_, fun n => ?_⟩ <;>
    haveI := hloc n <;> haveI := hlh n <;> haveI := hci n <;> haveI := hqc n
  · exact support_ker_pointι p (CommRingCat.ofHom (φ n)) hp (hA n)
  · rw [stalk_ker_pointι p (CommRingCat.ofHom (φ n))]
    exact hker n
  · exact stalk_ker_pointι_of_ne p (CommRingCat.ofHom (φ n)) hp (hA n) hx
  · exact exists_iso_subscheme_ker_pointι p (CommRingCat.ofHom (φ n)) sX (hK n)

end Marking

section MarkingProps

private theorem stalk_sup' {X : Scheme.{v}} (I J : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk (I ⊔ J) x = IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  simp only [IdealSheafData.stalk_eq_map_germ _ x ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, Ideal.map_sup]

/-- The markings are compatible with the thickenings of a curve with local equation `w`. -/
private theorem marking_le_and_eq_sup {X : Scheme.{v}} {p : X} {h w : X.presheaf.stalk p}
    (I : X.IdealSheafData) (hI : IdealSheafData.stalk I p = Ideal.span {w})
    (Z : ℕ → X.IdealSheafData)
    (hZp : ∀ n, IdealSheafData.stalk (Z n) p = Ideal.span {h, w ^ (n + 1)})
    (hZx : ∀ n x, x ≠ p → IdealSheafData.stalk (Z n) x = ⊤) :
    (∀ n, I ^ (n + 1) ≤ Z n) ∧ (∀ n, Z n = Z (n + 1) ⊔ I ^ (n + 1)) := by
  refine ⟨fun n => IdealSheafData.le_of_stalk_le _ _ fun x => ?_,
    fun n => IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_⟩
  · by_cases hx : x = p
    · subst hx
      rw [MMP.Resolution.Aux.stalk_pow, hI, hZp, Ideal.span_singleton_pow, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.subset_span (by simp)
    · rw [hZx n x hx]; exact le_top
  · rw [stalk_sup']
    by_cases hx : x = p
    · subst hx
      rw [MMP.Resolution.Aux.stalk_pow, hI, hZp, hZp, Ideal.span_singleton_pow]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro z (rfl | rfl)
        · exact Ideal.mem_sup_left (Ideal.subset_span (by simp))
        · exact Ideal.mem_sup_right (Ideal.subset_span rfl)
      · refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
        · rintro z (rfl | rfl)
          · exact Ideal.subset_span (by simp)
          · rw [pow_succ w (n + 1)]
            exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
        · rintro z rfl
          exact Ideal.subset_span (by simp)
    · rw [hZx n x hx, hZx (n + 1) x hx, top_sup_eq]

end MarkingProps

section Vanishing

set_option backward.isDefEq.respectTransparency false

private theorem germ_mem_stalk_congr {X : Scheme.{v}} (Z : X.IdealSheafData) {V : X.Opens}
    (a : Γ(X, V)) {q q' : X} (h : q = q') (hq : q ∈ V) (hq' : q' ∈ V) :
    (X.presheaf.germ V q hq).hom a ∈ IdealSheafData.stalk Z q ↔
      (X.presheaf.germ V q' hq').hom a ∈ IdealSheafData.stalk Z q' := by
  subst h; rfl

/-- **Vanishing on a subscheme supported at one point** is membership of the germ in the stalk
of its ideal. -/
private theorem appLE_subschemeι_eq_zero_iff {X : Scheme.{v}} (Z : X.IdealSheafData) {p : X}
    (hZ : (Z.support : Set X) = {p}) {V : X.Opens} (hpV : p ∈ V)
    (hle : ⊤ ≤ Z.subschemeι ⁻¹ᵁ V) (a : Γ(X, V)) :
    (Z.subschemeι.appLE V ⊤ hle).hom a = 0 ↔
      (X.presheaf.germ V p hpV).hom a ∈ IdealSheafData.stalk Z p := by
  have hpt : ∀ t : Z.subscheme, Z.subschemeι t = p := fun t => by
    have : Z.subschemeι t ∈ (Z.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
    rwa [hZ] at this
  have hgerm : ∀ (t : Z.subscheme), Z.subscheme.presheaf.germ ⊤ t trivial
      ((Z.subschemeι.appLE V ⊤ hle).hom a) =
        Z.subschemeι.stalkMap t (X.presheaf.germ V (Z.subschemeι t) (hle trivial) a) := by
    intro t
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE]
    rw [CommRingCat.comp_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hker : ∀ t : Z.subscheme, ∀ b : X.presheaf.stalk (Z.subschemeι t),
      Z.subschemeι.stalkMap t b = 0 ↔ b ∈ IdealSheafData.stalk Z (Z.subschemeι t) := by
    intro t b
    rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk, RingHom.mem_ker]
  obtain ⟨t₀, ht₀⟩ : ∃ t : Z.subscheme, Z.subschemeι t = p := by
    have : p ∈ (Z.support : Set X) := by rw [hZ]; rfl
    rw [← Scheme.IdealSheafData.range_subschemeι] at this
    exact this
  constructor
  · intro h0
    have := hgerm t₀
    rw [h0, map_zero, eq_comm, hker] at this
    exact (germ_mem_stalk_congr Z a ht₀ _ hpV).mp this
  · intro hmem
    refine TopCat.Presheaf.section_ext Z.subscheme.sheaf ⊤ _ _ fun t _ => ?_
    change Z.subscheme.presheaf.germ ⊤ t trivial _ = Z.subscheme.presheaf.germ ⊤ t trivial 0
    rw [map_zero, hgerm, hker]
    exact (germ_mem_stalk_congr Z a (hpt t) _ hpV).mpr hmem

end Vanishing

end Markings

/-! ### The completed boundary ideal, read on markings -/

section BoundaryIdeal

open Scheme.IdealSheafData in
/-- The formal function of a germ `s` at `y` vanishes on a marking `Z` supported at a point `p`
over `y` exactly when the germ of `f^♯ s` at `p` lies in the stalk of `Z`. -/
private theorem appTop_inclusion_completionToFormalNeighborhood_eq_zero_iff
    {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y) (D : X.IdealSheafData) [IsReduced D.subscheme]
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y) {p : X} (hp : f.base p = y)
    (Z : X.IdealSheafData) (hZs : (Z.support : Set X) = {p}) (n : ℕ) (hZ : D ^ (n + 1) ≤ Z)
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)) :
    (inclusion hZ).appTop.hom ((D.completionToFormalNeighborhood f y hmaps
        (algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) (Y.presheaf.germ U y hy s))).1 n) = 0 ↔
      X.presheaf.germ (f ⁻¹ᵁ U) p (show f.base p ∈ U from hp ▸ hy) (f.app U s) ∈
        IdealSheafData.stalk Z p := by
  have hpU : p ∈ f ⁻¹ᵁ U := show f.base p ∈ U from hp ▸ hy
  have hle : (⊤ : Z.subscheme.Opens) ≤ Z.subschemeι ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro t _
    have ht : Z.subschemeι t ∈ (Z.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
    rw [hZs, Set.mem_singleton_iff] at ht
    change f.base (Z.subschemeι t) ∈ U
    rwa [ht, hp]
  rw [← appLE_subschemeι_eq_zero_iff Z hZs hpU hle]
  have h1 : (D.completionToFormalNeighborhood f y hmaps
        (algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
          (Y.presheaf.stalk y)) (Y.presheaf.germ U y hy s))).1 n =
      (((D ^ (n + 1)).subschemeι ≫ f).appLE U ⊤
        (Scheme.Hom.top_le_preimage_of_forall_base_eq _ y (base_thickening_eq D f y hmaps n) U
          hy)).hom s := by
    change (D.completionToFormalNeighborhood f y hmaps (AdicCompletion.of _ _ _)).1 n = _
    rw [completionToFormalNeighborhood_of]
    exact Scheme.Hom.stalkToΓ_germ _ _ _ _ _ _
  have hcomp : inclusion hZ ≫ (D ^ (n + 1)).subschemeι ≫ f = Z.subschemeι ≫ f := by
    rw [← Category.assoc, inclusion_subschemeι]
  have key : ((D ^ (n + 1)).subschemeι ≫ f).appLE U ⊤
        (Scheme.Hom.top_le_preimage_of_forall_base_eq _ y (base_thickening_eq D f y hmaps n) U
          hy) ≫ (inclusion hZ).appTop =
      f.app U ≫ Z.subschemeι.appLE (f ⁻¹ᵁ U) ⊤ hle := by
    rw [← Stacks.FormalFunctions.appLE_top_eq_appTop _
      (Stacks.FormalFunctions.top_le_preimage_top _), Scheme.Hom.appLE_comp_appLE,
      Stacks.FormalFunctions.appLE_congr_hom hcomp, Scheme.Hom.comp_appLE]
    all_goals first | rfl | exact hle
  rw [h1, ← CommRingCat.comp_apply, key]
  rfl

/-- An element of the `I`-adic completion whose image in `R ⧸ I ^ k` vanishes lies in the `k`-th
power of the extended ideal, for `I` finitely generated. -/
private theorem mem_map_pow_of_evalₐ_eq_zero {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    {k : ℕ} {x : AdicCompletion I R} (hx : AdicCompletion.evalₐ I k x = 0) :
    x ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ k := by
  have h0 : AdicCompletion.eval I R k x = 0 := by
    have h' := hx
    simp only [AdicCompletion.evalₐ, AlgHom.comp_apply, AlgHom.ofLinearMap_apply] at h'
    exact (map_eq_zero_iff _ (AlgEquiv.injective _)).mp h'
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval hI] at h0
  rw [← Ideal.map_pow]
  exact Submodule.smul_induction_on h0
    (fun r hr z _ => by
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr))
    (fun z z' hz hz' => Ideal.add_mem _ hz hz')

/-- In a Noetherian local ring, an element of `𝔞 ⊔ 𝔪 ^ N` for every `N` lies in `𝔞`. -/
theorem mem_of_forall_mem_sup_maximalIdeal_pow {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {𝔞 : Ideal A} {t : A} (h : ∀ N : ℕ, t ∈ 𝔞 ⊔ maximalIdeal A ^ N) :
    t ∈ 𝔞 := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (maximalIdeal A) (M := A ⧸ 𝔞)
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))
  have hmem : (Ideal.Quotient.mk 𝔞 t : A ⧸ 𝔞) ∈
      (⨅ i : ℕ, maximalIdeal A ^ i • ⊤ : Submodule A (A ⧸ 𝔞)) := by
    refine Submodule.mem_iInf _ |>.mpr fun N => ?_
    obtain ⟨a, ha, m, hm, hsum⟩ := Submodule.mem_sup.mp (h N)
    have : Ideal.Quotient.mk 𝔞 t = m • (1 : A ⧸ 𝔞) := by
      rw [← hsum, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add,
        ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem_smul hm Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

open Scheme.IdealSheafData in
/-- **The completed boundary ideal, read on markings.** Let `f : X ⟶ Y` carry the reduced curve
`D` to `y`, and let `Z a n` be markings supported at points `p a` over `y`, with
`D ^ (n + 1) ≤ Z a n`. If the germs of `J` pull back into the markings, and conversely a germ
pulling back into the markings of high level lies in `J + 𝔪 ^ N`, then an element of `𝒪̂_{Y,y}`
lies in `J 𝒪̂_{Y,y}` exactly when its formal function vanishes on all the markings. -/
private theorem mem_map_iff_forall_appTop_inclusion_eq_zero
    {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (D : X.IdealSheafData) [IsReduced D.subscheme]
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y) {ι : Type*} (p : ι → X)
    (hp : ∀ a, f.base (p a) = y) (Z : ι → ℕ → X.IdealSheafData)
    (hZs : ∀ a n, ((Z a n).support : Set X) = {p a}) (hZ : ∀ a n, D ^ (n + 1) ≤ Z a n)
    (J : Ideal (Y.presheaf.stalk y))
    (h1 : ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)), Y.presheaf.germ U y hy s ∈ J →
      ∀ a n, X.presheaf.germ (f ⁻¹ᵁ U) (p a) (show f.base (p a) ∈ U from (hp a) ▸ hy)
        (f.app U s) ∈ IdealSheafData.stalk (Z a n) (p a))
    (h3 : ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
      (∀ a, X.presheaf.germ (f ⁻¹ᵁ U) (p a) (show f.base (p a) ∈ U from (hp a) ▸ hy)
        (f.app U s) ∈ IdealSheafData.stalk (Z a n) (p a)) →
      Y.presheaf.germ U y hy s ∈ J ⊔ maximalIdeal (Y.presheaf.stalk y) ^ N)
    (t : 𝒪̂(Y.presheaf.stalk y)) :
    t ∈ Ideal.map (algebraMap (Y.presheaf.stalk y)
        (𝒪̂(Y.presheaf.stalk y))) J ↔
      ∀ a n, (inclusion (hZ a n)).appTop.hom
        ((D.completionToFormalNeighborhood f y hmaps t).1 n) = 0 := by
  have hkey := fun a n U hy s =>
    appTop_inclusion_completionToFormalNeighborhood_eq_zero_iff f y D hmaps (hp a) (Z a n)
      (hZs a n) n (hZ a n) U hy s
  let ev : ∀ a n, 𝒪̂(Y.presheaf.stalk y) →+* Γ((Z a n).subscheme, ⊤) := fun a n =>
    (inclusion (hZ a n)).appTop.hom.comp (((Pi.evalRingHom _ n).comp
      (D.formalNeighborhoodRing).subtype).comp (D.completionToFormalNeighborhood f y hmaps))
  have hev : ∀ a n x, ev a n x = (inclusion (hZ a n)).appTop.hom
      ((D.completionToFormalNeighborhood f y hmaps x).1 n) := fun _ _ _ => rfl
  constructor
  · intro ht a n
    have hle : Ideal.map (algebraMap (Y.presheaf.stalk y) (𝒪̂(Y.presheaf.stalk y))) J ≤
        RingHom.ker (ev a n) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨U, hy, s, rfl⟩ := Y.presheaf.germ_exist g
      rw [Ideal.mem_comap, RingHom.mem_ker, hev]
      exact (hkey a n U hy s).mpr (h1 U hy s hg a n)
    simpa only [RingHom.mem_ker, hev] using hle ht
  · intro ht
    set 𝔞 := Ideal.map (algebraMap (Y.presheaf.stalk y) (𝒪̂(Y.presheaf.stalk y))) J with h𝔞
    have hfg : (maximalIdeal (Y.presheaf.stalk y)).FG := IsNoetherian.noetherian _
    have hN : ∀ N : ℕ, t ∈ 𝔞 ⊔ maximalIdeal (𝒪̂(Y.presheaf.stalk y)) ^ N := by
      intro N
      obtain ⟨n₀, hn₀⟩ := h3 N
      set n := max n₀ N
      obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) t)
      obtain ⟨U, hy, s, rfl⟩ := Y.presheaf.germ_exist g
      have hevₐ : AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)
          (algebraMap (Y.presheaf.stalk y) (𝒪̂(Y.presheaf.stalk y)) (Y.presheaf.germ U y hy s)) =
          AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) t := by
        rw [← hg]; exact AdicCompletion.evalₐ_of _ _ _
      have hcomp : ∀ x x' : 𝒪̂(Y.presheaf.stalk y),
          AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) x =
          AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) x' →
          (D.completionToFormalNeighborhood f y hmaps x).1 n =
            (D.completionToFormalNeighborhood f y hmaps x').1 n := by
        intro x x' h
        change (thickeningToStalkQuotient D f y hmaps n).hom
            (AdicCompletion.evalₐ _ (n + 1) x) =
          (thickeningToStalkQuotient D f y hmaps n).hom (AdicCompletion.evalₐ _ (n + 1) x')
        rw [h]
      have hgerm := hn₀ n (le_max_left _ _) U hy s fun a =>
        (hkey a n U hy s).mp (by rw [hcomp _ _ hevₐ]; exact ht a n)
      have h2 : algebraMap (Y.presheaf.stalk y) (𝒪̂(Y.presheaf.stalk y))
          (Y.presheaf.germ U y hy s) ∈
          𝔞 ⊔ maximalIdeal (𝒪̂(Y.presheaf.stalk y)) ^ N := by
        rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, h𝔞, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hgerm
      have h3' : t - algebraMap (Y.presheaf.stalk y) (𝒪̂(Y.presheaf.stalk y))
          (Y.presheaf.germ U y hy s) ∈ maximalIdeal (𝒪̂(Y.presheaf.stalk y)) ^ N := by
        have h0 : AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)
            (t - algebraMap (Y.presheaf.stalk y) (𝒪̂(Y.presheaf.stalk y))
              (Y.presheaf.germ U y hy s)) = 0 := by
          rw [map_sub, hevₐ, sub_self]
        have := mem_map_pow_of_evalₐ_eq_zero hfg h0
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.pow_le_pow_right (by omega) this
      simpa using (𝔞 ⊔ maximalIdeal (𝒪̂(Y.presheaf.stalk y)) ^ N).add_mem h2
        (Ideal.mem_sup_right h3')
    haveI : IsNoetherianRing (𝒪̂(Y.presheaf.stalk y)) :=
      AdicCompletion.isNoetherianRing (maximalIdeal (Y.presheaf.stalk y))
    exact mem_of_forall_mem_sup_maximalIdeal_pow hN

open Scheme.IdealSheafData in
/-- A ring map `𝒪̂_{Y,y} → Γ((n + 1)D, 𝒪)` extending the pullback of germs is the `n`-th
component of the comparison map to formal functions. -/
private theorem eq_completionToFormalNeighborhood {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y)
    [IsNoetherianRing (Y.presheaf.stalk y)] (D : X.IdealSheafData) [IsReduced D.subscheme]
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y) (n : ℕ)
    (ψ : 𝒪̂(Y.presheaf.stalk y) →+*
      Γ(D.thickening n, ⊤))
    (hψ : ∀ a, ψ (algebraMap _ _ a) = (stalkToThickening D f y hmaps n).hom a)
    (t : 𝒪̂(Y.presheaf.stalk y)) :
    ψ t = (D.completionToFormalNeighborhood f y hmaps t).1 n := by
  let χ : 𝒪̂(Y.presheaf.stalk y) →+*
      Γ(D.thickening n, ⊤) := (Pi.evalRingHom _ n).comp
    (D.formalNeighborhoodRing.subtype.comp (D.completionToFormalNeighborhood f y hmaps))
  have hχ : ∀ a, χ (algebraMap _ _ a) = (stalkToThickening D f y hmaps n).hom a := fun a => by
    change (D.completionToFormalNeighborhood f y hmaps (AdicCompletion.of _ _ a)).1 n = _
    rw [completionToFormalNeighborhood_of]
    rfl
  -- both maps kill `𝔪̂ ^ (n + 1)`, and agree on `𝒪_{Y,y}`, which is dense
  have hker : ∀ φ : 𝒪̂(Y.presheaf.stalk y) →+*
      Γ(D.thickening n, ⊤), (∀ a, φ (algebraMap _ _ a) = (stalkToThickening D f y hmaps n).hom a) →
      (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)).map (algebraMap _ _) ≤ RingHom.ker φ := by
    intro φ hφ
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hφ]
    exact stalkToThickening_eq_zero D f y hmaps n ha
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) t)
  have hev : AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)
      (algebraMap _ _ g) = AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1) t := by
    rw [← hg]; exact AdicCompletion.evalₐ_of _ _ _
  have hd : t - algebraMap _ _ g ∈
      (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)).map (algebraMap _ _) := by
    rw [Ideal.map_pow]
    refine mem_map_pow_of_evalₐ_eq_zero (IsNoetherian.noetherian _) ?_
    rw [map_sub, hev, sub_self]
  have h1 := hker ψ hψ hd
  have h2 := hker χ hχ hd
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  change ψ t = χ t
  rw [h1, h2, hψ, hχ]

end BoundaryIdeal

/-! ### Finite curves over the point -/

section FiniteBoundary

/-- A section lies in the prime of a point of an affine open exactly when its germ there is not a
unit. -/
private theorem mem_primeIdealOf_iff {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (r : Γ(X, U)) :
    r ∈ (hU.primeIdealOf x).asIdeal ↔ (X.presheaf.germ U x x.2).hom r ∈ maximalIdeal _ := by
  letI := X.presheaf.algebra_section_stalk x
  haveI := hU.isLocalization_stalk x
  rw [← IsLocalization.AtPrime.comap_maximalIdeal (X.presheaf.stalk x)
    (hU.primeIdealOf x).asIdeal]
  rfl

private theorem primeIdealOf_injective {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun x x' h => Subtype.ext (by
  rw [← hU.fromSpec_primeIdealOf x, ← hU.fromSpec_primeIdealOf x', h])

private theorem exists_primeIdealOf_eq {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) : ∃ x : U, hU.primeIdealOf x = P := by
  have hx : hU.fromSpec P ∈ (U : Set X) := hU.range_fromSpec ▸ ⟨P, rfl⟩
  refine ⟨⟨_, hx⟩, hU.fromSpec.isOpenEmbedding.injective ?_⟩
  rw [hU.fromSpec_primeIdealOf]

/-- A local homomorphism reflects the maximal ideal. -/
private theorem map_mem_maximalIdeal_iff {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (ψ : A →+* B) [IsLocalHom ψ] (a : A) :
    ψ a ∈ maximalIdeal B ↔ a ∈ maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

/-- The prime of a point of the preimage of an affine open pulls back to the prime of its
image. -/
private theorem comap_app_primeIdealOf {X Y : Scheme.{v}} (g : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U)) (x : g ⁻¹ᵁ U) (hx : g x.1 ∈ U) :
    (hV.primeIdealOf x).asIdeal.comap (g.app U).hom = (hU.primeIdealOf ⟨g x.1, hx⟩).asIdeal := by
  ext r
  rw [Ideal.mem_comap, mem_primeIdealOf_iff, mem_primeIdealOf_iff,
    ← map_mem_maximalIdeal_iff (g.stalkMap x.1).hom ((Y.presheaf.germ U (g x.1) hx).hom r),
    Scheme.Hom.germ_stalkMap_apply]

/-- A function on the base whose pullback lies in `(h, w ^ (n + 1))` at a point of a closed
subscheme `Z` containing `h` lies in the `(n + 1)`-st power of the prime of that point on an affine
open of `Z`. -/
private theorem app_mem_primeIdealOf_pow {X Y : Scheme.{v}} (f : X ⟶ Y) (Z : X.IdealSheafData)
    {U : Y.Opens} (hV : IsAffineOpen ((Z.subschemeι ≫ f) ⁻¹ᵁ U))
    (t : (Z.subschemeι ≫ f) ⁻¹ᵁ U) {q : X} (hq : Z.subschemeι t.1 = q)
    (hmax : (hV.primeIdealOf t).asIdeal.IsMaximal)
    {h w : X.presheaf.stalk q} (hh : h ∈ IdealSheafData.stalk Z q) (hw : w ∈ maximalIdeal _)
    (n : ℕ) (r : Γ(Y, U)) (hfq : f q ∈ U)
    (hr : (f.stalkMap q).hom ((Y.presheaf.germ U (f q) hfq).hom r) ∈
      Ideal.span {h, w ^ (n + 1)}) :
    ((Z.subschemeι ≫ f).app U).hom r ∈ (hV.primeIdealOf t).asIdeal ^ (n + 1) := by
  subst hq
  set 𝔫 := (hV.primeIdealOf t).asIdeal
  letI := Z.subscheme.presheaf.algebra_section_stalk t
  haveI := hV.isLocalization_stalk t
  have hprim : (𝔫 ^ (n + 1)).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by
    rwa [Ideal.radical_pow _ (Nat.succ_ne_zero n), hmax.isPrime.radical])
  have hdisj : Disjoint (𝔫.primeCompl : Set Γ(Z.subscheme, (Z.subschemeι ≫ f) ⁻¹ᵁ U))
      ((𝔫 ^ (n + 1) : Ideal _) : Set Γ(Z.subscheme, (Z.subschemeι ≫ f) ⁻¹ᵁ U)) :=
    Set.disjoint_left.mpr fun x hx hx' => hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hx')
  rw [← IsLocalization.comap_map_of_isPrimary_disjoint 𝔫.primeCompl
    (Z.subscheme.presheaf.stalk t) hprim hdisj, Ideal.map_pow,
    IsLocalization.AtPrime.map_eq_maximalIdeal]
  rw [Ideal.under, Ideal.mem_comap]
  change (Z.subscheme.presheaf.germ _ t t.2).hom (((Z.subschemeι ≫ f).app U).hom r) ∈
    maximalIdeal (Z.subscheme.presheaf.stalk t) ^ (n + 1)
  rw [← Scheme.Hom.germ_stalkMap_apply (Z.subschemeι ≫ f) U t.1 t.2 r, Scheme.Hom.stalkMap_comp]
  change (Z.subschemeι.stalkMap t.1).hom ((f.stalkMap (Z.subschemeι t.1)).hom
    ((Y.presheaf.germ U (f (Z.subschemeι t.1)) hfq).hom r)) ∈
      maximalIdeal (Z.subscheme.presheaf.stalk t) ^ (n + 1)
  have hπh : (Z.subschemeι.stalkMap t).hom h = 0 := by
    rwa [← RingHom.mem_ker, Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
  have hπw : (Z.subschemeι.stalkMap t).hom w ∈ maximalIdeal _ :=
    (map_mem_maximalIdeal_iff _ _).mpr hw
  have := Ideal.mem_map_of_mem (Z.subschemeι.stalkMap t).hom hr
  rw [Ideal.map_span, Set.image_pair, hπh, map_pow] at this
  refine Ideal.span_le.mpr ?_ this
  rintro _ (rfl | rfl)
  · exact zero_mem _
  · exact Ideal.pow_mem_pow hπw _

/-- **Artin–Rees for a finite extension with finitely many points over a maximal ideal.** Let
`φ : R → B` be finite, `R` Noetherian and `𝔮 ⊂ R` maximal, and let `𝔫_a` be the distinct primes of
`B` lying over `𝔮`. If `φ r` lies in `𝔫_a ^ (n + 1)` for every `a`, with `n` large, then `φ r` is
the image of an element of `𝔮 ^ N`. -/
private theorem exists_mem_pow_eq_of_forall_mem_pow {R B : Type*} [CommRing R] [CommRing B]
    [IsNoetherianRing R] (φ : R →+* B) (hφ : φ.Finite) (𝔮 : Ideal R) [h𝔮 : 𝔮.IsMaximal]
    {ι : Type*} [Fintype ι] (𝔫 : ι → Ideal B) [h𝔫p : ∀ a, (𝔫 a).IsPrime]
    (h𝔫 : ∀ a, (𝔫 a).comap φ = 𝔮) (hinj : Function.Injective 𝔫)
    (hall : ∀ P : Ideal B, P.IsPrime → P.comap φ = 𝔮 → ∃ a, 𝔫 a = P) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ r : R, (∀ a, φ r ∈ 𝔫 a ^ (n + 1)) →
      ∃ r' ∈ 𝔮 ^ N, φ r = φ r' := by
  classical
  letI := φ.toAlgebra
  have : Module.Finite R B := hφ
  have : IsNoetherianRing B := isNoetherian_of_tower R inferInstance
  have hmax : ∀ a, (𝔫 a).IsMaximal := fun a =>
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ (by
      change (Ideal.comap φ (𝔫 a)).IsMaximal; rwa [h𝔫 a])
  have hrad : (⨅ a, 𝔫 a) ≤ (𝔮.map φ).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hP, hPp⟩ => ?_
    have hc : P.comap φ = 𝔮 := by
      have h1 : 𝔮 ≤ P.comap φ := Ideal.map_le_iff_le_comap.mp hP
      exact (h𝔮.eq_of_le (Ideal.comap_ne_top φ hPp.ne_top) h1).symm
    obtain ⟨a, rfl⟩ := hall P hPp hc
    exact iInf_le _ a
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨k₀, hk₀⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔮 (R ∙ (1 : B))
  refine ⟨e * (N + k₀), fun n hn r hr => ?_⟩
  have hcop : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun IsCoprime
      fun a => 𝔫 a ^ (n + 1)) := fun a _ b _ hab =>
    (Ideal.isCoprime_iff_sup_eq.mpr ((hmax a).coprime_of_ne (hmax b) (hinj.ne hab))).pow
  have h1 : φ r ∈ ∏ a ∈ Finset.univ, 𝔫 a ^ (n + 1) := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop]
    simp only [Finset.mem_univ, iInf_pos]
    exact Ideal.mem_iInf.mpr hr
  have h2 : (∏ a ∈ Finset.univ, 𝔫 a ^ (n + 1)) ≤ (𝔮 ^ (N + k₀)).map φ := by
    rw [Finset.prod_pow, Ideal.map_pow]
    calc (∏ a ∈ Finset.univ, 𝔫 a) ^ (n + 1) ≤ (⨅ a, 𝔫 a) ^ (n + 1) :=
          Ideal.pow_right_mono (le_iInf fun a =>
            Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ a))) _
      _ ≤ (⨅ a, 𝔫 a) ^ (e * (N + k₀)) := Ideal.pow_le_pow_right (by omega)
      _ = ((⨅ a, 𝔫 a) ^ e) ^ (N + k₀) := pow_mul _ _ _
      _ ≤ (𝔮.map φ) ^ (N + k₀) := Ideal.pow_right_mono he _
  have h3 : φ r ∈ (𝔮 ^ (N + k₀) • ⊤ : Submodule R B) ⊓ (R ∙ (1 : B)) := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.smul_top_eq_map]; exact h2 h1
    · exact Submodule.mem_span_singleton.mpr ⟨r, by rw [Algebra.smul_def, mul_one]; rfl⟩
  rw [hk₀ (N + k₀) (by omega), Nat.add_sub_cancel] at h3
  have h4 : φ r ∈ 𝔮 ^ N • (R ∙ (1 : B)) := Submodule.smul_mono le_rfl inf_le_right h3
  obtain ⟨r', hr', hrr'⟩ := Submodule.mem_smul_span_singleton.mp h4
  refine ⟨r', hr', ?_⟩
  rw [← hrr', Algebra.smul_def, mul_one]
  rfl

/-- **Germs vanishing to high order on a finite curve.** Let `f : X ⟶ Y` carry a closed
subscheme `Z` finitely to `Y`, with points `p a` exactly the points of `Z` over the closed point
`y`. Suppose `h a` lies in the ideal of `Z` at `p a` and `w a ∈ 𝔪_{p a}`, and that a function on
an affine neighbourhood of `y` vanishing on `Z` has germ in `J`. If the germ of `s` at `y` pulls
back into `(h a, w a ^ (n + 1))` at every `p a`, for `n` large, then it lies in `J + 𝔪 ^ N`. -/
private theorem mem_sup_pow_of_forall_mem_span {X Y : Scheme.{v}} (f : X ⟶ Y) (y : Y)
    (hycl : IsClosed ({y} : Set Y)) [IsLocallyNoetherian Y] (Z : X.IdealSheafData)
    [IsFinite (Z.subschemeι ≫ f)] {ι : Type*} [Fintype ι] (p : ι → X)
    (hpinj : Function.Injective p) (hpy : ∀ a, f (p a) = y) (hpZ : ∀ a, p a ∈ Z.support)
    (hall : ∀ z ∈ Z.support, f z = y → ∃ a, p a = z) (h w : ∀ a, X.presheaf.stalk (p a))
    (hh : ∀ a, h a ∈ IdealSheafData.stalk Z (p a)) (hw : ∀ a, w a ∈ maximalIdeal _)
    (J : Ideal (Y.presheaf.stalk y))
    (hker : ∀ (U : Y.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ r : Γ(Y, U),
      ((Z.subschemeι ≫ f).app U).hom r = 0 → (Y.presheaf.germ U y hy).hom r ∈ J) (N : ℕ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
      (∀ a, (X.presheaf.germ (f ⁻¹ᵁ U) (p a) (show f (p a) ∈ U from (hpy a) ▸ hy)).hom
        ((f.app U).hom s) ∈ Ideal.span {h a, w a ^ (n + 1)}) →
      (Y.presheaf.germ U y hy).hom s ∈ J ⊔ maximalIdeal (Y.presheaf.stalk y) ^ N := by
  classical
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  set g := Z.subschemeι ≫ f with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U₀) := hU₀.preimage g
  have hφ : (g.app U₀).hom.Finite := IsFinite.finite_app g U₀ hU₀
  have : IsNoetherianRing Γ(Y, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  set 𝔮 := (hU₀.primeIdealOf ⟨y, hyU₀⟩).asIdeal with h𝔮def
  have h𝔮 : 𝔮.IsMaximal := hU₀.primeIdealOf_isMaximal_of_isClosed ⟨y, hyU₀⟩ hycl
  have ht : ∀ a, ∃ t : g ⁻¹ᵁ U₀, Z.subschemeι t.1 = p a := fun a => by
    obtain ⟨t, ht⟩ : p a ∈ Set.range Z.subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hpZ a
    exact ⟨⟨t, show f (Z.subschemeι t) ∈ U₀ by rwa [ht, hpy a]⟩, ht⟩
  choose t ht using ht
  have hgt : ∀ a, g (t a).1 = y := fun a => by
    change f (Z.subschemeι (t a).1) = y; rw [ht a, hpy a]
  have hcomap : ∀ x : g ⁻¹ᵁ U₀, g x.1 = y →
      (hV.primeIdealOf x).asIdeal.comap (g.app U₀).hom = 𝔮 := fun x hx => by
    rw [comap_app_primeIdealOf g hU₀ hV x (hx ▸ hyU₀)]
    exact congrArg (fun z => (hU₀.primeIdealOf z).asIdeal) (Subtype.ext hx)
  have hιinj : Function.Injective Z.subschemeι := Z.subschemeι.isClosedEmbedding.injective
  have hinj : Function.Injective fun a => (hV.primeIdealOf (t a)).asIdeal := by
    intro a b hab
    have h1 := primeIdealOf_injective hV (PrimeSpectrum.ext hab)
    apply hpinj
    rw [← ht a, ← ht b, h1]
  have hmax : ∀ a, (hV.primeIdealOf (t a)).asIdeal.IsMaximal := by
    intro a
    letI := (g.app U₀).hom.toAlgebra
    haveI : Module.Finite Γ(Y, U₀) Γ(Z.subscheme, g ⁻¹ᵁ U₀) := hφ
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ (by
      change (Ideal.comap (g.app U₀).hom _).IsMaximal
      rwa [hcomap _ (hgt a)])
  have hallP : ∀ P : Ideal Γ(Z.subscheme, g ⁻¹ᵁ U₀), P.IsPrime → P.comap (g.app U₀).hom = 𝔮 →
      ∃ a, (hV.primeIdealOf (t a)).asIdeal = P := by
    intro P hP hPc
    obtain ⟨x, hx⟩ := exists_primeIdealOf_eq hV ⟨P, hP⟩
    have hgx : g x.1 = y := by
      have h1 := comap_app_primeIdealOf g hU₀ hV x x.2
      rw [hx] at h1
      change P.comap _ = _ at h1
      rw [hPc] at h1
      exact congrArg Subtype.val (primeIdealOf_injective hU₀ (PrimeSpectrum.ext h1)).symm
    obtain ⟨a, ha⟩ := hall (Z.subschemeι x.1) (show Z.subschemeι x.1 ∈ (Z.support : Set X) by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x.1, rfl⟩) hgx
    refine ⟨a, ?_⟩
    have : t a = x := Subtype.ext (hιinj ((ht a).trans ha))
    rw [this, hx]
  obtain ⟨n₀, hn₀⟩ := exists_mem_pow_eq_of_forall_mem_pow (g.app U₀).hom hφ 𝔮
    (fun a => (hV.primeIdealOf (t a)).asIdeal) (fun a => hcomap _ (hgt a)) hinj hallP N
  refine ⟨n₀, fun n hn U hy s hs => ?_⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y, hyU₀⟩ : U₀)
  haveI := hU₀.isLocalization_stalk ⟨y, hyU₀⟩
  obtain ⟨⟨r, d⟩, hrd⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl
    ((Y.presheaf.germ U y hy).hom s)
  have hrd' : (Y.presheaf.germ U y hy).hom s * (Y.presheaf.germ U₀ y hyU₀).hom d =
      (Y.presheaf.germ U₀ y hyU₀).hom r := by
    rw [← hrd]; exact IsLocalization.mk'_spec _ r d
  -- the conditions at the points `p a`
  have hθ : ∀ a, (g.app U₀).hom r ∈ (hV.primeIdealOf (t a)).asIdeal ^ (n + 1) := by
    intro a
    have hsp : f (p a) ⤳ y := hpy a ▸ specializes_rfl
    refine app_mem_primeIdealOf_pow f Z hV (t a) (ht a) (hmax a) (hh a) (hw a) n r
      ((hpy a).symm ▸ hyU₀) ?_
    have e : ∀ (V : Y.Opens) (hV : y ∈ V) (σ : Γ(Y, V)),
        (Y.presheaf.germ V (f (p a)) (hsp.mem_open V.isOpen hV)).hom σ =
          (Y.presheaf.stalkSpecializes hsp).hom ((Y.presheaf.germ V y hV).hom σ) :=
      fun V hV σ => (TopCat.Presheaf.germ_stalkSpecializes_apply _ hV hsp σ).symm
    rw [e U₀ hyU₀, ← hrd', map_mul, map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    rw [← e U hy, Scheme.Hom.germ_stalkMap_apply]
    exact hs a
  obtain ⟨r', hr', hrr'⟩ := hn₀ n hn r hθ
  have h0 : ((Z.subschemeι ≫ f).app U₀).hom (r - r') = 0 := by
    rw [map_sub, hrr', sub_self]
  have hJ := hker U₀ hyU₀ hU₀ (r - r') h0
  have hm : (Y.presheaf.germ U₀ y hyU₀).hom r' ∈ maximalIdeal (Y.presheaf.stalk y) ^ N := by
    have hle : Ideal.map (Y.presheaf.germ U₀ y hyU₀).hom 𝔮 ≤ maximalIdeal _ := by
      rw [Ideal.map_le_iff_le_comap]
      intro z hz
      exact (mem_primeIdealOf_iff hU₀ ⟨y, hyU₀⟩ z).mp hz
    have := Ideal.mem_map_of_mem (Y.presheaf.germ U₀ y hyU₀).hom hr'
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle N this
  have hr : (Y.presheaf.germ U₀ y hyU₀).hom r ∈ J ⊔ maximalIdeal (Y.presheaf.stalk y) ^ N := by
    have := Ideal.add_mem _ (Ideal.mem_sup_left hJ) (Ideal.mem_sup_right hm)
    rwa [map_sub, sub_add_cancel] at this
  have hu : IsUnit ((Y.presheaf.germ U₀ y hyU₀).hom (d : Γ(Y, U₀))) :=
    IsLocalization.map_units (Y.presheaf.stalk y) d
  obtain ⟨u, hu⟩ := hu
  have : (Y.presheaf.germ U y hy).hom s =
      (Y.presheaf.germ U₀ y hyU₀).hom r * ↑u⁻¹ := by
    rw [← hrd', ← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hr

/-- **Curvilinear markings transverse to a curve.** At a closed point `p` of a surface over an
algebraically closed field `K`, with `𝔪_p = (h, w)` and `w` a local equation of the ideal sheaf
`I` at `p`, there are ideal sheaves `Zₙ` supported at `p`, with stalk `(h, w ^ (n + 1))` there,
containing `I ^ (n + 1)` and compatible with the thickenings, each `Zₙ ≅ Spec K[X]/(X ^ (n + 1))`
over `K`. -/
private theorem exists_marking_of_span_eq {K : Type v} [Field K] [IsAlgClosed K]
    {X : Scheme.{v}} (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX] [IsLocallyNoetherian X]
    (p : X) (hp : IsClosed ({p} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    (I : X.IdealSheafData) {h w : X.presheaf.stalk p}
    (hI : IdealSheafData.stalk I p = Ideal.span {w})
    (hhw : Ideal.span {h, w} = maximalIdeal (X.presheaf.stalk p)) :
    ∃ (Z : ℕ → X.IdealSheafData) (hZ : ∀ n, I ^ (n + 1) ≤ Z n),
      (∀ n, Z n = Z (n + 1) ⊔ I ^ (n + 1)) ∧ (∀ n, ((Z n).support : Set X) = {p}) ∧
      (∀ n, ∃ e : (Z n).subscheme ≅
        Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (Z n).subschemeι ≫ sX) ∧
      ∀ n, IdealSheafData.stalk (Z n) p = Ideal.span {h, w ^ (n + 1)} := by
  letI := Mori.stalkAlgebra sX p
  set c := algebraMap (X.presheaf.stalk p)
    (𝒪̂(X.presheaf.stalk p)) with hc
  have hz : Ideal.span (Set.range ![c h, c w]) =
      maximalIdeal (𝒪̂(X.presheaf.stalk p)) := by
    have h1 : Ideal.map c (Ideal.span {h, w}) = Ideal.span (Set.range ![c h, c w]) := by
      rw [Ideal.map_span, Set.image_pair]
      congr 1
      ext g
      simp [Fin.exists_fin_two, eq_comm, or_comm]
    rw [AdicCompletion.maximalIdeal_eq_map, ← h1]
    exact congrArg (Ideal.map c) hhw
  obtain ⟨Φ, hΦc, hΦX⟩ := exists_ringEquiv_mvPowerSeries_of_span_eq sX p hp (n := 2)
    (by rw [hdim]; rfl) hz
  have hres : ∀ g : X.presheaf.stalk p, ∃ c' : K, g - ((Scheme.ΓSpecIso (.of K)).inv ≫
      sX.appTop ≫ X.presheaf.germ ⊤ p (TopologicalSpace.Opens.mem_top _)).hom c' ∈
        maximalIdeal (X.presheaf.stalk p) := by
    intro g
    obtain ⟨c', hc'⟩ := MMP.Mori.SurfaceAux.residue_surjective sX p hp (Ideal.Quotient.mk _ g)
    refine ⟨c', Ideal.Quotient.eq.mp ?_⟩
    rw [← hc', IsScalarTower.algebraMap_apply K (X.presheaf.stalk p)
      (X.presheaf.stalk p ⧸ maximalIdeal (X.presheaf.stalk p)), Ideal.Quotient.algebraMap_eq]
    rfl
  obtain ⟨Z, hZs, hZp, hZx, hZe⟩ := exists_marking sX p hp hhw hres (Φ.symm.toRingHom.comp c)
    (fun c' => (RingEquiv.symm_apply_eq Φ).mpr (hΦc c').symm)
    ((RingEquiv.symm_apply_eq Φ).mpr (by rw [hΦX]; rfl))
    ((RingEquiv.symm_apply_eq Φ).mpr (by rw [hΦX]; rfl))
  obtain ⟨hle, hsucc⟩ := marking_le_and_eq_sup I hI Z hZp hZx
  exact ⟨Z, hle, hsucc, hZs, hZe, hZp⟩

end FiniteBoundary

/-! ### Boundary curves and their germs -/

section BoundaryCurves

/-- A germ at a point of a prime divisor lies in the ideal of the divisor exactly when its image at
the generic point of the divisor is not a unit. -/
private theorem germ_mem_stalk_iff {X : Scheme.{v}} (D : Mori.PrimeDivisor X) {x : X}
    (hx : x ∈ D.support) {U : X.Opens} (hU : x ∈ U) (s : Γ(X, U)) :
    (X.presheaf.germ U x hU).hom s ∈ IdealSheafData.stalk D.idealSheaf x ↔
      (X.presheaf.germ U D.genericPoint
        ((show D.genericPoint ⤳ x by
          rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
          exact hx).mem_open U.isOpen hU)).hom s ∈
        maximalIdeal (X.presheaf.stalk D.genericPoint) := by
  have hη : D.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx
  obtain ⟨q, hq, hqE, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support D hx
  have hsp : X.fromSpecStalk x q ⤳ x := MMP.Resolution.specializes_fromSpecStalk x q
  have h1 : IdealSheafData.stalk D.idealSheaf x = MMP.Intersection.primeOfSpecializes hη := by
    rw [hqE, ← MMP.Resolution.primeOfSpecializes_fromSpecStalk x q hsp,
      MMP.Resolution.primeOfSpecializes_congr hq hsp hη]
  rw [h1]
  change (X.presheaf.stalkSpecializes hη).hom ((X.presheaf.germ U x hU).hom s) ∈
    maximalIdeal (X.presheaf.stalk D.genericPoint) ↔ _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- The germ of a pullback `f^♯ s` at `ξ` is a unit exactly when the germ of `s` at `f ξ` is. -/
private theorem germ_app_mem_maximalIdeal_iff {X Y : Scheme.{v}} (f : X ⟶ Y) {ξ : X} {η : Y}
    (hξ : f ξ = η) {U : Y.Opens} (hU : η ∈ U) (s : Γ(Y, U)) :
    (X.presheaf.germ (f ⁻¹ᵁ U) ξ (show f ξ ∈ U from hξ ▸ hU)).hom ((f.app U).hom s) ∈
        maximalIdeal (X.presheaf.stalk ξ) ↔
      (Y.presheaf.germ U η hU).hom s ∈ maximalIdeal (Y.presheaf.stalk η) := by
  subst hξ
  rw [← Scheme.Hom.germ_stalkMap_apply]
  exact map_mem_maximalIdeal_iff (f.stalkMap ξ).hom _

/-- The local intersection number is symmetric. -/
private theorem localIntersectionNumber_comm {K : Type v} [Field K] {X : Scheme.{v}}
    (sX : X ⟶ Spec (.of K)) (q : X) (C C' : Mori.Divisor X) :
    localIntersectionNumber sX q C C' = localIntersectionNumber sX q C' C := by
  simp only [localIntersectionNumber]
  rw [sup_comm]

/-- Prime divisors with local intersection number one at `q` have ideals generating `𝔪_q`. -/
private theorem stalk_sup_eq_maximalIdeal_of_localIntersectionNumber_eq_one {K : Type v}
    [Field K] {X : Scheme.{v}} (sX : X ⟶ Spec (.of K)) (q : X) (C C' : Mori.PrimeDivisor X)
    (h1 : localIntersectionNumber sX q (Finsupp.single C 1) (Finsupp.single C' 1) = 1) :
    IdealSheafData.stalk C.idealSheaf q ⊔ IdealSheafData.stalk C'.idealSheaf q =
      maximalIdeal (X.presheaf.stalk q) := by
  letI := Mori.stalkAlgebra sX q
  have hloc : ∀ E : Mori.PrimeDivisor X,
      localIdeal q (Finsupp.single E 1) = IdealSheafData.stalk E.idealSheaf q := fun E => by
    rw [localIdeal, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.prod_singleton,
      Finsupp.single_eq_same, Int.toNat_one, pow_one]
  rw [localIntersectionNumber, hloc, hloc] at h1
  set J := IdealSheafData.stalk C.idealSheaf q ⊔ IdealSheafData.stalk C'.idealSheaf q
  have hb := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := K)
    (E := X.presheaf.stalk q ⧸ J)).mp h1
  exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField J
    ((RingEquiv.ofBijective _ hb).symm.toMulEquiv.isField (Field.toIsField K)))

/-- A prime divisor with nonzero coefficient in the birational transform of `B` is the transform
of a component of `B`. -/
private theorem exists_mem_support_of_inverseTransformDivisor_ne_zero {X Y : Scheme.{v}}
    (f : X ⟶ Y) (B : QDivisor Y) {D : Mori.PrimeDivisor X}
    (hD : inverseTransformDivisor f B D ≠ 0) :
    ∃ C ∈ B.support, inverseTransformPrimeDivisor f C = some D := by
  classical
  by_contra! h
  apply hD
  conv_lhs => rw [← Finsupp.sum_single B]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun C hC => ?_
  rw [inverseTransformDivisor_single]
  rcases hφ : inverseTransformPrimeDivisor f C with _ | D'
  · rfl
  · have : D' ≠ D := fun he => h C hC (by rw [hφ, he])
    exact Finsupp.single_eq_of_ne' this

/-- **A normal curve through a regular point is cut out by a parameter.** At a point `p` of a
prime divisor `E` with normal subscheme, on a scheme whose local ring at `p` is regular of
dimension two, a local equation `w` of `E` is part of a system of generators `h, w` of `𝔪_p`. -/
private theorem exists_span_pair_eq_maximalIdeal {X : Scheme.{v}} [IsLocallyNoetherian X]
    (E : Mori.PrimeDivisor X) [IsNormal E.idealSheaf.subscheme] {p : X} (hp : p ∈ E.support)
    [IsRegularLocalRing (X.presheaf.stalk p)] (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
    {w : X.presheaf.stalk p} (hw : IdealSheafData.stalk E.idealSheaf p = Ideal.span {w})
    (h0 : IdealSheafData.stalk E.idealSheaf p ≠ ⊥)
    (hm : IdealSheafData.stalk E.idealSheaf p ≠ maximalIdeal (X.presheaf.stalk p)) :
    ∃ h : X.presheaf.stalk p, Ideal.span {h, w} = maximalIdeal (X.presheaf.stalk p) := by
  have hPw : (Ideal.span {w}).IsPrime := hw ▸ isPrime_stalk_idealSheaf E hp
  obtain ⟨t, rfl⟩ : p ∈ Set.range E.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  set π := (E.idealSheaf.subschemeι.stalkMap t).hom with hπ
  have hsurj : Function.Surjective π := E.idealSheaf.subschemeι.stalkMap_surjective t
  have hker : RingHom.ker π = Ideal.span {w} := by
    rw [hπ, Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk, hw]
  have : IsDomain (X.presheaf.stalk (E.idealSheaf.subschemeι t)) :=
    IsRegularLocalRing.isDomain _
  have : IsNoetherianRing (E.idealSheaf.subscheme.presheaf.stalk t) :=
    isNoetherianRing_of_surjective _ _ π hsurj
  have hwm : Ideal.span {w} ≤ maximalIdeal _ := le_maximalIdeal hPw.ne_top
  obtain ⟨a, ha, haw⟩ : ∃ a ∈ maximalIdeal (X.presheaf.stalk (E.idealSheaf.subschemeι t)),
      a ∉ Ideal.span {w} := by
    by_contra! h
    exact hm (hw.trans (le_antisymm hwm h))
  have hπa : π a ≠ 0 := fun h => haw (hker ▸ RingHom.mem_ker.mpr h)
  have hπm : ∀ m, π m ∈ maximalIdeal (E.idealSheaf.subscheme.presheaf.stalk t) ↔
      m ∈ maximalIdeal _ := fun m => map_mem_maximalIdeal_iff π m
  have hnf : ¬ IsField (E.idealSheaf.subscheme.presheaf.stalk t) := by
    intro hF
    letI := hF.toField
    exact (IsLocalRing.mem_maximalIdeal _).mp ((hπm a).mpr ha) (isUnit_iff_ne_zero.mpr hπa)
  have hm2 : (maximalIdeal (X.presheaf.stalk (E.idealSheaf.subschemeι t))).height = 2 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      (R := X.presheaf.stalk (E.idealSheaf.subschemeι t))
    rw [hdim] at h
    exact WithBot.coe_injective (h.trans rfl)
  have hbot : (⊥ : Ideal (X.presheaf.stalk (E.idealSheaf.subschemeι t))).IsPrime :=
    Ideal.isPrime_bot
  have huniq : ∀ P : Ideal (E.idealSheaf.subscheme.presheaf.stalk t), P ≠ ⊥ → P.IsPrime →
      P = maximalIdeal _ := by
    intro P hP0 hPp
    have hQp : (P.comap π).IsPrime := Ideal.IsPrime.comap π
    have hwQ : Ideal.span {w} ≤ P.comap π := by
      rw [← hker]; exact Ideal.comap_mono bot_le
    have hwQ' : Ideal.span {w} ≠ P.comap π := by
      intro h
      apply hP0
      rw [← Ideal.map_comap_of_surjective π hsurj P, ← h, ← hker]
      refine eq_bot_iff.mpr (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
      rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
      exact (⊥ : Ideal _).zero_mem
    have hQm : P.comap π = maximalIdeal _ := by
      by_contra hQm
      have e1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr (hw ▸ h0))
      have e2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hwQ hwQ')
      have e3 := Ideal.height_add_one_le_of_lt_of_isPrime
        (lt_of_le_of_ne (le_maximalIdeal hQp.ne_top) hQm)
      rw [hm2] at e3
      have e1' : (1 : ℕ∞) ≤ (Ideal.span {w}).height := le_trans le_add_self e1
      have e4 : (1 : ℕ∞) + 1 + 1 ≤ 2 :=
        (add_le_add ((add_le_add e1' le_rfl).trans e2) le_rfl).trans e3
      exact absurd e4 (by decide)
    refine le_antisymm (le_maximalIdeal hPp.ne_top) fun b hb => ?_
    obtain ⟨m, rfl⟩ := hsurj b
    have : m ∈ P.comap π := hQm ▸ (hπm m).mp hb
    exact this
  have hP3 : IsIntegrallyClosed (E.idealSheaf.subscheme.presheaf.stalk t) ∧
      ∃! P : Ideal (E.idealSheaf.subscheme.presheaf.stalk t), P ≠ ⊥ ∧ P.IsPrime :=
    ⟨IsNormal.stalk_normal t, ⟨maximalIdeal _,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩,
      fun P hP => huniq P hP.1 hP.2⟩⟩
  have hdvr := ((IsDiscreteValuationRing.TFAE _ hnf).out 4 5).mp hP3
  obtain ⟨b, hb⟩ := hdvr.principal
  obtain ⟨h, rfl⟩ := hsurj b
  refine ⟨h, le_antisymm ?_ fun m hm' => ?_⟩
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨(hπm h).mp ?_, hwm (Ideal.mem_span_singleton_self w)⟩
    rw [hb]; exact Submodule.mem_span_singleton_self _
  · have h1 : π m ∈ Ideal.span {π h} := by
      have := (hπm m).mpr hm'
      rwa [hb] at this
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨c', rfl⟩ := hsurj c
    have h2 : m - c' * h ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
    rw [hker] at h2
    have h4 : Ideal.span {w} ≤ Ideal.span {h, w} := Ideal.span_mono (Set.subset_insert h {w})
    have h5 : h ∈ Ideal.span {h, w} := Ideal.subset_span (Set.mem_insert h {w})
    have h3 := Ideal.add_mem (Ideal.span {h, w}) (Ideal.mul_mem_left _ c' h5) (h4 h2)
    rwa [add_sub_cancel] at h3

end BoundaryCurves

/-! ### The chain of exceptional curves -/

/-- A curve of arithmetic genus zero over an algebraically closed field is a smooth rational
curve. -/
private theorem isSmoothRationalCurve_of_isArithmeticGenusOf_zero {k : Type v} [Field k]
    [IsAlgClosed k] {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) (C : Mori.PrimeDivisor X)
    (hC : IsCurveIn C.idealSheaf) (h0 : IsArithmeticGenusOf sX C 0) :
    IsSmoothRationalCurve sX C.idealSheaf := by
  obtain ⟨hprop, hcoh, hpa⟩ := h0
  have : IsIntegral C.idealSheaf.subscheme := C.integral
  obtain ⟨-, hiff⟩ := MMP.Mori.arithmeticGenus_nonneg_and_eq_zero_iff
    (C.idealSheaf.subschemeι ≫ sX) hC.2
  obtain ⟨eC, heC⟩ := hiff.mp hpa.symm
  exact ⟨⟨hC, hprop, eC.hom, heC, inferInstance, MMP.Mori.isBirationalMorphism_of_isIso _⟩, eC,
    heC⟩

/-- Two distinct prime divisors on a smooth surface, the first proper, with intersection number
`0` are disjoint. -/
private theorem disjoint_support_of_isIntersectionNumber_zero {k : Type v} [Field k]
    {X : Scheme.{v}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] (hX : Mori.IsVariety k sX) (hsm : Mori.IsSmoothScheme sX)
    (hdim : topologicalKrullDim X = 2) {C D : Mori.PrimeDivisor X} (hCD : C ≠ D)
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sX))
    (h0 : IsIntersectionNumber sX (Finsupp.single D 1) C.idealSheaf 0) :
    Disjoint C.support D.support := by
  obtain ⟨hfin, hnum, hpos⟩ :=
    MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne sX hX hsm hdim hCD hC
  have h := hnum.unique h0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hle := Finset.single_le_sum (f := fun w =>
    (localIntersectionNumber sX w (Finsupp.single C 1) (Finsupp.single D 1) : ℚ))
    (fun w _ => by positivity) (hfin.mem_toFinset.mpr hz)
  rw [h] at hle
  have : (0 : ℚ) < localIntersectionNumber sX z (Finsupp.single C 1) (Finsupp.single D 1) := by
    exact_mod_cast hpos z hz
  linarith

/-- **The fibre is the exceptional curve.** For a resolution of a surface germ with connected
fibre over the point and at least one exceptional curve, the fibre is the union of the
exceptional curves: any other point would be an isolated point of the fibre. -/
private theorem preimage_subset_iUnion_support {k : Type v} [Field k]
    {X Y : Scheme.{v}} {sX : X ⟶ Spec (.of k)} {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] (hg : IsGermResolution sX P g) {n : ℕ} (hn : 1 ≤ n)
    {E : Fin n → Mori.PrimeDivisor Y} (hE : IsExceptionalCurveEnumeration g P E)
    (hconn : _root_.IsConnected (g.base ⁻¹' {P})) :
    g.base ⁻¹' {P} ⊆ ⋃ j, ((E j).support : Set Y) := by
  classical
  have hYv := hg.isVariety
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  obtain ⟨hFcl, -⟩ := hg.isClosed_preimage_and_ne_univ
  set U := ⋃ j, ((E j).support : Set Y) with hU
  have hUcl : IsClosed U := isClosed_iUnion_of_finite fun j => (E j).idealSheaf.support.isClosed
  have hUF : U ⊆ g.base ⁻¹' {P} :=
    Set.iUnion_subset fun j => (hE.isGermExceptionalCurve j).1.prop.2
  intro z hz
  by_contra hzU
  obtain ⟨S, hSirr, hS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible ⟨g.base ⁻¹' {P}, hFcl⟩
  have hS' : g.base ⁻¹' {P} = ⋃ (K : TopologicalSpace.Closeds Y) (_ : K ∈ S), (K : Set Y) := by
    have := congrArg (fun K : TopologicalSpace.Closeds Y => (K : Set Y)) hS
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_eq_iSup] at this
    simpa [Set.iSup_eq_iUnion] using this
  -- a component not inside `U` is a closed point
  have hK : ∀ K ∈ S, ¬ (K : Set Y) ⊆ U → ∃ w, IsClosed ({w} : Set Y) ∧ (K : Set Y) = {w} := by
    intro K hKS hKU
    have hKirr : IsIrreducible (K : Set Y) := hSirr ⟨K, hKS⟩
    have hgen := hKirr.isGenericPoint_genericPoint_closure
    rw [K.isClosed.closure_eq] at hgen
    have hKF : (K : Set Y) ⊆ g.base ⁻¹' {P} := by
      rw [hS']
      exact Set.subset_biUnion_of_mem (u := fun K : TopologicalSpace.Closeds Y => (K : Set Y)) hKS
    by_cases hcl : IsClosed ({hKirr.genericPoint} : Set Y)
    · exact ⟨_, hcl, hgen.def.symm.trans hcl.closure_eq⟩
    · exfalso
      obtain ⟨j, hj⟩ := exists_mem_support_of_not_isClosed hg hE (hKF hgen.mem) hcl
      apply hKU
      rw [← hgen.def]
      exact hUcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (Set.mem_iUnion.mpr ⟨j, hj⟩))
  -- every point of the fibre off `U` is a closed point forming a component
  have hoff : ∀ w ∈ g.base ⁻¹' {P}, w ∉ U →
      ∃ K ∈ S, (K : Set Y) = {w} ∧ IsClosed ({w} : Set Y) := by
    intro w hw hwU
    rw [hS'] at hw
    obtain ⟨K, hKS, hwK⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨w', hw'cl, hKw'⟩ := hK K hKS fun h => hwU (h hwK)
    rw [hKw', Set.mem_singleton_iff] at hwK
    subst hwK
    exact ⟨K, hKS, hKw', hw'cl⟩
  obtain ⟨-, -, -, hzcl⟩ := hoff z hz hzU
  set W := U ∪ ⋃ K ∈ S.filter (fun K : TopologicalSpace.Closeds Y => z ∉ (K : Set Y)),
    (K : Set Y) with hW
  have hWcl : IsClosed W :=
    hUcl.union (Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun K _ => K.isClosed)
  have hzW : z ∉ W := by
    rintro (h | h)
    · exact hzU h
    · obtain ⟨K, hK', hzK⟩ := Set.mem_iUnion₂.mp h
      exact (Finset.mem_filter.mp hK').2 hzK
  have hFW : ∀ w ∈ g.base ⁻¹' {P}, w ≠ z → w ∈ W := by
    intro w hw hwz
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · obtain ⟨K, hKS, hKw, -⟩ := hoff w hw hwU
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨K, Finset.mem_filter.mpr ⟨hKS, ?_⟩, ?_⟩)
      · rw [hKw]; exact fun h => hwz (Set.mem_singleton_iff.mp h).symm
      · rw [hKw]; rfl
  rcases isPreconnected_iff_subset_of_disjoint.mp hconn.isPreconnected Wᶜ {z}ᶜ
      hWcl.isOpen_compl hzcl.isOpen_compl
      (fun w hw => by
        by_cases hwz : w = z
        · exact Or.inl (hwz ▸ hzW)
        · exact Or.inr hwz)
      (by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and, not_not]
        intro hw hwW
        by_contra hwz
        exact hwW (hFW w hw hwz)) with h | h
  · have hgen : (E ⟨0, hn⟩).genericPoint ∈ U := by
      refine Set.mem_iUnion.mpr ⟨⟨0, hn⟩, ?_⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    exact h (hUF hgen) (Or.inl hgen)
  · exact h hz rfl

/-- The support of a finite product of ideal sheaves is the union of their supports. -/
private theorem coe_support_prod {X : Scheme.{v}} {ι : Type*} (s : Finset ι)
    (F : ι → X.IdealSheafData) :
    ((∏ i ∈ s, F i).support : Set X) = ⋃ i ∈ s, ((F i).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, ih, Finset.set_biUnion_insert]

/-- On a scheme with regular local rings, the product of the ideal sheaves of distinct prime
divisors is their intersection. -/
private theorem prod_idealSheaf_eq_finsetInf {X : Scheme.{v}} [IsLocallyNoetherian X]
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) {r : ℕ}
    (E : Fin r → Mori.PrimeDivisor X) (hinj : Function.Injective E) :
    ∏ i, (E i).idealSheaf = Finset.univ.inf fun i => (E i).idealSheaf := by
  classical
  refine IdealSheafData.eq_of_stalk_eq _ _ fun x => ?_
  have := hreg x
  have : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  have hπ : ∀ i, ∃ π : X.presheaf.stalk x, IdealSheafData.stalk (E i).idealSheaf x =
      Ideal.span {π} ∧ (x ∈ (E i).support → Prime π) ∧ (x ∉ (E i).support → π = 1) := by
    intro i
    by_cases hx : x ∈ (E i).support
    · obtain ⟨q, -, hq, hq1⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support (E i) hx
      have hq0 : q.asIdeal ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.height_bot] at hq1
        exact zero_ne_one hq1
      obtain ⟨π, hπq, hπ⟩ := q.isPrime.exists_mem_prime_of_ne_bot hq0
      exact ⟨π, hq.trans (Ideal.eq_span_singleton_of_height_eq_one hq1 hπq hπ),
        fun _ => hπ, fun h => absurd hx h⟩
    · exact ⟨1, by rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ hx,
        Ideal.span_singleton_one], fun h => absurd h hx, fun _ => rfl⟩
  choose π hπ using hπ
  set T := Finset.univ.filter fun i => x ∈ (E i).support
  have hprod : ∏ i, π i = ∏ i ∈ T, π i := by
    rw [Finset.prod_filter_of_ne]
    intro i _ hi
    by_contra hx
    exact hi ((hπ i).2.2 hx)
  rw [MMP.Resolution.Aux.stalk_prod, MMP.Intersection.stalk_finsetInf]
  simp_rw [fun i => (hπ i).1]
  rw [Ideal.prod_span_singleton, hprod,
    ← MMP.Intersection.finsetInf_span_singleton_eq_span_prod T π
      (fun i hi => (hπ i).2.1 (Finset.mem_filter.mp hi).2)
      (fun i hi j hj hass => hinj (MMP.Intersection.eq_of_stalk_idealSheaf_eq
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        (by rw [(hπ i).1, (hπ j).1]; exact Ideal.span_singleton_eq_span_singleton.mpr hass)))]
  refine le_antisymm (Finset.le_inf fun i _ => ?_)
    (Finset.le_inf fun i hi => Finset.inf_le (Finset.mem_univ i))
  by_cases hx : x ∈ (E i).support
  · exact Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)
  · rw [(hπ i).2.2 hx, Ideal.span_singleton_one]
    exact le_top

/-- A finite intersection of ideal sheaves of prime divisors is the ideal of the union of their
supports. -/
private theorem finsetInf_idealSheaf_eq_vanishingIdeal {X : Scheme.{v}} {ι : Type*}
    (s : Finset ι) (E : ι → Mori.PrimeDivisor X) :
    (s.inf fun i => (E i).idealSheaf) =
      Scheme.IdealSheafData.vanishingIdeal (s.sup fun i => (E i).idealSheaf.support) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup, ih,
      MMP.Intersection.vanishingIdeal_support_idealSheaf (E a)]

section Cases

variable {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{v}}
  (sY : Y ⟶ Spec (.of K)) (y : Y) (B : QDivisor Y)

/-- **Type (3), empty chain.** The germ is smooth and the boundary is a smooth curve, so
`(𝒪̂_{Y,y}, I_C) ≅ (K[[x, y]], (x))`. -/
private theorem exists_ringEquiv_of_type3_smooth (hS : IsSurfaceGermWithBoundary sY y B)
    {Y' : Scheme.{v}} (f : Y' ⟶ Y) [QuasiCompact (f ≫ sY)] [IsLocallyNoetherian Y']
    [IsNormal Y'] (E : Fin 0 → Mori.PrimeDivisor Y') (hf : IsMinimalGermResolution sY y f)
    (hE : IsExceptionalCurveEnumeration f y E) (C : Mori.PrimeDivisor Y) (hC : B.support = {C})
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk C.idealSheaf y)) :
    letI := Mori.stalkAlgebra sY y
    ∃ Φ : MvPowerSeries (Fin 2) K ≃+*
        𝒪̂(Y.presheaf.stalk y),
      (∀ c : K, Φ (MvPowerSeries.C c) = algebraMap (Y.presheaf.stalk y)
        (𝒪̂(Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) ∧
      Ideal.map Φ (Ideal.span {MvPowerSeries.X 0}) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (𝒪̂(Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) := by
  letI := Mori.stalkAlgebra sY y
  obtain ⟨⟨hXv, hYd, hycl, -⟩, hBy, -⟩ := hS
  have : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_isExceptionalCurveEnumeration_zero hf.1 hE
  have hdim := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hXv.1 hYd y hycl
  have hyC : y ∈ C.support := hBy C (hC ▸ Finset.mem_singleton_self C)
  obtain ⟨h0, hm⟩ := stalk_idealSheaf_ne_bot_and_ne_maximalIdeal hXv.1 hYd C hyC hycl
  obtain ⟨x, hx, hIx⟩ := exists_isRegularSystemOfParameters_span_eq hdim _ hreg h0 hm
  obtain ⟨Φ, hc, hX⟩ := exists_ringEquiv_mvPowerSeries_of_isRegularSystemOfParameters sY y hycl hx
  refine ⟨Φ, hc, ?_⟩
  rw [hC, Finset.iInf_singleton, hIx, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton, hX]

/-- **Type (9), empty chain.** The germ is smooth and the boundary is a node, so
`(𝒪̂_{Y,y}, I_C) ≅ (K[[x, y]], (xy))`. -/
private theorem exists_ringEquiv_of_type9_smooth (hS : IsSurfaceGermWithBoundary sY y B)
    (hB : IsReducedBoundary B)
    {Y' : Scheme.{v}} (f : Y' ⟶ Y) [QuasiCompact (f ≫ sY)] [IsLocallyNoetherian Y']
    [IsNormal Y'] (E : Fin 0 → Mori.PrimeDivisor Y') (hf : IsMinimalGermResolution sY y f)
    (hE : IsExceptionalCurveEnumeration f y E) (hP : IsClosed ({y} : Set Y))
    (mu : Mori.PrimeDivisor Y → ℕ)
    (hmu : ∀ C ∈ B.support, MMP.Resolution.multAt C.idealSheaf y = mu C)
    (hsum : ∑ C ∈ B.support, B C * mu C = 2)
    (hcard : ((⋃ C ∈ B.support,
            SetLike.coe (MMP.Resolution.birationalTransform y hP C.idealSheaf).support) ∩
          SetLike.coe (exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hP⟩)).support).ncard = 2) :
    letI := Mori.stalkAlgebra sY y
    ∃ Φ : MvPowerSeries (Fin 2) K ≃+*
        𝒪̂(Y.presheaf.stalk y),
      (∀ c : K, Φ (MvPowerSeries.C c) = algebraMap (Y.presheaf.stalk y)
        (𝒪̂(Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) ∧
      Ideal.map Φ (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (𝒪̂(Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) := by
  letI := Mori.stalkAlgebra sY y
  obtain ⟨⟨hXv, hYd, hycl, -⟩, hBy, -⟩ := hS
  have : LocallyOfFiniteType sY := hXv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : QuasiCompact sY := hXv.1.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  have hreg : IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_isExceptionalCurveEnumeration_zero hf.1 hE
  have hdim := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two sY hXv.1 hYd y hycl
  have hκ : IsAlgClosed (Y.residueField y) := by
    have hs := MMP.Mori.SurfaceAux.residue_surjective sY y hycl
    let e : K →+* IsLocalRing.ResidueField (Y.presheaf.stalk y) :=
      (IsLocalRing.residue (Y.presheaf.stalk y)).comp (algebraMap K (Y.presheaf.stalk y))
    exact IsAlgClosed.of_ringEquiv K (IsLocalRing.ResidueField (Y.presheaf.stalk y))
      (RingEquiv.ofBijective e ⟨e.injective, hs⟩)
  -- the local equation of the boundary
  have hsum' : ∑ C ∈ B.support, mu C = 2 := by
    have : ∑ C ∈ B.support, B C * (mu C : ℚ) = ∑ C ∈ B.support, (mu C : ℚ) :=
      Finset.sum_congr rfl fun C hC => by rw [hB C hC, one_mul]
    rw [this] at hsum
    exact_mod_cast hsum
  obtain ⟨φ, hφ, hmφ⟩ := exists_stalk_iInf_eq_span hXv.1 hYd hycl B.support hBy mu hmu
  rw [hsum'] at hmφ
  -- the birational transform meets the exceptional curve in two points
  have hns : ¬ (SetLike.coe (MMP.Resolution.birationalTransform y hP
      (⨅ C ∈ B.support, C.idealSheaf) ⊔ exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hP⟩)).support).Subsingleton := by
    intro hsub
    have hA : ((⋃ C ∈ B.support,
        SetLike.coe (MMP.Resolution.birationalTransform y hP C.idealSheaf).support) ∩
          SetLike.coe (exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hP⟩)).support) ⊆
        SetLike.coe (MMP.Resolution.birationalTransform y hP
          (⨅ C ∈ B.support, C.idealSheaf) ⊔ exceptionalIdeal
            (Scheme.IdealSheafData.vanishingIdeal ⟨{y}, hP⟩)).support := by
      rintro z ⟨hz1, hz2⟩
      simp only [Set.mem_iUnion] at hz1
      obtain ⟨C, hC, hzC⟩ := hz1
      rw [Scheme.IdealSheafData.support_sup]
      exact ⟨Scheme.IdealSheafData.support_antitone (birationalTransform_mono y hP
        (biInf_le (fun C : Mori.PrimeDivisor Y => C.idealSheaf) hC)) hzC, hz2⟩
    have hss := hsub.anti hA
    have : Finite _ := hss.finite.to_subtype
    have := (Set.ncard_le_one_iff_subsingleton).mpr hss
    omega
  obtain ⟨u, v, huv, ε, hε⟩ :=
    exists_span_eq_and_unit_mul_sub_mul_mem_pow_three hP hreg hdim _ hφ hmφ hns
  -- the formal coordinates
  have hmhat : maximalIdeal (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y)) = Ideal.map (algebraMap (Y.presheaf.stalk y) _)
        (maximalIdeal (Y.presheaf.stalk y)) := AdicCompletion.maximalIdeal_eq_map
  have hrange : ∀ {T : Type v} (w : Fin 2 → T), Set.range w = {w 0, w 1} := fun w => by
    ext g; simp [Fin.exists_fin_two, eq_comm]
  have hz : Ideal.span (Set.range ![algebraMap (Y.presheaf.stalk y)
      (𝒪̂(Y.presheaf.stalk y)) u,
      algebraMap _ _ v]) = maximalIdeal _ := by
    rw [hmhat, ← huv, Ideal.map_span, Set.image_pair, hrange]
    rfl
  obtain ⟨Φ, -, hΦX⟩ := exists_ringEquiv_mvPowerSeries_of_span_eq sY y hycl (n := 2) hdim hz
  have hMmax : maximalIdeal (MvPowerSeries (Fin 2) K) =
      Ideal.span (Set.range MvPowerSeries.X) := maximalIdeal_mvPowerSeries_eq_span_X K 2
  have hΦM : Ideal.map Φ (Ideal.span (Set.range (MvPowerSeries.X (R := K)))) =
      maximalIdeal _ := by
    rw [← hMmax]; exact IsLocalRing.map_ringEquiv_maximalIdeal Φ
  have hXX : Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1} =
      Ideal.span (Set.range MvPowerSeries.X) := by
    rw [hrange]
  have hg : Φ.symm (algebraMap (Y.presheaf.stalk y) _ (ε * φ)) -
      MvPowerSeries.X 0 * MvPowerSeries.X 1 ∈
        Ideal.span (Set.range (MvPowerSeries.X (R := K))) ^ 3 := by
    have h1 : Φ (Φ.symm (algebraMap (Y.presheaf.stalk y) _ (ε * φ)) -
        MvPowerSeries.X 0 * MvPowerSeries.X 1) =
        algebraMap (Y.presheaf.stalk y) _ (ε * φ - u * v) := by
      rw [map_sub, RingEquiv.apply_symm_apply, map_mul Φ, hΦX, hΦX]
      simp [map_sub, map_mul]
    have h2 : algebraMap (Y.presheaf.stalk y) (AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (Y.presheaf.stalk y)) (ε * φ - u * v) ∈ Ideal.map Φ
          (Ideal.span (Set.range (MvPowerSeries.X (R := K))) ^ 3) := by
      rw [Ideal.map_pow, hΦM, hmhat, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hε
    rw [← h1, Ideal.mem_map_of_equiv] at h2
    obtain ⟨w, hw, hwe⟩ := h2
    rwa [← Φ.injective hwe]
  have hfg : (Ideal.span (Set.range (MvPowerSeries.X (R := K) (σ := Fin 2)))).FG :=
    Submodule.fg_span (Set.finite_range _)
  obtain ⟨a, b, ha, hb, hgab⟩ := exists_eq_mul_of_sub_mul_mem_pow_three hfg hXX hg
  have hz' : Ideal.span (Set.range ![Φ (MvPowerSeries.X 0 + a), Φ (MvPowerSeries.X 1 + b)]) =
      maximalIdeal _ := by
    have hjac : Ideal.span (Set.range (MvPowerSeries.X (R := K) (σ := Fin 2))) ≤
        (⊥ : Ideal (MvPowerSeries (Fin 2) K)).jacobson := by
      rw [← hMmax]; exact IsLocalRing.maximalIdeal_le_jacobson _
    rw [← hΦM, ← span_pair_add_eq hfg hjac hXX ha hb, Ideal.map_span, Set.image_pair, hrange]
    rfl
  obtain ⟨Φ', hΦ'c, hΦ'X⟩ := exists_ringEquiv_mvPowerSeries_of_span_eq sY y hycl (n := 2) hdim hz'
  refine ⟨Φ', hΦ'c, ?_⟩
  rw [Ideal.map_span, Set.image_singleton, map_mul, hΦ'X, hΦ'X]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← map_mul, ← hgab, RingEquiv.apply_symm_apply, hφ, Ideal.map_span, Set.image_singleton,
    map_mul, Ideal.span_singleton_mul_left_unit ((ε.isUnit).map _)]

/-- **Types (3) and (9), nonempty chain.** The completed germ is the cyclic quotient
`K[[x, y]]^{μ_m}` given by the formal plumbing of the chain, with the boundary ideal the
invariants in `(x)` (one boundary point, `l = 1`) or in `(x) ∩ (y)` (two, `l = 2`). -/
private theorem exists_ringEquiv_of_chain (hS : IsSurfaceGermWithBoundary sY y B)
    (hB : IsReducedBoundary B)
    {Y' : Scheme.{v}} (f : Y' ⟶ Y) [QuasiCompact (f ≫ sY)] [IsLocallyNoetherian Y']
    [IsNormal Y'] {n : ℕ} (E : Fin n → Mori.PrimeDivisor Y') (hf : IsMinimalGermResolution sY y f)
    (hE : IsExceptionalCurveEnumeration f y E) (hn : 1 ≤ n) {l : ℕ}
    (pt : Fin l → Mori.PrimeDivisor Y' × Y') (Γ : ExtendedWeightedGraph (Fin n) (Fin l))
    (e : Fin n ≃ Fin n) (hΓ : IsExtendedDualGraph sY y B f E pt Γ)
    (hchain : Γ.toWeightedGraph.IsChainOrder e) (hw : ∀ j, 2 ≤ Γ.toWeightedGraph.weight j)
    (hl : l = 1 ∨ l = 2) (hpt : ∀ (a b : Fin l), a ≠ b → (pt a).2 ≠ (pt b).2)
    (hbd : ∀ (a : Fin l) j, Γ.boundaryEdgeWeight j a =
      if j = e (if (a : ℕ) = 0 then ⟨0, hn⟩ else ⟨n - 1, by omega⟩) then 1 else 0) :
    letI := Mori.stalkAlgebra sY y
    ∃ (m : ℕ) (q : ℤ) (_ : IsCyclicQuotientSetting K m q)
      (φ : cyclicInvariants K m q ≃+*
        𝒪̂(Y.presheaf.stalk y)),
      (∀ c : K, ((φ.symm (algebraMap (Y.presheaf.stalk y)
          (𝒪̂(Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) : cyclicInvariants K m q) :
            MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (cyclicInvariants K m q).subtype
          (if l = 1 then Ideal.span {MvPowerSeries.X 0}
            else Ideal.span {MvPowerSeries.X 0} ⊓ Ideal.span {MvPowerSeries.X 1})) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (𝒪̂(Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) := by
  letI := Mori.stalkAlgebra sY y
  obtain ⟨⟨⟨hYv, hYn⟩, hYd, hycl, -⟩, hBy, -⟩ := hS
  have hg := hf.1
  have : IsIntegral Y' := hg.isIntegral sY
  have : IsProper f := hg.isSmoothResolution.isProper
  have hY'v : Mori.IsVariety K (f ≫ sY) := hg.isVariety
  have hY'd := hg.topologicalKrullDim_eq
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : QuasiCompact sY := hYv.toQuasiCompact
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsNoetherian Y := ⟨⟩
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace (f ≫ sY)
  have : IsNoetherian Y' := ⟨⟩
  have : IsIntegral Y := hYv.toIsIntegral
  have : Smooth (f ≫ sY) := (isSmoothScheme_iff _).mp hsm
  have : Mori.IsVariety K (f ≫ sY) := hY'v
  have : SmoothOfRelativeDimension 2 (f ≫ sY) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 2 (by exact_mod_cast hY'd)
  have hiso := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism (f ≫ sY)
    sY hY'v ⟨hYv, hYn⟩ f hg.isSmoothResolution.isBirationalMorphism).1
  -- the chain, from left to right
  set E' : Fin n → Mori.PrimeDivisor Y' := fun i => E (e i) with hE'
  set b : Fin n → ℕ := fun i => (Γ.toWeightedGraph.weight (e i)).toNat with hbdef
  have hb : ∀ i, 2 ≤ b i := fun i => by
    have := hw (e i); simp only [hbdef]; omega
  have hinj : Function.Injective E' := hE.injective.comp e.injective
  have hexc : ∀ i, IsGermExceptionalCurve f y (E' i) := fun i => hE.isGermExceptionalCurve _
  have hprop : ∀ i, IsProper ((E' i).idealSheaf.subschemeι ≫ f ≫ sY) := fun i =>
    ((hexc i).isProper sY hg).2
  have hrat : ∀ i, IsSmoothRationalCurve (f ≫ sY) (E' i).idealSheaf := fun i => by
    have h := hΓ.isWeightedDualGraph.genus (e i)
    rw [hchain.genus_eq_zero i] at h
    exact isSmoothRationalCurve_of_isArithmeticGenusOf_zero _ _ (hexc i).2 (by exact_mod_cast h)
  have hself : ∀ i, IsIntersectionNumber (f ≫ sY) (Finsupp.single (E' i) 1) (E' i).idealSheaf
      (-(b i : ℤ)) := fun i => by
    have h := hΓ.isWeightedDualGraph.weight (e i)
    have hnn : (0 : ℤ) ≤ Γ.toWeightedGraph.weight (e i) := by have := hw (e i); omega
    have hbi : ((b i : ℕ) : ℤ) = Γ.toWeightedGraph.weight (e i) := Int.toNat_of_nonneg hnn
    rw [hbi]
    push_cast
    exact h
  have hne : ∀ i j : Fin n, i.val ≠ j.val → e i ≠ e j := fun i j h he =>
    h (congrArg Fin.val (e.injective he))
  have hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      IsIntersectionNumber (f ≫ sY) (Finsupp.single (E' i) 1) (E' j).idealSheaf 1 := by
    intro i j hij
    have h := hΓ.isWeightedDualGraph.edgeWeight (e i) (e j) (hne i j (by omega))
    rw [hchain.edgeWeight_eq i j, if_pos (Or.inl hij)] at h
    exact_mod_cast h
  have hfar : ∀ i j : Fin n, i.val + 1 < j.val →
      Disjoint (E' i).support (E' j).support := by
    intro i j hij
    have h := hΓ.isWeightedDualGraph.edgeWeight (e i) (e j) (hne i j (by omega))
    rw [hchain.edgeWeight_eq i j, if_neg (by omega)] at h
    refine (disjoint_support_of_isIntersectionNumber_zero (f ≫ sY) hY'v hsm hY'd
      (fun h' => hne j i (by omega) (hE.injective h')) (hprop j) (by exact_mod_cast h)).symm
  -- the exceptional curve
  set I := ∏ i, (E' i).idealSheaf with hI
  have hreg' : ∀ x : Y', IsRegularLocalRing (Y'.presheaf.stalk x) :=
    ((isRegular_iff_regular_stalks Y').1
      (MMP.Resolution.Bridges.isRegular_of_isSmoothScheme (f ≫ sY) hsm)).2
  have hred : IsReduced I.subscheme := by
    rw [hI, prod_idealSheaf_eq_finsetInf hreg' E' hinj, finsetInf_idealSheaf_eq_vanishingIdeal]
    exact Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hmaps : ∀ x ∈ (I.support : Set Y'), f.base x = y := by
    intro x hx
    rw [hI, coe_support_prod] at hx
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hx
    exact (hexc i).1.prop.2 hi
  have hfib : f.base ⁻¹' {y} ⊆ (I.support : Set Y') := by
    have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      (f ≫ sY) sY hY'v ⟨hYv, hYn⟩ f hg.isSmoothResolution.isBirationalMorphism).2 y
    intro z hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (preimage_subset_iUnion_support hg hn hE hconn hz)
    rw [hI, coe_support_prod]
    refine Set.mem_iUnion₂.mpr ⟨e.symm j, Finset.mem_univ _, ?_⟩
    simpa only [hE', Equiv.apply_symm_apply] using hj
  -- the two marked points and their markings
  obtain ⟨pL, pR, hpLR, hpL, hpL', hpR, hpR', ZL, ZR, hZL, hZR, hZL_succ, hZR_succ, hZLs, hZRs,
    hZLc, hZRc, hJ⟩ : ∃ (pL pR : Y') (_ : pL ≠ pR) (_ : pL ∈ (E' ⟨0, hn⟩).support)
      (_ : ∀ i, i ≠ ⟨0, hn⟩ → pL ∉ (E' i).support) (_ : pR ∈ (E' ⟨n - 1, by omega⟩).support)
      (_ : ∀ i, i ≠ ⟨n - 1, by omega⟩ → pR ∉ (E' i).support)
      (ZL ZR : ℕ → Y'.IdealSheafData) (hZL : ∀ n, I ^ (n + 1) ≤ ZL n)
      (hZR : ∀ n, I ^ (n + 1) ≤ ZR n) (_ : ∀ n, ZL n = ZL (n + 1) ⊔ I ^ (n + 1))
      (_ : ∀ n, ZR n = ZR (n + 1) ⊔ I ^ (n + 1))
      (_ : ∀ n, ((ZL n).support : Set Y') = {pL}) (_ : ∀ n, ((ZR n).support : Set Y') = {pR})
      (_ : ∀ n, ∃ e : (ZL n).subscheme ≅
        Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZL n).subschemeι ≫ f ≫ sY)
      (_ : ∀ n, ∃ e : (ZR n).subscheme ≅
        Spec (.of (Polynomial K ⧸ Ideal.span {(Polynomial.X : Polynomial K) ^ (n + 1)})),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K _)) = (ZR n).subschemeι ≫ f ≫ sY),
      ∀ t, t ∈ Ideal.map (algebraMap (Y.presheaf.stalk y)
          (𝒪̂(Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) ↔
        if l = 1 then
          (∀ n, (Scheme.IdealSheafData.inclusion (hZL n)).appTop.hom
            ((I.completionToFormalNeighborhood f y hmaps t).1 n) = 0)
        else
          (∀ n, (Scheme.IdealSheafData.inclusion (hZL n)).appTop.hom
            ((I.completionToFormalNeighborhood f y hmaps t).1 n) = 0) ∧
          (∀ n, (Scheme.IdealSheafData.inclusion (hZR n)).appTop.hom
            ((I.completionToFormalNeighborhood f y hmaps t).1 n) = 0) := by
    classical
    have : LocallyOfFiniteType (f ≫ sY) := hY'v.toLocallyOfFiniteType
    obtain ⟨hFcl, hFne⟩ := hg.isClosed_preimage_and_ne_univ
    have hgenmem : ∀ D : Mori.PrimeDivisor Y', D.genericPoint ∈ D.support := fun D => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    have hgenmemY : ∀ C : Mori.PrimeDivisor Y, C.genericPoint ∈ C.support := fun C => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    -- the components of the boundary and their transforms
    have hbir : ∀ x : Y, x ≠ y → x ∈ biregularLocus f := by
      obtain ⟨U, hU, hiso⟩ := hg.isIso_away
      intro x hx
      exact le_biregularLocus hiso (show x ∈ (U : Set Y) by rwa [hU])
    have hgenC : ∀ C ∈ B.support, C.genericPoint ≠ y := by
      intro C hC hgen
      have hdimC : topologicalKrullDim (C.support : Set Y) = 1 := by
        rw [← topologicalKrullDim_subscheme]
        exact (isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hYd C).2
      have hsub : (C.support : Set Y) = {y} := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        change closure {C.genericPoint} = _
        rw [hgen, hycl.closure_eq]
      rw [hsub] at hdimC
      have : DiscreteTopology ({y} : Set Y) := Subsingleton.discreteTopology
      have h0 := topologicalKrullDim_zero_of_discreteTopology ({y} : Set Y)
      rw [hdimC] at h0
      exact absurd h0 (by decide)
    have htr : ∀ C ∈ B.support, ∃ D : Mori.PrimeDivisor Y',
        inverseTransformPrimeDivisor f C = some D ∧ f.base D.genericPoint = C.genericPoint :=
      fun C hC => exists_inverseTransformPrimeDivisor_eq_some C (hbir _ (hgenC C hC))
    have hDC : ∀ a, ∃ C ∈ B.support, f.base (pt a).1.genericPoint = C.genericPoint := by
      intro a
      obtain ⟨C, hC, hτ⟩ := exists_mem_support_of_inverseTransformDivisor_ne_zero f B
        (hΓ.isGermBoundaryPoint a).1
      obtain ⟨D, hD, hgen⟩ := htr C hC
      rw [hD] at hτ
      obtain rfl := Option.some.inj hτ
      exact ⟨C, hC, hgen⟩
    have hcoef : ∀ C ∈ B.support, ∀ D : Mori.PrimeDivisor Y',
        inverseTransformPrimeDivisor f C = some D → inverseTransformDivisor f B D ≠ 0 := by
      intro C hC D hD
      have hsum : inverseTransformDivisor f B D = ∑ C' ∈ B.support,
          ((inverseTransformPrimeDivisor f C').elim 0 (Finsupp.single · (B C'))) D := by
        conv_lhs => rw [← Finsupp.sum_single B]
        rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
        refine Finset.sum_congr rfl fun C' _ => ?_
        rw [inverseTransformDivisor_single]
      rw [hsum]
      refine (Finset.sum_pos' (fun C' hC' => ?_) ⟨C, hC, ?_⟩).ne'
      · rcases inverseTransformPrimeDivisor f C' with _ | D'
        · exact le_rfl
        · change (0 : ℚ) ≤ Finsupp.single D' (B C') D
          rw [Finsupp.single_apply]
          split_ifs
          · rw [hB C' hC']; exact zero_le_one
          · exact le_rfl
      · rw [hD]
        change (0 : ℚ) < Finsupp.single D (B C) D
        rw [Finsupp.single_eq_same, hB C hC]; exact zero_lt_one
    have hCD : ∀ C ∈ B.support, ∃ a, f.base (pt a).1.genericPoint = C.genericPoint := by
      intro C hC
      obtain ⟨D, hD, hgen⟩ := htr C hC
      have hcl : IsClosed (f.base '' (D.support : Set Y')) :=
        f.isClosedMap _ D.idealSheaf.support.isClosed
      have h1 : C.genericPoint ∈ f.base '' (D.support : Set Y') := ⟨_, hgenmem D, hgen⟩
      have h2 : (C.support : Set Y) ⊆ f.base '' D.support := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h1)
      obtain ⟨z, hz, hfz⟩ := h2 (hBy C hC)
      obtain ⟨a, ha⟩ := hΓ.exists_eq D z ⟨hcoef C hC D hD, hz, hfz⟩
      exact ⟨a, by rwa [ha]⟩
    have hptinj : Function.Injective fun a => (pt a).2 := fun a b h =>
      by_contra fun hab => hpt a b hab h
    have hDfib : ∀ a, f.base (pt a).1.genericPoint ≠ y := fun a => by
      obtain ⟨C, hC, hgen⟩ := hDC a
      rw [hgen]; exact hgenC C hC
    have hDE : ∀ a i, (pt a).1 ≠ E i := by
      intro a i h
      apply hDfib a
      rw [h]
      exact (hE.isGermExceptionalCurve i).1.prop.2 (hgenmem (E i))
    have hDb : ∀ a b, (pt a).2 ∈ (pt b).1.support → (pt b).1 = (pt a).1 := by
      intro a b hab
      obtain ⟨c, hc⟩ := hΓ.exists_eq (pt b).1 (pt a).2
        ⟨(hΓ.isGermBoundaryPoint b).1, hab, (hΓ.isGermBoundaryPoint a).2.2⟩
      have hca : c = a := hptinj (show (pt c).2 = (pt a).2 by rw [hc])
      subst hca
      exact (congrArg Prod.fst hc).symm
    -- the boundary points on the chain
    obtain ⟨eend, heend⟩ : ∃ g : Fin l → Fin n,
        ∀ a, g a = e (if (a : ℕ) = 0 then ⟨0, hn⟩ else ⟨n - 1, by omega⟩) := ⟨_, fun _ => rfl⟩
    have hpos : ∀ a j, (pt a).2 ∈ (E j).support → 0 < localIntersectionNumber (f ≫ sY)
        (pt a).2 (Finsupp.single (pt a).1 1) (Finsupp.single (E j) 1) := by
      intro a j hj
      have h := (MMP.Mori.isIntersectionNumber_finsum_localIntersectionNumber_of_ne (f ≫ sY)
        hY'v hsm hY'd (fun h => hDE a j h.symm)
        ((hE.isGermExceptionalCurve j).isProper sY hg).2).2.2 _
        ⟨hj, (hΓ.isGermBoundaryPoint a).2.1⟩
      rwa [localIntersectionNumber_comm] at h
    have hqE : ∀ a j, (pt a).2 ∈ (E j).support ↔ j = eend a := by
      intro a j
      have h := (hbd a j).symm.trans (hΓ.boundaryEdgeWeight_eq j a)
      rw [← heend a] at h
      constructor
      · intro hj
        by_contra hne
        rw [if_neg hne, if_pos hj] at h
        exact (hpos a j hj).ne h
      · rintro rfl
        rw [if_pos rfl] at h
        by_contra hj'
        rw [if_neg hj'] at h
        exact one_ne_zero h
    have hqlin : ∀ a, localIntersectionNumber (f ≫ sY) (pt a).2
        (Finsupp.single (pt a).1 1) (Finsupp.single (E (eend a)) 1) = 1 := by
      intro a
      have h := (hbd a (eend a)).symm.trans (hΓ.boundaryEdgeWeight_eq (eend a) a)
      rw [← heend a, if_pos rfl, if_pos ((hqE a _).mpr rfl)] at h
      exact h.symm
    have hqcl : ∀ a, IsClosed ({(pt a).2} : Set Y') := by
      intro a
      by_contra hcl
      have hqF : (pt a).2 ∈ f.base ⁻¹' {y} := (hΓ.isGermBoundaryPoint a).2.2
      have hne : closure ({(pt a).2} : Set Y') ≠ Set.univ := fun h =>
        hFne (Set.eq_univ_of_univ_subset
          (h ▸ hFcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hqF)))
      have h1 := coheight_eq_one_of_not_isClosed (f ≫ sY) hY'd hcl hne
      have hsp : (E (eend a)).genericPoint ⤳ (pt a).2 := by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact (hqE a _).mpr rfl
      have hneE : closure ({(E (eend a)).genericPoint} : Set Y') ≠ Set.univ := by
        rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        intro h
        apply hFne
        exact Set.eq_univ_of_univ_subset (h ▸ (hE.isGermExceptionalCurve (eend a)).1.prop.2)
      have h2 := eq_of_specializes_of_coheight_eq_one h1 hsp hneE
      apply hDE a (eend a)
      refine (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support ?_).symm
      rw [h2]; exact (hΓ.isGermBoundaryPoint a).2.1
    have hdimq : ∀ a, ringKrullDim (Y'.presheaf.stalk (pt a).2) = 2 := fun a =>
      MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two (f ≫ sY) hY'v hY'd (pt a).2 (hqcl a)
    have hprin : ∀ (x : Y'), IsClosed ({x} : Set Y') → ∀ D : Mori.PrimeDivisor Y',
        x ∈ D.support → ∃ π, IdealSheafData.stalk D.idealSheaf x = Ideal.span {π} := by
      intro x hx D hD
      have := hreg' x
      have := isPrime_stalk_idealSheaf D hD
      obtain ⟨h0, hm⟩ := stalk_idealSheaf_ne_bot_and_ne_maximalIdeal hY'v hY'd D hD hx
      obtain ⟨π, -, he⟩ := exists_prime_eq_span_of_ne
        (MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two (f ≫ sY) hY'v hY'd x hx) _ h0 hm
      exact ⟨π, he⟩
    have hloc : ∀ a, ∃ h w : Y'.presheaf.stalk (pt a).2,
        IdealSheafData.stalk (pt a).1.idealSheaf (pt a).2 = Ideal.span {h} ∧
        IdealSheafData.stalk (E (eend a)).idealSheaf (pt a).2 = Ideal.span {w} ∧
        Ideal.span {h, w} = maximalIdeal (Y'.presheaf.stalk (pt a).2) := by
      intro a
      obtain ⟨h, hh⟩ := hprin _ (hqcl a) _ (hΓ.isGermBoundaryPoint a).2.1
      obtain ⟨w, hw⟩ := hprin _ (hqcl a) _ ((hqE a _).mpr rfl)
      refine ⟨h, w, hh, hw, ?_⟩
      have := stalk_sup_eq_maximalIdeal_of_localIntersectionNumber_eq_one (f ≫ sY) _ _ _
        (hqlin a)
      rwa [hh, hw, ← Ideal.span_union, Set.singleton_union] at this
    choose hh hw hhD hwE hhw using hloc
    -- the ideal of the exceptional curve near a point of a single component
    have hIstalk : ∀ (x : Y') (i₀ : Fin n), (∀ i, i ≠ i₀ → x ∉ (E' i).support) →
        IdealSheafData.stalk I x = IdealSheafData.stalk (E' i₀).idealSheaf x := by
      intro x i₀ hx
      rw [hI, MMP.Resolution.Aux.stalk_prod, Finset.prod_eq_single i₀]
      · intro i _ hi
        rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ (hx i hi),
          Ideal.one_eq_top]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hIq : ∀ a, IdealSheafData.stalk I (pt a).2 = Ideal.span {hw a} := by
      intro a
      rw [hIstalk (pt a).2 (e.symm (eend a)) fun i hi hmem => hi ?_]
      · simpa only [hE', Equiv.apply_symm_apply] using hwE a
      · rw [← e.symm_apply_apply i, (hqE a (e i)).mp hmem]
    -- the markings at the boundary points
    have hmark := fun a => exists_marking_of_span_eq (f ≫ sY) (pt a).2 (hqcl a) (hdimq a) I
      (hIq a) (hhw a)
    choose Zm hZm hZm_succ hZms hZmc hZmp using hmark
    -- the boundary curve, finite over `Y`
    set Zb : Y'.IdealSheafData := Finset.univ.inf fun a => (pt a).1.idealSheaf with hZbdef
    have hZbmem : ∀ z : Y', z ∈ Zb.support ↔ ∃ a, z ∈ (pt a).1.support := by
      intro z
      have h1 := Stacks.Divisors.stalk_eq_top_iff_notMem_support Zb z
      rw [hZbdef, MMP.Intersection.stalk_finsetInf, Finset.inf_eq_top_iff] at h1
      have h2 : ∀ a, IdealSheafData.stalk (pt a).1.idealSheaf z = ⊤ ↔ z ∉ (pt a).1.support :=
        fun a => Stacks.Divisors.stalk_eq_top_iff_notMem_support _ z
      constructor
      · intro hz
        by_contra hz'
        push Not at hz'
        exact (h1.mp fun a _ => (h2 a).mpr (hz' a)) hz
      · rintro ⟨a, ha⟩
        by_contra hz
        exact (h2 a).mp (h1.mpr hz a (Finset.mem_univ a)) ha
    have hιZ : Function.Injective Zb.subschemeι := Zb.subschemeι.isClosedEmbedding.injective
    have hZbfin : IsFinite (Zb.subschemeι ≫ f) := by
      refine (IsFinite.iff_isProper_and_locallyQuasiFinite _).mpr ⟨inferInstance,
        LocallyQuasiFinite.of_finite_preimage_singleton _ fun x => ?_⟩
      refine Set.Finite.of_finite_image ?_ hιZ.injOn
      by_cases hx : x = y
      · refine (Set.finite_range fun a => (pt a).2).subset ?_
        rintro _ ⟨t, ht, rfl⟩
        have hz : Zb.subschemeι t ∈ Zb.support := by
          change _ ∈ (Zb.support : Set Y')
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨t, rfl⟩
        obtain ⟨b, hb⟩ := (hZbmem _).mp hz
        obtain ⟨c, hc⟩ := hΓ.exists_eq (pt b).1 (Zb.subschemeι t)
          ⟨(hΓ.isGermBoundaryPoint b).1, hb, by rwa [← hx]⟩
        exact ⟨c, show (pt c).2 = _ by rw [hc]⟩
      · obtain ⟨U, hU, hiso⟩ := hg.isIso_away
        have : IsIso (f ∣_ U) := hiso
        refine (MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict f U
          (show x ∈ (U : Set Y) by rwa [hU])).finite.subset ?_
        rintro _ ⟨t, ht, rfl⟩
        exact ht
    -- germs vanishing on the boundary
    have hJmem : ∀ z : Y.presheaf.stalk y,
        z ∈ IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y ↔
          ∀ C ∈ B.support, z ∈ IdealSheafData.stalk C.idealSheaf y := by
      intro z
      rw [← Finset.inf_eq_iInf, MMP.Intersection.stalk_finsetInf, Submodule.mem_finsetInf]
    have hspC : ∀ C ∈ B.support, AlgebraicGeometry.PrimeDivisor.genericPoint C ⤳ y :=
      fun C hC => by
        rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact hBy C hC
    have hkerZ : ∀ (U : Y.Opens) (hy : y ∈ U), IsAffineOpen U → ∀ r : Γ(Y, U),
        ((Zb.subschemeι ≫ f).app U).hom r = 0 →
        (Y.presheaf.germ U y hy).hom r ∈
          IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y := by
      intro U hy _ r hr
      rw [hJmem]
      intro C hC
      rw [germ_mem_stalk_iff C (hBy C hC) hy r]
      obtain ⟨a, ha⟩ := hCD C hC
      have hgZ : (pt a).1.genericPoint ∈ Zb.support := (hZbmem _).mpr ⟨a, hgenmem _⟩
      obtain ⟨t, ht⟩ : (pt a).1.genericPoint ∈ Set.range Zb.subschemeι := by
        rwa [Scheme.IdealSheafData.range_subschemeι]
      have hCU : AlgebraicGeometry.PrimeDivisor.genericPoint C ∈ U :=
        (hspC C hC).mem_open U.isOpen hy
      have hξ : f.base (Zb.subschemeι t) = C.genericPoint := by rwa [ht]
      have hfU : f.base (Zb.subschemeι t) ∈ U := by rwa [hξ]
      have htU : (Zb.subschemeι ≫ f).base t ∈ U := hfU
      have h0 := congrArg (Zb.subscheme.presheaf.germ ((Zb.subschemeι ≫ f) ⁻¹ᵁ U) t htU).hom hr
      rw [map_zero, ← Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.stalkMap_comp] at h0
      change (Zb.subschemeι.stalkMap t).hom ((f.stalkMap (Zb.subschemeι t)).hom
        ((Y.presheaf.germ U (f.base (Zb.subschemeι t)) hfU).hom r)) = 0 at h0
      have h1 : (f.stalkMap (Zb.subschemeι t)).hom
          ((Y.presheaf.germ U (f.base (Zb.subschemeι t)) hfU).hom r) ∈ maximalIdeal _ := by
        have h2 := RingHom.mem_ker.mpr h0
        rw [Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk] at h2
        exact (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support Zb _).mpr
          (by rw [ht]; exact hgZ) h2
      rw [Scheme.Hom.germ_stalkMap_apply] at h1
      exact (germ_app_mem_maximalIdeal_iff f hξ hCU r).mp h1
    have hpy : ∀ a, f.base (pt a).2 = y := fun a => (hΓ.isGermBoundaryPoint a).2.2
    have hpull : ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
        (Y.presheaf.germ U y hy).hom s ∈ IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y →
        ∀ a n, (Y'.presheaf.germ (f ⁻¹ᵁ U) (pt a).2
          (show f.base (pt a).2 ∈ U from (hpy a) ▸ hy)).hom ((f.app U).hom s) ∈
            IdealSheafData.stalk (Zm a n) (pt a).2 := by
      intro U hy s hs a n
      rw [hZmp a n]
      refine Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)) ?_
      rw [← hhD a]
      obtain ⟨C, hC, hgen⟩ := hDC a
      have hCU : AlgebraicGeometry.PrimeDivisor.genericPoint C ∈ U :=
        (hspC C hC).mem_open U.isOpen hy
      refine (germ_mem_stalk_iff (pt a).1 (hΓ.isGermBoundaryPoint a).2.1 (U := f ⁻¹ᵁ U)
        (show f.base (pt a).2 ∈ U from (hpy a) ▸ hy) ((f.app U).hom s)).mpr ?_
      refine (germ_app_mem_maximalIdeal_iff f hgen hCU s).mpr ?_
      exact (germ_mem_stalk_iff C (hBy C hC) hy s).mp ((hJmem _).mp hs C hC)
    have hpZ : ∀ a, (pt a).2 ∈ Zb.support := fun a =>
      (hZbmem _).mpr ⟨a, (hΓ.isGermBoundaryPoint a).2.1⟩
    have hallZ : ∀ z ∈ Zb.support, f.base z = y → ∃ a, (pt a).2 = z := by
      intro z hz hfz
      obtain ⟨b, hb⟩ := (hZbmem z).mp hz
      obtain ⟨c, hc⟩ := hΓ.exists_eq (pt b).1 z ⟨(hΓ.isGermBoundaryPoint b).1, hb, hfz⟩
      exact ⟨c, show (pt c).2 = _ by rw [hc]⟩
    have hhZ : ∀ a, hh a ∈ IdealSheafData.stalk Zb (pt a).2 := by
      intro a
      rw [hZbdef, MMP.Intersection.stalk_finsetInf, Submodule.mem_finsetInf]
      intro b _
      by_cases hab : (pt a).2 ∈ (pt b).1.support
      · rw [hDb a b hab, hhD a]; exact Ideal.mem_span_singleton_self _
      · rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support _ hab]; trivial
    have hwm : ∀ a, hw a ∈ maximalIdeal (Y'.presheaf.stalk (pt a).2) := fun a => by
      rw [← hhw a]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
    have hdeep : ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)),
        (∀ a, (Y'.presheaf.germ (f ⁻¹ᵁ U) (pt a).2
          (show f.base (pt a).2 ∈ U from (hpy a) ▸ hy)).hom ((f.app U).hom s) ∈
            IdealSheafData.stalk (Zm a n) (pt a).2) →
        (Y.presheaf.germ U y hy).hom s ∈
          IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y ⊔
            maximalIdeal (Y.presheaf.stalk y) ^ N := by
      intro N
      obtain ⟨n₀, hn₀⟩ := mem_sup_pow_of_forall_mem_span f y hycl Zb (fun a => (pt a).2)
        hptinj hpy hpZ hallZ hh hw hhZ hwm _ hkerZ N
      refine ⟨n₀, fun n hn U hy s hs => hn₀ n hn U hy s fun a => ?_⟩
      rw [← hZmp a n]; exact hs a
    have hJgen := mem_map_iff_forall_appTop_inclusion_eq_zero f y I hmaps (fun a => (pt a).2)
      hpy Zm hZms hZm _ hpull hdeep
    rcases hl with rfl | rfl
    · -- type (3): the boundary point, and an auxiliary marking at the other end
      have he0 : eend 0 = e ⟨0, hn⟩ := by rw [heend]; simp
      set iR : Fin n := ⟨n - 1, by omega⟩ with hiR
      have hEnormal : IsNormal (E' iR).idealSheaf.subscheme := by
        obtain ⟨-, eiso, -⟩ := hrat iR
        exact Stacks.ResolutionOfSurfaces.isNormal_of_iso_projectiveLineProj K
          ((projectiveLineIsoProj K).symm ≪≫ eiso)
      have : JacobsonSpace Y' := LocallyOfFiniteType.jacobsonSpace (f ≫ sY)
      set W : Set Y' := ((E' iR).support : Set Y') ∩
        ((⋃ i ∈ {i | i ≠ iR}, ((E' i).support : Set Y')) ∪ {(pt 0).2})ᶜ with hW
      have hWlc : IsLocallyClosed W :=
        (E' iR).idealSheaf.support.isClosed.isLocallyClosed.inter (IsOpen.isLocallyClosed
          (isOpen_compl_iff.mpr ((Set.Finite.isClosed_biUnion (Set.toFinite _)
            fun i _ => (E' i).idealSheaf.support.isClosed).union (hqcl 0))))
      have hWne : W.Nonempty := by
        refine ⟨(E' iR).genericPoint, hgenmem _, ?_⟩
        rintro (h | h)
        · obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp h
          exact hi (hinj (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hmem)).symm
        · have h' : (E' iR).genericPoint = (pt 0).2 := h
          apply hDE 0 (e iR)
          refine (MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support ?_).symm
          rw [h']; exact (hΓ.isGermBoundaryPoint 0).2.1
      obtain ⟨pR, ⟨hpRE, hpRo⟩, hpRcl⟩ := nonempty_inter_closedPoints hWne hWlc
      rw [mem_closedPoints_iff] at hpRcl
      have hpRo1 : pR ∉ ⋃ i ∈ {i | i ≠ iR}, ((E' i).support : Set Y') :=
        fun h => hpRo (Or.inl h)
      have hpRo2 : pR ≠ (pt 0).2 := fun h => hpRo (Or.inr h)
      obtain ⟨wR, hwR⟩ := hprin pR hpRcl (E' iR) hpRE
      have := hreg' pR
      obtain ⟨h0R, hmR⟩ := stalk_idealSheaf_ne_bot_and_ne_maximalIdeal hY'v hY'd (E' iR) hpRE hpRcl
      have hdimR := MMP.Mori.SurfaceAux.ringKrullDim_stalk_eq_two (f ≫ sY) hY'v hY'd pR hpRcl
      obtain ⟨hR, hhwR⟩ := exists_span_pair_eq_maximalIdeal (E' iR) hpRE hdimR hwR h0R hmR
      have hIR : IdealSheafData.stalk I pR = Ideal.span {wR} :=
        (hIstalk pR iR fun i hi hmem => hpRo1 (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩)).trans hwR
      obtain ⟨ZR, hZR, hZR_succ, hZRs, hZRc, -⟩ :=
        exists_marking_of_span_eq (f ≫ sY) pR hpRcl hdimR I hIR hhwR
      refine ⟨(pt 0).2, pR, fun h => hpRo2 h.symm, ?_, ?_, hpRE,
        fun i hi hmem => hpRo1 (Set.mem_iUnion₂.mpr ⟨i, hi, hmem⟩), Zm 0, ZR, hZm 0, hZR,
        hZm_succ 0, hZR_succ, hZms 0, hZRs, hZmc 0, hZRc, fun t => (hJgen t).trans ?_⟩
      · change (pt 0).2 ∈ (E (e ⟨0, hn⟩)).support
        rw [← he0]; exact (hqE 0 _).mpr rfl
      · intro i hi hmem
        exact hi (e.injective (((hqE 0 (e i)).mp hmem).trans he0))
      · rw [if_pos rfl, Fin.forall_fin_one]
    · -- type (9): the two boundary points
      have he0 : eend 0 = e ⟨0, hn⟩ := by rw [heend]; simp
      have he1 : eend 1 = e ⟨n - 1, by omega⟩ := by rw [heend]; simp
      refine ⟨(pt 0).2, (pt 1).2, hpt 0 1 (by decide), ?_, ?_, ?_, ?_, Zm 0, Zm 1, hZm 0, hZm 1,
        hZm_succ 0, hZm_succ 1, hZms 0, hZms 1, hZmc 0, hZmc 1, fun t => (hJgen t).trans ?_⟩
      · change (pt 0).2 ∈ (E (e ⟨0, hn⟩)).support
        rw [← he0]; exact (hqE 0 _).mpr rfl
      · intro i hi hmem
        exact hi (e.injective (((hqE 0 (e i)).mp hmem).trans he0))
      · change (pt 1).2 ∈ (E (e ⟨n - 1, by omega⟩)).support
        rw [← he1]; exact (hqE 1 _).mpr rfl
      · intro i hi hmem
        exact hi (e.injective (((hqE 1 (e i)).mp hmem).trans he1))
      · rw [if_neg (by decide), Fin.forall_fin_two]
  -- the contraction of the marked chain
  have : IsNormal Y := hYn
  have hfibE : f.base ⁻¹' {y} = ⋃ i, ((E' i).support : Set Y') := by
    rw [Set.Subset.antisymm hfib fun x hx => hmaps x hx, hI, coe_support_prod]
    simp
  obtain ⟨m, hm, q, hq, φ, ψ, hφc, hψ, hL, -, hLR⟩ :=
    exists_ringEquiv_cyclicInvariants_of_isSNCChain_fibre (f ≫ sY) sY f
      ⟨hYv, hY'v, rfl, inferInstance, hiso⟩ hYd y hycl hn E' b hb hfibE hinj hrat hself hadj
      hfar pL pR hpLR hpL hpL' hpR hpR' ZL ZR hZL hZR hZL_succ hZR_succ (hZLs 0) (hZRs 0) hZLc
      hZRc
  have hψt : ∀ n t, ψ n t = (I.completionToFormalNeighborhood f y hmaps t).1 n := fun n =>
    eq_completionToFormalNeighborhood f y I hmaps n (ψ n) fun a => by
      obtain ⟨U, hyU, s, rfl⟩ := Y.presheaf.germ_exist a
      rw [hψ n U hyU (Scheme.Hom.top_le_preimage_of_forall_base_eq _ y
        (Scheme.IdealSheafData.base_thickening_eq I f y hmaps n) U hyU)]
      exact (Scheme.Hom.stalkToΓ_germ _ _ _ _ _ _).symm
  simp only [hψt] at hL hLR
  refine ⟨m, q, ⟨inferInstance, inferInstance, by omega, hq⟩, φ, hφc, ?_⟩
  ext t
  rw [Ideal.mem_map_of_equiv, hJ]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Ideal.mem_comap] at ha
    split_ifs with hl1
    · rw [if_pos hl1] at ha
      exact (hL a).mpr (by simpa using ha)
    · rw [if_neg hl1] at ha
      exact (hLR a).mpr (by simpa using ha)
  · intro ht
    refine ⟨φ.symm t, ?_, φ.apply_symm_apply t⟩
    rw [← φ.apply_symm_apply t] at ht
    rw [Ideal.mem_comap]
    split_ifs with hl1
    · rw [if_pos hl1] at ht
      simpa using (hL _).mp ht
    · rw [if_neg hl1] at ht
      simpa using (hLR _).mp ht

end Cases

section

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}}
  (sY : Y ⟶ Spec (.of K))

/-- **Formal cyclic-quotient models of the chain germs** (FA 16.6.3). Let `(Y, y; C)` be a surface
germ with reduced boundary `C` over an algebraically closed field `K` of characteristic `0`.
If it is of type (3), resp. type (9), then for some `m ≥ 1` and `q` prime to `m` there is a
`K`-isomorphism `K[[x, y]]^{μ_m} ≃ 𝒪̂_{Y,y}` carrying the ideal of `C^{(1)}_{m,q}`, resp.
`C^{(2)}_{m,q}`, onto `I_{C,y} 𝒪̂_{Y,y}`: that is, `(Spec 𝒪̂_{Y,y}, C) ≅ (T_{m,q}, C^{(1)}_{m,q})`,
resp. `(T_{m,q}, C^{(2)}_{m,q})`, over `K`. -/
@[mmp "lem_mmp_foundation_fa16_chain_formal_cyclic_quotient"]
public theorem exists_ringEquiv_cyclicInvariants_of_isFig3Type3_or_isFig3Type9
    (y : Y) (B : QDivisor Y) (hB : IsReducedBoundary B)
    (g : MvPowerSeries (Fin 2) K)
    (htype : IsFig3Type3 sY y B ∧ g = MvPowerSeries.X 0 ∨
      IsFig3Type9 sY y B ∧ g = MvPowerSeries.X 0 * MvPowerSeries.X 1) :
    letI := Mori.stalkAlgebra sY y
    ∃ (m : ℕ) (q : ℤ) (h : IsCyclicQuotientSetting K m q)
      (φ : cyclicInvariants K m q ≃+*
        AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)),
      (∀ c : K, ((φ.symm (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) : cyclicInvariants K m q) :
            MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (Scheme.ΓSpecIso (.of (cyclicInvariants K m q))).inv.hom
          ((Scheme.IdealSheafData.vanishingIdeal (cyclicQuotientImage h g)).ideal
            ⟨⊤, isAffineOpen_top _⟩)) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) := by
  letI := Mori.stalkAlgebra sY y
  suffices H : ∃ (m : ℕ) (q : ℤ) (_ : IsCyclicQuotientSetting K m q)
      (φ : cyclicInvariants K m q ≃+*
        AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)),
      (∀ c : K, ((φ.symm (algebraMap (Y.presheaf.stalk y)
          (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y))
          (algebraMap K (Y.presheaf.stalk y) c)) : cyclicInvariants K m q) :
            MvPowerSeries (Fin 2) K) = MvPowerSeries.C c) ∧
      Ideal.map φ (Ideal.comap (cyclicInvariants K m q).subtype (Ideal.span {g}).radical) =
        Ideal.map (algebraMap (Y.presheaf.stalk y)
            (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
          (IdealSheafData.stalk (⨅ C ∈ B.support, C.idealSheaf) y) by
    obtain ⟨m, q, h, φ, hc, hI⟩ := H
    exact ⟨m, q, h, φ, hc, by rwa [comap_vanishingIdeal_cyclicQuotientImage]⟩
  rcases htype with ⟨⟨hS, Y', f, _, _, _, n, E, hf, hE, hcase⟩, rfl⟩ |
    ⟨⟨hS, Y', f, _, _, _, n, E, hf, hE, hcase⟩, rfl⟩
  · rcases hcase with ⟨rfl, C, hC, hreg⟩ | ⟨hn, pt, Γ, e, hΓ, hchain, hw, hbd⟩
    · obtain ⟨Φ, hc, hI⟩ := exists_ringEquiv_of_type3_smooth sY y B hS f E hf hE C hC hreg
      exact exists_of_ringEquiv_mvPowerSeries _ (radical_span_X 0) _ Φ hc hI
    · obtain ⟨m, q, h, φ, hc, hI⟩ := exists_ringEquiv_of_chain sY y B hS hB f E hf hE hn pt Γ e
        hΓ hchain hw (Or.inl rfl) (fun a b hab => absurd (Subsingleton.elim a b) hab)
        (fun a j => by rw [Subsingleton.elim a 0]; simpa using hbd j)
      refine ⟨m, q, h, φ, hc, ?_⟩
      rw [radical_span_X]
      rwa [if_pos rfl] at hI
  · have hrad : (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} :
        Ideal (MvPowerSeries (Fin 2) K)).radical =
          Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1} := by
      rw [radical_span_X_mul_X, span_X_inf_span_X]
    rcases hcase with ⟨rfl, hP, mu, hmu, hsum, hcard⟩ |
      ⟨hn, pt, Γ, e, hΓ, hchain, hw, hne, hbd0, hbd1⟩
    · obtain ⟨Φ, hc, hI⟩ := exists_ringEquiv_of_type9_smooth sY y B hS hB f E hf hE hP mu hmu
        hsum hcard
      exact exists_of_ringEquiv_mvPowerSeries _ hrad _ Φ hc hI
    · obtain ⟨m, q, h, φ, hc, hI⟩ := exists_ringEquiv_of_chain sY y B hS hB f E hf hE hn pt Γ e
        hΓ hchain hw (Or.inr rfl) (fun a b hab => by
          fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | exact hne | exact hne.symm)
        (fun a j => by fin_cases a <;> simpa using by first | exact hbd0 j | exact hbd1 j)
      refine ⟨m, q, h, φ, hc, ?_⟩
      rw [radical_span_X_mul_X]
      rwa [if_neg (by decide)] at hI

end

end MMP.Flips
