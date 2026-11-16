module

public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.TransferredDivisorDegree

/-!
# Enough curves in the fibre of a small `ℚ`-factorialization

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), `L_1, …, L_b` a
punctured-independent family of line bundles on the generic scheme fibre `F_{η_T}`
(`MMP.Fourfold.IsPuncturedIndependent`), `(Y_e, q, η', L̃_1, …, L̃_b)` a local étale datum for it
(`MMP.Fourfold.LocalEtaleDatum`), and `g : Y' ⟶ Y_e` a projective small birational morphism with
`Y'` `ℚ`-factorial. Then the fibre `g⁻¹(η')` has at least `b` irreducible curve components.

## Main results

* `MMP.Fourfold.LocalEtaleDatum.le_card_properCurve_fiber`: `b` is at most the number of
  curve components of `g⁻¹(η')`.

## Implementation notes

The irreducible curve components of `g⁻¹(η')_red` are the proper curves
(`MMP.Mori.ProperCurve`) of the scheme fibre `g⁻¹(η') ⟶ Spec κ(η')`: as `g` is small, this
fibre has dimension at most one, and as `g` is projective it is proper over `κ(η')`. Their
number is counted in `ℕ∞` (`ENat.card`), so that the statement does not presuppose that it is
finite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.OAI4LocalDegreeIndependenceB

/-- `b` linearly independent vectors of functions `C → K` force `b ≤ #C`, the cardinal taken
in `ℕ∞` so that an infinite `C` is allowed. -/
private theorem card_le_enatCard_of_linearIndependent {K ι C : Type*} [Field K] [Fintype ι]
    {v : ι → C → K} (h : LinearIndependent K v) : (Fintype.card ι : ℕ∞) ≤ ENat.card C := by
  cases finite_or_infinite C with
  | inr hC => simp
  | inl hC =>
    have := Fintype.ofFinite C
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_le]
    simpa using h.fintype_card_le_finrank

/-- The base change of `μ` along `q`, restricted over `q⁻¹(U)`, is a pullback of `μ ∣_ U`
along `q ∣_ U`. -/
private lemma exists_isPullback_morphismRestrict_pullback_snd {Y₀ Yₑ W : Scheme.{0}}
    (q : Yₑ ⟶ Y₀) (μ : W ⟶ Y₀) (U : Y₀.Opens) :
    ∃ v : ((pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)).toScheme ⟶ (μ ⁻¹ᵁ U).toScheme,
      IsPullback (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) v (q ∣_ U) (μ ∣_ U) := by
  have h3 := isPullback_morphismRestrict μ U
  have hc : (pullback.snd μ q ∣_ (q ⁻¹ᵁ U) ≫ q ∣_ U) ≫ U.ι =
      (((pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)).ι ≫ pullback.fst μ q) ≫ μ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, Category.assoc, ← pullback.condition]
  let v := h3.lift _ _ hc
  refine ⟨v, IsPullback.of_bot (h₂₁ := μ ∣_ U) (v₂₁ := (μ ⁻¹ᵁ U).ι) (v₂₂ := U.ι) ?_ ?_ h3⟩
  · rw [h3.lift_snd, morphismRestrict_ι]
    exact (isPullback_morphismRestrict (pullback.snd μ q) (q ⁻¹ᵁ U)).paste_vert
      (IsPullback.of_hasPullback μ q).flip
  · exact (h3.lift_fst _ _ hc).symm

/-- A space with an open map to an irreducible space is irreducible as soon as the preimage
of some open set is irreducible. -/
private lemma irreducibleSpace_of_isIrreducible_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [PreirreducibleSpace Y] {f : X → Y} (hf : IsOpenMap f) {O : Set Y}
    (hO : IsOpen O) (h : IsIrreducible (f ⁻¹' O)) : IrreducibleSpace X := by
  obtain ⟨x, hx⟩ := h.nonempty
  rw [irreducibleSpace_def]
  simpa [((hO.dense ⟨_, hx⟩).preimage hf).closure_eq] using h.closure

/-- **Étale base change of a birational morphism is integral.** Let `q : Yₑ ⟶ Y₀` be étale
with `Yₑ` integral, and `μ : W ⟶ Y₀` an isomorphism over a dense open `U`, with `W` integral
and normal. Then `W ×_{Y₀} Yₑ` is integral. -/
private lemma isIntegral_pullback_of_etale {Y₀ Yₑ W : Scheme.{0}} [IsIntegral Yₑ]
    (q : Yₑ ⟶ Y₀) [Etale q] [IsIntegral W] [IsNormal W] (μ : W ⟶ Y₀)
    {U : Y₀.Opens} (hU : Dense (U : Set Y₀)) (hμU : IsIso (μ ∣_ U)) :
    IsIntegral (pullback μ q) := by
  have : Etale (pullback.fst μ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip ‹Etale q›
  have : UniversallyOpen (pullback.fst μ q) := UniversallyOpen.of_flat _
  have : IsNormal (pullback μ q) := isNormal_of_etale (pullback.fst μ q)
  have : IsIso (pullback.snd μ q ∣_ (q ⁻¹ᵁ U)) := by
    obtain ⟨_, hv⟩ := exists_isPullback_morphismRestrict_pullback_snd q μ U
    exact hv.isIso_fst_of_isIso
  set V := (pullback.snd μ q) ⁻¹ᵁ (q ⁻¹ᵁ U)
  obtain ⟨x⟩ : Nonempty Yₑ := inferInstance
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hU.inter_open_nonempty _ q.isOpenMap.isOpen_range ⟨q x, x, rfl⟩
  have : Nonempty (q ⁻¹ᵁ U).toScheme := ⟨⟨y, hy⟩⟩
  have : Nonempty V.toScheme := ⟨(inv (pullback.snd μ q ∣_ (q ⁻¹ᵁ U))) ⟨y, hy⟩⟩
  have : IsIntegral V.toScheme :=
    isIntegral_of_isOpenImmersion (pullback.snd μ q ∣_ (q ⁻¹ᵁ U))
  have hVirr : IsIrreducible (V : Set ↥(pullback μ q)) := by
    have := (IrreducibleSpace.isIrreducible_univ V.toScheme).image V.ι V.ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have hVeq : (V : Set ↥(pullback μ q)) = pullback.fst μ q ⁻¹' (μ ⁻¹ᵁ U : Set W) := by
    ext x
    change q (pullback.snd μ q x) ∈ U ↔ μ (pullback.fst μ q x) ∈ U
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have : IrreducibleSpace ↥(pullback μ q) :=
    irreducibleSpace_of_isIrreducible_preimage (pullback.fst μ q).isOpenMap
      (μ ⁻¹ᵁ U).isOpen (hVeq ▸ hVirr)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end MMP.OAI4LocalDegreeIndependenceB

namespace MMP.Fourfold.LocalEtaleDatum

/-- For a local setting `(Y, Θ, T, π)`, a punctured-independent family `L_1, …, L_b` on
`F_{η_T}`, a local étale datum `E` for it and a projective small birational morphism
`g : Y' ⟶ Y_e` with `Y'` `ℚ`-factorial, the fibre `g⁻¹(η')` over the point `η'` of `E` has at
least `b` irreducible curve components. -/
@[mmp "lem_oai4_local_degree_independence_b"]
public theorem le_card_properCurve_fiber
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hY : IsLocalSetting sY Θ T π) {b : ℕ} {L : Fin b → (genericFibre π T).Modules}
    (hL : IsPuncturedIndependent sY hY.isBiregular L)
    (E : LocalEtaleDatum sY T π L)
    {Y' : Scheme.{0}} [IsLocallyNoetherian Y'] [IsNormal Y'] (g : Y' ⟶ E.scheme)
    (hg : IsSmallMorphism (g ≫ E.map ≫ sY) (E.map ≫ sY) g) (hgp : IsProjectiveMorphism g)
    (hQ : IsQFactorial (g ≫ E.map ≫ sY)) :
    (b : ℕ∞) ≤ ENat.card (ProperCurve (g.fiberToSpecResidueField E.point)) := by
  have := hY.isNormal_resolution
  have := hY.isLocallyNoetherian_resolution
  have hqp := E.isQuasiProjectiveVariety
  have : IsIntegral E.scheme := hqp.toIsIntegral
  have : CompactSpace E.scheme := QuasiCompact.compactSpace_of_compactSpace (E.map ≫ sY)
  have : IsProper g := hg.isProper
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨hYv, hYtv, hsm, hπp, -⟩ := hY.isResolution
  have : IsIntegral Yt := hYtv.toIsIntegral
  have : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have hU : Dense (smoothLocus sY : Set Y) := (smoothLocus sY).isOpen.dense
    ⟨_, MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus' (f := sY)⟩
  have : IsIntegral E.resolution :=
    OAI4LocalDegreeIndependenceB.isIntegral_pullback_of_etale E.map π hU hY.isBiregular
  have : IsProper π := isProper_of_isProjectiveMorphism π hπp
  have : CompactSpace E.resolution :=
    QuasiCompact.compactSpace_of_compactSpace E.resolutionMap
  have : Smooth (π ≫ sY) := (isSmoothScheme_iff (π ≫ sY)).mp hsm
  have hsme : IsSmoothScheme (pullback.fst π E.map ≫ π ≫ sY) :=
    (isSmoothScheme_iff _).mpr inferInstance
  choose D hD using fun i =>
    @exists_divisorialSheaf_iso_of_isInvertible _ _ _ _ _ (E.bundle i) (E.isInvertibleModule i)
  simpa using OAI4LocalDegreeIndependenceB.card_le_enatCard_of_linearIndependent <|
    linearIndependent_transferredDivisor_degree hY hL E g D
      ⟨hg, hgp, fun i => isCartier_of_isSmoothScheme hsme (D i), hD⟩ hQ

end MMP.Fourfold.LocalEtaleDatum
