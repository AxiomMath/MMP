module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
import MMP.AlgebraicGeometry.Intersection.InvertibleSheafCurveDegree
import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
import MMP.AlgebraicGeometry.Analytic.PluriformDensity
import MMP.AlgebraicTopology.ThomClass.Natural
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Codimension-two blow-ups and étale transport of punctured independence

Two local facts used in the analysis of fourfold contractions.

**The blow-up of a smooth codimension-two centre.** Let `Y` be a normal variety over a field `k`
of characteristic zero with `K_Y` `ℚ`-Cartier, and let `S ⊆ Y` be an irreducible closed subset of
codimension two such that `Y` is smooth at the generic point `η_S`. Then `𝒪_{Y,η_S}` is a regular
local ring of dimension two, and the exceptional prime `E` of the blow-up of `S` near `η_S`
defines a normalized divisorial valuation `w_S = ord_E` of `k(Y)` with centre `S`. On
`𝒪_{Y,η_S}` it is the `𝔪`-adic order: `ord_E(f) ≥ n` exactly when `f ∈ 𝔪^n`. Since
`K_{Bl} = β^*K_Y + E` near `E`, its log discrepancy is `a(w_S; Y, 0) = 2`.

Everything is local at `η_S`. In characteristic zero the reduced subscheme `Z` on `S` is smooth at
its generic point, so there is an open `U ∋ η_S` on which both `Y` and `Z ∩ U` are smooth. The
exceptional divisor of the blow-up of `Z ∩ U` has the `𝔪`-adic valuation and discrepancy `1`; that
valuation is realized by a proper divisor over `Y` with centre `S`, whose discrepancy is computed
on `U`.

**Independence survives the étale extension.** Let `(Y, Θ, T, π)` be a local setting,
`L_1, …, L_b` a punctured-independent family of line bundles on the generic scheme fibre
`F_{η_T}`, and `(Y_e, q, η', L̃_i)` a local étale datum for it, with
`π_e : Ỹ_e = Ỹ ×_Y Y_e ⟶ Y_e`, `T' = closure {η'}` and `j_e : (Y_e)_reg ⟶ Y_e`. Then `π_e` is
again an isomorphism over `(Y_e)_reg`, and there is a dense Zariski-open `T'° ⊆ T'` such that at
every `ℂ`-point `t'` of `T'°` the images of the first Chern classes `c₁(L̃_i|_{π_e⁻¹(t')})` in the
stalk `(R²j_{e*} ℚ)_{t'}` are linearly independent over `ℚ`. The proof spreads the generic
identification of `L̃_i` with the pull-back of the adapted family out to a dense open of `T'`,
transports Chern classes along the fibre isomorphisms `F_{t'} ≅ F_{q(t')}`, and uses that `q^an`
is a local homeomorphism to transport the independence of germs.

## Main results

* `MMP.Fourfold.exists_isCentre_of_codimension_eq_two`: on any variety, the valuation of `k(Y)`
  given on `𝒪_{Y,η_S}` by the `𝔪`-adic order has centre `S`.
* `MMP.Fourfold.exists_isCentre_isValuationLogDiscrepancy_two_of_codimension_eq_two`.
* `MMP.Fourfold.LocalEtaleDatum.exists_dense_linearIndependent_chernClass`.

## Implementation notes

* The exceptional valuation of the blow-up of `S` near `η_S` is pinned intrinsically: it is the
  valuation `w` with `w(f) ≤ exp(-n) ↔ f ∈ 𝔪^n` for every `f` in the stalk `𝒪_{Y,η_S}` and
  `n : ℕ`, which is the order valuation of the exceptional divisor of the blow-up of the maximal
  ideal of the regular local ring `𝒪_{Y,η_S}`. This determines `w` on the fraction field `k(Y)`.
* "`K_Y` is `ℚ`-Cartier" is `MMP.Mori.IsPair sY 0`, which also records that `Y` is a normal
  variety; the log discrepancy is `MMP.Fourfold.IsValuationLogDiscrepancy` with boundary `0`.

## References

* [KM98] Kollár, Mori, *Birational geometry of algebraic varieties*, Lemma 2.29.
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace MMP.Fourfold

/-! ### The blow-up of a smooth codimension-two centre -/

/-- A divisor `ξ_U` of the function field of a nonempty open `U ⊆ Y` gives the divisor
`ξ_U ∘ (k(Y) ≅ k(U))` of `k(Y)`. -/
private theorem isDivisorOfFunctionField_comap_functionFieldMap_ι {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] (U : Y.Opens) [Nonempty U]
    {ξU : Valuation U.toScheme.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Flips.IsDivisorOfFunctionField k (U.ι ≫ sY) ξU) :
    haveI := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›));
    MMP.Flips.IsDivisorOfFunctionField k sY
      (ξU.comap (AlgebraicGeometry.functionFieldMap U.ι)) := by
  have := Opens.isDominant_ι (U.isOpen.dense (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  have hf := MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
    ⟨_, Set.mem_univ (Classical.arbitrary U)⟩
  let := MMP.Mori.functionFieldAlgebra sY
  let := MMP.Mori.functionFieldAlgebra (U.ι ≫ sY)
  obtain ⟨Y', sY', hY', E, e, he⟩ := h
  have : IsIntegral Y' := hY'.1.toIsIntegral
  have : IsNormal Y' := hY'.2
  have : IsLocallyNoetherian Y' :=
    have := hY'.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sY'
  let := MMP.Mori.functionFieldAlgebra sY'
  refine ⟨Y', sY', hY', E, (MMP.Mori.functionFieldAlgEquiv sY U.ι hf).trans e, ?_⟩
  subst he
  rfl

/-- The `𝔪`-adic divisor of `k(Y)` is realized by a divisor `E` over `Y` with proper structure map
and centre `S`. -/
private theorem exists_divisorOver_of_isDivisorOfFunctionField
    {k : Type u} [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : AlgebraicGeometry.IsVariety k sY) (S : IrreducibleCloseds Y)
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hdiv : MMP.Flips.IsDivisorOfFunctionField k sY v)
    (hv : ∀ (f : Y.presheaf.stalk S.isIrreducible.genericPoint) (n : ℕ),
      v (algebraMap _ Y.functionField f) ≤ WithZero.exp (-(n : ℤ)) ↔
        f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk S.isIrreducible.genericPoint) ^ n) :
    ∃ D : MMP.Mori.DivisorOver k sY, IsProper D.f ∧ S = D.center ∧
      ∀ (f : Y.presheaf.stalk S.isIrreducible.genericPoint) (n : ℕ),
        D.valuation (algebraMap _ Y.functionField f) ≤ WithZero.exp (-(n : ℤ)) ↔
          f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk S.isIrreducible.genericPoint) ^ n := by
  have := hY
  obtain ⟨D, -, hDv, hDx⟩ := MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sY hdiv
    S.isIrreducible.genericPoint (fun a => by simpa using (hv a 0).2 (by simp))
    (fun a ha => ((hv a 1).2 (by simpa using ha)).trans_lt (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))
  refine ⟨D.toDivisorOver, D.isProper, ?_, fun f n => ?_⟩
  · refine IrreducibleCloseds.ext ?_
    rw [MMP.Mori.DivisorOver.center_eq_closure_genericPoint, hDx,
      S.isIrreducible.genericPoint_closure_eq, S.isClosed.closure_eq]
  · rw [show D.toDivisorOver.valuation = v from hDv, hv f n]

/-- In `ℤᵐ⁰`, if every bound `b ≤ exp (-n)` implies `a ≤ exp (-n)` and `b ≤ 1`, then `a ≤ b`. -/
private theorem le_of_forall_le_exp_neg_imp {a b : WithZero (Multiplicative ℤ)} (hb : b ≤ 1)
    (h : ∀ n : ℕ, b ≤ WithZero.exp (-(n : ℤ)) → a ≤ WithZero.exp (-(n : ℤ))) : a ≤ b := by
  rcases eq_or_ne b 0 with rfl | hb0
  · rcases eq_or_ne a 0 with rfl | ha0
    · exact le_rfl
    exfalso
    obtain ⟨z, rfl⟩ : ∃ z, a = WithZero.exp z := ⟨WithZero.log a, (WithZero.exp_log ha0).symm⟩
    have := h ((-z).toNat + 1) zero_le
    rw [WithZero.exp_le_exp] at this
    omega
  · obtain ⟨w, rfl⟩ : ∃ w, b = WithZero.exp w := ⟨WithZero.log b, (WithZero.exp_log hb0).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at hb
    have hw : w = -(((-w).toNat : ℕ) : ℤ) := by omega
    have := h (-w).toNat (by rw [← hw])
    rwa [← hw] at this

/-- A valuation of `k(X)` is determined by its `𝔪`-adic description on one stalk `𝒪_{X,x}`:
`v(f) ≤ exp (-n) ↔ f ∈ 𝔪_x^n`. -/
private theorem eq_of_forall_le_exp_neg_iff_mem_pow {X : Scheme.{u}} [IsIntegral X] (x : X)
    {v v' : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : ∀ (f : X.presheaf.stalk x) (n : ℕ), v (algebraMap _ X.functionField f) ≤
      WithZero.exp (-(n : ℤ)) ↔ f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n)
    (hv' : ∀ (f : X.presheaf.stalk x) (n : ℕ), v' (algebraMap _ X.functionField f) ≤
      WithZero.exp (-(n : ℤ)) ↔ f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n) :
    v = v' := by
  have h1 : ∀ (w : Valuation X.functionField (WithZero (Multiplicative ℤ))),
      (∀ (f : X.presheaf.stalk x) (n : ℕ), w (algebraMap _ X.functionField f) ≤
        WithZero.exp (-(n : ℤ)) ↔ f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n) →
      ∀ f : X.presheaf.stalk x, w (algebraMap _ X.functionField f) ≤ 1 := fun w hw f => by
    simpa using (hw f 0).2 (by simp)
  refine MMP.Fourfold.eq_of_forall_stalk_eq x fun g => le_antisymm
    (le_of_forall_le_exp_neg_imp (h1 v' hv' g) fun n h => (hv g n).2 ((hv' g n).1 h))
    (le_of_forall_le_exp_neg_imp (h1 v hv g) fun n h => (hv' g n).2 ((hv g n).1 h))

/-- The valuation `ord_E` of a divisor `(W, g, E)` over `X` is a divisor of `k(X)`. -/
private theorem isDivisorOfFunctionField_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (D : MMP.Mori.DivisorOver k sX) :
    MMP.Flips.IsDivisorOfFunctionField k sX D.valuation := by
  have := D.isIntegral
  have := D.isDominant
  let := MMP.Mori.functionFieldAlgebra sX
  let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
  let := MMP.Mori.functionFieldMapAlgebra D.f
  have := MMP.Mori.isScalarTower_functionFieldMap sX D.f
  exact ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k X.functionField D.Y.functionField)
    D.isBirationalMorphism.functionFieldMap_bijective, rfl⟩

open MMP.Mori MMP.Resolution MMP.Threefold.Resolution in
/-- **The exceptional divisor of a smooth codimension-two blow-up.** Let `X` be a smooth variety
of dimension `d` over `k`, `Z = V(I)` a smooth irreducible closed subscheme of codimension two
with generic point `x`, and `E` the exceptional prime divisor of the blow-up `Bl_Z X ⟶ X`. Then
`ord_E` is the `𝔪_x`-adic order on `𝒪_{X,x}`, and `ord_E(π^*τ) = m` for every rational
`m`-canonical form `τ` generating `ω_X^{⊗m}` near `x`. -/
private theorem exists_divisorOver_blowUp_ordPullback
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsVariety k sX)
    (I : X.IdealSheafData) (h : IsSmoothBlowup sX I) (hirr : IsIrreducible (I.support : Set X))
    (hc : ((2 : ℕ) : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X))
    {d : ℕ} (hd : topologicalKrullDim X = d) (x : X) (hx : hirr.genericPoint = x) :
    haveI := hX.toIsIntegral
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    ∃ D : MMP.Mori.DivisorOver k sX,
      (∀ (g : X.presheaf.stalk x) (s : ℕ), D.valuation (algebraMap _ X.functionField g) ≤
          WithZero.exp (-(s : ℤ)) ↔ g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ s) ∧
      ∀ (m : ℕ) (τ : MMP.Mori.RationalPluriForms sX d m),
        (∃ V : X.Opens, x ∈ V ∧ MMP.Mori.GeneratesOn (0 : MMP.Mori.QDivisor X) m V τ) →
          D.ordPullback τ = m := by
  subst hx
  have := hX.toIsIntegral
  have : Smooth sX := smooth_of_isSmoothScheme h.1
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_smooth sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have := AlgebraicGeometry.isNormal_of_smooth sX
  have hc2' : 2 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X) :=
    hc ▸ le_rfl
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds X) :=
    le_trans (by norm_num) hc2'
  have := isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have := isDominant_blowUpToBase I hirr hc1
  have := TwoStepTower.compactSpace_blowUp (TwoStepTower.isFiniteType_of_isLocallyNoetherian I)
  obtain ⟨hsm, hproj, hbir, -⟩ :=
    smooth_isProjective_isBirationalMorphism_blowUpToBase sX I h hirr hc2'
  have : IsProjective (blowUpToBase I) := hproj
  have : Smooth (blowUpToBase I ≫ sX) := hsm
  have : IsLocallyNoetherian (blowUp I) := isLocallyNoetherian_of_smooth (blowUpToBase I ≫ sX)
  have := AlgebraicGeometry.isNormal_of_smooth (blowUpToBase I ≫ sX)
  have hvar : AlgebraicGeometry.IsVariety k (blowUpToBase I ≫ sX) := {}
  obtain ⟨h1, h2⟩ := ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback sX hX I h hirr
    hc (le_refl 2) hd
  refine ⟨⟨blowUp I, blowUpToBase I, ⟨hvar, inferInstance⟩, hbir,
    exceptionalPrimeDivisor sX I h hirr hc1⟩, fun g s => ?_, fun m τ hτ => ?_⟩
  · change MMP.Mori.PrimeDivisor.divisorialValuation (exceptionalPrimeDivisor sX I h hirr hc1)
      (functionFieldMap (blowUpToBase I) (algebraMap _ X.functionField g)) ≤ _ ↔ _
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    have hg' : functionFieldMap (blowUpToBase I) (algebraMap _ X.functionField g) ≠ 0 :=
      (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg)
    rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg', WithZero.exp_le_exp,
      neg_le_neg_iff]
    exact h1 g hg s
  · have := h2 m τ hτ
    change MMP.Mori.PrimeDivisor.ordForm (exceptionalPrimeDivisor sX I h hirr hc1)
      (pullbackRationalPluriForms sX (blowUpToBase I) τ) = m
    rw [this]
    push_cast
    ring

/-- A morphism to `Spec k` locally of finite type is locally of finite presentation. -/
private theorem locallyOfFinitePresentation_of_spec {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : LocallyOfFinitePresentation f :=
  (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f)).mpr inferInstance

/-- If the range of an open immersion `j` lies in the smooth locus of `g`, then `j ≫ g` is
smooth. -/
private theorem isSmoothScheme_comp_of_range_subset {X Y Z : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (g : Y ⟶ Z) [LocallyOfFinitePresentation g]
    (hj : Set.range j ⊆ (g.smoothLocus : Set Y)) : MMP.Mori.IsSmoothScheme (j ≫ g) := by
  rw [MMP.Mori.IsSmoothScheme, MMP.Mori.smoothLocus_eq_smoothLocus,
    ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
  intro x _
  exact hj ⟨x, rfl⟩

/-- An isomorphism `φ` of local rings matches the powers of the maximal ideals. -/
private theorem mem_maximalIdeal_pow_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A ≃+* B) (a : A) (s : ℕ) :
    φ a ∈ IsLocalRing.maximalIdeal B ^ s ↔ a ∈ IsLocalRing.maximalIdeal A ^ s := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal φ, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨b, hb, hba⟩
    rwa [← φ.injective hba]
  · exact fun ha => ⟨a, ha, rfl⟩

/-- **Generic smoothness of a centre.** In characteristic zero, if `Y` is smooth at the generic
point `η` of an irreducible closed `S ⊆ Y`, there is an open `U ∋ η` such that `U` is smooth and
the reduced subscheme on `S ∩ U` is smooth. -/
private theorem exists_open_isSmoothScheme_comap_vanishingIdeal {k : Type u} [Field k]
    [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFinitePresentation sY]
    (S : IrreducibleCloseds Y) (hsm : S.isIrreducible.genericPoint ∈ sY.smoothLocus) :
    ∃ U : Y.Opens, S.isIrreducible.genericPoint ∈ U ∧ MMP.Mori.IsSmoothScheme (U.ι ≫ sY) ∧
      MMP.Mori.IsSmoothScheme
        (((Scheme.IdealSheafData.vanishingIdeal ⟨S, S.isClosed⟩).comap U.ι).subschemeι ≫
          U.ι ≫ sY) := by
  set η := S.isIrreducible.genericPoint
  have hηgen : IsGenericPoint η (S : Set Y) :=
    S.isIrreducible.isGenericPoint_genericPoint S.isClosed
  set J : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨S, S.isClosed⟩
  have hJS : (J.support : Set Y) = S := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsReduced J.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace J.subscheme := by
    have hr : Set.range J.subschemeι = (S : Set Y) := by
      rw [Scheme.IdealSheafData.range_subschemeι, hJS]
    have : IrreducibleSpace (Set.range J.subschemeι) :=
      Subtype.irreducibleSpace (hr ▸ S.isIrreducible)
    exact (Homeomorph.irreducibleSpace_iff
      J.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).mpr this
  have : IsIntegral J.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have := locallyOfFinitePresentation_of_spec (J.subschemeι ≫ sY)
  have hJgen : J.subschemeι (genericPoint J.subscheme) = η := by
    refine IsGenericPoint.eq ?_ hηgen
    change closure _ = _
    rw [MMP.Resolution.closure_subschemeι_genericPoint, hJS]
  have hgsm : genericPoint J.subscheme ∈ (J.subschemeι ≫ sY).smoothLocus :=
    Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField _
  -- `F` is the image of the singular locus of the reduced centre
  let F : Set Y := J.subschemeι '' ((J.subschemeι ≫ sY).smoothLocus : Set J.subscheme)ᶜ
  have hF : IsClosed F := J.subschemeι.isClosedEmbedding.isClosedMap _
    (J.subschemeι ≫ sY).smoothLocus.isOpen.isClosed_compl
  have hηF : η ∉ F := by
    rintro ⟨z, hz, hzη⟩
    rw [← hJgen] at hzη
    exact hz (J.subschemeι.isClosedEmbedding.injective hzη ▸ hgsm)
  let U : Y.Opens := sY.smoothLocus ⊓ ⟨Fᶜ, hF.isOpen_compl⟩
  refine ⟨U, ⟨hsm, hηF⟩, isSmoothScheme_comp_of_range_subset U.ι sY ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact y.2.1
  let I : U.toScheme.IdealSheafData := J.comap U.ι
  let j := (J.comapIso U.ι).hom ≫ pullback.snd U.ι J.subschemeι
  have hj : I.subschemeι ≫ U.ι = j ≫ J.subschemeι := by
    simp only [j, I, Category.assoc, ← pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  change MMP.Mori.IsSmoothScheme (I.subschemeι ≫ U.ι ≫ sY)
  rw [← Category.assoc, hj, Category.assoc]
  refine isSmoothScheme_comp_of_range_subset j _ ?_
  rintro _ ⟨z, rfl⟩
  by_contra hz
  refine (I.subschemeι z).2.2 ⟨_, hz, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hj]
  rfl

open MMP.Mori in
/-- **The blow-up of `S` near `η_S`.** Let `Y` be a variety of dimension `n` over a field `k` of
characteristic zero and `S ⊆ Y` an irreducible closed subset of codimension two with `Y` smooth at
its generic point `η_S`. There are an open `U ∋ η_S` of dimension `n` and a divisor `E` over `U`
(the exceptional divisor of the blow-up of the reduced subscheme on `S ∩ U`) such that `ord_E` is
the `𝔪`-adic order on `𝒪_{Y,η_S}` and `ord_E(π^*τ) = m` for every rational `m`-canonical form `τ`
generating `ω_U^{⊗m}` near `η_S`. -/
private theorem exists_open_divisorOver_blowUp {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y]
    (hY : AlgebraicGeometry.IsVariety k sY) {n : ℕ} (hn : topologicalKrullDim Y = n)
    (S : IrreducibleCloseds Y) (hS : codimension S = 2)
    (hsm : S.isIrreducible.genericPoint ∈ smoothLocus sY) :
    ∃ (U : Y.Opens) (hηU : S.isIrreducible.genericPoint ∈ U), topologicalKrullDim U = n ∧
      haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
      haveI := Opens.isDominant_ι (U.isOpen.dense ⟨_, hηU⟩)
      ∃ Dbl : DivisorOver k (U.ι ≫ sY),
        (∀ (f : Y.presheaf.stalk S.isIrreducible.genericPoint) (s : ℕ),
          Dbl.valuation.comap (functionFieldMap U.ι) (algebraMap _ Y.functionField f) ≤
            WithZero.exp (-(s : ℤ)) ↔
              f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk S.isIrreducible.genericPoint) ^ s) ∧
        ∀ (m : ℕ) (τ : RationalPluriForms (U.ι ≫ sY) n m),
          (∃ V : U.toScheme.Opens, ⟨_, hηU⟩ ∈ V ∧ GeneratesOn (0 : QDivisor U) m V τ) →
            Dbl.ordPullback τ = m := by
  have := hY
  have := locallyOfFinitePresentation_of_spec sY
  set η := S.isIrreducible.genericPoint
  have hηgen : IsGenericPoint η (S : Set Y) :=
    S.isIrreducible.isGenericPoint_genericPoint S.isClosed
  have hsm' : η ∈ sY.smoothLocus := by rwa [← smoothLocus_eq_smoothLocus]
  obtain ⟨U, hηU, hUsm, hIsm⟩ := exists_open_isSmoothScheme_comap_vanishingIdeal sY S hsm'
  have hJS : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨S, S.isClosed⟩ : TopologicalSpace.Closeds Y)).support : Set Y) = S :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : Nonempty U := ⟨⟨η, hηU⟩⟩
  have := Opens.isDominant_ι (U.isOpen.dense ⟨η, hηU⟩)
  let x₀ : U.toScheme := ⟨η, hηU⟩
  -- the reduced centre `Z ∩ U` of `U`
  set I : U.toScheme.IdealSheafData :=
    (Scheme.IdealSheafData.vanishingIdeal ⟨S, S.isClosed⟩).comap U.ι
  have hIsupp : (I.support : Set U) = U.ι ⁻¹' (S : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hJS]
  have hx₀gen : IsGenericPoint x₀ (I.support : Set U) := by
    rw [hIsupp]
    change closure ({x₀} : Set U.toScheme) = U.ι ⁻¹' (S : Set Y)
    rw [U.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image {x₀},
      show (U.ι '' ({x₀} : Set U.toScheme)) = {η} by
        ext y; constructor
        · rintro ⟨z, hz, rfl⟩; rw [Set.mem_singleton_iff.mp hz]; rfl
        · rintro rfl; exact ⟨x₀, rfl, rfl⟩,
      hηgen.def]
  have hirr : IsIrreducible (I.support : Set U) := hx₀gen.isIrreducible
  have hx₀ : hirr.genericPoint = x₀ :=
    (hirr.isGenericPoint_genericPoint I.support.isClosed).eq hx₀gen
  -- the stalks of `U` at `x₀` and of `Y` at `η` agree
  let φ : Y.presheaf.stalk η ≃+* U.toScheme.presheaf.stalk x₀ :=
    (asIso (U.ι.stalkMap x₀)).commRingCatIsoToRingEquiv
  have hc : ((2 : ℕ) : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    have h1 := codimension_eq_ringKrullDim_stalk
      (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) x₀ hx₀gen
    have h2 := codimension_eq_ringKrullDim_stalk S η hηgen
    rw [← ringKrullDim_eq_of_ringEquiv φ, ← h2, hS] at h1
    exact_mod_cast h1.symm
  have hUvar : MMP.Mori.IsVariety k (U.ι ≫ sY) := by
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    have : IsNoetherian Y := {}
    exact ⟨⟩
  have hUn : topologicalKrullDim U = n := by
    have hbij := functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨_, Set.mem_univ x₀⟩
    rw [← toENat_trdeg_functionField (sX := U.ι ≫ sY),
      ← trdeg_functionField_eq_of_bijective sY U.ι hbij, toENat_trdeg_functionField (sX := sY), hn]
  -- the exceptional divisor of the blow-up of `Z ∩ U`
  obtain ⟨Dbl, hDv, hDord⟩ := exists_divisorOver_blowUp_ordPullback (U.ι ≫ sY) hUvar I
    ⟨hUsm, hIsm⟩ hirr hc hUn x₀ hx₀
  refine ⟨U, hηU, hUn, Dbl, fun f s => ?_, hDord⟩
  rw [Valuation.comap_apply]
  erw [functionFieldMap_algebraMap_stalk U.ι x₀ f]
  rw [hDv, ← mem_maximalIdeal_pow_iff_of_ringEquiv φ f s]
  rfl

/-- **The blow-up valuation of a smooth codimension-two centre.** Let `Y` be a normal variety of
dimension `n` over a field `k` of characteristic zero, and `S ⊆ Y` an irreducible closed subset of
codimension two with `Y` smooth at its generic point `η_S`. Then the exceptional valuation `w` of
the blow-up of `S` near `η_S`, that is, the valuation of `k(Y)` given on `𝒪_{Y,η_S}` by the
`𝔪`-adic order, is a normalized divisorial valuation with centre `S`. -/
public theorem exists_isCentre_of_codimension_eq_two
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : AlgebraicGeometry.IsVariety k sY) {n : ℕ} (hn : topologicalKrullDim Y = n)
    (S : IrreducibleCloseds Y) (hS : codimension S = 2)
    (hsm : S.isIrreducible.genericPoint ∈ MMP.Mori.smoothLocus sY) :
    ∃ w : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      (∀ (f : Y.presheaf.stalk S.isIrreducible.genericPoint) (n : ℕ),
        w (algebraMap _ Y.functionField f) ≤ WithZero.exp (-(n : ℤ)) ↔
          f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk S.isIrreducible.genericPoint) ^ n) ∧
      MMP.Intersection.IsCentre k sY w S := by
  obtain ⟨U, hηU, -, Dbl, hξ, -⟩ := exists_open_divisorOver_blowUp sY hY hn S hS hsm
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  obtain ⟨D, hDp, hDc, hDv⟩ := exists_divisorOver_of_isDivisorOfFunctionField sY hY S
    (isDivisorOfFunctionField_comap_functionFieldMap_ι sY U
      (isDivisorOfFunctionField_valuation Dbl)) hξ
  exact ⟨D.valuation, hDv, D, hDp, rfl, hDc⟩

/-- **Blow-up of a smooth codimension-two centre.** Let `Y` be a normal variety over a field `k`
of characteristic zero with `K_Y` `ℚ`-Cartier, and `S ⊆ Y` an irreducible closed subset of
codimension two with `Y` smooth at its generic point `η_S`. Then the exceptional valuation `w` of
the blow-up of `S` near `η_S`, that is, the valuation of `k(Y)` given on `𝒪_{Y,η_S}` by the
`𝔪`-adic order, is a normalized divisorial valuation with centre `S`, and `a(w; Y, 0) = 2`.

The first two facts are `exists_isCentre_of_codimension_eq_two`. For the log discrepancy, write
`w = ord_D` for a proper divisor `D` over `Y`; restricted to the open `U ∋ η_S` of
`exists_open_divisorOver_blowUp`, `D` has the valuation of the exceptional divisor `E` of the
blow-up of `S ∩ U`, so its discrepancy is `ord_E(π^*τ)/m = 1` for a local generator `τ` of
`ω_U^{⊗m}`, and `a(w; Y, 0) = 1 + 1`. -/
@[mmp "lem_oai4_c2_codim_two_blowup"]
public theorem exists_isCentre_isValuationLogDiscrepancy_two_of_codimension_eq_two
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsPair sY (0 : MMP.Mori.QDivisor Y))
    (S : IrreducibleCloseds Y) (hS : codimension S = 2)
    (hsm : S.isIrreducible.genericPoint ∈ MMP.Mori.smoothLocus sY) :
    ∃ w : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      (∀ (f : Y.presheaf.stalk S.isIrreducible.genericPoint) (n : ℕ),
        w (algebraMap _ Y.functionField f) ≤ WithZero.exp (-(n : ℤ)) ↔
          f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk S.isIrreducible.genericPoint) ^ n) ∧
      MMP.Intersection.IsCentre k sY w S ∧
      IsValuationLogDiscrepancy sY (0 : MMP.Mori.QDivisor Y) w 2 := by
  obtain ⟨-, n, K, hK, hQ⟩ := id hY
  obtain ⟨w, hw, D, hDp, rfl, hDc⟩ :=
    exists_isCentre_of_codimension_eq_two sY hY.1.1 hK.topologicalKrullDim_eq S hS hsm
  obtain ⟨U, hηU, hUn, Dbl, hξ, hDord⟩ :=
    exists_open_divisorOver_blowUp sY hY.1.1 hK.topologicalKrullDim_eq S hS hsm
  set η := S.isIrreducible.genericPoint
  have hηgen : IsGenericPoint η (S : Set Y) :=
    S.isIrreducible.isGenericPoint_genericPoint S.isClosed
  have : Nonempty U := ⟨⟨η, hηU⟩⟩
  have := Opens.isDominant_ι (U.isOpen.dense ⟨η, hηU⟩)
  let x₀ : U.toScheme := ⟨η, hηU⟩
  have hx₀η : U.ι x₀ = η := rfl
  have hDw : D.valuation = Dbl.valuation.comap (functionFieldMap U.ι) :=
    eq_of_forall_le_exp_neg_iff_mem_pow _ hw hξ
  obtain ⟨a₀, ha₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hY hK D
  have hUc : ((D.center : Set Y) ∩ U).Nonempty := ⟨η, by rw [← hDc]; exact hηgen.mem, hηU⟩
  obtain ⟨hY', hf', E', hE', hv', hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff (K := K) ⟨hY.1, hK, hQ⟩ D U hUc
  obtain ⟨hXU, hKU, m, hm, -, V, hV, τ, hτ, hτa⟩ := (hiff a₀).1 ha₀
  -- the restriction of `D` to `U` and the blow-up divisor have the same valuation
  have hvv : (⟨_, D.f ∣_ U, hY', hf', E'⟩ : MMP.Mori.DivisorOver k (U.ι ≫ sY)).valuation =
      Dbl.valuation := by
    have hbij := MMP.Mori.functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤
      ⟨_, Set.mem_univ x₀⟩
    ext g
    obtain ⟨g, rfl⟩ := hbij.2 g
    exact congrArg (fun v => v g) (hv'.symm.trans hDw)
  have hord := MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hXU hUn hvv τ
  -- the centre of the restricted divisor is `x₀`
  have hDη : D.f D.E.genericPoint = η := by
    refine IsGenericPoint.eq ?_ hηgen
    change closure _ = _
    rw [← MMP.Mori.DivisorOver.center_eq_closure_genericPoint, ← hDc]
  have hx₀V : x₀ ∈ V := by
    have hpt : (D.f ∣_ U) E'.genericPoint = x₀ := by
      apply U.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hx₀η, ← hDη, ← hE']
      exact congrArg D.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm
    exact hpt ▸ hV
  have h0 : MMP.Mori.DivisorWithCoeffs.restrictOpen U (0 : MMP.Mori.QDivisor Y) = 0 :=
    Finsupp.comapDomain_zero _
  have hgen : MMP.Mori.GeneratesOn (0 : MMP.Mori.QDivisor U) m V τ := by rwa [h0] at hτ
  have hm1 := hDord m τ ⟨V, hx₀V, hgen⟩
  have ha₁ : a₀ = 1 := by
    rw [hord, hm1] at hτa
    exact mul_left_cancel₀ (by exact_mod_cast hm.ne' : (m : ℚ) ≠ 0) (by rw [hτa]; push_cast; ring)
  subst ha₁
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha₀ hDp
  rw [show (1 : ℝ) + ((1 : ℚ) : ℝ) = 2 by norm_num] at hlog
  exact ⟨D.valuation, hw, ⟨D, hDp, rfl, hDc⟩, ⟨n, D, hDp, rfl, hlog⟩⟩

/-! ### Independence survives the étale extension -/

section EtaleIndependence

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints Topology LocalEtaleDatum

/-- A base change of a morphism that is an isomorphism over `V` is an isomorphism over every
open contained in the preimage of `V`. -/
private theorem isIso_morphismRestrict_pullbackSnd {X Y Y' : Scheme.{0}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) {V : Y.Opens} {W : Y'.Opens} (hW : W ≤ g ⁻¹ᵁ V) (hf : IsIso (f ∣_ V)) :
    IsIso (pullback.snd f g ∣_ W) := by
  have hUY : pullback.snd f g ⁻¹ᵁ W =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ pullback.snd f g ⁻¹ᵁ W := by
    refine (inf_eq_right.mpr ?_).symm
    calc pullback.snd f g ⁻¹ᵁ W ≤ pullback.snd f g ⁻¹ᵁ (g ⁻¹ᵁ V) := Scheme.Hom.preimage_mono _ hW
      _ = pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g) hW le_rfl hUY
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict] at H
  exact H.isIso_snd_of_isIso hf

/-- The base change `π_e` of the resolution along the étale map `q : Y_e ⟶ Y` is an isomorphism
over the smooth locus of `Y_e`. -/
private theorem isBiregular_resolutionMap {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
    {L : Fin b → (genericFibre π T).Modules}
    (hLS : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L) :
    IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY)) := by
  have := hLS.isProjectiveVariety
  have := E.isQuasiProjectiveVariety
  have := E.neighborhood.obj.etale_toBase
  refine isIso_morphismRestrict_pullbackSnd π E.map (V := smoothLocus sY) ?_ hLS.isBiregular
  intro x hx
  exact ((smoothLocus_comp_of_smooth sY E.map).1 x).1 hx

/-! ### Stalks of inverse images -/

section Stalks

variable {X Y : TopCat.{0}}

/-- Naturality of `stalkPushforward` in the presheaf. -/
theorem stalkPushforward_naturality (f : X ⟶ Y) {F G : X.Presheaf (ModuleCat.{0} ℚ)}
    (φ : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map φ) ≫
        G.stalkPushforward _ f x =
      F.stalkPushforward _ f x ≫ (TopCat.Presheaf.stalkFunctor _ x).map φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- The canonical map `F_{f x} ⟶ (f⁻¹F)_x` from the stalk of a sheaf to the stalk of its inverse
image is bijective: it is the inverse of `Stacks.SheafifyStalk.stalkSheafPullbackIso`. -/
theorem bijective_stalkToPullbackStalk (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    (x : X) : Function.Bijective (stalkToPullbackStalk f F x) := by
  rw [show stalkToPullbackStalk f F x = (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv
    from (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm]
  exact (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).symm.toLinearEquiv.bijective

/-- The canonical map from the stalk of a sheaf to the stalk of its inverse image is
injective. -/
theorem injective_stalkToPullbackStalk (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    (x : X) : Function.Injective (stalkToPullbackStalk f F x) :=
  (bijective_stalkToPullbackStalk f F x).1

/-- The germ map of `R^q f_* ℚ` on a class is the sheafification map applied to its germ in the
presheaf `V ↦ H^q(f⁻¹(V); ℚ)`. -/
theorem higherDirectImageGerm_apply (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y)
    (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom c =
      (TopCat.Presheaf.stalkFunctor _ y).map
        (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))
        ((directImagePresheaf f q).germ V y hy c) := rfl

/-- The germ of a restricted class is the germ of the class. -/
theorem higherDirectImageGerm_res (f : X ⟶ Y) (q : ℕ) {V W : Opens Y} (hWV : W ≤ V)
    (y : Y) (hy : y ∈ W) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom
        ((rationalCohomologyMap (preimageInclusion f hWV) q).hom c) =
      (higherDirectImageGerm f q y (hWV hy)).hom c := by
  rw [higherDirectImageGerm_apply, higherDirectImageGerm_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply (directImagePresheaf f q) (homOfLE hWV) y hy c

/-- A class whose germ in `R^q f_* ℚ` vanishes restricts to zero on a smaller neighbourhood. -/
theorem exists_res_eq_zero_of_germ_eq_zero (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y)
    (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q)
    (hc : (higherDirectImageGerm f q y hy).hom c = 0) :
    ∃ (W : Opens Y) (_ : y ∈ W) (hWV : W ≤ V),
      (rationalCohomologyMap (preimageInclusion f hWV) q).hom c = 0 := by
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := ModuleCat.{0} ℚ)
    (𝓕 := directImagePresheaf f q) (p₀ := y)
  have hinj : Function.Injective ((TopCat.Presheaf.stalkFunctor _ y).map
      (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h0 : (directImagePresheaf f q).germ V y hy c = (directImagePresheaf f q).germ V y hy 0 := by
    apply hinj
    rw [higherDirectImageGerm_apply] at hc
    rw [hc, map_zero]
    exact (map_zero (ModuleCat.Hom.hom ((TopCat.Presheaf.stalkFunctor _ y).map
      (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))))).symm
  obtain ⟨W, hyW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (directImagePresheaf f q) y hy hy c 0 h0
  exact ⟨W, hyW, iU.le, e.trans (map_zero _)⟩

/-- Naturality of `stalkToPullbackStalk` in the sheaf. -/
theorem stalkToPullbackStalk_naturality (f : X ⟶ Y)
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : F ⟶ G) (x : X) :
    stalkToPullbackStalk f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ Y).map φ) ≫
        stalkToPullbackStalk f G x := by
  have hn := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality φ
  have hn' : (TopCat.Sheaf.forget _ Y).map φ ≫ (TopCat.Sheaf.forget _ Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app G) =
      (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ X).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) := by
    have := congrArg (fun m ↦ (TopCat.Sheaf.forget _ Y).map m) hn
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at this
    exact this
  unfold stalkToPullbackStalk
  erw [Category.assoc, ← stalkPushforward_naturality f, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← hn', CategoryTheory.Functor.map_comp, Category.assoc]

/-- The map on stalks induced by the sheafification of a morphism of the presheaves
`V ↦ H^q(f⁻¹(V); ℚ)`, on germs of classes. -/
theorem stalkFunctor_map_presheafToSheaf_germ {X X' : TopCat.{0}} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (q : ℕ) (ψ : directImagePresheaf p q ⟶ directImagePresheaf p' q)
    {V : Opens Y} (y : Y) (hy : y ∈ V) (c : rationalCohomology (preimageSpace p V) q) :
    (TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ Y).map
        ((presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map ψ))
        ((higherDirectImageGerm p q y hy).hom c) =
      (higherDirectImageGerm p' q y hy).hom (ψ.app (Opposite.op V) c) := by
  have hm : higherDirectImageGerm p q y hy ≫ (TopCat.Presheaf.stalkFunctor _ y).map
      ((TopCat.Sheaf.forget _ Y).map
        ((presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map ψ)) =
      ψ.app (Opposite.op V) ≫ higherDirectImageGerm p' q y hy := by
    unfold higherDirectImageGerm
    have h := toSheafify_naturality (Opens.grothendieckTopology Y) ψ
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← h, CategoryTheory.Functor.map_comp,
      ← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
  exact ConcreteCategory.congr_hom hm c

end Stalks

/-- The restriction map `r_t` on the germ at `t` of a class on `π⁻¹(V)` is the germ of its
restriction to `π⁻¹(V) ∩ π⁻¹(Y_reg) ≅ j⁻¹(V)`. -/
theorem localSystemRestrictionFibre_germ {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (hπ : IsBiregular π (smoothLocus sY))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    (localSystemRestrictionFibre sY hπ To t).hom
        ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)) =
      (stalkToPullbackStalk (curveOpenInclusion sY To) (regularHigherDirectImage sY 2) t).hom
        ((higherDirectImageGerm (regularInclusion sY) 2 _ hV).hom
          ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
            (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
            (regularSection_analyticMap_comp sY hπ) V) 2).hom α)) := by
  have h := ConcreteCategory.congr_hom (stalkToPullbackStalk_naturality
    (curveOpenInclusion sY To) (resolutionRestriction sY hπ 2) t)
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  unfold localSystemRestrictionFibre localSystemRestriction
  erw [h]
  exact congrArg (fun z ↦ (stalkToPullbackStalk (curveOpenInclusion sY To)
    (regularHigherDirectImage sY 2) t).hom z)
    (stalkFunctor_map_presheafToSheaf_germ _ _ 2 _ _ hV α)

/-! ### Complex points of open subschemes -/

noncomputable section OpenPoints

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The realization of the inclusion of an open subscheme is an open embedding. -/
private theorem isOpenEmbedding_realize_ι (sX : X ⟶ Spec (.of ℂ)) (U : X.Opens) :
    IsOpenEmbedding (realize (sX := U.ι ≫ sX) (sY := sX) U.ι rfl) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  let : (U : Scheme.{0}).Over (Spec (.of ℂ)) := ⟨U.ι ≫ sX⟩
  have : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  exact (homeomorphUnderlyingSpace (X := X)).symm.isOpenEmbedding.comp
    ((MMP.UnderlyingSpace.isOpenEmbedding_map_of_isOpenImmersion (K := ℂ)
      U.ι).comp (homeomorphUnderlyingSpace (X := (U : Scheme.{0}))).isOpenEmbedding)

/-- A `ℂ`-point of `X` lying in the open `U`, as a `ℂ`-point of `U`. -/
private def liftPoint (U : X.Opens) (x : ComplexPoints sX)
    (hx : Set.range x.hom.base ⊆ (U : Set X)) : ComplexPoints (U.ι ≫ sX) :=
  ⟨IsOpenImmersion.lift U.ι x.hom (by rwa [Scheme.Opens.range_ι]), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, x.hom_comp_structure]⟩

private theorem realize_liftPoint (U : X.Opens) (x : ComplexPoints sX)
    (hx : Set.range x.hom.base ⊆ (U : Set X)) :
    realize (sX := U.ι ≫ sX) (sY := sX) U.ι rfl (liftPoint U x hx) = x := by
  ext1
  exact IsOpenImmersion.lift_fac _ _ _

end OpenPoints

/-! ### The étale map on smooth loci and on preimages -/

noncomputable section EtaleSmooth

variable {Ye Y : Scheme.{0}} (q : Ye ⟶ Y) (sY : Y ⟶ Spec (.of ℂ)) [Etale q]
  [LocallyOfFiniteType sY] [QuasiCompact sY] [QuasiCompact (q ≫ sY)]

private theorem mem_smoothLocus_comp_iff' (y : Ye) :
    y ∈ smoothLocus (q ≫ sY) ↔ q.base y ∈ smoothLocus sY :=
  (smoothLocus_comp_of_smooth sY q).1 y

/-- The étale map `q` restricted to the smooth loci `(Y_e)_reg ⟶ Y_reg`. -/
private def regularLift : (smoothLocus (q ≫ sY) : Scheme.{0}) ⟶ smoothLocus sY :=
  IsOpenImmersion.lift (smoothLocus sY).ι ((smoothLocus (q ≫ sY)).ι ≫ q) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (mem_smoothLocus_comp_iff' q sY _).1 z.2)

@[reassoc]
private theorem regularLift_ι :
    regularLift q sY ≫ (smoothLocus sY).ι = (smoothLocus (q ≫ sY)).ι ≫ q :=
  IsOpenImmersion.lift_fac _ _ _

private theorem regularLift_comp_structure :
    regularLift q sY ≫ (smoothLocus sY).ι ≫ sY = (smoothLocus (q ≫ sY)).ι ≫ q ≫ sY := by
  rw [regularLift_ι_assoc]

/-- The realization `q^an : Y_e^an ⟶ Y^an`. -/
private abbrev etaleAnalyticMap : analyticSpace (q ≫ sY) ⟶ analyticSpace sY := analyticMap q rfl

private theorem regularInclusion_regularLift
    (z : analyticSpace ((smoothLocus (q ≫ sY)).ι ≫ q ≫ sY)) :
    regularInclusion sY (analyticMap (regularLift q sY) (regularLift_comp_structure q sY) z) =
      etaleAnalyticMap q sY (regularInclusion (q ≫ sY) z) := by
  ext1
  change (z.hom ≫ regularLift q sY) ≫ (smoothLocus sY).ι =
    (z.hom ≫ (smoothLocus (q ≫ sY)).ι) ≫ q
  rw [Category.assoc, regularLift_ι, Category.assoc]

private theorem mem_regularPreimage (V : Opens (analyticSpace sY))
    (z : preimageSpace (regularInclusion (q ≫ sY)) ((Opens.map (etaleAnalyticMap q sY)).obj V)) :
    analyticMap (regularLift q sY) (regularLift_comp_structure q sY) z.1 ∈
      (regularInclusion sY) ⁻¹' (V : Set (analyticSpace sY)) := by
  change regularInclusion sY _ ∈ V
  rw [regularInclusion_regularLift]
  exact z.2

/-- The map `j_e⁻¹(q^{an,-1}(V)) ⟶ j⁻¹(V)` induced by `q` on smooth loci. -/
private def regularPreimageMap (V : Opens (analyticSpace sY)) :
    preimageSpace (regularInclusion (q ≫ sY)) ((Opens.map (etaleAnalyticMap q sY)).obj V) ⟶
      preimageSpace (regularInclusion sY) V :=
  TopCat.ofHom ⟨fun z ↦ ⟨analyticMap (regularLift q sY) (regularLift_comp_structure q sY) z.1,
      mem_regularPreimage q sY V z⟩,
    ((analyticMap (regularLift q sY) (regularLift_comp_structure q sY)).hom.continuous.comp
      continuous_subtype_val).subtype_mk _⟩

/-- **Independence of germs is preserved by the étale map.** Since `q^an` is a local
homeomorphism, a class on `j⁻¹(V)` whose pullback to `j_e⁻¹(q^{an,-1}(V))` has vanishing germ
at `p'` has vanishing germ at `q^an(p')`. -/
private theorem linearIndependent_germ_regularPreimageMap
    (hlh : IsLocalHomeomorph (etaleAnalyticMap q sY)) {b : ℕ} (p' : analyticSpace (q ≫ sY))
    {p : analyticSpace sY} (hpq : etaleAnalyticMap q sY p' = p)
    {V : Opens (analyticSpace sY)} (hp₀ : p ∈ V)
    (hp' : p' ∈ (Opens.map (etaleAnalyticMap q sY)).obj V)
    (γ : Fin b → rationalCohomology (preimageSpace (regularInclusion sY) V) 2)
    (hγ : LinearIndependent ℚ fun i ↦
      (higherDirectImageGerm (regularInclusion sY) 2 p hp₀).hom (γ i)) :
    LinearIndependent ℚ fun i ↦ (higherDirectImageGerm (regularInclusion (q ≫ sY)) 2 p' hp').hom
      ((rationalCohomologyMap (regularPreimageMap q sY V) 2).hom (γ i)) := by
  subst hpq
  have hp : etaleAnalyticMap q sY p' ∈ V := hp₀
  rw [Fintype.linearIndependent_iff] at hγ ⊢
  intro g hg
  apply hγ g
  set Γ := ∑ i, g i • γ i with hΓdef
  have hΓ : (higherDirectImageGerm (regularInclusion (q ≫ sY)) 2 p' hp').hom
      ((rationalCohomologyMap (regularPreimageMap q sY V) 2).hom Γ) = 0 := by
    rw [hΓdef, map_sum, map_sum]
    simpa only [map_smul] using hg
  have hsum : ∑ i, g i • (higherDirectImageGerm (regularInclusion sY) 2 _ hp).hom (γ i) =
      (higherDirectImageGerm (regularInclusion sY) 2 _ hp).hom Γ := by
    rw [hΓdef, map_sum]
    simp only [map_smul]
  rw [hsum]
  obtain ⟨W', hpW', hW'V, hres⟩ := exists_res_eq_zero_of_germ_eq_zero _ 2 p' _ _ hΓ
  obtain ⟨e, hpe, he⟩ := hlh p'
  have heq : ∀ x, etaleAnalyticMap q sY x = e x := fun x ↦ congrFun he x
  let W : Opens (analyticSpace sY) :=
    ⟨e '' (e.source ∩ (W' : Set _)), e.isOpen_image_source_inter W'.2⟩
  have hpW : etaleAnalyticMap q sY p' ∈ W := ⟨p', ⟨hpe, hpW'⟩, (heq p').symm⟩
  have hWV : W ≤ V := by
    rintro _ ⟨x, ⟨-, hx⟩, rfl⟩
    rw [← heq]
    exact hW'V hx
  rw [← higherDirectImageGerm_res _ 2 hWV _ hpW]
  -- the local section `j⁻¹(W) ⟶ j_e⁻¹(W')`
  have hsymm : ∀ z : preimageSpace (regularInclusion sY) W,
      e.symm (regularInclusion sY z.1) ∈ e.source ∩ (W' : Set _) ∧
        e (e.symm (regularInclusion sY z.1)) = regularInclusion sY z.1 := by
    rintro ⟨z, x, hx, hxz⟩
    change e x = regularInclusion sY z at hxz
    rw [← hxz, e.left_inv hx.1]
    exact ⟨hx, rfl⟩
  have hrange : ∀ z : preimageSpace (regularInclusion sY) W,
      Set.range (e.symm (regularInclusion sY z.1)).hom.base ⊆
        (smoothLocus (q ≫ sY) : Set Ye) := by
    rintro z _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, mem_smoothLocus_comp_iff']
    have h1 : (e.symm (regularInclusion sY z.1)).hom ≫ q = z.1.hom ≫ (smoothLocus sY).ι :=
      congrArg ComplexPoints.hom ((heq _).trans (hsymm z).2)
    have h2 := congrArg (fun m ↦ m.base u) h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    rw [h2, ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  let sec : preimageSpace (regularInclusion sY) W ⟶
      preimageSpace (regularInclusion (q ≫ sY)) W' :=
    TopCat.ofHom ⟨fun z ↦ ⟨liftPoint _ _ (hrange z), by
        change realize (smoothLocus (q ≫ sY)).ι rfl _ ∈ W'
        rw [realize_liftPoint]
        exact (hsymm z).1.2⟩, by
      apply Continuous.subtype_mk
      rw [(isOpenEmbedding_realize_ι (q ≫ sY) (smoothLocus (q ≫ sY))).isInducing.continuous_iff]
      have : (realize (smoothLocus (q ≫ sY)).ι rfl ∘ fun z : preimageSpace
          (regularInclusion sY) W ↦ liftPoint _ _ (hrange z)) =
          fun z ↦ e.symm (regularInclusion sY z.1) :=
        funext fun z ↦ realize_liftPoint _ _ (hrange z)
      rw [this]
      refine e.continuousOn_symm.comp_continuous ?_ fun z ↦ ?_
      · exact (regularInclusion sY).hom.continuous.comp continuous_subtype_val
      · rw [← (hsymm z).2]
        exact e.map_source (hsymm z).1.1⟩
  have hcomp : preimageInclusion (regularInclusion sY) hWV =
      sec ≫ preimageInclusion (regularInclusion (q ≫ sY)) hW'V ≫ regularPreimageMap q sY V := by
    refine TopCat.ext fun z ↦ ?_
    apply Subtype.ext
    apply (isOpenEmbedding_realize_ι sY (smoothLocus sY)).injective
    change regularInclusion sY z.1 = regularInclusion sY
      (analyticMap (regularLift q sY) (regularLift_comp_structure q sY) (liftPoint _ _ (hrange z)))
    rw [regularInclusion_regularLift, heq]
    change _ = e (realize (smoothLocus (q ≫ sY)).ι rfl (liftPoint _ _ (hrange z)))
    rw [realize_liftPoint, (hsymm z).2]
  rw [hcomp, rationalCohomologyMap_comp, rationalCohomologyMap_comp, ModuleCat.comp_apply,
    ModuleCat.comp_apply, hres, map_zero, map_zero]

end EtaleSmooth

/-! ### The base-changed resolution over the smooth locus -/

noncomputable section BaseChange

/-- A morphism to `Ỹ` lying over the smooth locus factors through the inverse of `π` there. -/
private theorem eq_comp_regularSection {Y Yt Z : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    {π : Yt ⟶ Y} (hπ : IsBiregular π (smoothLocus sY)) (y : Z ⟶ Yt)
    (w : Z ⟶ smoothLocus sY) (h : y ≫ π = w ≫ (smoothLocus sY).ι) :
    y = w ≫ regularSection sY hπ := by
  have : IsIso (π ∣_ smoothLocus sY) := hπ
  have hr : Set.range y.base ⊆ Set.range (π ⁻¹ᵁ smoothLocus sY).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change π.base (y.base z) ∈ smoothLocus sY
    have h2 := congrArg (fun m ↦ m.base z) h
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    rw [h2, ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  let y' := IsOpenImmersion.lift (π ⁻¹ᵁ smoothLocus sY).ι y hr
  have hy' : y' ≫ (π ⁻¹ᵁ smoothLocus sY).ι = y := IsOpenImmersion.lift_fac _ _ _
  have hw : y' ≫ (π ∣_ smoothLocus sY) = w := by
    rw [← cancel_mono (smoothLocus sY).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      hy', h]
  unfold regularSection
  rw [← hw, Category.assoc]
  erw [IsIso.hom_inv_id_assoc]
  exact hy'.symm

variable {Ye Y Yt : Scheme.{0}} (q : Ye ⟶ Y) (sY : Y ⟶ Spec (.of ℂ)) (π : Yt ⟶ Y) [Etale q]
  [LocallyOfFiniteType sY] [QuasiCompact sY] [QuasiCompact (q ≫ sY)]

omit [Etale q] [LocallyOfFiniteType sY] [QuasiCompact sY] [QuasiCompact (q ≫ sY)] in
private theorem pullbackFst_comp_structure :
    pullback.fst π q ≫ π ≫ sY = pullback.snd π q ≫ q ≫ sY := by
  rw [← Category.assoc, pullback.condition, Category.assoc]

/-- The inverses of `π_e` and `π` over the smooth loci are compatible with `Ỹ_e ⟶ Ỹ`. -/
private theorem regularSection_pullbackFst (hπ : IsBiregular π (smoothLocus sY))
    (hπe : IsBiregular (pullback.snd π q) (smoothLocus (q ≫ sY))) :
    regularSection (q ≫ sY) hπe ≫ pullback.fst π q = regularLift q sY ≫ regularSection sY hπ := by
  apply eq_comp_regularSection
  rw [Category.assoc, pullback.condition, ← Category.assoc, regularSection_comp, regularLift_ι]

omit [Etale q] [LocallyOfFiniteType sY] [QuasiCompact sY] [QuasiCompact (q ≫ sY)] in
private theorem mem_resolutionPreimage (V : Opens (analyticSpace sY))
    (x : preimageSpace (resolutionAnalyticMap (q ≫ sY) (pullback.snd π q))
      ((Opens.map (etaleAnalyticMap q sY)).obj V)) :
    analyticMap (pullback.fst π q) (pullbackFst_comp_structure q sY π) x.1 ∈
      (resolutionAnalyticMap sY π) ⁻¹' (V : Set (analyticSpace sY)) := by
  have h := x.2
  change etaleAnalyticMap q sY (resolutionAnalyticMap (q ≫ sY) (pullback.snd π q) x.1) ∈ V at h
  change resolutionAnalyticMap sY π _ ∈ V
  convert h using 1
  ext1
  change (x.1.hom ≫ pullback.fst π q) ≫ π = (x.1.hom ≫ pullback.snd π q) ≫ q
  rw [Category.assoc, pullback.condition, Category.assoc]

/-- The map `π_e⁻¹(q^{an,-1}(V)) ⟶ π⁻¹(V)` induced by `Ỹ_e ⟶ Ỹ`. -/
private def resolutionPreimageMap (V : Opens (analyticSpace sY)) :
    preimageSpace (resolutionAnalyticMap (q ≫ sY) (pullback.snd π q))
        ((Opens.map (etaleAnalyticMap q sY)).obj V) ⟶
      preimageSpace (resolutionAnalyticMap sY π) V :=
  TopCat.ofHom ⟨fun x ↦ ⟨analyticMap (pullback.fst π q) (pullbackFst_comp_structure q sY π) x.1,
      mem_resolutionPreimage q sY π V x⟩,
    ((analyticMap (pullback.fst π q) (pullbackFst_comp_structure q sY π)).hom.continuous.comp
      continuous_subtype_val).subtype_mk _⟩

/-- Restricting to the smooth locus commutes with the maps induced by `q`. -/
private theorem preimageRestrict_resolutionPreimageMap (hπ : IsBiregular π (smoothLocus sY))
    (hπe : IsBiregular (pullback.snd π q) (smoothLocus (q ≫ sY))) (V : Opens (analyticSpace sY)) :
    preimageRestrict (resolutionAnalyticMap (q ≫ sY) (pullback.snd π q))
        (analyticMap (regularSection (q ≫ sY) hπe)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp (q ≫ sY) hπe)
        ((Opens.map (etaleAnalyticMap q sY)).obj V) ≫ resolutionPreimageMap q sY π V =
      regularPreimageMap q sY V ≫ preimageRestrict (resolutionAnalyticMap sY π)
        (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hπ) V := by
  refine TopCat.ext fun z ↦ Subtype.ext ?_
  ext1
  change (z.1.hom ≫ regularSection (q ≫ sY) hπe) ≫ pullback.fst π q =
    (z.1.hom ≫ regularLift q sY) ≫ regularSection sY hπ
  rw [Category.assoc, Category.assoc, regularSection_pullbackFst]

end BaseChange

/-! ### Change of coefficients and pullback -/

open MMP.SingularCochain in
/-- Change of coefficients `ℤ → ℚ` commutes with pullback of singular cohomology classes. -/
private theorem mapCoeff_map {X' X : TopCat.{0}} (g : X' ⟶ X)
    (c : singularCohomology ℤ X 2) :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        ((MMP.relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := Set.univᶜ)
          (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) ((2 : ℕ) : ℤ)).hom c) =
      (rationalCohomologyMap g 2).hom (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c) := by
  have e : ∀ {Z : TopCat.{0}} (x : singularCohomology ℤ Z 2),
      relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Z) 2
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 x) =
        singularCohomology.relCohomologyMap (Int.castRingHom ℚ) _ 2
          (relativeSingularCohomologyEquiv ℤ _ 2 x) := fun x ↦ by
    simp only [singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.apply_symm_apply]
  have h1 := relativeSingularCohomologyEquiv_map (R := ℚ) g (A' := (Set.univᶜ : Set X'))
    (A := (Set.univᶜ : Set X)) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2
    (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c)
  have h2 := relativeSingularCohomologyEquiv_map (R := ℤ) g (A' := (Set.univᶜ : Set X'))
    (A := (Set.univᶜ : Set X)) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2 c
  apply (relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set X') 2).injective
  refine (e _).trans (Eq.trans ?_ h1.symm)
  rw [h2, e]
  induction (relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set X) 2 c) using
    Submodule.Quotient.induction_on with
  | H φ => rfl

/-! ### Fibres of the base-changed resolution -/

noncomputable section Fibres

variable {Ye Y Yt : Scheme.{0}} {q : Ye ⟶ Y} {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y}
  {T : IrreducibleCloseds Y} {T' : IrreducibleCloseds Ye} {To : (curveScheme T').Opens}
  {T₁ : (curveScheme T).Opens} {t' : ComplexPoints (To.ι ≫ curveι T' ≫ q ≫ sY)}
  {t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY)}

/-- The isomorphism-to-be `F_{t'} ⟶ F_t` from the fibre of `π_e` over `t'` to the fibre of `π`
over `t = q(t')`, which is the identity on `Spec ℂ`. -/
private def fibreMap (ht : t'.hom ≫ To.ι ≫ curveι T' ≫ q = t.hom ≫ T₁.ι ≫ curveι T) :
    pointFibre (q ≫ sY) (pullback.snd π q) To t' ⟶ pointFibre sY π T₁ t :=
  pullback.lift (pointFibreFst _ _ To t' ≫ pullback.fst π q) (pointFibreSnd _ _ To t') (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointFibreFst_comp,
      Category.assoc, Category.assoc, Category.assoc, ← ht])

private theorem fibreMap_snd (ht : t'.hom ≫ To.ι ≫ curveι T' ≫ q = t.hom ≫ T₁.ι ≫ curveι T) :
    fibreMap ht ≫ pointFibreSnd sY π T₁ t = pointFibreSnd _ _ To t' :=
  pullback.lift_snd _ _ _

private theorem fibreMap_fst (ht : t'.hom ≫ To.ι ≫ curveι T' ≫ q = t.hom ≫ T₁.ι ≫ curveι T) :
    fibreMap ht ≫ pointFibreFst sY π T₁ t = pointFibreFst _ _ To t' ≫ pullback.fst π q :=
  pullback.lift_fst _ _ _

/-- The realization `F_{t'}(ℂ) ⟶ F_t(ℂ)` of `fibreMap`. -/
private abbrev fibreAnalyticMap
    (ht : t'.hom ≫ To.ι ≫ curveι T' ≫ q = t.hom ≫ T₁.ι ≫ curveι T) :
    analyticSpace (pointFibre (q ≫ sY) (pullback.snd π q) To t' ↘ Spec (.of ℂ)) ⟶
      analyticSpace (pointFibre sY π T₁ t ↘ Spec (.of ℂ)) :=
  analyticMap (fibreMap ht) (fibreMap_snd ht)

/-- **The Chern class on the fibre is transported along `F_{t'} ⟶ F_t`.** -/
private theorem pointFibreChernClass_eq_of_iso
    (ht : t'.hom ≫ To.ι ≫ curveι T' ≫ q = t.hom ≫ T₁.ι ≫ curveι T)
    (M : (pointFibre (q ≫ sY) (pullback.snd π q) To t').Modules)
    (N : (pointFibre sY π T₁ t).Modules)
    [SheafOfModules.IsInvertible (pointFibre sY π T₁ t).presheaf
      (pointFibre sY π T₁ t).ringCatSheaf.2 N]
    (e : M ≅ (Scheme.Modules.pullback (fibreMap ht)).obj N) :
    ∃ _ : SheafOfModules.IsInvertible (pointFibre (q ≫ sY) (pullback.snd π q) To t').presheaf
        (pointFibre (q ≫ sY) (pullback.snd π q) To t').ringCatSheaf.2 M,
      pointFibreChernClass (q ≫ sY) (pullback.snd π q) To t' M =
        (rationalCohomologyMap (fibreAnalyticMap ht) 2).hom (pointFibreChernClass sY π T₁ t N) := by
  have hN' : SheafOfModules.IsInvertible (pointFibre (q ≫ sY) (pullback.snd π q) To t').presheaf
      (pointFibre (q ≫ sY) (pullback.snd π q) To t').ringCatSheaf.2
      ((Scheme.Modules.pullback (fibreMap ht)).obj N) :=
    MMP.Mori.isInvertible_pullback_obj _ _
  have hM : SheafOfModules.IsInvertible (pointFibre (q ≫ sY) (pullback.snd π q) To t').presheaf
      (pointFibre (q ≫ sY) (pullback.snd π q) To t').ringCatSheaf.2 M :=
    Stacks.UFDExtensionGlobal.isInvertible_of_iso e.symm hN'
  refine ⟨hM, ?_⟩
  unfold pointFibreChernClass
  rw [algebraicFirstChernClass_eq_of_iso e, algebraicFirstChernClass_pullback (fibreMap ht)
    (fibreAnalyticMap ht) (fun _ ↦ rfl) N]
  exact mapCoeff_map _ _

end Fibres

/-- The inclusion of the fibre `F_{t'}` followed by `Ỹ_e ⟶ Ỹ` is `F_{t'} ⟶ F_t` followed by the
inclusion of `F_t`. -/
private theorem pointFibreInclusion_resolutionPreimageMap {Ye Y Yt : Scheme.{0}} {q : Ye ⟶ Y}
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {T : IrreducibleCloseds Y}
    {T' : IrreducibleCloseds Ye} {To : (curveScheme T').Opens} {T₁ : (curveScheme T).Opens}
    {t' : ComplexPoints (To.ι ≫ curveι T' ≫ q ≫ sY)} {t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY)}
    (ht : t'.hom ≫ To.ι ≫ curveι T' ≫ q = t.hom ≫ T₁.ι ≫ curveι T)
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY T₁ t ∈ V)
    (hV' : curveOpenInclusion (q ≫ sY) To t' ∈ (Opens.map (analyticMap q rfl)).obj V) :
    pointFibreInclusion (q ≫ sY) (pullback.snd π q) To t' hV' ≫
        resolutionPreimageMap q sY π V =
      fibreAnalyticMap ht ≫ pointFibreInclusion sY π T₁ t hV := by
  refine TopCat.ext fun x ↦ Subtype.ext ?_
  ext1
  change (x.hom ≫ pointFibreFst _ _ To t') ≫ pullback.fst π q =
    (x.hom ≫ fibreMap ht) ≫ pointFibreFst sY π T₁ t
  rw [Category.assoc, Category.assoc, fibreMap_fst]

/-- **Transport of punctured independence along the étale datum**, from the identification of
the restricted bundles on the fibres over a dense open of `T'` and the local homeomorphism
property of `q^an`. -/
private theorem exists_dense_linearIndependent_of_fibre_iso {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
    {L : Fin b → (genericFibre π T).Modules}
    (hLS : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L)
    (hπe : IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY)))
    (hlh : IsLocalHomeomorph (analyticMap (sX := E.map ≫ sY) (sY := sY) E.map rfl))
    (T₁ : (curveScheme T).Opens) (𝓛 : Fin b → (adaptedFamily π T₁).Modules)
    (hfib : ∀ t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY),
      ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY T₁ t ∈ V)
        (α : Fin b → rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
        (∀ i, ∃ _ : SheafOfModules.IsInvertible (pointFibre sY π T₁ t).presheaf
            (pointFibre sY π T₁ t).ringCatSheaf.2
            ((Scheme.Modules.pullback (pointFibreToFamily sY π T₁ t)).obj (𝓛 i)),
          (rationalCohomologyMap (pointFibreInclusion sY π T₁ t hV) 2).hom (α i) =
            pointFibreChernClass sY π T₁ t
              ((Scheme.Modules.pullback (pointFibreToFamily sY π T₁ t)).obj (𝓛 i))) ∧
        LinearIndependent ℚ fun i ↦ (localSystemRestrictionFibre sY hLS.isBiregular T₁ t).hom
          ((stalkToPullbackStalk (curveOpenInclusion sY T₁) (resolutionHigherDirectImage sY π 2)
            t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom (α i))))
    (hKA : ∃ (To : (curveScheme E.curve).Opens), Dense (To : Set (curveScheme E.curve)) ∧
      ∀ t' : ComplexPoints (To.ι ≫ curveι E.curve ≫ E.map ≫ sY),
        ∃ (t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY))
          (ht : t'.hom ≫ To.ι ≫ curveι E.curve ≫ E.map = t.hom ≫ T₁.ι ≫ curveι T),
          ∀ i, Nonempty ((Scheme.Modules.pullback
              (pointFibreFst (E.map ≫ sY) E.resolutionMap To t')).obj (E.bundle i) ≅
            (Scheme.Modules.pullback (fibreMap ht)).obj
              ((Scheme.Modules.pullback (pointFibreToFamily sY π T₁ t)).obj (𝓛 i)))) :
    ∃ (To : (curveScheme E.curve).Opens), Dense (To : Set (curveScheme E.curve)) ∧
      ∀ t : ComplexPoints (To.ι ≫ curveι E.curve ≫ E.map ≫ sY),
        ∃ (V : Opens (analyticSpace (E.map ≫ sY)))
          (hV : curveOpenInclusion (E.map ≫ sY) To t ∈ V)
          (α : Fin b → rationalCohomology
            (preimageSpace (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap) V) 2),
          (∀ i, ∃ _ : SheafOfModules.IsInvertible
              (pointFibre (E.map ≫ sY) E.resolutionMap To t).presheaf
              (pointFibre (E.map ≫ sY) E.resolutionMap To t).ringCatSheaf.2
              ((Scheme.Modules.pullback
                (pointFibreFst (E.map ≫ sY) E.resolutionMap To t)).obj (E.bundle i)),
            (rationalCohomologyMap
                (pointFibreInclusion (E.map ≫ sY) E.resolutionMap To t hV) 2).hom (α i) =
              pointFibreChernClass (E.map ≫ sY) E.resolutionMap To t
                ((Scheme.Modules.pullback
                  (pointFibreFst (E.map ≫ sY) E.resolutionMap To t)).obj (E.bundle i))) ∧
          LinearIndependent ℚ fun i ↦
            (localSystemRestrictionFibre (E.map ≫ sY) hπe To t).hom
              ((stalkToPullbackStalk (curveOpenInclusion (E.map ≫ sY) To)
                (resolutionHigherDirectImage (E.map ≫ sY) E.resolutionMap 2) t).hom
                ((higherDirectImageGerm (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap)
                  2 _ hV).hom (α i))) := by
  have := hLS.isProjectiveVariety
  have := E.isQuasiProjectiveVariety
  obtain ⟨To, hTo, hKA⟩ := hKA
  refine ⟨To, hTo, fun t' ↦ ?_⟩
  obtain ⟨t, ht, hiso⟩ := hKA t'
  obtain ⟨V, hV, α, hα, hind⟩ := hfib t
  have hp : etaleAnalyticMap E.map sY (curveOpenInclusion (E.map ≫ sY) To t') =
      curveOpenInclusion sY T₁ t := by
    ext1
    change (t'.hom ≫ To.ι ≫ curveι E.curve) ≫ E.map = t.hom ≫ T₁.ι ≫ curveι T
    rw [← ht]
    simp only [Category.assoc]
  have hV' : curveOpenInclusion (E.map ≫ sY) To t' ∈
      (Opens.map (etaleAnalyticMap E.map sY)).obj V := by
    change etaleAnalyticMap E.map sY _ ∈ V
    rw [hp]
    exact hV
  refine ⟨_, hV', fun i ↦ (rationalCohomologyMap (resolutionPreimageMap E.map sY π V) 2).hom
    (α i), fun i ↦ ?_, ?_⟩
  · obtain ⟨hinv, hαi⟩ := hα i
    obtain ⟨e⟩ := hiso i
    obtain ⟨hM, hc⟩ := pointFibreChernClass_eq_of_iso ht _ _ e
    refine ⟨hM, ?_⟩
    rw [hc, ← hαi, ← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, ← ModuleCat.comp_apply,
      ← rationalCohomologyMap_comp, pointFibreInclusion_resolutionPreimageMap ht hV hV']
  · have hind' : LinearIndependent ℚ fun i ↦
        (higherDirectImageGerm (regularInclusion sY) 2 _ hV).hom
          ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
            (analyticMap (regularSection sY hLS.isBiregular)
              (by rw [← Category.assoc, regularSection_comp]))
            (regularSection_analyticMap_comp sY hLS.isBiregular) V) 2).hom (α i)) := by
      refine LinearIndependent.of_comp (stalkToPullbackStalk (curveOpenInclusion sY T₁)
        (regularHigherDirectImage sY 2) t).hom ?_
      have e := funext fun i ↦ localSystemRestrictionFibre_germ sY hLS.isBiregular T₁ t hV (α i)
      rw [e] at hind
      exact hind
    have h3 := linearIndependent_germ_regularPreimageMap E.map sY hlh _ hp hV hV' _ hind'
    have h4 := LinearIndependent.map' h3 (stalkToPullbackStalk
      (curveOpenInclusion (E.map ≫ sY) To) (regularHigherDirectImage (E.map ≫ sY) 2) t').hom
      (LinearMap.ker_eq_bot.2 (injective_stalkToPullbackStalk _ _ _))
    have e := funext fun i ↦ localSystemRestrictionFibre_germ (E.map ≫ sY) hπe To t' hV'
      ((rationalCohomologyMap (resolutionPreimageMap E.map sY π V) 2).hom (α i))
    refine e ▸ ?_
    have e2 : ∀ i, (rationalCohomologyMap (preimageRestrict
        (resolutionAnalyticMap (E.map ≫ sY) (pullback.snd π E.map))
        (analyticMap (regularSection (E.map ≫ sY) hπe)
          (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp (E.map ≫ sY) hπe)
        ((Opens.map (etaleAnalyticMap E.map sY)).obj V)) 2).hom
        ((rationalCohomologyMap (resolutionPreimageMap E.map sY π V) 2).hom (α i)) =
        (rationalCohomologyMap (regularPreimageMap E.map sY V) 2).hom
          ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
            (analyticMap (regularSection sY hLS.isBiregular)
              (by rw [← Category.assoc, regularSection_comp]))
            (regularSection_analyticMap_comp sY hLS.isBiregular) V) 2).hom (α i)) := fun i ↦ by
      rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, ← ModuleCat.comp_apply,
        ← rationalCohomologyMap_comp, preimageRestrict_resolutionPreimageMap]
    have h5 := funext fun i ↦ congrArg (fun z ↦ (stalkToPullbackStalk
      (curveOpenInclusion (E.map ≫ sY) To) (regularHigherDirectImage (E.map ≫ sY) 2) t').hom
      ((higherDirectImageGerm (regularInclusion (E.map ≫ sY)) 2 _ hV').hom z)) (e2 i)
    rw [h5]
    exact h4

/-! ### The curve `T'` over `T` -/

/-- A point of the domain of a closed embedding whose image has closure the range is a generic
point of the domain. -/
private theorem closure_singleton_eq_univ_of_isClosedEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {e : A → B} (he : IsClosedEmbedding e) {x : A}
    (hx : closure {e x} = Set.range e) : closure ({x} : Set A) = Set.univ := by
  rw [he.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hx,
    Set.preimage_range]

/-- The curve `T'` maps into `T`, and the dense open `T¹` of `T` pulls back to a dense open of
`T'` on which `T' ⟶ Y` factors through `T¹`. -/
private theorem exists_curveOpen_factor {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ} {L : Fin b → (genericFibre π T).Modules}
    (E : LocalEtaleDatum sY T π L) (T₁ : (curveScheme T).Opens)
    (hT₁ : Dense (T₁ : Set (curveScheme T))) :
    ∃ (W : (curveScheme E.curve).Opens) (φ : (W : Scheme.{0}) ⟶ T₁),
      Dense (W : Set (curveScheme E.curve)) ∧
        φ ≫ T₁.ι ≫ curveι T = W.ι ≫ curveι E.curve ≫ E.map := by
  have hrT : Set.range (curveι T).base = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hrT' : Set.range (curveι E.curve).base = closure {E.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hηT : closure {localSettingGenericPoint T} = (T : Set Y) :=
    (T.isIrreducible.isGenericPoint_genericPoint T.isClosed)
  set g := curveι E.curve ≫ E.map with hg
  have hrange : closure (Set.range g.base) ⊆ (T : Set Y) := by
    refine T.isClosed.closure_subset_iff.2 ?_
    rintro _ ⟨z, rfl⟩
    have hz : (curveι E.curve).base z ∈ closure {E.point} := hrT' ▸ ⟨z, rfl⟩
    have := image_closure_subset_closure_image E.map.continuous ⟨_, hz, rfl⟩
    rw [Set.image_singleton, E.map_point, hηT] at this
    exact this
  have H : (curveι T).ker ≤ g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot,
      ← Scheme.nilradical_eq_bot, ← Scheme.IdealSheafData.vanishingIdeal_top,
      Scheme.IdealSheafData.map_vanishingIdeal]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    change closure (g.base '' Set.univ) ⊆ (T : Set Y)
    rw [Set.image_univ]
    exact hrange
  let ψ := IsClosedImmersion.lift (curveι T) g H
  have hψ : ψ ≫ curveι T = g := IsClosedImmersion.lift_fac _ _ _
  refine ⟨ψ ⁻¹ᵁ T₁, ψ ∣_ T₁, ?_, ?_⟩
  · obtain ⟨ξ', hξ'⟩ : E.point ∈ Set.range (curveι E.curve).base := hrT' ▸ subset_closure rfl
    have hgen' : closure ({ξ'} : Set (curveScheme E.curve)) = Set.univ :=
      closure_singleton_eq_univ_of_isClosedEmbedding (curveι E.curve).isClosedEmbedding
        (by rw [hξ', hrT'])
    have hψξ : (curveι T).base (ψ.base ξ') = localSettingGenericPoint T := by
      rw [← Scheme.Hom.comp_apply, hψ, hg, Scheme.Hom.comp_apply, hξ', E.map_point]
    have hgen : closure ({ψ.base ξ'} : Set (curveScheme T)) = Set.univ :=
      closure_singleton_eq_univ_of_isClosedEmbedding (curveι T).isClosedEmbedding
        (by rw [hψξ, hηT, hrT])
    have hmem : ψ.base ξ' ∈ T₁ := by
      by_contra h
      have hc : closure ({ψ.base ξ'} : Set (curveScheme T)) ⊆ (T₁ : Set _)ᶜ :=
        T₁.2.isClosed_compl.closure_subset_iff.2 (Set.singleton_subset_iff.2 h)
      rw [hgen] at hc
      have : Nonempty (curveScheme T) := ⟨ψ.base ξ'⟩
      obtain ⟨y, hy⟩ := hT₁.nonempty
      exact hc (Set.mem_univ y) hy
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    have : closure ({ξ'} : Set (curveScheme E.curve)) ⊆ closure (ψ ⁻¹ᵁ T₁ : Set _) :=
      closure_mono (Set.singleton_subset_iff.2 hmem)
    rw [hgen'] at this
    exact this (Set.mem_univ x)
  · rw [morphismRestrict_ι_assoc, hψ]

/-- For an open `W ⊆ T'` and a factorization `φ : W ⟶ T¹` of `W ⟶ Y`, the morphism
`Ỹ_e ×_{Y_e} W ⟶ Ỹ ×_Y T¹` which is `Ỹ_e ⟶ Ỹ` on the first factor and `φ` on the second. -/
private noncomputable def familyMap {Ye Y Yt : Scheme.{0}} {q : Ye ⟶ Y} {π : Yt ⟶ Y}
    {T : IrreducibleCloseds Y} {T' : IrreducibleCloseds Ye} {T₁ : (curveScheme T).Opens}
    {W : (curveScheme T').Opens} (φ : (W : Scheme.{0}) ⟶ T₁)
    (hφ : φ ≫ T₁.ι ≫ curveι T = W.ι ≫ curveι T' ≫ q) :
    pullback (pullback.snd π q) (W.ι ≫ curveι T') ⟶ adaptedFamily π T₁ :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst π q) (pullback.snd _ _ ≫ φ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
    simp only [Category.assoc, hφ])

/-! ### Spreading out along the generic point of `T'` -/

/-- The pull-back along `h` is the pull-back along `g` after the pull-back along `f`, for
`f ≫ g = h`. -/
private noncomputable def pullbackObjIsoOfEq {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) (M : Z.Modules) :
    (Scheme.Modules.pullback h).obj M ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackCongr w.symm).app M ≪≫ ((Scheme.Modules.pullbackComp f g).app M).symm

/-- An isomorphism of pull-backs along `g₁, g₂` pulls back along `ℓ` to one of the pull-backs
along `ℓ ≫ g₁, ℓ ≫ g₂`. -/
private theorem nonempty_pullback_iso_of_comp {X Y Z₁ Z₂ : Scheme.{0}} (ℓ : X ⟶ Y)
    {g₁ : Y ⟶ Z₁} {g₂ : Y ⟶ Z₂} {h₁ : X ⟶ Z₁} {h₂ : X ⟶ Z₂} (w₁ : ℓ ≫ g₁ = h₁)
    (w₂ : ℓ ≫ g₂ = h₂) {M₁ : Z₁.Modules} {M₂ : Z₂.Modules}
    (e : Nonempty ((Scheme.Modules.pullback g₁).obj M₁ ≅ (Scheme.Modules.pullback g₂).obj M₂)) :
    Nonempty ((Scheme.Modules.pullback h₁).obj M₁ ≅ (Scheme.Modules.pullback h₂).obj M₂) :=
  ⟨pullbackObjIsoOfEq ℓ g₁ h₁ w₁ M₁ ≪≫ (Scheme.Modules.pullback ℓ).mapIso e.some ≪≫
    (pullbackObjIsoOfEq ℓ g₂ h₂ w₂ M₂).symm⟩

/-- At a point `x` whose stalk is a field, `Spec 𝒪_{C,x} ⟶ C ⟶ X` factors through
`Spec κ(y) ⟶ X`, `y` the image of `x`. -/
private theorem exists_specStalk_lift {C X : Scheme.{0}} (x : C)
    (hx : IsField (C.presheaf.stalk x)) (g : C ⟶ X) {y : X} (h : g.base x = y) :
    ∃ τ : Spec (C.presheaf.stalk x) ⟶ Spec (X.residueField y),
      τ ≫ X.fromSpecResidueField y = C.fromSpecStalk x ≫ g := by
  subst h
  have hinj : Function.Injective (C.residue x).hom := by
    refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
    by_contra hne
    obtain ⟨b, hb⟩ := hx.mul_inv_cancel hne
    have hmem : a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x) :=
      (IsLocalRing.residue_eq_zero_iff a).1 ha
    exact (IsLocalRing.mem_maximalIdeal a).1 hmem (IsUnit.of_mul_eq_one b hb)
  have : IsIso (C.residue x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, C.residue_surjective x⟩
  refine ⟨inv (Spec.map (C.residue x)) ≫ Spec.map (g.residueFieldMap x), ?_⟩
  rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Scheme.fromSpecResidueField, Category.assoc, IsIso.inv_hom_id_assoc]

/-- A dense open `W` of the curve `T'` contains a point `x` over `η'`, at which the stalk of `W`
is a field, and the image in `T'` of every open of `W` containing `x` is dense. -/
private theorem exists_curveOpen_genericPoint {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ} {L : Fin b → (genericFibre π T).Modules}
    (E : LocalEtaleDatum sY T π L) (W : (curveScheme E.curve).Opens)
    (hW : Dense (W : Set (curveScheme E.curve))) :
    ∃ x : (W : Scheme.{0}), (W.ι ≫ curveι E.curve).base x = E.point ∧
      IsField ((W : Scheme.{0}).presheaf.stalk x) ∧
      ∀ U : (W : Scheme.{0}).Opens, x ∈ U →
        Dense ((W.ι ''ᵁ U : (curveScheme E.curve).Opens) : Set (curveScheme E.curve)) := by
  have hrT' : Set.range (curveι E.curve).base = closure {E.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨ξ', hξ'⟩ : E.point ∈ Set.range (curveι E.curve).base := hrT' ▸ subset_closure rfl
  have hgen' : closure ({ξ'} : Set (curveScheme E.curve)) = Set.univ :=
    closure_singleton_eq_univ_of_isClosedEmbedding (curveι E.curve).isClosedEmbedding
      (by rw [hξ', hrT'])
  have hξW : ξ' ∈ W := by
    by_contra h
    have hc : closure ({ξ'} : Set (curveScheme E.curve)) ⊆ (W : Set _)ᶜ :=
      W.2.isClosed_compl.closure_subset_iff.2 (Set.singleton_subset_iff.2 h)
    rw [hgen'] at hc
    have : Nonempty (curveScheme E.curve) := ⟨ξ'⟩
    obtain ⟨y, hy⟩ := hW.nonempty
    exact hc (Set.mem_univ y) hy
  let x : (W : Scheme.{0}) := ⟨ξ', hξW⟩
  have hιx : W.ι.base x = ξ' := rfl
  refine ⟨x, ?_, ?_, fun U hU ↦ ?_⟩
  · rw [Scheme.Hom.comp_apply, hιx, hξ']
  · have hcl : closure ({x} : Set (W : Scheme.{0})) = Set.univ := by
      rw [W.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
        hιx, hgen', Set.preimage_univ]
    have : IsReduced (W : Scheme.{0}) := isReduced_of_isOpenImmersion W.ι
    exact isField_stalk_of_closure_mem_irreducibleComponents _ x
      ⟨isIrreducible_singleton.closure, fun t _ _ ↦ hcl ▸ Set.subset_univ t⟩
  · have hmem : ξ' ∈ ((W.ι ''ᵁ U : (curveScheme E.curve).Opens) : Set (curveScheme E.curve)) :=
      ⟨x, hU, hιx⟩
    rw [dense_iff_closure_eq, ← Set.univ_subset_iff, ← hgen']
    exact closure_mono (Set.singleton_subset_iff.2 hmem)

set_option hygiene false in
/-- The family `Ỹ_e ×_{Y_e} W ⟶ W` over an open `W` of `T'`. -/
local notation "𝔣" => pullback.snd E.resolutionMap (W.ι ≫ curveι E.curve)

private theorem exists_specStalk_fibreMap {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ} {L : Fin b → (genericFibre π T).Modules}
    (E : LocalEtaleDatum sY T π L) (T₁ : (curveScheme T).Opens) (ξ : (T₁ : Scheme.{0}))
    (eξ : (T₁.ι ≫ curveι T).base ξ = localSettingGenericPoint T)
    (W : (curveScheme E.curve).Opens) (φ : (W : Scheme.{0}) ⟶ T₁)
    (hφ : φ ≫ T₁.ι ≫ curveι T = W.ι ≫ curveι E.curve ≫ E.map) (x : (W : Scheme.{0}))
    (hx : (W.ι ≫ curveι E.curve).base x = E.point)
    (hfield : IsField ((W : Scheme.{0}).presheaf.stalk x)) :
    ∃ bZ : pullback 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ⟶ curveOpenFibre π T₁ ξ,
      bZ ≫ curveOpenFibreToGenericFibre π T₁ ξ eξ ≫ localEtaleFibreMap π E.neighborhood =
        pullback.fst 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ≫
          pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve) ∧
      bZ ≫ curveOpenFibreToFamily π T₁ ξ =
        pullback.fst 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ≫ familyMap φ hφ := by
  obtain ⟨τa, hτa⟩ := exists_specStalk_lift x hfield (W.ι ≫ curveι E.curve) hx
  have hEiso := E.isIso_residueFieldMap
  set sa := τa ≫ Spec.map E.neighborhood.obj.residueFieldMap with hsa
  have hsaE : sa ≫ elementaryNeighborhoodSection E.neighborhood =
      (W : Scheme.{0}).fromSpecStalk x ≫ W.ι ≫ curveι E.curve := by
    simp only [hsa, elementaryNeighborhoodSection, Category.assoc]
    rw [← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp, hτa]
  have hsaY : sa ≫ Y.fromSpecResidueField (localSettingGenericPoint T) =
      (W : Scheme.{0}).fromSpecStalk x ≫ W.ι ≫ curveι E.curve ≫ E.map := by
    rw [← elementaryNeighborhoodSection_comp_toBase E.neighborhood, reassoc_of% hsaE]
  have hφx : φ.base x = ξ := by
    have h1 : (T₁.ι ≫ curveι T).base (φ.base x) = (T₁.ι ≫ curveι T).base ξ := by
      rw [eξ]
      calc (T₁.ι ≫ curveι T).base (φ.base x) = (φ ≫ T₁.ι ≫ curveι T).base x := rfl
        _ = ((W.ι ≫ curveι E.curve) ≫ E.map).base x := by rw [hφ, Category.assoc]
        _ = E.map.base E.point := by rw [Scheme.Hom.comp_apply, hx]
        _ = localSettingGenericPoint T := E.map_point
    exact T₁.ι.isOpenEmbedding.injective ((curveι T).isClosedEmbedding.injective h1)
  obtain ⟨τb, hτb⟩ := exists_specStalk_lift x hfield φ hφx
  have hkey : τb ≫ Spec.map ((T₁.ι ≫ curveι T).residueFieldMap ξ) ≫
      Spec.map (Y.residueFieldCongr eξ.symm).hom = sa := by
    rw [← cancel_mono (Y.fromSpecResidueField (localSettingGenericPoint T)), hsaY]
    simp only [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [reassoc_of% hτb, hφ]
  have h1 : pullback.fst 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ≫ 𝔣 =
      pullback.snd 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ≫ (W : Scheme.{0}).fromSpecStalk x :=
    pullback.condition
  have h2 : pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve) ≫ E.resolutionMap =
      𝔣 ≫ W.ι ≫ curveι E.curve := pullback.condition
  have h3 : pullback.fst π E.map ≫ π = E.resolutionMap ≫ E.map := pullback.condition
  let yZ : pullback 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ⟶ Yt :=
    pullback.fst 𝔣 _ ≫ pullback.fst E.resolutionMap _ ≫ pullback.fst π E.map
  let bZ : pullback 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ⟶ curveOpenFibre π T₁ ξ :=
    pullback.lift yZ (pullback.snd 𝔣 _ ≫ τb) (by
      simp only [yZ, Category.assoc, h3, reassoc_of% h2, reassoc_of% h1, reassoc_of% hτb, hφ])
  have b1 : bZ ≫ pullback.fst _ _ = yZ := pullback.lift_fst _ _ _
  have b2 : bZ ≫ pullback.snd _ _ = pullback.snd 𝔣 _ ≫ τb := pullback.lift_snd _ _ _
  have cF1 : curveOpenFibreToFamily π T₁ ξ ≫ pullback.fst π (T₁.ι ≫ curveι T) =
      pullback.fst _ _ := (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have cF2 : curveOpenFibreToFamily π T₁ ξ ≫ pullback.snd π (T₁.ι ≫ curveι T) =
      pullback.snd _ _ ≫ (T₁ : Scheme.{0}).fromSpecResidueField ξ := pullback.lift_snd _ _ _
  have cG1 : curveOpenFibreToGenericFibre π T₁ ξ eξ ≫ pullback.fst _ _ = pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have cG2 : curveOpenFibreToGenericFibre π T₁ ξ eξ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map ((T₁.ι ≫ curveι T).residueFieldMap ξ) ≫
        Spec.map (Y.residueFieldCongr eξ.symm).hom := pullback.lift_snd _ _ _
  have fm1 : familyMap φ hφ ≫ pullback.fst π (T₁.ι ≫ curveι T) =
      pullback.fst _ _ ≫ pullback.fst π E.map := pullback.lift_fst _ _ _
  have fm2 : familyMap φ hφ ≫ pullback.snd π (T₁.ι ≫ curveι T) = pullback.snd _ _ ≫ φ :=
    pullback.lift_snd _ _ _
  refine ⟨bZ, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [localEtaleFibreMap_fst, cG1, b1]
    · simp only [Category.assoc]
      rw [localEtaleFibreMap_snd, reassoc_of% cG2, reassoc_of% b2, reassoc_of% hkey, hsaE, h2,
        reassoc_of% h1]
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [cF1, b1, fm1]
    · simp only [Category.assoc]
      rw [cF2, reassoc_of% b2, fm2, hτb, reassoc_of% h1]

/-- An invertible module pulls back to a module of finite presentation. -/
private theorem isFinitePresentation_pullback_obj {X Y : Scheme.{0}} (g : X ⟶ Y) (M : Y.Modules)
    (hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M) :
    ((Scheme.Modules.pullback g).obj M).IsFinitePresentation := by
  have := MMP.Mori.isInvertible_pullback_obj g M (hL := hM)
  exact SheafOfModules.isFinitePresentation_of_isInvertible _ _

/-- **Spreading out (affine stage).** Over the preimage of some affine open neighbourhood `U` of
`x` in `W`, the pull-backs of `L̃_i` and of `𝓛_i` are isomorphic, as soon as they are over
`Spec 𝒪_{W,x}`. -/
private theorem exists_affineOpenNhds_iso {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
    {L : Fin b → (genericFibre π T).Modules}
    (hLS : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L)
    (T₁ : (curveScheme T).Opens) (𝓛 : (adaptedFamily π T₁).Modules)
    (h𝓛 : SheafOfModules.IsInvertible (adaptedFamily π T₁).presheaf
      (adaptedFamily π T₁).ringCatSheaf.2 𝓛) (i : Fin b)
    (W : (curveScheme E.curve).Opens) (φ : (W : Scheme.{0}) ⟶ T₁)
    (hφ : φ ≫ T₁.ι ≫ curveι T = W.ι ≫ curveι E.curve ≫ E.map) (x : (W : Scheme.{0}))
    (hZ : Nonempty ((Scheme.Modules.pullback
      (pullback.fst 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ≫
        pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve))).obj (E.bundle i) ≅
      (Scheme.Modules.pullback (pullback.fst 𝔣 ((W : Scheme.{0}).fromSpecStalk x) ≫
        familyMap φ hφ)).obj 𝓛)) :
    ∃ U : AffineOpenNhds (W : Scheme.{0}) x, Nonempty ((Scheme.Modules.pullback
      ((𝔣 ⁻¹ᵁ U.opens).ι ≫ pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve))).obj
        (E.bundle i) ≅
      (Scheme.Modules.pullback ((𝔣 ⁻¹ᵁ U.opens).ι ≫ familyMap φ hφ)).obj 𝓛) := by
  have hπp : IsProjectiveMorphism π := hLS.isResolution.2.2.2.1
  have : IsProper 𝔣 :=
    isProper_of_isProjectiveMorphism _ ((hπp.baseChange E.map).baseChange _)
  have : QuasiCompact 𝔣 := inferInstance
  have : IsSeparated 𝔣 := inferInstance
  have : QuasiSeparated 𝔣 := IsSeparated.instQuasiSeparated _
  let U₀ : AffineOpenNhds (W : Scheme.{0}) x := Classical.arbitrary _
  let A₀ : ((preimageAffineOpenNhdsDiagram 𝔣 x).obj U₀).Modules :=
    (Scheme.Modules.pullback ((𝔣 ⁻¹ᵁ U₀.opens).ι ≫
      pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve))).obj (E.bundle i)
  let B₀ : ((preimageAffineOpenNhdsDiagram 𝔣 x).obj U₀).Modules :=
    (Scheme.Modules.pullback ((𝔣 ⁻¹ᵁ U₀.opens).ι ≫ familyMap φ hφ)).obj 𝓛
  have hA : A₀.IsFinitePresentation :=
    isFinitePresentation_pullback_obj _ _ (E.isInvertibleModule i)
  have hB : B₀.IsFinitePresentation := isFinitePresentation_pullback_obj _ _ h𝓛
  have hc : (preimageSpecStalkCone 𝔣 x).π.app U₀ ≫ (𝔣 ⁻¹ᵁ U₀.opens).ι =
      pullback.fst 𝔣 ((W : Scheme.{0}).fromSpecStalk x) := preimageSpecStalkLeg_ι _ _ _
  have hZ' : Nonempty ((Scheme.Modules.pullback ((preimageSpecStalkCone 𝔣 x).π.app U₀)).obj A₀ ≅
      (Scheme.Modules.pullback ((preimageSpecStalkCone 𝔣 x).π.app U₀)).obj B₀) := by
    obtain ⟨eZ⟩ := hZ
    exact ⟨(pullbackObjIsoOfEq ((preimageSpecStalkCone 𝔣 x).π.app U₀)
        ((𝔣 ⁻¹ᵁ U₀.opens).ι ≫ pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve)) _
        ((Category.assoc _ _ _).symm.trans (eq_whisker hc _)) _).symm ≪≫ eZ ≪≫
      pullbackObjIsoOfEq ((preimageSpecStalkCone 𝔣 x).π.app U₀)
        ((𝔣 ⁻¹ᵁ U₀.opens).ι ≫ familyMap φ hφ) _
        ((Category.assoc _ _ _).symm.trans (eq_whisker hc _)) _⟩
  obtain ⟨U, e, ⟨iso⟩⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_iso_pullback_of_isLimit
    (preimageAffineOpenNhdsDiagram 𝔣 x) (preimageSpecStalkCone 𝔣 x)
    (isLimitPreimageSpecStalkCone 𝔣 x) U₀ A₀ B₀ hA hB hZ'
  have he : (preimageAffineOpenNhdsDiagram 𝔣 x).map e ≫ (𝔣 ⁻¹ᵁ U₀.opens).ι =
      (𝔣 ⁻¹ᵁ U.opens).ι := preimageAffineOpenNhdsDiagram_map_ι _ _ _
  exact ⟨U, ⟨pullbackObjIsoOfEq ((preimageAffineOpenNhdsDiagram 𝔣 x).map e)
    ((𝔣 ⁻¹ᵁ U₀.opens).ι ≫ pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve)) _
    ((Category.assoc _ _ _).symm.trans (eq_whisker he _)) _ ≪≫ iso ≪≫
    (pullbackObjIsoOfEq ((preimageAffineOpenNhdsDiagram 𝔣 x).map e)
      ((𝔣 ⁻¹ᵁ U₀.opens).ι ≫ familyMap φ hφ) _
      ((Category.assoc _ _ _).symm.trans (eq_whisker he _)) _).symm⟩⟩

/-- **Spreading out (scheme-level form).** Over a dense open `W' ⊆ W` the bundles `L̃_i` and the
pull-backs of the `𝓛_i` along `Ỹ_e ×_{Y_e} W' ⟶ Ỹ ×_Y T¹` are isomorphic. -/
private theorem exists_dense_family_iso {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
    {L : Fin b → (genericFibre π T).Modules}
    (hLS : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L)
    (T₁ : (curveScheme T).Opens)
    (𝓛 : Fin b → (adaptedFamily π T₁).Modules)
    (h𝓛 : ∀ i, SheafOfModules.IsInvertible (adaptedFamily π T₁).presheaf
      (adaptedFamily π T₁).ringCatSheaf.2 (𝓛 i))
    (hgen : ∃ (ξ : (T₁ : Scheme.{0})) (e : (T₁.ι ≫ curveι T).base ξ = localSettingGenericPoint T),
      ∀ i, Nonempty ((Scheme.Modules.pullback (curveOpenFibreToFamily π T₁ ξ)).obj (𝓛 i) ≅
        (Scheme.Modules.pullback (curveOpenFibreToGenericFibre π T₁ ξ e)).obj (L i)))
    (W : (curveScheme E.curve).Opens) (hW : Dense (W : Set (curveScheme E.curve)))
    (φ : (W : Scheme.{0}) ⟶ T₁) (hφ : φ ≫ T₁.ι ≫ curveι T = W.ι ≫ curveι E.curve ≫ E.map) :
    ∃ (W' : (curveScheme E.curve).Opens) (hW' : W' ≤ W),
      Dense (W' : Set (curveScheme E.curve)) ∧ ∀ i, Nonempty
        ((Scheme.Modules.pullback (pullback.fst E.resolutionMap (W'.ι ≫ curveι E.curve))).obj
            (E.bundle i) ≅
          (Scheme.Modules.pullback (familyMap ((curveScheme E.curve).homOfLE hW' ≫ φ)
            (by rw [Category.assoc, hφ, Scheme.homOfLE_ι_assoc]))).obj (𝓛 i)) := by
  classical
  obtain ⟨ξ, eξ, hξ⟩ := hgen
  obtain ⟨x, hx, hfield, hdense⟩ := exists_curveOpen_genericPoint E W hW
  obtain ⟨bZ, wA, wB⟩ := exists_specStalk_fibreMap E T₁ ξ eξ W φ hφ x hx hfield
  have hstage : ∀ i, ∃ U : AffineOpenNhds (W : Scheme.{0}) x, Nonempty ((Scheme.Modules.pullback
      ((𝔣 ⁻¹ᵁ U.opens).ι ≫ pullback.fst E.resolutionMap (W.ι ≫ curveι E.curve))).obj
        (E.bundle i) ≅
      (Scheme.Modules.pullback ((𝔣 ⁻¹ᵁ U.opens).ι ≫ familyMap φ hφ)).obj (𝓛 i)) := fun i ↦
    exists_affineOpenNhds_iso hLS E T₁ (𝓛 i) (h𝓛 i) i W φ hφ x
      (nonempty_pullback_iso_of_comp bZ wA wB
        ⟨pullbackObjIsoOfEq _ _ _ rfl _ ≪≫ (Scheme.Modules.pullback _).mapIso (E.restrict i).some ≪≫
          (hξ i).some.symm⟩)
  -- a common stage for the finitely many `i`
  choose U hU using hstage
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image U)
  have hmU : ∀ i, m.opens ≤ (U i).opens := fun i ↦
    AffineOpenNhds.opens_le (hm (Finset.mem_image_of_mem U (Finset.mem_univ i))).some
  refine ⟨W.ι ''ᵁ m.opens, W.ι_image_le m.opens, hdense _ m.mem_opens, fun i ↦ ?_⟩
  let k : pullback E.resolutionMap ((W.ι ''ᵁ m.opens).ι ≫ curveι E.curve) ⟶
      pullback E.resolutionMap (W.ι ≫ curveι E.curve) :=
    pullback.map _ _ _ _ (𝟙 _) ((curveScheme E.curve).homOfLE (W.ι_image_le m.opens)) (𝟙 _)
      (by simp) (by simp)
  have hkf : k ≫ 𝔣 = pullback.snd _ _ ≫ (curveScheme E.curve).homOfLE (W.ι_image_le m.opens) :=
    pullback.lift_snd _ _ _
  have hk1 : k ≫ pullback.fst _ _ = pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hk : Set.range k.base ⊆ Set.range (𝔣 ⁻¹ᵁ (U i).opens).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (𝔣).base (k.base z) ∈ (U i).opens
    rw [← Scheme.Hom.comp_apply, hkf, Scheme.Hom.comp_apply]
    set w := (pullback.snd E.resolutionMap ((W.ι ''ᵁ m.opens).ι ≫ curveι E.curve)).base z
    obtain ⟨u, hu, hu'⟩ : w.1 ∈ W.ι.base '' (m.opens : Set (W : Scheme.{0})) := w.2
    have : ((curveScheme E.curve).homOfLE (W.ι_image_le m.opens)).base w = u := by
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι, hu']
      rfl
    exact this ▸ hmU i hu
  let ℓ := IsOpenImmersion.lift (𝔣 ⁻¹ᵁ (U i).opens).ι k hk
  have hℓ : ℓ ≫ (𝔣 ⁻¹ᵁ (U i).opens).ι = k := IsOpenImmersion.lift_fac _ _ _
  refine nonempty_pullback_iso_of_comp ℓ ?_ ?_ (hU i)
  · rw [reassoc_of% hℓ, hk1]
  · rw [reassoc_of% hℓ]
    have fm1 : ∀ {W₀ : (curveScheme E.curve).Opens} (φ₀ : (W₀ : Scheme.{0}) ⟶ T₁)
        (hφ₀ : φ₀ ≫ T₁.ι ≫ curveι T = W₀.ι ≫ curveι E.curve ≫ E.map),
        familyMap φ₀ hφ₀ ≫ pullback.fst π (T₁.ι ≫ curveι T) =
          pullback.fst _ _ ≫ pullback.fst π E.map := fun _ _ ↦ pullback.lift_fst _ _ _
    have fm2 : ∀ {W₀ : (curveScheme E.curve).Opens} (φ₀ : (W₀ : Scheme.{0}) ⟶ T₁)
        (hφ₀ : φ₀ ≫ T₁.ι ≫ curveι T = W₀.ι ≫ curveι E.curve ≫ E.map),
        familyMap φ₀ hφ₀ ≫ pullback.snd π (T₁.ι ≫ curveι T) = pullback.snd _ _ ≫ φ₀ :=
      fun _ _ ↦ pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, fm1, fm1, reassoc_of% hk1]
    · rw [Category.assoc, fm2, fm2, reassoc_of% hkf]

/-- **Spreading out the generic identification of the bundles.** There is a dense open `T'°` of
`T'` over which `q` maps into `T¹`, such that at every `ℂ`-point `t'` of `T'°` the restriction of
`L̃_i` to `F_{t'}` is the pull-back along `F_{t'} ≅ F_{q(t')}` of the restriction of `𝓛_i`. -/
private theorem exists_dense_fibre_iso {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
    {L : Fin b → (genericFibre π T).Modules}
    (hLS : IsLocalSetting sY Θ T π) (E : LocalEtaleDatum sY T π L)
    (T₁ : (curveScheme T).Opens) (hT₁ : IsAdaptedOpen sY π T₁)
    (𝓛 : Fin b → (adaptedFamily π T₁).Modules)
    (h𝓛 : ∀ i, SheafOfModules.IsInvertible (adaptedFamily π T₁).presheaf
      (adaptedFamily π T₁).ringCatSheaf.2 (𝓛 i))
    (hgen : ∃ (ξ : (T₁ : Scheme.{0})) (e : (T₁.ι ≫ curveι T).base ξ = localSettingGenericPoint T),
      ∀ i, Nonempty ((Scheme.Modules.pullback (curveOpenFibreToFamily π T₁ ξ)).obj (𝓛 i) ≅
        (Scheme.Modules.pullback (curveOpenFibreToGenericFibre π T₁ ξ e)).obj (L i))) :
    ∃ (To : (curveScheme E.curve).Opens), Dense (To : Set (curveScheme E.curve)) ∧
      ∀ t' : ComplexPoints (To.ι ≫ curveι E.curve ≫ E.map ≫ sY),
        ∃ (t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY))
          (ht : t'.hom ≫ To.ι ≫ curveι E.curve ≫ E.map = t.hom ≫ T₁.ι ≫ curveι T),
          ∀ i, Nonempty ((Scheme.Modules.pullback
              (pointFibreFst (E.map ≫ sY) E.resolutionMap To t')).obj (E.bundle i) ≅
            (Scheme.Modules.pullback (fibreMap ht)).obj
              ((Scheme.Modules.pullback (pointFibreToFamily sY π T₁ t)).obj (𝓛 i))) := by
  obtain ⟨W, φ, hW, hφ⟩ := exists_curveOpen_factor E T₁ hT₁.dense
  obtain ⟨To, hTo, hTod, hiso⟩ :=
    exists_dense_family_iso hLS E T₁ 𝓛 h𝓛 hgen W hW φ hφ
  set φ' := (curveScheme E.curve).homOfLE hTo ≫ φ with hφ'def
  have hφ' : φ' ≫ T₁.ι ≫ curveι T = To.ι ≫ curveι E.curve ≫ E.map := by
    rw [hφ'def, Category.assoc, hφ, Scheme.homOfLE_ι_assoc]
  refine ⟨To, hTod, fun t' ↦ ?_⟩
  let t : ComplexPoints (T₁.ι ≫ curveι T ≫ sY) := ⟨t'.hom ≫ φ', by
    rw [Category.assoc, reassoc_of% hφ', t'.hom_comp_structure]⟩
  have ht : t'.hom ≫ To.ι ≫ curveι E.curve ≫ E.map = t.hom ≫ T₁.ι ≫ curveι T := by
    change _ = (t'.hom ≫ φ') ≫ _
    rw [Category.assoc, hφ']
  refine ⟨t, ht, fun i ↦ ?_⟩
  obtain ⟨e⟩ := hiso i
  let j := pointFibreToFamily (E.map ≫ sY) E.resolutionMap To t'
  have h1 : pointFibreFst (E.map ≫ sY) E.resolutionMap To t' =
      j ≫ pullback.fst E.resolutionMap (To.ι ≫ curveι E.curve) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _) |>.symm
  have hj2 : j ≫ pullback.snd E.resolutionMap (To.ι ≫ curveι E.curve) =
      pointFibreSnd (E.map ≫ sY) E.resolutionMap To t' ≫ t'.hom := pullback.lift_snd _ _ _
  have hf1 : ∀ {t₀ : ComplexPoints (T₁.ι ≫ curveι T ≫ sY)},
      pointFibreToFamily sY π T₁ t₀ ≫ pullback.fst π (T₁.ι ≫ curveι T) =
        pointFibreFst sY π T₁ t₀ := fun {_} ↦ (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hf2 : ∀ {t₀ : ComplexPoints (T₁.ι ≫ curveι T ≫ sY)},
      pointFibreToFamily sY π T₁ t₀ ≫ pullback.snd π (T₁.ι ≫ curveι T) =
        pointFibreSnd sY π T₁ t₀ ≫ t₀.hom := fun {_} ↦ pullback.lift_snd _ _ _
  have hm1 : familyMap φ' (by rw [hφ']) ≫ pullback.fst π (T₁.ι ≫ curveι T) =
      pullback.fst _ _ ≫ pullback.fst π E.map := pullback.lift_fst _ _ _
  have hm2 : familyMap φ' (by rw [hφ']) ≫ pullback.snd π (T₁.ι ≫ curveι T) =
      pullback.snd _ _ ≫ φ' := pullback.lift_snd _ _ _
  have h2 : fibreMap ht ≫ pointFibreToFamily sY π T₁ t =
      j ≫ familyMap φ' (by rw [hφ']) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hf1, hm1, fibreMap_fst, ← Category.assoc, ← h1]
    · rw [Category.assoc, Category.assoc, hf2, hm2, ← Category.assoc, fibreMap_snd,
        ← Category.assoc j, hj2]
      rfl
  exact ⟨(Scheme.Modules.pullbackCongr h1).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr h2.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm⟩

namespace LocalEtaleDatum

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {b : ℕ}
  {L : Fin b → (genericFibre π T).Modules}

/-- **Independence survives the étale extension.** For a local setting `(Y, Θ, T, π)`, a
punctured-independent family `L` on `F_{η_T}` and a local étale datum `E` for it, the resolution
`π_e = E.resolutionMap` is an isomorphism over the smooth locus of `Y_e`, and there is a dense
Zariski-open `T'°` of `T' = E.curve` such that for every `ℂ`-point `t'` of `T'°` the images in
`(R²j_{e*} ℚ)_{t'}` of the classes `c₁(L̃_i|_{π_e⁻¹(t')})` are linearly independent: there are a
neighbourhood `V` of `t'` and classes `α_i ∈ H²(π_e⁻¹(V); ℚ)` restricting to
`c₁(L̃_i|_{π_e⁻¹(t')})` whose germs have linearly independent images under the restriction map
`R²π_{e*} ℚ ⟶ R²j_{e*} ℚ`. -/
@[mmp "lem_oai4_c2_etale_independence"]
public theorem exists_dense_linearIndependent_chernClass (hLS : IsLocalSetting sY Θ T π)
    (hL : IsPuncturedIndependent sY hLS.isBiregular L) (E : LocalEtaleDatum sY T π L) :
    ∃ (hπe : IsBiregular E.resolutionMap (smoothLocus (E.map ≫ sY)))
      (To : (curveScheme E.curve).Opens), Dense (To : Set (curveScheme E.curve)) ∧
      ∀ t : ComplexPoints (To.ι ≫ curveι E.curve ≫ E.map ≫ sY),
        ∃ (V : Opens (analyticSpace (E.map ≫ sY)))
          (hV : curveOpenInclusion (E.map ≫ sY) To t ∈ V)
          (α : Fin b → rationalCohomology
            (preimageSpace (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap) V) 2),
          (∀ i, ∃ _ : SheafOfModules.IsInvertible
              (pointFibre (E.map ≫ sY) E.resolutionMap To t).presheaf
              (pointFibre (E.map ≫ sY) E.resolutionMap To t).ringCatSheaf.2
              ((Scheme.Modules.pullback
                (pointFibreFst (E.map ≫ sY) E.resolutionMap To t)).obj (E.bundle i)),
            (rationalCohomologyMap
                (pointFibreInclusion (E.map ≫ sY) E.resolutionMap To t hV) 2).hom (α i) =
              pointFibreChernClass (E.map ≫ sY) E.resolutionMap To t
                ((Scheme.Modules.pullback
                  (pointFibreFst (E.map ≫ sY) E.resolutionMap To t)).obj (E.bundle i))) ∧
          LinearIndependent ℚ fun i ↦
            (localSystemRestrictionFibre (E.map ≫ sY) hπe To t).hom
              ((stalkToPullbackStalk (curveOpenInclusion (E.map ≫ sY) To)
                (resolutionHigherDirectImage (E.map ≫ sY) E.resolutionMap 2) t).hom
                ((higherDirectImageGerm (resolutionAnalyticMap (E.map ≫ sY) E.resolutionMap)
                  2 _ hV).hom (α i))) := by
  have := hLS.isProjectiveVariety
  have := E.isQuasiProjectiveVariety
  obtain ⟨T₁, hT₁, 𝓛, h𝓛, hgen, hfib⟩ := hL
  exact ⟨isBiregular_resolutionMap hLS E, exists_dense_linearIndependent_of_fibre_iso hLS E _
    (isLocalHomeomorph_realize_of_etale E.map rfl) T₁ 𝓛 hfib
    (exists_dense_fibre_iso hLS E T₁ hT₁ 𝓛 h𝓛 hgen)⟩

end LocalEtaleDatum

end EtaleIndependence

end MMP.Fourfold

end
