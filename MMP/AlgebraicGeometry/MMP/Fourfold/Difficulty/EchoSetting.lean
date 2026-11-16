module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echo
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.LowDiscrepancyJunction
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationCharts
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Singularities.Bertini.HyperplaneDiscrepancyBound
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas

/-!
# Models of a prepared chain satisfy the echo hypotheses

Let `(Y, Θ)` be a model of a prepared chain, with labels `S_h`. Then `(Y, Θ)` is a terminal pair
on a projective `ℚ`-factorial complex threefold; the labels, all of them, including those of
coefficient zero, persist as distinct prime divisors `S_h^Y` of `Y`; the support of `Θ` lies in
their union, so `Θ = ∑_h b_h S_h^Y`, with every `b_h ∈ [0, 1)`. These are the hypotheses under
which the exceptional divisorial valuations `ξ` with `a(ξ; Y, Θ) < 2` are, up to finitely many,
echoes of the labels (`MMP.Fourfold.IsEcho`). Moreover `Y` is smooth (has regular local ring) at
the generic point of every irreducible closed curve.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.echoSetting_model`: the statement above.

## Implementation notes

* The labels on the model are recorded by a map `c` from the labels of the chain to the prime
  divisors of `Y`, with `c S` the centre of `S` on `Y`
  (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCentre`). Distinctness is injectivity of
  `c`; `Supp Θ ⊆ ⋃_h S_h` reads: every prime divisor with nonzero coefficient in `Θ` is some
  `c S`.
* A threefold is a scheme of Krull dimension `3`, and an irreducible closed curve is an
  irreducible closed subset of Krull dimension `1`, as in `MMP.Fourfold.IsEcho`. Smoothness at a
  point is regularity of the local ring there.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 5.18
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open MMP.Mori

section Pair

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The coefficients of the boundary of a klt pair lie in `[0, 1)`: the log discrepancy
`1 - coeff_P B` of a prime divisor `P` of `X` is positive. -/
private theorem coeff_mem_Ico_of_isKltPair {B : QDivisor X} (h : MMP.Fourfold.IsKltPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : 0 ≤ B.coeff P ∧ B.coeff P < 1 := by
  refine ⟨h.1.nonneg P, ?_⟩
  obtain ⟨hX, n, K, hK, -⟩ := h.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy h.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f :=
    inferInstanceAs (IsProper (𝟙 X))
  have hl := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp
  have hpos := h.2 n _ _ hl
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha] at hpos
  push_cast at hpos
  exact_mod_cast (by linarith : (B.coeff P : ℝ) < 1)

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- Being exceptional over a normal variety depends only on the valuation. -/
private theorem isExceptional_of_valuation_eq (hX : IsNormalVariety ℂ sX)
    {D D' : DivisorOver ℂ sX} (h : D.valuation = D'.valuation) (hD : D.IsExceptional) :
    D'.IsExceptional := by
  have key : ∀ D : DivisorOver ℂ sX, D.IsExceptional ↔
      ∀ P : MMP.Mori.PrimeDivisor X, D.valuation ≠ (DivisorOver.ofPrimeDivisor ℂ hX P).valuation :=
    fun D => (isExceptional_iff_two_le_coheight hX D).trans
      ((MMP.Positivity.DivisorOver.codimension_center D) ▸
        MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX D)
  exact (key D').mpr fun P hP => (key D).mp hD P (h.trans hP)

/-- If `(X, Θ)` is terminal and `K + Θ` is `ℚ`-Cartier, then the discrepancy
`discrep sX n K Θ` is positive. -/
private theorem discrep_pos_of_isKltTerminalPair [CompactSpace X] {Θ : QDivisor X}
    (h : MMP.Fourfold.IsKltTerminalPair sX Θ) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (hQ : (Divisor.toQDivisor K + Θ).IsQCartier) :
    0 < discrep sX n K Θ := by
  have hP : MMP.Mori.IsPair sX Θ := h.1.1.isPair
  have hX : IsNormalVariety ℂ sX := hP.1
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine lt_of_lt_of_le (b := (((1 : ℝ) / m : ℝ) : EReal)) (by exact_mod_cast (by positivity))
    (le_discrep_iff.mpr fun D a hD ha => ?_)
  obtain ⟨-, U, hxU, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hP hK hmC
    (D.f D.E.genericPoint)
  have ha' : IsDiscrepancy sX n K Θ D (D.ordPullback τ / m) := by
    refine ⟨hX, hK, m, hm, hmC, U, hxU, τ, hτ, ?_⟩
    have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  have heq : a = D.ordPullback τ / m := ha.eq ha'
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hX D
  have hEx : E.toDivisorOver.IsExceptional := isExceptional_of_valuation_eq hX hE.symm hD
  obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E.toDivisorOver
  have hab : a = b :=
    MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq ⟨hX, hK, hQ⟩ hE.symm ha hb
  have h1 := h.2 n _ _ hEx
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hb E.isProper)
  have hmq : (0 : ℚ) < m := by exact_mod_cast hm
  have hapos : (0 : ℚ) < D.ordPullback τ / m :=
    heq ▸ hab ▸ (by exact_mod_cast (by linarith : (0 : ℝ) < b))
  have hord : (1 : ℤ) ≤ D.ordPullback τ := by
    exact_mod_cast (div_pos_iff_of_pos_right hmq).mp hapos
  have hge : (1 : ℚ) / m ≤ a :=
    heq ▸ div_le_div_of_nonneg_right (by exact_mod_cast hord) hmq.le
  have : ((1 : ℝ) / m) ≤ (a : ℝ) := by simpa using (Rat.cast_le (K := ℝ)).mpr hge
  exact_mod_cast this

/-- **Terminal pairs are smooth in codimension two.** Let `(X, Θ)` be a terminal pair on a
`ℚ`-factorial variety of dimension `3`. Then the local ring of `X` at the generic point of every
irreducible closed curve is regular. -/
private theorem isRegularLocalRing_stalk_of_isKltTerminalPair {Θ : QDivisor X}
    (h : MMP.Fourfold.IsKltTerminalPair sX Θ) (hproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hQ : MMP.Fourfold.IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (V : IrreducibleCloseds X) (hV : topologicalKrullDim (V : Set X) = 1) :
    IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) := by
  have : CompactSpace X := by
    have := isProper_of_isProjectiveMorphism _ hproj.isProjective
    exact QuasiCompact.compactSpace_of_compactSpace sX
  have hP : MMP.Mori.IsPair sX Θ := h.1.1.isPair
  obtain ⟨hX, n, K, hK, hKΘ⟩ := hP
  have hKq : (Divisor.toQDivisor K + 0).IsQCartier := by
    rw [add_zero]; exact MMP.Fourfold.isQCartier_of_isQFactorial _ hQ _
  have hΘq : Θ.IsQCartier := MMP.Fourfold.isQCartier_of_isQFactorial _ hQ _
  have hterm : IsTerminalPair sX n K 0 := by
    refine ⟨⟨hX, hK, hKq⟩, ?_⟩
    have h1 := MMP.Threefold.Mori.Helpers.discrep_add_le (sX := sX) (n := n) (K := K)
      (Δ := 0) h.1.1.nonneg hΘq
    rw [zero_add] at h1
    exact (discrep_pos_of_isKltTerminalPair h hK hKΘ).trans_le h1
  set η := V.isIrreducible.genericPoint
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hcl : closure ({η} : Set X) = V := by
    have h := V.isIrreducible.isGenericPoint_genericPoint_closure
    rw [V.isClosed.closure_eq] at h
    exact h.def
  have hsum := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX η
  rw [hcl, hV, hdim] at hsum
  have hsm : η ∈ smoothLocus sX := by
    by_contra hη
    have h3 := IsTerminalPair.three_le_coheight_of_mem_singularLocus hterm hη
    have h4 : (1 : ℕ∞) + 3 ≤ 1 + Order.coheight η := add_le_add_right h3 1
    rw [show 1 + Order.coheight η = 3 from WithBot.coe_injective hsum] at h4
    exact absurd h4 (by decide)
  obtain ⟨U, hηU, hU⟩ := mem_smoothLocus_iff.mp hsm
  have : Smooth (U.ι ≫ sX) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sX) ⟨η, hηU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨η, hηU⟩).commRingCatIsoToRingEquiv

end Pair

section Valuations

/-- Restriction of valuations along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [Ring A] [Ring B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Surjective φ) :
    Function.Injective (fun v : Valuation B Γ => v.comap φ) := by
  intro v v' h
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  exact congrArg (fun w : Valuation A Γ => w a) h

/-- An element `x` with `v x < 1` lies in the maximal ideal of the valuation subring of `v`. -/
private theorem mem_nonunits_valuationSubring {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {x : K} (h : v x < 1) :
    x ∈ v.valuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have := Valuation.isEquiv_valuation_valuationSubring v 1 x
  simp only [map_one] at this
  exact lt_of_not_ge fun h' => (not_le.2 h) (this.2 h')

/-- On a normal integral scheme separated over a field, a prime divisor is determined by its
divisorial valuation: its generic point is the unique centre of that valuation. -/
private theorem divisorialValuation_injective {k : Type} [Field k] {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] :
    Function.Injective (fun P : MMP.Mori.PrimeDivisor Y => P.divisorialValuation) := by
  intro P P' h
  simp only at h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  refine MMP.Flips.eq_of_isLocal_le_valuationSubring sY P.divisorialValuation.valuationSubring
    ?_ ?_ ?_ ?_
  · intro a
    exact (P.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
  · intro a ha
    exact mem_nonunits_valuationSubring _ ((P.divisorialValuation_algebraMap_lt_one_iff a).2 ha)
  · intro a
    rw [Valuation.mem_valuationSubring_iff, h]
    exact (P'.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
  · intro a ha
    rw [h]
    exact mem_nonunits_valuationSubring _ ((P'.divisorialValuation_algebraMap_lt_one_iff a).2 ha)

/-- Through a birational morphism `f : Y ⟶ X`, a prime divisor of `Y` is determined by its
valuation `ord_P` regarded as a valuation of `k(X)`. -/
private theorem valuationOver_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] {f : Y ⟶ X} (hf : IsBirationalMorphism f) [IsDominant f] :
    Function.Injective (fun P : MMP.Mori.PrimeDivisor Y => P.valuationOver f) :=
  fun _ _ h => divisorialValuation_injective sY
    (comap_injective_of_surjective hf.functionFieldMap_bijective.2 h)

/-- Restriction of `ord_Q` along a composite `f ≫ g` is restriction along `f`, then along `g`. -/
private theorem valuationOver_comp {A B C : Scheme.{0}} [IsIntegral A] [IsLocallyNoetherian A]
    [IsNormal A] [IsIntegral B] [IsIntegral C] (Q : MMP.Mori.PrimeDivisor A) (f : A ⟶ B)
    (g : B ⟶ C) [IsDominant f] [IsDominant g] {c : A ⟶ C} [IsDominant c] (hc : f ≫ g = c) :
    Q.valuationOver c = (Q.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [MMP.Mori.PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply f g hc]

end Valuations

section Supports

/-- A prime divisor `P` with nonzero coefficient in `φ_* D` is `φ(Q)` for a prime divisor `Q`
with nonzero coefficient in `D`. -/
private theorem exists_of_mapPrimeDivisors_apply_ne_zero {X Y : Scheme.{0}} {R : Type*}
    [AddCommMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (D : DivisorWithCoeffs R X) (P : MMP.Mori.PrimeDivisor Y)
    (h : DivisorWithCoeffs.mapPrimeDivisors φ D P ≠ 0) : ∃ Q, D Q ≠ 0 ∧ φ Q = some P := by
  classical
  by_contra hne
  push Not at hne
  refine h ?_
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun Q hQ => ?_
  cases hφ : φ Q with
  | none => rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_none hφ]; rfl
  | some E =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single_of_eq_some hφ, Finsupp.single_apply, if_neg]
    rintro rfl
    exact hne Q (Finsupp.mem_support_iff.mp hQ) hφ

/-- A prime divisor `P` with nonzero coefficient in `g⁻¹_* D`, for a birational morphism `g`
onto a normal scheme, is the strict transform of a component `Q` of `D`, and `ord_P = ord_Q`. -/
private theorem exists_of_inverseTransformDivisor_apply_ne_zero {X Y : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {g : X ⟶ Y} (hg : IsBirationalMorphism g) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) (P : MMP.Mori.PrimeDivisor X)
    (h : inverseTransformDivisor g D P ≠ 0) :
    haveI := hg.isDominant
    ∃ Q, D Q ≠ 0 ∧ P.valuationOver g = Q.divisorialValuation := by
  have := hg.isDominant
  obtain ⟨Q, hQ, hP⟩ := exists_of_mapPrimeDivisors_apply_ne_zero _ D P h
  exact ⟨Q, hQ, MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint g
    hg.functionFieldMap_bijective.2 P Q
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hP).1⟩

/-- A prime divisor `P` with nonzero coefficient in the strict transform `(f⁺)⁻¹_* f_* D` across
birational morphisms `f : X⁻ ⟶ Z ⟵ X⁺ : f⁺` onto a separated normal scheme comes from a
component `P⁻` of `D` with `ord_{P⁻} = ord_P` as valuations of `k(Z)`. -/
private theorem exists_of_flipTransform_apply_ne_zero {Xm Xp Z : Scheme.{0}} [IsIntegral Xm]
    [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [IsSeparated (Z ↘ Limits.terminal Scheme)]
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hfm : IsBirationalMorphism fm) (hfp : IsBirationalMorphism fp)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) (P : MMP.Mori.PrimeDivisor Xp)
    (h : flipTransform fm fp D P ≠ 0) :
    haveI := hfm.isDominant
    haveI := hfp.isDominant
    ∃ Pm, D Pm ≠ 0 ∧ Pm.valuationOver fm = P.valuationOver fp := by
  have := hfm.isDominant
  have := hfp.isDominant
  obtain ⟨Q, hQ, hPQ⟩ := exists_of_inverseTransformDivisor_apply_ne_zero hfp _ P h
  obtain ⟨Pm, hPm, hPmQ⟩ := exists_of_mapPrimeDivisors_apply_ne_zero _ D Q hQ
  refine ⟨Pm, hPm, ?_⟩
  rw [hPQ]
  exact MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint fm
    hfm.functionFieldMap_bijective.2 Pm Q
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm Pm Q).mp hPmQ)

/-- The inverse transform of an effective divisor is effective. -/
private theorem inverseTransformDivisor_nonneg {X Y : Scheme.{0}} (g : Y ⟶ X) {D : QDivisor X}
    (hD : 0 ≤ D) : 0 ≤ inverseTransformDivisor g D := by
  classical
  rw [inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply,
    Finsupp.sum]
  refine Finset.sum_nonneg fun P _ => ?_
  cases inverseTransformPrimeDivisor g P with
  | none => exact le_rfl
  | some E => exact Finsupp.single_nonneg.mpr (hD P)

end Supports

section Chain

open MMP.Fourfold MMP.Fourfold.StabilizedTail

variable {T : StabilizedTail}

/-! ### Transport of valuations along a stabilized tail -/

/-- The transport of a valuation of `k(X_i)` to `k(X_{i+1})` is unique. -/
private theorem isTransportedValuation_right_unique {i : ℕ}
    {u : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (h : T.IsTransportedValuation i u w) (h' : T.IsTransportedValuation i u w') : w = w' := by
  have hd := T.isThreefoldStepDiagram i
  haveI : IsIntegral (T.Z i) := hd.isNormalVariety_target.1.toIsIntegral
  haveI := hd.isBirationalMorphism_minus.isDominant
  haveI := hd.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have h1 : w.comap (functionFieldMap (T.fp i)) = u.comap (functionFieldMap (T.f i)) := h
  have h2 : w'.comap (functionFieldMap (T.fp i)) = u.comap (functionFieldMap (T.f i)) := h'
  exact comap_injective_of_surjective
    hd.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2 (h1.trans h2.symm)

/-- A valuation of `k(X_{i+1})` is the transport of at most one valuation of `k(X_i)`. -/
private theorem isTransportedValuation_left_unique {i : ℕ}
    {u u' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    {w : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (h : T.IsTransportedValuation i u w) (h' : T.IsTransportedValuation i u' w) : u = u' := by
  have hd := T.isThreefoldStepDiagram i
  haveI : IsIntegral (T.Z i) := hd.isNormalVariety_target.1.toIsIntegral
  haveI := hd.isBirationalMorphism_minus.isDominant
  haveI := hd.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have h1 : w.comap (functionFieldMap (T.fp i)) = u.comap (functionFieldMap (T.f i)) := h
  have h2 : w.comap (functionFieldMap (T.fp i)) = u'.comap (functionFieldMap (T.f i)) := h'
  exact comap_injective_of_surjective
    hd.isBirationalMorphism_minus.functionFieldMap_bijective.2 (h1.symm.trans h2)

/-- A valuation of `k(X_i)` is the transport of at most one valuation of `k(X_0)`. -/
private theorem isTransportedValuationFrom_left_unique : ∀ (i : ℕ)
    {ν ν' : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν' w → ν = ν'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | i + 1, _, _, _, ⟨_, hu, huw⟩, ⟨_, hu', huw'⟩ => by
    obtain rfl := isTransportedValuation_left_unique huw huw'
    exact isTransportedValuationFrom_left_unique i hu hu'

/-- A valuation `u ∈ I(X_j, B_j)` has a transport to `k(X_{j+1})` lying in
`I(X_{j+1}, B_{j+1})`. -/
private theorem exists_isTransportedValuation_mem {j : ℕ}
    {u : Valuation (T.X j).functionField (WithZero (Multiplicative ℤ))}
    (hu : u ∈ lowDiscrepancySet (T.sX j) (T.B j)) :
    ∃ u' ∈ lowDiscrepancySet (T.sX (j + 1)) (T.B (j + 1)), T.IsTransportedValuation j u u' := by
  have he := T.lowDiscrepancySet_eq j
  haveI : IsIntegral (T.Z j) := (T.isThreefoldStepDiagram j).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram j).isBirationalMorphism_minus.isDominant
  haveI := (T.isThreefoldStepDiagram j).isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hmem : u.comap (functionFieldMap (T.f j)) ∈
      valuationsOver (T.f j) (lowDiscrepancySet (T.sX j) (T.B j)) := ⟨u, hu, rfl⟩
  rw [he] at hmem
  exact hmem

/-- Every valuation of `I(X_i, B_i)` is the transport of a valuation of `I_∞ = I(X_0, B_0)`. -/
private theorem exists_isTransportedValuationFrom_of_mem : ∀ (i : ℕ)
    {w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    w ∈ lowDiscrepancySet (T.sX i) (T.B i) →
    ∃ ν ∈ lowDiscrepancySet (T.sX 0) (T.B 0), T.IsTransportedValuationFrom i ν w
  | 0, w, hw => ⟨w, hw, rfl⟩
  | i + 1, w, hw => by
    have he := T.lowDiscrepancySet_eq i
    haveI : IsIntegral (T.Z i) :=
      (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    have hmem : w.comap (functionFieldMap (T.fp i)) ∈
        valuationsOver (T.fp i) (lowDiscrepancySet (T.sX (i + 1)) (T.B (i + 1))) := ⟨w, hw, rfl⟩
    rw [← he] at hmem
    obtain ⟨u, hu, hue⟩ := hmem
    obtain ⟨ν, hν, hνu⟩ := exists_isTransportedValuationFrom_of_mem i hu
    exact ⟨ν, hν, u, hνu, hue.symm⟩

/-- Every component of `B_i` is the transport of a component of `B_0`: `B_{i+1}` is the strict
transform `(f_i⁺)⁻¹_* (f_i)_* B_i`. -/
private theorem exists_isTransportedValuationFrom_of_coeff_ne_zero : ∀ (i : ℕ)
    (Γ : MMP.Mori.PrimeDivisor (T.X i)), T.B i Γ ≠ 0 →
    ∃ Γ₀ : MMP.Mori.PrimeDivisor (T.X 0), T.B 0 Γ₀ ≠ 0 ∧
      T.IsTransportedValuationFrom i Γ₀.divisorialValuation Γ.divisorialValuation
  | 0, Γ, h => ⟨Γ, h, rfl⟩
  | i + 1, Γ, h => by
    have hd := T.isThreefoldStepDiagram i
    have hZ := hd.isNormalVariety_target
    haveI : IsIntegral (T.Z i) := hZ.1.toIsIntegral
    haveI : IsNormal (T.Z i) := hZ.2
    haveI : LocallyOfFiniteType (T.sZ i) := hZ.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian (T.Z i) := LocallyOfFiniteType.isLocallyNoetherian (T.sZ i)
    haveI := MMP.Fourfold.isSeparated_toTerminal_of_isNormalVariety hZ
    rw [T.B_eq i] at h
    obtain ⟨Γm, hΓm, hv⟩ := exists_of_flipTransform_apply_ne_zero hd.isBirationalMorphism_minus
      hd.isSmallMorphism_plus.isBirationalMorphism _ Γ h
    obtain ⟨Γ₀, h₀, hc⟩ := exists_isTransportedValuationFrom_of_coeff_ne_zero i Γm hΓm
    exact ⟨Γ₀, h₀, _, hc, hv.symm⟩

variable (C : TerminalChain T)

/-- A prime divisor `R` of the junction `Y_i` in the support of a divisor
`p_i⁻¹_* B_i + ∑_s c(s) E_{i,s}`, whose valuation is the transport of that of a prime divisor `Q`
of `Y_0`: then `Q` is a label. -/
private theorem isLabel_of_isTransportedValuationFrom (i : ℕ) (c : C.I i → ℚ)
    (R : MMP.Mori.PrimeDivisor (C.junction i).Y)
    (hR : (inverseTransformDivisor (C.junction i).p (T.B i) +
      ∑ s : C.I i, Finsupp.single ((C.junction i).E s) (c s)) R ≠ 0)
    (Q : MMP.Mori.PrimeDivisor (C.junction 0).Y)
    (hQ : haveI := (C.junction 0).isBirationalMorphism.isDominant
      haveI := (C.junction i).isBirationalMorphism.isDominant
      T.IsTransportedValuationFrom i (Q.valuationOver (C.junction 0).p)
        (R.valuationOver (C.junction i).p)) :
    C.IsLabel Q := by
  classical
  haveI := (C.junction 0).isBirationalMorphism.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI : IsSeparated ((C.junction 0).p ≫ T.sX 0) :=
    (C.junction 0).isQFactorial.1.1.toIsSeparated
  have hinj := valuationOver_injective ((C.junction 0).p ≫ T.sX 0)
    (C.junction 0).isBirationalMorphism
  by_cases hs : ∃ s, R = (C.junction i).E s
  · obtain ⟨s, rfl⟩ := hs
    have hRv : ((C.junction i).E s).valuationOver (C.junction i).p = s.1 :=
      (C.junction i).valuation_eq s
    have hsI : s.1 ∈ lowDiscrepancySet (T.sX i) (T.B i) := C.coe_I i ▸ s.2
    obtain ⟨ξ, hξ, hξs⟩ := exists_isTransportedValuationFrom_of_mem i hsI
    have hξI : ξ ∈ (C.I 0 : Set _) := by rw [C.coe_I 0]; exact hξ
    rw [hRv] at hQ
    have hQξ := isTransportedValuationFrom_left_unique i hQ hξs
    have hE : ((C.junction 0).E ⟨ξ, hξI⟩).valuationOver (C.junction 0).p = ξ :=
      (C.junction 0).valuation_eq ⟨ξ, hξI⟩
    have : Q = (C.junction 0).E ⟨ξ, hξI⟩ := hinj (hQξ.trans hE.symm)
    exact this ▸ C.isLabel_E ⟨ξ, hξI⟩
  · have h0 : (∑ s : C.I i, Finsupp.single ((C.junction i).E s) (c s)) R = 0 := by
      rw [Finsupp.finset_sum_apply]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hs ⟨s, rfl⟩
    rw [Finsupp.add_apply, h0, add_zero] at hR
    obtain ⟨Γ, hΓ, hRv⟩ := exists_of_inverseTransformDivisor_apply_ne_zero
      (C.junction i).isBirationalMorphism _ R hR
    obtain ⟨Γ₀, h₀, htr⟩ := exists_isTransportedValuationFrom_of_coeff_ne_zero i Γ hΓ
    have : IsProper (C.junction 0).p :=
      isProper_of_isProjectiveMorphism _ (C.junction 0).isProjectiveMorphism
    obtain ⟨S, hS, hη⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some Γ₀
      (MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus (C.junction 0).p
        (C.junction 0).isBirationalMorphism Γ₀)
    have hSv : S.valuationOver (C.junction 0).p = Γ₀.divisorialValuation :=
      MMP.Fourfold.Oai4C1.CommonModel.valuationOver_eq_of_map_genericPoint _
        (C.junction 0).isBirationalMorphism.functionFieldMap_bijective.2 S Γ₀ hη
    rw [hRv] at hQ
    have hQS := isTransportedValuationFrom_left_unique i hQ (hSv ▸ htr)
    have : Q = S := hinj hQS
    exact this ▸ C.isLabel_of_inverseTransformPrimeDivisor_eq_some h₀ hS

/-- The junction `(Y_i, Θ_i)` is terminal. -/
private theorem isKltTerminalPair_junction (i : ℕ) :
    IsKltTerminalPair ((C.junction i).p ≫ T.sX i) (C.junction i).Θ :=
  ((C.junction i).isKltTerminalPair_of_coe_eq_lowDiscrepancySet (C.coe_I i)).1

/-- The decreased boundary `Θ_i'` is effective: its coefficient `1 - a_{i+1}(s)` at `E_{i,s}` is
nonnegative, since `s` lies in `I(X_{i+1}, B_{i+1})`. -/
private theorem decreasedBoundary_nonneg (i : ℕ) : 0 ≤ (C.bridge i).Θ' := by
  obtain ⟨a, ha, hΘ⟩ := (C.bridge i).isDecreasedBoundary
  rw [hΘ]
  refine add_nonneg (inverseTransformDivisor_nonneg _ (T.isKltPair i).1.nonneg)
    (Finset.sum_nonneg fun s _ => Finsupp.single_nonneg.mpr ?_)
  obtain ⟨s', hs', has'⟩ := ha s
  have hsI : s.1 ∈ lowDiscrepancySet (T.sX i) (T.B i) := C.coe_I i ▸ s.2
  obtain ⟨u', hu', hsu'⟩ := exists_isTransportedValuation_mem hsI
  obtain rfl := isTransportedValuation_right_unique hs' hsu'
  obtain ⟨-, b, ⟨n', D', -, hv', hl'⟩, hb1⟩ := hu'
  obtain ⟨n, D, -, hv, hl⟩ := has'
  have h1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hl hl' (hv.trans hv'.symm)
  have : a s ≤ 1 := by exact_mod_cast (h1 ▸ hb1 : ((a s : ℚ) : ℝ) ≤ 1)
  linarith

/-- **The decreased pair is terminal**: lowering the coefficients raises every log discrepancy. -/
private theorem isKltTerminalPair_decreased (i : ℕ) :
    IsKltTerminalPair ((C.junction i).p ≫ T.sX i) (C.bridge i).Θ' := by
  have hterm := isKltTerminalPair_junction C i
  obtain ⟨hX, n₀, K, hK, -⟩ := hterm.1.1.isPair
  have hpair : MMP.Fourfold.IsPair ((C.junction i).p ≫ T.sX i) (C.bridge i).Θ' :=
    ⟨inferInstance, inferInstance,
      ⟨hX, n₀, K, hK, MMP.Fourfold.isQCartier_of_isQFactorial _ (C.junction i).isQFactorial _⟩,
      fun P => decreasedBoundary_nonneg C i P⟩
  have hle : ∀ (n : ℕ) (D : DivisorOver ℂ ((C.junction i).p ≫ T.sX i)) (a' : ℝ),
      MMP.Intersection.IsLogDiscrepancy _ n (QDivisor.toRDivisor (C.bridge i).Θ') D a' →
        ∃ a : ℝ, MMP.Intersection.IsLogDiscrepancy _ n
          (QDivisor.toRDivisor (C.junction i).Θ) D a ∧ a ≤ a' := by
    intro n D a' ha'
    have hp : IsProper D.f := ha'.2.1
    obtain rfl : n₀ = n := by
      exact_mod_cast hK.topologicalKrullDim_eq.symm.trans
        (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha')
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hterm.1.1.isPair hK D
    have ha := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp
    exact ⟨_, ha, (IsDecreasedBoundary.sub_eq_sum_and_le (C.coe_I i)
      (C.bridge i).isDecreasedBoundary).2.2 _ _ _ ⟨n₀, D, hp, rfl, ha⟩ ⟨n₀, D, hp, rfl, ha'⟩⟩
  refine ⟨⟨hpair, fun n D a' ha' => ?_⟩, fun n D a' hE ha' => ?_⟩
  · obtain ⟨a, ha, hle⟩ := hle n D a' ha'
    exact (hterm.1.2 n D a ha).trans_le hle
  · obtain ⟨a, ha, hle⟩ := hle n D a' ha'
    exact (hterm.2 n D a hE ha).trans_le hle

/-- **The models of a bridge are terminal**: the first is the decreased pair, and terminal pairs
are preserved by the small flips of the bridge. -/
private theorem isKltTerminalPair_bridge (C : TerminalChain T) (i : ℕ) :
    ∀ k ≤ (C.bridge i).P.m,
      IsKltTerminalPair (modelStr ((C.junction i).p ≫ T.sX i) (C.bridge i).P.sY k)
        ((C.bridge i).P.boundary k)
  | 0, _ => isKltTerminalPair_decreased C i
  | k + 1, hk => by
    have hk' : k < (C.bridge i).P.m := hk
    have ih := isKltTerminalPair_bridge C i k hk'.le
    rw [(C.bridge i).P.boundary_succ_eq_flipTransform hk']
    exact (((C.bridge i).P.isThreefoldStepDiagram k
      hk').isKltPair_and_isKltTerminalPair_flipTransform
      ih.1).2 ((C.bridge i).isSmallMorphism k hk') ih

/-- Every model of a terminal chain is terminal. -/
private theorem isKltTerminalPair_model (C : TerminalChain T) :
    ∀ x : C.ModelIndex, IsKltTerminalPair (C.modelStructure x) (C.modelBoundary x)
  | ⟨i, none⟩ => isKltTerminalPair_junction C i
  | ⟨i, some k⟩ => isKltTerminalPair_bridge C i k k.2.le

/-- Along a bridge the coefficient of a prime divisor is that of its counterpart on the first
model. -/
private theorem coeff_bridge_eq (C : TerminalChain T) (i : ℕ)
    (e : ∀ k ≤ (C.bridge i).P.m, MMP.Mori.PrimeDivisor (C.junction 0).Y ≃
      MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k))
    (he : ∀ (k : ℕ) (hk : k < (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y),
      ((C.bridge i).P.boundary (k + 1)).coeff (e (k + 1) hk P) =
        ((C.bridge i).P.boundary k).coeff (e k hk.le P)) :
    ∀ (k : ℕ) (hk : k ≤ (C.bridge i).P.m) (P : MMP.Mori.PrimeDivisor (C.junction 0).Y),
      ((C.bridge i).P.boundary k).coeff (e k hk P) =
        ((C.bridge i).P.boundary 0).coeff (e 0 (Nat.zero_le _) P)
  | 0, _, _ => rfl
  | k + 1, hk, P => (he k hk P).trans (coeff_bridge_eq C i e he k _ P)

/-- On the junction `Y_i`, the valuation over `X_i` of a prime divisor is determined by its
valuation over `Z_i`. -/
private theorem valuationOver_eq_of_valuationOver_comp (i : ℕ)
    (R : MMP.Mori.PrimeDivisor (C.junction i).Y)
    (w : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))) :
    haveI : IsIntegral (T.Z i) :=
      (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (C.junction i).isBirationalMorphism.isDominant
    ∀ _ : IsDominant ((C.junction i).p ≫ T.f i),
      R.valuationOver ((C.junction i).p ≫ T.f i) = w.comap (functionFieldMap (T.f i)) →
      R.valuationOver (C.junction i).p = w := by
  haveI : IsIntegral (T.Z i) :=
    (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (C.junction i).isBirationalMorphism.isDominant
  intro _ h
  rw [valuationOver_comp R (C.junction i).p (T.f i) rfl] at h
  exact comap_injective_of_surjective
    (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.functionFieldMap_bijective.2 h

/-- **The labels on a model.** The centres of the labels on a model are distinct prime divisors,
and every component of the boundary is one of them. -/
private theorem exists_labelCentre (C : TerminalChain T) (x : C.ModelIndex) :
    ∃ c : C.Label → MMP.Mori.PrimeDivisor (C.model x), Function.Injective c ∧
      (∀ S, C.IsLabelCentre S x (c S)) ∧
      ∀ P, (C.modelBoundary x).coeff P ≠ 0 → P ∈ Set.range c := by
  classical
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨e, he⟩ := (TerminalChain.exists_equiv_primeDivisor C).1 i
    refine ⟨fun S => e S.1, fun S S' h => Subtype.ext (e.injective h), fun S => he S.1,
      fun P hP => ?_⟩
    let P' : MMP.Mori.PrimeDivisor (C.junction i).Y := P
    obtain ⟨w, hw, hwe⟩ := he (e.symm P')
    haveI := (C.junction i).isBirationalMorphism.isDominant
    have hwe' : P'.valuationOver (C.junction i).p = w :=
      (congrArg (fun R : MMP.Mori.PrimeDivisor (C.junction i).Y =>
        R.valuationOver (C.junction i).p) (e.apply_symm_apply P')).symm.trans hwe
    obtain ⟨a, -, hΘ⟩ := (C.junction i).Θ_eq
    have hP' : (inverseTransformDivisor (C.junction i).p (T.B i) +
        ∑ s : C.I i, Finsupp.single ((C.junction i).E s) (1 - a s)) P' ≠ 0 := by
      rw [← hΘ]; exact hP
    have hlab := isLabel_of_isTransportedValuationFrom C i _ P' hP' (e.symm P') (hwe' ▸ hw)
    exact ⟨⟨e.symm P', hlab⟩, e.apply_symm_apply P'⟩
  · obtain ⟨e, he1, he2⟩ := (TerminalChain.exists_equiv_primeDivisor C).2.1 i
    refine ⟨fun S => e k k.2.le S.1, fun S S' h => Subtype.ext ((e k k.2.le).injective h),
      fun S => he1 k k.2.le S.1, fun P hP => ?_⟩
    let P' : MMP.Mori.PrimeDivisor (modelSeq (C.junction i).Y (C.bridge i).P.Y k) := P
    set Q := (e k k.2.le).symm P'
    have hc := coeff_bridge_eq C i e he2 k k.2.le Q
    rw [show e k k.2.le Q = P' from (e k k.2.le).apply_symm_apply P'] at hc
    have hP0 : ((C.bridge i).P.boundary 0).coeff (e 0 (Nat.zero_le _) Q) ≠ 0 := by
      rw [← hc]; exact hP
    obtain ⟨w, hw, hdom, hwe⟩ := he1 0 (Nat.zero_le _) Q
    have hR := valuationOver_eq_of_valuationOver_comp C i (e 0 (Nat.zero_le _) Q) w hdom hwe
    obtain ⟨a, -, hΘ⟩ := (C.bridge i).isDecreasedBoundary
    have hP' : (inverseTransformDivisor (C.junction i).p (T.B i) +
        ∑ s : C.I i, Finsupp.single ((C.junction i).E s) (1 - a s))
          (e 0 (Nat.zero_le _) Q) ≠ 0 := by
      rw [← hΘ]; exact hP0
    have hlab := isLabel_of_isTransportedValuationFrom C i _ _ hP' Q (hR ▸ hw)
    exact ⟨⟨Q, hlab⟩, (e k k.2.le).apply_symm_apply P'⟩

/-- The model varieties of a terminal chain are projective `ℚ`-factorial threefolds. -/
private theorem isProjectiveVariety_and_isQFactorial_and_dim (C : TerminalChain T) :
    ∀ x : C.ModelIndex, MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x) ∧
      IsQFactorial (C.modelStructure x) ∧ topologicalKrullDim (C.model x) = 3
  | ⟨i, none⟩ => ⟨(C.junction i).isProjectiveVariety, (C.junction i).isQFactorial,
      (C.junction i).dim_eq⟩
  | ⟨i, some k⟩ => ⟨((C.bridge i).P.isThreefoldStepDiagram k k.2).isProjectiveVariety_minus,
      (C.bridge i).P.isQFactorial k k.2.le,
      ((C.bridge i).P.isThreefoldStepDiagram k k.2).dim_minus⟩

end Chain

/-- **Models of a prepared chain satisfy the echo hypotheses.** Let `(Y, Θ)` be the model of
the prepared chain `Q` indexed by `x`. Then `(Y, Θ)` is a terminal pair, `Y` is a projective
`ℚ`-factorial complex variety of dimension `3`, the labels `S` of the chain have centres `c S`
on `Y` which are pairwise distinct prime divisors, every prime divisor in the support of `Θ` is
one of them, the coefficients `b_S` of `Θ` at `c S` lie in `[0, 1)`, and the local ring of `Y`
at the generic point of every irreducible closed curve `V ⊆ Y` is regular. -/
@[mmp "lem_mmp_indexd_models_echo_setting"]
public theorem echoSetting_model {T : StabilizedTail} (Q : PreparedChain T) (x : Q.ModelIndex) :
    IsKltTerminalPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1) ∧
      MMP.Mori.IsProjectiveVariety ℂ (Q.chain.modelStructure x.1) ∧
      IsQFactorial (Q.chain.modelStructure x.1) ∧
      topologicalKrullDim (Q.chain.model x.1) = 3 ∧
      (∃ c : Q.chain.Label → MMP.Mori.PrimeDivisor (Q.chain.model x.1), Function.Injective c ∧
        (∀ S, Q.chain.IsLabelCentre S x.1 (c S)) ∧
        (∀ P, (Q.chain.modelBoundary x.1).coeff P ≠ 0 → P ∈ Set.range c) ∧
        ∀ S, 0 ≤ (Q.chain.modelBoundary x.1).coeff (c S) ∧
          (Q.chain.modelBoundary x.1).coeff (c S) < 1) ∧
      ∀ V : IrreducibleCloseds (Q.chain.model x.1),
        topologicalKrullDim (V : Set (Q.chain.model x.1)) = 1 →
        IsRegularLocalRing ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) := by
  have hterm := isKltTerminalPair_model Q.chain x.1
  obtain ⟨hproj, hQf, hdim⟩ :=
    isProjectiveVariety_and_isQFactorial_and_dim Q.chain x.1
  obtain ⟨c, hinj, hc, hsupp⟩ := exists_labelCentre Q.chain x.1
  exact ⟨hterm, hproj, hQf, hdim,
    ⟨c, hinj, hc, hsupp, fun S => coeff_mem_Ico_of_isKltPair hterm.1 (c S)⟩,
    fun V hV => isRegularLocalRing_stalk_of_isKltTerminalPair hterm hproj hQf hdim V hV⟩

end MMP.Fourfold.StabilizedTail.PreparedChain

end
