module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Singularities.DltFloorComplement
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltSemiampleFloorPencil
public import MMP.AlgebraicGeometry.MMP.Fourfold.BirationalFloorLowering
public import MMP.AlgebraicGeometry.Singularities.DltFloor.Sdlt
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedSdltThreefold
public import MMP.AlgebraicGeometry.MMP.BasepointFree.DltFloorSemiample
public import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.RingTheory.Kaehler.PluriformProduct
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentExistence
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# Nef complemented dlt fourfolds over a birational base are good

Let `(M, B)` be a `ℚ`-factorial dlt pair with rational boundary on a projective complex fourfold,
and let `g : M ⟶ Z` be a projective birational morphism to a normal projective variety. Suppose
that `D = K_M + B` is nef over `Z` and that there is an effective `ℚ`-Cartier `ℚ`-divisor `A`
with `(M, B + A)` log canonical and `D + A ∼_ℚ g^*H` for a `ℚ`-Cartier `ℚ`-divisor `H` on `Z`.
Then `D` is semiample over `Z`.

## Main results

* `MMP.Fourfold.IsDltPair.isRelativelySemiample_of_add_qLinearlyEquivalent_pullback`.

## Implementation notes

The pull-back `g^*H` is `MMP.Mori.QDivisor.pullback` along `g`, which needs the image of the
generic point of `M` to lie outside `Supp H`; since `g` is birational, that image is the generic
point of `Z`, so this condition (`hgH`) holds for every `H` and only makes the pull-back
defined. The canonical divisor `K_M` is any canonical divisor of `M`; whether `K_M + B` is nef or
semiample over `Z` does not depend on the choice.

## References

* [C. Birkar, *Existence of log canonical flips and a special LMMP*][BirkarLC]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Divisors with real coefficients -/

/-- The birational transform of divisors commutes with regarding a `ℚ`-divisor as an
`ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : QDivisor X) :
    RationalMap.transformDivisor φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (RationalMap.transformDivisor φ D) := by
  classical
  have hs : ∀ {Z : Scheme.{0}} (Q : MMP.Mori.PrimeDivisor Z) (r : ℚ),
      QDivisor.toRDivisor (Finsupp.single Q r) = Finsupp.single Q (r : ℝ) :=
    fun Q r => Finsupp.mapRange_single (hf := map_zero (Rat.castHom ℝ).toAddMonoidHom)
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D D' h h' => simp only [map_add, h, h']
  | single P r =>
    rw [hs, RationalMap.transformDivisor_single, RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor φ P with
    | none => exact (map_zero _).symm
    | some E => exact (hs E r).symm

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-Cartier pull-back. -/
private theorem isRCartierPullback_pullback {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {D : QDivisor X} (hDq : D.IsQCartier) (hB : ∀ Z, f (componentGenericPoint Y Z) ∉ D.supp) :
    MMP.Flips.IsRCartierPullback f (QDivisor.toRDivisor D)
      (QDivisor.toRDivisor (D.pullback hDq hB)) := by
  have hG := QDivisor.isPullback_pullback hDq hB
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, hD₀c⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  obtain ⟨D₀', hD₀', hp⟩ := hG _ hm D₀ hD₀ hD₀c
  have hmR : ((D.cartierIndex hDq : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => ((D.cartierIndex hDq : ℕ) : ℝ)⁻¹, fun _ => D₀, fun _ => D₀',
    fun _ => hD₀c, ?_, fun _ => ⟨_, hp⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    ext P
    have := congrArg (fun T : QDivisor X => T.coeff P) hD₀
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((D₀.coeff P : ℤ) : ℝ) = (((D₀.coeff P : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast
    field_simp
  · rw [Fin.sum_univ_one]
    ext P
    have := congrArg (fun T : QDivisor Y => T.coeff P) hD₀'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
    simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
      smul_eq_mul]
    rw [show ((D₀'.coeff P : ℤ) : ℝ) = (((D₀'.coeff P : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast
    field_simp

/-- A `ℚ`-linear equivalence `m (D₁ - D₂) = div φ`, read as an identity of `ℝ`-divisors. -/
private theorem smul_toRDivisor_eq_iff {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X]
    (D₁ D₂ : QDivisor X) (m : ℕ) (φ : (RationalFunctions X)ˣ) :
    (m : ℤ) • (D₁ - D₂) = Divisor.toQDivisor (principalDivisor φ) ↔
      (m : ℝ) • QDivisor.toRDivisor D₁ =
        (m : ℝ) • QDivisor.toRDivisor D₂ + Divisor.toRDivisor (principalDivisor φ) := by
  constructor
  · intro h
    ext P
    have := congrArg (fun T : QDivisor X => T.coeff P) h
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast] at this
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, smul_eq_mul]
    have h' := congrArg (fun t : ℚ => (t : ℝ)) this
    push_cast at h'
    linarith
  · intro h
    ext P
    have := congrArg (fun T : RDivisor X => T.coeff P) h
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      QDivisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, smul_eq_mul] at this
    simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      Divisor.coeff_toQDivisor, zsmul_eq_mul, Int.cast_natCast]
    have h' : (((m : ℚ) * (D₁.coeff P - D₂.coeff P) : ℚ) : ℝ) =
        (((principalDivisor φ).coeff P : ℚ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'

/-- The adjoint `K + B` of a `ℚ`-divisor, read as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_toRDivisor {X : Scheme.{0}} (K : Divisor X) (B : QDivisor X) :
    MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [MMP.Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- `K + B ∼_ℚ D` is the identity `m (K + B) = m D + div u` of `ℝ`-divisors for some `m > 0`. -/
private theorem qLinearlyEquivalent_iff_smul_logCanonicalDivisor_eq {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (K : Divisor X) (B D : QDivisor X) :
    (Divisor.toQDivisor K + B).QLinearlyEquivalent D ↔
      ∃ m : ℕ, 0 < m ∧ ∃ u : (RationalFunctions X)ˣ,
        (m : ℝ) • MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
          (m : ℝ) • QDivisor.toRDivisor D + Divisor.toRDivisor (principalDivisor u) := by
  simp only [QDivisor.QLinearlyEquivalent, smul_toRDivisor_eq_iff, logCanonicalDivisor_toRDivisor]

/-! ### The common resolution lies over the base -/

/-- The restriction of a partial map to the generic point is read off its domain. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{0}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{0}}
    [IsIntegral X] [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Two morphisms from an integral scheme to a separated scheme which agree at the generic
point are equal. -/
private theorem eq_of_fromSpecStalk_genericPoint_comp_eq {W Z : Scheme.{0}} [IsIntegral W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {a b : W ⟶ Z}
    (h : W.fromSpecStalk (genericPoint W) ≫ a = W.fromSpecStalk (genericPoint W) ≫ b) :
    a = b := by
  have hr : a.toRationalMap = b.toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom, h]
  have e := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)
    (f := a.toPartialMap) (g := b)).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp hr)
  have e' : W.topIso.hom ≫ a = W.topIso.hom ≫ b := by
    refine e.trans ?_
    rw [Scheme.topIso_hom]
    rfl
  exact (cancel_epi _).mp e'

/-- **A common resolution of models over `Z` commutes over `Z`.** If `φ : X ⤏ Y` lies over
`g : X ⟶ Z` and `g_Y : Y ⟶ Z`, and `p : W ⟶ X`, `q : W ⟶ Y` is a common resolution with
`q ∘ p⁻¹ = φ`, then `g ∘ p = g_Y ∘ q`. -/
private theorem comp_eq_comp_of_isLogComparisonResolution {X Y Z W : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {sY : Y ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} {φ : X.RationalMap Y} {KX : Divisor X} {BX : RDivisor X}
    {KY : Divisor Y} {BY : RDivisor Y} {p : W ⟶ X} {q : W ⟶ Y} {h : X.RationalMap W}
    {GX GY : RDivisor W}
    (hR : IsLogComparisonResolution sX sY sW φ KX BX KY BY p q h GX GY)
    [IsSeparated (Z ↘ ⊤_ Scheme)] {g : X ⟶ Z} {gY : Y ⟶ Z}
    (hover : MMP.Flips.RationalMap.IsOver g gY φ) : p ≫ g = q ≫ gY := by
  haveI : IsDominant p := hR.isBirationalMorphism_left.isDominant
  have hW : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
    obtain ⟨e, he1, he2⟩ := hR.isInverse
    rw [← hR.compHom_eq, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
      specMap_functionFieldMap_fromFunctionField_symm p e he1]
  apply eq_of_fromSpecStalk_genericPoint_comp_eq
  rw [← Category.assoc, ← Category.assoc, ← hW, ← functionFieldMap_fromSpecStalk p,
    Category.assoc, Category.assoc, ← MMP.Flips.RationalMap.fromFunctionField_hom,
    ← MMP.Flips.RationalMap.fromFunctionField_compHom, hover]

/-! ### The floor -/

/-- On a log canonical pair every coefficient of the boundary is at most one: the log
discrepancy of a prime divisor `P` is `1 - coeff_P`. -/
private theorem coeff_le_one_of_isLogCanonicalPair {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ≤ 1 := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, -, hlc⟩ := hB
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  have hd : IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hX P) (-B.coeff P) := by
    refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
    rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
    have hPV : (P.support ∩ (V : Set X)).Nonempty := by
      refine ⟨P.genericPoint, ?_, hV⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    linear_combination -hτ.2 P hPV
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd
    (show IsProper (𝟙 X) from inferInstance))
  have h1 : ((B.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast h1

/-- For a pair `(X, Δ)`, `K + Δ` is `ℚ`-Cartier for every canonical divisor `K` of `X`. -/
private theorem isQCartier_add_of_isPair {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} {Δ : QDivisor X} (h : MMP.Mori.IsPair sX Δ)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    (Divisor.toQDivisor K + Δ).IsQCartier := by
  obtain ⟨hX, n₀, K₀, hK₀, hQ⟩ := h
  exact hQ.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK₀ hK)

/-- If `m₀ B` is the Cartier divisor `D₀` for an `f`-nef `ℚ`-divisor `B`, then `D₀` has
nonnegative degree on every curve contracted by `f`. -/
private theorem degreeOn_nonneg_of_isRelativelyNef {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {f : X ⟶ Y} {B : QDivisor X}
    (hB : B.IsRelativelyNef sX f) {m₀ : ℕ} (hm₀ : 0 < m₀) {D₀ : Divisor X} (hD₀c : D₀.IsCartier)
    (hD₀B : Divisor.toQDivisor D₀ = (m₀ : ℤ) • B) (C : MMP.Mori.ProperCurve sX)
    (hC : C.IsContractedBy f) : 0 ≤ D₀.degreeOn ℂ sX C.ι C.dim_le hD₀c := by
  have h := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hB hB.fst C hC
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le B hB.fst hm₀ D₀ hD₀c hD₀B] at h
  exact_mod_cast ((div_nonneg_iff.1 h).resolve_right fun h => (Nat.cast_pos.2 hm₀).not_ge h.2).1

/-- **Residue adjunction for one adjunction step.** Let `(S, B_S)` arise from `(Y, B_Y)` by an
adjunction step `j : S ⟶ Y`, `Y` a normal complex variety of dimension `n + 1 ≥ 2` with
`K_Y + B_Y` `ℚ`-Cartier. There are a rational top form `σ` on `Y` with `div σ ∼ K_Y` and a
rational top form `ρ` on `S` with `div ρ ∼ K_S` such that `div ρ + B_S` is the pull-back of the
`ℚ`-Cartier divisor `div σ + B_Y`: `ρ` is the Poincaré residue of a form `σ` with a simple pole
along `S`. -/
private theorem exists_isPullback_divisorOfForm_add {Y S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY)
    {n : ℕ} (hn : 0 < n) (hdim : topologicalKrullDim Y = n + 1) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY (n + 1)) {BY : QDivisor Y}
    (hBq : (Divisor.toQDivisor KY + BY).IsQCartier)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {j : S ⟶ Y} [LocallyOfFiniteType (j ≫ sY)] {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) {KS : Divisor S} (hKS : KS.IsCanonicalDivisor (j ≫ sY) n) :
    ∃ (σ : RationalPluriForms sY (n + 1) 1) (ρ : RationalPluriForms (j ≫ sY) n 1),
      (divisorOfForm σ).LinearlyEquivalent KY ∧ (divisorOfForm ρ).LinearlyEquivalent KS ∧
      (Divisor.toQDivisor (divisorOfForm σ) + BY).IsQCartier ∧
      ∃ hgen : ∀ Z : irreducibleComponents S,
          j (componentGenericPoint S Z) ∉ (Divisor.toQDivisor (divisorOfForm σ) + BY).supp,
        (Divisor.toQDivisor (divisorOfForm σ) + BY).IsPullback j hgen
          (Divisor.toQDivisor (divisorOfForm ρ) + BS) := by
  classical
  obtain ⟨hSn, P, -, hPr, hci, -⟩ := id hS
  haveI := hci
  obtain ⟨σ, hσ0, hσP, ρ, hρ, hρ0⟩ :=
    exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero sY hdim j P hPr
  have hσK : (divisorOfForm σ).LinearlyEquivalent KY := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hYn hKY hσ0
  have hρK : (divisorOfForm ρ).LinearlyEquivalent KS := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSn hKS hρ0
  have hD : (Divisor.toQDivisor (divisorOfForm σ) + BY).IsQCartier :=
    hBq.add_of_linearlyEquivalent hσK.symm
  exact ⟨σ, ρ, hσK, hρK, hD,
    hS.isPullback_divisorOfForm_add_of_isPoincareResidue hdim P hPr σ hσ0 hσP ρ hρ hD⟩

/-- **Changing the canonical divisor in a Cartier multiple.** If `L = c (K' + B)` and `K' ∼ K`,
then `L + c (K - K') = c (K + B)`, and it is linearly equivalent to `L`. -/
private theorem linearlyEquivalent_add_zsmul_sub {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {K K' L : Divisor X} {B : QDivisor X}
    {c : ℤ} (hK : K'.LinearlyEquivalent K)
    (hL : Divisor.toQDivisor L = c • (Divisor.toQDivisor K' + B)) :
    (L + c • (K - K')).LinearlyEquivalent L ∧
      Divisor.toQDivisor (L + c • (K - K')) = c • (Divisor.toQDivisor K + B) := by
  refine ⟨?_, ?_⟩
  · rw [Divisor.linearlyEquivalent_iff_sub_mem_range, add_sub_cancel_left]
    exact AddSubgroup.zsmul_mem _ (Divisor.linearlyEquivalent_iff_sub_mem_range.mp hK.symm) _
  · rw [map_add, map_zsmul, map_sub, hL, ← smul_add]
    congr 1
    abel

/-- **Adjunction preserves relative nefness.** Let `(S, B_S)` arise from `(Y, B_Y)` by one
adjunction step `j : S ⟶ Y` (`MMP.Fourfold.IsAdjunctionStep`), `Y` a normal complex variety of
dimension `n + 1 ≥ 2` with `K_Y + B_Y` `ℚ`-Cartier and nef over `g : Y ⟶ Z`. Then `K_S + B_S` is
nef over `g ∘ j`. Indeed for a rational top form `σ` with a simple pole along `S` and Poincaré
residue `ρ`, `div ρ + B_S` is the pull-back of `div σ + B_Y`, so the degree of `K_S + B_S` on a
curve `C ⊆ S` contracted over `Z` is a positive multiple of the degree of `K_Y + B_Y` on `j(C)`,
or zero. -/
private theorem isRelativelyNef_of_isAdjunctionStep {Y Z S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] [QuasiCompact sY] [IsSeparated sY] (hYn : IsNormalVariety ℂ sY)
    {n : ℕ} (hn : 0 < n) (hdim : topologicalKrullDim Y = n + 1) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY (n + 1)) {BY : QDivisor Y}
    (hBq : (Divisor.toQDivisor KY + BY).IsQCartier) {gY : Y ⟶ Z}
    (hnef : QDivisor.IsRelativelyNef sY gY (Divisor.toQDivisor KY + BY))
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {j : S ⟶ Y} [QuasiCompact (j ≫ sY)] {BS : QDivisor S} (hS : IsAdjunctionStep sY BY j BS)
    {KS : Divisor S} (hKS : KS.IsCanonicalDivisor (j ≫ sY) n) :
    QDivisor.IsRelativelyNef (j ≫ sY) (j ≫ gY) (Divisor.toQDivisor KS + BS) := by
  classical
  obtain ⟨hSn, P, -, hPr, hci, -⟩ := id hS
  haveI := hci
  haveI : LocallyOfFiniteType (j ≫ sY) := hSn.1.toLocallyOfFiniteType
  obtain ⟨σ, ρ, hσK, hρK, hD, hgen, hpb⟩ :=
    exists_isPullback_divisorOfForm_add hYn hn hdim hKY hBq hS hKS
  obtain ⟨c, hc, L, hL, hLc⟩ := hD.exists_pos
  obtain ⟨L', hL', hLp⟩ := hpb c hc L hL hLc
  have hL'c : L'.IsCartier := hLp.isCartier hLc
  set LY : Divisor Y := L + (c : ℤ) • (KY - divisorOfForm σ)
  set LS : Divisor S := L' + (c : ℤ) • (KS - divisorOfForm ρ)
  obtain ⟨hLYL, hLY⟩ := linearlyEquivalent_add_zsmul_sub hσK hL
  obtain ⟨hLSL, hLS⟩ := linearlyEquivalent_add_zsmul_sub hρK hL'
  have hLYc : LY.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hLYL hLc
  have hLSc : LS.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hLSL hL'c
  have hSq : (Divisor.toQDivisor KS + BS).IsQCartier :=
    ⟨c, by exact_mod_cast hc.ne', LS, hLS, hLSc⟩
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (k := ℂ) (j ≫ sY) hSq
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul ℂ (j ≫ sY) C.ι C.dim_le _ hSq hc LS hLSc hLS]
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  haveI := hLc.isInvertibleModule_divisorialSheaf
  haveI := hLYc.isInvertibleModule_divisorialSheaf
  haveI := hL'c.isInvertibleModule_divisorialSheaf
  haveI := hLSc.isInvertibleModule_divisorialSheaf
  have e1 : LS.degreeOn ℂ (j ≫ sY) C.ι C.dim_le hLSc =
      C.degree ℂ ((Scheme.Modules.pullback j).obj L.divisorialSheaf) := by
    rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ (j ≫ sY) C.ι C.dim_le
      (hLSL.divisorialSheafIso ≪≫ hLp.divisorialSheafIso (hBc := hLc))]
    rfl
  rw [e1, C.degree_pullback j rfl]
  split_ifs with h
  · set Γ : MMP.Mori.ProperCurve sY := ⟨j C.point, h⟩ with hΓ
    haveI : IsProper (Γ.ι ≫ sY) := MMP.Mori.ProperCurve.isProper_ι_comp Γ
    suffices hdeg : 0 ≤ Γ.degree ℂ L.divisorialSheaf by
      exact_mod_cast (mul_nonneg (Nat.cast_nonneg _) hdeg : (0 : ℤ) ≤ _)
    have e2 : Γ.degree ℂ L.divisorialSheaf = LY.degreeOn ℂ sY Γ.ι Γ.dim_le hLYc := by
      rw [Divisor.degreeOn, degreeOn_eq_of_iso ℂ sY Γ.ι Γ.dim_le hLYL.divisorialSheafIso]
      rfl
    rw [e2]
    refine degreeOn_nonneg_of_isRelativelyNef hnef hc hLYc hLY Γ fun y hy => ?_
    have hcl : IsClosed (j '' closure {C.point}) := j.isClosedMap _ isClosed_closure
    have hsub : ({j C.point} : Set Y) ⊆ j '' closure {C.point} :=
      Set.singleton_subset_iff.mpr ⟨C.point, subset_closure rfl, rfl⟩
    obtain ⟨x, hx, rfl⟩ := closure_minimal hsub hcl hy
    simpa only [Scheme.Hom.comp_apply] using hC x hx
  · exact le_rfl

/-- The support of an integral multiple of a divisor lies in the support of the divisor. -/
private theorem notMem_supp_zsmul {X : Scheme.{0}} {D : Divisor X} {x : X} (hx : x ∉ D.supp)
    (n : ℤ) : x ∉ (n • D).supp := by
  intro h
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  refine hx (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, fun h0 => hE ?_, hxE⟩)
  rw [DivisorWithCoeffs.coeff_smul, h0, smul_zero]

/-- The support of a sum of divisors lies in the union of the supports. -/
private theorem notMem_supp_add {X : Scheme.{0}} {D₁ D₂ : Divisor X} {x : X} (h₁ : x ∉ D₁.supp)
    (h₂ : x ∉ D₂.supp) : x ∉ (D₁ + D₂).supp := by
  intro h
  obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [DivisorWithCoeffs.coeff_add] at hE
  by_cases hE₁ : D₁.coeff E = 0
  · rw [hE₁, zero_add] at hE
    exact h₂ (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE, hxE⟩)
  · exact h₁ (DivisorWithCoeffs.mem_supp_iff.mpr ⟨E, hE₁, hxE⟩)

/-- **The complement identity restricts to every floor component as a pulled-back invertible
sheaf.** Let `Y` be a normal complex variety of dimension `n + 1 ≥ 2`, `g_Y : Y ⟶ Z` dominant,
`A_Y` `ℚ`-Cartier and `K_Y + B_Y + A_Y ∼_ℚ g_Y^* H` for a `ℚ`-Cartier `H` on `Z`. For a family of
adjunction steps `(S_i, B_{S_i})` of `(Y, B_Y)` along `j_i`, missing `Supp A_Y` generically, there
are an invertible sheaf `M` on `Z` and `m > 0` such that `m(K_{S_i} + B_{S_i} + j_i^* A_Y)` is a
divisor whose sheaf is `(g_Y ∘ j_i)^* M`, for every `i`. -/
private theorem exists_divisorialSheaf_iso_pullback {Y Z : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    [CompactSpace Z] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    (hYn : IsNormalVariety ℂ sY) {n : ℕ} (hn : 0 < n) (hdim : topologicalKrullDim Y = n + 1)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY (n + 1)) {BY AY : QDivisor Y}
    (hBq : (Divisor.toQDivisor KY + BY).IsQCartier) (hAYq : AY.IsQCartier)
    {gY : Y ⟶ Z} {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgYH : ∀ T : irreducibleComponents Y, gY (componentGenericPoint Y T) ∉ H.supp)
    (hlinY : (Divisor.toQDivisor KY + BY + AY).QLinearlyEquivalent (H.pullback hHq hgYH))
    {ι : Type} {S : ι → Scheme.{0}} [∀ i, IsIntegral (S i)] [∀ i, IsLocallyNoetherian (S i)]
    [∀ i, IsNormal (S i)] [∀ i, CompactSpace (S i)] {j : ∀ i, S i ⟶ Y}
    [∀ i, LocallyOfFiniteType (j i ≫ sY)] {BS : ∀ i, QDivisor (S i)}
    (hS : ∀ i, IsAdjunctionStep sY BY (j i) (BS i)) {KS : ∀ i, Divisor (S i)}
    (hKS : ∀ i, (KS i).IsCanonicalDivisor (j i ≫ sY) n)
    (hA : ∀ i, ∀ T : irreducibleComponents (S i), j i (componentGenericPoint (S i) T) ∉ AY.supp) :
    ∃ (MZ : Z.Modules) (_ : Stacks.Ample.IsInvertibleModule Z MZ),
      ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (S i),
        Divisor.toQDivisor L =
          (m : ℤ) • (Divisor.toQDivisor (KS i) + BS i + AY.pullback hAYq (hA i)) ∧
        Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (j i ≫ gY)).obj MZ) := by
  classical
  obtain ⟨c₀, hc₀, F₀, hF₀, hF₀c⟩ := hBq.exists_pos
  obtain ⟨c₂, hc₂, F₂, hF₂, hF₂c⟩ := hAYq.exists_pos
  obtain ⟨cH, hcH, DH, hDH, hDHc⟩ := hHq.exists_pos
  obtain ⟨m₁, hm₁, u, hu⟩ := hlinY
  obtain ⟨D', hD', hD'p⟩ := QDivisor.isPullback_pullback hHq hgYH cH hcH DH hDH hDHc
  set N : ℤ := (c₀ : ℤ) * c₂ * m₁ with hN
  set M : ℤ := (c₀ : ℤ) * c₂ * cH with hM
  have hNDHc : (N • DH).IsCartier := hDHc.zsmul N
  haveI := hNDHc.isInvertibleModule_divisorialSheaf
  have hDHB : ∀ T : irreducibleComponents Y, gY (componentGenericPoint Y T) ∉ DH.supp := by
    intro T
    rw [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hcH.ne') hDH]
    exact hgYH T
  have hND'p := hD'p.zsmul hDHc N (fun T => notMem_supp_zsmul (hDHB T) N)
  refine ⟨(N • DH).divisorialSheaf, inferInstance, m₁ * (c₀ * c₂ * cH), by positivity,
    fun i => ?_⟩
  obtain ⟨σ, ρ, hσK, hρK, hD, hgen, hpb⟩ :=
    exists_isPullback_divisorOfForm_add hYn hn hdim hKY hBq (hS i) (hKS i)
  obtain ⟨φ, hφ⟩ := hσK
  obtain ⟨ψ, hψ⟩ := hρK
  set L₁ : Divisor Y := F₀ + (c₀ : ℤ) • principalDivisor φ with hL₁def
  have hL₁ : Divisor.toQDivisor L₁ = (c₀ : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BY) := by
    rw [hL₁def, map_add, map_zsmul, ← hφ, map_sub, hF₀, ← smul_add]
    congr 1
    abel
  have hL₁c : L₁.IsCartier := hF₀c.add ((Divisor.isCartier_principalDivisor φ).zsmul _)
  obtain ⟨L₁', hL₁', hL₁p⟩ := hpb c₀ hc₀ L₁ hL₁ hL₁c
  obtain ⟨L₂', hL₂', hL₂p⟩ := QDivisor.isPullback_pullback hAYq (hA i) c₂ hc₂ F₂ hF₂ hF₂c
  have hB₁ : ∀ T : irreducibleComponents (S i), j i (componentGenericPoint (S i) T) ∉ L₁.supp := by
    intro T
    rw [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hc₀.ne') hL₁]
    exact hgen T
  have hB₂ : ∀ T : irreducibleComponents (S i), j i (componentGenericPoint (S i) T) ∉ F₂.supp := by
    intro T
    rw [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hc₂.ne') hF₂]
    exact hA i T
  have hE₁ := hL₁p.zsmul hL₁c ((c₂ : ℤ) * cH) (fun T => notMem_supp_zsmul (hB₁ T) _)
  have hE₂ := hL₂p.zsmul hF₂c ((c₀ : ℤ) * cH) (fun T => notMem_supp_zsmul (hB₂ T) _)
  set E : Divisor Y := ((c₂ : ℤ) * cH) • L₁ + ((c₀ : ℤ) * cH) • F₂ with hEdef
  set E' : Divisor (S i) := ((c₂ : ℤ) * cH) • L₁' + ((c₀ : ℤ) * cH) • L₂' with hE'def
  have hEc : E.IsCartier := (hL₁c.zsmul _).add (hF₂c.zsmul _)
  have hEB : ∀ T : irreducibleComponents (S i), j i (componentGenericPoint (S i) T) ∉ E.supp :=
    fun T => notMem_supp_add (notMem_supp_zsmul (hB₁ T) _) (notMem_supp_zsmul (hB₂ T) _)
  have hEp : E.IsPullback (j i) hEB E' :=
    Divisor.IsPullback.add (hL₁c.zsmul _) (hF₂c.zsmul _) hEB hE₁ hE₂
  have hm₁Ep := hEp.zsmul hEc (m₁ : ℤ) (fun T => notMem_supp_zsmul (hEB T) _)
  have hlin : ((m₁ : ℤ) • E).LinearlyEquivalent (N • D') := by
    rw [Divisor.linearlyEquivalent_iff_sub_mem_range]
    have heq : (m₁ : ℤ) • E - N • D' =
        M • principalDivisor u + ((m₁ : ℤ) * M) • principalDivisor φ := by
      apply Divisor.toQDivisor_injective
      simp only [hEdef, map_sub, map_add, map_zsmul, hL₁, hF₂, hD', ← hu, ← hφ, hN, hM]
      module
    rw [heq]
    exact add_mem (AddSubgroup.zsmul_mem _ (AddMonoidHom.mem_range.mpr ⟨Additive.ofMul u, rfl⟩) _)
      (AddSubgroup.zsmul_mem _ (AddMonoidHom.mem_range.mpr ⟨Additive.ofMul φ, rfl⟩) _)
  set L : Divisor (S i) := (m₁ : ℤ) • E' + ((m₁ : ℤ) * M) • -principalDivisor ψ with hLdef
  have hLL : L.LinearlyEquivalent ((m₁ : ℤ) • E') := by
    rw [Divisor.linearlyEquivalent_iff_sub_mem_range,
      show L - (m₁ : ℤ) • E' = ((m₁ : ℤ) * M) • -principalDivisor ψ from add_sub_cancel_left _ _]
    exact AddSubgroup.zsmul_mem _ (neg_mem (AddMonoidHom.mem_range.mpr ⟨Additive.ofMul ψ, rfl⟩)) _
  refine ⟨L, ?_, ⟨?_⟩⟩
  · simp only [hLdef, hE'def, map_add, map_zsmul, map_neg, ← hψ, map_sub, hL₁', hL₂', hM]
    push_cast
    module
  · have hm₁Ec : ((m₁ : ℤ) • E).IsCartier := hEc.zsmul _
    exact hLL.divisorialSheafIso ≪≫ hm₁Ep.divisorialSheafIso (hBc := hm₁Ec) ≪≫
      (Scheme.Modules.pullback (j i)).mapIso hlin.divisorialSheafIso ≪≫
      (Scheme.Modules.pullback (j i)).mapIso (hND'p.divisorialSheafIso (hBc := hNDHc)) ≪≫
      (Scheme.Modules.pullbackComp (j i) gY).app _

/-! ### Powers of local generators -/

/-- **Powers of rational pluriforms on a line.** On an integral scheme of dimension `d`, there is
a `c`-th power map from rational `a`-canonical forms to rational `ac`-canonical forms sending
`f ω^{⊗a}` to `f^c ω^{⊗ac}` for every rational function `f` and every top form `ω`. -/
private theorem exists_powForm {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) (a c : ℕ) :
    letI := functionFieldAlgebra sX
    ∃ P : RationalPluriForms sX d a → RationalPluriForms sX d ((a * c : ℕ) : ℤ),
      ∀ (f : X.functionField) (ω : ⋀[X.functionField]^d Ω[X.functionField⁄ℂ]),
        P (f • formPow ω a) = f ^ c • formPow ω (a * c) := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  refine ⟨fun τ => ((ZTensorPower.basis b a).repr τ ()) ^ c • formPow (b ()) (a * c),
    fun f ω => ?_⟩
  have hpow : ∀ e : ℕ, formPow ω e = (b.repr ω ()) ^ e • formPow (b ()) e := fun e => by
    conv_lhs => rw [← basis_unit_repr_smul b ω]
    rw [formPow_smul]
  simp only
  rw [hpow a, smul_smul, repr_smul_formPow, hpow (a * c), smul_smul, mul_pow, ← pow_mul,
    mul_comm a c]

/-- The `c`-th power map is `c`-homogeneous: `P(f τ) = f^c P(τ)`. -/
private theorem powForm_smul {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d) {a c : ℕ}
    (P : RationalPluriForms sX d a → RationalPluriForms sX d ((a * c : ℕ) : ℤ))
    (hP : letI := functionFieldAlgebra sX
      ∀ (f : X.functionField) (ω : ⋀[X.functionField]^d Ω[X.functionField⁄ℂ]),
        P (f • formPow ω a) = f ^ c • formPow ω (a * c))
    (f : X.functionField) (τ : RationalPluriForms sX d a) : P (f • τ) = f ^ c • P τ := by
  let := functionFieldAlgebra sX
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hd
  set r := (ZTensorPower.basis b a).repr τ () with hr
  have hτ : τ = r • formPow (b ()) a := eq_repr_smul_formPow b τ
  have hPτ : P τ = r ^ c • formPow (b ()) (a * c) := by
    rw [show P τ = P (r • formPow (b ()) a) from congrArg P hτ]
    exact hP _ _
  rw [hPτ, show f • τ = (f * r) • formPow (b ()) a by rw [mul_smul, ← hτ]; rfl, hP, mul_pow,
    mul_smul]
  rfl

/-- A residue presentation of `s` along `P` gives one of the `c`-th power of `s`. -/
private theorem isLogResiduePresentation_powForm {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n a c : ℕ} {i : N.ι} {P : MMP.Mori.PrimeDivisor (N.X i)}
    {V : T.Opens} {hP : (N.n i).base P.genericPoint ∈ V} {α : Fin (n - 1) → Γ(T, V)}
    {g : Γ(T, V)} {ε : ℤ} {s : RationalPluriForms (N.n i ≫ sT) n a}
    (h : IsLogResiduePresentation N n a i P V hP α g ε s)
    (Pw : RationalPluriForms (N.n i ≫ sT) n a →
      RationalPluriForms (N.n i ≫ sT) n ((a * c : ℕ) : ℤ))
    (hPw : letI := functionFieldAlgebra (N.n i ≫ sT)
      ∀ (f : (N.X i).functionField) (ω : ⋀[(N.X i).functionField]^n Ω[(N.X i).functionField⁄ℂ]),
        Pw (f • formPow ω a) = f ^ c • formPow ω (a * c)) :
    IsLogResiduePresentation N n (a * c) i P V hP α (g ^ c) (ε ^ c) (Pw s) := by
  obtain ⟨z, h', hz, hs, hda, hres⟩ := h
  refine ⟨z, h' ^ c, hz, ?_, hda, ?_⟩
  · rw [hs, map_pow]
    exact hPw _ _
  · beta_reduce at hres ⊢
    simp only [map_pow, hres, mul_pow]
    push_cast
    rfl

/-- The `c`-th powers of a local generator of `𝒪_T(mL)` on `U` form a local generator of
`𝒪_T(mcL)` on `U`. -/
private theorem isAdjointGeneratorOn_powForm {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n m c : ℕ} {Θ : ∀ i, QDivisor (N.X i)}
    (hdim : ∀ i, topologicalKrullDim (N.X i) = n)
    (Pw : ∀ i, RationalPluriForms (N.n i ≫ sT) n m →
      RationalPluriForms (N.n i ≫ sT) n ((m * c : ℕ) : ℤ))
    (hPw : ∀ i, letI := functionFieldAlgebra (N.n i ≫ sT)
      ∀ (f : (N.X i).functionField) (ω : ⋀[(N.X i).functionField]^n Ω[(N.X i).functionField⁄ℂ]),
        Pw i (f • formPow ω m) = f ^ c • formPow ω (m * c))
    {U : T.Opens} {s : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hs : IsAdjointGeneratorOn N n m Θ U s) :
    IsAdjointGeneratorOn N n (m * c) Θ U (fun i => Pw i (s i)) := by
  obtain ⟨hgo, hres⟩ := hs
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  refine ⟨fun i => ?_, fun i j P P' h₁ h₂ h₃ h₄ => ?_⟩
  · let := functionFieldAlgebra (N.n i ≫ sT)
    obtain ⟨b⟩ := exists_basis_topForms (sX := N.n i ≫ sT) (hdim i)
    have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := N.n i ≫ sT) (hdim i)
    set f := (ZTensorPower.basis b m).repr (s i) () with hf_def
    have hf0 : f ≠ 0 := repr_ne_zero_of_ne_zero b (hgo i).1
    have hsi : s i = f • formPow (b ()) m := eq_repr_smul_formPow b (s i)
    have hP : Pw i (s i) = f ^ c • formPow (b ()) (m * c) := by rw [hsi]; exact hPw i _ _
    have hP0 : Pw i (s i) ≠ 0 := by
      rw [hP, ← ZTensorPower.basis_natCast]
      exact smul_ne_zero (pow_ne_zero _ hf0) ((ZTensorPower.basis b _).ne_zero ())
    refine ⟨hP0, fun Γ hΓ => ?_⟩
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := (hgo i).2 Γ hΓ
    rw [hNΓ _ _ (hgo i).1, ← hf_def] at e1
    rw [hNΓ _ _ hP0, hP, repr_smul_formPow, ← zpow_natCast, ord_zpow _ hf0]
    push_cast at e1 ⊢
    linear_combination (c : ℚ) * e1
  · obtain ⟨V, hP, hP', a, g, hpr, hpr'⟩ := hres i j P P' h₁ h₂ h₃ h₄
    refine ⟨V, hP, hP', a, g ^ c, by
      have := isLogResiduePresentation_powForm hpr (Pw i) (hPw i)
      rwa [one_pow] at this, ?_⟩
    have := isLogResiduePresentation_powForm hpr' (Pw j) (hPw j)
    rwa [← pow_mul] at this

/-- **Raising the degree of the generation statement.** If over a neighbourhood of every point of
`Z` a family of rational `m`-canonical forms on the normalization of `T` is locally a multiple
of a local generator of `𝒪_T(mL)`, a unit multiple at the given point, the same holds in degree
`mc`, for the `c`-th powers. -/
private theorem exists_isAdjointGeneratorOn_mul {T Z : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    {N : NormalizationComponents sT hT} {n m : ℕ} {Θ : ∀ i, QDivisor (N.X i)}
    (hdim : ∀ i, topologicalKrullDim (N.X i) = n) (f : T ⟶ Z) (c : ℕ)
    (hgen : ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V) (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n m),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N n m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i) :
    ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ sT) n ((m * c : ℕ) : ℤ)),
      ∀ y ∈ f ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ f ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ sT) n ((m * c : ℕ) : ℤ)) (a : Γ(T, U)),
          IsAdjointGeneratorOn N n (m * c) Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i := by
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ sT) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  choose Pw hPw using fun i => exists_powForm (sX := N.n i ≫ sT) (hdim i) m c
  intro x
  obtain ⟨V, hxV, t, ht⟩ := hgen x
  refine ⟨V, hxV, fun i => Pw i (t i), fun y hy => ?_⟩
  obtain ⟨U, hyU, hUV, g, a, hg, ha, hta⟩ := ht y hy
  refine ⟨U, hyU, hUV, fun i => Pw i (g i), a ^ c,
    isAdjointGeneratorOn_powForm hdim Pw hPw hg, fun h => (ha h).pow c, fun i hi => ?_⟩
  beta_reduce
  rw [hta i hi, powForm_smul (hdim i) (Pw i) (hPw i), map_pow, map_pow]

/-! ### Functions on the floor and its normalization -/

/-- Every point of `T` lies under a point of some normalization component. -/
private theorem exists_base_eq {k : Type} [Field k] {T : Scheme.{0}} {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (x : T) : ∃ i z, (N.n i).base z = x := by
  obtain ⟨φ, hφ⟩ := N.exists_iso
  have hsurj : Surjective (slcCurveNormalization T hT) := Scheme.surjective_normalization T hT
  obtain ⟨w, rfl⟩ := hsurj.surj x
  obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk N.X).surjective (φ.inv.base w)
  refine ⟨i, z, ?_⟩
  have h1 : (Limits.Sigma.ι N.X i ≫ φ.hom ≫ slcCurveNormalization T hT).base z =
      (N.n i).base z := by
    rw [hφ, Limits.Sigma.ι_desc]
  have h2 : φ.hom.base (φ.inv.base w) = w := by
    rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
    rfl
  rw [← h1, Scheme.Hom.comp_apply, ← sigmaMk_mk, hz, Scheme.Hom.comp_apply, h2]

/-- **Functions on a reduced scheme are detected on its normalization.** A function on an open
`U` of the reduced scheme `T` whose pull-back to every normalization component meeting `U`
vanishes in the function field is zero. -/
private theorem eq_zero_of_forall_germToFunctionField_eq_zero {k : Type} [Field k]
    {T : Scheme.{0}} [IsReduced T] {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {U : T.Opens} (b : Γ(T, U))
    (h : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b) = 0) : b = 0 := by
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨i, z, rfl⟩ := exists_base_eq N x
  have hzU : z ∈ N.n i ⁻¹ᵁ U := T.basicOpen_le b hx
  haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨z, hzU⟩⟩
  have hz : z ∈ (N.X i).basicOpen ((N.n i).app U b) := by
    rw [← Scheme.preimage_basicOpen]
    exact hx
  have h0 : (N.n i).app U b = 0 :=
    (N.X i).germToFunctionField_injective (N.n i ⁻¹ᵁ U)
      ((h i inferInstance).trans (map_zero _).symm)
  rw [h0, Scheme.basicOpen_zero] at hz
  exact hz

/-- A unit multiple of a local generator is a local generator. -/
private theorem isLocalGenerator_smul_of_isUnit {X : Scheme.{0}} {L : X.Modules} {W : X.Opens}
    {a : Γ(L, W)} (ha : MMP.Mori.IsLocalGenerator L W a) {u : Γ(X, W)} (hu : IsUnit u) :
    MMP.Mori.IsLocalGenerator L W (u • a) := by
  intro V hV
  obtain ⟨v, rfl⟩ := hu
  have hres : L.presheaf.map (homOfLE hV).op ((v : Γ(X, W)) • a) =
      X.presheaf.map (homOfLE hV).op (v : Γ(X, W)) • L.presheaf.map (homOfLE hV).op a :=
    MMP.Mori.modules_res_smul hV _ a
  set w : Γ(X, V)ˣ := v.map (X.presheaf.map (homOfLE hV).op).hom
  have hw : (w : Γ(X, V)) = X.presheaf.map (homOfLE hV).op (v : Γ(X, W)) := rfl
  have key : (fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op ((v : Γ(X, W)) • a)) =
      (fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op a) ∘ (fun c => c * w) := by
    funext c
    simp only [Function.comp_apply, hres, ← hw, mul_smul]
  rw [key]
  exact (ha V hV).comp (Units.mulRight_bijective w)

/-! ### Local generators of `𝒪_Y(m(K_Y + B_Y))` from local equations -/

/-- **Forms attached to local equations.** Let `C = m(K + Δ)` be a divisor on a normal complex
variety with canonical divisor `K`. There is a map `φ ↦ F(φ)` from units of `K(X)` to rational
`m`-canonical forms such that `F(φ)` generates `𝒪_X(m(K + Δ))` wherever `φ` is a local equation
of `C`, and such that `F(φ) = r F(φ')` whenever `φ⁻¹ = r φ'⁻¹` on an open `V` for a function `r`
on `V`: `F(φ)` is the form `ω^{⊗m}/φ` for a rational top form `ω` with `div ω = K`. -/
private theorem exists_chartForm {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n) {Δ : QDivisor Y} {m : ℕ}
    {C : Divisor Y} (hC : Divisor.toQDivisor C = (m : ℤ) • (Divisor.toQDivisor K + Δ)) :
    ∃ F : (RationalFunctions Y)ˣ → RationalPluriForms sY n m,
      (∀ (U : Y.Opens) (φ : (RationalFunctions Y)ˣ), C.IsLocalEquation U φ →
        GeneratesOn Δ m U (F φ)) ∧
      ∀ (φ φ' : (RationalFunctions Y)ˣ) (V : Y.Opens) [Nonempty V] (r : Γ(Y, V)),
        (∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ V),
          ((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z =
            Y.presheaf.germ V _ hZ r * ((φ'⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z) →
        F φ = (Y.germToFunctionField V).hom r • F φ' := by
  classical
  have hn := hK.topologicalKrullDim_eq
  let := functionFieldAlgebra sY
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hYn hn
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hYn hK
  have hsub : Subsingleton (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  obtain ⟨Z₀, -⟩ := exists_mem_irreducibleComponents y₀
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  let g : (RationalFunctions Y)ˣ → Y.functionField := fun φ =>
    (MMP.Positivity.componentToFunctionField Z₀).hom (φ.val Z₀)
  have hginv : ∀ φ : (RationalFunctions Y)ˣ,
      (MMP.Positivity.componentToFunctionField Z₀).hom
        (((φ⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z₀) = (g φ)⁻¹ := by
    intro φ
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    change (MMP.Positivity.componentToFunctionField Z₀).hom
      (((φ⁻¹ * φ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z₀) = 1
    rw [inv_mul_cancel, Units.val_one, Pi.one_apply, map_one]
  refine ⟨fun φ => (c ^ (m : ℤ) * (g φ)⁻¹) • ZTensorPower.basis b m (), ?_, ?_⟩
  · intro U φ hφ
    have hg0 : g φ ≠ 0 := ((φ.isUnit.map (Pi.evalRingHom _ Z₀)).map _).ne_zero
    have hg : ∀ Γ : MMP.Mori.PrimeDivisor Y, Γ.ord φ = Y.ord (g φ) Γ.genericPoint := fun Γ => by
      rw [MMP.Positivity.ord_eq_ord_componentToFunctionField Γ φ, Subsingleton.elim Γ.component Z₀]
    have hcg : c ^ (m : ℤ) * (g φ)⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg0)
    set τ : RationalPluriForms sY n m := (c ^ (m : ℤ) * (g φ)⁻¹) • ZTensorPower.basis b m ()
    have hrepr : (ZTensorPower.basis b m).repr τ () = c ^ (m : ℤ) * (g φ)⁻¹ := by
      simp [τ]
    have hτ : τ ≠ 0 := smul_ne_zero hcg ((ZTensorPower.basis b m).ne_zero ())
    refine ⟨hτ, fun Γ hΓ => ?_⟩
    obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hN 1 ω hω0
    have e2 := hN m τ hτ
    rw [hrepr, Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg0), ord_zpow _ hc,
      ← zpow_neg_one, ord_zpow _ hg0] at e2
    rw [← hc_def, hω Γ] at e1
    have hCΓ : (C.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ) := by
      have := congrArg (fun D : QDivisor Y => D.coeff Γ) hC
      rw [mul_add]
      simpa [zsmul_eq_mul] using this
    have hgΓ : C.coeff Γ = Y.ord (g φ) Γ.genericPoint := (hφ Γ hΓ).trans (hg Γ)
    have e1' : (K.coeff Γ : ℚ) = Y.ord c Γ.genericPoint + N := by exact_mod_cast (by omega : _)
    have e2' : (Γ.ordForm τ : ℚ) =
        m * Y.ord c Γ.genericPoint + -1 * Y.ord (g φ) Γ.genericPoint + m * N := by
      exact_mod_cast e2
    have hgΓ' : (C.coeff Γ : ℚ) = Y.ord (g φ) Γ.genericPoint := by exact_mod_cast hgΓ
    linear_combination e2' - (m : ℚ) * e1' + hgΓ' - hCΓ
  · intro φ φ' V _ r hrel
    obtain ⟨v⟩ : Nonempty V := inferInstance
    obtain ⟨Z₁, hZ₁⟩ := exists_mem_irreducibleComponents v.1
    obtain rfl : Z₁ = Z₀ := Subsingleton.elim _ _
    have hZ₀ : componentGenericPoint Y Z₁ ∈ V :=
      ((isGenericPoint_componentGenericPoint Y Z₁).mem_open_set_iff V.isOpen).mpr
        ⟨v.1, hZ₁, v.2⟩
    have key : (g φ)⁻¹ = (Y.germToFunctionField V).hom r * (g φ')⁻¹ := by
      rw [← hginv, ← hginv, hrel Z₁ hZ₀, map_mul]
      congr 1
      exact TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hZ₀ _ r
    simp only []
    rw [key, show c ^ (m : ℤ) * ((Y.germToFunctionField V).hom r * (g φ')⁻¹) =
      (Y.germToFunctionField V).hom r * (c ^ (m : ℤ) * (g φ')⁻¹) by ring]
    exact mul_smul _ _ _

/-! ### Residues of local generators -/

/-- **Residues of unit multiples.** If `τ = r τ'` for a function `r` on an open `V` containing
the generic point of the floor component `S`, then `Res_S τ = (r|_S) Res_S τ'`. -/
private theorem isPoincareResidue_eq_germ_smul {Y S : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY]
    [IsIntegral S] {j : S ⟶ Y} {BY : QDivisor Y} {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) {n m : ℕ} {V : Y.Opens} [Nonempty V]
    [Nonempty (j ⁻¹ᵁ V)] (hV : j (genericPoint S) ∈ V) (r : Γ(Y, V))
    {τ τ' : RationalPluriForms sY (n + 1) m} (hτ : τ = (Y.germToFunctionField V).hom r • τ')
    {ρ ρ' : RationalPluriForms (j ≫ sY) n m} (hρ : IsPoincareResidue sY j n m τ ρ)
    (hρ' : IsPoincareResidue sY j n m τ' ρ') :
    ρ = (S.germToFunctionField (j ⁻¹ᵁ V)).hom (j.app V r) • ρ' := by
  have h1 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ'
    (Y.presheaf.germ V _ hV r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← hτ, Scheme.Hom.germ_stalkMap_apply] at h1
  exact IsPoincareResidue.unique hS hρ h1

/-- **The residue of a local generator is nonzero.** Let `(S, B_S)` arise from `(Y, B_Y)` by an
adjunction step along the prime divisor `P = j(S)`, with `B_Y ≤ 1`, and let `τ` generate
`𝒪_Y(m(K_Y + B_Y))` on an open `W` meeting `P`. Then `Res_S τ ≠ 0`: `τ` has a pole of order
exactly `m` along `P`, so `τ = v σ^{⊗m}` for a form `σ` with a simple pole along `P` and a unit
`v` of `𝒪_{Y,P}`, and `Res_S τ = v̄ (Res_S σ)^{⊗m}`. -/
private theorem isPoincareResidue_ne_zero_of_generatesOn {Y S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY) {n : ℕ} (hn : 0 < n)
    (hdim : topologicalKrullDim Y = n + 1)
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] {j : S ⟶ Y}
    [LocallyOfFiniteType (j ≫ sY)] {BY : QDivisor Y} {BS : QDivisor S}
    (hS : IsAdjunctionStep sY BY j BS) (hdimS : topologicalKrullDim S = n)
    (hle : ∀ P, BY.coeff P ≤ 1) {M : ℕ} (hM : 0 < M) {W : Y.Opens}
    {τ : RationalPluriForms sY (n + 1) M} (hτ : GeneratesOn BY M W τ)
    (hW : j (genericPoint S) ∈ W) {ρ : RationalPluriForms (j ≫ sY) n M}
    (hρ : IsPoincareResidue sY j n M τ ρ) : ρ ≠ 0 := by
  classical
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  obtain ⟨hSn, P, hP1, hPr, hci, -⟩ := id hS
  haveI := hci
  have hjP : j (genericPoint S) = P.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hPr
  have hBP : BY.coeff P = 1 := le_antisymm (hle P) hP1
  have hdim' : topologicalKrullDim Y = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  obtain ⟨σ, hσ0, hσP, ρσ, hρσ, hρσ0⟩ :=
    exists_ordForm_eq_neg_one_isPoincareResidue_of_charZero sY hdim j P hPr
  set τ₀ := MMP.CyclicChartDifferent.Aux.pluriPow σ M with hτ₀def
  have hτ₀0 : τ₀ ≠ 0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdim' hσ0 M
  have hordτ₀ : P.ordForm τ₀ = -((M + 1 : ℕ) : ℤ) := by
    rw [hτ₀def, MMP.CyclicChartDifferent.Aux.ordForm_pluriPow hdim' hσ0 P M, hσP]
    ring
  have hρ₀ := MMP.CyclicChartDifferent.Aux.isPoincareResidue_pluriPow P hjP hdim hρσ M
  have hρ₀0 := MMP.CyclicChartDifferent.Aux.pluriPow_ne_zero hdimS hρσ0 M
  let := functionFieldAlgebra sY
  obtain ⟨b⟩ := exists_basis_topForms (sX := sY) hdim'
  set B := ZTensorPower.basis b ((M + 1 : ℕ) : ℤ)
  have hc₀ : B.repr τ₀ () ≠ 0 := repr_ne_zero_of_ne_zero b hτ₀0
  set u := B.repr τ () / B.repr τ₀ ()
  have hτu : τ = u • τ₀ := by
    rw [← basis_unit_repr_smul B τ, ← basis_unit_repr_smul B τ₀]
    exact (by rw [← mul_smul, div_mul_cancel₀ _ hc₀] :
      (B.repr τ () • B () : ZTensorPower _ _ _) = u • B.repr τ₀ () • B ())
  have hu0 : u ≠ 0 := div_ne_zero (repr_ne_zero_of_ne_zero b hτ.1) hc₀
  have hPW : (P.support ∩ (W : Set Y)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hjP ▸ hW⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hordu : Y.ord u P.genericPoint = 0 := by
    have e1 := hτ.2 P hPW
    rw [hτu, P.ordForm_smul_of_topologicalKrullDim_eq hdim' hu0 hτ₀0, hordτ₀, hBP] at e1
    push_cast at e1
    have : (Y.ord u P.genericPoint : ℚ) = 0 := by linarith
    exact_mod_cast this
  obtain ⟨v, hv, hvu⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero
    (j (genericPoint S)) hu0 fun Γ hΓ => by
      rw [hjP] at hΓ
      obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hΓ
      exact hordu
  have h1 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hρ₀ v
  rw [hvu, ← hτu] at h1
  rw [IsPoincareResidue.unique hS hρ h1]
  exact smul_ne_zero ((hv.map (j.stalkMap (genericPoint S)).hom).ne_zero) hρ₀0

/-- The image of a section in the function field does not change under restriction. -/
private theorem germToFunctionField_app_res {k : Type} [Field k] {T : Scheme.{0}}
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) (i : N.ι) {U U' : T.Opens} (hU : U' ≤ U) (f : Γ(T, U))
    [Nonempty (N.n i ⁻¹ᵁ U')] [Nonempty (N.n i ⁻¹ᵁ U)] :
    ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom
        ((N.n i).app U' (T.presheaf.map (homOfLE hU).op f)) =
      ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U f) := by
  have h := congrArg (fun φ => ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom (φ.hom f))
    ((N.n i).naturality (homOfLE hU).op)
  simp only [CommRingCat.comp_apply] at h
  rw [h]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- **Comparing coefficients against two families of forms.** On a reduced `T`, if
`t = b ρ = b' ρ'` on every normalization component meeting `U` and `ρ = r ρ'` with `ρ' ≠ 0`, then
`b r = b'` on `U`. -/
private theorem mul_eq_of_smul_eq {k : Type} [Field k] {T : Scheme.{0}} [IsReduced T]
    {sT : T ⟶ Spec (.of k)}
    {hT : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sT hT) {n m : ℕ} {U : T.Opens} {b b' r : Γ(T, U)}
    {t ρ ρ' : ∀ i, RationalPluriForms (N.n i ≫ sT) n m}
    (hρ : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      ρ i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U r) • ρ' i)
    (hρ'0 : ∀ i, ρ' i ≠ 0)
    (ht : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b) • ρ i)
    (ht' : ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
      t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U b') • ρ' i) :
    b * r = b' := by
  refine sub_eq_zero.mp (eq_zero_of_forall_germToFunctionField_eq_zero N _ fun i hi => ?_)
  have h := (ht i hi).symm.trans (ht' i hi)
  rw [hρ i hi, smul_smul] at h
  rw [map_sub, map_sub, map_mul, map_mul]
  exact sub_eq_zero.mpr (smul_left_injective _ (hρ'0 i) h)

/-- The restriction of a local generator to a smaller open is a local generator. -/
private theorem isLocalGenerator_res {X : Scheme.{0}} {L : X.Modules} {W W' : X.Opens}
    {a : Γ(L, W)} (ha : MMP.Mori.IsLocalGenerator L W a) (hW : W' ≤ W) :
    MMP.Mori.IsLocalGenerator L W' (L.presheaf.map (homOfLE hW).op a) := by
  intro V hV
  have h := ha V (hV.trans hW)
  rwa [show L.presheaf.map (homOfLE (hV.trans hW)).op a =
    L.presheaf.map (homOfLE hV).op (L.presheaf.map (homOfLE hW).op a) from
      (MMP.Mori.modules_res_res hV hW a).symm] at h

/-! ### Relative generation from local generators -/

/-- A locally surjective morphism of sheaves of modules is an epimorphism. -/
private theorem epi_of_locally_surjective {X : Scheme.{0}} {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ (U : X.Opens) (b : Γ(B, U)) (x : X), x ∈ U → ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧
      ∃ a : Γ(A, V), φ.val.app (Opposite.op V) a = B.presheaf.map (homOfLE hV).op b) :
    Epi φ := by
  have h' : TopCat.Presheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map φ).hom :=
    (TopCat.Presheaf.isLocallySurjective_iff _).2 fun U b x hx => by
      obtain ⟨V, hV, hxV, a, ha⟩ := h U b x hx
      exact ⟨V, hV, ⟨a, ha⟩, hxV⟩
  have hls : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map φ) := h'
  have : Epi ((SheafOfModules.toSheaf _).map φ) := Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf _).epi_of_epi_map this

/-- Morphisms of modules commute with restriction of sections. -/
private theorem modules_hom_app_res {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G)
    {A B : X.Opens} (i : A ⟶ B) (x : Γ(F, B)) :
    φ.app A (F.presheaf.map i.op x) = G.presheaf.map i.op (φ.app B x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
  exact congrArg (fun f => f x) (congrArg ConcreteCategory.hom (φ.mapPresheaf.naturality i.op))

/-- **Relative generation from a section generating near each point.** If every point `x` of `T`
has an open `V ∋ f(x)` and a section of `F` over `f⁻¹(V)` which freely generates `F` near `x`,
then `f^* f_* F ⟶ F` is surjective. -/
private theorem epi_counit_of_forall_exists_isLocalGenerator {T Z : Scheme.{0}} (f : T ⟶ Z)
    (F : T.Modules)
    (h : ∀ x : T, ∃ (V : Z.Opens) (_ : f x ∈ V) (σ : Γ(F, f ⁻¹ᵁ V)) (U₀ : T.Opens) (_ : x ∈ U₀)
      (hU₀ : U₀ ≤ f ⁻¹ᵁ V), MMP.Mori.IsLocalGenerator F U₀ (F.presheaf.map (homOfLE hU₀).op σ)) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction f
  set A := (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward f).obj F)
  refine epi_of_locally_surjective _ fun U b x hx => ?_
  obtain ⟨V, hxV, σ, U₀, hxU₀, hU₀, hgen⟩ := h x
  let y : Γ(A, f ⁻¹ᵁ V) := (adj.unit.app ((Scheme.Modules.pushforward f).obj F)).app V σ
  have hy : (adj.counit.app F).app (f ⁻¹ᵁ V) y = σ :=
    congrArg (fun ψ => (Scheme.Modules.Hom.app ψ V).hom σ) (adj.right_triangle_components F)
  have hVU₀ : U ⊓ U₀ ≤ U₀ := inf_le_right
  have hVU : U ⊓ U₀ ≤ U := inf_le_left
  set r := hgen.coord hVU₀ (F.presheaf.map (homOfLE hVU).op b)
  refine ⟨U ⊓ U₀, hVU, ⟨hx, hxU₀⟩, r • A.presheaf.map (homOfLE (hVU₀.trans hU₀)).op y, ?_⟩
  have hnat : (adj.counit.app F).app (U ⊓ U₀) (A.presheaf.map (homOfLE (hVU₀.trans hU₀)).op y) =
      F.presheaf.map (homOfLE (hVU₀.trans hU₀)).op ((adj.counit.app F).app (f ⁻¹ᵁ V) y) :=
    modules_hom_app_res (adj.counit.app F) (homOfLE (hVU₀.trans hU₀)) y
  change (adj.counit.app F).app (U ⊓ U₀) (r • A.presheaf.map (homOfLE (hVU₀.trans hU₀)).op y) =
    F.presheaf.map (homOfLE hVU).op b
  rw [Scheme.Modules.Hom.app_smul, hnat, hy, ← MMP.Mori.modules_res_res hVU₀ hU₀ σ]
  exact hgen.coord_smul_eq hVU₀ _

/-- **Generation of the adjoint on the floor gives relative generation of the restricted
adjoint.** Let `ι : T ⟶ Y` be the floor of a pair `(Y, B_Y)` on a normal complex fourfold, with
normalization components `νᵢ : Tᵢ ⟶ T` and boundaries `Θᵢ`, such that the residues of local
generators of `𝒪_Y(m(K_Y + B_Y))` are exactly the local generators of the adjoint on `T` up to
units of `𝒪_T`. If over a neighbourhood of every point of `Z` a family of forms on the `Tᵢ` is
locally a multiple of a local generator of the adjoint, a unit multiple at the given point, then
`ι^* 𝒪_Y(E)` is generated over `Z` for some Cartier multiple `E = m'(K_Y + B_Y)`. -/
private theorem exists_epi_counit_of_isAdjointGeneratorOn
    {Y Z T : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sY] (hYn : IsNormalVariety ℂ sY)
    {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY (3 + 1)) {BY : QDivisor Y}
    (hBY : MMP.Mori.IsPair sY BY)
    (ι : T ⟶ Y) [IsClosedImmersion ι] [IsReduced T]
    {hfin : ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents (ι ≫ sY) hfin) (Θ : ∀ i, QDivisor (N.X i))
    [∀ i, CompactSpace (N.X i)] (hdimN : ∀ i, topologicalKrullDim (N.X i) = 3)
    (hstep : ∀ i, IsAdjunctionStep sY BY (N.n i ≫ ι) (Θ i)) (hle : ∀ P, BY.coeff P ≤ 1)
    (hdict : ∀ m : ℕ, 0 < m → ((m : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor →
      ∀ (W : Y.Opens) (τ : RationalPluriForms sY (3 + 1) m), GeneratesOn BY m W τ →
        (∃ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 m,
          ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
            IsPoincareResidue sY (N.n i ≫ ι) 3 m τ (ρ i)) ∧
        ∀ ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 m,
          (∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
            IsPoincareResidue sY (N.n i ≫ ι) 3 m τ (ρ i)) →
          (∀ i, ρ i ≠ 0) → IsAdjointGeneratorOn N 3 m Θ (ι ⁻¹ᵁ W) ρ ∧
          ∀ U : T.Opens, U ≤ ι ⁻¹ᵁ W → ∀ g : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 m,
            IsAdjointGeneratorOn N 3 m Θ U g →
            ∃ e : Γ(T, U)ˣ, ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
              g i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom
                ((N.n i).app U (e : Γ(T, U))) • ρ i)
    (gY : Y ⟶ Z) {m : ℕ} (hm : 0 < m)
    (hgen : ∀ x : T, ∃ (V : Z.Opens) (_ : (ι ≫ gY) x ∈ V)
      (t : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 m),
      ∀ y ∈ (ι ≫ gY) ⁻¹ᵁ V, ∃ (U : T.Opens) (_ : y ∈ U) (_ : U ≤ (ι ≫ gY) ⁻¹ᵁ V)
        (g : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 m) (a : Γ(T, U)),
          IsAdjointGeneratorOn N 3 m Θ U g ∧ (y = x → IsUnit a) ∧
          ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U)),
            t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U)).hom ((N.n i).app U a) • g i) :
    ∃ m' : ℕ, 0 < m' ∧ ∃ E : Divisor Y,
      Divisor.toQDivisor E = (m' : ℚ) • (Divisor.toQDivisor KY + BY) ∧ E.IsCartier ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction (ι ≫ gY)).counit.app
        ((Scheme.Modules.pullback ι).obj E.divisorialSheaf)) := by
  classical
  haveI : ∀ i, LocallyOfFiniteType (N.n i ≫ ι ≫ sY) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  haveI : ∀ i, LocallyOfFiniteType ((N.n i ≫ ι) ≫ sY) := fun i =>
    (N.isNormalVariety i).1.toLocallyOfFiniteType
  have hBq := isQCartier_add_of_isPair hBY hKY
  obtain ⟨c, hc, F, hF, hFc⟩ := hBq.exists_pos
  have hgenM := exists_isAdjointGeneratorOn_mul (sT := ι ≫ sY) (N := N) (Θ := Θ) hdimN
    (ι ≫ gY) c hgen
  set M : ℕ := m * c with hMdef
  have hMpos : 0 < M := Nat.mul_pos hm hc
  set E : Divisor Y := (m : ℤ) • F with hEdef
  have hEq : Divisor.toQDivisor E = (M : ℤ) • (Divisor.toQDivisor KY + BY) := by
    rw [hEdef, map_zsmul, hF, smul_smul, hMdef]
    push_cast
    ring_nf
  have hEc : E.IsCartier := hFc.zsmul _
  have hMC : ((M : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor := ⟨E, hEq, hEc⟩
  refine ⟨M, hMpos, E, by rw [hEq, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ], hEc, ?_⟩
  haveI := hEc.isInvertibleModule_divisorialSheaf
  obtain ⟨Fch, hFgen, hFrel⟩ := exists_chartForm hYn hKY hEq
  have hdimY : topologicalKrullDim Y = (3 : ℕ) + 1 := by
    rw [hKY.topologicalKrullDim_eq]; norm_cast
  refine epi_counit_of_forall_exists_isLocalGenerator (ι ≫ gY) _ fun x => ?_
  obtain ⟨V, hxV, t, ht⟩ := hgenM x
  set O := (ι ≫ gY) ⁻¹ᵁ V with hOdef
  have data : ∀ y : O, ∃ (U' : T.Opens) (_ : y.1 ∈ U') (_ : U' ≤ O) (b : Γ(T, U'))
      (W : Y.Opens) (_ : U' ≤ ι ⁻¹ᵁ W) (ψ : (RationalFunctions Y)ˣ) (_ : E.IsLocalEquation W ψ)
      (ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 M),
      (∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
        IsPoincareResidue sY (N.n i ≫ ι) 3 M (Fch ψ) (ρ i)) ∧ (∀ i, ρ i ≠ 0) ∧
      (y.1 = x → IsUnit b) ∧
      ∀ i (_ : Nonempty (N.n i ⁻¹ᵁ U')),
        t i = ((N.X i).germToFunctionField (N.n i ⁻¹ᵁ U')).hom ((N.n i).app U' b) • ρ i := by
    intro y
    obtain ⟨U, hyU, hUV, g, a, hg, ha, hta⟩ := ht y.1 y.2
    obtain ⟨W, hyW, ψ, hψ⟩ := hEc (ι y.1)
    have hτ := hFgen W ψ hψ
    obtain ⟨ρ', hρ'⟩ := (hdict M hMpos hMC W (Fch ψ) hτ).1
    let ρ : ∀ i, RationalPluriForms (N.n i ≫ ι ≫ sY) 3 M := fun i =>
      if ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty then ρ' i else g i
    have hρres : ∀ i, ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty →
        IsPoincareResidue sY (N.n i ≫ ι) 3 M (Fch ψ) (ρ i) := fun i h => by
      simp only [ρ, if_pos h]
      exact hρ' i h
    have hρ0 : ∀ i, ρ i ≠ 0 := by
      intro i
      by_cases h : ((N.n i ≫ ι) ⁻¹ᵁ W : Set (N.X i)).Nonempty
      · simp only [ρ, if_pos h]
        obtain ⟨z, hz⟩ := h
        have hgW : (N.n i ≫ ι) (genericPoint (N.X i)) ∈ W :=
          ((genericPoint_spec (N.X i)).specializes trivial).map
            (N.n i ≫ ι).base.hom.continuous |>.mem_open W.isOpen hz
        exact isPoincareResidue_ne_zero_of_generatesOn hYn (n := 3) (by norm_num) hdimY
          (hstep i) (hdimN i) hle hMpos hτ hgW (hρ' i ⟨z, hz⟩)
      · simp only [ρ, if_neg h]
        exact (hg.1 i).1
    set U' : T.Opens := U ⊓ ι ⁻¹ᵁ W with hU'def
    obtain ⟨e, he⟩ := ((hdict M hMpos hMC W (Fch ψ) hτ).2 ρ hρres hρ0).2 U' inf_le_right g
      ⟨fun i => (hg.1 i).mono fun _ hx => hx.1, fun i j P P' h₁ h₂ h₃ h₄ =>
        hg.2 i j P P' h₁ h₂.1 h₃ h₄⟩
    refine ⟨U', ⟨hyU, hyW⟩, inf_le_left.trans hUV,
      T.presheaf.map (homOfLE (inf_le_left : U' ≤ U)).op a * e, W, inf_le_right, ψ, hψ, ρ,
      hρres, hρ0, fun h => ((ha h).map (T.presheaf.map (homOfLE inf_le_left).op).hom).mul
        e.isUnit, fun i hi => ?_⟩
    haveI : Nonempty (N.n i ⁻¹ᵁ U) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
    rw [hta i inferInstance, he i hi, smul_smul, map_mul, map_mul,
      germToFunctionField_app_res N i inf_le_left a]
  choose U' hyU' hU'O b W hW ψ hψ ρ hρres hρ0 hbx ht' using data
  set FT := (Scheme.Modules.pullback ι).obj E.divisorialSheaf with hFT
  set u := (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app E.divisorialSheaf with hu
  let pb : ∀ A : Y.Opens, Γ(E.divisorialSheaf, A) → Γ(FT, ι ⁻¹ᵁ A) := fun A a => u.app A a
  have hpbnat : ∀ (A B : Y.Opens) (h : A ≤ B) (a : Γ(E.divisorialSheaf, B)),
      FT.presheaf.map (homOfLE (ι.preimage_mono h)).op (pb B a) =
        pb A (E.divisorialSheaf.presheaf.map (homOfLE h).op a) := fun A B h a =>
    (modules_hom_app_res u (homOfLE h) a).symm
  have hpbsmul : ∀ (A : Y.Opens) (r : Γ(Y, A)) (a : Γ(E.divisorialSheaf, A)),
      pb A (r • a) = ι.app A r • pb A a := fun A r a =>
    Scheme.Modules.Hom.app_smul u r a
  let s : ∀ y : O, Γ(FT, U' y) := fun y =>
    FT.presheaf.map (homOfLE (hW y)).op (pb (W y) (hψ y).invSection)
  let σ : ∀ y : O, Γ(FT, U' y) := fun y => b y • s y
  have hcompat : TopCat.Presheaf.IsCompatible FT.presheaf U' σ := by
    intro y z
    have hQW : U' y ⊓ U' z ≤ ι ⁻¹ᵁ (W y ⊓ W z) := fun p hp => ⟨hW y hp.1, hW z hp.2⟩
    have hgz := (hψ z).isLocalGenerator_invSection
    set r := hgz.coord (inf_le_right : W y ⊓ W z ≤ W z)
      (E.divisorialSheaf.presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op
        (hψ y).invSection) with hrdef
    have hr : r • E.divisorialSheaf.presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op
        (hψ z).invSection =
        E.divisorialSheaf.presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op
          (hψ y).invSection :=
      hgz.coord_smul_eq _ _
    have hs : ∀ v : O, ∀ (hv : U' y ⊓ U' z ≤ U' v) (hvW : W y ⊓ W z ≤ W v),
        FT.presheaf.map (homOfLE hv).op (s v) =
          FT.presheaf.map (homOfLE hQW).op
            (pb (W y ⊓ W z) (E.divisorialSheaf.presheaf.map (homOfLE hvW).op
              (hψ v).invSection)) := by
      intro v hv hvW
      rw [← hpbnat _ _ hvW, MMP.Mori.modules_res_res]
      exact (MMP.Mori.modules_res_res hQW (ι.preimage_mono hvW) _).symm
    set rT : Γ(T, U' y ⊓ U' z) := T.presheaf.map (homOfLE hQW).op (ι.app (W y ⊓ W z) r)
      with hrT
    have hsyz : FT.presheaf.map (homOfLE (inf_le_left : U' y ⊓ U' z ≤ U' y)).op (s y) =
        rT • FT.presheaf.map (homOfLE (inf_le_right : U' y ⊓ U' z ≤ U' z)).op (s z) := by
      rw [hs y inf_le_left inf_le_left, hs z inf_le_right inf_le_right, ← hr, hpbsmul]
      exact MMP.Mori.modules_res_smul hQW _ _
    have hrel : ∀ (Z : irreducibleComponents Y) (hZ : componentGenericPoint Y Z ∈ W y ⊓ W z),
        (((ψ y)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z =
          Y.presheaf.germ (W y ⊓ W z) _ hZ r *
            (((ψ z)⁻¹ : (RationalFunctions Y)ˣ) : RationalFunctions Y) Z := fun Z hZ =>
      (congrArg (fun a : Γ(E.divisorialSheaf, W y ⊓ W z) =>
        (show E.divisorialSubmodule (W y ⊓ W z) from a).1 ⟨Z, hZ⟩) hr).symm
    have hb : T.presheaf.map (homOfLE (inf_le_left : U' y ⊓ U' z ≤ U' y)).op (b y) * rT =
        T.presheaf.map (homOfLE (inf_le_right : U' y ⊓ U' z ≤ U' z)).op (b z) := by
      refine mul_eq_of_smul_eq N (t := t) (ρ := ρ y) (ρ' := ρ z) (fun i hi => ?_) (hρ0 z)
        (fun i hi => ?_) (fun i hi => ?_)
      · haveI := hi
        set p := hi.some.1
        have hp : p ∈ N.n i ⁻¹ᵁ (U' y ⊓ U' z) := hi.some.2
        have hpW : (N.n i ≫ ι) p ∈ W y ⊓ W z := hQW hp
        haveI : Nonempty (W y ⊓ W z : Y.Opens) := ⟨⟨_, hpW⟩⟩
        haveI : Nonempty ((N.n i ≫ ι) ⁻¹ᵁ (W y ⊓ W z)) := ⟨⟨p, hpW⟩⟩
        haveI : Nonempty (N.n i ⁻¹ᵁ (ι ⁻¹ᵁ (W y ⊓ W z))) := ⟨⟨p, hpW⟩⟩
        have hgW : (N.n i ≫ ι) (genericPoint (N.X i)) ∈ W y ⊓ W z :=
          ((genericPoint_spec (N.X i)).specializes trivial).map
            (N.n i ≫ ι).base.hom.continuous |>.mem_open (W y ⊓ W z).isOpen hpW
        have h1 := isPoincareResidue_eq_germ_smul (hstep i) hgW r
          (hFrel _ _ (W y ⊓ W z) r hrel) (hρres y i ⟨p, hpW.1⟩) (hρres z i ⟨p, hpW.2⟩)
        rw [h1]
        congr 1
        rw [hrT, germToFunctionField_app_res N i hQW (ι.app (W y ⊓ W z) r)]
        rfl
      · haveI := hi
        haveI : Nonempty (N.n i ⁻¹ᵁ U' y) := ⟨⟨hi.some.1, hi.some.2.1⟩⟩
        rw [germToFunctionField_app_res N i (inf_le_left : U' y ⊓ U' z ≤ U' y) (b y)]
        exact ht' y i inferInstance
      · haveI := hi
        haveI : Nonempty (N.n i ⁻¹ᵁ U' z) := ⟨⟨hi.some.1, hi.some.2.2⟩⟩
        rw [germToFunctionField_app_res N i (inf_le_right : U' y ⊓ U' z ≤ U' z) (b z)]
        exact ht' z i inferInstance
    show FT.presheaf.map (homOfLE (inf_le_left : U' y ⊓ U' z ≤ U' y)).op (b y • s y) =
      FT.presheaf.map (homOfLE (inf_le_right : U' y ⊓ U' z ≤ U' z)).op (b z • s z)
    rw [MMP.Mori.modules_res_smul, MMP.Mori.modules_res_smul, hsyz, smul_smul, hb]
  obtain ⟨σO, hσO, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := ⟨FT.presheaf, FT.isSheaf⟩) U' O
    (fun y => homOfLE (hU'O y))
    (fun z hz => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hyU' ⟨z, hz⟩⟩) σ
    hcompat
  have hxO : x ∈ O := hxV
  refine ⟨V, hxV, σO, U' ⟨x, hxO⟩, hyU' _, hU'O _, ?_⟩
  rw [hσO ⟨x, hxO⟩]
  exact isLocalGenerator_smul_of_isUnit (isLocalGenerator_res
    (isLocalGenerator_pullback_unit ι _ (hψ _).isLocalGenerator_invSection) (hW _))
    (hbx _ rfl)

/-- **The adjoint restricted to the whole floor is generated over the base.** On the crepant
`ℚ`-factorial dlt model `(Y, B_Y)` with nonzero floor `T = ⌊B_Y⌋`, a complement `A_Y` with
`K_Y + B_Y + A_Y ∼_ℚ g_Y^* H` makes some Cartier multiple `E = m(K_Y + B_Y)` generated over `Z`
on `T`: `(g_Y|_T)^* (g_Y|_T)_* (E|_T) ⟶ E|_T` is surjective. -/
private theorem exists_epi_counit_floor {Y Z : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hdimY : topologicalKrullDim Y = 4)
    (hQY : IsQFactorial sY) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor sY 4)
    {BY : QDivisor Y} (hBY : MMP.Intersection.IsDltPair sY BY)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {gY : Y ⟶ Z} (hgYZ : gY ≫ sZ = sY) (hgY : IsProjectiveMorphism gY)
    (hnefY : QDivisor.IsRelativelyNef sY gY (Divisor.toQDivisor KY + BY))
    (hT0 : BY.roundDown ≠ 0)
    {AY : QDivisor Y} (hAY0 : 0 ≤ AY) (hAYq : AY.IsQCartier)
    (hlcY : MMP.Intersection.IsLogCanonicalPair sY (BY + AY))
    {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgYH : ∀ T : irreducibleComponents Y, gY (componentGenericPoint Y T) ∉ H.supp)
    (hlinY : (Divisor.toQDivisor KY + BY + AY).QLinearlyEquivalent (H.pullback hHq hgYH)) :
    ∃ m : ℕ, 0 < m ∧ ∃ E : Divisor Y,
      Divisor.toQDivisor E = (m : ℚ) • (Divisor.toQDivisor KY + BY) ∧ E.IsCartier ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction
          (BY.roundDown.suppIdeal.subschemeι ≫ gY)).counit.app
        ((Scheme.Modules.pullback BY.roundDown.suppIdeal.subschemeι).obj E.divisorialSheaf)) := by
  classical
  set ι := BY.roundDown.suppIdeal.subschemeι with hιdef
  haveI : IsReduced BY.roundDown.suppIdeal.subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  have hrange : Set.range ι.base = ⋃ P ∈ BY.roundDown.support, (P.support : Set Y) := by
    change Set.range ι = _
    rw [Scheme.IdealSheafData.range_subschemeι, DivisorWithCoeffs.suppIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, DivisorWithCoeffs.coe_supp]
  have hdim3 : topologicalKrullDim Y = ((3 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdimY]; rfl
  obtain ⟨-, hfin, N, Δ, Θ, hsdlt, hstep, -, hdict⟩ :=
    isCMScheme_and_exists_isSdltAdjointPair_of_isDltPair (k := ℂ) (n := 3) hdim3 hKY hY hQY
      ⟨inferInstance, inferInstance, hBY.1.1, hBY.1.2.1⟩ hBY hT0 ι hrange
  have hci : ∀ i, IsClosedImmersion (N.n i ≫ ι) := fun i => by
    obtain ⟨-, P, -, -, hc, -⟩ := hstep i
    exact hc
  haveI hNc : ∀ i, CompactSpace (N.X i) := fun i =>
    haveI := hci i
    QuasiCompact.compactSpace_of_compactSpace (N.n i ≫ ι)
  haveI : QuasiCompact sY := quasiCompact_of_compactSpace sY
  haveI hNqc : ∀ i, QuasiCompact (N.n i ≫ ι ≫ sY) := fun i => by
    haveI := hci i
    rw [← Category.assoc]
    infer_instance
  choose KN hKN using hsdlt.exists_isDltPair
  have hKNc : ∀ i, (KN i).IsCanonicalDivisor (N.n i ≫ ι ≫ sY) 3 := fun i => (hKN i).1.2.1
  have hYv := ((MMP.Mori.isProjectiveVariety_iff ℂ sY).mp hY).1
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  haveI : IsSeparated sY := hYv.toIsSeparated
  have hnef : ∀ i, (Divisor.toQDivisor (KN i) + Θ i).IsRelativelyNef (N.n i ≫ ι ≫ sY)
      (N.n i ≫ ι ≫ gY) := fun i => by
    have h := isRelativelyNef_of_isAdjunctionStep (j := N.n i ≫ ι) hBY.1.1.1 (n := 3)
      (by norm_num) (by rw [hdimY]; rfl) hKY (isQCartier_add_of_isPair hBY.1.1 hKY) hnefY
      (hstep i) (by simpa only [Category.assoc] using hKNc i)
    simpa only [Category.assoc] using h
  have hcompl := fun i => IsAdjunctionStep.exists_isLogCanonicalPair_add_pullback hKY
    ⟨inferInstance, inferInstance, hBY.1.1, hBY.1.2.1⟩ hQY hBY hgY hAY0 hAYq hlcY hHq hgYH hlinY
    (hstep i)
  choose hAN hAN0 hANq hANlc hANlin using hcompl
  have hAC : ∀ i (P : MMP.Mori.PrimeDivisor (N.X i)),
      (N.n i).base P.genericPoint ∈
        (doubleIntersectionLocus BY.roundDown.suppIdeal.subscheme : Set _) →
        (AY.pullback hAYq (hAN i)).coeff P = 0 := by
    intro i P hP
    have hle := coeff_le_one_of_isLogCanonicalPair (hANlc i) P
    have hΘ : (Θ i).coeff P = 1 := by
      rw [hsdlt.isAdjointBoundary i P, adjointBoundaryCoeff, if_pos hP, Finset.sum_eq_zero,
        add_zero]
      intro Γ hΓ
      rw [if_neg]
      intro h
      exact hsdlt.genericPoint_not_mem_doubleIntersectionLocus Γ hΓ (h ▸ hP)
    have h0 := (DivisorWithCoeffs.isEffective_iff_nonneg.mpr (hAN0 i)) P
    rw [DivisorWithCoeffs.coeff_add, hΘ] at hle
    linarith
  obtain ⟨GN, hGN, MZ, hMZ, hGM⟩ : ∃ (GN : ∀ i, QDivisor (N.X i))
      (_ : ∀ i, (Divisor.toQDivisor (KN i) + Θ i + AY.pullback hAYq (hAN i)).QLinearlyEquivalent
        (GN i))
      (MZ : Z.Modules) (_ : Stacks.Ample.IsInvertibleModule Z MZ),
      ∃ m : ℕ, 0 < m ∧ ∀ i, ∃ L : Divisor (N.X i), Divisor.toQDivisor L = (m : ℤ) • GN i ∧
        Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback (N.n i ≫ ι ≫ gY)).obj MZ) := by
    haveI : ∀ i, LocallyOfFiniteType ((N.n i ≫ ι) ≫ sY) := fun i => by
      rw [Category.assoc]
      exact (N.isNormalVariety i).1.toLocallyOfFiniteType
    obtain ⟨MZ, hMZ, m₀, hm₀, hL⟩ := exists_divisorialSheaf_iso_pullback (S := N.X)
      (j := fun i => N.n i ≫ ι) hBY.1.1.1 (n := 3) (by norm_num) (by rw [hdimY]; rfl) hKY
      (isQCartier_add_of_isPair hBY.1.1 hKY) hAYq hHq hgYH hlinY hstep
      (fun i => by simpa only [Category.assoc] using hKNc i) hAN
    refine ⟨fun i => Divisor.toQDivisor (KN i) + Θ i + AY.pullback hAYq (hAN i), fun i => by rfl,
      MZ, hMZ, m₀, hm₀, fun i => ?_⟩
    obtain ⟨L, h1, ⟨e⟩⟩ := hL i
    exact ⟨L, h1, ⟨e ≪≫ eqToIso (by rw [Category.assoc])⟩⟩
  obtain ⟨m, hm, hgen⟩ :=
    IsSdltAdjointPair.exists_isAdjointGeneratorOn_of_add_qLinearlyEquivalent_of_isLogCanonicalPair
      hsdlt hZ (ι ≫ gY) (by rw [Category.assoc, hgYZ]) hKNc hnef (fun i => hAN0 i)
      (fun i => hANq i) hAC (fun i => hANlc i) hGN MZ hGM
  exact exists_epi_counit_of_isAdjointGeneratorOn hBY.1.1.1 hKY hBY.1.1 ι N Θ
    (fun i => by exact_mod_cast (hKNc i).topologicalKrullDim_eq) hstep hBY.2.1 hdict
    gY hm hgen

private theorem solution : ∀
    {M Z : Scheme.{0}} [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sM : M ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hM : MMP.Mori.IsProjectiveVariety ℂ sM) (hdim : topologicalKrullDim M = 4)
    (hQ : IsQFactorial sM) {K : Divisor M} (hK : K.IsCanonicalDivisor sM 4) {B : QDivisor M}
    (hB : MMP.Intersection.IsDltPair sM B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {g : M ⟶ Z} (hgZ : g ≫ sZ = sM) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sM g (Divisor.toQDivisor K + B))
    {A : QDivisor M} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sM (B + A))
    {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgH : ∀ T : irreducibleComponents M, g (componentGenericPoint M T) ∉ H.supp)
    (hlin : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent (H.pullback hHq hgH)),
    QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B) := by
  intro M Z _ _ _ _ _ _ _ sM sZ hM hdim hQ K hK B hB hZ hZn g hgZ hg hgb hD A hA0 hAq hlc H hHq
    hgH hlin
  have hZv := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  have hMv := ((MMP.Mori.isProjectiveVariety_iff ℂ sM).mp hM).1
  haveI : MMP.Mori.IsVariety ℂ (g ≫ sZ) := hgZ ▸ hMv
  have hdimZ : topologicalKrullDim Z = 4 := hdim ▸
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (g ≫ sZ) hgb)
  obtain ⟨Y, _, _, _, _, sY, KY, BY, gY, φ, P, hY, hQY, hKY, hBY, hgYZ, hgY, hφ, hφg,
    ⟨W, _, _, _, sW, p, q, ψ, G, hR⟩, hP0, hPq, hPT, ⟨δ₀, hδ₀, hδ⟩, hnefY, hiff, h0⟩ :=
    IsDltPair.exists_isRelativelySemiample_sub_smul_of_supp_eq_roundDown hM hdim hQ hK hB hZ hZn
      hdimZ hgZ hg hgb hD
  by_cases hT0 : BY.roundDown = 0
  · exact h0 hT0
  rw [← hiff]
  haveI : IsSeparated sZ := hZv.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := by
    rw [show (Z ↘ ⊤_ Scheme) = sZ ≫ Limits.terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  haveI : LocallyOfFiniteType sM := hQ.1.1.toLocallyOfFiniteType
  have hpq : p ≫ g = q ≫ gY := comp_eq_comp_of_isLogComparisonResolution hR hφg
  haveI : IsDominant p := hR.isBirationalMorphism_left.isDominant
  haveI : IsDominant q := hR.isBirationalMorphism_right.isDominant
  haveI := hR.isVariety
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsDominant g := hgb.isDominant
  haveI : IsDominant gY := by
    haveI : IsDominant (q ≫ gY) := hpq ▸ inferInstance
    exact IsDominant.of_comp q gY
  rw [add_assoc] at hlin
  obtain ⟨m, hm, u, hu⟩ := (qLinearlyEquivalent_iff_smul_logCanonicalDivisor_eq _ _ _).mp hlin
  have hAp := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p A
  obtain ⟨⟨hAY0, hAYq⟩, ⟨HY, uY, hHY, -, hlinY⟩, -, -, hlcY, -⟩ :=
    hR.transport_lcComplement hZ hg hgY hgZ hgYZ hB.1 hBY.1 hpq hA0 hAq hlc hHq
      (isRCartierPullback_pullback hHq hgH) hm hu (isRCartierPullback_pullback hAq hAp)
      (transformDivisor_toRDivisor _ _)
  set AY := RationalMap.transformDivisor (Scheme.Hom.toRationalMap q) (A.pullback hAq hAp)
  have hgYH := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' gY H
  rw [MMP.Flips.IsRCartierPullback.eq gY hHY (isRCartierPullback_pullback hHq hgYH)] at hlinY
  have hlinY' : (Divisor.toQDivisor KY + BY + AY).QLinearlyEquivalent (H.pullback hHq hgYH) := by
    rw [add_assoc]
    exact (qLinearlyEquivalent_iff_smul_logCanonicalDivisor_eq _ _ _).mpr ⟨m, hm, uY, hlinY⟩
  have hdimY : topologicalKrullDim Y = 4 := by exact_mod_cast hKY.topologicalKrullDim_eq
  have hYv := ((MMP.Mori.isProjectiveVariety_iff ℂ sY).mp hY).1
  have hdltY : MMP.Mori.IsDltPair sY 4 KY BY :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sY hKY BY).mp hBY
  refine QDivisor.isRelativelySemiample_of_isDltPair_of_restrict_roundDown sY sZ hZ gY hgYZ hgY
    KY BY hQY hdltY P (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hP0) hPq
    (by rw [hPT, Divisor.supp_toQDivisor]) ?_
    (exists_epi_counit_floor hY hdimY hQY hKY hBY hZ hgYZ hgY hnefY hT0 hAY0 hAYq hlcY hHq hgYH
      hlinY')
  exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ₀) fun δ hδ' => hδ δ hδ'.1 hδ'.2

end Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Nef complemented dlt fourfolds over a birational base are good.** Let `M` be a projective
complex fourfold (`MMP.Mori.IsProjectiveVariety`) which is `ℚ`-factorial
(`MMP.Fourfold.IsQFactorial`), `K` a canonical divisor of `M` and `(M, B)` a dlt pair
(`MMP.Intersection.IsDltPair`). Let `g : M ⟶ Z` be a projective birational morphism over `ℂ` to a
normal projective variety `Z` such that `K + B` is nef over `g`. Suppose `A ≥ 0` is a
`ℚ`-Cartier `ℚ`-divisor with `(M, B + A)` log canonical and `K + B + A ∼_ℚ g^*H`
(`MMP.Mori.QDivisor.QLinearlyEquivalent`, `MMP.Mori.QDivisor.pullback`) for a `ℚ`-Cartier
`ℚ`-divisor `H` on `Z`. Then `K + B` is semiample over `g`
(`MMP.Fourfold.QDivisor.IsRelativelySemiample`). -/
@[mmp "thm_fourfold_nef_projective_birational_complemented_dlt_good"]
public theorem IsDltPair.isRelativelySemiample_of_add_qLinearlyEquivalent_pullback
    {M Z : Scheme.{0}} [IsIntegral M] [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
    [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]
    {sM : M ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hM : MMP.Mori.IsProjectiveVariety ℂ sM) (hdim : topologicalKrullDim M = 4)
    (hQ : IsQFactorial sM) {K : Divisor M} (hK : K.IsCanonicalDivisor sM 4) {B : QDivisor M}
    (hB : MMP.Intersection.IsDltPair sM B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (hZn : IsNormalVariety ℂ sZ)
    {g : M ⟶ Z} (hgZ : g ≫ sZ = sM) (hg : IsProjectiveMorphism g) (hgb : IsBirationalMorphism g)
    (hD : QDivisor.IsRelativelyNef sM g (Divisor.toQDivisor K + B))
    {A : QDivisor M} (hA0 : 0 ≤ A) (hAq : A.IsQCartier)
    (hlc : MMP.Intersection.IsLogCanonicalPair sM (B + A))
    {H : QDivisor Z} (hHq : H.IsQCartier)
    (hgH : ∀ T : irreducibleComponents M, g (componentGenericPoint M T) ∉ H.supp)
    (hlin : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent (H.pullback hHq hgH)) :
    QDivisor.IsRelativelySemiample g (Divisor.toQDivisor K + B) := by revert M Z sM sZ hM hdim hQ K hK B hB hZ hZn g hgZ hg hgb hD A hA0 hAq hlc H hHq hgH hlin; first | exact Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good.solution | exact Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good.solution _ | exact Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good.solution _ _ | exact Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good.solution _ _ _ | exact Proof_thm_fourfold_nef_projective_birational_complemented_dlt_good.solution _ _ _ _

end MMP.Fourfold

