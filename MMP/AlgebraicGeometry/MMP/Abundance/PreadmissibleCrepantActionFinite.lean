module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.MMP.Fourfold.LogMinimalModel
import MMP.AlgebraicGeometry.MMP.Abundance.PreadmissibleCrepantBoundaryFixed
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.MMP.Abundance.VerticalFloorRepresentation
import MMP.AlgebraicGeometry.MMP.Abundance.SubkltSurfacePluriformFinite
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport

/-!
# Finite crepant action on preadmissible sections of semiample dlt surfaces

Let `(X_i, B_i)`, `i ∈ I`, be a finite collection of projective rational dlt pairs on complex
surfaces whose adjoints `K_{X_i} + B_i` are semiample. In every sufficiently divisible even degree
`m`, the group of crepant birational self-maps of `(X_i, B_i)`
(`MMP.Fourfold.crepantBirationalAutomorphisms`) acts by pluriform pull-back on the `i`-th entries
of the preadmissible section systems (`MMP.Fourfold.preadmissibleSections`) through only finitely
many maps, and every such self-map leaves the residue restrictions of the `i`-th entry to all
proper strata of `X_i` (the components of `⌊B_i⌋` and their intersection points) unchanged.

The first assertion is the finite-image hypothesis of
`MMP.Fourfold.exists_admissibleSections_generatesOn_of_finite`; for a single pair take `I` a
one-point type.

## Main results

* `MMP.Fourfold.exists_finite_range_pluriformPullback_preadmissibleSections`

## Implementation notes

Semiampleness of the adjoint is `MMP.Fourfold.QDivisor.IsRelativelySemiample` over `Spec ℂ` of
`K_{X_i} + B_i`, for a canonical divisor `K_{X_i}`. Projectivity, the rational pair condition,
dlt, dimension two and evenness of `m` are the fields of the setting
`MMP.Fourfold.IsStratifiedSectionSetting` carried by the residue restriction structure. The
proof passes to a log resolution preserving the lc strata, writes `m(K + B) = f^* H` for the
semiample contraction `f : X → Y` and an ample `H`; if some floor curve dominates `Y`, restriction
to the floor is injective on `H⁰(X, m(K + B))` and the action is trivial, and otherwise the whole
floor is vertical and the action on all of `H⁰(X, m(K + B))` is finite.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.PreadmissibleCrepantActionFinite

section Residue

open MMP.CyclicChartDifferent.Aux MMP.CyclicChartDifferent

/-- Rational `m`-canonical forms on an integral scheme of transcendence degree `n` form a line. -/
private theorem finrank_rationalPluriForms {T : Scheme.{0}} [IsIntegral T]
    (sT : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sT] {n : ℕ}
    (hd : letI := functionFieldAlgebra sT; (Algebra.trdeg ℂ T.functionField).toNat = n)
    (m : ℤ) :
    letI := functionFieldAlgebra sT
    Module.finrank T.functionField (RationalPluriForms sT n m) = 1 := by
  letI := functionFieldAlgebra sT
  have := essFiniteType_functionField (sX := sT)
  have hK : Module.finrank T.functionField Ω[T.functionField⁄ℂ] = n :=
    (finrank_kaehlerDifferential_eq_trdeg ℂ T.functionField).trans hd
  have : FiniteDimensional T.functionField Ω[T.functionField⁄ℂ] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent ℂ T.functionField).1
  have h1 : Module.finrank T.functionField (⋀[T.functionField]^n Ω[T.functionField⁄ℂ]) = 1 := by
    rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
  let c₀ := (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique (Fin 1) Unit)
  let bb : Module.Basis Unit T.functionField (RationalPluriForms sT n m) :=
    ZTensorPower.basis c₀ m
  rw [Module.finrank_eq_card_basis bb, Fintype.card_unit]

/-- A nonzero rational top form of order zero along a given prime divisor. -/
private theorem exists_ne_zero_ordForm_eq_zero {T : Scheme.{0}} [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] (sT : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sT] {n : ℕ}
    (hd : letI := functionFieldAlgebra sT; (Algebra.trdeg ℂ T.functionField).toNat = n)
    (Q : MMP.Mori.PrimeDivisor T) :
    ∃ ρ : RationalPluriForms sT n 1, ρ ≠ 0 ∧ Q.ordForm ρ = 0 := by
  letI := functionFieldAlgebra sT
  have h1 : Module.finrank T.functionField (RationalPluriForms sT n 1) = 1 :=
    finrank_rationalPluriForms sT hd 1
  have : Nontrivial (RationalPluriForms sT n 1) :=
    Module.nontrivial_of_finrank_pos (R := T.functionField) (by omega)
  obtain ⟨ρ₀, hρ₀⟩ := exists_ne (0 : RationalPluriForms sT n 1)
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq Q (-Q.ordForm ρ₀)
  refine ⟨g • ρ₀, smul_ne_zero hg0 hρ₀, ?_⟩
  rw [Q.ordForm_smul (sX := sT) hd hg0 hρ₀, hg]
  ring

/-- **A pole of full order along a normal prime divisor has a nonzero residue.** If a rational
`(M + 1)`-canonical form `τ ≠ 0` has order `-(M + 1)` along `P`, its Poincaré residue along `P`
is nonzero: some power `σ^{⊗(M+1)}` of a top form with nonzero residue is `f τ` with `f` regular
along `P`. -/
private theorem isPoincareResidue_ne_zero_of_ordForm_eq
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1)
    (j : T ⟶ X) [IsClosedImmersion j] [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T]
    [CompactSpace T] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    (Q : MMP.Mori.PrimeDivisor T) {M : ℕ}
    (τ : RationalPluriForms sX (n + 1) ((M + 1 : ℕ) : ℤ)) (hτ0 : τ ≠ 0)
    (hτ : P.ordForm τ = -((M + 1 : ℕ) : ℤ))
    (ρ : RationalPluriForms (j ≫ sX) n ((M + 1 : ℕ) : ℤ))
    (hρ : IsPoincareResidue sX j n (M + 1) τ ρ) : ρ ≠ 0 := by
  classical
  have : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hjT := map_genericPoint_eq j P hP
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (j ≫ sX)
  have hd : (Algebra.trdeg ℂ X.functionField).toNat = n + 1 :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) (by rw [hdim]; norm_cast)
  have hdT : (Algebra.trdeg ℂ T.functionField).toNat = n := by
    have := MMP.Fourfold.trdeg_add_one_of_eq_genericPoint (sY := sX) (j := j) P hjT
    omega
  have hdimT : topologicalKrullDim T = n := by
    rw [topologicalKrullDim_eq_toNat_trdeg (j ≫ sX), hdT]
  have hrank : Module.finrank X.functionField
      (RationalPluriForms sX (n + 1) ((M + 1 : ℕ) : ℤ)) = 1 :=
    finrank_rationalPluriForms sX hd _
  obtain ⟨ρ₁, hρ₁0, hρ₁Q⟩ := exists_ne_zero_ordForm_eq_zero (j ≫ sX) hdT Q
  obtain ⟨σ, hσP, -, hσres⟩ :=
    exists_isPoincareResidue_of_le_ordForm sX hX hdim j hT P hP Q ρ₁ hρ₁Q.ge
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    have h0 : IsPoincareResidue sX j n 1 (0 : RationalPluriForms sX (n + 1) 1) 0 := by
      obtain ⟨t, g', x, ht, -, -⟩ := hσres
      refine ⟨t, 0, x, ht, ?_, ?_⟩ <;> simp <;> rfl
    exact hρ₁0 (MMP.Fourfold.isPoincareResidue_unique (sY := sX) hjT hσres h0)
  set σM := pluriPow σ M with hσM
  obtain ⟨f, hf⟩ := (finrank_eq_one_iff_of_nonzero' τ hτ0).mp hrank σM
  have hspP : j (genericPoint T) ⤳ P.genericPoint := specializes_of_eq hjT
  obtain ⟨a, haf⟩ : ∃ a : X.presheaf.stalk P.genericPoint,
      algebraMap _ X.functionField a = f := by
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [map_zero, hf0]⟩
    refine exists_algebraMap_eq_of_ord_nonneg P hf0 ?_
    have h1 := P.ordForm_smul (sX := sX) hd hf0 hτ0
    rw [hf, hτ, hσM, ordForm_pluriPow (by rw [hdim]; norm_cast) hσ0 P M] at h1
    have h2 : ((M + 1 : ℕ) : ℤ) * (-1) ≤ ((M + 1 : ℕ) : ℤ) * P.ordForm σ :=
      mul_le_mul_of_nonneg_left hσP (by positivity)
    omega
  set b₁ := X.presheaf.stalkSpecializes hspP a with hb₁
  have hb₁f : algebraMap _ X.functionField b₁ = f := by
    rw [hb₁, algebraMap_stalkSpecializes', haf]
  have hres := IsPoincareResidue.algebraMap_smul hρ b₁
  rw [hb₁f, hf] at hres
  have hσMres := isPoincareResidue_pluriPow P hjT hdim hσres M
  have hρσeq := MMP.Fourfold.isPoincareResidue_unique (sY := sX) hjT hσMres hres
  have hne : pluriPow ρ₁ M ≠ 0 := pluriPow_ne_zero hdimT hρ₁0 M
  rw [hρσeq] at hne
  exact (smul_ne_zero_iff.mp hne).2

/-- Orders of rational forms are unchanged along an equality of structure morphisms. -/
private theorem ordForm_eq_of_heq {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {s s' : Y ⟶ Spec (.of ℂ)} (h : s = s') {d : ℕ} {m : ℤ} {x : RationalPluriForms s d m}
    {y : RationalPluriForms s' d m} (hxy : HEq x y) (P : MMP.Mori.PrimeDivisor Y) :
    P.ordForm x = P.ordForm y ∧ (x = 0 → y = 0) := by
  subst h
  obtain rfl := eq_of_heq hxy
  exact ⟨rfl, id⟩

private theorem eq_zero_of_heq_zero {Y : Scheme.{0}} [IsIntegral Y] {s s' : Y ⟶ Spec (.of ℂ)}
    (h : s = s') {d : ℕ} {m : ℤ} {x : RationalPluriForms s' d m}
    (hx : HEq (0 : RationalPluriForms s d m) x) : x = 0 := by
  subst h
  exact (eq_of_heq hx).symm

/-- A nonzero section of `H⁰(X, m(K + B))` has order at least `-⌊m b_Γ⌋` along every prime `Γ`. -/
private theorem neg_floor_le_ordForm {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {m : ℕ}
    {s : RationalPluriForms sX 2 m} (hs : s ∈ logPluricanonicalSections sX 2 m B) (hs0 : s ≠ 0)
    (Γ : MMP.Mori.PrimeDivisor X) : -⌊((m : ℤ) • B.coeff Γ : ℚ)⌋ ≤ Γ.ordForm s := by
  have := ((mem_pluricanonicalSections_of_ne_bot top_ne_bot).1
    ((mem_logPluricanonicalSections sX).1 hs)) Γ
    ⟨Γ.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support Γ, trivial⟩ hs0
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at this
  linarith

/-- A prime of coefficient one of a dlt pair is a dlt stratum. -/
private theorem isDltStratum_support_of_coeff_eq_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B) (C : MMP.Mori.PrimeDivisor X)
    (hC : B.coeff C = 1) : IsDltStratum sX B (C.support : Set X) := by
  refine ⟨hdlt, {C}, Finset.singleton_nonempty C, fun P hP => ?_, ?_, ?_⟩
  · rw [Finset.mem_singleton.mp hP, hC]
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    exact ⟨C.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support C⟩
  · simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    refine ⟨⟨?_, subset_rfl⟩, fun T hT _ => hT.2⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure C]
    exact isIrreducible_singleton.closure

/-- A closed subscheme of a surface with image a prime divisor is a curve. -/
private theorem topologicalKrullDim_eq_one_of_range_eq {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (hdim : topologicalKrullDim X = (2 : ℕ)) (ι : T ⟶ X) [IsClosedImmersion ι]
    (C : MMP.Mori.PrimeDivisor X) (hrange : Set.range ι.base = (C.support : Set X)) :
    topologicalKrullDim T = (1 : ℕ) := by
  have h1 : topologicalKrullDim T = topologicalKrullDim (Set.range ι.base) :=
    IsHomeomorph.topologicalKrullDim_eq _
      (ι.isClosedEmbedding.isEmbedding.toHomeomorph).isHomeomorph
  have h2 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX C.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at h2
  rw [h1, hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure C]
  generalize topologicalKrullDim (closure {C.genericPoint} : Set X) = a at h2 ⊢
  induction a using WithBot.recBotCoe with
  | bot => simp at h2
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_add, top_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h2
      simp at h2
    | coe a =>
      rw [← WithBot.coe_add, ← WithBot.coe_natCast, WithBot.coe_inj] at h2
      have h4 : a + 1 = 2 := by exact_mod_cast h2
      obtain rfl : a = 1 := by omega
      rfl

end Residue

section Collection

variable {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of ℂ)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  {B : ∀ i, QDivisor (X i)} {m : ℕ}

/-- If the residue restriction along some proper stratum is injective on `H⁰(X_i, m(K + B))`,
crepant self-maps act trivially on the preadmissible entries. -/
private theorem finite_range_of_injective_toFun (R : ResidueRestriction sX B 2 m) (i : I)
    {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) {e : ℕ} (hF : 0 < F.length)
    (hS : topologicalKrullDim S = e) (hinj : Function.Injective (R.toFun i F e)) :
    (Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
        (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom 2 m
          ((s : logPluricanonicalSections (sX i) 2 m (B i)) :
            RationalPluriForms (sX i) 2 m)).Finite := by
  refine (Set.finite_singleton (fun (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
    ((s : logPluricanonicalSections (sX i) 2 m (B i)) :
      RationalPluriForms (sX i) 2 m))).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine funext fun s => ?_
  obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp s.2
  obtain ⟨⟨t', -, ht', -⟩, hb⟩ :=
    ResidueRestriction.exists_preadmissible_pluriformPullback_and_toFun_eq R
      (fun l P => (R.setting.isPair l).nonneg P) (σ : FunctionFieldEquiv (sX i) (sX i)) σ.2 ht
  have h1 := hinj (hb (t' i) ht' F e hF hS)
  have hs : (s : logPluricanonicalSections (sX i) 2 m (B i)) = t i := by rw [← hts]; rfl
  simp only
  rw [hs, ← ht', h1]

/-- Every coefficient-one prime of a component carries a nonzero section of `m(K + B)`
vanishing along it, when no residue restriction to a floor curve is injective. -/
private theorem exists_ordForm_ge_of_not_injective (R : ResidueRestriction sX B 2 m) (i : I)
    (h : ∀ (S : Scheme.{0}) (ι : S ⟶ X i) (BS : QDivisor S)
      (F : StratumAdjunctionData (sX i) (B i) ι BS), 0 < F.length →
        topologicalKrullDim S = (1 : ℕ) → ¬ Function.Injective (R.toFun i F 1))
    (C : MMP.Mori.PrimeDivisor (X i)) (hC : (B i).coeff C = 1) :
    ∃ s ∈ logPluricanonicalSections (sX i) 2 m (B i), s ≠ 0 ∧ 1 - (m : ℤ) ≤ C.ordForm s := by
  classical
  have hX : IsNormalVariety ℂ (sX i) := (R.setting.isPair i).isPair.1
  have hdimX := R.setting.topologicalKrullDim_eq i
  have : LocallyOfFiniteType (sX i) := hX.1.toLocallyOfFiniteType
  obtain ⟨T, ι, BT, hrange, ⟨F⟩⟩ := (isDltStratum_support_of_coeff_eq_one (R.setting.isDltPair i)
    C hC).exists_isStratumAdjunctionPair_and_isDltPair.1.1
  have hci := F.isClosedImmersion
  have hdimT := topologicalKrullDim_eq_one_of_range_eq (sX i) hdimX ι C hrange
  have hlen := F.dim_add_length hdimX hdimT
  rcases F with hpair | ⟨F', j, BT', hj⟩
  · simp [StratumAdjunctionData.length] at hlen
  rcases F' with hpair | ⟨F'', j', BT'', hj'⟩
  swap
  · simp only [StratumAdjunctionData.length] at hlen
    omega
  set F₁ : StratumAdjunctionData (sX i) (B i) (j ≫ 𝟙 (X i)) BT :=
    StratumAdjunctionData.step (StratumAdjunctionData.refl hpair) j BT hj with hF₁
  haveI := F₁.isIntegral_stratum
  haveI := F₁.isNormal_stratum
  haveI := F₁.isLocallyNoetherian_stratum
  have hnot := h T (j ≫ 𝟙 (X i)) BT F₁ (by simp [hF₁, StratumAdjunctionData.length]) hdimT
  rw [← LinearMap.ker_eq_bot] at hnot
  obtain ⟨s, hs, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hnot
  rw [LinearMap.mem_ker] at hs
  refine ⟨s, s.2, fun h0 => hs0 (Subtype.ext h0), ?_⟩
  have hres := R.isIteratedResidue i F₁ 1 s hdimT
  rw [hs] at hres
  obtain ⟨ρ₀, ⟨-, hρ₀⟩, ρ', hρres, hρ'⟩ := hres.rec'
  by_contra hlt
  push Not at hlt
  have hmem := neg_floor_le_ordForm s.2 (fun h0 => hs0 (Subtype.ext h0)) C
  rw [hC, zsmul_eq_mul, mul_one, Int.floor_intCast] at hmem
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by have := R.setting.pos; omega⟩
  have hord : C.ordForm (s : RationalPluriForms (sX i) 2 ((M + 1 : ℕ) : ℤ)) =
      -((M + 1 : ℕ) : ℤ) := by push_cast at hmem hlt ⊢; omega
  have hX' : IsNormalVariety ℂ (𝟙 (X i) ≫ sX i) := by rwa [Category.id_comp]
  haveI : LocallyOfFiniteType (𝟙 (X i) ≫ sX i) := hX'.1.toLocallyOfFiniteType
  haveI : CompactSpace (X i) := hX.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI hjci : IsClosedImmersion j := by obtain ⟨-, P, -, -, hc, -⟩ := hj; exact hc
  haveI : CompactSpace T := hj.1.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : LocallyOfFiniteType (j ≫ 𝟙 (X i) ≫ sX i) := hj.1.1.toLocallyOfFiniteType
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimT one_ne_zero
  have hrange' : Set.range j.base = (C.support : Set (X i)) := by simpa using hrange
  obtain ⟨hord₀, hzero₀⟩ := ordForm_eq_of_heq (Category.id_comp (sX i)) hρ₀ C
  have hρ₀0 : ρ₀ ≠ 0 := fun h0 => hs0 (Subtype.ext (hzero₀ h0))
  exact isPoincareResidue_ne_zero_of_ordForm_eq (𝟙 (X i) ≫ sX i) hX' (n := 1)
    (by rw [hdimX]; norm_num) j hj.1 C hrange' Q ρ₀ hρ₀0 (hord₀.trans hord) ρ' hρres
    (eq_zero_of_heq_zero (by rw [Category.assoc]) hρ')

end Collection

section Transport

open MMP.Mori.IsPair

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {n : ℕ} {K : Divisor X}
  {f : Y ⟶ X} [IsProper f] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsDominant f]
  [CompactSpace Y]

/-- **Log discrepancies are read through a crepant pull-back.** For a proper birational morphism
`f : Y ⟶ X` of normal varieties, a canonical divisor `K_Y` and the crepant boundary `B_Y` of
`(X, B)`, a valuation `v` of `k(Y)` has log discrepancy `a` with respect to `(Y, B_Y)` exactly
when `v ∘ f^*` has log discrepancy `a` with respect to `(X, B)`. -/
private theorem hasLogDiscrepancy_iff_comap_functionFieldMap (hP : MMP.Mori.IsPair sX B)
    (hK : K.IsCanonicalDivisor sX n) (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {BY : QDivisor Y} (hBY : IsCrepantBoundary sX n K B f hY hf BY)
    (v : Valuation Y.functionField (WithZero (Multiplicative ℤ))) (a : ℝ) :
    HasLogDiscrepancy (f ≫ sX) BY v a ↔
      HasLogDiscrepancy sX B (v.comap (functionFieldMap f)) a := by
  have hcr := isDiscrepancy_iff_of_crepant hP f hY hf hK hKY (Or.inl hBY)
  have hnY : topologicalKrullDim Y = n := hKY.topologicalKrullDim_eq
  have hnX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  constructor
  · rintro ⟨n', E, rfl, hE⟩
    obtain rfl : n' = n := by
      exact_mod_cast
        (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hE).symm.trans hnY
    haveI : IsProper E.f := hE.2.1
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hcr.1 hKY E
    have hv := MMP.Mori.valuation_compDivisorOver f hY hf E
    have hc' := (hcr.2 E _ hv c).1 hc
    have ha := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc hE
    refine ⟨n', MMP.Mori.compDivisorOver f hY hf E, hv, ?_⟩
    rw [ha]
    exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc'
      (show IsProper (E.f ≫ f) from inferInstance)
  · rintro ⟨n', D, hDv, hD⟩
    obtain rfl : n' = n := by
      exact_mod_cast
        (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hD).symm.trans hnX
    obtain ⟨E₀, hE₀⟩ := MMP.Mori.exists_divisorOver_comap_eq hY hf D
    haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
    obtain ⟨E, hE⟩ := MMP.Threefold.Bridges.exists_properDivisorOver_valuation_eq hY E₀
    have hEv : E.toDivisorOver.valuation = E₀.valuation := hE
    have hvE : E.toDivisorOver.valuation = v := by
      rw [hEv]
      ext y
      obtain ⟨x, rfl⟩ := hf.functionFieldMap_bijective.2 y
      exact (congrArg (fun w : Valuation X.functionField (WithZero (Multiplicative ℤ)) => w x)
        (hE₀.symm.trans hDv) :)
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
    have hc' := (hcr.2 E.toDivisorOver D (by rw [hEv]; exact hE₀) c).2 hc
    have ha := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc hD
    refine ⟨n', E.toDivisorOver, hvE, ?_⟩
    rw [ha]
    exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc' E.isProper

/-- **Crepant self-maps lift to a crepant pull-back.** In the setting of
`hasLogDiscrepancy_iff_comap_functionFieldMap`, conjugation by the isomorphism of function fields
`f^* : k(X) ≅ k(Y)` carries the crepant birational self-maps of `(X, B)` to crepant birational
self-maps of `(Y, B_Y)`. -/
private theorem autCongr_mem_crepantBirationalAutomorphisms (hP : MMP.Mori.IsPair sX B)
    (hK : K.IsCanonicalDivisor sX n) (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {BY : QDivisor Y} (hBY : IsCrepantBoundary sX n K B f hY hf BY)
    (F : letI := functionFieldAlgebra sX; letI := functionFieldAlgebra (f ≫ sX)
      X.functionField ≃ₐ[ℂ] Y.functionField)
    (hF : ∀ x, F x = functionFieldMap f x) {σ : FunctionFieldEquiv sX sX}
    (hσ : σ ∈ crepantBirationalAutomorphisms sX B) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    AlgEquiv.autCongr F σ ∈ crepantBirationalAutomorphisms (f ≫ sX) BY := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  intro v a
  have h1 := hasLogDiscrepancy_iff_comap_functionFieldMap hP hK hY hf hKY hBY v a
  have h2 := hasLogDiscrepancy_iff_comap_functionFieldMap hP hK hY hf hKY hBY
    (v.comap (AlgEquiv.autCongr F σ).toRingEquiv.toRingHom) a
  have h3 := (hσ : IsCrepantBirationalMap sX sX B B σ) (v.comap (functionFieldMap f)) a
  have e : (v.comap (AlgEquiv.autCongr F σ).toRingEquiv.toRingHom).comap (functionFieldMap f) =
      (v.comap (functionFieldMap f)).comap σ.toRingEquiv.toRingHom := by
    ext x
    change v (F (σ (F.symm (functionFieldMap f x)))) = v (functionFieldMap f (σ x))
    rw [← hF x, F.symm_apply_apply, hF]
  rw [h1, h3, ← e, ← h2]

/-- **Finiteness descends along a crepant pull-back.** In the setting of
`autCongr_mem_crepantBirationalAutomorphisms`, if crepant self-maps of `(Y, B_Y)` act with finite
image on `H⁰(Y, m(K_Y + B_Y))` and `f^*` maps `H⁰(X, m(K + B))` into it, crepant self-maps of
`(X, B)` act with finite image on `H⁰(X, m(K + B))`. -/
private theorem finite_range_of_finite_range_crepantBoundary (hP : MMP.Mori.IsPair sX B)
    (hK : K.IsCanonicalDivisor sX n) (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {BY : QDivisor Y} (hBY : IsCrepantBoundary sX n K B f hY hf BY) {m : ℕ}
    (hpb : ∀ s ∈ logPluricanonicalSections sX n m B, s ≠ 0 →
      pullbackRationalPluriForms sX f s ∈ logPluricanonicalSections (f ≫ sX) n m BY)
    (hfinY : (Set.range fun (σ : crepantBirationalAutomorphisms (f ≫ sX) BY)
      (s : logPluricanonicalSections (f ≫ sX) n m BY) =>
        pluriformPullback (f ≫ sX) (f ≫ sX) (σ : FunctionFieldEquiv (f ≫ sX) (f ≫ sX)).toHom n m
          (s : RationalPluriForms (f ≫ sX) n m)).Finite) :
    (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
        (s : logPluricanonicalSections sX n m B) =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom n m
        (s : RationalPluriForms sX n m)).Finite := by
  have hnY : topologicalKrullDim Y = n := hKY.topologicalKrullDim_eq
  have hnX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have : LocallyOfFiniteType sX := hP.1.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  let φf : FunctionFieldHom (f ≫ sX) sX :=
    { toRingHom := functionFieldMap f
      commutes' := fun c => by
        letI := functionFieldMapAlgebra f
        have := isScalarTower_functionFieldMap sX f
        exact (IsScalarTower.algebraMap_apply ℂ X.functionField Y.functionField c).symm }
  have hφf : ∀ s : RationalPluriForms sX n m,
      pluriformPullback (f ≫ sX) sX φf n m s = pullbackRationalPluriForms sX f s := fun _ => rfl
  let F : X.functionField ≃ₐ[ℂ] Y.functionField :=
    AlgEquiv.ofBijective φf hf.functionFieldMap_bijective
  let L := pluriformPullback sX (f ≫ sX) (FunctionFieldEquiv.toHom sX (f ≫ sX) F.symm) n m
  have hLf : ∀ s : RationalPluriForms sX n m, L (pullbackRationalPluriForms sX f s) = s :=
    fun s => by
      rw [← hφf, pluriformPullback_comp hnX hnY hnX]
      have : (FunctionFieldEquiv.toHom sX (f ≫ sX) F.symm).comp φf =
          (1 : FunctionFieldEquiv sX sX).toHom := AlgHom.ext F.symm_apply_apply
      rw [this, pluriformPullback_one hnX]
  have hc : ∀ (σ : FunctionFieldEquiv sX sX) (s : RationalPluriForms sX n m),
      pluriformPullback (f ≫ sX) (f ≫ sX)
          (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX) (AlgEquiv.autCongr F σ)) n m
          (pullbackRationalPluriForms sX f s) =
        pullbackRationalPluriForms sX f (pluriformPullback sX sX σ.toHom n m s) := by
    intro σ s
    rw [← hφf, ← hφf, pluriformPullback_comp hnY hnY hnX, pluriformPullback_comp hnY hnX hnX]
    have : (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX) (AlgEquiv.autCongr F σ)).comp φf =
        φf.comp (FunctionFieldEquiv.toHom sX sX σ) := AlgHom.ext fun x => by
      change F (σ (F.symm (F x))) = F (σ x)
      rw [F.symm_apply_apply]
    rw [this]
  have ha : ∀ s ∈ logPluricanonicalSections sX n m B,
      pullbackRationalPluriForms sX f s ∈ logPluricanonicalSections (f ≫ sX) n m BY := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0, ← hφf, map_zero]
      exact zero_mem _
    exact hpb s hs hs0
  refine (hfinY.image fun h (s : logPluricanonicalSections sX n m B) =>
    L (h ⟨pullbackRationalPluriForms sX f s, ha _ s.2⟩)).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨_, ⟨⟨AlgEquiv.autCongr F σ, autCongr_mem_crepantBirationalAutomorphisms hP hK hY hf
    hKY hBY F (fun _ => rfl) σ.2⟩, rfl⟩, funext fun s => ?_⟩
  change L (pluriformPullback (f ≫ sX) (f ≫ sX)
    (FunctionFieldEquiv.toHom (f ≫ sX) (f ≫ sX) (AlgEquiv.autCongr F σ)) n m
    (pullbackRationalPluriForms sX f s)) = _
  rw [hc, hLf]

end Transport

section Dlt

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {n : ℕ} {K : Divisor X}
  {f : Y ⟶ X} [IsProper f]

/-- On an open `U` over which the inverse transform of `B` is snc, `U ∩ Supp B` is an snc closed
subset. -/
private theorem isSNCClosedSubset_preimage_of_isSNC [LocallyOfFiniteType sX] (U : X.Opens)
    (h : DivisorWithCoeffs.IsSNC (Scheme.Opens.ι U ≫ sX)
      (MMP.Mori.inverseTransformDivisor (Scheme.Opens.ι U) B)) :
    MMP.Resolution.IsSNCClosedSubset (Scheme.Opens.ι U ≫ sX)
      (Scheme.Opens.ι U ⁻¹' (B.support.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  rw [MMP.Mori.inverseTransformDivisor_ι_eq_restrictOpen] at h
  have h' : (MMP.Intersection.reducedDivisorOf (B.restrictOpen U).support).IsSNC
      (Scheme.Opens.ι U ≫ sX) :=
    h.of_support_subset (by rw [MMP.Intersection.support_reducedDivisorOf])
  have hS := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ h'
  rw [MMP.Intersection.support_reducedDivisorOf] at hS
  convert hS using 1
  ext x
  simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨E, hE, hxE⟩
    obtain ⟨F, rfl⟩ :=
      MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      (Scheme.Opens.ι U) E x hxE
    refine ⟨F, ?_, (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff
      (Scheme.Opens.ι U) F x).mp hxE⟩
    rwa [Finsupp.mem_support_iff] at hE ⊢
  · rintro ⟨F, hF, hxF⟩
    refine ⟨OpenWeilRestriction.primeDivisorMap (Scheme.Opens.ι U) F, ?_,
      (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff
        (Scheme.Opens.ι U) F x).mpr hxF⟩
    rwa [Finsupp.mem_support_iff] at hF ⊢

/-- **Coefficient-one primes of the crepant boundary are not exceptional** on a log resolution
of a dlt pair which is an isomorphism over every smooth open on which `Supp B` is snc: an
exceptional prime of coefficient one would have log discrepancy `0`, so its centre meets the snc
locus, over which `f` is an isomorphism. -/
private theorem not_isExceptional_of_coeff_eq_one (hdlt : MMP.Intersection.IsDltPair sX B)
    (hK : K.IsCanonicalDivisor sX n) (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f)
    (hiso : ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
      MMP.Resolution.IsSNCClosedSubset (U.ι ≫ sX)
        (U.ι ⁻¹' (B.support.sup fun E => E.idealSheaf.support)) →
        IsIso (f ∣_ U))
    {BY : QDivisor Y} (hBY : IsCrepantBoundary sX n K B f hY hf BY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : BY.coeff G = 1) : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver ℂ sX).IsExceptional := by
  classical
  obtain ⟨⟨hpair, -, -⟩, -, Z, hZsm, hZsnc, hZpos⟩ := hdlt
  have hX : IsNormalVariety ℂ sX := hpair.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  set D : DivisorOver ℂ sX := ⟨Y, f, hY, hf, G⟩
  intro hEx
  have hdisc := hBY G
  rw [hG] at hdisc
  have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hdisc
    (show IsProper D.f from inferInstance)
  by_cases hx : f G.genericPoint ∈ (Z : Set X)
  · have hc : (D.center : Set X) ⊆ Z := by
      rw [D.center_eq_closure_genericPoint]
      exact closure_minimal (Set.singleton_subset_iff.mpr hx) Z.isClosed
    have := hZpos n D hc _ hlog
    norm_num at this
  · have hbir : f G.genericPoint ∈ MMP.Mori.biregularLocus f :=
      MMP.Mori.le_biregularLocus (hiso _ hZsm (isSNCClosedSubset_preimage_of_isSNC _ hZsnc)) hx
    have h2 := (MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hEx
    change 2 ≤ Order.coheight (f G.genericPoint) at h2
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hbir,
      MMP.Mori.PrimeDivisor.coheight_genericPoint] at h2
    exact absurd h2 (by norm_num)

end Dlt

section Vertical

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}

/-- A product of `N` sections of `H⁰(X, m(K + B))` is a section of `H⁰(X, Nm(K + B))`. -/
private theorem prodForm_mem_logPluricanonicalSections [LocallyOfFiniteType sX]
    (hn : topologicalKrullDim X = 2)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^2 Ω[X.functionField⁄ℂ]))
    {ι : Type*} (S : Finset ι) {m : ℕ} {g : ι → RationalPluriForms sX 2 m}
    (hg : ∀ i, g i ∈ logPluricanonicalSections sX 2 m B ∧ g i ≠ 0) :
    prodForm b S g (S.card * m) ∈ logPluricanonicalSections sX 2 (S.card * m) B := by
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot]
  intro Γ _ _
  rw [ordForm_prodForm b hn Γ (fun i _ => (hg i).2) rfl, DivisorWithCoeffs.coeff_roundDown,
    DivisorWithCoeffs.coeff_smul]
  have h1 : ∑ i ∈ S, -⌊((m : ℤ) • B.coeff Γ : ℚ)⌋ ≤ ∑ i ∈ S, Γ.ordForm (g i) :=
    Finset.sum_le_sum fun i _ => neg_floor_le_ordForm (hg i).1 (hg i).2 Γ
  rw [Finset.sum_const, smul_neg, nsmul_eq_mul] at h1
  have h2 : (S.card : ℤ) * ⌊((m : ℤ) • B.coeff Γ : ℚ)⌋ ≤
      ⌊(((S.card * m : ℕ) : ℤ) • B.coeff Γ : ℚ)⌋ := by
    rw [Int.le_floor]
    have h3 := Int.floor_le ((m : ℤ) • B.coeff Γ : ℚ)
    simp only [zsmul_eq_mul, Int.cast_natCast] at h3 ⊢
    push_cast
    have hN0 : (0 : ℚ) ≤ S.card := by positivity
    nlinarith
  linarith

/-- If one factor of a product of `N` sections of `H⁰(X, m(K + B))` has order at least `1 - m`
along a prime `C` of coefficient one, the product has order at least `1 - Nm` along `C`. -/
private theorem one_sub_le_ordForm_prodForm [LocallyOfFiniteType sX]
    (hn : topologicalKrullDim X = 2)
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^2 Ω[X.functionField⁄ℂ]))
    {ι : Type*} (S : Finset ι) {m : ℕ} {g : ι → RationalPluriForms sX 2 m}
    (hg : ∀ i, g i ∈ logPluricanonicalSections sX 2 m B ∧ g i ≠ 0)
    {C : MMP.Mori.PrimeDivisor X} (hC : B.coeff C = 1) {i₀ : ι} (hi₀ : i₀ ∈ S)
    (hgC : 1 - (m : ℤ) ≤ C.ordForm (g i₀)) :
    1 - ((S.card * m : ℕ) : ℤ) ≤ C.ordForm (prodForm b S g (S.card * m)) := by
  classical
  rw [ordForm_prodForm b hn C (fun i _ => (hg i).2) rfl, ← Finset.add_sum_erase _ _ hi₀]
  have h2 : ∑ i ∈ S.erase i₀, -(m : ℤ) ≤ ∑ i ∈ S.erase i₀, C.ordForm (g i) :=
    Finset.sum_le_sum fun i _ => by
      have := neg_floor_le_ordForm (hg i).1 (hg i).2 C
      rwa [hC, zsmul_eq_mul, mul_one, Int.floor_intCast] at this
  rw [Finset.sum_const, smul_neg, nsmul_eq_mul] at h2
  have hc : (S.erase i₀).card + 1 = S.card := Finset.card_erase_add_one hi₀
  have : ((S.card * m : ℕ) : ℤ) = ((S.erase i₀).card : ℤ) * m + m := by
    rw [← hc]
    push_cast
    ring
  linarith

/-- A nonzero section of `H⁰(X, M(K + B))`, for some `m ∣ M`, of order at least `1 - M` along
every prime of coefficient one: the product of `s₁` and of the sections given by `hfloor`. -/
private theorem exists_mem_logPluricanonicalSections_ordForm_ge [LocallyOfFiniteType sX]
    (hn : topologicalKrullDim X = 2) {m : ℕ} (hm : 0 < m)
    (hfloor : ∀ C : MMP.Mori.PrimeDivisor X, B.coeff C = 1 →
      ∃ s ∈ logPluricanonicalSections sX 2 m B, s ≠ 0 ∧ 1 - (m : ℤ) ≤ C.ordForm s)
    {s₁ : RationalPluriForms sX 2 m} (hs₁ : s₁ ∈ logPluricanonicalSections sX 2 m B)
    (hs₁0 : s₁ ≠ 0) :
    ∃ M : ℕ, 0 < M ∧ m ∣ M ∧ ∃ s₀ ∈ logPluricanonicalSections sX 2 M B, s₀ ≠ 0 ∧
      ∀ C : MMP.Mori.PrimeDivisor X, B.coeff C = 1 → 1 - (M : ℤ) ≤ C.ordForm s₀ := by
  classical
  obtain ⟨b⟩ := exists_basis_topForms (sX := sX) hn
  let g : Option (MMP.Mori.PrimeDivisor X) → RationalPluriForms sX 2 m := fun i =>
    i.elim s₁ fun C => if h : B.coeff C = 1 then (hfloor C h).choose else s₁
  have hg : ∀ i, g i ∈ logPluricanonicalSections sX 2 m B ∧ g i ≠ 0 := by
    rintro (_ | C)
    · exact ⟨hs₁, hs₁0⟩
    · by_cases h : B.coeff C = 1
      · simp only [g, Option.elim, dif_pos h]
        exact ⟨(hfloor C h).choose_spec.1, (hfloor C h).choose_spec.2.1⟩
      · simp only [g, Option.elim, dif_neg h]
        exact ⟨hs₁, hs₁0⟩
  have hgC : ∀ C : MMP.Mori.PrimeDivisor X, B.coeff C = 1 →
      1 - (m : ℤ) ≤ C.ordForm (g (some C)) := by
    intro C h
    simp only [g, Option.elim, dif_pos h]
    exact (hfloor C h).choose_spec.2.2
  set S' : Finset (Option (MMP.Mori.PrimeDivisor X)) := Finset.insertNone B.support
  refine ⟨S'.card * m, Nat.mul_pos (Finset.card_pos.2 ⟨none, Finset.none_mem_insertNone⟩) hm,
    dvd_mul_left m _, prodForm b S' g (S'.card * m),
    prodForm_mem_logPluricanonicalSections hn b S' hg,
    prodForm_ne_zero b (fun i _ => (hg i).2) _, fun C hC => ?_⟩
  have hCB : C ∈ B.support :=
    Finsupp.mem_support_iff.2 (by rw [← DivisorWithCoeffs.coeff_apply, hC]; norm_num)
  exact one_sub_le_ordForm_prodForm hn b S' hg hC (Finset.some_mem_insertNone.2 hCB) (hgC C hC)

/-- On a log resolution `f : Y ⟶ X` of a projective dlt surface pair `(X, B)` along which the
exceptional set and `f⁻¹(Supp B)` are snc, the crepant boundary `(Y, B_Y)` is an snc subboundary
pair. -/
private theorem isSNCSubboundaryPair_of_isCrepantBoundary
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hdlt : MMP.Intersection.IsDltPair sX B)
    {K : Divisor X} (hPw : IsPairWith sX 2 K B) {Y : Scheme.{0}} {f : Y ⟶ X}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsProper f]
    (hres : MMP.Resolution.IsResolutionOfVariety sX f)
    (hS : MMP.Resolution.IsSNCClosedSubset (f ≫ sX)
      ((MMP.Mori.exceptionalSet f : Set Y) ∪ f ⁻¹' (B.support.sup fun E => E.idealSheaf.support)))
    (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f) {BY : QDivisor Y}
    (hBY : IsCrepantBoundary sX 2 K B f hY hf BY) : IsSNCSubboundaryPair (f ≫ sX) BY := by
  have hle1 : ∀ F, BY.coeff F ≤ 1 := fun F => by
    have hlog := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hBY F)
      (show IsProper f from inferInstance)
    have h := hdlt.1.2.2 2 _ _ hlog
    have : ((BY.coeff F : ℚ) : ℝ) ≤ 1 := by
      push_cast at h
      linarith
    exact_mod_cast this
  have hprojY : MMP.Mori.IsProjectiveVariety ℂ (f ≫ sX) :=
    (MMP.Mori.isProjectiveVariety_iff ℂ (f ≫ sX)).2 ⟨hres.isVariety_source,
      isProjectiveMorphism_of_isProjective_of_isAffine (f ≫ sX) (hres.isProjective.comp
        ((MMP.Mori.isProjectiveVariety_iff ℂ sX).1 hproj).2.isProjective)⟩
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : CompactSpace Y := hY.1.toQuasiCompact.compactSpace_of_compactSpace
  have : AlgebraicGeometry.IsNoetherian Y := {}
  have : LocallyOfFinitePresentation (f ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := f ≫ sX)).mpr inferInstance
  obtain ⟨S, hsncS, hSmem⟩ := MMP.Mori.exists_finset_isSNC hres.isSmoothScheme
    (MMP.ProgramBaseChange.isSNCSubset_of_isSNCClosedSubset hres.isSmoothScheme
      (S := ⟨_, hS.1⟩) hS)
  refine ⟨hprojY, hres.isSmoothScheme, hsncS.of_support_subset fun G hG => ?_, hle1⟩
  rw [mem_support_sum_single]
  refine hSmem G ?_
  by_cases hGe : (⟨Y, f, hY, hf, G⟩ : DivisorOver ℂ sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
      (MMP.Flips.primeDivisor_genericPoint_mem_support G))
  · obtain ⟨P, hc, hη, -⟩ := MMP.Mori.exists_coeff_eq_of_not_isExceptional hPw hY hf hBY hGe
    refine Or.inr ?_
    show f G.genericPoint ∈ (B.support.sup fun E => (E.idealSheaf.support : Set X))
    rw [hη, Finset.sup_set_eq_biUnion]
    refine Set.mem_iUnion₂.2 ⟨P, ?_, MMP.Flips.primeDivisor_genericPoint_mem_support P⟩
    rwa [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, ← hc,
      DivisorWithCoeffs.coeff_apply, ← Finsupp.mem_support_iff]

/-- Pull-back along a resolution `f : Y ⟶ X` maps a nonzero section of `H⁰(X, e(K + B))` to a
form `τ` with `ord_E τ + ⌊e b_E⌋ ≥ 0` along every prime `E` of `Y`, for the crepant boundary
`B_Y`: a Hartogs bound. -/
private theorem ordForm_pullback_add_floor_nonneg (hX : IsNormalVariety ℂ sX) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) {Y : Scheme.{0}} {f : Y ⟶ X} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsProper f] [IsDominant f]
    (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f) {BY : QDivisor Y}
    (hBY : IsCrepantBoundary sX 2 K B f hY hf BY) {e : ℕ} (he : 0 < e)
    (heD : ((e : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    {s : RationalPluriForms sX 2 e} (hs : s ∈ logPluricanonicalSections sX 2 e B) (hs0 : s ≠ 0)
    (E : MMP.Mori.PrimeDivisor Y) :
    0 ≤ E.ordForm (pullbackRationalPluriForms sX f s) + ⌊((e : ℤ) • BY.coeff E : ℚ)⌋ := by
  change 0 ≤ (⟨Y, f, hY, hf, E⟩ : DivisorOver ℂ sX).ordPullback s + _
  exact ordPullback_add_floor_nonneg hX hK he heD _ hs hs0 (hBY E)

/-- On a log resolution of a dlt surface pair which is an isomorphism over the snc locus, the
pull-back of a section of `H⁰(X, M(K + B))` of order at least `1 - M` along every prime of
coefficient one vanishes along `T_Y = B_Y^{=1}`, whose components are the birational transforms of
those primes. -/
private theorem pullback_mem_pluricanonicalSections_sub_coeffOnePart [LocallyOfFiniteType sX]
    (hdlt : MMP.Intersection.IsDltPair sX B) (hn : topologicalKrullDim X = 2) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2) (hPw : IsPairWith sX 2 K B) {Y : Scheme.{0}}
    {f : Y ⟶ X} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsProper f] [IsDominant f]
    (hY : IsNormalVariety ℂ (f ≫ sX)) (hf : IsBirationalMorphism f)
    (hiso : ∀ U : X.Opens, IsSmoothScheme (U.ι ≫ sX) →
      MMP.Resolution.IsSNCClosedSubset (U.ι ≫ sX)
        (U.ι ⁻¹' (B.support.sup fun E => E.idealSheaf.support)) →
        IsIso (f ∣_ U))
    {BY : QDivisor Y} (hBY : IsCrepantBoundary sX 2 K B f hY hf BY) {M : ℕ} (hM : 0 < M)
    (hMD : ((M : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    {s₀ : RationalPluriForms sX 2 M} (hs₀ : s₀ ∈ logPluricanonicalSections sX 2 M B)
    (hs₀0 : s₀ ≠ 0)
    (hs₀C : ∀ C : MMP.Mori.PrimeDivisor X, B.coeff C = 1 → 1 - (M : ℤ) ≤ C.ordForm s₀) :
    pullbackRationalPluriForms sX f s₀ ∈ pluricanonicalSections (f ≫ sX) 2 M
      (DivisorWithCoeffs.roundDown ((M : ℤ) • BY) - (1 : ℤ) • coeffOnePart BY) ⊤ := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  rw [mem_pluricanonicalSections_of_ne_bot top_ne_bot]
  intro G _ _
  rw [one_smul, DivisorWithCoeffs.coeff_sub, coeff_coeffOnePart,
    DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  by_cases hG1 : BY.coeff G = 1
  · have hGe := not_isExceptional_of_coeff_eq_one hdlt hK hY hf hiso hBY hG1
    obtain ⟨P, hcoef, hη, hinv⟩ :=
      MMP.Mori.exists_coeff_eq_of_not_isExceptional hPw hY hf hBY hGe
    haveI := MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hinv).2
    have hP1 : B.coeff P = 1 := hcoef.symm.trans hG1
    rw [if_pos hG1, hG1, MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f
      hf.functionFieldMap_bijective hd G P hη s₀, zsmul_eq_mul, mul_one, Int.floor_intCast]
    linarith [hs₀C P hP1]
  · rw [if_neg hG1, sub_zero]
    exact ordForm_pullback_add_floor_nonneg hPw.1 hK hY hf hBY hM hMD hs₀ hs₀0 G

/-- Crepant self-maps of an snc subboundary surface pair `(Y, B_Y)` act with finite image on
`H⁰(Y, m(K_Y + B_Y))` once `H⁰(Y, M(K_Y + B_Y) - T_Y) ≠ 0` for some `m ∣ M`, `T_Y = B_Y^{=1}`:
multiplication by an invariant section `t` of `H⁰(Y, j(M(K_Y + B_Y) - T_Y))` embeds it
equivariantly into the sections of the klt snc pair `(Y, B_Y - (j/(m + jM))T_Y)`. -/
private theorem finite_range_of_mem_pluricanonicalSections_sub_coeffOnePart {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {BY : QDivisor Y} (hXBY : IsSNCSubboundaryPair sY BY) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor sY 2) (hnY : topologicalKrullDim Y = 2) {m : ℕ}
    (hmDY : ((m : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor) {M : ℕ} (hM : 0 < M)
    (hmM : m ∣ M) {t₀ : RationalPluriForms sY 2 M} (ht₀0 : t₀ ≠ 0)
    (ht₀ : t₀ ∈ pluricanonicalSections sY 2 M
      (DivisorWithCoeffs.roundDown ((M : ℤ) • BY) - (1 : ℤ) • coeffOnePart BY) ⊤) :
    (Set.range fun (σ : crepantBirationalAutomorphisms sY BY)
      (s : logPluricanonicalSections sY 2 m BY) =>
        pluriformPullback sY sY (σ : FunctionFieldEquiv sY sY).toHom 2 m
          (s : RationalPluriForms sY 2 m)).Finite := by
  have : LocallyOfFiniteType sY := hXBY.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  obtain ⟨j, hj, t, ht0, ht, htinv⟩ :=
    exists_invariant_mem_pluricanonicalSections hXBY hKY hmDY hM hmM ht₀0 ht₀
  have hN' : 0 < m + j * M := by positivity
  refine finite_range_of_injective_comp (finite_range_pluriformPullback_sub_coeffOnePart hXBY
    hKY hmDY hN' (dvd_add dvd_rfl (dvd_mul_of_dvd_right hmM j)) (a := j)
    (by exact_mod_cast hj)) (μ := fun y => RationalPluriForms.mul sY 2 m (j * M) y t)
    (fun y y' h => ?_) (fun s => ⟨RationalPluriForms.mul sY 2 m (j * M) s t,
      (mem_logPluricanonicalSections_sub_iff hN').2 ?_⟩)
    fun σ s => ?_
  · by_contra hne
    apply RationalPluriForms.mul_ne_zero hnY (sub_ne_zero.mpr hne) ht0
    rw [map_sub, LinearMap.sub_apply]
    exact sub_eq_zero.2 h
  · rw [roundDown_smul_add_mul BY (exists_mul_coeff_eq_intCast hmDY hmM) m j]
    have hs := s.2
    rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot] at hs
    rw [mem_pluricanonicalSections_of_ne_bot top_ne_bot] at ht ⊢
    intro Γ hΓ h0
    have hs0 : (s : RationalPluriForms sY 2 m) ≠ 0 :=
      fun h => h0 (by rw [h, map_zero, LinearMap.zero_apply])
    have h1 := hs Γ hΓ hs0
    have h2 := ht Γ hΓ ht0
    rw [ordForm_mul Γ hs0 ht0]
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, Finsupp.coe_add, Finsupp.coe_sub,
      Finsupp.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul,
      zsmul_eq_mul, one_smul, one_mul, mul_sub, Pi.mul_apply, Pi.natCast_apply,
      Pi.intCast_apply] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    linarith
  · rw [pluriformPullback_mul, htinv σ σ.2]

/-- Crepant self-maps of a projective dlt surface act with finite image on `H⁰(X, m(K + B))`
when every coefficient-one prime carries a nonzero section vanishing along it. -/
private theorem finite_range_of_forall_exists_ordForm_ge
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hP : MMP.Fourfold.IsPair sX B)
    (hdlt : MMP.Intersection.IsDltPair sX B) (hn : topologicalKrullDim X = 2)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2) {m : ℕ} (hm : 0 < m)
    (hmD : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hfloor : ∀ C : MMP.Mori.PrimeDivisor X, B.coeff C = 1 →
      ∃ s ∈ logPluricanonicalSections sX 2 m B, s ≠ 0 ∧ 1 - (m : ℤ) ≤ C.ordForm s) :
    (Set.range fun (σ : crepantBirationalAutomorphisms sX B)
        (s : logPluricanonicalSections sX 2 m B) =>
      pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
        (s : RationalPluriForms sX 2 m)).Finite := by
  have hMP : MMP.Mori.IsPair sX B := hP.isPair
  have hX : IsNormalVariety ℂ sX := hMP.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  by_cases hV : ∀ s ∈ logPluricanonicalSections sX 2 m B, s = 0
  · refine (Set.finite_singleton
      (fun _ : logPluricanonicalSections sX 2 m B => (0 : RationalPluriForms sX 2 m))).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine Set.mem_singleton_iff.2 (funext fun s => ?_)
    change pluriformPullback sX sX (σ : FunctionFieldEquiv sX sX).toHom 2 m
      (s : RationalPluriForms sX 2 m) = 0
    rw [hV _ s.2, map_zero]
  push Not at hV
  obtain ⟨s₁, hs₁, hs₁0⟩ := hV
  obtain ⟨M, hM, hmM, s₀, hs₀, hs₀0, hs₀C⟩ :=
    exists_mem_logPluricanonicalSections_ordForm_ge hn hm hfloor hs₁ hs₁0
  obtain ⟨Y, f, hres, -, hS, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset sX hX B.support
  haveI : IsProper f := hres.isProjective.isProper
  have hf := hres.isBirationalMorphism
  obtain ⟨hY, hdimY, -⟩ := (⟨inferInstance, hf, hres.isSmoothScheme⟩ :
    IsSmoothResolution sX f).isNormalVariety hX
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  haveI : IsNormal Y := hY.2
  haveI : CompactSpace Y := hY.1.toQuasiCompact.compactSpace_of_compactSpace
  haveI : AlgebraicGeometry.IsNoetherian Y := {}
  haveI := hf.isDominant
  haveI := hres.isVariety_source
  have hnY : topologicalKrullDim Y = 2 := hdimY.trans hn
  obtain ⟨⟨BY, hBY, -⟩, hint⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hMP hK f hY hf
  obtain ⟨KY, hKY⟩ :=
    MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hres.isSmoothScheme hnY
  have hmDY : ((m : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor := by
    obtain ⟨D', hD'⟩ := hint BY hBY (m : ℤ) hmD
    exact ⟨(m : ℤ) • KY + D', by rw [map_add, map_zsmul, hD', smul_add],
      MMP.Fourfold.isCartier_of_isSmoothScheme hres.isSmoothScheme _⟩
  have hPw : IsPairWith sX 2 K B := ⟨hX, hK, ⟨m, by exact_mod_cast hm.ne', hmD⟩⟩
  have ht₀0 : pullbackRationalPluriForms sX f s₀ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
      hf.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn) hs₀0
  refine finite_range_of_finite_range_crepantBoundary hMP hK hY hf hKY hBY (fun s hs hs0 => ?_)
    (finite_range_of_mem_pluricanonicalSections_sub_coeffOnePart
      (isSNCSubboundaryPair_of_isCrepantBoundary hproj hdlt hPw hres hS hY hf hBY) hKY hnY hmDY
      hM hmM ht₀0 (pullback_mem_pluricanonicalSections_sub_coeffOnePart hdlt hn hK hPw hY hf hiso
        hBY hM (isCartierDivisor_smul_of_dvd hmD hmM) hs₀ hs₀0 hs₀C))
  rw [mem_logPluricanonicalSections, mem_pluricanonicalSections_of_ne_bot top_ne_bot]
  intro E _ _
  rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul]
  exact ordForm_pullback_add_floor_nonneg hX hK hY hf hBY hm hmD hs hs0 E

end Vertical

section Collection

variable {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of ℂ)}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  {B : ∀ i, QDivisor (X i)} {m : ℕ}

/-- The degree-`m` adjoint of a component is Cartier for a canonical divisor of dimension two. -/
private theorem exists_isCanonicalDivisor_isCartierDivisor (R : ResidueRestriction sX B 2 m)
    (i : I) : ∃ K : Divisor (X i), K.IsCanonicalDivisor (sX i) 2 ∧
      ((m : ℤ) • (Divisor.toQDivisor K + B i)).IsCartierDivisor := by
  obtain ⟨d, K, hK, hKc⟩ :=
    R.setting.isCartierDivisor i (StratumAdjunctionData.refl (R.setting.isPair i).isPair)
  simp only [Category.id_comp] at hK
  have hd := hK.topologicalKrullDim_eq
  rw [R.setting.topologicalKrullDim_eq i] at hd
  obtain rfl : d = 2 := by exact_mod_cast hd.symm
  exact ⟨K, hK, hKc⟩

private theorem finite_range_of_not_injective (R : ResidueRestriction sX B 2 m) (i : I)
    (h : ∀ (S : Scheme.{0}) (ι : S ⟶ X i) (BS : QDivisor S)
      (F : StratumAdjunctionData (sX i) (B i) ι BS), 0 < F.length →
        topologicalKrullDim S = (1 : ℕ) → ¬ Function.Injective (R.toFun i F 1)) :
    (Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
        (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom 2 m
          ((s : logPluricanonicalSections (sX i) 2 m (B i)) :
            RationalPluriForms (sX i) 2 m)).Finite := by
  obtain ⟨K, hK, hKc⟩ := exists_isCanonicalDivisor_isCartierDivisor R i
  have hfin := finite_range_of_forall_exists_ordForm_ge (R.setting.isProjectiveVariety i)
    (R.setting.isPair i) (R.setting.isDltPair i) (R.setting.topologicalKrullDim_eq i) hK
    R.setting.pos hKc (exists_ordForm_ge_of_not_injective R i h)
  refine (hfin.image fun φ (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
    φ (s : logPluricanonicalSections (sX i) 2 m (B i))).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨_, ⟨σ, rfl⟩, rfl⟩

end Collection

end MMP.Fourfold.PreadmissibleCrepantActionFinite

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open PreadmissibleCrepantActionFinite

open MMP.Mori

/-- **Crepant self-maps of a semiample dlt surface act finitely on preadmissible sections.**
Let `(X_i, B_i)`, `i ∈ I`, be projective rational dlt pairs on complex surfaces with canonical
divisors `K_i` such that `K_i + B_i` is semiample. There is `m₀ > 0` such that for every `m`
divisible by `m₀` and every residue restriction structure `R` on the collection in degree `m`:
* for each `i`, the crepant birational self-maps of `(X_i, B_i)` induce only finitely many maps
  `σ^*` on the `i`-th entries of the preadmissible section systems;
* for each crepant birational self-map `σ` of `(X_i, B_i)` and each preadmissible system `s`,
  `σ^* s_i` has the same residue restriction as `s_i` on every proper stratum of `X_i`. -/
@[mmp "lem_fourfold_semiample_surface_preadmissible_representation_finite"]
public theorem exists_finite_range_pluriformPullback_preadmissibleSections
    {I : Type*} {X : I → Scheme.{0}} {sX : ∀ i, X i ⟶ Spec (.of ℂ)}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    {B : ∀ i, QDivisor (X i)} {K : ∀ i, Divisor (X i)}
    (_hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 2)
    (_hsemi : ∀ i, QDivisor.IsRelativelySemiample (sX i) (Divisor.toQDivisor (K i) + B i)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ∣ m → ∀ R : ResidueRestriction sX B 2 m,
      (∀ i : I, (Set.range fun (σ : crepantBirationalAutomorphisms (sX i) (B i))
        (s : (preadmissibleSections R).map (LinearMap.proj i)) =>
        pluriformPullback (sX i) (sX i) (σ : FunctionFieldEquiv (sX i) (sX i)).toHom 2 m
          ((s : logPluricanonicalSections (sX i) 2 m (B i)) :
            RationalPluriForms (sX i) 2 m)).Finite) ∧
      ∀ (i : I), ∀ σ ∈ crepantBirationalAutomorphisms (sX i) (B i),
        ∀ s ∈ preadmissibleSections R, ∀ u : logPluricanonicalSections (sX i) 2 m (B i),
        (u : RationalPluriForms (sX i) 2 m) = pluriformPullback (sX i) (sX i) σ.toHom 2 m (s i) →
        ∀ {S : Scheme.{0}} {ι : S ⟶ X i} {BS : QDivisor S}
          (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ), 0 < F.length →
          topologicalKrullDim S = e → R.toFun i F e u = R.toFun i F e (s i) := by
  refine ⟨1, one_pos, fun m _ R => ⟨fun i => ?_, ?_⟩⟩
  · by_cases hA : ∃ (S : Scheme.{0}) (ι : S ⟶ X i) (BS : QDivisor S)
        (F : StratumAdjunctionData (sX i) (B i) ι BS), 0 < F.length ∧
          topologicalKrullDim S = (1 : ℕ) ∧ Function.Injective (R.toFun i F 1)
    · obtain ⟨S, ι, BS, F, hF, hS, hinj⟩ := hA
      exact finite_range_of_injective_toFun R i F hF hS hinj
    · push Not at hA
      exact finite_range_of_not_injective R i hA
  · intro i σ hσ s hs u hu S ι BS F e hF he
    exact (ResidueRestriction.exists_preadmissible_pluriformPullback_and_toFun_eq R
      (fun l P => (R.setting.isPair l).nonneg P) σ hσ hs).2 u hu F e hF he

end MMP.Fourfold
