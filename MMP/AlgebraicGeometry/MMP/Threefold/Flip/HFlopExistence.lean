module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
import MMP.AlgebraicGeometry.MMP.MinimalModel.KltStepQFactorial
import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.KltFlipExistence
import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback
import MMP.AlgebraicGeometry.MMP.Flip.HFlopIsLogFlip
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial

/-!
# Existence of `H`-flops of projective klt threefolds

Let `(X, B)` be a klt pair, with `B ≥ 0` a `ℚ`-divisor, on a projective normal `ℚ`-factorial
complex threefold, and let `H ≥ 0` be a `ℚ`-Cartier `ℚ`-divisor on `X`. Let `f : X ⟶ V` be a
nontrivial small projective contraction onto a normal projective variety with `ρ(X/V) = 1`,
such that `K_X + B` is numerically `f`-trivial and `-H` is `f`-ample. Then the `H`-flop
`f⁺ : X⁺ ⟶ V` of `f` with respect to `K_X + B` exists. Moreover `X⁺` is projective and
`ℚ`-factorial, the flop is crepant (`K_X + B` and its transform `K_{X⁺} + B⁺` are the pull-backs
of one `ℝ`-Cartier divisor on `V`), and `(X⁺, B⁺)` is klt.

The proof perturbs the boundary to `B + εH`, for which `f` is the contraction of a negative
extremal ray, and applies the existence of klt threefold flips.

## Main results

* `MMP.Flips.exists_isHFlop_of_isKltPair`

## Implementation notes

The klt condition is Kollár–Mori's `MMP.Mori.IsKltPair` for the canonical divisor `K` of
dimension `3`, which also records that `X` is a threefold; effectivity of `B` is the separate
hypothesis `0 ≤ B`. The flop is `MMP.Flips.IsHFlop`, which carries the birational map
`ρ : X ⤏ X⁺`; the canonical divisor and boundary of `X⁺` are the transforms `ρ_* K` and `ρ_* B`.
Connectedness of the fibres of `f` is part of `MMP.Flips.IsSmall` (`f_* 𝒪_X = 𝒪_V`), and
nontriviality is `¬ IsIso f`. Crepancy is the existence of an `ℝ`-Cartier divisor `D` on `V`
with `MMP.Flips.IsRCartierPullback` along `f` and `f⁺`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.8, 15.4
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

namespace Proof_lem_fourfold_projective_effective_divisor_flop_exists

/-! ### Divisors -/

section Divisors

variable {X : Scheme.{0}}

/-- The coefficients of a klt boundary `B ≥ 0` lie in `[0, 1]`. -/
private theorem isBoundary_toRDivisor_of_isKltPair {k : Type} [Field k] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {B : QDivisor X} (hB : 0 ≤ B) (hklt : MMP.Mori.IsKltPair sX n K B) :
    IsBoundary (QDivisor.toRDivisor B) := by
  intro P
  rw [QDivisor.coeff_toRDivisor]
  have h1 : 0 ≤ B.coeff P := DivisorWithCoeffs.isEffective_iff_nonneg.2 hB P
  have h2 : B.coeff P < 1 := roundDown_nonpos_iff.mp hklt.2.2 P
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2.le⟩

/-- `q H`, regarded as an `ℝ`-divisor. -/
private theorem toRDivisor_smul (H : QDivisor X) (q : ℚ) :
    QDivisor.toRDivisor (q • H) = (q : ℝ) • QDivisor.toRDivisor H := by
  ext P
  change (((q • H).coeff P : ℚ) : ℝ) = (q : ℝ) * ((H.coeff P : ℚ) : ℝ)
  rw [DivisorWithCoeffs.coeff_smul, smul_eq_mul, Rat.cast_mul]

/-- `B + q H`, regarded as an `ℝ`-divisor. -/
private theorem toRDivisor_add_smul (B H : QDivisor X) (q : ℚ) :
    QDivisor.toRDivisor (B + q • H) = QDivisor.toRDivisor B + (q : ℝ) • QDivisor.toRDivisor H := by
  rw [map_add, toRDivisor_smul]

/-- `K + D`, for a divisor `K` and a `ℚ`-divisor `D`, regarded as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_toRDivisor (K : Divisor X) (D : QDivisor X) :
    logCanonicalDivisor K (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + D) := by
  rw [map_add, QDivisor.toRDivisor_toQDivisor]
  rfl

/-- If `M = r D` for a divisor `M` and `r > 0`, then `D = r⁻¹ M` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_natCast_smul {D : QDivisor X} {r : ℕ} (hr : 0 < r)
    {M : Divisor X} (hM : Divisor.toQDivisor M = (r : ℤ) • D) :
    QDivisor.toRDivisor D = (r : ℝ)⁻¹ • Divisor.toRDivisor M := by
  rw [QDivisor.toRDivisor_eq_inv_smul (by exact_mod_cast hr.ne') hM]
  push_cast
  rfl

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor_of_isQCartier [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (hD : D.IsQCartier) : IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, D', hD', hD'c⟩ := hD.exists_pos
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => D', fun _ => hD'c, ?_⟩
  rw [Fin.sum_univ_one]
  ext P
  have hP := congrArg (fun F : QDivisor X => F P) hD'
  change ((D' P : ℤ) : ℚ) = ((m : ℤ) : ℚ) * D P at hP
  change ((D P : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((D' P : ℤ) : ℝ)
  have h2 : ((D' P : ℤ) : ℝ) = (m : ℝ) * ((D P : ℚ) : ℝ) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hP
    simpa using this
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hm', one_mul]

/-- The birational transform commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem flipTransform_toQDivisor {Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (K : Divisor X) :
    flipTransform f g (Divisor.toQDivisor K) = Divisor.toQDivisor (flipTransform f g K) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Flips.transformDivisor_toQDivisor,
    MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]

/-- The birational transform commutes with regarding a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {Y : Scheme.{0}} (ρ : X.RationalMap Y)
    (D : QDivisor X) :
    RationalMap.transformDivisor ρ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (RationalMap.transformDivisor ρ D) := by
  have : (RationalMap.transformDivisor ρ).comp (QDivisor.toRDivisor (X := X)) =
      (QDivisor.toRDivisor (X := Y)).comp (RationalMap.transformDivisor ρ) := by
    refine Finsupp.addHom_ext fun P r => ?_
    simp only [AddMonoidHom.comp_apply, QDivisor.toRDivisor,
      DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply, DivisorWithCoeffs.mapCoeffs,
      Finsupp.mapRange_single, RationalMap.transformDivisor_single]
    cases RationalMap.transformPrimeDivisor ρ P <;> simp
  exact DFunLike.congr_fun this D

end Divisors

/-! ### Small morphisms -/

/-- The Kollár–Mori exceptional set of a small birational contraction onto a normal variety has
codimension at least two. -/
private theorem two_le_closedsCodimension_exceptionalSet_of_isSmall {k : Type} [Field k]
    {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    (hV : IsNormalVariety k sV) {f : X ⟶ V} (hf : IsSmall k sV sX f) :
    2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f) := by
  haveI : IsIntegral X := hf.isVariety_source.toIsIntegral
  haveI : IsIntegral V := hV.1.toIsIntegral
  haveI : IsNormal V := hV.2
  haveI : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : IsProper f := hf.isProper
  have hfb : IsBirationalMorphism f := IsSmall.isBirationalMorphism sV sX hf
  obtain ⟨-, V', W, hV', -, hle, hiso⟩ := hf
  rw [le_closedsCodimension_iff_le_coheight]
  intro x hx
  by_contra hlt
  have hx1 : Order.coheight x ≤ 1 := by
    by_contra h
    push Not at h
    exact hlt (by simpa [one_add_one_eq_two] using Order.add_one_le_of_lt h)
  have hxV : x ∈ V'.compl := fun hxV => by
    have := (le_closedsCodimension_iff_le_coheight.mp hV') x hxV
    have := this.trans hx1
    norm_num at this
  let U : X.Opens := V'.compl
  let U' : V.Opens := W.compl
  let p : U.toScheme := ⟨x, hxV⟩
  have hfp : U'.ι (f.resLE U' U hle p) = f x := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rfl
  have hfx : Order.coheight (f x) ≤ 1 := by
    rw [← hfp, Topology.IsOpenEmbedding.coheight_eq _ U'.ι.isOpenEmbedding,
      Topology.IsOpenEmbedding.coheight_eq _ (f.resLE U' U hle).isOpenEmbedding,
      ← Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding]
    exact hx1
  exact hx (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb hfx)

/-- A proper birational morphism from a normal variety onto a normal variety whose Kollár–Mori
exceptional set has codimension at least two is a small birational contraction. -/
private theorem isSmall_of_two_le_closedsCodimension_exceptionalSet {k : Type} [Field k]
    {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (hV : IsNormalVariety k sV) {g : Y ⟶ V} (hgs : g ≫ sV = sY)
    [IsProper g] (hgb : IsBirationalMorphism g)
    (h2 : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet g)) : IsSmall k sV sY g := by
  haveI : IsNormal V := hV.2
  haveI := hY.1
  haveI := hV.1
  have hbc : IsBirationalContraction k sV sY g :=
    { isVariety_target := hV.1
      isVariety_source := hY.1
      comp_eq := hgs
      isProper := inferInstance
      isIso_app := (isIso_app_and_exists_isBiregular_of_isBirationalMorphism hV g
        (hgs ▸ hY.1) hgb).1
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sY hgb).symm }
  refine (isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  rw [le_closedsCodimension_iff_le_coheight] at h2 ⊢
  intro y hy
  refine h2 y fun hy' => hy ⟨g ⁻¹ᵁ biregularLocus g, by simpa using hy', ?_⟩
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  rw [← morphismRestrict_ι]
  infer_instance

/-! ### Projectivity -/

/-- A proper morphism with a relatively ample `ℚ`-divisor, to a scheme carrying an ample
invertible module, is projective. -/
private theorem isProjectiveMorphism_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {g : X ⟶ Y} [IsProper g]
    {D : QDivisor X} (hD : D.HasRelativelyAmpleMultiple g) (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (hM : Stacks.Ample.IsAmple Y M) :
    IsProjectiveMorphism g := by
  obtain ⟨m, -, L, hL, -, hamp⟩ := hD
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact isProjectiveMorphism_of_isQuasiProjective g M hM
    ⟨⟨inferInstance, inferInstance⟩, L.divisorialSheaf, inferInstance,
      Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple g _
        inferInstance hamp⟩

/-! ### The flip as a rational map -/

/-- For birational morphisms `f : X ⟶ V` and `g : Y ⟶ V` to a separated scheme, there is a
birational map `ρ : X ⤏ Y` with `g ∘ ρ = f`. -/
private theorem exists_isBirational_compHom_eq {k : Type} [Field k] {X Y V : Scheme.{0}}
    [IsReduced X] [IsReduced Y] {sV : V ⟶ Spec (.of k)} [IsSeparated sV] {f : X ⟶ V}
    {g : Y ⟶ V} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    ∃ ρ : X.RationalMap Y, RationalMap.IsBirational ρ ∧ ρ.compHom g = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := hf
  obtain ⟨e₂, h₂⟩ := hg
  have : IsSeparated (V ↘ Limits.terminal Scheme) := by
    rw [show (V ↘ Limits.terminal Scheme) = sV ≫ (Spec (.of k) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have k₁ := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq e₁ f (𝟙 V) h₁
  have k₂ := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq e₂ g (𝟙 V) h₂
  simp only [Category.comp_id] at k₁ k₂
  set e := e₁.trans e₂.symm
  have H : e.IsOver f g := k₁.trans k₂.symm
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ g =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H]
  simp

/-! ### Intersection numbers on contracted curves -/

/-- If `r (K + B) = f^* M` for a Cartier divisor `M` on the base and `-H` is `f`-ample, then
`K + B + ε H` is negative on every curve contracted by `f`, for `ε > 0`. -/
private theorem intersectionNumber_add_smul_neg {k : Type} [Field k] {X V : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [QuasiCompact sX] [IsSeparated sV] [LocallyOfFiniteType sV]
    [QuasiCompact sV] [IsLocallyNoetherian V] [IsNormal V] {f : X ⟶ V} (hfs : f ≫ sV = sX)
    {K : Divisor X} {B H : QDivisor X} {r : ℕ} (hr : 0 < r) {M : Divisor V} (hMc : M.IsCartier)
    {MX : Divisor X} {hBX : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ M.supp}
    (hMX : Divisor.toQDivisor MX = (r : ℤ) • (Divisor.toQDivisor K + B))
    (hpbX : M.IsPullback f hBX MX)
    (hHf : IsRelativelyAntiAmple f (QDivisor.toRDivisor H)) {ε : ℚ} (hε : 0 < ε)
    (hQ : (Divisor.toQDivisor K + (B + ε • H)).IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    (Divisor.toQDivisor K + (B + ε • H)).intersectionNumber k sX C.ι C.dim_le hQ < 0 := by
  obtain ⟨m, rr, L, hm, hrr, hL, heq⟩ := hHf
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  have hMXc : MX.IsCartier := hpbX.isCartier hMc
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  -- a presentation of `K + B + ε H` by `M_X` and the `f`-ample `L_j`
  let r' : Fin (m + 1) → ℝ := Fin.cons ((r : ℝ)⁻¹) fun j => -((ε : ℝ) * rr j)
  let L' : Fin (m + 1) → Divisor X := Fin.cons MX L
  have hL'c : ∀ j, (L' j).IsCartier := fun j =>
    Fin.cases (motive := fun j => (L' j).IsCartier) hMXc hLc j
  have hPX : QDivisor.toRDivisor (Divisor.toQDivisor K + B) =
      (r : ℝ)⁻¹ • Divisor.toRDivisor MX :=
    toRDivisor_eq_inv_natCast_smul hr hMX
  have hHL : (ε : ℝ) • QDivisor.toRDivisor H = ∑ j, (-((ε : ℝ) * rr j)) • Divisor.toRDivisor (L j) := by
    have h := congrArg (fun G => (-(ε : ℝ)) • G) heq
    simp only [smul_neg, neg_smul, neg_neg, Finset.smul_sum, smul_smul] at h
    rw [h]
    simp only [neg_mul, neg_smul]
  have hpres : QDivisor.toRDivisor (Divisor.toQDivisor K + (B + ε • H)) =
      ∑ j, r' j • Divisor.toRDivisor (L' j) := by
    rw [Fin.sum_univ_succ]
    simp only [r', L', Fin.cons_zero, Fin.cons_succ]
    rw [← add_assoc, map_add, hPX, toRDivisor_smul, hHL]
  have hsum := intersectionNumber_eq_sum_of_toRDivisor_eq (sX := sX) C.ι C.dim_le _ hQ r'
    L' hL'c hpres
  have h0 : MX.degreeOn k sX C.ι C.dim_le hMXc = 0 := by
    have h := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f hfs hMc hBX C hC
    have hpe : M.pullback hMc hBX = MX := hpbX.pullback_eq hMc
    convert h using 2
    exact hpe.symm
  have hpos : ∀ j, 0 < (L j).degreeOn k sX C.ι C.dim_le (hLc j) := fun j =>
    degreeOn_pos_of_isRelativelyAmpleCartier (sX := sX) f (hL j) (hLc j) C hC
  have hneg : ((Divisor.toQDivisor K + (B + ε • H)).intersectionNumber k sX C.ι C.dim_le hQ :
      ℝ) < 0 := by
    have e : ∑ j, r' j * ((L' j).degreeOn k sX C.ι C.dim_le (hL'c j) : ℝ) =
        (r : ℝ)⁻¹ * (MX.degreeOn k sX C.ι C.dim_le hMXc : ℝ) +
          ∑ j : Fin m, -((ε : ℝ) * rr j) * ((L j).degreeOn k sX C.ι C.dim_le (hLc j) : ℝ) := by
      rw [Fin.sum_univ_succ]
      rfl
    rw [hsum, e, h0]
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    have h1 : ∑ j : Fin m, -((ε : ℝ) * rr j) * ((L j).degreeOn k sX C.ι C.dim_le (hLc j) : ℝ) <
        0 := by
      refine Finset.sum_neg (fun j _ => ?_) hne
      have := hpos j
      have hj : (0 : ℝ) < ((L j).degreeOn k sX C.ι C.dim_le (hLc j) : ℝ) := by exact_mod_cast this
      nlinarith [mul_pos hε' (hrr j)]
    simpa using h1
  exact_mod_cast hneg

/-! ### Relative curve classes in relative Picard number one -/

section RelativeClasses

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {f : X ⟶ Y}

/-- A numerically `f`-trivial `ℝ`-Cartier divisor vanishes on `N₁(X/Y)`. -/
private theorem relIntersectionNumber_eq_zero_of_mem {δ : KCartierDivisor ℝ X}
    (hδ : δ ∈ relativeNumericallyTrivialDivisors sX f) (z : RelativeNumericalCurveClasses sX f) :
    RelativeNumericalCurveClasses.intersectionNumber δ z = 0 := by
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass]
  have hle : relativeOneCycles sX f ≤
      LinearMap.ker (OneCycle.intersectionPairing (sX := sX) δ) := by
    rw [relativeOneCycles, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨C, hC, rfl⟩
    exact LinearMap.mem_ker.mpr ((mem_relativeNumericallyTrivialDivisors sX f).mp hδ C hC)
  exact LinearMap.mem_ker.mp (hle hZ)

/-- In relative Picard number one, every `ℝ`-Cartier divisor is proportional on `N₁(X/Y)` to a
divisor `δ₀` which is nonzero on a contracted curve `C₀`. -/
private theorem exists_relIntersectionNumber_eq_mul
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1)
    {δ₀ : KCartierDivisor ℝ X} {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (h₀ : (C₀.cycle ℝ).intersectionNumber δ₀ ≠ 0) (δ : KCartierDivisor ℝ X) :
    ∃ c : ℝ, ∀ z : RelativeNumericalCurveClasses sX f,
      RelativeNumericalCurveClasses.intersectionNumber δ z =
        c * RelativeNumericalCurveClasses.intersectionNumber δ₀ z := by
  have hne : (Submodule.Quotient.mk δ₀ : RelativeNumericalDivisorClasses sX f) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivialDivisors]
    exact fun h => h₀ (h C₀ hC₀)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hfin (Submodule.Quotient.mk δ)
  have hmem : δ - c • δ₀ ∈ relativeNumericallyTrivialDivisors sX f := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      hc, sub_self]
  refine ⟨c, fun z => ?_⟩
  have h := relIntersectionNumber_eq_zero_of_mem hmem z
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  simp only [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul] at h ⊢
  linarith

/-- On an integral scheme, Cartier divisors separate the points of `N₁(X/Y)`. -/
private theorem eq_zero_of_forall_relIntersectionNumber_ofCartier [IsIntegral X]
    (z : RelativeNumericalCurveClasses sX f)
    (h : ∀ E : X.CartierDivisor,
      RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) z = 0) :
    z = 0 := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  rw [mem_relativeNumericallyTrivial, OneCycle.mem_numericallyTrivial]
  intro L _
  obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
  have h0 := h E
  rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
    OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree] at h0
  rw [← h0, OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso k sX C.ι C.dim_le e)

/-- The pairing with a Cartier divisor is continuous on `N₁(X/Y)`. -/
private theorem continuous_relIntersectionNumber_ofCartier (E : X.CartierDivisor) :
    Continuous (RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f)
      (KCartierDivisor.ofCartier ℝ E)) := by
  have : ⇑(RelativeNumericalCurveClasses.intersectionNumber (sX := sX) (f := f)
      (KCartierDivisor.ofCartier ℝ E)) =
      ⇑(RelativeNumericalCurveClasses.degree sX f (MMP.CartierDivisor.sheaf E)) := by
    funext z
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
    rw [RelativeNumericalCurveClasses.intersectionNumber_relativeNumericalClass,
      OneCycle.intersectionNumber_ofCartier,
      RelativeNumericalCurveClasses.degree_relativeNumericalClass]
    rfl
  rw [this]
  exact RelativeNumericalCurveClasses.continuous_degree sX f _

/-- A Cartier divisor nonnegative on the contracted curves is nonnegative on `NE̅(X/Y)`. -/
private theorem relIntersectionNumber_nonneg_of_mem (E : X.CartierDivisor)
    (hE : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E))
    {z : RelativeNumericalCurveClasses sX f} (hz : z ∈ relativeClosedConeOfCurves sX f) :
    0 ≤ RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) z := by
  have hcl : IsClosed {z : RelativeNumericalCurveClasses sX f |
      0 ≤ RelativeNumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ E) z} :=
    isClosed_le continuous_const (continuous_relIntersectionNumber_ofCartier E)
  have hsub : (relativeConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) ⊆
      {z | 0 ≤ RelativeNumericalCurveClasses.intersectionNumber
        (KCartierDivisor.ofCartier ℝ E) z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hE C hC
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      exact add_nonneg hx hy
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq, LinearMap.map_smul_of_tower] at hx ⊢
      exact smul_nonneg c.2 hx
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal hsub hcl hz

/-- In relative Picard number one some curve is contracted. -/
private theorem exists_isContractedBy_of_finrank_eq_one
    (hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hno
  push Not at hno
  haveI : Subsingleton (RelativeNumericalDivisorClasses sX f) := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, mem_relativeNumericallyTrivialDivisors]
    exact fun C hC => absurd hC (hno C)⟩
  rw [Module.finrank_zero_of_subsingleton] at hfin
  exact zero_ne_one hfin

end RelativeClasses

/-! ### The extremal ray of a contraction of relative Picard number one -/

/-- **A contraction of relative Picard number one contracts an extremal ray.** Let
`f : X ⟶ V` be a small projective contraction between projective varieties over an algebraically
closed field of characteristic zero, with `ρ(X/V) = 1`, and `D` a `ℚ`-Cartier `ℚ`-divisor which is
negative on every curve contracted by `f`. Then `f` is the contraction of a `D`-negative extremal
ray of `NE̅(X)`. -/
private theorem exists_isNegativeExtremalRayOf_isContractionOfRay {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X V : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sV : V ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [QuasiCompact sX] [IsLocallyNoetherian V] [IsNormal V]
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hV : MMP.Mori.IsProjectiveVariety k sV)
    {f : X ⟶ V} (hf : IsSmall k sV sX f) (hfp : IsProjectiveMorphism f)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1) {A : Divisor X}
    (hA : IsRelativelyAmpleCartier f A) (D : QDivisor X) (hD : D.IsQCartier)
    (hneg : ∀ C : ProperCurve sX, C.IsContractedBy f →
      D.intersectionNumber k sX C.ι C.dim_le hD < 0) :
    ∃ R : Set (NumericalCurveClasses sX), MMP.Fourfold.IsNegativeExtremalRayOf sX D R ∧
      MMP.Fourfold.IsContractionOfRay sX sV R f := by
  have hfs : f ≫ sV = sX := hf.comp_eq
  haveI : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety k sV := hV
  have hVv : AlgebraicGeometry.IsVariety k sV := hV.toIsVariety
  haveI : IsSeparated sV := hVv.toIsSeparated
  haveI : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  have hfin : Module.finrank ℝ (RelativeNumericalDivisorClasses sX f) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)
  -- an `f`-ample Cartier divisor
  obtain ⟨EA, hEA⟩ := exists_cartierDivisor_degree_eq (sX := sX) A hA.1
  set δA := KCartierDivisor.ofCartier ℝ EA with hδA
  have hApos : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < (C.cycle ℝ).intersectionNumber δA := fun C hC => by
    rw [hEA C]
    exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier (sX := sX) f hA hA.1 C hC
  -- a contracted curve, whose class spans `N₁(X/V)`
  obtain ⟨C₀, hC₀⟩ := exists_isContractedBy_of_finrank_eq_one hfin
  set c₀ := C₀.relativeClass f hC₀ with hc₀def
  have hc₀ : 0 < RelativeNumericalCurveClasses.intersectionNumber δA c₀ := hApos C₀ hC₀
  have hc₀ne : c₀ ≠ 0 := fun h => by
    rw [h, map_zero] at hc₀
    exact lt_irrefl _ hc₀
  have hspan : ∀ z : RelativeNumericalCurveClasses sX f,
      z = (RelativeNumericalCurveClasses.intersectionNumber δA z /
        RelativeNumericalCurveClasses.intersectionNumber δA c₀) • c₀ := by
    intro z
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_relIntersectionNumber_ofCartier _ fun E => ?_
    obtain ⟨c, hc⟩ := exists_relIntersectionNumber_eq_mul hfin hC₀ (hApos C₀ hC₀).ne'
      (KCartierDivisor.ofCartier ℝ E)
    rw [map_sub, map_smul, hc z, hc c₀, smul_eq_mul]
    field_simp
    ring
  -- `NE̅(X/V)` is the ray spanned by `[C₀]`
  have hcone : (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • c₀ = w} := by
    ext z
    constructor
    · intro hz
      exact ⟨_, div_nonneg (relIntersectionNumber_nonneg_of_mem EA (fun C hC => (hApos C hC).le)
        hz) hc₀.le, (hspan z).symm⟩
    · rintro ⟨c, hc, rfl⟩
      exact (relativeClosedConeOfCurves sX f).smul_mem hc
        (subset_closure (relativeClass_mem_relativeConeOfCurves hC₀))
  have hrayrel : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) :=
    ⟨⟨subset_rfl, isCone_coe _, fun u hu v hv => add_mem hu hv, fun u hu v hv _ => ⟨hu, hv⟩⟩,
      c₀, hc₀ne, hcone⟩
  have hray := isExtremalRay_image_relativeToAbsolute sX sV f hfs hrayrel
  set u₀ := OneCycle.numericalClass sX (C₀.cycle ℝ) with hu₀
  have hR : relativeToAbsolute sX f ''
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • u₀ = w} := by
    rw [hcone]
    ext w
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul]; rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • c₀, ⟨c, hc, rfl⟩, by rw [map_smul]; rfl⟩
  refine ⟨_, ⟨hD, hray, fun u hu hu0 => ?_⟩, ?_⟩
  · rw [hR] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    have hc' : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact hu0 (zero_smul _ _))
    rw [map_smul, smul_eq_mul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D hD C₀]
    exact mul_neg_of_pos_of_neg hc' (by exact_mod_cast hneg C₀ hC₀)
  · refine
      { isNormalVariety_source := ⟨hf.isVariety_source, inferInstance⟩
        isNormalVariety_target := ⟨hf.isVariety_target, inferInstance⟩
        comp_eq := hfs
        isProjectiveMorphism := hfp
        surjective := (hf.toIsBirationalContraction.surjective_and_isBirational).1.surj
        isIso_app := hf.isIso_app
        isContractedBy_iff := fun C => ⟨fun hC => ?_, fun hCR => ?_⟩ }
    · exact ⟨C.relativeClass f hC, subset_closure (relativeClass_mem_relativeConeOfCurves hC), rfl⟩
    · rw [hR] at hCR
      obtain ⟨c, -, hc⟩ := hCR
      obtain ⟨HV, hHV, hHVa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hV
      haveI := hHV
      refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hfs HV hHVa C ?_
      have h1 := congrArg (NumericalCurveClasses.degree sX ((Scheme.Modules.pullback f).obj HV))
        hc
      rw [map_smul, smul_eq_mul, NumericalCurveClasses.degree_numericalClass,
        NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, OneCycle.degree_cycle,
        ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hfs C₀ hC₀] at h1
      have h2 : ((C.degree k ((Scheme.Modules.pullback f).obj HV) : ℤ) : ℝ) = 0 := by
        rw [← h1]
        simp
      exact_mod_cast h2

/-! ### The main theorem -/

private theorem solution
    {X V : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian V] [IsNormal V]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : MMP.Fourfold.IsQFactorial sX)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    {K : MMP.Mori.Divisor X} {B H : MMP.Mori.QDivisor X} (hB : 0 ≤ B)
    (hklt : MMP.Mori.IsKltPair sX 3 K B)
    (hH : 0 ≤ H) (hHC : H.IsQCartier)
    {f : X ⟶ V} (hf : MMP.Flips.IsSmall ℂ sV sX f) (hfp : IsProjectiveMorphism f)
    (hfi : ¬ IsIso f)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    (htriv : MMP.Flips.IsNumericallyTrivialOver ℂ sX f
      (MMP.Flips.logCanonicalDivisor K (MMP.Mori.QDivisor.toRDivisor B)))
    (hHf : MMP.Flips.IsRelativelyAntiAmple f (MMP.Mori.QDivisor.toRDivisor H)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (_ : CompactSpace Y) (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ V) (ρ : X.RationalMap Y),
      MMP.Flips.IsHFlop ℂ sX sV sY 3 K (MMP.Mori.QDivisor.toRDivisor B) H f g ρ ∧
      MMP.Mori.IsProjectiveVariety ℂ sY ∧ IsProjectiveMorphism g ∧
      MMP.Fourfold.IsQFactorial sY ∧
      (∃ D : MMP.Mori.RDivisor V,
        MMP.Flips.IsRCartierPullback f D
          (MMP.Flips.logCanonicalDivisor K (MMP.Mori.QDivisor.toRDivisor B)) ∧
        MMP.Flips.IsRCartierPullback g D
          (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor ρ K)
            (MMP.Mori.QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ρ B)))) ∧
      MMP.Mori.IsKltPair sY 3 (MMP.Mori.RationalMap.transformDivisor ρ K)
        (MMP.Mori.RationalMap.transformDivisor ρ B) := by
  classical
  -- the base `V`
  have hVv : AlgebraicGeometry.IsVariety ℂ sV := hV.toIsVariety
  haveI : IsIntegral V := hVv.toIsIntegral
  haveI : LocallyOfFiniteType sV := hVv.toLocallyOfFiniteType
  haveI : QuasiCompact sV := hVv.toQuasiCompact
  haveI : IsSeparated sV := hVv.toIsSeparated
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsProper f := hf.isProper
  have hVn : IsNormalVariety ℂ sV := ⟨hVv, inferInstance⟩
  have hXn : IsNormalVariety ℂ sX := hklt.1.1
  have hK : K.IsCanonicalDivisor sX 3 := hklt.1.2.1
  have hfs : f ≫ sV = sX := hf.comp_eq
  have hfb : IsBirationalMorphism f := IsSmall.isBirationalMorphism sV sX hf
  have hR0 : QDivisor.toRDivisor (Divisor.toQDivisor K + B) =
      logCanonicalDivisor K (QDivisor.toRDivisor B) := by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]
    rfl
  -- Step 1: `(X, B)` is klt in the sense of *Flips and abundance*
  have hBbd : IsBoundary (QDivisor.toRDivisor B) := isBoundary_toRDivisor_of_isKltPair hB hklt
  have hkltF : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor B) :=
    (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sX 3 K B hXn hK hBbd hklt.1.2.2).2 hklt
  -- Step 2: a rational `ε > 0` with `(X, B + ε H)` klt
  obtain ⟨ε₀, hε₀, hε₀k⟩ := MMP.Fourfold.exists_pos_forall_isKawamataLogTerminal_add_smul sX 3 K
    B H hkltF (DivisorWithCoeffs.isEffective_iff_nonneg.2 hH) hHC
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℚ, (0 : ℝ) < ε ∧ (ε : ℝ) < ε₀ := exists_rat_btwn hε₀
  have hε' : 0 < ε := by exact_mod_cast hε
  set E : QDivisor X := B + ε • H with hEdef
  have hkltEF : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor E) := by
    rw [hEdef, toRDivisor_add_smul]
    exact hε₀k _ hε.le hεlt
  have hKEQ : (Divisor.toQDivisor K + E).IsQCartier :=
    QDivisor.isQCartier_of_isCartierCombination
      (by rw [map_add, QDivisor.toRDivisor_toQDivisor]; exact hkltEF.2.2.1)
  have hkltE : MMP.Mori.IsKltPair sX 3 K E :=
    (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sX 3 K E hXn hK hkltEF.1.isBoundary
      hKEQ).1 hkltEF
  have hE0 : ∀ P, 0 ≤ E.coeff P := fun P => by
    have := hkltEF.1.isBoundary P
    rw [QDivisor.coeff_toRDivisor] at this
    exact_mod_cast this.1
  have hkltE4 : MMP.Fourfold.IsKltPair sX E :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK
      ⟨inferInstance, inferInstance, hkltE.1.isPair, hE0⟩).2 hkltE
  -- Step 3: `r (K + B) = f^* M` for a Cartier divisor `M` on `V`
  obtain ⟨-, ⟨r, hr, M, -, hMc, ⟨MX, hBX, hMX, hpbX⟩, -⟩, -⟩ :=
    IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne hX hX hV hfs hfs hfb hfb
      hf.exists_isIso hf.exists_isIso hkltF (by rw [hR0]; exact htriv)
  have hneg : ∀ C : ProperCurve sX, C.IsContractedBy f →
      (Divisor.toQDivisor K + E).intersectionNumber ℂ sX C.ι C.dim_le hKEQ < 0 :=
    intersectionNumber_add_smul_neg hfs hr hMc hMX hpbX hHf hε' hKEQ
  -- Step 4: `f` is the contraction of a `(K + B + ε H)`-negative extremal ray
  obtain ⟨m₀, r₀, L₀, hm₀, -, hL₀, -⟩ := id hHf
  obtain ⟨R, hR, hfR⟩ := exists_isNegativeExtremalRayOf_isContractionOfRay hX hV hf hfp hρ
    (hL₀ ⟨0, hm₀⟩) _ hKEQ hneg
  have hsmallf : MMP.Fourfold.IsSmallMorphism sX sV f :=
    ⟨hXn, hVn, hfs, inferInstance, hfb, two_le_closedsCodimension_exceptionalSet_of_isSmall hVn hf⟩
  have hampX : (-(Divisor.toQDivisor K + E)).HasRelativelyAmpleMultiple f := by
    refine hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sV hXn hX hV ⟨3, hK⟩ hKEQ hR.2.1
      (fun v hv hv0 => ?_) f hfs (fun C hC => (hfR.isContractedBy_iff C).1 hC)
    have := hR.2.2 v hv hv0
    simpa only [MMP.Fourfold.QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul] using this
  have hfc : IsFlippingContraction sX sV K E f :=
    ⟨hXn, hVn, hfs, ⟨3, hK⟩, hKEQ, inferInstance, hfb, hsmallf.two_le_codimension, hampX⟩
  -- Step 5: the flip
  obtain ⟨Y, hYc, hYl, hYn, sY, g, hflip⟩ := MMP.Fourfold.exists_isFlip_of_isKltPair sX K E hX
    hK.1 hXQ ⟨3, hK⟩ hkltE4 sV R f hR hfR hfc
  have hYv := hflip.isNormalVariety
  haveI : IsIntegral Y := hYv.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  haveI : QuasiCompact sY := hYv.1.toQuasiCompact
  haveI : IsProper g := hflip.isProper
  have hgs : g ≫ sV = sY := hflip.comp_eq
  have hgb : IsBirationalMorphism g := hflip.isBirationalMorphism
  -- `f⁺` and `X⁺` are projective
  obtain ⟨M₀, hM₀, hM₀a⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨MV, hMV, hMVa⟩ := exists_isAmple_of_isProjectiveMorphism sV M₀ hM₀a hV.isProjective
  have hgp : IsProjectiveMorphism g :=
    isProjectiveMorphism_of_hasRelativelyAmpleMultiple hflip.hasRelativelyAmpleMultiple MV hMVa
  have hY : MMP.Mori.IsProjectiveVariety ℂ sY := by
    refine (AlgebraicGeometry.isProjectiveVariety_iff ℂ sY).2 ⟨hYv.1, ?_⟩
    rw [← hgs]
    exact hgp.comp hV.isProjective
  have hgsmall : IsSmall ℂ sV sY g :=
    isSmall_of_two_le_closedsCodimension_exceptionalSet hYv hVn hgs hgb hflip.two_le_codimension
  -- the flip as a rational map
  obtain ⟨ρ, hρb, hρc⟩ := exists_isBirational_compHom_eq (sV := sV) hfb hgb
  have hρf : IsFlipRationalMap sX sV sY K E f g ρ := ⟨hflip, hρc⟩
  have htr : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      RationalMap.transformDivisor ρ D = flipTransform f g D :=
    fun D => hρf.transformDivisor_eq_flipTransform D
  -- Step 6: `X⁺` is `ℚ`-factorial
  have hDf : flipTransform f g (Divisor.toQDivisor K + E) =
      Divisor.toQDivisor (flipTransform f g K) + flipTransform f g E := by
    rw [map_add, flipTransform_toQDivisor]
  have hflipOf : MMP.Fourfold.IsFlipOf sX sV sY (Divisor.toQDivisor K + E) f g :=
    { isQCartier := hKEQ
      isContraction := hfR.toIsContraction
      isSmallMorphism := hsmallf
      hasRelativelyAmpleMultiple := hampX
      isSmallMorphism_flip := ⟨hYv, hVn, hgs, inferInstance, hgb, hflip.two_le_codimension⟩
      isProjectiveMorphism_flip := hgp
      isQCartier_flip := hDf ▸ hflip.isQCartier
      hasRelativelyAmpleMultiple_flip := hDf ▸ hflip.hasRelativelyAmpleMultiple }
  have hYQ : MMP.Fourfold.IsQFactorial sY :=
    (MMP.Fourfold.IsKltPair.isQFactorial_of_isContractionOfRay hkltE4 hX hXQ ⟨3, hK⟩ hR hfR
      hfb).2 Y sY g hflipOf
  -- Step 7: the trivial-flop bundle on `f` and `f⁺`
  obtain ⟨-, ⟨r', hr', M', -, hM'c, ⟨MX', hBX', hMX', hpbX'⟩, ⟨MY, hBY, hMY, hpbY⟩⟩, hkltY, -⟩ :=
    IsKawamataLogTerminal.exists_isPullback_of_isIsoInCodimOne hX hY hV hfs hgs hfb hgb
      hf.exists_isIso hgsmall.exists_isIso hkltF (by rw [hR0]; exact htriv)
  have hKρ : RationalMap.transformDivisor ρ K =
      inverseTransformDivisor g (RationalMap.transformDivisor f.toRationalMap K) := htr K
  have hBρ : RationalMap.transformDivisor ρ B = inverseTransformDivisor g (flopBaseDivisor f B) :=
    htr B
  have hMYc : MY.IsCartier := hpbY.isCartier hM'c
  -- crepancy: `K + B` and its transform are pulled back from `r'⁻¹ M'`
  have hcrep : ∃ D : RDivisor V,
      IsRCartierPullback f D (logCanonicalDivisor K (QDivisor.toRDivisor B)) ∧
      IsRCartierPullback g D (logCanonicalDivisor (RationalMap.transformDivisor ρ K)
        (QDivisor.toRDivisor (RationalMap.transformDivisor ρ B))) := by
    refine ⟨(r' : ℝ)⁻¹ • Divisor.toRDivisor M', ⟨1, fun _ => (r' : ℝ)⁻¹, fun _ => M',
      fun _ => MX', fun _ => hM'c, by simp, fun _ => ⟨hBX', hpbX'⟩, ?_⟩, ⟨1, fun _ => (r' : ℝ)⁻¹,
      fun _ => M', fun _ => MY, fun _ => hM'c, by simp, fun _ => ⟨hBY, hpbY⟩, ?_⟩⟩
    · rw [Fin.sum_univ_one, logCanonicalDivisor_toRDivisor]
      exact toRDivisor_eq_inv_natCast_smul hr' hMX'
    · rw [Fin.sum_univ_one, logCanonicalDivisor_toRDivisor, hKρ, hBρ]
      exact toRDivisor_eq_inv_natCast_smul hr' hMY
  -- `(X⁺, B⁺)` is klt
  have hkltYM : MMP.Mori.IsKltPair sY 3 (RationalMap.transformDivisor ρ K)
      (RationalMap.transformDivisor ρ B) := by
    rw [hKρ, hBρ]
    have hQY : (Divisor.toQDivisor
        (inverseTransformDivisor g (RationalMap.transformDivisor f.toRationalMap K)) +
          inverseTransformDivisor g (flopBaseDivisor f B)).IsQCartier :=
      QDivisor.isQCartier_iff_exists_pos.mpr ⟨r', hr', MY, hMY, hMYc⟩
    exact (MMP.Fourfold.isKawamataLogTerminal_iff_isKltPair sY 3 _ _ hYv hkltY.2.1
      hkltY.1.isBoundary hQY).1 hkltY
  -- Step 8: the flip of `f` for `K + B + ε H` is the `H`-flop
  have hτ : RationalMap.transformDivisor ρ (logCanonicalDivisor K (QDivisor.toRDivisor E)) =
      QDivisor.toRDivisor (Divisor.toQDivisor (flipTransform f g K) + flipTransform f g E) := by
    rw [logCanonicalDivisor_toRDivisor, transformDivisor_toRDivisor, htr, hDf]
  have hlogflip : IsLogFlip ℂ sX sV sY 3 K (QDivisor.toRDivisor E) f g ρ := by
    refine ⟨hkltEF.1, hK, ?_⟩
    exact
      { isNormalVariety_source := hXn
        isNormalVariety_target := hVn
        isNormalVariety_flip := hYv
        isContraction := hf.toIsContraction
        isCartierCombination := hkltEF.2.2.1
        isRelativelyAntiAmple := by
          change IsRelativelyAmple f (-(logCanonicalDivisor K (QDivisor.toRDivisor E)))
          rw [logCanonicalDivisor_toRDivisor, ← map_neg]
          exact hampX.isRelativelyAmple_toRDivisor
        isProper := inferInstance
        isModificationOf := ⟨hρb, hρc⟩
        isMorphismInCodimOne := RationalMap.isMorphismInCodimOne_of_isOver hXn f g ρ hρc
        isSmall := hgsmall
        isCartierCombination_transform := by
          rw [hτ]
          exact isCartierCombination_toRDivisor_of_isQCartier hflip.isQCartier
        isRelativelyAmple_transform := by
          rw [hτ]
          exact hflip.hasRelativelyAmpleMultiple.isRelativelyAmple_toRDivisor
        isSmall_source := hf }
  have hHF : IsHFlop ℂ sX sV sY 3 K (QDivisor.toRDivisor B) H f g ρ :=
    (IsHFlop.iff_isLogFlip_add_smul hX hV hkltF hH hHC hf htriv hHf hε' hkltEF hgsmall
      (IsProjectiveMorphism.isProjective hgp) ρ).2 hlogflip
  exact ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, sY, g, ρ, hHF, hY, hgp,
    hYQ, hcrep, hkltYM⟩

end Proof_lem_fourfold_projective_effective_divisor_flop_exists

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-- **Existence of projective `H`-flops of klt threefolds.** Let `(X, B)` be a klt pair
(`MMP.Mori.IsKltPair`, canonical divisor `K` of dimension `3`) with `B ≥ 0` a `ℚ`-divisor, on a
projective `ℚ`-factorial complex variety `X`, and let `H ≥ 0` be a `ℚ`-Cartier `ℚ`-divisor. Let
`f : X ⟶ V` be a small (`MMP.Flips.IsSmall`) projective contraction onto a normal projective
variety, not an isomorphism, with `ρ(X/V) = 1`, `K + B` numerically `f`-trivial and `-H`
`f`-ample. Then there are a projective `ℚ`-factorial variety `X⁺`, a projective morphism
`f⁺ : X⁺ ⟶ V` and a birational map `ρ : X ⤏ X⁺` forming an `H`-flop of `f` with respect to
`K + B` (`MMP.Flips.IsHFlop`), such that `K + B` and `ρ_* K + ρ_* B` are the pull-backs along `f`
and `f⁺` of one `ℝ`-Cartier divisor on `V`, and `(X⁺, ρ_* B)` is klt with canonical divisor
`ρ_* K`. -/
@[mmp "lem_fourfold_projective_effective_divisor_flop_exists"]
public theorem exists_isHFlop_of_isKltPair
    {X V : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian V] [IsNormal V]
    (hX : Mori.IsProjectiveVariety ℂ sX) (hXQ : MMP.Fourfold.IsQFactorial sX)
    (hV : Mori.IsProjectiveVariety ℂ sV)
    {K : Divisor X} {B H : QDivisor X} (hB : 0 ≤ B) (hklt : MMP.Mori.IsKltPair sX 3 K B)
    (hH : 0 ≤ H) (hHC : H.IsQCartier)
    {f : X ⟶ V} (hf : IsSmall ℂ sV sX f) (hfp : IsProjectiveMorphism f) (hfi : ¬ IsIso f)
    (hρ : relativePicardNumber sX f = 1)
    (htriv : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K (QDivisor.toRDivisor B)))
    (hHf : IsRelativelyAntiAmple f (QDivisor.toRDivisor H)) :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (_ : IsNormal Y)
      (_ : CompactSpace Y) (sY : Y ⟶ Spec (.of ℂ)) (g : Y ⟶ V) (ρ : X.RationalMap Y),
      IsHFlop ℂ sX sV sY 3 K (QDivisor.toRDivisor B) H f g ρ ∧
      Mori.IsProjectiveVariety ℂ sY ∧ IsProjectiveMorphism g ∧ MMP.Fourfold.IsQFactorial sY ∧
      (∃ D : RDivisor V, IsRCartierPullback f D (logCanonicalDivisor K (QDivisor.toRDivisor B)) ∧
        IsRCartierPullback g D (logCanonicalDivisor (Mori.RationalMap.transformDivisor ρ K)
          (QDivisor.toRDivisor (Mori.RationalMap.transformDivisor ρ B)))) ∧
      MMP.Mori.IsKltPair sY 3 (Mori.RationalMap.transformDivisor ρ K)
        (Mori.RationalMap.transformDivisor ρ B) :=
          by revert X V sX sV hX hXQ hV K B H hB hklt hH hHC f hf hfp hfi hρ htriv hHf; exact Proof_lem_fourfold_projective_effective_divisor_flop_exists.solution

end MMP.Flips
