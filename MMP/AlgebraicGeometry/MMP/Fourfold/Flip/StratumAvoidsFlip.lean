module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
public import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalFlips
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
public import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
public import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
public import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
public import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelProperties
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Singularities.Basic

/-!
# A fixed adjunction stratum avoids the flipping locus

An adjunction stratum of a projective dlt pair that the flip carries isomorphically onto its
flipped counterpart is disjoint from the exceptional sets of both contractions of the flip.

## Main results

* `MMP.Fourfold.IsAdjunctionStep.sub_single_nonneg`: for an adjunction step onto `P` from an
  effective boundary `B_S`, the divisor `B_S - P` is effective with coefficient zero at `P`.
* `MMP.Fourfold.IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair`: a fixed projective
  adjunction stratum lies in the isomorphism locus of a flip.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP MMP.Mori MMP.Fourfold

namespace MMP.Fourfold

/-- For an adjunction step `T ⊂ S` onto the prime divisor `P` from an effective boundary `B_S`,
the divisor `B_S - P` is effective and has coefficient zero at `P`. -/
theorem IsAdjunctionStep.sub_single_nonneg {k : Type} [Field k] {S T : Scheme.{0}}
    {sS : S ⟶ Spec (.of k)} {BS : QDivisor S} {j : T ⟶ S} {BT : QDivisor T}
    (hj : IsAdjunctionStep sS BS j BT) (hBS0 : ∀ Q, 0 ≤ BS.coeff Q)
    {P : MMP.Mori.PrimeDivisor S} (hPr : Set.range j.base = (P.support : Set S)) :
    0 ≤ BS - Finsupp.single P 1 ∧ (BS - Finsupp.single P 1).coeff P = 0 := by
  classical
  have h1 := hj.coeff_eq_one hPr
  refine ⟨fun Q => ?_, ?_⟩
  · change (0 : ℚ) ≤ BS.coeff Q - (Finsupp.single P (1 : ℚ) : QDivisor S) Q
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h; rw [h1]; norm_num
    · linarith [hBS0 Q]
  · rw [DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_single_self, h1, sub_self]

end MMP.Fourfold

namespace MMP.Fourfold.StratumAvoidsFlip

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### `IsFlipOf` as a flip in the sense of *Flips and abundance* -/

section FlipOfAsFlip

variable {k : Type} [Field k]

/-- If `L = m D` with `m ≠ 0`, then `D = m⁻¹ L` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_smul {X : Scheme.{0}} {D : QDivisor X} {m : ℤ} (hm : m ≠ 0)
    {L : Divisor X} (hL : Divisor.toQDivisor L = m • D) :
    QDivisor.toRDivisor D = ((m : ℝ)⁻¹) • Divisor.toRDivisor L := by
  ext E
  have h := congrArg (fun D : QDivisor X => D.coeff E) hL
  simp only [Divisor.coeff_toQDivisor] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  rw [mul_comm]
  exact_mod_cast h.symm

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact toRDivisor_eq_inv_smul hm hL⟩

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f] {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) :
    MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have := hL.isInvertibleModule_divisorialSheaf
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => ⟨hL, fun U hU =>
      (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
        inferInstance hamp).2 U hU⟩, ?_⟩
  rw [Fin.sum_univ_one]
  exact toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

private theorem isSeparated_toTerminal {X : Scheme.{0}} {s : X ⟶ Spec (.of k)}
    [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  have : (X ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- A small morphism with `𝒪_Z ≅ f_* 𝒪_X` is a small birational contraction. -/
private theorem isSmall_of_isSmallMorphism {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (happ : ∀ U : Z.Opens, IsIso (f.app U)) : MMP.Flips.IsSmall k sZ sX f := by
  have := hf.isNormalVariety_target.2
  have := hf.isProper
  have := hf.isNormalVariety_source.1
  have := hf.isNormalVariety_target.1
  have hbc : MMP.Flips.IsBirationalContraction k sZ sX f :=
    { isVariety_target := hf.isNormalVariety_target.1
      isVariety_source := hf.isNormalVariety_source.1
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isIso_app := happ
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
        hf.isBirationalMorphism).symm }
  refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  have h := hf.two_le_codimension
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h ⊢
  intro x hx
  refine h x fun hx' => hx ⟨f ⁻¹ᵁ biregularLocus f, by simpa [exceptionalSet] using hx', ?_⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

section Transforms

variable {X Y Z : Scheme.{0}}

/-- A morphism whose exceptional set has codimension at least two is biregular over the image of
the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus' {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f := by
  by_contra h
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (x := P.genericPoint) h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- Extending a composite `φ₂ ∘ φ₁` of partial maps on prime divisors linearly is composing the
linear extensions. -/
private theorem mapPrimeDivisors_bind {R : Type*} [AddCommMonoid R]
    (φ₁ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y))
    (φ₂ : Mori.PrimeDivisor Y → Option (Mori.PrimeDivisor Z)) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors (fun P => (φ₁ P).bind φ₂) D =
      DivisorWithCoeffs.mapPrimeDivisors φ₂ (DivisorWithCoeffs.mapPrimeDivisors φ₁ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ₁ E with
    | none => simp
    | some E' => simp [DivisorWithCoeffs.mapPrimeDivisors_single]

private theorem coe_transform_eq_closure_singleton [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If a representative `g'` of `φ` is defined at `η_P` and `φ_* P = E`, then `g'(η_P) = η_E`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If a representative `g'` of `φ` sends `η_P` to `η_E`, then `φ_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ V) ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ V).ι.continuous

/-- If `g` maps `η_E` to `η_D` inside its biregular locus, then `g⁻¹_* D = E`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_map_genericPoint {g : X ⟶ Y}
    {D : Mori.PrimeDivisor Y} {E : Mori.PrimeDivisor X}
    (hη : g E.genericPoint = D.genericPoint) (hV : g E.genericPoint ∈ biregularLocus g) :
    inverseTransformPrimeDivisor g D = some E := by
  have hDmem : D.genericPoint ∈ D.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hEmem : E.genericPoint ∈ (g ⁻¹' ((D.idealSheaf.support : Set Y) ∩ biregularLocus g)) :=
    ⟨hη ▸ hDmem, hV⟩
  have hsupp : E.idealSheaf.support = inverseTransform g D.idealSheaf.support := by
    apply TopologicalSpace.Closeds.ext
    change (E.support : Set X) = closure _
    apply subset_antisymm
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono (Set.singleton_subset_iff.mpr hEmem)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal ?_ isClosed_closure
      rintro w ⟨hwD, hwV⟩
      have hDw : D.genericPoint ⤳ g w := by
        have : g w ∈ D.support := hwD
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
        exact specializes_iff_mem_closure.mpr this
      rw [← hη] at hDw
      exact specializes_iff_mem_closure.mp
        (specializes_of_map_specializes hV hwV hDw)
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨D.genericPoint, hDmem, hη ▸ hV⟩, ?_⟩
  have := E.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp

/-- A representative `ψ` of a rational map `φ` over `f` and `g` satisfies `ψ ≫ g = f`. -/
private theorem hom_comp_eq_of_isOver [IsReduced X] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y} (hφ : Flips.RationalMap.IsOver f g φ)
    (ψ : X.PartialMap Y) (hψ : ψ.toRationalMap = φ) : ψ.hom ≫ g = ψ.domain.ι ≫ f := by
  have h1 : (ψ.compHom g).toRationalMap = f.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hψ]
    exact hφ
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)

private theorem hom_apply_eq_of_comp_eq {ψ : X.PartialMap Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : ψ.hom ≫ g = ψ.domain.ι ≫ f) (x : ψ.domain) : g (ψ.hom x) = f x.1 :=
  congrArg (fun k : ψ.domain.toScheme ⟶ Z => k x) h

/-- Two morphisms with the same composite with `g`, both landing over the biregular locus of `g`,
are equal. -/
private theorem eq_of_comp_eq_of_mem_biregularLocus {W : Scheme.{0}} (g : Y ⟶ Z) {a b : W ⟶ Y}
    {h : W ⟶ Z} (ha' : a ≫ g = h) (hb' : b ≫ g = h) (hh : ∀ w, h w ∈ biregularLocus g) :
    a = b := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hab : a ≫ g = b ≫ g := ha'.trans hb'.symm
  have ha : ∀ w, g (a w) ∈ biregularLocus g := fun w => by
    rw [← Scheme.Hom.comp_apply, ha']; exact hh w
  have hb : ∀ w, g (b w) ∈ biregularLocus g := fun w => by
    rw [← Scheme.Hom.comp_apply, hb']; exact hh w
  have hra : Set.range a ⊆ Set.range (g ⁻¹ᵁ biregularLocus g).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ha w
  have hrb : Set.range b ⊆ Set.range (g ⁻¹ᵁ biregularLocus g).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hb w
  rw [← IsOpenImmersion.lift_fac (g ⁻¹ᵁ biregularLocus g).ι a hra,
    ← IsOpenImmersion.lift_fac (g ⁻¹ᵁ biregularLocus g).ι b hrb]
  congr 1
  rw [← cancel_mono (g ∣_ biregularLocus g), ← cancel_mono (biregularLocus g).ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, hab]

/-- The partial map `g⁻¹ ∘ f`, defined on `f⁻¹(V_g)` for the biregular locus `V_g` of `g`. -/
private noncomputable def partialMapOverBiregularLocus [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty) :
    X.PartialMap Y where
  domain := f ⁻¹ᵁ biregularLocus g
  dense_domain := (f ⁻¹ᵁ biregularLocus g).2.dense hne
  hom := haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
    (f ∣_ biregularLocus g) ≫ inv (g ∣_ biregularLocus g) ≫ (g ⁻¹ᵁ biregularLocus g).ι

private theorem partialMapOverBiregularLocus_hom_comp [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty) :
    (partialMapOverBiregularLocus f g hne).hom ≫ g =
      (partialMapOverBiregularLocus f g hne).domain.ι ≫ f := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  change ((f ∣_ biregularLocus g) ≫ inv (g ∣_ biregularLocus g) ≫
    (g ⁻¹ᵁ biregularLocus g).ι) ≫ g = (f ⁻¹ᵁ biregularLocus g).ι ≫ f
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    morphismRestrict_ι]

private theorem partialMapOverBiregularLocus_hom_mem [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty)
    (x : (partialMapOverBiregularLocus f g hne).domain) :
    (partialMapOverBiregularLocus f g hne).hom x ∈ g ⁻¹ᵁ biregularLocus g := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  exact (inv (g ∣_ biregularLocus g) ((f ∣_ biregularLocus g) x)).2

end Transforms

/-- The birational map `(f⁺)⁻¹ ∘ f`, composed of partial isomorphisms representing the birational
morphisms `f` and `f⁺`, is a modification of `f` into `f⁺`. -/
private theorem exists_isModificationOf {Xm Xp Z : Scheme.{0}} [IsReduced Xm] [IsReduced Xp]
    {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hm : IsBirationalMorphism fm) (hp : IsBirationalMorphism fp) :
    ∃ φ : Xm.RationalMap Xp, MMP.Flips.IsModificationOf fm fp φ := by
  obtain ⟨em, hm⟩ := hm
  obtain ⟨ep, hp⟩ := hp
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em fm (𝟙 Z) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 Z) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver fm fp := h1.trans h2.symm
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change Xm.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
    Xm.homOfLE (le_top : e.source ≤ ⊤) ≫ Xm.topIso.hom ≫ fm
  rw [Category.assoc, H]
  simp

/-- For a small `f`, the birational transform of divisors under a modification `φ` of `f` into
`f⁺` is the strict transform `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_eq_flipTransform_of_isModificationOf {Xm Xp Z : Scheme.{0}}
    [IsIntegral Xm] {sZ : Z ⟶ Spec (.of k)} {sXp : Xp ⟶ Spec (.of k)} [IsSeparated sZ]
    [IsSeparated sXp] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hm2 : 2 ≤ closedsCodimension (exceptionalSet fm))
    (hp2 : 2 ≤ closedsCodimension (exceptionalSet fp))
    {φ : Xm.RationalMap Xp} (hφ : MMP.Flips.IsModificationOf fm fp φ)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    Mori.RationalMap.transformDivisor φ D = flipTransform fm fp D := by
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have : IsSeparated (Xp ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sXp)
  have hpt : ∀ P : Mori.PrimeDivisor Xm, Mori.RationalMap.transformPrimeDivisor φ P =
      (Mori.RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap P).bind
        (inverseTransformPrimeDivisor fp) := by
    intro P
    have hcoh : Order.coheight (fm P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fm
        (map_genericPoint_mem_biregularLocus' hm2 P),
        P.coheight_genericPoint]
    set Q : Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
    have hQ : fm P.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm P Q).mpr hQ,
      Option.bind_some]
    by_cases hV : Q.genericPoint ∈ biregularLocus fp
    · have hPU : P.genericPoint ∈ fm ⁻¹ᵁ biregularLocus fp :=
        show fm P.genericPoint ∈ biregularLocus fp from hQ ▸ hV
      set g' := partialMapOverBiregularLocus fm fp ⟨_, hPU⟩
      have hg' : g'.toRationalMap = φ := by
        obtain ⟨ψ, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective φ
        have hψ := hom_comp_eq_of_isOver hφ.2 ψ rfl
        have hg := partialMapOverBiregularLocus_hom_comp fm fp ⟨_, hPU⟩
        rw [Scheme.PartialMap.toRationalMap_eq_iff]
        refine ⟨g'.domain ⊓ ψ.domain,
          g'.dense_domain.inter_of_isOpen_left ψ.dense_domain g'.domain.2, inf_le_left,
          inf_le_right, ?_⟩
        have key : ∀ (U : Xm.Opens) (hWU : g'.domain ⊓ ψ.domain ≤ U) (c : U.toScheme ⟶ Xp),
            c ≫ fp = U.ι ≫ fm → (Xm.homOfLE hWU ≫ c) ≫ fp = (g'.domain ⊓ ψ.domain).ι ≫ fm :=
          fun U hWU c hc => by rw [Category.assoc, hc, Scheme.homOfLE_ι_assoc]
        refine eq_of_comp_eq_of_mem_biregularLocus fp (key _ inf_le_left _ hg)
          (key _ inf_le_right _ hψ) fun w => w.2.1
      set y := g'.hom ⟨P.genericPoint, hPU⟩
      have hyQ : fp y = Q.genericPoint :=
        (hom_apply_eq_of_comp_eq (partialMapOverBiregularLocus_hom_comp fm fp ⟨_, hPU⟩)
          ⟨P.genericPoint, hPU⟩).trans hQ
      have hyV : y ∈ fp ⁻¹ᵁ biregularLocus fp := partialMapOverBiregularLocus_hom_mem _ _ _ _
      have hcy : Order.coheight y = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hyV, hyQ,
          Q.coheight_genericPoint]
      set P' : Mori.PrimeDivisor Xp := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
      have hP' : y = P'.genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy).symm
      rw [inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (E := P') (hP' ▸ hyQ)
        (hP' ▸ hyV)]
      exact transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hPU hP'.symm
    · have hnone : inverseTransformPrimeDivisor fp Q = none := by
        rw [inverseTransformPrimeDivisor_eq_none_iff]
        rintro ⟨⟨z, hzQ, hzV⟩, -⟩
        have hz : Q.genericPoint ⤳ z := by
          have : z ∈ Q.support := hzQ
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
          exact specializes_iff_mem_closure.mpr this
        exact hV (hz.mem_open (biregularLocus fp).2 hzV)
      rw [hnone, Mori.RationalMap.transformPrimeDivisor_eq_none_iff]
      rintro ⟨hdef, E, hE⟩
      have hsome : Mori.RationalMap.transformPrimeDivisor φ P = some E :=
        Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr ⟨hdef, hE⟩
      obtain ⟨ψ, hPψ, hψ⟩ := Mori.RationalMap.definedAt_iff.mp hdef
      have hηE := genericPoint_eq_of_transformPrimeDivisor_eq_some hsome ψ hψ hPψ
      have h1 : fp E.genericPoint = Q.genericPoint := by
        rw [hηE]
        exact (hom_apply_eq_of_comp_eq (hom_comp_eq_of_isOver hφ.2 ψ hψ)
          ⟨P.genericPoint, hPψ⟩).trans hQ
      exact hV (h1 ▸ map_genericPoint_mem_biregularLocus'
        hp2 E)
  change DivisorWithCoeffs.mapPrimeDivisors _ D = inverseTransformDivisor fp
    (Mori.RationalMap.transformDivisor (X := Xm) fm.toRationalMap D)
  rw [funext hpt]
  exact mapPrimeDivisors_bind _ _ D

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {X Y : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y))
    (f : R →+ S) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X Y X' : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- **A flip is an isomorphism over the biregular locus of the flipping contraction**:
`V_f ⊆ V_{f⁺}` for a `D`-flip `f⁺` of `f` (`MMP.Fourfold.IsFlipOf`). -/
private theorem biregularLocus_le_of_isFlipOf {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {D : QDivisor X} {f : X ⟶ Z}
    {fp : X' ⟶ Z} (h : IsFlipOf sX sZ sX' D f fp) : biregularLocus f ≤ biregularLocus fp := by
  have hc := h.isContraction
  have hs := h.isSmallMorphism
  have hsp := h.isSmallMorphism_flip
  have := hs.isProper
  have := hsp.isProper
  have : IsSeparated sZ := hc.isNormalVariety_target.1.toIsSeparated
  have : IsSeparated sX' := hsp.isNormalVariety_source.1.toIsSeparated
  obtain ⟨g, hg⟩ := exists_isModificationOf (sZ := sZ) hs.isBirationalMorphism
    hsp.isBirationalMorphism
  have htr : Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (flipTransform f fp D) := by
    rw [transformDivisor_eq_flipTransform_of_isModificationOf (sZ := sZ) (sXp := sX')
      hs.two_le_codimension hsp.two_le_codimension hg]
    simp only [QDivisor.toRDivisor, flipTransform_mapCoeffsAddMonoidHom]
  have happ := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX' sZ
    hsp.isNormalVariety_source.1 hc.isNormalVariety_target fp hsp.isBirationalMorphism).1
  have hF : MMP.Flips.IsFlip k sX sZ sX' (QDivisor.toRDivisor D) f fp g :=
    { isNormalVariety_source := hc.isNormalVariety_source
      isNormalVariety_target := hc.isNormalVariety_target
      isNormalVariety_flip := hsp.isNormalVariety_source
      isContraction :=
        { isVariety_target := hc.isNormalVariety_target.1
          isVariety_source := hc.isNormalVariety_source.1
          comp_eq := hc.comp_eq
          isProper := inferInstance
          isIso_app := hc.isIso_app }
      isCartierCombination := isCartierCombination_toRDivisor h.isQCartier
      isRelativelyAntiAmple := by
        rw [MMP.Flips.IsRelativelyAntiAmple, ← map_neg]
        exact isRelativelyAmple_toRDivisor h.hasRelativelyAmpleMultiple
      isProper := inferInstance
      isModificationOf := hg
      isMorphismInCodimOne :=
        MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hc.isNormalVariety_source f fp g hg.2
      isSmall := isSmall_of_isSmallMorphism hsp happ
      isCartierCombination_transform := by
        rw [htr]; exact isCartierCombination_toRDivisor h.isQCartier_flip
      isRelativelyAmple_transform := by
        rw [htr]; exact isRelativelyAmple_toRDivisor h.hasRelativelyAmpleMultiple_flip
      isSmall_source := isSmall_of_isSmallMorphism hs hc.isIso_app }
  have : IsIso (fp ∣_ biregularLocus f) :=
    hF.isIso_morphismRestrict_of_disjoint_image_exceptionalSet h.isQCartier _ (by
      rw [Set.disjoint_left]
      rintro _ hzV ⟨y, hy, rfl⟩
      have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
      refine hy ⟨f ⁻¹ᵁ biregularLocus f, hzV, ?_⟩
      rw [← morphismRestrict_ι]
      infer_instance)
  exact le_biregularLocus this

end FlipOfAsFlip

/-- If `ι ≫ f = φ ≫ ι' ≫ f⁺` for an isomorphism `φ : S ≅ S'` and `f`, `f⁺` have the same
biregular locus in `Z`, then `ι(S)` misses `Ex(f)` exactly when `ι'(S')` misses `Ex(f⁺)`; here
the direction from `S` to `S'`. -/
private theorem disjoint_range_exceptionalSet_of_comp_eq {S S' X X' Z : Scheme.{0}}
    {ι : S ⟶ X} {ι' : S' ⟶ X'} {f : X ⟶ Z} {fp : X' ⟶ Z} (φ : S ≅ S')
    (hφ : ι ≫ f = φ.hom ≫ ι' ≫ fp) (hV : biregularLocus f ≤ biregularLocus fp)
    (h : Disjoint (Set.range ι.base) (exceptionalSet f : Set X)) :
    Disjoint (Set.range ι'.base) (exceptionalSet fp : Set X') := by
  rw [Set.disjoint_left]
  rintro _ ⟨s', rfl⟩ hy
  refine Set.disjoint_left.mp h ⟨φ.inv s', rfl⟩ ?_
  have he : f (ι (φ.inv s')) = fp (ι' s') := by
    have := congrArg (fun g : S ⟶ Z => g (φ.inv s')) hφ
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, ← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]; rfl
  change f (ι (φ.inv s')) ∉ biregularLocus f
  intro hmem
  have h' : fp (ι' s') ∈ biregularLocus fp := he ▸ hV hmem
  exact hy h'

/-- The strict transform `(f⁺)⁻¹_* f_*` of the `ℚ`-divisor of a divisor `K` is the `ℚ`-divisor
of its strict transform. -/
private theorem flipTransform_toQDivisor {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (K : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor K) = Divisor.toQDivisor (flipTransform f fp K) :=
  flipTransform_mapCoeffsAddMonoidHom f fp (Int.castAddHom ℚ) K

/-- A `(K + B)`-flip in the sense of `MMP.Fourfold.IsFlipOf` is a `(K + B)`-flip in the sense of
`MMP.Mori.IsFlip`. -/
private theorem isFlip_of_isFlipOf {k : Type} [Field k] {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hK : K.IsCanonicalDivisor sX n) (h : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp) :
    Mori.IsFlip sX sZ sX' K B f fp := by
  have hc := h.isContraction
  have hs := h.isSmallMorphism
  have hsp := h.isSmallMorphism_flip
  have htr : Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B =
      flipTransform f fp (Divisor.toQDivisor K + B) := by
    rw [map_add, flipTransform_toQDivisor]
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := hc.isNormalVariety_source
          isNormalVariety_target := hc.isNormalVariety_target
          comp_eq := hc.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := h.isQCartier
          isProper := hs.isProper
          isBirationalMorphism := hs.isBirationalMorphism
          two_le_codimension := hs.two_le_codimension
          hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple }
      isNormalVariety := hsp.isNormalVariety_source
      comp_eq := hsp.comp_eq
      isProper := hsp.isProper
      isBirationalMorphism := hsp.isBirationalMorphism
      isQCartier := htr ▸ h.isQCartier_flip
      hasRelativelyAmpleMultiple := htr ▸ h.hasRelativelyAmpleMultiple_flip
      two_le_codimension := hsp.two_le_codimension }

/-! ### A common normal model of a flip -/

section CommonModel

variable {k : Type} [Field k]

/-- **A common smooth model.** For proper birational morphisms `f : X ⟶ Z`, `f⁺ : X⁺ ⟶ Z` from
normal varieties over a field of characteristic zero to a separated `k`-scheme there are a normal
variety `W` with regular local rings and proper birational morphisms `p : W ⟶ X`, `q : W ⟶ X⁺`
with `p ≫ f = q ≫ f⁺`. -/
private theorem exists_commonModel [CharZero k] {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ]
    (hX : IsNormalVariety k sX) (hX' : IsNormalVariety k sX') {f : X ⟶ Z} {fp : X' ⟶ Z}
    [IsProper f] [IsProper fp] (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) :
    ∃ (W : Scheme.{0}) (p : W ⟶ X) (q : W ⟶ X'), IsNormalVariety k (p ≫ sX) ∧ IsProper p ∧
      IsProper q ∧ IsBirationalMorphism p ∧ IsBirationalMorphism q ∧ p ≫ f = q ≫ fp ∧
      ∀ w : W, IsRegularLocalRing (W.presheaf.stalk w) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral X' := hX'.1.toIsIntegral
  obtain ⟨φ, hφ⟩ := exists_isModificationOf (sZ := sZ) hf hfp
  obtain ⟨W₀, p₀, q₀, hW₀, hp₀, hq₀, hpb₀, hqb₀, -, hcomm⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism hX hX' f fp φ hφ.1 hφ.2
  obtain ⟨W, r, hr⟩ := MMP.Mori.exists_isLogResolution (p₀ ≫ sX) hW₀ 0
  have hrs := hr.toIsSmoothResolution
  obtain ⟨hWv, -, -⟩ := hrs.isNormalVariety hW₀
  have : IsIntegral W₀ := hW₀.1.toIsIntegral
  have : IsIntegral W := hWv.1.toIsIntegral
  have := hrs.isProper
  have := hp₀
  have := hq₀
  refine ⟨W, r ≫ p₀, r ≫ q₀, by rw [Category.assoc]; exact hWv, inferInstance, inferInstance,
    MMP.Mori.isBirationalMorphism_comp hrs.isBirationalMorphism hpb₀,
    MMP.Mori.isBirationalMorphism_comp hrs.isBirationalMorphism hqb₀,
    by rw [Category.assoc, Category.assoc, hcomm], ?_⟩
  have := hWv.1.toLocallyOfFiniteType
  have : Smooth (r ≫ p₀ ≫ sX) :=
    MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hrs.isSmoothScheme
  exact (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
    (r ≫ p₀ ≫ sX)).mp inferInstance

/-- A morphism from a reduced scheme whose image lies in the image of a closed immersion factors
through it. -/
private theorem exists_lift_of_range_subset {X Y S : Scheme.{0}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (g : Y ⟶ X) [QuasiCompact g] [IsReduced Y] (hg : Set.range g ⊆ Set.range ι) :
    ∃ l : Y ⟶ S, l ≫ ι = g := by
  have hrad : g.ker.radical = g.ker := by
    refine Scheme.IdealSheafData.ext (funext fun U => ?_)
    simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
    apply le_antisymm
    · rintro x ⟨n, hn⟩
      rw [RingHom.mem_ker, map_pow] at hn
      rw [RingHom.mem_ker]
      exact IsReduced.eq_zero _ ⟨n, hn⟩
    · exact Ideal.le_radical
  have hsupp : g.ker.support ≤ ι.ker.support := by
    change (g.ker.support : Set X) ⊆ ι.ker.support
    rw [Scheme.Hom.support_ker, Scheme.Hom.support_ker]
    exact closure_mono hg
  have H : ι.ker ≤ g.ker :=
    calc ι.ker ≤ ι.ker.radical := Scheme.IdealSheafData.le_radical _
      _ = Scheme.IdealSheafData.vanishingIdeal ι.ker.support :=
        Scheme.IdealSheafData.vanishingIdeal_support.symm
      _ ≤ Scheme.IdealSheafData.vanishingIdeal g.ker.support :=
        Scheme.IdealSheafData.vanishingIdeal_antimono hsupp
      _ = g.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
      _ = g.ker := hrad
  exact ⟨IsClosedImmersion.lift ι g H, IsClosedImmersion.lift_fac _ _ _⟩

/-- The closure of a point of a scheme, with its reduced structure, is an integral closed
subscheme whose generic point lies over the given point. -/
private theorem exists_isIntegral_closure_singleton {W : Scheme.{0}} (w₀ : W) :
    ∃ (F : Scheme.{0}) (h : F ⟶ W) (_ : IsIntegral F) (_ : IsClosedImmersion h),
      Set.range h = closure {w₀} ∧ h (genericPoint F) = w₀ := by
  set Z : Closeds W := ⟨closure {w₀}, isClosed_closure⟩
  have hZ : IsIrreducible (Z : Set W) := isIrreducible_singleton.closure
  haveI := MMP.Fourfold.isIntegral_subscheme_vanishingIdeal Z hZ
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = closure {w₀} := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  refine ⟨_, (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι, inferInstance, inferInstance,
    hr, ?_⟩
  have h1 := (genericPoint_spec (Scheme.IdealSheafData.vanishingIdeal Z).subscheme).image
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base.hom.continuous
  rw [Set.image_univ, hr, closure_closure] at h1
  exact h1.eq isGenericPoint_closure

/-- **The stratum dominating `S` on a common model.** Let `p : W ⟶ X`, `q : W ⟶ X⁺` satisfy
`p ≫ f = q ≫ f⁺`, and let `φ : S ≅ S⁺` be an isomorphism of integral closed subschemes of `X`,
`X⁺` over `Z` whose generic point lies over the biregular locus of `f⁺`. Then there is an integral
closed subscheme `F` of `W` with a morphism `p_F : F ⟶ S` sending generic point to generic point,
such that `p` restricts to `p_F` and `q` restricts to `p_F ≫ φ`. -/
private theorem exists_dominatingStratum {X X' Z W S S' : Scheme.{0}} [IsIntegral S]
    {f : X ⟶ Z} {fp : X' ⟶ Z} [IsSeparated fp] {p : W ⟶ X} {q : W ⟶ X'} [IsProper p]
    [IsDominant p] (hpq : p ≫ f = q ≫ fp) {ι : S ⟶ X} {ι' : S' ⟶ X'} [IsClosedImmersion ι]
    (φ : S ≅ S') (hφ : ι ≫ f = φ.hom ≫ ι' ≫ fp)
    (hV : f (ι (genericPoint S)) ∈ biregularLocus fp) :
    ∃ (F : Scheme.{0}) (h : F ⟶ W) (pF : F ⟶ S) (_ : IsIntegral F) (_ : IsClosedImmersion h),
      h ≫ p = pF ≫ ι ∧ h ≫ q = pF ≫ φ.hom ≫ ι' ∧ pF (genericPoint F) = genericPoint S := by
  obtain ⟨w₀, hw₀⟩ := p.surjective (ι (genericPoint S))
  obtain ⟨F, h, hFi, hFc, hr, hgen⟩ := exists_isIntegral_closure_singleton w₀
  have hsub : Set.range (h ≫ p) ⊆ Set.range ι := by
    rintro _ ⟨y, rfl⟩
    have hy : h y ∈ closure {w₀} := hr ▸ ⟨y, rfl⟩
    have h1 : w₀ ⤳ h y := specializes_iff_mem_closure.mpr hy
    have h2 : ι (genericPoint S) ⤳ p (h y) := hw₀ ▸ h1.map p.base.hom.continuous
    rw [Scheme.Hom.comp_apply]
    exact h2.mem_closed ι.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  obtain ⟨pF, hpF⟩ := exists_lift_of_range_subset ι (h ≫ p) hsub
  have hpFη : pF (genericPoint F) = genericPoint S := by
    apply ι.isClosedEmbedding.injective
    change (pF ≫ ι) (genericPoint F) = ι (genericPoint S)
    rw [hpF, Scheme.Hom.comp_apply, hgen, hw₀]
  refine ⟨F, h, pF, hFi, hFc, hpF.symm, ?_, hpFη⟩
  have hab : (h ≫ q) ≫ fp = (pF ≫ φ.hom ≫ ι') ≫ fp := by
    simp only [Category.assoc]
    rw [← hpq, ← reassoc_of% hpF, hφ]
  let O : F.Opens := ((h ≫ q) ≫ fp) ⁻¹ᵁ biregularLocus fp
  have hOne : genericPoint F ∈ O := by
    change ((h ≫ q) ≫ fp) (genericPoint F) ∈ biregularLocus fp
    rw [Category.assoc, ← hpq, ← Category.assoc, ← hpF, Category.assoc, Scheme.Hom.comp_apply,
      hpFη]
    exact hV
  haveI : IsDominant O.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact O.2.dense ⟨_, hOne⟩⟩
  have hU : O.ι ≫ h ≫ q = O.ι ≫ pF ≫ φ.hom ≫ ι' :=
    eq_of_comp_eq_of_mem_biregularLocus fp (h := O.ι ≫ (h ≫ q) ≫ fp)
      (by simp only [Category.assoc]) (by rw [Category.assoc, hab]) (fun w => w.2)
  exact ext_of_isDominant_of_isSeparated fp hab O.ι hU

/-- A nonzero rational function lying in the local ring of every point of an integral scheme
universally closed over a field is a unit in every local ring. -/
private theorem exists_isUnit_algebraMap_eq {F : Scheme.{0}} [IsIntegral F]
    (sF : F ⟶ Spec (.of k)) [UniversallyClosed sF] {u : F.functionField} (hu0 : u ≠ 0)
    (hu : ∀ w : F, u ∈ (algebraMap (F.presheaf.stalk w) F.functionField).range) (w : F) :
    ∃ a : F.presheaf.stalk w, IsUnit a ∧ algebraMap _ F.functionField a = u := by
  obtain ⟨r, hr⟩ := MMP.Intersection.exists_germToFunctionField_eq_of_forall_mem_range_stalk ⊤
    (fun x _ => hu x)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hu0 (by rw [← hr, map_zero])
  have hfield := isField_of_universallyClosed (K := k) sF
  have hunit : IsUnit r := by
    obtain ⟨r', hr'⟩ := hfield.mul_inv_cancel hr0
    exact IsUnit.of_mul_eq_one r' hr'
  refine ⟨F.presheaf.germ ⊤ w (Set.mem_univ _) r, hunit.map _, ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, hr]

end CommonModel

/-! ### Discrepancies on a common model of a flip -/

section CommonModelDiscrepancy

variable {k : Type} [Field k]

/-- A prime divisor `E` of `Y` is exceptional for a morphism `g : Y ⟶ X` exactly when `g(η_E)` has
codimension at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (g : Y ⟶ X) (E : Mori.PrimeDivisor Y) :
    RationalMap.IsExceptional (X := Y) g.toRationalMap E ↔
      2 ≤ Order.coheight (g E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hmem : g E.genericPoint ∈
      (Closeds.closure (g '' (E.idealSheaf.support : Set Y)) : Set X) := by
    refine subset_closure ⟨E.genericPoint, ?_, rfl⟩
    change E.genericPoint ∈ E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  refine ⟨fun h => h _ hmem, fun h x hx => h.trans (Order.coheight_anti ?_)⟩
  have h1 : g '' (E.idealSheaf.support : Set Y) ⊆ closure {g E.genericPoint} := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w ∈ E.support := hw
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hw'
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hw').map g.base.hom.continuous)
  exact specializes_iff_mem_closure.mpr (closure_minimal h1 isClosed_closure hx)

/-- A divisor over a normal variety is exceptional exactly when its center has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX)
  exact isExceptional_toRationalMap_iff_two_le_coheight D.f D.E

/-- A divisor over `X` whose centre is a point of codimension at most one is not exceptional. -/
private theorem not_isExceptional_of_coheight_le_one {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) (h : Order.coheight (D.f D.E.genericPoint) ≤ 1) :
    ¬ D.IsExceptional := fun hD =>
  absurd (((isExceptional_iff_two_le_coheight hX D).mp hD).trans h) (by decide)

/-- On a common model `p : W ⟶ X`, `q : W ⟶ X⁺` of a flip, the valuations of a prime divisor `E`
of `W`, read on `k(Z)` through `f` and `f⁺`, agree. -/
private theorem valuation_comap_eq_of_comp_eq {X X' Z W : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral Z] [IsLocallyNoetherian W] [IsNormal W] {sX : X ⟶ Spec (.of k)}
    {sX' : X' ⟶ Spec (.of k)}
    {f : X ⟶ Z} {fp : X' ⟶ Z} [IsDominant f] [IsDominant fp] {p : W ⟶ X} {q : W ⟶ X'}
    (hW : IsNormalVariety k (p ≫ sX)) (hW' : IsNormalVariety k (q ≫ sX'))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (E : Mori.PrimeDivisor W) :
    (⟨W, p, hW, hpb, E⟩ : DivisorOver k sX).valuation.comap (functionFieldMap f) =
      (⟨W, q, hW', hqb, E⟩ : DivisorOver k sX').valuation.comap (functionFieldMap fp) := by
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have key : ∀ (g g' : W ⟶ Z) (_ : g = g') [IsDominant g] [IsDominant g'] (t : Z.functionField),
      functionFieldMap g t = functionFieldMap g' t := by
    intro g g' hg _ _ t
    subst hg
    rfl
  ext t
  change E.divisorialValuation (functionFieldMap p (functionFieldMap f t)) =
    E.divisorialValuation (functionFieldMap q (functionFieldMap fp t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, key _ _ hpq]

/-- **Discrepancies do not decrease on a common model of a flip.** For a prime divisor `E` of a
common normal model `p : W ⟶ X`, `q : W ⟶ X⁺` of a `(K + B)`-flip, `a(E, X, B) ≤ a(E, X⁺, B⁺)`.
For `E` exceptional over `Z` this is `MMP.Mori.IsFlip.isDiscrepancy_le`; otherwise `E` lies over
prime divisors of `X` and of `X⁺` with the same coefficient in `B` and `B⁺`. -/
private theorem isDiscrepancy_le_of_comp_eq [IsAlgClosed k] [CharZero k]
    {X X' Z W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hflip : Mori.IsFlip sX sZ sX' K B f fp) {p : W ⟶ X} {q : W ⟶ X'}
    (hW : IsNormalVariety k (p ≫ sX)) (hW' : IsNormalVariety k (q ≫ sX'))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (E : Mori.PrimeDivisor W) {a a' : ℚ}
    (ha : IsDiscrepancy sX n K B ⟨W, p, hW, hpb, E⟩ a)
    (ha' : IsDiscrepancy sX' n (flipTransform f fp K) (flipTransform f fp B)
      ⟨W, q, hW', hqb, E⟩ a') : a ≤ a' := by
  have hFC := hflip.isFlippingContraction
  have hZ := hFC.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsProper f := hFC.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsDominant f := hFC.isBirationalMorphism.isDominant
  haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsNormal W := hW.2
  haveI := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  have hv := valuation_comap_eq_of_comp_eq hW hW' hpb hqb hpq E
  by_cases hE : RationalMap.IsExceptional (X := W) (p ≫ f).toRationalMap E
  · exact IsFlip.isDiscrepancy_le ha.isPair hflip _ _ hv hE ha ha'
  · have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
    set z := (p ≫ f) E.genericPoint
    have hz1 : Order.coheight z ≤ 1 := by
      rw [isExceptional_toRationalMap_iff_two_le_coheight] at hE
      push Not at hE
      exact (by simpa using hE : Order.coheight (f (p E.genericPoint)) ≤ 1)
    have hzf : z ∈ biregularLocus f :=
      MMP.Positivity.mem_biregularLocus_of_coheight_le_one f
        hFC.isBirationalMorphism.functionFieldMap_bijective hFC.two_le_codimension hz1
    have hzfp : z ∈ biregularLocus fp :=
      MMP.Positivity.mem_biregularLocus_of_coheight_le_one fp
        hflip.isBirationalMorphism.functionFieldMap_bijective hflip.two_le_codimension hz1
    have hzq : fp (q E.genericPoint) = z := by
      change (q ≫ fp) E.genericPoint = z
      rw [← hpq]
    have hcp : Order.coheight (p E.genericPoint) ≤ 1 :=
      (MMP.Positivity.coheight_map_of_mem_biregularLocus f (x := p E.genericPoint)
        hzf).symm.le.trans hz1
    have hcq : Order.coheight (q E.genericPoint) ≤ 1 := by
      have h1 := MMP.Positivity.coheight_map_of_mem_biregularLocus fp (x := q E.genericPoint)
        (hzq ▸ hzfp)
      rw [hzq] at h1
      exact h1.symm.le.trans hz1
    have hK' := hflip.isCanonicalDivisor_flipTransform ha.2.1
    obtain ⟨P, hPc, hPd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hFC.isNormalVariety_source, ha.2.1, hFC.isQCartier⟩ _
      (not_isExceptional_of_coheight_le_one hFC.isNormalVariety_source
        ⟨W, p, hW, hpb, E⟩ hcp)
    obtain ⟨P', hPc', hPd'⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff
      ⟨hflip.isNormalVariety, hK', hflip.isQCartier⟩ _
      (not_isExceptional_of_coheight_le_one hflip.isNormalVariety ⟨W, q, hW', hqb, E⟩ hcq)
    have e1 := ha.eq hPd
    have e2 := ha'.eq hPd'
    have hηP : p E.genericPoint = P.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨W, p, hW, hpb, E⟩ : DivisorOver k sX),
        hPc, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    have hηP' : q E.genericPoint = P'.genericPoint := by
      refine (inseparable_iff_closure_eq.2 ?_).eq
      rw [← DivisorOver.center_eq_closure_genericPoint (⟨W, q, hW', hqb, E⟩ : DivisorOver k sX'),
        hPc', AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    obtain ⟨V, hfV, hfpV, hXV, -, -⟩ := hflip.exists_opens_isIso
    have hPP : f P.genericPoint = fp P'.genericPoint := by
      rw [← hηP, ← hηP', hzq]
      rfl
    have hcoeff := MMP.Mori.flipTransform_apply hZ (hFC.comp_eq ▸ hFC.isNormalVariety_source)
      hFC.isBirationalMorphism V hXV hPP B
    have : (flipTransform f fp B).coeff P' = B.coeff P := hcoeff
    rw [e1, e2, this]

/-- **The rational top `m`-forms of a variety form a line.** -/
private theorem exists_eq_smul_of_ne_zero [PerfectField k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {σ : RationalPluriForms sX d m} (hσ : σ ≠ 0) (σ' : RationalPluriForms sX d m) :
    ∃ c : X.functionField, σ' = c • σ := by
  letI := functionFieldAlgebra sX
  haveI := essFiniteType_functionField (sX := sX)
  have hK : Module.finrank X.functionField Ω[X.functionField⁄k] = d :=
    (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans hd
  have h1 : Module.finrank X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
  let b1 : Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]) :=
    (Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique _ _)
  let B : Module.Basis Unit X.functionField (RationalPluriForms sX d m) := ZTensorPower.basis b1 m
  have hB : Module.finrank X.functionField (RationalPluriForms sX d m) = 1 := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_unit]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' σ hσ).mp hB σ'
  exact ⟨c, hc.symm⟩

/-- Transporting a rational pluriform along an equality of structure morphisms does not change its
order along a prime divisor. -/
private theorem ordForm_cast {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m)
    (E : Mori.PrimeDivisor X) : E.ordForm (h ▸ τ : RationalPluriForms s' d m) = E.ordForm τ := by
  subst h
  rfl

/-- **The difference of the pulled-back adjoints is effective.** On a common normal model
`p : W ⟶ X`, `q : W ⟶ X⁺` of a `(K + B)`-flip, let `τ` and `τ'` generate `𝒪_X(m(K + B))` near
`p w` and `𝒪_{X⁺}(m(K⁺ + B⁺))` near `q w`. Then the ratio `c = q^*τ' / p^*τ` is regular at
`w`. -/
private theorem exists_algebraMap_stalk_eq_of_generatesOn [IsAlgClosed k] [CharZero k]
    {X X' Z W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hflip : Mori.IsFlip sX sZ sX' K B f fp) (hK : K.IsCanonicalDivisor sX n)
    [IsIntegral W] {p : W ⟶ X} {q : W ⟶ X'}
    (hW : IsNormalVariety k (p ≫ sX)) (hW' : IsNormalVariety k (q ≫ sX'))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (hs : q ≫ sX' = p ≫ sX) {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hC' : ((m : ℤ) • (Divisor.toQDivisor (flipTransform f fp K) +
      flipTransform f fp B)).IsCartierDivisor)
    {U : X.Opens} {τ : RationalPluriForms sX n m} (hτ : GeneratesOn B m U τ)
    {U' : X'.Opens} {τ' : RationalPluriForms sX' n m}
    (hτ' : GeneratesOn (flipTransform f fp B) m U' τ') {w : W} (hwU : p w ∈ U)
    (hwU' : q w ∈ U') {c : W.functionField}
    (hc : haveI : IsDominant p := hpb.isDominant
      haveI : IsDominant q := hqb.isDominant
      (hs ▸ pullbackRationalPluriForms sX' q τ' : RationalPluriForms (p ≫ sX) n m) =
        c • pullbackRationalPluriForms sX p τ) :
    ∃ r : W.presheaf.stalk w, algebraMap _ W.functionField r = c := by
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsNormal W := hW.2
  haveI := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  haveI := hXv.1.toLocallyOfFiniteType
  haveI := hflip.isNormalVariety.1.toLocallyOfFiniteType
  have hK' := hflip.isCanonicalDivisor_flipTransform hK
  have hdX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  have hdW : topologicalKrullDim W = n := by
    haveI := hXv.1
    haveI := hW.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb, hdX]
  have hσ0 : pullbackRationalPluriForms sX p τ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hpb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdX) hτ.1
  have hσ0' : pullbackRationalPluriForms sX' q τ' ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' q
      hqb.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdX') hτ'.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    apply hσ0'
    have : ∀ (s s' : W ⟶ Spec (.of k)) (h : s' = s) (σ : RationalPluriForms s' n m),
        (h ▸ σ : RationalPluriForms s n m) = 0 → σ = 0 := by
      intro s s' h σ hσ
      subst h
      exact hσ
    exact this _ _ hs _ hc
  refine MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg w hc0
    fun E hwE => ?_
  have hEw : E.genericPoint ⤳ w := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwE
    exact specializes_iff_mem_closure.mpr hwE
  have hpE : p E.genericPoint ∈ U :=
    (hEw.map p.base.hom.continuous).mem_open U.isOpen hwU
  have hqE : q E.genericPoint ∈ U' :=
    (hEw.map q.base.hom.continuous).mem_open U'.isOpen hwU'
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have ha : IsDiscrepancy sX n K B ⟨W, p, hW, hpb, E⟩
      ((E.ordForm (pullbackRationalPluriForms sX p τ) : ℚ) / m) :=
    ⟨hXv, hK, m, hm, hC, U, hpE, τ, hτ, by field_simp; rfl⟩
  have ha' : IsDiscrepancy sX' n (flipTransform f fp K) (flipTransform f fp B) ⟨W, q, hW', hqb, E⟩
      ((E.ordForm (pullbackRationalPluriForms sX' q τ') : ℚ) / m) :=
    ⟨hflip.isNormalVariety, hK', m, hm, hC', U', hqE, τ', hτ', by field_simp; rfl⟩
  have hle := isDiscrepancy_le_of_comp_eq hflip hW hW' hpb hqb hpq E ha ha'
  have hsm := E.ordForm_smul_of_topologicalKrullDim_eq hdW hc0 hσ0
  rw [← hc, ordForm_cast] at hsm
  have hle' : (E.ordForm (pullbackRationalPluriForms sX p τ) : ℚ) ≤
      E.ordForm (pullbackRationalPluriForms sX' q τ') := by
    have hmpos : (0 : ℚ) < m := by exact_mod_cast hm
    exact (div_le_div_iff_of_pos_right hmpos).mp hle
  have : (E.ordForm (pullbackRationalPluriForms sX p τ) : ℤ) ≤
      E.ordForm (pullbackRationalPluriForms sX' q τ') := by exact_mod_cast hle'
  omega

/-- Transport of a pluriform along an equality of structure morphisms commutes with pull-back. -/
private theorem pullbackRationalPluriForms_cast {Y W : Scheme.{0}} [IsIntegral Y] [IsIntegral W]
    (g : Y ⟶ W) [IsDominant g] {s s' : W ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ}
    (σ : RationalPluriForms s d m) :
    pullbackRationalPluriForms s' g (h ▸ σ : RationalPluriForms s' d m) =
      ((congrArg (g ≫ ·) h) ▸ pullbackRationalPluriForms s g σ :
        RationalPluriForms (g ≫ s') d m) := by
  subst h
  rfl

/-- Pull-back of a multiple of a pluriform. -/
private theorem pullbackRationalPluriForms_smul' {Y W : Scheme.{0}} [IsIntegral Y] [IsIntegral W]
    (sW : W ⟶ Spec (.of k)) (g : Y ⟶ W) [IsDominant g] {d : ℕ} {m : ℤ} (c : W.functionField)
    (σ : RationalPluriForms sW d m) :
    pullbackRationalPluriForms sW g (c • σ) =
      functionFieldMap g c • pullbackRationalPluriForms sW g σ := by
  letI := functionFieldAlgebra sW
  letI := functionFieldAlgebra (g ≫ sW)
  letI := functionFieldMapAlgebra g
  haveI := isScalarTower_functionFieldMap sW g
  exact MMP.Fourfold.pullbackForms_smul (K := W.functionField) (K' := Y.functionField) c σ

/-- **Strict increase of discrepancies at a point over the flipping locus.** In the situation of
`exists_algebraMap_stalk_eq_of_generatesOn`, if `W` is regular at `w`, `w` has codimension at
least two and `f (p w)` lies outside the biregular locus of `f`, then `q^*τ' / p^*τ` is not a unit
at `w`. -/
private theorem not_exists_isUnit_of_notMem_biregularLocus [IsAlgClosed k] [CharZero k]
    {X X' Z W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hflip : Mori.IsFlip sX sZ sX' K B f fp) (hK : K.IsCanonicalDivisor sX n)
    [IsIntegral W] {p : W ⟶ X} {q : W ⟶ X'}
    (hW : IsNormalVariety k (p ≫ sX)) (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (hs : q ≫ sX' = p ≫ sX) {m : ℕ} (hm : 0 < m)
    (hC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor)
    (hC' : ((m : ℤ) • (Divisor.toQDivisor (flipTransform f fp K) +
      flipTransform f fp B)).IsCartierDivisor)
    {U : X.Opens} {τ : RationalPluriForms sX n m} (hτ : GeneratesOn B m U τ)
    {U' : X'.Opens} {τ' : RationalPluriForms sX' n m}
    (hτ' : GeneratesOn (flipTransform f fp B) m U' τ') {w : W} (hwU : p w ∈ U)
    (hwU' : q w ∈ U') (hwV : f (p w) ∉ biregularLocus f)
    (hreg : IsRegularLocalRing (W.presheaf.stalk w)) (hcw : 2 ≤ Order.coheight w)
    {c : W.functionField}
    (hc : haveI : IsDominant p := hpb.isDominant
      haveI : IsDominant q := hqb.isDominant
      (hs ▸ pullbackRationalPluriForms sX' q τ' : RationalPluriForms (p ≫ sX) n m) =
        c • pullbackRationalPluriForms sX p τ) :
    ¬ ∃ r : W.presheaf.stalk w, IsUnit r ∧ algebraMap _ W.functionField r = c := by
  rintro ⟨r, hr, hrc⟩
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hFC := hflip.isFlippingContraction
  have hXv := hFC.isNormalVariety_source
  have hX'v := hflip.isNormalVariety
  have hZ := hFC.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsProper f := hFC.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsDominant f := hFC.isBirationalMorphism.isDominant
  haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
  haveI := hXv.1.toLocallyOfFiniteType
  haveI := hX'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
  have hK' := hflip.isCanonicalDivisor_flipTransform hK
  have hdX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  -- the exceptional divisor of the blow-up of `w`
  set V : IrreducibleCloseds W := IrreducibleCloseds.closureSingleton w
  have hV : 2 ≤ codimension V := by
    rw [MMP.Flips.codimension_closureSingleton]; exact hcw
  obtain ⟨D₀, -, -, -, hD₀w, -, -, -⟩ :=
    MMP.Mori.TerminalCodimTwo.exists_divisorOver_smoothBlowup hW V hV w
    ((irreducibleSetEquivPoints (α := W)).apply_symm_apply w).symm hreg
  haveI := D₀.isIntegral
  haveI := D₀.isLocallyNoetherian
  haveI := D₀.isNormal
  haveI := D₀.isDominant
  have hYv : IsNormalVariety k ((D₀.f ≫ p) ≫ sX) := by
    rw [Category.assoc]; exact D₀.isNormalVariety
  have hYv' : IsNormalVariety k ((D₀.f ≫ q) ≫ sX') := by
    rw [Category.assoc, hs]; exact D₀.isNormalVariety
  have hgp : IsBirationalMorphism (D₀.f ≫ p) :=
    MMP.Mori.isBirationalMorphism_comp D₀.isBirationalMorphism hpb
  have hgq : IsBirationalMorphism (D₀.f ≫ q) :=
    MMP.Mori.isBirationalMorphism_comp D₀.isBirationalMorphism hqb
  set D : DivisorOver k sX := ⟨D₀.Y, D₀.f ≫ p, hYv, hgp, D₀.E⟩
  set D' : DivisorOver k sX' := ⟨D₀.Y, D₀.f ≫ q, hYv', hgq, D₀.E⟩
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpw : (D₀.f ≫ p) D₀.E.genericPoint = p w := by
    rw [Scheme.Hom.comp_apply, hD₀w]
  have hqw : (D₀.f ≫ q) D₀.E.genericPoint = q w := by
    rw [Scheme.Hom.comp_apply, hD₀w]
  have ha : IsDiscrepancy sX n K B D
      ((D₀.E.ordForm (pullbackRationalPluriForms sX (D₀.f ≫ p) τ) : ℚ) / m) :=
    ⟨hXv, hK, m, hm, hC, U, hpw ▸ hwU, τ, hτ, by field_simp; rfl⟩
  have ha' : IsDiscrepancy sX' n (flipTransform f fp K) (flipTransform f fp B) D'
      ((D₀.E.ordForm (pullbackRationalPluriForms sX' (D₀.f ≫ q) τ') : ℚ) / m) :=
    ⟨hX'v, hK', m, hm, hC', U', hqw ▸ hwU', τ', hτ', by field_simp; rfl⟩
  -- the strict comparison
  have hv : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) :=
    valuation_comap_eq_of_comp_eq hYv hYv' hgp hgq
      (by rw [Category.assoc, Category.assoc, hpq]) D₀.E
  have hz2 : 2 ≤ Order.coheight (f (p w)) := by
    by_contra h2
    push Not at h2
    exact hwV (MMP.Positivity.mem_biregularLocus_of_coheight_le_one f
      hFC.isBirationalMorphism.functionFieldMap_bijective hFC.two_le_codimension
      (by simpa using h2))
  have hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E := by
    have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
    rw [isExceptional_toRationalMap_iff_two_le_coheight, Scheme.Hom.comp_apply,
      show D.f D.E.genericPoint = p w from hpw]
    exact hz2
  have hΔ : RationalMap.transformDivisor (X := X) f.toRationalMap B =
      RationalMap.transformDivisor (X := X') fp.toRationalMap (flipTransform f fp B) :=
    (MMP.Mori.transformDivisor_inverseTransformDivisor hZ (hflip.comp_eq ▸ hX'v)
      hflip.isBirationalMorphism hflip.two_le_codimension _).symm
  have hWD : f (D.f D.E.genericPoint) ∉ biregularLocus f := by
    rw [show D.f D.E.genericPoint = p w from hpw]
    exact hwV
  have hlt := isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple hXv hX'v hZ hFC.comp_eq
    hflip.comp_eq hFC.isBirationalMorphism hflip.isBirationalMorphism hK hK' hΔ
    (MMP.Mori.isRelativelyNef_of_hasRelativelyAmpleMultiple hFC.hasRelativelyAmpleMultiple)
    (MMP.Mori.isRelativelyNef_of_hasRelativelyAmpleMultiple hflip.hasRelativelyAmpleMultiple)
    hFC.hasRelativelyAmpleMultiple D D' hv hE hWD ha ha'
  -- but `c` is a unit at the centre `w` of `D₀`, so the two discrepancies agree
  have hdW : topologicalKrullDim W = n := by
    haveI := hXv.1
    haveI := hW.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb, hdX]
  have hσ0 : pullbackRationalPluriForms sX p τ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hpb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdX) hτ.1
  haveI := hW.1.toLocallyOfFiniteType
  have hdW' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := p ≫ sX) hdW
  have hgσ0 : pullbackRationalPluriForms (p ≫ sX) D₀.f (pullbackRationalPluriForms sX p τ) ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' D₀.f
      D₀.isBirationalMorphism.functionFieldMap_bijective hdW' hσ0
  have hgc : functionFieldMap D₀.f c ≠ 0 := by
    rw [← hrc]
    exact (map_ne_zero _).mpr ((hr.map _).ne_zero)
  subst hD₀w
  have hordc : D₀.Y.ord (functionFieldMap D₀.f c) D₀.E.genericPoint = 0 := by
    rw [← hrc, MMP.Mori.functionFieldMap_algebraMap_stalk D₀.f D₀.E.genericPoint r]
    exact D₀.E.ord_algebraMap_of_isUnit (hr.map _)
  have hdY : topologicalKrullDim D₀.Y = n := by
    haveI := hW.1
    haveI := D₀.isNormalVariety.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (p ≫ sX)
      (D₀.f ≫ p ≫ sX) D₀.isBirationalMorphism, hdW]
  haveI : LocallyOfFiniteType (q ≫ sX') := by rw [hs]; infer_instance
  haveI : LocallyOfFiniteType (D₀.f ≫ p ≫ sX) := D₀.isNormalVariety.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdX
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hdX'
  have e1 := MMP.Flips.pullbackRationalPluriForms_comp p D₀.f hpb.functionFieldMap_bijective
    D₀.isBirationalMorphism.functionFieldMap_bijective hd τ
  have hgq' : Function.Bijective (functionFieldMap D₀.f) :=
    D₀.isBirationalMorphism.functionFieldMap_bijective
  have e2 := MMP.Flips.pullbackRationalPluriForms_comp q D₀.f hqb.functionFieldMap_bijective
    hgq' hd' τ'
  have e3 := pullbackRationalPluriForms_cast D₀.f hs (pullbackRationalPluriForms sX' q τ')
  rw [hc, pullbackRationalPluriForms_smul'] at e3
  have hord : D₀.E.ordForm (pullbackRationalPluriForms sX' (D₀.f ≫ q) τ') =
      D₀.E.ordForm (pullbackRationalPluriForms sX (D₀.f ≫ p) τ) := by
    have h1 := congrArg D₀.E.ordForm e3
    rw [ordForm_cast, e2, D₀.E.ordForm_smul_of_topologicalKrullDim_eq hdY hgc hgσ0, hordc,
      zero_add, e1] at h1
    exact h1.symm
  rw [hord] at hlt
  exact lt_irrefl _ hlt

/-- **Local generators pull back along an isomorphism.** If `ρ` generates `𝒪_{S'}(m(K + B'))` on
`U`, then for an isomorphism `e : S ⟶ S'` its pull-back generates `𝒪_S(m(K + e^*B'))` on
`e⁻¹U`, where `e^*B'` is the inverse transform. -/
private theorem generatesOn_pullback_of_isIso [PerfectField k] {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {sS' : S' ⟶ Spec (.of k)} [LocallyOfFiniteType sS'] (e : S ⟶ S') [IsIso e] {d : ℕ}
    (hd : letI := functionFieldAlgebra sS'; (Algebra.trdeg k S'.functionField).toNat = d)
    {m : ℕ} {B' : QDivisor S'} {U : S'.Opens} {ρ : RationalPluriForms sS' d m}
    (hρ : GeneratesOn B' m U ρ) :
    GeneratesOn (inverseTransformDivisor e B') m (e ⁻¹ᵁ U)
      (pullbackRationalPluriForms sS' e ρ) := by
  have hbij : Function.Bijective (functionFieldMap e) :=
    (isBirationalMorphism_of_isIso e).functionFieldMap_bijective
  have hV : ∀ y : S, e y ∈ biregularLocus e := fun y =>
    le_biregularLocus ((isBiregular_top_iff e).mpr inferInstance) trivial
  refine ⟨MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' e hbij hd hρ.1,
    fun Γ hΓ => ?_⟩
  have hco : Order.coheight (e Γ.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus e (hV _)]
    exact Γ.coheight_genericPoint
  set Γ' : Mori.PrimeDivisor S' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hΓ' : e Γ.genericPoint = Γ'.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm
  have hord := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso e hbij hd Γ Γ' hΓ' ρ
  have hsome : inverseTransformPrimeDivisor e Γ' = some Γ :=
    inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hΓ' (hV _)
  have huniq : ∀ E', inverseTransformPrimeDivisor e E' = some Γ → E' = Γ' := by
    intro E' hE'
    obtain ⟨-, hI⟩ := inverseTransformPrimeDivisor_eq_some_iff.mp hE'
    have hsupp : (Γ.support : Set S) ⊆ e ⁻¹' (E'.support : Set S') := by
      have h1 := congrArg (fun I : S.IdealSheafData => (I.support : Set S)) hI
      simp only [inverseTransformIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1
      change (Γ.support : Set S) = _ at h1
      rw [h1, inverseTransform, Closeds.coe_closure]
      exact closure_minimal (fun y hy => hy.1)
        (E'.idealSheaf.support.isClosed.preimage e.continuous)
    have hmem : e Γ.genericPoint ∈ E'.support := by
      refine hsupp ?_
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
    have hsp : E'.genericPoint ⤳ Γ'.genericPoint := hΓ' ▸ specializes_iff_mem_closure.mpr hmem
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    by_contra hne
    have hle : Γ'.genericPoint ≤ E'.genericPoint := hsp
    have hnle : ¬ E'.genericPoint ≤ Γ'.genericPoint := fun h => hne (hsp.antisymm h).eq
    have := Order.coheight_strictAnti (lt_of_le_not_ge hle hnle)
      (by rw [E'.coheight_genericPoint]; decide)
    rw [Γ'.coheight_genericPoint, E'.coheight_genericPoint] at this
    exact lt_irrefl _ this
  have hcoeff : (inverseTransformDivisor e B').coeff Γ = B'.coeff Γ' :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hsome huniq B'
  have hΓ'U : (Γ'.support ∩ (U : Set S')).Nonempty := by
    obtain ⟨y, hy, hyU⟩ := hΓ
    refine ⟨e y, ?_, hyU⟩
    have hy' : y ∈ Γ.support := hy
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy' ⊢
    have := (specializes_iff_mem_closure.mpr hy').map e.base.hom.continuous
    rw [hΓ'] at this
    exact specializes_iff_mem_closure.mp this
  rw [hord, hcoeff]
  exact hρ.2 Γ' hΓ'U

end CommonModelDiscrepancy

/-! ### Adjunction of local generators along a flag -/

section FlagAdjunction

variable {k : Type} [Field k]

/-- A rational function of order zero along every prime divisor through `x` is a unit of the
local ring at `x`. -/
private theorem exists_isUnit_algebraMap_eq_of_ord_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (x : X) {c : X.functionField} (hc : c ≠ 0)
    (h : ∀ Γ : Mori.PrimeDivisor X, x ∈ Γ.support → X.ord c Γ.genericPoint = 0) :
    ∃ r : X.presheaf.stalk x, IsUnit r ∧ algebraMap _ X.functionField r = c := by
  obtain ⟨r, hr⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x hc
    fun Γ hΓ => (h Γ hΓ).ge
  obtain ⟨r', hr'⟩ := MMP.Threefold.Mori.Helpers.exists_algebraMap_stalk_eq_of_forall_ord_nonneg x
    (inv_ne_zero hc) fun Γ hΓ => by
      have h1 := Scheme.ord_mul (x := Γ.genericPoint) hc (inv_ne_zero hc)
      rw [mul_inv_cancel₀ hc, MMP.CyclicChartDifferent.Aux.ord_one', h Γ hΓ] at h1
      omega
  exact ⟨r, IsUnit.of_mul_eq_one r' (IsFractionRing.injective _ X.functionField
    (by rw [map_mul, hr, hr', mul_inv_cancel₀ hc, map_one])), hr⟩

/-- Two generators of the same sheaf `𝒪_X(m(K_X + B))` on `O` differ by a unit at every point of
`O`. -/
private theorem exists_isUnit_of_generatesOn [PerfectField k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s] {d : ℕ}
    (hd : topologicalKrullDim X = d) {m : ℕ} {B : QDivisor X} {O : X.Opens}
    {ρ₁ ρ₂ : RationalPluriForms s d m} (h₁ : GeneratesOn B m O ρ₁) (h₂ : GeneratesOn B m O ρ₂)
    {ψ : X.functionField} (hψ : ρ₂ = ψ • ρ₁) {x : X} (hx : x ∈ O) :
    ∃ r : X.presheaf.stalk x, IsUnit r ∧ algebraMap _ X.functionField r = ψ := by
  have hψ0 : ψ ≠ 0 := by rintro rfl; rw [zero_smul] at hψ; exact h₂.1 hψ
  refine exists_isUnit_algebraMap_eq_of_ord_eq_zero x hψ0 fun Γ hΓ => ?_
  have e1 := h₁.2 Γ ⟨x, hΓ, hx⟩
  have e2 := h₂.2 Γ ⟨x, hΓ, hx⟩
  rw [hψ, Γ.ordForm_smul_of_topologicalKrullDim_eq hd hψ0 h₁.1] at e2
  push_cast at e1 e2
  have : ((X.ord ψ Γ.genericPoint : ℤ) : ℚ) = 0 := by linarith
  exact_mod_cast this

/-- Changing a top form by a nonzero rational function keeps `m(div σ + B)` Cartier. -/
private theorem isCartierDivisor_smul_divisorOfForm_add [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] {d : ℕ} (hd : topologicalKrullDim X = d)
    {σ : RationalPluriForms sX d 1} (hσ : σ ≠ 0) {B : QDivisor X} {m : ℕ}
    (hC : ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {c : X.functionField} (hc : c ≠ 0) :
    ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm (c • σ)) + B)).IsCartierDivisor := by
  obtain ⟨D, hD, hDc⟩ := hC
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero hc
  refine ⟨D + (m : ℤ) • principalDivisor φ, ?_,
    hDc.add ((Divisor.isCartier_principalDivisor φ).zsmul _)⟩
  ext Γ
  have h1 := congrArg (fun G : QDivisor X => G.coeff Γ) hD
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, zsmul_eq_mul] at h1 ⊢
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hd hc hσ, coeff_principalDivisor, hφ Γ]
  push_cast
  linear_combination h1

/-- If `m(K + B)` is Cartier for a canonical divisor `K`, then so is `m(div σ + B)` for every
nonzero rational top form `σ`. -/
private theorem isCartierDivisor_divisorOfForm_add [CharZero k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType sY] (hY : IsNormalVariety k sY) {n m : ℕ} {KY : Divisor Y}
    {BY : QDivisor Y} (hKY : KY.IsCanonicalDivisor sY n)
    (hCY : ((m : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor)
    (σ : RationalPluriForms sY n 1) (hσ : σ ≠ 0) :
    ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BY)).IsCartierDivisor := by
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hKY
  have hdivω : divisorOfForm ω = KY := Finsupp.ext hωK
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_ne_zero
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hKY.topologicalKrullDim_eq) hω0 σ
  have hc : c ≠ 0 := by rintro rfl; exact hσ (zero_smul _ _)
  exact isCartierDivisor_smul_divisorOfForm_add hKY.topologicalKrullDim_eq hω0
    (by rw [hdivω]; exact hCY) hc

/-- Conversely, if `m(div σ + B)` is Cartier for every nonzero rational top form `σ`, then
`m(K + B)` is Cartier for some canonical divisor `K`. -/
private theorem exists_isCanonicalDivisor_isCartierDivisor [CharZero k] {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] {sY : Y ⟶ Spec (.of k)}
    [LocallyOfFiniteType sY] (hY : IsNormalVariety k sY)
    {n m : ℕ} (hn : topologicalKrullDim Y = n) {BY : QDivisor Y}
    (hC : ∀ σ : RationalPluriForms sY n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BY)).IsCartierDivisor) :
    ∃ KY : Divisor Y, KY.IsCanonicalDivisor sY n ∧
      ((m : ℤ) • (Divisor.toQDivisor KY + BY)).IsCartierDivisor := by
  obtain ⟨KY, hKY⟩ := MMP.Mori.exists_isCanonicalDivisor sY hY hn
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hKY
  have hdivω : divisorOfForm ω = KY := Finsupp.ext hωK
  exact ⟨KY, hKY, hdivω ▸ hC ω hω0⟩

/-- An adjunction step drops the dimension by one. -/
private theorem IsAdjunctionStep.topologicalKrullDim_eq' [CharZero k] {M T : Scheme.{0}}
    {sM : M ⟶ Spec (.of k)} [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M]
    [LocallyOfFiniteType sM] {n : ℕ} (hdim : topologicalKrullDim M = n + 1)
    {B : QDivisor M} {j : T ⟶ M} {BT : QDivisor T} (hj : IsAdjunctionStep sM B j BT)
    [IsIntegral T] : topologicalKrullDim T = n := by
  haveI : LocallyOfFiniteType (j ≫ sM) := hj.1.1.toLocallyOfFiniteType
  have h1 := hj.trdeg_add_one
  have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ sM)
  have h3 := topologicalKrullDim_eq_toNat_trdeg sM
  rw [hdim] at h3
  have h6 : n + 1 = (letI := functionFieldAlgebra sM; (Algebra.trdeg k M.functionField).toNat) := by
    exact_mod_cast h3
  have h7 : (letI := functionFieldAlgebra (j ≫ sM); (Algebra.trdeg k T.functionField).toNat) =
      n := by omega
  rw [h2, h7]

/-- **One adjunction step for local generators.** -/
private theorem adjunctionStep_generatesOn [CharZero k] {M T : Scheme.{0}} {sM : M ⟶ Spec (.of k)}
    [IsIntegral M] [IsNormal M] [IsLocallyNoetherian M] [CompactSpace M] [LocallyOfFiniteType sM]
    (hM : IsNormalVariety k sM) {n : ℕ} (hdim : topologicalKrullDim M = n + 1) (hn : n ≠ 0)
    {B : QDivisor M} {j : T ⟶ M} {BT : QDivisor T} (hj : IsAdjunctionStep sM B j BT)
    [IsIntegral T] [IsNormal T] [IsLocallyNoetherian T] [CompactSpace T]
    {m : ℕ} (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sM (n + 1) 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {V : M.Opens} {ρ : RationalPluriForms sM (n + 1) m} (hρ : GeneratesOn B m V ρ)
    (hV : ((j ⁻¹ᵁ V : T.Opens) : Set T).Nonempty) :
    haveI : LocallyOfFiniteType (j ≫ sM) := hj.1.1.toLocallyOfFiniteType
    (∃ ρ' : RationalPluriForms (j ≫ sM) n m, IsPoincareResidue sM j n m ρ ρ') ∧
      (∀ ρ' : RationalPluriForms (j ≫ sM) n m, IsPoincareResidue sM j n m ρ ρ' →
        GeneratesOn BT m (j ⁻¹ᵁ V) ρ') ∧
      ∀ σ' : RationalPluriForms (j ≫ sM) n 1, σ' ≠ 0 →
        ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ') + BT)).IsCartierDivisor := by
  haveI : LocallyOfFiniteType (j ≫ sM) := hj.1.1.toLocallyOfFiniteType
  obtain ⟨hTv, P, -, hPr, hjc, -⟩ := id hj
  haveI := hjc
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 1 := ⟨m - 1, by omega⟩
  have hdT : topologicalKrullDim T = n := IsAdjunctionStep.topologicalKrullDim_eq' hdim hj
  have hdM' : topologicalKrullDim M = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; norm_cast
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sM) hdM'
  have hdT' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := j ≫ sM) hdT
  obtain ⟨Q₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdT hn
  obtain ⟨σ, hσ0, hσP, -, ρσ, hρσ, hρσ0, -⟩ :=
    MMP.Fourfold.exists_form_of_residue_order sM hM hdim j hTv P hPr Q₀
  obtain ⟨DM, hDM, hDMc⟩ := hC σ hσ0
  have hσQ : (Divisor.toQDivisor (divisorOfForm σ) + B).IsQCartier :=
    ⟨((N + 1 : ℕ) : ℤ), by exact_mod_cast (Nat.succ_pos N).ne', DM, hDM, hDMc⟩
  obtain ⟨hgen, hpull⟩ := IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue hj
    hdim P hPr σ hσ0 hσP ρσ hρσ hσQ
  set B' : QDivisor M := B - Finsupp.single P 1 with hB'
  have hBB' : Divisor.toQDivisor (divisorOfForm σ) + Finsupp.single P 1 + B' =
      Divisor.toQDivisor (divisorOfForm σ) + B := by rw [hB']; abel
  have key : ∀ L : QDivisor M, L = Divisor.toQDivisor (divisorOfForm σ) + B →
      ∃ hg, L.IsPullback j hg (Divisor.toQDivisor (divisorOfForm ρσ) + BT) := by
    rintro L rfl; exact ⟨hgen, hpull⟩
  obtain ⟨hgen', hpull'⟩ := key _ hBB'
  have hDM' : Divisor.toQDivisor DM = ((N + 1 : ℕ) : ℤ) •
      (Divisor.toQDivisor (divisorOfForm σ) + Finsupp.single P 1 + B') := by rw [hBB', hDM]
  have hPB : Finsupp.single P 1 + B' = B := by rw [hB']; abel
  -- the local comparison with the generators of `exists_generatesOn_isPoincareResidue`
  have hloc : ∀ x : T, j x ∈ V → ∃ U : M.Opens, j x ∈ U ∧
      ∃ ρ'' : RationalPluriForms (j ≫ sM) n ((N + 1 : ℕ) : ℤ),
        GeneratesOn BT (N + 1) (j ⁻¹ᵁ U) ρ'' ∧ ∃ r : M.presheaf.stalk (j x), IsUnit r ∧
          IsPoincareResidue sM j n (N + 1) ρ ((j.stalkMap (genericPoint T)).hom
            ((M.presheaf.stalkSpecializes
              ((genericPoint_specializes x).map j.base.hom.continuous)).hom r) • ρ'') := by
    intro x hxV
    obtain ⟨U, hxU, τ', hτ', ρ'', hres, hρ''⟩ :=
      MMP.CyclicChartDifferent.Aux.exists_generatesOn_isPoincareResidue sM hdim j hTv hdT P hPr B' σ
        hσ0 ρσ hρσ hρσ0 BT hgen' hpull' N DM hDM' hDMc x
    rw [hPB] at hτ'
    obtain ⟨c, hc⟩ := exists_eq_smul_of_ne_zero hd hτ'.1 ρ
    obtain ⟨r, hru, hr⟩ := exists_isUnit_of_generatesOn hdM' (hτ'.mono inf_le_left)
      (hρ.mono inf_le_right) hc (show j x ∈ U ⊓ V from ⟨hxU, hxV⟩)
    refine ⟨U, hxU, ρ'', hρ'', r, hru, ?_⟩
    have h := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hres
      ((M.presheaf.stalkSpecializes
        ((genericPoint_specializes x).map j.base.hom.continuous)).hom r)
    rwa [MMP.Mori.algebraMap_stalkSpecializes, hr, ← hc] at h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hV
    obtain ⟨U, -, ρ'', -, r, -, hres⟩ := hloc x hx
    exact ⟨_, hres⟩
  · intro ρ' hρ'
    refine ⟨?_, fun Q hQ => ?_⟩
    · obtain ⟨x, hx⟩ := hV
      obtain ⟨U, hxU, ρ'', hρ'', r, hr, hres⟩ := hloc x hx
      rw [IsPoincareResidue.unique hj hρ' hres]
      exact smul_ne_zero (((hr.map _).map _).ne_zero) hρ''.1
    · obtain ⟨x, hxQ, hxV⟩ := hQ
      obtain ⟨U, hxU, ρ'', hρ'', r, hr, hres⟩ := hloc x hxV
      rw [IsPoincareResidue.unique hj hρ' hres]
      have hQx : Q.genericPoint ⤳ x := by
        have : x ∈ Q.support := hxQ
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
        exact specializes_iff_mem_closure.mpr this
      have hQx' : j Q.genericPoint ⤳ j x := hQx.map j.base.hom.continuous
      have hTQ : genericPoint T ⤳ Q.genericPoint := genericPoint_specializes _
      set r₁ := (M.presheaf.stalkSpecializes hQx').hom r
      have hunit : IsUnit ((j.stalkMap Q.genericPoint).hom r₁) := (hr.map _).map _
      have ha : (j.stalkMap (genericPoint T)).hom ((M.presheaf.stalkSpecializes
          ((genericPoint_specializes x).map j.base.hom.continuous)).hom r) =
          algebraMap (T.presheaf.stalk Q.genericPoint) T.functionField
            ((j.stalkMap Q.genericPoint).hom r₁) := by
        have e1 : (M.presheaf.stalkSpecializes
            ((genericPoint_specializes x).map j.base.hom.continuous)).hom r =
            (M.presheaf.stalkSpecializes (j.base.hom.map_specializes hTQ)).hom r₁ := by
          change _ = (M.presheaf.stalkSpecializes hQx' ≫
            M.presheaf.stalkSpecializes (j.base.hom.map_specializes hTQ)).hom r
          rw [TopCat.Presheaf.stalkSpecializes_comp]
        rw [e1]
        exact Scheme.Hom.stalkSpecializes_stalkMap_apply j _ _ hTQ r₁
      have ha0 : (j.stalkMap (genericPoint T)).hom ((M.presheaf.stalkSpecializes
          ((genericPoint_specializes x).map j.base.hom.continuous)).hom r) ≠ 0 := by
        rw [ha]; exact (hunit.map _).ne_zero
      rw [Q.ordForm_smul_of_topologicalKrullDim_eq hdT ha0 hρ''.1, ha,
        Q.ord_algebraMap_of_isUnit hunit]
      have := hρ''.2 Q ⟨x, hxQ, hxU⟩
      push_cast at this ⊢
      linarith
  · intro σ' hσ'
    obtain ⟨D', hD', hp⟩ := hpull (N + 1) (Nat.succ_pos N) DM hDM hDMc
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_ne_zero hdT' hρσ0 σ'
    have hc0 : c ≠ 0 := by rintro rfl; exact hσ' (zero_smul _ _)
    exact isCartierDivisor_smul_divisorOfForm_add hdT hρσ0 ⟨D', hD', hp.isCartier hDMc⟩ hc0

/-- Transport of `GeneratesOn` along an equality of structure morphisms. -/
private theorem generatesOn_of_heq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {s s' : X ⟶ Spec (.of k)} (h : s' = s) {d m : ℕ} {B : QDivisor X} {U : X.Opens}
    {ρ : RationalPluriForms s' d m} {τ : RationalPluriForms s d m} (hρ : HEq ρ τ)
    (hτ : GeneratesOn B m U τ) : GeneratesOn B m U ρ := by
  subst h
  rw [eq_of_heq hρ]
  exact hτ

/-- Transport of the Cartier condition on adjoints along an equality of structure morphisms. -/
private theorem isCartierDivisor_of_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {s s' : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    [LocallyOfFiniteType s']
    (h : s' = s) {d m : ℕ} {B : QDivisor X}
    (hC : ∀ σ : RationalPluriForms s d 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor) :
    ∀ σ : RationalPluriForms s' d 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor := by
  subst h
  exact hC

/-- The final stratum of a flag on a compact scheme is compact. -/
private theorem compactSpace_of_stratumAdjunctionData {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X} {S : Scheme.{0}}
    {ι : S ⟶ X}
    {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) : CompactSpace S :=
  haveI := F.isClosedImmersion
  ι.isClosedEmbedding.compactSpace

/-- **Adjunction for local generators along a flag.** -/
private theorem flag_generatesOn [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX]
    {B : QDivisor X} {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    (hm : 0 < m) {U : X.Opens} {τ : RationalPluriForms sX n m} (hτ : GeneratesOn B m U τ)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, e + F.length = n → e ≠ 0 → ((ι ⁻¹ᵁ U : S.Opens) : Set S).Nonempty →
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    topologicalKrullDim S = e ∧
      (∀ σ : RationalPluriForms (ι ≫ sX) e 1, σ ≠ 0 →
        ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BS)).IsCartierDivisor) ∧
      (∃ ρ : RationalPluriForms (ι ≫ sX) e m, IsIteratedResidue sX B τ F e ρ) ∧
      ∀ ρ : RationalPluriForms (ι ≫ sX) e m, IsIteratedResidue sX B τ F e ρ →
        GeneratesOn BS m (ι ⁻¹ᵁ U) ρ := by
  induction F with
  | refl h =>
    intro e he _ _
    simp only [StratumAdjunctionData.length, add_zero] at he
    subst he
    refine ⟨hn, isCartierDivisor_of_eq (Category.id_comp sX) hC,
      ⟨_, IsIteratedResidue.refl h⟩, fun ρ hρ => ?_⟩
    obtain ⟨-, hρτ⟩ := hρ.rec'
    exact (generatesOn_of_heq (Category.id_comp sX) hρτ hτ).mono fun x hx => hx
  | @step S T ι BS F j BT hj ih =>
    intro e he he0 hU
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : IsNormal T := hj.1.2
    haveI : IsClosedImmersion j := by obtain ⟨-, -, -, -, h, -⟩ := hj; exact h
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    have he' : (e + 1) + F.length = n := by
      simp only [StratumAdjunctionData.length] at he; omega
    have hU' : ((ι ⁻¹ᵁ U : S.Opens) : Set S).Nonempty := by
      obtain ⟨x, hx⟩ := hU
      exact ⟨j x, hx⟩
    obtain ⟨hdS, hCS, ⟨ρ₀, hρ₀⟩, hgen⟩ := ih he' (Nat.succ_ne_zero e) hU'
    have hdS' : topologicalKrullDim S = (e : WithBot ℕ∞) + 1 := by rw [hdS]; norm_cast
    have hV : ((j ⁻¹ᵁ (ι ⁻¹ᵁ U) : T.Opens) : Set T).Nonempty := hU
    obtain ⟨⟨ρ', hρ'⟩, hgen', hCT⟩ := adjunctionStep_generatesOn F.isNormalVariety hdS' he0 hj hm
      hCS (hgen ρ₀ hρ₀) hV
    haveI : LocallyOfFiniteType ((j ≫ ι) ≫ sX) := by rw [Category.assoc]; infer_instance
    refine ⟨?_, isCartierDivisor_of_eq (Category.assoc j ι sX) hCT,
      ⟨_, IsIteratedResidue.step hρ₀ hρ'⟩, fun ρ hρ => ?_⟩
    · exact IsAdjunctionStep.topologicalKrullDim_eq' hdS' hj
    · obtain ⟨σ₀, hσ₀, σ', hσ', hρσ⟩ := hρ.rec'
      have h1 := IsIteratedResidue.unique (IsIteratedResidue.of_rec F hσ₀) hρ₀
      subst h1
      have h2 := hgen' _ hσ'
      exact (generatesOn_of_heq (Category.assoc j ι sX) hρσ h2).mono fun x hx => hx

/-- Casting a rational pluriform along an equality of structure morphisms commutes with scalar
multiplication. -/
private theorem cast_smul_rationalPluriForms {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (hs : s = s') {d : ℕ} {m : ℤ}
    (e : RationalPluriForms s d m = RationalPluriForms s' d m) (c : X.functionField)
    (τ : RationalPluriForms s d m) : cast e (c • τ) = c • cast e τ := by
  subst hs
  rfl

/-- **Iterated residues are linear over functions regular along the stratum**:
`Res_F(r τ) = r̄ Res_F(τ)` for `r` in the local ring at the generic point of the final stratum. -/
private theorem IsIteratedResidue.algebraMap_smul {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {n m : ℕ}
    {τ : RationalPluriForms sX n m} {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    [IsIntegral S] {F : StratumAdjunctionData sX B ι BS} {e : ℕ}
    {ρ : RationalPluriForms (ι ≫ sX) e m} (h : IsIteratedResidue sX B τ F e ρ) :
    ∀ r : X.presheaf.stalk (ι (genericPoint S)),
      IsIteratedResidue sX B (algebraMap _ X.functionField r • τ) F e
        ((ι.stalkMap (genericPoint S)).hom r • ρ) := by
  induction h with
  | refl hp =>
    intro r
    have h1 := IsIteratedResidue.refl (τ := algebraMap _ X.functionField r • τ) hp
    rw [cast_smul_rationalPluriForms (Category.id_comp sX).symm] at h1
    convert h1 using 2
    rw [Scheme.Hom.stalkMap_id]
    change r = (X.presheaf.stalkSpecializes (specializes_refl _)).hom r
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  | @step S T ι BS _ _ _ F j BT hj e ρ ρ' hF hr ih =>
    intro r
    have hsp : genericPoint S ⤳ j (genericPoint T) := genericPoint_specializes _
    have h1 := ih ((X.presheaf.stalkSpecializes (ι.base.hom.map_specializes hsp)).hom r)
    have e1 : algebraMap (X.presheaf.stalk (ι (genericPoint S))) X.functionField
        ((X.presheaf.stalkSpecializes (ι.base.hom.map_specializes hsp)).hom r) =
        algebraMap _ X.functionField r := MMP.Mori.algebraMap_stalkSpecializes _ r
    have e2 : (ι.stalkMap (genericPoint S)).hom
        ((X.presheaf.stalkSpecializes (ι.base.hom.map_specializes hsp)).hom r) =
        algebraMap (S.presheaf.stalk (j (genericPoint T))) S.functionField
          ((ι.stalkMap (j (genericPoint T))).hom r) :=
      Scheme.Hom.stalkSpecializes_stalkMap_apply ι _ _ hsp r
    rw [e1, e2] at h1
    have h2 := MMP.CyclicChartDifferent.Aux.IsPoincareResidue.algebraMap_smul hr
      ((ι.stalkMap (j (genericPoint T))).hom r)
    have h3 := IsIteratedResidue.step (hj := hj) h1 h2
    rw [cast_smul_rationalPluriForms (Category.assoc j ι sX).symm] at h3
    convert h3 using 2
    rw [Scheme.Hom.stalkMap_comp]
    rfl

/-- Moving a divisor over `X` along an equality of structure morphisms. -/
private theorem exists_divisorOver_of_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {s s' : X ⟶ Spec (.of k)} (h : s = s') {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (G : DivisorOver k s) {a : ℚ} (ha : IsDiscrepancy s n K B G a) :
    ∃ G' : DivisorOver k s', (G.IsExceptional → G'.IsExceptional) ∧
      G'.f G'.E.genericPoint = G.f G.E.genericPoint ∧ IsDiscrepancy s' n K B G' a := by
  subst h
  exact ⟨G, id, rfl, ha⟩

/-- The Cartier condition along a flag, from a generator on `X` near the stratum. -/
private theorem isCartierDivisor_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {B : QDivisor X} {n m : ℕ} (hn : topologicalKrullDim X = n) (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS)
    {e : ℕ} (he : e + F.length = n) (he0 : e ≠ 0) :
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    topologicalKrullDim S = e ∧ ∀ σ : RationalPluriForms (ι ≫ sX) e 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BS)).IsCartierDivisor := by
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  obtain ⟨K₀, hK₀, hCK⟩ := exists_isCanonicalDivisor_isCartierDivisor hX hn hC
  have hPX : Mori.IsPair sX B := ⟨hX, n, K₀, hK₀, ⟨m, by exact_mod_cast hm.ne', hCK⟩⟩
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  obtain ⟨-, U₀, hU₀, τ₀, hτ₀⟩ := MMP.Positivity.IsPair.exists_generatesOn hPX hK₀ hCK (ι x₀)
  obtain ⟨hdS, hCS, -, -⟩ := flag_generatesOn hn hC hm hτ₀ F he he0 ⟨x₀, hU₀⟩
  exact ⟨hdS, hCS⟩

/-- **The boundaries along a flag on an effective pair are effective.** -/
private theorem nonneg_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {B : QDivisor X} (hB0 : ∀ Q, 0 ≤ B.coeff Q) {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, e + F.length = n → ∀ Q, 0 ≤ BS.coeff Q := by
  induction F with
  | refl h => intro e _ Q; exact hB0 Q
  | @step S T ι BS F j BT hj ih =>
    intro e he Q
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : IsNormal T := hj.1.2
    have he' : (e + 1) + F.length = n := by
      simp only [StratumAdjunctionData.length] at he; omega
    have hBS0 := ih he'
    obtain ⟨hdS, hCS⟩ :=
      isCartierDivisor_of_stratumAdjunctionData hX hn hm hC F he' (Nat.succ_ne_zero e)
    have hdS' : topologicalKrullDim S = (e : WithBot ℕ∞) + 1 := by rw [hdS]; norm_cast
    obtain ⟨hTv, P, hP1, hPr, hjc, -⟩ := id hj
    haveI := hjc
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    set B₀ : QDivisor S := BS - Finsupp.single P 1 with hB₀
    have hB₀P : Finsupp.single P 1 + B₀ = BS := by rw [hB₀]; abel
    obtain ⟨hB0', hBP⟩ := hj.sub_single_nonneg hBS0 hPr
    have hB0 : B₀.IsEffective := hB0'
    obtain ⟨τ, hτ0, hτP, -, ρ, hρ, -, -⟩ :=
      MMP.Fourfold.exists_form_of_residue_order (ι ≫ sX) F.isNormalVariety hdS' j hTv P hPr Q
    have hDQ : (Divisor.toQDivisor (divisorOfForm τ) + BS).IsQCartier :=
      ⟨m, by exact_mod_cast hm.ne', hCS τ hτ0⟩
    obtain ⟨hgen, hpull⟩ := IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue hj
      hdS' P hPr τ hτ0 hτP ρ hρ hDQ
    have hBB : Divisor.toQDivisor (divisorOfForm τ) + Finsupp.single P 1 + B₀ =
        Divisor.toQDivisor (divisorOfForm τ) + BS := by rw [add_assoc, hB₀P]
    have key : ∀ L : QDivisor S, L = Divisor.toQDivisor (divisorOfForm τ) + BS →
        ∃ hg, L.IsPullback j hg (Divisor.toQDivisor (divisorOfForm ρ) + BT) := by
      rintro L rfl; exact ⟨hgen, hpull⟩
    obtain ⟨hgen', hpull'⟩ := key _ hBB
    exact coeff_nonneg_of_isPullback_divisorOfForm_isPoincareResidue_of_charZero (ι ≫ sX)
      F.isNormalVariety hdS' j hTv P hPr B₀ hB0 hBP τ hτ0 hτP ρ hρ (by rw [hBB]; exact hDQ) BT
      hgen' hpull' Q

/-- **Forward adjunction along a flag.** A divisor over the final stratum `S` of a flag on `X`
gives a divisor over `X`, exceptional unless the flag and the divisor are trivial, with the image
of the same centre and the same discrepancy. -/
private theorem exists_isDiscrepancy_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX)
    {B : QDivisor X} (hB0 : ∀ Q, 0 ≤ B.coeff Q) {n m : ℕ} (hn : topologicalKrullDim X = n)
    (hm : 0 < m)
    (hC : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
      ((m : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + B)).IsCartierDivisor)
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, e + F.length = n → e ≠ 0 →
    ∀ [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
      (KS : Divisor S), KS.IsCanonicalDivisor (ι ≫ sX) e →
    ∀ (G : DivisorOver k (ι ≫ sX)) (a : ℚ), IsDiscrepancy (ι ≫ sX) e KS BS G a →
    ∃ (K : Divisor X) (E : DivisorOver k sX), K.IsCanonicalDivisor sX n ∧
      (G.IsExceptional ∨ F.length ≠ 0 → E.IsExceptional) ∧
      ι (G.f G.E.genericPoint) = E.f E.E.genericPoint ∧ IsDiscrepancy sX n K B E a := by
  induction F with
  | refl h =>
    intro e he _ _ _ _ KS hKS G a ha
    simp only [StratumAdjunctionData.length, add_zero] at he
    subst he
    obtain ⟨G', hG'e, hG'c, hG'a⟩ := exists_divisorOver_of_eq (Category.id_comp sX) G ha
    refine ⟨KS, G', (Category.id_comp sX) ▸ hKS, fun h' => ?_, ?_, hG'a⟩
    · rcases h' with h' | h'
      · exact hG'e h'
      · exact absurd rfl h'
    · rw [hG'c]; rfl
  | @step S T ι BS F j BT hj ih =>
    intro e he he0 _ _ _ KT hKT G a ha
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
    haveI : IsNormal S := F.isNormalVariety.2
    haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
    haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    haveI : IsIntegral T := hj.1.1.toIsIntegral
    haveI : IsLocallyNoetherian T := by
      have := hj.1.1
      exact LocallyOfFiniteType.isLocallyNoetherian (j ≫ ι ≫ sX)
    haveI : IsNormal T := hj.1.2
    haveI : IsClosedImmersion j := by obtain ⟨-, -, -, -, h, -⟩ := hj; exact h
    haveI : CompactSpace T := j.isClosedEmbedding.compactSpace
    haveI : LocallyOfFiniteType (j ≫ ι ≫ sX) := hj.1.1.toLocallyOfFiniteType
    have he' : (e + 1) + F.length = n := by
      simp only [StratumAdjunctionData.length] at he; omega
    have hdS : topologicalKrullDim S = ((e + 1 : ℕ) : WithBot ℕ∞) := by
      have h1 := topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX)
      have h2 := StratumAdjunctionData.dim_add_length hn F h1
      rw [h1]; congr 1; omega
    have hdS' : topologicalKrullDim S = (e : WithBot ℕ∞) + 1 := by rw [hdS]; norm_cast
    obtain ⟨-, hCS⟩ :=
      isCartierDivisor_of_stratumAdjunctionData hX hn hm hC F he' (Nat.succ_ne_zero e)
    have hBS0 := nonneg_of_stratumAdjunctionData hX hB0 hn hm hC F he'
    -- a canonical divisor on `S`, and the pair `(S, B_S)`
    obtain ⟨KS, hKS, hCKS⟩ :=
      exists_isCanonicalDivisor_isCartierDivisor F.isNormalVariety hdS hCS
    have hPS : Mori.IsPair (ι ≫ sX) BS :=
      ⟨F.isNormalVariety, e + 1, KS, hKS, ⟨m, by exact_mod_cast hm.ne', hCKS⟩⟩
    -- the adjunction step `T ⊂ S`
    obtain ⟨hTv, P, hP1, hPr, hjc, -⟩ := id hj
    set B₀ : QDivisor S := BS - Finsupp.single P 1 with hB₀
    have hB₀P : Finsupp.single P 1 + B₀ = BS := by rw [hB₀]; abel
    obtain ⟨hB0, hBP⟩ := hj.sub_single_nonneg hBS0 hPr
    have hD : ∃ m' : ℕ, 0 < m' ∧ ((m' : ℤ) • (Divisor.toQDivisor KS +
        (Finsupp.single P 1 + B₀))).IsCartierDivisor :=
      ⟨m, hm, by rw [hB₀P]; exact hCKS⟩
    have hBSloc : ∃ m' : ℕ, 0 < m' ∧ ∀ x : T, ∃ U : S.Opens, j.base x ∈ U ∧
        ∃ τ : RationalPluriForms (ι ≫ sX) (e + 1) m',
          GeneratesOn (Finsupp.single P 1 + B₀) m' U τ ∧
          ∃ ρ : RationalPluriForms (j ≫ ι ≫ sX) e m',
            IsPoincareResidue (ι ≫ sX) j e m' τ ρ ∧ GeneratesOn BT m' (j ⁻¹ᵁ U) ρ := by
      refine ⟨m, hm, fun x => ?_⟩
      obtain ⟨-, U, hxU, τ, hτ⟩ := MMP.Positivity.IsPair.exists_generatesOn hPS hKS hCKS (j x)
      obtain ⟨⟨ρ, hρ⟩, hgen, -⟩ :=
        adjunctionStep_generatesOn F.isNormalVariety hdS' he0 hj hm hCS hτ ⟨x, hxU⟩
      exact ⟨U, hxU, τ, by rw [hB₀P]; exact hτ, ρ, hρ, hgen ρ hρ⟩
    -- forward adjunction along the step, then along the shorter flag
    obtain ⟨G', hG'e, hG'c, hG'a⟩ := exists_divisorOver_of_eq (Category.assoc j ι sX) G ha
    have hKT' : KT.IsCanonicalDivisor (j ≫ ι ≫ sX) e := (Category.assoc j ι sX) ▸ hKT
    obtain ⟨E₁, hE₁, hcen₁, hiff⟩ := exists_isExceptional_isDiscrepancy_iff_of_isPoincareResidue
      (ι ≫ sX) F.isNormalVariety e KS hKS P j hj.1 hPr KT hKT' B₀ hB0 hBP hD BT hBSloc G'
    have ha₁ : IsDiscrepancy (ι ≫ sX) (e + 1) KS BS E₁ a := by
      have := (hiff a).mp hG'a
      rwa [hB₀P] at this
    obtain ⟨K, E, hK, hEe, hcen, hEa⟩ := ih he' (Nat.succ_ne_zero e) KS hKS E₁ a ha₁
    refine ⟨K, E, hK, fun _ => hEe (Or.inl hE₁), ?_, hEa⟩
    rw [← hcen]
    change ι (j (G.f G.E.genericPoint)) = ι (E₁.f E₁.E.genericPoint)
    rw [← hG'c]
    exact congrArg ι hcen₁

/-- On a scheme of dimension `n`, every point has coheight at most `n`. -/
private theorem coheight_le_of_topologicalKrullDim_eq {Y : Scheme.{0}} {n : ℕ}
    (hn : topologicalKrullDim Y = n) (y : Y) : Order.coheight y ≤ n := by
  have h : (Order.coheight y : WithBot ℕ∞) ≤ topologicalKrullDim Y :=
    (Order.coheight_le_krullDim y).trans_eq
      (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))).symm
  rw [hn] at h
  exact_mod_cast h

/-- **The final stratum of a flag of length at least two on a dlt pair is a dlt stratum.**
Forward adjunction along the flag turns the step divisor, of discrepancy `≤ -1` on the
penultimate stratum, into an exceptional divisor over `X` with center `x = ι(η_S)` and
discrepancy `≤ -1`. By dlt, `x` lies in the snc open `U`, and the snc bound forces exactly
`codim x` components of `⌊B⌋` through `x`; they cut out `S` near `x`. -/
private theorem isDltStratum_range_step [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) {S T : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) {j : T ⟶ S} {BT : QDivisor T}
    (hj : IsAdjunctionStep (ι ≫ sX) BS j BT) (hF : F.length ≠ 0) :
    IsDltStratum sX B (Set.range (j ≫ ι).base) := by
  classical
  obtain ⟨⟨hP, hnn, -⟩, -, -⟩ := id hB
  obtain ⟨hX, n, K, hK, hQ⟩ := hP
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  obtain ⟨m, hm, hCK⟩ := hQ.exists_pos
  have hC := isCartierDivisor_divisorOfForm_add hX hK hCK
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
  haveI : IsNormal S := F.isNormalVariety.2
  haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
  haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
  haveI : IsClosedImmersion ι := F.isClosedImmersion
  obtain ⟨e, hdS, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e ∧ e + F.length = n :=
    ⟨_, topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX), StratumAdjunctionData.dim_add_length hn F
      (topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX))⟩
  have hBS0 := nonneg_of_stratumAdjunctionData hX hnn hn hm hC F he
  obtain ⟨hTv, P, hP1, hPr, hjc, -⟩ := id hj
  have he0 : e ≠ 0 := by
    rintro rfl
    have := coheight_le_of_topologicalKrullDim_eq hdS P.genericPoint
    rw [P.coheight_genericPoint] at this
    exact absurd this (by decide)
  obtain ⟨-, hCS⟩ := isCartierDivisor_of_stratumAdjunctionData hX hn hm hC F he he0
  obtain ⟨KS, hKS, hCKS⟩ := exists_isCanonicalDivisor_isCartierDivisor F.isNormalVariety hdS hCS
  have hPS : IsPairWith (ι ≫ sX) e KS BS :=
    ⟨F.isNormalVariety, hKS, m, by exact_mod_cast hm.ne', hCKS⟩
  -- the step divisor `P`, as a divisor over `S`, has discrepancy `-coeff_P B_S ≤ -1`
  set G := DivisorOver.ofPrimeDivisor k F.isNormalVariety P with hG
  have hGc : G.f G.E.genericPoint = P.genericPoint := rfl
  have hGex : ¬ G.IsExceptional := by
    rw [isExceptional_iff_two_le_coheight F.isNormalVariety, hGc, P.coheight_genericPoint]
    decide
  obtain ⟨D, hDc, hDa⟩ := MMP.Mori.DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hPS G hGex
  have hDP : D = P := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hDc,
      DivisorOver.center_eq_closure_genericPoint, hGc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have ha : -BS.coeff D ≤ -1 := by rw [hDP]; linarith
  -- forward adjunction along the flag
  obtain ⟨K', E, hK', hEex, hcen, hEa⟩ :=
    exists_isDiscrepancy_of_stratumAdjunctionData hX hnn hn hm hC F he he0 KS hKS G _ hDa
  have hEexc : E.IsExceptional := hEex (Or.inr hF)
  have hx2 : 2 ≤ Order.coheight (E.f E.E.genericPoint) :=
    (isExceptional_iff_two_le_coheight hX E).mp hEexc
  -- the open `U` of the dlt condition contains the center `x`
  obtain ⟨hPw, hcoeff, U, hUsm, hsnc, hZ⟩ :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK' B).mp hB
  have hxU : E.f E.E.genericPoint ∈ U := by
    by_contra hxU
    have hsub : (E.center : Set X) ⊆ (U : Set X)ᶜ := by
      rw [DivisorOver.center_eq_closure_genericPoint]
      exact closure_minimal (Set.singleton_subset_iff.mpr hxU) U.isOpen.isClosed_compl
    have := hZ E _ hsub hEa
    linarith
  have hEU : ((E.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl, hxU⟩
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  obtain ⟨hY, hf, E', hE', -, hiff⟩ :=
    MMP.Mori.DivisorOver.exists_restrict_isDiscrepancy_iff hPw E U hEU
  set E'' : DivisorOver k (U.ι ≫ sX) := ⟨_, E.f ∣_ U, hY, hf, E'⟩ with hE''
  have hE''c : U.ι (E''.f E''.E.genericPoint) = E.f E.E.genericPoint := by
    change U.ι ((E.f ∣_ U) E'.genericPoint) = _
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hE']
    exact congrArg E.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ E').symm
  have hcU : Order.coheight (E''.f E''.E.genericPoint) = Order.coheight (E.f E.E.genericPoint) := by
    rw [← hE''c]; exact (coheight_eq_of_isOpenImmersion U.ι).symm
  have hPU := hPw.restrictOpen U
  have hE''ex : E''.IsExceptional :=
    (isExceptional_iff_two_le_coheight hPU.1 E'').mpr (by rw [hcU]; exact hx2)
  have hE''a := (hiff _).mp hEa
  have hUsm' : IsSmoothScheme (U.ι ≫ sX) := by
    rw [isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
    intro y _
    have h := hUsm y.2
    rw [smoothLocus_eq_smoothLocus] at h
    exact h
  have hsnc' : DivisorWithCoeffs.IsSNC (U.ι ≫ sX)
      (∑ E ∈ (B.restrictOpen U).support, Finsupp.single E (1 : ℤ)) :=
    hsnc.of_support_subset <| Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
      fun E hE => Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE)
  obtain ⟨c, Tc, hc, hT, hc2, hcard, hTS, hTx, hle⟩ := MMP.Mori.le_isDiscrepancy_of_isSNC hPU.1
    hUsm' hPU.2.1 le_rfl hsnc' (fun E _ => (hcoeff _).2) E'' hE''ex hE''a
  -- every component through the center has coefficient one, and there are `c` of them
  have hnnT : ∀ G ∈ Tc, 0 ≤ 1 - (B.restrictOpen U).coeff G := fun G _ => by
    have := (hcoeff (OpenWeilRestriction.primeDivisorMap U.ι G)).2
    change (0 : ℚ) ≤ 1 - B.coeff (OpenWeilRestriction.primeDivisorMap U.ι G)
    linarith
  have hsum0 := Finset.sum_nonneg hnnT
  have hcardq : (Tc.card : ℚ) ≤ c := by exact_mod_cast hcard
  have hsum : ∑ G ∈ Tc, (1 - (B.restrictOpen U).coeff G) = 0 := by linarith
  have hcT : Tc.card = c := by
    have : (c : ℚ) = Tc.card := by linarith
    exact_mod_cast this.symm
  have hT1 : ∀ G ∈ Tc, B.coeff (OpenWeilRestriction.primeDivisorMap U.ι G) = 1 := fun G hG => by
    have := (Finset.sum_eq_zero_iff_of_nonneg hnnT).mp hsum G hG
    have h' : (B.restrictOpen U).coeff G = 1 := by linarith
    exact h'
  -- the center `x` and the range of the stratum
  set x := E.f E.E.genericPoint with hx
  have hxP : x = ι P.genericPoint := hcen.symm
  have hrange : Set.range (j ≫ ι).base = closure {x} := by
    have h1 : Set.range (j ≫ ι).base = ι.base '' Set.range j.base := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨j t, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, rfl⟩
    rw [h1, hPr, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hxP]
  have hcl : ∀ Q : Mori.PrimeDivisor X, IsClosed (Q.support : Set X) := fun Q => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hxmem : ∀ G ∈ Tc, x ∈ (OpenWeilRestriction.primeDivisorMap U.ι G).support :=
    fun G hG => by
      rw [← hE''c]
      exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι G _).mpr
        (hTx G hG)
  refine ⟨hB, Tc.image (OpenWeilRestriction.primeDivisorMap U.ι), ?_, ?_, ?_, ?_⟩
  · rw [Finset.image_nonempty, ← Finset.card_pos, hcT]; omega
  · intro P' hP'
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hP'
    rw [hT1 G hG]
  · refine ⟨x, Set.mem_iInter₂.mpr fun P' hP' => ?_⟩
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hP'
    exact hxmem G hG
  · rw [hrange]
    refine ⟨⟨isIrreducible_singleton.closure, fun y hy => Set.mem_iInter₂.mpr fun P' hP' => ?_⟩,
      fun T' hT' hsub => ?_⟩
    · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hP'
      exact closure_minimal (Set.singleton_subset_iff.mpr (hxmem G hG))
        (hcl _) hy
    · obtain ⟨hT'irr, hT'sub⟩ := hT'
      have hy := hT'irr.isGenericPoint_genericPoint_closure
      set y := hT'irr.genericPoint
      have hxT' : x ∈ T' := hsub (subset_closure rfl)
      have hyx : y ⤳ x := hy.specializes (subset_closure hxT')
      have hyU : y ∈ U := hyx.mem_open U.isOpen hxU
      have hyJ : ∀ G ∈ Tc, (⟨y, hyU⟩ : U.toScheme) ∈ G.support := fun G hG => by
        refine (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι G _).mp ?_
        have h1 : T' ⊆ (OpenWeilRestriction.primeDivisorMap U.ι G).support := fun z hz =>
          Set.mem_iInter₂.mp (hT'sub hz) _ (Finset.mem_image_of_mem _ hG)
        exact closure_minimal h1 (hcl _) hy.mem
      -- `y` lies on `c` components of an snc divisor, so it has coheight at least `c`
      obtain ⟨N, z, jj, hz, hjj, -⟩ := MMP.Mori.exists_at_of_isSNC hsnc' ⟨y, hyU⟩
      have hcN : Tc.card ≤ N := by
        have h := Fintype.card_le_of_injective
          (fun G : Tc => jj ⟨G.1, hTS G.2, hyJ G.1 G.2⟩)
          (fun a b hab => by
            have h := hjj hab
            simp only [Subtype.mk.injEq] at h
            exact Subtype.ext h)
        simpa using h
      have hcy : (c : ℕ∞) ≤ Order.coheight y := by
        have h := ringKrullDim_stalk_eq_coheight (X := U.toScheme) ⟨y, hyU⟩
        rw [hz.2] at h
        have h2 := coheight_eq_of_isOpenImmersion (x := (⟨y, hyU⟩ : U.toScheme)) U.ι
        have h3 : (N : ℕ∞) = Order.coheight (U.ι ⟨y, hyU⟩) := by rw [h2]; exact_mod_cast h
        change (c : ℕ∞) ≤ Order.coheight (U.ι ⟨y, hyU⟩)
        rw [← h3]
        exact_mod_cast hcT ▸ hcN
      have hcx : Order.coheight x = c := by rw [← hcU, ← hc]
      have hyeq : y = x := by
        by_contra hne
        have hlt : x < y := lt_of_le_not_ge hyx fun h => hne (hyx.antisymm h).eq
        have hfin : Order.coheight y ≠ ⊤ :=
          ne_top_of_le_ne_top (by simp) (coheight_le_of_topologicalKrullDim_eq hn y)
        have := Order.coheight_strictAnti hlt (lt_top_iff_ne_top.mpr hfin)
        rw [hcx] at this
        exact absurd hcy (not_le.mpr this)
      rw [hyeq] at hy
      exact fun w hw => (isGenericPoint_def.mp hy) ▸ subset_closure hw

end FlagAdjunction

/-! ### The final stratum of a flag on a dlt pair -/

section Flag

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)} {B : QDivisor X}

/-- A prime divisor with coefficient at least one in the boundary of a dlt pair is a dlt
stratum. -/
private theorem isDltStratum_support (hB : MMP.Intersection.IsDltPair sX B)
    (P : Mori.PrimeDivisor X) (hP : 1 ≤ B.coeff P) : IsDltStratum sX B (P.support : Set X) := by
  have hinter : (⋂ Q ∈ ({P} : Finset (Mori.PrimeDivisor X)), (Q.support : Set X)) =
      (P.support : Set X) := by simp
  refine ⟨hB, {P}, Finset.singleton_nonempty P, by simpa using hP, ?_, ?_⟩
  · rw [hinter]
    exact ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  · rw [hinter]
    refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure

/-- **The final stratum of a flag of positive length on a dlt pair is a dlt stratum.** -/
private theorem isDltStratum_range_of_stratumAdjunctionData [IsAlgClosed k] [CharZero k]
    (hB : MMP.Intersection.IsDltPair sX B) {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) (hF : 0 < F.length) :
    IsDltStratum sX B (Set.range ι.base) := by
  cases F with
  | refl h => simp [StratumAdjunctionData.length] at hF
  | step F₀ j BT hj =>
    by_cases h0 : F₀.length = 0
    · cases F₀ with
      | refl h =>
        obtain ⟨-, P, hP1, hPr, -⟩ := hj
        have hr : Set.range (j ≫ 𝟙 X).base = (P.support : Set X) := by
          rw [Category.comp_id]; exact hPr
        rw [hr]
        exact isDltStratum_support hB P hP1
      | step => simp [StratumAdjunctionData.length] at h0
    · exact isDltStratum_range_step hB F₀ hj h0

/-- The generic point of the final stratum of a flag on a dlt pair lies outside the exceptional
set of a small morphism, provided no dlt stratum lies in that exceptional set. -/
private theorem genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData [IsAlgClosed k]
    [CharZero k] {Z : Scheme.{0}} {f : X ⟶ Z} (h2 : 2 ≤ closedsCodimension (exceptionalSet f))
    (hB : MMP.Intersection.IsDltPair sX B)
    (hstrata : ∀ T : Set X, IsDltStratum sX B T → ¬ T ⊆ (exceptionalSet f : Set X))
    {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    ι (genericPoint S) ∉ (exceptionalSet f : Set X) := by
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  intro hmem
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · cases F with
    | refl h =>
      have h2x := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 hmem
      have hmaxX : IsMax ((𝟙 X : X ⟶ X) (genericPoint X)) := fun z _ ↦ genericPoint_specializes z
      rw [Order.coheight_eq_zero.mpr hmaxX] at h2x
      exact absurd h2x (by decide)
    | step => simp [StratumAdjunctionData.length] at h0
  · refine hstrata _ (isDltStratum_range_of_stratumAdjunctionData hB F hpos) ?_
    rintro _ ⟨s, rfl⟩
    have hsp : ι (genericPoint S) ⤳ ι s := (genericPoint_specializes s).map ι.base.hom.continuous
    exact hsp.mem_closed (exceptionalSet f).isClosed hmem

end Flag

/-! ### The G-argument on a common model -/

section GArgument

variable {k : Type} [Field k]

/-- **Restriction to a dominating stratum commutes with pull-back.** If `h ≫ p = p_F ≫ ι` and
`p_F` maps the generic point of `F'` to that of `S`, then for `r` regular at `ι(η_S)` the
pull-back `p^* r` is regular at `h(η_{F'})` and restricts to `p_F^*(r|_S)` on `F'`. -/
private theorem exists_stalk_eq_functionFieldMap {F' S W X : Scheme.{0}} [IsIntegral F']
    [IsIntegral S] [IsIntegral W] [IsIntegral X] (h : F' ⟶ W) (pF : F' ⟶ S) (p : W ⟶ X) (ι : S ⟶ X)
    [IsDominant pF] [IsDominant p] (hhp : h ≫ p = pF ≫ ι)
    (hpFη : pF (genericPoint F') = genericPoint S) (r : X.presheaf.stalk (ι (genericPoint S))) :
    ∃ t : W.presheaf.stalk (h (genericPoint F')),
      algebraMap _ W.functionField t = functionFieldMap p (algebraMap _ X.functionField r) ∧
        (h.stalkMap (genericPoint F')).hom t =
          functionFieldMap pF ((ι.stalkMap (genericPoint S)).hom r) := by
  have hpt : p (h (genericPoint F')) = ι (genericPoint S) := by
    rw [← Scheme.Hom.comp_apply, hhp, Scheme.Hom.comp_apply, hpFη]
  have hsp : p (h (genericPoint F')) ⤳ ι (genericPoint S) := hpt ▸ specializes_rfl
  refine ⟨(p.stalkMap (h (genericPoint F'))).hom ((X.presheaf.stalkSpecializes hsp).hom r), ?_, ?_⟩
  · rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, MMP.Mori.algebraMap_stalkSpecializes]
  · have hS : pF (genericPoint F') ⤳ genericPoint S := hpFη ▸ specializes_rfl
    have hX : ι (pF (genericPoint F')) ⤳ ι (genericPoint S) := hS.map ι.base.hom.continuous
    have e1 : (h.stalkMap (genericPoint F')).hom ((p.stalkMap (h (genericPoint F'))).hom
        ((X.presheaf.stalkSpecializes hsp).hom r)) =
        ((h ≫ p).stalkMap (genericPoint F')).hom ((X.presheaf.stalkSpecializes hsp).hom r) := by
      rw [Scheme.Hom.stalkMap_comp]; rfl
    rw [e1, Scheme.Hom.stalkMap_congr_hom (h ≫ p) (pF ≫ ι) hhp, Scheme.Hom.stalkMap_comp]
    change (pF.stalkMap (genericPoint F')).hom ((ι.stalkMap (pF (genericPoint F'))).hom
      ((X.presheaf.stalkSpecializes hsp ≫ (X.presheaf.stalkCongr _).hom).hom r)) =
      (pF.stalkMap (genericPoint F')).hom ((S.presheaf.stalkSpecializes hS).hom
        ((ι.stalkMap (genericPoint S)).hom r))
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply ι _ _ hS r]
    congr 2
    have hq : ι (pF (genericPoint F')) ⤳ p (h (genericPoint F')) := by
      have e : (pF ≫ ι) (genericPoint F') = (h ≫ p) (genericPoint F') := by rw [hhp]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
      rw [e]
    change (X.presheaf.stalkSpecializes hsp ≫ X.presheaf.stalkSpecializes hq).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]

/-- On an integral scheme locally of finite type over `k` of dimension `n`, a closed point has
coheight `n`. -/
private theorem coheight_eq_of_isClosed {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y]
    [LocallyOfFiniteType sY] {n : ℕ} (hn : topologicalKrullDim Y = n) {y : Y}
    (hy : IsClosed ({y} : Set Y)) : Order.coheight y = n := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y
  have h0 : topologicalKrullDim (closure {y} : Set Y) = 0 := by
    rw [hy.closure_eq]
    apply le_antisymm (topologicalKrullDim_zero_of_discreteTopology _)
    have : Nonempty ({y} : Set Y) := ⟨⟨y, rfl⟩⟩
    have : Nonempty (TopologicalSpace.IrreducibleCloseds ({y} : Set Y)) :=
      ⟨⟨{⟨y, rfl⟩}, isIrreducible_singleton, isClosed_discrete _⟩⟩
    exact Order.krullDim_nonneg
  rw [hn, h0, zero_add] at h
  exact_mod_cast h

/-- Transport along an equality of structure morphisms commutes with scalar multiplication. -/
private theorem eqRec_smul_rationalPluriForms {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} (c : X.functionField)
    (v : RationalPluriForms s d m) :
    (h ▸ (c • v) : RationalPluriForms s' d m) = c • (h ▸ v : RationalPluriForms s' d m) := by
  subst h
  rfl

/-- A transport along an equality of structure morphisms is heterogeneously equal to the form. -/
private theorem eqRec_heq_rationalPluriForms {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} (v : RationalPluriForms s d m) :
    HEq (h ▸ v : RationalPluriForms s' d m) v := by
  subst h
  rfl

/-- Pull-backs along equal dominant morphisms agree. -/
private theorem pullbackRationalPluriForms_heq_of_eq {Y W : Scheme.{0}} [IsIntegral Y]
    [IsIntegral W] (sW : W ⟶ Spec (.of k)) {g g' : Y ⟶ W} (h : g = g') [IsDominant g]
    [IsDominant g'] {d : ℕ}
    {m : ℤ} (σ : RationalPluriForms sW d m) :
    HEq (pullbackRationalPluriForms sW g σ) (pullbackRationalPluriForms sW g' σ) := by
  subst h
  rfl

/-- A transport of a nonzero form is nonzero. -/
private theorem eqRec_ne_zero_rationalPluriForms {X : Scheme.{0}} [IsIntegral X]
    {s s' : X ⟶ Spec (.of k)} (h : s = s') {d : ℕ} {m : ℤ} {v : RationalPluriForms s d m}
    (hv : v ≠ 0) :
    (h ▸ v : RationalPluriForms s' d m) ≠ 0 := by
  subst h
  exact hv

/-- **Over the isomorphism locus of a flip the ratio of generators is a unit.** On a common model
`p, q` of a flip, let `τ`, `τ'` generate `𝒪_X(m(K + B))` near `p w` and `𝒪_{X⁺}(m(K⁺ + B⁺))` near
`q w`, with `f (p w)` in the biregular locus of `f`. Then `q^*τ' / p^*τ` is a unit at `w`: both
generators are, up to units at `p w` and `q w`, pull-backs of one rational form on `Z`. -/
private theorem exists_isUnit_of_mem_biregularLocus [IsAlgClosed k] [CharZero k]
    {X X' Z W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hflip : Mori.IsFlip sX sZ sX' K B f fp) (hK : K.IsCanonicalDivisor sX n)
    [IsIntegral W] {p : W ⟶ X} {q : W ⟶ X'} (hpb : IsBirationalMorphism p)
    (hqb : IsBirationalMorphism q) (hpq : p ≫ f = q ≫ fp)
    (hs : q ≫ sX' = p ≫ sX) {m : ℕ}
    {U : X.Opens} {τ : RationalPluriForms sX n m} (hτ : GeneratesOn B m U τ)
    {U' : X'.Opens} {τ' : RationalPluriForms sX' n m}
    (hτ' : GeneratesOn (flipTransform f fp B) m U' τ') {w : W} (hwU : p w ∈ U)
    (hwU' : q w ∈ U') (hwV : f (p w) ∈ biregularLocus f) {c : W.functionField}
    (hc : haveI : IsDominant p := hpb.isDominant
      haveI : IsDominant q := hqb.isDominant
      (hs ▸ pullbackRationalPluriForms sX' q τ' : RationalPluriForms (p ≫ sX) n m) =
        c • pullbackRationalPluriForms sX p τ) :
    ∃ r : W.presheaf.stalk w, IsUnit r ∧ algebraMap _ W.functionField r = c := by
  classical
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hFC := hflip.isFlippingContraction
  have hZ := hFC.isNormalVariety_target
  have hX := hFC.isNormalVariety_source
  have hX' := hflip.isNormalVariety
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsProper f := hFC.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsDominant f := hFC.isBirationalMorphism.isDominant
  haveI : IsDominant fp := hflip.isBirationalMorphism.isDominant
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have hcf : f ≫ sZ = sX := hFC.comp_eq
  have hcfp : fp ≫ sZ = sX' := hflip.comp_eq
  haveI : LocallyOfFiniteType (f ≫ sZ) := by rw [hcf]; infer_instance
  haveI : LocallyOfFiniteType (fp ≫ sZ) := by rw [hcfp]; infer_instance
  have hK' := hflip.isCanonicalDivisor_flipTransform hK
  have hdX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  have hfb := hFC.isBirationalMorphism.functionFieldMap_bijective
  have hfpb := hflip.isBirationalMorphism.functionFieldMap_bijective
  have hdZ : topologicalKrullDim Z = n := by
    haveI := hZ.1
    haveI := hX.1
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
      hFC.isBirationalMorphism, hdX]
  have hdZn := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hdZ
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdX
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hdX'
  -- a rational form `σ` on `Z` with `f^*σ = τ`
  obtain ⟨b1⟩ := MMP.Fourfold.exists_basis_topForms (sX := sZ) hdZ
  letI := functionFieldAlgebra sZ
  let B₀ : Module.Basis Unit Z.functionField (RationalPluriForms sZ n m) :=
    ZTensorPower.basis b1 m
  let σ₀ : RationalPluriForms sZ n m := B₀ ()
  have hσ₀ : σ₀ ≠ 0 := B₀.ne_zero ()
  have hP : (hcf ▸ pullbackRationalPluriForms sZ f σ₀ : RationalPluriForms sX n m) ≠ 0 :=
    eqRec_ne_zero_rationalPluriForms hcf
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f hfb hdZn hσ₀)
  obtain ⟨a, ha⟩ := exists_eq_smul_of_ne_zero hd hP τ
  obtain ⟨aZ, haZ⟩ := hfb.2 a
  have hτσ : τ = (hcf ▸ pullbackRationalPluriForms sZ f (aZ • σ₀) : RationalPluriForms sX n m) := by
    rw [ha, pullbackRationalPluriForms_smul', eqRec_smul_rationalPluriForms, haZ]
  set σ := aZ • σ₀ with hσ
  have hσ0 : σ ≠ 0 := by
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_smul] at ha; exact hτ.1 ha
    have haZ0 : aZ ≠ 0 := by rintro rfl; rw [map_zero] at haZ; exact ha0 haZ.symm
    exact smul_ne_zero haZ0 hσ₀
  -- `τ' = g' · f⁺^*σ`
  have hP' : (hcfp ▸ pullbackRationalPluriForms sZ fp σ : RationalPluriForms sX' n m) ≠ 0 :=
    eqRec_ne_zero_rationalPluriForms hcfp
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' fp hfpb hdZn hσ0)
  obtain ⟨g', hg'⟩ := exists_eq_smul_of_ne_zero hd' hP' τ'
  have hg'0 : g' ≠ 0 := by rintro rfl; rw [zero_smul] at hg'; exact hτ'.1 hg'
  -- so `c = q^*g'`
  have key : (hs ▸ pullbackRationalPluriForms sX' q
      (hcfp ▸ pullbackRationalPluriForms sZ fp σ : RationalPluriForms sX' n m) :
        RationalPluriForms (p ≫ sX) n m) = pullbackRationalPluriForms sX p τ := by
    apply eq_of_heq
    refine (eqRec_heq_rationalPluriForms hs _).trans ?_
    rw [pullbackRationalPluriForms_cast]
    refine (eqRec_heq_rationalPluriForms _ _).trans ?_
    rw [MMP.Flips.pullbackRationalPluriForms_comp fp q hfpb hqb.functionFieldMap_bijective hdZn]
    refine (pullbackRationalPluriForms_heq_of_eq sZ hpq.symm σ).trans ?_
    rw [hτσ, pullbackRationalPluriForms_cast]
    refine HEq.symm ((eqRec_heq_rationalPluriForms _ _).trans ?_)
    rw [MMP.Flips.pullbackRationalPluriForms_comp f p hfb hpb.functionFieldMap_bijective hdZn]
    exact HEq.rfl
  have hP0 : pullbackRationalPluriForms sX p τ ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hpb.functionFieldMap_bijective hd hτ.1
  have hcq : c = functionFieldMap q g' := by
    apply smul_left_injective W.functionField hP0
    simp only
    rw [← hc, hg', pullbackRationalPluriForms_smul', eqRec_smul_rationalPluriForms, key]
  -- `g'` is a unit at `q w`
  obtain ⟨V, hfV, hfpV, hXV, -, -⟩ := hflip.exists_opens_isIso
  obtain ⟨r', hr', hr'g⟩ := exists_isUnit_algebraMap_eq_of_ord_eq_zero (q w) hg'0 fun Γ' hΓ' => by
    have hΓ'V : fp Γ'.genericPoint ∈ biregularLocus fp :=
      map_genericPoint_mem_biregularLocus' hflip.two_le_codimension Γ'
    have hcQ : Order.coheight (fp Γ'.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hΓ'V, Γ'.coheight_genericPoint]
    set Q : Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcQ
    have hQ : fp Γ'.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcQ).symm
    have hQV : Q.genericPoint ∈ biregularLocus f :=
      MMP.Positivity.mem_biregularLocus_of_coheight_le_one f hfb hFC.two_le_codimension
        (by rw [Q.coheight_genericPoint])
    obtain ⟨x, hx⟩ := f.surjective Q.genericPoint
    have hxV : f x ∈ biregularLocus f := hx ▸ hQV
    have hcx : Order.coheight x = 1 := by
      rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f hxV, hx, Q.coheight_genericPoint]
    set Γ : Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hcx
    have hΓx : Γ.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcx
    have hΓ'w : Γ'.genericPoint ⤳ q w := by
      have : q w ∈ Γ'.support := hΓ'
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have hfpw : fp (q w) = f (p w) := by
      rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply]
    have hsp : f Γ.genericPoint ⤳ f (p w) := by
      rw [hΓx, hx, ← hQ, ← hfpw]
      exact hΓ'w.map fp.base.hom.continuous
    have hΓw : p w ∈ Γ.support := by
      have := specializes_of_map_specializes (by rw [hΓx]; exact hxV) hwV hsp
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact specializes_iff_mem_closure.mp this
    have e1 := hτ'.2 Γ' ⟨q w, hΓ', hwU'⟩
    have e2 := hτ.2 Γ ⟨p w, hΓw, hwU⟩
    have hPP : f Γ.genericPoint = fp Γ'.genericPoint := by rw [hΓx, hx, hQ]
    have hBB : (flipTransform f fp B).coeff Γ' = B.coeff Γ :=
      MMP.Mori.flipTransform_apply hZ (hFC.comp_eq ▸ hFC.isNormalVariety_source)
        hFC.isBirationalMorphism V hXV hPP B
    have o1 : Γ'.ordForm τ' = X'.ord g' Γ'.genericPoint +
        Γ'.ordForm (hcfp ▸ pullbackRationalPluriForms sZ fp σ : RationalPluriForms sX' n m) := by
      rw [hg']; exact Γ'.ordForm_smul_of_topologicalKrullDim_eq hdX' hg'0 hP'
    have o2 : Γ'.ordForm (hcfp ▸ pullbackRationalPluriForms sZ fp σ :
        RationalPluriForms sX' n m) = Q.ordForm σ := by
      rw [ordForm_cast]
      haveI : IsIso (fp.stalkMap Γ'.genericPoint) :=
        MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus fp hΓ'V
      exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso fp hfpb hdZn Γ' Q hQ σ
    have o3 : Γ.ordForm τ = Q.ordForm σ := by
      rw [hτσ, ordForm_cast]
      have hΓV : f Γ.genericPoint ∈ biregularLocus f := by rw [hΓx]; exact hxV
      haveI : IsIso (f.stalkMap Γ.genericPoint) :=
        MMP.Threefold.Resolution.isIso_stalkMap_of_mem_biregularLocus f hΓV
      exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hfb hdZn Γ Q
        (by rw [hΓx, hx]) σ
    rw [o1, o2, hBB] at e1
    rw [o3] at e2
    push_cast at e1 e2
    have : ((X'.ord g' Γ'.genericPoint : ℤ) : ℚ) = 0 := by linarith
    exact_mod_cast this
  refine ⟨(q.stalkMap w).hom r', hr'.map _, ?_⟩
  rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, hr'g, hcq]

/-- **The G-argument.** In the setting of
`IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair`, with flags `F`, `Fp` of the two
strata, the generic point of `S` off `Ex(f)` and `φ` an isomorphism of pairs over `Z`, no point of
`S` lies in `Ex(f)`. -/
private theorem notMem_exceptionalSet_of_isIso [IsAlgClosed k] [CharZero k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hXp : Mori.IsProjectiveVariety k sX) (hK : K.IsCanonicalDivisor sX n)
    (hflipOf : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    {S S' : Scheme.{0}} {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (F : StratumAdjunctionData sX B ι BS)
    (Fp : StratumAdjunctionData sX' (flipTransform f fp B) ι' BS')
    (φ : S ≅ S') (hφ : ι ≫ f = φ.hom ≫ ι' ≫ fp)
    (hφB : inverseTransformDivisor φ.hom BS' = BS)
    (hη : haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
      ι (genericPoint S) ∉ (exceptionalSet f : Set X))
    (s₀ : S) : ι s₀ ∉ (exceptionalSet f : Set X) := by
  haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
  haveI : IsLocallyNoetherian S := F.isLocallyNoetherian_stratum
  haveI : IsNormal S := F.isNormalVariety.2
  haveI : CompactSpace S := compactSpace_of_stratumAdjunctionData F
  haveI : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
  haveI : IsClosedImmersion ι := F.isClosedImmersion
  haveI : IsIntegral S' := Fp.isNormalVariety.1.toIsIntegral
  haveI : IsLocallyNoetherian S' := Fp.isLocallyNoetherian_stratum
  haveI : IsNormal S' := Fp.isNormalVariety.2
  haveI : CompactSpace S' := compactSpace_of_stratumAdjunctionData Fp
  haveI : LocallyOfFiniteType (ι' ≫ sX') := Fp.isNormalVariety.1.toLocallyOfFiniteType
  haveI : IsClosedImmersion ι' := Fp.isClosedImmersion
  intro hs₀
  have hV := biregularLocus_le_of_isFlipOf hflipOf
  have hflip := isFlip_of_isFlipOf hK hflipOf
  have hFC := hflip.isFlippingContraction
  have hK' := hflip.isCanonicalDivisor_flipTransform hK
  have hX := hFC.isNormalVariety_source
  have hX' := hflip.isNormalVariety
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  have hdX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hdX' : topologicalKrullDim X' = n := hK'.topologicalKrullDim_eq
  -- a common Cartier index `m` of `K + B` and `K⁺ + B⁺`
  obtain ⟨m₁, hm₁, D₁, hD₁, hD₁c⟩ := hFC.isQCartier.exists_pos
  obtain ⟨m₂, hm₂, D₂, hD₂, hD₂c⟩ := hflip.isQCartier.exists_pos
  have hm : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  have hC : (((m₁ * m₂ : ℕ) : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor :=
    ⟨(m₂ : ℤ) • D₁, by rw [map_zsmul, hD₁, smul_smul, Nat.cast_mul, mul_comm], hD₁c.zsmul _⟩
  have hC' : (((m₁ * m₂ : ℕ) : ℤ) • (Divisor.toQDivisor (flipTransform f fp K) +
      flipTransform f fp B)).IsCartierDivisor :=
    ⟨(m₁ : ℤ) • D₂, by rw [map_zsmul, hD₂, smul_smul, Nat.cast_mul], hD₂c.zsmul _⟩
  generalize m₁ * m₂ = m at hm hC hC'
  have hCX := isCartierDivisor_divisorOfForm_add hX hK hC
  have hCX' := isCartierDivisor_divisorOfForm_add hX' hK' hC'
  have hPX : Mori.IsPair sX B := ⟨hX, n, K, hK, hFC.isQCartier⟩
  have hPX' : Mori.IsPair sX' (flipTransform f fp B) := ⟨hX', n, _, hK', hflip.isQCartier⟩
  -- dimensions of the strata
  obtain ⟨e, hdS, he⟩ : ∃ e : ℕ, topologicalKrullDim S = e ∧ e + F.length = n :=
    ⟨_, topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX), StratumAdjunctionData.dim_add_length hdX F
      (topologicalKrullDim_eq_toNat_trdeg (ι ≫ sX))⟩
  have hdS' : topologicalKrullDim S' = e := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso φ).isHomeomorph, hdS]
  have he' : e + Fp.length = n := StratumAdjunctionData.dim_add_length hdX' Fp hdS'
  by_cases he0 : e = 0
  · -- a zero-dimensional stratum is a point
    subst he0
    have h1 := coheight_le_of_topologicalKrullDim_eq hdS s₀
    have hmax : IsMax s₀ := Order.coheight_eq_zero.mp (nonpos_iff_eq_zero.mp (by exact_mod_cast h1))
    have h2 : s₀ ⤳ genericPoint S := hmax (genericPoint_specializes s₀)
    have h3 : genericPoint S = s₀ := ((genericPoint_specializes s₀).antisymm h2).eq
    exact hη (h3 ▸ hs₀)
  -- local generators near every point of `S`, and their residues along the two flags
  have hgen : ∀ y : S, ∃ U : X.Opens, ι y ∈ U ∧
      ∃ τ : RationalPluriForms sX n m, GeneratesOn B m U τ :=
    fun y => (MMP.Positivity.IsPair.exists_generatesOn hPX hK hC (ι y)).2
  choose U hU τ hτ using hgen
  have hgen' : ∀ y : S, ∃ U' : X'.Opens, ι' (φ.hom y) ∈ U' ∧
      ∃ τ' : RationalPluriForms sX' n m, GeneratesOn (flipTransform f fp B) m U' τ' :=
    fun y => (MMP.Positivity.IsPair.exists_generatesOn hPX' hK' hC' (ι' (φ.hom y))).2
  choose U' hU' τ' hτ' using hgen'
  have hres : ∀ y : S, ∃ ρ : RationalPluriForms (ι ≫ sX) e m,
      IsIteratedResidue sX B (τ y) F e ρ ∧ GeneratesOn BS m (ι ⁻¹ᵁ U y) ρ := by
    intro y
    obtain ⟨-, -, ⟨ρ, hρ⟩, hall⟩ := flag_generatesOn hdX hCX hm (hτ y) F he he0 ⟨y, hU y⟩
    exact ⟨ρ, hρ, hall ρ hρ⟩
  choose ρ hρ hρg using hres
  have hres' : ∀ y : S, ∃ ρ' : RationalPluriForms (ι' ≫ sX') e m,
      IsIteratedResidue sX' (flipTransform f fp B) (τ' y) Fp e ρ' ∧
        GeneratesOn BS' m (ι' ⁻¹ᵁ U' y) ρ' := by
    intro y
    obtain ⟨-, -, ⟨ρ', hρ'⟩, hall⟩ :=
      flag_generatesOn hdX' hCX' hm (hτ' y) Fp he' he0 ⟨φ.hom y, hU' y⟩
    exact ⟨ρ', hρ', hall ρ' hρ'⟩
  choose ρ' hρ' hρ'g using hres'
  have hsS : φ.hom ≫ ι' ≫ sX' = ι ≫ sX := by
    rw [← hflip.comp_eq, ← hFC.comp_eq, ← Category.assoc ι f sZ, hφ]
    simp only [Category.assoc]
  have hdSn := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι ≫ sX) hdS
  have hdS'n := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := ι' ≫ sX') hdS'
  -- the residues on `S'`, pulled back to `S` along `φ`, and their ratios `ψ` to those on `S`
  let π : S → RationalPluriForms (ι ≫ sX) e m := fun y =>
    cast (congrArg (fun s => RationalPluriForms s e m) hsS)
      (pullbackRationalPluriForms (ι' ≫ sX') φ.hom (ρ' y))
  have hπg : ∀ y, GeneratesOn BS m (φ.hom ⁻¹ᵁ (ι' ⁻¹ᵁ U' y)) (π y) := by
    intro y
    have h1 := generatesOn_pullback_of_isIso φ.hom hdS'n (hρ'g y)
    rw [hφB] at h1
    exact generatesOn_of_heq hsS.symm (cast_heq _ _) h1
  have hψ : ∀ y, ∃ ψ : S.functionField, π y = ψ • ρ y :=
    fun y => exists_eq_smul_of_ne_zero hdSn (hρg y).1 (π y)
  choose ψ hψ using hψ
  have hψu : ∀ y, ∀ y' ∈ (ι ⁻¹ᵁ U y ⊓ φ.hom ⁻¹ᵁ (ι' ⁻¹ᵁ U' y)), ∃ r : S.presheaf.stalk y',
      IsUnit r ∧ algebraMap _ S.functionField r = ψ y :=
    fun y y' hy' => exists_isUnit_of_generatesOn hdS ((hρg y).mono inf_le_left)
      ((hπg y).mono inf_le_right) (hψ y) hy'
  -- the common model `W` and the stratum `F'` dominating `S`
  have hc0 := hflipOf.isContraction
  have hs0 := hflipOf.isSmallMorphism
  have hsp0 := hflipOf.isSmallMorphism_flip
  haveI := hs0.isProper
  haveI := hsp0.isProper
  haveI : IsSeparated sZ := hc0.isNormalVariety_target.1.toIsSeparated
  have hVη : f (ι (genericPoint S)) ∈ biregularLocus fp := hV (by by_contra h'; exact hη h')
  obtain ⟨W, p, q, hW, hp, hq, hpb, hqb, hpq, hWreg⟩ := exists_commonModel (sZ := sZ)
    hc0.isNormalVariety_source hsp0.isNormalVariety_source hs0.isBirationalMorphism
    hsp0.isBirationalMorphism
  haveI := hp
  haveI := hq
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI : IsIntegral W := hW.1.toIsIntegral
  haveI : IsNormal W := hW.2
  haveI : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  obtain ⟨F', h, pF, hF'i, hhc, hhp, hhq, hpFη⟩ := exists_dominatingStratum hpq φ hφ hVη
  have hs : q ≫ sX' = p ≫ sX := by
    rw [← hflip.comp_eq, ← hFC.comp_eq, ← Category.assoc, ← Category.assoc, hpq]
  have hW' : IsNormalVariety k (q ≫ sX') := by rw [hs]; exact hW
  have hdW : topologicalKrullDim W = n := by
    haveI := hX.1
    haveI := hW.1
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb, hdX]
  have hdWn := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := p ≫ sX) hdW
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hdX
  have hcW : ∀ y, ∃ c : W.functionField,
      (hs ▸ pullbackRationalPluriForms sX' q (τ' y) : RationalPluriForms (p ≫ sX) n m) =
        c • pullbackRationalPluriForms sX p (τ y) := fun y =>
    exists_eq_smul_of_ne_zero hdWn
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero'
        p hpb.functionFieldMap_bijective hd (hτ y).1) _
  choose c hc using hcW
  -- the ratios are regular at the generic point `ζ` of `F'`
  set ζ := h (genericPoint F') with hζ
  have hpζ : p ζ = ι (genericPoint S) := by
    rw [hζ, ← Scheme.Hom.comp_apply, hhp, Scheme.Hom.comp_apply, hpFη]
  have hqζ : q ζ = ι' (φ.hom (genericPoint S)) := by
    rw [hζ, ← Scheme.Hom.comp_apply, hhq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hpFη]
  have hηU : ∀ y, ι (genericPoint S) ∈ U y := fun y =>
    ((genericPoint_specializes y).map ι.base.hom.continuous).mem_open (U y).isOpen (hU y)
  have hηU' : ∀ y, ι' (φ.hom (genericPoint S)) ∈ U' y := fun y =>
    (((genericPoint_specializes y).map φ.hom.base.hom.continuous).map
      ι'.base.hom.continuous).mem_open (U' y).isOpen (hU' y)
  have ht : ∀ y, ∃ t : W.presheaf.stalk ζ, algebraMap _ W.functionField t = c y := fun y =>
    exists_algebraMap_stalk_eq_of_generatesOn hflip hK hW hW' hpb hqb hpq hs hm hC hC' (hτ y)
      (hτ' y) (by rw [hpζ]; exact hηU y) (by rw [hqζ]; exact hηU' y) (hc y)
  choose t ht using ht
  haveI : IsDominant pF := ⟨Dense.mono (Set.singleton_subset_iff.mpr ⟨_, hpFη⟩)
    (dense_iff_closure_eq.mpr (isGenericPoint_def.mp (genericPoint_spec S)))⟩
  let γ : S → F'.functionField := fun y => (h.stalkMap (genericPoint F')).hom (t y)
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hdX'
  have hηU'' : ∀ y, ι' (genericPoint S') ∈ U' y := fun y =>
    ((genericPoint_specializes (φ.hom y)).map ι'.base.hom.continuous).mem_open (U' y).isOpen
      (hU' y)
  have hgS' : φ.hom (genericPoint S) = genericPoint S' := by
    have hsurj : Function.Surjective φ.hom := fun y =>
      ⟨φ.inv y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
    have h1 := (genericPoint_spec S).image φ.hom.base.hom.continuous
    rw [Set.image_univ, hsurj.range_eq, closure_univ] at h1
    exact h1.eq (genericPoint_spec S')
  have hA : ∀ y, γ y * functionFieldMap pF (ψ s₀) = γ s₀ * functionFieldMap pF (ψ y) := by
    intro y
    -- the changes of generators on `X` and on `X'`
    obtain ⟨a, ha⟩ := exists_eq_smul_of_ne_zero hd (hτ s₀).1 (τ y)
    obtain ⟨ra, hra, hraa⟩ := exists_isUnit_of_generatesOn hdX ((hτ s₀).mono inf_le_right)
      ((hτ y).mono inf_le_left) ha
      (show ι (genericPoint S) ∈ U y ⊓ U s₀ from ⟨hηU y, hηU s₀⟩)
    obtain ⟨a', ha'⟩ := exists_eq_smul_of_ne_zero hd' (hτ' s₀).1 (τ' y)
    obtain ⟨ra', hra', hraa'⟩ := exists_isUnit_of_generatesOn hdX' ((hτ' s₀).mono inf_le_right)
      ((hτ' y).mono inf_le_left) ha'
      (show ι' (genericPoint S') ∈ U' y ⊓ U' s₀ from ⟨hηU'' y, hηU'' s₀⟩)
    -- the residues change by the restrictions of these units
    have hρy : ρ y = (ι.stalkMap (genericPoint S)).hom ra • ρ s₀ := by
      have h1 := IsIteratedResidue.algebraMap_smul (hρ s₀) ra
      rw [hraa, ← ha] at h1
      exact IsIteratedResidue.unique (hρ y) h1
    have hρ'y : ρ' y = (ι'.stalkMap (genericPoint S')).hom ra' • ρ' s₀ := by
      have h1 := IsIteratedResidue.algebraMap_smul (hρ' s₀) ra'
      rw [hraa', ← ha'] at h1
      exact IsIteratedResidue.unique (hρ' y) h1
    have hπy : π y = functionFieldMap φ.hom ((ι'.stalkMap (genericPoint S')).hom ra') • π s₀ := by
      simp only [π]
      rw [hρ'y, pullbackRationalPluriForms_smul', cast_smul_rationalPluriForms hsS]
    have eS : ψ y * (ι.stalkMap (genericPoint S)).hom ra =
        functionFieldMap φ.hom ((ι'.stalkMap (genericPoint S')).hom ra') * ψ s₀ := by
      apply smul_left_injective S.functionField (hρg s₀).1
      simp only
      rw [mul_smul, mul_smul, ← hρy, ← hψ y, ← hψ s₀, hπy]
    -- the ratios on `W` change by the pull-backs of these units
    have hP0 : pullbackRationalPluriForms sX p (τ s₀) ≠ 0 :=
      MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
        hpb.functionFieldMap_bijective hd (hτ s₀).1
    have eW : c y * functionFieldMap p a = functionFieldMap q a' * c s₀ := by
      apply smul_left_injective W.functionField hP0
      simp only
      rw [mul_smul, mul_smul, ← pullbackRationalPluriForms_smul', ← ha, ← hc y, ← hc s₀, ha',
        pullbackRationalPluriForms_smul', eqRec_smul_rationalPluriForms]
    -- restricted to `F'`
    obtain ⟨tA, htA, htA'⟩ := exists_stalk_eq_functionFieldMap h pF p ι hhp hpFη ra
    have hpFη' : (pF ≫ φ.hom) (genericPoint F') = genericPoint S' := by
      rw [Scheme.Hom.comp_apply, hpFη, hgS']
    have hhq' : h ≫ q = (pF ≫ φ.hom) ≫ ι' := by rw [hhq, Category.assoc]
    obtain ⟨tB, htB, htB'⟩ := exists_stalk_eq_functionFieldMap h (pF ≫ φ.hom) q ι' hhq' hpFη' ra'
    have eζ : t y * tA = tB * t s₀ := IsFractionRing.injective _ W.functionField (by
      rw [map_mul, map_mul, ht, ht, htA, htB, hraa, hraa', eW])
    have e1 : γ y * functionFieldMap pF ((ι.stalkMap (genericPoint S)).hom ra) =
        functionFieldMap pF (functionFieldMap φ.hom ((ι'.stalkMap (genericPoint S')).hom ra')) *
          γ s₀ := by
      have h1 := congrArg (h.stalkMap (genericPoint F')).hom eζ
      rw [map_mul, map_mul, htA', htB',
        ← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply] at h1
      exact h1
    have e2 : functionFieldMap pF (ψ y) *
        functionFieldMap pF ((ι.stalkMap (genericPoint S)).hom ra) =
        functionFieldMap pF (functionFieldMap φ.hom ((ι'.stalkMap (genericPoint S')).hom ra')) *
          functionFieldMap pF (ψ s₀) := by
      rw [← map_mul, ← map_mul, eS]
    have hA0 : functionFieldMap pF ((ι.stalkMap (genericPoint S)).hom ra) ≠ 0 :=
      (map_ne_zero _).mpr ((hra.map _).ne_zero)
    apply mul_right_cancel₀ hA0
    linear_combination (functionFieldMap pF (ψ s₀)) * e1 - γ s₀ * e2
  have hψ0 : ∀ y, ψ y ≠ 0 := fun y h0 => by
    have := hψ y
    rw [h0, zero_smul] at this
    exact (hπg y).1 this
  have hΨ0 : ∀ y, functionFieldMap pF (ψ y) ≠ 0 := fun y => (map_ne_zero _).mpr (hψ0 y)
  set u := γ s₀ * (functionFieldMap pF (ψ s₀))⁻¹ with hu
  have huy : ∀ y, γ y = u * functionFieldMap pF (ψ y) := by
    intro y
    rw [hu, mul_right_comm, ← hA y, mul_assoc, mul_inv_cancel₀ (hΨ0 s₀), mul_one]
  -- the image of the ratio on `F'` near a point `w`
  have himage : ∀ w : F', ∃ tw : W.presheaf.stalk (h w),
      algebraMap _ W.functionField tw = c (pF w) ∧
        γ (pF w) = algebraMap _ F'.functionField ((h.stalkMap w).hom tw) := by
    intro w
    have hpw : p (h w) = ι (pF w) := by
      rw [← Scheme.Hom.comp_apply, hhp, Scheme.Hom.comp_apply]
    have hqw : q (h w) = ι' (φ.hom (pF w)) := by
      rw [← Scheme.Hom.comp_apply, hhq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    obtain ⟨tw, htw⟩ := exists_algebraMap_stalk_eq_of_generatesOn hflip hK hW hW' hpb hqb hpq hs
      hm hC hC' (hτ (pF w)) (hτ' (pF w)) (by rw [hpw]; exact hU _) (by rw [hqw]; exact hU' _)
      (hc (pF w))
    have hgw : genericPoint F' ⤳ w := genericPoint_specializes w
    have htt : (W.presheaf.stalkSpecializes (h.base.hom.map_specializes hgw)).hom tw =
        t (pF w) :=
      IsFractionRing.injective _ W.functionField
        (by rw [MMP.Mori.algebraMap_stalkSpecializes, htw, ht])
    refine ⟨tw, htw, ?_⟩
    change (h.stalkMap (genericPoint F')).hom (t (pF w)) = _
    rw [← htt]
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply h _ _ hgw tw
  -- `u` is a regular function on `F'`
  have hureg : ∀ w : F', u ∈ (algebraMap (F'.presheaf.stalk w) F'.functionField).range := by
    intro w
    obtain ⟨tw, -, hγ⟩ := himage w
    obtain ⟨r, hr, hrψ⟩ := hψu (pF w) (pF w) ⟨hU _, hU' _⟩
    have hΨ : functionFieldMap pF (ψ (pF w)) =
        algebraMap _ F'.functionField ((pF.stalkMap w).hom r) := by
      rw [← hrψ, MMP.Mori.functionFieldMap_algebraMap_stalk]
    have hr' : IsUnit ((pF.stalkMap w).hom r) := hr.map _
    refine ⟨(h.stalkMap w).hom tw * ↑(hr'.unit⁻¹), ?_⟩
    rw [map_mul, ← hγ, huy, hΨ, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  have hu0 : u ≠ 0 := by
    have hζV : f (p ζ) ∈ biregularLocus f := by
      rw [hpζ]; by_contra h'; exact hη h'
    obtain ⟨r, hr, hrc⟩ := exists_isUnit_of_mem_biregularLocus hflip hK hpb hqb hpq hs (hτ s₀)
      (hτ' s₀) (by rw [hpζ]; exact hηU s₀) (by rw [hqζ]; exact hηU' s₀) hζV (hc s₀)
    have hrt : r = t s₀ := IsFractionRing.injective _ W.functionField (by rw [hrc, ht])
    refine mul_ne_zero ?_ (inv_ne_zero (hΨ0 s₀))
    change (h.stalkMap (genericPoint F')).hom (t s₀) ≠ 0
    rw [← hrt]
    exact (hr.map _).ne_zero
  -- `F'` is proper over `k`, so `u` is a unit everywhere
  haveI : IsProper sX :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hXp.isProjective).2
  haveI : IsProper h := inferInstance
  have huu := exists_isUnit_algebraMap_eq (h ≫ p ≫ sX) hu0 hureg
  -- a closed point `s₁` of `S` in `Ex(f)` and a closed point `w₀` of `F'` over it
  obtain ⟨s₁, hs₁, hs₁c⟩ := (isClosed_closure (s := ({s₀} : Set S))).exists_closed_singleton
    ⟨s₀, subset_closure rfl⟩
  have hs₁Ex : ι s₁ ∈ (exceptionalSet f : Set X) :=
    ((specializes_iff_mem_closure.mpr hs₁).map ι.base.hom.continuous).mem_closed
      (exceptionalSet f).isClosed hs₀
  have hpFsurj : Function.Surjective pF := by
    intro y
    have hcl : IsClosed (Set.range (h ≫ p)) := (h ≫ p).isClosedMap.isClosed_range
    have hmem : ι (genericPoint S) ∈ Set.range (h ≫ p) := ⟨genericPoint F', hpζ⟩
    obtain ⟨w, hw⟩ := ((genericPoint_specializes y).map ι.base.hom.continuous).mem_closed hcl hmem
    refine ⟨w, ι.isClosedEmbedding.injective ?_⟩
    change (pF ≫ ι) w = ι y
    rw [← hhp]; exact hw
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace p
  haveI : CompactSpace F' := h.isClosedEmbedding.compactSpace
  obtain ⟨w₀, hw₀, hw₀c⟩ := (hs₁c.preimage pF.base.hom.continuous).exists_closed_singleton
    (hpFsurj s₁)
  have hw₀s : pF w₀ = s₁ := hw₀
  have hx₀c : IsClosed ({h w₀} : Set W) := by
    have := h.isClosedEmbedding.isClosedMap _ hw₀c
    rwa [Set.image_singleton] at this
  have hcx₀ : 2 ≤ Order.coheight (h w₀) := by
    rw [coheight_eq_of_isClosed (p ≫ sX) hdW hx₀c]
    exact (MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hs0.two_le_codimension
      hs₁Ex).trans (coheight_le_of_topologicalKrullDim_eq hdX (ι s₁))
  -- the ratio for the generators at `s₁` is a unit at `h w₀`, against strict increase
  obtain ⟨tw, htw, hγ⟩ := himage w₀
  rw [hw₀s] at htw hγ
  obtain ⟨a, ha, hau⟩ := huu w₀
  obtain ⟨r, hr, hrψ⟩ := hψu s₁ s₁ ⟨hU _, hU' _⟩
  have hΨ : functionFieldMap pF (ψ s₁) =
      algebraMap _ F'.functionField ((pF.stalkMap w₀).hom ((S.presheaf.stalkSpecializes
        (specializes_of_eq hw₀s)).hom r)) := by
    rw [← hrψ, ← MMP.Mori.algebraMap_stalkSpecializes (specializes_of_eq hw₀s) r,
      MMP.Mori.functionFieldMap_algebraMap_stalk]
  have hunit : IsUnit tw := by
    have e : (h.stalkMap w₀).hom tw = a * (pF.stalkMap w₀).hom
        ((S.presheaf.stalkSpecializes (specializes_of_eq hw₀s)).hom r) :=
      IsFractionRing.injective _ F'.functionField (by rw [← hγ, huy, map_mul, hau, hΨ])
    have : IsUnit ((h.stalkMap w₀).hom tw) := by
      rw [e]; exact ha.mul ((hr.map _).map _)
    exact (isUnit_map_iff _ _).mp this
  have hpw₀ : p (h w₀) = ι s₁ := by
    rw [← Scheme.Hom.comp_apply, hhp, Scheme.Hom.comp_apply, hw₀s]
  have hqw₀ : q (h w₀) = ι' (φ.hom s₁) := by
    rw [← Scheme.Hom.comp_apply, hhq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw₀s]
  refine not_exists_isUnit_of_notMem_biregularLocus hflip hK hW hpb hqb hpq hs hm hC hC'
    (hτ s₁) (hτ' s₁) (by rw [hpw₀]; exact hU _) (by rw [hqw₀]; exact hU' _)
    (by rw [hpw₀]; exact hs₁Ex)
    (hWreg _) hcx₀ (hc s₁) ⟨tw, hunit, htw⟩

end GArgument

end MMP.Fourfold.StratumAvoidsFlip

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

open StratumAvoidsFlip in
/-- **A fixed projective adjunction stratum lies in the isomorphism locus of a flip.** Let
`f⁺ : X⁺ ⟶ Z` be a `(K_X + B)`-flip (`MMP.Fourfold.IsFlipOf`) of `f : X ⟶ Z`, between projective
dlt pairs `(X, B)` and `(X⁺, B⁺)`, `B⁺ = (f⁺)⁻¹_* f_* B`, such that no boundary stratum of either
pair lies in the exceptional set of `f`, respectively `f⁺`. Let `(S, B_S)`, `ι : S ⟶ X`, and
`(S⁺, B_{S⁺})`, `ι⁺ : S⁺ ⟶ X⁺`, be adjunction pairs on strata
(`MMP.Fourfold.IsStratumAdjunctionPair`), and let `φ : S ≅ S⁺` be an isomorphism of pairs
induced by the flip: `ι ≫ f = φ ≫ ι⁺ ≫ f⁺` and `φ^* B_{S⁺} = B_S`. Then `ι(S)` is disjoint from
`Ex(f)` and `ι⁺(S⁺)` is disjoint from `Ex(f⁺)`. -/
@[mmp "lem_mmp_fixed_projective_stratum_avoids_flip"]
public theorem IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {n : ℕ} {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hX : Mori.IsProjectiveVariety k sX) (hX' : Mori.IsProjectiveVariety k sX')
    (hK : K.IsCanonicalDivisor sX n)
    (hB : MMP.Intersection.IsDltPair sX B)
    (hB' : MMP.Intersection.IsDltPair sX' (flipTransform f fp B))
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hstrata : ∀ T : Set X, IsDltStratum sX B T → ¬ T ⊆ (exceptionalSet f : Set X))
    (hstrata' : ∀ T : Set X', IsDltStratum sX' (flipTransform f fp B) T →
      ¬ T ⊆ (exceptionalSet fp : Set X'))
    {S S' : Scheme.{0}} {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (hS : IsStratumAdjunctionPair sX B ι BS)
    (hS' : IsStratumAdjunctionPair sX' (flipTransform f fp B) ι' BS')
    (φ : S ≅ S') (hφ : ι ≫ f = φ.hom ≫ ι' ≫ fp)
    (hφB : inverseTransformDivisor φ.hom BS' = BS) :
    Disjoint (Set.range ι.base) (exceptionalSet f : Set X) ∧
      Disjoint (Set.range ι'.base) (exceptionalSet fp : Set X') := by
  have hV : biregularLocus f ≤ biregularLocus fp := biregularLocus_le_of_isFlipOf hflip
  have source_disjoint : Disjoint (Set.range ι.base) (exceptionalSet f : Set X) := by
    have F := hS.some
    have Fp := hS'.some
    haveI : IsIntegral S := F.isNormalVariety.1.toIsIntegral
    have hη : ι (genericPoint S) ∉ (exceptionalSet f : Set X) :=
      genericPoint_notMem_exceptionalSet_of_stratumAdjunctionData
        hflip.isSmallMorphism.two_le_codimension hB hstrata F
    rw [Set.disjoint_left]
    rintro _ ⟨s₀, rfl⟩
    exact notMem_exceptionalSet_of_isIso hX hK hflip F Fp φ hφ hφB hη s₀
  have target_disjoint : Disjoint (Set.range ι'.base) (exceptionalSet fp : Set X') :=
    disjoint_range_exceptionalSet_of_comp_eq φ hφ hV source_disjoint
  exact ⟨source_disjoint, target_disjoint⟩

end MMP.Fourfold
