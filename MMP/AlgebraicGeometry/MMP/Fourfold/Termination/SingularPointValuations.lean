module
import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorIntegral

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.Divisor.DivisorialValuation
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.IndexBound.EnoughExceptionalCurves
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.IndexBound.ClosedFibreLineBundles
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.ProductPuncturedFamily
import MMP.AlgebraicGeometry.MMP.Threefold.TerminalSmallQFactorialization
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Singularities.EtaleNeighbourhoodTerminal
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleIndependence
import MMP.AlgebraicGeometry.Singularities.SmallModelCrepant
import MMP.AlgebraicGeometry.Morphisms.Etale.DivisorialValuationRestriction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.GenerationRequired
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.EpiClosedImmersionFactorization
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraCopies
import StacksFrontier.AlgebraicGeometry.ReflexiveTorsionFree.Converse
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DualTensorInternalHom
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation

/-!
# Valuations centred at a singular point

Let `Y` be a normal projective `ℚ`-factorial complex threefold and `(Y, Θ)` an effective terminal
pair. Let `y ∈ Sing Y` be a closed point lying on a prime divisor with positive coefficient in
`Θ`. Let `T_y = {y} × ℙ¹ ⊆ Y × ℙ¹` (`MMP.Fourfold.pointSettingCurve`) and `b = b_{T_y}` the rank of
its punctured local system (`MMP.Fourfold.curveLocalSystemRank`). Then there are at least `b`
distinct normalized divisorial valuations `v` of `ℂ(Y)` with centre `c_Y(v) = {y}`,
`a(v; Y, 0) = 2` and `a(v; Y, Θ) < 2`.

## Main results

* `MMP.Fourfold.le_encard_setOf_isCentre_singleton`: the count of such valuations.

## Implementation notes

* `Y × ℙ¹` is the pull-back of `s_Y : Y ⟶ Spec ℂ` and `ℙ¹_ℂ ⟶ Spec ℂ`, a complex scheme through
  its first projection, and `T_y` is an irreducible closed subset with underlying set
  `MMP.Fourfold.pointSettingCurve s_Y y`. The integer `b_{T_y}` does not depend on the
  local-system open on which it is computed, so the result is stated for every local-system open
  `T°` of `T_y`, with `b = curveLocalSystemRank T°`.
* Centres are `MMP.Intersection.IsCentre` (which includes that `v` is a normalized divisorial
  valuation) and log discrepancies `MMP.Fourfold.IsValuationLogDiscrepancy`; the valuations are
  counted with `Set.encard`.
* A boundary of a `ℚ`-divisor (`MMP.Mori.QDivisor`) is rational; effectivity is `0 ≤ Θ`.

## References

* [Termination for projective log canonical fourfolds with rational boundary (OpenAI, 2026)]
-/

@[expose] public section

section

universe u

namespace Proof_prop_mmp_indexb_point_valuations

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Fourfold MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A projective morphism in the sense of EGA onto a scheme H-projective over a field is
H-projective, the target carrying an ample invertible sheaf. -/
private theorem isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism {k : Type u}
    [Field k] {Y Z : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (hsZ : IsProjectiveMorphism sZ)
    (f : Y ⟶ Z) (hf : IsProjective f) : IsProjectiveMorphism f := by
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sZ _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective _
      (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.1 hsZ).1)
  haveI := hL
  exact isProjectiveMorphism_of_isProjective f L hLa hf

/-- On a `ℚ`-factorial terminal complex threefold `X`, every irreducible curve `S ⊆ X` is the
centre of a normalized divisorial valuation `w` with `a(w; X, 0) = 2`: `X` is smooth in
codimension two, so `X` is smooth at the generic point of `S`, and `w` is the valuation of the
exceptional divisor of the blow-up of `S` there. -/
private theorem exists_isCentre_isValuationLogDiscrepancy_two_of_topologicalKrullDim_eq_one
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX) (hT : IsTerminalVariety sX)
    (hdim : topologicalKrullDim X = 3) (S : IrreducibleCloseds X)
    (hS : topologicalKrullDim (S : Set X) = 1) :
    ∃ w : Valuation X.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sX w S ∧ IsValuationLogDiscrepancy sX 0 w 2 := by
  have hX : IsNormalVariety ℂ sX := hQ.1
  have hP : MMP.Mori.IsPair sX 0 := hT.1.1.isPair
  obtain ⟨n, K, hK, -⟩ := hP.2
  have hcod := (hT.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    (isQCartier_of_isQFactorial sX hQ 0) hK (isQCartier_of_isQFactorial sX hQ _)).2
  set η := S.isIrreducible.genericPoint
  have hcl : closure {η} = (S : Set X) := by
    have h := S.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [S.isClosed.closure_eq] at h
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hadd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX η
  rw [hcl, hS, hdim] at hadd
  have hc : Order.coheight η = 2 := by
    have h : 1 + Order.coheight η = 3 := WithBot.coe_injective hadd
    generalize Order.coheight η = c at h ⊢
    induction c using ENat.recTopCoe with
    | top => simp at h
    | coe m =>
      norm_cast at h ⊢
      omega
  have hcodS : codimension S = 2 := by
    rwa [MMP.Flips.codimension_eq_coheight_genericPoint]
  have hsm : η ∈ smoothLocus sX := by
    by_contra h
    have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcod η h
    rw [hc] at this
    norm_num at this
  obtain ⟨w, -, hw, hw2⟩ :=
    exists_isCentre_isValuationLogDiscrepancy_two_of_codimension_eq_two sX hP S hcodS hsm
  exact ⟨w, hw, hw2⟩

/-- The coefficients of a divisor `D` with `D = m • A` are `m` times those of `A`. -/
private theorem coe_apply_of_toQDivisor_eq {X : Scheme.{0}} {D : Divisor X} {A : QDivisor X}
    {m : ℕ} (h : Divisor.toQDivisor D = (m : ℤ) • A) (P : MMP.Mori.PrimeDivisor X) :
    (D P : ℚ) = m * A P :=
  (by simpa using congrArg (· P) h : Divisor.toQDivisor D P = m * A P)

/-- A divisor that is a multiple `m • A` of an effective `ℚ`-divisor is effective. -/
private theorem isEffective_of_toQDivisor_eq {X : Scheme.{0}} {D : Divisor X} {A : QDivisor X}
    {m : ℕ} (hA : 0 ≤ A) (h : Divisor.toQDivisor D = (m : ℤ) • A) :
    DivisorWithCoeffs.IsEffective D := fun P => by
  exact_mod_cast ((coe_apply_of_toQDivisor_eq h P) ▸ mul_nonneg m.cast_nonneg (hA P) :
    (0 : ℚ) ≤ D P)

/-- **The pull-back of an effective `ℚ`-Cartier `ℚ`-divisor is effective.** With `m` the Cartier
index of `A`, `m f^*A` is the pull-back of the effective Cartier divisor `mA`, whose local
equations are regular, so their pull-backs have nonnegative order. -/
private theorem nonneg_of_isPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) : 0 ≤ B := by
  obtain ⟨D₀, D', hD₀c, hD₀B, hD₀, hD', hp⟩ := h.exists_cartierIndex hAq
  intro E
  have h0 : (0 : ℚ) ≤ D' E := by
    exact_mod_cast MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hD₀c
      (fun P (_ : (P.support ∩ (⊤ : X.Opens)).Nonempty) => isEffective_of_toQDivisor_eq hA hD₀ P)
      hp E
      ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  rw [coe_apply_of_toQDivisor_eq hD' E] at h0
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast QDivisor.cartierIndex_pos hAq)

/-- **The pull-back of an effective `ℚ`-Cartier divisor is positive over its support.** If
`f(η_E) ∈ Supp A`, then `E` occurs in `f^*(mA)` (`Supp f^*(mA) = f⁻¹ Supp(mA)`), so the
coefficient of `E` in the effective `f^*A` is positive. -/
private theorem coeff_pos_of_isPullback_of_mem_supp {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {A : QDivisor X} (hA : 0 ≤ A)
    (hAq : A.IsQCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ A.supp}
    {B : QDivisor Y} (h : A.IsPullback f hB B) (E : MMP.Mori.PrimeDivisor Y)
    (hE : f E.genericPoint ∈ A.supp) : 0 < B.coeff E := by
  obtain ⟨D₀, D', hD₀c, hD₀B, hD₀, hD', hp⟩ := h.exists_cartierIndex hAq
  have hsupp : D₀.supp = A.supp := QDivisor.supp_eq_of_toQDivisor_eq
    (by exact_mod_cast (QDivisor.cartierIndex_pos hAq).ne') hD₀
  have hmem : E.genericPoint ∈ (D'.supp : Set Y) := by
    rwa [MMP.Flips.supp_eq_preimage_supp_of_isPullback hD₀c (isEffective_of_toQDivisor_eq hA hD₀)
      hp, Set.mem_preimage, hsupp]
  obtain ⟨P, hP0, hEP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  obtain rfl := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hEP
  refine (nonneg_of_isPullback hA hAq h P).lt_of_ne' fun h0 => hP0 ?_
  have : (D' P : ℚ) = 0 := by
    rw [coe_apply_of_toQDivisor_eq hD' P]
    simp [DivisorWithCoeffs.coeff] at h0 ⊢
    simp [h0]
  exact_mod_cast this

/-- **Adding an effective boundary through the centre lowers the log discrepancy.** On a
`ℚ`-factorial normal complex variety `X`, let `Θ` be an effective `ℚ`-divisor and `v` a
normalized divisorial valuation whose centre lies in `Supp Θ`. If `a = a(v; X, 0)`, then
`a(v; X, Θ) = a - coeff_v(f^*Θ) < a`, the coefficient being positive. -/
private theorem exists_isValuationLogDiscrepancy_lt_of_subset_supp
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX) {Θ : QDivisor X} (hΘ0 : 0 ≤ Θ)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} {Z : IrreducibleCloseds X}
    (hv : MMP.Intersection.IsCentre ℂ sX v Z) (hZ : (Z : Set X) ⊆ Θ.supp) {a : ℝ}
    (ha : IsValuationLogDiscrepancy sX 0 v a) :
    ∃ b : ℝ, IsValuationLogDiscrepancy sX Θ v b ∧ b < a := by
  obtain ⟨n, D, hDp, rfl, ha⟩ := ha
  obtain ⟨D', -, hv, rfl⟩ := hv
  have hD : D.f D.E.genericPoint ∈ Θ.supp := hZ <| by
    rw [← MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hQ.1.1 hv,
      DivisorOver.center_eq_closure_genericPoint]
    exact subset_closure rfl
  obtain ⟨hX, hf, -, -, ⟨K, hK, -⟩, -⟩ := id ha
  have hΘq : Θ.IsQCartier := isQCartier_of_isQFactorial sX hQ Θ
  have hPw : IsPairWith sX n K 0 :=
    ⟨hX, hK, by rw [add_zero]; exact isQCartier_of_isQFactorial sX hQ _⟩
  obtain ⟨-, hB, hiff⟩ := MMP.Mori.IsPairWith.isDiscrepancy_add_smul_iff hPw hΘq D
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : CompactSpace D.Y := by
    have := D.isNormalVariety.1
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨B', hB'⟩ := (hΘq.existsUnique_isPullback hB).exists
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPw.isPair hK D
  have hac := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha
  have hc' := ((hiff B' hB').1 c).2 hc
  rw [zero_add] at hc'
  have hpos : (0 : ℝ) < (B'.coeff D.E : ℝ) := by
    exact_mod_cast coeff_pos_of_isPullback_of_mem_supp hΘ0 hΘq hB' D.E hD
  refine ⟨1 + ((c - B'.coeff D.E : ℚ) : ℝ), ⟨n, D, hDp, rfl,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc' hf⟩, ?_⟩
  rw [hac]
  push_cast
  linarith

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : IsBirationalMorphism g) (hμ : IsBirationalMorphism μ) :
    IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- The image in `X` of a subset `Z` of a subspace `A ⊆ X` has the dimension of `Z`. -/
private theorem topologicalKrullDim_image_val {X : Type*} [TopologicalSpace X] (A : Set X)
    (Z : Set A) : topologicalKrullDim (Subtype.val '' Z : Set X) = topologicalKrullDim Z := by
  have he : Topology.IsEmbedding (fun z : Z => (z.1.1 : X)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hr : Set.range (fun z : Z => (z.1.1 : X)) = Subtype.val '' Z := by
    ext x
    simp
  rw [← hr]
  exact (IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph).symm

section Small

variable {k : Type u} [Field k] {X Y' : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] {sX : X ⟶ Spec (.of k)}

/-- A divisor `(W, h, E)` over `Y'`, regarded as a divisor `(W, g ∘ h, E)` over `X` through a
birational morphism `g : Y' ⟶ X`. -/
private noncomputable def compDivisorOver (g : Y' ⟶ X) (hg : IsBirationalMorphism g)
    (D : DivisorOver k (g ≫ sX)) : DivisorOver k sX where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by rw [Category.assoc]; exact D.isNormalVariety
  isBirationalMorphism := haveI := D.isIntegral; isBirationalMorphism_comp D.isBirationalMorphism hg
  E := D.E

/-- The valuation of `(W, g ∘ h, E)` is that of `(W, h, E)` read on `k(X)` through `g^*`. -/
private theorem valuation_compDivisorOver (g : Y' ⟶ X) (hg : IsBirationalMorphism g)
    [IsDominant g] (D : DivisorOver k (g ≫ sX)) :
    (compDivisorOver g hg D).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isDominant
  haveI : IsDominant (D.f ≫ g) := (compDivisorOver g hg D).isDominant
  ext t
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ g) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The centre of `(W, g ∘ h, E)` is the closure of the image under `g` of the generic point of
the centre of `(W, h, E)`. -/
private theorem coe_center_compDivisorOver (g : Y' ⟶ X) (hg : IsBirationalMorphism g)
    (D : DivisorOver k (g ≫ sX)) :
    ((compDivisorOver g hg D).center : Set X) = closure {g (D.f D.E.genericPoint)} := by
  rw [DivisorOver.center_eq_closure_genericPoint]
  rfl

/-- A small morphism maps the generic point of every prime divisor into its biregular locus. -/
private theorem map_genericPoint_mem_biregularLocus {g : Y' ⟶ X}
    (hg : IsSmallMorphism (g ≫ sX) sX g) (F : MMP.Mori.PrimeDivisor Y') :
    g F.genericPoint ∈ biregularLocus g := by
  by_contra hx
  have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hg.two_le_codimension
    F.genericPoint hx
  simp [F.coheight_genericPoint] at this

/-- A morphism is a local isomorphism at every point mapping into its biregular locus. -/
private theorem isIso_stalkMap_of_mem (g : Y' ⟶ X) {x : Y'} (hx : g x ∈ biregularLocus g) :
    IsIso (g.stalkMap x) := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have : IsOpenImmersion ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) := by
    rw [← morphismRestrict_ι g (biregularLocus g)]
    infer_instance
  let x' : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨x, hx⟩
  have h := IsOpenImmersion.instIsIsoCommRingCatStalkMap ((g ⁻¹ᵁ biregularLocus g).ι ≫ g) x'
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (g.stalkMap _) _
    (IsOpenImmersion.instIsIsoCommRingCatStalkMap (g ⁻¹ᵁ biregularLocus g).ι x') h

/-- **A small morphism is crepant for the empty boundary.** If `g : Y' ⟶ X` is small and `(X, 0)`
is a pair, the crepant boundary of `(X, 0)` on `Y'` is `0`: every prime divisor `F` of `Y'` is the
strict transform of a prime divisor `P` of `X`, with the same valuation, so
`a(F; X, 0) = a(P; X, 0) = 0`. -/
private theorem isCrepantBoundary_zero [IsAlgClosed k] [CharZero k] {n : ℕ} {K : Divisor X}
    (hPw : IsPairWith sX n K 0) {g : Y' ⟶ X}
    (hg : IsSmallMorphism (g ≫ sX) sX g) :
    IsCrepantBoundary sX n K 0 g hg.isNormalVariety_source hg.isBirationalMorphism 0 := by
  intro F
  have hX := hg.isNormalVariety_target
  haveI : IsDominant g := hg.isBirationalMorphism.isDominant
  have hx := map_genericPoint_mem_biregularLocus hg F
  have hc : Order.coheight (g F.genericPoint) = 1 :=
    (MMP.Positivity.coheight_map_of_mem_biregularLocus g hx).trans F.coheight_genericPoint
  set P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc
  have hgP : g F.genericPoint = P.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
  have := isIso_stalkMap_of_mem g hx
  set D : DivisorOver k sX :=
    ⟨Y', g, hg.isNormalVariety_source, hg.isBirationalMorphism, F⟩
  have hv : D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
    ext t
    change F.divisorialValuation (functionFieldMap g t) =
      P.divisorialValuation (functionFieldMap (𝟙 X) t)
    rw [functionFieldMap_id_apply]
    by_cases ht : t = 0
    · simp [ht]
    rw [F.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr ht),
      P.divisorialValuation_eq_exp_neg_ord ht,
      MMP.Positivity.ord_functionFieldMap_of_isIso g F P hgP]
  obtain ⟨c, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPw.isPair hPw.2.1 D
  obtain ⟨c', hc'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPw.isPair hPw.2.1
    (DivisorOver.ofPrimeDivisor k hX P)
  have hcc := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPw hv hcD hc'
  rw [hcc, IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX hc'] at hcD
  simpa using hcD

/-- **Log discrepancies over a small model.** Let `g : Y' ⟶ X` be a small morphism and `(X, 0)` a
pair. Every log discrepancy `a = a(D; Y', 0)` of a divisor `D` over `Y'` is the log discrepancy
`a(D; X, 0)` of `D` regarded as a divisor over `X` through `g`. -/
private theorem isLogDiscrepancy_compDivisorOver [IsAlgClosed k] [CharZero k]
    (hP : MMP.Mori.IsPair sX 0) {g : Y' ⟶ X} (hg : IsSmallMorphism (g ≫ sX) sX g)
    {n : ℕ} {D : DivisorOver k (g ≫ sX)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (g ≫ sX) n (QDivisor.toRDivisor 0) D a) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor 0)
      (compDivisorOver g hg.isBirationalMorphism D) a := by
  have hX := hg.isNormalVariety_target
  have hY' := hg.isNormalVariety_source
  have hgb := hg.isBirationalMorphism
  haveI := hg.isProper
  haveI : IsDominant g := hgb.isDominant
  haveI : CompactSpace Y' := by
    have := hY'.1
    exact QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  obtain ⟨-, n₀, K, hK, hKq⟩ := id hP
  rw [add_zero] at hKq
  have hPw : IsPairWith sX n₀ K 0 := ⟨hX, hK, by rwa [add_zero]⟩
  obtain ⟨K', hK', -⟩ := hg.exists_isCanonicalDivisor_eq_pullback hK hKq
  have hcb := isCrepantBoundary_zero hPw hg
  obtain ⟨hPY, hiff⟩ :=
    MMP.Mori.IsPair.isDiscrepancy_iff_of_crepant hP g hY' hgb hK hK' (Or.inl hcb)
  obtain rfl : n = n₀ := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK'.topologicalKrullDim_eq
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : IsProper D.f := ha.2.1
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPY hK' D
  have hac := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha
  have hc' := (hiff D (compDivisorOver g hgb D) (valuation_compDivisorOver g hgb D) c).1 hc
  rw [hac]
  exact MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc'
    (show IsProper (D.f ≫ g) by infer_instance)

/-- **A small model does not change log discrepancies.** If `g : Y' ⟶ X` is small and `(X, 0)`
is a pair, a valuation `w` of `k(Y')` with `a(w; Y', 0) = a` has `a(w; X, 0) = a` read on `k(X)`
through `g^*`. -/
private theorem isValuationLogDiscrepancy_comap_of_isSmallMorphism [IsAlgClosed k] [CharZero k]
    (hP : MMP.Mori.IsPair sX 0) {g : Y' ⟶ X} [IsDominant g]
    (hg : IsSmallMorphism (g ≫ sX) sX g)
    {w : Valuation Y'.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (hw : IsValuationLogDiscrepancy (g ≫ sX) 0 w a) :
    IsValuationLogDiscrepancy sX 0 (w.comap (functionFieldMap g)) a := by
  haveI := hg.isProper
  obtain ⟨n, D, hDp, rfl, hD⟩ := hw
  haveI := hDp
  exact ⟨n, compDivisorOver g hg.isBirationalMorphism D, (inferInstance : IsProper (D.f ≫ g)),
    valuation_compDivisorOver g _ D, isLogDiscrepancy_compDivisorOver hP hg hD⟩

/-- A valuation of `k(Y')` centred on a closed subset of the fibre `g⁻¹(x)` of a proper birational
`g : Y' ⟶ X` has centre `{x}` when read on `k(X)` through `g^*`. -/
private theorem isCentre_comap_of_subset_preimage {g : Y' ⟶ X} (hg : IsBirationalMorphism g)
    [IsProper g] [IsDominant g] {S : IrreducibleCloseds Y'}
    {w : Valuation Y'.functionField (WithZero (Multiplicative ℤ))}
    (hw : MMP.Intersection.IsCentre k (g ≫ sX) w S) {x : X} (hx : IsClosed ({x} : Set X))
    (hS : (S : Set Y') ⊆ g.base ⁻¹' {x}) :
    MMP.Intersection.IsCentre k sX (w.comap (functionFieldMap g))
      ⟨{x}, isIrreducible_singleton, hx⟩ := by
  obtain ⟨D, hDp, rfl, rfl⟩ := hw
  haveI := hDp
  refine ⟨compDivisorOver g hg D, (inferInstance : IsProper (D.f ≫ g)),
    (valuation_compDivisorOver g hg D).symm, IrreducibleCloseds.ext ?_⟩
  have h1 : D.f D.E.genericPoint ∈ (D.center : Set Y') := by
    rw [DivisorOver.center_eq_closure_genericPoint]
    exact subset_closure rfl
  rw [coe_center_compDivisorOver, (hS h1 : _ = x)]
  exact hx.closure_eq.symm

end Small

/-- **Restriction along an étale morphism keeps log discrepancies.** Let `q : Yₑ ⟶ Y₀` be étale
with `(Y₀, 0)` a pair, and `η'` a point at which `q` is an isomorphism on residue fields. A
valuation `w` of `k(Yₑ)` centred at `closure {η'}` with `a(w; Yₑ, 0) = a` restricts to one of
`k(Y₀)` with `a(w|; Y₀, 0) = a`. -/
private theorem isValuationLogDiscrepancy_comap_of_etale {k : Type u} [Field k] [CharZero k]
    {Y₀ Yₑ : Scheme.{u}} [IsIntegral Y₀] [IsLocallyNoetherian Y₀] [IsNormal Y₀]
    [IsIntegral Yₑ] [IsLocallyNoetherian Yₑ] [IsNormal Yₑ]
    {s₀ : Y₀ ⟶ Spec (.of k)} (q : Yₑ ⟶ Y₀) [Etale q] [IsDominant q]
    (h₀ : MMP.Mori.IsPair s₀ 0) (hₑ : MMP.Mori.IsNormalVariety k (q ≫ s₀))
    {η' : Yₑ} (hκ : IsIso (q.residueFieldMap η'))
    {Zₑ : IrreducibleCloseds Yₑ} (hZₑ : (Zₑ : Set Yₑ) = closure {η'})
    {w : Valuation Yₑ.functionField (WithZero (Multiplicative ℤ))}
    (hw : MMP.Intersection.IsCentre k (q ≫ s₀) w Zₑ) {a : ℝ}
    (hwa : IsValuationLogDiscrepancy (q ≫ s₀) 0 w a) :
    IsValuationLogDiscrepancy s₀ 0 (w.comap (functionFieldMap q)) a := by
  obtain ⟨n, Dₑ, hDₑp, hDₑv, hDₑ⟩ := hwa
  obtain ⟨D₀, hD₀p, hD₀v, -⟩ := MMP.Intersection.isCentre_comap_functionFieldMap_of_etale s₀ q
    h₀.1 hₑ η' hκ Zₑ hZₑ ⟨closure {q.base η'}, isIrreducible_singleton.closure, isClosed_closure⟩
    rfl w hw
  have h := (MMP.Intersection.isLogDiscrepancy_iff_of_etale_of_isCentre s₀ q h₀ hₑ η' hκ Zₑ hZₑ
    w hw Dₑ D₀ hDₑp hD₀p hDₑv hD₀v.symm n a).1 (by simpa using hDₑ)
  exact ⟨n, D₀, hD₀p, hD₀v.symm, by simpa using h⟩

private theorem solution
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (hYQ : IsQFactorial sY)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 3)
    (Θ : QDivisor Y) (hΘ0 : 0 ≤ Θ) (hΘ : IsKltTerminalPair sY Θ)
    (y : Y) (hy : y ∈ singularLocus sY) (hyc : IsClosed ({y} : Set Y))
    (hyΘ : ∃ D : MMP.Mori.PrimeDivisor Y, 0 < Θ D ∧ y ∈ (D.support : Set Y))
    (T : IrreducibleCloseds ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hT : (T : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) = pointSettingCurve sY y)
    (To : (curveScheme T).Opens)
    (hTo : IsLocalSystemOpen (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To) :
    (curveLocalSystemRank (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To : ℕ∞) ≤
      {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
        (∃ Z : IrreducibleCloseds Y, (Z : Set Y) = {y} ∧ MMP.Intersection.IsCentre ℂ sY v Z) ∧
        IsValuationLogDiscrepancy sY 0 v 2 ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.encard := by
  classical
  have hYn : IsNormalVariety ℂ sY := hYQ.1
  have hΘq : Θ.IsQCartier := isQCartier_of_isQFactorial sY hYQ Θ
  obtain ⟨n, K, hK, -⟩ := hΘ.1.1.isPair.2
  have hKq : (Divisor.toQDivisor K).IsQCartier := isQCartier_of_isQFactorial sY hYQ _
  have hterm : IsTerminalVariety sY :=
    (hΘ.isTerminalVariety_and_three_le_closedsCodimension_singularLocus hΘq hK hKq).1
  obtain ⟨Yt, π, hYtv, hπp, hπb, hYts, hπiso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution sY hYn.1
  have hset : IsThreefoldPointSetting sY π y :=
    ⟨hYQ, hYproj, hYdim, hterm, ⟨hYn.1, hYtv, hYts,
      isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism sY
        ((MMP.Mori.isProjectiveVariety_iff _ _).1 hYproj).2 π hπp, hπb⟩, hπiso, hy, hyc⟩
  obtain ⟨M, hMinv, hM⟩ := hset.exists_isPuncturedIndependent_pullback T hT To hTo
  obtain ⟨U, hUi, hUl, hUn', hUq, hUn, hUdim, hu, ⟨Mt, hMt, hMtr⟩, hUt, hUts, hπUp, hπUb,
    hπUi⟩ := hset.exists_elementaryEtaleNeighborhood_isInvertible M hMinv
  haveI := hUi
  haveI := hUl
  haveI := hUn'
  have hUterm : IsTerminalVariety (U.obj.toBase ≫ sY) :=
    (IsTerminalVariety.comp_etale U.obj.toBase hUn hterm).1
  obtain ⟨U', hU'i, hU'l, hU'n, sU', g, hgp, hgs, hU'Q, hU'term⟩ :=
    hUterm.exists_isSmallMorphism_isQFactorial hUn hUq hUdim
  have hcount := hset.le_encard_irreducibleComponents_preimage T hT To hTo M hMinv hM U hUq hUn
    hUdim hu Mt hMt hMtr hUt hUts hπUp hπUb hπUi hgp hgs hU'Q
  refine hcount.trans ?_
  obtain rfl := hgs.comp_eq
  have hgb := hgs.isBirationalMorphism
  haveI : IsDominant g := hgb.isDominant
  haveI : IsDominant U.obj.toBase := Stacks.Chow.isDominant_of_flat U.obj.toBase
  have hκ : IsIso (U.obj.toBase.residueFieldMap U.obj.point) := by
    haveI : IsIso U.obj.residueFieldMap := U.property
    have h : U.obj.toBase.residueFieldMap U.obj.point =
        (Y.residueFieldCongr U.obj.map_point).hom ≫ U.obj.residueFieldMap := by
      rw [EtaleNeighborhood.residueFieldMap_def, Iso.hom_inv_id_assoc]
    rw [h]
    infer_instance
  have hYP : MMP.Mori.IsPair sY 0 := hterm.1.1.isPair
  have hUP : MMP.Mori.IsPair (U.obj.toBase ≫ sY) 0 := hUterm.1.1.isPair
  have hU'v := hgs.isNormalVariety_source
  have hU'dim : topologicalKrullDim U' = 3 := by
    haveI := hUn.1
    haveI := hU'v.1
    rwa [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
      (U.obj.toBase ≫ sY) (g ≫ U.obj.toBase ≫ sY) hgb]
  let Zₑ : IrreducibleCloseds U.obj.scheme := ⟨{U.obj.point}, isIrreducible_singleton, hu⟩
  have hZₑ : (Zₑ : Set U.obj.scheme) = closure {U.obj.point} := hu.closure_eq.symm
  let Z₀ : IrreducibleCloseds Y := ⟨{y}, isIrreducible_singleton, hyc⟩
  have hZ₀ : (Z₀ : Set Y) = closure {U.obj.toBase.base U.obj.point} := by
    rw [U.obj.map_point]
    exact hyc.closure_eq.symm
  have hyΘ' : (Z₀ : Set Y) ⊆ Θ.supp := by
    obtain ⟨D, hD0, hyD⟩ := hyΘ
    exact Set.singleton_subset_iff.mpr (DivisorWithCoeffs.mem_supp_iff.mpr ⟨D, hD0.ne', hyD⟩)
  have hcl : IsClosed (g.base ⁻¹' {U.obj.point}) := hu.preimage g.continuous
  have hex : ∀ Z ∈ {Z ∈ irreducibleComponents ↥(g.base ⁻¹' {U.obj.point}) |
      topologicalKrullDim Z = 1}, ∃ w : Valuation U'.functionField (WithZero (Multiplicative ℤ)),
      ∃ S : IrreducibleCloseds U', (S : Set U') = Subtype.val '' Z ∧
        MMP.Intersection.IsCentre ℂ (g ≫ U.obj.toBase ≫ sY) w S ∧
        MMP.Intersection.IsCentre ℂ (U.obj.toBase ≫ sY) (w.comap (functionFieldMap g)) Zₑ ∧
        IsValuationLogDiscrepancy (U.obj.toBase ≫ sY) 0 (w.comap (functionFieldMap g)) 2 := by
    rintro Z ⟨hZc, hZd⟩
    let S : IrreducibleCloseds U' := ⟨Subtype.val '' Z,
      hZc.1.image _ continuous_subtype_val.continuousOn,
      hcl.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents Z hZc)⟩
    obtain ⟨w, hw, hw2⟩ :=
      exists_isCentre_isValuationLogDiscrepancy_two_of_topologicalKrullDim_eq_one hU'Q hU'term
        hU'dim S ((topologicalKrullDim_image_val _ Z).trans hZd)
    haveI := hgs.isProper
    exact ⟨w, S, rfl, hw, isCentre_comap_of_subset_preimage hgb hw hu
      (Subtype.coe_image_subset _ Z),
      isValuationLogDiscrepancy_comap_of_isSmallMorphism hUP hgs hw2⟩
  haveI : Nonempty (Valuation U'.functionField (WithZero (Multiplicative ℤ))) := ⟨1⟩
  choose! W hW using hex
  refine Set.encard_le_encard_of_injOn
    (f := fun Z => ((W Z).comap (functionFieldMap g)).comap (functionFieldMap U.obj.toBase))
    (fun Z hZ => ?_) (fun Z₁ h₁ Z₂ h₂ heq => ?_)
  · obtain ⟨-, -, -, hwU, hwU2⟩ := hW Z hZ
    have h2 := isValuationLogDiscrepancy_comap_of_etale U.obj.toBase hYP hUn hκ hZₑ hwU hwU2
    have hv0 := MMP.Intersection.isCentre_comap_functionFieldMap_of_etale sY U.obj.toBase hYn hUn
      U.obj.point hκ Zₑ hZₑ Z₀ hZ₀ _ hwU
    exact ⟨⟨Z₀, rfl, hv0⟩, h2,
      exists_isValuationLogDiscrepancy_lt_of_subset_supp hYQ hΘ0 hv0 hyΘ' h2⟩
  · obtain ⟨S₁, hS₁, ⟨D₁, -, hv₁, hc₁⟩, e1, -⟩ := hW Z₁ h₁
    obtain ⟨S₂, hS₂, ⟨D₂, -, hv₂, hc₂⟩, e2, -⟩ := hW Z₂ h₂
    have hgw : (W Z₁).comap (functionFieldMap g) = (W Z₂).comap (functionFieldMap g) :=
      MMP.Intersection.injOn_comap_functionFieldMap_of_etale sY U.obj.toBase hYn hUn U.obj.point
        hκ Zₑ hZₑ e1 e2 heq
    have hw : W Z₁ = W Z₂ := by
      ext t
      obtain ⟨s, rfl⟩ := hgb.functionFieldMap_bijective.2 t
      exact DFunLike.congr_fun hgw s
    have hc := MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hU'v.1
      (hv₁.symm.trans (hw ▸ hv₂))
    have h12 : Subtype.val '' Z₁ = Subtype.val '' Z₂ := by
      rw [← hS₁, ← hS₂, hc₁.trans (hc.trans hc₂.symm)]
    exact Subtype.val_injective.image_injective h12

end Proof_prop_mmp_indexb_point_valuations

end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

namespace MMP.Fourfold

open MMP.Mori

/-- **Valuations centred at a singular point.** Let `Y` be a normal projective `ℚ`-factorial
complex threefold, `(Y, Θ)` an effective terminal pair, and `y ∈ Sing Y` a closed point lying on a
prime divisor `D` with `0 < Θ D`. Let `T` be the curve `{y} × ℙ¹ ⊆ Y × ℙ¹` and `T°` a local-system
open of `T`, so that `b = curveLocalSystemRank T°` is `b_{T}`. Then there are at least `b`
normalized divisorial valuations `v` of `ℂ(Y)` with centre `{y}`, `a(v; Y, 0) = 2` and
`a(v; Y, Θ) < 2`. -/
@[mmp "prop_mmp_indexb_point_valuations"]
public theorem le_encard_setOf_isCentre_singleton
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (hYQ : IsQFactorial sY)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 3)
    (Θ : QDivisor Y) (hΘ0 : 0 ≤ Θ) (hΘ : IsKltTerminalPair sY Θ)
    (y : Y) (hy : y ∈ singularLocus sY) (hyc : IsClosed ({y} : Set Y))
    (hyΘ : ∃ D : MMP.Mori.PrimeDivisor Y, 0 < Θ D ∧ y ∈ (D.support : Set Y))
    (T : IrreducibleCloseds ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hT : (T : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) = pointSettingCurve sY y)
    (To : (curveScheme T).Opens)
    (hTo : IsLocalSystemOpen (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To) :
    (curveLocalSystemRank (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To : ℕ∞) ≤
      {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
        (∃ Z : IrreducibleCloseds Y, (Z : Set Y) = {y} ∧ MMP.Intersection.IsCentre ℂ sY v Z) ∧
        IsValuationLogDiscrepancy sY 0 v 2 ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.encard :=
  Proof_prop_mmp_indexb_point_valuations.solution sY hYQ hYproj hYdim Θ hΘ0 hΘ y hy hyc hyΘ
    T hT To hTo

end MMP.Fourfold
