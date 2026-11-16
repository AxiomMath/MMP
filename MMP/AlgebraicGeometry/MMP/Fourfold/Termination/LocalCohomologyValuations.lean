module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.LocalGenericLineBundles
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.EtaleDatumQFactorialization
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleLineBundleExtension
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreCurveCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.EtaleDatum
public import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
public import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
public import MMP.AlgebraicGeometry.Singularities.EtaleNeighbourhoodTerminal
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleIndependence
public import MMP.AlgebraicGeometry.Singularities.SmallModelCrepant
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.SmallModelTerminal
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleDatumTerminal
public import MMP.AlgebraicGeometry.Morphisms.Etale.DivisorialValuationRestriction
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyCoeff
public import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite

/-!
# Valuations from local cohomology

Let `Y` be a normal projective `ℚ`-factorial complex fourfold and `(Y, Θ)` an effective terminal
pair with rational boundary. Let `T ⊆ Sing Y` be an irreducible curve contained in a prime
divisor `D` of positive coefficient in `Θ`, and let `b_T` be the rank of the punctured local
system `𝒱_T = (R²j_* ℚ_{Y_reg})|_{T°}`, the dimension of `H²_c(T°, 𝒱_T)` on a local-system open
`T°`. Then there are at least `b_T` distinct normalized divisorial valuations `v` of `ℂ(Y)` with
centre `c_Y(v) = T`, log discrepancy `a(v; Y, 0) = 2` and `a(v; Y, Θ) < 2`.

## Main results

* `MMP.Fourfold.IsKltTerminalPair.curveLocalSystemRank_le_encard`: the set of such valuations
  has cardinality at least `MMP.Fourfold.curveLocalSystemRank sY T°`.

## Implementation notes

* "At least `b_T` distinct valuations" is the inequality `b_T ≤ #S` in `ℕ∞` for the set `S` of
  valuations with the three properties, `Set.encard` being `⊤` on an infinite set.
* The integer `b_T` does not depend on the local-system open on which it is computed, so the
  result is stated for every local-system open `T°`, with `b_T = curveLocalSystemRank sY T°`.
* Valuations are Mathlib's `Valuation ℂ(Y) ℤᵐ⁰`. A normalized divisorial valuation with centre
  `T` is `MMP.Intersection.IsCentre`, and `a(v; Y, B) = a` is
  `MMP.Fourfold.IsValuationLogDiscrepancy`.
* The positive-coefficient component of `Θ` containing `T` is a prime divisor `D` with
  `0 < Θ D` and `T ⊆ D`.

## References

* [Termination for projective log canonical fourfolds with rational boundary (OpenAI, 2026)]
-/

@[expose] public section

section

universe u

namespace Proof_prop_oai4_local_valuations

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Fourfold MMP.Mori

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

/-- The irreducible closed set `{x}⁻` spanned by a point. -/
private def closurePoint {X : Scheme.{u}} (x : X) : IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- The underlying set of `closurePoint x` is `{x}⁻`. -/
private theorem coe_closurePoint {X : Scheme.{u}} (x : X) :
    (closurePoint x : Set X) = closure {x} := rfl

/-- The generic point of `{x}⁻` is `x`. -/
private theorem genericPoint_closurePoint {X : Scheme.{u}} (x : X) :
    (closurePoint x).isIrreducible.genericPoint = x := by
  have h := (closurePoint x).isIrreducible.isGenericPoint_genericPoint_closure
  rw [(closurePoint x).isClosed.closure_eq] at h
  exact h.eq (isGenericPoint_closure)

/-- On a `ℚ`-factorial terminal complex variety `X`, every point `x` of codimension two is the
generic point of the centre of a normalized divisorial valuation `w` with `a(w; X, 0) = 2`: `X`
is smooth in codimension two, so `X` is smooth at `x`, and `w` is the valuation of the exceptional
divisor of the blow-up of `{x}⁻` there. -/
private theorem exists_isCentre_isValuationLogDiscrepancy_two_of_coheight_eq_two
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hQ : IsQFactorial sX) (hT : IsTerminalVariety sX) (x : X)
    (hx : Order.coheight x = 2) :
    ∃ w : Valuation X.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sX w (closurePoint x) ∧ IsValuationLogDiscrepancy sX 0 w 2 := by
  have hP : MMP.Mori.IsPair sX 0 := hT.1.1.isPair
  obtain ⟨n, K, hK, -⟩ := hP.2
  have hcod := (hT.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    (isQCartier_of_isQFactorial sX hQ 0) hK (isQCartier_of_isQFactorial sX hQ _)).2
  have hgen := genericPoint_closurePoint x
  have hcodS : codimension (closurePoint x) = 2 := by
    rwa [MMP.Flips.codimension_eq_coheight_genericPoint, hgen]
  have hsm : (closurePoint x).isIrreducible.genericPoint ∈ smoothLocus sX := by
    rw [hgen]
    by_contra h
    have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hcod x h
    rw [hx] at this
    norm_num at this
  obtain ⟨w, -, hw, hw2⟩ :=
    exists_isCentre_isValuationLogDiscrepancy_two_of_codimension_eq_two sX hP _ hcodS hsm
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
    rw [coe_apply_of_toQDivisor_eq hD' P]; simp [DivisorWithCoeffs.coeff] at h0 ⊢; simp [h0]
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
    rw [hfac]; exact h1
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
  have hn : n = n₀ := by
    have h := (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha).symm.trans
      hK'.topologicalKrullDim_eq
    exact_mod_cast h
  subst hn
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

/-- A valuation `w` of `k(Y')` with centre `S` has, read on `k(X)` through a proper birational
`g : Y' ⟶ X`, the centre `{g(η_S)}⁻`. -/
private theorem isCentre_comap_closurePoint {g : Y' ⟶ X} (hg : IsBirationalMorphism g)
    [IsProper g] [IsDominant g] {S : IrreducibleCloseds Y'}
    {w : Valuation Y'.functionField (WithZero (Multiplicative ℤ))}
    (hw : MMP.Intersection.IsCentre k (g ≫ sX) w S) :
    MMP.Intersection.IsCentre k sX (w.comap (functionFieldMap g))
      (closurePoint (g S.isIrreducible.genericPoint)) := by
  obtain ⟨D, hDp, rfl, rfl⟩ := hw
  haveI := hDp
  refine ⟨compDivisorOver g hg D, (inferInstance : IsProper (D.f ≫ g)),
    (valuation_compDivisorOver g hg D).symm, IrreducibleCloseds.ext ?_⟩
  have h1 : IsGenericPoint (D.f D.E.genericPoint) (D.center : Set Y') :=
    (DivisorOver.center_eq_closure_genericPoint D).symm
  have h2 := D.center.isIrreducible.isGenericPoint_genericPoint_closure
  rw [D.center.isClosed.closure_eq] at h2
  rw [coe_closurePoint, coe_center_compDivisorOver, h1.eq h2]

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

/-! ### Codimension of the generic points of fibre curves -/

/-- **Flat, locally quasi-finite morphisms preserve coheights.** Such a morphism is strictly
monotone for the specialization order (distinct points of a fibre are not specializations of
one another) and generizations lift along it. -/
private theorem coheight_apply_eq {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
    [LocallyQuasiFinite h] (y : Y) : Order.coheight (h y) = Order.coheight y := by
  refine (Order.coheight_eq_of_strictMono (⇑h) (fun a b hab => ?_) (fun a b hab => ?_) y).symm
  · have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map h.continuous)) fun hle => ?_
    have heq : h b = h a :=
      ((hba.map h.continuous).antisymm (Scheme.le_iff_specializes.mp hle)).eq
    exact hab.ne (MMP.Flips.eq_of_specializes_of_locallyQuasiFinite h hba heq).symm
  · obtain ⟨a', ha', rfl⟩ := Flat.generalizingMap h (Scheme.le_iff_specializes.mp hab.le)
    refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun hle => ?_, rfl⟩
    have heq : a' = a := (ha'.antisymm (Scheme.le_iff_specializes.mp hle)).eq
    rw [heq] at hab
    exact lt_irrefl _ hab

/-- The transcendence degree of `κ(t)` over a field `L`, for the `L`-algebra structure given by
global sections of a morphism `q : T ⟶ Spec L`. -/
private noncomputable def trdegΓ (L : Type u) [Field L] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of L)) (t : T) : Cardinal.{u} :=
  letI : Algebra L (T.residueField t) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ q.appTop ≫ T.Γevaluation t).hom.toAlgebra
  Algebra.trdeg L (T.residueField t)

/-- Additivity of `trdegΓ` along a morphism. -/
private theorem trdegΓ_comp (L : Type u) [Field L] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of L)) (x : X) :
    trdegΓ L (f ≫ q) x = trdegΓ L q (f x) + Stacks.Chow.residueTrdeg f x := by
  letI : Algebra L (Y.residueField (f x)) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ q.appTop ≫ Y.Γevaluation (f x)).hom.toAlgebra
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra L (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of L)).inv ≫ (f ≫ q).appTop ≫ X.Γevaluation x).hom.toAlgebra
  have e : (Scheme.ΓSpecIso (.of L)).inv ≫ (f ≫ q).appTop ≫ X.Γevaluation x =
      ((Scheme.ΓSpecIso (.of L)).inv ≫ q.appTop ≫ Y.Γevaluation (f x)) ≫ f.residueFieldMap x := by
    rw [Scheme.Hom.comp_appTop]
    simp only [Category.assoc, Scheme.Γevaluation_naturality, Scheme.Γevaluation_naturality_assoc]
  haveI : IsScalarTower L (Y.residueField (f x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congrArg (fun φ ↦ φ.hom a) e
  haveI : FaithfulSMul L (Y.residueField (f x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  haveI : FaithfulSMul (Y.residueField (f x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  exact (trdeg_add_eq L (Y.residueField (f x)) (A := X.residueField x)).symm

/-- The residue field of the point of `Spec L` is algebraic over `L`. -/
private theorem trdegΓ_id (L : Type u) [Field L] (t : Spec (.of L)) :
    trdegΓ L (𝟙 _) t = 0 := by
  have h := topologicalKrullDim_closure_singleton_eq_trdeg L (Spec (.of L)) (𝟙 _) t
  have hle : topologicalKrullDim (closure ({t} : Set (Spec (.of L)))) ≤ 0 := by
    refine (topologicalKrullDim_subspace_le _ _).trans ?_
    have : topologicalKrullDim (PrimeSpectrum L) = 0 := by
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    exact this.le
  rw [h] at hle
  have : Cardinal.toENat (trdegΓ L (𝟙 _) t) = 0 := by
    have h0 : ((Cardinal.toENat (trdegΓ L (𝟙 _) t) : ℕ∞) : WithBot ℕ∞) ≤
        ((0 : ℕ∞) : WithBot ℕ∞) := hle
    exact nonpos_iff_eq_zero.mp (WithBot.coe_le_coe.mp h0)
  exact Cardinal.toENat_eq_zero.mp this

/-- The dimension of the closure of a point `t` of a scheme locally of finite type over a field
is the transcendence degree of `κ(t)` over that field. -/
private theorem topologicalKrullDim_closure_singleton_eq_residueTrdeg {L : Type u} [Field L]
    {T : Scheme.{u}} (q : T ⟶ Spec (.of L)) [LocallyOfFiniteType q] (t : T) :
    topologicalKrullDim (closure ({t} : Set T)) =
      (Cardinal.toENat (Stacks.Chow.residueTrdeg q t) : WithBot ℕ∞) := by
  have h := topologicalKrullDim_closure_singleton_eq_trdeg L T q t
  have h2 := trdegΓ_comp L q (𝟙 _) t
  rw [Category.comp_id, trdegΓ_id, zero_add] at h2
  rw [← h2]
  exact h

/-- The residue field at the generic point `ξ` of a proper curve in the scheme fibre `g⁻¹(s)`
has transcendence degree one over `κ(s)`. -/
private theorem trdeg_residueField_fiberι_eq_one {X S : Scheme.{u}} (g : X ⟶ S)
    [LocallyOfFiniteType g] {s : S} (C : ProperCurve (g.fiberToSpecResidueField s)) :
    letI := (g.residueFieldMap (g.fiberι s C.point)).hom.toAlgebra
    Algebra.trdeg (S.residueField (g (g.fiberι s C.point))) (X.residueField (g.fiberι s C.point))
      = 1 := by
  have hC : topologicalKrullDim (closure ({C.point} : Set (g.fiber s))) = 1 := by
    rw [← C.dim_eq]
    set I := Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set (g.fiber s)))
    have hr : Set.range I.subschemeι = closure ({C.point} : Set (g.fiber s)) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have he := (IsClosedImmersion.isClosedEmbedding I.subschemeι).isEmbedding
    rw [← hr]
    exact (IsHomeomorph.topologicalKrullDim_eq _ he.toHomeomorph.isHomeomorph).symm
  have hq : LocallyOfFiniteType (g.fiberToSpecResidueField s) := inferInstance
  have key := @topologicalKrullDim_closure_singleton_eq_residueTrdeg (S.residueField s) _
    (g.fiber s) (g.fiberToSpecResidueField s) hq C.point
  rw [key] at hC
  have h1 : Stacks.Chow.residueTrdeg (g.fiberToSpecResidueField s) C.point = 1 := by
    have : Cardinal.toENat (Stacks.Chow.residueTrdeg (g.fiberToSpecResidueField s) C.point) = 1 := by
      exact_mod_cast hC
    exact Cardinal.toENat_eq_one.mp this
  rw [Stacks.Chow.residueTrdeg_fiberToSpecResidueField] at h1
  exact h1

/-- The fibre inclusion `g⁻¹(s) ⟶ X` maps into `g⁻¹{s}`. -/
private theorem apply_fiberι {X S : Scheme.{u}} (g : X ⟶ S) (s : S) (x : g.fiber s) :
    g (g.fiberι s x) = s := by
  have : g.fiberι s x ∈ Set.range (g.fiberι s) := ⟨x, rfl⟩
  rw [Scheme.Hom.range_fiberι] at this
  exact this

/-- **Codimension of the generic point of a fibre curve of a small morphism.** Let `g : Y' ⟶ X`
be a small morphism and `ξ` the generic point of a proper curve in the scheme fibre `g⁻¹(s)`.
Then `codim ξ + 1 ≤ codim s`, by the dimension inequality for the birational `g` at `ξ`
(`trdeg_{κ(s)} κ(ξ) = 1`), and `2 ≤ codim ξ`: `g` is not a local isomorphism at `ξ`, as `κ(ξ)` is
transcendental over `κ(s)`, and the exceptional locus of `g` has codimension at least two. -/
private theorem coheight_fiberι_add_one_le {k : Type u} [Field k] {X Y' : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] {sX : X ⟶ Spec (.of k)} {g : Y' ⟶ X}
    (hg : IsSmallMorphism (g ≫ sX) sX g) {s : X}
    (C : ProperCurve (g.fiberToSpecResidueField s)) :
    Order.coheight (g.fiberι s C.point) + 1 ≤ Order.coheight s ∧
      2 ≤ Order.coheight (g.fiberι s C.point) := by
  have hgb := hg.isBirationalMorphism
  haveI : IsDominant g := hgb.isDominant
  haveI := hg.isProper
  have htr := trdeg_residueField_fiberι_eq_one g C
  have hξs := apply_fiberι g s C.point
  set ξ := g.fiberι s C.point
  refine ⟨?_, ?_⟩
  · have hle := localDimension_add_trdeg_le g ξ
    have h0 : (letI := (dominantFunctionFieldMap g).toAlgebra
        Algebra.trdeg X.functionField Y'.functionField) = 0 := by
      letI := (dominantFunctionFieldMap g).toAlgebra
      have hs : Function.Surjective (algebraMap X.functionField Y'.functionField) := by
        change Function.Surjective (dominantFunctionFieldMap g)
        rw [MMP.Mori.dominantFunctionFieldMap_eq_functionFieldMap]
        exact hgb.functionFieldMap_bijective.2
      haveI : Algebra.IsAlgebraic X.functionField Y'.functionField :=
        ⟨fun x => by obtain ⟨y, rfl⟩ := hs x; exact isAlgebraic_algebraMap y⟩
      exact trdeg_eq_zero
    rw [h0, htr, ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hξs] at hle
    simp only [map_one, map_zero, WithBot.coe_zero, add_zero] at hle
    exact_mod_cast hle
  · by_contra hlt
    have hbir : g ξ ∈ biregularLocus g := by
      by_contra hx
      exact hlt (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hg.two_le_codimension ξ hx)
    have := isIso_stalkMap_of_mem g hbir
    have hsurj : Function.Surjective (g.residueFieldMap ξ).hom := by
      intro b
      obtain ⟨a, rfl⟩ := Y'.residue_surjective ξ b
      obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (g.stalkMap ξ)).2 a
      refine ⟨X.residue (g ξ) c, ?_⟩
      have := congrArg (fun φ => φ.hom c) (Scheme.residue_residueFieldMap g ξ)
      simpa using this
    letI := (g.residueFieldMap ξ).hom.toAlgebra
    haveI : Algebra.IsAlgebraic (X.residueField (g ξ)) (Y'.residueField ξ) :=
      ⟨fun x => by obtain ⟨y, rfl⟩ := hsurj x; exact isAlgebraic_algebraMap y⟩
    rw [trdeg_eq_zero] at htr
    exact zero_ne_one htr

/-- **The valuation of a fibre curve of a small terminal model.** Let `g : Y' ⟶ X` be a small
morphism with `Y'` `ℚ`-factorial and terminal, `(X, 0)` a pair, and `s ∈ X` a point of
codimension three. The generic point `ξ` of a proper curve of the scheme fibre `g⁻¹(s)` has
codimension two, so it is the generic point of the centre of a valuation `w` of `ℂ(Y')` with
`a(w; Y', 0) = 2`; read on `ℂ(X)` through `g^*`, `w` has centre `{s}⁻` and log discrepancy `2`. -/
private theorem exists_valuation_of_properCurve
    {X Y' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] {sX : X ⟶ Spec (.of ℂ)} (hP : MMP.Mori.IsPair sX 0)
    {g : Y' ⟶ X} [IsDominant g] (hg : IsSmallMorphism (g ≫ sX) sX g)
    (hQ : IsQFactorial (g ≫ sX)) (hterm : IsTerminalVariety (g ≫ sX)) {s : X}
    (hs : Order.coheight s = 3) (C : ProperCurve (g.fiberToSpecResidueField s)) :
    ∃ w : Valuation Y'.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ (g ≫ sX) w (closurePoint (g.fiberι s C.point)) ∧
      MMP.Intersection.IsCentre ℂ sX (w.comap (functionFieldMap g)) (closurePoint s) ∧
      IsValuationLogDiscrepancy sX 0 (w.comap (functionFieldMap g)) 2 := by
  haveI := hg.isProper
  obtain ⟨h1, h2⟩ := coheight_fiberι_add_one_le hg C
  rw [hs, show (3 : ℕ∞) = 2 + 1 from rfl] at h1
  obtain ⟨w, hw, hw2⟩ := exists_isCentre_isValuationLogDiscrepancy_two_of_coheight_eq_two hQ
    hterm _ (le_antisymm ((ENat.add_le_add_iff_right ENat.one_ne_top).1 h1) h2)
  have hcen := isCentre_comap_closurePoint hg.isBirationalMorphism hw
  rw [genericPoint_closurePoint, apply_fiberι] at hcen
  exact ⟨w, hw, hcen, isValuationLogDiscrepancy_comap_of_isSmallMorphism hP hg hw2⟩

private theorem solution
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y}
    (hQ : IsQFactorial sY) (hproj : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 4) (hΘ : IsKltTerminalPair sY Θ)
    (hT : topologicalKrullDim (T : Set Y) = 1) (hTsing : (T : Set Y) ⊆ singularLocus sY)
    (D : MMP.Mori.PrimeDivisor Y) (hD : 0 < Θ D) (hTD : (T : Set Y) ⊆ D.support)
    (To : (curveScheme T).Opens) (hTo : IsLocalSystemOpen sY To) :
    (curveLocalSystemRank sY To : ℕ∞) ≤
      {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
        MMP.Intersection.IsCentre ℂ sY v T ∧
        IsValuationLogDiscrepancy sY (0 : QDivisor Y) v 2 ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.encard := by
  classical
  have hYn : IsNormalVariety ℂ sY := hQ.1
  have hΘq : Θ.IsQCartier := isQCartier_of_isQFactorial sY hQ Θ
  obtain ⟨n, K, hK, -⟩ := hΘ.1.1.isPair.2
  have hterm : IsTerminalVariety sY :=
    (hΘ.isTerminalVariety_and_three_le_closedsCodimension_singularLocus hΘq hK
      (isQCartier_of_isQFactorial sY hQ _)).1
  -- a strong resolution makes `(Y, Θ, T, π)` a local setting, with `b_T` independent lines
  obtain ⟨Yt, π, hYtv, hπp, hπb, hYts, hπiso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution sY hYn.1
  have hLS : IsLocalSetting sY Θ T π :=
    ⟨hQ, hproj, hdim, hΘ, hT, hTsing, ⟨hYn.1, hYtv, hYts,
      isProjectiveMorphism_of_isProjective_of_isProjectiveMorphism sY
        ((MMP.Mori.isProjectiveVariety_iff _ _).1 hproj).2 π hπp, hπb⟩, hπiso⟩
  obtain ⟨L, hLinv, hLind⟩ := hLS.exists_isPuncturedIndependent To hTo
  obtain ⟨E, -⟩ := IsLocalSetting.exists_localEtaleDatum_isResolution hLS L hLinv
  haveI : IsIntegral E.scheme := E.isQuasiProjectiveVariety.toIsIntegral
  haveI : IsNormal E.scheme := E.isNormal
  haveI : IsLocallyNoetherian E.scheme := LocallyOfFiniteType.isLocallyNoetherian (E.map ≫ sY)
  obtain ⟨Y', hY'i, hY'l, hY'n, g, hgs, hgp, hgQ⟩ :=
    LocalEtaleDatum.exists_isSmallMorphism_isQFactorial hLS E
  refine (LocalEtaleDatum.le_card_properCurve_fiber hLS hLind E g hgs hgp hgQ).trans ?_
  rw [← Set.encard_univ]
  have hgb := hgs.isBirationalMorphism
  haveI : IsDominant g := hgb.isDominant
  haveI : IsDominant E.map := Stacks.Chow.isDominant_of_flat E.map
  have hκ : IsIso (E.map.residueFieldMap E.point) := by
    haveI : IsIso E.neighborhood.obj.residueFieldMap := E.isIso_residueFieldMap
    have h : E.map.residueFieldMap E.point =
        (Y.residueFieldCongr E.map_point).hom ≫ E.neighborhood.obj.residueFieldMap := by
      rw [EtaleNeighborhood.residueFieldMap_def, Iso.hom_inv_id_assoc]
    rw [h]
    infer_instance
  have hEn : IsNormalVariety ℂ (E.map ≫ sY) := hgs.isNormalVariety_target
  have hEP : MMP.Mori.IsPair (E.map ≫ sY) 0 :=
    (LocalEtaleDatum.exists_isCanonicalDivisor_isPullback_and_isTerminalVariety hLS E).2.1.1.isPair
  -- `η_T`, hence `η'`, has codimension three
  have hcT : Order.coheight (localSettingGenericPoint T) = 3 := by
    haveI : LocallyOfFiniteType sY := hYn.1.toLocallyOfFiniteType
    have hadd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
      (localSettingGenericPoint T)
    rw [(isGenericPoint_localSettingGenericPoint T).def, hT, hdim] at hadd
    have h : 1 + Order.coheight (localSettingGenericPoint T) = 4 := WithBot.coe_injective hadd
    rw [show (4 : ℕ∞) = 1 + 3 from rfl] at h
    exact (WithTop.add_left_inj ENat.one_ne_top).1 h
  have hcE : Order.coheight E.point = 3 := by
    rw [← coheight_apply_eq E.map, E.map_point, hcT]
  have hZ₀ : (T : Set Y) = closure {E.map.base E.point} := by
    rw [E.map_point]
    exact (isGenericPoint_localSettingGenericPoint T).def.symm
  -- each proper curve `C` of `g⁻¹(η')` gives a valuation `w_C` of `ℂ(Y')`, restricted to `ℂ(Y)`
  choose W hW using exists_valuation_of_properCurve hEP hgs hgQ
    (LocalEtaleDatum.isTerminalVariety_of_isSmallMorphism hLS E g hgs hgp) hcE
  refine Set.encard_le_encard_of_injOn
    (f := fun C => ((W C).comap (functionFieldMap g)).comap (functionFieldMap E.map))
    (fun C _ => ?_) (fun C₁ _ C₂ _ heq => ?_)
  · obtain ⟨-, hwU, hwU2⟩ := hW C
    have h2 := isValuationLogDiscrepancy_comap_of_etale E.map hterm.1.1.isPair hEn hκ
      E.coe_curve hwU hwU2
    have hv0 := MMP.Intersection.isCentre_comap_functionFieldMap_of_etale sY E.map hYn hEn
      E.point hκ E.curve E.coe_curve T hZ₀ _ hwU
    exact ⟨hv0, h2, exists_isValuationLogDiscrepancy_lt_of_subset_supp hQ hΘ.1.1.nonneg hv0
      (fun y hy => DivisorWithCoeffs.mem_supp_iff.mpr ⟨D, hD.ne', hTD hy⟩) h2⟩
  · obtain ⟨⟨D₁, -, hv₁, hc₁⟩, e1, -⟩ := hW C₁
    obtain ⟨⟨D₂, -, hv₂, hc₂⟩, e2, -⟩ := hW C₂
    have hgw : (W C₁).comap (functionFieldMap g) = (W C₂).comap (functionFieldMap g) :=
      MMP.Intersection.injOn_comap_functionFieldMap_of_etale sY E.map hYn hEn E.point
        hκ E.curve E.coe_curve e1 e2 heq
    have hw : W C₁ = W C₂ := by
      ext t
      obtain ⟨s, rfl⟩ := hgb.functionFieldMap_bijective.2 t
      exact DFunLike.congr_fun hgw s
    have hc := MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hgs.isNormalVariety_source.1
      (hv₁.symm.trans (hw ▸ hv₂))
    have h12 := congrArg (fun Z : IrreducibleCloseds Y' => Z.isIrreducible.genericPoint)
      (hc₁.trans (hc.trans hc₂.symm))
    simp only [genericPoint_closurePoint] at h12
    exact ProperCurve.ext ((IsPreimmersion.isEmbedding (g.fiberι E.point)).injective h12)

end Proof_prop_oai4_local_valuations

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y}

/-- **Valuations from local cohomology.** Let `Y` be a normal projective `ℚ`-factorial complex
fourfold, `(Y, Θ)` an effective terminal pair, and `T ⊆ Sing Y` an irreducible curve contained in
a prime divisor `D` with positive coefficient in `Θ`. Then for every local-system open `T°` of
`T`, there are at least `b_T = curveLocalSystemRank sY T°` normalized divisorial valuations `v`
of `ℂ(Y)` with centre `T`, `a(v; Y, 0) = 2` and `a(v; Y, Θ) < 2`. -/
@[mmp "prop_oai4_local_valuations"]
public theorem IsKltTerminalPair.curveLocalSystemRank_le_encard
    (hQ : IsQFactorial sY) (hproj : MMP.Mori.IsProjectiveVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 4) (hΘ : IsKltTerminalPair sY Θ)
    (hT : topologicalKrullDim (T : Set Y) = 1) (hTsing : (T : Set Y) ⊆ singularLocus sY)
    (D : MMP.Mori.PrimeDivisor Y) (hD : 0 < Θ D) (hTD : (T : Set Y) ⊆ D.support)
    (To : (curveScheme T).Opens) (hTo : IsLocalSystemOpen sY To) :
    (curveLocalSystemRank sY To : ℕ∞) ≤
      {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
        MMP.Intersection.IsCentre ℂ sY v T ∧
        IsValuationLogDiscrepancy sY (0 : QDivisor Y) v 2 ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.encard :=
          by revert hQ hproj hdim hΘ hT hTsing D hD hTD To hTo; first | exact Proof_prop_oai4_local_valuations.solution | exact Proof_prop_oai4_local_valuations.solution _ | exact Proof_prop_oai4_local_valuations.solution _ _ | exact Proof_prop_oai4_local_valuations.solution _ _ _ | exact Proof_prop_oai4_local_valuations.solution _ _ _ _

end MMP.Fourfold

