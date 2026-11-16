module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeNegativeRay
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.KltFlipExistence
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.MMP.Threefold.StepDiagram.BadLociTerminalChain
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.AmpleModelBirational
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Intersection.ChowVarietyFixedDegree
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# One terminal step of the minimal model program over a projective base

Let `W` be a normal projective `ℚ`-factorial complex threefold with `(W, 0)` terminal, and
`μ : W ⟶ S` a birational morphism to a projective variety such that `K_W` is not nef over `S`.
Then there is a `K_W`-negative extremal ray `R` of `NE̅(W)` whose contraction `q : W ⟶ V` is
birational and factors `μ = h ∘ q`, and a normal projective `ℚ`-factorial threefold `W'` with
`(W', 0)` terminal and a birational morphism `μ' = h ∘ q' : W' ⟶ S`, where either

* `q` is divisorial: `Ex(q)` is a prime divisor `F` exceptional over `S`, `q' : W' ⟶ V` is an
  isomorphism, and the prime divisors of `W'` are the images of the prime divisors of `W` other
  than `F`; or
* `q` is small: `q' : W' ⟶ V` is the `K_W`-flip of `q`, and `W ⤏ W'` induces a bijection of
  prime divisors.

## Main results

* `MMP.Fourfold.IsTerminalVariety.exists_terminal_step`: the step.

## Implementation notes

The model `W'` of the divisorial case is `V` up to the isomorphism `q'`; in both cases the
correspondence of prime divisors is the strict transform `MMP.Fourfold.flipTransformPrimeDivisor`
along `q` and `q'`. That the curves of `R` are contracted by `μ` follows from `μ = h ∘ q` and
`MMP.Fourfold.IsContractionOfRay`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

namespace MMP.Fourfold

open CategoryTheory AlgebraicGeometry

universe u

variable {Xm Xp Z : Scheme.{u}} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- The strict transform `MMP.Fourfold.flipTransformPrimeDivisor fm fp` is a bijection from the
prime divisors of `X⁻` to the prime divisors of `X⁺`: it is defined on every prime divisor of `X⁻`,
it is injective, and every prime divisor of `X⁺` is the strict transform of one of `X⁻`. -/
def InducesPrimeDivisorBijection (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) : Prop :=
  (∀ S, (flipTransformPrimeDivisor fm fp S).isSome) ∧
    (∀ S T, flipTransformPrimeDivisor fm fp S = flipTransformPrimeDivisor fm fp T → S = T) ∧
    ∀ S' : MMP.Mori.PrimeDivisor Xp, ∃ S, flipTransformPrimeDivisor fm fp S = some S'

/-- The bijection of prime divisors `S ↦ S⁺` given by the strict transform
`MMP.Fourfold.flipTransformPrimeDivisor fm fp`, when it is one. -/
noncomputable def InducesPrimeDivisorBijection.equiv (h : InducesPrimeDivisorBijection fm fp) :
    MMP.Mori.PrimeDivisor Xm ≃ MMP.Mori.PrimeDivisor Xp :=
  Equiv.ofBijective (fun S => (flipTransformPrimeDivisor fm fp S).get (h.1 S))
    ⟨fun S T hST => h.2.1 S T <| calc
        flipTransformPrimeDivisor fm fp S
            = some ((flipTransformPrimeDivisor fm fp S).get (h.1 S)) := (Option.some_get _).symm
        _ = some ((flipTransformPrimeDivisor fm fp T).get (h.1 T)) := congrArg some hST
        _ = flipTransformPrimeDivisor fm fp T := Option.some_get _,
      fun S' => (h.2.2 S').imp fun S hS => Option.some_injective _ (by rw [Option.some_get, hS])⟩

/-- The bijection `InducesPrimeDivisorBijection.equiv` is the strict transform. -/
theorem InducesPrimeDivisorBijection.flipTransformPrimeDivisor_eq_some_equiv
    (h : InducesPrimeDivisorBijection fm fp) (S : MMP.Mori.PrimeDivisor Xm) :
    flipTransformPrimeDivisor fm fp S = some (h.equiv S) :=
  (Option.some_get _).symm

/-- A bijection of prime divisors through which the strict transform factors shows that the strict
transform is a bijection. -/
theorem inducesPrimeDivisorBijection_of_equiv
    (σ : MMP.Mori.PrimeDivisor Xm ≃ MMP.Mori.PrimeDivisor Xp)
    (hσ : ∀ S, flipTransformPrimeDivisor fm fp S = some (σ S)) :
    InducesPrimeDivisorBijection fm fp :=
  ⟨fun S => by simp [hσ], fun S T hST => σ.injective (Option.some_injective _ (by
      rw [← hσ, ← hσ, hST])), fun S' => ⟨σ.symm S', by simp [hσ]⟩⟩

end MMP.Fourfold

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_lem_mmp_indexb_terminal_step

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {W S : Scheme.{0}} [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
  {sW : W ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}

/-! ### Birational morphisms -/

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- A dominant morphism `f` locally of finite type is birational when `f ≫ g` is: the function
field of the source is generated by the pull-backs along `f ≫ g`, hence along `f`. -/
private theorem isBirationalMorphism_of_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [LocallyOfFiniteType f]
    (hfg : IsBirationalMorphism (f ≫ g)) : IsBirationalMorphism f := by
  haveI := hfg.isDominant
  haveI : IsDominant g := IsDominant.of_comp f g
  refine isBirationalMorphism_of_isBirational f
    (isBirational_of_surjective_functionFieldMap f fun t => ?_)
  obtain ⟨z, hz⟩ := hfg.functionFieldMap_bijective.2 t
  exact ⟨functionFieldMap g z, by
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, hz]⟩

/-- If `f ≫ g` and `f` are birational, so is `f' ≫ g` for every birational `f'` to the target of
`f` locally of finite type: on function fields, `g^*` is then bijective. -/
private theorem isBirationalMorphism_comp_of_comp {X X' Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral X'] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y) (f' : X' ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f' ≫ g)] (hfg : IsBirationalMorphism (f ≫ g))
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    IsBirationalMorphism (f' ≫ g) := by
  haveI := hfg.isDominant
  haveI := hf.isDominant
  haveI := hf'.isDominant
  haveI : IsDominant g := IsDominant.of_comp f g
  refine isBirationalMorphism_of_isBirational _
    (isBirational_of_surjective_functionFieldMap _ fun t => ?_)
  obtain ⟨y, rfl⟩ := hf'.functionFieldMap_bijective.2 t
  obtain ⟨z, hz⟩ := hfg.functionFieldMap_bijective.2 (functionFieldMap f y)
  refine ⟨z, ?_⟩
  rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply] at hz ⊢
  rw [hf.functionFieldMap_bijective.1 hz]

/-! ### Projectivity -/

/-- The structure sheaf of `Spec ℂ` is an ample invertible module. -/
private theorem exists_isAmple_spec :
    ∃ (M : (Spec (.of ℂ)).Modules) (hM : Stacks.Ample.IsInvertibleModule (Spec (.of ℂ)) M),
      letI : Stacks.Ample.IsInvertibleModule (Spec (.of ℂ)) M := hM
      Stacks.Ample.IsAmple (Spec (.of ℂ)) M :=
  ⟨Stacks.Ample.unitModule _, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩

/-- A projective variety over `ℂ` carries an ample invertible module. -/
private theorem exists_isAmple_of_isProjectiveVariety {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ exists_isAmple_spec).out 2 5
  exact (h.mp hZ.isProjective).2

/-- A proper morphism to a projective variety over `ℂ` along which a `ℚ`-divisor has a relatively
ample Cartier multiple is projective. -/
private theorem isProjectiveMorphism_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) {f : X ⟶ Y} [IsProper f] {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple f) : IsProjectiveMorphism f := by
  obtain ⟨-, -, L, hL, -, hamp⟩ := hD
  haveI := hL.isInvertibleModule_divisorialSheaf
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple f L.divisorialSheaf :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _ inferInstance
      hamp
  have h := (isProjective_tfae_seven_of_exists_isAmple f
    (exists_isAmple_of_isProjectiveVariety hY)).out 6 2
  exact h.mp ⟨inferInstance, _, inferInstance, hrel⟩

/-- A variety with a projective morphism to a projective variety over `ℂ` is projective. -/
private theorem isProjectiveVariety_of_isProjectiveMorphism {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsVariety ℂ sX)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) {f : X ⟶ Y} (hf : IsProjectiveMorphism f)
    (hfs : f ≫ sY = sX) : MMP.Mori.IsProjectiveVariety ℂ sX := by
  have hf' : IsProjective f := ((isProjective_tfae_seven_of_exists_isAmple f
    (exists_isAmple_of_isProjectiveVariety hY)).out 2 1).mp hf
  have hY' : IsProjective sY :=
    ((isProjective_tfae_seven_of_exists_isAmple sY exists_isAmple_spec).out 2 1).mp hY.isProjective
  have h := IsProjective.comp hf' hY'
  rw [hfs] at h
  exact { toIsVariety := hX
          isProjective :=
            ((isProjective_tfae_seven_of_exists_isAmple sX exists_isAmple_spec).out 1 2).mp h }

/-! ### The negative step -/

/-- The relative negative step: a `K_W`-negative extremal ray contracted by `μ`, with its
birational contraction `q : W ⟶ V` onto a projective variety, `ρ(W/V) = 1`, `-K_W` `q`-ample and
`μ = q ≫ h`. -/
private theorem exists_negativeExtremalRay_contraction
    (hW : IsTerminalVariety sW) (hWp : MMP.Mori.IsProjectiveVariety ℂ sW)
    {K : Divisor W} {m : ℕ} (hK : K.IsCanonicalDivisor sW m)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {μ : W ⟶ S}
    (hμ : μ ≫ sS = sW) (hμb : IsBirationalMorphism μ)
    (hnef : ¬ QDivisor.IsRelativelyNef sW μ (Divisor.toQDivisor K)) :
    ∃ (R : Set (NumericalCurveClasses sW)) (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ))
      (q : W ⟶ V) (h : V ⟶ S),
      IsNegativeExtremalRayOf sW (Divisor.toQDivisor K + 0) R ∧ IsContractionOfRay sW sV R q ∧
      MMP.Mori.IsProjectiveVariety ℂ sV ∧ MMP.Flips.relativePicardNumber sW q = 1 ∧
      (-(Divisor.toQDivisor K + 0)).HasRelativelyAmpleMultiple q ∧
      IsBirationalMorphism q ∧ q ≫ h = μ ∧ h ≫ sS = sV := by
  obtain ⟨R, hR, -, V, sV, q, hq, hVp, -, hρ, hamp, ⟨h, hqh, hhS⟩, -⟩ :=
    exists_isContractionOfRay_comp_eq_of_not_isRelativelyNef sW hWp (B := 0) hW.1 hK hS hμ
      (by rwa [add_zero])
  haveI : IsIntegral V := hq.isNormalVariety_target.1.toIsIntegral
  haveI : IsIntegral S := hS.toIsIntegral
  haveI : Surjective q := ⟨hq.surjective⟩
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hq.isProjectiveMorphism
  exact ⟨R, V, sV, q, h, hR, hq, hVp, hρ, hamp,
    isBirationalMorphism_of_comp q h (hqh ▸ hμb), hqh, hhS⟩

/-! ### Comparison of log discrepancies along a threefold step -/

section OffBadLocus

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- Pulling valuations back along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {g : R →+* S} (hg : Function.Surjective g)
    {v w : Valuation S (WithZero (Multiplicative ℤ))} (h : v.comap g = w.comap g) : v = w := by
  ext t
  obtain ⟨s, rfl⟩ := hg t
  exact congrArg (fun u : Valuation R (WithZero (Multiplicative ℤ)) => u s) h

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme is that of its closure,
through the identification of function fields. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{0}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- The valuation of a prime divisor of `X`, regarded as a divisor over `X`. -/
private theorem valuation_ofPrimeDivisor {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor k hX P).valuation = P.divisorialValuation := by
  ext t
  change P.divisorialValuation (functionFieldMap (𝟙 X) t) = _
  rw [functionFieldMap_id_apply]

/-- An open immersion of nonempty irreducible schemes is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {W Y : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace Y] [Nonempty W] (j : W ⟶ Y) [IsOpenImmersion j] :
    IsBirationalMorphism j := by
  let U : W.Opens := ⊤
  let V' : Y.Opens := (U.ι ≫ j).opensRange
  have hle : U ≤ j ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE j U V' ⟨w, trivial⟩
    ⟨_, ⟨⟨w, trivial⟩, rfl⟩⟩ hle ?_
  have e : j.resLE V' U hle = (U.ι ≫ j).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- `functionFieldMap` only depends on the morphism. -/
private theorem functionFieldMap_congr {A C : Scheme.{0}} [IsIntegral A] [IsIntegral C]
    {a b : A ⟶ C} (hab : a = b) [IsDominant a] [IsDominant b] (t : C.functionField) :
    functionFieldMap a t = functionFieldMap b t := by
  subst hab
  rfl

/-- **Crepant invariance**, with the structure morphism of the source given up to equality: if
`ΔY` is the crepant boundary of `(X, Δ)` along a birational `φ : Y ⟶ X`, divisors over `Y` and
over `X` with corresponding valuations have the same discrepancies. -/
private theorem isDiscrepancy_iff_of_crepant {X Y : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {n : ℕ} {KX : Divisor X} {Δ : QDivisor X}
    {KY : Divisor Y} {ΔY : QDivisor Y} (hP : MMP.Mori.IsPair sX Δ)
    (hKX : KX.IsCanonicalDivisor sX n) (φ : Y ⟶ X) [IsDominant φ] (hs : φ ≫ sX = sY)
    (hY : IsNormalVariety ℂ sY) (hφ : IsBirationalMorphism φ) (hKY : KY.IsCanonicalDivisor sY n)
    (hcb : ∀ (F : MMP.Mori.PrimeDivisor Y) (D : DivisorOver ℂ sX), D.valuation = F.valuationOver φ →
      IsDiscrepancy sX n KX Δ D (-ΔY.coeff F))
    (E : DivisorOver ℂ sY) (E' : DivisorOver ℂ sX)
    (hv : E'.valuation = E.valuation.comap (functionFieldMap φ)) (a : ℚ) :
    IsDiscrepancy sY n KY ΔY E a ↔ IsDiscrepancy sX n KX Δ E' a := by
  subst hs
  have hcb' : IsCrepantBoundary sX n KX Δ φ hY hφ ΔY := fun F => hcb F _ rfl
  exact (IsPair.isDiscrepancy_iff_of_crepant hP φ hY hφ hKX hKY (Or.inl hcb')).2 E E' hv a

/-- Off the bad locus the log discrepancies of corresponding divisors agree. -/
private theorem eq_of_not_subset_badLocusPlus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    (hc : ¬ (Dp.center : Set Xp) ⊆ badLocusPlus fm fp)
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am = ap := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hU : ((Dp.center : Set Xp) ∩ (fp ⁻¹ᵁ commonBiregularLocus fm fp : Set Xp)).Nonempty := by
    rw [Set.not_subset] at hc
    obtain ⟨x, hx, hxW⟩ := hc
    refine ⟨x, hx, ?_⟩
    rw [coe_badLocusPlus, coe_badLocusBase] at hxW
    simpa using hxW
  -- dimensions and canonical divisors
  obtain ⟨mp, hKp⟩ := h.isCanonicalDivisor_plus
  obtain ⟨mm, hKm⟩ := h.isCanonicalDivisor
  obtain rfl : mp = n := by
    exact_mod_cast hKp.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hap)
  obtain rfl : mm = n' := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ham)
  obtain rfl : mm = mp := by
    exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans
      (h.dim_minus.trans (h.dim_plus.symm.trans hKp.topologicalKrullDim_eq))
  have hPp : IsPairWith sXp mm (flipTransform fm fp K) (flipTransform fm fp B) :=
    ⟨h.isNormalVariety_plus, hKp, h.isQCartier_plus⟩
  obtain ⟨cp, hcp⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPp.isPair hKp Dp
  obtain ⟨cm, hcm⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm Dm
  rw [((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcp ap).mp hap).2,
    ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy hcm am).mp ham).2]
  suffices hcc : cm = cp by rw [hcc]
  -- restriction of `Dp` to `V⁺ = (f⁺)⁻¹(U)`
  obtain ⟨hY, hf, E', -, hval, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPp Dp _ hU
  have hcE := (hiff cp).mp hcp
  -- the identification `V⁺ ≅ V⁻ ⊆ X⁻` over `U`
  haveI : Nonempty (fp ⁻¹ᵁ commonBiregularLocus fm fp) := ⟨⟨hU.choose, hU.choose_spec.2⟩⟩
  haveI : IsIso (fm ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_left fm fp
  haveI : IsIso (fp ∣_ commonBiregularLocus fm fp) := isBiregular_commonBiregularLocus_right fm fp
  let φ : (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme ⟶ Xm :=
    (fp ∣_ commonBiregularLocus fm fp) ≫ inv (fm ∣_ commonBiregularLocus fm fp) ≫
      (fm ⁻¹ᵁ commonBiregularLocus fm fp).ι
  have hφ : φ ≫ fm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp := by
    simp only [φ, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  have hs : φ ≫ sXm = (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp := by
    rw [← h.comp_eq_minus, ← h.comp_eq_plus, ← Category.assoc, hφ, Category.assoc]
  haveI : IsOpenImmersion φ := by dsimp only [φ]; infer_instance
  have hφb : IsBirationalMorphism φ := isBirationalMorphism_of_isOpenImmersion φ
  haveI : IsDominant φ := hφb.isDominant
  haveI : IsDominant (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι :=
    Opens.isDominant_ι ((fp ⁻¹ᵁ commonBiregularLocus fm fp).isOpen.dense
      ⟨hU.choose, hU.choose_spec.2⟩)
  haveI : IsDominant (φ ≫ fm) := inferInstance
  haveI : IsDominant ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ fp) := inferInstance
  have hfm := h.isBirationalMorphism_minus.functionFieldMap_bijective.2
  -- valuations of prime divisors of `V⁺`, read on `k(X⁻)` and on `k(X⁺)`
  have hvF : ∀ F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme,
      (F.valuationOver φ).comap (functionFieldMap fm) =
        MMP.Mori.PrimeDivisor.valuationOver
          (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F) fp := by
    intro F
    ext t
    simp only [MMP.Mori.PrimeDivisor.valuationOver, Valuation.comap_apply]
    rw [divisorialValuation_primeDivisorMap, Valuation.comap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hvE : Dm.valuation = (DivisorOver.valuation (⟨_, Dp.f ∣_ _, hY, hf, E'⟩ :
      DivisorOver ℂ ((fp ⁻¹ᵁ commonBiregularLocus fm fp).ι ≫ sXp))).comap
        (functionFieldMap φ) := by
    apply comap_injective_of_surjective hfm
    rw [← hv, hval]
    ext t
    simp only [Valuation.comap_apply]
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      functionFieldMap_congr hφ]
  have hcb : ∀ (F : MMP.Mori.PrimeDivisor (fp ⁻¹ᵁ commonBiregularLocus fm fp).toScheme)
      (D : DivisorOver ℂ sXm), D.valuation = F.valuationOver φ →
      IsDiscrepancy sXm mm K B D
        (-((flipTransform fm fp B).restrictOpen (fp ⁻¹ᵁ commonBiregularLocus fm fp)).coeff F) := by
    intro F D hD
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    obtain ⟨Pm, -, hPm, -, -, -, hcoef, -⟩ := h.exists_primeDivisor_valuationOver_eq
      (OpenWeilRestriction.primeDivisorMap (fp ⁻¹ᵁ commonBiregularLocus fm fp).ι F)
    rw [hcoef]
    obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm
      (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm)
    obtain ⟨cD, hcD⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hKm D
    have hvD :
        D.valuation = (DivisorOver.ofPrimeDivisor ℂ h.isNormalVariety_minus Pm).valuation := by
      rw [valuation_ofPrimeDivisor, hD]
      apply comap_injective_of_surjective hfm
      rw [hvF, ← hPm]
      rfl
    have e := MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hvD
      (MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq h.isNormalVariety_minus hvD)
      hcD hc₀
    rw [← hc₀.eq_neg_coeff_of_ofPrimeDivisor h.isNormalVariety_minus, ← e]
    exact hcD
  have hcrep := isDiscrepancy_iff_of_crepant hB.isPair hKm φ hs hcE.1 hφb hcE.2.1 hcb
    ⟨_, Dp.f ∣_ _, hY, hf, E'⟩ Dm hvE cp
  exact hcm.eq (hcrep.mp hcE)

/-- **The comparison** `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)`. -/
private theorem le_of_isLogDiscrepancy (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B)
    (Dp : DivisorOver ℂ sXp) (Dm : DivisorOver ℂ sXm) (hDm : IsProper Dm.f)
    (hv : haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
      haveI := h.isBirationalMorphism_minus.isDominant
      haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm))
    {n n' : ℕ} {ap am : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap)
    (ham : MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am) :
    am ≤ ap := by
  by_cases hc : (Dp.center : Set Xp) ⊆ badLocusPlus fm fp
  · have ham' : IsValuationLogDiscrepancy sXm B Dm.valuation am := ⟨n', Dm, hDm, rfl, ham⟩
    have hap' : IsValuationLogDiscrepancy sXp (flipTransform fm fp B) Dp.valuation ap :=
      ⟨n, Dp, hap.2.1, rfl, hap⟩
    have hCm : MMP.Intersection.IsCentre ℂ sXm Dm.valuation Dm.center := ⟨Dm, hDm, rfl, rfl⟩
    have hCp : MMP.Intersection.IsCentre ℂ sXp Dp.valuation Dp.center :=
      ⟨Dp, hap.2.1, rfl, rfl⟩
    have hT := IsThreefoldStepDiagram.tfae_lt_and_centre_subset_badLocus h hv
      ham' hap' hCm hCp
    exact (show am < ap from (hT.out 3 1).mp hc).le
  · exact (eq_of_not_subset_badLocusPlus h hB Dp Dm hv hc hap ham).le

end OffBadLocus

section

/-- A valuation `ξ'` of `ℂ(X')` restricting on `ℂ(Z)` to the valuation of a divisor `D` over a
model `X ⟶ Z` is a divisor of the function field `ℂ(X')`: it is `ord_E` on the normal variety
`D.Y`, transported along `ℂ(X') ≅ ℂ(Z) ≅ ℂ(D.Y)`. -/
private theorem isDivisorOfFunctionField_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g')
    (D : DivisorOver ℂ (g ≫ sZ)) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    MMP.Flips.IsDivisorOfFunctionField ℂ (g' ≫ sZ) ξ' := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hY : IsNormalVariety ℂ ((D.f ≫ g) ≫ sZ) := by
    rw [Category.assoc]
    exact D.isNormalVariety
  have hbij : Function.Bijective (functionFieldMap (D.f ≫ g)) := by
    have : ⇑(functionFieldMap (D.f ≫ g)) = functionFieldMap D.f ∘ functionFieldMap g := by
      funext t
      exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g t).symm
    rw [this]
    exact D.isBirationalMorphism.functionFieldMap_bijective.comp hg.functionFieldMap_bijective
  refine ⟨D.Y, (D.f ≫ g) ≫ sZ, hY, D.E, ?_⟩
  letI := MMP.Mori.functionFieldAlgebra sZ
  letI := MMP.Mori.functionFieldAlgebra (g' ≫ sZ)
  letI := MMP.Mori.functionFieldAlgebra ((D.f ≫ g) ≫ sZ)
  let eP := MMP.Mori.functionFieldAlgEquiv sZ g' hg'.functionFieldMap_bijective
  let eY := MMP.Mori.functionFieldAlgEquiv sZ (D.f ≫ g) hbij
  refine ⟨eP.symm.trans eY, ?_⟩
  ext t
  obtain ⟨s, rfl⟩ := hg'.functionFieldMap_bijective.2 t
  have hs := congrArg (fun v => v s) h
  simp only [Valuation.comap_apply] at hs
  have h1 : eP.symm (functionFieldMap g' s) = s := eP.symm_apply_apply s
  change ξ' (functionFieldMap g' s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap g' s)))
  rw [h1, hs]
  change D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap g s)) = _
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply D.f g s]
  rfl

/-- **The centre on a proper model.** Let `g : X ⟶ Z` and `g' : X' ⟶ Z` be dominant morphisms of
integral schemes with `g'` proper, and `D` a divisor over `X`. A valuation `ξ'` of `k(X')`
restricting on `k(Z)` to `ord_D` dominates the local ring of some point of `X'`: the valuation
ring of `ξ'` dominates `𝒪_{Z, g(c_X(D))}`, and the valuative criterion for `g'` lifts
`Spec 𝒪_{ξ'} ⟶ Z` to `X'`. -/
private theorem exists_dominated_point_of_comap_eq {k : Type} [Field k]
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z] {sX : X ⟶ Spec (.of k)}
    (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g'] (hgp' : IsProper g')
    (D : DivisorOver k sX) (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ x : X', (∀ a : X'.presheaf.stalk x, ξ' (algebraMap _ X'.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X'.presheaf.stalk x),
        ξ' (algebraMap _ X'.functionField a) < 1 := by
  set y := D.f D.E.genericPoint
  set z := g y
  have hw : ∀ b : Z.presheaf.stalk z,
      ξ' (functionFieldMap g' (algebraMap _ Z.functionField b)) =
        D.valuation (algebraMap _ X.functionField ((g.stalkMap y).hom b)) := by
    intro b
    have := congrArg (fun v => v (algebraMap _ Z.functionField b)) h
    simp only [Valuation.comap_apply] at this
    rw [this, functionFieldMap_algebraMap_stalk g y b]
  let R := ξ'.valuationSubring
  let φ : Z.presheaf.stalk z →+* R :=
    ((functionFieldMap g').comp (algebraMap (Z.presheaf.stalk z) Z.functionField)).codRestrict R
      fun b => (ξ'.mem_valuationSubring_iff _).2 (by
        rw [RingHom.comp_apply, hw]
        exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D y rfl _)
  have hgen : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have hex : ValuativeCriterion.Existence g' := by
    have h : @IsProper _ _ g' := hgp'
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1.existence
  let S : ValuativeCommSq g' :=
    { R := R
      K := X'.functionField
      i₁ := X'.fromSpecStalk (genericPoint X')
      i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Z.fromSpecStalk z
      commSq := ⟨by
        rw [← functionFieldMap_fromSpecStalk g',
          ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
          ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
  have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X'.functionField)) ≫ l =
      X'.fromSpecStalk (genericPoint X') := hl₁
  set x := l (IsLocalRing.closedPoint R)
  have hx : genericPoint X' ⤳ x := (genericPoint_spec X').specializes trivial
  let f := Scheme.stalkClosedPointTo l
  have hf : f ≫ CommRingCat.ofHom (algebraMap R X'.functionField) =
      X'.presheaf.stalkSpecializes hx := by
    apply Spec.map_injective
    apply (cancel_mono (X'.fromSpecStalk x)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hfa : ∀ a : X'.presheaf.stalk x,
      algebraMap _ X'.functionField a = ((f.hom a : R) : X'.functionField) := fun a =>
    (congrArg (fun q => q.hom a) hf).symm
  refine ⟨x, fun a => ?_, fun a ha => ?_⟩
  · rw [hfa]
    exact (f.hom a).2
  · rw [hfa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit f.hom a hu))

/-- Over a proper birational model `X' ⟶ Z` of a normal variety, a valuation `ξ'` of `ℂ(X')`
restricting on `ℂ(Z)` to the valuation of a divisor over another model `X ⟶ Z` is realized by a
proper divisor over `X'`. -/
private theorem exists_properDivisorOver_valuation_eq_of_comap_eq
    {X X' Z : Scheme.{0}} [IsIntegral X] [IsIntegral X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX' : IsNormalVariety ℂ sX') (g : X ⟶ Z) (g' : X' ⟶ Z) [IsDominant g] [IsDominant g']
    (hg : IsBirationalMorphism g) (hg' : IsBirationalMorphism g') (hgp' : IsProper g')
    (hc : g ≫ sZ = sX) (hc' : g' ≫ sZ = sX') (D : DivisorOver ℂ sX)
    (ξ' : Valuation X'.functionField (WithZero (Multiplicative ℤ)))
    (h : ξ'.comap (functionFieldMap g') = D.valuation.comap (functionFieldMap g)) :
    ∃ D' : DivisorOver ℂ sX', IsProper D'.f ∧ D'.valuation = ξ' := by
  obtain ⟨x, h1, h2⟩ := exists_dominated_point_of_comap_eq g g' hgp' D ξ' h
  haveI : AlgebraicGeometry.IsVariety ℂ sX' := hX'.1
  have hξ : MMP.Flips.IsDivisorOfFunctionField ℂ sX' ξ' := by
    subst hc hc'
    exact isDivisorOfFunctionField_of_comap_eq g g' hg hg' D ξ' h
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates sX' hξ x h1 h2
  exact ⟨D'.toDivisorOver, D'.isProper, hv⟩

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- Every divisor `D⁺` over `X⁺` (with proper structure morphism) has a counterpart `D⁻` over
`X⁻`, proper, whose valuation agrees with that of `D⁺` on `k(Z)`. -/
private theorem exists_properDivisorOver_minus (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (D : DivisorOver ℂ sXp) :
    haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ D' : DivisorOver ℂ sXm, IsProper D'.f ∧
      D.valuation.comap (functionFieldMap fp) = D'.valuation.comap (functionFieldMap fm) := by
  haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  let e : Z.functionField ≃+* Xm.functionField :=
    RingEquiv.ofBijective (functionFieldMap fm)
      h.isBirationalMorphism_minus.functionFieldMap_bijective
  have hξ : ((D.valuation.comap (functionFieldMap fp)).comap e.symm.toRingHom).comap
      (functionFieldMap fm) = D.valuation.comap (functionFieldMap fp) := by
    ext t
    simp only [Valuation.comap_apply]
    congr 2
    exact e.symm_apply_apply t
  obtain ⟨D', hD'p, hD'v⟩ := exists_properDivisorOver_valuation_eq_of_comap_eq
    h.isNormalVariety_minus fp fm h.isSmallMorphism_plus.isBirationalMorphism
    h.isBirationalMorphism_minus (isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus)
    h.comp_eq_plus h.comp_eq_minus D _ hξ
  exact ⟨D', hD'p, by rw [hD'v, hξ]⟩

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_codimension {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ codimension D.center := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe]

/-- A normalized divisorial valuation realized by a proper divisor `D` over a variety is
exceptional iff the centre of `D` has codimension at least two. -/
private theorem isExceptionalValuation_valuation_iff {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX)
    (D : DivisorOver k sX) (hD : IsProper D.f) :
    MMP.Intersection.IsExceptionalValuation k sX D.valuation ↔ 2 ≤ codimension D.center := by
  refine ⟨fun ⟨D₁, _, h, hc⟩ => ?_, fun h => ⟨D, hD, rfl, h⟩⟩
  rwa [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX h]

/-- The log discrepancy of a proper divisor over a pair exists. -/
private theorem exists_isLogDiscrepancy (hB : MMP.Fourfold.IsPair sXm B) (Dm : DivisorOver ℂ sXm)
    (hDm : IsProper Dm.f) :
    ∃ (n : ℕ) (am : ℝ), MMP.Intersection.IsLogDiscrepancy sXm n (QDivisor.toRDivisor B) Dm am := by
  obtain ⟨-, n, K', hK', -⟩ := hB.isPair
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB.isPair hK' Dm
  exact ⟨n, _, MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDm⟩

/-- **Log discrepancies do not drop along a threefold step.** Every log discrepancy `a⁺` of a
divisor `D⁺` over `(X⁺, B⁺)` bounds from above a log discrepancy `a⁻ ≤ a⁺` of a divisor `D⁻` over
`(X⁻, B⁻)` with the same valuation of `k(Z)`. -/
private theorem exists_isLogDiscrepancy_minus_le (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hB : MMP.Fourfold.IsPair sXm B) {n : ℕ} {Dp : DivisorOver ℂ sXp} {ap : ℝ}
    (hap : MMP.Intersection.IsLogDiscrepancy sXp n
      (QDivisor.toRDivisor (flipTransform fm fp B)) Dp ap) :
    haveI : IsIntegral Z := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ (Dm : DivisorOver ℂ sXm) (n' : ℕ) (am : ℝ), IsProper Dm.f ∧
      Dp.valuation.comap (functionFieldMap fp) = Dm.valuation.comap (functionFieldMap fm) ∧
      MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) Dm am ∧ am ≤ ap := by
  obtain ⟨Dm, hDm, hv⟩ := exists_properDivisorOver_minus h Dp
  obtain ⟨n', am, ham⟩ := exists_isLogDiscrepancy hB Dm hDm
  exact ⟨Dm, n', am, hDm, hv, ham, le_of_isLogDiscrepancy h hB Dp Dm hDm hv hap ham⟩

/-- **Terminality is preserved by threefold steps with boundary `0`.** In a threefold step
diagram `X⁻ → Z ← X⁺` with `(X⁻, 0)` terminal, `(X⁺, 0)` is terminal: an exceptional divisor
over `X⁺` either is exceptional over `X⁻`, with log discrepancy `> 1` there, or is `ord_E` for a
prime divisor `E` of `X⁻` lost on `X⁺`, whose log discrepancy increases strictly from `1`. -/
private theorem isKltTerminalPair_flipTransform_zero
    (h : IsThreefoldStepDiagram sXm sZ sXp K 0 fm fp) (hterm : IsTerminalVariety sXm) :
    IsKltTerminalPair sXp (flipTransform fm fp (0 : QDivisor Xm)) := by
  have hXm := h.isNormalVariety_minus
  refine ⟨(h.isKltPair_and_isKltTerminalPair_flipTransform hterm.1).1,
    fun n Dp ap hex hap => ?_⟩
  obtain ⟨Dm, n', am, hDmp, hv, ham, hle⟩ := exists_isLogDiscrepancy_minus_le h hterm.1.1 hap
  by_cases hDm : Dm.IsExceptional
  · exact (hterm.2 n' Dm am hDm ham).trans_le hle
  obtain ⟨E, hE⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hXm Dm hDm
  obtain ⟨n₁, h₁⟩ := isLogDiscrepancy_ofPrimeDivisor hXm (B := 0) hterm.1.1.isPair E
  have ham1 : am = 1 := by
    simpa using MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ham h₁ hE
  have hval := valuation_ofPrimeDivisor hXm E
  have hexcv : MMP.Intersection.IsExceptionalValuation ℂ sXp Dp.valuation :=
    (isExceptionalValuation_valuation_iff h.isNormalVariety_plus.1 Dp hap.2.1).2
      ((isExceptional_iff_two_le_codimension h.isNormalVariety_plus Dp).1 hex)
  have hlt := h.lt_of_isExceptionalValuation E (by rw [hv, hE, hval]) hexcv
    ⟨n', Dm, hDmp, hE.trans hval, ham⟩ ⟨n, Dp, hap.2.1, rfl, hap⟩
  linarith

end

/-! ### Step diagrams of the negative step -/

/-- A `ℚ`-divisor with a relatively ample Cartier multiple is `ℚ`-Cartier. -/
private theorem isQCartier_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} {f : X ⟶ Y}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsQCartier := by
  obtain ⟨m, hm, L, hL, hLD, -⟩ := h
  exact ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩

/-- If `-D` is `ℚ`-Cartier then so is `D`. -/
private theorem isQCartier_of_neg {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} (h : (-D).IsQCartier) :
    D.IsQCartier := by
  obtain ⟨m, hm, hC⟩ := h
  exact ⟨-m, neg_ne_zero.mpr hm, by rwa [neg_smul, ← smul_neg]⟩

/-- Regarding a divisor as a `ℚ`-divisor commutes with pushing prime divisors forward. -/
private theorem toQDivisor_mapPrimeDivisors {X Y : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E n =>
    have h1 : ∀ {Z : Scheme.{0}} (F : MMP.Mori.PrimeDivisor Z) (m : ℤ),
        Divisor.toQDivisor (Finsupp.single F m) = Finsupp.single F (m : ℚ) := fun F m => by
      simp only [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom_apply,
        DivisorWithCoeffs.mapCoeffs, Finsupp.mapRange_single, Int.coe_castAddHom]
    rw [h1, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [h1]

/-- Regarding a divisor as a `ℚ`-divisor commutes with the strict transform. -/
private theorem toQDivisor_flipTransform {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    Divisor.toQDivisor (flipTransform f fp D) = flipTransform f fp (Divisor.toQDivisor D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, toQDivisor_mapPrimeDivisors]

/-- The negative step `q : W ⟶ V` of a projective threefold `W` with `-K_W` `q`-ample, followed
by a small projective `q' : W' ⟶ V` from a projective threefold with `K_{W'} = q'⁻¹_* q_* K_W`
canonical, `ℚ`-Cartier and `q'`-ample, is a threefold step diagram with boundary `0`. -/
private theorem isThreefoldStepDiagram_of {W V W' : Scheme.{0}} [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral W'] [CompactSpace W']
    [IsLocallyNoetherian W'] [IsNormal W'] {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    {sW' : W' ⟶ Spec (.of ℂ)} {K : Divisor W} {m : ℕ} (hK : K.IsCanonicalDivisor sW m)
    {R : Set (NumericalCurveClasses sW)} {q : W ⟶ V} {q' : W' ⟶ V}
    (hWp : MMP.Mori.IsProjectiveVariety ℂ sW) (hdim : topologicalKrullDim W = 3)
    (hq : IsContractionOfRay sW sV R q) (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hqb : IsBirationalMorphism q)
    (hamp : (-(Divisor.toQDivisor K + 0)).HasRelativelyAmpleMultiple q)
    (hW'p : MMP.Mori.IsProjectiveVariety ℂ sW') (hdim' : topologicalKrullDim W' = 3)
    (hq'p : IsProjectiveMorphism q') (hq's : IsSmallMorphism sW' sV q')
    (hK' : ∃ m' : ℕ, Divisor.IsCanonicalDivisor sW' m' (flipTransform q q' K))
    (hQ' : (Divisor.toQDivisor (flipTransform q q' K) +
      flipTransform q q' (0 : QDivisor W)).IsQCartier)
    (hamp' : (Divisor.toQDivisor (flipTransform q q' K) +
      flipTransform q q' (0 : QDivisor W)).HasRelativelyAmpleMultiple q') :
    IsThreefoldStepDiagram sW sV sW' K 0 q q' := by
  haveI := hq's.isProper
  exact
  { isProjectiveVariety_minus := hWp
    isNormalVariety_minus := hq.isNormalVariety_source
    dim_minus := hdim
    isProjectiveVariety_plus := hW'p
    isNormalVariety_plus := hq's.isNormalVariety_source
    dim_plus := hdim'
    isProjectiveVariety_target := hVp
    isNormalVariety_target := hq.isNormalVariety_target
    comp_eq_minus := hq.comp_eq
    comp_eq_plus := hq's.comp_eq
    isProjectiveMorphism_minus := hq.isProjectiveMorphism
    isProjectiveMorphism_plus := hq'p
    isBirationalMorphism_minus := hqb
    isIso_app_minus := hq.isIso_app
    isIso_app_plus := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
      sW' sV hq's.isNormalVariety_source.1 hq.isNormalVariety_target q'
      hq's.isBirationalMorphism).1
    isSmallMorphism_plus := hq's
    isCanonicalDivisor := ⟨m, hK⟩
    isCanonicalDivisor_plus := hK'
    nonneg := fun P => by simp
    isQCartier_minus :=
      isQCartier_of_neg (isQCartier_of_hasRelativelyAmpleMultiple hamp)
    isQCartier_plus := hQ'
    hasRelativelyAmpleMultiple_minus := hamp
    hasRelativelyAmpleMultiple_plus := hamp' }

/-- A terminal variety `(W, 0)` is dlt: it is klt, so `Z = W` witnesses the dlt condition. -/
private theorem isDltPair_zero (hW : IsTerminalVariety sW) {K : Divisor W} {m : ℕ}
    (hK : K.IsCanonicalDivisor sW m) : MMP.Intersection.IsDltPair sW 0 :=
  (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sW hK 0).mpr
    (MMP.Threefold.Mori.IsKltPair.isDltPair
      ((isKltPair_iff_mori_isKltPair sW hK hW.1.1).mp hW.1) fun _ => le_refl _).1

/-! ### The divisorial case -/

/-- The points near which `f` is not an open immersion lie over the complement of the biregular
locus. -/
private theorem exceptionalSet_subset {X Y : Scheme.{0}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- **The two exceptional sets of a proper birational morphism onto a normal variety agree.** A
point `y` near which `f` is an open immersion is alone in its fibre: the fibre is connected, `y`
is open in it, and `y` is closed in it since a nontrivial specialization `y ⤳ z` inside the fibre
would raise the coheight above `coheight (f y) = coheight y`. -/
private theorem coe_exceptionalSet_eq {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (hY : MMP.Mori.IsVariety ℂ sY)
    (f : Y ⟶ X) [IsProper f] (hf : f ≫ sX = sY) (hb : IsBirationalMorphism f) :
    (MMP.Mori.exceptionalSet f : Set Y) = MMP.Flips.exceptionalSet f := by
  haveI := hX.1.toIsIntegral
  haveI := hY.toIsIntegral
  haveI := hX.2
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsVariety ℂ sY := hY
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine Set.Subset.antisymm (fun y hy => ?_) (exceptionalSet_subset f)
  by_contra hyF
  obtain ⟨U, hyU, hU⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hyF
  have hdim : topologicalKrullDim Y = topologicalKrullDim X :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sY hb).symm
  have hinj : ∀ z ∈ (U : Set Y), f z = f y → z = y := by
    intro z hz hzy
    have := (U.ι ≫ f).isOpenEmbedding.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨y, hyU⟩) hzy
    exact congrArg Subtype.val this
  have hcl : ∀ z, f z = f y → y ⤳ z → z = y := by
    intro z hzy hyz
    by_contra hne
    have h1 := MMP.Flips.coheight_le_coheight_map sX sY hX.1 hY f hf hdim z
    rw [hzy, MMP.Flips.coheight_map_of_notMem_exceptionalSet hyF] at h1
    exact (coheight_lt_coheight_of_specializes Y hyz (Ne.symm hne)).not_ge h1
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sY sX
    hY hX f hb).2 (f y)
  have hyf : y ∈ f ⁻¹' {f y} := rfl
  have hcov : f ⁻¹' {f y} ⊆ (U : Set Y) ∪ (closure {y})ᶜ := by
    intro z hz
    by_cases hzc : z ∈ closure {y}
    · left
      rw [hcl z hz (specializes_iff_mem_closure.mpr hzc)]
      exact hyU
    · exact Or.inr hzc
  have hdisj : f ⁻¹' {f y} ∩ ((U : Set Y) ∩ (closure {y})ᶜ) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, Set.mem_compl_iff,
      not_and, not_not]
    intro hz hzU
    rw [hinj z hzU hz]
    exact subset_closure (Set.mem_singleton y)
  have hsub : f ⁻¹' {f y} ⊆ (U : Set Y) := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hconn.isPreconnected U (closure {y})ᶜ
      U.isOpen isClosed_closure.isOpen_compl hcov hdisj with h | h
    · exact h
    · exact absurd (subset_closure (Set.mem_singleton y)) (h hyf)
  have hfin : (f ⁻¹' {f y}).Finite :=
    (Set.finite_singleton y).subset fun z hz => hinj z (hsub hz) hz
  exact MMP.Mori.mem_exceptionalSet.mp hy (mem_biregularLocus_of_finite f hb hfin)

/-- The inverse transform of a prime divisor along the identity is itself. -/
private theorem inverseTransformPrimeDivisor_id {Y : Scheme.{0}} (Q : MMP.Mori.PrimeDivisor Y) :
    inverseTransformPrimeDivisor (𝟙 Y) Q = some Q := by
  have h := inverseTransformDivisor_id (R := ℤ) (Finsupp.single Q 1)
  rw [inverseTransformDivisor_single] at h
  cases hQ : inverseTransformPrimeDivisor (𝟙 Y) Q with
  | none =>
    simp only [hQ, Option.elim] at h
    exact absurd h.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
  | some E =>
    simp only [hQ, Option.elim] at h
    exact congrArg some (Finsupp.single_left_injective one_ne_zero h)

/-- The strict transform `𝟙⁻¹_* f_*` along `f` and the identity is the push-forward `f_*`. -/
private theorem flipTransform_id {R : Type*} [AddCommMonoid R] {X Y : Scheme.{0}} (f : X ⟶ Y)
    (D : DivisorWithCoeffs R X) :
    flipTransform f (𝟙 Y) D = RationalMap.transformDivisor (X := X) f.toRationalMap D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor_id]

/-- The identity of a normal variety is small. -/
private theorem isSmallMorphism_id {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) : IsSmallMorphism sX sX (𝟙 X) where
  isNormalVariety_source := hX
  isNormalVariety_target := hX
  comp_eq := Category.id_comp sX
  isProper := inferInstance
  isBirationalMorphism := isBirationalMorphism_of_isIso _
  two_le_codimension := by
    have h : MMP.Mori.IsBiregular (𝟙 X) ⊤ := (MMP.Mori.isBiregular_top_iff _).mpr inferInstance
    have hle := MMP.Mori.le_biregularLocus h
    rw [le_closedsCodimension_iff]
    intro W hW
    obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
    exact absurd (hle (Set.mem_univ x)) (MMP.Mori.mem_exceptionalSet.mp (hW hx))

/-- The identity is projective. -/
private theorem isProjectiveMorphism_id (X : Scheme.{0}) : IsProjectiveMorphism (𝟙 X) :=
  MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 X)

/-- Every Cartier divisor is ample relative to an isomorphism. -/
private theorem isRelativelyAmple_of_isIso {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {L : Divisor X}
    (hL : L.IsCartier) : L.IsRelativelyAmple e hL := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨V, hV, hyV, ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  haveI : CompactSpace (e ⁻¹ᵁ V) := inferInstance
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- A `ℚ`-Cartier `ℚ`-divisor is ample relative to an isomorphism. -/
private theorem hasRelativelyAmpleMultiple_of_isIso {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {D : QDivisor X}
    (hD : D.IsQCartier) : D.HasRelativelyAmpleMultiple e := by
  obtain ⟨m, hm, L, hLD, hL⟩ := hD
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · refine ⟨(-m).toNat, by omega, -L, hL.neg, ?_, isRelativelyAmple_of_isIso e hL.neg⟩
    rw [map_neg, hLD, Int.toNat_of_nonneg (by omega), neg_smul]
  · refine ⟨m.toNat, by omega, L, hL, ?_, isRelativelyAmple_of_isIso e hL⟩
    rw [hLD, Int.toNat_of_nonneg hpos.le]

/-- The divisorial case: `Ex(q)` is a prime divisor and `W' = V`. -/
private theorem exists_model_of_not_isSmallMorphism
    (hW : IsTerminalVariety sW) (hQ : IsQFactorial sW)
    (hWp : MMP.Mori.IsProjectiveVariety ℂ sW) (hdim : topologicalKrullDim W = 3)
    {K : Divisor W} {m : ℕ} (hK : K.IsCanonicalDivisor sW m)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {μ : W ⟶ S}
    (hμ : μ ≫ sS = sW) (hμb : IsBirationalMorphism μ)
    {R : Set (NumericalCurveClasses sW)} {V : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {q : W ⟶ V} {h : V ⟶ S}
    (hR : IsNegativeExtremalRayOf sW (Divisor.toQDivisor K + 0) R)
    (hq : IsContractionOfRay sW sV R q) (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hρ : MMP.Flips.relativePicardNumber sW q = 1)
    (hamp : (-(Divisor.toQDivisor K + 0)).HasRelativelyAmpleMultiple q)
    (hqb : IsBirationalMorphism q) (hqh : q ≫ h = μ) (hhS : h ≫ sS = sV)
    (hsmall : ¬ IsSmallMorphism sW sV q) :
    ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (_ : CompactSpace W')
        (_ : IsLocallyNoetherian W') (_ : IsNormal W') (sW' : W' ⟶ Spec (.of ℂ)) (q' : W' ⟶ V),
        IsQFactorial sW' ∧ MMP.Mori.IsProjectiveVariety ℂ sW' ∧ topologicalKrullDim W' = 3 ∧
        IsTerminalVariety sW' ∧ q' ≫ h ≫ sS = sW' ∧ IsBirationalMorphism (q' ≫ h) ∧
        (∃ F : MMP.Mori.PrimeDivisor W, (exceptionalSet q : Set W) = F.support ∧ IsIso q' ∧
            MMP.Flips.IsExceptionalPrimeDivisor sS μ F ∧
            (∀ P, P ≠ F → (flipTransformPrimeDivisor q q' P).isSome) ∧
            ∀ P' : MMP.Mori.PrimeDivisor W', ∃ P, P ≠ F ∧
              flipTransformPrimeDivisor q q' P = some P') := by
  have hVn := hq.isNormalVariety_target
  haveI : IsIntegral V := hVn.1.toIsIntegral
  haveI : IsNormal V := hVn.2
  haveI : LocallyOfFiniteType sV := hVn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : QuasiCompact sV := hVn.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : MMP.Mori.IsVariety ℂ sV := hVn.1
  have hWn := hq.isNormalVariety_source
  haveI : MMP.Mori.IsVariety ℂ sW := hWn.1
  haveI : IsIntegral S := hS.toIsIntegral
  haveI : MMP.Mori.IsVariety ℂ sS := hS.toIsVariety
  haveI : IsProper q := isProper_of_isProjectiveMorphism q hq.isProjectiveMorphism
  haveI : IsDominant q := hqb.isDominant
  have hdimV : topologicalKrullDim V = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sW hqb).trans hdim
  -- `V` is `ℚ`-factorial and `(V, 0)` is dlt
  have hstep : IsProjectiveElementaryDltStep sW sV sV K 0 R q (𝟙 V)
      (flipTransform q (𝟙 V) 0) :=
    { isProjectiveQFactorialDltPair := ⟨hWp, hQ, ⟨m, hK⟩, isDltPair_zero hW hK⟩
      isNegativeExtremalRayOf := hR
      isContractionOfRay := hq
      isBirationalMorphism := hqb
      comp_eq := Category.id_comp sV
      eq_flipTransform := rfl
      flip_or_divisorial := Or.inr ⟨hsmall, inferInstance⟩ }
  obtain ⟨hQV, hdltV⟩ := hstep.isQFactorial_and_isDltPair
  -- `K_V = q_* K` is a canonical divisor
  obtain ⟨-, n₀, K₀, hK₀, -⟩ := hdltV.1.1
  obtain rfl : m = n₀ := by
    have := hK.topologicalKrullDim_eq.symm.trans
      (hdim.trans (hdimV.symm.trans hK₀.topologicalKrullDim_eq))
    exact_mod_cast this
  have hKV : Divisor.IsCanonicalDivisor sV m (flipTransform q (𝟙 V) K) := by
    rw [flipTransform_id]
    haveI : LocallyOfFiniteType (q ≫ sV) := by
      rw [hq.comp_eq]
      exact hWn.1.toLocallyOfFiniteType
    exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hVn
      (by rw [hq.comp_eq]; exact hWn) hqb hK₀ (by rw [hq.comp_eq]; exact hK)
  have hQ' : (Divisor.toQDivisor (flipTransform q (𝟙 V) K) +
      flipTransform q (𝟙 V) (0 : QDivisor W)).IsQCartier := isQCartier_of_isQFactorial sV hQV _
  have hD : IsThreefoldStepDiagram sW sV sV K 0 q (𝟙 V) :=
    isThreefoldStepDiagram_of hK hWp hdim hq hVp hqb hamp hVp hdimV (isProjectiveMorphism_id V)
      (isSmallMorphism_id hVn) ⟨m, hKV⟩ hQ' (hasRelativelyAmpleMultiple_of_isIso (𝟙 V) hQ')
  -- `(V, 0)` is terminal
  have hterm := isKltTerminalPair_flipTransform_zero hD hW
  rw [map_zero] at hterm
  -- `Ex(q)` is a prime divisor `F`
  have hBC : MMP.Flips.IsBirationalContraction ℂ sV sW q :=
    { isVariety_target := hVn.1
      isVariety_source := hWn.1
      comp_eq := hq.comp_eq
      isProper := inferInstance
      isIso_app := hq.isIso_app
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sW hqb).symm }
  have hEx := coe_exceptionalSet_eq hVn hWn.1 q hq.comp_eq hqb
  have hns : ¬ MMP.Flips.IsSmall ℂ sV sW q := by
    intro hs
    apply hsmall
    refine ⟨hWn, hVn, hq.comp_eq, inferInstance, hqb, ?_⟩
    have h2 := (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hBC).mp hs
    have he : MMP.Mori.exceptionalSet q = MMP.Flips.exceptionalCloseds q := Closeds.ext hEx
    rwa [he]
  obtain ⟨F, hF⟩ := MMP.Flips.exists_primeDivisor_exceptionalSet_eq_support_of_not_isSmall sW sV
    hQ hVn q hBC hq.isProjectiveMorphism hρ hns
  -- points of `Ex(q)` map to points of coheight at least two
  obtain ⟨V', hV', hV'b⟩ :=
    (MMP.Flips.isIso_app_and_exists_isBiregular_of_isBirationalMorphism hVn q
      (by rw [hq.comp_eq]; exact hWn.1) hqb).2
  have hFcoh : 2 ≤ Order.coheight (q F.genericPoint) := by
    have hmem : F.genericPoint ∈ (MMP.Mori.exceptionalSet q : Set W) := by
      rw [hEx, hF, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    refine MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV' _ fun hw => ?_
    exact MMP.Mori.mem_exceptionalSet.mp hmem (MMP.Mori.le_biregularLocus hV'b hw)
  have hdimS : topologicalKrullDim V = topologicalKrullDim S :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sW hqb).trans
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS sW hμb).symm
  have hexcF : MMP.Flips.IsExceptionalPrimeDivisor sS μ F := by
    haveI : IsProper μ := by
      rw [← hqh]
      haveI : IsSeparated sS := hS.toIsSeparated
      haveI : IsProper (h ≫ sS) := by
        rw [hhS]
        exact isProper_of_isProjectiveMorphism sV hVp.isProjective
      haveI : IsProper h := IsProper.of_comp h sS
      infer_instance
    refine ⟨by rw [hμ]; exact hWn, hμb, inferInstance, ?_⟩
    have h2 : 2 ≤ Order.coheight (μ F.genericPoint) := by
      rw [← hqh, Scheme.Hom.comp_apply]
      exact hFcoh.trans (MMP.Flips.coheight_le_coheight_map sS sV hS.toIsVariety hVn.1 h hhS
        hdimS _)
    unfold MMP.Flips.ProperDivisorOver.IsExceptional
    rw [MMP.Flips.ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint,
      ← MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS (μ F.genericPoint)]
    gcongr
    exact (WithBot.coe_le_coe.mpr h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ _)
  -- prime divisors
  have hsep : IsSeparated (V ↘ Limits.terminal Scheme) := by
    haveI : IsSeparated sV := hVn.1.toIsSeparated
    rw [show (V ↘ Limits.terminal Scheme) = sV ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have htr : ∀ (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor V),
      q P.genericPoint = Q.genericPoint → flipTransformPrimeDivisor q (𝟙 V) P = some Q := by
    intro P Q hPQ
    unfold flipTransformPrimeDivisor
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff q P Q).mpr hPQ]
    exact inverseTransformPrimeDivisor_id Q
  haveI : LocallyOfFiniteType (𝟙 V ≫ h) := by
    haveI : LocallyOfFiniteType (h ≫ sS) := by rw [hhS]; infer_instance
    rw [Category.id_comp]
    exact locallyOfFiniteType_of_comp h sS
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, sV, 𝟙 V, hQV, hVp, hdimV,
    hterm, by rw [Category.id_comp, hhS],
    isBirationalMorphism_comp_of_comp q (𝟙 V) h (hqh ▸ hμb) hqb (isBirationalMorphism_of_isIso _),
    F, hEx.trans hF, inferInstance, hexcF, fun P hP => ?_, fun P' => ?_⟩
  · have hPF : P.genericPoint ∉ MMP.Flips.exceptionalSet q := by
      rw [hF]
      intro hmem
      apply hP
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure F] at hmem
      exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (MMP.ProgramBaseChange.eq_of_specializes_of_coheight_eq_one
          (specializes_iff_mem_closure.mpr hmem) F.coheight_genericPoint
          P.coheight_genericPoint).symm
    have hc : Order.coheight (q P.genericPoint) = 1 := by
      rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hPF]
      exact P.coheight_genericPoint
    rw [htr P (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc)
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hc).symm]
    rfl
  · obtain ⟨y, hy⟩ := hq.surjective P'.genericPoint
    have hyb : q y ∈ biregularLocus q := by
      rw [hy]
      refine MMP.Mori.le_biregularLocus hV'b ?_
      by_contra hw
      have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV' _ hw
      rw [P'.coheight_genericPoint] at this
      exact absurd this (by norm_num)
    have hyF : y ∉ MMP.Flips.exceptionalSet q := fun h' =>
      MMP.Mori.mem_exceptionalSet.mp (exceptionalSet_subset q h') hyb
    have hc : Order.coheight y = 1 := by
      rw [← MMP.Flips.coheight_map_of_notMem_exceptionalSet hyF, hy]
      exact P'.coheight_genericPoint
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne y hc, fun hPF => hyF ?_, htr _ _ ?_⟩
    · rw [hF, ← hPF, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact subset_closure rfl
    · exact (congrArg q (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne y hc)).trans hy

/-! ### The small case -/

/-- The small case: `W'` is the flip of `q`. -/
private theorem exists_model_of_isSmallMorphism
    (hW : IsTerminalVariety sW) (hQ : IsQFactorial sW)
    (hWp : MMP.Mori.IsProjectiveVariety ℂ sW) (hdim : topologicalKrullDim W = 3)
    {K : Divisor W} {m : ℕ} (hK : K.IsCanonicalDivisor sW m)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {μ : W ⟶ S}
    (hμ : μ ≫ sS = sW) (hμb : IsBirationalMorphism μ)
    {R : Set (NumericalCurveClasses sW)} {V : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)}
    {q : W ⟶ V} {h : V ⟶ S}
    (hR : IsNegativeExtremalRayOf sW (Divisor.toQDivisor K + 0) R)
    (hq : IsContractionOfRay sW sV R q) (hVp : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hamp : (-(Divisor.toQDivisor K + 0)).HasRelativelyAmpleMultiple q)
    (hqb : IsBirationalMorphism q) (hqh : q ≫ h = μ) (hhS : h ≫ sS = sV)
    (hsmall : IsSmallMorphism sW sV q) :
    ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (_ : CompactSpace W')
        (_ : IsLocallyNoetherian W') (_ : IsNormal W') (sW' : W' ⟶ Spec (.of ℂ)) (q' : W' ⟶ V),
        IsQFactorial sW' ∧ MMP.Mori.IsProjectiveVariety ℂ sW' ∧ topologicalKrullDim W' = 3 ∧
        IsTerminalVariety sW' ∧ q' ≫ h ≫ sS = sW' ∧ IsBirationalMorphism (q' ≫ h) ∧
        (IsFlipOf sW sV sW' (Divisor.toQDivisor K) q q' ∧
            InducesPrimeDivisorBijection q q') := by
  have hVn := hq.isNormalVariety_target
  haveI : IsIntegral V := hVn.1.toIsIntegral
  haveI : IsNormal V := hVn.2
  haveI : LocallyOfFiniteType sV := hVn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : MMP.Mori.IsVariety ℂ sV := hVn.1
  haveI : MMP.Mori.IsVariety ℂ sW := hq.isNormalVariety_source.1
  haveI : IsIntegral S := hS.toIsIntegral
  have hFC : IsFlippingContraction sW sV K 0 q :=
    { isNormalVariety_source := hq.isNormalVariety_source
      isNormalVariety_target := hVn
      comp_eq := hq.comp_eq
      isCanonicalDivisor := ⟨m, hK⟩
      isQCartier := isQCartier_of_neg (isQCartier_of_hasRelativelyAmpleMultiple hamp)
      isProper := hsmall.isProper
      isBirationalMorphism := hqb
      two_le_codimension := hsmall.two_le_codimension
      hasRelativelyAmpleMultiple := hamp }
  obtain ⟨W', i2, i3, i4, sW', q', hflip⟩ :=
    exists_isFlip_of_isKltPair sW K 0 hWp hdim hQ ⟨m, hK⟩ hW.1 sV R q hR hq hFC
  have hW'n : IsNormalVariety ℂ sW' := hflip.isNormalVariety
  haveI : IsIntegral W' := hW'n.1.toIsIntegral
  haveI : MMP.Mori.IsVariety ℂ sW' := hW'n.1
  haveI := hflip.isProper
  have hq's : IsSmallMorphism sW' sV q' :=
    ⟨hW'n, hVn, hflip.comp_eq, hflip.isProper, hflip.isBirationalMorphism,
      hflip.two_le_codimension⟩
  have hq'p : IsProjectiveMorphism q' :=
    isProjectiveMorphism_of_hasRelativelyAmpleMultiple hVp hflip.hasRelativelyAmpleMultiple
  have hW'p : MMP.Mori.IsProjectiveVariety ℂ sW' :=
    isProjectiveVariety_of_isProjectiveMorphism hW'n.1 hVp hq'p hflip.comp_eq
  have hdim' : topologicalKrullDim W' = 3 :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sW'
      hflip.isBirationalMorphism).symm.trans
      ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sW hqb).trans hdim)
  have heq : flipTransform q q' (Divisor.toQDivisor K + 0) =
      Divisor.toQDivisor (flipTransform q q' K) + flipTransform q q' (0 : QDivisor W) := by
    rw [map_add, toQDivisor_flipTransform]
  have hflipOf : IsFlipOf sW sV sW' (Divisor.toQDivisor K + 0) q q' :=
    { isQCartier := hFC.isQCartier
      isContraction := hq.toIsContraction
      isSmallMorphism := hsmall
      hasRelativelyAmpleMultiple := hamp
      isSmallMorphism_flip := hq's
      isProjectiveMorphism_flip := hq'p
      isQCartier_flip := heq ▸ hflip.isQCartier
      hasRelativelyAmpleMultiple_flip := heq ▸ hflip.hasRelativelyAmpleMultiple }
  have hdlt : MMP.Intersection.IsDltPair sW 0 := isDltPair_zero hW hK
  have hstep : IsProjectiveElementaryDltStep sW sV sW' K 0 R q q' (flipTransform q q' 0) :=
    { isProjectiveQFactorialDltPair := ⟨hWp, hQ, ⟨m, hK⟩, hdlt⟩
      isNegativeExtremalRayOf := hR
      isContractionOfRay := hq
      isBirationalMorphism := hqb
      comp_eq := hflip.comp_eq
      eq_flipTransform := rfl
      flip_or_divisorial := Or.inl ⟨hsmall, hflipOf⟩ }
  have hD : IsThreefoldStepDiagram sW sV sW' K 0 q q' :=
    isThreefoldStepDiagram_of hK hWp hdim hq hVp hqb hamp hW'p hdim' hq'p hq's
      ⟨m, hflip.isCanonicalDivisor_flipTransform hK⟩ hflip.isQCartier
      hflip.hasRelativelyAmpleMultiple
  have hterm := (hD.isKltPair_and_isKltTerminalPair_flipTransform hW.1).2 hsmall hW
  rw [map_zero] at hterm
  obtain ⟨-, e, he⟩ := hD.isExceptionalValuation_iff_of_isSmallMorphism hsmall
  haveI : LocallyOfFiniteType (q' ≫ h) := by
    haveI : LocallyOfFiniteType ((q' ≫ h) ≫ sS) := by
      rw [Category.assoc, hhS, hflip.comp_eq]
      exact hW'n.1.toLocallyOfFiniteType
    exact locallyOfFiniteType_of_comp _ sS
  refine ⟨W', inferInstance, i2, i3, i4, sW', q', hstep.isQFactorial_and_isDltPair.1, hW'p,
    hdim', hterm, by rw [hhS, hflip.comp_eq],
    isBirationalMorphism_comp_of_comp q q' h (hqh ▸ hμb) hqb hflip.isBirationalMorphism,
    by simpa only [add_zero] using hflipOf,
    inducesPrimeDivisorBijection_of_equiv e fun P => (he P).1⟩

private theorem solution : ∀ {W S : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    (hW : IsTerminalVariety sW) (hQ : IsQFactorial sW)
    (hWp : MMP.Mori.IsProjectiveVariety ℂ sW) (hdim : topologicalKrullDim W = 3)
    {K : Divisor W} {m : ℕ} (hK : K.IsCanonicalDivisor sW m)
    {sS : S ⟶ Spec (.of ℂ)} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {μ : W ⟶ S}
    (hμ : μ ≫ sS = sW) (hμb : IsBirationalMorphism μ)
    (hnef : ¬ QDivisor.IsRelativelyNef sW μ (Divisor.toQDivisor K)),
    ∃ (R : Set (NumericalCurveClasses sW)) (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ))
      (q : W ⟶ V) (h : V ⟶ S),
      IsNegativeExtremalRayOf sW (Divisor.toQDivisor K) R ∧ IsContractionOfRay sW sV R q ∧
      IsBirationalMorphism q ∧ q ≫ h = μ ∧
      ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (_ : CompactSpace W')
        (_ : IsLocallyNoetherian W') (_ : IsNormal W') (sW' : W' ⟶ Spec (.of ℂ)) (q' : W' ⟶ V),
        IsQFactorial sW' ∧ MMP.Mori.IsProjectiveVariety ℂ sW' ∧ topologicalKrullDim W' = 3 ∧
        IsTerminalVariety sW' ∧ q' ≫ h ≫ sS = sW' ∧ IsBirationalMorphism (q' ≫ h) ∧
        ((∃ F : MMP.Mori.PrimeDivisor W, (exceptionalSet q : Set W) = F.support ∧ IsIso q' ∧
            MMP.Flips.IsExceptionalPrimeDivisor sS μ F ∧
            (∀ P, P ≠ F → (flipTransformPrimeDivisor q q' P).isSome) ∧
            ∀ P' : MMP.Mori.PrimeDivisor W', ∃ P, P ≠ F ∧ flipTransformPrimeDivisor q q' P = some P') ∨
          (IsFlipOf sW sV sW' (Divisor.toQDivisor K) q q' ∧
            InducesPrimeDivisorBijection q q')) := by
  intro W S _ _ _ _ sW hW hQ hWp hdim K m hK sS hS μ hμ hμb hnef
  obtain ⟨R, V, sV, q, h, hR, hq, hVp, hρ, hamp, hqb, hqh, hhS⟩ :=
    exists_negativeExtremalRay_contraction hW hWp hK hS hμ hμb hnef
  refine ⟨R, V, sV, q, h, by rwa [add_zero] at hR, hq, hqb, hqh, ?_⟩
  by_cases hsmall : IsSmallMorphism sW sV q
  · obtain ⟨W', i1, i2, i3, i4, sW', q', h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_model_of_isSmallMorphism hW hQ hWp hdim hK hS hμ hμb hR hq hVp hamp hqb hqh hhS
        hsmall
    exact ⟨W', i1, i2, i3, i4, sW', q', h1, h2, h3, h4, h5, h6, Or.inr h7⟩
  · obtain ⟨W', i1, i2, i3, i4, sW', q', h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_model_of_not_isSmallMorphism hW hQ hWp hdim hK hS hμ hμb hR hq hVp hρ hamp hqb hqh
        hhS hsmall
    exact ⟨W', i1, i2, i3, i4, sW', q', h1, h2, h3, h4, h5, h6, Or.inl h7⟩

end Proof_lem_mmp_indexb_terminal_step

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **One terminal step over a projective base.** Let `W` be a normal projective `ℚ`-factorial
complex threefold with `(W, 0)` terminal and canonical divisor `K`, and `μ : W ⟶ S` a birational
morphism over `ℂ` to a projective variety such that `K` is not nef over `S`. Then there are a
`K`-negative extremal ray `R` of `NE̅(W)`, its contraction `q : W ⟶ V`, birational, with
`μ = q ≫ h`, and a normal projective `ℚ`-factorial threefold `W'` with `(W', 0)` terminal, a
morphism `q' : W' ⟶ V` and the birational morphism `μ' = q' ≫ h`, such that either `Ex(q)` is a
prime divisor `F` of `W` exceptional over `S`, `q'` is an isomorphism and the prime divisors of
`W'` are the strict transforms of the prime divisors of `W` other than `F`; or `q'` is the
`K`-flip of `q` and the strict transform is a bijection of prime divisors. -/
@[mmp "lem_mmp_indexb_terminal_step"]
public theorem IsTerminalVariety.exists_terminal_step {W S : Scheme.{0}} [IsIntegral W]
    [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)}
    (hW : IsTerminalVariety sW) (hQ : IsQFactorial sW)
    (hWp : MMP.Mori.IsProjectiveVariety ℂ sW) (hdim : topologicalKrullDim W = 3)
    {K : Divisor W} {m : ℕ} (hK : K.IsCanonicalDivisor sW m)
    {sS : S ⟶ Spec (.of ℂ)} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {μ : W ⟶ S}
    (hμ : μ ≫ sS = sW) (hμb : IsBirationalMorphism μ)
    (hnef : ¬ QDivisor.IsRelativelyNef sW μ (Divisor.toQDivisor K)) :
    ∃ (R : Set (NumericalCurveClasses sW)) (V : Scheme.{0}) (sV : V ⟶ Spec (.of ℂ))
      (q : W ⟶ V) (h : V ⟶ S),
      IsNegativeExtremalRayOf sW (Divisor.toQDivisor K) R ∧ IsContractionOfRay sW sV R q ∧
      IsBirationalMorphism q ∧ q ≫ h = μ ∧
      ∃ (W' : Scheme.{0}) (_ : IsIntegral W') (_ : CompactSpace W')
        (_ : IsLocallyNoetherian W') (_ : IsNormal W') (sW' : W' ⟶ Spec (.of ℂ)) (q' : W' ⟶ V),
        IsQFactorial sW' ∧ MMP.Mori.IsProjectiveVariety ℂ sW' ∧ topologicalKrullDim W' = 3 ∧
        IsTerminalVariety sW' ∧ q' ≫ h ≫ sS = sW' ∧ IsBirationalMorphism (q' ≫ h) ∧
        ((∃ F : MMP.Mori.PrimeDivisor W, (exceptionalSet q : Set W) = F.support ∧ IsIso q' ∧
            MMP.Flips.IsExceptionalPrimeDivisor sS μ F ∧
            (∀ P, P ≠ F → (flipTransformPrimeDivisor q q' P).isSome) ∧
            ∀ P' : MMP.Mori.PrimeDivisor W', ∃ P, P ≠ F ∧ flipTransformPrimeDivisor q q' P = some P') ∨
          (IsFlipOf sW sV sW' (Divisor.toQDivisor K) q q' ∧
            InducesPrimeDivisorBijection q q')) :=
  Proof_lem_mmp_indexb_terminal_step.solution hW hQ hWp hdim hK hS hμ hμb hnef

end MMP.Fourfold
