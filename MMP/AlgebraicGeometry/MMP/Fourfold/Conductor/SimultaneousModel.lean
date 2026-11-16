module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalDefect
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalDefectBlowup
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionCenters
import MMP.AlgebraicGeometry.Resolution.TotalTransformSNC
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.AntiampleSncDomination
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.WeightedSurfaceIdentity
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupFactorization
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup

/-!
# A simultaneous curve-and-point conductor model

Let `p : Y ⟶ X` be a projective birational morphism of normal projective complex fourfolds,
with `Y` `ℚ`-factorial and terminal, and let `Q` be a reduced divisor on `Y` with
`dim p(Q) ≤ 1`. There is a curve-and-point exceptional model `r₀ : Z₀ ⟶ Y`
(`MMP.Fourfold.IsCurvePointExceptionalModel`) and a smooth blow-up sequence `q : Z ⟶ Z₀` whose
centres have simple normal crossings with the exceptional boundary of `r₀`, such that
`r = r₀ ∘ q` is an embedded resolution of `Q`, the full exceptional locus of `p ∘ r` is an snc
divisor which is the support of an effective divisor `D` with `-D` relatively ample over `X`,
and the inverse image under `r` of the ideal of each of finitely many prescribed subvarieties
(the conductor surfaces of `Q`) is invertible. Consequently the vertical defect over `Q`
satisfies `dim D_{v,Q}(r) ≤ ∑_{T ⊆ Sing Y ∩ Q} b_T`.

## Main results

* `MMP.Fourfold.exists_isCurvePointExceptionalModel_finrank_verticalDefectOver_le`.

## Implementation notes

* The boundary-compatible smooth blow-ups are a `MMP.Resolution.ClosedBlowupSequence` of `Z₀`
  which is smooth (`MMP.Resolution.ClosedBlowupSequence.IsSmooth`) and whose centres have simple
  normal crossings with the support of the exceptional divisor `F₀` of `r₀`
  (`MMP.Resolution.ClosedBlowupSequence.CentersHaveSNCWith`); `Z` is identified with its last
  scheme, `q` with the composite of the blow-ups.
* `r` is an embedded resolution of `Q`: it is a resolution and `r⁻¹(Q) ∪ Ex(r)` is a divisor
  with simple normal crossings (`MMP.Resolution.IsSNCClosedSubset`).
* For each `V` of a finite family of irreducible closed subsets of `Y` (the conductor surfaces
  of `Q` being one), the inverse image ideal `r⁻¹ I_V · 𝒪_Z` has principal stalks. For a
  surface `V` whose generic point `η_V` lies in the smooth locus of `Y`, moreover, the base
  change of `r` to `Spec 𝒪_{Y,η_V}` is a finite sequence of point blow-ups
  (`MMP.Resolution.PointBlowupSequence`) whose first centre is the closed point: the generic
  transverse resolution of `V` includes the blow-up of its point.
* The reduced divisor `F` with support `Ex(r)` exists, and the bound is stated for it.
* `b_T = curveLocalSystemRank` is computed on local-system opens `T° ⊆ T`
  (`MMP.Fourfold.IsLocalSystemOpen`); the bound is asserted for every choice of them.
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.Mori MMP.Fourfold

namespace MMP.Fourfold.SimultaneousModel

/-- The blow-up closure property under which the vertical defect injects
(`MMP.Fourfold.exists_injective_verticalDefect_blowup`): `q` is reached from `𝟙 Z₀` by
blow-ups of smooth centres with simple normal crossings with the exceptional locus over `Y`. -/
private def IsBoundaryBlowup {Z₀ Y : Scheme.{0}} [Z₀.Over (Spec (.of ℂ))] (r₀ : Z₀ ⟶ Y)
    {Z : Scheme.{0}} (q : Z ⟶ Z₀) : Prop :=
  ∀ P : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z₀) → Prop, P (𝟙 Z₀) →
    (∀ ⦃W : Scheme.{0}⦄ (p : W ⟶ Z₀) (I : W.IdealSheafData), P p →
      MMP.Mori.IsSmoothScheme (I.subschemeι ≫ p ≫ (Z₀ ↘ Spec (.of ℂ))) →
      MMP.Resolution.HasSNCWith
        (MMP.Resolution.componentsFamily (exceptionalSet (p ≫ r₀) : Set W)) I →
      P (blowUpToBase I ≫ p)) → P q

section BoundaryBlowups

open MMP.Resolution

/-- A family with simple normal crossings with `Z` restricts to any subfamily. -/
private theorem hasSNCWith_comp {X : Scheme.{0}} {Λ Λ' : Type*} (E : Λ → X.IdealSheafData)
    (ι : Λ' → Λ) (hι : Function.Injective ι) {Z : X.IdealSheafData} (h : HasSNCWith E Z) :
    HasSNCWith (E ∘ ι) Z := by
  intro x hx
  obtain ⟨n, z, c, J, hz, hc, hinj, hZ⟩ := h x hx
  refine ⟨n, z, fun i => c ⟨ι i.1, i.2⟩, J, hz, fun i => hc ⟨ι i.1, i.2⟩, ?_, hZ⟩
  intro i j hij
  exact Subtype.ext (hι (congrArg Subtype.val (hinj hij)))

/-- Simple normal crossings with the components of `B` give simple normal crossings with the
components of `A`, when every component of `A` is one of `B`. -/
private theorem hasSNCWith_componentsFamily_of_subset {X : Scheme.{0}} {A B : Set X}
    (h : componentsOf A ⊆ componentsOf B) {Z : X.IdealSheafData}
    (hZ : HasSNCWith (componentsFamily B) Z) : HasSNCWith (componentsFamily A) Z :=
  hasSNCWith_comp (componentsFamily B) (fun W : componentsOf A => (⟨W.1, h W.2⟩ : componentsOf B))
    (fun a b e => Subtype.ext (congrArg (fun w : componentsOf B => w.1) e)) hZ

/-- A closed subset of pure codimension one inside another one has its components among
those of the larger one. -/
private theorem componentsOf_subset_of_isPureCodimOne {X : Scheme.{0}} {A B : Set X}
    (hAc : IsClosed A) (hBc : IsClosed B) (hA : MMP.Mori.IsPureCodimOne (⟨A, hAc⟩ : Closeds X))
    (hB : MMP.Mori.IsPureCodimOne (⟨B, hBc⟩ : Closeds X)) (hAB : A ⊆ B) :
    componentsOf A ⊆ componentsOf B := by
  intro W hW
  obtain ⟨ξ, hWξ, hξ⟩ := MMP.ProgramBaseChange.exists_coheight_eq_one_of_mem_componentsOf hAc hA hW
  have hξW : ξ ∈ W := hWξ ▸ subset_closure rfl
  obtain ⟨C, hC, hξC⟩ := exists_mem_componentsOf (hAB (hW.1.2 hξW))
  obtain ⟨ξ', hCξ', hξ'⟩ :=
    MMP.ProgramBaseChange.exists_coheight_eq_one_of_mem_componentsOf hBc hB hC
  have hsp : ξ' ⤳ ξ := specializes_iff_mem_closure.mpr (hCξ' ▸ hξC)
  have heq : ξ = ξ' := by
    by_contra hne
    have hlt : ξ < ξ' := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hsp) fun hle =>
      hne (hsp.antisymm (Scheme.le_iff_specializes.mp hle)).eq.symm
    have := Order.coheight_strictAnti hlt (by rw [hξ']; exact WithTop.coe_lt_top 1)
    rw [hξ, hξ'] at this
    exact lt_irrefl _ this
  rw [hWξ, heq, ← hCξ']
  exact hC

/-- Every component of a set `E` lies in `E`, so `componentsOf E ⊆ componentsOf E'` forces
`E ⊆ E'`. -/
private theorem subset_of_componentsOf_subset {X : Scheme.{0}} {E E' : Set X}
    (h : componentsOf E ⊆ componentsOf E') : E ⊆ E' := by
  intro x hx
  obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hx
  exact (h hW).1.2 hxW

/-- A maximal irreducible closed subset of a closed set `E` is a component of `E`. -/
private theorem mem_componentsOf_of_maximal {X : Scheme.{0}} {E : Set X} (hE : IsClosed E)
    {W : IrreducibleCloseds X}
    (hW : Maximal (fun W' : IrreducibleCloseds X => (W' : Set X) ⊆ E) W) :
    (W : Set X) ∈ componentsOf E :=
  ⟨⟨W.isIrreducible, hW.1⟩, fun s hs hle => subset_closure.trans
    (hW.2 (y := ⟨closure s, hs.1.closure, isClosed_closure⟩) (closure_minimal hs.2 hE)
      (hle.trans subset_closure))⟩

/-- Components of a closed set of pure codimension one inside an snc set are components of the
snc set. -/
private theorem componentsOf_subset_of_isSNCClosedSubset_right {k : Type} [Field k]
    {X : Scheme.{0}} {s : X ⟶ Spec (.of k)} {A B : Set X} (hAc : IsClosed A)
    (hA : MMP.Mori.IsPureCodimOne (⟨A, hAc⟩ : Closeds X)) (hB : IsSNCClosedSubset s B)
    (hAB : A ⊆ B) : componentsOf A ⊆ componentsOf B := by
  obtain ⟨hBc, hB0 | ⟨hBp, -, -⟩⟩ := hB
  · exact fun V hV => ((hV.1.1.nonempty.mono (hV.1.2.trans hAB)).ne_empty hB0).elim
  exact componentsOf_subset_of_isPureCodimOne hAc hBc hA hBp hAB

/-- A composite of birational morphisms of irreducible schemes is birational. -/
private theorem isBirationalMorphism_comp {V X' X : Scheme.{0}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
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

/-- The blow-up of an integral scheme along an ideal whose cosupport misses the generic point is
birational. -/
private theorem isBirationalMorphism_blowUpToBase {W : Scheme.{0}} [IsIntegral W]
    (I : W.IdealSheafData) [IsIntegral (blowUp I)] (hI : genericPoint W ∉ I.support) :
    MMP.Mori.IsBirationalMorphism (blowUpToBase I) := by
  have hiso := isIso_blowUp_restrict_compl_support I
  set V : W.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨x, -⟩ := (asIso (blowUpToBase I ∣_ V)).hom.homeomorph.surjective ⟨_, hI⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (blowUpToBase I) (blowUpToBase I ⁻¹ᵁ V) V
    ⟨x.1, x.2⟩ ⟨_, hI⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact hiso

/-- **The blow-up closure property along a boundary-compatible sequence.** Let `r₀ : Z₀ ⟶ Y`
map to a `ℚ`-factorial `Y`, and let `p : W ⟶ Z₀` be such that `p ≫ r₀` is a projective
birational morphism from a variety with an ample invertible sheaf, whose exceptional locus lies
in `E`. Then every smooth blow-up sequence `B` of `W` whose centres have simple normal crossings
with `E` and lie over a set missing the generic point of `Z₀` is reached from `p` by blow-ups
of smooth centres with simple normal crossings with the exceptional locus over `Y`: each
component of that locus is a component of the total transform of `E`, both being of pure
codimension one. -/
private theorem toBase_comp_of_isSmooth {Z₀ Y : Scheme.{0}} [Z₀.Over (Spec (.of ℂ))]
    [IsIntegral Z₀] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hQf : IsQFactorial sY) (r₀ : Z₀ ⟶ Y) (hr₀ : r₀ ≫ sY = Z₀ ↘ Spec (.of ℂ))
    (P : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z₀) → Prop)
    (hP : ∀ ⦃W : Scheme.{0}⦄ (p : W ⟶ Z₀) (I : W.IdealSheafData), P p →
      MMP.Mori.IsSmoothScheme (I.subschemeι ≫ p ≫ (Z₀ ↘ Spec (.of ℂ))) →
      HasSNCWith (componentsFamily (exceptionalSet (p ≫ r₀) : Set W)) I →
      P (blowUpToBase I ≫ p)) :
    ∀ {W T : Scheme.{0}} [IsIntegral W] (B : ClosedBlowupSequence W) (p : W ⟶ Z₀) (E : Set W)
      (f : W ⟶ T) (S : Set T), P p →
      AlgebraicGeometry.IsVariety ℂ (p ≫ Z₀ ↘ Spec (.of ℂ)) →
      IsProjectiveMorphism (p ≫ r₀) → MMP.Mori.IsBirationalMorphism (p ≫ r₀) →
      (∃ (M : W.Modules) (_ : Stacks.Ample.IsInvertibleModule W M), Stacks.Ample.IsAmple W M) →
      (exceptionalSet (p ≫ r₀) : Set W) ⊆ E →
      B.IsSmooth (p ≫ Z₀ ↘ Spec (.of ℂ)) → B.CentersHaveSNCWith (p ≫ Z₀ ↘ Spec (.of ℂ)) E →
      B.CentersLieOver f S → f (genericPoint W) ∉ S →
      P (B.toBase ≫ p) ∧
        (exceptionalSet (B.toBase ≫ p ≫ r₀) : Set B.target) ⊆ B.totalTransform E
  | _, _, _, .nil _, p, _, _, _, hp, _, _, _, _, hEx, _, _, _, _ => by
    refine ⟨?_, ?_⟩
    · show @P _ (𝟙 _ ≫ p)
      rw [Category.id_comp]
      exact hp
    · have e : (ClosedBlowupSequence.nil _).toBase ≫ p ≫ r₀ = p ≫ r₀ := Category.id_comp _
      rw [e]
      exact hEx
  | W, _, _, .cons Z B, p, E, f, S, hp, hv, hproj, hbir, ⟨M, hMinv, hMamp⟩, hEx, ⟨_, hZs, hBs⟩,
      ⟨hEsnc, hZE, hBE⟩, hlie, hfS => by
    rw [ClosedBlowupSequence.CentersLieOver] at hlie
    obtain ⟨hZS, hBS⟩ := hlie
    haveI := hv
    haveI : IsIntegral W := hv.toIsIntegral
    haveI : LocallyOfFiniteType (p ≫ Z₀ ↘ Spec (.of ℂ)) := hv.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ Z₀ ↘ Spec (.of ℂ))
    haveI := hMinv
    -- the first step
    have hpure : MMP.Mori.IsPureCodimOne (exceptionalSet (p ≫ r₀)) :=
      MMP.Mori.isPureCodimOne_exceptionalSet_of_isQFactorial sY (p ≫ Z₀ ↘ Spec (.of ℂ)) hQf hv
        (p ≫ r₀) (by rw [Category.assoc, hr₀]) hproj hbir
    have hP1 : P (blowUpToBase Z ≫ p) := hP p Z hp hZs (hasSNCWith_componentsFamily_of_subset
      (componentsOf_subset_of_isSNCClosedSubset_right _ hpure hEsnc hEx) hZE)
    -- the blow-up
    have hZgen : genericPoint W ∉ Z.support := fun h => hfS (hZS ⟨_, h, rfl⟩)
    have hZ0 : Z ≠ ⊥ := by
      rintro rfl
      exact hZgen (by simp; trivial)
    obtain ⟨hv', -, -⟩ :=
      MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
        (p ≫ Z₀ ↘ Spec (.of ℂ)) Z hZ0
    haveI : IsIntegral (blowUp Z) := hv'.toIsIntegral
    have hft := TwoStepTower.isFiniteType_of_isLocallyNoetherian Z
    haveI : IsProper (blowUpToBase Z) := TwoStepTower.isProper_blowUpToBase hft
    have hblproj : IsProjectiveMorphism (blowUpToBase Z) :=
      isProjectiveMorphism_of_isQuasiProjective _ M hMamp
        (Stacks.Blowup.isQuasiProjective_blowUpToBase Z hft)
    have hblbir := isBirationalMorphism_blowUpToBase Z hZgen
    haveI : IsDominant (blowUpToBase Z) := hblbir.isDominant
    haveI : IsProper (p ≫ r₀) := isProper_of_isProjectiveMorphism _ hproj
    have hEx' : (exceptionalSet (blowUpToBase Z ≫ p ≫ r₀) : Set (blowUp Z)) ⊆
        ClosedBlowupSequence.totalTransformStep Z E := by
      refine (MMP.Fourfold.SNCWeight.SNCModel.exceptionalSet_comp_subset (p ≫ r₀) (blowUpToBase Z)
        Z.support (isIso_blowUp_restrict_compl_support Z) (B := E ∪ (Z.support : Set W))
        (hEx.trans Set.subset_union_left) Set.subset_union_right).trans ?_
      intro y hy
      by_cases hyZ : blowUpToBase Z y ∈ (Z.support : Set W)
      · exact Or.inr hyZ
      · exact Or.inl (subset_closure ⟨hy.resolve_right hyZ, hyZ⟩)
    obtain ⟨M', hM'inv, hM'amp⟩ := exists_isAmple_of_isProjectiveMorphism _ M hMamp hblproj
    have hgen' : (blowUpToBase Z ≫ f) (genericPoint (blowUp Z)) ∉ S := by
      rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
      exact hfS
    obtain ⟨h1, h2⟩ := toBase_comp_of_isSmooth hQf r₀ hr₀ P hP B (blowUpToBase Z ≫ p)
      (ClosedBlowupSequence.totalTransformStep Z E) (blowUpToBase Z ≫ f) S hP1
      (by rw [Category.assoc]; exact hv')
      (by rw [Category.assoc]; exact hblproj.comp hproj)
      (by rw [Category.assoc]; exact isBirationalMorphism_comp hblbir hbir) ⟨M', hM'inv, hM'amp⟩
      (by rw [Category.assoc]; exact hEx') (by rw [Category.assoc]; exact hBs)
      (by rw [Category.assoc]; exact hBE) hBS hgen'
    refine ⟨?_, ?_⟩
    · change P ((B.toBase ≫ blowUpToBase Z) ≫ p)
      rwa [Category.assoc]
    · change (exceptionalSet ((B.toBase ≫ blowUpToBase Z) ≫ p ≫ r₀) : Set B.target) ⊆
        B.totalTransform (ClosedBlowupSequence.totalTransformStep Z E)
      simpa only [Category.assoc] using h2

/-- **Krull's height theorem on a scheme.** The generic point of an irreducible component of the
cosupport of an ideal has coheight at most the number of generators of its ideal on an affine open
containing it. -/
private theorem coheight_le_spanRank_ideal {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {η : X}
    (hη : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X)) (closure {η}))
    (W : X.affineOpens) (hηW : η ∈ W.1) :
    Order.coheight η ≤ Cardinal.toENat (Submodule.spanRank (I.ideal W)) := by
  have hW : IsAffineOpen W.1 := W.2
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  set x := hW.primeIdealOf ⟨η, hηW⟩ with hx_def
  have hx : hW.fromSpec x = η := hW.fromSpec_primeIdealOf ⟨η, hηW⟩
  have hsupp : ∀ y : Spec Γ(X, W.1),
      hW.fromSpec y ∈ (I.support : Set X) ↔ (I.ideal W : Set Γ(X, W.1)) ⊆ y.asIdeal := by
    intro y
    have hyW : hW.fromSpec y ∈ W.1 := by
      rw [← SetLike.mem_coe, ← hW.range_fromSpec]
      exact ⟨y, rfl⟩
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem hyW]
    rw [← Set.mem_preimage, hW.fromSpec_preimage_zeroLocus]
    rfl
  have hηsupp : η ∈ (I.support : Set X) := hη.prop.2 (subset_closure rfl)
  have hmin : x.asIdeal ∈ (I.ideal W).minimalPrimes := by
    refine ⟨⟨x.isPrime, (hsupp x).mp (hx ▸ hηsupp)⟩, ?_⟩
    rintro q ⟨hq, hJq⟩ hqx
    let y : Spec Γ(X, W.1) := ⟨q, hq⟩
    have hyx : y ⤳ x := (PrimeSpectrum.le_iff_specializes y x).mp hqx
    have hyη : hW.fromSpec y ⤳ η := hx ▸ hyx.map (hW.fromSpec).continuous
    have hysupp : hW.fromSpec y ∈ (I.support : Set X) := (hsupp y).mpr hJq
    have hcl : closure {hW.fromSpec y} ⊆ closure {η} := by
      refine hη.2 ⟨isIrreducible_singleton.closure, ?_⟩
        (specializes_iff_closure_subset.mp hyη)
      exact (I.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hysupp)
    have hηy : η ⤳ hW.fromSpec y := specializes_iff_closure_subset.mpr hcl
    rw [← hx] at hηy
    have hxy : x ⤳ y := hW.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hηy
    exact (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hle := Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hmin
  rwa [idealHeight_eq_coheight _ x,
    show Order.coheight (α := Spec Γ(X, W.1)) x = Order.coheight η from
      (coheight_eq_of_isOpenImmersion (x := x) hW.fromSpec).symm.trans (congrArg _ hx)] at hle

/-- **Krull's principal ideal theorem.** On an integral locally noetherian scheme, the generic
point of an irreducible component of the support of an effective Cartier divisor not containing
the generic point has coheight one. -/
private theorem coheight_eq_one_of_isEffectiveCartierDivisor {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hgen : genericPoint X ∉ I.support)
    {η : X}
    (hmax : Maximal (fun s : Set X => IsIrreducible s ∧ s ⊆ (I.support : Set X)) (closure {η})) :
    Order.coheight η = 1 := by
  have hηI : η ∈ (I.support : Set X) := hmax.prop.2 (subset_closure rfl)
  obtain ⟨U, hU, hηU, f, -, hf⟩ :=
    Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor I hI η
  have h1 := coheight_le_spanRank_ideal I hmax ⟨U, hU⟩ hηU
  have hrank : Cardinal.toENat (Submodule.spanRank (I.ideal ⟨U, hU⟩)) ≤ 1 := by
    rw [hf]
    have := Submodule.spanRank_span_le_card (R := Γ(X, U)) ({f} : Set Γ(X, U))
    rw [Cardinal.mk_singleton] at this
    exact (Cardinal.toENat.monotone' this).trans (by simp)
  have h0 : Order.coheight η ≠ 0 := by
    intro h0
    rw [Order.coheight_eq_zero] at h0
    have hle : η ≤ genericPoint X := by
      rw [Scheme.le_iff_specializes]
      exact genericPoint_specializes η
    have h2 := h0 hle
    rw [Scheme.le_iff_specializes] at h2
    exact hgen (h2.mem_closed I.support.isClosed hηI)
  exact le_antisymm (h1.trans hrank) (Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0))

/-- **Pure codimension one of an effective Cartier divisor.** On an integral locally noetherian
scheme, the support of an effective Cartier divisor missing the generic point is of pure
codimension one. -/
private theorem isPureCodimOne_support_of_isEffectiveCartierDivisor {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hgen : genericPoint X ∉ I.support) :
    MMP.Mori.IsPureCodimOne I.support := by
  intro W hW
  set e := irreducibleSetEquivPoints (α := X)
  have hWη : (W : Set X) = closure {e W} := by
    conv_lhs => rw [← e.symm_apply_apply W]
    rfl
  have h1 : codimension W = Order.coheight (e W) := by
    change Order.coheight W = _
    rw [← Order.coheight_orderIso e W]
  rw [h1]
  refine coheight_eq_one_of_isEffectiveCartierDivisor I hI hgen ?_
  rw [← hWη]
  exact mem_componentsOf_of_maximal I.support.isClosed hW

/-- Components of an snc subset of an snc set are components of the larger set. -/
private theorem componentsOf_subset_of_isSNCClosedSubset {k k' : Type} [Field k] [Field k']
    {X : Scheme.{0}} {s : X ⟶ Spec (.of k)} {s' : X ⟶ Spec (.of k')} {A B : Set X}
    (hA : IsSNCClosedSubset s A) (hB : IsSNCClosedSubset s' B) (hAB : A ⊆ B) :
    componentsOf A ⊆ componentsOf B := by
  obtain ⟨hAc, hA0 | ⟨hAp, -, -⟩⟩ := hA
  · exact fun V hV => ((hV.1.1.nonempty.mono hV.1.2).ne_empty hA0).elim
  exact componentsOf_subset_of_isSNCClosedSubset_right hAc hAp hB hAB

/-- The union of two closed sets of pure codimension one is of pure codimension one. -/
private theorem isPureCodimOne_union {X : Scheme.{0}} {A B : Set X} (hAc : IsClosed A)
    (hBc : IsClosed B) (hA : MMP.Mori.IsPureCodimOne (⟨A, hAc⟩ : Closeds X))
    (hB : MMP.Mori.IsPureCodimOne (⟨B, hBc⟩ : Closeds X)) :
    MMP.Mori.IsPureCodimOne (⟨A ∪ B, hAc.union hBc⟩ : Closeds X) := by
  intro W hW
  have hAB : (W : Set X) ⊆ A ∨ (W : Set X) ⊆ B := by
    by_contra hc
    rw [not_or, Set.not_subset, Set.not_subset] at hc
    obtain ⟨⟨a, haW, haA⟩, ⟨b, hbW, hbB⟩⟩ := hc
    obtain ⟨x, hxW, hxA, hxB⟩ := W.isIrreducible.isPreirreducible _ _ hAc.isOpen_compl
      hBc.isOpen_compl ⟨a, haW, haA⟩ ⟨b, hbW, hbB⟩
    rcases hW.1 hxW with h | h
    · exact hxA h
    · exact hxB h
  rcases hAB with h | h
  · exact hA W ⟨h, fun W' hW' hle => hW.2 (hW'.trans Set.subset_union_left) hle⟩
  · exact hB W ⟨h, fun W' hW' hle => hW.2 (hW'.trans Set.subset_union_right) hle⟩

/-- A union of irreducible components of a divisor with simple normal crossings is a divisor
with simple normal crossings. -/
private theorem isSNCClosedSubset_of_componentsOf_subset {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {E E' : Set X} (hE' : IsSNCClosedSubset sX E') (hEc : IsClosed E)
    (h : componentsOf E ⊆ componentsOf E') : IsSNCClosedSubset sX E := by
  obtain ⟨hE'c, hE'0 | ⟨hpure, hfin, hfam⟩⟩ := hE'
  · exact ⟨hEc, Or.inl (Set.subset_empty_iff.1 (hE'0 ▸ subset_of_componentsOf_subset h))⟩
  refine ⟨hEc, Or.inr ⟨fun W hW => hpure W ⟨(h (mem_componentsOf_of_maximal hEc hW)).1.2,
    fun W' hW' hle => (h (mem_componentsOf_of_maximal hEc hW)).2 ⟨W'.isIrreducible, hW'⟩ hle⟩,
    hfin.subset h, ?_, ?_⟩⟩
  · exact fun i => hfam.1 ⟨i.1, h i.2⟩
  · intro x
    obtain ⟨n, z, c, hz, hc, hinj⟩ := hfam.2 x
    refine ⟨n, z, fun i => c ⟨⟨i.1.1, h i.1.2⟩, i.2⟩, hz, fun i => hc ⟨⟨i.1.1, h i.1.2⟩, i.2⟩, ?_⟩
    intro i j hij
    have := congrArg (fun w => w.1.1) (hinj hij)
    exact Subtype.ext (Subtype.ext this)

/-- The total transform under one blow-up is monotone. -/
private theorem totalTransformStep_mono {X : Scheme.{0}} (Z : X.IdealSheafData) {E E' : Set X}
    (h : E ⊆ E') :
    ClosedBlowupSequence.totalTransformStep Z E ⊆ ClosedBlowupSequence.totalTransformStep Z E' :=
  Set.union_subset_union_left _ (closure_mono (Set.preimage_mono (Set.diff_subset_diff_left h)))

/-- **Simple normal crossings with a union of components.** If the centres of a smooth blow-up
sequence have simple normal crossings with `E'`, they have simple normal crossings with every
union `E` of components of `E'`. -/
private theorem centersHaveSNCWith_of_componentsOf_subset :
    ∀ {W : Scheme.{0}} (B : ClosedBlowupSequence W) (s : W ⟶ Spec (.of ℂ))
      [LocallyOfFiniteType s] [QuasiCompact s] (E E' : Set W), IsClosed E →
      componentsOf E ⊆ componentsOf E' → B.IsSmooth s → B.CentersHaveSNCWith s E' →
      B.CentersHaveSNCWith s E
  | _, .nil _, _, _, _, _, _, _, _, _, _ => trivial
  | W, .cons Z B, s, _, _, E, E', hEc, h, ⟨hWs, _, hBs⟩, ⟨hE'snc, hZE', hBE'⟩ => by
    have hEsnc := isSNCClosedSubset_of_componentsOf_subset hE'snc hEc h
    have hZE := hasSNCWith_componentsFamily_of_subset h hZE'
    refine ⟨hEsnc, hZE, ?_⟩
    haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian s
    have hft := TwoStepTower.isFiniteType_of_isLocallyNoetherian Z
    haveI : IsProper (blowUpToBase Z) := TwoStepTower.isProper_blowUpToBase hft
    have h1 := isSNCClosedSubset_totalTransformStep s hWs hEsnc hZE
    have h2 := isSNCClosedSubset_totalTransformStep s hWs hE'snc hZE'
    have hsub := totalTransformStep_mono Z (subset_of_componentsOf_subset h)
    exact centersHaveSNCWith_of_componentsOf_subset B _ _ _ h1.1
      (componentsOf_subset_of_isSNCClosedSubset h1 h2 hsub) hBs hBE'

/-- The total transform of a closed set lies over the set and the images of the centres. -/
private theorem totalTransform_subset_preimage :
    ∀ {W T : Scheme.{0}} (B : ClosedBlowupSequence W) (f : W ⟶ T) (S : Set T) (E : Set W),
      IsClosed E → B.CentersLieOver f S →
        B.totalTransform E ⊆ B.toBase ⁻¹' (E ∪ f ⁻¹' S)
  | _, _, .nil _, _, _, _, _, _ => fun x hx => Or.inl hx
  | _, _, .cons Z B, f, S, E, hE, hlie => by
    rw [ClosedBlowupSequence.CentersLieOver] at hlie
    obtain ⟨hZS, hBS⟩ := hlie
    have hstep : ClosedBlowupSequence.totalTransformStep Z E ⊆
        blowUpToBase Z ⁻¹' (E ∪ f ⁻¹' S) := by
      rintro y (hy | hy)
      · exact Or.inl (closure_minimal (Set.preimage_mono Set.diff_subset)
          (hE.preimage (blowUpToBase Z).continuous) hy)
      · exact Or.inr (hZS ⟨_, hy, rfl⟩)
    have hcl : IsClosed (ClosedBlowupSequence.totalTransformStep Z E) :=
      isClosed_closure.union (Z.support.isClosed.preimage (blowUpToBase Z).continuous)
    intro x hx
    have := totalTransform_subset_preimage B (blowUpToBase Z ≫ f) S _ hcl hBS hx
    rcases this with h | h
    · exact hstep h
    · exact Or.inr h

/-- The inverse image of a set lies in its total transform. -/
private theorem preimage_subset_totalTransform :
    ∀ {W : Scheme.{0}} (B : ClosedBlowupSequence W) (E : Set W),
      B.toBase ⁻¹' E ⊆ B.totalTransform E
  | _, .nil _, _ => fun _ hx => hx
  | _, .cons Z B, E => by
    intro x hx
    refine preimage_subset_totalTransform B _ ?_
    change blowUpToBase Z (B.toBase x) ∈ E at hx
    by_cases hZ : blowUpToBase Z (B.toBase x) ∈ (Z.support : Set _)
    · exact Or.inr hZ
    · exact Or.inl (subset_closure ⟨hx, hZ⟩)

end BoundaryBlowups

/-- **The defect bound on a blow-up of a curve-and-point model.** -/
private theorem finrank_verticalDefectOver_le_of_isBoundaryBlowup
    {Z₀ Y Z : Scheme.{0}} [Z₀.Over (Spec (.of ℂ))] [IsComplexScheme Z₀] [CompactSpace Z₀]
    [IsLocallyNoetherian Z₀] [IsNormal Z₀] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {r₀ : Z₀ ⟶ Y} {F₀ D₀ : Divisor Z₀}
    (hM : IsCurvePointExceptionalModel sY r₀ F₀ D₀) (hZ₀ : IsProjective (Z₀ ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim Z₀ = 4)
    [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] (q : Z ⟶ Z₀) [q.IsOver (Spec (.of ℂ))]
    (hq : IsBoundaryBlowup r₀ q) (F : Divisor Z) (hF : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set Z) = exceptionalSet (q ≫ r₀)) (Q : Set Y) (hQ : IsClosed Q)
    (To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
      topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens)
    (hTo : ∀ T, IsLocalSystemOpen sY (To T)) (hres : MMP.Intersection.IsResolution sY (q ≫ r₀)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
      hM.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
    haveI : (q ≫ r₀).IsOver (Spec (.of ℂ)) :=
      ⟨by change (q ≫ r₀) ≫ sY = _; simp [hM.comp_eq]⟩
    haveI : IsProper (q ≫ r₀) := isProper_of_isProjectiveMorphism _ hres.2.2.2.1
    Module.finrank ℚ (verticalDefectOver (q ≫ r₀) F Q) ≤
      ∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ Q), curveLocalSystemRank sY (To T) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    hM.isProjectiveVariety.toIsVariety.toLocallyOfFiniteType
  haveI : r₀.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI : IsProper r₀ := isProper_of_isProjectiveMorphism _ hM.isResolution.2.2.2.1
  haveI : IsProper (q ≫ r₀) := isProper_of_isProjectiveMorphism _ hres.2.2.2.1
  obtain ⟨φ, hφ, hφQ⟩ := exists_injective_verticalDefect_blowup sY r₀ F₀ hM.comp_eq
    hM.isProjectiveVariety hM.isQFactorial hM.isResolution hZ₀ hdim hM.isReducedEffective
    hM.isSNC hM.supp_eq_exceptionalSet q hq F hF hFex
  obtain ⟨hfin, -, hcp⟩ := finiteDimensional_componentHomology_and_verticalDefect hM.comp_eq
    hM.isProjectiveVariety hM.isQFactorial hM.isResolution hdim hM.isReducedEffective hM.isSNC
    hM.supp_eq_exceptionalSet
  haveI := hfin
  calc Module.finrank ℚ (verticalDefectOver (q ≫ r₀) F Q)
      = Module.finrank ℚ ((verticalDefectOver (q ≫ r₀) F Q).map φ) :=
        (Submodule.equivMapOfInjective φ hφ _).finrank_eq
    _ ≤ Module.finrank ℚ (verticalDefectOver r₀ F₀ Q) := Submodule.finrank_mono (hφQ Q hQ)
    _ ≤ _ := ((hcp D₀ hM).2.2 Q hQ To hTo)

variable {X Y : Scheme.{0}} [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

section CurvePointModel

/-- A point over which a morphism from a smooth scheme is biregular is a smooth point. -/
private theorem mem_smoothLocus_of_mem_biregularLocus {Z Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    (r : Z ⟶ Y) (hZ : Smooth (r ≫ sY)) {y : Y} (hy : y ∈ biregularLocus r) :
    y ∈ smoothLocus sY := by
  haveI : IsIso (r ∣_ biregularLocus r) := isBiregular_biregularLocus r
  refine (mem_smoothLocus_iff).2 ⟨biregularLocus r, hy, ?_⟩
  have e : (biregularLocus r).ι ≫ sY =
      inv (r ∣_ biregularLocus r) ≫ (r ⁻¹ᵁ biregularLocus r).ι ≫ r ≫ sY := by
    rw [← Category.assoc (r ⁻¹ᵁ biregularLocus r).ι, ← morphismRestrict_ι, Category.assoc,
      IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- On a fourfold, a closed set of codimension at least three has dimension at most one. -/
private theorem topologicalKrullDim_le_one_of_three_le_closedsCodimension {Y : Scheme.{0}}
    [IsIntegral Y] (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY]
    (hdimY : topologicalKrullDim Y = 4) (C : Closeds Y) (hC : 3 ≤ closedsCodimension C) :
    topologicalKrullDim (C : Set Y) ≤ 1 :=
  MMP.Fourfold.topologicalKrullDim_le_sub_of_le_coheight ℂ sY (n := 4) (r := 3)
    (by rw [hdimY]; rfl) C.isClosed fun y hy => by
      have := (le_closedsCodimension_iff.1 hC) (IrreducibleCloseds.closureSingleton y)
        (closure_minimal (Set.singleton_subset_iff.2 hy) C.isClosed)
      rwa [MMP.Flips.codimension_closureSingleton] at this

/-- **A curve-and-point exceptional model exists.** For a projective `ℚ`-factorial terminal
complex fourfold `Y`, whose singular locus has dimension at most one, the dominating snc model
with an antiample exceptional divisor over `C = Sing Y`, which is an isomorphism over `Y_reg`,
is a curve-and-point exceptional model. -/
private theorem exists_isCurvePointExceptionalModel {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQf : IsQFactorial sY)
    (hdimY : topologicalKrullDim Y = 4) (hYt : IsTerminalVariety sY) :
    ∃ (Z₀ : Scheme.{0}) (_ : Z₀.Over (Spec (.of ℂ))) (_ : CompactSpace Z₀)
      (_ : IsLocallyNoetherian Z₀) (_ : IsNormal Z₀) (r₀ : Z₀ ⟶ Y) (F₀ D₀ : Divisor Z₀),
      IsCurvePointExceptionalModel sY r₀ F₀ D₀ ∧
        MMP.Mori.IsProjectiveVariety ℂ (r₀ ≫ sY) := by
  obtain ⟨hYv, -⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sY).1 hY
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  -- `dim Sing Y ≤ 1`
  obtain ⟨-, n, K, hK, hKQ⟩ := hYt.1.1.isPair
  have hcod := (IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    hYt QDivisor.isQCartier_zero hK (by simpa using hKQ)).2
  have hSing := topologicalKrullDim_le_one_of_three_le_closedsCodimension sY hdimY _ hcod
  -- the dominating model over `Y` with `C = Sing Y`
  obtain ⟨Z, _, _, _, r, -, hres, hZproj, hbir, ⟨F, hFred, hFsnc, hFex, D, hDpos, hD0, hDc,
      hDamp⟩, -⟩ :=
    MMP.Fourfold.exists_isResolution_comp_isSNC_isRelativelyAmple_neg_and_mem_biregularLocus
      (p := 𝟙 Y) (sX := sY) hY hdimY (by rwa [Category.id_comp]) hdimY (isProjectiveMorphism_id Y)
      (isBirationalMorphism_of_isIso _) (singularLocus sY) hSing
  simp only [Category.comp_id, Category.id_comp] at hres hZproj hbir hFsnc hFex hDamp
  letI : Z.Over (Spec (.of ℂ)) := ⟨r ≫ sY⟩
  have hsm : Smooth (r ≫ sY) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _ hres.2.2.1
  have hid : ∀ y : Y, y ∈ biregularLocus (𝟙 Y) := fun y =>
    le_biregularLocus (V := ⊤) (show IsIso ((𝟙 Y) ∣_ ⊤) by infer_instance) trivial
  have hsmooth : smoothLocus sY ≤ biregularLocus r := fun y hy =>
    hbir y (fun h => h hy) (hid y) fun y' h => by
      have : y' = y := h
      rw [this]; exact hy
  have hexc : (exceptionalSet r : Set Z) = r.base ⁻¹' (singularLocus sY : Set Y) := by
    ext z
    change z ∈ exceptionalSet r ↔ r z ∉ smoothLocus sY
    rw [mem_exceptionalSet]
    exact ⟨fun h hs => h (hsmooth hs),
      fun h hb => h (mem_smoothLocus_of_mem_biregularLocus r hsm hb)⟩
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance, r, F, D,
    ⟨rfl, hY, hQf, hdimY, hYt, hres, isBiregular_iff_le_biregularLocus.2 hsmooth, hFred, hFsnc,
      hFex, hFex.trans hexc, hDpos, hD0, ⟨hDc, hDamp⟩, fun P hP => ?_⟩, hZproj⟩
  have hsub : r.base '' (P.support : Set Z) ⊆ (singularLocus sY : Set Y) := by
    rintro _ ⟨z, hz, rfl⟩
    have : z ∈ (F.supp : Set Z) :=
      DivisorWithCoeffs.support_subset_supp (Finsupp.mem_support_iff.1 hP) hz
    rw [hFex, hexc] at this
    exact this
  exact ((Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le).trans hSing

end CurvePointModel

/-- A point outside the cosupports of finitely many ideals is outside that of their product. -/
private theorem notMem_support_prod {X : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData) (x : X) (h : ∀ i ∈ s, x ∉ (I i).support) :
    x ∉ (∏ i ∈ s, I i).support := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
    exact id
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hx
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
      at hx
    rcases hx with hx | hx
    · exact h a (Finset.mem_insert_self a s) hx
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hx

/-- An ideal whose cosupport misses the generic point of an integral scheme is nonzero at the
generic points of the irreducible components. -/
private theorem isNonzeroAtGenericPoints_of_genericPoint_notMem {X : Scheme.{0}} [IsIntegral X]
    (I : X.IdealSheafData) (h : genericPoint X ∉ I.support) :
    MMP.Resolution.IsNonzeroAtGenericPoints I := by
  intro η hη
  have hcl : closure ({η} : Set X) = Set.univ := by
    rw [irreducibleComponents_eq_singleton] at hη
    exact hη
  have hη' : η = genericPoint X :=
    ((isGenericPoint_def.2 hcl).eq (genericPoint_spec X))
  rw [hη', (IdealSheafData.stalk_eq_top_iff_notMem_support I _).2 h]
  exact top_ne_bot

/-- A morphism of irreducible schemes which is an isomorphism over a nonempty open is
birational. -/
private theorem isBirationalMorphism_of_isIso_restrict {W V : Scheme.{0}} [IrreducibleSpace W]
    [IrreducibleSpace V] (f : W ⟶ V) (U : V.Opens) (hU : (U : Set V).Nonempty)
    [IsIso (f ∣_ U)] : MMP.Mori.IsBirationalMorphism f := by
  obtain ⟨y, hy⟩ := hU
  obtain ⟨x, -⟩ := (asIso (f ∣_ U)).hom.homeomorph.surjective ⟨y, hy⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE f (f ⁻¹ᵁ U) U ⟨x.1, x.2⟩ ⟨y, hy⟩ le_rfl ?_
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The double locus of an ordered divisor is closed. -/
private theorem isClosed_doubleLocus {X : Scheme.{0}} (E : MMP.Resolution.OrderedDivisor X) :
    IsClosed E.doubleLocus := by
  have e : E.doubleLocus = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j),
      ((E.E i).support : Set X) ∩ ((E.E j).support : Set X) := by
    ext x
    simp only [MMP.Resolution.OrderedDivisor.doubleLocus, Set.mem_setOf_eq, Set.mem_iUnion,
      Set.mem_inter_iff, exists_prop]
  rw [e]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => (E.E i).support.isClosed.inter (E.E j).support.isClosed

/-- The double locus lies in the support. -/
private theorem doubleLocus_subset_support {X : Scheme.{0}} (E : MMP.Resolution.OrderedDivisor X) :
    E.doubleLocus ⊆ E.support := fun _ ⟨i, _, _, hi, _⟩ => Set.mem_iUnion.2 ⟨i, hi⟩

/-- The support of a divisor is the union of the supports of its components. -/
private theorem coe_supp_eq_iUnion {X : Scheme.{0}} {R : Type*} [Zero R]
    (D : DivisorWithCoeffs R X) :
    (D.supp : Set X) = ⋃ P ∈ D.support, (P.support : Set X) := by
  ext x
  simp only [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff, Set.mem_iUnion,
    Finsupp.mem_support_iff, exists_prop]
  rfl

/-- The union of the components of an snc divisor with natural coefficients is an snc closed
subset. -/
private theorem isSNCClosedSubset_iUnion_of_isSNC {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (D : DivisorWithCoeffs ℕ X) (hD : D.IsSNC sX) :
    MMP.Resolution.IsSNCClosedSubset sX (⋃ P ∈ D.support, (P.support : Set X)) := by
  set T : Divisor X := Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero D with hT
  have hTs : T.support = D.support :=
    Finsupp.support_mapRange_of_injective _ _ Nat.cast_injective
  have hTsnc : T.IsSNC sX := hD.of_support_subset hTs.le
  have := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC sX hTsnc
  rwa [hTs] at this

/-- A divisor with simple normal crossings on a smooth Noetherian scheme over a perfect field is
the support of an ordered snc divisor, its irreducible components in some order. -/
private theorem exists_orderedDivisor_support_eq {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [IsNoetherian X]
    (hX : MMP.Mori.IsSmoothScheme sX) {D : Set X} (hD : MMP.Resolution.IsSNCClosedSubset sX D) :
    ∃ E : MMP.Resolution.OrderedDivisor X, E.support = D ∧ E.IsOrderedSNC sX := by
  obtain ⟨hDc, hD0 | ⟨-, hfin, hfam⟩⟩ := hD
  · refine ⟨MMP.Resolution.OrderedDivisor.empty X, ?_, ?_⟩
    · simp [MMP.Resolution.OrderedDivisor.support, MMP.Resolution.OrderedDivisor.empty, hD0]
    · haveI : LocallyOfFinitePresentation sX :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
      haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hX
      refine ⟨fun i => i.elim0, fun i => i.elim0, fun x => ?_⟩
      haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
        (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp
          inferInstance x
      obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
      exact ⟨n, z, fun i => i.1.elim0, hz, fun i => i.1.elim0, fun i => i.1.elim0⟩
  · haveI : Finite (MMP.Resolution.componentsOf D) := hfin.to_subtype
    let e := (Finite.equivFin (MMP.Resolution.componentsOf D)).symm
    refine ⟨⟨_, fun i => MMP.Resolution.componentsFamily D (e i)⟩, ?_, ?_⟩
    · change ⋃ i, ((MMP.Resolution.componentsFamily D (e i)).support : Set X) = D
      rw [e.surjective.iUnion_comp
        (fun V => ((MMP.Resolution.componentsFamily D V).support : Set X))]
      exact MMP.Resolution.iUnion_support_componentsFamily hDc
    · exact MMP.Resolution.isOrderedSNC_of_exists_rep hfam _
        fun y => ⟨e, e.injective, fun i hi => ⟨hi, rfl⟩⟩

/-- A point of the double locus of an snc ordered divisor has codimension at least two. -/
private theorem two_le_coheight_of_mem_doubleLocus {k : Type} [Field k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {E : MMP.Resolution.OrderedDivisor X} (hE : E.IsSNC sX) {x : X}
    (hx : x ∈ E.doubleLocus) : 2 ≤ Order.coheight x := by
  obtain ⟨i, j, hij, hi, hj⟩ := hx
  obtain ⟨n, z, c, hz, -, hc⟩ := hE.2 x
  have hne : (c ⟨i, hi⟩).val ≠ (c ⟨j, hj⟩).val := fun h =>
    hij (congrArg Subtype.val (hc (Fin.ext h)))
  have hn : 2 ≤ n := by
    have h1 := (c ⟨i, hi⟩).isLt
    have h2 := (c ⟨j, hj⟩).isLt
    omega
  have h := hz.2
  rw [ringKrullDim_stalk_eq_coheight] at h
  have h' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight x : WithBot ℕ∞) := by
    rw [h]; exact_mod_cast hn
  exact_mod_cast h'

/-- On an integral scheme, an ideal whose cosupport misses the generic point has nonzero
stalks. -/
private theorem stalk_ne_bot_of_genericPoint_notMem {X : Scheme.{0}} [IsIntegral X]
    (I : X.IdealSheafData) (h : genericPoint X ∉ I.support) (x : X) :
    IdealSheafData.stalk I x ≠ ⊥ := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  intro h0
  rw [IdealSheafData.stalk_eq_map_germ I x ⟨U, hU⟩ hxU] at h0
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hxU⟩
  have hI : I.ideal ⟨U, hU⟩ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have h1 : X.presheaf.germ U x hxU a = 0 := by
      rw [← Ideal.mem_bot, ← h0]; exact Ideal.mem_map_of_mem _ ha
    exact Ideal.mem_bot.2 (germ_injective_of_isIntegral X x hxU (h1.trans (map_zero _).symm))
  have h2 := (IdealSheafData.stalk_eq_top_iff_notMem_support I _).2 h
  rw [IdealSheafData.stalk_eq_map_germ I _ ⟨U, hU⟩ hgU, hI, Ideal.map_bot] at h2
  exact bot_ne_top h2

/-- **A factor of an invertible ideal is invertible.** On a scheme smooth over `ℂ`, a factor of
an ideal whose stalk is a nonzero principal ideal has principal stalk: the stalk is a regular local
ring, hence a unique factorization domain. -/
private theorem isPrincipal_stalk_of_mul {W : Scheme.{0}} (s : W ⟶ Spec (.of ℂ)) [Smooth s]
    (R A : W.IdealSheafData) (x : W) (h : (IdealSheafData.stalk (R * A) x).IsPrincipal)
    (hne : IdealSheafData.stalk (R * A) x ≠ ⊥) : (IdealSheafData.stalk A x).IsPrincipal := by
  rw [MMP.Resolution.Aux.stalk_mul, mul_comm] at h hne
  haveI : IsRegularLocalRing (W.presheaf.stalk x) :=
    (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk s).mp inferInstance x
  haveI := IsRegularLocalRing.isDomain (W.presheaf.stalk x)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (W.presheaf.stalk x)
  haveI := instIsGCDMonoidOfUniqueFactorizationMonoid (W.presheaf.stalk x)
  exact IsGCDMonoid.isPrincipal_of_exists_mul_ne_zero_isPrincipal ⟨_, hne, h⟩

/-- A projective resolution of a normal variety is biregular at every point of codimension at
most one. -/
private theorem mem_biregularLocus_of_coheight_le_one {X W : Scheme.{0}} [IsIntegral X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {f : W ⟶ X} (hres : MMP.Intersection.IsResolution sX f)
    {x : X} (hx : Order.coheight x ≤ 1) : x ∈ biregularLocus f := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hres.2.2.2.1
  exact MMP.Mori.mem_biregularLocus_of_ringKrullDim_stalk_le_one ⟨hres.1, inferInstance⟩ f
    hres.2.1 hres.2.2.2.2 (by rw [ringKrullDim_stalk_eq_coheight]; exact_mod_cast hx)

/-- A projective resolution of a normal variety is biregular at its generic point. -/
private theorem genericPoint_mem_biregularLocus {X W : Scheme.{0}} [IsIntegral X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {f : W ⟶ X} (hres : MMP.Intersection.IsResolution sX f) :
    genericPoint X ∈ biregularLocus f :=
  mem_biregularLocus_of_coheight_le_one hres <| by
    rw [Order.coheight_eq_zero.2 fun z _ =>
      Scheme.le_iff_specializes.2 (genericPoint_specializes z)]
    exact zero_le_one

/-- **The exceptional locus of the second principalization.** Let `f₀ : W₀ ⟶ S` be a projective
resolution of a normal variety, `E` an snc divisor on `W₀`, and `I` an ideal on `S` with the
cosupport of the non-biregular locus of `f₀` over the biregular locus. Let `r : W ⟶ W₀` be an
isomorphism off `V(J) ∪ E^{(2)}`, where `J = I 𝒪_{W₀} · 𝓘(E^{(2)})`, and let `J 𝒪_W` have
cosupport the union of the prime divisors whose generic points map into `V(J)`. Then the
exceptional locus of `r ≫ f₀` is exactly `V(J 𝒪_W)`: points of `S` of codimension at most one are
biregular, and the double locus of `E` has codimension at least two. -/
private theorem exceptionalSet_comp_eq_support_comap {k : Type} [Field k] {S W₀ W : Scheme.{0}}
    [IsIntegral S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} {f₀ : W₀ ⟶ S}
    (hf₀ : MMP.Intersection.IsResolution sS f₀) {s : W₀ ⟶ Spec (.of k)}
    {E : MMP.Resolution.OrderedDivisor W₀} (hE : E.IsSNC s) {I : S.IdealSheafData}
    (hKI : (Scheme.IdealSheafData.vanishingIdeal (biregularLocus f₀).compl).support ≤ I.support)
    (hIbir : ∀ y ∈ biregularLocus f₀,
      y ∉ (Scheme.IdealSheafData.vanishingIdeal (biregularLocus f₀).compl).support →
        y ∉ I.support)
    (r : W ⟶ W₀) (hr : ∀ U : W₀.Opens, Disjoint (U : Set W₀)
      (((I.comap f₀ * Scheme.IdealSheafData.vanishingIdeal
        ⟨E.doubleLocus, isClosed_doubleLocus E⟩).support : Set W₀) ∪ E.doubleLocus) →
          IsIso (r ∣_ U))
    {DJ : DivisorWithCoeffs ℕ W}
    (hDJ : ∀ P : MMP.Mori.PrimeDivisor W, P ∈ DJ.support ↔ r P.genericPoint ∈
      (I.comap f₀ * Scheme.IdealSheafData.vanishingIdeal
        ⟨E.doubleLocus, isClosed_doubleLocus E⟩).support)
    (hsupp : (((I.comap f₀ * Scheme.IdealSheafData.vanishingIdeal
        ⟨E.doubleLocus, isClosed_doubleLocus E⟩).comap r).support : Set W) =
      ⋃ P ∈ DJ.support, (P.idealSheaf.support : Set W)) :
    (exceptionalSet (r ≫ f₀) : Set W) = ((I.comap f₀ * Scheme.IdealSheafData.vanishingIdeal
        ⟨E.doubleLocus, isClosed_doubleLocus E⟩).comap r).support := by
  set J := I.comap f₀ * Scheme.IdealSheafData.vanishingIdeal ⟨E.doubleLocus, isClosed_doubleLocus E⟩
  haveI : IsProper f₀ := isProper_of_isProjectiveMorphism _ hf₀.2.2.2.1
  have hK : ∀ x : S, x ∈ (Scheme.IdealSheafData.vanishingIdeal
      (biregularLocus f₀).compl).support ↔ x ∉ biregularLocus f₀ := fun x => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hJ : ∀ y : W₀, y ∈ J.support ↔ f₀ y ∈ (I.support : Set S) ∨ y ∈ E.doubleLocus :=
    fun y => by
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_mul,
        TopologicalSpace.Closeds.coe_sup, Set.mem_union, Scheme.IdealSheafData.support_comap,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
  apply le_antisymm
  · have hsub := MMP.Fourfold.SNCWeight.SNCModel.exceptionalSet_comp_subset f₀ r
      ⟨(J.support : Set W₀) ∪ E.doubleLocus, J.support.isClosed.union (isClosed_doubleLocus E)⟩
      (hr _ disjoint_compl_left) (B := (J.support : Set W₀))
      (fun y hy => (hJ y).2 (Or.inl (hKI ((hK _).2 ((mem_exceptionalSet).1 hy)))))
      (fun y hy => hy.elim id fun h => (hJ y).2 (Or.inr h))
    intro z hz
    rw [Scheme.IdealSheafData.support_comap]
    exact hsub hz
  · rw [hsupp]
    refine Set.iUnion₂_subset fun P hP => ?_
    change (P.support : Set W) ⊆ _
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal (Set.singleton_subset_iff.2 ?_) (exceptionalSet _).isClosed
    rw [SetLike.mem_coe, mem_exceptionalSet]
    intro hb
    have h1 : Order.coheight (f₀ (r P.genericPoint)) = 1 := by
      have := MMP.Positivity.coheight_map_of_mem_biregularLocus _ hb
      rw [Scheme.Hom.comp_apply] at this
      rw [this, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    have hbf := mem_biregularLocus_of_coheight_le_one hf₀ h1.le
    rcases (hJ _).1 ((hDJ P).1 hP) with h | h
    · exact hIbir _ hbf (fun h' => (hK _).1 h' hbf) h
    · have h2 := two_le_coheight_of_mem_doubleLocus hE h
      rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f₀ hbf, h1] at h2
      exact absurd h2 (by decide)

/-- **The construction.** The model `r₀`, the blow-ups `q` and every geometric clause, together
with the projectivity of `Z₀`, its complex structure and the blow-up closure property of `q`
used for the defect transfer. -/
private theorem exists_model
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {p : Y ⟶ X}
    (hpX : p ≫ sX = sY)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 4)
    (hp : IsProjectiveMorphism p ∧ MMP.Mori.IsBirationalMorphism p)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQf : IsQFactorial sY)
    (hdimY : topologicalKrullDim Y = 4) (hYt : IsTerminalVariety sY)
    {Q : Divisor Y} (hQ : MMP.Intersection.IsReducedEffective Q)
    (𝒱 : Set (IrreducibleCloseds Y)) (h𝒱 : 𝒱.Finite) :
    ∃ (Z₀ : Scheme.{0}) (_ : Z₀.Over (Spec (.of ℂ))) (_ : IsComplexScheme Z₀)
      (_ : CompactSpace Z₀) (_ : IsLocallyNoetherian Z₀) (_ : IsNormal Z₀) (r₀ : Z₀ ⟶ Y)
      (F₀ D₀ : Divisor Z₀),
      IsCurvePointExceptionalModel sY r₀ F₀ D₀ ∧ IsProjective (Z₀ ↘ Spec (.of ℂ)) ∧
      ∃ B : MMP.Resolution.ClosedBlowupSequence Z₀,
        B.IsSmooth (Z₀ ↘ Spec (.of ℂ)) ∧
        B.CentersHaveSNCWith (Z₀ ↘ Spec (.of ℂ)) (F₀.supp : Set Z₀) ∧
      ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of ℂ))) (_ : IsComplexScheme Z) (_ : CompactSpace Z)
        (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (q : Z ⟶ Z₀) (e : Z ≅ B.target),
        q = e.hom ≫ B.toBase ∧
        q ≫ r₀ ≫ sY = Z ↘ Spec (.of ℂ) ∧
        MMP.Intersection.IsResolution sY (q ≫ r₀) ∧
        MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ))
          ((q ≫ r₀).base ⁻¹' (Q.supp : Set Y) ∪ exceptionalSet (q ≫ r₀)) ∧
        MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) (exceptionalSet (q ≫ r₀ ≫ p)) ∧
        (∃ D : Divisor Z, (∀ P, 0 ≤ D.coeff P) ∧
          (D.supp : Set Z) = exceptionalSet (q ≫ r₀ ≫ p) ∧
          ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (q ≫ r₀ ≫ p) h) ∧
        (∀ V ∈ 𝒱, ∀ z : Z,
          (AlgebraicGeometry.IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal
            ⟨(V : Set Y), V.isClosed⟩).comap (q ≫ r₀)) z).IsPrincipal) ∧
        IsBoundaryBlowup r₀ q := by
  classical
  obtain ⟨Z₀, i₀, _, _, _, r₀, F₀, D₀, hM, hZ₀p⟩ :=
    exists_isCurvePointExceptionalModel hY hQf hdimY hYt
  obtain ⟨hYv, hYproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sY).1 hY
  obtain ⟨hXv, hXproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sX).1 hX
  haveI : IsIntegral X := hXv.toIsIntegral
  have hYqp : IsQuasiProjectiveVariety ℂ sY := (isQuasiProjectiveVariety_iff ℂ _).2
    ⟨hYv, Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sY hYproj.isHQuasiProjective⟩
  have hXqp : IsQuasiProjectiveVariety ℂ sX := (isQuasiProjectiveVariety_iff ℂ _).2
    ⟨hXv, Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective sX hXproj.isHQuasiProjective⟩
  have hres₀ := hM.isResolution
  have hcomp₀ : r₀ ≫ sY = Z₀ ↘ Spec (.of ℂ) := hM.comp_eq
  -- the boundary `F₀` as an ordered divisor
  haveI : LocallyOfFiniteType (r₀ ≫ sY) := hres₀.2.1.toLocallyOfFiniteType
  haveI : QuasiCompact (r₀ ≫ sY) := hres₀.2.1.toQuasiCompact
  haveI : IsNoetherian Z₀ := ⟨⟩
  have hF₀snc : MMP.Resolution.IsSNCClosedSubset (r₀ ≫ sY) (F₀.supp : Set Z₀) := by
    have h := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC (r₀ ≫ sY)
      hM.isSNC
    rwa [← coe_supp_eq_iUnion] at h
  obtain ⟨E₀, hE₀s, hE₀⟩ := exists_orderedDivisor_support_eq (r₀ ≫ sY) hres₀.2.2.1 hF₀snc
  -- the ideal principalized on `Z₀`
  set T : Finset (IrreducibleCloseds Y) :=
    h𝒱.toFinset.filter fun V => (V : Set Y) ≠ Set.univ with hTdef
  set IQ : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Q.supp with hIQdef
  set IV : IrreducibleCloseds Y → Y.IdealSheafData := fun V =>
    Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Y), V.isClosed⟩ with hIVdef
  set Ma : Z₀.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal F₀.supp * IQ.comap r₀ * ∏ V ∈ T, (IV V).comap r₀
    with hMadef
  have hgen₀ : genericPoint Y ∈ biregularLocus r₀ := genericPoint_mem_biregularLocus hres₀
  haveI : IsIntegral Z₀ := hres₀.2.1.toIsIntegral
  haveI : IsDominant r₀ := hres₀.2.2.2.2.isDominant
  have hr₀gen : r₀ (genericPoint Z₀) = genericPoint Y := map_genericPoint_of_isDominant r₀
  have hgenMa : genericPoint Z₀ ∉ Ma.support := by
    intro h
    rw [hMadef, ← SetLike.mem_coe, Scheme.IdealSheafData.support_mul,
      Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup,
      TopologicalSpace.Closeds.coe_sup] at h
    rcases h with (h | h) | h
    · rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
      exact MMP.Fourfold.genericPoint_notMem_supp F₀ h
    · rw [Scheme.IdealSheafData.support_comap] at h
      change r₀ (genericPoint Z₀) ∈ (IQ.support : Set Y) at h
      rw [hr₀gen, hIQdef, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
      exact MMP.Fourfold.genericPoint_notMem_supp Q h
    · refine notMem_support_prod T _ _ (fun V hV hV' => ?_) h
      rw [Scheme.IdealSheafData.support_comap] at hV'
      change r₀ (genericPoint Z₀) ∈ ((IV V).support : Set Y) at hV'
      rw [hr₀gen, hIVdef, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hV'
      refine (Finset.mem_filter.1 hV).2 (Set.eq_univ_of_univ_subset ?_)
      rw [← (genericPoint_spec Y).def]
      exact closure_minimal (Set.singleton_subset_iff.2 hV') V.isClosed
  have hMa : MMP.Resolution.IsNonzeroAtGenericPoints Ma :=
    isNonzeroAtGenericPoints_of_genericPoint_notMem Ma hgenMa
  -- stage A: principalization over `Y`
  obtain ⟨Ia, -, -, hIabir, Ba, hBas, hBac, hBal, hBam, _, _, _, hresa, hqpa, hBap, hBaiso, -,
      DJa, hDJasnc, hDJamem, hsuppJa, -⟩ :=
    MMP.Fourfold.exists_principalization_isRelativelyAmple_neg hYqp hres₀ hgen₀ ⊤
      (by rw [Scheme.IdealSheafData.support_top]; exact id) Ma
      hMa E₀ hE₀
  set Ja : Z₀.IdealSheafData := Ia.comap r₀ * Ma with hJadef
  haveI : IsIntegral Ba.target := hresa.2.1.toIsIntegral
  have hgenJa : genericPoint Z₀ ∉ Ja.support := by
    intro h
    rw [hJadef, ← SetLike.mem_coe, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup] at h
    rcases h with h | h
    · rw [Scheme.IdealSheafData.support_comap] at h
      change r₀ (genericPoint Z₀) ∈ (Ia.support : Set Y) at h
      rw [hr₀gen] at h
      exact hIabir _ hgen₀ (by rw [Scheme.IdealSheafData.support_top]; exact id) h
    · exact hgenMa h
  have hdbl₀ : genericPoint Z₀ ∉ E₀.doubleLocus := fun h => by
    have h' := doubleLocus_subset_support E₀ h
    rw [hE₀s] at h'
    exact MMP.Fourfold.genericPoint_notMem_supp F₀ h'
  set Ua : Z₀.Opens := ⟨((Ja.support : Set Z₀) ∪ E₀.doubleLocus)ᶜ,
    (Ja.support.isClosed.union (isClosed_doubleLocus E₀)).isOpen_compl⟩ with hUadef
  haveI : IsIso (Ba.toBase ∣_ Ua) := hBaiso Ua disjoint_compl_left
  have hBabir : MMP.Mori.IsBirationalMorphism Ba.toBase :=
    isBirationalMorphism_of_isIso_restrict _ Ua
      ⟨genericPoint Z₀, fun h => h.elim hgenJa hdbl₀⟩
  haveI : IsDominant Ba.toBase := hBabir.isDominant
  have hBagen : Ba.toBase (genericPoint Ba.target) = genericPoint Z₀ :=
    map_genericPoint_of_isDominant _
  -- stage B: the antiample principalization over `X`
  set fa : Ba.target ⟶ X := Ba.toBase ≫ r₀ ≫ p with hfadef
  have hresfa : MMP.Intersection.IsResolution sX fa := by
    refine ⟨hXv, ?_, ?_, ?_, ?_⟩
    · rw [hfadef, Category.assoc, Category.assoc, hpX]
      simpa only [Category.assoc] using hresa.2.1
    · rw [hfadef, Category.assoc, Category.assoc, hpX]
      simpa only [Category.assoc] using hresa.2.2.1
    · rw [hfadef, ← Category.assoc]
      exact hresa.2.2.2.1.comp hp.1
    · rw [hfadef, ← Category.assoc]
      exact isBirationalMorphism_comp hresa.2.2.2.2 hp.2
  have hgenfa : genericPoint X ∈ biregularLocus fa := genericPoint_mem_biregularLocus hresfa
  have hfas' : fa ≫ sX = Ba.toBase ≫ r₀ ≫ sY := by
    rw [hfadef, Category.assoc, Category.assoc, hpX]
  haveI : LocallyOfFiniteType (fa ≫ sX) := hresfa.2.1.toLocallyOfFiniteType
  haveI : QuasiCompact (fa ≫ sX) := hresfa.2.1.toQuasiCompact
  haveI : IsNoetherian Ba.target := ⟨⟩
  have hJaSNC : MMP.Resolution.IsSNCClosedSubset (fa ≫ sX)
      ((Ja.comap Ba.toBase).support : Set Ba.target) := by
    have h := isSNCClosedSubset_iUnion_of_isSNC (fa ≫ sX) DJa (by rw [hfas']; exact hDJasnc)
    rwa [← show ((Ja.comap Ba.toBase).support : Set Ba.target) =
      ⋃ P ∈ DJa.support, (P.support : Set Ba.target) from hsuppJa] at h
  obtain ⟨Eb, hEbs, hEb⟩ := exists_orderedDivisor_support_eq (fa ≫ sX) hresfa.2.2.1 hJaSNC
  have hEbd : IsClosed Eb.doubleLocus := isClosed_doubleLocus Eb
  set Kb : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (biregularLocus fa).compl with hKbdef
  have hKb : genericPoint X ∉ Kb.support := by
    rw [← SetLike.mem_coe, hKbdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact fun h => h hgenfa
  set Mb : Ba.target.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨Eb.doubleLocus, hEbd⟩ with hMbdef
  have hgenEb : genericPoint Ba.target ∉ Eb.support := by
    rw [hEbs, Scheme.IdealSheafData.support_comap]
    intro h
    change Ba.toBase (genericPoint Ba.target) ∈ (Ja.support : Set Z₀) at h
    rw [hBagen] at h
    exact hgenJa h
  have hgenMb : genericPoint Ba.target ∉ Mb.support := by
    rw [← SetLike.mem_coe, hMbdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact fun h => hgenEb (doubleLocus_subset_support Eb h)
  have hMb : MMP.Resolution.IsNonzeroAtGenericPoints Mb :=
    isNonzeroAtGenericPoints_of_genericPoint_notMem Mb hgenMb
  obtain ⟨Ib, -, hKIb, hIbbir, Bb, hBbs, hBbc, hBbl, hBbm, _, _, _, hresb, hqpb, hBbp, hBbiso,
      hcartb, DJb, hDJbsnc, hDJbmem, hsuppJb, Db, hDbpos, hDbout, hDbc, hDbamp⟩ :=
    MMP.Fourfold.exists_principalization_isRelativelyAmple_neg hXqp hresfa hgenfa Kb hKb Mb hMb
      Eb hEb
  set Jb : Ba.target.IdealSheafData := Ib.comap fa * Mb with hJbdef
  haveI : IsIntegral Bb.target := hresb.2.1.toIsIntegral
  have hgenJb : genericPoint Ba.target ∉ Jb.support := by
    intro h
    rw [hJbdef, ← SetLike.mem_coe, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup] at h
    rcases h with h | h
    · rw [Scheme.IdealSheafData.support_comap] at h
      haveI : IsDominant fa := hresfa.2.2.2.2.isDominant
      change fa (genericPoint Ba.target) ∈ (Ib.support : Set X) at h
      rw [map_genericPoint_of_isDominant] at h
      exact hIbbir _ hgenfa hKb h
    · exact hgenMb h
  have hdblb : genericPoint Ba.target ∉ Eb.doubleLocus := fun h =>
    hgenEb (doubleLocus_subset_support Eb h)
  set Ub : Ba.target.Opens := ⟨((Jb.support : Set Ba.target) ∪ Eb.doubleLocus)ᶜ,
    (Jb.support.isClosed.union (isClosed_doubleLocus Eb)).isOpen_compl⟩ with hUbdef
  haveI : IsIso (Bb.toBase ∣_ Ub) := hBbiso Ub disjoint_compl_left
  have hBbbir : MMP.Mori.IsBirationalMorphism Bb.toBase :=
    isBirationalMorphism_of_isIso_restrict _ Ub
      ⟨genericPoint Ba.target, fun h => h.elim hgenJb hdblb⟩
  haveI : IsDominant Bb.toBase := hBbbir.isDominant
  have hfas : fa ≫ sX = Ba.toBase ≫ Z₀ ↘ Spec (.of ℂ) := by
    rw [hfadef, Category.assoc, Category.assoc, hpX, hcomp₀]
  -- the exceptional locus over `X`
  have hJbmem : ∀ y : Ba.target, y ∈ Eb.doubleLocus → y ∈ Jb.support := fun y hy => by
    rw [hJbdef, ← SetLike.mem_coe, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, hMbdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Or.inr hy
  have hExb : (exceptionalSet (Bb.toBase ≫ fa) : Set Bb.target) =
      ((Jb.comap Bb.toBase).support : Set Bb.target) :=
    exceptionalSet_comp_eq_support_comap hresfa hEb.2 hKIb hIbbir Bb.toBase hBbiso hDJbmem hsuppJb
  have hDbsupp : ∀ P, Db.coeff P ≠ 0 ↔ P ∈ DJb.support := fun P => by
    refine ⟨fun h => by_contra fun hP => ?_, fun hP => (hDbpos P hP).ne'⟩
    exact hP ((hDJbmem P).2 (hJbmem _ (hDbout P hP h)))
  have hDbset : (Db.supp : Set Bb.target) = exceptionalSet (Bb.toBase ≫ fa) := by
    rw [hExb, hsuppJb, coe_supp_eq_iUnion]
    ext z
    simp only [Set.mem_iUnion, Finsupp.mem_support_iff, exists_prop]
    exact ⟨fun ⟨P, hP, hz⟩ => ⟨P, Finsupp.mem_support_iff.1 ((hDbsupp P).1 hP), hz⟩,
      fun ⟨P, hP, hz⟩ => ⟨P, (hDbsupp P).2 (Finsupp.mem_support_iff.2 hP), hz⟩⟩
  -- the composite blow-up sequence
  obtain ⟨e', he', hBto⟩ := MMP.Resolution.ClosedBlowupSequence.exists_isIso_append_toBase Ba Bb
  haveI := he'
  set q : Bb.target ⟶ Z₀ := Bb.toBase ≫ Ba.toBase with hqdef
  letI iZ : Bb.target.Over (Spec (.of ℂ)) := ⟨q ≫ Z₀ ↘ Spec (.of ℂ)⟩
  have hqc : q ≫ r₀ ≫ sY = Bb.target ↘ Spec (.of ℂ) := by rw [hcomp₀]; rfl
  have hqf : q ≫ r₀ ≫ p = Bb.toBase ≫ fa := by
    rw [hqdef, hfadef]; simp only [Category.assoc]
  have hZ₀proj : AlgebraicGeometry.IsProjectiveVariety ℂ (Z₀ ↘ Spec (.of ℂ)) := by
    rw [← hcomp₀]; exact hZ₀p
  have hZs : (Bb.toBase ≫ fa) ≫ sX = Bb.target ↘ Spec (.of ℂ) := by
    rw [Category.assoc, hfas]; rfl
  have hZv : AlgebraicGeometry.IsVariety ℂ (Bb.target ↘ Spec (.of ℂ)) := by
    rw [← hZs]; exact hresb.2.1
  have hZproj : AlgebraicGeometry.IsProjectiveVariety ℂ (Bb.target ↘ Spec (.of ℂ)) := by
    haveI := hZv
    refine ⟨?_⟩
    change IsProjectiveMorphism ((Bb.toBase ≫ Ba.toBase) ≫ Z₀ ↘ Spec (.of ℂ))
    rw [Category.assoc]
    exact hBbp.comp (hBap.comp hZ₀proj.isProjective)
  have hqres : MMP.Intersection.IsResolution sY (q ≫ r₀) := by
    refine ⟨hYv, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, hqc]; exact hZv
    · rw [Category.assoc, hqc, ← hZs]; exact hresb.2.2.1
    · rw [hqdef, Category.assoc]; exact hBbp.comp hresa.2.2.2.1
    · rw [hqdef, Category.assoc]; exact isBirationalMorphism_comp hBbbir hresa.2.2.2.2
  -- the boundary: `F₀` and `r₀⁻¹ Q` lie in `V(Ja)`, the total transform of `F₀` in `Eb`
  have hJamem : ∀ x : Z₀, x ∈ Ja.support ↔ (r₀ x ∈ (Ia.support : Set Y) ∨
      (x ∈ (F₀.supp : Set Z₀) ∨ r₀ x ∈ (Q.supp : Set Y)) ∨ x ∈ ((∏ V ∈ T, (IV V).comap r₀).support :
        Set Z₀)) := fun x => by
    rw [hJadef, hMadef, ← SetLike.mem_coe, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, Scheme.IdealSheafData.support_mul,
      TopologicalSpace.Closeds.coe_sup, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simp only [Set.mem_union]
    rw [hIQdef]
    change _ ∨ (_ ∨ r₀ x ∈ ((Scheme.IdealSheafData.vanishingIdeal Q.supp).support : Set Y)) ∨ _ ↔ _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hF₀Ja : (F₀.supp : Set Z₀) ⊆ Ja.support := fun x hx =>
    (hJamem x).2 (Or.inr (Or.inl (Or.inl hx)))
  have hQJa : r₀.base ⁻¹' (Q.supp : Set Y) ⊆ Ja.support := fun x hx =>
    (hJamem x).2 (Or.inr (Or.inl (Or.inr hx)))
  have hTTa : Ba.totalTransform (F₀.supp : Set Z₀) ⊆ Eb.support := by
    intro x hx
    have := totalTransform_subset_preimage Ba (𝟙 Z₀) _ _ F₀.supp.isClosed hBal hx
    rw [hEbs, Scheme.IdealSheafData.support_comap]
    change Ba.toBase x ∈ (Ja.support : Set Z₀)
    rcases this with h | h | h
    · exact hF₀Ja h
    · exact h
    · have h' := doubleLocus_subset_support E₀ h
      rw [hE₀s] at h'
      exact hF₀Ja h'
  have hTTasnc : MMP.Resolution.IsSNCClosedSubset (Ba.toBase ≫ r₀ ≫ sY)
      (Ba.totalTransform (F₀.supp : Set Z₀)) :=
    MMP.Resolution.ClosedBlowupSequence.isSNCClosedSubset_totalTransform (r₀ ≫ sY)
      hres₀.2.2.1 hF₀snc Ba hBas (hE₀s ▸ hBac)
  have hEbsnc : MMP.Resolution.IsSNCClosedSubset (fa ≫ sX) Eb.support := hEbs ▸ hJaSNC
  have hBbc' : Bb.CentersHaveSNCWith (fa ≫ sX) (Ba.totalTransform (F₀.supp : Set Z₀)) :=
    centersHaveSNCWith_of_componentsOf_subset Bb (fa ≫ sX) _ _
      (MMP.Resolution.ClosedBlowupSequence.isClosed_totalTransform Ba F₀.supp.isClosed)
      (componentsOf_subset_of_isSNCClosedSubset hTTasnc hEbsnc hTTa) hBbs hBbc
  -- ample invertible sheaves on `Z₀` and `Ba.target`
  have hamp₀ : ∃ (M : Z₀.Modules) (_ : Stacks.Ample.IsInvertibleModule Z₀ M),
      Stacks.Ample.IsAmple Z₀ M :=
    exists_isAmple_of_isProjectiveMorphism (Z₀ ↘ Spec (.of ℂ)) _
      (Stacks.Ample.isAmple_unitModule_of_isAffine _) hZ₀proj.isProjective
  have hampa : ∃ (M : Ba.target.Modules) (_ : Stacks.Ample.IsInvertibleModule Ba.target M),
      Stacks.Ample.IsAmple Ba.target M :=
    exists_isAmple_of_isProjectiveMorphism (Ba.toBase ≫ Z₀ ↘ Spec (.of ℂ)) _
      (Stacks.Ample.isAmple_unitModule_of_isAffine _) (hBap.comp hZ₀proj.isProjective)
  -- the two stages of blow-ups, along any blow-up closed property
  have hstages : ∀ (P : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z₀) → Prop), P (𝟙 Z₀) →
      (∀ ⦃W : Scheme.{0}⦄ (p : W ⟶ Z₀) (I : W.IdealSheafData), P p →
        MMP.Mori.IsSmoothScheme (I.subschemeι ≫ p ≫ (Z₀ ↘ Spec (.of ℂ))) →
        MMP.Resolution.HasSNCWith
          (MMP.Resolution.componentsFamily (exceptionalSet (p ≫ r₀) : Set W)) I →
        P (blowUpToBase I ≫ p)) →
      P q ∧ (exceptionalSet (q ≫ r₀) : Set Bb.target) ⊆ Bb.totalTransform Eb.support := by
    intro P h0 hstep
    obtain ⟨hPa, hExa⟩ := toBase_comp_of_isSmooth hQf r₀ hcomp₀ P hstep Ba (𝟙 Z₀)
      (F₀.supp : Set Z₀) (𝟙 Z₀) ((Ja.support : Set Z₀) ∪ E₀.doubleLocus) h0
      (by rw [Category.id_comp, ← hcomp₀]; exact hres₀.2.1)
      (by rw [Category.id_comp]; exact hres₀.2.2.2.1)
      (by rw [Category.id_comp]; exact hres₀.2.2.2.2) hamp₀
      (by rw [Category.id_comp]; exact hM.supp_eq_exceptionalSet.symm.le)
      (by rw [Category.id_comp, ← hcomp₀]; exact hBas)
      (by rw [Category.id_comp, ← hcomp₀, ← hE₀s]; exact hBac) hBal
      (fun h => h.elim hgenJa hdbl₀)
    rw [Category.comp_id] at hPa
    rw [Category.id_comp] at hExa
    obtain ⟨hPb, hExb'⟩ := toBase_comp_of_isSmooth hQf r₀ hcomp₀ P hstep Bb Ba.toBase
      Eb.support (𝟙 Ba.target) ((Jb.support : Set Ba.target) ∪ Eb.doubleLocus) hPa
      (by rw [← hcomp₀, ← Category.assoc]; exact hresa.2.1)
      hresa.2.2.2.1 hresa.2.2.2.2 hampa (hExa.trans hTTa)
      (by rw [← hfas]; exact hBbs) (by rw [← hfas]; exact hBbc) hBbl
      (fun h => h.elim hgenJb hdblb)
    refine ⟨hPb, ?_⟩
    rw [hqdef, Category.assoc]
    exact hExb'
  -- a factor of `Ja` becomes invertible on `Ba.target`
  haveI : Smooth (Ba.toBase ≫ r₀ ≫ sY) := MMP.Resolution.Aux.smooth_of_isSmoothScheme' _
    (by simpa only [Category.assoc] using hresa.2.2.1)
  have hfactor : ∀ A R : Z₀.IdealSheafData, Ja = R * A → ∀ z' : Ba.target,
      (IdealSheafData.stalk (A.comap Ba.toBase) z').IsPrincipal := by
    intro A R hJ z'
    obtain ⟨n, zz, c, hz, hstalk⟩ := hBam z'
    have hne := stalk_ne_bot_of_genericPoint_notMem (Ja.comap Ba.toBase)
      (fun h => hgenEb (by rw [hEbs]; exact h)) z'
    change IdealSheafData.stalk (Ja.comap Ba.toBase) z' = _ at hstalk
    rw [hJ, Stacks.IdealSheaf.comap_mul] at hstalk hne
    exact isPrincipal_stalk_of_mul (Ba.toBase ≫ r₀ ≫ sY) _ _ z'
      (by rw [hstalk]; exact ⟨⟨_, rfl⟩⟩) hne
  refine ⟨Z₀, i₀, MMP.Fourfold.isComplexScheme_of_isProjectiveVariety Z₀ hZ₀proj, inferInstance,
    inferInstance, inferInstance, r₀, F₀, D₀, hM, hZ₀proj.isProjective.isProjective, Ba.append Bb,
    MMP.Resolution.ClosedBlowupSequence.isSmooth_append _ Ba Bb (hcomp₀ ▸ hBas) (hfas ▸ hBbs),
    MMP.Resolution.ClosedBlowupSequence.centersHaveSNCWith_append _ Ba Bb _
      (by rw [← hcomp₀, ← hE₀s]; exact hBac) (by rw [← hfas]; exact hBbc'), Bb.target, iZ,
    MMP.Fourfold.isComplexScheme_of_isProjectiveVariety _ hZproj, inferInstance, inferInstance,
    inferInstance, q, (asIso e').symm, ?_, hqc, hqres, ?_, ?_, ?_, ?_,
    fun P h0 hstep => (hstages P h0 hstep).1⟩
  rotate_left
  · -- `r⁻¹ Q ∪ Ex(r)` lies in the snc total transform of `Eb`
    have hSfin := MMP.Resolution.ClosedBlowupSequence.isSNCClosedSubset_totalTransform (fa ≫ sX)
      hresfa.2.2.1 hEbsnc Bb hBbs hBbc
    rw [← Category.assoc, hZs] at hSfin
    have hExq := (hstages (fun _ _ => True) trivial (fun _ _ _ _ _ _ => trivial)).2
    set IQz : Bb.target.IdealSheafData := IQ.comap (q ≫ r₀) with hIQzdef
    have hQz : (q ≫ r₀).base ⁻¹' (Q.supp : Set Y) = (IQz.support : Set Bb.target) := by
      rw [hIQzdef, Scheme.IdealSheafData.support_comap, hIQdef]
      change _ = (q ≫ r₀).base ⁻¹'
        ((Scheme.IdealSheafData.vanishingIdeal Q.supp).support : Set Y)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    have hQsub : (q ≫ r₀).base ⁻¹' (Q.supp : Set Y) ⊆ Bb.totalTransform Eb.support := by
      intro x hx
      apply preimage_subset_totalTransform Bb Eb.support
      change Bb.toBase x ∈ Eb.support
      rw [hEbs, Scheme.IdealSheafData.support_comap]
      exact hQJa hx
    haveI : IsDominant (q ≫ r₀) := hqres.2.2.2.2.isDominant
    have hgenQz : genericPoint Bb.target ∉ IQz.support := by
      rw [← SetLike.mem_coe, ← hQz]
      change (q ≫ r₀) (genericPoint Bb.target) ∉ (Q.supp : Set Y)
      rw [map_genericPoint_of_isDominant]
      exact MMP.Fourfold.genericPoint_notMem_supp Q
    have hJQ : Ja = (Ia.comap r₀ * (Scheme.IdealSheafData.vanishingIdeal F₀.supp *
        ∏ V ∈ T, (IV V).comap r₀)) * IQ.comap r₀ := by
      rw [hJadef, hMadef]
      ac_rfl
    have hQcart : Stacks.Divisors.IsEffectiveCartierDivisor IQz :=
      Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor IQz
        fun x _ => by
          have hpr : (IdealSheafData.stalk IQz x).IsPrincipal := by
            rw [hIQzdef, hqdef, Category.assoc, Scheme.IdealSheafData.comap_comp,
              Scheme.IdealSheafData.comap_comp, IdealSheafData.stalk_comap]
            exact (hfactor _ _ hJQ (Bb.toBase x)).map_ringHom _
          obtain ⟨g, hg⟩ := hpr
          have hne := stalk_ne_bot_of_genericPoint_notMem IQz hgenQz x
          refine ⟨g, mem_nonZeroDivisors_of_ne_zero ?_, hg⟩
          rintro rfl
          apply hne
          rw [hg]
          exact Submodule.span_zero_singleton _
    have hQpure := isPureCodimOne_support_of_isEffectiveCartierDivisor IQz hQcart hgenQz
    have hExpure := MMP.Mori.isPureCodimOne_exceptionalSet_of_isQFactorial sY ((q ≫ r₀) ≫ sY)
      hQf hqres.2.1 (q ≫ r₀) rfl hqres.2.2.2.1 hqres.2.2.2.2
    have hTpure := isPureCodimOne_union IQz.support.isClosed (exceptionalSet (q ≫ r₀)).isClosed
      hQpure hExpure
    rw [hQz]
    have hTsub : (IQz.support : Set Bb.target) ∪ exceptionalSet (q ≫ r₀) ⊆
        Bb.totalTransform Eb.support := Set.union_subset (hQz ▸ hQsub) hExq
    exact isSNCClosedSubset_of_componentsOf_subset hSfin
      (IQz.support.isClosed.union (exceptionalSet _).isClosed)
      (componentsOf_subset_of_isSNCClosedSubset_right _ hTpure hSfin hTsub)
  · rw [hqf, hExb, hsuppJb]
    refine isSNCClosedSubset_iUnion_of_isSNC _ DJb ?_
    rw [← hZs, Category.assoc]
    exact hDJbsnc
  · refine ⟨Db, fun P => ?_, by rw [hqf]; exact hDbset, hqf ▸ ⟨hDbc, hDbamp⟩⟩
    by_cases hP : P ∈ DJb.support
    · exact (hDbpos P hP).le
    · have : Db.coeff P = 0 := by_contra fun h => hP ((hDbsupp P).1 h)
      rw [this]
  · intro V hV z
    have hcomp : (IV V).comap (q ≫ r₀) =
        (((IV V).comap r₀).comap Ba.toBase).comap Bb.toBase := by
      rw [hqdef, Category.assoc, Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_comp]
    change (IdealSheafData.stalk ((IV V).comap (q ≫ r₀)) z).IsPrincipal
    rw [hcomp, IdealSheafData.stalk_comap]
    refine Submodule.IsPrincipal.map_ringHom _ ?_
    set z' := Bb.toBase z
    by_cases hVu : (V : Set Y) = Set.univ
    · have hbot : IV V = ⊥ := by
        have e : (⟨(V : Set Y), V.isClosed⟩ : TopologicalSpace.Closeds Y) = ⊤ :=
          TopologicalSpace.Closeds.ext hVu
        change Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Y), V.isClosed⟩ = ⊥
        rw [e, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]
      rw [hbot, Scheme.IdealSheafData.comap_bot, Scheme.IdealSheafData.comap_bot]
      refine ⟨⟨0, ?_⟩⟩
      rw [Submodule.span_zero_singleton]
      obtain ⟨U, hU, hxU, -⟩ :=
        exists_isAffineOpen_mem_and_subset (X := Ba.target) (x := z') (U := ⊤) (by simp)
      rw [IdealSheafData.stalk_eq_map_germ _ z' ⟨U, hU⟩ hxU, Scheme.IdealSheafData.ideal_bot]
      exact Ideal.map_bot
    · have hVT : V ∈ T := Finset.mem_filter.2 ⟨h𝒱.mem_toFinset.2 hV, hVu⟩
      refine hfactor _ (Ia.comap r₀ * (Scheme.IdealSheafData.vanishingIdeal F₀.supp *
          IQ.comap r₀ * ∏ V' ∈ T.erase V, (IV V').comap r₀)) ?_ z'
      rw [hJadef, hMadef, ← Finset.mul_prod_erase T _ hVT]
      ac_rfl
  rw [hBto, Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc]

section GenericPoint

open MMP.Resolution

/-- The stages of the sequence `X, S 0, S 1, …`. -/
private def consStage (X : Scheme.{0}) (S : ℕ → Scheme.{0}) : ℕ → Scheme.{0}
  | 0 => X
  | i + 1 => S i

/-- The centres of the sequence `x, p 0, p 1, …`. -/
private def consPoint {X : Scheme.{0}} {S : ℕ → Scheme.{0}} (x : X) (p : ∀ i, S i) :
    ∀ i, consStage X S i
  | 0 => x
  | i + 1 => p i

private theorem natCast_lt_of_succ_lt_add_one {i : ℕ} {n : ℕ∞} (hi : ((i + 1 : ℕ) : ℕ∞) < n + 1) :
    (i : ℕ∞) < n := by
  have : ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by push_cast; rfl
  rw [this] at hi
  exact (ENat.add_lt_add_iff_right ENat.one_ne_top).1 hi

/-- Prefix a sequence of point blow-ups of `Bl_x X` by the blow-up of `X` at `x`. -/
private noncomputable def consSeq {X : Scheme.{0}} (x : X) (hx : IsClosed ({x} : Set X))
    (s : PointBlowupSequence (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))) :
    PointBlowupSequence X where
  length := s.length + 1
  S := consStage X s.S
  zeroIso := Iso.refl X
  p := consPoint x s.p
  isClosed_p
    | 0, _ => hx
    | i + 1, hi => s.isClosed_p i (natCast_lt_of_succ_lt_add_one hi)
  blowupIso
    | 0, _ => s.zeroIso
    | i + 1, hi => s.blowupIso i (natCast_lt_of_succ_lt_add_one hi)

private theorem consSeq_π_succ {X : Scheme.{0}} (x : X) (hx : IsClosed ({x} : Set X))
    (s : PointBlowupSequence (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))) :
    ∀ (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) ≤ (consSeq x hx s).length) (hi' : (i : ℕ∞) ≤ s.length),
      (consSeq x hx s).π (i + 1) hi =
        s.π i hi' ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)
  | 0, hi, hi' => by
    rw [PointBlowupSequence.π, PointBlowupSequence.π, PointBlowupSequence.π]
    exact Category.comp_id _
  | i + 1, hi, hi' => by
    rw [PointBlowupSequence.π, consSeq_π_succ x hx s i _
      (PointBlowupSequence.coe_lt_of_succ_le hi').le, PointBlowupSequence.π, Category.assoc]
    rfl

/-- `f : Y ⟶ X` is, up to an isomorphism of `Y` over `X`, the last stage of a finite sequence of
point blow-ups of `X`. -/
private def IsPointBlowupSeqEnd (X Y : Scheme.{0}) (f : Y ⟶ X) : Prop :=
  ∃ (s : PointBlowupSequence X) (n : ℕ) (hn : s.length = n) (e : s.S n ≅ Y),
    e.hom ≫ f = s.π n hn.ge

/-- The sequence of length zero. -/
private noncomputable def nilSeq (Y : Scheme.{0}) [Nonempty Y] : PointBlowupSequence Y where
  length := 0
  S := fun _ => Y
  zeroIso := Iso.refl Y
  p := fun _ => Classical.arbitrary Y
  isClosed_p := fun _ hi => by simp at hi
  blowupIso := fun _ hi => by simp at hi

private theorem isPointBlowupSeqEnd_id (Y : Scheme.{0}) [Nonempty Y] :
    IsPointBlowupSeqEnd Y Y (𝟙 Y) :=
  ⟨nilSeq Y, 0, Nat.cast_zero.symm, Iso.refl Y, Category.comp_id _⟩

private theorem isPointBlowupSeqEnd_cons {X Y : Scheme.{0}} (x : X) (hx : IsClosed ({x} : Set X))
    {g : Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)}
    (h : IsPointBlowupSeqEnd _ Y g) :
    IsPointBlowupSeqEnd X Y
      (g ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) := by
  obtain ⟨s, n, hn, e, he⟩ := h
  have hn' : (consSeq x hx s).length = ((n + 1 : ℕ) : ℕ∞) := by
    change s.length + 1 = _
    rw [hn]; push_cast; rfl
  refine ⟨consSeq x hx s, n + 1, hn', e, ?_⟩
  rw [consSeq_π_succ x hx s n hn'.ge hn.ge, ← he, Category.assoc]
  rfl

private theorem isPointBlowupSeqEnd_of_pointBlowupChain {X W : Scheme.{0}} {h : W ⟶ X}
    (hc : Stacks.ResolutionOfSurfaces.PointBlowupChain X Set.univ W h) :
    ∀ (Y : Scheme.{0}) (g : Y ⟶ W), IsPointBlowupSeqEnd W Y g →
      IsPointBlowupSeqEnd X Y (g ≫ h) := by
  induction hc with
  | refl => intro Y g hg; rwa [Category.comp_id]
  | step hh w hw _ ih =>
    intro Y g hg
    rw [← Category.assoc]
    exact ih _ _ (isPointBlowupSeqEnd_cons w hw hg)

private theorem isPointBlowupSeqEnd_of_factorsAsPointBlowups {X Y : Scheme.{0}} [Nonempty Y]
    {f : Y ⟶ X} (hf : Stacks.ResolutionOfSurfaces.FactorsAsPointBlowups X Set.univ Y f) :
    IsPointBlowupSeqEnd X Y f := by
  obtain ⟨W, h, hc, e, rfl⟩ := hf
  haveI : Nonempty W := ⟨e.hom.base (Classical.arbitrary Y)⟩
  obtain ⟨s, n, hn, e', he'⟩ := isPointBlowupSeqEnd_id W
  exact isPointBlowupSeqEnd_of_pointBlowupChain hc Y e.hom
    ⟨s, n, hn, e' ≪≫ e.symm, by rw [Iso.trans_hom, Category.assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.comp_id, ← he', Category.comp_id]⟩

/-- On a complex variety of dimension four, the generic point of a surface has coheight two. -/
private theorem coheight_genericPoint_eq_two {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sY] (hdimY : topologicalKrullDim Y = 4) (V : IrreducibleCloseds Y)
    (hV : topologicalKrullDim (V : Set Y) = 2) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hV, hdimY] at h
  generalize Order.coheight V.isIrreducible.genericPoint = c at h ⊢
  induction c using ENat.recTopCoe with
  | top => exact absurd h (by decide)
  | coe m =>
    have h2 : (((2 + m : ℕ) : ℕ∞) : WithBot ℕ∞) = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [Nat.cast_add, WithBot.coe_add]; exact h
    rw [WithBot.coe_inj, Nat.cast_inj] at h2
    have : m = 2 := by omega
    subst this; rfl

/-- The local ring of a scheme at a point of its smooth locus over a field is regular. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) {y : Y} (hy : y ∈ smoothLocus sY) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨U, hyU, hU⟩ := MMP.Mori.mem_smoothLocus_iff.1 hy
  have : Smooth (U.ι ≫ sY) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sY) ⟨y, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv

/-- A locally Noetherian scheme with a flat preimmersion to a scheme whose local rings at the
image points are regular is regular. -/
private theorem isRegular_of_flat_isPreimmersion {W X : Scheme.{0}} (h : W ⟶ X) [Flat h]
    [IsPreimmersion h] [IsLocallyNoetherian W]
    (hreg : ∀ w, IsRegularLocalRing (X.presheaf.stalk (h w))) : IsRegular W := by
  refine (isRegular_iff_regular_stalks W).2 ⟨inferInstance, fun w => ?_⟩
  haveI := isIso_stalkMap_of_flat_isPreimmersion h w
  have := hreg w
  exact IsRegularLocalRing.of_ringEquiv (asIso (h.stalkMap w)).commRingCatIsoToRingEquiv

/-- A scheme with a flat preimmersion to an integral scheme whose image contains the generic
point is integral. -/
private theorem isIntegral_of_flat_isPreimmersion {W X : Scheme.{0}} (h : W ⟶ X) [Flat h]
    [IsPreimmersion h] [IsIntegral X] (hgen : genericPoint X ∈ Set.range h) : IsIntegral W := by
  obtain ⟨w₀, hw₀⟩ := hgen
  haveI : Nonempty W := ⟨w₀⟩
  haveI : IrreducibleSpace W := by
    refine (irreducibleSpace_def W).2 ?_
    have hcl : closure ({w₀} : Set W) = Set.univ := by
      refine Set.eq_univ_of_forall fun w => ?_
      rw [← specializes_iff_mem_closure]
      refine ((IsPreimmersion.isEmbedding h).isInducing.specializes_iff).1 ?_
      rw [hw₀]
      exact (genericPoint_spec X).specializes (Set.mem_univ _)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI : ∀ w : W, _root_.IsReduced (W.presheaf.stalk w) := fun w => by
    haveI := isIso_stalkMap_of_flat_isPreimmersion h w
    exact isReduced_of_injective (asIso (h.stalkMap w)).commRingCatIsoToRingEquiv.symm
      (RingEquiv.injective _)
  haveI : IsReduced W := isReduced_of_isReduced_stalk W
  exact isIntegral_of_irreducibleSpace_of_isReduced W

/-- In a commutative square, if the stalk maps of the two legs out of the corner are
isomorphisms (one on each side), the stalk maps of the two remaining legs are isomorphisms
together. -/
private theorem isIso_stalkMap_iff_of_comp_eq {P Z T Y : Scheme.{0}} {fst : P ⟶ Z} {snd : P ⟶ T}
    {r : Z ⟶ Y} {g : T ⟶ Y} (w : fst ≫ r = snd ≫ g) (x : P) [IsIso (fst.stalkMap x)]
    [IsIso (g.stalkMap (snd x))] : IsIso (r.stalkMap (fst x)) ↔ IsIso (snd.stalkMap x) := by
  have key : IsIso ((fst ≫ r).stalkMap x) ↔ IsIso ((snd ≫ g).stalkMap x) := by rw [w]
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at key
  exact (isIso_comp_right_iff (r.stalkMap (fst x)) (fst.stalkMap x)).symm.trans
    (key.trans (isIso_comp_left_iff (g.stalkMap (snd x)) (snd.stalkMap x)))

/-- The ideal induced at a point by the reduced ideal of its closure is the maximal ideal. -/
private theorem stalk_vanishingIdeal_eq_maximalIdeal_of_eq_closure {Y : Scheme.{0}} (y : Y)
    (W : Closeds Y) (hW : (W : Set Y) = closure {y}) :
    AlgebraicGeometry.IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal W) y =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  rw [MMP.Resolution.stalk_vanishingIdeal_eq]
  have hpre : Y.fromSpecStalk y ⁻¹' (W : Set Y) =
      {IsLocalRing.closedPoint (Y.presheaf.stalk y)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hW, ← specializes_iff_mem_closure]
    constructor
    · intro hp
      have hgen : Y.fromSpecStalk y p ⤳ y := by
        have : Y.fromSpecStalk y p ∈ Set.range (Y.fromSpecStalk y) := ⟨p, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      have heq : Y.fromSpecStalk y p = Y.fromSpecStalk y (IsLocalRing.closedPoint _) := by
        rw [Scheme.fromSpecStalk_closedPoint]
        exact (hgen.antisymm hp).eq
      exact (IsPreimmersion.isEmbedding (Y.fromSpecStalk y)).injective heq
    · rintro rfl
      rw [Scheme.fromSpecStalk_closedPoint]
  refine (congrArg PrimeSpectrum.vanishingIdeal hpre).trans ?_
  exact PrimeSpectrum.vanishingIdeal_singleton (IsLocalRing.closedPoint _)

/-- A point of coheight two of a locally Noetherian scheme: under a morphism whose stalk map at
a point over it is an isomorphism, the inverse image of the reduced ideal of its closure is not
principal there. -/
private theorem not_isPrincipal_stalk_comap_vanishingIdeal {Y Z : Scheme.{0}}
    [IsLocallyNoetherian Y]
    (y : Y) (hy : Order.coheight y = 2) (W : Closeds Y) (hW : (W : Set Y) = closure {y})
    (r : Z ⟶ Y) (z : Z) (hz : r.base z = y) [IsIso (r.stalkMap z)] :
    ¬ (AlgebraicGeometry.IdealSheafData.stalk
      ((Scheme.IdealSheafData.vanishingIdeal W).comap r) z).IsPrincipal := by
  intro hpr
  rw [IdealSheafData.stalk_comap,
    stalk_vanishingIdeal_eq_maximalIdeal_of_eq_closure (r.base z) W (hz ▸ hW)] at hpr
  set e := (asIso (r.stalkMap z)).commRingCatIsoToRingEquiv
  have hm : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (r.base z))).IsPrincipal := by
    have := hpr.map_ringHom e.symm.toRingHom
    rwa [Ideal.map_map, show e.symm.toRingHom.comp (r.stalkMap z).hom = RingHom.id _ from
      RingHom.ext e.symm_apply_apply, Ideal.map_id] at this
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (r.base z)))
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  have h2 : ((IsLocalRing.maximalIdeal (Y.presheaf.stalk (r.base z))).height : WithBot ℕ∞) =
      ((2 : ℕ∞) : WithBot ℕ∞) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ringKrullDim_stalk_eq_coheight, hz, hy]
  rw [WithBot.coe_inj] at h2
  rw [h2] at hle
  exact absurd hle (by decide)

/-- **The base change of a resolution to the local scheme at the generic point of a surface in
the smooth locus is a sequence of point blow-ups starting at the closed point.** -/
private theorem exists_pointBlowupSequence_pullback_fromSpecStalk
    {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {sY : Y ⟶ Spec (.of ℂ)}
    {r : Z ⟶ Y} (hres : MMP.Intersection.IsResolution sY r)
    (hdimY : topologicalKrullDim Y = 4) (V : IrreducibleCloseds Y)
    (hV : topologicalKrullDim (V : Set Y) = 2)
    (hη : V.isIrreducible.genericPoint ∈ smoothLocus sY)
    (hpr : ∀ z : Z, (AlgebraicGeometry.IdealSheafData.stalk
      ((Scheme.IdealSheafData.vanishingIdeal ⟨(V : Set Y), V.isClosed⟩).comap r) z).IsPrincipal) :
    ∃ (s : MMP.Resolution.PointBlowupSequence
        (Spec (Y.presheaf.stalk V.isIrreducible.genericPoint)))
      (n : ℕ) (hn : s.length = n)
      (e : s.S n ≅ Limits.pullback r (Y.fromSpecStalk V.isIrreducible.genericPoint)),
      e.hom ≫ Limits.pullback.snd _ _ = s.π n hn.ge ∧
      ∃ h0 : ((0 : ℕ) : ℕ∞) < s.length,
        (s.π 0 h0.le).base (s.p 0) =
          IsLocalRing.closedPoint (Y.presheaf.stalk V.isIrreducible.genericPoint) := by
  set η := V.isIrreducible.genericPoint with hηdef
  set A := Y.presheaf.stalk η
  set g := Y.fromSpecStalk η
  set P := Limits.pullback r g
  set fst : P ⟶ Z := Limits.pullback.fst r g
  set snd : P ⟶ Spec A := Limits.pullback.snd r g
  obtain ⟨hYv, hZv, hZs, hproj, hbir⟩ := hres
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hproj
  haveI : LocallyOfFiniteType sY := hYv.toLocallyOfFiniteType
  have hcoh : Order.coheight η = 2 := coheight_genericPoint_eq_two (sY := sY) hdimY V hV
  have hηcl : (V : Set Y) = closure {η} :=
    (IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed).symm
  haveI : Flat g := flat_fromSpecStalk Y η
  have hsq : IsPullback fst snd r g := IsPullback.of_hasPullback r g
  haveI : Flat fst := MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip ‹Flat g›
  haveI : IsPreimmersion fst :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip
      (inferInstance : IsPreimmersion g)
  have hfstiso : ∀ x, IsIso (fst.stalkMap x) := isIso_stalkMap_of_flat_isPreimmersion fst
  have hgiso : ∀ x, IsIso (g.stalkMap x) := isIso_stalkMap_of_flat_isPreimmersion g
  -- the local scheme is a regular surface
  have hT : Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface (Spec A) := by
    haveI : IsNoetherian (Spec A) := inferInstance
    refine ⟨inferInstance, inferInstance, isRegular_of_flat_isPreimmersion g fun t => ?_, ?_⟩
    · refine isRegularLocalRing_stalk_of_mem_smoothLocus sY ?_
      have ht : g.base t ⤳ η := by
        have : g.base t ∈ Set.range g := ⟨t, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      exact ht.mem_open (smoothLocus sY).isOpen hη
    · rw [show topologicalKrullDim (Spec A) = ringKrullDim A from
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A, ringKrullDim_stalk_eq_coheight, hcoh]
      rfl
  -- the base change is a regular surface, proper and birational over it
  have hbirZ := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbir
  haveI : IsDominant r := hbir.isDominant
  have hrgen : r.base (genericPoint Z) = genericPoint Y := map_genericPoint_of_isDominant r
  have hYgen : genericPoint Y ∈ Set.range g := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec Y).specializes (Set.mem_univ η)
  have hgenP : genericPoint Z ∈ Set.range fst := by
    rw [Scheme.Pullback.range_fst]
    change r.base (genericPoint Z) ∈ Set.range g
    rw [hrgen]
    exact hYgen
  haveI : IsIntegral P := isIntegral_of_flat_isPreimmersion fst hgenP
  haveI : IsLocallyNoetherian (Spec A) := hT.isNoetherian.toIsLocallyNoetherian
  haveI : IsLocallyNoetherian P :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ snd inferInstance inferInstance
  have hfstgen : fst.base (genericPoint P) = genericPoint Z := by
    obtain ⟨w₀, hw₀⟩ := hgenP
    have h1 : fst.base (genericPoint P) ⤳ genericPoint Z := by
      rw [← hw₀]
      exact ((genericPoint_spec P).specializes (Set.mem_univ w₀)).map fst.base.hom.continuous
    exact (h1.antisymm ((genericPoint_spec Z).specializes (Set.mem_univ _))).eq
  have hgT : g.base (genericPoint (Spec A)) = genericPoint Y := by
    obtain ⟨t₁, ht₁⟩ := hYgen
    have h1 : g.base (genericPoint (Spec A)) ⤳ genericPoint Y := by
      rw [← ht₁]
      exact ((genericPoint_spec (Spec A)).specializes (Set.mem_univ t₁)).map
        g.base.hom.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hsndgen : snd.base (genericPoint P) = genericPoint (Spec A) := by
    refine (IsPreimmersion.isEmbedding g).injective ?_
    change (snd ≫ g).base (genericPoint P) = g.base (genericPoint (Spec A))
    rw [← Limits.pullback.condition, hgT, Scheme.Hom.comp_apply, hfstgen, hrgen]
  have hbirP : IsBirational snd := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
      exact hsndgen
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      haveI := hfstiso (genericPoint P)
      haveI := hgiso (snd.base (genericPoint P))
      haveI : IsIso (r.stalkMap (fst.base (genericPoint P))) :=
        hbirZ.2 _ (by rw [hfstgen, genericPoints_eq_singleton]; rfl)
      exact (isIso_stalkMap_iff_of_comp_eq Limits.pullback.condition _).1 inferInstance
  have hP : Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface P := by
    haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace snd
    haveI : IsNoetherian P := ⟨⟩
    refine ⟨inferInstance, inferInstance, isRegular_of_flat_isPreimmersion fst fun w =>
      isRegularLocalRing_stalk_of_mem_smoothLocus (r ≫ sY) (hZs ▸ trivial), ?_⟩
    rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hbirP snd.isClosedMap]
    exact hT.topologicalKrullDim_eq
  have hfac := Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_isProper_of_isBirational snd
    hT hP inferInstance hbirP
  haveI : Nonempty P := ⟨genericPoint P⟩
  obtain ⟨s, n, hn, e, he⟩ := isPointBlowupSeqEnd_of_factorsAsPointBlowups hfac
  have h0 : ((0 : ℕ) : ℕ∞) < s.length := by
    by_contra hle
    have hn0 : n = 0 := by
      have : s.length = 0 := by
        rw [Nat.cast_zero] at hle; exact nonpos_iff_eq_zero.1 (not_lt.1 hle)
      rw [this] at hn; exact_mod_cast hn.symm
    subst hn0
    rw [PointBlowupSequence.π] at he
    haveI : IsIso snd := by
      have : snd = e.inv ≫ s.zeroIso.hom := by rw [← he, Iso.inv_hom_id_assoc]
      rw [this]; infer_instance
    set p₀ := (inv snd).base (IsLocalRing.closedPoint A)
    have hp₀ : snd.base p₀ = IsLocalRing.closedPoint A := by
      change (inv snd ≫ snd).base (IsLocalRing.closedPoint A) = _
      rw [IsIso.inv_hom_id]; rfl
    have hz : r.base (fst.base p₀) = η := by
      rw [← Scheme.Hom.comp_apply, Limits.pullback.condition, Scheme.Hom.comp_apply, hp₀]
      exact Scheme.fromSpecStalk_closedPoint
    haveI := hfstiso p₀
    haveI := hgiso (snd.base p₀)
    haveI : IsIso (r.stalkMap (fst.base p₀)) :=
      (isIso_stalkMap_iff_of_comp_eq Limits.pullback.condition p₀).2 inferInstance
    exact not_isPrincipal_stalk_comap_vanishingIdeal η hcoh _ hηcl r _ hz (hpr _)
  refine ⟨s, n, hn, e, he, h0, ?_⟩
  rw [PointBlowupSequence.π]
  have hcl : IsClosed ({s.zeroIso.hom.base (s.p 0)} : Set (Spec A)) := by
    rw [← Set.image_singleton]
    exact s.zeroIso.hom.isClosedMap _ (s.isClosed_p 0 h0)
  have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hcl
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

end GenericPoint

end MMP.Fourfold.SimultaneousModel

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open MMP.Mori

namespace MMP.Fourfold

variable {X Y : Scheme.{0}} [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

open SimultaneousModel in
/-- **A simultaneous curve-and-point conductor model.** Let `p : Y ⟶ X` be a projective birational
morphism of normal projective complex fourfolds, `Y` `ℚ`-factorial and terminal, and `Q` a reduced
divisor on `Y` with `dim p(Q) ≤ 1`, and let `𝒱` be a finite family of irreducible closed subsets of
`Y`. There are a curve-and-point exceptional model `(r₀, F₀, D₀)` of `Y`
(`MMP.Fourfold.IsCurvePointExceptionalModel`) and a smooth blow-up sequence `B` of `Z₀` whose
centres have simple normal crossings with `F₀`, with composite `q : Z ⟶ Z₀`, such that `r = q ≫ r₀`
is a resolution with `r⁻¹(Q) ∪ Ex(r)` snc, `Ex(p ∘ r)` is snc and the support of an effective
divisor `D` with `-D` Cartier and `(p ∘ r)`-ample, the inverse image ideal of every `V ∈ 𝒱` is
invertible on `Z`, over the generic point of every surface `V ∈ 𝒱` in the smooth locus of `Y` the
base change of `r` is a sequence of point blow-ups starting with the closed point, the reduced
divisor `F` with support `Ex(r)` exists, and for every such `F` and every choice of local-system
opens `T° ⊆ T`, `dim_ℚ D_{v,Q}(r) ≤ ∑_{T ⊆ Sing Y ∩ Q} b_T` (`MMP.Fourfold.verticalDefectOver`,
`MMP.Fourfold.curveLocalSystemRank`). -/
@[mmp "lem_mmp_conductor_general_simultaneous_model"]
public theorem exists_isCurvePointExceptionalModel_finrank_verticalDefectOver_le
    {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} {p : Y ⟶ X}
    (hpX : p ≫ sX = sY)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hdimX : topologicalKrullDim X = 4)
    (hp : IsProjectiveMorphism p ∧ MMP.Mori.IsBirationalMorphism p)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQf : IsQFactorial sY)
    (hdimY : topologicalKrullDim Y = 4) (hYt : IsTerminalVariety sY)
    {Q : Divisor Y} (hQ : MMP.Intersection.IsReducedEffective Q)
    (hpQ : topologicalKrullDim (p.base '' (Q.supp : Set Y)) ≤ 1)
    (𝒱 : Set (IrreducibleCloseds Y)) (h𝒱 : 𝒱.Finite) :
    ∃ (Z₀ : Scheme.{0}) (_ : Z₀.Over (Spec (.of ℂ))) (_ : CompactSpace Z₀)
      (_ : IsLocallyNoetherian Z₀) (_ : IsNormal Z₀) (r₀ : Z₀ ⟶ Y) (F₀ D₀ : Divisor Z₀),
      IsCurvePointExceptionalModel sY r₀ F₀ D₀ ∧
      ∃ B : MMP.Resolution.ClosedBlowupSequence Z₀,
        B.IsSmooth (Z₀ ↘ Spec (.of ℂ)) ∧
        B.CentersHaveSNCWith (Z₀ ↘ Spec (.of ℂ)) (F₀.supp : Set Z₀) ∧
      ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of ℂ))) (_ : IsComplexScheme Z) (_ : CompactSpace Z)
        (_ : IsLocallyNoetherian Z) (_ : IsNormal Z) (q : Z ⟶ Z₀) (e : Z ≅ B.target),
        q = e.hom ≫ B.toBase ∧
        ∃ hqc : q ≫ r₀ ≫ sY = Z ↘ Spec (.of ℂ),
        ∃ hres : MMP.Intersection.IsResolution sY (q ≫ r₀),
        MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ))
          ((q ≫ r₀).base ⁻¹' (Q.supp : Set Y) ∪ exceptionalSet (q ≫ r₀)) ∧
        MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) (exceptionalSet (q ≫ r₀ ≫ p)) ∧
        (∃ D : Divisor Z, (∀ P, 0 ≤ D.coeff P) ∧
          (D.supp : Set Z) = exceptionalSet (q ≫ r₀ ≫ p) ∧
          ∃ h : (-D).IsCartier, (-D).IsRelativelyAmple (q ≫ r₀ ≫ p) h) ∧
        (∀ V ∈ 𝒱, ∀ z : Z,
          (AlgebraicGeometry.IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal
            ⟨(V : Set Y), V.isClosed⟩).comap (q ≫ r₀)) z).IsPrincipal) ∧
        (∀ V ∈ 𝒱, topologicalKrullDim (V : Set Y) = 2 →
          V.isIrreducible.genericPoint ∈ smoothLocus sY →
          ∃ (s : MMP.Resolution.PointBlowupSequence
              (Spec (Y.presheaf.stalk V.isIrreducible.genericPoint)))
            (n : ℕ) (hn : s.length = n)
            (e : s.S n ≅ Limits.pullback (q ≫ r₀) (Y.fromSpecStalk V.isIrreducible.genericPoint)),
            e.hom ≫ Limits.pullback.snd _ _ = s.π n hn.ge ∧
            ∃ h0 : ((0 : ℕ) : ℕ∞) < s.length,
              (s.π 0 h0.le).base (s.p 0) =
                IsLocalRing.closedPoint (Y.presheaf.stalk V.isIrreducible.genericPoint)) ∧
        (∃ F : Divisor Z, MMP.Intersection.IsReducedEffective F ∧
          (F.supp : Set Z) = exceptionalSet (q ≫ r₀)) ∧
        ∀ F : Divisor Z, MMP.Intersection.IsReducedEffective F →
          (F.supp : Set Z) = exceptionalSet (q ≫ r₀) →
          ∀ To : ∀ T : {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
              topologicalKrullDim (T : Set Y) = 1}, (curveScheme T.1).Opens,
            (∀ T, IsLocalSystemOpen sY (To T)) →
            letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
            haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hY.toIsVariety.toLocallyOfFiniteType
            haveI : (q ≫ r₀).IsOver (Spec (.of ℂ)) := ⟨(Category.assoc _ _ _).trans hqc⟩
            haveI : IsProper (q ≫ r₀) := isProper_of_isProjectiveMorphism _ hres.2.2.2.1
            Module.finrank ℚ (verticalDefectOver (q ≫ r₀) F (Q.supp : Set Y)) ≤
              ∑ᶠ (T) (_ : (T.1 : Set Y) ⊆ Q.supp), curveLocalSystemRank sY (To T) := by
  clear hpQ
  obtain ⟨Z₀, i₀, _, _, _, _, r₀, F₀, D₀, hM, hZ₀, B, hBs, hBc, Z, iZ, _, _, _, _, q, e, hqe,
    hqc, hres, hsncQ, hsncX, hD, hV, hq⟩ :=
    exists_model hpX hX hdimX hp hY hQf hdimY hYt hQ 𝒱 h𝒱
  have hqo : q.IsOver (Spec (.of ℂ)) := ⟨by rw [← hqc, ← hM.comp_eq]⟩
  have hdim₀ : topologicalKrullDim Z₀ = 4 := by
    haveI := hM.isResolution.1
    haveI : MMP.Mori.IsVariety ℂ (r₀ ≫ sY) := hM.isResolution.2.1
    rw [← hdimY]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r₀ ≫ sY)
      hM.isResolution.2.2.2.2).symm
  haveI : IsNoetherian Z := ⟨⟩
  obtain ⟨Ps, hPs⟩ := MMP.Fourfold.ConductorBlowup.exists_finset_primeDivisor_eq
    (exceptionalSet (q ≫ r₀)).isClosed
    (MMP.Mori.isPureCodimOne_exceptionalSet_of_isQFactorial sY ((q ≫ r₀) ≫ sY) hQf hres.2.1
      (q ≫ r₀) rfl hres.2.2.2.1 hres.2.2.2.2)
  refine ⟨Z₀, i₀, inferInstance, inferInstance, inferInstance, r₀, F₀, D₀, hM, B, hBs, hBc, Z,
    iZ, inferInstance, inferInstance, inferInstance, inferInstance, q, e, hqe, hqc, hres, hsncQ,
    hsncX, hD, hV, fun V hV𝒱 hV2 hη => exists_pointBlowupSequence_pullback_fromSpecStalk hres
      hdimY V hV2 hη (hV V hV𝒱), ⟨MMP.Intersection.reducedDivisorOf Ps,
      MMP.Intersection.isReducedEffective_reducedDivisorOf Ps, ?_⟩, fun F hF hFex To hTo => ?_⟩
  · rw [coe_supp_eq_iUnion, MMP.Intersection.support_reducedDivisorOf, ← hPs]
  exact finrank_verticalDefectOver_le_of_isBoundaryBlowup hM hZ₀ hdim₀ q hq F hF hFex _
    (Q.supp).isClosed To hTo hres

end MMP.Fourfold
