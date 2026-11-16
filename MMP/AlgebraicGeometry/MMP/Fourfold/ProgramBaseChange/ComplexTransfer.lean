module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.AlgClosedExtension
import MMP.AlgebraicGeometry.MMP.Fourfold.ProgramBaseChange.CountableDescent
import MMP.AlgebraicGeometry.Geometrically.CurveClassesBaseChange
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.Analysis.Convex.FiniteDimensional

/-!
# Transfer of an infinite program to `ℂ`

Let `k` be an algebraically closed field of characteristic zero and `(X, B)` a projective lc
fourfold pair over `k` with rational boundary. If some program from `(X, B)` has infinitely many
birational steps, then so does some program from a projective lc fourfold pair over `ℂ` with
rational boundary. The program is the base change of a program over a countable algebraically
closed subfield `k₀ ⊆ k` (`MMP.Fourfold.Program.exists_countable_isAlgClosed_subfield_program`),
and `k₀` embeds in `ℂ`. Base changing all the data of the program along `Spec ℂ ⟶ Spec k₀` —
models, targets and morphisms by fibre products, the canonical divisors and boundaries prime
divisor by prime divisor (the preimage of a prime divisor is a prime divisor, `k₀` being
algebraically closed), and the rays through the isomorphism of numerical curve classes
`MMP.Fourfold.numericalCurveClassesBaseChange` — gives a program over `ℂ`
by `MMP.Fourfold.program_conditions_iff_of_isPullback`.

## Main results

* `MMP.Fourfold.Program.exists_complex_of_n_eq_top`: an infinite program over `k` gives an
  infinite program over `ℂ`.

## Implementation notes

A program `P : MMP.Fourfold.Program sX K B` carries the projectivity of `X`, the log canonicity
of `(X, B)` and the canonical divisor `K`; it has infinitely many birational steps exactly when
`P.n = ⊤`. The boundary is a `ℚ`-divisor, so it is rational. "Fourfold" is
`topologicalKrullDim X = 4`.

The field `k` and the schemes are taken in universe `0`, the universe of `ℂ`, so that the
program over `k` and the program over `ℂ` are compared by base change inside one category of
schemes.

An infinite program has no final fibre-type contraction, so the final target of the
base-changed program is taken to be a model with the identity as final contraction; no condition
is imposed on it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

section Preimage

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]
  {X W : Scheme.{u}} (f : X ⟶ Spec (.of k₀)) [LocallyOfFiniteType f] {p : W ⟶ X}
  {s : W ⟶ Spec (.of K)}

/-- The preimage of a locally closed subset under the projection of a base change of the ground
field has the same dimension. -/
private lemma topologicalKrullDim_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZ : IsLocallyClosed Z) : topologicalKrullDim (p ⁻¹' Z) = topologicalKrullDim Z := by
  obtain ⟨-, -, -, -, hdim⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) f
  rw [← hdim Z hZ]
  have hp (w : W) : p w = pullback.fst f _ (h.isoPullback.hom w) := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  refine (Homeomorph.subtype (Scheme.homeoOfIso h.isoPullback) fun w => ?_).isHomeomorph
    |>.topologicalKrullDim_eq
  simp only [Set.mem_preimage, Scheme.homeoOfIso_apply, hp w]

/-- The preimage of an irreducible closed subset under the projection of a base change of an
algebraically closed ground field is irreducible. -/
private lemma isIrreducible_preimage_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) {Z : Set X}
    (hZc : IsClosed Z) (hZ : IsIrreducible Z) : IsIrreducible (p ⁻¹' Z) := by
  let C : TopologicalSpace.Closeds X := ⟨Z, hZc⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible C hZ
  have hsq : IsPullback (pullback.snd p I.subschemeι) (pullback.fst p I.subschemeι ≫ s)
      (I.subschemeι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    (IsPullback.of_hasPullback p I.subschemeι).flip.paste_vert h
  obtain ⟨-, hint, -⟩ :=
    MMP.isReduced_isIntegral_isNormal_dim_baseChange_of_isAlgClosed (K := K) (I.subschemeι ≫ f)
  have : IsIntegral (pullback (I.subschemeι ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) := hint.1 ‹_›
  have : IsIntegral (pullback p I.subschemeι) := .of_isIso hsq.isoPullback.inv
  have hr : Set.range (pullback.fst p I.subschemeι) = p ⁻¹' Z := by
    rw [Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (Scheme.Hom.continuous _).continuousOn

/-- Under a base change of an algebraically closed ground field of an integral scheme, coheights
can only grow. -/
private lemma coheight_le_of_isPullback
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] :
    ∀ w : W, Order.coheight (p w) ≤ Order.coheight w := by
  have hD : topologicalKrullDim W = topologicalKrullDim X :=
    (ProgramBaseChange.invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  intro w
  have hsub : closure {w} ⊆ p ⁻¹' closure {p w} :=
    closure_minimal (Set.singleton_subset_iff.mpr (subset_closure rfl))
      (isClosed_closure.preimage p.continuous)
  have hle : topologicalKrullDim (closure {w} : Set W) ≤
      topologicalKrullDim (closure {p w} : Set X) := by
    rw [← topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
  exact ProgramBaseChange.le_of_add_eq_add_of_le (hW w) (hX (p w)) hle

/-- The generic point of the preimage of the closure of a point `x` lies over `x` and has the
coheight of `x`. -/
private lemma coheight_eq_of_isGenericPoint_preimage
    (h : IsPullback p s f (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) [IsIntegral X]
    [IsIntegral W] [LocallyOfFiniteType s] [Surjective p] {x : X} {w : W}
    (hw : IsGenericPoint w (p ⁻¹' closure {x})) :
    p w = x ∧ Order.coheight w = Order.coheight x := by
  have hD : topologicalKrullDim W = topologicalKrullDim X :=
    (ProgramBaseChange.invariants_of_isPullback f h).2.2
  have hn := MMP.Fourfold.topologicalKrullDim_eq_toNat_trdeg f
  have hX (x : X) := (MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f x).trans hn
  have hW (w : W) := ((MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight s w).trans
    hD).trans hn
  have hcl : topologicalKrullDim (p ⁻¹' closure {x}) =
      topologicalKrullDim (closure {x} : Set X) :=
    topologicalKrullDim_preimage_of_isPullback f h isClosed_closure.isLocallyClosed
  have hpw : p w = x := ProgramBaseChange.map_eq_of_closure_eq hw.def
  refine ⟨hpw, le_antisymm ?_ ?_⟩
  · have heq : topologicalKrullDim (closure {w} : Set W) =
        topologicalKrullDim (closure {x} : Set X) := by
      rw [← hcl, ← hw.def]
    exact ProgramBaseChange.le_of_add_eq_add_of_le (hX x) (hW w) heq.ge
  · exact hpw ▸ coheight_le_of_isPullback f h w

end Preimage

section BaseChange

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-- The preimage of a prime divisor under a base change along `Spec K ⟶ Spec k₀` (`k₀`
algebraically closed) is a prime divisor. -/
private theorem exists_primeDivisor_closure_eq {X₀ X : Scheme.{u}} [IsIntegral X₀]
    [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)} {π : X ⟶ X₀}
    [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (P₀ : MMP.Mori.PrimeDivisor X₀) :
    ∃ P : MMP.Mori.PrimeDivisor X,
      closure {P.genericPoint} = π.base ⁻¹' closure {P₀.genericPoint} := by
  have : LocallyOfFiniteType s :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h ‹_›
  have : Surjective π := ProgramBaseChange.surjective_of_isPullback h
  obtain ⟨w, hw⟩ := QuasiSober.sober
    (isIrreducible_preimage_of_isPullback s₀ h isClosed_closure isIrreducible_singleton.closure)
    (isClosed_closure.preimage π.continuous)
  have hcoh := (coheight_eq_of_isGenericPoint_preimage s₀ h hw).2
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P₀] at hcoh
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh, ?_⟩
  change closure {(AlgebraicGeometry.PrimeDivisor.ofCoheightOne w hcoh).genericPoint} = _
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hw.def

end BaseChange

end MMP.Fourfold

namespace MMP.ProgramBaseChange

open MMP.Fourfold MMP.Mori

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-- A divisor on `X₀` has a base change along `Spec K ⟶ Spec k₀` (`k₀` algebraically closed):
a divisor on `X` with the coefficient of `P₀` along the prime divisor `π⁻¹(P₀)`, supported on
such prime divisors. -/
theorem exists_divisor_baseChange {R : Type*} [AddCommMonoid R] {X₀ X : Scheme.{u}}
    [IsIntegral X₀] [IsIntegral X] {s₀ : X₀ ⟶ Spec (.of k₀)} {s : X ⟶ Spec (.of K)}
    {π : X ⟶ X₀} [LocallyOfFiniteType s₀]
    (h : IsPullback π s s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (D₀ : DivisorWithCoeffs R X₀) :
    ∃ D : DivisorWithCoeffs R X, IsBaseChange π D₀ D := by
  have : Surjective π := ProgramBaseChange.surjective_of_isPullback h
  choose b hb using exists_primeDivisor_closure_eq h
  have hinj : Function.Injective b := fun P₀ Q₀ e =>
    primeDivisor_eq_of_closure_eq (hb P₀) (e ▸ hb Q₀)
  refine ⟨Finsupp.mapDomain b D₀, fun P₀ P hP => ?_, fun P hP => ?_⟩
  · obtain rfl : b P₀ = P := primeDivisor_eq_of_closure_eq' (hb P₀) hP
    exact Finsupp.mapDomain_apply_of_injective hinj D₀ P₀
  · by_contra hne
    push Not at hne
    exact hP (Finsupp.mapDomain_notin_range D₀ P fun ⟨P₀, e⟩ => hne P₀ (e ▸ hb P₀))

/-- The base change of a normal integral scheme of finite type over `k₀` along
`Spec K ⟶ Spec k₀` is a normal integral Noetherian scheme. -/
theorem isIntegral_compactSpace_isLocallyNoetherian_isNormal_pullback {X₀ : Scheme.{u}}
    [IsIntegral X₀] [IsNormal X₀] (s₀ : X₀ ⟶ Spec (.of k₀)) [LocallyOfFiniteType s₀]
    [QuasiCompact s₀] :
    let W := pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
    IsIntegral W ∧ CompactSpace W ∧ IsLocallyNoetherian W ∧ IsNormal W := by
  intro W
  have hinv := invariants_of_isPullback s₀
    (IsPullback.of_hasPullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
  exact ⟨hinv.2.1.1 ‹_›,
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s₀ _),
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s₀ _), hinv.1.1 ‹_›⟩

end MMP.ProgramBaseChange

namespace MMP.Fourfold

open MMP.Mori

section ModelProj

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K] [IsAlgClosed k₀]

/-- The projections from the base changes of the models of a program to the models. -/
private noncomputable def modelProj {X₀ : Scheme.{u}} {Y₀ : ℕ → Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (sY₀ : ∀ i, Y₀ i ⟶ Spec (.of k₀)) :
    ∀ i, modelSeq (pullback s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
        (fun j => pullback (sY₀ j) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) i ⟶
      modelSeq X₀ Y₀ i
  | 0 => pullback.fst _ _
  | _ + 1 => pullback.fst _ _

/-- The base change of a model of a program is a pullback square over the base change of the
ground field. -/
private theorem isPullback_modelProj {X₀ : Scheme.{u}} {Y₀ : ℕ → Scheme.{u}}
    (s₀ : X₀ ⟶ Spec (.of k₀)) (sY₀ : ∀ i, Y₀ i ⟶ Spec (.of k₀)) (i : ℕ) :
    IsPullback (modelProj (K := K) s₀ sY₀ i)
      (modelStr (pullback.snd s₀ (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
        (fun j => pullback.snd (sY₀ j) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))) i)
      (modelStr s₀ sY₀ i) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) := by
  cases i <;> exact IsPullback.of_hasPullback _ _

end ModelProj

/-- **Transfer of an infinite program to `ℂ`.** If a projective lc fourfold pair `(X, B)` over an
algebraically closed field of characteristic zero has a program with infinitely many birational
steps, then some projective lc fourfold pair `(X', B')` over `ℂ`, with rational boundary, has a
program with infinitely many birational steps. -/
@[mmp "prop_oai4_field_transfer"]
theorem Program.exists_complex_of_n_eq_top {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) (P : Program sX K B) (hP : P.n = ⊤) :
    ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (_ : IsIntegral X') (_ : CompactSpace X')
      (_ : IsLocallyNoetherian X') (_ : IsNormal X') (K' : Divisor X') (B' : QDivisor X'),
      topologicalKrullDim X' = 4 ∧ ∃ P' : Program sX' K' B', P'.n = ⊤ := by
  obtain ⟨k₀, _, _, X₀, _, _, _, _, s₀, K₀, B₀, P₀, hn, _, -, -, hmod, -, -, -⟩ :=
    P.exists_countable_isAlgClosed_subfield_program
  obtain ⟨σ⟩ := MMP.Resolution.Bridges.nonempty_ringHom_complex_and_countable_algebraicClosure.1 k₀
  letI : Algebra k₀ ℂ := σ.toAlgebra
  have hn0 : P₀.n = ⊤ := hn.trans hP
  have hnf : ¬ P₀.hasFinal := fun h => (P₀.final_spec h).1 hn0
  have hstep := fun i => P₀.isPermittedStep i (hn0 ▸ ENat.coe_lt_top i)
  have hproj : ∀ i, MMP.Mori.IsProjectiveVariety k₀ (modelStr s₀ P₀.sY i) := fun i =>
    (hstep i).isProjectiveVariety
  have hft : ∀ i, LocallyOfFiniteType (modelStr s₀ P₀.sY i) := fun i =>
    (hproj i).toLocallyOfFiniteType
  have hqc : ∀ i, QuasiCompact (modelStr s₀ P₀.sY i) := fun i =>
    (hproj i).toIsVariety.toQuasiCompact
  have : LocallyOfFiniteType s₀ := hft 0
  have : QuasiCompact s₀ := hqc 0
  set A : Spec (.of ℂ) ⟶ Spec (.of k₀) := Spec.map (CommRingCat.ofHom (algebraMap k₀ ℂ))
  have iY := fun i => by
    have : LocallyOfFiniteType (P₀.sY i) := hft (i + 1)
    have : QuasiCompact (P₀.sY i) := hqc (i + 1)
    exact
      ProgramBaseChange.isIntegral_compactSpace_isLocallyNoetherian_isNormal_pullback (K := ℂ)
        (P₀.sY i)
  obtain ⟨_, _, _, _⟩ :=
    ProgramBaseChange.isIntegral_compactSpace_isLocallyNoetherian_isNormal_pullback (K := ℂ) s₀
  let X' : Scheme.{0} := pullback s₀ A
  let sX' : X' ⟶ Spec (.of ℂ) := pullback.snd s₀ A
  let Y' : ℕ → Scheme.{0} := fun i => pullback (P₀.sY i) A
  let sY' : ∀ i, Y' i ⟶ Spec (.of ℂ) := fun i => pullback.snd (P₀.sY i) A
  haveI : ∀ i, IsIntegral (Y' i) := fun i => (iY i).1
  haveI : ∀ i, CompactSpace (Y' i) := fun i => (iY i).2.1
  haveI : ∀ i, IsLocallyNoetherian (Y' i) := fun i => (iY i).2.2.1
  haveI : ∀ i, IsNormal (Y' i) := fun i => (iY i).2.2.2
  let π : ∀ i, modelSeq X' Y' i ⟶ modelSeq X₀ P₀.Y i := modelProj (K := ℂ) s₀ P₀.sY
  have hπ : ∀ i, IsPullback (π i) (modelStr sX' sY' i) (modelStr s₀ P₀.sY i) A :=
    isPullback_modelProj (K := ℂ) s₀ P₀.sY
  let Z' : ℕ → Scheme.{0} := fun i => pullback (P₀.sZ i) A
  let sZ' : ∀ i, Z' i ⟶ Spec (.of ℂ) := fun i => pullback.snd (P₀.sZ i) A
  let πZ : ∀ i, Z' i ⟶ P₀.Z i := fun i => pullback.fst (P₀.sZ i) A
  let f' : ∀ i, modelSeq X' Y' i ⟶ Z' i := fun i =>
    pullback.lift (π i ≫ P₀.f i) (modelStr sX' sY' i) (by
      rw [Category.assoc, (hstep i).isContractionOfRay.comp_eq]; exact (hπ i).w)
  let fp' : ∀ i, Y' i ⟶ Z' i := fun i =>
    pullback.lift (pullback.fst (P₀.sY i) A ≫ P₀.fp i) (sY' i) (by
      rw [Category.assoc, (hstep i).isSmallMorphism_step.comp_eq]; exact pullback.condition)
  let φ := fun i => numericalCurveClassesBaseChange (K := ℂ) _ _ _ (hπ i) (hproj i)
  have hφ := fun i =>
    numericalCurveClassesBaseChange_eq_of_isPullback (K := ℂ) _ _ _ (hπ i) (hproj i)
  choose DK hDK using fun i =>
    have := hft i
    ProgramBaseChange.exists_divisor_baseChange (hπ i) (divisorSeq K₀ P₀.KY i)
  choose DB hDB using fun i =>
    have := hft i
    ProgramBaseChange.exists_divisor_baseChange (hπ i) (divisorSeq B₀ P₀.BY i)
  let R' : ∀ i, Set (NumericalCurveClasses (modelStr sX' sY' i)) := fun i =>
    (φ i : _ →ₗ[ℝ] _) '' P₀.R i
  have hR₀ : ∀ i : ℕ, (i : ℕ∞) < P₀.n →
      P₀.R i ⊆ closedConeOfCurves (modelStr s₀ P₀.sY i) := fun i _ => by
    obtain ⟨_, hray, _⟩ := (hstep i).isNegativeExtremalRayOf
    exact hray.1.1
  have hc3 := program_conditions_iff_of_isPullback (K := ℂ) P₀.n P₀.hasFinal s₀ K₀ B₀ P₀.sY
    P₀.KY P₀.BY P₀.R hR₀ P₀.sZ P₀.f (fun i _ => (hstep i).isContractionOfRay.comp_eq) P₀.fp
    (fun i _ => (hstep i).isSmallMorphism_step.comp_eq) P₀.finalRay (fun h => absurd h hnf)
    P₀.sT P₀.g (fun h => absurd h hnf)
    sX' (DK 0) (DB 0) sY' (fun j => DK (j + 1)) (fun j => DB (j + 1)) R' sZ' f'
    (fun i _ => pullback.lift_snd _ _ _) fp' (fun i _ => pullback.lift_snd _ _ _)
    ((φ P₀.n.toNat : _ →ₗ[ℝ] _) '' P₀.finalRay) (modelStr sX' sY' P₀.n.toNat) (𝟙 _)
    (fun h => absurd h hnf) π (fun i _ => hπ i) πZ (fun i _ => IsPullback.of_hasPullback _ _)
    (π P₀.n.toNat ≫ P₀.g) (fun h => absurd h hnf) (fun i _ => pullback.lift_fst _ _ _)
    (fun i _ => pullback.lift_fst _ _ _) (fun h => absurd h hnf)
    (fun i _ P₀' P' hP => by
      cases i <;> exact ⟨(hDK _).1 P₀' P' hP, (hDB _).1 P₀' P' hP⟩)
    (fun i _ P' hP => by
      cases i <;> exact hP.elim ((hDK _).2 P') ((hDB _).2 P'))
    (fun i => (φ i : _ →ₗ[ℝ] _)) (fun i _ => hφ i) (fun i _ => rfl) (fun _ => rfl)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc3.mp ⟨P₀.isProjectiveVariety, P₀.isLogCanonicalPair,
    P₀.isCanonicalDivisor, P₀.isPermittedStep, P₀.KY_eq, P₀.BY_eq, P₀.final_spec⟩
  have hdim₀ : topologicalKrullDim X = topologicalKrullDim X₀ :=
    (ProgramBaseChange.invariants_of_isPullback s₀ (hmod 0 (by simp)).1).2.2
  have hdim' : topologicalKrullDim X' = topologicalKrullDim X₀ :=
    (ProgramBaseChange.invariants_of_isPullback s₀ (hπ 0)).2.2
  exact ⟨X', sX', inferInstance, inferInstance, inferInstance, inferInstance, DK 0, DB 0,
    hdim'.trans (hdim₀.symm.trans hdim), ⟨P₀.n, Y', sY', fun j => DK (j + 1),
    fun j => DB (j + 1), R', Z', sZ', f', fp', h1, h2, h3, h4, h5, h6, P₀.hasFinal,
    (φ P₀.n.toNat : _ →ₗ[ℝ] _) '' P₀.finalRay,
    modelSeq X' Y' P₀.n.toNat, modelStr sX' sY' P₀.n.toNat, 𝟙 _, h7⟩, hn0⟩

end MMP.Fourfold
