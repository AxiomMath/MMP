module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MoveAntitone
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MoveStrictAnti
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionLabels
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Fourfold.StepBranchesUnitDrop
import MMP.AlgebraicGeometry.Singularities.SmallModelCrepant
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.EtaleIndependence

/-!
# Strict drop of the difficulty at a positive-side bad surface

Let `(X_i, B_i)_{i ≥ 0}` be a stabilized small klt tail of projective complex fourfold pairs, with
a terminal chain whose tail from the junction `Y_{i₀}` is a prepared chain. Let `i ≥ i₀` and let
`V ⊆ W_i⁺ ⊆ X_{i+1}` be an irreducible surface in the positive-side bad locus of the `i`-th step
such that `X_{i+1}` is smooth at the generic point `η_V` and
`mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. Then the difficulty strictly drops between consecutive
junctions: `𝒟(Y_{i+1}, Θ_{i+1}) < 𝒟(Y_i, Θ_i)`.

The generic blowup valuation `v_V` has its weight lowered by at least one between the two
junctions, stays exceptional over every model of the `i`-th bridge, and so its weight drops
strictly at some move of the bridge, where the difficulty drops strictly.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.difficulty_succ_lt_of_subset_badLocusPlusAt`:
  the difficulty of the junction `(Y_{i+1}, Θ_{i+1})` is less than that of `(Y_i, Θ_i)` when the
  `i`-th step has such a surface `V`.

## Implementation notes

* Difficulties (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`) are
  predicates on their values; the inequality is stated for all values satisfying them.
* An irreducible surface of `X_{i+1}` is an irreducible closed subset `V` with
  `topologicalKrullDim V = 2`; "`X_{i+1}` is smooth at `η_V`" is the regularity of the stalk at
  the generic point of `V`, as in `MMP.Fourfold.IsSurfaceGenericBlowupValuation`; the generic
  minimal log discrepancy is `MMP.Fourfold.minimalLogDiscrepancy` at that generic point.
-/

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Proof_lem_oai4_c3_junction_strict_drop

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

/-! ### Valuations along birational morphisms -/

/-- Along a bijective ring map, every valuation of the source is the pull-back of one of the
target. -/
private theorem exists_comap_eq {K L : Type*} [Field K] [Field L] {e : K →+* L}
    (he : Function.Bijective e) (v : Valuation K (WithZero (Multiplicative ℤ))) :
    ∃ w : Valuation L (WithZero (Multiplicative ℤ)), w.comap e = v :=
  ⟨v.comap (RingEquiv.ofBijective e he).symm.toRingHom, by
    ext x
    exact congrArg v ((RingEquiv.ofBijective e he).symm_apply_apply x)⟩

/-- Pull-backs of valuations along a composite of dominant morphisms. -/
private theorem comap_functionFieldMap_comp {A B Z : Scheme.{0}} [IsIntegral A] [IsIntegral B]
    [IsIntegral Z] (a : A ⟶ B) (b : B ⟶ Z) [IsDominant a] [IsDominant b] {c : A ⟶ Z}
    [IsDominant c] (hc : a ≫ b = c) (u : Valuation A.functionField (WithZero (Multiplicative ℤ))) :
    u.comap (functionFieldMap c) = (u.comap (functionFieldMap a)).comap (functionFieldMap b) := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply a b hc t]

/-- Two valuations whose pull-backs along `f ≫ h` and `f' ≫ h` agree have the same pull-backs
along `f` and `f'`, when `h` induces a surjection of function fields. -/
private theorem comap_eq_of_comap_comp_eq {A A' B Z : Scheme.{0}} [IsIntegral A] [IsIntegral A']
    [IsIntegral B] [IsIntegral Z] (f : A ⟶ B) (f' : A' ⟶ B) (h : B ⟶ Z) (c : A ⟶ Z)
    (c' : A' ⟶ Z) (hf : IsDominant f) (hf' : IsDominant f') (hhd : IsDominant h)
    (hcd : IsDominant c) (hcd' : IsDominant c') (hh : Function.Surjective (functionFieldMap h))
    (hc : f ≫ h = c) (hc' : f' ≫ h = c')
    (u : Valuation A.functionField (WithZero (Multiplicative ℤ)))
    (u' : Valuation A'.functionField (WithZero (Multiplicative ℤ)))
    (heq : u.comap (functionFieldMap c) = u'.comap (functionFieldMap c')) :
    u.comap (functionFieldMap f) = u'.comap (functionFieldMap f') := by
  refine MMP.Fourfold.Oai4C1.valuation_eq_of_comap_eq hh ?_
  rw [← comap_functionFieldMap_comp f h hc, ← comap_functionFieldMap_comp f' h hc', heq]

section

variable {T : StabilizedSmallKltTail}

/-! ### Weights and difficulties exist -/

/-- Every valuation exceptional over a model of a terminal chain has a weight. -/
private theorem exists_isValuationWeight (C : TerminalChain T) (N : ℕ) (x : C.ModelIndex)
    {u : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))}
    (hu : MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) u) :
    ∃ w, C.IsValuationWeight N x u w := by
  have hP : MMP.Mori.IsPair (C.modelStructure x) (C.modelBoundary x) :=
    (C.isKltTerminalPair_modelBoundary x).1.1.1.isPair
  obtain ⟨-, n, K, hK, -⟩ := id hP
  obtain ⟨D, hDp, hDv, -⟩ := id hu
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨_, hu, _, ⟨n, D, hDp, hDv.symm,
    MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hDp⟩, rfl⟩

/-- A divisorial valuation whose centre is a surface of a fourfold is exceptional. -/
private theorem isExceptionalValuation_of_isCentre {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsVariety ℂ sX) {V : IrreducibleCloseds X}
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h4 : topologicalKrullDim X = 4) (h2 : topologicalKrullDim (V : Set X) = 2)
    (hc : MMP.Intersection.IsCentre ℂ sX v V) :
    MMP.Intersection.IsExceptionalValuation ℂ sX v := by
  obtain ⟨D, hp, hv, hVD⟩ := hc
  refine ⟨D, hp, hv, ?_⟩
  have := hX.toLocallyOfFiniteType
  rw [MMP.Positivity.DivisorOver.codimension_center]
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  have hcl : (closure {D.f D.E.genericPoint} : Set X) = (V : Set X) := by
    rw [← D.center_eq_closure_genericPoint, hVD]
  rw [hcl, h2, h4] at h3
  induction hco : Order.coheight (D.f D.E.genericPoint) using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    rw [hco] at h3
    have h5 : ((2 + n : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ∞) : WithBot ℕ∞) := by
      rw [WithBot.coe_add]; exact h3
    have h6 : (2 + n : ℕ∞) = 4 := WithBot.coe_injective h5
    have h7 : (2 + n : ℕ) = 4 := by exact_mod_cast h6
    exact_mod_cast (by omega : 2 ≤ n)

/-- Every model of a prepared chain has a difficulty. -/
private theorem exists_isDifficulty (Q : PreparedChain T) (x : Q.ModelIndex) :
    ∃ D, Q.IsDifficulty x D := by
  classical
  obtain ⟨hK, -, hproj, hdim4⟩ := Q.chain.isKltTerminalPair_modelBoundary x.1
  have hvar : MMP.Mori.IsVariety ℂ (Q.chain.modelStructure x.1) := hK.1.1.isPair.1.1
  -- the weights of the valuations with centre of codimension at least three
  have hw : ∀ v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)),
      ∃ w : ℕ, (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧ 3 ≤ codimension Z) →
        Q.chain.IsValuationWeight Q.scale x.1 v w := by
    intro v
    by_cases h : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧ 3 ≤ codimension Z
    · obtain ⟨Z, ⟨D, hDp, hDv, hZ⟩, h3⟩ := h
      obtain ⟨w, hw⟩ := exists_isValuationWeight Q.chain Q.scale x.1
        ⟨D, hDp, hDv, hZ ▸ le_trans (by norm_num) h3⟩
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose w hw using hw
  -- the brackets at the irreducible surfaces
  have hβ : ∀ V : IrreducibleCloseds (Q.chain.model x.1), ∃ β : ℤ,
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 → Q.IsSurfaceBracket x V β := by
    intro V
    by_cases hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2
    · have hw' : ∀ v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)),
          ∃ w : ℕ, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
            Q.chain.IsValuationWeight Q.scale x.1 v w := by
        intro v
        by_cases hc : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V
        · obtain ⟨w, hw⟩ := exists_isValuationWeight Q.chain Q.scale x.1
            (isExceptionalValuation_of_isCentre hvar hdim4 hV hc)
          exact ⟨w, fun _ => hw⟩
        · exact ⟨0, fun h => absurd h hc⟩
      choose w' hw' using hw'
      choose r hr using fun S => TerminalChain.exists_isLabelBranchNumber S x.1 V
      choose d hd using fun S => TerminalChain.exists_isLabelDefault Q.scale S x.1
      exact ⟨_, fun _ => ⟨w', r, d, hw', hr, hd, rfl⟩⟩
    · exact ⟨0, fun h => absurd h hV⟩
  choose β hβ using hβ
  -- the default echo weights and the divisor cycle ranks of the labels
  choose d hd using fun S => TerminalChain.exists_isLabelDefault Q.scale S x.1
  have hρ : ∀ S : Q.chain.Label, ∃ ρ : ℕ,
      (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), Q.chain.IsLabelCentre S x.1 P ∧
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure x.1) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P)) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ¬ Q.chain.IsLabelCentre S x.1 P) ∧
        ρ = 0) := by
    intro S
    by_cases h : ∃ P, Q.chain.IsLabelCentre S x.1 P
    · obtain ⟨P, hP⟩ := h
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure x.1) P
      haveI := isComplexScheme_primeDivisorNormalizationScheme (Q.chain.modelStructure x.1)
        hproj P
      exact ⟨_, Or.inl ⟨P, hP, inferInstance, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨fun P hP => h ⟨P, hP⟩, rfl⟩⟩
  choose ρ hρ using hρ
  exact ⟨_, w, β, d, ρ, hw, hβ, hd, hρ, rfl⟩

/-! ### The generic blowup valuation of a surface -/

/-- An irreducible surface `V` of a fourfold `X` along whose generic point `X` is smooth has
codimension two. -/
private theorem codimension_eq_two {X : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (h4 : topologicalKrullDim X = 4) {V : IrreducibleCloseds X}
    (h2 : topologicalKrullDim (V : Set X) = 2) : codimension V = 2 := by
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  have h3 := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    V.isIrreducible.genericPoint
  rw [V.isIrreducible.genericPoint_closure_eq, V.isClosed.closure_eq, h2, h4] at h3
  induction hco : Order.coheight V.isIrreducible.genericPoint using ENat.recTopCoe with
  | top =>
    rw [hco] at h3
    exact absurd h3 (by decide)
  | coe n =>
    rw [hco] at h3
    have h5 : ((2 + n : ℕ∞) : WithBot ℕ∞) = ((4 : ℕ∞) : WithBot ℕ∞) := by
      rw [WithBot.coe_add]; exact h3
    have h6 : (2 + n : ℕ∞) = 4 := WithBot.coe_injective h5
    have h7 : (2 + n : ℕ) = 4 := by exact_mod_cast h6
    exact_mod_cast (by omega : n = 2)

/-- An irreducible surface `V` of `X_{i+1}` along whose generic point `X_{i+1}` is smooth has a
generic blowup valuation. -/
private theorem exists_isSurfaceGenericBlowupValuation (T : StabilizedSmallKltTail) (i : ℕ)
    (V : IrreducibleCloseds (T.X (i + 1)))
    (hdim : topologicalKrullDim (V : Set (T.X (i + 1))) = 2)
    (hreg : IsRegularLocalRing ((T.X (i + 1)).presheaf.stalk V.isIrreducible.genericPoint)) :
    ∃ v, IsSurfaceGenericBlowupValuation (T.sX (i + 1)) V v := by
  have hS := T.isFourfoldStepDiagram i
  have hX : MMP.Mori.IsNormalVariety ℂ (T.sX (i + 1)) := hS.isNormalVariety_plus
  have h4 : topologicalKrullDim (T.X (i + 1)) = 4 := hS.dim_plus
  haveI : AlgebraicGeometry.IsVariety ℂ (T.sX (i + 1)) := hX.1
  haveI : LocallyOfFiniteType (T.sX (i + 1)) := inferInstance
  haveI : LocallyOfFinitePresentation (T.sX (i + 1)) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := T.sX (i + 1))).mpr inferInstance
  set η := V.isIrreducible.genericPoint with hη
  -- `X_{i+1}` is smooth at `η_V`
  have hsm : η ∈ MMP.Mori.smoothLocus (T.sX (i + 1)) := by
    letI : Algebra ℂ ((T.X (i + 1)).residueField η) :=
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (T.sX (i + 1)).appTop ≫
        (T.X (i + 1)).Γevaluation η).hom.toAlgebra
    have h := (AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk (T.sX (i + 1)) η
      (Algebra.isSeparableExtension_of_perfectField ℂ _)).mpr hreg
    rw [MMP.Mori.smoothLocus_eq_smoothLocus]
    exact Scheme.Hom.mem_smoothLocus.mpr (h.formallySmooth_stalkMap _ _)
  obtain ⟨w, hw, hcent⟩ := MMP.Fourfold.exists_isCentre_of_codimension_eq_two (T.sX (i + 1)) hX.1
    (n := 4) (by exact_mod_cast h4) V (codimension_eq_two (sX := T.sX (i + 1)) h4 hdim) hsm
  refine ⟨w, hX, h4, hdim, hreg, hcent, fun g hg => ?_⟩
  classical
  -- the `𝔪`-adic order of `g` is finite, by Krull's intersection theorem
  have hex : ∃ N : ℕ, g ∉ IsLocalRing.maximalIdeal ((T.X (i + 1)).presheaf.stalk η) ^ N := by
    by_contra h
    push Not at h
    have hmem : g ∈ ⨅ N : ℕ, IsLocalRing.maximalIdeal ((T.X (i + 1)).presheaf.stalk η) ^ N :=
      Ideal.mem_iInf.mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top]
      at hmem
    exact hg hmem
  set N := Nat.find hex with hNdef
  have hN : g ∉ IsLocalRing.maximalIdeal ((T.X (i + 1)).presheaf.stalk η) ^ N := Nat.find_spec hex
  have hmem : ∀ n < N, g ∈ IsLocalRing.maximalIdeal ((T.X (i + 1)).presheaf.stalk η) ^ n :=
    fun n hn => not_not.mp (Nat.find_min hex hn)
  have hN0 : N ≠ 0 := by
    intro h0
    apply hN
    rw [h0, pow_zero, Ideal.one_eq_top]
    trivial
  refine ⟨N - 1, ⟨hmem _ (by omega), fun n hn => ?_⟩, ?_⟩
  · by_contra hlt
    push Not at hlt
    exact hN (Ideal.pow_le_pow_right (by omega : N ≤ n) hn)
  · have h1 := (hw g (N - 1)).2 (hmem _ (by omega))
    have h2 : ¬ w (algebraMap _ (T.X (i + 1)).functionField g) ≤
        WithZero.exp (-((N - 1 + 1 : ℕ) : ℤ)) := fun h => hN (by
      have := (hw g (N - 1 + 1)).1 h
      rwa [show N - 1 + 1 = N by omega] at this)
    have h0 : w (algebraMap _ (T.X (i + 1)).functionField g) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg
    obtain ⟨z, hz⟩ : ∃ z, w (algebraMap _ (T.X (i + 1)).functionField g) = WithZero.exp z :=
      ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hz, WithZero.exp_le_exp] at h1 h2
    rw [hz]
    congr 1
    push_cast at h1 h2 ⊢
    omega

/-! ### Crepancy of junctions -/

section Crepancy

open MMP.Mori

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X}
  {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}

/-- The morphism `p` of a crepant junction is proper. -/
private theorem isProper_p (J : FourfoldCrepantJunction sX B I) : IsProper J.p :=
  isProper_of_isProjectiveMorphism _ J.isProjectiveMorphism

/-- A divisor `(W, g, F)` over the source `Y` of a junction, with `g` proper, as the divisor
`(W, g ≫ p, F)` over `X`. -/
private noncomputable def compDivisorOver (J : FourfoldCrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) (hD : IsProper D.f) : DivisorOver ℂ sX where
  Y := D.Y
  f := D.f ≫ J.p
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc]
  isBirationalMorphism := by
    haveI := D.isIntegral
    haveI := D.isNormal
    haveI := D.isLocallyNoetherian
    haveI := isProper_p J
    exact isBirationalMorphism_comp_of_isBirational J.p D.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism J.isBirationalMorphism)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism)
  E := D.E

private theorem isProper_compDivisorOver (J : FourfoldCrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) (hD : IsProper D.f) : IsProper (compDivisorOver J D hD).f := by
  haveI := isProper_p J
  change IsProper (D.f ≫ J.p)
  infer_instance

/-- Every point lies in every irreducible component of an irreducible space. -/
private theorem mem_irreducibleComponent {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 :=
  W.2.2 (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _) (Set.mem_univ t)

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- If `m • (div ω + Δ)` is the integral divisor `D`, then `ord_Γ ω + coeff_Γ Δ = m⁻¹ coeff_Γ D`:
the coefficients of the `ℝ`-divisor `K + Δ` read off from a Cartier multiple. -/
private theorem ordForm_add_coeff_eq {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sZ] {d : ℕ}
    (ω : RationalPluriForms sZ d 1) (Δ : QDivisor Z)
    {m₀ : ℕ} (hm₀ : 0 < m₀) {D : Divisor Z}
    (hD : Divisor.toQDivisor D = (m₀ : ℤ) • (Divisor.toQDivisor (divisorOfForm ω) + Δ))
    (Γ : MMP.Mori.PrimeDivisor Z) :
    (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor Δ).coeff Γ =
      ∑ _i : Fin 1, (m₀ : ℝ)⁻¹ * (D.coeff Γ : ℝ) := by
  have hc := congrArg (fun G : QDivisor Z => G.coeff Γ) hD
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul,
    DivisorWithCoeffs.coeff_add, zsmul_eq_mul, Int.cast_natCast, coeff_divisorOfForm] at hc
  have hR : (D.coeff Γ : ℝ) = m₀ * (Γ.ordForm ω + (Δ.coeff Γ : ℝ)) := by exact_mod_cast hc
  have hm₀R : (m₀ : ℝ) ≠ 0 := by exact_mod_cast hm₀.ne'
  simp only [Finset.univ_unique, Finset.sum_singleton, QDivisor.coeff_toRDivisor, hR]
  field_simp

/-- **Crepant transfer of log discrepancies.** A log discrepancy of `(W, g, F)` with respect to
`(Y, Θ)` is the log discrepancy of `(W, g ≫ p, F)` with respect to `(X, B)`. -/
private theorem isLogDiscrepancy_compDivisorOver (J : FourfoldCrepantJunction sX B I) {n : ℕ}
    {D : DivisorOver ℂ J.sY} {a : ℝ} (hD : IsProper D.f)
    (h : MMP.Intersection.IsLogDiscrepancy J.sY n (QDivisor.toRDivisor J.Θ) D a) :
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) (compDivisorOver J D hD) a := by
  obtain ⟨hY, -, -, -, ⟨KY, hKY, -⟩, -⟩ := id h
  have hX : IsNormalVariety ℂ sX := J.isKltPair.1.isPair.1
  have hn : n = 4 := by
    have := hKY.topologicalKrullDim_eq.symm.trans J.dim_eq
    exact_mod_cast this
  subst hn
  haveI : CompactSpace X := by
    have := isProper_of_isProjectiveMorphism _ J.isProjectiveVariety_base.isProjective
    exact QuasiCompact.compactSpace_of_compactSpace sX
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType J.sY := hY.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (J.p ≫ sX) := hY.1.toLocallyOfFiniteType
  haveI := J.isBirationalMorphism.isDominant
  obtain ⟨-, n₀, K₀, hK₀, hQ⟩ := J.isKltPair.1.isPair
  have hn₀ : n₀ = 4 := by
    have := hK₀.topologicalKrullDim_eq.symm.trans J.dim_base
    exact_mod_cast this
  subst hn₀
  obtain ⟨ω, hω, -⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK₀
  have hKXle : (divisorOfForm ω).LinearlyEquivalent K₀ := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK₀ hω
    rwa [one_smul] at this
  have hKXcan : (divisorOfForm ω).IsCanonicalDivisor sX 4 := hK₀.of_linearlyEquivalent hKXle
  have hQX : (Divisor.toQDivisor (divisorOfForm ω) + B).IsQCartier :=
    hQ.add_of_linearlyEquivalent hKXle.symm
  obtain ⟨m₀, hm₀, DX, hDX, hDXc⟩ := hQX.exists_pos
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) J.dim_base
  have hω' : pullbackRationalPluriForms sX J.p ω ≠ 0 :=
    MMP.Fourfold.Oai4C1.Main.pullbackRationalPluriForms_ne_zero J.p
      J.isBirationalMorphism.functionFieldMap_bijective hd hω
  have hKYle : (divisorOfForm (pullbackRationalPluriForms sX J.p ω)).LinearlyEquivalent KY := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hKY hω'
    rwa [one_smul] at this
  have hKYcan : (divisorOfForm (pullbackRationalPluriForms sX J.p ω)).IsCanonicalDivisor J.sY 4 :=
    hKY.of_linearlyEquivalent hKYle
  have hcrep := J.isPullback_canonical_add_boundary ω hω (divisorOfForm ω)
    (fun Γ => coeff_divisorOfForm ω Γ) (divisorOfForm (pullbackRationalPluriForms sX J.p ω))
    (fun Γ => coeff_divisorOfForm _ Γ)
  obtain ⟨hBsupp, hpbQ⟩ := hcrep
  obtain ⟨DY, hDY, hDYpb⟩ := hpbQ m₀ hm₀ DX hDX hDXc
  have hDYc : DY.IsCartier := hDYpb.isCartier hDXc
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI : CompactSpace D.Y :=
    (D.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  obtain ⟨L, hL⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hDYc
  have h2 : MMP.Intersection.IsLogDiscrepancy J.sY 4 (QDivisor.toRDivisor J.Θ) D
      (1 + (D.ordPullback (pullbackRationalPluriForms sX J.p ω) : ℝ) -
        ∑ _i : Fin 1, (m₀ : ℝ)⁻¹ * (L.coeff D.E : ℝ)) := by
    refine ⟨hY, hD, _, hω', ⟨_, hKYcan, fun Γ => coeff_divisorOfForm _ Γ⟩, 1,
      fun _ => (m₀ : ℝ)⁻¹, fun _ => DY, fun _ => L, fun _ => hDYc, fun Γ => ?_,
      fun _ => ⟨_, hL⟩, rfl⟩
    exact ordForm_add_coeff_eq _ _ hm₀ hDY Γ
  have heq := MMP.Threefold.Bridges.IsLogDiscrepancy.unique h h2
  refine ⟨hX, isProper_compDivisorOver J D hD, ω, hω,
    ⟨_, hKXcan, fun Γ => coeff_divisorOfForm ω Γ⟩, 1, fun _ => (m₀ : ℝ)⁻¹, fun _ => DX,
    fun _ => L, fun _ => hDXc, fun Γ => ordForm_add_coeff_eq ω B hm₀ hDX Γ,
    fun _ => ⟨_, isPullback_comp hDYpb hL
      (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ J.p) DX)⟩, ?_⟩
  rw [heq]
  congr 3
  change D.E.ordForm (pullbackRationalPluriForms (J.p ≫ sX) D.f
    (pullbackRationalPluriForms sX J.p ω)) =
      D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ J.p) ω)
  rw [pullbackRationalPluriForms_comp J.p D.f
    (IsBirationalMorphism.functionFieldMap_bijective J.isBirationalMorphism)
    (IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism) hd ω]
  rfl

/-- The valuation of `(W, g ≫ p, F)` is that of `(W, g, F)` read on `k(X)` through `p`. -/
private theorem valuation_compDivisorOver (J : FourfoldCrepantJunction sX B I)
    (D : DivisorOver ℂ J.sY) (hD : IsProper D.f) :
    haveI := J.isBirationalMorphism.isDominant
    (compDivisorOver J D hD).valuation = D.valuation.comap (functionFieldMap J.p) := by
  haveI := J.isBirationalMorphism.isDominant
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  ext g
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ J.p) g) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap J.p g))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- Log discrepancies on the source of a crepant junction `p : Y ⟶ X` are those on `X`. -/
private theorem isValuationLogDiscrepancy_comap_p (J : FourfoldCrepantJunction sX B I)
    {u : Valuation J.Y.functionField (WithZero (Multiplicative ℤ))} {a : ℝ}
    (h : IsValuationLogDiscrepancy J.sY J.Θ u a) :
    haveI := J.isBirationalMorphism.isDominant
    IsValuationLogDiscrepancy sX B (u.comap (functionFieldMap J.p)) a := by
  obtain ⟨n, D, hDp, rfl, hD⟩ := h
  exact ⟨n, compDivisorOver J D hDp, isProper_compDivisorOver J D hDp,
    valuation_compDivisorOver J D hDp, isLogDiscrepancy_compDivisorOver J hDp hD⟩

end Crepancy

/-! ### The moves of the bridge -/

/-- At the end of a bridge, `g_{m-1}⁺ ∘ e⁻¹` followed by `h_{m-1}` is `f_i⁺ ∘ p_{i+1}`. -/
private theorem bridge_end_comp {i : ℕ}
    {I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))}
    {I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ)))}
    {J : FourfoldCrepantJunction (T.sX i) (T.B i) I}
    {J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'}
    (β : TerminalBridge i J J') (k : ℕ) (h : β.P.m = k + 1) :
    (β.e.inv ≫ eqToHom (congrArg (modelSeq J.Y β.P.Y) h) ≫ β.P.gp k) ≫ β.P.h k =
      J'.p ≫ T.fp i := by
  have key : ∀ (a : ℕ) (h : a = k + 1) (e : modelSeq J.Y β.P.Y a ≅ J'.Y),
      e.hom ≫ J'.p ≫ T.fp i = modelMap (J.p ≫ T.f i) β.P.πY a →
      (e.inv ≫ eqToHom (congrArg (modelSeq J.Y β.P.Y) h) ≫ β.P.gp k) ≫ β.P.h k =
        J'.p ≫ T.fp i := by
    rintro a rfl e he
    simp only [eqToHom_refl, Category.id_comp, Category.assoc]
    have h2 : (β.P.gp k ≫ β.P.h k : modelSeq J.Y β.P.Y (k + 1) ⟶ T.Z i) =
        e.hom ≫ J'.p ≫ T.fp i := (β.P.πY_eq k (by omega)).symm.trans he.symm
    exact (congrArg (e.inv ≫ ·) h2).trans (e.inv_hom_id_assoc _)
  exact key _ h β.e β.toBase_end_eq.symm

/-- The model reached by a flip of a bridge of a prepared chain is a model of the prepared
chain. -/
private theorem start_le_flipTargetOf (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    (k : Fin (Q.chain.bridge i).P.m) (d : Decidable (k.1 + 1 < (Q.chain.bridge i).P.m)) :
    Q.start ≤ (Q.chain.flipTargetOf i k d).1 := by
  cases d <;> simp only [TerminalChain.flipTargetOf] <;> omega

open StabilizedSmallKltTail.PreparedChain in
/-- A flip of the `i`-th bridge ending inside the bridge, `V_k ⤏ V_{k+1}` with `k + 1 < m_i`,
along which the weight of a valuation drops, strictly lowers the difficulty. -/
private theorem flip_lt (Q : PreparedChain T) {i k : ℕ} (hi : Q.start ≤ i)
    (hk : k < (Q.chain.bridge i).P.m) (hk1 : k + 1 < (Q.chain.bridge i).P.m)
    (v : Valuation ((Q.chain.bridge i).P.model k).functionField (WithZero (Multiplicative ℤ)))
    (v' : Valuation ((Q.chain.bridge i).P.model (k + 1)).functionField
      (WithZero (Multiplicative ℤ)))
    (hcond : haveI := Q.chain.isDominant_flipTargetMapOf i ⟨k, hk⟩ (isTrue hk1)
      haveI := Q.chain.isIntegral_flipBase i ⟨k, hk⟩
      haveI := Q.chain.isDominant_flipSourceMap i ⟨k, hk⟩
      v'.comap (functionFieldMap (Q.chain.flipTargetMapOf i ⟨k, hk⟩ (isTrue hk1))) =
        v.comap (functionFieldMap ((Q.chain.bridge i).P.g k)))
    {w w' : ℕ} (hw : Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k, hk⟩⟩ v w)
    (hw' : Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k + 1, hk1⟩⟩ v' w') (hlt : w' < w)
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i, some ⟨k + 1, hk1⟩⟩, hi⟩ D') : D' < D := by
  have key : ∀ d : Decidable ((⟨k, hk⟩ : Fin (Q.chain.bridge i).P.m).1 + 1 <
      (Q.chain.bridge i).P.m), d = isTrue hk1 →
      (∀ (v : Valuation (Q.chain.model ⟨i, some ⟨k, hk⟩⟩).functionField
          (WithZero (Multiplicative ℤ)))
        (v' : Valuation (Q.chain.model (Q.chain.flipTargetOf i ⟨k, hk⟩ d)).functionField
          (WithZero (Multiplicative ℤ))),
        haveI := Q.chain.isDominant_flipTargetMapOf i ⟨k, hk⟩ d
        haveI := Q.chain.isIntegral_flipBase i ⟨k, hk⟩
        haveI := Q.chain.isDominant_flipSourceMap i ⟨k, hk⟩
        v'.comap (functionFieldMap (Q.chain.flipTargetMapOf i ⟨k, hk⟩ d)) =
          v.comap (functionFieldMap ((Q.chain.bridge i).P.g k)) →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k, hk⟩⟩ v w →
          Q.chain.IsValuationWeight Q.scale (Q.chain.flipTargetOf i ⟨k, hk⟩ d) v' w' → w' < w →
          ∀ D D' : ℤ, Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ D →
            Q.IsDifficulty ⟨Q.chain.flipTargetOf i ⟨k, hk⟩ d, start_le_flipTargetOf Q hi _ d⟩ D' →
            D' < D) → D' < D := by
    rintro d rfl hc
    exact hc v v' hcond w w' hw hw' hlt D D' hD hD'
  exact key _ (Subsingleton.elim _ _)
    ((difficulty_lt_of_valuationWeight_lt Q).2.2 ⟨⟨i, ⟨k, hk⟩⟩, hi⟩)

open StabilizedSmallKltTail.PreparedChain in
/-- The last flip of the `i`-th bridge, `V_{m-1} ⤏ V_m ≅ Y_{i+1}`, along which the weight of a
valuation drops, strictly lowers the difficulty. -/
private theorem flip_end_lt (Q : PreparedChain T) {i k : ℕ} (hi : Q.start ≤ i)
    (hk : k < (Q.chain.bridge i).P.m) (hk1 : ¬ k + 1 < (Q.chain.bridge i).P.m)
    (v : Valuation ((Q.chain.bridge i).P.model k).functionField (WithZero (Multiplicative ℤ)))
    (v' : Valuation (Q.chain.junction (i + 1)).Y.functionField (WithZero (Multiplicative ℤ)))
    (hcond : haveI := Q.chain.isDominant_flipTargetMapOf i ⟨k, hk⟩ (isFalse hk1)
      haveI := Q.chain.isIntegral_flipBase i ⟨k, hk⟩
      haveI := Q.chain.isDominant_flipSourceMap i ⟨k, hk⟩
      v'.comap (functionFieldMap (Q.chain.flipTargetMapOf i ⟨k, hk⟩ (isFalse hk1))) =
        v.comap (functionFieldMap ((Q.chain.bridge i).P.g k)))
    {w w' : ℕ} (hw : Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k, hk⟩⟩ v w)
    (hw' : Q.chain.IsValuationWeight Q.scale ⟨i + 1, none⟩ v' w') (hlt : w' < w)
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩ D') : D' < D := by
  have key : ∀ d : Decidable ((⟨k, hk⟩ : Fin (Q.chain.bridge i).P.m).1 + 1 <
      (Q.chain.bridge i).P.m), d = isFalse hk1 →
      (∀ (v : Valuation (Q.chain.model ⟨i, some ⟨k, hk⟩⟩).functionField
          (WithZero (Multiplicative ℤ)))
        (v' : Valuation (Q.chain.model (Q.chain.flipTargetOf i ⟨k, hk⟩ d)).functionField
          (WithZero (Multiplicative ℤ))),
        haveI := Q.chain.isDominant_flipTargetMapOf i ⟨k, hk⟩ d
        haveI := Q.chain.isIntegral_flipBase i ⟨k, hk⟩
        haveI := Q.chain.isDominant_flipSourceMap i ⟨k, hk⟩
        v'.comap (functionFieldMap (Q.chain.flipTargetMapOf i ⟨k, hk⟩ d)) =
          v.comap (functionFieldMap ((Q.chain.bridge i).P.g k)) →
        ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k, hk⟩⟩ v w →
          Q.chain.IsValuationWeight Q.scale (Q.chain.flipTargetOf i ⟨k, hk⟩ d) v' w' → w' < w →
          ∀ D D' : ℤ, Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ D →
            Q.IsDifficulty ⟨Q.chain.flipTargetOf i ⟨k, hk⟩ d, start_le_flipTargetOf Q hi _ d⟩ D' →
            D' < D) → D' < D := by
    rintro d rfl hc
    exact hc v v' hcond w w' hw hw' hlt D D' hD hD'
  exact key _ (Subsingleton.elim _ _)
    ((difficulty_lt_of_valuationWeight_lt Q).2.2 ⟨⟨i, ⟨k, hk⟩⟩, hi⟩)

end

end Proof_lem_oai4_c3_junction_strict_drop

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral in
open Proof_lem_oai4_c3_junction_strict_drop in
/-- On a prepared chain, let `i ≥ i₀` and let `V ⊆ X_{i+1}` be an irreducible surface contained
in the positive-side bad locus `W_i⁺` of the `i`-th step, such that `X_{i+1}` is smooth at its
generic point `η_V` and `mld_{η_V}(X_{i+1}, B_{i+1}) > 1`. If `D = 𝒟(Y_i, Θ_i)` and
`D' = 𝒟(Y_{i+1}, Θ_{i+1})`, then `D' < D`. -/
@[mmp "lem_oai4_c3_junction_strict_drop"]
public theorem difficulty_succ_lt_of_subset_badLocusPlusAt {i : ℕ} (hi : Q.start ≤ i)
    (V : IrreducibleCloseds (T.X (i + 1))) (hdim : topologicalKrullDim (V : Set (T.X (i + 1))) = 2)
    (hVW : (V : Set (T.X (i + 1))) ⊆ T.badLocusPlusAt i)
    (hreg : IsRegularLocalRing ((T.X (i + 1)).presheaf.stalk V.isIrreducible.genericPoint))
    (hmld : 1 < minimalLogDiscrepancy (T.sX (i + 1)) (T.B (i + 1)) V.isIrreducible.genericPoint)
    {D D' : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩ D') :
    D' < D := by
  classical
  -- the generic blowup valuation `v = v_V` of `V` on `X_{i+1}`, exceptional over the bridge
  obtain ⟨v, hv⟩ := exists_isSurfaceGenericBlowupValuation T i V hdim hreg
  obtain ⟨hexc, hexc'⟩ :=
    TerminalBridge.isExceptionalValuation_of_isSurfaceGenericBlowupValuation (Q.chain.bridge i)
      hVW hmld hv
  -- `v` read on `k(Z_i)`
  set θ := v.comap (functionFieldMap (T.fp i))
  have hπ : MMP.Mori.IsBirationalMorphism ((Q.chain.junction i).p ≫ T.f i) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
      (Q.chain.junction i).isBirationalMorphism
      (T.isFourfoldStepDiagram i).isBirationalMorphism_minus
  have hb : ∀ k ≤ (Q.chain.bridge i).P.m,
      MMP.Mori.IsBirationalMorphism ((Q.chain.bridge i).P.toBase k) :=
    fun k hk => MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_toBase _ hπ hk
  -- the incarnations of `v` on the models `V_k` of the bridge
  have hu : ∀ k (hk : k ≤ (Q.chain.bridge i).P.m),
      ∃ u : Valuation ((Q.chain.bridge i).P.model k).functionField
          (WithZero (Multiplicative ℤ)),
        haveI := (hb k hk).isDominant
        u.comap (functionFieldMap ((Q.chain.bridge i).P.toBase k)) = θ := fun k hk =>
    haveI := (hb k hk).isDominant
    exists_comap_eq (hb k hk).functionFieldMap_bijective θ
  choose u hu using hu
  -- the incarnation of `v` on the junction `Y_{i+1}`
  haveI := (Q.chain.junction (i + 1)).isBirationalMorphism.isDominant
  obtain ⟨u', hu'⟩ := exists_comap_eq
    (Q.chain.junction (i + 1)).isBirationalMorphism.functionFieldMap_bijective v
  have hu'θ : u'.comap
      (functionFieldMap ((Q.chain.junction (i + 1)).p ≫ T.fp i)) = θ := by
    rw [comap_functionFieldMap_comp _ _ rfl, hu']
  have hm0 : 0 ≤ (Q.chain.bridge i).P.m := Nat.zero_le _
  haveI := (hb 0 hm0).isDominant
  haveI := (Q.chain.junction i).isBirationalMorphism.isDominant
  -- the weights of `v` on the models of the bridge
  obtain ⟨w₀, hw₀⟩ := exists_isValuationWeight Q.chain Q.scale ⟨i, none⟩ (u := u 0 hm0) (by
    obtain ⟨_, h⟩ := hexc 0 hm0
    exact h _ (hu 0 hm0))
  have hwk : ∀ k (hk : k < (Q.chain.bridge i).P.m),
      ∃ w, Q.chain.IsValuationWeight Q.scale ⟨i, some ⟨k, hk⟩⟩ (u k hk.le) w := fun k hk =>
    exists_isValuationWeight _ _ _ (by
      obtain ⟨_, h⟩ := hexc k hk.le
      exact h _ (hu k hk.le))
  choose wk hwk using hwk
  obtain ⟨w', hw'⟩ := exists_isValuationWeight Q.chain Q.scale ⟨i + 1, none⟩ (u := u')
    (hexc' u' hu'θ)
  -- the weight drops by at least one between the junctions
  have hdrop : w' + 1 ≤ w₀ := by
    obtain ⟨-, a₀, ha₀, rfl⟩ := id hw₀
    obtain ⟨-, a', ha', rfl⟩ := id hw'
    have h1 := isValuationLogDiscrepancy_comap_p (Q.chain.junction i) ha₀
    have h2 := isValuationLogDiscrepancy_comap_p (Q.chain.junction (i + 1)) ha'
    rw [hu'] at h2
    refine T.difficultyWeight_add_one_le_of_subset_badLocusPlusAt Q.chain Q.isAdmissibleScale i V
      hVW hv ?_ h1 h2
    change v.comap _ = _
    have hc := comap_functionFieldMap_comp (Q.chain.junction i).p (T.f i) rfl
      (u 0 hm0 : Valuation (Q.chain.junction i).Y.functionField (WithZero (Multiplicative ℤ)))
    exact (hu 0 hm0).symm.trans hc
  rcases Nat.eq_zero_or_pos (Q.chain.bridge i).P.m with hm | hm
  · -- no flip: the coefficient decrease is the only move
    exact (difficulty_lt_of_valuationWeight_lt Q).2.1 hi hm (u 0 hm0) u'
      (hu'θ.trans (hu 0 hm0).symm) w₀ w' hw₀ hw' (by omega) D D' hD hD'
  -- the difficulties of the models of the bridge
  have hDk : ∀ k (hk : k < (Q.chain.bridge i).P.m),
      ∃ Dk, Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ Dk := fun k hk => exists_isDifficulty Q _
  choose Dk hDk using hDk
  -- the coefficient decrease
  have hfirst : Dk 0 hm ≤ D ∧ (wk 0 hm < w₀ → Dk 0 hm < D) :=
    ⟨Q.difficulty_le_of_eq_next (x := ⟨⟨i, none⟩, hi⟩) (y := ⟨⟨i, some ⟨0, hm⟩⟩, hi⟩)
      (by simp [TerminalChain.next, hm]) hD (hDk 0 hm),
      fun hlt => (difficulty_lt_of_valuationWeight_lt Q).1 hi hm (u 0 hm0) w₀ (wk 0 hm) hw₀
        (hwk 0 hm) hlt D (Dk 0 hm) hD (hDk 0 hm)⟩
  -- the flips inside the bridge
  have hflip : ∀ k (hk : k + 1 < (Q.chain.bridge i).P.m),
      Dk (k + 1) hk ≤ Dk k (by omega) ∧ (wk (k + 1) hk < wk k (by omega) →
        Dk (k + 1) hk < Dk k (by omega)) := by
    intro k hk
    have hk' : k < (Q.chain.bridge i).P.m := by omega
    refine ⟨Q.difficulty_le_of_eq_next (x := ⟨⟨i, some ⟨k, hk'⟩⟩, hi⟩)
      (y := ⟨⟨i, some ⟨k + 1, hk⟩⟩, hi⟩) (by simp [TerminalChain.next, hk]) (hDk k hk')
      (hDk (k + 1) hk), fun hlt => flip_lt Q hi hk' hk (u k hk'.le) (u (k + 1) hk.le) ?_
        (hwk k hk') (hwk (k + 1) hk) hlt (hDk k hk') (hDk (k + 1) hk)⟩
    have hS := (Q.chain.bridge i).P.isFourfoldStepDiagram k hk'
    haveI : IsIntegral ((Q.chain.bridge i).P.T k) := hS.isNormalVariety_target.1.toIsIntegral
    have hh := MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_h _ hk' (hb k hk'.le)
    exact comap_eq_of_comap_comp_eq (Q.chain.flipTargetMapOf i ⟨k, hk'⟩ (isTrue hk))
      ((Q.chain.bridge i).P.g k) ((Q.chain.bridge i).P.h k)
      ((Q.chain.bridge i).P.toBase (k + 1)) ((Q.chain.bridge i).P.toBase k)
      (Q.chain.isDominant_flipTargetMapOf _ _ _) hS.isBirationalMorphism_minus.isDominant
      hh.isDominant (hb (k + 1) hk.le).isDominant (hb _ hk'.le).isDominant
      (by haveI := hh.isDominant; exact hh.functionFieldMap_bijective.2)
      ((Q.chain.bridge i).P.πY_eq k hk').symm
      ((Q.chain.bridge i).P.modelMap_eq k hk').symm _ _
      ((hu (k + 1) hk.le).trans (hu k hk'.le).symm)
  -- the last flip
  have hend : ∀ k (hk : k < (Q.chain.bridge i).P.m) (hk1 : ¬ k + 1 < (Q.chain.bridge i).P.m),
      D' ≤ Dk k hk ∧ (w' < wk k hk → D' < Dk k hk) := by
    intro k hk hk1
    refine ⟨Q.difficulty_le_of_eq_next (x := ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩)
      (y := ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩) (by simp [TerminalChain.next, hk1])
      (hDk k hk) hD', fun hlt => flip_end_lt Q hi hk hk1 (u k hk.le) u' ?_
        (hwk k hk) hw' hlt (hDk k hk) hD'⟩
    have hS := (Q.chain.bridge i).P.isFourfoldStepDiagram k hk
    haveI : IsIntegral ((Q.chain.bridge i).P.T k) := hS.isNormalVariety_target.1.toIsIntegral
    have hh := MMP.Fourfold.Oai4C1.Main.isBirationalMorphism_h _ hk (hb k hk.le)
    have hc : Q.chain.flipTargetMapOf i ⟨k, hk⟩ (isFalse hk1) ≫ (Q.chain.bridge i).P.h k =
        (Q.chain.junction (i + 1)).p ≫ T.fp i :=
      bridge_end_comp (Q.chain.bridge i) k (by omega)
    exact comap_eq_of_comap_comp_eq (Q.chain.flipTargetMapOf i ⟨k, hk⟩ (isFalse hk1))
      ((Q.chain.bridge i).P.g k) ((Q.chain.bridge i).P.h k)
      ((Q.chain.junction (i + 1)).p ≫ T.fp i) ((Q.chain.bridge i).P.toBase k)
      (Q.chain.isDominant_flipTargetMapOf _ _ _) hS.isBirationalMorphism_minus.isDominant
      hh.isDominant (MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp
        (Q.chain.junction (i + 1)).isBirationalMorphism
        (T.isFourfoldStepDiagram i).isBirationalMorphism_plus).isDominant (hb _ hk.le).isDominant
      (by haveI := hh.isDominant; exact hh.functionFieldMap_bijective.2) hc
      ((Q.chain.bridge i).P.modelMap_eq k hk).symm _ _
      (hu'θ.trans (hu k hk.le).symm)
  -- along the bridge
  have key : ∀ k (hk : k < (Q.chain.bridge i).P.m),
      Dk k hk ≤ D ∧ (wk k hk < w₀ → Dk k hk < D) := by
    intro k
    induction k with
    | zero => exact fun _ => hfirst
    | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨h3, h4⟩ := hflip k hk
      refine ⟨h3.trans h1, fun hlt => ?_⟩
      by_cases hw : wk k (by omega) < w₀
      · exact h3.trans_lt (h2 hw)
      · exact (h4 (by omega)).trans_le h1
  have hlast : (Q.chain.bridge i).P.m - 1 < (Q.chain.bridge i).P.m := by omega
  obtain ⟨h1, h2⟩ := key _ hlast
  obtain ⟨h3, h4⟩ := hend _ hlast (by omega)
  by_cases hw : wk _ hlast < w₀
  · exact h3.trans_lt (h2 hw)
  · exact (h4 (by omega)).trans_le h1

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
