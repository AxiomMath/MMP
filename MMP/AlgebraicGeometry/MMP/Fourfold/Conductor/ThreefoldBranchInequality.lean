module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.SingularPointValuations
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.BranchBound
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.ProductWithLine
import MMP.AlgebraicGeometry.Divisor.ProductLineQFactorial
import MMP.AlgebraicGeometry.Singularities.EtaleDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.IndexBound.ProductBoundaryNormalization
import MMP.AlgebraicGeometry.Singularities.Terminal.ProductLineSingularCurves
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The threefold branch inequality

Let `p : Y ⟶ X` be a projective birational morphism of normal projective complex threefolds,
with `Y` `ℚ`-factorial, and let `(Y, Θ)` be an effective terminal pair. Let
`Q = Q_1 ∪ ⋯ ∪ Q_m` be a reduced union of distinct prime divisors of `Y` with positive
coefficients in `Θ`, such that `p(Q)` is finite. Then every irreducible curve `C ⊆ Q` has branch
count `r_C ≥ 1`, only finitely many have `r_C > 1`, and
`∑_{C ⊆ Q} (r_C - 1) ≤ ∑_j ρ^□(Q_j^ν) + #{v | c_Y(v) a closed point of Q, a(v; Y, Θ) < 2}`,
where `v` runs over the normalized divisorial valuations of `ℂ(Y)` and the count lies in `ℕ∞`.

## Main results

* `MMP.Fourfold.sum_boundaryBranchCount_sub_one_le_of_threefold`: the threefold branch
  inequality.

## Implementation notes

* The reduced union `Q` is a finite set of prime divisors of `Y`, as for
  `MMP.Fourfold.boundaryBranchCount`, which is `r_C`; `C ⊆ Q` means containment in the union of
  the supports, and irreducible curves are irreducible closed subsets of dimension one.
* Since every term `r_C - 1` is a natural number, the left side is the finitely supported sum
  `∑ᶠ` of the truncated differences in `ℕ`; its support is finite by the first two conclusions.
  The inequality is in `ℕ∞`, where the count of valuations is `Set.encard`.
* `ρ^□(Q_j^ν)` is `MMP.Fourfold.boxedSurfaceRank` of
  `MMP.Fourfold.primeDivisorNormalizationScheme`, over `ℂ` through `Q_j^ν ⟶ Y`, a complex scheme by
  `MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`.
* Centres are `MMP.Intersection.IsCentre`, which includes that `v` is a normalized divisorial
  valuation; a closed point `y` of `Q` as centre means that the centre is `{y}` with `y ∈ Q`.
  Log discrepancies are `MMP.Fourfold.IsValuationLogDiscrepancy`.
* A boundary of a `ℚ`-divisor (`MMP.Mori.QDivisor`) is rational; effectivity is `0 ≤ Θ` and
  terminality of `(Y, Θ)` is `MMP.Fourfold.IsKltTerminalPair`.

## References

* [Termination for projective log canonical fourfolds with rational boundary (OpenAI, 2026)]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace Proof_thm_mmp_indexb_branch_inequality

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori

/-- The structure morphism of the complex projective line. -/
local notation "ℓ" => projectiveLine ℂ ↘ Spec (CommRingCat.of ℂ)

/-- A finitely supported sum of natural numbers is at most a finitely supported sum of
nonnegative integers when an injective map carries every nonzero term to an equal term. -/
private lemma natCast_finsum_le_finsum {α β : Type*} {P : α → Prop} {R : β → Prop} {f : α → ℕ}
    {g : β → ℤ} (φ : α → β) (hf : {a | P a ∧ f a ≠ 0}.Finite)
    (hg : {b | R b ∧ g b ≠ 0}.Finite) (hg0 : ∀ b, R b → 0 ≤ g b)
    (hφ : ∀ a, P a → f a ≠ 0 → R (φ a) ∧ g (φ a) = f a)
    (hinj : ∀ a, P a → ∀ a', P a' → φ a = φ a' → a = a') :
    ((∑ᶠ (a) (_ : P a), f a : ℕ) : ℤ) ≤ ∑ᶠ (b) (_ : R b), g b := by
  classical
  rw [finsum_cond_eq_sum_of_cond_iff f (t := hf.toFinset) fun {a} ha => by simp [ha],
    finsum_cond_eq_sum_of_cond_iff g (t := hg.toFinset) fun {b} hb => by simp [hb],
    Nat.cast_sum]
  have hinj' : Set.InjOn φ ↑hf.toFinset := fun a ha a' ha' h => by
    simp only [Finset.coe_sort_coe, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at ha ha'
    exact hinj a ha.1 a' ha'.1 h
  calc ∑ a ∈ hf.toFinset, (f a : ℤ) = ∑ a ∈ hf.toFinset, g (φ a) :=
        Finset.sum_congr rfl fun a ha => by
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at ha
          exact (hφ a ha.1 ha.2).2.symm
    _ = ∑ b ∈ hf.toFinset.image φ, g b := (Finset.sum_image hinj').symm
    _ ≤ ∑ b ∈ hg.toFinset, g b := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b hb _ => ?_
        · intro b hb
          simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hb ⊢
          obtain ⟨a, ⟨ha, hfa⟩, rfl⟩ := hb
          obtain ⟨hR, hg'⟩ := hφ a ha hfa
          exact ⟨hR, by rw [hg']; exact_mod_cast hfa⟩
        · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hb
          exact hg0 b hb.1

/-- A finite sum of natural numbers, each bounded by the cardinality of one of pairwise disjoint
subsets of a set `S`, is bounded by the cardinality of `S`. -/
private lemma finsum_mem_le_encard {ι α : Type*} {s : Set ι} (hs : s.Finite) (b : ι → ℕ)
    (Ξ : ι → Set α) {S : Set α} (hΞS : ∀ i ∈ s, Ξ i ⊆ S)
    (hb : ∀ i ∈ s, (b i : ℕ∞) ≤ (Ξ i).encard)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ξ i) (Ξ j)) :
    ((∑ᶠ i ∈ s, b i : ℕ) : ℕ∞) ≤ S.encard := by
  classical
  rw [← hs.coe_toFinset, finsum_mem_coe_finset, Nat.cast_sum]
  have key : ∀ t : Finset ι, (↑t : Set ι) ⊆ s →
      ∑ i ∈ t, (b i : ℕ∞) ≤ (⋃ i ∈ t, Ξ i).encard := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      intro hts
      have has : a ∈ s := hts (by simp)
      have hts' : (↑t : Set ι) ⊆ s := fun x hx => hts (by simp [hx])
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert, Set.encard_union_eq]
      · exact add_le_add (hb a has) (ih hts')
      · rw [Set.disjoint_iUnion₂_right]
        intro j hj
        exact hdisj a has j (hts' hj) fun h => ha (h ▸ hj)
  refine (key _ (by simp)).trans (Set.encard_le_encard ?_)
  intro x hx
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset] at hx
  obtain ⟨i, hi, hx⟩ := hx
  exact hΞS i hi hx

/-- In a Jacobson space, a point whose closure is finite is closed. -/
private lemma isClosed_singleton_of_finite_closure {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {x : T} (h : (closure {x} : Set T).Finite) : IsClosed ({x} : Set T) := by
  have hc : IsClosed (closure {x} ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closure {x} ∩ closedPoints T)]
    exact (h.subset Set.inter_subset_left).isClosed_biUnion fun y hy => hy.2
  have := JacobsonSpace.closure_inter_closedPoints (isClosed_closure (s := ({x} : Set T)))
  rw [hc.closure_eq] at this
  have hx : x ∈ closure {x} ∩ closedPoints T := by rw [this]; exact subset_closure rfl
  exact hx.2

/-- A closed subset of a quasi-sober `T₀` space all of whose points `x` satisfy
`dim closure {x} ≤ n` has dimension at most `n`. -/
private lemma topologicalKrullDim_le_of_forall_closure {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] {W : Set X} (hW : IsClosed W) {n : WithBot ℕ∞}
    (h : ∀ x ∈ W, topologicalKrullDim (closure {x} : Set X) ≤ n) :
    topologicalKrullDim W ≤ n := by
  haveI : QuasiSober W := hW.isClosedEmbedding_subtypeVal.quasiSober
  refine MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun C hC => ?_
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  haveI : QuasiSober C := hCc.isClosedEmbedding_subtypeVal.quasiSober
  have hgen := hC.1.isGenericPoint_genericPoint hCc
  set c := hC.1.genericPoint
  let g : C → (closure {c.1} : Set X) := fun a =>
    ⟨a.1.1, specializes_iff_mem_closure.mp ((hgen.specializes a.2).map continuous_subtype_val)⟩
  refine (MMP.Flips.topologicalKrullDim_le_of_specializes_imp_eq (f := g) (by fun_prop)
    fun a b _ hab => ?_).trans (h c.1 c.2)
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val hab :))

/-- For a closed point `x` of a normal complex variety `X`, the fibre `{x} × ℙ¹` of the first
projection `X × ℙ¹ ⟶ X` has dimension one. -/
private lemma topologicalKrullDim_pointSettingCurve {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (x : X) (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDim (pointSettingCurve sX x) = 1 := by
  set sL := projectiveLine ℂ ↘ Spec (.of ℂ)
  set i := X.fromSpecResidueField x
  haveI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  haveI := hX.1
  haveI : IsNormal (Spec (X.residueField x)) := isNormal_spec_of_isIntegrallyClosed _
  have hg : IsNormalVariety ℂ (i ≫ sX) :=
    ⟨(isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
      inferInstance⟩
  have hb := (product_line_basic (i ≫ sX) sL hg (Or.inl ⟨Iso.refl _, by simp [sL]⟩)).1
  let ψ := pullbackRightPullbackFstIso sX sL i
  let φ := ψ.inv ≫ pullback.snd i (pullback.fst sX sL)
  have hφ : Set.range φ = pointSettingCurve sX x := by
    have hsurj : Function.Surjective ψ.inv.base := (inferInstance : Surjective ψ.inv).surj
    simp only [φ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ]
    rw [Scheme.Pullback.range_snd, Scheme.range_fromSpecResidueField]
    rfl
  let e := φ.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hφ)
  rw [← IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph, hb.2.2.2.1]
  change topologicalKrullDim (PrimeSpectrum (X.residueField x)) + 1 = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  rfl

/-- Over a closed finite set `F` of a normal complex variety `X`, the preimage of `F` in
`X × ℙ¹` has dimension at most one. -/
private lemma topologicalKrullDim_preimage_fst_le_one {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) {F : Set X} (hF : F.Finite) (hFc : IsClosed F) :
    topologicalKrullDim ((pullback.fst sX ℓ).base ⁻¹' F) ≤ 1 := by
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  refine topologicalKrullDim_le_of_forall_closure
    (hFc.preimage (pullback.fst sX ℓ).base.hom.continuous) fun w hw => ?_
  have hw' : IsClosed {(pullback.fst sX ℓ).base w} := isClosed_singleton_of_finite_closure
    (hF.subset (hFc.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hw)))
  have hwsub : closure {w} ⊆ pointSettingCurve sX ((pullback.fst sX ℓ).base w) :=
    closure_minimal (Set.singleton_subset_iff.mpr (Set.mem_singleton _))
      (hw'.preimage (pullback.fst sX ℓ).base.hom.continuous)
  exact (Topology.IsEmbedding.inclusion hwsub).isInducing.topologicalKrullDim_le.trans
    (topologicalKrullDim_pointSettingCurve hX _ hw').le

/-- Combining the bound `L ≤ A + B` in `ℤ` with `B ≤ E` in `ℕ∞`. -/
private lemma natCast_le_add_of_intCast_le {L A A' B : ℕ} {E : ℕ∞} (h : (L : ℤ) ≤ A' + B)
    (hA : A' = A) (hB : (B : ℕ∞) ≤ E) : (L : ℕ∞) ≤ A + E := by
  subst hA
  have : L ≤ A' + B := by exact_mod_cast h
  calc (L : ℕ∞) ≤ ((A' + B : ℕ) : ℕ∞) := by exact_mod_cast this
    _ = A' + B := by push_cast; rfl
    _ ≤ A' + E := by gcongr

/-- The irreducible curves contained in the singular locus of `Y`. -/
private abbrev SingularCurve {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) : Type :=
  {T : IrreducibleCloseds Y // (T : Set Y) ⊆ (singularLocus sY : Set Y) ∧
    topologicalKrullDim (T : Set Y) = 1}

private theorem solution :
    ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (hXproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXdim : topologicalKrullDim X = 3)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) (hpproj : IsProjectiveMorphism p)
    (hpbir : IsBirationalMorphism p)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 3)
    (hYQ : IsQFactorial sY)
    (Θ : QDivisor Y) (hΘ0 : 0 ≤ Θ) (hΘ : IsKltTerminalPair sY Θ)
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) (hQ : ∀ S ∈ Q, 0 < Θ S)
    (hpQ : (p.base '' ⋃ S ∈ Q, (S.support : Set Y)).Finite),
    (∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) → 1 ≤ boundaryBranchCount Q C) ∧
      {C : IrreducibleCloseds Y | topologicalKrullDim (C : Set Y) = 1 ∧
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ 1 < boundaryBranchCount Q C}.Finite ∧
      ((∑ᶠ (C : IrreducibleCloseds Y) (_ : topologicalKrullDim (C : Set Y) = 1 ∧
          (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)), (boundaryBranchCount Q C - 1) : ℕ) : ℕ∞) ≤
        ((∑ S ∈ Q,
            letI := primeDivisorNormalizationOver sY S
            haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
            boxedSurfaceRank (primeDivisorNormalizationScheme S) : ℕ) : ℕ∞) +
          {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
            (∃ (Z : IrreducibleCloseds Y) (y : Y), (Z : Set Y) = {y} ∧
              y ∈ ⋃ S ∈ Q, (S.support : Set Y) ∧ MMP.Intersection.IsCentre ℂ sY v Z) ∧
            ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.encard := by
  intro X Y _ _ _ _ _ _ sX sY hX hXproj hXdim p hp hpproj hpbir hYproj hYdim hYQ Θ hΘ0 hΘ
    Q hQ hpQ
  subst hp
  have hL : (∃ e : projectiveLine ℂ ≅ projectiveLine ℂ, e.hom ≫ ℓ = ℓ) ∨
      ∃ e : projectiveLine ℂ ≅ 𝔸(PUnit.{1}; Spec (.of ℂ)),
        e.hom ≫ (𝔸(PUnit.{1}; Spec (.of ℂ)) ↘ Spec (.of ℂ)) = ℓ :=
    Or.inl ⟨Iso.refl _, by simp⟩
  have hYn : IsNormalVariety ℂ (p ≫ sX) := hYQ.1
  have hbY := product_line_basic (p ≫ sX) ℓ hYn hL
  have hbX := product_line_basic sX ℓ hX hL
  -- `(Y, 0)` is terminal
  obtain ⟨n, K, hK, -⟩ := hΘ.1.1.isPair.2
  have hYt : IsTerminalVariety (p ≫ sX) :=
    (IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus hΘ
      (isQCartier_of_isQFactorial _ hYQ Θ) hK (isQCartier_of_isQFactorial _ hYQ _)).1
  obtain ⟨_, _, hYt'⟩ := hYt.pullback_projectiveLine
  haveI : IsLocallyNoetherian (pullback (p ≫ sX) ℓ) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX)
      hbY.1.2.2.1.1.toLocallyOfFiniteType (isLocallyNoetherian_Spec.mpr inferInstance)
  haveI : IsIntegral (pullback sX ℓ) := hbX.1.2.2.1.1.toIsIntegral
  haveI : IsNormal (pullback sX ℓ) := hbX.1.2.2.1.2
  haveI : IsLocallyNoetherian (pullback sX ℓ) :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.fst sX ℓ ≫ sX)
      hbX.1.2.2.1.1.toLocallyOfFiniteType (isLocallyNoetherian_Spec.mpr inferInstance)
  -- the product of `p` with `ℙ¹`
  obtain ⟨hp'proj, hp'bir, -, -⟩ := hbX.2.2.2 p hYn hpproj hpbir
  -- the divisors `S × ℙ¹`
  obtain ⟨hY'n, hY'dim, Φ, hΦ, -, hcurve, hcinj, hVpos, hCpos, hrank⟩ :=
    exists_embedding_primeDivisor_pullback_projectiveLine (p ≫ sX) hYn hYdim Q
  have hU' : ⋃ S ∈ Q.map Φ, ((S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0}))) =
      (pullback.fst (p ≫ sX) ℓ).base ⁻¹' ⋃ S ∈ Q, (S.support : Set Y) := by
    ext z; simp [hΦ]
  have hBB := one_le_boundaryBranchCount_and_finite_setOf_one_lt _ hY'n hY'dim (Q.map Φ)
  have hXdim' : topologicalKrullDim ↥(pullback sX ℓ : Scheme.{0}) = 4 := by
    rw [hbX.1.2.2.2.1, hXdim]; rfl
  have hYQ' : IsQFactorial (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX) :=
    (isQFactorial_pullback_line (p ≫ sX) ℓ hYn hL).2 hYQ
  have hYproj' : MMP.Mori.IsProjectiveVariety ℂ (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX) :=
    hbY.1.2.2.2.2.1 ⟨Iso.refl _, by simp⟩ hYproj
  have hXproj' : MMP.Mori.IsProjectiveVariety ℂ (pullback.fst sX ℓ ≫ sX) :=
    hbX.1.2.2.2.2.1 ⟨Iso.refl _, by simp⟩ hXproj
  have hpQ' : topologicalKrullDim
      ((pullback.map (p ≫ sX) ℓ sX ℓ p (𝟙 _) (𝟙 _) (by simp) (by simp)).base ''
        ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0}))) ≤ 1 := by
    have hpQc : IsClosed (p.base '' ⋃ S ∈ Q, (S.support : Set Y)) := by
      haveI := isProper_of_isProjectiveMorphism p hpproj
      exact p.isClosedMap _
        (Q.finite_toSet.isClosed_biUnion fun S _ => S.idealSheaf.support.isClosed)
    have hcomm : pullback.map (p ≫ sX) ℓ sX ℓ p (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
        pullback.fst sX ℓ = pullback.fst (p ≫ sX) ℓ ≫ p := by simp
    have hsub : (pullback.map (p ≫ sX) ℓ sX ℓ p (𝟙 _) (𝟙 _) (by simp) (by simp)).base ''
        ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) ⊆
        (pullback.fst sX ℓ).base ⁻¹' (p.base '' ⋃ S ∈ Q, (S.support : Set Y)) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hU'] at hz
      refine ⟨_, hz, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le.trans
      (topologicalKrullDim_preimage_fst_le_one hX hpQ hpQc)
  obtain ⟨To, hTo, hbound⟩ := sum_boundaryBranchCount_sub_one_le_sum_curveLocalSystemRank
    (pullback.fst sX ℓ ≫ sX) (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX) hbX.1.2.2.1 hXproj' hXdim'
    _ (by simp) hp'proj hp'bir hYproj' hY'dim hYQ' hYt' (Q.map Φ) hpQ'
  classical
  -- the surfaces `C × ℙ¹`
  let φ : IrreducibleCloseds Y → IrreducibleCloseds ↥(pullback (p ≫ sX) ℓ : Scheme.{0}) :=
    fun C => if h : topologicalKrullDim (C : Set Y) = 1 ∧
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) then
      ⟨(pullback.fst (p ≫ sX) ℓ).base ⁻¹' C, (hcurve C h.1 h.2).1, (hcurve C h.1 h.2).2.1⟩
    else ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hφ : ∀ (C : IrreducibleCloseds Y) (h : topologicalKrullDim (C : Set Y) = 1 ∧
      (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)),
      (φ C : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) =
        (pullback.fst (p ≫ sX) ℓ).base ⁻¹' C := fun C h => by
    simp only [φ, dif_pos h]
    rfl
  have hmaps : ∀ (C : IrreducibleCloseds Y) (h : topologicalKrullDim (C : Set Y) = 1 ∧
      (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)),
      topologicalKrullDim (φ C : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) = 2 ∧
      (φ C : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) ⊆
        ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) ∧
      boundaryBranchCount (Q.map Φ) (φ C : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) =
        boundaryBranchCount Q C := fun C h => by
    rw [hφ C h, hU']
    exact ⟨(hcurve C h.1 h.2).2.2.1, Set.preimage_mono h.2, (hcurve C h.1 h.2).2.2.2⟩
  have hinjφ : ∀ C : IrreducibleCloseds Y, (topologicalKrullDim (C : Set Y) = 1 ∧
      (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) → ∀ C' : IrreducibleCloseds Y,
      (topologicalKrullDim (C' : Set Y) = 1 ∧ (C' : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)) →
      φ C = φ C' → C = C' := fun C h C' h' he =>
    hcinj C C' h.1 h'.1 (by rw [← hφ C h, ← hφ C' h', he])
  have hfin2 : {C : IrreducibleCloseds Y | topologicalKrullDim (C : Set Y) = 1 ∧
      (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ 1 < boundaryBranchCount Q C}.Finite :=
    by
    refine Set.Finite.of_injOn (f := φ) ?_
      (fun C hC C' hC' he => hinjφ C ⟨hC.1, hC.2.1⟩ C' ⟨hC'.1, hC'.2.1⟩ he) hBB.2
    intro C hC
    obtain ⟨h1, h2, h3⟩ := hmaps C ⟨hC.1, hC.2.1⟩
    exact ⟨h1, h2, by rw [h3]; exact hC.2.2⟩
  refine ⟨hCpos, hfin2, ?_⟩
  -- the singular curves `y × ℙ¹`
  obtain ⟨⟨hSfin, hScl⟩, hcurves, -⟩ :=
    IsTerminalVariety.singularLocus_product_projectiveLine_curves hYn hYdim hYt
      ⟨⋃ S ∈ Q, (S.support : Set Y),
        Q.finite_toSet.isClosed_biUnion fun S _ => S.idealSheaf.support.isClosed⟩
  have hex : ∀ T : SingularCurve (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX), ∃ y : Y,
      (T.1 : Set _) ⊆ ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) →
        y ∈ (singularLocus (p ≫ sX) : Set Y) ∩ ⋃ S ∈ Q, (S.support : Set Y) ∧
          pointSettingCurve (p ≫ sX) y = (T.1 : Set _) := by
    intro T
    by_cases hT : (T.1 : Set _) ⊆
        ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0}))
    · rw [hU'] at hT
      obtain ⟨y, hy, he⟩ := (Set.ext_iff.mp hcurves T.1).mp
        ⟨T.1.isClosed, T.1.isIrreducible, T.2.2, Set.subset_inter T.2.1 hT⟩
      exact ⟨y, fun _ => ⟨hy, he⟩⟩
    · exact ⟨Classical.arbitrary Y, fun h => absurd h hT⟩
  choose yT hyT using hex
  have hyinj : ∀ T T' : SingularCurve (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX),
      (T.1 : Set _) ⊆ ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) →
      (T'.1 : Set _) ⊆ ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) →
      yT T = yT T' → T = T' := fun T T' hT hT' he => by
    have h1 := (hyT T hT).2
    have h2 := (hyT T' hT').2
    rw [he] at h1
    exact Subtype.ext (SetLike.coe_injective (h1.symm.trans h2))
  refine natCast_le_add_of_intCast_le ((natCast_finsum_le_finsum φ
    (hfin2.subset fun C hC => ⟨hC.1.1, hC.1.2, by have := hC.2; omega⟩)
    (hBB.2.subset fun V hV => ⟨hV.1.1, hV.1.2, by
      have := hVpos V hV.1.1 hV.1.2; have := hV.2; omega⟩)
    (fun V hV => by have := hVpos V hV.1 hV.2; omega)
    (fun C hC _ => ⟨⟨(hmaps C hC).1, (hmaps C hC).2.1⟩, by
      rw [(hmaps C hC).2.2]; have := hCpos C hC.1 hC.2; omega⟩) hinjφ).trans hbound) ?_ ?_
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun S hS => ?_
    obtain ⟨_, h⟩ := hrank hYproj S hS
    exact h
  refine finsum_mem_le_encard (s := {T : SingularCurve (pullback.fst (p ≫ sX) ℓ ≫ p ≫ sX) |
      (T.1 : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0})) ⊆
        ⋃ S ∈ Q.map Φ, (S.support : Set ↥(pullback (p ≫ sX) ℓ : Scheme.{0}))})
    (Set.Finite.of_injOn (f := yT) (t := (singularLocus (p ≫ sX) : Set Y))
      (fun T hT => (hyT T hT).1.1) (fun T hT T' hT' he => hyinj T T' hT hT' he) hSfin)
    (fun T => curveLocalSystemRank _ (To T))
    (fun T => {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      (∃ Z : IrreducibleCloseds Y, (Z : Set Y) = {yT T} ∧
        MMP.Intersection.IsCentre ℂ (p ≫ sX) v Z) ∧
      IsValuationLogDiscrepancy (p ≫ sX) 0 v 2 ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy (p ≫ sX) Θ v a ∧ a < 2}) ?_ ?_ ?_
  · rintro T hT v ⟨⟨Z, hZ, hc⟩, -, ha⟩
    exact ⟨⟨Z, yT T, hZ, (hyT T hT).1.2, hc⟩, ha⟩
  · intro T hT
    obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.mp (hyT T hT).1.2
    exact le_encard_setOf_isCentre_singleton (p ≫ sX) hYQ hYproj hYdim Θ hΘ0 hΘ (yT T)
      (hyT T hT).1.1 (hScl _ (hyT T hT).1.1) ⟨S, hQ S hS, hyS⟩ T.1 (hyT T hT).2.symm (To T)
      (hTo T)
  · intro T hT T' hT' hne
    refine Set.disjoint_left.mpr fun v hv hv' => hne (hyinj T T' hT hT' ?_)
    obtain ⟨⟨Z, hZ, D, -, hDv, rfl⟩, -⟩ := hv
    obtain ⟨⟨Z', hZ', D', -, hD'v, rfl⟩, -⟩ := hv'
    rw [MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hYn.1 (hDv.symm.trans hD'v)] at hZ
    exact Set.singleton_injective (hZ.symm.trans hZ')

end Proof_thm_mmp_indexb_branch_inequality

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **Threefold branch inequality.** Let `p : Y ⟶ X` be a projective birational morphism of
normal projective complex threefolds, with `Y` `ℚ`-factorial and `(Y, Θ)` an effective terminal
pair. Let `Q` be a finite set of prime divisors of `Y` with positive coefficients in `Θ`, whose
union has finite image under `p`. Then every irreducible curve `C ⊆ Q` has
`1 ≤ r_C = boundaryBranchCount Q C`, only finitely many have `1 < r_C`, and
`∑_{C ⊆ Q} (r_C - 1) ≤ ∑_{S ∈ Q} ρ^□(S^ν) + #{v | c_Y(v) = {y}, y ∈ Q, a(v; Y, Θ) < 2}`
in `ℕ∞`, with `ρ^□(S^ν) = MMP.Fourfold.boxedSurfaceRank` of the normalization of `S` and `v`
over the normalized divisorial valuations of `ℂ(Y)`. -/
@[mmp "thm_mmp_indexb_branch_inequality"]
public theorem sum_boundaryBranchCount_sub_one_le_of_threefold
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ))
    (hX : IsNormalVariety ℂ sX) (hXproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXdim : topologicalKrullDim X = 3)
    (p : Y ⟶ X) (hp : p ≫ sX = sY) (hpproj : IsProjectiveMorphism p)
    (hpbir : IsBirationalMorphism p)
    (hYproj : MMP.Mori.IsProjectiveVariety ℂ sY) (hYdim : topologicalKrullDim Y = 3)
    (hYQ : IsQFactorial sY)
    (Θ : QDivisor Y) (hΘ0 : 0 ≤ Θ) (hΘ : IsKltTerminalPair sY Θ)
    (Q : Finset (MMP.Mori.PrimeDivisor Y)) (hQ : ∀ S ∈ Q, 0 < Θ S)
    (hpQ : (p.base '' ⋃ S ∈ Q, (S.support : Set Y)).Finite) :
    (∀ C : IrreducibleCloseds Y, topologicalKrullDim (C : Set Y) = 1 →
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) → 1 ≤ boundaryBranchCount Q C) ∧
      {C : IrreducibleCloseds Y | topologicalKrullDim (C : Set Y) = 1 ∧
        (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ 1 < boundaryBranchCount Q C}.Finite ∧
      ((∑ᶠ (C : IrreducibleCloseds Y) (_ : topologicalKrullDim (C : Set Y) = 1 ∧
          (C : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y)), (boundaryBranchCount Q C - 1) : ℕ) : ℕ∞) ≤
        ((∑ S ∈ Q,
            letI := primeDivisorNormalizationOver sY S
            haveI := isComplexScheme_primeDivisorNormalizationScheme sY hYproj S
            boxedSurfaceRank (primeDivisorNormalizationScheme S) : ℕ) : ℕ∞) +
          {v : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
            (∃ (Z : IrreducibleCloseds Y) (y : Y), (Z : Set Y) = {y} ∧
              y ∈ ⋃ S ∈ Q, (S.support : Set Y) ∧ MMP.Intersection.IsCentre ℂ sY v Z) ∧
            ∃ a : ℝ, IsValuationLogDiscrepancy sY Θ v a ∧ a < 2}.encard :=
              by revert X Y sX sY hX hXproj hXdim p hp hpproj hpbir hYproj hYdim hYQ Θ hΘ0 hΘ Q hQ hpQ; first | exact Proof_thm_mmp_indexb_branch_inequality.solution | exact Proof_thm_mmp_indexb_branch_inequality.solution _ | exact Proof_thm_mmp_indexb_branch_inequality.solution _ _ | exact Proof_thm_mmp_indexb_branch_inequality.solution _ _ _ | exact Proof_thm_mmp_indexb_branch_inequality.solution _ _ _ _

end MMP.Fourfold
