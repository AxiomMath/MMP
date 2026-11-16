module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Positivity.Kleiman.RhoOneCurveTest
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.Flip.RealCanonicalRationalWitness
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Surface.ContractionChainBound
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Flip.DivisorNormalizationLift
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# Termination of globally projective real canonical threefold flips

Let `(X₀, B₀) ⟶ Z₀ ⟵ (X₁, B₁) ⟶ ⋯` be an extremal real flip sequence of real canonical
complex threefold pairs with all boundary coefficients below one, all of whose models and
contraction targets are projective. We show that it is finite, by induction on the number of
components of the boundary.

For the empty boundary the canonical difficulty drops at every step. Otherwise let `b > 0` be the
largest coefficient and `G_i` the reduced divisor of the components of `B_i` of coefficient `b`.
In an infinite sequence the difficulty is eventually constant, so eventually no flipped curve lies
in `G_{i+1}`; the morphisms of normalizations of the components of `G_i` along the flips then show
that eventually no flipping curve lies in `G_i` either. A sign argument in relative Picard number
one, together with the transfer of numerically trivial divisors across a flip, shows that `G_i`
is then numerically trivial over `Z_i` on both sides of the flip. Hence `B_i - b G_i` is the
boundary of an infinite extremal real canonical flip sequence with fewer components, a
contradiction.

## Main results

* `MMP.Fourfold.RealFlipSequence.n_ne_top_of_isRealCanonicalPair`

## Implementation notes

Relative Picard number one, ampleness and intersection numbers are those of
`MMP.Fourfold.IsRealFlipStep`, that is, of `MMP.Flips`. The numerical triviality of `G_i` over
`Z_i` is obtained without the disjointness of `G_i` from the flipping curves: if `G_i` were
negative on the flipping ray it would contain every flipping curve; if it were positive, then
`K + B⁰ + λ G_i` would be numerically trivial over `Z_i` for a rational canonical witness `B⁰` and
some `λ > 0`, so its strict transform would be numerically trivial over `Z_i` too (FA 18), which
is impossible since `K⁺ + B⁰⁺` is ample over `Z_i` and `G⁺` is not negative on the flipped curves.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.13
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

section Helpers

open TopologicalSpace

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X}

/-! ### Tails of a flip sequence with a new boundary -/

section Tail

/-- The sequence `X_N ⟶ Z_N ⟵ X_{N+1} ⟶ ⋯` of an infinite extremal real flip sequence, with the
boundaries replaced by divisors `B'_i` for which the diagrams are still steps. -/
private noncomputable def tail (σ : RealFlipSequence sX K B) (N : ℕ)
    (B' : ∀ i, RDivisor (modelSeq X σ.Y i))
    (hstep : ∀ i ≥ N, IsRealFlipStep (modelStr sX σ.sY i) (σ.sZ i) (σ.sY i)
      (divisorSeq K σ.KY i) (B' i) (σ.KY i) (B' (i + 1)) (σ.f i) (σ.fp i))
    (hn : σ.n = ⊤) :
    RealFlipSequence (modelStr sX σ.sY N) (divisorSeq K σ.KY N) (B' N) where
  n := ⊤
  Y j := σ.Y (N + j)
  sY j := σ.sY (N + j)
  KY j := σ.KY (N + j)
  BY j := B' (N + j + 1)
  Z j := σ.Z (N + j)
  sZ j := σ.sZ (N + j)
  f
    | 0 => σ.f N
    | j + 1 => σ.f (N + j + 1)
  fp j := σ.fp (N + j)
  isCanonicalDivisor := by
    cases N with
    | zero => exact σ.isCanonicalDivisor
    | succ N => exact (σ.isRealFlipStep N (by simp [hn])).isCanonicalDivisor_flip
  isQFactorial
    | 0, _ => σ.isQFactorial N (by simp [hn])
    | j + 1, _ => σ.isQFactorial (N + j + 1) (by simp [hn])
  isQuasiProjectiveVariety
    | 0, _ => σ.isQuasiProjectiveVariety N (by simp [hn])
    | j + 1, _ => σ.isQuasiProjectiveVariety (N + j + 1) (by simp [hn])
  dim_eq
    | 0, _ => σ.dim_eq N (by simp [hn])
    | j + 1, _ => σ.dim_eq (N + j + 1) (by simp [hn])
  isRealFlipStep
    | 0, _ => hstep N le_rfl
    | j + 1, _ => hstep (N + j + 1) (by omega)

/-- The models of a tail are models of the sequence, with the new boundaries. -/
private theorem tail_isRealCanonicalPair (σ : RealFlipSequence sX K B) (N : ℕ)
    (B' : ∀ i, RDivisor (modelSeq X σ.Y i)) (hstep) (hn : σ.n = ⊤)
    (h : ∀ i ≥ N, IsRealCanonicalPair (modelStr sX σ.sY i) (B' i)) (j : ℕ) :
    IsRealCanonicalPair (modelStr (modelStr sX σ.sY N) (tail σ N B' hstep hn).sY j)
      (divisorSeq (B' N) (tail σ N B' hstep hn).BY j) := by
  cases j with
  | zero => exact h N le_rfl
  | succ j => exact h (N + j + 1) (by omega)

private theorem tail_isProjectiveVariety (σ : RealFlipSequence sX K B) (N : ℕ)
    (B' : ∀ i, RDivisor (modelSeq X σ.Y i)) (hstep) (hn : σ.n = ⊤)
    (h : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (modelStr sX σ.sY i)) (j : ℕ) :
    MMP.Mori.IsProjectiveVariety ℂ (modelStr (modelStr sX σ.sY N) (tail σ N B' hstep hn).sY j) := by
  cases j with
  | zero => exact h N
  | succ j => exact h (N + j + 1)

end Tail

/-! ### The empty boundary -/

/-- An extremal real flip sequence of real canonical pairs with empty boundary is finite: the
canonical difficulty is a finite natural number which drops at every step. -/
private theorem n_ne_top_of_eq_zero (σ : RealFlipSequence sX K B)
    (hσ : ∀ i : ℕ, (i : ℕ∞) ≤ σ.n →
      IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i)) (hB : B = 0) :
    σ.n ≠ ⊤ := by
  intro hn
  obtain ⟨hfin, -, -, hdrop⟩ := σ.realCanonicalDifficulty_ne_top_and_antitone hσ
  set d : ℕ → ℕ∞ := fun i =>
    realCanonicalDifficulty (modelStr sX σ.sY i) (divisorSeq B σ.BY i)
  have hlt : ∀ i, d (i + 1) < d i := fun i => hdrop hB i (by simp [hn])
  have hle : ∀ i : ℕ, d i + i ≤ d 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc d (i + 1) + ((i + 1 : ℕ) : ℕ∞) = (d (i + 1) + 1) + i := by push_cast; ring
        _ ≤ d i + i := by gcongr; exact Order.add_one_le_of_lt (hlt i)
        _ ≤ d 0 := ih
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hfin _ _ (hσ 0 (by simp)))
  have h := hle (m + 1)
  have hm' : d 0 = m := hm.symm
  rw [hm'] at h
  have : ((m + 1 : ℕ) : ℕ∞) ≤ m := le_trans le_add_self h
  exact absurd (ENat.coe_le_coe.mp this) (by omega)

/-! ### Small contractions -/

section Points

variable {X Y : Scheme.{u}}

/-- The restriction `f ∣_ V` followed by `V ⊆ Y` is `f` on `f⁻¹(V)`. -/
private theorem apply_ι_morphismRestrict (f : X ⟶ Y) (V : Y.Opens) (p : (f ⁻¹ᵁ V).toScheme) :
    V.ι ((f ∣_ V) p) = f ((f ⁻¹ᵁ V).ι p) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x₁ x₂ : X}
    (h₁ : f x₁ ∈ V) (h₂ : f x₂ ∈ V) (h : f x₁ = f x₂) : x₁ = x₂ := by
  let p₁ : (f ⁻¹ᵁ V).toScheme := ⟨x₁, h₁⟩
  let p₂ : (f ⁻¹ᵁ V).toScheme := ⟨x₂, h₂⟩
  have : (f ∣_ V) p₁ = (f ∣_ V) p₂ :=
    V.ι.isOpenEmbedding.injective ((apply_ι_morphismRestrict f V p₁).trans
      (h.trans (apply_ι_morphismRestrict f V p₂).symm))
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective this)

end Points

section Small

variable {X Z : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **A small contraction is an isomorphism off codimension two.** For a small birational
contraction `f : X ⟶ Z` there are closed subsets `V ⊆ X` and `W ⊆ Z` of points of coheight at
least two, with `X ∖ V ⊆ f⁻¹(Z ∖ W)`, such that `f` is an isomorphism over `Z ∖ W`: the section of
the separated `f⁻¹(Z ∖ W) ⟶ Z ∖ W` given by `X ∖ V` is a closed immersion, so `X ∖ V` is
open and closed in the irreducible `f⁻¹(Z ∖ W)`. -/
private theorem exists_closeds_isIso_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : Closeds X) (W : Closeds Z), (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  refine ⟨V, W, hV', hW', h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  -- `X ∖ V` is nonempty: it contains the generic point
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

variable [IsLocallyNoetherian X] [IsNormal X]

/-- Points of coheight at most one of the base lie in the biregular locus of a small
contraction. -/
private theorem mem_biregularLocus_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    {z : Z} (hz : Order.coheight z ≤ 1) : z ∈ biregularLocus f := by
  obtain ⟨V, W, -, hW, -, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hzW : z ∈ (W.compl : Set Z) := fun h => absurd ((hW z h).trans hz) (by decide)
  exact le_biregularLocus hiso hzW

/-- A small contraction maps the generic point of a prime divisor to a point of coheight one,
in its biregular locus. -/
private theorem coheight_map_genericPoint_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 ∧ f P.genericPoint ∈ biregularLocus f := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hb : f P.genericPoint ∈ biregularLocus f := le_biregularLocus hiso (h hPV)
  exact ⟨by rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
    P.coheight_genericPoint], hb⟩

/-- Two prime divisors with the same image under a small contraction coincide. -/
private theorem primeDivisor_eq_of_map_eq_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) {P Q : MMP.Mori.PrimeDivisor X}
    (hPQ : f P.genericPoint = f Q.genericPoint) : P = Q := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hQV : Q.genericPoint ∈ (V.compl : Set X) := fun hQ =>
    absurd (hV _ hQ) (by rw [Q.coheight_genericPoint]; decide)
  haveI := hiso
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq f W.compl (h hPV) (h hQV) hPQ)

end Small

section SmallPair

variable {X X' Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- Every prime divisor of `X` corresponds, through `Z`, to a prime divisor of `X⁺`. -/
private theorem exists_primeDivisor_map_eq_of_isSmall {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint = f P.genericPoint := by
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  have hb := mem_biregularLocus_of_isSmall hfp hz.le
  obtain ⟨x', hx'⟩ :=
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj (f P.genericPoint)
  have hc : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hb), hx', hz]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc)).trans hx'⟩

/-- The strict transform `(f⁺)⁻¹_* f_* D` across two small contractions has, at the prime divisor
`P⁺` corresponding to `P`, the coefficient of `D` at `P`. -/
private theorem flipTransform_apply_of_isSmall [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP' : fp P'.genericPoint = f P.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper f := hf.isProper
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj hQ (hPP'.trans hQ)
    (mem_biregularLocus_of_isSmall hfp (hQ ▸ hz).le) D

/-- The strict transform commutes with real multiples of integral divisors. -/
private theorem flipTransform_smul_toRDivisor [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f) (c : ℝ)
    (G : Divisor X) :
    flipTransform f fp (c • Divisor.toRDivisor G) =
      c • Divisor.toRDivisor (flipTransform f fp G) := by
  ext P'
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hfp hf P'
  have h1 := flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm (c • Divisor.toRDivisor G)
  have h2 := flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm G
  simp only [DivisorWithCoeffs.coeff_apply] at h1 ⊢
  rw [h1]
  change c * (Divisor.toRDivisor G).coeff P =
    c * (Divisor.toRDivisor (flipTransform f fp G)).coeff P'
  rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_apply, h2]

/-- The strict transform commutes with the inclusion of integral divisors into `ℝ`-divisors. -/
private theorem flipTransform_toRDivisor [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f) (G : Divisor X) :
    flipTransform f fp (Divisor.toRDivisor G) = Divisor.toRDivisor (flipTransform f fp G) := by
  simpa only [one_smul] using flipTransform_smul_toRDivisor hZ hf hfp hfb 1 G

end SmallPair

section Threshold

/-- The largest coefficient `d(B)` depends only on the coefficients along the support. -/
private theorem realThresholdMax_eq_of_bijOn {X X' : Scheme.{0}} {B : RDivisor X}
    {B' : RDivisor X'} (e : MMP.Mori.PrimeDivisor X → MMP.Mori.PrimeDivisor X')
    (he : Set.BijOn e B.support B'.support) (hc : ∀ P, B'.coeff (e P) = B.coeff P) :
    realThresholdMax B' = realThresholdMax B := by
  classical
  have himg : B'.support.image B'.coeff = B.support.image B.coeff := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨P', hP', rfl⟩
      obtain ⟨P, hP, rfl⟩ := he.surjOn hP'
      exact ⟨P, hP, (hc P).symm⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨e P, he.mapsTo hP, hc P⟩
  simp only [realThresholdMax, himg]

/-- **Small contractions identify the components.** Across two small contractions `X ⟶ Z ⟵ X⁺`
the strict transform maps the components of `B` bijectively onto those of its transform, keeping
the coefficients. -/
private theorem exists_bijOn_support_flipTransform {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f) (B : RDivisor X) :
    ∃ e : MMP.Mori.PrimeDivisor X → MMP.Mori.PrimeDivisor X',
      Set.BijOn e B.support (flipTransform f fp B).support ∧
        ∀ P, (flipTransform f fp B).coeff (e P) = B.coeff P := by
  classical
  choose e he using exists_primeDivisor_map_eq_of_isSmall hf hfp
  have hc : ∀ P, (flipTransform f fp B).coeff (e P) = B.coeff P := fun P => by
    simp only [DivisorWithCoeffs.coeff_apply]
    exact flipTransform_apply_of_isSmall hZ hf hfp hfb (he P) B
  refine ⟨e, ⟨fun P hP => ?_, fun P _ Q _ hPQ => ?_, fun P' hP' => ?_⟩, hc⟩
  · simp only [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hP ⊢
    rwa [hc P]
  · exact primeDivisor_eq_of_map_eq_of_isSmall hf ((he P).symm.trans (hPQ ▸ he Q))
  · obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hfp hf P'
    have hcP : (flipTransform f fp B).coeff P' = B.coeff P := by
      simp only [DivisorWithCoeffs.coeff_apply]
      exact flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm B
    refine ⟨P, ?_, primeDivisor_eq_of_map_eq_of_isSmall hfp ((he P).trans hP)⟩
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply] at hP' ⊢
    rwa [← hcP]

end Threshold

/-! ### The flip as a birational map -/

section Transforms

/-- If `f⁺` is an isomorphism over `U`, two morphisms into `(f⁺)⁻¹(U)` which agree after
composing with `f⁺` are equal. -/
private theorem eq_of_comp_eq {T X' Y : Scheme.{u}} (fp : X' ⟶ Y) (U : Y.Opens)
    [IsIso (fp ∣_ U)] (a b : T ⟶ X') (ha : Set.range a ⊆ (fp ⁻¹ᵁ U : Set X'))
    (hb : Set.range b ⊆ (fp ⁻¹ᵁ U : Set X')) (h : a ≫ fp = b ≫ fp) : a = b := by
  have ha' : Set.range a ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  have hb' : Set.range b ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  rw [← IsOpenImmersion.lift_fac _ _ ha', ← IsOpenImmersion.lift_fac _ _ hb']
  congr 1
  rw [← cancel_mono (fp ∣_ U), ← cancel_mono U.ι, Category.assoc, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
    IsOpenImmersion.lift_fac, h]

/-- A morphism `a : T ⟶ X'` with `a ≫ f⁺ = c ≫ f` for some `c` landing in `f⁻¹(U)` lands in
`(f⁺)⁻¹(U)`. -/
private theorem range_subset_of_comp_eq {T X X' Y : Scheme.{u}} {f : X ⟶ Y} {fp : X' ⟶ Y}
    {U : Y.Opens} (a : T ⟶ X') (c : T ⟶ X) (hc : ∀ t, c t ∈ f ⁻¹ᵁ U) (h : a ≫ fp = c ≫ f) :
    Set.range a ⊆ (fp ⁻¹ᵁ U : Set X') := by
  rintro _ ⟨t, rfl⟩
  change fp (a t) ∈ U
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact hc t

/-- Let `f⁺` be an isomorphism over `U`. A partial map `p : X ⇀ X'` defined inside `f⁻¹(U)` with
`f⁺ ∘ p = f` represents every rational map `g` with `f⁺ ∘ g = f`. -/
private theorem toRationalMap_eq_of_comp_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y)
    (U : Y.Opens) [IsIso (fp ∣_ U)] (p : X.PartialMap X') (hpU : p.domain ≤ f ⁻¹ᵁ U)
    (hp : p.hom ≫ fp = p.domain.ι ≫ f) (g : X.PartialMap X')
    (hg : g.toRationalMap.compHom fp = f.toPartialMap.toRationalMap) :
    p.toRationalMap = g.toRationalMap := by
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hg
  obtain ⟨W, hWd, hWl, _, hWe⟩ := hg
  replace hWl : W ≤ g.domain := hWl
  have h2 : W ⊓ p.domain ≤ g.domain := inf_le_left.trans hWl
  have hc : ∀ t, (W ⊓ p.domain).ι t ∈ f ⁻¹ᵁ U := fun t ↦ hpU t.2.2
  have ha : (X.homOfLE (inf_le_right : W ⊓ p.domain ≤ _) ≫ p.hom) ≫ fp =
      (W ⊓ p.domain).ι ≫ f := by
    rw [Category.assoc, hp, Scheme.homOfLE_ι_assoc]
  have hb : (X.homOfLE h2 ≫ g.hom) ≫ fp = (W ⊓ p.domain).ι ≫ f := by
    have hWe' : X.homOfLE hWl ≫ g.hom ≫ fp = X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom ≫ f := hWe
    rw [Category.assoc, ← X.homOfLE_homOfLE (inf_le_left : W ⊓ p.domain ≤ W) hWl,
      Category.assoc, hWe', Scheme.topIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.homOfLE_homOfLE, Scheme.homOfLE_ι]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  exact ⟨_, hWd.inter_of_isOpen_left p.dense_domain W.isOpen, inf_le_right, h2,
    eq_of_comp_eq fp U _ _ (range_subset_of_comp_eq _ _ hc ha)
      (range_subset_of_comp_eq _ _ hc hb) (ha.trans hb.symm)⟩

/-- A rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, where `f` and `f⁺` are isomorphisms over a
`V` over which lie the points of codimension at most one of `X`, is represented on `f⁻¹(V)` by
`(f⁺)⁻¹ ∘ f`. -/
private theorem exists_partialMap {X X' Y : Scheme.{u}} [IsIntegral X] {f : X ⟶ Y} (fp : X' ⟶ Y)
    (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) :
    ∃ g : X.PartialMap X', g.domain = f ⁻¹ᵁ V ∧ g.toRationalMap = φ ∧
      g.hom ≫ fp = g.domain.ι ≫ f ∧ ∀ t, fp (g.hom t) ∈ V := by
  have hgen : Order.coheight (genericPoint X) ≤ 1 :=
    (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le zero_le_one
  have hd : Dense (f ⁻¹ᵁ V : Set X) := (f ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ hgen⟩
  let g : X.PartialMap X' := ⟨f ⁻¹ᵁ V, hd, (f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι⟩
  have hg : g.hom ≫ fp = g.domain.ι ≫ f := by
    change ((f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι) ≫ fp = (f ⁻¹ᵁ V).ι ≫ f
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  refine ⟨g, rfl, ?_, hg, fun t => ?_⟩
  · obtain ⟨g₀, rfl⟩ := Quotient.exists_rep φ
    exact toRationalMap_eq_of_comp_eq fp V g le_rfl hg g₀ hφ
  · change fp ((fp ⁻¹ᵁ V).ι ((inv (fp ∣_ V)) ((f ∣_ V) t))) ∈ V
    exact ((inv (fp ∣_ V)) ((f ∣_ V) t)).2

/-- **A rational map over `Y` matches prime divisors over the same point.** If `f`, `f⁺` are
isomorphisms over `V`, over which lie the points of codimension at most one of `X`, a rational map
`φ` with `f⁺ ∘ φ = f` carries a prime divisor `P` to `P⁺` exactly when `P` and `P⁺` lie over the
same point of `Y`. -/
private theorem transformPrimeDivisor_eq_some_iff {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some P' ↔
      f P.genericPoint = fp P'.genericPoint := by
  obtain ⟨g, hgd, hgφ, hgc, hgV⟩ := exists_partialMap fp V hXV hφ
  have hmem : P.genericPoint ∈ g.domain := by
    rw [hgd]; exact hXV _ P.coheight_genericPoint.le
  have hval : fp (g.hom ⟨P.genericPoint, hmem⟩) = f P.genericPoint :=
    congrArg (fun h => h.base ⟨P.genericPoint, hmem⟩) hgc
  refine ⟨fun h => ?_, fun hPP =>
    MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g hgφ hmem
      (eq_of_apply_eq fp V (hPP ▸ hXV _ P.coheight_genericPoint.le) (hgV _)
        (hPP.symm.trans hval.symm))⟩
  rw [MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some h g hgφ hmem, hval]

/-- The coefficients of `φ_* D` for a rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, when `f` and
`f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one of `X`: the
coefficient of `P⁺` is that of the prime divisor `P` of `X` over the same point of `Y`. -/
private theorem transformDivisor_apply {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D P' = D P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((transformPrimeDivisor_eq_some_iff fp V hXV hφ).mpr hPP) (fun P₁ hP₁ =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
        eq_of_apply_eq f V (hXV _ P₁.coheight_genericPoint.le) (hXV _ P.coheight_genericPoint.le)
          (((transformPrimeDivisor_eq_some_iff fp V hXV hφ).mp hP₁).trans hPP.symm)) D

/-- **The flip transforms divisors as `(f⁺)⁻¹_* f_*`.** If `f` and `f⁺` are isomorphisms over `V`,
over which lie the points of codimension at most one of `X` and of `X⁺`, then
`φ_* D = (f⁺)⁻¹_* f_* D` for every rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`. -/
private theorem transformDivisor_eq_flipTransform {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X' ↘ ⊤_ Scheme)]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {φ : X.RationalMap X'}
    (hφ : φ.compHom fp = f.toRationalMap) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, hP⟩ := MMP.Mori.exists_primeDivisor_genericPoint_eq f fp V P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  rw [transformDivisor_apply fp V hXV hφ hP, MMP.Mori.flipTransform_apply hY hX hf V hXV hP]

end Transforms

/-! ### `ℚ`-factorial varieties and presentations -/

/-- An `ℝ`-divisor is the sum of its prime components with their coefficients. -/
private theorem eq_sum_coeff_smul_single {W : Scheme.{0}} (G : RDivisor W) :
    G = ∑ j : Fin G.support.card, G.coeff (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) •
      Divisor.toRDivisor
        (Finsupp.single (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) 1) := by
  classical
  have hsumFin : ∀ F : MMP.Mori.PrimeDivisor W → ℝ,
      ∑ j, F (G.support.equivFin.symm j) = ∑ Q ∈ G.support, F Q := fun F => by
    rw [← Finset.sum_coe_sort G.support]
    exact Equiv.sum_comp G.support.equivFin.symm (fun Q => F Q)
  refine DivisorWithCoeffs.ext' fun Q => ?_
  simp only [MMP.Flips.coeff_sum_smul_toRDivisor]
  have key : ∀ R : MMP.Mori.PrimeDivisor W,
      ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single R 1) Q : ℤ) : ℝ) =
        if R = Q then 1 else 0 := fun R => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]
    split_ifs <;> simp
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [hsumFin (fun R => if R = Q then G.coeff R else 0), Finset.sum_ite_eq']
  by_cases hQ : Q ∈ G.support
  · simp [hQ]
  · simp only [hQ, if_false]
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp hQ

section QFactorial

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- Dividing the coefficient by `m` undoes the multiple `m D`:
`(c / m) • (m D) = c • D` for `m > 0`. -/
private theorem div_smul_toRDivisor_zsmul {X : Scheme.{u}} (c : ℝ) {m : ℕ} (hm : 0 < m)
    (D : Divisor X) :
    (c / m) • Divisor.toRDivisor ((m : ℤ) • D) = c • Divisor.toRDivisor D := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
    div_mul_cancel₀ c (by exact_mod_cast hm.ne')]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: `G = ∑ g_P P` is the
combination `∑ (g_P / m_P) (m_P P)` of Cartier divisors, where `m_P P` is Cartier. -/
private theorem isCartierCombination_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    IsCartierCombination G := by
  classical
  choose mq hmq hmqC using fun P : MMP.Mori.PrimeDivisor X => hq.2 (Finsupp.single P 1)
  set Pj : Fin G.support.card → MMP.Mori.PrimeDivisor X :=
    fun j => (G.support.equivFin.symm j : _)
  have hG : G = ∑ j, (fun j => G.coeff (Pj j) / (mq (Pj j) : ℝ)) j •
      Divisor.toRDivisor ((fun j => (mq (Pj j) : ℤ) • Finsupp.single (Pj j) 1) j) := by
    conv_lhs => rw [eq_sum_coeff_smul_single G]
    exact Finset.sum_congr rfl fun j _ => (div_smul_toRDivisor_zsmul _ (hmq _) _).symm
  exact ⟨G.support.card, fun j => G.coeff (Pj j) / (mq (Pj j) : ℝ),
    fun j => (mq (Pj j) : ℤ) • Finsupp.single (Pj j) 1, fun j => hmqC _,
    hG.trans (by simp only [MMP.Flips.toRDivisor_eq_mapCoeffs])⟩

end QFactorial

section FlipMap

variable {X Z X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- The points of codimension at most one of `X` lie over the open of `Z` over which both small
contractions are isomorphisms. -/
private theorem mem_biregularLocus_inf_of_isSmall (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) {x : X} (hx : Order.coheight x ≤ 1) :
    f x ∈ biregularLocus f ⊓ biregularLocus fp := by
  obtain ⟨V, W, hV, -, hVW, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hxV : x ∈ (V.compl : Set X) := fun h => absurd ((hV x h).trans hx) (by decide)
  have hb : f x ∈ biregularLocus f := le_biregularLocus hiso (hVW hxV)
  refine ⟨hb, mem_biregularLocus_of_isSmall hfp ?_⟩
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb]
  exact hx

/-- **The flip as a birational map.** For small contractions `f : X ⟶ Z ⟵ X⁺ : f⁺` of normal
varieties there is a birational map `g = (f⁺)⁻¹ ∘ f : X ⤏ X⁺` over `Z`, which transforms divisors
as the strict transform `(f⁺)⁻¹_* f_*` and every prime divisor of `X⁺` is a transform. -/
private theorem exists_flipMap (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX')
    (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) :
    ∃ g : X.RationalMap X', MMP.Mori.RationalMap.IsBirational g ∧
      MMP.Flips.RationalMap.IsOver f fp g ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor g D = flipTransform f fp D) ∧
      ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor g P = some P' := by
  obtain ⟨g, hg, hgo⟩ := MMP.Mori.exists_isBirational_compHom_eq hfb hfpb
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hX'
  haveI : IsIso (f ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ biregularLocus f ⊓ biregularLocus fp :=
    fun x hx => mem_biregularLocus_inf_of_isSmall hf hfp hx
  have hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ biregularLocus f ⊓ biregularLocus fp :=
    fun x hx => by
      have := mem_biregularLocus_inf_of_isSmall hfp hf hx
      exact ⟨this.2, this.1⟩
  haveI : IsProper f := hf.isProper
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rwa [hf.comp_eq]
  refine ⟨g, hg, hgo, fun D => transformDivisor_eq_flipTransform hZ hXn hfb _ hXV hX'V hgo D,
    fun P' => ?_⟩
  obtain ⟨P, hP⟩ := MMP.Mori.exists_primeDivisor_genericPoint_eq f fp _ P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  exact ⟨P, (transformPrimeDivisor_eq_some_iff fp _ hXV hgo).mpr hP⟩

end FlipMap

section CurveNormalization

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_of_eq_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

end CurveNormalization

/-! ### Numerical triviality over the base -/

section Numerical

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- The empty presentation computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX 0 (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every presentation of an `ℝ`-Cartier divisor computes some value of `D · C`. -/
private theorem exists_isRIntersectionNumber_of_isCartierCombination {D : RDivisor X}
    (hD : IsCartierCombination D) (C : ProperCurve sX) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX D r L C x := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  refine ⟨m, r, L, ∑ j, r j * (L j).degreeOn ℂ sX C.ι C.dim_le (hL j),
    isRIntersectionNumber_of_eq_sum_degreeOn D r L hL ?_ C⟩
  rw [hDeq]
  simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]

/-- `ℝ`-Cartier divisors form a real vector space. -/
private theorem isCartierCombination_add_smul {D N : RDivisor X} (hD : IsCartierCombination D)
    (hN : IsCartierCombination N) (c : ℝ) : IsCartierCombination (D + c • N) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  obtain ⟨m', r', L', hL', rfl⟩ := hN
  refine ⟨m + m', Fin.append r (c • r'), Fin.append L L', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [Fin.sum_univ_add, Finset.smul_sum]
    simp [smul_smul]

/-- A relatively ample `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRelativelyAmple [CompactSpace X] {f : X ⟶ Y}
    {A : RDivisor X} (hA : MMP.Flips.IsRelativelyAmple f A) : IsCartierCombination A := by
  obtain ⟨m, r, L, -, -, hL, rfl⟩ := hA
  exact ⟨m, r, L, fun j => (hL j).1, by simp [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- A numerically trivial divisor computes `0` on every contracted curve. -/
private theorem eq_zero_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) {C : ProperCurve sX} (hC : C.IsContractedBy f)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX N r L C x) : x = 0 :=
  hN.2.2 C hC m r L x 0 Fin.elim0 Fin.elim0 0 hx (isRIntersectionNumber_zero C)

/-- Adding a multiple of a numerically trivial divisor does not change numerical classes. -/
private theorem isNumericallyEquivalentOver_add_smul {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyEquivalentOver ℂ sX f (D + c • N) D := by
  refine ⟨isCartierCombination_add_smul hD hN.1 c, hD,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨m₃, r₃, L₃, x₃, h₃⟩ := exists_isRIntersectionNumber_of_isCartierCombination hN.1 C
  have h0 := eq_zero_of_isNumericallyTrivialOver hN hC h₃
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D N r₂ L₂ r₃ L₃ x₂ x₃ 1 c h₂ h₃
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum, h0]
  ring

/-- A Cartier divisor linearly equivalent to `0` is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent [CompactSpace X]
    (f : X ⟶ Y) {D : Divisor X} (hD : D.IsCartier) (h : D.LinearlyEquivalent 0) :
    IsNumericallyTrivialOver ℂ sX f (Divisor.toRDivisor D) := by
  have hDc : IsCartierCombination (Divisor.toRDivisor D) :=
    ⟨1, fun _ => 1, fun _ => D, fun _ => hD, by simp [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  refine ⟨hDc, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have h₃ := isRIntersectionNumber_of_eq_sum_degreeOn (Divisor.toRDivisor D)
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ => D) (fun _ => hD) (by simp) C
  have hdeg : D.degreeOn ℂ sX C.ι C.dim_le hD = 0 :=
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hD h
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ h₃,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C)]
  simp [hdeg]

end Numerical

/-- **Numerically equivalent divisors are ample together** over a projective morphism of normal
varieties (FA 2.16.3). -/
private theorem isRelativelyAmple_of_isNumericallyEquivalentOver {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
    (hf : IsProjectiveMorphism f) (hfs : f ≫ sZ = sX) {D A : RDivisor X}
    (hDA : haveI : QuasiCompact sX := hX.1.toQuasiCompact
      MMP.Flips.IsNumericallyEquivalentOver ℂ sX f D A)
    (hA : MMP.Flips.IsRelativelyAmple f A) : MMP.Flips.IsRelativelyAmple f D := by
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf
  exact (MMP.Flips.relativelyAmple_basics sX sZ hX hZ f hfs).2.2.2.2.2
    (IsProjectiveMorphism.isProjective hf) D A hDA hA

section SurfaceNormalization

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- A prime divisor of a variety, with its reduced structure, is a variety. -/
private theorem isVariety_subscheme (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    haveI := P.integral
    AlgebraicGeometry.IsVariety k (P.idealSheaf.subschemeι ≫ sX) := by
  haveI := P.integral
  haveI : AlgebraicGeometry.IsVariety k sX := hX
  exact (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance,
    inferInstance⟩

/-- The normalization of a prime divisor of a variety is a normal variety. -/
private theorem isNormalVariety_normalization (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    IsNormalVariety k (primeDivisorNormalization P ≫ sX) := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  refine ⟨?_, h.2.1⟩
  have h1 := h.1
  rw [← Category.assoc] at h1
  exact h1

/-- The normalization of a prime divisor of a variety is finite. -/
private theorem isFinite_normalization (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) :
    IsFinite (primeDivisorNormalization P) := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  have h1 : IsFinite (P.idealSheaf.subscheme.normalization
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) := h.2.2.1
  exact MorphismProperty.comp_mem _ _ _ h1 inferInstance

/-- On an integral scheme locally of finite type over a field, a prime divisor has codimension
one: its dimension plus one is the dimension of the scheme. -/
private theorem topologicalKrullDim_support_add_one [IsIntegral X]
    [LocallyOfFiniteType sX] (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (P.support : Set X) + 1 = topologicalKrullDim X := by
  let _ : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact_mod_cast h

/-- The normalization of a prime divisor of a threefold is a surface. -/
private theorem topologicalKrullDim_normalization (hX : MMP.Mori.IsVariety k sX)
    (h3 : topologicalKrullDim X = 3) (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (primeDivisorNormalizationScheme P) = 2 := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  haveI := h.1
  haveI : AlgebraicGeometry.IsVariety k sX := hX
  haveI : IsIntegral X := hX.toIsIntegral
  have e1 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
    (P.idealSheaf.subschemeι ≫ sX) (P.idealSheaf.subscheme.normalization
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) ≫
        (P.idealSheaf.subschemeι ≫ sX)) h.2.2.2.2
  change topologicalKrullDim (P.idealSheaf.subscheme.normalizationScheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) = 2
  rw [← e1, topologicalKrullDim_subscheme_eq]
  have := topologicalKrullDim_support_add_one sX P
  rw [h3] at this
  exact ENat.WithBot.add_one_cancel.mp this

/-- The normalization of a prime divisor maps the generic point to the generic point. -/
private theorem primeDivisorNormalization_apply_genericPoint (P : MMP.Mori.PrimeDivisor X)
    [IsIntegral (primeDivisorNormalizationScheme P)] :
    primeDivisorNormalization P (genericPoint (primeDivisorNormalizationScheme P)) =
      P.genericPoint := by
  have := P.integral
  have hz : genericPoint (primeDivisorNormalizationScheme P) ∈
      genericPoints (primeDivisorNormalizationScheme P) := by
    rw [genericPoints_eq_singleton]; rfl
  have h := Scheme.normalization_mem_genericPoints P.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) hz
  rw [genericPoints_eq_singleton] at h
  change P.idealSheaf.subschemeι _ = P.idealSheaf.subschemeι _
  congr 1

/-- The normalization of a prime divisor of a variety is surjective on the stalk at the generic
point: it is a birational morphism followed by the closed immersion `P ⟶ X`. -/
private theorem surjective_stalkMap_normalization (hX : MMP.Mori.IsVariety k sX)
    (P : MMP.Mori.PrimeDivisor X) [IsIntegral (primeDivisorNormalizationScheme P)] :
    Function.Surjective ((primeDivisorNormalization P).stalkMap
      (genericPoint (primeDivisorNormalizationScheme P))) := by
  haveI := P.integral
  haveI := isVariety_subscheme sX hX P
  have h := (MMP.Threefold.normalization_spec (P.idealSheaf.subschemeι ≫ sX)).1
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h.2.2.2.2
  have hiso := hb.2 (genericPoint (primeDivisorNormalizationScheme P))
    (by rw [genericPoints_eq_singleton]; rfl)
  have hf := ((ConcreteCategory.isIso_iff_bijective _).mp hiso).2
  rw [Scheme.Hom.stalkMap_comp]
  intro y
  obtain ⟨a, rfl⟩ := hf y
  obtain ⟨b, rfl⟩ := P.idealSheaf.subschemeι.stalkMap_surjective _ a
  exact ⟨b, rfl⟩

end SurfaceNormalization

section FlipNormalization

open MMP.Flips

/-- A morphism which restricts to an isomorphism over an open `U` is an isomorphism on the stalks
at the points over `U`. -/
private theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{0}} (g : X ⟶ Y)
    (U : Y.Opens) [IsIso (g ∣_ U)] (x : X) (hx : g x ∈ U) : IsIso (g.stalkMap x) := by
  have e := morphismRestrictStalkMap g U ⟨x, hx⟩
  have h1 : IsIso ((g ∣_ U).stalkMap ⟨x, hx⟩) :=
    ((isIso_iff_isIso_stalkMap (g ∣_ U)).mp inferInstance).2 _
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).mp h1

variable {k : Type} [Field k] {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {E : RDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}

/-- **The morphism of normalizations along a flip.** Let `φ⁺ : X⁺ ⟶ Z` be a flip of `φ : X ⟶ Z`
with birational map `g`, `P ⊆ X` a prime divisor with transform `P⁺ = g_* P`, and
`ψ : P^ν ⟶ (P⁺)^ν` a morphism of normalizations agreeing with `g` on a dense open subset. Then
`ψ` is a proper birational morphism over `k`. -/
private theorem normalization_hom_spec (hflip : IsFlip k sX sZ sX' E φ φp g)
    {P : MMP.Mori.PrimeDivisor X} {Pp : MMP.Mori.PrimeDivisor X'}
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor g P = some Pp)
    (ψ : primeDivisorNormalizationScheme P ⟶ primeDivisorNormalizationScheme Pp)
    (hψ : ∃ g₀ : X.PartialMap X', g₀.toRationalMap = g ∧
      ∃ U : (primeDivisorNormalizationScheme P).Opens,
        Dense (U : Set (primeDivisorNormalizationScheme P)) ∧
        ∃ hU : U ≤ primeDivisorNormalization P ⁻¹ᵁ g₀.domain,
          U.ι ≫ ψ ≫ primeDivisorNormalization Pp =
            (primeDivisorNormalization P).resLE g₀.domain U hU ≫ g₀.hom) :
    ψ ≫ primeDivisorNormalization Pp ≫ sX' = primeDivisorNormalization P ≫ sX ∧
      IsProper ψ ∧ IsBirationalMorphism ψ := by
  have hsm := hflip.isSmall_source
  have hsm' := hflip.isSmall
  have hvX : MMP.Mori.IsVariety k sX := hsm.isVariety_source
  have hvX' : MMP.Mori.IsVariety k sX' := hsm'.isVariety_source
  have hvZ : MMP.Mori.IsVariety k sZ := hsm.isVariety_target
  haveI : IsProper φ := hsm.isProper
  haveI : IsProper φp := hsm'.isProper
  haveI : AlgebraicGeometry.IsVariety k sZ := hvZ
  haveI : AlgebraicGeometry.IsVariety k sX := hvX
  haveI : AlgebraicGeometry.IsVariety k sX' := hvX'
  haveI : Z.IsSeparated :=
    ⟨by rw [show Limits.terminal.from Z = sZ ≫ Limits.terminal.from _ from
      Limits.terminal.hom_ext _ _]; infer_instance⟩
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_terminal sX'
  have hN := isNormalVariety_normalization sX hvX P
  have hN' := isNormalVariety_normalization sX' hvX' Pp
  haveI : IsIntegral (primeDivisorNormalizationScheme P) := hN.1.toIsIntegral
  haveI : IsIntegral (primeDivisorNormalizationScheme Pp) := hN'.1.toIsIntegral
  haveI : IsReduced (primeDivisorNormalizationScheme P) := isReduced_of_isIntegral _
  haveI : LocallyOfFiniteType (primeDivisorNormalization P ≫ sX) :=
    hN.1.toLocallyOfFiniteType
  haveI := isFinite_normalization sX hvX P
  haveI := isFinite_normalization sX' hvX' Pp
  haveI : IsIntegral X := hvX.toIsIntegral
  obtain ⟨g₀, rfl, U, hUd, hU, hUeq⟩ := hψ
  -- `ψ` lies over `Z`.
  have hover : ψ ≫ primeDivisorNormalization Pp ≫ φp = primeDivisorNormalization P ≫ φ := by
    have h : (g₀.compHom φp).equiv φ.toPartialMap := by
      rw [← Scheme.PartialMap.toRationalMap_eq_iff]; exact hflip.isModificationOf.2
    have hD : g₀.hom ≫ φp = g₀.domain.ι ≫ φ := by
      obtain ⟨W, hW, hWl, hWr, hWe⟩ := h
      have hWl' : W ≤ g₀.domain := hWl
      haveI : IsDominant (X.homOfLE hWl') := Opens.isDominant_homOfLE hW _
      refine ext_of_isDominant (X.homOfLE hWl') ?_
      rw [Scheme.homOfLE_ι_assoc]
      simp only [Scheme.PartialMap.restrict, Scheme.PartialMap.compHom] at hWe
      refine hWe.trans ?_
      simp only [Scheme.Hom.toPartialMap]
      exact Scheme.homOfLE_ι_assoc ..
    haveI : IsDominant U.ι := Opens.isDominant_ι hUd
    refine ext_of_isDominant U.ι ?_
    calc U.ι ≫ ψ ≫ primeDivisorNormalization Pp ≫ φp
        = (U.ι ≫ ψ ≫ primeDivisorNormalization Pp) ≫ φp := by simp only [Category.assoc]
      _ = ((primeDivisorNormalization P).resLE g₀.domain U hU ≫ g₀.hom) ≫ φp := by rw [hUeq]
      _ = U.ι ≫ primeDivisorNormalization P ≫ φ := by
        rw [Category.assoc, hD, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  have hstr : ψ ≫ primeDivisorNormalization Pp ≫ sX' = primeDivisorNormalization P ≫ sX := by
    calc ψ ≫ primeDivisorNormalization Pp ≫ sX'
        = (ψ ≫ primeDivisorNormalization Pp ≫ φp) ≫ sZ := by
          rw [← hsm'.comp_eq]; simp only [Category.assoc]
      _ = (primeDivisorNormalization P ≫ φ) ≫ sZ := by rw [hover]
      _ = primeDivisorNormalization P ≫ sX := by rw [Category.assoc, hsm.comp_eq]
  have hprop : IsProper ψ := by
    haveI : IsProper (ψ ≫ primeDivisorNormalization Pp ≫ φp) := by rw [hover]; infer_instance
    exact IsProper.of_comp ψ (primeDivisorNormalization Pp ≫ φp)
  haveI : LocallyOfFiniteType ψ := by
    haveI : LocallyOfFiniteType (ψ ≫ primeDivisorNormalization Pp ≫ sX') := by
      rw [hstr]; infer_instance
    exact locallyOfFiniteType_of_comp ψ (primeDivisorNormalization Pp ≫ sX')
  -- `ψ` maps the generic point to the generic point.
  have hUne : (U : Set (primeDivisorNormalizationScheme P)).Nonempty := hUd.nonempty
  have hηU : genericPoint (primeDivisorNormalizationScheme P) ∈ U :=
    ((genericPoint_spec (primeDivisorNormalizationScheme P)).mem_open_set_iff U.isOpen).mpr
      (by simpa using hUne)
  have hνη := primeDivisorNormalization_apply_genericPoint P
  have hνηp := primeDivisorNormalization_apply_genericPoint Pp
  have hdom : P.genericPoint ∈ g₀.domain := hνη ▸ hU hηU
  have hg₀P : g₀.hom ⟨P.genericPoint, hdom⟩ = Pp.genericPoint :=
    (MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP g₀ rfl hdom).symm
  have hψη : ψ (genericPoint (primeDivisorNormalizationScheme P)) =
      genericPoint (primeDivisorNormalizationScheme Pp) := by
    let x : U.toScheme := ⟨_, hηU⟩
    have h3 : (primeDivisorNormalization P).resLE g₀.domain U hU x = ⟨P.genericPoint, hdom⟩ :=
      Subtype.ext ((Scheme.Hom.coe_resLE_apply _ _ _).trans hνη)
    have h2 : primeDivisorNormalization Pp (ψ (genericPoint (primeDivisorNormalizationScheme P)))
        = Pp.genericPoint :=
      (congrArg (fun f : U.toScheme ⟶ X' ↦ f x) hUeq).trans ((congrArg g₀.hom h3).trans hg₀P)
    exact (eq_of_specializes_of_isFinite (primeDivisorNormalization Pp)
      ((genericPoint_spec _).specializes (Set.mem_univ _)) (hνηp.trans h2.symm)).symm
  -- `ψ` is an isomorphism on the stalks at the generic point.
  have hsurjν := surjective_stalkMap_normalization sX hvX P
  have hisoφ : IsIso (φ.stalkMap (primeDivisorNormalization P
      (genericPoint (primeDivisorNormalizationScheme P)))) := by
    obtain ⟨W, hW, hWP, -⟩ := exists_isIso_morphismRestrict_of_isSmall hsm
    exact isIso_stalkMap_of_isIso_morphismRestrict φ W _ (by rw [hνη]; exact hWP P)
  have hsurjψ : Function.Surjective
      (ψ.stalkMap (genericPoint (primeDivisorNormalizationScheme P))) := by
    have e1 := Scheme.Hom.stalkMap_congr_hom _ _ hover
      (genericPoint (primeDivisorNormalizationScheme P))
    have e2 := Scheme.Hom.stalkMap_comp ψ (primeDivisorNormalization Pp ≫ φp)
      (genericPoint (primeDivisorNormalizationScheme P))
    have e3 := Scheme.Hom.stalkMap_comp (primeDivisorNormalization P) φ
      (genericPoint (primeDivisorNormalizationScheme P))
    intro y
    obtain ⟨a, rfl⟩ := hsurjν y
    obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (φ.stalkMap (primeDivisorNormalization P
        (genericPoint (primeDivisorNormalizationScheme P))))).2 a
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Z.presheaf.stalkCongr (Inseparable.of_eq (congrArg
        (fun f : primeDivisorNormalizationScheme P ⟶ Z ↦
          f (genericPoint (primeDivisorNormalizationScheme P))) hover))).hom).2 b
    refine ⟨(primeDivisorNormalization Pp ≫ φp).stalkMap _ c, ?_⟩
    have h4 := congrArg (fun f ↦ f c) (e2.symm.trans (e1.trans (congrArg (_ ≫ ·) e3)))
    simp only [ConcreteCategory.comp_apply] at h4
    exact h4
  have hinjψ : Function.Injective
      (ψ.stalkMap (genericPoint (primeDivisorNormalizationScheme P))) := by
    have hfield : IsField ((primeDivisorNormalizationScheme Pp).presheaf.stalk
        (ψ (genericPoint (primeDivisorNormalizationScheme P)))) := by
      rw [hψη]
      exact Field.toIsField (primeDivisorNormalizationScheme Pp).functionField
    letI := hfield.toField
    exact (ψ.stalkMap (genericPoint (primeDivisorNormalizationScheme P))).hom.injective
  have hiso : IsIso (ψ.stalkMap (genericPoint (primeDivisorNormalizationScheme P))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinjψ, hsurjψ⟩
  have hbir : IsBirational ψ := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
      exact Set.bijOn_singleton.mpr hψη
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      exact hiso
  exact ⟨hstr, hprop, Oai4C1.CommonModel.isBirationalMorphism_of_isBirational ψ hbir⟩

end FlipNormalization

section Chain

open MMP.Flips

/-- A proper curve contracted by `ψ` is, with its reduced structure, a `ψ`-exceptional curve. -/
private theorem exists_isExceptionalCurve_of_isContractedBy {k : Type} [Field k]
    {Y Y' : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} (ψ : Y ⟶ Y') (C : ProperCurve sY)
    (hC : C.IsContractedBy ψ) : ∃ C' : Y.IdealSheafData, IsExceptionalCurve ψ C' := by
  refine ⟨Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure {C.point}),
    ⟨StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure, C.dim_eq⟩, ψ C.point, ?_⟩
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hC x hx
  · rintro rfl
    exact ⟨C.point, subset_closure rfl, rfl⟩

/-- The finiteness instances carried by a normal variety. -/
private theorem normalVariety_instances {K : Type} [Field K] {Z : Scheme.{0}}
    {s : Z ⟶ Spec (.of K)} (h : IsNormalVariety K s) :
    IsIntegral Z ∧ IsNormal Z ∧ IsLocallyNoetherian Z ∧ CompactSpace Z ∧
      TopologicalSpace.NoetherianSpace Z := by
  have := h.1
  have := h.2
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Z := ⟨⟩
  exact ⟨h.1.toIsIntegral, h.2, inferInstance, inferInstance, inferInstance⟩

/-- **Exceptional curves pull back along birational morphisms of surfaces.** If `h : A ⟶ B` is a
proper birational morphism of normal surfaces and `E` is a `ψ`-exceptional curve on `B`, then
the birational transform `h⁻¹_* E` is an `(h ≫ ψ)`-exceptional curve on `A`. -/
private theorem isExceptionalCurve_comp {K : Type} [Field K] {A B C : Scheme.{0}}
    {sA : A ⟶ Spec (.of K)} {sB : B ⟶ Spec (.of K)} (hA : IsNormalVariety K sA)
    (hB : IsNormalVariety K sB) (hdA : topologicalKrullDim A = 2)
    (hdB : topologicalKrullDim B = 2) (h : A ⟶ B) [IsProper h] (hb : IsBirationalMorphism h)
    (ψ : B ⟶ C) {E : B.IdealSheafData} (hE : IsExceptionalCurve ψ E) :
    ∃ E' : A.IdealSheafData, IsExceptionalCurve (h ≫ ψ) E' := by
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hA
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances hB
  obtain ⟨hcurve, himage⟩ := isCurveIn_inverseTransformIdeal h
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb) hdA.le hdB hE.1
  obtain ⟨x, hx⟩ := hE.2
  refine ⟨_, hcurve, x, ?_⟩
  have hc : (h ≫ ψ).base '' (inverseTransform h E.support : Set A) =
      ψ.base '' (h.base '' (inverseTransform h E.support : Set A)) := by
    rw [Set.image_image]; rfl
  rw [support_inverseTransformIdeal, hc]
  exact (congrArg _ himage).trans hx

/-- The indices of a chain of contractions: `0`, then one past each contracting step. -/
private def chainIndex (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => t n + 1

/-- **Contractions along a chain of normal surfaces are finitely many.** In a chain
`N 0 → N 1 → ⋯` of proper birational morphisms of normal surfaces over a field of characteristic
zero, only finitely many steps map a curve to a point. -/
private theorem finite_setOf_exists_isExceptionalCurve {K : Type} [Field K] [CharZero K]
    (N : ℕ → Scheme.{0}) (s : ∀ j, N j ⟶ Spec (.of K)) (ψ : ∀ j, N j ⟶ N (j + 1))
    (hN : ∀ j, IsNormalVariety K (s j) ∧ topologicalKrullDim (N j) = 2)
    (hψ : ∀ j, ψ j ≫ s (j + 1) = s j ∧ IsProper (ψ j) ∧ IsBirationalMorphism (ψ j)) :
    {j | ∃ C : (N j).IdealSheafData, IsExceptionalCurve (ψ j) C}.Finite := by
  set B := {j | ∃ C : (N j).IdealSheafData, IsExceptionalCurve (ψ j) C}
  obtain ⟨M, hM⟩ := MMP.Mori.exists_forall_length_le_of_isExceptionalCurve_chain K (s 0)
    (hN 0).1 (hN 0).2
  by_contra hinf
  have hcomp : ∀ a b, a ≤ b → ∃ h : N a ⟶ N b,
      h ≫ s b = s a ∧ IsProper h ∧ IsBirationalMorphism h := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨𝟙 _, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _⟩
    | succ b _ ih =>
      obtain ⟨h, h1, h2, h3⟩ := ih
      obtain ⟨g1, g2, g3⟩ := hψ b
      obtain ⟨_, _, _, _, _⟩ := normalVariety_instances (hN a).1
      obtain ⟨_, _, _, _, _⟩ := normalVariety_instances (hN b).1
      obtain ⟨_, _, _, _, _⟩ := normalVariety_instances (hN (b + 1)).1
      refine ⟨h ≫ ψ b, by rw [Category.assoc, g1, h1], inferInstance, ?_⟩
      exact isBirationalMorphism_comp_of_isBirational (ψ b) h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism g3)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h3)
  have hinf' : (Set.ofPred (· ∈ B)).Infinite := hinf
  set t := Nat.nth (· ∈ B)
  have ht : ∀ n, chainIndex t n ≤ t n := by
    intro n
    cases n with
    | zero => exact Nat.zero_le _
    | succ n => exact Nat.nth_strictMono hinf' (Nat.lt_succ_self n)
  choose h hh using fun n ↦ hcomp (chainIndex t n) (t n) (ht n)
  have key := hM (M + 1) (fun n ↦ N (chainIndex t n)) (fun n ↦ s (chainIndex t n))
    (fun n ↦ h n ≫ ψ (t n)) (Iso.refl _) (Category.id_comp _) (fun i _ ↦ hN _) ?_
  · omega
  intro i _
  show (h i ≫ ψ (t i)) ≫ s (t i + 1) = s (chainIndex t i) ∧ IsProper (h i ≫ ψ (t i)) ∧
    IsBirationalMorphism (h i ≫ ψ (t i)) ∧
      ∃ C : (N (chainIndex t i)).IdealSheafData, IsExceptionalCurve (h i ≫ ψ (t i)) C
  obtain ⟨h1, h2, h3⟩ := hh i
  obtain ⟨g1, g2, g3⟩ := hψ (t i)
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances (hN (chainIndex t i)).1
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances (hN (t i)).1
  obtain ⟨_, _, _, _, _⟩ := normalVariety_instances (hN (t i + 1)).1
  refine ⟨by simp only [Category.assoc]; rw [g1, h1], inferInstance, ?_, ?_⟩
  · exact isBirationalMorphism_comp_of_isBirational (ψ (t i)) (h i)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism g3)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism h3)
  · obtain ⟨E, hE⟩ : t i ∈ B := Nat.nth_mem_of_infinite hinf' i
    exact isExceptionalCurve_comp (hN _).1 (hN _).1 (hN _).2 (hN _).2 (h i) h3 (ψ (t i)) hE

end Chain

section Divisors

variable {X Y : Scheme.{0}}

open Classical in
/-- The coefficient of `Q` in the image of `D` under a partial map of prime divisors is the sum of
the coefficients of the prime divisors sent to `Q`. -/
private theorem mapPrimeDivisors_apply
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X)
    (Q : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.mapPrimeDivisors φ D Q = D.sum fun P r => if φ P = some Q then r else 0 := by
  rw [DivisorWithCoeffs.mapPrimeDivisors, Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  refine Finsupp.sum_congr fun P _ => ?_
  rcases h : φ P with _ | Q'
  · simp
  · simp [Finsupp.single_apply]

/-- The transform of an effective divisor is effective. -/
private theorem transformDivisor_apply_nonneg (f : MMP.Mori.RationalMap X Y) {D : Divisor X}
    (hD : ∀ P, 0 ≤ D P) (Q : MMP.Mori.PrimeDivisor Y) :
    0 ≤ MMP.Mori.RationalMap.transformDivisor f D Q := by
  classical
  rw [MMP.Mori.RationalMap.transformDivisor, mapPrimeDivisors_apply, Finsupp.sum]
  exact Finset.sum_nonneg fun P _ => by split_ifs <;> simp [hD P]

/-- For an effective divisor `D`, the coefficient of `f_* P` in `f_* D` is at least that of `P`
in `D`. -/
private theorem le_transformDivisor_apply (f : MMP.Mori.RationalMap X Y) {D : Divisor X}
    (hD : ∀ P, 0 ≤ D P) {P : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (hP : MMP.Mori.RationalMap.transformPrimeDivisor f P = some Q) :
    D P ≤ MMP.Mori.RationalMap.transformDivisor f D Q := by
  classical
  by_cases hPs : P ∈ D.support
  · rw [MMP.Mori.RationalMap.transformDivisor, mapPrimeDivisors_apply, Finsupp.sum]
    have h := Finset.single_le_sum (f := fun P => if f.transformPrimeDivisor P = some Q then D P
      else 0) (fun P _ => by split_ifs <;> simp [hD P]) hPs
    simpa [hP] using h
  · rw [Finsupp.notMem_support_iff.mp hPs]
    exact transformDivisor_apply_nonneg f hD Q

/-- A prime divisor with nonzero coefficient in `f_* D` is the transform of a prime divisor with
nonzero coefficient in `D`. -/
private theorem exists_of_transformDivisor_apply_ne_zero (f : MMP.Mori.RationalMap X Y)
    {D : Divisor X} {Q : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformDivisor f D Q ≠ 0) :
    ∃ P, D P ≠ 0 ∧ MMP.Mori.RationalMap.transformPrimeDivisor f P = some Q := by
  classical
  rw [MMP.Mori.RationalMap.transformDivisor, mapPrimeDivisors_apply] at h
  obtain ⟨P, hP, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨P, Finsupp.mem_support_iff.mp hP, ?_⟩
  by_contra hc
  exact hne (if_neg hc)

/-- An irreducible set contained in the support of a divisor lies in one of its components. -/
private theorem exists_subset_support_of_subset_supp {D : Divisor X} {C : Set X}
    (hC : IsIrreducible C) (h : C ⊆ (D.supp : Set X)) :
    ∃ P, D P ≠ 0 ∧ C ⊆ P.support := by
  classical
  suffices ∀ s : Finset (MMP.Mori.PrimeDivisor X),
      C ⊆ ((s.sup fun E => E.idealSheaf.support : TopologicalSpace.Closeds X) : Set X) →
        ∃ P ∈ s, C ⊆ P.support by
    obtain ⟨P, hP, hCP⟩ := this D.support h
    exact ⟨P, Finsupp.mem_support_iff.mp hP, hCP⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    obtain ⟨x, hx⟩ := hC.nonempty
    simpa using hs hx
  | insert a s _ ih =>
    intro hs
    rw [Finset.sup_insert, TopologicalSpace.Closeds.coe_sup] at hs
    obtain ⟨z, hz, hCz⟩ := isIrreducible_iff_sUnion_isClosed.mp hC
      {(a.idealSheaf.support : Set X), ((s.sup fun E => E.idealSheaf.support :
        TopologicalSpace.Closeds X) : Set X)}
      (by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact a.idealSheaf.support.isClosed
        · rw [Finset.mem_singleton.mp hz]; exact TopologicalSpace.Closeds.isClosed _)
      (by rw [Finset.coe_insert, Finset.coe_singleton, Set.sUnion_insert, Set.sUnion_singleton]
          exact hs)
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact ⟨a, Finset.mem_insert_self _ _, hCz⟩
    · rw [Finset.mem_singleton.mp hz'] at hCz
      obtain ⟨P, hP, hCP⟩ := ih hCz
      exact ⟨P, Finset.mem_insert_of_mem hP, hCP⟩

end Divisors

/-! ### Eventually no flipping curve lies in a divisor (FA 4.13.3) -/

section Family

open MMP.Flips

variable {M : ℕ → Scheme.{0}} [∀ i, IsLocallyNoetherian (M i)] [∀ i, IsNormal (M i)]
  [∀ i, CompactSpace (M i)] {s : ∀ i, M i ⟶ Spec (.of ℂ)} {Zf : ℕ → Scheme.{0}}
  {sZf : ∀ i, Zf i ⟶ Spec (.of ℂ)} {φ : ∀ i, M i ⟶ Zf i} {φp : ∀ i, M (i + 1) ⟶ Zf i}
  {g : ∀ i, (M i).RationalMap (M (i + 1))} {E : ∀ i, RDivisor (M i)}

/-- The successive transforms `P, g_a* P, g_{a+1}* g_a* P, …` of a prime divisor `P` of `M_a`
along a family of birational maps, `none` from the first step at which the transform is not a
prime divisor. -/
private noncomputable def flipChain (g : ∀ i, (M i).RationalMap (M (i + 1))) (a : ℕ)
    (P : MMP.Mori.PrimeDivisor (M a)) : ∀ j, Option (MMP.Mori.PrimeDivisor (M (a + j)))
  | 0 => some P
  | j + 1 => (flipChain g a P j).bind (MMP.Mori.RationalMap.transformPrimeDivisor (g (a + j)))

private theorem flipChain_succ (a : ℕ) (P : MMP.Mori.PrimeDivisor (M a)) (j : ℕ) :
    flipChain g a P (j + 1) =
      (flipChain g a P j).bind (MMP.Mori.RationalMap.transformPrimeDivisor (g (a + j))) :=
  rfl

/-- Once the chain of transforms stops, it stays stopped. -/
private theorem flipChain_eq_none_of_le (a : ℕ) (P : MMP.Mori.PrimeDivisor (M a)) {j j' : ℕ}
    (hjj' : j ≤ j') (h : flipChain g a P j = none) : flipChain g a P j' = none := by
  induction j', hjj' using Nat.le_induction with
  | base => exact h
  | succ m _ ih => rw [flipChain_succ, ih, Option.bind_none]

/-- The chain of transforms stops at most once. -/
private theorem subsingleton_setOf_flipChain_stops (a : ℕ) (P : MMP.Mori.PrimeDivisor (M a)) :
    {j | (flipChain g a P j).isSome ∧ flipChain g a P (j + 1) = none}.Subsingleton := by
  intro j hj j' hj'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · simp [flipChain_eq_none_of_le a P (Nat.succ_le_of_lt h) hj.2] at hj'
  · simp [flipChain_eq_none_of_le a P (Nat.succ_le_of_lt h) hj'.2] at hj

/-- **Flipping curves in a chain of transforms are finitely many.** -/
private theorem finite_setOf_exists_isFlippingCurve_subset
    (hflip : ∀ i, IsFlip ℂ (s i) (sZf i) (s (i + 1)) (E i) (φ i) (φp i) (g i))
    (hdim : ∀ i, topologicalKrullDim (M i) = 3) (a : ℕ)
    (Q : ∀ j, MMP.Mori.PrimeDivisor (M (a + j)))
    (hQ : ∀ j, MMP.Mori.RationalMap.transformPrimeDivisor (g (a + j)) (Q j) = some (Q (j + 1)))
    (hno : ∀ j, ∀ C : Set (M (a + j + 1)),
      IsFlippedCurveOf ℂ (s (a + j)) (sZf (a + j)) (s (a + j + 1)) (E (a + j)) (φ (a + j))
        (φp (a + j)) (g (a + j)) C → ¬ C ⊆ (Q (j + 1)).support) :
    {j | ∃ C, IsFlippingCurve ℂ (s (a + j)) (sZf (a + j)) (φ (a + j)) C ∧
      C ⊆ (Q j).support}.Finite := by
  have hvar i : MMP.Mori.IsVariety ℂ (s i) := (hflip i).isNormalVariety_source.1
  have hA : ∀ j, ∃ ψ : primeDivisorNormalizationScheme (Q j) ⟶
      primeDivisorNormalizationScheme (Q (j + 1)),
      ∃ g₀ : (M (a + j)).PartialMap (M (a + j + 1)), g₀.toRationalMap = g (a + j) ∧
        ∃ U : (primeDivisorNormalizationScheme (Q j)).Opens,
          Dense (U : Set (primeDivisorNormalizationScheme (Q j))) ∧
          ∃ hU : U ≤ primeDivisorNormalization (Q j) ⁻¹ᵁ g₀.domain,
            U.ι ≫ ψ ≫ primeDivisorNormalization (Q (j + 1)) =
              (primeDivisorNormalization (Q j)).resLE g₀.domain U hU ≫ g₀.hom := fun j =>
    exists_normalization_hom_of_forall_isFlippedCurveOf_not_subset ℂ _ _ _ _ _ _ _
      (hflip (a + j)) (hdim _) (Q j) (Q (j + 1)) (hQ j) (hno j)
  choose ψ hψ using hA
  have hspec j : ψ j ≫ primeDivisorNormalization (Q (j + 1)) ≫ s (a + j + 1) =
      primeDivisorNormalization (Q j) ≫ s (a + j) ∧
      IsProper (ψ j) ∧ IsBirationalMorphism (ψ j) :=
    normalization_hom_spec (hflip (a + j)) (hQ j) (ψ j) (hψ j)
  refine (finite_setOf_exists_isExceptionalCurve (K := ℂ)
    (fun j => primeDivisorNormalizationScheme (Q j))
    (fun j => primeDivisorNormalization (Q j) ≫ s (a + j)) ψ
    (fun j => ⟨isNormalVariety_normalization _ (hvar _) _,
      topologicalKrullDim_normalization _ (hvar _) (hdim _) _⟩) hspec).subset
    fun j ⟨C, hC, hCQ⟩ => ?_
  obtain ⟨C', hC'⟩ := IsFlip.exists_properCurve_isContractedBy_normalization
    (hflip (a + j)) (hdim _) (hQ j) (hno j) ⟨C, hC, hCQ⟩ (ψ j) (hψ j)
  exact exists_isExceptionalCurve_of_isContractedBy (ψ j) C' hC'

/-- **FA Claim 4.13.3 for a family of flips.** Let `g_i : M_i ⤏ M_{i+1}` be flips of threefolds
and `G_i` effective divisors with `G_{i+1} = g_{i*} G_i`. If from `i₀` on no flipped curve lies in
`G_{i+1}`, then from some later index on no flipping curve lies in `G_i`. -/
private theorem exists_forall_not_subset_supp_of_isFlippingCurve_family
    (hflip : ∀ i, IsFlip ℂ (s i) (sZf i) (s (i + 1)) (E i) (φ i) (φp i) (g i))
    (hdim : ∀ i, topologicalKrullDim (M i) = 3)
    (G : ∀ i, Divisor (M i)) (hG0 : ∀ P, 0 ≤ G 0 P)
    (hG : ∀ i, G (i + 1) = MMP.Mori.RationalMap.transformDivisor (g i) (G i)) (i₀ : ℕ)
    (h₀ : ∀ i ≥ i₀, ∀ C : Set (M (i + 1)), IsFlippingCurve ℂ (s (i + 1)) (sZf i) (φp i) C →
      ¬ C ⊆ (G (i + 1)).supp) :
    ∃ i₁ ≥ i₀, ∀ i ≥ i₁, ∀ C : Set (M i), IsFlippingCurve ℂ (s i) (sZf i) (φ i) C →
      ¬ C ⊆ (G i).supp := by
  classical
  -- The transforms `G_i` are effective.
  have hnonneg : ∀ i P, 0 ≤ G i P := by
    intro i
    induction i with
    | zero => exact hG0
    | succ i ih =>
      intro P
      rw [hG i]
      exact transformDivisor_apply_nonneg _ ih P
  -- Transforms of components of `G_{i₀}` stay components.
  have hpos : ∀ (P : MMP.Mori.PrimeDivisor (M i₀)), G i₀ P ≠ 0 → ∀ j Q,
      flipChain g i₀ P j = some Q → G (i₀ + j) Q ≠ 0 := by
    intro P hP j
    induction j with
    | zero =>
      intro Q hQ
      cases Option.some.inj hQ
      exact hP
    | succ j ih =>
      intro Q hQ
      rw [flipChain_succ, Option.bind_eq_some_iff] at hQ
      obtain ⟨Q', hQ', hQQ'⟩ := hQ
      have h1 := lt_of_le_of_ne (hnonneg _ Q') (Ne.symm (ih Q' hQ'))
      have h2 := le_transformDivisor_apply (g (i₀ + j)) (hnonneg (i₀ + j)) hQQ'
      rw [← hG (i₀ + j)] at h2
      exact (lt_of_lt_of_le h1 h2).ne'
  -- Every component of `G_{i₀ + j}` is the transform of a component of `G_{i₀}`.
  have hcover : ∀ j (Q : MMP.Mori.PrimeDivisor (M (i₀ + j))), G (i₀ + j) Q ≠ 0 →
      ∃ P, G i₀ P ≠ 0 ∧ flipChain g i₀ P j = some Q := by
    intro j
    induction j with
    | zero => exact fun Q hQ => ⟨Q, hQ, rfl⟩
    | succ j ih =>
      intro Q hQ
      have hQ' : MMP.Mori.RationalMap.transformDivisor (g (i₀ + j)) (G (i₀ + j)) Q ≠ 0 :=
        by rwa [← hG (i₀ + j)]
      obtain ⟨Q', hQ'0, hQQ'⟩ := exists_of_transformDivisor_apply_ne_zero _ hQ'
      obtain ⟨P, hP, hPQ'⟩ := ih Q' hQ'0
      exact ⟨P, hP, by rw [flipChain_succ, hPQ', Option.bind_some, hQQ']⟩
  -- The index at which a chain stops.
  let Death (P : MMP.Mori.PrimeDivisor (M i₀)) : Set ℕ :=
    {j | (flipChain g i₀ P j).isSome ∧ flipChain g i₀ P (j + 1) = none}
  -- The indices at which a flipping curve lies in a component that has a transform.
  let Contr (P : MMP.Mori.PrimeDivisor (M i₀)) : Set ℕ :=
    {j | ∃ Q₀, flipChain g i₀ P j = some Q₀ ∧ (flipChain g i₀ P (j + 1)).isSome ∧
      ∃ C, IsFlippingCurve ℂ (s (i₀ + j)) (sZf (i₀ + j)) (φ (i₀ + j)) C ∧ C ⊆ Q₀.support}
  have hContr : ∀ P, G i₀ P ≠ 0 → (Contr P).Finite := by
    intro P hP
    by_contra hinf
    -- The chain never stops.
    have hsome : ∀ j, (flipChain g i₀ P j).isSome := by
      intro j
      obtain ⟨j', ⟨Q₀, hQ₀, -⟩, hjj'⟩ := Set.Infinite.exists_gt hinf j
      rcases h : flipChain g i₀ P j with _ | Q
      · simp [flipChain_eq_none_of_le i₀ P hjj'.le h] at hQ₀
      · rfl
    let Q j : MMP.Mori.PrimeDivisor (M (i₀ + j)) := (flipChain g i₀ P j).get (hsome j)
    have hQc j : flipChain g i₀ P j = some (Q j) := (Option.some_get _).symm
    have hQ j : MMP.Mori.RationalMap.transformPrimeDivisor (g (i₀ + j)) (Q j) =
        some (Q (j + 1)) := by
      simpa [flipChain_succ, hQc j] using hQc (j + 1)
    refine hinf ((finite_setOf_exists_isFlippingCurve_subset hflip hdim i₀ Q hQ
      fun j C hC hCQ => h₀ (i₀ + j) (Nat.le_add_right _ _) C hC.2
        (hCQ.trans
          (DivisorWithCoeffs.support_subset_supp (hpos P hP _ _ (hQc (j + 1)))))).subset ?_)
    rintro j ⟨Q₀, hQ₀, -, hC⟩
    rw [hQc j, Option.some_inj] at hQ₀
    subst hQ₀
    exact hC
  -- Every bad index lies in a finite set.
  have hF : (⋃ P ∈ (G i₀).support, (Death P ∪ Contr P)).Finite :=
    (G i₀).support.finite_toSet.biUnion fun P hP =>
      (subsingleton_setOf_flipChain_stops i₀ P).finite.union
        (hContr P (Finsupp.mem_support_iff.mp hP))
  obtain ⟨m, hm⟩ := hF.bddAbove
  refine ⟨i₀ + m + 1, by omega, fun i hi C hC hCsub => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show i₀ ≤ i by omega)
  obtain ⟨-, -, -, -, z, -, hmax, -⟩ := id hC
  obtain ⟨Q₀, hQ₀, hCQ₀⟩ := exists_subset_support_of_subset_supp hmax.1.1 hCsub
  obtain ⟨P, hP, hcP⟩ := hcover j Q₀ hQ₀
  have hjF : j ∈ ⋃ P ∈ (G i₀).support, (Death P ∪ Contr P) := by
    refine Set.mem_biUnion (Finsupp.mem_support_iff.mpr hP) ?_
    rcases h : flipChain g i₀ P (j + 1) with _ | Q₁
    · exact Or.inl ⟨by rw [hcP]; rfl, h⟩
    · exact Or.inr ⟨Q₀, hcP, by rw [h]; rfl, C, hC, hCQ₀⟩
  have := hm hjF
  omega

end Family

section FlippedCurve

/-- A subset containing two distinct points `a ⤳ b` of a `T₀` space has positive topological
Krull dimension. -/
private theorem topologicalKrullDim_pos_of_specializes {α : Type*} [TopologicalSpace α]
    [T0Space α] {T : Set α} {a b : α} (ha : a ∈ T) (hb : b ∈ T) (hab : a ⤳ b) (hne : a ≠ b) :
    0 < topologicalKrullDim T := by
  let A : IrreducibleCloseds T :=
    ⟨closure {⟨a, ha⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds T :=
    ⟨closure {⟨b, hb⟩}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hsp : (⟨a, ha⟩ : T) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  have hBA : B < A := by
    refine lt_of_le_of_ne ?_ fun h => hne ?_
    · change closure {(⟨b, hb⟩ : T)} ⊆ closure {⟨a, ha⟩}
      exact closure_minimal (Set.singleton_subset_iff.mpr hsp.mem_closure) isClosed_closure
    · have hmem : (⟨a, ha⟩ : T) ∈ closure {(⟨b, hb⟩ : T)} := by
        change (⟨a, ha⟩ : T) ∈ (B : Set T)
        rw [h]
        exact subset_closure rfl
      have hba : (⟨b, hb⟩ : T) ⤳ ⟨a, ha⟩ := specializes_iff_mem_closure.mpr hmem
      exact congrArg Subtype.val (hsp.antisymm hba).eq
  exact Order.krullDim_pos_iff.mpr ⟨B, A, hBA⟩

/-- A birational contraction onto a normal variety without flipping curves is an isomorphism:
an infinite fibre over a closed point has an infinite irreducible component, which has positive
dimension; so every fibre over a closed point is finite, the open finite-fibre locus contains every
closed point and is everything, and the morphism is an isomorphism over it. -/
private theorem isIso_of_forall_not_isFlippingCurve {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z} [IsNormal Z]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (hf : MMP.Flips.IsBirationalContraction k sZ sY f)
    (h : ∀ C, ¬ MMP.Flips.IsFlippingCurve k sY sZ f C) :
    IsIso f := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isVariety_source.toIsIntegral
  have : IsNoetherian Y := ⟨⟩
  have hfp := hf.isProper
  have hb : IsBirational f := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
    hf.surjective_and_isBirational.2
  obtain ⟨hU, hI⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f hb).1 hfp
  have hall : MMP.Resolution.Bridges.finiteFibreLocus f = Set.univ := by
    by_contra hne
    have : CompactSpace Z :=
      hf.surjective_and_isBirational.1.surj.compactSpace f.continuous
    obtain ⟨z, hz, hzc⟩ := hU.isClosed_compl.exists_closed_singleton
      (Set.nonempty_compl.mpr hne)
    have hinf : (f ⁻¹' {z}).Infinite := hz
    have hFc : IsClosed (f ⁻¹' {z}) := hzc.preimage f.continuous
    obtain ⟨S, hSf, hScl, hSirr, hFS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible hFc
    obtain ⟨t, htS, htinf⟩ : ∃ t ∈ S, t.Infinite := by
      by_contra! hfin
      exact hinf (hFS ▸ hSf.sUnion fun t ht => hfin t ht)
    obtain ⟨t', htt', ht'max⟩ := hSf.exists_le_maximal htS
    have ht'S : t' ∈ S := ht'max.prop
    have ha := (hScl t' ht'S).closure_eq ▸ (hSirr t' ht'S).isGenericPoint_genericPoint_closure
    obtain ⟨c, hct, hca⟩ :=
      (htinf.diff (Set.finite_singleton (hSirr t' ht'S).genericPoint)).nonempty
    have ht'F : t' ⊆ f ⁻¹' {z} := hFS ▸ Set.subset_sUnion_of_mem ht'S
    refine h t' ⟨hf.isVariety_source, hf.isVariety_target, hf.comp_eq, hfp, z, hzc,
      ⟨⟨hSirr t' ht'S, ht'F⟩, ?_⟩,
      topologicalKrullDim_pos_of_specializes ha.mem (htt' hct) (ha.specializes (htt' hct))
        fun h => hca h.symm⟩
    rintro U ⟨hUirr, hUF⟩ htU
    obtain ⟨s, hs, hUs⟩ := (isIrreducible_iff_sUnion_isClosed.mp hUirr) hSf.toFinset
      (fun s hs => hScl s (hSf.mem_toFinset.mp hs))
      (by rwa [Set.Finite.coe_toFinset, ← hFS])
    exact hUs.trans (ht'max.2 (hSf.mem_toFinset.mp hs) (htU.trans hUs))
  have hI' : IsIso (f ∣_ ⊤) := (show (⟨_, hU⟩ : Z.Opens) = ⊤ from Opens.ext hall) ▸ hI
  exact (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit => (⊤ : Z.Opens)) (by simp)).mpr fun _ => hI'

end FlippedCurve

section FlippingCurve

/-- If `d + c = 3` with `d > 0`, then `c ≤ 2`. -/
private theorem coheight_le_two_of_add_eq_three {d : WithBot ℕ∞} {c : ℕ∞} (h : d + c = 3)
    (hd : 0 < d) : c ≤ 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have h3 : e + c = 3 := WithBot.coe_injective h
    norm_cast at hd
    by_contra hc
    have h4 := add_le_add (Order.one_le_iff_pos.mpr hd) (Order.add_one_le_of_lt (not_le.mp hc))
    rw [h3] at h4
    exact absurd h4 (by decide)

/-- A dimension `d` with `d + 2 = 3` is `1`. -/
private theorem eq_one_of_add_two_eq_three {d : WithBot ℕ∞}
    (h : d + ((2 : ℕ∞) : WithBot ℕ∞) = 3) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have h3 : ((3 : ℕ∞) : WithBot ℕ∞) = 3 := rfl
      rw [← h3, ← WithBot.coe_add, WithBot.coe_inj] at h
      have : n + 2 = 3 := by exact_mod_cast h
      obtain rfl : n = 1 := by omega
      rfl

/-- A flipping curve `C` of a small contraction `φ⁺ : X⁺ ⟶ Z` of a threefold is an irreducible
closed subset of codimension two, whose generic point has coheight two and lies over a point of
`Z` of coheight three: it lies in the exceptional set of `φ⁺`, of codimension at least two, since
off that set `φ⁺` is an isomorphism and the generic point of `C` would be a closed point. -/
private theorem exists_irreducibleCloseds_of_isFlippingCurve {k : Type u} [Field k]
    {X' Z : Scheme.{u}} {sX' : X' ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {φp : X' ⟶ Z}
    [IsIntegral X'] [LocallyOfFiniteType sX'] [IsIntegral Z] [LocallyOfFiniteType sZ]
    (hs : MMP.Flips.IsSmall k sZ sX' φp) (h3 : topologicalKrullDim X' = 3)
    {C : Set X'} (hC : MMP.Flips.IsFlippingCurve k sX' sZ φp C) :
    ∃ W : IrreducibleCloseds X', (W : Set X') = C ∧ IsGenericPoint W.isIrreducible.genericPoint C ∧
      codimension W = 2 ∧ Order.coheight W.isIrreducible.genericPoint = 2 ∧
      Order.coheight (φp W.isIrreducible.genericPoint) = 3 := by
  obtain ⟨-, -, -, -, z, hz, hCmax, hCdim⟩ := hC
  have hF : IsClosed {x : X' | φp x = z} := hz.preimage φp.continuous
  have hCcl : IsClosed C := closure_subset_iff_isClosed.mp
    (hCmax.2 ⟨hCmax.1.1.closure, closure_minimal hCmax.1.2 hF⟩ subset_closure)
  let W : IrreducibleCloseds X' := ⟨C, hCmax.1.1, hCcl⟩
  set ξ := W.isIrreducible.genericPoint
  have hξ : IsGenericPoint ξ C := by
    have h := W.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [W.isClosed.closure_eq] at h
  have hcod : codimension W = Order.coheight ξ := by
    have hEq : (irreducibleSetEquivPoints (α := X')).symm ξ = W := IrreducibleCloseds.ext hξ
    rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX' ξ
  rw [isGenericPoint_def.mp hξ, h3] at hd
  have hle := coheight_le_two_of_add_eq_three hd hCdim
  have hξz : φp ξ = z := hCmax.1.2 (hξ.mem)
  have hdz := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sZ z
  rw [hz.closure_eq, topologicalKrullDim_eq_zero_of_subsingleton, zero_add,
    ← hs.dim_eq, h3] at hdz
  have h3' : Order.coheight z = 3 :=
    WithBot.coe_injective (hdz.trans (WithBot.coe_ofNat 3).symm)
  obtain ⟨V, Wc, hV, hW, hVW, hρ⟩ := hs.exists_isIso
  have hξV : ξ ∈ V := by
    by_contra hξV
    let Vo : X'.Opens := V.compl
    let Wo : Z.Opens := Wc.compl
    let x' : Vo.toScheme := ⟨ξ, hξV⟩
    have e1 : Order.coheight (Vo.ι x') = Order.coheight x' :=
      Topology.IsOpenEmbedding.coheight_eq _ Vo.ι.isOpenEmbedding
    have e2 : Order.coheight ((φp.resLE Wo Vo hVW) x') = Order.coheight x' :=
      Topology.IsOpenEmbedding.coheight_eq _ (φp.resLE Wo Vo hVW).isOpenEmbedding
    have e3 : Order.coheight (Wo.ι ((φp.resLE Wo Vo hVW) x')) =
        Order.coheight ((φp.resLE Wo Vo hVW) x') :=
      Topology.IsOpenEmbedding.coheight_eq _ Wo.ι.isOpenEmbedding
    have e4 : Wo.ι ((φp.resLE Wo Vo hVW) x') = φp ξ := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]; rfl
    have hco : Order.coheight ξ = Order.coheight z := by
      rw [← hξz, ← e4, e3, e2, ← e1]
      rfl
    rw [hco, h3'] at hle
    exact absurd hle (by decide)
  have hge : 2 ≤ Order.coheight ξ := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV ξ hξV
  have h2 : Order.coheight ξ = 2 := le_antisymm hle hge
  exact ⟨W, rfl, hξ, hcod.trans h2, h2, hξz ▸ h3'⟩

/-- A flipping curve of a small contraction of a projective threefold is the closure of a proper
curve contracted by the contraction. -/
private theorem exists_properCurve_of_isFlippingCurve {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] [IsIntegral Z]
    [LocallyOfFiniteType sZ] [IsProper sX] {f : X ⟶ Z} (hs : MMP.Flips.IsSmall ℂ sZ sX f)
    (h3 : topologicalKrullDim X = 3) {C : Set X} (hC : MMP.Flips.IsFlippingCurve ℂ sX sZ f C) :
    ∃ A : ProperCurve sX, A.IsContractedBy f ∧ closure ({A.point} : Set X) = C := by
  obtain ⟨W, hWC, hξ, -, hcoh, -⟩ := exists_irreducibleCloseds_of_isFlippingCurve hs h3 hC
  obtain ⟨-, -, -, -, z, -, hmax, -⟩ := hC
  set ξ := W.isIrreducible.genericPoint
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX ξ
  rw [hcoh, h3] at hd
  have hd1 : topologicalKrullDim (closure ({ξ} : Set X)) = 1 :=
    eq_one_of_add_two_eq_three (by exact_mod_cast hd)
  have hcl : closure ({ξ} : Set X) = C := isGenericPoint_def.mp hξ
  refine ⟨⟨ξ, isProperCurve_of_isProper sX
    ((MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq ξ).trans hd1)⟩, fun x hx => ?_, hcl⟩
  change x ∈ closure {ξ} at hx
  rw [hcl] at hx
  exact (hmax.1.2 hx).trans (hmax.1.2 (hcl ▸ subset_closure rfl)).symm

end FlippingCurve

/-! ### Intersection numbers in relative Picard number one -/

section Sign

open MMP.Flips

variable {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}

/-- A `ℚ`-Cartier divisor `L` with `m L = E` Cartier is presented as `(1/m) E`. -/
private theorem toRDivisor_eq_of_isQCartier {L : QDivisor X} {m : ℕ} (hm : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • L) :
    QDivisor.toRDivisor L = ∑ j : Fin 1, (fun _ => 1 / (m : ℝ)) j •
      Divisor.toRDivisor ((fun _ => E) j) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  ext P
  rw [Fin.sum_univ_one, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    QDivisor.coeff_toRDivisor]
  have h1 := congrArg (fun D : QDivisor X => D.coeff P) hE
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at h1
  have h3 : ((E.coeff P : ℤ) : ℝ) = (m : ℝ) * (L.coeff P : ℝ) := by exact_mod_cast h1
  rw [h3, smul_eq_mul]
  field_simp

/-- A `ℚ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {L : QDivisor X} (hL : L.IsQCartier) :
    IsCartierCombination (QDivisor.toRDivisor L) := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hL.exists_pos
  exact ⟨1, fun _ => 1 / (m : ℝ), fun _ => E, fun _ => hEc, by
    rw [toRDivisor_eq_of_isQCartier hm hE]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

/-- An effective divisor is nonnegative on a proper curve whose closure does not lie in its
support. -/
private theorem intersectionNumber_toQDivisor_nonneg {G : Divisor X} (hG : ∀ P, 0 ≤ G P)
    (hGq : (Divisor.toQDivisor G).IsQCartier) (C : ProperCurve sX)
    (hC : ¬ closure {C.point} ⊆ (G.supp : Set X)) :
    0 ≤ (Divisor.toQDivisor G).intersectionNumber ℂ sX C.ι C.dim_le hGq := by
  refine (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sX _ hGq
    (fun P => by change (0 : ℚ) ≤ ((G P : ℤ) : ℚ); exact_mod_cast hG P) C fun hP => hC ?_).1
  rw [Divisor.supp_toQDivisor] at hP
  exact G.supp.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hP)

/-- **The intersection number of a `ℚ`-Cartier divisor with a curve is a presentation value.** -/
private theorem isRIntersectionNumber_intersectionNumber {L : QDivisor X} (hL : L.IsQCartier)
    (C : ProperCurve sX) : ∃ (m : ℕ) (r : Fin m → ℝ) (E : Fin m → Divisor X),
      IsRIntersectionNumber ℂ sX (QDivisor.toRDivisor L) r E C
        (L.intersectionNumber ℂ sX C.ι C.dim_le hL : ℝ) := by
  obtain ⟨m, hm, E, hE, hEc⟩ := hL.exists_pos
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨1, fun _ => 1 / (m : ℝ), fun _ => E, ?_⟩
  have h := isRIntersectionNumber_of_eq_sum_degreeOn (QDivisor.toRDivisor L) _ _ (fun _ => hEc)
    (toRDivisor_eq_of_isQCartier hm hE) C
  convert h using 1
  rw [Fin.sum_univ_one, MMP.Mori.QDivisor.intersectionNumber_eq_of_smul ℂ sX C.ι C.dim_le L hL hm
    E hEc hE]
  push_cast
  field_simp

/-- A `ℚ`-Cartier divisor of degree `0` on every contracted curve is numerically trivial. -/
private theorem isNumericallyTrivialOver_of_intersectionNumber_eq_zero {Y : Scheme.{0}}
    {f : X ⟶ Y} {L : QDivisor X} (hL : L.IsQCartier)
    (h : ∀ C : ProperCurve sX, C.IsContractedBy f →
      L.intersectionNumber ℂ sX C.ι C.dim_le hL = 0) :
    IsNumericallyTrivialOver ℂ sX f (QDivisor.toRDivisor L) := by
  refine ⟨isCartierCombination_toRDivisor hL, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0,
    by simp⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨_, r, E, hv⟩ := isRIntersectionNumber_intersectionNumber hL C
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hv,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C), h C hC]
  simp

/-- A numerically trivial `ℚ`-Cartier divisor has degree `0` on every contracted curve. -/
private theorem intersectionNumber_eq_zero_of_isNumericallyTrivialOver {Y : Scheme.{0}}
    {f : X ⟶ Y} {L : QDivisor X} (hL : L.IsQCartier)
    (h : IsNumericallyTrivialOver ℂ sX f (QDivisor.toRDivisor L)) {C : ProperCurve sX}
    (hC : C.IsContractedBy f) : L.intersectionNumber ℂ sX C.ι C.dim_le hL = 0 := by
  obtain ⟨_, r, E, hv⟩ := isRIntersectionNumber_intersectionNumber hL C
  exact_mod_cast eq_zero_of_isNumericallyTrivialOver h hC hv

/-- The sum of numerically trivial divisors is numerically trivial. -/
private theorem isNumericallyTrivialOver_add_smul {Y : Scheme.{0}} {f : X ⟶ Y} {T N : RDivisor X}
    (hT : IsNumericallyTrivialOver ℂ sX f T) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyTrivialOver ℂ sX f (T + c • N) := by
  refine ⟨isCartierCombination_add_smul hT.1 hN.1 c, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0,
    by simp⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨_, rT, LT, xT, hxT⟩ := exists_isRIntersectionNumber_of_isCartierCombination hT.1 C
  obtain ⟨_, rN, LN, xN, hxN⟩ := exists_isRIntersectionNumber_of_isCartierCombination hN.1 C
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 T N rT LT rN LN xT xN 1 c hxT hxN
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C), eq_zero_of_isNumericallyTrivialOver hT hC hxT,
    eq_zero_of_isNumericallyTrivialOver hN hC hxN]
  ring

variable (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
  (hf : MMP.Flips.IsContraction ℂ sZ sX f) (hfp : IsProjective f)
  (hρ : MMP.Flips.relativePicardNumber sX f = 1)

include hX hZ hf hfp hρ

/-- In relative Picard number one, a `ℚ`-Cartier divisor positive on one contracted curve is
positive on all of them. -/
private theorem intersectionNumber_pos_of_pos {C₀ C : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (hC : C.IsContractedBy f) {L : QDivisor X} (hL : L.IsQCartier)
    (h : 0 < L.intersectionNumber ℂ sX C₀.ι C₀.dim_le hL) :
    0 < L.intersectionNumber ℂ sX C.ι C.dim_le hL :=
  (isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one sX sZ hX hZ f hf
    hfp hρ C hC L hL).mp
    ((isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one sX sZ hX hZ f hf
      hfp hρ C₀ hC₀ L hL).mpr h)

/-- In relative Picard number one, a `ℚ`-Cartier divisor of degree zero on one contracted curve has
degree zero on all of them. -/
private theorem intersectionNumber_eq_zero_of_eq_zero {C₀ C : ProperCurve sX}
    (hC₀ : C₀.IsContractedBy f) (hC : C.IsContractedBy f) {L : QDivisor X} (hL : L.IsQCartier)
    (h : L.intersectionNumber ℂ sX C₀.ι C₀.dim_le hL = 0) :
    L.intersectionNumber ℂ sX C.ι C.dim_le hL = 0 := by
  have hL' := Oai4C1.isQCartier_neg hL
  rcases lt_trichotomy (L.intersectionNumber ℂ sX C.ι C.dim_le hL) 0 with hlt | heq | hgt
  · have := intersectionNumber_pos_of_pos hX hZ hf hfp hρ hC hC₀ hL'
      (by rw [QDivisor.intersectionNumber_neg ℂ sX C.ι C.dim_le hL hL']; linarith)
    rw [QDivisor.intersectionNumber_neg ℂ sX C₀.ι C₀.dim_le hL hL'] at this
    linarith
  · exact heq
  · have := intersectionNumber_pos_of_pos hX hZ hf hfp hρ hC hC₀ hL hgt
    linarith

end Sign

/-! ### One step -/

section Step

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- **The strict transform of a canonical divisor across a flip is canonical.** If `K` is a
canonical divisor of `X`, then `(f⁺)⁻¹_* f_* K` is a canonical divisor of `X⁺`: `f_* K` is a
canonical divisor of `Z`, which is `f⁺_* K⁺` for a canonical divisor `K⁺` of `X⁺`, and the small
`f⁺` identifies the prime divisors of `X⁺` and `Z`. -/
private theorem isCanonicalDivisor_flipTransform (hX : IsNormalVariety ℂ sX)
    (hX' : IsNormalVariety ℂ sX') (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) {n : ℕ} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := hf.isProper
  haveI : IsProper fp := hfp.isProper
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  have hdimZ : topologicalKrullDim Z = n := by rw [← hf.dim_eq]; exact hK.1
  have hdimX' : topologicalKrullDim X' = n := by rwa [hfp.dim_eq]
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor sZ hZ hdimZ
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sX' hX' hdimX'
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rwa [hf.comp_eq]
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ) := by rwa [hfp.comp_eq]
  haveI : LocallyOfFiniteType (f ≫ sZ) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hX'n.1.toLocallyOfFiniteType
  have hK1 : K.IsCanonicalDivisor (f ≫ sZ) n := by rwa [hf.comp_eq]
  have hK₀' : K₀.IsCanonicalDivisor (fp ≫ sZ) n := by rwa [hfp.comp_eq]
  have h1 := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZ hXn hfb hKZ hK1
  obtain ⟨KY, hKY, hKYeq⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hZ hX'n hfpb h1 hK₀'
  have heq : flipTransform f fp K = flipTransform fp fp KY := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, hKYeq]
  have hid : flipTransform fp fp KY = KY := by
    ext P
    simp only [DivisorWithCoeffs.coeff_apply]
    exact flipTransform_apply_of_isSmall hZ hfp hfp hfpb rfl KY
  rw [heq, hid]
  rw [hfp.comp_eq] at hKY
  exact hKY

/-- Across a step of an extremal real flip sequence, the strict transform of the canonical
divisor `K` is linearly equivalent to the canonical divisor `K⁺`. -/
private theorem linearlyEquivalent_flipTransform (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) :
    MMP.Mori.Divisor.LinearlyEquivalent (flipTransform f fp K) K' := by
  have hE := h.isNegativeExtremalContraction
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  obtain ⟨m, hKm⟩ := hK
  obtain ⟨m', hK'm⟩ := h.isCanonicalDivisor_flip
  exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'
    (isCanonicalDivisor_flipTransform hE.isNormalVariety_source hX' hZ h.isSmall h.isSmall_flip
      h.isBirationalMorphism h.isBirationalMorphism_flip hKm) hK'm

/-- **A step of an extremal real flip sequence is a flip** in the sense of `MMP.Flips.IsFlip`, for
the birational map `(f⁺)⁻¹ ∘ f`, which transforms divisors as the strict transform. -/
private theorem exists_isFlip_of_isRealFlipStep (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ' : IsQFactorial sX') :
    ∃ g : X.RationalMap X',
      MMP.Flips.IsFlip ℂ sX sZ sX' (MMP.Flips.logCanonicalDivisor K B) f fp g ∧
      MMP.Flips.RationalMap.IsOver f fp g ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor g D = flipTransform f fp D) ∧
      ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor g P = some P' := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper fp := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_flip
  obtain ⟨g, hg, hgo, htr, hsurj⟩ := exists_flipMap hX hX' hZ h.isSmall h.isSmall_flip
    h.isBirationalMorphism h.isBirationalMorphism_flip
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_flipTransform h hK
  have htrE : MMP.Mori.RationalMap.transformDivisor g (MMP.Flips.logCanonicalDivisor K B) =
      MMP.Flips.logCanonicalDivisor K' B' + (1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    rw [htr, MMP.Flips.logCanonicalDivisor, map_add,
      flipTransform_toRDivisor hZ h.isSmall h.isSmall_flip h.isBirationalMorphism,
      ← h.eq_flipTransform, ← hφ,
      MMP.Flips.logCanonicalDivisor, one_smul, map_sub]
    abel
  have hnum := isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent (sX := sX') fp
    (Divisor.isCartier_principalDivisor φ) (Divisor.linearlyEquivalent_principalDivisor_zero φ)
  refine ⟨g,
    { isNormalVariety_source := hX
      isNormalVariety_target := hZ
      isNormalVariety_flip := hX'
      isContraction := hE.isContraction
      isCartierCombination := hE.isCartierCombination
      isRelativelyAntiAmple := hE.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := ⟨hg, hgo⟩
      isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX f fp g hgo
      isSmall := h.isSmall_flip
      isCartierCombination_transform := isCartierCombination_of_isQFactorial hQ' _
      isRelativelyAmple_transform := by
        rw [htrE]
        exact isRelativelyAmple_of_isNumericallyEquivalentOver hX' hZ
          h.isProjectiveMorphism_flip h.isSmall_flip.comp_eq
          (isNumericallyEquivalentOver_add_smul
            (isCartierCombination_of_isRelativelyAmple h.isRelativelyAmple_flip) hnum 1)
          h.isRelativelyAmple_flip
      isSmall_source := h.isSmall }, hgo, htr, hsurj⟩

/-- **A numerically trivial log canonical class crosses the flip.** If `K + M + λ G ≡_Z 0` on
`X`, then `K⁺ + M⁺ + λ G⁺ ≡_Z 0` on `X⁺`, where `M⁺`, `G⁺` are strict transforms: the strict
transform of a numerically trivial divisor is numerically trivial (FA 18), and the strict
transform of `K` differs from `K⁺` by a principal divisor. -/
private theorem isNumericallyTrivialOver_flipTransform
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hQ' : IsQFactorial sX') [QuasiCompact sX] [QuasiCompact sX'] (M : QDivisor X)
    {G : Divisor X} {lam : ℚ}
    (hT : MMP.Flips.IsNumericallyTrivialOver ℂ sX f
      (QDivisor.toRDivisor (Divisor.toQDivisor K + M + lam • Divisor.toQDivisor G))) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX' fp (QDivisor.toRDivisor
      (Divisor.toQDivisor K' + flipTransform f fp M +
        lam • Divisor.toQDivisor (flipTransform f fp G))) := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper f := h.isSmall.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  have hcfp : MMP.Flips.IsContraction ℂ sZ sX' fp :=
    h.isSmall_flip.toIsBirationalContraction.toIsContraction
  obtain ⟨g, -, hgo, htr, hsurj⟩ := exists_flipMap hX hX' hZ h.isSmall h.isSmall_flip
    h.isBirationalMorphism h.isBirationalMorphism_flip
  obtain ⟨-, hT'⟩ := MMP.Flips.IsNumericallyTrivialOver.transformDivisor_of_isOver sZ hX hQ'
    hE.isContraction.comp_eq hcfp.comp_eq h.isBirationalMorphism h.isBirationalMorphism_flip hgo
    hsurj hT.1 hT
  rw [htr] at hT'
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_flipTransform h hK
  have heq : QDivisor.toRDivisor (Divisor.toQDivisor K' + flipTransform f fp M +
        lam • Divisor.toQDivisor (flipTransform f fp G)) =
      flipTransform f fp (QDivisor.toRDivisor (Divisor.toQDivisor K + M +
        lam • Divisor.toQDivisor G)) + (-1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    ext Q'
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_eq_of_isSmall h.isSmall_flip h.isSmall Q'
    have hc : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        flipTransform f fp D Q' = D Q := fun D =>
      flipTransform_apply_of_isSmall hZ h.isSmall h.isSmall_flip h.isBirationalMorphism hQ.symm D
    have hφQ := congrArg (fun D : Divisor X' => D Q') hφ
    simp only [Finsupp.coe_sub, Pi.sub_apply, hc K] at hφQ
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.coe_smul, Pi.smul_apply, hc]
    simp only [← DivisorWithCoeffs.coeff_apply, QDivisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor,
      Divisor.coeff_toRDivisor]
    simp only [DivisorWithCoeffs.coeff_apply, hc, ← hφQ]
    push_cast
    ring
  rw [heq]
  exact isNumericallyTrivialOver_add_smul hT'
    (isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent fp
      (Divisor.isCartier_principalDivisor φ)
      (Divisor.linearlyEquivalent_principalDivisor_zero φ)) (-1)

/-- **A divisor containing no flipping and no flipped curve is numerically trivial over the
base.** Let `X ⟶ Z ⟵ X⁺` be a step of an extremal real flip sequence of projective `ℚ`-factorial
threefolds over a projective `Z`, with `(X, B)` real canonical, and `G ≥ 0` a divisor on `X`. If
no flipping curve lies in `Supp G` and no flipped curve lies in the support of the strict
transform `G⁺`, then `G ≡_Z 0` and `G⁺ ≡_Z 0`. -/
private theorem isNumericallyTrivialOver_of_forall_not_subset
    (h : IsRealFlipStep sX sZ sX' K B K' B' f fp) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (hQ : IsQFactorial sX) (hQ' : IsQFactorial sX')
    (hXp : MMP.Mori.IsProjectiveVariety ℂ sX) (hXp' : MMP.Mori.IsProjectiveVariety ℂ sX')
    (hXq : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX)
    (hXq' : AlgebraicGeometry.IsQuasiProjectiveVariety ℂ sX')
    (hd : topologicalKrullDim X = 3) (hd' : topologicalKrullDim X' = 3)
    (hB : IsRealCanonicalPair sX B) {G : Divisor X} (hG : ∀ P, 0 ≤ G P)
    (hGC : ∀ C, MMP.Flips.IsFlippingCurve ℂ sX sZ f C → ¬ C ⊆ (G.supp : Set X))
    (hGC' : ∀ C, MMP.Flips.IsFlippingCurve ℂ sX' sZ fp C →
      ¬ C ⊆ ((flipTransform f fp G).supp : Set X')) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX f (Divisor.toRDivisor G) ∧
      MMP.Flips.IsNumericallyTrivialOver ℂ sX' fp (Divisor.toRDivisor (flipTransform f fp G)) := by
  classical
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'.1.toQuasiCompact
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsProper sX :=
    isProper_of_isProjectiveMorphism _ ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sX).mp hXp).2
  haveI : IsProper sX' :=
    isProper_of_isProjectiveMorphism _ ((AlgebraicGeometry.isProjectiveVariety_iff ℂ sX').mp hXp').2
  haveI : IsProper f := h.isSmall.isProper
  haveI : IsProper fp := h.isSmall_flip.isProper
  have hfP : IsProjective f := IsProjectiveMorphism.isProjective h.isProjectiveMorphism
  have hfpP : IsProjective fp := IsProjectiveMorphism.isProjective h.isProjectiveMorphism_flip
  have hcf := hE.isContraction
  have hcfp : MMP.Flips.IsContraction ℂ sZ sX' fp :=
    h.isSmall_flip.toIsBirationalContraction.toIsContraction
  have hρ := hE.relativePicardNumber_eq_one
  have hρ' := h.relativePicardNumber_flip
  -- flipping curves on both sides, and the proper curves they are
  obtain ⟨Γ, hΓ⟩ : ∃ Γ, MMP.Flips.IsFlippingCurve ℂ sX sZ f Γ := by
    by_contra hno
    push Not at hno
    exact h.not_isIso (isIso_of_forall_not_isFlippingCurve h.isSmall.toIsBirationalContraction hno)
  obtain ⟨Γ', hΓ'⟩ : ∃ Γ, MMP.Flips.IsFlippingCurve ℂ sX' sZ fp Γ := by
    by_contra hno
    push Not at hno
    exact h.not_isIso_flip
      (isIso_of_forall_not_isFlippingCurve h.isSmall_flip.toIsBirationalContraction hno)
  obtain ⟨C₀, hC₀, hC₀Γ⟩ := exists_properCurve_of_isFlippingCurve h.isSmall hd hΓ
  obtain ⟨C₀', hC₀', hC₀'Γ⟩ := exists_properCurve_of_isFlippingCurve h.isSmall_flip hd' hΓ'
  -- the flip as a birational map, and a rational canonical witness for the step
  obtain ⟨g, -, hgo, htr, hsurj⟩ := exists_flipMap hX hX' hZ h.isSmall h.isSmall_flip
    h.isBirationalMorphism h.isBirationalMorphism_flip
  obtain ⟨-, B₀, -, -, h₀⟩ := h.exists_isRealCanonicalPair_qDivisor hK hQ hQ' hXq hXq' hd hd' hB
  have hcoeff : ∀ Q' : MMP.Mori.PrimeDivisor X', ∃ Q : MMP.Mori.PrimeDivisor X,
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        flipTransform f fp D Q' = D Q := fun Q' => by
    obtain ⟨Q, hQ⟩ := exists_primeDivisor_map_eq_of_isSmall h.isSmall_flip h.isSmall Q'
    exact ⟨Q, fun D => flipTransform_apply_of_isSmall hZ h.isSmall h.isSmall_flip
      h.isBirationalMorphism hQ.symm D⟩
  have hG' : ∀ Q', 0 ≤ flipTransform f fp G Q' := fun Q' => by
    obtain ⟨Q, hQ⟩ := hcoeff Q'
    rw [hQ]; exact hG Q
  have hGq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (Divisor.toQDivisor G)
  have hGq' := MMP.Fourfold.isQCartier_of_isQFactorial sX' hQ'
    (Divisor.toQDivisor (flipTransform f fp G))
  set L₀ : QDivisor X := Divisor.toQDivisor K + B₀
  set L₀' : QDivisor X' := Divisor.toQDivisor K' + flipTransform f fp B₀
  have hL₀ := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ L₀
  have hL₀' := MMP.Fourfold.isQCartier_of_isQFactorial sX' hQ' L₀'
  have hnL₀ := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (-L₀)
  have htoR : ∀ {W : Scheme.{0}} (D : Divisor W) (E : QDivisor W),
      QDivisor.toRDivisor (Divisor.toQDivisor D + E) =
        MMP.Flips.logCanonicalDivisor D (QDivisor.toRDivisor E) := fun D E => by
    rw [map_add, QDivisor.toRDivisor_toQDivisor]; rfl
  -- `K + B₀` is negative on `C₀` and `K⁺ + B₀⁺` is positive on `C₀⁺`
  have hneg : L₀.intersectionNumber ℂ sX C₀.ι C₀.dim_le hL₀ < 0 := by
    have h1 :=
      (MMP.Flips.isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one
        sX sZ hX hZ f hcf hfP hρ C₀ hC₀ (-L₀) hnL₀).mp (by
        rw [map_neg, htoR]; exact h₀.isNegativeExtremalContraction.isRelativelyAntiAmple)
    rw [QDivisor.intersectionNumber_neg ℂ sX C₀.ι C₀.dim_le hL₀ hnL₀] at h1
    linarith
  have hpos' : 0 < L₀'.intersectionNumber ℂ sX' C₀'.ι C₀'.dim_le hL₀' :=
    (MMP.Flips.isRelativelyAmple_iff_intersectionNumber_pos_of_relativePicardNumber_eq_one
      sX' sZ hX' hZ fp hcfp hfpP hρ' C₀' hC₀' L₀' hL₀').mp (by
        rw [htoR]; exact h₀.isRelativelyAmple_flip)
  -- `G` and `G⁺` are nonnegative on the flipping and flipped curves
  have hnn := intersectionNumber_toQDivisor_nonneg hG hGq C₀ (by rw [hC₀Γ]; exact hGC Γ hΓ)
  have hnn' := intersectionNumber_toQDivisor_nonneg hG' hGq' C₀' (by rw [hC₀'Γ]; exact hGC' Γ' hΓ')
  -- `G · C₀ = 0`
  have ha : (Divisor.toQDivisor G).intersectionNumber ℂ sX C₀.ι C₀.dim_le hGq = 0 := by
    rcases lt_trichotomy ((Divisor.toQDivisor G).intersectionNumber ℂ sX C₀.ι C₀.dim_le hGq) 0
      with hlt | heq | hgt
    · exact absurd hlt (not_lt.mpr hnn)
    · exact heq
    · exfalso
      set a := (Divisor.toQDivisor G).intersectionNumber ℂ sX C₀.ι C₀.dim_le hGq
      set lam : ℚ := -(L₀.intersectionNumber ℂ sX C₀.ι C₀.dim_le hL₀) / a with hlamdef
      have hlam : 0 < lam := div_pos (by linarith) hgt
      have hlamG := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (lam • Divisor.toQDivisor G)
      have hP := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ (L₀ + lam • Divisor.toQDivisor G)
      have hP0 : (L₀ + lam • Divisor.toQDivisor G).intersectionNumber ℂ sX C₀.ι C₀.dim_le hP =
          0 := by
        rw [MMP.Mori.QDivisor.intersectionNumber_add' ℂ sX C₀.ι C₀.dim_le L₀ _ hL₀ hlamG hP,
          MMP.Fourfold.intersectionNumber_smul sX C₀.ι C₀.dim_le _ hGq lam hlamG, hlamdef]
        field_simp
        ring
      have hPtriv := isNumericallyTrivialOver_of_intersectionNumber_eq_zero hP fun C hC =>
        intersectionNumber_eq_zero_of_eq_zero hX hZ hcf hfP hρ hC₀ hC hP hP0
      have hP' := MMP.Fourfold.isQCartier_of_isQFactorial sX' hQ'
        (L₀' + lam • Divisor.toQDivisor (flipTransform f fp G))
      have htriv' := isNumericallyTrivialOver_flipTransform h hK hQ' B₀ hPtriv
      have h0 := intersectionNumber_eq_zero_of_isNumericallyTrivialOver hP' htriv' hC₀'
      have hlamG' := MMP.Fourfold.isQCartier_of_isQFactorial sX' hQ'
        (lam • Divisor.toQDivisor (flipTransform f fp G))
      rw [MMP.Mori.QDivisor.intersectionNumber_add' ℂ sX' C₀'.ι C₀'.dim_le L₀' _ hL₀' hlamG' hP',
        MMP.Fourfold.intersectionNumber_smul sX' C₀'.ι C₀'.dim_le _ hGq' lam hlamG'] at h0
      have := mul_nonneg hlam.le hnn'
      linarith
  -- conclusion: `G ≡_Z 0`, and its strict transform by the transfer across the flip
  have hGtriv := isNumericallyTrivialOver_of_intersectionNumber_eq_zero hGq fun C hC =>
    intersectionNumber_eq_zero_of_eq_zero hX hZ hcf hfP hρ hC₀ hC hGq ha
  rw [QDivisor.toRDivisor_toQDivisor] at hGtriv
  refine ⟨hGtriv, ?_⟩
  obtain ⟨-, h2⟩ := MMP.Flips.IsNumericallyTrivialOver.transformDivisor_of_isOver sZ hX hQ'
    hcf.comp_eq hcfp.comp_eq h.isBirationalMorphism h.isBirationalMorphism_flip hgo hsurj
    hGtriv.1 hGtriv
  rwa [htr, flipTransform_toRDivisor hZ h.isSmall h.isSmall_flip h.isBirationalMorphism] at h2

/-- Lowering the boundary by `c D` lowers the log canonical divisor by `c D`. -/
private theorem logCanonicalDivisor_sub_smul {W : Scheme.{0}} (K : Divisor W) (B D : RDivisor W)
    (c : ℝ) : MMP.Flips.logCanonicalDivisor K (B - c • D) =
      MMP.Flips.logCanonicalDivisor K B + (-c) • D := by
  simp only [MMP.Flips.logCanonicalDivisor, neg_smul]; abel

/-- **Removing a numerically trivial divisor keeps a step.** If `G ≡_Z 0` and its strict
transform `G⁺ ≡_Z 0`, then the same diagram is a step for the boundaries `B - c G` and
`B⁺ - c G⁺`. -/
private theorem isRealFlipStep_sub_smul (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    {G : Divisor X} (c : ℝ)
    (hG : MMP.Flips.IsNumericallyTrivialOver ℂ sX f (Divisor.toRDivisor G))
    (hG' : MMP.Flips.IsNumericallyTrivialOver ℂ sX' fp
      (Divisor.toRDivisor (flipTransform f fp G))) :
    IsRealFlipStep sX sZ sX' K (B - c • Divisor.toRDivisor G) K'
      (B' - c • Divisor.toRDivisor (flipTransform f fp G)) f fp := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  have hnKB : -MMP.Flips.logCanonicalDivisor K (B - c • Divisor.toRDivisor G) =
      -MMP.Flips.logCanonicalDivisor K B + c • Divisor.toRDivisor G := by
    rw [logCanonicalDivisor_sub_smul, neg_add, neg_smul, neg_neg]
  refine
    { isQuasiProjectiveVariety_target := h.isQuasiProjectiveVariety_target
      isNegativeExtremalContraction :=
        { isNormalVariety_source := hX
          isNormalVariety_target := hZ
          isCartierCombination := by
            rw [logCanonicalDivisor_sub_smul]
            exact isCartierCombination_add_smul hE.isCartierCombination hG.1 _
          isContraction := hE.isContraction
          isRelativelyAntiAmple := by
            change MMP.Flips.IsRelativelyAmple f _
            rw [hnKB]
            exact isRelativelyAmple_of_isNumericallyEquivalentOver hX hZ h.isProjectiveMorphism
              hE.isContraction.comp_eq (isNumericallyEquivalentOver_add_smul
                (isCartierCombination_of_isRelativelyAmple hE.isRelativelyAntiAmple) hG c)
              hE.isRelativelyAntiAmple
          relativePicardNumber_eq_one := hE.relativePicardNumber_eq_one }
      isSmall := h.isSmall
      isBirationalMorphism := h.isBirationalMorphism
      isProjectiveMorphism := h.isProjectiveMorphism
      not_isIso := h.not_isIso
      isCanonicalDivisor_flip := h.isCanonicalDivisor_flip
      isSmall_flip := h.isSmall_flip
      isBirationalMorphism_flip := h.isBirationalMorphism_flip
      isProjectiveMorphism_flip := h.isProjectiveMorphism_flip
      not_isIso_flip := h.not_isIso_flip
      relativePicardNumber_flip := h.relativePicardNumber_flip
      isRelativelyAmple_flip := by
        rw [logCanonicalDivisor_sub_smul]
        exact isRelativelyAmple_of_isNumericallyEquivalentOver hX' hZ
          h.isProjectiveMorphism_flip h.isSmall_flip.comp_eq
          (isNumericallyEquivalentOver_add_smul
            (isCartierCombination_of_isRelativelyAmple h.isRelativelyAmple_flip) hG' (-c))
          h.isRelativelyAmple_flip
      eq_flipTransform := by
        rw [map_sub, ← h.eq_flipTransform,
          flipTransform_smul_toRDivisor hZ h.isSmall h.isSmall_flip h.isBirationalMorphism] }

end Step

/-- **Removing an effective part with the same coefficients keeps canonicity.** If `(X, B)` is
real canonical on a `ℚ`-factorial `X` and `D ≥ 0` agrees with `B` on its support, then `(X, B - D)`
is real canonical: each log discrepancy grows by the order of the pulled-back `D`. -/
private theorem isRealCanonicalPair_sub (hB : IsRealCanonicalPair sX B) (hQ : IsQFactorial sX)
    {D : RDivisor X} (hDB : ∀ P, D P ≠ 0 → D P = B P)
    (hDQ : ∃ G : Divisor X, (∀ P, 0 ≤ G P) ∧ ∃ c : ℝ, 0 ≤ c ∧ D = c • Divisor.toRDivisor G) :
    IsRealCanonicalPair sX (B - D) := by
  classical
  obtain ⟨hXn, hcoef, ⟨n₀, K₀, hK₀, m₀, r₀, C₀, hC₀, hRC⟩, hdisc⟩ := hB
  obtain ⟨G, hG0, c, hc, rfl⟩ := hDQ
  obtain ⟨m, hm, hmG⟩ := hQ.2 G
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  -- `c G = (c / m) (m G)`, a nonnegative multiple of an effective Cartier divisor
  have hcG : ∀ P, (c • Divisor.toRDivisor G) P = c / m * (((m : ℤ) • G) P : ℤ) := fun P => by
    rw [Finsupp.smul_apply, ← DivisorWithCoeffs.coeff_apply, Divisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, Int.cast_mul,
      Int.cast_natCast]
    field_simp
  refine ⟨hXn, fun P hP => ?_, ⟨n₀, K₀, hK₀, m₀ + 1, Fin.snoc r₀ (-(c / m)),
    Fin.snoc C₀ ((m : ℤ) • G), fun i => ?_, fun Γ => ?_⟩, fun n E a hE ha => ?_⟩
  · -- the coefficients of `B - c G`
    rw [DivisorWithCoeffs.coeff_sub] at hP ⊢
    by_cases hDP : (c • Divisor.toRDivisor G) P = 0
    · rw [DivisorWithCoeffs.coeff_apply (c • Divisor.toRDivisor G), hDP, sub_zero] at hP ⊢
      exact hcoef P hP
    · exact absurd (by rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
        hDB P hDP, sub_self]) hP
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using hmG
    · simpa using hC₀ i
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have h1 := hRC Γ
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_sub, Pi.sub_apply,
      DivisorWithCoeffs.coeff_apply] at h1 ⊢
    rw [add_sub_assoc', h1, hcG Γ]
    ring
  · -- a log discrepancy for `B - c G` is at least one for `B`
    obtain ⟨hXn', hprop, ω, hω, hKω, m₁, r, C, C', hC, hpres, hpb, rfl⟩ := ha
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    haveI := E.isIntegral
    haveI := E.isDominant
    haveI : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
    obtain ⟨Gp, hGp⟩ := hmG.exists_isPullback
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f ((m : ℤ) • G))
    have hGp0 : 0 ≤ Gp.coeff E.E :=
      MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hmG (V := ⊤)
        (fun P _ => by
          rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul]
          exact mul_nonneg (by positivity) (hG0 P)) hGp E.E
        ⟨E.E.genericPoint, by
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl,
          trivial⟩
    have hLD : MMP.Intersection.IsLogDiscrepancy sX n B E (1 + (E.ordPullback ω : ℝ) -
        ∑ i, (Fin.snoc r (c / m) : Fin (m₁ + 1) → ℝ) i *
          (((Fin.snoc C' Gp : Fin (m₁ + 1) → Divisor E.Y) i).coeff E.E : ℝ)) := by
      refine ⟨hXn', hprop, ω, hω, hKω, m₁ + 1, Fin.snoc r (c / m),
        (Fin.snoc C ((m : ℤ) • G) : Fin (m₁ + 1) → Divisor X),
        (Fin.snoc C' Gp : Fin (m₁ + 1) → Divisor E.Y), fun i => ?_, fun Γ => ?_, fun i => ?_, rfl⟩
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last]; exact hmG
        · rw [Fin.snoc_castSucc]; exact hC i
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have h1 := hpres Γ
        rw [DivisorWithCoeffs.coeff_sub] at h1
        rw [← h1, DivisorWithCoeffs.coeff_apply (c • Divisor.toRDivisor G), hcG Γ,
          DivisorWithCoeffs.coeff_apply ((m : ℤ) • G)]
        ring
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · rw [Fin.snoc_last, Fin.snoc_last]; exact ⟨_, hGp⟩
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hpb i
    have hB' := hdisc n E _ hE hLD
    rw [Fin.sum_univ_castSucc] at hB'
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hB'
    have : 0 ≤ c / m * (Gp.coeff E.E : ℝ) :=
      mul_nonneg (div_nonneg hc (Nat.cast_nonneg _)) (by exact_mod_cast hGp0)
    linarith

/-! ### Removing the components of maximal coefficient -/

/-- The reduced divisor of the components of `D` with coefficient `c`. -/
private noncomputable def levelDivisor {W : Scheme.{0}} (D : RDivisor W) (c : ℝ) : Divisor W :=
  ∑ P ∈ D.support.filter (fun P => D P = c), Finsupp.single P 1

private theorem levelDivisor_apply {W : Scheme.{0}} (D : RDivisor W) {c : ℝ} (hc : c ≠ 0)
    (P : MMP.Mori.PrimeDivisor W) : levelDivisor D c P = if D P = c then 1 else 0 := by
  classical
  rw [levelDivisor, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finsupp.mem_support_iff]
  by_cases hP : D P = c
  · rw [if_pos ⟨hP ▸ hc, hP⟩, if_pos hP]
  · rw [if_neg (fun h => hP h.2), if_neg hP]

/-- `c G_c(D)` has coefficient `c` along the components of `D` of coefficient `c`. -/
private theorem coeff_smul_levelDivisor {W : Scheme.{0}} (D : RDivisor W) {c : ℝ} (hc : c ≠ 0)
    (P : MMP.Mori.PrimeDivisor W) :
    (c • Divisor.toRDivisor (levelDivisor D c)).coeff P = if D.coeff P = c then c else 0 := by
  rw [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
    levelDivisor_apply _ hc, DivisorWithCoeffs.coeff_apply]
  split_ifs <;> simp

/-- The level divisor is effective. -/
private theorem levelDivisor_nonneg {W : Scheme.{0}} (D : RDivisor W) {c : ℝ} (hc : c ≠ 0)
    (P : MMP.Mori.PrimeDivisor W) : 0 ≤ levelDivisor D c P := by
  rw [levelDivisor_apply _ hc]
  split_ifs <;> simp

/-- The largest coefficient of a nonzero divisor with positive coefficients is attained and
positive. -/
private theorem exists_coeff_eq_realThresholdMax {W : Scheme.{0}} (D : RDivisor W) (hD : D ≠ 0)
    (hpos : ∀ P, D.coeff P ≠ 0 → 0 < D.coeff P) :
    ∃ P ∈ D.support, D.coeff P = realThresholdMax D ∧ 0 < realThresholdMax D := by
  classical
  have hne : D.support.Nonempty := Finsupp.support_nonempty_iff.mpr hD
  have hSne : (D.support.image D.coeff).Nonempty := hne.image _
  have hm := Finset.max'_mem _ hSne
  obtain ⟨P, hP, hPm⟩ := Finset.mem_image.mp hm
  have hPpos : 0 < D.coeff P := hpos P (Finsupp.mem_support_iff.mp hP)
  have hmax : realThresholdMax D = (D.support.image D.coeff).max' hSne := by
    unfold realThresholdMax
    refine le_antisymm (Finset.max'_le _ _ _ fun y hy => ?_)
      (Finset.le_max' _ _ (Finset.mem_insert_of_mem hm))
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [← hPm]; exact hPpos.le
    · exact Finset.le_max' _ _ hy
  exact ⟨P, hP, hPm.trans hmax.symm, hmax ▸ hPm ▸ hPpos⟩

section Sequence

variable (σ : RealFlipSequence sX K B)

/-- The components of `B_i` and of `B_{i+1}` correspond, with the same coefficients. -/
private theorem exists_bijOn_support_succ (hn : σ.n = ⊤) (i : ℕ) :
    ∃ e : MMP.Mori.PrimeDivisor (modelSeq X σ.Y i) → MMP.Mori.PrimeDivisor (σ.Y i),
      Set.BijOn e (divisorSeq B σ.BY i).support (σ.BY i).support ∧
        ∀ P, (σ.BY i).coeff (e P) = (divisorSeq B σ.BY i).coeff P := by
  have hs := σ.isRealFlipStep i (by simp [hn])
  have hZ := hs.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (σ.Z i) := hZ.1.toIsIntegral
  rw [hs.eq_flipTransform]
  exact exists_bijOn_support_flipTransform hZ hs.isSmall hs.isSmall_flip hs.isBirationalMorphism _

/-- The coefficient of `B_{i+1}` at a prime divisor is that of `B_i` at the corresponding prime
divisor, for any divisor transported along the step. -/
private theorem exists_flipTransform_apply_eq (hn : σ.n = ⊤) (i : ℕ)
    (P' : MMP.Mori.PrimeDivisor (σ.Y i)) :
    ∃ P : MMP.Mori.PrimeDivisor (modelSeq X σ.Y i), ∀ {R : Type} [AddCommMonoid R]
      (D : DivisorWithCoeffs R (modelSeq X σ.Y i)), flipTransform (σ.f i) (σ.fp i) D P' = D P := by
  have hs := σ.isRealFlipStep i (by simp [hn])
  have hZ := hs.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsIntegral (σ.Z i) := hZ.1.toIsIntegral
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hs.isSmall_flip hs.isSmall P'
  exact ⟨P, fun D => flipTransform_apply_of_isSmall hZ hs.isSmall hs.isSmall_flip
    hs.isBirationalMorphism hP.symm D⟩

private theorem realThresholdMax_divisorSeq (hn : σ.n = ⊤) (i : ℕ) :
    realThresholdMax (divisorSeq B σ.BY i) = realThresholdMax B := by
  induction i with
  | zero => rfl
  | succ i ih =>
    obtain ⟨e, he, hc⟩ := exists_bijOn_support_succ σ hn i
    exact (realThresholdMax_eq_of_bijOn e he hc).trans ih

private theorem levelDivisor_succ (hn : σ.n = ⊤) {c : ℝ} (hc : c ≠ 0) (i : ℕ) :
    levelDivisor (σ.BY i) c =
      flipTransform (σ.f i) (σ.fp i) (levelDivisor (divisorSeq B σ.BY i) c) := by
  ext P'
  obtain ⟨P, hP⟩ := exists_flipTransform_apply_eq σ hn i P'
  simp only [DivisorWithCoeffs.coeff_apply]
  rw [hP, levelDivisor_apply _ hc, levelDivisor_apply _ hc,
    (σ.isRealFlipStep i (by simp [hn])).eq_flipTransform, hP]

private theorem card_support_divisorSeq (hn : σ.n = ⊤) (i : ℕ) :
    (divisorSeq B σ.BY i).support.card = B.support.card := by
  induction i with
  | zero => rfl
  | succ i ih =>
    obtain ⟨e, he, -⟩ := exists_bijOn_support_succ σ hn i
    rw [← ih]
    exact (Finset.card_nbij e (fun P hP => he.mapsTo hP) he.injOn he.surjOn).symm

private theorem isCanonicalDivisor_divisorSeq (hn : σ.n = ⊤) :
    ∀ i : ℕ, ∃ m, Divisor.IsCanonicalDivisor (modelStr sX σ.sY i) m (divisorSeq K σ.KY i)
  | 0 => σ.isCanonicalDivisor
  | j + 1 => (σ.isRealFlipStep j (by simp [hn])).isCanonicalDivisor_flip

/-- **Eventually no flipped curve lies in a component of maximal coefficient**, since the
canonical difficulty is eventually constant. -/
private theorem exists_forall_not_subset_levelDivisor_succ (hn : σ.n = ⊤)
    (hσ : ∀ i : ℕ, IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i))
    (hb : realThresholdMax B ≠ 0) :
    ∃ N₀ : ℕ, ∀ i ≥ N₀, ∀ C, MMP.Flips.IsFlippingCurve ℂ (σ.sY i) (σ.sZ i) (σ.fp i) C →
      ¬ C ⊆ ((levelDivisor (σ.BY i) (realThresholdMax B)).supp : Set (σ.Y i)) := by
  classical
  have hlt : ∀ i : ℕ, (i : ℕ∞) < σ.n := fun i => by simp [hn]
  obtain ⟨-, hanti, hdrop, -⟩ := σ.realCanonicalDifficulty_ne_top_and_antitone fun i _ => hσ i
  set d : ℕ → ℕ∞ := fun i =>
    realCanonicalDifficulty (modelStr sX σ.sY i) (divisorSeq B σ.BY i)
  have hd' : Antitone d := antitone_nat_of_succ_le fun i => hanti i (hlt i)
  -- the difficulty attains its minimum, after which it is constant
  obtain ⟨_, ⟨N₀, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt (Set.range d) ⟨_, 0, rfl⟩
  have hconst : ∀ i ≥ N₀, d (i + 1) = d i := fun i hi =>
    le_antisymm (hd' (Nat.le_succ i))
      ((hd' hi).trans (not_lt.mp (hmin _ ⟨i + 1, rfl⟩)))
  refine ⟨N₀, fun i hi C hC hCsub => ?_⟩
  obtain ⟨-, -, -, -, z, -, hmax, -⟩ := id hC
  obtain ⟨P, hP, hCP⟩ := exists_subset_support_of_subset_supp hmax.1.1 hCsub
  rw [levelDivisor_apply _ hb] at hP
  have hPb : σ.BY i P = realThresholdMax B := by
    by_contra h
    exact hP (if_neg h)
  have hmax' : realThresholdMax (σ.BY i) = realThresholdMax B :=
    realThresholdMax_divisorSeq σ hn (i + 1)
  have hPs : P ∈ (σ.BY i).support := Finsupp.mem_support_iff.mpr (hPb ▸ hb)
  have := hdrop i (hlt i) C P hC hPs (by rw [DivisorWithCoeffs.coeff_apply, hPb, hmax']) hCP
  exact absurd (hconst i hi) this.ne

/-- **Eventually no flipping curve lies in a component of maximal coefficient** (FA 4.13.3): the
morphisms of normalizations of the components along the flips contract curves only finitely
often. -/
private theorem exists_forall_not_subset_levelDivisor (hn : σ.n = ⊤) {c : ℝ} (hc : c ≠ 0) (N₀ : ℕ)
    (h₀ : ∀ i ≥ N₀, ∀ C, MMP.Flips.IsFlippingCurve ℂ (σ.sY i) (σ.sZ i) (σ.fp i) C →
      ¬ C ⊆ ((levelDivisor (σ.BY i) c).supp : Set (σ.Y i))) :
    ∃ N₁ ≥ N₀, ∀ i ≥ N₁, ∀ C, MMP.Flips.IsFlippingCurve ℂ (modelStr sX σ.sY i) (σ.sZ i) (σ.f i) C →
      ¬ C ⊆ ((levelDivisor (divisorSeq B σ.BY i) c).supp : Set (modelSeq X σ.Y i)) := by
  classical
  have hlt : ∀ i : ℕ, (i : ℕ∞) < σ.n := fun i => by simp [hn]
  have hex : ∀ i, ∃ g : (modelSeq X σ.Y i).RationalMap (σ.Y i),
      MMP.Flips.IsFlip ℂ (modelStr sX σ.sY i) (σ.sZ i) (σ.sY i)
        (MMP.Flips.logCanonicalDivisor (divisorSeq K σ.KY i) (divisorSeq B σ.BY i)) (σ.f i)
        (σ.fp i) g ∧
      MMP.Flips.RationalMap.IsOver (σ.f i) (σ.fp i) g ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (modelSeq X σ.Y i)),
        MMP.Mori.RationalMap.transformDivisor g D = flipTransform (σ.f i) (σ.fp i) D) ∧
      ∀ P' : MMP.Mori.PrimeDivisor (σ.Y i), ∃ P : MMP.Mori.PrimeDivisor (modelSeq X σ.Y i),
        MMP.Mori.RationalMap.transformPrimeDivisor g P = some P' := fun i =>
    exists_isFlip_of_isRealFlipStep (σ.isRealFlipStep i (hlt i))
      (isCanonicalDivisor_divisorSeq σ hn i) (σ.isQFactorial (i + 1) (hlt _).le)
  choose g hg using hex
  exact exists_forall_not_subset_supp_of_isFlippingCurve_family (M := modelSeq X σ.Y)
    (s := modelStr sX σ.sY) (sZf := σ.sZ) (φ := σ.f) (φp := σ.fp) (g := g)
    (fun i => (hg i).1) (fun i => σ.dim_eq i (hlt i).le)
    (fun i => levelDivisor (divisorSeq B σ.BY i) c)
    (levelDivisor_nonneg _ hc)
    (fun i => (levelDivisor_succ σ hn hc i).trans ((hg i).2.2.1 _).symm) N₀ h₀

end Sequence

/-- **The tail with fewer components.** In an infinite extremal real flip sequence of real
canonical pairs with projective models and targets and nonzero boundary, there is a tail on which
removing the components of maximal coefficient from every boundary leaves an extremal real
canonical flip sequence. -/
private theorem exists_tail (σ : RealFlipSequence sX K B) (hn : σ.n = ⊤)
    (hσ : ∀ i : ℕ, IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i))
    (hX : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (modelStr sX σ.sY i)) (hB : B ≠ 0) :
    ∃ (N : ℕ) (B' : ∀ i, RDivisor (modelSeq X σ.Y i)),
      (∀ i ≥ N, IsRealFlipStep (modelStr sX σ.sY i) (σ.sZ i) (σ.sY i)
        (divisorSeq K σ.KY i) (B' i) (σ.KY i) (B' (i + 1)) (σ.f i) (σ.fp i)) ∧
      (∀ i ≥ N, IsRealCanonicalPair (modelStr sX σ.sY i) (B' i)) ∧
      (B' N).support.card < B.support.card := by
  classical
  have hlt : ∀ i : ℕ, (i : ℕ∞) < σ.n := fun i => by simp [hn]
  set b := realThresholdMax B
  -- the largest coefficient is positive and attained
  obtain ⟨-, -, -, hbpos⟩ :=
    exists_coeff_eq_realThresholdMax B hB fun P h => ((hσ 0).2.1 P h).1
  have hb0 : b ≠ 0 := hbpos.ne'
  set G : ∀ i, Divisor (modelSeq X σ.Y i) := fun i => levelDivisor (divisorSeq B σ.BY i) b
  have hGsucc : ∀ i, G (i + 1) = flipTransform (σ.f i) (σ.fp i) (G i) := fun i =>
    levelDivisor_succ σ hn hb0 i
  obtain ⟨N₀, hN₀⟩ := exists_forall_not_subset_levelDivisor_succ σ hn hσ hb0
  obtain ⟨N₁, hN₁₀, hN₁⟩ := exists_forall_not_subset_levelDivisor σ hn hb0 N₀ hN₀
  have hnum : ∀ i ≥ N₁,
      MMP.Flips.IsNumericallyTrivialOver ℂ (modelStr sX σ.sY i) (σ.f i)
        (Divisor.toRDivisor (G i)) ∧
      MMP.Flips.IsNumericallyTrivialOver ℂ (σ.sY i) (σ.fp i)
        (Divisor.toRDivisor (flipTransform (σ.f i) (σ.fp i) (G i))) := by
    intro i hi
    refine isNumericallyTrivialOver_of_forall_not_subset (σ.isRealFlipStep i (hlt i))
      (isCanonicalDivisor_divisorSeq σ hn i) (σ.isQFactorial i (hlt i).le)
      (σ.isQFactorial (i + 1) (hlt _).le) (hX i) (hX (i + 1))
      (σ.isQuasiProjectiveVariety i (hlt i).le) (σ.isQuasiProjectiveVariety (i + 1) (hlt _).le)
      (σ.dim_eq i (hlt i).le)
      (σ.dim_eq (i + 1) (hlt _).le) (hσ i) (levelDivisor_nonneg _ hb0) (hN₁ i hi) ?_
    rw [← hGsucc]
    exact hN₀ i (by omega)
  refine ⟨N₁, fun i => divisorSeq B σ.BY i - b • Divisor.toRDivisor (G i), fun i hi => ?_,
    fun i hi => ?_, ?_⟩
  · have := isRealFlipStep_sub_smul (σ.isRealFlipStep i (hlt i)) b (hnum i hi).1 (hnum i hi).2
    rw [← hGsucc] at this
    exact this
  · refine isRealCanonicalPair_sub (hσ i) (σ.isQFactorial i (hlt i).le)
      (fun P hP => ?_) ⟨G i, levelDivisor_nonneg _ hb0, b, hbpos.le, rfl⟩
    rw [← DivisorWithCoeffs.coeff_apply, coeff_smul_levelDivisor _ hb0] at hP ⊢
    split_ifs at hP ⊢ with h
    · rw [DivisorWithCoeffs.coeff_apply] at h; exact h.symm
    · exact absurd rfl hP
  · -- the components of coefficient `b` are removed from `B_{N₁}`
    have hBN : divisorSeq B σ.BY N₁ ≠ 0 := by
      intro h0
      have := card_support_divisorSeq σ hn N₁
      rw [h0, Finsupp.support_zero, Finset.card_empty] at this
      exact hB (Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp this.symm))
    obtain ⟨P₁, hP₁, hP₁b, -⟩ :=
      exists_coeff_eq_realThresholdMax _ hBN fun P h => ((hσ N₁).2.1 P h).1
    rw [realThresholdMax_divisorSeq σ hn] at hP₁b
    rw [← card_support_divisorSeq σ hn N₁]
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun P hP => ?_).mpr ⟨P₁, hP₁, ?_⟩)
    · rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_sub,
        coeff_smul_levelDivisor _ hb0] at hP
      rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply]
      split_ifs at hP with h
      · rwa [h]
      · simpa using hP
    · rw [Finsupp.mem_support_iff, not_not, ← DivisorWithCoeffs.coeff_apply,
        DivisorWithCoeffs.coeff_sub, coeff_smul_levelDivisor _ hb0, if_pos hP₁b, hP₁b, sub_self]

/-! ### The induction -/

private theorem n_ne_top_of_card_le : ∀ (m : ℕ) {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : RDivisor X} (σ : RealFlipSequence sX K B), B.support.card ≤ m →
    (∀ i : ℕ, (i : ℕ∞) ≤ σ.n →
      IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i)) →
    (∀ i : ℕ, (i : ℕ∞) ≤ σ.n → MMP.Mori.IsProjectiveVariety ℂ (modelStr sX σ.sY i)) →
    σ.n ≠ ⊤
  | m, X, _, _, _, _, sX, K, B, σ, hm, hσ, hX => by
    intro hn
    by_cases hB : B = 0
    · exact n_ne_top_of_eq_zero σ hσ hB hn
    have hσ' : ∀ i : ℕ, IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i) :=
      fun i => hσ i (by simp [hn])
    have hX' : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (modelStr sX σ.sY i) :=
      fun i => hX i (by simp [hn])
    obtain ⟨N, B', hstep, hcan, hcard⟩ := exists_tail σ hn hσ' hX' hB
    match m with
    | 0 => omega
    | m + 1 =>
      exact n_ne_top_of_card_le m (tail σ N B' hstep hn) (by omega)
        (fun j _ => tail_isRealCanonicalPair σ N B' hstep hn hcan j)
        (fun j _ => tail_isProjectiveVariety σ N B' hstep hn hX' j) rfl

end Helpers

/-- An extremal real flip sequence `σ` of real canonical complex threefold pairs `(X_i, B_i)`
(coefficients less than one), all of whose models `X_i` and contraction targets `Z_i` are
projective varieties, has finitely many steps. -/
@[mmp "thm_fourfold_projective_real_canonical_threefold_termination"]
public theorem RealFlipSequence.n_ne_top_of_isRealCanonicalPair
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : RDivisor X} (σ : RealFlipSequence sX K B)
    (hσ : ∀ i : ℕ, (i : ℕ∞) ≤ σ.n →
      IsRealCanonicalPair (modelStr sX σ.sY i) (divisorSeq B σ.BY i))
    (hX : ∀ i : ℕ, (i : ℕ∞) ≤ σ.n → MMP.Mori.IsProjectiveVariety ℂ (modelStr sX σ.sY i))
    (_hZ : ∀ i : ℕ, (i : ℕ∞) < σ.n → MMP.Mori.IsProjectiveVariety ℂ (σ.sZ i)) :
    σ.n ≠ ⊤ :=
  n_ne_top_of_card_le _ σ le_rfl hσ hX

end MMP.Fourfold
