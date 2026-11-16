module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
public import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc

/-!
# Bad branch counts, weighted bad sets of flips, generic blowup valuations and varying labels

Let `Y⁻ → Z ← Y⁺` (by `f^±`) be a threefold step diagram in which both morphisms are small, with
bad loci `W^± ⊆ Y^±`. A prime divisor `S⁻` of `Y⁻` has a strict transform `S⁺` on `Y⁺`; with
`ν^± : (S^±)^ν ⟶ S^± ⊆ Y^±` the normalizations, the *bad branch count* `e^±(S⁻)` is the number
of prime divisors `P` of the normal surface `(S^±)^ν` with `ν^±(P) ⊆ W^±`.

For a small terminal flip move `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a prepared chain, written as a threefold
step diagram `Y⁻ → Z ← Y⁺` with bad loci `W^±`, the *weighted bad set* `𝒜₀` is the set of
normalized divisorial valuations `v` exceptional over both `Y⁻` and `Y⁺` with `c_{Y⁻}(v) ⊆ W⁻`
and `w_v(Y⁻, Θ⁻) + w_v(Y⁺, Θ⁺) > 0`.

For a normal complex threefold `X` and an irreducible closed curve `V ⊆ X` such that `X` is smooth
at the generic point `η_V`, the local ring `𝒪_{X,η_V}` is regular of dimension two with maximal
ideal `𝔪_V`, and the *generic blowup valuation* `v_V` is the valuation of `ℂ(X)` with
`v_V(g) = max {n : g ∈ 𝔪_V^n}` for `0 ≠ g ∈ 𝒪_{X,η_V}`; it is the `𝔪_V`-adic order, the monomial
valuation `v_{x,t;1}` for any regular parameters `(x, t)` at `η_V`.

On a model `(Y, Θ)` of a terminal chain, the *varying branch number* at an irreducible closed
curve `C` is `r_C^var = ∑_{h varying} r_{C,h}`, the sum of the branch numbers of the varying
labels. At a junction `p : (Y, Θ) ⟶ (X_i, B_i)` the *varying union* is the union of the varying
labels on `Y`, with its reduced structure; on a prepared chain, `p` maps it onto a finite set of
closed points.

## Main definitions

* `MMP.Fourfold.flipTransformPrimeDivisor`: the strict transform `(f⁺)⁻¹_* f⁻_* S` of a prime
  divisor.
* `MMP.Fourfold.badBranchCount`: the number of prime divisors of the normalization of a prime
  divisor whose image lies in a given subset.
* `MMP.Fourfold.IsBadBranchCountMinus`, `MMP.Fourfold.IsBadBranchCountPlus`: `e = e^-(S⁻)` and
  `e = e^+(S⁻)` for a threefold step diagram with both maps small.
* `MMP.Fourfold.StabilizedTail.TerminalChain.flipTarget`,
  `MMP.Fourfold.StabilizedTail.TerminalChain.flipTargetMap`: the model reached by a flip of a
  bridge, and its morphism to the base of the flip.
* `MMP.Fourfold.StabilizedTail.PreparedChain.FlipMove`: the small terminal flip moves of a
  prepared chain.
* `MMP.Fourfold.StabilizedTail.PreparedChain.flipBadSet`: the weighted bad set `𝒜₀` of a flip
  move.
* `MMP.Fourfold.IsGenericBlowupValuation`: `v = v_V`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingBranchNumber`: `r = r_C^var`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.varyingUnion`: the varying union at a junction.

## Main results

* `MMP.Fourfold.flipTransform_single_of_eq_some`: the strict transform of the divisor `r S` is
  `r S⁺`.
* `MMP.Fourfold.IsGenericBlowupValuation.eq`: the generic blowup valuation is unique.
* `MMP.Fourfold.isGenericBlowupValuation_iff_isWeightedMonomialValuation`: for regular
  parameters `(x, t)` at `η_V`, the generic blowup valuation is the monomial valuation
  `v_{x,t;1}`.
* `MMP.Fourfold.StabilizedTail.PreparedChain.finite_image_varyingUnion`,
  `MMP.Fourfold.StabilizedTail.PreparedChain.isClosed_of_mem_image_varyingUnion`: on a prepared
  chain, `p_i` maps the varying union onto a finite set of closed points.

## Implementation notes

* The strict transform `S⁺ = (f⁺)⁻¹_* f⁻_* S⁻` of a prime divisor is the transform of `S⁻` under
  the rational map `f⁻` followed by the inverse transform under `f⁺`, as for divisors
  (`MMP.Mori.flipTransform`). It is `none` when one of the two transforms is not a prime divisor;
  for a threefold step diagram with both maps small the source asserts that it exists, and the
  bad branch count `e^+` is stated for a strict transform `S⁺` which exists. The normalization of
  a prime divisor is `MMP.Fourfold.primeDivisorNormalization`, as for branch numbers, and the
  count is `Set.ncard` (`0` on an infinite set). The image `ν(P)` of a prime divisor `P` of the
  normalization is the image of its support.
* The moves of a prepared chain are those of its terminal chain from the junction `Y_{i₀}` on. A
  flip move is the `k`-th flip `V_k → T_k ← V_{k+1}` of the `i`-th bridge, `i ≥ i₀`, `k < m_i`;
  its source is the model `(i, some k)` and its target the model `(i, some (k + 1))` when
  `k + 1 < m_i` and the junction `(i + 1, none)` when `k + 1 = m_i`, through the identification
  `e : V_{m_i} ≅ Y_{i+1}` of the bridge. The step diagram `Y⁻ → Z ← Y⁺` of the move is
  `g_k : V_k ⟶ T_k` with `g_k⁺ : V_{k+1} ⟶ T_k`, composed with `e⁻¹` in the second case; the bad
  loci `W^±` are those of this pair of morphisms. Both maps are small
  (`MMP.Fourfold.StabilizedTail.TerminalBridge.isSmallMorphism_and_isSmallMorphism`).
* In the weighted bad set, the valuations are valuations of `k(Y⁻)`; a valuation `v⁺` of `k(Y⁺)`
  corresponds to `v` when their restrictions to `k(Z)` agree (both `Y^± ⟶ Z` are dominant,
  `MMP.Fourfold.StabilizedTail.TerminalChain.isDominant_flipTargetMap`). The weights are those of
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` at the admissible scale of the
  prepared chain, on the source and target models with their boundaries `Θ^±`; that predicate
  already contains that the valuation is a normalized divisorial valuation exceptional over the
  model. The centre condition `c_{Y⁻}(v) ⊆ W⁻` is `MMP.Intersection.IsCentre` for an irreducible
  closed subset contained in `W⁻`.
* "`X` is smooth at `η_V`" is the regularity of `𝒪_{X,η_V}`, as for the regular locus
  `AlgebraicGeometry.regularLocus` used for the one-label smooth locus; over `ℂ` the two agree.
  A normal threefold is a normal variety of dimension `3` and an irreducible curve is an
  irreducible closed subset of dimension `1`. That `𝒪_{X,η_V}` has dimension two is a
  consequence in the source, not a condition. The valuation `v_V` is a predicate on a valuation,
  with values `v(g) = M` read as `v g = exp (-M)`; it is determined by its values on
  `𝒪_{X,η_V}`, whose fraction field is `ℂ(X)` (`MMP.Fourfold.IsGenericBlowupValuation.eq`).
* Branch numbers on a model of a terminal chain are a predicate on their value
  (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBranchNumber`), so the varying branch number
  is too. The sum over the varying labels is the finitely supported sum `∑ᶠ`, a finite sum since
  there are finitely many labels (`MMP.Fourfold.StabilizedTail.TerminalChain.finite_label`).
* The varying union is defined at every junction of a terminal chain, as a subset (a closed subset
  carries its reduced structure): the union of the supports of the centres on `Y_i` of the
  varying labels, as in `MMP.Fourfold.StabilizedTail.PreparedChain`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Strict transforms of prime divisors and bad branch counts -/

section BadBranchCount

variable {Xm Xp Z : Scheme.{u}}

/-- The strict transform `(f⁺)⁻¹_* f⁻_* S` on `X⁺` of a prime divisor `S` of `X⁻`, for morphisms
`f⁻ : X⁻ ⟶ Z` and `f⁺ : X⁺ ⟶ Z`: the transform of `S` under the rational map `f⁻`, followed by
the inverse transform under `f⁺`; `none` if one of them is not a prime divisor. -/
def flipTransformPrimeDivisor (fm : Xm ⟶ Z) (fp : Xp ⟶ Z) (S : MMP.Mori.PrimeDivisor Xm) :
    Option (MMP.Mori.PrimeDivisor Xp) :=
  (RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap S).bind
    (inverseTransformPrimeDivisor fp)

/-- The strict transform of the divisor `r S` is `r S⁺`. -/
theorem flipTransform_single_of_eq_some {R : Type*} [AddCommMonoid R] {fm : Xm ⟶ Z}
    {fp : Xp ⟶ Z} {S : MMP.Mori.PrimeDivisor Xm} {S' : MMP.Mori.PrimeDivisor Xp}
    (h : flipTransformPrimeDivisor fm fp S = some S') (r : R) :
    flipTransform fm fp (Finsupp.single S r) = Finsupp.single S' r := by
  unfold flipTransformPrimeDivisor at h
  obtain ⟨E, hE, hE'⟩ := Option.bind_eq_some_iff.mp h
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [RationalMap.transformDivisor_single_of_eq_some hE,
    inverseTransformDivisor_single_of_eq_some hE']

variable {Y : Scheme.{u}}

/-- The number of prime divisors `P` of the normalization `S^ν` of a prime divisor `S` of `Y` with
`ν(P) ⊆ W`, for `ν : S^ν ⟶ S ⊆ Y` (`0` if there were infinitely many). For `W` a bad locus this
is the bad branch count. -/
@[mmp "def_mmp_indexd_bad_branch_count"]
def badBranchCount (S : MMP.Mori.PrimeDivisor Y) (W : Set Y) : ℕ :=
  {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
    primeDivisorNormalization S '' P.support ⊆ W}.ncard

/-- The bad branch count is monotone in the subset. -/
theorem badBranchCount_mono (S : MMP.Mori.PrimeDivisor Y) {W W' : Set Y} (hW : W ⊆ W')
    (hfin : {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support ⊆ W'}.Finite) :
    badBranchCount S W ≤ badBranchCount S W' :=
  Set.ncard_le_ncard (fun _ hP => Set.Subset.trans hP hW) hfin

end BadBranchCount

section StepDiagramBadBranchCount

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]

/-- `e` is the *bad branch count* `e^-(S⁻)` of a prime divisor `S⁻` of `Y⁻`, for a threefold step
diagram `Y⁻ → Z ← Y⁺` (by `f^±`, canonical divisor `K` and boundary `B` of `Y⁻`) in which both
morphisms are small, with bad loci `W^±`: the number of prime divisors `P` of the normalization
`(S⁻)^ν` with `ν⁻(P) ⊆ W⁻`. -/
@[mmp "def_mmp_indexd_bad_branch_count"]
def IsBadBranchCountMinus (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)
    (S : MMP.Mori.PrimeDivisor Xm) (e : ℕ) : Prop :=
  IsThreefoldStepDiagram sXm sZ sXp K B fm fp ∧ IsSmallMorphism sXm sZ fm ∧
    e = badBranchCount S (badLocusMinus fm fp)

/-- `e` is the *bad branch count* `e^+(S⁻)` of a prime divisor `S⁻` of `Y⁻`, for a threefold step
diagram `Y⁻ → Z ← Y⁺` (by `f^±`, canonical divisor `K` and boundary `B` of `Y⁻`) in which both
morphisms are small, with bad loci `W^±`: the strict transform `S⁺ = (f⁺)⁻¹_* f⁻_* S⁻` is a prime
divisor of `Y⁺`, and `e` is the number of prime divisors `P` of its normalization `(S⁺)^ν` with
`ν⁺(P) ⊆ W⁺`. -/
@[mmp "def_mmp_indexd_bad_branch_count"]
def IsBadBranchCountPlus (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)
    (S : MMP.Mori.PrimeDivisor Xm) (e : ℕ) : Prop :=
  IsThreefoldStepDiagram sXm sZ sXp K B fm fp ∧ IsSmallMorphism sXm sZ fm ∧
    ∃ S' : MMP.Mori.PrimeDivisor Xp, flipTransformPrimeDivisor fm fp S = some S' ∧
      e = badBranchCount S' (badLocusPlus fm fp)

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {S : MMP.Mori.PrimeDivisor Xm}

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The bad branch count `e^-(S⁻)` is unique. -/
theorem IsBadBranchCountMinus.eq {e e' : ℕ} (h : IsBadBranchCountMinus sXm sZ sXp K B fm fp S e)
    (h' : IsBadBranchCountMinus sXm sZ sXp K B fm fp S e') : e = e' :=
  h.2.2.trans h'.2.2.symm

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The bad branch count `e^+(S⁻)` is unique. -/
theorem IsBadBranchCountPlus.eq {e e' : ℕ} (h : IsBadBranchCountPlus sXm sZ sXp K B fm fp S e)
    (h' : IsBadBranchCountPlus sXm sZ sXp K B fm fp S e') : e = e' := by
  obtain ⟨-, -, S₁, h₁, rfl⟩ := h
  obtain ⟨-, -, S₂, h₂, rfl⟩ := h'
  cases h₁.symm.trans h₂
  rfl

end StepDiagramBadBranchCount

/-! ### Generic blowup valuations -/

section GenericBlowup

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]

/-- **The generic blowup valuation of a curve.** Let `X` be a normal complex threefold and
`V ⊆ X` an irreducible closed curve such that `X` is smooth at its generic point `η_V`, that is,
`𝒪_{X,η_V}` is regular (of dimension two), with maximal ideal `𝔪_V`. A valuation `v` of `ℂ(X)`
is the *generic blowup valuation* `v_V` if `v(g) = max {n : g ∈ 𝔪_V^n}` for every nonzero
`g ∈ 𝒪_{X,η_V}`. It is the `𝔪_V`-adic order, the monomial valuation `v_{x,t;1}` for any regular
parameters `(x, t)` at `η_V`
(`MMP.Fourfold.isGenericBlowupValuation_iff_isWeightedMonomialValuation`). -/
@[mmp "def_mmp_indexd_generic_blowup"]
def IsGenericBlowupValuation (V : IrreducibleCloseds X)
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) : Prop :=
  IsNormalVariety ℂ sX ∧ topologicalKrullDim X = 3 ∧ topologicalKrullDim (V : Set X) = 1 ∧
    IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) ∧
    ∀ g : X.presheaf.stalk V.isIrreducible.genericPoint, g ≠ 0 →
      ∃ M : ℕ, IsGreatest {n : ℕ | g ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk V.isIrreducible.genericPoint) ^ n} M ∧
        v (algebraMap _ X.functionField g) = WithZero.exp (-(M : ℤ))

variable {sX}

/-- The generic blowup valuation is unique: a valuation of `ℂ(X)` is determined by its values on
`𝒪_{X,η_V}`, whose fraction field is `ℂ(X)`. -/
theorem IsGenericBlowupValuation.eq {V : IrreducibleCloseds X}
    {v v' : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h : IsGenericBlowupValuation sX V v) (h' : IsGenericBlowupValuation sX V v') : v = v' := by
  have hR : ∀ g : X.presheaf.stalk V.isIrreducible.genericPoint,
      v (algebraMap _ X.functionField g) = v' (algebraMap _ X.functionField g) := by
    intro g
    by_cases hg : g = 0
    · simp [hg]
    obtain ⟨M, hM, hv⟩ := h.2.2.2.2 g hg
    obtain ⟨M', hM', hv'⟩ := h'.2.2.2.2 g hg
    rw [hv, hv', hM.unique hM']
  ext z
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective
    (A := X.presheaf.stalk V.isIrreducible.genericPoint) z
  rw [map_div₀, map_div₀, hR, hR]

omit [IsIntegral X] in
/-- For a regular system of parameters `(x, t)` of `𝒪_{X,η_V}`, the monomial valuation
`v_{x,t;1}(g)` of weight one is the `𝔪_V`-adic order of `g`. -/
theorem monomialValuation_one_eq_iSup {V : IrreducibleCloseds X}
    {x t : X.presheaf.stalk V.isIrreducible.genericPoint}
    (hxt : IsRegularSystemOfParameters ![x, t])
    (g : X.presheaf.stalk V.isIrreducible.genericPoint) :
    MMP.Resolution.monomialValuation t x 1 g = ⨆ (n : ℕ) (_ : g ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk V.isIrreducible.genericPoint) ^ n), (n : ℕ∞) := by
  have hm : Ideal.span {t, x} =
      IsLocalRing.maximalIdeal (X.presheaf.stalk V.isIrreducible.genericPoint) := by
    rw [← hxt.1, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.union_comm]
    rfl
  simp only [MMP.Resolution.monomialValuation, monomialIdeal_one_eq_pow, hm]

/-- For a nonempty set `s` of natural numbers, `M` is the greatest element of `s` exactly when
`⨆ n ∈ s, n = M` in `ℕ∞`. -/
theorem isGreatest_iff_iSup_eq {s : Set ℕ} (hne : s.Nonempty) {M : ℕ} :
    IsGreatest s M ↔ ⨆ (n : ℕ) (_ : n ∈ s), (n : ℕ∞) = M := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← ENat.natCast_sSup ⟨M, h.2⟩, h.csSup_eq]
  · have hbdd : BddAbove s := ⟨M, fun n hn => by
      exact_mod_cast h ▸ le_iSup₂ (f := fun (n : ℕ) (_ : n ∈ s) => (n : ℕ∞)) n hn⟩
    rw [← ENat.natCast_sSup hbdd] at h
    have hM : sSup s = M := by exact_mod_cast h
    exact hM ▸ ⟨Nat.sSup_mem hne hbdd, fun n hn => le_csSup hbdd hn⟩

/-- **The generic blowup valuation is `v_{x,t;1}`.** For an irreducible closed curve `V` of
codimension two of a normal complex threefold `X` and a regular system of parameters `(x, t)` of
`𝒪_{X,η_V}`, a valuation of `ℂ(X)` is the generic blowup valuation `v_V` exactly when it is the
monomial valuation `v_{x,t;1}` of weights `(1, 1)`. -/
theorem isGenericBlowupValuation_iff_isWeightedMonomialValuation {V : IrreducibleCloseds X}
    (h3 : topologicalKrullDim X = 3) (hV : topologicalKrullDim (V : Set X) = 1)
    (hcodim : codimension V = 2) {x t : X.presheaf.stalk V.isIrreducible.genericPoint}
    (hxt : IsRegularSystemOfParameters ![x, t])
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))} :
    IsGenericBlowupValuation sX V v ↔ IsWeightedMonomialValuation sX V x t 1 v := by
  have key : ∀ (g : X.presheaf.stalk V.isIrreducible.genericPoint) (M : ℕ),
      IsGreatest {n : ℕ | g ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk V.isIrreducible.genericPoint) ^ n} M ↔
        MMP.Resolution.monomialValuation t x 1 g = M := by
    intro g M
    rw [monomialValuation_one_eq_iSup hxt, isGreatest_iff_iSup_eq ⟨0, by simp⟩]
    rfl
  constructor
  · rintro ⟨hN, -, -, hreg, hv⟩
    exact ⟨hN, hcodim, hreg, hxt, le_rfl, fun g hg =>
      (hv g hg).imp fun M h => ⟨(key g M).mp h.1, h.2⟩⟩
  · rintro ⟨hN, -, hreg, -, -, hv⟩
    exact ⟨hN, h3, hV, hreg, fun g hg => (hv g hg).imp fun M h => ⟨(key g M).mpr h.1, h.2⟩⟩

end GenericBlowup

/-! ### Flip moves, weighted bad sets, varying branch numbers and varying unions -/

namespace StabilizedTail

namespace TerminalChain

variable {T : StabilizedTail} (C : TerminalChain T)

/-- The index of the model `V_{k+1}` reached by the `k`-th flip `V_k → T_k ← V_{k+1}` of the
`i`-th bridge, by cases on the decision of `k + 1 < m_i`. -/
def flipTargetOf (i : ℕ) (k : Fin (C.bridge i).P.m) :
    Decidable (k.1 + 1 < (C.bridge i).P.m) → C.ModelIndex
  | isTrue h => ⟨i, some ⟨k.1 + 1, h⟩⟩
  | isFalse _ => ⟨i + 1, none⟩

/-- The index of the model `V_{k+1}` reached by the `k`-th flip `V_k → T_k ← V_{k+1}` of the
`i`-th bridge: the model `(i, some (k + 1))` if `k + 1 < m_i`, and otherwise the junction
`(i + 1, none)`, the end of the bridge. -/
def flipTarget (i : ℕ) (k : Fin (C.bridge i).P.m) : C.ModelIndex :=
  C.flipTargetOf i k inferInstance

/-- If `k + 1 < m_i`, the `k`-th flip of the `i`-th bridge reaches the model
`(i, some (k + 1))`. -/
theorem flipTarget_of_lt {i : ℕ} {k : Fin (C.bridge i).P.m} (h : k.1 + 1 < (C.bridge i).P.m) :
    C.flipTarget i k = ⟨i, some ⟨k.1 + 1, h⟩⟩ := by
  unfold flipTarget
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

/-- If `k + 1 < m_i` fails, the `k`-th flip of the `i`-th bridge reaches the junction
`(i + 1, none)`. -/
theorem flipTarget_of_not_lt {i : ℕ} {k : Fin (C.bridge i).P.m}
    (h : ¬ k.1 + 1 < (C.bridge i).P.m) : C.flipTarget i k = ⟨i + 1, none⟩ := by
  unfold flipTarget
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

/-- The model reached by a flip of the `i`-th bridge lies on the `i`-th bridge or later. -/
theorem fst_flipTarget_ge (i : ℕ) (k : Fin (C.bridge i).P.m) : i ≤ (C.flipTarget i k).1 := by
  unfold flipTarget
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d <;> simp [flipTargetOf]

/-- The morphism `V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge, by cases on the
decision of `k + 1 < m_i`. -/
def flipTargetMapOf (i : ℕ) (k : Fin (C.bridge i).P.m) :
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) →
      C.model (C.flipTargetOf i k d) ⟶ (C.bridge i).P.T k
  | isTrue _ => (C.bridge i).P.gp k
  | isFalse _ => (C.bridge i).e.inv ≫
      eqToHom (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y) (by omega :
        (C.bridge i).P.m = k.1 + 1)) ≫ (C.bridge i).P.gp k

/-- The morphism `g_k⁺ : V_{k+1} ⟶ T_k` of the `k`-th flip of the `i`-th bridge, on the model
`C.flipTarget i k`: `g_k⁺` itself if `k + 1 < m_i`, and `g_k⁺ ∘ e⁻¹ : Y_{i+1} ⟶ T_k` otherwise,
for the identification `e : V_{m_i} ≅ Y_{i+1}` of the bridge. -/
def flipTargetMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    C.model (C.flipTarget i k) ⟶ (C.bridge i).P.T k :=
  C.flipTargetMapOf i k inferInstance

/-- The morphism `V_{k+1} ⟶ T_k` of a flip of a bridge is dominant, for either decision of
`k + 1 < m_i`. -/
theorem isDominant_flipTargetMapOf (i : ℕ) (k : Fin (C.bridge i).P.m)
    (d : Decidable (k.1 + 1 < (C.bridge i).P.m)) : IsDominant (C.flipTargetMapOf i k d) := by
  have hD : IsDominant ((C.bridge i).P.gp k) :=
    ((C.bridge i).P.isThreefoldStepDiagram k k.2).isSmallMorphism_plus.isBirationalMorphism
      |>.isDominant
  cases d with
  | isTrue _ => exact hD
  | isFalse h =>
    have h1 : IsDominant (C.bridge i).e.inv := inferInstance
    have h2 : IsDominant (eqToHom (congrArg (modelSeq (C.junction i).Y
      (C.bridge i).P.Y) (by omega : (C.bridge i).P.m = k.1 + 1))) := inferInstance
    have h3 : IsDominant (eqToHom (congrArg (modelSeq (C.junction i).Y
        (C.bridge i).P.Y) (by omega : (C.bridge i).P.m = k.1 + 1)) ≫ (C.bridge i).P.gp k) :=
      ⟨hD.denseRange.comp h2.denseRange ((C.bridge i).P.gp k).continuous⟩
    exact ⟨h3.denseRange.comp h1.denseRange (Scheme.Hom.continuous _)⟩

/-- The morphism `V_{k+1} ⟶ T_k` of a flip of a bridge is dominant. -/
theorem isDominant_flipTargetMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsDominant (C.flipTargetMap i k) :=
  C.isDominant_flipTargetMapOf i k _

/-- The base `T_k` of a flip of a bridge is an integral scheme. -/
theorem isIntegral_flipBase (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsIntegral ((C.bridge i).P.T k) :=
  ((C.bridge i).P.isThreefoldStepDiagram k k.2).isNormalVariety_target.1.toIsIntegral

/-- The morphism `g_k : V_k ⟶ T_k` of a flip of a bridge is dominant. -/
theorem isDominant_flipSourceMap (i : ℕ) (k : Fin (C.bridge i).P.m) :
    IsDominant ((C.bridge i).P.g k) :=
  ((C.bridge i).P.isThreefoldStepDiagram k k.2).isBirationalMorphism_minus.isDominant

end TerminalChain

namespace PreparedChain

variable {T : StabilizedTail} (Q : PreparedChain T)

/-- The *small terminal flip moves* of a prepared chain: the flips `V_k → T_k ← V_{k+1}`,
`k < m_i`, of the `i`-th bridges with `i ≥ i₀`; both morphisms of each are small
(`MMP.Fourfold.StabilizedTail.TerminalBridge.isSmallMorphism_and_isSmallMorphism`). -/
abbrev FlipMove : Type := {p : Σ i : ℕ, Fin (Q.chain.bridge i).P.m // Q.start ≤ p.1}

namespace FlipMove

variable {Q} (μ : Q.FlipMove)

/-- The source `(Y⁻, Θ⁻) = (V_k, Θ_k)` of a flip move, a model of the prepared chain. -/
def source : Q.ModelIndex := ⟨⟨μ.1.1, some μ.1.2⟩, μ.2⟩

/-- The target `(Y⁺, Θ⁺)` of a flip move, a model of the prepared chain: `(V_{k+1}, Θ_{k+1})`,
which is the next junction `(Y_{i+1}, Θ_{i+1})` when `k + 1 = m_i`. -/
def target : Q.ModelIndex :=
  ⟨Q.chain.flipTarget μ.1.1 μ.1.2, μ.2.trans (Q.chain.fst_flipTarget_ge _ _)⟩

/-- The base `Z = T_k` of the step diagram `Y⁻ → Z ← Y⁺` of a flip move. -/
abbrev base : Scheme.{0} := (Q.chain.bridge μ.1.1).P.T μ.1.2

/-- The morphism `Y⁻ ⟶ Z` of a flip move. -/
def sourceMap : Q.chain.model μ.source.1 ⟶ μ.base := (Q.chain.bridge μ.1.1).P.g μ.1.2

/-- The morphism `Y⁺ ⟶ Z` of a flip move. -/
def targetMap : Q.chain.model μ.target.1 ⟶ μ.base := Q.chain.flipTargetMap μ.1.1 μ.1.2

/-- The base `Z` of a flip move is an integral scheme. -/
instance isIntegral_base : IsIntegral μ.base := Q.chain.isIntegral_flipBase _ _

/-- The morphism `Y⁻ ⟶ Z` of a flip move is dominant. -/
instance isDominant_sourceMap : IsDominant μ.sourceMap := Q.chain.isDominant_flipSourceMap _ _

/-- The morphism `Y⁺ ⟶ Z` of a flip move is dominant. -/
instance isDominant_targetMap : IsDominant μ.targetMap := Q.chain.isDominant_flipTargetMap _ _

/-- The bad locus `W⁻ ⊆ Y⁻` of a flip move. -/
abbrev badLocusSource : Closeds (Q.chain.model μ.source.1) :=
  badLocusMinus μ.sourceMap μ.targetMap

/-- The bad locus `W⁺ ⊆ Y⁺` of a flip move. -/
abbrev badLocusTarget : Closeds (Q.chain.model μ.target.1) :=
  badLocusPlus μ.sourceMap μ.targetMap

end FlipMove

/-- The *weighted bad set* `𝒜₀` of a small terminal flip move `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a
prepared chain, written as a threefold step diagram `Y⁻ → Z ← Y⁺` with bad loci `W^±`: the set of
normalized divisorial valuations `v` of `ℂ(Y⁻)` which are exceptional over `Y⁻` and over `Y⁺`
(as a valuation `v⁺` of `ℂ(Y⁺)` with the same restriction to `ℂ(Z)`), whose centre `c_{Y⁻}(v)`
lies in `W⁻`, and such that `w_v(Y⁻, Θ⁻) + w_v(Y⁺, Θ⁺) > 0`, for the weights
`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight` at the admissible scale. -/
@[mmp "def_mmp_indexd_flip_bad_set"]
def flipBadSet (μ : Q.FlipMove) :
    Set (Valuation (Q.chain.model μ.source.1).functionField (WithZero (Multiplicative ℤ))) :=
  {v | (∃ Z : IrreducibleCloseds (Q.chain.model μ.source.1),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure μ.source.1) v Z ∧
        (Z : Set (Q.chain.model μ.source.1)) ⊆ μ.badLocusSource) ∧
    ∃ v' : Valuation (Q.chain.model μ.target.1).functionField (WithZero (Multiplicative ℤ)),
      v'.comap (functionFieldMap μ.targetMap) = v.comap (functionFieldMap μ.sourceMap) ∧
      ∃ w w' : ℕ, Q.chain.IsValuationWeight Q.scale μ.source.1 v w ∧
        Q.chain.IsValuationWeight Q.scale μ.target.1 v' w' ∧ 0 < w + w'}

end PreparedChain

namespace TerminalChain

variable {T : StabilizedTail} (C : TerminalChain T)

/-- `r` is the *varying branch number* `r_C^var = ∑_{h varying} r_{C,h}` at an irreducible closed
curve `C` (`γ`) of the model `M` indexed by `x`: the sum, over the varying labels `S_h`, of their
branch numbers `r_{C,h}` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBranchNumber`), that
is, the number of prime divisors of `∐_{h varying} S_h^ν` mapping onto `C`. -/
@[mmp "def_mmp_indexd_varying_branch_number"]
def IsVaryingBranchNumber (x : C.ModelIndex) (γ : ProperCurve (C.modelStructure x)) (r : ℕ) :
    Prop :=
  ∃ r' : C.Label → ℕ, (∀ S, C.IsVaryingLabel S → C.IsLabelBranchNumber S x γ (r' S)) ∧
    r = ∑ᶠ (S) (_ : C.IsVaryingLabel S), r' S

/-- The *varying union* `Q ⊆ Y_i` at the junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)` of a terminal
chain: the union of the varying labels on `Y_i`, that is, of the supports of the prime divisors
`S_h^{Y_i}` of `Y_i` for the varying labels `S_h`, with its reduced structure. -/
@[mmp "def_mmp_indexd_varying_union"]
def varyingUnion (i : ℕ) : Set (C.junction i).Y :=
  {y | ∃ S : C.Label, C.IsVaryingLabel S ∧
    ∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧
      y ∈ P.support}

end TerminalChain

namespace PreparedChain

variable {T : StabilizedTail} (Q : PreparedChain T)

/-- At a junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, of a prepared chain, `p_i` maps the
varying union onto a finite set. -/
theorem finite_image_varyingUnion {i : ℕ} (hi : Q.start ≤ i) :
    ((Q.chain.junction i).p '' Q.chain.varyingUnion i).Finite :=
  Q.finite_image_varyingLabels i hi

/-- At a junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, of a prepared chain, `p_i` maps the
varying union onto a set of closed points. -/
theorem isClosed_of_mem_image_varyingUnion {i : ℕ} (hi : Q.start ≤ i) {z : T.X i}
    (hz : z ∈ (Q.chain.junction i).p '' Q.chain.varyingUnion i) : IsClosed ({z} : Set (T.X i)) :=
  Q.isClosed_of_mem_image_varyingLabels i hi z hz

end PreparedChain

end StabilizedTail

end MMP.Fourfold
