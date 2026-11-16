module

public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChainLabel
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.GenericPoints

/-!
# Graph divisors of threefold step diagrams, branch numbers, weights and defaults

For a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)`, let `Γ ⊆ X⁻ ×_Z X⁺` be the closure of
the graph of the birational map `(f⁺)⁻¹ ∘ f⁻` and `ν : G ⟶ Γ` its normalization; with
`u : G ⟶ X⁻` and `v : G ⟶ X⁺` the two projections composed with `ν`, `(G, u, v)` is the
*normalized graph*, and the *graph divisor* is the `ℚ`-Cartier `ℚ`-divisor `H = u^* D⁻ - v^* D⁺`
on `G`, where `D^± = K_{X^±} + B^±`.

Let `(Y, Θ)` be a model of a terminal chain, `S_h` a label with normalization
`ν_h : S_h^ν ⟶ S_h`, and `C ⊆ Y` an irreducible closed curve. The *branch number* `r_{C,h}` is the
number of prime divisors of `S_h^ν` mapping onto `C`; it is `0` when `C ⊄ S_h`.

An *admissible scale* for a terminal chain over a stabilized tail `(X_i, B_i, Z_i, f_i, f_i⁺)` is
a positive integer `N` with `N c ∈ ℤ` for every coefficient `c` of `B_0` and for the eventual
value `c` of the coefficient of every fixed label. The *weight* of a real number `u` is
`w(u) = ⌈N max{u, 0}⌉ ∈ ℕ`; it is monotone, and `w(u) = 0` exactly when `u ≤ 0`. The *default*
of `b ∈ [0, 1)` is `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))`, a finite sum, and the default of a label
`S_h` of a model with coefficient `b_h` is `d_h = d(b_h)`.

## Main definitions

* `MMP.Fourfold.IsThreefoldGraphDivisor`: the graph divisor of a threefold step diagram; the
  normalized graph is `MMP.Fourfold.IsNormalizedGraph`.
* `MMP.Fourfold.branchNumber`: the number of prime divisors of the normalization of a prime
  divisor `S` mapping onto a given closed subset.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBranchNumber`: `r = r_{C,h}` on a model.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsAdmissibleScale`: admissible scales.
* `MMP.Fourfold.difficultyWeight`: the weight `w(u) = ⌈N max{u, 0}⌉`.
* `MMP.Fourfold.defaultWeight`: the default `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelDefault`: `d = d_h` on a model.

## Main results

* `MMP.Fourfold.IsThreefoldGraphDivisor.eq`: the graph divisor is unique.
* `MMP.Fourfold.branchNumber_eq_zero_of_not_subset`: `r_{C,h} = 0` when `C ⊄ S_h`.
* `MMP.Fourfold.difficultyWeight_mono`, `MMP.Fourfold.difficultyWeight_eq_zero_iff`: `w` is
  monotone, and `w(u) = 0` if and only if `u ≤ 0`.
* `MMP.Fourfold.finite_support_difficultyWeight`: for `b < 1`, only finitely many terms of the
  sum defining `d(b)` are nonzero.

## Implementation notes

* The normalized graph of the threefold source is the normalized graph of two morphisms to a
  common base, `MMP.Fourfold.IsNormalizedGraph`, which is stated for arbitrary morphisms; it is
  registered rather than restated. The graph divisor differs from `MMP.Fourfold.IsGraphDivisor`
  only in that the step diagram is a threefold step diagram, `MMP.Fourfold.IsThreefoldStepDiagram`,
  instead of a fourfold one, so it is stated anew. As there, the canonical divisor of `X⁺` is
  `(f⁺)⁻¹_* f⁻_* K⁻`, cut out by the same rational top form as `K⁻`.
* The normalization of a prime divisor `S` (an integral closed subscheme) is the normalization
  `Stacks.AlgebraicGeometry.Normalization.normalization` of `S` (Stacks 035N). A prime divisor `P`
  of `S^ν` maps onto `C` when the image of its support under `S^ν ⟶ S ⟶ Y` is `C`. The branch
  number of `S` along any closed subset `Z ⊆ Y` is defined; for a curve `C` it is taken at
  `Z = C`, the closure of the generic point of `C`. The count is `Set.ncard`, which is `0` on an
  infinite set; the set is finite.
* On a model `M` of a terminal chain the label `S_h` is its centre `S_h^M`, recorded (as in
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCoefficient`) only when it is a prime divisor
  of `M`; branch numbers and defaults on `M` are accordingly predicates on the value.
* The weight and the default are defined for every natural number `N`; the source takes `N` the
  fixed admissible scale of the chain. That `w(u) = 0` only for `u ≤ 0` needs `N > 0`. The
  default `d(b)` is defined for every real `b`, as a finitely supported sum `∑ᶠ` (`0` if the
  support is infinite); the source considers `b ∈ [0, 1)`, where the support is finite.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### Normalized graphs and graph divisors of threefold step diagrams -/

attribute [mmp "def_mmp_indexc_normalized_graph"] MMP.Fourfold.IsNormalizedGraph

section GraphDivisor

variable {Xm Xp Z G : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  [IsLocallyNoetherian G] [IsNormal G]

/-- The *graph divisor* of a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` (canonical divisors
`K⁻` and `K⁺ = (f⁺)⁻¹_* f⁻_* K⁻`) with normalized graph `(G, u, v)`: the `ℚ`-divisor
`H = u^* D⁻ - v^* D⁺` on `G`, where `D⁻ = K⁻ + B⁻`, `D⁺ = K⁺ + B⁺` and `u^*`, `v^*` are the
pull-backs of `ℚ`-Cartier `ℚ`-divisors. -/
@[mmp "def_mmp_indexc_normalized_graph"]
structure IsThreefoldGraphDivisor (sXm : Xm ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (sXp : Xp ⟶ Spec (.of ℂ)) (K : Divisor Xm) (B : QDivisor Xm) (fm : Xm ⟶ Z) (fp : Xp ⟶ Z)
    (u : G ⟶ Xm) (v : G ⟶ Xp) (H : QDivisor G) : Prop where
  isThreefoldStepDiagram : IsThreefoldStepDiagram sXm sZ sXp K B fm fp
  isNormalizedGraph : IsNormalizedGraph fm fp u v
  exists_pullback : ∃ (Hm Hp : QDivisor G)
    (hm : ∀ T : irreducibleComponents G,
      u (componentGenericPoint G T) ∉ (Divisor.toQDivisor K + B).supp)
    (hp : ∀ T : irreducibleComponents G, v (componentGenericPoint G T) ∉
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).supp),
    (Divisor.toQDivisor K + B).IsPullback u hm Hm ∧
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B).IsPullback v hp Hp ∧
      H = Hm - Hp

variable {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} {u : G ⟶ Xm} {v : G ⟶ Xp}
  {H : QDivisor G}

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- The graph divisor of a threefold step diagram with normalized graph `(G, u, v)` is
unique. -/
theorem IsThreefoldGraphDivisor.eq [CompactSpace G] {H' : QDivisor G}
    (h : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H)
    (h' : IsThreefoldGraphDivisor sXm sZ sXp K B fm fp u v H') : H = H' := by
  obtain ⟨Hm, Hp, hm, hp, hHm, hHp, rfl⟩ := h.exists_pullback
  obtain ⟨Hm', Hp', hm', hp', hHm', hHp', rfl⟩ := h'.exists_pullback
  have hD := h.isThreefoldStepDiagram
  rw [← hHm.pullback_eq hD.isQCartier_minus, ← hHm'.pullback_eq hD.isQCartier_minus,
    ← hHp.pullback_eq hD.isQCartier_plus, ← hHp'.pullback_eq hD.isQCartier_plus]

end GraphDivisor

/-! ### Branch numbers -/

section BranchNumber

/-- Every open subset of an irreducible scheme has finitely many irreducible components: it is
empty or irreducible. -/
theorem finite_irreducibleComponents_opens_of_irreducibleSpace {X : Scheme.{u}}
    [IrreducibleSpace X] (U : X.Opens) : (irreducibleComponents (U : Set X)).Finite := by
  rcases (U : Set X).eq_empty_or_nonempty with hU | hU
  · have : IsEmpty (U : Set X) := Set.isEmpty_coe_sort.mpr hU
    exact Set.toFinite _
  · have : IrreducibleSpace (U : Set X) := Subtype.irreducibleSpace
      ⟨hU, (IrreducibleSpace.isIrreducible_univ X).2.open_subset U.isOpen (Set.subset_univ _)⟩
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _

variable {Y : Scheme.{u}}

/-- The normalization `S^ν` of a prime divisor `S` of `Y`, regarded as an integral scheme. -/
abbrev primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y) : Scheme.{u} :=
  haveI := S.integral
  Stacks.AlgebraicGeometry.Normalization.normalizationScheme S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)

/-- The normalization `ν : S^ν ⟶ S` of a prime divisor `S` of `Y`, composed with the closed
immersion `S ⟶ Y`. -/
abbrev primeDivisorNormalization (S : MMP.Mori.PrimeDivisor Y) :
    primeDivisorNormalizationScheme S ⟶ Y :=
  haveI := S.integral
  Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) ≫ S.idealSheaf.subschemeι

/-- The *branch number* of a prime divisor `S` of `Y` along a subset `Z ⊆ Y`: the number of prime
divisors `P` of the normalization `S^ν` of `S` mapping onto `Z`, that is, with
`ν(P) = Z` for `ν : S^ν ⟶ S ⊆ Y` (`0` if there were infinitely many). For an irreducible closed
curve `C ⊆ Y` this is `r_C`, taken at `Z = C`. -/
@[mmp "def_mmp_indexd_branch_number"]
def branchNumber (S : MMP.Mori.PrimeDivisor Y) (Z : Set Y) : ℕ :=
  {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
    primeDivisorNormalization S '' P.support = Z}.ncard

/-- The image of the normalization of a prime divisor `S` lies in `S`. -/
theorem range_primeDivisorNormalization_subset (S : MMP.Mori.PrimeDivisor Y) :
    Set.range (primeDivisorNormalization S) ⊆ S.support := by
  have := S.integral
  rintro _ ⟨x, rfl⟩
  have h := S.idealSheaf.range_subschemeι ▸
    Set.mem_range_self (f := S.idealSheaf.subschemeι)
      (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
        (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) x)
  exact h

/-- The branch number of `S` along a subset `Z` not contained in `S` vanishes. -/
theorem branchNumber_eq_zero_of_not_subset {S : MMP.Mori.PrimeDivisor Y} {Z : Set Y}
    (hZ : ¬ Z ⊆ S.support) : branchNumber S Z = 0 := by
  rw [branchNumber, Set.eq_empty_of_forall_notMem fun P (hP : _ = Z) => hZ <|
    hP ▸ (Set.image_subset_range _ _).trans (range_primeDivisorNormalization_subset S)]
  exact Set.ncard_empty _

end BranchNumber

/-! ### Weights and defaults -/

section Weight

/-- The *weight* `w(u) = ⌈N max{u, 0}⌉` of a real number `u` at scale `N`, a natural number. -/
@[mmp "def_mmp_indexd_weight"]
def difficultyWeight (N : ℕ) (u : ℝ) : ℕ :=
  ⌈(N : ℝ) * max u 0⌉₊

variable {N : ℕ} {u : ℝ}

/-- The weight is the integer `⌈N max{u, 0}⌉`. -/
theorem natCast_difficultyWeight (N : ℕ) (u : ℝ) :
    (difficultyWeight N u : ℤ) = ⌈(N : ℝ) * max u 0⌉ :=
  Int.natCast_ceil_eq_ceil (mul_nonneg (Nat.cast_nonneg N) (le_max_right u 0))

/-- The weight is nondecreasing. -/
theorem difficultyWeight_mono (N : ℕ) : Monotone (difficultyWeight N) := fun _ _ h =>
  Nat.ceil_mono (mul_le_mul_of_nonneg_left (max_le_max h le_rfl) (Nat.cast_nonneg N))

/-- The weight of a nonpositive number is zero. -/
theorem difficultyWeight_of_nonpos (hu : u ≤ 0) : difficultyWeight N u = 0 := by
  rw [difficultyWeight, max_eq_right hu, mul_zero, Nat.ceil_zero]

/-- At a positive scale, the weight of `u` is zero exactly when `u ≤ 0`. -/
theorem difficultyWeight_eq_zero_iff (hN : 0 < N) : difficultyWeight N u = 0 ↔ u ≤ 0 := by
  refine ⟨fun h => not_lt.mp fun hu => ?_, difficultyWeight_of_nonpos⟩
  rw [difficultyWeight, Nat.ceil_eq_zero, max_eq_left hu.le] at h
  linarith [mul_pos (Nat.cast_pos.mpr hN : (0 : ℝ) < N) hu]

/-- The *default* `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))` at scale `N`, a finitely supported sum
(`0` if the support were infinite; for `b < 1` it is finite,
`MMP.Fourfold.finite_support_difficultyWeight`). -/
@[mmp "def_mmp_indexd_default"]
def defaultWeight (N : ℕ) (b : ℝ) : ℕ :=
  ∑ᶠ (j : ℕ) (_ : 1 ≤ j), difficultyWeight N (1 - j * (1 - b))

/-- For `b < 1`, the terms `w(1 - j(1 - b))` vanish for all but finitely many `j`. -/
theorem finite_support_difficultyWeight (N : ℕ) {b : ℝ} (hb : b < 1) :
    (Function.support fun j : ℕ => difficultyWeight N (1 - j * (1 - b))).Finite := by
  refine (Set.finite_Iio ⌈(1 - b)⁻¹⌉₊).subset fun j hj =>
    Set.mem_Iio.mpr <| not_le.mp fun hj' => hj ?_
  have hpos : 0 < 1 - b := by linarith
  have h := mul_le_mul_of_nonneg_right (Nat.ceil_le.mp hj') hpos.le
  rw [inv_mul_cancel₀ hpos.ne'] at h
  exact difficultyWeight_of_nonpos (by linarith)

end Weight

/-! ### Branch numbers, admissible scales and defaults on a terminal chain -/

namespace StabilizedTail

namespace TerminalChain

variable {T : StabilizedTail} (C : TerminalChain T)

/-- `r` is the *branch number* `r_{γ,h}` of a label `S_h` at an irreducible closed curve `γ` of
the model `M` indexed by `x`: the centre `S_h^M` is a prime divisor `P` of `M`, and `r` is the
number of prime divisors of the normalization of `P` mapping onto `γ`
(`MMP.Fourfold.branchNumber`); `r = 0` when `γ ⊄ S_h^M`
(`MMP.Fourfold.branchNumber_eq_zero_of_not_subset`). -/
@[mmp "def_mmp_indexd_branch_number"]
def IsLabelBranchNumber (S : C.Label) (x : C.ModelIndex) (γ : ProperCurve (C.modelStructure x))
    (r : ℕ) : Prop :=
  ∃ P : MMP.Mori.PrimeDivisor (C.model x),
    C.IsLabelCentre S x P ∧ r = branchNumber P (closure {γ.point})

/-- An *admissible scale* for a terminal chain over a stabilized tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`: a positive integer `N` such that `N c ∈ ℤ` for every
coefficient `c` of `B_0`, and for the eventual constant value `c` of the coefficient
`b_h^{(i)}` of every fixed label `S_h` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsFixedLabel`).
No condition is imposed on varying labels. -/
@[mmp "def_mmp_indexd_admissible_scale"]
def IsAdmissibleScale (N : ℕ) : Prop :=
  0 < N ∧ (∀ P : MMP.Mori.PrimeDivisor (T.X 0), ∃ z : ℤ, (N : ℚ) * (T.B 0).coeff P = z) ∧
    ∀ (S : C.Label) (c : ℚ), (∃ n : ℕ, ∀ i ≥ n, C.IsJunctionLabelCoefficient S i c) →
      ∃ z : ℤ, (N : ℚ) * c = z

variable {C}

/-- An admissible scale is positive. -/
theorem IsAdmissibleScale.pos {N : ℕ} (h : C.IsAdmissibleScale N) : 0 < N :=
  h.1

/-- An admissible scale `N` makes `N c` an integer for every coefficient `c` of `B_0`. -/
theorem IsAdmissibleScale.exists_intCast_eq_coeff {N : ℕ} (h : C.IsAdmissibleScale N)
    (P : MMP.Mori.PrimeDivisor (T.X 0)) : ∃ z : ℤ, (N : ℚ) * (T.B 0).coeff P = z :=
  h.2.1 P

/-- An admissible scale clears the denominator of the eventual coefficient of a fixed label. -/
theorem IsAdmissibleScale.exists_intCast_eq_of_eventually {N : ℕ} (h : C.IsAdmissibleScale N)
    {S : C.Label} {c : ℚ} {n : ℕ} (hc : ∀ i ≥ n, C.IsJunctionLabelCoefficient S i c) :
    ∃ z : ℤ, (N : ℚ) * c = z :=
  h.2.2 S c ⟨n, hc⟩

variable (C)

/-- `d` is the *default* `d_h = d(b_h)` of a label `S_h` at the model `M` indexed by `x`, at
scale `N` (the fixed admissible scale of the chain): `b_h` is the label coefficient `b_h^M` and
`d = d(b_h)` (`MMP.Fourfold.defaultWeight`). -/
@[mmp "def_mmp_indexd_default"]
def IsLabelDefault (N : ℕ) (S : C.Label) (x : C.ModelIndex) (d : ℕ) : Prop :=
  ∃ b : ℚ, C.IsLabelCoefficient S x b ∧ d = defaultWeight N b

end TerminalChain

end StabilizedTail

end MMP.Fourfold
