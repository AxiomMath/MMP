module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.RationalQCartierLcBoundary
import MMP.AlgebraicGeometry.Singularities.Surface.ExceptionalCycleEuler
import MMP.AlgebraicGeometry.Singularities.Surface.ArtinRationalityCriterion
import MMP.AlgebraicGeometry.Singularities.Surface.NoetherFormulaLcObstruction
import MMP.AlgebraicGeometry.Singularities.Surface.WeightedDualGraph
import MMP.AlgebraicGeometry.Intersection.Surface.BlowupGenusDropAdjunction
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts

/-!
# A nonzero boundary with nonnegative log discrepancies forces a rational surface singularity

Let `f : Y ⟶ X` be the minimal resolution of a normal surface germ `(X, P)` over an
algebraically closed field `k`, with exceptional curves `E_1, …, E_n`, `n ≥ 1`. Let `T ≠ 0` be
a boundary on the germ (an effective `ℚ`-divisor with coefficients in `[0, 1]` whose components
pass through `P`), and let `a ∈ ℚ^n` be the log discrepancy vector of `(X, P; T)` on `f`, that
is the solution of `((K_Y + f⁻¹_* T + ∑_j (1 - a_j) E_j) · E_i) = 0` for all `i`. If every
`a_i ≥ 0`, then `(X, P)` is a rational singularity, and consequently every `ℚ`-divisor on `X`
is `ℚ`-Cartier on a neighbourhood of `P`.

The positive boundary is what excludes the elliptic and cusp cases of numerically log canonical
surface germs with zero boundary.

## Main results

* `MMP.Flips.IsMinimalGermResolution.isRationalSurfaceSingularity_of_isGermLogDiscrepancyVector`:
  the rationality of `(X, P)` and the `ℚ`-Cartier property of all `ℚ`-divisors near `P`.

## Implementation notes

Write `Γ` for the weighted dual graph of `f` with boundary `T` and `Γ⁰` for the one with
boundary `0`; they have the same intersection matrix `M`, weights `n_j` and genera `p_j`. Some
boundary degree `β_j = (f⁻¹_* T · E_j)` is positive, so a genus-one vertex is excluded, every
`p_j = 0`, and minimality gives `n_j ≥ 2`. The log discrepancy vector `a⁰` of `Γ⁰` satisfies
`a < a⁰ ≤ 1`. The positive-cycle criterion is then proved directly: a nonzero cycle `z ≥ 0` with
`χ(𝒪_z) ≤ 0` and minimal `∑ z_j` has `(M z)_i ≥ 2 - n_i` on its support, and
`x = (z + a⁰ - 1)|_{supp z}` would be a nonzero vector with `xᵀ M x ≥ 0`, contradicting negative
definiteness. So `Γ⁰` is rational, and Artin's criterion makes `(X, P)` rational.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][FA], Chapter 3.
* [M. Artin, *On isolated rational singularities of surfaces*][Artin1966]
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori Finset

/-! ### The positive-cycle criterion for weighted graphs -/

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

open WeightedGraph

/-- The integer form `zᵀ M(Γ) z + ∑_j z_j (2p_j - 2 + n_j)`, which is `-2 χ(𝒪_Z)` for the cycle
`Z = ∑ z_j E_j`. -/
private def eulerForm (Γ : WeightedGraph V) (z : V → ℤ) : ℤ :=
  (∑ j, ∑ l, z j * Γ.matrix j l * z l) + ∑ j, z j * (2 * Γ.genus j - 2 + Γ.weight j)

/-- The diagonal entries of `M(Γ)` are `-n_j`. -/
private lemma matrix_self (Γ : WeightedGraph V) (j : V) : Γ.matrix j j = -Γ.weight j := by
  simp [matrix]

/-- The off-diagonal entries of `M(Γ)` are the edge weights. -/
private lemma matrix_of_ne (Γ : WeightedGraph V) {j l : V} (h : j ≠ l) :
    Γ.matrix j l = Γ.edgeWeight j l := by
  simp [matrix, h]

/-- Adding a vertex to a cycle: `Q(w + e_i) = Q(w) + 2 (M w)_i + M_ii + 2p_i - 2 + n_i`. -/
private lemma eulerForm_add_single (Γ : WeightedGraph V) (w : V → ℤ) (i : V) :
    eulerForm Γ (w + Pi.single i 1) = eulerForm Γ w + 2 * ∑ l, Γ.matrix i l * w l +
      Γ.matrix i i + (2 * Γ.genus i - 2 + Γ.weight i) := by
  have hs : ∑ j, w j * Γ.matrix j i = ∑ l, Γ.matrix i l * w l :=
    Finset.sum_congr rfl fun j _ => by rw [Γ.matrix_isSymm.apply i j, mul_comm]
  have h2 : (∑ x, ∑ x_1, if x = i then Γ.matrix x x_1 * w x_1 else 0) =
      ∑ l, Γ.matrix i l * w l := by
    rw [Finset.sum_comm]
    simp
  simp only [eulerForm, Pi.add_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hs, h2]
  ring

/-- For a cycle `z` with `χ(𝒪_z) ≤ 0` such that `z - e_i`, if nonzero, has `χ ≥ 1`, and
`p_i = 0`: `(M z)_i ≥ 2 - n_i`. -/
private lemma two_sub_weight_le {i : V} (hp : Γ.genus i = 0) {z : V → ℤ}
    (hbad : -2 < eulerForm Γ z)
    (hmin : z - Pi.single i 1 ≠ 0 → eulerForm Γ (z - Pi.single i 1) ≤ -2) :
    2 - Γ.weight i ≤ ∑ l, Γ.matrix i l * z l := by
  set w := z - Pi.single i 1 with hw
  have hz : z = w + Pi.single i 1 := by rw [hw, sub_add_cancel]
  have hE := eulerForm_add_single Γ w i
  rw [← hz] at hE
  have hS : ∑ l, Γ.matrix i l * z l = ∑ l, Γ.matrix i l * w l + Γ.matrix i i := by
    rw [hz]
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  rw [hS, matrix_self]
  rw [matrix_self, hp] at hE
  by_cases hw0 : w = 0
  · have h0 : eulerForm Γ 0 = 0 := by simp [eulerForm]
    simp only [hw0, Pi.zero_apply, mul_zero, Finset.sum_const_zero, h0] at hE
    push_cast at hE
    omega
  · have := hmin hw0
    push_cast at hE
    omega

/-- On the support of a cycle `z` with `(M z)_i ≥ 2 - n_i` and `p_i = 0`, the vector
`x = (z + α - 1)|_{supp z}` has `(M x)_i ≥ 0`. -/
private lemma sum_matrix_mul_nonneg_of_two_sub_weight_le {i : V} (hp : Γ.genus i = 0)
    {α : V → ℚ} (hα : Γ.IsLogDiscrepancyVector α) (hα1 : ∀ j, α j ≤ 1) {z : V → ℤ}
    (hi : z i ≠ 0) (hzi : 2 - Γ.weight i ≤ ∑ l, Γ.matrix i l * z l) :
    0 ≤ ∑ l, (Γ.matrix i l : ℚ) * (if z l = 0 then 0 else (z l : ℚ) + α l - 1) := by
  have hsplit : ∑ l, (Γ.matrix i l : ℚ) * (if z l = 0 then 0 else (z l : ℚ) + α l - 1) =
      ∑ l, (Γ.matrix i l : ℚ) * (z l + α l - 1) -
        ∑ l, (Γ.matrix i l : ℚ) * (if z l = 0 then α l - 1 else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : z l = 0 <;> simp [hl]
  have hneg2 : ∑ l, (Γ.matrix i l : ℚ) * (if z l = 0 then α l - 1 else 0) ≤ 0 :=
    Finset.sum_nonpos fun l _ => by
      by_cases hl : z l = 0
      · have hil : i ≠ l := fun h => hi (h ▸ hl)
        simp only [hl, if_true, matrix_of_ne Γ hil]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hα1 l])
      · simp [hl]
  have hsymm : ∑ l, (Γ.matrix i l : ℚ) * α l = ∑ l, α l * (Γ.matrix l i : ℚ) :=
    Finset.sum_congr rfl fun l _ => by rw [Γ.matrix_isSymm.apply l i, mul_comm]
  have hrow : ∑ l, (Γ.matrix i l : ℚ) = -Γ.weight i +
      ∑ l ∈ univ.erase i, (Γ.edgeWeight i l : ℚ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [matrix_self]
    · exact Finset.sum_congr rfl fun l hl => by
        rw [matrix_of_ne Γ (Finset.ne_of_mem_erase hl).symm]
        push_cast
        rfl
  have hzq : (2 - Γ.weight i : ℚ) ≤ ∑ l, (Γ.matrix i l : ℚ) * z l := mod_cast hzi
  have hfirst : ∑ l, (Γ.matrix i l : ℚ) * (z l + α l - 1) =
      ∑ l, (Γ.matrix i l : ℚ) * z l + ∑ l, (Γ.matrix i l : ℚ) * α l -
        ∑ l, (Γ.matrix i l : ℚ) := by
    simp only [mul_sub, mul_add, mul_one, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit, hfirst, hsymm, hα i, hrow]
  simp only [c, hp, Nat.cast_zero, mul_zero, sub_zero]
  linarith [Γ.boundary_nonneg i]

/-- No nonzero cycle `z ≥ 0` has `(M z)_i ≥ 2 - n_i` on its support, when `Γ` is negative
definite of genus zero with a log discrepancy vector `0 < α ≤ 1`. -/
private lemma false_of_two_sub_weight_le (hneg : Γ.IsNegDef) (hp : ∀ j, Γ.genus j = 0)
    {α : V → ℚ} (hα : Γ.IsLogDiscrepancyVector α) (hα0 : ∀ j, 0 < α j) (hα1 : ∀ j, α j ≤ 1)
    {z : V → ℤ} (hz0 : 0 ≤ z) (hzne : z ≠ 0)
    (hz : ∀ i, z i ≠ 0 → 2 - Γ.weight i ≤ ∑ l, Γ.matrix i l * z l) : False := by
  set x : V → ℚ := fun j => if z j = 0 then 0 else z j + α j - 1 with hx
  have hxi : ∀ i, z i ≠ 0 → 0 < x i := fun i hi => by
    have : (1 : ℚ) ≤ z i := by exact_mod_cast (lt_of_le_of_ne (hz0 i) (Ne.symm hi))
    simp only [hx, if_neg hi]
    linarith [hα0 i]
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hzne
  have hxne : x ≠ 0 := fun h => (hxi i₀ hi₀).ne' (congrFun h i₀)
  have hpos := hneg.dotProduct_mulVec_pos hxne
  have hle : 0 ≤ ∑ i, x i * ∑ l, (Γ.matrix i l : ℚ) * x l :=
    Finset.sum_nonneg fun i _ => by
      by_cases hi : z i = 0
      · simp [hx, hi]
      · exact mul_nonneg (hxi i hi).le
          (sum_matrix_mul_nonneg_of_two_sub_weight_le (hp i) hα hα1 hi (hz i hi))
  simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg, dotProduct, Matrix.mulVec,
    Matrix.map_apply, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg] at hpos
  linarith

/-- **The positive-cycle criterion.** A negative definite weighted graph of genus zero with a log
discrepancy vector `α` with `0 < α ≤ 1` is rational. -/
private lemma isRational_of_isLogDiscrepancyVector (hneg : Γ.IsNegDef) (hp : ∀ j, Γ.genus j = 0)
    {α : V → ℚ} (hα : Γ.IsLogDiscrepancyVector α) (hα0 : ∀ j, 0 < α j) (hα1 : ∀ j, α j ≤ 1) :
    Γ.IsRational := by
  have key : ∀ N : ℕ, ∀ z : V → ℤ, 0 ≤ z → z ≠ 0 → ∑ j, z j = N →
      eulerForm Γ z ≤ -2 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro z hz0 hzne hN
    by_contra hbad
    push Not at hbad
    refine false_of_two_sub_weight_le hneg hp hα hα0 hα1 hz0 hzne fun i hi => ?_
    have hzi : 1 ≤ z i := lt_of_le_of_ne (hz0 i) (Ne.symm hi)
    have hle : z i ≤ ∑ j, z j := Finset.single_le_sum (fun j _ => hz0 j) (Finset.mem_univ i)
    refine two_sub_weight_le (hp i) hbad fun hw => ?_
    refine ih (N - 1) (by omega) _ (fun j => ?_) hw ?_
    · by_cases hj : j = i
      · subst hj
        simp only [Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same]
        omega
      · simpa [Pi.single_apply, hj] using hz0 j
    · simp only [Pi.sub_apply]
      rw [Finset.sum_sub_distrib, Finset.sum_pi_single']
      simp only [Finset.mem_univ, if_true]
      omega
  intro z hz
  have h := key (∑ j, z j) (fun j => (z j : ℤ)) (fun j => by simp)
    (fun h => hz (funext fun j => by simpa using congrFun h j)) (by push_cast; rfl)
  have hq : ((eulerForm Γ fun j => (z j : ℤ)) : ℚ) ≤ -2 := mod_cast h
  simp only [eulerForm] at hq
  push_cast at hq
  linarith

end Graph

/-! ### Transfer to the full restriction -/

/-- A log discrepancy vector of `G|_{univ}` is one of `G`. -/
private lemma isLogDiscrepancyVector_of_restrict_univ {V : Type*} [Fintype V] [DecidableEq V]
    (G : WeightedGraph V) {a : ↥(univ : Finset V) → ℚ}
    (ha : (G.restrict univ).IsLogDiscrepancyVector a) :
    G.IsLogDiscrepancyVector fun k => a ⟨k, mem_univ k⟩ := by
  let e : ↥(univ : Finset V) ≃ V := Equiv.subtypeUnivEquiv mem_univ
  have hm : ∀ k l : ↥(univ : Finset V), (G.restrict univ).matrix k l = G.matrix k l := by
    intro k l
    simp only [WeightedGraph.matrix, Matrix.of_apply, Subtype.ext_iff]
    rfl
  have hc : ∀ l : ↥(univ : Finset V), (G.restrict univ).c l = G.c l := by
    intro l
    simp only [WeightedGraph.c, Finset.sum_erase_eq_sub (mem_univ _)]
    congr 2
    exact Fintype.sum_equiv e _ _ fun k => rfl
  intro j
  have := ha ⟨j, mem_univ j⟩
  rw [hc] at this
  rw [← this]
  exact (Fintype.sum_equiv e _ _ fun k => by rw [hm]; rfl).symm

/-! ### The surface germ -/

/-- If the boundary `T` is nonzero and the exceptional locus is nonempty, some boundary degree
`β_j = (f⁻¹_* T · E_j)` of the weighted dual graph is positive. -/
private lemma exists_boundary_pos {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {P : X} {T : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}
    {Γ : WeightedGraph (Fin n)} (hΓ : IsWeightedDualGraph sX P T f E Γ) (hn : 0 < n)
    (hT : T ≠ 0) : ∃ j, 0 < Γ.boundary j := by
  classical
  have hB := hΓ.isSurfaceGermWithBoundary
  have hg := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  obtain ⟨C, hC⟩ : ∃ C, T C ≠ 0 := Finsupp.ne_iff.1 hT
  obtain ⟨j, x, hx, hx1⟩ := hg.exists_one_le_inverseTransform_intersectionNumber hB hE hn
    (Finsupp.mem_support_iff.2 hC)
  have hB' : IsSurfaceGermWithBoundary sX P (T.erase C) := by
    refine ⟨hB.1, fun C' hC' => hB.2.1 C' ?_, fun C' => ?_⟩
    · rw [Finsupp.support_erase] at hC'
      exact Finset.mem_of_mem_erase hC'
    · rw [Finsupp.erase_apply]
      split_ifs
      · exact ⟨le_rfl, zero_le_one⟩
      · exact hB.2.2 C'
  obtain ⟨Γ', hΓ'⟩ := hg.exists_isWeightedDualGraph hB' hE
  have hsplit : inverseTransformDivisor f T = inverseTransformDivisor f (T.erase C) +
      T C • inverseTransformDivisor f (Finsupp.single C (1 : ℚ)) := by
    conv_lhs => rw [← Finsupp.erase_add_single C T, ← Finsupp.smul_single_one]
    rw [map_add]
    congr 1
    exact (inverseTransformDivisorₗ ℚ f).map_smul (T C) (Finsupp.single C 1)
  have h3 := isIntersectionNumber_add (hΓ'.boundary j) (hx.smul (T C)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hg.isSmoothResolution.isSmoothScheme _))
  rw [← hsplit] at h3
  refine ⟨j, ?_⟩
  rw [(hΓ.boundary j).unique h3]
  nlinarith [Γ'.boundary_nonneg j, lt_of_le_of_ne (hB.2.2 C).1 (Ne.symm hC)]

/-- A `ℚ`-combination of Cartier divisors is `ℚ`-Cartier. -/
private lemma isQCartier_of_isCartierCombination {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : IsCartierCombination D) : D.IsQCartier := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  exact QDivisor.isQCartier_sum _ _ fun j _ =>
    QDivisor.IsQCartier.qsmul (QDivisor.isQCartier_toQDivisor (hL j)) (r j)

/-- For the dual graph of a minimal resolution with nonnegative log discrepancies, a positive
boundary degree at some vertex forces every vertex to have genus zero. -/
private lemma IsMinimalGermResolution.genus_eq_zero_of_boundary_pos {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {T : QDivisor X}
    {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)} {a : Fin n → ℚ}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P T f E Γ)
    (haΓ : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ i, 0 ≤ a i) {j₀ : Fin n}
    (hj₀ : 0 < Γ.boundary j₀) (j : Fin n) : Γ.genus j = 0 := by
  by_contra h0
  have hj1 : Γ.genus j = 1 := by
    have := hf.genus_le_one_of_logDiscrepancy_nonneg hΓ haΓ ha0 j
    omega
  obtain ⟨rfl, hβ⟩ := hf.eq_one_and_boundary_eq_zero_of_genus_eq_one hΓ haΓ ha0 hj1
  rw [Subsingleton.elim j₀ j, hβ] at hj₀
  exact lt_irrefl _ hj₀

/-- **A nonzero boundary with nonnegative log discrepancies forces rationality.** Let
`f : Y ⟶ X` be a minimal resolution of the surface germ `(X, P)` over an algebraically closed
field, with exceptional curves `E_1, …, E_n`, `n ≥ 1`, and let `a` be the log discrepancy vector
on `f` of a nonzero boundary `T` of the germ. If `0 ≤ a_i` for every `i`, then `(X, P)` is a
rational singularity and every `ℚ`-divisor on `X` is `ℚ`-Cartier on some open neighbourhood
of `P`. -/
@[mmp "lem_mmp_surface_positive_boundary_numerical_lc_rational"]
public theorem IsMinimalGermResolution.isRationalSurfaceSingularity_of_isGermLogDiscrepancyVector
    {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    [IsLocallyNoetherian X] [IsNormal X] {T : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)]
    [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {a : Fin n → ℚ}
    (hf : IsMinimalGermResolution sX P f) (hn : 0 < n) (hT : T ≠ 0)
    (ha : IsGermLogDiscrepancyVector sX P T f E a) (ha0 : ∀ i, 0 ≤ a i) :
    IsRationalSurfaceSingularity sX P ∧
      ∀ D : QDivisor X, ∃ U : X.Opens, P ∈ U ∧ QDivisor.IsQCartier (D.restrictOpen U) := by
  classical
  obtain ⟨hB, hg, hE, -⟩ := id ha
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨Γ, hΓ⟩ := hg.exists_isWeightedDualGraph hB hE
  have haΓ : Γ.IsLogDiscrepancyVector a := (hΓ.isGermLogDiscrepancyVector_iff a).1 ha
  obtain ⟨j₀, hj₀⟩ := exists_boundary_pos hΓ hn hT
  obtain ⟨Γ0, hΓ0⟩ := hg.exists_isWeightedDualGraph
    (⟨hB.1, fun C hC => by simp at hC, fun C => by simp⟩ : IsSurfaceGermWithBoundary sX P 0) hE
  have hw : ∀ j, Γ0.weight j = Γ.weight j := fun j => by
    exact_mod_cast neg_injective ((hΓ0.weight j).unique (hΓ.weight j))
  have hgen : ∀ j, Γ0.genus j = Γ.genus j := fun j => mod_cast (hΓ0.genus j).unique (hΓ.genus j)
  have hew : ∀ j l, Γ0.edgeWeight j l = Γ.edgeWeight j l := fun j l => by
    rcases eq_or_ne j l with rfl | h
    · rw [Γ0.edgeWeight_self, Γ.edgeWeight_self]
    · exact_mod_cast (hΓ0.edgeWeight j l h).unique (hΓ.edgeWeight j l h)
  have hb0 : ∀ j, Γ0.boundary j = 0 := fun j => by
    have h := hΓ0.boundary j
    rw [map_zero] at h
    exact h.unique (isIntersectionNumber_zero (hΓ.weight j))
  have hp := hf.genus_eq_zero_of_boundary_pos hΓ haΓ ha0 hj₀
  have hd0 := hf.d_nonpos hΓ0
  have hw2 : ∀ j, 2 ≤ Γ.weight j := fun j => by
    have h := hd0 j
    simp only [WeightedGraph.d, hgen, hp, hb0, Nat.cast_zero, mul_zero, sub_zero] at h
    rw [hw] at h
    exact_mod_cast (by linarith : (2 : ℚ) ≤ Γ.weight j)
  have hneg0 := hΓ0.isNegDef
  obtain ⟨a', ha', -⟩ := WeightedGraph.existsUnique_isLogDiscrepancyVector (Γ0.restrict univ)
    (hneg0.delta_pos univ).ne'
  have hα := isLogDiscrepancyVector_of_restrict_univ Γ0 ha'
  have hsub : (Γ0.restrict univ).IsSubgraph Γ :=
    ⟨fun j => hw j, fun j l _ => (hew j l).le, fun j => (hgen j).le,
      fun j => (hb0 j).trans_le (Γ.boundary_nonneg j)⟩
  have hne : (Γ0.restrict univ) ≠ Γ.restrict univ := fun h => hj₀.ne' <| by
    simpa [WeightedGraph.restrict, hb0] using
      (congrArg (fun G => G.boundary ⟨j₀, mem_univ j₀⟩) h).symm
  have hlt : ∀ j, a j < a' ⟨j, mem_univ j⟩ := fun j =>
    haΓ.lt_of_isSubgraph ha' hsub (.inr hne) hΓ.isNegDef ⟨hΓ.preconnected⟩ (hf.d_nonpos hΓ)
      (fun l h => by have := hw2 l; omega) (fun h => hj₀.ne' (h j₀).2.2) ⟨j, mem_univ j⟩
  have hX : IsRationalSurfaceSingularity sX P :=
    (hΓ0.isRationalSurfaceSingularity_iff_isRational hf).2 <|
      isRational_of_isLogDiscrepancyVector hneg0 (fun j => (hgen j).trans (hp j)) hα
        (fun j => (ha0 j).trans_lt (hlt j)) (hα.le_one hneg0 hd0)
  refine ⟨hX, fun D => ?_⟩
  obtain ⟨U, hPU, hD⟩ := hX.exists_isCartierCombination_restrictOpen D
  exact ⟨U, hPU, isQCartier_of_isCartierCombination hD⟩

end MMP.Flips
