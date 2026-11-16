module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DltModification
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltRelativeConeTheorem
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.FloorProgramInputs
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.PushforwardRelativeCone
public import MMP.AlgebraicGeometry.Curves.RationalCurveImage
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.BoundedCurveClasses
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeExtremalRays
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward

/-!
# The cone theorem for projective lc fourfolds

Let `h : X ⟶ S` be a morphism of projective complex varieties, with `X` normal of dimension
four, and let `(X, B)` be a log canonical pair with effective rational boundary `B`. Put
`D = K_X + B`. Then:

* every `D`-negative extremal ray of the relative closed cone of curves `NE̅(X/S)` is spanned by
  the class of a rational curve `C` contracted by `h` with `0 < -(D · C) ≤ 8`;
* there are countably many such rays, and
  `NE̅(X/S) = NE̅(X/S)_{D ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]` with finite sums;
* for every ample Cartier divisor `A` on `X` and every `ε > 0`, only finitely many
  `D`-negative extremal rays `R` satisfy `(D + εA) · R < 0`;
* in particular the negative extremal rays are locally finite in the half-space `D < 0`, and
  if `D` is not nef over `S` then there is a `D`-negative extremal ray of `NE̅(X/S)`.

The proof passes to a crepant dlt modification `p : (W, B_W) ⟶ (X, B)`, applies the relative
cone theorem for dlt pairs on `W` over `S`, and pushes the rational curves forward to `X`. The
bounded `A`-degree of the curves gives finiteness of the rays in each region `D + εA < 0`.

## Main results

* `MMP.Fourfold.exists_relativeClosedConeOfCurves_eq_add_hull_of_isLogCanonicalPair`: the cone
  theorem for projective lc complex fourfolds.

## Implementation notes

The sum `∑ⱼ ℝ_{≥0} [Cⱼ]` over the negative extremal rays is the convex cone
`PointedCone.hull ℝ` spanned by the union of these rays, whose elements are the finite sums of
elements of the rays; the first assertion identifies each ray with `ℝ_{≥0} [C]`. The pairing
with `D` on `N₁(X/S)` is `MMP.Fourfold.QDivisor.relativeCurveForm`, which needs `D` to be
`ℚ`-Cartier; the theorem asserts this. The pairing with `D + εA` is that of `D` plus `ε` times the
degree of `𝒪_X(A)`. A ray `R` with `(D + εA) · R < 0` means `(D + εA) · u < 0` for `0 ≠ u ∈ R`.
Local finiteness in `D < 0` is stated as: every class `z` with `D · z < 0` has a neighbourhood
meeting only finitely many negative extremal rays. The boundary of an lc pair
(`MMP.Intersection.IsLogCanonicalPair`) has non-negative coefficients, so effectivity is part of
the hypothesis `hB`.

## References

* [OAI4] the fourfold source, *The projective complex fourfold lc cone theorem*.
* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Theorem 3.7.
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Pointwise Topology MMP.Mori MMP.Fourfold

namespace Proof_thm_mmp_projective_fourfold_lc_cone

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Convex cones -/

section Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A linear form nonnegative on a set is nonnegative on the convex cone it spans. -/
private theorem nonneg_of_mem_hull (α : V →ₗ[ℝ] ℝ) {S : Set V} (hS : ∀ g ∈ S, 0 ≤ α g)
    {z : V} (hz : z ∈ PointedCone.hull ℝ S) : 0 ≤ α z := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
  | smul a x _ hx =>
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    exact mul_nonneg a.2 hx

/-- In a ray `ℝ_{≥0} v`, every nonzero element spans the same ray. -/
private theorem ray_eq_of_mem {R : Set V} {v : V} (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
    {u : V} (hu : u ∈ R) (hu0 : u ≠ 0) : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • u = w} := by
  rw [hR] at hu ⊢
  obtain ⟨c, hc, rfl⟩ := hu
  have hc0 : c ≠ 0 := by rintro rfl; simp at hu0
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  ext w
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d / c, div_nonneg hd hc, by rw [smul_smul, div_mul_cancel₀ _ hc0]⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, mul_nonneg hd hc, by rw [smul_smul]⟩

/-- A linear form negative at one point of a ray is negative at every nonzero point of it. -/
private theorem neg_of_mem_ray (ℓ : V →ₗ[ℝ] ℝ) {R : Set V} {v : V}
    (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w}) {u : V} (hu : u ∈ R) (hℓu : ℓ u < 0) :
    ∀ w ∈ R, w ≠ 0 → ℓ w < 0 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hℓu
  rw [ray_eq_of_mem hR hu hu0]
  rintro _ ⟨c, hc, rfl⟩ hw
  have hc0 : c ≠ 0 := by rintro rfl; simp at hw
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) hℓu

/-- A finite sum of elements of a cone `N` lying in an extremal face of `N` has all its summands
in the face. -/
private theorem mem_of_sum_mem {N R : Set V} (hNadd : ∀ u ∈ N, ∀ v ∈ N, u + v ∈ N)
    (hN0 : (0 : V) ∈ N) (hR : IsExtremalFace ℝ N R) {ι : Type*} (s : Finset ι) (x : ι → V)
    (hx : ∀ i ∈ s, x i ∈ N) (hsum : ∑ i ∈ s, x i ∈ R) : ∀ i ∈ s, x i ∈ R := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has] at hsum
    have hsN : ∑ i ∈ s, x i ∈ N := by
      have : ∀ t : Finset ι, (∀ i ∈ t, x i ∈ N) → ∑ i ∈ t, x i ∈ N := by
        intro t
        induction t using Finset.induction_on with
        | empty => simpa using hN0
        | insert b t hbt iht =>
          intro ht
          rw [Finset.sum_insert hbt]
          exact hNadd _ (ht b (Finset.mem_insert_self _ _)) _
            (iht fun i hi => ht i (Finset.mem_insert_of_mem hi))
      exact this s fun i hi => hx i (Finset.mem_insert_of_mem hi)
    obtain ⟨ha, hs⟩ := hR.2.2.2 _ (hx a (Finset.mem_insert_self _ _)) _ hsN hsum
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ha
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)) hs i hi

/-- **A ray inside a finitely generated decomposition.** Let `R` be an extremal ray of a convex
cone `N`, on whose nonzero elements the linear form `μ` is negative. If
`N ⊆ N_{μ ≥ 0} + hull F` with `F ⊆ N`, then `R = ℝ_{≥0} g` for some `g ∈ F`. -/
private theorem exists_mem_eq_ray {N : PointedCone ℝ V} {R : Set V}
    (hR : IsExtremalRay ℝ (N : Set V) R) (μ : V →ₗ[ℝ] ℝ) (hμ : ∀ u ∈ R, u ≠ 0 → μ u < 0)
    {F : Set V} (hF : F ⊆ N)
    (hdec : (N : Set V) ⊆ {z | z ∈ N ∧ 0 ≤ μ z} + (PointedCone.hull ℝ F : Set V)) :
    ∃ g ∈ F, R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • g = w} := by
  classical
  obtain ⟨hface, v, hv0, hRv⟩ := hR
  have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨w, ⟨hwN, hwμ⟩, h, hh, hvwh⟩ := hdec (hface.1 hvR)
  obtain ⟨n, f, g, rfl⟩ := Submodule.mem_span_set'.mp hh
  have hterm : ∀ i ∈ Finset.univ, (f i • (g i : V)) ∈ (N : Set V) := fun i _ =>
    Submodule.smul_mem N (f i) (hF (g i).2)
  subst hvwh
  -- the summands all lie on `R`
  have hall : ∀ i ∈ (Finset.univ : Finset (Option (Fin n))),
      (Option.elim i w fun j => f j • (g j : V)) ∈ R := by
    refine mem_of_sum_mem (fun u hu v hv => N.add_mem hu hv) N.zero_mem hface _ _ ?_ ?_
    · rintro (_ | j) -
      · exact hwN
      · exact hterm j (Finset.mem_univ _)
    · rw [Fintype.sum_option]
      simpa using hvR
  have hw0 : w = 0 := by
    by_contra hw0
    exact absurd hwμ (not_le.mpr (hμ w (hall none (Finset.mem_univ _)) hw0))
  have hsum0 : ∑ i, f i • (g i : V) ≠ 0 := by
    simpa [hw0] using hv0
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum0
  have hiR : f i • (g i : V) ∈ R := hall (some i) (Finset.mem_univ _)
  have hf0 : (f i : ℝ) ≠ 0 := by
    intro h0
    apply hi
    rw [← Nonneg.coe_smul, h0, zero_smul]
  refine ⟨g i, (g i).2, ?_⟩
  rw [ray_eq_of_mem hRv hiR hi, ← Nonneg.coe_smul]
  ext u
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * f i, mul_nonneg hc (f i).2, by rw [smul_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c / f i, div_nonneg hc (f i).2, by rw [smul_smul, div_mul_cancel₀ _ hf0]⟩

end Convex

section Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V]

/-- Adding a ray to a closed set on which a continuous linear form `α` is nonnegative keeps it
closed, provided `α` is positive on the ray. -/
private theorem isClosed_add_hull_singleton (α : V →ₗ[ℝ] ℝ) (hα : Continuous α) {K : Set V}
    (hK : IsClosed K) (hKα : ∀ z ∈ K, 0 ≤ α z) {g : V} (hg : 0 < α g) :
    IsClosed (K + (PointedCone.hull ℝ {g} : Set V)) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  set T : ℝ := (α x + 1) / α g
  set S : Set V := (fun t : ℝ => t • g) '' Set.Icc 0 T
  have hS : IsCompact S := isCompact_Icc.image (continuous_id.smul continuous_const)
  have hKS : IsClosed (K + S) := hK.add_right_of_isCompact hS
  have hsub : K + S ⊆ K + (PointedCone.hull ℝ {g} : Set V) := by
    rintro _ ⟨a, ha, _, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨a, ha, t • g, ?_, rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨⟨t, ht.1⟩, rfl⟩
  refine hsub (hKS.closure_subset ?_)
  rw [mem_closure_iff] at hx ⊢
  intro o ho hxo
  have hU : IsOpen {y : V | α y < α x + 1} := isOpen_lt hα continuous_const
  obtain ⟨y, ⟨hyo, hyU⟩, a, ha, b, hb, rfl⟩ :=
    hx (o ∩ {y | α y < α x + 1}) (ho.inter hU) ⟨hxo, by simp⟩
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
  refine ⟨a + t • g, hyo, a, ha, (t : ℝ) • g, ⟨t, ⟨t.2, ?_⟩, rfl⟩, by
    simp only [Nonneg.coe_smul]⟩
  have h1 := hKα a ha
  have h2 : α (a + (t : ℝ) • g) < α x + 1 := by rwa [Nonneg.coe_smul]
  rw [map_add, map_smul, smul_eq_mul] at h2
  rw [le_div_iff₀ hg]
  linarith

/-- Adding a finitely generated cone, on whose generators `α` is positive, to a closed set on
which `α` is nonnegative keeps it closed. -/
private theorem isClosed_add_hull (α : V →ₗ[ℝ] ℝ) (hα : Continuous α) {K : Set V}
    (hK : IsClosed K) (hKα : ∀ z ∈ K, 0 ≤ α z) (F : Finset V) (hF : ∀ g ∈ F, 0 < α g) :
    IsClosed (K + (PointedCone.hull ℝ (F : Set V) : Set V)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.bot_coe]
    simpa [Set.add_singleton] using hK
  | insert g F _ ih =>
    have ih' := ih fun g' hg' => hF g' (Finset.mem_insert_of_mem hg')
    have e : ∀ a b c : Set V, a + (b + c) = a + c + b := fun a b c => by
      rw [add_comm b c, add_assoc]
    rw [Finset.coe_insert, PointedCone.hull, Submodule.span_insert, Submodule.coe_sup, e]
    refine isClosed_add_hull_singleton α hα ih' ?_ (hF g (Finset.mem_insert_self _ _))
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [map_add]
    exact add_nonneg (hKα a ha)
      (nonneg_of_mem_hull α (fun g' hg' => (hF g' (Finset.mem_insert_of_mem hg')).le) hb)

/-- **Absorbing rays, then closing up.** Let `N` be a closed convex cone, `ℓ` and `α`
continuous linear forms with `α ≥ 0` on `N`, and `g` a family in `N` with `α > 0` on it. If the
classes of a set `N₀` with `N = closure N₀` decompose as `N₀ ⊆ N_{ℓ ≥ 0} + hull g`, then for every
`ε > 0` with only finitely many `(ℓ + εα)`-negative members `F_ε` of the family,
`N ⊆ N_{ℓ + εα ≥ 0} + hull F_ε`. -/
private theorem subset_add_hull_of_finite {N : PointedCone ℝ V} (hN : IsClosed (N : Set V))
    {N₀ : Set V} (hN₀ : (N : Set V) ⊆ closure N₀) (ℓ α : V →ₗ[ℝ] ℝ) (hℓc : Continuous ℓ)
    (hαc : Continuous α) (hα : ∀ z ∈ N, 0 ≤ α z) {ι : Type*} (g : ι → V) (hg : ∀ j, g j ∈ N)
    (hgα : ∀ j, 0 < α (g j))
    (hdec : N₀ ⊆ {z | z ∈ N ∧ 0 ≤ ℓ z} + (PointedCone.hull ℝ (Set.range g) : Set V))
    {ε : ℝ} (hε : 0 < ε) (hfin : {x | ∃ j, g j = x ∧ ℓ x + ε * α x < 0}.Finite) :
    (N : Set V) ⊆ {z | z ∈ N ∧ 0 ≤ ℓ z + ε * α z} +
      (PointedCone.hull ℝ {x | ∃ j, g j = x ∧ ℓ x + ε * α x < 0} : Set V) := by
  classical
  set F := {x | ∃ j, g j = x ∧ ℓ x + ε * α x < 0}
  let P : PointedCone ℝ V :=
    { carrier := {z | z ∈ N ∧ 0 ≤ ℓ z + ε * α z}
      add_mem' := fun {a b} ha hb => ⟨N.add_mem ha.1 hb.1, by
        simp only [map_add]; nlinarith [ha.2, hb.2]⟩
      zero_mem' := ⟨N.zero_mem, by simp⟩
      smul_mem' := fun c z hz => ⟨Submodule.smul_mem N c hz.1, by
        change 0 ≤ ℓ ((c : ℝ) • z) + ε * α ((c : ℝ) • z)
        simp only [map_smul, smul_eq_mul]
        nlinarith [hz.2, c.2]⟩ }
  have hPcl : IsClosed (P : Set V) :=
    hN.inter (isClosed_le continuous_const (hℓc.add (continuous_const.mul hαc)))
  have hcl : IsClosed ((P : Set V) + (PointedCone.hull ℝ (hfin.toFinset : Set V) : Set V)) := by
    refine isClosed_add_hull α hαc hPcl (fun z hz => hα z hz.1) _ fun x hx => ?_
    obtain ⟨j, rfl, -⟩ := hfin.mem_toFinset.mp hx
    exact hgα j
  rw [hfin.coe_toFinset] at hcl
  refine hN₀.trans (closure_minimal (fun z hz => ?_) hcl)
  obtain ⟨a, ⟨haN, ha⟩, h, hh, rfl⟩ := hdec hz
  have hle : PointedCone.hull ℝ (Set.range g) ≤ P ⊔ PointedCone.hull ℝ F := by
    refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ?_)
    by_cases hj : ℓ (g j) + ε * α (g j) < 0
    · exact (le_sup_right : PointedCone.hull ℝ F ≤ _) (Submodule.subset_span ⟨j, rfl, hj⟩)
    · exact (le_sup_left : P ≤ _) ⟨hg j, le_of_not_gt hj⟩
  obtain ⟨p, hp, h', hh', rfl⟩ := Submodule.mem_sup.mp (hle hh)
  have haP : a ∈ P := ⟨haN, by nlinarith [hα a haN]⟩
  exact ⟨a + p, P.add_mem haP hp, h', hh', add_assoc _ _ _⟩

end Topology

/-! ### Crepancy as a pull-back -/

section Crepancy

universe u

/-- The order of `c ^ m * g⁻¹` along a point, for nonzero rational functions `c` and `g`. -/
private theorem ord_zpow_mul_inv {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y)
    {c g : Y.functionField} (hc : c ≠ 0) (hg : g ≠ 0) (m : ℤ) :
    Y.ord (c ^ m * g⁻¹) z = m * Y.ord c z - Y.ord g z := by
  rw [Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg), MMP.Mori.ord_zpow _ hc,
    ← zpow_neg_one, MMP.Mori.ord_zpow _ hg]
  ring

variable {k : Type u} [Field k] [PerfectField k] {X U : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]

/-- Coefficientwise crepancy: along a prime divisor `F` of `U`, the pull-back of a Cartier
multiple `E = m (K + B)` has coefficient `m (ord_F div(p^*ω) + Δ_F)` when `K = div(ω)`. -/
private theorem coeff_pullback_eq {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {p : U ⟶ X}
    [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {m : ℕ} (hm0 : 0 < m) {E : Divisor X}
    (hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B)) (hEc : E.IsCartier)
    {hB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ E.supp}
    {Dp : Divisor U} (hDp : E.IsPullback p hB Dp) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (F : MMP.Mori.PrimeDivisor U) :
    (Dp.coeff F : ℚ) =
      m * ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F + Δ.coeff F) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hK := (hcrep F).2.1
  obtain rfl : n = n' := by exact_mod_cast hK.1.symm.trans hK'.1
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨U, p, hY, hp, F⟩ with hD
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hX hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      U.ord (functionFieldMap p ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨V, hxV, φ, hφ⟩ := hEc (p F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X) with hg_def
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hKcoeff : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    intro Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    refine ⟨NΓ, ?_, ?_⟩
    · rw [← hωK Γ, hNΓ 1 ω hω0]
      simp [hc_def]
    · rw [hNΓ _ τ hτ0, hτr, hc''_def, ord_zpow_mul_inv _ hc hg]
  have hgord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ V).Nonempty →
      X.ord g Γ.genericPoint = E.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    have : Γ.component = Z0 :=
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [this]
  have hCq : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (E.coeff Γ : ℚ) = m * (K.coeff Γ + B.coeff Γ) := by
    intro Γ
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hE
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgen : GeneratesOn B m V τ := by
    refine ⟨hτ0, fun Γ hΓ => ?_⟩
    obtain ⟨NΓ, h1, h2⟩ := hKcoeff Γ
    have h3 := hgord Γ hΓ
    have h1' : (K.coeff Γ : ℚ) = X.ord c Γ.genericPoint + NΓ := by exact_mod_cast h1
    have h2' : (Γ.ordForm τ : ℚ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint
        + m * NΓ := by exact_mod_cast h2
    have h3' : (X.ord g Γ.genericPoint : ℚ) = E.coeff Γ := by exact_mod_cast h3
    linear_combination h2' - hCq Γ - h3' - (m : ℚ) * h1'
  have hKY : (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F =
      U.ord (functionFieldMap p c) F.genericPoint + N' := by
    have h := hb 1 ω hω0
    have e : D.ordPullback ω = (divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F := by
      rw [coeff_divisorOfForm]
      rfl
    rw [← e, h]
    simp [hc_def]
  have hcoeff : Dp.coeff F = U.ord (functionFieldMap p g) F.genericPoint :=
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hDp hφ F hxV Z0
  have hgY : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap p c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * U.ord (functionFieldMap p c) F.genericPoint
      - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀, ord_zpow_mul_inv _ hcY hgY]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hdisc : IsDiscrepancy sX n K B D
      ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F - Dp.coeff F / m) := by
    refine ⟨hX, hK, m, hm0, ⟨E, hE, hEc⟩, V, hxV, τ, hgen, ?_⟩
    have e1 : (D.ordPullback τ : ℚ) = m * U.ord (functionFieldMap p c) F.genericPoint
        - U.ord (functionFieldMap p g) F.genericPoint + m * N' := by exact_mod_cast hordτ
    have e2 : ((divisorOfForm (pullbackRationalPluriForms sX p ω)).coeff F : ℚ) =
        U.ord (functionFieldMap p c) F.genericPoint + N' := by exact_mod_cast hKY
    have e3 : (Dp.coeff F : ℚ) = U.ord (functionFieldMap p g) F.genericPoint := by
      exact_mod_cast hcoeff
    rw [e1, e2, e3]
    field_simp
    ring
  have heq := IsDiscrepancy.eq (hcrep F) hdisc
  field_simp at heq
  linear_combination heq

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- **Crepancy as a pull-back.** If `Δ` is the crepant boundary of `(X, B)` on `U` and
`K = div(ω)`, then `div(p^*ω) + Δ = p^*(K + B)`. -/
private theorem isPullback_divisorOfForm_add {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX)
    {p : U ⟶ X} [IsDominant p] [LocallyOfFiniteType (p ≫ sX)]
    (hY : IsNormalVariety k (p ≫ sX)) (hp : IsBirationalMorphism p) {n n' : ℕ} {K : Divisor X}
    (hK' : K.IsCanonicalDivisor sX n') {B : QDivisor X} {Δ : QDivisor U}
    (hcrep : IsCrepantBoundary sX n K B p hY hp Δ) {ω : RationalPluriForms sX n' 1}
    (hω0 : ω ≠ 0) (hωK : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.ordForm ω = K.coeff Γ)
    (hLB : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉
      (Divisor.toQDivisor K + B).supp) :
    (Divisor.toQDivisor K + B).IsPullback p hLB
      (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + Δ) := by
  intro m hm D hD hDc
  have hB' : ∀ Z : irreducibleComponents U, p (componentGenericPoint U Z) ∉ D.supp :=
    fun Z hZ => hLB Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ)
  refine ⟨D.pullback hDc hB', ?_, Divisor.isPullback_pullback hDc hB'⟩
  ext F
  have h := coeff_pullback_eq hX hY hp hK' hcrep hm hD hDc
    (Divisor.isPullback_pullback hDc hB') hω0 hωK F
  simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add, zsmul_eq_mul,
    Divisor.coeff_toQDivisor, Int.cast_natCast]
  exact h

end Crepancy

/-! ### Curve forms -/

section CurveForm

variable {k : Type} [Field k] {X S : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- The pairing of a `ℚ`-Cartier `ℚ`-divisor with `N₁(X/S)` is continuous. -/
private theorem continuous_relativeCurveForm (sX : X ⟶ Spec (.of k)) (f : X ⟶ S)
    (D : QDivisor X) (h : D.IsQCartier) :
    Continuous (QDivisor.relativeCurveForm sX f D h) := by
  unfold QDivisor.relativeCurveForm
  rw [Finsupp.sum, LinearMap.coe_sum, Finset.sum_fn]
  refine continuous_finsetSum _ fun E _ => ?_
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  rw [LinearMap.coe_smul]
  exact (RelativeNumericalCurveClasses.continuous_degree sX f _).const_smul _

/-- The pairing of a `ℚ`-Cartier `ℚ`-divisor with the class of a contracted curve is its
intersection number with the curve. -/
private theorem relativeCurveForm_relativeClass {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    (f : X ⟶ S) (D : QDivisor X) (h : D.IsQCartier) (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    QDivisor.relativeCurveForm sX f D h (C.relativeClass f hC) =
      (D.intersectionNumber k sX C.ι C.dim_le h : ℝ) := by
  rw [QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply]
  exact MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX D h C

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor `D` is `1 / m_D` times the degree of
`𝒪_X(m_D D)`. -/
private theorem curveForm_apply (sX : X ⟶ Spec (.of k)) (D : QDivisor X) (h : D.IsQCartier)
    (z : NumericalCurveClasses sX) :
    haveI :=
      (Divisor.mem_cartierSubgroup.mp (D.cartierIndexSMul h).2).isInvertibleModule_divisorialSheaf
    QDivisor.curveForm sX D h z = (1 / (D.cartierIndex h : ℝ)) *
      NumericalCurveClasses.degree sX (D.cartierIndexSMul h : Divisor X).divisorialSheaf z := by
  rw [QDivisor.curveForm, QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single_index]
  · rw [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    rfl
  · simp

/-- A `ℚ`-Cartier `ℚ`-divisor `D` is nef over `S` once `(D · C) ≥ 0` for every curve contracted
to a point of `S`. -/
private theorem isRelativelyNef_of_forall {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    (f : X ⟶ S) (D : QDivisor X) (h : D.IsQCartier)
    (hC : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ D.intersectionNumber k sX C.ι C.dim_le h) :
    QDivisor.IsRelativelyNef sX f D := by
  refine ⟨h, fun C hCf => ?_⟩
  have key := hC C hCf
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    Finsupp.sum_single_index (by simp)]
  rw [QDivisor.intersectionNumber] at key
  have hm : (0 : ℚ) < D.cartierIndex h := by exact_mod_cast QDivisor.cartierIndex_pos h
  have h1 : (0 : ℚ) ≤ ((QDivisor.isCartierDivisor_cartierIndex_smul h).toDivisor.degreeOn k sX C.ι
      C.dim_le (QDivisor.isCartierDivisor_cartierIndex_smul h).isCartier_toDivisor : ℚ) := by
    have := mul_nonneg key hm.le
    rwa [div_mul_cancel₀ _ hm.ne'] at this
  have hm' : (0 : ℝ) < (D.cartierIndex h : ℝ) := by exact_mod_cast hm
  simp only [smul_eq_mul, mul_one]
  push_cast
  exact mul_nonneg (by positivity) (by exact_mod_cast h1)

end CurveForm

/-! ### The crepant projection formula -/

section Projection

variable {X W : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- **The crepant projection formula on one curve.** If `Δ_W` is the crepant boundary of
`(X, B)` on the birational model `p : W ⟶ X` and `K_W` is a canonical divisor of `W`, then for
every curve `Γ ⊆ W`, `(K + B) · p_*Γ = (K_W + Δ_W) · Γ`. -/
private theorem curveForm_pushforward_cycle (hXv : IsNormalVariety ℂ sX) {p : W ⟶ X}
    [IsDominant p] (hW : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {ΔW : QDivisor W}
    (hcrep : IsCrepantBoundary sX n K B p hW hp ΔW) (hD : (Divisor.toQDivisor K + B).IsQCartier)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (p ≫ sX) n)
    (hDW : (Divisor.toQDivisor KW + ΔW).IsQCartier) (Γ : ProperCurve (p ≫ sX)) :
    haveI : QuasiCompact (p ≫ sX) := hW.1.toQuasiCompact
    QDivisor.curveForm sX (Divisor.toQDivisor K + B) hD
        (OneCycle.numericalClass sX (OneCycle.pushforward ℝ (p ≫ sX) sX p (Γ.cycle ℝ))) =
      ((Divisor.toQDivisor KW + ΔW).intersectionNumber ℂ (p ≫ sX) Γ.ι Γ.dim_le hDW : ℝ) := by
  haveI : QuasiCompact (p ≫ sX) := hW.1.toQuasiCompact
  haveI : LocallyOfFiniteType (p ≫ sX) := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXv hK
  have hLB : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor K + B).supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hpb := isPullback_divisorOfForm_add hXv hW hp hK hcrep hω0 hωK hLB
  set m := (Divisor.toQDivisor K + B).cartierIndex hD with hm_def
  have hm := QDivisor.cartierIndex_pos hD
  set E : Divisor X := ((Divisor.toQDivisor K + B).cartierIndexSMul hD : Divisor X) with hE_def
  have hEc : E.IsCartier :=
    Divisor.mem_cartierSubgroup.mp ((Divisor.toQDivisor K + B).cartierIndexSMul hD).2
  have hE : Divisor.toQDivisor E = (m : ℤ) • (Divisor.toQDivisor K + B) :=
    QDivisor.toQDivisor_cartierIndexSMul _ hD
  obtain ⟨D', hD', hpbE⟩ := hpb m hm E hE hEc
  have hD'c := hpbE.isCartier hEc
  haveI := hEc.isInvertibleModule_divisorialSheaf
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  -- the left side is `(1 / m) deg_Γ p^* 𝒪_X(E) = (1 / m) deg_Γ 𝒪_W(D')`
  rw [curveForm_apply, NumericalCurveClasses.degree_numericalClass, OneCycle.pushforward_cycle,
    ProperCurve.degree_pushforward_eq_degree_pullback p rfl Γ E.divisorialSheaf]
  have h1 : Γ.degree ℂ ((Scheme.Modules.pullback p).obj E.divisorialSheaf) =
      D'.degreeOn ℂ (p ≫ sX) Γ.ι Γ.dim_le hD'c := by
    rw [← ProperCurve.degree_divisorialSheaf Γ D' hD'c]
    exact (degreeOn_eq_of_iso ℂ (p ≫ sX) Γ.ι Γ.dim_le (hpbE.divisorialSheafIso (hBc := hEc))).symm
  rw [h1]
  -- the right side, through the canonical divisor `div(p^*ω)`
  set KW' := divisorOfForm (pullbackRationalPluriForms sX p ω)
  have hW' : (Divisor.toQDivisor KW' + ΔW).IsQCartier := hpb.isQCartier hD
  have h2 := QDivisor.intersectionNumber_eq_of_smul ℂ (p ≫ sX) Γ.ι Γ.dim_le _ hW' hm D' hD'c hD'
  have hne := pullbackRationalPluriForms_ne_zero hXv hp hK.1 hω0
  have hlin : KW'.LinearlyEquivalent KW := by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hW hKW hne
  obtain ⟨_, _, _, h3⟩ := MMP.Flips.isIntersectionNumber_add_of_linearlyEquivalent
    (sX := p ≫ sX) (C := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({Γ.point} : Set W)))
    (x := (Divisor.toQDivisor KW' + ΔW).intersectionNumber ℂ (p ≫ sX) Γ.ι Γ.dim_le hW') hlin
    ⟨inferInstance, Γ.dim_le, hW', rfl⟩
  change (Divisor.toQDivisor KW + ΔW).intersectionNumber ℂ (p ≫ sX) Γ.ι Γ.dim_le _ = _ at h3
  rw [show (Divisor.toQDivisor KW + ΔW).intersectionNumber ℂ (p ≫ sX) Γ.ι Γ.dim_le hDW =
      (Divisor.toQDivisor KW' + ΔW).intersectionNumber ℂ (p ≫ sX) Γ.ι Γ.dim_le hW' from h3, h2]
  push_cast
  ring

/-- The image of a curve contracted by `p ≫ h` under a closed map `p` is contracted by `h`. -/
private theorem isContractedBy_image {S : Scheme.{0}} {h : X ⟶ S} {p : W ⟶ X} [IsProper p]
    {Γ : ProperCurve (p ≫ sX)} (hΓ : Γ.IsContractedBy (p ≫ h)) (hC : IsProperCurve sX (p Γ.point)) :
    (⟨p Γ.point, hC⟩ : ProperCurve sX).IsContractedBy h := by
  intro x hx
  have hsub : closure ({p Γ.point} : Set X) ⊆ p '' closure ({Γ.point} : Set W) :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨Γ.point, subset_closure rfl, rfl⟩)
      (p.isClosedMap _ isClosed_closure)
  obtain ⟨y, hy, rfl⟩ := hsub hx
  have := hΓ y hy
  simpa only [Scheme.Hom.comp_apply] using this

/-- The push-forward of a curve contracted by `p ≫ h` is a relative 1-cycle over `S`. -/
private theorem pushforward_mem_relativeOneCycles {S : Scheme.{0}} {h : X ⟶ S} {p : W ⟶ X}
    [IsProper p] {Γ : ProperCurve (p ≫ sX)} (hΓ : Γ.IsContractedBy (p ≫ h)) :
    OneCycle.pushforward ℝ (p ≫ sX) sX p (Γ.cycle ℝ) ∈ relativeOneCycles sX h := by
  classical
  rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint]
  split_ifs with hC
  · exact Finsupp.single_mem_supported ℝ _ (isContractedBy_image hΓ hC)
  · exact zero_mem _

/-- Two linear forms on the relative 1-cycles agree once they agree on the contracted curves. -/
private theorem linearMap_ext_relativeOneCycles {k : Type} [Field k] {Y T : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ T} {g₁ g₂ : relativeOneCycles sY f →ₗ[ℝ] ℝ}
    (hg : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy f),
      g₁ ⟨C.cycle ℝ, C.cycle_mem_relativeOneCycles hC⟩ =
        g₂ ⟨C.cycle ℝ, C.cycle_mem_relativeOneCycles hC⟩) : g₁ = g₂ := by
  classical
  let e : relativeOneCycles sY f ≃ₗ[ℝ] ({C : ProperCurve sY | C.IsContractedBy f} →₀ ℝ) :=
    Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ) {C : ProperCurve sY | C.IsContractedBy f}
  suffices hs : g₁ ∘ₗ e.symm.toLinearMap = g₂ ∘ₗ e.symm.toLinearMap by
    ext Z
    simpa using LinearMap.congr_fun hs (e Z)
  refine Finsupp.lhom_ext fun a b => ?_
  have he : e.symm (Finsupp.single a b) =
      b • ⟨a.1.cycle ℝ, a.1.cycle_mem_relativeOneCycles a.2⟩ := by
    apply Subtype.ext
    change ((Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ)
      {C : ProperCurve sY | C.IsContractedBy f}).symm (Finsupp.single a b) :
        ProperCurve sY →₀ ℝ) = _
    rw [Finsupp.supportedEquivFinsupp_symm_single]
    simp [ProperCurve.cycle]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, map_smul, hg a.1 a.2]

/-- **The crepant projection formula on `N₁(W/S)`.** For a crepant model `p : (W, Δ_W) ⟶ (X, B)`
over `S` and the push-forward `φ = p_* : N₁(W/S) ⟶ N₁(X/S)`,
`((K + B) · φ z) = ((K_W + Δ_W) · z)`. -/
private theorem relativeCurveForm_comp_eq {S : Scheme.{0}} (h : X ⟶ S)
    (hXv : IsNormalVariety ℂ sX) {p : W ⟶ X} [IsDominant p] [IsProper p]
    (hW : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {ΔW : QDivisor W}
    (hcrep : IsCrepantBoundary sX n K B p hW hp ΔW) (hD : (Divisor.toQDivisor K + B).IsQCartier)
    {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (p ≫ sX) n)
    (hDW : (Divisor.toQDivisor KW + ΔW).IsQCartier)
    (φ : RelativeNumericalCurveClasses (p ≫ sX) (p ≫ h) →ₗ[ℝ] RelativeNumericalCurveClasses sX h)
    (hφ : ∀ (Z : relativeOneCycles (p ≫ sX) (p ≫ h)) (Z' : relativeOneCycles sX h),
      (Z' : OneCycle ℝ sX) = OneCycle.pushforward ℝ (p ≫ sX) sX p Z →
        φ (relativeNumericalClass (p ≫ sX) (p ≫ h) Z) = relativeNumericalClass sX h Z')
    (z : RelativeNumericalCurveClasses (p ≫ sX) (p ≫ h)) :
    QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD (φ z) =
      QDivisor.relativeCurveForm (p ≫ sX) (p ≫ h) (Divisor.toQDivisor KW + ΔW) hDW z := by
  haveI : QuasiCompact (p ≫ sX) := hW.1.toQuasiCompact
  suffices hs : QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD ∘ₗ φ =
      QDivisor.relativeCurveForm (p ≫ sX) (p ≫ h) (Divisor.toQDivisor KW + ΔW) hDW from
    LinearMap.congr_fun hs z
  refine Submodule.linearMap_qext _ (linearMap_ext_relativeOneCycles fun Γ hΓ => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
  change QDivisor.relativeCurveForm sX h _ hD
      (φ (relativeNumericalClass (p ≫ sX) (p ≫ h) ⟨Γ.cycle ℝ, _⟩)) =
    QDivisor.relativeCurveForm (p ≫ sX) (p ≫ h) _ hDW (Γ.relativeClass (p ≫ h) hΓ)
  rw [hφ _ ⟨_, pushforward_mem_relativeOneCycles hΓ⟩ rfl,
    relativeCurveForm_relativeClass, QDivisor.relativeCurveForm_eq_comp, LinearMap.comp_apply]
  exact curveForm_pushforward_cycle hXv hW hp hK hcrep hD hKW hDW Γ

end Projection

/-! ### Degrees of an ample divisor -/

section Ample

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- A projective variety carries a Cartier divisor whose sheaf is ample. -/
private theorem exists_isAmple_cartierSheaf (hX : MMP.Mori.IsProjectiveVariety ℂ sX) :
    ∃ M : X.CartierDivisor,
      Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M) := by
  haveI : IsIntegral X := hX.toIsIntegral
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hX
  obtain ⟨M, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf H
  exact ⟨M, (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp
    ((Stacks.AmpleBridge.isAmple_iff_isAmple X H).mpr hHa)⟩

/-- Isomorphic invertible sheaves have the same degree form on `N₁(X/S)`. -/
private theorem relativeDegree_eq_of_iso (h : X ⟶ S) {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    RelativeNumericalCurveClasses.degree sX h L = RelativeNumericalCurveClasses.degree sX h L' := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  change OneCycle.degree ℝ sX L Z = OneCycle.degree ℝ sX L' Z
  rw [OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e)

/-- An ample Cartier divisor has positive degree on every contracted curve. -/
private theorem relativeDegree_pos (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (h : X ⟶ S)
    (M : X.CartierDivisor) (hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M))
    (C : ProperCurve sX) (hC : C.IsContractedBy h) :
    0 < RelativeNumericalCurveClasses.degree sX h (MMP.CartierDivisor.sheaf M)
      (C.relativeClass h hC) := by
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  change 0 < OneCycle.degree ℝ sX _ (C.cycle ℝ)
  rw [OneCycle.degree_cycle]
  exact_mod_cast MMP.Threefold.Mori.degreeOn_cartierSheaf_pos_of_isAmple hX.toIsVariety M hM C

/-- An ample Cartier divisor has nonnegative degree on `NE̅(X/S)`. -/
private theorem relativeDegree_nonneg (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (h : X ⟶ S)
    (M : X.CartierDivisor) (hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M))
    {z : RelativeNumericalCurveClasses sX h} (hz : z ∈ relativeClosedConeOfCurves sX h) :
    0 ≤ RelativeNumericalCurveClasses.degree sX h
      (MMP.CartierDivisor.sheaf M) z := by
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_const
    (RelativeNumericalCurveClasses.continuous_degree sX h _)) hz
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨C, hC⟩, rfl⟩ := hx
    exact (relativeDegree_pos hX h M hM C hC).le
  | zero => simp
  | add x y _ _ hx hy =>
    change 0 ≤ RelativeNumericalCurveClasses.degree sX h _ (x + y)
    rw [map_add]
    exact add_nonneg hx hy
  | smul a x _ hx =>
    change 0 ≤ RelativeNumericalCurveClasses.degree sX h _ ((a : ℝ) • x)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg a.2 hx

/-- **Bounded classes.** Only finitely many classes of contracted curves have bounded degree
against an ample Cartier divisor: `N₁(X/S) → N₁(X)` is injective, and in `N₁(X)` the classes of
effective integral cycles of bounded ample degree are finitely many. -/
private theorem finite_relativeClass_degree_le [hXp : MMP.Mori.IsProjectiveVariety ℂ sX]
    (h : X ⟶ S) (M : X.CartierDivisor)
    (hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M)) (c : ℝ) :
    {z : RelativeNumericalCurveClasses sX h | ∃ (C : ProperCurve sX) (hC : C.IsContractedBy h),
      C.relativeClass h hC = z ∧
        RelativeNumericalCurveClasses.degree sX h (MMP.CartierDivisor.sheaf M) z ≤
          c}.Finite := by
  have hS := (MMP.Mori.isCompact_closedConeOfCurves_inter_le_and_finite sX M hM
    (max c 1)).2
  have hinj : Function.Injective (relativeToAbsolute sX h) :=
    (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX h).2 _
      (isNaturalRelativeMap_relativeToAbsolute sX h)
  refine (hS.preimage hinj.injOn).subset ?_
  rintro _ ⟨C, hC, rfl, hc⟩
  refine ⟨C.cycle ℤ, fun D => ?_, ?_, ?_⟩
  · classical
    unfold ProperCurve.cycle
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num
  · simp only [ProperCurve.cycle, Finsupp.mapRange_single, Int.cast_one]
    rfl
  · rw [NumericalCurveClasses.intersectionNumber_ofCartier]
    exact hc.trans (le_max_left _ _)

end Ample

/-! ### The decomposition through a crepant dlt modification -/

/-- **The curves of the cone theorem.** For a projective lc fourfold `(X, B)` over `S` there is a
countable family of rational curves `Cⱼ ⊆ X` contracted to points of `S`, with
`0 < -((K + B) · Cⱼ) ≤ 8`, such that every class of the cone of curves of `X` over `S` lies in
`NE̅(X/S)_{K + B ≥ 0} + ∑ⱼ ℝ_{≥0} [Cⱼ]`. The curves are the images of those of the dlt cone
theorem on a crepant dlt modification. -/
private theorem exists_curves_subset_add_hull
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sS : S ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (h : X ⟶ S) (hh : h ≫ sS = sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (hD : (Divisor.toQDivisor K + B).IsQCartier) :
    ∃ (ι : Type) (_ : Countable ι) (C : ι → ProperCurve sX) (hC : ∀ j, (C j).IsContractedBy h),
      (∀ j, IsRationalCurve sX
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({(C j).point} : Set X)))) ∧
      (∀ j, 0 < -QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
          ((C j).relativeClass h (hC j)) ∧
        -QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
          ((C j).relativeClass h (hC j)) ≤ 8) ∧
      (relativeConeOfCurves sX h : Set (RelativeNumericalCurveClasses sX h)) ⊆
        {z | z ∈ relativeClosedConeOfCurves sX h ∧
          0 ≤ QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD z} +
        (PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass h (hC j)) :
          Set (RelativeNumericalCurveClasses sX h)) := by
  classical
  obtain ⟨W, _, _, _, p, hp, hWq, ΔW, hpproj, hdlt, hcrepall, -⟩ :=
    MMP.Fourfold.projectiveFloorProgramInputs_four.exists_crepant_dltModification sX hX
      (by rw [hdim]; rfl) hB
  have hcrep := hcrepall K hK
  have hXv : IsNormalVariety ℂ sX := ⟨hX.toIsVariety, inferInstance⟩
  have hWv : IsNormalVariety ℂ (p ≫ sX) := hWq.1
  haveI : IsProper p := isProper_of_isProjectiveMorphism _ hpproj
  haveI : IsDominant p := hp.isDominant
  haveI : QuasiCompact (p ≫ sX) := hWv.1.toQuasiCompact
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  haveI : IsSeparated sX := hX.toIsVariety.toIsSeparated
  have hpX : IsProjectiveMorphism sX := ((MMP.Mori.isProjectiveVariety_iff ℂ sX).1 hX).2
  have hWp : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) :=
    (MMP.Mori.isProjectiveVariety_iff ℂ _).2 ⟨hWv.1, IsProjectiveMorphism.comp hpproj hpX⟩
  haveI : Surjective p := ⟨fun x => by
    have : Set.range p = Set.univ := by
      rw [← p.isClosedMap.isClosed_range.closure_eq]; exact p.denseRange.closure_range
    rw [← Set.mem_range, this]; trivial⟩
  have hdimW : topologicalKrullDim W = (4 : ℕ) := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp, hdim]
    rfl
  obtain ⟨KW, hKW⟩ := MMP.Mori.exists_isCanonicalDivisor (p ≫ sX) hWv hdimW
  have hdltM : MMP.Mori.IsDltPair (p ≫ sX) 4 KW ΔW :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (p ≫ sX) hKW ΔW).1 hdlt
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX := hX
  haveI : MMP.Mori.IsProjectiveVariety ℂ sS := hS
  haveI : MMP.Mori.IsProjectiveVariety ℂ (p ≫ sX) := hWp
  have hπW : (p ≫ h) ≫ sS = p ≫ sX := by rw [Category.assoc, hh]
  obtain ⟨ι, hι, Γ, hΓ, hrat, hbd, heq⟩ :=
    hdltM.exists_relativeClosedConeOfCurves_eq_add_hull sS (p ≫ h) hπW hWq
  obtain ⟨φ, hφ, -, hmap, himg, -, -⟩ :=
    MMP.Mori.exists_relativeNumericalPushforward_of_surjective hWp hX hS hπW hh (p := p) rfl
  set ℓX := QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
  set ℓW := QDivisor.relativeCurveForm (p ≫ sX) (p ≫ h) (Divisor.toQDivisor KW + ΔW)
    hdltM.1.2.2
  have hℓ : ∀ z, ℓX (φ z) = ℓW z :=
    relativeCurveForm_comp_eq h hXv hWv hp hK hcrep hD hKW hdltM.1.2.2 φ hφ
  -- the image of each `Γⱼ` is a proper curve, since `K_W + Δ_W` is negative on `Γⱼ`
  have hφΓ : ∀ j, φ ((Γ j).relativeClass (p ≫ h) (hΓ j)) =
      relativeNumericalClass sX h ⟨_, pushforward_mem_relativeOneCycles (hΓ j)⟩ :=
    fun j => hφ _ _ rfl
  have hprop : ∀ j, IsProperCurve sX (p (Γ j).point) := by
    intro j
    by_contra hnp
    have h0' : OneCycle.pushforward ℝ (p ≫ sX) sX p ((Γ j).cycle ℝ) = 0 := by
      rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dif_neg hnp]
    have h0 : (⟨_, pushforward_mem_relativeOneCycles (hΓ j)⟩ : relativeOneCycles sX h) = 0 :=
      Subtype.ext h0'
    have := hℓ ((Γ j).relativeClass (p ≫ h) (hΓ j))
    rw [hφΓ j, h0, map_zero, map_zero] at this
    linarith [(hbd j).1]
  let C : ι → ProperCurve sX := fun j => ⟨p (Γ j).point, hprop j⟩
  have hC : ∀ j, (C j).IsContractedBy h := fun j => isContractedBy_image (hΓ j) (hprop j)
  let d : ι → ℕ := fun j => residueFieldDegree p (Γ j).point
  have hφC : ∀ j, φ ((Γ j).relativeClass (p ≫ h) (hΓ j)) =
      (d j : ℝ) • (C j).relativeClass h (hC j) := by
    intro j
    have e1 : OneCycle.pushforward ℝ (p ≫ sX) sX p ((Γ j).cycle ℝ) =
        (d j : ℝ) • (C j).cycle ℝ := by
      rw [OneCycle.pushforward_cycle, cyclePushforwardOfPoint, dif_pos (hprop j)]
      simp [ProperCurve.cycle, C, d]
    rw [hφΓ j, ProperCurve.relativeClass, ← map_smul]
    congr 1
    exact Subtype.ext e1
  have hℓC : ∀ j, ℓW ((Γ j).relativeClass (p ≫ h) (hΓ j)) =
      (d j : ℝ) * ℓX ((C j).relativeClass h (hC j)) := by
    intro j
    rw [← hℓ, hφC j, map_smul, smul_eq_mul]
  have hhull : ∀ b ∈ PointedCone.hull ℝ
      (Set.range fun j => (Γ j).relativeClass (p ≫ h) (hΓ j)),
      φ b ∈ PointedCone.hull ℝ (Set.range fun j => (C j).relativeClass h (hC j)) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [hφC j, ← Nonneg.mk_smul _ (Nat.cast_nonneg (d j))]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [← Nonneg.coe_smul, map_smul, Nonneg.coe_smul]
      exact Submodule.smul_mem _ a hx
  refine ⟨ι, hι, C, hC, fun j => ?_, fun j => ?_, ?_⟩
  · -- the image of a rational curve is rational
    have hnc : ¬ (p.base '' ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(Γ j).point} : Set W))).support : Set W)).Subsingleton := by
      intro hsub
      have hmem : ∀ x ∈ closure ({(Γ j).point} : Set W), x ∈ ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({(Γ j).point} : Set W))).support : Set W) := fun x hx => by
        rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      refine ProperCurve.not_isProperCurve_of_forall_eq p (Γ j) (y := p (Γ j).point)
        (fun z => ?_) (hprop j)
      rw [Scheme.Hom.comp_apply]
      exact hsub ⟨_, hmem _ (by rw [← (Γ j).range_ι]; exact ⟨z, rfl⟩), rfl⟩
        ⟨_, hmem _ (subset_closure rfl), rfl⟩
    have := IsRationalCurve.ker_subschemeι_comp (sY := sX) (f := p) rfl (hrat j) hnc
    rwa [show (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(Γ j).point} : Set W))).subschemeι ≫ p = (Γ j).ι ≫ p from rfl,
      ProperCurve.ker_comp] at this
  · -- the length bound, through `p_*[Γⱼ] = dⱼ [Cⱼ]`
    obtain ⟨h1, h2⟩ := hbd j
    rw [hℓC j] at h1 h2
    have hd0 : d j ≠ 0 := by
      rintro h0
      simp [h0] at h1
    have hd1 : (1 : ℝ) ≤ d j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
    have hpos : 0 < -ℓX ((C j).relativeClass h (hC j)) := by nlinarith
    refine ⟨hpos, ?_⟩
    push_cast at h2
    nlinarith
  · -- every curve class of `X` over `S` is a push-forward
    intro z hz
    rw [SetLike.mem_coe, ← hmap] at hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    have hw' : w ∈ (relativeClosedConeOfCurves (p ≫ sX) (p ≫ h) : Set _) := subset_closure hw
    rw [heq] at hw'
    obtain ⟨a, ⟨haN, ha⟩, b, hb, rfl⟩ := hw'
    refine ⟨φ a, ⟨himg ⟨a, haN, rfl⟩, by rw [hℓ]; exact ha⟩, φ b, ?_, by
      simp only [LinearMap.restrictScalars_apply, map_add]⟩
    exact hhull b hb

/-! ### The cone theorem -/

/-- The `D`-negative rays meeting the region `D + εA < 0`, for an ample Cartier divisor `A`, are
among the rays of the curves `Cⱼ`. -/
private theorem finite_rays {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    [MMP.Mori.IsProjectiveVariety ℂ sX] (h : X ⟶ S) {D : QDivisor X} (hD : D.IsQCartier)
    {ι : Type} (C : ι → ProperCurve sX) (hC : ∀ j, (C j).IsContractedBy h)
    (hpos : ∀ j, 0 < -QDivisor.relativeCurveForm sX h D hD ((C j).relativeClass h (hC j)))
    (hbd : ∀ j, -QDivisor.relativeCurveForm sX h D hD ((C j).relativeClass h (hC j)) ≤ 8)
    (hray : ∀ R, IsNegativeRelativeExtremalRayOf sX h D R →
      ∃ j, R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • (C j).relativeClass h (hC j) = w})
    (M : X.CartierDivisor) (hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M))
    {ε : ℝ} (hε : 0 < ε) :
    {R : Set (RelativeNumericalCurveClasses sX h) | IsNegativeRelativeExtremalRayOf sX h D R ∧
      ∀ u ∈ R, u ≠ 0 → QDivisor.relativeCurveForm sX h D hD u +
        ε * RelativeNumericalCurveClasses.degree sX h
          (MMP.CartierDivisor.sheaf M) u < 0}.Finite := by
  set ℓ := QDivisor.relativeCurveForm sX h D hD
  set α := RelativeNumericalCurveClasses.degree sX h (MMP.CartierDivisor.sheaf M)
  have hF : {x | ∃ j, (C j).relativeClass h (hC j) = x ∧ ℓ x + ε * α x < 0}.Finite := by
    refine (finite_relativeClass_degree_le h M hM (8 / ε)).subset ?_
    rintro _ ⟨j, rfl, hj⟩
    refine ⟨C j, hC j, rfl, ?_⟩
    rw [le_div_iff₀ hε]
    nlinarith [hbd j]
  refine (hF.image fun x => {w | ∃ c : ℝ, 0 ≤ c ∧ c • x = w}).subset ?_
  rintro R ⟨hR, hneg⟩
  obtain ⟨j, hj⟩ := hray R hR
  have hjR : (C j).relativeClass h (hC j) ∈ R := by rw [hj]; exact ⟨1, zero_le_one, one_smul _ _⟩
  have hj0 : (C j).relativeClass h (hC j) ≠ 0 := by
    intro h0
    have := hpos j
    rw [h0, map_zero, neg_zero] at this
    exact lt_irrefl _ this
  exact ⟨_, ⟨j, rfl, hneg _ hjR hj0⟩, hj.symm⟩

private theorem solution :
    ∀ {X S : Scheme.{0}} [inst : IsIntegral X] [inst_1 : CompactSpace X]
      [inst_2 : IsLocallyNoetherian X] [inst_3 : IsNormal X]
      {sX : X ⟶ Spec (.of ℂ)} [inst_4 : QuasiCompact sX] {sS : S ⟶ Spec (.of ℂ)}
      (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
      (h : X ⟶ S), h ≫ sS = sX → topologicalKrullDim X = 4 →
      ∀ {K : Divisor X}, K.IsCanonicalDivisor sX 4 →
      ∀ {B : QDivisor X}, MMP.Intersection.IsLogCanonicalPair sX B →
    ∃ hD : (Divisor.toQDivisor K + B).IsQCartier,
      (∀ R : Set (RelativeNumericalCurveClasses sX h),
        IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R →
          ∃ (C : ProperCurve sX) (hC : C.IsContractedBy h),
            IsRationalCurve sX
              (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
            R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = w} ∧
            0 < -QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
              (C.relativeClass h hC) ∧
            -QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
              (C.relativeClass h hC) ≤ 8) ∧
      {R : Set (RelativeNumericalCurveClasses sX h) |
        IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R}.Countable ∧
      (relativeClosedConeOfCurves sX h : Set (RelativeNumericalCurveClasses sX h)) =
        {z | z ∈ relativeClosedConeOfCurves sX h ∧
          0 ≤ QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD z} +
        (PointedCone.hull ℝ (⋃₀ {R : Set (RelativeNumericalCurveClasses sX h) |
            IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R}) :
          Set (RelativeNumericalCurveClasses sX h)) ∧
      (∀ (A : Divisor X) (hA : A.IsCartier), A.IsAmple hA → ∀ ε : ℝ, 0 < ε →
        haveI := hA.isInvertibleModule_divisorialSheaf
        {R : Set (RelativeNumericalCurveClasses sX h) |
          IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R ∧
            ∀ u ∈ R, u ≠ 0 →
              QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD u +
                ε * RelativeNumericalCurveClasses.degree sX h A.divisorialSheaf u < 0}.Finite) ∧
      (∀ z : RelativeNumericalCurveClasses sX h,
        QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD z < 0 →
          ∃ U ∈ 𝓝 z, {R : Set (RelativeNumericalCurveClasses sX h) |
            IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R ∧
              (R ∩ U).Nonempty}.Finite) ∧
      (¬ QDivisor.IsRelativelyNef sX h (Divisor.toQDivisor K + B) →
        ∃ R : Set (RelativeNumericalCurveClasses sX h),
          IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R) := by
  intro X S _ _ _ _ sX _ sS hX hS h hh hdim K hK B hB
  classical
  haveI : MMP.Mori.IsProjectiveVariety ℂ sX := hX
  haveI : MMP.Mori.IsProjectiveVariety ℂ sS := hS
  have hD : (Divisor.toQDivisor K + B).IsQCartier := by
    obtain ⟨⟨hXn, n', K', hK', hQ'⟩, -, -⟩ := hB
    exact hQ'.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hK' hK)
  refine ⟨hD, ?_⟩
  obtain ⟨ι, hι, C, hC, hrat, hbd, hdec⟩ := exists_curves_subset_add_hull hX hS h hh hdim hK hB hD
  set D := Divisor.toQDivisor K + B
  set ℓ := QDivisor.relativeCurveForm sX h D hD with hℓ_def
  set N := relativeClosedConeOfCurves sX h
  haveI : IsTopologicalAddGroup (RelativeNumericalCurveClasses sX h) :=
    topologicalAddGroup_iInf fun _ => topologicalAddGroup_iInf fun _ =>
      topologicalAddGroup_induced _
  haveI : ContinuousSMul ℝ (RelativeNumericalCurveClasses sX h) :=
    continuousSMul_iInf fun _ => continuousSMul_iInf fun _ => continuousSMul_induced _
  have hℓc : Continuous ℓ := continuous_relativeCurveForm sX h D hD
  set g : ι → RelativeNumericalCurveClasses sX h := fun j => (C j).relativeClass h (hC j)
  have hgN : ∀ j, g j ∈ N := fun j => by
    rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves (hC j))
  have hNcl : IsClosed (N : Set (RelativeNumericalCurveClasses sX h)) := by
    rw [coe_relativeClosedConeOfCurves]; exact isClosed_closure
  have hN₀ : (N : Set (RelativeNumericalCurveClasses sX h)) ⊆
      closure (relativeConeOfCurves sX h : Set _) := by
    rw [coe_relativeClosedConeOfCurves]
  -- for every ample `M` and `ε > 0`, `NE̅(X/S) ⊆ NE̅(X/S)_{D + εM ≥ 0} + hull F_ε`
  have key : ∀ (M : X.CartierDivisor)
      (hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M)) (ε : ℝ),
      0 < ε → (N : Set (RelativeNumericalCurveClasses sX h)) ⊆
        {z | z ∈ N ∧ 0 ≤ ℓ z + ε * RelativeNumericalCurveClasses.degree sX h
          (MMP.CartierDivisor.sheaf M) z} +
        (PointedCone.hull ℝ {x | ∃ j, g j = x ∧ ℓ x + ε * RelativeNumericalCurveClasses.degree
          sX h (MMP.CartierDivisor.sheaf M) x < 0} : Set _) := by
    intro M hM ε hε
    refine subset_add_hull_of_finite hNcl hN₀ ℓ _ hℓc
      (RelativeNumericalCurveClasses.continuous_degree sX h _)
      (fun z hz => relativeDegree_nonneg hX h M hM hz) g hgN
      (fun j => relativeDegree_pos hX h M hM (C j) (hC j)) hdec hε ?_
    refine (finite_relativeClass_degree_le h M hM (8 / ε)).subset ?_
    rintro _ ⟨j, rfl, hj⟩
    refine ⟨C j, hC j, rfl, ?_⟩
    rw [le_div_iff₀ hε]
    nlinarith [(hbd j).2]
  obtain ⟨M₀, hM₀⟩ := exists_isAmple_cartierSheaf hX
  set α₀ := RelativeNumericalCurveClasses.degree sX h (MMP.CartierDivisor.sheaf M₀)
  have hα₀c : Continuous α₀ := RelativeNumericalCurveClasses.continuous_degree sX h _
  -- every negative extremal ray is spanned by one of the `Cⱼ`
  have hray : ∀ R, IsNegativeRelativeExtremalRayOf sX h D R →
      ∃ j, R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • g j = w} := by
    rintro R ⟨hD', hR, hneg⟩
    obtain ⟨-, v, hv0, hRv⟩ := id hR
    have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
    have hαv : 0 ≤ α₀ v := relativeDegree_nonneg hX h M₀ hM₀ (hR.1.1 hvR)
    have hℓv : ℓ v < 0 := hneg v hvR hv0
    set ε := -ℓ v / (α₀ v + 1)
    have hε : 0 < ε := div_pos (neg_pos.mpr hℓv) (by linarith)
    set μ : RelativeNumericalCurveClasses sX h →ₗ[ℝ] ℝ := ℓ + ε • α₀
    have hμv : μ v < 0 := by
      have e : μ v = ℓ v / (α₀ v + 1) := by
        simp only [μ, ε, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        field_simp
        ring
      rw [e]
      exact div_neg_of_neg_of_pos hℓv (by linarith)
    obtain ⟨_, ⟨j, rfl, -⟩, hRj⟩ := exists_mem_eq_ray hR μ (neg_of_mem_ray μ hRv hvR hμv)
      (F := {x | ∃ j, g j = x ∧ ℓ x + ε * α₀ x < 0}) (by rintro _ ⟨j, rfl, -⟩; exact hgN j)
      (fun z hz => by
        obtain ⟨a, ha, b, hb, rfl⟩ := key M₀ hM₀ ε hε hz
        exact ⟨a, ⟨ha.1, by simpa [μ] using ha.2⟩, b, hb, rfl⟩)
    exact ⟨j, hRj⟩
  have hfin : ∀ (M : X.CartierDivisor)
      (hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M)) {ε : ℝ}, 0 < ε →
      {R : Set (RelativeNumericalCurveClasses sX h) | IsNegativeRelativeExtremalRayOf sX h D R ∧
        ∀ u ∈ R, u ≠ 0 → ℓ u + ε * RelativeNumericalCurveClasses.degree sX h
          (MMP.CartierDivisor.sheaf M) u < 0}.Finite :=
    fun M hM ε hε => finite_rays h hD C hC (fun j => (hbd j).1) (fun j => (hbd j).2) hray M hM hε
  refine ⟨fun R hR => ?_, ?_, ?_, fun A hA hAmp ε hε => ?_, fun z hz => ?_, fun hnn => ?_⟩
  · -- the rays
    obtain ⟨j, hj⟩ := hray R hR
    exact ⟨C j, hC j, hrat j, hj, hbd j⟩
  · -- countability
    refine (Set.countable_range fun j => {w | ∃ c : ℝ, 0 ≤ c ∧ c • g j = w}).mono ?_
    intro R hR
    obtain ⟨j, hj⟩ := hray R hR
    exact ⟨j, hj.symm⟩
  · -- the cone formula, from the decomposition into extremal rays
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨s, Rs, w, hRw, rfl⟩ :=
        exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sS h hh hz
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => IsNegativeRelativeExtremalRayOf sX h D (Rs i)) w
      rw [← hsplit]
      refine Set.mem_add.mpr ⟨∑ i ∈ Finset.univ.filter
          (fun i => ¬ IsNegativeRelativeExtremalRayOf sX h D (Rs i)), w i, ?_,
        ∑ i ∈ Finset.univ.filter (fun i => IsNegativeRelativeExtremalRayOf sX h D (Rs i)), w i,
        ?_, add_comm _ _⟩
      swap
      · exact Submodule.sum_mem _ fun i hi => Submodule.subset_span
          (Set.mem_sUnion_of_mem (hRw i).2 (Finset.mem_filter.mp hi).2)
      refine ⟨Submodule.sum_mem _ fun i _ => (hRw i).1.1.1 (hRw i).2, ?_⟩
      rw [map_sum]
      refine Finset.sum_nonneg fun i hi => ?_
      by_contra hlt
      obtain ⟨-, v, -, hRv⟩ := (hRw i).1
      exact (Finset.mem_filter.mp hi).2
        ⟨hD, (hRw i).1, neg_of_mem_ray ℓ hRv (hRw i).2 (not_le.mp hlt)⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      refine N.add_mem ha.1 ?_
      refine (Submodule.span_le.mpr ?_ : PointedCone.hull ℝ _ ≤ N) hb
      rintro x ⟨R, ⟨-, hR, -⟩, hx⟩
      exact hR.1.1 hx
  · -- finiteness in each region `D + εA < 0`
    haveI := hA.isInvertibleModule_divisorialSheaf
    obtain ⟨M, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf A.divisorialSheaf
    have hM : Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf M) :=
      (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).mp hAmp
    have hdeg := relativeDegree_eq_of_iso (sX := sX) h e
    simp only [hdeg]
    exact hfin M hM hε
  · -- local finiteness in `D < 0`
    set ε := -ℓ z / (|α₀ z| + 1)
    have hε : 0 < ε := div_pos (neg_pos.mpr hz) (by positivity)
    have hεz : ℓ z + ε * α₀ z < 0 := by
      have h1 : ε * α₀ z ≤ ε * |α₀ z| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
      have h2 : ε * |α₀ z| < -ℓ z := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (α₀ z), neg_pos.mpr hz]
      linarith
    set U := {y : RelativeNumericalCurveClasses sX h | ℓ y + ε * α₀ y < 0}
    have hU : IsOpen U := isOpen_lt (hℓc.add (continuous_const.mul hα₀c)) continuous_const
    refine ⟨U, hU.mem_nhds hεz, (hfin M₀ hM₀ hε).subset ?_⟩
    rintro R ⟨hR, y, hyR, hyU⟩
    obtain ⟨j, hj⟩ := hray R hR
    refine ⟨hR, neg_of_mem_ray (ℓ + ε • α₀) hj hyR ?_⟩
    have hyU' : ℓ y + ε * α₀ y < 0 := hyU
    simpa using hyU'
  · -- a non-nef adjoint has a negative ray
    by_contra hno
    simp only [not_exists] at hno
    apply hnn
    refine isRelativelyNef_of_forall h D hD fun Γ hΓ => ?_
    have hΓN : Γ.relativeClass h hΓ ∈ N := by
      rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves]
      exact subset_closure (relativeClass_mem_relativeConeOfCurves hΓ)
    have e := relativeCurveForm_relativeClass h D hD Γ hΓ
    by_contra hlt
    have hlt' : ℓ (Γ.relativeClass h hΓ) < 0 := by
      rw [e]; exact_mod_cast not_le.mp hlt
    obtain ⟨s, Rs, w, hRw, hsum⟩ :=
      exists_sum_mem_isExtremalRay_relativeClosedConeOfCurves sX sS h hh hΓN
    rw [hsum, map_sum] at hlt'
    obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt (by simpa using hlt' :
      ∑ i, ℓ (w i) < ∑ i : Fin s, (0 : ℝ))
    obtain ⟨-, v, -, hRv⟩ := (hRw i).1
    exact hno (Rs i) ⟨hD, (hRw i).1, neg_of_mem_ray ℓ hRv (hRw i).2 hi⟩

end Proof_thm_mmp_projective_fourfold_lc_cone

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Pointwise Topology

namespace MMP.Fourfold

open MMP.Mori

/-- **The cone theorem for projective lc fourfolds.** Let `h : X ⟶ S` be a morphism of
projective complex varieties with `X` normal of dimension four, `K` a canonical divisor of `X`
and `(X, B)` a log canonical pair with `B` a `ℚ`-divisor. Then `D = K + B` is `ℚ`-Cartier and:

1. every `D`-negative extremal ray `R` of `relativeClosedConeOfCurves sX h` is
   `ℝ_{≥0} [C]` for a rational curve `C` contracted by `h` with `0 < -(D · C) ≤ 8`;
2. the set of `D`-negative extremal rays is countable;
3. `NE̅(X/S)` is the sum of its part where `D ≥ 0` and the convex cone spanned by the
   `D`-negative extremal rays;
4. for every ample Cartier divisor `A` and every `ε > 0`, only finitely many `D`-negative
   extremal rays are `(D + εA)`-negative;
5. every class `z` with `D · z < 0` has a neighbourhood meeting only finitely many
   `D`-negative extremal rays;
6. if `D` is not nef over `S`, there is a `D`-negative extremal ray. -/
@[mmp "thm_mmp_projective_fourfold_lc_cone"]
public theorem exists_relativeClosedConeOfCurves_eq_add_hull_of_isLogCanonicalPair
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sS : S ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (h : X ⟶ S) (hh : h ≫ sS = sX) (hdim : topologicalKrullDim X = 4)
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX 4)
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B) :
    ∃ hD : (Divisor.toQDivisor K + B).IsQCartier,
      (∀ R : Set (RelativeNumericalCurveClasses sX h),
        IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R →
          ∃ (C : ProperCurve sX) (hC : C.IsContractedBy h),
            IsRationalCurve sX
              (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({C.point} : Set X))) ∧
            R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • C.relativeClass h hC = w} ∧
            0 < -QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
              (C.relativeClass h hC) ∧
            -QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD
              (C.relativeClass h hC) ≤ 8) ∧
      {R : Set (RelativeNumericalCurveClasses sX h) |
        IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R}.Countable ∧
      (relativeClosedConeOfCurves sX h : Set (RelativeNumericalCurveClasses sX h)) =
        {z | z ∈ relativeClosedConeOfCurves sX h ∧
          0 ≤ QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD z} +
        (PointedCone.hull ℝ (⋃₀ {R : Set (RelativeNumericalCurveClasses sX h) |
            IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R}) :
          Set (RelativeNumericalCurveClasses sX h)) ∧
      (∀ (A : Divisor X) (hA : A.IsCartier), A.IsAmple hA → ∀ ε : ℝ, 0 < ε →
        haveI := hA.isInvertibleModule_divisorialSheaf
        {R : Set (RelativeNumericalCurveClasses sX h) |
          IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R ∧
            ∀ u ∈ R, u ≠ 0 →
              QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD u +
                ε * RelativeNumericalCurveClasses.degree sX h A.divisorialSheaf u < 0}.Finite) ∧
      (∀ z : RelativeNumericalCurveClasses sX h,
        QDivisor.relativeCurveForm sX h (Divisor.toQDivisor K + B) hD z < 0 →
          ∃ U ∈ 𝓝 z, {R : Set (RelativeNumericalCurveClasses sX h) |
            IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R ∧
              (R ∩ U).Nonempty}.Finite) ∧
      (¬ QDivisor.IsRelativelyNef sX h (Divisor.toQDivisor K + B) →
        ∃ R : Set (RelativeNumericalCurveClasses sX h),
          IsNegativeRelativeExtremalRayOf sX h (Divisor.toQDivisor K + B) R) :=
            by revert X S sX sS hX hS h hh hdim K hK B hB; first | exact Proof_thm_mmp_projective_fourfold_lc_cone.solution | exact Proof_thm_mmp_projective_fourfold_lc_cone.solution _ | exact Proof_thm_mmp_projective_fourfold_lc_cone.solution _ _ | exact Proof_thm_mmp_projective_fourfold_lc_cone.solution _ _ _ | exact Proof_thm_mmp_projective_fourfold_lc_cone.solution _ _ _ _

end MMP.Fourfold

