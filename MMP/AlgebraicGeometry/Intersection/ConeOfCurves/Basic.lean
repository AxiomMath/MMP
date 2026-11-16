module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Intersection.OneCycles
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Analysis.Convex.Cone.Closure
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Cones, extremal faces and the cone of curves

Let `𝕜` be an ordered field (`ℚ` or `ℝ` in Kollár–Mori) and `V` a `𝕜`-vector space. A subset
`N ⊆ V` is a *cone* if `0 ∈ N` and `λ v ∈ N` for `v ∈ N`, `λ > 0`; it is *convex* if it is moreover
closed under addition, that is, a pointed cone `PointedCone 𝕜 V`. A subcone `M ⊆ N` is an
*extremal face* of `N` if `u + v ∈ M` with `u, v ∈ N` forces `u, v ∈ M`, and an *extremal ray* if
moreover `M = 𝕜_{≥0} v` for some `v ≠ 0`. For a linear form `L ≥ 0` on a cone `C`, the *face*
`F_L = {z ∈ C : L(z) = 0}` is an extremal face. A face is `K`-negative, for a linear form `K`, if
it is convex and `K < 0` on its nonzero points.

For a proper variety `X`, the *cone of curves* `NE(X) ⊆ N₁(X)` is the convex cone spanned by the
classes `[C]` of the curves of `X`, and the *closed cone of curves* `NE̅(X)` is its closure for the
numerical topology.

The *`K`-threshold* of a linear form `G` on a cone `C` is the largest `t` with `G + tK ≥ 0` on
`C`. A *cone datum* `(N_ℤ, NE̅, K, a)` collects the hypotheses of the abstract cone theorem
(Kollár–Mori, Theorem 3.15), and `𝓡(NE̅, K)` is the set of `K`-negative rays cut out by rational
nef forms. Finally, for `ℚ`-Cartier divisors `H, K` on a normal variety, a *nef threshold* of `H`
with respect to `K` is the largest real `r` with `H + rK` nef.

## Main definitions

* `MMP.Mori.IsCone`: cones.
* `MMP.Mori.IsExtremalFace`, `MMP.Mori.IsExtremalRay`: extremal faces and extremal rays.
* `MMP.Mori.faceOfNefForm`: the face `F_L = L^⊥ ∩ C`.
* `MMP.Mori.IsNegativeExtremalFace`: `K`-negative extremal faces.
* `MMP.Mori.IsConeThreshold`: the `K`-threshold of `G` on a cone.
* `MMP.Mori.coneOfCurves`, `MMP.Mori.closedConeOfCurves`: `NE(X)` and `NE̅(X)`.
* `MMP.Mori.ConeDatum`, `MMP.Mori.ConeDatum.negativeRationalRays`: cone data and `𝓡(NE̅, K)`.
* `MMP.Mori.QDivisor.IsNefCombination`, `MMP.Mori.QDivisor.IsNefThreshold`: nefness of
  `H + tK` for real `t`, and nef thresholds.

## Main results

* `MMP.Mori.isCone_and_add_mem_iff`: the convex cones are exactly the pointed cones.
* `MMP.Mori.isExtremalFace_iff_isFaceOf`: for pointed cones, extremal faces are the faces
  `PointedCone.IsFaceOf`.
* `MMP.Mori.isExtremalFace_iff_isExtreme`: for cones, extremal faces are the extreme subcones.
* `MMP.Mori.isExtremalFace_faceOfNefForm`: `F_L` is an extremal face when `L ≥ 0` on the convex
  cone.
* `MMP.Mori.isConeThreshold_iff_isGreatest`: the threshold is the greatest `t` with `G + tK ≥ 0`.
* `MMP.Mori.mem_coneOfCurves_iff`: `NE(X)` consists of the classes of effective real 1-cycles.

## Implementation notes

Cones, faces and thresholds are stated for subsets of a module, without the convexity or
closedness hypotheses the source places on the ambient cone where the definition does not need
them; the source's definitions are the special cases.

In a cone datum the lattice `N_ℤ` is a free `ℤ`-module of finite rank `N`, the real space is the
base change `N_ℝ = ℝ ⊗_ℤ N` with its canonical (module) topology, and the dual spaces
`N_ℚ^* = Hom_ℚ(ℚ ⊗ N, ℚ)` and `N_ℤ^*` are recorded as `Hom_ℤ(N, ℚ)` and `Hom_ℤ(N, ℤ)`, which
are canonically isomorphic to them; a form acts on `N_ℝ` through its `ℝ`-linear extension.
The condition on `a` is stated for every threshold `t`; since a threshold, when it exists, is
unique, this is the source's condition on "the" threshold.

The cone of curves is spanned by the classes of the proper curves of `X` of
`MMP.Mori.ProperCurve`, which on a proper variety are all of its irreducible curves, and its
closure is taken for the numerical topology of `N₁(X)`, for which `N₁(X)` is a topological real
vector space (`MMP.Mori.NumericalCurveClasses.instContinuousAdd`,
`MMP.Mori.NumericalCurveClasses.instContinuousConstSMul`).

For the nef threshold, "every closed curve" is every closed curve proper over `k`, which on a
proper variety is every closed curve, as in `MMP.Mori.QDivisor.IsNef`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.15, 1.17,
  3.3, 3.5, 3.7, 3.15
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Mori

/-! ### Cones and extremal faces -/

section Cones

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- A subset `N` of a `𝕜`-vector space is a *cone* if `0 ∈ N` and `λ v ∈ N` for every `v ∈ N`
and every `λ > 0`. A cone closed under addition is a *convex cone*, that is, a
`PointedCone 𝕜 V` (`MMP.Mori.isCone_and_add_mem_iff`). -/
@[mmp "def_km1b_cone"]
def IsCone (N : Set V) : Prop :=
  0 ∈ N ∧ ∀ v ∈ N, ∀ c : 𝕜, 0 < c → c • v ∈ N

variable {𝕜}

/-- A pointed cone is a cone. -/
theorem isCone_coe (C : PointedCone 𝕜 V) : IsCone 𝕜 (C : Set V) :=
  ⟨C.zero_mem, fun _ hv _ hc => C.smul_mem hc.le hv⟩

/-- The convex cones are exactly the pointed cones. -/
theorem isCone_and_add_mem_iff (N : Set V) :
    (IsCone 𝕜 N ∧ ∀ u ∈ N, ∀ v ∈ N, u + v ∈ N) ↔ ∃ C : PointedCone 𝕜 V, (C : Set V) = N := by
  constructor
  · rintro ⟨⟨h0, hs⟩, ha⟩
    refine ⟨
      { carrier := N
        zero_mem' := h0
        add_mem' := fun hu hv => ha _ hu _ hv
        smul_mem' := ?_ }, rfl⟩
    rintro ⟨c, hc⟩ v hv
    rcases hc.lt_or_eq with hc | rfl
    · exact hs v hv c hc
    · simpa using h0
  · rintro ⟨C, rfl⟩
    exact ⟨isCone_coe C, fun _ hu _ hv => C.add_mem hu hv⟩

variable (𝕜)

/-- A subset `M` of a cone `N` is an *extremal face* of `N` if it is a convex subcone of `N` (a
subset which is itself a cone, closed under addition, as in Kollár–Mori 1.15) such that
`u + v ∈ M` with `u, v ∈ N` implies `u ∈ M` and `v ∈ M`. -/
@[mmp "def_km1b_extremal_face"]
def IsExtremalFace (N M : Set V) : Prop :=
  M ⊆ N ∧ IsCone 𝕜 M ∧ (∀ u ∈ M, ∀ v ∈ M, u + v ∈ M) ∧
    ∀ u ∈ N, ∀ v ∈ N, u + v ∈ M → u ∈ M ∧ v ∈ M

/-- An *extremal ray* of a cone `N` is an extremal face `R` of `N` of the form `R = 𝕜_{≥0} · v`
for some `v ≠ 0`. -/
@[mmp "def_km1b_extremal_ray"]
def IsExtremalRay (N R : Set V) : Prop :=
  IsExtremalFace 𝕜 N R ∧ ∃ v : V, v ≠ 0 ∧ R = {w | ∃ c : 𝕜, 0 ≤ c ∧ c • v = w}

variable {𝕜}

/-- For cones `M ⊆ N`, `M` is an extremal face of `N` if and only if it is an extreme subset of
`N` in the sense of convexity. -/
theorem isExtremalFace_iff_isExtreme {N M : Set V} (hN : IsCone 𝕜 N) (hM : IsCone 𝕜 M)
    (hMadd : ∀ u ∈ M, ∀ v ∈ M, u + v ∈ M) :
    IsExtremalFace 𝕜 N M ↔ IsExtreme 𝕜 N M := by
  constructor
  · rintro ⟨hMN, -, -, h⟩
    refine ⟨hMN, ?_⟩
    rintro x₁ hx₁ x₂ hx₂ x hx ⟨a, b, ha, hb, -, rfl⟩
    simpa [smul_smul, ha.ne'] using
      hM.2 _ (h _ (hN.2 x₁ hx₁ a ha) _ (hN.2 x₂ hx₂ b hb) hx).1 a⁻¹ (inv_pos.mpr ha)
  · intro h
    refine ⟨h.1, hM, hMadd, fun u hu v hv huv => ?_⟩
    have h2 : (0 : 𝕜) < 2⁻¹ := by positivity
    have hm : (2⁻¹ : 𝕜) • (u + v) ∈ M := hM.2 _ huv 2⁻¹ h2
    refine ⟨h.2 hu hv hm ⟨2⁻¹, 2⁻¹, h2, h2, by norm_num, (smul_add _ _ _).symm⟩,
      h.2 hv hu hm ⟨2⁻¹, 2⁻¹, h2, h2, by norm_num, ?_⟩⟩
    rw [smul_add, add_comm]

/-- For pointed cones over an ordered field, the extremal faces of `C` are exactly the faces
`PointedCone.IsFaceOf`. -/
theorem isExtremalFace_iff_isFaceOf (C F : PointedCone 𝕜 V) :
    IsExtremalFace 𝕜 (C : Set V) (F : Set V) ↔ F.IsFaceOf C := by
  constructor
  · rintro ⟨hFC, -, -, h⟩
    refine ⟨hFC, fun {x y a} hx hy ha hxy => ?_⟩
    simpa [smul_smul, ha.ne'] using
      F.smul_mem (inv_pos.mpr ha).le (h _ (C.smul_mem ha.le hx) _ hy hxy).1
  · intro h
    refine ⟨h.le, isCone_coe F, fun u hu v hv => F.add_mem hu hv, fun u hu v hv huv => ⟨?_, ?_⟩⟩
    · exact h.mem_of_smul_add_mem hu hv one_pos (by simpa using huv)
    · exact h.mem_of_smul_add_mem hv hu one_pos (by simpa [add_comm] using huv)

/-- The *face* `F_L = {z ∈ C : L(z) = 0}` of a linear form `L` on a cone `C`; when `C` is a
convex cone and `L ≥ 0` on `C`, this is the face of the nef class `L`, an extremal face
of `C` (`MMP.Mori.isExtremalFace_faceOfNefForm`). -/
@[mmp "def_km3b_face_of_nef_class"]
def faceOfNefForm (C : Set V) (L : Module.Dual 𝕜 V) : Set V :=
  {z | z ∈ C ∧ L z = 0}

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- `z ∈ F_L` if and only if `z ∈ C` and `L(z) = 0`. -/
@[simp]
theorem mem_faceOfNefForm_iff {C : Set V} {L : Module.Dual 𝕜 V} {z : V} :
    z ∈ faceOfNefForm C L ↔ z ∈ C ∧ L z = 0 :=
  Iff.rfl

/-- If `L ≥ 0` on a convex cone `C`, then `F_L` is an extremal face of `C`. -/
theorem isExtremalFace_faceOfNefForm {C : Set V} (hC : IsCone 𝕜 C)
    (hCadd : ∀ u ∈ C, ∀ v ∈ C, u + v ∈ C) {L : Module.Dual 𝕜 V}
    (hL : ∀ z ∈ C, 0 ≤ L z) : IsExtremalFace 𝕜 C (faceOfNefForm C L) := by
  refine ⟨fun z hz => hz.1, ⟨⟨hC.1, map_zero L⟩, fun v hv c hc => ⟨hC.2 v hv.1 c hc, ?_⟩⟩,
    fun u hu v hv => ⟨hCadd u hu.1 v hv.1, by rw [map_add, hu.2, hv.2, add_zero]⟩,
    fun u hu v hv huv => ?_⟩
  · rw [map_smul, hv.2, smul_zero]
  · obtain ⟨hu0, hv0⟩ := (add_eq_zero_iff_of_nonneg (hL u hu) (hL v hv)).1
      ((map_add L u v).symm.trans huv.2)
    exact ⟨⟨hu, hu0⟩, hv, hv0⟩

variable (𝕜) in
/-- A *`K`-negative extremal face* of a cone `N`, for a linear form `K`, is an extremal face `F`
of `N` which is convex (closed under addition) and on which `K(z) < 0` for every `z ≠ 0`. For a
projective variety `X` and an `ℝ`-Cartier divisor `D` this is applied to `N = NE̅(X)` and the
linear form `K = (D · _)`. -/
@[mmp "def_km3b_negative_extremal_face"]
def IsNegativeExtremalFace (N : Set V) (K : Module.Dual 𝕜 V) (F : Set V) : Prop :=
  IsExtremalFace 𝕜 N F ∧ (∀ u ∈ F, ∀ v ∈ F, u + v ∈ F) ∧ ∀ z ∈ F, z ≠ 0 → K z < 0

/-- An element `t : 𝕜` is the *`K`-threshold of `G` on `C`*, for linear forms `G, K` on a (closed
convex) cone `C`, if `G + tK ≥ 0` on `C` and, for every `t' > t`, `G + t'K` is not `≥ 0` on
`C`. -/
@[mmp "def_km3b_cone_threshold"]
def IsConeThreshold (C : Set V) (G K : Module.Dual 𝕜 V) (t : 𝕜) : Prop :=
  (∀ z ∈ C, 0 ≤ G z + t * K z) ∧ ∀ t' : 𝕜, t < t' → ¬ ∀ z ∈ C, 0 ≤ G z + t' * K z

omit [IsStrictOrderedRing 𝕜] in
/-- The `K`-threshold of `G` on `C` is the greatest `t` with `G + tK ≥ 0` on `C`. -/
theorem isConeThreshold_iff_isGreatest (C : Set V) (G K : Module.Dual 𝕜 V) (t : 𝕜) :
    IsConeThreshold C G K t ↔ IsGreatest {s : 𝕜 | ∀ z ∈ C, 0 ≤ G z + s * K z} t := by
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, fun s hs => not_lt.mp fun hts => h₂ s hts hs⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, fun t' ht' h => (h₂ h).not_gt ht'⟩⟩

omit [IsStrictOrderedRing 𝕜] in
/-- The `K`-threshold of `G` on `C` is unique. -/
theorem IsConeThreshold.unique {C : Set V} {G K : Module.Dual 𝕜 V} {t t' : 𝕜}
    (h : IsConeThreshold C G K t) (h' : IsConeThreshold C G K t') : t = t' :=
  ((isConeThreshold_iff_isGreatest C G K t).mp h).unique
    ((isConeThreshold_iff_isGreatest C G K t').mp h')

end Cones

/-! ### Cone data -/

section ConeDatum

variable (N : Type u) [AddCommGroup N]

/-- The `ℝ`-linear extension `N_ℝ = ℝ ⊗_ℤ N → ℝ` of a `ℚ`-valued form `K : N → ℚ`, an element
of `N_ℚ^*`. -/
def realOfRatForm (K : N →ₗ[ℤ] ℚ) : Module.Dual ℝ (ℝ ⊗[ℤ] N) :=
  LinearMap.liftBaseChange ℝ ((Rat.castHom ℝ).toAddMonoidHom.toIntLinearMap ∘ₗ K)

/-- The `ℝ`-linear extension `N_ℝ = ℝ ⊗_ℤ N → ℝ` of an integral form `H ∈ N_ℤ^*`. -/
def realOfIntForm (H : Module.Dual ℤ N) : Module.Dual ℝ (ℝ ⊗[ℤ] N) :=
  LinearMap.liftBaseChange ℝ ((Int.castAddHom ℝ).toIntLinearMap ∘ₗ H)

/-- A *cone datum* `(N_ℤ, NE̅, K, a)`, the hypotheses of the abstract cone theorem: `N_ℤ = N`
is a free `ℤ`-module of finite rank; `NE̅ ⊆ N_ℝ = ℝ ⊗_ℤ N` is a closed convex cone with
`NE̅ ∩ (-NE̅) = {0}`; `K ∈ N_ℚ^*` (recorded as `N → ℚ`) satisfies `K(z) < 0` for some `z ∈ NE̅`;
and `a ∈ ℤ_{>0}` is such that for every `H ∈ N_ℤ^*` positive on `NE̅ \ {0}` the `K`-threshold of
`H` on `NE̅` lies in `(1/a) ℤ`. -/
@[mmp "def_km3b_cone_datum"]
structure ConeDatum [Module.Free ℤ N] [Module.Finite ℤ N] where
  /-- The closed convex cone `NE̅ ⊆ N_ℝ`. -/
  cone : PointedCone ℝ (ℝ ⊗[ℤ] N)
  /-- `NE̅` is closed for the canonical topology of the finite-dimensional space `N_ℝ`. -/
  isClosed_cone : @IsClosed _ (moduleTopology ℝ (ℝ ⊗[ℤ] N)) (cone : Set (ℝ ⊗[ℤ] N))
  /-- `NE̅ ∩ (-NE̅) = {0}`. -/
  inter_neg_eq : ((cone : Set (ℝ ⊗[ℤ] N)) ∩ -(cone : Set (ℝ ⊗[ℤ] N))) = {0}
  /-- The rational form `K ∈ N_ℚ^*`. -/
  form : N →ₗ[ℤ] ℚ
  /-- `K(z) < 0` for some `z ∈ NE̅`. -/
  exists_form_neg : ∃ z ∈ cone, realOfRatForm N form z < 0
  /-- The denominator bound `a`. -/
  index : ℤ
  /-- The denominator bound is positive. -/
  index_pos : 0 < index
  /-- For every `H ∈ N_ℤ^*` positive on `NE̅ \ {0}`, the `K`-threshold of `H` on `NE̅` lies in
  `(1/a) ℤ`. -/
  threshold_mem : ∀ H : Module.Dual ℤ N, (∀ z ∈ cone, z ≠ 0 → 0 < realOfIntForm N H z) →
    ∀ t : ℝ, IsConeThreshold (cone : Set (ℝ ⊗[ℤ] N)) (realOfIntForm N H)
      (realOfRatForm N form) t → ∃ m : ℤ, t = m / index

variable {N}

/-- For a cone datum `(N_ℤ, NE̅, K, a)`, the set `𝓡(NE̅, K)` of rays `R = ℝ_{≥0} ξ` with
`ξ ∈ N_ℝ` and `K(ξ) < 0` such that `R = F_L` for some `L ∈ N_ℚ^*` with `L ≥ 0` on `NE̅`. -/
@[mmp "def_km3b_negative_rational_rays"]
def ConeDatum.negativeRationalRays [Module.Free ℤ N] [Module.Finite ℤ N] (D : ConeDatum N) :
    Set (Set (ℝ ⊗[ℤ] N)) :=
  {R | ∃ ξ : ℝ ⊗[ℤ] N, realOfRatForm N D.form ξ < 0 ∧
    R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ξ = w} ∧
    ∃ L : N →ₗ[ℤ] ℚ, (∀ z ∈ D.cone, 0 ≤ realOfRatForm N L z) ∧
      R = faceOfNefForm (D.cone : Set (ℝ ⊗[ℤ] N)) (realOfRatForm N L)}

end ConeDatum

/-! ### The cone of curves -/

section ConeOfCurves

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- Addition on `N₁(X)` is continuous for the numerical topology. -/
instance NumericalCurveClasses.instContinuousAdd : ContinuousAdd (NumericalCurveClasses sX) :=
  ⟨continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun _ => continuous_induced_rng.2 <| by
    have hc := NumericalCurveClasses.continuous_degree sX L
    change Continuous fun p : NumericalCurveClasses sX × NumericalCurveClasses sX =>
      NumericalCurveClasses.degree sX L (p.1 + p.2)
    simp only [map_add]
    exact (hc.comp continuous_fst).add (hc.comp continuous_snd)⟩

/-- Scalar multiplication by a real number on `N₁(X)` is continuous for the numerical
topology. -/
instance NumericalCurveClasses.instContinuousConstSMul :
    ContinuousConstSMul ℝ (NumericalCurveClasses sX) :=
  ⟨fun c => continuous_iInf_rng.2 fun L => continuous_iInf_rng.2 fun _ =>
    continuous_induced_rng.2 <| by
      have hc := NumericalCurveClasses.continuous_degree sX L
      change Continuous fun z : NumericalCurveClasses sX =>
        NumericalCurveClasses.degree sX L (c • z)
      simp only [map_smul, smul_eq_mul]
      exact continuous_const.mul hc⟩

/-- The *cone of curves* `NE(X) ⊆ N₁(X)`: the convex cone of the classes
`∑ aᵢ [Cᵢ]`, `aᵢ ≥ 0`, of the curves `Cᵢ ⊆ X`. -/
@[mmp "def_km1b_cone_of_curves"]
def coneOfCurves : PointedCone ℝ (NumericalCurveClasses sX) :=
  PointedCone.hull ℝ (Set.range fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ))

/-- The *closed cone of curves* `NE̅(X)`: the closure of `NE(X)` in `N₁(X)` for the numerical
topology. -/
@[mmp "def_km1b_closed_cone_of_curves"]
def closedConeOfCurves : PointedCone ℝ (NumericalCurveClasses sX) :=
  (coneOfCurves sX).closure

/-- As a set, `NE̅(X)` is the topological closure of `NE(X)`. -/
theorem coe_closedConeOfCurves :
    (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) = closure (coneOfCurves sX) :=
  rfl

/-- `NE(X)` is contained in its closure `NE̅(X)`. -/
theorem coneOfCurves_le_closedConeOfCurves : coneOfCurves sX ≤ closedConeOfCurves sX :=
  fun _ hz => subset_closure hz

/-- The class `[C]` of a curve lies in `NE(X)`. -/
theorem numericalClass_cycle_mem_coneOfCurves (C : ProperCurve sX) :
    OneCycle.numericalClass sX (C.cycle ℝ) ∈ coneOfCurves sX :=
  Submodule.subset_span ⟨C, rfl⟩

/-- `NE(X)` consists of the classes of the effective real 1-cycles. -/
theorem mem_coneOfCurves_iff (z : NumericalCurveClasses sX) :
    z ∈ coneOfCurves sX ↔
      ∃ Z : OneCycle ℝ sX, (∀ C, 0 ≤ Z C) ∧ OneCycle.numericalClass sX Z = z := by
  have key : ∀ c : ProperCurve sX →₀ {a : ℝ // 0 ≤ a},
      OneCycle.numericalClass sX (c.mapRange Subtype.val rfl) =
        c.sum fun C a => a • OneCycle.numericalClass sX (C.cycle ℝ) := by
    intro c
    have hZ : c.mapRange Subtype.val rfl = c.sum fun C a => (a : ℝ) • C.cycle ℝ := by
      ext C'
      simp only [Finsupp.mapRange_apply, Finsupp.sum_apply, ProperCurve.cycle,
        Finsupp.smul_apply]
      rw [Finsupp.sum, Finset.sum_eq_single C']
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        simp [Finsupp.notMem_support_iff.mp h]
    rw [hZ, map_finsuppSum]
    rfl
  rw [coneOfCurves, PointedCone.hull, Finsupp.mem_span_range_iff_exists_finsupp]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.mapRange Subtype.val rfl, fun C => (c C).2, key c⟩
  · rintro ⟨Z, hZ, rfl⟩
    refine ⟨Z.mapRange (fun a => ⟨|a|, abs_nonneg a⟩) (Subtype.ext abs_zero), ?_⟩
    rw [← key]
    congr 1
    ext C
    simp [abs_of_nonneg (hZ C)]

end ConeOfCurves

/-! ### Divisor half-spaces and supporting divisors -/

section HalfSpaces

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

namespace KCartierDivisor

/-- The closed half-space `D_{≥0} = {z ∈ N₁(X) | (C · D) ≥ 0 for every real 1-cycle C with
[C] = z}` of an `ℝ`-Cartier divisor `D`. -/
@[mmp "def_km1b_divisor_nonneg_halfspace"]
def nonnegHalfspace (D : KCartierDivisor ℝ X) : Set (NumericalCurveClasses sX) :=
  {z | ∀ Z : OneCycle ℝ sX, OneCycle.numericalClass sX Z = z → 0 ≤ Z.intersectionNumber D}

/-- The open half-space `D_{>0} = {z ∈ N₁(X) | (C · D) > 0 for every real 1-cycle C with
[C] = z}` of an `ℝ`-Cartier divisor `D`. -/
@[mmp "def_km1b_divisor_pos_halfspace"]
def posHalfspace (D : KCartierDivisor ℝ X) : Set (NumericalCurveClasses sX) :=
  {z | ∀ Z : OneCycle ℝ sX, OneCycle.numericalClass sX Z = z → 0 < Z.intersectionNumber D}

/-- The closed half-space `D_{≤0} = {z ∈ N₁(X) | (C · D) ≤ 0 for every real 1-cycle C with
[C] = z}` of an `ℝ`-Cartier divisor `D`. -/
@[mmp "def_km1b_divisor_nonpos_halfspace"]
def nonposHalfspace (D : KCartierDivisor ℝ X) : Set (NumericalCurveClasses sX) :=
  {z | ∀ Z : OneCycle ℝ sX, OneCycle.numericalClass sX Z = z → Z.intersectionNumber D ≤ 0}

/-- The open half-space `D_{<0} = {z ∈ N₁(X) | (C · D) < 0 for every real 1-cycle C with
[C] = z}` of an `ℝ`-Cartier divisor `D`. -/
@[mmp "def_km1b_divisor_neg_halfspace"]
def negHalfspace (D : KCartierDivisor ℝ X) : Set (NumericalCurveClasses sX) :=
  {z | ∀ Z : OneCycle ℝ sX, OneCycle.numericalClass sX Z = z → Z.intersectionNumber D < 0}

private theorem forall_numericalClass_eq_iff (D : KCartierDivisor ℝ X)
    (z : NumericalCurveClasses sX) (P : ℝ → Prop) :
    (∀ Z : OneCycle ℝ sX, OneCycle.numericalClass sX Z = z → P (Z.intersectionNumber D)) ↔
      P (NumericalCurveClasses.intersectionNumber D z) := by
  refine ⟨fun h => ?_, fun h Z hZ => ?_⟩
  · obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
    exact h Z rfl
  · rwa [← hZ, NumericalCurveClasses.intersectionNumber_numericalClass] at h

/-- `z ∈ D_{≥0}` if and only if `0 ≤ (z · D)`. -/
@[simp]
theorem mem_nonnegHalfspace_iff (D : KCartierDivisor ℝ X) (z : NumericalCurveClasses sX) :
    z ∈ nonnegHalfspace sX D ↔ 0 ≤ NumericalCurveClasses.intersectionNumber D z :=
  forall_numericalClass_eq_iff sX D z _

/-- `z ∈ D_{>0}` if and only if `0 < (z · D)`. -/
@[simp]
theorem mem_posHalfspace_iff (D : KCartierDivisor ℝ X) (z : NumericalCurveClasses sX) :
    z ∈ posHalfspace sX D ↔ 0 < NumericalCurveClasses.intersectionNumber D z :=
  forall_numericalClass_eq_iff sX D z _

/-- `z ∈ D_{≤0}` if and only if `(z · D) ≤ 0`. -/
@[simp]
theorem mem_nonposHalfspace_iff (D : KCartierDivisor ℝ X) (z : NumericalCurveClasses sX) :
    z ∈ nonposHalfspace sX D ↔ NumericalCurveClasses.intersectionNumber D z ≤ 0 :=
  forall_numericalClass_eq_iff sX D z (· ≤ 0)

/-- `z ∈ D_{<0}` if and only if `(z · D) < 0`. -/
@[simp]
theorem mem_negHalfspace_iff (D : KCartierDivisor ℝ X) (z : NumericalCurveClasses sX) :
    z ∈ negHalfspace sX D ↔ NumericalCurveClasses.intersectionNumber D z < 0 :=
  forall_numericalClass_eq_iff sX D z (· < 0)

end KCartierDivisor

variable (k) in
/-- A Cartier divisor `D` on `X` is a *supporting divisor* of a subset `F ⊆ NE̅(X)` (in KM, an
extremal face of `NE̅(X)` on a projective variety) if `D` is nef and
`{z ∈ NE̅(X) | (D · z) = 0} = F`. -/
@[mmp "def_km3b_supporting_divisor"]
def IsSupportingDivisor (F : Set (NumericalCurveClasses sX)) (D : X.CartierDivisor) : Prop :=
  (KCartierDivisor.ofCartier ℝ D).IsNef k sX ∧
    {z | z ∈ closedConeOfCurves sX ∧
      NumericalCurveClasses.intersectionNumber (KCartierDivisor.ofCartier ℝ D) z = 0} = F

end HalfSpaces

/-! ### Nef thresholds -/

namespace QDivisor

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X]

/-- For `ℚ`-Cartier `ℚ`-divisors `H, K` on a normal `k`-scheme `X` and a real number `t`,
`H + tK` is *nef* if `(H · C) + t (K · C) ≥ 0` for every closed curve `C ⊆ X` proper over `k`
(every closed curve, when `X` is proper over `k`). -/
@[mmp "def_km3a_nef_threshold"]
def IsNefCombination (H K : QDivisor X) (t : ℝ) : Prop :=
  ∃ (hH : H.IsQCartier) (hK : K.IsQCartier),
    ∀ (C : Scheme.{u}) (i : C ⟶ X) [IsClosedImmersion i] [IsIntegral C] [IsProper (i ≫ sX)]
      (hC : topologicalKrullDim C = 1),
      0 ≤ (H.intersectionNumber k sX i hC.le hH : ℝ) + t * (K.intersectionNumber k sX i hC.le hK)

/-- A real number `r` is a *nef threshold of `H` with respect to `K`* if `H + rK` is nef and
`H + tK` is not nef for every real `t > r`. -/
@[mmp "def_km3a_nef_threshold"]
def IsNefThreshold (H K : QDivisor X) (r : ℝ) : Prop :=
  IsNefCombination k sX H K r ∧ ∀ t : ℝ, r < t → ¬ IsNefCombination k sX H K t

end QDivisor

end MMP.Mori
