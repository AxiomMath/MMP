module

public import MMP.AlgebraicGeometry.Variety.LocalNormalFormAlgebra
public import MMP.Analysis.Complex.HolomorphicLocalNormalForm
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChartDifferential
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold

/-!
# Local normal form of a function near a general point of a component of its zeros

Let `X` be a normal complex variety of dimension `n`, `X₀ ⊆ X` a non-empty affine open subset,
`h ∈ 𝒪(X₀)` non-zero, `Z` an irreducible component of the zero scheme `V(h)` and `m = ord_Z(h)`.
Then there are a connected open subset `U ⊆ X₀(ℂ)` of the classical topology and a holomorphic
function `g` on `U` such that `U ⊆ X_reg(ℂ)`; the set `Y = U ∩ V(h)` is non-empty, contained in
`Z_reg` and disjoint from every other component of `V(h)`; `Y` is a connected closed complex
submanifold of `U` of codimension one; `g⁻¹(0) = Y` with `dg` nowhere zero on `Y`; and
`h|_U = gᵐ`.

The local ring `𝒪_{X,Z}` is a discrete valuation ring, and `h = v πᵐ` there with `π` a
uniformizer and `v` a unit; on a basic open neighbourhood `D(s)` of the generic point of `Z`,
`X` and `Z` are regular, `D(s)` misses the other components of `V(h)`, `V(h) ∩ D(s) = V(π) ∩ D(s)`
and `𝒪_{X,x}/(π)` is regular at the points of `Z ∩ D(s)`
(`MMP.LocalNormalForm.exists_uniformizer_of_maximal`). At a closed point
`p ∈ Z ∩ D(s)` choose an algebraic chart `e` of `X_reg(ℂ)`; since `π` is part of a regular system
of parameters at `p`, its differential at `p` is non-zero
(`MMP.UnderlyingSpace.chartDeriv_ne_zero_of_isRegularLocalRing_quotient`). On a
small neighbourhood `v = e^w`, and `g = π e^{w/m}` together with a complementary linear projection
gives holomorphic coordinates `ψ` with first coordinate `g`
(`MMP.LocalNormalForm.exists_pow_eq_mul_pow_of_fderiv_ne_zero`); `U` is the source
of `ψ ∘ e`, homeomorphic to a convex set, and `Y` corresponds to its intersection with the
hyperplane `{0} × ℂⁿ⁻¹`.

## Main results

* `MMP.UnderlyingSpace.exists_localNormalForm`: the local normal form.

## Implementation notes

The underlying space `X(ℂ)` is `MMP.UnderlyingSpace ℂ X`, and the value of a
section `a ∈ Γ(X, X₀)` at a point `p` is `MMP.UnderlyingSpace.evalExt X₀ a p`. The
complex manifold structure of `X_reg(ℂ)` is given by its algebraic charts
(`MMP.UnderlyingSpace.regularChartedSpace`), with values in `ℂⁿ`, `n = dim X`. So
"`g` is holomorphic on `U`" is stated as: `g ∘ e⁻¹` is `C^ω` on `e(U ∩ source e)` for every
algebraic chart `e`; and "`dg` is nowhere zero on `Y`" as: the derivative of `g ∘ e⁻¹` at `e(y)`
is non-zero for every `y ∈ Y` and every algebraic chart `e` around `y`. That `Y` is a closed
complex submanifold of `U` of codimension one is stated by a holomorphic chart of `U`, the
composite of an algebraic chart and a biholomorphism `ψ` onto an open subset of `ℂ × ℂⁿ⁻¹`, whose
first coordinate is `g`; in it, `Y` is the hyperplane `{0} × ℂⁿ⁻¹`.

The variety `X` is an integral scheme locally of finite type and quasi-compact over `ℂ`. The
irreducible components of `V(h) = X₀ - D(h)` are its maximal irreducible subsets, and `Z` is
the closed subscheme of `X`, given by an ideal sheaf with integral subscheme, whose trace on `X₀`
is the given component; its generic point is the image of the generic point of `Z.subscheme`.
`ord_Z(h)` is the order of vanishing `AlgebraicGeometry.Scheme.ord` of the rational function `h`
at that generic point, a point of coheight one. `Z_reg` is the image of the regular locus of
`Z.subscheme`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology IsLocalRing Set
open scoped ContDiff

namespace MMP

namespace UnderlyingSpace

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- Reading a function in another algebraic chart preserves the non-vanishing of its
differential. -/
theorem fderiv_comp_symm_ne_zero_of_isAlgebraicChart {n : ℕ}
    {e e₀ : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n))}
    (he : IsAlgebraicChart e) (he₀ : IsAlgebraicChart e₀) {g₀ : EuclideanSpace ℂ (Fin n) → ℂ}
    {p : UnderlyingSpace ℂ X} (hpe : p ∈ e.source) (hpe₀ : p ∈ e₀.source)
    (hgd : DifferentiableAt ℂ g₀ (e₀ p)) (hdg : fderiv ℂ g₀ (e₀ p) ≠ 0) :
    fderiv ℂ (g₀ ∘ e₀ ∘ e.symm) (e p) ≠ 0 := by
  set T := e.symm.trans e₀
  set T' := e₀.symm.trans e
  have hkT : e p ∈ T.source :=
    ⟨e.map_source hpe, show e.symm (e p) ∈ e₀.source by rwa [e.left_inv hpe]⟩
  have hTk : T (e p) = e₀ p := by
    change e₀ (e.symm (e p)) = _
    rw [e.left_inv hpe]
  have hk'T' : e₀ p ∈ T'.source :=
    ⟨e₀.map_source hpe₀, show e₀.symm (e₀ p) ∈ e.source by rwa [e₀.left_inv hpe₀]⟩
  have hT'k : T' (e₀ p) = e p := by
    change e (e₀.symm (e₀ p)) = _
    rw [e₀.left_inv hpe₀]
  have hTd : DifferentiableAt ℂ T (e p) :=
    ((he.contDiffOn_symm_trans he₀).contDiffAt (T.open_source.mem_nhds hkT)).differentiableAt
      (by simp)
  have hT'd : DifferentiableAt ℂ T' (e₀ p) :=
    ((he₀.contDiffOn_symm_trans he).contDiffAt (T'.open_source.mem_nhds hk'T')).differentiableAt
      (by simp)
  have hcomp : (fderiv ℂ T (e p)).comp (fderiv ℂ T' (e₀ p)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) := by
    have heq : (T ∘ T') =ᶠ[𝓝 (e₀ p)] id := by
      filter_upwards [T'.open_source.mem_nhds hk'T'] with q hq
      change e₀ (e.symm (e (e₀.symm q))) = q
      have h₁ : e₀.symm q ∈ e.source := hq.2
      have h₂ : q ∈ e₀.target := hq.1
      rw [e.left_inv h₁, e₀.right_inv h₂]
    have := heq.fderiv_eq (𝕜 := ℂ)
    rwa [fderiv_id, fderiv_comp _ (by rwa [hT'k]) hT'd, hT'k] at this
  intro h0
  apply hdg
  calc fderiv ℂ g₀ (e₀ p)
      = (fderiv ℂ g₀ (e₀ p)).comp ((fderiv ℂ T (e p)).comp (fderiv ℂ T' (e₀ p))) := by
        rw [hcomp, ContinuousLinearMap.comp_id]
    _ = (fderiv ℂ (g₀ ∘ T) (e p)).comp (fderiv ℂ T' (e₀ p)) := by
        rw [fderiv_comp _ (by rwa [hTk]) hTd, hTk, ContinuousLinearMap.comp_assoc]
    _ = 0 := by rw [show g₀ ∘ T = g₀ ∘ e₀ ∘ e.symm from rfl, h0, ContinuousLinearMap.zero_comp]

/-- The source of a chart `e.trans ψ` whose second factor has non-empty convex target is
connected. -/
theorem isConnected_trans_source {M E F : Type*} [TopologicalSpace M] [TopologicalSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : OpenPartialHomeomorph M E)
    (ψ : OpenPartialHomeomorph E F) (hψ : ψ.source ⊆ e.target) (hconv : Convex ℝ ψ.target)
    (hne : ψ.target.Nonempty) : IsConnected (e.source ∩ e ⁻¹' ψ.source) := by
  have hφt : (e.trans ψ).target = ψ.target := by
    rw [OpenPartialHomeomorph.trans_target]
    exact inter_eq_left.2 fun z hz ↦ hψ (ψ.map_target hz)
  have := (show IsConnected ψ.target from ⟨hne, hconv.isPreconnected⟩).image (e.trans ψ).symm
    (hφt ▸ (e.trans ψ).continuousOn_symm)
  rwa [← hφt, (e.trans ψ).symm_image_target_eq_source] at this

/-- In the source of a chart `e.trans ψ` with values in `ℂ × F` and convex target, the locus where
the first coordinate vanishes is connected when non-empty. -/
theorem isConnected_trans_source_inter_fst_eq_zero {M E F : Type*} [TopologicalSpace M]
    [TopologicalSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : OpenPartialHomeomorph M E)
    (ψ : OpenPartialHomeomorph E (ℂ × F)) (hψ : ψ.source ⊆ e.target) (hconv : Convex ℝ ψ.target)
    (hne : (e.source ∩ e ⁻¹' ψ.source ∩ {p | (ψ (e p)).1 = 0}).Nonempty) :
    IsConnected (e.source ∩ e ⁻¹' ψ.source ∩ {p | (ψ (e p)).1 = 0}) := by
  set φ := e.trans ψ
  have hφt : φ.target = ψ.target := by
    rw [OpenPartialHomeomorph.trans_target]
    exact inter_eq_left.2 fun z hz ↦ hψ (ψ.map_target hz)
  have hS : e.source ∩ e ⁻¹' ψ.source ∩ {p | (ψ (e p)).1 = 0} =
      φ.symm '' (ψ.target ∩ {z | z.1 = 0}) := by
    ext p
    constructor
    · rintro ⟨hp, hp0⟩
      exact ⟨φ p, ⟨hφt ▸ φ.map_source hp, hp0⟩, φ.left_inv hp⟩
    · rintro ⟨z, ⟨hzt, hz0⟩, rfl⟩
      have hz : z ∈ φ.target := hφt ▸ hzt
      refine ⟨φ.map_target hz, ?_⟩
      change (φ (φ.symm z)).1 = 0
      rwa [φ.right_inv hz]
  have hH : Convex ℝ (ψ.target ∩ {z : ℂ × F | z.1 = 0}) := hconv.inter
    ((convex_singleton (0 : ℂ)).linear_preimage (LinearMap.fst ℝ ℂ F))
  rw [hS] at hne ⊢
  have hHc : IsConnected (ψ.target ∩ {z : ℂ × F | z.1 = 0}) :=
    ⟨image_nonempty.1 hne, hH.isPreconnected⟩
  exact hHc.image _ (φ.continuousOn_symm.mono (hφt ▸ inter_subset_left))

/-- If `g` is continuous on `U` and `g = c` cuts out `P` on `U`, then `U ∩ {p | P p}` is closed
in `U`. -/
theorem isClosed_preimage_coe_inter_setOf {M β : Type*} [TopologicalSpace M] [TopologicalSpace β]
    [T1Space β] {U : Set M} {g : M → β} {c : β} (hg : ContinuousOn g U) {P : M → Prop}
    (hP : ∀ p ∈ U, g p = c ↔ P p) : IsClosed (((↑) : U → M) ⁻¹' (U ∩ {p | P p})) := by
  have : ((↑) : U → M) ⁻¹' (U ∩ {p | P p}) = (U.domRestrict g) ⁻¹' {c} := by
    ext q
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hq ↦ (hP q q.2).2 hq.2, fun hq ↦ ⟨q.2, (hP q q.2).1 hq⟩⟩
  rw [this]
  exact isClosed_singleton.preimage (continuousOn_iff_continuous_domRestrict.1 hg)

/-- If `D(s)` meets `Z` at its generic point, is regular, and `π` cuts out a regular divisor of
`D(s)` through it, then some closed point `p₀ ∈ D(s)` with `π(p₀) = 0` has an algebraic chart in
which `dπ` does not vanish at `p₀`. -/
theorem exists_chartDeriv_ne_zero_of_uniformizer [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] {n : ℕ}
    (hn : (n : WithBot ℕ∞) = Intersection.Scheme.dimension X) {X₀ : X.Opens}
    (hX₀ : IsAffineOpen X₀) (V : Intersection.Scheme.Subvariety X) {s π : Γ(X, X₀)}
    (hπ0 : π ≠ 0) (hηs : V.genericPoint ∈ X.basicOpen s) (hηπ : V.genericPoint ∉ X.basicOpen π)
    (hsreg : ∀ x ∈ X.basicOpen s, x ∈ regularLocus X)
    (hsquot : ∀ (x : X) (hx : x ∈ X.basicOpen s), x ∉ X.basicOpen π →
      IsRegularLocalRing (X.presheaf.stalk x ⧸
        Ideal.span {X.presheaf.germ X₀ x (X.basicOpen_le s hx) π})) :
    ∃ (p₀ : UnderlyingSpace ℂ X)
      (e₀ : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n))),
      IsAlgebraicChart e₀ ∧ p₀ ∈ e₀.source ∧ ⊤ ≤ p₀.toHom ⁻¹ᵁ X.basicOpen s ∧
        evalExt X₀ π p₀ = 0 ∧ chartDeriv e₀ X₀ p₀ π ≠ 0 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have hlc : IsLocallyClosed ((X.basicOpen s : Set X) ∩ V.support) :=
    ⟨_, _, (X.basicOpen s).isOpen, V.isClosed_support, rfl⟩
  have hne : ((X.basicOpen s : Set X) ∩ V.support).Nonempty :=
    ⟨V.genericPoint, hηs, V.closure_genericPoint ▸ subset_closure rfl⟩
  obtain ⟨x₀, ⟨hx₀s, hx₀Z⟩, hx₀cl⟩ := nonempty_inter_closedPoints hne hlc
  obtain ⟨p₀, rfl⟩ : ∃ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) = x₀ :=
    ⟨(equivClosedPoints X).symm ⟨x₀, hx₀cl⟩, by
      rw [← equivClosedPoints_apply, Equiv.apply_symm_apply]⟩
  set x₀ := p₀.toHom (IsLocalRing.closedPoint ℂ) with hx₀
  have hp₀s : ⊤ ≤ p₀.toHom ⁻¹ᵁ X.basicOpen s := (top_le_preimage_iff _ _).2 hx₀s
  have hp₀X₀ : ⊤ ≤ p₀.toHom ⁻¹ᵁ X₀ :=
    hp₀s.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le s))
  have hx₀π : x₀ ∉ X.basicOpen π := fun hx ↦ by
    have hsp : V.genericPoint ⤳ x₀ := by
      rwa [specializes_iff_mem_closure, V.closure_genericPoint]
    exact hηπ (hsp.mem_open (X.basicOpen π).isOpen hx)
  have hπp₀ : evalExt X₀ π p₀ = 0 :=
    of_not_not fun hne0 ↦ hx₀π ((mem_basicOpen_iff_evalExt_ne_zero hp₀X₀ π).2 hne0)
  have hp₀reg : p₀ ∈ regularPart ℂ X := (mem_regularPart_iff p₀).2 (hsreg x₀ hx₀s)
  obtain ⟨e₀, hp₀e, he₀⟩ := exists_isAlgebraicChart_of_dimension_eq hn p₀ hp₀reg
  have hdπ : chartDeriv e₀ X₀ p₀ π ≠ 0 := by
    have : IsRegularLocalRing (X.presheaf.stalk x₀) := hsreg x₀ hx₀s
    have hdim : ringKrullDim (X.presheaf.stalk x₀) = n := by
      rw [ringKrullDim_stalk_eq_dimension_of_isClosed ℂ X x₀ hx₀cl, hn]
    refine chartDeriv_ne_zero_of_isRegularLocalRing_quotient (finrank_euclideanSpace_fin) he₀
      hp₀e hX₀ hp₀X₀ hdim π hπp₀ ?_ (hsquot x₀ hx₀s hx₀π)
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ hπ0 ?_
    exact germ_injective_of_isIntegral X _ _ (h0.trans (map_zero _).symm)
  exact ⟨p₀, e₀, he₀, hp₀e, hp₀s, hπp₀, hdπ⟩

/-- **Local normal form near a general point of a component of `V(h)`** (Fulton, §19.2). Let `X`
be a normal complex variety of dimension `n`, `X₀ ⊆ X` a non-empty affine open, `h ∈ Γ(X, X₀)`
non-zero, `Z` an integral closed subscheme of `X` (an ideal sheaf whose subscheme is integral)
such that `Z ∩ X₀` is an irreducible component of `V(h) = X₀ - D(h)`, and `r` the rational
function `h`. Then there are `m = ord_Z(h)`, the order of vanishing of `r` at the generic point
of `Z` (a point of coheight one), a connected
open subset `U ⊆ X₀(ℂ) ∩ X_reg(ℂ)` and a function `g`, holomorphic on `U`, such that, with
`Y = U ∩ V(h)`:

* `Y` is non-empty, lies over regular points of `Z` and misses every other component of `V(h)`;
* `Y` is connected and closed in `U`, and a holomorphic chart of `U` has first coordinate `g`, so
  that `Y` is a complex submanifold of `U` of codimension one;
* `g⁻¹(0) ∩ U = Y`, `dg` is nowhere zero on `Y`, and `h = gᵐ` on `U`. -/
theorem exists_localNormalForm [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [QuasiCompact (X ↘ Spec (.of ℂ))] [IsNormal X] {n : ℕ}
    (hn : (n : WithBot ℕ∞) = Intersection.Scheme.dimension X) {X₀ : X.Opens}
    (hX₀ : IsAffineOpen X₀) [Nonempty X₀] {h : Γ(X, X₀)} (hh : h ≠ 0)
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (hZ : Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h)
      ((Z.support : Set X) ∩ X₀))
    {r : X.functionFieldˣ}
    (hr : (r : X.functionField) = X.germToFunctionField X₀ h) :
    ∃ (m : ℕ) (U : Set (UnderlyingSpace ℂ X)) (g : UnderlyingSpace ℂ X → ℂ),
      (haveI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ));
        (m : ℤ) = X.ord (r : X.functionField) (Z.subschemeι (genericPoint Z.subscheme))) ∧
      Order.coheight (Z.subschemeι (genericPoint Z.subscheme)) = 1 ∧
      IsOpen U ∧ IsConnected U ∧
      (∀ p ∈ U, p.toHom (IsLocalRing.closedPoint ℂ) ∈ X₀) ∧ U ⊆ regularPart ℂ X ∧
      (∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)),
        IsAlgebraicChart e → ContDiffOn ℂ ω (g ∘ e.symm) (e.target ∩ e.symm ⁻¹' U)) ∧
      (U ∩ {p | evalExt X₀ h p = 0}).Nonempty ∧
      (∀ p ∈ U ∩ {p | evalExt X₀ h p = 0},
        ∃ z ∈ regularLocus Z.subscheme, Z.subschemeι z = p.toHom (IsLocalRing.closedPoint ℂ)) ∧
      (∀ T : Set X, Maximal (fun T : Set X ↦ IsIrreducible T ∧ T ⊆ (X₀ : Set X) \ X.basicOpen h) T →
        T ≠ (Z.support : Set X) ∩ X₀ →
        ∀ p ∈ U ∩ {p | evalExt X₀ h p = 0}, p.toHom (IsLocalRing.closedPoint ℂ) ∉ T) ∧
      IsConnected (U ∩ {p | evalExt X₀ h p = 0}) ∧
      IsClosed (((↑) : U → UnderlyingSpace ℂ X) ⁻¹' (U ∩ {p | evalExt X₀ h p = 0})) ∧
      (∃ (e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)))
        (ψ : OpenPartialHomeomorph (EuclideanSpace ℂ (Fin n))
          (ℂ × EuclideanSpace ℂ (Fin (n - 1)))),
        IsAlgebraicChart e ∧ ContDiffOn ℂ ω ψ ψ.source ∧ ContDiffOn ℂ ω ψ.symm ψ.target ∧
          U = e.source ∩ e ⁻¹' ψ.source ∧ ∀ p ∈ U, (ψ (e p)).1 = g p) ∧
      (∀ p ∈ U, g p = 0 ↔ evalExt X₀ h p = 0) ∧
      (∀ p ∈ U ∩ {p | evalExt X₀ h p = 0},
        ∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)),
          IsAlgebraicChart e → p ∈ e.source → fderiv ℂ (g ∘ e.symm) (e p) ≠ 0) ∧
      ∀ p ∈ U, evalExt X₀ h p = g p ^ m := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  set V : Intersection.Scheme.Subvariety X := ⟨Z, ‹_›⟩ with hV
  obtain ⟨s, π, t, u, m, hord, hco, hm, htu, hπ0, hηs, hηπ, hsle, hsreg, hsZ, hsquot⟩ :=
    LocalNormalForm.exists_uniformizer_of_maximal ℂ (Z := V) hX₀ hh hZ hr
  obtain ⟨p₀, e₀, he₀, hp₀e, hp₀s, hπp₀, hdπ⟩ :=
    exists_chartDeriv_ne_zero_of_uniformizer hn hX₀ V hπ0 hηs hηπ hsreg hsquot
  have hsX₀ : X.basicOpen s ≤ X₀ := X.basicOpen_le s
  have hle_s : ∀ q : UnderlyingSpace ℂ X, ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen s → ⊤ ≤ q.toHom ⁻¹ᵁ X₀ :=
    fun q hq ↦ hq.trans (Scheme.Hom.preimage_mono _ hsX₀)
  have hp₀X₀ : ⊤ ≤ p₀.toHom ⁻¹ᵁ X₀ := hle_s p₀ hp₀s
  have hval : ∀ q : UnderlyingSpace ℂ X, ⊤ ≤ q.toHom ⁻¹ᵁ X₀ →
      evalExt X₀ t q * evalExt X₀ h q = evalExt X₀ u q * evalExt X₀ π q ^ m := fun q hq ↦ by
    rw [← evalExt_mul hq, htu, evalExt_mul hq, evalExt_pow hq]
  have htne : ∀ q : UnderlyingSpace ℂ X, ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen s → evalExt X₀ t q ≠ 0 :=
    fun q hq ↦ (mem_basicOpen_iff_evalExt_ne_zero (hle_s q hq) t).1
      (hsle ((top_le_preimage_iff _ _).1 hq)).1
  have hune : ∀ q : UnderlyingSpace ℂ X, ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen s → evalExt X₀ u q ≠ 0 :=
    fun q hq ↦ (mem_basicOpen_iff_evalExt_ne_zero (hle_s q hq) u).1
      (hsle ((top_le_preimage_iff _ _).1 hq)).2
  set O := e₀.target ∩ e₀.symm ⁻¹' {q : UnderlyingSpace ℂ X | ⊤ ≤ q.toHom ⁻¹ᵁ X.basicOpen s}
  have hO : IsOpen O := e₀.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage _)
  have hk₀ : e₀ p₀ ∈ O := ⟨e₀.map_source hp₀e,
    show ⊤ ≤ (e₀.symm (e₀ p₀)).toHom ⁻¹ᵁ X.basicOpen s by rwa [e₀.left_inv hp₀e]⟩
  have hOX₀ : O ⊆ e₀.target ∩ e₀.symm ⁻¹' {q : UnderlyingSpace ℂ X | ⊤ ≤ q.toHom ⁻¹ᵁ X₀} :=
    fun k hk ↦ ⟨hk.1, hle_s _ hk.2⟩
  set πf : EuclideanSpace ℂ (Fin n) → ℂ := fun k ↦ evalExt X₀ π (e₀.symm k)
  set vf : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun k ↦ evalExt X₀ u (e₀.symm k) / evalExt X₀ t (e₀.symm k)
  have hπf : ContDiffOn ℂ ω πf O := (he₀.contDiffOn_evalExt X₀ π).mono hOX₀
  have hvf : ContDiffOn ℂ ω vf O :=
    ((he₀.contDiffOn_evalExt X₀ u).mono hOX₀).div ((he₀.contDiffOn_evalExt X₀ t).mono hOX₀)
      fun k hk ↦ htne _ hk.2
  have hvf0 : ∀ k ∈ O, vf k ≠ 0 := fun k hk ↦ div_ne_zero (hune _ hk.2) (htne _ hk.2)
  have hπf0 : πf (e₀ p₀) = 0 := by simp only [πf, e₀.left_inv hp₀e, hπp₀]
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exfalso
      apply hdπ
      ext v
      have : v = 0 := Subsingleton.elim _ _
      simp [this]
    · exact hpos
  have hF : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n - 1))) + 1 =
      Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) := by
    simp only [finrank_euclideanSpace_fin]
    omega
  obtain ⟨g₀, ψ, hk₀ψ, hψO, hψconv, hψC, hψsC, hg₀C, hψ1, hgm, hdg⟩ :=
    LocalNormalForm.exists_pow_eq_mul_pow_of_fderiv_ne_zero hF hO hk₀ hπf hvf hvf0 hπf0 hdπ hm
  set U := e₀.source ∩ e₀ ⁻¹' ψ.source with hUdef
  set g : UnderlyingSpace ℂ X → ℂ := fun p ↦ g₀ (e₀ p) with hgdef
  have hUs : ∀ p ∈ U, ⊤ ≤ p.toHom ⁻¹ᵁ X.basicOpen s := fun p hp ↦ by
    have := (hψO hp.2).2
    rwa [Set.mem_preimage, e₀.left_inv hp.1] at this
  have hUX₀ : ∀ p ∈ U, ⊤ ≤ p.toHom ⁻¹ᵁ X₀ := fun p hp ↦ hle_s p (hUs p hp)
  have hhg : ∀ p ∈ U, evalExt X₀ h p = g p ^ m := by
    intro p hp
    have h1 := hgm _ hp.2
    simp only [vf, πf, e₀.left_inv hp.1] at h1
    rw [← h1, div_mul_eq_mul_div, eq_div_iff (htne p (hUs p hp))]
    linear_combination hval p (hUX₀ p hp)
  have hgh : ∀ p ∈ U, g p = 0 ↔ evalExt X₀ h p = 0 := fun p hp ↦ by
    rw [hhg p hp, pow_eq_zero_iff hm.ne']
  have hπh : ∀ p ∈ U, evalExt X₀ h p = 0 → evalExt X₀ π p = 0 := fun p hp hp0 ↦ by
    have h1 := hval p (hUX₀ p hp)
    rw [hp0, mul_zero, eq_comm, mul_eq_zero] at h1
    exact pow_eq_zero_iff hm.ne' |>.1 (h1.resolve_left (hune p (hUs p hp)))
  have hp₀U : p₀ ∈ U := ⟨hp₀e, hk₀ψ⟩
  have hUconn : IsConnected U :=
    isConnected_trans_source e₀ ψ (fun k hk ↦ (hψO hk).1) hψconv ⟨_, ψ.map_source hk₀ψ⟩
  have hhp₀ : evalExt X₀ h p₀ = 0 := by
    have h1 := hval p₀ hp₀X₀
    rw [hπp₀, zero_pow hm.ne', mul_zero, mul_eq_zero] at h1
    exact h1.resolve_left (htne p₀ hp₀s)
  set Y := U ∩ {p | evalExt X₀ h p = 0} with hYdef
  have hYψ : Y = U ∩ {p | (ψ (e₀ p)).1 = 0} := by
    ext p
    simp only [Y, mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun hp ↦ ?_
    rw [hψ1 _ hp.2]
    exact (hgh p hp).symm
  have hYne : Y.Nonempty := ⟨p₀, hp₀U, hhp₀⟩
  have hYconn : IsConnected Y := by
    rw [hYψ] at hYne ⊢
    exact isConnected_trans_source_inter_fst_eq_zero e₀ ψ (fun k hk ↦ (hψO hk).1) hψconv hYne
  have hgC : ∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)),
      IsAlgebraicChart e → ContDiffOn ℂ ω (g ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := fun e he ↦
    hg₀C.comp ((he.contDiffOn_symm_trans he₀).mono fun k hk ↦ ⟨hk.1, hk.2.1⟩) fun k hk ↦ hk.2.2
  have hdgY : ∀ p ∈ Y, ∀ e : OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)),
      IsAlgebraicChart e → p ∈ e.source → fderiv ℂ (g ∘ e.symm) (e p) ≠ 0 :=
    fun p hp e he hpe ↦ fderiv_comp_symm_ne_zero_of_isAlgebraicChart he he₀ hpe hp.1.1
      ((hg₀C.contDiffAt (ψ.open_source.mem_nhds hp.1.2)).differentiableAt (by simp))
      (hdg _ hp.1.2)
  have hYπ : ∀ p ∈ Y, p.toHom (IsLocalRing.closedPoint ℂ) ∈ X.basicOpen s ∧
      p.toHom (IsLocalRing.closedPoint ℂ) ∉ X.basicOpen π := fun p hp ↦
    ⟨(top_le_preimage_iff _ _).1 (hUs p hp.1), fun hx ↦
      (mem_basicOpen_iff_evalExt_ne_zero (hUX₀ p hp.1) π).1 hx (hπh p hp.1 hp.2)⟩
  have hYcl : IsClosed (((↑) : U → UnderlyingSpace ℂ X) ⁻¹' Y) :=
    isClosed_preimage_coe_inter_setOf
      (hg₀C.continuousOn.comp (e₀.continuousOn.mono inter_subset_left) fun p hp ↦ hp.2) hgh
  refine ⟨m, U, g, hord, hco, e₀.isOpen_inter_preimage ψ.open_source, hUconn,
    fun p hp ↦ (top_le_preimage_iff _ _).1 (hUX₀ p hp),
    fun p hp ↦ (mem_regularPart_iff p).2 (hsreg _ ((top_le_preimage_iff _ _).1 (hUs p hp))),
    hgC, hYne, fun p hp ↦ (hsZ _ (hYπ p hp).1 (hYπ p hp).2).2.1,
    fun T hT hTne p hp ↦ (hsZ _ (hYπ p hp).1 (hYπ p hp).2).2.2 T hT hTne, hYconn, hYcl,
    ⟨e₀, ψ, he₀, hψC, hψsC, rfl, fun p hp ↦ hψ1 _ hp.2⟩, hgh, hdgY, hhg⟩

end UnderlyingSpace

end MMP
