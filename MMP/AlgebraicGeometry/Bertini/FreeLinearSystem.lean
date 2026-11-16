module
public import MMP.AlgebraicGeometry.Bertini.ReducedGeneralMember
public import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
public import MMP.AlgebraicGeometry.Resolution.SNCRestriction
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DerivedBoundaryCocycle
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueAbelianSheavesAreAcyclic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SupportedSheafCohomologyVanishing
public import MMP.AlgebraicGeometry.Analytic.ExponentialSequence

/-!
# Picard obstructions, inseparability exponents and Bertini theorems for free systems

This file collects four foundational results used by the minimal model program.

*The logarithmic obstruction sequence.* Let `X` be a quasi-compact scheme locally of finite type
over `ℂ` and `A = X^an` its analytification. The stalks of `𝒪_A` are local rings, and the
exponential sequence `0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0`, `u ↦ exp (2πi u)`, is exact. Composing the
inverse of the canonical isomorphism `H¹(A, 𝒪_A^×) ≃ Pic(A)` with its connecting map gives the
obstruction map `c_exp : Pic(A) → H²(A, ℤ_A)`; on transition functions `g_{ij}` it is the class
of the integer cocycle `ℓ_{ij} + ℓ_{jk} - ℓ_{ik}` built from local logarithms of the `g_{ij}`.
The sequence `Pic(A) → H²(A, ℤ_A) → H²(A, 𝒪_A)` is exact, so `c_exp` is surjective when
`H²(A, 𝒪_A) = 0`.

*A uniform inseparability exponent.* In a finite extension `F / K` of exponential characteristic
`p` there is one exponent `e` with `α ^ p ^ e` separable over `K` for every `α ∈ F`.

*Bertini theorems.* Let `k` be algebraically closed of characteristic zero, `X` a variety over
`k` and `V ⊆ H⁰(X, L)` a finite-dimensional system generating an invertible sheaf `L`. For a
general member `s ∈ V` the traces `Z(s) ∩ Yᵢ` on finitely many smooth locally closed subschemes
`Yᵢ` are smooth, and so is `Z(s)` when `X` is smooth. If moreover `G = ∑ᵢ Gᵢ` is a simple normal
crossing divisor on a smooth locally closed `Y ⊆ X`, the trace `H = Z(s) ∩ Y` is smooth,
contains no component of any stratum `⋂_{i ∈ J} Gᵢ`, and `H + G` has simple normal crossings.

## Main definitions

* `MMP.Analytic.picardObstruction`: the obstruction map `Pic(A) → H²(A, F)` of a short exact
  sequence `0 ⟶ F ⟶ M ⟶ 𝒪_A^× ⟶ 0`.

## Main results

* `MMP.Analytic.isLocalRing_stalk_analytification`: the stalks of `X^an` are local rings.
* `MMP.Analytic.exact_picardObstruction_analytification`: for `A = X^an`, exactness of
  `Pic(A) → H²(A, ℤ_A) → H²(A, 𝒪_A)` along the exponential sequence, and surjectivity of the
  obstruction map when `H²(A, 𝒪_A)` vanishes.
* `MMP.Analytic.exact_picardObstruction_of_shortExact`: the same exactness for any ringed space
  with local stalks and any short exact sequence ending in `𝒪_A^×`.
* `MMP.exists_pow_pow_mem_separableClosure`: the uniform inseparability exponent.
* `MMP.Threefold.Bridges.exists_dense_open_smooth_zeroScheme`: Bertini's theorem for smoothness
  of the general member of a free system.
* `MMP.Threefold.Bridges.exists_dense_open_isSNCFamily_zeroScheme`: Bertini's theorem for a free
  system relative to a simple normal crossing divisor.

## Implementation notes

The complex analytic spaces of the obstruction sequence are the analytifications `X^an`
(`MMP.Analytic.analytification`, with its full structure sheaf), and the exponential sequence
is `MMP.Analytic.exists_shortExact_exponentialSequence`, whose two maps are determined by the
formulas recorded in the statement: an integer goes to the constant section, the class of a
holomorphic germ `f` to the class of `exp(2πi f)`. The obstruction map is the connecting map
`Stacks.Thickenings.cohomologyBoundary` precomposed with the inverse of
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`, transported to `Ext` from the
constant sheaf by `Stacks.Thickenings.sheafCohomologyOneExtEquiv`. Since precomposing with a
surjection does not change the range, exactness is that of the long exact sequence at
`H²(A, ℤ_A)`. The isomorphism `H¹(A, 𝒪_A^×) ≃ Pic(A)` needs local stalks: a germ of `𝒪_{X^an}`
whose value at the point is nonzero is a unit, since on every chart it is the class of a
holomorphic function that vanishes nowhere nearby.

The characteristic hypothesis of the inseparability exponent is `ExpChar K p`, which allows the
trivial case `p = 1`; the exponent is that of `F` over `separableClosure K F`
(`IsPurelyInseparable.HasExponent`).

In the Bertini theorems, as in `MMP.Threefold.Bridges.exists_dense_open_isReduced_zeroScheme`,
the system is presented by spanning sections `s₀, …, s_N`, a member by its coefficient vector
`c`, and the parameter spaces are `MMP.Threefold.Bridges.coefficientSpace` and
`MMP.Threefold.Bridges.projectiveSpace`. A locally closed subscheme is an immersion `ι : Y ⟶ X`
and the trace of `Z(s)` on it is the ideal sheaf `(zeroScheme X L s).comap ι`; `H + G` is the
family `Option Λ → Y.IdealSheafData` sending `none` to `H`, and simple normal crossings is
`MMP.Resolution.IsSNCFamily`. The smoothness proof runs through the incidence scheme
`{(x, a) : ∑ aᵢ sᵢ(x) = 0}` of the system: its local rings are regular, so its projection to the
coefficient space is smooth over the generic point, hence (Chevalley) over a dense open. For
the snc statement the strata of `G` are smooth, so the smoothness theorem applies to them, and
`H + G` is snc once `H` is smooth on every stratum and contains no stratum component. Both
properties are invariant under scaling, which gives the projective opens.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §1]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.39
* [R. Hartshorne, *Algebraic geometry*][Hartshorne], III.10.9
-/

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

/-! ### Local rings of the analytification -/

namespace MMP.Analytic

open Analytification Filter Topology Opposite

section LocalStalks

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}

private lemma exists_rep {p : Fin n → ℂ} (g : holGerms p) :
    ∃ f : (Fin n → ℂ) → ℂ, (g : Germ (𝓝 p) ℂ) = f ∧ ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f, hf, hd⟩ := g.2
  exact ⟨f, hf.symm, hd⟩

private lemma eventually_differentiableAt_of_coe_eq {p : Fin n → ℂ} (g : holGerms p)
    {f : (Fin n → ℂ) → ℂ} (hf : (g : Germ (𝓝 p) ℂ) = f) :
    ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f', hf', hd⟩ := exists_rep g
  have heq : f' =ᶠ[𝓝 p] f := Germ.coe_eq.1 (hf'.symm.trans hf)
  exact (hd.and heq.eventuallyEq_nhds).mono fun y hy => hy.1.congr_of_eventuallyEq hy.2.symm

private lemma isUnit_of_value_ne_zero {p : Fin n → ℂ} (g : holGerms p)
    (hg : Germ.value (g : Germ (𝓝 p) ℂ) ≠ 0) : IsUnit g := by
  obtain ⟨f, hf, hd⟩ := exists_rep g
  rw [hf] at hg
  change f p ≠ 0 at hg
  have hne : ∀ᶠ y in 𝓝 p, f y ≠ 0 := hd.self_of_nhds.continuousAt.eventually_ne hg
  refine IsUnit.of_mul_eq_one (b := ⟨((f⁻¹ : (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ),
    coe_mem_holGerms ((hd.and hne).mono fun y hy => hy.1.inv hy.2)⟩) (Subtype.ext ?_)
  change (g : Germ (𝓝 p) ℂ) * ((f⁻¹ : (Fin n → ℂ) → ℂ) : Germ (𝓝 p) ℂ) = 1
  rw [hf, ← Germ.coe_mul]
  exact Germ.coe_eq.2 (hne.mono fun y hy => by simp [hy])

private lemma mk_surjective (c : Chart sX) (p : Fin c.n → ℂ) (a : c.StalkRing p) :
    ∃ g, Chart.StalkRing.mk c p g = a :=
  Ideal.Quotient.mk_surjective a

/-- The residue `𝒪_{U,y} → ℂ` at a `ℂ`-point `y` of a chart: the value at `z(y)`. -/
private noncomputable def residue (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U) :
    c.StalkRing (c.coords y) →+* ℂ :=
  Ideal.Quotient.lift (c.ideal.map (polyGermHom (c.coords y)))
    ((Germ.valueRingHom).comp (holGerms (c.coords y)).subtype) (by
      have : c.ideal.map (polyGermHom (c.coords y)) ≤
          RingHom.ker ((Germ.valueRingHom).comp (holGerms (c.coords y)).subtype) := by
        rw [Ideal.map_le_iff_le_comap]
        intro q hq
        rw [Ideal.mem_comap, RingHom.mem_ker]
        change MvPolynomial.eval (c.coords y) q = 0
        rw [← c.evalHom_pres, (RingHom.mem_ker).1 hq, map_zero]
      exact fun g hg => this hg)

private lemma residue_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (g : holGerms (c.coords y)) :
    residue c y (Chart.StalkRing.mk c _ g) = Germ.value (g : Germ (𝓝 (c.coords y)) ℂ) :=
  Ideal.Quotient.lift_mk _ _ _

private lemma residue_of_eq_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    {a : c.StalkRing (c.coords y)} {g : holGerms (c.coords y)} {f : (Fin c.n → ℂ) → ℂ}
    (ha : a = Chart.StalkRing.mk c _ g) (hg : (g : Germ (𝓝 (c.coords y)) ℂ) = f) :
    residue c y a = f (c.coords y) := by
  rw [ha, residue_mk, hg]
  rfl

private lemma residue_transition {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (a : c.StalkRing (c.coords (m.incl y))) :
    residue d y (m.transition y a) = residue c (m.incl y) a := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  obtain ⟨f, hf, -⟩ := exists_rep g
  rw [m.transition_mk, residue_mk, residue_mk, coe_holPullback, hf, Germ.coe_compTendsto]
  change f (m.polyMap (d.coords y)) = f (c.coords (m.incl y))
  rw [m.coords_incl]

/-- An element of the local ring of a chart with nonzero residue is a unit. -/
private lemma isUnit_of_residue_ne_zero (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (a : c.StalkRing (c.coords y)) (ha : residue c y a ≠ 0) : IsUnit a := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  rw [residue_mk] at ha
  exact (isUnit_of_value_ne_zero g ha).map _

/-- For `X` locally of finite type over `ℂ`, the sections over an affine open are a finitely
generated `ℂ`-algebra. -/
private lemma exists_gens [LocallyOfFiniteType sX] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (gen : Fin n → Γ(X, U)),
      Function.Surjective (MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen) := by
  have h₁ : (sX.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (f := sX) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (ComplexPoints.baseRingHom sX U).FiniteType := by
    have : ComplexPoints.baseRingHom sX U =
        (sX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom := rfl
    rw [this]
    exact h₁.comp (RingHom.FiniteType.of_surjective _ fun a =>
      ⟨(Scheme.ΓSpecIso (.of ℂ)).hom a, Iso.hom_inv_id_apply _ a⟩)
  let _ := (ComplexPoints.baseRingHom sX U).toAlgebra
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h₂
  refine ⟨n, fun i => φ (MvPolynomial.X i), ?_⟩
  have : MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U)
      (fun i => φ (MvPolynomial.X i)) = φ.toRingHom :=
    MvPolynomial.ringHom_ext (fun a => by simp [RingHom.algebraMap_toAlgebra])
      (fun i => by simp)
  rwa [this]

/-- For `X` locally of finite type over `ℂ`, every `ℂ`-point lies in a chart. -/
private lemma exists_chart [LocallyOfFiniteType sX] (x : space sX) :
    ∃ c : Chart sX, x ∈ ComplexPoints.chart c.U := by
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (Opens.mem_top (ComplexPoints.toScheme x))
  obtain ⟨n, gen, h⟩ := exists_gens (sX := sX) hU
  exact ⟨⟨U, hU, n, gen, h⟩, ComplexPoints.mem_chart_iff.2 hxU⟩

/-- Two charts at a point are refined by a third. -/
private lemma exists_chartHom_chartHom [LocallyOfFiniteType sX] (c d : Chart sX)
    {y : ComplexPoints sX} (hc : y ∈ ComplexPoints.chart c.U)
    (hd : y ∈ ComplexPoints.chart d.U) :
    ∃ (e : Chart sX) (_ : ChartHom c e) (_ : ChartHom d e), y ∈ ComplexPoints.chart e.U := by
  obtain ⟨U, hU, hyU, hUcd⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := c.U ⊓ d.U) (x := y.toScheme)
    ⟨ComplexPoints.mem_chart_iff.1 hc, ComplexPoints.mem_chart_iff.1 hd⟩
  obtain ⟨k, g, hg⟩ := exists_gens (sX := sX) hU
  let gen : Fin (c.n + d.n + k) → Γ(X, U) :=
    Fin.append (Fin.append
      (fun i => X.presheaf.map (homOfLE (hUcd.trans inf_le_left)).op (c.gen i))
      (fun j => X.presheaf.map (homOfLE (hUcd.trans inf_le_right)).op (d.gen j))) g
  have hsurj : Function.Surjective
      (MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen) := by
    intro a
    obtain ⟨q, rfl⟩ := hg a
    refine ⟨MvPolynomial.rename (Fin.natAdd (c.n + d.n)) q, ?_⟩
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
    congr 1
    funext i
    exact Fin.append_right _ _ i
  let e : Chart sX := ⟨U, hU, c.n + d.n + k, gen, hsurj⟩
  refine ⟨e, ⟨hUcd.trans inf_le_left,
    fun i => MvPolynomial.X (Fin.castAdd k (Fin.castAdd d.n i)), fun i => ?_⟩,
    ⟨hUcd.trans inf_le_right, fun j => MvPolynomial.X (Fin.castAdd k (Fin.natAdd c.n j)),
      fun j => ?_⟩, ComplexPoints.mem_chart_iff.2 hyU⟩
  · change _ = MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen (MvPolynomial.X _)
    rw [MvPolynomial.eval₂Hom_X']
    simp only [gen, Fin.append_left]
  · change _ = MvPolynomial.eval₂Hom (ComplexPoints.baseRingHom sX U) gen (MvPolynomial.X _)
    rw [MvPolynomial.eval₂Hom_X']
    simp only [gen, Fin.append_left, Fin.append_right]

/-- For a compatible family, the residue at a point does not depend on the chart. -/
private lemma residue_eq_of_isCompatible [LocallyOfFiniteType sX] {W : Opens (space sX)}
    {s : ∀ x : W, Fibre x.1} (hs : IsCompatible s) (x : W) (c d : Chart sX)
    (hc : x.1 ∈ ComplexPoints.chart c.U) (hd : x.1 ∈ ComplexPoints.chart d.U) :
    residue c ⟨x.1, hc⟩ (s x ⟨c, hc⟩) = residue d ⟨x.1, hd⟩ (s x ⟨d, hd⟩) := by
  obtain ⟨e, m₁, m₂, he⟩ := exists_chartHom_chartHom c d hc hd
  exact ((residue_transition m₁ ⟨x.1, he⟩ _).symm.trans (congrArg _ (hs c e m₁ x he))).trans
    ((congrArg _ (hs d e m₂ x he)).symm.trans (residue_transition m₂ ⟨x.1, he⟩ _))

/-- The `ℂ`-points of an open `U` at which the value of a section `f ∈ Γ(X, U)` lies in an open
set form an open subset of `X(ℂ)`. -/
private lemma isOpen_setOf_evalHom_mem (U : X.Opens) (f : Γ(X, U)) {T : Set ℂ}
    (hT : IsOpen T) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ ComplexPoints.chart U,
      ComplexPoints.evalHom U ⟨y, hy⟩ f ∈ T} := by
  rw [ComplexPoints.isOpen_iff]
  intro U'
  let _ := ComplexPoints.chartTopology (sX := sX) (U' : X.Opens)
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨hyU, hyT⟩
  obtain ⟨g, hgU, hyg⟩ := U'.2.exists_basicOpen_le
    ⟨y.1.toScheme, ComplexPoints.mem_chart_iff.1 hyU⟩ (ComplexPoints.mem_chart_iff.1 y.2)
  have := U'.2.isLocalization_basicOpen g
  obtain ⟨⟨a, _, k, rfl⟩, hak⟩ := IsLocalization.mk'_surjective (Submonoid.powers g)
    (X.presheaf.map (homOfLE hgU).op f)
  have hval : ∀ z : ComplexPoints.chart (sX := sX) (U' : X.Opens),
      ComplexPoints.evalHom (U' : X.Opens) z g ≠ 0 →
        ∃ hzU : z.1 ∈ ComplexPoints.chart U, ComplexPoints.evalHom U ⟨z.1, hzU⟩ f =
          ComplexPoints.evalHom (U' : X.Opens) z a /
            ComplexPoints.evalHom (U' : X.Opens) z g ^ k := by
    intro z hz
    have hzD : z.1.toScheme ∈ X.basicOpen g := (ComplexPoints.toScheme_mem_basicOpen_iff z g).2 hz
    let zB : ComplexPoints.chart (sX := sX) (X.basicOpen g) :=
      ⟨z.1, ComplexPoints.mem_chart_iff.2 hzD⟩
    have hres : ∀ b : Γ(X, (U' : X.Opens)), ComplexPoints.evalHom (U' : X.Opens) z b =
        ComplexPoints.evalHom (X.basicOpen g) zB
          (algebraMap Γ(X, (U' : X.Opens)) Γ(X, X.basicOpen g) b) :=
      fun b => ComplexPoints.evalHom_res (X.basicOpen_le g) zB b
    refine ⟨ComplexPoints.mem_chart_iff.2 (hgU hzD), ?_⟩
    rw [ComplexPoints.evalHom_res hgU zB f, ← hak, eq_div_iff (pow_ne_zero _ hz), hres, hres,
      ← map_pow, ← map_mul, ← map_pow, IsLocalization.mk'_spec]
  refine ⟨{z | ComplexPoints.evalHom (U' : X.Opens) z g ≠ 0} ∩
      (fun z => ComplexPoints.evalHom (U' : X.Opens) z a /
        ComplexPoints.evalHom (U' : X.Opens) z g ^ k) ⁻¹' T, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hzT⟩
    obtain ⟨hzU, hzv⟩ := hval z hz
    exact ⟨hzU, by rwa [hzv]⟩
  · refine ContinuousOn.isOpen_inter_preimage ?_
      (isOpen_compl_singleton.preimage (ComplexPoints.continuous_eval _ g)) hT
    exact (ComplexPoints.continuous_eval _ a).continuousOn.div
      ((ComplexPoints.continuous_eval _ g).pow k).continuousOn fun z hz => pow_ne_zero _ hz
  · have hy : ComplexPoints.evalHom (U' : X.Opens) y g ≠ 0 :=
      (ComplexPoints.toScheme_mem_basicOpen_iff y g).1 hyg
    obtain ⟨_, hyv⟩ := hval y hy
    exact ⟨hy, by rwa [Set.mem_preimage, ← hyv]⟩

/-- A subset of the `ℂ`-points of an affine open, open for its chart topology, is open in
`X(ℂ)`. -/
private lemma isOpen_setOf_mem_chart (U : X.affineOpens)
    {O : Set (ComplexPoints.chart (sX := sX) (U : X.Opens))}
    (hO : IsOpen[ComplexPoints.chartTopology (U : X.Opens)] O) :
    IsOpen {y : ComplexPoints sX | ∃ hy : y ∈ ComplexPoints.chart (U : X.Opens), ⟨y, hy⟩ ∈ O} := by
  have hS : IsOpen (ComplexPoints.chart (sX := sX) (U : X.Opens)) := by
    have : ComplexPoints.chart (sX := sX) (U : X.Opens) =
        ComplexPoints.toScheme ⁻¹' ((U : X.Opens) : Set X) :=
      Set.ext fun _ => ComplexPoints.mem_chart_iff
    rw [this]
    exact (U : X.Opens).2.preimage ComplexPoints.continuous_toScheme
  have hid : @Continuous _ _ instTopologicalSpaceSubtype
      (ComplexPoints.chartTopology (U : X.Opens))
      (id : ComplexPoints.chart (sX := sX) (U : X.Opens) → _) := by
    refine continuous_iInf_rng.2 fun f => continuous_induced_rng.2 ?_
    refine continuous_def.2 fun T hT => ?_
    convert (isOpen_setOf_evalHom_mem (sX := sX) (U : X.Opens) f hT).preimage
      continuous_subtype_val using 1
    ext q
    exact ⟨fun h => ⟨q.2, h⟩, fun ⟨_, h⟩ => h⟩
  convert hS.isOpenMap_subtype_val _
    (@IsOpen.preimage _ _ instTopologicalSpaceSubtype (ComplexPoints.chartTopology _) _ hid _ hO)
    using 1
  ext y
  exact ⟨fun ⟨hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨q, hq, e⟩ => e ▸ ⟨q.2, hq⟩⟩

/-- A neighbourhood, in the chart topology, of a point of a chart, on which the coordinates lie
in a prescribed neighbourhood, contains an open of `X(ℂ)` around the point. -/
private lemma exists_opens_of_mem_chart (c : Chart sX)
    {O : Set (ComplexPoints.chart (sX := sX) c.U)}
    (hO : IsOpen[ComplexPoints.chartTopology c.U] O) (y : ComplexPoints.chart (sX := sX) c.U)
    (hy : y ∈ O) {N : Set (Fin c.n → ℂ)} (hN : N ∈ 𝓝 (c.coords y)) :
    ∃ V : Opens (space sX), y.1 ∈ V ∧ ∀ z ∈ V, ∃ hz : z ∈ ComplexPoints.chart c.U,
      ⟨z, hz⟩ ∈ O ∧ c.coords ⟨z, hz⟩ ∈ N := by
  let _ := ComplexPoints.chartTopology (sX := sX) c.U
  obtain ⟨B, hBN, hB, hyB⟩ := mem_nhds_iff.1 hN
  have hcont : Continuous c.coords :=
    continuous_pi fun i => ComplexPoints.continuous_eval c.U (c.gen i)
  have hO' : IsOpen (O ∩ c.coords ⁻¹' B) := hO.inter (hB.preimage hcont)
  refine ⟨⟨_, isOpen_setOf_mem_chart ⟨c.U, c.isAffineOpen⟩ hO'⟩, ⟨y.2, hy, hyB⟩, ?_⟩
  rintro z ⟨hz, hzO, hzB⟩
  exact ⟨hz, hzO, hBN hzB⟩

/-- The residue of a section of `𝒪_{X^an}` is continuous: near a point `x`, its residues in
every chart lie in any prescribed neighbourhood of its residue at `x`. -/
private lemma exists_opens_residue_mem [LocallyOfFiniteType sX] {W : Opens (space sX)}
    (s : sections sX W) (x : W) (c : Chart sX) (hc : x.1 ∈ ComplexPoints.chart c.U) {N : Set ℂ}
    (hN : N ∈ 𝓝 (residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩))) :
    ∃ V : Opens (space sX), x.1 ∈ V ∧ ∀ y : W, y.1 ∈ V → ∀ (d : Chart sX)
      (hd : y.1 ∈ ComplexPoints.chart d.U), residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩) ∈ N := by
  obtain ⟨O, hO, hxO, h, hh⟩ := s.2.1 c x hc
  have hres : ∀ y ∈ O, ∀ hyW : y.1 ∈ W,
      residue c y (s.1 ⟨y.1, hyW⟩ ⟨c, y.2⟩) = h (c.coords y) := fun y hy _ => by
    obtain ⟨_, g, hg, hsg⟩ := hh y hy
    exact residue_of_eq_mk c y hsg hg
  obtain ⟨_, g₀, hg₀, -⟩ := hh _ hxO
  rw [hres _ hxO x.2] at hN
  obtain ⟨V, hxV, hV⟩ := exists_opens_of_mem_chart c hO _ hxO
    ((eventually_differentiableAt_of_coe_eq g₀ hg₀).self_of_nhds.continuousAt.preimage_mem_nhds hN)
  refine ⟨V, hxV, fun y hyV d hd => ?_⟩
  obtain ⟨hyc, hyO, hyN⟩ := hV y.1 hyV
  rwa [residue_eq_of_isCompatible s.2.2 y d c hd hyc, hres _ hyO]

/-- A section of `𝒪_{X^an}` whose residues vanish nowhere is a unit. -/
private lemma isUnit_of_forall_residue_ne_zero {W : Opens (space sX)} (s : sections sX W)
    (hs : ∀ (y : W) (d : Chart sX) (hd : y.1 ∈ ComplexPoints.chart d.U),
      residue d ⟨y.1, hd⟩ (s.1 y ⟨d, hd⟩) ≠ 0) :
    IsUnit s := by
  have hu : ∀ (y : W) (d : {c : Chart sX // y.1 ∈ ComplexPoints.chart c.U}),
      IsUnit (s.1 y d) := fun y d =>
    isUnit_of_residue_ne_zero d.1 ⟨y.1, d.2⟩ _ (hs y d.1 d.2)
  let t : ∀ y : W, Fibre y.1 := fun y d => ↑(hu y d).unit⁻¹
  have hmul : ∀ y d, s.1 y d * t y d = 1 := fun y d => (hu y d).mul_val_inv
  have hcompat : IsCompatible t := by
    intro c d m x hx
    refine (hu x ⟨d, hx⟩).mul_left_cancel ?_
    rw [hmul x ⟨d, hx⟩, ← s.2.2 c d m x hx]
    exact ((map_mul (m.transition ⟨x.1, hx⟩) _ _).symm.trans
      (congrArg _ (hmul x ⟨c, ComplexPoints.chart_mono m.le hx⟩))).trans (map_one _)
  have hloc : IsLocallyHolomorphic t := by
    intro c x hx
    obtain ⟨O, hO, hxO, h, hh⟩ := s.2.1 c x hx
    refine ⟨O, hO, hxO, h⁻¹, fun y hy => ?_⟩
    obtain ⟨hyW, g, hg, hsg⟩ := hh y hy
    have hne : h (c.coords y) ≠ 0 := by
      have := hs ⟨y.1, hyW⟩ c y.2
      rwa [residue_of_eq_mk c y hsg hg] at this
    have hd := eventually_differentiableAt_of_coe_eq g hg
    have hne' : ∀ᶠ z in 𝓝 (c.coords y), h z ≠ 0 := hd.self_of_nhds.continuousAt.eventually_ne hne
    let g' : holGerms (c.coords y) := ⟨((h⁻¹ : (Fin c.n → ℂ) → ℂ) : Germ (𝓝 (c.coords y)) ℂ),
      coe_mem_holGerms ((hd.and hne').mono fun z hz => hz.1.inv hz.2)⟩
    have hgg' : g * g' = 1 := by
      apply Subtype.ext
      change (g : Germ (𝓝 (c.coords y)) ℂ) * ((h⁻¹ : (Fin c.n → ℂ) → ℂ) : Germ _ ℂ) = 1
      rw [hg, ← Germ.coe_mul]
      exact Germ.coe_eq.2 (hne'.mono fun z hz => by simp [hz])
    refine ⟨hyW, g', rfl, (hu ⟨y.1, hyW⟩ ⟨c, y.2⟩).mul_left_cancel ?_⟩
    rw [hmul, hsg, ← map_mul, hgg', map_one]
  exact IsUnit.of_mul_eq_one (b := ⟨t, hloc, hcompat⟩)
    (Subtype.ext (funext fun y => funext fun d => hmul y d))

/-- The stalks of the analytification `X^an` of a scheme `X` locally of finite type over `ℂ`
are local rings: a germ is a unit exactly when its value at the point is nonzero. -/
public instance isLocalRing_stalk_analytification [LocallyOfFiniteType sX] (x : space sX) :
    IsLocalRing ((analytification sX).presheaf.stalk x) := by
  obtain ⟨c, hc⟩ := exists_chart (sX := sX) x
  let F : TopCat.Presheaf CommRingCat.{0} (space sX) := (structureSheaf sX).obj
  let v : ∀ {U : Opens (space sX)} (_ : x ∈ U), sections sX U → ℂ := fun hxU s =>
    residue c ⟨x, hc⟩ (s.1 ⟨x, hxU⟩ ⟨c, hc⟩)
  have key : ∀ (U : Opens (space sX)) (hxU : x ∈ U) (s : sections sX U), v hxU s ≠ 0 →
      IsUnit (F.germ U x hxU s) := by
    intro U hxU s hs
    obtain ⟨V, hxV, hV⟩ := exists_opens_residue_mem s ⟨x, hxU⟩ c hc
      (isOpen_compl_singleton.mem_nhds hs)
    have hu : IsUnit (restrictHom (inf_le_right : V ⊓ U ≤ U) s) :=
      isUnit_of_forall_residue_ne_zero _ fun y d hd => hV ⟨y.1, y.2.2⟩ y.2.1 d hd
    have h2 := hu.map (F.germ (V ⊓ U) x ⟨hxV, hxU⟩).hom
    have h3 := TopCat.Presheaf.germ_res_apply F (homOfLE (inf_le_right : V ⊓ U ≤ U)) x
      ⟨hxV, hxU⟩ s
    exact h3 ▸ h2
  have : Nontrivial ((analytification sX).presheaf.stalk x) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : F.germ ⊤ x trivial (0 : sections sX ⊤) = F.germ ⊤ x trivial (1 : sections sX ⊤) :=
      (map_zero _).trans (h.trans (map_one _).symm)
    obtain ⟨V, hxV, i, j, hV⟩ :=
      TopCat.Presheaf.germ_eq F (U := ⊤) (V := ⊤) x trivial trivial _ _ h'
    have hV' : (0 : sections sX V) = 1 :=
      ((map_zero (F.map i.op).hom).symm.trans hV).trans (map_one (F.map j.op).hom)
    have := congrArg (v hxV) hV'
    change residue c ⟨x, hc⟩ 0 = residue c ⟨x, hc⟩ 1 at this
    rw [map_zero, map_one] at this
    exact zero_ne_one this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F a
  by_cases hs : v hxU s = 0
  · right
    have h1 : (1 : (analytification sX).presheaf.stalk x) - F.germ U x hxU s =
        F.germ U x hxU (1 - s) := by
      rw [map_sub, map_one]
    rw [h1]
    refine key U hxU (1 - (show sections sX U from s)) ?_
    change residue c ⟨x, hc⟩ (1 - s.1 ⟨x, hxU⟩ ⟨c, hc⟩) ≠ 0
    rw [map_sub, map_one]
    change 1 - v hxU s ≠ 0
    rw [hs, sub_zero]
    exact one_ne_zero
  · exact Or.inl (key U hxU s hs)

end LocalStalks

/-! ### The logarithmic obstruction sequence -/

section

attribute [local instance] hasExt_of_enoughInjectives
  Stacks.Cohomology.Generators.picardGroupAddCommGroup
attribute [local implicit_reducible] TopCat.Sheaf

/-- Precomposing with a surjection does not change the range, so it preserves exactness. -/
private lemma exact_comp_of_surjective {A B C D : Type*} [Zero D] {f : A → B} {g : B → C}
    {h : C → D} (hgh : Function.Exact g h) (hf : Function.Surjective f) :
    Function.Exact (g ∘ f) h := fun y => by
  rw [hgh y, hf.range_comp]

/-- The **obstruction map** `Pic(A) → H²(A, F)` of a short exact sequence of sheaves of abelian
groups `0 ⟶ F ⟶ M ⟶ 𝒪_A^× ⟶ 0` on a ringed space `A` with local stalks: the connecting map
`H¹(A, 𝒪_A^×) → H²(A, F)` precomposed with the inverse of the canonical isomorphism
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup : H¹(A, 𝒪_A^×) ≃ Pic(A)`. For the
exponential sequence of a complex analytic space it is the obstruction `c_exp` to choosing
compatible logarithms of the transition functions of a line bundle. -/
public noncomputable def picardObstruction (A : RingedSpace.{u})
    [∀ x, IsLocalRing (A.presheaf.stalk x)] {F M : TopCat.Sheaf AddCommGrpCat.{u} A}
    {i : F ⟶ M} {e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf A}
    {w : i ≫ e = 0} (hS : (ShortComplex.mk i e w).ShortExact) :=
  (Stacks.Thickenings.cohomologyBoundary hS 1).comp
    ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv A.carrier
        (Stacks.Cohomology.Generators.unitsSheaf A))).toAddMonoidHom.comp
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup A).symm.toAddMonoidHom)

/-- The obstruction map is the connecting map applied to the first-cohomology class corresponding
to a Picard class. -/
public theorem picardObstruction_apply (A : RingedSpace.{u})
    [∀ x, IsLocalRing (A.presheaf.stalk x)] {F M : TopCat.Sheaf AddCommGrpCat.{u} A}
    {i : F ⟶ M} {e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf A} {w : i ≫ e = 0}
    (hS : (ShortComplex.mk i e w).ShortExact) (x) :
    picardObstruction A hS x =
      Stacks.Thickenings.cohomologyBoundary hS 1
        ((Stacks.Thickenings.sheafCohomologyOneExtEquiv A.carrier
          (Stacks.Cohomology.Generators.unitsSheaf A)).hom
            ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup A).symm x)) := by
  rfl

/-- For a ringed space `A` with local stalks and a short exact sequence of sheaves of abelian
groups `0 ⟶ F ⟶ M ⟶ 𝒪_A^× ⟶ 0`, the connecting map precomposed with the inverse of
`Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup` and `H²` of `F ⟶ M` form an exact
sequence `Pic(A) → H²(A, F) → H²(A, M)`; the first map is surjective when `H²(A, M) = 0`. -/
public theorem exact_picardObstruction_of_shortExact (A : RingedSpace.{u})
    [∀ x, IsLocalRing (A.presheaf.stalk x)] {F M : TopCat.Sheaf AddCommGrpCat.{u} A}
    (i : F ⟶ M) (e : M ⟶ Stacks.Cohomology.Generators.unitsSheaf A)
    (w : i ≫ e = 0) (hS : (ShortComplex.mk i e w).ShortExact) :
    Function.Exact (picardObstruction A hS) (Sheaf.H.map.{u} i 2) ∧
      (Subsingleton (Sheaf.H.{u} M 2) → Function.Surjective (picardObstruction A hS)) := by
  have hex := exact_comp_of_surjective (Stacks.Thickenings.cohomology_exact_sub hS 1)
    ((Stacks.Thickenings.sheafCohomologyOneExtEquiv A.carrier
      (Stacks.Cohomology.Generators.unitsSheaf A)).addCommGroupIsoToAddEquiv.surjective.comp
      (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup A).symm.surjective)
  exact ⟨hex, fun _ y => (hex y).mp (Subsingleton.elim _ _)⟩

/-- **The logarithmic obstruction sequence** on the analytification `A = X^an` of a
quasi-compact scheme `X` locally of finite type over `ℂ`. Let
`0 ⟶ ℤ_A ⟶ 𝒪_A ⟶ 𝒪_A^× ⟶ 0` be the exponential sequence, whose first map sends an integer to
the constant section and whose second map sends the class of a holomorphic germ `f` to the class
of `exp(2πi f)`. The obstruction map `c_exp : Pic(A) → H²(A, ℤ_A)`, the connecting map
precomposed with the inverse of `Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`, and
`H²` of `ℤ_A ⟶ 𝒪_A` form an exact sequence `Pic(A) → H²(A, ℤ_A) → H²(A, 𝒪_A)`; in particular
`c_exp` is surjective when `H²(A, 𝒪_A) = 0`. -/
@[mmp "lem_mmp_analytic_picard_obstruction_sequence"]
public theorem exact_picardObstruction_analytification {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [QuasiCompact sX] :
    let J := Opens.grothendieckTopology (space sX)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∃ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
      (∀ (W : Opens (space sX)) (n : ℤ),
        (show (structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) ∧
      (∀ (W : Opens (space sX)) (s : (structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
        (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
        (g' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ g →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf sX).obj.obj (op W))ˣ) :
          (structureSheaf sX).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ g') ∧
      Function.Exact (picardObstruction (analytification sX) hS) (Sheaf.H.map.{0} ι 2) ∧
      (Subsingleton (Sheaf.H.{0} O 2) →
        Function.Surjective (picardObstruction (analytification sX) hS)) := by
  intro J O Ou ZA
  obtain ⟨ι, e, w, hS, hι, he⟩ := exists_shortExact_exponentialSequence sX
  exact ⟨ι, e, w, hS, hι, he,
    exact_picardObstruction_of_shortExact (analytification sX) ι e w hS⟩

end

end MMP.Analytic

/-! ### Bertini theorems for free systems -/

@[expose] public noncomputable section

namespace MMP.Threefold.Bridges

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open MMP.Resolution (IsSNCFamily componentsOf)

attribute [local instance] globalSectionsModule

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance {X : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule X L)

section Smooth

open Topology Stacks.Bertini.FamilyDivisors

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
local instance {X Y : Scheme.{u}} {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    (ι : Y ⟶ X) : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback ι).obj L) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback ι L

private theorem flat_fromSpecResidueField_of_isField {S : Scheme.{u}} (s : S)
    (hs : IsField (S.presheaf.stalk s)) : Flat (S.fromSpecResidueField s) := by
  have hbij : Function.Bijective (S.residue s).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) :=
      (IsLocalRing.residue_eq_zero_iff a).mp ha
    rwa [(IsLocalRing.isField_iff_maximalIdeal_eq).mp hs] at this
  have : IsIso (S.residue s) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  dsimp only [Scheme.fromSpecResidueField]
  infer_instance

private theorem mem_smoothLocus_of_isField_stalk {T S : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFinitePresentation g] (t : T)
    (hT : IsRegularLocalRing (T.presheaf.stalk t))
    (hs : IsField (S.presheaf.stalk (g t))) (hchar : CharZero (S.residueField (g t))) :
    t ∈ g.smoothLocus := by
  set s := g t with hsdef
  have hflat := flat_fromSpecResidueField_of_isField s hs
  have hsq : IsPullback (g.fiberι s) (g.fiberToSpecResidueField s) g
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have : LocallyOfFinitePresentation (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFinitePresentation
      (Limits.pullback.snd g (S.fromSpecResidueField s)))
  have : LocallyOfFiniteType (g.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.snd g (S.fromSpecResidueField s)))
  have hloc := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inr hflat)
  have : PerfectField (S.residueField s) := PerfectField.ofCharZero
  obtain ⟨e, -⟩ := quotientStalk_bridge g t
  have hm : Ideal.map (g.stalkMap (g.fiberι (g t) (g.asFiber t))).hom
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (g (g.fiberι (g t) (g.asFiber t))))) = ⊥ := by
    have h1 : IsField (S.presheaf.stalk (g (g.fiberι (g t) (g.asFiber t)))) := by
      rwa [g.fiberι_asFiber]
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp h1, Ideal.map_bot]
  have : IsRegularLocalRing (T.presheaf.stalk (g.fiberι (g t) (g.asFiber t))) := by
    rwa [g.fiberι_asFiber]
  have hreg : IsRegularLocalRing ((g.fiber s).presheaf.stalk (g.asFiber t)) :=
    IsRegularLocalRing.of_ringEquiv
      (((Ideal.quotEquivOfEq hm).trans (RingEquiv.quotientBot _)).symm.trans e)
  have hsm := (smoothAt_iff_isRegularLocalRing_stalk (k := ↥(S.residueField s))
    (g.fiberToSpecResidueField s)
    (g.asFiber t) ?_).mpr hreg
  · have hmem : g.asFiber t ∈ (g.fiberToSpecResidueField s).smoothLocus :=
      Scheme.Hom.mem_smoothLocus.mpr (hsm.formallySmooth_stalkMap _ _)
    rwa [hloc, Scheme.Hom.mem_preimage, g.fiberι_asFiber t] at hmem
  · let _ : Algebra (S.residueField s) ((g.fiber s).residueField (g.asFiber t)) :=
      ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
        (g.fiberToSpecResidueField s).appTop ≫ (g.fiber s).Γevaluation (g.asFiber t)).hom.toAlgebra
    exact Algebra.isSeparableExtension_of_perfectField _ _

private theorem exists_isOpen_mem_subset_of_isConstructible' {T : Type*} [TopologicalSpace T]
    {E : Set T} (hE : IsConstructible E) {η : T}
    (hη : IsGenericPoint η (Set.univ : Set T)) (hηE : η ∈ E) :
    ∃ U : Set T, IsOpen U ∧ η ∈ U ∧ U ⊆ E := by
  obtain ⟨t, ht, hEeq⟩ := Topology.isConstructible_iff_exists_finset_biUnion_inter_compl.mp hE
  rw [hEeq] at hηE ⊢
  obtain ⟨p, hpt, hηU, hηV⟩ := Set.mem_iUnion₂.mp hηE
  have hVempty : p.2 = ∅ := by
    have hsub : (Set.univ : Set T) ⊆ p.2ᶜ := by
      rw [← hη]
      exact (ht p hpt).2.2.1.isClosed_compl.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hηV)
    simpa using Set.subset_compl_comm.mp hsub
  exact ⟨p.1, (ht p hpt).1, hηU, fun x hx =>
    Set.mem_biUnion hpt ⟨hx, by simp [hVempty]⟩⟩

private theorem exists_opens_subset_smoothLocus {T S : Scheme.{u}} (g : T ⟶ S)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [NoetherianSpace T] [CompactSpace S]
    [QuasiSeparatedSpace S] (η : S) (hη : IsGenericPoint η (Set.univ : Set S))
    (hfield : IsField (S.presheaf.stalk η)) (hchar : CharZero (S.residueField η))
    (hT : ∀ t, IsRegularLocalRing (T.presheaf.stalk t)) :
    ∃ U : S.Opens, η ∈ U ∧ ((g ⁻¹ᵁ U : T.Opens) : Set T) ⊆ g.smoothLocus := by
  have : QuasiSeparatedSpace T := NoetherianSpace.to_quasiSeparatedSpace
  have hZ : IsConstructible ((g.smoothLocus : Set T)ᶜ) := by
    rw [isConstructible_compl]
    exact (NoetherianSpace.isCompact _).isConstructible g.smoothLocus.2
  have himg : IsConstructible (g '' (g.smoothLocus : Set T)ᶜ) := g.isConstructible_image hZ
  have hηnot : η ∉ g '' (g.smoothLocus : Set T)ᶜ := by
    rintro ⟨t, ht, rfl⟩
    exact ht (mem_smoothLocus_of_isField_stalk g t (hT t) hfield hchar)
  obtain ⟨U, hUo, hηU, hUsub⟩ := exists_isOpen_mem_subset_of_isConstructible'
    ((isConstructible_compl).mpr himg) hη hηnot
  refine ⟨⟨U, hUo⟩, hηU, fun t ht => ?_⟩
  by_contra hns
  exact hUsub ht ⟨t, hns, rfl⟩

open MvPolynomial in
private theorem exists_ringEquiv_quotient_span_sum_C_mul_X {A σ : Type*} [CommRing A]
    [Fintype σ] (f : σ → A) (i₀ : σ) (hu : IsUnit (f i₀)) :
    ∃ n : ℕ, Nonempty ((MvPolynomial σ A ⧸ Ideal.span {∑ j, C (f j) * X j}) ≃+*
      MvPolynomial (Fin n) A) := by
  have : Nonempty σ := ⟨i₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card σ = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e₀ : σ ≃ Fin (n + 1) := (Fintype.equivFin σ).trans (finCongr hn)
  let e : σ ≃ Fin (n + 1) := e₀.trans (Equiv.swap (e₀ i₀) 0)
  have he : e i₀ = 0 := by simp [e]
  let g : Fin (n + 1) → A := fun i => f (e.symm i)
  have hg0 : g 0 = f i₀ := by simp [g, ← he]
  obtain ⟨w, hw⟩ : ∃ w, w * g 0 = 1 := by
    obtain ⟨v, hv⟩ := hu
    exact ⟨(v⁻¹ : Aˣ), by rw [hg0, ← hv]; simp⟩
  have hmap : Ideal.span {Algebra.universalLinearForm g} =
      Ideal.map (renameEquiv A e : MvPolynomial σ A →+* MvPolynomial (Fin (n + 1)) A)
      (Ideal.span {∑ j, C (f j) * X j}) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp only [RingHom.coe_coe, renameEquiv_apply, map_sum, map_mul, rename_C, rename_X,
      Algebra.universalLinearForm, g]
    exact (Fintype.sum_equiv e _ _ (fun j => by simp)).symm
  exact ⟨n, ⟨((Ideal.quotientEquivAlg _ _ (renameEquiv A e) hmap).trans
    (Algebra.quotientSpanUniversalLinearFormEquiv g hw)).toRingEquiv⟩⟩

private theorem isRegularRing_chart (D : Stacks.Bertini.FamilyDivisors.{u, u}) [Smooth D.toBase]
    (c : D.Chart) :
    IsRegularRing Γ(c.U.toScheme, ⊤) := by
  have hsm : Smooth (c.U.ι ≫ D.toBase) := inferInstance
  let : IsRegularRing Γ(Spec (.of D.k), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of D.k)).symm.commRingCatIsoToRingEquiv
  let φ := ((c.U.ι ≫ D.toBase).appLE ⊤ ⊤ le_top).hom
  let : Algebra Γ(Spec (.of D.k), ⊤) Γ(c.U.toScheme, ⊤) := φ.toAlgebra
  let : Algebra.Smooth Γ(Spec (.of D.k), ⊤) Γ(c.U.toScheme, ⊤) :=
    ((c.U.ι ≫ D.toBase).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) le_top).toAlgebra
  exact Algebra.isRegularRing_of_smooth Γ(Spec (.of D.k), ⊤) Γ(c.U.toScheme, ⊤)

private theorem isRegularLocalRing_stalk_universalDivisorScheme
    (D : Stacks.Bertini.FamilyDivisors.{u, u})
    [Smooth D.toBase]
    (hgen : ∀ x : D.X, ∃ i, ∃ W : D.X.Opens, x ∈ W ∧
      (W : Set D.X) ⊆ (D.divisorSet (D.basis i))ᶜ)
    (z : D.universalDivisorScheme) :
    IsRegularLocalRing (D.universalDivisorScheme.presheaf.stalk z) := by
  classical
  obtain ⟨i, W, hxW, hW⟩ := hgen (D.parameterProjection (D.universalDivisor.subschemeι z))
  obtain ⟨c, hcU, hxc⟩ := D.exists_chart_le W _ hxW
  have hu : IsUnit (D.chartEquation c.triv i) :=
    isUnit_chartFunction_of_subset_compl_divisorSet c.triv (D.basis i)
      fun y hy => hW (hcU hy)
  have := isRegularRing_chart D c
  obtain ⟨n, ⟨φ⟩⟩ := exists_ringEquiv_quotient_span_sum_C_mul_X
    (D.chartEquationIndex c.U c.triv) (ULift.up i) hu
  have hreg : IsRegularRing Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U) :=
    IsRegularRing.of_ringEquiv ((D.chartSubschemeΓEquiv c.U c.triv).trans φ).symm
  have hz : z ∈ D.chartDivisorOpen c.U := by
    change D.universalDivisor.subschemeι z ∈ ((D.chartOpen c.U).1 : Set D.parameterSpace)
    rwa [chartOpen_coe]
  have hV := D.isAffineOpen_chartDivisorOpen c.U
  let _ : Algebra Γ(D.universalDivisorScheme, D.chartDivisorOpen c.U)
      (D.universalDivisorScheme.presheaf.stalk z) :=
    D.universalDivisorScheme.presheaf.algebra_section_stalk ⟨z, hz⟩
  have : IsLocalization.AtPrime (D.universalDivisorScheme.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal := hV.isLocalization_stalk ⟨z, hz⟩
  have := hreg.isRegularLocalRing_localization (hV.primeIdealOf ⟨z, hz⟩).asIdeal
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨z, hz⟩).asIdeal) _).toRingEquiv

private theorem exists_polynomial_smooth_specializedDivisor
    (D : Stacks.Bertini.FamilyDivisors.{u, u})
    [Smooth D.toBase] [QuasiCompact D.toBase] [CharZero D.k]
    (hgen : ∀ x : D.X, ∃ i, ∃ W : D.X.Opens, x ∈ W ∧
      (W : Set D.X) ⊆ (D.divisorSet (D.basis i))ᶜ) :
    ∃ P : MvPolynomial D.basisIndex D.k, P ≠ 0 ∧ ∀ a' : D.basisIndex → D.k,
      MvPolynomial.eval a' P ≠ 0 →
      Smooth ((D.specializedDivisor D.k (fun i => a' (ULift.up i))).subschemeι ≫
        D.baseChangeToSpec D.k) := by
  have := D.locallyOfFiniteType_universalFamily
  have := D.quasiCompact_universalFamily
  have := D.irreducibleSpace_parameterBase
  have : IsIntegral D.parameterBase := isIntegral_of_irreducibleSpace_of_isReduced _
  set η := genericPoint D.parameterBase
  have hfield : IsField (D.parameterBase.presheaf.stalk η) :=
    Field.toIsField D.parameterBase.functionField
  let φ : D.k →+* D.parameterBase.residueField η :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (D.parameterBase ↘ Spec (.of D.k)).appTop ≫
      D.parameterBase.evaluation ⊤ _ trivial).hom
  have hchar : CharZero (D.parameterBase.residueField η) :=
    charZero_of_injective_ringHom φ.injective
  obtain ⟨U, hηU, hsing⟩ := exists_opens_subset_smoothLocus D.universalFamily η
    (genericPoint_spec _) hfield hchar
    (isRegularLocalRing_stalk_universalDivisorScheme D hgen)
  obtain ⟨P, hP0, hP⟩ := exists_polynomial_parameterPoint_mem (D := D) U ⟨η, hηU⟩
  refine ⟨P, hP0, fun a' ha' => ?_⟩
  obtain ⟨p, hp⟩ := D.exists_isPullback_universalFamily D.k (fun i => a' (ULift.up i))
  exact smooth_of_isPullback_of_subset_smoothLocus D.universalFamily U hsing _ (hP a' ha') p _ hp

/-- The `i`-th basis vector of the system family of `s` gives back the section `s i`. -/
private theorem systemFamily_sectionOf_basis {k : Type u} [Field k]
    {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (i : Fin (Module.finrank (systemFamily (k := k) s).k (systemFamily (k := k) s).V)) :
    (systemFamily (k := k) s).sectionOf ((systemFamily (k := k) s).basis i) =
      s (Fin.cast (Module.finrank_fin_fun k) i) := by
  classical
  have hb : (systemFamily (k := k) s).basis i =
      Pi.single (Fin.cast (Module.finrank_fin_fun k) i) 1 :=
    (Module.Basis.reindex_apply (Pi.basisFun k (Fin (N + 1)))
      (finCongr (Module.finrank_fin_fun k).symm) i).trans (by simp; rfl)
  rw [hb]
  change systemSection s _ = _
  simp [systemSection, Fintype.linearCombination_apply_single]

private theorem exists_polynomial_smooth_zeroScheme_of_smooth {k : Type u} [Field k] [CharZero k]
    {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    [Smooth (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hgen : ∀ x : X, ∃ j, ∃ W : X.Opens, x ∈ W ∧
      (W : Set X) ⊆ ((zeroScheme X L (s j)).supportSet)ᶜ) :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        Smooth ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) := by
  classical
  set D := systemFamily (k := k) s
  have : Smooth D.toBase := ‹Smooth (X ↘ Spec (.of k))›
  have : QuasiCompact D.toBase := ‹QuasiCompact (X ↘ Spec (.of k))›
  have : CharZero D.k := ‹CharZero k›
  have hgen' : ∀ x : D.X, ∃ i, ∃ W : D.X.Opens, x ∈ W ∧
      (W : Set D.X) ⊆ (D.divisorSet (D.basis i))ᶜ := by
    intro x
    obtain ⟨j, W, hxW, hW⟩ := hgen x
    refine ⟨Fin.cast (Module.finrank_fin_fun k).symm j, W, hxW, ?_⟩
    change (W : Set X) ⊆ ((zeroScheme X L (D.sectionOf (D.basis _))).supportSet)ᶜ
    rw [systemFamily_sectionOf_basis]
    convert hW using 5
    exact Fin.ext rfl
  obtain ⟨P, hP0, hP⟩ :=
    exists_polynomial_smooth_specializedDivisor D hgen'
  let σ : D.basisIndex ≃ Fin (N + 1) :=
    Equiv.ulift.trans (finCongr (Module.finrank_fin_fun k))
  refine ⟨MvPolynomial.rename σ P, fun h => hP0 (MvPolynomial.rename_injective _ σ.injective
    (h.trans (map_zero _).symm)), fun c hc => ?_⟩
  have hPc : MvPolynomial.eval (c ∘ σ) P ≠ 0 := fun h0 =>
    hc ((MvPolynomial.eval_rename _ _ _).trans h0)
  have hsm := Stacks.Bertini.FamilyDivisors.smooth_zeroScheme_of_smooth_specializedDivisor D _
    (hP (c ∘ σ) hPc)
  let a : Fin (Module.finrank D.k D.V) → D.k := fun i => (c ∘ σ) (ULift.up i)
  have hsum : (∑ i, a i • D.basis i) = (c : D.V) :=
    sum_smul_reindex_basisFun c
  change Smooth ((Stacks.Divisors.zeroScheme D.X D.L
    (D.sectionOf (∑ i, a i • D.basis i))).subschemeι ≫ D.toBase) at hsm
  rwa [hsum] at hsm

private theorem zeroScheme_systemSection_pullback {k : Type u} [Field k]
    {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {Y : Scheme.{u}} (ι : Y ⟶ X)
    (s : Fin (N + 1) → Γ(L, ⊤)) (c : Fin (N + 1) → k) :
    let _ : Y.Over (Spec (.of k)) := ⟨ι ≫ X ↘ Spec (.of k)⟩
    zeroScheme Y ((Scheme.Modules.pullback ι).obj L)
        (systemSection (fun j => pullbackGlobalSections ι L (s j)) c) =
      (zeroScheme X L (systemSection s c)).comap ι := by
  let _ : Y.Over (Spec (.of k)) := ⟨ι ≫ X ↘ Spec (.of k)⟩
  rw [← Stacks.Divisors.zeroScheme_pullback ι L (systemSection s c)]
  congr 1
  rw [systemSection_apply, systemSection_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show c j • s j = Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.baseRingHom k X
    (c j) • s j from rfl, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul]
  rfl

private theorem exists_mem_subset_compl_supportSet {k : Type u} [Field k]
    {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) (x : X) :
    ∃ j, ∃ W : X.Opens, x ∈ W ∧ (W : Set X) ⊆ ((zeroScheme X L (s j)).supportSet)ᶜ := by
  classical
  set D := systemFamily (k := k) s
  have hid : D.GeneratesBy (id : D.V → D.V) := by
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
    have hx : x ∈ (⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c)) := by
      rw [hs]
      trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨c, hc⟩
  obtain ⟨i, hi⟩ : ∃ i, x ∈ nonvanishingOpen D.X D.L (D.sectionOf (D.basis i)) :=
    Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks _
      (D.generatesBy_basis hid D.basis) x
  refine ⟨Fin.cast (Module.finrank_fin_fun k) i,
    nonvanishingOpen D.X D.L (D.sectionOf (D.basis i)), hi, fun y hy => ?_⟩
  have := D.notMem_divisorSet_of_mem_nonvanishingOpen (D.basis i) hy
  change y ∉ (zeroScheme X L (D.sectionOf (D.basis i))).supportSet at this
  rwa [systemFamily_sectionOf_basis] at this

private theorem exists_polynomial_smooth_trace {k : Type u} [Field k] [CharZero k]
    {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsVariety k (X ↘ Spec (.of k))]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (s : Fin (N + 1) → Γ(L, ⊤))
    (hgen : ∀ x : X, ∃ j, ∃ W : X.Opens, x ∈ W ∧
      (W : Set X) ⊆ ((zeroScheme X L (s j)).supportSet)ᶜ)
    {Y : Scheme.{u}} (ι : Y ⟶ X) [IsImmersion ι] [Smooth (ι ≫ X ↘ Spec (.of k))] :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        Smooth (((zeroScheme X L (systemSection s c)).comap ι).subschemeι ≫ ι ≫
          X ↘ Spec (.of k)) := by
  let _ : Y.Over (Spec (.of k)) := ⟨ι ≫ X ↘ Spec (.of k)⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : AlgebraicGeometry.IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have : NoetherianSpace Y := ι.isEmbedding.isInducing.noetherianSpace
  have : Smooth (Y ↘ Spec (.of k)) := ‹Smooth (ι ≫ X ↘ Spec (.of k))›
  set s' : Fin (N + 1) → Γ((Scheme.Modules.pullback ι).obj L, ⊤) :=
    fun j => pullbackGlobalSections ι L (s j)
  have hgen' : ∀ y : Y, ∃ j, ∃ W : Y.Opens, y ∈ W ∧
      (W : Set Y) ⊆ ((zeroScheme Y ((Scheme.Modules.pullback ι).obj L) (s' j)).supportSet)ᶜ := by
    intro y
    obtain ⟨j, W, hyW, hW⟩ := hgen (ι y)
    refine ⟨j, ι ⁻¹ᵁ W, hyW, fun y' hy' hmem => ?_⟩
    have hz : zeroScheme Y ((Scheme.Modules.pullback ι).obj L) (s' j) =
        (zeroScheme X L (s j)).comap ι :=
      Stacks.Divisors.zeroScheme_pullback ι L (s j)
    rw [hz] at hmem
    have h := congrArg (fun C : TopologicalSpace.Closeds Y => (C : Set Y))
      (Scheme.IdealSheafData.support_comap (zeroScheme X L (s j)) ι)
    have hmem' : y' ∈ (((zeroScheme X L (s j)).comap ι).support : Set Y) := hmem
    rw [h] at hmem'
    exact hW hy' hmem'
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_smooth_zeroScheme_of_smooth (k := k) s' hgen'
  refine ⟨Q, hQ0, fun c hc => ?_⟩
  have h := hQ c hc
  rwa [zeroScheme_systemSection_pullback ι s c] at h

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **General members of a free system are smooth**, in polynomial form: a nonzero polynomial `Q`
in the coefficients such that `Q(c) ≠ 0` makes every trace `Z(∑ᵢ cᵢ sᵢ) ∩ Yᵢ` smooth over `k`,
and `Z(∑ᵢ cᵢ sᵢ)` itself when `X` is smooth. -/
private theorem exists_polynomial_smooth_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {I : Type u} [Finite I] {Y : I → Scheme.{u}} (ι : (i : I) → Y i ⟶ X)
    [∀ i, IsImmersion (ι i)] [∀ i, Smooth (ι i ≫ X ↘ Spec (.of k))] :
    ∃ Q : MvPolynomial (Fin (N + 1)) k, Q ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c Q ≠ 0 →
        (Smooth (X ↘ Spec (.of k)) →
          Smooth ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k))) ∧
        ∀ i, Smooth (((zeroScheme X L (systemSection s c)).comap (ι i)).subschemeι ≫ ι i ≫
          X ↘ Spec (.of k)) := by
  classical
  have hgen := exists_mem_subset_compl_supportSet (k := k) s hs
  have := Fintype.ofFinite I
  choose QY hQY0 hQY using fun i => exists_polynomial_smooth_trace (k := k) s hgen (ι i)
  obtain ⟨QX, hQX0, hQX⟩ : ∃ QX : MvPolynomial (Fin (N + 1)) k, QX ≠ 0 ∧
      ∀ c : Fin (N + 1) → k, MvPolynomial.eval c QX ≠ 0 → Smooth (X ↘ Spec (.of k)) →
        Smooth ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k)) := by
    by_cases hX : Smooth (X ↘ Spec (.of k))
    · obtain ⟨Q, h0, h⟩ := exists_polynomial_smooth_zeroScheme_of_smooth (k := k) s hgen
      exact ⟨Q, h0, fun c hc _ => h c hc⟩
    · exact ⟨1, one_ne_zero, fun c _ h => absurd h hX⟩
  refine ⟨QX * ∏ i, QY i, mul_ne_zero hQX0 (Finset.prod_ne_zero_iff.mpr fun i _ => hQY0 i),
    fun c hc => ?_⟩
  rw [map_mul, map_prod] at hc
  refine ⟨hQX c (left_ne_zero_of_mul hc), fun i => hQY i c ?_⟩
  exact (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hc)) i (Finset.mem_univ _)

private lemma exists_homogeneousComponent_ne_zero {σ R : Type*} [CommSemiring R]
    {Q : MvPolynomial σ R} (hQ : Q ≠ 0) : ∃ d, MvPolynomial.homogeneousComponent d Q ≠ 0 := by
  by_contra h
  push Not at h
  exact hQ ((MvPolynomial.sum_homogeneousComponent Q).symm.trans
    (Finset.sum_eq_zero fun i _ => h i))

private lemma eval_homogeneousComponent_ne_zero_of_mem {c : Fin (N + 1) → k} (hc : c ≠ 0)
    {Q : MvPolynomial (Fin (N + 1)) k} {d : ℕ}
    (hmem : dualPoint c hc ∈ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q)) :
    MvPolynomial.eval c (MvPolynomial.homogeneousComponent d Q) ≠ 0 := by
  intro h0
  change MvPolynomial.homogeneousComponent d Q ∉
    (RingHom.ker (MvPolynomial.eval c)).homogeneousCore
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) at hmem
  exact hmem (Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨d, MvPolynomial.homogeneousComponent_isHomogeneous d Q⟩ ((RingHom.mem_ker).mpr h0))

/-- **Bertini's theorem for smoothness of a free system in characteristic zero.** Let `X` be a
variety over an algebraically closed field `k` of characteristic zero, and `s₀, …, s_N` global
sections of an invertible sheaf `L` generating it. Let `ιᵢ : Yᵢ ⟶ X`, `i ∈ I`, be finitely many
immersions with `Yᵢ` smooth over `k`. Then there is a dense open `U` of the coefficient space
`𝔸ᴺ⁺¹_k`, and a dense open `U'` of `ℙᴺ_k`, such that for every coefficient vector `c` with
`c ∈ U` (resp. `c ≠ 0` and `[c] ∈ U'`) the scheme-theoretic preimage in every `Yᵢ` of the zero
scheme of `∑ᵢ cᵢ sᵢ` is smooth over `k`, and, if `X` is smooth over `k`, so is the zero scheme
itself. -/
@[mmp "lem_mmp_foundation_free_system_smooth_bertini"]
public theorem exists_dense_open_smooth_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {I : Type u} [Finite I] {Y : I → Scheme.{u}} (ι : (i : I) → Y i ⟶ X)
    [∀ i, IsImmersion (ι i)] [∀ i, Smooth (ι i ≫ X ↘ Spec (.of k))] :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        (Smooth (X ↘ Spec (.of k)) →
          Smooth ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k))) ∧
        ∀ i, Smooth (((zeroScheme X L (systemSection s c)).comap (ι i)).subschemeι ≫ ι i ≫
          X ↘ Spec (.of k))) ∧
    (∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        (Smooth (X ↘ Spec (.of k)) →
          Smooth ((zeroScheme X L (systemSection s c)).subschemeι ≫ X ↘ Spec (.of k))) ∧
        ∀ i, Smooth (((zeroScheme X L (systemSection s c)).comap (ι i)).subschemeι ≫ ι i ≫
          X ↘ Spec (.of k))) := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := exists_polynomial_smooth_zeroScheme s hs ι
  refine ⟨⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ0, fun c hc => hQ c ?_⟩, ?_⟩
  · intro h0
    change Q ∉ RingHom.ker (MvPolynomial.eval c) at hc
    exact hc ((RingHom.mem_ker).mpr h0)
  obtain ⟨d, hd⟩ := exists_homogeneousComponent_ne_zero hQ0
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun c hc hmem => ?_⟩
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q c
    (eval_homogeneousComponent_ne_zero_of_mem hc hmem)
  have h := hQ (t • c) htQ
  rwa [zeroScheme_systemSection_smul s c ht] at h

end Smooth

section SNC

variable {k : Type u} [Field k] {N : ℕ} {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- A dense open of the spectrum of a domain contains the basic open of a nonzero element. -/
private lemma exists_ne_zero_basicOpen_le {R : Type*} [CommRing R] [IsDomain R]
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) (hU : Dense (U : Set (PrimeSpectrum R))) :
    ∃ f : R, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ U := by
  obtain ⟨x, hx⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨f, fun h => ?_, hfU⟩
  subst h
  exact hxf (by simp)

/-- The general position property of the trace `H` of `Z(∑ cᵢ sᵢ)` on `Y`. -/
private abbrev SNCProp (s : Fin (N + 1) → Γ(L, ⊤)) {Y : Scheme.{u}} (j : Y ⟶ X)
    {Λ : Type u} (G : Λ → Y.IdealSheafData) (c : Fin (N + 1) → k) : Prop :=
  let H := (zeroScheme X L (systemSection s c)).comap j
  Smooth (H.subschemeι ≫ j ≫ X ↘ Spec (.of k)) ∧
  (∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
    ¬ W ⊆ (H.support : Set Y)) ∧
  IsSNCFamily (j ≫ X ↘ Spec (.of k)) (fun o : Option Λ => o.elim H G)

/-- The stratum `⋂_{i ∈ J} Gᵢ` of the family `G`, as the sum of the ideals `Gᵢ`, `i ∈ J`. -/
private abbrev stratum {Y : Scheme.{u}} {Λ : Type u} (G : Λ → Y.IdealSheafData) (J : Set Λ) :
    Y.IdealSheafData :=
  ⨆ i ∈ J, G i

/-- The stalk of a stratum at a point of it is generated by the coordinates `z (c i)`,
`i ∈ J`, of the components through the point. -/
private lemma stalk_stratum_eq_span {Y : Scheme.{u}} {Λ : Type u} [Finite Λ]
    (G : Λ → Y.IdealSheafData) (J : Set Λ) (y : Y) {n : ℕ} (z : Fin n → Y.presheaf.stalk y)
    (c : {i // y ∈ (G i).support} → Fin n)
    (hc : ∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c i)})
    (hy : ∀ i ∈ J, y ∈ (G i).support) :
    ∃ S : Finset (Fin n), IdealSheafData.stalk (stratum G J) y = Ideal.span (z '' S) := by
  classical
  have := Fintype.ofFinite Λ
  refine ⟨(Finset.univ.filter (fun i : {i // y ∈ (G i).support} => i.1 ∈ J)).image c, ?_⟩
  have hst : IdealSheafData.stalk (stratum G J) y = ⨆ i ∈ J, IdealSheafData.stalk (G i) y := by
    rw [stratum, iSup_subtype', MMP.Resolution.stalk_iSup, iSup_subtype']
  rw [hst]
  apply le_antisymm
  · refine iSup₂_le fun i hi => ?_
    rw [hc ⟨i, hy i hi⟩, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨c ⟨i, hy i hi⟩, by simpa using ⟨i, hi, hy i hi, rfl⟩, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨m, hm, rfl⟩
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_image, Set.mem_ofPred_eq] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    refine (le_iSup₂ (f := fun i (_ : i ∈ J) => IdealSheafData.stalk (G i) y) i.1 hi) ?_
    rw [hc i]
    exact Ideal.mem_span_singleton_self _

/-- A smooth morphism is locally of finite type. -/
private lemma locallyOfFiniteType_of_smooth {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Smooth f] :
    LocallyOfFiniteType f :=
  have := AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth f
  inferInstance

/-- Over a field of characteristic zero, the local rings of a smooth scheme are regular. -/
private lemma isRegularLocalRing_stalk_of_smooth [CharZero k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] (y : Y) : IsRegularLocalRing (Y.presheaf.stalk y) :=
  (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk f).1 ‹_› y

/-- The strata of an snc family on a smooth scheme over a field of characteristic zero are
smooth: the local ring of `⋂_{i ∈ J} Gᵢ` is the quotient of a regular local ring by part of a
regular system of parameters, hence regular, and over a perfect field regular means smooth. -/
private lemma smooth_stratum [CharZero k] {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j]
    [Smooth (j ≫ X ↘ Spec (.of k))] {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) (J : Set Λ) :
    Smooth ((stratum G J).subschemeι ≫ j ≫ X ↘ Spec (.of k)) := by
  have := locallyOfFiniteType_of_smooth (j ≫ X ↘ Spec (.of k))
  have : LocallyOfFiniteType ((stratum G J).subschemeι ≫ j ≫ X ↘ Spec (.of k)) := inferInstance
  rw [MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk]
  intro w
  set y := (stratum G J).subschemeι w
  have hyS : y ∈ ((stratum G J).support : Set Y) := by
    rw [← (stratum G J).range_subschemeι]
    exact ⟨w, rfl⟩
  have hy : ∀ i ∈ J, y ∈ (G i).support := fun i hi =>
    Scheme.IdealSheafData.support_antitone (le_biSup G hi) hyS
  obtain ⟨n, z, c, hz, hc, -⟩ := hG.2 y
  obtain ⟨S, hS⟩ := stalk_stratum_eq_span G J y z c hc hy
  apply isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient
  rw [hS]
  have := isRegularLocalRing_stalk_of_smooth (j ≫ X ↘ Spec (.of k)) y
  exact (MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz S).1

section PointValue

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
  Stacks.AlgebraicGeometry.ProjDegreeOneRepresents

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- A degree-one form lies in the homogeneous prime of the image of `x` under the morphism to
projective space defined by a generating system exactly when its section vanishes at `x`. -/
private lemma ι_mem_asHomogeneousIdeal_iff' (V : Type u) [AddCommGroup V] [Module k V]
    (ψ : V →ₗ[k] Γ(L, ⊤)) (hψ : ⨆ v : V, nonvanishingOpen X L (ψ v) = ⊤) (x : X) (v : V) :
    SymmetricAlgebra.ι k V v ∈
        ((morphismOfGeneratingSections k V L ψ hψ).base x).asHomogeneousIdeal ↔
      x ∉ nonvanishingOpen X L (ψ v) := by
  have hpre : morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        _root_.AlgebraicGeometry.Proj.basicOpen _ (SymmetricAlgebra.ι k V v) =
      nonvanishingOpen X L (ψ v) := by
    refine ((classifies_classifyingPair k V L ψ hψ).1 (degreeOneElement k V v)).trans ?_
    change nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L 1)
        ((veroneseOfLinearMap k V L ψ).pow (degreeOneElement k V v).2 1) = _
    rw [pow_degreeOneElement, nonvanishingOpen_twistOneSection]
  have hx : (x ∈ morphismOfGeneratingSections k V L ψ hψ ⁻¹ᵁ
        _root_.AlgebraicGeometry.Proj.basicOpen _ (SymmetricAlgebra.ι k V v)) ↔
      SymmetricAlgebra.ι k V v ∉
        ((morphismOfGeneratingSections k V L ψ hψ).base x).asHomogeneousIdeal := Iff.rfl
  rw [hpre] at hx
  rw [← not_iff_not, not_not, hx]

end PointValue

/-- At a point `x` of `X`, the coefficient vectors `c` with `∑ cᵢ sᵢ` vanishing at `x` lie in
the zero set of a nonzero linear polynomial: they form a `k`-subspace (the degree-one part of the
homogeneous prime of the image of `x` under the morphism to `ℙᴺ` the system defines), and it is
proper because the system generates `L` at `x`. -/
private lemma exists_ne_zero_eval_ne_zero_imp_mem_nonvanishingOpen
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤) (x : X) :
    ∃ P : MvPolynomial (Fin (N + 1)) k, P ≠ 0 ∧ ∀ c : Fin (N + 1) → k,
      MvPolynomial.eval c P ≠ 0 → x ∈ nonvanishingOpen X L (systemSection s c) := by
  classical
  let K : Submodule k (Fin (N + 1) → k) :=
    (Submodule.restrictScalars k
      ((Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections
        k (Fin (N + 1) → k) L (systemSection s) hs).base x).asHomogeneousIdeal.toIdeal).comap
      (SymmetricAlgebra.ι k (Fin (N + 1) → k))
  have hK : ∀ c, c ∈ K ↔ x ∉ nonvanishingOpen X L (systemSection s c) := fun c =>
    ι_mem_asHomogeneousIdeal_iff' (Fin (N + 1) → k) (systemSection s) hs x c
  have hKtop : K ≠ ⊤ := by
    intro h
    have hx : x ∈ ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) := by
      rw [hs]
      trivial
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact (hK c).1 (h ▸ Submodule.mem_top) hc
  obtain ⟨φ, hφ0, hφK⟩ := Submodule.exists_le_ker_of_lt_top K (lt_top_iff_ne_top.mpr hKtop)
  set P : MvPolynomial (Fin (N + 1)) k :=
    ∑ i, MvPolynomial.C (φ (fun j => if i = j then 1 else 0)) * MvPolynomial.X i
  have heval : ∀ c, MvPolynomial.eval c P = φ c := fun c => by
    rw [LinearMap.pi_apply_eq_sum_univ φ c]
    simp [P, mul_comm]
  refine ⟨P, fun h0 => hφ0 (LinearMap.ext fun c => by simp [← heval, h0]), fun c hc => ?_⟩
  rw [heval] at hc
  by_contra hx
  exact hc (hφK ((hK c).2 hx))

/-- General members of the system contain no component of a stratum `⋂_{i ∈ J} Gᵢ`: each of the
finitely many components has a generic point, and by
`exists_ne_zero_eval_ne_zero_imp_mem_nonvanishingOpen` the members vanishing there lie in the zero
set of a nonzero polynomial. -/
private lemma exists_dense_open_not_subset [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [Smooth (j ≫ X ↘ Spec (.of k))]
    {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) :
    ∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        ∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
          ¬ W ⊆ (((zeroScheme X L (systemSection s c)).comap j).support : Set Y) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace Y := by
    rw [TopologicalSpace.noetherianSpace_iff_isCompact]
    intro t
    rw [j.isEmbedding.isInducing.isCompact_iff]
    exact TopologicalSpace.NoetherianSpace.isCompact _
  let S : Set (Set Y) := ⋃ J : Set Λ, componentsOf (⋂ i ∈ J, ((G i).support : Set Y))
  have hclosed : ∀ J : Set Λ, IsClosed (⋂ i ∈ J, ((G i).support : Set Y)) := fun J =>
    isClosed_biInter fun i _ => (G i).support.isClosed
  have hSfin : S.Finite := Set.finite_iUnion fun J =>
    (MMP.Resolution.Aux.finite_and_cover_componentsOf (hclosed J)).1
  have hgen : ∀ W : S, ∃ ξ : Y, (W : Set Y) = closure {ξ} := by
    rintro ⟨W, hW⟩
    obtain ⟨J, hJ⟩ := Set.mem_iUnion.mp hW
    obtain ⟨ξ, -, hξ⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf (hclosed J) hJ
    exact ⟨ξ, hξ⟩
  choose ξ hξ using hgen
  choose P hP0 hP using exists_ne_zero_eval_ne_zero_imp_mem_nonvanishingOpen (k := k) s hs
  have := hSfin.fintype
  let Q : MvPolynomial (Fin (N + 1)) k := ∏ W : S, P (j.base (ξ W))
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W _ => hP0 _
  refine ⟨PrimeSpectrum.basicOpen Q, dense_basicOpen_of_ne_zero hQ, fun c hc J W hW hWH => ?_⟩
  have hcQ : MvPolynomial.eval c Q ≠ 0 := fun h =>
    (show Q ∉ RingHom.ker (MvPolynomial.eval c) from hc) ((RingHom.mem_ker).mpr h)
  have hWS : W ∈ S := Set.mem_iUnion.mpr ⟨J, hW⟩
  have hprod : ∏ W' : S, MvPolynomial.eval c (P (j.base (ξ W'))) ≠ 0 := by
    simpa only [Q, map_prod] using hcQ
  have hnv := hP (j.base (ξ ⟨W, hWS⟩)) c
    (Finset.prod_ne_zero_iff.mp hprod ⟨W, hWS⟩ (Finset.mem_univ _))
  have hmem : ξ ⟨W, hWS⟩ ∈ (((zeroScheme X L (systemSection s c)).comap j).support : Set Y) :=
    hWH (by
      have h := hξ ⟨W, hWS⟩
      simp only at h
      exact h.symm.subset (subset_closure (Set.mem_singleton _)))
  rw [Scheme.IdealSheafData.support_comap] at hmem
  exact notMem_supportSet_zeroScheme_of_mem_nonvanishingOpen L _ hnv hmem

/-- If `dim R + 1` is a natural number, then so is `dim R`. -/
private lemma exists_nat_eq_ringKrullDim_of_add_one_eq {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (h : ringKrullDim R + 1 = n) : ∃ d : ℕ, ringKrullDim R = d := by
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := R)
  generalize ringKrullDim R = q at h0 h ⊢
  induction q using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      exfalso
      rw [← WithBot.coe_one, ← WithBot.coe_add, top_add] at h
      exact ENat.top_ne_natCast _ (WithBot.coe_injective h)
    | coe d => exact ⟨d, rfl⟩

/-- Cutting a regular local quotient `A ⧸ I` by an element nonzero in it lowers its dimension by
one. -/
private lemma ringKrullDim_quotient_sup_span_singleton_add_one {A : Type*} [CommRing A]
    {I : Ideal A} [IsRegularLocalRing (A ⧸ I)] {h : A} [Nontrivial (A ⧸ (I ⊔ Ideal.span {h}))]
    (hh : Ideal.Quotient.mk I h ≠ 0) :
    ringKrullDim (A ⧸ (I ⊔ Ideal.span {h})) + 1 = ringKrullDim (A ⧸ I) := by
  have := IsRegularLocalRing.isDomain (A ⧸ I)
  have hm : Ideal.Quotient.mk I h ∈ IsLocalRing.maximalIdeal (A ⧸ I) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ Ideal.span {h}))
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self h))] at hu'
    exact not_isUnit_zero hu'
  let e : (A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I h} ≃+* A ⧸ (I ⊔ Ideal.span {h}) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {h}))
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hh) hm

/-- Let `z` be a regular system of parameters of a regular local ring `A`, and `h ∈ 𝔪_A` an
element that is nonzero modulo the parameters `z (c₀ i)`. If `A / (z (c₀ i), h)` is regular, then
the `z (c₀ i)` together with `h` extend to a regular system of parameters of `A`. -/
private lemma exists_isRegularSystemOfParameters_extend {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {n : ℕ} {z : Fin n → A} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    {ι : Type*} [Finite ι] (c₀ : ι → Fin n) (hinj : Function.Injective c₀) (h : A)
    (hm : h ∈ IsLocalRing.maximalIdeal A)
    (hh : Ideal.Quotient.mk (Ideal.span (Set.range (z ∘ c₀))) h ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ (Ideal.span (Set.range (z ∘ c₀)) ⊔ Ideal.span {h}))) :
    ∃ (m : ℕ) (z' : Fin m → A) (e : Fin m) (c' : ι → Fin m),
      MMP.Mori.IsRegularSystemOfParameters z' ∧ (∀ i, z' (c' i) = z (c₀ i)) ∧
        Function.Injective c' ∧ (∀ i, c' i ≠ e) ∧ z' e = h := by
  classical
  have := Fintype.ofFinite ι
  set r := Fintype.card ι
  let σ := Fintype.equivFin ι
  let g : Fin r → A := z ∘ c₀ ∘ σ.symm
  have hg : Set.range g = Set.range (z ∘ c₀) := by
    simp only [g, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  let S : Finset (Fin n) := Finset.univ.image c₀
  have hS : z '' (S : Set (Fin n)) = Set.range (z ∘ c₀) := by
    simp [S, Set.range_comp]
  have hScard : S.card = r := by
    simp only [S, r]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  obtain ⟨hBreg, hBdim, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz S
  rw [hS] at hBreg hBdim
  rw [hScard] at hBdim
  set I := Ideal.span (Set.range (z ∘ c₀))
  have hdimB := ringKrullDim_quotient_sup_span_singleton_add_one hh
  rw [hBdim] at hdimB
  let hfam : Fin (r + 1) → A := Fin.append g ![h]
  have hspan : Ideal.span (Set.range hfam) = I ⊔ Ideal.span {h} := by
    rw [show Set.range hfam = Set.range g ∪ {h} by
      simp [hfam, Fin.append_right_eq_snoc, Fin.range_snoc, Set.union_comm], Ideal.span_union, hg]
  have hdimA : ringKrullDim A = n := hz.2
  obtain ⟨d, hd⟩ := exists_nat_eq_ringKrullDim_of_add_one_eq hdimB
  rw [hd] at hdimB
  have hdn : d + 1 = n - r := mod_cast hdimB
  obtain ⟨m, t, ht⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
    hfam).1 ⟨hspan ▸ hreg, by
      rw [hspan, hdimA, hd]
      have : d + (r + 1) = n := by omega
      exact_mod_cast this⟩
  refine ⟨r + 1 + m, Fin.append hfam t, Fin.castAdd m (Fin.natAdd r (0 : Fin 1)),
    fun i => Fin.castAdd m (Fin.castAdd 1 (σ i)), ht, fun i => ?_, fun i i' hii' => ?_,
    fun i => ?_, ?_⟩
  · simp [hfam, g]
  · have := congrArg Fin.val hii'
    simp only [Fin.val_castAdd] at this
    exact σ.injective (Fin.ext this)
  · intro hie
    have := congrArg Fin.val hie
    simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at this
    have := (σ i).isLt
    omega
  · simp [hfam]

/-- At `y ∈ H`, the quotient of the local ring of `Y` by the parameters `z (c₀ i)` of the
components of `G` through `y` and the local equation `h` of `H` is the local ring of the smooth
scheme `H ∩ ⋂_{y ∈ Gᵢ} Gᵢ`, hence regular. -/
private lemma isRegularLocalRing_quotient_sup_localEquation [CharZero k]
    (s : Fin (N + 1) → Γ(L, ⊤)) {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j]
    [Smooth (j ≫ X ↘ Spec (.of k))] {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (c : Fin (N + 1) → k)
    (hst : ∀ J : Set Λ, Smooth (((zeroScheme X L (systemSection s c)).comap
      ((stratum G J).subschemeι ≫ j)).subschemeι ≫ ((stratum G J).subschemeι ≫ j) ≫
        X ↘ Spec (.of k)))
    {y : Y} (hy : y ∈ ((zeroScheme X L (systemSection s c)).comap j).support) {n : ℕ}
    {z : Fin n → Y.presheaf.stalk y} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (c₀ : {i // y ∈ (G i).support} → Fin n)
    (hc₀ : ∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c₀ i)}) {h : Y.presheaf.stalk y}
    (hHh : IdealSheafData.stalk ((zeroScheme X L (systemSection s c)).comap j) y =
      Ideal.span {h}) :
    IsRegularLocalRing (Y.presheaf.stalk y ⧸
      (Ideal.span (Set.range (z ∘ c₀)) ⊔ Ideal.span {h})) := by
  classical
  set H := (zeroScheme X L (systemSection s c)).comap j with hHdef
  let J : Set Λ := {i | y ∈ (G i).support}
  set Z := stratum G J with hZdef
  have hZ : IdealSheafData.stalk Z y = Ideal.span (Set.range (z ∘ c₀)) := by
    rw [← Set.iUnion_singleton_eq_range, Ideal.span_iUnion]
    simp only [Function.comp_apply, ← hc₀]
    rw [hZdef, stratum, iSup_subtype', MMP.Resolution.stalk_iSup]
    rfl
  have hyZ : y ∈ Z.support := by
    by_contra hn
    have htop := (Stacks.Divisors.stalk_eq_top_iff_notMem_support Z y).2 hn
    rw [hZ] at htop
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top <|
      hz.1 ▸ top_unique (htop ▸ Ideal.span_mono (Set.range_comp_subset_range c₀ z))
  let w := IdealSheafData.subschemePoint Z y hyZ
  set T := (zeroScheme X L (systemSection s c)).comap (Z.subschemeι ≫ j) with hTdef
  have hwT : w ∈ T.support := by
    rw [hTdef, Scheme.IdealSheafData.support_comap]
    rwa [hHdef, Scheme.IdealSheafData.support_comap] at hy
  let v := IdealSheafData.subschemePoint T w hwT
  have hregT : IsRegularLocalRing (T.subscheme.presheaf.stalk v) :=
    have := hst J
    isRegularLocalRing_stalk_of_smooth (T.subschemeι ≫ (Z.subschemeι ≫ j) ≫ X ↘ Spec (.of k)) v
  have hreg₁ : IsRegularLocalRing (Z.subscheme.presheaf.stalk w ⧸ IdealSheafData.stalk T w) :=
    IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv T v).symm
  let y' := Z.subschemeι w
  let A' := Y.presheaf.stalk y'
  let h' : A' := h
  let I' : Ideal A' := IdealSheafData.stalk Z y'
  have hTw : IdealSheafData.stalk T w = Ideal.span {Z.subschemeι.stalkMap w h'} := by
    rw [hTdef, Scheme.IdealSheafData.comap_comp, ← hHdef,
      AlgebraicGeometry.IdealSheafData.stalk_comap,
      show IdealSheafData.stalk H y' = Ideal.span {h'} from hHh, Ideal.map_span,
      Set.image_singleton]
  let φ : A' ⧸ I' ≃+* Z.subscheme.presheaf.stalk w := IdealSheafData.subschemeStalkQuotEquiv Z w
  let K : Ideal (A' ⧸ I') := Ideal.span {Ideal.Quotient.mk I' h'}
  rw [hTw] at hreg₁
  have hKmk : K = (Ideal.span {h'}).map (Ideal.Quotient.mk I') := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← hZ]
  change IsRegularLocalRing (A' ⧸ (I' ⊔ Ideal.span {h'}))
  let e₀ : (A' ⧸ I') ⧸ K ≃+*
      Z.subscheme.presheaf.stalk w ⧸ Ideal.span {Z.subschemeι.stalkMap w h'} :=
    Ideal.quotientEquiv K (Ideal.span {Z.subschemeι.stalkMap w h'}) φ (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2)
  let e₁ : (A' ⧸ I') ⧸ K ≃+* A' ⧸ (I' ⊔ Ideal.span {h'}) :=
    (Ideal.quotEquivOfEq hKmk).trans (DoubleQuot.quotQuotEquivQuotSup I' (Ideal.span {h'}))
  have := hreg₁
  exact IsRegularLocalRing.of_ringEquiv (e₀.symm.trans e₁)

/-- **The coordinate clause at a point of `H`.** At `y ∈ H` with regular parameters `z` from
the snc family `G`, the local equation `h` of `H` is nonzero modulo the parameters of the
components through `y` (no stratum component lies in `H`), and the quotient by those parameters
and `h` is the local ring of the smooth scheme `H ∩ ⋂_{y ∈ Gᵢ} Gᵢ`, hence regular; so they extend
to a regular system of parameters. -/
private lemma exists_coordinates_of_mem_support [CharZero k] (s : Fin (N + 1) → Γ(L, ⊤))
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [Smooth (j ≫ X ↘ Spec (.of k))]
    {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) (c : Fin (N + 1) → k)
    (hH : Smooth (((zeroScheme X L (systemSection s c)).comap j).subschemeι ≫ j ≫
      X ↘ Spec (.of k)))
    (hst : ∀ J : Set Λ, Smooth (((zeroScheme X L (systemSection s c)).comap
      ((stratum G J).subschemeι ≫ j)).subschemeι ≫ ((stratum G J).subschemeι ≫ j) ≫
        X ↘ Spec (.of k)))
    (hW : ∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
      ¬ W ⊆ (((zeroScheme X L (systemSection s c)).comap j).support : Set Y))
    (y : Y) (hy : y ∈ ((zeroScheme X L (systemSection s c)).comap j).support) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (e : Fin n)
      (c' : {i // y ∈ (G i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c' i)}) ∧
        Function.Injective c' ∧ (∀ i, c' i ≠ e) ∧
        IdealSheafData.stalk ((zeroScheme X L (systemSection s c)).comap j) y =
          Ideal.span {z e} := by
  classical
  set H := (zeroScheme X L (systemSection s c)).comap j with hHdef
  obtain ⟨n, z, c₀, hz, hc₀, hinj⟩ := hG.2 y
  have := isRegularLocalRing_stalk_of_smooth (j ≫ X ↘ Spec (.of k)) y
  obtain ⟨h, hHh⟩ : ∃ h : Y.presheaf.stalk y, IdealSheafData.stalk H y = Ideal.span {h} := by
    obtain ⟨U, hU⟩ := Stacks.Divisors.exists_affineOpens_mem (j.base y)
    obtain ⟨g, hg, -, ⟨e⟩⟩ := AlgebraicGeometry.exists_basicOpen_linearEquiv L U (j.base y) hU
    refine ⟨(j.stalkMap y).hom ((X.presheaf.germ (X.basicOpen g) (j.base y) hg).hom
      (e (L.presheaf.map (homOfLE le_top).op (systemSection s c)))), ?_⟩
    rw [hHdef, AlgebraicGeometry.IdealSheafData.stalk_comap,
      Stacks.Divisors.stalk_zeroScheme_eq_span_germ L _ ⟨X.basicOpen g, U.2.basicOpen g⟩ e _ rfl
        (j.base y) hg, Ideal.map_span, Set.image_singleton]
  have hm : h ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine (Stacks.Divisors.stalk_eq_top_iff_notMem_support H y).1 ?_ hy
    rw [hHh, Ideal.span_singleton_eq_top.mpr hu]
  have hh : Ideal.Quotient.mk (Ideal.span (Set.range (z ∘ c₀))) h ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro hhI
    let J : Set Λ := {i | y ∈ (G i).support}
    have hyD : y ∈ ⋂ i ∈ J, ((G i).support : Set Y) := Set.mem_iInter₂.mpr fun i hi => hi
    obtain ⟨W, hW', hyW⟩ := MMP.Resolution.exists_mem_componentsOf hyD
    obtain ⟨ξ, hξD, rfl⟩ := MMP.Resolution.Aux.exists_eq_closure_of_mem_componentsOf
      (isClosed_biInter fun i _ => (G i).support.isClosed) hW'
    have hsp : ξ ⤳ y := specializes_iff_mem_closure.mpr hyW
    apply hW J _ hW'
    refine closure_minimal ?_ H.support.isClosed
    rw [Set.singleton_subset_iff]
    refine (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes H hsp).2 ?_
    rw [hHh, Ideal.span_le, Set.singleton_subset_iff]
    refine (Ideal.span_le.mpr ?_) hhI
    rintro _ ⟨i, rfl⟩
    have := (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes (G i.1) hsp).1
      (Set.mem_iInter₂.mp hξD i.1 i.2)
    rw [hc₀ i] at this
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨m, z', e, c', hz', hzc, hinj', hne, he⟩ :=
    exists_isRegularSystemOfParameters_extend hz c₀ hinj h hm hh
      (isRegularLocalRing_quotient_sup_localEquation s j G c hst hy hz c₀ hc₀ hHh)
  refine ⟨m, z', e, c', hz', fun i => ?_, hinj', hne, ?_⟩
  · rw [hc₀ i, hzc i]
  · rw [hHh, he]

/-- Regular parameters at every point of `Y` adapted to the family `H + G`. -/
private lemma exists_coordinates_option_elim [CharZero k] (s : Fin (N + 1) → Γ(L, ⊤))
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [Smooth (j ≫ X ↘ Spec (.of k))]
    {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) (c : Fin (N + 1) → k)
    (hH : Smooth (((zeroScheme X L (systemSection s c)).comap j).subschemeι ≫ j ≫
      X ↘ Spec (.of k)))
    (hst : ∀ J : Set Λ, Smooth (((zeroScheme X L (systemSection s c)).comap
      ((stratum G J).subschemeι ≫ j)).subschemeι ≫ ((stratum G J).subschemeι ≫ j) ≫
        X ↘ Spec (.of k)))
    (hW : ∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
      ¬ W ⊆ (((zeroScheme X L (systemSection s c)).comap j).support : Set Y)) (y : Y) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y)
      (c' : {o // y ∈ ((fun o : Option Λ =>
        o.elim ((zeroScheme X L (systemSection s c)).comap j) G) o).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ o, IdealSheafData.stalk ((fun o : Option Λ =>
          o.elim ((zeroScheme X L (systemSection s c)).comap j) G) o.1) y =
          Ideal.span {z (c' o)}) ∧ Function.Injective c' := by
  set H := (zeroScheme X L (systemSection s c)).comap j
  by_cases hyH : y ∈ H.support
  · obtain ⟨n, z, e, c₀, hz, hc₀, hinj, hne, hHe⟩ :=
      exists_coordinates_of_mem_support s j G hG c hH hst hW y hyH
    refine ⟨n, z, fun o => match o with
      | ⟨none, _⟩ => e
      | ⟨some i, hi⟩ => c₀ ⟨i, hi⟩, hz, ?_, ?_⟩
    · rintro ⟨_ | i, hi⟩
      · exact hHe
      · exact hc₀ ⟨i, hi⟩
    · rintro ⟨_ | i, hi⟩ ⟨_ | i', hi'⟩ h
      · rfl
      · exact absurd h.symm (hne _)
      · exact absurd h (hne _)
      · obtain rfl : i = i' := congrArg Subtype.val (hinj h)
        rfl
  · obtain ⟨n, z, c₀, hz, hc₀, hinj⟩ := hG.2 y
    refine ⟨n, z, fun o => match o with
      | ⟨none, h⟩ => absurd h hyH
      | ⟨some i, hi⟩ => c₀ ⟨i, hi⟩, hz, ?_, ?_⟩
    · rintro ⟨_ | i, hi⟩
      · exact absurd hi hyH
      · exact hc₀ ⟨i, hi⟩
    · rintro ⟨_ | i, hi⟩ ⟨_ | i', hi'⟩ h
      · exact absurd hi hyH
      · exact absurd hi hyH
      · exact absurd hi' hyH
      · obtain rfl : i = i' := congrArg Subtype.val (hinj h)
        rfl

/-- If the traces of `H` on `Y` and on every stratum of `G` are smooth and `H` contains no
stratum component, then `H + G` is a simple normal crossing family. -/
private lemma isSNCFamily_of_smooth_strata [CharZero k] (s : Fin (N + 1) → Γ(L, ⊤))
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [Smooth (j ≫ X ↘ Spec (.of k))]
    {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) (c : Fin (N + 1) → k)
    (hH : Smooth (((zeroScheme X L (systemSection s c)).comap j).subschemeι ≫ j ≫
      X ↘ Spec (.of k)))
    (hst : ∀ J : Set Λ, Smooth (((zeroScheme X L (systemSection s c)).comap
      ((stratum G J).subschemeι ≫ j)).subschemeι ≫ ((stratum G J).subschemeι ≫ j) ≫
        X ↘ Spec (.of k)))
    (hW : ∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
      ¬ W ⊆ (((zeroScheme X L (systemSection s c)).comap j).support : Set Y)) :
    IsSNCFamily (j ≫ X ↘ Spec (.of k))
      (fun o : Option Λ => o.elim ((zeroScheme X L (systemSection s c)).comap j) G) := by
  classical
  set H := (zeroScheme X L (systemSection s c)).comap j with hHdef
  have : LocallyOfFinitePresentation (j ≫ X ↘ Spec (.of k)) :=
    AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth _
  have := locallyOfFiniteType_of_smooth (j ≫ X ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ X ↘ Spec (.of k))
  have hcoord := exists_coordinates_option_elim s j G hG c hH hst hW
  have hHD : ∀ y ∈ H.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (e : Fin m),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk H y = Ideal.span {w e} := by
    intro y hy
    obtain ⟨n, z, c', hz, hc', -⟩ := hcoord y
    exact ⟨n, z, c' ⟨none, hy⟩, hz, hc' ⟨none, hy⟩⟩
  refine ⟨fun o => ?_, hcoord⟩
  rcases o with _ | i
  · have : LocallyOfFinitePresentation (H.subschemeι ≫ j ≫ X ↘ Spec (.of k)) :=
      AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth _
    exact ⟨MMP.Resolution.isReduced_subscheme_of_stalk_eq_span_parameter H hHD,
      MMP.Resolution.isPureCodimOne_support_of_stalk_eq_span_parameter H hHD,
      (MMP.Mori.isSmoothScheme_iff _).mpr hH⟩
  · exact hG.1 i

/-- The general position property holds on a dense open of the coefficient space. -/
private lemma exists_dense_open_sncProp [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [Smooth (j ≫ X ↘ Spec (.of k))]
    {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) :
    ∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U → SNCProp s j G c := by
  let Yι : Option (Set Λ) → Scheme.{u} := fun o => o.elim Y fun J => (stratum G J).subscheme
  let ι : (o : Option (Set Λ)) → Yι o ⟶ X := fun o => match o with
    | none => j
    | some J => (stratum G J).subschemeι ≫ j
  have : ∀ o, IsImmersion (ι o) := fun o => match o with
    | none => inferInstanceAs (IsImmersion j)
    | some J => inferInstanceAs (IsImmersion ((stratum G J).subschemeι ≫ j))
  have : ∀ o, Smooth (ι o ≫ X ↘ Spec (.of k)) := fun o => match o with
    | none => inferInstanceAs (Smooth (j ≫ X ↘ Spec (.of k)))
    | some J => by
      have := smooth_stratum (k := k) j G hG J
      change Smooth (((stratum G J).subschemeι ≫ j) ≫ X ↘ Spec (.of k))
      rwa [Category.assoc]
  obtain ⟨⟨U₁, hU₁, hc₁⟩, -⟩ := exists_dense_open_smooth_zeroScheme (k := k) s hs ι
  obtain ⟨U₂, hU₂, hc₂⟩ := exists_dense_open_not_subset s hs j G hG
  refine ⟨U₁ ⊓ U₂, hU₁.inter_of_isOpen_left hU₂ U₁.isOpen, fun c hc => ?_⟩
  have h₁ := (hc₁ c hc.1).2
  have hW := hc₂ c hc.2
  have hH : Smooth (((zeroScheme X L (systemSection s c)).comap j).subschemeι ≫ j ≫
      X ↘ Spec (.of k)) := h₁ none
  refine ⟨hH, hW, isSNCFamily_of_smooth_strata s j G hG c hH (fun J => ?_) hW⟩
  have : Smooth (((zeroScheme X L (systemSection s c)).comap
      ((stratum G J).subschemeι ≫ j)).subschemeι ≫ ((stratum G J).subschemeι ≫ j) ≫
        X ↘ Spec (.of k)) := h₁ (some J)
  simpa only [Category.assoc] using this

/-- The general position property is invariant under scaling the coefficients. -/
private lemma sncProp_smul (s : Fin (N + 1) → Γ(L, ⊤)) {Y : Scheme.{u}} (j : Y ⟶ X)
    {Λ : Type u} (G : Λ → Y.IdealSheafData) (c : Fin (N + 1) → k) {t : k} (ht : t ≠ 0) :
    SNCProp s j G (t • c) ↔ SNCProp s j G c := by
  unfold SNCProp
  rw [zeroScheme_systemSection_smul s c ht]

/-- **Bertini's theorem for a free system and an snc divisor, characteristic zero.** Let `X` be a
variety over an algebraically closed field `k` of characteristic zero, `s₀, …, s_N` global
sections of an invertible sheaf `L` generating it, `j : Y ⟶ X` an immersion with `Y` smooth over
`k`, and `G = (Gᵢ)_{i ∈ Λ}` a finite simple normal crossing family on `Y`. Then there is a dense
open `U` of `𝔸ᴺ⁺¹_k`, and a dense open `U'` of `ℙᴺ_k`, such that for every `c` with
`c ∈ U` (resp. `c ≠ 0` and `[c] ∈ U'`) the trace `H = j⁻¹ Z(∑ᵢ cᵢ sᵢ)` is smooth over `k`,
contains no irreducible component of `⋂_{i ∈ J} Gᵢ` for any `J ⊆ Λ`, and `H + G` is a simple
normal crossing family on `Y`. -/
@[mmp "lem_mmp_foundation_free_system_snc_bertini"]
public theorem exists_dense_open_isSNCFamily_zeroScheme [IsAlgClosed k] [CharZero k]
    [IsVariety k (X ↘ Spec (.of k))]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen X L (systemSection s c) = ⊤)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [Smooth (j ≫ X ↘ Spec (.of k))]
    {Λ : Type u} [Finite Λ] (G : Λ → Y.IdealSheafData)
    (hG : IsSNCFamily (j ≫ X ↘ Spec (.of k)) G) :
    (∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        let H := (zeroScheme X L (systemSection s c)).comap j
        Smooth (H.subschemeι ≫ j ≫ X ↘ Spec (.of k)) ∧
        (∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
          ¬ W ⊆ (H.support : Set Y)) ∧
        IsSNCFamily (j ≫ X ↘ Spec (.of k)) (fun o : Option Λ => o.elim H G)) ∧
    (∃ U : (AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N)).Opens,
      Dense (U : Set (AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k N))) ∧
      ∀ (c : Fin (N + 1) → k) (hc : c ≠ 0), dualPoint c hc ∈ U →
        let H := (zeroScheme X L (systemSection s c)).comap j
        Smooth (H.subschemeι ≫ j ≫ X ↘ Spec (.of k)) ∧
        (∀ (J : Set Λ), ∀ W ∈ componentsOf (⋂ i ∈ J, ((G i).support : Set Y)),
          ¬ W ⊆ (H.support : Set Y)) ∧
        IsSNCFamily (j ≫ X ↘ Spec (.of k)) (fun o : Option Λ => o.elim H G)) := by
  classical
  obtain ⟨U, hU, hUc⟩ := exists_dense_open_sncProp s hs j G hG
  obtain ⟨Q, hQ0, hQU⟩ := exists_ne_zero_basicOpen_le U hU
  have hQ : ∀ c : Fin (N + 1) → k, MvPolynomial.eval c Q ≠ 0 → SNCProp s j G c := by
    intro c hc
    refine hUc c (hQU ?_)
    change Q ∉ RingHom.ker (MvPolynomial.eval c)
    exact fun h => hc ((RingHom.mem_ker).mp h)
  refine ⟨⟨U, hU, hUc⟩, ?_⟩
  obtain ⟨d, hd⟩ := exists_homogeneousComponent_ne_zero hQ0
  refine ⟨ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
      (MvPolynomial.homogeneousComponent d Q), dense_projectiveSpace_basicOpen hd,
    fun c hc hmem => ?_⟩
  obtain ⟨t, ht, htQ⟩ := exists_ne_zero_eval_smul_ne_zero Q c
    (eval_homogeneousComponent_ne_zero_of_mem hc hmem)
  exact (sncProp_smul s j G c ht).mp (hQ (t • c) htQ)

end SNC

end MMP.Threefold.Bridges

end
