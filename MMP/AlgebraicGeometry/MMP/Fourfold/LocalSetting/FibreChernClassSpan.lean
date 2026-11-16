module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.GAGA.ProjectiveParts.Picard
public import MMP.AlgebraicGeometry.Analytic.ExponentialFirstChernClass
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreH2Vanishing
import MMP.AlgebraicGeometry.Analytic.FiniteCochainsBetti

/-!
# First Chern classes span the second cohomology of a resolution fibre

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and `y ∈ Y` a closed point
whose scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` (`MMP.Fourfold.pointSettingFibre`) has dimension at
most two. Then the first Chern classes `c₁(L) ∈ H²(F_y; ℚ)` of the invertible modules `L` on
`F_y` span `H²(F_y; ℚ)`.

The fibre is a projective complex scheme with `H²(F_y, 𝒪_{F_y}) = 0`. By GAGA and the
exponential sequence on `F_y^an`, the first Chern class `Pic(F_y) ⟶ H²(F_y; ℤ)` is onto, and
tensoring with `ℚ` gives the statement.

## Main results

* `MMP.Fourfold.IsLocalSetting.span_firstChernClass_pointSettingFibre_eq_top`: the span.

## Implementation notes

* `F_y` is a scheme over `ℂ` through `F_y ⟶ Ỹ ⟶ Y ⟶ Spec ℂ`; its cohomology `H²(F_y; ℚ)` is
  the singular cohomology `MMP.Fourfold.rationalCohomology` of its complex points, and the
  rational first Chern class of an invertible module is `MMP.Analytic.algebraicFirstChernClass`
  carried to `ℚ`-coefficients, as in `MMP.Fourfold.pointFibreChernClass`.
* The dimension of `F_y` is the Krull dimension of its underlying topological space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.OAI4LocalSchemeFibreVanishingB

attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax
attribute [local instance] MMP.Analytic.globalSections_additive

section AnalyticLineBundle

open Filter Topology Opposite MMP.Analytic MMP.Analytic.ComplexPoints MMP.Analytic.Analytification

attribute [local implicit_reducible] TopCat.Sheaf

section Residue

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

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
  letI := (ComplexPoints.baseRingHom sX U).toAlgebra
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

variable {n : ℕ}

private lemma exists_rep {p : Fin n → ℂ} (g : holGerms p) :
    ∃ f : (Fin n → ℂ) → ℂ, (g : Germ (𝓝 p) ℂ) = f ∧ ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f, hf, hd⟩ := g.2
  exact ⟨f, hf.symm, hd⟩

private lemma mk_surjective (c : Chart sX) (p : Fin c.n → ℂ) (a : c.StalkRing p) :
    ∃ g, Chart.StalkRing.mk c p g = a :=
  Ideal.Quotient.mk_surjective a

private lemma residue_of_eq_mk (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    {a : c.StalkRing (c.coords y)} {g : holGerms (c.coords y)} {f : (Fin c.n → ℂ) → ℂ}
    (ha : a = Chart.StalkRing.mk c _ g) (hg : (g : Germ (𝓝 (c.coords y)) ℂ) = f) :
    residue c y a = f (c.coords y) := by
  rw [ha, residue_mk, hg]
  rfl

private lemma eventually_differentiableAt_of_coe_eq {p : Fin n → ℂ} (g : holGerms p)
    {f : (Fin n → ℂ) → ℂ} (hf : (g : Germ (𝓝 p) ℂ) = f) :
    ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ f y := by
  obtain ⟨f', hf', hd⟩ := exists_rep g
  have heq : f' =ᶠ[𝓝 p] f := Germ.coe_eq.1 (hf'.symm.trans hf)
  exact (hd.and heq.eventuallyEq_nhds).mono fun y hy => hy.1.congr_of_eventuallyEq hy.2.symm

private lemma residue_transition {c d : Chart sX} (m : ChartHom c d)
    (y : ComplexPoints.chart (sX := sX) d.U) (a : c.StalkRing (c.coords (m.incl y))) :
    residue d y (m.transition y a) = residue c (m.incl y) a := by
  obtain ⟨g, rfl⟩ := mk_surjective c _ a
  obtain ⟨f, hf, -⟩ := exists_rep g
  rw [m.transition_mk, residue_mk, residue_mk, coe_holPullback, hf, Germ.coe_compTendsto]
  change f (m.polyMap (d.coords y)) = f (c.coords (m.incl y))
  rw [m.coords_incl]

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
  letI := ComplexPoints.chartTopology (sX := sX) (U' : X.Opens)
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
  letI := ComplexPoints.chartTopology (sX := sX) c.U
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
  rw [residue_eq_of_isCompatible s.2.2 y d c hd hyc, hres _ hyO]
  exact hyN

variable (sX) [LocallyOfFiniteType sX]

/-- A chart containing a given `ℂ`-point. -/
private noncomputable def pointChart (x : space sX) :
    {c : Chart sX // x ∈ ComplexPoints.chart c.U} :=
  ⟨(exists_chart x).choose, (exists_chart x).choose_spec⟩

/-- The value at a point of a section of `𝒪_{X^an}`: the residue of its component in
`pointChart`. -/
private noncomputable def sectionValue {W : Opens (space sX)}
    (s : (structureSheaf sX).obj.obj (op W)) (x : W) : ℂ :=
  residue (pointChart sX x.1).1 ⟨x.1, (pointChart sX x.1).2⟩ (s.1 x (pointChart sX x.1))

/-- Values of sections of `𝒪_{X^an}` are continuous functions. -/
private lemma continuous_sectionValue {W : Opens (space sX)}
    (s : (structureSheaf sX).obj.obj (op W)) : Continuous (sectionValue sX s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨V, hxV, hV⟩ := exists_opens_residue_mem s x (pointChart sX x.1).1 (pointChart sX x.1).2
    (N := N) (by rwa [← sectionValue])
  exact Filter.mem_of_superset ((V.isOpen.preimage continuous_subtype_val).mem_nhds hxV)
    fun y hy => hV y hy _ _

end Residue

section Value

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

variable [LocallyOfFiniteType sX]

/-- The value of a section of `𝒪_{X^an}` is its residue in any chart. -/
private lemma sectionValue_eq_residue {W : Opens (space sX)}
    (s : (structureSheaf sX).obj.obj (op W)) (x : W) (c : Chart sX)
    (hc : x.1 ∈ ComplexPoints.chart c.U) :
    sectionValue sX s x = residue c ⟨x.1, hc⟩ (s.1 x ⟨c, hc⟩) :=
  residue_eq_of_isCompatible s.2.2 x _ _ _ _

/-- Values of sections are compatible with restriction. -/
private lemma sectionValue_res {W W' : Opens (space sX)} (h : W' ≤ W)
    (s : (structureSheaf sX).obj.obj (op W)) (x : W') :
    sectionValue sX ((structureSheaf sX).obj.map (homOfLE h).op s) x =
      sectionValue sX s ⟨x.1, h x.2⟩ :=
  rfl

variable (sX) in
/-- Evaluation at a point of sections of `𝒪_{X^an}`, as a ring homomorphism. -/
private noncomputable def sectionValueHom (W : Opens (space sX)) (x : W) :
    (structureSheaf sX).obj.obj (op W) →+* ℂ where
  toFun s := sectionValue sX s x
  map_one' := map_one (residue _ _)
  map_mul' s t := map_mul (residue _ _) _ _
  map_zero' := map_zero (residue _ _)
  map_add' s t := map_add (residue _ _) _ _

/-- The residue of an algebraic function is its value. -/
private lemma residue_toStalkRing (c : Chart sX) (y : ComplexPoints.chart (sX := sX) c.U)
    (f : Γ(X, c.U)) : residue c y (c.toStalkRing (c.coords y) f) = evalHom c.U y f := by
  obtain ⟨q, rfl⟩ := c.surjective f
  change residue c y (c.toStalkRing (c.coords y) (c.pres q)) = evalHom c.U y (c.pres q)
  rw [c.toStalkRing_pres, residue_mk, coe_polyGermHom, c.evalHom_pres]
  rfl

/-- The value of the analytification of an algebraic function is its value. -/
private lemma sectionValue_sharpHom (V : X.Opens) (g : Γ(X, V))
    (x : (Opens.map (toSchemeHom sX)).obj V) :
    sectionValue sX (show (structureSheaf sX).obj.obj (op ((Opens.map (toSchemeHom sX)).obj V))
      from sharpHom V g) x = evalHom V ⟨x.1, ComplexPoints.mem_chart_iff.2 x.2⟩ g := by
  obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x.1.toScheme ∈ V from x.2)
  obtain ⟨n, gen, h⟩ := exists_gens (sX := sX) hU
  let c : Chart sX := ⟨U, hU, n, gen, h⟩
  have hc : x.1 ∈ ComplexPoints.chart c.U := ComplexPoints.mem_chart_iff.2 hxU
  rw [sectionValue_eq_residue _ x c hc]
  change residue c ⟨x.1, hc⟩ (c.stalkHom ⟨x.1, hc⟩ (X.presheaf.germ V x.1.toScheme x.2 g)) = _
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUV) x.1.toScheme hxU g,
    c.stalkHom_germ, residue_toStalkRing]
  exact (evalHom_res hUV ⟨x.1, hc⟩ g).symm

variable (sX) in
/-- Evaluation at a point `y` on the stalk of `𝒪_{X^an}` at `y`. -/
private noncomputable def stalkValue (y : space sX) : (analytification sX).presheaf.stalk y →+* ℂ :=
  (colimit.desc ((OpenNhds.inclusion y).op ⋙ (structureSheaf sX).obj)
    ⟨CommRingCat.of ℂ,
      { app := fun U => CommRingCat.ofHom (sectionValueHom sX U.unop.1 ⟨y, U.unop.2⟩)
        naturality := fun U U' i => by
          ext s
          exact sectionValue_res (sX := sX) i.unop.le s ⟨y, U'.unop.2⟩ }⟩).hom

/-- Evaluation on the stalk of a germ is the value of the section. -/
private lemma stalkValue_germ (y : space sX) (W : Opens (space sX)) (hy : y ∈ W)
    (s : (structureSheaf sX).obj.obj (op W)) :
    stalkValue sX y ((analytification sX).presheaf.germ W y hy s) = sectionValue sX s ⟨y, hy⟩ :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion y).op ⋙ (structureSheaf sX).obj) _ (op ⟨W, hy⟩)) s

end Value

section Stalk

/-- The germ at `x` of a section `a` over `W ∋ x` generates the stalk if every restriction of `a`
generates the sections over its domain. -/
private lemma surjective_smul_germ_of_surjective {T : TopCat.{0}}
    {R : TopCat.Presheaf CommRingCat.{0} T}
    (F' : PresheafOfModules.{0} (R ⋙ forget₂ CommRingCat RingCat)) {W : Opens T}
    (a : F'.obj (op W))
    (ha : ∀ (V : Opens T) (h : V ≤ W), Function.Surjective fun c : R.obj (op V) =>
      c • F'.map (homOfLE h).op a) (x : T) (hx : x ∈ W) :
    Function.Surjective fun b : R.stalk x =>
      b • TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf W x hx a := by
  intro n
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.germ_exist F'.presheaf n
  let h₁ : V ⊓ W ≤ V := inf_le_left
  let h₂ : V ⊓ W ≤ W := inf_le_right
  obtain ⟨c, hc⟩ := ha (V ⊓ W) h₂ (F'.map (homOfLE h₁).op m)
  refine ⟨R.germ (V ⊓ W) x ⟨hxV, hx⟩ c, ?_⟩
  dsimp only at hc ⊢
  exact (congrArg (R.germ (V ⊓ W) x ⟨hxV, hx⟩ c • ·)
      (TopCat.Presheaf.germ_res_apply F'.presheaf (homOfLE h₂) x ⟨hxV, hx⟩ a).symm).trans
    ((PresheafOfModules.germ_smul F' x _ _ c _).symm.trans ((congrArg _ hc).trans
      (TopCat.Presheaf.germ_res_apply F'.presheaf (homOfLE h₁) x _ m)))

/-- The stalk at `x` of a presheaf of modules is free of rank one on the germ of a section `a`
over `W ∋ x` all of whose restrictions are bases. -/
private lemma bijective_smul_germ_of_bijective {T : TopCat.{0}}
    {R : TopCat.Presheaf CommRingCat.{0} T}
    (F' : PresheafOfModules.{0} (R ⋙ forget₂ CommRingCat RingCat)) {W : Opens T}
    (a : F'.obj (op W))
    (ha : ∀ (V : Opens T) (h : V ≤ W), Function.Bijective fun c : R.obj (op V) =>
      c • F'.map (homOfLE h).op a) (x : T) (hx : x ∈ W) :
    Function.Bijective fun b : R.stalk x =>
      b • TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf W x hx a := by
  have hsmul : ∀ (V : Opens T) (hxV : x ∈ V) (c : R.obj (op V)) (m : F'.obj (op V)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf V x hxV (c • m) =
        R.germ V x hxV c • TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf V x hxV m :=
    fun V hxV c m => PresheafOfModules.germ_smul F' x V hxV c m
  have hres : ∀ {V V' : Opens T} (h : V' ≤ V) (hxV' : x ∈ V') (m : F'.obj (op V)),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf V' x hxV'
          (F'.map (homOfLE h).op m) =
        TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf V x (h hxV') m :=
    fun h hxV' m => TopCat.Presheaf.germ_res_apply F'.presheaf (homOfLE h) x hxV' m
  have hmapsmul : ∀ {V V' : Opens T} (h : V' ≤ V) (c : R.obj (op V)) (m : F'.obj (op V)),
      F'.map (homOfLE h).op (c • m) = R.map (homOfLE h).op c • F'.map (homOfLE h).op m :=
    fun h c m => F'.map_smul (homOfLE h).op c m
  have hmapmap : ∀ {V V' V'' : Opens T} (h : V' ≤ V) (h' : V'' ≤ V') (m : F'.obj (op V)),
      F'.map (homOfLE h').op (F'.map (homOfLE h).op m) = F'.map (homOfLE (h'.trans h)).op m :=
    fun h h' m => (PresheafOfModules.map_comp_apply F' (homOfLE h).op (homOfLE h').op m).symm
  refine ⟨?_, ?_⟩
  · change Function.Injective (LinearMap.toSpanSingleton (R.stalk x) _
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf W x hx a))
    refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
    obtain ⟨U, hxU, c, rfl⟩ := TopCat.Presheaf.germ_exist R b
    let h₁ : U ⊓ W ≤ U := inf_le_left
    let h₂ : U ⊓ W ≤ W := inf_le_right
    have hxU' : x ∈ U ⊓ W := ⟨hxU, hx⟩
    rw [← TopCat.Presheaf.germ_res_apply R (homOfLE h₁) x hxU' c] at hb ⊢
    rw [LinearMap.toSpanSingleton_apply, ← hres h₂ hxU'] at hb
    have hb' : TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) F'.presheaf (U ⊓ W) x hxU'
        (R.map (homOfLE h₁).op c • F'.map (homOfLE h₂).op a) = 0 :=
      (hsmul _ hxU' _ _).trans hb
    obtain ⟨V, hxV, iU, iV, hV⟩ := TopCat.Presheaf.germ_eq F'.presheaf x hxU' hxU' _ 0
      (hb'.trans (map_zero _).symm)
    have hiV : iV = homOfLE iU.le := Subsingleton.elim _ _
    rw [hiV, map_zero] at hV
    have hV' : R.map (homOfLE iU.le).op (R.map (homOfLE h₁).op c) •
        F'.map (homOfLE (iU.le.trans h₂)).op a = (0 : R.obj (op V)) •
          F'.map (homOfLE (iU.le.trans h₂)).op a := by
      rw [zero_smul, ← hmapmap h₂ iU.le]
      exact (hmapsmul iU.le _ _).symm.trans hV
    have h0 := (ha V (iU.le.trans h₂)).1 hV'
    rw [← TopCat.Presheaf.germ_res_apply R (homOfLE iU.le) x hxV]
    exact (congrArg _ h0).trans (map_zero _)
  · exact surjective_smul_germ_of_surjective F' a (fun V h => (ha V h).2) x hx

end Stalk

section Triv

open MMP.Analytic.InvertibleModule

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- A sheaf of `𝒪_{X^an}`-modules, as a presheaf of modules over the commutative structure
presheaf. -/
private abbrev anMod (N : SheafOfModules.{0} (ringCatSheaf sX)) :
    PresheafOfModules.{0} ((structureSheaf sX).obj ⋙ forget₂ CommRingCat RingCat) :=
  N.val

/-- An `𝒪_X`-module, as a presheaf of modules over the commutative structure presheaf. -/
private abbrev algMod (L : X.Modules) :
    PresheafOfModules.{0} (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  L.val

/-- The `𝒪_{X^an,y}`-module structure of the stalk at `y` of an `𝒪_{X^an}`-module. -/
private noncomputable abbrev stalkModule (N : SheafOfModules.{0} (ringCatSheaf sX)) (y : space sX) :
    Module ((analytification sX).presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (anMod N).presheaf y) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (anMod N) y

attribute [local instance] stalkModule

variable [LocallyOfFiniteType sX] [QuasiCompact sX] {L : X.Modules}

/-- The section `s^an` of `L^an` over `α_X⁻¹ W` of a section `s` of `L` over `W`. -/
private noncomputable abbrev anSec (L : X.Modules) {W : X.Opens} (a : Γ(L, W)) :
    (anMod ((analytifyModule sX).obj L)).obj (op ((Opens.map (toSchemeHom sX)).obj W)) :=
  (analytifyModuleUnit sX L).val.app (op W) a

/-- If `N ≅ A ⊗_B P` and `P` is free of rank one on `g`, then `N` is free of rank one over `A` on
the element corresponding to `1 ⊗ g`. -/
private lemma exists_linearEquiv_eq_one_of_tensor {A B N P : Type*} [CommRing A] [CommRing B]
    [Algebra B A] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module B P]
    (e : N ≃ₗ[A] TensorProduct B A P) (g : P) (hg : Function.Bijective fun b : B => b • g)
    (n : N) (hn : e n = 1 ⊗ₜ g) : ∃ ψ : N ≃ₗ[A] A, ψ n = 1 := by
  let φ := LinearEquiv.ofBijective (LinearMap.toSpanSingleton B P g) hg
  have hφ : φ.symm g = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    exact (one_smul B g).symm
  refine ⟨e.trans ((LinearEquiv.baseChange _ _ _ _ φ.symm).trans
    (TensorProduct.AlgebraTensorModule.rid _ _ _)), ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hn, LinearEquiv.baseChange_tmul, hφ,
    TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]

/-- Near a point of the open of a local generator `a` of `L`, the stalk of `L^an` is trivialised
by the germ of `a^an`. -/
private lemma exists_stalkTriv (s : Generator L) (y : space sX) (hy : y.toScheme ∈ s.W) :
    ∃ ψ : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0})
        (anMod ((analytifyModule sX).obj L)).presheaf y
        ≃ₗ[(analytification sX).presheaf.stalk y] (analytification sX).presheaf.stalk y,
      ψ (TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) (anMod ((analytifyModule sX).obj L)).presheaf
        ((Opens.map (toSchemeHom sX)).obj s.W) y hy (anSec L s.a)) = 1 := by
  obtain ⟨e, he⟩ := (analytification_stalks sX).2.2.1 L y
  letI : Algebra (X.presheaf.stalk y.toScheme) ((analytification sX).presheaf.stalk y) :=
    ((analytificationHom sX).hom.stalkMap y).hom.toAlgebra
  letI : Module (X.presheaf.stalk y.toScheme)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (algMod L).presheaf y.toScheme) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier (algMod L) _
  exact exists_linearEquiv_eq_one_of_tensor e _
    (bijective_smul_germ_of_bijective (algMod L) s.a (fun V h => s.bijective V h) y.toScheme hy)
    _ (he s.W hy s.a)

/-- The trivialisation `(L^an)_y ≅ 𝒪_{X^an,y}` by the germ of `a^an` for a local generator `a`. -/
private noncomputable def stalkTriv (s : Generator L) (y : space sX) (hy : y.toScheme ∈ s.W) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (anMod ((analytifyModule sX).obj L)).presheaf y
      ≃ₗ[(analytification sX).presheaf.stalk y] (analytification sX).presheaf.stalk y :=
  (exists_stalkTriv s y hy).choose

/-- `stalkTriv s` sends the germ of `a^an` to `1`. -/
private lemma stalkTriv_germ_anSec (s : Generator L) (y : space sX) (hy : y.toScheme ∈ s.W) :
    stalkTriv s y hy (TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule sX).obj L)).presheaf ((Opens.map (toSchemeHom sX)).obj s.W) y hy
        (anSec L s.a)) = 1 :=
  (exists_stalkTriv s y hy).choose_spec

/-- Every element of the stalk of `L^an` is its coefficient times the germ of `a^an`. -/
private lemma eq_stalkTriv_smul (s : Generator L) (y : space sX) (hy : y.toScheme ∈ s.W)
    (n : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule sX).obj L)).presheaf y) :
    n = stalkTriv s y hy n • TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule sX).obj L)).presheaf ((Opens.map (toSchemeHom sX)).obj s.W) y hy
        (anSec L s.a) := by
  apply (stalkTriv s y hy).injective
  rw [map_smul, stalkTriv_germ_anSec, smul_eq_mul, mul_one]

/-- Analytification of sections commutes with restriction. -/
private lemma anSec_res {V W : X.Opens} (h : V ≤ W) (m : Γ(L, W)) :
    anSec (sX := sX) L (sectionRes L h m) =
      (anMod ((analytifyModule sX).obj L)).map
        (homOfLE ((Opens.map (toSchemeHom sX)).monotone h)).op (anSec L m) :=
  PresheafOfModules.naturality_apply (analytifyModuleUnit sX L).val (homOfLE h).op m

/-- Germs of analytified sections are compatible with restriction. -/
private lemma germ_anSec_res {V W : X.Opens} (h : V ≤ W) (m : Γ(L, W)) (y : space sX)
    (hy : y.toScheme ∈ V) :
    TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) (anMod ((analytifyModule sX).obj L)).presheaf
        ((Opens.map (toSchemeHom sX)).obj V) y hy (anSec L (sectionRes L h m)) =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{0}) (anMod ((analytifyModule sX).obj L)).presheaf
        ((Opens.map (toSchemeHom sX)).obj W) y (h hy) (anSec L m) := by
  rw [anSec_res]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/-- Analytification of sections is semilinear along `α_X^#`. -/
private lemma anSec_smul {W : X.Opens} (c : Γ(X, W)) (m : Γ(L, W)) :
    anSec (sX := sX) L (c • m) =
      (show (structureSheaf sX).obj.obj (op ((Opens.map (toSchemeHom sX)).obj W)) from
        sharpHom W c) • anSec L m :=
  ((analytifyModuleUnit sX L).val.app (op W)).hom.map_smul c m

/-- The coefficient of `a^an` with respect to `a'^an` is the germ of the transition function. -/
private lemma stalkTriv_germ_anSec_of_generator (s s' : Generator L) (y : space sX)
    (hy : y.toScheme ∈ s.W) (hy' : y.toScheme ∈ s'.W) (hyy : y.toScheme ∈ s.W ⊓ s'.W) :
    stalkTriv s' y hy' (TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule sX).obj L)).presheaf ((Opens.map (toSchemeHom sX)).obj s.W) y hy
        (anSec L s.a)) =
      (analytification sX).presheaf.germ ((Opens.map (toSchemeHom sX)).obj (s.W ⊓ s'.W)) y
        hyy (sharpHom _ (transitionSection s s')) := by
  rw [← germ_anSec_res inf_le_left s.a y hyy, ← transitionSection_smul s s', anSec_smul]
  refine (congrArg (stalkTriv s' y hy')
    (PresheafOfModules.germ_smul (anMod ((analytifyModule sX).obj L)) y _ hyy _ _)).trans ?_
  rw [germ_anSec_res inf_le_right s'.a y hyy, map_smul, stalkTriv_germ_anSec, smul_eq_mul, mul_one]

/-- Near a point `x₀` of the open of a local generator `a`, the coefficient of a section `m` of
`L^an` with respect to `a^an` is the germ of a single analytic function. -/
private lemma exists_stalkTriv_eq_germ (s : Generator L) {V : Opens (space sX)}
    (m : (anMod ((analytifyModule sX).obj L)).obj (op V)) (x₀ : space sX) (hx₀V : x₀ ∈ V)
    (hx₀ : x₀.toScheme ∈ s.W) :
    ∃ (U : Opens (space sX)) (_ : x₀ ∈ U) (hUV : U ≤ V)
      (hUs : U ≤ (Opens.map (toSchemeHom sX)).obj s.W)
      (σ : (structureSheaf sX).obj.obj (op U)), ∀ (x : space sX) (hx : x ∈ U),
        stalkTriv s x (hUs hx) (TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
          (anMod ((analytifyModule sX).obj L)).presheaf V x (hUV hx) m) =
          (analytification sX).presheaf.germ U x hx σ := by
  obtain ⟨U₁, hx₀U₁, σ₁, hσ₁⟩ := TopCat.Presheaf.germ_exist (analytification sX).presheaf
    (stalkTriv s x₀ hx₀ (TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule sX).obj L)).presheaf V x₀ hx₀V m))
  let U₂ : Opens (space sX) := U₁ ⊓ V ⊓ (Opens.map (toSchemeHom sX)).obj s.W
  have h₂₁ : U₂ ≤ U₁ := inf_le_left.trans inf_le_left
  have h₂s : U₂ ≤ (Opens.map (toSchemeHom sX)).obj s.W := inf_le_right
  have hx₀U₂ : x₀ ∈ U₂ := ⟨⟨hx₀U₁, hx₀V⟩, hx₀⟩
  let m₂ : (anMod ((analytifyModule sX).obj L)).obj (op U₂) :=
    (structureSheaf sX).obj.map (homOfLE h₂₁).op σ₁ •
    (anMod ((analytifyModule sX).obj L)).map (homOfLE h₂s).op (anSec L s.a)
  have hgerm : ∀ (x : space sX) (hx : x ∈ U₂),
      TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
          (anMod ((analytifyModule sX).obj L)).presheaf U₂ x hx m₂ =
        (analytification sX).presheaf.germ U₁ x (h₂₁ hx) σ₁ •
          TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
            (anMod ((analytifyModule sX).obj L)).presheaf
            ((Opens.map (toSchemeHom sX)).obj s.W) x (h₂s hx) (anSec L s.a) := by
    intro x hx
    refine (PresheafOfModules.germ_smul (anMod ((analytifyModule sX).obj L)) x U₂ hx _ _).trans ?_
    rw [TopCat.Presheaf.germ_res_apply]
    exact congrArg _
      (TopCat.Presheaf.germ_res_apply (anMod ((analytifyModule sX).obj L)).presheaf
        (homOfLE h₂s) x hx _)
  have hm₂ : TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule sX).obj L)).presheaf U₂ x₀ hx₀U₂ m₂ =
      TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
        (anMod ((analytifyModule sX).obj L)).presheaf V x₀ hx₀V m := by
    rw [hgerm, hσ₁]
    exact (eq_stalkTriv_smul s x₀ hx₀ _).symm
  obtain ⟨U, hx₀U, iV, i₂, hU⟩ :=
    TopCat.Presheaf.germ_eq (anMod ((analytifyModule sX).obj L)).presheaf x₀ hx₀V hx₀U₂ m m₂
      hm₂.symm
  refine ⟨U, hx₀U, iV.le, i₂.le.trans h₂s, (structureSheaf sX).obj.map (i₂ ≫ homOfLE h₂₁).op σ₁,
    fun x hx => ?_⟩
  have e1 := (TopCat.Presheaf.germ_res_apply (anMod ((analytifyModule sX).obj L)).presheaf iV x hx
    m).symm
  rw [e1, hU, TopCat.Presheaf.germ_res_apply (anMod ((analytifyModule sX).obj L)).presheaf i₂ x hx
    m₂, hgerm, map_smul]
  refine (congrArg (_ • ·) (stalkTriv_germ_anSec s x _)).trans ?_
  rw [smul_eq_mul, mul_one, TopCat.Presheaf.germ_res_apply]

end Triv

section Bundle

open MMP.Analytic.InvertibleModule Bundle

attribute [local instance] stalkModule

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [QuasiCompact (X ↘ Spec (.of ℂ))] (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

/-- The chart of `L^top` at `y`. -/
private noncomputable abbrev idx (y : space (X ↘ Spec (.of ℂ))) : Generator L :=
  (lineBundleCore L).indexAt y

/-- A point lies in the open of the chart of `L^top` at it. -/
private lemma mem_idx (y : space (X ↘ Spec (.of ℂ))) : y.toScheme ∈ (idx L y).W :=
  ComplexPoints.mem_chart_iff.1 ((lineBundleCore L).mem_baseSet_at y)

/-- The value at `y`, in the chart of `L^top` at `y`, of a section of `L^an`. -/
private noncomputable def valN (V : Opens (space (X ↘ Spec (.of ℂ))))
    (m : (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).obj (op V)) (y : V) : ℂ :=
  stalkValue _ y.1 (stalkTriv (idx L y.1) y.1 (mem_idx L y.1)
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).presheaf V y.1 y.2 m))

variable {L}

/-- Change of chart for values of coefficients: multiplication by the transition function. -/
private lemma stalkValue_stalkTriv_change (s s' : Generator L) (y : space (X ↘ Spec (.of ℂ)))
    (hy : y.toScheme ∈ s.W) (hy' : y.toScheme ∈ s'.W)
    (n : TopCat.Presheaf.stalk (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).presheaf y) :
    stalkValue _ y (stalkTriv s' y hy' n) =
      evalExt _ (transitionSection s s') y * stalkValue _ y (stalkTriv s y hy n) := by
  conv_lhs => rw [eq_stalkTriv_smul s y hy n]
  rw [map_smul, stalkTriv_germ_anSec_of_generator s s' y hy hy' (Opens.mem_inf.2 ⟨hy, hy'⟩),
    smul_eq_mul, map_mul, mul_comm]
  congr 1
  exact (stalkValue_germ _ _ _ _).trans ((sectionValue_sharpHom _ _ _).trans
    (evalExt_of_mem (U := s.W ⊓ s'.W) (transitionSection s s') (x := y)
      (ComplexPoints.mem_chart_iff.2 (Opens.mem_inf.2 ⟨hy, hy'⟩))).symm)

variable (L)

/-- `valN` is additive. -/
private lemma valN_add (V : Opens (space (X ↘ Spec (.of ℂ))))
    (m m' : (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).obj (op V)) (y : V) :
    valN L V (m + m') y = valN L V m y + valN L V m' y := by
  simp only [valN]
  refine (congrArg (fun z => stalkValue _ _ (stalkTriv _ _ _ z))
    (map_add (ConcreteCategory.hom (TopCat.Presheaf.germ (C := AddCommGrpCat.{0})
      (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).presheaf V y.1 y.2)) m m')).trans ?_
  rw [map_add, map_add]
  rfl

/-- `valN` is compatible with restriction. -/
private lemma valN_res {V W : Opens (space (X ↘ Spec (.of ℂ)))} (h : W ≤ V)
    (m : (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).obj (op V)) (y : W) :
    valN L W ((anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).map (homOfLE h).op m) y =
      valN L V m ⟨y.1, h y.2⟩ := by
  simp only [valN]
  exact congrArg (fun z => stalkValue _ _ (stalkTriv _ _ _ z))
    (TopCat.Presheaf.germ_res_apply (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).presheaf
      (homOfLE h) y.1 y.2 m)

/-- `valN` is semilinear along evaluation of analytic functions. -/
private lemma valN_smul (V : Opens (space (X ↘ Spec (.of ℂ))))
    (σ : (structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op V))
    (m : (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).obj (op V)) (x : V)
    (c : {c : Chart (X ↘ Spec (.of ℂ)) // x.1 ∈ ComplexPoints.chart c.U})
    (g : holGerms (c.1.coords ⟨x.1, c.2⟩)) (hg : σ.1 x c = Chart.StalkRing.mk c.1 _ g) :
    valN L V (σ • m) x = Germ.value (g : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) * valN L V m x := by
  simp only [valN]
  rw [PresheafOfModules.germ_smul, map_smul, smul_eq_mul, map_mul, stalkValue_germ,
    sectionValue_eq_residue σ x c.1 c.2, hg, residue_mk]

/-- The value of the analytification of the chart generator at `y` is `1`. -/
private lemma valN_anSec (y : space (X ↘ Spec (.of ℂ))) :
    valN L ((Opens.map (toSchemeHom _)).obj (idx L y).W) (anSec L (idx L y).a)
      ⟨y, mem_idx L y⟩ = 1 := by
  simp only [valN]
  rw [stalkTriv_germ_anSec, map_one]

/-- `valN` is a continuous section of `L^top`. -/
private lemma continuous_valN (V : Opens (space (X ↘ Spec (.of ℂ))))
    (m : (anMod ((analytifyModule (X ↘ Spec (.of ℂ))).obj L)).obj (op V)) :
    Continuous fun x : V => (⟨x.1, valN L V m x⟩ : TotalSpace ℂ (topologicalLineBundle L)) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  obtain ⟨U, hx₀U, hUV, hUs, σ, hσ⟩ :=
    exists_stalkTriv_eq_germ (idx L x₀.1) m x₀.1 x₀.2 (mem_idx L x₀.1)
  let S : Set V := {x | x.1 ∈ U}
  have hS : IsOpen S := U.isOpen.preimage continuous_subtype_val
  refine ContinuousOn.continuousAt ?_ (hS.mem_nhds hx₀U)
  have key : ∀ (x : V) (hx : x.1 ∈ U),
      ((trivializationAt ℂ (topologicalLineBundle L) x₀.1) ⟨x.1, valN L V m x⟩).2 =
        sectionValue _ σ ⟨x.1, hx⟩ := by
    intro x hx
    change evalExt _ (transitionSection (idx L x.1) (idx L x₀.1)) x.1 * valN L V m x = _
    rw [valN, ← stalkValue_stalkTriv_change (idx L x.1) (idx L x₀.1) x.1 (mem_idx L x.1)
      (hUs hx), hσ x.1 hx, stalkValue_germ]
  rw [continuousOn_iff_continuous_restrict]
  refine ((continuous_sectionValue _ σ).comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x : S => show x.1.1 ∈ U from x.2))).congr fun x => (key x.1 x.2).symm

private theorem exists_val_topologicalLineBundle
    (M : SheafOfModules.{0} (ringCatSheaf (X ↘ Spec (.of ℂ))))
    (t : (analytifyModule (X ↘ Spec (.of ℂ))).obj L ≅ M) :
      ∃ val : ∀ V : Opens (space (X ↘ Spec (.of ℂ))), M.val.obj (op V) → ∀ x : V,
          InvertibleModule.topologicalLineBundle L x.1,
        (∀ (V : Opens (space (X ↘ Spec (.of ℂ)))) (t : M.val.obj (op V)),
          Continuous fun x : V ↦ (⟨x.1, val V t x⟩ :
            Bundle.TotalSpace ℂ (InvertibleModule.topologicalLineBundle L))) ∧
        (∀ (V : Opens (space (X ↘ Spec (.of ℂ)))) (t t' : M.val.obj (op V)),
          val V (t + t') = val V t + val V t') ∧
        (∀ (V W : Opens (space (X ↘ Spec (.of ℂ)))) (h : W ≤ V) (t : M.val.obj (op V)) (x : W),
          val W (M.val.map (homOfLE h).op t) x = val V t ⟨x.1, h x.2⟩) ∧
        (∀ (V : Opens (space (X ↘ Spec (.of ℂ))))
          (s : (Analytification.structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op V))
          (t : M.val.obj (op V)) (x : V)
          (c : {c : Chart (X ↘ Spec (.of ℂ)) // x.1 ∈ ComplexPoints.chart c.U})
          (g : holGerms (c.1.coords ⟨x.1, c.2⟩)),
          s.1 x c = Chart.StalkRing.mk c.1 _ g →
          val V ((show (ringCatSheaf (X ↘ Spec (.of ℂ))).obj.obj (op V) from s) • t) x =
            Filter.Germ.value (g : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) • val V t x) ∧
        (∀ x : space (X ↘ Spec (.of ℂ)), ∃ (V : Opens (space (X ↘ Spec (.of ℂ))))
          (t : M.val.obj (op V)) (hx : x ∈ V), val V t ⟨x, hx⟩ ≠ 0) := by
  refine ⟨fun V m x => valN L V (t.inv.val.app (op V) m) x, fun V m => continuous_valN L V _,
    fun V m m' => ?_, fun V W h m x => ?_, fun V σ m x c g hg => ?_, fun x => ?_⟩
  · funext x
    dsimp only
    rw [map_add]
    exact valN_add L V _ _ x
  · dsimp only
    rw [PresheafOfModules.naturality_apply]
    exact valN_res L h _ x
  · exact (congrArg (fun z => valN L V z x) ((t.inv.val.app (op V)).hom.map_smul σ m)).trans
      (valN_smul L V σ _ x c g hg)
  · refine ⟨(Opens.map (toSchemeHom _)).obj (idx L x).W,
      t.hom.val.app (op _) (anSec L (idx L x).a), mem_idx L x, ?_⟩
    dsimp only
    rw [← PresheafOfModules.comp_app_apply, ← SheafOfModules.comp_val, Iso.hom_inv_id,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
    change valN L _ _ ⟨x, mem_idx L x⟩ ≠ (0 : ℂ)
    rw [valN_anSec]
    exact one_ne_zero

end Bundle

end AnalyticLineBundle

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Analytic.Analytification
  Opposite

/-- For a projective complex scheme `X`, the rationalizations of integral classes span
`H²(X^an; ℚ)`. -/
private theorem span_range_mapCoeff_eq_top_of_isProjective {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) :
    Submodule.span ℚ (Set.range (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 :
      singularCohomology ℤ (analyticSpace sX) 2 → singularCohomology ℚ (analyticSpace sX) 2)) =
      ⊤ :=
  eq_top_iff.2 fun x _ => (isBaseChange_mapCoeff_of_isProjectiveMorphism sX
      (isProjectiveMorphism_of_isProjective_of_isAffine sX hX) 2).inductionOn x
    (motive := fun x => x ∈ Submodule.span ℚ (Set.range (singularCohomology.mapCoeff
      (Int.castRingHom ℚ) 2 :
        singularCohomology ℤ (analyticSpace sX) 2 → singularCohomology ℚ (analyticSpace sX) 2)))
    (fun m => Submodule.subset_span ⟨m, rfl⟩)
    (fun _ _ h => Submodule.smul_mem _ _ h) (fun _ _ h h' => Submodule.add_mem _ h h')

/-- The scheme fibre of the resolution of a local setting over a closed point is a projective
complex scheme: it is the base change of the projective `π` along the `ℂ`-point
`Spec ℂ ≅ Spec κ(y) ⟶ Y`. -/
private theorem isProjective_pointSettingFibre
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hS : IsLocalSetting sY Θ T π) {y : Y} (hy : IsClosed {y}) :
    IsProjective (pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY) := by
  have hproj : IsProjectiveMorphism π := hS.isResolution.2.2.2.1
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isResolution.1
  let e : Spec (Y.residueField y) ≅ Spec (.of ℂ) :=
    Scheme.Spec.mapIso (residueFieldIsoBase sY y hy).op.symm
  have sq : IsPullback (pullback.snd π (Y.fromSpecResidueField y) ≫ e.hom)
      (pullback.fst π (Y.fromSpecResidueField y)) (e.inv ≫ Y.fromSpecResidueField y) π :=
    IsPullback.of_iso (IsPullback.of_hasPullback π (Y.fromSpecResidueField y)).flip
      (Iso.refl _) e (Iso.refl _) (Iso.refl _) (Category.id_comp _).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp) (by simp)
  have heq : pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY =
      pullback.snd π (Y.fromSpecResidueField y) ≫ e.hom := by
    have h2 : e.hom = Y.fromSpecResidueField y ≫ sY := by
      rw [← SpecMap_residueFieldIsoBase_inv sY y hy]
      rfl
    rw [h2, ← Category.assoc, pullback.condition, Category.assoc]
  rw [heq]
  exact IsProjective.of_isPullback sq hproj.isProjective

/-- A sheaf of modules on a ringed space which is locally isomorphic to the structure sheaf is
invertible. -/
private theorem isInvertible_of_forall_over (Y : RingedSpace.{0})
    (L : _root_.SheafOfModules.{0} (_root_.structureSheaf Y.sheaf))
    (h : ∀ y : Y, ∃ U : Opens Y, y ∈ U ∧ Nonempty (L.over U ≅ _root_.SheafOfModules.unit _)) :
    Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (_root_.structureSheaf Y.sheaf).property L := by
  choose U hU e using h
  haveI : Stacks.SheafOfModules.Invertible.IsLocallyTrivial L :=
    ⟨Y, U, (Opens.coversTop_iff _ U).2 (TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr
      fun y _ => Opens.mem_iSup.mpr ⟨y, hU y⟩)), e⟩
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank L 1 :=
    ⟨(Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial
      L).exists_isFiniteLocallyFreeOfRankData⟩
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one Y L

/-- An invertible sheaf of modules on a ringed space with local stalks is locally isomorphic to
the structure sheaf. -/
private theorem exists_over_iso_unit_of_isInvertible (Y : RingedSpace.{0})
    [∀ y : Y, IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y y)]
    (L : _root_.SheafOfModules.{0} (_root_.structureSheaf Y.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (_root_.structureSheaf Y.sheaf).property L)
    (y : Y) :
    ∃ U : Opens Y, y ∈ U ∧ Nonempty (L.over U ≅ _root_.SheafOfModules.unit _) := by
  haveI : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (_root_.structureSheaf Y.sheaf).property L := hL
  obtain ⟨I, Xs, hXs, hiso⟩ :=
    (Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible
      (X := Y) L).exists_trivializing_cover
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff (U := Xs)).1 hXs).exists_mem y
  exact ⟨Xs i, hi, hiso i⟩

/-- `H²(Y; ℤ) ≅ H²(Y, ∅; ℤ)`: absolute singular cohomology is relative cohomology of the pair
`(Y, ∅)`. -/
private noncomputable def singularCohomologyIsoRelEmpty (Y : TopCat.{0}) :
    singularCohomology ℤ Y 2 ≅
      MMP.relativeSingularCohomology ℤ (.of ℤ ℤ) Y ∅ 2 where
  hom := (MMP.relativeSingularCohomology.map ℤ (.of ℤ ℤ) (𝟙 Y)
    (Set.empty_subset _) 2)
  inv := (MMP.relativeSingularCohomology.map ℤ (.of ℤ ℤ) (𝟙 Y)
    (A' := (Set.univ : Set Y)ᶜ) (A := ∅) (by simp) 2)
  hom_inv_id := by
    rw [← MMP.relativeSingularCohomology.map_comp]
    exact MMP.relativeSingularCohomology.map_id _ _ _ _ _
  inv_hom_id := by
    rw [← MMP.relativeSingularCohomology.map_comp]
    exact MMP.relativeSingularCohomology.map_id _ _ _ _ _

/-- `exists_addEquiv_picardObstruction_eq_algebraicFirstChernClass` for a scheme over `ℂ` with its
structure morphism as an instance. -/
private theorem exists_addEquiv_picardObstruction_eq_algebraicFirstChernClass_aux {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] (hX : IsProjective (X ↘ Spec (.of ℂ)))
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [QuasiCompact (X ↘ Spec (.of ℂ))] :
    haveI := isLocalRing_stalk_analytification (sX := X ↘ Spec (.of ℂ))
    let J := Opens.grothendieckTopology (space (X ↘ Spec (.of ℂ)))
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf (X ↘ Spec (.of ℂ)))
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification (X ↘ Spec (.of ℂ)))
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
      (∀ (W : Opens (space (X ↘ Spec (.of ℂ)))) (n : ℤ),
        (show (Analytification.structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W) from
          ι.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
      (∀ (W : Opens (space (X ↘ Spec (.of ℂ))))
        (s : (Analytification.structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)) (x : W)
        (c : {c : Chart (X ↘ Spec (.of ℂ)) // x.1 ∈ ComplexPoints.chart c.U})
        (f : (Fin c.1.n → ℂ) → ℂ)
        (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (g : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
        (g' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ g →
        ((Additive.toMul (e.hom.app (op W) s) :
            ((Analytification.structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W))ˣ) :
          (Analytification.structureSheaf (X ↘ Spec (.of ℂ))).obj.obj (op W)).1 x c =
            Chart.StalkRing.mk c.1 _ g') →
      ∃ (ψ : Sheaf.H.{0} ZA 2 ≃+ singularCohomology ℤ (analyticSpace (X ↘ Spec (.of ℂ))) 2)
        (ε : ℤˣ), ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
          (M : SheafOfModules.{0} (ringCatSheaf (X ↘ Spec (.of ℂ))))
          (hM : Stacks.SheafOfModules.IsInvertible
            (Analytification.structureSheaf (X ↘ Spec (.of ℂ))).obj
              (ringCatSheaf (X ↘ Spec (.of ℂ))).2 M),
          Nonempty ((analytifyModule (X ↘ Spec (.of ℂ))).obj L ≅ M) →
          ψ (picardObstruction (analytification (X ↘ Spec (.of ℂ))) hS
              (Stacks.SheafOfModules.Picard.classOf _ _ M hM)) =
            ε • algebraicFirstChernClass L := by
  intro J O Ou ZA ι e w hS hι he
  have hX' : IsProjectiveMorphism (X ↘ Spec (.of ℂ)) :=
    isProjectiveMorphism_of_isProjective_of_isAffine _ hX
  obtain ⟨φ, -, ε, hφ⟩ := exists_addEquiv_picardObstruction_eq_firstChernClass
  refine ⟨(φ _ hX').trans
    (singularCohomologyIsoRelEmpty (analyticSpace _)).toLinearEquiv.toAddEquiv.symm, ε,
    fun L _ M hM ⟨t⟩ => ?_⟩
  obtain ⟨val, h1, h2, h3, h4, h5⟩ := exists_val_topologicalLineBundle L M t
  have key := hφ _ hX' ι e w hS hι he M hM (InvertibleModule.topologicalLineBundle L) val
    h1 h2 h3 h4 h5
  rw [AddEquiv.trans_apply, key, AddEquiv.symm_apply_eq, Units.smul_def, Units.smul_def,
    map_zsmul]
  rfl

/-- The analytic Picard obstruction of the exponential sequence on the analytification of a
projective complex scheme is, under an identification of `H²(X^an, ℤ_{X^an})` with singular
cohomology and up to one sign, the topological first Chern class of the underlying line bundle. -/
private theorem exists_addEquiv_picardObstruction_eq_algebraicFirstChernClass {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) [LocallyOfFiniteType sX] [QuasiCompact sX] :
    haveI := isLocalRing_stalk_analytification (sX := sX)
    let J := Opens.grothendieckTopology (space sX)
    let O : Sheaf J AddCommGrpCat.{0} :=
      (sheafCompose J (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)
    let Ou : Sheaf J AddCommGrpCat.{0} :=
      Stacks.Cohomology.Generators.unitsSheaf (analytification sX)
    let ZA : Sheaf J AddCommGrpCat.{0} :=
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    ∀ (ι : ZA ⟶ O) (e : O ⟶ Ou) (w : ι ≫ e = 0) (hS : (ShortComplex.mk ι e w).ShortExact),
      (∀ (W : Opens (space sX)) (n : ℤ),
        (show (Analytification.structureSheaf sX).obj.obj (op W) from ι.hom.app (op W)
          ((toSheafify J ((Functor.const _).obj (AddCommGrpCat.of ℤ))).app (op W) n)) = n) →
      (∀ (W : Opens (space sX)) (s : (Analytification.structureSheaf sX).obj.obj (op W)) (x : W)
        (c : {c : Chart sX // x.1 ∈ ComplexPoints.chart c.U}) (f : (Fin c.1.n → ℂ) → ℂ)
        (g g' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (g : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) = f →
        (g' : Filter.Germ (nhds (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * f z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ g →
        ((Additive.toMul (e.hom.app (op W) s) :
            ((Analytification.structureSheaf sX).obj.obj (op W))ˣ) :
          (Analytification.structureSheaf sX).obj.obj (op W)).1 x c =
            Chart.StalkRing.mk c.1 _ g') →
      letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
      ∃ (ψ : Sheaf.H.{0} ZA 2 ≃+ singularCohomology ℤ (analyticSpace (X ↘ Spec (.of ℂ))) 2)
        (ε : ℤˣ), ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
          (M : SheafOfModules.{0} (ringCatSheaf sX))
          (hM : Stacks.SheafOfModules.IsInvertible (Analytification.structureSheaf sX).obj
            (ringCatSheaf sX).2 M),
          Nonempty ((analytifyModule sX).obj L ≅ M) →
          ψ (picardObstruction (analytification sX) hS
              (Stacks.SheafOfModules.Picard.classOf _ _ M hM)) =
            ε • algebraicFirstChernClass L := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  haveI : QuasiCompact (X ↘ Spec (.of ℂ)) := ‹QuasiCompact sX›
  exact exists_addEquiv_picardObstruction_eq_algebraicFirstChernClass_aux hX

/-- On a projective complex scheme `X` with `H²(X^an, 𝒪_{X^an}) = 0`, every integral class in
`H²(X^an; ℤ)` is the first Chern class of an invertible `𝒪_X`-module. -/
private theorem exists_algebraicFirstChernClass_eq_of_subsingleton {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX)
    (hO : Subsingleton (Sheaf.H.{0} ((sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)) 2)) :
    letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
    ∀ c : singularCohomology ℤ (analyticSpace (X ↘ Spec (.of ℂ))) 2,
      ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        algebraicFirstChernClass L = c := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsProper sX := hX.isProper
  haveI := isLocalRing_stalk_analytification (sX := sX)
  intro c
  obtain ⟨ι, e, w, hS, hι, he, -, hsurj⟩ := exact_picardObstruction_analytification sX
  obtain ⟨ψ, ε, hψ⟩ :=
    exists_addEquiv_picardObstruction_eq_algebraicFirstChernClass sX hX ι e w hS hι he
  obtain ⟨P, hP⟩ := hsurj hO (ψ.symm (ε • c))
  obtain ⟨M, hM, rfl⟩ := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ P
  obtain ⟨L, hL, ⟨t⟩⟩ := exists_analytify_iso_of_isLocallyTrivial sX hX M fun y => by
    haveI : ∀ y : analytification sX,
        IsLocalRing
          (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk (analytification sX) y) :=
      fun y => isLocalRing_stalk_analytification (sX := sX) y
    exact exists_over_iso_unit_of_isInvertible (analytification sX) M hM y
  haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).1
      (isInvertible_of_forall_over X.toRingedSpace L hL)
  refine ⟨L, inferInstance, ?_⟩
  have h := hψ L M hM ⟨t⟩
  rw [hP, AddEquiv.apply_symm_apply] at h
  have := congrArg (fun a => ε⁻¹ • a) h
  simpa [smul_smul] using this.symm

noncomputable section

/-- Global sections preserve finite limits. -/
@[instance_reducible]
private def preservesFiniteLimits_globalSections (S : TopCat.{0}) :
    PreservesFiniteLimits (MMP.Analytic.globalSections S) :=
  inferInstanceAs (PreservesFiniteLimits
    ((sheafSections (Opens.grothendieckTopology S) AddCommGrpCat.{0}).obj (op ⊤)))

attribute [local instance] preservesFiniteLimits_globalSections

/-- The constant sheaf `ℤ_S`. -/
private def zS (S : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} S :=
  (constantSheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}).obj (.of (ULift ℤ))

/-- `Hom(ULift ℤ, A) ≃+ A`. -/
private def uliftIntHomEquiv (A : AddCommGrpCat.{0}) : (AddCommGrpCat.of (ULift ℤ) ⟶ A) ≃+ A where
  toFun φ := φ (ULift.up 1)
  invFun a := AddCommGrpCat.ofHom ((zmultiplesHom A a).comp AddEquiv.ulift.toAddMonoidHom)
  left_inv φ := by
    ext ⟨k⟩
    change k • φ (ULift.up 1) = φ (ULift.up k)
    rw [← map_zsmul]
    congr 1
    exact ULift.ext (by simp)
  right_inv a := by
    change (1 : ℤ) • a = a
    exact one_zsmul a
  map_add' φ ψ := rfl

/-- The unit section `1 ∈ Γ(S, ℤ_S)`. -/
private def oneSec (S : TopCat.{0}) : (MMP.Analytic.globalSections S).obj (zS S) :=
  (constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0} isTerminalTop).unit.app
    (AddCommGrpCat.of (ULift ℤ)) (ULift.up 1)

/-- Evaluation at the unit section: `Hom(ℤ_S, G) ≃+ Γ(S, G)`. -/
private def evalOne (S : TopCat.{0}) (G : TopCat.Sheaf AddCommGrpCat.{0} S) :
    (zS S ⟶ G) ≃+ (MMP.Analytic.globalSections S).obj G where
  toFun t := (MMP.Analytic.globalSections S).map t (oneSec S)
  invFun s := ((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
    isTerminalTop).homEquiv _ G).symm ((uliftIntHomEquiv _).symm s)
  left_inv t := by
    apply ((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
      isTerminalTop).homEquiv _ G).injective
    rw [Equiv.apply_symm_apply]
    apply (uliftIntHomEquiv _).injective
    rw [AddEquiv.apply_symm_apply]
    exact (ConcreteCategory.congr_hom (Adjunction.homEquiv_unit _ _ _ t) (ULift.up (1 : ℤ))).symm
  right_inv s := by
    change (MMP.Analytic.globalSections S).map _ (oneSec S) = s
    have h := Adjunction.homEquiv_unit (constantSheafAdj (Opens.grothendieckTopology S)
      AddCommGrpCat.{0} isTerminalTop) (X := AddCommGrpCat.of (ULift ℤ)) (Y := G)
      (((constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{0}
        isTerminalTop).homEquiv _ G).symm ((uliftIntHomEquiv _).symm s))
    rw [Equiv.apply_symm_apply] at h
    have h2 := congrArg (fun φ => (ConcreteCategory.hom φ) (ULift.up (1 : ℤ))) h
    exact h2.symm.trans ((uliftIntHomEquiv _).apply_symm_apply s)
  map_add' t t' := by
    change (MMP.Analytic.globalSections S).map (t + t') (oneSec S) = _
    rw [Functor.map_add]
    rfl

/-- `Γ(S, -)` is corepresented by `ℤ_S`. -/
private def corep (S : TopCat.{0}) :
    MMP.Analytic.globalSections S ≅ preadditiveCoyoneda.obj (op (zS S)) :=
  (NatIso.ofComponents (fun G => (evalOne S G).toAddCommGrpIso) (by
    intro G G' a
    ext t
    change (MMP.Analytic.globalSections S).map (t ≫ a) (oneSec S) =
      (MMP.Analytic.globalSections S).map a ((MMP.Analytic.globalSections S).map t (oneSec S))
    exact ConcreteCategory.congr_hom
      ((MMP.Analytic.globalSections S).map_comp (t : zS S ⟶ G) a) (oneSec S))).symm

/-- Cohomology `Sheaf.H` of an abelian sheaf on a topological space agrees with its Godement
cohomology. -/
private noncomputable def sheafHEquivSheafCohomology (S : TopCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat.{0} S) (n : ℕ) :
    Sheaf.H.{0} F n ≃ (MMP.Analytic.sheafCohomology S n).obj F :=
  ((ModuleSheafCohomology.extFunctorObjIsoRightDerived (MMP.Analytic.globalSections S) (zS S)
    (corep S) n).app F ≪≫
    (MMP.Analytic.sheafCohomologyIso S n).symm.app F).addCommGroupIsoToAddEquiv.toEquiv

open MMP.Analytic MMP.Analytic.ComplexPoints MMP.Analytic.Analytification in
/-- **GAGA in degree two for the structure sheaf.** If `X` is a projective complex scheme with
`H²(X, 𝒪_X) = 0`, then `H²(X^an, 𝒪_{X^an}) = 0`. -/
private theorem subsingleton_sheafH_two_of_isProjective {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX)
    (h : Subsingleton ((MMP.Analytic.sheafCohomology X.toPresheafedSpace.carrier (2 : ℕ)).obj
      ((SheafOfModules.toSheaf _).obj (SheafOfModules.unit X.ringCatSheaf)))) :
    Subsingleton (Sheaf.H.{0} ((sheafCompose (Opens.grothendieckTopology (space sX))
      (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX)) 2) := by
  haveI : IsProper sX := hX.isProper
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsIso (comparisonMap sX (SheafOfModules.unit X.ringCatSheaf) (2 : ℕ)) :=
    isIso_comparisonMap_of_isProjective sX hX _
      (AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X)) _
  have h1 : Subsingleton ((MMP.Analytic.sheafCohomology (space sX) (2 : ℕ)).obj
      ((SheafOfModules.toSheaf _).obj
        ((analytifyModule sX).obj (SheafOfModules.unit X.ringCatSheaf)))) :=
    (Iso.addCommGroupIsoToAddEquiv
      (asIso (comparisonMap sX (SheafOfModules.unit X.ringCatSheaf)
        (2 : ℕ))).symm).toEquiv.subsingleton
  have hfin : (Opens.map (toSchemeHom sX)).Final := by
    rw [Functor.final_iff_of_isFiltered]
    exact ⟨fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩, fun {_ c} _ _ => ⟨c, 𝟙 c, Subsingleton.elim _ _⟩⟩
  let u : (analytifyModule sX).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (ringCatSheaf sX) :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom sX))
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (ringCatSheafHom sX))
  have h2 : Subsingleton ((MMP.Analytic.sheafCohomology (space sX) (2 : ℕ)).obj
      ((sheafCompose (Opens.grothendieckTopology (space sX))
        (forget₂ RingCat AddCommGrpCat)).obj (ringCatSheaf sX))) :=
    (Iso.addCommGroupIsoToAddEquiv ((MMP.Analytic.sheafCohomology (space sX) (2 : ℕ)).mapIso
      ((SheafOfModules.toSheaf _).mapIso u)).symm).toEquiv.subsingleton
  exact (sheafHEquivSheafCohomology (space sX) _ 2).subsingleton

end

/-- `H²(F_y, 𝒪_{F_y}) = 0` for the scheme fibre of a local setting over a closed point, when the
fibre has dimension at most two, as a Godement cohomology group. -/
private theorem subsingleton_sheafCohomology_two_pointSettingFibre
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hS : IsLocalSetting sY Θ T π) {y : Y}
    (hdim : topologicalKrullDim (pointSettingFibre π y) ≤ 2) :
    Subsingleton ((MMP.Analytic.sheafCohomology
      (pointSettingFibre π y).toPresheafedSpace.carrier (2 : ℕ)).obj
        ((SheafOfModules.toSheaf _).obj
          (SheafOfModules.unit (pointSettingFibre π y).ringCatSheaf))) :=
  haveI := hS.subsingleton_H_two_pointSettingFibre hdim
  (sheafHEquivSheafCohomology _ _ 2).symm.subsingleton

end MMP.OAI4LocalSchemeFibreVanishingB

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

open MMP.OAI4LocalSchemeFibreVanishingB in
/-- In a local setting `(Y, Θ, T, π)`, for a closed point `y ∈ Y` whose scheme fibre
`F_y = Ỹ ×_Y Spec κ(y)` has dimension at most two, the rational first Chern classes of
invertible modules on `F_y` span `H²(F_y; ℚ)`. -/
@[mmp "lem_oai4_local_scheme_fibre_vanishing_b"]
public theorem IsLocalSetting.span_firstChernClass_pointSettingFibre_eq_top
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hS : IsLocalSetting sY Θ T π) {y : Y} (hy : IsClosed {y})
    (hdim : topologicalKrullDim (pointSettingFibre π y) ≤ 2) :
    letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) := ⟨pullback.fst π _ ≫ π ≫ sY⟩
    Submodule.span ℚ
      {c : rationalCohomology (analyticSpace (pointSettingFibre π y ↘ Spec (.of ℂ))) 2 |
        ∃ (M : (pointSettingFibre π y).Modules)
          (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
            (pointSettingFibre π y).ringCatSheaf.2 M),
          singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M) = c} =
      ⊤ := by
  letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) := ⟨pullback.fst π _ ≫ π ≫ sY⟩
  have hX := isProjective_pointSettingFibre hS hy
  have hc := exists_algebraicFirstChernClass_eq_of_subsingleton _ hX
    (subsingleton_sheafH_two_of_isProjective _ hX
      (subsingleton_sheafCohomology_two_pointSettingFibre hS hdim))
  refine eq_top_iff.2 ((span_range_mapCoeff_eq_top_of_isProjective _ hX).ge.trans
    (Submodule.span_mono ?_))
  rintro _ ⟨c, rfl⟩
  obtain ⟨M, hM, rfl⟩ := hc c
  exact ⟨M, hM, rfl⟩

end MMP.Fourfold
