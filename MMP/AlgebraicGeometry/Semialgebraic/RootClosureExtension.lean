module

public import MMP.AlgebraicGeometry.Semialgebraic.ShearRootBound
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.ExtendFrom

/-!
# Root functions extend continuously to the closures of convex cells

Let `C` be a subset of a topological space and `b ∈ closure C` a point at which `C` is locally
connected from inside: arbitrarily small neighbourhoods `t ∈ 𝓝[C] b` with `t ⊆ C` are
preconnected (for instance `C` convex in a normed space, `t = B(b, r) ∩ C`). If `f` is
continuous on `C`, bounded near `b` and its cluster values at `b` lie in a finite set, then `f`
has a limit at `b` along `C`: two cluster values `y < y'` are separated by a value `c ∉ Z`
which is not a cluster value, so `f` omits `c` on some small connected `t`, while `f(t)` meets
both sides of `c`.

Applied to a root function `ξ` of a family `G(a, ·)` (`G(a, ξ(a)) = 0` on `C`), whose cluster
values at `b` are zeros of `G(b, ·)` by continuity, this extends `ξ` continuously to
`closure C` with `G(b, ξ(b)) = 0`. For `G(a, t) = F(a, t)` a polynomial with constant leading
coefficient in `t` (after a good direction,
`MMP.exists_shearPolynomial_leadingCoeff`)
the roots are bounded by the continuous Cauchy bound (`MMP.abs_lt_polyRootBound`)
and `F(b, ·)` has finitely many zeros. This is the step of the triangulation of compact
semialgebraic sets where, over an open simplex of a triangulation of the base, the root
functions of the cylindrical decomposition are extended to the closed simplex.

## Main results

* `MMP.exists_tendsto_nhdsWithin_of_isPreconnected`: a limit exists when the
  cluster values are finitely many and `C` is locally connected at `b` from inside.
* `MMP.Convex.exists_isPreconnected_nhdsWithin`: convex sets are locally
  connected from inside at every point.
* `MMP.exists_continuousOn_closure_of_eval_eq_zero`: a continuous, locally
  bounded root function of a continuous family with finitely many zeros extends continuously to
  the closure.
* `MMP.Convex.exists_continuousOn_closure_of_specAt`: the same over a convex set,
  for a polynomial in `t` with constant nonzero leading coefficient, composed with a map `Φ`
  continuous on the closure (the triangulation of the base).

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], proof of
  Theorem 9.2.1.
-/

@[expose] public section

open Set Filter Topology Metric Polynomial

namespace MMP

/-- **Limits of functions with finitely many cluster values.** Let `f` be continuous on `C`,
bounded near `b ∈ closure C` along `C`, with all its cluster values at `b` in a finite set `Z`.
If arbitrarily small neighbourhoods of `b` in `C` are preconnected, then `f` has a limit in `Z`
at `b` along `C`. -/
theorem exists_tendsto_nhdsWithin_of_isPreconnected {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {C : Set X} {b : X} (hb : b ∈ closure C) (hf : ContinuousOn f C)
    (hconn : ∀ s ∈ 𝓝[C] b, ∃ t ∈ 𝓝[C] b, t ⊆ s ∧ t ⊆ C ∧ IsPreconnected t)
    {M : ℝ} (hM : ∀ᶠ a in 𝓝[C] b, |f a| ≤ M) {Z : Set ℝ} (hZ : Z.Finite)
    (hcl : ∀ y, MapClusterPt y (𝓝[C] b) f → y ∈ Z) :
    ∃ y ∈ Z, Tendsto f (𝓝[C] b) (𝓝 y) := by
  haveI : (𝓝[C] b).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hb
  have hK : IsCompact (Icc (-M) M) := isCompact_Icc
  have hfK : ∀ᶠ a in 𝓝[C] b, f a ∈ Icc (-M) M :=
    hM.mono fun a ha ↦ abs_le.1 ha
  obtain ⟨y, -, hy⟩ := hK.exists_mapClusterPt (tendsto_principal.2 hfK)
  -- two cluster values coincide
  have huniq : ∀ y₁ y₂, MapClusterPt y₁ (𝓝[C] b) f → MapClusterPt y₂ (𝓝[C] b) f → y₁ < y₂ →
      False := by
    intro y₁ y₂ h₁ h₂ h12
    obtain ⟨c, hc, hcZ⟩ : (Ioo y₁ y₂ \ Z).Nonempty :=
      ((Ioo_infinite h12).diff hZ).nonempty
    have hnc : ¬ MapClusterPt c (𝓝[C] b) f := fun h ↦ hcZ (hcl c h)
    rw [mapClusterPt_iff_frequently] at hnc
    push Not at hnc
    obtain ⟨s, hs, hev⟩ := hnc
    obtain ⟨t, ht, hts, htC, htc⟩ := hconn _ (hev.and self_mem_nhdsWithin)
    have himg : IsPreconnected (f '' t) := htc.image f (hf.mono htC)
    obtain ⟨a₁, ha₁, ha₁t⟩ :=
      (((mapClusterPt_iff_frequently.1 h₁) _ (Iio_mem_nhds hc.1)).and_eventually ht).exists
    obtain ⟨a₂, ha₂, ha₂t⟩ :=
      (((mapClusterPt_iff_frequently.1 h₂) _ (Ioi_mem_nhds hc.2)).and_eventually ht).exists
    obtain ⟨a, hat, hac⟩ :=
      himg.Icc_subset (mem_image_of_mem f ha₁t) (mem_image_of_mem f ha₂t)
        ⟨le_of_lt ha₁, le_of_lt ha₂⟩
    exact (hts hat).1 (hac ▸ mem_of_mem_nhds hs)
  refine ⟨y, hcl y hy, hK.tendsto_nhds_of_unique_mapClusterPt hfK fun y' _ hy' ↦ ?_⟩
  rcases lt_trichotomy y' y with h | h | h
  · exact (huniq _ _ hy' hy h).elim
  · exact h
  · exact (huniq _ _ hy hy' h).elim

/-- A convex set in a normed space is locally connected from inside at every point: the sets
`B(b, r) ∩ C` are convex. -/
theorem Convex.exists_isPreconnected_nhdsWithin {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {C : Set E} (hC : Convex ℝ C) (b : E) :
    ∀ s ∈ 𝓝[C] b, ∃ t ∈ 𝓝[C] b, t ⊆ s ∧ t ⊆ C ∧ IsPreconnected t := by
  intro s hs
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhdsWithin_iff.1 hs
  refine ⟨ball b r ∩ C, ?_, hrs, inter_subset_right,
    ((convex_ball b r).inter hC).isPreconnected⟩
  rw [inter_comm]
  exact inter_mem_nhdsWithin C (ball_mem_nhds b hr)

/-- Cluster values of a root function are roots: if `G(a, ξ(a)) = 0` for `a ∈ C` and `G` is
continuous at `(b, y)` within `C × ℝ`, with `y` a cluster value of `ξ` at `b` along `C`, then
`G(b, y) = 0`. -/
theorem eq_zero_of_mapClusterPt {X : Type*} [TopologicalSpace X] {G : X → ℝ → ℝ}
    {ξ : X → ℝ} {C : Set X} {b : X} {y : ℝ}
    (hG : ContinuousWithinAt (Function.uncurry G) (C ×ˢ univ) (b, y))
    (hξ : ∀ a ∈ C, G a (ξ a) = 0) (hy : MapClusterPt y (𝓝[C] b) ξ) : G b y = 0 := by
  by_contra hne
  have hW : {w : X × ℝ | G w.1 w.2 ≠ 0} ∈ 𝓝[C] b ×ˢ 𝓝 y := by
    rw [← nhdsWithin_univ (a := y), ← nhdsWithin_prod_eq]
    exact hG.eventually_ne hne
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 hW
  obtain ⟨a, ⟨haV, haU⟩, haC⟩ :=
    (((mapClusterPt_iff_frequently.1 hy) V hV).and_eventually hU).and_eventually
      self_mem_nhdsWithin |>.exists
  exact hUV (mk_mem_prod haU haV) (hξ a haC)

/-- **Root functions extend to the closure.** Let `G : X → ℝ → ℝ` be jointly continuous on
`closure C × ℝ`, with finitely many zeros `G(b, ·)` for `b ∈ closure C`, and `ξ` a root
function (`G(a, ξ(a)) = 0`) continuous on `C` and bounded near each point of `closure C`.
If `C` is locally connected from inside at each point of its closure, `ξ` extends to a
continuous root function on `closure C`. -/
theorem exists_continuousOn_closure_of_eval_eq_zero {X : Type*} [TopologicalSpace X]
    {G : X → ℝ → ℝ} {ξ : X → ℝ} {C : Set X}
    (hG : ContinuousOn (Function.uncurry G) (closure C ×ˢ univ))
    (hfin : ∀ b ∈ closure C, {y | G b y = 0}.Finite) (hξ : ContinuousOn ξ C)
    (hξG : ∀ a ∈ C, G a (ξ a) = 0)
    (hbdd : ∀ b ∈ closure C, ∃ M, ∀ᶠ a in 𝓝[C] b, |ξ a| ≤ M)
    (hconn : ∀ b ∈ closure C, ∀ s ∈ 𝓝[C] b, ∃ t ∈ 𝓝[C] b, t ⊆ s ∧ t ⊆ C ∧ IsPreconnected t) :
    ∃ g : X → ℝ, ContinuousOn g (closure C) ∧ EqOn g ξ C ∧ ∀ b ∈ closure C, G b (g b) = 0 := by
  have hlim : ∀ b ∈ closure C, ∃ y, G b y = 0 ∧ Tendsto ξ (𝓝[C] b) (𝓝 y) := by
    intro b hb
    obtain ⟨M, hM⟩ := hbdd b hb
    obtain ⟨y, hy, hT⟩ := exists_tendsto_nhdsWithin_of_isPreconnected hb hξ (hconn b hb) hM
      (hfin b hb) fun y hy ↦ eq_zero_of_mapClusterPt
        ((hG (b, y) ⟨hb, mem_univ y⟩).mono (prod_mono subset_closure subset_rfl)) hξG hy
    exact ⟨y, hy, hT⟩
  refine ⟨extendFrom C ξ, continuousOn_extendFrom subset_rfl fun b hb ↦
    (hlim b hb).imp fun _ h ↦ h.2, fun a ha ↦ extendFrom_extends hξ a ha, fun b hb ↦ ?_⟩
  obtain ⟨y, hy, hT⟩ := hlim b hb
  haveI : (𝓝[C] b).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hb
  rwa [tendsto_nhds_unique (tendsto_extendFrom ⟨y, hT⟩) hT]

/-- `(a, t) ↦ F(a, t)` is jointly continuous for `F ∈ ℝ[X_σ][T]`. -/
theorem continuous_uncurry_eval_specAt {σ : Type*} (F : (MvPolynomial σ ℝ)[X]) :
    Continuous fun w : (σ → ℝ) × ℝ ↦ (TarskiSeidenberg.specAt w.1 F).eval w.2 := by
  have h : Continuous fun w : (σ → ℝ) × ℝ ↦
      MvPolynomial.eval (optionCons w.1 w.2) ((MvPolynomial.optionEquivLeft ℝ σ).symm F) :=
    (MvPolynomial.continuous_eval _).comp continuous_optionCons
  refine h.congr fun w ↦ ?_
  rw [TarskiSeidenberg.eval_eq_eval_specAt_optionEquivLeft]
  simp only [AlgEquiv.apply_symm_apply]
  rfl

/-- A polynomial in `T` with constant nonzero leading coefficient has finitely many zeros at
every specialisation of the other variables. -/
theorem finite_setOf_eval_specAt_eq_zero {σ : Type*} {F : (MvPolynomial σ ℝ)[X]} {c : ℝ}
    (hc : c ≠ 0) (hF : F.leadingCoeff = MvPolynomial.C c) (a : σ → ℝ) :
    {y | (TarskiSeidenberg.specAt a F).eval y = 0}.Finite := by
  have hne : TarskiSeidenberg.specAt a F ≠ 0 := by
    intro h
    have := (natDegree_specAt_of_leadingCoeff hc hF a).2
    rw [h, leadingCoeff_zero] at this
    exact hc this.symm
  exact (TarskiSeidenberg.specAt a F).roots.toFinset.finite_toSet.subset fun y hy ↦
    Multiset.mem_toFinset.2 ((mem_roots hne).2 hy)

/-- **Root functions over a convex cell extend to its closure.** Let `F ∈ ℝ[X_σ][T]` have
constant nonzero leading coefficient `c` in `T`, `C` a convex set in a normed space, `Φ` a map
to `ℝ^σ` continuous on `closure C`, and `ξ` continuous on `C` with `F(Φ(a), ξ(a)) = 0` for
`a ∈ C`. Then `ξ` extends to a continuous function on `closure C` with `F(Φ(b), ξ(b)) = 0`. -/
theorem Convex.exists_continuousOn_closure_of_specAt {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {σ : Type*} [Fintype σ] {F : (MvPolynomial σ ℝ)[X]} {c : ℝ} (hc : c ≠ 0)
    (hF : F.leadingCoeff = MvPolynomial.C c) {C : Set E} (hC : Convex ℝ C) {Φ : E → σ → ℝ}
    (hΦ : ContinuousOn Φ (closure C)) {ξ : E → ℝ} (hξ : ContinuousOn ξ C)
    (hξF : ∀ a ∈ C, (TarskiSeidenberg.specAt (Φ a) F).eval (ξ a) = 0) :
    ∃ g : E → ℝ, ContinuousOn g (closure C) ∧ EqOn g ξ C ∧
      ∀ b ∈ closure C, (TarskiSeidenberg.specAt (Φ b) F).eval (g b) = 0 := by
  have hG : ContinuousOn (fun w : E × ℝ ↦ (TarskiSeidenberg.specAt (Φ w.1) F).eval w.2)
      (closure C ×ˢ univ) :=
    (continuous_uncurry_eval_specAt F).comp_continuousOn
      ((hΦ.comp continuousOn_fst fun _ hw ↦ hw.1).prodMk continuousOn_snd)
  refine exists_continuousOn_closure_of_eval_eq_zero
    (G := fun a t ↦ (TarskiSeidenberg.specAt (Φ a) F).eval t) hG
    (fun b _ ↦ finite_setOf_eval_specAt_eq_zero hc hF (Φ b)) hξ hξF (fun b hb ↦ ?_)
    (fun b _ ↦ Convex.exists_isPreconnected_nhdsWithin hC b)
  -- the Cauchy bound is continuous on `closure C`, hence bounded near `b`
  have hB : ContinuousWithinAt (fun a ↦ polyRootBound F c (Φ a)) (closure C) b :=
    (continuous_polyRootBound F c).comp_continuousOn hΦ b hb
  refine ⟨polyRootBound F c (Φ b) + 1, ?_⟩
  have h1 : ∀ᶠ a in 𝓝[closure C] b, polyRootBound F c (Φ a) < polyRootBound F c (Φ b) + 1 :=
    hB.eventually (gt_mem_nhds (lt_add_one _))
  filter_upwards [nhdsWithin_mono b subset_closure h1, self_mem_nhdsWithin] with a ha haC
  exact ((abs_lt_polyRootBound hc hF (hξF a haC)).trans ha).le

end MMP
