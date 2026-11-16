module

public import MMP.AlgebraicGeometry.Analytic.Analytification
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import MMP.AlgebraicGeometry.AnalytificationChartTransition
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.Analytic.SurfaceHodge.RestrictionFamilies
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Algebraic families inside countably many translates of a linear image

Let `X` be a scheme locally of finite type over `ℂ`, `Φ : ℂⁿ → X(ℂ)` a map holomorphic in the
affine charts of `X(ℂ)` (for instance the uniformisation `ℂⁿ → ℂⁿ/Λ ≅ J(ℂ)` of the Jacobian of a
curve), and `V ⊆ ℂⁿ` a complex subspace. If a morphism `g : T ⟶ X` over `ℂ` from a scheme of
finite type over `ℂ` sends every `ℂ`-point of `T` into countably many translates `Φ(aₖ + V)`,
then the Zariski closure of the image of `g` has dimension at most `dim V`.

The proof compares two dimensions of a set of complex values.
* If the closure of the image had dimension `d`, some point `g ξ` has a closure of dimension
  `≥ d`, and `d` polynomials `q` in the coordinates of a chart at `g ξ` have algebraically
  independent values in the residue field. By Chevalley's theorem the values `q(g(u))` at the
  `ℂ`-points `u` of `T` then contain a nonempty open subset of `ℂᵈ` (the image of `Spec` of the
  coordinate ring contains a basic open of `𝔸ᵈ`, and a maximal ideal over each of its points is
  a closed point, hence a `ℂ`-point of `T`).
* On the other hand these values lie in the images of countably many holomorphic maps on `V`,
  `v ↦ q(Φ(aₖ + v))`, so their Hausdorff dimension is at most `dim_ℝ V = 2 dim V`, while a set
  with nonempty interior in `ℂᵈ` has Hausdorff dimension `2d`.

Applied to the Jacobian `J` of a curve `C` on a smooth projective surface `X`, with `V` the image
of `H¹(X^an, 𝒪)`, this bounds the image closures of the algebraic families of restrictions to
`C` of line bundles on `X`, without the Kodaira–Spencer map: the classes of these restrictions
lie in the translates of `Φ(V)` by representatives of the countably many first Chern classes.

## Main definitions

* `MMP.Analytic.SurfaceHodge.chartPolyMap`: the polynomial map `y ↦ (q₁(y), …, q_d(y))` on the
  `ℂ`-points of a chart.

## Main results

* `MMP.Analytic.SurfaceHodge.dimH_chartPolyMap_image_le`,
  `MMP.Analytic.SurfaceHodge.le_finrank_of_nonempty_interior`: the analytic bound.
* `MMP.Analytic.SurfaceHodge.exists_ne_zero_forall_exists_isMaximal`: generic lifting of points
  along `ℂ[Y₁, …, Y_d] → B` (Chevalley).
* `MMP.Analytic.SurfaceHodge.exists_forall_mem_basicOpen`: algebraically independent chart
  coordinates at a point whose closure has dimension `≥ d`.
* `MMP.Analytic.SurfaceHodge.exists_le_topologicalKrullDim_closure_singleton`: the dimension of the
  closure of an image is attained at the closure of one image point.
* `MMP.Analytic.SurfaceHodge.nonempty_interior_chartPolyMap_image`: the values of the chart
  polynomials on the `ℂ`-points of `T` have nonempty interior.
* `MMP.Analytic.SurfaceHodge.topologicalKrullDim_closure_range_le_finrank`: the dimension bound.
* `MMP.Analytic.SurfaceHodge.exists_countable_isClosed_cover_of_subset_iUnion`: the countable
  closed cover of `Φ(V)` in the Jacobian of a curve on a surface, from the translates.

## Implementation notes

Dimension is `topologicalKrullDim` of a subset of the scheme, compared with transcendence degrees
of residue fields by `AlgebraicGeometry.topologicalKrullDim_closure_singleton_eq_trdeg`. The
analytic side uses only the Hausdorff dimension of images of differentiable maps
(`DifferentiableOn.dimH_image_le`); no smooth locus, generic smoothness or deformation theory is
used.

## References

* [D. Mumford, *Lectures on curves on an algebraic surface*], Lecture 19.
* [Stacks Project, Tag 054J](https://stacks.math.columbia.edu/tag/054J) (Chevalley)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open Set Filter Topology CategoryTheory AlgebraicGeometry
open MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Analytic.SurfaceHodge

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}

/-- The polynomial map `y ↦ (q₁(y), …, q_d(y))` in the coordinates of a chart. -/
noncomputable def chartPolyMap (c : Chart sX) {d : ℕ} (q : Fin d → MvPolynomial (Fin c.n) ℂ)
    (y : chart (sX := sX) c.U) : Fin d → ℂ :=
  fun i => MvPolynomial.eval (c.coords y) (q i)

/-- If `Φ : ℂⁿ → X(ℂ)` is holomorphic in the affine charts of `X(ℂ)` and every point of a set `S`
of `ℂ`-points of the chart `c` lies in a countable union of translates `Φ(aₖ + V)`, then the
image of `S` under the polynomial map `chartPolyMap c q` has Hausdorff dimension at most
`2 dim V`. -/
theorem dimH_chartPolyMap_image_le {Φ : (Fin n → ℂ) → ComplexPoints sX}
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart sX) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (c : Chart sX) {d : ℕ} (q : Fin d → MvPolynomial (Fin c.n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) {κ : Type*} [Countable κ] (a : κ → Fin n → ℂ)
    (S : Set (chart (sX := sX) c.U))
    (hS : ∀ y ∈ S, y.1 ∈ ⋃ k, (fun v => Φ (a k + v)) '' (V : Set (Fin n → ℂ))) :
    dimH (chartPolyMap c q '' S) ≤ (2 * Module.finrank ℂ V : ℕ) := by
  classical
  let F : κ → V → (Fin d → ℂ) := fun k v =>
    if h : Φ (a k + v) ∈ chart c.U then chartPolyMap c q ⟨_, h⟩ else 0
  let O : κ → Set V := fun k => {v | Φ (a k + v) ∈ chart c.U}
  have hsub : chartPolyMap c q '' S ⊆ ⋃ k, F k '' O k := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, v, hv, hyv⟩ := mem_iUnion.1 (hS y hy)
    have h : Φ (a k + v) ∈ chart c.U := (show Φ (a k + v) = y.1 from hyv) ▸ y.2
    refine mem_iUnion.2 ⟨k, ⟨v, hv⟩, h, ?_⟩
    simp only [F, h, ↓reduceDIte]
    exact congrArg _ (Subtype.ext hyv)
  have hdiff : ∀ k, DifferentiableOn ℂ (F k) (O k) := by
    intro k v hv
    obtain ⟨F', hF', hev⟩ := hhol (a k + v) c hv
    let G : (Fin n → ℂ) → (Fin d → ℂ) := fun w i => MvPolynomial.eval (F' w) (q i)
    have hcomp : DifferentiableAt ℂ (fun w : V => G (a k + w)) v :=
      DifferentiableAt.comp (g := G) (f := fun w : V => a k + (w : Fin n → ℂ)) v
        (differentiableAt_pi.2 fun i => (differentiable_eval_mvPolynomial (q i) _).comp _ hF')
        ((differentiableAt_const _).add V.subtypeL.differentiableAt)
    refine (hcomp.congr_of_eventuallyEq ?_).differentiableWithinAt
    have ht : Tendsto (fun w : V => a k + (w : Fin n → ℂ)) (𝓝 v) (𝓝 (a k + v)) :=
      ((continuous_const.add continuous_subtype_val).tendsto v)
    filter_upwards [ht.eventually hev] with w ⟨h', e⟩
    simp only [F, h', ↓reduceDIte, G]
    unfold chartPolyMap
    rw [e]
  calc dimH (chartPolyMap c q '' S) ≤ dimH (⋃ k, F k '' O k) := dimH_mono hsub
    _ = ⨆ k, dimH (F k '' O k) := dimH_iUnion _
    _ ≤ (2 * Module.finrank ℂ V : ℕ) := iSup_le fun k =>
        ((hdiff k).dimH_image_le.trans (dimH_mono (subset_univ _))).trans_eq
          (by rw [Real.dimH_univ_eq_finrank V, finrank_real_of_complex])

/-- **A countable union of translates of `Φ(V)` contains no algebraically large set.** If the
image of a set `S` of `ℂ`-points of a chart under `d` polynomial functions in the coordinates has
nonempty interior in `ℂᵈ`, and `S` lies in countably many translates `Φ(aₖ + V)`, then
`d ≤ dim V`. -/
theorem le_finrank_of_nonempty_interior {Φ : (Fin n → ℂ) → ComplexPoints sX}
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart sX) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (c : Chart sX) {d : ℕ} (q : Fin d → MvPolynomial (Fin c.n) ℂ)
    (V : Submodule ℂ (Fin n → ℂ)) {κ : Type*} [Countable κ] (a : κ → Fin n → ℂ)
    (S : Set (chart (sX := sX) c.U))
    (hS : ∀ y ∈ S, y.1 ∈ ⋃ k, (fun v => Φ (a k + v)) '' (V : Set (Fin n → ℂ)))
    (hint : (interior (chartPolyMap c q '' S)).Nonempty) :
    d ≤ Module.finrank ℂ V := by
  have h1 := dimH_chartPolyMap_image_le hhol c q V a S hS
  rw [Real.dimH_of_nonempty_interior hint, finrank_real_of_complex,
    Module.finrank_fin_fun] at h1
  have h2 : 2 * d ≤ 2 * Module.finrank ℂ V := by exact_mod_cast h1
  omega

section Algebra

/-- **Constructible sets near a generic point.** A constructible set `s` either contains or misses
the trace on an irreducible closed set `P` of some open neighbourhood of the generic point `η` of
`P`, according as `η ∈ s` or not. -/
private theorem exists_isOpen_of_isConstructible {T : Type*} [TopologicalSpace T] {s : Set T}
    (hs : Topology.IsConstructible s) {P : Set T} {η : T} (hη : IsGenericPoint η P) :
    ∃ N : Set T, IsOpen N ∧ η ∈ N ∧ (η ∈ s → P ∩ N ⊆ s) ∧ (η ∉ s → P ∩ N ⊆ sᶜ) := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : η ∈ U
    · exact ⟨U, hU, h, fun _ x hx => hx.2, fun h' => absurd h h'⟩
    · refine ⟨Set.univ, isOpen_univ, trivial, fun h' => absurd h' h, fun _ x hx hxU => h ?_⟩
      exact (hη.mem_open_set_iff hU).mpr ⟨x, hx.1, hxU⟩
  | union s _ t _ ihs iht =>
    obtain ⟨N₁, hN₁, hη₁, hs₁, hs₁'⟩ := ihs
    obtain ⟨N₂, hN₂, hη₂, ht₂, ht₂'⟩ := iht
    refine ⟨N₁ ∩ N₂, hN₁.inter hN₂, ⟨hη₁, hη₂⟩, fun h x hx => ?_, fun h x hx => ?_⟩
    · rcases h with h | h
      · exact Or.inl (hs₁ h ⟨hx.1, hx.2.1⟩)
      · exact Or.inr (ht₂ h ⟨hx.1, hx.2.2⟩)
    · rintro (h' | h')
      · exact hs₁' (fun h'' => h (Or.inl h'')) ⟨hx.1, hx.2.1⟩ h'
      · exact ht₂' (fun h'' => h (Or.inr h'')) ⟨hx.1, hx.2.2⟩ h'
  | compl s _ ih =>
    obtain ⟨N, hN, hηN, h₁, h₂⟩ := ih
    refine ⟨N, hN, hηN, h₂, fun h => ?_⟩
    rw [compl_compl]
    exact h₁ (not_not.mp h)

/-- **Generic lifting of `ℂ`-points.** Let `ρ : ℂ[Y₁, …, Y_d] → B` be of finite presentation and
`P₀` a prime of `B` meeting the image of no nonzero polynomial (so `ρ` is injective modulo
`P₀`). Then there is a nonzero polynomial `h` such that every `z ∈ ℂᵈ` with `h(z) ≠ 0` lifts:
some maximal ideal of `B` contains all `ρ(Yᵢ - zᵢ)`. By Chevalley's theorem the image of
`Spec B` is constructible; it contains the generic point, hence a basic open `D(h)`. -/
theorem exists_ne_zero_forall_exists_isMaximal {B : Type*} [CommRing B] {d : ℕ}
    {ρ : MvPolynomial (Fin d) ℂ →+* B} (hρ : ρ.FinitePresentation) (P₀ : PrimeSpectrum B)
    (hP₀ : ∀ f, f ≠ 0 → ρ f ∉ P₀.asIdeal) :
    ∃ h : MvPolynomial (Fin d) ℂ, h ≠ 0 ∧ ∀ z : Fin d → ℂ, MvPolynomial.eval z h ≠ 0 →
      ∃ M : Ideal B, M.IsMaximal ∧
        ∀ i, ρ (MvPolynomial.X i - MvPolynomial.C (z i)) ∈ M := by
  classical
  set η := PrimeSpectrum.comap ρ P₀
  have hη : η.asIdeal = ⊥ := eq_bot_iff.2 fun f hf => by_contra fun h0 => hP₀ f h0 hf
  have hgen : IsGenericPoint η (univ : Set (PrimeSpectrum (MvPolynomial (Fin d) ℂ))) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [mem_univ, iff_true]
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal, hη]
    exact bot_le
  obtain ⟨N, hN, hηN, hNs, -⟩ :=
    exists_isOpen_of_isConstructible (PrimeSpectrum.isConstructible_range_comap hρ) hgen
  obtain ⟨_, ⟨h, rfl⟩, hηh, hhN⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηN hN
  refine ⟨h, fun h0 => ?_, fun z hz => ?_⟩
  · simp [h0] at hηh
  · let m : PrimeSpectrum (MvPolynomial (Fin d) ℂ) :=
      ⟨RingHom.ker (MvPolynomial.eval z), RingHom.ker_isPrime _⟩
    have hm : m ∈ (PrimeSpectrum.basicOpen h : Set _) := by
      change h ∉ RingHom.ker (MvPolynomial.eval z)
      rwa [RingHom.mem_ker]
    obtain ⟨P, hP⟩ := hNs ⟨P₀, rfl⟩ ⟨mem_univ _, hhN hm⟩
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    refine ⟨M, hM, fun i => hPM ?_⟩
    change MvPolynomial.X i - MvPolynomial.C (z i) ∈ (PrimeSpectrum.comap ρ P).asIdeal
    rw [hP]
    change _ ∈ RingHom.ker (MvPolynomial.eval z)
    simp [RingHom.mem_ker]

end Algebra

section Transcendence

/-- If a field `κ` is algebraic over the subalgebra generated by a family `t` and has
transcendence degree at least `n`, then `n` members of the family are algebraically
independent. -/
private theorem exists_algebraicIndependent_comp {k κ ι : Type} [Field k] [Field κ]
    [Algebra k κ] (t : ι → κ) [Algebra.IsAlgebraic (Algebra.adjoin k (Set.range t)) κ] {n : ℕ}
    (h : (n : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg k κ)) :
    ∃ v : Fin n → ι, AlgebraicIndependent k (t ∘ v) := by
  classical
  obtain ⟨T, hT, hb⟩ := exists_isTranscendenceBasis_subset (R := k) (Set.range t)
  have hcard : Cardinal.mk (Fin n) ≤ Cardinal.mk T := by
    rw [hb.cardinalMk_eq_trdeg, Cardinal.mk_fin]
    exact Cardinal.natCast_le_toENat.1 h
  obtain ⟨e⟩ := Cardinal.le_def _ _ |>.1 hcard
  choose g hg using fun x : T => hT x.2
  refine ⟨g ∘ e, ?_⟩
  rw [show t ∘ (g ∘ e) = Subtype.val ∘ e from funext fun l => hg (e l)]
  exact hb.1.comp e e.injective

/-- A field is algebraic over a subalgebra of which it is the field of fractions. -/
private theorem isAlgebraic_of_forall_eq_div {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    (R : Subalgebra k κ) (h : ∀ z : κ, ∃ a ∈ R, ∃ b ∈ R, z = a / b) :
    Algebra.IsAlgebraic R κ := by
  refine ⟨fun z => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := h z
  rw [div_eq_mul_inv]
  exact (isAlgebraic_algebraMap (⟨a, ha⟩ : R)).mul (isAlgebraic_algebraMap (⟨b, hb⟩ : R)).inv

/-- Every element of the residue field at a point of an affine open `W` is a quotient of two
evaluations of sections over `W`. -/
private theorem exists_eq_evaluation_div {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W)
    (x : Z) (hx : x ∈ W) (z : Z.residueField x) :
    ∃ a s : Γ(Z, W), Z.evaluation W x hx s ≠ 0 ∧
      z = Z.evaluation W x hx a / Z.evaluation W x hx s := by
  obtain ⟨g, rfl⟩ := Z.residue_surjective x z
  let := TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨x, hx⟩ : W)
  have hloc := hW.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨⟨a, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl g
  have hu : IsUnit (algebraMap Γ(Z, W) (Z.presheaf.stalk x) s) :=
    IsLocalization.map_units _ s
  have hs : Z.evaluation W x hx s ≠ 0 := by
    rw [← Scheme.germ_residue]
    exact (hu.map (Z.residue x).hom).ne_zero
  refine ⟨a, s, hs, ?_⟩
  rw [eq_div_iff hs, ← Scheme.germ_residue]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  exact IsLocalization.mk'_spec _ a s

/-- Evaluation at a point of the presentation of a chart is the `ℂ`-algebra evaluation at the
values of the generators, for the `ℂ`-algebra structure of the residue field coming from `sX`. -/
private lemma evaluation_comp_pres (c : Chart sX) (x : X) (hx : x ∈ c.U) :
    letI : Algebra ℂ (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    (X.evaluation c.U x hx).hom.comp c.pres =
      (MvPolynomial.aeval (fun j => X.evaluation c.U x hx (c.gen j))).toRingHom := by
  let _ : Algebra ℂ (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, Chart.pres, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.aeval_C, RingHom.algebraMap_toAlgebra, baseRingHom]
    rw [← CommRingCat.comp_apply (X.presheaf.map _), ← Scheme.germ_residue,
      ← Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  · intro j
    simp [Chart.pres]

/-- **Algebraically independent coordinates at a point of large dimension.** If the closure of a
point `x` of an affine chart `c` has dimension at least `d`, there are `d` polynomials `qᵢ` in the
chart coordinates whose values in the residue field `κ(x)` are algebraically independent: no
nonzero polynomial in the `qᵢ` vanishes at `x`. -/
theorem exists_forall_mem_basicOpen [LocallyOfFiniteType sX] (c : Chart sX) {x : X}
    (hx : x ∈ c.U) {d : ℕ} (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x} : Set X))) :
    ∃ q : Fin d → MvPolynomial (Fin c.n) ℂ, ∀ f : MvPolynomial (Fin d) ℂ, f ≠ 0 →
      x ∈ X.basicOpen (c.pres (MvPolynomial.bind₁ q f)) := by
  classical
  let _ : Algebra ℂ (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  rw [topologicalKrullDim_closure_singleton_eq_trdeg ℂ X sX x] at hd
  have hd' : (d : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg ℂ (X.residueField x)) := by
    exact_mod_cast hd
  let t : Γ(X, c.U) → X.residueField x := fun a => X.evaluation c.U x hx a
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range t)) (X.residueField x) :=
    isAlgebraic_of_forall_eq_div _ fun z => by
      obtain ⟨a, b, -, rfl⟩ := exists_eq_evaluation_div c.isAffineOpen x hx z
      exact ⟨_, Algebra.subset_adjoin ⟨a, rfl⟩, _, Algebra.subset_adjoin ⟨b, rfl⟩, rfl⟩
  obtain ⟨v, hv⟩ := exists_algebraicIndependent_comp t hd'
  choose q hq using fun i => c.surjective (v i)
  refine ⟨q, fun f hf => ?_⟩
  refine (X.evaluation_ne_zero_iff_mem_basicOpen x hx _).1 ?_
  have e1 : ∀ r, X.evaluation c.U x hx (c.pres r) =
      MvPolynomial.aeval (fun j => X.evaluation c.U x hx (c.gen j)) r := fun r =>
    congrArg (fun φ : MvPolynomial (Fin c.n) ℂ →+* X.residueField x => φ r)
      (evaluation_comp_pres c x hx)
  rw [e1, MvPolynomial.aeval_bind₁]
  have e2 : (fun i => MvPolynomial.aeval (fun j => X.evaluation c.U x hx (c.gen j)) (q i)) =
      t ∘ v := funext fun i => by
    rw [← e1]
    exact congrArg t (hq i)
  rw [e2]
  exact fun h0 => hf ((algebraicIndependent_iff.1 hv) f h0)

end Transcendence

section Topology

/-- **A point of the image of large dimension.** If `f : T → X` is continuous on a Noetherian
quasi-sober space and the closure of its image has dimension at least `d`, then the closure of
some single image point `f ξ` has dimension at least `d`: the closure of the image is the finite
union of the closures of the images of the generic points of the irreducible components. -/
theorem exists_le_topologicalKrullDim_closure_singleton {T Y : Type*} [TopologicalSpace T]
    [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace T] [QuasiSober T] {f : T → Y}
    (hf : Continuous f) {d : ℕ}
    (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim (closure (range f))) :
    ∃ ξ : T, (d : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({f ξ} : Set Y)) := by
  classical
  by_contra! hcon
  let C := irreducibleComponents T
  have : Fintype C := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.fintype
  have hgen : ∀ K : C, ∃ ξ : T, closure ({ξ} : Set T) = K := fun K =>
    ⟨K.2.1.genericPoint, (K.2.1.isGenericPoint_genericPoint_closure).trans
      (isClosed_of_mem_irreducibleComponents _ K.2).closure_eq⟩
  choose ξ hξ using hgen
  let m : WithBot ℕ∞ := Finset.univ.sup fun K : C => topologicalKrullDim (closure {f (ξ K)})
  have hm : m < d := (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun K _ => hcon (ξ K)
  set S := closure (range f)
  let F : Finset (Set Y) := Finset.univ.image fun K : C => closure ({f (ξ K)} : Set Y)
  have hcov : (S : Set Y) ⊆ ⋃₀ (F : Set (Set Y)) := by
    refine closure_minimal ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨K, hK, hxK⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
        isIrreducible_singleton
      refine ⟨closure {f (ξ ⟨K, hK⟩)}, Finset.mem_coe.2 (Finset.mem_image_of_mem _
        (Finset.mem_univ _)), ?_⟩
      have hx : x ∈ closure ({ξ ⟨K, hK⟩} : Set T) := by
        rw [hξ]
        exact hxK rfl
      simpa using image_closure_subset_closure_image hf ⟨x, hx, rfl⟩
    · simp only [F, Finset.coe_image]
      exact Set.Finite.isClosed_sUnion (Set.toFinite _) fun _ ⟨_, _, h⟩ => h ▸ isClosed_closure
  have hle : topologicalKrullDim S ≤ m := by
    refine MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun Z hZ => ?_
    have hirr : IsIrreducible ((fun z : S => z.1) '' Z) :=
      hZ.1.image _ continuous_subtype_val.continuousOn
    obtain ⟨_, hz, hZz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hirr) F
      (fun z hz => by
        obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 hz
        exact isClosed_closure)
      ((image_subset_range _ _).trans (by rwa [Subtype.range_coe]))
    obtain ⟨K, -, rfl⟩ := Finset.mem_image.1 hz
    let e : Z → closure ({f (ξ K)} : Set Y) := fun z => ⟨z.1.1, hZz ⟨z.1, z.2, rfl⟩⟩
    have he : Topology.IsInducing e := by
      refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
      change Topology.IsInducing ((Subtype.val : S → Y) ∘ (Subtype.val : Z → S))
      exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    exact he.topologicalKrullDim_le.trans
      (Finset.le_sup (f := fun K : C => topologicalKrullDim (closure {f (ξ K)}))
        (Finset.mem_univ K))
  exact (hd.trans_lt (hle.trans_lt hm)).false

end Topology

section Points

/-- Every closed point of a scheme locally of finite type over `ℂ` is a `ℂ`-point. -/
private theorem exists_toScheme_eq {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sZ] (z : Z) (hz : IsClosed ({z} : Set Z)) :
    ∃ y : ComplexPoints sZ, y.toScheme = z := by
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  have hiso : IsIso (Z.fromSpecResidueField z ≫ sZ) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hz
    have hfin : IsFinite (Z.fromSpecResidueField z ≫ sZ) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
    rw [← Spec.map_preimage (Z.fromSpecResidueField z ≫ sZ)] at hfin ⊢
    rw [IsFinite.SpecMap_iff] at hfin
    have : IsIso (Spec.preimage (Z.fromSpecResidueField z ≫ sZ)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr
        (IsAlgClosed.ringHom_bijective_of_isIntegral _ hfin.to_isIntegral)
    infer_instance
  refine ⟨⟨inv (Z.fromSpecResidueField z ≫ sZ) ≫ Z.fromSpecResidueField z, by simp⟩, ?_⟩
  simp only [ComplexPoints.toScheme, ComplexPoints.hom, Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply]

/-- A point of `Spec Γ(Z, W)` lies over the basic open of `b` iff `b` is not in its prime. -/
private lemma fromSpec_mem_basicOpen_iff {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W)
    (P : Spec Γ(Z, W)) (b : Γ(Z, W)) :
    hW.fromSpec P ∈ Z.basicOpen b ↔ b ∉ P.asIdeal :=
  (congrArg (fun U : (Spec Γ(Z, W)).Opens => P ∈ U) (hW.fromSpec_preimage_basicOpen b)).to_iff

/-- A morphism over `ℂ` is compatible with the structure maps `ℂ → Γ(-, -)`. -/
private lemma appLE_baseRingHom {T : Scheme.{0}} {p : T ⟶ Spec (.of ℂ)} (g : T ⟶ X)
    (hg : g ≫ sX = p) (U : X.Opens) (W : T.Opens) (e : W ≤ g ⁻¹ᵁ U) (a : ℂ) :
    g.appLE U W e (baseRingHom sX U a) = baseRingHom p W a := by
  subst hg
  have key : sX.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ g.appLE U W e =
      (g ≫ sX).appTop ≫ T.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    exact (Scheme.Hom.comp_appLE g sX ⊤ W (by simp)).symm
  exact congrArg (fun φ => φ ((Scheme.ΓSpecIso (.of ℂ)).inv a)) key

/-- The structure map `ℂ → Γ(T, W)` of a scheme locally of finite type over `ℂ` is of finite
type on every affine open `W`. -/
theorem finiteType_baseRingHom {T : Scheme.{0}} (p : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p]
    {W : T.Opens} (hW : IsAffineOpen W) : (baseRingHom p W).FiniteType := by
  have h1 : (p.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) p ‹_›
      ⟨⊤, isAffineOpen_top (Spec (.of ℂ))⟩ ⟨W, hW⟩ _
  exact h1.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of ℂ)).inv).2)

/-- For a morphism `g : T ⟶ X` over `ℂ` with `T` locally of finite type, the map
`ℂ[Y₁, …, Y_d] → Γ(T, W)` sending `Yᵢ` to the pullback of the chart polynomial `qᵢ` is of finite
presentation. -/
theorem finitePresentation_appLE_comp_pres {T : Scheme.{0}} {p : T ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType p] (g : T ⟶ X) (hg : g ≫ sX = p) (c : Chart sX) {W : T.Opens}
    (hW : IsAffineOpen W) (hWU : W ≤ g ⁻¹ᵁ c.U) {d : ℕ}
    (q : Fin d → MvPolynomial (Fin c.n) ℂ) :
    ((g.appLE c.U W hWU).hom.comp
      (c.pres.comp (MvPolynomial.bind₁ q).toRingHom)).FinitePresentation := by
  let φ := g.appLE c.U W hWU
  let ρ : MvPolynomial (Fin d) ℂ →+* Γ(T, W) :=
    φ.hom.comp (c.pres.comp (MvPolynomial.bind₁ q).toRingHom)
  have hbase : ρ.comp MvPolynomial.C = baseRingHom p W := by
    ext a
    have e : ρ (MvPolynomial.C a) = φ (c.pres (MvPolynomial.C a)) := by
      simp only [ρ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.bind₁_C_right]
    rw [RingHom.comp_apply, e, Chart.pres, MvPolynomial.eval₂Hom_C]
    exact appLE_baseRingHom g hg c.U W hWU a
  exact RingHom.FinitePresentation.of_finiteType.1
    (RingHom.FiniteType.of_comp_finiteType (f := MvPolynomial.C)
      (hbase ▸ finiteType_baseRingHom p hW))

/-- The image in `Z` of a maximal ideal of `Γ(Z, W)`, for `W` an affine open, is a closed
point. -/
theorem isClosed_singleton_fromSpec_of_isMaximal {Z : Scheme.{0}} [JacobsonSpace Z]
    {W : Z.Opens} (hW : IsAffineOpen W) {P : Spec Γ(Z, W)} (hP : P.asIdeal.IsMaximal) :
    IsClosed ({hW.fromSpec P} : Set Z) := by
  have h : P ∈ closedPoints (Spec Γ(Z, W)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 hP
  rwa [← hW.fromSpec.isOpenEmbedding.preimage_closedPoints] at h

/-- **The image of a family contains an open set of values.** Let `g : T ⟶ X` be a morphism of
schemes locally of finite type over `ℂ`, `ξ ∈ T` with `g ξ` in a chart `c`, and `q` polynomials in
the chart coordinates with no polynomial relation at `g ξ`. Then the values `q(g(u))` at the
`ℂ`-points `u` of `T` fill a set with nonempty interior in `ℂᵈ`. -/
theorem nonempty_interior_chartPolyMap_image [LocallyOfFiniteType sX] {T : Scheme.{0}}
    {p : T ⟶ Spec (.of ℂ)} [LocallyOfFiniteType p] (g : T ⟶ X) (hg : g ≫ sX = p)
    (c : Chart sX) {ξ : T} (hξ : g ξ ∈ c.U) {d : ℕ} (q : Fin d → MvPolynomial (Fin c.n) ℂ)
    (hq : ∀ f : MvPolynomial (Fin d) ℂ, f ≠ 0 →
      g ξ ∈ X.basicOpen (c.pres (MvPolynomial.bind₁ q f))) :
    (interior (chartPolyMap c q '' {y : chart (sX := sX) c.U |
      y.1 ∈ Set.range (realize (sX := p) (sY := sX) g hg)})).Nonempty := by
  classical
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨W, hW, hξW, hWU⟩ := exists_isAffineOpen_mem_and_subset (x := ξ) (U := g ⁻¹ᵁ c.U) hξ
  have hWU' : W ≤ g ⁻¹ᵁ c.U := hWU
  let φ := g.appLE c.U W hWU'
  let ρ : MvPolynomial (Fin d) ℂ →+* Γ(T, W) :=
    φ.hom.comp (c.pres.comp (MvPolynomial.bind₁ q).toRingHom)
  have hρ : ρ.FinitePresentation := finitePresentation_appLE_comp_pres g hg c hW hWU' q
  have hmem : ∀ (P : Spec Γ(T, W)) (a : Γ(X, c.U)),
      hW.fromSpec P ∈ T.basicOpen (φ a) ↔ g (hW.fromSpec P) ∈ X.basicOpen a := by
    intro P a
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => h.2, fun h => ⟨hW.range_fromSpec ▸ Set.mem_range_self P, h⟩⟩
  let P₀ : Spec Γ(T, W) := hW.primeIdealOf ⟨ξ, hξW⟩
  obtain ⟨h, hh0, hlift⟩ := exists_ne_zero_forall_exists_isMaximal hρ P₀ (fun f hf => by
    rw [← fromSpec_mem_basicOpen_iff hW]
    change hW.fromSpec P₀ ∈ T.basicOpen (φ _)
    rw [hmem, hW.fromSpec_primeIdealOf ⟨ξ, hξW⟩]
    exact hq f hf)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Fin d → ℂ, MvPolynomial.eval z₀ h ≠ 0 :=
    not_forall.1 fun hcon => hh0 (MvPolynomial.funext fun z => by simpa using hcon z)
  refine ⟨z₀, mem_interior.2 ⟨{z | MvPolynomial.eval z h ≠ 0}, fun z hz => ?_,
    isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const, hz₀⟩⟩
  obtain ⟨M, hM, hMz⟩ := hlift z hz
  let P : Spec Γ(T, W) := ⟨M, hM.isPrime⟩
  set t := hW.fromSpec P with ht
  have htW : t ∈ W := hW.opensRange_fromSpec ▸ ⟨P, rfl⟩
  obtain ⟨u, hu⟩ := exists_toScheme_eq p t (isClosed_singleton_fromSpec_of_isMaximal hW hM)
  set y := realize (sX := p) (sY := sX) g hg u
  have hyt : y.toScheme = g t := by
    rw [← hu]
    rfl
  have hyU : y ∈ chart c.U := mem_chart_iff.2 (hyt ▸ hWU htW)
  refine ⟨⟨y, hyU⟩, ⟨u, rfl⟩, funext fun i => ?_⟩
  have hnot : g t ∉ X.basicOpen
      (c.pres (MvPolynomial.bind₁ q (MvPolynomial.X i - MvPolynomial.C (z i)))) := by
    rw [ht, ← hmem, fromSpec_mem_basicOpen_iff hW, not_not]
    exact hMz i
  rw [← hyt, toScheme_mem_basicOpen_iff ⟨y, hyU⟩, not_not, Chart.evalHom_pres] at hnot
  simp only [map_sub, MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_C_right,
    MvPolynomial.eval_C, sub_eq_zero] at hnot
  exact hnot

end Points

private lemma natCast_add_one_le_of_lt {m : ℕ} {x : WithBot ℕ∞} (h : (m : WithBot ℕ∞) < x) :
    ((m + 1 : ℕ) : WithBot ℕ∞) ≤ x := by
  induction x with
  | bot => exact absurd h not_lt_bot
  | coe y =>
    have h'' : (m : ℕ∞) + 1 ≤ y :=
      (ENat.add_one_le_iff (ENat.natCast_ne_top m)).2 (WithBot.coe_lt_coe.1 h)
    exact WithBot.coe_le_coe.2 (by simpa using h'')

/-- **Families inside countably many translates of `Φ(V)` have small image.** Let `X` be locally
of finite type over `ℂ`, `Φ : ℂⁿ → X(ℂ)` holomorphic in charts, `V ⊆ ℂⁿ` a complex subspace and
`(aₖ)` countably many points of `ℂⁿ`. If a morphism `g : T ⟶ X` over `ℂ` from a scheme of finite
type over `ℂ` sends every `ℂ`-point of `T` into `⋃ₖ Φ(aₖ + V)`, then the closure of its image has
dimension at most `dim V`.

If the dimension were `d > dim V`, some point `g ξ` would have a closure of dimension `≥ d`, and
`d` polynomials in chart coordinates, algebraically independent at `g ξ`, would take on the
`ℂ`-points of `T` a set of values with nonempty interior in `ℂᵈ` (Chevalley). That set has
Hausdorff dimension `2d`, but it lies in the images of countably many holomorphic maps on `V`,
of Hausdorff dimension at most `2 dim V`. -/
theorem topologicalKrullDim_closure_range_le_finrank [LocallyOfFiniteType sX]
    {Φ : (Fin n → ℂ) → ComplexPoints sX}
    (hhol : ∀ (v : Fin n → ℂ) (c : Chart sX) (_ : Φ v ∈ chart c.U),
      ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
        ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v')
    (V : Submodule ℂ (Fin n → ℂ)) {κ : Type*} [Countable κ] (a : κ → Fin n → ℂ)
    {T : Scheme.{0}} (p : T ⟶ Spec (.of ℂ)) [QuasiCompact p] [LocallyOfFiniteType p]
    (g : T ⟶ X) (hg : g ≫ sX = p)
    (hcov : ∀ u : ComplexPoints p, realize (sX := p) (sY := sX) g hg u ∈
      ⋃ k, (fun v => Φ (a k + v)) '' (V : Set (Fin n → ℂ))) :
    topologicalKrullDim (closure (Set.range g.base)) ≤ Module.finrank ℂ V := by
  classical
  by_contra! hlt
  set m := Module.finrank ℂ V
  have hd := natCast_add_one_le_of_lt hlt
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian T := {}
  obtain ⟨ξ, hξ⟩ := exists_le_topologicalKrullDim_closure_singleton g.base.hom.continuous hd
  obtain ⟨U', hU', hmem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := g ξ) (U := ⊤) trivial
  obtain ⟨c, rfl⟩ := Chart.exists_eq (sX := sX) hU'
  obtain ⟨q, hq⟩ := exists_forall_mem_basicOpen c hmem hξ
  have hint := nonempty_interior_chartPolyMap_image g hg c hmem q hq
  have hS : ∀ y ∈ {y : chart (sX := sX) c.U |
      y.1 ∈ Set.range (realize (sX := p) (sY := sX) g hg)},
      y.1 ∈ ⋃ k, (fun v => Φ (a k + v)) '' (V : Set (Fin n → ℂ)) :=
    fun _ ⟨u, hu⟩ => hu ▸ hcov u
  have := le_finrank_of_nonempty_interior hhol c q V a _ hS hint
  omega

section Cover

open CategoryTheory.Limits Opposite

/-- **The countable closed cover of `Φ(V)`, from countably many translates.** Let `ι : C ⟶ X` be
a smooth projective curve with a point `σ` on a projective variety over `ℂ`, `JX` its Jacobian,
`Φ : ℂⁿ → JX(ℂ)` holomorphic in charts and `V ⊆ ℂⁿ` a complex subspace. Suppose
* every restriction point of `JX` lies in one of countably many translates `Φ(aₖ + V)`;
* `Φ v` is a restriction point for every `v ∈ V`.

Then `Φ(V)` is covered by countably many closed subsets of `JX` of dimension at most `dim V`:
the closures of the images of the families of
`MMP.Analytic.SurfaceHodge.exists_families_restriction_isRestrictionPoint`, whose dimension is
bounded by `topologicalKrullDim_closure_range_le_finrank`. -/
theorem exists_countable_isClosed_cover_of_subset_iUnion {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] {C : Scheme.{0}}
    (ι : C ⟶ X) [IsClosedImmersion ι] (hproj : IsProjective (ι ≫ (X ↘ Spec (.of ℂ))))
    [SmoothOfRelativeDimension 1 (ι ≫ (X ↘ Spec (.of ℂ)))]
    (hdim : ∀ s : Spec (.of ℂ), topologicalKrullDim ↥((ι ≫ (X ↘ Spec (.of ℂ))).fiber s) ≤ 1)
    (σ : Spec (.of ℂ) ⟶ C) (hσ : σ ≫ ι ≫ (X ↘ Spec (.of ℂ)) = 𝟙 _) :
    haveI := hproj.isProper
    ∀ (JX : Grp (Over (Spec (.of ℂ)))) [LocallyOfFiniteType JX.X.hom]
      (eJ : yonedaGrp.obj JX ≅ Stacks.RigidifiedPicard.functorZero _ hdim σ hσ)
      {n : ℕ} (Φ : (Fin n → ℂ) → ComplexPoints JX.X.hom),
      (∀ (v : Fin n → ℂ) (c : Chart JX.X.hom) (_ : Φ v ∈ chart c.U),
        ∃ F : (Fin n → ℂ) → (Fin c.n → ℂ), DifferentiableAt ℂ F v ∧
          ∀ᶠ v' in 𝓝 v, ∃ h' : Φ v' ∈ chart c.U, c.coords ⟨Φ v', h'⟩ = F v') →
      ∀ (V : Submodule ℂ (Fin n → ℂ)) {κ : Type} [Countable κ] (a : κ → Fin n → ℂ),
      (∀ x : ComplexPoints JX.X.hom, IsRestrictionPoint ι _ hdim σ hσ eJ x →
        x ∈ ⋃ k, (fun v => Φ (a k + v)) '' (V : Set (Fin n → ℂ))) →
      (∀ v ∈ V, IsRestrictionPoint ι _ hdim σ hσ eJ (Φ v)) →
        ∃ (κ' : Type) (_ : Countable κ') (T' : κ' → Set JX.X.left), (∀ k, IsClosed (T' k)) ∧
          (∀ k, topologicalKrullDim (T' k) ≤ Module.finrank ℂ V) ∧
          ∀ v ∈ V, (Φ v).toScheme ∈ ⋃ k, T' k := by
  have := hproj.isProper
  intro JX _ eJ n Φ hhol V κ _ a hP hR
  obtain ⟨κ₀, hκ₀, T, p, hqc, hlft, c, g, hg, hpt, hcov⟩ :=
    exists_families_restriction_isRestrictionPoint ι hdim σ hσ eJ
  have hbound : ∀ k, topologicalKrullDim (closure (Set.range (g k).base)) ≤
      ((Module.finrank ℂ V : ℕ) : WithBot ℕ∞) := fun k => by
    have := hqc k
    have := hlft k
    refine topologicalKrullDim_closure_range_le_finrank hhol V a (p k) (g k) (hg k)
      (fun u => hP _ ?_)
    refine ⟨Stacks.Picard.schemePullbackClass (pullback.lift (𝟙 X)
      (X ↘ Spec (.of ℂ) ≫ u.1)
      (by rw [Category.assoc, u.2, Category.comp_id, Category.id_comp])) (c k), ?_⟩
    rw [Stacks.Picard.schemePullbackClass_comp, Category.assoc]
    exact hpt k u.1 u.2
  obtain ⟨κ', hκ', T', hT', hdT', hcov'⟩ := exists_countable_isClosed_cover_of_families g hbound
    (S := {y | ∃ v ∈ V, (Φ v).toScheme = y})
    (fun _ ⟨v, hv, hy⟩ => hy ▸ hcov _ (hR v hv))
  exact ⟨κ', hκ', T', hT', hdT', fun v hv => hcov' ⟨v, hv, rfl⟩⟩

end Cover

end MMP.Analytic.SurfaceHodge
