module

public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Divisor.Basic
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.PointsOver
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVariety
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularOpensSmooth
public import MMP.AlgebraicTopology.OrientationClass.CapCodimZero
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.ProjectiveSpace
import MMP.AlgebraicGeometry.Semialgebraic.Operations
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
public import StacksFrontier.Topology.Compactification.OnePoint

/-!
# Retracting neighbourhoods and supported duality for algebraic subsets

Two topological facts about the complex points of a projective complex scheme `X` and a
Zariski-closed `D ⊆ X`. First, every open neighbourhood of the analytic trace `D^an` contains an
open neighbourhood which strongly deformation retracts onto `D^an`. Second, when `X = Y` is a
non-singular projective complex variety of dimension `d` with fundamental class `μ`, capping with
`μ` is an isomorphism `H^{2d-k}(Y(ℂ), Y(ℂ) - D(ℂ); ℚ) ≅ H_k(D(ℂ); ℚ)` for every `k`.

## Main results

* `MMP.Analytic.exists_homotopicRel_retraction_of_isProjective`: every open neighbourhood of
  `D^an` contains one that strongly deformation retracts onto `D^an`.
* `MMP.Analytic.bijective_dualityMap_of_isVarietyFundamentalClass`: the duality map
  `c ↦ c ∩ μ_Y` is bijective.
* `MMP.Analytic.bijective_dualityMap_natural_of_isVarietyFundamentalClass`: supported duality in
  full: the duality map is bijective, natural in the support and under restriction to open
  subsets, the orientation isomorphism on normal disks to the smooth part of `D(ℂ)` (it carries
  orientation classes to fundamental classes), and its induced map to `H^k D(ℂ)` is restriction.

## Implementation notes

Each result's auxiliary lemmas live in a namespace `Proof_<tag>` named after its label,
opened only for that result.

* `X^an` is `MMP.Analytic.ComplexPoints sX` with its analytic topology, and `D^an` is the inverse
  image of `D` under `MMP.Analytic.ComplexPoints.toScheme`. A strong deformation retraction of
  `N` onto `D^an` is a retraction `r : N → D^an` with the identity of `N` homotopic to `r`
  relative to `D^an`, as `ContinuousMap.HomotopicRel`. The proof embeds `X^an` as a compact
  semialgebraic set, triangulates it compatibly with the image of `D^an`, and uses the
  straight-line deformation of the barycentric subdivision onto the full subcomplex over `D^an`;
  its trajectories are nested, so the points whose trajectory stays in a given neighbourhood
  form a smaller retracting neighbourhood.
* `Y(ℂ)` is Fulton's underlying space `MMP.UnderlyingSpace ℂ Y`, `D(ℂ)` its subset
  `MMP.UnderlyingSpace.pointsOver D`, the supported cohomology is
  `MMP.cohomologyWithSupports` and the map is
  `MMP.borelMooreHomology.dualityMap`, the cap product with `μ_Y`. Since `Y` is
  non-singular, `Y(ℂ)` is its own regular part, a real `2d`-manifold with fundamental class the
  restriction of `μ`; Alexander duality on it is transported along `Y_reg(ℂ) ≅ Y(ℂ)`.
  Naturality is the compatibility of the cap product with forgetting supports and with
  restriction to open subsets; the normal-disk clause is `u_{Z,U} ∩ μ_U = μ_Z` for the orientation
  class of a closed complex submanifold `Z = D(ℂ) ∩ U` of an open `U`, after comparing the bases
  `e₁, i e₁, …` of `ℂᵈ` and `complexOrientationBasisOf ℂᵈ`, which have the same orientation; the
  restriction clause is homotopy invariance of singular cohomology along the retraction.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
* [J. Bochnak, M. Coste, M.-F. Roy, *Real algebraic geometry*][bochnak1998], §9.2.
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Set

namespace MMP.Proof_lem_mmp_projective_algebraic_retracting_neighbourhoods

section Deformation

open unitInterval

/-- `D` has a *nested deformation*: an open neighbourhood `N₀` of `D` and a homotopy `H` of `N₀`
in itself from the identity into `D`, fixing `D`, whose trajectories are nested: the trajectory
of `H y s` is part of that of `y`. -/
private def HasNestedDeformation {Y : Type*} [TopologicalSpace Y] (D : Set Y) : Prop :=
  ∃ (N₀ : Set Y) (H : Y → I → Y), IsOpen N₀ ∧ D ⊆ N₀ ∧
    ContinuousOn (fun p : Y × I ↦ H p.1 p.2) (N₀ ×ˢ univ) ∧
    (∀ y ∈ N₀, H y 0 = y) ∧ (∀ y ∈ N₀, H y 1 ∈ D) ∧ (∀ y ∈ D, ∀ t, H y t = y) ∧
    (∀ y ∈ N₀, ∀ t, H y t ∈ N₀) ∧ (∀ y ∈ N₀, ∀ s t, ∃ u, H (H y s) t = H y u)

/-- **Nested deformations give small strong deformation retractions.** If `D` has a nested
deformation `H` on `N₀`, every open `W ⊇ D` contains the open set `N` of points whose whole
trajectory lies in `W`; `N` is invariant under `H`, which restricts to a strong deformation
retraction of `N` onto `D`. -/
private theorem HasNestedDeformation.exists_homotopicRel_retraction {Y : Type*}
    [TopologicalSpace Y] {D : Set Y} (h : HasNestedDeformation D) {W : Set Y} (hW : IsOpen W)
    (hDW : D ⊆ W) :
    ∃ N : Set Y, IsOpen N ∧ N ⊆ W ∧ ∃ hDN : D ⊆ N, ∃ r : C(N, D),
      (ContinuousMap.id N).HomotopicRel
        ((⟨Set.inclusion hDN, continuous_inclusion hDN⟩ : C(D, N)).comp r)
        (Set.range (Set.inclusion hDN)) := by
  obtain ⟨N₀, H, hN₀, hDN₀, hHc, hH0, hH1, hHD, hHN, hHH⟩ := h
  set O := N₀ ×ˢ univ ∩ (fun p : Y × I ↦ H p.1 p.2) ⁻¹' W
  have hO : IsOpen O := hHc.isOpen_inter_preimage (hN₀.prod isOpen_univ) hW
  set N := {y : Y | ∀ t : I, (y, t) ∈ O} with hNdef
  have hNeq : N = (Prod.fst '' Oᶜ)ᶜ := by
    ext y
    simp only [hNdef, mem_setOf_eq, mem_compl_iff, mem_image, not_exists, not_and]
    exact ⟨fun h ⟨_, t⟩ hp hy ↦ hp (by subst hy; exact h t),
      fun h t ↦ Classical.byContradiction fun hc ↦ h (y, t) hc rfl⟩
  have hNo : IsOpen N := hNeq ▸ (isClosedMap_fst_of_compactSpace _ hO.isClosed_compl).isOpen_compl
  have hNN₀ : ∀ y ∈ N, y ∈ N₀ := fun y hy ↦ (hy 0).1.1
  have hNW : ∀ y ∈ N, ∀ t, H y t ∈ W := fun y hy t ↦ (hy t).2
  have hDN : D ⊆ N := fun y hy t ↦ ⟨⟨hDN₀ hy, mem_univ _⟩, by
    simpa only [mem_preimage, hHD y hy t] using hDW hy⟩
  have hHNN : ∀ y ∈ N, ∀ s, H y s ∈ N := by
    intro y hy s t
    obtain ⟨u, hu⟩ := hHH y (hNN₀ y hy) s t
    exact ⟨⟨hHN y (hNN₀ y hy) s, mem_univ _⟩, by
      simpa only [mem_preimage, hu] using hNW y hy u⟩
  have hcont : Continuous fun p : I × N ↦ H p.2.1 p.1 := by
    refine hHc.comp_continuous (f := fun p : I × N ↦ ((p.2 : Y), p.1))
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
      fun p ↦ ⟨hNN₀ _ p.2.2, mem_univ _⟩
  refine ⟨N, hNo, fun y hy ↦ by simpa [hH0 y (hNN₀ y hy)] using hNW y hy 0, hDN,
    ⟨fun y ↦ ⟨H y.1 1, hH1 _ (hNN₀ _ y.2)⟩, ?_⟩, ⟨?_⟩⟩
  · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).subtype_mk _
  refine
    { toFun := fun p ↦ ⟨H p.2.1 p.1, hHNN _ p.2.2 _⟩
      continuous_toFun := hcont.subtype_mk _
      map_zero_left := fun y ↦ Subtype.ext (hH0 _ (hNN₀ _ y.2))
      map_one_left := fun y ↦ rfl
      prop' := ?_ }
  rintro t _ ⟨d, rfl⟩
  exact Subtype.ext (hHD _ d.2 t)

/-- Nested deformations pull back along homeomorphisms. -/
private theorem HasNestedDeformation.preimage {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {D : Set Z} (h : HasNestedDeformation D) (e : Y ≃ₜ Z) :
    HasNestedDeformation (e ⁻¹' D) := by
  obtain ⟨N₀, H, hN₀, hDN₀, hHc, hH0, hH1, hHD, hHN, hHH⟩ := h
  refine ⟨e ⁻¹' N₀, fun y t ↦ e.symm (H (e y) t), hN₀.preimage e.continuous,
    fun y hy ↦ hDN₀ hy, ?_, fun y hy ↦ by simp [hH0 _ hy], fun y hy ↦ by simpa using hH1 _ hy,
    fun y hy t ↦ by simp [hHD _ hy t], fun y hy t ↦ by simpa using hHN _ hy t,
    fun y hy s t ↦ ?_⟩
  · exact e.symm.continuous.comp_continuousOn (hHc.comp (f := fun p : Y × I ↦ (e p.1, p.2))
      (by fun_prop) fun p hp ↦ ⟨hp.1, trivial⟩)
  · obtain ⟨u, hu⟩ := hHH _ hy s t
    exact ⟨u, by simp [hu]⟩

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The weight `∑_{b ∈ V} y_b` of a weight vector `y` on the vertices in `V`. -/
private noncomputable def faceWeight (V : Finset κ) (y : κ → ℝ) : ℝ := ∑ b ∈ V, y b

/-- The renormalised restriction `(∑_{b ∈ V} y_b)⁻¹ y|_V` of `y` to the vertices in `V`. -/
private noncomputable def faceRetraction (V : Finset κ) (y : κ → ℝ) : κ → ℝ :=
  (faceWeight V y)⁻¹ • fun b ↦ if b ∈ V then y b else 0

/-- The straight-line homotopy `(1 - t) y + t r(y)` from `y` to its face retraction `r(y)`. -/
private noncomputable def faceDeformation (V : Finset κ) (y : κ → ℝ) (t : ℝ) : κ → ℝ :=
  (1 - t) • y + t • faceRetraction V y

private lemma faceWeight_faceRetraction (V : Finset κ) {y : κ → ℝ} (hy : faceWeight V y ≠ 0) :
    faceWeight V (faceRetraction V y) = 1 := by
  simp only [faceWeight, faceRetraction, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_congr rfl fun b hb ↦ if_pos hb]
  exact inv_mul_cancel₀ hy

private lemma faceWeight_faceDeformation (V : Finset κ) {y : κ → ℝ} (hy : faceWeight V y ≠ 0)
    (t : ℝ) : faceWeight V (faceDeformation V y t) = (1 - t) * faceWeight V y + t := by
  have := faceWeight_faceRetraction V hy
  simp only [faceWeight, faceDeformation, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib,
    ← Finset.mul_sum] at this ⊢
  rw [this, mul_one]

/-- The straight-line homotopy keeps the weight on `V` positive. -/
private lemma faceWeight_faceDeformation_pos (V : Finset κ) {y : κ → ℝ}
    (hy : 0 < faceWeight V y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < faceWeight V (faceDeformation V y t) := by
  rw [faceWeight_faceDeformation V hy.ne']
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hy.le]

private lemma faceRetraction_faceDeformation (V : Finset κ) {y : κ → ℝ} (hy : 0 < faceWeight V y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    faceRetraction V (faceDeformation V y t) = faceRetraction V y := by
  have hpos := faceWeight_faceDeformation_pos V hy ht0 ht1
  have hw := faceWeight_faceDeformation V hy.ne' t
  rw [hw] at hpos
  rw [show faceRetraction V (faceDeformation V y t) =
    (faceWeight V (faceDeformation V y t))⁻¹ • fun b ↦
    if b ∈ V then faceDeformation V y t b else 0 from rfl, hw]
  funext b
  simp only [Pi.smul_apply, smul_eq_mul, faceRetraction]
  split_ifs with hb
  · simp only [faceDeformation, faceRetraction, Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_pos hb]
    field_simp
  · simp

private lemma faceDeformation_faceDeformation (V : Finset κ) {y : κ → ℝ} (hy : 0 < faceWeight V y)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    faceDeformation V (faceDeformation V y s) t = faceDeformation V y (1 - (1 - s) * (1 - t)) := by
  rw [faceDeformation, faceRetraction_faceDeformation V hy hs0 hs1]
  funext b
  simp only [faceDeformation, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The weight vectors (nonnegative, of sum one) whose support satisfies `Q`. For `Q` the
chains of a face relation this is the polyhedron of the order complex. -/
private def supportPolyhedron (Q : Set κ → Prop) : Set (κ → ℝ) :=
  {y | (∀ a, 0 ≤ y a) ∧ ∑ a, y a = 1 ∧ Q {a | y a ≠ 0}}

/-- **Full subcomplexes have nested deformations.** In the polyhedron of weight vectors with
support satisfying a hereditary `Q`, the points supported on `V` have the nested deformation
`faceDeformation V` on the open set of points of positive weight on `V`. -/
private theorem hasNestedDeformation_supportPolyhedron (Q : Set κ → Prop)
    (hQ : ∀ s t, t ⊆ s → Q s → Q t) (V : Finset κ) :
    HasNestedDeformation {y : supportPolyhedron Q | ∀ a, (y : κ → ℝ) a ≠ 0 → a ∈ V} := by
  classical
  set D := {y : supportPolyhedron Q | ∀ a, (y : κ → ℝ) a ≠ 0 → a ∈ V}
  set N₀ := {y : supportPolyhedron Q | 0 < faceWeight V y}
  have hmem : ∀ y : supportPolyhedron Q, 0 < faceWeight V y → ∀ t : I,
      faceDeformation V y t ∈ supportPolyhedron Q := by
    intro y hy t
    obtain ⟨h0, h1, h2⟩ := y.2
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    refine ⟨fun a ↦ ?_, ?_, hQ _ _ ?_ h2⟩
    · simp only [faceDeformation, faceRetraction, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : 0 ≤ (faceWeight V y)⁻¹ * (if a ∈ V then (y : κ → ℝ) a else 0) :=
        mul_nonneg (inv_nonneg.2 hy.le) (by split_ifs <;> simp [h0 a])
      nlinarith [h0 a]
    · have hp : ∑ a, faceRetraction V y a = 1 := by
        simp only [faceRetraction, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
        exact inv_mul_cancel₀ hy.ne'
      simp only [faceDeformation, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, h1, hp]
      ring
    · intro a ha
      simp only [mem_setOf_eq] at ha ⊢
      intro hya
      apply ha
      simp [faceDeformation, faceRetraction, hya]
  have hwt_cont : Continuous (faceWeight V) := continuous_finset_sum _ fun b _ ↦ continuous_apply b
  have hwtD : ∀ y ∈ D, faceWeight V (y : κ → ℝ) = 1 := by
    intro y hy
    rw [faceWeight, ← y.2.2.1]
    exact Finset.sum_subset (Finset.subset_univ _) fun b _ hb ↦ not_imp_comm.1 (hy b) hb
  have hprojD : ∀ y ∈ D, faceRetraction V (y : κ → ℝ) = y := by
    intro y hy
    funext b
    simp only [faceRetraction, hwtD y hy, inv_one, one_smul]
    split_ifs with hb
    · rfl
    · exact (not_imp_comm.1 (hy b) hb).symm
  let H : supportPolyhedron Q → I → supportPolyhedron Q := fun y t ↦
    if h : 0 < faceWeight V y then ⟨faceDeformation V y t, hmem y h t⟩ else y
  have hH : ∀ y : supportPolyhedron Q, ∀ hy : 0 < faceWeight V y, ∀ t,
      H y t = ⟨faceDeformation V y t, hmem y hy t⟩ :=
    fun y hy t ↦ dif_pos hy
  refine ⟨N₀, H, (isOpen_lt continuous_const (hwt_cont.comp continuous_subtype_val)),
    fun y hy ↦ by simp [N₀, hwtD y hy], ?_, fun y hy ↦ ?_, fun y hy ↦ ?_, fun y hy t ↦ ?_,
    fun y hy t ↦ ?_, fun y hy s t ↦ ?_⟩
  · rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : ContinuousOn (fun p : supportPolyhedron Q × I ↦
        faceDeformation V (p.1 : κ → ℝ) p.2) (N₀ ×ˢ univ) := by
      have hw : ContinuousOn (fun p : supportPolyhedron Q × I ↦
          (faceWeight V (p.1 : κ → ℝ))⁻¹) (N₀ ×ˢ univ) :=
        ((hwt_cont.comp (continuous_subtype_val.comp continuous_fst)).continuousOn).inv₀
          fun p hp ↦ (show 0 < faceWeight V (p.1 : κ → ℝ) from hp.1).ne'
      have hi : Continuous (fun p : supportPolyhedron Q × I ↦
          fun b ↦ if b ∈ V then (p.1 : κ → ℝ) b else 0) := by
        refine continuous_pi fun b ↦ ?_
        split_ifs
        · exact (continuous_apply b).comp (continuous_subtype_val.comp continuous_fst)
        · exact continuous_const
      have ht : Continuous (fun p : supportPolyhedron Q × I ↦ (p.2 : ℝ)) :=
        continuous_subtype_val.comp continuous_snd
      exact ((continuous_const.sub ht).smul
        (continuous_subtype_val.comp continuous_fst)).continuousOn.add
        (ht.continuousOn.smul (hw.smul hi.continuousOn))
    refine hc.congr fun p hp ↦ ?_
    simp only [Function.comp_apply, hH p.1 hp.1]
  · rw [hH y hy]
    ext b
    simp [faceDeformation]
  · rw [hH y hy]
    intro a ha
    simp only [faceDeformation, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add,
      faceRetraction,
      Pi.smul_apply, smul_eq_mul] at ha
    by_contra h
    simp [h] at ha
  · have hy' : 0 < faceWeight V (y : κ → ℝ) := by simp [hwtD y hy]
    rw [hH y hy' t]
    ext b
    simp [faceDeformation, hprojD y hy]
    ring
  · rw [hH y hy t]
    exact faceWeight_faceDeformation_pos V hy t.2.1 t.2.2
  · refine ⟨σ (σ s * σ t), ?_⟩
    rw [hH y hy s, hH _ (faceWeight_faceDeformation_pos V hy s.2.1 s.2.2) t, hH y hy]
    exact Subtype.ext (faceDeformation_faceDeformation V hy s.2.1 s.2.2)

/-- **Closed semialgebraic subsets of compact semialgebraic sets have nested deformations.**
Triangulate `S` compatibly with `A`; the open simplices form a radial cell complex, whose order
complex triangulates `S` again with `A` the full subcomplex on the cells inside `A`. -/
private theorem hasNestedDeformation_of_isSemialgebraic {ω : Type} [Fintype ω] {S A : Set (ω → ℝ)}
    (hSc : IsCompact S) (hS : IsSemialgebraic S) (hA : IsSemialgebraic A) (hAc : IsClosed A)
    (hAS : A ⊆ S) : HasNestedDeformation {x : S | (x : ω → ℝ) ∈ A} := by
  classical
  rcases isEmpty_or_nonempty S with hE | hNe
  · exact ⟨univ, fun y _ ↦ y, isOpen_univ, subset_univ _, continuousOn_fst,
      fun y _ ↦ rfl, fun y ↦ (hE.false y).elim, fun _ _ _ ↦ rfl, fun _ _ _ ↦ mem_univ _,
      fun y _ s t ↦ ⟨t, rfl⟩⟩
  obtain ⟨ν, _, _, Δ, h, hT, hcomp⟩ := stdTriangulable ω S Unit (fun _ ↦ A) hSc hS
    (fun _ ↦ hA) (fun _ ↦ hAS)
  have hcomp' : ∀ s ∈ Δ, h '' openStd s ⊆ A ∨ Disjoint (h '' openStd s) A := fun s hs ↦ by
    rw [openStd_eq_openSimplex]
    exact hcomp () s hs
  let κ := Δ
  haveI : Finite κ := Set.toFinite Δ
  letI : Fintype κ := Fintype.ofFinite κ
  have hne : ∀ s : κ, (s : Finset ν).Nonempty := fun s ↦ hT.nonempty s.1 s.2
  let e : κ → Set (ω → ℝ) := fun s ↦ h '' openStd (s : Finset ν)
  let center : κ → ω → ℝ := fun s ↦ h (baryStd (s : Finset ν))
  let ray : κ → (ω → ℝ) → ℝ → ω → ℝ := fun s q τ ↦
    h (baryStd (s : Finset ν) + τ • (Function.invFunOn h (closedStd (s : Finset ν)) q -
      baryStd (s : Finset ν)))
  have hcell : ∀ s : κ, closure (e s) = h '' closedStd (s : Finset ν) ∧
      IsRadialCell (e s) (center s) (ray s) := by
    intro s
    have hθ : ContinuousOn h (closedStd (s : Finset ν)) :=
      hT.continuousOn.mono (closedStd_subset_stdSpace s.2)
    have hinj : InjOn h (closedStd (s : Finset ν)) := hT.injOn.mono (closedStd_subset_stdSpace s.2)
    have := (isRadialModel_closedStd (hne s)).isRadialCell (isCompact_closedStd _)
      (continuous_stdGauge (hne s)).continuousOn hθ hinj
    rw [closedStd_inter_lt_one (hne s)] at this
    exact ⟨this.1, this.2.2⟩
  have hsupp : ∀ y ∈ stdSpace Δ, ∃ t : κ, y ∈ openStd (t : Finset ν) := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 hy
    rw [← closedStd_eq_convexHull] at hys
    obtain ⟨hts, htne, hyt⟩ := mem_openStd_support hys
    exact ⟨⟨_, hT.down_closed s hs _ hts htne⟩, hyt⟩
  have hopen_supp : ∀ (t : Finset ν) (y : ν → ℝ), y ∈ openStd t →
      Finset.univ.filter (y · ≠ 0) = t := by
    intro t y hy
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hu ↦ by by_contra h'; exact hu (hy.2.2 u h'), fun hu ↦ (hy.1 u hu).ne'⟩
  have hHC : IsRadialCellComplex e center ray := by
    refine ⟨fun s t hst ↦ ?_, fun s ↦ (hcell s).2, fun s ↦ ?_, fun s t ↦ ?_⟩
    · refine Set.disjoint_left.2 ?_
      rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
      have hyS := closedStd_subset_stdSpace s.2 (openStd_subset_closedStd _ hy)
      have hzS := closedStd_subset_stdSpace t.2 (openStd_subset_closedStd _ hz)
      have := hT.injOn hzS hyS hzy
      subst this
      exact hst (Subtype.ext ((hopen_supp _ _ hy).symm.trans (hopen_supp _ _ hz)))
    · rw [(hcell s).1]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := hsupp y (closedStd_subset_stdSpace s.2 hy)
      exact mem_iUnion.2 ⟨t, y, ht, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hcl⟩
      rw [(hcell s).1] at hcl ⊢
      obtain ⟨z, hz, hzy⟩ := hcl
      have hyS := closedStd_subset_stdSpace t.2 (openStd_subset_closedStd _ hy)
      have hzS := closedStd_subset_stdSpace s.2 hz
      have := hT.injOn hzS hyS hzy
      subst this
      have hts : (t : Finset ν) ⊆ s := by
        rw [← hopen_supp _ _ hy]; exact (mem_openStd_support hz).1
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨w, ⟨(openStd_subset_closedStd _ hw).1, hw.2.1, fun u hu ↦ hw.2.2 u
        fun hu' ↦ hu (hts hu')⟩, rfl⟩
  haveI : Nonempty κ := by
    obtain ⟨x⟩ := hNe
    have hx : (x : ω → ℝ) ∈ h '' stdSpace Δ := hT.image_eq ▸ x.2
    obtain ⟨y, hy, -⟩ := hx
    obtain ⟨t, -⟩ := hsupp y hy
    exact ⟨t⟩
  obtain ⟨hT', -⟩ := hHC.isStdTriangulation
  set g := coneMap e center ray
  let Q : Set κ → Prop := fun c ↦ IsChain (CellLT e) c
  have hQ : ∀ s t, t ⊆ s → Q s → Q t := fun s t hts hs ↦ hs.mono hts
  have hpoly : supportPolyhedron Q = stdSpace (orderComplex e) :=
    Set.ext fun _ ↦ isChainPoint_iff_mem_stdSpace
  have hU : (⋃ a, e a) = S := by
    rw [← hT.image_eq, stdSpace, image_iUnion₂]
    ext x
    simp only [mem_iUnion, e]
    constructor
    · rintro ⟨s, y, hy, rfl⟩
      exact ⟨s.1, s.2, y, by rw [← closedStd_eq_convexHull]; exact openStd_subset_closedStd _ hy,
        rfl⟩
    · rintro ⟨s, hs, y, hy, rfl⟩
      rw [← closedStd_eq_convexHull] at hy
      obtain ⟨t, ht⟩ := hsupp y (closedStd_subset_stdSpace hs hy)
      exact ⟨t, y, ht, rfl⟩
  have hgS : ∀ y ∈ supportPolyhedron Q, g y ∈ S := fun y hy ↦ by
    rw [← hU, ← hT'.image_eq]
    exact ⟨y, hpoly ▸ hy, rfl⟩
  haveI : CompactSpace (supportPolyhedron Q) := by
    rw [← isCompact_iff_compactSpace, hpoly, stdSpace]
    exact (Set.toFinite _).isCompact_biUnion fun c _ ↦
      (Finset.finite_toSet _).isCompact_convexHull ℝ
  have hcont : Continuous fun y : supportPolyhedron Q ↦ (⟨g y, hgS y y.2⟩ : S) :=
    (hT'.continuousOn.comp_continuous continuous_subtype_val
      fun y ↦ hpoly ▸ y.2).subtype_mk _
  have hbij : Function.Bijective fun y : supportPolyhedron Q ↦ (⟨g y, hgS y y.2⟩ : S) := by
    refine ⟨fun y y' hyy ↦ Subtype.ext (hT'.injOn (hpoly ▸ y.2) (hpoly ▸ y'.2)
      (congrArg Subtype.val hyy)), fun x ↦ ?_⟩
    have hx : (x : ω → ℝ) ∈ g '' stdSpace (orderComplex e) := hT'.image_eq.trans hU ▸ x.2
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hpoly ▸ hy⟩, Subtype.ext hyx⟩
  let Θ : supportPolyhedron Q ≃ₜ S := hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij)
  have hΘ : ∀ y, (Θ y : ω → ℝ) = g y := fun y ↦ rfl
  set V := Finset.univ.filter fun a ↦ e a ⊆ A
  have hkey : ∀ y : supportPolyhedron Q, g y ∈ A ↔ ∀ a, (y : κ → ℝ) a ≠ 0 → a ∈ V := by
    intro y
    have hy : IsChainPoint e y := y.2
    have hmem := hHC.coneMap_mem hy
    have htop := hHC.isChainTop_chainTop hy
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hgA
      have htopA : e (chainTop e y) ⊆ A := by
        rcases hcomp' _ (chainTop e y).2 with h' | h'
        · exact h'
        · exact absurd hgA (Set.disjoint_left.1 h' hmem)
      intro a ha
      rcases htop.2 a ha with rfl | hlt
      · exact htopA
      · exact hlt.trans (diff_subset.trans (closure_minimal htopA hAc))
    · intro hall
      exact hall _ htop.1 hmem
  have := (hasNestedDeformation_supportPolyhedron Q hQ V).preimage Θ.symm
  convert this using 1
  ext x
  simp only [mem_setOf_eq, mem_preimage]
  rw [← hkey, ← hΘ, Θ.apply_symm_apply]

end Deformation

section Model

open MMP MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

/-- A section over the standard chart `Uᵢ` of `ℙⁿ_ℂ` is, at the points of `Uᵢ(ℂ)`, a polynomial
in the affine coordinates `x_j / xᵢ`. -/
private theorem exists_eval_eq_eval_mvPolynomial
    [(AlgebraicGeometry.Proj (polyGrading ℂ n)).Over (Spec (.of ℂ))]
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n)
    (i : Fin (n + 1))
    (f : Γ(AlgebraicGeometry.Proj (polyGrading ℂ n), projectiveSpaceStdChart ℂ n i)) :
    ∃ Q : MvPolynomial (Fin (n + 1)) ℂ,
      ∀ (q : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n)))
      (hq : ⊤ ≤ q.toHom ⁻¹ᵁ projectiveSpaceStdChart ℂ n i),
      eval q hq f = MvPolynomial.eval (fun j ↦ eval q hq (projectiveSpaceStdCoord ℂ n i j)) Q := by
  have hf : f ∈ Subring.closure
      (Set.range (structureRingHomOpens (K := ℂ) (projectiveSpaceStdChart ℂ n i)) ∪
        Set.range (projectiveSpaceStdCoord ℂ n i)) := by
    rw [closure_projectiveSpaceStdCoord hP]; trivial
  induction hf using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨MvPolynomial.C c, fun q hq ↦ by simp [eval_structureRingHomOpens]⟩
    · exact ⟨MvPolynomial.X j, fun q hq ↦ by simp⟩
  | zero => exact ⟨0, fun q hq ↦ by rw [← evalRingHom_apply, map_zero, map_zero]⟩
  | one => exact ⟨1, fun q hq ↦ by rw [← evalRingHom_apply, map_one, map_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨R, hR⟩ := hy
    exact ⟨P + R, fun q hq ↦ by rw [← evalRingHom_apply, map_add, map_add, evalRingHom_apply,
      evalRingHom_apply, hP, hR]⟩
  | neg x _ hx =>
    obtain ⟨P, hP⟩ := hx
    exact ⟨-P, fun q hq ↦ by rw [← evalRingHom_apply, map_neg, map_neg, evalRingHom_apply, hP]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨R, hR⟩ := hy
    exact ⟨P * R, fun q hq ↦ by rw [← evalRingHom_apply, map_mul, map_mul, evalRingHom_apply,
      evalRingHom_apply, hP, hR]⟩

/-- A Zariski-closed subset of `ℙⁿ_ℂ` is cut out, on the points of the standard chart `Uᵢ(ℂ)`,
by finitely many polynomials in the affine coordinates `x_j / xᵢ`. -/
private theorem exists_mem_iff_eval_eq_zero
    [(AlgebraicGeometry.Proj (polyGrading ℂ n)).Over (Spec (.of ℂ))]
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n)
    {Z : Set (AlgebraicGeometry.Proj (polyGrading ℂ n))} (hZ : IsClosed Z)
    (i : Fin (n + 1)) :
    ∃ (ι : Type) (_ : Finite ι) (Q : ι → MvPolynomial (Fin (n + 1)) ℂ),
      ∀ (q : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n)))
        (hq : ⊤ ≤ q.toHom ⁻¹ᵁ projectiveSpaceStdChart ℂ n i),
        (q.toHom (IsLocalRing.closedPoint ℂ) ∈ Z ↔ ∀ k, MvPolynomial.eval
          (fun j ↦ eval q hq (projectiveSpaceStdCoord ℂ n i j)) (Q k) = 0) := by
  set U := projectiveSpaceStdChart ℂ n i
  have hU : IsAffineOpen U := Proj.isAffineOpen_basicOpen _ _
    (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one ℂ n i) one_pos
  let O : (AlgebraicGeometry.Proj (polyGrading ℂ n)).Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hf : ∀ x : O, ∃ f : Γ(AlgebraicGeometry.Proj (polyGrading ℂ n), U),
      (AlgebraicGeometry.Proj (polyGrading ℂ n)).basicOpen f ≤ O ∧
        (x : AlgebraicGeometry.Proj (polyGrading ℂ n)) ∈
          (AlgebraicGeometry.Proj (polyGrading ℂ n)).basicOpen f :=
    fun x ↦ hU.exists_basicOpen_le x x.2.1
  choose f hfO hxf using hf
  have hc :=
    TopologicalSpace.NoetherianSpace.isCompact (O : Set (AlgebraicGeometry.Proj (polyGrading ℂ n)))
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun x : O ↦
      ((AlgebraicGeometry.Proj (polyGrading ℂ n)).basicOpen (f x) :
        Set (AlgebraicGeometry.Proj (polyGrading ℂ n))))
    (fun x ↦ ((AlgebraicGeometry.Proj (polyGrading ℂ n)).basicOpen (f x)).2)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩)
  choose Q hQ using fun x : t ↦ exists_eval_eq_eval_mvPolynomial hP i (f x)
  refine ⟨t, inferInstance, Q, fun q hq ↦ ?_⟩
  have hqU : q.toHom (IsLocalRing.closedPoint ℂ) ∈ U := (top_le_preimage_iff q U).1 hq
  have hb : ∀ x : t,
      q.toHom (IsLocalRing.closedPoint ℂ) ∈
        (AlgebraicGeometry.Proj (polyGrading ℂ n)).basicOpen (f x) ↔
      MvPolynomial.eval (fun j ↦ eval q hq (projectiveSpaceStdCoord ℂ n i j)) (Q x) ≠ 0 := by
    intro x
    rw [← hQ x q hq, ← top_le_preimage_basicOpen_iff q hq, top_le_preimage_iff]
  constructor
  · exact fun hqZ k ↦ Classical.byContradiction fun hk ↦ (hfO k ((hb k).2 hk)).2 hqZ
  · intro hall
    by_contra hqZ
    have hqO : q.toHom (IsLocalRing.closedPoint ℂ) ∈
        (O : Set (AlgebraicGeometry.Proj (polyGrading ℂ n))) := ⟨hqU, hqZ⟩
    obtain ⟨x, hx⟩ := mem_iUnion₂.1 (ht hqO)
    exact (hb ⟨x, hx.1⟩).1 hx.2 (hall ⟨x, hx.1⟩)

open MMP.Topology in
/-- Real coordinates of a complex square matrix. -/
private noncomputable def matrixToReal (P : Fin (n + 1) → Fin (n + 1) → ℂ) :
    (Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ :=
  complexToReal fun ab ↦ P ab.1 ab.2

/-- `matrixToReal` is injective. -/
private theorem matrixToReal_injective : Function.Injective (matrixToReal (n := n)) := by
  intro P P' h
  have := congrArg realToComplex h
  simp only [matrixToReal, realToComplex_complexToReal] at this
  funext a b
  exact congrFun this (a, b)

/-- `matrixToReal` is continuous. -/
private theorem continuous_matrixToReal : Continuous (matrixToReal (n := n)) := by
  refine continuous_pi fun ⟨⟨a, b⟩, c⟩ ↦ ?_
  simp only [matrixToReal, complexToReal]
  split_ifs
  · exact Complex.continuous_re.comp ((continuous_apply b).comp (continuous_apply a))
  · exact Complex.continuous_im.comp ((continuous_apply b).comp (continuous_apply a))

/-- The polynomial map `(w, λ) ↦ λ w w^*` in real coordinates. -/
private noncomputable def projPoly : (Fin (n + 1) × Fin (n + 1)) × Fin 2 →
    MvPolynomial (Option (Fin (n + 1) × Fin 2)) ℝ := fun p ↦
  if p.2 = 0 then
    MvPolynomial.X none * (MvPolynomial.X (some (p.1.1, 0)) * MvPolynomial.X (some (p.1.2, 0)) +
      MvPolynomial.X (some (p.1.1, 1)) * MvPolynomial.X (some (p.1.2, 1)))
  else
    MvPolynomial.X none * (MvPolynomial.X (some (p.1.1, 1)) * MvPolynomial.X (some (p.1.2, 0)) -
      MvPolynomial.X (some (p.1.1, 0)) * MvPolynomial.X (some (p.1.2, 1)))

/-- The polynomial `λ ∑_j |w_j|² - 1` in the real coordinates of `(w, λ) ∈ ℂⁿ⁺¹ × ℝ`. -/
private noncomputable def normPoly : MvPolynomial (Option (Fin (n + 1) × Fin 2)) ℝ :=
  MvPolynomial.X none * ∑ j, (MvPolynomial.X (some (j, 0)) ^ 2 +
    MvPolynomial.X (some (j, 1)) ^ 2) - 1

open MMP.Topology in
/-- Where `λ ∑_j |w_j|² = 1`, the polynomial map `projPoly` is the line projection of `w`. -/
private theorem polynomialMap_projPoly {x : Option (Fin (n + 1) × Fin 2) → ℝ}
    (hx : MvPolynomial.eval x normPoly = 0) :
    IsSemialgebraic.polynomialMap projPoly x =
      matrixToReal (lineProjection (realToComplex (x ∘ some))) := by
  set w := realToComplex (x ∘ some)
  have hs : ∑ k, w k * (starRingEnd ℂ) (w k) = ((x none)⁻¹ : ℝ) := by
    rw [sum_mul_conj_eq_ofReal]
    congr 1
    simp only [normPoly, map_sub, map_mul, map_sum, map_add, map_pow, MvPolynomial.eval_X,
      map_one, sub_eq_zero] at hx
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm, ← hx]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [w, realToComplex, Complex.normSq_apply, Function.comp]
    ring
  funext ⟨⟨a, b⟩, c⟩
  simp only [IsSemialgebraic.polynomialMap, matrixToReal, complexToReal, lineProjection, hs]
  fin_cases c
  · simp [projPoly, w, realToComplex, Complex.div_ofReal_re]
    ring
  · simp [projPoly, w, realToComplex, Complex.div_ofReal_im]
    ring

open MMP.Topology in
/-- **Zariski-closed subsets of `ℙⁿ_ℂ` are semialgebraic in the matrix model.** The image in the
real coordinates of the line projections of the complex points of a closed `Z ⊆ ℙⁿ_ℂ` is
semialgebraic: on each standard chart it is the image under the polynomial map `projPoly` of a
real algebraic set. -/
private theorem isSemialgebraic_image_toLineProjection
    [(AlgebraicGeometry.Proj (polyGrading ℂ n)).Over (Spec (.of ℂ))]
    (hP : (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = projToSpecCoeff ℂ n)
    {Z : Set (AlgebraicGeometry.Proj (polyGrading ℂ n))} (hZ : IsClosed Z) :
    IsSemialgebraic ((fun q ↦ matrixToReal (toLineProjection q)) ''
      {q : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n)) |
        q.toHom (IsLocalRing.closedPoint ℂ) ∈ Z}) := by
  choose ι hι Q hQ using fun i ↦ exists_mem_iff_eval_eq_zero hP hZ i
  let F : ∀ i, Option (ι i) → MvPolynomial (Fin (n + 1)) ℂ := fun i o ↦
    o.elim (MvPolynomial.X i - 1) (Q i)
  let S : Fin (n + 1) → Set (Option (Fin (n + 1) × Fin 2) → ℝ) := fun i ↦
    {x | MvPolynomial.eval x normPoly = 0} ∩
      (fun x ↦ x ∘ some) ⁻¹' (realToComplex ⁻¹' {w | ∀ k, MvPolynomial.eval w (F i k) = 0})
  have hS : ∀ i, IsSemialgebraic (S i) := fun i ↦
    (IsSemialgebraic.zero _).inter (IsSemialgebraic.preimage_comp some
      (isSemialgebraic_preimage_complexZeroLocus (F i)))
  have hF : ∀ i (w : Fin (n + 1) → ℂ), (∀ k, MvPolynomial.eval w (F i k) = 0) ↔
      w i = 1 ∧ ∀ k, MvPolynomial.eval w (Q i k) = 0 := by
    intro i w
    simp only [F, Option.forall, Option.elim, map_sub, MvPolynomial.eval_X, map_one, sub_eq_zero]
  convert IsSemialgebraic.iUnion fun i ↦ (hS i).image_polynomialMap projPoly using 1
  ext P
  simp only [mem_image, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro ⟨q, hqZ, rfl⟩
    obtain ⟨i, hq⟩ := exists_top_le_preimage_projectiveSpaceStdChart q
    set w := fun j ↦ eval q hq (projectiveSpaceStdCoord ℂ n i j)
    have hwi : w i = 1 := eval_projectiveSpaceStdCoord_self hq
    have hpos : 0 < ∑ k, Complex.normSq (w k) :=
      lt_of_lt_of_le (by simp [hwi]) (Finset.single_le_sum (fun k _ ↦ Complex.normSq_nonneg (w k))
        (Finset.mem_univ i))
    let x : Option (Fin (n + 1) × Fin 2) → ℝ := fun o ↦
      o.elim (∑ k, Complex.normSq (w k))⁻¹ (complexToReal w)
    have hxw : realToComplex (x ∘ some) = w := realToComplex_complexToReal w
    have hxn : MvPolynomial.eval x normPoly = 0 := by
      simp only [normPoly, map_sub, map_mul, map_sum, map_add, map_pow, MvPolynomial.eval_X,
        map_one, sub_eq_zero]
      have : ∑ j, (x (some (j, 0)) ^ 2 + x (some (j, 1)) ^ 2) = ∑ k, Complex.normSq (w k) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp [x, complexToReal, Complex.normSq_apply]
        ring
      rw [this]
      exact inv_mul_cancel₀ hpos.ne'
    refine ⟨i, x, ⟨hxn, ?_⟩, ?_⟩
    · simp only [mem_preimage, mem_setOf_eq, hxw]
      exact (hF i w).2 ⟨hwi, (hQ i q hq).1 hqZ⟩
    · rw [polynomialMap_projPoly hxn, hxw, toLineProjection_eq hq]
  · rintro ⟨i, x, ⟨hxn, hxF⟩, rfl⟩
    simp only [mem_preimage, mem_setOf_eq] at hxF
    obtain ⟨hwi, hwQ⟩ := (hF i _).1 hxF
    obtain ⟨q, hq, hqw⟩ := exists_eval_projectiveSpaceStdCoord_eq hP i hwi
    have hcoord : (fun j ↦ eval q hq (projectiveSpaceStdCoord ℂ n i j)) =
        realToComplex (x ∘ some) := funext hqw
    refine ⟨q, (hQ i q hq).2 (by rwa [hcoord]), ?_⟩
    rw [polynomialMap_projPoly hxn, toLineProjection_eq hq, hcoord]

open MMP.Topology MMP.Analytic in
/-- **A semialgebraic model of `X^an`.** For `X` projective over `ℂ`, `X^an` has a closed
embedding into a real vector space with compact semialgebraic image, carrying the trace of every
Zariski-closed `D ⊆ X` to a semialgebraic set. -/
private theorem exists_isClosedEmbedding_isSemialgebraic {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : IsProjective sX) (D : TopologicalSpace.Closeds X) :
    ∃ (ω : Type) (_ : Fintype ω) (Ψ : ComplexPoints sX → ω → ℝ), IsClosedEmbedding Ψ ∧
      IsCompact (range Ψ) ∧ IsSemialgebraic (range Ψ) ∧
      IsSemialgebraic (Ψ '' (ComplexPoints.toScheme ⁻¹' (D : Set X))) := by
  obtain ⟨n, i, hi, hif⟩ := isProjectiveMorphism_of_isProjective_of_isAffine sX hX
  let e := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ n
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ n)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ n⟩
  let j := i ≫ e.iso.hom
  have hj : j ≫ (AlgebraicGeometry.Proj (polyGrading ℂ n) ↘ Spec (.of ℂ)) = sX := by
    change (i ≫ e.iso.hom) ≫ projToSpecCoeff ℂ n = sX
    rw [Category.assoc, projToSpecCoeff, e.toBase]
    exact hif
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : j.IsOver (Spec (.of ℂ)) := ⟨hj⟩
  let φ : ComplexPoints sX ≃ₜ UnderlyingSpace ℂ X := ComplexPoints.homeomorphUnderlyingSpace
  let f : UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n)) → _ :=
    fun q ↦ matrixToReal (toLineProjection q)
  let Ψ : ComplexPoints sX → (Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ := fun x ↦ f (map j (φ x))
  have hcont : Continuous Ψ := continuous_matrixToReal.comp (continuous_toLineProjection.comp
    ((map j).continuous.comp φ.continuous))
  have hinj : Function.Injective Ψ := matrixToReal_injective.comp
    ((injective_toLineProjection rfl).comp
    ((isClosedEmbedding_map_of_isClosedImmersion j).injective.comp φ.injective))
  haveI : CompactSpace (UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ n))) :=
    compactSpace_projectiveSpace n rfl
  haveI : CompactSpace (UnderlyingSpace ℂ X) :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) j).compactSpace
  haveI : CompactSpace (ComplexPoints sX) := φ.symm.compactSpace
  have hjc : IsClosedEmbedding j := j.isClosedEmbedding
  have hrange : range (map (K := ℂ) j) =
      {q | q.toHom (IsLocalRing.closedPoint ℂ) ∈ range j} := range_mapFun_of_isClosedImmersion j
  have hpt : ∀ x : ComplexPoints sX, (φ x).toHom (IsLocalRing.closedPoint ℂ) = x.toScheme :=
    fun x ↦ congrArg x.hom (Subsingleton.elim _ _)
  refine ⟨_, inferInstance, Ψ, hcont.isClosedEmbedding hinj, isCompact_range hcont, ?_, ?_⟩
  · have : range Ψ = f '' {q | q.toHom (IsLocalRing.closedPoint ℂ) ∈ range j} := by
      rw [← hrange, ← range_comp]
      exact φ.surjective.range_comp (f ∘ map j)
    rw [this]
    exact isSemialgebraic_image_toLineProjection rfl hjc.isClosed_range
  · have : Ψ '' (ComplexPoints.toScheme ⁻¹' (D : Set X)) =
        f '' {q | q.toHom (IsLocalRing.closedPoint ℂ) ∈ j '' (D : Set X)} := by
      rw [show Ψ = f ∘ (fun x ↦ map j (φ x)) from rfl, image_comp]
      congr 1
      ext q
      simp only [mem_image, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨_, hx, ?_⟩
        rw [← hpt x]
        change _ = (mapFun j (φ x)).toHom _
        rw [toHom_mapFun]
        rfl
      · rintro ⟨z, hz, hzq⟩
        obtain ⟨p, rfl⟩ : q ∈ range (map (K := ℂ) j) := by rw [hrange]; exact ⟨z, hzq⟩
        refine ⟨φ.symm p, ?_, by simp⟩
        have h1 : (mapFun j p).toHom (IsLocalRing.closedPoint ℂ) =
            j (p.toHom (IsLocalRing.closedPoint ℂ)) := by rw [toHom_mapFun]; rfl
        have h2 : p.toHom (IsLocalRing.closedPoint ℂ) = z :=
          hjc.injective (h1.symm.trans hzq.symm)
        rw [← hpt, φ.apply_symm_apply, h2]
        exact hz
    rw [this]
    exact isSemialgebraic_image_toLineProjection rfl (hjc.isClosedMap _ D.isClosed)

end Model

end MMP.Proof_lem_mmp_projective_algebraic_retracting_neighbourhoods

namespace MMP.Analytic

open MMP.Proof_lem_mmp_projective_algebraic_retracting_neighbourhoods

/-- **Retracting neighbourhoods of algebraic subsets.** Let `X` be a projective scheme over `ℂ`
and `D ⊆ X` a Zariski-closed subset, with analytic trace `D^an ⊆ X^an`. Every open neighbourhood
`W` of `D^an` in `X^an` contains an open neighbourhood `N` of `D^an` which strongly deformation
retracts onto `D^an`: there is a continuous `r : N → D^an` such that the identity of `N` is
homotopic, relative to `D^an`, to `r` followed by the inclusion `D^an ⊆ N`. -/
@[mmp "lem_mmp_projective_algebraic_retracting_neighbourhoods"]
public theorem exists_homotopicRel_retraction_of_isProjective
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (hX : IsProjective sX) (D : Closeds X)
    (W : Set (ComplexPoints sX)) (hW : IsOpen W)
    (hDW : ComplexPoints.toScheme ⁻¹' (D : Set X) ⊆ W) :
    ∃ N : Set (ComplexPoints sX), IsOpen N ∧ N ⊆ W ∧
      ∃ hDN : ComplexPoints.toScheme ⁻¹' (D : Set X) ⊆ N,
      ∃ r : C(N, ComplexPoints.toScheme ⁻¹' (D : Set X)),
        (ContinuousMap.id N).HomotopicRel
          ((⟨Set.inclusion hDN, continuous_inclusion hDN⟩ :
            C(ComplexPoints.toScheme ⁻¹' (D : Set X), N)).comp r)
          (Set.range (Set.inclusion hDN)) := by
  obtain ⟨ω, _, Ψ, hΨ, hSc, hSs, hAs⟩ := exists_isClosedEmbedding_isSemialgebraic sX hX D
  set Dan := ComplexPoints.toScheme ⁻¹' (D : Set X)
  have hAc : IsClosed (Ψ '' Dan) :=
    hΨ.isClosedMap _ (D.isClosed.preimage ComplexPoints.continuous_toScheme)
  have hN := (hasNestedDeformation_of_isSemialgebraic hSc hSs hAs hAc (image_subset_range _ _))
    |>.preimage hΨ.isEmbedding.toHomeomorph
  have hset : hΨ.isEmbedding.toHomeomorph ⁻¹' {x : range Ψ | (x : ω → ℝ) ∈ Ψ '' Dan} = Dan :=
    Set.ext fun _ ↦ hΨ.injective.mem_set_image
  rw [hset] at hN
  exact hN.exists_homotopicRel_retraction hW hDW

end MMP.Analytic

namespace MMP.Proof_lem_mmp_projective_algebraic_supported_duality

open MMP MMP.UnderlyingSpace MMP.FundamentalClass
open MMP.borelMooreHomology MMP.BorelMooreCross

/-- **Duality maps transported along a homeomorphism.** For `φ : M ≃ₜ M'` and closed `A ⊆ M`, if
the duality map `c ↦ c ∩ μ` on `H^{n-k}(M, M - A)` is bijective and the pullback `(φ⁻¹)^*` onto
`H^{n-k}(M', M' - φ(A))` is surjective, then the duality map of `φ(A)` with `φ_* μ` is
bijective. -/
private lemma bijective_dualityMap_pushforward_homeomorph {R : Type} [CommRing R]
    {M M' : TopCat.{0}} (φ : M ≃ₜ M') {A : Set M} (hA : IsClosed A)
    (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (φ.symm ⁻¹' A)) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) M n) (k : ℤ)
    (hP : Function.Surjective (cohomologyWithSupports.pullback R (ModuleCat.of R R)
      (TopCat.ofHom (φ.symm : C(M', M))) A (n - k)).hom)
    (h : Function.Bijective (dualityMap R hA hAd μ k)) :
    Function.Bijective (dualityMap R (hA.preimage φ.symm.continuous) hA'd
      ((pushforward R (ModuleCat.of R R) (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap n).hom μ)
      k) := by
  have hQ := bijective_pushforward_homeomorph R (Y := TopCat.of (φ.symm ⁻¹' A)) (Y' := TopCat.of A)
    (preimageHomeomorph φ.symm A) k
  rw [show ⇑(dualityMap R hA hAd μ k) = _ ∘ _ ∘ _ from
    funext fun c ↦ (pushforward_dualityMap_pullback_symm R φ hA hAd hA'd μ k c).symm] at h
  replace h := (hQ.of_comp_iff' _).1 h
  exact (Function.Bijective.of_comp_iff _ ⟨.of_comp h.1, hP⟩).1 h

/-- **Fundamental classes only see the orientation of the basis.** If `b'` has the orientation
of `b` (`0 < det_b b'`), a fundamental class for `b` is one for `b'`. -/
private lemma isFundamentalClass_of_det_pos {R : Type} [CommRing R] {H : Type*} [AddCommGroup H]
    [Module ℝ H] [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] {M : Type}
    [TopologicalSpace M] [T2Space M] [ChartedSpace H M] {n : ℕ}
    {b b' : Module.Basis (Fin n) ℝ H} (hbb' : 0 < b.det b')
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) n}
    (hμ : IsFundamentalClass R b μ) : IsFundamentalClass R b' μ := by
  intro e he x v hv hvt
  refine hμ e he x v ⟨hv.1, ?_⟩ hvt
  have hmul : ∀ w : Fin n → H, b.det w = b.det b' * b'.det w := fun w ↦ by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  rw [hmul]
  exact mul_pos hbb' hv.2

/-- The fundamental class of a complex manifold modelled on `ℂᵈ` for the basis
`e₁, i e₁, …, e_d, i e_d` is its fundamental class for `complexOrientationBasisOf ℂᵈ`, in degree
`2 dim ℂᵈ = 2 d`. -/
private lemma isFundamentalClass_complexOrientationBasisOf {R : Type} [CommRing R] {d : ℕ}
    {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℂ (Fin d)) M]
    {μ : borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) (2 * d : ℕ)}
    (hμ : IsFundamentalClass R (euclideanComplexOrientationBasis d) μ)
    (h : 2 * d = 2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin d))) :
    IsFundamentalClass R (complexOrientationBasisOf (EuclideanSpace ℂ (Fin d)))
      (congrDegree R _ (congrArg Nat.cast h) μ) := by
  refine isFundamentalClass_of_det_pos ?_ (hμ.congrDegree_reindex h)
  have hd : d = Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) := finrank_euclideanSpace_fin.symm
  have hc : euclideanComplexOrientationBasis d =
      complexRealBasis (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin d → ℂ))) := by
    rw [complexRealBasis, Module.Basis.equivFun_ofEquivFun]
    rfl
  rw [hc, ← complexRealBasis_reindex_finCongr hd]
  exact complexRealBasis_det_pos (Module.finBasis ℂ _) _ (L := LinearMap.id) Function.injective_id

end MMP.Proof_lem_mmp_projective_algebraic_supported_duality

namespace MMP.Analytic

open MMP MMP.UnderlyingSpace MMP.FundamentalClass
open MMP.borelMooreHomology MMP.BorelMooreCross
open MMP.Proof_lem_mmp_projective_algebraic_supported_duality
open scoped Manifold

/-- **Supported duality: bijectivity of the cap product.** Let `Y`
be a non-singular projective complex variety of dimension `d` with fundamental class
`μ ∈ H_{2d} Y(ℂ)` (the complex orientation), and `D ⊆ Y` Zariski closed. For every `k`, the cap
product with `μ`, `H^{2d-k}(Y(ℂ), Y(ℂ) - D(ℂ); ℚ) → H_k(D(ℂ); ℚ)`, is bijective. -/
public theorem bijective_dualityMap_of_isVarietyFundamentalClass
    {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] [IsIntegral Y]
    (hY : IsProjective (Y ↘ Spec (.of ℂ))) {d : ℕ} [SmoothOfRelativeDimension d (Y ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y)) (2 * d : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Y) d) μ)
    (D : Closeds Y) (k : ℤ) :
    Function.Bijective
      (borelMooreHomology.dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ Y))
        (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver Y D)
        μ k) := by
  letI := regularChartedSpace (𝕜 := ℂ)
    (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Y) d)
  have hU := regularOpens_eq_top_of_smoothOfRelativeDimension (X := Y) d
  -- `φ : Y_reg(ℂ) ≃ₜ Y(ℂ)`, the inclusion of the regular part, which is everything.
  let φ : (regularOpens ℂ Y : Opens (UnderlyingSpace ℂ Y)) ≃ₜ UnderlyingSpace ℂ Y :=
    (Homeomorph.setCongr (congrArg SetLike.coe hU)).trans (Homeomorph.Set.univ _)
  let M : TopCat.{0} := TopCat.of (regularOpens ℂ Y : Opens (UnderlyingSpace ℂ Y))
  let M' : TopCat.{0} := TopCat.of (UnderlyingSpace ℂ Y)
  let X : Set M' := pointsOver D
  have hXd : HasProperNeighbourhoodDeformations X :=
    hasProperNeighbourhoodDeformations_pointsOver Y D
  let A : Set M := φ ⁻¹' X
  have hA : IsClosed A := (isClosed_pointsOver D.isClosed).preimage φ.continuous
  let μr := (restrict ℚ (ModuleCat.of ℚ ℚ) (regularOpens ℂ Y : Opens M') (2 * d : ℕ)).hom μ
  have e : cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (𝟙 M') X ((2 * d : ℕ) - k) = _ :=
    cohomologyWithSupports.pullback_comp ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (φ.symm : C(M', M))) (TopCat.ofHom (φ : C(M, M'))) X _
  rw [cohomologyWithSupports.pullback_id] at e
  have hpush : (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (φ : C(M, M'))) φ.isProperMap
      (2 * d : ℕ)).hom μr = μ :=
    pushforward_inclHom_restrict_of_eq_top ℚ hU _ _ μ
  have hP : Function.Surjective (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (φ.symm : C(M', M))) A ((2 * d : ℕ) - k)).hom :=
    fun c ↦ ⟨_, (congrArg (fun F ↦ F.hom c) e).symm⟩
  have hG := bijective_dualityMap_of_isFundamentalClass
      (M := (regularOpens ℂ Y : Opens (UnderlyingSpace ℂ Y)))
      (euclideanComplexOrientationBasis d) μr hμ hA (hXd.preimage_homeomorph φ) k
  rw [← hpush]
  exact bijective_dualityMap_pushforward_homeomorph (M := M) (M' := M') φ hA _ hXd μr k hP hG

/-- **Supported duality for an algebraic subset of a smooth projective complex variety.** Let `Y`
be a non-singular projective complex variety of dimension `d` with fundamental class
`μ ∈ H_{2d} Y(ℂ)` (the complex orientation), and `D ⊆ Y` Zariski closed, with trace
`D(ℂ) ⊆ Y(ℂ)`. Then:
1. for every `k`, the cap product with `μ`, `H^{2d-k}(Y(ℂ), Y(ℂ) - D(ℂ); ℚ) → H_k(D(ℂ); ℚ)`, is
  bijective;
2. it is natural: for Zariski-closed `D ⊆ D'` it commutes with the forgetful map
  `H^*_D → H^*_{D'}` and the push-forward `H_* D(ℂ) → H_* D'(ℂ)`; and for every open
  `U ⊆ Y(ℂ)` it commutes with the restrictions `c ↦ c|_U`, `μ ↦ μ|_U` and
  `H_* D(ℂ) → H_*(D(ℂ) ∩ U)`;
3. on every open `U ⊆ Y(ℂ) = Y_reg(ℂ)` where `D(ℂ) ∩ U` is a closed complex submanifold `Z` with a
  tubular (normal disk) neighbourhood, it carries the orientation class `u_{Z,U}` to the
  fundamental class of `Z`: it is the orientation isomorphism on the normal disks;
4. the induced map to `H^k D(ℂ)` is restriction of supported classes: for every neighbourhood `W`
  of `D(ℂ)` retracting onto `D(ℂ)` by `r` homotopic to the identity of `W`, the image of
  `c ∈ H^k(Y(ℂ), Y(ℂ) - D(ℂ))` in `H^k W` is `r^*(c|_{D(ℂ)})`. -/
@[mmp "lem_mmp_projective_algebraic_supported_duality"]
public theorem bijective_dualityMap_natural_of_isVarietyFundamentalClass
    {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] [IsIntegral Y]
    (hY : IsProjective (Y ↘ Spec (.of ℂ))) {d : ℕ} [SmoothOfRelativeDimension d (Y ↘ Spec (.of ℂ))]
    {μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y)) (2 * d : ℕ)}
    (hμ : IsVarietyFundamentalClass ℚ
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Y) d) μ)
    (D : Closeds Y) :
    -- (1) the isomorphism
    (∀ k : ℤ, Function.Bijective
      (borelMooreHomology.dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ Y))
        (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver Y D)
        μ k)) ∧
    -- (2a) naturality in the support
    (∀ (D' : Closeds Y) (hDD' : (D : Set Y) ⊆ D') (k : ℤ)
        (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y))
          (pointsOver (K := ℂ) (D : Set Y)) ((2 * d : ℕ) - k)),
        (pushforward ℚ (ModuleCat.of ℚ ℚ) (subsetInclusionOfSubset (pointsOver_mono hDD'))
            (isProperMap_subsetInclusionOfSubset (isClosed_pointsOver D.isClosed)
              (pointsOver_mono hDD')) k).hom
          (borelMooreHomology.dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ Y))
            (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver Y D)
            μ k c) =
        borelMooreHomology.dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ Y))
            (isClosed_pointsOver D'.isClosed) (hasProperNeighbourhoodDeformations_pointsOver Y D')
            μ k
          ((cohomologyWithSupports.forget ℚ (ModuleCat.of ℚ ℚ) _ (pointsOver_mono hDD') _).hom
            c)) ∧
    -- (2b) naturality under restriction to open subsets
    (∀ (U : Opens (TopCat.of (UnderlyingSpace ℂ Y)))
        (hUd : HasProperNeighbourhoodDeformations
          ((inclHom U).hom ⁻¹' pointsOver (K := ℂ) (D : Set Y))) (k : ℤ)
        (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y))
          (pointsOver (K := ℂ) (D : Set Y)) ((2 * d : ℕ) - k)),
        (pushforward ℚ (ModuleCat.of ℚ ℚ) (opensInterMap U (pointsOver (K := ℂ) (D : Set Y)))
            (isProperMap_opensInterMap U _) k).hom
          ((restrict ℚ (ModuleCat.of ℚ ℚ) (opensInter U (pointsOver (K := ℂ) (D : Set Y))) k).hom
            (borelMooreHomology.dualityMap ℚ (M := TopCat.of (UnderlyingSpace ℂ Y))
              (isClosed_pointsOver D.isClosed) (hasProperNeighbourhoodDeformations_pointsOver Y D)
              μ k c)) =
        borelMooreHomology.dualityMap ℚ (M := TopCat.of U)
            ((isClosed_pointsOver D.isClosed).preimage (inclHom U).hom.continuous) hUd
            ((restrict ℚ (ModuleCat.of ℚ ℚ) U (2 * d : ℕ)).hom μ) k
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (inclHom U) _ _).hom c)) ∧
    -- (3) on a smooth transverse normal disk it is the orientation isomorphism
    (letI := regularChartedSpace (𝕜 := ℂ)
        (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Y) d)
      ∀ (U : Opens (regularOpens ℂ Y : Opens (TopCat.of (UnderlyingSpace ℂ Y))))
        (Z : Set (TopCat.of U)),
        Z = (fun x : U ↦ (x.1.1 : UnderlyingSpace ℂ Y)) ⁻¹' pointsOver (K := ℂ) (D : Set Y) →
      ∀ {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
        [ChartedSpace E' Z], IsComplexSubmanifold (EuclideanSpace ℂ (Fin d)) E' Z →
      ∀ (hZc : IsClosed Z) (hZd : HasProperNeighbourhoodDeformations Z)
        {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
        {N : Z → Type} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)]
        [∀ x, TopologicalSpace (N x)] [TopologicalSpace (Bundle.TotalSpace F N)]
        [FiberBundle F N] [_root_.VectorBundle ℂ F N] (φ : TubularNeighbourhood F N)
        (u : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of U) Z
          (2 * Module.finrank ℂ F : ℕ)),
        IsOrientationClass (EuclideanSpace ℂ (Fin d)) ℚ φ u →
      ∀ (hdeg : ((2 * d : ℕ) : ℤ) - (2 * Module.finrank ℂ F : ℕ) = (2 * Module.finrank ℂ E' : ℕ)),
        IsFundamentalClass (M := Z) ℚ (complexOrientationBasisOf E')
          (congrDegree ℚ _ hdeg
            (capProductSupport ℚ (TopCat.of U) hZc hZd (2 * Module.finrank ℂ F : ℕ)
              (2 * d : ℕ) u
              ((restrict ℚ (ModuleCat.of ℚ ℚ)
                  (Y := TopCat.of (regularOpens ℂ Y : Opens (TopCat.of (UnderlyingSpace ℂ Y)))) U
                  (2 * d : ℕ)).hom
                ((restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ Y))
                  (regularOpens ℂ Y : Opens (TopCat.of (UnderlyingSpace ℂ Y)))
                  (2 * d : ℕ)).hom μ))))) ∧
    -- (4) the induced map to `H^k D` is restriction of supported classes
    (∀ (W : Set (UnderlyingSpace ℂ Y)) (hDW : pointsOver (K := ℂ) (D : Set Y) ⊆ W)
        (r : C(W, pointsOver (K := ℂ) (D : Set Y))),
        (ContinuousMap.id W).Homotopic
          ((⟨Set.inclusion hDW, continuous_inclusion hDW⟩ :
            C(pointsOver (K := ℂ) (D : Set Y), W)).comp r) →
      ∀ (k : ℤ) (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.of (UnderlyingSpace ℂ Y)) (pointsOver (K := ℂ) (D : Set Y)) k),
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom r)
            (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ Y))
              (pointsOver (K := ℂ) (D : Set Y)) ⁻¹' Set.univ) k).hom
          ((cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
              (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ Y))
                (pointsOver (K := ℂ) (D : Set Y))) Set.univ k).hom
            ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ k).hom c)) =
        (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
            (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ Y)) W) Set.univ k).hom
          ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ k).hom c)) := by
  let M' : TopCat.{0} := TopCat.of (UnderlyingSpace ℂ Y)
  let X : Set M' := pointsOver (K := ℂ) (D : Set Y)
  refine ⟨fun k ↦ bijective_dualityMap_of_isVarietyFundamentalClass hY hμ D k, ?_, ?_, ?_, ?_⟩
  · -- (2a) forgetting supports, `lem_ext_c19_cap_forget_support`
    intro D' hDD' k c
    rw [dualityMap_apply, dualityMap_apply, MMP.borelMooreHomology.pushforward_congrDegree,
      pushforward_subsetInclusionOfSubset_capProductSupport]
  · -- (2b) restriction to open subsets, `lem_ext_c19_cap_restriction`
    intro U hUd k c
    rw [dualityMap_apply, dualityMap_apply, ← MMP.congrDegree_restrict,
      MMP.borelMooreHomology.pushforward_congrDegree,
      pushforward_opensInterMap_restrict_capProductSupport ℚ M' U (isClosed_pointsOver D.isClosed)
        (hasProperNeighbourhoodDeformations_pointsOver Y D) hUd, capProductSupportPullback_apply]
    rfl
  · -- (3) `u_{Z,U} ∩ μ_U = μ_Z`, `lem_ext_c19_orientation_class_cap_fundamental`
    letI := regularChartedSpace (𝕜 := ℂ)
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Y) d)
    intro U Z _hZ E' _ _ _ _ hZm hZc hZd F _ _ _ N _ _ _ _ _ _ φ u hu hdeg
    haveI := isManifold_regularOpens (𝕜 := ℂ) (X := Y)
      (natCast_eq_dimension_of_isVariety (K := ℂ) (Y := Y) d)
    haveI : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin d)) 1 (regularOpens ℂ Y) :=
      IsManifold.of_le le_top
    have hμU : IsFundamentalClass ℚ (euclideanComplexOrientationBasis d)
        ((restrict ℚ (ModuleCat.of ℚ ℚ)
            (Y := TopCat.of (regularOpens ℂ Y : Opens (TopCat.of (UnderlyingSpace ℂ Y)))) U
            (2 * d : ℕ)).hom
          ((restrict ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (UnderlyingSpace ℂ Y))
            (regularOpens ℂ Y : Opens (TopCat.of (UnderlyingSpace ℂ Y))) (2 * d : ℕ)).hom μ)) :=
      IsFundamentalClass.restrict hμ U
    have hE : 2 * d = 2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) := by
      rw [finrank_euclideanSpace_fin]
    have hμP := isFundamentalClass_complexOrientationBasisOf hμU hE
    have hdeg' : ((2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℤ) -
        (2 * Module.finrank ℂ F : ℕ) = (2 * Module.finrank ℂ E' : ℕ) := by
      rwa [← hE]
    have key := IsOrientationClass.isFundamentalClass_capProductSupport (P := TopCat.of U) ℚ
      hZm hZc hZd hu hμP hdeg'
    rwa [capProductSupport_congrDegree_right,
      MMP.borelMooreHomology.congrDegree_congrDegree] at key
  · -- (4) restriction through a retracting neighbourhood, by homotopy invariance
    intro W hDW r hr k c
    obtain ⟨G⟩ := hr
    let H : TopCat.Homotopy (TopCat.ofHom r ≫ subspaceInclusion M' X) (subspaceInclusion M' W) :=
      (((ContinuousMap.Homotopy.refl (subspaceInclusion M' W).hom).comp G).symm).cast
        (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun _ ↦ rfl)
    have e := cohomologyWithSupports.pullback_comp ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom r)
      (subspaceInclusion M' X) Set.univ k
    have e₂ : cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom r ≫ subspaceInclusion M' X) Set.univ k =
        cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion M' W)
          Set.univ k :=
      relativeSingularCohomology.map_eq_of_homotopy ℚ H
        (by intro _ hy; exact (hy trivial).elim) (by intro _ hy; exact (hy trivial).elim)
        (by intro _ hy; exact (hy trivial).elim) k
    exact congrArg (fun f ↦ f.hom ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ)
      M' X k).hom c)) (e.symm.trans e₂)

end MMP.Analytic
