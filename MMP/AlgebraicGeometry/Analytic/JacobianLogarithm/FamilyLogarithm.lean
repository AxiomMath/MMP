module

public import MMP.AlgebraicGeometry.Analytic.JacobianLogarithm.TransitionLogDeriv
import MMP.AlgebraicGeometry.Analytic.CornerPresentation

/-!
# The holomorphic logarithm of the family of slice classes

Let `C` be a smooth projective connected curve over `ℂ`, `J` a scheme over `ℂ` and `M` an
invertible module on `C ×_ℂ J`. Integrating the decomposed logarithmic derivatives along segments
in étale coordinates expresses the transition cocycle of `M|_{C × {t}}` as that of
`M|_{C × {e}}` times the exponential of a combination of fixed cochains with holomorphic
coefficients, up to a coboundary of holomorphic units. The Čech-to-derived comparison then gives
a logarithm of the family of slice classes in `H¹(C^an, 𝒪)`, holomorphic in `t` and linear in the
coefficients.

## Main results

* `MMP.JacobianLogarithm.Fam.exists_etaleCoordinateChart_sliceClass_eq`: logarithms of the family
  of slice classes.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][griffithsharris1978], Ch. 2 §6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace Filter Topology
open MMP.Analytic MMP.Analytic.Analytification MMP.Analytic.ComplexPoints

namespace MMP.JacobianLogarithm

attribute [local instance] hasExt_of_enoughInjectives
attribute [local implicit_reducible] TopCat.Sheaf
attribute [local instance] CategoryTheory.Hom.group

section FamilyLogarithm

open Limits
open scoped Manifold ContDiff Interval
open KaehlerDifferential TensorProduct MeasureTheory Set intervalIntegral

namespace Fam

open Stacks.CategoryTheory.CechComplex

section Final

open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

variable {C J : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) (sJ : J ⟶ Spec (.of ℂ))

section EvalE

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}

/-- The value of a regular function on `U` at a `ℂ`-point, extended by `0` off `U(ℂ)`. -/
noncomputable def evalE (U : X.Opens) (g : Γ(X, U)) (y : ComplexPoints sX) : ℂ := by
  classical
  exact if h : y ∈ chart U then eval U g ⟨y, h⟩ else 0

/-- On `U(ℂ)`, `evalE U g` agrees with the value of `g`. -/
theorem evalE_of_mem {U : X.Opens} (g : Γ(X, U)) {y : ComplexPoints sX} (h : y ∈ chart U) :
    evalE U g y = eval U g ⟨y, h⟩ := by
  rw [evalE, dif_pos h]

/-- `evalE` is compatible with restriction of regular functions on `V(ℂ)`. -/
theorem evalE_res {U V : X.Opens} (hVU : V ≤ U) (g : Γ(X, U)) {y : ComplexPoints sX}
    (h : y ∈ chart V) : evalE V (X.presheaf.map (homOfLE hVU).op g) y = evalE U g y := by
  rw [evalE_of_mem _ h, evalE_of_mem _ (chart_mono hVU h), ← evalHom_apply, ← evalHom_apply,
    evalHom_res hVU ⟨y, h⟩]

/-- **Regular functions are continuous on `U(ℂ)`.** -/
theorem continuousOn_evalE [LocallyOfFiniteType sX] (U : X.Opens) (g : Γ(X, U)) :
    ContinuousOn (evalE (sX := sX) U g) (chart U) := by
  intro y hy
  obtain ⟨V, hV, hyV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (mem_chart_iff.1 hy)
  obtain ⟨c, hc⟩ := Chart.exists_eq (sX := sX) hV
  have hVo : IsOpen (chart (sX := sX) V) := isOpen_chart sX V
  have hcont : ContinuousOn (evalE (sX := sX) V (X.presheaf.map (homOfLE hVU).op g))
      (chart V) := by
    rw [continuousOn_iff_continuous_restrict]
    have htop := (Chart.isOpen_chart_and_isEmbedding_coords c).2.1
    subst hc
    have h1 : (fun z : chart (sX := sX) c.U =>
        evalE (sX := sX) c.U (X.presheaf.map (homOfLE hVU).op g) z.1) =
        eval c.U (X.presheaf.map (homOfLE hVU).op g) := by
      funext z
      exact evalE_of_mem _ z.2
    change Continuous (fun z : chart (sX := sX) c.U =>
        evalE (sX := sX) c.U (X.presheaf.map (homOfLE hVU).op g) z.1)
    rw [h1]
    have := continuous_eval (sX := sX) c.U (X.presheaf.map (homOfLE hVU).op g)
    rwa [← htop] at this
  have hat : ContinuousAt (evalE (sX := sX) U g) y := by
    have h2 := (hcont y (mem_chart_iff.2 hyV)).continuousAt (hVo.mem_nhds (mem_chart_iff.2 hyV))
    refine h2.congr ?_
    filter_upwards [hVo.mem_nhds (mem_chart_iff.2 hyV)] with z hz
    exact evalE_res hVU g hz
  exact hat.continuousWithinAt

end EvalE

/-- **Separable form of a regular function on a basic open of a box.** A regular function `g` on
`D(G) ⊆ A × V` is, at the `ℂ`-points, a quotient `(∑ p₁ ⊗ q₁) / (∑ p₂ ⊗ q₂)ᵏ` with
`G = ∑ p₂ ⊗ q₂`. -/
theorem exists_sep_basicOpen {A : C.Opens} {V : J.Opens} (hA : IsAffineOpen A)
    (hV : IsAffineOpen V) (G : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V))
    (g : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) :
    ∃ (k m₁ m₂ : ℕ) (p₁ : Fin m₁ → Γ(C, A)) (q₁ : Fin m₁ → Γ(J, V)) (p₂ : Fin m₂ → Γ(C, A))
      (q₂ : Fin m₂ → Γ(J, V)), ∀ (x : ComplexPoints f) (t : ComplexPoints sJ),
      (pair x t ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G) ↔
        x ∈ chart A ∧ t ∈ chart V ∧ ∑ l, evalE A (p₂ l) x * evalE V (q₂ l) t ≠ 0) ∧
      (pair x t ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G) →
        evalE _ g (pair x t) = (∑ l, evalE A (p₁ l) x * evalE V (q₁ l) t) /
          (∑ l, evalE A (p₂ l) x * evalE V (q₂ l) t) ^ k) := by
  classical
  have hB : IsAffineOpen (box (f := f) (sJ := sJ) A V) := isAffineOpen_box hA hV
  let ρ : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V) →+*
      Γ(pullback f sJ, (pullback f sJ).basicOpen G) :=
    ((pullback f sJ).presheaf.map (homOfLE ((pullback f sJ).basicOpen_le G)).op).hom
  letI : Algebra Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)
      Γ(pullback f sJ, (pullback f sJ).basicOpen G) := ρ.toAlgebra
  haveI : IsLocalization.Away G Γ(pullback f sJ, (pullback f sJ).basicOpen G) :=
    hB.isLocalization_basicOpen G
  obtain ⟨⟨a, sG⟩, hak⟩ := IsLocalization.mk'_surjective (Submonoid.powers G) g
  obtain ⟨k, hk⟩ := sG.2
  have hau : g * ρ G ^ k = ρ a := by
    have := IsLocalization.mk'_spec (S := Γ(pullback f sJ, (pullback f sJ).basicOpen G)) a sG
    have hak' : IsLocalization.mk' Γ(pullback f sJ, (pullback f sJ).basicOpen G) a sG = g := hak
    rw [hak'] at this
    have hk' : G ^ k = (sG : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V)) := hk
    rwa [← map_pow, hk']
  obtain ⟨m₁, p₁, q₁, ha⟩ := exists_sum_box hA hV a
  obtain ⟨m₂, p₂, q₂, hG⟩ := exists_sum_box hA hV G
  refine ⟨k, m₁, m₂, p₁, q₁, p₂, q₂, fun x t => ?_⟩
  have hsum : ∀ (hx : x ∈ chart A) (ht : t ∈ chart V) {m : ℕ} (p : Fin m → Γ(C, A))
      (q : Fin m → Γ(J, V)), ∑ l, evalE A (p l) x * evalE V (q l) t =
        ∑ l, eval A (p l) ⟨x, hx⟩ * eval V (q l) ⟨t, ht⟩ := by
    intro hx ht m p q
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [evalE_of_mem _ hx, evalE_of_mem _ ht]
  have hGv : ∀ (hx : x ∈ chart A) (ht : t ∈ chart V),
      eval _ G ⟨pair x t, mem_chart_box hx ht⟩ =
        ∑ l, evalE A (p₂ l) x * evalE V (q₂ l) t := by
    intro hx ht
    rw [hsum hx ht, ← eval_sum_box p₂ q₂ hx ht, ← hG]
  have hav : ∀ (hx : x ∈ chart A) (ht : t ∈ chart V),
      eval _ a ⟨pair x t, mem_chart_box hx ht⟩ =
        ∑ l, evalE A (p₁ l) x * evalE V (q₁ l) t := by
    intro hx ht
    rw [hsum hx ht, ← eval_sum_box p₁ q₁ hx ht, ← ha]
  have hmem : pair x t ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G) ↔
      x ∈ chart A ∧ t ∈ chart V ∧ ∑ l, evalE A (p₂ l) x * evalE V (q₂ l) t ≠ 0 := by
    constructor
    · intro h
      have hb := chart_mono ((pullback f sJ).basicOpen_le G) h
      obtain ⟨hx, ht⟩ := mem_chart_of_pair_mem_box hb
      refine ⟨hx, ht, ?_⟩
      rw [← hGv hx ht]
      exact (toScheme_mem_basicOpen_iff (sX := prodHom f sJ) ⟨pair x t, hb⟩ G).1
        (mem_chart_iff.1 h)
    · rintro ⟨hx, ht, hne⟩
      rw [← hGv hx ht] at hne
      exact mem_chart_iff.2 ((toScheme_mem_basicOpen_iff (sX := prodHom f sJ)
        ⟨pair x t, mem_chart_box hx ht⟩ G).2 hne)
  refine ⟨hmem, fun h => ?_⟩
  obtain ⟨hx, ht, hne⟩ := hmem.1 h
  have hb : pair x t ∈ chart (sX := prodHom f sJ) (box (f := f) (sJ := sJ) A V) :=
    mem_chart_box hx ht
  have e := congrArg (evalHom _ ⟨pair x t, h⟩) hau
  rw [map_mul, map_pow] at e
  have e2 : ∀ b : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V),
      evalHom _ ⟨pair x t, h⟩ (ρ b) = eval _ b ⟨pair x t, hb⟩ := fun b =>
    (evalHom_res ((pullback f sJ).basicOpen_le G) ⟨pair x t, h⟩ b).symm
  rw [e2, e2, hGv hx ht, hav hx ht] at e
  rwa [evalE_of_mem _ h, eq_div_iff (pow_ne_zero _ hne)]

/-- **Joint continuity on a basic open of a box.** -/
theorem isOpen_and_continuousOn_pair_basicOpen {A : C.Opens} {V : J.Opens}
    [LocallyOfFiniteType f] [LocallyOfFiniteType sJ] (hA : IsAffineOpen A)
    (hV : IsAffineOpen V) (G : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V))
    (g : Γ(pullback f sJ, (pullback f sJ).basicOpen G)) :
    IsOpen {xt : ComplexPoints f × ComplexPoints sJ |
        pair xt.1 xt.2 ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)} ∧
      ContinuousOn (fun xt : ComplexPoints f × ComplexPoints sJ => evalE _ g (pair xt.1 xt.2))
        {xt | pair xt.1 xt.2 ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)} := by
  obtain ⟨k, m₁, m₂, p₁, q₁, p₂, q₂, hsep⟩ := exists_sep_basicOpen f sJ hA hV G g
  set S := {xt : ComplexPoints f × ComplexPoints sJ |
    pair xt.1 xt.2 ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)}
  set S₀ := (chart (sX := f) A) ×ˢ (chart (sX := sJ) V) with hS₀
  have hS₀o : IsOpen S₀ := (isOpen_chart f A).prod (isOpen_chart sJ V)
  have hsumc : ∀ {m : ℕ} (p : Fin m → Γ(C, A)) (q : Fin m → Γ(J, V)),
      ContinuousOn (fun xt : ComplexPoints f × ComplexPoints sJ =>
        ∑ l, evalE A (p l) xt.1 * evalE V (q l) xt.2) S₀ := by
    intro m p q
    refine continuousOn_finset_sum _ fun l _ => ContinuousOn.mul ?_ ?_
    · exact (continuousOn_evalE A (p l)).comp continuous_fst.continuousOn fun xt h => h.1
    · exact (continuousOn_evalE V (q l)).comp continuous_snd.continuousOn fun xt h => h.2
  have hSeq : S = S₀ ∩ (fun xt : ComplexPoints f × ComplexPoints sJ =>
      ∑ l, evalE A (p₂ l) xt.1 * evalE V (q₂ l) xt.2) ⁻¹' {0}ᶜ := by
    ext xt
    simp only [S, S₀, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff, (hsep xt.1 xt.2).1, and_assoc]
  have hSo : IsOpen S := by
    rw [hSeq]
    exact (hsumc p₂ q₂).isOpen_inter_preimage hS₀o isOpen_compl_singleton
  refine ⟨hSo, ?_⟩
  have hc : ContinuousOn (fun xt : ComplexPoints f × ComplexPoints sJ =>
      (∑ l, evalE A (p₁ l) xt.1 * evalE V (q₁ l) xt.2) /
        (∑ l, evalE A (p₂ l) xt.1 * evalE V (q₂ l) xt.2) ^ k) S := by
    have hsub : S ⊆ S₀ := hSeq.subset.trans Set.inter_subset_left
    refine ((hsumc p₁ q₁).mono hsub).div (((hsumc p₂ q₂).mono hsub).pow k) ?_
    intro xt hxt
    exact pow_ne_zero _ ((hsep xt.1 xt.2).1.1 hxt).2.2
  exact hc.congr fun xt hxt => (hsep xt.1 xt.2).2 hxt

/-- **The holomorphic-function model of `𝒪_{C^an}` for a smooth projective connected curve.** -/
theorem exists_theta_curve {C : Scheme.{0}} (f : C ⟶ Spec (.of ℂ)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [ConnectedSpace C] :
    ∃ cs : ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f),
      letI := cs
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ∞ (ComplexPoints f) ∧
      ∃ Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f],
        ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
          Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
            evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g := by
  have h := isAlgebraicComplexManifold f (n := 1)
  exact ⟨analytificationChartedSpace f 1, h.1, structureSheafIsoHolomorphic f 1, h.2.2.2.2⟩

/-- Étale coordinates restrict to étale coordinates on a smaller open. -/
theorem etale_homOfVector_restrict {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    {U V : X.Opens} (hVU : V ≤ U) (z : Fin n → Γ(X, U))
    (hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)))) :
    Etale (AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (X.presheaf.map (homOfLE hVU).op (z i.down)))) := by
  have e : AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (X.presheaf.map (homOfLE hVU).op (z i.down))) =
      X.homOfLE hVU ≫ AffineSpace.homOfVector (U.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down)) := by
    rw [AffineSpace.comp_homOfVector, Scheme.homOfLE_ι_assoc]
    congr 1
    funext i
    simp only [Function.comp_apply, Scheme.Opens.topIso_inv, Scheme.Hom.appTop,
      Scheme.homOfLE_app]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [e]
  infer_instance

/-- **An affine étale coordinate chart through a given point.** -/
theorem exists_affine_etaleChart {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [SmoothOfRelativeDimension n sX] (e₀ : ComplexPoints sX) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (z : Fin n → Γ(X, V))
      (hz : Etale (AffineSpace.homOfVector (V.ι ≫ sX)
        (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z i.down))))
      (W : Set (ComplexPoints sX)) (hW : W ⊆ chart V), IsOpen W ∧ e₀ ∈ W ∧
        IsOpenEmbedding (fun y : W ↦ fun i ↦ eval V (z i) ⟨y.1, hW y.2⟩) := by
  obtain ⟨U, z, hz, he⟩ := (etaleCoordinate_atlas_of_smooth sX (n := n)).1 e₀
  obtain ⟨V₀, hV, heV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (mem_chart_iff.1 he)
  let V : X.Opens := V₀
  let z' : Fin n → Γ(X, V) := fun i => X.presheaf.map (homOfLE hVU).op (z i)
  have hz' : Etale (AffineSpace.homOfVector (V.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ V.topIso.inv (z' i.down))) :=
    etale_homOfVector_restrict hVU z hz
  obtain ⟨W, hW, hWo, heW, hemb⟩ :=
    (etaleCoordinate_atlas_of_smooth sX).2.1 V z' hz' e₀ (mem_chart_iff.2 heV)
  exact ⟨V, hV, z', hz', W, hW, hWo, heW, hemb⟩

/-- **A finite affine cover with affine pairwise intersections** of a
quasi-compact separated scheme over `ℂ`. -/
theorem exists_affine_cover_fin {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]
    [IsSeparated sX] :
    ∃ (r : ℕ) (A : Fin r → X.Opens), (∀ c, IsAffineOpen (A c)) ∧
      (∀ c d, IsAffineOpen (A c ⊓ A d)) ∧ ∀ x : X, ∃ c, x ∈ A c := by
  classical
  haveI : CompactSpace X := (quasiCompact_iff_compactSpace sX).1 inferInstance
  haveI : IsSeparated (terminal.from X) := by
    rw [show terminal.from X = sX ≫ terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  let A : Fin t.card → X.Opens := fun c => ((t.equivFin.symm c : X.affineOpens) : X.Opens)
  refine ⟨t.card, A, fun c => (t.equivFin.symm c : X.affineOpens).2,
    fun c d => ((t.equivFin.symm c : X.affineOpens).2).inf (t.equivFin.symm d : X.affineOpens).2,
    fun x => ?_⟩
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨t.equivFin ⟨U, hU⟩, by simpa [A] using hxU⟩

/-- **Tube lemma for the standard covers of the boxes.** Near a `ℂ`-point `e₀` of `V`, the
slices `C × {t}` are covered by finitely many opens `W a` of `C(ℂ)` with `W a × B` inside a
member `D(F (ρ a))` of the standard covers, for a fixed open neighbourhood `B` of `e₀`. -/
theorem exists_tube [IsProper f] [LocallyOfFiniteType sJ] {r : ℕ} (A : Fin r → C.Opens)
    (hA : ∀ c, IsAffineOpen (A c)) (hAcov : ∀ x : C, ∃ c, x ∈ A c) {V : J.Opens}
    (hV : IsAffineOpen V) {s : Fin r → ℕ}
    (F : ∀ c, Fin (s c) → Γ(pullback f sJ, box (f := f) (sJ := sJ) (A c) V))
    (hF : ∀ c, Ideal.span (Set.range (F c)) = ⊤) (e₀ : ComplexPoints sJ)
    (he₀ : e₀ ∈ chart V) :
    ∃ (Ai : Type) (W : Ai → Opens (space f)) (ρ : Ai → Σ c, Fin (s c))
      (B : Set (ComplexPoints sJ)), IsOpen B ∧ e₀ ∈ B ∧ (⊤ : Opens (space f)) = ⨆ a, W a ∧
      ∀ a, ∀ x ∈ W a, ∀ t ∈ B, pair x t ∈ chart (sX := prodHom f sJ) (Nopen F (ρ a)) := by
  classical
  haveI := MMP.Proof_lem_mmp_projective_corner_presentation.compactSpace_complexPoints f
  have hloc : ∀ x : ComplexPoints f, ∃ (j : Σ c, Fin (s c)) (O : Set (ComplexPoints f))
      (Bx : Set (ComplexPoints sJ)), IsOpen O ∧ IsOpen Bx ∧ x ∈ O ∧ e₀ ∈ Bx ∧
      ∀ x' ∈ O, ∀ t ∈ Bx, pair x' t ∈ chart (sX := prodHom f sJ) (Nopen F j) := by
    intro x
    obtain ⟨c, hc⟩ := hAcov x.toScheme
    have hbox : pair x e₀ ∈ chart (sX := prodHom f sJ) (box (f := f) (sJ := sJ) (A c) V) :=
      mem_chart_box (mem_chart_iff.2 hc) he₀
    have hcov := ((isAffineOpen_box (f := f) (sJ := sJ) (hA c) hV).self_le_iSup_basicOpen_iff
      (s := Set.range (F c))).2 (hF c)
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := Opens.mem_iSup.1 (hcov (mem_chart_iff.1 hbox))
    have hm' : pair x e₀ ∈ chart (sX := prodHom f sJ) (Nopen F ⟨c, m⟩) := mem_chart_iff.2 hm
    obtain ⟨hSo, -⟩ := isOpen_and_continuousOn_pair_basicOpen f sJ (hA c) hV (F c m) 0
    obtain ⟨O, Bx, hO, hBx, hxO, heB, hsub⟩ := isOpen_prod_iff.1 hSo x e₀ hm'
    refine ⟨⟨c, m⟩, O, Bx, hO, hBx, hxO, heB, fun x' hx' t ht => ?_⟩
    have h1 : (x', t) ∈ {xt : ComplexPoints f × ComplexPoints sJ |
        pair xt.1 xt.2 ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen (F c m))} :=
      hsub (Set.mk_mem_prod hx' ht)
    exact h1
  choose j O Bx hO hBx hxO heB hsub using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxO x⟩)
  refine ⟨t, fun a => ⟨O a.1, hO a.1⟩, fun a => j a.1, ⋂ a ∈ t, Bx a,
    isOpen_biInter_finset fun a _ => hBx a, Set.mem_iInter₂.2 fun a _ => heB a, ?_, ?_⟩
  · refine le_antisymm (fun x _ => ?_) le_top
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩
  · rintro ⟨a, ha⟩ x hx t' ht'
    exact hsub a x hx t' (Set.mem_iInter₂.1 ht' a ha)

section ThetaTools

variable {C : Scheme.{0}} {f : C ⟶ Spec (.of ℂ)}
  [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]

/-- The isomorphism `Θ` is injective on sections over each open set. -/
theorem theta_injective (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) (W : Opens (space f)) :
    Function.Injective (Θ.hom.hom.app (op W)) := fun a b h => by
  rw [← theta_hom_inv_apply Θ W a, ← theta_hom_inv_apply Θ W b, h]

/-- Two sections of the structure sheaf are equal if their images under `Θ` agree pointwise. -/
theorem theta_ext (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {W : Opens (space f)}
    {a b : (structureSheaf f).obj.obj (op W)}
    (h : ∀ x : W, Θ.hom.hom.app (op W) a x = Θ.hom.hom.app (op W) b x) : a = b :=
  theta_injective Θ W (Subtype.ext (funext h))

/-- `Θ` sends a product of sections to the pointwise product of their values. -/
theorem theta_mul (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {W : Opens (space f)}
    (a b : (structureSheaf f).obj.obj (op W)) (x : W) :
    Θ.hom.hom.app (op W) (a * b) x = Θ.hom.hom.app (op W) a x * Θ.hom.hom.app (op W) b x := by
  rw [map_mul]
  rfl

/-- `Θ` sends a sum of sections to the pointwise sum of their values. -/
theorem theta_add (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {W : Opens (space f)}
    (a b : (structureSheaf f).obj.obj (op W)) (x : W) :
    Θ.hom.hom.app (op W) (a + b) x = Θ.hom.hom.app (op W) a x + Θ.hom.hom.app (op W) b x := by
  rw [map_add]
  rfl

/-- `Θ` sends the unit section to the constant function `1`. -/
theorem theta_one (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {W : Opens (space f)} (x : W) :
    Θ.hom.hom.app (op W) 1 x = 1 := by
  rw [map_one]
  rfl

/-- **Holomorphic functions are sections of `𝒪_{C^an}`.** -/
theorem exists_section_of_contMDiffOn
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ∞ (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) (W : Opens (space f)) {g : ComplexPoints f → ℂ}
    (hg : ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞ g (W : Set (ComplexPoints f))) :
    ∃ σ : (structureSheaf f).obj.obj (op W), ∀ x : W, Θ.hom.hom.app (op W) σ x = g x := by
  have hs : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞ (fun x : W => g x) := fun x =>
    contMDiffAt_subtype_iff.2 (hg.contMDiffAt (W.isOpen.mem_nhds x.2))
  let τ : (𝒪[1, ComplexPoints f]).obj.obj (op W) := ⟨fun x : W => g x, hs⟩
  exact ⟨Θ.inv.hom.app (op W) τ, fun x => by rw [theta_inv_hom_apply]⟩

/-- **Sections of `𝒪_{C^an}` are holomorphic.** -/
theorem contMDiffOn_of_section [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ∞ (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) (W : Opens (space f))
    (σ : (structureSheaf f).obj.obj (op W)) {g : ComplexPoints f → ℂ}
    (hg : ∀ x : W, Θ.hom.hom.app (op W) σ x = g x) :
    ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞ g (W : Set (ComplexPoints f)) := by
  have hs := smoothSheaf.contMDiff_section (IM := 𝓘(ℂ, EuclideanSpace ℂ (Fin 1))) (I := 𝓘(ℂ, ℂ))
    (M := ComplexPoints f) (N := ℂ) (U := op W) (Θ.hom.hom.app (op W) σ)
  intro x hx
  have h2 : ContMDiffAt 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞ (fun y : W => g y) ⟨x, hx⟩ :=
    (hs ⟨x, hx⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => (hg y).symm)
  exact (contMDiffAt_subtype_iff.1 h2).contMDiffWithinAt

end ThetaTools

/-- **Segment integrals of holomorphic functions are holomorphic.** -/
theorem analyticOnNhd_segmentIntegral {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {p : Fin n → ℂ} (hp : p ∈ Ω) {G : (Fin n → ℂ) → ℂ}
    (hG : DifferentiableOn ℂ G Ω) (i : Fin n) :
    AnalyticOnNhd ℂ (fun w => ∫ s in (0 : ℝ)..1, (w - p) i * G (p + s • (w - p))) Ω := by
  have hseg : ∀ w ∈ Ω, ∀ s ∈ Set.Icc (0 : ℝ) 1, p + s • (w - p) ∈ Ω := fun w hw s hs => by
    simpa using hΩc.add_smul_sub_mem hp hw hs
  have hcont : ContinuousOn (Function.uncurry fun (w : Fin n → ℂ) (s : ℝ) =>
      (w - p) i * G (p + s • (w - p))) (Ω ×ˢ Set.Icc 0 1) := by
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    exact hG.continuousOn.comp (Continuous.continuousOn (by fun_prop))
      fun q hq => hseg q.1 hq.1 q.2 hq.2
  refine ((MMP.SeveralComplex.cauchy_osgood_laurent.{0, 0} ℂ).2.2.1 n Ω _ hΩo
    (Ana.continuousOn_intervalIntegral hcont) fun ζ hζ j => ?_).2.1
  let U : Set ℂ := (fun τ => Function.update ζ j τ) ⁻¹' Ω
  have hUo : IsOpen U := hΩo.preimage (by fun_prop)
  have hζU : ζ j ∈ U := by simp [U, hζ]
  have hcU : ContinuousOn (Function.uncurry fun (τ : ℂ) (s : ℝ) =>
      (Function.update ζ j τ - p) i * G (p + s • (Function.update ζ j τ - p)))
      (U ×ˢ Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun q : ℂ × ℝ => (Function.update ζ j q.1, q.2)) (U ×ˢ Set.Icc 0 1) :=
      Continuous.continuousOn (by fun_prop)
    exact hcont.comp h1 fun q hq => ⟨hq.1, hq.2⟩
  have hdU : ∀ s ∈ Set.Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun τ : ℂ =>
      (Function.update ζ j τ - p) i * G (p + s • (Function.update ζ j τ - p))) U := by
    intro s hs τ hτ
    have hu : DifferentiableAt ℂ (fun τ : ℂ => Function.update ζ j τ) τ := by
      rw [differentiableAt_pi]
      intro k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Function.update_of_ne hk]
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
    · exact (differentiableAt_apply i _).comp τ (hu.sub_const p)
    · have hGd : DifferentiableAt ℂ G (p + s • (Function.update ζ j τ - p)) :=
        hG.differentiableAt (hΩo.mem_nhds (hseg _ hτ s hs))
      refine hGd.comp τ ?_
      have : (fun τ : ℂ => p + s • (Function.update ζ j τ - p)) =
          fun τ => p + (s : ℂ) • (Function.update ζ j τ - p) := by
        ext τ k
        simp [Complex.real_smul]
      rw [this]
      exact ((hu.sub_const p).const_smul (s : ℂ)).const_add p
  exact (Ana.differentiableOn_intervalIntegral hUo hcU hdU).differentiableAt (hUo.mem_nhds hζU)

section UnitsVal

variable {C : Scheme.{0}} {f : C ⟶ Spec (.of ℂ)}
  [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]

/-- The value at a point of a section of `𝒪^×` given additively. -/
noncomputable abbrev uval (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {U : Opens (space f)}
    (a : (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj.obj (op U))
    (x : U) : ℂ :=
  Θ.hom.hom.app (op U) ((Additive.toMul a : ((structureSheaf f).obj.obj (op U))ˣ) :
    (structureSheaf f).obj.obj (op U)) x

/-- Two sections of `𝒪^×` are equal if their values agree at every point. -/
theorem uval_ext (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {U : Opens (space f)}
    {a b : (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj.obj (op U)}
    (h : ∀ x : U, uval Θ a x = uval Θ b x) : a = b :=
  Additive.toMul.injective (Units.ext (theta_ext Θ h))

/-- The value of a sum of sections of `𝒪^×`, given additively, is the product of the values. -/
theorem uval_add (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {U : Opens (space f)}
    (a b : (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj.obj (op U))
    (x : U) : uval Θ (a + b) x = uval Θ a x * uval Θ b x := by
  change Θ.hom.hom.app (op U) ((((Additive.toMul a : ((structureSheaf f).obj.obj (op U))ˣ) *
    (Additive.toMul b : ((structureSheaf f).obj.obj (op U))ˣ) :
    ((structureSheaf f).obj.obj (op U))ˣ)) : (structureSheaf f).obj.obj (op U)) x = _
  rw [Units.val_mul, theta_mul]

/-- The value of the additive inverse of a section of `𝒪^×` is the inverse of its value. -/
theorem uval_neg (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {U : Opens (space f)}
    (a : (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj.obj (op U))
    (x : U) : uval Θ (-a) x = (uval Θ a x)⁻¹ := by
  have h := uval_add Θ a (-a) x
  rw [add_neg_cancel] at h
  have h1 : uval Θ (0 : (Stacks.Cohomology.Generators.unitsSheaf
      (analytification f)).obj.obj (op U)) x = 1 := by
    change Θ.hom.hom.app (op U) (((1 : ((structureSheaf f).obj.obj (op U))ˣ)) :
      (structureSheaf f).obj.obj (op U)) x = 1
    rw [Units.val_one, theta_one]
  rw [h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The value of a restricted section of `𝒪^×` is the value of the section at the same point. -/
theorem uval_restr (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {U U' : Opens (space f)}
    (hle : U' ≤ U)
    (a : (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj.obj (op U))
    (x : U') : uval Θ (CechCochains.restr
      (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj hle a) x =
        uval Θ a ⟨x.1, hle x.2⟩ :=
  theta_res Θ hle _ x

end UnitsVal

/-- The slice `C → C ×_ℂ J`, `x ↦ (x, y)`, at a `ℂ`-point `y` of `J`. -/
noncomputable def sliceAt (y : ComplexPoints sJ) : C ⟶ pullback f sJ :=
  pullback.lift (𝟙 C) (f ≫ y.hom) (by
    rw [Category.id_comp, Category.assoc, y.hom_comp_structure, Category.comp_id])

/-- The slice at `y` is a morphism over `Spec ℂ`: its composite with `prodHom f sJ` is `f`. -/
theorem sliceAt_comp (y : ComplexPoints sJ) : sliceAt f sJ y ≫ prodHom f sJ = f := by
  simp only [sliceAt, prodHom, ← Category.assoc, pullback.lift_snd]
  rw [Category.assoc, y.hom_comp_structure, Category.comp_id]

/-- The `ℂ`-point of `C ×_ℂ J` obtained from `x` through the slice at `y` is `(x, y)`. -/
theorem realize_sliceAt (y : ComplexPoints sJ) (x : ComplexPoints f) :
    realize (sliceAt f sJ y) (sliceAt_comp f sJ y) x = pair x y := by
  apply ComplexPoints.ext
  apply pullback.hom_ext
  · change (x.hom ≫ sliceAt f sJ y) ≫ _ = _
    rw [pair_hom_fst, Category.assoc, sliceAt, pullback.lift_fst, Category.comp_id]
  · change (x.hom ≫ sliceAt f sJ y) ≫ _ = _
    rw [pair_hom_snd, Category.assoc, sliceAt, pullback.lift_snd, ← Category.assoc,
      x.hom_comp_structure, Category.id_comp]

/-- **Restrictions of regular functions to slices are holomorphic.** -/
theorem contMDiffOn_evalE_pair [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ∞ (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (N : (pullback f sJ).Opens) (g : Γ(pullback f sJ, N)) (t : ComplexPoints sJ) :
    ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞
      (fun x => evalE N g (pair x t)) {x | pair x t ∈ chart (sX := prodHom f sJ) N} := by
  let j := sliceAt f sJ t
  let V' : Opens (space f) := (Opens.map (toSchemeHom f)).obj (j ⁻¹ᵁ N)
  have hV' : (V' : Set (ComplexPoints f)) = {x | pair x t ∈ chart (sX := prodHom f sJ) N} := by
    ext x
    change j (x.toScheme) ∈ N ↔ pair x t ∈ chart (sX := prodHom f sJ) N
    rw [← realize_sliceAt f sJ t x, mem_chart_iff]
    rfl
  rw [← hV']
  refine contMDiffOn_of_section Θ V' ((analytificationHom f).hom.c.app (op (j ⁻¹ᵁ N)) (j.app N g))
    fun x => (hΘ (j ⁻¹ᵁ N) (j.app N g) x).trans ?_
  have hx : pair x.1 t ∈ chart (sX := prodHom f sJ) N := by
    have := x.2
    rwa [← SetLike.mem_coe, hV'] at this
  rw [evalE_of_mem _ hx]
  have h1 : realize j (sliceAt_comp f sJ t) x.1 ∈ chart (sX := prodHom f sJ) N := by
    rwa [realize_sliceAt]
  have key : ∀ (q : ComplexPoints (prodHom f sJ)) (_ : q = pair x.1 t)
      (hq : q ∈ chart (sX := prodHom f sJ) N),
      evalHom N ⟨q, hq⟩ g = eval N g ⟨pair x.1 t, hx⟩ := by
    rintro _ rfl _
    rfl
  exact (evalHom_realize j (sliceAt_comp f sJ t) N g x.1 h1 _).symm.trans
    (key _ (realize_sliceAt f sJ t x.1) h1)

variable [LocallyOfFiniteType f]

/-- The class in `H¹(C^an, 𝒪^×)` of the analytification of the restriction of an invertible
module `M` on `C ×_ℂ J` to the slice `C × {y}`. -/
noncomputable def sliceClass
    (M : SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf (pullback f sJ).toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible (pullback f sJ).toRingedSpace.sheaf.obj
      (structureSheafRing (pullback f sJ).toRingedSpace).property M)
    (y : ComplexPoints sJ) :
    Stacks.Cohomology.SheafTorsor.sheafCohomologyOne (analytification f : RingedSpace)
      (Stacks.Cohomology.Generators.unitsSheaf (analytification f)) :=
  Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne (analytification f : RingedSpace)
    (Stacks.Cohomology.Generators.unitsSheaf (analytification f))
    (Quotient.mk _ (Stacks.Cohomology.Generators.generatorTorsorOfInvertible
      (analytification f : RingedSpace)
      ((modulePullback (X := (analytification f : RingedSpace)) (Y := C.toRingedSpace)
        (analytificationHom f)).obj
        ((modulePullback (sliceAt f sJ y).toLRSHom.toShHom).obj M))
      (by
        haveI := hM
        haveI := Stacks.RingedSpace.isInvertible_modulePullback
          ((sliceAt f sJ y).toLRSHom.toShHom) M
        exact Stacks.RingedSpace.isInvertible_modulePullback _ _)).toTorsor)

omit [LocallyOfFiniteType f] in
/-- **The analytification morphism is local on stalks.** A germ of a regular function whose
image in the analytic stalk is a unit does not vanish at the point, hence is a unit. -/
theorem isLocalHom_stalkMap_analytificationHom {n₀ : ℕ}
    [ChartedSpace (EuclideanSpace ℂ (Fin n₀)) (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[n₀, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (x : space f) : IsLocalHom ((analytificationHom f).hom.stalkMap x).hom := by
  refine ⟨fun γ hγ => ?_⟩
  obtain ⟨V, hxV, g, rfl⟩ := C.presheaf.exists_germ_eq γ
  have e := congrArg (fun φ => φ.hom g)
    (PresheafedSpace.stalkMap_germ (analytificationHom f).hom V x hxV)
  simp only [CommRingCat.comp_apply] at e
  rw [e] at hγ
  set Fp := (analytification f).presheaf
  set sg := (analytificationHom f).hom.c.app (op V) g
  obtain ⟨u, hu⟩ := hγ
  obtain ⟨U', hxU', t, ht⟩ := Fp.exists_germ_eq (↑u⁻¹ : Fp.stalk x)
  set V' := (Opens.map (analytificationHom f).hom.base).obj V
  have hmul : Fp.germ (V' ⊓ U') x ⟨hxV, hxU'⟩
      (Fp.map (homOfLE inf_le_left).op sg * Fp.map (homOfLE inf_le_right).op t) =
      Fp.germ (V' ⊓ U') x ⟨hxV, hxU'⟩ 1 := by
    rw [map_mul, map_one]
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht]
    change _ * _ = (1 : Fp.stalk x)
    rw [← hu]
    exact u.mul_inv
  obtain ⟨W, hxW, iU, iV, heq⟩ := Fp.germ_eq x _ _ _ _ hmul
  have hΘW := congrArg (fun r => Θ.hom.hom.app (op W) r ⟨x, hxW⟩) heq
  simp only [map_mul, map_one] at hΘW
  have h1 : Θ.hom.hom.app (op W) (Fp.map iU.op (Fp.map (homOfLE inf_le_left).op sg)) ⟨x, hxW⟩ =
      evalHom V ⟨x, mem_chart_iff.2 hxV⟩ g := by
    rw [show iU = homOfLE (leOfHom iU) from rfl]
    erw [theta_res Θ (leOfHom iU), theta_res Θ inf_le_left]
    exact hΘ V g ⟨x, hxV⟩
  have hΘW' : Θ.hom.hom.app (op W) (Fp.map iU.op (Fp.map (homOfLE inf_le_left).op sg))
      ⟨x, hxW⟩ * Θ.hom.hom.app (op W) (Fp.map iU.op (Fp.map (homOfLE inf_le_right).op t))
      ⟨x, hxW⟩ = 1 := hΘW
  have hne : evalHom V ⟨x, mem_chart_iff.2 hxV⟩ g ≠ 0 := by
    intro h0
    rw [h1, h0, zero_mul] at hΘW'
    exact zero_ne_one hΘW'
  exact (C.mem_basicOpen g _ _).1
    ((toScheme_mem_basicOpen_iff (sX := f) ⟨x, mem_chart_iff.2 hxV⟩ g).2 hne)

/-- The abelian sheaf `𝒪_{C^an}`. -/
noncomputable abbrev anO : Sheaf (Opens.grothendieckTopology (space f)) AddCommGrpCat.{0} :=
  (sheafCompose (Opens.grothendieckTopology (space f)) (forget₂ RingCat AddCommGrpCat)).obj
    (ringCatSheaf f)

/-- The Čech `1`-cochain `∑ₖ bₖ · Pₖ` of `𝒪_{C^an}`, the scalars acting through `m`. -/
noncomputable def lamCochain (m : ℂ → (anO f ⟶ anO f)) {A : Type} {W : A → Opens (space f)}
    {K : Type} [Fintype K] (Pc : K → CechCochains.Cochain W (anO f).obj 1) (b : K → ℂ) :
    CechCochains.Cochain W (anO f).obj 1 :=
  ∑ k, Stacks.Cohomology.CechOne.push W (m (b k)).hom 1 (Pc k)

/-- `lamCochain` is additive in the coefficients when `m` is additive. -/
theorem lamCochain_add (m : ℂ → (anO f ⟶ anO f)) (hmadd : ∀ a b : ℂ, m (a + b) = m a + m b)
    {A : Type} {W : A → Opens (space f)} {K : Type} [Fintype K]
    (Pc : K → CechCochains.Cochain W (anO f).obj 1) (b b' : K → ℂ) :
    lamCochain f m Pc (b + b') = lamCochain f m Pc b + lamCochain f m Pc b' := by
  simp only [lamCochain, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext i
  simp only [Pi.add_apply, Stacks.Cohomology.CechOne.push_apply, CechCochains.Cochain.add_apply,
    hmadd]
  rfl

/-- Scaling the coefficients of `lamCochain` by `a` amounts to applying `m a` to it. -/
theorem lamCochain_smul (m : ℂ → (anO f ⟶ anO f)) (hmmul : ∀ a b : ℂ, m (a * b) = m b ≫ m a)
    {A : Type} {W : A → Opens (space f)} {K : Type} [Fintype K]
    (Pc : K → CechCochains.Cochain W (anO f).obj 1) (a : ℂ) (b : K → ℂ) :
    lamCochain f m Pc (a • b) =
      Stacks.Cohomology.CechOne.push W (m a).hom 1 (lamCochain f m Pc b) := by
  simp only [lamCochain, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Stacks.Cohomology.CechOne.push_apply, hmmul]
  rfl

/-- **Čech logarithms are linear.** The Čech classes of the cocycles among the combinations
`∑ₖ bₖ Pₖ` are, through `φ`, the values of a `ℂ`-linear map of the coefficients. -/
theorem exists_linear_cechLog {n : ℕ} (m : ℂ → (anO f ⟶ anO f))
    (hmadd : ∀ a b : ℂ, m (a + b) = m a + m b) (hmmul : ∀ a b : ℂ, m (a * b) = m b ≫ m a)
    (φ : (Fin n → ℂ) ≃+ Sheaf.H (anO f) 1)
    (hφ : ∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v))
    {A : Type} (W : A → Opens (space f)) (hW : (⊤ : Opens (space f)) = ⨆ a, W a)
    {K : Type} [Fintype K] (Pc : K → CechCochains.Cochain W (anO f).obj 1) :
    ∃ ℓ : (K → ℂ) →ₗ[ℂ] (Fin n → ℂ), ∀ (b : K → ℂ)
      (hb : lamCochain f m Pc b ∈ CechCochains.cocycles1 W (anO f).obj),
      φ (ℓ b) = (Stacks.Thickenings.sheafCohomologyOneExtEquiv (space f) (anO f)).hom
        (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections (space f) ⊤ W hW (anO f)
          (CechCochains.cls W _ ⟨_, hb⟩)) := by
  classical
  let RD := fun (G : Sheaf (Opens.grothendieckTopology (space f)) AddCommGrpCat.{0}) =>
    Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections (space f) ⊤ W hW G
  let E := Stacks.Thickenings.sheafCohomologyOneExtEquiv (space f) (anO f)
  have hpush : ∀ (a : ℂ) (c : CechCochains.Cochain W (anO f).obj 1),
      c ∈ CechCochains.cocycles1 W (anO f).obj →
      Stacks.Cohomology.CechOne.push W (m a).hom 1 c ∈
        CechCochains.cocycles1 W (anO f).obj := fun a c hc =>
    Stacks.Cohomology.CechOne.cechD_push W (m a).hom 1 c hc
  let Z : Submodule ℂ (K → ℂ) :=
    { carrier := {b | lamCochain f m Pc b ∈ CechCochains.cocycles1 W (anO f).obj}
      add_mem' := fun {b b'} hb hb' => by
        simp only [Set.mem_setOf_eq, lamCochain_add f m hmadd] at hb hb' ⊢
        exact add_mem hb hb'
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have : lamCochain f m Pc 0 = 0 := by
          have h := lamCochain_add f m hmadd Pc 0 0
          rw [add_zero] at h
          exact left_eq_add.mp h
        rw [this]
        exact zero_mem _
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, lamCochain_smul f m hmmul] at hb ⊢
        exact hpush a _ hb }
  let T : Z → Sheaf.H (anO f) 1 := fun b => E.hom (RD (anO f) (CechCochains.cls W _ ⟨_, b.2⟩))
  have hTadd : ∀ b b' : Z, T (b + b') = T b + T b' := by
    intro b b'
    have : (⟨_, (b + b').2⟩ : CechCochains.cocycles1 W (anO f).obj) = ⟨_, b.2⟩ + ⟨_, b'.2⟩ :=
      Subtype.ext (lamCochain_add f m hmadd Pc b b')
    simp only [T, this]
    rw [CechCochains.cls, QuotientAddGroup.mk_add, map_add]
    exact map_add (ConcreteCategory.hom E.hom) _ _
  have hTsmul : ∀ (a : ℂ) (b : Z), T (a • b) = Sheaf.H.map (m a) 1 (T b) := by
    intro a b
    have hnat := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality (space f) ⊤ W hW
      (m a) ⟨_, b.2⟩ ⟨_, (a • b).2⟩ (fun i => by
        change lamCochain f m Pc (a • (b : K → ℂ)) i = _
        rw [lamCochain_smul f m hmmul]
        rfl)
    simp only [T]
    rw [← hnat]
    exact sheafCohomologyOneExtEquiv_naturality (space f) (m a) _
  let ℓZ : Z →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun b => φ.symm (T b)
      map_add' := fun b b' => by rw [hTadd, map_add]
      map_smul' := fun a b => by
        rw [hTsmul, RingHom.id_apply]
        apply φ.injective
        rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] }
  obtain ⟨Z', hZZ'⟩ := Submodule.exists_isCompl Z
  refine ⟨ℓZ ∘ₗ Submodule.linearProjOfIsCompl Z Z' hZZ', fun b hb => ?_⟩
  have hπ : Submodule.linearProjOfIsCompl Z Z' hZZ' b = ⟨b, hb⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hZZ' ⟨b, hb⟩
  rw [LinearMap.comp_apply, hπ]
  exact φ.apply_symm_apply _

/-- **The slice class as a Čech class.** -/
theorem sliceClass_eq_cech {n₀ : ℕ} [ChartedSpace (EuclideanSpace ℂ (Fin n₀)) (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[n₀, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (M : SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf (pullback f sJ).toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible (pullback f sJ).toRingedSpace.sheaf.obj
      (structureSheafRing (pullback f sJ).toRingedSpace).property M)
    {I : Type} (N : I → (pullback f sJ).Opens)
    (ε : ∀ j, Stacks.SheafOfModules.GeneratorSections (pullback f sJ).toRingedSpace M (N j))
    {A : Type} (W : A → Opens (space f)) (hW : (⊤ : Opens (space f)) = ⨆ a, W a) (ρ : A → I)
    (y : ComplexPoints sJ)
    (hWρ : ∀ a (x : space f), x ∈ W a → pair x y ∈ chart (sX := prodHom f sJ) (N (ρ a))) :
    ∃ z : CechCochains.cocycles1 W
        (Stacks.Cohomology.Generators.unitsSheaf (analytification f : RingedSpace)).presheaf,
      (∀ (i : Fin 2 → A) (x : CechCochains.inter W i)
        (hx : pair x.1 y ∈ chart (sX := prodHom f sJ) (N (ρ (i 0)) ⊓ N (ρ (i 1)))),
        Θ.hom.hom.app (op _) ((Additive.toMul (z.val i) :
          ((structureSheaf f).obj.obj (op (CechCochains.inter W i)))ˣ) :
            (structureSheaf f).obj.obj (op (CechCochains.inter W i))) x =
          eval _ (show Γ(pullback f sJ, N (ρ (i 0)) ⊓ N (ρ (i 1))) from
            (Stacks.SheafOfModules.generatorRatioUnit M (N (ρ (i 0)) ⊓ N (ρ (i 1)))
            (Stacks.SheafOfModules.generatorRestrict M inf_le_left (ε (ρ (i 0))))
            (Stacks.SheafOfModules.generatorRestrict M inf_le_right (ε (ρ (i 1))))).val)
              ⟨pair x.1 y, hx⟩) ∧
      sliceClass f sJ M hM y =
        Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections (analytification f : RingedSpace)
          ⊤ W hW (Stacks.Cohomology.Generators.unitsSheaf (analytification f))
          (CechCochains.cls W _ z) := by
  classical
  haveI := hM
  let α : (analytification f : RingedSpace) ⟶ C.toRingedSpace := analytificationHom f
  let j := (sliceAt f sJ y).toLRSHom.toShHom
  have hα : ∀ x, IsLocalHom (α.hom.stalkMap x).hom :=
    isLocalHom_stalkMap_analytificationHom f Θ hΘ
  have hj : ∀ x, IsLocalHom (j.hom.stalkMap x).hom := fun x =>
    (sliceAt f sJ y).toLRSHom.prop x
  have hL1 := Stacks.RingedSpace.isInvertible_modulePullback j M
  let N' : I → Opens C.toRingedSpace := fun k => (opensMap j).obj (N k)
  let ε' := fun k => pullbackGenerator' j hj M hM (N k) (ε k)
  have hWρ' : ∀ a, W a ≤ (opensMap α).obj (N' (ρ a)) := by
    intro a x hx
    have h := hWρ a x hx
    rwa [← realize_sliceAt f sJ y x, mem_chart_iff] at h
  obtain ⟨z, hz, hcls⟩ := torsorClass_pullback_eq_cech α hα ((modulePullback j).obj M) hL1 N' ε'
    W hW ρ hWρ' (Stacks.RingedSpace.isInvertible_modulePullback _ _)
  refine ⟨z, fun i x hx => ?_, hcls⟩
  rw [hz i, toMul_ofMul]
  have hle : CechCochains.inter W i ≤ (opensMap α).obj (N' (ρ (i 0)) ⊓ N' (ρ (i 1))) :=
    le_inf ((iInf_le (fun k => W (i k)) 0).trans (hWρ' (i 0)))
      ((iInf_le (fun k => W (i k)) 1).trans (hWρ' (i 1)))
  have e1 := pullbackGenerator'_restrict j hj M hM
    (inf_le_left : N (ρ (i 0)) ⊓ N (ρ (i 1)) ≤ N (ρ (i 0))) (ε (ρ (i 0)))
  have e2 := pullbackGenerator'_restrict j hj M hM
    (inf_le_right : N (ρ (i 0)) ⊓ N (ρ (i 1)) ≤ N (ρ (i 1))) (ε (ρ (i 1)))
  have e3 := generatorRatioUnit_pullbackGenerator' j hj M hM (N (ρ (i 0)) ⊓ N (ρ (i 1)))
    (Stacks.SheafOfModules.generatorRestrict M inf_le_left (ε (ρ (i 0))))
    (Stacks.SheafOfModules.generatorRestrict M inf_le_right (ε (ρ (i 1))))
  simp only [pullTransUnit, Units.coe_map, ε']
  erw [e1, e2, e3]
  erw [Units.coe_map, Units.coe_map]
  erw [theta_res Θ hle]
  erw [hΘ]
  have hr := realize_sliceAt f sJ y x.1
  have h1 : realize (sliceAt f sJ y) (sliceAt_comp f sJ y) x.1 ∈
      chart (sX := prodHom f sJ) (N (ρ (i 0)) ⊓ N (ρ (i 1))) := hr ▸ hx
  have key : ∀ (q : ComplexPoints (prodHom f sJ)) (_ : q = pair x.1 y)
      (hq : q ∈ chart (sX := prodHom f sJ) (N (ρ (i 0)) ⊓ N (ρ (i 1))))
      (a : Γ(pullback f sJ, N (ρ (i 0)) ⊓ N (ρ (i 1)))),
      evalHom _ ⟨q, hq⟩ a = eval _ a ⟨pair x.1 y, hx⟩ := by
    rintro _ rfl _ _; rfl
  exact (evalHom_realize (sliceAt f sJ y) (sliceAt_comp f sJ y) _ _ x.1 h1 _).symm.trans
    (key _ hr h1 _)

/-- Holomorphy of the segment integrals of a regular function along the slices. -/
theorem contMDiffOn_sliceIntegral [LocallyOfFiniteType sJ]
    [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) ∞ (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    {A : C.Opens} {V : J.Opens} (hA : IsAffineOpen A) (hV : IsAffineOpen V) {n : ℕ}
    (G : Γ(pullback f sJ, box (f := f) (sJ := sJ) A V))
    (hf : Fin n → Γ(pullback f sJ, (pullback f sJ).basicOpen G)) (Wa : Opens (space f))
    (φc : OpenPartialHomeomorph (ComplexPoints sJ) (Fin n → ℂ)) {Ω : Set (Fin n → ℂ)}
    (hΩc : Convex ℝ Ω) {p w : Fin n → ℂ} (hp : p ∈ Ω) (hw : w ∈ Ω)
    (hΩT : ∀ v ∈ Ω, v ∈ φc.target)
    (hmem : ∀ x ∈ Wa, ∀ v ∈ Ω,
      pair x (φc.symm v) ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)) :
    ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞
      (fun x => (2 * Real.pi * Complex.I)⁻¹ * ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i *
        evalE _ (hf i) (pair x (φc.symm (p + s • (w - p)))))
      (Wa : Set (ComplexPoints f)) := by
  have hγ : ∀ s ∈ Set.Icc (0 : ℝ) 1, p + s • (w - p) ∈ Ω := fun s hs =>
    hΩc.add_smul_sub_mem hp hw hs
  have hφs : ContinuousOn (fun s : ℝ => φc.symm (p + s • (w - p))) (Set.Icc 0 1) :=
    φc.continuousOn_symm.comp (Continuous.continuousOn (by fun_prop))
      fun s hs => hΩT _ (hγ s hs)
  have hGc : ContinuousOn (Function.uncurry fun (x : ComplexPoints f) (s : ℝ) =>
      ∑ i, (w - p) i * evalE _ (hf i) (pair x (φc.symm (p + s • (w - p)))))
      ((Wa : Set (ComplexPoints f)) ×ˢ Set.Icc 0 1) := by
    refine continuousOn_finset_sum _ fun i _ => continuousOn_const.mul ?_
    obtain ⟨-, hcj⟩ := isOpen_and_continuousOn_pair_basicOpen f sJ hA hV G (hf i)
    have hmap : ContinuousOn (fun q : ComplexPoints f × ℝ =>
        (q.1, φc.symm (p + q.2 • (w - p)))) ((Wa : Set (ComplexPoints f)) ×ˢ Set.Icc 0 1) :=
      continuous_fst.continuousOn.prodMk (hφs.comp continuous_snd.continuousOn
        fun q hq => hq.2)
    have hmt : Set.MapsTo (fun q : ComplexPoints f × ℝ => (q.1, φc.symm (p + q.2 • (w - p))))
        ((Wa : Set (ComplexPoints f)) ×ˢ Set.Icc 0 1)
        {xt : ComplexPoints f × ComplexPoints sJ |
          pair xt.1 xt.2 ∈ chart (sX := prodHom f sJ) ((pullback f sJ).basicOpen G)} :=
      fun q hq => hmem q.1 hq.1 _ (hγ q.2 hq.2)
    have h3 := hcj.comp hmap hmt
    exact h3
  have hGd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContMDiffOn 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 𝓘(ℂ, ℂ) ∞
      (fun x => ∑ i, (w - p) i * evalE _ (hf i) (pair x (φc.symm (p + s • (w - p)))))
      (Wa : Set (ComplexPoints f)) := by
    intro s hs
    refine contMDiffOn_finset_sum fun i _ => contMDiffOn_const.mul ?_
    exact (contMDiffOn_evalE_pair f sJ Θ hΘ _ (hf i) _).mono
      fun x hx => hmem x hx _ (hγ s hs)
  exact contMDiffOn_const.mul (Ana.contMDiffOn_intervalIntegral Wa.isOpen hGc hGd)

/-- A linear image of segment integrals of holomorphic functions is `C¹`. -/
theorem contDiffOn_linear_segmentIntegral {n : ℕ} {K : Type} [Fintype K]
    (ℓ : (K → ℂ) →ₗ[ℂ] (Fin n → ℂ)) {Ω : Set (Fin n → ℂ)} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {p : Fin n → ℂ} (hp : p ∈ Ω) (G : K → (Fin n → ℂ) → ℂ)
    (hG : ∀ k, DifferentiableOn ℂ (G k) Ω) (idx : K → Fin n) :
    ContDiffOn ℂ 1 (fun w => ℓ (fun k => (2 * Real.pi * Complex.I)⁻¹ *
      ∫ s in (0 : ℝ)..1, (w - p) (idx k) * G k (p + s • (w - p)))) Ω := by
  have hb : ContDiffOn ℂ 1 (fun w => fun k => (2 * Real.pi * Complex.I)⁻¹ *
      ∫ s in (0 : ℝ)..1, (w - p) (idx k) * G k (p + s • (w - p))) Ω :=
    contDiffOn_pi.2 fun k => contDiffOn_const.mul
      ((analyticOnNhd_segmentIntegral hΩo hΩc hp (hG k) (idx k)).contDiffOn hΩo.uniqueDiffOn)
  exact (LinearMap.toContinuousLinearMap ℓ).contDiff.comp_contDiffOn hb

section ValueLemmas

variable [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]

/-- Under `Θ`, the endomorphism `m a` of `𝒪_{C^an}` acts as multiplication by `a`. -/
theorem theta_m (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (m : ℂ → (anO f ⟶ anO f))
    (hm : ∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s)
    (a : ℂ) {W : Opens (space f)} (s : (structureSheaf f).obj.obj (op W)) (x : W) :
    Θ.hom.hom.app (op W) (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) x =
      a * Θ.hom.hom.app (op W) s x := by
  rw [hm a W s, theta_mul]
  congr 1
  exact theta_constSection Θ hΘ W a x

/-- `theta_exp` stated through `uval`. -/
theorem uval_e (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (e : anO f ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification f))
    (he : ∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    {W : Opens (space f)} (s : (structureSheaf f).obj.obj (op W)) (x : W) :
    uval Θ (e.hom.app (op W) s) x =
      Complex.exp (2 * Real.pi * Complex.I * Θ.hom.hom.app (op W) s x) :=
  theta_exp Θ hΘ e he W s x

/-- Under `Θ`, a restricted analytified regular function takes the values of the function. -/
theorem theta_analytificationHom_res (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    {U : C.Opens} (g : Γ(C, U)) {W : Opens (space f)}
    (hle : W ≤ (Opens.map (toSchemeHom f)).obj U) (x : W) :
    Θ.hom.hom.app (op W) ((structureSheaf f).obj.map (homOfLE hle).op
      ((analytificationHom f).hom.c.app (op U) g)) x = evalE U g x.1 := by
  refine (theta_res Θ hle _ x).trans ((hΘ _ _ ⟨x.1, hle x.2⟩).trans ?_)
  rw [evalE_of_mem _ (mem_chart_iff.2 (hle x.2))]
  rfl

end ValueLemmas

/-- **A cochain identity of units from the values.** -/
theorem unitsCochain_eq_of_values [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (e : anO f ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification f))
    (he : ∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    {Ai : Type} (W : Ai → Opens (space f))
    (zw zp : CechCochains.Cochain W
      (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj 1)
    (lam : CechCochains.Cochain W (anO f).obj 1) (Hc : CechCochains.Cochain W (anO f).obj 0)
    (hval : ∀ (σ : Fin 2 → Ai) (x : CechCochains.inter W σ),
      uval Θ (zw σ) x = uval Θ (zp σ) x *
        Complex.exp (2 * Real.pi * Complex.I * Θ.hom.hom.app (op _) (lam σ) x) *
        (Complex.exp (2 * Real.pi * Complex.I *
            Θ.hom.hom.app (op _) (Hc (σ ∘ Fin.succAbove 0))
              ⟨x.1, CechCochains.inter_le_omit W σ 0 x.2⟩) *
          (Complex.exp (2 * Real.pi * Complex.I *
            Θ.hom.hom.app (op _) (Hc (σ ∘ Fin.succAbove 1))
              ⟨x.1, CechCochains.inter_le_omit W σ 1 x.2⟩))⁻¹)) :
    zw = zp + Stacks.Cohomology.CechOne.push W e.hom 1 lam +
      CechCochains.cechD W _ 0 (Stacks.Cohomology.CechOne.push W e.hom 0 Hc) := by
  funext σ
  refine uval_ext Θ fun x => ?_
  rw [hval σ x, CechCochains.Cochain.add_apply, CechCochains.Cochain.add_apply, uval_add, uval_add,
    Stacks.Cohomology.CechOne.push_apply]
  erw [uval_e f Θ hΘ e he]
  rw [CechCochains.cechD_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  rw [uval_add, uval_neg, uval_restr, uval_restr,
    Stacks.Cohomology.CechOne.push_apply, Stacks.Cohomology.CechOne.push_apply]
  erw [uval_e f Θ hΘ e he, uval_e f Θ hΘ e he]

/-- Under `Θ`, the value of `lamCochain` at a point is `∑ₖ bₖ · Pₖ`, evaluated there. -/
theorem theta_lamCochain [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f])
    (hΘ : ∀ (V : C.Opens) (g : Γ(C, V)) (y : (Opens.map (toSchemeHom f)).obj V),
      Θ.hom.hom.app (op _) ((analytificationHom f).hom.c.app (op V) g) y =
        evalHom V ⟨y.1, mem_chart_iff.2 y.2⟩ g)
    (m : ℂ → (anO f ⟶ anO f))
    (hm : ∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s)
    {A : Type} {W : A → Opens (space f)} {K : Type} [Fintype K]
    (Pc : K → CechCochains.Cochain W (anO f).obj 1) (b : K → ℂ) (σ : Fin 2 → A)
    (x : CechCochains.inter W σ) :
    Θ.hom.hom.app (op _) (lamCochain f m Pc b σ) x =
      ∑ k, b k * Θ.hom.hom.app (op _) (Pc k σ) x := by
  let ev : (anO f).obj.obj (op (CechCochains.inter W σ)) →+ ℂ :=
    AddMonoidHom.mk' (fun t => Θ.hom.hom.app (op _)
      (show (structureSheaf f).obj.obj (op (CechCochains.inter W σ)) from t) x)
      (fun a b => theta_add Θ a b x)
  have h1 : lamCochain f m Pc b σ =
      ∑ k, Stacks.Cohomology.CechOne.push W (m (b k)).hom 1 (Pc k) σ :=
    Finset.sum_apply _ _ _
  change ev (lamCochain f m Pc b σ) = _
  rw [h1, map_sum]
  exact Finset.sum_congr rfl fun k _ => theta_m f Θ hΘ m hm (b k) (Pc k σ) x

/-- A Čech `1`-cochain of `anO f` is a cocycle once its `Θ`-values satisfy the cocycle identity
on every triple overlap. -/
theorem mem_cocycles1_of_theta [ChartedSpace (EuclideanSpace ℂ (Fin 1)) (ComplexPoints f)]
    (Θ : structureSheaf f ≅ 𝒪[1, ComplexPoints f]) {A : Type} {W : A → Opens (space f)}
    (c : CechCochains.Cochain W (anO f).obj 1)
    (hc : ∀ (τ : Fin 3 → A) (x : CechCochains.inter W τ),
      Θ.hom.hom.app (op _) (c (τ ∘ Fin.succAbove 0))
          ⟨x.1, CechCochains.inter_le_omit W τ 0 x.2⟩ -
        Θ.hom.hom.app (op _) (c (τ ∘ Fin.succAbove 1))
          ⟨x.1, CechCochains.inter_le_omit W τ 1 x.2⟩ +
        Θ.hom.hom.app (op _) (c (τ ∘ Fin.succAbove 2))
          ⟨x.1, CechCochains.inter_le_omit W τ 2 x.2⟩ = 0) :
    c ∈ CechCochains.cocycles1 W (anO f).obj := by
  rw [CechCochains.mem_cocycles1_iff]
  funext τ
  apply theta_ext Θ
  intro x
  let ev : (anO f).obj.obj (op (CechCochains.inter W τ)) →+ ℂ :=
    AddMonoidHom.mk' (fun t => Θ.hom.hom.app (op _)
      (show (structureSheaf f).obj.obj (op (CechCochains.inter W τ)) from t) x)
      (fun a b => theta_add Θ a b x)
  change ev (CechCochains.cechD W _ 1 c τ) = ev 0
  rw [map_zero, CechCochains.cechD_apply, map_sum, Fin.sum_univ_three]
  simp only [map_zsmul]
  have hres : ∀ j : Fin 3, ev (CechCochains.restr _ (CechCochains.inter_le_omit W τ j)
      (c (τ ∘ Fin.succAbove j))) = Θ.hom.hom.app (op _) (c (τ ∘ Fin.succAbove j))
        ⟨x.1, CechCochains.inter_le_omit W τ j x.2⟩ := fun j => theta_res Θ _ _ x
  rw [hres, hres, hres]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, Even.neg_pow even_two, one_pow, smul_eq_mul]
  linear_combination hc τ x

/-- A sum over the `Σ`-type of terms supported on `(c₀, c₁)` reduces to a sum over that fibre. -/
theorem sum_sigma_ite {n r : ℕ} {L : Fin n → Fin r → Fin r → ℕ} (c₀ c₁ : Fin r)
    (b G : (Σ (i : Fin n) (c d : Fin r), Fin (L i c d)) → ℂ) :
    (∑ k, b k * (if c₀ = k.2.1 ∧ c₁ = k.2.2.1 then G k else 0)) =
      ∑ i, ∑ l : Fin (L i c₀ c₁), b ⟨i, c₀, c₁, l⟩ * G ⟨i, c₀, c₁, l⟩ := by
  classical
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single c₀]
  · rw [Fintype.sum_sigma, Finset.sum_eq_single c₁]
    · simp
    · intro d _ hd
      refine Finset.sum_eq_zero fun l _ => ?_
      simp [Ne.symm hd]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [Ne.symm hc]
  · simp

/-- If `F₁ - F₂ + F₃` vanishes on `[0, 1]`, so does the same combination of their integrals. -/
theorem intervalIntegral_sub_add_eq_zero {F₁ F₂ F₃ : ℝ → ℂ}
    (h₁ : IntervalIntegrable F₁ volume 0 1) (h₂ : IntervalIntegrable F₂ volume 0 1)
    (h₃ : IntervalIntegrable F₃ volume 0 1) (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, F₁ s - F₂ s + F₃ s = 0) :
    (∫ s in (0 : ℝ)..1, F₁ s) - (∫ s in (0 : ℝ)..1, F₂ s) + ∫ s in (0 : ℝ)..1, F₃ s = 0 := by
  rw [← intervalIntegral.integral_sub h₁ h₂, ← intervalIntegral.integral_add (h₁.sub h₂) h₃,
    ← intervalIntegral.integral_zero (a := (0 : ℝ)) (b := 1) (μ := volume) (E := ℂ)]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  exact h s hs

/-- **Logarithms of the family of slice classes.** Near `e₀`, in étale coordinates `c`, the slice
class at `y` is the image under `e` of `φ (L (c y))` for a `C¹` map `L` on an open `Ω ∋ c e₀`. -/
theorem exists_etaleCoordinateChart_sliceClass_eq [IsProper f] [SmoothOfRelativeDimension 1 f]
    [ConnectedSpace C]
    {n : ℕ} [SmoothOfRelativeDimension n sJ] [LocallyOfFiniteType sJ] [QuasiCompact sJ]
    (M : SheafOfModules.{0} (Stacks.RingedSpace.structureRingSheaf (pullback f sJ).toRingedSpace))
    (hM : Stacks.SheafOfModules.IsInvertible (pullback f sJ).toRingedSpace.sheaf.obj
      (structureSheafRing (pullback f sJ).toRingedSpace).property M)
    (e₀ : ComplexPoints sJ) (he₀ : sliceClass f sJ M hM e₀ = 0)
    (e : anO f ⟶ Stacks.Cohomology.Generators.unitsSheaf (analytification f))
    (he : ∀ (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)) (x : W)
        (c : {c : Chart f // x.1 ∈ ComplexPoints.chart c.U}) (g : (Fin c.1.n → ℂ) → ℂ)
        (γ γ' : holGerms (c.1.coords ⟨x.1, c.2⟩)),
        (γ : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) = g →
        (γ' : Germ (𝓝 (c.1.coords ⟨x.1, c.2⟩)) ℂ) =
          (fun z => Complex.exp (2 * Real.pi * Complex.I * g z)) →
        s.1 x c = Chart.StalkRing.mk c.1 _ γ →
        ((Additive.toMul (e.hom.app (op W) s) : ((structureSheaf f).obj.obj (op W))ˣ) :
          (structureSheaf f).obj.obj (op W)).1 x c = Chart.StalkRing.mk c.1 _ γ')
    (m : ℂ → (anO f ⟶ anO f))
    (hm : ∀ (a : ℂ) (W : Opens (space f)) (s : (structureSheaf f).obj.obj (op W)),
        (show (structureSheaf f).obj.obj (op W) from (m a).hom.app (op W) s) =
          (show (structureSheaf f).obj.obj (op W) from
            (structureSheaf f).obj.map (homOfLE (le_top : W ≤ ⊤)).op
              (show (structureSheaf f).obj.obj (op ⊤) from
                (ringCatSheafHom f).hom.app (op ⊤) (baseRingHom f ⊤ a))) * s)
    (hmadd : ∀ a b : ℂ, m (a + b) = m a + m b) (hmmul : ∀ a b : ℂ, m (a * b) = m b ≫ m a)
    (φ : (Fin n → ℂ) ≃+ Sheaf.H (anO f) 1)
    (hφ : ∀ (a : ℂ) (v : Fin n → ℂ), φ (a • v) = Sheaf.H.map (m a) 1 (φ v)) :
    ∃ (c : EtaleCoordinateChart sJ n) (L : (Fin n → ℂ) → (Fin n → ℂ)) (Ω : Set (Fin n → ℂ)),
      IsOpen Ω ∧ ContDiffOn ℂ 1 L Ω ∧ e₀ ∈ c.W ∧ c.toOpenPartialHomeomorph e₀ ∈ Ω ∧
      ∀ y ∈ c.W, c.toOpenPartialHomeomorph y ∈ Ω →
        sliceClass f sJ M hM y =
          (Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
            (space f) (Stacks.Cohomology.Generators.unitsSheaf (analytification f)))).symm
            (Sheaf.H.map e 1 (φ (L (c.toOpenPartialHomeomorph y)))) := by
  classical
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI : Smooth sJ := SmoothOfRelativeDimension.smooth n sJ
  haveI : IsReduced (pullback f sJ) := isReduced_of_smooth (prodHom f sJ)
  obtain ⟨cs, hman, Θ, hΘ⟩ := exists_theta_curve f
  letI := cs
  obtain ⟨V, hV, z, hz, W₀, hW₀, hW₀o, he₀W, hemb⟩ := exists_affine_etaleChart sJ (n := n) e₀
  let c : EtaleCoordinateChart sJ n := ⟨V, z, hz, W₀, hW₀, hW₀o, ⟨e₀, he₀W⟩, hemb⟩
  set φc := c.toOpenPartialHomeomorph
  obtain ⟨r, A, hA, hA2, hAcov⟩ := exists_affine_cover_fin f
  choose s F hF hε using fun c' => exists_standardCover_generators (pullback f sJ) M hM
    (isAffineOpen_box (f := f) (sJ := sJ) (hA c') hV)
  let ε : ∀ j : Σ c', Fin (s c'), Stacks.SheafOfModules.GeneratorSections
      (pullback f sJ).toRingedSpace M (Nopen F j) := fun j => (hε j.1).some j.2
  obtain ⟨κ, h, L, P, R, hκ, hcoc, hdec⟩ :=
    exists_logDeriv_decomposition hV z hz A hA hA2 F hF M ε
  obtain ⟨Ai, W, ρ, B, hBo, he₀B, hcov, hWρ⟩ :=
    exists_tube f sJ A hA hAcov hV F hF e₀ (hW₀ he₀W)
  set p := φc e₀
  have hsrc : φc.source = W₀ := c.source_toOpenPartialHomeomorph
  have he₀src : e₀ ∈ φc.source := hsrc ▸ he₀W
  have hpT : p ∈ φc.target := φc.map_source he₀src
  have hpe : φc.symm p = e₀ := φc.left_inv he₀src
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, Metric.ball p δ ⊆ φc.target ∩ φc.symm ⁻¹' B := by
    have ho : IsOpen (φc.target ∩ φc.symm ⁻¹' B) := φc.isOpen_inter_preimage_symm hBo
    exact Metric.isOpen_iff.1 ho p ⟨hpT, by rwa [Set.mem_preimage, hpe]⟩
  set Ω := Metric.ball p δ
  have hΩT : ∀ w ∈ Ω, w ∈ φc.target := fun w hw => (hball hw).1
  have hΩB : ∀ w ∈ Ω, φc.symm w ∈ B := fun w hw => (hball hw).2
  have hΩW : ∀ w ∈ Ω, φc.symm w ∈ c.W := fun w hw => by
    have := φc.map_target (hΩT w hw)
    rwa [hsrc] at this
  have hpΩ : p ∈ Ω := Metric.mem_ball_self hδ
  choose zc hzv hzcls using fun w (hw : w ∈ Ω) => sliceClass_eq_cech f sJ Θ hΘ M hM (Nopen F) ε
    W hcov ρ (φc.symm w) (fun a x hx => hWρ a x hx _ (hΩB w hw))
  have hWA : ∀ a, ∀ x ∈ W a, x ∈ chart (A (ρ a).1) := fun a x hx =>
    (mem_chart_of_pair_mem_box (chart_mono ((pullback f sJ).basicOpen_le _)
      (hWρ a x hx e₀ he₀B))).1
  let K := Σ (i : Fin n) (c' d : Fin r), Fin (L i c' d)
  have hle : ∀ (σ : Fin 2 → Ai) (c' d : Fin r), (ρ (σ 0)).1 = c' ∧ (ρ (σ 1)).1 = d →
      CechCochains.inter W σ ≤ (Opens.map (toSchemeHom f)).obj (A c' ⊓ A d) := by
    rintro σ c' d ⟨rfl, rfl⟩ x hx
    exact ⟨mem_chart_iff.1 (hWA (σ 0) x ((iInf_le (fun k => W (σ k)) 0) hx)),
      mem_chart_iff.1 (hWA (σ 1) x ((iInf_le (fun k => W (σ k)) 1) hx))⟩
  let Pc : K → CechCochains.Cochain W (anO f).obj 1 := fun k σ =>
    if hk : (ρ (σ 0)).1 = k.2.1 ∧ (ρ (σ 1)).1 = k.2.2.1 then
      (show (structureSheaf f).obj.obj (op (CechCochains.inter W σ)) from
        (structureSheaf f).obj.map (homOfLE (hle σ _ _ hk)).op
          ((analytificationHom f).hom.c.app (op (A k.2.1 ⊓ A k.2.2.1))
            (P k.1 k.2.1 k.2.2.1 k.2.2.2)))
    else 0
  choose GR hGRa hGRe using fun k : K => c.exists_analyticOnNhd V (R k.1 k.2.1 k.2.2.1 k.2.2.2)
  let bvec : (Fin n → ℂ) → K → ℂ := fun w k =>
    (2 * Real.pi * Complex.I)⁻¹ * ∫ s in (0 : ℝ)..1, (w - p) k.1 * GR k (p + s • (w - p))
  have hHex : ∀ w ∈ Ω, ∀ a : Ai, ∃ σ : (structureSheaf f).obj.obj (op (W a)),
      ∀ x : W a, Θ.hom.hom.app (op (W a)) σ x = (2 * Real.pi * Complex.I)⁻¹ *
        ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i *
          evalE _ (h i (ρ a)) (pair x.1 (φc.symm (p + s • (w - p)))) := by
    intro w hw a
    refine exists_section_of_contMDiffOn Θ (W a) (g := fun x => (2 * Real.pi * Complex.I)⁻¹ *
        ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i *
          evalE _ (h i (ρ a)) (pair x (φc.symm (p + s • (w - p))))) ?_
    exact contMDiffOn_sliceIntegral f sJ Θ hΘ (hA (ρ a).1) hV (F (ρ a).1 (ρ a).2)
      (fun i => h i (ρ a)) (W a) φc (convex_ball p δ) hpΩ hw hΩT
      (fun x hx v hv => hWρ a x hx _ (hΩB v hv))
  choose Hs hHs using hHex
  let Hc : ∀ w, w ∈ Ω → CechCochains.Cochain W (anO f).obj 0 := fun w hw σ =>
    (show (structureSheaf f).obj.obj (op (CechCochains.inter W σ)) from
      (structureSheaf f).obj.map (homOfLE (iInf_le (fun k => W (σ k)) 0)).op (Hs w hw (σ 0)))
  obtain ⟨ℓ, hℓ⟩ := exists_linear_cechLog f m hmadd hmmul φ hφ W hcov Pc
  refine ⟨c, fun w => ℓ (bvec w), Ω, Metric.isOpen_ball, ?_, he₀W, hpΩ, ?_⟩
  · refine contDiffOn_linear_segmentIntegral ℓ Metric.isOpen_ball (convex_ball p δ) hpΩ GR
      (fun k v hv => ?_) (fun k => k.1)
    exact (hGRa k v ⟨hΩT v hv, hW₀ (hΩW v hv)⟩).differentiableAt.differentiableWithinAt
  · intro y hy hyΩ
    set w := φc y
    have hyw : φc.symm w = y := φc.left_inv (hsrc ▸ hy)
    have hPc : ∀ (kk : K) (σ : Fin 2 → Ai) (x : CechCochains.inter W σ),
        Θ.hom.hom.app (op _) (Pc kk σ) x =
          if (ρ (σ 0)).1 = kk.2.1 ∧ (ρ (σ 1)).1 = kk.2.2.1 then
            evalE (A kk.2.1 ⊓ A kk.2.2.1) (P kk.1 kk.2.1 kk.2.2.1 kk.2.2.2) x.1 else 0 := by
      intro kk σ x
      by_cases hk : (ρ (σ 0)).1 = kk.2.1 ∧ (ρ (σ 1)).1 = kk.2.2.1
      · rw [if_pos hk, show Pc kk σ = _ from dif_pos hk]
        exact theta_analytificationHom_res f Θ hΘ _ (hle σ _ _ hk) x
      · rw [if_neg hk, show Pc kk σ = 0 from dif_neg hk]
        change Θ.hom.hom.app (op _) (0 : (structureSheaf f).obj.obj (op _)) x = 0
        rw [map_zero]
        rfl
    let S : Ai → Ai → ComplexPoints f → Fin n → (Fin n → ℂ) → ℂ := fun a b x i v =>
      ∑ l, evalE (A (ρ a).1 ⊓ A (ρ b).1) (P i (ρ a).1 (ρ b).1 l) x *
        GR ⟨i, (ρ a).1, (ρ b).1, l⟩ v
    have hSc : ∀ a b x i, ContinuousOn (S a b x i) Ω := fun a b x i =>
      continuousOn_finset_sum _ fun l _ => continuousOn_const.mul
        ((hGRa _).continuousOn.mono fun v hv => ⟨hΩT v hv, hW₀ (hΩW v hv)⟩)
    have hlv : ∀ (σ : Fin 2 → Ai) (x : CechCochains.inter W σ),
        Θ.hom.hom.app (op _) (lamCochain f m Pc (bvec w) σ) x =
          (2 * Real.pi * Complex.I)⁻¹ * ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i *
            S (σ 0) (σ 1) x.1 i (p + s • (w - p)) := by
      intro σ x
      rw [theta_lamCochain f Θ hΘ m hm Pc (bvec w) σ x]
      simp_rw [hPc _ σ x]
      rw [sum_sigma_ite]
      have := Ana.sum_sum_mul_integral (convex_ball p δ) hpΩ hyΩ
        (fun i l => evalE (A (ρ (σ 0)).1 ⊓ A (ρ (σ 1)).1) (P i (ρ (σ 0)).1 (ρ (σ 1)).1 l) x.1)
        (fun i l => GR ⟨i, (ρ (σ 0)).1, (ρ (σ 1)).1, l⟩)
        (fun i l => (hGRa _).continuousOn.mono fun v hv => ⟨hΩT v hv, hW₀ (hΩW v hv)⟩)
      simp only [S]
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [bvec]
      ring
    have hS : ∀ (a b d : Ai) (x : ComplexPoints f), x ∈ W a → x ∈ W b → x ∈ W d →
        ∀ v ∈ Ω, ∀ i, S a b x i v + S b d x i v = S a d x i v := by
      intro a b d x hxa hxb hxd v hv i
      have htV : φc.symm v ∈ chart V := hW₀ (hΩW v hv)
      have hφv : φc (φc.symm v) = v := φc.right_inv (hΩT v hv)
      have hqa := hWρ a x hxa _ (hΩB v hv)
      have hqb := hWρ b x hxb _ (hΩB v hv)
      have hqd := hWρ d x hxd _ (hΩB v hv)
      have hAa := hWA a x hxa
      have hAb := hWA b x hxb
      have hAd := hWA d x hxd
      have hsep : ∀ (j k : Ai)
          (hqj : pair x (φc.symm v) ∈ chart (sX := prodHom f sJ) (Nopen F (ρ j)))
          (hqk : pair x (φc.symm v) ∈ chart (sX := prodHom f sJ) (Nopen F (ρ k)))
          (hx : x ∈ chart (A (ρ j).1 ⊓ A (ρ k).1)),
          S j k x i v = eval _ (κ i (ρ j) (ρ k)) ⟨pair x (φc.symm v),
            mem_chart_iff.2 ⟨mem_chart_iff.1 hqj, mem_chart_iff.1 hqk⟩⟩ -
            eval _ (h i (ρ k)) ⟨_, hqk⟩ + eval _ (h i (ρ j)) ⟨_, hqj⟩ := by
        intro j k hqj hqk hx
        rw [hdec i (ρ j) (ρ k) x _ hqj hqk hx htV]
        simp only [S]
        have : ∀ l, evalE (A (ρ j).1 ⊓ A (ρ k).1) (P i (ρ j).1 (ρ k).1 l) x *
            GR ⟨i, (ρ j).1, (ρ k).1, l⟩ v = eval _ (P i (ρ j).1 (ρ k).1 l) ⟨x, hx⟩ *
              eval V (R i (ρ j).1 (ρ k).1 l) ⟨φc.symm v, htV⟩ := by
          intro l
          rw [evalE_of_mem _ hx, hGRe ⟨i, (ρ j).1, (ρ k).1, l⟩ _ (hΩW v hv) htV, hφv]
        simp_rw [this]
        ring
      have hx2 : ∀ {j k : Ai}, x ∈ chart (A (ρ j).1) → x ∈ chart (A (ρ k).1) →
          x ∈ chart (A (ρ j).1 ⊓ A (ρ k).1) := fun h1 h2 =>
        mem_chart_iff.2 ⟨mem_chart_iff.1 h1, mem_chart_iff.1 h2⟩
      rw [hsep a b hqa hqb (hx2 hAa hAb), hsep b d hqb hqd (hx2 hAb hAd),
        hsep a d hqa hqd (hx2 hAa hAd)]
      linear_combination hcoc i (ρ a) (ρ b) (ρ d) (pair x (φc.symm v)) hqa hqb hqd
    have hlam : lamCochain f m Pc (bvec w) ∈ CechCochains.cocycles1 W (anO f).obj := by
      refine mem_cocycles1_of_theta f Θ _ fun τ x => ?_
      have hxj : ∀ j : Fin 3, x.1 ∈ W (τ j) := fun j => (iInf_le (fun k => W (τ k)) j) x.2
      have t0 : Θ.hom.hom.app (op _) (lamCochain f m Pc (bvec w) (τ ∘ Fin.succAbove 0))
          ⟨x.1, CechCochains.inter_le_omit W τ 0 x.2⟩ = (2 * Real.pi * Complex.I)⁻¹ *
            ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * S (τ 1) (τ 2) x.1 i (p + s • (w - p)) :=
        hlv _ _
      have t1 : Θ.hom.hom.app (op _) (lamCochain f m Pc (bvec w) (τ ∘ Fin.succAbove 1))
          ⟨x.1, CechCochains.inter_le_omit W τ 1 x.2⟩ = (2 * Real.pi * Complex.I)⁻¹ *
            ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * S (τ 0) (τ 2) x.1 i (p + s • (w - p)) :=
        hlv _ _
      have t2 : Θ.hom.hom.app (op _) (lamCochain f m Pc (bvec w) (τ ∘ Fin.succAbove 2))
          ⟨x.1, CechCochains.inter_le_omit W τ 2 x.2⟩ = (2 * Real.pi * Complex.I)⁻¹ *
            ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * S (τ 0) (τ 1) x.1 i (p + s • (w - p)) :=
        hlv _ _
      rw [t0, t1, t2]
      have hγ : ∀ s ∈ Set.Icc (0 : ℝ) 1, p + s • (w - p) ∈ Ω := fun s hs =>
        (convex_ball p δ).add_smul_sub_mem hpΩ hyΩ hs
      have hint : ∀ a b, IntervalIntegrable (fun s : ℝ => ∑ i, (w - p) i *
          S a b x.1 i (p + s • (w - p))) MeasureTheory.volume 0 1 := fun a b =>
        (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul ((hSc a b x.1 i).comp
          (Continuous.continuousOn (by fun_prop)) fun s hs => hγ s hs)).intervalIntegrable_of_Icc
          zero_le_one
      have hsum : (∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * S (τ 1) (τ 2) x.1 i (p + s • (w - p))) -
          (∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * S (τ 0) (τ 2) x.1 i (p + s • (w - p))) +
          (∫ s in (0 : ℝ)..1, ∑ i, (w - p) i * S (τ 0) (τ 1) x.1 i (p + s • (w - p))) = 0 := by
        refine intervalIntegral_sub_add_eq_zero (hint (τ 1) (τ 2)) (hint (τ 0) (τ 2))
          (hint (τ 0) (τ 1)) fun s hs => ?_
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun i _ => ?_
        linear_combination
          (w - p) i * hS (τ 0) (τ 1) (τ 2) x.1 (hxj 0) (hxj 1) (hxj 2) _ (hγ s hs) i
      linear_combination (2 * Real.pi * Complex.I)⁻¹ * hsum
    have hval : ∀ (σ : Fin 2 → Ai) (x : CechCochains.inter W σ),
        uval Θ ((zc w hyΩ).val σ) x = uval Θ ((zc p hpΩ).val σ) x *
          Complex.exp (2 * Real.pi * Complex.I *
            Θ.hom.hom.app (op _) (lamCochain f m Pc (bvec w) σ) x) *
          (Complex.exp (2 * Real.pi * Complex.I *
              Θ.hom.hom.app (op _) (Hc w hyΩ (σ ∘ Fin.succAbove 0))
                ⟨x.1, CechCochains.inter_le_omit W σ 0 x.2⟩) *
            (Complex.exp (2 * Real.pi * Complex.I *
              Θ.hom.hom.app (op _) (Hc w hyΩ (σ ∘ Fin.succAbove 1))
                ⟨x.1, CechCochains.inter_le_omit W σ 1 x.2⟩))⁻¹) := by
      intro σ x
      have hx0 : x.1 ∈ W (σ 0) := (iInf_le (fun k => W (σ k)) 0) x.2
      have hx1 : x.1 ∈ W (σ 1) := (iInf_le (fun k => W (σ k)) 1) x.2
      have hq0 : ∀ v ∈ Ω, pair x.1 (φc.symm v) ∈ chart (sX := prodHom f sJ) (Nopen F (ρ (σ 0))) :=
        fun v hv => hWρ _ _ hx0 _ (hΩB v hv)
      have hq1 : ∀ v ∈ Ω, pair x.1 (φc.symm v) ∈ chart (sX := prodHom f sJ) (Nopen F (ρ (σ 1))) :=
        fun v hv => hWρ _ _ hx1 _ (hΩB v hv)
      have hmem : ∀ v ∈ Ω, pair x.1 (φc.symm v) ∈
          chart (sX := prodHom f sJ) (Nopen F (ρ (σ 0)) ⊓ Nopen F (ρ (σ 1))) := fun v hv =>
        mem_chart_iff.2 ⟨mem_chart_iff.1 (hq0 v hv), mem_chart_iff.1 (hq1 v hv)⟩
      have hxA : x.1 ∈ chart (A (ρ (σ 0)).1 ⊓ A (ρ (σ 1)).1) :=
        mem_chart_iff.2 ⟨mem_chart_iff.1 (hWA _ _ hx0), mem_chart_iff.1 (hWA _ _ hx1)⟩
      have hcU : ∀ {N : (pullback f sJ).Opens} (g : Γ(pullback f sJ, N)),
          (∀ v ∈ Ω, pair x.1 (φc.symm v) ∈ chart (sX := prodHom f sJ) N) →
          ContinuousOn (fun v => evalE N g (pair x.1 (φc.symm v))) Ω := by
        intro N g hN
        refine (continuousOn_evalE N g).comp ?_ hN
        exact ((continuous_pair_right (f := f) (sJ := sJ) x.1).comp_continuousOn
          φc.continuousOn_symm).mono fun v hv => hΩT v hv
      have hcore := Ana.eq_mul_exp_of_decomposition (convex_ball p δ) Metric.isOpen_ball hpΩ hyΩ
        (U := fun v => evalE _ (transUnit F M ε (ρ (σ 0)) (ρ (σ 1)) :
          Γ(pullback f sJ, Nopen F (ρ (σ 0)) ⊓ Nopen F (ρ (σ 1)))) (pair x.1 (φc.symm v)))
        (κ := fun i v => evalE _ (κ i (ρ (σ 0)) (ρ (σ 1))) (pair x.1 (φc.symm v)))
        (fun v hv => by
          have htW : φc.symm v ∈ W₀ := hΩW v hv
          obtain ⟨Fu, Fu', hFd, hFe, hFv⟩ := hκ (ρ (σ 0)) (ρ (σ 1)) x.1 (φc.symm v) (hmem v hv)
            W₀ hW₀ hW₀o ⟨e₀, he₀W⟩ hemb htW
          have hφv : φc (φc.symm v) = v := φc.right_inv (hΩT v hv)
          have hFd' : HasFDerivAt Fu Fu' v := by rwa [← hφv]
          have hFe' : ∀ᶠ w' in 𝓝 v, ∃ hw' : pair x.1 (φc.symm w') ∈
              chart (sX := prodHom f sJ) (Nopen F (ρ (σ 0)) ⊓ Nopen F (ρ (σ 1))),
              Fu w' = eval _ (transUnit F M ε (ρ (σ 0)) (ρ (σ 1)) :
                Γ(pullback f sJ, Nopen F (ρ (σ 0)) ⊓ Nopen F (ρ (σ 1)))) ⟨_, hw'⟩ := by
            rwa [← hφv]
          refine ⟨Fu', hFd'.congr_of_eventuallyEq ?_, fun i => ?_⟩
          · filter_upwards [hFe'] with w' ⟨hw', e'⟩
            rw [evalE_of_mem _ hw']
            exact e'.symm
          · rw [hFv i, evalE_of_mem _ (hmem v hv), evalE_of_mem _ (hmem v hv)])
        (fun i l => evalE (A (ρ (σ 0)).1 ⊓ A (ρ (σ 1)).1) (P i (ρ (σ 0)).1 (ρ (σ 1)).1 l) x.1)
        (fun i l => GR ⟨i, (ρ (σ 0)).1, (ρ (σ 1)).1, l⟩)
        (fun i l => (hGRa _).continuousOn.mono fun v hv => ⟨hΩT v hv, hW₀ (hΩW v hv)⟩)
        (fun i v => evalE _ (h i (ρ (σ 0))) (pair x.1 (φc.symm v)))
        (fun i v => evalE _ (h i (ρ (σ 1))) (pair x.1 (φc.symm v)))
        (fun i => hcU _ hq0) (fun i => hcU _ hq1)
        (fun i v hv => by
          have htV : φc.symm v ∈ chart V := hW₀ (hΩW v hv)
          have hd := hdec i (ρ (σ 0)) (ρ (σ 1)) x.1 (φc.symm v) (hq0 v hv) (hq1 v hv) hxA htV
          have hφv : φc (φc.symm v) = v := φc.right_inv (hΩT v hv)
          rw [evalE_of_mem _ (hmem v hv), evalE_of_mem _ (hq0 v hv), evalE_of_mem _ (hq1 v hv),
            hd]
          congr 2
          refine Finset.sum_congr rfl fun l _ => ?_
          have hR : eval V (R i (ρ (σ 0)).1 (ρ (σ 1)).1 l) ⟨φc.symm v, htV⟩ =
              GR ⟨i, (ρ (σ 0)).1, (ρ (σ 1)).1, l⟩ v :=
            (hGRe ⟨i, (ρ (σ 0)).1, (ρ (σ 1)).1, l⟩ _ (hΩW v hv) htV).trans (by rw [hφv])
          rw [evalE_of_mem _ hxA, hR])
      have eUw : evalE _ (transUnit F M ε (ρ (σ 0)) (ρ (σ 1)) :
          Γ(pullback f sJ, Nopen F (ρ (σ 0)) ⊓ Nopen F (ρ (σ 1)))) (pair x.1 (φc.symm w)) =
            uval Θ ((zc w hyΩ).val σ) x :=
        (evalE_of_mem _ (hmem w hyΩ)).trans (hzv w hyΩ σ x (hmem w hyΩ)).symm
      have eUp : evalE _ (transUnit F M ε (ρ (σ 0)) (ρ (σ 1)) :
          Γ(pullback f sJ, Nopen F (ρ (σ 0)) ⊓ Nopen F (ρ (σ 1)))) (pair x.1 (φc.symm p)) =
            uval Θ ((zc p hpΩ).val σ) x :=
        (evalE_of_mem _ (hmem p hpΩ)).trans (hzv p hpΩ σ x (hmem p hpΩ)).symm
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hlamv : 2 * Real.pi * Complex.I *
          Θ.hom.hom.app (op _) (lamCochain f m Pc (bvec w) σ) x =
          ∑ i, ∑ l, evalE (A (ρ (σ 0)).1 ⊓ A (ρ (σ 1)).1) (P i (ρ (σ 0)).1 (ρ (σ 1)).1 l) x.1 *
            ∫ s in (0 : ℝ)..1, (w - p) i * GR ⟨i, (ρ (σ 0)).1, (ρ (σ 1)).1, l⟩
              (p + s • (w - p)) := by
        rw [theta_lamCochain f Θ hΘ m hm Pc (bvec w) σ x]
        simp_rw [hPc _ σ x]
        rw [sum_sigma_ite, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [bvec]
        field_simp
      have hH0v : 2 * Real.pi * Complex.I *
          Θ.hom.hom.app (op _) (Hc w hyΩ (σ ∘ Fin.succAbove 0))
            ⟨x.1, CechCochains.inter_le_omit W σ 0 x.2⟩ =
          ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i *
            evalE _ (h i (ρ (σ 1))) (pair x.1 (φc.symm (p + s • (w - p)))) := by
        refine (congrArg (2 * Real.pi * Complex.I * ·) ?_).trans (mul_inv_cancel_left₀ h2pi _)
        exact (theta_res Θ (iInf_le (fun k => W ((σ ∘ Fin.succAbove 0) k)) 0) _ _).trans
          (hHs w hyΩ ((σ ∘ Fin.succAbove 0) 0) _)
      have hH1v : 2 * Real.pi * Complex.I *
          Θ.hom.hom.app (op _) (Hc w hyΩ (σ ∘ Fin.succAbove 1))
            ⟨x.1, CechCochains.inter_le_omit W σ 1 x.2⟩ =
          ∫ s in (0 : ℝ)..1, ∑ i, (w - p) i *
            evalE _ (h i (ρ (σ 0))) (pair x.1 (φc.symm (p + s • (w - p)))) := by
        refine (congrArg (2 * Real.pi * Complex.I * ·) ?_).trans (mul_inv_cancel_left₀ h2pi _)
        exact (theta_res Θ (iInf_le (fun k => W ((σ ∘ Fin.succAbove 1) k)) 0) _ _).trans
          (hHs w hyΩ ((σ ∘ Fin.succAbove 1) 0) _)
      rw [← eUw, ← eUp, hcore, hlamv, hH0v, hH1v, ← Complex.exp_neg, ← Complex.exp_add,
        mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    have hid : (zc w hyΩ).val = (zc p hpΩ).val +
        Stacks.Cohomology.CechOne.push W e.hom 1 (lamCochain f m Pc (bvec w)) +
        CechCochains.cechD W _ 0 (Stacks.Cohomology.CechOne.push W e.hom 0 (Hc w hyΩ)) :=
      unitsCochain_eq_of_values f Θ hΘ e he W _ _ _ _ hval
    let zlam : CechCochains.cocycles1 W
        (Stacks.Cohomology.Generators.unitsSheaf (analytification f)).obj :=
      ⟨_, Stacks.Cohomology.CechOne.cechD_push W e.hom 1 _ hlam⟩
    have hcls : CechCochains.cls W _ (zc w hyΩ) =
        CechCochains.cls W _ (zc p hpΩ) + CechCochains.cls W _ zlam := by
      have h0 : CechCochains.cls W _ (zc w hyΩ - zc p hpΩ - zlam) = 0 := by
        refine (CechCochains.cls_eq_zero_iff _ _ _).2
          ⟨Stacks.Cohomology.CechOne.push W e.hom 0 (Hc w hyΩ), ?_⟩
        rw [AddSubgroup.coe_sub, AddSubgroup.coe_sub, hid]
        change _ = _ + _ + _ - _ - Stacks.Cohomology.CechOne.push W e.hom 1 _
        abel
      simp only [CechCochains.cls, QuotientAddGroup.mk_sub] at h0 ⊢
      rwa [sub_sub, sub_eq_zero] at h0
    have hnat := Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections_naturality
      (analytification f : RingedSpace) ⊤ W hcov e ⟨_, hlam⟩ zlam (fun i => rfl)
    have hnat2 := sheafCohomologyOneExtEquiv_naturality (space f) e
      (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections (space f) ⊤ W hcov (anO f)
        (CechCochains.cls W _ ⟨_, hlam⟩))
    rw [← hyw, hzcls w hyΩ, hcls, map_add, ← hzcls p hpΩ, hpe, he₀]
    erw [zero_add]
    rw [hℓ (bvec w) hlam, ← hnat2, ← hnat]
    exact ((Iso.addCommGroupIsoToAddEquiv (Stacks.Thickenings.sheafCohomologyOneExtEquiv
      (space f) (Stacks.Cohomology.Generators.unitsSheaf (analytification f)))).symm_apply_apply
      _).symm

end Final

end Fam

end FamilyLogarithm

end MMP.JacobianLogarithm

end
