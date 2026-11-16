module

public import MMP.AlgebraicGeometry.RegularEmbedding.ConesBlowups
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.DegreeOneGeneration
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionRings
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SectionsUniversalInjectivity
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Absolute
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# Generation in degree one of the graded algebra of a cone

Let `s` be a relative `Proj` situation over a scheme `X`, with graded algebra `S^•`. Fulton's
conditions on `S^•` (`MMP.Intersection.Scheme.IsConeAlgebra`) ask that around every point there be
an affine open over which `S^•` is generated in degree one, in the additive-subgroup form
`SheafOfModules.GradedAlgebra.IsGeneratedInDegreeOne`. Here this is compared with the span form
of generation: over an affine open on which `S⁰ = 𝒪_X`, the sheaf-level generation holds if and
only if every section of `Sⁿ` is a combination of products of `n` sections of `S¹`. By
quasi-coherence, the span form then holds near every point of every open
(`Stacks.RelativeProj.Situation.IsLocallyDegreeOneGenerated`), so the graded ring of sections
over every affine open is generated in degree one, and the projective cone `Proj(S^•) ⟶ X` is
proper.

## Main results

* `MMP.RelativeProjSituation.mem_span_homogeneousPow_of_isGeneratedInDegreeOne` and
  `MMP.RelativeProjSituation.isGeneratedInDegreeOne_of_mem_span_homogeneousPow`: the two
  forms of generation in degree one over an open.
* `MMP.Intersection.Scheme.IsConeAlgebra.isLocallyDegreeOneGenerated`: the graded algebra of a
  cone is locally generated in degree one over every open.
* `MMP.Intersection.Scheme.IsConeAlgebra.adjoin_sectionRingGrading_one_eq_top`: over an affine
  open its ring of sections is generated in degree one.
* `MMP.Intersection.Scheme.IsConeAlgebra.isInvertibleModule_twistSheaf`: the twisting sheaves
  `𝒪_{Proj S^•}(n)` of a projective cone are invertible.
* `MMP.Intersection.Scheme.IsConeAlgebra.isProper_relativeProjToBase`: the projective cone is
  proper over the base (Fulton, Appendix B.5).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace MMP.RelativeProjSituation

open Stacks.RelativeProj Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- The ordered product of `w` with `b` appended is the product of the ordered product of `w`
with `b`. -/
theorem homogeneousPow_snoc (V : s.base.Opens) (n : ℕ)
    (w : Fin n → Γ(s.pieceModules (1 : ℤ), V)) (b : Γ(s.pieceModules (1 : ℤ), V)) :
    s.homogeneousPow V (n + 1) (Fin.snoc w b) = s.pieceMul n 1 V (s.homogeneousPow V n w) b := by
  rw [Situation.homogeneousPow_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- A combination of ordered products of `n` degree-one sections, times a degree-one section, is
a combination of ordered products of `n + 1` degree-one sections. -/
theorem pieceMul_mem_span_homogeneousPow (V : s.base.Opens) (n : ℕ)
    {a : Γ(s.pieceModules (n : ℤ), V)}
    (ha : a ∈ Submodule.span Γ(s.base, V) (Set.range fun z => s.homogeneousPow V n z))
    (b : Γ(s.pieceModules (1 : ℤ), V)) :
    s.pieceMul n 1 V a b ∈ Submodule.span Γ(s.base, V)
      (Set.range fun z => s.homogeneousPow V (n + 1) z) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨Fin.snoc w b, homogeneousPow_snoc s V n w b⟩
  | zero =>
    rw [Situation.pieceMul_zero_left]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Situation.pieceMul_add_left]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [Situation.pieceMul_smul_left]
    exact Submodule.smul_mem _ r hx

/-- Transport of a homogeneous section along an equality of degrees. -/
def pieceCast {i j : ℤ} (h : i = j) (U : s.base.Opens) :
    Γ(s.pieceModules i, U) ≃+ Γ(s.pieceModules j, U) := by
  subst h
  exact AddEquiv.refl _

/-- Transport along an equality of degrees does not change a section up to `HEq`. -/
theorem pieceCast_heq {i j : ℤ} (h : i = j) (U : s.base.Opens) (x : Γ(s.pieceModules i, U)) :
    HEq (pieceCast s h U x) x := by
  subst h
  rfl

/-- The integer `1 + n` is the cast of the natural number `n + 1`. -/
theorem one_add_natCast_eq (n : ℕ) : (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by
  omega

/-- Moved to degree `n + 1`, the product of a degree-one section `x` with a degree-`n` section
`y` is the product of `y` with `x`. -/
theorem pieceCast_pieceMul_one (n : ℕ) (U : s.base.Opens) (x : Γ(s.pieceModules (1 : ℤ), U))
    (y : Γ(s.pieceModules (n : ℤ), U)) :
    pieceCast s (one_add_natCast_eq n) U (s.pieceMul 1 n U x y) =
      (s.pieceMul n 1 U y x : Γ(s.pieceModules ((n + 1 : ℕ) : ℤ), U)) :=
  eq_of_heq ((pieceCast_heq s _ U _).trans (s.mul_comm 1 n (op U) x y))

/-- **Sheaf-level generation in degree one gives the span form.** Over an open `U` on which every
degree-zero section is a multiple of `1` and the graded algebra is generated in degree one, every
section of degree `n` is a combination of ordered products of `n` degree-one sections. -/
theorem mem_span_homogeneousPow_of_isGeneratedInDegreeOne (U : s.base.Opens)
    (h0 : Function.Surjective
      (fun r : s.base.ringCatSheaf.obj.obj (op U) => r • s.algebra.one.eval (op U)))
    (hgen : s.algebra.IsGeneratedInDegreeOne (op U)) :
    ∀ (n : ℕ) (a : Γ(s.pieceModules (n : ℤ), U)),
      a ∈ Submodule.span Γ(s.base, U) (Set.range fun z => s.homogeneousPow U n z) := by
  intro n
  induction n with
  | zero =>
    intro a
    obtain ⟨r, rfl⟩ := h0 a
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨Fin.elim0, rfl⟩)
  | succ n ih =>
    intro a
    let P := Submodule.span Γ(s.base, U) (Set.range fun z => s.homogeneousPow U (n + 1) z)
    let Q : AddSubgroup Γ(s.pieceModules ((1 : ℤ) + (n : ℤ)), U) :=
      P.toAddSubgroup.comap (pieceCast s (one_add_natCast_eq n) U).toAddMonoidHom
    have hQ : Q = ⊤ := hgen n Q fun x y => by
      change pieceCast s (one_add_natCast_eq n) U (s.pieceMul 1 n U x y) ∈ P
      rw [pieceCast_pieceMul_one s n U x y]
      exact pieceMul_mem_span_homogeneousPow s U n (ih y) x
    obtain ⟨w, rfl⟩ := (pieceCast s (one_add_natCast_eq n) U).surjective a
    exact (AddSubgroup.eq_top_iff' Q).1 hQ w

/-- **The span form of generation in degree one gives the sheaf-level form.** If over an open `U`
every section of every degree `n` is a combination of ordered products of `n` degree-one
sections, the graded algebra is generated in degree one over `U`. -/
theorem isGeneratedInDegreeOne_of_mem_span_homogeneousPow (U : s.base.Opens)
    (h : ∀ (n : ℕ) (a : Γ(s.pieceModules (n : ℤ), U)),
      a ∈ Submodule.span Γ(s.base, U) (Set.range fun z => s.homogeneousPow U n z)) :
    s.algebra.IsGeneratedInDegreeOne (op U) := by
  intro n P hP
  refine (AddSubgroup.eq_top_iff' P).2 fun w => ?_
  have key : ∀ v ∈ Submodule.span Γ(s.base, U)
      (Set.range fun z => s.homogeneousPow U (n + 1) z), ∀ r : Γ(s.base, U),
      (pieceCast s (one_add_natCast_eq n) U).symm (r • v) ∈ P := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      intro r
      have e : r • s.homogeneousPow U (n + 1) z =
          pieceCast s (one_add_natCast_eq n) U (s.pieceMul 1 n U (r • z (Fin.last n))
            (s.homogeneousPow U n fun i => z i.castSucc)) := by
        rw [pieceCast_pieceMul_one s]
        exact (s.pieceMul_smul_right n 1 U r _ _).symm
      rw [(AddEquiv.symm_apply_eq _).2 e]
      exact hP _ _
    | zero =>
      intro r
      rw [smul_zero, map_zero]
      exact P.zero_mem
    | add v v' _ _ hv hv' =>
      intro r
      rw [smul_add, map_add]
      exact P.add_mem (hv r) (hv' r)
    | smul r' v _ hv =>
      intro r
      rw [smul_smul]
      exact hv _
  have := key _ (h (n + 1) (pieceCast s (one_add_natCast_eq n) U w)) 1
  have e3 : (pieceCast s (one_add_natCast_eq n) U).symm
      ((1 : Γ(s.base, U)) • pieceCast s (one_add_natCast_eq n) U w) = w := by
    rw [one_smul]
    exact (pieceCast s (one_add_natCast_eq n) U).symm_apply_apply w
  exact Eq.mpr (congrArg (· ∈ P) e3.symm) this

end MMP.RelativeProjSituation

namespace MMP.Intersection.Scheme.IsConeAlgebra

open Stacks.RelativeProj

variable {s : Situation.{u}} (hs : IsConeAlgebra s)

include hs

/-- **The graded algebra of a cone is locally generated in degree one over every open.** Near a
point, pick an affine open `V₀` over which `S^•` is generated in degree one and an affine open
`V ⊆ U ∩ V₀` around the point; by quasi-coherence every section over `V` is a combination of
restrictions of sections over `V₀`, which are combinations of products of degree-one sections. -/
theorem isLocallyDegreeOneGenerated (U : s.base.Opens) : s.IsLocallyDegreeOneGenerated U := by
  intro n a x hx
  obtain ⟨V₀, hxV₀, hV₀, hgen⟩ := hs.locally_generatedInDegreeOne x
  obtain ⟨V, hV, hxV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    s.base.isBasis_affineOpens (show x ∈ U ⊓ V₀ from ⟨hx, hxV₀⟩)
  have hVU : V ≤ U := hVle.trans inf_le_left
  have hVV₀ : V ≤ V₀ := hVle.trans inf_le_right
  refine ⟨V, hVU, hxV, ?_⟩
  have hspan := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.mem_span_range_restrict
    (s.pieceModules (n : ℤ)) hV hV₀ hVV₀ (s.pieceRestrict (n : ℤ) hVU a)
  refine (Submodule.span_le.2 ?_) hspan
  rintro _ ⟨b, rfl⟩
  have hb := MMP.RelativeProjSituation.mem_span_homogeneousPow_of_isGeneratedInDegreeOne s V₀
    (hs.bijective_smul_one V₀).2 hgen n b
  have hb' := s.pieceRestrict_mem_span (n : ℤ) hVV₀ _ hb
  refine (Submodule.span_le.2 ?_) hb'
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨_, (s.homogeneousPow_naturality hVV₀ n z).symm⟩

/-- Over an affine open, the graded ring of sections of the algebra of a cone is generated by its
degree-one part over its degree-zero part. -/
theorem adjoin_sectionRingGrading_one_eq_top (U : s.base.Opens) (hU : IsAffineOpen U) :
    Algebra.adjoin ↥(s.sectionRingGrading U 0)
      (s.sectionRingGrading U 1 : Set (s.sectionRing U)) = ⊤ :=
  s.adjoin_sectionRingGrading_one_eq_top U hU (hs.isLocallyDegreeOneGenerated U)

/-- **The projection of a projective cone is proper** (Fulton, Appendix B.5): for a graded
algebra `S^•` satisfying Fulton's conditions, `Proj(S^•) ⟶ X` is proper. Over every affine open
`U`, `S⁰(U) = 𝒪_X(U)`, and `Γ(U, S^•)` is generated by the finite module `S¹(U)`. -/
theorem isProper_relativeProjToBase : IsProper s.relativeProjToBase := by
  have := hs.isCoherent_one
  refine s.isProper_relativeProjToBase_of_cover (fun U : s.base.affineOpens => U)
    (iSup_affineOpens_eq_top s.base) (fun U => ?_) (fun U => ?_)
  · exact s.isIso_sectionRingZeroMap U.1 (hs.bijective_smul_one U.1)
  · obtain ⟨g, hg⟩ := (finite_sections_of_isAffineOpen (s.algebra.piece 1) U.1 U.2).fg_top
    exact s.finiteType_sectionRing_of_adjoin_eq_top U.1
      (hs.adjoin_sectionRingGrading_one_eq_top U.1 U.2) g hg

open Stacks.AlgebraicGeometry in
/-- **The twisting sheaves of a projective cone are invertible.** Over an affine open `V` of the
base the graded ring of sections of `S^•` is generated in degree one, so on the chart over `V`
every `𝒪(n)` is trivial near each point; the charts cover `Proj(S^•)`. -/
theorem isInvertibleModule_twistSheaf (n : ℤ) :
    Stacks.Ample.IsInvertibleModule s.relativeProj (s.twistSheaf n) := by
  refine TwistMapsInvertible.isInvertibleModule_of_forall_exists_isoUnit_openImmersion
    _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := s.base) (x := s.relativeProjToBase.base x) (U := ⊤) trivial
  obtain ⟨y, hy⟩ : x ∈ (s.relativeProjChart ⟨V, hV⟩).opensRange := by
    rwa [Situation.opensRange_relativeProjChart s ⟨V, hV⟩]
  obtain ⟨U, hyU, ⟨eU⟩⟩ :=
    TwistMapsInvertible.exists_mem_restrict_isoUnit_twistingSheaf_of_adjoin
      _ (hs.adjoin_sectionRingGrading_one_eq_top V hV) n y
  refine ⟨U.toScheme, U.ι ≫ s.relativeProjChart ⟨V, hV⟩, inferInstance, ⟨⟨y, hyU⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp U.ι (s.relativeProjChart ⟨V, hV⟩)).app
      (s.twistSheaf n) ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (Situation.twistSheafChartIso s n ⟨V, hV⟩) ≪≫ eU

end MMP.Intersection.Scheme.IsConeAlgebra
