module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksNonvanishing
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularEmbeddingOrientation.StacksClass
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Orientation data from a quotient bundle near `X`, for Stacks vector bundles

Let `i : X → Y` be a regular imbedding of codimension `d` of complex schemes, `σ : Y ⟶ 𝐕(ℰ)` a
section of the vector bundle of a quasi-coherent `𝒪_Y`-module `ℰ`, finite locally free of rank
`e ≥ d`, with zero scheme `X`, and `𝐕(ℰ)(ℂ)|_N → Q` a surjective morphism of complex topological
vector bundles on an open `N ⊇ X(ℂ)`, with `Q` of rank `d`, whose kernel is complementary to the
normal bundle along `X`. Restricting `Q` to the open neighbourhood `V ⊆ N` of `X(ℂ)` on which `σ̄`
vanishes only on `X` (`MMP.Modules.exists_isOpen_sectionBar_mem_range_zeroSection`) gives the
data `(ℰ, σ, V, Q|_V)` of an orientation class of `i` (Fulton, §19.2).

## Main results

* `MMP.Modules.RegularImbeddingOrientationDatum.ofRestrict`: the datum on `V ⊆ N`, with `Q|_V`
  the pull-back of `Q` along `V ⊆ N`.
* `MMP.Modules.RegularImbeddingOrientationDatum.nonempty_of_quot`: such a morphism
  `𝐕(ℰ)(ℂ)|_N → Q` yields an orientation datum of `i`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Bundle Set

namespace MMP.Modules

open UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

section Cast

variable {B F : Type*} {Q : B → Type*}

private lemma mk_cast_snd (z : TotalSpace F Q) {b : B} (h : z.proj = b) :
    (⟨b, cast (congrArg Q h) z.2⟩ : TotalSpace F Q) = z := by
  subst h
  rfl

end Cast

namespace RegularImbeddingOrientationDatum

variable {i : X ⟶ Y} [i.IsOver (Spec (.of ℂ))] {d e : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : Set (UnderlyingSpace ℂ Y)} {Q : N → Type} [∀ y, AddCommGroup (Q y)]
  [∀ y, Module ℂ (Q y)] [∀ y, TopologicalSpace (Q y)] [TopologicalSpace (TotalSpace F Q)]
  [FiberBundle F Q] [_root_.VectorBundle ℂ F Q]

/-- The orientation datum `(ℰ, σ, V, Q|_V)` obtained by restricting a quotient bundle
`𝐕(ℰ)(ℂ)|_N → Q` to an open neighbourhood `V ⊆ N` of `X(ℂ)` on which `σ̄` vanishes only on
`X`. -/
def ofRestrict (le_rank : d ≤ e) (E : Y.Modules) [E.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E e] (σ : Y ⟶ totalSpace E)
    [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 Y) (hs : zeroLocus E σ = i.ker)
    (finrank_F : Module.finrank ℂ F = d)
    (quot : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ N} → TotalSpace F Q)
    (hquot : Continuous quot) (proj_quot : ∀ p, (quot p).proj = ⟨mapFun (proj E) p.1, p.2⟩)
    (hfibre : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (hyN : y ∈ N), ∃ L : (Fin e → ℂ) →ₗ[ℂ] Q ⟨y, hyN⟩,
        (∀ w, quot ⟨chartInv c y hy w, by rwa [mapFun_proj_chartInv]⟩ = ⟨⟨y, hyN⟩, L w⟩) ∧
        Function.Surjective L ∧
        (y ∈ Set.range (UnderlyingSpace.map i) → IsCompl (LinearMap.ker L) (normalFibre σ c y)))
    (V : Set (UnderlyingSpace ℂ Y)) (hVN : V ⊆ N) (hV : IsOpen V)
    (hXV : Set.range (UnderlyingSpace.map (K := ℂ) i) ⊆ V)
    (hVs : ∀ y : N, y.1 ∈ V →
      quot ⟨mapFun σ y, by rw [mapFun_proj_mapFun_section hσ]; exact y.2⟩ ∈
        Set.range (Bundle.zeroSection F Q) →
      y.1 ∈ Set.range (UnderlyingSpace.map (K := ℂ) i)) :
    RegularImbeddingOrientationDatum i d where
  rank := e
  le_rank := le_rank
  E := E
  σ := σ
  comp_proj := hσ
  zeroLocus_eq := hs
  nbhd := V
  isOpen_nbhd := hV
  range_subset_nbhd := hXV
  F := F
  finrank_F := finrank_F
  Q := ((⟨Set.inclusion hVN, continuous_inclusion hVN⟩ : C(V, N)) : V → N) *ᵖ Q
  addCommGroup y := inferInstanceAs (AddCommGroup (Q (Set.inclusion hVN y)))
  module y := inferInstanceAs (Module ℂ (Q (Set.inclusion hVN y)))
  fiberBundle := FiberBundle.pullback (⟨Set.inclusion hVN, continuous_inclusion hVN⟩ : C(V, N))
  quot p := ⟨⟨mapFun (proj E) p.1, p.2⟩,
    cast (congrArg Q (proj_quot ⟨p.1, hVN p.2⟩)) (quot ⟨p.1, hVN p.2⟩).2⟩
  continuous_quot := by
    let ι : C(V, N) := ⟨Set.inclusion hVN, continuous_inclusion hVN⟩
    have hlift : ∀ p : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ V},
        Pullback.lift (ι : V → N) (⟨⟨mapFun (proj E) p.1, p.2⟩,
          cast (congrArg Q (proj_quot ⟨p.1, hVN p.2⟩)) (quot ⟨p.1, hVN p.2⟩).2⟩ :
            TotalSpace F ((ι : V → N) *ᵖ Q)) = quot ⟨p.1, hVN p.2⟩ := fun p ↦
      mk_cast_snd (quot ⟨p.1, hVN p.2⟩) (proj_quot ⟨p.1, hVN p.2⟩)
    unfold Pullback.TotalSpace.topologicalSpace
    rw [pullbackTopology_def]
    refine continuous_inf_rng.2 ⟨continuous_induced_rng.2 ?_, continuous_induced_rng.2 ?_⟩
    · exact ((continuous_mapFun (proj E)).comp continuous_subtype_val).subtype_mk _
    · exact (continuous_congr hlift).2 (hquot.comp (continuous_subtype_val.subtype_mk _))
  proj_quot _ := rfl
  fibre c y hy hyV := by
    obtain ⟨L, hL, hsurj, hC⟩ := hfibre c y hy (hVN hyV)
    exact ⟨L, fun w ↦ TotalSpace.ext (Subtype.ext (mapFun_proj_chartInv _ _ _ _))
      ((cast_heq _ _).trans (congr_arg_heq TotalSpace.snd (hL w))), hsurj, hC⟩
  quot_sec_notMem y hy hmem := by
    obtain ⟨b, hb⟩ := hmem
    refine hy (hVs ⟨y.1, hVN y.2⟩ y.2 ⟨⟨b.1, hVN b.2⟩, ?_⟩)
    have hp : mapFun (proj E) (mapFun σ y.1) ∈ V := by
      rw [mapFun_proj_mapFun_section hσ]
      exact y.2
    exact (congrArg (Pullback.lift (⟨Set.inclusion hVN, continuous_inclusion hVN⟩ : C(V, N)))
      hb).trans (mk_cast_snd (quot ⟨mapFun σ y.1, hVN hp⟩) (proj_quot ⟨mapFun σ y.1, hVN hp⟩))

/-- **Orientation data from a quotient bundle.** For a regular imbedding `i` of codimension `d`,
a section `σ` of `𝐕(ℰ)` (`ℰ` of rank `e ≥ d`) with `Z(σ) = X`, and a surjective morphism
`𝐕(ℰ)(ℂ)|_N → Q` onto a complex topological vector bundle of rank `d` on an open `N ⊇ X(ℂ)`,
complex linear on the fibres and with kernel complementary to the normal bundle along `X`, there
is an orientation datum of `i`: restrict `Q` to a neighbourhood of `X(ℂ)` on which `σ̄` vanishes
only on `X`. -/
theorem nonempty_of_quot [IsClosedImmersion i] (hi : IsRegularClosedImmersionOfCodim i d)
    (le_rank : d ≤ e) (E : Y.Modules) [E.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} E e]
    (σ : Y ⟶ totalSpace E) [σ.IsOver (Spec (.of ℂ))] (hσ : σ ≫ proj E = 𝟙 Y)
    (hs : zeroLocus E σ = i.ker) (finrank_F : Module.finrank ℂ F = d)
    (hN : IsOpen N) (hXN : Set.range (UnderlyingSpace.map (K := ℂ) i) ⊆ N)
    (quot : {p : UnderlyingSpace ℂ (totalSpace E) // mapFun (proj E) p ∈ N} → TotalSpace F Q)
    (hquot : Continuous quot) (proj_quot : ∀ p, (quot p).proj = ⟨mapFun (proj E) p.1, p.2⟩)
    (hfibre : ∀ (c : Chart E e) (y : UnderlyingSpace ℂ Y) (hy : ⊤ ≤ y.toHom ⁻¹ᵁ c.1.1)
      (hyN : y ∈ N), ∃ L : (Fin e → ℂ) →ₗ[ℂ] Q ⟨y, hyN⟩,
        (∀ w, quot ⟨chartInv c y hy w, by rwa [mapFun_proj_chartInv]⟩ = ⟨⟨y, hyN⟩, L w⟩) ∧
        Function.Surjective L ∧
        (y ∈ Set.range (UnderlyingSpace.map i) → IsCompl (LinearMap.ker L) (normalFibre σ c y))) :
    Nonempty (RegularImbeddingOrientationDatum i d) := by
  obtain ⟨V, hVN, hV, hXV, hVs⟩ := exists_isOpen_sectionBar_mem_range_zeroSection i hi σ hσ
    hs hN hXN quot hquot hfibre
  exact ⟨ofRestrict le_rank E σ hσ hs finrank_F quot hquot proj_quot hfibre V hVN hV hXV hVs⟩

end RegularImbeddingOrientationDatum

end MMP.Modules
