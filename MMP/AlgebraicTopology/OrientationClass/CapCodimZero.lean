module

public import MMP.AlgebraicTopology.OrientationClass.CapLocal
public import MMP.AlgebraicTopology.PoincareDuality.AlexanderSquare
public import MMP.AlgebraicTopology.SingularCohomology.Contractible
public import Mathlib.Topology.Metrizable.Urysohn

/-!
# `u_{M,P} ∩ μ_P = μ_M` in codimension `0` (Fulton, §19.1)

The case `dim F = 0` of `lem_ext_c19_orientation_class_cap_fundamental`. A tubular neighbourhood
`φ : N → P` of rank `0` is onto `M`, so `M` is open (and closed) in `P`; the orientation class
`u ∈ H^0(P, P - M)` is represented by a cocycle taking the value `1` at every point of `M`
(the Thom class condition on the fibres, which are points), so on the open set `V = M` the cap
product with `u` is the identity, and `u ∩ μ_P = μ_P|_M`. Finally `μ_P|_M` is the fundamental
class of `M` for the complex orientation of its own charts: the transitions `e ∘ e'⁻¹` are
holomorphic with bijective derivative.

## Main results

* `MMP.borelMooreHomology.capProduct_eq_congrDegree_of_eq_one`: the cap product
  with a `0`-class represented by the constant cocycle `1` is the identity.
* `MMP.borelMooreHomology.isLocallyClassOf_capProductSupport_of_eq_one`: the same,
  for the cap product with supports in a closed set that is the whole space, in local-class form.
* `MMP.IsOrientationClass.isFundamentalClass_capProductSupport_of_eq_zero`: the
  codimension-`0` case.
* `MMP.IsOrientationClass.isFundamentalClass_capProductSupport`:
  `u_{M,P} ∩ μ_P = μ_M` (`lem_ext_c19_orientation_class_cap_fundamental`).
-/

@[expose] public noncomputable section

open CategoryTheory Set Topology

universe u

namespace MMP

open MMP

namespace borelMooreHomology

open MMP.borelMooreHomology

open BorelMooreCap SingularChain SingularCochain BorelMooreCross PoincareAlexander FundamentalClass

variable (R : Type u) [CommRing R]

/-- **The cap product with the unit class.** If `c ∈ H^0(Y, Y - X)` is represented by a cocycle
taking the value `1` on every point, then `c ∩ b = b` for every `b ∈ H_m Y`. -/
theorem capProduct_eq_congrDegree_of_eq_one (Y : TopCat.{u}) (X : Set Y) (m : ℕ)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X ((0 : ℕ) : ℤ))
    (φ : Simplex Y 0 → R) (hφ : φ ∈ relCocycles R Xᶜ 0)
    (hc : relativeSingularCohomologyEquiv R Xᶜ 0 c = Submodule.Quotient.mk ⟨φ, hφ⟩)
    (h1 : ∀ σ, φ σ = 1) (h : (m : ℤ) = m - ((0 : ℕ) : ℤ))
    (b : borelMooreHomology R (ModuleCat.of R R) Y m) :
    capProduct R Y X ((0 : ℕ) : ℤ) m c b = congrDegree R Y h b := by
  rw [capProduct_natCast Y X (Nat.zero_le m), hc]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (homologyEquiv R Y m b)
  obtain rfl : φ = constCochain 0 1 := funext h1
  rw [← hz]
  erw [capHomQ_mk]
  have e : (⟨capChain R 0 (m - 0) m (by omega) (constCochain 0 1) z.1,
      capChain_mem_cyc Xᶜ 0 (m - 0) m (by omega) ⟨constCochain 0 1, hφ⟩ z⟩ :
        Cyc (R := R) Y m) = z :=
    Subtype.ext ((capChain_constCochain m (by omega) 1 z.1).trans (one_smul _ _))
  erw [e, hz, LinearEquiv.symm_apply_apply]
  rfl

/-- **The cap product with the unit class, with supports, in local-class form.** Let `X` be a
closed subset of `Y` containing every point, and `c ∈ H^0(Y, Y - X)` represented by a cocycle
taking the value `1` on every point. If `a ∈ H_k Y` is locally the class of `X ⊆ Y ∘ σ` at `p`,
then `c ∩ a ∈ H_k X` is locally the class of `σ` at `p`. -/
theorem isLocallyClassOf_capProductSupport_of_eq_one (Y : TopCat.{u}) [T2Space Y] {X : Set Y}
    (hX : IsClosed X) (hXd : HasProperNeighbourhoodDeformations X) (hXu : ∀ y, y ∈ X)
    {j : ℕ} (hj : j = 0) (k : ℕ) {n : ℕ} (hn : (k : ℤ) - (j : ℤ) = n) (hk : (k : ℤ) = n)
    (c : cohomologyWithSupports R (ModuleCat.of R R) Y X j)
    (hc : ∃ (φ : Simplex Y j → R) (hφ : φ ∈ relCocycles R Xᶜ j),
      relativeSingularCohomologyEquiv R Xᶜ j c = Submodule.Quotient.mk ⟨φ, hφ⟩ ∧ ∀ σ, φ σ = 1)
    (a : borelMooreHomology R (ModuleCat.of R R) Y k) {p : TopCat.of X}
    {σ : Simplex (TopCat.of X) n}
    (ha : IsLocallyClassOf R (congrDegree R _ hk a) p.1 ((subsetInclusion X).hom.comp σ)) :
    IsLocallyClassOf R (congrDegree R _ hn (capProductSupport R Y hX hXd _ _ c a)) p σ := by
  subst hj
  obtain ⟨φ, hφ, hrep, h1⟩ := hc
  have e1 := pushforward_subsetInclusion_capProductSupport R Y hX hXd _ _ c a
  rw [capProduct_eq_congrDegree_of_eq_one R Y X k c φ hφ hrep h1 (by omega)] at e1
  let H : TopCat.of X ≃ₜ Y :=
    (Homeomorph.setCongr (eq_univ_of_forall hXu)).trans (Homeomorph.Set.univ Y)
  let g : Y ⟶ TopCat.of X := TopCat.ofHom (H.symm : C(Y, X))
  have hg : IsProperMap g := H.symm.isProperMap
  have hcomp : subsetInclusion X ≫ g = 𝟙 _ := by ext; rfl
  have e2 := eq_pushforward_of_pushforward_eq R (subsetInclusion X) g
    (isProperMap_subsetInclusion hX) hg hcomp _ e1
  have h3 := ha.pushforward g hg (fun y hy ↦ H.symm.injective hy)
  erw [pushforward_congrDegree_apply] at h3
  rw [e2]
  erw [pushforward_congrDegree_apply, congrDegree_congrDegree]
  exact h3

end borelMooreHomology

/-- A set containing every point has arbitrarily small proper neighbourhood deformations: the
whole space, the identity retraction and the constant homotopy. -/
theorem hasProperNeighbourhoodDeformations_of_forall_mem {Y : Type*} [TopologicalSpace Y]
    {X : Set Y} (hXu : ∀ y, y ∈ X) : HasProperNeighbourhoodDeformations X := by
  intro W hW
  have hWu : ∀ y, y ∈ W := fun y ↦ subset_of_mem_nhdsSet hW (hXu y)
  let H : (univ : Set Y) ≃ₜ X := (Homeomorph.Set.univ Y).trans
    ((Homeomorph.setCongr (eq_univ_of_forall hXu)).trans (Homeomorph.Set.univ Y)).symm
  refine ⟨univ, isClosed_univ, fun y _ ↦ by rw [interior_univ]; trivial, fun y _ ↦ hWu y,
    (H : C((univ : Set Y), X)), H.isProperMap, fun _ _ ↦ rfl,
    ⟨fun q ↦ (q.1 : Y), continuous_subtype_val.comp continuous_fst⟩, ?_, fun _ ↦ rfl,
    fun _ ↦ rfl, fun _ _ _ ↦ rfl, fun q ↦ hWu _⟩
  exact (Homeomorph.Set.univ Y).isProperMap.comp isProperMap_fst_of_compactSpace

section Thom

open Bundle ThomClass SingularChain SingularCochain FundamentalClass Finsupp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {P : TopCat.{u}} [ChartedSpace E P]
  {M : Set P}
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- **The orientation class in codimension `0` is the unit on `M`.** If the normal bundle has
rank `0`, every cocycle `α` representing the orientation class `u ∈ H^0(P, P - M)` takes the
value `1` on every (constant) simplex in `M`: the Thom class condition on the fibre over a point
`x ∈ M`, which is the point `0`. -/
theorem IsOrientationClass.apply_eq_one_of_finrank_eq_zero {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (hF : Module.finrank ℂ F = 0)
    {α : Simplex P (2 * Module.finrank ℂ F) → R}
    (hα : α ∈ relCocycles R Mᶜ (2 * Module.finrank ℂ F))
    (hrep : relativeSingularCohomologyEquiv R Mᶜ (2 * Module.finrank ℂ F) u =
      Submodule.Quotient.mk ⟨α, hα⟩)
    (τ : Simplex P (2 * Module.finrank ℂ F)) (hτ : ∀ t, τ t ∈ M) : α τ = 1 := by
  have : IsEmpty (Fin (Module.finrank ℂ F)) := by rw [hF]; infer_instance
  have : IsEmpty (Fin (2 * Module.finrank ℂ F)) := by rw [hF, mul_zero]; infer_instance
  have : Subsingleton (Fin (2 * Module.finrank ℂ F + 1)) := by
    rw [hF]
    exact inferInstanceAs (Subsingleton (Fin 1))
  have : Subsingleton (stdSimplex ℝ (Fin (2 * Module.finrank ℂ F + 1))) :=
    ⟨fun s s' ↦ Subtype.ext (funext fun i ↦ by
      have hs := s.2.2
      have hs' := s'.2.2
      rw [Fintype.sum_subsingleton _ i] at hs hs'
      rw [hs, hs'])⟩
  obtain ⟨t₀⟩ : Nonempty (stdSimplex ℝ (Fin (2 * Module.finrank ℂ F + 1))) :=
    ⟨⟨fun _ ↦ 1, fun _ ↦ zero_le_one, by rw [Fintype.sum_subsingleton _ 0]⟩⟩
  set x : M := ⟨τ t₀, hτ t₀⟩
  obtain ⟨ψ, -⟩ := hu.1 x
  set v : Fin (2 * Module.finrank ℂ F + 1) → (Fin (Module.finrank ℂ F) → ℂ) := fun _ ↦ 0
  have hv : IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ F)) v := by
    refine ⟨⟨fun _ ↦ 1, fun _ ↦ zero_lt_one, by rw [Fintype.sum_subsingleton _ 0],
      by simp [v]⟩, ?_⟩
    rw [Module.Basis.det_apply, Matrix.det_isEmpty]
    exact zero_lt_one
  have hc := eval_single_eq_zero_of_mem_relCoboundaries (R := R) (fibreSimplex F x ψ v)
    (fibreSimplex_notMem_range_zeroSection F x ψ hv)
  have h₁ : (φ.toHom ⁻¹' M)ᶜ ⊆ φ.toHom ⁻¹' Mᶜ := fun _ hx ↦ hx
  have h₂ : (range (zeroSection F N))ᶜ ⊆
      (𝟙 (TopCat.of (TotalSpace F N))) ⁻¹' (φ.toHom ⁻¹' M)ᶜ :=
    compl_subset_compl.mpr φ.preimage_eq_range_zeroSection.subset
  have e2 := relativeSingularCohomologyEquiv_map (R := R) φ.toHom h₁ (2 * Module.finrank ℂ F) u
  have e1 := relativeSingularCohomologyEquiv_map (R := R) (𝟙 (TopCat.of (TotalSpace F N))) h₂
    (2 * Module.finrank ℂ F)
    ((relativeSingularCohomology.map R (ModuleCat.of R R) φ.toHom h₁
      (2 * Module.finrank ℂ F : ℕ)).hom u)
  have hth : relEval (single (fibreSimplex F x ψ v) 1) hc
      (relCohomologyMap R (𝟙 (TopCat.of (TotalSpace F N))) h₂ (2 * Module.finrank ℂ F)
        (relCohomologyMap R φ.toHom h₁ (2 * Module.finrank ℂ F)
          (relativeSingularCohomologyEquiv R Mᶜ (2 * Module.finrank ℂ F) u))) = 1 :=
    ((congrArg (relEval (single (fibreSimplex F x ψ v) 1) hc)
      (e1.trans (congrArg _ e2))).symm.trans (hu.2 x ψ v hv))
  rw [hrep, relCohomologyMap_mk, relCohomologyMap_mk, relEval_mk, linearCombination_single,
    one_smul] at hth
  refine Eq.trans ?_ hth
  change α τ = α (φ.toHom.hom.comp ((TopCat.Hom.hom (𝟙 (TopCat.of (TotalSpace F N)))).comp
    (fibreSimplex F x ψ v)))
  congr 1
  ext t
  rw [Subsingleton.elim t t₀]
  change (τ t₀ : P) = φ (TotalSpace.mk x (ψ (affineSimplex v t₀)))
  rw [Subsingleton.elim (affineSimplex v t₀) 0, map_zero]
  exact (φ.map_zeroSection x).symm

end Thom

section Open

open Manifold ThomClass SingularChain FundamentalClass borelMooreHomology BorelMooreCross

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] [T2Space P] {M : Set P}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  [ChartedSpace E' M]
  (R : Type u) [CommRing R]

/-- An open subset `M` of `P`, as the open set `⟨M, hMo⟩`: the identity of `M`, from the charts
of `M` to the charts that `P` induces on the open set. -/
def openSelfHomeomorph (hMo : IsOpen M) : M ≃ₜ (⟨M, hMo⟩ : TopologicalSpace.Opens P) :=
  Homeomorph.setCongr rfl

/-- **An open complex submanifold carries the induced orientation.** If `M` is an open complex
submanifold of `P` (of the same dimension), the identity of `M`, from its own charts to those
induced by `P`, is orientation preserving for the complex orientations: the transitions
`e ∘ e'⁻¹` are holomorphic with injective, hence bijective, derivative. -/
theorem isOrientationPreserving_openSelfHomeomorph (hM : IsComplexSubmanifold E E' M)
    (hMo : IsOpen M) (hdim : Module.finrank ℂ E = Module.finrank ℂ E') :
    IsOrientationPreserving (complexOrientationBasisOf E')
      ((complexOrientationBasisOf E).reindex (finCongr (congrArg (2 * ·) hdim)))
      (openSelfHomeomorph hMo) := by
  apply isOrientationPreserving_of_hasFDerivAt
  rintro e he e₂ ⟨_, ⟨q, rfl⟩, he₂⟩ x hx hx'
  rw [mem_singleton_iff] at he₂
  subst he₂
  set c := chartAt E (q : P)
  have hxs : ((e.symm (e x) : M) : P) ∈ c.source := by
    rw [e.left_inv hx]
    rwa [OpenPartialHomeomorph.subtypeRestr_source] at hx'
  obtain ⟨hcd, hinj⟩ := hM e he c (chart_mem_atlas E (q : P)) (e x) (e.map_source hx) hxs
  refine ⟨(fderiv ℂ (fun z ↦ c (e.symm z : P)) (e x)).restrictScalars ℝ,
    (hcd.differentiableAt one_ne_zero).hasFDerivAt.restrictScalars ℝ, ?_⟩
  have := complexRealBasis_det_pos (Module.finBasis ℂ E')
    ((Module.finBasis ℂ E).reindex (finCongr hdim))
    (L := (fderiv ℂ (fun z ↦ c (e.symm z : P)) (e x) : E' →ₗ[ℂ] E)) hinj
  rwa [complexRealBasis_reindex_finCongr] at this

/-- **The fundamental class of `P` restricted to an open complex submanifold is locally the
orientation generator of `M`.** For an open complex submanifold `M` of `P` and a chart `e'` of
`M`, `μ_P|_M` is locally, at `x`, the class of `e'⁻¹ ∘ Δ` for every simplex `Δ` around `e' x`
positively oriented for the complex orientation of the model of `M`. -/
theorem IsFundamentalClass.isLocallyClassOf_restrict_open (hM : IsComplexSubmanifold E E' M)
    (hMo : IsOpen M) (hdim : Module.finrank ℂ E = Module.finrank ℂ E')
    {μP : borelMooreHomology R (ModuleCat.of R R) P (2 * Module.finrank ℂ E : ℕ)}
    (hμP : IsFundamentalClass (M := P) R (complexOrientationBasisOf E) μP)
    (hk : ((2 * Module.finrank ℂ E : ℕ) : ℤ) = (2 * Module.finrank ℂ E' : ℕ))
    {e' : OpenPartialHomeomorph M E'} (he' : e' ∈ atlas E' M) {x : M} (hx : x ∈ e'.source)
    {v : Fin (2 * Module.finrank ℂ E' + 1) → E'}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasisOf E') fun k ↦ v k - e' x)
    (hvt : range (affineSimplex v) ⊆ e'.target) :
    IsLocallyClassOf R (congrDegree R _ hk
      ((borelMooreHomology.restrict R (ModuleCat.of R R) (⟨M, hMo⟩ : TopologicalSpace.Opens P)
        _).hom μP))
      (openSelfHomeomorph hMo x)
      ((openSelfHomeomorph hMo : C(M, (⟨M, hMo⟩ : TopologicalSpace.Opens P))).comp
        (inclChainSimplex (chartOpens e') (chartSimplex e' v hvt))) := by
  have hV := (hμP.restrict (⟨M, hMo⟩ : TopologicalSpace.Opens P)).congrDegree_reindex
    (congrArg (2 * ·) hdim)
  set y := openSelfHomeomorph hMo x
  set eV := chartAt E y
  have hy : y ∈ eV.source := mem_chart_source E y
  obtain ⟨w, hw, hwt⟩ := exists_isOrientedSimplexAroundZero_subset
    ((complexOrientationBasisOf E).reindex (finCongr (congrArg (2 * ·) hdim))) (eV y)
    (eV.open_target.mem_nhds (eV.map_source hy))
  have h0 := (hV eV (chart_mem_atlas E y) ⟨y, hy⟩ w hw hwt).of_restrict
  have hφ := isOrientationPreserving_openSelfHomeomorph hM hMo hdim e' he' eV
    (chart_mem_atlas E y) x hx hy v hv hvt w hw hwt
  exact h0.of_isLocallyHomologous hφ.symm

end Open

section Assembly

open Bundle ThomClass SingularChain SingularCochain FundamentalClass borelMooreHomology
  BorelMooreCross BorelMooreCap Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] [IsManifold 𝓘(ℂ, E) 1 P] [T2Space P]
  [SecondCountableTopology P] {M : Set P}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  [ChartedSpace E' M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) 1 P] [T2Space P] [SecondCountableTopology P]
  [ChartedSpace E' M] in
/-- **A tubular neighbourhood of rank `0` is onto `M`**, so `M` is open in `P`. -/
theorem IsOrientationClass.isOpen_of_finrank_eq_zero {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (hF : Module.finrank ℂ F = 0) : IsOpen M := by
  have : IsEmpty (Fin (Module.finrank ℂ F)) := by rw [hF]; infer_instance
  have hN : ∀ x : M, Subsingleton (N x) := fun x ↦ by
    obtain ⟨ψ, -⟩ := hu.1 x
    exact ψ.symm.injective.subsingleton
  have hrange : range φ = M := by
    refine subset_antisymm ?_ fun y hy ↦ ⟨zeroSection F N ⟨y, hy⟩, φ.map_zeroSection ⟨y, hy⟩⟩
    rintro _ ⟨⟨b, w⟩, rfl⟩
    obtain rfl : w = 0 := (hN b).elim w 0
    change φ.toFun (zeroSection F N b) ∈ M
    rw [φ.map_zeroSection]
    exact b.2
  rw [← hrange]
  exact φ.isOpenEmbedding.isOpen_range

/-- **`u_{M,P} ∩ μ_P = μ_M` in codimension `0`.** Let `M` be a closed complex submanifold of the
second countable complex manifold `P` with a tubular neighbourhood of rank `0` (so `M` is open
and closed in `P`), `u ∈ H^0(P, P - M)` its orientation class and `μ_P` the fundamental class of
`P`. Then `u ∩ μ_P ∈ H_{2m} M` is the fundamental class of `M` for its complex orientation. -/
theorem IsOrientationClass.isFundamentalClass_capProductSupport_of_eq_zero
    (hM : IsComplexSubmanifold E E' M) (hMc : IsClosed M)
    (hXd : HasProperNeighbourhoodDeformations M) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {μP : borelMooreHomology R (ModuleCat.of R R) P (2 * Module.finrank ℂ E : ℕ)}
    (hμP : IsFundamentalClass (M := P) R (complexOrientationBasisOf E) μP)
    (hF : Module.finrank ℂ F = 0)
    (hdeg : ((2 * Module.finrank ℂ E : ℕ) : ℤ) - (2 * Module.finrank ℂ F : ℕ) =
      (2 * Module.finrank ℂ E' : ℕ)) :
    IsFundamentalClass (M := M) R (complexOrientationBasisOf E')
      (congrDegree R _ hdeg (capProductSupport R P hMc hXd _ _ u μP)) := by
  have : TopologicalSpace.MetrizableSpace P := by
    have := ChartedSpace.locallyCompactSpace E P
    exact TopologicalSpace.metrizableSpace_of_t3_secondCountable P
  have hMo := hu.isOpen_of_finrank_eq_zero R hF
  have hdim : Module.finrank ℂ E = Module.finrank ℂ E' := by
    rw [hF] at hdeg
    push_cast at hdeg
    omega
  have hk : ((2 * Module.finrank ℂ E : ℕ) : ℤ) = (2 * Module.finrank ℂ E' : ℕ) := by
    rw [hdim]
  set V : TopologicalSpace.Opens P := ⟨M, hMo⟩
  have hVu : ∀ y : TopCat.of V, y ∈ (inclHom V).hom ⁻¹' M := fun y ↦ y.2
  have hXVd : HasProperNeighbourhoodDeformations ((inclHom V).hom ⁻¹' M) :=
    hasProperNeighbourhoodDeformations_of_forall_mem hVu
  let ρ : TopCat.of V ≃ₜ V := Homeomorph.refl _
  have hρu : ∀ y : TopCat.of V,
      y ∈ (TopCat.ofHom (ρ : C(TopCat.of V, V))).hom ⁻¹' ((inclHom V).hom ⁻¹' M) :=
    fun y ↦ y.2
  have hX'd := hasProperNeighbourhoodDeformations_of_forall_mem hρu
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R Mᶜ (2 * Module.finrank ℂ F) u)
  have hα1 := hu.apply_eq_one_of_finrank_eq_zero R hF hα hrep.symm
  have ha : (pushforward R (ModuleCat.of R R) (TopCat.ofHom (ρ : C(TopCat.of V, V)))
      ρ.isProperMap _).hom ((restrict R (ModuleCat.of R R) V _).hom μP) =
      (restrict R (ModuleCat.of R R) V _).hom μP :=
    pushforward_id_apply' R _ _ rfl _ _
  intro e' he' x v hv hvt
  refine IsLocallyClassOf.restrict (chartOpens e') ?_
  set σ₀ := inclChainSimplex (chartOpens e') (chartSimplex e' v hvt)
  refine isLocallyClassOf_capProductSupport_of_homeomorph R P hMc hXd V hXVd
    (W := TopCat.of V) ρ hX'd _ _ hdeg u μP _ ha
    (p := ⟨⟨x.1.1, x.1.2⟩, x.1.2⟩)
    (σ := ⟨fun t ↦ ⟨⟨(σ₀ t : P), (σ₀ t).2⟩, (σ₀ t).2⟩,
      ((continuous_subtype_val.comp σ₀.continuous).subtype_mk _).subtype_mk _⟩) ?_ x.1 rfl _
    (fun t ↦ rfl)
  rw [capProductSupportPullback_apply]
  refine isLocallyClassOf_capProductSupport_of_eq_one R _ _ hX'd hρu (by omega) _ hdeg hk _ ?_ _ ?_
  · rw [relativeSingularCohomologyEquiv_pullback, relativeSingularCohomologyEquiv_pullback,
      ← hrep]
    erw [relCohomologyMap_mk]
    exact ⟨_, _, rfl, fun τ ↦ hα1 _ (fun t ↦ (τ t).2)⟩
  · exact hμP.isLocallyClassOf_restrict_open R hM hMo hdim hk he' x.2 hv hvt

/-- **`u_{M,P} ∩ μ_P = μ_M`** (Fulton, §19.1, (9); [BT] 4.1.3). Let `M` be a closed complex
submanifold of the (Hausdorff, second countable) complex manifold `P`, with arbitrarily small
proper neighbourhood deformations, `u ∈ H^{2d}(P, P - M)` its orientation class
(`def_c19_orientation_class_submanifold`) and `μ_P` the fundamental class of `P`. Then
`u ∩ μ_P ∈ H_{2m} M` is the fundamental class `μ_M` of `M` for its complex orientation. -/
theorem IsOrientationClass.isFundamentalClass_capProductSupport
    (hM : IsComplexSubmanifold E E' M) (hMc : IsClosed M)
    (hXd : HasProperNeighbourhoodDeformations M) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {μP : borelMooreHomology R (ModuleCat.of R R) P (2 * Module.finrank ℂ E : ℕ)}
    (hμP : IsFundamentalClass (M := P) R (complexOrientationBasisOf E) μP)
    (hdeg : ((2 * Module.finrank ℂ E : ℕ) : ℤ) - (2 * Module.finrank ℂ F : ℕ) =
      (2 * Module.finrank ℂ E' : ℕ)) :
    IsFundamentalClass (M := M) R (complexOrientationBasisOf E')
      (congrDegree R _ hdeg (capProductSupport R P hMc hXd _ _ u μP)) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ F) with hF | hF
  · exact hu.isFundamentalClass_capProductSupport_of_eq_zero R hM hMc hXd hμP hF hdeg
  · exact hu.isFundamentalClass_capProductSupport_of_pos R hM hMc hXd hμP hF hdeg

end Assembly

end MMP
