module

public import MMP.AlgebraicTopology.OrientationClass.CupCompositeNaturality
public import MMP.AlgebraicTopology.ThomClass.DirectSumEuclidean
public import MMP.AlgebraicTopology.OrientationClass.Point
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# The Thom class of a direct sum (Fulton, §19.1)

For complex topological vector bundles `E₁`, `E₂` on a space `B` with Thom classes `u₁`, `u₂`, the
class `pr₁^* u₁ ∪ pr₂^* u₂ ∈ H^{2(r₁ + r₂)}(E₁ ⊕ E₂, E₁ ⊕ E₂ - 0)` is a Thom class of the direct
sum `E₁ ⊕ E₂ = E₁ ×ᵇ E₂`, `pr₁`, `pr₂` the projections of the total space of `E₁ ⊕ E₂` to those of
`E₁`, `E₂`.

The Thom condition is checked on one fibre at a time. A complex frame `ψ` of `(E₁ ⊕ E₂)_x` is
`ψ = (ψ₁ × ψ₂) ∘ L` for complex frames `ψ₁`, `ψ₂` of `E₁_x`, `E₂_x` and a complex linear
isomorphism `L : ℂ^{r₁ + r₂} ≅ ℂ^{r₁} × ℂ^{r₂}`; `L` carries simplices oriented for the complex
orientation of `ℂ^{r₁ + r₂}` to simplices oriented for the product of the complex orientations
(`isOrientedSimplexAroundZero_map_prod`). Pulling back along `ψ₁ × ψ₂`, the cup product becomes
the cup product `fst^* α ∪ snd^* β` of the Thom cocycles `α`, `β` of the fibres, whose value on an
oriented simplex is `1` (`MMP.ThomClass.relCupCochain_cochainPullback_fst_snd_affineSimplex`).

## Main definitions

* `MMP.ThomClass.prodFstHom`, `MMP.ThomClass.prodSndHom`: the projections of `E₁ ⊕ E₂`.
* `MMP.ThomClass.thomCup`: the class `pr₁^* u₁ ∪ pr₂^* u₂`.

## Main results

* `MMP.ThomClass.isClosed_range_zeroSection`: the zero section is closed.
* `MMP.ThomClass.isOrientedSimplexAroundZero_map_prod`: complex linear isomorphisms
  `ℂ^N ≅ ℂ^d × ℂ^e` preserve the complex orientations.
* `MMP.ThomClass.IsThomClass.thomCup`: `pr₁^* u₁ ∪ pr₂^* u₂` is a Thom class.

## References

* [J. Milnor, J. Stasheff, *Characteristic classes*][milnorstasheff1974], §9.
-/

@[expose] public noncomputable section

open Bundle Set CategoryTheory

namespace MMP

namespace ThomClass

/-! ### Coordinates of the complex orientation basis -/

/-- The `k`-th vector of `complexOrientationBasis r` is `e_{k/2}` for `k` even and `i e_{k/2}`
for `k` odd. -/
lemma complexOrientationBasis_apply_apply (r : ℕ) (k : Fin (2 * r)) (j : Fin r) :
    complexOrientationBasis r k j =
      if (k : ℕ) / 2 = j then (if (k : ℕ) % 2 = 0 then 1 else Complex.I) else 0 := by
  simp only [complexOrientationBasis, Module.Basis.reindex_apply, Equiv.symm_trans_apply,
    finProdFinEquiv_symm_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Module.Basis.smulTower_apply, Pi.basisFun_apply]
  set k' := (finCongr (Nat.mul_comm r 2)).symm k
  have hk : (k' : ℕ) = k := rfl
  rw [Pi.smul_apply, Pi.single_apply]
  have hd : ((k'.divNat : Fin r) : ℕ) = k / 2 := by simp [Fin.coe_divNat, hk]
  have hm : ((k'.modNat : Fin 2) : ℕ) = k % 2 := by simp [Fin.coe_modNat, hk]
  by_cases h : (k : ℕ) / 2 = j
  · rw [ite_eq_left (Fin.ext (by rw [hd, h])), ite_eq_left h, smul_eq_mul, mul_one]
    rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
    · rw [ite_eq_left h2, show k'.modNat = 0 from Fin.ext (by rw [hm, h2]; rfl)]
      simp
    · rw [ite_eq_right (by omega), show k'.modNat = 1 from Fin.ext (by rw [hm, h2]; rfl)]
      simp
  · rw [ite_eq_right (fun h' ↦ h (by rw [← hd, h'])), ite_eq_right h, smul_zero]

/-- The splitting `ℂ^N ≅ ℂ^d × ℂ^e`, `N = d + e`, into the first `d` and the last `e`
coordinates. -/
def finSplitLinearEquiv {d e N : ℕ} (h : N = d + e) :
    (Fin N → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) × (Fin e → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (finSumFinEquiv.trans (finCongr h.symm))).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin d) (Fin e) ℂ ℂ)

/-- The first component of `finSplitLinearEquiv h w` consists of the first `d` coordinates of
`w`. -/
@[simp]
lemma finSplitLinearEquiv_apply_fst {d e N : ℕ} (h : N = d + e) (w : Fin N → ℂ) (j : Fin d) :
    (finSplitLinearEquiv h w).1 j = w ⟨j, by omega⟩ := rfl

/-- The second component of `finSplitLinearEquiv h w` consists of the last `e` coordinates of
`w`. -/
@[simp]
lemma finSplitLinearEquiv_apply_snd {d e N : ℕ} (h : N = d + e) (w : Fin N → ℂ) (j : Fin e) :
    (finSplitLinearEquiv h w).2 j = w ⟨d + j, by omega⟩ := rfl

/-- The splitting `ℂ^{d + e} ≅ ℂ^d × ℂ^e` carries the complex orientation basis of `ℂ^{d + e}` to
the product of those of `ℂ^d` and `ℂ^e`. -/
lemma finSplitLinearEquiv_complexOrientationBasis {d e N : ℕ} (h : N = d + e)
    (h2 : 2 * d + 2 * e = 2 * N) (k : Fin (2 * N)) :
    finSplitLinearEquiv h (complexOrientationBasis N k) =
      ((((complexOrientationBasis d).prod (complexOrientationBasis e)).reindex
        finSumFinEquiv).reindex (finCongr h2)) k := by
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  set k' : Fin (2 * d + 2 * e) := (finCongr h2).symm k
  have hk : (k' : ℕ) = k := rfl
  by_cases hkd : (k : ℕ) < 2 * d
  · have : finSumFinEquiv.symm k' = Sum.inl ⟨k, hkd⟩ := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp [hk])
    rw [this]
    ext j
    · rw [Module.Basis.prod_apply_inl_fst, finSplitLinearEquiv_apply_fst,
        complexOrientationBasis_apply_apply, complexOrientationBasis_apply_apply]
    · rw [Module.Basis.prod_apply_inl_snd, finSplitLinearEquiv_apply_snd,
        complexOrientationBasis_apply_apply, Pi.zero_apply, ite_eq_right (by simp; omega)]
  · have : finSumFinEquiv.symm k' = Sum.inr ⟨k - 2 * d, by omega⟩ := by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp [hk]; omega)
    rw [this]
    ext j
    · rw [Module.Basis.prod_apply_inr_fst, finSplitLinearEquiv_apply_fst,
        complexOrientationBasis_apply_apply, Pi.zero_apply, ite_eq_right (by simp; omega)]
    · rw [Module.Basis.prod_apply_inr_snd, finSplitLinearEquiv_apply_snd,
        complexOrientationBasis_apply_apply, complexOrientationBasis_apply_apply]
      simp only
      have e1 : ((k : ℕ) / 2 = d + j) ↔ ((k : ℕ) - 2 * d) / 2 = j := by omega
      have e2 : ((k : ℕ) % 2 = 0) ↔ ((k : ℕ) - 2 * d) % 2 = 0 := by omega
      simp only [e1, e2]

/-- **Complex linear isomorphisms `ℂ^N ≅ ℂ^d × ℂ^e` preserve the complex orientations**: they carry
simplices around `0` oriented for the complex orientation of `ℂ^N` to simplices around `0`
oriented for the product of the complex orientations of `ℂ^d` and `ℂ^e`. -/
lemma isOrientedSimplexAroundZero_map_prod {d e N : ℕ} (h : N = d + e)
    (h2 : 2 * d + 2 * e = 2 * N) (L : (Fin N → ℂ) ≃ₗ[ℂ] (Fin d → ℂ) × (Fin e → ℂ))
    {v : Fin (2 * N + 1) → (Fin N → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis N) v) :
    IsOrientedSimplexAroundZero ((((complexOrientationBasis d).prod
      (complexOrientationBasis e)).reindex finSumFinEquiv).reindex (finCongr h2))
      (fun k ↦ L (v k)) := by
  set P := (((complexOrientationBasis d).prod
      (complexOrientationBasis e)).reindex finSumFinEquiv).reindex (finCongr h2)
  set K : ((Fin d → ℂ) × (Fin e → ℂ)) ≃ₗ[ℂ] ((Fin d → ℂ) × (Fin e → ℂ)) :=
    (finSplitLinearEquiv h).symm.trans L
  have hL : (L.toLinearMap.restrictScalars ℝ) ∘ complexOrientationBasis N =
      (K.toLinearMap.restrictScalars ℝ) ∘ P := by
    funext k
    simp only [Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, K, P,
      ← finSplitLinearEquiv_complexOrientationBasis h h2, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply]
  have hdet : 0 < P.det ((L.toLinearMap.restrictScalars ℝ) ∘ complexOrientationBasis N) := by
    rw [hL, FundamentalClass.basis_det_comp_self, LinearMap.det_restrictScalars,
      Algebra.norm_complex_apply, Complex.normSq_pos]
    exact (LinearEquiv.isUnit_det' K).ne_zero
  exact hv.map_linearMap _ hdet

/-! ### The zero section -/

section ZeroSection

/-- A point of the total space lies on the zero section if and only if it is the zero vector of
its fibre. -/
lemma mem_range_zeroSection_iff_snd_eq_zero {B F : Type*} {E : B → Type*}
    [∀ x, Zero (E x)] {p : TotalSpace F E} :
    p ∈ range (zeroSection F E) ↔ p.2 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩; rfl
  · obtain ⟨b, y⟩ := p
    rintro (h : y = 0)
    exact ⟨b, by rw [h]; rfl⟩

variable {B : Type*} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
  (E : B → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [_root_.VectorBundle ℂ F E]

/-- The zero section of a complex topological vector bundle is closed. -/
lemma isClosed_range_zeroSection : IsClosed (range (zeroSection F E)) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  rw [mem_compl_iff, mem_range_zeroSection_iff_snd_eq_zero] at hp
  set e := trivializationAt F E p.proj
  have hpe : p ∈ e.source := e.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt F E p.proj)
  have hU : IsOpen (e.source ∩ e ⁻¹' {z | z.2 ≠ 0}) :=
    e.continuousOn.isOpen_inter_preimage e.open_source
      (isOpen_ne_fun continuous_snd continuous_const)
  have key : ∀ q ∈ e.source, (e q).2 = 0 ↔ q.2 = 0 := fun q hq ↦ by
    have hb : q.proj ∈ e.baseSet := e.mem_source.1 hq
    have h' : (e q).2 = e.linearEquivAt ℂ q.proj hb q.2 := by
      rw [Trivialization.linearEquivAt_apply]
    rw [h', LinearEquiv.map_eq_zero_iff]
  refine Filter.mem_of_superset (hU.mem_nhds ⟨hpe, fun h ↦ hp ((key p hpe).1 h)⟩) ?_
  rintro q ⟨hq, hq'⟩
  rw [mem_compl_iff, mem_range_zeroSection_iff_snd_eq_zero]
  exact fun h ↦ hq' ((key q hq).2 h)

end ZeroSection

/-! ### The direct sum -/

section DirectSum

open SingularChain SingularCochain cohomologyWithSupports

variable {R : Type} [CommRing R] {B : Type} [TopologicalSpace B]
  (F₁ : Type) [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  (E₁ : B → Type) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [_root_.VectorBundle ℂ F₁ E₁]
  (F₂ : Type) [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  (E₂ : B → Type) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℂ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [_root_.VectorBundle ℂ F₂ E₂]

/-- The projection `E₁ ⊕ E₂ → E₁` of total spaces. -/
def prodFstHom : TopCat.of (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) ⟶ TopCat.of (TotalSpace F₁ E₁) :=
  TopCat.ofHom ⟨fun p ↦ ⟨p.proj, p.2.1⟩,
    continuous_fst.comp (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous⟩

/-- The projection `E₁ ⊕ E₂ → E₂` of total spaces. -/
def prodSndHom : TopCat.of (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) ⟶ TopCat.of (TotalSpace F₂ E₂) :=
  TopCat.ofHom ⟨fun p ↦ ⟨p.proj, p.2.2⟩,
    continuous_snd.comp (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous⟩

omit [FiniteDimensional ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  [∀ x, Module ℂ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
  [_root_.VectorBundle ℂ F₂ E₂] in
/-- The inverse image in `E₁ ⊕ E₂` of the zero section of `E₁` is closed. -/
lemma isClosed_preimage_prodFstHom :
    IsClosed (prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁)) :=
  (isClosed_range_zeroSection F₁ E₁).preimage (prodFstHom F₁ E₁ F₂ E₂).hom.continuous

omit [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁] [∀ x, Module ℂ (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [_root_.VectorBundle ℂ F₁ E₁]
  [FiniteDimensional ℂ F₂] in
/-- The inverse image in `E₁ ⊕ E₂` of the zero section of `E₂` is closed. -/
lemma isClosed_preimage_prodSndHom :
    IsClosed (prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂)) :=
  (isClosed_range_zeroSection F₂ E₂).preimage (prodSndHom F₁ E₁ F₂ E₂).hom.continuous

omit [TopologicalSpace B] [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [FiniteDimensional ℂ F₁]
  [∀ x, Module ℂ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
  [_root_.VectorBundle ℂ F₁ E₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [FiniteDimensional ℂ F₂]
  [∀ x, Module ℂ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
  [_root_.VectorBundle ℂ F₂ E₂] in
/-- The zero section of `E₁ ⊕ E₂` is the intersection of the inverse images of those of `E₁`
and `E₂`. -/
lemma preimage_prodFstHom_inter_preimage_prodSndHom :
    prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁) ∩
        prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂) =
      range (zeroSection (F₁ × F₂) (E₁ ×ᵇ E₂)) := by
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_range_zeroSection_iff_snd_eq_zero]
  exact ⟨fun h ↦ Prod.ext h.1 h.2, fun h ↦ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

/-- `2 r₁ + 2 r₂ = 2 (r₁ + r₂)` for the ranks `r₁`, `r₂` of `F₁`, `F₂`, as natural numbers. -/
lemma two_mul_finrank_add_two_mul_finrank_nat :
    2 * Module.finrank ℂ F₁ + 2 * Module.finrank ℂ F₂ = 2 * Module.finrank ℂ (F₁ × F₂) := by
  rw [Module.finrank_prod]; ring

/-- `2 r₁ + 2 r₂ = 2 (r₁ + r₂)` for the ranks `r₁`, `r₂` of `F₁`, `F₂`, as integers. -/
lemma two_mul_finrank_add_two_mul_finrank :
    ((2 * Module.finrank ℂ F₁ : ℕ) : ℤ) + ((2 * Module.finrank ℂ F₂ : ℕ) : ℤ) =
      ((2 * Module.finrank ℂ (F₁ × F₂) : ℕ) : ℤ) := by
  exact_mod_cast two_mul_finrank_add_two_mul_finrank_nat F₁ F₂

/-- The class `pr₁^* u₁ ∪ pr₂^* u₂ ∈ H^{2(r₁ + r₂)}(E₁ ⊕ E₂, E₁ ⊕ E₂ - 0)` of classes
`u₁ ∈ H^{2r₁}(E₁, E₁ - 0)`, `u₂ ∈ H^{2r₂}(E₂, E₂ - 0)`. -/
def thomCup
    (u₁ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F₁ E₁))
      (range (zeroSection F₁ E₁)) (2 * Module.finrank ℂ F₁ : ℕ))
    (u₂ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F₂ E₂))
      (range (zeroSection F₂ E₂)) (2 * Module.finrank ℂ F₂ : ℕ)) :
    cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)))
      (range (zeroSection (F₁ × F₂) (E₁ ×ᵇ E₂))) (2 * Module.finrank ℂ (F₁ × F₂) : ℕ) :=
  congrIndex R _ (congrArg compl (preimage_prodFstHom_inter_preimage_prodSndHom F₁ E₁ F₂ E₂))
    (two_mul_finrank_add_two_mul_finrank F₁ F₂)
    (cup R _ (isClosed_preimage_prodFstHom F₁ E₁ F₂ E₂) (isClosed_preimage_prodSndHom F₁ E₁ F₂ E₂)
      _ _ ((pullback R _ (prodFstHom F₁ E₁ F₂ E₂) _ _).hom u₁)
      ((pullback R _ (prodSndHom F₁ E₁ F₂ E₂) _ _).hom u₂))

/-- `congrIndex` along `S = S'` sends the class of a cocycle `x` to the class of the same
cochain `x'`, viewed as a cocycle relative to `S'`. -/
lemma relativeSingularCohomologyEquiv_congrIndex_symm {Y : TopCat.{0}} {S S' : Set Y}
    (hS : S = S') {n : ℕ} (x : relCocycles R S n) (x' : relCocycles R S' n)
    (hxx' : (x : Simplex Y n → R) = x') :
    relativeSingularCohomologyEquiv R S' n (congrIndex R Y hS rfl
        ((relativeSingularCohomologyEquiv R S n).symm (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk x' := by
  rw [congrIndex_symm_mk R Y hS n x x' hxx', LinearEquiv.apply_symm_apply]

/-- The relative cup product of the pull-backs of relative cocycles of `(E₁, E₁ - 0)` and
`(E₂, E₂ - 0)` is a relative cocycle of `(E₁ ⊕ E₂, E₁ ⊕ E₂ - 0)`. -/
theorem relCupCochain_cochainPullback_mem_relCocycles
    (φ₁ : relCocycles R (range (zeroSection F₁ E₁))ᶜ (2 * Module.finrank ℂ F₁))
    (φ₂ : relCocycles R (range (zeroSection F₂ E₂))ᶜ (2 * Module.finrank ℂ F₂)) :
    relCupCochain
        (A := (prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁))ᶜ)
        (B := (prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂))ᶜ)
        (2 * Module.finrank ℂ F₁) (2 * Module.finrank ℂ F₂) (2 * Module.finrank ℂ (F₁ × F₂))
        (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂)
        (cochainPullback R (prodFstHom F₁ E₁ F₂ E₂) _ φ₁.1)
        (cochainPullback R (prodSndHom F₁ E₁ F₂ E₂) _ φ₂.1) ∈
      relCocycles R (range (zeroSection (F₁ × F₂) (E₁ ×ᵇ E₂)))ᶜ
        (2 * Module.finrank ℂ (F₁ × F₂)) := by
  rw [← preimage_prodFstHom_inter_preimage_prodSndHom F₁ E₁ F₂ E₂, compl_inter]
  exact relCupCochain_mem_relCocycles (isClosed_preimage_prodFstHom F₁ E₁ F₂ E₂).isOpen_compl
    (isClosed_preimage_prodSndHom F₁ E₁ F₂ E₂).isOpen_compl _ _ _ _
    (cochainPullback_mem_relCocycles (prodFstHom F₁ E₁ F₂ E₂)
      (A' := (prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁))ᶜ)
      (A := (range (zeroSection F₁ E₁))ᶜ) (fun _ hx ↦ hx) φ₁.2)
    (cochainPullback_mem_relCocycles (prodSndHom F₁ E₁ F₂ E₂)
      (A' := (prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂))ᶜ)
      (A := (range (zeroSection F₂ E₂))ᶜ) (fun _ hx ↦ hx) φ₂.2)

/-- On cocycles, `pr₁^* u₁ ∪ pr₂^* u₂` is the class of the relative cup product
`ρ^* (pr₁^* φ₁ ∪ pr₂^* φ₂)` of cocycles `φ₁`, `φ₂` representing `u₁`, `u₂`. -/
lemma relativeSingularCohomologyEquiv_thomCup
    (u₁ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F₁ E₁))
      (range (zeroSection F₁ E₁)) (2 * Module.finrank ℂ F₁ : ℕ))
    (u₂ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F₂ E₂))
      (range (zeroSection F₂ E₂)) (2 * Module.finrank ℂ F₂ : ℕ))
    (φ₁ : relCocycles R (range (zeroSection F₁ E₁))ᶜ (2 * Module.finrank ℂ F₁))
    (φ₂ : relCocycles R (range (zeroSection F₂ E₂))ᶜ (2 * Module.finrank ℂ F₂))
    (hu₁ : relativeSingularCohomologyEquiv R _ _ u₁ = Submodule.Quotient.mk φ₁)
    (hu₂ : relativeSingularCohomologyEquiv R _ _ u₂ = Submodule.Quotient.mk φ₂) :
    relativeSingularCohomologyEquiv R _ _ (thomCup F₁ E₁ F₂ E₂ u₁ u₂) =
      Submodule.Quotient.mk ⟨relCupCochain
        (A := (prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁))ᶜ)
        (B := (prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂))ᶜ)
        (2 * Module.finrank ℂ F₁) (2 * Module.finrank ℂ F₂) (2 * Module.finrank ℂ (F₁ × F₂))
        (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂)
        (cochainPullback R (prodFstHom F₁ E₁ F₂ E₂) _ φ₁.1)
        (cochainPullback R (prodSndHom F₁ E₁ F₂ E₂) _ φ₂.1),
        relCupCochain_cochainPullback_mem_relCocycles F₁ E₁ F₂ E₂ φ₁ φ₂⟩ := by
  rw [thomCup, cup_natCast_eq R _ _ _ _ _ _ (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂),
    congrIndex_congrIndex]
  have e₁ := relativeSingularCohomologyEquiv_map (R := R) (prodFstHom F₁ E₁ F₂ E₂)
    (A' := (prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁))ᶜ)
    (A := (range (zeroSection F₁ E₁))ᶜ) (fun _ hx ↦ hx) (2 * Module.finrank ℂ F₁) u₁
  have e₂ := relativeSingularCohomologyEquiv_map (R := R) (prodSndHom F₁ E₁ F₂ E₂)
    (A' := (prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂))ᶜ)
    (A := (range (zeroSection F₂ E₂))ᶜ) (fun _ hx ↦ hx) (2 * Module.finrank ℂ F₂) u₂
  rw [hu₁] at e₁
  rw [hu₂] at e₂
  simp only [cohomologyWithSupports.pullback]
  erw [e₁, e₂]
  exact relativeSingularCohomologyEquiv_congrIndex_symm _ _ _ rfl

/-- The complex frame `ℂ^{rank F₁} ≅ E₁ x` of the fibre at `x` given by the trivialization
`trivializationAt F₁ E₁ x`. -/
def fibreFrame (x : B) : (Fin (Module.finrank ℂ F₁) → ℂ) ≃L[ℂ] E₁ x :=
  (ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])).trans
    ((trivializationAt F₁ E₁ x).continuousLinearEquivAt ℂ x
      (FiberBundle.mem_baseSet_trivializationAt' x)).symm

variable {F₁ E₁ F₂ E₂} in
/-- The map `(w₁, w₂) ↦ (ψ₁ w₁, ψ₂ w₂)` of `ℂ^{r₁} × ℂ^{r₂}` onto the fibre of `E₁ ⊕ E₂` at `x`,
for complex frames `ψ₁`, `ψ₂` of `E₁_x`, `E₂_x`. -/
def prodFrameMap (x : B) (ψ₁ : (Fin (Module.finrank ℂ F₁) → ℂ) ≃L[ℂ] E₁ x)
    (ψ₂ : (Fin (Module.finrank ℂ F₂) → ℂ) ≃L[ℂ] E₂ x) :
    C((Fin (Module.finrank ℂ F₁) → ℂ) × (Fin (Module.finrank ℂ F₂) → ℂ),
      TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :=
  ⟨fun w ↦ ⟨x, (ψ₁ w.1, ψ₂ w.2)⟩, by
    refine (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous_iff.2 ?_
    exact ((FiberBundle.continuous_totalSpaceMk F₁ E₁ x).comp
      (ψ₁.continuous.comp continuous_fst)).prodMk
      ((FiberBundle.continuous_totalSpaceMk F₂ E₂ x).comp (ψ₂.continuous.comp continuous_snd))⟩

variable {F₁ E₁ F₂ E₂} in
/-- The fibre map `w ↦ ψ₁ w` of a complex frame `ψ₁` of `E₁_x`, into the total space. -/
def frameMap (x : B) (ψ₁ : (Fin (Module.finrank ℂ F₁) → ℂ) ≃L[ℂ] E₁ x) :
    C(Fin (Module.finrank ℂ F₁) → ℂ, TotalSpace F₁ E₁) :=
  ⟨fun w ↦ ⟨x, ψ₁ w⟩, (FiberBundle.continuous_totalSpaceMk F₁ E₁ x).comp ψ₁.continuous⟩

variable {F₁ E₁ F₂ E₂} in
/-- **The Thom class of a direct sum** (Milnor–Stasheff, §9): if `u₁`, `u₂` are Thom classes of
`E₁`, `E₂`, then `pr₁^* u₁ ∪ pr₂^* u₂` is a Thom class of `E₁ ⊕ E₂`. -/
theorem IsThomClass.thomCup
    {u₁ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F₁ E₁))
      (range (zeroSection F₁ E₁)) (2 * Module.finrank ℂ F₁ : ℕ)}
    {u₂ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (TotalSpace F₂ E₂))
      (range (zeroSection F₂ E₂)) (2 * Module.finrank ℂ F₂ : ℕ)}
    (h₁ : IsThomClass F₁ E₁ u₁) (h₂ : IsThomClass F₂ E₂ u₂) :
    IsThomClass (F₁ × F₂) (E₁ ×ᵇ E₂) (thomCup F₁ E₁ F₂ E₂ u₁ u₂) := by
  intro x ψ v hv
  obtain ⟨φ₁, hφ₁⟩ := Submodule.Quotient.mk_surjective _ (relativeSingularCohomologyEquiv R _ _ u₁)
  obtain ⟨φ₂, hφ₂⟩ := Submodule.Quotient.mk_surjective _ (relativeSingularCohomologyEquiv R _ _ u₂)
  rw [relativeSingularCohomologyEquiv_thomCup F₁ E₁ F₂ E₂ u₁ u₂ φ₁ φ₂ hφ₁.symm hφ₂.symm,
    relEval_mk]
  set ψ₁ := fibreFrame F₁ E₁ x
  set ψ₂ := fibreFrame F₂ E₂ x
  set L : (Fin (Module.finrank ℂ (F₁ × F₂)) → ℂ) ≃ₗ[ℂ]
      (Fin (Module.finrank ℂ F₁) → ℂ) × (Fin (Module.finrank ℂ F₂) → ℂ) :=
    ψ.toLinearEquiv.trans (ψ₁.symm.toLinearEquiv.prodCongr ψ₂.symm.toLinearEquiv)
  set Φ := prodFrameMap x ψ₁ ψ₂
  have hL : ∀ t, affineSimplex (fun k ↦ L (v k)) t = L (affineSimplex v t) := fun t ↦ by
    simp only [affineSimplex_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ ((L.toLinearMap.restrictScalars ℝ).map_smul _ _).symm
  have hfs : fibreSimplex (F₁ × F₂) x ψ v = Φ.comp (affineSimplex fun k ↦ L (v k)) := by
    ext1 t
    rw [ContinuousMap.comp_apply, hL, fibreSimplex_apply]
    simp [Φ, prodFrameMap, L]
  rw [hfs, Finsupp.linearCombination_single, one_smul]
  set α := cochainPullback R (TopCat.ofHom (frameMap x ψ₁)) _ φ₁.1
  set β := cochainPullback R (TopCat.ofHom (frameMap x ψ₂)) _ φ₂.1
  have hα : α ∈ relCocycles R ({0}ᶜ : Set (Fin (Module.finrank ℂ F₁) → ℂ)) _ :=
    cochainPullback_mem_relCocycles (TopCat.ofHom (frameMap x ψ₁))
      (A' := ({0}ᶜ : Set (Fin (Module.finrank ℂ F₁) → ℂ))) (A := (range (zeroSection F₁ E₁))ᶜ)
      (fun w hw h ↦ hw (by
        rw [mem_range_zeroSection_iff_snd_eq_zero] at h
        exact ψ₁.map_eq_zero_iff.1 h)) φ₁.2
  have hβ : β ∈ relCocycles R ({0}ᶜ : Set (Fin (Module.finrank ℂ F₂) → ℂ)) _ :=
    cochainPullback_mem_relCocycles (TopCat.ofHom (frameMap x ψ₂))
      (A' := ({0}ᶜ : Set (Fin (Module.finrank ℂ F₂) → ℂ))) (A := (range (zeroSection F₂ E₂))ᶜ)
      (fun w hw h ↦ hw (by
        rw [mem_range_zeroSection_iff_snd_eq_zero] at h
        exact ψ₂.map_eq_zero_iff.1 h)) φ₂.2
  have hα1 : ∀ v₁, IsOrientedSimplexAroundZero (complexOrientationBasis _) v₁ →
      α (affineSimplex v₁) = 1 := fun v₁ hv₁ ↦ by
    have := h₁ x ψ₁ v₁ hv₁
    rw [← hφ₁, relEval_mk, Finsupp.linearCombination_single, one_smul] at this
    exact this
  have hβ1 : ∀ v₂, IsOrientedSimplexAroundZero (complexOrientationBasis _) v₂ →
      β (affineSimplex v₂) = 1 := fun v₂ hv₂ ↦ by
    have := h₂ x ψ₂ v₂ hv₂
    rw [← hφ₂, relEval_mk, Finsupp.linearCombination_single, one_smul] at this
    exact this
  have hw := isOrientedSimplexAroundZero_map_prod Module.finrank_prod
    (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂) L hv
  have hcore := relCupCochain_cochainPullback_fst_snd_affineSimplex (R := R)
    (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂) (complexOrientationBasis _)
    (complexOrientationBasis _) hα hα1 hβ hβ1 hw
  set A := (prodFstHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₁ E₁))ᶜ
  set B := (prodSndHom F₁ E₁ F₂ E₂ ⁻¹' range (zeroSection F₂ E₂))ᶜ
  set A' : Set ((Fin (Module.finrank ℂ F₁) → ℂ) × (Fin (Module.finrank ℂ F₂) → ℂ)) :=
    Prod.fst ⁻¹' {0}ᶜ
  set B' : Set ((Fin (Module.finrank ℂ F₁) → ℂ) × (Fin (Module.finrank ℂ F₂) → ℂ)) :=
    Prod.snd ⁻¹' {0}ᶜ
  have hc₁ := cochainPullback_mem_relCocycles (prodFstHom F₁ E₁ F₂ E₂)
      (A' := A) (A := (range (zeroSection F₁ E₁))ᶜ) (fun _ hx ↦ hx) φ₁.2
  have hc₂ := cochainPullback_mem_relCocycles (prodSndHom F₁ E₁ F₂ E₂)
      (A' := B) (A := (range (zeroSection F₂ E₂))ᶜ) (fun _ hx ↦ hx) φ₂.2
  have hAA : A' ⊆ (TopCat.ofHom Φ) ⁻¹' A := fun w hw h ↦ hw (by
    change TotalSpace.mk x (ψ₁ w.1) ∈ range (zeroSection F₁ E₁) at h
    rw [mem_range_zeroSection_iff_snd_eq_zero] at h
    exact ψ₁.map_eq_zero_iff.1 h)
  have hBB : B' ⊆ (TopCat.ofHom Φ) ⁻¹' B := fun w hw h ↦ hw (by
    change TotalSpace.mk x (ψ₂ w.2) ∈ range (zeroSection F₂ E₂) at h
    rw [mem_range_zeroSection_iff_snd_eq_zero] at h
    exact ψ₂.map_eq_zero_iff.1 h)
  have key := cochainPullback_pullback_smallChainMap_sub_mem_relCoboundaries (TopCat.ofHom Φ)
    (isClosed_preimage_prodFstHom F₁ E₁ F₂ E₂).isOpen_compl
    (isClosed_preimage_prodSndHom F₁ E₁ F₂ E₂).isOpen_compl
    (isOpen_compl_singleton.preimage continuous_fst)
    (isOpen_compl_singleton.preimage continuous_snd)
    hAA hBB (cup_mem_vanishing (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂) hc₁.1 hc₂.1)
    (coboundary_cup_eq_zero _ _ _ (two_mul_finrank_add_two_mul_finrank_nat F₁ F₂) hc₁.2 hc₂.2)
  have hbd : ∀ t : stdSimplex ℝ (Fin (2 * Module.finrank ℂ (F₁ × F₂) + 1)), (∃ i, t i = 0) →
      affineSimplex (fun k ↦ L (v k)) t ∈ A' ∪ B' := fun t ht ↦ by
    rw [hL]
    have h0 : L (affineSimplex v t) ≠ 0 :=
      fun h ↦ hv.affineSimplex_ne_zero t ht (L.map_eq_zero_iff.1 h)
    by_contra hc
    simp only [mem_union, mem_preimage, mem_compl_iff, mem_singleton_iff, not_or, not_not,
      A', B'] at hc
    exact h0 (Prod.ext hc.1 hc.2)
  have hz := eval_single_eq_zero_of_mem_relCoboundaries _ hbd _ key
  rw [Finsupp.linearCombination_single, one_smul, Pi.sub_apply, sub_eq_zero] at hz
  refine (hz.trans ?_).trans hcore
  rw [cochainPullback_cup]
  rfl

end DirectSum

end ThomClass

end MMP
