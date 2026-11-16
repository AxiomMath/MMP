module

public import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Normalized singular cochains

A singular `n`-cochain is normalized if it vanishes on the degenerate simplices, the simplices
`σ ∘ f` for a monotone non-injective vertex map `f`. Every relative singular cocycle of a pair
`(Y, A)` is cohomologous, through a relative coboundary, to a normalized relative cocycle.

The proof uses the Dold–Kan projection `PInfty` on the alternating face map complex of the
simplicial `R`-module of singular chains: `PInfty` kills the degeneracies, and it is homotopic
to the identity by the homotopy `homotopyPInftyToId`. For a cocycle `φ`, the cochain
`ψ = φ ∘ PInfty` is normalized, and `φ - ψ` is the coboundary of `-(φ ∘ h)` with `h` the
homotopy. Both `PInfty` and the components of `h` are natural in the simplicial object, so they
commute with the map of singular chains induced by the inclusion `A → Y`; hence `ψ` and `φ ∘ h`
vanish on the simplices of `A` when `φ` does.

## Main definitions

* `MMP.SingularCochain.IsNormalized`: vanishing on the degenerate simplices.
* `MMP.SingularCochain.freeSingular`: the simplicial module of singular chains.

## Main results

* `MMP.DoldKanAux.homotopyPToId_hom_naturality`: the components of the homotopies
  `homotopyPToId` are natural.
* `MMP.SingularCochain.exists_isNormalized_sub_mem_relCoboundaries`: every
  relative cocycle differs from a normalized relative cocycle by a relative coboundary.

## References

* [A. Dold, *Lectures on Algebraic Topology*][dold1995], VI.6.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace MMP.DoldKanAux

open AlgebraicTopology AlgebraicTopology.DoldKan

/-- The components of the homotopy `homotopyPToId` from `P q` to the identity are natural in
the simplicial object. -/
theorem homotopyPToId_hom_naturality {C : Type*} [Category* C] [Preadditive C]
    {X X' : SimplicialObject C} (f : X ⟶ X') (q i j : ℕ) :
    f.app (op ⦋i⦌) ≫ (homotopyPToId X' q).hom i j =
      (homotopyPToId X q).hom i j ≫ f.app (op ⦋j⦌) := by
  induction q with
  | zero => simp [homotopyPToId]
  | succ q ih =>
    simp only [homotopyPToId, Homotopy.trans_hom, Homotopy.ofEq_hom,
      Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero, zero_add,
      Preadditive.comp_add, Preadditive.add_comp, ih]
    congr 1
    simp only [homotopyHσToZero, Homotopy.nullHomotopy'_hom]
    split_ifs with h
    · rw [Category.assoc, ← hσ'_naturality, ← Category.assoc, ← Category.assoc]
      congr 1
      exact P_f_naturality q i f
    · simp

/-- The components of the homotopy `homotopyPInftyToId` from `PInfty` to the identity are
natural in the simplicial object. -/
theorem homotopyPInftyToId_hom_naturality {C : Type*} [Category* C] [Preadditive C]
    {X X' : SimplicialObject C} (f : X ⟶ X') (i j : ℕ) :
    f.app (op ⦋i⦌) ≫ (homotopyPInftyToId X').hom i j =
      (homotopyPInftyToId X).hom i j ≫ f.app (op ⦋j⦌) :=
  homotopyPToId_hom_naturality f (j + 1) i j

end MMP.DoldKanAux

namespace MMP

open MMP

namespace SingularCochain

open MMP.SingularCochain

open SingularChain AlgebraicTopology AlgebraicTopology.DoldKan MMP.DoldKanAux

variable {R : Type u} [CommRing R] {Y : TopCat.{u}}

/-- A cochain is normalized if it vanishes on the degenerate simplices `σ ∘ f` for a monotone
non-injective vertex map `f`. -/
def IsNormalized {n : ℕ} (φ : Simplex Y n → R) : Prop :=
  ∀ (m : ℕ) (σ : Simplex Y m) (f : Fin (n + 1) → Fin (m + 1)), Monotone f →
    ¬ Function.Injective f → φ (σ.comp (smap f)) = 0

variable (R Y) in
/-- The simplicial `R`-module of singular chains of `Y`: in degree `n`, the free `R`-module on
the singular `n`-simplices. -/
abbrev freeSingular : SimplicialObject (ModuleCat.{u} R) :=
  TopCat.toSSet.obj Y ⋙ ModuleCat.free R

/-- The linear form on singular `n`-chains given by an `n`-cochain. -/
def evalFree {n : ℕ} (φ : Simplex Y n → R) : (freeSingular R Y).obj (op ⦋n⦌) →ₗ[R] R :=
  Finsupp.linearCombination R (φ ∘ simplexEquiv Y n)

/-- The linear form of `φ` sends `a` times the basis chain `τ` to `a * φ τ`. -/
lemma evalFree_single {n : ℕ} (φ : Simplex Y n → R) (τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌))
    (a : R) : evalFree φ (Finsupp.single τ a) = a * φ (simplexEquiv Y n τ) :=
  (Finsupp.linearCombination_single R (v := φ ∘ simplexEquiv Y n) a τ).trans (smul_eq_mul _ _)

/-- The cochain `φ ∘ g` for a linear map `g` of singular chain modules. -/
def precomp {m n : ℕ}
    (g : (freeSingular R Y).obj (op ⦋m⦌) →ₗ[R] (freeSingular R Y).obj (op ⦋n⦌))
    (φ : Simplex Y n → R) : Simplex Y m → R :=
  fun σ ↦ evalFree φ (g (Finsupp.single ((simplexEquiv Y m).symm σ) 1))

/-- The linear form of `precomp g φ` is the linear form of `φ` composed with `g`. -/
lemma evalFree_precomp {m n : ℕ}
    (g : (freeSingular R Y).obj (op ⦋m⦌) →ₗ[R] (freeSingular R Y).obj (op ⦋n⦌))
    (φ : Simplex Y n → R) : evalFree (precomp g φ) = evalFree φ ∘ₗ g := by
  refine Finsupp.lhom_ext' fun τ ↦ LinearMap.ext_ring ?_
  change evalFree (precomp g φ) (Finsupp.single τ 1) = evalFree φ (g (Finsupp.single τ 1))
  rw [evalFree_single, one_mul, precomp, Equiv.symm_apply_apply]

/-- Under `simplexEquiv`, the `i`-th face of a singular simplex is its composition with the `i`-th
face map of the standard simplex. -/
lemma simplexEquiv_δ (n : ℕ) (τ : (TopCat.toSSet.obj Y).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) :
    simplexEquiv Y n ((TopCat.toSSet.obj Y).δ i τ) = (simplexEquiv Y (n + 1) τ).comp (face n i) := by
  rw [← Equiv.symm_apply_apply (simplexEquiv Y (n + 1)) τ, simplexEquiv_symm_δ,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The linear form of `φ` takes the value `φ τ` on the basis chain `τ`. -/
lemma evalFree_freeMk {n : ℕ} (φ : Simplex Y n → R) (τ : (TopCat.toSSet.obj Y).obj (op ⦋n⦌)) :
    evalFree φ (ModuleCat.freeMk τ) = φ (simplexEquiv Y n τ) :=
  (evalFree_single φ τ 1).trans (one_mul _)

/-- Two linear forms on singular `n`-chains are equal if they agree on every singular
`n`-simplex. -/
lemma evalFree_ext {n : ℕ} {f g : (freeSingular R Y).obj (op ⦋n⦌) →ₗ[R] R}
    (h : ∀ τ, f (ModuleCat.freeMk τ) = g (ModuleCat.freeMk τ)) : f = g :=
  Finsupp.lhom_ext' fun τ ↦ LinearMap.ext_ring (h τ)

/-- The linear form of the coboundary of `φ` is the linear form of `φ` composed with the
differential of the alternating face map complex of singular chains. -/
lemma evalFree_coboundary (n : ℕ) (φ : Simplex Y n → R) :
    evalFree (coboundary R n φ) =
      evalFree φ ∘ₗ ((AlternatingFaceMapComplex.obj (freeSingular R Y)).d (n + 1) n).hom := by
  refine evalFree_ext fun τ ↦ ?_
  rw [LinearMap.comp_apply, AlternatingFaceMapComplex.obj_d_eq, ModuleCat.hom_sum,
    LinearMap.sum_apply, map_sum, evalFree_freeMk, coboundary_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, map_zsmul]
  erw [ModuleCat.free_map_apply]
  rw [evalFree_freeMk, zsmul_eq_mul]
  push_cast
  exact congrArg _ (congrArg φ (simplexEquiv_δ n τ i).symm)

variable (R) in
/-- The map of simplicial modules of singular chains induced by the inclusion of a subset. -/
abbrev inclusionFree (A : Set Y) : freeSingular R (TopCat.of A) ⟶ freeSingular R Y :=
  Functor.whiskerRight (TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩))
    (ModuleCat.free R)

/-- The linear form of a cochain vanishing on the simplices of `A` vanishes on the chains of
`A`. -/
lemma evalFree_comp_inclusionFree {n : ℕ} {A : Set Y} {φ : Simplex Y n → R}
    (hφ : φ ∈ vanishing R n A) :
    evalFree φ ∘ₗ ((inclusionFree R A).app (op ⦋n⦌)).hom = 0 := by
  refine evalFree_ext fun τ ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  erw [ModuleCat.free_map_apply]
  rw [evalFree_freeMk]
  refine hφ _ ?_
  rintro _ ⟨t, rfl⟩
  exact (simplexEquiv (TopCat.of A) n τ t).2

/-- A cochain vanishing on the simplices of `A` stays so under precomposition with a map of
singular chain modules that commutes with the inclusion of the chains of `A`. -/
lemma precomp_mem_vanishing {m n : ℕ} {A : Set Y}
    (gA : (freeSingular R (TopCat.of A)).obj (op ⦋m⦌) ⟶ (freeSingular R (TopCat.of A)).obj (op ⦋n⦌))
    (g : (freeSingular R Y).obj (op ⦋m⦌) ⟶ (freeSingular R Y).obj (op ⦋n⦌))
    (hg : (inclusionFree R A).app (op ⦋m⦌) ≫ g = gA ≫ (inclusionFree R A).app (op ⦋n⦌))
    {φ : Simplex Y n → R} (hφ : φ ∈ vanishing R n A) : precomp g.hom φ ∈ vanishing R m A := by
  intro σ hσ
  let σ' : Simplex (TopCat.of A) m := ⟨fun t ↦ ⟨σ t, hσ ⟨t, rfl⟩⟩, σ.continuous.subtype_mk _⟩
  have h1 : Finsupp.single ((simplexEquiv Y m).symm σ) 1 = ((inclusionFree R A).app (op ⦋m⦌)).hom
      (ModuleCat.freeMk ((simplexEquiv (TopCat.of A) m).symm σ')) := by
    erw [ModuleCat.free_map_apply]
    rfl
  change evalFree φ (g.hom (Finsupp.single ((simplexEquiv Y m).symm σ) 1)) = 0
  rw [h1]
  have := congrArg (fun k ↦ evalFree φ
    (k.hom (ModuleCat.freeMk ((simplexEquiv (TopCat.of A) m).symm σ')))) hg
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  rw [this]
  exact LinearMap.congr_fun (evalFree_comp_inclusionFree hφ) _

/-- The cochain `φ ∘ PInfty` vanishes on the degenerate simplices. -/
lemma isNormalized_precomp_PInfty {n : ℕ} (φ : Simplex Y n → R) :
    IsNormalized (precomp ((PInfty (X := freeSingular R Y)).f n).hom φ) := by
  intro m σ f hf hinj
  cases n with
  | zero => exact absurd (fun a b _ ↦ Fin.ext (by have := a.isLt; have := b.isLt; omega)) hinj
  | succ k =>
    let θ : ⦋k + 1⦌ ⟶ ⦋m⦌ := SimplexCategory.mkHom ⟨f, hf⟩
    obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_σ_comp_of_not_injective θ hinj
    have h1 : Finsupp.single ((simplexEquiv Y (k + 1)).symm (σ.comp (smap f))) (1 : R) =
        ((freeSingular R Y).map θ.op).hom (ModuleCat.freeMk ((simplexEquiv Y m).symm σ)) := by
      erw [ModuleCat.free_map_apply]
      change Finsupp.single _ 1 = Finsupp.single _ 1
      congr 1
      change (Y.toSSetObjEquiv _).symm ((σ.comp (smap f)).comp ⟨(SingularChain.stdSimplexHomeo _).symm, (SingularChain.stdSimplexHomeo _).symm.continuous⟩) =
        (TopCat.toSSet.obj Y).map θ.op ((Y.toSSetObjEquiv _).symm (σ.comp ⟨(SingularChain.stdSimplexHomeo _).symm, (SingularChain.stdSimplexHomeo _).symm.continuous⟩))
      rw [TopCat.toSSetObjEquiv_symm_naturality]
      congr 1
      ext s
      exact congrArg σ (SingularChain.stdSimplexHomeo_symm_map _ s).symm
    change evalFree φ (((PInfty (X := freeSingular R Y)).f (k + 1)).hom
      (Finsupp.single ((simplexEquiv Y (k + 1)).symm (σ.comp (smap f))) 1)) = 0
    have key : (freeSingular R Y).map θ.op ≫ (PInfty (X := freeSingular R Y)).f (k + 1) = 0 := by
      rw [hθ, op_comp, Functor.map_comp, Category.assoc]
      erw [σ_comp_PInfty]
      rw [Limits.comp_zero]
    have := congrArg (fun g ↦ evalFree φ (g.hom (ModuleCat.freeMk ((simplexEquiv Y m).symm σ)))) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
      map_zero] at this
    rw [h1, this]

/-- The linear form of the zero cochain is zero. -/
lemma evalFree_zero (n : ℕ) : evalFree (0 : Simplex Y n → R) = 0 :=
  evalFree_ext fun τ ↦ by rw [evalFree_freeMk]; rfl

/-- Every relative singular cocycle is cohomologous to a normalized one: it differs from a
normalized relative cocycle by a relative coboundary. -/
theorem exists_isNormalized_sub_mem_relCoboundaries (A : Set Y) (n : ℕ) (φ : Simplex Y n → R)
    (hφ : φ ∈ relCocycles R A n) :
    ∃ ψ ∈ relCocycles R A n, IsNormalized ψ ∧ φ - ψ ∈ relCoboundaries R A n := by
  have hψA : precomp ((PInfty (X := freeSingular R Y)).f n).hom φ ∈ vanishing R n A :=
    precomp_mem_vanishing ((PInfty (X := freeSingular R (TopCat.of A))).f n) _
      (PInfty_f_naturality n (inclusionFree R A)) hφ.1
  have hδφ : coboundary R n φ = 0 := hφ.2
  cases n with
  | zero =>
    have hψ : precomp ((PInfty (X := freeSingular R Y)).f 0).hom φ = φ := by
      funext σ
      change evalFree φ (ModuleCat.freeMk ((simplexEquiv Y 0).symm σ)) = φ σ
      rw [evalFree_freeMk, Equiv.apply_symm_apply]
    refine ⟨_, ⟨hψA, ?_⟩, isNormalized_precomp_PInfty φ, ?_⟩
    · rw [hψ]; exact hδφ
    · rw [hψ, sub_self]; exact Submodule.zero_mem _
  | succ k =>
    let H := (homotopyPInftyToId (freeSingular R Y)).hom k (k + 1)
    let H' := (homotopyPInftyToId (freeSingular R Y)).hom (k + 1) (k + 2)
    let ψ := precomp ((PInfty (X := freeSingular R Y)).f (k + 1)).hom φ
    let χ := precomp H.hom φ
    have hχ : χ ∈ vanishing R k A :=
      precomp_mem_vanishing ((homotopyPInftyToId (freeSingular R (TopCat.of A))).hom k (k + 1)) H
        (homotopyPInftyToId_hom_naturality _ _ _) hφ.1
    have hcomm := (homotopyPInftyToId (freeSingular R Y)).comm (k + 1)
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hcomm
    have hdiff : coboundary R k (-χ) = φ - ψ := by
      funext σ
      set x : (freeSingular R Y).obj (op ⦋k + 1⦌) :=
        ModuleCat.freeMk ((simplexEquiv Y (k + 1)).symm σ)
      have e1 : ∀ c : Simplex Y (k + 1) → R, c σ = evalFree c x := fun c ↦ by
        rw [evalFree_freeMk, Equiv.apply_symm_apply]
      have hψx : ψ σ = evalFree φ (((PInfty (X := freeSingular R Y)).f (k + 1)).hom x) := rfl
      have h := congrArg (fun g ↦ evalFree φ (g.hom x)) hcomm
      simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
        map_add, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply] at h
      have h0 : evalFree φ (((AlternatingFaceMapComplex.obj (freeSingular R Y)).d (k + 2)
          (k + 1)).hom (H'.hom x)) = 0 := by
        rw [← LinearMap.comp_apply, ← evalFree_coboundary, hδφ, evalFree_zero,
          LinearMap.zero_apply]
      rw [map_neg, Pi.neg_apply, Pi.sub_apply, hψx, h, e1 φ, e1 (coboundary R k χ),
        evalFree_coboundary, LinearMap.comp_apply, evalFree_precomp, LinearMap.comp_apply]
      rw [h0]
      ring
    refine ⟨ψ, ⟨hψA, ?_⟩, isNormalized_precomp_PInfty φ, -χ, Submodule.neg_mem _ hχ, hdiff⟩
    change coboundary R (k + 1) ψ = 0
    rw [show ψ = φ - coboundary R k (-χ) by rw [hdiff, sub_sub_cancel], map_sub, hδφ,
      coboundary_coboundary, sub_zero]

end SingularCochain

end MMP
