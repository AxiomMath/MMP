module

public import MMP.AlgebraicGeometry.Cohomology.Cech.CupProduct
public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingMap

/-!
# Čech gluing data as Čech cocycles, and morphisms into the Čech double complex from sections

Let `V` be a scheme, `𝒰 = (U α)` an open cover of `V`, `K` a cochain complex of `𝒪_V`-modules
and `M` an `𝒪_V`-module. Local maps `f α : M|_{U α} → K^{n+1}|_{U α}` glued by homotopies `h α β`
satisfying the cocycle condition (`MMP.DeRham.CechGluingData`) are a cocycle of total degree
`n + 1` of the Čech double complex `Č(𝒰, K)` with only two nonzero components: `f` in bidegree
`(n + 1, 0)` and `(-1)^n h` in bidegree `(n, 1)`. This is a Čech cocycle of the general form
`MMP.DeRham.CechCocycleData`, and the two constructions of the morphism `M[-(n+1)] ⟶ K` in the
derived category agree.

A morphism from `M` into the Čech term `Č^m(𝒰, K^p) = ∏ₓ (j_{x₀⋯x_m})_* (j_{x₀⋯x_m})^* K^p` is
given, for every tuple `x` of `m + 1` indices, by additive maps `Γ(M, W) → Γ(K^p, W)` on the opens
`W ⊆ U_{x₀} ∩ ⋯ ∩ U_{x_m}`, linear and compatible with restriction.

## Main definitions

* `MMP.DeRham.CechGluingData.toCechCocycleData`: gluing data as a Čech cocycle of total degree
  `n + 1`.
* `MMP.DeRham.toCechBiOfSections`: the morphism `M ⟶ Č^m(𝒰, K^p)` given by maps on the
  sections over the opens inside the `(m + 1)`-fold intersections.

## Main results

* `MMP.DeRham.CechGluingData.toCechCocycleData_cechMap`,
  `MMP.DeRham.CechGluingData.toCechCocycleData_homologyMap`,
  `MMP.DeRham.CechGluingData.toCechCocycleData_derivedMap`: the morphisms of complexes, on
  cohomology sheaves and in the derived category defined by the cocycle are those defined by the
  gluing data.
* `MMP.DeRham.CechGluingData.toCechCocycleData_g_zero_app_down`: the component of bidegree
  `(n + 1, 0)` of the cocycle at an index `α` is the local map `f α`.
* `MMP.DeRham.secCochain_toCechBiOfSections_app`: the Čech cochain of sections of the morphism
  built from sections.

## Implementation notes

The components of a `MMP.DeRham.CechCocycleData` are indexed by a bidegree `(p, m)` and an
equation `p + m = n + 1`; `MMP.DeRham.CechGluingData.cocycleComponent` transports `f` and `h`
to the bidegree `p` named by the equation along the canonical isomorphisms `XIsoOfEq` of the
double complex, which are identities for the bidegrees `(n + 1, 0)` and `(n, 1)` themselves.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], §2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.CechSiteChange
open Stacks.CategoryTheory.CechComplex (inter interπ interMap)
open ComplexShape

universe u

namespace MMP.DeRham

variable {V : Scheme.{u}} {ι : Type u} {U : ι → V.Opens}

/-! ### Morphisms into the Čech double complex from sections -/

section Sections

variable (K : CochainComplex V.Modules ℤ) (p : ℤ) (m : ℕ) {M : V.Modules}
  (φ : ∀ (x : Fin (m + 1) → ι) (W : V.Opens), W ≤ inter U x → Γ(M, W) →+ Γ(K.X p, W))
  (hsmul : ∀ (x : Fin (m + 1) → ι) (W : V.Opens) (hW : W ≤ inter U x) (r : Γ(V, W))
    (s : Γ(M, W)), φ x W hW (r • s) = r • φ x W hW s)
  (hnat : ∀ (x : Fin (m + 1) → ι) (W₁ W₂ : V.Opens) (h₁ : W₁ ≤ inter U x)
    (h₂ : W₂ ≤ inter U x) (h : W₁ ≤ W₂) (s : Γ(M, W₂)),
    φ x W₁ h₁ (M.presheaf.map (homOfLE h).op s) =
      (K.X p).presheaf.map (homOfLE h).op (φ x W₂ h₂ s))

variable (U) in
/-- **A morphism into the term of bidegree `(p, m)` of the Čech double complex, from sections.**
For every tuple `x` of `m + 1` indices, additive maps `φ x W : Γ(M, W) → Γ(K^p, W)` on the opens
`W ⊆ inter U x`, linear and compatible with restriction, give the morphism
`M ⟶ ∏ₓ (j_{inter U x})_* (j_{inter U x})^* K^p` whose component at `x` sends a section `s` over
`W` to `φ x (W ⊓ inter U x) (s|_{W ⊓ inter U x})`. -/
def toCechBiOfSections : M ⟶ ((cechBicomplex U K).X p).X m :=
  toCechBi U K p m fun x ↦ cechDiagramOpensLift (inter U x) (φ x) (hsmul x) (hnat x)

/-- The component at a tuple `x` of the morphism built from sections sends a section `s` over `W`
to `φ x` applied to the restriction of `s` to `W ⊓ inter U x`. -/
theorem cechBiπ_app_toCechBiOfSections_app_down (x : Fin (m + 1) → ι) (W : V.Opens)
    (s : Γ(M, W)) :
    ((cechBiπ K p m x).app W ((toCechBiOfSections U K p m φ hsmul hnat).app W s)).down =
      φ x (W ⊓ inter U x) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s) := by
  have h := congrArg (fun ψ ↦ (ψ.app W s).down)
    (toCechBi_cechBiπ K p m (fun x ↦ cechDiagramOpensLift (inter U x) (φ x) (hsmul x) (hnat x)) x)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h

/-- **The Čech cochain of sections of a morphism built from sections**: its component at a tuple
`x` is `φ x` applied to the restriction to `W ⊓ inter U x`. -/
theorem secCochain_toCechBiOfSections_app (W : V.Opens) (s : Γ(M, W)) :
    secCochain ((toCechBiOfSections U K p m φ hsmul hnat).app W s) =
      fun x ↦ φ x (W ⊓ inter U x) inf_le_right (M.presheaf.map (homOfLE inf_le_left).op s) :=
  funext fun x ↦ cechBiπ_app_toCechBiOfSections_app_down K p m φ hsmul hnat x W s

end Sections

section SecCochain

variable {K : CochainComplex V.Modules ℤ} {M : V.Modules}

/-- The Čech cochain of sections of `φ` followed by the horizontal differential of the double
complex is the horizontal differential of the Čech cochain of sections of `φ`. -/
theorem secCochain_comp_d_f_app {p : ℤ} {m : ℕ} (φ : M ⟶ ((cechBicomplex U K).X p).X m)
    (p' : ℤ) (W : V.Opens) (s : Γ(M, W)) :
    secCochain ((φ ≫ ((cechBicomplex U K).d p p').f m).app W s) =
      CechCochain.horiz p p' (secCochain (φ.app W s)) :=
  secCochain_horiz p p' (φ.app W s)

/-- The Čech cochain of sections of `φ` followed by the Čech differential is the Čech
coboundary of the Čech cochain of sections of `φ`. -/
theorem secCochain_comp_X_d_app {p : ℤ} {m : ℕ} (φ : M ⟶ ((cechBicomplex U K).X p).X m)
    (W : V.Opens) (s : Γ(M, W)) :
    secCochain ((φ ≫ ((cechBicomplex U K).X p).d m ((m + 1 : ℕ) : ℤ)).app W s) =
      (secCochain (φ.app W s)).delta :=
  secCochain_vert p m (φ.app W s)

/-- The Čech cochain of sections of the zero morphism is zero. -/
theorem secCochain_zero_app {p : ℤ} {m : ℕ} (W : V.Opens) (s : Γ(M, W)) :
    secCochain ((0 : M ⟶ ((cechBicomplex U K).X p).X m).app W s) = 0 := by
  rw [Scheme.Modules.Hom.zero_app]
  exact secCochain_zero

end SecCochain

/-! ### Gluing data as Čech cocycles -/

namespace CechGluingData

variable {K : CochainComplex V.Modules ℤ} {M : V.Modules} {n : ℤ} (D : CechGluingData U K M n)

/-- The components of the Čech cocycle of gluing data: the local maps in bidegree `(n + 1, 0)`,
`(-1)^n` times the homotopies in bidegree `(n, 1)`, and `0` in the other bidegrees. -/
def cocycleComponent (p : ℤ) : (m : ℕ) → p + m = n + 1 → (M ⟶ ((cechBicomplex U K).X p).X m)
  | 0, h => D.cechF ≫
      ((cechBicomplex U K).XIsoOfEq (show n + 1 = p by push_cast at h; omega)).hom.f
        ((0 : ℕ) : ℤ)
  | 1, h => (n.negOnePow : ℤ) • (D.cechH ≫
      ((cechBicomplex U K).XIsoOfEq (show n = p by push_cast at h; omega)).hom.f ((1 : ℕ) : ℤ))
  | _ + 2, _ => 0

/-- The component of bidegree `(n + 1, 0)` of the cocycle is the local map `D.cechF`. -/
theorem cocycleComponent_zero (h : n + 1 + ((0 : ℕ) : ℤ) = n + 1) :
    D.cocycleComponent (n + 1) 0 h = D.cechF := by
  simp [cocycleComponent]

/-- The component of bidegree `(n, 1)` of the cocycle is `(-1)^n • D.cechH`. -/
theorem cocycleComponent_one (h : n + ((1 : ℕ) : ℤ) = n + 1) :
    D.cocycleComponent n 1 h = (n.negOnePow : ℤ) • D.cechH := by
  simp [cocycleComponent]

/-- The components of the cocycle in Čech degree at least `2` vanish. -/
theorem cocycleComponent_add_two (p : ℤ) (m : ℕ) (h : p + ((m + 2 : ℕ) : ℤ) = n + 1) :
    D.cocycleComponent p (m + 2) h = 0 := rfl

/-- The Čech cochain of sections of the component of bidegree `(n, 1)` of the cocycle is
`(-1)^n` times the Čech cochain of sections of `D.cechH`. -/
theorem secCochain_cocycleComponent_one_app (h : n + ((1 : ℕ) : ℤ) = n + 1) (W : V.Opens)
    (s : Γ(M, W)) : secCochain ((D.cocycleComponent n 1 h).app W s) =
      (n.negOnePow : ℤ) • secCochain (D.cechH.app W s) := by
  rw [cocycleComponent_one, zsmul_app_apply, secCochain_zsmul]

/-- On the sections over every open `W`, the components of gluing data form a cocycle of the
total Čech complex. -/
theorem isCocycle_cocycleComponent (W : V.Opens) (s : Γ(M, W)) :
    CechTotalCochain.IsCocycle
      (fun p m h ↦ secCochain ((D.cocycleComponent p m h).app W s)) := by
  set c : CechTotalCochain U K W (n + 1) :=
    fun p m h ↦ secCochain ((D.cocycleComponent p m h).app W s)
  intro p m h
  match m, h with
  | 0, h =>
    obtain rfl : p = n + 2 := by push_cast at h; omega
    rw [CechTotalCochain.d_apply, CechTotalCochain.vert_zero, smul_zero, add_zero,
      CechTotalCochain.horiz_congr c (n + 2) 0 (show n + 2 - 1 = n + 1 by ring) _ (by simp)]
    change CechCochain.horiz (n + 1) (n + 2)
      (secCochain ((D.cocycleComponent (n + 1) 0 (by simp)).app W s)) = 0
    rw [cocycleComponent_zero, ← secCochain_comp_d_f_app, D.cechF_d,
      secCochain_zero_app]
  | 1, h =>
    obtain rfl : p = n + 1 := by push_cast at h; omega
    rw [CechTotalCochain.d_apply,
      CechTotalCochain.horiz_congr c (n + 1) 1 (show n + 1 - 1 = n by ring) _ (by simp)]
    change CechCochain.horiz n (n + 1)
      (secCochain ((D.cocycleComponent n 1 (by simp)).app W s)) +
      (((n + 1).negOnePow : ℤˣ) : ℤ) •
        (secCochain ((D.cocycleComponent (n + 1) 0 (by simp)).app W s)).delta = 0
    rw [cocycleComponent_one, cocycleComponent_zero, zsmul_app_apply, secCochain_zsmul,
      CechCochain.horiz_zsmul, ← secCochain_comp_d_f_app, D.cechH_d_f,
      ← secCochain_comp_X_d_app]
    change _ • secCochain ((D.cechF ≫ ((cechBicomplex U K).X (n + 1)).d ((0 : ℕ) : ℤ)
      ((1 : ℕ) : ℤ)).app W s) + _ = 0
    rw [Int.negOnePow_succ, Units.val_neg, neg_smul, add_neg_cancel]
  | 2, h =>
    have hp : p = n := by push_cast at h; omega
    subst p
    rw [CechTotalCochain.d_apply]
    change CechCochain.horiz (n - 1) n
      (secCochain ((D.cocycleComponent (n - 1) (0 + 2) _).app W s)) +
      ((n.negOnePow : ℤˣ) : ℤ) •
        (secCochain ((D.cocycleComponent n 1 (by simp)).app W s)).delta = 0
    rw [cocycleComponent_add_two, secCochain_zero_app, CechCochain.horiz_zero]
    refine (zero_add _).trans ?_
    rw [secCochain_cocycleComponent_one_app,
      CechCochain.delta_zsmul, ← secCochain_comp_X_d_app]
    change _ • _ • secCochain ((D.cechH ≫ ((cechBicomplex U K).X n).d ((1 : ℕ) : ℤ)
      ((1 + 1 : ℕ) : ℤ)).app W s) = 0
    rw [D.cechH_d, secCochain_zero_app, smul_zero, smul_zero]
  | m + 3, h =>
    rw [CechTotalCochain.d_apply]
    change CechCochain.horiz (p - 1) p
      (secCochain ((D.cocycleComponent (p - 1) ((m + 1) + 2) _).app W s)) +
      ((p.negOnePow : ℤˣ) : ℤ) •
        (secCochain ((D.cocycleComponent p (m + 2) _).app W s)).delta = 0
    rw [cocycleComponent_add_two, cocycleComponent_add_two, secCochain_zero_app,
      secCochain_zero_app, CechCochain.horiz_zero, CechCochain.delta_zero, smul_zero, add_zero]

/-- **Gluing data as a Čech cocycle**: the local maps `f` in bidegree `(n + 1, 0)` and `(-1)^n h`
in bidegree `(n, 1)` form a cocycle of total degree `n + 1` of the Čech double complex. -/
def toCechCocycleData : CechCocycleData U K M (n + 1) where
  g := D.cocycleComponent
  isCocycle := D.isCocycle_cocycleComponent

/-- The components of the Čech cocycle of gluing data are
`MMP.DeRham.CechGluingData.cocycleComponent`. -/
theorem toCechCocycleData_g : D.toCechCocycleData.g = D.cocycleComponent := rfl

/-- The component of bidegree `(n + 1, 0)` of the cocycle at a single index `α` is the local map
`f α`, restricted to `W ⊓ inter U (fun _ ↦ α)`. -/
theorem toCechCocycleData_g_zero_app_down (α : ι) (W : V.Opens) (s : Γ(M, W))
    (h : n + 1 + ((0 : ℕ) : ℤ) = n + 1) :
    ((cechBiπ K (n + 1) 0 (fun _ ↦ α)).app W ((D.toCechCocycleData.g (n + 1) 0 h).app W s)).down =
      (K.X (n + 1)).presheaf.map (homOfLE (inf_le_inf_left W (leOfHom (interπ U (fun _ ↦ α) 0)) :
        W ⊓ inter U (fun _ : Fin 1 ↦ α) ≤ W ⊓ U α)).op ((D.f α).app W s).down := by
  rw [toCechCocycleData_g, cocycleComponent_zero]
  have e := congrArg (fun ψ ↦ (ψ.app W s).down) (toCechBi_cechBiπ K (n + 1) 0 (fun x ↦
    D.f (x 0) ≫ ((cechDiagramOpens V).obj (K.X (n + 1))).map (interπ U x 0).op) (fun _ ↦ α))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
  exact e

/-- The morphism `M ⟶ Tot^{n+1} Č(𝒰, K)` of the cocycle is the one of the gluing data. -/
theorem toCechCocycleData_cocycle (a : ℤ) [K.IsStrictlyGE a] :
    D.toCechCocycleData.cocycle a = D.cechCocycle := by
  have hι : ∀ (m : ℕ) (p p' : ℤ) (e : p = p') (h : p + m = n + 1) (h' : p' + m = n + 1) (hι hι'),
      D.cocycleComponent p m h ≫ (cechBicomplex U K).ιTotal (up ℤ) p m (n + 1) hι =
        D.cocycleComponent p' m h' ≫ (cechBicomplex U K).ιTotal (up ℤ) p' m (n + 1) hι' := by
    intro m p p' e h h' hι hι'
    subst e
    rfl
  unfold CechCocycleData.cocycle
  rw [toCechCocycleData_g, Finset.sum_range_succ',
    hι 0 _ (n + 1) (by simp) _ (by simp) _ (by simp), cocycleComponent_zero, cechCocycle]
  refine (add_comm _ _).trans (congrArg (_ + ·) ?_)
  rcases hL : (n + 1 - a).toNat with _ | L
  · have hn : n < a := by omega
    rw [Finset.sum_range_zero]
    have hz : IsZero (((cechBicomplex U K).X n).X ((1 : ℕ) : ℤ)) :=
      isZero_cechBicomplex_X_X (a := a) hn _
    rw [hz.eq_of_tgt D.cechH 0, zero_comp, smul_zero]
  · rw [Finset.sum_range_succ', hι 1 _ n (by push_cast; ring) _ (by simp) _ (by simp),
      cocycleComponent_one, Preadditive.zsmul_comp]
    refine (add_eq_right.2 (Finset.sum_eq_zero fun m _ ↦ ?_))
    exact (congrArg (· ≫ _) (D.cocycleComponent_add_two _ m _)).trans zero_comp

/-- **The morphism of complexes `M[-(n+1)] ⟶ Tot Č(𝒰, K)` of the cocycle is the one of the
gluing data.** -/
theorem toCechCocycleData_cechMap (a : ℤ) [K.IsStrictlyGE a] :
    D.toCechCocycleData.cechMap a = D.cechMap :=
  HomologicalComplex.from_single_hom_ext (by
    rw [CechCocycleData.cechMap_f, cechMap_f, toCechCocycleData_cocycle])

/-- **The cohomology map of the cocycle is the one of the gluing data.** -/
theorem toCechCocycleData_homologyMap (hU : ⨆ i, U i = ⊤) (a : ℤ) [K.IsStrictlyGE a] :
    D.toCechCocycleData.homologyMap hU a = D.homologyMap hU a := by
  unfold CechCocycleData.homologyMap homologyMap
  rw [toCechCocycleData_cechMap]

/-- **The morphism `M[-(n+1)] ⟶ K` in the derived category of the cocycle is the one of the
gluing data.** -/
theorem toCechCocycleData_derivedMap [HasDerivedCategory.{u} V.Modules] (hU : ⨆ i, U i = ⊤)
    (a : ℤ) [K.IsStrictlyGE a] :
    D.toCechCocycleData.derivedMap hU a = D.derivedMap hU a := by
  unfold CechCocycleData.derivedMap derivedMap
  rw [toCechCocycleData_cechMap]

end CechGluingData

end MMP.DeRham
