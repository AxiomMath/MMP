module

public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingIso
public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingChartExists
public import MMP.AlgebraicGeometry.DeRham.FrobeniusSplittingPow

/-!
# The Čech cocycles of the Deligne–Illusie decomposition in positive degrees

Let `k` be a perfect field of characteristic `p`, `V` a smooth proper `k`-scheme of dimension
`n < p` with a simple normal crossing divisor `S` and complement `U`, lifted with `S` over
`W₂(k)`, `K^•` the logarithmic forms and `𝒦` the complex `F_*K^•` extended to `ℤ`
(`MMP.DeRham.FrobeniusSplittingData`). A local Frobenius splitting gives a Čech cocycle of total
degree `1` on `K¹` whose component of bidegree `(1, 0)` represents the inverse Cartier map. This
file builds the cocycles in every degree `q + 1 ≤ n` and proves the decomposition
`⨁_{q ≤ n} K^q[-q] ≅ 𝒦` in the derived category.

On a chart of the divisor every logarithmic `(q + 1)`-form is a sum of wedges of logarithmic
`1`-forms, by Deligne's criterion. To a family `θ₀, …, θ_q` of `1`-forms on an open inside a
Čech intersection we attach the antisymmetrised cup product
`∑_σ sgn σ · c(θ_{σ 0}) ⌣ ⋯ ⌣ c(θ_{σ q})` of their degree-`1` cocycles. It is alternating and
multilinear, so on the affine opens of `U`, where logarithmic forms are the Kähler forms, it
only depends on the wedge `θ₀ ∧ ⋯ ∧ θ_q`; the values on the affine opens of `U` determine the
sections of `𝒦`, so the local cup products glue to morphisms from `K^{q+1}` into the Čech
double complex, which form a cocycle. Its component of
bidegree `(q + 1, 0)` at a single index `α` is `(q + 1)! φ_α(θ₀) ∧ ⋯ ∧ φ_α(θ_q)`, a representative
of `(q + 1)! C⁻¹(θ₀ ∧ ⋯ ∧ θ_q)`; since `(q + 1)!` is invertible modulo `p`, a multiple of the
cocycle represents the inverse Cartier map.

## Main definitions

* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.cupAt`: the antisymmetrised cup
  product of a family of logarithmic `1`-forms, read at a tuple of indices.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.cupComponent`: the components of the
  cocycle on `K^{q+1}`.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.cupCocycle`: the Čech cocycle on
  `K^{q+1}`, scaled by an integer.

## Main results

* `MMP.DeRham.FrobeniusSplittingData.exists_list_wedgeFin_eq_of_chart`: on a chart, logarithmic
  forms are sums of wedges of logarithmic `1`-forms.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.sum_cupAt_eq`: the antisymmetrised
  cup product only depends on the wedge.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.cupCochain_zero_const`: its
  component of bidegree `(q + 1, 0)`.
* `MMP.DeRham.FrobeniusSplittingData.LocalFrobeniusSplitting.isCartierCocycle_cupCocycle`: the
  scaled cocycle represents the inverse Cartier map.
* `MMP.DeRham.FrobeniusSplittingData.nonempty_iso_directSum_singleFunctor`: **the Deligne–Illusie
  decomposition** `⨁_{q ≤ n} K^q[-q] ≅ F_*K^•`.

## Implementation notes

Logarithmic forms are written as sums of wedges through lists of families of `1`-forms. On a
chart, Deligne's criterion is read on the affine open `W ∩ U` through a restriction map, so that
all forms live over one affine open.

## References

* [P. Deligne, L. Illusie, *Relèvements modulo p² et décomposition du complexe de de Rham*,
  Invent. Math. 89 (1987)][DeligneIllusie1987], Thm 2.1, §4.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius
open KaehlerDifferential
open scoped TensorProduct
open Stacks.CategoryTheory.CechComplex (inter)
open ComplexShape

universe u v

namespace MMP.DeRham

namespace CechTotalCochain

variable {V : Scheme.{u}} {κ : Type u} {U : κ → V.Opens} {K : CochainComplex V.Modules ℤ}
  {W : V.Opens} {n : ℤ}

/-- The sum of two cocycles of the Čech total complex is a cocycle. -/
theorem IsCocycle.add {c c' : CechTotalCochain U K W n} (hc : c.IsCocycle) (hc' : c'.IsCocycle) :
    CechTotalCochain.IsCocycle (fun p m h ↦ c p m h + c' p m h) := by
  intro p m h
  have e1 := hc p m h
  have e2 := hc' p m h
  rw [d_apply] at e1 e2 ⊢
  rcases m with _ | m
  · rw [vert_zero] at e1 e2 ⊢
    rw [smul_zero, add_zero] at e1 e2 ⊢
    change CechCochain.horiz (p - 1) p (c (p - 1) 0 _ + c' (p - 1) 0 _) = 0
    rw [CechCochain.horiz_add, e1, e2, add_zero]
  · rw [vert_succ] at e1 e2 ⊢
    change CechCochain.horiz (p - 1) p (c (p - 1) (m + 1) _ + c' (p - 1) (m + 1) _) +
      ((p.negOnePow : ℤˣ) : ℤ) • (c p m _ + c' p m _).delta = 0
    rw [CechCochain.horiz_add, CechCochain.delta_add, smul_add, add_add_add_comm, e1, e2,
      add_zero]

/-- The zero cochain of the Čech total complex is a cocycle. -/
theorem isCocycle_zero :
    CechTotalCochain.IsCocycle (n := n) (fun p m _ ↦ (0 : CechCochain U K W p m)) := by
  intro p m h
  rw [d_apply]
  rcases m with _ | m
  · rw [vert_zero, smul_zero, add_zero]
    exact CechCochain.horiz_zero _ _
  · rw [vert_succ]
    rw [CechCochain.horiz_zero, CechCochain.delta_zero, smul_zero, add_zero]

/-- A list sum of cocycles is a cocycle. -/
theorem isCocycle_list_sum {α : Type*} (l : List α) {c : α → CechTotalCochain U K W n}
    (hc : ∀ a, (c a).IsCocycle) :
    CechTotalCochain.IsCocycle (fun p m h ↦ (l.map (fun a ↦ c a p m h)).sum) := by
  induction l with
  | nil => exact isCocycle_zero
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hc a).add ih

/-- An integer multiple of a cocycle of the Čech total complex is a cocycle. -/
theorem IsCocycle.zsmul {c : CechTotalCochain U K W n} (hc : c.IsCocycle) (k : ℤ) :
    CechTotalCochain.IsCocycle (fun p m h ↦ k • c p m h) := by
  have := IsCocycle.sum_zsmul ({()} : Finset Unit) (fun _ ↦ k) (c := fun _ ↦ c) (fun _ ↦ hc)
  simpa only [Finset.sum_singleton] using this

end CechTotalCochain

/-- Restriction commutes with list sums. -/
theorem presheaf_map_list_sum {V : Scheme.{u}} {M : V.Modules} {A B : V.Opens} (g : B ⟶ A)
    (l : List Γ(M, A)) : M.presheaf.map g.op l.sum = (l.map (M.presheaf.map g.op)).sum := by
  induction l with
  | nil => exact map_zero _
  | cons a l ih => rw [List.sum_cons, map_add, ih, List.map_cons, List.sum_cons]

/-- In a module over a ring of characteristic `p`, an integer congruent to `1` modulo `p` acts
trivially. -/
theorem natCast_zsmul_eq_self {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : ℕ}
    (hp : (p : R) = 0) {N : ℕ} (hN : N % p = 1) (z : M) : (N : ℤ) • z = z := by
  have hpz : p • z = 0 := by rw [← Nat.cast_smul_eq_nsmul R, hp, zero_smul]
  rw [natCast_zsmul, ← Nat.div_add_mod N p, hN, add_smul, one_smul, mul_comm, mul_smul, hpz,
    smul_zero, zero_add]

namespace FrobeniusSplittingData

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectField k] {n : ℕ}
  {V : Scheme.{u}} {f : V ⟶ Spec (.of k)} [IsProper f] [SmoothOfRelativeDimension n f]
  {ι : Type v} [Fintype ι] [HasDerivedCategory.{u} V.Modules]
  (D : FrobeniusSplittingData p k n f ι)

/-- **Decomposition along a spanning set**: if an injective additive map `E`, compatible with
scalars, sends `s` into the span of a set `S` each of whose elements is the image of some `w m`,
and the `w m` are stable under scalars, then `s` is a sum of elements `w m`. -/
theorem exists_list_sum_eq_of_mem_span {B X Y Z M : Type*} [CommRing B] {_ : AddCommMonoid X}
    {_ : Module B X} {_ : AddCommMonoid Y} {_ : Module B Y} {_ : AddCommMonoid Z} {S : Set X}
    {P : Z → Prop} {F : Z → X} (hcrit : ∀ z, P z ↔ F z ∈ Submodule.span B S) (e : Y →+ Z)
    (he : ∀ y, P (e y)) (hinj : ∀ y y', F (e y) = F (e y') → y = y')
    (h0 : F 0 = 0) (hadd : ∀ z z', F (z + z') = F z + F z')
    (hsmul : ∀ (b : B) y, F (e (b • y)) = b • F (e y))
    (w : M → Y) (hS : ∀ x ∈ S, ∃ m, F (e (w m)) = x) (g : B → M → M)
    (hg : ∀ b m, w (g b m) = b • w m) (s : Y) : ∃ l : List M, (l.map w).sum = s := by
  let F' : Z →+ X := { toFun := F, map_zero' := h0, map_add' := hadd }
  let E' : Y →+ X := F'.comp e
  have hsmul' : ∀ (b : B) y, E' (b • y) = b • E' y := hsmul
  suffices H : ∀ x ∈ Submodule.span B S, ∃ l : List M, E' (l.map w).sum = x by
    obtain ⟨l, hl⟩ := H _ ((hcrit _).1 (he s))
    exact ⟨l, hinj _ _ hl⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ := hS x hx
    exact ⟨[m], by rw [List.map_singleton, List.sum_singleton]; exact hm⟩
  | zero => exact ⟨[], by rw [List.map_nil, List.sum_nil, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨l', hl'⟩ := hy
    exact ⟨l ++ l', by rw [List.map_append, List.sum_append, map_add, hl, hl']⟩
  | smul a x _ hx =>
    obtain ⟨l, hl⟩ := hx
    refine ⟨l.map (g a), ?_⟩
    have h1 : ((l.map (g a)).map w).sum = a • (l.map w).sum := by
      rw [List.smul_sum, List.map_map, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun m _ ↦ hg a m)
    rw [h1, ← hl]
    exact hsmul' a _

/-- On an open `W` with an affine open `P = W ∩ U` on which Deligne's criterion holds, every
wedge of logarithmic generators is the algebraic form of a wedge of logarithmic `1`-forms. -/
theorem exists_oneEquiv_eq_of_mem_logGenerators (q : ℕ) (W : V.Opens) (t : ι → Γ(V, W))
    (P : V.affineOpens) (hP : (P : V.Opens) = W ⊓ D.U)
    (crit : ∀ (i : ℕ) (ω : Γ(f.relativeDifferentialForms (i : ℤ), W ⊓ D.U)),
        ω ∈ Set.range (D.e i W) ↔
          (formsAlgEquiv f i P ((f.relativeDifferentialForms (i : ℤ)).presheaf.map
              (homOfLE hP.le).op ω)).val ∈
            (letI := MMP.Mori.sectionAlgebra f P
             letI : Algebra Γ(V, W) Γ(V, P) :=
               (V.presheaf.map (homOfLE (hP.le.trans inf_le_left)).op).hom.toAlgebra
             logForms k Γ(V, P) t i))
    (v : Fin (q + 1) → (letI := MMP.Mori.sectionAlgebra f P; Ω[Γ(V, P)⁄k]))
    (hv : ∀ m, v m ∈ (letI := MMP.Mori.sectionAlgebra f P
             letI : Algebra Γ(V, W) Γ(V, P) :=
               (V.presheaf.map (homOfLE (hP.le.trans inf_le_left)).op).hom.toAlgebra
             logGenerators k Γ(V, P) t)) :
    ∀ m, ∃ θ : Γ(D.K 1, W), exteriorPower.oneEquiv _ _ (formsAlgEquiv f 1 P
      ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hP.le).op
        (D.e 1 W θ))) = v m := by
  have h1 : ∀ m, ∃ θ : Γ(D.K 1, W), exteriorPower.oneEquiv _ _ (formsAlgEquiv f 1 P
      ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hP.le).op
        (D.e 1 W θ))) = v m := by
    intro m
    obtain ⟨ω, hω⟩ : ∃ ω : Γ(f.relativeDifferentialForms ((1 : ℕ) : ℤ), W ⊓ D.U),
        formsAlgEquiv f 1 P ((f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map
          (homOfLE hP.le).op ω) = exteriorPower.ιMulti _ 1 (fun _ ↦ v m) := by
      refine ⟨(f.relativeDifferentialForms ((1 : ℕ) : ℤ)).presheaf.map (homOfLE hP.ge).op
        ((formsAlgEquiv f 1 P).symm (exteriorPower.ιMulti _ 1 (fun _ ↦ v m))), ?_⟩
      have e1 := presheaf_map_map (F := f.relativeDifferentialForms ((1 : ℕ) : ℤ))
        (homOfLE hP.ge) (homOfLE hP.le) (𝟙 _)
        ((formsAlgEquiv f 1 P).symm (exteriorPower.ιMulti _ 1 (fun _ ↦ v m)))
      rw [e1, presheaf_map_id, LinearEquiv.apply_symm_apply]
    obtain ⟨θ, hθ⟩ := (crit 1 ω).2 (by
        let := MMP.Mori.sectionAlgebra f P
        let : Algebra Γ(V, W) Γ(V, P) :=
          (V.presheaf.map (homOfLE (hP.le.trans inf_le_left)).op).hom.toAlgebra
        rw [hω, exteriorPower.ιMulti_apply_coe]
        exact Submodule.subset_span ⟨fun _ ↦ v m, fun _ ↦ hv m, rfl⟩)
    refine ⟨θ, ?_⟩
    rw [hθ, hω, exteriorPower.oneEquiv_ιMulti]
  exact h1

/-- **Logarithmic forms are sums of wedges of logarithmic `1`-forms**, on an open `W` with an
affine open `P = W ∩ U` on which Deligne's criterion describes the logarithmic forms. -/
theorem exists_list_wedgeFin_eq_of_criterion (q : ℕ) (W : V.Opens) (t : ι → Γ(V, W))
    (P : V.affineOpens) (hP : (P : V.Opens) = W ⊓ D.U)
    (crit : ∀ (i : ℕ) (ω : Γ(f.relativeDifferentialForms (i : ℤ), W ⊓ D.U)),
        ω ∈ Set.range (D.e i W) ↔
          (formsAlgEquiv f i P ((f.relativeDifferentialForms (i : ℤ)).presheaf.map
              (homOfLE hP.le).op ω)).val ∈
            (letI := MMP.Mori.sectionAlgebra f P
             letI : Algebra Γ(V, W) Γ(V, P) :=
               (V.presheaf.map (homOfLE (hP.le.trans inf_le_left)).op).hom.toAlgebra
             logForms k Γ(V, P) t i))
    (s : Γ(D.K (q + 1), W)) :
    ∃ l : List (Fin (q + 1) → Γ(D.K 1, W)), (l.map (D.wedgeFin q)).sum = s := by
  have hρ : ∀ (i : ℤ) (ω ω' : Γ(f.relativeDifferentialForms i, W ⊓ D.U)),
      (f.relativeDifferentialForms i).presheaf.map (homOfLE hP.le).op ω =
        (f.relativeDifferentialForms i).presheaf.map (homOfLE hP.le).op ω' → ω = ω' := by
    intro i ω ω' h
    have h' := congrArg ((f.relativeDifferentialForms i).presheaf.map (homOfLE hP.ge).op) h
    rwa [presheaf_map_map _ _ (𝟙 _), presheaf_map_map _ _ (𝟙 _), presheaf_map_id,
      presheaf_map_id] at h'
  have crit' := crit (q + 1)
  unfold logForms at crit'
  refine exists_list_sum_eq_of_mem_span (B := Γ(V, W)) crit' (D.e (q + 1) W) (fun y ↦ ⟨y, rfl⟩)
    ?_ ?_ ?_ ?_ (D.wedgeFin q) ?_
    (fun a θ ↦ Function.update θ 0 (a • θ 0)) (fun a θ ↦ D.wedgeFin_update_zero_smul a q θ) s
  · intro y y' h
    have h1 := Subtype.val_injective h
    have h2 := (formsAlgEquiv f (q + 1) P).injective h1
    have h3 := hρ _ _ _ h2
    exact D.he_inj _ _ h3
  · rw [map_zero, map_zero]
    rfl
  · intro z z'
    rw [map_add, map_add]
    rfl
  · intro b y
    let := MMP.Mori.sectionAlgebra f P
    let : Algebra Γ(V, W) Γ(V, P) :=
      (V.presheaf.map (homOfLE (hP.le.trans inf_le_left)).op).hom.toAlgebra
    rw [D.he_smul, Scheme.Modules.map_smul, map_smul, Submodule.coe_smul,
      ring_presheaf_map_map _ _ (homOfLE (hP.le.trans inf_le_left))]
    rw [show (V.presheaf.map (homOfLE (hP.le.trans inf_le_left)).op).hom b =
      algebraMap Γ(V, W) Γ(V, P) b from rfl, algebraMap_smul]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    choose θ hθ using D.exists_oneEquiv_eq_of_mem_logGenerators q W t P hP crit v hv
    refine ⟨θ, ?_⟩
    have h2 := D.formsAlgEquiv_map_e_wedgeFin (O := W) P hP.le q θ
    rw [h2, exteriorPower.ιMulti_apply_coe]
    exact congrArg _ (funext hθ)

/-- **Logarithmic forms on a chart are sums of wedges of logarithmic `1`-forms.** -/
theorem exists_list_wedgeFin_eq_of_chart (q : ℕ) (W : V.affineOpens) (t : ι → Γ(V, W))
    (hJ : ∀ j, (D.J j).ideal W = Ideal.span {t j})
    (hWU : (W : V.Opens) ⊓ D.U = V.basicOpen (∏ j, t j))
    (hS : letI := MMP.Mori.sectionAlgebra f W
      ∀ 𝔭 : PrimeSpectrum Γ(V, W),
        LinearIndependent 𝔭.asIdeal.ResidueField
          (fun j : {j : ι // t j ∈ 𝔭.asIdeal} ↦
            ((1 : 𝔭.asIdeal.ResidueField) ⊗ₜ[Γ(V, W)] KaehlerDifferential.D k Γ(V, W) (t j) :
              𝔭.asIdeal.ResidueField ⊗[Γ(V, W)] Ω[Γ(V, W)⁄k])))
    (s : Γ(D.K (q + 1), W)) :
    ∃ l : List (Fin (q + 1) → Γ(D.K 1, W)), (l.map (D.wedgeFin q)).sum = s := by
  refine D.exists_list_wedgeFin_eq_of_criterion q W t
    ⟨(W : V.Opens) ⊓ D.U, isAffineOpen_of_eq_basicOpen _ hWU⟩ rfl (fun i ω ↦ ?_) s
  rw [presheaf_map_id]
  exact D.mem_range_e_iff_mem_logForms i W t hJ hWU hS ω

/-- **Logarithmic forms are locally sums of wedges of logarithmic `1`-forms.** -/
theorem exists_list_wedgeFin_eq_map (q : ℕ) {O : V.Opens} (s : Γ(D.K (q + 1), O)) {x : V}
    (hx : x ∈ O) : ∃ (W : V.Opens) (h : W ≤ O), x ∈ W ∧
      ∃ l : List (Fin (q + 1) → Γ(D.K 1, W)),
        (l.map (D.wedgeFin q)).sum = (D.K (q + 1)).presheaf.map (homOfLE h).op s := by
  obtain ⟨W₁, t, hle, hxW₁, hJ₁, -, hWU, hS⟩ :=
    exists_affineOpen_snc_chart_le f D.J D.hJ D.U D.hU hx
  exact ⟨W₁, hle, hxW₁, D.exists_list_wedgeFin_eq_of_chart q W₁ t hJ₁ hWU hS _⟩

/-- Restriction of a sum of wedges of logarithmic `1`-forms. -/
theorem map_sum_wedgeFin (q : ℕ) {O O' : V.Opens} (h : O' ≤ O)
    (l : List (Fin (q + 1) → Γ(D.K 1, O))) :
    (D.K (q + 1)).presheaf.map (homOfLE h).op (l.map (D.wedgeFin q)).sum =
      ((l.map fun θ i ↦ (D.K 1).presheaf.map (homOfLE h).op (θ i)).map (D.wedgeFin q)).sum := by
  rw [presheaf_map_list_sum, List.map_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun θ _ ↦ D.wedgeFin_map h q θ)

/-- Scaling the first form of each family by `r` scales the sum of their wedge products by `r`. -/
theorem sum_wedgeFin_update_smul (q : ℕ) {O : V.Opens} (r : Γ(V, O))
    (l : List (Fin (q + 1) → Γ(D.K 1, O))) :
    ((l.map fun θ ↦ Function.update θ 0 (r • θ 0)).map (D.wedgeFin q)).sum =
      r • (l.map (D.wedgeFin q)).sum := by
  rw [List.smul_sum, List.map_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun θ _ ↦ D.wedgeFin_update_zero_smul r q θ)

/-- Sections of a term of `𝒦` agreeing on the affine opens of `O ∩ U` agree. -/
theorem complexZ_eq_of_forall_affineOpens {p : ℤ} {O : V.Opens} (y y' : Γ(D.complexZ.X p, O))
    (h : ∀ (G : V.affineOpens) (hG : (G : V.Opens) ≤ O ⊓ D.U),
      (D.complexZ.X p).presheaf.map (homOfLE (hG.trans inf_le_left)).op y =
        (D.complexZ.X p).presheaf.map (homOfLE (hG.trans inf_le_left)).op y') : y = y' := by
  rcases lt_or_ge p 0 with hp | hp
  · rw [D.extend_X_eq_zero hp y, D.extend_X_eq_zero hp y']
  lift p to ℕ using hp
  obtain ⟨s, rfl⟩ := (D.toComplexZ_bijective p O).2 y
  obtain ⟨s', rfl⟩ := (D.toComplexZ_bijective p O).2 y'
  refine congrArg _ (D.he_inj p O (sub_eq_zero.1 (D.eq_zero_of_forall_affineOpens p _
    fun G hG _ ↦ ?_)))
  have h1 := h G hG
  rw [← D.toComplexZ_res, ← D.toComplexZ_res] at h1
  have h2 := (D.toComplexZ_bijective p G).1 h1
  have hGG : (G : V.Opens) ≤ (G : V.Opens) ⊓ D.U := le_inf le_rfl (hG.trans inf_le_right)
  have e1 := D.map_e_map p (hG.trans inf_le_left) hGG s
  have e2 := D.map_e_map p (hG.trans inf_le_left) hGG s'
  rw [h2] at e1
  rw [map_sub, sub_eq_zero]
  exact e1.symm.trans e2

/-- The wedge product on `𝒦` in nonnegative degrees, on sections of the logarithmic forms. -/
theorem sectionProduct_mul_toComplexZ (i j : ℕ) (A : V.Opens) (a : Γ(D.K i, A))
    (b : Γ(D.K j, A)) :
    D.sectionProduct.mul i j ((i + j : ℕ) : ℤ) (by push_cast; ring) A (D.toComplexZ i A a)
        (D.toComplexZ j A b) =
      D.toComplexZ (i + j) A (D.wedge i j (i + j) rfl A a b) := by
  rw [D.sectionProduct_mul i j (i + j) rfl]
  have ha := D.extendXIso_hom_app_inv_app (i := i) rfl A a
  have hb := D.extendXIso_hom_app_inv_app (i := j) rfl A b
  exact congrArg ((D.complex.extendXIso embeddingUpNat rfl).inv.app A)
    (congrArg₂ (D.wedge i j (i + j) rfl _) ha hb)

/-- **Wedges of logarithmic `1`-forms are alternating.** -/
theorem wedgeFin_perm (q : ℕ) {O : V.Opens} (θ : Fin (q + 1) → Γ(D.K 1, O))
    (σ : Equiv.Perm (Fin (q + 1))) :
    D.wedgeFin q (θ ∘ σ) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • D.wedgeFin q θ := by
  refine D.he_inj (q + 1) O (sub_eq_zero.1 (D.eq_zero_of_forall_affineOpens (q + 1) _
    fun G hG _ ↦ ?_))
  rw [map_sub, sub_eq_zero]
  refine (formsAlgEquiv f (q + 1) G).injective ?_
  rw [map_zsmul, map_zsmul, map_zsmul, D.formsAlgEquiv_map_e_wedgeFin G hG q,
    D.formsAlgEquiv_map_e_wedgeFin G hG q, ← Units.smul_def, ← AlternatingMap.map_perm]
  simp only [Function.comp_def]

/-- The inverse Cartier relation is additive. -/
theorem cartierRep_add (q : ℕ) {W : V.Opens} {s s' z z' : Γ(D.K q, W)}
    (h : D.cartierRep q W s z) (h' : D.cartierRep q W s' z') :
    D.cartierRep q W (s + s') (z + z') := by
  intro A hA _
  let := MMP.Mori.sectionAlgebra f A
  have := (h A hA).add (h' A hA)
  simpa only [map_add] using this

/-- `0` represents the inverse Cartier image of `0`. -/
theorem cartierRep_zero (q : ℕ) {W : V.Opens} : D.cartierRep q W 0 0 := by
  intro A hA _
  let := MMP.Mori.sectionAlgebra f A
  simpa only [map_zero] using IsInvCartierRep.zero (p := p) (A := k) (L := Γ(V, A)) (i := q)

/-- The inverse Cartier relation is preserved by finite sums. -/
theorem cartierRep_list_sum (q : ℕ) {W : V.Opens} {α : Type*} (l : List α)
    {s z : α → Γ(D.K q, W)} (h : ∀ a, D.cartierRep q W (s a) (z a)) :
    D.cartierRep q W (l.map s).sum (l.map z).sum := by
  induction l with
  | nil => exact D.cartierRep_zero q
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact D.cartierRep_add q (h a) ih

/-- **Representatives multiply**: the wedge of representatives of `C⁻¹ s` and `C⁻¹ s'`
represents `C⁻¹ (s ∧ s')`. -/
theorem cartierRep_wedge (i j : ℕ) {W : V.Opens} {s z : Γ(D.K i, W)} {s' z' : Γ(D.K j, W)}
    (h : D.cartierRep i W s z) (h' : D.cartierRep j W s' z') :
    D.cartierRep (i + j) W (D.wedge i j (i + j) rfl W s s') (D.wedge i j (i + j) rfl W z z') := by
  intro A hA _
  let := MMP.Mori.sectionAlgebra f A
  rw [D.e_wedge, D.e_wedge, formsWedge_map, formsWedge_map, formsWedge_apply, formsWedge_apply,
    formsAlgEquiv_mul, formsAlgEquiv_mul]
  exact (h A hA).wedge (h' A hA)

namespace LocalFrobeniusSplitting

variable {D} (L : D.LocalFrobeniusSplitting)

/-- The iterated cup product of the cochains of `q + 1` logarithmic `1`-forms on an open
`O ⊆ U_x`, read at the tuple `x` in bidegree `(p, m)`: a multilinear map. -/
def cupMultilinear (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) (O : V.Opens) (hO : O ≤ inter L.U x) :
    MultilinearMap Γ(V, O) (fun _ : Fin (q + 1) ↦ Γ(D.K 1, O)) Γ(D.complexZ.X p, O) :=
  MultilinearMap.mk' (fun θ ↦ (D.complexZ.X p).presheaf.map (homOfLE (le_inf le_rfl hO)).op
      (CechTotalCochain.cupFin D.sectionProduct q (fun i ↦ L.oneCochain O (θ i)) p m h x))
    (fun θ i a b ↦ by
      have e : ∀ c, (fun j ↦ L.oneCochain O (Function.update θ i c j)) =
          Function.update (fun j ↦ L.oneCochain O (θ j)) i (L.oneCochain O c) := fun c ↦
        funext fun j ↦ Function.apply_update (fun _ ↦ L.oneCochain O) θ i c j
      rw [e, e, e, L.oneCochain_add, CechTotalCochain.cupFin_update_add]
      exact map_add _ _ _)
    (fun θ i r a ↦ by
      have e : ∀ c, (fun j ↦ L.oneCochain O (Function.update θ i c j)) =
          Function.update (fun j ↦ L.oneCochain O (θ j)) i (L.oneCochain O c) := fun c ↦
        funext fun j ↦ Function.apply_update (fun _ ↦ L.oneCochain O) θ i c j
      rw [e, e, L.oneCochain_smul,
        CechTotalCochain.cupFin_update_smul D.sectionProduct_isLinear]
      change (D.complexZ.X p).presheaf.map _ (V.presheaf.map (homOfLE inf_le_left).op r • _) = _
      rw [Scheme.Modules.map_smul, ring_presheaf_map_map _ _ (𝟙 _), op_id, V.presheaf.map_id]
      rfl)

/-- The antisymmetrised cup product of the cochains of `q + 1` logarithmic `1`-forms on an open
`O ⊆ U_x`, read at the tuple `x` in bidegree `(p, m)`. -/
def cupAt (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ) (h : p + m = (q : ℤ) + 1)
    {O : V.Opens} (hO : O ≤ inter L.U x) (θ : Fin (q + 1) → Γ(D.K 1, O)) :
    Γ(D.complexZ.X p, O) :=
  (D.complexZ.X p).presheaf.map (homOfLE (le_inf le_rfl hO)).op (L.cupCochain q O θ p m h x)

/-- `cupAt` is the alternatization of the multilinear map `cupMultilinear`. -/
theorem cupAt_eq_alternatization (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) {O : V.Opens} (hO : O ≤ inter L.U x)
    (θ : Fin (q + 1) → Γ(D.K 1, O)) :
    L.cupAt q x p h hO θ = (L.cupMultilinear q x p h O hO).alternatization θ := by
  rw [MultilinearMap.alternatization_apply]
  unfold cupAt LocalFrobeniusSplitting.cupCochain
  rw [Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Pi.smul_apply, map_zsmul, Units.smul_def]
  rfl

/-- Restriction to a smaller open commutes with `cupAt`. -/
theorem map_cupAt (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) {O O' : V.Opens} (hO : O ≤ inter L.U x) (h' : O' ≤ O)
    (θ : Fin (q + 1) → Γ(D.K 1, O)) :
    (D.complexZ.X p).presheaf.map (homOfLE h').op (L.cupAt q x p h hO θ) =
      L.cupAt q x p h (h'.trans hO) (fun i ↦ (D.K 1).presheaf.map (homOfLE h').op (θ i)) := by
  unfold cupAt
  rw [L.cupCochain_res q h' θ]
  change _ = (D.complexZ.X p).presheaf.map _ ((D.complexZ.X p).presheaf.map
    (homOfLE (inf_le_inf_right _ h')).op (L.cupCochain q O θ p m h x))
  rw [presheaf_map_map _ _ (homOfLE (le_inf h' (h'.trans hO))),
    presheaf_map_map _ _ (homOfLE (le_inf h' (h'.trans hO)))]

/-- The cup product of the restrictions of `1`-forms on `W` to `W ∩ U_x`, read at `x`, is the
component at `x` of the cup product on `W`. -/
theorem cupAt_inf (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) {W : V.Opens} (θ : Fin (q + 1) → Γ(D.K 1, W)) :
    L.cupAt q x p h (inf_le_right : W ⊓ inter L.U x ≤ _)
        (fun i ↦ (D.K 1).presheaf.map (homOfLE inf_le_left).op (θ i)) =
      L.cupCochain q W θ p m h x := by
  unfold cupAt
  rw [L.cupCochain_res q inf_le_left θ]
  change (D.complexZ.X p).presheaf.map _ ((D.complexZ.X p).presheaf.map
    (homOfLE (inf_le_inf_right _ inf_le_left)).op (L.cupCochain q W θ p m h x)) = _
  rw [presheaf_map_map _ _ (𝟙 _), presheaf_map_id]

/-- Restriction to a smaller open commutes with sums of `cupAt` over a list of families of
`1`-forms. -/
theorem map_sum_cupAt (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) {O O' : V.Opens} (hO : O ≤ inter L.U x) (h' : O' ≤ O)
    (l : List (Fin (q + 1) → Γ(D.K 1, O))) :
    (D.complexZ.X p).presheaf.map (homOfLE h').op (l.map (L.cupAt q x p h hO)).sum =
      ((l.map fun θ i ↦ (D.K 1).presheaf.map (homOfLE h').op (θ i)).map
        (L.cupAt q x p h (h'.trans hO))).sum := by
  rw [presheaf_map_list_sum, List.map_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun θ _ ↦ L.map_cupAt q x p h hO h' θ)

/-- Scaling the first form of each family by `r` scales the sum of their cup products `cupAt` by
`r`. -/
theorem sum_cupAt_update_smul (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) {O : V.Opens} (hO : O ≤ inter L.U x) (r : Γ(V, O))
    (l : List (Fin (q + 1) → Γ(D.K 1, O))) :
    ((l.map fun θ ↦ Function.update θ 0 (r • θ 0)).map (L.cupAt q x p h hO)).sum =
      r • (l.map (L.cupAt q x p h hO)).sum := by
  rw [List.smul_sum, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun θ _ ↦ ?_)
  simp only [Function.comp_apply, L.cupAt_eq_alternatization]
  rw [AlternatingMap.map_update_smul, Function.update_eq_self]

/-- **The antisymmetrised cup product only depends on the wedge**, on an affine open of `U`. -/
theorem sum_cupAt_eq_of_affine (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) (G : V.affineOpens) (hGU : (G : V.Opens) ≤ D.U)
    (hG : (G : V.Opens) ≤ inter L.U x) (l l' : List (Fin (q + 1) → Γ(D.K 1, G)))
    (hl : (l.map (D.wedgeFin q)).sum = (l'.map (D.wedgeFin q)).sum) :
    (l.map (L.cupAt q x p h hG)).sum = (l'.map (L.cupAt q x p h hG)).sum := by
  set l₁ := l ++ l'.map fun θ ↦ Function.update θ 0 ((-1 : Γ(V, G)) • θ 0)
  have h1 : (l₁.map (D.wedgeFin q)).sum = 0 := by
    rw [List.map_append, List.sum_append, D.sum_wedgeFin_update_smul, neg_one_smul, hl,
      add_neg_cancel]
  have h2 := D.sum_map_alternatingMap_eq_zero q G hGU
    (L.cupMultilinear q x p h G hG).alternatization l₁ h1
  have e : ∀ l₀ : List (Fin (q + 1) → Γ(D.K 1, G)),
      l₀.map (L.cupMultilinear q x p h G hG).alternatization = l₀.map (L.cupAt q x p h hG) :=
    fun l₀ ↦ List.map_congr_left fun θ _ ↦ (L.cupAt_eq_alternatization q x p h hG θ).symm
  rw [e, List.map_append, List.sum_append, L.sum_cupAt_update_smul, neg_one_smul,
    ← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

/-- **The antisymmetrised cup product only depends on the wedge.** -/
theorem sum_cupAt_eq (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) {O : V.Opens} (hO : O ≤ inter L.U x)
    (l l' : List (Fin (q + 1) → Γ(D.K 1, O)))
    (hl : (l.map (D.wedgeFin q)).sum = (l'.map (D.wedgeFin q)).sum) :
    (l.map (L.cupAt q x p h hO)).sum = (l'.map (L.cupAt q x p h hO)).sum := by
  refine D.complexZ_eq_of_forall_affineOpens _ _ fun G hG ↦ ?_
  rw [L.map_sum_cupAt, L.map_sum_cupAt]
  refine L.sum_cupAt_eq_of_affine q x p h G (hG.trans inf_le_right) _ _ _ ?_
  rw [← D.map_sum_wedgeFin, ← D.map_sum_wedgeFin, hl]

/-- The relation defining the antisymmetrised cup product on logarithmic `q + 1`-forms: `y` is
the cup product of a family of `1`-forms whose wedges sum to `s`. -/
def CupRel (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ) (h : p + m = (q : ℤ) + 1)
    (O : V.Opens) (hO : O ≤ inter L.U x) (s : Γ(D.K (q + 1), O)) (y : Γ(D.complexZ.X p, O)) :
    Prop :=
  ∃ l : List (Fin (q + 1) → Γ(D.K 1, O)),
    (l.map (D.wedgeFin q)).sum = s ∧ (l.map (L.cupAt q x p h hO)).sum = y

/-- The relation `CupRel` is a local section relation. -/
theorem isLocalSectionRel_cupRel (q : ℕ) {m : ℕ} (x : Fin (m + 1) → L.Chart) (p : ℤ)
    (h : p + m = (q : ℤ) + 1) : IsLocalSectionRel (L.CupRel q x p h) where
  exists_local O hO s pt hpt := by
    obtain ⟨W', hW', hptW', l, hl⟩ := D.exists_list_wedgeFin_eq_map q s hpt
    exact ⟨W', hW', hptW', _, l, hl, rfl⟩
  compat h₁ h₂ h₃₁ h₃₂ := by
    rintro s₁ y₁ s₂ y₂ ⟨l₁, rfl, rfl⟩ ⟨l₂, rfl, rfl⟩ hs
    rw [L.map_sum_cupAt, L.map_sum_cupAt]
    refine L.sum_cupAt_eq q x p h _ _ _ ?_
    rw [← D.map_sum_wedgeFin, ← D.map_sum_wedgeFin]
    exact hs
  res hO h' := by
    rintro s y ⟨l, rfl, rfl⟩
    exact ⟨_, (D.map_sum_wedgeFin q h' l).symm, (L.map_sum_cupAt q x p h hO h' l).symm⟩
  add hO := by
    rintro s y s' y' ⟨l, rfl, rfl⟩ ⟨l', rfl, rfl⟩
    exact ⟨l ++ l', by rw [List.map_append, List.sum_append],
      by rw [List.map_append, List.sum_append]⟩
  smul hO r := by
    rintro s y ⟨l, rfl, rfl⟩
    exact ⟨_, D.sum_wedgeFin_update_smul q r l, L.sum_cupAt_update_smul q x p h hO r l⟩

/-- The component of bidegree `(1, 0)` of the cochain of a logarithmic `1`-form at a single index
`α` is the local splitting `φ α`. -/
theorem oneCochain_one_zero (O : V.Opens) (ω : Γ(D.K 1, O)) (α : L.Chart)
    (h : (1 : ℤ) + ((0 : ℕ) : ℤ) = 1) (hle : O ⊓ inter L.U (fun _ : Fin 1 ↦ α) ≤ L.U α) :
    L.oneCochain O ω 1 0 h (fun _ ↦ α) =
      D.toComplexZ 1 _ (L.φ α _ hle ((D.K 1).presheaf.map (homOfLE inf_le_left).op ω)) := by
  have e := L.toCechGluingSections.toCechGluingData.toCechCocycleData_g_zero_app_down α O ω
    (by simp)
  change ((cechBiπ D.complexZ (0 + 1) 0 (fun _ ↦ α)).app O
    ((L.oneCocycle.g (0 + 1) 0 (by simp)).app O ω)).down = _
  refine e.trans ?_
  change (D.complexZ.X ((1 : ℕ) : ℤ)).presheaf.map (homOfLE _).op
    (D.toComplexZ 1 _ (L.φ α (O ⊓ L.U α) inf_le_right
      ((D.K 1).presheaf.map (homOfLE inf_le_left).op ω))) = _
  rw [← D.toComplexZ_res, ← L.φ_res, presheaf_map_map]

/-- **The component of bidegree `(q + 1, 0)` of the iterated cup product** of the cochains of
logarithmic `1`-forms at a single index `α` is the wedge of their local splittings. -/
theorem cupFin_oneCochain_zero (O : V.Opens) (α : L.Chart)
    (hle : O ⊓ inter L.U (fun _ : Fin 1 ↦ α) ≤ L.U α) : (q : ℕ) →
    (θ : Fin (q + 1) → Γ(D.K 1, O)) → (h : ((q + 1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = (q : ℤ) + 1) →
    CechTotalCochain.cupFin D.sectionProduct q (fun i ↦ L.oneCochain O (θ i))
        ((q + 1 : ℕ) : ℤ) 0 h (fun _ ↦ α) =
      D.toComplexZ (q + 1) _ (D.wedgeFin q
        (fun i ↦ L.φ α _ hle ((D.K 1).presheaf.map (homOfLE inf_le_left).op (θ i))))
  | 0, θ, h => by
    rw [CechTotalCochain.cupFin_zero_apply]
    exact (L.oneCochain_one_zero O (θ 0) α _ hle).trans rfl
  | q + 1, θ, h => by
    refine (CechTotalCochain.cupFin_succ_apply_zero D.sectionProduct q _ h (fun _ ↦ α)).trans ?_
    change D.sectionProduct.mul ((q + 1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) ((q + 1 + 1 : ℕ) : ℤ) _ _
      (CechTotalCochain.cupFin D.sectionProduct q (fun i ↦ L.oneCochain O (θ i.castSucc))
        ((q + 1 : ℕ) : ℤ) 0 (by push_cast; ring) (fun _ ↦ α))
      (L.oneCochain O (θ (Fin.last _)) 1 0 (by simp) (fun _ ↦ α)) = _
    rw [cupFin_oneCochain_zero O α hle q, L.oneCochain_one_zero O _ α _ hle,
      D.sectionProduct_mul_toComplexZ]
    rfl

/-- The wedge of the local splittings of logarithmic `1`-forms represents the inverse Cartier image
of their wedge. -/
theorem cartierRep_wedgeFin (α : L.Chart) {W : V.Opens} (hW : W ≤ L.U α) : (q : ℕ) →
    (θ : Fin (q + 1) → Γ(D.K 1, W)) →
    D.cartierRep (q + 1) W (D.wedgeFin q θ) (D.wedgeFin q (fun i ↦ L.φ α W hW (θ i)))
  | 0, θ => L.cartierRep_φ α W hW (θ 0)
  | q + 1, θ => D.cartierRep_wedge (q + 1) 1 (cartierRep_wedgeFin α hW q _)
      (L.cartierRep_φ α W hW (θ (Fin.last _)))

/-- The components of the Čech cocycle of the antisymmetrised cup products on logarithmic
`q + 1`-forms, glued from the local cup products of families of `1`-forms. -/
def cupComponent (q : ℕ) (p : ℤ) (m : ℕ) (h : p + m = (q : ℤ) + 1) :
    D.K (q + 1) ⟶ ((cechBicomplex L.U D.complexZ).X p).X m :=
  toCechBiOfSections L.U D.complexZ p m
    (fun x O hO ↦ (L.isLocalSectionRel_cupRel q x p h).glue O hO)
    (fun x _ hO r s ↦ (L.isLocalSectionRel_cupRel q x p h).glueSec_smul hO r s)
    (fun x _ _ _ h₂ hle s ↦ (L.isLocalSectionRel_cupRel q x p h).glueSec_res h₂ hle s)

/-- On a sum of wedges of logarithmic `1`-forms, the components of the cocycle are the sums of
the antisymmetrised cup products. -/
theorem secCochain_cupComponent_app (q : ℕ) (p : ℤ) (m : ℕ) (h : p + m = (q : ℤ) + 1)
    (W : V.Opens) (l : List (Fin (q + 1) → Γ(D.K 1, W))) :
    secCochain ((L.cupComponent q p m h).app W (l.map (D.wedgeFin q)).sum) =
      fun x ↦ (l.map fun θ ↦ L.cupCochain q W θ p m h x).sum := by
  funext x
  refine (cechBiπ_app_toCechBiOfSections_app_down D.complexZ p m _ _ _ x W _).trans ?_
  rw [IsLocalSectionRel.glue_apply]
  refine (L.isLocalSectionRel_cupRel q x p h).glueSec_eq _ ⟨_, (D.map_sum_wedgeFin q _ l).symm, ?_⟩
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left fun θ _ ↦ L.cupAt_inf q x p h θ)

/-- **The component of bidegree `(q + 1, 0)` of the antisymmetrised cup product** at a single
index `α` is `(q + 1)!` times the wedge of the local splittings. -/
theorem cupCochain_zero_const (q : ℕ) {W : V.Opens} (α : L.Chart) (hW : W ≤ L.U α)
    (θ : Fin (q + 1) → Γ(D.K 1, W)) (h : ((q + 1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) = (q : ℤ) + 1) :
    L.cupCochain q W θ ((q + 1 : ℕ) : ℤ) 0 h (fun _ ↦ α) =
      ((q + 1).factorial : ℤ) • (D.complexZ.X ((q + 1 : ℕ) : ℤ)).presheaf.map
        (homOfLE inf_le_left).op
        (D.toComplexZ (q + 1) W (D.wedgeFin q (fun i ↦ L.φ α W hW (θ i)))) := by
  have hle : W ⊓ inter L.U (fun _ : Fin 1 ↦ α) ≤ L.U α := inf_le_left.trans hW
  have hw : ∀ σ : Equiv.Perm (Fin (q + 1)),
      D.wedgeFin q (fun i ↦ L.φ α _ hle ((D.K 1).presheaf.map (homOfLE inf_le_left).op
        (θ (σ i)))) = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        (D.K (q + 1)).presheaf.map (homOfLE inf_le_left).op
          (D.wedgeFin q (fun i ↦ L.φ α W hW (θ i))) := by
    intro σ
    rw [D.wedgeFin_map]
    simp only [← L.φ_res α _ W hle hW inf_le_left]
    exact D.wedgeFin_perm q (fun i ↦ L.φ α _ hle
      ((D.K 1).presheaf.map (homOfLE inf_le_left).op (θ i))) σ
  unfold cupCochain
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  simp only [L.cupFin_oneCochain_zero W α hle, hw, map_zsmul, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, natCast_zsmul, D.toComplexZ_res]

/-- An integer multiple of the cochain obtained by evaluating the components `cupComponent` on
a section `s` is a cocycle of the Čech total complex. -/
theorem isCocycle_cupComponent (q : ℕ) (c : ℤ) (W : V.Opens) (s : Γ(D.K (q + 1), W)) :
    CechTotalCochain.IsCocycle (n := ((q + 1 : ℕ) : ℤ)) (fun p m h ↦
      secCochain ((c • L.cupComponent q p m (h.trans (by push_cast; ring))).app W s)) := by
  refine CechTotalCochain.isCocycle_of_local _ fun pt hpt ↦ ?_
  obtain ⟨W', hW', hptW', l, hl⟩ := D.exists_list_wedgeFin_eq_map q s hpt
  refine ⟨W', hW', hptW', ?_⟩
  have key : CechTotalCochain.res hW' (n := ((q + 1 : ℕ) : ℤ)) (fun p m h ↦
      secCochain ((c • L.cupComponent q p m (h.trans (by push_cast; ring))).app W s)) =
      fun p m h ↦ c • (l.map fun θ ↦ ((L.cupCochain q W' θ).cast ((q + 1 : ℕ) : ℤ)
        (by push_cast; ring)) p m h).sum := by
    funext p m h
    change CechCochain.res hW' (secCochain ((c • L.cupComponent q p m _).app W s)) = _
    rw [← secCochain_map, ← app_presheaf_map, ← hl, zsmul_app_apply, secCochain_zsmul,
      L.secCochain_cupComponent_app]
    congr 1
    funext x
    rw [Pi.list_sum_apply, List.map_map]
    rfl
  rw [key]
  exact (CechTotalCochain.isCocycle_list_sum l fun θ ↦
    (L.isCocycle_cupCochain q W' θ).cast _ _).zsmul c

/-- **The Čech cocycle of the antisymmetrised cup products** on logarithmic `q + 1`-forms, scaled
by an integer `c`. -/
def cupCocycle (q : ℕ) (c : ℤ) :
    CechCocycleData L.U D.complexZ (D.K (q + 1)) ((q + 1 : ℕ) : ℤ) where
  g p m h := c • L.cupComponent q p m (h.trans (by push_cast; ring))
  isCocycle := L.isCocycle_cupComponent q c

/-- **The scaled cup-product cocycle represents the inverse Cartier map** when `c (q + 1)! ≡ 1`
modulo `p`. -/
theorem isCartierCocycle_cupCocycle (q : ℕ) {c : ℕ} (hc : c * (q + 1).factorial % p = 1) :
    D.IsCartierCocycle (q + 1) (L.cupCocycle q c) := by
  intro W s pt hpt
  have hpt' : pt ∈ ⨆ α, L.U α := by rw [L.iSup_U]; trivial
  obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hpt'
  obtain ⟨W₁, hW₁, hpt₁, l, hl⟩ := D.exists_list_wedgeFin_eq_map q
    ((D.K (q + 1)).presheaf.map (homOfLE (inf_le_left : W ⊓ L.U α ≤ W)).op s)
    (⟨hpt, hα⟩ : pt ∈ W ⊓ L.U α)
  rw [presheaf_map_map _ _ (homOfLE (hW₁.trans inf_le_left))] at hl
  have hW₁α : W₁ ≤ L.U α := hW₁.trans inf_le_right
  refine ⟨α, W₁, hW₁.trans inf_le_left, hW₁α, hpt₁,
    (l.map fun θ ↦ D.wedgeFin q (fun i ↦ L.φ α W₁ hW₁α (θ i))).sum, ?_, ?_⟩
  · rw [← hl]
    exact D.cartierRep_list_sum (q + 1) l fun θ ↦ L.cartierRep_wedgeFin α hW₁α q θ
  · rw [← hl]
    change secCochain (((c : ℤ) • L.cupComponent q _ 0 _).app W₁ _) (fun _ ↦ α) = _
    rw [zsmul_app_apply, secCochain_zsmul, L.secCochain_cupComponent_app, Pi.smul_apply]
    simp only [L.cupCochain_zero_const q α hW₁α]
    rw [map_list_sum, presheaf_map_list_sum, List.map_map, List.map_map, List.smul_sum,
      List.map_map]
    refine congrArg List.sum (List.map_congr_left fun θ _ ↦ ?_)
    simp only [Function.comp_apply]
    rw [smul_smul, ← Nat.cast_mul]
    exact natCast_zsmul_eq_self (R := Γ(V, W₁ ⊓ inter L.U (fun _ : Fin 1 ↦ α)))
      (cast_eq_zero_of_isInCharacteristic D.hV _) hc _

end LocalFrobeniusSplitting

/-- **The Deligne–Illusie decomposition** `⨁_{q ≤ n} K^q[-q] ≅ F_*K^•` in the derived category,
for a smooth proper `k`-scheme of dimension `n < p` with a simple normal crossing divisor, lifted
with the divisor over `W₂(k)`. -/
theorem nonempty_iso_directSum_singleFunctor :
    Nonempty ((⨁ fun q : Fin (n + 1) ↦
        (DerivedCategory.singleFunctor V.Modules ((q : ℕ) : ℤ)).obj (D.K q)) ≅
      DerivedCategory.Q.obj D.complexZ) := by
  obtain ⟨L⟩ := D.nonempty_localFrobeniusSplitting
  have hc : ∀ q : Fin n, ∃ c : ℕ, c * ((q : ℕ) + 1).factorial % p = 1 := fun q ↦ by
    have hp : Nat.Coprime p ((q : ℕ) + 1).factorial := by
      rw [Nat.Prime.coprime_iff_not_dvd Fact.out, Nat.Prime.dvd_factorial Fact.out]
      have := D.hpn
      omega
    obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hp.symm (Fact.out : p.Prime).one_lt
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  choose c hc using hc
  let Ψ : ∀ q : Fin (n + 1), CechCocycleData L.U D.complexZ (D.K q) ((q : ℕ) : ℤ) :=
    Fin.cases (D.zeroCocycle L.U D.frobeniusPow D.cartierRep_frobeniusPow)
      (fun q ↦ L.cupCocycle q (c q))
  refine D.nonempty_iso_of_isCartierCocycle L.iSup_U Ψ fun q ↦ ?_
  refine Fin.cases ?_ (fun q ↦ ?_) q
  · exact D.isCartierCocycle_zeroCocycle L.U D.frobeniusPow D.cartierRep_frobeniusPow L.iSup_U
  · exact L.isCartierCocycle_cupCocycle q (hc q)

end FrobeniusSplittingData

end MMP.DeRham
