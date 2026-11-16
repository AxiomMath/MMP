module

public import MMP.Algebra.Category.ModuleCat.Sheaf.RelLocallyExact

/-!
# Local exactness of the twist inclusion of the fractional logarithmic complex

Let `C^•` be the fractional logarithmic complex `𝒪_V(-M) · Ω^•_V(log D)` with the connection
`∇ = d - N⁻¹ du/u ∧`, and `C'^• ⊆ C^•` its twist by `-E` for a component `E` of `D`, the
complex of the same connection on `𝒪_V(-M - E) · Ω^•_V(log D)`. The residue of `∇` along `E` is
a nonzero number `λ`, and this makes the inclusion `C'^• ⊆ C^•` relatively locally exact: near a
point of `E`, with `t` an equation of `E` and `θ = dt/t`, write a section of `C^{q+1}` as
`g₀ (α + θ ∧ β)` with `g₀` a generator of `𝒪_V(-M)` and `α`, `β` free of `θ`. If `∇ x` lies in
`C'`, then comparing `θ`-parts modulo `t` gives `λ α ≡ ξ' ∧ β + dβ`, and `x - ∇(λ⁻¹ g₀ β)` lies
in `C'`.

## Main definitions

* `MMP.LcBpf.ResidueData`: the chart data of the residue argument along one component.
* `MMP.LcBpf.TwistChart`: a residue chart of a twist inclusion, encoding sections as forms.

## Main results

* `MMP.LcBpf.relLocallyExact_comp`: relative local exactness composes.
* `MMP.LcBpf.ResidueData.exists_sub_nabla_mem`: the residue argument in positive degree.
* `MMP.LcBpf.ResidueData.exists_eq_smul_of_nabla_mem_zero`: the residue argument in degree zero.
* `MMP.LcBpf.relLocallyExact_of_twistCharts`: residue charts near every point of `E`, and
  surjectivity off `E`, make the twist inclusion relatively locally exact.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace MMP.LcBpf

section Comp

variable {X : TopCat.{0}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- The sections map of a composite of morphisms of sheaves of modules is the composite of the
sections maps. -/
theorem sheafOfModules_comp_app_apply {A B C : SheafOfModules.{0} R} (f : A ⟶ B) (g : B ⟶ C)
    (W : Opens X) (a : A.val.obj (op W)) :
    (f ≫ g).val.app (op W) a = g.val.app (op W) (f.val.app (op W) a) := rfl

/-- Restriction of sections of a sheaf of modules, as a map of sections. -/
noncomputable abbrev restr (A : SheafOfModules.{0} R) {V W : Opens X} (h : V ≤ W)
    (a : A.val.obj (op W)) : A.val.obj (op V) :=
  A.val.map (homOfLE h).op a

/-- Restriction of sections is additive. -/
theorem restr_add (A : SheafOfModules.{0} R) {V W : Opens X} (h : V ≤ W)
    (a b : A.val.obj (op W)) : restr A h (a + b) = restr A h a + restr A h b :=
  map_add (A.val.map (homOfLE h).op).hom a b

/-- Restricting from `W` to `V` and then to `V'` is restricting from `W` to `V'`. -/
theorem restr_restr (A : SheafOfModules.{0} R) {V V' W : Opens X} (h : V ≤ W) (h' : V' ≤ V)
    (a : A.val.obj (op W)) : restr A h' (restr A h a) = restr A (h'.trans h) a :=
  (PresheafOfModules.map_comp_apply A.val (homOfLE h).op (homOfLE h').op a).symm

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem app_restr {A B : SheafOfModules.{0} R} (f : A ⟶ B) {V W : Opens X} (h : V ≤ W)
    (a : A.val.obj (op W)) : f.val.app (op V) (restr A h a) = restr B h (f.val.app (op W) a) :=
  PresheafOfModules.naturality_apply f.val (homOfLE h).op a

/-- **Relative local exactness composes** along a composite `K'' ⟶ K' ⟶ K` whose second map is
injective on sections. -/
theorem relLocallyExact_comp {K'' K' K : CochainComplex (SheafOfModules.{0} R) ℕ}
    (φ' : K'' ⟶ K') (φ : K' ⟶ K)
    (hinj : ∀ (p : ℕ) (W : Opens X), Function.Injective ((φ.f p).val.app (op W)))
    (h' : RelLocallyExact φ') (h : RelLocallyExact φ) : RelLocallyExact (φ' ≫ φ) := by
  intro p W x ⟨z, hz⟩ pt hpt
  obtain ⟨V, hV, hptV, y, x', hx⟩ := h p W x ⟨(φ'.f (p + 1)).val.app (op W) z, hz⟩ pt hpt
  change restr (K.X p) hV x = _ at hx
  have hdd : ∀ (V : Opens X) (y : (K.X (p - 1)).val.obj (op V)),
      (K.d p (p + 1)).val.app (op V) ((K.d (p - 1) p).val.app (op V) y) = 0 := fun _ y =>
    congrArg (fun f => f.val.app _ y) (K.d_comp_d (p - 1) p (p + 1))
  have hcomm : ∀ (i j : ℕ) (V : Opens X) (y : (K'.X i).val.obj (op V)),
      (K.d i j).val.app (op V) ((φ.f i).val.app (op V) y) =
        (φ.f j).val.app (op V) ((K'.d i j).val.app (op V) y) := fun i j V y => by
    have := congrArg (fun f => f.val.app (op V) y) (φ.comm i j)
    simp only [sheafOfModules_comp_app_apply] at this
    exact this
  have hdx' : (K'.d p (p + 1)).val.app (op V) x' =
      (φ'.f (p + 1)).val.app (op V) (restr (K''.X (p + 1)) hV z) := by
    apply hinj (p + 1) V
    have e1 := congrArg ((K.d p (p + 1)).val.app (op V)) hx
    rw [map_add, hdd, zero_add, app_restr, ← hz, hcomm] at e1
    rw [← e1, ← sheafOfModules_comp_app_apply, app_restr]
    rfl
  obtain ⟨V', hV', hptV', y', x'', hx'⟩ := h' p V x' ⟨_, hdx'.symm⟩ pt hptV
  change restr (K'.X p) hV' x' = _ at hx'
  refine ⟨V', hV'.trans hV, hptV',
    restr (K.X (p - 1)) hV' y + (φ.f (p - 1)).val.app (op V') y', x'', ?_⟩
  change restr (K.X p) (hV'.trans hV) x = _
  rw [← restr_restr (K.X p) hV hV', hx, restr_add, ← app_restr, ← app_restr, hx', map_add, map_add,
    hcomm, add_assoc]
  rfl

end Comp

section Residue

/-- **The chart data of the residue argument along one component `E` of `D`.** On a chart near a
point of `E`, with `t` an equation of `E` and `θ = dt/t`, a logarithmic `q`-form with regular
coefficients is `α + θ ∧ β` with `α`, `β` in the lattices `L q`, `L (q - 1)` of logarithmic forms
with regular coefficients and no `θ`; it lies in the twist by `-E` exactly when it is
`t (α' + θ ∧ β')`. The connection is `∇ = ξ₀ ∧ - + d` on forms divided by the generator `g₀` of
`𝒪(-M)`, where `ξ₀ = λ θ + ξ' + t μ θ`, `λ` is the residue along `E` and `ξ'` has no `θ`. Here
`Λ` is a ring of forms, an algebra over the ring `R` of regular functions on the chart. -/
structure ResidueData (R Λ : Type*) [CommRing R] [Ring Λ] [Algebra R Λ] where
  /-- The logarithmic `q`-forms with regular coefficients and no `θ`. -/
  L : ℕ → Submodule R Λ
  /-- The form `θ = dt/t`. -/
  θ : Λ
  /-- The part of `ξ₀` with no `θ`. -/
  ξ' : Λ
  /-- The equation of `E`. -/
  t : R
  /-- The correction `t μ` of the `θ`-coefficient of `ξ₀`. -/
  μ : R
  /-- The residue `λ` along `E`. -/
  lam : R
  /-- The inverse of the residue. -/
  lamInv : R
  /-- The de Rham differential in degree `q`. -/
  d : ℕ → Λ →+ Λ
  θ_mul_self : θ * θ = 0
  θ_mul_ξ' : θ * ξ' = -(ξ' * θ)
  ξ'_mul_mem : ∀ q, ∀ a ∈ L q, ξ' * a ∈ L (q + 1)
  lamInv_mul_lam : lamInv * lam = 1
  /-- The `θ`-part of a form in the twist by `-E` is divisible by `t`. -/
  eq_smul_of_add_θ_mul : ∀ q, ∀ a ∈ L (q + 1), ∀ b ∈ L q, ∀ a' ∈ L (q + 1), ∀ b' ∈ L q,
    a + θ * b = t • (a' + θ * b') → ∃ b'' ∈ L q, b = t • b''
  /-- The differential of a form with no `θ` has its `θ`-part divisible by `t`. -/
  d_mem : ∀ q, ∀ a ∈ L q, ∃ a₀ ∈ L (q + 1), ∃ a₁ ∈ L q, d q a = a₀ + t • (θ * a₁)
  d_θ_mul : ∀ q, ∀ b ∈ L q, d (q + 1) (θ * b) = -(θ * d q b)
  d_lamInv_smul : ∀ q b, d q (lamInv • b) = lamInv • d q b

namespace ResidueData

variable {R Λ : Type*} [CommRing R] [Ring Λ] [Algebra R Λ] (H : ResidueData R Λ)

/-- The connection form `ξ₀ = λ θ + ξ' + t μ θ`. -/
def ξ₀ : Λ := H.lam • H.θ + H.ξ' + (H.t * H.μ) • H.θ

/-- The connection `∇ = ξ₀ ∧ - + d` in degree `q`, on forms divided by the generator `g₀`. -/
def nabla (q : ℕ) (z : Λ) : Λ := H.ξ₀ * z + H.d q z

/-- **The residue argument.** If `x = α + θ ∧ β` is a logarithmic `(q + 1)`-form with
`∇ x` in the twist by `-E`, then `y = λ⁻¹ β` is a logarithmic `q`-form with `x - ∇ y` in the
twist by `-E`. -/
theorem exists_sub_nabla_mem (q : ℕ) {α β : Λ} (hα : α ∈ H.L (q + 1)) (hβ : β ∈ H.L q)
    (h : ∃ a' ∈ H.L (q + 2), ∃ b' ∈ H.L (q + 1),
      H.nabla (q + 1) (α + H.θ * β) = H.t • (a' + H.θ * b')) :
    H.lamInv • β ∈ H.L q ∧ ∃ a' ∈ H.L (q + 1), ∃ b' ∈ H.L q,
      (α + H.θ * β) - H.nabla q (H.lamInv • β) = H.t • (a' + H.θ * b') := by
  obtain ⟨a', ha', b', hb', hab⟩ := h
  obtain ⟨a₀, ha₀, a₁, ha₁, hda⟩ := H.d_mem (q + 1) α hα
  obtain ⟨b₀, hb₀, b₁, hb₁, hdb⟩ := H.d_mem q β hβ
  -- `∇ x = (ξ' α + a₀) + θ (λ α + t μ α + t a₁ - ξ' β - b₀)`
  have hsplit : H.nabla (q + 1) (α + H.θ * β) = (H.ξ' * α + a₀) +
      H.θ * (H.lam • α + (H.t * H.μ) • α + H.t • a₁ - H.ξ' * β - b₀) := by
    simp only [nabla, ξ₀, map_add, hda, H.d_θ_mul q β hβ, hdb]
    simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, ← mul_assoc,
      H.θ_mul_self, H.θ_mul_ξ', zero_mul, smul_zero, neg_mul]
    abel
  rw [hsplit] at hab
  obtain ⟨c, hc, hce⟩ := H.eq_smul_of_add_θ_mul (q + 1) _
    (add_mem (H.ξ'_mul_mem _ α hα) ha₀) _
    (sub_mem (sub_mem (add_mem (add_mem (Submodule.smul_mem _ _ hα) (Submodule.smul_mem _ _ hα))
      (Submodule.smul_mem _ _ ha₁)) (H.ξ'_mul_mem _ β hβ)) hb₀) a' ha' b' hb' hab
  refine ⟨Submodule.smul_mem _ _ hβ, H.lamInv • (c - H.μ • α - a₁),
    Submodule.smul_mem _ _ (sub_mem (sub_mem hc (Submodule.smul_mem _ _ hα)) ha₁),
    -(H.lamInv • (H.μ • β + b₁)),
    neg_mem (Submodule.smul_mem _ _ (add_mem (Submodule.smul_mem _ _ hβ) hb₁)), ?_⟩
  -- `b₀ = λ α + t μ α + t a₁ - ξ' β - t c`
  have hb₀e : b₀ = H.lam • α + (H.t * H.μ) • α + H.t • a₁ - H.ξ' * β - H.t • c := by
    rw [← hce]
    abel
  simp only [nabla, ξ₀, H.d_lamInv_smul, hdb, hb₀e]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub,
    smul_neg, mul_neg, smul_smul, ← mul_assoc]
  rw [H.lamInv_mul_lam, one_smul, one_smul, mul_comm H.t H.lamInv]
  abel

/-- **The residue argument in degree zero.** A function `α` (divided by `g₀`) with `∇ α` in the
twist by `-E` is itself in the twist by `-E`. -/
theorem exists_eq_smul_of_nabla_mem_zero {α : Λ} (hα : α ∈ H.L 0)
    (h : ∃ a' ∈ H.L 1, ∃ b' ∈ H.L 0, H.nabla 0 α = H.t • (a' + H.θ * b')) :
    ∃ a' ∈ H.L 0, α = H.t • a' := by
  obtain ⟨a', ha', b', hb', hab⟩ := h
  obtain ⟨a₀, ha₀, a₁, ha₁, hda⟩ := H.d_mem 0 α hα
  have hsplit : H.nabla 0 α = (H.ξ' * α + a₀) +
      H.θ * (H.lam • α + (H.t * H.μ) • α + H.t • a₁) := by
    simp only [nabla, ξ₀, hda]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    abel
  rw [hsplit] at hab
  obtain ⟨c, hc, hce⟩ := H.eq_smul_of_add_θ_mul 0 _ (add_mem (H.ξ'_mul_mem _ α hα) ha₀) _
    (add_mem (add_mem (Submodule.smul_mem _ _ hα) (Submodule.smul_mem _ _ hα))
      (Submodule.smul_mem _ _ ha₁)) a' ha' b' hb' hab
  refine ⟨H.lamInv • (c - H.μ • α - a₁),
    Submodule.smul_mem _ _ (sub_mem (sub_mem hc (Submodule.smul_mem _ _ hα)) ha₁), ?_⟩
  have e : H.lam • α = H.t • c - (H.t * H.μ) • α - H.t • a₁ := by
    rw [← hce]
    abel
  have e2 := congrArg (H.lamInv • ·) e
  simp only [smul_smul, H.lamInv_mul_lam, one_smul, smul_sub] at e2
  refine e2.trans ?_
  module

end ResidueData

end Residue

section Assembly

variable {X : TopCat.{0}} {Rs : Sheaf (Opens.grothendieckTopology X) RingCat.{0}}

/-- **A residue chart of a twist inclusion over an open `V`.** The sections of `K` and `K'` over
`V` are encoded, injectively and compatibly with `φ`, as forms `g₀ ω` in a ring `Λ` carrying
residue data `H` along the component `E`: sections of `K` are `g₀ (α + θ ∧ β)`, sections of `K'`
are `g₀ t (α' + θ ∧ β')` and every such form is one, every `g₀ b` with `b` free of `θ` is a
section of `K`, and the differential of `K` is `g₀ ∇`. -/
structure TwistChart {K' K : CochainComplex (SheafOfModules.{0} Rs) ℕ} (φ : K' ⟶ K)
    (V : Opens X) where
  /-- The regular functions on the chart. -/
  R : Type
  /-- The ring of forms. -/
  Λ : Type
  [instCommRing : CommRing R]
  [instRing : Ring Λ]
  [instAlgebra : Algebra R Λ]
  /-- The residue data along `E`. -/
  H : ResidueData R Λ
  /-- The generator `g₀` of `𝒪(-M)`. -/
  G : Λ
  /-- The encoding of the sections of `K`. -/
  E : ∀ q, (K.X q).val.obj (op V) →+ Λ
  /-- The encoding of the sections of `K'`. -/
  E' : ∀ q, (K'.X q).val.obj (op V) →+ Λ
  /-- The encoding of the sections of `K` is injective. -/
  E_injective : ∀ q, Function.Injective (E q)
  E_φ : ∀ q x', E q ((φ.f q).val.app (op V) x') = E' q x'
  G_cancel : ∀ a b, G * a = G * b → a = b
  rep_zero : ∀ x, ∃ α ∈ H.L 0, E 0 x = G * α
  rep_succ : ∀ q x, ∃ α ∈ H.L (q + 1), ∃ β ∈ H.L q, E (q + 1) x = G * (α + H.θ * β)
  twist_rep : ∀ q z, ∃ a ∈ H.L (q + 1), ∃ b ∈ H.L q,
    E' (q + 1) z = G * H.t • (a + H.θ * b)
  twist_lift_zero : ∀ a ∈ H.L 0, ∃ z, E' 0 z = G * H.t • a
  twist_lift_succ : ∀ q, ∀ a ∈ H.L (q + 1), ∀ b ∈ H.L q, ∃ z,
    E' (q + 1) z = G * H.t • (a + H.θ * b)
  lift : ∀ q, ∀ b ∈ H.L q, ∃ y, E q y = G * b
  d_rep : ∀ q y z, E q y = G * z →
    E (q + 1) ((K.d q (q + 1)).val.app (op V) y) = G * H.nabla q z

attribute [instance] TwistChart.instCommRing TwistChart.instRing TwistChart.instAlgebra

/-- **Local exactness of a twist inclusion from residue charts.** If every point of every open
`W` has a neighbourhood `V ⊆ W` which either carries a residue chart of `φ`, or on which `φ` is
onto on sections (the points off `E`), then `φ` is relatively locally exact. -/
theorem relLocallyExact_of_twistCharts {K' K : CochainComplex (SheafOfModules.{0} Rs) ℕ}
    (φ : K' ⟶ K)
    (hloc : ∀ (W : Opens X), ∀ pt ∈ W, ∃ (V : Opens X) (_ : V ≤ W), pt ∈ V ∧
      (Nonempty (TwistChart φ V) ∨
        ∀ (q : ℕ) (x : (K.X q).val.obj (op V)), ∃ x', x = (φ.f q).val.app (op V) x')) :
    RelLocallyExact φ := by
  intro p W x ⟨z, hz⟩ pt hpt
  obtain ⟨V, hV, hptV, hc | hoff⟩ := hloc W pt hpt
  swap
  · obtain ⟨x', hx'⟩ := hoff p (restr (K.X p) hV x)
    refine ⟨V, hV, hptV, 0, x', ?_⟩
    rw [map_zero, zero_add]
    exact hx'
  obtain ⟨C⟩ := hc
  have hdz : (K.d p (p + 1)).val.app (op V) (restr (K.X p) hV x) =
      (φ.f (p + 1)).val.app (op V) (restr (K'.X (p + 1)) hV z) := by
    rw [app_restr, app_restr, hz]
  refine ⟨V, hV, hptV, ?_⟩
  change ∃ y x', restr (K.X p) hV x = _
  cases p with
  | zero =>
    obtain ⟨α, hα, hEx⟩ := C.rep_zero (restr (K.X 0) hV x)
    obtain ⟨a', ha', b', hb', hEz⟩ := C.twist_rep 0 (restr (K'.X 1) hV z)
    have h1 := C.d_rep 0 _ _ hEx
    rw [hdz, C.E_φ, hEz] at h1
    obtain ⟨a'', ha'', hα'⟩ :=
      C.H.exists_eq_smul_of_nabla_mem_zero hα ⟨a', ha', b', hb', (C.G_cancel _ _ h1).symm⟩
    obtain ⟨z₀, hz₀⟩ := C.twist_lift_zero a'' ha''
    refine ⟨0, z₀, ?_⟩
    rw [map_zero, zero_add]
    apply C.E_injective 0
    rw [C.E_φ, hz₀, hEx, hα']
  | succ q =>
    obtain ⟨α, hα, β, hβ, hEx⟩ := C.rep_succ q (restr (K.X (q + 1)) hV x)
    obtain ⟨a', ha', b', hb', hEz⟩ := C.twist_rep (q + 1) (restr (K'.X (q + 2)) hV z)
    have h1 := C.d_rep (q + 1) _ _ hEx
    rw [hdz, C.E_φ, hEz] at h1
    obtain ⟨hβ', a'', ha'', b'', hb'', hcore⟩ :=
      C.H.exists_sub_nabla_mem q hα hβ ⟨a', ha', b', hb', (C.G_cancel _ _ h1).symm⟩
    obtain ⟨y, hy⟩ := C.lift q _ hβ'
    obtain ⟨x', hx'⟩ := C.twist_lift_succ q a'' ha'' b'' hb''
    refine ⟨y, x', ?_⟩
    apply C.E_injective (q + 1)
    change C.E (q + 1) _ = C.E (q + 1) ((K.d q (q + 1)).val.app (op V) y + _)
    rw [map_add, C.d_rep q y _ hy, C.E_φ, hx', hEx, ← hcore, ← mul_add]
    congr 1
    abel

end Assembly

end MMP.LcBpf
